#include <cassert>
#include <iostream>
#include <fstream>
#include <map>
#include <set>
#include <string>
#include <vector>

#include "graph.h"
#include "sat.h"
#include "sample.h"

using namespace std;

string filename(const string &prefix, int K, const string &suffix, bool opt = true) {
    string fn(prefix);
    if( opt ) fn += string("_") + to_string(K);
    fn += suffix;
    return fn;
}

template<typename T>
class Items : public set<T> {
    int num_;
  public:
    Items(int num = 0) : num_(num) { }
    ~Items() { }
    int num() const {
        return num_;
    }
    void dump(ostream &os) const {
        os << set<T>::size();
        for( typename set<T>::const_iterator it = set<T>::begin(); it != set<T>::end(); ++it )
            os << " " << *it;
        os << endl;
    }
    void read(istream &is) {
        for( size_t i = 0; i < num_; ++i ) {
            T item;
            is >> item;
            set<T>::insert(item);
        }
    }
    static const Items<T>* read_dump(istream &is) {
        int num;
        is >> num;
        Items<T> *items = new Items<T>(num);
        items->read(is);
        cout << "Items::read_dump: #items=" << items->num() << endl;
        return items;
    }
};

class Theory {
  public:
    struct Options {
        string prefix_;
        bool redundant_;
        bool redundant_graph_edges_;
        bool break_symmetries_using_graph_clique_;
        bool decode_;
        Options()
          : redundant_(true),
            redundant_graph_edges_(false),
            break_symmetries_using_graph_clique_(true),
            decode_(false) {
        }
    };

  protected:
    const DFA::Sample &S_;
    const int K_;
    const DFA::APTA<string> &apta_;
    const Options options_;

    vector<pair<int, string> > var_offsets_;
    vector<const SAT::Var*> variables_;
    vector<const SAT::Literal*> literals_;

    vector<pair<int, const string> > comments_;
    vector<const SAT::Implication*> implications_;
    vector<pair<int, string> > imp_offsets_;

    mutable bool satisfiable_;
    mutable vector<bool> model_;

  public:
    Theory(const DFA::Sample &S, int K, const DFA::APTA<string> &apta, const Options &options)
      : S_(S), K_(K), apta_(apta), options_(options) {
        cout << "Theory:"
             << " parameters:" << " K=" << K_
             << ", #labels=" << apta_.num_labels()
             << ", #vertices=" << apta_.num_vertices()
             << ", #V_accept=" << apta_.accept().size()
             << ", #V_reject=" << apta_.reject().size()
             << endl;

        cout << "---------------- variables + literals ---------------" << endl;
        build_variables();
        build_literals();
        cout << "----------------- base implications -----------------" << endl;
        build_base();

        if( options.redundant_graph_edges_ || options.break_symmetries_using_graph_clique_ ) {
            Graph::Undirected g;
            apta_.build_induced_undirected_graph(g);
            //cout << "graph" << endl;
            //g.dump(cout);

            if( options.redundant_graph_edges_ ) {
                cout << "---- add redundant implications from graph edges ----" << endl;
                add_implications_from_graph_edges(g);
            }

            if( options.break_symmetries_using_graph_clique_ ) {
                cout << "------------- add clauses from clique ---------------" << endl;
                break_symmetries_using_graph_clique(g);
            }
        }
        cout << "-----------------------------------------------------" << endl;
    }
    virtual ~Theory() {
        for( size_t i = 0; i < implications_.size(); ++i )
            delete implications_[i];
        for( size_t i = 0; i < literals_.size(); ++i )
            delete literals_[i];
        for( size_t i = 0; i < variables_.size(); ++i )
            delete variables_[i];
    }

    const SAT::Var& variable(int index) const {
        assert((0 <= index) && (index < variables_.size()));
        return *variables_[index];
    }
    const SAT::Literal& literal(int index) const {
        assert(index != 0);
        assert((-int(literals_.size()) <= index) && (index <= int(literals_.size())));
        return index > 0 ? *literals_[index - 1] : *literals_[variables_.size() + -index - 1];
    }
    int num_variables() const {
        return variables_.size();
    }

    void add_implication(const SAT::Implication *IP) {
        implications_.push_back(IP);
    }
    void add_comment(const string &comment) {
        comments_.push_back(make_pair(implications_.size(), comment));
    }
    int num_implications() const {
        return implications_.size();
    }

    bool satisfiable() const {
        return satisfiable_;
    }
    const vector<bool>& model() const {
        return model_;
    }

    void build_variables() {
        // X variables: vertices x K
        var_offsets_.push_back(make_pair(0, "X"));
        for( int v = 0; v < apta_.num_vertices(); ++v ) {
            for( int i = 0; i < K_; ++i ) {
                int index = variables_.size();
                string name = string("X(") + to_string(v) + "," + to_string(i) + ")";
                variables_.push_back(new SAT::Var(index, name));
                assert(index == X(v, i));
            }
        }
        cout << "X: #variables=" << variables_.size() - var_offsets_.back().first << " (VN), offset=" << var_offsets_.back().first << endl;

        // Z variables: K
        var_offsets_.push_back(make_pair(variables_.size(), "Z"));
        for( int i = 0; i < K_; ++i ) {
            int index = variables_.size();
            string name = string("Z(") + to_string(i) + ")";
            variables_.push_back(new SAT::Var(index, name));
            assert(index == Z(i));
        }
        cout << "Z: #variables=" << variables_.size() - var_offsets_.back().first << " (K), offset=" << var_offsets_.back().first << endl;

        // Y variables: labels x K x K
        var_offsets_.push_back(make_pair(variables_.size(), "Y"));
        for( int a = 0; a < apta_.num_labels(); ++a ) {
            for( int i = 0; i < K_; ++i ) {
                for( int j = 0; j < K_; ++j ) {
                    int index = variables_.size();
                    string name = string("Y(") + to_string(a) + "," + to_string(i) + "," + to_string(j) + ")";
                    variables_.push_back(new SAT::Var(index, name));
                    assert(index == Y(a, i, j));
                }
            }
        }
        cout << "Y: #variables=" << variables_.size() - var_offsets_.back().first << " (LK^2), offset=" << var_offsets_.back().first << endl;
    }
    void build_literals() {
        for( size_t i = 0; i < variables_.size(); ++i )
            literals_.push_back(new SAT::Literal(*variables_[i], false));
        for( size_t i = 0; i < variables_.size(); ++i )
            literals_.push_back(new SAT::Literal(*variables_[i], true));
    }

    // references to variables
    int X(int v, int i) const { // v in vertices, i in {0, ..., K-1}
        assert((0 <= v) && (v < apta_.num_vertices()));
        assert((0 <= i) && (i < K_));
        int index = i + K_ * v;
        assert(var_offsets_[0].second == "X");
        return var_offsets_[0].first + index;
    }
    int Z(int i) const { // i in {0, ..., K-1}
        assert((0 <= i) && (i < K_));
        int index = i;
        assert(var_offsets_[1].second == "Z");
        return var_offsets_[1].first + index;
    }
    int Y(int a, int i, int j) const { // a in label, i, j in {0, ..., K-1}
        assert((0 <= a) && (a < apta_.num_labels()));
        assert((0 <= i) && (i < K_));
        assert((0 <= j) && (j < K_));
        int index = j + K_ * (i + K_ * a);
        assert(var_offsets_[2].second == "Y");
        return var_offsets_[2].first + index;
    }

    // construction of base formulas
    void build_formulas_X() {
        // each vertex has at least one color (required)
        for( int v = 0; v < apta_.num_vertices(); ++v ) {
            SAT::Implication *IP = new SAT::Implication;
            for( int i = 0; i < K_; ++i )
                IP->add_consequent(1 + X(v, i));
            add_implication(IP);
        }

        // each vertex has at most one color (redundant)
        if( options_.redundant_ ) {
            for( int v = 0; v < apta_.num_vertices(); ++v ) {
                for( int i = 0; i < K_; ++i ) {
                    for( int j = 1 + i; j < K_; ++j ) {
                        SAT::Implication *IP = new SAT::Implication;
                        IP->add_consequent(-(1 + X(v, i)));
                        IP->add_consequent(-(1 + X(v, j)));
                        add_implication(IP);
                    }
                }
            }
        }
    }

    void build_formulas_Y() {
        // each parent relation targets at most one color (required)
        for( int a = 0; a < apta_.num_labels(); ++a ) {
            for( int i = 0; i < K_; ++i ) {
                for( int j = 0; j < K_; ++j ) {
                    for( int h = 0; h < j; ++h ) {
                        SAT::Implication *IP = new SAT::Implication;
                        IP->add_consequent(-(1 + Y(a, i, h)));
                        IP->add_consequent(-(1 + Y(a, i, j)));
                        add_implication(IP);
                    }
                }
            }
        }

        // each parent relation targets at least one color (redundant)
        if( options_.redundant_ ) {
            for( int a = 0; a < apta_.num_labels(); ++a ) {
                for( int i = 0; i < K_; ++i ) {
                    SAT::Implication *IP = new SAT::Implication;
                    for( int j = 0; j < K_; ++j )
                        IP->add_consequent(1 + Y(a, i, j));
                    add_implication(IP);
                }
            }
        }
    }

    void build_formulas_XZ() {
        // accepting vertices cannot have same color as rejecting ones (required)
        for( int i = 0; i < K_; ++i ) {
            for( set<int>::const_iterator it = apta_.accept().begin(); it != apta_.accept().end(); ++it ) {
                SAT::Implication *IP = new SAT::Implication;
                IP->add_consequent(-(1 + X(*it, i)));
                IP->add_consequent(1 + Z(i));
                add_implication(IP);
            }
            for( set<int>::const_iterator it = apta_.reject().begin(); it != apta_.reject().end(); ++it ) {
                SAT::Implication *IP = new SAT::Implication;
                IP->add_consequent(-(1 + X(*it, i)));
                IP->add_consequent(-(1 + Z(i)));
                add_implication(IP);
            }
        }
    }

    void build_formulas_XY() {
        // parent relation set when a vertex and its parent are colored (required)
        for( int v = 0; v < apta_.num_vertices(); ++v ) {
            std::pair<int, int> p = apta_.parent(v);
            assert((p.first != -1) || (v == apta_.initial_vertex()));
            if( v == apta_.initial_vertex() ) continue;
            for( int i = 0; i < K_; ++i ) {
                for( int j = 0; j < K_; ++j ) {
                    SAT::Implication *IP = new SAT::Implication;
                    IP->add_antecedent(1 + X(p.first, i));
                    IP->add_antecedent(1 + X(v, j));
                    IP->add_consequent(1 + Y(p.second, i, j));
                    add_implication(IP);
                }
            }
        }

        // parent relation forces vertex once parent is colored (redundant)
        if( options_.redundant_ ) {
            for( int v = 0; v < apta_.num_vertices(); ++v ) {
                std::pair<int, int> p = apta_.parent(v);
                assert((p.first != -1) || (v == apta_.initial_vertex()));
                if( v == apta_.initial_vertex() ) continue;
                for( int i = 0; i < K_; ++i ) {
                    for( int j = 0; j < K_; ++j ) {
                        SAT::Implication *IP = new SAT::Implication;
                        IP->add_antecedent(1 + Y(p.second, i, j));
                        IP->add_antecedent(1 + X(p.first, i));
                        IP->add_consequent(1 + X(v, j));
                        add_implication(IP);
                    }
                }
            }
        }
    }

    void build_base() {
        imp_offsets_.push_back(make_pair(0, "X"));
        add_comment("Theory for formulas X(v,i)");
        build_formulas_X();
        cout << "X: #implications=" << implications_.size() - imp_offsets_.back().first << " (V + V * (K-1) * K / 2 + ?)" << endl;
        //print_implications(cout, imp_offsets_.back().first, implications_.size());

        imp_offsets_.push_back(make_pair(implications_.size(), "Y"));
        add_comment("Theory for formulas Y(a,i,j)");
        build_formulas_Y();
        cout << "Y: #implications=" << implications_.size() - imp_offsets_.back().first << " (L * K^2 * (K-1) / 2 + L * K)" << endl;
        //print_implications(cout, imp_offsets_.back().first, implications_.size());

        imp_offsets_.push_back(make_pair(implications_.size(), "XZ"));
        add_comment("Theory for formulas X(v,i) and Z(i)");
        build_formulas_XZ();
        cout << "XZ: #implications=" << implications_.size() - imp_offsets_.back().first << " (K * (V_accept + V_reject))" << endl;
        //print_implications(cout, imp_offsets_.back().first, implications_.size());

        imp_offsets_.push_back(make_pair(implications_.size(), "XY"));
        add_comment("Theory for formulas X(v,i) and Y(a,i,j)");
        build_formulas_XY();
        cout << "XY: #implications=" << implications_.size() - imp_offsets_.back().first << " (2 * (V-1) * K^2)" << endl;
        //print_implications(cout, imp_offsets_.back().first, implications_.size());
    }

    void add_implications_from_graph_edges(const Graph::Undirected &g) {
        imp_offsets_.push_back(make_pair(implications_.size(), "edges"));
        add_comment(string("Redundant clauses from graph edges: #vertices=") + to_string(g.num_vertices()) + " #edges=" + to_string(g.num_edges() >> 1));
        for( int src = 0; src < g.num_vertices(); ++src ) {
            const vector<int> &edges = g.edges(src);
            for( size_t i = 0; i < edges.size(); ++i ) {
                int dst = edges[i];
                assert(src != dst);
                if( src < dst ) {
                    // add constraint: color(src) != color(dst)
                    for( int i = 0; i < K_; ++i ) {
                        SAT::Implication *IP = new SAT::Implication;
                        IP->add_consequent(-(1 + X(src, i)));
                        IP->add_consequent(-(1 + X(dst, i)));
                        add_implication(IP);
                    }
                }
            }
        }
        cout << "#implications=" << implications_.size() - imp_offsets_.back().first << endl;
    }

    void break_symmetries_using_graph_clique(const Graph::Undirected &g) {
        // calculate accept/reject cliques
        set<int> accept_clique, reject_clique;
        g.find_large_clique_greedy(apta_.accept(), accept_clique);
        g.find_large_clique_greedy(apta_.reject(), reject_clique);

        // merge accept/reject cliques into bigger clique
        set<int> clique;
        clique.insert(accept_clique.begin(), accept_clique.end());
        clique.insert(reject_clique.begin(), reject_clique.end());
        assert(clique.size() == accept_clique.size() + reject_clique.size());

        // if not enough color, add empty clause, else assign different color to vertices in clique
        imp_offsets_.push_back(make_pair(implications_.size(), "clique"));
        add_comment(string("Theory for breaking symmetries: #vertices=") + to_string(g.num_vertices()) + " #edges=" + to_string(g.num_edges() >> 1) + " clique-size=" + to_string(clique.size()));
        if( K_ < clique.size() ) {
            SAT::Implication *IP = new SAT::Implication;
            add_implication(IP);
        } else {
            int color = 0;
            for( set<int>::const_iterator it = clique.begin(); it != clique.end(); ++it, ++color ) {
                // assign color to vertex *it
                assert(color < K_);
                SAT::Implication *IP = new SAT::Implication;
                IP->add_consequent(1 + X(*it, color));
                add_implication(IP);
            }
        }
        cout << "#implications=" << implications_.size() - imp_offsets_.back().first << endl;
    }

    // readers
    void read_minisat_output(ifstream &is) const {
        string status;
        is >> status;
        satisfiable_ = status == "SAT";
        if( satisfiable_ ) {
            int var, lit;
            model_ = vector<bool>(variables_.size(), false);
            for( size_t i = 0; i < variables_.size(); ++i ) {
                is >> lit;
                var = lit > 0 ? lit - 1 : -lit - 1;
                assert(var == int(i));
                model_[var] = lit > 0;
            }
            is >> lit;
            assert(lit == 0);
        } else {
            model_.clear();
        }
    }

    // output
    void dump(ostream &os) const {
        os << "p cnf " << variables_.size() << " " << implications_.size() << endl;
        size_t i = 0;
        for( size_t j = 0; j < implications_.size(); ++j ) {
            while( (i < comments_.size()) && (comments_[i].first == j) ) {
                os << "c " << comments_[i].second << endl;
                ++i;
            }
            implications_[j]->dump(os);
        }
        while( i < comments_.size() ) {
            os << "c " << comments_[i].second << endl;
            ++i;
        }
    }
    void print(ostream &os) const {
        size_t i = 0;
        for( size_t j = 0; j < implications_.size(); ++j ) {
            while( (i < comments_.size()) && (comments_[i].first == j) ) {
                os << "% " << comments_[i].second << endl;
                ++i;
            }
            implications_[j]->print(os, literals_);
            os << endl;
        }
        while( i < comments_.size() ) {
            os << "% " << comments_[i].second << endl;
            ++i;
        }
    }
    void print_implications(ostream &os, int start, int end) const {
        while( start < end ) {
            implications_[start++]->print(os, literals_);
            os << endl;
        }
    }

    void dump_model(ostream &os) const {
        for( size_t var = 0; var < variables_.size(); ++var ) {
            os << variables_[var] << " ";
        }
        os << "0" << endl;
    }
    void print_model(ostream &os) const {
        for( size_t var = 0; var < model_.size(); ++var ) {
            bool sign = model_[var];
            if( sign ) {
                assert(var < variables_.size());
                variables_[var]->print(os);
                os << endl;
            }
        }
    }

    // print abstraction coded in model
    void decode_model(const string &name, ostream &os, bool dot_format) const {
        assert(satisfiable_ && (model_.size() == variables_.size()));
        //print_model(cout);

        // vertex colors
        vector<int> color(apta_.num_vertices(), -1);
        vector<vector<int> > group(K_);
        for( int v = 0; v < apta_.num_vertices(); ++v ) {
            os << "// color of vertex v" << v << " is";
            for( int i = 0; i < K_; ++i ) {
                if( model_[X(v, i)] ) {
                    os << " " << i;
                    color[v] = i;
                    group[i].push_back(v);
                }
            }
            os << endl;
        }

        // extract dfa edges
        vector<set<pair<int, int> > > dfa_edges(K_);
        for( int i = 0; i < K_; ++i ) {
            for( int j = 0; j < group[i].size(); ++j ) {
                int src = group[i][j];
                const vector<pair<int, int> > &edges = apta_.edges(src);
                for( int k = 0; k < edges.size(); ++k ) {
                    int label_index = edges[k].first;
                    int dst = edges[k].second;
                    dfa_edges[i].insert(make_pair(label_index, color[dst]));
                }
            }
        }

        set<int> accepting;
        for( set<int>::const_iterator it = apta_.accept().begin(); it != apta_.accept().end(); ++it )
            accepting.insert(color[*it]);

        // output comments
        os << "// initial state: q" << color[apta_.initial_vertex()] << endl;
        for( int i = 0; i < K_; ++i ) {
            for( set<pair<int, int> >::const_iterator it = dfa_edges[i].begin(); it != dfa_edges[i].end(); ++it ) {
                string label = apta_.get_label(it->first);
                int j = it->second;
                os << "// edge q" << i << " -> q" << j << " w/ label " << label << endl;
            }
        }

        os << "// accepting states:";
        for( set<int>::const_iterator it = accepting.begin(); it != accepting.end(); ++it )
            os << " q" << *it;
        os << endl;

        if( dot_format ) {
            os << "digraph dfa {" << endl;
            os << "    node [shape = point ]; init;" << endl;

            os << "    node [shape = doublecircle];" << endl;
            for( set<int>::const_iterator it = accepting.begin(); it != accepting.end(); ++it )
                os << "    q" << *it << ";" << endl;

            os << "    node [shape = circle];" << endl;
            for( int i = 0; i < K_; ++i ) {
                for( set<pair<int, int> >::const_iterator it = dfa_edges[i].begin(); it != dfa_edges[i].end(); ++it ) {
                    string label = apta_.get_label(it->first);
                    int j = it->second;
                    os << "    q" << i << " -> q" << j << " [label=\"" << label << "\"];" << endl;
                }
            }
            os << "    init -> q" << color[apta_.initial_vertex()] << ";" << endl;
            os << "}" << endl;
        }
    }
};

const DFA::Sample* read_data(const string &sample_filename) {
    const DFA::Sample* sample = nullptr;

    cout << "reading '" << sample_filename << "' ... " << flush;
    ifstream ifs_sample(sample_filename.c_str());
    if( !ifs_sample.fail() ) {
        sample = DFA::Sample::read_dump(ifs_sample);
        ifs_sample.close();
    } else {
        throw runtime_error("error: opening file '" + sample_filename + "'");
        cout << "error: opening file '" << sample_filename << "'" << endl;
    }

    return sample;
}

void usage(ostream &os, const string &name) {
    cout << endl
         << "usage: " << name << " [--decode] [--disable-redundant] [--disable-symmetries-break-using-graph-clique] [--enable-redundant-graph-edges] <prefix> <K>" << endl
         << endl
         << "where" << endl
         << "    <prefix> is prefix for all files" << endl
         << "    K is number of colors" << endl
         << endl
         << "For the options," << endl
         << "    --decode to decode model in '<prefix>_<K>_model.cnf' found by minisat" << endl
         << "    --disable-redundant to disable redundant clauses (except for below options)" << endl
         << "    --disable-symmetries-break-using-graph-clique to enable assigning fixed colors using graph clique" << endl
         << "    --enable-redundant-graph-edges to enable redundant clauses from graph edges" << endl
         << endl
         ;
}

int main(int argc, const char **argv) {
    // print call
    cout << "call:";
    for( int i = 0; i < argc; ++i )
        cout << " " << argv[i];
    cout << endl;

    // read executable name
    string name(*argv);

    // read options
    Theory::Options options;
    for( ++argv, --argc; (argc > 0) && (**argv == '-'); ++argv, --argc ) {
        if( string(*argv) == "--decode" ) {
            options.decode_ = true;
        } else if( string(*argv) == "--disable-redundant" ) {
            options.redundant_ = false;
        } else if( string(*argv) == "--disable-symmetries-break-using-graph-clique" ) {
            options.break_symmetries_using_graph_clique_ = true;
        } else if( string(*argv) == "--enable-redundant-graph-edges" ) {
            options.redundant_graph_edges_ = true;
        } else {
            cout << "error: unrecognized option '" << *argv << "'" << endl;
            usage(cout, name);
            exit(0);
        }
    }

    // check we have enough arguments
    if( argc < 2 ) {
        usage(cout, name);
        exit(0);
    }

    // read arguments
    options.prefix_ = argv[0];
    int K = atoi(argv[1]);
    cout << "arguments: prefix=" << options.prefix_ << ", K=" << K << endl;

    // input filenames
    string sample_filename = filename(options.prefix_, K, "_sample.dat", false);

    // read data
    const DFA::Sample *S = read_data(sample_filename);
    const DFA::APTA<string> *apta = S->build_APTA();

    // create theory
    Theory Th(*S, K, *apta, options);
    cout << "#variables=" << Th.num_variables() << endl;
    cout << "#implications=" << Th.num_implications() << endl;

    // decode
    if( options.decode_ ) {
        string model_filename = filename(options.prefix_, K, "_model.cnf");
        cout << "reading file '" << model_filename << "' ..." << flush;
        ifstream ifs(model_filename.c_str());
        if( !ifs.fail() ) {
            Th.read_minisat_output(ifs);
            ifs.close();
            cout << " done!" << endl;

            // output model in .dot format
            string dot_filename = filename(options.prefix_, K, "_dfa.dot");
            cout << "writing file '" << dot_filename << "' ..." << flush;
            ofstream os(dot_filename.c_str());
            Th.decode_model(model_filename, os, true);
            os.close();
            cout << " done!" << endl;
        } else {
            cout << "error: opening file '" << model_filename << "'" << endl;
        }
    } else {
        // output theory in human readable format
        //Th.print(cout);

        // output theory in SATLIB format
        string theory_filename = filename(options.prefix_, K, "_theory.cnf");
        cout << "writing file '" << theory_filename << "' ..." << flush;
        ofstream os(theory_filename.c_str());
        Th.dump(os);
        os.close();
        cout << " done!" << endl;
    }

    delete S;
    delete apta;
    return 0;
}

