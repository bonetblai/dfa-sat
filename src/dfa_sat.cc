#include <cassert>
#include <iostream>
#include <fstream>
#include <map>
#include <set>
#include <string>
#include <vector>

#include "dfa.h"
#include "graph.h"
#include "sample.h"

#include <sat/encoder/theory.h>

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

class Theory : public SAT::Theory {
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

    virtual void build_variables() {
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

    virtual void build_base() {
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

    virtual void build_rest() {
        if( options_.redundant_graph_edges_ || options_.break_symmetries_using_graph_clique_ ) {
            Graph::Undirected g;
            cout << "----------- constructing undirected graph -----------" << endl;
            cout << "apta: #accept=" << apta_.accept().size() << ", #reject=" << apta_.reject().size() << endl;
            apta_.build_induced_undirected_graph(g);
            //cout << "graph" << endl;
            //g.dump(cout);
            cout << "undirected graph: #vertices=" << g.num_vertices() << ", #edges=" << g.num_edges() << std::endl;

            if( options_.redundant_graph_edges_ ) {
                cout << "---- add redundant implications from graph edges ----" << endl;
                add_implications_from_graph_edges(g);
            }

            if( options_.break_symmetries_using_graph_clique_ ) {
                cout << "------------- add clauses from clique ---------------" << endl;
                break_symmetries_using_graph_clique(g);
            }
        }
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
        cout << "clique: size=" << clique.size() << ", accept-clique.size=" << accept_clique.size() << ", reject-clique.size=" << reject_clique.size() << endl;

        // if not enough color, add empty clause, else assign different color to vertices in clique
        imp_offsets_.push_back(make_pair(implications_.size(), "clique"));
        add_comment(string("Theory for breaking symmetries: #vertices=") + to_string(g.num_vertices()) + " #edges=" + to_string(g.num_edges() >> 1) + " clique-size=" + to_string(clique.size()));
        if( K_ < clique.size() ) {
            clear_implications();
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

  public:
    Theory(const DFA::Sample &S, int K, const DFA::APTA<string> &apta, const Options &options)
      : SAT::Theory(options.decode_),
        S_(S), K_(K), apta_(apta), options_(options) {
        cout << "Theory:"
             << " parameters:" << " K=" << K_
             << ", #labels=" << apta_.num_labels()
             << ", #vertices=" << apta_.num_vertices()
             << ", #V_accept=" << apta_.accept().size()
             << ", #V_reject=" << apta_.reject().size()
             << endl;
        build_theory();
    }
    virtual ~Theory() { }

    // print abstraction coded in model
    void decode_model(DFA::DFA<string> &dfa) const {
        assert(satisfiable_ && (model_.size() == variables_.size()));
        //print_model(cout);

        // vertex colors
        vector<int> color(apta_.num_vertices(), -1);
        vector<vector<int> > group(K_);
        for( int v = 0; v < apta_.num_vertices(); ++v ) {
            for( int i = 0; i < K_; ++i ) {
                if( model_[X(v, i)] ) {
                    color[v] = i;
                    group[i].push_back(v);
                }
            }
            //os << "// color of vertex v" << v << " is " << color[v] << endl;
        }

        // build DFA
        assert(K_ == dfa.num_states());
        for( int i = 0; i < K_; ++i ) {
            for( int j = 0; j < group[i].size(); ++j ) {
                int src = group[i][j];
                const vector<pair<int, int> > &edges = apta_.edges(src);
                for( int k = 0; k < edges.size(); ++k ) {
                    int label_index = edges[k].first;
                    const string &label = apta_.get_label(label_index);
                    label_index = dfa.get_label_index(label);
                    if( label_index == -1 ) label_index = dfa.add_label(label);
                    int dst = dfa.edge(color[src], label_index);
                    if( dst == -1 ) {
                        dst = edges[k].second;
                        //cout << "dfa: add_edge: src=" << color[src] << ", dst=" << color[dst] << ", label=|" << label << "|" << endl;
                        dfa.add_edge(color[src], label_index, color[dst]);
                    } else {
                        assert(dst == color[edges[k].second]);
                    }
                }
            }
        }

        // set initial and accepting states
        dfa.set_initial_state(color[apta_.initial_vertex()]);
        for( set<int>::const_iterator it = apta_.accept().begin(); it != apta_.accept().end(); ++it )
            dfa.mark_as_accept(color[*it]);

        // simplify
        dfa.remove_redundant_non_accepting_states();
    }
    virtual void decode_model(ostream &os) const {
        DFA::DFA<string> dfa(K_);
        decode_model(dfa);
        dfa.dump(os);
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

            // get dfa from model
            DFA::DFA<string> dfa(K);
            Th.decode_model(dfa);

            // output dfa in .dot format
            string dot_filename = filename(options.prefix_, K, "_dfa.dot");
            cout << "writing file '" << dot_filename << "' ..." << flush;
            ofstream dot_os(dot_filename.c_str());
            dfa.dump_dot(dot_os);
            dot_os.close();
            cout << " done!" << endl;

            // output dfa in .dfa format
            string dfa_filename = filename(options.prefix_, K, ".dfa");
            cout << "writing file '" << dfa_filename << "' ..." << flush;
            ofstream dfa_os(dfa_filename.c_str());
            dfa.dump(dfa_os);
            dfa_os.close();
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

