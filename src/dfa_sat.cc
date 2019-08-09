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
#include "utils.h"

#include <sat/encoder/theory.h>

// strong typedefs for safer implementation
#include <boost/serialization/strong_typedef.hpp>

using namespace std;

inline std::string color(const std::string &control_sequence, const std::string &str, bool use_colors = true) {
    return use_colors ? control_sequence + str + Utils::normal() : str;
}
inline std::string cyan(const std::string &str, bool use_colors = true) {
    return color(Utils::cyan(), str, use_colors);
}
inline std::string green(const std::string &str, bool use_colors = true) {
    return color(Utils::green(), str, use_colors);
}

string filename(const string &prefix, int K, const string &suffix, bool opt = true) {
    string fn(prefix);
    if( opt ) fn += string("_") + to_string(K);
    fn += suffix;
    return fn;
}

// create strong typedefs (type aliases)
BOOST_STRONG_TYPEDEF(int, Color)
BOOST_STRONG_TYPEDEF(int, Label)
BOOST_STRONG_TYPEDEF(int, Vertex)

class Theory : public SAT::Theory {
  public:
    struct Options {
        string prefix_;
        bool disable_colors_;
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
    const DFA::APTA<string> &apta_;
    const Options options_;

    const int num_colors_;
    const int num_labels_;
    const int num_vertices_;

    // parameters
    vector<Color> p_colors_;
    vector<Label> p_labels_;
    vector<Vertex> p_vertices_;

    // variables
    SAT::VarSet color, Y, accept;

  public:
    Theory(const DFA::Sample &S, const DFA::APTA<string> &apta, int num_colors, const Options &options)
      : SAT::Theory(options.decode_),
        S_(S),
        apta_(apta),
        options_(options),
        num_colors_(num_colors),
        num_labels_(apta_.num_labels()),
        num_vertices_(apta_.num_vertices()) {
        initialize(cout);
        build_variables();
    }
    virtual ~Theory() { }

  protected:
    void initialize(ostream &os) {
        os << "Theory:"
           << " parameters:" << " K=" << num_colors_
           << ", #labels=" << num_labels_
           << ", #vertices=" << num_vertices_
           << ", #V_accept=" << apta_.accept().size()
           << ", #V_reject=" << apta_.reject().size()
           << endl;

        // construct parameter lists
        p_colors_ = vector<Color>(num_colors_);
        iota(p_colors_.begin(), p_colors_.end(), 0);
        p_labels_ = vector<Label>(apta_.num_labels());
        iota(p_labels_.begin(), p_labels_.end(), 0);
        p_vertices_ = vector<Vertex>(apta_.num_vertices());
        iota(p_vertices_.begin(), p_vertices_.end(), 0);
    }

    void initialize_variables() override {
        color.initialize(*this, "color(v,k)", p_vertices_, p_colors_);
        Y.initialize(*this, "Y(l,k,kp)", p_labels_, p_colors_, p_colors_);
        accept.initialize(*this, "accept(k)", p_colors_);
    }

    // base formulas

    // exactly one color per vertex
    void build_formulas_exactly_1_color(Vertex v) {
        assert((0 <= v) && (v < num_vertices_));
        std::vector<int> literals(num_colors_);
        for( Color k = Color(0); k < num_colors_; ++k )
            literals[k] = 1 + color(v, k);
        exactly_1(string("color-exactly-1(") + to_string(v) + ")", literals);
    }
    void build_formulas_exactly_1_color(ostream &os) {
        imp_offsets_.push_back(std::make_pair(num_implications(), "exactly-1 { color(v,k) : 0 <= k < #colors }"));
        add_comment("exactly-1 { color(v,k) : 0 <= k < #colors }");
        for( Vertex v = Vertex(0); v < num_vertices_; ++v )
            build_formulas_exactly_1_color(v);
        os << "(1) exactly-1 { color(v,k) : 0 <= k < #colors }: #implications=" << num_implications() - imp_offsets_.back().first << endl;
    }

    // exactly one color for parent-relation
    void build_formulas_exactly_1_parent_relation(Label l, Color k) {
        assert((0 <= l) && (l < num_labels_));
        assert((0 <= k) && (k < num_colors_));
        std::vector<int> literals(num_colors_);
        for( Color kp = Color(0); kp < num_colors_; ++kp )
            literals[kp] = 1 + Y(l, k, kp);
        exactly_1(string("parent-relation-exactly-1(") + to_string(l) + "," + to_string(k) + ")", literals);
    }
    void build_formulas_exactly_1_parent_relation(ostream &os) {
        imp_offsets_.push_back(std::make_pair(num_implications(), "exactly-1 { Y(l,k,kp) : 0 <= kp < #colors }"));
        add_comment("exactly-1 { Y(l,k,kp) : 0 <= kp < #colors }");
        for( Label l = Label(0); l < num_labels_; ++l ) {
            for( Color k = Color(0); k < num_colors_; ++k )
                build_formulas_exactly_1_parent_relation(l, k);
        }
        os << "(2) exactly-1 { Y(l,k,kp) : 0 <= kp < #colors }: #implications=" << num_implications() - imp_offsets_.back().first << endl;
    }

    // separate colors
    // [v is accepting] color(v,k) => accept(k)
    // [v isn't accepting] color(v,k) => -accept(k)
    void build_formulas_separate_colors(Color k, Vertex v, bool accepting) {
        assert((0 <= k) && (k < num_colors_));
        assert((0 <= v) && (v < num_vertices_));
        SAT::Implication *IP = new SAT::Implication;
        IP->add_antecedent(1 + color(v, k));
        IP->add_consequent(accepting ? 1 + accept(k) : -(1 + accept(k)));
        add_implication(IP);
    }
    void build_formulas_separate_colors(ostream &os) {
        imp_offsets_.push_back(std::make_pair(num_implications(), "color(v,k) => accept(k)[v is accepting] v -accept(k)[v isn't accepting]"));
        add_comment("color(v,k) => accept(k)[v is accepting] v -accept(k)[v isn't accepting]");
        for( Color k = Color(0); k < num_colors_; ++k ) {
            for( set<int>::const_iterator it = apta_.accept().begin(); it != apta_.accept().end(); ++it )
                build_formulas_separate_colors(k, Vertex(*it), true);
            for( set<int>::const_iterator it = apta_.reject().begin(); it != apta_.reject().end(); ++it )
                build_formulas_separate_colors(k, Vertex(*it), false);
        }
        os << "(3) color(v,k) => accept(k)[v is accepting] v -accept(k)[v isn't accepting]: #implications=" << num_implications() - imp_offsets_.back().first << std::endl;
    }

    // color(u,k) => [ color(v,kp) <=> Y(u.label,k,kp) ] [ (u,v) ]
    void build_formulas_color_then_color_iff_Y(Vertex u, Vertex v, Label l, Color k, Color kp) {
        assert((0 <= u) && (u < num_vertices_));
        assert((0 <= v) && (v < num_vertices_));
        assert((0 <= l) && (l < num_labels_));
        assert((0 <= k) && (k < num_colors_));
        assert((0 <= kp) && (kp < num_colors_));

        // color(u,k) & color(v,kp) => Y(u.label,k,kp) [ (u,v) ]
        SAT::Implication *IP1 = new SAT::Implication;
        IP1->add_antecedent(1 + color(u, k));
        IP1->add_antecedent(1 + color(v, kp));
        IP1->add_consequent(1 + Y(l, k, kp));
        add_implication(IP1);

        // color(u,k) & Y(u,label,k,kp) => color(v,kp) [ (u,v) ]
        SAT::Implication *IP2 = new SAT::Implication;
        IP2->add_antecedent(1 + color(u, k));
        IP2->add_antecedent(1 + Y(l, k, kp));
        IP2->add_consequent(1 + color(v, kp));
        add_implication(IP2);
    }
    void build_formulas_color_then_color_iff_Y(ostream &os) {
        imp_offsets_.push_back(std::make_pair(num_implications(), "color(u,k) => [ color(v,kp) <=> Y(u.label,k,kp) ] [ (u,v) ]"));
        add_comment("color(u,k) => [ color(v,kp) <=> Y(u.label,k,kp) ] [ (u,v) ]");

        for( Vertex v = Vertex(0); v < num_vertices_; ++v ) {
            pair<int, int> p = apta_.parent(v);
            assert((p.first != -1) || (v == apta_.initial_vertex()));
            if( v == apta_.initial_vertex() ) continue;

            Vertex u = Vertex(p.first);
            Label l = Label(p.second);
            for( Color k = Color(0); k < num_colors_; ++k ) {
                for( Color kp = Color(0); kp < num_colors_; ++kp )
                    build_formulas_color_then_color_iff_Y(u, v, l, k, kp);
            }
        }

        os << "(4) color(u,k) => [ color(v,kp) <=> Y(u.label,k,kp) ] [ (u,v) ]: #implications=" << num_implications() - imp_offsets_.back().first << std::endl;
    }

    void build_base() override {
        cout << green("Each vertex has exactly one color:", !options_.disable_colors_) << endl;
        build_formulas_exactly_1_color(cout);

        cout << green("Each parent relation has exactly one color:", !options_.disable_colors_) << endl;
        build_formulas_exactly_1_parent_relation(cout);

        cout << green("Separate colors between accepting and non-accepting:", !options_.disable_colors_) << endl;
        build_formulas_separate_colors(cout);

        cout << green("Parents 1:", !options_.disable_colors_) << endl;
        build_formulas_color_then_color_iff_Y(cout);
    }

    // rest

    void add_implications_from_graph_edges(ostream &os, const Graph::Undirected &g) {
        imp_offsets_.push_back(make_pair(num_implications(), "edges"));
        add_comment(string("Redundant clauses from graph edges: #vertices=") + to_string(g.num_vertices()) + " #edges=" + to_string(g.num_edges() >> 1));

        for( Vertex src = Vertex(0); src < num_vertices_; ++src ) {
            const vector<int> &edges = g.edges(src);
            for( size_t i = 0; i < edges.size(); ++i ) {
                Vertex dst = Vertex(edges[i]);
                assert(src != dst);
                if( src < dst ) {
                    // add constraint: color(src) != color(dst)
                    for( Color k = Color(0); k < num_colors_; ++k ) {
                        SAT::Implication *IP = new SAT::Implication;
                        IP->add_consequent(-(1 + color(src, k)));
                        IP->add_consequent(-(1 + color(dst, k)));
                        add_implication(IP);
                    }
                }
            }
        }

        os << "edges: #implications=" << num_implications() - imp_offsets_.back().first << endl;
    }

    void break_symmetries_using_graph_clique(ostream &os, const Graph::Undirected &g) {
        // calculate accept/reject cliques
        set<int> accept_clique, reject_clique;
        g.find_large_clique_greedy(apta_.accept(), accept_clique);
        g.find_large_clique_greedy(apta_.reject(), reject_clique);

        // merge accept/reject cliques into bigger clique
        set<int> clique;
        clique.insert(accept_clique.begin(), accept_clique.end());
        clique.insert(reject_clique.begin(), reject_clique.end());
        assert(clique.size() == accept_clique.size() + reject_clique.size());
        os << "clique: size=" << clique.size() << ", accept-clique.size=" << accept_clique.size() << ", reject-clique.size=" << reject_clique.size() << endl;

        // if not enough color, add empty clause, else assign different color to vertices in clique
        imp_offsets_.push_back(make_pair(num_implications(), "clique"));
        add_comment(string("Theory for breaking symmetries: #vertices=") + to_string(g.num_vertices()) + " #edges=" + to_string(g.num_edges() >> 1) + " clique-size=" + to_string(clique.size()));

        if( num_colors_ < clique.size() ) {
            SAT::Implication *IP = new SAT::Implication;
            add_implication(IP);
        } else {
            Color k = Color(0);
            for( set<int>::const_iterator it = clique.begin(); it != clique.end(); ++it, ++k ) {
                // assign color k to vertex *it
                assert(k < num_colors_);
                SAT::Implication *IP = new SAT::Implication;
                IP->add_consequent(1 + color(*it, k));
                add_implication(IP);
            }
        }

        os << "clique: #implications=" << num_implications() - imp_offsets_.back().first << endl;
    }

    void build_rest() override {
        if( !options_.decode_ && (options_.redundant_graph_edges_ || options_.break_symmetries_using_graph_clique_) ) {
            Graph::Undirected g;
            cout << "----------- constructing undirected graph -----------" << endl;
            cout << "apta: #accept=" << apta_.accept().size() << ", #reject=" << apta_.reject().size() << endl;
            apta_.build_induced_undirected_graph(g);
            cout << "undirected graph: #vertices=" << g.num_vertices() << ", #edges=" << g.num_edges() << endl;

            if( options_.redundant_graph_edges_ ) {
                cout << "---- add redundant implications from graph edges ----" << endl;
                add_implications_from_graph_edges(cout, g);
            }

            if( options_.break_symmetries_using_graph_clique_ ) {
                cout << "------------- add clauses from clique ---------------" << endl;
                break_symmetries_using_graph_clique(cout, g);
            }
        }
    }

  public:
    // print abstraction coded in model
    void decode_model(DFA::DFA<string> &dfa) const {
        assert(satisfiable_ && (model_.size() == variables_.size()));
        //print_model(cout);

        // vertex colors
        vector<int> colors(num_vertices_, -1);
        vector<vector<int> > group(num_colors_);
        for( Vertex v = Vertex(0); v < num_vertices_; ++v ) {
            for( Color k = Color(0); k < num_colors_; ++k ) {
                if( model_[color(v, k)] ) {
                    colors[v] = k;
                    group[k].push_back(v);
                }
            }
            //os << "// color of vertex v" << v << " is " << color[v] << endl;
        }

        // build DFA
        assert(num_colors_ == dfa.num_states());
        for( int i = 0; i < num_colors_; ++i ) {
            for( int j = 0; j < group[i].size(); ++j ) {
                int src = group[i][j];
                const vector<pair<int, int> > &edges = apta_.edges(src);
                for( int k = 0; k < edges.size(); ++k ) {
                    int label_index = edges[k].first;
                    const string &label = apta_.get_label(label_index);
                    label_index = dfa.get_label_index(label);
                    if( label_index == -1 ) label_index = dfa.add_label(label);
                    int dst = dfa.edge(colors[src], label_index);
                    if( dst == -1 ) {
                        dst = edges[k].second;
                        //cout << "dfa: add_edge: src=" << colors[src] << ", dst=" << colors[dst] << ", label=|" << label << "|" << endl;
                        dfa.add_edge(colors[src], label_index, colors[dst]);
                    } else {
                        assert(dst == colors[edges[k].second]);
                    }
                }
            }
        }

        // set initial and accepting states
        dfa.set_initial_state(colors[apta_.initial_vertex()]);
        for( set<int>::const_iterator it = apta_.accept().begin(); it != apta_.accept().end(); ++it )
            dfa.mark_as_accept(colors[*it]);

        // simplify
        dfa.remove_redundant_non_accepting_states();
    }
    void decode_model(ostream &os) const override {
        DFA::DFA<string> dfa(num_colors_);
        decode_model(dfa);
        dfa.dump(os);
    }
};

const DFA::Sample* read_data(const string &sample_filename) {
    const DFA::Sample* sample = nullptr;

    cout << Utils::cyan() << "reading '" << sample_filename << "' ... " << Utils::normal() << flush;
    ifstream ifs_sample(sample_filename.c_str());
    if( !ifs_sample.fail() ) {
        sample = DFA::Sample::read_dump(ifs_sample);
        ifs_sample.close();
    } else {
        throw runtime_error("error: opening file '" + sample_filename + "'");
        cout << Utils::error() << "opening file '" << sample_filename << "'" << endl;
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
            cout << Utils::error() << "unrecognized option '" << *argv << "'" << endl;
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

    // build apta
    cout << "building APTA ..." << flush;
    const DFA::APTA<string> *apta = S->build_APTA();
    cout << " done!" << endl;

    // create theory
    Theory theory(*S, *apta, K, options);

    // decode
    if( options.decode_ ) {
        // perform void construction to terminate generation of (auxiliary) variables
        theory.build_theory();

        // report theory size
        cout << "#variables=" << theory.num_variables() << endl;
        cout << "#implications=" << theory.num_implications() << endl;

        // read model
        string model_filename = filename(options.prefix_, K, "_model.cnf");
        cout << Utils::cyan() << "reading file '" << model_filename << "' ..." << Utils::normal() << flush;
        ifstream ifs(model_filename.c_str());
        if( !ifs.fail() ) {
            // read model w/ appropriate reader; to decide, extract header and re-open file
            string header;
            ifs >> header;
            ifs.close();
            ifs.open(model_filename.c_str());
            assert(!ifs.fail());

            if( (header == "SAT") || (header == "UNSAT") )
                theory.read_minisat_output(ifs);
            else if( isdigit(*header.c_str()) || (*header.c_str() == '-') )
                theory.read_glucose_output(ifs);
            else
                theory.read_other_output(ifs);

            ifs.close();
            cout << Utils::cyan() << " done!" << Utils::normal() << endl;

            // get dfa from model
            DFA::DFA<string> dfa(K);
            theory.decode_model(dfa);

            // output dfa in .dot format
            string dot_filename = filename(options.prefix_, K, ".dot");
            cout << Utils::cyan() << "writing file '" << dot_filename << "' ..." << Utils::normal() << flush;
            ofstream dot_os(dot_filename.c_str());
            dfa.dump_dot(dot_os);
            dot_os.close();
            cout << Utils::cyan() << " done!" << Utils::normal() << endl;

            // output dfa in .dfa format
            string dfa_filename = filename(options.prefix_, K, ".dfa");
            cout << Utils::cyan() << "writing file '" << dfa_filename << "' ..." << Utils::normal() << flush;
            ofstream dfa_os(dfa_filename.c_str());
            dfa.dump(dfa_os);
            dfa_os.close();
            cout << Utils::cyan() << " done!" << Utils::normal() << endl;
        } else {
            cout << Utils::error() << "opening file '" << model_filename << "'" << endl;
        }
    } else {
        // output theory in human readable format
        //theory.print(cout);

        // open output stream (tunnel)
        string theory_filename = filename(options.prefix_, K, "_theory.cnf");
        cout << Utils::cyan() << "set tunnel to '" << theory_filename << "'" << Utils::normal() << endl;
        ofstream ofs(theory_filename.c_str());
        theory.set_tunnel(&ofs);

        // build theory (generate output)
        theory.build_theory();

        // report theory size
        cout << "#variables=" << theory.num_variables() << endl;
        cout << "#implications=" << theory.num_implications() << endl;

        // close output stream (tunnel)
        ofs << theory.header() << std::endl;
        ofs.close();
        theory.set_tunnel(nullptr);
    }

    delete S;
    delete apta;
    return 0;
}

