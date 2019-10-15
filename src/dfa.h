#ifndef DFA_H
#define DFA_H

#include <cassert>
#include <iostream>
#include <deque>
#include <map>
#include <set>
#include <vector>

#include "graph.h"

namespace DFA {

// Augmented Prefix Tree Acceptor (APTA)
template<typename T> class DFA {
  protected:
    int num_states_;
    int num_labels_;
    int num_edges_;
    int initial_state_;
    std::vector<std::set<int> > state_classes_; // first one is 'accepting states'

    std::vector<T> labels_;
    std::vector<std::vector<std::pair<int, int> > > edges_;
    std::map<T, int> labels_map_;
    std::vector<T> state_labels_;

  public:
    DFA(int num_states = 0)
      : num_states_(num_states), num_labels_(0), num_edges_(0), initial_state_(-1) {
        edges_ = std::vector<std::vector<std::pair<int, int> > >(num_states_);
        state_labels_ = std::vector<T>(num_states_);
    }
    virtual ~DFA() = default;

    // accessors
    int num_states() const {
        return num_states_;
    }
    int num_labels() const {
        return num_labels_;
    }
    int num_edges() const {
        return num_edges_;
    }
    int initial_state() const {
        return initial_state_;
    }

    bool is_sink(int state) const {
        assert((0 <= state) && (state < num_states_));
        for( size_t i = 0; i < edges_[state].size(); ++i ) {
            if( edges_[state][i].second != state )
                return false;
        }
        return true;
    }

    int num_state_classes() const {
        return state_classes_.size();
    }
    bool belong(int state, int i) const {
        assert((0 <= i) && (i < num_state_classes()));
        return state_classes_.at(i).find(state) != state_classes_.at(i).end();
    }
    bool marked(int state) const {
        for( int i = 0; i < num_state_classes(); ++i ) {
            if( belong(state, i) )
                return true;
        }
        return false;
    }
    void marks(int state, std::vector<int> &m) const {
        for( int i = 0; i < num_state_classes(); ++i ) {
            if( belong(state, i) )
                m.push_back(i);
        }
    }
    const std::set<int>& state_class(int i) const {
        assert((0 <= i) && (i < num_state_classes()));
        return state_classes_.at(i);
    }

    bool accept(int state) const {
        return belong(state, 0);
    }
    const std::set<int>& accept() const {
        return state_class(0);
    }

    int get_label_index(const T &label) const {
        typename std::map<T, int>::const_iterator it = labels_map_.find(label);
        return it == labels_map_.end() ? -1 : it->second;
    }
    T get_label(int index) const {
        assert((0 <= index) && (index < num_labels_));
        return labels_[index];
    }
    const std::vector<T>& labels() const {
        return labels_;
    }

    int edge(int src, int label_index) const {
        assert((0 <= src) && (src < num_states_));
        for( size_t i = 0; i < edges_[src].size(); ++i ) {
            if( edges_[src][i].first == label_index )
                return edges_[src][i].second; // dst
        }
        return -1;
    }
    bool is_edge(int src, int dst) const {
        assert((0 <= src) && (src < num_states_));
        for( size_t i = 0; i < edges_[src].size(); ++i ) {
            if( edges_[src][i].second == dst )
                return true;
        }
        return false;
    }
    const std::vector<std::pair<int, int> >& edges(int src) const {
        assert((0 <= src) && (src < num_states_));
        return edges_[src];
    }

    // modifiers
    int add_state() {
        edges_.push_back(std::vector<std::pair<int, int> >());
        state_labels_.push_back("");
        return num_states_++;
    }
    void set_initial_state(int state) {
        assert((0 <= state) && (state < num_states_));
        initial_state_ = state;
    }
    void set_state_label(int state, const T &label) {
        state_labels_[state] = label;
    }

    int add_label(const T &label) {
        labels_.push_back(label);
        labels_map_.insert(std::make_pair(label, num_labels_));
        return num_labels_++;
    }
    int add_edge(int src, int label_index, int dst) {
        assert(label_index != -1);
        assert((0 <= src) && (src < num_states_));
        edges_[src].push_back(std::make_pair(label_index, dst));
        num_edges_++;
        return dst;
    }

    void mark(int state, int i) {
        assert((0 <= i) && (i < num_state_classes()));
        state_classes_[i].insert(state);
    }
    void mark_as_accept(int state) {
        mark(state, 0);
    }

    void subst_state_name(int q, int nq) {
        if( initial_state_ == q )
            initial_state_ = nq;

        for( int i = 0; i < int(state_classes_.size()); ++i ) {
            if( belong(q, i) ) {
                state_classes_[i].erase(q);
                state_classes_[i].insert(nq);
            }
        }

        for( int i = 0; i < num_states_; ++i ) {
            for( size_t j = 0; j < edges_[i].size(); ++j ) {
                if( edges_[i][j].second == q )
                    edges_[i][j].second = nq;
            }
        }
    }

    // operations
    void remove_redundant_non_accepting_states() {
        bool change = true;
        while( change ) {
            change = false;
            int sink = -1;
            for( int q = 0; q < num_states_; ++q ) {
                if( is_sink(q) && !accept(q) ) {
                    sink = q;
                    break;
                }
            }

            if( sink != -1 ) {
                // swap sink and last state
                if( sink < num_states_ - 1 ) {
                    subst_state_name(sink, num_states_);

                    // swap rows: sink w/ num_states - 1
                    std::vector<std::pair<int, int> > row(edges_[sink]);
                    edges_[sink] = edges_[num_states_ - 1];
                    edges_[num_states_ - 1] = row;
                    subst_state_name(num_states_ - 1, sink);

                    subst_state_name(num_states_, num_states_ - 1);
                    sink = num_states_ - 1;
                }

                // remove last state
                assert(sink == num_states_ - 1);
                if( sink != initial_state_ ) {
                    // remove all transitions going to last state
                    for( int q = 0; q < num_states_; ++q ) {
                        for( int i = 0; i < edges_[q].size(); ++i ) {
                            if( edges_[q][i].second == sink ) {
                                edges_[q][i] = edges_[q].back();
                                edges_[q].pop_back();
                                --i;
                            }
                        }
                    }
                    edges_.pop_back();
                    --num_states_;
                    change = true;
                }
            }
        }
    }

    // output
    void dump(std::ostream &os) const {
        // dump parameters
        os << num_states_ << " " << initial_state_;
        if( num_state_classes() > 1 )
            os << " " << num_state_classes();
        os << std::endl;

        // dump labels
        os << num_labels_;
        for( typename std::map<T, int>::const_iterator it = labels_map_.begin(); it != labels_map_.end(); ++it )
            os << " " << it->first;
        os << std::endl;

        // dump state classes
        for( int i = 0; i < int(state_classes_.size()); ++i ) {
            os << state_classes_[i].size();
            for( std::set<int>::const_iterator it = state_classes_[i].begin(); it != state_classes_[i].end(); ++it )
                os << " " << *it;
            os << std::endl;
        }

        // dump transitions
        for( int q = 0; q < num_states_; ++q ) {
            os << edges_[q].size();
            for( size_t i = 0; i < edges_[q].size(); ++i ) {
                const T &label = get_label(edges_[q][i].first);
                int t = edges_[q][i].second;
                os << " " << label << " " << t;
            }
            os << std::endl;
        }
    }
    void dump_dot(std::ostream &os) const {
        // output comments
        if( initial_state_ != -1 ) os << "// initial state: q" << initial_state_ << std::endl;

        for( int i = 0; i < int(state_classes_.size()); ++i ) {
            if( i == 0 )
                os << "// accepting states:";
            else
                os << "// other state class:";
            for( std::set<int>::const_iterator it = state_classes_[i].begin(); it != state_classes_[i].end(); ++it )
                os << " " << *it;
            os << std::endl;
        }

        for( int q = 0; q < num_states_; ++q ) {
            for( size_t i = 0; i < edges_[q].size(); ++i ) {
                int label_index = edges_[q][i].first;
                const T &label = get_label(label_index);
                int t = edges_[q][i].second;
                os << "// edge " << q << " -> " << t << " w/ label " << label << std::endl;
            }
        }

        os << "digraph dfa {" << std::endl;

        // initial and state classes
        if( initial_state_ != -1 ) os << "    init [shape = point];" << std::endl;
        for( int i = 0; i < int(state_classes_.size()); ++i ) {
            for( std::set<int>::const_iterator it = state_classes_[i].begin(); it != state_classes_[i].end(); ++it ) {
                if( i == 0 )
                    os << "    " << *it << " [shape = doublecircle";
                else
                    os << "    " << *it << " [shape = hexagon";
                if( !state_labels_.at(*it).empty() )
                    os << ", label = \"" << state_labels_.at(*it) << "\"";
                os << "];" << std::endl;
            }
        }

        // other states
        for( int q = 0; q < num_states_; ++q ) {
            if( !marked(q) ) {
                os << "    " << q << " [shape = circle";
                if( !state_labels_.at(q).empty() )
                    os << ", label = \"" << state_labels_.at(q) << "\"";
                os << "];" << std::endl;
            }
        }

        // edges
        for( int q = 0; q < num_states_; ++q ) {
            for( size_t i = 0; i < edges_[q].size(); ++i ) {
                const T &label = get_label(edges_[q][i].first);
                int t = edges_[q][i].second;
                os << "    " << q << " -> " << t << " [label=\"" << label << "\"];" << std::endl;
            }
        }
        if( initial_state_ != -1 ) os << "    init -> " << initial_state_ << ";" << std::endl;
        os << "}" << std::endl;
    }

    void read(std::istream &is) {
        // skip over comments in first part of file
        std::string line;
        while( getline(is, line) && (line[0] == '#') );
        assert(!line.empty() && (line[0] != '#'));

        // read parameters
        std::istringstream iss(line);
        int num_states, initial_state, num_state_classes;
        iss >> num_states >> initial_state;
        if( iss.rdbuf()->in_avail() == 0 ) {
            std::cout << "HOLA.0" << std::endl;
            num_state_classes = 1;
        } else {
            std::cout << "HOLA.1" << std::endl;
            iss >> num_state_classes;
        }

        // add states and set initial state
        for( int i = 0; i < num_states; ++i )
            add_state();

        if( initial_state >= 0 )
            set_initial_state(initial_state);

        // read labels
        int num_labels;
        is >> num_labels;
        for( int i = 0; i < num_labels; ++i ) {
            T label;
            is >> label;
            add_label(label);
        }

        // read state classes: first class is accepting states
        for( int i = 0; i < num_state_classes; ++i ) {
            assert(state_classes_.size() == i);
            int num_states_in_class;
            is >> num_states_in_class;
            std::set<int> state_class;
            for( int j = 0; j < num_states_in_class; ++j ) {
                int state;
                is >> state;
                state_class.insert(state);
            }
            state_classes_.emplace_back(std::move(state_class));
        }

        // read edges
        for( int src = 0; src < num_states; ++src ) {
            int num_edges;
            is >> num_edges;
            for( int i = 0; i < num_edges; ++i ) {
                T label;
                int dst;
                is >> label >> dst;
                int label_index = get_label_index(label);
                if( (label_index == -1) || (dst < 0) || (dst >= num_states) ) {
                    std::cout << "warning: unrecognized label '" << label << "'."
                              << " Skipping edge: (" << src << "," << label << "," << dst << ")"
                              << std::endl;
                    continue;
                }
                add_edge(src, label_index, dst);
            }
        }
    }
    static const DFA<T>* read_dump(std::istream &is) {
        DFA<T> *dfa = new DFA();
        dfa->read(is);
        return dfa;
    }
};

}; // namespace DFA

#endif

