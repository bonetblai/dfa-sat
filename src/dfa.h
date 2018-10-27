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
    std::set<int> accept_;

    std::vector<T> labels_;
    std::vector<std::vector<std::pair<int, int> > > edges_;
    std::map<T, int> labels_map_;

  public:
    DFA(int num_states = 0)
      : num_states_(num_states), num_labels_(0), num_edges_(0), initial_state_(-1) {
        edges_ = std::vector<std::vector<std::pair<int, int> > >(num_states_);
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

    bool accept(int state) const {
        return accept_.find(state) != accept_.end();
    }
    const std::set<int>& accept() const {
        return accept_;
    }

    int get_label_index(const T &label) const {
        typename std::map<T, int>::const_iterator it = labels_map_.find(label);
        return it == labels_map_.end() ? -1 : it->second;
    }
    T get_label(int index) const {
        assert((0 <= index) && (index < num_labels_));
        return labels_[index];
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
        return num_states_++;
    }
    void set_initial_state(int state) {
        assert((0 <= state) && (state < num_states_));
        initial_state_ = state;
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
    void mark_as_accept(int state) {
        assert((0 <= state) && (state < num_states_));
        accept_.insert(state);
    }

    void subst_state_name(int q, int nq) {
        if( initial_state_ == q )
            initial_state_ = nq;
        if( accept(q) ) {
            accept_.erase(q);
            accept_.insert(nq);
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

    // input/out
    void dump(std::ostream &os) {
        os << num_states_ << " " << initial_state_ << std::endl;
        os << num_labels_;
        for( typename std::map<T, int>::const_iterator it = labels_map_.begin(); it != labels_map_.end(); ++it )
            os << " " << it->first;
        os << std::endl;
        os << accept_.size();
        for( std::set<int>::const_iterator it = accept_.begin(); it != accept_.end(); ++it )
            os << " " << *it;
        os << std::endl;
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
    void dump_dot(std::ostream &os) {
        // output comments
        os << "// initial state: q" << initial_state_ << std::endl;
        os << "// accepting states:";
        for( std::set<int>::const_iterator it = accept_.begin(); it != accept_.end(); ++it )
            os << " q" << *it;
        os << std::endl;
        for( size_t q = 0; q < num_states_; ++q ) {
            for( size_t i = 0; i < edges_[q].size(); ++i ) {
                int label_index = edges_[q][i].first;
                const T &label = get_label(label_index);
                int t = edges_[q][i].second;
                os << "// edge q" << q << " -> q" << t << " w/ label " << label << std::endl;
            }
        }

        os << "digraph dfa {" << std::endl;
        os << "    node [shape = point ]; init;" << std::endl;
        os << "    node [shape = doublecircle];" << std::endl;
        for( std::set<int>::const_iterator it = accept_.begin(); it != accept_.end(); ++it )
            os << "    q" << *it << ";" << std::endl;

        os << "    node [shape = circle];" << std::endl;
        for( int q = 0; q < num_states_; ++q ) {
            for( size_t i = 0; i < edges_[q].size(); ++i ) {
                const T &label = get_label(edges_[q][i].first);
                int t = edges_[q][i].second;
                os << "    q" << q << " -> q" << t << " [label=\"" << label << "\"];" << std::endl;
            }
        }
        os << "    init -> q" << initial_state_ << ";" << std::endl;
        os << "}" << std::endl;
    }
};

}; // namespace DFA

#endif

