#ifndef APTA_H
#define APTA_H

#include <cassert>
#include <iostream>
#include <deque>
#include <map>
#include <set>
#include <vector>

#include "graph.h"

namespace DFA {

// Augmented Prefix Tree Acceptor (APTA)
template<typename T> class APTA {
  protected:
    int num_vertices_;
    int num_labels_;
    int num_edges_;
    int initial_vertex_;
    std::set<int> accept_vertices_;
    std::set<int> reject_vertices_;
    std::vector<T> labels_;
    std::vector<std::pair<int, int> > parents_;
    std::vector<std::vector<std::pair<int, int> > > edges_;
    std::map<T, int> labels_map_;

  public:
    APTA() : num_vertices_(0), num_labels_(0), num_edges_(0), initial_vertex_(-1) { }
    virtual ~APTA() = default;

    // accessors
    int num_vertices() const {
        return num_vertices_;
    }
    int num_labels() const {
        return num_labels_;
    }
    int num_edges() const {
        return num_edges_;
    }
    int initial_vertex() const {
        return initial_vertex_;
    }

    std::pair<int, int> parent(int vertex) const {
        assert((0 <= vertex) && (vertex < num_vertices_));
        return parents_[vertex];
    }
    int type(int vertex) const {
        if( accept_vertices_.find(vertex) != accept_vertices_.end() )
            return 0;
        else if( reject_vertices_.find(vertex) != reject_vertices_.end() )
            return 1;
        else
            return 2;
    }

    const std::set<int>& accept() const {
        return accept_vertices_;
    }
    const std::set<int>& reject() const {
        return reject_vertices_;
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
        assert((0 <= src) && (src < num_vertices_));
        for( size_t i = 0; i < edges_[src].size(); ++i ) {
            if( edges_[src][i].first == label_index )
                return edges_[src][i].second; // dst
        }
        return -1;
    }
    bool is_edge(int src, int dst) const {
        assert((0 <= src) && (src < num_vertices_));
        for( size_t i = 0; i < edges_[src].size(); ++i ) {
            if( edges_[src][i].second == dst )
                return true;
        }
        return false;
    }
    const std::vector<std::pair<int, int> >& edges(int src) const {
        assert((0 <= src) && (src < num_vertices_));
        return edges_[src];
    }

    // modifiers
    int add_vertex() {
        parents_.push_back(std::make_pair(-1, -1));
        edges_.push_back(std::vector<std::pair<int, int> >());
        return num_vertices_++;
    }
    void set_initial_vertex(int vertex) {
        assert((0 <= vertex) && (vertex < num_vertices_));
        initial_vertex_ = vertex;
    }
    int add_label(const T &label) {
        labels_.push_back(label);
        labels_map_.insert(std::make_pair(label, num_labels_));
        return num_labels_++;
    }
    int add_edge(int src, int label_index, int dst) {
        assert(label_index != -1);
        assert((0 <= src) && (src < num_vertices_));
        assert(parents_[dst].first == -1);
        parents_[dst] = std::make_pair(src, label_index);
        edges_[src].push_back(std::make_pair(label_index, dst));
        num_edges_++;
        return dst;
    }
    void mark_as_accept(int vertex) {
        assert((0 <= vertex) && (vertex < num_vertices_));
        assert(reject_vertices_.find(vertex) == reject_vertices_.end());
        accept_vertices_.insert(vertex);
    }
    void mark_as_reject(int vertex) {
        assert((0 <= vertex) && (vertex < num_vertices_));
        assert(accept_vertices_.find(vertex) == accept_vertices_.end());
        reject_vertices_.insert(vertex);
    }

    // operations
    void build_induced_undirected_graph(Graph::Undirected &g) const {
        // initialize empty graph
        assert(g.empty());
        g.add_vertices(num_vertices());

        // initialize queue with all pairs of accept/reject states
        std::deque<std::pair<int, int> > queue;
        for( std::set<int>::const_iterator it = accept().begin(); it != accept().end(); ++it ) {
            for( std::set<int>::const_iterator jt = reject().begin(); jt != reject().end(); ++jt ) {
                assert(*it != *jt);
                if( *it < *jt )
                    queue.emplace_back(*it, *jt);
                else
                    queue.emplace_back(*jt, *it);
            }
        }

        // process queue while keeping record of added edges
        std::set<std::pair<int, int> > added;
        while( !queue.empty() ) {
            std::pair<int, int> p = queue.front();
            assert(p.first < p.second);
            queue.pop_front();

            if( added.find(p) == added.end() ) {
                added.insert(p);
                g.add_edge(p.first, p.second);

                // if label leading to pair states are the same, add pair for parents
                std::pair<int, int> pa_first = parent(p.first);
                std::pair<int, int> pa_second = parent(p.second);
                if( pa_first.second == pa_second.second ) {
                    if( pa_first.first < pa_second.first )
                        queue.emplace_back(pa_first.first, pa_second.first);
                    else if( pa_first.first > pa_second.first )
                        queue.emplace_back(pa_second.first, pa_first.first);
                }
            }
        }
    }
};

}; // namespace DFA

#endif

