#ifndef GRAPH_H
#define GRAPH_H

#include <cassert>
#include <iostream>
#include <set>
#include <vector>

namespace Graph {

// Augmented Prefix Tree Acceptor (APTA)
class Undirected {
  protected:
    int num_vertices_;
    int num_edges_;
    std::vector<std::vector<int> > edges_;

  public:
    Undirected(int num_vertices = 0)
      : num_vertices_(num_vertices),
        num_edges_(0) {
        edges_ = std::vector<std::vector<int> >(num_vertices_);
    }
    virtual ~Undirected() = default;

    // accessors
    int num_vertices() const {
        return num_vertices_;
    }
    int num_edges() const {
        return num_edges_;
    }
    bool empty() const {
        return num_vertices_ == 0;
    }

    const std::vector<int>& edges(int src) const {
        assert((0 <= src) && (src < num_vertices_));
        return edges_[src];
    }

    // modifiers
    int add_vertex() {
        edges_.emplace_back();
        return num_vertices_++;
    }
    void add_vertices(int n) {
        assert(n >= 0);
        edges_.resize(n + edges_.size());
        num_vertices_ += n;
    }

    int add_edge(int src, int dst) {
        assert((0 <= src) && (src < num_vertices_));
        assert((0 <= dst) && (dst < num_vertices_));
        edges_[src].push_back(dst);
        edges_[dst].push_back(src);
        num_edges_ += 2;
        return dst;
    }

    // operations
    template <typename T>
    int find_large_clique_greedy(const T &subset, std::set<int> &clique) const {
        // look for vertex with largest degree
        int vertex = -1;
        int degree = -1;
        for( typename T::const_iterator it = subset.begin(); it != subset.end(); ++it ) {
            assert((*it >= 0) || (*it < num_vertices_));
            if( degree < int(edges_[*it].size()) ) {
                degree = edges_[*it].size();
                vertex = *it;
            }
        }
        assert((vertex >= 0) || (subset.size() == 0));
        if( vertex == -1 ) return 0;

        // initialize clique with vertex
        clique.clear();
        clique.insert(vertex);

        // extend clique by adding vertices with highest degree
        // connected to all vertices in clique
        int old_size = 0;
        while( old_size != int(clique.size()) ) {
            old_size = clique.size();

            int vertex = -1;
            int degree = -1;
            for( typename T::const_iterator it = subset.begin(); it != subset.end(); ++it ) {
                int v = *it;

                // check whether vertex v is a valid clique extension
                bool valid = true;
                for( std::set<int>::const_iterator jt = clique.begin(); valid && (jt != clique.end()); ++jt ) {
                    bool found = false;
                    for( size_t i = 0; i < edges_[v].size(); ++i ) {
                        if( edges_[v][i] == *jt ) {
                            found = true;
                            break;
                        }
                    }
                    valid = found;
                }
                if( !valid ) continue;

                // if it is a valid extension, select one with max degree
                if( degree < int(edges_[v].size()) ) {
                    degree = edges_[v].size();
                    vertex = v;
                }
            }

            // extend clique with vertex
            if( vertex != -1 ) {
                assert(clique.find(vertex) == clique.end());
                clique.insert(vertex);
            }
        }

        return clique.size();
    }

    int find_large_clique_greedy(std::set<int> &clique) const {
        std::vector<int> subset(0, num_vertices_ - 1);
        return find_large_clique_greedy(subset, clique);
    }

    // input/output
    void dump(std::ostream &os) const {
        os << num_vertices_ << " " << num_edges_ << std::endl;
        for( int v = 0; v < num_vertices_; ++v ) {
            os << edges_[v].size();
            for( size_t i = 0; i < edges_[v].size(); ++i )
                os << " " << edges_[v][i];
            os << std::endl;
        }
    }
};

}; // namespace GRAPH

std::ostream& operator<<(std::ostream &os, const Graph::Undirected &g) {
    g.dump(os);
    return os;
}

#endif

