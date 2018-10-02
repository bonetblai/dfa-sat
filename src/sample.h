#ifndef SAMPLE_H
#define SAMPLE_H

#include <cassert>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>

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
};

class Sample {
  protected:
    const int num_symbols_;
    const int num_histories_;
    std::vector<std::string> language_;
    std::vector<std::vector<std::string> > positive_histories_;
    std::vector<std::vector<std::string> > negative_histories_;

  public:
    Sample(int num_symbols, int num_histories)
      : num_symbols_(num_symbols),
        num_histories_(num_histories) {
    }
    virtual ~Sample() { }

    int num_symbols() const {
        return num_symbols_;
    }
    int num_histories() const {
        return num_histories_;
    }
    int num_positive_histories() const {
        return positive_histories_.size();
    }
    int num_negative_histories() const {
        return negative_histories_.size();
    }

    APTA<std::string>* build_APTA() const {
        APTA<std::string> *apta = new APTA<std::string>;
        apta->set_initial_vertex(apta->add_vertex());

        for( size_t i = 0; i < positive_histories_.size(); ++i ) {
            int current = apta->initial_vertex();
            for( size_t j = 0; j < positive_histories_[i].size(); ++j ) {
                const std::string &label = positive_histories_[i][j];
                int label_index = apta->get_label_index(label);
                if( label_index == -1 ) label_index = apta->add_label(label);
                int next = apta->edge(current, label_index);
                if( next == -1 ) {
                    int new_vertex = apta->add_vertex();
                    next = apta->add_edge(current, label_index, new_vertex);
                }
                current = next;
            }
            assert(apta->type(current) != 1);
            apta->mark_as_accept(current);
        }

        for( size_t i = 0; i < negative_histories_.size(); ++i ) {
            int current = apta->initial_vertex();
            for( size_t j = 0; j < negative_histories_[i].size(); ++j ) {
                const std::string &label = negative_histories_[i][j];
                int label_index = apta->get_label_index(label);
                if( label_index == -1 ) label_index = apta->add_label(label);
                int next = apta->edge(current, label_index);
                if( next == -1 ) {
                    int new_vertex = apta->add_vertex();
                    next = apta->add_edge(current, label_index, new_vertex);
                }
                current = next;
            }
            assert(apta->type(current) != 0);
            apta->mark_as_reject(current);
        }

        return apta;
    }

    // output
    void dump(std::ostream &os) const {
        os << num_symbols_ << " " << num_histories_ << std::endl;

        os << language_.size() << std::endl;
        for( size_t i = 0; i < language_.size(); ++i )
            os << " " << language_[i];
        os << std::endl;

        os << positive_histories_.size() << std::endl;
        for( size_t i = 0; i < positive_histories_.size(); ++i ) {
            os << positive_histories_[i].size();
            for( size_t j = 0; i < positive_histories_[i].size(); ++j )
                os << " " << positive_histories_[i][j];
            os << std::endl;
        }

        os << negative_histories_.size() << std::endl;
        for( size_t i = 0; i < negative_histories_.size(); ++i ) {
            os << negative_histories_[i].size();
            for( size_t j = 0; i < negative_histories_[i].size(); ++j )
                os << " " << negative_histories_[i][j];
            os << std::endl;
        }
    }
    void print(std::ostream &os) const {
        os << "Sample stats: #symbols=" << num_symbols_
           << ", #histories=" << num_histories_
           << std::endl;

        for( size_t i = 0; i < positive_histories_.size(); ++i ) {
            os << "positive history:";
            for( size_t j = 0; j < positive_histories_[i].size(); ++j )
                os << " " << positive_histories_[i][j];
            os << std::endl;
        }

        for( size_t i = 0; i < negative_histories_.size(); ++i ) {
            os << "negative history:";
            for( size_t j = 0; j < negative_histories_[i].size(); ++j )
                os << " " << negative_histories_[i][j];
            os << std::endl;
        }
    }

    // readers
    void read(std::istream &is) {
        // read symbols
        int n;
        is >> n;
        assert(n == num_symbols_);
        for( int i = 0; i < num_symbols_; ++i ) {
            std::string symbol;
            is >> symbol;
            language_.push_back(symbol);
        }

        // read positive histories
        is >> n;
        assert((0 <= n) && (n <= num_histories_));
        for( int i = 0; i < n; ++i ) {
            int m;
            is >> m;
            positive_histories_.emplace_back(std::vector<std::string>());
            for( int j = 0; j < m; ++j ) {
                std::string symbol;
                is >> symbol;
                positive_histories_[i].push_back(symbol);
            }
        }

        // read negative histories
        is >> n;
        assert(positive_histories_.size() + n == num_histories_);
        for( int i = 0; i < n; ++i ) {
            int m;
            is >> m;
            negative_histories_.emplace_back(std::vector<std::string>());
            for( int j = 0; j < m; ++j ) {
                std::string symbol;
                is >> symbol;
                negative_histories_[i].push_back(symbol);
            }
        }
    }
    static const Sample* read_dump(std::istream &is) {
        int num_symbols, num_histories;
        is >> num_symbols >> num_histories;
        Sample *S = new Sample(num_symbols, num_histories);
        S->read(is);
        std::cout << "Sample::read_dump: "
                  << "#symbols=" << S->num_symbols()
                  << ", #num-positive_histories=" << S->num_positive_histories()
                  << ", #num-negative_histories=" << S->num_negative_histories()
                  << std::endl;
        return S;
    }
};

}; // namespace DFA

#endif

