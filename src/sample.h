#ifndef SAMPLE_H
#define SAMPLE_H

#include <cassert>
#include <iostream>
#include <string>
#include <vector>

#include "apta.h"

namespace DFA {

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

