#ifndef SAT_THEORY_H
#define SAT_THEORY_H

#include <bitset>
#include <cassert>
#include <iostream>
#include <string>
#include <vector>

#include <sat.h>

namespace SAT {

class Theory {
  protected:
    const bool decode_;

    std::vector<std::pair<int, std::string> > var_offsets_;
    std::vector<const SAT::Var*> variables_;
    std::vector<const SAT::Literal*> literals_;

    std::vector<std::pair<int, const std::string> > comments_;
    std::vector<const SAT::Implication*> implications_;
    std::vector<std::pair<int, std::string> > imp_offsets_;

    mutable bool satisfiable_;
    mutable std::vector<bool> model_;

    virtual void build_variables() = 0;
    virtual void build_base() = 0;
    virtual void build_rest() = 0;

    void build_theory() {
        std::cout << "---------------- variables + literals ---------------" << std::endl;
        build_variables();
        build_literals();

        if( !decode_ ) {
            std::cout << "----------------- base implications -----------------" << std::endl;
            build_base();
            build_rest();
        }
        std::cout << "-----------------------------------------------------" << std::endl;
    }

  public:
    Theory(bool decode) : decode_(decode) { }
    virtual ~Theory() {
        clear_implications();
        clear_literals();
        clear_variables();
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

    void clear_variables() {
        for( size_t i = 0; i < variables_.size(); ++i )
            delete variables_[i];
        variables_.clear();
    }
    void clear_literals() {
        for( size_t i = 0; i < literals_.size(); ++i )
            delete literals_[i];
        literals_.clear();
    }
    int num_variables() const {
        return variables_.size();
    }

    void clear_implications() {
        for( size_t i = 0; i < implications_.size(); ++i )
            delete implications_[i];
        implications_.clear();
    }
    void add_implication(const SAT::Implication *IP) {
        implications_.push_back(IP);
    }
    int num_implications() const {
        return implications_.size();
    }

    void add_comment(const std::string &comment) {
        comments_.push_back(make_pair(implications_.size(), comment));
    }

    bool satisfiable() const {
        return satisfiable_;
    }
    const std::vector<bool>& model() const {
        return model_;
    }

    void build_literals() {
        for( size_t i = 0; i < variables_.size(); ++i )
            literals_.push_back(new SAT::Literal(*variables_[i], false));
        for( size_t i = 0; i < variables_.size(); ++i )
            literals_.push_back(new SAT::Literal(*variables_[i], true));
    }

    // readers
    void read_minisat_output(std::ifstream &is) const {
        std::string status;
        is >> status;
        satisfiable_ = status == "SAT";
        if( satisfiable_ ) {
            int var, lit;
            model_ = std::vector<bool>(variables_.size(), false);
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
    void dump(std::ostream &os) const {
        os << "p cnf " << variables_.size() << " " << implications_.size() << std::endl;
        size_t i = 0;
        for( size_t j = 0; j < implications_.size(); ++j ) {
            while( (i < comments_.size()) && (comments_[i].first == j) ) {
                os << "c " << comments_[i].second << std::endl;
                ++i;
            }
            implications_[j]->dump(os);
        }
        while( i < comments_.size() ) {
            os << "c " << comments_[i].second << std::endl;
            ++i;
        }
    }
    void print(std::ostream &os) const {
        size_t i = 0;
        for( size_t j = 0; j < implications_.size(); ++j ) {
            while( (i < comments_.size()) && (comments_[i].first == j) ) {
                os << "% " << comments_[i].second << std::endl;
                ++i;
            }
            implications_[j]->print(os, literals_);
            os << std::endl;
        }
        while( i < comments_.size() ) {
            os << "% " << comments_[i].second << std::endl;
            ++i;
        }
    }
    void print_implications(std::ostream &os, int start, int end) const {
        while( start < end ) {
            implications_[start++]->print(os, literals_);
            os << std::endl;
        }
    }

    void dump_model(std::ostream &os) const {
        for( size_t var = 0; var < variables_.size(); ++var ) {
            os << variables_[var] << " ";
        }
        os << "0" << std::endl;
    }
    void print_model(std::ostream &os) const {
        for( size_t var = 0; var < model_.size(); ++var ) {
            bool sign = model_[var];
            if( sign ) {
                assert(var < variables_.size());
                variables_[var]->print(os);
                os << std::endl;
            }
        }
    }
};

}; // namespace SAT

#endif

