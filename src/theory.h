#ifndef SAT_THEORY_H
#define SAT_THEORY_H

#include <bitset>
#include <cassert>
#include <iostream>
#include <set>
#include <string>
#include <vector>

#include <sat.h>

namespace SAT {

class Theory {
  protected:
    const bool decode_;

    std::vector<std::pair<int, std::string> > var_offsets_;
    std::vector<const Var*> variables_;
    std::vector<const Literal*> literals_;

    std::vector<std::pair<int, const std::string> > comments_;
    std::vector<const Implication*> implications_;
    std::vector<std::pair<int, std::string> > imp_offsets_;

    mutable bool satisfiable_;
    mutable std::vector<bool> model_;

    std::set<std::string> at_most_k_constraints_;
    std::set<std::string> at_least_k_constraints_;

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

    // unimplemented virtual function to decode model
    virtual void decode_model(std::ostream &os) const = 0;

    const Var& variable(int index) const {
        assert((0 <= index) && (index < variables_.size()));
        return *variables_[index];
    }
    const Literal& literal(int index) const {
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
    void add_implication(const Implication *IP) {
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
            literals_.push_back(new Literal(*variables_[i], false));
        for( size_t i = 0; i < variables_.size(); ++i )
            literals_.push_back(new Literal(*variables_[i], true));
    }

    // support for at-most-k pseudo boolean constraints
    void build_variables_for_at_most_k(const std::string &prefix, const std::vector<int> &variables, int k) {
        assert((0 <= k) && (k <= variables.size()));
        if( k > 2 ) {
            std::cout << "error: unsupported formulas for at-most-k for k > 2: k=" << k << std::endl;
            exit(0);
        }
    }
    void build_variables_for_at_least_k(const std::string &prefix, const std::vector<int> &variables, int k) {
        assert((0 <= k) && (k <= variables.size()));
        if( k > 1 ) {
            std::cout << "error: unsupported formulas for at-least-k for k > 1: k=" << k << std::endl;
            exit(0);
        }
    }
    void build_variables_for_equal_to_k(const std::string &prefix, const std::vector<int> &variables, int k) {
        assert((0 <= k) && (k <= variables.size()));
        build_variables_for_at_least_k(prefix, variables, k);
        build_variables_for_at_most_k(prefix, variables, k);
    }

    void build_formulas_for_at_most_k(const std::string &prefix, const std::vector<int> &variables, int k) {
        assert((0 <= k) && (k <= variables.size()));

        // check we have not already issued these constraints
        if( (prefix != "") && (at_most_k_constraints_.find(prefix) != at_most_k_constraints_.end()) ) {
            std::cout << "error: at-most-k constraints for '" << prefix << "' already emited!" << std::endl;
            exit(0);
        }

        // generate required variables
        build_variables_for_at_most_k(prefix, variables, k);

        // provisional, direct encoding
        if( k == 1 ) {
            for( size_t i = 0; i < variables.size(); ++i ) {
                assert((0 <= variables[i]) && (variables[i] < num_variables()));
                for( size_t j = 1 + i; j < variables.size(); ++j ) {
                    Implication *IP = new Implication;
                    IP->add_consequent(-(1 + variables[i]));
                    IP->add_consequent(-(1 + variables[j]));
                    add_implication(IP);
                }
            }
        } else if( k == 2 ) {
            for( size_t i = 0; i < variables.size(); ++i ) {
                assert((0 <= variables[i]) && (variables[i] < num_variables()));
                for( size_t j = 1 + i; j < variables.size(); ++j ) {
                    for( size_t l = 0; l < variables.size(); ++l ) {
                        if( (l == i) || (l == j) ) continue;
                        Implication *IP = new Implication;
                        IP->add_antecedent(1 + variables[i]);
                        IP->add_antecedent(1 + variables[j]);
                        IP->add_consequent(-(1 + variables[l]));
                        add_implication(IP);
                    }
                }
            }
        } else {
            std::cout << "error: unsupported formulas for at-most-k for k > 2: k=" << k << std::endl;
            exit(0);
        }
    }
    void build_formulas_for_at_least_k(const std::string &prefix, const std::vector<int> &variables, int k) {
        assert((0 <= k) && (k <= variables.size()));

        // check we have not already issued these constraints
        if( (prefix != "") && (at_least_k_constraints_.find(prefix) != at_least_k_constraints_.end()) ) {
            std::cout << "error: at-least-k constraints for '" << prefix << "' already emited!" << std::endl;
            exit(0);
        }

        // generate required variables
        build_variables_for_at_least_k(prefix, variables, k);

        // provisional, direct encoding
        if( k == 1 ) {
            Implication *IP = new Implication;
            for( size_t i = 0; i < variables.size(); ++i )
                IP->add_consequent(1 + variables[i]);
            add_implication(IP);
        } else {
            std::cout << "error: unsupported formulas for at-least-k for k > 1: k=" << k << std::endl;
            exit(0);
        }
    }
    void build_formulas_for_equal_to_k(const std::string &prefix, const std::vector<int> &variables, int k) {
        assert((0 <= k) && (k <= variables.size()));
        build_formulas_for_at_least_k(prefix, variables, k);
        build_formulas_for_at_most_k(prefix, variables, k);
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
                if( lit == 0 ) break;
                var = lit > 0 ? lit - 1 : -lit - 1;
                assert(var == int(i));
                model_[var] = lit > 0;
            }
            if( lit != 0 ) {
                is >> lit;
                assert(lit == 0);
            }
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

