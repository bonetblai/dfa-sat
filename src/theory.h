#ifndef SAT_THEORY_H
#define SAT_THEORY_H

#include <cassert>
#include <iostream>
#include <fstream>
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
    std::vector<const Literal*> pos_literals_;
    std::vector<const Literal*> neg_literals_;

    std::vector<std::pair<int, const std::string> > comments_;
    std::vector<const Implication*> implications_;
    std::vector<std::pair<int, std::string> > imp_offsets_;

    mutable bool satisfiable_;
    mutable std::vector<bool> model_;

    std::set<std::string> at_most_k_constraints_;
    std::set<std::string> at_least_k_constraints_;
    std::set<std::string> equal_k_constraints_;

    virtual void build_variables() = 0;
    virtual void build_base() = 0;
    virtual void build_rest() = 0;

    void build_theory() {
        std::cout << "---------------- variables + literals ---------------" << std::endl;
        build_variables();
        build_literals();
        std::cout << "----------------- base implications -----------------" << std::endl;
        build_base();
        build_rest();
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
        assert((0 <= index) && (index < int(variables_.size())));
        return *variables_[index];
    }
    const Literal& literal(int index) const {
        assert(index != 0);
        assert((-int(variables_.size()) <= index) && (index <= int(variables_.size())));
        return index > 0 ? *pos_literals_[index - 1] : *neg_literals_[-index - 1];
    }

    void clear_variables() {
        for( size_t i = 0; i < variables_.size(); ++i )
            delete variables_[i];
        variables_.clear();
    }
    void clear_literals() {
        for( size_t i = 0; i < pos_literals_.size(); ++i )
            delete pos_literals_[i];
        pos_literals_.clear();
        for( size_t i = 0; i < neg_literals_.size(); ++i )
            delete neg_literals_[i];
        neg_literals_.clear();
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

    void build_literal(int index) {
        assert(pos_literals_.size() == neg_literals_.size());
        assert((0 <= index) && (index < int(variables_.size())) && (index >= int(pos_literals_.size())));
        pos_literals_.push_back(new Literal(*variables_[index], false));
        neg_literals_.push_back(new Literal(*variables_[index], true));
    }
    void build_literals() {
        for( size_t i = 0; i < variables_.size(); ++i )
            build_literal(i);
    }
    int new_variable(const std::string &name) {
        int index = variables_.size();
        variables_.push_back(new Var(index, name));
        return index;
    }
    int new_literal(const std::string &name) {
        int index = new_variable(name);
        build_literal(index);
        return index;
    }
    void push_new_vartype(const std::string &name) {
        var_offsets_.push_back(std::make_pair(variables_.size(), name));
    }
    int num_variables_in_last_block() const {
        assert(!var_offsets_.empty());
        return variables_.size() - var_offsets_.back().first;
    }
    int offset_of_last_block() const {
        assert(!var_offsets_.empty());
        return var_offsets_.back().first;
    }

    // support for pseudo boolean constraints
    void build_2_comparator(const std::string &prefix, int x1, int y1, std::vector<int> &z) { // z1 = max(x1,y1), z2 = min(x1,y1)
        // create new vars z1 and z2
        int z1 = new_literal(prefix + "_z1");
        int z2 = new_literal(prefix + "_z2");
        z.push_back(z1);
        z.push_back(z2);

        // top three clauses (required for at-least and equal)
        // x1 <= z2, y1 <= z2, x1 v y1 <= z1
        Implication *IP1 = new Implication;
        IP1->add_antecedent(1 + z2);
        IP1->add_consequent(1 + x1);
        add_implication(IP1);

        Implication *IP2 = new Implication;
        IP2->add_antecedent(1 + z2);
        IP2->add_consequent(1 + y1);
        add_implication(IP2);

        Implication *IP3 = new Implication;
        IP3->add_antecedent(1 + z1);
        IP3->add_consequent(1 + x1);
        IP3->add_consequent(1 + y1);
        add_implication(IP3);

        // bottom three clauses (required for at-most and equal)
        // x1 => z1, y1 => z1, x1 & y1 => z2
        Implication *IP4 = new Implication;
        IP4->add_antecedent(1 + x1);
        IP4->add_consequent(1 + z1);
        add_implication(IP4);

        Implication *IP5 = new Implication;
        IP5->add_antecedent(1 + y1);
        IP5->add_consequent(1 + z1);
        add_implication(IP5);

        Implication *IP6 = new Implication;
        IP6->add_antecedent(1 + x1);
        IP6->add_antecedent(1 + y1);
        IP6->add_consequent(1 + z2);
        add_implication(IP6);
    }
    void build_merge_network(const std::string &prefix, int n, const std::vector<int> &x, const std::vector<int> &y, std::vector<int> &z) {
        assert((n == 1) || (n % 2 == 0));
        assert((int(x.size()) == n) && (int(y.size()) == n));
        if( n == 1 ) {
            build_2_comparator(prefix + "_base", x[0], y[0], z);
        } else {
            int m = n >> 1;
            std::vector<int> x1(m), y1(m), z1;
            std::vector<int> x2(m), y2(m), z2;
            for( int i = 0; i < m; ++i ) {
                x1[i] = x[2*i];
                y1[i] = y[2*i];
                x2[i] = x[2*i+1];
                y2[i] = y[2*i+1];
            }

            build_merge_network(prefix + "_rec" + std::to_string(m), m, x1, y1, z1);
            assert(int(z1.size()) == n);
            build_merge_network(prefix + "_rec" + std::to_string(m), m, x2, y2, z2);
            assert(int(z2.size()) == n);

            z.push_back(z1[0]);
            for( int i = 0; i < n - 1; ++i )
                build_2_comparator(prefix + "_final_" + std::to_string(i) + "of" + std::to_string(n - 1), z2[i], z1[1 + i], z);
            z.push_back(z2.back());
        }
    }
    void build_sorting_network(const std::string &prefix, int n, const std::vector<int> &x, std::vector<int> &z) {
        assert((n > 0) && (n % 2 == 0));
        assert(int(x.size()) == n);
        if( n == 2 ) {
            build_2_comparator(prefix + "_base", x[0], x[1], z);
        } else {
            int m = n >> 1;
            std::vector<int> x1(&x[0], &x[m]), z1;
            assert(int(x1.size()) == m);
            build_sorting_network(prefix + "_rec" + std::to_string(m), m, x1, z1);
            std::vector<int> x2(&x[m], &x[n]), z2;
            assert(int(x2.size()) == m);
            build_sorting_network(prefix + "_rec" + std::to_string(m), m, x2, z2);
            build_merge_network(prefix + "_merge" + std::to_string(m), m, z1, z2, z);
        }
    }
    void pad_and_build_sorting_network(const std::string &prefix, const std::vector<int> &variables, std::vector<int> &z) {
        assert(!variables.empty());
        int n = 1;
        while( n < int(variables.size()) )
            n = n << 1;

        std::vector<int> x(variables);
        while( int(x.size()) < n ) {
            // pad one var
            int index = new_literal(prefix + "_pad_var" + std::to_string(x.size()));
            Implication *IP = new Implication;
            IP->add_consequent(-(1 + index));
            add_implication(IP);
            x.push_back(index);
        }
        assert(int(x.size()) == n);

        // build sorting network
        build_sorting_network(prefix + "_sort" + std::to_string(n), n, x, z);
    }

    void build_formulas_for_at_most_k(const std::string &prefix, const std::vector<int> &variables, int k) {
        // trivial cases
        if( k == 0 ) {
            for( int i = 0; i < int(variables.size()); ++i ) {
                Implication *IP = new Implication;
                IP->add_consequent(-(1 + variables[i]));
                add_implication(IP);
            }
            return;
        } else if ( k >= int(variables.size()) ) {
            return;
        }

        // check that we have not already issued these constraints
        if( (prefix != "") && (at_most_k_constraints_.find(prefix) != at_most_k_constraints_.end()) ) {
            std::cout << "error: at-most-k constraints for '" << prefix << "' already emited!" << std::endl;
            exit(0);
        }

#if 0
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
        }
#endif

        // issue constraints, handling special cases
        std::vector<int> z;
        pad_and_build_sorting_network(prefix, variables, z);

        Implication *IP = new Implication;
        IP->add_consequent(-(1 + z[k]));
        add_implication(IP);
    }
    void build_formulas_for_at_least_k(const std::string &prefix, const std::vector<int> &variables, int k) {
        assert((0 <= k) && (k <= int(variables.size())));

        // trivial cases
        if( k == 0 ) {
            return;
        } else if( k == int(variables.size()) ) {
            for( int i = 0; i < int(variables.size()); ++i ) {
                Implication *IP = new Implication;
                IP->add_consequent(1 + variables[i]);
                add_implication(IP);
            }
            return;
        }

        // check that we have not already issued these constraints
        if( (prefix != "") && (at_least_k_constraints_.find(prefix) != at_least_k_constraints_.end()) ) {
            std::cout << "error: at-least-k constraints for '" << prefix << "' already emited!" << std::endl;
            exit(0);
        }

        // issue constraints, handling special cases
        if( k == 1 ) {
            Implication *IP = new Implication;
            for( size_t i = 0; i < variables.size(); ++i )
                IP->add_consequent(1 + variables[i]);
            add_implication(IP);
            return;
        } else {
            std::vector<int> z;
            pad_and_build_sorting_network(prefix, variables, z);

            Implication *IP = new Implication;
            IP->add_consequent(1 + z[k - 1]);
            add_implication(IP);
        }
    }
    void build_formulas_for_equal_to_k(const std::string &prefix, const std::vector<int> &variables, int k) {
        assert((0 <= k) && (k <= int(variables.size())));

        // trivial cases
        if( k == int(variables.size()) ) {
            for( int i = 0; i < int(variables.size()); ++i ) {
                Implication *IP = new Implication;
                IP->add_consequent(1 + variables[i]);
                add_implication(IP);
            }
            return;
        }

        // check that we have not already issued these constraints
        if( (prefix != "") && (equal_k_constraints_.find(prefix) != equal_k_constraints_.end()) ) {
            std::cout << "error: equal-k constraints for '" << prefix << "' already emited!" << std::endl;
            exit(0);
        }

        std::vector<int> z;
        pad_and_build_sorting_network(prefix, variables, z);

        Implication *IP1 = new Implication;
        IP1->add_consequent(-(1 + z[k]));
        add_implication(IP1);

        Implication *IP2 = new Implication;
        IP2->add_consequent(1 + z[k - 1]);
        add_implication(IP2);
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
            while( (i < comments_.size()) && (comments_[i].first == int(j)) ) {
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
            while( (i < comments_.size()) && (comments_[i].first == int(j)) ) {
                os << "% " << comments_[i].second << std::endl;
                ++i;
            }
            implications_[j]->print(os, pos_literals_, neg_literals_);
            os << std::endl;
        }
        while( i < comments_.size() ) {
            os << "% " << comments_[i].second << std::endl;
            ++i;
        }
    }
    void print_implications(std::ostream &os, int start, int end) const {
        while( start < end ) {
            implications_[start++]->print(os, pos_literals_, neg_literals_);
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

class VarClass {
  protected:
    int base_;
    std::string varname_;
    std::vector<int> multipliers_;
    bool initialized_;
    int verbose_;

    template<typename T, typename ...Ts>
    void fill_multipliers(const T &first, const Ts... args) {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        multipliers_.push_back(first.size());
        fill_multipliers(args...);
    }
    template<typename T>
    void fill_multipliers(const T &first) {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        multipliers_.push_back(first.size());
    }

    template<typename T, typename ...Ts>
    void create_vars_helper2(SAT::Theory &theory,
                             std::vector<int> &tuple,
                             const T &first,
                             const Ts... args) {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        for( size_t i = 0; i < first.size(); ++i ) {
            tuple.push_back(first[i]);
            create_vars_helper(theory, tuple, args...);
            tuple.pop_back();
        }
    }

    template<typename ...Ts>
    void create_vars_helper(SAT::Theory &theory,
                            std::vector<int> &tuple,
                            const Ts... args) {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        create_vars_helper2(theory, tuple, args...);
    }

    template<typename ...Ts>
    void create_vars(SAT::Theory &theory, const Ts... args) {
        theory.push_new_vartype(varname_);
        std::vector<int> tuple;
        create_vars_helper(theory, tuple, args...);
        if( verbose_ > 0 ) {
            std::cout << varname_
                      << ": #variables=" << theory.num_variables_in_last_block()
                      << ", offset=" << theory.offset_of_last_block()
                      << std::endl;
        }
    }

    template<typename T, typename ...Ts> int calculate_index_helper(int i, int index, T &first, Ts... args) const {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        assert(i < multipliers_.size());
        assert((0 <= first) && (first < multipliers_.at(i)));
        int new_index = index * multipliers_.at(i) + first;
        return calculate_index(1 + i, new_index, args...);
    }
    
  public:
    VarClass(int verbose = 1) : initialized_(false), verbose_(verbose) { }
    virtual ~VarClass() = default;

    int base() const {
        return base_;
    }
    const std::string& varname() const {
        return varname_;
    }
    const std::vector<int>& multipliers() const {
        return multipliers_;
    }
    int verbose() const {
        return verbose_;
    }
    void set_verbose(int verbose) {
        verbose_ = verbose;
    }

    template<typename ...Ts> void initialize(SAT::Theory &theory, const std::string &varname, Ts... args) {
        assert(!initialized_);
        base_ = theory.num_variables();
        varname_ = varname;
        fill_multipliers(args...);
        create_vars(theory, args...);
        initialized_ = true;
    }

    template<typename ...Ts> int calculate_index(int i, int index, Ts... args) const {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        return calculate_index_helper(i, index, args...);
    }
    template<typename ...Ts> int operator()(Ts... args) const {
        return base_ + calculate_index(0, 0, args...);
    }
    int operator()(const std::vector<int> &tuple) const {
        assert(multipliers_.size() == tuple.size());
        int index = 0;
        for( size_t i = 0; i < tuple.size(); ++i ) {
            assert((0 <= tuple[i]) && (tuple[i] < multipliers_.at(i)));
            index *= multipliers_.at(i);
            index += tuple[i];
        }
        return base_ + index;
    }
};

template<>
inline void VarClass::create_vars_helper(SAT::Theory &theory,
                                         std::vector<int> &tuple) {
    //std::cout << __PRETTY_FUNCTION__ << std::endl;
    std::string name(varname_);
    if( !tuple.empty() ) name += "(";
    for( size_t i = 0; i < tuple.size(); ++i ) {
        if( i > 0 ) name += ",";
        name += std::to_string(tuple[i]);
    }
    if( !tuple.empty() ) name += ")";

    int var_index = theory.new_variable(name);
    if( verbose_ > 1 ) {
        std::cout << "create_var:"
                  << " name=" << name
                  << ", index=" << var_index
                  << std::endl;
    }
    assert(var_index == (*this)(tuple));
}

template<>
inline int VarClass::calculate_index(int i, int index) const {
    //std::cout << __PRETTY_FUNCTION__ << std::endl;
    assert(i == int(multipliers_.size()));
    return index;
}

}; // namespace SAT

#endif

