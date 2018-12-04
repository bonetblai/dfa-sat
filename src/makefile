CXX=clang++ -I.

dfa-sat:	dfa_sat.cc apta.h dfa.h graph.h sat.h theory.h sample.h
		$(CXX) -O3 -Wall -std=c++14 -o dfa-sat dfa_sat.cc

clean:
		rm -f dfa-sat *~

