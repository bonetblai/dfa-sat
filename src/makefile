SAT=../sat-engine
CXX=clang++ -I. -I$(SAT)/include

dfa-sat:
		$(CXX) -O3 -Wall -std=c++14 -o dfa-sat dfa_sat.cc

clean:
		rm -f dfa-sat *~

dfa-sat:	dfa_sat.cc
dfa-sat:	apta.h dfa.h graph.h sample.h
dfa-sat:	$(SAT)/include/sat/encoder/sat.h $(SAT)/include/sat/encoder/theory.h


