CXX=clang++

dfa:	dfa.cc sat.h sample.h
	$(CXX) -std=c++14 -o dfa dfa.cc

dfa.d:	dfa.cc sat.h sample.h
	$(CXX) -g -std=c++14 -o dfa.d dfa.cc

clean:
	rm -f *~

