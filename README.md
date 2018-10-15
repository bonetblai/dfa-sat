# dfa-sat
Learning Deterministic Finite Automata (DFA) from examples using SAT

Implements a reduction to sat for learning (synthesizing) a DFA 
that accepts a given set of strings, and rejects another given set. 
The input for the reduction is a file with the two set of strings
and an integer N. The output is a CNF theory that is satisfiable
iff there is a DFA with N states that is compatible with the input
file. In the positive case, the DFA can be obtained from a model
for the theory.

# Build

Got to src/ folder and make 'make'.

# Format

The file begins with a line containing two integers n and m
where n is the number of symbols in the alphabet, and m is
the number of samples (strings) in the file. Then, a line
containing the integer n followed by n blank-separated strings
specify the symbols in the input alphabet. (The symbols are
not necessarily of lenght equal to 1.)

For example, the file preamble

```
2 6
2 a b
```

tells that the file contains a sample of 6 strings made from
an alphabet of two 'symbols' which are ``a`` and ``b``.

The last part of the file contains the positive and negative
samples. First, a single line containing number p less than 
or equal to m tells that there are p positive samples (i.e.
strings that should be accepted by the DFA). After this line,
there are p lines, each containing one string. Each such line
begins with an integer that tells the length of the string (0
if the string is empty) followed by a blank-separated list of
symbols from the alphabet that make up the string.
The negative samples are specified in a similar way.

For example, the file

```
2 6
2 a b
3
1 a
4 a b a a
2 b b
3
3 a b b
1 b
0
```

describes a sample of 6 strings over the alphabet { a, b }
with 3 positive samples: ``a``, ``abaa`` and ``bb``, and
3 negative samples: ``abb``, ``b``, and the empty string.


