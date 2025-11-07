This is a project created as part of my Undergraduate Honours Thesis. It is a
formalisation of Two-way Deterministic Finite Automata in
[Lean](https://lean-lang.org/about/), following the definition and proof of
equivalence to One-way DFAs given by Kozen in his book
[Automata and Computability](https://link.springer.com/book/10.1007/978-1-4612-1844-9).

It also contains a verified function for executing a 2DFA on an input in
guaranteed finite time, as well as a collection of tools for easily
characterising the language of a 2DFA by proving it is equivalent to some other
description, and some functions for outputting both 2DFAs and regular DFAs in
[Graphviz Dot format](https://graphviz.org/doc/info/lang.html) to allow for
automatic rendering of their state graphs. These tools are demonstrated by
applying them to some example automata.
