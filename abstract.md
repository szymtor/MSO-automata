We formalize monadic second-order logic over arbitrary first-order languages,
using mathlib's structures and term semantics for the first-order fragment and
set-valued valuations for monadic variables.  We then represent a finite word
as its linearly ordered set of positions, with one unary predicate for each
alphabet letter.

For a finite alphabet, we prove the Büchi--Elgot--Trakhtenbrot correspondence
between MSO-definable languages of finite words and languages recognized by
nondeterministic finite automata.  The MSO-to-automata proof uses marked words
for valuations of free first- and second-order variables and proves regularity
by structural induction, with union, complement, and projection constructions.
The automata-to-MSO proof existentially guesses the state at every position and
expresses that these state predicates encode an initial, transition-respecting,
accepting run.  Empty words are handled separately in the constructed sentence.
