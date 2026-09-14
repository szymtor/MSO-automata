import Lax146103.NFAToMSO
import Lax146103.MSOToNFA

/-!
---
title: Büchi-Elgot-Trakhtenbrot theorem for finite words
type: theorem
---

Over a finite alphabet, a language of finite words is recognizable by a
nondeterministic finite automaton if and only if it is definable by a monadic
second-order sentence in the ordered word structure with one unary predicate
for each letter.
-/

namespace Lax146103.MSOAutomataEquivalence

open Lax146103.MSOSyntax
open Lax146103.WordStructure
open Lax146103.NFARecognizable

universe u

axiom nfaRecognizable_iff_msoDefinable {Sigma : Type u} [Fintype Sigma]
    (L : _root_.Language Sigma) :
  NFARecognizable L ↔
    ∃ phi : MSOSyntax.Sentence (wordLanguage Sigma), L = sentenceLanguage phi

end Lax146103.MSOAutomataEquivalence
