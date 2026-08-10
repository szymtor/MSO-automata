import Lax52.NFAToMSO
import Lax52.MSOToNFA

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

namespace Lax52.MSOAutomataEquivalence

open Lax52.MSOSyntax
open Lax52.WordStructure
open Lax52.NFARecognizable

universe u

axiom nfaRecognizable_iff_msoDefinable {Sigma : Type u} [Fintype Sigma]
    (L : _root_.Language Sigma) :
  NFARecognizable L ↔
    ∃ phi : MSOSyntax.Sentence (wordLanguage Sigma), L = sentenceLanguage phi

end Lax52.MSOAutomataEquivalence
