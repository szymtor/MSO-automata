import Lax52.NFARecognizable
import Lax52.WordStructure

/-!
---
title: Finite automata are MSO-definable
type: theorem
---

Every nondeterministic finite automaton over a finite alphabet has a monadic
second-order sentence that holds on exactly the words accepted by the
automaton.
-/

namespace Lax52.NFAToMSO

open Lax52.MSOSyntax
open Lax52.WordStructure

universe u

axiom nfa_definable_by_mso {Sigma : Type u} [Fintype Sigma]
    {Q : Type} [Fintype Q] (M : NFA Sigma Q) :
  ∃ phi : MSOSyntax.Sentence (wordLanguage Sigma), M.accepts = sentenceLanguage phi

end Lax52.NFAToMSO
