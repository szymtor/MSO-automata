import Lax146103.NFARecognizable
import Lax146103.WordStructure

/-!
---
title: Finite automata are MSO-definable
type: theorem
---

Every nondeterministic finite automaton over a finite alphabet has a monadic
second-order sentence that holds on exactly the words accepted by the
automaton.
-/

namespace Lax146103.NFAToMSO

open Lax146103.MSOSyntax
open Lax146103.WordStructure

universe u

axiom nfa_definable_by_mso {Sigma : Type u} [Fintype Sigma]
    {Q : Type} [Fintype Q] (M : NFA Sigma Q) :
  ∃ phi : MSOSyntax.Sentence (wordLanguage Sigma), M.accepts = sentenceLanguage phi

end Lax146103.NFAToMSO
