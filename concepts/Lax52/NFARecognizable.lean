import Lax52.WordStructure

/-!
---
title: Recognition by a finite nondeterministic automaton
type: definition
---

A language is NFA-recognizable when it is accepted by a mathlib
nondeterministic automaton whose state type is finite.
-/

namespace Lax52.NFARecognizable

open Lax52.WordStructure

universe u

/-- Recognition by an NFA with a finite state type. -/
def NFARecognizable {Sigma : Type u} (L : _root_.Language Sigma) : Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, ∃ M : NFA Sigma Q, M.accepts = L

end Lax52.NFARecognizable
