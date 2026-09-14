import Mathlib.Computability.NFA

/-!
---
title: Recognition by a finite nondeterministic automaton
type: definition
---

A language is NFA-recognizable when it is accepted by a mathlib
nondeterministic automaton whose state type is finite.
-/

namespace Lax146103.NFARecognizable

universe u

/-- Recognition by an NFA with a finite state type. -/
def NFARecognizable {Sigma : Type u} (L : _root_.Language Sigma) : Prop :=
  ∃ Q : Type, ∃ _ : Fintype Q, ∃ M : NFA Sigma Q, M.accepts = L

end Lax146103.NFARecognizable
