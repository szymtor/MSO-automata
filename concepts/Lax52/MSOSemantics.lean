import Lax52.MSOSyntax

/-!
---
title: Semantics of monadic second-order logic
type: definition
---

The satisfaction relation for monadic second-order formulas over an arbitrary
first-order structure.  First-order terms and relation symbols are interpreted
by mathlib's first-order semantics, while a monadic valuation assigns a set of
elements to every monadic variable.
-/

namespace Lax52.MSOSemantics

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.Structure
open Lax52.MSOSyntax

universe u v w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Extend a valuation by putting a newly bound variable at index zero. -/
def consVal {n : Nat} (x : M) (v : Fin n → M) : Fin (n + 1) → M :=
  Fin.cases x v

/-- Satisfaction of an MSO formula under first-order and monadic valuations. -/
def Realize : {n m : Nat} → Formula L n m → (Fin n → M) →
    (Fin m → Set M) → Prop
  | _, _, .falsum, _, _ => False
  | _, _, .equal t₁ t₂, v, _ => t₁.realize v = t₂.realize v
  | _, _, .rel r ts, v, _ => RelMap r (fun i => (ts i).realize v)
  | _, _, .mem t X, v, V => t.realize v ∈ V X
  | _, _, .or phi psi, v, V => Realize phi v V ∨ Realize psi v V
  | _, _, .neg phi, v, V => ¬Realize phi v V
  | _, _, .exFO phi, v, V => ∃ x : M, Realize phi (consVal x v) V
  | _, _, .exSO phi, v, V => ∃ X : Set M, Realize phi v (consVal X V)

end Lax52.MSOSemantics
