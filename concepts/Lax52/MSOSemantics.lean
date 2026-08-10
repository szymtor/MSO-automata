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

@[simp] theorem realize_falsum {n m : Nat} {v : Fin n → M} {V : Fin m → Set M} :
    Realize (Formula.falsum : Formula L n m) v V ↔ False := Iff.rfl

@[simp] theorem realize_equal {n m : Nat} {t₁ t₂ : L.Term (Fin n)}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.equal t₁ t₂) v V ↔ t₁.realize v = t₂.realize v := Iff.rfl

@[simp] theorem realize_rel {n m k : Nat} {r : L.Relations k}
    {ts : Fin k → L.Term (Fin n)} {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.rel r ts) v V ↔ RelMap r (fun i => (ts i).realize v) := Iff.rfl

@[simp] theorem realize_mem {n m : Nat} {t : L.Term (Fin n)} {X : Fin m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.mem t X) v V ↔ t.realize v ∈ V X := Iff.rfl

@[simp] theorem realize_or {n m : Nat} {phi psi : Formula L n m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.or phi psi) v V ↔ Realize phi v V ∨ Realize psi v V := Iff.rfl

@[simp] theorem realize_neg {n m : Nat} {phi : Formula L n m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.neg phi) v V ↔ ¬Realize phi v V := Iff.rfl

@[simp] theorem realize_exFO {n m : Nat} {phi : Formula L (n + 1) m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.exFO phi) v V ↔ ∃ x : M, Realize phi (consVal x v) V := Iff.rfl

@[simp] theorem realize_exSO {n m : Nat} {phi : Formula L n (m + 1)}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.exSO phi) v V ↔ ∃ X : Set M, Realize phi v (consVal X V) := Iff.rfl

@[simp] theorem realize_and {n m : Nat} {phi psi : Formula L n m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (MSOSyntax.Formula.and phi psi) v V ↔
      Realize phi v V ∧ Realize psi v V := by
  simp [MSOSyntax.Formula.and, Realize]

@[simp] theorem realize_verum {n m : Nat} {v : Fin n → M} {V : Fin m → Set M} :
    Realize (MSOSyntax.Formula.verum : Formula L n m) v V ↔ True := by
  simp [MSOSyntax.Formula.verum, Realize]

@[simp] theorem realize_imp {n m : Nat} {phi psi : Formula L n m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (MSOSyntax.Formula.imp phi psi) v V ↔
      (Realize phi v V → Realize psi v V) := by
  simp only [MSOSyntax.Formula.imp, Realize]
  tauto

@[simp] theorem realize_allFO {n m : Nat} {phi : Formula L (n + 1) m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (MSOSyntax.Formula.allFO phi) v V ↔
      ∀ x : M, Realize phi (consVal x v) V := by
  simp [MSOSyntax.Formula.allFO, Realize]

@[simp] theorem realize_allSO {n m : Nat} {phi : Formula L n (m + 1)}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (MSOSyntax.Formula.allSO phi) v V ↔
      ∀ X : Set M, Realize phi v (consVal X V) := by
  simp [MSOSyntax.Formula.allSO, Realize]

end Lax52.MSOSemantics
