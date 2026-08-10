import Lax52.MSOSemantics

namespace Lax52Proofs.MSOSemantics

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.Structure
open Lax52.MSOSyntax
open Lax52.MSOSemantics

universe u v w

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

@[simp] theorem realize_falsum {n m : Nat} {v : Fin n → M} {V : Fin m → Set M} :
    Realize (Lax52.MSOSyntax.Formula.falsum : Lax52.MSOSyntax.Formula L n m) v V ↔
      False := Iff.rfl

@[simp] theorem realize_equal {n m : Nat} {t₁ t₂ : L.Term (Fin n)}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.equal t₁ t₂) v V ↔ t₁.realize v = t₂.realize v := Iff.rfl

@[simp] theorem realize_rel {n m k : Nat} {r : L.Relations k}
    {ts : Fin k → L.Term (Fin n)} {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.rel r ts) v V ↔ RelMap r (fun i => (ts i).realize v) := Iff.rfl

@[simp] theorem realize_mem {n m : Nat} {t : L.Term (Fin n)} {X : Fin m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.mem t X) v V ↔ t.realize v ∈ V X := Iff.rfl

@[simp] theorem realize_or {n m : Nat} {phi psi : Lax52.MSOSyntax.Formula L n m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.or phi psi) v V ↔ Realize phi v V ∨ Realize psi v V := Iff.rfl

@[simp] theorem realize_neg {n m : Nat} {phi : Lax52.MSOSyntax.Formula L n m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.neg phi) v V ↔ ¬Realize phi v V := Iff.rfl

@[simp] theorem realize_exFO {n m : Nat} {phi : Lax52.MSOSyntax.Formula L (n + 1) m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.exFO phi) v V ↔ ∃ x : M, Realize phi (consVal x v) V := Iff.rfl

@[simp] theorem realize_exSO {n m : Nat} {phi : Lax52.MSOSyntax.Formula L n (m + 1)}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (.exSO phi) v V ↔ ∃ X : Set M, Realize phi v (consVal X V) := Iff.rfl

@[simp] theorem realize_and {n m : Nat} {phi psi : Lax52.MSOSyntax.Formula L n m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (Lax52.MSOSyntax.Formula.and phi psi) v V ↔
      Realize phi v V ∧ Realize psi v V := by
  simp [Lax52.MSOSyntax.Formula.and, Realize]

@[simp] theorem realize_verum {n m : Nat} {v : Fin n → M} {V : Fin m → Set M} :
    Realize (Lax52.MSOSyntax.Formula.verum : Lax52.MSOSyntax.Formula L n m) v V ↔ True := by
  simp [Lax52.MSOSyntax.Formula.verum, Realize]

@[simp] theorem realize_imp {n m : Nat} {phi psi : Lax52.MSOSyntax.Formula L n m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (Lax52.MSOSyntax.Formula.imp phi psi) v V ↔
      (Realize phi v V → Realize psi v V) := by
  simp only [Lax52.MSOSyntax.Formula.imp, Realize]
  tauto

@[simp] theorem realize_allFO {n m : Nat} {phi : Lax52.MSOSyntax.Formula L (n + 1) m}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (Lax52.MSOSyntax.Formula.allFO phi) v V ↔
      ∀ x : M, Realize phi (consVal x v) V := by
  simp [Lax52.MSOSyntax.Formula.allFO, Realize]

@[simp] theorem realize_allSO {n m : Nat} {phi : Lax52.MSOSyntax.Formula L n (m + 1)}
    {v : Fin n → M} {V : Fin m → Set M} :
    Realize (Lax52.MSOSyntax.Formula.allSO phi) v V ↔
      ∀ X : Set M, Realize phi v (consVal X V) := by
  simp [Lax52.MSOSyntax.Formula.allSO, Realize]

end Lax52Proofs.MSOSemantics
