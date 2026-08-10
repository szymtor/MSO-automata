import Lax52
import Lax52Proofs.MarkedWords

namespace Lax52Proofs

open FirstOrder
open FirstOrder.Language
open Lax52.MSOSyntax
open Lax52.MSOSemantics
open Lax52.WordStructure

universe u

/-! ## Word structures -/

/-- A concrete witness for the uniquely characterized structure of a word. -/
@[reducible] def wordStructure {Sigma : Type u} (w : List Sigma) :
    (wordLanguage Sigma).Structure (Fin w.length) where
  funMap := fun f => nomatch f
  RelMap := fun r xs => by
    cases r with
    | letter a => exact w.get (xs 0) = a
    | le => exact xs 0 ≤ xs 1

theorem wordStructure_spec {Sigma : Type u} (w : List Sigma) :
    IsWordStructure w (wordStructure w) :=
  ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem wordStructure_unique {Sigma : Type u} (w : List Sigma)
    (S : (wordLanguage Sigma).Structure (Fin w.length))
    (hS : IsWordStructure w S) : S = wordStructure w := by
  apply FirstOrder.Language.Structure.ext
  · funext k f xs
    exact nomatch f
  · funext k r xs
    cases r with
    | letter a => exact propext (hS.1 a xs)
    | le => exact propext (hS.2 xs)

/--
---
conclusion: Lax52.WordStructure.existsUnique_wordStructure
---
-/
theorem existsUnique_wordStructure_proof {Sigma : Type u} (w : List Sigma) :
    ∃! S : (wordLanguage Sigma).Structure (Fin w.length), IsWordStructure w S :=
  ⟨wordStructure w, wordStructure_spec w, wordStructure_unique w⟩

@[simp] theorem wordModels_iff_realize {Sigma : Type u} (w : List Sigma)
    (phi : Lax52.MSOSyntax.Sentence (wordLanguage Sigma)) :
    WordModels w phi ↔
      @Realize (wordLanguage Sigma) (Fin w.length) (wordStructure w) 0 0 phi
        (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i) := by
  constructor
  · intro h
    exact h (wordStructure w) (wordStructure_spec w)
  · intro h S hS
    rw [wordStructure_unique w S hS]
    exact h

/-! ## Marked-word structures -/

/-- A concrete witness for the uniquely characterized structure underlying a
marked word. -/
@[reducible] def markedWordStructure {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) :
    (wordLanguage Sigma).Structure (Fin w.length) where
  funMap := fun f => nomatch f
  RelMap := fun r xs => by
    cases r with
    | letter a => exact (w.get (xs 0)).1 = a
    | le => exact xs 0 ≤ xs 1

theorem markedWordStructure_spec {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) :
    IsMarkedWordStructure w (markedWordStructure w) :=
  ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem markedWordStructure_unique {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m))
    (S : (wordLanguage Sigma).Structure (Fin w.length))
    (hS : IsMarkedWordStructure w S) : S = markedWordStructure w := by
  apply FirstOrder.Language.Structure.ext
  · funext k f xs
    exact nomatch f
  · funext k r xs
    cases r with
    | letter a => exact propext (hS.1 a xs)
    | le => exact propext (hS.2 xs)

theorem existsUnique_markedWordStructure_proof {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) :
    ∃! S : (wordLanguage Sigma).Structure (Fin w.length), IsMarkedWordStructure w S :=
  ⟨markedWordStructure w, markedWordStructure_spec w, markedWordStructure_unique w⟩

@[simp] theorem markedRealize_iff_realize {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m))
    (phi : Formula (wordLanguage Sigma) n m)
    (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)) :
    MarkedRealize w phi v V ↔
      @Realize (wordLanguage Sigma) (Fin w.length) (markedWordStructure w) n m phi v V := by
  constructor
  · intro h
    exact h (markedWordStructure w) (markedWordStructure_spec w)
  · intro h S hS
    rw [markedWordStructure_unique w S hS]
    exact h

@[simp] theorem markedRealize_or {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m))
    (phi psi : Formula (wordLanguage Sigma) n m)
    (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)) :
    MarkedRealize w (.or phi psi) v V ↔
      MarkedRealize w phi v V ∨ MarkedRealize w psi v V := by
  rw [markedRealize_iff_realize, markedRealize_iff_realize,
    markedRealize_iff_realize]
  rfl

@[simp] theorem markedRealize_neg {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m))
    (phi : Formula (wordLanguage Sigma) n m)
    (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)) :
    MarkedRealize w (.neg phi) v V ↔ ¬MarkedRealize w phi v V := by
  rw [markedRealize_iff_realize, markedRealize_iff_realize]
  rfl

end Lax52Proofs
