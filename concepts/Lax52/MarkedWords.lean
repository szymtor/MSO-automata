import Lax52.WordStructure

/-!
---
title: Marked words representing valuations
type: definition
---

A word together with valuations of finitely many first-order and monadic
second-order variables is represented over the alphabet
`Sigma × 2^(Fin n ⊕ Fin m)`.  A first-order marker occurs at exactly its one
assigned position, while a monadic marker occurs at all positions belonging to
its assigned set.  The language of an open formula consists only of valid
representations whose represented valuation satisfies the formula.
-/

namespace Lax52.MarkedWords

open FirstOrder
open FirstOrder.Language
open Lax52.MSOSyntax
open Lax52.MSOSemantics
open Lax52.WordStructure

universe u

/-- A letter decorated by the first-order and monadic variables true at its
position. -/
abbrev MarkedLetter (Sigma : Type u) (n m : Nat) :=
  Sigma × Set (Fin n ⊕ Fin m)

/-- The word structure underlying a marked word, obtained by forgetting all
variable markers. -/
@[reducible] def markedWordStructure {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) :
    (wordLanguage Sigma).Structure (Fin w.length) where
  funMap := fun f => nomatch f
  RelMap := fun r xs => by
    cases r with
    | letter a => exact (w.get (xs 0)).1 = a
    | le => exact xs 0 ≤ xs 1

/-- A marked word exactly represents the supplied valuations. -/
def Represents {Sigma : Type u} {n m : Nat} (w : List (MarkedLetter Sigma n m))
    (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)) : Prop :=
  (∀ (i : Fin w.length) (x : Fin n),
      Sum.inl x ∈ (w.get i).2 ↔ v x = i) ∧
  (∀ (i : Fin w.length) (X : Fin m),
      Sum.inr X ∈ (w.get i).2 ↔ i ∈ V X)

/-- A marked word is valid if it represents some pair of valuations. -/
def ValidMarked {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) : Prop :=
  ∃ (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)), Represents w v V

/-- Satisfaction of an open formula by a represented marked word and its
valuations. -/
def MarkedRealize {Sigma : Type u} {n m : Nat} (w : List (MarkedLetter Sigma n m))
    (phi : MSOSyntax.Formula (wordLanguage Sigma) n m)
    (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)) : Prop := by
  letI := markedWordStructure w
  exact MSOSemantics.Realize phi v V

/-- The valid marked encodings whose represented valuations satisfy `phi`. -/
def formulaLanguage {Sigma : Type u} {n m : Nat}
    (phi : MSOSyntax.Formula (wordLanguage Sigma) n m) :
    _root_.Language (MarkedLetter Sigma n m) :=
  {w | ∃ (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)),
    Represents w v V ∧ MarkedRealize w phi v V}

/-- The language of valid marked encodings. -/
def validMarkedLanguage (Sigma : Type u) (n m : Nat) :
    _root_.Language (MarkedLetter Sigma n m) :=
  {w | ValidMarked w}

end Lax52.MarkedWords
