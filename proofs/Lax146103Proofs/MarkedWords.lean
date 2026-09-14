import Lax146103.WordStructure

namespace Lax146103Proofs

open FirstOrder
open FirstOrder.Language
open Lax146103.MSOSyntax
open Lax146103.MSOSemantics
open Lax146103.WordStructure

universe u

/-- A letter decorated by the first-order and monadic variables true at its
position. -/
abbrev MarkedLetter (Sigma : Type u) (n m : Nat) :=
  Sigma × Set (Fin n ⊕ Fin m)

/-- A structure has the relational content of a marked word when it interprets
only the underlying alphabet letters and the natural order, ignoring all
variable markers. -/
def IsMarkedWordStructure {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m))
    (S : (wordLanguage Sigma).Structure (Fin w.length)) : Prop :=
  (∀ (a : Sigma) (xs : Fin 1 → Fin w.length),
      @FirstOrder.Language.Structure.RelMap
        (wordLanguage Sigma) (Fin w.length) S 1 (WordRelation.letter a) xs ↔
        (w.get (xs 0)).1 = a) ∧
  (∀ xs : Fin 2 → Fin w.length,
      @FirstOrder.Language.Structure.RelMap
        (wordLanguage Sigma) (Fin w.length) S 2 WordRelation.le xs ↔
        xs 0 ≤ xs 1)

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
    (phi : Formula (wordLanguage Sigma) n m)
    (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)) : Prop :=
  ∀ S : (wordLanguage Sigma).Structure (Fin w.length), IsMarkedWordStructure w S →
    @Realize (wordLanguage Sigma) (Fin w.length) S n m phi v V

/-- The valid marked encodings whose represented valuations satisfy `phi`. -/
def formulaLanguage {Sigma : Type u} {n m : Nat}
    (phi : Formula (wordLanguage Sigma) n m) :
    _root_.Language (MarkedLetter Sigma n m) :=
  {w | ∃ (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)),
    Represents w v V ∧ MarkedRealize w phi v V}

/-- The language of valid marked encodings. -/
def validMarkedLanguage (Sigma : Type u) (n m : Nat) :
    _root_.Language (MarkedLetter Sigma n m) :=
  {w | ValidMarked w}

end Lax146103Proofs
