import Lax146103.MSOSemantics
import Mathlib.Computability.NFA

/-!
---
title: Words as finite relational structures
type: definition
---

A word over an alphabet `Sigma` is viewed as a structure whose elements are its
positions, ordered by their natural order, with one unary predicate for each
letter.  The predicate belonging to `a` holds exactly at positions carrying
the letter `a`.  These properties uniquely determine the structure; no
particular construction of it is part of the concept.
-/

namespace Lax146103.WordStructure

open FirstOrder
open FirstOrder.Language
open Lax146103.MSOSyntax
open Lax146103.MSOSemantics

universe u

/-- Relation symbols of the language of words over `Sigma`. -/
inductive WordRelation (Sigma : Type u) : Nat → Type u
  | letter (a : Sigma) : WordRelation Sigma 1
  | le : WordRelation Sigma 2

/-- The first-order language with order and one unary predicate per letter. -/
def wordLanguage (Sigma : Type u) : FirstOrder.Language.{0, u} where
  Functions := fun _ => Empty
  Relations := WordRelation Sigma

/-- A structure has the relational content of `w` when its unary letter
relations record exactly the letters of `w` and its order relation is the
natural order on positions. -/
def IsWordStructure {Sigma : Type u} (w : List Sigma)
    (S : (wordLanguage Sigma).Structure (Fin w.length)) : Prop :=
  (∀ (a : Sigma) (xs : Fin 1 → Fin w.length),
      @FirstOrder.Language.Structure.RelMap
        (wordLanguage Sigma) (Fin w.length) S 1 (WordRelation.letter a) xs ↔
        w.get (xs 0) = a) ∧
  (∀ xs : Fin 2 → Fin w.length,
      @FirstOrder.Language.Structure.RelMap
        (wordLanguage Sigma) (Fin w.length) S 2 WordRelation.le xs ↔
        xs 0 ≤ xs 1)

/-- The relational content of a word determines a unique first-order
structure on its positions. -/
axiom existsUnique_wordStructure {Sigma : Type u} (w : List Sigma) :
  ∃! S : (wordLanguage Sigma).Structure (Fin w.length), IsWordStructure w S

/-- Satisfaction of a closed MSO sentence by a word, expressed using any
structure with the uniquely determined relational content of that word. -/
def WordModels {Sigma : Type u} (w : List Sigma)
    (phi : MSOSyntax.Sentence (wordLanguage Sigma)) : Prop :=
  ∀ S : (wordLanguage Sigma).Structure (Fin w.length), IsWordStructure w S →
    @MSOSemantics.Realize (wordLanguage Sigma) (Fin w.length) S 0 0 phi
      (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)

/-- The language of words satisfying an MSO sentence. -/
def sentenceLanguage {Sigma : Type u} (phi : MSOSyntax.Sentence (wordLanguage Sigma)) :
    _root_.Language Sigma :=
  {w | WordModels w phi}

end Lax146103.WordStructure
