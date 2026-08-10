import Lax52.MSOSemantics
import Mathlib.Computability.NFA

/-!
---
title: Words as finite relational structures
type: definition
---

A word over an alphabet `Sigma` is viewed as a structure whose elements are its
positions, ordered by their natural order, with one unary predicate for each
letter.  The predicate belonging to `a` holds exactly at positions carrying
the letter `a`.
-/

namespace Lax52.WordStructure

open FirstOrder
open FirstOrder.Language
open Lax52.MSOSyntax
open Lax52.MSOSemantics

universe u

/-- Relation symbols of the language of words over `Sigma`. -/
inductive WordRelation (Sigma : Type u) : Nat → Type u
  | letter (a : Sigma) : WordRelation Sigma 1
  | le : WordRelation Sigma 2

/-- The first-order language with order and one unary predicate per letter. -/
def wordLanguage (Sigma : Type u) : FirstOrder.Language.{0, u} where
  Functions := fun _ => Empty
  Relations := WordRelation Sigma

/-- The canonical word structure carried by the positions of `w`. -/
@[reducible] def wordStructure {Sigma : Type u} (w : List Sigma) :
    (wordLanguage Sigma).Structure (Fin w.length) where
  funMap := fun f => nomatch f
  RelMap := fun r xs => by
    cases r with
    | letter a => exact w.get (xs 0) = a
    | le => exact xs 0 ≤ xs 1

/-- Satisfaction of a closed MSO sentence by a word. -/
def WordModels {Sigma : Type u} (w : List Sigma)
    (phi : MSOSyntax.Sentence (wordLanguage Sigma)) : Prop := by
  letI := wordStructure w
  exact MSOSemantics.Realize (M := Fin w.length) phi
    (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)

/-- The language of words satisfying an MSO sentence. -/
def sentenceLanguage {Sigma : Type u} (phi : MSOSyntax.Sentence (wordLanguage Sigma)) :
    _root_.Language Sigma :=
  {w | WordModels w phi}

end Lax52.WordStructure
