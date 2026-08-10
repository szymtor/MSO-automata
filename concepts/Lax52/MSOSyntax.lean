import Mathlib.ModelTheory.Semantics

/-!
---
title: Monadic second-order syntax
type: definition
---

Monadic second-order formulas over an arbitrary first-order language.  A formula
in context `(n, m)` has `n` first-order variables and `m` monadic second-order
variables.  First-order terms are the terms of the underlying first-order
language.  Disjunction and negation are primitive; conjunction and the other
usual connectives are derived operations.
-/

namespace Lax52.MSOSyntax

open FirstOrder

universe u v

/-- Monadic second-order formulas over `L`, intrinsically scoped by the numbers
of available first-order and monadic variables. -/
inductive Formula (L : Language.{u, v}) : Nat → Nat → Type (max u v)
  | falsum {n m : Nat} : Formula L n m
  | equal {n m : Nat} : L.Term (Fin n) → L.Term (Fin n) → Formula L n m
  | rel {n m k : Nat} : L.Relations k → (Fin k → L.Term (Fin n)) → Formula L n m
  | mem {n m : Nat} : L.Term (Fin n) → Fin m → Formula L n m
  | or {n m : Nat} : Formula L n m → Formula L n m → Formula L n m
  | neg {n m : Nat} : Formula L n m → Formula L n m
  | exFO {n m : Nat} : Formula L (n + 1) m → Formula L n m
  | exSO {n m : Nat} : Formula L n (m + 1) → Formula L n m

/-- An MSO sentence has no free variables of either sort. -/
abbrev Sentence (L : Language.{u, v}) := Formula L 0 0

namespace Formula

variable {L : Language.{u, v}} {n m : Nat}

/-- Derived conjunction. -/
def and (phi psi : Formula L n m) : Formula L n m :=
  .neg (.or (.neg phi) (.neg psi))

/-- Derived truth. -/
def verum : Formula L n m := .neg .falsum

/-- Derived implication. -/
def imp (phi psi : Formula L n m) : Formula L n m :=
  .or (.neg phi) psi

/-- Derived biconditional. -/
def iff (phi psi : Formula L n m) : Formula L n m :=
  and (imp phi psi) (imp psi phi)

/-- Derived universal first-order quantification. -/
def allFO (phi : Formula L (n + 1) m) : Formula L n m :=
  .neg (.exFO (.neg phi))

/-- Derived universal monadic second-order quantification. -/
def allSO (phi : Formula L n (m + 1)) : Formula L n m :=
  .neg (.exSO (.neg phi))

end Formula

end Lax52.MSOSyntax
