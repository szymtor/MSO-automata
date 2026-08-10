import Lax52.ValidMarkedWordsRegular

/-!
---
title: Regularity of MSO formula languages
type: theorem
---

Over a finite alphabet, the valid marked encodings satisfying any monadic
second-order formula form a regular language.
-/

namespace Lax52.MSOFormulaRegularity

open Lax52.MSOSyntax
open Lax52.MarkedWords
open Lax52.WordStructure

universe u

axiom formulaLanguage_isRegular {Sigma : Type u} [Fintype Sigma] {n m : Nat}
    (phi : MSOSyntax.Formula (wordLanguage Sigma) n m) :
  (formulaLanguage phi).IsRegular

end Lax52.MSOFormulaRegularity
