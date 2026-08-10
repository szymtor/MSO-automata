import Lax52.MSOFormulaRegularity
import Lax52.NFARecognizable

/-!
---
title: MSO-definable word languages are NFA-recognizable
type: theorem
---

Every monadic second-order sentence over finite words on a finite alphabet is
recognized by a nondeterministic finite automaton.
-/

namespace Lax52.MSOToNFA

open Lax52.MSOSyntax
open Lax52.WordStructure
open Lax52.NFARecognizable

universe u

axiom mso_definable_is_nfaRecognizable {Sigma : Type u} [Fintype Sigma]
    (phi : MSOSyntax.Sentence (wordLanguage Sigma)) :
  NFARecognizable (sentenceLanguage phi)

end Lax52.MSOToNFA
