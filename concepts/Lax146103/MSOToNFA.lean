import Lax146103.NFARecognizable
import Lax146103.WordStructure

/-!
---
title: MSO-definable word languages are NFA-recognizable
type: theorem
---

Every monadic second-order sentence over finite words on a finite alphabet is
recognized by a nondeterministic finite automaton.
-/

namespace Lax146103.MSOToNFA

open Lax146103.MSOSyntax
open Lax146103.WordStructure
open Lax146103.NFARecognizable

universe u

axiom mso_definable_is_nfaRecognizable {Sigma : Type u} [Fintype Sigma]
    (phi : MSOSyntax.Sentence (wordLanguage Sigma)) :
  NFARecognizable (sentenceLanguage phi)

end Lax146103.MSOToNFA
