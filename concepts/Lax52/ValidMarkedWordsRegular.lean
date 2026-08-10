import Lax52.MarkedWords

/-!
---
title: Regularity of valid marked words
type: theorem
---

For a finite alphabet and finitely many variables, the marked words that encode
genuine valuations form a regular language.  In particular, every first-order
variable marker must occur exactly once.
-/

namespace Lax52.ValidMarkedWordsRegular

open Lax52.MarkedWords

universe u

axiom validMarkedLanguage_isRegular {Sigma : Type u} [Fintype Sigma] (n m : Nat) :
  (validMarkedLanguage Sigma n m).IsRegular

end Lax52.ValidMarkedWordsRegular
