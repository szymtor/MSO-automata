import Lax146103Proofs.MSOToNFA
import Lax146103Proofs.NFAToMSO

namespace Lax146103Proofs

open FirstOrder
open Lax146103
open Lax146103.MSOSyntax
open Lax146103.MSOSemantics
open Lax146103.WordStructure
open Lax146103.NFARecognizable
open Lax146103.NFAToMSO
open Lax146103.MSOToNFA

universe u

/--
---
conclusion: Lax146103.MSOAutomataEquivalence.nfaRecognizable_iff_msoDefinable
---
-/
theorem nfaRecognizable_iff_msoDefinable_proof {Sigma : Type u} [Fintype Sigma]
    (L : _root_.Language Sigma) :
    NFARecognizable L ↔
      ∃ phi : MSOSyntax.Sentence (wordLanguage Sigma), L = sentenceLanguage phi := by
  constructor
  · rintro ⟨Q, instQ, M, hM⟩
    letI : Fintype Q := instQ
    obtain ⟨phi, hphi⟩ := nfa_definable_by_mso_proof M
    exact ⟨phi, hM.symm.trans hphi⟩
  · rintro ⟨phi, rfl⟩
    exact mso_definable_is_nfaRecognizable_proof phi

end Lax146103Proofs
