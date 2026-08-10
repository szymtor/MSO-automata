import Lax52Proofs.MSOToNFA
import Lax52Proofs.NFAToMSO

namespace Lax52Proofs

open FirstOrder
open Lax52
open Lax52.MSOSyntax
open Lax52.MSOSemantics
open Lax52.WordStructure
open Lax52.NFARecognizable
open Lax52.NFAToMSO
open Lax52.MSOToNFA

universe u

/--
---
conclusion: Lax52.MSOAutomataEquivalence.nfaRecognizable_iff_msoDefinable
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

end Lax52Proofs
