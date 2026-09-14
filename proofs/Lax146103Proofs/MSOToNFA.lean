import Lax146103Proofs.MSOFormulaRegularity

namespace Lax146103Proofs

open FirstOrder
open FirstOrder.Language
open Lax146103
open Lax146103.MSOSyntax
open Lax146103.MSOSemantics
open Lax146103.WordStructure
open Lax146103.NFARecognizable
open Lax146103.NFAToMSO
open Lax146103.MSOToNFA

universe u

/-- A plain alphabet letter with the (necessarily empty) zero-variable marker
set. -/
def noMarkerLetter {Sigma : Type u} (a : Sigma) : MarkedLetter Sigma 0 0 :=
  (a, ∅)

/-- A word and its zero-variable marked copy carry isomorphic word
structures. -/
noncomputable def noMarkerEquiv {Sigma : Type u} (w : List Sigma) :
    @FirstOrder.Language.Equiv (wordLanguage Sigma)
      (Fin w.length) (Fin (w.map noMarkerLetter).length)
      (wordStructure w) (markedWordStructure (w.map noMarkerLetter)) := by
  letI : (wordLanguage Sigma).Structure (Fin w.length) := wordStructure w
  letI : (wordLanguage Sigma).Structure (Fin (w.map noMarkerLetter).length) :=
    markedWordStructure (w.map noMarkerLetter)
  let hlen : w.length = (w.map noMarkerLetter).length := by simp
  let e : Fin w.length ≃ Fin (w.map noMarkerLetter).length := finCongr hlen
  have he (i : Fin w.length) : (e i).val = i.val := by simp [e]
  refine ⟨e, ?_, ?_⟩
  · intro k f xs
    exact nomatch f
  · intro k r xs
    cases r with
    | letter a =>
        change ((w.map noMarkerLetter).get (e (xs 0))).1 = a ↔ w.get (xs 0) = a
        simp [e, noMarkerLetter]
    | le =>
        change e (xs 0) ≤ e (xs 1) ↔ xs 0 ≤ xs 1
        simp only [Fin.le_iff_val_le_val, he]

theorem represents_noMarker {Sigma : Type u} (w : List Sigma) :
    Represents (w.map noMarkerLetter)
      (fun x : Fin 0 => Fin.elim0 x)
      (fun X : Fin 0 => Fin.elim0 X) := by
  constructor
  · intro i x
    exact Fin.elim0 x
  · intro i X
    exact Fin.elim0 X

theorem sentenceLanguage_eq_comap_formulaLanguage {Sigma : Type u}
    (phi : MSOSyntax.Sentence (wordLanguage Sigma)) :
    sentenceLanguage phi =
      ({w | w.map noMarkerLetter ∈ formulaLanguage phi} : _root_.Language Sigma) := by
  classical
  ext w
  constructor
  · intro hw
    letI : (wordLanguage Sigma).Structure (Fin w.length) := wordStructure w
    letI : (wordLanguage Sigma).Structure (Fin (w.map noMarkerLetter).length) :=
      markedWordStructure (w.map noMarkerLetter)
    let e : Fin w.length ≃[wordLanguage Sigma] Fin (w.map noMarkerLetter).length :=
      noMarkerEquiv w
    let v : Fin 0 → Fin (w.map noMarkerLetter).length := fun x => Fin.elim0 x
    let V : Fin 0 → Set (Fin (w.map noMarkerLetter).length) := fun X => Fin.elim0 X
    refine ⟨v, V, represents_noMarker w, ?_⟩
    rw [markedRealize_iff_realize]
    change MSOSemantics.Realize phi v V
    have hv : e ∘ (fun x : Fin 0 => Fin.elim0 x) = v := Subsingleton.elim _ _
    have hV : (fun X => e '' (fun X : Fin 0 => Fin.elim0 X) X) = V :=
      Subsingleton.elim _ _
    rw [← hv, ← hV]
    exact (MSOSemantics.realize_equiv e phi
      (fun x : Fin 0 => Fin.elim0 x)
      (fun X : Fin 0 => Fin.elim0 X)).mpr ((wordModels_iff_realize w phi).mp hw)
  · rintro ⟨v, V, hrep, hphi⟩
    letI : (wordLanguage Sigma).Structure (Fin w.length) := wordStructure w
    letI : (wordLanguage Sigma).Structure (Fin (w.map noMarkerLetter).length) :=
      markedWordStructure (w.map noMarkerLetter)
    let e : Fin w.length ≃[wordLanguage Sigma] Fin (w.map noMarkerLetter).length :=
      noMarkerEquiv w
    have hv : v = fun x : Fin 0 => Fin.elim0 x := Subsingleton.elim _ _
    have hV : V = fun X : Fin 0 => Fin.elim0 X := Subsingleton.elim _ _
    subst v
    subst V
    rw [markedRealize_iff_realize] at hphi
    change MSOSemantics.Realize phi
      (fun x : Fin 0 => Fin.elim0 x) (fun X : Fin 0 => Fin.elim0 X) at hphi
    have hv : e ∘ (fun x : Fin 0 => Fin.elim0 x) =
        (fun x : Fin 0 => Fin.elim0 x) := Subsingleton.elim _ _
    have hV : (fun X => e '' (fun X : Fin 0 => Fin.elim0 X) X) =
        (fun X : Fin 0 => Fin.elim0 X) := Subsingleton.elim _ _
    apply (wordModels_iff_realize w phi).mpr
    apply (MSOSemantics.realize_equiv e phi
      (fun x : Fin 0 => Fin.elim0 x)
      (fun X : Fin 0 => Fin.elim0 X)).mp
    rw [hv, hV]
    exact hphi

/--
---
conclusion: Lax146103.MSOToNFA.mso_definable_is_nfaRecognizable
---
-/
theorem mso_definable_is_nfaRecognizable_proof {Sigma : Type u} [Fintype Sigma]
    (phi : MSOSyntax.Sentence (wordLanguage Sigma)) :
    NFARecognizable (sentenceLanguage phi) := by
  have hreg := Language.IsRegular.comap
    (formulaLanguage_isRegular_proof phi) (noMarkerLetter : Sigma → MarkedLetter Sigma 0 0)
  rw [← sentenceLanguage_eq_comap_formulaLanguage] at hreg
  exact (nfaRecognizable_iff_isRegular _).mpr hreg

end Lax146103Proofs
