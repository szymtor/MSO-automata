import Lax52

namespace Lax52Proofs

open FirstOrder
open FirstOrder.Language

universe u v w w'

namespace MSOSemantics

variable {L : FirstOrder.Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- MSO satisfaction is invariant under an isomorphism of first-order
structures, with monadic valuations transported by direct image. -/
theorem realize_equiv (e : M ≃[L] N) :
    {n m : Nat} → (phi : Lax52.MSOSyntax.Formula L n m) →
      (v : Fin n → M) → (V : Fin m → Set M) →
      Lax52.MSOSemantics.Realize phi (e ∘ v) (fun X => e '' V X) ↔
        Lax52.MSOSemantics.Realize phi v V
  | _, _, .falsum, _, _ => Iff.rfl
  | _, _, .equal t₁ t₂, v, _ => by
      simp only [Lax52.MSOSemantics.Realize, HomClass.realize_term]
      exact e.injective.eq_iff
  | _, _, .rel r ts, v, _ => by
      simp only [Lax52.MSOSemantics.Realize, HomClass.realize_term]
      exact StrongHomClass.map_rel e r (fun i => (ts i).realize v)
  | _, _, .mem t X, v, V => by
      simp only [Lax52.MSOSemantics.Realize, HomClass.realize_term]
      constructor
      · rintro ⟨x, hx, he⟩
        exact e.injective he ▸ hx
      · intro hx
        exact ⟨t.realize v, hx, rfl⟩
  | _, _, .or phi psi, v, V => by
      simp only [Lax52.MSOSemantics.Realize]
      rw [realize_equiv e phi v V, realize_equiv e psi v V]
  | _, _, .neg phi, v, V => by
      simp only [Lax52.MSOSemantics.Realize]
      rw [realize_equiv e phi v V]
  | _, _, .exFO phi, v, V => by
      simp only [Lax52.MSOSemantics.Realize]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨e.symm y, ?_⟩
        have hv : Lax52.MSOSemantics.consVal y (e ∘ v) =
            e ∘ Lax52.MSOSemantics.consVal (e.symm y) v := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [Lax52.MSOSemantics.consVal]
          · rfl
        rw [hv] at hy
        exact (realize_equiv e phi _ V).mp hy
      · rintro ⟨x, hx⟩
        refine ⟨e x, ?_⟩
        have hv : Lax52.MSOSemantics.consVal (e x) (e ∘ v) =
            e ∘ Lax52.MSOSemantics.consVal x v := by
          funext i
          refine Fin.cases rfl (fun _ => rfl) i
        rw [hv]
        exact (realize_equiv e phi _ V).mpr hx
  | _, _, .exSO phi, v, V => by
      simp only [Lax52.MSOSemantics.Realize]
      constructor
      · rintro ⟨Y, hY⟩
        let X : Set M := e ⁻¹' Y
        refine ⟨X, ?_⟩
        have hsets : Lax52.MSOSemantics.consVal Y (fun Z => e '' V Z) =
            fun Z => e '' Lax52.MSOSemantics.consVal X V Z := by
          funext i
          refine Fin.cases ?_ (fun _ => rfl) i
          ext y
          change y ∈ Y ↔ y ∈ e '' X
          constructor
          · intro hy
            refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
            simpa [X] using hy
          · rintro ⟨x, hx, rfl⟩
            simpa [X] using hx
        rw [hsets] at hY
        exact (realize_equiv e phi v _).mp hY
      · rintro ⟨X, hX⟩
        refine ⟨e '' X, ?_⟩
        have hsets : Lax52.MSOSemantics.consVal (e '' X) (fun Z => e '' V Z) =
            fun Z => e '' Lax52.MSOSemantics.consVal X V Z := by
          funext i
          refine Fin.cases rfl (fun _ => rfl) i
        rw [hsets]
        exact (realize_equiv e phi v _).mpr hX

end MSOSemantics

end Lax52Proofs
