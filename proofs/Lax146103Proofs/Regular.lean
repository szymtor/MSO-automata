import Lax146103

namespace Lax146103Proofs

open Set

universe u v w

namespace NFA

/-- Relabel the input alphabet of an NFA existentially. -/
def mapAlphabet {Alpha : Type u} {Beta : Type v} {Q : Type w}
    (M : NFA Alpha Q) (f : Alpha → Beta) : NFA Beta Q where
  step q b := {q' | ∃ a : Alpha, f a = b ∧ q' ∈ M.step q a}
  start := M.start
  accept := M.accept

theorem mapAlphabet_stepSet {Alpha : Type u} {Beta : Type v} {Q : Type w}
    (M : NFA Alpha Q) (f : Alpha → Beta) (S : Set Q) (b : Beta) :
    (mapAlphabet M f).stepSet S b =
      ⋃ (a : Alpha) (_ : f a = b), M.stepSet S a := by
  ext q
  simp only [NFA.mem_stepSet, mapAlphabet, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs, a, ha, hq⟩
    exact ⟨a, ha, s, hs, hq⟩
  · rintro ⟨a, ha, s, hs, hq⟩
    exact ⟨s, hs, a, ha, hq⟩

theorem mem_evalFrom_mapAlphabet_iff {Alpha : Type u} {Beta : Type v} {Q : Type w}
    (M : NFA Alpha Q) (f : Alpha → Beta) (S : Set Q) (y : List Beta) (q : Q) :
    q ∈ (mapAlphabet M f).evalFrom S y ↔
      ∃ x : List Alpha, x.map f = y ∧ q ∈ M.evalFrom S x := by
  induction y generalizing S with
  | nil =>
      simp
  | cons b y ih =>
      rw [NFA.evalFrom_cons, ih, mapAlphabet_stepSet]
      constructor
      · rintro ⟨x, hx, hq⟩
        rw [M.evalFrom_iUnion₂] at hq
        simp only [Set.mem_iUnion] at hq
        obtain ⟨a, ha, hq⟩ := hq
        exact ⟨a :: x, by simp [ha, hx], hq⟩
      · rintro ⟨x, hx, hq⟩
        cases x with
        | nil => simp at hx
        | cons a x =>
            simp only [List.map_cons, List.cons.injEq] at hx
            refine ⟨x, hx.2, ?_⟩
            rw [M.evalFrom_iUnion₂]
            simp only [Set.mem_iUnion]
            exact ⟨a, hx.1, hq⟩

theorem accepts_mapAlphabet {Alpha : Type u} {Beta : Type v} {Q : Type w}
    (M : NFA Alpha Q) (f : Alpha → Beta) :
    (mapAlphabet M f).accepts = Language.map f M.accepts := by
  ext y
  rw [NFA.mem_accepts]
  change (∃ q ∈ M.accept, q ∈ (mapAlphabet M f).evalFrom M.start y) ↔ _
  simp only [mem_evalFrom_mapAlphabet_iff]
  constructor
  · rintro ⟨q, hqa, x, hxy, hqx⟩
    change y ∈ Set.image (List.map f) M.accepts
    exact ⟨x, ⟨q, hqa, hqx⟩, hxy⟩
  · change y ∈ Set.image (List.map f) M.accepts → _
    rintro ⟨x, ⟨q, hqa, hqx⟩, hxy⟩
    exact ⟨q, hqa, x, hxy, hqx⟩

end NFA

namespace Language.IsRegular

/-- Regular languages are closed under inverse letter maps. -/
theorem comap {Alpha : Type u} {Beta : Type v} {L : Language Beta}
    (h : L.IsRegular) (f : Alpha → Beta) :
    Language.IsRegular ({x | x.map f ∈ L} : Language Alpha) := by
  obtain ⟨Q, _, M, hM⟩ := h
  refine ⟨Q, inferInstance, M.comap f, ?_⟩
  calc
    (M.comap f).accepts = List.map f ⁻¹' M.accepts := M.accepts_comap f
    _ = {x | x.map f ∈ L} := by
      rw [hM]
      ext x
      rfl

/-- Regular languages are closed under direct letter maps. -/
theorem map {Alpha : Type u} {Beta : Type v} {L : Language Alpha}
    (h : L.IsRegular) (f : Alpha → Beta) :
    (Language.map f L).IsRegular := by
  obtain ⟨Q, _, M, hM⟩ := h
  let N := NFA.mapAlphabet M.toNFA f
  refine ⟨Set Q, inferInstance, N.toDFA, ?_⟩
  rw [NFA.toDFA_correct, NFA.accepts_mapAlphabet, DFA.toNFA_correct, hM]

end Language.IsRegular

/-- Recognition by a finite NFA is equivalent to mathlib regularity. -/
theorem nfaRecognizable_iff_isRegular {Alpha : Type u} (L : Language Alpha) :
    Lax146103.NFARecognizable.NFARecognizable L ↔ L.IsRegular := by
  constructor
  · rintro ⟨Q, _, M, hM⟩
    exact ⟨Set Q, inferInstance, M.toDFA, by simpa [hM] using M.toDFA_correct⟩
  · rintro ⟨Q, _, M, hM⟩
    exact ⟨Q, inferInstance, M.toNFA, by simpa [hM] using M.toNFA_correct⟩

end Lax146103Proofs
