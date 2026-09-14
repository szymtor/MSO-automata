import Lax146103Proofs.Regular
import Lax146103Proofs.MarkedWords

namespace Lax146103Proofs

open Lax146103
open Lax146103.MSOSyntax
open Lax146103.MSOSemantics
open Lax146103.WordStructure
open Lax146103.NFARecognizable
open Lax146103.NFAToMSO
open Lax146103.MSOToNFA

universe u

/-- A predicate holds at exactly one position of a list. -/
def ExactlyOnce {Alpha : Type u} (p : Alpha → Prop) : List Alpha → Prop
  | [] => False
  | a :: w =>
      (p a ∧ ∀ b ∈ w, ¬p b) ∨ (¬p a ∧ ExactlyOnce p w)

/-- A predicate holds nowhere in a list. -/
def Nowhere {Alpha : Type u} (p : Alpha → Prop) (w : List Alpha) : Prop :=
  ∀ a ∈ w, ¬p a

theorem nowhere_cons {Alpha : Type u} {p : Alpha → Prop} {a : Alpha} {w : List Alpha} :
    Nowhere p (a :: w) ↔ ¬p a ∧ Nowhere p w := by
  simp [Nowhere]

theorem exactlyOnce_iff_unique_fin {Alpha : Type u} (p : Alpha → Prop) (w : List Alpha) :
    ExactlyOnce p w ↔
      ∃ i : Fin w.length, ∀ j : Fin w.length, p (w.get j) ↔ j = i := by
  induction w with
  | nil => simp [ExactlyOnce]
  | cons a w ih =>
      constructor
      · intro h
        rcases h with h | h
        · refine ⟨0, ?_⟩
          intro j
          refine Fin.cases ?_ (fun k => ?_) j
          · simp [h.1]
          · simp only [List.get_eq_getElem, List.getElem_cons_succ]
            constructor
            · intro hp
              exact False.elim (h.2 (w.get k) (List.get_mem w k) hp)
            · intro hk
              exact False.elim (Fin.succ_ne_zero k hk)
        · obtain ⟨i, hi⟩ := ih.mp h.2
          refine ⟨i.succ, ?_⟩
          intro j
          refine Fin.cases ?_ (fun k => ?_) j
          · constructor
            · exact fun hp => False.elim (h.1 hp)
            · exact fun hz => False.elim (Fin.succ_ne_zero i hz.symm)
          · simpa using hi k
      · rintro ⟨i, hi⟩
        obtain rfl | ⟨k, rfl⟩ := i.eq_zero_or_eq_succ
        · left
          constructor
          · simpa using (hi 0).mpr rfl
          · intro b hb hpb
            obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hb
            have hs : (Fin.succ k : Fin (w.length + 1)) = 0 :=
              (hi k.succ).mp (by simpa using hpb)
            exact Fin.succ_ne_zero k hs
        · right
          constructor
          · intro hpa
            have hz : (0 : Fin (w.length + 1)) = k.succ :=
              (hi 0).mp (by simpa using hpa)
            exact Fin.succ_ne_zero k hz.symm
          · apply ih.mpr
            refine ⟨k, ?_⟩
            intro j
            simpa using hi j.succ

/-- The three possible occurrence counts relevant to exact-once recognition. -/
inductive OccurrenceCount
  | zero
  | one
  | many
  deriving DecidableEq, Fintype

namespace OccurrenceCount

/-- Add one occurrence, saturating at `many`. -/
def add (s : OccurrenceCount) (present : Bool) : OccurrenceCount :=
  if present then
    match s with
    | zero => one
    | one | many => many
  else s

end OccurrenceCount

/-- A DFA recognizing that `p` holds at exactly one input position. -/
def exactlyOnceDFA {Alpha : Type u} (p : Alpha → Bool) : DFA Alpha OccurrenceCount where
  step s a := s.add (p a)
  start := .zero
  accept := {.one}

theorem exactlyOnceDFA_evalFrom {Alpha : Type u} (p : Alpha → Bool)
    (w : List Alpha) (s : OccurrenceCount) :
    (exactlyOnceDFA p).evalFrom s w = .one ↔
      match s with
      | .zero => ExactlyOnce (fun a => p a = true) w
      | .one => Nowhere (fun a => p a = true) w
      | .many => False := by
  induction w generalizing s with
  | nil => cases s <;> simp [ExactlyOnce, Nowhere]
  | cons a w ih =>
      rw [DFA.evalFrom_cons]
      change (exactlyOnceDFA p).evalFrom (s.add (p a)) w = .one ↔ _
      cases s <;> cases h : p a <;>
        simp [OccurrenceCount.add, h, ih, ExactlyOnce, Nowhere]

theorem exactlyOnceDFA_eval {Alpha : Type u} (p : Alpha → Bool) (w : List Alpha) :
    (exactlyOnceDFA p).eval w = .one ↔
      ExactlyOnce (fun a => p a = true) w := by
  exact exactlyOnceDFA_evalFrom p w .zero

/-- The Boolean first-order marker at a decorated letter. -/
noncomputable def foMarker {Sigma : Type u} {n m : Nat} (x : Fin n) :
    MarkedLetter Sigma n m → Bool := by
  classical
  exact fun a => decide (Sum.inl x ∈ a.2)

@[simp] theorem foMarker_eq_true {Sigma : Type u} {n m : Nat} (x : Fin n)
    (a : MarkedLetter Sigma n m) :
    foMarker x a = true ↔ Sum.inl x ∈ a.2 := by
  classical
  simp [foMarker]

/-- The product counter DFA for validity of all first-order markers. -/
noncomputable def validMarkedDFA (Sigma : Type u) (n m : Nat) :
    DFA (MarkedLetter Sigma n m) (Fin n → OccurrenceCount) := by
  classical
  exact
    { step := fun s a x => s x |>.add (foMarker x a)
      start := fun _ => .zero
      accept := {s | ∀ x, s x = .one} }

theorem validMarkedDFA_evalFrom_apply (Sigma : Type u) (n m : Nat)
    (w : List (MarkedLetter Sigma n m)) (s : Fin n → OccurrenceCount) (x : Fin n) :
    (validMarkedDFA Sigma n m).evalFrom s w x =
      (exactlyOnceDFA (foMarker x)).evalFrom (s x) w := by
  classical
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
      rw [DFA.evalFrom_cons, DFA.evalFrom_cons, ih]
      rfl

theorem validMarkedDFA_eval_apply (Sigma : Type u) (n m : Nat)
    (w : List (MarkedLetter Sigma n m)) (x : Fin n) :
    (validMarkedDFA Sigma n m).eval w x =
      (exactlyOnceDFA (foMarker x)).eval w := by
  exact validMarkedDFA_evalFrom_apply Sigma n m w _ x

theorem validMarkedDFA_accepts_iff (Sigma : Type u) (n m : Nat)
    (w : List (MarkedLetter Sigma n m)) :
    w ∈ (validMarkedDFA Sigma n m).accepts ↔
      ∀ x : Fin n, ExactlyOnce (fun a => Sum.inl x ∈ a.2) w := by
  classical
  rw [DFA.mem_accepts]
  change (∀ x, (validMarkedDFA Sigma n m).eval w x = .one) ↔ _
  constructor
  · intro h x
    have hx := h x
    rw [validMarkedDFA_eval_apply, exactlyOnceDFA_eval] at hx
    simpa using hx
  · intro h x
    rw [validMarkedDFA_eval_apply, exactlyOnceDFA_eval]
    simpa using h x

theorem validMarked_iff_exactlyOnce {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) :
    ValidMarked w ↔
      ∀ x : Fin n, ExactlyOnce (fun a => Sum.inl x ∈ a.2) w := by
  classical
  constructor
  · rintro ⟨v, V, hv, hV⟩ x
    apply (exactlyOnce_iff_unique_fin _ _).mpr
    exact ⟨v x, fun j => (hv j x).trans eq_comm⟩
  · intro h
    have hx : ∀ x : Fin n, ∃ i : Fin w.length,
        ∀ j : Fin w.length, Sum.inl x ∈ (w.get j).2 ↔ j = i :=
      fun x => (exactlyOnce_iff_unique_fin _ _).mp (h x)
    let v : Fin n → Fin w.length := fun x => Classical.choose (hx x)
    let V : Fin m → Set (Fin w.length) :=
      fun X => {i | Sum.inr X ∈ (w.get i).2}
    refine ⟨v, V, ?_, ?_⟩
    · intro i x
      exact (Classical.choose_spec (hx x) i).trans eq_comm
    · intro i X
      rfl

theorem validMarkedLanguage_isRegular_proof {Sigma : Type u} [Fintype Sigma] (n m : Nat) :
    (validMarkedLanguage Sigma n m).IsRegular := by
  refine ⟨Fin n → OccurrenceCount, inferInstance, validMarkedDFA Sigma n m, ?_⟩
  ext w
  change (w ∈ (validMarkedDFA Sigma n m).accepts) ↔ ValidMarked w
  rw [validMarkedDFA_accepts_iff, validMarked_iff_exactlyOnce]

end Lax146103Proofs
