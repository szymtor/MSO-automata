import Lax146103Proofs.SemanticTransport
import Lax146103Proofs.Structures
import Lax146103Proofs.ValidMarkedWordsRegular

-- Preserve Lean 4.30 elaboration of dependent indices during this port.
set_option backward.isDefEq.respectTransparency false

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

/-! ## Elementary facts about marked valuations -/

theorem represents_unique {Sigma : Type u} {n m : Nat}
    {w : List (MarkedLetter Sigma n m)}
    {v v' : Fin n → Fin w.length} {V V' : Fin m → Set (Fin w.length)}
    (h : Represents w v V) (h' : Represents w v' V') : v = v' ∧ V = V' := by
  rcases h with ⟨hv, hV⟩
  rcases h' with ⟨hv', hV'⟩
  constructor
  · funext x
    have hx := (hv (v x) x).mp ((hv (v x) x).mpr rfl)
    exact (hv' (v x) x).mp ((hv (v x) x).mpr rfl) |>.symm
  · funext X
    ext i
    exact (hV i X).symm.trans (hV' i X)

/-- In the function-free word language every term is a variable. -/
def wordTermVar {Sigma : Type u} {n : Nat} :
    (wordLanguage Sigma).Term (Fin n) → Fin n
  | .var x => x
  | .func f _ => nomatch f

@[simp] theorem wordTerm_eq_var {Sigma : Type u} {n : Nat}
    (t : (wordLanguage Sigma).Term (Fin n)) :
    t = .var (wordTermVar t) := by
  cases t with
  | var x => rfl
  | func f _ => exact nomatch f

@[simp] theorem wordTerm_realize {Sigma : Type u} {n : Nat} {M : Type*}
    [((wordLanguage Sigma).Structure M)]
    (t : (wordLanguage Sigma).Term (Fin n)) (v : Fin n → M) :
    t.realize v = v (wordTermVar t) := by
  rw [wordTerm_eq_var t]
  rfl

/-! ## Small finite automata for the atomic formulas -/

/-- A DFA which remembers whether an input letter satisfying `p` has occurred. -/
def somewhereDFA {Alpha : Type u} (p : Alpha → Bool) : DFA Alpha Bool where
  step seen a := seen || p a
  start := false
  accept := {true}

theorem somewhereDFA_evalFrom {Alpha : Type u} (p : Alpha → Bool)
    (w : List Alpha) (seen : Bool) :
    (somewhereDFA p).evalFrom seen w = (seen || w.any p) := by
  induction w generalizing seen with
  | nil => simp [somewhereDFA]
  | cons a w ih =>
      rw [DFA.evalFrom_cons, ih]
      simp [somewhereDFA, Bool.or_assoc]

theorem somewhereDFA_accepts_iff {Alpha : Type u} (p : Alpha → Bool)
    (w : List Alpha) :
    w ∈ (somewhereDFA p).accepts ↔ ∃ a ∈ w, p a = true := by
  rw [DFA.mem_accepts]
  rw [show (somewhereDFA p).eval w = (false || w.any p) by
    exact somewhereDFA_evalFrom p w false]
  simp [somewhereDFA, List.any_eq_true]

/-- A finite summary for whether an `x`-marked position has occurred and
whether a later (or equal) `y`-marked position has then occurred. -/
def orderDFA {Alpha : Type u} (px py : Alpha → Bool) : DFA Alpha (Bool × Bool) where
  step s a :=
    let seen := s.1 || px a
    (seen, s.2 || (seen && py a))
  start := (false, false)
  accept := {s | s.2 = true}

/-- There are positions satisfying `p` and `q`, in that order (equality is
allowed). -/
def OrderedOccurrence {Alpha : Type u} (p q : Alpha → Prop) (w : List Alpha) : Prop :=
  ∃ i j : Fin w.length, i ≤ j ∧ p (w.get i) ∧ q (w.get j)

theorem orderedOccurrence_cons {Alpha : Type u} (p q : Alpha → Prop)
    (a : Alpha) (w : List Alpha) :
    OrderedOccurrence p q (a :: w) ↔
      (p a ∧ (q a ∨ ∃ b ∈ w, q b)) ∨ OrderedOccurrence p q w := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · left
      refine ⟨by simpa using hi, ?_⟩
      obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
      · exact Or.inl (by simpa using hj)
      · exact Or.inr ⟨w.get j, List.get_mem w j, by simpa using hj⟩
    · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
      · exact False.elim (by simpa using hij)
      · right
        exact ⟨i, j, Fin.succ_le_succ_iff.mp hij, by simpa using hi, by simpa using hj⟩
  · rintro (⟨ha, hq⟩ | h)
    · rcases hq with hqa | ⟨b, hb, hqb⟩
      · exact ⟨0, 0, by simp, by simpa using ha, by simpa using hqa⟩
      · obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hb
        exact ⟨0, j.succ, by simp, by simpa using ha, by simpa using hqb⟩
    · rcases h with ⟨i, j, hij, hi, hj⟩
      exact ⟨i.succ, j.succ, Fin.succ_le_succ_iff.mpr hij,
        by simpa using hi, by simpa using hj⟩

theorem orderDFA_evalFrom_snd {Alpha : Type u} (px py : Alpha → Bool)
    (w : List Alpha) (s : Bool × Bool) :
    ((orderDFA px py).evalFrom s w).2 = true ↔
      s.2 = true ∨
      (s.1 = true ∧ ∃ a ∈ w, py a = true) ∨
      OrderedOccurrence (fun a => px a = true) (fun a => py a = true) w := by
  induction w generalizing s with
  | nil => simp [OrderedOccurrence]
  | cons a w ih =>
      rw [DFA.evalFrom_cons, ih]
      rw [orderedOccurrence_cons]
      simp only [orderDFA, Bool.or_eq_true, Bool.and_eq_true, List.mem_cons,
        exists_eq_or_imp]
      by_cases hs2 : s.2 = true <;> by_cases hs1 : s.1 = true <;>
        by_cases hpx : px a = true <;> by_cases hpy : py a = true <;>
        simp [hs2, hs1, hpx, hpy]

theorem orderDFA_accepts_iff {Alpha : Type u} (px py : Alpha → Bool)
    (w : List Alpha) :
    w ∈ (orderDFA px py).accepts ↔
      OrderedOccurrence (fun a => px a = true) (fun a => py a = true) w := by
  rw [DFA.mem_accepts]
  change ((orderDFA px py).evalFrom (false, false) w).2 = true ↔ _
  rw [orderDFA_evalFrom_snd]
  simp

noncomputable def markerBool {Sigma : Type u} {n m : Nat}
    (z : Fin n ⊕ Fin m) : MarkedLetter Sigma n m → Bool := by
  classical
  exact fun a => decide (z ∈ a.2)

@[simp] theorem markerBool_eq_true {Sigma : Type u} {n m : Nat}
    (z : Fin n ⊕ Fin m) (a : MarkedLetter Sigma n m) :
    markerBool z a = true ↔ z ∈ a.2 := by
  classical
  simp [markerBool]

noncomputable def bothMarkerBool {Sigma : Type u} {n m : Nat}
    (z z' : Fin n ⊕ Fin m) : MarkedLetter Sigma n m → Bool := by
  classical
  exact fun a => decide (z ∈ a.2 ∧ z' ∈ a.2)

@[simp] theorem bothMarkerBool_eq_true {Sigma : Type u} {n m : Nat}
    (z z' : Fin n ⊕ Fin m) (a : MarkedLetter Sigma n m) :
    bothMarkerBool z z' a = true ↔ z ∈ a.2 ∧ z' ∈ a.2 := by
  classical
  simp [bothMarkerBool]

noncomputable def letterMarkerBool {Sigma : Type u} [DecidableEq Sigma]
    {n m : Nat} (a : Sigma) (x : Fin n) : MarkedLetter Sigma n m → Bool := by
  classical
  exact fun b => decide (b.1 = a ∧ Sum.inl x ∈ b.2)

@[simp] theorem letterMarkerBool_eq_true {Sigma : Type u} [DecidableEq Sigma]
    {n m : Nat} (a : Sigma) (x : Fin n) (b : MarkedLetter Sigma n m) :
    letterMarkerBool a x b = true ↔ b.1 = a ∧ Sum.inl x ∈ b.2 := by
  classical
  simp [letterMarkerBool]

theorem somewhere_two_fo_iff {Sigma : Type u} {n m : Nat}
    {w : List (MarkedLetter Sigma n m)} {v : Fin n → Fin w.length}
    {V : Fin m → Set (Fin w.length)} (h : Represents w v V) (x y : Fin n) :
    (∃ a ∈ w, Sum.inl x ∈ a.2 ∧ Sum.inl y ∈ a.2) ↔ v x = v y := by
  rcases h with ⟨hv, _⟩
  constructor
  · rintro ⟨a, ha, hx, hy⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact (hv i x).mp hx |>.trans ((hv i y).mp hy).symm
  · intro hxy
    refine ⟨w.get (v x), List.get_mem w (v x), ?_, ?_⟩
    · exact (hv (v x) x).mpr rfl
    · exact (hv (v x) y).mpr hxy.symm

theorem somewhere_fo_so_iff {Sigma : Type u} {n m : Nat}
    {w : List (MarkedLetter Sigma n m)} {v : Fin n → Fin w.length}
    {V : Fin m → Set (Fin w.length)} (h : Represents w v V) (x : Fin n) (X : Fin m) :
    (∃ a ∈ w, Sum.inl x ∈ a.2 ∧ Sum.inr X ∈ a.2) ↔ v x ∈ V X := by
  rcases h with ⟨hv, hV⟩
  constructor
  · rintro ⟨a, ha, hx, hX⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    rw [(hv i x).mp hx]
    exact (hV i X).mp hX
  · intro hx
    refine ⟨w.get (v x), List.get_mem w (v x),
      (hv (v x) x).mpr rfl, (hV (v x) X).mpr hx⟩

theorem somewhere_letter_iff {Sigma : Type u} {n m : Nat}
    {w : List (MarkedLetter Sigma n m)} {v : Fin n → Fin w.length}
    {V : Fin m → Set (Fin w.length)} (h : Represents w v V) (a : Sigma) (x : Fin n) :
    (∃ b ∈ w, b.1 = a ∧ Sum.inl x ∈ b.2) ↔ (w.get (v x)).1 = a := by
  rcases h with ⟨hv, _⟩
  constructor
  · rintro ⟨b, hb, hba, hx⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hb
    rw [(hv i x).mp hx]
    exact hba
  · intro ha
    exact ⟨w.get (v x), List.get_mem w (v x), ha, (hv (v x) x).mpr rfl⟩

theorem ordered_fo_iff {Sigma : Type u} {n m : Nat}
    {w : List (MarkedLetter Sigma n m)} {v : Fin n → Fin w.length}
    {V : Fin m → Set (Fin w.length)} (h : Represents w v V) (x y : Fin n) :
    OrderedOccurrence (fun a => Sum.inl x ∈ a.2) (fun a => Sum.inl y ∈ a.2) w ↔
      v x ≤ v y := by
  rcases h with ⟨hv, _⟩
  constructor
  · rintro ⟨i, j, hij, hx, hy⟩
    simpa only [(hv i x).mp hx, (hv j y).mp hy] using hij
  · intro hxy
    exact ⟨v x, v y, hxy, (hv (v x) x).mpr rfl, (hv (v y) y).mpr rfl⟩

/-! ## Regularity of the atomic and Boolean cases -/

theorem somewhereDFA_isRegular {Alpha : Type u} (p : Alpha → Bool) :
    (somewhereDFA p).accepts.IsRegular :=
  ⟨Bool, inferInstance, somewhereDFA p, rfl⟩

theorem orderDFA_isRegular {Alpha : Type u} (px py : Alpha → Bool) :
    (orderDFA px py).accepts.IsRegular :=
  ⟨Bool × Bool, inferInstance, orderDFA px py, rfl⟩

theorem emptyLanguage_isRegular {Alpha : Type u} :
    (0 : _root_.Language Alpha).IsRegular := by
  let M : DFA Alpha Unit :=
    { step := fun _ _ => ()
      start := ()
      accept := ∅ }
  exact ⟨Unit, inferInstance, M, by ext w; simp [M, DFA.mem_accepts]⟩

theorem formulaLanguage_falsum {Sigma : Type u} {n m : Nat} :
    formulaLanguage (MSOSyntax.Formula.falsum : MSOSyntax.Formula (wordLanguage Sigma) n m) = 0 := by
  ext w
  change (∃ v V, Represents w v V ∧
    MarkedRealize w (MSOSyntax.Formula.falsum : MSOSyntax.Formula (wordLanguage Sigma) n m) v V) ↔ False
  constructor
  · rintro ⟨v, V, hrep, hfalse⟩
    exact (markedRealize_iff_realize w _ v V).mp hfalse
  · exact False.elim

theorem formulaLanguage_equal {Sigma : Type u} {n m : Nat}
    (t₁ t₂ : (wordLanguage Sigma).Term (Fin n)) :
    formulaLanguage (MSOSyntax.Formula.equal t₁ t₂ : MSOSyntax.Formula (wordLanguage Sigma) n m) =
      validMarkedLanguage Sigma n m ⊓
        (somewhereDFA (bothMarkerBool (Sum.inl (wordTermVar t₁))
          (Sum.inl (wordTermVar t₂)))).accepts := by
  classical
  ext w
  simp only [Language.mem_inf, Set.mem_inter_iff]
  constructor
  · rintro ⟨v, V, hrep, hreal⟩
    refine ⟨⟨v, V, hrep⟩, ?_⟩
    rw [somewhereDFA_accepts_iff]
    simp only [bothMarkerBool_eq_true]
    apply (somewhere_two_fo_iff hrep _ _).mpr
    letI := markedWordStructure w
    rw [markedRealize_iff_realize] at hreal
    change t₁.realize v = t₂.realize v at hreal
    simpa only [wordTerm_realize] using hreal
  · rintro ⟨⟨v, V, hrep⟩, hsome⟩
    refine ⟨v, V, hrep, ?_⟩
    rw [somewhereDFA_accepts_iff] at hsome
    simp only [bothMarkerBool_eq_true] at hsome
    have hxy := (somewhere_two_fo_iff hrep _ _).mp hsome
    letI := markedWordStructure w
    rw [markedRealize_iff_realize]
    change t₁.realize v = t₂.realize v
    simpa only [wordTerm_realize] using hxy

theorem formulaLanguage_mem {Sigma : Type u} {n m : Nat}
    (t : (wordLanguage Sigma).Term (Fin n)) (X : Fin m) :
    formulaLanguage (MSOSyntax.Formula.mem t X : MSOSyntax.Formula (wordLanguage Sigma) n m) =
      validMarkedLanguage Sigma n m ⊓
        (somewhereDFA (bothMarkerBool (Sum.inl (wordTermVar t)) (Sum.inr X))).accepts := by
  classical
  ext w
  simp only [Language.mem_inf, Set.mem_inter_iff]
  constructor
  · rintro ⟨v, V, hrep, hreal⟩
    refine ⟨⟨v, V, hrep⟩, ?_⟩
    rw [somewhereDFA_accepts_iff]
    simp only [bothMarkerBool_eq_true]
    apply (somewhere_fo_so_iff hrep _ _).mpr
    letI := markedWordStructure w
    rw [markedRealize_iff_realize] at hreal
    change t.realize v ∈ V X at hreal
    simpa only [wordTerm_realize] using hreal
  · rintro ⟨⟨v, V, hrep⟩, hsome⟩
    refine ⟨v, V, hrep, ?_⟩
    rw [somewhereDFA_accepts_iff] at hsome
    simp only [bothMarkerBool_eq_true] at hsome
    have hx := (somewhere_fo_so_iff hrep _ _).mp hsome
    letI := markedWordStructure w
    rw [markedRealize_iff_realize]
    change t.realize v ∈ V X
    simpa only [wordTerm_realize] using hx

theorem formulaLanguage_letter {Sigma : Type u} [DecidableEq Sigma] {n m : Nat}
    (a : Sigma) (t : (wordLanguage Sigma).Term (Fin n)) :
    formulaLanguage
        (MSOSyntax.Formula.rel (WordRelation.letter a) (fun _ => t) :
          MSOSyntax.Formula (wordLanguage Sigma) n m) =
      validMarkedLanguage Sigma n m ⊓
        (somewhereDFA (letterMarkerBool a (wordTermVar t))).accepts := by
  classical
  ext w
  simp only [Language.mem_inf, Set.mem_inter_iff]
  constructor
  · rintro ⟨v, V, hrep, hreal⟩
    refine ⟨⟨v, V, hrep⟩, ?_⟩
    rw [somewhereDFA_accepts_iff]
    simp only [letterMarkerBool_eq_true]
    apply (somewhere_letter_iff hrep _ _).mpr
    letI := markedWordStructure w
    rw [markedRealize_iff_realize] at hreal
    change (w.get (t.realize v)).1 = a at hreal
    simpa only [wordTerm_realize] using hreal
  · rintro ⟨⟨v, V, hrep⟩, hsome⟩
    refine ⟨v, V, hrep, ?_⟩
    rw [somewhereDFA_accepts_iff] at hsome
    simp only [letterMarkerBool_eq_true] at hsome
    have hx := (somewhere_letter_iff hrep _ _).mp hsome
    letI := markedWordStructure w
    rw [markedRealize_iff_realize]
    change (w.get (t.realize v)).1 = a
    simpa only [wordTerm_realize] using hx

theorem formulaLanguage_le {Sigma : Type u} {n m : Nat}
    (t₁ t₂ : (wordLanguage Sigma).Term (Fin n)) :
    formulaLanguage
        (MSOSyntax.Formula.rel WordRelation.le (fun i => Fin.cases t₁ (fun _ => t₂) i) :
          MSOSyntax.Formula (wordLanguage Sigma) n m) =
      validMarkedLanguage Sigma n m ⊓
        (orderDFA (markerBool (Sum.inl (wordTermVar t₁)))
          (markerBool (Sum.inl (wordTermVar t₂)))).accepts := by
  classical
  ext w
  simp only [Language.mem_inf, Set.mem_inter_iff]
  constructor
  · rintro ⟨v, V, hrep, hreal⟩
    refine ⟨⟨v, V, hrep⟩, ?_⟩
    rw [orderDFA_accepts_iff]
    simp only [markerBool_eq_true]
    apply (ordered_fo_iff hrep _ _).mpr
    letI := markedWordStructure w
    rw [markedRealize_iff_realize] at hreal
    change t₁.realize v ≤ t₂.realize v at hreal
    simpa only [wordTerm_realize] using hreal
  · rintro ⟨⟨v, V, hrep⟩, horder⟩
    refine ⟨v, V, hrep, ?_⟩
    rw [orderDFA_accepts_iff] at horder
    simp only [markerBool_eq_true] at horder
    have hxy := (ordered_fo_iff hrep _ _).mp horder
    letI := markedWordStructure w
    rw [markedRealize_iff_realize]
    change t₁.realize v ≤ t₂.realize v
    simpa only [wordTerm_realize] using hxy

theorem formulaLanguage_or {Sigma : Type u} {n m : Nat}
    (phi psi : MSOSyntax.Formula (wordLanguage Sigma) n m) :
    formulaLanguage (.or phi psi) = formulaLanguage phi + formulaLanguage psi := by
  ext w
  simp only [Language.mem_add]
  constructor
  · rintro ⟨v, V, hrep, hreal⟩
    obtain hphi | hpsi := (markedRealize_or w phi psi v V).mp hreal
    · exact Or.inl ⟨v, V, hrep, hphi⟩
    · exact Or.inr ⟨v, V, hrep, hpsi⟩
  · rintro (⟨v, V, hrep, hphi⟩ | ⟨v, V, hrep, hpsi⟩)
    · exact ⟨v, V, hrep, (markedRealize_or w phi psi v V).mpr (Or.inl hphi)⟩
    · exact ⟨v, V, hrep, (markedRealize_or w phi psi v V).mpr (Or.inr hpsi)⟩

theorem formulaLanguage_neg {Sigma : Type u} {n m : Nat}
    (phi : MSOSyntax.Formula (wordLanguage Sigma) n m) :
    formulaLanguage (.neg phi) =
      validMarkedLanguage Sigma n m ⊓ (formulaLanguage phi)ᶜ := by
  classical
  ext w
  simp only [Language.mem_inf, Set.mem_inter_iff, Set.mem_compl_iff]
  constructor
  · rintro ⟨v, V, hrep, hreal⟩
    have hnphi := (markedRealize_neg w phi v V).mp hreal
    refine ⟨⟨v, V, hrep⟩, ?_⟩
    rintro ⟨v', V', hrep', hphi⟩
    obtain ⟨rfl, rfl⟩ := represents_unique hrep hrep'
    exact hnphi hphi
  · rintro ⟨⟨v, V, hrep⟩, hnot⟩
    refine ⟨v, V, hrep, (markedRealize_neg w phi v V).mpr ?_⟩
    intro hphi
    exact hnot ⟨v, V, hrep, hphi⟩

/-! ## Projection of a bound-variable track -/

/-- Forget the marker for the newly bound first-order variable, shifting the
remaining first-order marker indices down by one. -/
def dropFO {Sigma : Type u} {n m : Nat} :
    MarkedLetter Sigma (n + 1) m → MarkedLetter Sigma n m :=
  fun a => (a.1, {z | match z with
    | Sum.inl x => Sum.inl x.succ ∈ a.2
    | Sum.inr X => Sum.inr X ∈ a.2})

@[simp] theorem dropFO_fst {Sigma : Type u} {n m : Nat}
    (a : MarkedLetter Sigma (n + 1) m) : (dropFO a).1 = a.1 := rfl

@[simp] theorem mem_dropFO_inl {Sigma : Type u} {n m : Nat}
    (a : MarkedLetter Sigma (n + 1) m) (x : Fin n) :
    Sum.inl x ∈ (dropFO a).2 ↔ Sum.inl x.succ ∈ a.2 := Iff.rfl

@[simp] theorem mem_dropFO_inr {Sigma : Type u} {n m : Nat}
    (a : MarkedLetter Sigma (n + 1) m) (X : Fin m) :
    Sum.inr X ∈ (dropFO a).2 ↔ Sum.inr X ∈ a.2 := Iff.rfl

/-- Forget the marker for the newly bound monadic variable, shifting the
remaining monadic marker indices down by one. -/
def dropSO {Sigma : Type u} {n m : Nat} :
    MarkedLetter Sigma n (m + 1) → MarkedLetter Sigma n m :=
  fun a => (a.1, {z | match z with
    | Sum.inl x => Sum.inl x ∈ a.2
    | Sum.inr X => Sum.inr X.succ ∈ a.2})

@[simp] theorem dropSO_fst {Sigma : Type u} {n m : Nat}
    (a : MarkedLetter Sigma n (m + 1)) : (dropSO a).1 = a.1 := rfl

@[simp] theorem mem_dropSO_inl {Sigma : Type u} {n m : Nat}
    (a : MarkedLetter Sigma n (m + 1)) (x : Fin n) :
    Sum.inl x ∈ (dropSO a).2 ↔ Sum.inl x ∈ a.2 := Iff.rfl

@[simp] theorem mem_dropSO_inr {Sigma : Type u} {n m : Nat}
    (a : MarkedLetter Sigma n (m + 1)) (X : Fin m) :
    Sum.inr X ∈ (dropSO a).2 ↔ Sum.inr X.succ ∈ a.2 := Iff.rfl

/-- The position equivalence induced by mapping `dropFO` over a word. -/
noncomputable def dropFOEquiv {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma (n + 1) m)) :
    @FirstOrder.Language.Equiv (wordLanguage Sigma)
      (Fin w.length) (Fin (w.map dropFO).length)
      (markedWordStructure w) (markedWordStructure (w.map dropFO)) := by
  letI : (wordLanguage Sigma).Structure (Fin w.length) := markedWordStructure w
  letI : (wordLanguage Sigma).Structure (Fin (w.map dropFO).length) :=
    markedWordStructure (w.map dropFO)
  let hlen : w.length = (w.map dropFO).length := by simp
  let e : Fin w.length ≃ Fin (w.map dropFO).length := finCongr hlen
  have he (i : Fin w.length) : (e i).val = i.val := by simp [e]
  refine ⟨e, ?_, ?_⟩
  · intro k f xs
    exact nomatch f
  · intro k r xs
    cases r with
    | letter a =>
        change ((w.map dropFO).get (e (xs 0))).1 = a ↔ (w.get (xs 0)).1 = a
        simp [e, dropFO]
    | le =>
        change e (xs 0) ≤ e (xs 1) ↔ xs 0 ≤ xs 1
        simp only [Fin.le_iff_val_le_val, he]

/-- The position equivalence induced by mapping `dropSO` over a word. -/
noncomputable def dropSOEquiv {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n (m + 1))) :
    @FirstOrder.Language.Equiv (wordLanguage Sigma)
      (Fin w.length) (Fin (w.map dropSO).length)
      (markedWordStructure w) (markedWordStructure (w.map dropSO)) := by
  letI : (wordLanguage Sigma).Structure (Fin w.length) := markedWordStructure w
  letI : (wordLanguage Sigma).Structure (Fin (w.map dropSO).length) :=
    markedWordStructure (w.map dropSO)
  let hlen : w.length = (w.map dropSO).length := by simp
  let e : Fin w.length ≃ Fin (w.map dropSO).length := finCongr hlen
  have he (i : Fin w.length) : (e i).val = i.val := by simp [e]
  refine ⟨e, ?_, ?_⟩
  · intro k f xs
    exact nomatch f
  · intro k r xs
    cases r with
    | letter a =>
        change ((w.map dropSO).get (e (xs 0))).1 = a ↔ (w.get (xs 0)).1 = a
        simp [e, dropSO]
    | le =>
        change e (xs 0) ≤ e (xs 1) ↔ xs 0 ≤ xs 1
        simp only [Fin.le_iff_val_le_val, he]

/-- Add a first-order marker at the chosen position and shift all old
first-order marker indices up by one. -/
def addFOLetter {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (x : Fin w.length) (i : Fin w.length) :
    MarkedLetter Sigma (n + 1) m :=
  ((w.get i).1, {z | match z with
    | Sum.inl y => Fin.cases (i = x) (fun y => Sum.inl y ∈ (w.get i).2) y
    | Sum.inr X => Sum.inr X ∈ (w.get i).2})

/-- Add a chosen first-order valuation track to a marked word. -/
def addFO {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (x : Fin w.length) :
    List (MarkedLetter Sigma (n + 1) m) :=
  List.ofFn (addFOLetter w x)

/-- Positions of `addFO w x` are canonically the positions of `w`. -/
def addFOPosEquiv {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (x : Fin w.length) :
    Fin (addFO w x).length ≃ Fin w.length :=
  finCongr (by simp [addFO])

@[simp] theorem addFOPosEquiv_coe {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (x : Fin w.length)
    (i : Fin (addFO w x).length) :
    ((addFOPosEquiv w x i : Fin w.length) : Nat) = i := rfl

@[simp] theorem addFO_get {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (x : Fin w.length)
    (i : Fin (addFO w x).length) :
    (addFO w x).get i = addFOLetter w x (addFOPosEquiv w x i) := by
  unfold addFO
  rw [List.get_ofFn]
  congr

@[simp] theorem dropFO_addFOLetter {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (x i : Fin w.length) :
    dropFO (addFOLetter w x i) = w.get i := by
  apply Prod.ext
  · rfl
  · ext z
    cases z with
    | inl y => simp [dropFO, addFOLetter]
    | inr X => rfl

@[simp] theorem map_dropFO_addFO {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (x : Fin w.length) :
    (addFO w x).map dropFO = w := by
  rw [addFO, ← List.ofFn_comp']
  simp

/-- Add a monadic marker according to the chosen set and shift all old
monadic marker indices up by one. -/
def addSOLetter {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (X : Set (Fin w.length)) (i : Fin w.length) :
    MarkedLetter Sigma n (m + 1) :=
  ((w.get i).1, {z | match z with
    | Sum.inl x => Sum.inl x ∈ (w.get i).2
    | Sum.inr Y => Fin.cases (i ∈ X) (fun Y => Sum.inr Y ∈ (w.get i).2) Y})

/-- Add a chosen monadic valuation track to a marked word. -/
def addSO {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (X : Set (Fin w.length)) :
    List (MarkedLetter Sigma n (m + 1)) :=
  List.ofFn (addSOLetter w X)

/-- Positions of `addSO w X` are canonically the positions of `w`. -/
def addSOPosEquiv {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (X : Set (Fin w.length)) :
    Fin (addSO w X).length ≃ Fin w.length :=
  finCongr (by simp [addSO])

@[simp] theorem addSOPosEquiv_coe {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (X : Set (Fin w.length))
    (i : Fin (addSO w X).length) :
    ((addSOPosEquiv w X i : Fin w.length) : Nat) = i := rfl

@[simp] theorem addSO_get {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (X : Set (Fin w.length))
    (i : Fin (addSO w X).length) :
    (addSO w X).get i = addSOLetter w X (addSOPosEquiv w X i) := by
  unfold addSO
  rw [List.get_ofFn]
  congr

@[simp] theorem dropSO_addSOLetter {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (X : Set (Fin w.length)) (i : Fin w.length) :
    dropSO (addSOLetter w X i) = w.get i := by
  apply Prod.ext
  · rfl
  · ext z
    cases z with
    | inl x => rfl
    | inr Y => simp [dropSO, addSOLetter]

@[simp] theorem map_dropSO_addSO {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (X : Set (Fin w.length)) :
    (addSO w X).map dropSO = w := by
  rw [addSO, ← List.ofFn_comp']
  simp

theorem represents_dropFO {Sigma : Type u} {n m : Nat}
    {w : List (MarkedLetter Sigma (n + 1) m)}
    {v : Fin (n + 1) → Fin w.length} {V : Fin m → Set (Fin w.length)}
    (h : Represents w v V) :
    Represents (w.map dropFO)
      (fun x => dropFOEquiv w (v x.succ))
      (fun X => dropFOEquiv w '' V X) := by
  letI : (wordLanguage Sigma).Structure (Fin w.length) := markedWordStructure w
  letI : (wordLanguage Sigma).Structure (Fin (w.map dropFO).length) :=
    markedWordStructure (w.map dropFO)
  let e : Fin w.length ≃[wordLanguage Sigma] Fin (w.map dropFO).length := dropFOEquiv w
  constructor
  · intro i x
    obtain ⟨j, rfl⟩ := e.surjective i
    change Sum.inl x ∈ ((w.map dropFO).get (e j)).2 ↔ e (v x.succ) = e j
    rw [e.injective.eq_iff]
    simpa [e, dropFOEquiv, dropFO] using! h.1 j x.succ
  · intro i X
    obtain ⟨j, rfl⟩ := e.surjective i
    change Sum.inr X ∈ ((w.map dropFO).get (e j)).2 ↔ e j ∈ e '' V X
    simpa [e, dropFOEquiv, dropFO, e.injective.eq_iff] using! h.2 j X

theorem represents_dropSO {Sigma : Type u} {n m : Nat}
    {w : List (MarkedLetter Sigma n (m + 1))}
    {v : Fin n → Fin w.length} {V : Fin (m + 1) → Set (Fin w.length)}
    (h : Represents w v V) :
    Represents (w.map dropSO)
      (fun x => dropSOEquiv w (v x))
      (fun X => dropSOEquiv w '' V X.succ) := by
  letI : (wordLanguage Sigma).Structure (Fin w.length) := markedWordStructure w
  letI : (wordLanguage Sigma).Structure (Fin (w.map dropSO).length) :=
    markedWordStructure (w.map dropSO)
  let e : Fin w.length ≃[wordLanguage Sigma] Fin (w.map dropSO).length := dropSOEquiv w
  constructor
  · intro i x
    obtain ⟨j, rfl⟩ := e.surjective i
    change Sum.inl x ∈ ((w.map dropSO).get (e j)).2 ↔ e (v x) = e j
    rw [e.injective.eq_iff]
    simpa [e, dropSOEquiv, dropSO] using! h.1 j x
  · intro i X
    obtain ⟨j, rfl⟩ := e.surjective i
    change Sum.inr X ∈ ((w.map dropSO).get (e j)).2 ↔ e j ∈ e '' V X.succ
    simpa [e, dropSOEquiv, dropSO, e.injective.eq_iff] using! h.2 j X.succ

/-- Adding a first-order track does not change the underlying word
structure. -/
noncomputable def addFOEquiv {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (x : Fin w.length) :
    @FirstOrder.Language.Equiv (wordLanguage Sigma)
      (Fin (addFO w x).length) (Fin w.length)
      (markedWordStructure (addFO w x)) (markedWordStructure w) := by
  letI : (wordLanguage Sigma).Structure (Fin (addFO w x).length) :=
    markedWordStructure (addFO w x)
  letI : (wordLanguage Sigma).Structure (Fin w.length) := markedWordStructure w
  let e := addFOPosEquiv w x
  have he (i : Fin (addFO w x).length) : (e i).val = i.val := rfl
  refine ⟨e, ?_, ?_⟩
  · intro k f xs
    exact nomatch f
  · intro k r xs
    cases r with
    | letter a =>
        change (w.get (e (xs 0))).1 = a ↔ ((addFO w x).get (xs 0)).1 = a
        rw [addFO_get]
        rfl
    | le =>
        change e (xs 0) ≤ e (xs 1) ↔ xs 0 ≤ xs 1
        simp only [Fin.le_iff_val_le_val, he]

/-- Adding a monadic track does not change the underlying word structure. -/
noncomputable def addSOEquiv {Sigma : Type u} {n m : Nat}
    (w : List (MarkedLetter Sigma n m)) (X : Set (Fin w.length)) :
    @FirstOrder.Language.Equiv (wordLanguage Sigma)
      (Fin (addSO w X).length) (Fin w.length)
      (markedWordStructure (addSO w X)) (markedWordStructure w) := by
  letI : (wordLanguage Sigma).Structure (Fin (addSO w X).length) :=
    markedWordStructure (addSO w X)
  letI : (wordLanguage Sigma).Structure (Fin w.length) := markedWordStructure w
  let e := addSOPosEquiv w X
  have he (i : Fin (addSO w X).length) : (e i).val = i.val := rfl
  refine ⟨e, ?_, ?_⟩
  · intro k f xs
    exact nomatch f
  · intro k r xs
    cases r with
    | letter a =>
        change (w.get (e (xs 0))).1 = a ↔ ((addSO w X).get (xs 0)).1 = a
        rw [addSO_get]
        rfl
    | le =>
        change e (xs 0) ≤ e (xs 1) ↔ xs 0 ≤ xs 1
        simp only [Fin.le_iff_val_le_val, he]

theorem represents_addFO {Sigma : Type u} {n m : Nat}
    {w : List (MarkedLetter Sigma n m)}
    {v : Fin n → Fin w.length} {V : Fin m → Set (Fin w.length)}
    (h : Represents w v V) (x : Fin w.length) :
    Represents (addFO w x)
      (fun y => (addFOPosEquiv w x).symm (MSOSemantics.consVal x v y))
      (fun X => (addFOPosEquiv w x).symm '' V X) := by
  let e := addFOPosEquiv w x
  constructor
  · intro i y
    rw [addFO_get]
    refine Fin.cases ?_ (fun z => ?_) y
    · change e i = x ↔ e.symm x = i
      constructor
      · intro hi
        apply e.injective
        simpa using hi.symm
      · intro hi
        have := congrArg e hi
        simpa using this.symm
    · change Sum.inl z ∈ (w.get (e i)).2 ↔ e.symm (v z) = i
      rw [h.1 (e i) z]
      constructor
      · intro hi
        apply e.injective
        simpa using hi
      · intro hi
        have := congrArg e hi
        simpa using this
  · intro i X
    rw [addFO_get]
    change Sum.inr X ∈ (w.get (e i)).2 ↔ e.symm (e i) ∈ e.symm '' V X
    rw [h.2 (e i) X]
    simp [e]

theorem represents_addSO {Sigma : Type u} {n m : Nat}
    {w : List (MarkedLetter Sigma n m)}
    {v : Fin n → Fin w.length} {V : Fin m → Set (Fin w.length)}
    (h : Represents w v V) (X : Set (Fin w.length)) :
    Represents (addSO w X)
      (fun x => (addSOPosEquiv w X).symm (v x))
      (fun Y => (addSOPosEquiv w X).symm '' MSOSemantics.consVal X V Y) := by
  let e := addSOPosEquiv w X
  constructor
  · intro i x
    rw [addSO_get]
    change Sum.inl x ∈ (w.get (e i)).2 ↔ e.symm (v x) = i
    rw [h.1 (e i) x]
    change v x = e i ↔ e.symm (v x) = i
    constructor
    · intro hi
      apply e.injective
      simpa using hi
    · intro hi
      have := congrArg e hi
      simpa using this
  · intro i Y
    rw [addSO_get]
    refine Fin.cases ?_ (fun Z => ?_) Y
    · change e i ∈ X ↔ i ∈ e.symm '' X
      simp [e]
    · change Sum.inr Z ∈ (w.get (e i)).2 ↔ i ∈ e.symm '' V Z
      rw [h.2 (e i) Z]
      simp [e]

theorem formulaLanguage_exFO {Sigma : Type u} {n m : Nat}
    (phi : MSOSyntax.Formula (wordLanguage Sigma) (n + 1) m) :
    formulaLanguage (.exFO phi) = Language.map dropFO (formulaLanguage phi) := by
  classical
  ext w
  constructor
  · rintro ⟨v, V, hrep, hreal⟩
    letI : (wordLanguage Sigma).Structure (Fin w.length) := markedWordStructure w
    rw [markedRealize_iff_realize] at hreal
    change ∃ x : Fin w.length,
      MSOSemantics.Realize phi (MSOSemantics.consVal x v) V at hreal
    obtain ⟨x, hx⟩ := hreal
    let u := addFO w x
    letI : (wordLanguage Sigma).Structure (Fin u.length) := markedWordStructure u
    let e : Fin u.length ≃[wordLanguage Sigma] Fin w.length := addFOEquiv w x
    let v' : Fin (n + 1) → Fin u.length :=
      fun y => e.symm (MSOSemantics.consVal x v y)
    let V' : Fin m → Set (Fin u.length) := fun X => e.symm '' V X
    have hrep' : Represents u v' V' := by
      simpa [u, e, v', V'] using! represents_addFO hrep x
    have hv : e ∘ v' = MSOSemantics.consVal x v := by
      funext y
      simp [v']
    have hV : (fun X => e '' V' X) = V := by
      funext X
      ext i
      simp [V']
    have hphi' : MSOSemantics.Realize phi v' V' := by
      apply (MSOSemantics.realize_equiv e phi v' V').mp
      rw [hv, hV]
      exact hx
    change w ∈ Set.image (List.map dropFO) (formulaLanguage phi)
    refine ⟨u, ⟨v', V', hrep', ?_⟩, ?_⟩
    · exact (markedRealize_iff_realize u phi v' V').mpr hphi'
    · simpa [u] using map_dropFO_addFO w x
  · change w ∈ Set.image (List.map dropFO) (formulaLanguage phi) → _
    rintro ⟨u, ⟨v, V, hrep, hphi⟩, rfl⟩
    letI : (wordLanguage Sigma).Structure (Fin u.length) := markedWordStructure u
    letI : (wordLanguage Sigma).Structure (Fin (u.map dropFO).length) :=
      markedWordStructure (u.map dropFO)
    let e : Fin u.length ≃[wordLanguage Sigma] Fin (u.map dropFO).length := dropFOEquiv u
    let v' : Fin n → Fin (u.map dropFO).length := fun x => e (v x.succ)
    let V' : Fin m → Set (Fin (u.map dropFO).length) := fun X => e '' V X
    refine ⟨v', V', by simpa [e, v', V'] using represents_dropFO hrep, ?_⟩
    rw [markedRealize_iff_realize]
    change ∃ x : Fin (u.map dropFO).length,
      MSOSemantics.Realize phi (MSOSemantics.consVal x v') V'
    refine ⟨e (v 0), ?_⟩
    have hv : MSOSemantics.consVal (e (v 0)) v' = e ∘ v := by
      funext y
      refine Fin.cases ?_ (fun z => ?_) y
      · simp [MSOSemantics.consVal]
      · rfl
    rw [hv]
    rw [markedRealize_iff_realize] at hphi
    exact (MSOSemantics.realize_equiv e phi v V).mpr hphi

theorem formulaLanguage_exSO {Sigma : Type u} {n m : Nat}
    (phi : MSOSyntax.Formula (wordLanguage Sigma) n (m + 1)) :
    formulaLanguage (.exSO phi) = Language.map dropSO (formulaLanguage phi) := by
  classical
  ext w
  constructor
  · rintro ⟨v, V, hrep, hreal⟩
    letI : (wordLanguage Sigma).Structure (Fin w.length) := markedWordStructure w
    rw [markedRealize_iff_realize] at hreal
    change ∃ X : Set (Fin w.length),
      MSOSemantics.Realize phi v (MSOSemantics.consVal X V) at hreal
    obtain ⟨X, hX⟩ := hreal
    let u := addSO w X
    letI : (wordLanguage Sigma).Structure (Fin u.length) := markedWordStructure u
    let e : Fin u.length ≃[wordLanguage Sigma] Fin w.length := addSOEquiv w X
    let v' : Fin n → Fin u.length := fun x => e.symm (v x)
    let V' : Fin (m + 1) → Set (Fin u.length) :=
      fun Y => e.symm '' MSOSemantics.consVal X V Y
    have hrep' : Represents u v' V' := by
      simpa [u, e, v', V'] using! represents_addSO hrep X
    have hv : e ∘ v' = v := by
      funext x
      simp [v']
    have hV : (fun Y => e '' V' Y) = MSOSemantics.consVal X V := by
      funext Y
      ext i
      simp [V']
    have hphi' : MSOSemantics.Realize phi v' V' := by
      apply (MSOSemantics.realize_equiv e phi v' V').mp
      rw [hv, hV]
      exact hX
    change w ∈ Set.image (List.map dropSO) (formulaLanguage phi)
    refine ⟨u, ⟨v', V', hrep', ?_⟩, ?_⟩
    · exact (markedRealize_iff_realize u phi v' V').mpr hphi'
    · simpa [u] using map_dropSO_addSO w X
  · change w ∈ Set.image (List.map dropSO) (formulaLanguage phi) → _
    rintro ⟨u, ⟨v, V, hrep, hphi⟩, rfl⟩
    letI : (wordLanguage Sigma).Structure (Fin u.length) := markedWordStructure u
    letI : (wordLanguage Sigma).Structure (Fin (u.map dropSO).length) :=
      markedWordStructure (u.map dropSO)
    let e : Fin u.length ≃[wordLanguage Sigma] Fin (u.map dropSO).length := dropSOEquiv u
    let v' : Fin n → Fin (u.map dropSO).length := fun x => e (v x)
    let V' : Fin m → Set (Fin (u.map dropSO).length) := fun X => e '' V X.succ
    refine ⟨v', V', by simpa [e, v', V'] using represents_dropSO hrep, ?_⟩
    rw [markedRealize_iff_realize]
    change ∃ X : Set (Fin (u.map dropSO).length),
      MSOSemantics.Realize phi v' (MSOSemantics.consVal X V')
    refine ⟨e '' V 0, ?_⟩
    have hV : MSOSemantics.consVal (e '' V 0) V' = fun Y => e '' V Y := by
      funext Y
      refine Fin.cases rfl (fun _ => rfl) Y
    rw [hV]
    rw [markedRealize_iff_realize] at hphi
    exact (MSOSemantics.realize_equiv e phi v V).mpr hphi

theorem formulaLanguage_isRegular_proof {Sigma : Type u} [Fintype Sigma] {n m : Nat}
    (phi : MSOSyntax.Formula (wordLanguage Sigma) n m) :
    (formulaLanguage phi).IsRegular := by
  classical
  induction phi with
  | falsum =>
      rw [formulaLanguage_falsum]
      exact emptyLanguage_isRegular
  | @equal n' m' t₁ t₂ =>
      rw [formulaLanguage_equal]
      exact (validMarkedLanguage_isRegular_proof (Sigma := Sigma) n' m').inf
        (somewhereDFA_isRegular _)
  | @rel n' m' k r ts =>
      cases r with
      | letter a =>
          let t := ts 0
          have hts : ts = fun _ => t := by
            funext i
            have hi : i = 0 := Fin.eq_zero i
            subst i
            rfl
          rw [hts, formulaLanguage_letter]
          exact (validMarkedLanguage_isRegular_proof (Sigma := Sigma) n' m').inf
            (somewhereDFA_isRegular _)
      | le =>
          let t₁ := ts 0
          let t₂ := ts 1
          have hts : ts = fun i => Fin.cases t₁ (fun _ => t₂) i := by
            funext i
            obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
            · rfl
            · have hj : j = 0 := Fin.eq_zero j
              subst j
              rfl
          rw [hts, formulaLanguage_le]
          exact (validMarkedLanguage_isRegular_proof (Sigma := Sigma) n' m').inf
            (orderDFA_isRegular _ _)
  | @mem n' m' t X =>
      rw [formulaLanguage_mem]
      exact (validMarkedLanguage_isRegular_proof (Sigma := Sigma) n' m').inf
        (somewhereDFA_isRegular _)
  | or phi psi ihphi ihpsi =>
      rw [formulaLanguage_or]
      exact ihphi.add ihpsi
  | @neg n' m' phi ih =>
      rw [formulaLanguage_neg]
      exact (validMarkedLanguage_isRegular_proof (Sigma := Sigma) n' m').inf ih.compl
  | exFO phi ih =>
      rw [formulaLanguage_exFO]
      exact Language.IsRegular.map ih dropFO
  | exSO phi ih =>
      rw [formulaLanguage_exSO]
      exact Language.IsRegular.map ih dropSO

end Lax146103Proofs
