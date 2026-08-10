import Lax52Proofs.SemanticTransport

namespace Lax52Proofs

open FirstOrder
open FirstOrder.Language
open Lax52
open Lax52.MSOSyntax
open Lax52.MSOSemantics
open Lax52.WordStructure
open Lax52.MarkedWords
open Lax52.NFARecognizable
open Lax52.ValidMarkedWordsRegular
open Lax52.MSOFormulaRegularity
open Lax52.NFAToMSO
open Lax52.MSOToNFA

universe u

namespace RunFormula

/-- A formula which records a proposition decided while constructing the
finite automaton formula. -/
noncomputable def holds {Sigma : Type u} {n m : Nat} (P : Prop) :
    MSOSyntax.Formula (wordLanguage Sigma) n m := by
  classical
  exact if P then .verum else .falsum

theorem realize_holds {Sigma : Type u} {n m : Nat} (P : Prop)
    {M : Type*} [((wordLanguage Sigma).Structure M)]
    (v : Fin n → M) (V : Fin m → Set M) :
    MSOSemantics.Realize (holds (Sigma := Sigma) P) v V ↔ P := by
  classical
  by_cases h : P <;> simp [holds, h]

/-- Finite disjunction indexed by `Fin k`. -/
def anyFin {Sigma : Type u} {n m : Nat} :
    (k : Nat) → (Fin k → MSOSyntax.Formula (wordLanguage Sigma) n m) →
      MSOSyntax.Formula (wordLanguage Sigma) n m
  | 0, _ => .falsum
  | k + 1, f => .or (f 0) (anyFin k (fun i => f i.succ))

/-- Finite conjunction indexed by `Fin k`. -/
def allFin {Sigma : Type u} {n m : Nat} :
    (k : Nat) → (Fin k → MSOSyntax.Formula (wordLanguage Sigma) n m) →
      MSOSyntax.Formula (wordLanguage Sigma) n m
  | 0, _ => .verum
  | k + 1, f => .and (f 0) (allFin k (fun i => f i.succ))

theorem realize_anyFin {Sigma : Type u} {n m k : Nat}
    (f : Fin k → MSOSyntax.Formula (wordLanguage Sigma) n m)
    {M : Type*} [((wordLanguage Sigma).Structure M)]
    (v : Fin n → M) (V : Fin m → Set M) :
    MSOSemantics.Realize (anyFin k f) v V ↔
      ∃ i : Fin k, MSOSemantics.Realize (f i) v V := by
  induction k with
  | zero => simp [anyFin]
  | succ k ih =>
      simp only [anyFin, MSOSemantics.realize_or, ih]
      constructor
      · rintro (h | ⟨i, hi⟩)
        · exact ⟨0, h⟩
        · exact ⟨i.succ, hi⟩
      · rintro ⟨i, hi⟩
        obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
        · exact Or.inl hi
        · exact Or.inr ⟨j, hi⟩

theorem realize_allFin {Sigma : Type u} {n m k : Nat}
    (f : Fin k → MSOSyntax.Formula (wordLanguage Sigma) n m)
    {M : Type*} [((wordLanguage Sigma).Structure M)]
    (v : Fin n → M) (V : Fin m → Set M) :
    MSOSemantics.Realize (allFin k f) v V ↔
      ∀ i : Fin k, MSOSemantics.Realize (f i) v V := by
  induction k with
  | zero => simp [allFin]
  | succ k ih =>
      simp only [allFin, MSOSemantics.realize_and, ih]
      constructor
      · rintro ⟨h0, hs⟩ i
        refine Fin.cases h0 (fun j => hs j) i
      · intro h
        exact ⟨h 0, fun i => h i.succ⟩

/-- Close all monadic variables, binding marker `0`, then `1`, and so on. -/
def closeSO {Sigma : Type u} {n : Nat} :
    (m : Nat) → MSOSyntax.Formula (wordLanguage Sigma) n m →
      MSOSyntax.Formula (wordLanguage Sigma) n 0
  | 0, phi => phi
  | m + 1, phi => closeSO m (.exSO phi)

theorem realize_closeSO {Sigma : Type u} {n m : Nat}
    (phi : MSOSyntax.Formula (wordLanguage Sigma) n m)
    {M : Type*} [((wordLanguage Sigma).Structure M)]
    (v : Fin n → M) :
    MSOSemantics.Realize (closeSO m phi) v (fun i : Fin 0 => Fin.elim0 i) ↔
      ∃ V : Fin m → Set M, MSOSemantics.Realize phi v V := by
  induction m with
  | zero =>
      constructor
      · intro h
        exact ⟨fun i => Fin.elim0 i, h⟩
      · rintro ⟨V, h⟩
        simpa only [Subsingleton.elim V (fun i : Fin 0 => Fin.elim0 i)] using h
  | succ m ih =>
      rw [closeSO, ih]
      simp only [MSOSemantics.realize_exSO]
      constructor
      · rintro ⟨V, X, h⟩
        exact ⟨MSOSemantics.consVal X V, h⟩
      · rintro ⟨W, hW⟩
        let V : Fin m → Set M := fun i => W i.succ
        refine ⟨V, W 0, ?_⟩
        have hcons : MSOSemantics.consVal (W 0) V = W := by
          funext i
          refine Fin.cases rfl (fun _ => rfl) i
        rwa [hcons]

def var {Sigma : Type u} {n : Nat} (x : Fin n) :
    (wordLanguage Sigma).Term (Fin n) := .var x

def mem {Sigma : Type u} {n m : Nat} (x : Fin n) (X : Fin m) :
    MSOSyntax.Formula (wordLanguage Sigma) n m := .mem (var x) X

def letter {Sigma : Type u} {n m : Nat} (a : Sigma) (x : Fin n) :
    MSOSyntax.Formula (wordLanguage Sigma) n m :=
  .rel (WordRelation.letter a) (fun _ => var x)

def le {Sigma : Type u} {n m : Nat} (x y : Fin n) :
    MSOSyntax.Formula (wordLanguage Sigma) n m :=
  .rel WordRelation.le (fun i => Fin.cases (var x) (fun _ => var y) i)

def eq {Sigma : Type u} {n m : Nat} (x y : Fin n) :
    MSOSyntax.Formula (wordLanguage Sigma) n m := .equal (var x) (var y)

def lt {Sigma : Type u} {n m : Nat} (x y : Fin n) :
    MSOSyntax.Formula (wordLanguage Sigma) n m := .and (le x y) (.neg (eq x y))

/-- `x` is the first position. -/
def first {Sigma : Type u} {n m : Nat} (x : Fin n) :
    MSOSyntax.Formula (wordLanguage Sigma) n m :=
  .allFO (le x.succ 0)

/-- `x` is the last position. -/
def last {Sigma : Type u} {n m : Nat} (x : Fin n) :
    MSOSyntax.Formula (wordLanguage Sigma) n m :=
  .allFO (le 0 x.succ)

/-- `y` is the position immediately following `x`. -/
def successor {Sigma : Type u} {n m : Nat} (x y : Fin n) :
    MSOSyntax.Formula (wordLanguage Sigma) n m :=
  .and (lt x y) (.neg (.exFO (.and (lt x.succ 0) (lt 0 y.succ))))

def Adjacent {n : Nat} (i j : Fin n) : Prop :=
  i < j ∧ ¬∃ z : Fin n, i < z ∧ z < j

theorem realize_mem {Sigma : Type u} {n m : Nat} (x : Fin n) (X : Fin m)
    {M : Type*} [((wordLanguage Sigma).Structure M)]
    (v : Fin n → M) (V : Fin m → Set M) :
    MSOSemantics.Realize (mem (Sigma := Sigma) x X) v V ↔ v x ∈ V X := Iff.rfl

theorem realize_eq {Sigma : Type u} {n m : Nat} (x y : Fin n)
    {M : Type*} [((wordLanguage Sigma).Structure M)]
    (v : Fin n → M) (V : Fin m → Set M) :
    MSOSemantics.Realize (eq (Sigma := Sigma) x y) v V ↔ v x = v y := Iff.rfl

theorem realize_letter {Sigma : Type u} {n m : Nat}
    (w : List Sigma) (a : Sigma) (x : Fin n)
    (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)) :
    @MSOSemantics.Realize _ (Fin w.length) (wordStructure w) _ _ (letter a x) v V ↔
      w.get (v x) = a := Iff.rfl

theorem realize_le {Sigma : Type u} {n m : Nat}
    (w : List Sigma) (x y : Fin n)
    (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)) :
    @MSOSemantics.Realize _ (Fin w.length) (wordStructure w) _ _ (le x y) v V ↔
      v x ≤ v y := Iff.rfl

theorem realize_lt {Sigma : Type u} {n m : Nat}
    (w : List Sigma) (x y : Fin n)
    (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)) :
    @MSOSemantics.Realize _ (Fin w.length) (wordStructure w) _ _ (lt x y) v V ↔
      v x < v y := by
  simp only [lt, MSOSemantics.realize_and, realize_le, MSOSemantics.realize_neg,
    realize_eq, lt_iff_le_and_ne]

theorem realize_first {Sigma : Type u} {n m : Nat}
    (w : List Sigma) (x : Fin n)
    (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)) :
    @MSOSemantics.Realize _ (Fin w.length) (wordStructure w) _ _ (first x) v V ↔
      ∀ y : Fin w.length, v x ≤ y := by
  simp only [first, MSOSemantics.realize_allFO, realize_le]
  rfl

theorem realize_last {Sigma : Type u} {n m : Nat}
    (w : List Sigma) (x : Fin n)
    (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)) :
    @MSOSemantics.Realize _ (Fin w.length) (wordStructure w) _ _ (last x) v V ↔
      ∀ y : Fin w.length, y ≤ v x := by
  simp only [last, MSOSemantics.realize_allFO, realize_le]
  rfl

theorem realize_successor {Sigma : Type u} {n m : Nat}
    (w : List Sigma) (x y : Fin n)
    (v : Fin n → Fin w.length) (V : Fin m → Set (Fin w.length)) :
    @MSOSemantics.Realize _ (Fin w.length) (wordStructure w) _ _ (successor x y) v V ↔
      Adjacent (v x) (v y) := by
  simp only [successor, MSOSemantics.realize_and, realize_lt,
    MSOSemantics.realize_neg, MSOSemantics.realize_exFO]
  rfl

/-- The fixed enumeration of a finite type used to associate monadic
variables with automaton states (and finite disjunctions with letters). -/
noncomputable def enum (A : Type*) [Fintype A] : Fin (Fintype.card A) ≃ A :=
  (Fintype.equivFin A).symm

variable {Sigma : Type u} [Fintype Sigma]
variable {Q : Type} [Fintype Q]

def someState (x : Fin 1) :
    MSOSyntax.Formula (wordLanguage Sigma) 1 (Fintype.card Q) :=
  anyFin (Fintype.card Q) (fun q => mem x q)

noncomputable def uniqueState (x : Fin 1) :
    MSOSyntax.Formula (wordLanguage Sigma) 1 (Fintype.card Q) :=
  .and (someState x)
    (allFin (Fintype.card Q) fun q =>
      allFin (Fintype.card Q) fun r =>
        .imp (.and (mem x q) (mem x r)) (holds (q = r)))

noncomputable def partitionFormula :
    MSOSyntax.Formula (wordLanguage Sigma) 0 (Fintype.card Q) :=
  .allFO (uniqueState 0)

noncomputable def initialFormula (M : NFA Sigma Q) :
    MSOSyntax.Formula (wordLanguage Sigma) 0 (Fintype.card Q) :=
  .allFO (.imp (first 0)
    (anyFin (Fintype.card Q) fun q =>
      .and (mem 0 q) (holds (enum Q q ∈ M.start))))

noncomputable def transitionFormula (M : NFA Sigma Q) :
    MSOSyntax.Formula (wordLanguage Sigma) 0 (Fintype.card Q) :=
  .allFO (.allFO (.imp (successor 1 0)
    (anyFin (Fintype.card Q) fun q =>
      anyFin (Fintype.card Q) fun r =>
        anyFin (Fintype.card Sigma) fun a =>
          .and (mem 1 q) (.and (mem 0 r) (.and (letter (enum Sigma a) 1)
            (holds (enum Q r ∈ M.step (enum Q q) (enum Sigma a))))))))

noncomputable def finalFormula (M : NFA Sigma Q) :
    MSOSyntax.Formula (wordLanguage Sigma) 0 (Fintype.card Q) :=
  .allFO (.imp (last 0)
    (anyFin (Fintype.card Q) fun q =>
      anyFin (Fintype.card Sigma) fun a =>
        .and (mem 0 q) (.and (letter (enum Sigma a) 0)
          (holds (∃ t ∈ M.accept, t ∈ M.step (enum Q q) (enum Sigma a))))))

noncomputable def runBody (M : NFA Sigma Q) :
    MSOSyntax.Formula (wordLanguage Sigma) 0 (Fintype.card Q) :=
  .and partitionFormula
    (.and (initialFormula M) (.and (transitionFormula M) (finalFormula M)))

def nonemptyFormula : MSOSyntax.Sentence (wordLanguage Sigma) :=
  .exFO .verum

def emptyFormula : MSOSyntax.Sentence (wordLanguage Sigma) :=
  .neg nonemptyFormula

noncomputable def runSentence (M : NFA Sigma Q) :
    MSOSyntax.Sentence (wordLanguage Sigma) :=
  .or (.and (holds (∃ q ∈ M.start, q ∈ M.accept)) emptyFormula)
    (.and nonemptyFormula (closeSO (Fintype.card Q) (runBody M)))

def StatePartition {A : Type*} (V : Fin (Fintype.card Q) → Set A) : Prop :=
  ∀ i : A, ∃! q : Fin (Fintype.card Q), i ∈ V q

def InitialCondition (M : NFA Sigma Q) (w : List Sigma)
    (V : Fin (Fintype.card Q) → Set (Fin w.length)) : Prop :=
  ∀ i : Fin w.length, (∀ j : Fin w.length, i ≤ j) →
    ∃ q : Fin (Fintype.card Q), i ∈ V q ∧ enum Q q ∈ M.start

def TransitionCondition (M : NFA Sigma Q) (w : List Sigma)
    (V : Fin (Fintype.card Q) → Set (Fin w.length)) : Prop :=
  ∀ i j : Fin w.length, Adjacent i j →
    ∃ q r : Fin (Fintype.card Q), ∃ a : Fin (Fintype.card Sigma),
      i ∈ V q ∧ j ∈ V r ∧ w.get i = enum Sigma a ∧
        enum Q r ∈ M.step (enum Q q) (enum Sigma a)

def FinalCondition (M : NFA Sigma Q) (w : List Sigma)
    (V : Fin (Fintype.card Q) → Set (Fin w.length)) : Prop :=
  ∀ i : Fin w.length, (∀ j : Fin w.length, j ≤ i) →
    ∃ q : Fin (Fintype.card Q), ∃ a : Fin (Fintype.card Sigma),
      i ∈ V q ∧ w.get i = enum Sigma a ∧
        ∃ t ∈ M.accept, t ∈ M.step (enum Q q) (enum Sigma a)

def RunValuation (M : NFA Sigma Q) (w : List Sigma)
    (V : Fin (Fintype.card Q) → Set (Fin w.length)) : Prop :=
  StatePartition V ∧ InitialCondition M w V ∧
    TransitionCondition M w V ∧ FinalCondition M w V

theorem realize_someState (x : Fin 1) {A : Type*}
    [((wordLanguage Sigma).Structure A)] (v : Fin 1 → A)
    (V : Fin (Fintype.card Q) → Set A) :
    MSOSemantics.Realize (someState (Sigma := Sigma) (Q := Q) x) v V ↔
      ∃ q : Fin (Fintype.card Q), v x ∈ V q := by
  simp [someState, realize_anyFin, realize_mem]

theorem realize_uniqueState (x : Fin 1) {A : Type*}
    [((wordLanguage Sigma).Structure A)] (v : Fin 1 → A)
    (V : Fin (Fintype.card Q) → Set A) :
    MSOSemantics.Realize (uniqueState (Sigma := Sigma) (Q := Q) x) v V ↔
      ∃! q : Fin (Fintype.card Q), v x ∈ V q := by
  simp only [uniqueState, MSOSemantics.realize_and, realize_someState,
    realize_allFin, MSOSemantics.realize_imp, realize_mem, realize_holds]
  constructor
  · rintro ⟨⟨q, hq⟩, hu⟩
    refine ⟨q, hq, ?_⟩
    intro r hr
    exact hu r q ⟨hr, hq⟩
  · rintro ⟨q, hq, hu⟩
    refine ⟨⟨q, hq⟩, ?_⟩
    intro r s hrs
    exact (hu r hrs.1).trans (hu s hrs.2).symm

theorem realize_partitionFormula (w : List Sigma)
    (V : Fin (Fintype.card Q) → Set (Fin w.length)) :
    @MSOSemantics.Realize _ (Fin w.length) (wordStructure w) _ _
      (partitionFormula (Sigma := Sigma) (Q := Q))
      (fun i : Fin 0 => Fin.elim0 i) V ↔ StatePartition V := by
  simp only [partitionFormula, MSOSemantics.realize_allFO, realize_uniqueState]
  rfl

theorem realize_initialFormula (M : NFA Sigma Q) (w : List Sigma)
    (V : Fin (Fintype.card Q) → Set (Fin w.length)) :
    @MSOSemantics.Realize _ (Fin w.length) (wordStructure w) _ _
      (initialFormula M) (fun i : Fin 0 => Fin.elim0 i) V ↔
      InitialCondition M w V := by
  simp only [initialFormula, MSOSemantics.realize_allFO, MSOSemantics.realize_imp,
    realize_first, realize_anyFin, MSOSemantics.realize_and, realize_mem, realize_holds]
  rfl

theorem realize_transitionFormula (M : NFA Sigma Q) (w : List Sigma)
    (V : Fin (Fintype.card Q) → Set (Fin w.length)) :
    @MSOSemantics.Realize _ (Fin w.length) (wordStructure w) _ _
      (transitionFormula M) (fun i : Fin 0 => Fin.elim0 i) V ↔
      TransitionCondition M w V := by
  simp only [transitionFormula, MSOSemantics.realize_allFO,
    MSOSemantics.realize_imp, realize_successor, realize_anyFin,
    MSOSemantics.realize_and, realize_mem, realize_letter, realize_holds]
  rfl

theorem realize_finalFormula (M : NFA Sigma Q) (w : List Sigma)
    (V : Fin (Fintype.card Q) → Set (Fin w.length)) :
    @MSOSemantics.Realize _ (Fin w.length) (wordStructure w) _ _
      (finalFormula M) (fun i : Fin 0 => Fin.elim0 i) V ↔
      FinalCondition M w V := by
  simp only [finalFormula, MSOSemantics.realize_allFO, MSOSemantics.realize_imp,
    realize_last, realize_anyFin, MSOSemantics.realize_and, realize_mem,
    realize_letter, realize_holds]
  rfl

theorem realize_runBody (M : NFA Sigma Q) (w : List Sigma)
    (V : Fin (Fintype.card Q) → Set (Fin w.length)) :
    @MSOSemantics.Realize _ (Fin w.length) (wordStructure w) _ _
      (runBody M) (fun i : Fin 0 => Fin.elim0 i) V ↔ RunValuation M w V := by
  simp only [runBody, MSOSemantics.realize_and, realize_partitionFormula,
    realize_initialFormula, realize_transitionFormula, realize_finalFormula,
    RunValuation]

def FirstPos {n : Nat} (i : Fin n) : Prop := ∀ j : Fin n, i ≤ j
def LastPos {n : Nat} (i : Fin n) : Prop := ∀ j : Fin n, j ≤ i

def PositionRun (M : NFA Sigma Q) (w : List Sigma)
    (r : Fin w.length → Q) : Prop :=
  (∀ i : Fin w.length, FirstPos i → r i ∈ M.start) ∧
  (∀ i j : Fin w.length, Adjacent i j → r j ∈ M.step (r i) (w.get i)) ∧
  (∀ i : Fin w.length, LastPos i →
    ∃ t ∈ M.accept, t ∈ M.step (r i) (w.get i))

theorem runValuation_iff_exists_positionRun (M : NFA Sigma Q) (w : List Sigma) :
    (∃ V : Fin (Fintype.card Q) → Set (Fin w.length), RunValuation M w V) ↔
      ∃ r : Fin w.length → Q, PositionRun M w r := by
  classical
  constructor
  · rintro ⟨V, hpart, hinit, htrans, hfinal⟩
    let idx : Fin w.length → Fin (Fintype.card Q) :=
      fun i => Classical.choose (hpart i)
    let r : Fin w.length → Q := fun i => enum Q (idx i)
    have hidx (i : Fin w.length) : i ∈ V (idx i) :=
      Classical.choose_spec (hpart i) |>.1
    have huniq (i : Fin w.length) (q : Fin (Fintype.card Q)) (hq : i ∈ V q) :
        q = idx i :=
      Classical.choose_spec (hpart i) |>.2 q hq
    refine ⟨r, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨q, hq, hstart⟩ := hinit i hi
      have hqi := huniq i q hq
      simpa [r, hqi] using hstart
    · intro i j hij
      obtain ⟨q, s, a, hq, hs, ha, hstep⟩ := htrans i j hij
      have hqi := huniq i q hq
      have hsj := huniq j s hs
      rw [hqi, hsj] at hstep
      rw [ha]
      simpa [r] using hstep
    · intro i hi
      obtain ⟨q, a, hq, ha, t, ht, hstep⟩ := hfinal i hi
      have hqi := huniq i q hq
      refine ⟨t, ht, ?_⟩
      rw [ha]
      simpa [r, hqi] using hstep
  · rintro ⟨r, hinit, htrans, hfinal⟩
    let V : Fin (Fintype.card Q) → Set (Fin w.length) :=
      fun q => {i | enum Q q = r i}
    refine ⟨V, ?_, ?_, ?_, ?_⟩
    · intro i
      refine ⟨(enum Q).symm (r i), ?_, ?_⟩
      · simp [V]
      · intro q hq
        change enum Q q = r i at hq
        exact (enum Q).injective (by simpa using hq)
    · intro i hi
      refine ⟨(enum Q).symm (r i), by simp [V], ?_⟩
      simpa using hinit i hi
    · intro i j hij
      refine ⟨(enum Q).symm (r i), (enum Q).symm (r j),
        (enum Sigma).symm (w.get i), by simp [V], by simp [V], by simp, ?_⟩
      simpa using htrans i j hij
    · intro i hi
      obtain ⟨t, ht, hstep⟩ := hfinal i hi
      refine ⟨(enum Q).symm (r i), (enum Sigma).symm (w.get i),
        by simp [V], by simp, t, ht, ?_⟩
      simpa using hstep

theorem firstPos_iff_eq_zero {n : Nat} (i : Fin (n + 1)) :
    FirstPos i ↔ i = 0 := by
  constructor
  · intro h
    apply Fin.ext
    have hi := h 0
    exact Nat.eq_zero_of_le_zero hi
  · rintro rfl
    exact fun _ => Fin.zero_le _

theorem lastPos_iff_eq_last {n : Nat} (i : Fin (n + 1)) :
    LastPos i ↔ i = Fin.last n := by
  constructor
  · intro h
    apply le_antisymm (Fin.le_last i)
    exact h (Fin.last n)
  · rintro rfl
    exact Fin.le_last

theorem adjacent_iff_val_succ {n : Nat} (i j : Fin n) :
    Adjacent i j ↔ i.val + 1 = j.val := by
  constructor
  · rintro ⟨hij, hnone⟩
    have hle : i.val + 1 ≤ j.val := by omega
    apply Nat.le_antisymm hle
    by_contra h
    have hmid : i.val + 1 < j.val := by omega
    let z : Fin n := ⟨i.val + 1, lt_trans hmid j.isLt⟩
    exact hnone ⟨z, by change i.val < i.val + 1; omega, by simpa [z] using hmid⟩
  · intro h
    constructor
    · exact Fin.mk_lt_mk.mpr (by omega)
    · rintro ⟨z, hiz, hzj⟩
      have : i.val < z.val ∧ z.val < j.val := ⟨hiz, hzj⟩
      omega

theorem adjacent_zero_one {n : Nat} :
    Adjacent (0 : Fin (n + 2)) (1 : Fin (n + 2)) := by
  rw [adjacent_iff_val_succ]
  rfl

theorem adjacent_succ {n : Nat} (i j : Fin n) :
    Adjacent i j ↔ Adjacent i.succ j.succ := by
  simp only [adjacent_iff_val_succ, Fin.val_succ]
  constructor <;> omega

/-- The state occupied immediately before each letter along a nonempty NFA
path. -/
def pathBefore (M : NFA Sigma Q) :
    {s t : Q} → {w : List Sigma} → M.Path s t w → Fin w.length → Q
  | _, _, _, .nil _ => fun i => Fin.elim0 i
  | _, _, _, .cons next s _ _ _ _ p => Fin.cases s (pathBefore M p)

@[simp] theorem pathBefore_cons_zero {M : NFA Sigma Q} {s t next : Q}
    {a : Sigma} {w : List Sigma} (h : next ∈ M.step s a) (p : M.Path next t w) :
    pathBefore M (.cons next s t a w h p) 0 = s := rfl

@[simp] theorem pathBefore_cons_succ {M : NFA Sigma Q} {s t next : Q}
    {a : Sigma} {w : List Sigma} (h : next ∈ M.step s a) (p : M.Path next t w)
    (i : Fin w.length) :
    pathBefore M (.cons next s t a w h p) i.succ = pathBefore M p i := rfl

theorem pathBefore_transition {M : NFA Sigma Q} {s t : Q} {w : List Sigma}
    (p : M.Path s t w) (i j : Fin w.length) (hij : Adjacent i j) :
    pathBefore M p j ∈ M.step (pathBefore M p i) (w.get i) := by
  induction p with
  | nil s => exact Fin.elim0 i
  | cons next s t a x hstep p ih =>
      obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
      · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
        · exact False.elim (by
            have := (adjacent_iff_val_succ 0 0).mp hij
            simp at this)
        · have hj : j.val = 0 := by
            have := (adjacent_iff_val_succ 0 j.succ).mp hij
            change 1 = j.val + 1 at this
            omega
          cases p with
          | nil next => exact Fin.elim0 j
          | cons next' next t b x hnext p =>
              have hj0 : j = 0 := Fin.ext hj
              subst j
              simpa [pathBefore] using hstep
      · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
        · exact False.elim (by
            have := (adjacent_iff_val_succ i.succ 0).mp hij
            simp at this)
        · apply ih i j
          exact (adjacent_succ i j).mpr hij

theorem pathBefore_zero {M : NFA Sigma Q} {s t : Q} {a : Sigma} {w : List Sigma}
    (p : M.Path s t (a :: w)) : pathBefore M p 0 = s := by
  cases p
  rfl

theorem pathBefore_lastStep_aux {M : NFA Sigma Q} {s t : Q} {w : List Sigma}
    (p : M.Path s t w) :
    match w with
    | [] => True
    | a :: x =>
        t ∈ M.step (pathBefore M p (Fin.last x.length))
          ((a :: x).get (Fin.last x.length)) := by
  induction p with
  | nil => trivial
  | cons next s t a x hstep p ih =>
      cases x with
      | nil =>
          cases p with
          | nil => simpa [pathBefore] using hstep
      | cons b x => simpa [pathBefore] using ih

theorem pathBefore_lastStep {M : NFA Sigma Q} {s t : Q} {a : Sigma} {w : List Sigma}
    (p : M.Path s t (a :: w)) :
    t ∈ M.step (pathBefore M p (Fin.last w.length)) ((a :: w).get (Fin.last w.length)) := by
  exact pathBefore_lastStep_aux p

theorem positionRun_of_path {M : NFA Sigma Q} {s t : Q} {a : Sigma} {w : List Sigma}
    (hs : s ∈ M.start) (ht : t ∈ M.accept) (p : M.Path s t (a :: w)) :
    PositionRun M (a :: w) (pathBefore M p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hi0 := (firstPos_iff_eq_zero i).mp hi
    subst i
    simpa [pathBefore_zero p] using hs
  · intro i j hij
    exact pathBefore_transition p i j hij
  · intro i hi
    have hilast := (lastPos_iff_eq_last i).mp hi
    subst i
    exact ⟨t, ht, pathBefore_lastStep p⟩

theorem path_of_positionRun (M : NFA Sigma Q) (a : Sigma) (w : List Sigma)
    (r : Fin (a :: w).length → Q)
    (htrans : ∀ i j : Fin (a :: w).length, Adjacent i j →
      r j ∈ M.step (r i) ((a :: w).get i))
    (hfinal : ∀ i : Fin (a :: w).length, LastPos i →
      ∃ t ∈ M.accept, t ∈ M.step (r i) ((a :: w).get i)) :
    ∃ t ∈ M.accept, Nonempty (M.Path (r 0) t (a :: w)) := by
  induction w generalizing a with
  | nil =>
      obtain ⟨t, ht, hstep⟩ := hfinal 0 ((lastPos_iff_eq_last 0).mpr rfl)
      exact ⟨t, ht, ⟨NFA.Path.cons t (r 0) t a [] hstep (.nil t)⟩⟩
  | cons b w ih =>
      let r' : Fin (b :: w).length → Q := fun i => r i.succ
      have htrans' : ∀ i j : Fin (b :: w).length, Adjacent i j →
          r' j ∈ M.step (r' i) ((b :: w).get i) := by
        intro i j hij
        simpa [r'] using htrans i.succ j.succ ((adjacent_succ i j).mp hij)
      have hfinal' : ∀ i : Fin (b :: w).length, LastPos i →
          ∃ t ∈ M.accept, t ∈ M.step (r' i) ((b :: w).get i) := by
        intro i hi
        apply hfinal i.succ
        have hilast := (lastPos_iff_eq_last i).mp hi
        apply (lastPos_iff_eq_last i.succ).mpr
        subst i
        apply Fin.ext
        rfl
      obtain ⟨t, ht, ⟨p⟩⟩ := ih b r' htrans' hfinal'
      have hstep : r 1 ∈ M.step (r 0) a := by
        exact htrans 0 1 adjacent_zero_one
      refine ⟨t, ht, ⟨NFA.Path.cons (r 1) (r 0) t a (b :: w) hstep ?_⟩⟩
      simpa [r'] using p

theorem exists_positionRun_iff_accepts (M : NFA Sigma Q) (a : Sigma) (w : List Sigma) :
    (∃ r : Fin (a :: w).length → Q, PositionRun M (a :: w) r) ↔
      a :: w ∈ M.accepts := by
  constructor
  · rintro ⟨r, hinit, htrans, hfinal⟩
    obtain ⟨t, ht, hp⟩ := path_of_positionRun M a w r htrans hfinal
    apply NFA.accepts_iff_exists_path.mpr
    refine ⟨r 0, ?_, t, ht, hp⟩
    exact hinit 0 ((firstPos_iff_eq_zero 0).mpr rfl)
  · intro h
    obtain ⟨s, hs, t, ht, ⟨p⟩⟩ := NFA.accepts_iff_exists_path.mp h
    exact ⟨pathBefore M p, positionRun_of_path hs ht p⟩

theorem realize_nonemptyFormula (w : List Sigma) :
    WordModels w (nonemptyFormula (Sigma := Sigma)) ↔ w ≠ [] := by
  cases w with
  | nil => simp [WordModels, nonemptyFormula]
  | cons a w => simp [WordModels, nonemptyFormula]

theorem realize_emptyFormula (w : List Sigma) :
    WordModels w (emptyFormula (Sigma := Sigma)) ↔ w = [] := by
  change (¬WordModels w (nonemptyFormula (Sigma := Sigma))) ↔ w = []
  rw [realize_nonemptyFormula]
  exact not_ne_iff

theorem empty_mem_accepts (M : NFA Sigma Q) :
    [] ∈ M.accepts ↔ ∃ q ∈ M.start, q ∈ M.accept := by
  rw [NFA.accepts_iff_exists_path]
  constructor
  · rintro ⟨s, hs, t, ht, ⟨p⟩⟩
    cases p
    exact ⟨s, hs, ht⟩
  · rintro ⟨q, hq, hqa⟩
    exact ⟨q, hq, q, hqa, ⟨.nil q⟩⟩

theorem realize_closedRun (M : NFA Sigma Q) (w : List Sigma) :
    @MSOSemantics.Realize _ (Fin w.length) (wordStructure w) _ _
      (closeSO (Fintype.card Q) (runBody M))
      (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i) ↔
      ∃ V : Fin (Fintype.card Q) → Set (Fin w.length), RunValuation M w V := by
  rw [realize_closeSO]
  apply exists_congr
  intro V
  exact realize_runBody M w V

theorem runSentence_correct (M : NFA Sigma Q) (w : List Sigma) :
    WordModels w (runSentence M) ↔ w ∈ M.accepts := by
  cases w with
  | nil =>
      have he : @MSOSemantics.Realize _ (Fin [].length) (wordStructure []) _ _
          (emptyFormula (Sigma := Sigma))
          (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i) ↔
          ([] : List Sigma) = [] := realize_emptyFormula []
      have hn : @MSOSemantics.Realize _ (Fin [].length) (wordStructure []) _ _
          (nonemptyFormula (Sigma := Sigma))
          (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i) ↔
          ([] : List Sigma) ≠ [] := realize_nonemptyFormula []
      simp only [WordModels, runSentence, MSOSemantics.realize_or,
        MSOSemantics.realize_and, realize_holds, he, hn]
      simp only [ne_eq, eq_self, not_true_eq_false, false_and, or_false, and_true]
      exact (empty_mem_accepts M).symm
  | cons a w =>
      have he : @MSOSemantics.Realize _ (Fin (a :: w).length)
          (wordStructure (a :: w)) _ _ (emptyFormula (Sigma := Sigma))
          (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i) ↔
          a :: w = [] := realize_emptyFormula (a :: w)
      have hn : @MSOSemantics.Realize _ (Fin (a :: w).length)
          (wordStructure (a :: w)) _ _ (nonemptyFormula (Sigma := Sigma))
          (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i) ↔
          a :: w ≠ [] := realize_nonemptyFormula (a :: w)
      have hc := realize_closedRun M (a :: w)
      simp only [WordModels, runSentence, MSOSemantics.realize_or,
        MSOSemantics.realize_and, realize_holds, he, hn, hc,
        runValuation_iff_exists_positionRun]
      constructor
      · rintro (⟨_, hfalse⟩ | ⟨_, hr⟩)
        · exact False.elim (List.cons_ne_nil a w hfalse)
        · exact (exists_positionRun_iff_accepts M a w).mp hr
      · intro h
        exact Or.inr ⟨List.cons_ne_nil a w, (exists_positionRun_iff_accepts M a w).mpr h⟩

end RunFormula

open RunFormula

/--
---
conclusion: Lax52.NFAToMSO.nfa_definable_by_mso
---
-/
theorem nfa_definable_by_mso_proof {Sigma : Type u} [Fintype Sigma]
    {Q : Type} [Fintype Q] (M : NFA Sigma Q) :
    ∃ phi : MSOSyntax.Sentence (wordLanguage Sigma), M.accepts = sentenceLanguage phi := by
  refine ⟨runSentence M, ?_⟩
  ext w
  exact (runSentence_correct M w).symm

end Lax52Proofs
