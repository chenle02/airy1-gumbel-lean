/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.BlockExtremes
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Airy1Gumbel

/-!
# Assembly layer, part 1: measure toolkit, block geometry, per-core
Bonferroni bounds, and the eventual control of `D_{N,k}`

This file builds, on top of the `Airy1BlockExtremes` interface of
`Airy1Gumbel.BlockExtremes`, the measure-algebra ingredients of the paper's
blocking assembly (Section 5.2):

* **T0** (`MeasureToolkit`): finite union bound and the second-order
  Bonferroni lower bound for `P.real`, complement algebra;
* **T1** (`sum_Ico_pair_sub_eq_sum_Icc`): the separation-grouping identity
  `∑_{a ≤ i < j < b} g (j - i) = ∑_{r=1}^{b-a-1} (b - a - r) · g r`;
* **T2** (`coreBlock`): the core blocks of the blocking scheme, their
  cardinality and their pairwise `q_N`-separation;
* **T3** (`safe_coreBlock_bounds`): the per-core two-sided Bonferroni bounds
  on the safe event `Safe`;
* **T4** (`D_eventually_le`): the eventual bound
  `DD k N ≤ τ²/k + 1/k`, `τ = e^{-z}`, obtained from the four-piece split at
  `m_N` and `q_N` together with `tail_normalized` and the transferred
  `mixing_tail` (via `mixing_tail_of_bound` at the enlarged cut `A`).

The exceedance events are `Exc j u = {Y j > u}` and the per-core safe event is
`Safe s u = {∀ j ∈ s, Y j ≤ u} = (⋃ j ∈ s, Exc j u)ᶜ`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### T0: measure toolkit for `P.real` -/

section MeasureToolkit

omit [IsProbabilityMeasure P] in
lemma measureReal_nonneg (s : Set Ω) : 0 ≤ P.real s := ENNReal.toReal_nonneg

lemma measureReal_univ : P.real Set.univ = 1 := by
  simp [measureReal_def]

lemma measureReal_mono {s t : Set Ω} (h : s ⊆ t) : P.real s ≤ P.real t :=
  ENNReal.toReal_mono (measure_ne_top P t) (measure_mono h)

/-- Complement algebra: `P.real (sᶜ) = 1 - P.real s` for measurable `s`. -/
lemma measureReal_compl {s : Set Ω} (hs : MeasurableSet s) :
    P.real sᶜ = 1 - P.real s := by
  have h : P sᶜ = 1 - P s := by
    rw [measure_compl hs (measure_ne_top P s), measure_univ]
  have hle : P s ≤ 1 := by
    calc P s ≤ P Set.univ := measure_mono (Set.subset_univ s)
      _ = 1 := measure_univ
  rw [measureReal_def, h, ENNReal.toReal_sub_of_le hle (by simp)]
  simp [measureReal_def]

/-- Union = sum − intersection, in `P.real`. -/
lemma measureReal_union_add_inter (s t : Set Ω) (ht : MeasurableSet t) :
    P.real (s ∪ t) + P.real (s ∩ t) = P.real s + P.real t := by
  have h := measure_union_add_inter (μ := P) s ht
  simp only [measureReal_def]
  rw [← ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _), h,
    ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _)]

/-- Decomposition `X = (X ∩ Y) ∪ (X \ Y)` in `P.real`. -/
lemma measureReal_inter_add_sdiff (s t : Set Ω) (ht : MeasurableSet t) :
    P.real (s ∩ t) + P.real (s \ t) = P.real s := by
  have h := measure_inter_add_sdiff (μ := P) s ht
  simp only [measureReal_def]
  rw [← ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _), h]

/-- Finite union bound for `P.real` (no measurability needed). -/
lemma measureReal_biUnion_finset_le {ι : Type*} (s : Finset ι) (A : ι → Set Ω) :
    P.real (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, P.real (A i) := by
  have h := measure_biUnion_finset_le (μ := P) s A
  have hfin : (∑ i ∈ s, P (A i)) ≠ ⊤ := by
    simp only [ne_eq, ENNReal.sum_eq_top, not_exists, not_and]
    exact fun i _ => measure_ne_top P (A i)
  have h2 := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top P (A i))] at h2
  simpa only [measureReal_def] using h2

/-- `P.real (X ∩ Y) ≥ P.real X - P.real (Yᶜ)` for measurable `Y`. -/
lemma measureReal_inter_ge_sub_compl {X Y : Set Ω} (hY : MeasurableSet Y) :
    P.real X - P.real Yᶜ ≤ P.real (X ∩ Y) := by
  have h := measureReal_inter_add_sdiff (P := P) X Y hY
  have hsub : X \ Y ⊆ Yᶜ := by
    rw [Set.sdiff_eq]
    exact Set.inter_subset_right
  have h2 := measureReal_mono (P := P) hsub
  linarith

/-- `|P.real (X ∩ Y) - P.real X| ≤ P.real (Yᶜ)` for measurable `Y`. -/
lemma abs_measureReal_inter_sub_le_compl {X Y : Set Ω} (hY : MeasurableSet Y) :
    |P.real (X ∩ Y) - P.real X| ≤ P.real Yᶜ := by
  have h := measureReal_inter_add_sdiff (P := P) X Y hY
  have hsub : X \ Y ⊆ Yᶜ := by
    rw [Set.sdiff_eq]
    exact Set.inter_subset_right
  have h2 := measureReal_mono (P := P) hsub
  have hle : P.real (X ∩ Y) ≤ P.real X := measureReal_mono Set.inter_subset_left
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

end MeasureToolkit

/-! ### Finset union/insert and measurability -/

section FinsetBasics

omit [MeasurableSpace Ω] in
lemma biUnion_finset_insert {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (A : ι → Set Ω) : (⋃ i ∈ insert a s, A i) = A a ∪ ⋃ i ∈ s, A i := by
  ext ω
  rw [Set.mem_iUnion₂, Set.mem_union, Set.mem_iUnion₂]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Or.inl hx
    · exact Or.inr ⟨i, hi, hx⟩
  · rintro (hx | ⟨i, hi, hx⟩)
    · exact ⟨a, Finset.mem_insert_self _ _, hx⟩
    · exact ⟨i, Finset.mem_insert_of_mem hi, hx⟩

lemma measurableSet_biUnion_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (A : ι → Set Ω) (hA : ∀ j, MeasurableSet (A j)) :
    MeasurableSet (⋃ j ∈ s, A j) := by
  induction s using Finset.induction_on with
  | empty =>
    have h1 : (⋃ j ∈ (∅ : Finset ι), A j) = ∅ := by
      ext ω
      rw [Set.mem_iUnion₂]
      simp
    rw [h1]
    exact MeasurableSet.empty
  | @insert a s ha ih =>
    rw [biUnion_finset_insert]
    exact MeasurableSet.union (hA a) ih

/-- The pair-sum increment when inserting an element into the index finset:
the new pairs are exactly the `{a, x}` with `x ∈ s`. -/
lemma pair_sum_insert {ι : Type*} [DecidableEq ι] [LinearOrder ι] {a : ι}
    {s : Finset ι} (ha : a ∉ s) (f : ι → ι → ℝ) (hf : ∀ i j, f i j = f j i) :
    (∑ i ∈ insert a s, ∑ j ∈ (insert a s).filter (fun j => j < i), f i j) =
      (∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), f i j) + ∑ x ∈ s, f a x := by
  have hGa : (∑ j ∈ (insert a s).filter (fun j => j < a), f a j) =
      ∑ j ∈ s.filter (fun j => j < a), f a j := by
    rw [Finset.filter_insert, if_neg (lt_irrefl a)]
  have hGi : ∀ i ∈ s, (∑ j ∈ (insert a s).filter (fun j => j < i), f i j) =
      (∑ j ∈ s.filter (fun j => j < i), f i j) + (if a < i then f i a else 0) := by
    intro i hi
    have hnot : a ∉ s.filter (fun j => j < i) := fun h => ha (Finset.mem_filter.mp h).1
    rw [Finset.filter_insert]
    by_cases h : a < i
    · rw [if_pos h, Finset.sum_insert hnot, if_pos h, add_comm]
    · rw [if_neg h, if_neg h, add_zero]
  have h1 : (∑ i ∈ insert a s, ∑ j ∈ (insert a s).filter (fun j => j < i), f i j) =
      (∑ j ∈ (insert a s).filter (fun j => j < a), f a j) +
        ∑ i ∈ s, ∑ j ∈ (insert a s).filter (fun j => j < i), f i j :=
    Finset.sum_insert ha
  have h2 : (∑ i ∈ s, ∑ j ∈ (insert a s).filter (fun j => j < i), f i j) =
      (∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), f i j) +
        ∑ i ∈ s, (if a < i then f i a else 0) := by
    rw [Finset.sum_congr rfl hGi, Finset.sum_add_distrib]
  have h3 : (∑ i ∈ s, (if a < i then f i a else 0)) =
      ∑ i ∈ s.filter (fun i => a < i), f i a :=
    (Finset.sum_filter _ _).symm
  have hsymm : (∑ i ∈ s.filter (fun i => a < i), f i a) =
      ∑ i ∈ s.filter (fun i => a < i), f a i :=
    Finset.sum_congr rfl (fun i _ => hf i a)
  have hflt : s.filter (fun i => a < i) = s.filter (fun i => ¬ i < a) :=
    Finset.filter_congr (fun x hx => by
      have hxa : x ≠ a := fun h => ha (h ▸ hx)
      constructor
      · intro h
        exact not_lt.mpr (le_of_lt h)
      · intro h
        exact lt_of_le_of_ne (not_lt.mp h) (fun hax => hxa hax.symm))
  have hsplit : (∑ j ∈ s.filter (fun j => j < a), f a j) +
      (∑ i ∈ s.filter (fun i => a < i), f a i) = ∑ x ∈ s, f a x := by
    rw [hflt]
    exact Finset.sum_filter_add_sum_filter_not s (fun x => x < a) (f a)
  rw [h1, hGa, h2, h3, hsymm]
  linarith [hsplit]

/-- **T0-2, Bonferroni lower bound**: the sum of the singleton measures minus
the sum over pairs `{i, j}` with `j < i` of the intersection measures is a
lower bound for the measure of the union. -/
theorem sum_measureReal_sub_pair_le_biUnion {ι : Type*} [DecidableEq ι]
    [LinearOrder ι] (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) :
    (∑ i ∈ s, P.real (A i)) -
        ∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), P.real (A i ∩ A j) ≤
      P.real (⋃ i ∈ s, A i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.filter_empty, sub_zero]
    exact measureReal_nonneg _
  | @insert a s ha ih =>
    have hU : MeasurableSet (⋃ i ∈ s, A i) := measurableSet_biUnion_finset s A (fun i => hA i)
    have hunion := measureReal_union_add_inter (P := P) (A a) (⋃ i ∈ s, A i) hU
    have hcov : A a ∩ (⋃ i ∈ s, A i) = ⋃ i ∈ s, A a ∩ A i := Set.inter_iUnion₂ _ _
    have hcap : P.real (A a ∩ ⋃ i ∈ s, A i) ≤ ∑ i ∈ s, P.real (A a ∩ A i) := by
      rw [hcov]
      exact measureReal_biUnion_finset_le s (fun i => A a ∩ A i)
    have hpairs : (∑ i ∈ insert a s, ∑ j ∈ (insert a s).filter (fun j => j < i),
        P.real (A i ∩ A j)) =
        (∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), P.real (A i ∩ A j)) +
          ∑ x ∈ s, P.real (A a ∩ A x) :=
      pair_sum_insert ha (fun i j => P.real (A i ∩ A j)) (fun i j => by rw [Set.inter_comm])
    have hdisj : (⋃ i ∈ insert a s, A i) = A a ∪ ⋃ i ∈ s, A i := biUnion_finset_insert a s A
    rw [hdisj, Finset.sum_insert ha, hpairs]
    linarith [ih]

end FinsetBasics

/-! ### Block events -/

section Events

variable (D : Airy1BlockExtremes P)

/-- The exceedance event `Exc j u = {Y j > u}`. -/
def Exc (j : ℕ) (u : ℝ) : Set Ω := {ω | D.Y j ω > u}

/-- The core-safe event `Safe s u = {∀ j ∈ s, Y j ≤ u}`. -/
def Safe (s : Finset ℕ) (u : ℝ) : Set Ω := {ω | ∀ j ∈ s, D.Y j ω ≤ u}

lemma measurableExc (j : ℕ) (u : ℝ) : MeasurableSet (Exc D j u) :=
  D.Y_meas j measurableSet_Ioi

lemma Exc_inter (i j : ℕ) (u : ℝ) :
    Exc D i u ∩ Exc D j u = {ω | D.Y i ω > u ∧ D.Y j ω > u} := rfl

/-- The safe event is the complement of the union of exceedances. -/
lemma Safe_eq_compl_biUnion (s : Finset ℕ) (u : ℝ) :
    Safe D s u = (⋃ j ∈ s, Exc D j u)ᶜ := by
  ext ω
  constructor
  · intro h
    rw [Set.mem_compl_iff, Set.mem_iUnion₂]
    push Not
    intro j hj
    exact not_lt.mpr (h j hj)
  · intro h j hj
    rw [Set.mem_compl_iff, Set.mem_iUnion₂] at h
    push Not at h
    exact not_lt.mp (h j hj)

lemma measurableSafe (s : Finset ℕ) (u : ℝ) : MeasurableSet (Safe D s u) := by
  rw [Safe_eq_compl_biUnion]
  exact (measurableSet_biUnion_finset s (fun j => Exc D j u) (fun j => measurableExc D j u)).compl

/-- Stationarity of the one-block marginal, transferred to `P.real`. -/
lemma Exc_real_eq (u : ℝ) (j : ℕ) :
    P.real (Exc D j u) = P.real (Exc D 0 u) := by
  rw [measureReal_def, measureReal_def]
  change (P {ω | D.Y j ω > u}).toReal = (P {ω | D.Y 0 ω > u}).toReal
  rw [D.stat_marginal u j]

/-- Stationarity of the pair tail at distance `j - i`, transferred to
`P.real`. -/
lemma Exc_inter_real_eq (u : ℝ) (i j : ℕ) (hij : i ≤ j) :
    P.real (Exc D i u ∩ Exc D j u) = P.real (Exc D 0 u ∩ Exc D (j - i) u) := by
  rw [measureReal_def, measureReal_def, Exc_inter, Exc_inter]
  have hji : i + (j - i) = j := by omega
  have h := D.stat_pair u i (j - i)
  rw [hji] at h
  rw [h]

end Events

/-! ### T1: the separation-grouping identity -/

section GroupingIdentity

lemma Icc_eq_Ico_succ_right_nat (a b : ℕ) : Finset.Icc a b = Finset.Ico a (b + 1) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

lemma sum_Icc_eq_sum_range_nat (f : ℕ → ℝ) (a b : ℕ) :
    ∑ r ∈ Finset.Icc a b, f r = ∑ r ∈ Finset.range (b + 1 - a), f (a + r) := by
  rw [Icc_eq_Ico_succ_right_nat]
  exact Finset.sum_Ico_eq_sum_range f a (b + 1)

/-- The triangular double sum over `Finset.range`, by induction on `ℓ`:
both sides satisfy the recursion `F (ℓ+1) = F ℓ + ∑_{i < ℓ} g i`. -/
theorem sum_range_triangle (g : ℕ → ℝ) (ℓ : ℕ) :
    (∑ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range (ℓ - 1 - i), g j) =
      ∑ r ∈ Finset.range (ℓ - 1), ((ℓ - 1 - r : ℕ) : ℝ) * g r := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
    · subst hℓ
      simp
    · have hL : (∑ i ∈ Finset.range (ℓ + 1), ∑ j ∈ Finset.range (ℓ + 1 - 1 - i), g j) =
          (∑ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range (ℓ - 1 - i), g j) +
            ∑ i ∈ Finset.range ℓ, g i := by
        have hlast : (∑ j ∈ Finset.range (ℓ + 1 - 1 - ℓ), g j) = 0 := by
          have h0 : ℓ + 1 - 1 - ℓ = 0 := by omega
          rw [h0]
          simp
        have hsplit : (∑ i ∈ Finset.range (ℓ + 1), ∑ j ∈ Finset.range (ℓ + 1 - 1 - i), g j) =
            (∑ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range (ℓ + 1 - 1 - i), g j) +
              (∑ j ∈ Finset.range (ℓ + 1 - 1 - ℓ), g j) :=
          Finset.sum_range_succ _ ℓ
        rw [hsplit, hlast, add_zero]
        have hF : ∀ i ∈ Finset.range ℓ,
            (∑ j ∈ Finset.range (ℓ + 1 - 1 - i), g j) =
              (∑ j ∈ Finset.range (ℓ - 1 - i), g j) + g (ℓ - 1 - i) := by
          intro i hi
          have hi' : i < ℓ := Finset.mem_range.mp hi
          have h1 : ℓ + 1 - 1 - i = (ℓ - 1 - i) + 1 := by omega
          rw [h1]
          exact Finset.sum_range_succ _ _
        have hsum : (∑ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range (ℓ + 1 - 1 - i), g j) =
            (∑ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range (ℓ - 1 - i), g j) +
              ∑ i ∈ Finset.range ℓ, g (ℓ - 1 - i) := by
          rw [Finset.sum_congr rfl hF, Finset.sum_add_distrib]
        rw [hsum]
        congr 1
        exact Finset.sum_range_reflect g ℓ
      have hR : (∑ r ∈ Finset.range (ℓ + 1 - 1), ((ℓ + 1 - 1 - r : ℕ) : ℝ) * g r) =
          (∑ r ∈ Finset.range (ℓ - 1), ((ℓ - 1 - r : ℕ) : ℝ) * g r) +
            ∑ i ∈ Finset.range ℓ, g i := by
        have h1 : ℓ + 1 - 1 = ℓ := by omega
        rw [h1]
        have h6 : Finset.range ℓ = Finset.range ((ℓ - 1) + 1) := by
          congr 1
          omega
        have h5 : (∑ r ∈ Finset.range ℓ, ((ℓ - r : ℕ) : ℝ) * g r) =
            (∑ r ∈ Finset.range (ℓ - 1), ((ℓ - r : ℕ) : ℝ) * g r) +
              ((ℓ - (ℓ - 1) : ℕ) : ℝ) * g (ℓ - 1) := by
          rw [h6]
          exact Finset.sum_range_succ _ _
        have hterm : ∀ r ∈ Finset.range (ℓ - 1),
            ((ℓ - r : ℕ) : ℝ) * g r = ((ℓ - 1 - r : ℕ) : ℝ) * g r + g r := by
          intro r hr
          have hr' : r < ℓ - 1 := Finset.mem_range.mp hr
          have h2 : ℓ - r = (ℓ - 1 - r) + 1 := by omega
          rw [h2]
          push_cast
          ring
        have hsum2 : (∑ r ∈ Finset.range (ℓ - 1), ((ℓ - r : ℕ) : ℝ) * g r) =
            (∑ r ∈ Finset.range (ℓ - 1), ((ℓ - 1 - r : ℕ) : ℝ) * g r) +
              ∑ r ∈ Finset.range (ℓ - 1), g r := by
          rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
        have h3 : ((ℓ - (ℓ - 1) : ℕ) : ℝ) * g (ℓ - 1) = g (ℓ - 1) := by
          have h4 : ℓ - (ℓ - 1) = 1 := by omega
          rw [h4]
          simp
        have h7 : (∑ i ∈ Finset.range ℓ, g i) =
            (∑ i ∈ Finset.range (ℓ - 1), g i) + g (ℓ - 1) := by
          rw [h6]
          exact Finset.sum_range_succ _ _
        rw [h5, hsum2, h3, h7]
        ring
      rw [hL, hR]
      linarith [ih]

/-- **T1, the separation-grouping identity**: reindexing the double sum over
`a ≤ i < j < b` by the gap `r = j - i`; for fixed `r` there are exactly
`b - a - r` pairs. -/
theorem sum_Ico_pair_sub_eq_sum_Icc (a b : ℕ) (g : ℕ → ℝ) :
    ∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico (i + 1) b, g (j - i) =
      ∑ r ∈ Finset.Icc 1 (b - a - 1), ((b - a - r : ℕ) : ℝ) * g r := by
  have hinner : ∀ i ∈ Finset.range (b - a),
      (∑ j ∈ Finset.Ico (a + i + 1) b, g (j - (a + i))) =
        ∑ j ∈ Finset.range (b - a - 1 - i), g (j + 1) := by
    intro i hi
    have hi' : i < b - a := Finset.mem_range.mp hi
    rw [Finset.sum_Ico_eq_sum_range]
    have h1 : b - (a + i + 1) = b - a - 1 - i := by omega
    rw [h1]
    apply Finset.sum_congr rfl
    intro j _
    show g (a + i + 1 + j - (a + i)) = g (j + 1)
    have h2 : a + i + 1 + j - (a + i) = j + 1 := by omega
    rw [h2]
  have hL : (∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico (i + 1) b, g (j - i)) =
      ∑ i ∈ Finset.range (b - a), ∑ j ∈ Finset.range (b - a - 1 - i), g (j + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    show (∑ j ∈ Finset.Ico (a + i + 1) b, g (j - (a + i))) = _
    exact hinner i hi
  have hR : (∑ r ∈ Finset.Icc 1 (b - a - 1), ((b - a - r : ℕ) : ℝ) * g r) =
      ∑ r ∈ Finset.range (b - a - 1), ((b - a - 1 - r : ℕ) : ℝ) * g (r + 1) := by
    rw [sum_Icc_eq_sum_range_nat]
    have h3 : b - a - 1 + 1 - 1 = b - a - 1 := by omega
    rw [h3]
    apply Finset.sum_congr rfl
    intro r _
    show ((b - a - (1 + r) : ℕ) : ℝ) * g (1 + r) = _
    have h4 : b - a - (1 + r) = b - a - 1 - r := by omega
    rw [h4, add_comm (1 : ℕ) r]
  rw [hL, hR]
  exact sum_range_triangle (fun j => g (j + 1)) (b - a)

end GroupingIdentity

/-! ### T2: block geometry -/

section BlockGeometry

/-- The `m`-th core block: the `m`-th block of size `N / k` with the
`q_N`-buffer deleted from its right end. -/
noncomputable def coreBlock (A : ℝ) (k N m : ℕ) : Finset ℕ :=
  Finset.Ico (m * (N / k)) ((m + 1) * (N / k) - qN A N)

/-- Every core-block index lies below `N`. -/
theorem coreBlock_subset_range {A : ℝ} {k N : ℕ} {m : ℕ} (hm : m ∈ Finset.range k)
    {j : ℕ} (hj : j ∈ coreBlock A k N m) : j < N := by
  rw [Finset.mem_range] at hm
  simp only [coreBlock, Finset.mem_Ico] at hj
  obtain ⟨hlo, hhi⟩ := hj
  have h1 : (m + 1) * (N / k) ≤ k * (N / k) :=
    Nat.mul_le_mul_right (N / k) (show m + 1 ≤ k by omega)
  have h2 : k * (N / k) ≤ N := Nat.mul_div_le N k
  have h3 : (m + 1) * (N / k) - qN A N ≤ (m + 1) * (N / k) := Nat.sub_le _ _
  omega

/-- The core block has exactly `N / k - qN A N` indices. -/
theorem coreBlock_card {A : ℝ} {k N m : ℕ} (hq : qN A N ≤ N / k) :
    (coreBlock A k N m).card = N / k - qN A N := by
  simp only [coreBlock, Nat.card_Ico]
  have h : (m + 1) * (N / k) = m * (N / k) + N / k := by ring
  omega

/-- Distinct cores are separated by the `q_N`-buffer. -/
theorem coreBlock_separated {A : ℝ} {k N : ℕ} {m₁ m₂ : ℕ} (hm : m₁ < m₂)
    {s t : ℕ} (hs : s ∈ coreBlock A k N m₁) (ht : t ∈ coreBlock A k N m₂) :
    s + qN A N ≤ t := by
  simp only [coreBlock, Finset.mem_Ico] at hs ht
  obtain ⟨h1, h2⟩ := hs
  obtain ⟨h3, h4⟩ := ht
  have hd : (m₁ + 1) * (N / k) ≤ m₂ * (N / k) :=
    Nat.mul_le_mul_right (N / k) (show m₁ + 1 ≤ m₂ by omega)
  omega

end BlockGeometry

/-! ### T3: per-core Bonferroni bounds -/

section CoreBounds

/-- Two-sided Bonferroni bound for the safe event over an index interval
`Ico lo hi`, in terms of the one-block tail `P.real (Exc 0 u)` and the pair
tails `P.real (Exc 0 u ∩ Exc r u)`. -/
theorem safe_Ico_bounds (D : Airy1BlockExtremes P) (lo hi : ℕ) (u : ℝ) :
    1 - ((hi - lo : ℕ) : ℝ) * P.real (Exc D 0 u) ≤ P.real (Safe D (Finset.Ico lo hi) u) ∧
      P.real (Safe D (Finset.Ico lo hi) u) ≤
        1 - ((hi - lo : ℕ) : ℝ) * P.real (Exc D 0 u) +
          ((hi - lo : ℕ) : ℝ) *
            ∑ r ∈ Finset.Icc 1 (hi - lo), P.real (Exc D 0 u ∩ Exc D r u) := by
  have hmeasU : MeasurableSet (⋃ j ∈ Finset.Ico lo hi, Exc D j u) :=
    measurableSet_biUnion_finset _ _ (fun j => measurableExc D j u)
  have hSafe : P.real (Safe D (Finset.Ico lo hi) u) =
      1 - P.real (⋃ j ∈ Finset.Ico lo hi, Exc D j u) := by
    rw [Safe_eq_compl_biUnion, measureReal_compl hmeasU]
  have hsum1 : (∑ j ∈ Finset.Ico lo hi, P.real (Exc D j u)) =
      ((hi - lo : ℕ) : ℝ) * P.real (Exc D 0 u) := by
    have h1 : (∑ j ∈ Finset.Ico lo hi, P.real (Exc D j u)) =
        ∑ j ∈ Finset.Ico lo hi, P.real (Exc D 0 u) :=
      Finset.sum_congr rfl (fun j _ => Exc_real_eq D u j)
    rw [h1, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hflt : ∀ i ∈ Finset.Ico lo hi,
      (Finset.Ico lo hi).filter (fun j => j < i) = Finset.Ico lo i := by
    intro i hi'
    rw [Finset.mem_Ico] at hi'
    rw [Finset.Ico_filter_lt, min_eq_right (by omega : i ≤ hi)]
  have hcomm : (∑ i ∈ Finset.Ico lo hi, ∑ j ∈ Finset.Ico (i + 1) hi,
        P.real (Exc D j u ∩ Exc D i u)) =
      ∑ j ∈ Finset.Ico lo hi, ∑ i ∈ Finset.Ico lo j, P.real (Exc D j u ∩ Exc D i u) :=
    Finset.sum_Ico_Ico_comm' lo hi (fun i j => P.real (Exc D j u ∩ Exc D i u))
  have hterm : (∑ i ∈ Finset.Ico lo hi, ∑ j ∈ Finset.Ico (i + 1) hi,
        P.real (Exc D i u ∩ Exc D j u)) =
      ∑ i ∈ Finset.Ico lo hi, ∑ j ∈ Finset.Ico (i + 1) hi,
        P.real (Exc D 0 u ∩ Exc D (j - i) u) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact Exc_inter_real_eq D u i j (by omega)
  have hpair : (∑ i ∈ Finset.Ico lo hi, ∑ j ∈ (Finset.Ico lo hi).filter (fun j => j < i),
        P.real (Exc D i u ∩ Exc D j u)) ≤
      ((hi - lo : ℕ) : ℝ) *
        ∑ r ∈ Finset.Icc 1 (hi - lo), P.real (Exc D 0 u ∩ Exc D r u) := by
    have hp1 : (∑ i ∈ Finset.Ico lo hi, ∑ j ∈ (Finset.Ico lo hi).filter (fun j => j < i),
          P.real (Exc D i u ∩ Exc D j u)) =
        ∑ i ∈ Finset.Ico lo hi, ∑ j ∈ Finset.Ico lo i, P.real (Exc D i u ∩ Exc D j u) := by
      apply Finset.sum_congr rfl
      intro i hi'
      rw [hflt i hi']
    have hp2 : (∑ i ∈ Finset.Ico lo hi, ∑ j ∈ Finset.Ico lo i,
          P.real (Exc D i u ∩ Exc D j u)) =
        ∑ i ∈ Finset.Ico lo hi, ∑ j ∈ Finset.Ico (i + 1) hi,
          P.real (Exc D i u ∩ Exc D j u) := by
      rw [← hcomm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Set.inter_comm]
    have hp3 : (∑ i ∈ Finset.Ico lo hi, ∑ j ∈ Finset.Ico (i + 1) hi,
          P.real (Exc D i u ∩ Exc D j u)) =
        ∑ r ∈ Finset.Icc 1 (hi - lo - 1),
          ((hi - lo - r : ℕ) : ℝ) * P.real (Exc D 0 u ∩ Exc D r u) := by
      rw [hterm]
      exact sum_Ico_pair_sub_eq_sum_Icc lo hi (fun r => P.real (Exc D 0 u ∩ Exc D r u))
    have hnn : ∀ r : ℕ, 0 ≤ P.real (Exc D 0 u ∩ Exc D r u) := fun r => measureReal_nonneg _
    calc (∑ i ∈ Finset.Ico lo hi, ∑ j ∈ (Finset.Ico lo hi).filter (fun j => j < i),
            P.real (Exc D i u ∩ Exc D j u))
        = ∑ r ∈ Finset.Icc 1 (hi - lo - 1),
            ((hi - lo - r : ℕ) : ℝ) * P.real (Exc D 0 u ∩ Exc D r u) := by
          rw [hp1, hp2, hp3]
      _ ≤ ∑ r ∈ Finset.Icc 1 (hi - lo - 1),
            ((hi - lo : ℕ) : ℝ) * P.real (Exc D 0 u ∩ Exc D r u) := by
          apply Finset.sum_le_sum
          intro r _
          apply mul_le_mul_of_nonneg_right _ (hnn r)
          exact_mod_cast Nat.sub_le (hi - lo) r
      _ = ((hi - lo : ℕ) : ℝ) *
            ∑ r ∈ Finset.Icc 1 (hi - lo - 1), P.real (Exc D 0 u ∩ Exc D r u) := by
          rw [Finset.mul_sum]
      _ ≤ ((hi - lo : ℕ) : ℝ) *
            ∑ r ∈ Finset.Icc 1 (hi - lo), P.real (Exc D 0 u ∩ Exc D r u) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Icc_subset_Icc_right (Nat.sub_le _ _)
          · intro r _ _
            exact hnn r
  have hbonf : (∑ i ∈ Finset.Ico lo hi, P.real (Exc D i u)) -
        ∑ i ∈ Finset.Ico lo hi, ∑ j ∈ (Finset.Ico lo hi).filter (fun j => j < i),
          P.real (Exc D i u ∩ Exc D j u) ≤
      P.real (⋃ i ∈ Finset.Ico lo hi, Exc D i u) :=
    sum_measureReal_sub_pair_le_biUnion (Finset.Ico lo hi) (fun j => Exc D j u)
      (fun j => measurableExc D j u)
  rw [hsum1] at hbonf
  constructor
  · rw [hSafe]
    have hUle : P.real (⋃ j ∈ Finset.Ico lo hi, Exc D j u) ≤
        ((hi - lo : ℕ) : ℝ) * P.real (Exc D 0 u) := by
      have h := measureReal_biUnion_finset_le (P := P) (Finset.Ico lo hi) (fun j => Exc D j u)
      rw [hsum1] at h
      exact h
    linarith
  · rw [hSafe]
    linarith [hpair]

/-- **T3, per-core Bonferroni bounds**: with `p = P.real (Exc 0 u)` and
`ℓ = N / k - qN A N` the cardinality of each core block,
`1 - ℓ p ≤ P (Safe) ≤ 1 - ℓ p + ℓ ∑_{r=1}^{N/k} P (Exc 0 ∩ Exc r)`. -/
theorem safe_coreBlock_bounds (D : Airy1BlockExtremes P) {A : ℝ} {k N m : ℕ}
    (hq : qN A N ≤ N / k) (u : ℝ) :
    1 - ((N / k - qN A N : ℕ) : ℝ) * P.real (Exc D 0 u) ≤
      P.real (Safe D (coreBlock A k N m) u) ∧
      P.real (Safe D (coreBlock A k N m) u) ≤
        1 - ((N / k - qN A N : ℕ) : ℝ) * P.real (Exc D 0 u) +
          ((N / k - qN A N : ℕ) : ℝ) *
            ∑ r ∈ Finset.Icc 1 (N / k), P.real (Exc D 0 u ∩ Exc D r u) := by
  have hhi : (m + 1) * (N / k) - qN A N - m * (N / k) = N / k - qN A N := by
    have h : (m + 1) * (N / k) = m * (N / k) + N / k := by ring
    omega
  have hcb : coreBlock A k N m = Finset.Ico (m * (N / k)) ((m + 1) * (N / k) - qN A N) := rfl
  rw [hcb]
  have h := safe_Ico_bounds D (m * (N / k)) ((m + 1) * (N / k) - qN A N) u
  rw [hhi] at h
  have hnonneg : ∀ r : ℕ, 0 ≤ P.real (Exc D 0 u ∩ Exc D r u) := fun r => measureReal_nonneg _
  have hext : (∑ r ∈ Finset.Icc 1 (N / k - qN A N), P.real (Exc D 0 u ∩ Exc D r u)) ≤
      ∑ r ∈ Finset.Icc 1 (N / k), P.real (Exc D 0 u ∩ Exc D r u) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc_right (Nat.sub_le _ _)
    · intro r _ _
      exact hnonneg r
  have hℓnn : (0 : ℝ) ≤ ((N / k - qN A N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hext hℓnn
  constructor
  · exact h.1
  · have h2 := h.2
    linarith

end CoreBounds

/-! ### T4: the `D_{N,k}` quantity and its eventual control -/

section DQuantity

variable (D : Airy1BlockExtremes P)

/-- The one-block exceedance probability along the Gumbel normalization. -/
noncomputable def oneTail (z : ℝ) (N : ℕ) : ℝ :=
  P.real (Exc D 0 (gumbelU N z))

/-- The pair exceedance probability at distance `r` along the normalization. -/
noncomputable def pairTail (z : ℝ) (N r : ℕ) : ℝ :=
  P.real (Exc D 0 (gumbelU N z) ∩ Exc D r (gumbelU N z))

lemma oneTail_eq (z : ℝ) (N : ℕ) :
    oneTail D z N = P.real {ω | D.Y 0 ω > gumbelU N z} := rfl

lemma pairTail_eq (z : ℝ) (N r : ℕ) :
    pairTail D z N r = P.real {ω | D.Y 0 ω > gumbelU N z ∧ D.Y r ω > gumbelU N z} := rfl

/-- The `D_{N,k}` quantity of the paper: `N` times the sum of the pair
exceedance probabilities over distances `1 ≤ r ≤ N / k`. -/
noncomputable def DD (z : ℝ) (k N : ℕ) : ℝ :=
  (N : ℝ) * ∑ r ∈ Finset.Icc 1 (N / k), pairTail D z N r

/-- Shifts of the mixing coefficients are summable: dominated by the
super-geometric elementary bound `alpha m ≤ C e^{-c(m-1)³}`. -/
lemma summable_alpha_add (c : ℕ) : Summable fun j : ℕ => D.alpha (c + j) := by
  have hc := D.mixc_pos
  have hC := D.mixC_pos
  have hgeo : Summable fun j : ℕ => (Real.exp (-D.mixc)) ^ j :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc))
  have hshift : Summable fun j : ℕ =>
      D.mixC * Real.exp (-D.mixc * (((j + 1 : ℕ) : ℝ) - 1) ^ 3) := by
    apply Summable.of_nonneg_of_le (fun j => mul_nonneg hC.le (Real.exp_pos _).le) _
      (hgeo.mul_left D.mixC)
    intro j
    have hexp : (Real.exp (-D.mixc)) ^ j = Real.exp (-D.mixc * (j : ℝ)) := by
      have hmul : (j : ℝ) * (-D.mixc) = -D.mixc * (j : ℝ) := by ring
      rw [← hmul, Real.exp_nat_mul]
    rw [hexp]
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    have hje : (((j + 1 : ℕ) : ℝ) - 1) = (j : ℝ) := by push_cast; ring
    have hj3 : (j : ℝ) ≤ (j : ℝ) ^ 3 := by
      by_cases hj : j = 0
      · subst hj
        norm_num
      · have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
        have h2 : (j : ℝ) ^ 1 ≤ (j : ℝ) ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
        rwa [pow_one] at h2
    rw [hje]
    exact mul_le_mul_of_nonpos_left hj3 (neg_nonpos.mpr hc.le)
  have halpha : Summable fun m : ℕ => D.mixC * Real.exp (-D.mixc * ((m : ℝ) - 1) ^ 3) :=
    (summable_nat_add_iff 1).mp hshift
  have halpha' : Summable fun m : ℕ => D.alpha m :=
    Summable.of_nonneg_of_le D.alpha_nonneg D.alpha_bound halpha
  have h := (summable_nat_add_iff c).mpr halpha'
  simpa [add_comm] using h

/-- `(log N)^{1/3} / N → 0`, by squeezing against `N^{-1/2}`. -/
lemma tendsto_L13_div_N :
    Tendsto (fun N : ℕ => (Real.log N) ^ ((1 : ℝ) / 3) / (N : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (f := fun N : ℕ => (Real.log N) ^ ((1 : ℝ) / 3) / (N : ℝ))
    (g := fun N : ℕ => ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_nonneg
      (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
    have hlog : Real.log (N : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 2) := by
      calc Real.log (N : ℝ) ≤ (N : ℝ) - 1 := Real.log_le_sub_one_of_pos hN0
        _ ≤ (N : ℝ) := by linarith
        _ = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    have h13 : (Real.log N) ^ ((1 : ℝ) / 3) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
      calc (Real.log N) ^ ((1 : ℝ) / 3)
          ≤ ((N : ℝ) ^ ((3 : ℝ) / 2)) ^ ((1 : ℝ) / 3) :=
            Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast hN)) hlog (by norm_num)
        _ = (N : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ (N : ℝ))]
            norm_num
    have hpow : (N : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ) = ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
      have h1 : (N : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ) = (N : ℝ) ^ (((1 : ℝ) / 2) - 1) := by
        rw [Real.rpow_sub hN0, Real.rpow_one]
      rw [h1, show ((1 : ℝ) / 2) - 1 = -((1 : ℝ) / 2) by norm_num]
      exact Real.rpow_neg (by linarith) _
    calc (Real.log N) ^ ((1 : ℝ) / 3) / (N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ) := by
          gcongr
      _ = ((N : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := hpow
  · have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2)) atTop atTop := by
      have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop
      simpa [Function.comp_def] using h
    have h2 := tendsto_inv_atTop_zero.comp h1
    simpa [Function.comp_def] using h2

/-- Eventually the polylogarithmic block length plus any fixed constant fits
into one block `N / k` (for fixed `k ≥ 1`). -/
lemma eventually_qN_add_le_div {A : ℝ} (hA : 0 < A) {k : ℕ} (hk : 1 ≤ k) (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, qN A N + C ≤ N / k := by
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsum : Tendsto (fun N : ℕ => A * (k : ℝ) * ((Real.log N) ^ ((1 : ℝ) / 3) / N) +
      ((C : ℝ) + 2) * (k : ℝ) / N) atTop (𝓝 0) := by
    have h1 := tendsto_L13_div_N.const_mul (A * (k : ℝ))
    have h2 := tendsto_const_div_atTop_nhds_zero_nat (((C : ℝ) + 2) * (k : ℝ))
    have h := h1.add h2
    simpa [mul_zero, add_zero] using h
  have hconv : (fun N : ℕ => A * (k : ℝ) * ((Real.log N) ^ ((1 : ℝ) / 3) / N) +
      ((C : ℝ) + 2) * (k : ℝ) / N) =ᶠ[atTop]
      (fun N : ℕ => (A * (Real.log N) ^ ((1 : ℝ) / 3) + ((C : ℝ) + 2)) / ((N : ℝ) / k)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    field_simp [hN0.ne', hkr.ne']
  have h0 := Tendsto.congr' hconv hsum
  have hlt := (Metric.tendsto_nhds.mp h0) 1 one_pos
  have hmain : ∀ᶠ N : ℕ in atTop,
      A * (Real.log N) ^ ((1 : ℝ) / 3) + ((C : ℝ) + 2) ≤ (N : ℝ) / k := by
    filter_upwards [hlt, eventually_ge_atTop 1] with N hN hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    rw [Real.dist_eq, sub_zero] at hN
    have hden : (0 : ℝ) < (N : ℝ) / k := div_pos hN0 hkr
    have hlt1 : (A * (Real.log N) ^ ((1 : ℝ) / 3) + ((C : ℝ) + 2)) / ((N : ℝ) / k) < 1 :=
      lt_of_le_of_lt (le_abs_self _) hN
    rw [div_lt_one hden] at hlt1
    linarith
  filter_upwards [hmain, eventually_ge_atTop 1] with N hN hN1
  have hceil : (qN A N : ℝ) < A * (Real.log N) ^ ((1 : ℝ) / 3) + 1 :=
    Nat.ceil_lt_add_one
      (mul_nonneg hA.le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN1)) _))
  have hdiv : (N : ℝ) / k < ((N / k : ℕ) : ℝ) + 1 := by
    have h1 := Nat.div_add_mod N k
    have h2 : N % k < k := Nat.mod_lt N (by omega)
    have h3 : (N : ℝ) < (k : ℝ) * ((N / k : ℕ) : ℝ) + (k : ℝ) := by
      have h4 : (k : ℝ) * ((N / k : ℕ) : ℝ) + ((N % k : ℕ) : ℝ) = (N : ℝ) := by
        exact_mod_cast h1
      have h5 : ((N % k : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast h2
      linarith
    rw [div_lt_iff₀ hkr]
    have h6 : (((N / k : ℕ) : ℝ) + 1) * (k : ℝ) = (k : ℝ) * ((N / k : ℕ) : ℝ) + (k : ℝ) := by
      ring
    rw [h6]
    exact h3
  have hfin : (qN A N : ℝ) + (C : ℝ) < ((N / k : ℕ) : ℝ) := by linarith
  have hlt' : qN A N + C < N / k := by exact_mod_cast hfin
  omega

/-- Eventually the mesoscopic boundary `m_N = ⌊χ √(2 u_N(z))⌋` lies below the
polylogarithmic cut `q_N = ⌈A (log N)^{1/3}⌉` when `χ ≤ 1` and
`A ≥ √(6γ)`. -/
lemma mN_le_qN_eventually (χ : ℝ) (z : ℝ) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) {A : ℝ}
    (hA : Real.sqrt (6 * airyGamma) ≤ A) :
    ∀ᶠ N : ℕ in atTop, mN χ z N ≤ qN A N := by
  have hδt := tendsto_deltaN z
  have hδ : ∀ᶠ N : ℕ in atTop, |deltaN z N| ≤ 1 / 2 := by
    have h := (Metric.tendsto_nhds.mp hδt) (1 / 2) (by norm_num)
    filter_upwards [h] with N hN
    rw [Real.dist_eq, sub_zero] at hN
    exact hN.le
  filter_upwards [eventually_ge_atTop 2, epsN_eventually_le, hδ] with N hN hε hδN
  have hL0 : (0 : ℝ) < Real.log N := log_nat_pos hN
  have hL13 : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hL0.le _
  have hu : 2 * gumbelU N z ≤ 6 * airyGamma * (Real.log N) ^ ((2 : ℝ) / 3) := by
    rw [gumbelU_eq hN hε, gumbelA_eq hN]
    have h1δ : 1 + deltaN z N ≤ 3 / 2 := by linarith [(abs_le.mp hδN).2]
    have h1ε : 1 + epsN N ≤ 3 / 2 := by linarith [(abs_le.mp hε).2]
    have h1δlo : (0 : ℝ) ≤ 1 + deltaN z N := by linarith [(abs_le.mp hδN).1]
    have hbase : (0 : ℝ) ≤ airyGamma * (Real.log N) ^ ((2 : ℝ) / 3) :=
      mul_nonneg airyGamma_pos.le (Real.rpow_nonneg hL0.le _)
    have hstep1 : airyGamma * (Real.log N) ^ ((2 : ℝ) / 3) * (1 + epsN N) * (1 + deltaN z N) ≤
        airyGamma * (Real.log N) ^ ((2 : ℝ) / 3) * (3 / 2) * (1 + deltaN z N) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1ε hbase) h1δlo
    have hstep2 : airyGamma * (Real.log N) ^ ((2 : ℝ) / 3) * (3 / 2) * (1 + deltaN z N) ≤
        airyGamma * (Real.log N) ^ ((2 : ℝ) / 3) * (3 / 2) * (3 / 2) :=
      mul_le_mul_of_nonneg_left h1δ (mul_nonneg hbase (by norm_num))
    linarith [hstep1, hstep2]
  have hsqrt : Real.sqrt (2 * gumbelU N z) ≤
      Real.sqrt (6 * airyGamma) * (Real.log N) ^ ((1 : ℝ) / 3) := by
    calc Real.sqrt (2 * gumbelU N z) ≤ Real.sqrt (6 * airyGamma * (Real.log N) ^ ((2 : ℝ) / 3)) :=
          Real.sqrt_le_sqrt hu
      _ = Real.sqrt (6 * airyGamma) * Real.sqrt ((Real.log N) ^ ((2 : ℝ) / 3)) :=
          Real.sqrt_mul (mul_nonneg (by norm_num) airyGamma_pos.le) _
      _ = Real.sqrt (6 * airyGamma) * (Real.log N) ^ ((1 : ℝ) / 3) := by
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le,
            show (2 : ℝ) / 3 * (1 / 2) = 1 / 3 by norm_num]
  have hchain : (mN χ z N : ℝ) ≤ A * (Real.log N) ^ ((1 : ℝ) / 3) := by
    calc (mN χ z N : ℝ) ≤ χ * Real.sqrt (2 * gumbelU N z) :=
          Nat.floor_le (mul_nonneg hχ0 (Real.sqrt_nonneg _))
      _ ≤ χ * (Real.sqrt (6 * airyGamma) * (Real.log N) ^ ((1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left hsqrt hχ0
      _ ≤ 1 * (Real.sqrt (6 * airyGamma) * (Real.log N) ^ ((1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_right hχ1 (mul_nonneg (Real.sqrt_nonneg _) hL13)
      _ = Real.sqrt (6 * airyGamma) * (Real.log N) ^ ((1 : ℝ) / 3) := one_mul _
      _ ≤ A * (Real.log N) ^ ((1 : ℝ) / 3) := mul_le_mul_of_nonneg_right hA hL13
  have hq : A * (Real.log N) ^ ((1 : ℝ) / 3) ≤ (qN A N : ℝ) := Nat.le_ceil _
  have hfin : (mN χ z N : ℝ) ≤ (qN A N : ℝ) := hchain.trans hq
  exact_mod_cast hfin

/-- The sum of a nonnegative function over `Icc 1 M` is bounded by the sum
over the covering pieces `{1} ∪ Icc 2 m ∪ Icc (m+1) q ∪ Icc (q+1) M` (the
pieces may overlap at the boundaries, which only adds nonnegative terms). -/
lemma sum_Icc_le_four_piece (f : ℕ → ℝ) (hf : ∀ r, 0 ≤ f r) {M q m : ℕ}
    (_hmq : m ≤ q) (_hqM : q ≤ M) :
    ∑ r ∈ Finset.Icc 1 M, f r ≤
      f 1 + (∑ r ∈ Finset.Icc 2 m, f r +
        (∑ r ∈ Finset.Icc (m + 1) q, f r + ∑ r ∈ Finset.Icc (q + 1) M, f r)) := by
  have hunion : Finset.Icc 1 M ⊆
      {1} ∪ (Finset.Icc 2 m ∪ (Finset.Icc (m + 1) q ∪ Finset.Icc (q + 1) M)) := by
    intro r hr
    simp only [Finset.mem_Icc] at hr
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hadd : ∀ s t : Finset ℕ, (∑ r ∈ s ∪ t, f r) ≤ (∑ r ∈ s, f r) + (∑ r ∈ t, f r) := by
    intro s t
    have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
    have hnn : 0 ≤ ∑ r ∈ s ∩ t, f r := Finset.sum_nonneg (fun r _ => hf r)
    linarith
  calc ∑ r ∈ Finset.Icc 1 M, f r
      ≤ ∑ r ∈ {1} ∪ (Finset.Icc 2 m ∪ (Finset.Icc (m + 1) q ∪ Finset.Icc (q + 1) M)), f r :=
        Finset.sum_le_sum_of_subset_of_nonneg hunion (fun r _ _ => hf r)
    _ ≤ f 1 + ((∑ r ∈ Finset.Icc 2 m, f r) +
          ((∑ r ∈ Finset.Icc (m + 1) q, f r) + ∑ r ∈ Finset.Icc (q + 1) M, f r)) := by
        have h1 := hadd ({1} : Finset ℕ) (Finset.Icc 2 m ∪ (Finset.Icc (m + 1) q ∪ Finset.Icc (q + 1) M))
        have h2 := hadd (Finset.Icc 2 m) (Finset.Icc (m + 1) q ∪ Finset.Icc (q + 1) M)
        have h3 := hadd (Finset.Icc (m + 1) q) (Finset.Icc (q + 1) M)
        rw [Finset.sum_singleton] at h1
        linarith

/-- The far piece `N · ∑_{r = q_N + 1}^{N/k} P (Exc 0 ∩ Exc r)` is bounded by
`(1/k) (N p_N)² + N · (mixing tail)`, via `pair_mix`. -/
lemma far_piece_le (z : ℝ) (k : ℕ) (A : ℝ) (N : ℕ) :
    (N : ℝ) * ∑ r ∈ Finset.Icc (qN A N + 1) (N / k), pairTail D z N r ≤
      (1 / (k : ℝ)) * ((N : ℝ) * oneTail D z N) ^ 2 +
        (N : ℝ) * ∑' j : ℕ, D.alpha (qN A N + j) := by
  have h1 : (∑ r ∈ Finset.Icc (qN A N + 1) (N / k), pairTail D z N r) ≤
      ∑ r ∈ Finset.Icc (qN A N + 1) (N / k), (oneTail D z N ^ 2 + D.alpha r) := by
    apply Finset.sum_le_sum
    intro r _
    have h := D.pair_mix (gumbelU N z) r
    rw [pairTail_eq, oneTail_eq]
    exact h
  have hcard : (Finset.Icc (qN A N + 1) (N / k)).card = N / k - qN A N := by
    rw [Nat.card_Icc]
    omega
  have h2 : (∑ r ∈ Finset.Icc (qN A N + 1) (N / k), (oneTail D z N ^ 2 + D.alpha r)) =
      ((N / k - qN A N : ℕ) : ℝ) * oneTail D z N ^ 2 +
        ∑ r ∈ Finset.Icc (qN A N + 1) (N / k), D.alpha r := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hcast : ((N / k - qN A N : ℕ) : ℝ) ≤ (N : ℝ) / k := by
    calc ((N / k - qN A N : ℕ) : ℝ) ≤ ((N / k : ℕ) : ℝ) := by
            exact_mod_cast Nat.sub_le (N / k) (qN A N)
      _ ≤ (N : ℝ) / k := Nat.cast_div_le
  have h3 : ((N / k - qN A N : ℕ) : ℝ) * oneTail D z N ^ 2 ≤
      ((N : ℝ) / k) * oneTail D z N ^ 2 :=
    mul_le_mul_of_nonneg_right hcast (sq_nonneg _)
  have h4 : (∑ r ∈ Finset.Icc (qN A N + 1) (N / k), D.alpha r) ≤
      ∑' j : ℕ, D.alpha (qN A N + j) := by
    have hsub : Finset.Icc (qN A N + 1) (N / k) ⊆ Finset.Icc (qN A N) (N / k) :=
      Finset.Icc_subset_Icc_left (by omega)
    calc (∑ r ∈ Finset.Icc (qN A N + 1) (N / k), D.alpha r)
        ≤ ∑ r ∈ Finset.Icc (qN A N) (N / k), D.alpha r :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => D.alpha_nonneg r)
      _ = ∑ j ∈ Finset.range (N / k + 1 - qN A N), D.alpha (qN A N + j) :=
          sum_Icc_eq_sum_range_nat _ _ _
      _ ≤ ∑' j : ℕ, D.alpha (qN A N + j) :=
          Summable.sum_le_tsum _ (fun j _ => D.alpha_nonneg _) (summable_alpha_add D _)
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  calc (N : ℝ) * ∑ r ∈ Finset.Icc (qN A N + 1) (N / k), pairTail D z N r
      ≤ (N : ℝ) * (((N / k - qN A N : ℕ) : ℝ) * oneTail D z N ^ 2 +
            ∑ r ∈ Finset.Icc (qN A N + 1) (N / k), D.alpha r) :=
        mul_le_mul_of_nonneg_left (h1.trans h2.le) hN
    _ = (N : ℝ) * (((N / k - qN A N : ℕ) : ℝ) * oneTail D z N ^ 2) +
          (N : ℝ) * ∑ r ∈ Finset.Icc (qN A N + 1) (N / k), D.alpha r := by
        rw [mul_add]
    _ ≤ (N : ℝ) * (((N : ℝ) / k) * oneTail D z N ^ 2) +
          (N : ℝ) * ∑' j : ℕ, D.alpha (qN A N + j) :=
        add_le_add (mul_le_mul_of_nonneg_left h3 hN) (mul_le_mul_of_nonneg_left h4 hN)
    _ = (1 / (k : ℝ)) * ((N : ℝ) * oneTail D z N) ^ 2 +
          (N : ℝ) * ∑' j : ℕ, D.alpha (qN A N + j) := by
        congr 1
        ring

/-- **T4**: with `τ = e^{-z}`, the pair-sum quantity satisfies
`DD k N ≤ τ²/k + 1/k` eventually. The four-piece split at `m_N` and `q_N`
kills the touching, separated and mesoscopic pieces (via the corresponding
`Airy1BlockExtremes` fields), while the far piece is at most
`(1/k)(N p_N)² + N · tail → τ²/k`, which is eventually strictly below
`τ²/k + 1/k`. -/
theorem D_eventually_le (z : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ N : ℕ in atTop,
      DD D z k N ≤ Real.exp (-z) ^ 2 / (k : ℝ) + 1 / (k : ℝ) := by
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  -- the mesoscopic split parameter `χ`, midpoint of `(1/2)^{1/3}` and `1`
  set χ₀ : ℝ := (1 / 2) ^ ((1 : ℝ) / 3) with hχ₀def
  have hχ₀1 : χ₀ < 1 := by
    rw [hχ₀def]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  have hχ₀pos : 0 < χ₀ := by
    rw [hχ₀def]
    exact Real.rpow_pos_of_pos (by norm_num) _
  set χ : ℝ := (χ₀ + 1) / 2 with hχdef
  have hχ1 : χ₀ < χ := by rw [hχdef]; linarith
  have hχ2 : χ < 1 := by rw [hχdef]; linarith
  -- the enlarged polylogarithmic cut `A`
  obtain ⟨A₀, hA₀, hA₀c, -⟩ := D.mixing_tail
  set A : ℝ := max A₀ (Real.sqrt (6 * airyGamma)) with hAdef
  have hApos : 0 < A := hA₀.trans_le (le_max_left _ _)
  have hAsqrt : Real.sqrt (6 * airyGamma) ≤ A := le_max_right _ _
  have hAc : 1 < D.mixc * A ^ 3 := by
    have h1 : A₀ ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ hA₀.le (le_max_left _ _) 3
    have h2 : D.mixc * A₀ ^ 3 ≤ D.mixc * A ^ 3 := mul_le_mul_of_nonneg_left h1 D.mixc_pos.le
    linarith [hA₀c]
  have hAtail : Tendsto (fun N : ℕ => (N : ℝ) * ∑' j : ℕ, D.alpha (qN A N + j)) atTop (𝓝 0) :=
    mixing_tail_of_bound D.mixC_pos D.mixc_pos D.alpha_bound D.alpha_nonneg hApos hAc
  -- the four pieces
  have hT1 : Tendsto (fun N : ℕ => (N : ℝ) * pairTail D z N 1) atTop (𝓝 0) :=
    Tendsto.congr' (Eventually.of_forall fun N => rfl) (D.touching z)
  have hT2 : Tendsto (fun N : ℕ => (N : ℝ) *
      (∑ r ∈ Finset.Icc 2 (mN χ z N), pairTail D z N r)) atTop (𝓝 0) :=
    Tendsto.congr' (Eventually.of_forall fun N => rfl) (D.separated z χ hχ1 hχ2)
  have hT3 : Tendsto (fun N : ℕ => (N : ℝ) *
      (∑ r ∈ Finset.Icc (mN χ z N + 1) (qN A N), pairTail D z N r)) atTop (𝓝 0) :=
    Tendsto.congr' (Eventually.of_forall fun N => rfl) (D.mesoscopic z χ A hχ1 hχ2 hApos)
  have hTN : Tendsto (fun N : ℕ => (N : ℝ) * oneTail D z N) atTop (𝓝 (Real.exp (-z))) :=
    Tendsto.congr' (Eventually.of_forall fun N => rfl) (D.tail_normalized z)
  -- the assembled bound `G N → τ²/k`
  have h123 : Tendsto (fun N : ℕ => (N : ℝ) * pairTail D z N 1 +
      (N : ℝ) * (∑ r ∈ Finset.Icc 2 (mN χ z N), pairTail D z N r) +
      (N : ℝ) * (∑ r ∈ Finset.Icc (mN χ z N + 1) (qN A N), pairTail D z N r))
      atTop (𝓝 0) := by
    have h := (hT1.add hT2).add hT3
    simpa using h
  have hfar : Tendsto (fun N : ℕ => (1 / (k : ℝ)) * ((N : ℝ) * oneTail D z N) ^ 2 +
      (N : ℝ) * (∑' j : ℕ, D.alpha (qN A N + j)))
      atTop (𝓝 (Real.exp (-z) ^ 2 / (k : ℝ))) := by
    have h := ((hTN.pow 2).const_mul (1 / (k : ℝ))).add hAtail
    have hlim : (1 / (k : ℝ)) * Real.exp (-z) ^ 2 + 0 = Real.exp (-z) ^ 2 / (k : ℝ) := by
      rw [add_zero, one_div_mul_eq_div]
    rwa [hlim] at h
  have hG : Tendsto (fun N : ℕ => ((N : ℝ) * pairTail D z N 1 +
        (N : ℝ) * (∑ r ∈ Finset.Icc 2 (mN χ z N), pairTail D z N r) +
        (N : ℝ) * (∑ r ∈ Finset.Icc (mN χ z N + 1) (qN A N), pairTail D z N r)) +
        ((1 / (k : ℝ)) * ((N : ℝ) * oneTail D z N) ^ 2 +
          (N : ℝ) * (∑' j : ℕ, D.alpha (qN A N + j))))
      atTop (𝓝 (Real.exp (-z) ^ 2 / (k : ℝ))) := by
    have h := h123.add hfar
    simpa using h
  have hGlt : ∀ᶠ N : ℕ in atTop, ((N : ℝ) * pairTail D z N 1 +
        (N : ℝ) * (∑ r ∈ Finset.Icc 2 (mN χ z N), pairTail D z N r) +
        (N : ℝ) * (∑ r ∈ Finset.Icc (mN χ z N + 1) (qN A N), pairTail D z N r)) +
        ((1 / (k : ℝ)) * ((N : ℝ) * oneTail D z N) ^ 2 +
          (N : ℝ) * (∑' j : ℕ, D.alpha (qN A N + j))) <
      Real.exp (-z) ^ 2 / (k : ℝ) + 1 / (k : ℝ) :=
    hG.eventually (eventually_lt_nhds (by
      have h1k : (0 : ℝ) < 1 / (k : ℝ) := one_div_pos.mpr hkr
      linarith))
  have hDDle : ∀ᶠ N : ℕ in atTop, DD D z k N ≤ ((N : ℝ) * pairTail D z N 1 +
        (N : ℝ) * (∑ r ∈ Finset.Icc 2 (mN χ z N), pairTail D z N r) +
        (N : ℝ) * (∑ r ∈ Finset.Icc (mN χ z N + 1) (qN A N), pairTail D z N r)) +
        ((1 / (k : ℝ)) * ((N : ℝ) * oneTail D z N) ^ 2 +
          (N : ℝ) * (∑' j : ℕ, D.alpha (qN A N + j))) := by
    filter_upwards [eventually_qN_add_le_div hApos hk 2,
      mN_le_qN_eventually χ z (hχ₀pos.trans hχ1).le hχ2.le hAsqrt] with N hqN hmN
    have hnn : ∀ r : ℕ, 0 ≤ pairTail D z N r := fun r => measureReal_nonneg _
    have hcov : (∑ r ∈ Finset.Icc 1 (N / k), pairTail D z N r) ≤
        pairTail D z N 1 + ((∑ r ∈ Finset.Icc 2 (mN χ z N), pairTail D z N r) +
          ((∑ r ∈ Finset.Icc (mN χ z N + 1) (qN A N), pairTail D z N r) +
            (∑ r ∈ Finset.Icc (qN A N + 1) (N / k), pairTail D z N r))) :=
      sum_Icc_le_four_piece (fun r => pairTail D z N r) hnn hmN (by omega)
    have hfarN := far_piece_le D z k A N
    have hNN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have hstep : (N : ℝ) * (∑ r ∈ Finset.Icc 1 (N / k), pairTail D z N r) ≤
        (N : ℝ) * (pairTail D z N 1 + ((∑ r ∈ Finset.Icc 2 (mN χ z N), pairTail D z N r) +
          ((∑ r ∈ Finset.Icc (mN χ z N + 1) (qN A N), pairTail D z N r) +
            (∑ r ∈ Finset.Icc (qN A N + 1) (N / k), pairTail D z N r)))) :=
      mul_le_mul_of_nonneg_left hcov hNN
    have hexp : (N : ℝ) * (pairTail D z N 1 + ((∑ r ∈ Finset.Icc 2 (mN χ z N), pairTail D z N r) +
        ((∑ r ∈ Finset.Icc (mN χ z N + 1) (qN A N), pairTail D z N r) +
          (∑ r ∈ Finset.Icc (qN A N + 1) (N / k), pairTail D z N r)))) =
        (N : ℝ) * pairTail D z N 1 + ((N : ℝ) * (∑ r ∈ Finset.Icc 2 (mN χ z N), pairTail D z N r) +
          ((N : ℝ) * (∑ r ∈ Finset.Icc (mN χ z N + 1) (qN A N), pairTail D z N r) +
            (N : ℝ) * (∑ r ∈ Finset.Icc (qN A N + 1) (N / k), pairTail D z N r))) := by ring
    rw [DD]
    calc (N : ℝ) * (∑ r ∈ Finset.Icc 1 (N / k), pairTail D z N r)
        ≤ (N : ℝ) * (pairTail D z N 1 + ((∑ r ∈ Finset.Icc 2 (mN χ z N), pairTail D z N r) +
            ((∑ r ∈ Finset.Icc (mN χ z N + 1) (qN A N), pairTail D z N r) +
              (∑ r ∈ Finset.Icc (qN A N + 1) (N / k), pairTail D z N r)))) := hstep
      _ ≤ ((N : ℝ) * pairTail D z N 1 +
            (N : ℝ) * (∑ r ∈ Finset.Icc 2 (mN χ z N), pairTail D z N r) +
            (N : ℝ) * (∑ r ∈ Finset.Icc (mN χ z N + 1) (qN A N), pairTail D z N r)) +
            ((1 / (k : ℝ)) * ((N : ℝ) * oneTail D z N) ^ 2 +
              (N : ℝ) * (∑' j : ℕ, D.alpha (qN A N + j))) := by
          rw [hexp]
          linarith [hfarN]
  filter_upwards [hDDle, hGlt] with N h1 h2
  exact (h1.trans_lt h2).le

end DQuantity

end Airy1Gumbel
