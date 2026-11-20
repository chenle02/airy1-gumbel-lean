/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Mesh.Skeleton

/-!
# Dyadic reflection and the mesh hitting-kernel limit

Let `B` be a Brownian motion (Mathlib `IsBrownianReal`: pre-Brownian with a.s. continuous
paths) with measurable coordinates, `X = B − B 0`, `τ = 2T` (Brownian time; `X_τ ~ N(0, 2T)`
has density `heatKernel T`), the dyadic grid `t_{n,j} = jτ/2ⁿ` and a start `u < M`.

* **Survival / crossing.** `survSet n = {u + X_{t_{n,j}} ≤ M ∀ j < 2ⁿ}`, decreasing in `n`;
  `crossSet = ⋃ₙ (survSet n)ᶜ`.
* **Skeleton identification on the mesh** (`measure_survSet_inter`, `measure_compl_survSet_inter`):
  the law of
  `u + X_τ` on `survSet n` has density `lamKerN` of the mesh, and on its complement the mesh
  hitting kernel `meshHitKer M T n (u, ·)`.
* **Fixed-`n` reflection** (`measure_compl_survSet_inter_le_eq`): decompose on the first grid
  crossing `k`; the increment `X_τ − X_{t_k}` is independent of the pre-`t_k` skeleton
  (weak Markov, `indepFun_shift`) and symmetric, so it can be flipped (`measure_flip`).  No
  strong Markov property and no stopping-time σ-algebra are used.
* **Continuity limit** (`measure_crossSet_inter_Iic`): the overshoot of the first crossing
  is at most the grid modulus of the path (uniform continuity on `[0, τ]`), giving the
  reflection principle in CDF form `P(crossSet, u + X_τ ≤ v) = P(u + X_τ ≥ 2M − v)` for
  `v ≤ M`.
* **Kernel identification** (`measure_crossSet_inter`): the law of `u + X_τ` on `crossSet`
  has density `Q_{M,T}(u, ·) = AiryConj.qMT M T u ·`.
* **The kernel fact** (`meshHittingLimit_of_isBrownianReal`): `MeshHittingLimit M T` for all
  `M` and `T > 0` — (K1) from `(survSet n)ᶜ ⊆ crossSet`, (K2) by monotone convergence of
  the densities and equality of total masses; `u > M` is exact; Tonelli lifts to `ℝ²`.
-/

namespace AiryFdd

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

/-! ## The dyadic grid in Brownian time -/

/-- The grid time `t_{n,j} = j τ / 2ⁿ`. -/
noncomputable def gridT (τ : ℝ≥0) (n j : ℕ) : ℝ≥0 := (j : ℝ≥0) * (τ / 2 ^ n)

theorem coe_gridT (τ : ℝ≥0) (n j : ℕ) : (gridT τ n j : ℝ) = j * ((τ : ℝ) / 2 ^ n) := by
  simp [gridT]

theorem gridT_zero (τ : ℝ≥0) (n : ℕ) : gridT τ n 0 = 0 := by simp [gridT]

theorem gridT_pow (τ : ℝ≥0) (n : ℕ) : gridT τ n (2 ^ n) = τ := by
  apply NNReal.eq
  rw [coe_gridT]
  push_cast
  field_simp

theorem gridT_le {τ : ℝ≥0} {n j : ℕ} (hj : j ≤ 2 ^ n) : gridT τ n j ≤ τ := by
  rw [← NNReal.coe_le_coe, coe_gridT]
  have h1 : (j : ℝ) ≤ 2 ^ n := by exact_mod_cast hj
  calc (j : ℝ) * ((τ : ℝ) / 2 ^ n) ≤ 2 ^ n * ((τ : ℝ) / 2 ^ n) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = τ := by field_simp

theorem gridT_mono {τ : ℝ≥0} {n j k : ℕ} (hjk : j ≤ k) : gridT τ n j ≤ gridT τ n k := by
  rw [← NNReal.coe_le_coe, coe_gridT, coe_gridT]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjk) (by positivity)

theorem gridT_double (τ : ℝ≥0) (n j : ℕ) : gridT τ (n + 1) (2 * j) = gridT τ n j := by
  apply NNReal.eq
  rw [coe_gridT, coe_gridT]
  push_cast
  rw [pow_succ]
  field_simp

/-- **The grid modulus of a continuous path tends to 0**: for every `ε > 0`, eventually all
consecutive grid increments of `f` on `[0, τ]` are `< ε` (uniform continuity on `[0, τ]`). -/
theorem exists_grid_incr_lt {f : ℝ≥0 → ℝ} (hf : Continuous f) (τ : ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) : ∃ m : ℕ, ∀ n ≥ m, ∀ j, j + 1 ≤ 2 ^ n →
      |f (gridT τ n (j + 1)) - f (gridT τ n j)| < ε := by
  have hu := (isCompact_Icc (a := (0 : ℝ≥0)) (b := τ)).uniformContinuousOn_of_continuous
    hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hδ'⟩ := hu ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt ((τ : ℝ) / δ)
  refine ⟨m, fun n hn j hj => ?_⟩
  have hmem : ∀ i, i ≤ 2 ^ n → gridT τ n i ∈ Icc (0 : ℝ≥0) τ :=
    fun i hi => ⟨zero_le, gridT_le hi⟩
  have hd : dist (gridT τ n (j + 1)) (gridT τ n j) < δ := by
    rw [NNReal.dist_eq, coe_gridT, coe_gridT]
    have h2n : (m : ℝ) ≤ 2 ^ n := by
      have h1 : m < 2 ^ m := Nat.lt_two_pow_self
      calc (m : ℝ) ≤ 2 ^ m := by exact_mod_cast h1.le
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hτ0 : (0 : ℝ) ≤ τ := τ.2
    rw [show ((j + 1 : ℕ) : ℝ) * ((τ : ℝ) / 2 ^ n) - j * ((τ : ℝ) / 2 ^ n) = (τ : ℝ) / 2 ^ n by
      push_cast; ring, abs_of_nonneg (by positivity)]
    have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
    calc (τ : ℝ) / 2 ^ n ≤ τ / m := div_le_div_of_nonneg_left hτ0 hm0 h2n
      _ < δ := by
        rw [div_lt_iff₀ hm0]
        rw [div_lt_iff₀ hδ] at hm
        linarith
  have := hδ' _ (hmem _ hj) _ (hmem _ (by omega)) hd
  rwa [Real.dist_eq] at this

/-- If `M < u + f τ` for a continuous `f`, the last grid point eventually crosses `M`. -/
theorem exists_last_cross {f : ℝ≥0 → ℝ} (hf : Continuous f) (τ : ℝ≥0) {u M : ℝ}
    (h : M < u + f τ) : ∃ m : ℕ, ∀ n ≥ m, M < u + f (gridT τ n (2 ^ n - 1)) := by
  obtain ⟨m, hm⟩ := exists_grid_incr_lt hf τ (sub_pos.2 h)
  refine ⟨m, fun n hn => ?_⟩
  have h1 : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel Nat.one_le_two_pow
  have := hm n hn (2 ^ n - 1) h1.le
  rw [h1, gridT_pow] at this
  have := (abs_lt.1 this).2
  linarith

/-! ## Survival, first crossing and the reflected event -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The skeleton stays below `M` at all grid times `t_{n,j}`, `j < 2ⁿ`. -/
def survSet (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (M u : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ j < 2 ^ n, u + (B (gridT τ n j) ω - B 0 ω) ≤ M}

/-- Some dyadic grid point exceeds `M`. -/
def crossSet (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (M u : ℝ) : Set Ω :=
  ⋃ n, (survSet B τ M u n)ᶜ

/-- The end value `u + X_τ`. -/
def endVal (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (u : ℝ) (ω : Ω) : ℝ := u + (B τ ω - B 0 ω)

/-- The first grid crossing is at `t_{n,k}`. -/
def firstSet (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (M u : ℝ) (n k : ℕ) : Set Ω :=
  {ω | (∀ j < k, u + (B (gridT τ n j) ω - B 0 ω) ≤ M) ∧ M < u + (B (gridT τ n k) ω - B 0 ω)}

/-- The reflected event `{first crossing at t_k, u + X_τ ≥ 2(u + X_{t_k}) − v}`. -/
def reflSet (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (M u v : ℝ) (n : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range (2 ^ n), firstSet B τ M u n k ∩
    {ω | 2 * (u + (B (gridT τ n k) ω - B 0 ω)) - v ≤ endVal B τ u ω}

theorem survSet_succ_subset (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (M u : ℝ) (n : ℕ) :
    survSet B τ M u (n + 1) ⊆ survSet B τ M u n := by
  intro ω hω j hj
  have := hω (2 * j) (by rw [pow_succ]; omega)
  rwa [gridT_double] at this

theorem compl_survSet_mono (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (M u : ℝ) :
    Monotone fun n => (survSet B τ M u n)ᶜ :=
  monotone_nat_of_le_succ fun n => compl_subset_compl.2 (survSet_succ_subset B τ M u n)

section Measurability

variable {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
include hm

theorem measurable_endVal (τ : ℝ≥0) (u : ℝ) : Measurable (endVal B τ u) :=
  ((hm τ).sub (hm 0)).const_add u

theorem measurableSet_survSet (τ : ℝ≥0) (M u : ℝ) (n : ℕ) :
    MeasurableSet (survSet B τ M u n) :=
  measurableSet_forall_lt (2 ^ n) (s := fun j => {ω | u + (B (gridT τ n j) ω - B 0 ω) ≤ M})
    fun _ => measurableSet_le (((hm _).sub (hm 0)).const_add u) measurable_const

theorem measurableSet_firstSet (τ : ℝ≥0) (M u : ℝ) (n k : ℕ) :
    MeasurableSet (firstSet B τ M u n k) := by
  unfold firstSet
  rw [Set.ofPred_and]
  exact (measurableSet_forall_lt k (s := fun j => {ω | u + (B (gridT τ n j) ω - B 0 ω) ≤ M})
    fun j => measurableSet_le (((hm _).sub (hm 0)).const_add u) measurable_const).inter
    (measurableSet_lt measurable_const (((hm _).sub (hm 0)).const_add u))

theorem measurableSet_reflCond (τ : ℝ≥0) (u v : ℝ) (n k : ℕ) :
    MeasurableSet {ω | 2 * (u + (B (gridT τ n k) ω - B 0 ω)) - v ≤ endVal B τ u ω} :=
  measurableSet_le (((((hm _).sub (hm 0)).const_add u).const_mul 2).sub_const v)
    (measurable_endVal hm τ u)

end Measurability

/-- The complement of survival is the disjoint union of the first-crossing events. -/
theorem compl_survSet_eq (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (M u : ℝ) (n : ℕ) :
    (survSet B τ M u n)ᶜ = ⋃ k ∈ Finset.range (2 ^ n), firstSet B τ M u n k := by
  classical
  ext ω
  simp only [mem_compl_iff, mem_iUnion, Finset.mem_range, exists_prop, survSet, firstSet,
    mem_ofPred_eq]
  constructor
  · intro hω
    have hex : ∃ j, j < 2 ^ n ∧ M < u + (B (gridT τ n j) ω - B 0 ω) := by
      by_contra hne
      push Not at hne
      exact hω hne
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, fun j hj => ?_, (Nat.find_spec hex).2⟩
    have := Nat.find_min hex hj
    push Not at this
    exact this (lt_trans hj (Nat.find_spec hex).1)
  · rintro ⟨k, hk, -, hMk⟩ hsurv
    exact absurd (hsurv k hk) (not_le.2 hMk)

theorem firstSet_disjoint (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (M u : ℝ) (n : ℕ) {k l : ℕ}
    (hkl : k ≠ l) : Disjoint (firstSet B τ M u n k) (firstSet B τ M u n l) := by
  rcases lt_or_gt_of_ne hkl with h | h
  · exact Set.disjoint_left.2 fun ω h1 h2 => absurd (h2.1 k h) (not_le.2 h1.2)
  · exact Set.disjoint_left.2 fun ω h1 h2 => absurd (h1.1 l h) (not_le.2 h2.2)

theorem reflSet_subset (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (M u v : ℝ) (n : ℕ) :
    reflSet B τ M u v n ⊆ {ω | 2 * M - v < endVal B τ u ω} := by
  intro ω hω
  simp only [reflSet, mem_iUnion, Finset.mem_range, exists_prop] at hω
  obtain ⟨k, -, ⟨-, hMk⟩, hr⟩ := hω
  simp only [mem_ofPred_eq] at hr ⊢
  linarith

/-! ## The flip -/

/-- **Symmetric flip.** If `Z` is independent of `R` and `−Z` has the law of `Z`, then
`(R, Z)` and `(R, −Z)` have the same law. -/
theorem measure_flip {α : Type*} [MeasurableSpace α] [IsFiniteMeasure P] {R : Ω → α}
    {Z : Ω → ℝ} (hR : Measurable R) (hZ : Measurable Z) (hind : IndepFun R Z P)
    (hsym : P.map (-Z) = P.map Z) {S : Set (α × ℝ)} (hS : MeasurableSet S) :
    P {ω | (R ω, -Z ω) ∈ S} = P {ω | (R ω, Z ω) ∈ S} := by
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hR.aemeasurable hZ.aemeasurable).1 hind
  have hind' : IndepFun R (-Z) P := hind.comp measurable_id measurable_neg
  have h2 := (indepFun_iff_map_prod_eq_prod_map_map hR.aemeasurable
    hZ.neg.aemeasurable).1 hind'
  have e1 : P {ω | (R ω, Z ω) ∈ S} = P.map (fun ω => (R ω, Z ω)) S :=
    (Measure.map_apply (hR.prodMk hZ) hS).symm
  have e2 : P {ω | (R ω, -Z ω) ∈ S} = P.map (fun ω => (R ω, (-Z) ω)) S :=
    (Measure.map_apply (hR.prodMk hZ.neg) hS).symm
  rw [e1, e2, h1, h2, hsym]

section Reflection

variable {B : ℝ≥0 → Ω → ℝ}

/-- **The flip at the first crossing `t_k`.** -/
theorem measure_firstSet_flip (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (τ : ℝ≥0) (M u v : ℝ) {n k : ℕ} (hk : k < 2 ^ n) :
    P (firstSet B τ M u n k ∩ {ω | endVal B τ u ω ≤ v}) =
      P (firstSet B τ M u n k ∩
        {ω | 2 * (u + (B (gridT τ n k) ω - B 0 ω)) - v ≤ endVal B τ u ω}) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  set t := gridT τ n k with ht
  have htτ : t ≤ τ := gridT_le hk.le
  set R : Ω → (ℕ → ℝ) := fun ω j => B (gridT τ n (min j k)) ω - B 0 ω with hRdef
  set Z : Ω → ℝ := B τ - B t with hZdef
  have hRm : Measurable R := Measurable.of_eval fun j => (hm _).sub (hm 0)
  have hZm : Measurable Z := (hm τ).sub (hm t)
  have hind : IndepFun R Z P := by
    have h0 := hB.indepFun_shift t
    have h1 := h0.comp (φ := fun (f : ℝ≥0 → ℝ) => f (τ - t))
      (ψ := fun (r : Iic t → ℝ) (j : ℕ) =>
        r ⟨gridT τ n (min j k), Set.mem_Iic.2 (gridT_mono (min_le_right j k))⟩ -
          r ⟨0, Set.mem_Iic.2 zero_le⟩)
      (measurable_pi_apply (τ - t) : Measurable fun f : ℝ≥0 → ℝ => f (τ - t))
      (Measurable.of_eval fun j => by fun_prop)
    have hZ' : ((fun (f : ℝ≥0 → ℝ) => f (τ - t)) ∘
        fun ω s => B (t + s) ω - B t ω) = Z := by
      funext ω
      simp only [Function.comp_apply, add_tsub_cancel_of_le htτ, hZdef, Pi.sub_apply]
    rw [hZ'] at h1
    exact h1.symm
  have hsym : P.map (-Z) = P.map Z := by
    have hl := (hB.hasLaw_sub τ t).map_eq
    have e : (-Z) = (fun x : ℝ => -x) ∘ Z := rfl
    rw [e, ← Measure.map_map measurable_neg hZm, hZdef, hl, gaussianReal_map_neg, neg_zero]
  set S1 : Set ((ℕ → ℝ) × ℝ) :=
    {p | (∀ j < k, u + p.1 j ≤ M) ∧ M < u + p.1 k ∧ u + p.1 k + p.2 ≤ v} with hS1def
  have hS1 : MeasurableSet S1 := by
    rw [hS1def, Set.ofPred_and, Set.ofPred_and]
    refine (measurableSet_forall_lt k (s := fun j => {p : (ℕ → ℝ) × ℝ | u + p.1 j ≤ M})
      fun j => measurableSet_le (by fun_prop) measurable_const).inter
      ((measurableSet_lt measurable_const (by fun_prop)).inter
        (measurableSet_le (by fun_prop) measurable_const))
  have hRj : ∀ ω, ∀ j ≤ k, R ω j = B (gridT τ n j) ω - B 0 ω := by
    intro ω j hj
    simp only [hRdef, min_eq_left hj]
  have hend : ∀ ω, endVal B τ u ω = u + R ω k + Z ω := by
    intro ω
    rw [hRj ω k le_rfl]
    simp only [endVal, hZdef, Pi.sub_apply, ht]
    ring
  have e1 : firstSet B τ M u n k ∩ {ω | endVal B τ u ω ≤ v} = {ω | (R ω, Z ω) ∈ S1} := by
    ext ω
    simp only [firstSet, hS1def, mem_inter_iff, mem_ofPred_eq, hend ω]
    rw [hRj ω k le_rfl]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun j hj => by rw [hRj ω j hj.le]; exact h1 j hj, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun j hj => by rw [← hRj ω j hj.le]; exact h1 j hj, h2⟩, h3⟩
  have e2 : firstSet B τ M u n k ∩
      {ω | 2 * (u + (B (gridT τ n k) ω - B 0 ω)) - v ≤ endVal B τ u ω} =
      {ω | (R ω, -Z ω) ∈ S1} := by
    ext ω
    simp only [firstSet, hS1def, mem_inter_iff, mem_ofPred_eq, hend ω]
    rw [hRj ω k le_rfl]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun j hj => by rw [hRj ω j hj.le]; exact h1 j hj, h2, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun j hj => by rw [← hRj ω j hj.le]; exact h1 j hj, h2⟩, by linarith⟩
  rw [e1, e2, measure_flip hRm hZm hind hsym hS1]

/-- **Fixed-`n` reflection identity**: `P(not surviving, u + X_τ ≤ v) = P(reflSet n)`. -/
theorem measure_compl_survSet_inter_le_eq (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (τ : ℝ≥0) (M u v : ℝ) (n : ℕ) :
    P ((survSet B τ M u n)ᶜ ∩ {ω | endVal B τ u ω ≤ v}) = P (reflSet B τ M u v n) := by
  have hC : MeasurableSet {ω | endVal B τ u ω ≤ v} :=
    measurableSet_le (measurable_endVal hm τ u) measurable_const
  rw [compl_survSet_eq, Set.iUnion₂_inter, reflSet,
    measure_biUnion_finset _ (fun k _ => (measurableSet_firstSet hm τ M u n k).inter hC),
    measure_biUnion_finset _ (fun k _ =>
      (measurableSet_firstSet hm τ M u n k).inter (measurableSet_reflCond hm τ u v n k))]
  · exact Finset.sum_congr rfl fun k hk =>
      measure_firstSet_flip hB hm τ M u v (Finset.mem_range.1 hk)
  · exact fun k _ l _ hkl =>
      (firstSet_disjoint B τ M u n hkl).mono inter_subset_left inter_subset_left
  · exact fun k _ l _ hkl =>
      (firstSet_disjoint B τ M u n hkl).mono inter_subset_left inter_subset_left

/-- **Pathwise overshoot control.** For a continuous path with `u < M`, `v ≤ M` and
`u + X_τ > 2M − v`, eventually the path lies in the reflected event. -/
theorem eventually_mem_reflSet {ω : Ω} (hc : Continuous fun t => B t ω) (τ : ℝ≥0)
    {M u v : ℝ} (hu : u < M) (hv : v ≤ M) (hY : 2 * M - v < endVal B τ u ω) :
    ∃ m, ∀ n ≥ m, ω ∈ reflSet B τ M u v n := by
  classical
  set f : ℝ≥0 → ℝ := fun t => B t ω - B 0 ω with hfdef
  have hf : Continuous f := hc.sub continuous_const
  have hYf : endVal B τ u ω = u + f τ := rfl
  set ε := (endVal B τ u ω - (2 * M - v)) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨m1, hm1⟩ := exists_grid_incr_lt hf τ hεpos
  obtain ⟨m2, hm2⟩ := exists_last_cross hf τ (u := u) (M := M) (by rw [← hYf]; linarith)
  refine ⟨max m1 m2, fun n hn => ?_⟩
  have hex : ∃ j, j < 2 ^ n ∧ M < u + f (gridT τ n j) :=
    ⟨2 ^ n - 1, Nat.sub_lt (Nat.two_pow_pos n) one_pos, hm2 n (le_of_max_le_right hn)⟩
  set k := Nat.find hex with hkdef
  have hk : k < 2 ^ n := (Nat.find_spec hex).1
  have hMk : M < u + f (gridT τ n k) := (Nat.find_spec hex).2
  have hmin : ∀ j < k, u + f (gridT τ n j) ≤ M := by
    intro j hj
    have := Nat.find_min hex hj
    push Not at this
    exact this (lt_trans hj hk)
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, gridT_zero] at hMk
    simp [hfdef] at hMk
    linarith
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hinc := hm1 n (le_of_max_le_left hn) k' (by omega)
  rw [show k' + 1 = k by omega] at hinc
  have hprev := hmin k' (by omega)
  have hup := (abs_lt.1 hinc).2
  simp only [reflSet, mem_iUnion, Finset.mem_range, exists_prop]
  refine ⟨k, hk, ⟨hmin, hMk⟩, ?_⟩
  simp only [mem_ofPred_eq]
  change 2 * (u + f (gridT τ n k)) - v ≤ endVal B τ u ω
  linarith

/-- On a continuous path, `u + X_τ > M` forces a grid crossing. -/
theorem mem_crossSet_of_lt {ω : Ω} (hc : Continuous fun t => B t ω) (τ : ℝ≥0) {M u : ℝ}
    (hY : M < endVal B τ u ω) : ω ∈ crossSet B τ M u := by
  obtain ⟨m, hm⟩ := exists_last_cross (hc.sub continuous_const) τ (u := u) (M := M) hY
  refine mem_iUnion.2 ⟨m, fun hs => ?_⟩
  have h1 := hs (2 ^ m - 1) (Nat.sub_lt (Nat.two_pow_pos m) one_pos)
  have h2 : M < u + (B (gridT τ m (2 ^ m - 1)) ω - B 0 ω) := hm m le_rfl
  linarith

section Brownian

variable (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
include hB hm

/-- The law of the end value: `u + X_τ ~ N(u, τ)`. -/
theorem map_endVal (τ : ℝ≥0) (u : ℝ) : P.map (endVal B τ u) = gaussianReal u τ := by
  have := map_add_sub_eq hB.toIsPreBrownianReal hm (zero_le : (0 : ℝ≥0) ≤ τ) u
  rwa [tsub_zero] at this

/-- `P{u + X_τ = a} = 0`. -/
theorem measure_endVal_eq {τ : ℝ≥0} (hτ : τ ≠ 0) (u a : ℝ) :
    P (endVal B τ u ⁻¹' {a}) = 0 := by
  rw [← Measure.map_apply (measurable_endVal hm τ u) (measurableSet_singleton a),
    map_endVal hB hm]
  have := nullSingletonClass_gaussianReal (μ := u) hτ
  exact measure_singleton a

/-- **Reflection principle (CDF form)**: for `u < M` and `v ≤ M`,
`P(some grid point > M, u + X_τ ≤ v) = P(u + X_τ ≥ 2M − v)`. -/
theorem measure_crossSet_inter_Iic {τ : ℝ≥0} (hτ : τ ≠ 0) {M u v : ℝ} (hu : u < M)
    (hv : v ≤ M) :
    P (crossSet B τ M u ∩ {ω | endVal B τ u ω ≤ v}) = P {ω | 2 * M - v ≤ endVal B τ u ω} := by
  have hP := hB.toIsPreBrownianReal
  have := hP.isGaussianProcess.isProbabilityMeasure
  set C : ℕ → Set Ω := fun n => (survSet B τ M u n)ᶜ ∩ {ω | endVal B τ u ω ≤ v} with hCdef
  have hCmono : Monotone C := fun a b hab =>
    inter_subset_inter_left _ (compl_survSet_mono B τ M u hab)
  have hU : crossSet B τ M u ∩ {ω | endVal B τ u ω ≤ v} = ⋃ n, C n := by
    rw [crossSet, iUnion_inter]
  have hCeq : ∀ n, P (C n) = P (reflSet B τ M u v n) := fun n =>
    measure_compl_survSet_inter_le_eq hP hm τ M u v n
  rw [hU, hCmono.measure_iUnion]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    rw [hCeq n]
    exact measure_mono ((reflSet_subset B τ M u v n).trans fun ω hω => by
      simp only [mem_ofPred_eq] at hω ⊢; exact hω.le)
  · -- `≥`: no atom at `2M − v`, then the pathwise overshoot control
    set D : ℕ → Set Ω := fun m => ⋂ n, ⋂ (_ : m ≤ n), reflSet B τ M u v n with hDdef
    have hDmono : Monotone D := fun a b hab => by
      intro ω hω
      simp only [hDdef, mem_iInter] at hω ⊢
      exact fun n hn => hω n (hab.trans hn)
    have h1 : P {ω | 2 * M - v ≤ endVal B τ u ω} ≤ P (⋃ m, D m) := by
      have hsub : {ω | 2 * M - v ≤ endVal B τ u ω} ⊆
          {ω | 2 * M - v < endVal B τ u ω} ∪ endVal B τ u ⁻¹' {2 * M - v} := by
        intro ω hω
        rcases eq_or_lt_of_le (show 2 * M - v ≤ endVal B τ u ω from hω) with h | h
        · exact Or.inr h.symm
        · exact Or.inl h
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
      rw [measure_endVal_eq hB hm hτ, add_zero]
      refine measure_mono_ae ?_
      filter_upwards [hB.cont] with ω hc hω
      obtain ⟨m, hm'⟩ := eventually_mem_reflSet hc τ hu hv hω
      exact mem_iUnion.2 ⟨m, mem_iInter₂.2 fun n hn => hm' n hn⟩
    refine h1.trans ?_
    rw [hDmono.measure_iUnion]
    refine iSup_le fun m => ?_
    calc P (D m) ≤ P (reflSet B τ M u v m) :=
          measure_mono (iInter₂_subset m le_rfl)
      _ = P (C m) := (hCeq m).symm
      _ ≤ ⨆ n, P (C n) := le_iSup (fun n => P (C n)) m

omit hm in
/-- On `{u + X_τ > M}` the path crosses a grid point almost surely. -/
theorem measure_crossSet_inter_of_subset (τ : ℝ≥0) {M u : ℝ} {E : Set ℝ}
    (hE : E ⊆ Ioi M) : P (endVal B τ u ⁻¹' E ∩ crossSet B τ M u) = P (endVal B τ u ⁻¹' E) := by
  refine le_antisymm (measure_mono inter_subset_left) (measure_mono_ae ?_)
  filter_upwards [hB.cont] with ω hc hω
  exact ⟨hω, mem_crossSet_of_lt hc τ (hE hω)⟩

/-- **Kernel identification**: for `u < M`, the law of `u + X_τ` on `crossSet` has density
`Q_{M,T}(u, ·)` (`τ = 2T`). -/
theorem measure_crossSet_inter {T : ℝ} (hT : 0 < T) {τ : ℝ≥0} (hτ : (τ : ℝ) = 2 * T)
    {M u : ℝ} (hu : u < M) {S : Set ℝ} (hS : MeasurableSet S) :
    P (crossSet B τ M u ∩ endVal B τ u ⁻¹' S) =
      ∫⁻ v in S, ENNReal.ofReal (AiryConj.qMT M T u v) := by
  have hP := hB.toIsPreBrownianReal
  have := hP.isGaussianProcess.isProbabilityMeasure
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h, NNReal.coe_zero] at hτ; linarith
  have hme := measurable_endVal hm τ u
  set m1 : Measure ℝ := (P.restrict (crossSet B τ M u)).map (endVal B τ u) with hm1def
  set m2 : Measure ℝ := volume.withDensity fun v => ENNReal.ofReal (AiryConj.qMT M T u v)
    with hm2def
  have hm1 : ∀ A, MeasurableSet A → m1 A = P (endVal B τ u ⁻¹' A ∩ crossSet B τ M u) :=
    fun A hA => by rw [hm1def, Measure.map_apply hme hA, Measure.restrict_apply (hme hA)]
  -- the gaussian bridge
  have hG : ∀ μ : ℝ, gaussianReal μ τ =
      volume.withDensity (fun x => ENNReal.ofReal (heatKernel T (μ - x))) :=
    gaussianReal_eq_withDensity_heatKernel hT hτ
  -- left half-lines below `M`
  have hlow : ∀ a ≤ M, m1 (Iic a) = m2 (Iic a) := by
    intro a ha
    rw [hm1 _ measurableSet_Iic, inter_comm]
    have e1 : crossSet B τ M u ∩ endVal B τ u ⁻¹' Iic a =
        crossSet B τ M u ∩ {ω | endVal B τ u ω ≤ a} := rfl
    rw [e1, measure_crossSet_inter_Iic hB hm hτ0 hu ha]
    have e2 : {ω | 2 * M - a ≤ endVal B τ u ω} =
        endVal B τ u ⁻¹' ((fun x => 2 * M - x) ⁻¹' Iic a) := by
      ext ω; simp only [mem_ofPred_eq, mem_preimage, mem_Iic]; constructor <;> intro <;> linarith
    rw [e2, ← Measure.map_apply hme (measurable_const_sub _ measurableSet_Iic), map_endVal hB hm,
      ← Measure.map_apply (measurable_const_sub _) measurableSet_Iic, gaussianReal_map_const_sub,
      hG, hm2def, withDensity_apply _ measurableSet_Iic, withDensity_apply _ measurableSet_Iic]
    refine setLIntegral_congr_fun measurableSet_Iic (fun v hv => ?_)
    rw [AiryConj.qMT_eq_reflected hu.le ((mem_Iic.1 hv).trans ha)]
  -- the band `(M, a]`
  have hband : ∀ a, m1 (Ioc M a) = m2 (Ioc M a) := by
    intro a
    rw [hm1 _ measurableSet_Ioc,
      measure_crossSet_inter_of_subset hB τ (E := Ioc M a) Ioc_subset_Ioi_self,
      ← Measure.map_apply hme measurableSet_Ioc, map_endVal hB hm, hG, hm2def,
      withDensity_apply _ measurableSet_Ioc, withDensity_apply _ measurableSet_Ioc]
    refine setLIntegral_congr_fun measurableSet_Ioc (fun v hv => ?_)
    rw [AiryConj.qMT_eq_free (fun h => absurd h.2 (not_le.2 hv.1))]
  have hext : m1 = m2 := by
    refine Measure.ext_of_Iic m1 m2 fun a => ?_
    by_cases ha : a ≤ M
    · exact hlow a ha
    · have hU : Iic a = Iic M ∪ Ioc M a := (Iic_union_Ioc_eq_Iic (le_of_not_ge ha)).symm
      have hd : Disjoint (Iic M) (Ioc M a) :=
        Set.disjoint_left.2 fun x hx hy => not_lt.2 (mem_Iic.1 hx) hy.1
      rw [hU, measure_union hd measurableSet_Ioc, measure_union hd measurableSet_Ioc,
        hlow M le_rfl, hband a]
  rw [inter_comm, ← hm1 S hS, hext, hm2def, withDensity_apply _ hS]

end Brownian

end Reflection

/-! ## The mesh kernels as densities -/

section MeshDensity

variable {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
include hB hm

/-- Skeleton identification on the mesh: the law of `u + X_τ` on survival has density `lamKerN` of
the mesh. -/
theorem measure_survSet_inter {T : ℝ} (hT : 0 < T) {τ : ℝ≥0} (hτ : (τ : ℝ) = 2 * T)
    (M u : ℝ) (n : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    P (survSet B τ M u n ∩ endVal B τ u ⁻¹' S) =
      ∫⁻ v in S, ENNReal.ofReal (lamKerN (M, meshGap T n) (meshTail M T n) (u, v)) := by
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
  have hg := meshGap_pos hT n
  have hh : ((τ / 2 ^ n : ℝ≥0) : ℝ) = 2 * meshGap T n := by
    rw [NNReal.coe_div, NNReal.coe_pow, hτ, meshGap]
    push_cast
    ring
  have hB1 := measure_skelSet hg hh M k hB hm u hS
  have htail : meshTail M T n = List.replicate k (M, meshGap T n) := by
    rw [meshTail, hk, Nat.add_sub_cancel]
  have hend : ((k + 1 : ℕ) : ℝ≥0) * (τ / 2 ^ n) = τ := by
    rw [← hk]; exact gridT_pow τ n
  rw [htail, ← hB1]
  congr 1
  ext ω
  simp only [survSet, skelSet, endVal, mem_inter_iff, mem_preimage, mem_ofPred_eq, hend, hk,
    gridT]

/-- The law of `u + X_τ` off survival has density `meshHitKer M T n (u, ·)`. -/
theorem measure_compl_survSet_inter {T : ℝ} (hT : 0 < T) {τ : ℝ≥0} (hτ : (τ : ℝ) = 2 * T)
    (M u : ℝ) (n : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    P ((survSet B τ M u n)ᶜ ∩ endVal B τ u ⁻¹' S) =
      ∫⁻ v in S, ENNReal.ofReal (meshHitKer M T n (u, v)) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hme := measurable_endVal hm τ u
  have hE : MeasurableSet (endVal B τ u ⁻¹' S) := hme hS
  have hlaw : P (endVal B τ u ⁻¹' S) = ∫⁻ v in S, ENNReal.ofReal (heatKernel T (u - v)) := by
    have h0 := map_add_sub_eq hB hm (zero_le : (0 : ℝ≥0) ≤ τ) u
    rw [tsub_zero, gaussianReal_eq_withDensity_heatKernel hT hτ] at h0
    rw [← Measure.map_apply hme hS]
    change (P.map fun ω => u + (B τ ω - B 0 ω)) S = _
    rw [h0, withDensity_apply _ hS]
  have hsurv := measure_survSet_inter hB hm hT hτ M u n hS
  have hpos : ∀ y ∈ meshTail M T n, 0 < y.2 := meshTail_pos hT n
  obtain ⟨hLm, hL0, hL1⟩ := lamKerN_props (meshTail M T n) (M, meshGap T n)
    (meshGap_pos hT n) hpos
  have hset : (survSet B τ M u n)ᶜ ∩ endVal B τ u ⁻¹' S =
      endVal B τ u ⁻¹' S \ (survSet B τ M u n ∩ endVal B τ u ⁻¹' S) := by
    ext ω; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
  rw [hset, measure_sdiff inter_subset_right
    ((measurableSet_survSet hm τ M u n).inter hE).nullMeasurableSet (measure_ne_top _ _),
    hlaw, hsurv]
  have hfin : ∫⁻ v in S, ENNReal.ofReal (lamKerN (M, meshGap T n) (meshTail M T n) (u, v))
      ≠ ∞ := by rw [← hsurv]; exact measure_ne_top _ _
  have hgm : Measurable fun v => ENNReal.ofReal
      (lamKerN (M, meshGap T n) (meshTail M T n) (u, v)) :=
    (ENNReal.measurable_ofReal.comp hLm).comp measurable_prodMk_left
  rw [← lintegral_sub (f := fun v => ENNReal.ofReal (heatKernel T (u - v))) hgm hfin
    (Eventually.of_forall fun v => ENNReal.ofReal_le_ofReal (by
      have := hL1 (u, v)
      rwa [gapSum_meshTail] at this))]
  refine lintegral_congr fun v => ?_
  rw [← ENNReal.ofReal_sub _ (hL0 _)]
  simp only [meshHitKer, hitKerN, gapSum_meshTail]

end MeshDensity

/-! ## The kernel fact -/

theorem lamKerN_eq_zero_of_lt (L : List (ℝ × ℝ)) (e : ℝ × ℝ) {p : ℝ × ℝ} (h : e.1 < p.1) :
    lamKerN e L p = 0 := by
  have hI : (Iic e.1).indicator (fun _ => (1 : ℝ)) p.1 = 0 :=
    Set.indicator_of_notMem (not_le.2 h) _
  cases L with
  | nil => simp only [lamKerN, lamKer1, hI, zero_mul]
  | cons y L => simp only [lamKerN, hI, zero_mul]

/-- Above the level the mesh hitting kernel is exactly `Q_{M,T}` (`= p_T`). -/
theorem meshHitKer_eq_qMT_of_lt (M T : ℝ) (n : ℕ) {u : ℝ} (hu : M < u) (v : ℝ) :
    meshHitKer M T n (u, v) = AiryConj.qMT M T u v := by
  rw [meshHitKer, hitKerN, gapSum_meshTail, lamKerN_eq_zero_of_lt _ _ hu, sub_zero,
    AiryConj.qMT_eq_free (fun h => absurd h.1 (not_le.2 hu))]

section Kernel

variable {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
include hB hm

/-- (K1) at a start below the level. -/
theorem ae_meshHitKer_le_qMT {T : ℝ} (hT : 0 < T) {τ : ℝ≥0} (hτ : (τ : ℝ) = 2 * T) {M u : ℝ}
    (hu : u < M) (n : ℕ) : ∀ᵐ v, meshHitKer M T n (u, v) ≤ AiryConj.qMT M T u v := by
  have h := ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ := volume)
    (f := fun v => ENNReal.ofReal (meshHitKer M T n (u, v)))
    (g := fun v => ENNReal.ofReal (AiryConj.qMT M T u v))
    (ENNReal.measurable_ofReal.comp ((measurable_meshHitKer hT n).comp measurable_prodMk_left))
    (fun S hS _ => by
      rw [← measure_compl_survSet_inter hB.toIsPreBrownianReal hm hT hτ M u n hS,
        ← measure_crossSet_inter hB hm hT hτ hu hS]
      exact measure_mono (inter_subset_inter_left _
        (subset_iUnion (fun n => (survSet B τ M u n)ᶜ) n)))
  filter_upwards [h] with v hv
  exact (ENNReal.ofReal_le_ofReal_iff (qMT_nonneg hT u v)).1 hv

/-- (K2) at a start below the level. -/
theorem ae_tendsto_meshHitKer {T : ℝ} (hT : 0 < T) {τ : ℝ≥0} (hτ : (τ : ℝ) = 2 * T) {M u : ℝ}
    (hu : u < M) :
    ∀ᵐ v, Tendsto (fun n => meshHitKer M T n (u, v)) atTop (𝓝 (AiryConj.qMT M T u v)) := by
  have hP := hB.toIsPreBrownianReal
  have := hP.isGaussianProcess.isProbabilityMeasure
  have hfm : ∀ n, Measurable fun v => ENNReal.ofReal (meshHitKer M T n (u, v)) := fun n =>
    ENNReal.measurable_ofReal.comp ((measurable_meshHitKer hT n).comp measurable_prodMk_left)
  have hqm : Measurable fun v => ENNReal.ofReal (AiryConj.qMT M T u v) :=
    ENNReal.measurable_ofReal.comp ((AiryConj.measurable_qMT M T).comp measurable_prodMk_left)
  -- monotone in `n` a.e.
  have hstep : ∀ n, (fun v => ENNReal.ofReal (meshHitKer M T n (u, v))) ≤ᵐ[volume]
      fun v => ENNReal.ofReal (meshHitKer M T (n + 1) (u, v)) := fun n =>
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite (hfm n) (fun S hS _ => by
      rw [← measure_compl_survSet_inter hP hm hT hτ M u n hS,
        ← measure_compl_survSet_inter hP hm hT hτ M u (n + 1) hS]
      exact measure_mono (inter_subset_inter_left _
        (compl_subset_compl.2 (survSet_succ_subset B τ M u n))))
  have hmono : ∀ᵐ v, Monotone fun n => ENNReal.ofReal (meshHitKer M T n (u, v)) := by
    filter_upwards [ae_all_iff.2 hstep] with v hv
    exact monotone_nat_of_le_succ hv
  have hle : ∀ᵐ v, ∀ n, ENNReal.ofReal (meshHitKer M T n (u, v)) ≤
      ENNReal.ofReal (AiryConj.qMT M T u v) := by
    refine ae_all_iff.2 fun n => ?_
    filter_upwards [ae_meshHitKer_le_qMT hB hm hT hτ hu n] with v hv
    exact ENNReal.ofReal_le_ofReal hv
  -- total masses
  have hmass : ∀ n, ∫⁻ v, ENNReal.ofReal (meshHitKer M T n (u, v)) =
      P ((survSet B τ M u n)ᶜ ∩ endVal B τ u ⁻¹' univ) := fun n => by
    rw [measure_compl_survSet_inter hP hm hT hτ M u n MeasurableSet.univ, Measure.restrict_univ]
  have hsup : ∫⁻ v, ⨆ n, ENNReal.ofReal (meshHitKer M T n (u, v)) =
      ∫⁻ v, ENNReal.ofReal (AiryConj.qMT M T u v) := by
    rw [lintegral_iSup' (fun n => (hfm n).aemeasurable) hmono]
    simp_rw [hmass]
    have hmon : Monotone fun n => (survSet B τ M u n)ᶜ ∩ endVal B τ u ⁻¹' univ :=
      fun a b hab => inter_subset_inter_left _ (compl_survSet_mono B τ M u hab)
    have hcs : crossSet B τ M u = ⋃ n, (survSet B τ M u n)ᶜ := rfl
    rw [← hmon.measure_iUnion, ← iUnion_inter, ← hcs,
      measure_crossSet_inter hB hm hT hτ hu MeasurableSet.univ, Measure.restrict_univ]
  have hFle : (fun v => ⨆ n, ENNReal.ofReal (meshHitKer M T n (u, v))) ≤ᵐ[volume]
      fun v => ENNReal.ofReal (AiryConj.qMT M T u v) := by
    filter_upwards [hle] with v hv
    exact iSup_le hv
  have hFfin : ∫⁻ v, ⨆ n, ENNReal.ofReal (meshHitKer M T n (u, v)) ≠ ∞ := by
    rw [hsup, ← Measure.restrict_univ (μ := volume),
      ← measure_crossSet_inter hB hm hT hτ hu MeasurableSet.univ]
    exact measure_ne_top _ _
  have hEq := ae_eq_of_ae_le_of_lintegral_le hFle hFfin hqm.aemeasurable hsup.ge
  filter_upwards [hEq, hmono] with v hv hmv
  have h1 : Tendsto (fun n => ENNReal.ofReal (meshHitKer M T n (u, v))) atTop
      (𝓝 (ENNReal.ofReal (AiryConj.qMT M T u v))) := by
    rw [← hv]; exact tendsto_atTop_iSup hmv
  have h2 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h1
  have e1 : (fun n => meshHitKer M T n (u, v)) =
      (ENNReal.toReal ∘ fun n => ENNReal.ofReal (meshHitKer M T n (u, v))) := by
    funext n
    simp only [Function.comp_apply, ENNReal.toReal_ofReal (meshHitKer_nonneg hT n _)]
  rw [e1, ← ENNReal.toReal_ofReal (qMT_nonneg hT u v)]
  exact h2

/-- **The kernel fact.** For a Brownian motion with measurable coordinates,
the dyadic hitting kernels satisfy (K1) and (K2) for every level `M` and every `T > 0`. -/
theorem meshHittingLimit_of_isBrownianReal (M : ℝ) {T : ℝ} (hT : 0 < T) :
    MeshHittingLimit M T := by
  set τ : ℝ≥0 := ⟨2 * T, by positivity⟩ with hτdef
  have hτ : (τ : ℝ) = 2 * T := rfl
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ M := by
    rw [ae_iff]
    simp
  refine ⟨fun n => ?_, ?_⟩
  · have hs : MeasurableSet {p : ℝ × ℝ | meshHitKer M T n p ≤ AiryConj.qMT M T p.1 p.2} :=
      measurableSet_le (measurable_meshHitKer hT n) (AiryConj.measurable_qMT M T)
    change ∀ᵐ p ∂(volume.prod volume), p ∈ {p : ℝ × ℝ | meshHitKer M T n p ≤
      AiryConj.qMT M T p.1 p.2}
    rw [Measure.ae_prod_mem_iff_ae_ae_mem hs]
    filter_upwards [hne] with u hu
    rcases lt_or_gt_of_ne hu with h | h
    · exact ae_meshHitKer_le_qMT hB hm hT hτ h n
    · exact Eventually.of_forall fun v => (meshHitKer_eq_qMT_of_lt M T n h v).le
  · have hs : MeasurableSet {p : ℝ × ℝ | Tendsto (fun n => meshHitKer M T n p) atTop
        (𝓝 (AiryConj.qMT M T p.1 p.2))} := by
      have e : {p : ℝ × ℝ | Tendsto (fun n => meshHitKer M T n p) atTop
          (𝓝 (AiryConj.qMT M T p.1 p.2))} = {p : ℝ × ℝ | Tendsto (fun n =>
            meshHitKer M T n p - AiryConj.qMT M T p.1 p.2) atTop (𝓝 0)} := by
        ext p; simp only [mem_ofPred_eq, tendsto_sub_nhds_zero_iff]
      rw [e]
      exact measurableSet_tendsto (𝓝 0) fun n =>
        (measurable_meshHitKer hT n).sub (AiryConj.measurable_qMT M T)
    change ∀ᵐ p ∂(volume.prod volume), p ∈ {p : ℝ × ℝ | Tendsto (fun n => meshHitKer M T n p)
      atTop (𝓝 (AiryConj.qMT M T p.1 p.2))}
    rw [Measure.ae_prod_mem_iff_ae_ae_mem hs]
    filter_upwards [hne] with u hu
    rcases lt_or_gt_of_ne hu with h | h
    · exact ae_tendsto_meshHitKer hB hm hT hτ h
    · refine Eventually.of_forall fun v => ?_
      simp only [meshHitKer_eq_qMT_of_lt M T _ h v]
      exact tendsto_const_nhds

end Kernel

end AiryFdd
