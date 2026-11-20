/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.MesoscopicSpec

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace Airy1Gumbel

/-!
# Mesoscopic estimate: the grid-pair bound and the one-point tail

Proves two of the target statements of `MesoscopicSpec.lean` (statements verbatim):

* `grid_pair_bound` — the Lean form of the Newman step in the paper's mesoscopic
  estimate, combined with the covariance shift used in the paper's covariance bound:
  `ℙ(A x > v, A y > v) ≤ ℙ(A 0 > v - 1)² + Cov(A 0, A (y - x))`.
  The indicator `𝟙{t > v}` is replaced by the clamp `clampInd v`, which is
  monotone, `1`-Lipschitz and satisfies `𝟙{t > v} ≤ clampInd v t ≤ 𝟙{t > v - 1}`;
  then `covariance_eq_sub` splits `𝔼[g(A x) g(A y)]` into the product of means and
  the covariance, the means are bounded by `ℙ(A 0 > v - 1)` (`X.stat`), and the
  covariance by `Cov(A x, A y) = Cov(A 0, A (y - x))` (`newman_pair` with Lipschitz
  constants `1, 1`, then `PairStationary.cov_shift`).
* `Airy1ContinuousMax.one_point_le_block`:
  `ℙ(A 0 > w) ≤ ℙ(Y₀ > w)`, since `0 ∈ [0, 1]` and, on the full-measure event of
  continuous paths with `Y_eq`, `A 0 ≤ Y 0` (`le_block_sup`).
-/

/-! ## The clamped indicator `clampInd v` -/

section ClampInd

/-- `clampInd v` is monotone. -/
theorem clampInd_monotone (v : ℝ) : Monotone (clampInd v) := by
  intro a b hab
  unfold clampInd
  exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

/-- `clampInd v` is `1`-Lipschitz (composition of a translation with the clamps
`min 1 ·` and `max 0 ·`). -/
theorem clampInd_lipschitzWith (v : ℝ) : LipschitzWith 1 (clampInd v) := by
  have h : LipschitzWith 1 fun t : ℝ => t - (v - 1) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_sub_cancel_right]
  exact (h.const_min 1).const_max 0

/-- `clampInd v` is measurable (it is continuous). -/
theorem clampInd_measurable (v : ℝ) : Measurable (clampInd v) :=
  (clampInd_lipschitzWith v).continuous.measurable

/-- `clampInd v` is nonnegative. -/
theorem clampInd_nonneg (v t : ℝ) : 0 ≤ clampInd v t := le_max_left _ _

/-- `clampInd v` is at most `1`. -/
theorem clampInd_le_one (v t : ℝ) : clampInd v t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- `clampInd v` takes values in `[0, 1]`. -/
theorem clampInd_mem_Icc (v t : ℝ) : clampInd v t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨clampInd_nonneg v t, clampInd_le_one v t⟩

/-- `clampInd v` is bounded in absolute value by `1`. -/
theorem abs_clampInd_le_one (v t : ℝ) : |clampInd v t| ≤ 1 := by
  rw [abs_of_nonneg (clampInd_nonneg v t)]
  exact clampInd_le_one v t

/-- `clampInd v t = 1` when `t > v`. -/
theorem clampInd_eq_one_of_lt {v t : ℝ} (h : v < t) : clampInd v t = 1 := by
  unfold clampInd
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

/-- `clampInd v t = 0` when `t ≤ v - 1`. -/
theorem clampInd_eq_zero_of_le {v t : ℝ} (h : t ≤ v - 1) : clampInd v t = 0 := by
  unfold clampInd
  exact max_eq_left (min_le_of_right_le (by linarith))

/-- Lower half of the indicator sandwich: `𝟙{t > v} ≤ clampInd v t`. -/
theorem indicator_lt_le_clampInd (v t : ℝ) :
    Set.indicator (Set.Ioi v) (1 : ℝ → ℝ) t ≤ clampInd v t := by
  by_cases h : t ∈ Set.Ioi v
  · rw [Set.indicator_of_mem h, clampInd_eq_one_of_lt h, Pi.one_apply]
  · rw [Set.indicator_of_notMem h]
    exact clampInd_nonneg v t

/-- Upper half of the indicator sandwich: `clampInd v t ≤ 𝟙{t > v - 1}`. -/
theorem clampInd_le_indicator (v t : ℝ) :
    clampInd v t ≤ Set.indicator (Set.Ioi (v - 1)) (1 : ℝ → ℝ) t := by
  by_cases h : t ∈ Set.Ioi (v - 1)
  · rw [Set.indicator_of_mem h, Pi.one_apply]
    exact clampInd_le_one v t
  · rw [Set.indicator_of_notMem h, clampInd_eq_zero_of_le (not_lt.mp h)]

end ClampInd

/-! ## The grid-pair bound -/

section GridPair

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- One-point stationarity of tail probabilities: `ℙ(A x > w) = ℙ(A 0 > w)`
(`X.stat`). -/
theorem StationaryRealProcess.measureReal_gt_eq (X : StationaryRealProcess P)
    (x w : ℝ) : P.real {ω | X.A x ω > w} = P.real {ω | X.A 0 ω > w} := by
  have hx := X.stat 0 x
  rw [zero_add] at hx
  have e : ∀ y, P.real {ω | X.A y ω > w} = (P.map (X.A y)).real (Set.Ioi w) := fun y =>
    (map_measureReal_apply (X.A_meas y) measurableSet_Ioi).symm
  rw [e x, e 0, hx]

/-- The mean of the clamp of `A x` is at most `ℙ(A 0 > v - 1)`
(upper half of the indicator sandwich, then `X.stat`). -/
theorem StationaryRealProcess.integral_clampInd_le (X : StationaryRealProcess P)
    (x v : ℝ) :
    ∫ ω, (clampInd v ∘ X.A x) ω ∂P ≤ P.real {ω | X.A 0 ω > v - 1} := by
  have hs : MeasurableSet {ω | X.A x ω > v - 1} := measurableSet_lt measurable_const (X.A_meas x)
  have hmeas : Measurable (clampInd v ∘ X.A x) := (clampInd_measurable v).comp (X.A_meas x)
  calc ∫ ω, (clampInd v ∘ X.A x) ω ∂P
      ≤ ∫ ω, Set.indicator {ω | X.A x ω > v - 1} (1 : Ω → ℝ) ω ∂P := by
        refine integral_mono (Integrable.of_bound hmeas.aestronglyMeasurable 1
          (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs]; exact abs_clampInd_le_one v _))
          ((integrable_const (1 : ℝ)).indicator hs) fun ω => ?_
        have := clampInd_le_indicator v (X.A x ω)
        by_cases h : ω ∈ {ω | X.A x ω > v - 1}
        · rw [Set.indicator_of_mem h]
          rw [Set.indicator_of_mem (show X.A x ω ∈ Set.Ioi (v - 1) from h)] at this
          exact this
        · rw [Set.indicator_of_notMem h]
          rw [Set.indicator_of_notMem (show X.A x ω ∉ Set.Ioi (v - 1) from h)] at this
          exact this
    _ = P.real {ω | X.A x ω > v - 1} := integral_indicator_one hs
    _ = P.real {ω | X.A 0 ω > v - 1} := X.measureReal_gt_eq x (v - 1)

/-- **Grid-pair bound.** For an associated process with
`L²` marginals and stationary two-point marginals,
`ℙ(A x > v, A y > v) ≤ ℙ(A 0 > v - 1)² + Cov(A 0, A (y - x))`.

Paper anchors: the Newman step of the paper's mesoscopic estimate, here with the 1-Lipschitz clamp
`clampInd v` in place of the smoothed indicator (so
the constant in front of the covariance is `1 · 1`), and the covariance shift feeding
the paper's covariance bound. Proof: `𝟙{A x > v, A y > v} ≤ g(A x) g(A y)`
for `g = clampInd v`; `covariance_eq_sub` gives
`𝔼[g(A x) g(A y)] = 𝔼g(A x) 𝔼g(A y) + Cov(g(A x), g(A y))`; each mean is
`≤ ℙ(A 0 > v - 1)` (`integral_indicator_one`, `X.stat`); the covariance is
`≤ Cov(A x, A y)` (`newman_pair`, Lipschitz constants `1, 1`) `= Cov(A 0, A (y - x))`
(`PairStationary.cov_shift`). -/
theorem grid_pair_bound {X : StationaryRealProcess P} (As : ProcessAssociated X)
    (hL2 : ∀ x, MemLp (X.A x) 2 P) (PS : PairStationary X) :
    ∀ x y v : ℝ,
      P.real {ω | X.A x ω > v ∧ X.A y ω > v} ≤
        P.real {ω | X.A 0 ω > v - 1} ^ 2 + covariance (X.A 0) (X.A (y - x)) P := by
  intro x y v
  set g : ℝ → ℝ := clampInd v with hg
  set Gx : Ω → ℝ := g ∘ X.A x with hGx
  set Gy : Ω → ℝ := g ∘ X.A y with hGy
  set p : ℝ := P.real {ω | X.A 0 ω > v - 1} with hp
  have hGxm : Measurable Gx := (clampInd_measurable v).comp (X.A_meas x)
  have hGym : Measurable Gy := (clampInd_measurable v).comp (X.A_meas y)
  have hGxL2 : MemLp Gx 2 P :=
    memLp_of_bounded (a := 0) (b := 1) (Eventually.of_forall fun ω => clampInd_mem_Icc v _)
      hGxm.aestronglyMeasurable 2
  have hGyL2 : MemLp Gy 2 P :=
    memLp_of_bounded (a := 0) (b := 1) (Eventually.of_forall fun ω => clampInd_mem_Icc v _)
      hGym.aestronglyMeasurable 2
  -- Step 1: the joint exceedance probability is at most `𝔼[Gx Gy]`.
  have hS : MeasurableSet {ω | X.A x ω > v ∧ X.A y ω > v} :=
    (measurableSet_lt measurable_const (X.A_meas x)).inter
      (measurableSet_lt measurable_const (X.A_meas y))
  have hprod_int : Integrable (Gx * Gy) P := by
    refine Integrable.of_bound (hGxm.mul hGym).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    calc |Gx ω| * |Gy ω| ≤ 1 * 1 :=
          mul_le_mul (abs_clampInd_le_one v _) (abs_clampInd_le_one v _) (abs_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  have step1 : P.real {ω | X.A x ω > v ∧ X.A y ω > v} ≤ ∫ ω, (Gx * Gy) ω ∂P := by
    rw [← integral_indicator_one hS]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hS) hprod_int fun ω => ?_
    by_cases h : ω ∈ {ω | X.A x ω > v ∧ X.A y ω > v}
    · rw [Set.indicator_of_mem h, Pi.one_apply, Pi.mul_apply]
      have h1 : Gx ω = 1 := clampInd_eq_one_of_lt h.1
      have h2 : Gy ω = 1 := clampInd_eq_one_of_lt h.2
      rw [h1, h2, mul_one]
    · rw [Set.indicator_of_notMem h, Pi.mul_apply]
      exact mul_nonneg (clampInd_nonneg v _) (clampInd_nonneg v _)
  -- Step 2: split `𝔼[Gx Gy]` into the product of means and the covariance.
  have step2 : ∫ ω, (Gx * Gy) ω ∂P =
      (∫ ω, Gx ω ∂P) * (∫ ω, Gy ω ∂P) + covariance Gx Gy P := by
    rw [covariance_eq_sub hGxL2 hGyL2]
    ring
  -- Step 3: each mean is in `[0, p]`.
  have hmx0 : 0 ≤ ∫ ω, Gx ω ∂P :=
    integral_nonneg fun ω => clampInd_nonneg v _
  have hmy0 : 0 ≤ ∫ ω, Gy ω ∂P :=
    integral_nonneg fun ω => clampInd_nonneg v _
  have hmx : ∫ ω, Gx ω ∂P ≤ p := X.integral_clampInd_le x v
  have hmy : ∫ ω, Gy ω ∂P ≤ p := X.integral_clampInd_le y v
  have step3 : (∫ ω, Gx ω ∂P) * (∫ ω, Gy ω ∂P) ≤ p ^ 2 := by
    rw [sq]
    exact mul_le_mul hmx hmy hmy0 (hmx0.trans hmx)
  -- Step 4: Newman with Lipschitz constants `1, 1`, then the covariance shift.
  have step4 : covariance Gx Gy P ≤ covariance (X.A 0) (X.A (y - x)) P := by
    have hN := newman_pair As hL2 x y (clampInd_lipschitzWith v) (clampInd_lipschitzWith v)
    have hshift := PS.cov_shift x (y - x)
    rw [add_sub_cancel] at hshift
    simp only [NNReal.coe_one, one_mul] at hN
    rw [← hshift]
    exact (le_abs_self _).trans hN
  calc P.real {ω | X.A x ω > v ∧ X.A y ω > v}
      ≤ ∫ ω, (Gx * Gy) ω ∂P := step1
    _ = (∫ ω, Gx ω ∂P) * (∫ ω, Gy ω ∂P) + covariance Gx Gy P := step2
    _ ≤ p ^ 2 + covariance (X.A 0) (X.A (y - x)) P := add_le_add step3 step4

end GridPair

/-! ## The one-point tail below the block tail -/

section OnePoint

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- On the full-measure event of continuous paths with `Y_eq`, `A 0 ≤ Y 0`
(`0 ∈ [0, 1]`, `le_block_sup`). -/
theorem Airy1ContinuousMax.ae_A_zero_le_Y_zero (C : Airy1ContinuousMax P) :
    ∀ᵐ ω ∂P, C.A 0 ω ≤ C.Y 0 ω := by
  filter_upwards [C.path_cont, C.Y_eq] with ω hcont hY
  have h0 : (0 : ℝ) ∈ Set.Icc ((0 : ℕ) : ℝ) ((0 : ℕ) + 1) := by
    rw [Nat.cast_zero, zero_add]
    exact Set.left_mem_Icc.mpr zero_le_one
  exact C.le_block_sup hcont hY 0 h0

/-- **One-point tail below the block tail** (replacing the paper's one-point tail
bound): `ℙ(A 0 > w) ≤ ℙ(Y₀ > w)`, because a.s. `A 0 ≤ Y 0` (`path_cont`, `Y_eq`,
`le_block_sup` at `0 ∈ [0, 1]`); the sets are compared a.e. (`measure_mono_ae`),
so no measurability of either event is needed. -/
theorem Airy1ContinuousMax.one_point_le_block (C : Airy1ContinuousMax P) :
    ∀ w : ℝ, P.real {ω | C.A 0 ω > w} ≤ P.real {ω | C.Y 0 ω > w} := by
  intro w
  have hsub : {ω | C.A 0 ω > w} ≤ᵐ[P] {ω | C.Y 0 ω > w} := by
    filter_upwards [C.ae_A_zero_le_Y_zero] with ω hω hA
    exact lt_of_lt_of_le hA hω
  exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)

end OnePoint

end Airy1Gumbel
