/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoTime.TwoTimeNonvanishing

/-! # Operator-level nonvanishing of the two-time blocks `Q` and `D`

`TwoTime/TwoTimeNonvanishing.lean` shows that the kernels `qKer`, `dKer` are nonzero at some
point past both cuts. A kernel operator only sees its kernel up to null sets, so this file
upgrades that nonvanishing argument to the
operators: `qOp x₁ x₂ hd ≠ 0` and `dOp x₁ x₂ hd ≠ 0` for every `d > 0` and all levels.

## Route

1. **Testing against interval indicators** (`ae_forall_rat_setIntegral_Ioo_eq_zero`, general
   `L²` kernels on `ℝ`): if `kernelOperator hK = 0` then, for a.e. `u`, every rational interval
   integral `∫_{(p, q)} K(u, m) dm` vanishes (apply the operator to `1_{(p, q)} ∈ L²`; countably
   many intervals).
2. **Continuity of the inner integral in `m`** (`continuousOn_blkInner`): for `b ≥ x₁` the map
   `m ↦ ∫ G(u + y) 1_{y ≤ x₁} p_d(y − m) dy` is continuous on `[b, ∞)`, by dominated convergence
   with the dominant at `m = b` (for `y ≤ x₁ ≤ b ≤ m`, `|y − m| ≥ |y − b|`, so
   `p_d(y − m) ≤ p_d(y − b)`).
3. **Interval integrals detect continuous functions** (`eq_zero_of_forall_rat_setIntegral_Ioo`).
4. Combining with the Laplace nonvanishing argument `exists_blkInner_ne_zero`, a positive-measure
set of `u`
   (all `u > max c x`) contradicts step 1 (`kernelOperator_blkKer_ne_zero`).
-/

namespace AiryFdd

open MeasureTheory Real Set Filter Topology
open HilbertSchmidt

/-! ## 1. A vanishing kernel operator kills all rational interval integrals of a.e. section -/

/-- If `T_K = 0` on `L²(ℝ)`, then for every `p, q` and a.e. `u`, `∫_{(p, q)} K(u, m) dm = 0`. -/
theorem ae_setIntegral_Ioo_eq_zero_of_kernelOperator_eq_zero {K : ℝ × ℝ → ℝ}
    (hK : MemLp K 2 (volume.prod volume)) (h0 : kernelOperator hK = 0) (p q : ℝ) :
    ∀ᵐ u : ℝ, (∫ m in Ioo p q, K (u, m)) = 0 := by
  set f : Lp ℝ 2 (volume : Measure ℝ) :=
    indicatorConstLp 2 measurableSet_Ioo (measure_Ioo_lt_top (a := p) (b := q)).ne (1 : ℝ)
  have hz : kernelOperator hK f = 0 := by rw [h0]; rfl
  filter_upwards [kernelOperator_apply_ae hK f, Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)]
    with u hu hzero
  have h1 : (kernelOperator hK f) u = 0 := by rw [hz]; exact hzero
  rw [hu] at h1
  unfold kernelIntegralFun at h1
  rw [← h1, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioo (a := p) (b := q))
    (hμs := (measure_Ioo_lt_top (a := p) (b := q)).ne) (c := (1 : ℝ))] with m hm
  rw [hm]
  by_cases hmem : m ∈ Ioo p q
  · simp [hmem]
  · simp [hmem]

/-- Countable version: for a.e. `u`, all rational interval integrals of `K(u, ·)` vanish. -/
theorem ae_forall_rat_setIntegral_Ioo_eq_zero {K : ℝ × ℝ → ℝ}
    (hK : MemLp K 2 (volume.prod volume)) (h0 : kernelOperator hK = 0) :
    ∀ᵐ u : ℝ, ∀ r : ℚ × ℚ, (∫ m in Ioo (r.1 : ℝ) r.2, K (u, m)) = 0 :=
  ae_all_iff.2 fun _ => ae_setIntegral_Ioo_eq_zero_of_kernelOperator_eq_zero hK h0 _ _

/-! ## 2. Rational interval integrals detect continuous functions -/

/-- A function continuous on `(a, ∞)` whose integrals over all rational intervals
`(p, q)` with `a < p` vanish is zero on `(a, ∞)`. -/
theorem eq_zero_of_forall_rat_setIntegral_Ioo {f : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousOn f (Ioi a))
    (h : ∀ p q : ℚ, a < p → (∫ m in Ioo (p : ℝ) q, f m) = 0) {m₀ : ℝ} (hm₀ : a < m₀) :
    f m₀ = 0 := by
  by_contra hne
  set g : ℝ → ℝ := fun m => f m₀ * f m with hg
  have hgc : ContinuousOn g (Ioi a) := continuousOn_const.mul hf
  have hg0 : 0 < g m₀ := mul_self_pos.2 hne
  have hev : ∀ᶠ m in 𝓝 m₀, 0 < g m ∧ a < m :=
    ((hgc.continuousAt (isOpen_Ioi.mem_nhds hm₀)).eventually (lt_mem_nhds hg0)).and
      (lt_mem_nhds hm₀)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show m₀ - ε < m₀ by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show m₀ < m₀ + ε by linarith)
  have hin : ∀ m, (p : ℝ) ≤ m → m ≤ q → 0 < g m ∧ a < m := by
    intro m h1 h2
    apply hball
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hap : a < p := (hin p le_rfl (by linarith)).2
  have hpq : (p : ℝ) < q := by linarith
  have hint : IntervalIntegrable g volume p q := by
    apply ContinuousOn.intervalIntegrable
    apply hgc.mono
    intro m hm
    rw [uIcc_of_le hpq.le] at hm
    exact (hin m hm.1 hm.2).2
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on hint
    (fun m hm => (hin m hm.1.le hm.2.le).1) hpq
  rw [intervalIntegral.integral_of_le hpq.le, integral_Ioc_eq_integral_Ioo] at hpos
  have hzero : (∫ m in Ioo (p : ℝ) q, g m) = 0 := by
    simp only [hg]
    rw [integral_const_mul, h p q hap, mul_zero]
  linarith

/-! ## 3. Continuity of the inner integral in `m` -/

/-- Monotonicity of the heat kernel on the left of the cut: for `y ≤ b ≤ m`,
`p_d(y − m) ≤ p_d(y − b)`. -/
theorem heatKernel_le_of_le_of_le {d : ℝ} (hd : 0 < d) {y b m : ℝ} (hyb : y ≤ b)
    (hbm : b ≤ m) : heatKernel d (y - m) ≤ heatKernel d (y - b) := by
  unfold heatKernel
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
  apply Real.exp_le_exp.2
  have h4 : 0 < 4 * d := by linarith
  rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff_of_pos_right h4]
  nlinarith

/-- **Continuity of the inner integral**: for continuous `G` with `|G(t)| ≤ C e^{−βt}` and
`b ≥ x₁`, the map `m ↦ ∫ G(u + y) 1_{y ≤ x₁} p_d(y − m) dy` is continuous on `[b, ∞)`. -/
theorem continuousOn_blkInner {G : ℝ → ℝ} (hG : Continuous G) {C β : ℝ}
    (hGb : ∀ t, |G t| ≤ C * Real.exp (-β * t)) {d : ℝ} (hd : 0 < d) (u x₁ : ℝ) {b : ℝ}
    (hb : x₁ ≤ b) :
    ContinuousOn (fun m => ∫ y : ℝ, G (u + y) * ((Iic x₁).indicator (fun _ => (1 : ℝ)) y
        * heatKernel d (y - m))) (Ici b) := by
  refine continuousOn_of_dominated (bound := fun y => ‖G (u + y)
      * ((Iic x₁).indicator (fun _ => (1 : ℝ)) y * heatKernel d (y - b))‖)
    (fun m _ => (integrable_comp_add_mul_indicator_heatKernel hG.measurable hGb hd u m
      measurableSet_Iic).aestronglyMeasurable) (fun m hm => Eventually.of_forall fun y => ?_)
    (integrable_comp_add_mul_indicator_heatKernel hG.measurable hGb hd u b
      measurableSet_Iic).norm
    (Eventually.of_forall fun y => ?_)
  · have hm' : b ≤ m := hm
    by_cases hy : y ∈ Iic x₁
    · have hy' : y ≤ x₁ := hy
      simp only [Set.indicator_of_mem hy, one_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (heatKernel_nonneg hd _)]
      exact mul_le_mul_of_nonneg_left (heatKernel_le_of_le_of_le hd (hy'.trans hb) hm')
        (abs_nonneg _)
    · simp [Set.indicator_of_notMem hy]
  · exact (continuous_const.mul (continuous_const.mul
      ((continuous_heatKernel d).comp (continuous_const.sub continuous_id)))).continuousOn

/-! ## 4. The nonvanishing criterion for `blkKer` operators -/

/-- **Operator-level nonvanishing for a general second-column block**: let `G` be continuous with
`|G(t)| ≤ C e^{−βt}`, `d > 0`, and suppose `G(u + x₁) ≠ 0` for all `u > c`.  Then the kernel
operator of `blkKer x x₁ x₂ d G` (for any `L²` proof) is not the zero operator. -/
theorem kernelOperator_blkKer_ne_zero {G : ℝ → ℝ} (hG : Continuous G) {C β : ℝ}
    (hGb : ∀ t, |G t| ≤ C * Real.exp (-β * t)) {x x₁ x₂ d : ℝ} (hd : 0 < d)
    (hK : MemLp (blkKer x x₁ x₂ d G) 2 (volume.prod volume)) {c : ℝ}
    (hc : ∀ u, c < u → G (u + x₁) ≠ 0) :
    kernelOperator hK ≠ 0 := by
  intro h0
  set a := max x₁ x₂
  set c' := max c x
  have hae := ae_forall_rat_setIntegral_Ioo_eq_zero hK h0
  have hae' : ∀ᵐ u ∂(volume.restrict (Ioi c')), u ∈ Ioi c' ∧
      ∀ r : ℚ × ℚ, (∫ m in Ioo (r.1 : ℝ) r.2, blkKer x x₁ x₂ d G (u, m)) = 0 :=
    (ae_restrict_mem measurableSet_Ioi).and (ae_restrict_of_ae hae)
  have : (ae (volume.restrict (Ioi c'))).NeBot :=
    ae_restrict_neBot.2 (by simp [Real.volume_Ioi])
  obtain ⟨u, hu, hr⟩ := hae'.exists
  have hux : x < u := lt_of_le_of_lt (le_max_right _ _) hu
  have huc : c < u := lt_of_le_of_lt (le_max_left _ _) hu
  set I : ℝ → ℝ := fun m => ∫ y : ℝ, G (u + y) * ((Iic x₁).indicator (fun _ => (1 : ℝ)) y
      * heatKernel d (y - m)) with hI
  have hcont : ContinuousOn I (Ioi a) :=
    (continuousOn_blkInner hG hGb hd u x₁ (le_max_left x₁ x₂)).mono Ioi_subset_Ici_self
  have hzero : ∀ p q : ℚ, a < p → (∫ m in Ioo (p : ℝ) q, I m) = 0 := by
    intro p q hap
    rw [← hr (p, q)]
    refine setIntegral_congr_fun measurableSet_Ioo fun m hm => ?_
    have hm2 : x₂ < m := lt_of_le_of_lt (le_max_right _ _) (hap.trans hm.1)
    simp only [blkKer, hI]
    rw [Set.indicator_of_mem (show u ∈ Ioi x from hux),
      Set.indicator_of_mem (show m ∈ Ioi x₂ from hm2), one_mul, mul_one]
  obtain ⟨m, hm, hIm⟩ := exists_blkInner_ne_zero hG hGb hd (u := u) (x₁ := x₁) (hc u huc) a
  exact hIm (eq_zero_of_forall_rat_setIntegral_Ioo hcont hzero hm)

/-! ## 5. Nonvanishing of `Q` and `D` -/

/-- **`Q ≠ 0`**: the block `Q = P₁ B₀ P̄₁ e^{dΔ} P₂` is not the zero operator, for every `d > 0`
and all levels `x₁, x₂`. -/
theorem qOp_ne_zero (x₁ x₂ : ℝ) {d : ℝ} (hd : 0 < d) : qOp x₁ x₂ hd ≠ 0 := by
  obtain ⟨C, hC⟩ := airy_abs_le_exp_zero
  exact kernelOperator_blkKer_ne_zero (x := x₁) AiryConj.continuous_airyAiReal hC hd
    (memLp_qKer x₁ x₂ hd) (c := -x₁)
    (fun u hu => (airyAiReal_pos_of_nonneg (by linarith)).ne')

/-- **`D ≠ 0`**: the block `D = P₂ e^{−dΔ}B₀ P̄₁ e^{dΔ} P₂` is not the zero operator, for every
`d > 0` and all levels `x₁, x₂`. -/
theorem dOp_ne_zero (x₁ x₂ : ℝ) {d : ℝ} (hd : 0 < d) : dOp x₁ x₂ hd ≠ 0 := by
  obtain ⟨C, hC⟩ := backwardAiry_abs_le_exp_neg hd
  refine kernelOperator_blkKer_ne_zero (x := x₂) (continuous_backwardAiry_s d) hC hd
    (memLp_dKer x₁ x₂ hd) (c := -x₁) (fun u hu => ?_)
  unfold backwardAiry
  exact mul_ne_zero (Real.exp_pos _).ne'
    (airyAiReal_pos_of_nonneg (by nlinarith [sq_nonneg d])).ne'

end AiryFdd
