/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoTime.TwoTimeKernel

/-! # Nonvanishing of the two-time blocks `Q` and `D`

The second-column block kernels `qKer`, `dKer` (`TwoTimeBlock.blkKer`) contain the inner integral
`I(u, m) = ∫ G(u + y) 1_{y ≤ x₁} p_d(y − m) dy` with `G = Ai` (for `Q`) or `G = g_d` (for `D`).
The integrand is integrable, so `I` is a genuine Bochner integral.  This file shows
that `I` is not identically zero, hence neither is `qKer` nor `dKer`.

## Route (Laplace concentration at the cut)

Fix `u` and put `m = x₁ + 2dL`.  The substitution `y = x₁ − s/L` and the Gaussian identity
`p_d(−s/L − 2dL) = p_d(2dL) · e^{−s − (s/L)²/(4d)}` give (`blkInner_eq_mul_integral`)

  `I(u, x₁ + 2dL) = L⁻¹ p_d(2dL) ∫ G(u + x₁ − s/L) 1_{s ≥ 0} e^{−s − (s/L)²/(4d)} ds`.

As `L → ∞` the normalised integral tends to `G(u + x₁) ∫_0^∞ e^{−s} ds = G(u + x₁)` by dominated
convergence (`tendsto_integral_blkNorm`; needs `|G(t)| ≤ C e^{−βt}`).  Choosing `u` with
`u + x₁ ≥ 0` makes `G(u + x₁) ≠ 0` (`Ai > 0` on `[0, ∞)`; `g_d(t) = e^{−2d³/3 − dt} Ai(t + d²)`).
-/

namespace AiryFdd

open MeasureTheory Real Set Filter Topology

/-- The normalised inner integrand `G(c − s/L) 1_{s ≥ 0} e^{−s − (s/L)²/(4d)}`. -/
noncomputable def blkNorm (G : ℝ → ℝ) (d c L s : ℝ) : ℝ :=
  G (c - s / L) * (Ici 0).indicator (fun s => Real.exp (-s - (s / L) ^ 2 / (4 * d))) s

/-- Gaussian shift: `p_d(−s/L − 2dL) = p_d(2dL) e^{−s − (s/L)²/(4d)}`. -/
theorem heatKernel_shift_eq {d : ℝ} (hd : 0 < d) {L : ℝ} (hL : L ≠ 0) (s : ℝ) :
    heatKernel d (-(s / L) - 2 * d * L)
      = heatKernel d (2 * d * L) * Real.exp (-s - (s / L) ^ 2 / (4 * d)) := by
  unfold heatKernel
  rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- **Substitution**: `I(u, x₁ + 2dL) = L⁻¹ p_d(2dL) ∫ blkNorm`. -/
theorem blkInner_eq_mul_integral (G : ℝ → ℝ) {d : ℝ} (hd : 0 < d) {L : ℝ} (hL : 0 < L)
    (u x₁ : ℝ) :
    (∫ y : ℝ, G (u + y) * ((Iic x₁).indicator (fun _ => (1 : ℝ)) y
        * heatKernel d (y - (x₁ + 2 * d * L))))
      = L⁻¹ * heatKernel d (2 * d * L) * ∫ s : ℝ, blkNorm G d (u + x₁) L s := by
  set f : ℝ → ℝ := fun y => G (u + y) * ((Iic x₁).indicator (fun _ => (1 : ℝ)) y
    * heatKernel d (y - (x₁ + 2 * d * L))) with hf
  have h1 : (∫ y, f y) = ∫ t, f (x₁ - t) := (integral_sub_left_eq_self f volume x₁).symm
  have h2 : (∫ s, f (x₁ - s / L)) = L * ∫ t, f (x₁ - t) := by
    rw [Measure.integral_comp_div (fun t => f (x₁ - t)) L, abs_of_pos hL, smul_eq_mul]
  have h3 : ∀ s, f (x₁ - s / L) = heatKernel d (2 * d * L) * blkNorm G d (u + x₁) L s := by
    intro s
    simp only [hf, blkNorm]
    by_cases hs : 0 ≤ s
    · have hy : x₁ - s / L ∈ Iic x₁ := by
        simp only [mem_Iic]; linarith [div_nonneg hs hL.le]
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show s ∈ Ici (0 : ℝ) from hs),
        show x₁ - s / L - (x₁ + 2 * d * L) = -(s / L) - 2 * d * L by ring,
        heatKernel_shift_eq hd hL.ne' s, show u + (x₁ - s / L) = u + x₁ - s / L by ring]
      ring
    · have hs' : s < 0 := lt_of_not_ge hs
      have hy : x₁ - s / L ∉ Iic x₁ := by
        simp only [mem_Iic, not_le]; linarith [div_neg_of_neg_of_pos hs' hL]
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (show s ∉ Ici (0 : ℝ) from hs)]
      ring
  rw [h1]
  have h4 : (∫ t, f (x₁ - t)) = L⁻¹ * ∫ s, f (x₁ - s / L) := by
    rw [h2, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
  rw [h4, integral_congr_ae (Eventually.of_forall h3), integral_const_mul]
  ring

/-- `∫ G(c) 1_{s ≥ 0} e^{−s} ds = G(c)`. -/
theorem integral_blkNorm_limit (G : ℝ → ℝ) (c : ℝ) :
    (∫ s : ℝ, G c * (Ici 0).indicator (fun s => Real.exp (-s)) s) = G c := by
  rw [integral_const_mul, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_exp_neg_Ioi_zero, mul_one]

/-- **Laplace concentration**: `∫ blkNorm G d c L → G(c)` as `L → ∞`, for continuous `G` with
`|G(t)| ≤ C e^{−βt}`. -/
theorem tendsto_integral_blkNorm {G : ℝ → ℝ} (hG : Continuous G) {C β : ℝ}
    (hGb : ∀ t, |G t| ≤ C * Real.exp (-β * t)) {d : ℝ} (hd : 0 < d) (c : ℝ) :
    Tendsto (fun L => ∫ s : ℝ, blkNorm G d c L s) atTop (𝓝 (G c)) := by
  have hC : 0 ≤ C := by
    have h := hGb 0
    have : 0 ≤ C * Real.exp (-β * 0) := le_trans (abs_nonneg _) h
    simpa using this
  rw [← integral_blkNorm_limit G c]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun s => (Ici 0).indicator (fun s => C * Real.exp (-β * c) * Real.exp (-(1 / 2) * s)) s)
    (Eventually.of_forall fun L => ?_) ?_ ?_ (Eventually.of_forall fun s => ?_)
  · exact ((hG.comp (continuous_const.sub (continuous_id.div_const L))).measurable.mul
      ((Real.continuous_exp.comp ((continuous_neg.sub
        (((continuous_id.div_const L).pow 2).div_const _)))).measurable.indicator
        measurableSet_Ici)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (max (2 * β) 1)] with L hL
    have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
    have hL2 : 2 * β ≤ L := le_trans (le_max_left _ _) hL
    have hL0 : 0 < L := by linarith
    refine Eventually.of_forall fun s => ?_
    simp only [blkNorm]
    by_cases hs : s ∈ Ici (0 : ℝ)
    · have hs0 : 0 ≤ s := hs
      rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      have hb : β * (s / L) ≤ s / 2 := by
        rw [← mul_div_assoc, div_le_iff₀ hL0]; nlinarith
      have hq : 0 ≤ (s / L) ^ 2 / (4 * d) := by positivity
      calc |G (c - s / L)| * Real.exp (-s - (s / L) ^ 2 / (4 * d))
          ≤ C * Real.exp (-β * (c - s / L)) * Real.exp (-s - (s / L) ^ 2 / (4 * d)) :=
            mul_le_mul_of_nonneg_right (hGb _) (Real.exp_pos _).le
        _ = C * Real.exp (-β * c + (β * (s / L) - s - (s / L) ^ 2 / (4 * d))) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ C * Real.exp (-β * c + -(1 / 2) * s) := by
            gcongr; linarith
        _ = C * Real.exp (-β * c) * Real.exp (-(1 / 2) * s) := by
            rw [Real.exp_add]; ring
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, mul_zero, norm_zero]
  · have h : IntegrableOn (fun s => C * Real.exp (-β * c) * Real.exp (-(1 / 2) * s)) (Ici 0) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).2
        ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _)
    exact h.integrable_indicator measurableSet_Ici
  · by_cases hs : s ∈ Ici (0 : ℝ)
    · simp only [blkNorm, Set.indicator_of_mem hs]
      have hε : Tendsto (fun L : ℝ => s / L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
      have hφ : Continuous fun ε : ℝ => G (c - ε) * Real.exp (-s - ε ^ 2 / (4 * d)) :=
        (hG.comp (continuous_const.sub continuous_id)).mul
          (Real.continuous_exp.comp (continuous_const.sub ((continuous_id.pow 2).div_const _)))
      have := (hφ.tendsto 0).comp hε
      simpa [Function.comp_def] using this
    · simp only [blkNorm, Set.indicator_of_notMem hs, mul_zero]
      exact tendsto_const_nhds

/-- **The inner integral of a `Q`/`D`-type block is not identically zero**: if `G` is continuous,
`|G(t)| ≤ C e^{−βt}` and `G(u + x₁) ≠ 0`, then for every `M` there is `m > M` with
`∫ G(u + y) 1_{y ≤ x₁} p_d(y − m) dy ≠ 0`. -/
theorem exists_blkInner_ne_zero {G : ℝ → ℝ} (hG : Continuous G) {C β : ℝ}
    (hGb : ∀ t, |G t| ≤ C * Real.exp (-β * t)) {d : ℝ} (hd : 0 < d) {u x₁ : ℝ}
    (hG0 : G (u + x₁) ≠ 0) (M : ℝ) :
    ∃ m, M < m ∧ (∫ y : ℝ, G (u + y) * ((Iic x₁).indicator (fun _ => (1 : ℝ)) y
        * heatKernel d (y - m))) ≠ 0 := by
  have hev := ((tendsto_integral_blkNorm hG hGb hd (u + x₁)).eventually_ne hG0).and
    ((eventually_gt_atTop 0).and (eventually_gt_atTop ((M - x₁) / (2 * d))))
  obtain ⟨L, hJ, hL0, hLM⟩ := hev.exists
  refine ⟨x₁ + 2 * d * L, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)] at hLM
    linarith
  · rw [blkInner_eq_mul_integral G hd hL0 u x₁]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hL0.ne') (heatKernel_pos hd _).ne') hJ

/-- `Ai(u + x₁) > 0` and `g_d(u + x₁) > 0` at the point `u = |x₁| + |x₂| + 1`. -/
theorem probe_point_nonneg (x₁ x₂ : ℝ) : 0 ≤ (|x₁| + |x₂| + 1) + x₁ := by
  have := neg_abs_le x₁
  have := abs_nonneg x₂
  linarith

theorem probe_point_gt (x₁ x₂ : ℝ) : x₁ < |x₁| + |x₂| + 1 ∧ x₂ < |x₁| + |x₂| + 1 := by
  have := le_abs_self x₁
  have := le_abs_self x₂
  have := abs_nonneg x₁
  have := abs_nonneg x₂
  constructor <;> linarith

/-- **Nonvanishing witness (`Q`)**: for every `d > 0` and levels `x₁, x₂`, the `Q`-kernel is
nonzero at some
point `(u, m)` with `u > x₁`, `m > x₂` (here `u = |x₁| + |x₂| + 1`, `m` large). -/
theorem exists_qKer_ne_zero (x₁ x₂ : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ u m, x₁ < u ∧ x₂ < m ∧ qKer x₁ x₂ d (u, m) ≠ 0 := by
  set u := |x₁| + |x₂| + 1
  obtain ⟨C, hC⟩ := airy_abs_le_exp_zero
  obtain ⟨m, hm, hI⟩ := exists_blkInner_ne_zero AiryConj.continuous_airyAiReal hC hd
    (u := u) (x₁ := x₁) (airyAiReal_pos_of_nonneg (probe_point_nonneg x₁ x₂)).ne' x₂
  have hu := (probe_point_gt x₁ x₂).1
  refine ⟨u, m, hu, hm, ?_⟩
  unfold qKer blkKer
  rw [Set.indicator_of_mem (show u ∈ Ioi x₁ from hu), Set.indicator_of_mem (show m ∈ Ioi x₂ from hm),
    one_mul, mul_one]
  exact hI

/-- **Nonvanishing witness (`D`)**: for every `d > 0` and levels `x₁, x₂`, the `D`-kernel is
nonzero at some
point `(u, m)` with `u > x₂`, `m > x₂` (here `u = |x₁| + |x₂| + 1`, `m` large). -/
theorem exists_dKer_ne_zero (x₁ x₂ : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ u m, x₂ < u ∧ x₂ < m ∧ dKer x₁ x₂ d (u, m) ≠ 0 := by
  set u := |x₁| + |x₂| + 1
  obtain ⟨C, hC⟩ := backwardAiry_abs_le_exp_neg hd
  have hg : backwardAiry d (u + x₁) ≠ 0 := by
    unfold backwardAiry
    exact mul_ne_zero (Real.exp_pos _).ne'
      (airyAiReal_pos_of_nonneg (by have := probe_point_nonneg x₁ x₂; positivity)).ne'
  obtain ⟨m, hm, hI⟩ := exists_blkInner_ne_zero (continuous_backwardAiry_s d) hC hd
    (u := u) (x₁ := x₁) hg x₂
  have hu := (probe_point_gt x₁ x₂).2
  refine ⟨u, m, hu, hm, ?_⟩
  unfold dKer blkKer
  rw [Set.indicator_of_mem (show u ∈ Ioi x₂ from hu), Set.indicator_of_mem (show m ∈ Ioi x₂ from hm),
    one_mul, mul_one]
  exact hI

/-- The `Q` kernel is not the zero function. -/
theorem qKer_ne_zero (x₁ x₂ : ℝ) {d : ℝ} (hd : 0 < d) : qKer x₁ x₂ d ≠ 0 := fun h => by
  obtain ⟨u, m, -, -, hne⟩ := exists_qKer_ne_zero x₁ x₂ hd
  exact hne (congrFun h (u, m))

/-- The `D` kernel is not the zero function. -/
theorem dKer_ne_zero (x₁ x₂ : ℝ) {d : ℝ} (hd : 0 < d) : dKer x₁ x₂ d ≠ 0 := fun h => by
  obtain ⟨u, m, -, -, hne⟩ := exists_dKer_ne_zero x₁ x₂ hd
  exact hne (congrFun h (u, m))

end AiryFdd
