/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.TailSensitiveNewman
import Airy1GumbelContrib.Airy.AiryFourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Uniform left-cut trace bound for the GOE kernel

The negative-axis primitive of the Airy function is bounded by an ODE energy
estimate. The positive-axis contribution is absolutely integrable.
-/

namespace Airy1Gumbel

open MeasureTheory Set

/-- The Airy function in the positive coordinate on its oscillatory half-line. -/
noncomputable def leftAiry (y : ℝ) : ℝ := airyAiReal (-y)

/-- The derivative of the reflected Airy function. -/
noncomputable def leftAirySlope (y : ℝ) : ℝ := -deriv airyAiReal (-y)

/-- The reflected Airy function has derivative `leftAirySlope`. -/
theorem hasDerivAt_leftAiry (y : ℝ) : HasDerivAt leftAiry (leftAirySlope y) y := by
  have h := (AiryKernel.hasDerivAt_airyAiReal' (-y)).comp y (hasDerivAt_neg' y)
  convert h using 1
  · rfl
  · simp [leftAirySlope]

/-- The reflected Airy ODE gives the derivative of the slope. -/
theorem hasDerivAt_leftAirySlope (y : ℝ) : HasDerivAt leftAirySlope (-y * leftAiry y) y := by
  have hd : HasDerivAt (deriv airyAiReal) ((-y) * airyAiReal (-y)) (-y) := by
    rw [← AiryKernel.deriv_deriv_airyAiReal]
    exact (hasDerivAt_deriv_airyAiReal (-y)).differentiableAt.hasDerivAt
  have h := (hd.comp y (hasDerivAt_neg' y)).neg
  convert h using 1
  · rfl
  · simp [leftAiry]

/-- The Airy ODE energy divided by the coordinate. -/
noncomputable def leftAiryEnergy (y : ℝ) : ℝ := leftAiry y ^ 2 + leftAirySlope y ^ 2 / y

/-- The divided energy has nonpositive derivative at positive coordinates. -/
theorem hasDerivAt_leftAiryEnergy (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt leftAiryEnergy (-(leftAirySlope y ^ 2) / y ^ 2) y := by
  have h := ((hasDerivAt_leftAiry y).fun_pow 2).add
    (((hasDerivAt_leftAirySlope y).fun_pow 2).div (hasDerivAt_id y) hy)
  convert h using 1
  · rfl
  · norm_num
    field_simp
    ring

/-- The divided energy is decreasing on the oscillatory tail. -/
theorem antitoneOn_leftAiryEnergy : AntitoneOn leftAiryEnergy (Ici 1) := by
  have hf : Continuous leftAiry := continuous_iff_continuousAt.mpr fun y => (hasDerivAt_leftAiry y).continuousAt
  have hv : Continuous leftAirySlope :=
    continuous_iff_continuousAt.mpr fun y => (hasDerivAt_leftAirySlope y).continuousAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
  · exact hf.continuousOn.pow 2 |>.add
      (hv.continuousOn.pow 2 |>.div continuousOn_id fun y hy => by
        have : (1 : ℝ) ≤ y := hy
        linarith)
  · rw [interior_Ici]
    exact fun y hy => (hasDerivAt_leftAiryEnergy y (by have := mem_Ioi.mp hy; linarith)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro y hy
    rw [(hasDerivAt_leftAiryEnergy y (by have := mem_Ioi.mp hy; linarith)).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _)

/-- The divided energy controls the derivative by `√E(1) · √y` for `y ≥ 1`. -/
theorem abs_leftAirySlope_le (y : ℝ) (hy : 1 ≤ y) :
    |leftAirySlope y| ≤ Real.sqrt (leftAiryEnergy 1) * Real.sqrt y := by
  have hy0 : 0 < y := by linarith
  have hmono := antitoneOn_leftAiryEnergy (mem_Ici.mpr (le_rfl : (1 : ℝ) ≤ 1)) (mem_Ici.mpr hy) hy
  have hE : 0 ≤ leftAiryEnergy 1 := by unfold leftAiryEnergy; positivity
  have h : leftAirySlope y ^ 2 / y ≤ leftAiryEnergy 1 := by
    unfold leftAiryEnergy at hmono ⊢
    linarith [sq_nonneg (leftAiry y)]
  apply le_of_sq_le_sq _ (by positivity)
  rw [sq_abs, mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hy0.le]
  exact (div_le_iff₀ hy0).mp h

/-- The tail primitive starting at `1` is bounded in absolute value by `4√E(1)`. -/
theorem abs_intervalIntegral_leftAiry_one_le (b : ℝ) (hb : 1 ≤ b) :
    |∫ y in (1 : ℝ)..b, leftAiry y| ≤ 4 * Real.sqrt (leftAiryEnergy 1) := by
  let K := Real.sqrt (leftAiryEnergy 1)
  let v := leftAirySlope
  let H (y : ℝ) := -v y / y
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hv : Continuous v := continuous_iff_continuousAt.mpr fun y => (hasDerivAt_leftAirySlope y).continuousAt
  have hf : Continuous leftAiry := continuous_iff_continuousAt.mpr fun y => (hasDerivAt_leftAiry y).continuousAt
  have hH (y : ℝ) (hy : 1 ≤ y) : HasDerivAt H (leftAiry y + v y / y ^ 2) y := by
    have hy0 : y ≠ 0 := by linarith
    have h := (hasDerivAt_leftAirySlope y).neg.div (hasDerivAt_id y) hy0
    convert h using 1
    · rfl
    · simp only [id_eq, mul_one, Pi.neg_apply, v]
      field_simp
      ring
  have hvI : IntervalIntegrable (fun y => v y / y ^ 2) volume 1 b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hb]
    exact hv.continuousOn.div (continuousOn_id.pow 2) fun y hy => pow_ne_zero _ (by linarith [hy.1])
  have hFTC : (∫ y in (1 : ℝ)..b, leftAiry y + v y / y ^ 2) = H b - H 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · rw [uIcc_of_le hb]
      exact fun y hy => hH y hy.1
    · exact (hf.intervalIntegrable _ _).add hvI
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) hvI] at hFTC
  have hsplit : (∫ y in (1 : ℝ)..b, leftAiry y) = H b - H 1 - ∫ y in (1 : ℝ)..b, v y / y ^ 2 := by
    linarith
  have hboundary (y : ℝ) (hy : 1 ≤ y) : |H y| ≤ K := by
    have hy0 : 0 < y := by linarith
    rw [show H y = -v y / y by rfl, abs_div, abs_neg, abs_of_pos hy0, div_le_iff₀ hy0]
    refine (abs_leftAirySlope_le y hy).trans (mul_le_mul_of_nonneg_left ?_ hK)
    apply le_of_sq_le_sq _ hy0.le
    rw [Real.sq_sqrt hy0.le]
    nlinarith
  let w (y : ℝ) := y ^ (-(3 / 2) : ℝ)
  have hw (y : ℝ) (hy : 0 < y) : w y = Real.sqrt y / y ^ 2 := by
    dsimp [w]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub hy]
    norm_num
  have hwI : IntervalIntegrable w volume 1 b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hb]
    exact continuousOn_id.rpow_const fun y hy => Or.inl (by change y ≠ 0; linarith [hy.1])
  have hwint : (∫ y in (1 : ℝ)..b, w y) ≤ 2 := by
    unfold w
    rw [integral_rpow (Or.inr ⟨by norm_num, by rw [uIcc_of_le hb]; simp⟩)]
    norm_num
    have hnonneg := Real.rpow_nonneg (show 0 ≤ b by linarith) (-(1 / 2) : ℝ)
    nlinarith
  have hrem : |∫ y in (1 : ℝ)..b, v y / y ^ 2| ≤ 2 * K := by
    have hbound (y : ℝ) (hy : y ∈ Icc (1 : ℝ) b) : ‖v y / y ^ 2‖ ≤ K * w y := by
      have hy0 : 0 < y := by linarith [hy.1]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hy0), hw y hy0, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (abs_leftAirySlope_le y hy.1) (sq_nonneg _)
    calc
      _ ≤ ∫ y in (1 : ℝ)..b, ‖v y / y ^ 2‖ :=
        intervalIntegral.norm_integral_le_integral_norm hb
      _ ≤ ∫ y in (1 : ℝ)..b, K * w y :=
        intervalIntegral.integral_mono_on hb hvI.norm (hwI.const_mul K) hbound
      _ ≤ _ := by
        rw [intervalIntegral.integral_const_mul, mul_comm (2 : ℝ)]
        exact mul_le_mul_of_nonneg_left hwint hK
  rw [hsplit]
  calc
    _ ≤ (|H b| + |H 1|) + |∫ y in (1 : ℝ)..b, v y / y ^ 2| :=
      (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ _ := by linarith [hboundary b hb, hboundary 1 le_rfl]

/-- The reflected Airy primitive is uniformly bounded for all nonnegative upper endpoints. -/
theorem abs_intervalIntegral_leftAiry_bounded : ∃ C : ℝ, 0 ≤ C ∧
    ∀ b : ℝ, 0 ≤ b → |∫ y in (0 : ℝ)..b, leftAiry y| ≤ C := by
  obtain ⟨A, hA⟩ := AiryFourier.airyAiReal_bdd
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  let K := Real.sqrt (leftAiryEnergy 1)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  refine ⟨A + 4 * K, by positivity, ?_⟩
  have hf : Continuous leftAiry := continuous_iff_continuousAt.mpr fun y => (hasDerivAt_leftAiry y).continuousAt
  have hshort (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
      |∫ y in (0 : ℝ)..b, leftAiry y| ≤ A := by
    calc
      _ ≤ A * |b - 0| := by
        rw [← Real.norm_eq_abs]
        exact intervalIntegral.norm_integral_le_of_norm_le_const
          (fun y _ => by simpa only [Real.norm_eq_abs, leftAiry] using hA (-y))
      _ ≤ A := by simp only [sub_zero, abs_of_nonneg hb0]; nlinarith
  intro b hb
  by_cases hb1 : b ≤ 1
  · linarith [hshort b hb hb1]
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 1)
      (hf.intervalIntegrable 1 b)]
    exact (abs_add_le _ _).trans (add_le_add (hshort 1 zero_le_one le_rfl)
      (abs_intervalIntegral_leftAiry_one_le b (le_of_not_ge hb1)))

/-- Uniform trace bound for all nonpositive GOE cuts. The constant is one plus half
the sum of a bound for the reflected Airy primitive and the positive-axis integral norm. -/
theorem abs_trace_goeOp_left_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 ≤ M →
      |HilbertSchmidt.trace (AiryFdd.goeOp (-M))| ≤ C := by
  obtain ⟨A, hA, hprim⟩ := abs_intervalIntegral_leftAiry_bounded
  obtain ⟨D, hD, hbound⟩ := AiryKernel.airyAiReal_abs_le_exp'
  have hf : Continuous airyAiReal :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_airyAiReal u).continuousAt
  have hfpos : IntegrableOn airyAiReal (Ioi 0) := by
    refine ((integrableOn_exp_neg_Ioi 0).const_mul D).mono' hf.aestronglyMeasurable ?_
    exact ae_of_all _ fun u => hbound u
  let J := ∫ u in Ioi (0 : ℝ), airyAiReal u
  refine ⟨1 + (A + |J|) / 2, by positivity, ?_⟩
  intro M hM
  let t := -(2 * M)
  have ht : t ≤ 0 := by dsimp [t]; linarith
  have hfinite : IntegrableOn airyAiReal (Ioc t 0) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp (hf.intervalIntegrable t 0)
  have hsplit : (∫ u in Ioi t, airyAiReal u) = (∫ u in t..0, airyAiReal u) + J := by
    rw [← Ioc_union_Ioi_eq_Ioi ht, setIntegral_union ?_ measurableSet_Ioi hfinite hfpos,
      intervalIntegral.integral_of_le ht]
    exact disjoint_left.mpr fun u hu₁ hu₂ => (not_lt_of_ge hu₁.2) hu₂
  have hleft : |∫ u in t..0, airyAiReal u| ≤ A := by
    simpa only [leftAiry, intervalIntegral.integral_comp_neg, neg_zero, t, neg_neg] using
      hprim (2 * M) (by positivity)
  rw [trace_goeOp_eq_half_integral, show 2 * -M = t by dsimp [t]; ring, hsplit, abs_mul]
  norm_num
  linarith [abs_add_le (∫ u in t..0, airyAiReal u) J]

end Airy1Gumbel
