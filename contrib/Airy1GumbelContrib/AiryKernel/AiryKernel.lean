/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryReal
import Airy1GumbelContrib.Airy.AiryIdentity
import Airy1GumbelContrib.Airy.AiryLaplaceFull
import Airy1GumbelContrib.TraceClass.FredholmTwo
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The Airy kernel operator on `L²((0, ∞))`

The Airy kernel is the integral kernel

  `K(x, y) = ∫₀^∞ Ai(x + u) Ai(y + u) du`
           `= (Ai(x) Ai'(y) - Ai'(x) Ai(y)) / (x - y)`    (`x ≠ y`),

acting on `L²((s, ∞))`.  Its square-root factor is the **Airy–Hankel operator** `T_s`
with kernel `Ai(x + t)` on `(s, ∞) × (0, ∞)`; the Airy kernel operator is the product
`K_s = T_s T_s*`, hence trace class, and its Hilbert–Schmidt norm tends to `0` as
`s → ∞`.

## Main results

* `airyAiReal_abs_le_exp`: a global exponential bound `|Ai(u)| ≤ C e^{-u}` on the whole
  real line (from the `ℝ₋` bound `airyAiReal_abs_le_nonpos`, compactness on `[0, 9/4]`,
  and the super-exponential decay `airyAiReal_le` for `u ≥ 9/4`).
* `airyHankelKernel`, `memLp_airyHankelKernel`, `eLpNorm_airyHankelKernel_le`: the
  truncated kernel `Ai(x + t) 1_{s < x}` is in `L²(ν × ν)` (where `ν` is Lebesgue
  measure on `(0, ∞)`), with the decay `‖K̃_s‖_{L²} ≤ (C/2) e^{-s}` for `s ≥ 0`.
* `airyHankel`, `isHilbertSchmidt_airyHankel`, `tendsto_hsENorm_airyHankel`: the
  Airy–Hankel operator on `L²(ν)` is Hilbert–Schmidt with `‖T_s‖_HS → 0`.
* `airyKernelOp`, `isTraceClass_airyKernelOp`, `tendsto_hsENorm_airyKernelOp`: the Airy
  kernel operator `K_s = T_s T_s*` is trace class with `‖K_s‖_HS → 0`.
* `airyAiReal_sq_integral` (the energy identity) and `airyKernelWronskian`: the closed
  Wronskian form of the Airy kernel, from the energy derivative identity
  `E'(t) = -Ai(t)²` for `E(t) = Ai'(t)² - t Ai(t)²`.

## Notation

`ν` (`halfLineMeasure`) is Lebesgue measure restricted to `(0, ∞)`.
-/

open MeasureTheory Filter
open scoped ENNReal Topology InnerProduct

namespace AiryKernel

/-- Lebesgue measure restricted to the positive half-line `(0, ∞)`: the ambient measure
of the Hilbert space `L²(ν)` on which the Airy kernel operator acts. -/
noncomputable abbrev halfLineMeasure : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Ioi 0)

section GlobalBound

/-- A global exponential bound for the real Airy function: `|Ai(u)| ≤ C e^{-u}` for all
`u : ℝ`.  Three regions: `u ≤ 0` uses the boundedness of `Ai` on `ℝ₋`
(`airyAiReal_abs_le_nonpos`), `0 ≤ u ≤ 9/4` uses compactness, and `u ≥ 9/4` uses the
super-exponential decay `airyAiReal_le`, where `(2/3) u^{3/2} ≥ u`. -/
theorem airyAiReal_abs_le_exp : ∃ C : ℝ, ∀ u : ℝ, |airyAiReal u| ≤ C * Real.exp (-u) := by
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le_nonpos
  obtain ⟨C₁, hC₁⟩ := airyAiReal_le
  have hC₀nn : 0 ≤ C₀ := (abs_nonneg _).trans (hC₀ 0 le_rfl)
  have hC₁nn : 0 ≤ C₁ := by
    have h1 := hC₁ 1 le_rfl
    rw [Real.one_rpow, Real.one_rpow, mul_one] at h1
    have hpos : (0 : ℝ) < airyAiReal 1 := airyAiReal_pos_of_nonneg zero_le_one
    exact le_of_lt (pos_of_mul_pos_left (hpos.trans_le h1) (Real.exp_pos _).le)
  have hcont : Continuous airyAiReal :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyAiReal x).continuousAt
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (by norm_num : (0:ℝ) ≤ 9/4)) hcont.abs.continuousOn
  set M := |airyAiReal x₀| with hM_def
  have hMnn : 0 ≤ M := abs_nonneg _
  have hM : ∀ u ∈ Set.Icc 0 (9/4), |airyAiReal u| ≤ M := fun u hu => hmax hu
  refine ⟨max (max C₀ (M * Real.exp (9/4))) C₁, fun u => ?_⟩
  rcases le_total u 0 with hu | hu
  · -- `u ≤ 0`: `|Ai u| ≤ C₀ ≤ C₀ e^{-u}` since `e^{-u} ≥ 1`.
    have h1 : (1 : ℝ) ≤ Real.exp (-u) := Real.one_le_exp (by linarith)
    calc |airyAiReal u| ≤ C₀ := hC₀ u hu
      _ = C₀ * 1 := (mul_one C₀).symm
      _ ≤ C₀ * Real.exp (-u) := mul_le_mul_of_nonneg_left h1 hC₀nn
      _ ≤ max (max C₀ (M * Real.exp (9/4))) C₁ * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _))
            (Real.exp_pos _).le
  · by_cases hu2 : u ≤ 9/4
    · -- `0 ≤ u ≤ 9/4`: the compactness bound, inflated by `e^{9/4}`.
      have h1 : (1 : ℝ) ≤ Real.exp (9/4 - u) := Real.one_le_exp (by linarith)
      calc |airyAiReal u| ≤ M := hM u ⟨hu, hu2⟩
        _ = M * 1 := (mul_one M).symm
        _ ≤ M * Real.exp (9/4 - u) := mul_le_mul_of_nonneg_left h1 hMnn
        _ = (M * Real.exp (9/4)) * Real.exp (-u) := by
            rw [Real.exp_sub, Real.exp_neg, div_eq_mul_inv, ← Real.exp_neg]
            ring
        _ ≤ max (max C₀ (M * Real.exp (9/4))) C₁ * Real.exp (-u) :=
            mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _))
              (Real.exp_pos _).le
    · -- `u > 9/4`: the super-exponential decay dominates `e^{-u}`.
      have hu2' : 9/4 < u := lt_of_not_ge hu2
      have hAipos : 0 < airyAiReal u := airyAiReal_pos_of_nonneg (by linarith)
      rw [abs_of_pos hAipos]
      have hu1 : (1 : ℝ) ≤ u := by linarith
      have hu0 : (0 : ℝ) < u := by linarith
      have hr1 : u ^ (-1/4 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
      have hsqrt : (3 : ℝ)/2 ≤ Real.sqrt u := by
        have h94 : Real.sqrt (9/4 : ℝ) = 3/2 := by
          have h : (9/4 : ℝ) = (3/2)^2 := by norm_num
          rw [h, Real.sqrt_sq (by norm_num)]
        have h2 := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 9/4) hu2'
        rw [h94] at h2
        exact h2.le
      have hr32 : u ^ (3/2 : ℝ) = Real.sqrt u * u := by
        rw [show (3/2 : ℝ) = 1/2 + 1 by norm_num, Real.rpow_add_one (ne_of_gt hu0),
          Real.sqrt_eq_rpow]
      have hexp : Real.exp (-(2/3 * u^(3/2:ℝ))) ≤ Real.exp (-u) := by
        apply Real.exp_le_exp.mpr
        rw [hr32]
        have h1 : (3:ℝ)/2 * u ≤ Real.sqrt u * u :=
          mul_le_mul_of_nonneg_right hsqrt hu0.le
        linarith
      calc airyAiReal u ≤ C₁ * u^(-1/4:ℝ) * Real.exp (-(2/3 * u^(3/2:ℝ))) := hC₁ u hu1
        _ ≤ C₁ * 1 * Real.exp (-u) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hr1 hC₁nn) hexp (Real.exp_pos _).le
              (mul_nonneg hC₁nn zero_le_one)
        _ = C₁ * Real.exp (-u) := by ring
        _ ≤ max (max C₀ (M * Real.exp (9/4))) C₁ * Real.exp (-u) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- A positive constant bounding `|Ai(u)|` by `C e^{-u}` globally. -/
theorem airyAiReal_abs_le_exp' :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, |airyAiReal u| ≤ C * Real.exp (-u) := by
  obtain ⟨C, hC⟩ := airyAiReal_abs_le_exp
  have hCpos : 0 < C := by
    have h1 := hC 0
    rw [neg_zero, Real.exp_zero, mul_one] at h1
    exact (abs_pos.mpr (airyAiReal_pos_of_nonneg le_rfl).ne').trans_le h1
  exact ⟨C, hCpos, hC⟩

end GlobalBound

section OneDimIntegrals

/-- `(e^{-t})² = e^{-2t}`. -/
theorem exp_neg_sq (t : ℝ) : (Real.exp (-t))^2 = Real.exp (-(2*t)) := by
  rw [sq, ← Real.exp_add]
  ring_nf

/-- `e^{-2t}` is integrable on `(a, ∞)`. -/
theorem integrableOn_exp_neg_two_mul (a : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(2*t))) (Set.Ioi a) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi a) := integrableOn_exp_neg_Ioi a
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-t))
      (volume.restrict (Set.Ioi a)) :=
    (Real.measurable_exp.comp measurable_neg).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi a)), ‖Real.exp (-t)‖ ≤ Real.exp (-a) := by
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    have ht' : a < t := ht
    exact Real.exp_le_exp.mpr (by linarith)
  have h2 : Integrable (fun t : ℝ => Real.exp (-t) * Real.exp (-t))
      (volume.restrict (Set.Ioi a)) := h1.bdd_mul hmeas hbound
  apply h2.congr (Filter.Eventually.of_forall fun t => ?_)
  show Real.exp (-t) * Real.exp (-t) = Real.exp (-(2*t))
  rw [← Real.exp_add]
  ring_nf

/-- `∫_a^∞ e^{-2t} dt = e^{-2a} / 2`. -/
theorem integral_exp_neg_two_mul_Ioi (a : ℝ) :
    ∫ t in Set.Ioi a, Real.exp (-(2*t)) = Real.exp (-(2*a))/2 := by
  have hF : ∀ x : ℝ, HasDerivAt (fun x : ℝ => -Real.exp (-(2*x))/2) (Real.exp (-(2*x))) x := by
    intro x
    have h2 : HasDerivAt (fun x : ℝ => (2:ℝ) * x) 2 x := by
      simpa using (hasDerivAt_id' x).const_mul (2:ℝ)
    have h4 : HasDerivAt (fun x : ℝ => Real.exp (-(2*x))) (Real.exp (-(2*x)) * -2) x := by
      have h5 := (Real.hasDerivAt_exp (-(2*x))).comp x h2.neg
      exact h5
    have h6 := h4.neg.div_const 2
    convert h6 using 1
    ring
  have hlim : Tendsto (fun x : ℝ => -Real.exp (-(2*x))/2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.exp (-(2*x))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => (2:ℝ) * x) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) tendsto_id
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 := h0.neg.div_const 2
    simpa using h3
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun x : ℝ => -Real.exp (-(2*x))/2) (f' := fun x : ℝ => Real.exp (-(2*x)))
    ((hF a).continuousAt.continuousWithinAt) (fun x _ => hF x)
    (integrableOn_exp_neg_two_mul a) hlim
  rw [hftc]
  ring

/-- The `lintegral` version: `∫⁻_a^∞ ofReal (e^{-2t}) = ofReal (e^{-2a} / 2)`. -/
theorem lintegral_exp_neg_two_mul_Ioi (a : ℝ) :
    ∫⁻ t in Set.Ioi a, ENNReal.ofReal (Real.exp (-(2*t))) =
      ENNReal.ofReal (Real.exp (-(2*a))/2) := by
  have hnn : ∀ᵐ t ∂(volume.restrict (Set.Ioi a)), (0:ℝ) ≤ Real.exp (-(2*t)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => (Real.exp_pos _).le
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_two_mul a) hnn,
    integral_exp_neg_two_mul_Ioi a]

end OneDimIntegrals

section HankelKernel

/-- `airyAiReal` is measurable (it is continuous). -/
theorem measurable_airyAiReal : Measurable airyAiReal :=
  (continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyAiReal x).continuousAt).measurable

/-- The truncated Airy–Hankel kernel at level `s`: `K̃_s(x, t) = Ai(x + t)` for `x > s`,
`0` otherwise. -/
noncomputable def airyHankelKernel (s : ℝ) : ℝ × ℝ → ℝ :=
  fun p => if s < p.1 then airyAiReal (p.1 + p.2) else 0

/-- The cutoff set `{p | s < p.1}` is measurable. -/
theorem measurableSet_hankelCut (s : ℝ) : MeasurableSet {q : ℝ × ℝ | s < q.1} :=
  measurableSet_lt measurable_const measurable_fst

/-- The truncated Airy–Hankel kernel is measurable. -/
theorem measurable_airyHankelKernel (s : ℝ) : Measurable (airyHankelKernel s) :=
  Measurable.ite (measurableSet_hankelCut s)
    (measurable_airyAiReal.comp (measurable_fst.add measurable_snd)) measurable_const

/-- The squared dominating function for the Airy–Hankel kernel:
`F q = ofReal ((C e^{-(q.1 + q.2)})²)`. -/
noncomputable def hankelDom (C : ℝ) : ℝ × ℝ → ℝ≥0∞ :=
  fun q => ENNReal.ofReal ((C * Real.exp (-(q.1 + q.2)))^2)

/-- The squared dominating function is measurable. -/
theorem measurable_hankelDom (C : ℝ) : Measurable (hankelDom C) :=
  ENNReal.measurable_ofReal.comp
    ((measurable_const.mul
      (Real.measurable_exp.comp (measurable_fst.add measurable_snd).neg)).pow_const 2)

/-- Pointwise domination: `‖K̃_s p‖ₑ² ≤ 1_{s < p.1} · ofReal ((C e^{-(p.1+p.2)})²)`. -/
theorem enorm_sq_airyHankelKernel_le {C : ℝ} (_hCnn : 0 ≤ C)
    (hC : ∀ u : ℝ, |airyAiReal u| ≤ C * Real.exp (-u)) (s : ℝ) (p : ℝ × ℝ) :
    ‖airyHankelKernel s p‖ₑ ^ 2 ≤
      ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) p := by
  by_cases h : s < p.1
  · rw [Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | s < q.1} from h)]
    have hK : airyHankelKernel s p = airyAiReal (p.1 + p.2) := ite_eq_left h
    rw [enorm_sq_eq_ofReal, hK, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (hC _) 2)
  · rw [Set.indicator_of_notMem (show p ∉ {q : ℝ × ℝ | s < q.1} from h)]
    have hK : airyHankelKernel s p = 0 := ite_eq_right h
    rw [hK]
    simp

/-- The slice `lintegral` of the squared dominator:
`∫⁻ t in Ioi 0, ofReal ((C e^{-(x+t)})²) = ofReal (C² e^{-2x} / 2)`. -/
theorem lintegral_hankelDom_slice {C : ℝ} (_hCnn : 0 ≤ C) (x : ℝ) :
    ∫⁻ t, hankelDom C (x, t) ∂halfLineMeasure = ENNReal.ofReal (C^2 * Real.exp (-(2*x)) / 2) := by
  have h1 : ∀ t : ℝ, hankelDom C (x, t)
      = ENNReal.ofReal (C^2 * Real.exp (-(2*x))) * ENNReal.ofReal (Real.exp (-(2*t))) := by
    intro t
    show ENNReal.ofReal ((C * Real.exp (-(x + t)))^2) = _
    rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    congr 1
    rw [mul_pow, exp_neg_sq, show (2:ℝ) * (x + t) = 2*x + 2*t by ring, neg_add, Real.exp_add]
    ring
  have h2 : (∫⁻ t, ENNReal.ofReal (Real.exp (-(2*t))) ∂halfLineMeasure)
      = ENNReal.ofReal (Real.exp (-(2*(0:ℝ)))/2) := lintegral_exp_neg_two_mul_Ioi 0
  calc ∫⁻ t, hankelDom C (x, t) ∂halfLineMeasure
      = ∫⁻ t, ENNReal.ofReal (C^2 * Real.exp (-(2*x))) * ENNReal.ofReal (Real.exp (-(2*t)))
          ∂halfLineMeasure := MeasureTheory.lintegral_congr h1
    _ = ENNReal.ofReal (C^2 * Real.exp (-(2*x)))
          * ∫⁻ t, ENNReal.ofReal (Real.exp (-(2*t))) ∂halfLineMeasure :=
        MeasureTheory.lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
          (Real.measurable_exp.comp ((measurable_id'.const_mul 2).neg)))
    _ = ENNReal.ofReal (C^2 * Real.exp (-(2*x))) * ENNReal.ofReal (Real.exp (-(2*(0:ℝ)))/2) := by
        rw [h2]
    _ = ENNReal.ofReal (C^2 * Real.exp (-(2*x)) / 2) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
        congr 1
        rw [mul_zero, neg_zero, Real.exp_zero]
        ring

/-- `lintegral` over `ν` restricted further to `(s, ∞)` equals `lintegral` over
`(max s 0, ∞)`. -/
theorem setLIntegral_halfLineMeasure_Ioi (s : ℝ) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in Set.Ioi s, f x ∂halfLineMeasure = ∫⁻ x in Set.Ioi (max s 0), f x := by
  show ∫⁻ x, f x ∂(halfLineMeasure.restrict (Set.Ioi s))
    = ∫⁻ x, f x ∂(volume.restrict (Set.Ioi (max s 0)))
  rw [MeasureTheory.Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi]

/-- The `L²`-norm computation for the dominating function: the `lintegral` of the squared
dominator over `{q | s < q.1}` equals `C² e^{-2 max(s, 0)} / 4`. -/
theorem lintegral_hankelDom_sq {C : ℝ} (hCnn : 0 ≤ C) (s : ℝ) :
    ∫⁻ p, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) p
        ∂(halfLineMeasure.prod halfLineMeasure)
      = ENNReal.ofReal (C^2 * Real.exp (-(2 * (max s 0))) / 4) := by
  have hmeas : Measurable (({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C)) :=
    (measurable_hankelDom C).indicator (measurableSet_hankelCut s)
  calc ∫⁻ p, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) p
        ∂(halfLineMeasure.prod halfLineMeasure)
      = ∫⁻ x, ∫⁻ t, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) (x, t)
          ∂halfLineMeasure ∂halfLineMeasure :=
        MeasureTheory.lintegral_prod _ hmeas.aemeasurable
    _ = ∫⁻ x, (Set.Ioi s).indicator
          (fun x' => ∫⁻ t, hankelDom C (x', t) ∂halfLineMeasure) x ∂halfLineMeasure := by
        apply MeasureTheory.lintegral_congr
        intro x
        by_cases hx : s < x
        · have h1 : ∀ t : ℝ, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) (x, t)
              = hankelDom C (x, t) := fun t =>
            Set.indicator_of_mem (show (x, t) ∈ {q : ℝ × ℝ | s < q.1} from hx) _
          rw [MeasureTheory.lintegral_congr h1,
            Set.indicator_of_mem (show x ∈ Set.Ioi s from hx) _]
        · have h1 : ∀ t : ℝ, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) (x, t)
              = 0 := fun t =>
            Set.indicator_of_notMem (show (x, t) ∉ {q : ℝ × ℝ | s < q.1} from hx) _
          rw [MeasureTheory.lintegral_congr h1, MeasureTheory.lintegral_zero,
            Set.indicator_of_notMem (show x ∉ Set.Ioi s from hx)]
    _ = ∫⁻ x in Set.Ioi s, (∫⁻ t, hankelDom C (x, t) ∂halfLineMeasure) ∂halfLineMeasure :=
        MeasureTheory.lintegral_indicator measurableSet_Ioi _
    _ = ∫⁻ x in Set.Ioi s, ENNReal.ofReal (C^2 * Real.exp (-(2*x)) / 2) ∂halfLineMeasure := by
        apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
        exact fun x _ => lintegral_hankelDom_slice hCnn x
    _ = ∫⁻ x in Set.Ioi (max s 0), ENNReal.ofReal (C^2 * Real.exp (-(2*x)) / 2) := by
        rw [setLIntegral_halfLineMeasure_Ioi s]
    _ = ENNReal.ofReal (C^2 * Real.exp (-(2 * (max s 0))) / 4) := by
        have h3 : ∀ x : ℝ, ENNReal.ofReal (C^2 * Real.exp (-(2*x)) / 2)
            = ENNReal.ofReal (C^2/2) * ENNReal.ofReal (Real.exp (-(2*x))) := fun x => by
          rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C^2/2)]
          congr 1
          ring
        have h4 : (∫⁻ x in Set.Ioi (max s 0),
              ENNReal.ofReal (C^2/2) * ENNReal.ofReal (Real.exp (-(2*x))))
            = ENNReal.ofReal (C^2/2)
              * ∫⁻ x in Set.Ioi (max s 0), ENNReal.ofReal (Real.exp (-(2*x))) :=
          MeasureTheory.lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
            (Real.measurable_exp.comp ((measurable_id'.const_mul 2).neg)))
        rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi (fun x _ => h3 x), h4,
          lintegral_exp_neg_two_mul_Ioi (max s 0),
          ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C^2/2)]
        congr 1
        ring

/-- The truncated Airy–Hankel kernel is square-integrable on `ν × ν`. -/
theorem memLp_airyHankelKernel (s : ℝ) :
    MemLp (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  show eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure) < ⊤
  have hlt : (eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)) ^ 2 < ⊤ := by
    calc (eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)) ^ 2
        = ∫⁻ p, ‖airyHankelKernel s p‖ₑ ^ 2 ∂(halfLineMeasure.prod halfLineMeasure) :=
          MeasureTheory.eLpNorm_two_sq_eq_lintegral
            (measurable_airyHankelKernel s).aestronglyMeasurable
      _ ≤ ∫⁻ p, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) p
            ∂(halfLineMeasure.prod halfLineMeasure) :=
          MeasureTheory.lintegral_mono (enorm_sq_airyHankelKernel_le hCpos.le hC s)
      _ = ENNReal.ofReal (C^2 * Real.exp (-(2 * (max s 0))) / 4) :=
          lintegral_hankelDom_sq hCpos.le s
      _ < ⊤ := ENNReal.ofReal_lt_top
  by_contra htop
  rw [lt_top_iff_ne_top, not_not] at htop
  rw [htop, ENNReal.top_pow (by norm_num : (2:ℕ) ≠ 0)] at hlt
  exact (lt_irrefl ⊤) hlt

/-- The quantitative decay of the kernel norm: for `s ≥ 0`,
`‖K̃_s‖_{L²(ν × ν)} ≤ (C/2) e^{-s}`. -/
theorem eLpNorm_airyHankelKernel_le {C : ℝ} (hCnn : 0 ≤ C)
    (hC : ∀ u : ℝ, |airyAiReal u| ≤ C * Real.exp (-u)) {s : ℝ} (hs : 0 ≤ s) :
    eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)
      ≤ ENNReal.ofReal (C/2 * Real.exp (-s)) := by
  have hle : (eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)) ^ 2
      ≤ ENNReal.ofReal ((C/2 * Real.exp (-s))^2) := by
    calc (eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)) ^ 2
        = ∫⁻ p, ‖airyHankelKernel s p‖ₑ ^ 2 ∂(halfLineMeasure.prod halfLineMeasure) :=
          MeasureTheory.eLpNorm_two_sq_eq_lintegral
            (measurable_airyHankelKernel s).aestronglyMeasurable
      _ ≤ ∫⁻ p, ({q : ℝ × ℝ | s < q.1}).indicator (hankelDom C) p
            ∂(halfLineMeasure.prod halfLineMeasure) :=
          MeasureTheory.lintegral_mono (enorm_sq_airyHankelKernel_le hCnn hC s)
      _ = ENNReal.ofReal (C^2 * Real.exp (-(2 * (max s 0))) / 4) :=
          lintegral_hankelDom_sq hCnn s
      _ = ENNReal.ofReal ((C/2 * Real.exp (-s))^2) := by
          congr 1
          rw [max_eq_left hs, mul_pow, div_pow, exp_neg_sq]
          ring
  calc eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)
      = ((eLpNorm (airyHankelKernel s) 2 (halfLineMeasure.prod halfLineMeasure)) ^ 2) ^ (1/2 : ℝ) :=
        (HilbertSchmidt.rpow_half_sq' _).symm
    _ ≤ (ENNReal.ofReal ((C/2 * Real.exp (-s))^2)) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow hle (by norm_num : (0:ℝ) ≤ 1/2)
    _ = ((ENNReal.ofReal (C/2 * Real.exp (-s)))^2) ^ (1/2 : ℝ) := by
        rw [ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ C/2 * Real.exp (-s)) 2]
    _ = ENNReal.ofReal (C/2 * Real.exp (-s)) := HilbertSchmidt.rpow_half_sq' _

end HankelKernel

section Operators

/-- The Airy–Hankel operator at level `s`: the integral operator on `L²(ν)` with kernel
`Ai(x + t)` for `x > s`. -/
noncomputable def airyHankel (s : ℝ) :
    Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure :=
  HilbertSchmidt.kernelOperator (memLp_airyHankelKernel s)

/-- The Airy–Hankel operator is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_airyHankel (s : ℝ) :
    HilbertSchmidt.IsHilbertSchmidt (airyHankel s) :=
  HilbertSchmidt.isHilbertSchmidt_kernelOperator (memLp_airyHankelKernel s)

/-- The Hilbert–Schmidt norm of the Airy–Hankel operator tends to `0` as `s → ∞`:
`‖T_s‖_HS ≤ (C/2) e^{-s}` for `s ≥ 0`. -/
theorem tendsto_hsENorm_airyHankel :
    Tendsto (fun s => HilbertSchmidt.hsENorm (airyHankel s)) atTop (𝓝 0) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ => (0:ℝ≥0∞))
    (h := fun s => ENNReal.ofReal (C/2 * Real.exp (-s)))
  · exact tendsto_const_nhds
  · have h0 : Tendsto (fun s : ℝ => C/2 * Real.exp (-s)) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (C/2)
      rwa [mul_zero] at h
    have h1 := (ENNReal.continuous_ofReal.tendsto 0).comp h0
    rwa [ENNReal.ofReal_zero] at h1
  · exact Filter.Eventually.of_forall fun s => zero_le
  · filter_upwards [Filter.eventually_ge_atTop 0] with s hs
    exact (HilbertSchmidt.hsENorm_kernelOperator_le (memLp_airyHankelKernel s)).trans
      (eLpNorm_airyHankelKernel_le hCpos.le hC hs)

/-- The operator norm of the Airy–Hankel operator is bounded by its Hilbert–Schmidt
norm. -/
theorem enorm_airyHankel_le_hsENorm (s : ℝ) :
    ‖airyHankel s‖ₑ ≤ HilbertSchmidt.hsENorm (airyHankel s) :=
  HilbertSchmidt.opENorm_le_sumSq_rpow_half _ _

end Operators

section AiryKernelOperator

/-- The Airy kernel operator at level `s`: `K_s = T_s T_s*` on `L²(ν)`. -/
noncomputable def airyKernelOp (s : ℝ) :
    Lp ℝ 2 halfLineMeasure →L[ℝ] Lp ℝ 2 halfLineMeasure :=
  airyHankel s ∘L (airyHankel s)†

/-- The Airy kernel operator is trace class (a product of two Hilbert–Schmidt
operators). -/
theorem isTraceClass_airyKernelOp (s : ℝ) : HilbertSchmidt.IsTraceClass (airyKernelOp s) :=
  ⟨airyHankel s, (airyHankel s)†, isHilbertSchmidt_airyHankel s,
    (isHilbertSchmidt_airyHankel s).adjoint, rfl⟩

/-- `‖K_s‖_HS ≤ ‖T_s‖_HS²`. -/
theorem hsENorm_airyKernelOp_le (s : ℝ) :
    HilbertSchmidt.hsENorm (airyKernelOp s)
      ≤ HilbertSchmidt.hsENorm (airyHankel s) * HilbertSchmidt.hsENorm (airyHankel s) :=
  (HilbertSchmidt.hsENorm_comp_le _ _).trans (by rw [HilbertSchmidt.hsENorm_adjoint])

/-- The Hilbert–Schmidt norm of the Airy kernel operator tends to `0` as `s → ∞`. -/
theorem tendsto_hsENorm_airyKernelOp :
    Tendsto (fun s => HilbertSchmidt.hsENorm (airyKernelOp s)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ => (0:ℝ≥0∞))
    (h := fun s => HilbertSchmidt.hsENorm (airyHankel s) * HilbertSchmidt.hsENorm (airyHankel s))
  · exact tendsto_const_nhds
  · have h := ENNReal.Tendsto.mul tendsto_hsENorm_airyHankel (Or.inr ENNReal.zero_ne_top)
      tendsto_hsENorm_airyHankel (Or.inr ENNReal.zero_ne_top)
    rwa [mul_zero] at h
  · exact Filter.Eventually.of_forall fun s => zero_le
  · exact Filter.Eventually.of_forall fun s => hsENorm_airyKernelOp_le s

end AiryKernelOperator

section Energy

/-- `Ai` is continuous (it is differentiable). -/
theorem continuous_airyAiReal : Continuous airyAiReal :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyAiReal x).continuousAt

/-- `Ai` is differentiable everywhere, with derivative `deriv airyAiReal`. -/
theorem hasDerivAt_airyAiReal' (u : ℝ) : HasDerivAt airyAiReal (deriv airyAiReal u) u := by
  have h := hasDerivAt_airyAiReal u
  rwa [← h.deriv] at h

/-- `Ai'` is continuous (it is differentiable). -/
theorem continuous_deriv_airyAiReal : Continuous (deriv airyAiReal) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_deriv_airyAiReal x).continuousAt

/-- The second derivative of `Ai` at a point, from the Airy ODE `Ai'' = x · Ai`. -/
theorem deriv_deriv_airyAiReal (u : ℝ) : deriv (deriv airyAiReal) u = u * airyAiReal u := by
  have h := iteratedDeriv_two_airyAiReal u
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
  exact h

/-- The Airy energy `E(t) = Ai'(t)^2 - t·Ai(t)^2`, whose derivative is `-Ai(t)^2`. -/
noncomputable def airyEnergy (t : ℝ) : ℝ := (deriv airyAiReal t)^2 - t * (airyAiReal t)^2

/-- The energy derivative identity `E'(u) = -Ai(u)^2`: the cross terms cancel by the
Airy ODE. -/
theorem hasDerivAt_airyEnergy (u : ℝ) : HasDerivAt airyEnergy (-(airyAiReal u)^2) u := by
  show HasDerivAt (fun t => (deriv airyAiReal t)^2 - t * (airyAiReal t)^2)
    (-(airyAiReal u)^2) u
  have hAi : HasDerivAt airyAiReal (deriv airyAiReal u) u := by
    have h := hasDerivAt_airyAiReal u
    rwa [← h.deriv] at h
  have hAi' : HasDerivAt (deriv airyAiReal) (u * airyAiReal u) u := by
    have h := hasDerivAt_deriv_airyAiReal u
    have hv : deriv (deriv airyAiReal) u = u * airyAiReal u := deriv_deriv_airyAiReal u
    rw [h.deriv] at hv
    rwa [hv] at h
  have h1 : HasDerivAt (fun t => (deriv airyAiReal t)^2)
      (deriv airyAiReal u * (u * airyAiReal u) + (u * airyAiReal u) * deriv airyAiReal u) u := by
    have h := hAi'.mul hAi'
    convert h using 1
    · ext t
      exact sq (deriv airyAiReal t)
    · ring
  have hsq : HasDerivAt (fun t => (airyAiReal t)^2)
      (airyAiReal u * deriv airyAiReal u + deriv airyAiReal u * airyAiReal u) u := by
    have h := hAi.mul hAi
    convert h using 1
    · ext t
      exact sq (airyAiReal t)
    · ring
  have h2 : HasDerivAt (fun t => t * (airyAiReal t)^2)
      (u * (airyAiReal u * deriv airyAiReal u + deriv airyAiReal u * airyAiReal u)
        + 1 * (airyAiReal u)^2) u := by
    have h := (hasDerivAt_id' u).mul hsq
    convert h using 1
    ring
  exact (h1.sub h2).congr_deriv (by ring)

/-- The shifted energy derivative: `u ↦ E(x + u)` has derivative `-Ai(x + u)^2`. -/
theorem hasDerivAt_airyEnergy_comp_add (x u : ℝ) :
    HasDerivAt (fun t => airyEnergy (x + t)) (-(airyAiReal (x + u))^2) u := by
  have h := (hasDerivAt_airyEnergy (x + u)).comp u
    ((hasDerivAt_const u x).add (hasDerivAt_id' u))
  exact h.congr_deriv (by ring)

/-- `Ai²` is integrable on `(a, ∞)` (dominated by `C² e^{-2t}`). -/
theorem integrable_airyAiReal_sq_Ioi (a : ℝ) :
    IntegrableOn (fun t => (airyAiReal t)^2) (Set.Ioi a) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  have hmeas : AEStronglyMeasurable (fun t => (airyAiReal t)^2)
      (volume.restrict (Set.Ioi a)) :=
    (measurable_airyAiReal.pow_const 2).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi a)),
      ‖(airyAiReal t)^2‖ ≤ ‖C^2 * Real.exp (-(2*t))‖ := by
    apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg
      (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le), ← sq_abs]
    calc |airyAiReal t|^2 ≤ (C * Real.exp (-t))^2 := pow_le_pow_left₀ (abs_nonneg _) (hC t) 2
      _ = C^2 * Real.exp (-(2*t)) := by rw [mul_pow, exp_neg_sq]
  exact ((integrableOn_exp_neg_two_mul a).const_mul (C^2)).mono hmeas hbound

/-- The shifted square `u ↦ Ai(x + u)²` is integrable on `(0, ∞)`. -/
theorem integrable_airyAiReal_sq_comp_add_Ioi (x : ℝ) :
    IntegrableOn (fun u => (airyAiReal (x + u))^2) (Set.Ioi 0) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  have hmeas : AEStronglyMeasurable (fun u => (airyAiReal (x + u))^2)
      (volume.restrict (Set.Ioi 0)) :=
    ((measurable_airyAiReal.comp (measurable_const.add measurable_id')).pow_const
      2).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioi 0)),
      ‖(airyAiReal (x + u))^2‖ ≤ ‖C^2 * Real.exp (-(2*x)) * Real.exp (-(2*u))‖ := by
    apply Filter.Eventually.of_forall
    intro u
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le), ← sq_abs]
    calc |airyAiReal (x + u)|^2 ≤ (C * Real.exp (-(x + u)))^2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hC _) 2
      _ = C^2 * Real.exp (-(2*x)) * Real.exp (-(2*u)) := by
        rw [mul_pow, exp_neg_sq, show (2:ℝ) * (x + u) = 2*x + 2*u by ring, neg_add, Real.exp_add]
        ring
  exact ((integrableOn_exp_neg_two_mul 0).const_mul (C^2 * Real.exp (-(2*x)))).mono hmeas hbound

/-- The product `u ↦ Ai(x + u) Ai(y + u)` is integrable on `(0, ∞)`. -/
theorem integrable_airyAiReal_mul_Ioi (x y : ℝ) :
    IntegrableOn (fun u => airyAiReal (x + u) * airyAiReal (y + u)) (Set.Ioi 0) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  have hmeas : AEStronglyMeasurable (fun u => airyAiReal (x + u) * airyAiReal (y + u))
      (volume.restrict (Set.Ioi 0)) :=
    ((measurable_airyAiReal.comp (measurable_const.add measurable_id')).mul
      (measurable_airyAiReal.comp (measurable_const.add measurable_id'))).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioi 0)),
      ‖airyAiReal (x + u) * airyAiReal (y + u)‖
        ≤ ‖C^2 * Real.exp (-(x + y)) * Real.exp (-(2*u))‖ := by
    apply Filter.Eventually.of_forall
    intro u
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_of_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le)]
    calc |airyAiReal (x + u)| * |airyAiReal (y + u)|
        ≤ (C * Real.exp (-(x + u))) * (C * Real.exp (-(y + u))) :=
        mul_le_mul (hC _) (hC _) (abs_nonneg _) (mul_nonneg hCpos.le (Real.exp_pos _).le)
      _ = C^2 * Real.exp (-(x + y)) * Real.exp (-(2*u)) := by
        rw [show C * Real.exp (-(x + u)) * (C * Real.exp (-(y + u)))
            = C^2 * (Real.exp (-(x + u)) * Real.exp (-(y + u))) by ring, ← Real.exp_add,
          show C^2 * Real.exp (-(x + y)) * Real.exp (-(2*u))
            = C^2 * (Real.exp (-(x + y)) * Real.exp (-(2*u))) by ring, ← Real.exp_add]
        congr 1
        ring_nf
  exact ((integrableOn_exp_neg_two_mul 0).const_mul (C^2 * Real.exp (-(x + y)))).mono hmeas
    hbound

/-- The energy has a limit at infinity: `E(t) → E(0) - ∫₀^∞ Ai²`. -/
theorem airyEnergy_tendsto_nhds : ∃ L : ℝ, Tendsto airyEnergy atTop (𝓝 L) := by
  refine ⟨airyEnergy 0 + ∫ t in Set.Ioi 0, (-(airyAiReal t)^2), ?_⟩
  have hint : IntegrableOn (fun t => -(airyAiReal t)^2) (Set.Ioi 0) :=
    (integrable_airyAiReal_sq_Ioi 0).neg
  have h1 : Tendsto (fun t : ℝ => ∫ x in (0:ℝ)..t, (-(airyAiReal x)^2)) atTop
      (𝓝 (∫ x in Set.Ioi 0, (-(airyAiReal x)^2))) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  refine (tendsto_const_nhds.add h1).congr fun t => ?_
  have hftc : ∫ x in (0:ℝ)..t, (-(airyAiReal x)^2) = airyEnergy t - airyEnergy 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_airyEnergy u)
      ((continuous_airyAiReal.pow 2).neg.intervalIntegrable 0 t)
  rw [hftc]
  ring

/-- The energy tends to `0` at infinity.  The limit `L` exists by
`airyEnergy_tendsto_nhds`; `L ≥ 0` since `(Ai'(t))² → L`; and `L > 0` would force
`Ai'` to keep a constant sign of magnitude `≥ √(L/2)` eventually (by continuity and the
intermediate value theorem), which is incompatible with `Ai(t) → 0`. -/
theorem airyEnergy_tendsto_zero : Tendsto airyEnergy atTop (𝓝 0) := by
  obtain ⟨C, hCpos, hC⟩ := airyAiReal_abs_le_exp'
  obtain ⟨L, hL⟩ := airyEnergy_tendsto_nhds
  -- `t · Ai(t)² → 0`, by `0 ≤ t Ai(t)² ≤ C² e^{-t}` for `t ≥ 0`.
  have htwist : Tendsto (fun t : ℝ => t * (airyAiReal t)^2) atTop (𝓝 0) := by
    apply squeeze_zero'
      (by filter_upwards [Filter.eventually_ge_atTop 0] with t ht
          exact mul_nonneg ht (sq_nonneg _))
      (by filter_upwards [Filter.eventually_ge_atTop 0] with t ht
          calc t * (airyAiReal t)^2 = t * |airyAiReal t|^2 := by rw [sq_abs]
            _ ≤ t * (C * Real.exp (-t))^2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hC t) 2) ht
            _ = C^2 * (t * Real.exp (-(2*t))) := by rw [mul_pow, exp_neg_sq]; ring
            _ ≤ C^2 * Real.exp (-t) := by
              apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
              have h1 : t ≤ Real.exp t :=
                (by linarith : t ≤ t + 1).trans (Real.add_one_le_exp t)
              calc t * Real.exp (-(2*t)) ≤ Real.exp t * Real.exp (-(2*t)) :=
                  mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
                _ = Real.exp (-t) := by rw [← Real.exp_add]; ring_nf)
      (by have h := (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (C^2)
          rwa [mul_zero] at h)
  -- `(Ai'(t))² = E(t) + t Ai(t)² → L`, hence `L ≥ 0`.
  have hlim2 : Tendsto (fun t : ℝ => (deriv airyAiReal t)^2) atTop (𝓝 L) := by
    have h : Tendsto (fun t => airyEnergy t + t * (airyAiReal t)^2) atTop (𝓝 (L + 0)) :=
      hL.add htwist
    rw [add_zero] at h
    exact h.congr fun t => by
      show (deriv airyAiReal t)^2 - t * (airyAiReal t)^2 + t * (airyAiReal t)^2
        = (deriv airyAiReal t)^2
      ring
  have hLge : (0:ℝ) ≤ L :=
    ge_of_tendsto hlim2 (Filter.Eventually.of_forall fun t => sq_nonneg (deriv airyAiReal t))
  -- `L ≤ 0`: otherwise `Ai'` keeps one sign of magnitude `≥ √(L/2)` eventually.
  have hLle : L ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hc_pos : (0:ℝ) < Real.sqrt (L/2) := Real.sqrt_pos_of_pos (by linarith)
    have hev : ∀ᶠ t in atTop, L / 2 < (deriv airyAiReal t)^2 :=
      hlim2.eventually (Ioi_mem_nhds (show L / 2 < L by linarith))
    obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hev
    set B₀ := max B 0 with hB₀
    have hc_lt : ∀ t, B₀ ≤ t → Real.sqrt (L/2) < |deriv airyAiReal t| := by
      intro t ht
      have h1 : L / 2 < (deriv airyAiReal t)^2 := hB t (le_trans (le_max_left _ _) ht)
      have h2 : Real.sqrt (L / 2) < Real.sqrt ((deriv airyAiReal t)^2) :=
        Real.sqrt_lt_sqrt (by linarith) h1
      rwa [Real.sqrt_sq_eq_abs] at h2
    have hsign : (∀ t, B₀ ≤ t → Real.sqrt (L/2) < deriv airyAiReal t)
        ∨ (∀ t, B₀ ≤ t → deriv airyAiReal t < -Real.sqrt (L/2)) := by
      by_contra h
      push Not at h
      obtain ⟨⟨t₁, ht₁, h₁⟩, ⟨t₂, ht₂, h₂⟩⟩ := h
      have h₁' : deriv airyAiReal t₁ < -Real.sqrt (L/2) := by
        have h := hc_lt t₁ ht₁
        rcases lt_abs.mp h with h' | h'
        · linarith
        · linarith
      have h₂' : Real.sqrt (L/2) < deriv airyAiReal t₂ := by
        have h := hc_lt t₂ ht₂
        rcases lt_abs.mp h with h' | h'
        · exact h'
        · linarith
      rcases le_total t₁ t₂ with hle | hle
      · have hivt := intermediate_value_Icc hle continuous_deriv_airyAiReal.continuousOn
        have h0 : (0:ℝ) ∈ Set.Icc (deriv airyAiReal t₁) (deriv airyAiReal t₂) :=
          ⟨by linarith, by linarith⟩
        obtain ⟨ξ, hξ, hξ0⟩ := hivt h0
        have := hc_lt ξ (le_trans ht₁ hξ.1)
        rw [hξ0, abs_zero] at this
        exact absurd this (not_lt.mpr hc_pos.le)
      · have hivt := intermediate_value_Icc' hle continuous_deriv_airyAiReal.continuousOn
        have h0 : (0:ℝ) ∈ Set.Icc (deriv airyAiReal t₁) (deriv airyAiReal t₂) :=
          ⟨by linarith, by linarith⟩
        obtain ⟨ξ, hξ, hξ0⟩ := hivt h0
        have := hc_lt ξ (le_trans ht₂ hξ.1)
        rw [hξ0, abs_zero] at this
        exact absurd this (not_lt.mpr hc_pos.le)
    -- `Ai(t) → 0` as `t → ∞` (squeezed against `C e^{-t}`).
    have hAi0 : Tendsto airyAiReal atTop (𝓝 0) := by
      have hbound : ∀ᶠ u in atTop, ‖airyAiReal u‖ ≤ C * Real.exp (-u) :=
        Filter.Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs]
          exact hC u
      apply squeeze_zero_norm' hbound
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul C
      rwa [mul_zero] at h
    rcases hsign with hgt | hlt
    · -- case `Ai' > √(L/2)` eventually: `Ai` grows without bound, contradicting `Ai → 0`.
      have hmono : ∀ t, B₀ ≤ t → airyAiReal B₀ + Real.sqrt (L/2) * (t - B₀)
          ≤ airyAiReal t := by
        intro t ht
        have hftc : ∫ u in B₀..t, deriv airyAiReal u = airyAiReal t - airyAiReal B₀ :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_airyAiReal' u)
            (continuous_deriv_airyAiReal.intervalIntegrable B₀ t)
        have hle : Real.sqrt (L/2) * (t - B₀) ≤ ∫ u in B₀..t, deriv airyAiReal u := by
          have hconst : ∫ u in B₀..t, (Real.sqrt (L/2) : ℝ) = Real.sqrt (L/2) * (t - B₀) := by
            rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
          rw [← hconst]
          apply intervalIntegral.integral_mono_on ht intervalIntegrable_const
            (continuous_deriv_airyAiReal.intervalIntegrable B₀ t)
          intro u hu
          exact le_of_lt (hgt u hu.1)
        rw [hftc] at hle
        linarith
      have htend : Tendsto (fun t : ℝ => airyAiReal B₀ + Real.sqrt (L/2) * (t - B₀))
          atTop atTop := by
        have hbase : Tendsto (fun t : ℝ => t - B₀) atTop atTop :=
          (tendsto_atTop_add_const_right atTop (-B₀) tendsto_id).congr
            (fun t => by simp only [id_eq]; ring)
        exact tendsto_atTop_add_const_left atTop (airyAiReal B₀)
          (Filter.Tendsto.const_mul_atTop hc_pos hbase)
      obtain ⟨t, ⟨h1, h2⟩, h3⟩ := (((htend.eventually (Filter.eventually_gt_atTop 1)).and
        (hAi0.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)))).and
        (Filter.eventually_ge_atTop B₀)).exists
      have := hmono t h3
      linarith
    · -- case `Ai' < -√(L/2)` eventually: `Ai → -∞`, contradicting `Ai → 0`.
      have hanti : ∀ t, B₀ ≤ t → airyAiReal t
          ≤ airyAiReal B₀ - Real.sqrt (L/2) * (t - B₀) := by
        intro t ht
        have hftc : ∫ u in B₀..t, deriv airyAiReal u = airyAiReal t - airyAiReal B₀ :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_airyAiReal' u)
            (continuous_deriv_airyAiReal.intervalIntegrable B₀ t)
        have hle : ∫ u in B₀..t, deriv airyAiReal u ≤ -Real.sqrt (L/2) * (t - B₀) := by
          have hconst : ∫ u in B₀..t, (-Real.sqrt (L/2) : ℝ) = -Real.sqrt (L/2) * (t - B₀) := by
            rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
          rw [← hconst]
          apply intervalIntegral.integral_mono_on ht
            (continuous_deriv_airyAiReal.intervalIntegrable B₀ t) intervalIntegrable_const
          intro u hu
          exact le_of_lt (hlt u hu.1)
        rw [hftc] at hle
        linarith
      have htend : Tendsto (fun t : ℝ => airyAiReal B₀ - Real.sqrt (L/2) * (t - B₀))
          atTop atBot := by
        have hbase : Tendsto (fun t : ℝ => t - B₀) atTop atTop :=
          (tendsto_atTop_add_const_right atTop (-B₀) tendsto_id).congr
            (fun t => by simp only [id_eq]; ring)
        have h2 := Filter.Tendsto.const_mul_atTop_of_neg (by linarith : -Real.sqrt (L/2) < 0)
          hbase
        have h3 := tendsto_atBot_add_const_left atTop (airyAiReal B₀) h2
        exact h3.congr fun t => by ring
      obtain ⟨t, ⟨h1, h2⟩, h3⟩ := (((htend.eventually (Iio_mem_atBot (-1))).and
        (hAi0.eventually (Ioi_mem_nhds (by norm_num : (-1:ℝ) < 0)))).and
        (Filter.eventually_ge_atTop B₀)).exists
      have := hanti t h3
      linarith
  -- hence `L = 0`.
  have hL0 : L = 0 := le_antisymm hLle hLge
  rwa [hL0] at hL

/-- The energy identity (the diagonal case of the Airy kernel closed form):
`∫₀^∞ Ai(x + u)² du = Ai'(x)² - x Ai(x)²`. -/
theorem airyAiReal_sq_integral (x : ℝ) :
    ∫ u in Set.Ioi 0, (airyAiReal (x + u))^2
      = (deriv airyAiReal x)^2 - x * (airyAiReal x)^2 := by
  have hF : ∀ u : ℝ, HasDerivAt (fun u => -airyEnergy (x + u)) ((airyAiReal (x + u))^2) u := by
    intro u
    have h := (hasDerivAt_airyEnergy_comp_add x u).neg
    rwa [neg_neg] at h
  have hT : Tendsto (fun u => -airyEnergy (x + u)) atTop (𝓝 0) := by
    have h := airyEnergy_tendsto_zero.comp (tendsto_atTop_add_const_left atTop x tendsto_id)
    have h2 := h.neg
    rwa [neg_zero] at h2
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun u : ℝ => -airyEnergy (x + u)) (f' := fun u : ℝ => (airyAiReal (x + u))^2)
    ((hF 0).continuousAt.continuousWithinAt) (fun u _ => hF u)
    (integrable_airyAiReal_sq_comp_add_Ioi x) hT
  rw [hftc, add_zero]
  show 0 - -((deriv airyAiReal x)^2 - x * (airyAiReal x)^2)
    = (deriv airyAiReal x)^2 - x * (airyAiReal x)^2
  ring

end Energy

end AiryKernel
