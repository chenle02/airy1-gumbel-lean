/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Gaussian tail asymptotics (the Mills ratio)

We study the Gaussian tail integral with temperature parameter `T > 0`,

`G_T(b) = ∫_b^∞ exp(-d²/(4T)) dd`,     (`gaussianTail T b`)

which is the integral form of the Mills ratio.  The classical two-term expansion

`G_T(b) = (2T/b) exp(-b²/(4T)) (1 - 2T/b² + O_T(b⁻⁴))`     as `b → ∞`

is proved here in exact `=O` form (`gaussianTail_asymptotic`), together with the standard
Mills upper bound `G_T(b) ≤ (2T/b) exp(-b²/(4T))` and the asymptotic equivalence
`G_T(b) ~ (2T/b) exp(-b²/(4T))`.

## Main results

* `integrableOn_exp_neg_sq_div_Ioi`: the integrand `exp(-d²/(4T))` is integrable on `(b, ∞)`.
* `gaussianTail_le`: the Mills upper bound `G_T(b) ≤ (2T/b) exp(-b²/(4T))`.
* `gaussianTail_eq`: one round of integration by parts,
  `G_T(b) = (2T/b) exp(-b²/(4T)) - 2T ∫_b^∞ exp(-d²/(4T))/d² dd`.
* `gaussianTail_sub_eq`: the exact error identity
  `G_T(b) - (2T/b) exp(-b²/(4T)) (1 - 2T/b²) = 12 T² ∫_b^∞ exp(-d²/(4T))/d⁴ dd`.
* `gaussianTail_asymptotic`: the `=O` two-term expansion (the form the paper uses).
* `gaussianTail_isEquivalent`: `gaussianTail T ~[atTop] fun b => (2T/b) exp(-b²/(4T))`.

## Proof outline

Writing `φ(d) = exp(-d²/(4T))`, one has `φ'(d) = -(d/(2T)) φ(d)`, so that on `(b, ∞)`
`φ(d) = (2T/d) · (-φ'(d)) ≤ (2T/b) · (-φ'(d))`; integrating gives the Mills bound by FTC.
For the expansion, two rounds of integration by parts with `u = -(2T)/d` and `u = -(2T)/d³`
give the exact identities `G_T = (2T/b)φ(b) - 2T ∫ φ/d²` and
`∫ φ/d² = (2T/b³)φ(b) - 6T ∫ φ/d⁴`; combining,
`G_T(b) - (2T/b)φ(b)(1 - 2T/b²) = 12 T² ∫_b^∞ φ(d)/d⁴ dd`, and the remainder integral is
nonnegative and bounded by `G_T(b)/b⁴ ≤ (2T/b)φ(b)/b⁴`.
-/

open Asymptotics Filter MeasureTheory Set

open scoped Asymptotics Topology

/-- The Gaussian tail integral with temperature `T`: `G_T(b) = ∫_b^∞ exp(-d²/(4T)) dd`. -/
noncomputable def gaussianTail (T b : ℝ) : ℝ := ∫ d in Set.Ioi b, Real.exp (- d^2 / (4 * T))

/-- The derivative of `d ↦ exp(-d²/(4T))` is `-(d/(2T)) exp(-d²/(4T))`. -/
theorem hasDerivAt_exp_neg_sq_div (hT : 0 < T) (d : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-x^2/(4*T))) (-(d/(2*T)) * Real.exp (-d^2/(4*T))) d := by
  have h := (Real.hasDerivAt_exp (-d^2/(4*T))).comp d
    (((hasDerivAt_pow 2 d).neg).div_const (4*T))
  convert h using 1
  · rfl
  · field_simp [hT.ne']
    ring

/-- The integrand `exp(-d²/(4T))` is integrable on `(b, ∞)` for `0 < T`. -/
theorem integrableOn_exp_neg_sq_div_Ioi (hT : 0 < T) (b : ℝ) :
    IntegrableOn (fun d : ℝ => Real.exp (-d^2/(4*T))) (Set.Ioi b) := by
  have h : (fun d : ℝ => Real.exp (-d^2/(4*T))) = fun d => Real.exp (-(4*T)⁻¹ * d^2) := by
    funext d
    congr 1
    ring
  rw [h]
  exact (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < (4*T)⁻¹)).integrableOn

/-- The derivative factor `(d/(2T)) exp(-d²/(4T))` is integrable on `(b, ∞)` for `0 < T`. -/
theorem integrableOn_mul_exp_neg_sq_div_Ioi (hT : 0 < T) (b : ℝ) :
    IntegrableOn (fun d : ℝ => (d/(2*T)) * Real.exp (-d^2/(4*T))) (Set.Ioi b) := by
  have h : (fun d : ℝ => (d/(2*T)) * Real.exp (-d^2/(4*T)))
      = fun d => (2*T)⁻¹ * (d * Real.exp (-(4*T)⁻¹ * d^2)) := by
    funext d
    have e1 : -d^2/(4*T) = -(4*T)⁻¹ * d^2 := by ring
    rw [e1]
    ring
  rw [h]
  exact ((integrable_mul_exp_neg_mul_sq (by positivity : (0:ℝ) < (4*T)⁻¹)).const_mul _).integrableOn

/-- The derivative `-(d/(2T)) exp(-d²/(4T))` is integrable on `(b, ∞)` for `0 < T`. -/
theorem integrableOn_neg_mul_exp_neg_sq_div_Ioi (hT : 0 < T) (b : ℝ) :
    IntegrableOn (fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))) (Set.Ioi b) := by
  have hfun : (fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T)))
      = fun d => -((d/(2*T)) * Real.exp (-d^2/(4*T))) := funext fun d => neg_mul _ _
  rw [hfun]
  exact (integrableOn_mul_exp_neg_sq_div_Ioi hT b).neg

/-- `exp(-d²/(4T)) → 0` as `d → ∞` for `0 < T`. -/
theorem tendsto_exp_neg_sq_div_atTop (hT : 0 < T) :
    Tendsto (fun d : ℝ => Real.exp (-d^2/(4*T))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun d : ℝ => d^2 * (4*T)⁻¹) atTop atTop :=
    Tendsto.atTop_mul_const (by positivity : (0:ℝ) < (4*T)⁻¹) (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun d : ℝ => -(d^2 * (4*T)⁻¹)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h1
  have h3 := Real.tendsto_exp_atBot.comp h2
  refine h3.congr' (Eventually.of_forall fun d => ?_)
  simp only [Function.comp_apply]
  congr 1
  ring

/-- FTC on `(b, ∞)`: `∫_b^∞ -(d/(2T)) exp(-d²/(4T)) dd = -exp(-b²/(4T))`. -/
theorem integral_Ioi_neg_mul_exp_neg_sq_div (hT : 0 < T) (b : ℝ) :
    ∫ d in Set.Ioi b, -(d/(2*T)) * Real.exp (-d^2/(4*T)) = - Real.exp (-b^2/(4*T)) := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun d : ℝ => Real.exp (-d^2/(4*T)))
    (f' := fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))) (a := b) (m := 0)
    (fun x _ => hasDerivAt_exp_neg_sq_div hT x)
    (integrableOn_neg_mul_exp_neg_sq_div_Ioi hT b)
    (tendsto_exp_neg_sq_div_atTop hT)
  rwa [zero_sub] at h

/-- The Mills upper bound: `G_T(b) ≤ (2T/b) exp(-b²/(4T))` for `0 < T`, `0 < b`.

On `(b, ∞)`, `φ(d) = (2T/d) · (-φ'(d)) ≤ (2T/b) · (-φ'(d))`, and `∫ -φ' = φ(b)` by FTC. -/
theorem gaussianTail_le (hT : 0 < T) {b : ℝ} (hb : 0 < b) :
    gaussianTail T b ≤ (2*T/b) * Real.exp (-b^2/(4*T)) := by
  have hpt : ∀ d ∈ Set.Ioi b, Real.exp (-d^2/(4*T))
      ≤ (2*T/b) * (-( -(d/(2*T)) * Real.exp (-d^2/(4*T)))) := by
    intro d hd
    have hd0 : (0:ℝ) < d := hb.trans hd
    have hnn : (0:ℝ) ≤ - (-(d/(2*T)) * Real.exp (-d^2/(4*T))) := by
      simp only [neg_mul, neg_neg]
      positivity
    have heq : Real.exp (-d^2/(4*T)) = (2*T/d) * (- (-(d/(2*T)) * Real.exp (-d^2/(4*T)))) := by
      field_simp [hT.ne', hd0.ne']
    have hmono : (2*T/d) ≤ (2*T/b) := by
      rw [show (2:ℝ)*T/d = (2*T) * (1/d) by ring, show (2:ℝ)*T/b = (2*T) * (1/b) by ring]
      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hb hd.le) (by positivity)
    calc Real.exp (-d^2/(4*T))
        = (2*T/d) * (- (-(d/(2*T)) * Real.exp (-d^2/(4*T)))) := heq
      _ ≤ (2*T/b) * (- (-(d/(2*T)) * Real.exp (-d^2/(4*T)))) :=
        mul_le_mul_of_nonneg_right hmono hnn
  calc gaussianTail T b = ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) := rfl
    _ ≤ ∫ d in Set.Ioi b, (2*T/b) * (-(-(d/(2*T)) * Real.exp (-d^2/(4*T)))) :=
        setIntegral_mono_on (integrableOn_exp_neg_sq_div_Ioi hT b)
          (Integrable.const_mul ((integrableOn_neg_mul_exp_neg_sq_div_Ioi hT b).neg) _)
          measurableSet_Ioi hpt
    _ = (2*T/b) * (∫ d in Set.Ioi b, -(-(d/(2*T)) * Real.exp (-d^2/(4*T)))) := by
        rw [integral_const_mul]
    _ = (2*T/b) * Real.exp (-b^2/(4*T)) := by
        rw [integral_neg, integral_Ioi_neg_mul_exp_neg_sq_div hT b, neg_neg]

/-- `exp(-d²/(4T))/dᵏ` is integrable on `(b, ∞)` for `0 < T`, `0 < b` (comparison with
`exp(-d²/(4T))/bᵏ`). -/
theorem integrableOn_exp_neg_sq_div_div_pow (hT : 0 < T) {b : ℝ} (hb : 0 < b) (k : ℕ) :
    IntegrableOn (fun d : ℝ => Real.exp (-d^2/(4*T)) / d^k) (Set.Ioi b) := by
  have hg : MeasureTheory.Integrable (fun d : ℝ => Real.exp (-d^2/(4*T)) * (b^k)⁻¹)
      (volume.restrict (Set.Ioi b)) :=
    MeasureTheory.Integrable.mul_const (integrableOn_exp_neg_sq_div_Ioi hT b) _
  apply hg.mono' ?_ ?_
  · have hφ : Continuous fun d : ℝ => Real.exp (-d^2/(4*T)) := by fun_prop
    have hp : Continuous fun d : ℝ => d^k := by fun_prop
    have hcon : ContinuousOn (fun d : ℝ => Real.exp (-d^2/(4*T)) / d^k) (Set.Ioi b) := by
      apply ContinuousOn.div hφ.continuousOn hp.continuousOn
      intro x hx
      exact pow_ne_zero k (hb.trans hx).ne'
    exact hcon.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with d hd
    have hd0 : (0:ℝ) < d := hb.trans hd
    rw [Real.norm_of_nonneg (div_nonneg (Real.exp_nonneg _) (pow_nonneg hd0.le _))]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ (pow_pos hd0 k) (pow_pos hb k)).2 (pow_le_pow_left₀ hb.le hd.le k))
      (Real.exp_nonneg _)

/-- Integration by parts on `[b, X]`: with `u = -(2T)/d` and `v = exp(-d²/(4T))`,
`∫_b^X φ = -(2T/X)φ(X) + (2T/b)φ(b) - 2T ∫_b^X φ(d)/d² dd`. -/
theorem intervalIntegral_exp_neg_sq_div (hT : 0 < T) {b X : ℝ} (hb : 0 < b) (hbX : b ≤ X) :
    ∫ d in b..X, Real.exp (-d^2/(4*T))
      = -(2*T/X) * Real.exp (-X^2/(4*T)) + (2*T/b) * Real.exp (-b^2/(4*T))
        - 2*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2 := by
  have hu : ∀ x ∈ Set.uIcc b X, HasDerivAt (fun d : ℝ => -(2*T/d)) (2*T/x^2) x := by
    intro x hx
    rw [Set.uIcc_of_le hbX] at hx
    have hx0 : x ≠ 0 := (hb.trans_le hx.1).ne'
    have h := ((hasDerivAt_const x (2*T)).div (hasDerivAt_id' x) hx0).neg
    convert h using 1
    field_simp [hx0]
    ring
  have hv : ∀ x ∈ Set.uIcc b X,
      HasDerivAt (fun d : ℝ => Real.exp (-d^2/(4*T))) (-(x/(2*T)) * Real.exp (-x^2/(4*T))) x :=
    fun x _ => hasDerivAt_exp_neg_sq_div hT x
  have hu' : IntervalIntegrable (fun d : ℝ => 2*T/d^2) volume b X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbX]
    have hp : Continuous fun d : ℝ => d^2 := by fun_prop
    exact continuousOn_const.div hp.continuousOn
      (fun x hx => pow_ne_zero 2 (hb.trans_le hx.1).ne')
  have hv' : IntervalIntegrable (fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))) volume b X := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))).continuousOn
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun d : ℝ => -(2*T/d)) (u' := fun d : ℝ => 2*T/d^2)
    (v := fun d : ℝ => Real.exp (-d^2/(4*T)))
    (v' := fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))) hu hv hu' hv'
  have h1 : ∫ d in b..X, -(2*T/d) * (-(d/(2*T)) * Real.exp (-d^2/(4*T)))
      = ∫ d in b..X, Real.exp (-d^2/(4*T)) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hbX]
    intro x hx
    have hx0 : x ≠ 0 := (hb.trans_le hx.1).ne'
    field_simp [hT.ne', hx0]
  have h2 : ∫ d in b..X, (2*T/d^2) * Real.exp (-d^2/(4*T))
      = 2*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hbX]
    intro x hx
    ring
  rw [h1, h2] at hibp
  linear_combination hibp

/-- One round of integration by parts for the Gaussian tail:
`G_T(b) = (2T/b) exp(-b²/(4T)) - 2T ∫_b^∞ exp(-d²/(4T))/d² dd`. -/
theorem gaussianTail_eq (hT : 0 < T) {b : ℝ} (hb : 0 < b) :
    gaussianTail T b = (2*T/b) * Real.exp (-b^2/(4*T))
      - 2*T * ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^2 := by
  have hlimI : Tendsto (fun X : ℝ => ∫ d in b..X, Real.exp (-d^2/(4*T))) atTop
      (𝓝 (gaussianTail T b)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi b
      (integrableOn_exp_neg_sq_div_Ioi hT b) tendsto_id
  have hlimR : Tendsto (fun X : ℝ => ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2) atTop
      (𝓝 (∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^2)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi b
      (integrableOn_exp_neg_sq_div_div_pow hT hb 2) tendsto_id
  have hlimB : Tendsto (fun X : ℝ => -(2*T/X) * Real.exp (-X^2/(4*T))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun X : ℝ => 2*T/X) atTop (𝓝 0) := by
      have heq : (fun X : ℝ => 2*T/X) = fun X => (2*T) * X⁻¹ :=
        funext fun X => div_eq_mul_inv _ _
      rw [heq]
      simpa using tendsto_inv_atTop_zero.const_mul (2*T)
    have h3 := ((h1.neg).mul (tendsto_exp_neg_sq_div_atTop hT))
    rw [neg_zero, zero_mul] at h3
    exact h3
  have h_eq : ∀ᶠ X : ℝ in atTop, ∫ d in b..X, Real.exp (-d^2/(4*T))
      = -(2*T/X) * Real.exp (-X^2/(4*T)) + (2*T/b) * Real.exp (-b^2/(4*T))
        - 2*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2 :=
    (eventually_gt_atTop b).mono fun X hX => intervalIntegral_exp_neg_sq_div hT hb hX.le
  have hlimAll : Tendsto (fun X : ℝ => -(2*T/X) * Real.exp (-X^2/(4*T))
      + (2*T/b) * Real.exp (-b^2/(4*T))
      - 2*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2) atTop
      (𝓝 (0 + (2*T/b) * Real.exp (-b^2/(4*T))
        - 2*T * ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^2)) :=
    (hlimB.add tendsto_const_nhds).sub (hlimR.const_mul (2*T))
  have hfin := tendsto_nhds_unique (Tendsto.congr' h_eq hlimI) hlimAll
  rwa [zero_add] at hfin

/-- Second round of integration by parts on `[b, X]`: with `u = -(2T)/d³`,
`∫_b^X φ(d)/d² dd = -(2T/X³)φ(X) + (2T/b³)φ(b) - 6T ∫_b^X φ(d)/d⁴ dd`. -/
theorem intervalIntegral_exp_neg_sq_div_div_sq (hT : 0 < T) {b X : ℝ} (hb : 0 < b) (hbX : b ≤ X) :
    ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2
      = -(2*T/X^3) * Real.exp (-X^2/(4*T)) + (2*T/b^3) * Real.exp (-b^2/(4*T))
        - 6*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^4 := by
  have hu : ∀ x ∈ Set.uIcc b X, HasDerivAt (fun d : ℝ => -(2*T/d^3)) (6*T/x^4) x := by
    intro x hx
    rw [Set.uIcc_of_le hbX] at hx
    have hx0 : x ≠ 0 := (hb.trans_le hx.1).ne'
    have h := ((hasDerivAt_const x (2*T)).div ((hasDerivAt_pow 3 x)) (pow_ne_zero 3 hx0)).neg
    convert h using 1
    field_simp [hx0]
    ring
  have hv : ∀ x ∈ Set.uIcc b X,
      HasDerivAt (fun d : ℝ => Real.exp (-d^2/(4*T))) (-(x/(2*T)) * Real.exp (-x^2/(4*T))) x :=
    fun x _ => hasDerivAt_exp_neg_sq_div hT x
  have hu' : IntervalIntegrable (fun d : ℝ => 6*T/d^4) volume b X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbX]
    have hp : Continuous fun d : ℝ => d^4 := by fun_prop
    exact continuousOn_const.div hp.continuousOn
      (fun x hx => pow_ne_zero 4 (hb.trans_le hx.1).ne')
  have hv' : IntervalIntegrable (fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))) volume b X := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))).continuousOn
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun d : ℝ => -(2*T/d^3)) (u' := fun d : ℝ => 6*T/d^4)
    (v := fun d : ℝ => Real.exp (-d^2/(4*T)))
    (v' := fun d : ℝ => -(d/(2*T)) * Real.exp (-d^2/(4*T))) hu hv hu' hv'
  have h1 : ∫ d in b..X, -(2*T/d^3) * (-(d/(2*T)) * Real.exp (-d^2/(4*T)))
      = ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2 := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hbX]
    intro x hx
    have hx0 : x ≠ 0 := (hb.trans_le hx.1).ne'
    field_simp [hT.ne', hx0]
  have h2 : ∫ d in b..X, (6*T/d^4) * Real.exp (-d^2/(4*T))
      = 6*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^4 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hbX]
    intro x hx
    ring
  rw [h1, h2] at hibp
  linear_combination hibp

/-- The second IBP for the Gaussian tail:
`∫_b^∞ φ(d)/d² dd = (2T/b³) φ(b) - 6T ∫_b^∞ φ(d)/d⁴ dd`. -/
theorem integral_Ioi_exp_neg_sq_div_div_sq (hT : 0 < T) {b : ℝ} (hb : 0 < b) :
    ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^2
      = (2*T/b^3) * Real.exp (-b^2/(4*T))
        - 6*T * ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4 := by
  have hlimI : Tendsto (fun X : ℝ => ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2) atTop
      (𝓝 (∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^2)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi b
      (integrableOn_exp_neg_sq_div_div_pow hT hb 2) tendsto_id
  have hlimR : Tendsto (fun X : ℝ => ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^4) atTop
      (𝓝 (∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi b
      (integrableOn_exp_neg_sq_div_div_pow hT hb 4) tendsto_id
  have hlimB : Tendsto (fun X : ℝ => -(2*T/X^3) * Real.exp (-X^2/(4*T))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun X : ℝ => 2*T/X^3) atTop (𝓝 0) := by
      have heq : (fun X : ℝ => 2*T/X^3) = fun X => (2*T) * (X^3)⁻¹ :=
        funext fun X => div_eq_mul_inv _ _
      rw [heq]
      have hbase : Tendsto (fun X : ℝ => (X^3)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : (3:ℕ) ≠ 0))
      simpa using hbase.const_mul (2*T)
    have h3 := ((h1.neg).mul (tendsto_exp_neg_sq_div_atTop hT))
    rw [neg_zero, zero_mul] at h3
    exact h3
  have h_eq : ∀ᶠ X : ℝ in atTop, ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^2
      = -(2*T/X^3) * Real.exp (-X^2/(4*T)) + (2*T/b^3) * Real.exp (-b^2/(4*T))
        - 6*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^4 :=
    (eventually_gt_atTop b).mono fun X hX => intervalIntegral_exp_neg_sq_div_div_sq hT hb hX.le
  have hlimAll : Tendsto (fun X : ℝ => -(2*T/X^3) * Real.exp (-X^2/(4*T))
      + (2*T/b^3) * Real.exp (-b^2/(4*T))
      - 6*T * ∫ d in b..X, Real.exp (-d^2/(4*T)) / d^4) atTop
      (𝓝 (0 + (2*T/b^3) * Real.exp (-b^2/(4*T))
        - 6*T * ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4)) :=
    (hlimB.add tendsto_const_nhds).sub (hlimR.const_mul (6*T))
  have hfin := tendsto_nhds_unique (Tendsto.congr' h_eq hlimI) hlimAll
  rwa [zero_add] at hfin

/-- The exact two-term error identity for the Gaussian tail:
`G_T(b) - (2T/b) exp(-b²/(4T)) (1 - 2T/b²) = 12 T² ∫_b^∞ exp(-d²/(4T))/d⁴ dd`. -/
theorem gaussianTail_sub_eq (hT : 0 < T) {b : ℝ} (hb : 0 < b) :
    gaussianTail T b - (2*T/b) * Real.exp (-b^2/(4*T)) * (1 - 2*T/b^2)
      = 12 * T^2 * ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4 := by
  rw [gaussianTail_eq hT hb, integral_Ioi_exp_neg_sq_div_div_sq hT hb]
  field_simp [hb.ne']
  ring

/-- The Gaussian tail two-term asymptotic expansion with quartic remainder, in exact
big-`O` form: as `b → ∞`,
`G_T(b) - (2T/b) exp(-b²/(4T)) (1 - 2T/b²) = O((2T/b) exp(-b²/(4T)) · b⁻⁴)`.

In fact the difference is *nonnegative* and equal to `12 T² ∫_b^∞ exp(-d²/(4T))/d⁴ dd`
(`gaussianTail_sub_eq`); the bound then follows from `∫ φ/d⁴ ≤ G_T(b)/b⁴` and the Mills
bound `gaussianTail_le`. -/
theorem gaussianTail_asymptotic (T : ℝ) (hT : 0 < T) :
    (fun b => gaussianTail T b - (2*T/b) * Real.exp (-b^2/(4*T)) * (1 - 2*T/b^2))
      =O[Filter.atTop] (fun b => (2*T/b) * Real.exp (-b^2/(4*T)) * b^(-4:ℝ)) := by
  rw [isBigO_iff]
  refine ⟨12 * T^2, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with b hb
  have hb0 : (0:ℝ) < b := one_pos.trans_le hb
  have hrp : b^(-4:ℝ) = (b^4)⁻¹ := by
    rw [← Real.rpow_natCast b 4, ← Real.rpow_neg hb0.le]
    norm_cast
  rw [gaussianTail_sub_eq hT hb0]
  have hI4nn : 0 ≤ ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4 :=
    setIntegral_nonneg measurableSet_Ioi fun d hd =>
      div_nonneg (Real.exp_nonneg _) (pow_nonneg (hb0.trans hd).le _)
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 12 * T^2) hI4nn)]
  have hG0 : (0:ℝ) < (2*T/b) * Real.exp (-b^2/(4*T)) * b^(-4:ℝ) := by positivity
  rw [Real.norm_of_nonneg hG0.le, hrp]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 12 * T^2)
  have hI4le : ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4 ≤ gaussianTail T b / b^4 := by
    have hle : ∀ d ∈ Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4 ≤ Real.exp (-d^2/(4*T)) / b^4 := by
      intro d hd
      have hd0 : (0:ℝ) < d := hb0.trans hd
      exact (div_le_div_iff_of_pos_left (Real.exp_pos _) (by positivity) (by positivity)).2
        (pow_le_pow_left₀ hb0.le hd.le 4)
    have hg4 : IntegrableOn (fun d => Real.exp (-d^2/(4*T)) / b^4) (Set.Ioi b) := by
      have hfun : (fun d : ℝ => Real.exp (-d^2/(4*T)) / b^4)
          = fun d => Real.exp (-d^2/(4*T)) * (b^4)⁻¹ := funext fun d => div_eq_mul_inv _ _
      rw [hfun]
      exact Integrable.mul_const (integrableOn_exp_neg_sq_div_Ioi hT b) _
    calc ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4
        ≤ ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / b^4 :=
          setIntegral_mono_on (integrableOn_exp_neg_sq_div_div_pow hT hb0 4)
            hg4 measurableSet_Ioi hle
      _ = (∫ d in Set.Ioi b, Real.exp (-d^2/(4*T))) / b^4 := by
          simp only [div_eq_mul_inv, MeasureTheory.integral_mul_const]
      _ = gaussianTail T b / b^4 := rfl
  calc ∫ d in Set.Ioi b, Real.exp (-d^2/(4*T)) / d^4
      ≤ gaussianTail T b / b^4 := hI4le
    _ ≤ ((2*T/b) * Real.exp (-b^2/(4*T))) / b^4 :=
        (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < b^4)).2 (gaussianTail_le hT hb0)
    _ = (2*T/b) * Real.exp (-b^2/(4*T)) * (b^4)⁻¹ := by ring

/-- The Mills-ratio asymptotic equivalence: `G_T(b) ~ (2T/b) exp(-b²/(4T))` as `b → ∞`. -/
theorem gaussianTail_isEquivalent (T : ℝ) (hT : 0 < T) :
    gaussianTail T ~[Filter.atTop] fun b => (2*T/b) * Real.exp (-b^2/(4*T)) := by
  have hGn : ∀ᶠ b in atTop, (fun b => (2*T/b) * Real.exp (-b^2/(4*T))) b ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with b hb
    have hb0 : (0:ℝ) < b := one_pos.trans_le hb
    show (2*T/b) * Real.exp (-b^2/(4*T)) ≠ 0
    positivity
  have hmul : (fun b => (2*T/b) * Real.exp (-b^2/(4*T)) * b^(-4:ℝ))
      =o[atTop] (fun b => (2*T/b) * Real.exp (-b^2/(4*T))) := by
    apply (isLittleO_iff_tendsto' ?_).2 ?_
    · exact hGn.mono fun b hb' h => by rw [h]; ring
    · have hratio : (fun b => ((2*T/b) * Real.exp (-b^2/(4*T)) * b^(-4:ℝ))
          / ((2*T/b) * Real.exp (-b^2/(4*T)))) =ᶠ[atTop] fun b => b^(-4:ℝ) := by
        filter_upwards [hGn] with b hb'
        exact mul_div_cancel_left₀ _ hb'
      exact (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 4)).congr' hratio.symm
  have hΔ : (fun b => gaussianTail T b - (2*T/b) * Real.exp (-b^2/(4*T)) * (1 - 2*T/b^2))
      =o[atTop] (fun b => (2*T/b) * Real.exp (-b^2/(4*T))) :=
    (gaussianTail_asymptotic T hT).trans_isLittleO hmul
  have hrest : (fun b => ((2*T/b) * Real.exp (-b^2/(4*T))) * (2*T/b^2))
      =o[atTop] (fun b => (2*T/b) * Real.exp (-b^2/(4*T))) := by
    apply (isLittleO_iff_tendsto' ?_).2 ?_
    · exact hGn.mono fun b hb' h => by rw [h]; ring
    · have hratio : (fun b => (((2*T/b) * Real.exp (-b^2/(4*T))) * (2*T/b^2))
          / ((2*T/b) * Real.exp (-b^2/(4*T)))) =ᶠ[atTop] fun b => 2*T * b^(-2:ℝ) := by
        filter_upwards [hGn, eventually_ge_atTop 1] with b hb' hb1
        have hb0 : (0:ℝ) < b := one_pos.trans_le hb1
        rw [mul_div_cancel_left₀ _ hb']
        have hrp2 : b^(-2:ℝ) = (b^2)⁻¹ := by
          rw [← Real.rpow_natCast b 2, ← Real.rpow_neg hb0.le]
          norm_cast
        rw [hrp2, div_eq_mul_inv]
      have htr : Tendsto (fun b : ℝ => 2*T * b^(-2:ℝ)) atTop (𝓝 0) := by
        have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 2)).const_mul (2*T)
        rwa [mul_zero] at h
      exact htr.congr' hratio.symm
  show (gaussianTail T - fun b => (2*T/b) * Real.exp (-b^2/(4*T)))
      =o[atTop] (fun b => (2*T/b) * Real.exp (-b^2/(4*T)))
  exact (hΔ.sub hrest).congr
    (fun b => by
      show gaussianTail T b - (2*T/b) * Real.exp (-b^2/(4*T)) * (1 - 2*T/b^2)
          - ((2*T/b) * Real.exp (-b^2/(4*T))) * (2*T/b^2)
        = gaussianTail T b - (2*T/b) * Real.exp (-b^2/(4*T))
      ring)
    (fun _ => rfl)
