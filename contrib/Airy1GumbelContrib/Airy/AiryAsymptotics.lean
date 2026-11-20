/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryBessel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open MeasureTheory Set Filter
open scoped Topology
open Asymptotics

/-! # Small-`z` asymptotics of the Schläfli `s`-integrals

Part of the Airy–Bessel identity route (see `Airy/AiryBessel.lean` for
the overall strategy): the small-`z` asymptotics of the two `s`-integral pieces
`schlaefliJ1`, `schlaefliJ2`:

* `schlaefliJ2_const`: the Hadamard finite-part evaluation
  `∫₀^∞ (e^{-s} - 1) s^{-4/3} ds = -3 Γ(2/3)`;
* `schlaefliJ2_sub_tendsto`: `J₂(z) - 3 (z/2)^{-1/3} → -3 Γ(2/3)` as `z → 0⁺`;
* `schlaefliJ1_isBigO`: `J₁(z) - Γ(1/3) + 3 (z/2)^{1/3} = O(z^{4/3})` as `z → 0⁺`.
-/

/-! ## Power integrals on half-lines and finite intervals -/

/-- For `0 < a` and `p < -1`, the power `s ↦ s^p` is integrable on `(a, ∞)` and
`∫_{a}^{∞} s^p ds = -a^{p+1}/(p+1)` (FTC with antiderivative `s^{p+1}/(p+1)`, which
vanishes at `+∞`). -/
private theorem integrableOn_and_integral_rpow_Ioi {a : ℝ} (ha : 0 < a) {p : ℝ}
    (hp : p < -1) :
    IntegrableOn (fun s : ℝ => s^(p:ℝ)) (Set.Ioi a)
      ∧ ∫ s in Set.Ioi a, s^(p:ℝ) = - a^(p+1:ℝ)/(p+1) := by
  have hp1 : p + 1 < 0 := by linarith
  have hp1ne : (p + 1 : ℝ) ≠ 0 := ne_of_lt hp1
  have hderiv : ∀ s ∈ Set.Ioi a,
      HasDerivAt (fun s : ℝ => s^(p+1:ℝ)/(p+1)) (s^(p:ℝ)) s := by
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt (ha.trans hs)
    have h := (Real.hasDerivAt_rpow_const (p := p+1) (Or.inl hs0)).div_const (p+1)
    convert h using 1
    rw [show p + 1 - 1 = p by ring]
    field_simp
  have hT : Tendsto (fun s : ℝ => s^(p+1:ℝ)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (show (0:ℝ) < -(p+1) by linarith)
    simpa only [neg_neg] using h
  have hT2 : Tendsto (fun s : ℝ => s^(p+1:ℝ)/(p+1)) atTop (𝓝 0) := by
    have h := hT.div_const (p+1)
    rwa [zero_div] at h
  have hcont : ContinuousWithinAt (fun s : ℝ => s^(p+1:ℝ)/(p+1)) (Set.Ici a) a :=
    ((Real.continuousAt_rpow_const a (p+1) (Or.inl ha.ne')).div_const _).continuousWithinAt
  have hpos : ∀ s ∈ Set.Ioi a, 0 ≤ s^(p:ℝ) :=
    fun s hs => Real.rpow_nonneg (ha.trans hs).le _
  have hint : IntegrableOn (fun s : ℝ => s^(p:ℝ)) (Set.Ioi a) :=
    integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hT2
  refine ⟨hint, ?_⟩
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hT2
  rw [hftc, zero_sub, neg_div]

/-- For `0 < a ≤ b` and `p ≠ -1`, `∫_{(a,b)} s^p ds = (b^{p+1} - a^{p+1})/(p+1)`. -/
private theorem integral_Ioo_rpow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {p : ℝ}
    (hp : p ≠ -1) :
    ∫ s in Set.Ioo a b, s^(p:ℝ) = (b^(p+1:ℝ) - a^(p+1:ℝ))/(p+1) := by
  have h0 : (0:ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h => absurd h.1 (not_le.mpr ha)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  exact integral_rpow (Or.inr ⟨hp, h0⟩)

/-- For `0 ≤ a` and `-1 < p`, the power `s ↦ s^p` is integrable on `(0, a]` with
`∫_{(0,a]} s^p ds = a^{p+1}/(p+1)`. -/
private theorem integrableOn_and_integral_Ioc_zero_rpow {a : ℝ} (ha : 0 ≤ a) {p : ℝ}
    (hp : -1 < p) :
    IntegrableOn (fun s : ℝ => s^(p:ℝ)) (Set.Ioc 0 a)
      ∧ ∫ s in Set.Ioc 0 a, s^(p:ℝ) = a^(p+1:ℝ)/(p+1) := by
  have hI : IntervalIntegrable (fun s : ℝ => s^(p:ℝ)) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' hp
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mp hI, ?_⟩
  rw [← intervalIntegral.integral_of_le ha, integral_rpow (Or.inl hp),
    Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < p + 1)), sub_zero]

/-! ## The antiderivative for the Hadamard finite-part constant -/

/-- The antiderivative for the Hadamard finite-part computation of
`∫₀^∞ (e^{-s} - 1) s^{-4/3} ds`: on `(0, ∞)`, `A(s) = -3 (s^{-1/3} (e^{-s} - 1))`
differentiates to `s^{-4/3} (e^{-s} - 1) + 3 s^{-1/3} e^{-s}`. -/
private noncomputable def schlaefliJ2ConstAntideriv (s : ℝ) : ℝ :=
  -3 * (s^(-1/3:ℝ) * (Real.exp (-s) - 1))

/-- The product-rule derivative of `schlaefliJ2ConstAntideriv`. -/
private theorem hasDerivAt_schlaefliJ2ConstAntideriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt schlaefliJ2ConstAntideriv
      (s^(-4/3:ℝ) * (Real.exp (-s) - 1) + 3 * s^(-1/3:ℝ) * Real.exp (-s)) s := by
  have h1 : HasDerivAt (fun s : ℝ => s^(-1/3:ℝ)) ((-1/3) * s^(-4/3:ℝ)) s := by
    convert Real.hasDerivAt_rpow_const (Or.inl hs.ne') using 1
    norm_num
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s) - 1) (-Real.exp (-s)) s := by
    convert ((hasDerivAt_id' s).neg.exp.sub_const 1) using 1
    simp only [Pi.neg_apply]
    ring
  have h3 := (h1.mul h2).const_mul (-3)
  convert h3 using 1
  funext t
  simp only [schlaefliJ2ConstAntideriv, Pi.mul_apply]
  ring

/-- `schlaefliJ2ConstAntideriv` vanishes at `0`. -/
private theorem schlaefliJ2ConstAntideriv_zero : schlaefliJ2ConstAntideriv 0 = 0 := by
  simp [schlaefliJ2ConstAntideriv]

/-- `schlaefliJ2ConstAntideriv` is continuous at `0` from the right (squeeze against
`3 s^{2/3}`, using `|e^{-s} - 1| = 1 - e^{-s} ≤ s` for `s ≥ 0`). -/
private theorem continuousWithinAt_schlaefliJ2ConstAntideriv_zero :
    ContinuousWithinAt schlaefliJ2ConstAntideriv (Set.Ici 0) 0 := by
  have hlim : Tendsto schlaefliJ2ConstAntideriv (𝓝[Set.Ici 0] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (g := fun s : ℝ => 3 * s^(2/3:ℝ))
      (Eventually.of_forall fun s => abs_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs0 : 0 ≤ s := hs
      rcases hs0.eq_or_lt with rfl | hspos
      · show |(schlaefliJ2ConstAntideriv) 0| ≤ 3 * (0:ℝ)^(2/3:ℝ)
        rw [schlaefliJ2ConstAntideriv_zero, abs_zero]; positivity
      · have hexp1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hspos.le)
        have hle : 1 - Real.exp (-s) ≤ s := by
          have h := Real.add_one_le_exp (-s)
          linarith
        calc |schlaefliJ2ConstAntideriv s|
            = 3 * s^(-1/3:ℝ) * |Real.exp (-s) - 1| := by
              unfold schlaefliJ2ConstAntideriv
              rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (Real.rpow_nonneg hspos.le _),
                abs_of_pos (by norm_num : (0:ℝ) < 3), mul_assoc]
          _ = 3 * s^(-1/3:ℝ) * (1 - Real.exp (-s)) := by
              rw [abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub]
          _ ≤ 3 * s^(-1/3:ℝ) * s := mul_le_mul_of_nonneg_left hle (by positivity)
          _ = 3 * s^(2/3:ℝ) := by
              have key : s^(-1/3:ℝ) * s^(1:ℝ) = s^(2/3:ℝ) := by
                rw [← Real.rpow_add hspos, show (-1/3:ℝ) + 1 = 2/3 by norm_num]
              rw [Real.rpow_one] at key
              rw [mul_assoc, key]
    · have hc : ContinuousAt (fun s : ℝ => 3 * s^(2/3:ℝ)) 0 :=
        (Real.continuousAt_rpow_const 0 (2/3:ℝ) (Or.inr (by norm_num))).const_mul 3
      have hv : 3 * (0:ℝ)^(2/3:ℝ) = 0 := by
        rw [Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0), mul_zero]
      have h0 : Tendsto (fun s : ℝ => 3 * s^(2/3:ℝ)) (𝓝 (0:ℝ)) (𝓝 0) := by
        have ht := hc.tendsto
        rwa [hv] at ht
      exact h0.mono_left nhdsWithin_le_nhds
  simpa only [ContinuousWithinAt, schlaefliJ2ConstAntideriv_zero] using hlim

/-- `schlaefliJ2ConstAntideriv s → 0` as `s → ∞` (squeeze against `3 s^{-1/3}`). -/
private theorem tendsto_schlaefliJ2ConstAntideriv_atTop :
    Tendsto schlaefliJ2ConstAntideriv Filter.atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (g := fun s : ℝ => 3 * s^(-1/3:ℝ))
    (Eventually.of_forall fun s => abs_nonneg _) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 0] with s hs
    have hexp1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)
    have hle : 1 - Real.exp (-s) ≤ 1 := by linarith [Real.exp_pos (-s)]
    calc |schlaefliJ2ConstAntideriv s|
        = 3 * s^(-1/3:ℝ) * |Real.exp (-s) - 1| := by
          unfold schlaefliJ2ConstAntideriv
          rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (Real.rpow_nonneg hs _),
            abs_of_pos (by norm_num : (0:ℝ) < 3), mul_assoc]
      _ = 3 * s^(-1/3:ℝ) * (1 - Real.exp (-s)) := by
          rw [abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub]
      _ ≤ 3 * s^(-1/3:ℝ) * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 3 * s^(-1/3:ℝ) := mul_one _
  · have h := tendsto_rpow_neg_atTop (show (0:ℝ) < 1/3 by norm_num)
    have h2 := h.const_mul 3
    rw [mul_zero, show -(1/3:ℝ) = (-1/3:ℝ) by norm_num] at h2
    exact h2

/-- The first summand `s ↦ s^{-4/3} (e^{-s} - 1)` of the derivative of
`schlaefliJ2ConstAntideriv` is integrable on `(0, ∞)`: it is `O(s^{-1/3})` near `0`
(since `|e^{-s} - 1| ≤ s`) and `O(s^{-4/3})` near `∞`. -/
private theorem integrableOn_rpow_mul_exp_neg_sub_one :
    IntegrableOn (fun s : ℝ => s^(-4/3:ℝ) * (Real.exp (-s) - 1)) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun s : ℝ => s^(-4/3:ℝ) * (Real.exp (-s) - 1)) (Set.Ioi 0) := by
    intro s hs
    exact ((Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt hs))).mul
      ((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).sub_const
        1)).continuousWithinAt
  have hIoc : IntegrableOn (fun s : ℝ => s^(-4/3:ℝ) * (Real.exp (-s) - 1))
      (Set.Ioc 0 1) := by
    apply Integrable.mono' (integrableOn_and_integral_Ioc_zero_rpow zero_le_one
      (show (-1:ℝ) < -1/3 by norm_num)).1 ?_ ?_
    · exact (hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      have hs0 : 0 < s := hs.1
      have hexp1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0.le)
      have hle : 1 - Real.exp (-s) ≤ s := by
        have h := Real.add_one_le_exp (-s)
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
        abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub]
      calc s^(-4/3:ℝ) * (1 - Real.exp (-s)) ≤ s^(-4/3:ℝ) * s :=
          mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hs0.le _)
        _ = s^(-1/3:ℝ) := by
          have key : s^(-4/3:ℝ) * s^(1:ℝ) = s^(-1/3:ℝ) := by
            rw [← Real.rpow_add hs0, show (-4/3:ℝ) + 1 = -1/3 by norm_num]
          rwa [Real.rpow_one] at key
  have hIoi : IntegrableOn (fun s : ℝ => s^(-4/3:ℝ) * (Real.exp (-s) - 1))
      (Set.Ioi 1) := by
    apply Integrable.mono' (integrableOn_and_integral_rpow_Ioi one_pos
      (show (-4/3:ℝ) < -1 by norm_num)).1 ?_ ?_
    · exact (hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
        measurableSet_Ioi
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
      have hs0 : 0 < s := zero_lt_one.trans hs
      have hexp1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0.le)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
        abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub]
      have hle : 1 - Real.exp (-s) ≤ 1 := by linarith [Real.exp_pos (-s)]
      calc s^(-4/3:ℝ) * (1 - Real.exp (-s)) ≤ s^(-4/3:ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hs0.le _)
        _ = s^(-4/3:ℝ) := mul_one _
  have h := hIoc.union hIoi
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at h

/-- The second summand `s ↦ 3 s^{-1/3} e^{-s}` of the derivative of
`schlaefliJ2ConstAntideriv` is integrable on `(0, ∞)` (`O(s^{-1/3})` near `0`,
exponentially decaying near `∞`). -/
private theorem integrableOn_rpow_mul_exp_neg :
    IntegrableOn (fun s : ℝ => 3 * s^(-1/3:ℝ) * Real.exp (-s)) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun s : ℝ => 3 * s^(-1/3:ℝ) * Real.exp (-s)) (Set.Ioi 0) := by
    intro s hs
    exact (((Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt hs))).const_mul 3).mul
      (Real.continuous_exp.continuousAt.comp continuousAt_id.neg)).continuousWithinAt
  have hIoc : IntegrableOn (fun s : ℝ => 3 * s^(-1/3:ℝ) * Real.exp (-s))
      (Set.Ioc 0 1) := by
    apply Integrable.mono' ((integrableOn_and_integral_Ioc_zero_rpow zero_le_one
      (show (-1:ℝ) < -1/3 by norm_num)).1.const_mul 3) ?_ ?_
    · exact (hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      have hs0 : 0 < s := hs.1
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
        abs_of_pos (Real.exp_pos _), abs_of_pos (by norm_num : (0:ℝ) < 3)]
      calc 3 * s^(-1/3:ℝ) * Real.exp (-s) ≤ 3 * s^(-1/3:ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0.le))
            (by positivity)
        _ = 3 * s^(-1/3:ℝ) := mul_one _
  have hIoi : IntegrableOn (fun s : ℝ => 3 * s^(-1/3:ℝ) * Real.exp (-s))
      (Set.Ioi 1) := by
    apply Integrable.mono' ((integrableOn_exp_neg_Ioi 1).const_mul 3) ?_ ?_
    · exact (hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
        measurableSet_Ioi
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
      have hs0 : 0 < s := zero_lt_one.trans hs
      have hs1 : 1 ≤ s := hs.le
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
        abs_of_pos (Real.exp_pos _), abs_of_pos (by norm_num : (0:ℝ) < 3)]
      have hpow : s^(-1/3:ℝ) ≤ 1 := by
        have h := Real.rpow_le_rpow_of_exponent_le hs1 (show (-1/3:ℝ) ≤ 0 by norm_num)
        rwa [Real.rpow_zero] at h
      calc 3 * s^(-1/3:ℝ) * Real.exp (-s) ≤ 3 * 1 * Real.exp (-s) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num))
            (Real.exp_pos _).le
        _ = 3 * Real.exp (-s) := by ring
  have h := hIoc.union hIoi
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at h

/-- The Hadamard finite-part constant: `∫₀^∞ (e^{-s} - 1) s^{-4/3} ds = -3 Γ(2/3)`.
Proof: FTC on `(0, ∞)` applied to `A(s) = -3 s^{-1/3} (e^{-s} - 1)` gives
`∫ A' = 0`, i.e. `∫ s^{-4/3} (e^{-s} - 1) = -3 ∫ s^{-1/3} e^{-s} = -3 Γ(2/3)`. -/
theorem schlaefliJ2_const :
    ∫ s in Set.Ioi (0:ℝ), (Real.exp (-s) - 1) * s^(-4/3:ℝ) = -3 * Real.Gamma (2/3) := by
  have hint : IntegrableOn (fun s : ℝ => s^(-4/3:ℝ) * (Real.exp (-s) - 1)
      + 3 * s^(-1/3:ℝ) * Real.exp (-s)) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_sub_one.add integrableOn_rpow_mul_exp_neg
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    continuousWithinAt_schlaefliJ2ConstAntideriv_zero
    (fun s hs => hasDerivAt_schlaefliJ2ConstAntideriv hs)
    hint tendsto_schlaefliJ2ConstAntideriv_atTop
  rw [schlaefliJ2ConstAntideriv_zero, sub_zero] at hftc
  rw [integral_add integrableOn_rpow_mul_exp_neg_sub_one integrableOn_rpow_mul_exp_neg]
    at hftc
  have hG : Real.Gamma (2/3) = ∫ s in Set.Ioi 0, Real.exp (-s) * s^(-1/3:ℝ) := by
    have h := Real.Gamma_eq_integral (show (0:ℝ) < 2/3 by norm_num)
    rwa [show (2/3:ℝ) - 1 = -1/3 by norm_num] at h
  have h2val : (∫ s in Set.Ioi 0, 3 * s^(-1/3:ℝ) * Real.exp (-s)) = 3 * Real.Gamma (2/3) := by
    have hcongr : (∫ s in Set.Ioi 0, 3 * s^(-1/3:ℝ) * Real.exp (-s))
        = 3 * ∫ s in Set.Ioi 0, Real.exp (-s) * s^(-1/3:ℝ) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s _
      ring
    rw [hcongr, ← hG]
  have hmain : (∫ s in Set.Ioi 0, s^(-4/3:ℝ) * (Real.exp (-s) - 1))
      = -3 * Real.Gamma (2/3) := by linarith [hftc, h2val]
  rw [← hmain]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  ring


/-! ## Small-`z` asymptotics of `J₂` -/

/-- The limiting centered integrand `k(s) = (e^{-s} - 1) s^{-4/3}` is integrable on
`(0, ∞)` (repackaging of `integrableOn_rpow_mul_exp_neg_sub_one`). -/
private theorem integrableOn_exp_sub_one_mul_rpow :
    IntegrableOn (fun s : ℝ => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) (Set.Ioi 0) :=
  integrableOn_rpow_mul_exp_neg_sub_one.congr_fun (fun _ _ => mul_comm _ _)
    measurableSet_Ioi

/-- For `0 < z`, the centered `J₂` integral:
`J₂(z) - 3 (z/2)^{-1/3} = ∫_{z/2}^∞ (e^{-s - z²/(4s)} - 1) s^{-4/3} ds`
(the constant `3 (z/2)^{-1/3}` is the bare power integral `∫_{z/2}^∞ s^{-4/3} ds`). -/
private theorem schlaefliJ2_sub_eq_integral {z : ℝ} (hz : 0 < z) :
    schlaefliJ2 z - 3 * (z/2)^(-1/3:ℝ)
      = ∫ s in Set.Ioi (z/2), (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ) := by
  have hza : (0:ℝ) < z/2 := by linarith
  have hI1 : IntegrableOn (fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ))
      (Set.Ioi (z/2)) := integrableOn_schlaefliJ_kernel hz (by norm_num)
  have hI2 : IntegrableOn (fun s : ℝ => s^(-4/3:ℝ)) (Set.Ioi (z/2)) :=
    (integrableOn_and_integral_rpow_Ioi hza (by norm_num)).1
  have hval : ∫ s in Set.Ioi (z/2), s^(-4/3:ℝ) = 3 * (z/2)^(-1/3:ℝ) := by
    have h := (integrableOn_and_integral_rpow_Ioi hza (show (-4/3:ℝ) < -1 by norm_num)).2
    rw [show (-4/3:ℝ) + 1 = -1/3 by norm_num] at h
    rw [h, div_eq_iff (by norm_num : (-1/3:ℝ) ≠ 0)]
    ring
  unfold schlaefliJ2
  rw [← hval, ← integral_sub hI1 hI2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  ring

/-- The centered `J₂` integrand is integrable on `(z/2, ∞)` for `0 < z`. -/
private theorem integrableOn_centeredJ2 {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun s => (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
      (Set.Ioi (z/2)) := by
  have hI1 : IntegrableOn (fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ))
      (Set.Ioi (z/2)) := integrableOn_schlaefliJ_kernel hz (by norm_num)
  have hI2 : IntegrableOn (fun s : ℝ => s^(-4/3:ℝ)) (Set.Ioi (z/2)) :=
    (integrableOn_and_integral_rpow_Ioi (by linarith) (by norm_num)).1
  have heq : (fun s => (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
      = (fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ)) - (fun s => s^(-4/3:ℝ)) := by
    funext s
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  exact hI1.sub hI2

/-- For `0 < z ≤ 1`, the centered `J₂` integral splits at `s = 1`. -/
private theorem centeredJ2_split {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (∫ s in Set.Ioi (z/2), (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
      = (∫ s in Set.Ioc (z/2) 1, (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
        + ∫ s in Set.Ioi 1, (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ) := by
  have hz2 : z/2 ≤ 1 := by linarith
  have hI := integrableOn_centeredJ2 hz
  rw [← Ioc_union_Ioi_eq_Ioi hz2]
  exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi hz2))

/-- Powers `s ↦ s^p` are integrable on `(a, b)` when `0 < a ≤ b` (any `p`). -/
private theorem integrableOn_Ioo_rpow_of_pos {a : ℝ} (ha : 0 < a) {b : ℝ} (hab : a ≤ b)
    (p : ℝ) :
    IntegrableOn (fun s : ℝ => s^(p:ℝ)) (Set.Ioo a b) := by
  have h0 : (0:ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h => absurd h.1 (not_le.mpr ha)
  have hI : IntervalIntegrable (fun s : ℝ => s^(p:ℝ)) volume a b :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hI).mono_set
    Ioo_subset_Ioc_self

/-- Dominated convergence of the centered `J₂` integral on `(1, ∞)` as `z → 0⁺`
(dominator `s^{-4/3}`). -/
private theorem tendsto_centeredJ2_Ioi_one :
    Tendsto (fun z => ∫ s in Set.Ioi (1:ℝ), (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ s in Set.Ioi (1:ℝ), (Real.exp (-s) - 1) * s^(-4/3:ℝ))) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun s : ℝ => s^(-4/3:ℝ)) ?_ ?_
    ((integrableOn_and_integral_rpow_Ioi one_pos (by norm_num)).1) ?_
  · filter_upwards with z
    have h1 : ContinuousOn (fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ))
        (Set.Ioi 1) := continuousOn_schlaefliJ_kernel one_pos _
    have h2 : ContinuousOn (fun s : ℝ => s^(-4/3:ℝ)) (Set.Ioi 1) := by
      intro s hs
      exact (Real.continuousAt_rpow_const s _
        (Or.inl (ne_of_gt (zero_lt_one.trans hs)))).continuousWithinAt
    have heq : (fun s => (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
        = fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ) - s^(-4/3:ℝ) :=
      funext fun s => by ring
    have hc : ContinuousOn (fun s => (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
        (Set.Ioi 1) := by
      rw [heq]
      exact h1.sub h2
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards with z
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
    have hs0 : (0:ℝ) < s := zero_lt_one.trans hs
    have hnn : (0:ℝ) ≤ z^2/(4*s) :=
      div_nonneg (sq_nonneg z) (mul_nonneg (by norm_num) hs0.le)
    have hexp1 : Real.exp (-s - z^2/(4*s)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub,
      abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
    have hle : 1 - Real.exp (-s - z^2/(4*s)) ≤ 1 := by
        linarith [Real.exp_pos (-s - z^2/(4*s))]
    calc (1 - Real.exp (-s - z^2/(4*s))) * s^(-4/3:ℝ) ≤ 1 * s^(-4/3:ℝ) :=
        mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hs0.le _)
      _ = s^(-4/3:ℝ) := one_mul _
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
    have hs0 : (0:ℝ) < s := zero_lt_one.trans hs
    have hc : ContinuousAt (fun z : ℝ => (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ)) 0 := by
      fun_prop
    have h0 : Tendsto (fun z : ℝ => (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
        (𝓝 (0:ℝ)) (𝓝 ((Real.exp (-s - (0:ℝ)^2/(4*s)) - 1) * s^(-4/3:ℝ))) := hc.tendsto
    have hv : (Real.exp (-s - (0:ℝ)^2/(4*s)) - 1) * s^(-4/3:ℝ)
        = (Real.exp (-s) - 1) * s^(-4/3:ℝ) := by
      rw [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div, sub_zero]
    rw [hv] at h0
    exact h0.mono_left nhdsWithin_le_nhds

/-- The `k`-integral over `(z/2, 1)` tends to the `k`-integral over `(0, 1)` as `z → 0⁺`
(dominated convergence with dominator `|k|`). -/
private theorem tendsto_airyAsympK_Ioo :
    Tendsto (fun z => ∫ s in Set.Ioo (z/2) 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ s in Set.Ioo 0 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ))) := by
  have hkI : IntegrableOn (fun s : ℝ => (Real.exp (-s) - 1) * s^(-4/3:ℝ))
      (Set.Ioo 0 1) :=
    integrableOn_exp_sub_one_mul_rpow.mono_set Ioo_subset_Ioi_self
  have hmeas : AEStronglyMeasurable (fun s => (Real.exp (-s) - 1) * s^(-4/3:ℝ))
      (volume.restrict (Set.Ioo 0 1)) := by
    have hcont : ContinuousOn (fun s => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) (Set.Ioi 0) := by
      intro s hs
      exact (((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).sub
        continuousAt_const).mul
        (Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt hs)))).continuousWithinAt
    exact (hcont.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo
  have hdct : Tendsto (fun z => ∫ s in Set.Ioo 0 1,
        (Set.Ioi (z/2)).indicator (fun s => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) s)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ s in Set.Ioo 0 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun s => |(Real.exp (-s) - 1) * s^(-4/3:ℝ)|) ?_ ?_ hkI.abs ?_
    · filter_upwards with z
      exact hmeas.indicator measurableSet_Ioi
    · filter_upwards with z
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun s _ => ?_
      calc ‖(Set.Ioi (z/2)).indicator (fun s => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) s‖
          ≤ ‖(Real.exp (-s) - 1) * s^(-4/3:ℝ)‖ := norm_indicator_le_norm_self _ _
        _ = |(Real.exp (-s) - 1) * s^(-4/3:ℝ)| := Real.norm_eq_abs _
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_
      have hz2 : Tendsto (fun z : ℝ => z/2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have hc : ContinuousAt (fun z : ℝ => z / 2) 0 := continuousAt_id.div_const 2
        have h0 : Tendsto (fun z : ℝ => z / 2) (𝓝 (0:ℝ)) (𝓝 0) := by
          have ht := hc.tendsto
          rwa [zero_div] at ht
        exact h0.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ z in 𝓝[>] (0:ℝ), z/2 < s := hz2.eventually (Iio_mem_nhds hs.1)
      have heq : (fun z => (Set.Ioi (z/2)).indicator
            (fun s => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) s)
          =ᶠ[𝓝[>] (0:ℝ)] (fun _ => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) := by
        filter_upwards [hev] with z hz2s
        exact Set.indicator_of_mem hz2s _
      exact heq.tendsto
  refine Tendsto.congr' ?_ hdct
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with z hz hz1
  have hzpos : (0:ℝ) < z := hz
  have hz2 : (0:ℝ) ≤ z/2 := by linarith
  rw [setIntegral_indicator measurableSet_Ioi]
  have hset : Set.Ioo 0 1 ∩ Set.Ioi (z/2) = Set.Ioo (z/2) 1 := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by linarith, h2⟩, h1⟩
  rw [hset]

/-- The pointwise bound for the difference integrand: for `0 < z` and `z/2 < s`,
`|(e^{-s-z²/(4s)} - e^{-s}) s^{-4/3}| ≤ (z²/4) s^{-7/3}` (from `1 - e^{-u} ≤ u`). -/
private theorem abs_centeredJ2_diff_le {z : ℝ} (hz : 0 < z) {s : ℝ} (hs : z/2 < s) :
    |(Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)| ≤ (z^2/4) * s^(-7/3:ℝ) := by
  have hs0 : 0 < s := by linarith [hz]
  have hnn : (0:ℝ) ≤ z^2/(4*s) := div_nonneg (sq_nonneg z) (mul_nonneg (by norm_num) hs0.le)
  have hrewrite : Real.exp (-s - z^2/(4*s)) - Real.exp (-s)
      = Real.exp (-s) * (Real.exp (-(z^2/(4*s))) - 1) := by
    rw [show -s - z^2/(4*s) = -s + -(z^2/(4*s)) by ring, Real.exp_add]
    ring
  have hexp1 : Real.exp (-(z^2/(4*s))) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hnn)
  have hle : 1 - Real.exp (-(z^2/(4*s))) ≤ z^2/(4*s) := by
    have h := Real.add_one_le_exp (-(z^2/(4*s)))
    linarith
  rw [hrewrite, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
    abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub,
    abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
  calc Real.exp (-s) * (1 - Real.exp (-(z^2/(4*s)))) * s^(-4/3:ℝ)
      ≤ 1 * (z^2/(4*s)) * s^(-4/3:ℝ) := by
        apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hs0.le _)
        exact mul_le_mul (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0.le)) hle
          (sub_nonneg.mpr hexp1) zero_le_one
    _ = (z^2/4) * s^(-7/3:ℝ) := by
        have key : s^(-1:ℝ) * s^(-4/3:ℝ) = s^(-7/3:ℝ) := by
          rw [← Real.rpow_add hs0, show (-1:ℝ) + -4/3 = -7/3 by norm_num]
        have h2 : z^2/(4*s) = (z^2/4) * s^(-1:ℝ) := by
          have hsne : s ≠ 0 := hs0.ne'
          rw [Real.rpow_neg_one]
          field_simp
        rw [h2]
        calc 1 * ((z^2/4) * s^(-1:ℝ)) * s^(-4/3:ℝ)
            = (z^2/4) * (s^(-1:ℝ) * s^(-4/3:ℝ)) := by ring
          _ = (z^2/4) * s^(-7/3:ℝ) := by rw [key]

/-- Continuity of the difference integrand on `(a, ∞)` for `0 < a`. -/
private theorem continuousOn_centeredJ2_diff {z a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s => (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ))
      (Set.Ioi a) := by
  have h1 : ContinuousOn (fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ)) (Set.Ioi a) :=
    continuousOn_schlaefliJ_kernel ha _
  have h2 : ContinuousOn (fun s : ℝ => Real.exp (-s) * s^(-4/3:ℝ)) (Set.Ioi a) := by
    intro s hs
    exact ((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).mul
      (Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt (ha.trans hs))))).continuousWithinAt
  have heq : (fun s => (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ))
      = fun s => Real.exp (-s - z^2/(4*s)) * s^(-4/3:ℝ) - Real.exp (-s) * s^(-4/3:ℝ) :=
    funext fun s => by ring
  rw [heq]
  exact h1.sub h2

/-- The difference integrand on `(z/2, 1)` tends to `0` as `z → 0⁺`: its absolute value is
bounded by `(z²/4) ∫_{z/2}^1 s^{-7/3} ds = (3/16) z² ((z/2)^{-4/3} - 1) ≤ C z^{2/3}`. -/
private theorem tendsto_centeredJ2_diff_Ioo :
    Tendsto (fun z => ∫ s in Set.Ioo (z/2) 1,
      (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (g := fun z : ℝ => (3/16) * (2:ℝ)^(4/3:ℝ) * z^(2/3:ℝ))
    (Eventually.of_forall fun z => abs_nonneg _) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with z hz hz1
    have hzpos : (0:ℝ) < z := hz
    have hz2 : (0:ℝ) < z/2 := by linarith
    have hz2le : z/2 ≤ 1 := by linarith
    have hg : IntegrableOn (fun s : ℝ => (z^2/4) * s^(-7/3:ℝ)) (Set.Ioo (z/2) 1) :=
      (integrableOn_Ioo_rpow_of_pos hz2 hz2le _).const_mul _
    have hf : IntegrableOn
        (fun s => |(Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)|)
        (Set.Ioo (z/2) 1) := by
      apply hg.mono' ?_ ?_
      · exact ((continuousOn_centeredJ2_diff hz2).mono
          Ioo_subset_Ioi_self).abs.aestronglyMeasurable measurableSet_Ioo
      · refine ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_
        rw [Real.norm_eq_abs, abs_abs]
        exact abs_centeredJ2_diff_le hz hs.1
    have hval : ∫ s in Set.Ioo (z/2) 1, s^(-7/3:ℝ) = (3/4) * ((z/2)^(-4/3:ℝ) - 1) := by
      rw [integral_Ioo_rpow hz2 hz2le (by norm_num : (-7/3:ℝ) ≠ -1), Real.one_rpow,
        show (-7/3:ℝ) + 1 = -4/3 by norm_num]
      field_simp
      ring
    have h1 : |∫ s in Set.Ioo (z/2) 1,
        (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)|
        ≤ ∫ s in Set.Ioo (z/2) 1,
            |(Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)| := by
      calc |∫ s in Set.Ioo (z/2) 1, (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)|
          = ‖∫ s in Set.Ioo (z/2) 1,
              (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∫ s in Set.Ioo (z/2) 1,
              ‖(Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ s in Set.Ioo (z/2) 1,
              |(Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)| := by
            apply setIntegral_congr_fun measurableSet_Ioo
            intro s _
            exact Real.norm_eq_abs _
    calc |∫ s in Set.Ioo (z/2) 1, (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)|
        ≤ ∫ s in Set.Ioo (z/2) 1,
            |(Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ)| := h1
      _ ≤ ∫ s in Set.Ioo (z/2) 1, (z^2/4) * s^(-7/3:ℝ) :=
          setIntegral_mono_on hf hg measurableSet_Ioo
            (fun s hs => abs_centeredJ2_diff_le hz hs.1)
      _ = (z^2/4) * ((3/4) * ((z/2)^(-4/3:ℝ) - 1)) := by
          rw [integral_const_mul, hval]
      _ ≤ (z^2/4) * ((3/4) * (z/2)^(-4/3:ℝ)) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (by norm_num)
      _ = (3/16) * (2:ℝ)^(4/3:ℝ) * z^(2/3:ℝ) := by
          have hz2pow : (z/2)^(-4/3:ℝ) = (2:ℝ)^(4/3:ℝ) * z^(-4/3:ℝ) := by
            have h2p : (0:ℝ) < (2:ℝ)^(-4/3:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
            rw [Real.div_rpow hz.le (by norm_num : (0:ℝ) ≤ 2), div_eq_iff h2p.ne']
            calc z^(-4/3:ℝ) = 1 * z^(-4/3:ℝ) := (one_mul _).symm
              _ = (2:ℝ)^((4/3:ℝ) + (-4/3:ℝ)) * z^(-4/3:ℝ) := by
                  rw [show (4/3:ℝ) + -4/3 = 0 by norm_num, Real.rpow_zero]
              _ = (2:ℝ)^(4/3:ℝ) * (2:ℝ)^(-4/3:ℝ) * z^(-4/3:ℝ) := by
                  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
              _ = (2:ℝ)^(4/3:ℝ) * z^(-4/3:ℝ) * (2:ℝ)^(-4/3:ℝ) := by ring
          have hzpow : z^2 * z^(-4/3:ℝ) = z^(2/3:ℝ) := by
            rw [← Real.rpow_natCast z 2, ← Real.rpow_add hz]
            norm_num
          rw [hz2pow]
          calc (z^2/4) * ((3/4) * ((2:ℝ)^(4/3:ℝ) * z^(-4/3:ℝ)))
              = (3/16) * (2:ℝ)^(4/3:ℝ) * (z^2 * z^(-4/3:ℝ)) := by ring
            _ = (3/16) * (2:ℝ)^(4/3:ℝ) * z^(2/3:ℝ) := by rw [hzpow]
  · have hc : ContinuousAt (fun z : ℝ => (3/16) * (2:ℝ)^(4/3:ℝ) * z^(2/3:ℝ)) 0 :=
      (Real.continuousAt_rpow_const 0 (2/3:ℝ) (Or.inr (by norm_num))).const_mul _
    have hv : (3/16) * (2:ℝ)^(4/3:ℝ) * (0:ℝ)^(2/3:ℝ) = 0 := by
      rw [Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0), mul_zero]
    have h0 : Tendsto (fun z : ℝ => (3/16) * (2:ℝ)^(4/3:ℝ) * z^(2/3:ℝ)) (𝓝 (0:ℝ)) (𝓝 0) := by
      have ht := hc.tendsto
      rwa [hv] at ht
    exact h0.mono_left nhdsWithin_le_nhds

/-- Decomposition of the centered `J₂` integral on `(z/2, 1]` into the difference part and
the limiting part, for `0 < z ≤ 1`. -/
private theorem centeredJ2_Ioc_eq_add {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (∫ s in Set.Ioc (z/2) 1, (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
      = (∫ s in Set.Ioo (z/2) 1, (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ))
        + ∫ s in Set.Ioo (z/2) 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ) := by
  have hz2 : (0:ℝ) < z/2 := by linarith
  have hz2le : z/2 ≤ 1 := by linarith
  have hg : IntegrableOn (fun s : ℝ => (z^2/4) * s^(-7/3:ℝ)) (Set.Ioo (z/2) 1) :=
    (integrableOn_Ioo_rpow_of_pos hz2 hz2le _).const_mul _
  have hhI : IntegrableOn
      (fun s => (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ))
      (Set.Ioo (z/2) 1) := by
    apply hg.mono' ?_ ?_
    · exact ((continuousOn_centeredJ2_diff hz2).mono
        Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_
      rw [Real.norm_eq_abs]
      exact abs_centeredJ2_diff_le hz hs.1
  have hkI : IntegrableOn (fun s => (Real.exp (-s) - 1) * s^(-4/3:ℝ)) (Set.Ioo (z/2) 1) :=
    integrableOn_exp_sub_one_mul_rpow.mono_set
      (Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi hz2.le))
  rw [integral_Ioc_eq_integral_Ioo, ← integral_add hhI hkI]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s _
  ring

/-- `J₂(z) = 3 (z/2)^{-1/3} - 3 Γ(2/3) + o(1)` as `z → 0⁺`: the centered integral tends to
`∫₀^∞ (e^{-s} - 1) s^{-4/3} ds = -3 Γ(2/3)` (`schlaefliJ2_const`) by dominated convergence
on `(1, ∞)` and on `(0, 1)`, and the `z²/(4s)`-perturbation contributes `O(z^{2/3})`. -/
theorem schlaefliJ2_sub_tendsto :
    Tendsto (fun z => schlaefliJ2 z - 3 * (z/2)^(-1/3:ℝ)) (𝓝[>] (0:ℝ))
      (𝓝 (-3 * Real.Gamma (2/3))) := by
  have heq : (fun z => (∫ s in Set.Ioi (1:ℝ), (Real.exp (-s - z^2/(4*s)) - 1) * s^(-4/3:ℝ))
        + ((∫ s in Set.Ioo (z/2) 1, (Real.exp (-s - z^2/(4*s)) - Real.exp (-s)) * s^(-4/3:ℝ))
          + ∫ s in Set.Ioo (z/2) 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ)))
      =ᶠ[𝓝[>] (0:ℝ)] fun z => schlaefliJ2 z - 3 * (z/2)^(-1/3:ℝ) := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with z hz hz1
    rw [schlaefliJ2_sub_eq_integral hz, centeredJ2_split hz hz1.le,
      centeredJ2_Ioc_eq_add hz hz1.le]
    ring
  refine Tendsto.congr' heq ?_
  have hsum := tendsto_centeredJ2_Ioi_one.add
    (tendsto_centeredJ2_diff_Ioo.add tendsto_airyAsympK_Ioo)
  have hval : (∫ s in Set.Ioi (1:ℝ), (Real.exp (-s) - 1) * s^(-4/3:ℝ))
      + (0 + ∫ s in Set.Ioo 0 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ))
      = -3 * Real.Gamma (2/3) := by
    have hsplit : (∫ s in Set.Ioi 0, (Real.exp (-s) - 1) * s^(-4/3:ℝ))
        = (∫ s in Set.Ioo 0 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ))
          + ∫ s in Set.Ici 1, (Real.exp (-s) - 1) * s^(-4/3:ℝ) := by
      have hdisj : Disjoint (Set.Ioo (0:ℝ) 1) (Set.Ici 1) := by
        rw [Set.disjoint_left]
        rintro s ⟨-, h1⟩ h2
        exact absurd h2 (not_le.mpr h1)
      rw [← Ioo_union_Ici_eq_Ioi zero_lt_one]
      exact setIntegral_union hdisj measurableSet_Ici
        (integrableOn_exp_sub_one_mul_rpow.mono_set Ioo_subset_Ioi_self)
        (integrableOn_exp_sub_one_mul_rpow.mono_set
          (by intro s hs; exact Set.mem_Ioi.mpr (zero_lt_one.trans_le (Set.mem_Ici.mp hs))))
    rw [schlaefliJ2_const, integral_Ici_eq_integral_Ioi] at hsplit
    linarith [hsplit]
  rwa [hval] at hsum


/-! ## Small-`z` asymptotics of `J₁` -/

/-- Powers `s ↦ s^p` are integrable on `(a, b]` when `0 < a ≤ b` (any `p`). -/
private theorem integrableOn_Ioc_rpow_of_pos {a : ℝ} (ha : 0 < a) {b : ℝ} (hab : a ≤ b)
    (p : ℝ) :
    IntegrableOn (fun s : ℝ => s^(p:ℝ)) (Set.Ioc a b) := by
  have h0 : (0:ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h => absurd h.1 (not_le.mpr ha)
  have hI : IntervalIntegrable (fun s : ℝ => s^(p:ℝ)) volume a b :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr h0)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hI

/-- For `0 < s` and any `p`, `|(e^{-s} - 1) s^p| ≤ s^{p+1}` (from `1 - e^{-s} ≤ s`). -/
private theorem abs_exp_sub_one_mul_rpow_le {p : ℝ} {s : ℝ} (hs : 0 < s) :
    |(Real.exp (-s) - 1) * s^(p:ℝ)| ≤ s^(p + 1:ℝ) := by
  have hexp1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.le)
  have hle : 1 - Real.exp (-s) ≤ s := by
    have h := Real.add_one_le_exp (-s)
    linarith
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _),
    abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub]
  calc (1 - Real.exp (-s)) * s^(p:ℝ) ≤ s * s^(p:ℝ) :=
      mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hs.le _)
    _ = s^(p + 1:ℝ) := by
      have key : s^(1:ℝ) * s^(p:ℝ) = s^(p + 1:ℝ) := by
        rw [← Real.rpow_add hs, show (1:ℝ) + p = p + 1 by ring]
      rwa [Real.rpow_one] at key

/-- The `J₁` decomposition: for `0 < z`,
`J₁(z) - Γ(1/3) + 3 (z/2)^{1/3} = R₂(z) - R₁(z)` with
`R₂(z) = ∫_{z/2}^∞ (e^{-z²/(4s)} - 1) e^{-s} s^{-2/3} ds` and
`R₁(z) = ∫_0^{z/2} (e^{-s} - 1) s^{-2/3} ds`. -/
private theorem schlaefliJ1_decomp {z : ℝ} (hz : 0 < z) :
    schlaefliJ1 z - Real.Gamma (1/3) + 3 * (z/2)^(1/3:ℝ)
      = (∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ)))
        - ∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ) := by
  have hza : (0:ℝ) < z/2 := by linarith
  have hG0 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x^(-2/3:ℝ)) (Set.Ioi 0) := by
    have h := Real.GammaIntegral_convergent (show (0:ℝ) < 1/3 by norm_num)
    rwa [show (1/3:ℝ) - 1 = -2/3 by norm_num] at h
  have hI1 : IntegrableOn (fun s => Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ))
      (Set.Ioi (z/2)) := integrableOn_schlaefliJ_kernel hz (by norm_num)
  have hI1' : IntegrableOn (fun s => Real.exp (-s) * s^(-2/3:ℝ)) (Set.Ioi (z/2)) :=
    hG0.mono_set (Ioi_subset_Ioi hza.le)
  have hR2I : IntegrableOn
      (fun s => (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ)))
      (Set.Ioi (z/2)) := by
    have heq : (fun s => (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ)))
        = (fun s => Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ))
          - (fun s => Real.exp (-s) * s^(-2/3:ℝ)) := by
      funext s
      simp only [Pi.sub_apply]
      rw [show -s - z^2/(4*s) = -s + -z^2/(4*s) by ring, Real.exp_add]
      ring
    rw [heq]
    exact hI1.sub hI1'
  have hJ : schlaefliJ1 z = (∫ s in Set.Ioi (z/2), Real.exp (-s) * s^(-2/3:ℝ))
      + ∫ s in Set.Ioi (z/2),
          (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ)) := by
    unfold schlaefliJ1
    rw [← integral_add hI1' hR2I]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    dsimp only
    rw [show -s - z^2/(4*s) = -s + -z^2/(4*s) by ring, Real.exp_add]
    ring
  have hG : Real.Gamma (1/3) = (∫ s in Set.Ioc 0 (z/2), Real.exp (-s) * s^(-2/3:ℝ))
      + ∫ s in Set.Ioi (z/2), Real.exp (-s) * s^(-2/3:ℝ) := by
    have hGe : Real.Gamma (1/3) = ∫ s in Set.Ioi 0, Real.exp (-s) * s^(-2/3:ℝ) := by
      have h := Real.Gamma_eq_integral (show (0:ℝ) < 1/3 by norm_num)
      rwa [show (1/3:ℝ) - 1 = -2/3 by norm_num] at h
    rw [hGe, ← Ioc_union_Ioi_eq_Ioi hza.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hG0.mono_set (fun s hs => hs.1)) hI1'
  have hIoc : (∫ s in Set.Ioc 0 (z/2), Real.exp (-s) * s^(-2/3:ℝ))
      = 3 * (z/2)^(1/3:ℝ) + ∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ) := by
    have hpow : ∫ s in Set.Ioc 0 (z/2), s^(-2/3:ℝ) = 3 * (z/2)^(1/3:ℝ) := by
      have h := (integrableOn_and_integral_Ioc_zero_rpow hza.le
        (show (-1:ℝ) < -2/3 by norm_num)).2
      rw [show (-2/3:ℝ) + 1 = 1/3 by norm_num] at h
      rw [h, div_eq_iff (by norm_num : (1/3:ℝ) ≠ 0)]
      ring
    have hIp : IntegrableOn (fun s : ℝ => s^(-2/3:ℝ)) (Set.Ioc 0 (z/2)) :=
      (integrableOn_and_integral_Ioc_zero_rpow hza.le (by norm_num)).1
    have hIe : IntegrableOn (fun s => (Real.exp (-s) - 1) * s^(-2/3:ℝ))
        (Set.Ioc 0 (z/2)) := by
      have hG0' := hG0.mono_set (fun s (hs : s ∈ Set.Ioc 0 (z/2)) => hs.1)
      have heq : (fun s => (Real.exp (-s) - 1) * s^(-2/3:ℝ))
          = (fun s => Real.exp (-s) * s^(-2/3:ℝ)) - (fun s => s^(-2/3:ℝ)) := by
        funext s
        simp only [Pi.sub_apply]
        ring
      rw [heq]
      exact hG0'.sub hIp
    have hsplit : (∫ s in Set.Ioc 0 (z/2), Real.exp (-s) * s^(-2/3:ℝ))
        = (∫ s in Set.Ioc 0 (z/2), s^(-2/3:ℝ))
          + ∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ) := by
      rw [← integral_add hIp hIe]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s _
      ring
    rw [hsplit, hpow]
  rw [hJ, hG, hIoc]
  ring

/-- The `R₁` bound: for `0 < z`,
`|∫_0^{z/2} (e^{-s} - 1) s^{-2/3} ds| ≤ ∫_0^{z/2} s^{1/3} ds = (3/4) (z/2)^{4/3}`. -/
private theorem abs_schlaefliJ1_R1_le {z : ℝ} (hz : 0 < z) :
    |∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)| ≤ (3/4) * (z/2)^(4/3:ℝ) := by
  have hza : (0:ℝ) < z/2 := by linarith
  have hg : IntegrableOn (fun s : ℝ => s^(1/3:ℝ)) (Set.Ioc 0 (z/2)) :=
    (integrableOn_and_integral_Ioc_zero_rpow hza.le (by norm_num)).1
  have hval : ∫ s in Set.Ioc 0 (z/2), s^(1/3:ℝ) = (3/4) * (z/2)^(4/3:ℝ) := by
    have h := (integrableOn_and_integral_Ioc_zero_rpow hza.le
      (show (-1:ℝ) < 1/3 by norm_num)).2
    rw [show (1/3:ℝ) + 1 = 4/3 by norm_num] at h
    rw [h, div_eq_iff (by norm_num : (4/3:ℝ) ≠ 0)]
    ring
  have hf : IntegrableOn (fun s => |(Real.exp (-s) - 1) * s^(-2/3:ℝ)|)
      (Set.Ioc 0 (z/2)) := by
    apply Integrable.mono' hg ?_ ?_
    · have hcont : ContinuousOn (fun s => |(Real.exp (-s) - 1) * s^(-2/3:ℝ)|)
        (Set.Ioi 0) := by
        intro s hs
        exact ((((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).sub
          continuousAt_const).mul
          (Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt hs)))).abs).continuousWithinAt
      exact (hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      rw [Real.norm_eq_abs, abs_abs]
      have h := abs_exp_sub_one_mul_rpow_le (p := -2/3) hs.1
      rwa [show (-2/3:ℝ) + 1 = 1/3 by norm_num] at h
  calc |∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)|
      ≤ ∫ s in Set.Ioc 0 (z/2), |(Real.exp (-s) - 1) * s^(-2/3:ℝ)| := by
        calc |∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)|
            = ‖∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ∫ s in Set.Ioc 0 (z/2), ‖(Real.exp (-s) - 1) * s^(-2/3:ℝ)‖ :=
              norm_integral_le_integral_norm _
          _ = ∫ s in Set.Ioc 0 (z/2), |(Real.exp (-s) - 1) * s^(-2/3:ℝ)| := by
              apply setIntegral_congr_fun measurableSet_Ioc
              intro s _
              exact Real.norm_eq_abs _
    _ ≤ ∫ s in Set.Ioc 0 (z/2), s^(1/3:ℝ) := by
        apply setIntegral_mono_on hf hg measurableSet_Ioc
        intro s hs
        have h := abs_exp_sub_one_mul_rpow_le (p := -2/3) hs.1
        rwa [show (-2/3:ℝ) + 1 = 1/3 by norm_num] at h
    _ = (3/4) * (z/2)^(4/3:ℝ) := hval

/-- The `R₂` bound, first form: for `0 < z ≤ 1`,
`|R₂(z)| ≤ (z²/4)((3/2)(z/2)^{-2/3} + 1)`. -/
private theorem abs_schlaefliJ1_R2_le_aux {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
      ≤ (z^2/4) * ((3/2) * (z/2)^(-2/3:ℝ) + 1) := by
  have hza : (0:ℝ) < z/2 := by linarith
  have hzle : z/2 ≤ 1 := by linarith
  have hdom : IntegrableOn (fun s : ℝ => Real.exp (-s) * s^(-5/3:ℝ)) (Set.Ioi (z/2)) := by
    have h1 : IntegrableOn (fun s : ℝ => Real.exp (-s) * s^(-5/3:ℝ)) (Set.Ioc (z/2) 1) := by
      apply Integrable.mono' (integrableOn_Ioc_rpow_of_pos hza hzle (-5/3)) ?_ ?_
      · have hcont : ContinuousOn (fun s => Real.exp (-s) * s^(-5/3:ℝ))
          (Set.Ioi (z/2)) := by
          intro s hs
          exact ((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).mul
            (Real.continuousAt_rpow_const s _
              (Or.inl (ne_of_gt (hza.trans hs))))).continuousWithinAt
        exact (hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
      · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
        have hs0 : 0 < s := hza.trans hs.1
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
          abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
        calc Real.exp (-s) * s^(-5/3:ℝ) ≤ 1 * s^(-5/3:ℝ) :=
            mul_le_mul_of_nonneg_right
              (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0.le)) (Real.rpow_nonneg hs0.le _)
          _ = s^(-5/3:ℝ) := one_mul _
    have h2 : IntegrableOn (fun s : ℝ => Real.exp (-s) * s^(-5/3:ℝ)) (Set.Ioi 1) := by
      apply Integrable.mono' (integrableOn_exp_neg_Ioi 1) ?_ ?_
      · have hcont : ContinuousOn (fun s => Real.exp (-s) * s^(-5/3:ℝ)) (Set.Ioi 1) := by
          intro s hs
          exact ((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).mul
            (Real.continuousAt_rpow_const s _
              (Or.inl (ne_of_gt (zero_lt_one.trans hs))))).continuousWithinAt
        exact hcont.aestronglyMeasurable measurableSet_Ioi
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
        have hs1 : 1 ≤ s := hs.le
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
          abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hs).le _)]
        have hpow : s^(-5/3:ℝ) ≤ 1 := by
          have h := Real.rpow_le_rpow_of_exponent_le hs1 (show (-5/3:ℝ) ≤ 0 by norm_num)
          rwa [Real.rpow_zero] at h
        calc Real.exp (-s) * s^(-5/3:ℝ) ≤ Real.exp (-s) * 1 :=
            mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
          _ = Real.exp (-s) := mul_one _
    have h := h1.union h2
    rwa [Ioc_union_Ioi_eq_Ioi hzle] at h
  have hpt : ∀ s ∈ Set.Ioi (z/2),
      |(Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
        ≤ (z^2/4) * (Real.exp (-s) * s^(-5/3:ℝ)) := by
    intro s hs
    have hs0 : 0 < s := hza.trans hs
    have hnn : (0:ℝ) ≤ z^2/(4*s) := div_nonneg (sq_nonneg z) (mul_nonneg (by norm_num) hs0.le)
    have hexp1 : Real.exp (-z^2/(4*s)) ≤ 1 := by
      rw [neg_div]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hnn)
    have hle : 1 - Real.exp (-z^2/(4*s)) ≤ z^2/(4*s) := by
      rw [neg_div]
      have h := Real.add_one_le_exp (-(z^2/(4*s)))
      linarith
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hexp1), neg_sub, abs_mul,
      abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
    calc (1 - Real.exp (-z^2/(4*s))) * (Real.exp (-s) * s^(-2/3:ℝ))
        ≤ (z^2/(4*s)) * (Real.exp (-s) * s^(-2/3:ℝ)) :=
        mul_le_mul_of_nonneg_right hle
          (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hs0.le _))
      _ = (z^2/4) * (Real.exp (-s) * s^(-5/3:ℝ)) := by
        have key : s^(-1:ℝ) * s^(-2/3:ℝ) = s^(-5/3:ℝ) := by
          rw [← Real.rpow_add hs0, show (-1:ℝ) + -2/3 = -5/3 by norm_num]
        have h2 : z^2/(4*s) = (z^2/4) * s^(-1:ℝ) := by
          have hsne : s ≠ 0 := hs0.ne'
          rw [Real.rpow_neg_one]
          field_simp
        rw [h2]
        calc (z^2/4 * s^(-1:ℝ)) * (Real.exp (-s) * s^(-2/3:ℝ))
            = (z^2/4) * (Real.exp (-s) * (s^(-1:ℝ) * s^(-2/3:ℝ))) := by ring
          _ = (z^2/4) * (Real.exp (-s) * s^(-5/3:ℝ)) := by rw [key]
  have hfabs : IntegrableOn
      (fun s => |(Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|)
      (Set.Ioi (z/2)) := by
    apply Integrable.mono' (hdom.const_mul (z^2/4)) ?_ ?_
    · have h1 : ContinuousOn (fun s => Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ))
          (Set.Ioi (z/2)) := continuousOn_schlaefliJ_kernel hza _
      have h2 : ContinuousOn (fun s => Real.exp (-s) * s^(-2/3:ℝ)) (Set.Ioi (z/2)) := by
        intro s hs
        exact ((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).mul
          (Real.continuousAt_rpow_const s _
            (Or.inl (ne_of_gt (hza.trans hs))))).continuousWithinAt
      have heq : (fun s => |(Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|)
          = fun s => |Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ)
              - Real.exp (-s) * s^(-2/3:ℝ)| := by
        funext s
        congr 1
        rw [show -s - z^2/(4*s) = -s + -z^2/(4*s) by ring, Real.exp_add]
        ring
      have hcont : ContinuousOn
          (fun s => |Real.exp (-s - z^2/(4*s)) * s^(-2/3:ℝ) - Real.exp (-s) * s^(-2/3:ℝ)|)
          (Set.Ioi (z/2)) := (h1.sub h2).abs
      rw [heq]
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
      rw [Real.norm_eq_abs, abs_abs]
      exact hpt s hs
  have hnorm : |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
      ≤ ∫ s in Set.Ioi (z/2), (z^2/4) * (Real.exp (-s) * s^(-5/3:ℝ)) := by
    calc |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
        ≤ ∫ s in Set.Ioi (z/2),
            |(Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))| := by
          calc |∫ s in Set.Ioi (z/2),
                (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
              = ‖∫ s in Set.Ioi (z/2),
                  (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))‖ :=
                (Real.norm_eq_abs _).symm
            _ ≤ ∫ s in Set.Ioi (z/2),
                  ‖(Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))‖ :=
                norm_integral_le_integral_norm _
            _ = ∫ s in Set.Ioi (z/2),
                  |(Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))| := by
                apply setIntegral_congr_fun measurableSet_Ioi
                intro s _
                exact Real.norm_eq_abs _
      _ ≤ ∫ s in Set.Ioi (z/2), (z^2/4) * (Real.exp (-s) * s^(-5/3:ℝ)) :=
          setIntegral_mono_on hfabs (hdom.const_mul (z^2/4)) measurableSet_Ioi hpt
  rw [integral_const_mul] at hnorm
  have hint : (∫ s in Set.Ioi (z/2), Real.exp (-s) * s^(-5/3:ℝ))
      ≤ (3/2) * (z/2)^(-2/3:ℝ) + 1 := by
    have hsplit : (∫ s in Set.Ioi (z/2), Real.exp (-s) * s^(-5/3:ℝ))
        = (∫ s in Set.Ioc (z/2) 1, Real.exp (-s) * s^(-5/3:ℝ))
          + ∫ s in Set.Ioi 1, Real.exp (-s) * s^(-5/3:ℝ) := by
      rw [← Ioc_union_Ioi_eq_Ioi hzle]
      exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hdom.mono_set Ioc_subset_Ioi_self) (hdom.mono_set (Ioi_subset_Ioi hzle))
    have h1le : (∫ s in Set.Ioc (z/2) 1, Real.exp (-s) * s^(-5/3:ℝ))
        ≤ (3/2) * ((z/2)^(-2/3:ℝ) - 1) := by
      calc (∫ s in Set.Ioc (z/2) 1, Real.exp (-s) * s^(-5/3:ℝ))
          ≤ ∫ s in Set.Ioc (z/2) 1, s^(-5/3:ℝ) := by
            apply setIntegral_mono_on (hdom.mono_set Ioc_subset_Ioi_self)
              (integrableOn_Ioc_rpow_of_pos hza hzle _) measurableSet_Ioc
            intro s hs
            have hs0 : 0 < s := hza.trans hs.1
            calc Real.exp (-s) * s^(-5/3:ℝ) ≤ 1 * s^(-5/3:ℝ) :=
                mul_le_mul_of_nonneg_right
                  (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0.le))
                  (Real.rpow_nonneg hs0.le _)
              _ = s^(-5/3:ℝ) := one_mul _
        _ = (3/2) * ((z/2)^(-2/3:ℝ) - 1) := by
            rw [integral_Ioc_eq_integral_Ioo,
              integral_Ioo_rpow hza hzle (by norm_num : (-5/3:ℝ) ≠ -1), Real.one_rpow,
              show (-5/3:ℝ) + 1 = -2/3 by norm_num, div_eq_iff (by norm_num : (-2/3:ℝ) ≠ 0)]
            ring
    have h2le : (∫ s in Set.Ioi 1, Real.exp (-s) * s^(-5/3:ℝ)) ≤ 1 := by
      calc (∫ s in Set.Ioi 1, Real.exp (-s) * s^(-5/3:ℝ))
          ≤ ∫ s in Set.Ioi 1, Real.exp (-s) := by
            apply setIntegral_mono_on (hdom.mono_set (Ioi_subset_Ioi hzle))
              (integrableOn_exp_neg_Ioi 1) measurableSet_Ioi
            intro s hs
            have hs1 : 1 ≤ s := hs.le
            have hpow : s^(-5/3:ℝ) ≤ 1 := by
              have h := Real.rpow_le_rpow_of_exponent_le hs1 (show (-5/3:ℝ) ≤ 0 by norm_num)
              rwa [Real.rpow_zero] at h
            calc Real.exp (-s) * s^(-5/3:ℝ) ≤ Real.exp (-s) * 1 :=
                mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
              _ = Real.exp (-s) := mul_one _
        _ = Real.exp (-1) := integral_exp_neg_Ioi 1
        _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    rw [hsplit]
    linarith [h1le, h2le]
  calc |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
      ≤ (z^2/4) * ∫ s in Set.Ioi (z/2), Real.exp (-s) * s^(-5/3:ℝ) := hnorm
    _ ≤ (z^2/4) * ((3/2) * (z/2)^(-2/3:ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hint (by positivity)

/-- The `R₂` bound, final form: for `0 < z ≤ 1`, `|R₂(z)| ≤ z^{4/3}`. -/
private theorem abs_schlaefliJ1_R2_le {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
      ≤ z^(4/3:ℝ) := by
  have haux := abs_schlaefliJ1_R2_le_aux hz hz1
  have h2pow2 : (2:ℝ)^(2/3:ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le one_le_two (show (2/3:ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hzpow4 : z^2 ≤ z^(4/3:ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hz hz1
      (show (4/3:ℝ) ≤ ((2:ℕ):ℝ) by norm_num)
    rwa [Real.rpow_natCast] at h
  have hz2pow : (z/2)^(-2/3:ℝ) = (2:ℝ)^(2/3:ℝ) * z^(-2/3:ℝ) := by
    have h2p : (0:ℝ) < (2:ℝ)^(-2/3:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    rw [Real.div_rpow hz.le (by norm_num : (0:ℝ) ≤ 2), div_eq_iff h2p.ne']
    calc z^(-2/3:ℝ) = 1 * z^(-2/3:ℝ) := (one_mul _).symm
      _ = (2:ℝ)^((2/3:ℝ) + (-2/3:ℝ)) * z^(-2/3:ℝ) := by
          rw [show (2/3:ℝ) + -2/3 = 0 by norm_num, Real.rpow_zero]
      _ = (2:ℝ)^(2/3:ℝ) * (2:ℝ)^(-2/3:ℝ) * z^(-2/3:ℝ) := by
          rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      _ = (2:ℝ)^(2/3:ℝ) * z^(-2/3:ℝ) * (2:ℝ)^(-2/3:ℝ) := by ring
  have hzpow : z^2 * z^(-2/3:ℝ) = z^(4/3:ℝ) := by
    rw [← Real.rpow_natCast z 2, ← Real.rpow_add hz]
    norm_num
  calc |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
      ≤ (z^2/4) * ((3/2) * (z/2)^(-2/3:ℝ) + 1) := haux
    _ = (3/8) * (2:ℝ)^(2/3:ℝ) * z^(4/3:ℝ) + z^2/4 := by
        rw [hz2pow]
        calc (z^2/4) * ((3/2) * ((2:ℝ)^(2/3:ℝ) * z^(-2/3:ℝ)) + 1)
            = (3/8) * (2:ℝ)^(2/3:ℝ) * (z^2 * z^(-2/3:ℝ)) + z^2/4 := by ring
          _ = (3/8) * (2:ℝ)^(2/3:ℝ) * z^(4/3:ℝ) + z^2/4 := by rw [hzpow]
    _ ≤ (3/8) * 2 * z^(4/3:ℝ) + z^(4/3:ℝ)/4 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h2pow2 (by norm_num)) (Real.rpow_nonneg hz.le _)
        · calc z^2/4 = z^2 * (1/4) := by ring
            _ ≤ z^(4/3:ℝ) * (1/4) := mul_le_mul_of_nonneg_right hzpow4 (by norm_num)
            _ = z^(4/3:ℝ)/4 := by ring
    _ = z^(4/3:ℝ) := by ring

/-- `J₁(z) = Γ(1/3) - 3 (z/2)^{1/3} + O(z^{4/3})` as `z → 0⁺`:
`J₁(z) - Γ(1/3) + 3 (z/2)^{1/3} = R₂(z) - R₁(z)` with
`|R₂(z)| ≤ z^{4/3}` and `|R₁(z)| ≤ (3/4) (z/2)^{4/3} ≤ (3/4) z^{4/3}` on `(0, 1]`. -/
theorem schlaefliJ1_isBigO :
    (fun z => schlaefliJ1 z - Real.Gamma (1/3) + 3 * (z/2)^(1/3:ℝ))
      =O[𝓝[>] (0:ℝ)] fun z => z^(4/3:ℝ) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨7/4, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with z hz hz1
  have hzpos : (0:ℝ) < z := hz
  have hz1le : z ≤ 1 := hz1.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hzpos.le _)]
  rw [schlaefliJ1_decomp hzpos]
  have hR1 : |∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)|
      ≤ (3/4) * (z/2)^(4/3:ℝ) := abs_schlaefliJ1_R1_le hzpos
  have hR2 : |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
      ≤ z^(4/3:ℝ) := abs_schlaefliJ1_R2_le hzpos hz1le
  have h14 : (z/2)^(4/3:ℝ) ≤ z^(4/3:ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  calc |(∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ)))
        - ∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)|
      ≤ |∫ s in Set.Ioi (z/2), (Real.exp (-z^2/(4*s)) - 1) * (Real.exp (-s) * s^(-2/3:ℝ))|
        + |∫ s in Set.Ioc 0 (z/2), (Real.exp (-s) - 1) * s^(-2/3:ℝ)| := abs_sub _ _
    _ ≤ z^(4/3:ℝ) + (3/4) * (z/2)^(4/3:ℝ) := add_le_add hR2 hR1
    _ ≤ z^(4/3:ℝ) + (3/4) * z^(4/3:ℝ) :=
        add_le_add_right (mul_le_mul_of_nonneg_left h14 (show (0:ℝ) ≤ 3/4 by norm_num)) _
    _ = 7/4 * z^(4/3:ℝ) := by ring

