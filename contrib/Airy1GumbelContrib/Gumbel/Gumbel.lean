/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The standard Gumbel distribution

Define the standard Gumbel measure over the reals, whose cumulative distribution function
is `x ↦ exp (-exp (-x))`.

## Main definitions
* `gumbelPDFReal`: the function `x ↦ exp (-(x + exp (-x)))`, the probability density
  function of the standard Gumbel distribution.
* `gumbelPDF`: `ℝ≥0∞`-valued pdf, `gumbelPDF x = ENNReal.ofReal (gumbelPDFReal x)`.
* `gumbelCDFReal`: the function `x ↦ exp (-exp (-x))`, the cumulative distribution function.
* `gumbelMeasure`: the standard Gumbel measure on `ℝ`.

## Main results
* `hasDerivAt_gumbelCDFReal`: the Gumbel pdf is the derivative of the Gumbel cdf.
* `lintegral_gumbelPDF_eq_one`: the pdf integrates to `1`.
* `isProbabilityMeasure_gumbelMeasure`: the Gumbel measure is a probability measure.
* `cdf_gumbelMeasure`: `cdf gumbelMeasure x = exp (-exp (-x))`.

## Possible extensions
Generalize to location `μ` and scale `β`; the mean (the Euler–Mascheroni constant) and
the moment generating function `Γ(1 - t)` for `t < 1`.
-/

open scoped ENNReal NNReal Topology

open MeasureTheory Real Set Filter

namespace ProbabilityTheory

/-- The pdf of the standard Gumbel distribution. -/
noncomputable def gumbelPDFReal (x : ℝ) : ℝ := Real.exp (-(x + Real.exp (-x)))

/-- The cdf of the standard Gumbel distribution: `x ↦ exp (-exp (-x))`. -/
noncomputable def gumbelCDFReal (x : ℝ) : ℝ := Real.exp (-Real.exp (-x))

/-- The pdf of the standard Gumbel distribution, as a function valued in `ℝ≥0∞`. -/
noncomputable def gumbelPDF (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (gumbelPDFReal x)

lemma gumbelPDF_eq (x : ℝ) : gumbelPDF x = ENNReal.ofReal (gumbelPDFReal x) := rfl

/-- The Gumbel pdf is positive everywhere. -/
lemma gumbelPDFReal_pos (x : ℝ) : 0 < gumbelPDFReal x := Real.exp_pos _

/-- The Gumbel pdf is nonnegative. -/
lemma gumbelPDFReal_nonneg (x : ℝ) : 0 ≤ gumbelPDFReal x := (gumbelPDFReal_pos x).le

/-- The Gumbel pdf is continuous. -/
lemma continuous_gumbelPDFReal : Continuous gumbelPDFReal :=
  Real.continuous_exp.comp ((continuous_id.add (Real.continuous_exp.comp continuous_neg)).neg)

/-- The Gumbel cdf is continuous. -/
lemma continuous_gumbelCDFReal : Continuous gumbelCDFReal :=
  Real.continuous_exp.comp ((Real.continuous_exp.comp continuous_neg).neg)

/-- The Gumbel pdf is measurable. -/
@[fun_prop]
lemma measurable_gumbelPDFReal : Measurable gumbelPDFReal := continuous_gumbelPDFReal.measurable

/-- The `ℝ≥0∞`-valued Gumbel pdf is measurable. -/
lemma measurable_gumbelPDF : Measurable gumbelPDF := measurable_gumbelPDFReal.ennreal_ofReal

private lemma two_mul_le_exp (y : ℝ) : 2 * y ≤ Real.exp y := by
  rcases le_total y 0 with hy | hy
  · nlinarith [Real.exp_nonneg y]
  · have h1 : 1 + y / 2 ≤ Real.exp (y / 2) := by linarith [Real.add_one_le_exp (y / 2)]
    have h2 : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : (1 + y / 2) * (1 + y / 2) ≤ Real.exp (y / 2) * Real.exp (y / 2) :=
      mul_le_mul h1 h1 (by linarith) (Real.exp_nonneg _)
    nlinarith [h3, sq_nonneg (1 - y / 2)]

/-- The Gumbel pdf is the derivative of the Gumbel cdf. -/
lemma hasDerivAt_gumbelCDFReal (x : ℝ) :
    HasDerivAt gumbelCDFReal (gumbelPDFReal x) x := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
    have h := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg
    simpa [Function.comp_def] using h
  have h_inner : HasDerivAt (fun x : ℝ => -Real.exp (-x)) (Real.exp (-x)) x := by
    have h := h1.neg
    rw [neg_neg] at h
    exact h
  have h := (Real.hasDerivAt_exp (-Real.exp (-x))).comp x h_inner
  unfold gumbelCDFReal gumbelPDFReal
  rw [neg_add, Real.exp_add, mul_comm]
  exact h

/-- The Gumbel cdf tends to `1` at `+∞`. -/
lemma tendsto_gumbelCDFReal_atTop : Tendsto gumbelCDFReal atTop (𝓝 1) := by
  unfold gumbelCDFReal
  have h1 : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h2 : Tendsto (fun x : ℝ => -Real.exp (-x)) atTop (𝓝 0) := by
    simpa using h1.neg
  have h3 := (Real.continuous_exp.tendsto 0).comp h2
  simpa [Real.exp_zero, Function.comp_def] using h3

/-- The Gumbel cdf tends to `0` at `-∞`. -/
lemma tendsto_gumbelCDFReal_atBot : Tendsto gumbelCDFReal atBot (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.exp (-x)) atBot atTop :=
    Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  have h2 : Tendsto (fun x : ℝ => -Real.exp (-x)) atBot atBot :=
    tendsto_neg_atTop_atBot.comp h1
  exact Real.tendsto_exp_atBot.comp h2

/-- The Gumbel pdf is integrable on `(-∞, 0]`, by comparison with `exp`. -/
lemma integrableOn_gumbelPDFReal_Iic_zero : IntegrableOn gumbelPDFReal (Iic 0) := by
  apply Integrable.mono' (integrableOn_exp_Iic 0) measurable_gumbelPDFReal.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
  rw [Real.norm_of_nonneg (gumbelPDFReal_nonneg x)]
  unfold gumbelPDFReal
  rw [Real.exp_le_exp]
  have h := two_mul_le_exp (-x)
  linarith

/-- The Gumbel pdf is integrable on every left half-line `(-∞, x]`. -/
lemma integrableOn_gumbelPDFReal_Iic (x : ℝ) : IntegrableOn gumbelPDFReal (Iic x) := by
  rcases le_total x 0 with hx | hx
  · exact integrableOn_gumbelPDFReal_Iic_zero.mono_set (Iic_subset_Iic.mpr hx)
  · rw [← Iic_union_Icc_eq_Iic hx]
    exact integrableOn_gumbelPDFReal_Iic_zero.union
      continuous_gumbelPDFReal.continuousOn.integrableOn_Icc

/-- The Gumbel pdf is integrable on every right half-line `(x, ∞)`: it is the derivative
of the cdf, which is nonnegative and converges at `+∞`. -/
lemma integrableOn_gumbelPDFReal_Ioi (x : ℝ) : IntegrableOn gumbelPDFReal (Ioi x) :=
  MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (fun y _ => hasDerivAt_gumbelCDFReal y)
    (fun y _ => (gumbelPDFReal_pos y).le)
    tendsto_gumbelCDFReal_atTop

/-- The Gumbel pdf is integrable on `ℝ`. -/
lemma integrable_gumbelPDFReal : Integrable gumbelPDFReal := by
  rw [← integrableOn_univ, ← Iic_union_Ioi_of_le (le_refl (0 : ℝ))]
  exact integrableOn_gumbelPDFReal_Iic_zero.union (integrableOn_gumbelPDFReal_Ioi 0)

/-- The integral of the Gumbel pdf over `(-∞, x]` is the cdf, by FTC-2. -/
lemma integral_gumbelPDFReal_Iic (x : ℝ) :
    ∫ y in Iic x, gumbelPDFReal y = gumbelCDFReal x := by
  rw [MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto
    continuous_gumbelCDFReal.continuousWithinAt
    (fun y _ => hasDerivAt_gumbelCDFReal y)
    (integrableOn_gumbelPDFReal_Iic x)
    tendsto_gumbelCDFReal_atBot, sub_zero]

/-- The integral of the Gumbel pdf over `(x, ∞)` is `1 - cdf`, by FTC-2. -/
lemma integral_gumbelPDFReal_Ioi (x : ℝ) :
    ∫ y in Ioi x, gumbelPDFReal y = 1 - gumbelCDFReal x :=
  MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y _ => hasDerivAt_gumbelCDFReal y)
    (integrableOn_gumbelPDFReal_Ioi x)
    tendsto_gumbelCDFReal_atTop

/-- The Gumbel pdf integrates to `1`. -/
@[simp]
lemma lintegral_gumbelPDF_eq_one : ∫⁻ x, gumbelPDF x = 1 := by
  have h : ∫ x, gumbelPDFReal x = 1 := by
    rw [← integral_add_compl (measurableSet_Iic (a := 0)) integrable_gumbelPDFReal, compl_Iic,
      integral_gumbelPDFReal_Iic 0, integral_gumbelPDFReal_Ioi 0]
    ring
  rw [← ENNReal.toReal_eq_one_iff]
  simp_rw [gumbelPDF_eq]
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => gumbelPDFReal_nonneg x)
    measurable_gumbelPDFReal.aestronglyMeasurable]
  exact h

/-- The standard Gumbel measure on `ℝ`. -/
noncomputable def gumbelMeasure : Measure ℝ := volume.withDensity gumbelPDF

/-- The Gumbel measure is a probability measure. -/
instance isProbabilityMeasure_gumbelMeasure : IsProbabilityMeasure gumbelMeasure where
  measure_univ := by
    rw [gumbelMeasure, withDensity_apply gumbelPDF MeasurableSet.univ, Measure.restrict_univ,
      lintegral_gumbelPDF_eq_one]

/-- The cdf of the standard Gumbel measure is `x ↦ exp (-exp (-x))`. -/
lemma cdf_gumbelMeasure (x : ℝ) : cdf gumbelMeasure x = gumbelCDFReal x := by
  rw [cdf_eq_real, gumbelMeasure, measureReal_def, withDensity_apply gumbelPDF measurableSet_Iic]
  simp_rw [gumbelPDF_eq]
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => gumbelPDFReal_nonneg y)
    measurable_gumbelPDFReal.aestronglyMeasurable.restrict]
  exact integral_gumbelPDFReal_Iic x

end ProbabilityTheory
