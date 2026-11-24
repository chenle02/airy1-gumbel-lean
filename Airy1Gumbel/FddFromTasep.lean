/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.FddRectangle
import Airy1GumbelContrib.FddMeasure.TasepScaling

/-!
# Airy₁ finite-dimensional laws from flat TASEP

The discrete box inequalities pass to the extended Airy determinant limit.
The GOE left tail supplies grounding for the resulting finite-dimensional laws.
-/

open Filter MeasureTheory
open scoped Topology

namespace Airy1Gumbel

/-- The discrete CDFs converge to the Airy₁ finite-dimensional CDF. -/
theorem tendsto_flatTasepCdf_airy1FinCdf (I : Finset ℝ) (x : I → ℝ) :
    Tendsto (fun N : ℕ => AiryFdd.flatTasepCdf N I x) atTop
      (𝓝 (AiryFdd.airy1FinCdf I x)) := by
  simpa only [AiryFdd.airyExtendedSeries_eq_airy1FinCdf] using
    AiryFdd.tendsto_flatTasepCdf_extendedSeries I x

/-- The flat TASEP limit preserves nonnegativity of the box CDF. -/
theorem airy1FinCdf_nonneg_of_tasep (I : Finset ℝ) (x : I → ℝ) :
    0 ≤ AiryFdd.airy1FinCdf I x :=
  le_of_tendsto_of_tendsto' tendsto_const_nhds (tendsto_flatTasepCdf_airy1FinCdf I x)
    (fun _ => measureReal_nonneg)

/-- The lower-orthant inclusion passes to the flat TASEP limit. -/
theorem airy1FinCdf_monotone_of_tasep (I : Finset ℝ) :
    Monotone (AiryFdd.airy1FinCdf I) := by
  intro a b hab
  apply le_of_tendsto_of_tendsto' (tendsto_flatTasepCdf_airy1FinCdf I a)
    (tendsto_flatTasepCdf_airy1FinCdf I b)
  intro N
  letI := AiryFdd.flatTasepLaw_isProbabilityMeasure N I
  apply measureReal_mono
  · intro f hf
    exact fun i hi => (hf i hi).trans (hab i)
  · exact measure_ne_top _ _

/-- The finite alternation over box corners commutes with the flat TASEP limit. -/
theorem airy1FinCdf_rectangle_nonneg (I : Finset ℝ) (a b : I → ℝ) (hab : a ≤ b) :
    0 ≤ AiryFdd.boxCdfIncrement (AiryFdd.airy1FinCdf I) a b := by
  classical
  have h : Tendsto (fun N : ℕ => AiryFdd.boxCdfIncrement (AiryFdd.flatTasepCdf N I) a b)
      atTop (𝓝 (AiryFdd.boxCdfIncrement (AiryFdd.airy1FinCdf I) a b)) := by
    unfold AiryFdd.boxCdfIncrement
    apply tendsto_finsetSum
    intro s _
    exact (tendsto_flatTasepCdf_airy1FinCdf I (fun i => if i ∈ s then b i else a i)).const_mul _
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds h
    (fun N => AiryFdd.flatTasepCdf_rectangle_nonneg N I hab)

/-- The Airy₁ finite-dimensional laws follow from flat TASEP, with grounding from the GOE left tail. -/
theorem airy1FddPositive_of_goeLeftTail (hT : GOELeftTail) :
    Airy1Gumbel.Airy1FddPositive :=
  airy1FddPositive_of_rectangle hT airy1FinCdf_nonneg_of_tasep
    airy1FinCdf_monotone_of_tasep airy1FinCdf_rectangle_nonneg

end Airy1Gumbel
