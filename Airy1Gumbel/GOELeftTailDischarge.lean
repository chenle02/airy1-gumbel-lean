/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.GOELeftTail
import Airy1Gumbel.GOETraceBound
import Airy1GumbelContrib.GOE.GOESpectralSection
import Airy1GumbelContrib.FddMeasure.TasepScaling

/-!
# A cubic GOE left-tail bound

The localized Hermite family gives the determinant bound at large negative
levels. The flat TASEP limit bounds the one-time function on the remaining
bounded interval.
-/

namespace Airy1Gumbel

open Filter MeasureTheory
open scoped Topology

/-- The one-time Airy candidate CDF is at most one, by passage to the limit
from probability measures of the flat TASEP observations. -/
theorem airy1FinCdf_singleton_le_one_of_flatTasep (x : ℝ) :
    AiryFdd.airy1FinCdf {0} (fun _ => x) ≤ 1 := by
  let I : Finset ℝ := {0}
  let u : I → ℝ := fun _ => x
  have ht : Tendsto (fun n : ℕ => AiryFdd.flatTasepCdf n I u) atTop
      (𝓝 (AiryFdd.airy1FinCdf I u)) := by
    simpa only [AiryFdd.airyExtendedSeries_eq_airy1FinCdf] using
      AiryFdd.tendsto_flatTasepCdf_extendedSeries I u
  apply le_of_tendsto_of_tendsto' ht tendsto_const_nhds
  intro n
  let _ := AiryFdd.flatTasepLaw_isProbabilityMeasure n I
  exact measureReal_le_one

/-- For cutoffs at least `16`, the localized-family determinant bound has
rate constant `1/163840` and prefactor `exp(C_tr)`, where `C_tr` bounds the absolute trace. -/
theorem fredholmDet_goeOp_le_cubic (M : ℝ) (hM : 16 ≤ M) {C_tr : ℝ}
    (htr : |HilbertSchmidt.trace (AiryFdd.goeOp (-M))| ≤ C_tr) :
    HilbertSchmidt.fredholmDet (AiryFdd.goeOp (-M)) 1 ≤
      Real.exp C_tr * Real.exp (-(1 / 163840 : ℝ) * M ^ 3) := by
  let T := M * Real.sqrt M
  let N := GOELocalization.goeModeCount M
  let tr := HilbertSchmidt.trace (AiryFdd.goeOp (-M))
  have hM₀ : 0 ≤ M := by linarith
  have hT : 64 ≤ T := by
    have h16 : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    have hs : 4 ≤ Real.sqrt M := h16 ▸ Real.sqrt_le_sqrt hM
    change 64 ≤ M * Real.sqrt M
    nlinarith [mul_le_mul hM hs (by norm_num : (0 : ℝ) ≤ 4) hM₀]
  have hTsq : T ^ 2 = M ^ 3 := by
    dsimp [T]
    rw [mul_pow, Real.sq_sqrt hM₀]
    ring
  have hN : T / 2560 ≤ (N : ℝ) := by
    change T / 2560 ≤ ((⌊T / 2560⌋₊ + 1 : ℕ) : ℝ)
    rw [Nat.cast_add, Nat.cast_one]
    exact (Nat.lt_floor_add_one _).le
  have h₄ : 4 ≤ Real.exp 2 := by
    have h₂ := Real.add_one_le_exp (1 : ℝ)
    norm_num at h₂
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [mul_le_mul h₂ h₂ (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_nonneg _)]
  have hq : 4 * Real.exp (-T / 16) ≤ Real.exp (-T / 32) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-T / 16) :=
        mul_le_mul_of_nonneg_right h₄ (Real.exp_nonneg _)
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have htrace : -tr ≤ C_tr := (neg_le_abs _).trans htr
  have hsize : (N : ℝ) ≤ (N : ℝ) * (T / 64) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (show 1 ≤ T / 64 by linarith) (Nat.cast_nonneg (α := ℝ) N)
  have hrate : M ^ 3 / 163840 ≤ (N : ℝ) * (T / 64) := by
    have h := mul_le_mul_of_nonneg_right hN (show 0 ≤ T / 64 by linarith)
    nlinarith [hTsq]
  calc
    _ ≤ (4 * Real.exp (-T / 16)) ^ N * Real.exp ((N : ℝ) - tr) :=
      GOELocalization.fredholmDet_goeOp_le_defect M hM
    _ ≤ (Real.exp (-T / 32)) ^ N * Real.exp ((N : ℝ) - tr) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hq N) (Real.exp_nonneg _)
    _ = Real.exp ((N : ℝ) * (-T / 32) + ((N : ℝ) - tr)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)

/-- The one-time Airy₁ GOE determinant has a cubic left tail at levels `-M` for every `M ≥ 0`.
One may take `c = 1/163840` and `C = exp(C_tr + 16³ c)`, with `C_tr` any
positive uniform bound on the absolute trace of the GOE operator at nonpositive cuts. -/
theorem goeLeftTail_holds : Airy1Gumbel.GOELeftTail := by
  obtain ⟨C_tr, hC_tr, htr⟩ := abs_trace_goeOp_left_bounded
  let c : ℝ := 1 / 163840
  have hc : 0 < c := by norm_num [c]
  refine ⟨Real.exp (C_tr + 16 ^ 3 * c), c, Real.exp_pos _, hc, ?_⟩
  intro M hM
  by_cases hlarge : 16 ≤ M
  · rw [AiryFdd.airy1FinCdf_singleton_eq_goe]
    calc
      _ ≤ Real.exp C_tr * Real.exp (-c * M ^ 3) :=
        fredholmDet_goeOp_le_cubic M hlarge (htr M hM)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity))) (Real.exp_nonneg _)
  · have hpow : M ^ 3 ≤ (16 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hM (le_of_not_ge hlarge) 3
    calc
      _ ≤ 1 := airy1FinCdf_singleton_le_one_of_flatTasep (-M)
      _ = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp ((C_tr + 16 ^ 3 * c) + -c * M ^ 3) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hpow hc.le]
      _ = _ := Real.exp_add _ _

end Airy1Gumbel
