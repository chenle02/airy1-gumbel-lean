/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.AiryKernel.Conjugates

/-!
# The `L² → L²` bound for the conjugated heat operator

This is the paper's `L² → L²` conjugation lemma:
`‖U_a P_L U_a⁻¹‖_{2→2} ≤ e^{L a²}`, where `U_a f(x) = e^{-ax} f(x)` and
`P_L` is convolution with the heat kernel `p_L`. The conjugated operator is
convolution with `k(v) = e^{-av} p_L(v)`, and `∫ k = e^{L a²}` exactly.

## Main results

* `integral_conjugateHeatKernel`: the exact Gaussian exponential moment
  `∫ v, e^{-av} p_L(v) dv = e^{L a²}` for `0 < L`, proved by completing the
  square `-av - v²/(4L) = La² - (v + 2La)²/(4L)` and translating the Gaussian
  integral.
* `enorm_convolution_conjugateHeat_le`: the pointwise Cauchy–Schwarz bound
  `‖(k ⋆ f)(x)‖ₑ ≤ ‖k‖₁^{1/2} · (∫⁻ t, ‖k t‖ₑ ‖f (x−t)‖ₑ²)^{1/2}`.
* `eLpNorm_conjugateHeat_conv_le`: the function-level form of the conjugation lemma,
  `‖k ⋆ f‖₂ ≤ e^{L a²} ‖f‖₂` for `f ∈ L²(ℝ)`, proved from the pointwise bound
  by Tonelli's theorem and translation invariance of the `L²` seminorm.
-/

namespace AiryConj

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal

/-- The convolution kernel of `U_a P_L U_a⁻¹`: `k(v) = e^{-av} p_L(v)`. -/
noncomputable def conjugateHeatKernel (L a v : ℝ) : ℝ :=
  Real.exp (-a * v) * heatKernel L v

/-- The conjugated kernel is nonnegative for `0 < L`. -/
theorem conjugateHeatKernel_nonneg (hL : 0 < L) (a v : ℝ) :
    0 ≤ conjugateHeatKernel L a v :=
  mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg hL v)

/-- The conjugated kernel is continuous. -/
theorem continuous_conjugateHeatKernel (L a : ℝ) :
    Continuous (conjugateHeatKernel L a) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (continuous_heatKernel L)

/-- The completed-square factorization: since
`-av - v²/(4L) = La² - (v + 2La)²/(4L)`, the conjugated kernel factors as
`e^{-av} p_L(v) = (4πL)^{-1/2} · e^{La²} · e^{-(v+2La)²/(4L)}`. -/
theorem conjugateHeatKernel_eq (hL : 0 < L) (a v : ℝ) :
    conjugateHeatKernel L a v = (4 * Real.pi * L)^(-1/2 : ℝ) * Real.exp (L * a^2)
      * Real.exp (-(v + 2*L*a)^2/(4*L)) := by
  have h : -a * v + -v^2/(4*L) = L * a^2 + -(v + 2*L*a)^2/(4*L) := by
    field_simp
    ring
  unfold conjugateHeatKernel heatKernel
  rw [show Real.exp (-a * v) * ((4 * Real.pi * L)^(-1/2 : ℝ) * Real.exp (-v^2/(4*L)))
      = (4 * Real.pi * L)^(-1/2 : ℝ) * (Real.exp (-a * v) * Real.exp (-v^2/(4*L)))
      from by ring,
    ← Real.exp_add, h, Real.exp_add]
  ring

/-- The conjugated kernel is integrable for `0 < L` (it is a constant times a
translated Gaussian). -/
theorem integrable_conjugateHeatKernel (hL : 0 < L) (a : ℝ) :
    Integrable (conjugateHeatKernel L a) volume := by
  have h4L : (0:ℝ) < (4*L)⁻¹ := by positivity
  have h2 : Integrable (fun v : ℝ => Real.exp (-(4*L)⁻¹ * (v - (-2*L*a))^2)) volume :=
    (integrable_exp_neg_mul_sq h4L).comp_sub_right (-2*L*a)
  have h3 : Integrable (fun v : ℝ => Real.exp (-(v + 2*L*a)^2/(4*L))) volume := by
    have heq : (fun v : ℝ => Real.exp (-(v + 2*L*a)^2/(4*L)))
        = fun v => Real.exp (-(4*L)⁻¹ * (v - (-2*L*a))^2) := by
      funext v
      congr 1
      field_simp
      ring
    rw [heq]
    exact h2
  rw [show (conjugateHeatKernel L a)
      = fun v => (4 * Real.pi * L)^(-1/2 : ℝ) * Real.exp (L * a^2)
        * Real.exp (-(v + 2*L*a)^2/(4*L)) from funext fun v => conjugateHeatKernel_eq hL a v]
  exact h3.const_mul _

/-- The exact Gaussian exponential moment (the operator-norm bound's value):
`∫ v, e^{-av} p_L(v) dv = e^{L a²}` for `0 < L`. -/
theorem integral_conjugateHeatKernel (hL : 0 < L) (a : ℝ) :
    ∫ v : ℝ, conjugateHeatKernel L a v = Real.exp (L * a ^ 2) := by
  have h4πL : (0:ℝ) < 4 * Real.pi * L := by positivity
  rw [show (fun v : ℝ => conjugateHeatKernel L a v)
      = fun v => (4 * Real.pi * L)^(-1/2 : ℝ) * Real.exp (L * a^2)
        * Real.exp (-(v + 2*L*a)^2/(4*L)) from funext fun v => conjugateHeatKernel_eq hL a v]
  rw [integral_const_mul]
  have hG : (∫ v : ℝ, Real.exp (-(v + 2*L*a)^2/(4*L))) = Real.sqrt (4*Real.pi*L) := by
    have h1 : (∫ v : ℝ, Real.exp (-(v + 2*L*a)^2/(4*L)))
        = ∫ v : ℝ, Real.exp (-(4*L)⁻¹ * v^2) := by
      have h2 : (fun v : ℝ => Real.exp (-(v + 2*L*a)^2/(4*L)))
          = fun v => Real.exp (-(4*L)⁻¹ * (v - (-2*L*a))^2) := by
        funext v
        congr 1
        field_simp
        ring
      rw [h2]
      exact MeasureTheory.integral_sub_right_eq_self (μ := volume)
        (fun v => Real.exp (-(4*L)⁻¹ * v^2)) (-2*L*a)
    rw [h1, integral_gaussian]
    congr 1
    field_simp
  rw [hG, Real.sqrt_eq_rpow,
    show (4 * Real.pi * L)^(-1/2 : ℝ) * Real.exp (L * a^2) * (4 * Real.pi * L)^((1/2 : ℝ))
      = ((4 * Real.pi * L)^(-1/2 : ℝ) * (4 * Real.pi * L)^((1/2 : ℝ))) * Real.exp (L * a^2)
      from by ring,
    show (4 * Real.pi * L)^(-1/2 : ℝ) * (4 * Real.pi * L)^((1/2 : ℝ)) = 1 by
      rw [← Real.rpow_add h4πL, show (-1/2 : ℝ) + 1/2 = 0 by norm_num, Real.rpow_zero],
    one_mul]

/-- The `L¹` seminorm of the conjugated kernel is the exact Gaussian moment:
`‖k‖₁ = ∫ k = e^{L a²}` (the kernel is nonnegative). -/
theorem eLpNorm_one_conjugateHeatKernel (hL : 0 < L) (a : ℝ) :
    eLpNorm (conjugateHeatKernel L a) 1 volume = ENNReal.ofReal (Real.exp (L * a^2)) := by
  have h1 : ∫⁻ v, ‖conjugateHeatKernel L a v‖ₑ ∂volume
      = ∫⁻ v, ENNReal.ofReal (conjugateHeatKernel L a v) ∂volume := by
    apply lintegral_congr_ae
    apply Eventually.of_forall
    intro v
    dsimp only
    rw [Real.enorm_eq_ofReal (conjugateHeatKernel_nonneg hL a v)]
  rw [eLpNorm_one_eq_lintegral_enorm (continuous_conjugateHeatKernel L a).aestronglyMeasurable,
    h1,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_conjugateHeatKernel hL a)
      (Eventually.of_forall (fun v => conjugateHeatKernel_nonneg hL a v)),
    integral_conjugateHeatKernel hL a]

/-- Pointwise Cauchy–Schwarz bound for the conjugated convolution: for every `x`,
writing the integrand as `(‖k‖ₑ^{1/2}) · (‖k‖ₑ^{1/2} ‖f‖ₑ)` and applying Hölder
with exponents `2, 2` gives
`‖(k ⋆ f)(x)‖ₑ ≤ (∫⁻ ‖k‖ₑ)^{1/2} · (∫⁻ t, ‖k t‖ₑ ‖f (x−t)‖ₑ²)^{1/2}`. -/
theorem enorm_convolution_conjugateHeat_le (L a : ℝ) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f volume) (x : ℝ) :
    ‖MeasureTheory.convolution (conjugateHeatKernel L a) f (ContinuousLinearMap.mul ℝ ℝ)
        volume x‖ₑ
      ≤ (∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ∂volume) ^ (1/2 : ℝ)
        * (∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ * ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2 : ℝ) := by
  have hu : AEMeasurable (fun t => ‖conjugateHeatKernel L a t‖ₑ ^ (1/2 : ℝ)) volume :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (continuous_conjugateHeatKernel L a).aestronglyMeasurable.enorm
  have hv : AEMeasurable
      (fun t => ‖conjugateHeatKernel L a t‖ₑ ^ (1/2 : ℝ) * ‖f (x - t)‖ₑ) volume :=
    hu.mul (hf.enorm.comp_quasiMeasurePreserving
      (volume.measurePreserving_sub_left x).quasiMeasurePreserving)
  rw [MeasureTheory.convolution_mul]
  calc ‖∫ t, conjugateHeatKernel L a t * f (x - t) ∂volume‖ₑ
      ≤ ∫⁻ t, ‖conjugateHeatKernel L a t * f (x - t)‖ₑ ∂volume :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ^ (1/2 : ℝ)
          * (‖conjugateHeatKernel L a t‖ₑ ^ (1/2 : ℝ) * ‖f (x - t)‖ₑ) ∂volume := by
        apply lintegral_congr_ae
        apply Eventually.of_forall
        intro t
        dsimp only
        have hrw : ‖conjugateHeatKernel L a t‖ₑ ^ (1/2 : ℝ)
              * (‖conjugateHeatKernel L a t‖ₑ ^ (1/2 : ℝ) * ‖f (x - t)‖ₑ)
            = ‖conjugateHeatKernel L a t‖ₑ * ‖f (x - t)‖ₑ := by
          rw [← mul_assoc,
            ← ENNReal.rpow_add_of_nonneg (1/2 : ℝ) (1/2 : ℝ) (by norm_num) (by norm_num),
            show (1/2 : ℝ) + 1/2 = 1 by norm_num, ENNReal.rpow_one]
        rw [enorm_mul, hrw]
    _ ≤ (∫⁻ t, (‖conjugateHeatKernel L a t‖ₑ ^ (1/2 : ℝ)) ^ (2 : ℝ) ∂volume) ^ (1/2 : ℝ)
          * (∫⁻ t, (‖conjugateHeatKernel L a t‖ₑ ^ (1/2 : ℝ) * ‖f (x - t)‖ₑ) ^ (2 : ℝ)
              ∂volume) ^ (1/2 : ℝ) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hu hv
    _ = (∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ∂volume) ^ (1/2 : ℝ)
          * (∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ * ‖f (x - t)‖ₑ ^ (2 : ℝ) ∂volume)
            ^ (1/2 : ℝ) := by
        have hleft : (∫⁻ t, (‖conjugateHeatKernel L a t‖ₑ ^ (1/2 : ℝ)) ^ (2 : ℝ) ∂volume)
            = ∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ∂volume := by
          apply lintegral_congr_ae
          apply Eventually.of_forall
          intro t
          dsimp only
          rw [← ENNReal.rpow_mul, show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
        have hright : (∫⁻ t, (‖conjugateHeatKernel L a t‖ₑ ^ (1/2 : ℝ) * ‖f (x - t)‖ₑ)
              ^ (2 : ℝ) ∂volume)
            = ∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ * ‖f (x - t)‖ₑ ^ (2 : ℝ) ∂volume := by
          apply lintegral_congr_ae
          apply Eventually.of_forall
          intro t
          dsimp only
          rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0:ℝ) ≤ 2 by norm_num),
            ← ENNReal.rpow_mul, show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
        rw [hleft, hright]

/-- The paper's conjugation lemma: convolution by `k = e^{-a·} p_L` is an `L²`
contraction up to the factor `e^{L a²}`: for every `f ∈ L²(ℝ)`,
`‖k ⋆ f‖₂ ≤ e^{L a²} ‖f‖₂`. Function-level form of
`‖U_a P_L U_a⁻¹‖_{2→2} ≤ e^{L a²}`. -/
theorem eLpNorm_conjugateHeat_conv_le (hL : 0 < L) (a : ℝ) (f : ℝ → ℝ)
    (hf : MemLp f 2 volume) :
    MemLp (MeasureTheory.convolution (conjugateHeatKernel L a) f (ContinuousLinearMap.mul ℝ ℝ)
        volume) 2 volume ∧
    eLpNorm (MeasureTheory.convolution (conjugateHeatKernel L a) f (ContinuousLinearMap.mul ℝ ℝ)
        volume) 2 volume ≤
      ENNReal.ofReal (Real.exp (L * a ^ 2)) * eLpNorm f 2 volume := by
  have hk_meas : AEStronglyMeasurable (conjugateHeatKernel L a) volume :=
    (continuous_conjugateHeatKernel L a).aestronglyMeasurable
  have hf_meas : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hf_fin : eLpNorm f 2 volume < ∞ := hf
  have hconv : AEStronglyMeasurable (MeasureTheory.convolution (conjugateHeatKernel L a) f
      (ContinuousLinearMap.mul ℝ ℝ) volume) volume :=
    hk_meas.convolution (ContinuousLinearMap.mul ℝ ℝ) hf_meas
  have hA : ∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ∂volume
      = ENNReal.ofReal (Real.exp (L * a^2)) := by
    rw [← eLpNorm_one_eq_lintegral_enorm hk_meas, eLpNorm_one_conjugateHeatKernel hL a]
  have eLpNorm_two_eq : ∀ g : ℝ → ℝ, AEStronglyMeasurable g volume →
      eLpNorm g 2 volume = (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2 : ℝ) := by
    intro g hg
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg]
    simp
  have hF : AEMeasurable (fun p : ℝ × ℝ => ‖conjugateHeatKernel L a p.2‖ₑ
      * ‖f (p.1 - p.2)‖ₑ ^ (2:ℝ)) (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : ℝ × ℝ => ‖f (p.1 - p.2)‖ₑ) (volume.prod volume) :=
      hf_meas.enorm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)
    have h2 : AEMeasurable (fun p : ℝ × ℝ => ‖f (p.1 - p.2)‖ₑ ^ (2:ℝ))
        (volume.prod volume) :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable h1
    exact ((continuous_enorm.comp (continuous_conjugateHeatKernel L a)).comp
      continuous_snd).measurable.aemeasurable.mul h2
  have hB : AEMeasurable (fun x => ∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ
      * ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume) volume :=
    hF.lintegral_prod_right'
  have hft : ∀ t : ℝ, AEMeasurable (fun x => ‖f (x - t)‖ₑ ^ (2:ℝ)) volume := fun t =>
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (hf_meas.enorm.comp_quasiMeasurePreserving
        (MeasureTheory.measurePreserving_sub_right volume t).quasiMeasurePreserving)
  have htrans : ∀ t : ℝ, ∫⁻ x, ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume
      = eLpNorm f 2 volume ^ (2:ℝ) := by
    intro t
    have h1 : ∫⁻ x, ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂volume :=
      MeasureTheory.lintegral_sub_right_eq_self (μ := volume) (fun x => ‖f x‖ₑ ^ (2:ℝ)) t
    rw [h1, eLpNorm_two_eq f hf_meas, ← ENNReal.rpow_mul,
      show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hpt : ∀ x : ℝ, ‖MeasureTheory.convolution (conjugateHeatKernel L a) f
        (ContinuousLinearMap.mul ℝ ℝ) volume x‖ₑ ^ (2:ℝ)
      ≤ (∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ∂volume)
        * (∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ * ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume) := by
    intro x
    refine (ENNReal.rpow_le_rpow (enorm_convolution_conjugateHeat_le L a f hf_meas x)
      (show (0:ℝ) ≤ 2 by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0:ℝ) ≤ 2 by norm_num),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one]
  have hmain : eLpNorm (MeasureTheory.convolution (conjugateHeatKernel L a) f
        (ContinuousLinearMap.mul ℝ ℝ) volume) 2 volume
      ≤ ENNReal.ofReal (Real.exp (L * a ^ 2)) * eLpNorm f 2 volume := by
    rw [eLpNorm_two_eq _ hconv]
    calc (∫⁻ x, ‖MeasureTheory.convolution (conjugateHeatKernel L a) f
              (ContinuousLinearMap.mul ℝ ℝ) volume x‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2 : ℝ)
        ≤ (∫⁻ x, (∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ∂volume)
            * (∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ * ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume)
            ∂volume) ^ (1/2 : ℝ) :=
          ENNReal.rpow_le_rpow (lintegral_mono hpt) (show (0:ℝ) ≤ 1/2 by norm_num)
      _ = ((∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ∂volume)
            * (∫⁻ x, ∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ * ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume
              ∂volume)) ^ (1/2 : ℝ) := by
          rw [lintegral_const_mul'' _ hB]
      _ = ((∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ∂volume)
            * (∫⁻ t, ∫⁻ x, ‖conjugateHeatKernel L a t‖ₑ * ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume
              ∂volume)) ^ (1/2 : ℝ) := by
          rw [lintegral_lintegral_swap hF]
      _ = ((∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ∂volume)
            * (∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ
                * (∫⁻ x, ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume) ∂volume)) ^ (1/2 : ℝ) := by
          congr 2
          apply lintegral_congr_ae
          apply Eventually.of_forall
          intro t
          dsimp only
          exact lintegral_const_mul'' _ (hft t)
      _ = ((∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ∂volume)
            * (∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ * eLpNorm f 2 volume ^ (2:ℝ) ∂volume))
            ^ (1/2 : ℝ) := by
          congr 2
          apply lintegral_congr_ae
          apply Eventually.of_forall
          intro t
          dsimp only
          rw [htrans t]
      _ = ((∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ∂volume)
            * ((∫⁻ t, ‖conjugateHeatKernel L a t‖ₑ ∂volume)
              * eLpNorm f 2 volume ^ (2:ℝ))) ^ (1/2 : ℝ) := by
          rw [lintegral_mul_const'' _ hk_meas.enorm]
      _ = ENNReal.ofReal (Real.exp (L * a ^ 2)) * eLpNorm f 2 volume := by
          rw [hA]
          have h1 : ENNReal.ofReal (Real.exp (L * a ^ 2))
              * (ENNReal.ofReal (Real.exp (L * a ^ 2)) * eLpNorm f 2 volume ^ (2:ℝ))
              = (ENNReal.ofReal (Real.exp (L * a ^ 2)) * eLpNorm f 2 volume) ^ (2:ℝ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0:ℝ) ≤ 2 by norm_num),
              ENNReal.rpow_two (ENNReal.ofReal (Real.exp (L * a ^ 2)))]
            ring
          rw [h1, ← ENNReal.rpow_mul, show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one]
  exact ⟨hmain.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf_fin), hmain⟩

end AiryConj
