/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryTransformL2
import Airy1GumbelContrib.TwoTime.TwoTimeBlock
import Airy1GumbelContrib.TwoTime.TwoTimeKernel

/-! # `‖Q‖ ≤ 1` for the two-time block operator

For all levels `x₁, x₂` and every `d > 0` the two-time block operator
`Q = qOp x₁ x₂ hd` on `L²(ℝ)` is a contraction (`norm_qOp_le_one`).

## Factorisation

The kernel `qKer x₁ x₂ d (u, m) = 1_{u > x₁} ∫ Ai(u + y) 1_{y ≤ x₁} p_d(y − m) dy · 1_{m > x₂}`
factorises as `Q = P₁ B₀ P̄₁ e^{dΔ} P₂`, with `P₂ = 1_{> x₂}`, `e^{dΔ}` convolution with the heat
kernel `p_d`, `P̄₁ = 1_{≤ x₁}`, `B₀` the Airy transform and `P₁ = 1_{> x₁}`
(`integral_qKer_mul_eq`, by Fubini).  On a Schwartz function `ψ`, with
`G = 1_{> x₂} ψ` and `h = qHeatFun x₁ d G = 1_{≤ x₁} (p_d ⋆ G)`:

* `‖G‖₂ ≤ ‖ψ‖₂` (indicator);
* `‖h‖₂ ≤ ‖G‖₂` and `h ∈ L¹` (`eLpNorm_qHeatFun_le`, `integrable_qHeatFun`: Jensen against the
  probability density `p_d(y − ·)` and Tonelli, the heat contraction);
* `‖B₀ h‖₂ ≤ ‖h‖₂` (`AiryTransform.eLpNorm_integral_airyAiReal_mul_le`, the
  `L¹ ∩ L²` Airy bound of `Airy/AiryTransformL2.lean`);
* `‖1_{> x₁} B₀ h‖₂ ≤ ‖B₀ h‖₂`.

Density of `𝓢` in `L²` and continuity of `Q` conclude.

## Scope

This result improves the bound `‖Q‖ ≤ C √(1 + d)`
(`exists_enorm_qOp_le_sqrt`, used in `TwoTimeSharpSqrt`/`TwoTimeSharpD`) by `‖Q‖ ≤ 1`, which
removes the source of the `√(1 + d)` prefactor in the sharp-Ψ excess bound; it is used in
`TwoTimeSharpE`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

noncomputable section

namespace AiryFdd

/-- The heat-smoothed, cut-off input of the Airy factor of `Q`:
`qHeatFun x₁ d G y = 1_{y ≤ x₁} ∫ p_d(y − m) G(m) dm`. -/
def qHeatFun (x₁ d : ℝ) (G : ℝ → ℝ) (y : ℝ) : ℝ :=
  (Iic x₁).indicator (fun _ => (1 : ℝ)) y * ∫ m, heatKernel d (y - m) * G m

private lemma integrable_heatKernel_sub_mul {d : ℝ} (hd : 0 < d) {G : ℝ → ℝ}
    (hG : Integrable G) (y : ℝ) :
    Integrable fun m => heatKernel d (y - m) * G m := by
  refine hG.bdd_mul (c := (4 * Real.pi * d) ^ (-1 / 2 : ℝ))
    ((continuous_heatKernel d).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun m => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hd _)]
  unfold heatKernel
  exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 (by
    have : 0 < 4 * d := by positivity
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) this.le))

/-- For integrable `G` and `d > 0`, `qHeatFun x₁ d G` is integrable. -/
theorem integrable_qHeatFun (x₁ : ℝ) {d : ℝ} (hd : 0 < d) {G : ℝ → ℝ} (hG : Integrable G) :
    Integrable (qHeatFun x₁ d G) := by
  have hc := hG.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) (integrable_heatKernel hd)
  have hc' : Integrable fun y => ∫ m, heatKernel d (y - m) * G m := by
    refine hc.congr (Eventually.of_forall fun y => ?_)
    simp only [convolution_def, ContinuousLinearMap.mul_apply', mul_comm]
  refine hc'.bdd_mul (c := 1) (measurable_indicator_one _ measurableSet_Iic).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]; exact abs_indicator_one_le _ _

/-- **Heat contraction.** For `d > 0` and `G ∈ L¹ ∩ L²`, `‖qHeatFun x₁ d G‖₂ ≤ ‖G‖₂`. -/
theorem eLpNorm_qHeatFun_le (x₁ : ℝ) {d : ℝ} (hd : 0 < d) {G : ℝ → ℝ} (hGm : Measurable G)
    (hG : Integrable G) (hG2 : MemLp G 2 volume) :
    eLpNorm (qHeatFun x₁ d G) 2 volume ≤ eLpNorm G 2 volume := by
  have hGsq := hG2.integrable_sq
  have hp : ∀ y, Integrable fun m => heatKernel d (y - m) :=
    fun y => ((integrable_heatKernel hd).comp_sub_left y)
  have hpt : ∀ y, ENNReal.ofReal (qHeatFun x₁ d G y ^ 2)
      ≤ ∫⁻ m, ENNReal.ofReal (G m ^ 2) * ENNReal.ofReal (heatKernel d (y - m)) := by
    intro y
    have hJ := sq_integral_mul_le (f := G) (p := fun m => heatKernel d (y - m))
      (fun m => heatKernel_nonneg hd _) (hp y)
      (by rw [integral_sub_left_eq_self (fun v => heatKernel d v), integral_heatKernel hd])
      (by simpa only [mul_comm] using integrable_heatKernel_sub_mul hd hG y)
      (by simpa only [mul_comm] using integrable_heatKernel_sub_mul hd hGsq y)
    have hsq : qHeatFun x₁ d G y ^ 2 ≤ (∫ m, G m * heatKernel d (y - m)) ^ 2 := by
      unfold qHeatFun
      rw [mul_pow]
      simp_rw [mul_comm (G _)]
      exact mul_le_of_le_one_left (sq_nonneg _) (by
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (abs_indicator_one_le _ _))
    calc ENNReal.ofReal (qHeatFun x₁ d G y ^ 2)
        ≤ ENNReal.ofReal (∫ m, G m ^ 2 * heatKernel d (y - m)) :=
          ENNReal.ofReal_le_ofReal (hsq.trans hJ)
      _ = ∫⁻ m, ENNReal.ofReal (G m ^ 2 * heatKernel d (y - m)) :=
          ofReal_integral_eq_lintegral_ofReal
            (by simpa only [mul_comm] using integrable_heatKernel_sub_mul hd hGsq y)
            (Eventually.of_forall fun m => mul_nonneg (sq_nonneg _) (heatKernel_nonneg hd _))
      _ = _ := lintegral_congr fun m => ENNReal.ofReal_mul (sq_nonneg _)
  have hpm : ∀ m, ∫⁻ y, ENNReal.ofReal (heatKernel d (y - m)) = 1 := fun m => by
    rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_heatKernel hd).comp_sub_right m)
      (Eventually.of_forall fun y => heatKernel_nonneg hd _),
      integral_sub_right_eq_self (fun v => heatKernel d v), integral_heatKernel hd,
      ENNReal.ofReal_one]
  have hmeasP : Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal (G q.2 ^ 2) * ENNReal.ofReal (heatKernel d (q.1 - q.2)) :=
    (ENNReal.measurable_ofReal.comp ((hGm.comp measurable_snd).pow_const 2)).mul
      (ENNReal.measurable_ofReal.comp ((continuous_heatKernel d).measurable.comp
        (measurable_fst.sub measurable_snd)))
  refine eLpNorm_le_of_lintegral_sq_le_lintegral_sq
    (integrable_qHeatFun x₁ hd hG).aestronglyMeasurable hGm.aestronglyMeasurable ?_
  calc ∫⁻ y, ENNReal.ofReal (qHeatFun x₁ d G y ^ 2)
      ≤ ∫⁻ y, ∫⁻ m, ENNReal.ofReal (G m ^ 2) * ENNReal.ofReal (heatKernel d (y - m)) :=
        lintegral_mono hpt
    _ = ∫⁻ m, ∫⁻ y, ENNReal.ofReal (G m ^ 2) * ENNReal.ofReal (heatKernel d (y - m)) :=
        lintegral_lintegral_swap hmeasP.aemeasurable
    _ = ∫⁻ m, ENNReal.ofReal (G m ^ 2) := by
        refine lintegral_congr fun m => ?_
        rw [lintegral_const_mul (ENNReal.ofReal (G m ^ 2))
          (f := fun y => ENNReal.ofReal (heatKernel d (y - m)))
          ((continuous_heatKernel d).comp
            (continuous_id.sub continuous_const)).measurable.ennreal_ofReal,
          hpm m, mul_one]

/-- **Kernel factorisation of `Q`.** For integrable measurable `ψ`,
`∫ qKer(u, m) ψ(m) dm = 1_{u > x₁} ∫ Ai(u + y) h(y) dy` with
`h = qHeatFun x₁ d (1_{> x₂} ψ)`, i.e. `Q = P₁ B₀ P̄₁ e^{dΔ} P₂`. -/
theorem integral_qKer_mul_eq (x₁ x₂ : ℝ) {d : ℝ} (hd : 0 < d) {ψ : ℝ → ℝ}
    (hψm : Measurable ψ) (hψ : Integrable ψ) (u : ℝ) :
    ∫ m, qKer x₁ x₂ d (u, m) * ψ m
      = (Ioi x₁).indicator (fun _ => (1 : ℝ)) u * ∫ y, airyAiReal (u + y)
          * qHeatFun x₁ d (fun m => (Ioi x₂).indicator (fun _ => (1 : ℝ)) m * ψ m) y := by
  set G : ℝ → ℝ := fun m => (Ioi x₂).indicator (fun _ => (1 : ℝ)) m * ψ m with hGdef
  have hGm : Measurable G :=
    (measurable_indicator_one _ measurableSet_Ioi).mul hψm
  have hG : Integrable G := hψ.bdd_mul (c := 1)
    (measurable_indicator_one _ measurableSet_Ioi).aestronglyMeasurable
    (Eventually.of_forall fun m => by
      rw [Real.norm_eq_abs]; exact abs_indicator_one_le _ _)
  set F : ℝ → ℝ → ℝ := fun y m => airyAiReal (u + y)
    * ((Iic x₁).indicator (fun _ => (1 : ℝ)) y * heatKernel d (y - m)) * G m with hF
  obtain ⟨C, hC0, hC⟩ := AiryTransform.exists_norm_airyAiReal_le
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hdom := (hG.norm).convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
      (integrable_heatKernel hd) (μ := volume) (ν := volume)
    refine (hdom.const_mul C).mono' ?_ (Eventually.of_forall fun q => ?_)
    · exact ((((AiryConj.continuous_airyAiReal.comp
        (continuous_const.add continuous_id)).measurable.comp measurable_fst).mul
        (((measurable_indicator_one _ measurableSet_Iic).comp measurable_fst).mul
          ((continuous_heatKernel d).measurable.comp
            (measurable_fst.sub measurable_snd)))).mul
        (hGm.comp measurable_snd)).aestronglyMeasurable
    · obtain ⟨y, m⟩ := q
      simp only [Function.uncurry_apply_pair, hF, ContinuousLinearMap.mul_apply', norm_mul,
        Real.norm_eq_abs]
      have h1 := hC (u + y)
      rw [Complex.norm_real, Real.norm_eq_abs] at h1
      have h2 := abs_indicator_one_le (Iic x₁) y
      have h3 := heatKernel_nonneg hd (y - m)
      rw [abs_of_nonneg h3]
      calc |airyAiReal (u + y)| * (|(Iic x₁).indicator (fun _ => (1 : ℝ)) y|
            * heatKernel d (y - m)) * |G m|
          ≤ C * (1 * heatKernel d (y - m)) * |G m| := by gcongr
        _ = C * (|G m| * heatKernel d (y - m)) := by ring
  have hswap := integral_integral_swap hFi
  unfold qKer blkKer
  have hl : ∀ m, (Ioi x₁).indicator (fun _ => (1 : ℝ)) u
      * (∫ y, airyAiReal (u + y) * ((Iic x₁).indicator (fun _ => (1 : ℝ)) y
        * heatKernel d (y - m))) * (Ioi x₂).indicator (fun _ => (1 : ℝ)) m * ψ m
      = (Ioi x₁).indicator (fun _ => (1 : ℝ)) u * ∫ y, F y m := fun m => by
    rw [hF]; simp only
    rw [integral_mul_const, hGdef]; ring
  simp_rw [hl]
  rw [integral_const_mul, ← hswap]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hF, qHeatFun]
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1; funext m; ring

/-- **`‖Q‖ ≤ 1`.** For all levels `x₁, x₂` and every `d > 0`, the two-time block operator
`qOp x₁ x₂ hd` on `L²(ℝ)` has operator norm at most `1`. -/
theorem norm_qOp_le_one (x₁ x₂ : ℝ) {d : ℝ} (hd : 0 < d) : ‖qOp x₁ x₂ hd‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => ?_
  rw [one_mul]
  refine (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℝ) (p := 2) ENNReal.ofNat_ne_top
    (μ := volume)).induction_on g
    (isClosed_le (continuous_norm.comp (qOp x₁ x₂ hd).continuous) continuous_norm)
    fun ψ => ?_
  rw [SchwartzMap.toLpCLM_apply]
  set G : ℝ → ℝ := fun m => (Ioi x₂).indicator (fun _ => (1 : ℝ)) m * ψ m with hGdef
  have hψm : Measurable ψ := ψ.continuous.measurable
  have hind : Measurable ((Ioi x₂).indicator fun _ => (1 : ℝ)) :=
    measurable_indicator_one _ measurableSet_Ioi
  have hGm : Measurable G := hind.mul hψm
  have hGψ : ∀ m, ‖G m‖ ≤ ‖ψ m‖ := fun m => by
    simp only [hGdef, norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_indicator_one_le _ _)
  have hG : Integrable G :=
    ψ.integrable.norm.mono' hGm.aestronglyMeasurable (Eventually.of_forall fun m => hGψ m)
  have hGle : eLpNorm G 2 volume ≤ eLpNorm ψ 2 volume :=
    eLpNorm_mono hGm.aestronglyMeasurable hGψ
  have hG2 : MemLp G 2 volume := hGle.trans_lt (ψ.memLp 2 volume)
  have hh := eLpNorm_qHeatFun_le x₁ hd hGm hG hG2
  have hh2 : MemLp (qHeatFun x₁ d G) 2 volume := hh.trans_lt hG2
  have hae : (qOp x₁ x₂ hd (ψ.toLp 2 volume) : ℝ → ℝ) =ᵐ[volume]
      fun u => (Ioi x₁).indicator (fun _ => (1 : ℝ)) u
        * ∫ y, airyAiReal (u + y) * qHeatFun x₁ d G y := by
    filter_upwards [HilbertSchmidt.kernelOperator_apply_ae (memLp_qKer x₁ x₂ hd)
      (ψ.toLp 2 volume)] with u hu
    rw [qOp, hu, HilbertSchmidt.kernelIntegralFun,
      ← integral_qKer_mul_eq x₁ x₂ hd hψm ψ.integrable u]
    refine integral_congr_ae ?_
    filter_upwards [ψ.coeFn_toLp 2 volume] with m hm
    rw [hm]
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hae]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) ?_
  calc eLpNorm (fun u => (Ioi x₁).indicator (fun _ => (1 : ℝ)) u
          * ∫ y, airyAiReal (u + y) * qHeatFun x₁ d G y) 2 volume
      ≤ eLpNorm (fun u => ∫ y, airyAiReal (u + y) * qHeatFun x₁ d G y) 2 volume := by
        refine eLpNorm_mono ((Lp.aestronglyMeasurable _).congr hae) fun u => ?_
        rw [norm_mul, Real.norm_eq_abs (Set.indicator _ _ _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (abs_indicator_one_le _ _)
    _ ≤ eLpNorm (qHeatFun x₁ d G) 2 volume :=
        AiryTransform.eLpNorm_integral_airyAiReal_mul_le (integrable_qHeatFun x₁ hd hG) hh2
    _ ≤ eLpNorm G 2 volume := hh
    _ ≤ eLpNorm ψ 2 volume := hGle
    _ = eLpNorm (ψ.toLp 2 volume : ℝ → ℝ) 2 volume :=
        (eLpNorm_congr_ae (ψ.coeFn_toLp 2 volume)).symm

end AiryFdd

end
