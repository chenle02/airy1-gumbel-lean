/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryContour
import Airy1GumbelContrib.Airy.AiryLaplaceFull
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# The Fourier transform of the Airy function

With Mathlib's Fourier transform `𝓕 f ξ = ∫ e^{-2πixξ} f x dx`, the Airy function `Ai`
(contrib's series-defined `airyAiReal`, `Airy/Airy.lean`) is a bounded continuous function,
hence a tempered distribution, and its Fourier transform is the unimodular symbol
`ψ(ξ) = exp(i (2πξ)³/3)`:
`𝓕 Ai = ψ` in `𝓢'(ℝ, ℂ)`.
Convention: Mathlib's `𝓕` (kernel `e^{-2πixξ}`), Airy scale `κ = 1`, phase sign `+`
(formally `Ai(x) = ∫ ψ(ξ) e^{2πixξ} dξ`, i.e. DLMF 9.5.1 after `t = 2πξ`).

## Main definitions and results

* `AiryFourier.airySymbol ξ = exp(i (2πξ)³/3)`; `norm_airySymbol` (`‖ψ ξ‖ = 1`),
  `hasTemperateGrowth_airySymbol` (so `fourierMultiplierCLM ℂ airySymbol` is available).
* `airyAiReal_bdd`: `Ai` is bounded on `ℝ` (the contour form with `c = 1` for `x ≥ 0`).
* `integral_airyAi_mul_fourier`: the weak form `∫ Ai(x) 𝓕φ(x) dx = ∫ ψ(ξ) φ(ξ) dξ` for every
  integrable `φ` with integrable `𝓕 φ`; `integral_airyAi_mul_fourier_schwartz` for `φ ∈ 𝓢`.
* `airyAiDist`, `airySymbolDist`: `Ai` and `ψ` as tempered distributions (through `L^∞`).
* `fourier_airyAiDist`: **`𝓕 airyAiDist = airySymbolDist`**.

## Proof idea

Regularise by a Gaussian: `g_δ(x) = Ai(x) e^{-δ²x²}` is integrable, so by self-adjointness of
`𝓕`, `∫ g_δ 𝓕φ = ∫ 𝓕g_δ φ`.  To compute `𝓕 g_δ`, insert the contour formula
(`AiryContour.airyAi_eq_integral`) on the moving line `Re t = δ²`, swap the integrals (Fubini;
the joint integrand has Gaussian decay in both variables), evaluate the complex Gaussian
`x`-integral, and substitute `s = -2πξ + 2δv`.  The result is
`𝓕 g_δ(ξ) = π^{-1/2} ∫ H_δ(ξ, v) dv` with `|H_δ(ξ, v)| ≤ e^{7/12} e^{-v²}` uniformly in
`δ ≤ 1` and `H_0(ξ, v) = ψ(ξ) e^{-v²}`.  Dominated convergence as `δ → 0` on both sides gives
the weak form.

This is the Fourier-side input for an `L²` treatment of the Airy
transform (unitarity of the Airy transform).  Nothing downstream in this package uses it yet.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform SchwartzMap

noncomputable section

namespace AiryFourier

/-- The Airy symbol `ψ(ξ) = exp(i (2πξ)³/3)`. -/
def airySymbol (ξ : ℝ) : ℂ := cexp (I * (2 * (Real.pi : ℂ) * ξ) ^ 3 / 3)

/-- The symbol is unimodular. -/
lemma norm_airySymbol (ξ : ℝ) : ‖airySymbol ξ‖ = 1 := by
  rw [airySymbol,
    show I * (2 * (Real.pi : ℂ) * ξ) ^ 3 / 3 = (((2 * Real.pi * ξ) ^ 3 / 3 : ℝ) : ℂ) * I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-- The symbol is continuous. -/
lemma continuous_airySymbol : Continuous airySymbol := by unfold airySymbol; fun_prop

private lemma continuous_airyAiReal : Continuous airyAiReal :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiReal x).continuousAt

private lemma cube_eq (a b : ℝ) : ((a : ℂ) + b * I) ^ 3 =
    ((a ^ 3 - 3 * a * b ^ 2 : ℝ) : ℂ) + ((3 * a ^ 2 * b - b ^ 3 : ℝ) : ℂ) * I := by
  push_cast
  linear_combination (3 * (a : ℂ) * (b : ℂ) ^ 2 + (b : ℂ) ^ 3 * I) * Complex.I_sq

private lemma re_cube (a b : ℝ) : (((a : ℂ) + b * I) ^ 3).re = a ^ 3 - 3 * a * b ^ 2 := by
  rw [cube_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-- `Ai` is bounded on `ℝ`. -/
lemma airyAiReal_bdd : ∃ C, ∀ x, |airyAiReal x| ≤ C := by
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le_nonpos
  set g : ℝ → ℝ := fun s => Real.exp (1 / 3) * Real.exp (-1 * s ^ 2) with hg_def
  have hg : Integrable g := (integrable_exp_neg_mul_sq one_pos).const_mul _
  refine ⟨max C₀ ((1 / (2 * Real.pi)) * ∫ s, g s), fun x => ?_⟩
  rcases le_total x 0 with hx | hx
  · exact (hC₀ x hx).trans (le_max_left _ _)
  refine le_trans ?_ (le_max_right _ _)
  have h := AiryContour.airyAi_eq_integral 1 one_pos (x : ℂ)
  have hn : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc |airyAiReal x| = ‖Complex.airyAi x‖ := by
        rw [← airyAiReal_ofReal, Complex.norm_real, Real.norm_eq_abs]
    _ = (1 / (2 * Real.pi)) * ‖∫ s : ℝ,
          cexp ((((1 : ℝ) : ℂ) + s * I) ^ 3 / 3 - (x : ℂ) * (((1 : ℝ) : ℂ) + s * I))‖ := by
        rw [h, norm_mul, hn]
    _ ≤ (1 / (2 * Real.pi)) * ∫ s, g s := by
        gcongr
        refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun s => ?_)
        have hre : ((((1 : ℝ) : ℂ) + s * I) ^ 3 / 3 - (x : ℂ) * (((1 : ℝ) : ℂ) + s * I)).re
            = (1 - 3 * s ^ 2) / 3 - x := by
          rw [Complex.sub_re, Complex.div_ofNat_re, re_cube]
          simp
        rw [Complex.norm_exp, hre]
        show Real.exp _ ≤ Real.exp (1 / 3) * Real.exp (-1 * s ^ 2)
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)

/-! ## The Gaussian-regularised Airy function -/

/-- `Ai(x) e^{-δ²x²}`. -/
private def gw (δ x : ℝ) : ℂ := (airyAiReal x : ℂ) * cexp (-((δ ^ 2 : ℝ) : ℂ) * (x : ℂ) ^ 2)

private lemma continuous_gw : Continuous (fun p : ℝ × ℝ => gw p.1 p.2) := by
  unfold gw
  have := continuous_airyAiReal
  fun_prop

private lemma integrable_gw {δ : ℝ} (hδ : 0 < δ) : Integrable (gw δ) := by
  obtain ⟨C, hC⟩ := airyAiReal_bdd
  have hG : Integrable (fun x : ℝ => cexp (-((δ ^ 2 : ℝ) : ℂ) * (x : ℂ) ^ 2)) :=
    integrable_cexp_neg_mul_sq (by rw [Complex.ofReal_re]; positivity)
  exact hG.bdd_mul (c := C)
    (Complex.continuous_ofReal.comp continuous_airyAiReal).aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hC x)

/-- The point `δ² + i(-2πξ + 2δv)`. -/
private def Tt (δ ξ v : ℝ) : ℂ := ((δ ^ 2 : ℝ) : ℂ) + ((-2 * Real.pi * ξ + 2 * δ * v : ℝ) : ℂ) * I

/-- The integrand after the substitution `s = -2πξ + 2δv`. -/
private def H (δ ξ v : ℝ) : ℂ :=
  cexp (Tt δ ξ v ^ 3 / 3 + ((δ ^ 2 / 4 - v ^ 2 : ℝ) : ℂ) + ((δ * v : ℝ) : ℂ) * I)

private lemma integrable_exp_quad (a β : ℝ) (ha : 0 < a) :
    Integrable (fun s : ℝ => Real.exp (β * s - a * s ^ 2)) := by
  have h := integrable_cexp_quadratic (b := (a : ℂ)) (by simpa using ha) (β : ℂ) 0
  refine h.norm.congr (Eventually.of_forall fun s => ?_)
  simp only [Complex.norm_exp]
  rw [show -(a : ℂ) * (s : ℂ) ^ 2 + β * s + 0 = ((β * s - a * s ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

/-- The vertical-line point `δ² + is`. -/
private def τ (δ s : ℝ) : ℂ := ((δ ^ 2 : ℝ) : ℂ) + (s : ℂ) * I

/-- The joint `(x, s)` integrand. -/
private def K (δ ξ x s : ℝ) : ℂ :=
  cexp (τ δ s ^ 3 / 3 + (-((δ ^ 2 : ℝ) : ℂ) * (x : ℂ) ^ 2
    + (-τ δ s - 2 * (Real.pi : ℂ) * ξ * I) * x))

private lemma norm_K (δ ξ x s : ℝ) : ‖K δ ξ x s‖ =
    Real.exp ((-δ ^ 2) * x - δ ^ 2 * x ^ 2) *
      (Real.exp ((δ ^ 2) ^ 3 / 3) * Real.exp (-(δ ^ 2) * s ^ 2)) := by
  have hre : (τ δ s ^ 3 / 3 + (-((δ ^ 2 : ℝ) : ℂ) * (x : ℂ) ^ 2
      + (-τ δ s - 2 * (Real.pi : ℂ) * ξ * I) * x)).re
      = ((δ ^ 2) ^ 3 - 3 * δ ^ 2 * s ^ 2) / 3 + (-(δ ^ 2) * x ^ 2 - δ ^ 2 * x) := by
    rw [Complex.add_re, Complex.div_ofNat_re, τ, re_cube]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.add_im, Complex.mul_im, pow_two]
    norm_num
    ring
  rw [K, Complex.norm_exp, hre, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

private lemma integrable_K {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    Integrable (Function.uncurry (K δ ξ)) (volume.prod volume) := by
  have hc : 0 < δ ^ 2 := by positivity
  have h1 := integrable_exp_quad (δ ^ 2) (-δ ^ 2) hc
  have h2 : Integrable (fun s : ℝ => Real.exp ((δ ^ 2) ^ 3 / 3) * Real.exp (-(δ ^ 2) * s ^ 2)) :=
    (integrable_exp_neg_mul_sq hc).const_mul _
  refine (h1.mul_prod h2).mono' ?_ (Eventually.of_forall fun p => ?_)
  · have : Continuous (fun p : ℝ × ℝ => K δ ξ p.1 p.2) := by unfold K τ; fun_prop
    exact this.aestronglyMeasurable
  · rw [Function.uncurry_apply_pair, norm_K]

/-- **Fourier transform of the regularised Airy function.** -/
private lemma fourier_gw {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    𝓕 (gw δ) ξ = ((1 / Real.sqrt Real.pi : ℝ) : ℂ) * ∫ v : ℝ, H δ ξ v := by
  have hc : 0 < δ ^ 2 := by positivity
  -- Step 1: insert the contour formula with `c = δ²`.
  have step1 : ∀ x : ℝ, cexp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * I) • gw δ x =
      (1 / (2 * (Real.pi : ℂ))) * ∫ s, K δ ξ x s := by
    intro x
    rw [gw, airyAiReal_ofReal, AiryContour.airyAi_eq_integral (δ ^ 2) hc, smul_eq_mul]
    have hK : ∀ s, K δ ξ x s = cexp ((((δ ^ 2 : ℝ) : ℂ) + s * I) ^ 3 / 3
        - (x : ℂ) * (((δ ^ 2 : ℝ) : ℂ) + s * I)) *
        (cexp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * I) *
          cexp (-((δ ^ 2 : ℝ) : ℂ) * (x : ℂ) ^ 2)) := by
      intro s
      simp only [K, τ, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hK]
    rw [integral_mul_const]
    ring
  -- Step 2: Fubini.
  have step2 : 𝓕 (gw δ) ξ = (1 / (2 * (Real.pi : ℂ))) * ∫ s, ∫ x, K δ ξ x s := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp_rw [step1]
    rw [integral_const_mul, integral_integral_swap (integrable_K hδ ξ)]
  -- Step 3: the Gaussian `x`-integral.
  have hb : (-((δ ^ 2 : ℝ) : ℂ)).re < 0 := by rw [Complex.neg_re, Complex.ofReal_re]; linarith
  have step3 : ∀ s, ∫ x, K δ ξ x s =
      ((Real.pi : ℂ) / -(-((δ ^ 2 : ℝ) : ℂ))) ^ (1 / 2 : ℂ) *
        cexp (τ δ s ^ 3 / 3 - (-τ δ s - 2 * (Real.pi : ℂ) * ξ * I) ^ 2 /
          (4 * -((δ ^ 2 : ℝ) : ℂ))) := by
    intro s
    rw [← integral_cexp_quadratic hb]
    congr 1
    funext x
    simp only [K]
    congr 1
    ring
  -- Step 4: the substitution `s = -2πξ + 2δv`.
  set E : ℝ → ℂ := fun s => cexp (τ δ s ^ 3 / 3 - (-τ δ s - 2 * (Real.pi : ℂ) * ξ * I) ^ 2 /
          (4 * -((δ ^ 2 : ℝ) : ℂ))) with hE
  have hEH : ∀ v, E (-2 * Real.pi * ξ + 2 * δ * v) = H δ ξ v := by
    intro v
    simp only [hE, H, τ]
    have hT : (((δ ^ 2 : ℝ) : ℂ) + ((-2 * Real.pi * ξ + 2 * δ * v : ℝ) : ℂ) * I) = Tt δ ξ v := rfl
    rw [hT]
    congr 1
    have hδ' : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
    simp only [Tt]
    push_cast
    field_simp
    linear_combination (12 * (δ : ℂ) ^ 2 * (v : ℂ) ^ 2) * Complex.I_sq
  have hsub : ∫ s, E s = ((2 * δ : ℝ) : ℂ) * ∫ v, H δ ξ v := by
    have h := Measure.integral_comp_mul_left (fun w => E (-2 * Real.pi * ξ + w)) (2 * δ)
    rw [integral_add_left_eq_self (fun s => E s) (-2 * Real.pi * ξ)] at h
    simp_rw [hEH] at h
    rw [h, abs_of_pos (by positivity), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (by positivity), Complex.ofReal_one, one_mul]
  -- Step 5: constants.
  have hP : ((Real.pi : ℂ) / -(-((δ ^ 2 : ℝ) : ℂ))) ^ (1 / 2 : ℂ) =
      ((Real.sqrt Real.pi / δ : ℝ) : ℂ) := by
    rw [neg_neg, ← Complex.ofReal_div, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_div' _ hc.le,
      Real.sqrt_sq hδ.le]
  rw [step2]
  simp_rw [step3]
  rw [integral_const_mul, hP]
  change _ * (_ * ∫ s, E s) = _
  rw [hsub]
  have hpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hreal : (1 / (2 * Real.pi)) * (Real.sqrt Real.pi / δ) * (2 * δ) = 1 / Real.sqrt Real.pi := by
    field_simp
    nlinarith [hpi]
  rw [← mul_assoc, ← mul_assoc, show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by
    push_cast; rfl, ← Complex.ofReal_mul, ← Complex.ofReal_mul, hreal]

private lemma norm_H_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (ξ v : ℝ) :
    ‖H δ ξ v‖ ≤ Real.exp (7 / 12) * Real.exp (-1 * v ^ 2) := by
  have hre : (Tt δ ξ v ^ 3 / 3 + ((δ ^ 2 / 4 - v ^ 2 : ℝ) : ℂ) + ((δ * v : ℝ) : ℂ) * I).re
      = ((δ ^ 2) ^ 3 - 3 * δ ^ 2 * (-2 * Real.pi * ξ + 2 * δ * v) ^ 2) / 3
        + (δ ^ 2 / 4 - v ^ 2) := by
    rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re, Tt, re_cube]
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [H, Complex.norm_exp, hre, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h2 : δ ^ 2 ≤ 1 := by nlinarith
  have h6 : (δ ^ 2) ^ 3 ≤ 1 := pow_le_one₀ (by positivity) h2
  have h3 : 0 ≤ δ ^ 2 * (-2 * Real.pi * ξ + 2 * δ * v) ^ 2 := by positivity
  nlinarith

private lemma H_zero (ξ v : ℝ) : H 0 ξ v = airySymbol ξ * ((Real.exp (-1 * v ^ 2) : ℝ) : ℂ) := by
  rw [H, Tt, airySymbol, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (-(2 * (Real.pi : ℂ) * ξ) ^ 3 / 3) * Complex.I_pow_three

private lemma continuous_H' (δ ξ : ℝ) : Continuous (H δ ξ) := by
  unfold H Tt; fun_prop

private lemma continuous_H (ξ v : ℝ) : Continuous (fun δ : ℝ => H δ ξ v) := by
  unfold H Tt; fun_prop

private lemma integral_H_zero (ξ : ℝ) :
    ∫ v : ℝ, H 0 ξ v = airySymbol ξ * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  simp_rw [H_zero]
  rw [integral_const_mul, integral_complex_ofReal, integral_gaussian, div_one]

/-- The regularisation sequence `δₙ = 1/(n+1)`. -/
private def δs (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private lemma δs_pos (n : ℕ) : 0 < δs n := by unfold δs; positivity

private lemma δs_le_one (n : ℕ) : δs n ≤ 1 := by
  unfold δs
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  linarith

private lemma tendsto_δs : Tendsto δs atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

private lemma sqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos

private lemma norm_fourier_gw_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : ℝ) :
    ‖𝓕 (gw δ) ξ‖ ≤ Real.exp (7 / 12) := by
  have hb : Integrable (fun v : ℝ => Real.exp (7 / 12) * Real.exp (-1 * v ^ 2)) :=
    (integrable_exp_neg_mul_sq one_pos).const_mul _
  rw [fourier_gw hδ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by have := sqrt_pi_pos; positivity)]
  calc 1 / Real.sqrt Real.pi * ‖∫ v : ℝ, H δ ξ v‖
      ≤ 1 / Real.sqrt Real.pi * ∫ v : ℝ, Real.exp (7 / 12) * Real.exp (-1 * v ^ 2) := by
        gcongr
        exact norm_integral_le_of_norm_le hb
          (Eventually.of_forall fun v => norm_H_le hδ.le hδ1 ξ v)
    _ = Real.exp (7 / 12) := by
        rw [integral_const_mul, integral_gaussian, div_one]
        field_simp [sqrt_pi_pos.ne']

private lemma tendsto_fourier_gw (ξ : ℝ) :
    Tendsto (fun n => 𝓕 (gw (δs n)) ξ) atTop (𝓝 (airySymbol ξ)) := by
  have hb : Integrable (fun v : ℝ => Real.exp (7 / 12) * Real.exp (-1 * v ^ 2)) :=
    (integrable_exp_neg_mul_sq one_pos).const_mul _
  have hlim : Tendsto (fun n => ∫ v : ℝ, H (δs n) ξ v) atTop (𝓝 (∫ v : ℝ, H 0 ξ v)) := by
    refine tendsto_integral_of_dominated_convergence _
      (fun n => (continuous_H' (δs n) ξ).aestronglyMeasurable) hb
      (fun n => Eventually.of_forall fun v => norm_H_le (δs_pos n).le (δs_le_one n) ξ v)
      (Eventually.of_forall fun v => ((continuous_H ξ v).tendsto 0).comp tendsto_δs)
  have := hlim.const_mul ((1 / Real.sqrt Real.pi : ℝ) : ℂ)
  rw [integral_H_zero] at this
  convert this using 1
  · funext n; exact fourier_gw (δs_pos n) ξ
  · push_cast
    field_simp [Complex.ofReal_ne_zero.mpr sqrt_pi_pos.ne']

private lemma continuous_fourier_gw {δ : ℝ} (hδ : 0 < δ) : Continuous (𝓕 (gw δ)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
    (integrable_gw hδ)

/-- Self-adjointness of `𝓕` against the regularised Airy function. -/
private lemma integral_fourier_gw_mul {δ : ℝ} (hδ : 0 < δ) {φ : ℝ → ℂ} (hφ : Integrable φ) :
    ∫ ξ, 𝓕 (gw δ) ξ * φ ξ = ∫ x, gw δ x * 𝓕 φ x := by
  simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner (integrable_gw hδ) hφ)

/-- **The Fourier transform of `Ai` (weak form).** With Mathlib's `𝓕` (kernel `e^{-2πixξ}`),
for every integrable `φ` with integrable `𝓕 φ`:
`∫ Ai(x) 𝓕φ(x) dx = ∫ exp(i(2πξ)³/3) φ(ξ) dξ`. -/
theorem integral_airyAi_mul_fourier {φ : ℝ → ℂ} (hφ : Integrable φ) (hFφ : Integrable (𝓕 φ)) :
    ∫ x, (airyAiReal x : ℂ) * 𝓕 φ x = ∫ ξ, airySymbol ξ * φ ξ := by
  obtain ⟨C, hC⟩ := airyAiReal_bdd
  have h1 : Tendsto (fun n => ∫ x, gw (δs n) x * 𝓕 φ x) atTop
      (𝓝 (∫ x, (airyAiReal x : ℂ) * 𝓕 φ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => C * ‖𝓕 φ x‖)
      (fun n => ((continuous_gw.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul hFφ.1))
      (hFφ.norm.const_mul C)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · have hA : ‖(airyAiReal x : ℂ)‖ ≤ C := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact hC x
      have hE : ‖cexp (-((δs n ^ 2 : ℝ) : ℂ) * (x : ℂ) ^ 2)‖ ≤ 1 := by
        rw [show -((δs n ^ 2 : ℝ) : ℂ) * (x : ℂ) ^ 2 = ((-(δs n ^ 2 * x ^ 2) : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_exp_ofReal, Real.exp_le_one_iff]
        have : 0 ≤ δs n ^ 2 * x ^ 2 := by positivity
        linarith
      have hC0 : 0 ≤ C := (norm_nonneg _).trans hA
      rw [gw, norm_mul, norm_mul]
      calc ‖(airyAiReal x : ℂ)‖ * ‖cexp (-((δs n ^ 2 : ℝ) : ℂ) * (x : ℂ) ^ 2)‖ * ‖𝓕 φ x‖
          ≤ C * 1 * ‖𝓕 φ x‖ := by gcongr
        _ = C * ‖𝓕 φ x‖ := by ring
    · have hg : Tendsto (fun n => gw (δs n) x) atTop (𝓝 (gw 0 x)) :=
        ((continuous_gw.comp (continuous_id.prodMk continuous_const)).tendsto 0).comp tendsto_δs
      have h0 : gw 0 x = (airyAiReal x : ℂ) := by simp [gw]
      rw [h0] at hg
      exact hg.mul_const _
  have h2 : Tendsto (fun n => ∫ ξ, 𝓕 (gw (δs n)) ξ * φ ξ) atTop
      (𝓝 (∫ ξ, airySymbol ξ * φ ξ)) := by
    refine tendsto_integral_of_dominated_convergence (fun ξ => Real.exp (7 / 12) * ‖φ ξ‖)
      (fun n => (continuous_fourier_gw (δs_pos n)).aestronglyMeasurable.mul hφ.1)
      (hφ.norm.const_mul _)
      (fun n => Eventually.of_forall fun ξ => ?_)
      (Eventually.of_forall fun ξ => (tendsto_fourier_gw ξ).mul_const _)
    rw [norm_mul]
    gcongr
    exact norm_fourier_gw_le (δs_pos n) (δs_le_one n) ξ
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  exact integral_fourier_gw_mul (δs_pos n) hφ

/-- Schwartz form: `⟨Ai, 𝓕φ⟩ = ⟨ψ, φ⟩` for every `φ ∈ 𝓢(ℝ, ℂ)`. -/
theorem integral_airyAi_mul_fourier_schwartz (φ : 𝓢(ℝ, ℂ)) :
    ∫ x, (airyAiReal x : ℂ) * (𝓕 φ) x = ∫ ξ, airySymbol ξ * φ ξ := by
  have h := (𝓕 φ).integrable (μ := volume)
  rw [SchwartzMap.fourier_coe] at h ⊢
  exact integral_airyAi_mul_fourier φ.integrable h

/-! ## Tempered-distribution form -/

/-- `Ai ∈ L^∞(ℝ)`. -/
lemma memLp_top_airyAiReal : MemLp (fun x : ℝ => (airyAiReal x : ℂ)) ⊤ := by
  obtain ⟨C, hC⟩ := airyAiReal_bdd
  exact memLp_top_of_bound
    (Complex.continuous_ofReal.comp continuous_airyAiReal).aestronglyMeasurable
    C (Eventually.of_forall fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hC x)

/-- `ψ ∈ L^∞(ℝ)`. -/
lemma memLp_top_airySymbol : MemLp airySymbol ⊤ :=
  memLp_top_of_bound continuous_airySymbol.aestronglyMeasurable 1
    (Eventually.of_forall fun ξ => (norm_airySymbol ξ).le)

/-- `Ai` as a tempered distribution (via `L^∞`). -/
def airyAiDist : 𝓢'(ℝ, ℂ) := Lp.toTemperedDistribution (memLp_top_airyAiReal.toLp _)

/-- The symbol `ψ(ξ) = exp(i(2πξ)³/3)` as a tempered distribution (via `L^∞`). -/
def airySymbolDist : 𝓢'(ℝ, ℂ) := Lp.toTemperedDistribution (memLp_top_airySymbol.toLp _)

/-- **`𝓕 Ai = exp(i(2π·)³/3)` in `𝓢'(ℝ, ℂ)`** (Mathlib's `𝓕` on tempered distributions). -/
theorem fourier_airyAiDist : 𝓕 airyAiDist = airySymbolDist := by
  ext g
  rw [TemperedDistribution.fourier_apply]
  simp only [airyAiDist, airySymbolDist, Lp.toTemperedDistribution_apply]
  have h1 : ∫ x, (𝓕 g) x • (memLp_top_airyAiReal.toLp _ : Lp ℂ ⊤ (volume : Measure ℝ)) x
      = ∫ x, (airyAiReal x : ℂ) * (𝓕 g) x := by
    refine integral_congr_ae ?_
    filter_upwards [memLp_top_airyAiReal.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul, mul_comm]
  have h2 : ∫ ξ, g ξ • (memLp_top_airySymbol.toLp _ : Lp ℂ ⊤ (volume : Measure ℝ)) ξ
      = ∫ ξ, airySymbol ξ * g ξ := by
    refine integral_congr_ae ?_
    filter_upwards [memLp_top_airySymbol.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul, mul_comm]
  rw [h1, h2, integral_airyAi_mul_fourier_schwartz]

/-- The symbol has temperate growth (so `fourierMultiplierCLM ℂ airySymbol` is available). -/
theorem hasTemperateGrowth_airySymbol : airySymbol.HasTemperateGrowth := by
  have h : airySymbol = (fun x : ℝ ↦ Complex.exp (x * Complex.I)) ∘
      (fun ξ : ℝ => (1 / 3 : ℝ) * (2 * Real.pi * ξ) ^ 3) := by
    funext ξ; simp only [airySymbol, Function.comp_apply]; push_cast; ring_nf
  rw [h]
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

end AiryFourier

end
