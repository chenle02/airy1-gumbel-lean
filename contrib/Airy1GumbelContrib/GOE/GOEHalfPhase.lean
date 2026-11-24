/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryTransform
import Airy1GumbelContrib.GOE.GOEHermite
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Hermite packets for the Airy involution

The positive cubic half phase conjugates frequency reflection to the full
Airy symbol times reflection. The half-phase Hermite packets can be shifted
to a lower horizontal contour inside their Gaussian strip.
-/

namespace GOELocalization

open Complex MeasureTheory Set Filter SchwartzMap
open scoped ENNReal FourierTransform SchwartzMap Topology ContDiff ComplexConjugate

/-- Real Lebesgue L² on the line. -/
noncomputable abbrev GOERealL2 := MeasureTheory.Lp ℝ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)

/-- Complex Lebesgue L² on the line. -/
noncomputable abbrev GOEComplexL2 := MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)

/-- Half of the cubic phase of the Airy Fourier symbol. -/
noncomputable def halfPhase (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * z) ^ 3 / 6)

/-- A real linear combination of the first `N` even scaled Hermite functions. -/
noncomputable def hermiteEvenSum {N : ℕ}
    (ℓ : ℝ) (c : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ j : Fin N, (c j : ℂ) * hermiteScaled ℓ (2 * (j : ℕ)) z

/-- The inverse Fourier integral of the Hermite combination with the cubic half phase. -/
noncomputable def halfAiryPacket {N : ℕ}
    (ℓ : ℝ) (c : Fin N → ℝ) (x : ℝ) : ℂ :=
  ∫ ν : ℝ, Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * ν) * x) * halfPhase (ν : ℂ) *
    hermiteEvenSum ℓ c (ν : ℂ)

/-- Reflection of the real line preserves Lebesgue measure. -/
theorem goeMeasurePreserving_neg : MeasurePreserving (fun t : ℝ => -t) volume volume :=
  Measure.measurePreserving_neg volume

/-- Reflection `g ↦ g(−·)` on complex Lebesgue L² in the frequency coordinate. -/
noncomputable def goeFourierReflection : GOEComplexL2 ≃ₗᵢ[ℂ] GOEComplexL2 := by
  let R : GOEComplexL2 →ₗᵢ[ℂ] GOEComplexL2 :=
    Lp.compMeasurePreservingₗᵢ ℂ _ goeMeasurePreserving_neg
  have hR (g : GOEComplexL2) : R g =ᵐ[volume] fun t : ℝ => g (-t) :=
    Lp.coeFn_compMeasurePreserving g goeMeasurePreserving_neg
  have hh : Function.Involutive R := by
    intro g
    apply Lp.ext
    filter_upwards [hR (R g), (hR g).comp_tendsto goeMeasurePreserving_neg.quasiMeasurePreserving.tendsto_ae] with t h₁ h₂
    simpa using h₁.trans h₂
  exact { R.toLinearMap with
    invFun := R
    left_inv := hh
    right_inv := hh
    norm_map' := R.norm_map }

/-- Pointwise formula for frequency reflection, almost everywhere. -/
theorem goeFourierReflection_apply_ae (g : GOEComplexL2) :
    (goeFourierReflection g : ℝ → ℂ) =ᵐ[volume] fun t => g (-t) :=
  Lp.coeFn_compMeasurePreserving g goeMeasurePreserving_neg

/-- A measurable scalar of unit modulus preserves membership in complex L². -/
theorem memLp_unitMul (u : ℝ → ℂ) (hu : Measurable u) (hn : ∀ t, ‖u t‖ = 1)
    (g : GOEComplexL2) : MemLp (fun t => u t * g t) 2 volume := by
  refine (Lp.memLp g).of_le (hu.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)) ?_
  exact ae_of_all _ fun t => by simp [hn t]

/-- The L² operator given by multiplication by a measurable scalar of unit modulus. -/
noncomputable def unitMulLp (u : ℝ → ℂ) (hu : Measurable u) (hn : ∀ t, ‖u t‖ = 1)
    (g : GOEComplexL2) : GOEComplexL2 :=
  (memLp_unitMul u hu hn g).toLp _

/-- Pointwise formula for the L² multiplication operator, almost everywhere. -/
theorem unitMulLp_apply_ae (u : ℝ → ℂ) (hu : Measurable u) (hn : ∀ t, ‖u t‖ = 1)
    (g : GOEComplexL2) : (unitMulLp u hu hn g : ℝ → ℂ) =ᵐ[volume] fun t => u t * g t :=
  (memLp_unitMul u hu hn g).coeFn_toLp

/-- Multiplication by a measurable unimodular scalar as a complex linear isometry equivalence. -/
noncomputable def unitMulLpEquiv (u : ℝ → ℂ) (hu : Measurable u)
    (hn : ∀ t, ‖u t‖ = 1) : GOEComplexL2 ≃ₗᵢ[ℂ] GOEComplexL2 := by
  let v : ℝ → ℂ := fun t => conj (u t)
  have hv : Measurable v := Complex.continuous_conj.measurable.comp hu
  have hvn (t : ℝ) : ‖v t‖ = 1 := by simp [v, hn]
  let U := unitMulLp u hu hn
  let V := unitMulLp v hv hvn
  have hU (g : GOEComplexL2) : (U g : ℝ → ℂ) =ᵐ[volume] fun t => u t * g t :=
    unitMulLp_apply_ae u hu hn g
  have hV (g : GOEComplexL2) : (V g : ℝ → ℂ) =ᵐ[volume] fun t => v t * g t :=
    unitMulLp_apply_ae v hv hvn g
  have h (t : ℝ) : v t * u t = 1 := by simp [v, Complex.conj_mul', hn]
  refine
    { toFun := U
      invFun := V
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_
      norm_map' := ?_ }
  · intro g k
    apply Lp.ext
    filter_upwards [hU (g + k), hU g, hU k, Lp.coeFn_add g k, Lp.coeFn_add (U g) (U k)]
      with t hgk hg hk ha hb
    simp only [Pi.add_apply] at ha hb
    rw [hgk, ha, hb, hg, hk, mul_add]
  · intro r g
    apply Lp.ext
    filter_upwards [hU (r • g), hU g, Lp.coeFn_smul r g, Lp.coeFn_smul r (U g)]
      with t hrg hg ha hb
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply, smul_eq_mul] at ha hb
    rw [hrg, ha, hb, hg]
    ring
  · intro g
    apply Lp.ext
    filter_upwards [hV (U g), hU g] with t h₁ h₂
    rw [h₁, h₂, ← mul_assoc, h, one_mul]
  · intro g
    apply Lp.ext
    filter_upwards [hU (V g), hV g] with t h₁ h₂
    rw [h₁, h₂, ← mul_assoc, mul_comm (u t), h, one_mul]
  · intro g
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable (U g)) (Lp.aestronglyMeasurable g) ?_
    filter_upwards [hU g] with t ht
    simp [ht, hn]

/-- Pointwise formula for a unimodular multiplication equivalence. -/
theorem unitMulLpEquiv_apply_ae (u : ℝ → ℂ) (hu : Measurable u) (hn : ∀ t, ‖u t‖ = 1)
    (g : GOEComplexL2) : (unitMulLpEquiv u hu hn g : ℝ → ℂ) =ᵐ[volume] fun t => u t * g t :=
  unitMulLp_apply_ae u hu hn g

/-- The inverse multiplier is multiplication by the conjugate phase. -/
theorem unitMulLpEquiv_symm_apply_ae (u : ℝ → ℂ) (hu : Measurable u) (hn : ∀ t, ‖u t‖ = 1)
    (g : GOEComplexL2) :
    ((unitMulLpEquiv u hu hn).symm g : ℝ → ℂ) =ᵐ[volume] fun t => conj (u t) * g t :=
  unitMulLp_apply_ae (fun t => conj (u t)) (Complex.continuous_conj.measurable.comp hu)
    (fun t => by simp [hn]) g

/-- The half phase is unimodular on the real axis. -/
theorem norm_halfPhase_real (t : ℝ) : ‖halfPhase (t : ℂ)‖ = 1 := by
  unfold halfPhase
  convert Complex.norm_exp_ofReal_mul_I ((2 * Real.pi * t) ^ 3 / 6) using 3
  push_cast
  ring

/-- The half phase is continuous on the complex plane. -/
theorem continuous_halfPhase : Continuous halfPhase := by
  unfold halfPhase
  fun_prop

/-- Multiplication by the cubic half phase on complex frequency L². -/
noncomputable def goeFrequencyHalfPhase : GOEComplexL2 ≃ₗᵢ[ℂ] GOEComplexL2 :=
  unitMulLpEquiv (fun t => halfPhase (t : ℂ))
    (continuous_halfPhase.comp Complex.continuous_ofReal).measurable norm_halfPhase_real

/-- On frequency L², the full Airy symbol multiplies the reflected function. -/
noncomputable def goeAiryFrequency : GOEComplexL2 ≃ₗᵢ[ℂ] GOEComplexL2 :=
  goeFourierReflection.trans
    (unitMulLpEquiv AiryFourier.airySymbol AiryFourier.continuous_airySymbol.measurable
      AiryFourier.norm_airySymbol)

/-- Fourier conjugation of `(Wg)(ν) = exp(i(2πν)³/3) g(−ν)` on complex L². -/
noncomputable def goeAiryInvolution : GOEComplexL2 ≃ₗᵢ[ℂ] GOEComplexL2 :=
  ((Lp.fourierTransformₗᵢ ℝ ℂ).trans goeAiryFrequency).trans (Lp.fourierTransformₗᵢ ℝ ℂ).symm

/-- Reflecting the real frequency conjugates the cubic half phase. -/
theorem conj_halfPhase_neg (t : ℝ) : conj (halfPhase ((-t : ℝ) : ℂ)) = halfPhase (t : ℂ) := by
  simp only [halfPhase, ← Complex.exp_conj, map_div₀, map_mul, map_pow, map_ofNat,
    Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg, map_neg]
  congr 1
  ring

/-- The two half phases combine to give the Airy Fourier symbol. -/
theorem halfPhase_mul_self (t : ℝ) :
    halfPhase (t : ℂ) * halfPhase (t : ℂ) = AiryFourier.airySymbol t := by
  rw [halfPhase, ← Complex.exp_add, AiryFourier.airySymbol]
  congr 1
  ring

/-- The full Airy frequency operator acts by reflection followed by multiplication. -/
theorem goeAiryFrequency_apply_ae (g : GOEComplexL2) :
    (goeAiryFrequency g : ℝ → ℂ) =ᵐ[volume] fun t => AiryFourier.airySymbol t * g (-t) := by
  unfold goeAiryFrequency
  simp only [LinearIsometryEquiv.trans_apply]
  filter_upwards [unitMulLpEquiv_apply_ae _ _ _ (goeFourierReflection g),
    goeFourierReflection_apply_ae g] with t h₁ h₂
  rw [h₁, h₂]

/-- The half-phase multiplier conjugates frequency reflection to the full Airy operator. -/
theorem goeAiryInvolution_frequency :
    ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm.trans
      goeAiryInvolution).trans (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
      = (goeFrequencyHalfPhase.symm.trans goeFourierReflection).trans
          goeFrequencyHalfPhase := by
  ext1 g
  simp only [LinearIsometryEquiv.trans_apply, goeAiryInvolution,
    LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  let v := goeFrequencyHalfPhase.symm g
  let w := goeFourierReflection v
  change (goeAiryFrequency g : ℝ → ℂ) =ᵐ[volume] (goeFrequencyHalfPhase w : ℝ → ℂ)
  have hv : (v : ℝ → ℂ) =ᵐ[volume] fun t => conj (halfPhase (t : ℂ)) * g t :=
    unitMulLpEquiv_symm_apply_ae _ _ _ g
  have hw : (goeFrequencyHalfPhase w : ℝ → ℂ) =ᵐ[volume] fun t => halfPhase (t : ℂ) * w t :=
    unitMulLpEquiv_apply_ae _ _ _ w
  filter_upwards [goeAiryFrequency_apply_ae g, hw, goeFourierReflection_apply_ae v,
    hv.comp_tendsto goeMeasurePreserving_neg.quasiMeasurePreserving.tendsto_ae] with t h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃]
  change v (-t) = conj (halfPhase ((-t : ℝ) : ℂ)) * g (-t) at h₄
  rw [h₄, conj_halfPhase_neg, ← mul_assoc, halfPhase_mul_self]

/-- The lower contour at angular-frequency height `b`, in Mathlib's frequency coordinate. -/
noncomputable def lowerFrequency (t b : ℝ) : ℂ :=
  (t : ℂ) - Complex.I * (b / (2 * Real.pi))

/-- The Hermite combination with its common Gaussian factor removed. -/
noncomputable def hermitePacketPoly {N : ℕ} (ℓ : ℝ) (c : Fin N → ℝ) (z : ℂ) : ℂ :=
  ((Real.sqrt (2 * Real.pi * ℓ) / Real.sqrt (Real.sqrt (2 * Real.pi)) : ℝ) : ℂ) *
    ∑ j : Fin N, (c j : ℂ) * hermiteNormalizedPoly (2 * (j : ℕ)) ((2 * (Real.pi : ℂ) * ℓ) * z)

/-- The combined cubic half phase and common Hermite Gaussian exponent. -/
noncomputable def hermitePacketExponent (ℓ : ℝ) (z : ℂ) : ℂ :=
  Complex.I * (2 * (Real.pi : ℂ) * z) ^ 3 / 6 - ((2 * (Real.pi : ℂ) * ℓ) * z) ^ 2 / 4

/-- The half-phase Hermite profile factors into an exponential and a polynomial. -/
theorem halfPhase_mul_hermiteEvenSum {N : ℕ} (ℓ : ℝ) (c : Fin N → ℝ) (z : ℂ) :
    halfPhase z * hermiteEvenSum ℓ c z =
      Complex.exp (hermitePacketExponent ℓ z) * hermitePacketPoly ℓ c z := by
  unfold hermiteEvenSum hermitePacketPoly
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hermiteScaled, hermiteEntire, hermitePacketExponent, sub_eq_add_neg, Complex.exp_add,
    halfPhase, Complex.ofReal_div]
  ring

/-- Changing the lower contour from the Fourier coordinate to angular frequency. -/
theorem twoPi_mul_lowerFrequency (t b : ℝ) :
    (2 * (Real.pi : ℂ)) * lowerFrequency t b =
      (↑(2 * Real.pi * t) : ℂ) - Complex.I * (b : ℂ) := by
  have hp : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  unfold lowerFrequency
  push_cast
  field_simp

/-- The exponent on a lower contour separates into a Gaussian and a real phase polynomial. -/
theorem hermitePacketExponent_lower (ℓ t b : ℝ) :
    hermitePacketExponent ℓ (lowerFrequency t b) =
      (((b / 2 - ℓ ^ 2 / 4) * (2 * Real.pi * t) ^ 2 + ℓ ^ 2 * b ^ 2 / 4 - b ^ 3 / 6 : ℝ) : ℂ) +
      Complex.I * (((2 * Real.pi * t) ^ 3 / 6 +
        (ℓ ^ 2 * b / 2 - b ^ 2 / 2) * (2 * Real.pi * t) : ℝ) : ℂ) := by
  unfold hermitePacketExponent
  rw [show (2 * (Real.pi : ℂ) * ℓ) * lowerFrequency t b =
    (ℓ : ℂ) * ((2 * (Real.pi : ℂ)) * lowerFrequency t b) by ring, twoPi_mul_lowerFrequency]
  push_cast
  suffices ∀ u l v : ℂ,
      Complex.I * (u - Complex.I * v) ^ 3 / 6 - (l * (u - Complex.I * v)) ^ 2 / 4 =
        (v / 2 - l ^ 2 / 4) * u ^ 2 + l ^ 2 * v ^ 2 / 4 - v ^ 3 / 6 +
          Complex.I * (u ^ 3 / 6 + (l ^ 2 * v / 2 - v ^ 2 / 2) * u) by
    exact this _ _ _
  intro u l v
  have hs : (u - Complex.I * v) ^ 2 = u ^ 2 - 2 * Complex.I * v * u - v ^ 2 := by
    simp only [sub_sq, mul_pow, Complex.I_sq]
    ring
  have hc : (u - Complex.I * v) ^ 3 =
      u ^ 3 - 3 * Complex.I * v * u ^ 2 - 3 * v ^ 2 * u + Complex.I * v ^ 3 := by
    rw [pow_succ, hs]
    linear_combination 2 * v ^ 2 * u * Complex.I_sq
  rw [hc, mul_pow, hs]
  linear_combination (v ^ 3 / 6 - v * u ^ 2 / 2) * Complex.I_sq

/-- A shifted frequency profile is a finite Hermite sum with the half phase attached. -/
noncomputable def halfAiryFrequencyProfile {N : ℕ} (ℓ : ℝ) (c : Fin N → ℝ) (b t : ℝ) : ℂ :=
  halfPhase (lowerFrequency t b) * hermiteEvenSum ℓ c (lowerFrequency t b)

/-- The lower shift is the real height cast to the complex line. -/
theorem lowerFrequency_eq_real_height (t b : ℝ) :
    lowerFrequency t b = (t : ℂ) - Complex.I * ((b / (2 * Real.pi) : ℝ) : ℂ) := by
  unfold lowerFrequency
  push_cast
  rfl

/-- At height zero the lower contour is the real line. -/
theorem lowerFrequency_zero (t : ℝ) : lowerFrequency t 0 = (t : ℂ) := by
  simp [lowerFrequency_eq_real_height]

/-- The inverse Fourier exponential on the lower contour picks up a real factor. -/
theorem lowerFrequency_fourierExponential (t b x : ℝ) :
    Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * lowerFrequency t b) * x) =
      (Real.exp (b * x) : ℂ) * Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * t) * x) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add, twoPi_mul_lowerFrequency]
  congr 1
  push_cast
  linear_combination -((b : ℂ) * x) * Complex.I_sq

/-- Any polynomial times the Hermite Gaussian decays after multiplication by a power of the norm. -/
theorem tendsto_aeval_mul_hermiteGaussianWeight (p : Polynomial ℤ) (k : ℕ) :
    Tendsto (fun x : ℝ => ‖x‖ ^ k * Polynomial.aeval x p * hermiteGaussianWeight x)
      (cocompact ℝ) (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, mul_add, add_mul, add_zero] using hp.add hq
  | monomial n a =>
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 1 / 2)
      (by norm_num) ((k + n : ℕ) : ℝ)
    rw [show (fun x : ℝ => |x| ^ ((k + n : ℕ) : ℝ) * Real.exp (-(1 / 2) * x ^ 2)) =
        (fun x : ℝ => |x| ^ (k + n) * hermiteGaussianWeight x) by
      ext x
      rw [Real.rpow_natCast, hermiteGaussianWeight]
      congr 2
      ring] at h
    have h' := h.const_mul ‖(a : ℝ)‖
    convert h' using 1
    · ext x
      simp only [Polynomial.aeval_monomial, eq_intCast, norm_mul, norm_pow,
        Real.norm_eq_abs x, Real.norm_of_nonneg (abs_nonneg x), pow_add, hermiteGaussianWeight, Real.norm_of_nonneg (Real.exp_pos _).le]
      ring
    · rw [mul_zero]

/-- The real Hermite Gaussian, as a Schwartz function. -/
noncomputable def hermiteGaussianSchwartz : 𝓢(ℝ, ℝ) where
  toFun := hermiteGaussianWeight
  smooth' := by unfold hermiteGaussianWeight; fun_prop
  decay' k n := by
    let f : ℝ → ℝ := fun x => ‖x‖ ^ k * Polynomial.aeval x (Polynomial.hermite n) *
      hermiteGaussianWeight x
    have h : Tendsto f (cocompact ℝ) (𝓝 0) :=
      tendsto_aeval_mul_hermiteGaussianWeight _ _
    have hc : Continuous f := by
      dsimp [f, hermiteGaussianWeight]
      have hp : Continuous fun x : ℝ => Polynomial.aeval x (Polynomial.hermite n) :=
        (Polynomial.hermite n).differentiable_aeval.continuous
      fun_prop
    have hb := hc.isBounded_range_iff_isBigO.mpr ((Asymptotics.isLittleO_one_iff ℝ).2 h).isBigO
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
    refine ⟨C, fun x => ?_⟩
    have hx := hC (f x) (mem_range_self x)
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, deriv_gaussian_formula]
    change ‖‖x‖ ^ k * Polynomial.aeval x (Polynomial.hermite n) * hermiteGaussianWeight x‖ ≤ C at hx
    simpa only [norm_mul, norm_pow, norm_norm, norm_neg, norm_one, one_pow, one_mul, mul_assoc]
      using hx

/-- The Gaussian `t ↦ exp(-q*t²)` as a complex Schwartz function for `q > 0`. -/
noncomputable def goeGaussianSchwartz (q : ℝ) (hq : 0 < q) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (Units.mk0 (Real.sqrt (2 * q)) (ne_of_gt (Real.sqrt_pos.2 (by positivity))) •
        ContinuousLinearEquiv.refl ℝ ℝ) hermiteGaussianSchwartz)

/-- Pointwise formula for the complex Schwartz Gaussian. -/
theorem goeGaussianSchwartz_apply (q : ℝ) (hq : 0 < q) (t : ℝ) :
    goeGaussianSchwartz q hq t = (Real.exp (-q * t ^ 2) : ℂ) := by
  change (Real.exp (-((Real.sqrt (2 * q) * t) ^ 2 / 2)) : ℂ) = _
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * q)]
  congr 2
  ring

/-- Evaluation of a normalized Hermite polynomial on a complex affine line has temperate growth. -/
theorem hasTemperateGrowth_hermiteNormalizedPoly_affine (m : ℕ) (u v : ℂ) :
    (fun t : ℝ => hermiteNormalizedPoly m (u * (t : ℂ) + v)).HasTemperateGrowth := by
  simp only [hermiteNormalizedPoly, Polynomial.aeval_eq_sum_range, zsmul_eq_mul, div_eq_mul_inv]
  apply Function.HasTemperateGrowth.mul _ (Function.HasTemperateGrowth.const _)
  apply Function.HasTemperateGrowth.sum
  intro j _
  fun_prop

/-- The polynomial factor of a shifted Hermite profile has temperate growth. -/
theorem hasTemperateGrowth_hermitePacketPoly_lower {N : ℕ} (ℓ : ℝ) (c : Fin N → ℝ) (b : ℝ) :
    (fun t : ℝ => hermitePacketPoly ℓ c (lowerFrequency t b)).HasTemperateGrowth := by
  unfold hermitePacketPoly
  apply Function.HasTemperateGrowth.mul (Function.HasTemperateGrowth.const _)
  apply Function.HasTemperateGrowth.sum
  intro j _
  apply Function.HasTemperateGrowth.mul (Function.HasTemperateGrowth.const _)
  simp only [lowerFrequency, sub_eq_add_neg, mul_add]
  exact hasTemperateGrowth_hermiteNormalizedPoly_affine _ _ _

/-- The phase left over after extracting the Gaussian on a lower contour. -/
noncomputable def lowerHermitePhase (ℓ b t : ℝ) : ℝ :=
  (2 * Real.pi * t) ^ 3 / 6 + (ℓ ^ 2 * b / 2 - b ^ 2 / 2) * (2 * Real.pi * t)

/-- A lower frequency profile is Schwartz whenever the net Gaussian coefficient is positive. -/
noncomputable def halfAiryFrequencySchwartz {N : ℕ} (ℓ : ℝ) (c : Fin N → ℝ) (b : ℝ)
    (hb : b / 2 < ℓ ^ 2 / 4) : 𝓢(ℝ, ℂ) :=
  let q := (ℓ ^ 2 / 4 - b / 2) * (2 * Real.pi) ^ 2
  smulLeftCLM ℂ (fun t : ℝ =>
    (Real.exp (ℓ ^ 2 * b ^ 2 / 4 - b ^ 3 / 6) : ℂ) *
      Complex.exp ((lowerHermitePhase ℓ b t : ℂ) * Complex.I) *
      hermitePacketPoly ℓ c (lowerFrequency t b))
    (goeGaussianSchwartz q (mul_pos (sub_pos.mpr hb) (by positivity)))

/-- The Schwartz representation agrees pointwise with the shifted frequency profile. -/
theorem halfAiryFrequencySchwartz_apply {N : ℕ} (ℓ : ℝ) (c : Fin N → ℝ) (b : ℝ)
    (hb : b / 2 < ℓ ^ 2 / 4) (t : ℝ) :
    halfAiryFrequencySchwartz ℓ c b hb t = halfAiryFrequencyProfile ℓ c b t := by
  have hP : (lowerHermitePhase ℓ b).HasTemperateGrowth := by
    change (fun t : ℝ => (2 * Real.pi * t) ^ 3 / 6 +
      (ℓ ^ 2 * b / 2 - b ^ 2 / 2) * (2 * Real.pi * t)).HasTemperateGrowth
    simp only [div_eq_mul_inv]
    fun_prop
  have hphase : (fun t => Complex.exp ((lowerHermitePhase ℓ b t : ℂ) * Complex.I)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_exp_mul_I.comp hP
  have hc : (fun t : ℝ => (Real.exp (ℓ ^ 2 * b ^ 2 / 4 - b ^ 3 / 6) : ℂ) *
      Complex.exp ((lowerHermitePhase ℓ b t : ℂ) * Complex.I) *
        hermitePacketPoly ℓ c (lowerFrequency t b)).HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const _).mul hphase).mul
      (hasTemperateGrowth_hermitePacketPoly_lower ℓ c b)
  simp only [halfAiryFrequencySchwartz, smulLeftCLM_apply_apply hc,
    smul_eq_mul, goeGaussianSchwartz_apply, halfAiryFrequencyProfile, halfPhase_mul_hermiteEvenSum,
    hermitePacketExponent_lower]
  unfold lowerHermitePhase
  rw [Complex.exp_add, ← Complex.ofReal_exp,
    show (b / 2 - ℓ ^ 2 / 4) * (2 * Real.pi * t) ^ 2 + ℓ ^ 2 * b ^ 2 / 4 - b ^ 3 / 6 =
      (ℓ ^ 2 * b ^ 2 / 4 - b ^ 3 / 6) + (-( (ℓ ^ 2 / 4 - b / 2) * (2 * Real.pi) ^ 2) * t ^ 2) by ring,
    Real.exp_add, Complex.ofReal_mul,
    mul_comm Complex.I]
  ring

/-- The entire integrand of the inverse Fourier integral for a Hermite packet. -/
noncomputable def packetContourIntegrand {N : ℕ} (ℓ : ℝ) (c : Fin N → ℝ) (x : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * z) * x) *
    halfPhase z * hermiteEvenSum ℓ c z

/-- The packet integrand is entire. -/
theorem differentiable_packetContourIntegrand {N : ℕ} (ℓ : ℝ) (c : Fin N → ℝ) (x : ℝ) :
    Differentiable ℂ (packetContourIntegrand ℓ c x) := by
  have hp (k : ℕ) : Differentiable ℂ (fun z => Polynomial.aeval z (Polynomial.hermite k)) :=
    (Polynomial.hermite k).differentiable_aeval
  unfold packetContourIntegrand halfPhase hermiteEvenSum hermiteScaled hermiteEntire hermiteNormalizedPoly
  simp only [div_eq_mul_inv]
  fun_prop

/-- The Hermite argument is controlled by its real frequency and shift height. -/
theorem norm_hermite_argument_lower_le {ℓ b : ℝ} (hℓ : 0 ≤ ℓ) (hb : 0 ≤ b) (t : ℝ) :
    ‖(2 * (Real.pi : ℂ) * ℓ) * lowerFrequency t b‖ ≤
      ℓ * (2 * Real.pi * |t| + b) := by
  rw [show (2 * (Real.pi : ℂ) * ℓ) * lowerFrequency t b =
      (ℓ : ℂ) * ((2 * (Real.pi : ℂ)) * lowerFrequency t b) by ring, twoPi_mul_lowerFrequency,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hℓ]
  apply mul_le_mul_of_nonneg_left (le_trans (norm_sub_le _ _) ?_) hℓ
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg hb]

/-- Uniform Gaussian domination on a closed lower strip. -/
theorem exists_norm_packetContourIntegrand_le {N : ℕ} {ℓ a : ℝ} (hℓ : 0 < ℓ)
    (hastrip : a ≤ ℓ ^ 2 / 4) (c : Fin N → ℝ) (x : ℝ) :
    ∃ C q : ℝ, 0 ≤ C ∧ 0 < q ∧ ∀ (t b : ℝ), 0 ≤ b → b ≤ a →
      ‖packetContourIntegrand ℓ c x (lowerFrequency t b)‖ ≤ C * Real.exp (-q * t ^ 2) := by
  let q : ℝ := ℓ ^ 2 / 8 * (2 * Real.pi) ^ 2
  have hq : 0 < q := by dsimp [q]; positivity
  let K : ℝ := 2 * N
  let B : ℝ := 2 * Real.sqrt K * ℓ
  let D : ℝ := B * (2 * Real.pi)
  let A : ℝ := ‖Real.sqrt (2 * Real.pi * ℓ) / Real.sqrt (Real.sqrt (2 * Real.pi))‖ *
    ∑ j : Fin N, ‖c j‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A * Real.exp (K + B * a + ℓ ^ 2 * a ^ 2 / 4 + a * |x| + D ^ 2 / (2 * q)),
    q / 2, by positivity, by positivity, ?_⟩
  intro t b hb hba
  have hpoly : ‖hermitePacketPoly ℓ c (lowerFrequency t b)‖ ≤
      A * Real.exp (K + B * a + D * |t|) := by
    have hconst : 0 ≤ ‖Real.sqrt (2 * Real.pi * ℓ) / Real.sqrt (Real.sqrt (2 * Real.pi))‖ :=
      norm_nonneg (Real.sqrt (2 * Real.pi * ℓ) / Real.sqrt (Real.sqrt (2 * Real.pi)))
    dsimp only [A]
    rw [hermitePacketPoly, norm_mul, Complex.norm_real,
      mul_assoc ‖Real.sqrt (2 * Real.pi * ℓ) / Real.sqrt (Real.sqrt (2 * Real.pi))‖]
    apply mul_le_mul_of_nonneg_left _ hconst
    refine (norm_sum_le Finset.univ
      (fun j : Fin N => (c j : ℂ) * hermiteNormalizedPoly (2 * (j : ℕ))
        ((2 * (Real.pi : ℂ) * ℓ) * lowerFrequency t b))).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    have hk : ((2 * (j : ℕ) : ℕ) : ℝ) ≤ K := by
      dsimp [K]
      push_cast
      gcongr
      exact_mod_cast j.isLt.le
    rw [norm_mul, Complex.norm_real]
    apply mul_le_mul_of_nonneg_left ((norm_hermiteNormalizedPoly_le _ _).trans
      (Real.exp_le_exp.mpr ?_)) (norm_nonneg _)
    have harg := norm_hermite_argument_lower_le hℓ.le hb t
    calc
      _ ≤ K + 2 * Real.sqrt K * (ℓ * (2 * Real.pi * |t| + b)) := by
        gcongr
      _ = K + B * b + D * |t| := by dsimp [B, D]; ring
      _ ≤ _ := by gcongr
  have hphase : ‖Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * t) * x)‖ = 1 := by
    convert Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t * x) using 3
    push_cast
    ring
  have hbound : b * x + ((b / 2 - ℓ ^ 2 / 4) * (2 * Real.pi * t) ^ 2 +
      ℓ ^ 2 * b ^ 2 / 4 - b ^ 3 / 6) ≤
      -q * t ^ 2 + ℓ ^ 2 * a ^ 2 / 4 + a * |x| := by
    have h₁ : b * x ≤ a * |x| :=
      (mul_le_mul_of_nonneg_left (le_abs_self _) hb).trans
        (mul_le_mul_of_nonneg_right hba (abs_nonneg _))
    have h₂ : (b / 2 - ℓ ^ 2 / 4) * (2 * Real.pi * t) ^ 2 ≤ -q * t ^ 2 := by
      have hmargin : b / 2 - ℓ ^ 2 / 4 ≤ -(ℓ ^ 2 / 8) := by linarith
      convert mul_le_mul_of_nonneg_right hmargin (sq_nonneg (2 * Real.pi * t)) using 1
      dsimp [q]
      ring
    have h₃ : ℓ ^ 2 * b ^ 2 / 4 ≤ ℓ ^ 2 * a ^ 2 / 4 := by gcongr
    linarith [pow_nonneg hb 3]
  have habsorb : D * |t| ≤ q / 2 * t ^ 2 + D ^ 2 / (2 * q) := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * q by positivity)).mp
    rw [mul_add, mul_div_cancel₀ _ (by positivity : (2 * q) ≠ 0), ← sq_abs t]
    nlinarith [sq_nonneg (q * |t| - D)]
  unfold packetContourIntegrand
  rw [mul_assoc, halfPhase_mul_hermiteEvenSum, lowerFrequency_fourierExponential, norm_mul,
    norm_mul, norm_mul, hphase, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_exp, hermitePacketExponent_lower]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  calc
    _ ≤ Real.exp (b * x) * (Real.exp _ * (A * Real.exp (K + B * a + D * |t|))) := by gcongr
    _ = A * Real.exp (b * x + ((b / 2 - ℓ ^ 2 / 4) * (2 * Real.pi * t) ^ 2 +
      ℓ ^ 2 * b ^ 2 / 4 - b ^ 3 / 6) + (K + B * a + D * |t|)) := by
      conv_rhs =>
        rw [Real.exp_add, Real.exp_add (b * x)]
      ac_rfl
    _ ≤ _ := by
      rw [mul_assoc A, ← Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hA

/-- An entire integrand with uniform Gaussian domination can be shifted to the lower edge. -/
theorem integral_eq_integral_lower_of_gaussian_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s C q : ℝ} (hs : 0 ≤ s) (hq : 0 < q)
    (h : ∀ (t y : ℝ), 0 ≤ y → y ≤ s →
      ‖f ((t : ℂ) - Complex.I * (y : ℂ))‖ ≤ C * Real.exp (-q * t ^ 2)) :
    (∫ t : ℝ, f (t : ℂ)) = ∫ t : ℝ, f ((t : ℂ) - Complex.I * (s : ℂ)) := by
  have hGaussian : Integrable (fun t : ℝ => C * Real.exp (-q * t ^ 2)) :=
    (integrable_exp_neg_mul_sq hq).const_mul C
  have hInt (y : ℝ) (hy : 0 ≤ y) (hys : y ≤ s) :
      Integrable (fun t : ℝ => f ((t : ℂ) - Complex.I * (y : ℂ))) :=
    hGaussian.mono' (by have := hf.continuous; fun_prop) (ae_of_all _ fun t => h t y hy hys)
  have hInt₀ : Integrable (fun t : ℝ => f (t : ℂ)) := by simpa using hInt 0 le_rfl hs
  let V (t : ℝ) : ℂ := ∫ y : ℝ in 0..-s, f ((t : ℂ) + (y : ℂ) * Complex.I)
  have hV (t : ℝ) : ‖V t‖ ≤ (s * C) * Real.exp (-q * t ^ 2) := by
    unfold V
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C * Real.exp (-q * t ^ 2)) ?_).trans_eq ?_
    · intro y hy
      have hy' : y ∈ Icc (-s) 0 := by
        simpa only [uIcc_of_ge (neg_nonpos.mpr hs)] using uIoc_subset_uIcc hy
      rw [show (t : ℂ) + (y : ℂ) * Complex.I = (t : ℂ) - Complex.I * ((-y : ℝ) : ℂ) by
        push_cast
        ring]
      exact h t (-y) (neg_nonneg.mpr hy'.2) (neg_le.mp hy'.1)
    · rw [sub_zero, abs_neg, abs_of_nonneg hs]
      ring
  have hG : Tendsto (fun T : ℝ => Real.exp (-q * T ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg (neg_lt_zero.mpr hq))
  have hGs : Tendsto (fun T : ℝ => (s * C) * Real.exp (-q * T ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hG.const_mul (s * C)
  have hVR : Tendsto V atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) hV hGs
  have hVL : Tendsto (fun T => V (-T)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun T => by simpa using hV (-T))
      hGs
  let H (y T : ℝ) : ℂ := ∫ t : ℝ in -T..T, f ((t : ℂ) - Complex.I * (y : ℂ))
  have hrect (T : ℝ) :
      H 0 T - H s T + Complex.I * V T - Complex.I * V (-T) = 0 := by
    have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((-T : ℝ) : ℂ) ((T : ℂ) - Complex.I * (s : ℂ)) hf.differentiableOn
    simpa [H, V, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, smul_eq_mul,
      sub_eq_add_neg, mul_comm Complex.I] using hr
  have hH₀ : Tendsto (H 0) atTop (𝓝 (∫ t : ℝ, f (t : ℂ))) := by
    simpa [H] using intervalIntegral_tendsto_integral hInt₀ tendsto_neg_atTop_atBot tendsto_id
  have hHs : Tendsto (H s) atTop (𝓝 (∫ t : ℝ, f ((t : ℂ) - Complex.I * (s : ℂ)))) :=
    intervalIntegral_tendsto_integral (hInt s hs le_rfl) tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hH₀.sub hHs).add (hVR.const_mul Complex.I)).sub (hVL.const_mul Complex.I)
  have hz := tendsto_nhds_unique hlim
    (show Tendsto (fun T => H 0 T - H s T + Complex.I * V T - Complex.I * V (-T)) atTop (𝓝 0) by
      simp only [hrect]
      exact tendsto_const_nhds)
  simpa only [mul_zero, add_zero, sub_zero, sub_eq_zero] using hz

/-- The weighted packet is the inverse Fourier integral on the shifted frequency line. -/
theorem halfAiryPacket_shift {N : ℕ} {ℓ a : ℝ}
    (hℓ : 0 < ℓ) (ha : 0 ≤ a) (hastrip : a ≤ ℓ ^ 2 / 4)
    (c : Fin N → ℝ) (x : ℝ) :
    (Real.exp (-a * x) : ℂ) * halfAiryPacket ℓ c x =
      ∫ ν : ℝ,
        Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * ν) * x) *
          halfPhase ((ν : ℂ) - Complex.I * (a / (2 * Real.pi))) *
          hermiteEvenSum ℓ c ((ν : ℂ) - Complex.I * (a / (2 * Real.pi))) := by
  let s := a / (2 * Real.pi)
  have hp : 0 < 2 * Real.pi := by positivity
  obtain ⟨C, q, -, hq, h⟩ := exists_norm_packetContourIntegrand_le hℓ hastrip c x
  have hf := integral_eq_integral_lower_of_gaussian_bound
    (differentiable_packetContourIntegrand ℓ c x) (div_nonneg ha hp.le) hq
    (s := s) (by
      intro t y hy hys
      have hb : 0 ≤ y * (2 * Real.pi) := mul_nonneg hy hp.le
      have hba : y * (2 * Real.pi) ≤ a := (le_div_iff₀ hp).mp hys
      simpa only [lowerFrequency_eq_real_height, mul_div_cancel_right₀ _ hp.ne'] using h t _ hb hba)
  have heq : halfAiryPacket ℓ c x =
      (∫ t : ℝ, packetContourIntegrand ℓ c x (lowerFrequency t a)) := by
    simpa only [halfAiryPacket, packetContourIntegrand, lowerFrequency_eq_real_height, s] using hf
  rw [heq]
  simp_rw [packetContourIntegrand, lowerFrequency_fourierExponential,
    mul_assoc (Real.exp (a * x) : ℂ)]
  rw [integral_const_mul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  simp [neg_mul, lowerFrequency]

/-- The action of the full Airy frequency operator on a Schwartz representative. -/
theorem goeAiryFrequency_fourier_toLp (f : 𝓢(ℝ, ℂ)) :
    goeAiryFrequency ((𝓕 f).toLp 2 volume) =
      (smulLeftCLM ℂ AiryFourier.airySymbol (𝓕 (AiryTransform.reflectCLM f))).toLp 2 volume := by
  let g : 𝓢(ℝ, ℂ) := smulLeftCLM ℂ AiryFourier.airySymbol (𝓕 (AiryTransform.reflectCLM f))
  change goeAiryFrequency ((𝓕 f).toLp 2 volume) = g.toLp 2 volume
  apply Lp.ext
  filter_upwards [goeAiryFrequency_apply_ae ((𝓕 f).toLp 2 volume), g.coeFn_toLp 2 volume,
    ((𝓕 f).coeFn_toLp 2 volume).comp_tendsto
      goeMeasurePreserving_neg.quasiMeasurePreserving.tendsto_ae] with t h₁ h₂ h₃
  change ((𝓕 f).toLp 2 volume) (-t) = (𝓕 f) (-t) at h₃
  rw [h₁, h₂, h₃]
  have he : (𝓕 (AiryTransform.reflectCLM f)) t = (𝓕 f) (-t) := by
    exact Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ)) f t
  simp [g, smulLeftCLM_apply_apply AiryFourier.hasTemperateGrowth_airySymbol, smul_eq_mul, he]

/-- The Airy involution agrees with the Airy Schwartz transform in L². -/
theorem goeAiryInvolution_toLp (f : 𝓢(ℝ, ℂ)) :
    goeAiryInvolution (f.toLp 2 volume) = (AiryTransform.airyTransformCLM f).toLp 2 volume := by
  change 𝓕⁻ (goeAiryFrequency (𝓕 (f.toLp 2 volume))) = _
  rw [SchwartzMap.toLp_fourier_eq, goeAiryFrequency_fourier_toLp, SchwartzMap.toLp_fourierInv_eq,
    AiryTransform.airyTransformCLM, ContinuousLinearMap.comp_apply, fourierMultiplierCLM_apply]

/-- The Schwartz transform representing the Airy involution has the kernel `Ai(x+y)`. -/
theorem goeAiryInvolution_toLp_ae (f : 𝓢(ℝ, ℂ)) :
    (goeAiryInvolution (f.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y, (airyAiReal (x + y) : ℂ) * f y := by
  rw [goeAiryInvolution_toLp]
  exact ((AiryTransform.airyTransformCLM f).coeFn_toLp 2 volume).trans
    (ae_of_all _ (AiryTransform.airyTransformCLM_apply f))

/-- The inverse Fourier transform uses the positive exponential in the packet coordinate. -/
theorem goeFourierInv_apply (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕⁻ g) x = ∫ t : ℝ, Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * t) * x) * g t := by
  change ((𝓕⁻ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x = _
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  apply integral_congr_ae
  refine ae_of_all _ fun t => ?_
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  congr 2
  push_cast
  ring

/-- The packet obtained from the inverse transform of the real-axis profile. -/
noncomputable def halfAiryPacketSchwartz {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (c : Fin N → ℝ) :
    𝓢(ℝ, ℂ) :=
  𝓕⁻ (halfAiryFrequencySchwartz ℓ c 0 (by nlinarith [sq_pos_of_pos hℓ]))

/-- The packet is the pointwise inverse Fourier transform of its Schwartz frequency profile. -/
theorem halfAiryPacketSchwartz_apply {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (c : Fin N → ℝ) (x : ℝ) :
    halfAiryPacketSchwartz ℓ hℓ c x = halfAiryPacket ℓ c x := by
  unfold halfAiryPacketSchwartz
  simp only [goeFourierInv_apply, halfAiryFrequencySchwartz_apply, halfAiryFrequencyProfile,
    lowerFrequency_zero, halfAiryPacket, mul_assoc]

/-- The weighted packet agrees with the inverse Fourier transform of the shifted Schwartz profile. -/
theorem halfAiryPacket_shift_fourierInv {N : ℕ} {ℓ a : ℝ}
    (hℓ : 0 < ℓ) (ha : 0 ≤ a) (hastrip : a ≤ ℓ ^ 2 / 4)
    (c : Fin N → ℝ) (x : ℝ) :
    (Real.exp (-a * x) : ℂ) * halfAiryPacket ℓ c x =
      (𝓕⁻ (halfAiryFrequencySchwartz ℓ c a (by nlinarith [sq_pos_of_pos hℓ]))) x := by
  rw [halfAiryPacket_shift hℓ ha hastrip, goeFourierInv_apply]
  simp only [halfAiryFrequencySchwartz_apply, halfAiryFrequencyProfile, lowerFrequency, mul_assoc]

/-- L² and Schwartz inverse Fourier transforms agree, with Lebesgue measure on the line. -/
theorem goeFourierInv_toLp (g : 𝓢(ℝ, ℂ)) :
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm (g.toLp 2 volume) = (𝓕⁻ g).toLp 2 volume :=
  SchwartzMap.toLp_fourierInv_eq g

/-- The L² norm of a Schwartz representative is its integrated squared norm. -/
theorem norm_sq_schwartz_toLp (g : 𝓢(ℝ, ℂ)) :
    ‖g.toLp 2 volume‖ ^ 2 = ∫ t : ℝ, ‖g t‖ ^ 2 := by
  have hg : MemLp (g : ℝ → ℂ) 2 (volume : Measure ℝ) := g.memLp 2
  have h := MemLp.eLpNorm_eq_integral_rpow_norm (p := (2 : ℝ≥0∞))
    (by norm_num) ENNReal.ofNat_ne_top hg
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← one_div (2 : ℝ), ← Real.sqrt_eq_rpow] at h
  rw [SchwartzMap.norm_toLp, h, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (integral_nonneg fun t => sq_nonneg ‖g t‖)

/-- Inverse Plancherel in the squared-integral form used for shifted packets. -/
theorem goeIntegral_norm_sq_fourierInv (g : 𝓢(ℝ, ℂ)) :
    (∫ t : ℝ, ‖(𝓕⁻ g) t‖ ^ 2) = ∫ t : ℝ, ‖g t‖ ^ 2 :=
  AiryTransform.integral_norm_sq_fourierInv g

/-- Scaled Hermite functions are real on the real axis. -/
theorem conj_hermiteScaled_real (ℓ : ℝ) (j : ℕ) (t : ℝ) :
    conj (hermiteScaled ℓ j (t : ℂ)) = hermiteScaled ℓ j (t : ℂ) := by
  unfold hermiteScaled
  have he : (2 * (Real.pi : ℂ) * ℓ) * t = ((2 * Real.pi * ℓ * t : ℝ) : ℂ) := by push_cast; rfl
  rw [he, hermiteEntire_ofReal, map_mul, conj_ofReal, conj_ofReal]

/-- A real Hermite combination of even indices is even on the complex plane. -/
theorem hermiteEvenSum_neg {N : ℕ} (ℓ : ℝ) (c : Fin N → ℝ) (z : ℂ) :
    hermiteEvenSum ℓ c (-z) = hermiteEvenSum ℓ c z := by
  simp only [hermiteEvenSum, hermiteScaled_even]

/-- A real Hermite combination takes real values on the real axis. -/
theorem conj_hermiteEvenSum_real {N : ℕ} (ℓ : ℝ) (c : Fin N → ℝ) (t : ℝ) :
    conj (hermiteEvenSum ℓ c (t : ℂ)) = hermiteEvenSum ℓ c (t : ℂ) := by
  simp only [hermiteEvenSum, map_sum, map_mul, conj_ofReal, conj_hermiteScaled_real]

/-- Reality of a packet follows from conjugate symmetry of its inverse Fourier integrand. -/
theorem halfAiryPacket_real {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ)
    (c : Fin N → ℝ) (x : ℝ) : (halfAiryPacket ℓ c x).im = 0 := by
  have hs (t : ℝ) : conj (packetContourIntegrand ℓ c x (t : ℂ)) =
      packetContourIntegrand ℓ c x ((-t : ℝ) : ℂ) := by
    have hp : conj (halfPhase (t : ℂ)) = halfPhase ((-t : ℝ) : ℂ) := by
      simpa using conj_halfPhase_neg (-t)
    have hexp : conj (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * t) * x)) =
        Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (-(t : ℂ))) * x) := by
      simp only [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      congr 1
      ring
    simp only [packetContourIntegrand, Complex.ofReal_neg, map_mul, hp, hexp,
      conj_hermiteEvenSum_real, hermiteEvenSum_neg]

  have he : conj (halfAiryPacket ℓ c x) = halfAiryPacket ℓ c x := by
    change conj (∫ t : ℝ, packetContourIntegrand ℓ c x (t : ℂ)) =
      ∫ t : ℝ, packetContourIntegrand ℓ c x (t : ℂ)
    have hInt : Integrable (fun t : ℝ => packetContourIntegrand ℓ c x (t : ℂ)) := by
      obtain ⟨C, q, -, hq, h⟩ :=
        exists_norm_packetContourIntegrand_le hℓ (by positivity : 0 ≤ ℓ ^ 2 / 4) c x
      refine ((integrable_exp_neg_mul_sq hq).const_mul C).mono' ?_ (ae_of_all _ fun t => ?_)
      · exact ((differentiable_packetContourIntegrand ℓ c x).continuous.comp
          Complex.continuous_ofReal).aestronglyMeasurable
      · simpa only [lowerFrequency_zero] using h t 0 le_rfl le_rfl
    have hcomm := Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hInt
    change (∫ t : ℝ, conj (packetContourIntegrand ℓ c x (t : ℂ))) =
      conj (∫ t : ℝ, packetContourIntegrand ℓ c x (t : ℂ)) at hcomm
    rw [← hcomm]
    simp only [hs]
    exact integral_neg_eq_self (fun t : ℝ => packetContourIntegrand ℓ c x (t : ℂ)) volume
  have hj := congrArg Complex.im he
  simp only [conj_im] at hj
  linarith

/-- The full Airy frequency operator fixes the half-phase even profile in L². -/
theorem goeAiryFrequency_halfAiryFrequency_toLp {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ)
    (c : Fin N → ℝ) :
    goeAiryFrequency ((halfAiryFrequencySchwartz ℓ c 0 (by nlinarith [sq_pos_of_pos hℓ])).toLp 2 volume) =
      (halfAiryFrequencySchwartz ℓ c 0 (by nlinarith [sq_pos_of_pos hℓ])).toLp 2 volume := by
  let f := halfAiryFrequencySchwartz ℓ c 0 (by nlinarith [sq_pos_of_pos hℓ])
  change goeAiryFrequency (f.toLp 2 volume) = f.toLp 2 volume
  apply Lp.ext
  filter_upwards [goeAiryFrequency_apply_ae (f.toLp 2 volume), f.coeFn_toLp 2 volume,
    (f.coeFn_toLp 2 volume).comp_tendsto goeMeasurePreserving_neg.quasiMeasurePreserving.tendsto_ae]
    with t h₁ h₂ h₃
  change (f.toLp 2 volume) (-t) = f (-t) at h₃
  rw [h₁, h₂, h₃]
  simp only [f, halfAiryFrequencySchwartz_apply, halfAiryFrequencyProfile, lowerFrequency_zero,
    Complex.ofReal_neg, hermiteEvenSum_neg]
  rw [← halfPhase_mul_self]
  have hp : halfPhase (t : ℂ) * halfPhase (-(t : ℂ)) = 1 := by
    have hc := conj_halfPhase_neg (-t)
    simp only [neg_neg, Complex.ofReal_neg] at hc
    rw [← hc, Complex.mul_conj, ← Complex.sq_norm, norm_halfPhase_real, one_pow, Complex.ofReal_one]
  calc
    _ = halfPhase (t : ℂ) * ((halfPhase (t : ℂ) * halfPhase (-(t : ℂ))) *
        hermiteEvenSum ℓ c (t : ℂ)) := by ac_rfl
    _ = _ := by rw [hp, one_mul]

/-- The Airy involution fixes the L² class of every half-phase Hermite packet. -/
theorem goeAiryInvolution_halfAiryPacket_toLp {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ)
    (c : Fin N → ℝ) :
    goeAiryInvolution ((halfAiryPacketSchwartz ℓ hℓ c).toLp 2 volume) =
      (halfAiryPacketSchwartz ℓ hℓ c).toLp 2 volume := by
  unfold halfAiryPacketSchwartz
  rw [← goeFourierInv_toLp]
  simp only [goeAiryInvolution, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, goeAiryFrequency_halfAiryFrequency_toLp ℓ hℓ c]

/-- Each product appearing in the scaled Hermite pairing is integrable. -/
theorem integrable_hermiteScaled_pairing (ℓ : ℝ) (hℓ : 0 < ℓ) (j k : ℕ) :
    Integrable (fun t : ℝ => conj (hermiteScaled ℓ j (t : ℂ)) * hermiteScaled ℓ k (t : ℂ)) := by
  have hg : Integrable (fun t : ℝ => conj (hermiteEntire j (t : ℂ)) * hermiteEntire k (t : ℂ)) := by
    simp only [← Complex.star_def, hermiteEntire_pairing_integrand]
    apply Integrable.ofReal
    apply Integrable.const_mul
    simpa only [map_mul] using integrable_aeval_mul_gaussian (Polynomial.hermite j * Polynomial.hermite k)
  let a := 2 * Real.pi * ℓ
  have ha : 0 < a := by dsimp only [a]; positivity
  have h' := (hg.comp_mul_left' ha.ne').const_mul (((Real.sqrt a : ℝ) : ℂ) ^ 2)
  have he : (2 * (Real.pi : ℂ) * ℓ) = (a : ℂ) := by dsimp only [a]; push_cast; rfl
  convert h' using 1
  ext t
  simp only [hermiteScaled, he, ← Complex.ofReal_mul, map_mul, conj_ofReal]
  ring

/-- The squared integral of an even Hermite combination is the Euclidean squared coefficient norm. -/
theorem integral_norm_sq_hermiteEvenSum {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (c : Fin N → ℝ) :
    (∫ t : ℝ, ‖hermiteEvenSum ℓ c (t : ℂ)‖ ^ 2) = ∑ j, (c j) ^ 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_sum]
  let f (j k : Fin N) (t : ℝ) : ℂ :=
    ((c j : ℂ) * (c k : ℂ)) *
      (conj (hermiteScaled ℓ (2 * (j : ℕ)) (t : ℂ)) *
        hermiteScaled ℓ (2 * (k : ℕ)) (t : ℂ))
  have hf (j k : Fin N) : Integrable (f j k) :=
    (integrable_hermiteScaled_pairing ℓ hℓ _ _).const_mul _
  have he (t : ℝ) : ((‖hermiteEvenSum ℓ c (t : ℂ)‖ ^ 2 : ℝ) : ℂ) = ∑ j, ∑ k, f j k t := by
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
    simp only [hermiteEvenSum, map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [f]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hf j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun k _ => hf j k), Finset.sum_eq_single j]
  · unfold f
    rw [integral_const_mul]
    simp only [← Complex.star_def, hermiteScaled_orthonormal ℓ hℓ, ite_true, mul_one,
      pow_two, Complex.ofReal_mul]
  · intro k _ hk
    have hne : 2 * (j : ℕ) ≠ 2 * (k : ℕ) := by
      intro hh
      apply hk
      apply Fin.ext
      omega
    unfold f
    rw [integral_const_mul]
    simp only [← Complex.star_def, hermiteScaled_orthonormal ℓ hℓ, hne, ite_false, mul_zero]
  · simp

/-- The unshifted Airy packet has the squared norm of its Hermite coefficients. -/
theorem integral_norm_sq_halfAiryPacket {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (c : Fin N → ℝ) :
    (∫ t : ℝ, ‖halfAiryPacket ℓ c t‖ ^ 2) = ∑ j, (c j) ^ 2 := by
  simp_rw [← halfAiryPacketSchwartz_apply ℓ hℓ c]
  unfold halfAiryPacketSchwartz
  rw [goeIntegral_norm_sq_fourierInv]
  simp only [halfAiryFrequencySchwartz_apply, halfAiryFrequencyProfile, lowerFrequency_zero, norm_mul,
    norm_halfPhase_real, one_mul, integral_norm_sq_hermiteEvenSum ℓ hℓ c]

end GOELocalization
