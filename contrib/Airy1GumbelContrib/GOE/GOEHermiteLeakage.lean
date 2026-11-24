/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.GOE.GOEHalfPhase
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Leakage of half-Airy Hermite packets

The weighted packet energy is the squared norm on the shifted frequency line.
At shift `a = ℓ²/16`, the Gaussian decay controls all the chosen even modes.
-/

namespace GOELocalization

open MeasureTheory Set Polynomial
open scoped FourierTransform SchwartzMap

/-- The number of even modes for the leakage bound. With `T = M√M` and
`η = 1/1280`, this is `⌊ηT/2⌋ + 1`. -/
noncomputable def goeModeCount (M : ℝ) : ℕ :=
  ⌊(M * Real.sqrt M) / 2560⌋₊ + 1

/-- The Hermite dilation at cutoff `M`. -/
noncomputable def goeEll (M : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt M)

/-- The refined exponential majorant from the normalized Hermite coefficient bounds. -/
theorem norm_hermiteNormalizedPoly_le_exp_sqrt (k : ℕ) (z : ℂ) :
    ‖hermiteNormalizedPoly k z‖ ≤ Real.exp (Real.sqrt k * ‖z‖) := by
  rw [hermiteNormalizedPoly, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    aeval_eq_sum_range, natDegree_hermite]
  simp only [zsmul_eq_mul]
  calc
    _ ≤ (∑ m ∈ Finset.range (k + 1), ‖((hermite k).coeff m : ℂ) * z ^ m‖) /
        Real.sqrt (k.factorial : ℝ) :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) (Real.sqrt_nonneg _)
    _ ≤ ∑ m ∈ Finset.range (k + 1), (Real.sqrt (k : ℝ) * ‖z‖) ^ m / (m.factorial : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, norm_pow, mul_div_right_comm, mul_pow, mul_div_right_comm]
      exact mul_le_mul_of_nonneg_right
        (norm_hermiteCoeff_div_sqrt_le k m (Nat.le_of_lt_succ (Finset.mem_range.1 hm)))
        (pow_nonneg (norm_nonneg z) _)
    _ ≤ _ := Real.sum_le_exp_of_nonneg (by positivity) _

/-- Weighted Plancherel on the lower contour with strictly positive Gaussian margin. -/
theorem halfAiryPacket_weightedEnergy {N : ℕ} {ℓ a : ℝ}
    (hℓ : 0 < ℓ) (ha : 0 ≤ a) (hastrip : a ≤ ℓ ^ 2 / 4)
    (c : Fin N → ℝ) :
    (∫ x : ℝ, ‖(Real.exp (-a*x) : ℂ) * halfAiryPacket ℓ c x‖ ^ 2) =
      ∫ ν : ℝ, ‖halfPhase ((ν : ℂ) - Complex.I * (a/(2*Real.pi))) *
        hermiteEvenSum ℓ c ((ν : ℂ) - Complex.I * (a/(2*Real.pi)))‖ ^ 2 := by
  simp_rw [halfAiryPacket_shift_fourierInv hℓ ha hastrip c]
  rw [goeIntegral_norm_sq_fourierInv]
  simp only [halfAiryFrequencySchwartz_apply, halfAiryFrequencyProfile, lowerFrequency]

/-- The weighted squared modulus used in Plancherel is integrable. -/
theorem integrable_weighted_halfAiryPacket_sq {N : ℕ} {ℓ a : ℝ}
    (hℓ : 0 < ℓ) (ha : 0 ≤ a) (hastrip : a ≤ ℓ ^ 2 / 4) (c : Fin N → ℝ) :
    Integrable (fun x : ℝ => ‖(Real.exp (-a * x) : ℂ) * halfAiryPacket ℓ c x‖ ^ 2) := by
  let g : 𝓢(ℝ, ℂ) := 𝓕⁻ (halfAiryFrequencySchwartz ℓ c a (by nlinarith [sq_pos_of_pos hℓ]))
  have hg : MemLp (g : ℝ → ℂ) 2 (volume : Measure ℝ) := g.memLp 2
  simpa only [halfAiryPacket_shift_fourierInv hℓ ha hastrip c] using
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg

/-- The single Hermite mode with the half phase factors using the common shifted exponent. -/
theorem halfPhase_mul_hermiteScaled (ℓ : ℝ) (k : ℕ) (z : ℂ) :
    halfPhase z * hermiteScaled ℓ k z =
      Complex.exp (hermitePacketExponent ℓ z) *
        (((Real.sqrt (2 * Real.pi * ℓ) / Real.sqrt (Real.sqrt (2 * Real.pi)) : ℝ) : ℂ) *
          hermiteNormalizedPoly k ((2 * (Real.pi : ℂ) * ℓ) * z)) := by
  rw [hermiteScaled, hermiteEntire, hermitePacketExponent, sub_eq_add_neg, Complex.exp_add,
    halfPhase, Complex.ofReal_div]
  ring

/-- Squared modulus of one phase-shifted mode at `a = ℓ²/16`. In coordinates
`y = ℓ (2πν)` and `b = ℓa`, the two absorptions retain `5y²/16` decay and leave
`9k + 3b²/2` in the exponent. The Gaussian normalization before integration is `√(2π) ℓ`. -/
theorem norm_sq_shifted_hermiteMode_le (ℓ : ℝ) (hℓ : 0 < ℓ) (k : ℕ) (ν : ℝ) :
    ‖halfPhase (lowerFrequency ν (ℓ ^ 2 / 16)) *
        hermiteScaled ℓ k (lowerFrequency ν (ℓ ^ 2 / 16))‖ ^ 2 ≤
      (Real.sqrt (2 * Real.pi) * ℓ) *
        Real.exp (-(5 / 16) * (2 * Real.pi * ℓ * ν) ^ 2 + 9 * k +
          3 * (ℓ * (ℓ ^ 2 / 16)) ^ 2 / 2) := by
  let a := ℓ ^ 2 / 16
  let y := 2 * Real.pi * ℓ * ν
  let b := ℓ * a
  let r := (a / 2 - ℓ ^ 2 / 4) * (2 * Real.pi * ν) ^ 2 + ℓ ^ 2 * a ^ 2 / 4 - a ^ 3 / 6
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have harg : ‖(2 * (Real.pi : ℂ) * ℓ) * lowerFrequency ν a‖ ≤ |y| + b := by
    calc
      _ ≤ ℓ * (2 * Real.pi * |ν| + a) := norm_hermite_argument_lower_le hℓ.le ha ν
      _ = _ := by
        dsimp [y, b]
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * ℓ)]
        ring
  have hpoly := (norm_hermiteNormalizedPoly_le_exp_sqrt k
    ((2 * (Real.pi : ℂ) * ℓ) * lowerFrequency ν a)).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left harg (Real.sqrt_nonneg _)))
  have h₁ : 2 * Real.sqrt k * |y| ≤ y ^ 2 / 8 + 8 * (k : ℝ) := by
    nlinarith [sq_nonneg (|y| - 8 * Real.sqrt k), sq_abs y,
      Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k)]
  have h₂ : 2 * Real.sqrt k * b ≤ (k : ℝ) + b ^ 2 := by
    nlinarith [sq_nonneg (b - Real.sqrt k), Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k)]
  have hreal : 2 * r = -(7 / 16) * y ^ 2 + b ^ 2 / 2 - a ^ 3 / 3 := by
    dsimp [r, a, y, b]
    ring
  have hnormal : ‖(Real.sqrt (2 * Real.pi * ℓ) / Real.sqrt (Real.sqrt (2 * Real.pi)) : ℝ)‖ ^ 2 =
      Real.sqrt (2 * Real.pi) * ℓ := by
    rw [Real.norm_of_nonneg (by positivity), div_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (Real.sqrt_nonneg _)]
    apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.2 (by positivity : 0 < 2 * Real.pi)))).2
    calc
      _ = (2 * Real.pi) * ℓ := rfl
      _ = _ := by nth_rw 1 [← Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]; ring
  change ‖halfPhase (lowerFrequency ν a) * hermiteScaled ℓ k (lowerFrequency ν a)‖ ^ 2 ≤
    (Real.sqrt (2 * Real.pi) * ℓ) * Real.exp (-(5 / 16) * y ^ 2 + 9 * k + 3 * b ^ 2 / 2)
  rw [halfPhase_mul_hermiteScaled, norm_mul, norm_mul, Complex.norm_real, Complex.norm_exp,
    hermitePacketExponent_lower]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  change (Real.exp r * (_ * _)) ^ 2 ≤ _
  rw [mul_pow, mul_pow, hnormal, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  calc
    _ ≤ Real.exp (2 * r) * ((Real.sqrt (2 * Real.pi) * ℓ) *
        Real.exp (Real.sqrt k * (|y| + b)) ^ 2) := by gcongr
    _ = (Real.sqrt (2 * Real.pi) * ℓ) * Real.exp (2 * r + 2 * (Real.sqrt k * (|y| + b))) := by
      rw [Real.exp_add, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      ac_rfl
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      rw [hreal]
      nlinarith [pow_nonneg ha 3]

/-- The Gaussian envelope has mass `√(8/5)`: the factor `√(2π) ℓ` is
multiplied by `1/(2πℓ)` under `y = 2πℓν`, and the Gaussian integral is `√(16π/5)`. -/
theorem integral_shifted_hermite_gaussian (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (∫ ν : ℝ, (Real.sqrt (2 * Real.pi) * ℓ) *
      Real.exp (-(5 / 16) * (2 * Real.pi * ℓ * ν) ^ 2)) = Real.sqrt (8 / 5) := by
  have hs : 0 < 2 * Real.pi * ℓ := by positivity
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun y : ℝ => Real.exp (-(5 / 16) * y ^ 2)),
    abs_of_pos (inv_pos.mpr hs), smul_eq_mul, integral_gaussian]
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).1
  simp only [mul_pow, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi),
    Real.sq_sqrt (by positivity : 0 ≤ Real.pi / (5 / 16)), Real.sq_sqrt (by norm_num : 0 ≤ (8 / 5 : ℝ))]
  field_simp
  ring

/-- Cauchy–Schwarz for the coefficient sum gives one copy of the sum of squared mode moduli. -/
theorem norm_sq_halfPhase_mul_hermiteEvenSum_le {N : ℕ} (ℓ : ℝ) (c : Fin N → ℝ) (z : ℂ) :
    ‖halfPhase z * hermiteEvenSum ℓ c z‖ ^ 2 ≤
      (∑ j, (c j) ^ 2) * ∑ j : Fin N, ‖halfPhase z * hermiteScaled ℓ (2 * (j : ℕ)) z‖ ^ 2 := by
  let f (j : Fin N) := halfPhase z * hermiteScaled ℓ (2 * (j : ℕ)) z
  have he : halfPhase z * hermiteEvenSum ℓ c z = ∑ j, (c j : ℂ) * f j := by
    rw [hermiteEvenSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]
    ring
  rw [he]
  calc
    _ ≤ (∑ j, ‖(c j : ℂ) * f j‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ = (∑ j, |c j| * ‖f j‖) ^ 2 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := by
      simpa only [sq_abs] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j => |c j|) (fun j => ‖f j‖)

/-- The shifted profile has energy at most the exact Gaussian prefactor `√(8/5)`
times a single factor of `N`, the common exponent bound and the squared coefficient norm. -/
theorem integral_norm_sq_shiftedHermite_le {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (c : Fin N → ℝ) :
    (∫ ν : ℝ, ‖halfAiryFrequencyProfile ℓ c (ℓ ^ 2 / 16) ν‖ ^ 2) ≤
      Real.sqrt (8 / 5) * N *
        Real.exp (9 * (2 * (N - 1) : ℕ) + 3 * (ℓ * (ℓ ^ 2 / 16)) ^ 2 / 2) *
        ∑ j, (c j) ^ 2 := by
  let n : ℕ := 2 * (N - 1)
  let b := ℓ * (ℓ ^ 2 / 16)
  let B := Real.exp (9 * (n : ℝ) + 3 * b ^ 2 / 2)
  let G (ν : ℝ) := (Real.sqrt (2 * Real.pi) * ℓ) * Real.exp (-(5 / 16) * (2 * Real.pi * ℓ * ν) ^ 2)
  let S : ℝ := ∑ j, (c j) ^ 2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hG : Integrable G := by
    have hg := (integrable_exp_neg_mul_sq (b := (5 / 16) * (2 * Real.pi * ℓ) ^ 2) (by positivity)).const_mul
      (Real.sqrt (2 * Real.pi) * ℓ)
    convert hg using 1
    ext t
    dsimp only [G]
    congr 2
    ring
  have hm (ν : ℝ) (j : Fin N) :
      ‖halfPhase (lowerFrequency ν (ℓ ^ 2 / 16)) *
          hermiteScaled ℓ (2 * (j : ℕ)) (lowerFrequency ν (ℓ ^ 2 / 16))‖ ^ 2 ≤ B * G ν := by
    have hdegree : 2 * (j : ℕ) ≤ n := by
      have hj := j.isLt
      dsimp [n]
      omega
    have hcast : ((2 * (j : ℕ) : ℕ) : ℝ) ≤ n := by exact_mod_cast hdegree
    have hE : Real.exp (9 * ((2 * (j : ℕ) : ℕ) : ℝ) + 3 * b ^ 2 / 2) ≤ B :=
      Real.exp_le_exp.mpr (show 9 * ((2 * (j : ℕ) : ℕ) : ℝ) + 3 * b ^ 2 / 2 ≤
        9 * (n : ℝ) + 3 * b ^ 2 / 2 by linarith)
    have hGν : 0 ≤ G ν := by dsimp only [G]; positivity
    refine (norm_sq_shifted_hermiteMode_le ℓ hℓ _ ν).trans ?_
    calc
      _ = G ν * Real.exp (9 * ((2 * (j : ℕ) : ℕ) : ℝ) + 3 * b ^ 2 / 2) := by
        dsimp only [G, b]
        simp only [Real.exp_add]
        ac_rfl
      _ ≤ G ν * B := mul_le_mul_of_nonneg_left hE hGν
      _ = B * G ν := mul_comm _ _
  have hp (ν : ℝ) : ‖halfAiryFrequencyProfile ℓ c (ℓ ^ 2 / 16) ν‖ ^ 2 ≤
      ((N : ℝ) * B * S) * G ν := by
    unfold halfAiryFrequencyProfile
    refine (norm_sq_halfPhase_mul_hermiteEvenSum_le _ _ _).trans ?_
    change S * _ ≤ _
    calc
      _ ≤ S * ∑ _ : Fin N, B * G ν :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hm ν j) hS
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  let g := halfAiryFrequencySchwartz ℓ c (ℓ ^ 2 / 16) (by nlinarith [sq_pos_of_pos hℓ])
  have hg : MemLp (g : ℝ → ℂ) 2 (volume : Measure ℝ) := g.memLp 2
  have hgi : Integrable (fun ν : ℝ => ‖halfAiryFrequencyProfile ℓ c (ℓ ^ 2 / 16) ν‖ ^ 2) := by
    simpa only [g, halfAiryFrequencySchwartz_apply] using
      (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  change _ ≤ Real.sqrt (8 / 5) * N * B * S
  calc
    _ ≤ ∫ ν : ℝ, ((N : ℝ) * B * S) * G ν :=
      integral_mono_ae hgi (hG.const_mul _) (ae_of_all _ hp)
    _ = _ := by
      rw [integral_const_mul, integral_shifted_hermite_gaussian ℓ hℓ]
      ring

/-- Restricting to `x ≤ -M` removes at least `exp(-2aM)` from the weighted energy. -/
theorem setIntegral_halfAiryPacket_le_weighted {N : ℕ} {ℓ a : ℝ}
    (hℓ : 0 < ℓ) (ha : 0 ≤ a) (hastrip : a ≤ ℓ ^ 2 / 4)
    (c : Fin N → ℝ) (M : ℝ) :
    (∫ x in Iic (-M), ‖halfAiryPacket ℓ c x‖ ^ 2) ≤
      Real.exp (-2 * a * M) * ∫ x : ℝ, ‖(Real.exp (-a * x) : ℂ) * halfAiryPacket ℓ c x‖ ^ 2 := by
  let f (x : ℝ) := ‖(Real.exp (-a * x) : ℂ) * halfAiryPacket ℓ c x‖ ^ 2
  have hf : Integrable f := integrable_weighted_halfAiryPacket_sq hℓ ha hastrip c
  let g := halfAiryPacketSchwartz ℓ hℓ c
  have hg : MemLp (g : ℝ → ℂ) 2 (volume : Measure ℝ) := g.memLp 2
  have hgi : Integrable (fun x : ℝ => ‖halfAiryPacket ℓ c x‖ ^ 2) := by
    simpa only [g, halfAiryPacketSchwartz_apply] using
      (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  let C := Real.exp (-2 * a * M)
  change _ ≤ C * ∫ x : ℝ, f x
  calc
    _ ≤ ∫ x in Iic (-M), C * f x := by
      refine integral_mono_ae hgi.integrableOn (hf.const_mul C).integrableOn ?_
      filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      change x ≤ -M at hx
      have hx' : 2 * a * x ≤ -2 * a * M := by
        nlinarith [mul_le_mul_of_nonneg_left hx ha]
      calc
        ‖halfAiryPacket ℓ c x‖ ^ 2 = Real.exp (2 * a * x) * f x := by
          dsimp [f]
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow,
            ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
          rw [show 2 * a * x + (2 : ℕ) * (-a * x) = (0 : ℝ) by push_cast; ring, Real.exp_zero, one_mul]
        _ ≤ C * f x := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx') (sq_nonneg _)
    _ ≤ _ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hf (ae_of_all _ fun _ => sq_nonneg _)) (Real.exp_nonneg _)

/-- The combined constants for `M ≥ 16`. Here `T = M√M ≥ 64`, the largest degree is
at most `T/1280`, and `b² = T/256`. The exact prefactor `√(8/5)` is bounded by `2`. -/
theorem goeLeakage_factor_le (M : ℝ) (hM : 16 ≤ M) :
    Real.exp (-2 * (goeEll M ^ 2 / 16) * M) *
      (Real.sqrt (8 / 5) * (goeModeCount M : ℝ) *
        Real.exp (9 * (2 * (goeModeCount M - 1) : ℕ) +
          3 * (goeEll M * (goeEll M ^ 2 / 16)) ^ 2 / 2)) ≤
      Real.exp (-(M * Real.sqrt M) / 16) := by
  let T := M * Real.sqrt M
  let N := goeModeCount M
  let ℓ := goeEll M
  have hM₀ : 0 ≤ M := by linarith
  have hT : 64 ≤ T := by
    have h16 : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    have hr : 4 ≤ Real.sqrt M := h16 ▸ Real.sqrt_le_sqrt hM
    change 64 ≤ M * Real.sqrt M
    nlinarith [mul_le_mul hM hr (by norm_num : (0 : ℝ) ≤ 4) hM₀]
  have hℓ : ℓ ^ 2 = Real.sqrt M := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hb : (ℓ * (ℓ ^ 2 / 16)) ^ 2 = T / 256 := by
    rw [mul_pow, hℓ, div_pow, Real.sq_sqrt hM₀]
    dsimp [T]
    ring
  have hfloor : (⌊T / 2560⌋₊ : ℝ) ≤ T / 2560 := Nat.floor_le (by linarith)
  have hN : (N : ℝ) ≤ T / 2560 + 1 := by
    change ((⌊T / 2560⌋₊ + 1 : ℕ) : ℝ) ≤ _
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hn : ((2 * (N - 1) : ℕ) : ℝ) ≤ T / 1280 := by
    change ((2 * ((⌊T / 2560⌋₊ + 1) - 1) : ℕ) : ℝ) ≤ T / 1280
    rw [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have hp : Real.sqrt (8 / 5) * N ≤ Real.exp (T / 32) := by
    have hpre : Real.sqrt (8 / 5) ≤ 2 := by
      calc
        _ ≤ Real.sqrt (2 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
        _ ≤ Real.sqrt ((2 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
        _ = _ := Real.sqrt_sq (by norm_num)
    calc
      _ ≤ 2 * (N : ℝ) := mul_le_mul_of_nonneg_right hpre (Nat.cast_nonneg _)
      _ ≤ 1 + T / 32 := by linarith
      _ ≤ _ := by simpa only [add_comm (1 : ℝ)] using Real.add_one_le_exp (T / 32)
  have he : 9 * ((2 * (N - 1) : ℕ) : ℝ) + 3 * (ℓ * (ℓ ^ 2 / 16)) ^ 2 / 2 ≤ T / 32 := by
    have hdegree : 20 * ((2 * (N - 1) : ℕ) : ℝ) ≤ T / 64 := by linarith
    have hshift : 3 * (ℓ * (ℓ ^ 2 / 16)) ^ 2 ≤ T / 64 := by rw [hb]; linarith
    linarith [Nat.cast_nonneg (α := ℝ) (2 * (N - 1)), sq_nonneg (ℓ * (ℓ ^ 2 / 16))]
  change Real.exp (-2 * (ℓ ^ 2 / 16) * M) * (Real.sqrt (8 / 5) * N * Real.exp _) ≤
    Real.exp (-T / 16)
  have houter : -2 * (ℓ ^ 2 / 16) * M = -T / 8 := by rw [hℓ]; dsimp [T]; ring
  rw [houter]
  calc
    _ ≤ Real.exp (-T / 8) * (Real.exp (T / 32) * Real.exp (T / 32)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- The squared leakage of a half-Airy packet below `-M` decays at rate
`exp(-M√M/16)` relative to the squared coefficient norm. Here `ε = 1/16`
sets the shift and `η = 1/1280` sets the number of modes. -/
theorem halfAiryPacket_leakage (M : ℝ) (hM : 16 ≤ M)
    (c : Fin (goeModeCount M) → ℝ) :
    (∫ x in Set.Iic (-M), ‖halfAiryPacket (goeEll M) c x‖ ^ 2) ≤
      Real.exp (-(M * Real.sqrt M) / 16) * ∑ j, c j ^ 2 := by
  let ℓ := goeEll M
  let a := ℓ ^ 2 / 16
  have hℓ : 0 < ℓ := by dsimp [ℓ, goeEll]; apply Real.sqrt_pos.2; apply Real.sqrt_pos.2; linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : a ≤ ℓ ^ 2 / 4 := by dsimp [a]; nlinarith [sq_nonneg ℓ]
  have hW := setIntegral_halfAiryPacket_le_weighted hℓ ha hs c M
  rw [halfAiryPacket_weightedEnergy hℓ ha hs c] at hW
  refine hW.trans ?_
  change Real.exp (-2 * a * M) * (∫ ν : ℝ, ‖halfAiryFrequencyProfile ℓ c a ν‖ ^ 2) ≤ _
  calc
    _ ≤ Real.exp (-2 * a * M) *
        (Real.sqrt (8 / 5) * (goeModeCount M : ℝ) *
          Real.exp (9 * (2 * (goeModeCount M - 1) : ℕ) + 3 * (ℓ * a) ^ 2 / 2) *
          ∑ j, (c j) ^ 2) :=
      mul_le_mul_of_nonneg_left (integral_norm_sq_shiftedHermite_le ℓ hℓ c) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (goeLeakage_factor_le M hM) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end GOELocalization
