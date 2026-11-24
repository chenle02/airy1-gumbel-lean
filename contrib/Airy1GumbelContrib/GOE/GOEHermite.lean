/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# Scaled Hermite functions

We normalize the probabilists' Hermite polynomials by the Gaussian pairing
and obtain a growth estimate for their entire extensions.
-/

namespace GOELocalization

open MeasureTheory Polynomial
open scoped Nat

/-- The probabilists' Hermite polynomial evaluated at `z` and divided by `√(k!)`. -/
noncomputable def hermiteNormalizedPoly (k : ℕ) (z : ℂ) : ℂ :=
  aeval z (hermite k) / (Real.sqrt (k.factorial : ℝ) : ℂ)

/-- The normalized Hermite function with Gaussian factor `exp (-z²/4)`
and normalization constant `1 / √(√(2π))`. -/
noncomputable def hermiteEntire (k : ℕ) (z : ℂ) : ℂ :=
  hermiteNormalizedPoly k z * Complex.exp (-(z ^ 2 / 4)) /
    (Real.sqrt (Real.sqrt (2 * Real.pi)) : ℂ)

/-- The Hermite function dilated by `2πℓ` with the corresponding square-root weight. -/
noncomputable def hermiteScaled (ℓ : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  (Real.sqrt (2 * Real.pi * ℓ) : ℂ) * hermiteEntire k ((2 * (Real.pi : ℂ) * ℓ) * z)

/-- Each positive odd factor is bounded by the following even factor. -/
theorem oddDoubleFactorial_le_even (n : ℕ) :
    (2 * n - 1)‼ ≤ (2 * n)‼ := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, Nat.doubleFactorial_add_one,
      show 2 * (n + 1) = 2 * n + 2 by omega, Nat.doubleFactorial_add_two]
    exact Nat.mul_le_mul (by omega) ih

/-- The square of the odd double factorial is bounded by the full even factorial. -/
theorem sq_oddDoubleFactorial_le_factorial (n : ℕ) :
    ((2 * n - 1)‼) ^ 2 ≤ (2 * n)! := by
  have hf : (2 * n)! = (2 * n)‼ * (2 * n - 1)‼ := by
    cases h : 2 * n with
    | zero => rfl
    | succ m => exact Nat.factorial_eq_mul_doubleFactorial m
  rw [hf, pow_two]
  exact Nat.mul_le_mul_right _ (oddDoubleFactorial_le_even n)

/-- A squared coefficient bound in natural numbers, before Hermite normalization. -/
theorem hermiteCoeff_mul_factorial_sq_le (k m : ℕ) (hm : m ≤ k) :
    (((hermite k).coeff m).natAbs * m.factorial) ^ 2 ≤ k.factorial * k ^ m := by
  rw [coeff_hermite]
  split_ifs with he
  · have hd : Even (k - m) := by rwa [Nat.even_add, ← Nat.even_sub hm] at he
    obtain ⟨n, hn⟩ := hd
    rw [← two_mul] at hn
    have hpow : ((k - m - 1)‼) ^ 2 ≤ (k - m)! := by
      rw [hn]
      exact sq_oddDoubleFactorial_le_factorial n
    have hc : Int.natAbs ((-1 : ℤ) ^ ((k - m) / 2) * ((k - m - 1)‼ : ℕ) * (k.choose m : ℕ)) =
        (k - m - 1)‼ * k.choose m := by
      simp [Int.natAbs_mul, Int.natAbs_pow]
    rw [hc, show (k - m - 1)‼ * k.choose m * m.factorial =
      (k - m - 1)‼ * (k.choose m * m.factorial) by ac_rfl, mul_pow]
    calc
      _ ≤ (k - m)! * (k.choose m * m.factorial) ^ 2 := Nat.mul_le_mul_right _ hpow
      _ = k.factorial * (k.choose m * m.factorial) := by
        rw [pow_two, ← mul_assoc, mul_comm (k - m)!, Nat.choose_mul_factorial_mul_factorial hm]
      _ ≤ k.factorial * k ^ m := by
        rw [mul_comm (k.choose m) (m.factorial), ← Nat.descFactorial_eq_factorial_mul_choose]
        exact Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow k m)
  · simp

/-- The normalized coefficient of degree `m` is bounded by `√k ^ m / m!`. -/
theorem norm_hermiteCoeff_div_sqrt_le (k m : ℕ) (hm : m ≤ k) :
    ‖((hermite k).coeff m : ℂ)‖ / Real.sqrt (k.factorial : ℝ) ≤
      (Real.sqrt (k : ℝ)) ^ m / (m.factorial : ℝ) := by
  have hk : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hm' : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hnorm : ‖((hermite k).coeff m : ℂ)‖ =
      (((hermite k).coeff m).natAbs : ℝ) := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
    rw [← Int.natCast_natAbs]
    exact Int.cast_natCast _
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hk) hm', hnorm]
  apply le_of_sq_le_sq _ (by positivity)
  simp only [mul_pow]
  rw [← pow_mul, mul_comm m 2, pow_mul, Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ)),
    Real.sq_sqrt hk.le, mul_comm ((k : ℝ) ^ m)]
  have h := hermiteCoeff_mul_factorial_sq_le k m hm
  rw [mul_pow] at h
  exact_mod_cast h

/-- An exponential bound on the normalized probabilists' Hermite polynomial on the complex plane. -/
theorem norm_hermiteNormalizedPoly_le (k : ℕ) (z : ℂ) :
    ‖hermiteNormalizedPoly k z‖ ≤
      Real.exp ((k : ℝ) + 2 * Real.sqrt k * ‖z‖) := by
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
    _ ≤ Real.exp (Real.sqrt (k : ℝ) * ‖z‖) := Real.sum_le_exp_of_nonneg (by positivity) _
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [show 0 ≤ Real.sqrt (k : ℝ) * ‖z‖ by positivity])

/-- The Gaussian weight `exp (-x²/2)` for the probabilists’ Hermite pairing. -/
noncomputable def hermiteGaussianWeight (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2))

/-- An integer polynomial times the Hermite Gaussian weight is integrable on the real line. -/
theorem integrable_aeval_mul_gaussian (p : ℤ[X]) :
    Integrable (fun x : ℝ => aeval x p * hermiteGaussianWeight x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, add_mul]
    change Integrable ((fun x : ℝ => aeval x p * hermiteGaussianWeight x) +
      (fun x : ℝ => aeval x q * hermiteGaussianWeight x))
    exact hp.add hq
  | monomial n a =>
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (s := (n : ℝ))
      (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    rw [show (fun x : ℝ => x ^ (n : ℝ) * Real.exp (-(1 / 2) * x ^ 2)) =
        (fun x : ℝ => x ^ n * hermiteGaussianWeight x) by
      ext x
      rw [Real.rpow_natCast, hermiteGaussianWeight]
      congr 2
      ring] at h
    simpa only [aeval_monomial, eq_intCast, mul_assoc] using h.const_mul (a : ℝ)

/-- Rodrigues’ formula for the Hermite Gaussian weight. -/
theorem deriv_gaussian_formula (k : ℕ) (x : ℝ) :
    deriv^[k] hermiteGaussianWeight x = (-1 : ℝ) ^ k * aeval x (hermite k) * hermiteGaussianWeight x :=
  deriv_gaussian_eq_hermite_mul_gaussian k x

/-- Each iterated derivative of the Gaussian has the next iterated derivative as its derivative. -/
theorem hasDerivAt_iterate_gaussian (k : ℕ) (x : ℝ) :
    HasDerivAt (deriv^[k] hermiteGaussianWeight) (deriv^[k + 1] hermiteGaussianWeight x) x := by
  rw [Function.iterate_succ_apply']
  apply DifferentiableAt.hasDerivAt
  rw [show deriv^[k] hermiteGaussianWeight = (fun y : ℝ => (-1 : ℝ) ^ k * aeval y (hermite k) * hermiteGaussianWeight y)
    from funext (deriv_gaussian_formula k)]
  apply DifferentiableAt.mul
  · exact (hermite k).differentiableAt_aeval.const_mul _
  · unfold hermiteGaussianWeight
    fun_prop

/-- Pairing a polynomial with any iterated derivative of the Gaussian gives an integrable function. -/
theorem integrable_aeval_mul_iterate_gaussian (p : ℤ[X]) (k : ℕ) :
    Integrable (fun x : ℝ => aeval x p * deriv^[k] hermiteGaussianWeight x) := by
  simpa only [deriv_gaussian_formula, map_mul, mul_left_comm, mul_assoc] using
    (integrable_aeval_mul_gaussian (p * hermite k)).const_mul ((-1 : ℝ) ^ k)

/-- Repeated integration by parts transfers derivatives from the Gaussian to a polynomial. -/
theorem rodrigues_pairing (p : ℤ[X]) (k : ℕ) :
    (∫ x : ℝ, aeval x p * deriv^[k] hermiteGaussianWeight x) =
      (-1 : ℝ) ^ k * ∫ x : ℝ, aeval x (derivative^[k] p) * hermiteGaussianWeight x := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    have hp := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun (x : ℝ) _ => p.hasDerivAt_aeval x)
      (fun (x : ℝ) _ => hasDerivAt_iterate_gaussian k x)
      (integrable_aeval_mul_iterate_gaussian p (k + 1))
      (integrable_aeval_mul_iterate_gaussian (derivative p) k)
      (integrable_aeval_mul_iterate_gaussian p k)
    change (∫ x : ℝ, aeval x p * deriv^[k + 1] hermiteGaussianWeight x) =
      -(∫ x : ℝ, aeval x (derivative p) * deriv^[k] hermiteGaussianWeight x) at hp
    rw [hp, ih, pow_succ', Function.iterate_succ_apply]
    ring

/-- The derivative of order equal to the degree of a monic Hermite polynomial is its degree factorial. -/
theorem iterate_derivative_hermite_self (j : ℕ) :
    derivative^[j] (hermite j) = C (j.factorial : ℤ) := by
  ext m
  rw [coeff_iterate_derivative]
  cases m with
  | zero => simp [coeff_hermite_self, Nat.descFactorial_self]
  | succ m =>
    rw [coeff_hermite_of_lt (by omega), smul_zero, coeff_C, ite_eq_right (by omega)]

/-- The total integral of the Hermite Gaussian weight. -/
theorem integral_gaussian_weight :
    (∫ x : ℝ, hermiteGaussianWeight x) = Real.sqrt (2 * Real.pi) := by
  rw [← show Real.pi / (1 / 2) = 2 * Real.pi by ring, ← integral_gaussian]
  congr 1
  ext x
  unfold hermiteGaussianWeight
  congr 1
  ring

/-- The unnormalized Hermite pairing for indices in increasing order. -/
theorem integral_hermite_pairing_of_le (j k : ℕ) (hjk : j ≤ k) :
    (∫ x : ℝ, aeval x (hermite j) * aeval x (hermite k) * hermiteGaussianWeight x) =
      if j = k then (k.factorial : ℝ) * Real.sqrt (2 * Real.pi) else 0 := by
  have hp := rodrigues_pairing (hermite j) k
  simp only [deriv_gaussian_formula] at hp
  have hfactor : (-1 : ℝ) ^ k *
      (∫ x : ℝ, aeval x (hermite j) * aeval x (hermite k) * hermiteGaussianWeight x) =
      (-1 : ℝ) ^ k * ∫ x : ℝ, aeval x (derivative^[k] (hermite j)) * hermiteGaussianWeight x := by
    rw [← integral_const_mul]
    convert hp using 2
    ext x
    ring
  apply mul_left_cancel₀ (pow_ne_zero k (by norm_num : (-1 : ℝ) ≠ 0)) at hfactor
  rw [hfactor]
  split_ifs with he
  · subst k
    rw [iterate_derivative_hermite_self]
    simp only [map_natCast, integral_const_mul, integral_gaussian_weight]
  · rw [iterate_derivative_eq_zero (by simpa using lt_of_le_of_ne hjk he)]
    simp

/-- Orthogonality and squared norms of the unnormalized Hermite polynomials with Gaussian weight. -/
theorem integral_hermite_pairing (j k : ℕ) :
    (∫ x : ℝ, aeval x (hermite j) * aeval x (hermite k) * hermiteGaussianWeight x) =
      if j = k then (k.factorial : ℝ) * Real.sqrt (2 * Real.pi) else 0 := by
  rcases le_total j k with h | h
  · exact integral_hermite_pairing_of_le j k h
  · rw [show (fun x : ℝ => aeval x (hermite j) * aeval x (hermite k) * hermiteGaussianWeight x) =
        (fun x : ℝ => aeval x (hermite k) * aeval x (hermite j) * hermiteGaussianWeight x) by
        ext x
        rw [mul_comm (aeval x (hermite j))]]
    rw [integral_hermite_pairing_of_le k j h]
    by_cases he : j = k
    · subst k
      rfl
    · simp [he, Ne.symm he]

/-- Real and complex evaluation of a Hermite polynomial agree at real arguments. -/
theorem ofReal_aeval_hermite (k : ℕ) (x : ℝ) :
    ((aeval x (hermite k) : ℝ) : ℂ) = aeval (x : ℂ) (hermite k) := by
  simp only [aeval_eq_sum_range, zsmul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_intCast, Complex.ofReal_pow]

/-- The entire Hermite function takes the real Gaussian formula at real arguments. -/
theorem hermiteEntire_ofReal (k : ℕ) (x : ℝ) :
    hermiteEntire k (x : ℂ) =
      (((aeval x (hermite k) / Real.sqrt (k.factorial : ℝ) * Real.exp (-(x ^ 2 / 4))) /
        Real.sqrt (Real.sqrt (2 * Real.pi)) : ℝ) : ℂ) := by
  simp only [hermiteEntire, hermiteNormalizedPoly, Complex.ofReal_div, Complex.ofReal_mul,
    ofReal_aeval_hermite, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_ofNat]

/-- The conjugate Hermite pairing on the real line is a normalized real polynomial-Gaussian product. -/
theorem hermiteEntire_pairing_integrand (j k : ℕ) (x : ℝ) :
    star (hermiteEntire j (x : ℂ)) * hermiteEntire k (x : ℂ) =
      (((Real.sqrt (j.factorial : ℝ) * Real.sqrt (k.factorial : ℝ) *
          Real.sqrt (2 * Real.pi))⁻¹ *
        (aeval x (hermite j) * aeval x (hermite k) * hermiteGaussianWeight x) : ℝ) : ℂ) := by
  rw [hermiteEntire_ofReal, hermiteEntire_ofReal]
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  congr 1
  have hexp : Real.exp (-(x ^ 2 / 4)) * Real.exp (-(x ^ 2 / 4)) = hermiteGaussianWeight x := by
    rw [← Real.exp_add, hermiteGaussianWeight]
    congr 1
    ring
  have hnorm : Real.sqrt (Real.sqrt (2 * Real.pi)) * Real.sqrt (Real.sqrt (2 * Real.pi)) =
      Real.sqrt (2 * Real.pi) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  calc
    _ = (Real.sqrt (j.factorial : ℝ) * Real.sqrt (k.factorial : ℝ) *
          (Real.sqrt (Real.sqrt (2 * Real.pi)) * Real.sqrt (Real.sqrt (2 * Real.pi))))⁻¹ *
        (aeval x (hermite j) * aeval x (hermite k) *
          (Real.exp (-(x ^ 2 / 4)) * Real.exp (-(x ^ 2 / 4)))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hnorm, hexp]

/-- The normalized Hermite functions are orthonormal before dilation. -/
theorem hermiteEntire_pairing (j k : ℕ) :
    (∫ x : ℝ, star (hermiteEntire j (x : ℂ)) * hermiteEntire k (x : ℂ)) =
      if j = k then (1 : ℂ) else 0 := by
  simp_rw [hermiteEntire_pairing_integrand]
  rw [integral_complex_ofReal, integral_const_mul, integral_hermite_pairing]
  by_cases he : j = k
  · subst k
    have hfact : 0 < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
    have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    simp only [ite_true, Real.mul_self_sqrt hfact.le]
    rw [inv_mul_cancel₀ (mul_ne_zero hfact.ne' hpi.ne'), Complex.ofReal_one]
  · simp [he]

/-- The scaled Hermite functions are orthonormal on the real line for every positive dilation. -/
theorem hermiteScaled_orthonormal (ℓ : ℝ) (hℓ : 0 < ℓ) (j k : ℕ) :
    (∫ ν : ℝ, star (hermiteScaled ℓ j (ν : ℂ)) * hermiteScaled ℓ k (ν : ℂ))
      = if j = k then (1 : ℂ) else 0 := by
  let a : ℝ := 2 * Real.pi * ℓ
  have ha : 0 < a := by dsimp [a]; positivity
  have haC : (2 * (Real.pi : ℂ) * ℓ) = (a : ℂ) := by simp [a]
  simp only [hermiteScaled, haC]
  change (∫ ν : ℝ, star ((Real.sqrt a : ℂ) * hermiteEntire j ((a : ℂ) * (ν : ℂ))) *
    ((Real.sqrt a : ℂ) * hermiteEntire k ((a : ℂ) * (ν : ℂ)))) = _
  have hpoint (ν : ℝ) :
      star ((Real.sqrt a : ℂ) * hermiteEntire j ((a : ℂ) * (ν : ℂ))) *
        ((Real.sqrt a : ℂ) * hermiteEntire k ((a : ℂ) * (ν : ℂ))) =
      (a : ℂ) * (star (hermiteEntire j ((a * ν : ℝ) : ℂ)) *
        hermiteEntire k ((a * ν : ℝ) : ℂ)) := by
    rw [star_mul]
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
    calc
      _ = ((Real.sqrt a : ℂ) * (Real.sqrt a : ℂ)) *
          ((starRingEnd ℂ) (hermiteEntire j ((a : ℂ) * (ν : ℂ))) *
            hermiteEntire k ((a : ℂ) * (ν : ℂ))) := by ring
      _ = _ := by rw [← Complex.ofReal_mul, Real.mul_self_sqrt ha.le]
  simp_rw [hpoint]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun x : ℝ => star (hermiteEntire j (x : ℂ)) * hermiteEntire k (x : ℂ)),
    abs_of_pos (inv_pos.2 ha), Complex.real_smul, Complex.ofReal_inv,
    ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne'), one_mul,
    hermiteEntire_pairing]

/-- The scaled Hermite function of an even index is even on the complex plane. -/
theorem hermiteScaled_even (ℓ : ℝ) (j : ℕ) (z : ℂ) :
    hermiteScaled ℓ (2 * j) (-z) = hermiteScaled ℓ (2 * j) z := by
  have hp (w : ℂ) : aeval (-w) (hermite (2 * j)) = aeval w (hermite (2 * j)) := by
    simp only [aeval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hm : Even m
    · rw [hm.neg_pow]
    · have ho : Odd (2 * j + m) := by
        simpa using (even_two_mul j).add_odd (Nat.not_even_iff_odd.1 hm)
      simp only [coeff_hermite_of_odd_add ho, zero_smul]
  simp only [hermiteScaled, mul_neg, hermiteEntire, hermiteNormalizedPoly, hp, neg_sq]

end GOELocalization
