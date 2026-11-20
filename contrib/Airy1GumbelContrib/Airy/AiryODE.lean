/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.Airy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-! # The Airy differential equation

We prove that the Airy functions `Complex.airyAi` and `Complex.airyBi` (defined in
`Airy1GumbelContrib.Airy.Airy`) satisfy the Airy differential equation `y'' = z y`,
and that they commute with complex conjugation (so they are real-valued on the real axis).

Everything is bootstrapped from the corresponding statements for the regularized
hypergeometric function `₀F̃₁(; b; w) = ∑' n, w ^ n / (n ! * Γ(b + n))`
(`Complex.regularizedHGFun 0 {b} w` in Mathlib):

* `Complex.regularizedHGFunCoeff_zero_singleton_succ`: the coefficient identity
  `(n + 1) * c_b (n + 1) = c_{b+1} n` (this is `Γ(b + n + 1) = (b + n) Γ(b + n)` in disguise,
  but formulated so that it holds for all `b`, even at the poles of `Γ`);
* `Complex.radius_regularizedHGFunSeries_zero_singleton_succ`: the series for `b + 1` is
  again entire (its radius of convergence is `⊤`);
* `Complex.hasDerivAt_regularizedHGFun_zero_singleton`: the term-by-term derivative
  identity `d/dw ₀F̃₁(; b; w) = ₀F̃₁(; b + 1; w)`, proved by locally uniform approximation
  by partial sums (`hasDerivAt_of_tendstoLocallyUniformlyOn`);
* `Complex.regularizedHGFun_zero_singleton_recurrence`:
  `w * ₀F̃₁(; b + 2; w) + b * ₀F̃₁(; b + 1; w) = ₀F̃₁(; b; w)` for `b ∉ {0, -1, -2, ...}`,
  from `Γ(s + 1) = s Γ(s)`;
* `Complex.iteratedDeriv_two_airyAi`, `Complex.iteratedDeriv_two_airyBi`: the Airy ODE
  `iteratedDeriv 2 airyAi z = z * airyAi z` (and the same for `airyBi`);
* `Complex.airyAi_conj`, `Complex.airyBi_conj`: `Ai, Bi` commute with `star`.

For the ODE, write `u_b z := ₀F̃₁(; b; z³/9)`.  The chain rule and the two hypergeometric
identities above give `u_b'' z = z * u_b z + (2/3 - b) * z * u_{b+1} z`; at `b = 2/3` the
second term vanishes, while for `b = 4/3` it is exactly what is needed for
`(z * u_{4/3})'' = z * (z * u_{4/3})`, and the Airy equation follows.
-/

open scoped Nat

open FormalMultilinearSeries Filter

namespace Complex

/-- The power series expansion of the regularized hypergeometric function with a singleton
lower parameter: `₀F̃₁(; b; w) = ∑' n, w ^ n / (n ! * Γ (b + n))`. -/
theorem regularizedHGFun_zero_singleton_eq_tsum (b : ℂ) (w : ℂ) :
    regularizedHGFun 0 {b} w = ∑' n, regularizedHGFunCoeff 0 {b} n * w ^ n := by
  show ∑' n, (regularizedHGFunSeries 0 {b}) n (fun _ => w) = _
  apply tsum_congr
  intro n
  simp [regularizedHGFunSeries, smul_eq_mul]
  ring

/-- The key coefficient identity `(n + 1) * c_b (n + 1) = c_{b + 1} n` for the regularized
`₀F₁` coefficients.  Note that this holds for *all* `b : ℂ`, even at the poles of `Γ`
(where both sides vanish), since we use the regularized coefficients. -/
theorem regularizedHGFunCoeff_zero_singleton_succ (b : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * regularizedHGFunCoeff 0 {b} (n + 1) = regularizedHGFunCoeff 0 {b + 1} n := by
  have hfact : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsucc : ((n : ℂ) + 1) ≠ 0 := by
    rw [show ((n : ℂ) + 1) = ((((n : ℝ)) + 1 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
    Multiset.prod_singleton, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [show b + ((n : ℂ) + 1) = b + 1 + ↑n by ring]
  by_cases hΓ : Complex.Gamma (b + 1 + (n : ℂ)) = 0
  · simp [hΓ]
  · field_simp [hΓ, hfact, hsucc]

/-- The radius of convergence of the `₀F̃₁(; b + 1; ·)` series is infinite: shifting the
parameter of an entire `₀F̃₁` series preserves entireness. -/
theorem radius_regularizedHGFunSeries_zero_singleton_succ (b : ℂ) :
    (regularizedHGFunSeries 0 {b + 1}).radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_summable_norm _ fun r => ?_
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := NNReal.coe_nonneg r
  have hs1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hq_norm : ∀ n : ℕ, ‖regularizedHGFunSeries 0 {b + 1} n‖
      = ‖regularizedHGFunCoeff 0 {b + 1} n‖ := by
    intro n
    simp [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars, norm_smul]
  have hp_coeff_le : ∀ n : ℕ, ‖regularizedHGFunCoeff 0 {b} n‖
      ≤ ‖regularizedHGFunSeries 0 {b} n‖ := by
    intro n
    have h1 : (regularizedHGFunSeries 0 {b}) n (fun _ => (1 : ℂ))
        = regularizedHGFunCoeff 0 {b} n := by
      simp [regularizedHGFunSeries, smul_eq_mul]
    rw [← h1]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
    simp
  have hcoeff_norm : ∀ n : ℕ, ‖regularizedHGFunCoeff 0 {b + 1} n‖
      = (n + 1 : ℝ) * ‖regularizedHGFunCoeff 0 {b} (n + 1)‖ := by
    intro n
    rw [← regularizedHGFunCoeff_zero_singleton_succ b n, norm_mul]
    congr 1
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by norm_cast, RCLike.norm_natCast,
      Nat.cast_add_one]
  have hA : Summable fun n : ℕ => ‖regularizedHGFunSeries 0 {b} n‖ * ((r : ℝ) + 1) ^ n := by
    have h := (regularizedHGFunSeries 0 {b}).summable_norm_mul_pow (r := r + 1) (by
      rw [radius_regularizedHGFunSeries_zero_eq_top]
      exact ENNReal.coe_lt_top)
    simpa using h
  have hA' : Summable fun n : ℕ => ‖regularizedHGFunSeries 0 {b} (n + 1)‖ * ((r : ℝ) + 1) ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hA
  set C : ℝ := ∑' m : ℕ, ‖regularizedHGFunSeries 0 {b} (m + 1)‖ * ((r : ℝ) + 1) ^ (m + 1)
    with hC_def
  have hC : ∀ n : ℕ, ‖regularizedHGFunSeries 0 {b} (n + 1)‖ * ((r : ℝ) + 1) ^ (n + 1) ≤ C :=
    fun n => hA'.le_tsum n (fun m _ => by positivity)
  have ht : Summable fun n : ℕ =>
      (n + 1 : ℝ) * ((r : ℝ) / ((r : ℝ) + 1)) ^ n * (C / ((r : ℝ) + 1)) := by
    have ht1 : ‖(r : ℝ) / ((r : ℝ) + 1)‖ < 1 := by
      rw [norm_div, Real.norm_of_nonneg hr0, Real.norm_of_nonneg hs1.le]
      exact (div_lt_one hs1).2 (lt_add_one _)
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * ((r : ℝ) / ((r : ℝ) + 1)) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1 ht1
    have h2 : Summable fun n : ℕ => ((r : ℝ) / ((r : ℝ) + 1)) ^ n :=
      summable_geometric_of_norm_lt_one ht1
    refine ((h1.add h2).mul_right (C / ((r : ℝ) + 1))).congr fun n => ?_
    ring
  have hbound : ∀ n : ℕ, (n + 1 : ℝ) * ‖regularizedHGFunSeries 0 {b} (n + 1)‖ * (r : ℝ) ^ n
      ≤ (n + 1 : ℝ) * ((r : ℝ) / ((r : ℝ) + 1)) ^ n * (C / ((r : ℝ) + 1)) := by
    intro n
    have hs2 : ((r : ℝ) + 1) ^ (n + 1) ≠ 0 := pow_ne_zero _ hs1.ne'
    have he : (n + 1 : ℝ) * ‖regularizedHGFunSeries 0 {b} (n + 1)‖ * (r : ℝ) ^ n
        = (n + 1 : ℝ) * ((r : ℝ) / ((r : ℝ) + 1)) ^ n
          * (‖regularizedHGFunSeries 0 {b} (n + 1)‖ * ((r : ℝ) + 1) ^ (n + 1) / ((r : ℝ) + 1)) := by
      rw [div_pow]
      field_simp [hs2, hs1.ne']
      ring
    rw [he]
    have hnn2 : (0 : ℝ) ≤ (n + 1 : ℝ) * ((r : ℝ) / ((r : ℝ) + 1)) ^ n := by positivity
    exact mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hs1).2 (hC n)) hnn2
  have hkey : ∀ n : ℕ, ‖regularizedHGFunSeries 0 {b + 1} n‖ * (r : ℝ) ^ n
      ≤ (n + 1 : ℝ) * ‖regularizedHGFunSeries 0 {b} (n + 1)‖ * (r : ℝ) ^ n := by
    intro n
    rw [hq_norm n, hcoeff_norm n]
    have h1 := hp_coeff_le (n + 1)
    have hnn : (0 : ℝ) ≤ (n + 1 : ℝ) := by positivity
    have hnr : (0 : ℝ) ≤ (r : ℝ) ^ n := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hnn) hnr
  exact Summable.of_nonneg_of_le (fun n => by positivity) (fun n => (hkey n).trans (hbound n)) ht

/-- The derivative of the `(n + 1)`-th partial sum of the `₀F̃₁(; b; ·)` series is the `n`-th
partial sum of the `₀F̃₁(; b + 1; ·)` series. -/
theorem hasDerivAt_partialSum_regularizedHGFunSeries_zero_singleton (b : ℂ) (n : ℕ) (x : ℂ) :
    HasDerivAt (fun w => (regularizedHGFunSeries 0 {b}).partialSum (n + 1) w)
      ((regularizedHGFunSeries 0 {b + 1}).partialSum n x) x := by
  have hsum := HasDerivAt.sum (u := Finset.range (n + 1))
    (fun k (_ : k ∈ Finset.range (n + 1)) =>
      ((hasDerivAt_pow k x).const_mul (regularizedHGFunCoeff 0 {b} k)))
  have h1 : (fun w => (regularizedHGFunSeries 0 {b}).partialSum (n + 1) w)
      = ∑ k ∈ Finset.range (n + 1), fun w => regularizedHGFunCoeff 0 {b} k * w ^ k := by
    funext w
    rw [Finset.sum_apply]
    simp only [FormalMultilinearSeries.partialSum, regularizedHGFunSeries]
    apply Finset.sum_congr rfl
    intro k _
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have h2 : (regularizedHGFunSeries 0 {b + 1}).partialSum n x
      = ∑ k ∈ Finset.range (n + 1), regularizedHGFunCoeff 0 {b} k * ((k : ℂ) * x ^ (k - 1)) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel]
    simp only [FormalMultilinearSeries.partialSum, regularizedHGFunSeries]
    apply Finset.sum_congr rfl
    intro k _
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    calc regularizedHGFunCoeff 0 {b + 1} k * x ^ k
        = ((↑k + 1) * regularizedHGFunCoeff 0 {b} (k + 1)) * x ^ k := by
          rw [regularizedHGFunCoeff_zero_singleton_succ]
      _ = regularizedHGFunCoeff 0 {b} (k + 1) * ((↑k + 1) * x ^ k) := by ring
  rw [h1, h2]
  exact hsum

/-- The fundamental derivative identity for the regularized `₀F₁` function with a singleton
lower parameter: `d/dw ₀F̃₁(; b; w) = ₀F̃₁(; b + 1; w)`.  Proved by locally uniform
term-by-term differentiation of the defining power series. -/
theorem hasDerivAt_regularizedHGFun_zero_singleton (b : ℂ) (w : ℂ) :
    HasDerivAt (regularizedHGFun 0 {b}) (regularizedHGFun 0 {b + 1} w) w := by
  show HasDerivAt (regularizedHGFunSeries 0 {b}).sum ((regularizedHGFunSeries 0 {b + 1}).sum w) w
  have hr : (regularizedHGFunSeries 0 {b + 1}).radius = ⊤ :=
    radius_regularizedHGFunSeries_zero_singleton_succ b
  have hball := (regularizedHGFunSeries 0 {b + 1}).hasFPowerSeriesOnBall (by
    rw [hr]; exact ENNReal.zero_lt_top)
  have hUL : TendstoLocallyUniformlyOn
      (fun n y => (regularizedHGFunSeries 0 {b + 1}).partialSum n y)
      (regularizedHGFunSeries 0 {b + 1}).sum atTop (Set.univ : Set ℂ) := by
    have h := hball.tendstoLocallyUniformlyOn'
    rw [hr, Metric.eball_top_eq_univ] at h
    simpa only [sub_zero] using h
  refine hasDerivAt_of_tendstoLocallyUniformlyOn (isOpen_univ) (hUL)
    (f := fun n w => (regularizedHGFunSeries 0 {b}).partialSum (n + 1) w) ?_ ?_ (Set.mem_univ w)
  · exact Filter.Eventually.of_forall fun n x _ =>
      hasDerivAt_partialSum_regularizedHGFunSeries_zero_singleton b n x
  · intro x _
    have hx : x ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries 0 {b}).radius := by
      rw [radius_regularizedHGFunSeries_zero_eq_top, Metric.eball_top_eq_univ]
      exact Set.mem_univ x
    have h := ((regularizedHGFunSeries 0 {b}).hasSum hx).tendsto_sum_nat
    simpa [Function.comp_def, FormalMultilinearSeries.partialSum] using
      h.comp (Filter.tendsto_add_atTop_nat 1)

/-- The `₀F̃₁` three-term recurrence `w * ₀F̃₁(; b + 2; w) + b * ₀F̃₁(; b + 1; w) = ₀F̃₁(; b; w)`,
valid when `b` is not a nonpositive integer.  This is `Γ(s + 1) = s Γ(s)` at the level of
power series coefficients. -/
theorem regularizedHGFun_zero_singleton_recurrence (b : ℂ) (hb : ∀ n : ℕ, b + (n : ℂ) ≠ 0)
    (w : ℂ) :
    w * regularizedHGFun 0 {b + 2} w + b * regularizedHGFun 0 {b + 1} w
      = regularizedHGFun 0 {b} w := by
  have hb0 : b ≠ 0 := by
    have h := hb 0
    simpa using h
  have hs : ∀ n : ℕ, b + 1 + (n : ℂ) ≠ 0 := by
    intro n
    have h := hb (n + 1)
    push_cast at h
    rwa [show b + 1 + (n : ℂ) = b + (↑n + 1) by ring]
  have hcoeff : ∀ n : ℕ, regularizedHGFunCoeff 0 {b + 2} n
      + b * regularizedHGFunCoeff 0 {b + 1} (n + 1) = regularizedHGFunCoeff 0 {b} (n + 1) := by
    intro n
    have hfact : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hsucc : ((n : ℂ) + 1) ≠ 0 := by
      rw [show ((n : ℂ) + 1) = ((((n : ℝ)) + 1 : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_ne_zero.mpr (by positivity)
    simp only [regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
      Multiset.prod_singleton, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [show b + 2 + (n : ℂ) = (b + 1 + ↑n) + 1 by ring,
      show b + 1 + (↑n + 1) = (b + 1 + ↑n) + 1 by ring,
      show b + (↑n + 1) = b + 1 + ↑n by ring,
      Complex.Gamma_add_one (b + 1 + ↑n) (hs n)]
    by_cases hG : Complex.Gamma (b + 1 + (n : ℂ)) = 0
    · simp [hG]
    · field_simp [hG, hs n, hfact, hsucc]
      ring
  have h0 : b * regularizedHGFunCoeff 0 {b + 1} 0 = regularizedHGFunCoeff 0 {b} 0 := by
    simp only [regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
      Multiset.prod_singleton, Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, add_zero]
    rw [Complex.Gamma_add_one b hb0]
    by_cases hG : Complex.Gamma b = 0
    · simp [hG]
    · field_simp [hG, hb0]
  have hr1 : (regularizedHGFunSeries 0 {b + 1}).radius = ⊤ :=
    radius_regularizedHGFunSeries_zero_singleton_succ b
  have hr2 : (regularizedHGFunSeries 0 {b + 2}).radius = ⊤ := by
    rw [show b + 2 = b + 1 + 1 by ring]
    exact radius_regularizedHGFunSeries_zero_singleton_succ (b + 1)
  have hs_b : Summable fun n => regularizedHGFunCoeff 0 {b} n * w ^ n := by
    apply ((regularizedHGFunSeries 0 {b}).summable (x := w) (by
      rw [radius_regularizedHGFunSeries_zero_eq_top, Metric.eball_top_eq_univ]
      exact Set.mem_univ w)).congr
    intro n
    simp [regularizedHGFunSeries, smul_eq_mul]
    ring
  have hs_b1 : Summable fun n => regularizedHGFunCoeff 0 {b + 1} n * w ^ n := by
    apply ((regularizedHGFunSeries 0 {b + 1}).summable (x := w) (by
      rw [hr1, Metric.eball_top_eq_univ]; exact Set.mem_univ w)).congr
    intro n
    simp [regularizedHGFunSeries, smul_eq_mul]
    ring
  have hs_b2 : Summable fun n => regularizedHGFunCoeff 0 {b + 2} n * w ^ n := by
    apply ((regularizedHGFunSeries 0 {b + 2}).summable (x := w) (by
      rw [hr2, Metric.eball_top_eq_univ]; exact Set.mem_univ w)).congr
    intro n
    simp [regularizedHGFunSeries, smul_eq_mul]
    ring
  have hs1shift : Summable fun n => b * (regularizedHGFunCoeff 0 {b + 1} (n + 1) * w ^ (n + 1)) :=
    ((summable_nat_add_iff 1).2 hs_b1).mul_left b
  have hs2shift : Summable fun n => regularizedHGFunCoeff 0 {b + 2} n * w ^ (n + 1) := by
    refine (hs_b2.mul_right w).congr fun n => ?_
    rw [pow_succ']; ring
  rw [regularizedHGFun_zero_singleton_eq_tsum b, regularizedHGFun_zero_singleton_eq_tsum (b + 1),
    regularizedHGFun_zero_singleton_eq_tsum (b + 2), ← tsum_mul_left, ← tsum_mul_left]
  have hw2 : (∑' n, w * (regularizedHGFunCoeff 0 {b + 2} n * w ^ n))
      = ∑' n, regularizedHGFunCoeff 0 {b + 2} n * w ^ (n + 1) :=
    tsum_congr fun n => by rw [pow_succ']; ring
  rw [hw2]
  have hsplit0 : (∑' n, regularizedHGFunCoeff 0 {b} n * w ^ n)
      = regularizedHGFunCoeff 0 {b} 0 + ∑' n, regularizedHGFunCoeff 0 {b} (n + 1) * w ^ (n + 1) := by
    have h := tsum_eq_zero_add' (f := fun n => regularizedHGFunCoeff 0 {b} n * w ^ n)
      ((summable_nat_add_iff 1).2 hs_b)
    simpa using h
  have hsplit1 : (∑' n, b * (regularizedHGFunCoeff 0 {b + 1} n * w ^ n))
      = regularizedHGFunCoeff 0 {b} 0
        + ∑' n, b * (regularizedHGFunCoeff 0 {b + 1} (n + 1) * w ^ (n + 1)) := by
    have h := tsum_eq_zero_add' (f := fun n => b * (regularizedHGFunCoeff 0 {b + 1} n * w ^ n))
      hs1shift
    have h0' : b * (regularizedHGFunCoeff 0 {b + 1} 0 * w ^ 0) = regularizedHGFunCoeff 0 {b} 0 := by
      simp only [pow_zero, mul_one]
      exact h0
    rwa [h0'] at h
  rw [hsplit0, hsplit1, add_comm (∑' n, regularizedHGFunCoeff 0 {b + 2} n * w ^ (n + 1)) _,
    add_assoc, add_left_cancel_iff, ← Summable.tsum_add hs1shift hs2shift]
  apply tsum_congr
  intro n
  calc b * (regularizedHGFunCoeff 0 {b + 1} (n + 1) * w ^ (n + 1))
        + regularizedHGFunCoeff 0 {b + 2} n * w ^ (n + 1)
      = (b * regularizedHGFunCoeff 0 {b + 1} (n + 1)) * w ^ (n + 1)
        + regularizedHGFunCoeff 0 {b + 2} n * w ^ (n + 1) := by ring
    _ = (regularizedHGFunCoeff 0 {b + 2} n + b * regularizedHGFunCoeff 0 {b + 1} (n + 1))
        * w ^ (n + 1) := by ring
    _ = regularizedHGFunCoeff 0 {b} (n + 1) * w ^ (n + 1) := by rw [hcoeff n]

section AiryODE

/-- The derivative of `z ↦ z ^ 3 / 9`. -/
theorem hasDerivAt_cube_div_nine (z : ℂ) :
    HasDerivAt (fun z : ℂ => z ^ 3 / 9) (3 * z ^ 2 / 9) z := by
  convert (hasDerivAt_pow 3 z).div_const 9 using 1

theorem hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (b : ℂ) (z : ℂ) :
    HasDerivAt (fun z => regularizedHGFun 0 {b} (z ^ 3 / 9))
      (3 * z ^ 2 / 9 * regularizedHGFun 0 {b + 1} (z ^ 3 / 9)) z := by
  convert (hasDerivAt_regularizedHGFun_zero_singleton b (z ^ 3 / 9)).comp z
    (hasDerivAt_cube_div_nine z) using 1
  · rfl
  · ring

theorem deriv_regularizedHGFun_zero_singleton_comp_cube_div_nine (b : ℂ) :
    deriv (fun z => regularizedHGFun 0 {b} (z ^ 3 / 9))
      = fun z => 3 * z ^ 2 / 9 * regularizedHGFun 0 {b + 1} (z ^ 3 / 9) :=
  funext fun z => (hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine b z).deriv

theorem hasDerivAt_deriv_regularizedHGFun_zero_singleton_comp_cube_div_nine (b : ℂ)
    (hb : ∀ n : ℕ, b + (n : ℂ) ≠ 0) (z : ℂ) :
    HasDerivAt (deriv (fun z => regularizedHGFun 0 {b} (z ^ 3 / 9)))
      (z * regularizedHGFun 0 {b} (z ^ 3 / 9) +
        (2 / 3 - b) * z * regularizedHGFun 0 {b + 1} (z ^ 3 / 9)) z := by
  rw [deriv_regularizedHGFun_zero_singleton_comp_cube_div_nine b]
  have key := (((hasDerivAt_pow 2 z).const_mul 3).div_const 9).fun_mul
    (hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (b + 1) z)
  convert key using 1
  have hrec := regularizedHGFun_zero_singleton_recurrence b hb (z ^ 3 / 9)
  rw [show b + 1 + 1 = b + 2 by ring, ← hrec]
  ring

theorem two_thirds_add_nat_ne_zero (n : ℕ) : (2 / 3 : ℂ) + (n : ℂ) ≠ 0 := by
  rw [show (2 / 3 : ℂ) + (n : ℂ) = (((2 / 3 + n : ℝ)) : ℂ) by push_cast; ring]
  exact Complex.ofReal_ne_zero.mpr (by positivity)

theorem four_thirds_add_nat_ne_zero (n : ℕ) : (4 / 3 : ℂ) + (n : ℂ) ≠ 0 := by
  rw [show (4 / 3 : ℂ) + (n : ℂ) = (((4 / 3 + n : ℝ)) : ℂ) by push_cast; ring]
  exact Complex.ofReal_ne_zero.mpr (by positivity)

theorem hasDerivAt_deriv_u_two_thirds (z : ℂ) :
    HasDerivAt (deriv (fun z => regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)))
      (z * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)) z := by
  have h := hasDerivAt_deriv_regularizedHGFun_zero_singleton_comp_cube_div_nine (2 / 3 : ℂ)
    (fun n => two_thirds_add_nat_ne_zero n) z
  convert h using 1
  simp [sub_self]

theorem hasDerivAt_z_mul_four_thirds (z : ℂ) :
    HasDerivAt (fun z => z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))
      (regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) +
        z * (3 * z ^ 2 / 9 * regularizedHGFun 0 {(4 / 3 : ℂ) + 1} (z ^ 3 / 9))) z := by
  convert (hasDerivAt_id' (x := z)).fun_mul
    (hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (4 / 3 : ℂ) z) using 1
  ring

theorem deriv_z_mul_four_thirds :
    deriv (fun z => z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))
      = fun z => regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) +
          z * (3 * z ^ 2 / 9 * regularizedHGFun 0 {(4 / 3 : ℂ) + 1} (z ^ 3 / 9)) :=
  funext fun z => (hasDerivAt_z_mul_four_thirds z).deriv

theorem hasDerivAt_deriv_z_mul_four_thirds (z : ℂ) :
    HasDerivAt (deriv (fun z => z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)))
      (z * (z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))) z := by
  rw [deriv_z_mul_four_thirds]
  have key := (hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (4 / 3 : ℂ) z).fun_add
    ((hasDerivAt_id' (x := z)).fun_mul (((hasDerivAt_pow 2 z).const_mul 3 |>.div_const 9).fun_mul
      (hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine ((4 / 3 : ℂ) + 1) z)))
  convert key using 1
  have hrec := regularizedHGFun_zero_singleton_recurrence (4 / 3 : ℂ)
    (fun n => four_thirds_add_nat_ne_zero n) (z ^ 3 / 9)
  rw [show (4 / 3 : ℂ) + 1 + 1 = 4 / 3 + 2 by ring, ← hrec]
  ring


theorem airyAi_eq : airyAi = fun w => (3 : ℂ) ^ (-2 / 3 : ℂ)
      * regularizedHGFun 0 {(2 / 3 : ℂ)} (w ^ 3 / 9)
    - (3 : ℂ) ^ (-4 / 3 : ℂ) * (w * regularizedHGFun 0 {(4 / 3 : ℂ)} (w ^ 3 / 9)) := by
  funext w
  simp only [airyAi]
  ring

theorem airyBi_eq : airyBi = fun w => (3 : ℂ) ^ (-1 / 6 : ℂ)
      * regularizedHGFun 0 {(2 / 3 : ℂ)} (w ^ 3 / 9)
    + (3 : ℂ) ^ (-5 / 6 : ℂ) * (w * regularizedHGFun 0 {(4 / 3 : ℂ)} (w ^ 3 / 9)) := by
  funext w
  simp only [airyBi]
  ring

theorem deriv_airyAi :
    deriv airyAi = fun w => (3 : ℂ) ^ (-2 / 3 : ℂ)
        * deriv (fun z => regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)) w
      - (3 : ℂ) ^ (-4 / 3 : ℂ)
        * deriv (fun z => z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) w := by
  funext w
  rw [airyAi_eq]
  rw [deriv_fun_sub ((hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (2 / 3 : ℂ)
      w).differentiableAt.const_mul _)
    ((hasDerivAt_z_mul_four_thirds w).differentiableAt.const_mul _)]
  rw [deriv_const_mul _ (hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (2 / 3 : ℂ)
      w).differentiableAt,
    deriv_const_mul _ (hasDerivAt_z_mul_four_thirds w).differentiableAt]

theorem deriv_airyBi :
    deriv airyBi = fun w => (3 : ℂ) ^ (-1 / 6 : ℂ)
        * deriv (fun z => regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)) w
      + (3 : ℂ) ^ (-5 / 6 : ℂ)
        * deriv (fun z => z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) w := by
  funext w
  rw [airyBi_eq]
  rw [deriv_fun_add ((hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (2 / 3 : ℂ)
      w).differentiableAt.const_mul _)
    ((hasDerivAt_z_mul_four_thirds w).differentiableAt.const_mul _)]
  rw [deriv_const_mul _ (hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (2 / 3 : ℂ)
      w).differentiableAt,
    deriv_const_mul _ (hasDerivAt_z_mul_four_thirds w).differentiableAt]

theorem iteratedDeriv_two_airyAi (z : ℂ) : iteratedDeriv 2 airyAi z = z * airyAi z := by
  have hdu23 : deriv (deriv (fun z => regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9))) z
      = z * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) :=
    (hasDerivAt_deriv_u_two_thirds z).deriv
  have hds : deriv (deriv (fun z => z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))) z
      = z * (z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) :=
    (hasDerivAt_deriv_z_mul_four_thirds z).deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_airyAi]
  rw [deriv_fun_sub ((hasDerivAt_deriv_u_two_thirds z).differentiableAt.const_mul _)
    ((hasDerivAt_deriv_z_mul_four_thirds z).differentiableAt.const_mul _)]
  rw [deriv_const_mul _ (hasDerivAt_deriv_u_two_thirds z).differentiableAt,
    deriv_const_mul _ (hasDerivAt_deriv_z_mul_four_thirds z).differentiableAt, hdu23, hds]
  simp only [airyAi_eq]
  ring

theorem iteratedDeriv_two_airyBi (z : ℂ) : iteratedDeriv 2 airyBi z = z * airyBi z := by
  have hdu23 : deriv (deriv (fun z => regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9))) z
      = z * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) :=
    (hasDerivAt_deriv_u_two_thirds z).deriv
  have hds : deriv (deriv (fun z => z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))) z
      = z * (z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) :=
    (hasDerivAt_deriv_z_mul_four_thirds z).deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_airyBi]
  rw [deriv_fun_add ((hasDerivAt_deriv_u_two_thirds z).differentiableAt.const_mul _)
    ((hasDerivAt_deriv_z_mul_four_thirds z).differentiableAt.const_mul _)]
  rw [deriv_const_mul _ (hasDerivAt_deriv_u_two_thirds z).differentiableAt,
    deriv_const_mul _ (hasDerivAt_deriv_z_mul_four_thirds z).differentiableAt, hdu23, hds]
  simp only [airyBi_eq]
  ring


/-- The regularized `₀F₁` coefficient with a real (cast) lower parameter is real, hence
`star`-invariant. -/
theorem star_regularizedHGFunCoeff_zero_singleton_real (t : ℝ) (n : ℕ) :
    star (regularizedHGFunCoeff 0 {((t : ℝ) : ℂ)} n)
      = regularizedHGFunCoeff 0 {((t : ℝ) : ℂ)} n := by
  have hG : Complex.Gamma (((t : ℝ) : ℂ) + (n : ℂ)) = ((Real.Gamma (t + n) : ℝ) : ℂ) := by
    rw [show ((t : ℝ) : ℂ) + (n : ℂ) = ((t + n : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
  have e : regularizedHGFunCoeff 0 {((t : ℝ) : ℂ)} n
      = ((1 / (n ! * Real.Gamma (t + n)) : ℝ) : ℂ) := by
    simp only [regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero,
      Multiset.map_singleton, Multiset.prod_singleton]
    rw [hG]
    push_cast
    ring
  rw [e, Complex.star_def, Complex.conj_ofReal]

/-- `₀F̃₁(; b; ·)` with a real parameter `b` commutes with complex conjugation. -/
theorem regularizedHGFun_zero_singleton_real_conj (t : ℝ) (w : ℂ) :
    star (regularizedHGFun 0 {((t : ℝ) : ℂ)} w) = regularizedHGFun 0 {((t : ℝ) : ℂ)} (star w) := by
  rw [regularizedHGFun_zero_singleton_eq_tsum, regularizedHGFun_zero_singleton_eq_tsum, tsum_star]
  apply tsum_congr
  intro n
  rw [star_mul', star_pow, star_regularizedHGFunCoeff_zero_singleton_real]

theorem airyAi_conj (z : ℂ) : airyAi (star z) = star (airyAi z) := by
  have hF23 : ∀ w : ℂ, star (regularizedHGFun 0 {(2 / 3 : ℂ)} w)
      = regularizedHGFun 0 {(2 / 3 : ℂ)} (star w) := by
    intro w
    have h := regularizedHGFun_zero_singleton_real_conj (2 / 3 : ℝ) w
    rwa [show ((2 / 3 : ℝ) : ℂ) = (2 / 3 : ℂ) by norm_num] at h
  have hF43 : ∀ w : ℂ, star (regularizedHGFun 0 {(4 / 3 : ℂ)} w)
      = regularizedHGFun 0 {(4 / 3 : ℂ)} (star w) := by
    intro w
    have h := regularizedHGFun_zero_singleton_real_conj (4 / 3 : ℝ) w
    rwa [show ((4 / 3 : ℝ) : ℂ) = (4 / 3 : ℂ) by norm_num] at h
  have hc23 : ((3 : ℂ) ^ (-2 / 3 : ℂ)) = Complex.ofReal ((3 : ℝ) ^ (-2 / 3 : ℝ)) := by
    rw [show (-2 / 3 : ℂ) = ((-2 / 3 : ℝ) : ℂ) by norm_num,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3) (-2 / 3)]
  have hc43 : ((3 : ℂ) ^ (-4 / 3 : ℂ)) = Complex.ofReal ((3 : ℝ) ^ (-4 / 3 : ℝ)) := by
    rw [show (-4 / 3 : ℂ) = ((-4 / 3 : ℝ) : ℂ) by norm_num,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3) (-4 / 3)]
  have hz39 : star (z ^ 3 / 9) = (star z) ^ 3 / 9 := by
    rw [star_div₀, star_pow, star_ofNat]
  show (3 : ℂ) ^ (-2 / 3 : ℂ) * regularizedHGFun 0 {(2 / 3 : ℂ)} ((star z) ^ 3 / 9)
      - (3 : ℂ) ^ (-4 / 3 : ℂ) * (star z) * regularizedHGFun 0 {(4 / 3 : ℂ)} ((star z) ^ 3 / 9)
    = star ((3 : ℂ) ^ (-2 / 3 : ℂ) * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)
      - (3 : ℂ) ^ (-4 / 3 : ℂ) * z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))
  rw [hc23, hc43, star_sub, star_mul', star_mul', star_mul', hF23, hF43, hz39, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_ofReal]

theorem airyBi_conj (z : ℂ) : airyBi (star z) = star (airyBi z) := by
  have hF23 : ∀ w : ℂ, star (regularizedHGFun 0 {(2 / 3 : ℂ)} w)
      = regularizedHGFun 0 {(2 / 3 : ℂ)} (star w) := by
    intro w
    have h := regularizedHGFun_zero_singleton_real_conj (2 / 3 : ℝ) w
    rwa [show ((2 / 3 : ℝ) : ℂ) = (2 / 3 : ℂ) by norm_num] at h
  have hF43 : ∀ w : ℂ, star (regularizedHGFun 0 {(4 / 3 : ℂ)} w)
      = regularizedHGFun 0 {(4 / 3 : ℂ)} (star w) := by
    intro w
    have h := regularizedHGFun_zero_singleton_real_conj (4 / 3 : ℝ) w
    rwa [show ((4 / 3 : ℝ) : ℂ) = (4 / 3 : ℂ) by norm_num] at h
  have hc16 : ((3 : ℂ) ^ (-1 / 6 : ℂ)) = Complex.ofReal ((3 : ℝ) ^ (-1 / 6 : ℝ)) := by
    rw [show (-1 / 6 : ℂ) = ((-1 / 6 : ℝ) : ℂ) by norm_num,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3) (-1 / 6)]
  have hc56 : ((3 : ℂ) ^ (-5 / 6 : ℂ)) = Complex.ofReal ((3 : ℝ) ^ (-5 / 6 : ℝ)) := by
    rw [show (-5 / 6 : ℂ) = ((-5 / 6 : ℝ) : ℂ) by norm_num,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3) (-5 / 6)]
  have hz39 : star (z ^ 3 / 9) = (star z) ^ 3 / 9 := by
    rw [star_div₀, star_pow, star_ofNat]
  show (3 : ℂ) ^ (-1 / 6 : ℂ) * regularizedHGFun 0 {(2 / 3 : ℂ)} ((star z) ^ 3 / 9)
      + (3 : ℂ) ^ (-5 / 6 : ℂ) * (star z) * regularizedHGFun 0 {(4 / 3 : ℂ)} ((star z) ^ 3 / 9)
    = star ((3 : ℂ) ^ (-1 / 6 : ℂ) * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)
      + (3 : ℂ) ^ (-5 / 6 : ℂ) * z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9))
  rw [hc16, hc56, star_add, star_mul', star_mul', star_mul', hF23, hF43, hz39, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_ofReal]

end AiryODE

end Complex
