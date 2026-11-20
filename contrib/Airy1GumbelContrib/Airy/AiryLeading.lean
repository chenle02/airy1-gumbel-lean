/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryIdentity
import Airy1GumbelContrib.Gaussian.MillsRatio

/-! # Exact leading asymptotics of the Airy function and its derivative at `+∞`

This file establishes the classical exact leading asymptotics

  `Ai(x) ~ (1/(2√π)) x^{-1/4} e^{-(2/3) x^{3/2}}`,   `Ai'(x) ~ -(1/(2√π)) x^{1/4} e^{-(2/3) x^{3/2}}`,

together with the tail-integral version

  `∫_A^∞ Ai(u) du ~ (1/(2√π)) A^{-3/4} e^{-(2/3) A^{3/2}}`,

via the Schläfli integral `schlaefliK13 z = ∫₀^∞ e^{-z cosh t} cosh(t/3) dt` and Laplace's
method.  From these the paper's constants `κ = 4√2/3` and `C* = 2^{1/4}/√π` become
derivable.

## Method

After factoring out `e^{-z}` and substituting `t = u/√z`, the Schläfli integral reads

  `K(z) = e^{-z} z^{-1/2} ∫₀^∞ e^{-z(cosh(u/√z) - 1)} cosh(u/(3√z)) du`.

Since `cosh s ≥ 1 + s²/2` with quadratic gap `cosh s - 1 - s²/2 ≤ (s²/2)(cosh s - 1)`
(`cosh_sub_one_sub_half_sq_le`), the rescaled integrand converges pointwise to `e^{-u²/2}`
and is dominated by `e^{1/9} e^{-u²/4}`; dominated convergence gives

  `schlaefliK13 z ~ √(π/(2z)) e^{-z}`   (`schlaefliK13_isEquivalent`).

A master lemma (`schlaefli_master_isEquivalent`) packages the same argument for the
weighted integrands `w(z,t) e^{-z cosh t} cosh(t/3)` with `w z (t/√z) → 1`; with
`w = cosh t` it yields the asymptotics of the derivative integral.  The Airy asymptotics
then follow from the Airy–Bessel identity `Ai(x) = (1/π) √(x/3) K((2/3) x^{3/2})`
(`airyAiReal_eq_airyBesselY_div_pi`), the derivative asymptotics from the explicit
derivative formula `airyBesselY1`, and the tail integral from a two-sided comparison
against the antiderivative of `u^{-1/4}(1 + (3/4) u^{-3/2}) e^{-(2/3) u^{3/2}}`.

## Main results

* `schlaefliK13_isEquivalent`: `K(z) ~ √(π/(2z)) e^{-z}`.
* `deriv_schlaefliK13`, `schlaefliK13_deriv_isEquivalent`: the derivative formula and
  `-K'(z) ~ √(π/(2z)) e^{-z}`.
* `airyAiReal_isEquivalent`: `Ai(x) ~ (1/(2√π)) x^{-1/4} e^{-(2/3) x^{3/2}}`.
* `deriv_airyAiReal_isEquivalent`: `Ai'(x) ~ -(1/(2√π)) x^{1/4} e^{-(2/3) x^{3/2}}`.
* `integral_airyAiReal_isEquivalent`: `∫_A^∞ Ai ~ (1/(2√π)) A^{-3/4} e^{-(2/3) A^{3/2}}`.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Asymptotics Topology

section AiryLeading

/-- The rescaled Schläfli integrand after factoring out `e^{-z}` and substituting
`t = u / √z`: `F_z(u) = e^{-z (cosh (u/√z) - 1)} cosh (u/(3√z))`. -/
noncomputable def airyLeadF (z u : ℝ) : ℝ :=
  Real.exp (-z * (Real.cosh (u / Real.sqrt z) - 1)) * Real.cosh (u / Real.sqrt z / 3)

/-- `airyLeadF z` is continuous in `u` for every `z`. -/
theorem continuous_airyLeadF (z : ℝ) : Continuous fun u => airyLeadF z u := by
  unfold airyLeadF
  fun_prop

/-- **The quadratic-gap bound for `cosh`**: `cosh s - 1 - s²/2 ≤ (s²/2)(cosh s - 1)`.
Termwise comparison of the power series: for `n ≥ 2`,
`s^{2n}/(2n)! ≤ (s²/2) · s^{2n-2}/(2n-2)!` since `(2n)! = (2n)(2n-1)·(2n-2)! ≥ 2·(2n-2)!`. -/
theorem cosh_sub_one_sub_half_sq_le (s : ℝ) :
    Real.cosh s - 1 - s ^ 2 / 2 ≤ (s ^ 2 / 2) * (Real.cosh s - 1) := by
  have hs : Summable (fun n : ℕ => s ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) :=
    (Real.hasSum_cosh s).summable
  have hs1 : Summable (fun i : ℕ => s ^ (2 * (i + 1)) / (Nat.factorial (2 * (i + 1)) : ℝ)) :=
    (summable_nat_add_iff 1).2 hs
  have hs2 : Summable (fun i : ℕ => s ^ (2 * (i + 2)) / (Nat.factorial (2 * (i + 2)) : ℝ)) :=
    (summable_nat_add_iff 2).2 hs
  have hpt : ∀ i : ℕ, s ^ (2 * (i + 2)) / (Nat.factorial (2 * (i + 2)) : ℝ)
      ≤ (s ^ 2 / 2) * (s ^ (2 * (i + 1)) / (Nat.factorial (2 * (i + 1)) : ℝ)) := by
    intro i
    have hfact : (Nat.factorial (2 * (i + 2)) : ℝ)
        = ((2 * i + 4) * (2 * i + 3) : ℝ) * (Nat.factorial (2 * (i + 1)) : ℝ) := by
      rw [show 2 * (i + 2) = (2 * i + 3) + 1 from by ring, Nat.factorial_succ,
        show 2 * i + 3 = (2 * i + 2) + 1 from by ring, Nat.factorial_succ,
        show 2 * i + 2 = 2 * (i + 1) from by ring]
      push_cast
      ring
    have hpow : s ^ (2 * (i + 2)) = s ^ 2 * s ^ (2 * (i + 1)) := by
      rw [show 2 * (i + 2) = 2 + 2 * (i + 1) from by ring, pow_add]
    have hC : (2:ℝ) ≤ ((2 * i + 4) * (2 * i + 3) : ℝ) := by
      have h1 : (4:ℕ) ≤ 2 * i + 4 := by omega
      have h2 : (3:ℕ) ≤ 2 * i + 3 := by omega
      have h3 := Nat.mul_le_mul h1 h2
      calc (2:ℝ) ≤ (12:ℕ) := by norm_num
        _ ≤ (2 * i + 4) * (2 * i + 3) := by exact_mod_cast h3
    have hC0 : (0:ℝ) < ((2 * i + 4) * (2 * i + 3) : ℝ) := by linarith [hC]
    have hB : (0:ℝ) < (Nat.factorial (2 * (i + 1)) : ℝ) := by positivity
    rw [hpow, hfact,
      show (s ^ 2 / 2) * (s ^ (2 * (i + 1)) / (Nat.factorial (2 * (i + 1)) : ℝ))
        = (s ^ 2 / 2 * s ^ (2 * (i + 1))) / (Nat.factorial (2 * (i + 1)) : ℝ) from
        (mul_div_assoc _ _ _).symm,
      div_le_div_iff₀ (mul_pos hC0 hB) hB]
    calc s ^ 2 * s ^ (2 * (i + 1)) * (Nat.factorial (2 * (i + 1)) : ℝ)
        = (s ^ 2 / 2 * s ^ (2 * (i + 1))) * (2 * (Nat.factorial (2 * (i + 1)) : ℝ)) := by ring
      _ ≤ (s ^ 2 / 2 * s ^ (2 * (i + 1)))
          * (((2 * i + 4) * (2 * i + 3) : ℝ) * (Nat.factorial (2 * (i + 1)) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (by positivity : (0:ℝ) ≤ s ^ 2 / 2)
              (by rw [pow_mul]; positivity : (0:ℝ) ≤ s ^ (2 * (i + 1))))
          exact mul_le_mul_of_nonneg_right hC hB.le
  have h01 : (s ^ (2 * 0) / (Nat.factorial (2 * 0) : ℝ)
      + s ^ (2 * 1) / (Nat.factorial (2 * 1) : ℝ)) = 1 + s ^ 2 / 2 := by
    norm_num
  have h0 : (s ^ (2 * 0) / (Nat.factorial (2 * 0) : ℝ)) = 1 := by
    norm_num
  calc Real.cosh s - 1 - s ^ 2 / 2
      = ∑' i : ℕ, s ^ (2 * (i + 2)) / (Nat.factorial (2 * (i + 2)) : ℝ) := by
        rw [Real.cosh_eq_tsum, ← hs.sum_add_tsum_nat_add 2,
          show Finset.range 2 = {0, 1} from by decide,
          Finset.sum_insert (by norm_num), Finset.sum_singleton, h01]
        ring
    _ ≤ ∑' i : ℕ, (s ^ 2 / 2) * (s ^ (2 * (i + 1)) / (Nat.factorial (2 * (i + 1)) : ℝ)) :=
        hs2.tsum_le_tsum hpt (hs1.mul_left _)
    _ = (s ^ 2 / 2) * ∑' i : ℕ, s ^ (2 * (i + 1)) / (Nat.factorial (2 * (i + 1)) : ℝ) :=
        tsum_mul_left
    _ = (s ^ 2 / 2) * (Real.cosh s - 1) := by
        rw [Real.cosh_eq_tsum, ← hs.sum_add_tsum_nat_add 1,
          show Finset.range 1 = {0} from by decide, Finset.sum_singleton, h0]
        ring

/-- `u / √z → 0` as `z → ∞`. -/
theorem tendsto_div_sqrt_atTop (u : ℝ) :
    Tendsto (fun z : ℝ => u / Real.sqrt z) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul u
  rw [mul_zero] at h
  refine h.congr' (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, div_eq_mul_inv]

/-- For `0 < z` and `0 ≤ u`: `z * (cosh (u/√z) - 1) ≥ u²/2` (from `cosh s ≥ 1 + s²/2`). -/
theorem mul_cosh_div_sqrt_sub_one_ge {z u : ℝ} (hz : 0 < z) (_hu : 0 ≤ u) :
    u ^ 2 / 2 ≤ z * (Real.cosh (u / Real.sqrt z) - 1) := by
  have h := one_add_sq_div_two_le_cosh (u / Real.sqrt z)
  have h2 : z * ((u / Real.sqrt z) ^ 2 / 2) = u ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt hz.le]
    field_simp [hz.ne']
  calc u ^ 2 / 2 = z * ((u / Real.sqrt z) ^ 2 / 2) := h2.symm
    _ ≤ z * (Real.cosh (u / Real.sqrt z) - 1) :=
        mul_le_mul_of_nonneg_left (by linarith [h]) hz.le

/-- `z * (cosh (u/√z) - 1) → u²/2` as `z → ∞` (squeeze between `u²/2` and
`u²/2 + (u²/2)(cosh (u/√z) - 1)` via `cosh_sub_one_sub_half_sq_le`). -/
theorem tendsto_mul_cosh_div_sqrt_sub_one {u : ℝ} (hu : 0 < u) :
    Tendsto (fun z : ℝ => z * (Real.cosh (u / Real.sqrt z) - 1)) atTop (𝓝 (u ^ 2 / 2)) := by
  have h0 := tendsto_div_sqrt_atTop u
  have hcosh : Tendsto (fun z : ℝ => Real.cosh (u / Real.sqrt z)) atTop (𝓝 1) := by
    have h := (Real.continuous_cosh.tendsto 0).comp h0
    rwa [Real.cosh_zero] at h
  have hup : Tendsto (fun z : ℝ => u ^ 2 / 2 + (u ^ 2 / 2) * (Real.cosh (u / Real.sqrt z) - 1))
      atTop (𝓝 (u ^ 2 / 2)) := by
    have h : Tendsto (fun z : ℝ => u ^ 2 / 2 + (u ^ 2 / 2) * (Real.cosh (u / Real.sqrt z) - 1))
        atTop (𝓝 (u ^ 2 / 2 + (u ^ 2 / 2) * (1 - 1))) :=
      (tendsto_const_nhds (x := u ^ 2 / 2)).add
        ((tendsto_const_nhds (x := u ^ 2 / 2)).mul (hcosh.sub_const 1))
    rwa [sub_self, mul_zero, add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with z hz
    exact mul_cosh_div_sqrt_sub_one_ge hz hu.le
  · filter_upwards [eventually_gt_atTop 0] with z hz
    have h := cosh_sub_one_sub_half_sq_le (u / Real.sqrt z)
    have h2 : z * ((u / Real.sqrt z) ^ 2 / 2) = u ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt hz.le]
      field_simp [hz.ne']
    have h3 := mul_le_mul_of_nonneg_left h hz.le
    rw [mul_sub, h2] at h3
    have h4 : z * ((u / Real.sqrt z) ^ 2 / 2 * (Real.cosh (u / Real.sqrt z) - 1))
        = (u ^ 2 / 2) * (Real.cosh (u / Real.sqrt z) - 1) := by
      rw [← mul_assoc, h2]
    rw [h4] at h3
    linarith [h3]

/-- **Dominated convergence for the rescaled Schläfli family**: if `W z u` is continuous
in `u`, nonnegative on `[0, ∞)`, bounded by `e^{C u}` for `z ≥ 1`, and converges pointwise
to `1` as `z → ∞`, then `∫₀^∞ W z · airyLeadF z → ∫₀^∞ e^{-u²/2} du`. -/
theorem tendsto_integral_airyLeadF_mul (W : ℝ → ℝ → ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hW_cont : ∀ z, Continuous fun u => W z u)
    (hW_nn : ∀ z u, 0 ≤ u → 0 ≤ W z u)
    (hW_bound : ∀ z, 1 ≤ z → ∀ u, 0 ≤ u → W z u ≤ Real.exp (C * u))
    (hW_lim : ∀ u, 0 < u → Tendsto (fun z => W z u) atTop (𝓝 1)) :
    Tendsto (fun z => ∫ u in Set.Ioi 0, W z u * airyLeadF z u) atTop
      (𝓝 (∫ u in Set.Ioi 0, Real.exp (-(1/2) * u ^ 2))) := by
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun u => Real.exp ((C + 1/3) ^ 2) * Real.exp (-(1/4) * u ^ 2)) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun z =>
      ((hW_cont z).mul (continuous_airyLeadF z)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0:ℝ) ≤ u := hu.le
    have hz0 : (0:ℝ) < z := by linarith
    have h1 : Real.exp (-z * (Real.cosh (u / Real.sqrt z) - 1)) ≤ Real.exp (-(u ^ 2 / 2)) := by
      apply Real.exp_le_exp.2
      rw [neg_mul]
      exact neg_le_neg (mul_cosh_div_sqrt_sub_one_ge hz0 hu0)
    have hdiv : u / Real.sqrt z ≤ u := by
      calc u / Real.sqrt z ≤ u / 1 :=
            div_le_div_of_nonneg_left hu0 zero_lt_one (Real.one_le_sqrt.2 hz)
        _ = u := div_one u
    have h2 : Real.cosh (u / Real.sqrt z / 3) ≤ Real.exp (u / 3) := by
      calc Real.cosh (u / Real.sqrt z / 3)
          ≤ Real.exp |u / Real.sqrt z / 3| := cosh_le_exp_abs _
        _ = Real.exp (u / Real.sqrt z / 3) := by
            congr 1
            exact abs_of_nonneg (by positivity)
        _ ≤ Real.exp (u / 3) :=
            Real.exp_le_exp.2 ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 3)).2 hdiv)
    have hnn : 0 ≤ W z u * airyLeadF z u :=
      mul_nonneg (hW_nn z u hu0) (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)
    rw [Real.norm_of_nonneg hnn]
    calc W z u * airyLeadF z u
        ≤ Real.exp (C * u) * (Real.exp (-(u ^ 2 / 2)) * Real.exp (u / 3)) := by
          apply mul_le_mul (hW_bound z hz u hu0) _ _
            (Real.exp_pos _).le
          · exact mul_le_mul h1 h2 (Real.cosh_pos _).le (Real.exp_pos _).le
          · exact mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
      _ = Real.exp (C * u + (-(u ^ 2 / 2) + u / 3)) := by
          rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp ((C + 1/3) ^ 2) * Real.exp (-(1/4) * u ^ 2) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          have h4 : (C + 1/3) * u ≤ u ^ 2 / 4 + (C + 1/3) ^ 2 := by
            have h5 := sq_nonneg (u / 2 - (C + 1/3))
            nlinarith
          nlinarith
  · exact ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).const_mul _).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0:ℝ) < u := hu
    have h1 := tendsto_mul_cosh_div_sqrt_sub_one hu0
    have h2 : Tendsto (fun z : ℝ => Real.exp (-(z * (Real.cosh (u / Real.sqrt z) - 1))))
        atTop (𝓝 (Real.exp (-(1/2) * u ^ 2))) := by
      have h := (Real.continuous_exp.tendsto _).comp h1.neg
      rwa [show -(u ^ 2 / 2) = -(1/2) * u ^ 2 from by ring] at h
    have h3 : Tendsto (fun z : ℝ => Real.cosh (u / Real.sqrt z / 3)) atTop (𝓝 1) := by
      have h0 := (tendsto_div_sqrt_atTop u).div_const 3
      rw [zero_div] at h0
      have h := (Real.continuous_cosh.tendsto 0).comp h0
      rwa [Real.cosh_zero] at h
    have h4 := (hW_lim u hu0).mul (h2.mul h3)
    rw [one_mul, mul_one] at h4
    refine h4.congr' (Eventually.of_forall fun z => ?_)
    show W z u * (Real.exp (-(z * (Real.cosh (u / Real.sqrt z) - 1))) * Real.cosh (u / Real.sqrt z / 3))
      = W z u * airyLeadF z u
    unfold airyLeadF
    rw [neg_mul]

/-- The normalized half-line Gaussian integral: `√(2/π) ∫₀^∞ e^{-u²/2} du = 1`. -/
theorem sqrt_two_div_pi_mul_integral_exp_neg_half_sq :
    Real.sqrt (2 / Real.pi) * ∫ u in Set.Ioi 0, Real.exp (-(1/2) * u ^ 2) = 1 := by
  rw [integral_gaussian_Ioi, show Real.pi / (1/2 : ℝ) = 2 * Real.pi from by field_simp,
    ← mul_div_assoc, ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 / Real.pi),
    show (2 / Real.pi) * (2 * Real.pi) = (2:ℝ) ^ 2 from by field_simp [Real.pi_ne_zero],
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- **Master Laplace lemma**: for a weight `w z t` that is continuous in `t`, nonnegative
on `[0, ∞)`, bounded by `e^{C t}` for `z ≥ 1`, and satisfies `w z (t/√z) → 1` as `z → ∞`,
the weighted Schläfli integral has the exact leading asymptotics
`∫₀^∞ w(z,t) e^{-z cosh t} cosh(t/3) dt ~ √(π/(2z)) e^{-z}`. -/
theorem schlaefli_master_isEquivalent (w : ℝ → ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hw_cont : ∀ z, Continuous fun t => w z t)
    (hw_nn : ∀ z t, 0 ≤ t → 0 ≤ w z t)
    (hw_bound : ∀ z, 1 ≤ z → ∀ t, 0 ≤ t → w z t ≤ Real.exp (C * t))
    (hw_lim : ∀ t, 0 < t → Tendsto (fun z => w z (t / Real.sqrt z)) atTop (𝓝 1)) :
    (fun z => ∫ t in Set.Ioi 0, w z t * (Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)))
      ~[atTop] fun z => Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z) := by
  have hDCT := tendsto_integral_airyLeadF_mul (fun z u => w z (u / Real.sqrt z)) hC
    (fun z => (hw_cont z).comp (continuous_id.div_const _))
    (fun z u hu => hw_nn z _ (div_nonneg hu (Real.sqrt_nonneg _)))
    (fun z hz u hu => (hw_bound z hz _ (div_nonneg hu (Real.sqrt_nonneg _))).trans
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
        (by
          calc u / Real.sqrt z ≤ u / 1 :=
                div_le_div_of_nonneg_left hu zero_lt_one (Real.one_le_sqrt.2 hz)
            _ = u := div_one u)
        hC)))
    hw_lim
  have hne : ∀ᶠ z in atTop, (fun z => Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z)) z ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with z hz
    positivity
  rw [isEquivalent_iff_tendsto_one hne]
  have hlim : Tendsto (fun z => Real.sqrt (2 / Real.pi) *
      ∫ u in Set.Ioi 0, w z (u / Real.sqrt z) * airyLeadF z u) atTop (𝓝 1) := by
    have h := hDCT.const_mul (Real.sqrt (2 / Real.pi))
    rwa [sqrt_two_div_pi_mul_integral_exp_neg_half_sq] at h
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with z hz
  have hzsq : (0:ℝ) < Real.sqrt z := Real.sqrt_pos.2 hz
  have hE : ∀ t : ℝ, Real.exp (-z * Real.cosh t)
      = Real.exp (-z) * Real.exp (-z * (Real.cosh t - 1)) := by
    intro t
    rw [← Real.exp_add]
    congr 1
    ring
  have hI1 : (∫ t in Set.Ioi 0, w z t * (Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)))
      = Real.exp (-z) * ∫ t in Set.Ioi 0, w z t *
        (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    show w z t * (Real.exp (-z * Real.cosh t) * Real.cosh (t / 3))
      = Real.exp (-z) * (w z t * (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)))
    rw [hE t]
    ring
  have hconv : (∫ u in Set.Ioi 0, w z (u / Real.sqrt z) * airyLeadF z u)
      = (∫ u in Set.Ioi 0, w z ((Real.sqrt z)⁻¹ * u) *
        (Real.exp (-z * (Real.cosh ((Real.sqrt z)⁻¹ * u) - 1)) *
          Real.cosh ((Real.sqrt z)⁻¹ * u / 3))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    show w z (u / Real.sqrt z) * (Real.exp (-z * (Real.cosh (u / Real.sqrt z) - 1)) *
        Real.cosh (u / Real.sqrt z / 3))
      = w z ((Real.sqrt z)⁻¹ * u) * (Real.exp (-z * (Real.cosh ((Real.sqrt z)⁻¹ * u) - 1)) *
        Real.cosh ((Real.sqrt z)⁻¹ * u / 3))
    rw [show u / Real.sqrt z = (Real.sqrt z)⁻¹ * u from by rw [div_eq_mul_inv, mul_comm]]
  have hsub : (∫ u in Set.Ioi 0, w z ((Real.sqrt z)⁻¹ * u) *
        (Real.exp (-z * (Real.cosh ((Real.sqrt z)⁻¹ * u) - 1)) *
          Real.cosh ((Real.sqrt z)⁻¹ * u / 3)))
      = Real.sqrt z * ∫ t in Set.Ioi 0, w z t *
        (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)) := by
    have h := integral_comp_mul_left_Ioi
      (fun t => w z t * (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)))
      (0 : ℝ) (b := (Real.sqrt z)⁻¹) (inv_pos.2 hzsq)
    simpa only [inv_inv, mul_zero, smul_eq_mul] using h
  show Real.sqrt (2 / Real.pi) * ∫ u in Set.Ioi 0, w z (u / Real.sqrt z) * airyLeadF z u
    = (∫ t in Set.Ioi 0, w z t * (Real.exp (-z * Real.cosh t) * Real.cosh (t / 3))) /
      (Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z))
  rw [hconv, hsub, hI1]
  set I := ∫ t in Set.Ioi 0, w z t * (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3))
    with hI
  have hsp : (0:ℝ) < Real.sqrt (Real.pi / (2 * z)) := Real.sqrt_pos.2 (by positivity)
  have hee : Real.exp (-z) ≠ 0 := (Real.exp_pos _).ne'
  rw [show Real.sqrt (2 / Real.pi) * (Real.sqrt z * I)
      = I * (Real.sqrt (2 / Real.pi) * Real.sqrt z) from by ring,
    mul_comm (Real.sqrt (Real.pi / (2 * z))) (Real.exp (-z)), mul_div_mul_left _ _ hee]
  rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 / Real.pi)]
  rw [show (2 / Real.pi) * z = 2 * z / Real.pi from by ring]
  rw [eq_div_iff hsp.ne', mul_assoc,
    ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * z / Real.pi),
    show (2 * z / Real.pi) * (Real.pi / (2 * z)) = 1 from by
      field_simp [Real.pi_ne_zero, hz.ne'],
    Real.sqrt_one, mul_one]

/-- **The exact leading asymptotics of the Schläfli `K_{1/3}` integral**:
`schlaefliK13 z ~ √(π/(2z)) e^{-z}` as `z → ∞` (Laplace's method). -/
theorem schlaefliK13_isEquivalent :
    schlaefliK13 ~[atTop] fun z => Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z) := by
  have h := schlaefli_master_isEquivalent (fun _ _ => 1) zero_le_one
    (fun _ => continuous_const) (fun _ _ _ => zero_le_one)
    (fun z hz t ht => by
      rw [one_mul]
      exact Real.one_le_exp_iff.2 ht)
    (fun t _ => tendsto_const_nhds)
  refine h.congr_left (Eventually.of_forall fun z => ?_)
  unfold schlaefliK13
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [one_mul]

/-- **D2a: the derivative of the Schläfli integral**: for `0 < z`,
`K'(z) = -∫₀^∞ cosh t · e^{-z cosh t} cosh(t/3) dt` (reformulation of
`hasDerivAt_schlaefliK13` from `Airy/AiryBessel.lean`). -/
theorem deriv_schlaefliK13 {z : ℝ} (hz : 0 < z) :
    HasDerivAt schlaefliK13
      (-(∫ t in Set.Ioi 0, Real.cosh t * Real.exp (-z * Real.cosh t) * Real.cosh (t / 3))) z := by
  convert (hasDerivAt_schlaefliK13 hz).2 using 1
  rw [← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  ring

/-- **D2b: the exact leading asymptotics of the derivative integral**:
`-K'(z) = ∫₀^∞ cosh t · e^{-z cosh t} cosh(t/3) dt ~ √(π/(2z)) e^{-z}` as `z → ∞`
(the master lemma with weight `w z t = cosh t`, which is `1 + O(t²)` near the saddle). -/
theorem schlaefliK13_deriv_isEquivalent :
    (fun z => ∫ t in Set.Ioi 0, Real.cosh t * Real.exp (-z * Real.cosh t) * Real.cosh (t / 3))
      ~[atTop] fun z => Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z) := by
  have h := schlaefli_master_isEquivalent (fun _ t => Real.cosh t) zero_le_one
    (fun _ => Real.continuous_cosh) (fun _ t _ => (Real.cosh_pos t).le)
    (fun z hz t ht => by
      rw [one_mul]
      exact (cosh_le_exp_abs t).trans_eq (by rw [abs_of_nonneg ht]))
    (fun t _ => by
      show Tendsto (fun z => Real.cosh (t / Real.sqrt z)) atTop (𝓝 1)
      have h0 := tendsto_div_sqrt_atTop t
      have h := (Real.continuous_cosh.tendsto 0).comp h0
      rwa [Real.cosh_zero] at h)
  refine h.congr_left (Eventually.of_forall fun z => ?_)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  show Real.cosh t * (Real.exp (-z * Real.cosh t) * Real.cosh (t / 3))
    = Real.cosh t * Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)
  ring

/-- The square-root factor at the saddle: for `0 < x`,
`√(π/(2 ((2/3) x^{3/2}))) = (3^{1/2} √π / 2) · x^{-3/4}`. -/
theorem sqrt_pi_div_two_mul_g {x : ℝ} (hx : 0 < x) :
    Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ))))
      = ((3:ℝ) ^ (1/2 : ℝ) * Real.sqrt Real.pi / 2) * x ^ (-3/4 : ℝ) := by
  have hxp : (0:ℝ) ≤ x := hx.le
  have h2 : Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ))) = (3 * Real.pi / 4) * x ^ (-3/2 : ℝ) := by
    have hy : (0:ℝ) < x ^ (3/2 : ℝ) := Real.rpow_pos_of_pos hx _
    rw [show (-3/2 : ℝ) = -(3/2 : ℝ) from by norm_num, Real.rpow_neg hxp]
    field_simp [hy.ne', Real.pi_ne_zero]
    ring
  have h3 : Real.sqrt ((3 * Real.pi / 4) * x ^ (-3/2 : ℝ))
      = Real.sqrt (3 * Real.pi / 4) * Real.sqrt (x ^ (-3/2 : ℝ)) :=
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 3 * Real.pi / 4) _
  have h4 : Real.sqrt (x ^ (-3/2 : ℝ)) = x ^ (-3/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hxp]
    norm_num
  have h5 : Real.sqrt (3 * Real.pi / 4) = (3:ℝ) ^ (1/2 : ℝ) * Real.sqrt Real.pi / 2 := by
    rw [show (3 * Real.pi / 4 : ℝ) = (3 * Real.pi) / 2 ^ 2 from by ring,
      Real.sqrt_div (by positivity : (0:ℝ) ≤ 3 * Real.pi), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2),
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_eq_rpow]
  rw [h2, h3, h4, h5]

/-- The constant identity `√π / (2π) = 1 / (2√π)`. -/
theorem sqrt_pi_div_two_mul_pi : Real.sqrt Real.pi / (2 * Real.pi)
    = 1 / (2 * Real.sqrt Real.pi) := by
  have hsp : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [eq_div_iff (by positivity : (0:ℝ) < 2 * Real.sqrt Real.pi).ne']
  rw [show Real.sqrt Real.pi / (2 * Real.pi) * (2 * Real.sqrt Real.pi)
      = (Real.sqrt Real.pi * Real.sqrt Real.pi) / Real.pi from by
    field_simp [hsp.ne', Real.pi_ne_zero]]
  rw [Real.mul_self_sqrt Real.pi_pos.le, div_self Real.pi_ne_zero]

/-- The prefactor identity for `airyAiReal_isEquivalent`: for `0 < x`,
`(1/π) √(x/3) √(π/(2 ((2/3) x^{3/2}))) = (1/(2√π)) x^{-1/4}`. -/
theorem airyAiReal_prefactor {x : ℝ} (hx : 0 < x) :
    (1 / Real.pi) * Real.sqrt (x / 3) * Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ))))
      = (1 / (2 * Real.sqrt Real.pi)) * x ^ (-1/4 : ℝ) := by
  have hxp : (0:ℝ) ≤ x := hx.le
  rw [sqrt_pi_div_two_mul_g hx]
  have h1 : Real.sqrt (x / 3) = x ^ (1/2 : ℝ) / (3:ℝ) ^ (1/2 : ℝ) := by
    rw [Real.sqrt_div hxp, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [h1]
  have h2 : (1 / Real.pi) * (x ^ (1/2 : ℝ) / (3:ℝ) ^ (1/2 : ℝ)) *
      (((3:ℝ) ^ (1/2 : ℝ) * Real.sqrt Real.pi / 2) * x ^ (-3/4 : ℝ))
      = ((3:ℝ) ^ (1/2 : ℝ) * Real.sqrt Real.pi / (2 * Real.pi * (3:ℝ) ^ (1/2 : ℝ))) *
        (x ^ (1/2 : ℝ) * x ^ (-3/4 : ℝ)) := by ring
  rw [h2]
  have h3 : x ^ (1/2 : ℝ) * x ^ (-3/4 : ℝ) = x ^ (-1/4 : ℝ) := by
    rw [← Real.rpow_add hx]
    norm_num
  rw [h3]
  have hs3 : (0:ℝ) < (3:ℝ) ^ (1/2 : ℝ) := by positivity
  rw [show 2 * Real.pi * (3:ℝ) ^ (1/2 : ℝ) = (3:ℝ) ^ (1/2 : ℝ) * (2 * Real.pi) from by ring,
    mul_div_mul_left _ _ hs3.ne', sqrt_pi_div_two_mul_pi]

/-- **The exact leading asymptotics of the Airy function** (DLMF 9.7.5):
`Ai(x) ~ (1/(2√π)) x^{-1/4} e^{-(2/3) x^{3/2}}` as `x → ∞`, via the Airy–Bessel
identity and Laplace asymptotics of the Schläfli integral at `z = (2/3) x^{3/2}`. -/
theorem airyAiReal_isEquivalent :
    airyAiReal ~[atTop] fun x => (1 / (2 * Real.sqrt Real.pi)) * x ^ (-1/4 : ℝ) *
      Real.exp (-(2/3) * x ^ (3/2 : ℝ)) := by
  have hg : Tendsto (fun x : ℝ => (2/3) * x ^ (3/2 : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ) < 2/3)).2
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/2))
  have hAi : airyAiReal =ᶠ[atTop] fun x => (1 / Real.pi) * Real.sqrt (x / 3) *
      schlaefliK13 ((2/3) * x ^ (3/2 : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [airyAiReal_eq_airyBesselY_div_pi hx]
    unfold airyBesselY
    rw [div_eq_mul_inv, one_div]
    ring
  have hK : (fun x => schlaefliK13 ((2/3) * x ^ (3/2 : ℝ))) ~[atTop]
      fun x => Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
        Real.exp (-((2/3) * x ^ (3/2 : ℝ))) :=
    schlaefliK13_isEquivalent.comp_tendsto hg
  have hmul : (fun x => (1 / Real.pi) * Real.sqrt (x / 3) *
      schlaefliK13 ((2/3) * x ^ (3/2 : ℝ))) ~[atTop]
      fun x => (1 / Real.pi) * Real.sqrt (x / 3) *
        (Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
          Real.exp (-((2/3) * x ^ (3/2 : ℝ)))) :=
    IsEquivalent.refl.mul hK
  refine hAi.isEquivalent.trans (hmul.trans_eventuallyEq ?_)
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [show (1 / Real.pi) * Real.sqrt (x / 3) *
      (Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
        Real.exp (-((2/3) * x ^ (3/2 : ℝ))))
    = ((1 / Real.pi) * Real.sqrt (x / 3) * Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ))))) *
      Real.exp (-((2/3) * x ^ (3/2 : ℝ))) from by ring, airyAiReal_prefactor hx, neg_mul]

/-- The prefactor identity for `deriv_airyAiReal_isEquivalent`: for `0 < x`,
`(1/π) (√3)⁻¹ x √(π/(2 ((2/3) x^{3/2}))) = (1/(2√π)) x^{1/4}`. -/
theorem deriv_airyAiReal_prefactor {x : ℝ} (hx : 0 < x) :
    (1 / Real.pi) * (Real.sqrt 3)⁻¹ * x * Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ))))
      = (1 / (2 * Real.sqrt Real.pi)) * x ^ (1/4 : ℝ) := by
  rw [sqrt_pi_div_two_mul_g hx, Real.sqrt_eq_rpow]
  have hs3 : (0:ℝ) < (3:ℝ) ^ (1/2 : ℝ) := by positivity
  have hpow : x * x ^ (-3/4 : ℝ) = x ^ (1/4 : ℝ) := by
    have h : x ^ (1:ℝ) * x ^ (-3/4 : ℝ) = x ^ (1/4 : ℝ) := by
      rw [← Real.rpow_add hx]
      norm_num
    rwa [Real.rpow_one] at h
  rw [show (1 / Real.pi) * ((3:ℝ) ^ (1/2 : ℝ))⁻¹ * x *
      (((3:ℝ) ^ (1/2 : ℝ) * Real.sqrt Real.pi / 2) * x ^ (-3/4 : ℝ))
    = ((3:ℝ) ^ (1/2 : ℝ))⁻¹ * (3:ℝ) ^ (1/2 : ℝ) *
      ((Real.sqrt Real.pi / (2 * Real.pi)) * (x * x ^ (-3/4 : ℝ))) from by ring,
    inv_mul_cancel₀ hs3.ne', one_mul, hpow, sqrt_pi_div_two_mul_pi]

/-- **The exact leading asymptotics of the Airy derivative** (DLMF 9.7.6):
`Ai'(x) ~ -(1/(2√π)) x^{1/4} e^{-(2/3) x^{3/2}}` as `x → ∞`, from the explicit
derivative formula `airyBesselY1`: the term `x · K'((2/3)x^{3/2})` dominates by a
factor `≍ x^{3/2}` over the term `x^{-1/2} K((2/3)x^{3/2})`. -/
theorem deriv_airyAiReal_isEquivalent :
    deriv airyAiReal ~[atTop] fun x => -(1 / (2 * Real.sqrt Real.pi)) * x ^ (1/4 : ℝ) *
      Real.exp (-(2/3) * x ^ (3/2 : ℝ)) := by
  have hg : Tendsto (fun x : ℝ => (2/3) * x ^ (3/2 : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ) < 2/3)).2
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/2))
  have hderiv : deriv airyAiReal =ᶠ[atTop] fun x => (1 / Real.pi) * airyBesselY1 x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    have heq : airyAiReal =ᶠ[𝓝 x] fun y => airyBesselY y / Real.pi := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact airyAiReal_eq_airyBesselY_div_pi hy
    rw [heq.deriv_eq, ((hasDerivAt_airyBesselY hx).div_const Real.pi).deriv,
      div_eq_mul_inv, one_div]
    ring
  have hY1 : (fun x => (1 / Real.pi) * airyBesselY1 x) =ᶠ[atTop] fun x =>
      (1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2) * x ^ (-1/2 : ℝ) *
        schlaefliK13 ((2/3) * x ^ (3/2 : ℝ))
      + -((1 / Real.pi) * (Real.sqrt 3)⁻¹ * x *
        ∫ t in Set.Ioi 0, Real.cosh t * Real.exp (-((2/3) * x ^ (3/2 : ℝ)) * Real.cosh t) *
          Real.cosh (t / 3)) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    show (1 / Real.pi) * airyBesselY1 x
      = (1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2) * x ^ (-1/2 : ℝ) *
          schlaefliK13 ((2/3) * x ^ (3/2 : ℝ))
        + -((1 / Real.pi) * (Real.sqrt 3)⁻¹ * x *
          ∫ t in Set.Ioi 0, Real.cosh t * Real.exp (-((2/3) * x ^ (3/2 : ℝ)) * Real.cosh t) *
            Real.cosh (t / 3))
    unfold airyBesselY1
    rw [(deriv_schlaefliK13 (by positivity : (0:ℝ) < (2/3) * x ^ (3/2 : ℝ))).deriv]
    ring
  have hJ : (fun x => ∫ t in Set.Ioi 0, Real.cosh t *
      Real.exp (-((2/3) * x ^ (3/2 : ℝ)) * Real.cosh t) * Real.cosh (t / 3)) ~[atTop]
      fun x => Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
        Real.exp (-((2/3) * x ^ (3/2 : ℝ))) :=
    schlaefliK13_deriv_isEquivalent.comp_tendsto hg
  have hT2 : (fun x => (1 / Real.pi) * (Real.sqrt 3)⁻¹ * x *
      ∫ t in Set.Ioi 0, Real.cosh t * Real.exp (-((2/3) * x ^ (3/2 : ℝ)) * Real.cosh t) *
        Real.cosh (t / 3)) ~[atTop]
      fun x => (1 / Real.pi) * (Real.sqrt 3)⁻¹ * x *
        (Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
          Real.exp (-((2/3) * x ^ (3/2 : ℝ)))) :=
    IsEquivalent.refl.mul hJ
  have halg2 : (fun x => (1 / Real.pi) * (Real.sqrt 3)⁻¹ * x *
      (Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
        Real.exp (-((2/3) * x ^ (3/2 : ℝ))))) =ᶠ[atTop]
      fun x => (1 / (2 * Real.sqrt Real.pi)) * x ^ (1/4 : ℝ) *
        Real.exp (-(2/3) * x ^ (3/2 : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [show (1 / Real.pi) * (Real.sqrt 3)⁻¹ * x *
        (Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
          Real.exp (-((2/3) * x ^ (3/2 : ℝ))))
      = ((1 / Real.pi) * (Real.sqrt 3)⁻¹ * x *
          Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ))))) *
        Real.exp (-((2/3) * x ^ (3/2 : ℝ))) from by ring, deriv_airyAiReal_prefactor hx, neg_mul]
  have hT2' := hT2.trans_eventuallyEq halg2
  have hFne : ∀ᶠ z in atTop, (fun z => Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z)) z ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with z hz
    positivity
  have hK1 : Tendsto (fun x => schlaefliK13 ((2/3) * x ^ (3/2 : ℝ)) /
      (Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
        Real.exp (-((2/3) * x ^ (3/2 : ℝ))))) atTop (𝓝 1) :=
    ((isEquivalent_iff_tendsto_one hFne).1 schlaefliK13_isEquivalent).comp hg
  have hsqrt0 : Tendsto (fun x => Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) atTop (𝓝 0) := by
      have h := hg.inv_tendsto_atTop.const_mul (Real.pi / 2)
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      show (Real.pi / 2) * ((2/3) * x ^ (3/2 : ℝ))⁻¹ = Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))
      rw [div_eq_mul_inv, mul_inv]
      ring
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rwa [Real.sqrt_zero] at h2
  have hT1 : (fun x => (1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2) * x ^ (-1/2 : ℝ) *
      schlaefliK13 ((2/3) * x ^ (3/2 : ℝ)))
      =o[atTop] fun x => (1 / (2 * Real.sqrt Real.pi)) * x ^ (1/4 : ℝ) *
        Real.exp (-(2/3) * x ^ (3/2 : ℝ)) := by
    have hne : ∀ᶠ x in atTop, ((1 / (2 * Real.sqrt Real.pi)) * x ^ (1/4 : ℝ) *
        Real.exp (-(2/3) * x ^ (3/2 : ℝ))) ≠ 0 := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      positivity
    refine (isLittleO_iff_tendsto' (hne.mono fun x hx' h => absurd h hx')).2 ?_
    have hratio : (fun x => ((1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2) * x ^ (-1/2 : ℝ) *
        schlaefliK13 ((2/3) * x ^ (3/2 : ℝ))) /
        ((1 / (2 * Real.sqrt Real.pi)) * x ^ (1/4 : ℝ) *
          Real.exp (-(2/3) * x ^ (3/2 : ℝ))))
        =ᶠ[atTop] fun x => ((1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2)) *
          (2 * Real.sqrt Real.pi) * x ^ (-3/4 : ℝ) *
          (schlaefliK13 ((2/3) * x ^ (3/2 : ℝ)) /
            (Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
              Real.exp (-((2/3) * x ^ (3/2 : ℝ))))) *
          Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      have hs3 : Real.sqrt 3 ≠ 0 := by positivity
      field_simp [hs3, Real.pi_ne_zero,
        (by positivity : (2:ℝ) * Real.sqrt Real.pi ≠ 0),
        (Real.rpow_pos_of_pos hx _).ne', (Real.exp_pos _).ne',
        (by positivity : Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) ≠ 0)]
      rw [mul_assoc, ← Real.rpow_add hx,
        show (1/4 : ℝ) + -(3/4 : ℝ) = -(1/2 : ℝ) from by norm_num]
      exact mul_comm _ _
    have hlim : Tendsto (fun x => ((1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2)) *
        (2 * Real.sqrt Real.pi) * x ^ (-3/4 : ℝ) *
        (schlaefliK13 ((2/3) * x ^ (3/2 : ℝ)) /
          (Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
            Real.exp (-((2/3) * x ^ (3/2 : ℝ))))) *
        Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ))))) atTop (𝓝 0) := by
      have h34 : Tendsto (fun x : ℝ => x ^ (-3/4 : ℝ)) atTop (𝓝 0) := by
        refine (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 3/4)).congr fun x => ?_
        rw [show (-(3/4 : ℝ)) = (-3/4 : ℝ) from by norm_num]
      have h := (((tendsto_const_nhds (x := ((1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2)) *
          (2 * Real.sqrt Real.pi))).mul h34).mul hK1).mul hsqrt0
      simp only [mul_zero, zero_mul] at h
      exact h
    exact hlim.congr' hratio.symm
  have hneg : (fun x => -((1 / Real.pi) * (Real.sqrt 3)⁻¹ * x *
      ∫ t in Set.Ioi 0, Real.cosh t * Real.exp (-((2/3) * x ^ (3/2 : ℝ)) * Real.cosh t) *
        Real.cosh (t / 3))) ~[atTop]
      fun x => -((1 / (2 * Real.sqrt Real.pi)) * x ^ (1/4 : ℝ) *
        Real.exp (-(2/3) * x ^ (3/2 : ℝ))) := hT2'.neg
  have hsum := (isLittleO_neg_right.mpr hT1).add_isEquivalent hneg
  refine (hderiv.trans hY1).isEquivalent.trans (hsum.congr_right ?_)
  filter_upwards with x
  ring

/-! ## The tail-integral asymptotic

`∫_A^∞ Ai(u) du ~ (1/(2√π)) A^{-3/4} e^{-(2/3)A^{3/2}}` as `A → ∞`, by two-sided
comparison against the exact antiderivative `-u^{-3/4} e^{-(2/3)u^{3/2}}` of
`u^{-1/4}(1 + (3/4) u^{-3/2}) e^{-(2/3)u^{3/2}}`. -/

/-- The antiderivative identity: for `0 < u`,
`(u^{-3/4} e^{-(2/3)u^{3/2}})' = -(u^{-1/4} + (3/4) u^{-7/4}) e^{-(2/3)u^{3/2}}`. -/
theorem hasDerivAt_airyTailAntideriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun u => u ^ (-3/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
      (-(u ^ (-1/4 : ℝ) + (3/4) * u ^ (-(7/4) : ℝ)) *
        Real.exp (-(2/3) * u ^ (3/2 : ℝ))) u := by
  have h1 : HasDerivAt (fun u : ℝ => u ^ (-3/4 : ℝ)) ((-3/4) * u ^ (-3/4 - 1 : ℝ)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have hr : HasDerivAt (fun u : ℝ => u ^ (3/2 : ℝ)) ((3/2) * u ^ (3/2 - 1 : ℝ)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have h2 : HasDerivAt (fun u : ℝ => Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
      (Real.exp (-(2/3) * u ^ (3/2 : ℝ)) * (-(2/3) * ((3/2) * u ^ (3/2 - 1 : ℝ)))) u :=
    (Real.hasDerivAt_exp _).comp u (hr.const_mul (-(2/3) : ℝ))
  convert h1.mul h2 using 1
  rw [show (-3/4 : ℝ) - 1 = -(7/4) by norm_num, show (3/2 : ℝ) - 1 = 1/2 by norm_num,
    show u ^ (-(7/4) : ℝ) = u ^ (-1/4 : ℝ) * u ^ (-3/2 : ℝ) from by
      rw [← Real.rpow_add hu]; congr 1; norm_num]
  have hpow : u ^ (-3/4 : ℝ) * u ^ (1/2 : ℝ) = u ^ (-1/4 : ℝ) := by
    rw [← Real.rpow_add hu]; congr 1; norm_num
  linear_combination Real.exp (-(2/3) * u ^ (3/2 : ℝ)) * hpow

/-- The tail antiderivative vanishes at `+∞`. -/
theorem tendsto_airyTailAntideriv_atTop :
    Tendsto (fun u => u ^ (-3/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => u ^ (-3/4 : ℝ)) atTop (𝓝 0) := by
    refine (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 3/4)).congr fun x => ?_
    rw [show (-(3/4 : ℝ)) = (-3/4 : ℝ) from by norm_num]
  have h2 : Tendsto (fun u : ℝ => Real.exp (-(2/3) * u ^ (3/2 : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atTop_of_neg
      (by norm_num : (-(2/3):ℝ) < 0) (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/2)))
  simpa using h1.mul h2

/-- `u ↦ u ^ p * e^{-(2/3)u^{3/2}}` is continuous on `[1, ∞)`. -/
theorem continuousOn_rpow_mul_exp_tail (p : ℝ) :
    ContinuousOn (fun u => u ^ p * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) (Set.Ici 1) := by
  apply ContinuousOn.mul
  · intro u hu
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt (lt_of_lt_of_le
      zero_lt_one (mem_Ici.mp hu))))).continuousWithinAt
  · exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_id.rpow_const fun u => Or.inr (by norm_num : (0:ℝ) ≤ 3/2)))).continuousOn

/-- The tail envelope `u^{-1/4} e^{-(2/3)u^{3/2}}` is integrable on `(A, ∞)` for
`1 ≤ A`. -/
theorem integrableOn_airyTailEnvelope {A : ℝ} (hA : 1 ≤ A) :
    IntegrableOn (fun u => u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
      (Set.Ioi A) := by
  have hI3 : IntegrableOn (fun u => u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
      (Set.Ioi 3) := by
    refine (integrableOn_exp_neg_Ioi 3).mono' (((continuousOn_rpow_mul_exp_tail _).mono
      (Set.Ioi_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr (by norm_num)))).aestronglyMeasurable
        measurableSet_Ioi) (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
    have hu3 : (3:ℝ) ≤ u := (mem_Ioi.mp hu).le
    have hu1 : (1:ℝ) ≤ u := by linarith
    have hu0 : (0:ℝ) < u := by linarith
    have h1 : u ^ (-1/4 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
    have hsqrt : (3/2 : ℝ) ≤ Real.sqrt u :=
      Real.le_sqrt_of_sq_le (by linarith : (3/2 : ℝ)^2 ≤ u)
    have h2 : (u:ℝ) ≤ (2/3) * u ^ (3/2 : ℝ) := by
      rw [show u ^ (3/2 : ℝ) = u ^ (1 : ℝ) * u ^ (1/2 : ℝ) from by
        rw [← Real.rpow_add hu0]; congr 1; norm_num, Real.rpow_one, ← Real.sqrt_eq_rpow]
      have hmul := mul_le_mul_of_nonneg_left hsqrt (by linarith : (0:ℝ) ≤ u)
      calc u = (2/3) * (u * (3/2)) := by ring
        _ ≤ (2/3) * (u * Real.sqrt u) := mul_le_mul_of_nonneg_left hmul (by norm_num)
    have hE : Real.exp (-(2/3) * u ^ (3/2 : ℝ)) ≤ Real.exp (-u) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))
        ≤ 1 * Real.exp (-u) := mul_le_mul h1 hE (Real.exp_pos _).le zero_le_one
      _ = Real.exp (-u) := one_mul _
  have hI13 : IntegrableOn (fun u => u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
      (Set.Ioc 1 3) :=
    (((continuousOn_rpow_mul_exp_tail _).mono (Set.Icc_subset_Ici_self :
      Set.Icc (1:ℝ) 3 ⊆ Set.Ici 1)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hU : Set.Ioi (1:ℝ) = Set.Ioc 1 3 ∪ Set.Ioi 3 := by
    ext u
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro h
      by_cases h3 : u ≤ 3
      · exact Or.inl ⟨h, h3⟩
      · exact Or.inr (lt_of_not_ge h3)
    · rintro (⟨h1, -⟩ | h3) <;> linarith
  have hI1 : IntegrableOn (fun u => u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
      (Set.Ioi 1) := by
    rw [hU]
    exact hI13.union hI3
  exact hI1.mono_set (Set.Ioi_subset_Ioi hA)

/-- The summed tail integrand `(u^{-1/4} + (3/4) u^{-7/4}) e^{-(2/3)u^{3/2}}` is
integrable on `(A, ∞)` for `1 ≤ A`. -/
theorem integrableOn_airyTailSum {A : ℝ} (hA : 1 ≤ A) :
    IntegrableOn (fun u => (u ^ (-1/4 : ℝ) + (3/4) * u ^ (-(7/4) : ℝ)) *
        Real.exp (-(2/3) * u ^ (3/2 : ℝ))) (Set.Ioi A) := by
  have hJ := integrableOn_airyTailEnvelope hA
  have hJ2 : IntegrableOn (fun u => u ^ (-(7/4) : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
      (Set.Ioi A) := by
    refine hJ.mono' (((continuousOn_rpow_mul_exp_tail _).mono
      (Set.Ioi_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr hA))).aestronglyMeasurable
        measurableSet_Ioi) (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
    · have hu1 : (1:ℝ) ≤ u := hA.trans (mem_Ioi.mp hu).le
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hu1 (show (-(7/4):ℝ) ≤ -1/4 by norm_num))
        (Real.exp_pos _).le
  exact (hJ.add (hJ2.const_mul (3/4 : ℝ))).congr (ae_restrict_of_forall_mem measurableSet_Ioi
    fun u _ => by simp only [Pi.add_apply]; ring)

/-- The exact tail integral of the summed envelope: for `1 ≤ A`,
`∫_A^∞ (u^{-1/4} + (3/4) u^{-7/4}) e^{-(2/3)u^{3/2}} du = A^{-3/4} e^{-(2/3)A^{3/2}}`. -/
theorem integral_airyTailSum_eq {A : ℝ} (hA : 1 ≤ A) :
    ∫ u in Set.Ioi A, (u ^ (-1/4 : ℝ) + (3/4) * u ^ (-(7/4) : ℝ)) *
        Real.exp (-(2/3) * u ^ (3/2 : ℝ))
      = A ^ (-3/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ)) := by
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hderiv : ∀ u ∈ Set.Ioi A,
      HasDerivAt (fun u => u ^ (-3/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
        (-(u ^ (-1/4 : ℝ) + (3/4) * u ^ (-(7/4) : ℝ)) *
          Real.exp (-(2/3) * u ^ (3/2 : ℝ))) u :=
    fun u hu => hasDerivAt_airyTailAntideriv (lt_trans hA0 (mem_Ioi.mp hu))
  have hint : IntegrableOn (fun u => -(u ^ (-1/4 : ℝ) + (3/4) * u ^ (-(7/4) : ℝ)) *
      Real.exp (-(2/3) * u ^ (3/2 : ℝ))) (Set.Ioi A) :=
    (integrableOn_airyTailSum hA).neg.congr (ae_restrict_of_forall_mem measurableSet_Ioi
      fun u _ => by simp only [Pi.neg_apply]; ring)
  have hcontF : ContinuousWithinAt (fun u => u ^ (-3/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
      (Set.Ici A) A := ((Real.continuousAt_rpow_const _ _ (Or.inl hA0.ne')).mul
        (Real.continuous_exp.comp (continuous_const.mul
          (continuous_id.rpow_const fun u => Or.inr (by norm_num : (0:ℝ) ≤ 3/2)))).continuousAt
        ).continuousWithinAt
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcontF hderiv hint
    tendsto_airyTailAntideriv_atTop
  have hcongr : (fun u : ℝ => -(u ^ (-1/4 : ℝ) + (3/4) * u ^ (-(7/4) : ℝ)) *
      Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
      = fun u => -((u ^ (-1/4 : ℝ) + (3/4) * u ^ (-(7/4) : ℝ)) *
        Real.exp (-(2/3) * u ^ (3/2 : ℝ))) := funext fun u => by ring
  rw [hcongr, integral_neg, zero_sub] at hFTC
  linarith [hFTC]

/-- The tail-envelope integral asymptotic: `J(A) ~ A^{-3/4} e^{-(2/3)A^{3/2}}`. -/
theorem integral_airyTailEnvelope_isEquivalent :
    (fun A => ∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
      ~[atTop]
      fun A => A ^ (-3/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ)) := by
  have hFne : ∀ᶠ A in atTop,
      (A ^ (-3/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ))) ≠ 0 :=
    (eventually_gt_atTop 0).mono fun A hA => ne_of_gt (by positivity)
  rw [isEquivalent_iff_tendsto_one hFne]
  -- The two-sided bound: for `A ≥ 1`, `J(A) ≤ F(A) ≤ J(A) (1 + (3/4) A^{-3/2})`.
  have hcore : ∀ᶠ A in atTop,
      0 < A ^ (-3/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ)) ∧
      (∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) ≤
        A ^ (-3/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ)) ∧
      A ^ (-3/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ)) ≤
        (∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) *
          (1 + (3/4) * A ^ (-3/2 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with A hA
    have hA0 : (0:ℝ) < A := lt_of_lt_of_le zero_lt_one hA
    have hFA : 0 < A ^ (-3/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ)) := by positivity
    have hJ := integrableOn_airyTailEnvelope hA
    have hJ2 : IntegrableOn (fun u => u ^ (-(7/4) : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
        (Set.Ioi A) := by
      refine hJ.mono' (((continuousOn_rpow_mul_exp_tail _).mono
        (Set.Ioi_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr hA))).aestronglyMeasurable
          measurableSet_Ioi) (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
      have hu1 : (1:ℝ) ≤ u := hA.trans (mem_Ioi.mp hu).le
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hu1 (show (-(7/4):ℝ) ≤ -1/4 by norm_num))
        (Real.exp_pos _).le
    have hsplit : ∫ u in Set.Ioi A, (u ^ (-1/4 : ℝ) + (3/4) * u ^ (-(7/4) : ℝ)) *
          Real.exp (-(2/3) * u ^ (3/2 : ℝ))
        = (∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) +
            (3/4) * ∫ u in Set.Ioi A, u ^ (-(7/4) : ℝ) *
              Real.exp (-(2/3) * u ^ (3/2 : ℝ)) := by
      rw [← integral_const_mul, ← integral_add hJ (hJ2.const_mul (3/4 : ℝ))]
      exact integral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi
        fun u _ => by ring)
    have h2nd : ∫ u in Set.Ioi A, u ^ (-(7/4) : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))
        ≤ A ^ (-3/2 : ℝ) * ∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) *
            Real.exp (-(2/3) * u ^ (3/2 : ℝ)) := by
      have hkey : ∀ u ∈ Set.Ioi A,
          u ^ (-(7/4) : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ)) ≤
            A ^ (-3/2 : ℝ) * (u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) := by
        intro u hu
        have hu0 : 0 < u := lt_trans hA0 (mem_Ioi.mp hu)
        have hsplit' : u ^ (-(7/4) : ℝ) = u ^ (-1/4 : ℝ) * u ^ (-3/2 : ℝ) := by
          rw [← Real.rpow_add hu0]; congr 1; norm_num
        have hAle : u ^ (-3/2 : ℝ) ≤ A ^ (-3/2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hA0 (mem_Ioi.mp hu).le (by norm_num)
        rw [hsplit']
        calc u ^ (-1/4 : ℝ) * u ^ (-3/2 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))
            ≤ u ^ (-1/4 : ℝ) * A ^ (-3/2 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAle (by positivity))
                (Real.exp_pos _).le
          _ = A ^ (-3/2 : ℝ) * (u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) := by
              ring
      calc ∫ u in Set.Ioi A, u ^ (-(7/4) : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))
          ≤ ∫ u in Set.Ioi A, A ^ (-3/2 : ℝ) * (u ^ (-1/4 : ℝ) *
              Real.exp (-(2/3) * u ^ (3/2 : ℝ))) :=
            setIntegral_mono_on hJ2 (hJ.const_mul _) measurableSet_Ioi hkey
        _ = A ^ (-3/2 : ℝ) * ∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) *
              Real.exp (-(2/3) * u ^ (3/2 : ℝ)) := integral_const_mul _ _
    refine ⟨hFA, ?_, ?_⟩
    · calc ∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))
          ≤ ∫ u in Set.Ioi A, (u ^ (-1/4 : ℝ) + (3/4) * u ^ (-(7/4) : ℝ)) *
              Real.exp (-(2/3) * u ^ (3/2 : ℝ)) :=
            setIntegral_mono_on hJ (integrableOn_airyTailSum hA) measurableSet_Ioi
              (fun u hu => mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_right (by
                  have hu0 : (0:ℝ) < u := lt_trans hA0 (mem_Ioi.mp hu)
                  positivity)) (Real.exp_pos _).le)
        _ = A ^ (-3/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ)) := integral_airyTailSum_eq hA
    · calc A ^ (-3/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ))
          = ∫ u in Set.Ioi A, (u ^ (-1/4 : ℝ) + (3/4) * u ^ (-(7/4) : ℝ)) *
              Real.exp (-(2/3) * u ^ (3/2 : ℝ)) := (integral_airyTailSum_eq hA).symm
        _ = (∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) +
              (3/4) * ∫ u in Set.Ioi A, u ^ (-(7/4) : ℝ) *
                Real.exp (-(2/3) * u ^ (3/2 : ℝ)) := hsplit
        _ ≤ (∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) +
              (3/4) * (A ^ (-3/2 : ℝ) * ∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) *
                Real.exp (-(2/3) * u ^ (3/2 : ℝ))) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left h2nd (by norm_num))
        _ = (∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) *
              (1 + (3/4) * A ^ (-3/2 : ℝ)) := by ring
  -- The ratio is squeezed between `1 / (1 + (3/4) A^{-3/2})` and `1`.
  have hlb : ∀ᶠ A in atTop, 1 / (1 + (3/4) * A ^ (-3/2 : ℝ)) ≤
      (∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) /
        (A ^ (-3/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ))) := by
    filter_upwards [hcore, eventually_gt_atTop 0] with A hc hA0
    obtain ⟨hFA, hJF, hFJ⟩ := hc
    have hε : (0:ℝ) < 1 + (3/4) * A ^ (-3/2 : ℝ) := by positivity
    rw [le_div_iff₀ hFA, div_mul_eq_mul_div, div_le_iff₀ hε, one_mul]
    exact hFJ
  have hub : ∀ᶠ A in atTop,
      (∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) /
        (A ^ (-3/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ))) ≤ 1 := by
    filter_upwards [hcore] with A hc
    obtain ⟨hFA, hJF, -⟩ := hc
    exact (div_le_one hFA).mpr hJF
  have hlbT : Tendsto (fun A : ℝ => 1 / (1 + (3/4) * A ^ (-3/2 : ℝ))) atTop (𝓝 1) := by
    have h0' : Tendsto (fun A : ℝ => A ^ (-3/2 : ℝ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 3/2)).congr fun A => by
        rw [show (-(3/2 : ℝ)) = (-3/2 : ℝ) from by norm_num]
    have hsum : Tendsto (fun A : ℝ => (1:ℝ) + (3/4) * A ^ (-3/2 : ℝ)) atTop
        (𝓝 (1 + (3/4) * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul h0')
    rw [mul_zero, add_zero] at hsum
    have hinv : Tendsto (fun A : ℝ => (1 + (3/4) * A ^ (-3/2 : ℝ))⁻¹) atTop (𝓝 (1⁻¹)) :=
      hsum.inv₀ one_ne_zero
    rw [inv_one] at hinv
    exact hinv.congr fun A => by rw [one_div]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlbT tendsto_const_nhds hlb hub

/-- `Ai` is integrable on `(A, ∞)` for `1 ≤ A` (comparison with the tail envelope via
`airyAiReal_le`, using positivity on `[0, ∞)`). -/
theorem integrableOn_airyAiReal_Ioi {A : ℝ} (hA : 1 ≤ A) :
    IntegrableOn airyAiReal (Set.Ioi A) := by
  obtain ⟨C₁, hC₁⟩ := airyAiReal_le
  have hC₁pos : 0 < C₁ := by
    have h1 := hC₁ 1 le_rfl
    rw [Real.one_rpow, mul_one] at h1
    exact pos_of_mul_pos_left (lt_of_lt_of_le (airyAiReal_pos one_pos) h1)
      (Real.exp_pos _).le
  refine ((integrableOn_airyTailEnvelope hA).const_mul C₁).mono' ?_ ?_
  · exact (continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_airyAiReal x).continuousAt).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu1 : (1:ℝ) ≤ u := hA.trans (mem_Ioi.mp hu).le
    rw [Real.norm_eq_abs, abs_of_nonneg (airyAiReal_pos_of_nonneg (zero_le_one.trans hu1)).le]
    calc airyAiReal u ≤ C₁ * u ^ (-1/4 : ℝ) * Real.exp (-(2/3 * u ^ (3/2 : ℝ))) :=
        hC₁ u hu1
      _ = C₁ * (u ^ (-1/4 : ℝ) * Real.exp (-(2/3) * u ^ (3/2 : ℝ))) := by
          rw [← mul_assoc, show -(2/3 * u ^ (3/2 : ℝ)) = -(2/3) * u ^ (3/2 : ℝ) from
            (neg_mul _ _).symm]

/-- **The Airy tail integral** (DLMF 9.7.7; the form in which the paper's
`ρ(M) = C* M^{1/4} e^{-κ M^{3/2}}` normalization feeds the two-block expansion):
`∫_A^∞ Ai(u) du ~ (1/(2√π)) A^{-3/4} e^{-(2/3)A^{3/2}}` as `A → ∞`. -/
theorem integral_airyAiReal_isEquivalent :
    (fun A => ∫ u in Set.Ioi A, airyAiReal u) ~[atTop]
      fun A => (1 / (2 * Real.sqrt Real.pi)) * A ^ (-3/4 : ℝ) *
        Real.exp (-(2/3) * A ^ (3/2 : ℝ)) := by
  have hφ : (fun A => ∫ u in Set.Ioi A, (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
        Real.exp (-(2/3) * u ^ (3/2 : ℝ))) ~[atTop]
      fun A => (1 / (2 * Real.sqrt Real.pi)) * A ^ (-3/4 : ℝ) *
        Real.exp (-(2/3) * A ^ (3/2 : ℝ)) := by
    have hc_ne : (1 : ℝ) / (2 * Real.sqrt Real.pi) ≠ 0 := by positivity
    have hFne0 : ∀ᶠ A in atTop,
        (A ^ (-3/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ))) ≠ 0 :=
      (eventually_gt_atTop 0).mono fun A hA => ne_of_gt (by positivity)
    have hFne' : ∀ᶠ A in atTop, (1 / (2 * Real.sqrt Real.pi)) * A ^ (-3/4 : ℝ) *
        Real.exp (-(2/3) * A ^ (3/2 : ℝ)) ≠ 0 :=
      (eventually_gt_atTop 0).mono fun A hA => mul_ne_zero
        (mul_ne_zero hc_ne (by positivity)) (Real.exp_pos _).ne'
    rw [isEquivalent_iff_tendsto_one hFne']
    have hJF := (isEquivalent_iff_tendsto_one hFne0).mp
      integral_airyTailEnvelope_isEquivalent
    exact hJF.congr fun A => by
      simp only [Pi.div_apply]
      have hnum : (∫ u in Set.Ioi A, (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
            Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
          = (1 / (2 * Real.sqrt Real.pi)) * (∫ u in Set.Ioi A, u ^ (-1/4 : ℝ) *
              Real.exp (-(2/3) * u ^ (3/2 : ℝ))) := by
        rw [show (fun u => (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
              Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
            = fun u => (1 / (2 * Real.sqrt Real.pi)) * (u ^ (-1/4 : ℝ) *
              Real.exp (-(2/3) * u ^ (3/2 : ℝ))) from funext fun u => mul_assoc _ _ _,
          integral_const_mul]
      rw [hnum, mul_assoc, mul_div_mul_left _ _ hc_ne]
  have hdiff : (fun A => (∫ u in Set.Ioi A, airyAiReal u) -
        (∫ u in Set.Ioi A, (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
          Real.exp (-(2/3) * u ^ (3/2 : ℝ)))) =o[atTop]
      fun A => ∫ u in Set.Ioi A, (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
        Real.exp (-(2/3) * u ^ (3/2 : ℝ)) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have h0 := airyAiReal_isEquivalent.isLittleO
    rw [Asymptotics.isLittleO_iff] at h0
    obtain ⟨B, hB⟩ := eventually_atTop.1 (h0 hε)
    filter_upwards [eventually_ge_atTop (max B 1)] with A hA
    have hA1 : 1 ≤ A := le_trans (le_max_right B 1) hA
    have hAB : ∀ u ∈ Set.Ioi A,
        ‖airyAiReal u - (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
          Real.exp (-(2/3) * u ^ (3/2 : ℝ))‖ ≤
          ε * ‖(1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
            Real.exp (-(2/3) * u ^ (3/2 : ℝ))‖ :=
      fun u hu => hB u (((le_max_left B 1).trans hA).trans_lt (mem_Ioi.mp hu)).le
    have hAiI := integrableOn_airyAiReal_Ioi hA1
    have hφI : IntegrableOn (fun u => (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
        Real.exp (-(2/3) * u ^ (3/2 : ℝ))) (Set.Ioi A) :=
      ((integrableOn_airyTailEnvelope hA1).const_mul (1 / (2 * Real.sqrt Real.pi))).congr
        (Filter.Eventually.of_forall fun u => (mul_assoc _ _ _).symm)
    have hφpos : ∀ u ∈ Set.Ioi A, (0:ℝ) ≤ (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
        Real.exp (-(2/3) * u ^ (3/2 : ℝ)) := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one (hA1.trans (mem_Ioi.mp hu).le)
      positivity
    have hsub : (∫ u in Set.Ioi A, airyAiReal u) -
        (∫ u in Set.Ioi A, (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
          Real.exp (-(2/3) * u ^ (3/2 : ℝ)))
        = ∫ u in Set.Ioi A, (airyAiReal u - ((1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
            Real.exp (-(2/3) * u ^ (3/2 : ℝ)))) := (integral_sub hAiI hφI).symm
    calc ‖(∫ u in Set.Ioi A, airyAiReal u) -
          (∫ u in Set.Ioi A, (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
            Real.exp (-(2/3) * u ^ (3/2 : ℝ)))‖
        = ‖∫ u in Set.Ioi A, (airyAiReal u - ((1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
            Real.exp (-(2/3) * u ^ (3/2 : ℝ))))‖ := by rw [hsub]
      _ ≤ ∫ u in Set.Ioi A, ‖airyAiReal u - ((1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
            Real.exp (-(2/3) * u ^ (3/2 : ℝ)))‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi A, ε * ((1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
            Real.exp (-(2/3) * u ^ (3/2 : ℝ))) :=
          setIntegral_mono_on ((hAiI.sub hφI).norm) (hφI.const_mul ε) measurableSet_Ioi
            (fun u hu => (hAB u hu).trans_eq (by rw [Real.norm_of_nonneg (hφpos u hu)]))
      _ = ε * (∫ u in Set.Ioi A, (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
            Real.exp (-(2/3) * u ^ (3/2 : ℝ))) := by rw [integral_const_mul]
      _ = ε * ‖∫ u in Set.Ioi A, (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
            Real.exp (-(2/3) * u ^ (3/2 : ℝ))‖ := by
          rw [Real.norm_of_nonneg (integral_nonneg_of_ae
            (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => hφpos u hu))]
  have hsum := hdiff.add_isEquivalent (IsEquivalent.refl :
    (fun A => ∫ u in Set.Ioi A, (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
      Real.exp (-(2/3) * u ^ (3/2 : ℝ))) ~[atTop]
      (fun A => ∫ u in Set.Ioi A, (1 / (2 * Real.sqrt Real.pi)) * u ^ (-1/4 : ℝ) *
        Real.exp (-(2/3) * u ^ (3/2 : ℝ))))
  exact (hsum.trans hφ).congr_left (Filter.Eventually.of_forall fun A => by
    simp only [Pi.add_apply]; ring)

end AiryLeading
