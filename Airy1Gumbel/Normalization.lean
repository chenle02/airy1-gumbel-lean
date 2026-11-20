/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

open Filter
open scoped Topology

namespace Airy1Gumbel

/-!
# Gumbel normalization constants and the analytic core of the centering and normalization lemmas

This file defines the constants of the Airy₁ maxima problem (the tail constants
`κ`, `γ = κ^{-2/3}`, `c_*`, the exponent function `H(u)`, and the centering/scaling
sequences `a_N`, `b_N`, `u_N(z)`; the real-length versions `a_T`, `b_T`, `u_T(z)`
are `gumbelAR`, `gumbelBR`, `gumbelUR`) and proves the two analytic normalization
statements:

* `airyH_gumbelA`: `H(a_N) - log N → 0`, the analytic content of the paper's centering lemma;
* `gumbel_normalization`: `N * exp(-H(u_N(z))) → exp(-z)`, the analytic content
  of the paper's normalization lemma.

The proofs avoid any Taylor theorem: they rest on the exact algebraic identity
`(1+ε)^{3/2} - 1 - (3/2) ε = ε² c(ε)` with `|c(ε)| ≤ 1` for `|ε| ≤ 1/2`
(see `rpow_three_halves_one_add` and `abs_airyCorrC_le`), together with the
elementary limits `log L / L → 0` and `(log L)² / L → 0`.
-/

/-- The Airy₁ tail constant `κ = 4√2/3`. -/
noncomputable def airyKappa : ℝ := 4 * Real.sqrt 2 / 3

/-- `γ = κ^{-2/3}`. -/
noncomputable def airyGamma : ℝ := airyKappa ^ (-(2 : ℝ) / 3)

/-- The prefactor `c_* = 2^{1/4} / √π`. -/
noncomputable def airyCStar : ℝ := 2 ^ ((1 : ℝ) / 4) / Real.sqrt Real.pi

/-- The exponent function `H(u) = κ u^{3/2} - (1/4) log u - log c_*`. -/
noncomputable def airyH (u : ℝ) : ℝ :=
  airyKappa * u ^ ((3 : ℝ) / 2) - (1 / 4) * Real.log u - Real.log airyCStar

/-- The centering sequence `a_N`. -/
noncomputable def gumbelA (N : ℕ) : ℝ :=
  airyGamma * (Real.log N) ^ ((2 : ℝ) / 3) +
    (airyGamma / 9) * (Real.log (Real.log N) + Real.log (3 / (2 * Real.pi ^ 3))) *
      (Real.log N) ^ (-(1 : ℝ) / 3)

/-- The scaling sequence `b_N`. -/
noncomputable def gumbelB (N : ℕ) : ℝ :=
  (2 * airyGamma / 3) * (Real.log N) ^ (-(1 : ℝ) / 3)

/-- The normalization `u_N(z) = a_N + b_N z`. -/
noncomputable def gumbelU (N : ℕ) (z : ℝ) : ℝ := gumbelA N + gumbelB N * z

/-- The real-length centering `a_T`: the same formula as `gumbelA` with
`Real.log T` in place of `Real.log N`. -/
noncomputable def gumbelAR (T : ℝ) : ℝ :=
  airyGamma * (Real.log T) ^ ((2 : ℝ) / 3) +
    (airyGamma / 9) * (Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) *
      (Real.log T) ^ (-(1 : ℝ) / 3)

/-- The real-length scaling `b_T`: the same formula as `gumbelB` with
`Real.log T` in place of `Real.log N`. -/
noncomputable def gumbelBR (T : ℝ) : ℝ :=
  (2 * airyGamma / 3) * (Real.log T) ^ (-(1 : ℝ) / 3)

/-- The real-length normalization `u_T(z) = a_T + b_T z`. -/
noncomputable def gumbelUR (T : ℝ) (z : ℝ) : ℝ := gumbelAR T + gumbelBR T * z

/-- Cast bridge: `a_T` at an integer length recovers `a_N`. -/
@[simp] lemma gumbelAR_natCast (N : ℕ) : gumbelAR (N : ℝ) = gumbelA N := rfl

/-- Cast bridge: `b_T` at an integer length recovers `b_N`. -/
@[simp] lemma gumbelBR_natCast (N : ℕ) : gumbelBR (N : ℝ) = gumbelB N := rfl

/-- Cast bridge: `u_T(z)` at an integer length recovers `u_N(z)`. -/
@[simp] lemma gumbelUR_natCast (N : ℕ) (z : ℝ) : gumbelUR (N : ℝ) z = gumbelU N z := rfl

/-- Auxiliary constant `A = γ / 9`. -/
noncomputable def auxA : ℝ := airyGamma / 9

/-- Auxiliary constant `B = (γ / 9) * log (3 / (2π³))`. -/
noncomputable def auxB : ℝ := airyGamma / 9 * Real.log (3 / (2 * Real.pi ^ 3))

/-- The relative second-order correction `ε_N` in `a_N = γ L^{2/3} (1 + ε_N)`. -/
noncomputable def epsN (N : ℕ) : ℝ :=
  (auxA * Real.log (Real.log (N : ℝ)) + auxB) / (airyGamma * Real.log (N : ℝ))

/-- The relative perturbation `δ_N` in `u_N(z) = a_N (1 + δ_N)`. -/
noncomputable def deltaN (z : ℝ) (N : ℕ) : ℝ := gumbelB N * z / gumbelA N

/-- The exact quadratic remainder `c(ε)` in
`(1+ε)^{3/2} = 1 + (3/2) ε + ε² c(ε)`. -/
noncomputable def airyCorrC (ε : ℝ) : ℝ :=
  1 / 2 - (1 + ε) / (4 * (Real.sqrt (1 + ε) + 1 + ε / 2))

/-! ### Positivity and power/logarithm algebra for the constants -/

lemma airyKappa_pos : 0 < airyKappa := by
  unfold airyKappa
  positivity

lemma airyGamma_pos : 0 < airyGamma := Real.rpow_pos_of_pos airyKappa_pos _

lemma airyCStar_pos : 0 < airyCStar := by
  unfold airyCStar
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.sqrt_pos_of_pos Real.pi_pos)

lemma airyGamma_rpow_three_halves : airyGamma ^ ((3 : ℝ) / 2) = airyKappa⁻¹ := by
  have hκ : (0 : ℝ) ≤ airyKappa := airyKappa_pos.le
  unfold airyGamma
  rw [← Real.rpow_mul hκ, show (-(2 : ℝ) / 3) * (3 / 2) = -1 by norm_num,
    Real.rpow_neg_one]

lemma airyKappa_mul_airyGamma_rpow : airyKappa * airyGamma ^ ((3 : ℝ) / 2) = 1 := by
  rw [airyGamma_rpow_three_halves, mul_inv_cancel₀ (ne_of_gt airyKappa_pos)]

lemma log_airyKappa : Real.log airyKappa = (5 / 2) * Real.log 2 - Real.log 3 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  unfold airyKappa
  rw [Real.log_div (mul_ne_zero (by norm_num) h2.ne') (by norm_num),
    Real.log_mul (by norm_num) h2.ne', Real.log_sqrt (by norm_num), h4]
  ring

lemma log_airyGamma : Real.log airyGamma = (-(2 : ℝ) / 3) * Real.log airyKappa := by
  unfold airyGamma
  rw [Real.log_rpow airyKappa_pos]

lemma log_airyCStar :
    Real.log airyCStar = (1 / 4) * Real.log 2 - (1 / 2) * Real.log Real.pi := by
  have h1 : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos_of_pos Real.pi_pos
  unfold airyCStar
  rw [Real.log_div h1.ne' h2.ne', Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_sqrt Real.pi_pos.le]
  ring

lemma log_const :
    Real.log (3 / (2 * Real.pi ^ 3)) = Real.log 3 - Real.log 2 - 3 * Real.log Real.pi := by
  rw [Real.log_div (by norm_num) (mul_ne_zero (by norm_num) (pow_ne_zero 3 Real.pi_ne_zero)),
    Real.log_mul (by norm_num) (pow_ne_zero 3 Real.pi_ne_zero), Real.log_pow]
  push_cast
  ring

/-- The constant terms in the expansion of `H(a_N)` cancel exactly. -/
lemma airyH_const_zero :
    Real.log (3 / (2 * Real.pi ^ 3)) / 6 - (1 / 4) * Real.log airyGamma -
      Real.log airyCStar = 0 := by
  rw [log_airyGamma, log_airyKappa, log_airyCStar, log_const]
  ring

/-! ### Elementary real facts -/

lemma log_nat_pos {N : ℕ} (hN : 2 ≤ N) : 0 < Real.log (N : ℝ) := by
  apply Real.log_pos
  have h : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  linarith

lemma one_add_pos_of_abs_le_half {ε : ℝ} (hε : |ε| ≤ 1 / 2) : (0 : ℝ) < 1 + ε := by
  linarith [(abs_le.mp hε).1]

/-! ### The exact second-order identity for `(1+ε)^{3/2}` -/

lemma sqrt_diff_mul {ε : ℝ} (hε : |ε| ≤ 1 / 2) :
    (Real.sqrt (1 + ε) - (1 + ε / 2)) * (4 * (Real.sqrt (1 + ε) + 1 + ε / 2)) = -ε ^ 2 := by
  have h0 : (0 : ℝ) ≤ 1 + ε := by linarith [(abs_le.mp hε).1]
  have hs := Real.sq_sqrt h0
  linear_combination 4 * hs

lemma four_mul_denom_pos {ε : ℝ} (hε : |ε| ≤ 1 / 2) :
    (0 : ℝ) < 4 * (Real.sqrt (1 + ε) + 1 + ε / 2) := by
  have h2 : (0 : ℝ) < 1 + ε / 2 := by linarith [(abs_le.mp hε).1]
  have h3 : (0 : ℝ) < Real.sqrt (1 + ε) + (1 + ε / 2) :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) h2
  have h4 : (0 : ℝ) < Real.sqrt (1 + ε) + 1 + ε / 2 := by linarith
  exact mul_pos (by norm_num) h4

lemma rpow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

/-- The exact quadratic identity `(1+ε)^{3/2} - 1 - (3/2)ε = ε² c(ε)`. -/
lemma rpow_three_halves_one_add {ε : ℝ} (hε : |ε| ≤ 1 / 2) :
    (1 + ε) ^ ((3 : ℝ) / 2) - 1 - (3 / 2) * ε = ε ^ 2 * airyCorrC ε := by
  have h0 : (0 : ℝ) < 1 + ε := one_add_pos_of_abs_le_half hε
  have hden := four_mul_denom_pos hε
  have h := sqrt_diff_mul hε
  rw [rpow_three_halves_eq_mul_sqrt h0]
  have hd : (4 * (Real.sqrt (1 + ε) + 1 + ε / 2)) / 2 /
      (4 * (Real.sqrt (1 + ε) + 1 + ε / 2)) = 1 / 2 := by
    rw [div_div, div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hden.ne')]
    ring
  unfold airyCorrC
  rw [← hd, ← sub_div, ← mul_div_assoc, eq_div_iff hden.ne']
  linear_combination (1 + ε) * h

/-- The remainder factor is uniformly bounded: `|c(ε)| ≤ 1` for `|ε| ≤ 1/2`. -/
lemma abs_airyCorrC_le {ε : ℝ} (hε : |ε| ≤ 1 / 2) : |airyCorrC ε| ≤ 1 := by
  have hden := four_mul_denom_pos hε
  have hden3 : (3 : ℝ) ≤ 4 * (Real.sqrt (1 + ε) + 1 + ε / 2) := by
    have h1 : (0 : ℝ) ≤ Real.sqrt (1 + ε) := Real.sqrt_nonneg _
    have h2 : (3 : ℝ) / 4 ≤ 1 + ε / 2 := by linarith [(abs_le.mp hε).1]
    linarith
  have hnum0 : (0 : ℝ) ≤ 1 + ε := by linarith [(abs_le.mp hε).1]
  have hnum1 : (1 : ℝ) + ε ≤ 3 / 2 := by linarith [(abs_le.mp hε).2]
  have hfrac0 : (0 : ℝ) ≤ (1 + ε) / (4 * (Real.sqrt (1 + ε) + 1 + ε / 2)) :=
    div_nonneg hnum0 hden.le
  have hfrac1 : (1 + ε) / (4 * (Real.sqrt (1 + ε) + 1 + ε / 2)) ≤ 1 / 2 := by
    rw [div_le_iff₀ hden]
    linarith
  unfold airyCorrC
  rw [abs_le]
  constructor <;> linarith

/-! ### Building-block limits -/

lemma tendsto_L_atTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_logL_div_L :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_L_atTop
  simpa [Function.comp_def] using h

lemma tendsto_logL_sq_div_L :
    Tendsto (fun N : ℕ => (Real.log (Real.log (N : ℝ))) ^ 2 / Real.log (N : ℝ))
      atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp tendsto_L_atTop
  simpa [Function.comp_def] using h

lemma tendsto_one_div_L :
    Tendsto (fun N : ℕ => 1 / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp tendsto_L_atTop
  simpa [Function.comp_def, one_div] using h

/-- The relative correction vanishes: `ε_N → 0`. -/
lemma tendsto_epsN : Tendsto epsN atTop (𝓝 0) := by
  have h1 := tendsto_logL_div_L.const_mul (auxA / airyGamma)
  have h2 := tendsto_one_div_L.const_mul (auxB / airyGamma)
  have h := h1.add h2
  simp only [mul_zero, add_zero] at h
  have hdec : (fun N : ℕ => auxA / airyGamma *
        (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) +
      auxB / airyGamma * (1 / Real.log (N : ℝ))) =ᶠ[atTop] epsN := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hL := (log_nat_pos hN).ne'
    have hγ := airyGamma_pos.ne'
    unfold epsN
    field_simp [hL, hγ]
  exact Tendsto.congr' hdec h

lemma epsN_eventually_le : ∀ᶠ N : ℕ in atTop, |epsN N| ≤ 1 / 2 := by
  have h := (Metric.tendsto_nhds.mp tendsto_epsN) (1 / 2) (by norm_num)
  filter_upwards [h] with N hN
  rw [Real.dist_eq, sub_zero] at hN
  exact hN.le

/-! ### Algebra of `a_N`, `b_N`, `u_N` -/

/-- Factorization `a_N = γ L^{2/3} (1 + ε_N)` for `N ≥ 2`. -/
lemma gumbelA_eq {N : ℕ} (hN : 2 ≤ N) :
    gumbelA N = airyGamma * (Real.log (N : ℝ)) ^ ((2 : ℝ) / 3) * (1 + epsN N) := by
  have hL := log_nat_pos hN
  have hγ := airyGamma_pos.ne'
  have h3 : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (-(1 : ℝ) / 3) =
      (Real.log (N : ℝ)) ^ ((2 : ℝ) / 3) := by
    have h := Real.rpow_add hL (1 : ℝ) (-(1 : ℝ) / 3)
    rw [Real.rpow_one, show (1 : ℝ) + -(1 : ℝ) / 3 = 2 / 3 by norm_num] at h
    exact h.symm
  unfold gumbelA epsN auxA auxB
  conv_rhs => rw [mul_add, mul_one]
  rw [add_left_cancel_iff, ← mul_div_assoc,
    eq_div_iff (mul_ne_zero hγ hL.ne')]
  linear_combination
    (airyGamma * ((airyGamma / 9) *
      (Real.log (Real.log (N : ℝ)) + Real.log (3 / (2 * Real.pi ^ 3))))) * h3

lemma gumbelA_pos {N : ℕ} (hN : 2 ≤ N) (hε : |epsN N| ≤ 1 / 2) : 0 < gumbelA N := by
  rw [gumbelA_eq hN]
  exact mul_pos (mul_pos airyGamma_pos (Real.rpow_pos_of_pos (log_nat_pos hN) _))
    (one_add_pos_of_abs_le_half hε)

/-- The scaling sequence is positive: `b_N > 0` for `N ≥ 2`. -/
lemma gumbelB_pos {N : ℕ} (hN : 2 ≤ N) : 0 < gumbelB N := by
  unfold gumbelB
  exact mul_pos (div_pos (mul_pos (by norm_num) airyGamma_pos) (by norm_num))
    (Real.rpow_pos_of_pos (log_nat_pos hN) _)

/-- The real-length scaling is positive: `b_T > 0` for `T > 1`. -/
lemma gumbelBR_pos {T : ℝ} (hT : 1 < T) : 0 < gumbelBR T := by
  unfold gumbelBR
  exact mul_pos (div_pos (mul_pos (by norm_num) airyGamma_pos) (by norm_num))
    (Real.rpow_pos_of_pos (Real.log_pos hT) _)

/-- The key power identity `κ a_N^{3/2} = L (1 + ε_N)^{3/2}`. -/
lemma kappa_gumbelA_rpow {N : ℕ} (hN : 2 ≤ N) (hε : |epsN N| ≤ 1 / 2) :
    airyKappa * (gumbelA N) ^ ((3 : ℝ) / 2) =
      Real.log (N : ℝ) * (1 + epsN N) ^ ((3 : ℝ) / 2) := by
  have hL := log_nat_pos hN
  have h1ε := one_add_pos_of_abs_le_half hε
  rw [gumbelA_eq hN,
    Real.mul_rpow (mul_nonneg airyGamma_pos.le (Real.rpow_nonneg hL.le _)) h1ε.le,
    Real.mul_rpow airyGamma_pos.le (Real.rpow_nonneg hL.le _),
    ← Real.rpow_mul hL.le, show (2 : ℝ) / 3 * (3 / 2) = 1 by norm_num, Real.rpow_one]
  linear_combination
    (Real.log (N : ℝ) * (1 + epsN N) ^ ((3 : ℝ) / 2)) * airyKappa_mul_airyGamma_rpow

lemma log_gumbelA {N : ℕ} (hN : 2 ≤ N) (hε : |epsN N| ≤ 1 / 2) :
    Real.log (gumbelA N) =
      Real.log airyGamma + (2 / 3) * Real.log (Real.log (N : ℝ)) +
        Real.log (1 + epsN N) := by
  have hL := log_nat_pos hN
  have h1ε := one_add_pos_of_abs_le_half hε
  rw [gumbelA_eq hN,
    Real.log_mul (mul_ne_zero airyGamma_pos.ne' (Real.rpow_pos_of_pos hL _).ne') h1ε.ne',
    Real.log_mul airyGamma_pos.ne' (Real.rpow_pos_of_pos hL _).ne',
    Real.log_rpow hL]

lemma three_halves_aux_div (x : ℝ) :
    (3 / 2) * (auxA * x + auxB) / airyGamma =
      x / 6 + Real.log (3 / (2 * Real.pi ^ 3)) / 6 := by
  have hγ := airyGamma_pos.ne'
  unfold auxA auxB
  field_simp [hγ]
  ring

lemma L_mul_epsN {N : ℕ} (hN : 2 ≤ N) :
    Real.log (N : ℝ) * epsN N =
      (auxA * Real.log (Real.log (N : ℝ)) + auxB) / airyGamma := by
  have hL := (log_nat_pos hN).ne'
  have hγ := airyGamma_pos.ne'
  unfold epsN
  field_simp [hL, hγ]

/-- The exact second-order expansion of `H(a_N) - log N`: only the two
vanishing terms survive after the exact cancellation of the constants. -/
lemma airyH_gumbelA_eq {N : ℕ} (hN : 2 ≤ N) (hε : |epsN N| ≤ 1 / 2) :
    airyH (gumbelA N) - Real.log (N : ℝ) =
      Real.log (N : ℝ) * (epsN N) ^ 2 * airyCorrC (epsN N) -
        (1 / 4) * Real.log (1 + epsN N) := by
  have hexpand : Real.log (N : ℝ) * (1 + epsN N) ^ ((3 : ℝ) / 2) =
      Real.log (N : ℝ) + (1 / 6) * Real.log (Real.log (N : ℝ)) +
        Real.log (3 / (2 * Real.pi ^ 3)) / 6 +
          Real.log (N : ℝ) * (epsN N) ^ 2 * airyCorrC (epsN N) := by
    have h1 := rpow_three_halves_one_add hε
    have h2 := three_halves_aux_div (Real.log (Real.log (N : ℝ)))
    have h3 := L_mul_epsN hN
    linear_combination Real.log (N : ℝ) * h1 + (3 / 2) * h3 + h2
  unfold airyH
  rw [kappa_gumbelA_rpow hN hε, log_gumbelA hN hε]
  linear_combination hexpand + airyH_const_zero

/-! ### Centering lemma: `H(a_N) - log N → 0` -/

theorem airyH_gumbelA :
    Tendsto (fun N : ℕ => airyH (gumbelA N) - Real.log N) atTop (𝓝 0) := by
  have h1εt : Tendsto (fun N : ℕ => 1 + epsN N) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_epsN
  have hlogt : Tendsto (fun N : ℕ => Real.log (1 + epsN N)) atTop (𝓝 0) := by
    have hg : Tendsto Real.log (𝓝 (1 + 0 : ℝ)) (𝓝 (Real.log (1 + 0 : ℝ))) :=
      Real.continuousAt_log (by norm_num : (1 : ℝ) + 0 ≠ 0)
    have h := hg.comp h1εt
    simpa [Function.comp_def, Real.log_one] using h
  have hLε2 : Tendsto (fun N : ℕ => Real.log (N : ℝ) * (epsN N) ^ 2) atTop (𝓝 0) := by
    have t1 := tendsto_logL_sq_div_L.const_mul (auxA ^ 2 / airyGamma ^ 2)
    have t2 := tendsto_logL_div_L.const_mul (2 * auxA * auxB / airyGamma ^ 2)
    have t3 := tendsto_one_div_L.const_mul (auxB ^ 2 / airyGamma ^ 2)
    have t := (t1.add t2).add t3
    simp only [mul_zero, add_zero] at t
    have hdec : (fun N : ℕ => auxA ^ 2 / airyGamma ^ 2 *
          ((Real.log (Real.log (N : ℝ))) ^ 2 / Real.log (N : ℝ)) +
        2 * auxA * auxB / airyGamma ^ 2 *
          (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) +
        auxB ^ 2 / airyGamma ^ 2 * (1 / Real.log (N : ℝ))) =ᶠ[atTop]
        (fun N : ℕ => Real.log (N : ℝ) * (epsN N) ^ 2) := by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hL := (log_nat_pos hN).ne'
      have hγ := airyGamma_pos.ne'
      unfold epsN
      field_simp [hL, hγ]
      ring
    exact Tendsto.congr' hdec t
  have hterm1 :
      Tendsto (fun N : ℕ => Real.log (N : ℝ) * (epsN N) ^ 2 * airyCorrC (epsN N))
        atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hLε2
    filter_upwards [eventually_ge_atTop 2, epsN_eventually_le] with N hN hε
    have hL := log_nat_pos hN
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hL,
      abs_of_nonneg (sq_nonneg (epsN N) : (0 : ℝ) ≤ (epsN N) ^ 2)]
    calc Real.log (N : ℝ) * (epsN N) ^ 2 * |airyCorrC (epsN N)|
        ≤ Real.log (N : ℝ) * (epsN N) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (abs_airyCorrC_le hε)
            (mul_nonneg hL.le (sq_nonneg _))
      _ = Real.log (N : ℝ) * (epsN N) ^ 2 := mul_one _
  have h := hterm1.sub (hlogt.const_mul (1 / 4))
  simp only [mul_zero, sub_zero] at h
  apply Tendsto.congr' _ h
  filter_upwards [eventually_ge_atTop 2, epsN_eventually_le] with N hN hε
  exact (airyH_gumbelA_eq hN hε).symm

/-! ### Normalization lemma: the perturbation by `b_N z` -/

lemma gumbelU_eq {z : ℝ} {N : ℕ} (hN : 2 ≤ N) (hε : |epsN N| ≤ 1 / 2) :
    gumbelU N z = gumbelA N * (1 + deltaN z N) := by
  have hA := (gumbelA_pos hN hε).ne'
  unfold gumbelU deltaN
  rw [mul_add, mul_one, add_left_cancel_iff, ← mul_div_assoc, mul_div_cancel_left₀ _ hA]

/-- Explicit form `δ_N = (2z/3) · (1/L) / (1 + ε_N)`. -/
lemma deltaN_eq {z : ℝ} {N : ℕ} (hN : 2 ≤ N) (hε : |epsN N| ≤ 1 / 2) :
    deltaN z N = (2 * z / 3) * (1 / Real.log (N : ℝ)) / (1 + epsN N) := by
  have hL := log_nat_pos hN
  have h1ε := one_add_pos_of_abs_le_half hε
  have hγ := airyGamma_pos.ne'
  have hr : (Real.log (N : ℝ)) ^ (-(1 : ℝ) / 3) =
      (Real.log (N : ℝ)) ⁻¹ * (Real.log (N : ℝ)) ^ ((2 : ℝ) / 3) := by
    have h := Real.rpow_add hL (-1 : ℝ) (2 / 3)
    rw [show (-1 : ℝ) + 2 / 3 = -(1 : ℝ) / 3 by norm_num, Real.rpow_neg_one] at h
    exact h
  unfold deltaN gumbelB
  rw [gumbelA_eq hN, one_div,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hγ (Real.rpow_pos_of_pos hL _).ne') h1ε.ne')
      h1ε.ne']
  linear_combination ((2 * airyGamma / 3) * z * (1 + epsN N)) * hr

/-- The perturbation vanishes: `δ_N → 0`. -/
lemma tendsto_deltaN (z : ℝ) : Tendsto (fun N : ℕ => deltaN z N) atTop (𝓝 0) := by
  have h1εt : Tendsto (fun N : ℕ => 1 + epsN N) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_epsN
  have h := (tendsto_one_div_L.const_mul (2 * z / 3)).div h1εt (by norm_num)
  simp only [mul_zero, zero_div] at h
  apply Tendsto.congr' _ h
  filter_upwards [eventually_ge_atTop 2, epsN_eventually_le] with N hN hε
  exact (deltaN_eq hN hε).symm

/-- The difference `H(u_N(z)) - H(a_N)` in exact form. -/
lemma airyH_gumbelU_diff_eq {z : ℝ} {N : ℕ} (hN : 2 ≤ N) (hε : |epsN N| ≤ 1 / 2)
    (hδ : |deltaN z N| ≤ 1 / 2) :
    airyH (gumbelU N z) - airyH (gumbelA N) =
      (airyKappa * (gumbelA N) ^ ((3 : ℝ) / 2)) *
          ((3 / 2) * deltaN z N + (deltaN z N) ^ 2 * airyCorrC (deltaN z N)) -
        (1 / 4) * Real.log (1 + deltaN z N) := by
  have hA := gumbelA_pos hN hε
  have h1δ : (0 : ℝ) < 1 + deltaN z N := one_add_pos_of_abs_le_half hδ
  have hpow := Real.mul_rpow hA.le h1δ.le (z := ((3 : ℝ) / 2))
  have hlog := Real.log_mul hA.ne' h1δ.ne'
  have hid := rpow_three_halves_one_add hδ
  rw [gumbelU_eq hN hε]
  unfold airyH
  rw [hpow, hlog]
  linear_combination (airyKappa * (gumbelA N) ^ ((3 : ℝ) / 2)) * hid

/-- The main term simplifies exactly: `κ a_N^{3/2} · (3/2) δ_N = z √(1 + ε_N)`. -/
lemma gumbel_main_term_eq {z : ℝ} {N : ℕ} (hN : 2 ≤ N) (hε : |epsN N| ≤ 1 / 2) :
    (airyKappa * (gumbelA N) ^ ((3 : ℝ) / 2)) * ((3 / 2) * deltaN z N) =
      z * Real.sqrt (1 + epsN N) := by
  have hL := log_nat_pos hN
  have h1ε := one_add_pos_of_abs_le_half hε
  have hr2 := rpow_three_halves_eq_mul_sqrt h1ε
  have hLi : Real.log (N : ℝ) * (Real.log (N : ℝ)) ⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
  rw [kappa_gumbelA_rpow hN hε, deltaN_eq hN hε, one_div, ← mul_div_assoc,
    ← mul_div_assoc, div_eq_iff h1ε.ne']
  linear_combination z * hr2 + (z * (1 + epsN N) ^ ((3 : ℝ) / 2)) * hLi

theorem gumbel_normalization (z : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-airyH (gumbelU N z)))
      atTop (𝓝 (Real.exp (-z))) := by
  have hδt := tendsto_deltaN z
  have hδ_ev : ∀ᶠ N : ℕ in atTop, |deltaN z N| ≤ 1 / 2 := by
    have h := (Metric.tendsto_nhds.mp hδt) (1 / 2) (by norm_num)
    filter_upwards [h] with N hN
    rw [Real.dist_eq, sub_zero] at hN
    exact hN.le
  have h1εt : Tendsto (fun N : ℕ => 1 + epsN N) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_epsN
  have hsqrt1 : Tendsto (fun N : ℕ => Real.sqrt (1 + epsN N)) atTop (𝓝 1) := by
    have h := (Real.continuous_sqrt.tendsto (1 + 0)).comp h1εt
    simpa [Function.comp_def, Real.sqrt_one] using h
  have hmain1 : Tendsto
      (fun N : ℕ => (airyKappa * (gumbelA N) ^ ((3 : ℝ) / 2)) * ((3 / 2) * deltaN z N))
      atTop (𝓝 z) := by
    have h := hsqrt1.const_mul z
    simp only [mul_one] at h
    apply Tendsto.congr' _ h
    filter_upwards [eventually_ge_atTop 2, epsN_eventually_le] with N hN hε
    exact (gumbel_main_term_eq hN hε).symm
  have hmain2 : Tendsto
      (fun N : ℕ => (airyKappa * (gumbelA N) ^ ((3 : ℝ) / 2)) *
        ((deltaN z N) ^ 2 * airyCorrC (deltaN z N))) atTop (𝓝 0) := by
    have hC : Tendsto (fun N : ℕ =>
        ((3 / 2 : ℝ) ^ ((3 : ℝ) / 2) * (4 * (2 * z / 3) ^ 2)) * (1 / Real.log (N : ℝ)))
        atTop (𝓝 0) := by
      simpa using tendsto_one_div_L.const_mul _
    apply squeeze_zero_norm' _ hC
    filter_upwards [eventually_ge_atTop 2, epsN_eventually_le, hδ_ev] with N hN hε hδ
    have hL := log_nat_pos hN
    have hA := gumbelA_pos hN hε
    have h1ε := one_add_pos_of_abs_le_half hε
    have hpow_nonneg : (0 : ℝ) ≤ airyKappa * (gumbelA N) ^ ((3 : ℝ) / 2) :=
      mul_nonneg airyKappa_pos.le (Real.rpow_nonneg hA.le _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow_nonneg, abs_mul,
      abs_of_nonneg (sq_nonneg (deltaN z N) : (0 : ℝ) ≤ (deltaN z N) ^ 2)]
    have hb1 : (1 + epsN N) ^ ((3 : ℝ) / 2) ≤ (3 / 2 : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow h1ε.le (by linarith [(abs_le.mp hε).2]) (by norm_num)
    have hb2 : (deltaN z N) ^ 2 ≤ 4 * (2 * z / 3) ^ 2 * (1 / Real.log (N : ℝ)) ^ 2 := by
      have h12 : (1 : ℝ) / 2 ≤ 1 + epsN N := by linarith [(abs_le.mp hε).1]
      have hP : (0 : ℝ) ≤ (2 * z / 3) ^ 2 * (1 / Real.log (N : ℝ)) ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have hQ : (1 : ℝ) ≤ 4 * (1 + epsN N) ^ 2 := by
        have hq4 : ((1 : ℝ) / 2) ^ 2 ≤ (1 + epsN N) ^ 2 :=
          pow_le_pow_left₀ (by norm_num) h12 2
        norm_num at hq4
        linarith
      rw [deltaN_eq hN hε, div_pow, mul_pow, div_le_iff₀ (pow_pos h1ε 2)]
      calc (2 * z / 3) ^ 2 * (1 / Real.log (N : ℝ)) ^ 2
          = (2 * z / 3) ^ 2 * (1 / Real.log (N : ℝ)) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (2 * z / 3) ^ 2 * (1 / Real.log (N : ℝ)) ^ 2 * (4 * (1 + epsN N) ^ 2) :=
            mul_le_mul_of_nonneg_left hQ hP
        _ = 4 * (2 * z / 3) ^ 2 * (1 / Real.log (N : ℝ)) ^ 2 * (1 + epsN N) ^ 2 := by ring
    have hstep : Real.log (N : ℝ) * (1 + epsN N) ^ ((3 : ℝ) / 2) * (deltaN z N) ^ 2 ≤
        ((3 / 2 : ℝ) ^ ((3 : ℝ) / 2) * (4 * (2 * z / 3) ^ 2)) *
          (1 / Real.log (N : ℝ)) := by
      have hLL : Real.log (N : ℝ) * (1 / Real.log (N : ℝ)) ^ 2 = 1 / Real.log (N : ℝ) := by
        field_simp [hL.ne']
      calc Real.log (N : ℝ) * (1 + epsN N) ^ ((3 : ℝ) / 2) * (deltaN z N) ^ 2
          = Real.log (N : ℝ) * ((1 + epsN N) ^ ((3 : ℝ) / 2) * (deltaN z N) ^ 2) := by ring
        _ ≤ Real.log (N : ℝ) * ((3 / 2 : ℝ) ^ ((3 : ℝ) / 2) *
            (4 * (2 * z / 3) ^ 2 * (1 / Real.log (N : ℝ)) ^ 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hb1 hb2 (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)) hL.le
        _ = ((3 / 2 : ℝ) ^ ((3 : ℝ) / 2) * (4 * (2 * z / 3) ^ 2)) *
            (Real.log (N : ℝ) * (1 / Real.log (N : ℝ)) ^ 2) := by ring
        _ = ((3 / 2 : ℝ) ^ ((3 : ℝ) / 2) * (4 * (2 * z / 3) ^ 2)) *
            (1 / Real.log (N : ℝ)) := by rw [hLL]
    calc (airyKappa * (gumbelA N) ^ ((3 : ℝ) / 2)) *
            ((deltaN z N) ^ 2 * |airyCorrC (deltaN z N)|)
        ≤ (airyKappa * (gumbelA N) ^ ((3 : ℝ) / 2)) * ((deltaN z N) ^ 2 * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (abs_airyCorrC_le hδ) (sq_nonneg _))
            hpow_nonneg
      _ = (airyKappa * (gumbelA N) ^ ((3 : ℝ) / 2)) * (deltaN z N) ^ 2 := by rw [mul_one]
      _ = Real.log (N : ℝ) * (1 + epsN N) ^ ((3 : ℝ) / 2) * (deltaN z N) ^ 2 := by
          rw [kappa_gumbelA_rpow hN hε]
      _ ≤ ((3 / 2 : ℝ) ^ ((3 : ℝ) / 2) * (4 * (2 * z / 3) ^ 2)) *
            (1 / Real.log (N : ℝ)) := hstep
  have hlogδ : Tendsto (fun N : ℕ => (1 / 4) * Real.log (1 + deltaN z N)) atTop (𝓝 0) := by
    have h1δt : Tendsto (fun N : ℕ => 1 + deltaN z N) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hδt
    have hg : Tendsto Real.log (𝓝 (1 + 0 : ℝ)) (𝓝 (Real.log (1 + 0 : ℝ))) :=
      Real.continuousAt_log (by norm_num : (1 : ℝ) + 0 ≠ 0)
    have h := hg.comp h1δt
    have h' := h.const_mul (1 / 4)
    simpa [Function.comp_def, Real.log_one] using h'
  have hdiff : Tendsto (fun N : ℕ => airyH (gumbelU N z) - airyH (gumbelA N))
      atTop (𝓝 z) := by
    have hdec : (fun N : ℕ => airyH (gumbelU N z) - airyH (gumbelA N)) =ᶠ[atTop]
        (fun N : ℕ => (airyKappa * (gumbelA N) ^ ((3 : ℝ) / 2)) * ((3 / 2) * deltaN z N) +
          (airyKappa * (gumbelA N) ^ ((3 : ℝ) / 2)) *
            ((deltaN z N) ^ 2 * airyCorrC (deltaN z N)) -
          (1 / 4) * Real.log (1 + deltaN z N)) := by
      filter_upwards [eventually_ge_atTop 2, epsN_eventually_le, hδ_ev] with N hN hε hδ
      rw [airyH_gumbelU_diff_eq hN hε hδ]
      ring
    have h := (hmain1.add hmain2).sub hlogδ
    simp only [add_zero, sub_zero] at h
    exact Tendsto.congr' hdec.symm h
  have hfull : Tendsto (fun N : ℕ => airyH (gumbelU N z) - Real.log (N : ℝ))
      atTop (𝓝 z) := by
    have hdec : (fun N : ℕ => airyH (gumbelU N z) - Real.log (N : ℝ)) =ᶠ[atTop]
        (fun N : ℕ => (airyH (gumbelU N z) - airyH (gumbelA N)) +
          (airyH (gumbelA N) - Real.log (N : ℝ))) := by
      filter_upwards with N
      ring
    have h := hdiff.add airyH_gumbelA
    simp only [add_zero] at h
    exact Tendsto.congr' hdec.symm h
  have hexp : Tendsto (fun N : ℕ => Real.exp (-(airyH (gumbelU N z) - Real.log (N : ℝ))))
      atTop (𝓝 (Real.exp (-z))) := hfull.neg.rexp
  apply Tendsto.congr' _ hexp
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0n : 0 < N := by omega
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0n
  rw [show -(airyH (gumbelU N z) - Real.log (N : ℝ)) =
        Real.log (N : ℝ) - airyH (gumbelU N z) from by ring,
    Real.exp_sub, Real.exp_log hN0, Real.exp_neg, div_eq_mul_inv]

end Airy1Gumbel
