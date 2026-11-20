/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.AiryKernel.TraceExpansion

/-! # Sharp-tail asymptotic assembly

This module assembles the **two-term sharp-tail expansion** of the paper's sharp
one-block tail,

  `π_T(M) = T·ρ(M) + ρ(M)/(4M) + o(ρ(M)/M)`,

from the heat-exact trace expansion (`trace_airyTilde_eq_heat_exact`,
`errorMT_abs_le`, AiryKernel/TraceExpansion.lean), the Hilbert–Schmidt
estimates (`vKernel_sq_integral_le`, `wKernel_sq_integral_le`, packaged as
`hsNorm_airyTilde_le`), the `det₁` first-order remainder
(`norm_one_sub_fredholmDetOne_one_sub_trace_le`, TraceClass/FredholmOne.lean), and the
Schläfli/Airy asymptotics (`schlaefli_master_isEquivalent`,
`integral_airyAiReal_isEquivalent`, Airy/AiryLeading.lean).

## What is proved here

* **Rates for the Schläfli integrals**: the master-lemma asymptotics
  upgraded from `IsEquivalent` to an explicit `O(1/z)` relative rate, via the
  quadratic-gap bound `cosh_sub_one_sub_half_sq_le` (the `cosh s - 1 ≤ (s²/2) cosh s`
  corollary) and the phase gap `z(cosh(u/√z) - 1) - u²/2 = O(u⁴ e^u / z)`:
    `schlaefliK13_sub_lead_abs_le`,
    `neg_deriv_schlaefliK13_sub_lead_abs_le`.
  These give the relative error `(1 + O(A^{-3/2}))` used in the paper.
* **Rate for the Airy derivative** (`neg_deriv_airyAiReal_sub_lead_isBigO`):
  `-Ai'(A) = leadAiDeriv A · (1 + O(A^{-3/2}))` with
  `leadAiDeriv A = (1/(2√π)) A^{1/4} e^{-(2/3) A^{3/2}}`, via the explicit
  derivative formula `airyBesselY1` and the prefactor identity
  `deriv_airyAiReal_prefactor`.
* **The `ρ`-assembly** (`neg_two_mul_T_deriv_sub_T_rhoM_isBigO`):
  `-2T·Ai'(2M) = T·ρ(M) + O(M^{-3/2} ρ(M))`; the exact constant
  identity `2·leadAiDeriv(2M) = ρ(M)` (`two_mul_leadAiDeriv_two_mul`), i.e.
  `2·(1/(2√π))·(2M)^{1/4} = C_*·M^{1/4}` and `(2/3)(2M)^{3/2} = κ M^{3/2}`.
* **The tail two-term** (`integral_Ici_airyAiReal_sub_rhoM_div_isLittleO`):
  `∫_{2M}^∞ Ai = ρ(M)/(4M) + o(ρ(M)/M)`; only `IsEquivalent`
  (`integral_airyAiReal_isEquivalent`) is needed, no rate.
* **Trace assembly** (`traceAiryTilde_sub_traceLead_isLittleO`): the paper's
  two-term trace asymptotic
  `Tr Ã_{M,T} = T·ρ(M) + ρ(M)/(4M) + o(ρ(M)/M)`,
  with the error `ℰ_{M,T}` of the heat-exact trace identity absorbed via
  `|ℰ_{M,T}| ≤ C_T M^{-3/4} e^{-2TM} e^{-κM^{3/2}} = o(ρ(M)/M)`
  (`errorMT_isLittleO_rhoM_div`; the factor `e^{-2TM}` beats any power of `M`).
* **The `det₁` remainder** (`one_sub_detOneAiryTilde_sub_trace_isLittleO`):
  the paper's determinant remainder estimate
  `1 - det₁(1-Ã_{M,T}) = Tr Ã_{M,T} + o(ρ(M)/M)`,
  from `norm_one_sub_fredholmDetOne_one_sub_trace_le` and the Hilbert–Schmidt bound
  `hsNorm Ã ≤ C_T (1+M)√(1+a³) e^{-κM^{3/2}}` at `a = √(2M)`,
  whose square is `o(ρ(M)/M)`.
* **The sharp-tail expansion** (`piT_sub_traceLead_isLittleO`): for any `piT`
  identified with `1 - det₁(1-Ã_{M,T})` by a hypothesis record field
  `hpi : ∀ M, piT M = 1 - detOneAiryTilde M T` (the paper's determinant form of the
  one-block tail, discharged in the main package, `Airy1Gumbel.SharpTail`),
    `piT M = T·ρ(M) + ρ(M)/(4M) + o(ρ(M)/M)`.

## Conventions

* `kappaC = 4√2/3`, `Cstar = 2^{1/4}/√π`,
  `rhoM M = C_* M^{1/4} e^{-κ M^{3/2}}`,
  `traceLead M T = T·ρ(M) + ρ(M)/(4M)` (the two-term lead), all as in the paper.
* `traceAiryTilde M T` and `detOneAiryTilde M T` are total functions with junk value
  `0` outside the valid region `0 < M, T + 1 ≤ √(2M)`; every theorem about them is an
  `atTop` asymptotic, so the junk region is invisible.
* All fractional powers are `Real.rpow` (never `^(3/2)` on `ℝ`: the ℕ-division trap).

The `o(ρ/M)` scale in the trace, `det₁` and sharp-tail statements is not weakened.
-/

namespace AiryConj

open MeasureTheory Real Set Filter
open scoped Asymptotics Topology
open HilbertSchmidt

/-! ## The constants `κ`, `C_*`, `ρ` and the two-term lead -/

section Constants

/-- The Airy-decay constant `κ = 4√2/3`. -/
noncomputable def kappaC : ℝ := 4 * Real.sqrt 2 / 3

/-- The prefactor constant `C_* = 2^{1/4}/√π`. -/
noncomputable def Cstar : ℝ := 2 ^ (1/4 : ℝ) / Real.sqrt Real.pi

/-- The sharp-tail rate function `ρ(M) = C_* M^{1/4} e^{-κ M^{3/2}}`
(as in the paper). -/
noncomputable def rhoM (M : ℝ) : ℝ :=
  Cstar * M ^ (1/4 : ℝ) * Real.exp (-kappaC * M ^ (3/2 : ℝ))

/-- The Airy-derivative leading term `leadAiDeriv A = (1/(2√π)) A^{1/4} e^{-(2/3)A^{3/2}}`. -/
noncomputable def leadAiDeriv (A : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt Real.pi)) * A ^ (1/4 : ℝ) * Real.exp (-(2/3) * A ^ (3/2 : ℝ))

/-- The two-term trace lead `traceLead M T = T·ρ(M) + ρ(M)/(4M)`. -/
noncomputable def traceLead (M T : ℝ) : ℝ := T * rhoM M + rhoM M / (4 * M)

theorem kappaC_pos : 0 < kappaC :=
  div_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num))) (by norm_num)

theorem Cstar_pos : 0 < Cstar :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.sqrt_pos.2 Real.pi_pos)

theorem rhoM_pos (hM : 0 < M) : 0 < rhoM M :=
  mul_pos (mul_pos Cstar_pos (Real.rpow_pos_of_pos hM _)) (Real.exp_pos _)

theorem leadAiDeriv_pos (hA : 0 < A) : 0 < leadAiDeriv A :=
  mul_pos (mul_pos (div_pos one_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 Real.pi_pos)))
    (Real.rpow_pos_of_pos hA _)) (Real.exp_pos _)

/-- `(2M)^{3/2} = 2√2 · M^{3/2}` for `0 ≤ M` (all `rpow`). -/
theorem two_mul_rpow_three_halves (hM : 0 ≤ M) :
    (2 * M) ^ (3/2 : ℝ) = 2 * Real.sqrt 2 * M ^ (3/2 : ℝ) := by
  rw [Real.mul_rpow (by norm_num) hM]
  congr 1
  rw [show (3/2 : ℝ) = 1 + 1/2 from by norm_num, Real.rpow_add (by norm_num),
    Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- The exponent identity `κ·M^{3/2} = (2/3)(2M)^{3/2}` for `0 ≤ M`. -/
theorem kappaC_mul_rpow_eq (hM : 0 ≤ M) :
    kappaC * M ^ (3/2 : ℝ) = (2/3) * (2 * M) ^ (3/2 : ℝ) := by
  rw [two_mul_rpow_three_halves hM]
  unfold kappaC
  ring

/-- The negated exponent identity `-(2/3)(2M)^{3/2} = -κ·M^{3/2}` for `0 ≤ M`. -/
theorem neg_two_thirds_mul_two_mul_rpow (hM : 0 ≤ M) :
    -(2/3 : ℝ) * (2 * M) ^ (3/2 : ℝ) = -kappaC * M ^ (3/2 : ℝ) := by
  rw [neg_mul, neg_mul, kappaC_mul_rpow_eq hM]

/-- `(2M)^{1/4} = 2^{1/4} · M^{1/4}` for `0 ≤ M`. -/
theorem two_mul_rpow_one_quarter (hM : 0 ≤ M) :
    (2 * M) ^ (1/4 : ℝ) = (2 : ℝ) ^ (1/4 : ℝ) * M ^ (1/4 : ℝ) :=
  Real.mul_rpow (by norm_num) hM

/-- `(2M)^{-3/4} = 2^{-3/4} · M^{-3/4}` for `0 ≤ M`. -/
theorem two_mul_rpow_neg_three_quarters (hM : 0 ≤ M) :
    (2 * M) ^ (-3/4 : ℝ) = (2 : ℝ) ^ (-3/4 : ℝ) * M ^ (-3/4 : ℝ) :=
  Real.mul_rpow (by norm_num) hM

/-- `(2M)^{-3/2} = 2^{-3/2} · M^{-3/2}` for `0 ≤ M`. -/
theorem two_mul_rpow_neg_three_halves (hM : 0 ≤ M) :
    (2 * M) ^ (-3/2 : ℝ) = (2 : ℝ) ^ (-3/2 : ℝ) * M ^ (-3/2 : ℝ) :=
  Real.mul_rpow (by norm_num) hM

/-- The exact constant identity behind the `ρ`-assembly:
`2 · leadAiDeriv (2M) = ρ(M)` for `0 < M`, i.e.
`2·(1/(2√π))·(2M)^{1/4} e^{-(2/3)(2M)^{3/2}} = C_* M^{1/4} e^{-κ M^{3/2}}`. -/
theorem two_mul_leadAiDeriv_two_mul (hM : 0 < M) :
    2 * leadAiDeriv (2 * M) = rhoM M := by
  unfold leadAiDeriv rhoM Cstar
  rw [two_mul_rpow_one_quarter hM.le, neg_two_thirds_mul_two_mul_rpow hM.le]
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp

/-- The exact identity behind the tail two-term: the tail-integral lead at
`A = 2M` is `ρ(M)/(4M)`, i.e. `(1/(2√π))(2M)^{-3/4} e^{-(2/3)(2M)^{3/2}} =
ρ(M)/(4M)` for `0 < M`. -/
theorem leadIntegral_two_mul_eq_rhoM_div (hM : 0 < M) :
    (1 / (2 * Real.sqrt Real.pi)) * (2 * M) ^ (-3/4 : ℝ) *
        Real.exp (-(2/3) * (2 * M) ^ (3/2 : ℝ))
      = rhoM M / (4 * M) := by
  unfold rhoM Cstar
  rw [two_mul_rpow_neg_three_quarters hM.le, neg_two_thirds_mul_two_mul_rpow hM.le]
  have h2 : (2 : ℝ) ^ (1/4 : ℝ) / 4 = (1/2) * (2 : ℝ) ^ (-3/4 : ℝ) := by
    rw [div_eq_iff (by norm_num : (4:ℝ) ≠ 0),
      show (1/2 : ℝ) * (2 : ℝ) ^ (-3/4 : ℝ) * 4 = (2 : ℝ) ^ (-3/4 : ℝ) * 2 ^ (1 : ℝ) from by
        rw [Real.rpow_one]; ring,
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      show (-3/4 + 1 : ℝ) = 1/4 by norm_num]
  have hC : (2 : ℝ) ^ (1/4 : ℝ) / Real.sqrt Real.pi / 4
      = (1 / (2 * Real.sqrt Real.pi)) * (2 : ℝ) ^ (-3/4 : ℝ) := by
    calc (2 : ℝ) ^ (1/4 : ℝ) / Real.sqrt Real.pi / 4
        = ((2 : ℝ) ^ (1/4 : ℝ) / 4) / Real.sqrt Real.pi := by ring
      _ = ((1/2) * (2 : ℝ) ^ (-3/4 : ℝ)) / Real.sqrt Real.pi := by rw [h2]
      _ = (1 / (2 * Real.sqrt Real.pi)) * (2 : ℝ) ^ (-3/4 : ℝ) := by ring
  have hM34 : M ^ (1/4 : ℝ) / M = M ^ (-3/4 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hM]
    norm_num
  rw [show (2 : ℝ) ^ (1/4 : ℝ) / Real.sqrt Real.pi * M ^ (1/4 : ℝ) *
        Real.exp (-kappaC * M ^ (3/2 : ℝ)) / (4 * M)
      = ((2 : ℝ) ^ (1/4 : ℝ) / Real.sqrt Real.pi / 4) * (M ^ (1/4 : ℝ) / M) *
        Real.exp (-kappaC * M ^ (3/2 : ℝ)) from by ring]
  rw [hM34, hC]
  ring

end Constants

/-! ## Moment integrability and the Schläfli envelope estimates -/

section SchlaefliRate

/-- Polynomial-exponential moments are integrable on `(0, ∞)`: for `k : ℕ` and any
linear drift `c`, `u ↦ u^k e^{c u - u²/2}` is integrable on `Ioi 0` (dominated by
`e^{c²} u^k e^{-u²/4}`, since `c u - u²/2 ≤ c² - u²/4` from `(u/2 - c)² ≥ 0`). -/
theorem integrableOn_pow_mul_exp_linear_sub_half_sq (k : ℕ) (c : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (c * u - u ^ 2 / 2)) (Set.Ioi 0) := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hg : IntegrableOn
      (fun u : ℝ => Real.exp (c ^ 2) * (u ^ (k : ℝ) * Real.exp (-(1/4) * u ^ 2)))
      (Set.Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1/4) (s := (k : ℝ)) (by norm_num)
      hk).const_mul _
  refine hg.mono' ?_ ?_
  · exact ((continuous_pow k).mul (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub
        ((continuous_pow 2).div_const 2)))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu0 : (0:ℝ) ≤ u := (mem_Ioi.mp hu).le
    have hexp : Real.exp (c * u - u ^ 2 / 2)
        ≤ Real.exp (c ^ 2) * Real.exp (-(1/4) * u ^ 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (u / 2 - c)])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hu0 k) (Real.exp_pos _).le)]
    calc u ^ k * Real.exp (c * u - u ^ 2 / 2)
        ≤ u ^ k * (Real.exp (c ^ 2) * Real.exp (-(1/4) * u ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp (pow_nonneg hu0 k)
      _ = Real.exp (c ^ 2) * (u ^ (k : ℝ) * Real.exp (-(1/4) * u ^ 2)) := by
          rw [Real.rpow_natCast]; ring

/-- The Schläfli Gaussian envelope: for `0 < z` and `0 ≤ u`,
`e^{-z(\cosh(u/√z) - 1)} ≤ e^{-u²/2}` (the quadratic lower bound for `cosh`). -/
theorem exp_neg_cosh_sub_one_le {z u : ℝ} (hz : 0 < z) (hu : 0 ≤ u) :
    Real.exp (-z * (Real.cosh (u / Real.sqrt z) - 1)) ≤ Real.exp (-(u ^ 2 / 2)) := by
  rw [neg_mul]
  exact Real.exp_le_exp.2 (neg_le_neg (mul_cosh_div_sqrt_sub_one_ge hz hu))

/-- The secondary `cosh` factor is at most `e^{u/3}` for `1 ≤ z` and `0 ≤ u`. -/
theorem cosh_div_sqrt_div_three_le {z u : ℝ} (hz : 1 ≤ z) (hu : 0 ≤ u) :
    Real.cosh (u / Real.sqrt z / 3) ≤ Real.exp (u / 3) := by
  have hdiv : u / Real.sqrt z ≤ u := by
    calc u / Real.sqrt z ≤ u / 1 :=
          div_le_div_of_nonneg_left hu zero_lt_one (Real.one_le_sqrt.2 hz)
      _ = u := div_one u
  calc Real.cosh (u / Real.sqrt z / 3) ≤ Real.exp |u / Real.sqrt z / 3| :=
        cosh_le_exp_abs _
    _ = Real.exp (u / Real.sqrt z / 3) := by
        congr 1
        exact abs_of_nonneg
          (div_nonneg (div_nonneg hu (Real.sqrt_nonneg z)) (by norm_num))
    _ ≤ Real.exp (u / 3) :=
        Real.exp_le_exp.2
          ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 3)).2 hdiv)

/-- The rescaled Schläfli integrand is dominated by the Gaussian envelope times
`e^{u/3}`: for `1 ≤ z` and `0 ≤ u`, `airyLeadF z u ≤ e^{-u²/2} e^{u/3}`. -/
theorem airyLeadF_le {z u : ℝ} (hz : 1 ≤ z) (hu : 0 ≤ u) :
    airyLeadF z u ≤ Real.exp (-(u ^ 2 / 2)) * Real.exp (u / 3) := by
  have hz0 : (0:ℝ) < z := by linarith
  unfold airyLeadF
  exact mul_le_mul (exp_neg_cosh_sub_one_le hz0 hu) (cosh_div_sqrt_div_three_le hz hu)
    (Real.cosh_pos _).le (Real.exp_pos _).le

/-- The rescaled Schläfli integrand is integrable on `(0, ∞)` for `1 ≤ z`. -/
theorem integrableOn_airyLeadF {z : ℝ} (hz : 1 ≤ z) :
    IntegrableOn (fun u => airyLeadF z u) (Set.Ioi 0) := by
  have hg : IntegrableOn (fun u : ℝ => Real.exp ((1/3) * u - u ^ 2 / 2)) (Set.Ioi 0) := by
    have h := integrableOn_pow_mul_exp_linear_sub_half_sq 0 (1/3)
    refine h.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_)
    simp
  refine hg.mono' (continuous_airyLeadF z).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
  have hu0 : (0:ℝ) ≤ u := (mem_Ioi.mp hu).le
  have hnn : (0:ℝ) ≤ airyLeadF z u := mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc airyLeadF z u ≤ Real.exp (-(u ^ 2 / 2)) * Real.exp (u / 3) := airyLeadF_le hz hu0
    _ = Real.exp ((1/3) * u - u ^ 2 / 2) := by
        rw [← Real.exp_add]; congr 1; ring

/-- `cosh s - 1 ≤ (s²/2) cosh s` for all `s` (rearrangement of
`cosh_sub_one_sub_half_sq_le`). -/
theorem cosh_sub_one_le (s : ℝ) : Real.cosh s - 1 ≤ (s ^ 2 / 2) * Real.cosh s := by
  have h := cosh_sub_one_sub_half_sq_le s
  have he : (s ^ 2 / 2) * (Real.cosh s - 1) = (s ^ 2 / 2) * Real.cosh s - s ^ 2 / 2 := by
    ring
  linarith

/-- The phase gap is nonnegative: `u²/2 ≤ z(cosh(u/√z) - 1)`. -/
theorem phase_gap_nonneg {z u : ℝ} (hz : 0 < z) (hu : 0 ≤ u) :
    0 ≤ z * (Real.cosh (u / Real.sqrt z) - 1) - u ^ 2 / 2 := by
  have h := mul_cosh_div_sqrt_sub_one_ge hz hu
  linarith

/-- The phase-gap rate: for `1 ≤ z` and `0 ≤ u`,
`z(cosh(u/√z) - 1) - u²/2 ≤ (u⁴/(4z)) e^u`.  This is the `O(u⁴/z)` gap
behind the `O(1/z)` master-lemma rate. -/
theorem phase_gap_le {z u : ℝ} (hz : 1 ≤ z) (hu : 0 ≤ u) :
    z * (Real.cosh (u / Real.sqrt z) - 1) - u ^ 2 / 2
      ≤ (u ^ 4 / (4 * z)) * Real.exp u := by
  have hz0 : (0:ℝ) < z := by linarith
  have hsz : (0:ℝ) < Real.sqrt z := Real.sqrt_pos.2 hz0
  have hzs : z * ((u / Real.sqrt z) ^ 2 / 2) = u ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt hz0.le]
    field_simp [hz0.ne']
  have h1 := cosh_sub_one_sub_half_sq_le (u / Real.sqrt z)
  have h2 : z * (Real.cosh (u / Real.sqrt z) - 1) - u ^ 2 / 2
      ≤ (u ^ 2 / 2) * (Real.cosh (u / Real.sqrt z) - 1) := by
    have hznn : (0:ℝ) ≤ z := hz0.le
    have hmul := mul_le_mul_of_nonneg_left h1 hznn
    rw [mul_sub, hzs] at hmul
    have hass : z * ((u / Real.sqrt z) ^ 2 / 2 * (Real.cosh (u / Real.sqrt z) - 1))
        = (u ^ 2 / 2) * (Real.cosh (u / Real.sqrt z) - 1) := by
      rw [← mul_assoc, hzs]
    rwa [hass] at hmul
  have h3 : (u ^ 2 / 2) * (Real.cosh (u / Real.sqrt z) - 1)
      ≤ (u ^ 4 / (4 * z)) * Real.exp u := by
    have hc := cosh_sub_one_le (u / Real.sqrt z)
    have h4 : (u ^ 2 / 2) * (Real.cosh (u / Real.sqrt z) - 1)
        ≤ (u ^ 2 / 2) * (((u / Real.sqrt z) ^ 2 / 2) * Real.cosh (u / Real.sqrt z)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    have h5 : (u ^ 2 / 2) * (((u / Real.sqrt z) ^ 2 / 2) * Real.cosh (u / Real.sqrt z))
        = (u ^ 4 / (4 * z)) * Real.cosh (u / Real.sqrt z) := by
      rw [div_pow, Real.sq_sqrt hz0.le]
      field_simp [hz0.ne']
      ring
    have hcosh : Real.cosh (u / Real.sqrt z) ≤ Real.exp u := by
      calc Real.cosh (u / Real.sqrt z) ≤ Real.exp |u / Real.sqrt z| := cosh_le_exp_abs _
        _ = Real.exp (u / Real.sqrt z) :=
            by rw [abs_of_nonneg (div_nonneg hu (Real.sqrt_nonneg z))]
        _ ≤ Real.exp u := Real.exp_le_exp.2 (by
            rw [div_le_iff₀ hsz]
            calc u = u * 1 := (mul_one u).symm
              _ ≤ u * Real.sqrt z :=
                  mul_le_mul_of_nonneg_left (Real.one_le_sqrt.2 hz) hu)
    exact h4.trans (h5.le.trans (mul_le_mul_of_nonneg_left hcosh (by positivity)))
  exact h2.trans h3

end SchlaefliRate

/-! ## The pointwise master estimate and the `O(1/z)` Schläfli rate -/

section CoreRate

/-- **The pointwise master estimate**: for `1 ≤ z` and `0 ≤ u`, the rescaled
Schläfli integrand differs from the Gaussian `e^{-u²/2}` by at most
`e^{-u²/2}·((u²/(18z)) e^{u/3} + (u⁴/(4z)) e^u)`.  Decomposing

  `airyLeadF z u − e^{-u²/2} = e^{-u²/2}(e^{-φ}(cosh(u/(3√z)) − 1) + (e^{-φ} − 1))`

with the phase gap `φ = z(cosh(u/√z) − 1) − u²/2 ∈ [0, (u⁴/(4z)) e^u]`
(`phase_gap_nonneg`, `phase_gap_le`), `cosh(s) − 1 ≤ (s²/2) cosh s`
(`cosh_sub_one_le`), and `1 − e^{-φ} ≤ φ` (from `x + 1 ≤ e^x`). -/
theorem airyLeadF_sub_gaussian_abs_le {z u : ℝ} (hz : 1 ≤ z) (hu : 0 ≤ u) :
    |airyLeadF z u - Real.exp (-(u ^ 2 / 2))|
      ≤ Real.exp (-(u ^ 2 / 2)) * ((u ^ 2 / (18 * z)) * Real.exp (u / 3)
          + (u ^ 4 / (4 * z)) * Real.exp u) := by
  have hz0 : (0:ℝ) < z := by linarith
  have hφnn := phase_gap_nonneg hz0 hu
  have hφle := phase_gap_le hz hu
  set φ := z * (Real.cosh (u / Real.sqrt z) - 1) - u ^ 2 / 2 with hφ_def
  have hexp : Real.exp (-z * (Real.cosh (u / Real.sqrt z) - 1))
      = Real.exp (-(u ^ 2 / 2)) * Real.exp (-φ) := by
    rw [← Real.exp_add]
    congr 1
    rw [hφ_def]
    ring
  have hdiff : airyLeadF z u - Real.exp (-(u ^ 2 / 2))
      = Real.exp (-(u ^ 2 / 2)) * (Real.exp (-φ) * (Real.cosh (u / Real.sqrt z / 3) - 1)
          + (Real.exp (-φ) - 1)) := by
    unfold airyLeadF
    rw [hexp]
    ring
  have hexpφ : Real.exp (-φ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hcosh1 : (0:ℝ) ≤ Real.cosh (u / Real.sqrt z / 3) - 1 := by
    have h := Real.one_le_cosh (u / Real.sqrt z / 3)
    linarith
  have hone : (0:ℝ) ≤ 1 - Real.exp (-φ) := by linarith
  have h1m : 1 - Real.exp (-φ) ≤ φ := by
    have h := Real.add_one_le_exp (-φ)
    linarith
  have hcoshbound : Real.cosh (u / Real.sqrt z / 3) - 1
      ≤ (u ^ 2 / (18 * z)) * Real.exp (u / 3) := by
    have h1 := cosh_sub_one_le (u / Real.sqrt z / 3)
    have h2 : ((u / Real.sqrt z / 3) ^ 2 / 2) = u ^ 2 / (18 * z) := by
      rw [div_pow, div_pow, Real.sq_sqrt hz0.le]
      field_simp [hz0.ne']
      ring
    have h3 := cosh_div_sqrt_div_three_le hz hu
    calc Real.cosh (u / Real.sqrt z / 3) - 1
        ≤ ((u / Real.sqrt z / 3) ^ 2 / 2) * Real.cosh (u / Real.sqrt z / 3) := h1
      _ = (u ^ 2 / (18 * z)) * Real.cosh (u / Real.sqrt z / 3) := by rw [h2]
      _ ≤ (u ^ 2 / (18 * z)) * Real.exp (u / 3) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  rw [hdiff, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hA : (0:ℝ) ≤ Real.exp (-φ) * (Real.cosh (u / Real.sqrt z / 3) - 1) :=
    mul_nonneg (Real.exp_pos _).le hcosh1
  have hB : Real.exp (-φ) - 1 ≤ 0 := by linarith
  calc |Real.exp (-φ) * (Real.cosh (u / Real.sqrt z / 3) - 1) + (Real.exp (-φ) - 1)|
      ≤ |Real.exp (-φ) * (Real.cosh (u / Real.sqrt z / 3) - 1)| + |Real.exp (-φ) - 1| :=
        abs_add_le _ _
    _ = Real.exp (-φ) * (Real.cosh (u / Real.sqrt z / 3) - 1) + (1 - Real.exp (-φ)) := by
        rw [abs_of_nonneg hA, abs_of_nonpos hB]
        ring
    _ ≤ (Real.cosh (u / Real.sqrt z / 3) - 1) + φ := by
        have hle : Real.exp (-φ) * (Real.cosh (u / Real.sqrt z / 3) - 1)
            ≤ Real.cosh (u / Real.sqrt z / 3) - 1 := by
          calc Real.exp (-φ) * (Real.cosh (u / Real.sqrt z / 3) - 1)
              ≤ 1 * (Real.cosh (u / Real.sqrt z / 3) - 1) :=
                mul_le_mul_of_nonneg_right hexpφ hcosh1
            _ = Real.cosh (u / Real.sqrt z / 3) - 1 := one_mul _
        linarith
    _ ≤ (u ^ 2 / (18 * z)) * Real.exp (u / 3) + (u ^ 4 / (4 * z)) * Real.exp u :=
        add_le_add hcoshbound hφle

/-- The Gaussian integral value: `∫₀^∞ e^{-u²/2} du = √(π/2)`. -/
theorem integral_exp_neg_half_sq_eq_sqrt_pi_div_two :
    ∫ u in Set.Ioi 0, Real.exp (-(1/2) * u ^ 2) = Real.sqrt (Real.pi / 2) := by
  have h := sqrt_two_div_pi_mul_integral_exp_neg_half_sq
  have h2 : Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2) = 1 := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 / Real.pi),
      show (2 / Real.pi) * (Real.pi / 2) = 1 from by field_simp [Real.pi_ne_zero],
      Real.sqrt_one]
  have h4 : Real.sqrt (Real.pi / 2) = (Real.sqrt (2 / Real.pi))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h2)
  rw [h4]
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h)

/-- **The Schläfli rate estimate** (core of the Schläfli rate): the rescaled Schläfli integral
approaches the Gaussian value with rate `1/z`:
`|∫₀^∞ airyLeadF z − √(π/2)| ≤ C·z⁻¹` for `1 ≤ z`.  Integrating the pointwise master
estimate `airyLeadF_sub_gaussian_abs_le`, with the moments
`∫₀^∞ u² e^{u/3 − u²/2}` and `∫₀^∞ u⁴ e^{u − u²/2}` finite
(`integrableOn_pow_mul_exp_linear_sub_half_sq`). -/
theorem integral_airyLeadF_sub_sqrt_pi_div_two_abs_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 1 ≤ z →
      |(∫ u in Set.Ioi 0, airyLeadF z u) - Real.sqrt (Real.pi / 2)| ≤ C * z⁻¹ := by
  have hJ2 := integrableOn_pow_mul_exp_linear_sub_half_sq 2 (1/3)
  have hJ4 := integrableOn_pow_mul_exp_linear_sub_half_sq 4 1
  have hJ2nn : (0:ℝ) ≤ ∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu => by positivity
  have hJ4nn : (0:ℝ) ≤ ∫ u in Set.Ioi 0, u ^ 4 * Real.exp (1 * u - u ^ 2 / 2) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu => by positivity
  refine ⟨(1/18) * (∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))
      + (1/4) * (∫ u in Set.Ioi 0, u ^ 4 * Real.exp (1 * u - u ^ 2 / 2)),
      by positivity, fun z hz => ?_⟩
  have hFint : IntegrableOn (fun u => airyLeadF z u) (Set.Ioi 0) :=
    integrableOn_airyLeadF hz
  have hGint : IntegrableOn (fun u => Real.exp (-(1/2) * u ^ 2)) (Set.Ioi 0) := by
    have h := integrableOn_pow_mul_exp_linear_sub_half_sq 0 0
    refine h.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_)
    show u ^ 0 * Real.exp (0 * u - u ^ 2 / 2) = Real.exp (-(1/2) * u ^ 2)
    rw [pow_zero, one_mul, zero_mul, zero_sub]
    congr 1
    ring
  have hsplit : (∫ u in Set.Ioi 0, airyLeadF z u) - Real.sqrt (Real.pi / 2)
      = ∫ u in Set.Ioi 0, (airyLeadF z u - Real.exp (-(1/2) * u ^ 2)) := by
    rw [← integral_exp_neg_half_sq_eq_sqrt_pi_div_two]
    exact (integral_sub hFint hGint).symm
  have hBint : IntegrableOn (fun u => Real.exp (-(u ^ 2 / 2)) *
        ((u ^ 2 / (18 * z)) * Real.exp (u / 3) + (u ^ 4 / (4 * z)) * Real.exp u))
      (Set.Ioi 0) := by
    have h2' := hJ2.const_mul (1 / (18 * z))
    have h4' := hJ4.const_mul (1 / (4 * z))
    refine (h2'.add h4').congr (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
    show (1 / (18 * z)) * (u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))
        + (1 / (4 * z)) * (u ^ 4 * Real.exp (1 * u - u ^ 2 / 2))
      = Real.exp (-(u ^ 2 / 2)) * ((u ^ 2 / (18 * z)) * Real.exp (u / 3)
          + (u ^ 4 / (4 * z)) * Real.exp u)
    rw [show Real.exp ((1/3) * u - u ^ 2 / 2)
          = Real.exp (u / 3) * Real.exp (-(u ^ 2 / 2)) from by
          rw [← Real.exp_add]; congr 1; ring,
        show Real.exp (1 * u - u ^ 2 / 2)
          = Real.exp u * Real.exp (-(u ^ 2 / 2)) from by
          rw [← Real.exp_add]; congr 1; ring]
    ring
  rw [hsplit]
  calc |∫ u in Set.Ioi 0, (airyLeadF z u - Real.exp (-(1/2) * u ^ 2))|
      = ‖∫ u in Set.Ioi 0, (airyLeadF z u - Real.exp (-(1/2) * u ^ 2))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ u in Set.Ioi 0, ‖airyLeadF z u - Real.exp (-(1/2) * u ^ 2)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u in Set.Ioi 0, Real.exp (-(u ^ 2 / 2)) *
          ((u ^ 2 / (18 * z)) * Real.exp (u / 3) + (u ^ 4 / (4 * z)) * Real.exp u) := by
        refine setIntegral_mono_on (hFint.sub hGint).norm hBint measurableSet_Ioi
          fun u hu => ?_
        have hu0 : (0:ℝ) ≤ u := (mem_Ioi.mp hu).le
        rw [Real.norm_eq_abs,
          show Real.exp (-(1/2) * u ^ 2) = Real.exp (-(u ^ 2 / 2)) from by
            congr 1; ring]
        exact airyLeadF_sub_gaussian_abs_le hz hu0
    _ = (1 / (18 * z)) * (∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))
          + (1 / (4 * z)) * (∫ u in Set.Ioi 0, u ^ 4 * Real.exp (1 * u - u ^ 2 / 2)) := by
        have hcongr : (∫ u in Set.Ioi 0, Real.exp (-(u ^ 2 / 2)) *
              ((u ^ 2 / (18 * z)) * Real.exp (u / 3) + (u ^ 4 / (4 * z)) * Real.exp u))
            = ∫ u in Set.Ioi 0, ((1 / (18 * z)) * (u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))
              + (1 / (4 * z)) * (u ^ 4 * Real.exp (1 * u - u ^ 2 / 2))) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          show Real.exp (-(u ^ 2 / 2)) * (u ^ 2 / (18 * z) * Real.exp (u / 3)
                + u ^ 4 / (4 * z) * Real.exp u)
            = (1 / (18 * z)) * (u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))
              + (1 / (4 * z)) * (u ^ 4 * Real.exp (1 * u - u ^ 2 / 2))
          rw [show Real.exp ((1/3) * u - u ^ 2 / 2)
                = Real.exp (u / 3) * Real.exp (-(u ^ 2 / 2)) from by
                rw [← Real.exp_add]; congr 1; ring,
              show Real.exp (1 * u - u ^ 2 / 2)
                = Real.exp u * Real.exp (-(u ^ 2 / 2)) from by
                rw [← Real.exp_add]; congr 1; ring]
          ring
        rw [hcongr, integral_add (hJ2.const_mul _) (hJ4.const_mul _),
          integral_const_mul, integral_const_mul]
    _ = ((1/18) * (∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))
          + (1/4) * (∫ u in Set.Ioi 0, u ^ 4 * Real.exp (1 * u - u ^ 2 / 2))) * z⁻¹ := by
        rw [show (1 / (18 * z)) = (1/18) * z⁻¹ from by
              rw [div_eq_mul_inv, mul_inv, one_mul, inv_eq_one_div],
            show (1 / (4 * z)) = (1/4) * z⁻¹ from by
              rw [div_eq_mul_inv, mul_inv, one_mul, inv_eq_one_div]]
        ring

/-- The cosh-weight deviation: for `1 ≤ z` and `0 ≤ u`,
`cosh(u/√z) − 1 ≤ (u²/(2z)) e^u`. -/
theorem cosh_div_sqrt_sub_one_le {z u : ℝ} (hz : 1 ≤ z) (hu : 0 ≤ u) :
    Real.cosh (u / Real.sqrt z) - 1 ≤ (u ^ 2 / (2 * z)) * Real.exp u := by
  have hz0 : (0:ℝ) < z := by linarith
  have hsz : (0:ℝ) < Real.sqrt z := Real.sqrt_pos.2 hz0
  have h1 := cosh_sub_one_le (u / Real.sqrt z)
  have h2 : ((u / Real.sqrt z) ^ 2 / 2) = u ^ 2 / (2 * z) := by
    rw [div_pow, Real.sq_sqrt hz0.le]
    field_simp [hz0.ne']
  have hcosh : Real.cosh (u / Real.sqrt z) ≤ Real.exp u := by
    calc Real.cosh (u / Real.sqrt z) ≤ Real.exp |u / Real.sqrt z| := cosh_le_exp_abs _
      _ = Real.exp (u / Real.sqrt z) :=
          by rw [abs_of_nonneg (div_nonneg hu (Real.sqrt_nonneg z))]
      _ ≤ Real.exp u := Real.exp_le_exp.2 (by
          rw [div_le_iff₀ hsz]
          calc u = u * 1 := (mul_one u).symm
            _ ≤ u * Real.sqrt z := mul_le_mul_of_nonneg_left (Real.one_le_sqrt.2 hz) hu)
  calc Real.cosh (u / Real.sqrt z) - 1
      ≤ ((u / Real.sqrt z) ^ 2 / 2) * Real.cosh (u / Real.sqrt z) := h1
    _ = (u ^ 2 / (2 * z)) * Real.cosh (u / Real.sqrt z) := by rw [h2]
    _ ≤ (u ^ 2 / (2 * z)) * Real.exp u :=
        mul_le_mul_of_nonneg_left hcosh (by positivity)

/-- **The cosh-weighted Schläfli rate estimate** (core of the derivative rate): the rescaled
derivative
integrand approaches the Gaussian value with rate `1/z`:
`|∫₀^∞ cosh(u/√z)·airyLeadF z − √(π/2)| ≤ C·z⁻¹` for `1 ≤ z`, with the extra moment
`∫₀^∞ u² e^{4u/3 − u²/2}` finite. -/
theorem integral_cosh_airyLeadF_sub_sqrt_pi_div_two_abs_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 1 ≤ z →
      |(∫ u in Set.Ioi 0, Real.cosh (u / Real.sqrt z) * airyLeadF z u)
        - Real.sqrt (Real.pi / 2)| ≤ C * z⁻¹ := by
  have hJ2 := integrableOn_pow_mul_exp_linear_sub_half_sq 2 (1/3)
  have hJ4 := integrableOn_pow_mul_exp_linear_sub_half_sq 4 1
  have hJ2' := integrableOn_pow_mul_exp_linear_sub_half_sq 2 (4/3)
  have hJ2nn : (0:ℝ) ≤ ∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu => by positivity
  have hJ4nn : (0:ℝ) ≤ ∫ u in Set.Ioi 0, u ^ 4 * Real.exp (1 * u - u ^ 2 / 2) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu => by positivity
  have hJ2'nn : (0:ℝ) ≤ ∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((4/3) * u - u ^ 2 / 2) :=
    setIntegral_nonneg measurableSet_Ioi fun u hu => by positivity
  refine ⟨(1/2) * (∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((4/3) * u - u ^ 2 / 2))
      + (1/18) * (∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))
      + (1/4) * (∫ u in Set.Ioi 0, u ^ 4 * Real.exp (1 * u - u ^ 2 / 2)),
      by positivity, fun z hz => ?_⟩
  have hFint : IntegrableOn (fun u => airyLeadF z u) (Set.Ioi 0) :=
    integrableOn_airyLeadF hz
  have hGint : IntegrableOn (fun u => Real.exp (-(1/2) * u ^ 2)) (Set.Ioi 0) := by
    have h := integrableOn_pow_mul_exp_linear_sub_half_sq 0 0
    refine h.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_)
    show u ^ 0 * Real.exp (0 * u - u ^ 2 / 2) = Real.exp (-(1/2) * u ^ 2)
    rw [pow_zero, one_mul, zero_mul, zero_sub]
    congr 1
    ring
  have hWFint : IntegrableOn (fun u => Real.cosh (u / Real.sqrt z) * airyLeadF z u)
      (Set.Ioi 0) := by
    have henv : IntegrableOn (fun u => Real.exp ((1/3) * u - u ^ 2 / 2)) (Set.Ioi 0) := by
      have h := integrableOn_pow_mul_exp_linear_sub_half_sq 0 (1/3)
      refine h.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_)
      show u ^ 0 * Real.exp ((1/3) * u - u ^ 2 / 2) = Real.exp ((1/3) * u - u ^ 2 / 2)
      rw [pow_zero, one_mul]
    refine ((hJ2'.const_mul (1/2)).add henv).mono'
      (((Real.continuous_cosh.comp (continuous_id.div_const _))).mul
        (continuous_airyLeadF z)).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu0 : (0:ℝ) ≤ u := (mem_Ioi.mp hu).le
    have hz0 : (0:ℝ) < z := by linarith
    have hzinv : z⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz
    have hch : Real.cosh (u / Real.sqrt z) ≤ (u ^ 2 / (2 * z)) * Real.exp u + 1 := by
      have h := cosh_div_sqrt_sub_one_le hz hu0
      linarith
    have hch' : Real.cosh (u / Real.sqrt z) ≤ ((u ^ 2 / 2) * Real.exp u + 1) := by
      have hmono : (u ^ 2 / (2 * z)) * Real.exp u ≤ (u ^ 2 / 2) * Real.exp u := by
        have huz : (u ^ 2 / (2 * z)) = (u ^ 2 / 2) * z⁻¹ := by
          rw [div_eq_mul_inv, mul_inv]; ring
        rw [huz]
        calc (u ^ 2 / 2) * z⁻¹ * Real.exp u ≤ (u ^ 2 / 2) * 1 * Real.exp u := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
              exact mul_le_mul_of_nonneg_left hzinv (by positivity)
          _ = (u ^ 2 / 2) * Real.exp u := by ring
      linarith
    have hF := airyLeadF_le hz hu0
    have hFnn : (0:ℝ) ≤ airyLeadF z u :=
      mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.cosh_pos _).le hFnn)]
    calc Real.cosh (u / Real.sqrt z) * airyLeadF z u
        ≤ ((u ^ 2 / 2) * Real.exp u + 1) *
            (Real.exp (-(u ^ 2 / 2)) * Real.exp (u / 3)) :=
          mul_le_mul hch' hF hFnn (by positivity)
      _ = (1/2) * (u ^ 2 * Real.exp ((4/3) * u - u ^ 2 / 2))
          + Real.exp ((1/3) * u - u ^ 2 / 2) := by
          rw [show Real.exp (-(u ^ 2 / 2)) * Real.exp (u / 3)
                = Real.exp ((1/3) * u - u ^ 2 / 2) from by
                rw [← Real.exp_add]; congr 1; ring]
          have e2 : Real.exp u * Real.exp ((1/3) * u - u ^ 2 / 2)
              = Real.exp ((4/3) * u - u ^ 2 / 2) := by
            rw [← Real.exp_add]; congr 1; ring
          calc (u ^ 2 / 2 * Real.exp u + 1) * Real.exp ((1/3) * u - u ^ 2 / 2)
              = (u ^ 2 / 2) * (Real.exp u * Real.exp ((1/3) * u - u ^ 2 / 2))
                + Real.exp ((1/3) * u - u ^ 2 / 2) := by ring
            _ = (1/2) * (u ^ 2 * Real.exp ((4/3) * u - u ^ 2 / 2))
                + Real.exp ((1/3) * u - u ^ 2 / 2) := by rw [e2]; ring
  have hsplit : (∫ u in Set.Ioi 0, Real.cosh (u / Real.sqrt z) * airyLeadF z u)
        - Real.sqrt (Real.pi / 2)
      = ∫ u in Set.Ioi 0, (Real.cosh (u / Real.sqrt z) * airyLeadF z u
          - Real.exp (-(1/2) * u ^ 2)) := by
    rw [← integral_exp_neg_half_sq_eq_sqrt_pi_div_two]
    exact (integral_sub hWFint hGint).symm
  have hBint : IntegrableOn (fun u => Real.exp (-(u ^ 2 / 2)) *
        ((u ^ 2 / (2 * z)) * Real.exp (4 * u / 3)
          + ((u ^ 2 / (18 * z)) * Real.exp (u / 3) + (u ^ 4 / (4 * z)) * Real.exp u)))
      (Set.Ioi 0) := by
    have h1' := hJ2'.const_mul (1 / (2 * z))
    have h2' := hJ2.const_mul (1 / (18 * z))
    have h4' := hJ4.const_mul (1 / (4 * z))
    refine (h1'.add (h2'.add h4')).congr
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
    show (1 / (2 * z)) * (u ^ 2 * Real.exp ((4/3) * u - u ^ 2 / 2))
        + ((1 / (18 * z)) * (u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))
          + (1 / (4 * z)) * (u ^ 4 * Real.exp (1 * u - u ^ 2 / 2)))
      = Real.exp (-(u ^ 2 / 2)) * ((u ^ 2 / (2 * z)) * Real.exp (4 * u / 3)
          + ((u ^ 2 / (18 * z)) * Real.exp (u / 3) + (u ^ 4 / (4 * z)) * Real.exp u))
    rw [show Real.exp ((4/3) * u - u ^ 2 / 2)
          = Real.exp (4 * u / 3) * Real.exp (-(u ^ 2 / 2)) from by
          rw [← Real.exp_add]; congr 1; ring,
        show Real.exp ((1/3) * u - u ^ 2 / 2)
          = Real.exp (u / 3) * Real.exp (-(u ^ 2 / 2)) from by
          rw [← Real.exp_add]; congr 1; ring,
        show Real.exp (1 * u - u ^ 2 / 2)
          = Real.exp u * Real.exp (-(u ^ 2 / 2)) from by
          rw [← Real.exp_add]; congr 1; ring]
    ring
  rw [hsplit]
  calc |∫ u in Set.Ioi 0, (Real.cosh (u / Real.sqrt z) * airyLeadF z u
        - Real.exp (-(1/2) * u ^ 2))|
      = ‖∫ u in Set.Ioi 0, (Real.cosh (u / Real.sqrt z) * airyLeadF z u
          - Real.exp (-(1/2) * u ^ 2))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ u in Set.Ioi 0, ‖Real.cosh (u / Real.sqrt z) * airyLeadF z u
          - Real.exp (-(1/2) * u ^ 2)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u in Set.Ioi 0, Real.exp (-(u ^ 2 / 2)) *
          ((u ^ 2 / (2 * z)) * Real.exp (4 * u / 3)
            + ((u ^ 2 / (18 * z)) * Real.exp (u / 3) + (u ^ 4 / (4 * z)) * Real.exp u)) := by
        refine setIntegral_mono_on (hWFint.sub hGint).norm hBint measurableSet_Ioi
          fun u hu => ?_
        have hu0 : (0:ℝ) ≤ u := (mem_Ioi.mp hu).le
        have hz0 : (0:ℝ) < z := by linarith
        rw [Real.norm_eq_abs,
          show Real.exp (-(1/2) * u ^ 2) = Real.exp (-(u ^ 2 / 2)) from by
            congr 1; ring]
        have hdev := cosh_div_sqrt_sub_one_le hz hu0
        have hpt := airyLeadF_sub_gaussian_abs_le hz hu0
        have hFnn : (0:ℝ) ≤ airyLeadF z u :=
          mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
        have hdev' : (0:ℝ) ≤ (Real.cosh (u / Real.sqrt z) - 1) * airyLeadF z u :=
          mul_nonneg (by linarith [Real.one_le_cosh (u / Real.sqrt z)]) hFnn
        calc |Real.cosh (u / Real.sqrt z) * airyLeadF z u - Real.exp (-(u ^ 2 / 2))|
            = |(Real.cosh (u / Real.sqrt z) - 1) * airyLeadF z u
                + (airyLeadF z u - Real.exp (-(u ^ 2 / 2)))| := by ring_nf
          _ ≤ |(Real.cosh (u / Real.sqrt z) - 1) * airyLeadF z u|
              + |airyLeadF z u - Real.exp (-(u ^ 2 / 2))| := abs_add_le _ _
          _ = (Real.cosh (u / Real.sqrt z) - 1) * airyLeadF z u
              + |airyLeadF z u - Real.exp (-(u ^ 2 / 2))| := by
              rw [abs_of_nonneg hdev']
          _ ≤ (u ^ 2 / (2 * z)) * Real.exp u *
                (Real.exp (-(u ^ 2 / 2)) * Real.exp (u / 3))
              + Real.exp (-(u ^ 2 / 2)) * ((u ^ 2 / (18 * z)) * Real.exp (u / 3)
                + (u ^ 4 / (4 * z)) * Real.exp u) :=
              add_le_add (mul_le_mul hdev (airyLeadF_le hz hu0) hFnn (by positivity)) hpt
          _ = Real.exp (-(u ^ 2 / 2)) * ((u ^ 2 / (2 * z)) * Real.exp (4 * u / 3)
                + ((u ^ 2 / (18 * z)) * Real.exp (u / 3)
                  + (u ^ 4 / (4 * z)) * Real.exp u)) := by
              rw [show (u ^ 2 / (2 * z)) * Real.exp u * (Real.exp (-(u ^ 2 / 2)) * Real.exp (u / 3))
                    = (u ^ 2 / (2 * z)) * (Real.exp (4 * u / 3) * Real.exp (-(u ^ 2 / 2))) from by
                    have e1 : Real.exp (-(u ^ 2 / 2)) * Real.exp (u / 3)
                        = Real.exp (u / 3 - u ^ 2 / 2) := by
                      rw [← Real.exp_add]; congr 1; ring
                    have e2 : Real.exp u * Real.exp (u / 3 - u ^ 2 / 2)
                        = Real.exp (4 * u / 3) * Real.exp (-(u ^ 2 / 2)) := by
                      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
                    rw [e1, mul_assoc (u ^ 2 / (2 * z)) (Real.exp u), e2]]
              ring
    _ = (1 / (2 * z)) * (∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((4/3) * u - u ^ 2 / 2))
          + ((1 / (18 * z)) * (∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))
            + (1 / (4 * z)) * (∫ u in Set.Ioi 0, u ^ 4 * Real.exp (1 * u - u ^ 2 / 2))) := by
        have hcongr : (∫ u in Set.Ioi 0, Real.exp (-(u ^ 2 / 2)) *
              (u ^ 2 / (2 * z) * Real.exp (4 * u / 3)
                + (u ^ 2 / (18 * z) * Real.exp (u / 3) + u ^ 4 / (4 * z) * Real.exp u)))
            = ∫ u in Set.Ioi 0, (1 / (2 * z)) * (u ^ 2 * Real.exp ((4/3) * u - u ^ 2 / 2))
              + (((fun u => (1 / (18 * z)) * (u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))))
                + (fun u => (1 / (4 * z)) * (u ^ 4 * Real.exp (1 * u - u ^ 2 / 2)))
                  : ℝ → ℝ) u := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          show Real.exp (-(u ^ 2 / 2)) * (u ^ 2 / (2 * z) * Real.exp (4 * u / 3)
                + (u ^ 2 / (18 * z) * Real.exp (u / 3) + u ^ 4 / (4 * z) * Real.exp u))
            = (1 / (2 * z)) * (u ^ 2 * Real.exp ((4/3) * u - u ^ 2 / 2))
              + ((1 / (18 * z)) * (u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))
                + (1 / (4 * z)) * (u ^ 4 * Real.exp (1 * u - u ^ 2 / 2)))
          rw [show Real.exp ((4/3) * u - u ^ 2 / 2)
                = Real.exp (4 * u / 3) * Real.exp (-(u ^ 2 / 2)) from by
                rw [← Real.exp_add]; congr 1; ring,
              show Real.exp ((1/3) * u - u ^ 2 / 2)
                = Real.exp (u / 3) * Real.exp (-(u ^ 2 / 2)) from by
                rw [← Real.exp_add]; congr 1; ring,
              show Real.exp (1 * u - u ^ 2 / 2)
                = Real.exp u * Real.exp (-(u ^ 2 / 2)) from by
                rw [← Real.exp_add]; congr 1; ring]
          ring
        have hI23 : (∫ a in Set.Ioi 0,
              (((fun u => (1 / (18 * z)) * (u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))))
                + (fun u => (1 / (4 * z)) * (u ^ 4 * Real.exp (1 * u - u ^ 2 / 2)))
                  : ℝ → ℝ) a)
            = (1 / (18 * z)) * (∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))
              + (1 / (4 * z)) * (∫ u in Set.Ioi 0, u ^ 4 * Real.exp (1 * u - u ^ 2 / 2)) :=
          (integral_add (hJ2.const_mul (1 / (18 * z))) (hJ4.const_mul (1 / (4 * z)))).trans
            (by rw [integral_const_mul, integral_const_mul])
        rw [hcongr,
          integral_add (hJ2'.const_mul (1 / (2 * z)))
            ((hJ2.const_mul (1 / (18 * z))).add (hJ4.const_mul (1 / (4 * z)))),
          hI23, integral_const_mul]
    _ = ((1/2) * (∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((4/3) * u - u ^ 2 / 2))
          + (1/18) * (∫ u in Set.Ioi 0, u ^ 2 * Real.exp ((1/3) * u - u ^ 2 / 2))
          + (1/4) * (∫ u in Set.Ioi 0, u ^ 4 * Real.exp (1 * u - u ^ 2 / 2))) * z⁻¹ := by
        rw [show (1 / (2 * z)) = (1/2) * z⁻¹ from by
              rw [div_eq_mul_inv, mul_inv, one_mul, inv_eq_one_div],
            show (1 / (18 * z)) = (1/18) * z⁻¹ from by
              rw [div_eq_mul_inv, mul_inv, one_mul, inv_eq_one_div],
            show (1 / (4 * z)) = (1/4) * z⁻¹ from by
              rw [div_eq_mul_inv, mul_inv, one_mul, inv_eq_one_div]]
        ring

/-- **The `t = u/√z` substitution identity** for weighted Schläfli integrals
(factoring out `e^{-z}` and substituting `t = u/√z`, as in
`schlaefli_master_isEquivalent`): for `0 < z`,
`∫₀^∞ w(t) e^{-z cosh t} cosh(t/3) dt
  = (√z)⁻¹ e^{-z} ∫₀^∞ w(u/√z)·airyLeadF z u du`. -/
theorem integral_schlaefli_weighted_eq (hz : 0 < z) (w : ℝ → ℝ) :
    (∫ t in Set.Ioi 0, w t * Real.exp (-z * Real.cosh t) * Real.cosh (t / 3))
      = (Real.sqrt z)⁻¹ * Real.exp (-z) *
        ∫ u in Set.Ioi 0, w (u / Real.sqrt z) * airyLeadF z u := by
  have hsz : (0:ℝ) < Real.sqrt z := Real.sqrt_pos.2 hz
  have hE : ∀ t : ℝ, Real.exp (-z * Real.cosh t)
      = Real.exp (-z) * Real.exp (-z * (Real.cosh t - 1)) := by
    intro t
    rw [← Real.exp_add]
    congr 1
    ring
  have hI1 : (∫ t in Set.Ioi 0, w t * Real.exp (-z * Real.cosh t) * Real.cosh (t / 3))
      = Real.exp (-z) * ∫ t in Set.Ioi 0, w t *
        (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    show w t * Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)
      = Real.exp (-z) * (w t * (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)))
    rw [hE t]
    ring
  have hsub : (∫ u in Set.Ioi 0, w (u / Real.sqrt z) * airyLeadF z u)
      = Real.sqrt z * ∫ t in Set.Ioi 0, w t *
        (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)) := by
    have h := integral_comp_mul_left_Ioi
      (fun t => w t * (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)))
      (0 : ℝ) (b := (Real.sqrt z)⁻¹) (inv_pos.2 hsz)
    simp only [inv_inv, smul_eq_mul, mul_zero] at h
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    show w (u / Real.sqrt z) * airyLeadF z u
      = w ((Real.sqrt z)⁻¹ * u) * (Real.exp (-z * (Real.cosh ((Real.sqrt z)⁻¹ * u) - 1)) *
          Real.cosh ((Real.sqrt z)⁻¹ * u / 3))
    unfold airyLeadF
    rw [show u / Real.sqrt z = (Real.sqrt z)⁻¹ * u from by rw [div_eq_mul_inv, mul_comm]]
  rw [hI1, hsub]
  set G := ∫ t in Set.Ioi 0, w t *
    (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)) with hG
  calc Real.exp (-z) * G
      = (Real.sqrt z)⁻¹ * Real.sqrt z * (Real.exp (-z) * G) := by
        rw [inv_mul_cancel₀ hsz.ne', one_mul]
    _ = (Real.sqrt z)⁻¹ * Real.exp (-z) * (Real.sqrt z * G) := by ring

/-- **The `O(1/z)` rate for the Schläfli `K_{1/3}` integral** (the rate behind
`schlaefliK13_isEquivalent`; the `(1 + O(z⁻¹))` of DLMF 10.40.2 at `ν = 1/3`, used in
the paper): there is `C` with, for all `1 ≤ z`,
`|K_{1/3}(z) − √(π/(2z)) e^{−z}| ≤ C z⁻¹ √(π/(2z)) e^{−z}`. -/
theorem schlaefliK13_sub_lead_abs_le :
    ∃ C : ℝ, ∀ z : ℝ, 1 ≤ z →
      |schlaefliK13 z - Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z)|
        ≤ C * z⁻¹ * Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z) := by
  obtain ⟨C₀, hC₀nn, hC₀⟩ := integral_airyLeadF_sub_sqrt_pi_div_two_abs_le
  refine ⟨C₀ * Real.sqrt (2 / Real.pi), fun z hz => ?_⟩
  have hz0 : (0:ℝ) < z := by linarith
  have hsz : (0:ℝ) < Real.sqrt z := Real.sqrt_pos.2 hz0
  have hK : schlaefliK13 z
      = (Real.sqrt z)⁻¹ * Real.exp (-z) * ∫ u in Set.Ioi 0, airyLeadF z u := by
    have h := integral_schlaefli_weighted_eq hz0 (fun _ => 1)
    simp only [one_mul] at h
    unfold schlaefliK13
    exact h
  have hlead : Real.sqrt (Real.pi / (2 * z))
      = Real.sqrt (Real.pi / 2) * (Real.sqrt z)⁻¹ := by
    rw [show Real.pi / (2 * z) = (Real.pi / 2) * z⁻¹ from by
      rw [inv_eq_one_div, div_mul_div_comm, mul_one],
      Real.sqrt_mul (by positivity), Real.sqrt_inv]
  have hfac : (0:ℝ) ≤ (Real.sqrt z)⁻¹ * Real.exp (-z) :=
    mul_nonneg (inv_nonneg.2 hsz.le) (Real.exp_pos _).le
  have h22 : Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2) = 1 := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 / Real.pi),
      show (2 / Real.pi) * (Real.pi / 2) = 1 from by field_simp [Real.pi_ne_zero],
      Real.sqrt_one]
  rw [hK, hlead]
  have hfact : (Real.sqrt z)⁻¹ * Real.exp (-z) * (∫ u in Set.Ioi 0, airyLeadF z u)
      - (Real.sqrt (Real.pi / 2) * (Real.sqrt z)⁻¹) * Real.exp (-z)
      = ((Real.sqrt z)⁻¹ * Real.exp (-z)) *
        ((∫ u in Set.Ioi 0, airyLeadF z u) - Real.sqrt (Real.pi / 2)) := by ring
  rw [hfact, abs_mul, abs_of_nonneg hfac]
  calc (Real.sqrt z)⁻¹ * Real.exp (-z) *
        |(∫ u in Set.Ioi 0, airyLeadF z u) - Real.sqrt (Real.pi / 2)|
      ≤ (Real.sqrt z)⁻¹ * Real.exp (-z) * (C₀ * z⁻¹) :=
        mul_le_mul_of_nonneg_left (hC₀ z hz) hfac
    _ = (C₀ * Real.sqrt (2 / Real.pi)) * z⁻¹ * (Real.sqrt (Real.pi / 2) * (Real.sqrt z)⁻¹)
          * Real.exp (-z) := by
        calc (Real.sqrt z)⁻¹ * Real.exp (-z) * (C₀ * z⁻¹)
            = C₀ * z⁻¹ * ((Real.sqrt z)⁻¹ * Real.exp (-z)) *
                (Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2)) := by rw [h22]; ring
          _ = (C₀ * Real.sqrt (2 / Real.pi)) * z⁻¹
                * (Real.sqrt (Real.pi / 2) * (Real.sqrt z)⁻¹) * Real.exp (-z) := by ring

/-- **The `O(1/z)` rate for the derivative integral** (weight `cosh`, the rate
behind `schlaefliK13_deriv_isEquivalent`): there is `C` with, for
all `1 ≤ z`, `|−K_{1/3}'(z) − √(π/(2z)) e^{−z}| ≤ C z⁻¹ √(π/(2z)) e^{−z}`. -/
theorem neg_deriv_schlaefliK13_sub_lead_abs_le :
    ∃ C : ℝ, ∀ z : ℝ, 1 ≤ z →
      |-deriv schlaefliK13 z - Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z)|
        ≤ C * z⁻¹ * Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z) := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ := integral_cosh_airyLeadF_sub_sqrt_pi_div_two_abs_le
  refine ⟨C₁ * Real.sqrt (2 / Real.pi), fun z hz => ?_⟩
  have hz0 : (0:ℝ) < z := by linarith
  have hsz : (0:ℝ) < Real.sqrt z := Real.sqrt_pos.2 hz0
  have hd : -deriv schlaefliK13 z
      = (Real.sqrt z)⁻¹ * Real.exp (-z) *
        ∫ u in Set.Ioi 0, Real.cosh (u / Real.sqrt z) * airyLeadF z u := by
    have hder : deriv schlaefliK13 z
        = -(∫ t in Set.Ioi 0, Real.cosh t * Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)) :=
      (deriv_schlaefliK13 hz0).deriv
    rw [hder, neg_neg]
    exact integral_schlaefli_weighted_eq hz0 Real.cosh
  have hlead : Real.sqrt (Real.pi / (2 * z))
      = Real.sqrt (Real.pi / 2) * (Real.sqrt z)⁻¹ := by
    rw [show Real.pi / (2 * z) = (Real.pi / 2) * z⁻¹ from by
      rw [inv_eq_one_div, div_mul_div_comm, mul_one],
      Real.sqrt_mul (by positivity), Real.sqrt_inv]
  have hfac : (0:ℝ) ≤ (Real.sqrt z)⁻¹ * Real.exp (-z) :=
    mul_nonneg (inv_nonneg.2 hsz.le) (Real.exp_pos _).le
  have h22 : Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2) = 1 := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 / Real.pi),
      show (2 / Real.pi) * (Real.pi / 2) = 1 from by field_simp [Real.pi_ne_zero],
      Real.sqrt_one]
  rw [hd, hlead]
  have hfact : (Real.sqrt z)⁻¹ * Real.exp (-z) *
        (∫ u in Set.Ioi 0, Real.cosh (u / Real.sqrt z) * airyLeadF z u)
      - (Real.sqrt (Real.pi / 2) * (Real.sqrt z)⁻¹) * Real.exp (-z)
      = ((Real.sqrt z)⁻¹ * Real.exp (-z)) *
        ((∫ u in Set.Ioi 0, Real.cosh (u / Real.sqrt z) * airyLeadF z u)
          - Real.sqrt (Real.pi / 2)) := by ring
  rw [hfact, abs_mul, abs_of_nonneg hfac]
  calc (Real.sqrt z)⁻¹ * Real.exp (-z) *
        |(∫ u in Set.Ioi 0, Real.cosh (u / Real.sqrt z) * airyLeadF z u)
          - Real.sqrt (Real.pi / 2)|
      ≤ (Real.sqrt z)⁻¹ * Real.exp (-z) * (C₁ * z⁻¹) :=
        mul_le_mul_of_nonneg_left (hC₁ z hz) hfac
    _ = (C₁ * Real.sqrt (2 / Real.pi)) * z⁻¹ * (Real.sqrt (Real.pi / 2) * (Real.sqrt z)⁻¹)
          * Real.exp (-z) := by
        calc (Real.sqrt z)⁻¹ * Real.exp (-z) * (C₁ * z⁻¹)
            = C₁ * z⁻¹ * ((Real.sqrt z)⁻¹ * Real.exp (-z)) *
                (Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2)) := by rw [h22]; ring
          _ = (C₁ * Real.sqrt (2 / Real.pi)) * z⁻¹
                * (Real.sqrt (Real.pi / 2) * (Real.sqrt z)⁻¹) * Real.exp (-z) := by ring

end CoreRate

/-! ## The Airy-derivative rate -/

section AiryDerivRate

/-- **Airy-derivative rate** (`-Ai'(A) = (1/(2√π)) A^{1/4} e^{-(2/3)A^{3/2}} (1 +
O(A^{-3/2}))`): the Airy derivative with the explicit `A^{-3/2}` relative rate,
assembled from the two Schläfli rates through the exact derivative formula `airyBesselY1` and the
prefactor identity `deriv_airyAiReal_prefactor`. -/
theorem neg_deriv_airyAiReal_sub_lead_isBigO :
    (fun A => -deriv airyAiReal A - leadAiDeriv A) =O[atTop]
      fun A => A ^ (-3/2 : ℝ) * leadAiDeriv A := by
  obtain ⟨C₁, hC₁⟩ := schlaefliK13_sub_lead_abs_le
  obtain ⟨C₂, hC₂⟩ := neg_deriv_schlaefliK13_sub_lead_abs_le
  have hL1 : (0:ℝ) < Real.sqrt (Real.pi / (2 * (1:ℝ))) * Real.exp (-1 : ℝ) := by
    positivity
  have hC₁nn : 0 ≤ C₁ := by
    have h1 := hC₁ 1 le_rfl
    have h3 := (abs_nonneg _).trans h1
    have h4 : (0:ℝ) ≤ Real.sqrt (Real.pi / (2 * (1:ℝ))) * Real.exp (-1 : ℝ) * C₁ := by
      rw [show (Real.sqrt (Real.pi / (2 * (1:ℝ))) * Real.exp (-1 : ℝ)) * C₁
          = C₁ * (1:ℝ)⁻¹ * Real.sqrt (Real.pi / (2 * (1:ℝ))) * Real.exp (-1 : ℝ) from by ring]
      exact h3
    exact nonneg_of_mul_nonneg_right h4 hL1
  have hC₂nn : 0 ≤ C₂ := by
    have h1 := hC₂ 1 le_rfl
    have h3 := (abs_nonneg _).trans h1
    have h4 : (0:ℝ) ≤ Real.sqrt (Real.pi / (2 * (1:ℝ))) * Real.exp (-1 : ℝ) * C₂ := by
      rw [show (Real.sqrt (Real.pi / (2 * (1:ℝ))) * Real.exp (-1 : ℝ)) * C₂
          = C₂ * (1:ℝ)⁻¹ * Real.sqrt (Real.pi / (2 * (1:ℝ))) * Real.exp (-1 : ℝ) from by ring]
      exact h3
    exact nonneg_of_mul_nonneg_right h4 hL1
  refine Asymptotics.isBigO_iff.2 ⟨(3/2) * C₂ + (1/2) * (1 + (3/2) * C₁), ?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ)] with A hA2
  have hA0 : (0:ℝ) < A := by linarith
  have hξ : (1:ℝ) ≤ (2/3) * A ^ (3/2 : ℝ) := by
    have h2p : (2:ℝ) ^ (3/2 : ℝ) = 2 * Real.sqrt 2 := by
      have h := two_mul_rpow_three_halves (M := 1) (by norm_num)
      rwa [mul_one, Real.one_rpow, mul_one] at h
    have hA32 : (2:ℝ) ^ (3/2 : ℝ) ≤ A ^ (3/2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hA2 (by norm_num)
    have h4 : (1:ℝ) ≤ (2/3) * (2 * Real.sqrt 2) := by
      have h34 : (3/4:ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
      linarith
    calc (1:ℝ) ≤ (2/3) * (2 * Real.sqrt 2) := h4
      _ = (2/3) * ((2:ℝ) ^ (3/2 : ℝ)) := by rw [h2p]
      _ ≤ (2/3) * A ^ (3/2 : ℝ) := by linarith [hA32]
  have hξ0 : (0:ℝ) < (2/3) * A ^ (3/2 : ℝ) := by linarith
  have hK1 := hC₁ _ hξ
  have hK2 := hC₂ _ hξ
  have hderivA : deriv airyAiReal A = (1 / Real.pi) * airyBesselY1 A := by
    have heq : airyAiReal =ᶠ[𝓝 A] fun y => airyBesselY y / Real.pi := by
      filter_upwards [Ioi_mem_nhds hA0] with y hy
      exact airyAiReal_eq_airyBesselY_div_pi hy
    rw [heq.deriv_eq, ((hasDerivAt_airyBesselY hA0).div_const Real.pi).deriv,
      div_eq_mul_inv, one_div, mul_comm]
  have hLlead : (1 / Real.pi) * (Real.sqrt 3)⁻¹ * A *
        (Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
          Real.exp (-((2/3) * A ^ (3/2 : ℝ))))
      = (1 / (2 * Real.sqrt Real.pi)) * A ^ (1/4 : ℝ) *
        Real.exp (-(2/3) * A ^ (3/2 : ℝ)) := by
    rw [← deriv_airyAiReal_prefactor hA0, neg_mul]
    ring
  have hξinv : ((2/3) * A ^ (3/2 : ℝ))⁻¹ = (3/2) * A ^ (-3/2 : ℝ) := by
    rw [mul_inv, ← Real.rpow_neg hA0.le, show ((2/3):ℝ)⁻¹ = 3/2 by norm_num,
      show (-(3/2) : ℝ) = (-3/2 : ℝ) by norm_num]
  have hLnn : (0:ℝ) ≤ Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
      Real.exp (-((2/3) * A ^ (3/2 : ℝ))) := by positivity
  have hB1 : |schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))|
      ≤ (1 + C₁ * ((2/3) * A ^ (3/2 : ℝ))⁻¹) *
        (Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
          Real.exp (-((2/3) * A ^ (3/2 : ℝ)))) := by
    rw [show C₁ * ((2/3) * A ^ (3/2:ℝ))⁻¹ * Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ))))
        * Real.exp (-((2/3) * A ^ (3/2 : ℝ)))
        = C₁ * ((2/3) * A ^ (3/2:ℝ))⁻¹ *
          (Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
            Real.exp (-((2/3) * A ^ (3/2 : ℝ)))) from by ring] at hK1
    calc |schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))|
        = |(schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))
            - Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
              Real.exp (-((2/3) * A ^ (3/2 : ℝ))))
          + (Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
            Real.exp (-((2/3) * A ^ (3/2 : ℝ))))| := by ring_nf
      _ ≤ |(schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))
            - Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
              Real.exp (-((2/3) * A ^ (3/2 : ℝ))))|
          + |Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
              Real.exp (-((2/3) * A ^ (3/2 : ℝ)))| := abs_add_le _ _
      _ ≤ C₁ * ((2/3) * A ^ (3/2:ℝ))⁻¹ *
            (Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
              Real.exp (-((2/3) * A ^ (3/2 : ℝ))))
          + (Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
            Real.exp (-((2/3) * A ^ (3/2 : ℝ)))) := by
          rw [abs_of_nonneg hLnn]
          exact add_le_add hK1 le_rfl
      _ = (1 + C₁ * ((2/3) * A ^ (3/2 : ℝ))⁻¹) *
          (Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
            Real.exp (-((2/3) * A ^ (3/2 : ℝ)))) := by ring
  have hB2 : |-deriv schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))
        - Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
          Real.exp (-((2/3) * A ^ (3/2 : ℝ)))|
      ≤ C₂ * ((2/3) * A ^ (3/2 : ℝ))⁻¹ *
        (Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
          Real.exp (-((2/3) * A ^ (3/2 : ℝ)))) := by
    rw [show C₂ * ((2/3) * A ^ (3/2:ℝ))⁻¹ * Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ))))
        * Real.exp (-((2/3) * A ^ (3/2 : ℝ)))
        = C₂ * ((2/3) * A ^ (3/2:ℝ))⁻¹ *
          (Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
            Real.exp (-((2/3) * A ^ (3/2 : ℝ)))) from by ring] at hK2
    exact hK2
  have hdecomp : -deriv airyAiReal A - leadAiDeriv A
      = (1 / Real.pi) * (Real.sqrt 3)⁻¹ * A *
          (-deriv schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))
            - Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
              Real.exp (-((2/3) * A ^ (3/2 : ℝ))))
        + -((1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2) * A ^ (-1/2 : ℝ) *
          schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))) := by
    rw [hderivA]
    unfold airyBesselY1 leadAiDeriv
    rw [← hLlead]
    ring
  have hc0 : (0:ℝ) ≤ (1 / Real.pi) * (Real.sqrt 3)⁻¹ * A := by positivity
  have hc0' : (0:ℝ) ≤ (1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2) * A ^ (-1/2 : ℝ) := by
    positivity
  have hA32le : A ^ (-3/2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hAhalf : A ^ (-1/2 : ℝ) = A ^ (-3/2 : ℝ) * A := by
    have e : (-3/2 : ℝ) + 1 = -1/2 := by norm_num
    calc A ^ (-1/2 : ℝ) = A ^ (-3/2 + 1 : ℝ) := by rw [e]
      _ = A ^ (-3/2 : ℝ) * A ^ (1 : ℝ) := Real.rpow_add hA0 _ _
      _ = A ^ (-3/2 : ℝ) * A := by rw [Real.rpow_one]
  have hT1 : |(1 / Real.pi) * (Real.sqrt 3)⁻¹ * A *
        (-deriv schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))
          - Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
            Real.exp (-((2/3) * A ^ (3/2 : ℝ))))|
      ≤ (3/2) * C₂ * (A ^ (-3/2 : ℝ) * leadAiDeriv A) := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc (1 / Real.pi) * (Real.sqrt 3)⁻¹ * A *
          |-deriv schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))
            - Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
              Real.exp (-((2/3) * A ^ (3/2 : ℝ)))|
        ≤ (1 / Real.pi) * (Real.sqrt 3)⁻¹ * A *
          (C₂ * ((2/3) * A ^ (3/2 : ℝ))⁻¹ *
            (Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
              Real.exp (-((2/3) * A ^ (3/2 : ℝ))))) :=
          mul_le_mul_of_nonneg_left hB2 hc0
      _ = (3/2) * C₂ * (A ^ (-3/2 : ℝ) * leadAiDeriv A) := by
          rw [hξinv]
          unfold leadAiDeriv
          rw [← deriv_airyAiReal_prefactor hA0, neg_mul]
          ring
  have hT2 : |(1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2) * A ^ (-1/2 : ℝ) *
        schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))|
      ≤ (1/2) * (1 + (3/2) * C₁) * (A ^ (-3/2 : ℝ) * leadAiDeriv A) := by
    rw [abs_mul, abs_of_nonneg hc0']
    calc (1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2) * A ^ (-1/2 : ℝ) *
          |schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))|
        ≤ (1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2) * A ^ (-1/2 : ℝ) *
          ((1 + C₁ * ((2/3) * A ^ (3/2 : ℝ))⁻¹) *
            (Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
              Real.exp (-((2/3) * A ^ (3/2 : ℝ))))) :=
          mul_le_mul_of_nonneg_left hB1 hc0'
      _ ≤ (1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2) * A ^ (-1/2 : ℝ) *
          ((1 + C₁ * (3/2)) *
            (Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
              Real.exp (-((2/3) * A ^ (3/2 : ℝ))))) := by
          apply mul_le_mul_of_nonneg_left _ hc0'
          apply mul_le_mul_of_nonneg_right _ hLnn
          rw [hξinv]
          nlinarith [hC₁nn]
      _ = (1/2) * (1 + (3/2) * C₁) * (A ^ (-3/2 : ℝ) * leadAiDeriv A) := by
          unfold leadAiDeriv
          rw [← deriv_airyAiReal_prefactor hA0, neg_mul, hAhalf]
          ring
  rw [Real.norm_eq_abs, hdecomp,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hA0.le _)
      (leadAiDeriv_pos hA0).le)]
  calc |(1 / Real.pi) * (Real.sqrt 3)⁻¹ * A *
          (-deriv schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))
            - Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
              Real.exp (-((2/3) * A ^ (3/2 : ℝ))))
        + -((1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2) * A ^ (-1/2 : ℝ) *
          schlaefliK13 ((2/3) * A ^ (3/2 : ℝ)))|
      ≤ |(1 / Real.pi) * (Real.sqrt 3)⁻¹ * A *
          (-deriv schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))
            - Real.sqrt (Real.pi / (2 * ((2/3) * A ^ (3/2 : ℝ)))) *
              Real.exp (-((2/3) * A ^ (3/2 : ℝ))))|
        + |(1 / Real.pi) * (Real.sqrt 3)⁻¹ * (1/2) * A ^ (-1/2 : ℝ) *
          schlaefliK13 ((2/3) * A ^ (3/2 : ℝ))| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ ≤ (3/2) * C₂ * (A ^ (-3/2 : ℝ) * leadAiDeriv A)
        + (1/2) * (1 + (3/2) * C₁) * (A ^ (-3/2 : ℝ) * leadAiDeriv A) :=
        add_le_add hT1 hT2
    _ = ((3/2) * C₂ + (1/2) * (1 + (3/2) * C₁)) * (A ^ (-3/2 : ℝ) * leadAiDeriv A) := by
        ring

end AiryDerivRate

/-! ## The `ρ`-assembly at `A = 2M` -/

section RhoAssembly

/-- **The `ρ`-assembly** (`-2T·Ai'(2M) = Tρ(M) + O_T(M^{-3/2} ρ(M))`): the
derivative block with rate, from the Airy-derivative rate at `A = 2M` and the exact identity
`two_mul_leadAiDeriv_two_mul`.  The constant may depend on `T`. -/
theorem neg_two_mul_T_deriv_sub_T_rhoM_isBigO (T : ℝ) (hT : 0 < T) :
    (fun M => -2 * T * deriv airyAiReal (2 * M) - T * rhoM M) =O[atTop]
      fun M => M ^ (-3/2 : ℝ) * rhoM M := by
  obtain ⟨C₃, hC₃⟩ := Asymptotics.isBigO_iff.1 neg_deriv_airyAiReal_sub_lead_isBigO
  rw [eventually_atTop] at hC₃
  obtain ⟨A₀, hA₀⟩ := hC₃
  refine Asymptotics.isBigO_iff.2 ⟨C₃ * (2:ℝ) ^ (-3/2 : ℝ) * T, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 A₀)] with M hM
  have hM1 : (1:ℝ) ≤ M := le_trans (le_max_left _ _) hM
  have hM0 : (0:ℝ) < M := by linarith
  have h2M0 : (0:ℝ) < 2 * M := by linarith
  have hbound := hA₀ (2 * M) (by linarith [le_max_right 1 A₀])
  have hnorm1 : ‖-deriv airyAiReal (2 * M) - leadAiDeriv (2 * M)‖
      ≤ C₃ * ((2 * M) ^ (-3/2 : ℝ) * leadAiDeriv (2 * M)) := by
    rw [Real.norm_eq_abs]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg h2M0.le _)
      (leadAiDeriv_pos h2M0).le)] at hbound
    exact hbound
  have hid := two_mul_leadAiDeriv_two_mul hM0
  have hfactor : -2 * T * deriv airyAiReal (2 * M) - T * rhoM M
      = 2 * T * (-deriv airyAiReal (2 * M) - leadAiDeriv (2 * M)) := by
    rw [← hid]
    ring
  calc ‖-2 * T * deriv airyAiReal (2 * M) - T * rhoM M‖
      = 2 * T * ‖-deriv airyAiReal (2 * M) - leadAiDeriv (2 * M)‖ := by
        rw [hfactor, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (mul_nonneg (by norm_num) hT.le), Real.norm_eq_abs]
    _ ≤ 2 * T * (C₃ * ((2 * M) ^ (-3/2 : ℝ) * leadAiDeriv (2 * M))) :=
        mul_le_mul_of_nonneg_left hnorm1 (mul_nonneg (by norm_num) hT.le)
    _ = (C₃ * (2:ℝ) ^ (-3/2 : ℝ) * T) * (M ^ (-3/2 : ℝ) * rhoM M) := by
        rw [two_mul_rpow_neg_three_halves hM0.le,
          show 2 * T * (C₃ * ((2:ℝ) ^ (-3/2 : ℝ) * M ^ (-3/2 : ℝ) * leadAiDeriv (2 * M)))
            = C₃ * (2:ℝ) ^ (-3/2 : ℝ) * T * (M ^ (-3/2 : ℝ) * (2 * leadAiDeriv (2 * M))) from by
            ring, hid]
    _ = (C₃ * (2:ℝ) ^ (-3/2 : ℝ) * T) * ‖M ^ (-3/2 : ℝ) * rhoM M‖ := by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hM0.le _) (rhoM_pos hM0).le)]

end RhoAssembly

/-! ## The tail two-term -/

section TailTwoTerm

/-- **Tail two-term, `Ioi` form**: the Airy tail integral is
`ρ(M)/(4M) + o(ρ(M)/M)`; only the `IsEquivalent` form
(`integral_airyAiReal_isEquivalent`) is needed, with the exact identity
`leadIntegral_two_mul_eq_rhoM_div` for the constant. -/
theorem integral_Ioi_airyAiReal_sub_rhoM_div_isLittleO :
    (fun M => (∫ u in Set.Ioi (2 * M), airyAiReal u) - rhoM M / (4 * M)) =o[atTop]
      fun M => rhoM M / M := by
  have h2M : Tendsto (fun M : ℝ => 2 * M) atTop atTop := by
    have h := (tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ) < 2)).2 tendsto_id
    simpa only [id_eq] using h
  have hcomp := integral_airyAiReal_isEquivalent.comp_tendsto h2M
  have hlo := hcomp.isLittleO
  have hcongr1 : ((fun A => ∫ u in Set.Ioi A, airyAiReal u) ∘ fun M => 2 * M)
      - ((fun A => (1 / (2 * Real.sqrt Real.pi)) * A ^ (-3/4 : ℝ) *
          Real.exp (-(2/3) * A ^ (3/2 : ℝ))) ∘ fun M => 2 * M)
      =ᶠ[atTop] fun M => (∫ u in Set.Ioi (2 * M), airyAiReal u) - rhoM M / (4 * M) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    simp only [Function.comp_apply, Pi.sub_apply]
    rw [leadIntegral_two_mul_eq_rhoM_div hM]
  have hcongr2 : ((fun A => (1 / (2 * Real.sqrt Real.pi)) * A ^ (-3/4 : ℝ) *
        Real.exp (-(2/3) * A ^ (3/2 : ℝ))) ∘ fun M => 2 * M)
      =ᶠ[atTop] fun M => rhoM M / (4 * M) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    simp only [Function.comp_apply]
    rw [leadIntegral_two_mul_eq_rhoM_div hM]
  have h1 := hlo.congr' hcongr1 hcongr2
  have h2 : (fun M => rhoM M / (4 * M)) =O[atTop] fun M => rhoM M / M := by
    refine Asymptotics.isBigO_iff.2 ⟨1/4, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with M hM
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (rhoM_pos hM).le (by positivity)),
      abs_of_nonneg (div_nonneg (rhoM_pos hM).le hM.le),
      show rhoM M / (4 * M) = (1/4) * (rhoM M / M) from by field_simp [hM.ne']]
  exact h1.trans_isBigO h2

/-- **Tail two-term, `Ici` form** (`Ici`/`Ioi` agree by `integral_Ici_eq_integral_Ioi`). -/
theorem integral_Ici_airyAiReal_sub_rhoM_div_isLittleO :
    (fun M => (∫ u in Set.Ici (2 * M), airyAiReal u) - rhoM M / (4 * M)) =o[atTop]
      fun M => rhoM M / M := by
  refine integral_Ioi_airyAiReal_sub_rhoM_div_isLittleO.congr'
    (Eventually.of_forall fun M => ?_) (EventuallyEq.refl _ _)
  show (∫ u in Set.Ioi (2 * M), airyAiReal u) - rhoM M / (4 * M)
    = (∫ u in Set.Ici (2 * M), airyAiReal u) - rhoM M / (4 * M)
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]

end TailTwoTerm

/-! ## Stretched-exponential decay and the `o(ρ(M)/M)` scale management -/

section Decay

/-- Polynomials times the stretched exponential vanish:
`M^p · e^{-c M^{3/2}} → 0` for `0 < c`, via `(cM^{3/2})^n e^{-cM^{3/2}} → 0`
(`tendsto_pow_mul_exp_neg_atTop_nhds_zero`) with `n = ⌈2p/3⌉`-sized slack. -/
theorem tendsto_rpow_mul_exp_neg_mul_rpow (c : ℝ) (hc : 0 < c) (p : ℝ) :
    Tendsto (fun M : ℝ => M ^ p * Real.exp (-c * M ^ (3/2 : ℝ))) atTop (𝓝 0) := by
  set n := ⌈p⌉₊ with hn
  have hφ : Tendsto (fun M : ℝ => c * M ^ (3/2 : ℝ)) atTop atTop := by
    have h := (tendsto_const_mul_atTop_of_pos hc).2
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/2))
    simpa only [id_eq] using h
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp hφ
  have hcn : (0:ℝ) < c ^ n := pow_pos hc n
  have halg : ∀ M : ℝ, 0 ≤ M → M ^ (3 * n / 2 : ℝ) * Real.exp (-c * M ^ (3/2 : ℝ))
      = (c ^ n)⁻¹ * ((c * M ^ (3/2 : ℝ)) ^ n * Real.exp (-(c * M ^ (3/2 : ℝ)))) := by
    intro M hM
    rw [mul_pow, ← Real.rpow_natCast (M ^ (3/2 : ℝ)) n, ← Real.rpow_mul hM,
      show (3/2 : ℝ) * (n : ℝ) = 3 * n / 2 from by ring, neg_mul]
    field_simp [hcn.ne']
  have hupper : Tendsto (fun M : ℝ => (c ^ n)⁻¹ *
        ((c * M ^ (3/2 : ℝ)) ^ n * Real.exp (-(c * M ^ (3/2 : ℝ))))) atTop (𝓝 0) := by
    have h := h0.const_mul (c ^ n)⁻¹
    rwa [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with M hM
    exact mul_nonneg (Real.rpow_nonneg hM _) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have hM0 : (0:ℝ) < M := by linarith
    have hpn : p ≤ 3 * n / 2 := by
      have h1 : p ≤ (n : ℝ) := Nat.le_ceil p
      have h2 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    calc M ^ p * Real.exp (-c * M ^ (3/2 : ℝ))
        ≤ M ^ (3 * n / 2 : ℝ) * Real.exp (-c * M ^ (3/2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hM hpn)
            (Real.exp_pos _).le
      _ = (c ^ n)⁻¹ * ((c * M ^ (3/2 : ℝ)) ^ n * Real.exp (-(c * M ^ (3/2 : ℝ)))) :=
          halg M hM0.le

/-- Eventually-smallness wrapper: for `0 < c` and `0 < ε`, eventually
`K · M^p · e^{-c M^{3/2}} ≤ ε`. -/
theorem eventually_rpow_mul_exp_neg_le {c p K ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ M in atTop, K * M ^ p * Real.exp (-c * M ^ (3/2 : ℝ)) ≤ ε := by
  have h := (tendsto_rpow_mul_exp_neg_mul_rpow c hc p).const_mul K
  rw [mul_zero] at h
  have h' := h.congr' (Eventually.of_forall fun M => by ring : (fun M : ℝ =>
    K * (M ^ p * Real.exp (-c * M ^ (3/2 : ℝ)))) =ᶠ[atTop]
      fun M => K * M ^ p * Real.exp (-c * M ^ (3/2 : ℝ)))
  filter_upwards [(tendsto_order.1 h').2 ε hε] with M hM
  linarith [hM]

/-- `ρ(M)/M = C_* · M^{-3/4} · e^{-κ M^{3/2}}` for `0 < M`. -/
theorem rhoM_div_eq (hM : 0 < M) :
    rhoM M / M = Cstar * M ^ (-3/4 : ℝ) * Real.exp (-kappaC * M ^ (3/2 : ℝ)) := by
  unfold rhoM
  rw [show Cstar * M ^ (1/4 : ℝ) * Real.exp (-kappaC * M ^ (3/2 : ℝ)) / M
      = Cstar * (M ^ (1/4 : ℝ) / M) * Real.exp (-kappaC * M ^ (3/2 : ℝ)) from by ring,
    show M ^ (1/4 : ℝ) / M = M ^ (-3/4 : ℝ) from by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hM]
      norm_num]

/-- The sub-lead scale `M^{-3/2} ρ(M)` is `o(ρ(M)/M)`: the ratio is `M^{-1/2} → 0`. -/
theorem rpow_neg_three_halves_mul_rhoM_isLittleO :
    (fun M => M ^ (-3/2 : ℝ) * rhoM M) =o[atTop] fun M => rhoM M / M := by
  refine Asymptotics.isLittleO_iff.2 fun ε hε => ?_
  have hhalf : Tendsto (fun M : ℝ => M ^ (-1/2 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)).congr fun M => by
      rw [show (-(1/2) : ℝ) = -1/2 from by norm_num]
  filter_upwards [(tendsto_order.1 hhalf).2 ε hε, eventually_ge_atTop 1] with M hM hM1
  have hM0 : (0:ℝ) < M := by linarith
  have hρ : (0:ℝ) < rhoM M := rhoM_pos hM0
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hM0.le _) hρ.le),
    abs_of_nonneg (div_nonneg hρ.le hM0.le)]
  have hfactor : M ^ (-3/2 : ℝ) * rhoM M = M ^ (-1/2 : ℝ) * (rhoM M / M) := by
    rw [show rhoM M / M = rhoM M * M ^ (-1 : ℝ) from by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]]
    rw [mul_comm (rhoM M) (M ^ (-1 : ℝ)), ← mul_assoc, ← Real.rpow_add hM0]
    congr 1
    norm_num
  rw [hfactor]
  exact mul_le_mul_of_nonneg_right hM.le (div_nonneg hρ.le hM0.le)

/-- The error of the heat-exact trace identity is `o(ρ(M)/M)`:
`|ℰ_{M,T}| ≤ C_T M^{-3/4} e^{-2TM} e^{-κ M^{3/2}}` and `e^{-2TM} → 0`. -/
theorem errorMT_isLittleO_rhoM_div (T : ℝ) (hT : 0 < T) :
    (fun M => errorMT M T) =o[atTop] fun M => rhoM M / M := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := errorMT_abs_le hT
  refine Asymptotics.isLittleO_iff.2 fun ε hε => ?_
  have hexp : Tendsto (fun M : ℝ => Real.exp (-(2 * T * M))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℝ => (2 * T) * M) atTop atTop := by
      have h := (tendsto_const_mul_atTop_of_pos (by positivity : (0:ℝ) < 2 * T)).2
        tendsto_id
      simpa only [id_eq] using h
    have h2 : Tendsto (fun M : ℝ => -((2 * T) * M)) atTop atBot :=
      tendsto_neg_atBot_iff.2 h1
    have h3 := Real.tendsto_exp_atBot.comp h2
    exact h3
  have hscale : Tendsto (fun M : ℝ => (C₂ / Cstar) * Real.exp (-(2 * T * M))) atTop (𝓝 0) := by
    have h := hexp.const_mul (C₂ / Cstar)
    rwa [mul_zero] at h
  filter_upwards [(tendsto_order.1 hscale).2 ε hε, eventually_ge_atTop 1] with M hM hM1
  have hM0 : (0:ℝ) < M := by linarith
  have hρ : (0:ℝ) < rhoM M := rhoM_pos hM0
  have hρM : rhoM M / M = Cstar * M ^ (-3/4 : ℝ) * Real.exp (-kappaC * M ^ (3/2 : ℝ)) :=
    rhoM_div_eq hM0
  have hexpand : Real.exp (-T * (2 * M) - (2/3) * (2 * M) ^ (3/2 : ℝ))
      = Real.exp (-(2 * T * M)) * Real.exp (-kappaC * M ^ (3/2 : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    rw [show (2/3 : ℝ) * (2 * M) ^ (3/2 : ℝ) = kappaC * M ^ (3/2 : ℝ) from
      (kappaC_mul_rpow_eq hM0.le).symm]
    ring
  have hCstar : (0:ℝ) < Cstar := Cstar_pos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hρ.le hM0.le)]
  calc |errorMT M T|
      ≤ C₂ * M ^ (-3/4 : ℝ) * Real.exp (-T * (2 * M) - (2/3) * (2 * M) ^ (3/2 : ℝ)) :=
        hC₂ M hM1
    _ = (C₂ / Cstar) * Real.exp (-(2 * T * M)) * (rhoM M / M) := by
        rw [hexpand, hρM]
        field_simp [hCstar.ne']
    _ ≤ ε * (rhoM M / M) :=
        mul_le_mul_of_nonneg_right hM.le (div_nonneg hρ.le hM0.le)

end Decay

/-! ## The trace and `det₁` at the paper's `a = √(2M)`, and the trace assembly -/

section TraceAssembly

/-- The trace of the conjugated operator `Ã_{M,T}` at the paper's parameter
choice `a = √(2M)`.  Totalized: junk value `0` outside the
valid region `0 < M`, `T + 1 ≤ √(2M)` (invisible to the `atTop` asymptotics). -/
noncomputable def traceAiryTilde (M T : ℝ) : ℝ :=
  if h : (0 < T) ∧ (0 < M) ∧ (T + 1 ≤ Real.sqrt (2 * M)) then
    HilbertSchmidt.trace (airyTildeOp M T (Real.sqrt (2 * M)) h.1 h.2.1 h.2.2)
  else 0

/-- The `det₁(1 − Ã_{M,T})` at `a = √(2M)`, totalized with junk value `0`
(the paper's `det(I − Ã_{M,T})`). -/
noncomputable def detOneAiryTilde (M T : ℝ) : ℝ :=
  if h : (0 < T) ∧ (0 < M) ∧ (T + 1 ≤ Real.sqrt (2 * M)) then
    HilbertSchmidt.fredholmDetOne (airyTildeOp M T (Real.sqrt (2 * M)) h.1 h.2.1 h.2.2)
      (isTraceClass_airyTildeOp h.1 h.2.1 h.2.2) 1
  else 0

/-- The heat-exact trace identity at `a = √(2M)` (as in the paper),
restated for the totalized `traceAiryTilde`. -/
theorem traceAiryTilde_eq_heat (hT : 0 < T) {M : ℝ} (hM : 0 < M)
    (ha : T + 1 ≤ Real.sqrt (2 * M)) :
    traceAiryTilde M T
      = -(2 * T) * deriv airyAiReal (2 * M) + (∫ u in Set.Ioi (2 * M), airyAiReal u)
        + errorMT M T := by
  unfold traceAiryTilde
  rw [dite_eq_left ⟨hT, hM, ha⟩]
  exact trace_airyTilde_eq_heat_exact hT hM ha

/-- **Trace assembly** (the paper's two-term trace asymptotic): the trace of the
conjugated operator is
`Tρ(M) + ρ(M)/(4M) + o(ρ(M)/M)`.  The three pieces of `trace_airyTilde_eq_heat_exact`
are: `-2T·Ai'(2M) = Tρ(M) + O(M^{-3/2}ρ(M))` (the `ρ`-assembly, and `M^{-3/2}ρ = o(ρ/M)` by
`rpow_neg_three_halves_mul_rhoM_isLittleO`), `∫_{2M}^∞ Ai = ρ(M)/(4M) + o(ρ(M)/M)`
(the tail two-term), and `ℰ_{M,T} = o(ρ(M)/M)` (`errorMT_isLittleO_rhoM_div`). -/
theorem traceAiryTilde_sub_traceLead_isLittleO (T : ℝ) (hT : 0 < T) :
    (fun M => traceAiryTilde M T - traceLead M T) =o[atTop] fun M => rhoM M / M := by
  have hB1 : (fun M => -2 * T * deriv airyAiReal (2 * M) - T * rhoM M) =o[atTop]
      fun M => rhoM M / M :=
    (neg_two_mul_T_deriv_sub_T_rhoM_isBigO T hT).trans_isLittleO
      rpow_neg_three_halves_mul_rhoM_isLittleO
  have hB2 := integral_Ioi_airyAiReal_sub_rhoM_div_isLittleO
  have hB3 := errorMT_isLittleO_rhoM_div T hT
  have hsum := (hB1.add hB2).add hB3
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop (max 1 ((T + 1) ^ 2 / 2))] with M hM
  have hM1 : (1:ℝ) ≤ M := le_trans (le_max_left _ _) hM
  have hM0 : (0:ℝ) < M := by linarith
  have ha : T + 1 ≤ Real.sqrt (2 * M) := by
    have h2M : (T + 1) ^ 2 ≤ 2 * M := by linarith [le_max_right 1 ((T + 1) ^ 2 / 2)]
    have hT1 : (0:ℝ) ≤ T + 1 := by linarith [hT.le]
    calc T + 1 = Real.sqrt ((T + 1) ^ 2) := (Real.sqrt_sq hT1).symm
      _ ≤ Real.sqrt (2 * M) := Real.sqrt_le_sqrt h2M
  have htr := traceAiryTilde_eq_heat hT hM0 ha
  show (-2 * T * deriv airyAiReal (2 * M) - T * rhoM M)
      + ((∫ u in Set.Ioi (2 * M), airyAiReal u) - rhoM M / (4 * M)) + errorMT M T
    = traceAiryTilde M T - traceLead M T
  rw [htr]
  unfold traceLead
  ring

end TraceAssembly

/-! ## The `det₁` remainder -/

section DetRemainder

/-- The squared-`HS`-norm bound at `a = √(2M)` (as in the paper): the
exponent `a³/3 − 2Ma` at `a = √(2M)` is `−κM^{3/2}`, and the
polynomial factors absorb into `M^{7/4}`. -/
theorem hsNorm_airyTilde_le_at_sqrt (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, ∀ (hM : 0 < M), 1 ≤ M → ∀ (ha : T + 1 ≤ Real.sqrt (2 * M)),
      hsNorm (airyTildeOp M T (Real.sqrt (2 * M)) hT hM ha)
        ≤ C * M ^ (7/4 : ℝ) * Real.exp (-kappaC * M ^ (3/2 : ℝ)) := by
  obtain ⟨C₃, hC₃pos, hC₃⟩ := hsNorm_airyTilde_le T hT
  refine ⟨C₃ * 2 ^ (5/4 : ℝ) * 2, by positivity, fun M hM0 hM1 ha => ?_⟩
  have h2M0 : (0:ℝ) < 2 * M := by linarith
  have hbound := hC₃ M (Real.sqrt (2 * M)) hM0 ha
  have hcube : (Real.sqrt (2 * M)) ^ 3 = (2 * M) ^ (3/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((2 * M) ^ (1/2 : ℝ)) 3,
      ← Real.rpow_mul h2M0.le]
    congr 1
    norm_num
  have h2Msqrt : 2 * M * Real.sqrt (2 * M) = (2 * M) ^ (3/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (3/2 : ℝ) = 1 + 1/2 from by norm_num,
      Real.rpow_add h2M0, Real.rpow_one]
  have hexp : (Real.sqrt (2 * M)) ^ 3 / 3 - 2 * M * Real.sqrt (2 * M)
      = -kappaC * M ^ (3/2 : ℝ) := by
    rw [hcube, h2Msqrt,
      show (2 * M) ^ (3/2 : ℝ) / 3 - (2 * M) ^ (3/2 : ℝ)
        = -(2/3) * (2 * M) ^ (3/2 : ℝ) from by ring,
      neg_two_thirds_mul_two_mul_rpow hM0.le]
  have h1a3 : 1 + (Real.sqrt (2 * M)) ^ 3 ≤ 2 * (2 * M) ^ (3/2 : ℝ) := by
    have h : (1:ℝ) ≤ (2 * M) ^ (3/2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rw [hcube]
    linarith
  have hsqrt : Real.sqrt (1 + (Real.sqrt (2 * M)) ^ 3)
      ≤ 2 ^ (1/2 : ℝ) * (2 * M) ^ (3/4 : ℝ) := by
    calc Real.sqrt (1 + (Real.sqrt (2 * M)) ^ 3)
        ≤ Real.sqrt (2 * (2 * M) ^ (3/2 : ℝ)) := Real.sqrt_le_sqrt h1a3
      _ = Real.sqrt 2 * Real.sqrt ((2 * M) ^ (3/2 : ℝ)) :=
          Real.sqrt_mul (by norm_num) _
      _ = (2 : ℝ) ^ (1/2 : ℝ) * (2 * M) ^ (3/4 : ℝ) := by
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul h2M0.le]
          norm_num
  calc hsNorm (airyTildeOp M T (Real.sqrt (2 * M)) hT (by linarith) ha)
      ≤ C₃ * (1 + M) * Real.sqrt (1 + (Real.sqrt (2 * M)) ^ 3) *
        Real.exp ((Real.sqrt (2 * M)) ^ 3 / 3 - 2 * M * Real.sqrt (2 * M)) := hbound
    _ ≤ C₃ * (2 * M) * (2 ^ (1/2 : ℝ) * (2 * M) ^ (3/4 : ℝ)) *
        Real.exp (-kappaC * M ^ (3/2 : ℝ)) := by
        rw [hexp]
        have hexpnn : (0:ℝ) ≤ Real.exp (-kappaC * M ^ (3/2 : ℝ)) := (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ hexpnn
        apply mul_le_mul _ _ (Real.sqrt_nonneg _) (by positivity)
        · exact mul_le_mul_of_nonneg_left (by linarith) hC₃pos.le
        · exact hsqrt
    _ = C₃ * 2 ^ (5/4 : ℝ) * 2 * M ^ (7/4 : ℝ) * Real.exp (-kappaC * M ^ (3/2 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hM0.le]
        have h2p : (2 : ℝ) ^ (1/2 : ℝ) * (2 : ℝ) ^ (3/4 : ℝ) = (2 : ℝ) ^ (5/4 : ℝ) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), show (1/2 : ℝ) + 3/4 = 5/4 by norm_num]
        have hM74 : M * M ^ (3/4 : ℝ) = M ^ (7/4 : ℝ) := by
          calc M * M ^ (3/4 : ℝ) = M ^ (1 : ℝ) * M ^ (3/4 : ℝ) := by rw [Real.rpow_one]
            _ = M ^ (1 + 3/4 : ℝ) := (Real.rpow_add hM0 _ _).symm
            _ = M ^ (7/4 : ℝ) := by rw [show (1:ℝ) + 3/4 = 7/4 by norm_num]
        rw [show C₃ * (2 * M) * ((2 : ℝ) ^ (1/2 : ℝ) * ((2 : ℝ) ^ (3/4 : ℝ) * M ^ (3/4 : ℝ))) *
            Real.exp (-kappaC * M ^ (3/2 : ℝ))
          = (C₃ * 2 * ((2 : ℝ) ^ (1/2 : ℝ) * (2 : ℝ) ^ (3/4 : ℝ))) *
            (M * M ^ (3/4 : ℝ)) * Real.exp (-kappaC * M ^ (3/2 : ℝ)) from by ring,
          h2p, hM74]
        ring

/-- **The `det₁` remainder** (the paper's determinant remainder estimate; the first-order
input is `norm_one_sub_fredholmDetOne_one_sub_trace_le`, and the decay of the squared
Hilbert–Schmidt norm is the inline estimate below):
`1 − det₁(1−Ã_{M,T}) − Tr Ã_{M,T} = o(ρ(M)/M)`. -/
theorem one_sub_detOneAiryTilde_sub_trace_isLittleO (T : ℝ) (hT : 0 < T) :
    (fun M => (1 - detOneAiryTilde M T) - traceAiryTilde M T) =o[atTop]
      fun M => rhoM M / M := by
  obtain ⟨D, hDpos, hD⟩ := hsNorm_airyTilde_le_at_sqrt T hT
  have htr := traceAiryTilde_sub_traceLead_isLittleO T hT
  have hρ0 : Tendsto (fun M : ℝ => rhoM M) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_rpow kappaC kappaC_pos (1/4)).const_mul Cstar
    rw [mul_zero] at h
    refine h.congr' (Eventually.of_forall fun M => ?_)
    unfold rhoM
    ring
  have hρT : Tendsto (fun M : ℝ => (T + 5/4) * rhoM M) atTop (𝓝 0) := by
    have h := hρ0.const_mul (T + 5/4)
    rwa [mul_zero] at h
  refine Asymptotics.isLittleO_iff.2 fun ε hε => ?_
  filter_upwards [eventually_ge_atTop (max 1 ((T + 1) ^ 2 / 2)),
    htr.def (show (0:ℝ) < 1 by norm_num),
    (tendsto_order.1 hρT).2 (1/2) (by norm_num),
    eventually_rpow_mul_exp_neg_le (c := kappaC) kappaC_pos (p := 7/4) (K := D)
      (ε := 1/2) (by norm_num),
    eventually_rpow_mul_exp_neg_le (c := kappaC) kappaC_pos (p := 5/4)
      (K := Real.exp 1 * (T + 5/4) ^ 2 * Cstar) (ε := ε/2) (by positivity),
    eventually_rpow_mul_exp_neg_le (c := kappaC) kappaC_pos (p := 17/4)
      (K := (Real.exp 1 + 1) * D ^ 2 * Cstar⁻¹) (ε := ε/2) (by positivity)]
    with M hM htr1 hρTbound hhsB hsmall1 hsmall2
  have hM1 : (1:ℝ) ≤ M := le_trans (le_max_left _ _) hM
  have hM0 : (0:ℝ) < M := by linarith
  have ha : T + 1 ≤ Real.sqrt (2 * M) := by
    have h2M : (T + 1) ^ 2 ≤ 2 * M := by linarith [le_max_right 1 ((T + 1) ^ 2 / 2)]
    have hT1 : (0:ℝ) ≤ T + 1 := by linarith [hT.le]
    calc T + 1 = Real.sqrt ((T + 1) ^ 2) := (Real.sqrt_sq hT1).symm
      _ ≤ Real.sqrt (2 * M) := Real.sqrt_le_sqrt h2M
  have hρ : (0:ℝ) < rhoM M := rhoM_pos hM0
  have hρM : rhoM M / M = Cstar * M ^ (-3/4 : ℝ) * Real.exp (-kappaC * M ^ (3/2 : ℝ)) :=
    rhoM_div_eq hM0
  have hρMnn : (0:ℝ) ≤ rhoM M / M := div_nonneg hρ.le hM0.le
  set A := airyTildeOp M T (Real.sqrt (2 * M)) hT hM0 ha with hA
  have hAtr : IsTraceClass A := isTraceClass_airyTildeOp hT hM0 ha
  have hd : detOneAiryTilde M T = fredholmDetOne A hAtr 1 := by
    unfold detOneAiryTilde
    rw [dite_eq_left ⟨hT, hM0, ha⟩]
  have htrc : traceAiryTilde M T = trace A := by
    unfold traceAiryTilde
    rw [dite_eq_left ⟨hT, hM0, ha⟩]
  have hhs : hsNorm A ≤ D * M ^ (7/4 : ℝ) * Real.exp (-kappaC * M ^ (3/2 : ℝ)) :=
    hD M hM0 hM1 ha
  have hhsnn : (0:ℝ) ≤ hsNorm A := hsNorm_nonneg _
  have hhs12 : hsNorm A ≤ 1 / 2 := hhs.trans hhsB
  have htleadnn : (0:ℝ) ≤ traceLead M T := by
    unfold traceLead
    exact add_nonneg (mul_nonneg hT.le hρ.le) (div_nonneg hρ.le (by positivity))
  have htrM : ‖trace A‖ ≤ (T + 5/4) * rhoM M := by
    rw [← htrc]
    have h1 : ‖traceAiryTilde M T - traceLead M T‖ ≤ 1 * ‖rhoM M / M‖ := htr1
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hρMnn] at h1
    have hρMle : rhoM M / M ≤ rhoM M := by
      rw [div_le_iff₀ hM0]
      calc rhoM M = rhoM M * 1 := (mul_one _).symm
        _ ≤ rhoM M * M := mul_le_mul_of_nonneg_left hM1 hρ.le
    have hquarter : rhoM M / (4 * M) ≤ rhoM M / 4 :=
      div_le_div_of_nonneg_left hρ.le (by norm_num) (by linarith)
    calc ‖traceAiryTilde M T‖
        = ‖(traceAiryTilde M T - traceLead M T) + traceLead M T‖ := by rw [sub_add_cancel]
      _ ≤ ‖traceAiryTilde M T - traceLead M T‖ + ‖traceLead M T‖ := norm_add_le _ _
      _ ≤ (rhoM M / M) + traceLead M T := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg htleadnn]
          exact add_le_add h1 le_rfl
      _ ≤ rhoM M + (T * rhoM M + rhoM M / 4) := by
          unfold traceLead
          linarith [hρMle, hquarter]
      _ = (T + 5/4) * rhoM M := by ring
  have htrsmall : ‖trace A‖ ≤ 1 / 2 := htrM.trans hρTbound.le
  have hsum1 : ‖trace A‖ + hsNorm A ^ 2 ≤ 1 := by
    have h2 : hsNorm A ^ 2 ≤ 1 / 4 :=
      (pow_le_pow_left₀ hhsnn hhs12 2).trans (by norm_num)
    linarith
  have hexp1 : Real.exp (‖trace A‖ + hsNorm A ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.2 hsum1
  have hrem := norm_one_sub_fredholmDetOne_one_sub_trace_le hAtr
    (hhs12.trans_lt (by norm_num)) hhs12
  have hs21 : hsNorm A ^ 2 ≤ 1 := (pow_le_pow_left₀ hhsnn hhs12 2).trans (by norm_num)
  have h4 : (hsNorm A ^ 2) ^ 2 ≤ hsNorm A ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hs21 (pow_nonneg hhsnn 2)
    rw [one_mul] at h
    calc (hsNorm A ^ 2) ^ 2 = hsNorm A ^ 2 * hsNorm A ^ 2 := by ring
      _ ≤ hsNorm A ^ 2 := h
  have hρsq : rhoM M ^ 2
      = Cstar ^ 2 * M ^ (1/2 : ℝ) * Real.exp (-(2 * kappaC) * M ^ (3/2 : ℝ)) := by
    unfold rhoM
    rw [mul_pow, mul_pow,
      show (Real.exp (-kappaC * M ^ (3/2 : ℝ))) ^ 2
        = Real.exp (-(2 * kappaC) * M ^ (3/2 : ℝ)) from by
        rw [pow_two, ← Real.exp_add]; congr 1; ring,
      ← Real.rpow_natCast (M ^ (1/4 : ℝ)) 2, ← Real.rpow_mul hM0.le,
      show ((1/4 : ℝ) * ((2 : ℕ) : ℝ)) = 1/2 from by norm_num]
  have hquot1 : Real.exp 1 * ((T + 5/4) * rhoM M) ^ 2
      = (Real.exp 1 * (T + 5/4) ^ 2 * Cstar * M ^ (5/4 : ℝ) *
          Real.exp (-kappaC * M ^ (3/2 : ℝ))) * (rhoM M / M) := by
    rw [hρM, mul_pow, hρsq,
      show (Real.exp 1 * (T + 5/4) ^ 2 * Cstar * M ^ (5/4 : ℝ) *
          Real.exp (-kappaC * M ^ (3/2 : ℝ))) * (Cstar * M ^ (-3/4 : ℝ) *
          Real.exp (-kappaC * M ^ (3/2 : ℝ)))
        = Real.exp 1 * (T + 5/4) ^ 2 * Cstar ^ 2 * (M ^ (5/4 : ℝ) * M ^ (-3/4 : ℝ)) *
          (Real.exp (-kappaC * M ^ (3/2 : ℝ)) * Real.exp (-kappaC * M ^ (3/2 : ℝ))) from by ring,
      ← Real.rpow_add hM0, ← Real.exp_add,
      show (5/4 : ℝ) + -3/4 = 1/2 by norm_num,
      show -kappaC * M ^ (3/2 : ℝ) + -kappaC * M ^ (3/2 : ℝ)
        = -(2 * kappaC) * M ^ (3/2 : ℝ) from by ring]
    ring
  have hquot2 : (Real.exp 1 + 1) * (D * M ^ (7/4 : ℝ) * Real.exp (-kappaC * M ^ (3/2 : ℝ))) ^ 2
      = ((Real.exp 1 + 1) * D ^ 2 * Cstar⁻¹ * M ^ (17/4 : ℝ) *
          Real.exp (-kappaC * M ^ (3/2 : ℝ))) * (rhoM M / M) := by
    rw [hρM, mul_pow, mul_pow,
      show ((Real.exp 1 + 1) * D ^ 2 * Cstar⁻¹ * M ^ (17/4 : ℝ) *
          Real.exp (-kappaC * M ^ (3/2 : ℝ))) * (Cstar * M ^ (-3/4 : ℝ) *
          Real.exp (-kappaC * M ^ (3/2 : ℝ)))
        = (Real.exp 1 + 1) * D ^ 2 * (Cstar⁻¹ * Cstar) *
          (M ^ (17/4 : ℝ) * M ^ (-3/4 : ℝ)) *
          (Real.exp (-kappaC * M ^ (3/2 : ℝ)) * Real.exp (-kappaC * M ^ (3/2 : ℝ))) from by ring,
      inv_mul_cancel₀ Cstar_pos.ne', ← Real.rpow_add hM0, ← Real.exp_add,
      show (17/4 : ℝ) + -3/4 = 7/2 by norm_num,
      show -kappaC * M ^ (3/2 : ℝ) + -kappaC * M ^ (3/2 : ℝ)
        = -(2 * kappaC) * M ^ (3/2 : ℝ) from by ring,
      show (M ^ (7/4 : ℝ)) ^ 2 = M ^ (7/2 : ℝ) from by
        rw [← Real.rpow_natCast (M ^ (7/4 : ℝ)) 2, ← Real.rpow_mul hM0.le,
          show ((7/4 : ℝ) * ((2 : ℕ) : ℝ)) = 7/2 from by norm_num],
      show (Real.exp (-kappaC * M ^ (3/2 : ℝ))) ^ 2
        = Real.exp (-(2 * kappaC) * M ^ (3/2 : ℝ)) from by
        rw [pow_two, ← Real.exp_add]; congr 1; ring]
    ring
  rw [Real.norm_eq_abs, hd, htrc]
  calc |(1 - fredholmDetOne A hAtr 1) - trace A|
      ≤ (‖trace A‖ + hsNorm A ^ 2) ^ 2 / 2 * Real.exp (‖trace A‖ + hsNorm A ^ 2)
        + hsNorm A ^ 2 := by
        rw [← Real.norm_eq_abs]
        exact hrem
    _ ≤ (‖trace A‖ + hsNorm A ^ 2) ^ 2 / 2 * Real.exp 1 + hsNorm A ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hexp1
            (div_nonneg (pow_nonneg (add_nonneg (norm_nonneg _) (pow_nonneg hhsnn 2)) 2)
              (by norm_num))) le_rfl
    _ ≤ (2 * ‖trace A‖ ^ 2 + 2 * (hsNorm A ^ 2) ^ 2) / 2 * Real.exp 1 + hsNorm A ^ 2 := by
        have hsq2 : (‖trace A‖ + hsNorm A ^ 2) ^ 2
            ≤ 2 * ‖trace A‖ ^ 2 + 2 * (hsNorm A ^ 2) ^ 2 := by
          nlinarith [sq_nonneg (‖trace A‖ - hsNorm A ^ 2)]
        exact add_le_add (by gcongr) le_rfl
    _ = Real.exp 1 * ‖trace A‖ ^ 2 + (Real.exp 1 * (hsNorm A ^ 2) ^ 2 + hsNorm A ^ 2) := by
        ring
    _ ≤ Real.exp 1 * ‖trace A‖ ^ 2 + (Real.exp 1 + 1) * hsNorm A ^ 2 := by
        refine add_le_add le_rfl ?_
        calc Real.exp 1 * (hsNorm A ^ 2) ^ 2 + hsNorm A ^ 2
            ≤ Real.exp 1 * (hsNorm A ^ 2) + hsNorm A ^ 2 :=
              add_le_add (mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le) le_rfl
          _ = (Real.exp 1 + 1) * hsNorm A ^ 2 := by ring
    _ ≤ Real.exp 1 * ((T + 5/4) * rhoM M) ^ 2
        + (Real.exp 1 + 1) * (D * M ^ (7/4 : ℝ) * Real.exp (-kappaC * M ^ (3/2 : ℝ))) ^ 2 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) htrM 2) (Real.exp_pos _).le
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hhsnn hhs 2) (add_nonneg (Real.exp_pos _).le zero_le_one)
    _ = (Real.exp 1 * (T + 5/4) ^ 2 * Cstar * M ^ (5/4 : ℝ) *
          Real.exp (-kappaC * M ^ (3/2 : ℝ))) * (rhoM M / M)
        + ((Real.exp 1 + 1) * D ^ 2 * Cstar⁻¹ * M ^ (17/4 : ℝ) *
          Real.exp (-kappaC * M ^ (3/2 : ℝ))) * (rhoM M / M) := by
        rw [hquot1, hquot2]
    _ ≤ (ε/2) * (rhoM M / M) + (ε/2) * (rhoM M / M) :=
        add_le_add (mul_le_mul_of_nonneg_right hsmall1 hρMnn)
          (mul_le_mul_of_nonneg_right hsmall2 hρMnn)
    _ = ε * (rhoM M / M) := by ring
    _ = ε * ‖rhoM M / M‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hρMnn]

end DetRemainder

/-! ## The sharp-tail expansion -/

/-- **Sharp-tail expansion** (the paper's sharp one-block tail, with the
Quastel–Remenik/conjugation identity kept as the hypothesis record
field `hpi`; that identity is discharged in the main package):
`π_T(M) = Tρ(M) + ρ(M)/(4M) + o(ρ(M)/M)`. -/
theorem piT_sub_traceLead_isLittleO (T : ℝ) (hT : 0 < T) (piT : ℝ → ℝ)
    (hpi : ∀ M, piT M = 1 - detOneAiryTilde M T) :
    (fun M => piT M - traceLead M T) =o[atTop] fun M => rhoM M / M := by
  have h7 := one_sub_detOneAiryTilde_sub_trace_isLittleO T hT
  have h6 := traceAiryTilde_sub_traceLead_isLittleO T hT
  have hsum := h7.add h6
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards with M
  show ((1 - detOneAiryTilde M T) - traceAiryTilde M T)
      + (traceAiryTilde M T - traceLead M T) = piT M - traceLead M T
  rw [hpi M]
  ring

end AiryConj
