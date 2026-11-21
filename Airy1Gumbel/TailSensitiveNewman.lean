/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.TwoPointBound
import Airy1GumbelContrib.FredholmDet.KernelDet
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Layercake

open Asymptotics Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal

namespace Airy1Gumbel

open AiryConj AiryFdd HilbertSchmidt

/-- The GOE operator's diagonal trace in the Airy₁ normalization. -/
theorem trace_goeOp_eq_half_integral (u : ℝ) :
    HilbertSchmidt.trace (AiryFdd.goeOp u) =
      (1 / 2 : ℝ) * (∫ x in Ioi (2 * u), airyAiReal x) := by
  rw [goeOp_eq_comp, trace_kernelOperator_comp_eq_integral_diag,
    compKernel_goeVKer_goeWKer]
  have hdiag (x : ℝ) :
      goeKer u (x, x) = (Ioi u).indicator (fun t => airyAiReal (2 * t)) x := by
    by_cases hx : x ∈ Ioi u
    · simp [goeKer, hx, two_mul]
    · simp [goeKer, hx]
  simp_rw [hdiag]
  rw [integral_indicator measurableSet_Ioi, integral_comp_mul_left_Ioi _ _ two_pos]
  simp [smul_eq_mul, one_div]

/-- The one-point Fredholm tail has the sharp Airy₁ prefactor used in arXiv:2611.23658v1,
Lemma 4.2. The first determinant term is the GOE operator's diagonal trace. -/
theorem goe_singleton_right_tail_sub_profile_isLittleO :
    (fun u : ℝ => 1 - AiryFdd.airy1FinCdf {0} (fun _ => u) -
      AiryConj.rhoM u / (8 * u)) =o[atTop] (fun u => AiryConj.rhoM u / u) := by
  have hrate {u : ℝ} (hu : 0 ≤ u) : rateI u = kappaC * u ^ (3 / 2 : ℝ) := by
    have htwo := rpow_three_halves_eq (by norm_num : (0 : ℝ) ≤ 2)
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hcoef : (2 / 3 : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ) = kappaC := by
      rw [htwo, pow_succ, hs, kappaC]
      ring
    unfold rateI
    rw [Real.mul_rpow two_pos.le hu, ← mul_assoc, hcoef]
  have hpow {u : ℝ} (hu : 0 ≤ u) :
      u ^ (3 / 2 : ℝ) = u * Real.sqrt u := by
    rw [rpow_three_halves_eq hu, pow_succ, Real.sq_sqrt hu]
  have hrate_large : ∀ᶠ u : ℝ in atTop, 32 * (1 + u) ≤ rateI u / 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      Real.tendsto_sqrt_atTop.eventually_ge_atTop (128 / kappaC)] with u hu hs
    have hu0 : 0 ≤ u := by linarith
    rw [hrate hu0, hpow hu0]
    have hm := (div_le_iff₀ kappaC_pos).mp hs
    have hm' := mul_le_mul_of_nonneg_right hm hu0
    linarith
  let D := (2 * Real.exp 1 + 1) * tpConst ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrem : ∀ᶠ u : ℝ in atTop,
      ‖1 - AiryFdd.airy1FinCdf {0} (fun _ => u) - trace (goeOp u)‖ ≤
        D * Real.exp (-(3 / 2 : ℝ) * rateI u) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_ge_atTop goeLevel0,
      hrate_large] with u hu hlarge hrate_u
    let n := traceNorm (goeOp u)
    have htc := isTraceClass_goeOp u
    have hn0 : 0 ≤ n := traceNorm_nonneg _
    have hn : n ≤ 1 / 2 :=
      traceNorm_le_of_traceENorm_le (by norm_num) (traceENorm_goeOp_le_half hlarge)
    have hhs0 : 0 ≤ hsNorm (goeOp u) := hsNorm_nonneg _
    have hhs := hsNorm_le_traceNorm htc.traceENorm_ne_top
    have htr := norm_trace_le_traceNorm htc.traceENorm_ne_top
    have hhalf : hsNorm (goeOp u) ≤ 1 / 2 := hhs.trans hn
    have hsmall : hsNorm (goeOp u) < 1 := hhalf.trans_lt (by norm_num)
    have hcdf := airy1FinCdf_singleton_eq_goe 0 (fun _ => u)
    rw [hcdf, fredholmDet_eq_fredholmDetOne htc (by simpa only [norm_one, one_mul] using hsmall)]
    have hhs_sq : hsNorm (goeOp u) ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hhs0 hhs 2
    have haux0 : 0 ≤ ‖trace (goeOp u)‖ + hsNorm (goeOp u) ^ 2 :=
      add_nonneg (norm_nonneg _) (sq_nonneg _)
    have haux : ‖trace (goeOp u)‖ + hsNorm (goeOp u) ^ 2 ≤ 2 * n := by
      nlinarith [mul_nonneg hn0 (show 0 ≤ 1 - n by linarith)]
    have hsq := pow_le_pow_left₀ haux0 haux 2
    have he : Real.exp (‖trace (goeOp u)‖ + hsNorm (goeOp u) ^ 2) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (haux.trans (by linarith))
    have hn_bound : n ≤ tpConst * Real.exp (-rateI u + 16 * (1 + u)) :=
      traceNorm_le_of_traceENorm_le (by positivity [tpConst_pos]) (traceENorm_goeOp_le hu)
    calc
      _ ≤ (‖trace (goeOp u)‖ + hsNorm (goeOp u) ^ 2) ^ 2 / 2 *
            Real.exp (‖trace (goeOp u)‖ + hsNorm (goeOp u) ^ 2) + hsNorm (goeOp u) ^ 2 :=
        norm_one_sub_fredholmDetOne_one_sub_trace_le htc hsmall hhalf
      _ ≤ (2 * n) ^ 2 / 2 * Real.exp 1 + n ^ 2 := by
        exact add_le_add (mul_le_mul (div_le_div_of_nonneg_right hsq (by norm_num))
          he (Real.exp_pos _).le (by positivity)) hhs_sq
      _ = (2 * Real.exp 1 + 1) * n ^ 2 := by ring
      _ ≤ (2 * Real.exp 1 + 1) *
          (tpConst * Real.exp (-rateI u + 16 * (1 + u))) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0 hn_bound 2) (by positivity)
      _ = D * Real.exp (2 * (-rateI u + 16 * (1 + u))) := by
        have hs_exp (x : ℝ) : Real.exp x ^ 2 = Real.exp (2 * x) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        rw [mul_pow, hs_exp]
        dsimp [D]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hD
  have hratio_limit : Tendsto
      (fun u : ℝ => (D / Cstar) * (u ^ (3 / 4 : ℝ) *
        Real.exp (-(kappaC / 2) * u ^ (3 / 2 : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_rpow (kappaC / 2) (by positivity [kappaC_pos])
        (3 / 4)).const_mul (D / Cstar)
  have hdet :
      (fun u : ℝ => 1 - AiryFdd.airy1FinCdf {0} (fun _ => u) - trace (goeOp u))
        =o[atTop] (fun u => rhoM u / u) := by
    refine Asymptotics.isLittleO_iff.2 fun ε hε => ?_
    filter_upwards [hrem, eventually_gt_atTop (0 : ℝ),
      hratio_limit.eventually (gt_mem_nhds hε)] with u hu hu0 hratio
    have hprofile : 0 < rhoM u / u := div_pos (rhoM_pos hu0) hu0
    rw [Real.norm_of_nonneg hprofile.le]
    refine hu.trans ?_
    have heq : D * Real.exp (-(3 / 2 : ℝ) * rateI u) =
        ((D / Cstar) * (u ^ (3 / 4 : ℝ) *
          Real.exp (-(kappaC / 2) * u ^ (3 / 2 : ℝ)))) * (rhoM u / u) := by
      rw [hrate hu0.le, rhoM_div_eq hu0]
      have hmul : u ^ (3 / 4 : ℝ) * u ^ (-3 / 4 : ℝ) = 1 := by
        rw [← Real.rpow_add hu0, show (3 / 4 : ℝ) + -3 / 4 = 0 by norm_num, Real.rpow_zero]
      have he : Real.exp (-(kappaC / 2) * u ^ (3 / 2 : ℝ)) *
          Real.exp (-kappaC * u ^ (3 / 2 : ℝ)) =
          Real.exp (-(3 / 2 : ℝ) * (kappaC * u ^ (3 / 2 : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (D / Cstar * Cstar) * (u ^ (3 / 4 : ℝ) * u ^ (-3 / 4 : ℝ)) *
          (Real.exp (-(kappaC / 2) * u ^ (3 / 2 : ℝ)) *
            Real.exp (-kappaC * u ^ (3 / 2 : ℝ))) := by rw [hmul, he, div_mul_cancel₀ _ Cstar_pos.ne', mul_one]
        _ = _ := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hratio.le hprofile.le
  have htrace :
      (fun u : ℝ => trace (goeOp u) - rhoM u / (8 * u)) =o[atTop] (fun u => rhoM u / u) := by
    refine (integral_Ioi_airyAiReal_sub_rhoM_div_isLittleO.const_mul_left (1 / 2)).congr ?_ (fun _ => rfl)
    intro u
    rw [trace_goeOp_eq_half_integral]
    ring
  exact (hdet.add htrace).congr (fun _ => by ring) (fun _ => rfl)

/-- Two-sided bounds for the right tail of the continuous Airy₁ one-point marginal. -/
theorem one_point_tail_profile_bounds_airy1 (h : Airy1FddPositive) (hT : GOELeftTail) :
    ∃ A B u₀ : ℝ, 0 < A ∧ 0 < B ∧ 0 < u₀ ∧
      ∀ u : ℝ, u₀ ≤ u →
        A * (AiryConj.rhoM u / u) ≤
          (airy1Law h).real {f | u < airy1ContR h 0 f} ∧
        (airy1Law h).real {f | u < airy1ContR h 0 f} ≤ B * (AiryConj.rhoM u / u) := by
  obtain ⟨u₀, hb⟩ := eventually_atTop.mp
    (goe_singleton_right_tail_sub_profile_isLittleO.def (show (0 : ℝ) < 1 / 16 by norm_num))
  refine ⟨1 / 16, 3 / 16, max 1 u₀, by norm_num, by norm_num,
    one_pos.trans_le (le_max_left _ _), ?_⟩
  intro u hu
  have hu0 : 0 < u := one_pos.trans_le ((le_max_left _ _).trans hu)
  have hp : 0 < rhoM u / u := div_pos (rhoM_pos hu0) hu0
  have hb_u := hb u ((le_max_right _ _).trans hu)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp, abs_le] at hb_u
  change _ ≤ (airy1Law h).real {f | (airy1SRP h hT).A 0 f > u} ∧
    (airy1Law h).real {f | (airy1SRP h hT).A 0 f > u} ≤ _
  rw [airy1SRP_gt_eq h hT, airy1Law_coord_gt h]
  rw [show rhoM u / (8 * u) = (rhoM u / u) / 8 by ring] at hb_u
  exact ⟨by linarith [hb_u.1], by linarith [hb_u.2]⟩

/-- Lowering a high threshold by the reciprocal square root of its level changes the
Airy₁ one-point tail by at most a constant factor. -/
theorem one_point_tail_shift_le_airy1 (h : Airy1FddPositive) (hT : GOELeftTail) :
    ∃ K u₀ : ℝ, 0 < K ∧ 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      (airy1Law h).real {f | u - (Real.sqrt u)⁻¹ < airy1ContR h 0 f}
        ≤ K * (airy1Law h).real {f | u < airy1ContR h 0 f} := by
  obtain ⟨A, B, U, hA, hB, hU, hb⟩ := one_point_tail_profile_bounds_airy1 h hT
  let J := (2 : ℝ) ^ (3 / 4 : ℝ) * Real.exp (2 * kappaC)
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨B * J / A, 2 * max 1 U, by positivity, by positivity, ?_⟩
  intro u hu
  have hu2 : 2 ≤ u := by
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left (le_max_left 1 U) two_pos.le).trans hu
  have hu0 : 0 < u := by linarith
  let s := Real.sqrt u
  let v := u - s⁻¹
  have hs : 0 < s := Real.sqrt_pos.2 hu0
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (by linarith)
  have hhalf : u / 2 ≤ v := by
    have hinv : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
    dsimp [v]
    linarith
  have hv : v ≤ u := sub_le_self _ (inv_nonneg.mpr hs.le)
  have hv0 : 0 < v := (half_pos hu0).trans_le hhalf
  have hvU : U ≤ v := by
    have hU' := mul_le_mul_of_nonneg_left (le_max_right 1 U) two_pos.le
    linarith
  have hs_sq : s ^ 2 = u := Real.sq_sqrt hu0.le
  have hv_sq := Real.sq_sqrt hv0.le
  have hroot_gap : s - Real.sqrt v = (u - v) / (s + Real.sqrt v) := by
    apply (eq_div_iff (by positivity : s + Real.sqrt v ≠ 0)).2
    nlinarith
  have hweighted_gap : v * (s - Real.sqrt v) ≤ s * (u - v) := by
    rw [hroot_gap, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < s + Real.sqrt v)).2
    have hnum : v ≤ s * (s + Real.sqrt v) := by
      nlinarith [mul_nonneg hs.le (Real.sqrt_nonneg v)]
    nlinarith [mul_le_mul_of_nonneg_right hnum (sub_nonneg.mpr hv)]
  have hp (w : ℝ) (hw : 0 ≤ w) : w ^ (3 / 2 : ℝ) = w * Real.sqrt w := by
    rw [rpow_three_halves_eq hw, pow_succ, Real.sq_sqrt hw]
  have hphase : u ^ (3 / 2 : ℝ) - v ^ (3 / 2 : ℝ) ≤ 2 := by
    rw [hp u hu0.le, hp v hv0.le]
    change u * s - v * Real.sqrt v ≤ 2
    have hδ : s * (u - v) = 1 := by
      dsimp [v]
      rw [sub_sub_cancel, mul_inv_cancel₀ hs.ne']
    linarith [hweighted_gap, show u * s - v * Real.sqrt v =
        s * (u - v) + v * (s - Real.sqrt v) by ring]
  have hpow : v ^ (-3 / 4 : ℝ) ≤ (2 : ℝ) ^ (3 / 4 : ℝ) * u ^ (-3 / 4 : ℝ) := by
    refine (Real.rpow_le_rpow_of_nonpos (half_pos hu0) hhalf (by norm_num)).trans_eq ?_
    rw [Real.div_rpow hu0.le two_pos.le,
      show (2 : ℝ) ^ (-3 / 4 : ℝ) = ((2 : ℝ) ^ (3 / 4 : ℝ))⁻¹ by
        rw [show (-3 / 4 : ℝ) = -(3 / 4) by ring, Real.rpow_neg two_pos.le]]
    simp [div_eq_mul_inv, mul_comm]
  have hexp : Real.exp (-kappaC * v ^ (3 / 2 : ℝ)) ≤
      Real.exp (2 * kappaC) * Real.exp (-kappaC * u ^ (3 / 2 : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [mul_le_mul_of_nonneg_right hphase kappaC_pos.le]
  have hratio : rhoM v / v ≤ J * (rhoM u / u) := by
    rw [rhoM_div_eq hv0, rhoM_div_eq hu0]
    calc
      _ ≤ Cstar * ((2 : ℝ) ^ (3 / 4 : ℝ) * u ^ (-3 / 4 : ℝ)) *
            (Real.exp (2 * kappaC) * Real.exp (-kappaC * u ^ (3 / 2 : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow Cstar_pos.le) hexp
          (Real.exp_pos _).le (by positivity [Cstar_pos])
      _ = _ := by dsimp [J]; ring
  calc
    _ ≤ B * (rhoM v / v) := (hb v hvU).2
    _ ≤ B * (J * (rhoM u / u)) := mul_le_mul_of_nonneg_left hratio hB.le
    _ = (B * J / A) * (A * (rhoM u / u)) := by field_simp [hA.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb u (hvU.trans hv)).1 (by positivity)

/-- The continuous Airy₁ one-point marginals have finite second moments. -/
theorem memLp_two_airy1ContR (h : Airy1FddPositive) (hT : GOELeftTail) (t : ℝ) :
    MemLp (airy1ContR h t) 2 (airy1Law h) := by
  let P := airy1Law h
  let X := airy1ContR h t
  have hXm : Measurable X := measurable_airy1ContR h t
  obtain ⟨_, B, U, _, hB, _, hright⟩ := one_point_tail_profile_bounds_airy1 h hT
  obtain ⟨C, c, hC, hc, hleft⟩ := hT.airy1Law_le_ofReal h
  let b := max 1 U
  let m := min kappaC c
  have hm : 0 < m := lt_min kappaC_pos hc
  let D := B * Cstar + C + Real.exp (m * b)
  have hD : 0 < D := by dsimp [D]; positivity [Cstar_pos]
  have htail (v : ℝ) (hv : 0 ≤ v) :
      P {f | v < |X f|} ≤ ENNReal.ofReal (D * Real.exp (-m * v)) := by
    by_cases hvb : b ≤ v
    · have hv1 : 1 ≤ v := (le_max_left _ _).trans hvb
      have hvU : U ≤ v := (le_max_right _ _).trans hvb
      have hv0 : 0 < v := one_pos.trans_le hv1
      have hR : P {f | v < X f} ≤ ENNReal.ofReal (B * Cstar * Real.exp (-m * v)) := by
        rw [← ofReal_measureReal (measure_ne_top _ _)]
        change ENNReal.ofReal ((airy1Law h).real {f | (airy1SRP h hT).A t f > v}) ≤ _
        rw [(airy1SRP h hT).measureReal_gt_eq t v]
        apply ENNReal.ofReal_le_ofReal
        have hp := (hright v hvU).2
        rw [rhoM_div_eq hv0] at hp
        refine hp.trans ?_
        have hpow : v ^ (-3 / 4 : ℝ) ≤ 1 := by
          simpa using Real.rpow_le_rpow_of_nonpos one_pos hv1 (by norm_num : (-3 / 4 : ℝ) ≤ 0)
        have hphase : v ≤ v ^ (3 / 2 : ℝ) := by
          rw [rpow_three_halves_eq hv, pow_succ, Real.sq_sqrt hv]
          exact le_mul_of_one_le_right hv (Real.one_le_sqrt.mpr hv1)
        have he : Real.exp (-kappaC * v ^ (3 / 2 : ℝ)) ≤ Real.exp (-m * v) := by
          apply Real.exp_le_exp.mpr
          linarith [mul_le_mul_of_nonneg_left hphase kappaC_pos.le,
            mul_le_mul_of_nonneg_right (min_le_left kappaC c) hv]
        calc
          _ = (B * Cstar) * (v ^ (-3 / 4 : ℝ) * Real.exp (-kappaC * v ^ (3 / 2 : ℝ))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (by simpa using mul_le_mul hpow he (Real.exp_pos _).le zero_le_one)
            (mul_nonneg hB.le Cstar_pos.le)
      have hL : P {f | X f < -v} ≤ ENNReal.ofReal (C * Real.exp (-m * v)) := by
        have hae : {f | X f < -v} ≤ᵐ[P] {f : ℝ → ℝ | f t ≤ -v} := by
          filter_upwards [airy1ContR_ae_eq h hT t] with f hf hmem
          exact le_of_lt (hf ▸ hmem)
        refine (measure_mono_ae hae).trans ((hleft t v hv).trans ?_)
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Real.exp_le_exp.mpr
        have hcube : v ≤ v ^ 3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hv1) (sq_nonneg v)]
        linarith [mul_le_mul_of_nonneg_left hcube hc.le,
          mul_le_mul_of_nonneg_right (min_le_right kappaC c) hv]
      have hset : {f | v < |X f|} ⊆ {f | v < X f} ∪ {f | X f < -v} := by
        intro f hf
        change v < |X f| at hf
        by_cases hsign : 0 ≤ X f
        · exact Or.inl (by change v < X f; rwa [abs_of_nonneg hsign] at hf)
        · rw [abs_of_neg (lt_of_not_ge hsign)] at hf
          exact Or.inr (by change X f < -v; linarith)
      calc
        _ ≤ P {f | v < X f} + P {f | X f < -v} :=
          (measure_mono hset).trans (measure_union_le _ _)
        _ ≤ ENNReal.ofReal (B * Cstar * Real.exp (-m * v)) +
            ENNReal.ofReal (C * Real.exp (-m * v)) := add_le_add hR hL
        _ ≤ _ := by
          rw [← ENNReal.ofReal_add (by positivity [Cstar_pos]) (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          dsimp [D]
          nlinarith [mul_nonneg (Real.exp_pos (m * b)).le (Real.exp_pos (-m * v)).le]
    · have hlarge : 1 ≤ D * Real.exp (-m * v) := by
        calc
          1 = Real.exp (m * b - m * b) := by simp
          _ ≤ Real.exp (m * b - m * v) := Real.exp_le_exp.mpr (by
            linarith [mul_le_mul_of_nonneg_left (le_of_not_ge hvb) hm.le])
          _ = Real.exp (m * b) * Real.exp (-m * v) := by rw [sub_eq_add_neg, Real.exp_add, neg_mul]
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            dsimp [D]
            linarith [show 0 ≤ B * Cstar by positivity [Cstar_pos]]
      exact (measure_mono (subset_univ _)).trans
        (by simpa only [measure_univ, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hlarge)
  have hAbs : Measurable fun f => |X f| := by simpa only [Real.norm_eq_abs] using hXm.norm
  have hcake := lintegral_comp_eq_lintegral_meas_lt_mul (f := fun f => |X f|)
    (g := fun v : ℝ => 2 * v) P (Eventually.of_forall fun _ => abs_nonneg _)
    hAbs.aemeasurable
    (fun _ _ => (continuous_const.mul continuous_id).intervalIntegrable _ _)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        exact mul_nonneg two_pos.le (le_of_lt hv))
  have hcalc (f : ℝ → ℝ) : (∫ v in 0..|X f|, 2 * v) = X f ^ 2 := by
    rw [intervalIntegral.integral_const_mul]
    have hi := integral_pow (a := (0 : ℝ)) (b := |X f|) (n := 1)
    simp only [pow_one, Nat.reduceAdd, zero_pow (by decide : 2 ≠ 0)] at hi
    rw [hi, sq_abs]
    ring
  simp_rw [hcalc] at hcake
  have henv : IntegrableOn (fun v : ℝ => (2 * D) * (v * Real.exp (-m * v))) (Ioi 0) := by
    have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := m)
      (by norm_num) one_pos hm
    simpa only [IntegrableOn, Real.rpow_one, neg_mul] using hi.const_mul (2 * D)
  have henv_lt : (∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal ((2 * D) * (v * Real.exp (-m * v)))) < ⊤ := by
    have hpos : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun v => (2 * D) * (v * Real.exp (-m * v))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact mul_nonneg (by positivity) (mul_nonneg (le_of_lt hv) (Real.exp_pos _).le)
    exact ((lintegral_ofReal_ne_top_iff_integrable henv.aestronglyMeasurable hpos).mpr henv).lt_top
  have hfinite : (∫⁻ f, ENNReal.ofReal (X f ^ 2) ∂P) < ⊤ := by
    rw [hcake]
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) henv_lt
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    calc
      _ ≤ ENNReal.ofReal (D * Real.exp (-m * v)) * ENNReal.ofReal (2 * v) :=
        mul_le_mul' (htail v (le_of_lt hv)) le_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  apply (memLp_two_iff_integrable_sq hXm.aestronglyMeasurable).2
  exact (lintegral_ofReal_ne_top_iff_integrable (hXm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun _ => sq_nonneg _)).1 hfinite.ne

/-- Lemma 4.2, equation (4.3) of arXiv:2611.23658v1. The threshold-sensitive
Newman bound holds uniformly over nonnegative lags for the continuous Airy₁ version. -/
theorem tail_sensitive_newman_airy1 (h : Airy1FddPositive) (hT : GOELeftTail)
    (As : ProcessAssociated (airy1SRP h hT)) :
    ∃ C u₀ : ℝ, 0 < C ∧ ∀ u d : ℝ, u₀ ≤ u → 0 ≤ d →
      (airy1Law h).real {f | u < airy1ContR h 0 f ∧ u < airy1ContR h d f}
        ≤ C * ((airy1Law h).real {f | u < airy1ContR h 0 f}) ^ 2 +
          C * u * covariance (airy1ContR h 0) (airy1ContR h d) (airy1Law h) := by
  obtain ⟨K, U, hK, hU, hshift⟩ := one_point_tail_shift_le_airy1 h hT
  let C := max 1 (K ^ 2)
  have hC : 1 ≤ C := le_max_left 1 _
  refine ⟨C, U, one_pos.trans_le hC, ?_⟩
  intro u d hu _
  have hu0 : 0 < u := hU.trans_le hu
  let P := airy1Law h
  let W := airy1SRP h hT
  let s : ℝ≥0 := ⟨Real.sqrt u, Real.sqrt_nonneg _⟩
  have hs : 0 < (s : ℝ) := Real.sqrt_pos.2 hu0
  let v := u - (s : ℝ)⁻¹
  let g (x : ℝ) := clampInd ((s : ℝ) * u) ((s : ℝ) * x)
  let G (t : ℝ) := g ∘ W.A t
  let p := P.real {f | u < W.A 0 f}
  change P.real {f | u < W.A 0 f ∧ u < W.A d f} ≤ C * p ^ 2 +
    C * u * covariance (W.A 0) (W.A d) P
  have hg0 (x : ℝ) : 0 ≤ g x := clampInd_nonneg _ _
  have hg1 (x : ℝ) : g x ≤ 1 := clampInd_le_one _ _
  have hgon {x : ℝ} (hx : u < x) : g x = 1 :=
    clampInd_eq_one_of_lt (mul_lt_mul_of_pos_left hx hs)
  have hgoff {x : ℝ} (hx : x ≤ v) : g x = 0 := by
    apply clampInd_eq_zero_of_le
    have hv : (s : ℝ) * v = (s : ℝ) * u - 1 := by
      dsimp [v]
      rw [mul_sub, mul_inv_cancel₀ hs.ne']
    rw [← hv]
    exact mul_le_mul_of_nonneg_left hx hs.le
  have hLip : LipschitzWith s g := by
    have hscale : LipschitzWith s (fun x : ℝ => (s : ℝ) * x) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hs.le]
    simpa only [one_mul, Function.comp_def, g] using (clampInd_lipschitzWith ((s : ℝ) * u)).comp hscale
  have hGm (t : ℝ) : Measurable (G t) := hLip.continuous.measurable.comp (W.A_meas t)
  have hG2 (t : ℝ) : MemLp (G t) 2 P :=
    memLp_of_bounded (a := 0) (b := 1) (Eventually.of_forall fun f => ⟨hg0 _, hg1 _⟩)
      (hGm t).aestronglyMeasurable 2
  have hmean0 (t : ℝ) : 0 ≤ ∫ f, G t f ∂P := integral_nonneg fun _ => hg0 _
  have hmean (t : ℝ) : (∫ f, G t f ∂P) ≤ K * p := by
    let E : Set (ℝ → ℝ) := {f | v < W.A t f}
    have hE : MeasurableSet E := measurableSet_lt measurable_const (W.A_meas t)
    calc
      _ ≤ ∫ f, E.indicator (1 : (ℝ → ℝ) → ℝ) f ∂P := by
        refine integral_mono ((hG2 t).integrable (by norm_num)) ((integrable_const (1 : ℝ)).indicator hE) ?_
        intro f
        by_cases hf : f ∈ E
        · rw [Set.indicator_of_mem hf]
          exact hg1 _
        · rw [Set.indicator_of_notMem hf]
          have hz : G t f = 0 := hgoff (le_of_not_gt hf)
          simpa only [hz] using (le_rfl : (0 : ℝ) ≤ 0)
      _ = P.real E := integral_indicator_one hE
      _ = P.real {f | v < W.A 0 f} := W.measureReal_gt_eq t v
      _ ≤ _ := hshift u hu
  have hprod : Integrable (G 0 * G d) P := (hG2 0).integrable_mul (hG2 d)
  have hE : MeasurableSet {f | u < W.A 0 f ∧ u < W.A d f} :=
    (measurableSet_lt measurable_const (W.A_meas 0)).inter
      (measurableSet_lt measurable_const (W.A_meas d))
  have hpair : P.real {f | u < W.A 0 f ∧ u < W.A d f} ≤ ∫ f, (G 0 * G d) f ∂P := by
    rw [← integral_indicator_one hE]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hE) hprod ?_
    intro f
    by_cases hf : f ∈ {f | u < W.A 0 f ∧ u < W.A d f}
    · rw [Set.indicator_of_mem hf, Pi.mul_apply,
        show G 0 f = 1 from hgon hf.1, show G d f = 1 from hgon hf.2, mul_one]
      exact le_rfl
    · rw [Set.indicator_of_notMem hf, Pi.mul_apply]
      exact mul_nonneg (hg0 _) (hg0 _)
  have hnew := newman_pair As (memLp_two_airy1ContR h hT) 0 d hLip hLip
  have hnew' : |covariance (G 0) (G d) P| ≤ u * covariance (W.A 0) (W.A d) P := by
    change |covariance (G 0) (G d) P| ≤
      (s : ℝ) * (s : ℝ) * covariance (W.A 0) (W.A d) P at hnew
    rw [← sq, show (s : ℝ) ^ 2 = u from Real.sq_sqrt hu0.le] at hnew
    exact hnew
  have huCov : 0 ≤ u * covariance (W.A 0) (W.A d) P := (abs_nonneg _).trans hnew'
  calc
    _ ≤ ∫ f, (G 0 * G d) f ∂P := hpair
    _ = (∫ f, G 0 f ∂P) * (∫ f, G d f ∂P) + covariance (G 0) (G d) P := by
      rw [covariance_eq_sub (hG2 0) (hG2 d)]
      ring
    _ ≤ (K * p) ^ 2 + u * covariance (W.A 0) (W.A d) P := by
      rw [sq]
      exact add_le_add
        (mul_le_mul (hmean 0) (hmean d) (hmean0 d) ((hmean0 0).trans (hmean 0)))
        ((le_abs_self _).trans hnew')
    _ ≤ _ := by
      rw [mul_pow, show C * u * covariance (W.A 0) (W.A d) P =
        C * (u * covariance (W.A 0) (W.A d) P) by ring]
      exact add_le_add (mul_le_mul_of_nonneg_right (le_max_right 1 _) (sq_nonneg _))
        (le_mul_of_one_le_left huCov hC)

end Airy1Gumbel
