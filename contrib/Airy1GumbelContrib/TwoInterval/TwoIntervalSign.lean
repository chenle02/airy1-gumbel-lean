/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoInterval.TwoIntervalPlemelj
import Airy1GumbelContrib.TwoInterval.TwoIntervalN2
import Airy1GumbelContrib.TwoInterval.TwoIntervalSumEst
import Airy1GumbelContrib.AiryKernel.TailAsymptotic

/-!
# The sign certificate for the two-interval record: `X ≥ (1 − ε) π₁² > 0`

Part of `TwoInterval/`.  This module completes the Plemelj-exponent argument for the sign
of the two-interval joint term.  It feeds the
three discharged analytic inputs

* N1 `trace_crKerT_ge_neg_discharged_a` (`Tr C̃_r ≥ −C e^{−a⁴/64}`),
* N2 `trace_k1k2_le_discharged`
  (`tr(K̃₁K̃₂) ≤ C(1+2M²)(1+256M) e^{−(4/3)a³ − 2ar²}`),
* N3 `hsNorm_crKerT_le_discharged` (`‖C̃_r‖₂ ≤ C e^{−(2/3)a³ − rM}`),

into the assembly `twoInt_joint_ge_plemelj_eventually` (TwoIntervalPlemelj.lean),
and compares the margin `Δ` with the one-block lower bound `π₁ ≥ ρ(M)/2`.

## Conventions

`a = √(2M)`; `d₁ = det₁(I − K̃₁)` for `K̃₁ = kernelOperator (k1KerT a M)` (identified
with `AiryConj.detOneAiryTilde M 1` by `fredholmDetOne_k1KerT_eq_detOneAiryTilde`, since
`K̃₁ = Ã_{M,1}` as operators); `π₁ = 1 − d₁`; `X = 1 − d₁ − d₂ + d∪` exactly as in
`twoInt_joint_ge_plemelj`.

## Headlines

* `twoInt_joint_ge_assoc_eventually`: for `0 < χ < 1` and `ε > 0`, there is `M₀` such
  that for `M ≥ M₀`, `1 ≤ r ≤ χ√(2M)` and any `MemLp`/trace-class proof terms,
  `ρ(M)/2 ≤ π₁` and `(1 − ε) π₁² ≤ X` (association shape `X ≥ π₁²(1 − o(1))`).
* `twoInt_joint_pos_eventually`: under the same quantifiers, `0 < X`.

## The absorption (`plemeljMargin_le`)

For `M ≥ 10⁴`, `1 ≤ r ≤ a`, and `η ≤ 1/2`, each of the five terms of
`Δ = C₁e^{−a⁴/64} + e₂ + 2ηe₃ + e₃²/2 + η³/(1−η)` is at most
`(constant) · (polynomial in M) · e^{−(4/3)a³} · e^{−√M}`:
`a⁴/64 ≥ (4/3)a³ + √M` (needs `√M ≥ 100`), `2ar² ≥ √M`, `rM ≥ √M`, `2rM ≥ √M`, and
`(2/3)a³ ≥ √M`.  Since `ρ² = C_*² M^{1/2} e^{−(4/3)a³}` (`rhoM_sq_eq`) and
`M^p e^{−√M} → 0` (`tendsto_rpow_mul_exp_neg_sqrt`), `Δ ≤ ε ρ²/4 ≤ ε π₁²` eventually.

## Range covered

Every `χ < 1`, `1 ≤ r ≤ χ√(2M)`, `M ≥ M₀(χ, ε)`.  The guard `r + 3 ≤ a` of the two-interval record
allows `r` up to `a − 3`; the strip `χa < r ≤ a − 3` is NOT covered for any fixed
`χ < 1` (the constants of N1–N3, `twoInt_stepThree` and the one-block lower bound are uniform only
on
`r ≤ χa`).
-/

namespace AiryTwoInt

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal InnerProduct InnerProductSpace
open HilbertSchmidt

/-! ### Real-analysis helpers -/

/-- `M^p e^{−√M} → 0` as `M → ∞`, for every real `p`. -/
theorem tendsto_rpow_mul_exp_neg_sqrt (p : ℝ) :
    Tendsto (fun M : ℝ => M ^ p * Real.exp (-Real.sqrt M)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * p) 1 one_pos).comp
    Real.tendsto_sqrt_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with M hM
  have hp : Real.sqrt M ^ (2 * p) = M ^ p := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hM]
    congr 1
    ring
  simp only [Function.comp_apply, neg_mul, one_mul, hp]

/-- `ρ(M)² = C_*² M^{1/2} e^{−(4/3)(√(2M))³}` (the κ-identity
`(2/3)(2M)^{3/2} = κM^{3/2}`). -/
theorem rhoM_sq_eq {M : ℝ} (hM : 0 ≤ M) :
    AiryConj.rhoM M ^ 2
      = AiryConj.Cstar ^ 2 * M ^ (1/2 : ℝ) * Real.exp (-(4/3) * Real.sqrt (2*M) ^ 3) := by
  unfold AiryConj.rhoM AiryConj.kappaC
  have h1 : (M ^ (1/4 : ℝ)) ^ 2 = M ^ (1/2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
    norm_num
  have h2 : (Real.exp (-(4 * Real.sqrt 2 / 3) * M ^ (3/2 : ℝ))) ^ 2
      = Real.exp (-(4/3) * Real.sqrt (2*M) ^ 3) := by
    rw [sq, ← Real.exp_add, rpow_sqrt_two_mul_cube hM]
    congr 1
    have k := kappa_rpow_identity hM
    linear_combination 2 * k
  rw [mul_pow, mul_pow, h1, h2]

/-- **The identification `K̃₁ = Ã_{M,1}` at the determinant level**: at `a = √(2M) ≥ 2`,
`det₁(I − K̃₁)` (any proof
terms) is the contrib `AiryConj.detOneAiryTilde M 1`. -/
theorem fredholmDetOne_k1KerT_eq_detOneAiryTilde {M : ℝ} (hM : 0 < M)
    (ha : 2 ≤ Real.sqrt (2*M))
    (hk1 : MemLp (k1KerT (Real.sqrt (2*M)) M) 2 (volume.prod volume))
    (hk1t : IsTraceClass (kernelOperator hk1)) :
    fredholmDetOne (kernelOperator hk1) hk1t 1 = AiryConj.detOneAiryTilde M 1 := by
  have h2 : (1 : ℝ) + 1 ≤ Real.sqrt (2 * M) := by linarith
  rw [AiryConj.detOneAiryTilde, dite_eq_left ⟨one_pos, hM, h2⟩]
  exact fredholmDetOne_congr
    ((kernelOperator_congr rfl hk1 (memLp_k1KerT hM ha)).trans
      (kernelOperator_k1KerT_eq_airyTildeOp hM ha)) _ _ 1

/-- **One-block lower bound**: eventually `M ≥ 1` and `π₁(M) = 1 − det₁(I − Ã_{M,1}) ≥ ρ(M)/2`
(from `piT_sub_traceLead_isLittleO` at `T = 1`, `ε = 1/16`). -/
theorem exists_piOne_ge_half_rho :
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M →
      1 ≤ M ∧ AiryConj.rhoM M / 2 ≤ 1 - AiryConj.detOneAiryTilde M 1 := by
  have h := (AiryConj.piT_sub_traceLead_isLittleO 1 one_pos
    (fun M => 1 - AiryConj.detOneAiryTilde M 1) (fun _ => rfl)).def
    (by norm_num : (0 : ℝ) < 1 / 16)
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (h.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨h1, hM1⟩ := hM₀ M hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hρ : 0 < AiryConj.rhoM M := AiryConj.rhoM_pos hM0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (div_pos hρ hM0)] at h1
  have hq : AiryConj.rhoM M / M ≤ AiryConj.rhoM M := div_le_self hρ.le hM1
  have hL : AiryConj.traceLead M 1 = AiryConj.rhoM M + AiryConj.rhoM M / (4 * M) := by
    unfold AiryConj.traceLead
    ring
  have hq4 : 0 ≤ AiryConj.rhoM M / (4 * M) := div_nonneg hρ.le (by linarith)
  refine ⟨hM1, ?_⟩
  have h1' := (abs_le.mp h1).1
  rw [hL] at h1'
  linarith

/-! ### The absorption of the margin `Δ` -/

/-- **Margin absorption** (pure real analysis): for `M ≥ 10⁴`, `1 ≤ r ≤ √(2M)`,
nonnegative constants and `η ≤ 1/2`, the margin `Δ` of
`twoInt_joint_ge_plemelj_eventually` with `e₂`, `e₃` the N2/N3 bounds is at most
`(C₁ + 771C₂M³ + 2C₀3^{K₀}C₃(M^{K₀})² + C₃²/2 + 2C₀³(3^{K₀})³(M^{K₀})⁶)
 · e^{−(4/3)a³} e^{−√M}`. -/
theorem plemeljMargin_le {M r C₀ K₀ C₁ C₂ C₃ : ℝ} (hM : 10000 ≤ M) (hr : 1 ≤ r)
    (hra : r ≤ Real.sqrt (2*M)) (hC₀ : 0 ≤ C₀) (hK₀ : 0 ≤ K₀) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hη : C₀ * M ^ K₀ * (1+r) ^ (K₀:ℝ) * Real.exp (-(2/3) * (Real.sqrt (2*M)) ^ 3) ≤ 1/2) :
    C₁ * Real.exp (-(Real.sqrt (2*M)) ^ 4 / 64)
        + C₂ * (1 + 2 * M ^ 2) * (1 + 256 * M)
          * Real.exp (-(4/3) * Real.sqrt (2*M) ^ 3 - 2 * Real.sqrt (2*M) * r ^ 2)
        + 2 * (C₀ * M ^ K₀ * (1+r) ^ (K₀:ℝ) * Real.exp (-(2/3) * (Real.sqrt (2*M)) ^ 3))
          * (C₃ * Real.exp (-(2/3) * Real.sqrt (2*M) ^ 3 - r * M))
        + (C₃ * Real.exp (-(2/3) * Real.sqrt (2*M) ^ 3 - r * M)) ^ 2 / 2
        + (C₀ * M ^ K₀ * (1+r) ^ (K₀:ℝ) * Real.exp (-(2/3) * (Real.sqrt (2*M)) ^ 3)) ^ 3
          / (1 - C₀ * M ^ K₀ * (1+r) ^ (K₀:ℝ) * Real.exp (-(2/3) * (Real.sqrt (2*M)) ^ 3))
      ≤ (C₁ + 771 * C₂ * M ^ 3 + 2 * C₀ * 3 ^ K₀ * C₃ * (M ^ K₀) ^ 2 + C₃ ^ 2 / 2
          + 2 * C₀ ^ 3 * (3 ^ K₀) ^ 3 * (M ^ K₀) ^ 6)
        * (Real.exp (-(4/3) * Real.sqrt (2*M) ^ 3) * Real.exp (-Real.sqrt M)) := by
  have hM1 : (1:ℝ) ≤ M := by linarith
  have hM0 : (0:ℝ) ≤ M := by linarith
  have ha2 : Real.sqrt (2*M) ^ 2 = 2 * M := Real.sq_sqrt (by linarith)
  have has : Real.sqrt (2*M) = Real.sqrt 2 * Real.sqrt M := Real.sqrt_mul (by norm_num) M
  set a := Real.sqrt (2*M) with ha_def
  set s := Real.sqrt M with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = M := Real.sq_sqrt hM0
  have hs100 : 100 ≤ s := by nlinarith only [hs2, hM, hs0]
  have hsM : s ≤ M := by nlinarith only [hs2, hs100, hs0]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2le : Real.sqrt 2 ≤ 3/2 := by nlinarith only [h2, Real.sqrt_nonneg 2]
  have h2ge : 1 ≤ Real.sqrt 2 := by nlinarith only [h2, Real.sqrt_nonneg 2]
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hsa : s ≤ a := by rw [has]; nlinarith only [h2ge, hs0]
  have ha_le : a ≤ 3/2 * s := by rw [has]; nlinarith only [h2le, hs0]
  have ha3 : a ^ 3 ≤ 3 * s ^ 3 := by
    have e : a ^ 3 = a * a ^ 2 := by ring
    rw [e, ha2, ← hs2]
    have := mul_le_mul_of_nonneg_right ha_le (by positivity : (0:ℝ) ≤ 2 * s ^ 2)
    linarith [show 3/2 * s * (2 * s ^ 2) = 3 * s ^ 3 by ring]
  have ha4 : a ^ 4 = 4 * s ^ 4 := by
    have e : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [e, ha2, ← hs2]
    ring
  have ha3s : s ≤ (2/3) * a ^ 3 := by
    have e : a ^ 3 = a * (2 * M) := by rw [← ha2]; ring
    rw [e]
    linarith [mul_le_mul_of_nonneg_left hM1 ha0]
  -- the common target `E·X`
  set E := Real.exp (-(4/3) * a ^ 3) with hE
  set Xs := Real.exp (-s) with hXs
  have hEX : ∀ t : ℝ, t ≤ -(4/3) * a ^ 3 + -s → Real.exp t ≤ E * Xs := by
    intro t ht
    rw [hE, hXs, ← Real.exp_add]
    exact Real.exp_le_exp.mpr ht
  have hEX0 : 0 ≤ E * Xs := by rw [hE, hXs]; positivity
  -- the shared bound on η
  set P := M ^ K₀ with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hM0 _
  set e23 := Real.exp (-(2/3) * a ^ 3) with he23
  have he230 : 0 ≤ e23 := (Real.exp_pos _).le
  set η := C₀ * P * (1+r) ^ (K₀:ℝ) * e23 with hηdef
  have h1r : 1 + r ≤ 3 * M := by linarith
  have hrpow : (1+r) ^ (K₀:ℝ) ≤ 3 ^ K₀ * P := by
    calc (1+r) ^ (K₀:ℝ) ≤ (3 * M) ^ K₀ := Real.rpow_le_rpow (by linarith) h1r hK₀
      _ = 3 ^ K₀ * P := Real.mul_rpow (by norm_num) hM0
  have h3K : 0 ≤ (3:ℝ) ^ K₀ := Real.rpow_nonneg (by norm_num) _
  set ηb := C₀ * 3 ^ K₀ * P ^ 2 * e23 with hηb
  have hη0 : 0 ≤ η := by
    have : 0 ≤ (1+r) ^ (K₀:ℝ) := Real.rpow_nonneg (by linarith) _
    exact mul_nonneg (mul_nonneg (mul_nonneg hC₀ hP0) this) he230
  have hηle : η ≤ ηb := by
    have : C₀ * P * (1+r) ^ (K₀:ℝ) ≤ C₀ * P * (3 ^ K₀ * P) :=
      mul_le_mul_of_nonneg_left hrpow (mul_nonneg hC₀ hP0)
    calc η = C₀ * P * (1+r) ^ (K₀:ℝ) * e23 := rfl
      _ ≤ C₀ * P * (3 ^ K₀ * P) * e23 := mul_le_mul_of_nonneg_right this he230
      _ = ηb := by rw [hηb]; ring
  -- T1
  have T1 : C₁ * Real.exp (-a ^ 4 / 64) ≤ C₁ * (E * Xs) := by
    apply mul_le_mul_of_nonneg_left _ hC₁
    apply hEX
    have hs3 : 100 * s ^ 3 ≤ s ^ 4 :=
      calc 100 * s ^ 3 ≤ s * s ^ 3 := mul_le_mul_of_nonneg_right hs100 (pow_nonneg hs0 3)
        _ = s ^ 4 := by ring
    have hs1 : (1:ℝ) ≤ s ^ 2 := by nlinarith only [hs100]
    have hs31 : s ≤ s ^ 3 :=
      calc s = s * 1 := (mul_one s).symm
        _ ≤ s * s ^ 2 := mul_le_mul_of_nonneg_left hs1 hs0
        _ = s ^ 3 := by ring
    rw [ha4]
    linarith
  -- T2
  have T2 : C₂ * (1 + 2 * M ^ 2) * (1 + 256 * M)
        * Real.exp (-(4/3) * a ^ 3 - 2 * a * r ^ 2)
      ≤ 771 * C₂ * M ^ 3 * (E * Xs) := by
    have p1 : 1 + 2 * M ^ 2 ≤ 3 * M ^ 2 := by linarith [one_le_pow₀ (n := 2) hM1]
    have p2 : 1 + 256 * M ≤ 257 * M := by linarith
    have hpoly : (1 + 2 * M ^ 2) * (1 + 256 * M) ≤ 771 * M ^ 3 :=
      calc (1 + 2 * M ^ 2) * (1 + 256 * M) ≤ (3 * M ^ 2) * (257 * M) :=
            mul_le_mul p1 p2 (by linarith) (by positivity)
        _ = 771 * M ^ 3 := by ring
    have hex : Real.exp (-(4/3) * a ^ 3 - 2 * a * r ^ 2) ≤ E * Xs := by
      apply hEX
      have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
      linarith [mul_le_mul_of_nonneg_left hr2 ha0]
    calc C₂ * (1 + 2 * M ^ 2) * (1 + 256 * M) * Real.exp (-(4/3) * a ^ 3 - 2 * a * r ^ 2)
        = (C₂ * ((1 + 2 * M ^ 2) * (1 + 256 * M)))
            * Real.exp (-(4/3) * a ^ 3 - 2 * a * r ^ 2) := by ring
      _ ≤ (C₂ * (771 * M ^ 3)) * (E * Xs) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpoly hC₂) hex (Real.exp_pos _).le
            (mul_nonneg hC₂ (mul_nonneg (by norm_num) (pow_nonneg hM0 3)))
      _ = 771 * C₂ * M ^ 3 * (E * Xs) := by ring
  -- T3
  have hrM : s ≤ r * M := by linarith [mul_le_mul_of_nonneg_right hr hM0]
  have T3 : 2 * η * (C₃ * Real.exp (-(2/3) * a ^ 3 - r * M))
      ≤ 2 * C₀ * 3 ^ K₀ * C₃ * P ^ 2 * (E * Xs) := by
    have hex : e23 * Real.exp (-(2/3) * a ^ 3 - r * M) ≤ E * Xs := by
      rw [he23, ← Real.exp_add]
      apply hEX
      linarith
    have hc0 : 0 ≤ C₃ * Real.exp (-(2/3) * a ^ 3 - r * M) := mul_nonneg hC₃ (Real.exp_pos _).le
    calc 2 * η * (C₃ * Real.exp (-(2/3) * a ^ 3 - r * M))
        ≤ 2 * ηb * (C₃ * Real.exp (-(2/3) * a ^ 3 - r * M)) := by
          apply mul_le_mul_of_nonneg_right _ hc0
          linarith
      _ = 2 * C₀ * 3 ^ K₀ * C₃ * P ^ 2 * (e23 * Real.exp (-(2/3) * a ^ 3 - r * M)) := by
          rw [hηb]; ring
      _ ≤ 2 * C₀ * 3 ^ K₀ * C₃ * P ^ 2 * (E * Xs) :=
          mul_le_mul_of_nonneg_left hex (mul_nonneg (mul_nonneg (mul_nonneg
            (mul_nonneg (by norm_num) hC₀) h3K) hC₃) (sq_nonneg _))
  -- T4
  have T4 : (C₃ * Real.exp (-(2/3) * a ^ 3 - r * M)) ^ 2 / 2 ≤ C₃ ^ 2 / 2 * (E * Xs) := by
    have hex : Real.exp (-(2/3) * a ^ 3 - r * M) ^ 2 ≤ E * Xs := by
      rw [sq, ← Real.exp_add]
      apply hEX
      linarith
    calc (C₃ * Real.exp (-(2/3) * a ^ 3 - r * M)) ^ 2 / 2
        = C₃ ^ 2 / 2 * Real.exp (-(2/3) * a ^ 3 - r * M) ^ 2 := by ring
      _ ≤ C₃ ^ 2 / 2 * (E * Xs) := mul_le_mul_of_nonneg_left hex (by positivity)
  -- T5
  have T5 : η ^ 3 / (1 - η) ≤ 2 * C₀ ^ 3 * (3 ^ K₀) ^ 3 * P ^ 6 * (E * Xs) := by
    have hη3 : η ^ 3 / (1 - η) ≤ 2 * η ^ 3 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith only [pow_nonneg hη0 3, hη]
    have hb3 : η ^ 3 ≤ ηb ^ 3 := pow_le_pow_left₀ hη0 hηle 3
    have hex : e23 ^ 3 ≤ E * Xs := by
      have e : e23 ^ 3 = Real.exp (-(2/3) * a ^ 3 + (-(2/3) * a ^ 3 + -(2/3) * a ^ 3)) := by
        rw [he23, Real.exp_add, Real.exp_add]; ring
      rw [e]
      apply hEX
      linarith
    calc η ^ 3 / (1 - η) ≤ 2 * ηb ^ 3 := by linarith
      _ = 2 * C₀ ^ 3 * (3 ^ K₀) ^ 3 * P ^ 6 * e23 ^ 3 := by rw [hηb]; ring
      _ ≤ 2 * C₀ ^ 3 * (3 ^ K₀) ^ 3 * P ^ 6 * (E * Xs) :=
          mul_le_mul_of_nonneg_left hex (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
            (pow_nonneg hC₀ 3)) (pow_nonneg h3K 3)) (pow_nonneg hP0 6))
  have hsum : (C₁ + 771 * C₂ * M ^ 3 + 2 * C₀ * 3 ^ K₀ * C₃ * P ^ 2 + C₃ ^ 2 / 2
        + 2 * C₀ ^ 3 * (3 ^ K₀) ^ 3 * P ^ 6) * (E * Xs)
      = C₁ * (E * Xs) + 771 * C₂ * M ^ 3 * (E * Xs) + 2 * C₀ * 3 ^ K₀ * C₃ * P ^ 2 * (E * Xs)
        + C₃ ^ 2 / 2 * (E * Xs) + 2 * C₀ ^ 3 * (3 ^ K₀) ^ 3 * P ^ 6 * (E * Xs) := by ring
  rw [hsum]
  linarith [T1, T2, T3, T4, T5]

/-! ### The certificate -/

/-- **The sign certificate, association shape.** For `0 < χ < 1` and
`ε > 0` there is `M₀` such that for `M ≥ M₀`, `1 ≤ r ≤ χ√(2M)` (`a = √(2M)`) and any
`MemLp`/trace-class proof terms, `π₁ = 1 − det₁(I − K̃₁)` satisfies `ρ(M)/2 ≤ π₁` and
`(1 − ε) π₁² ≤ X := 1 − d₁ − d₂ + d∪`. -/
theorem twoInt_joint_ge_assoc_eventually {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℝ, ∀ {M r : ℝ}, M₀ ≤ M → 1 ≤ r → r ≤ χ * Real.sqrt (2*M) →
      ∀ (hk1 : MemLp (k1KerT (Real.sqrt (2*M)) M) 2 (volume.prod volume))
        (hk2 : MemLp (k2KerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume))
        (hkcup : MemLp (kcupKerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume))
        (hk1t : IsTraceClass (kernelOperator hk1)) (hk2t : IsTraceClass (kernelOperator hk2))
        (hkcupt : IsTraceClass (kernelOperator hkcup)),
        AiryConj.rhoM M / 2 ≤ 1 - fredholmDetOne (kernelOperator hk1) hk1t 1 ∧
        (1 - ε) * (1 - fredholmDetOne (kernelOperator hk1) hk1t 1) ^ 2
          ≤ 1 - fredholmDetOne (kernelOperator hk1) hk1t 1
              - fredholmDetOne (kernelOperator hk2) hk2t 1
              + fredholmDetOne (kernelOperator hkcup) hkcupt 1 := by
  obtain ⟨C₁, C₀, K₀, Mp, hC₁, hC₀, hK₀, HP⟩ := twoInt_joint_ge_plemelj_eventually hχ0 hχ1
  obtain ⟨C₂, M₂, hC₂, H2⟩ := trace_k1k2_le_discharged hχ0 hχ1
  obtain ⟨C₃, M₃, hC₃, H3⟩ := hsNorm_crKerT_le_discharged hχ0 hχ1
  obtain ⟨Mη, hMη⟩ := etaMr_tendsto_zero_uniform hC₀ K₀ hK₀ hχ0 hχ1 (1/2) (by norm_num)
  obtain ⟨Mπ, hMπ⟩ := exists_piOne_ge_half_rho
  obtain ⟨Ma, hMa⟩ := exists_admissible_M₀ hχ0 hχ1
  set B := C₁ + 771 * C₂ + 2 * C₀ * 3 ^ K₀ * C₃ + C₃ ^ 2 / 2
    + 2 * C₀ ^ 3 * (3 ^ K₀) ^ 3 with hB
  have hT : Tendsto (fun M : ℝ => B * (((M ^ (0:ℝ) * Real.exp (-Real.sqrt M)
      + M ^ ((3:ℕ):ℝ) * Real.exp (-Real.sqrt M))
      + M ^ (K₀ * ((2:ℕ):ℝ)) * Real.exp (-Real.sqrt M))
      + M ^ (K₀ * ((6:ℕ):ℝ)) * Real.exp (-Real.sqrt M))) atTop (𝓝 0) := by
    have h := ((((tendsto_rpow_mul_exp_neg_sqrt 0).add
      (tendsto_rpow_mul_exp_neg_sqrt ((3:ℕ):ℝ))).add
      (tendsto_rpow_mul_exp_neg_sqrt (K₀ * ((2:ℕ):ℝ)))).add
      (tendsto_rpow_mul_exp_neg_sqrt (K₀ * ((6:ℕ):ℝ)))).const_mul B
    rw [add_zero, add_zero, add_zero, mul_zero] at h
    exact h
  have hε' : 0 < ε * AiryConj.Cstar ^ 2 / 4 :=
    div_pos (mul_pos hε (pow_pos AiryConj.Cstar_pos 2)) (by norm_num)
  obtain ⟨Mt, hMt⟩ := eventually_atTop.mp (hT.eventually (Iic_mem_nhds hε'))
  refine ⟨max (max (max Mp M₂) (max M₃ Mη)) (max (max Mπ Ma) (max Mt 10000)), ?_⟩
  intro M r hM hr hrM hk1 hk2 hkcup hk1t hk2t hkcupt
  have hMp : Mp ≤ M := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hM
  have hM2 : M₂ ≤ M := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hM
  have hM3 : M₃ ≤ M := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_left _ _)) hM
  have hMη' : Mη ≤ M := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_left _ _)) hM
  have hMπ' : Mπ ≤ M := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hM
  have hMa' : Ma ≤ M := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _)) hM
  have hMt' : Mt ≤ M := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hM
  have hM4 : (10000:ℝ) ≤ M := le_trans (le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) (le_max_right _ _)) hM
  obtain ⟨hadr, ha2, hM1⟩ := hMa M r hMa' hr hrM
  have hMpos : (0:ℝ) < M := by linarith
  have hM0 : (0:ℝ) ≤ M := hMpos.le
  have hr0 : (0:ℝ) < r := by linarith
  have hcr := memLp_crKerT hr0 hMpos hadr
  have hX := HP hMp hr hrM hk1 hk2 hkcup hcr hk1t hk2t hkcupt (H2 hM2 hr hrM hk1 hk2)
    (H3 hM3 hr hrM hcr)
  -- η ≤ 1/2
  have hη12 : C₀ * M ^ K₀ * (1+r) ^ (K₀:ℝ) * Real.exp (-(2/3) * (Real.sqrt (2*M)) ^ 3)
      ≤ 1/2 := by
    have h := hMη M r hMη' hr hrM
    rwa [← rpow_sqrt_two_mul_cube hM0] at h
  have hra : r ≤ Real.sqrt (2*M) := by linarith
  have hΔ := plemeljMargin_le hM4 hr hra hC₀.le hK₀ hC₁.le hC₂.le hC₃.le hη12
  -- π₁ ≥ ρ/2
  obtain ⟨_, hπ⟩ := hMπ M hMπ'
  rw [← fredholmDetOne_k1KerT_eq_detOneAiryTilde hMpos ha2 hk1 hk1t] at hπ
  refine ⟨hπ, ?_⟩
  set d := fredholmDetOne (kernelOperator hk1) hk1t 1 with hd
  have hρ : 0 < AiryConj.rhoM M := AiryConj.rhoM_pos hMpos
  have hd0 : 0 ≤ d := by
    rw [hd, fredholmDetOne_one_eq_exp_neg_plemeljTau]
    exact (Real.exp_pos _).le
  have hd1 : d ≤ 1 := by linarith
  -- the eventual smallness at this `M`
  have hsmall := hMt M hMt'
  have hρ2 := rhoM_sq_eq hM0
  set Xs := Real.exp (-Real.sqrt M) with hXs
  set E := Real.exp (-(4/3) * Real.sqrt (2*M) ^ 3) with hE
  set P := M ^ K₀ with hP
  have hP2 : M ^ (K₀ * ((2:ℕ):ℝ)) = P ^ 2 := by
    rw [Real.rpow_mul hM0, Real.rpow_natCast]
  have hP6 : M ^ (K₀ * ((6:ℕ):ℝ)) = P ^ 6 := by
    rw [Real.rpow_mul hM0, Real.rpow_natCast]
  rw [Real.rpow_zero, Real.rpow_natCast, hP2, hP6] at hsmall
  have hXs0 : 0 ≤ Xs := (Real.exp_pos _).le
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hP0 : 0 ≤ P := Real.rpow_nonneg hM0 _
  have h3K : 0 ≤ (3:ℝ) ^ K₀ := Real.rpow_nonneg (by norm_num) _
  set c1 := C₁
  set c2 := 771 * C₂
  set c3 := 2 * C₀ * 3 ^ K₀ * C₃
  set c4 := C₃ ^ 2 / 2
  set c5 := 2 * C₀ ^ 3 * (3 ^ K₀) ^ 3
  have hc1 : 0 ≤ c1 := hC₁.le
  have hc2 : 0 ≤ c2 := mul_nonneg (by norm_num) hC₂.le
  have hc3 : 0 ≤ c3 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀.le) h3K) hC₃.le
  have hc4 : 0 ≤ c4 := div_nonneg (sq_nonneg _) (by norm_num)
  have hc5 : 0 ≤ c5 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC₀.le 3))
    (pow_nonneg h3K 3)
  have hcoef : (c1 + c2 * M ^ 3 + c3 * P ^ 2 + c4 + c5 * P ^ 6) * Xs
      ≤ B * (((1 * Xs + M ^ 3 * Xs) + P ^ 2 * Xs) + P ^ 6 * Xs) := by
    have hm3 : 0 ≤ M ^ 3 * Xs := mul_nonneg (pow_nonneg hM0 3) hXs0
    have hp2 : 0 ≤ P ^ 2 * Xs := mul_nonneg (pow_nonneg hP0 2) hXs0
    have hp6 : 0 ≤ P ^ 6 * Xs := mul_nonneg (pow_nonneg hP0 6) hXs0
    have hB' : B = c1 + c2 + c3 + c4 + c5 := by rw [hB]
    rw [hB']
    linarith [mul_nonneg hc2 hXs0, mul_nonneg hc3 hXs0, mul_nonneg hc5 hXs0,
      mul_nonneg hc1 hm3, mul_nonneg hc3 hm3, mul_nonneg hc4 hm3, mul_nonneg hc5 hm3,
      mul_nonneg hc1 hp2, mul_nonneg hc2 hp2, mul_nonneg hc4 hp2, mul_nonneg hc5 hp2,
      mul_nonneg hc1 hp6, mul_nonneg hc2 hp6, mul_nonneg hc3 hp6, mul_nonneg hc4 hp6]
  have hΔ' : (c1 + c2 * M ^ 3 + c3 * P ^ 2 + c4 + c5 * P ^ 6) * (E * Xs)
      ≤ ε * AiryConj.Cstar ^ 2 / 4 * E := by
    have := mul_le_mul_of_nonneg_right (hcoef.trans hsmall) hE0
    calc (c1 + c2 * M ^ 3 + c3 * P ^ 2 + c4 + c5 * P ^ 6) * (E * Xs)
        = (c1 + c2 * M ^ 3 + c3 * P ^ 2 + c4 + c5 * P ^ 6) * Xs * E := by ring
      _ ≤ ε * AiryConj.Cstar ^ 2 / 4 * E := this
  have hsq : 1 ≤ M ^ (1/2 : ℝ) := Real.one_le_rpow hM1 (by norm_num)
  have hρπ : AiryConj.rhoM M ^ 2 / 4 ≤ (1 - d) ^ 2 := by
    have h := pow_le_pow_left₀ (div_nonneg hρ.le (by norm_num : (0:ℝ) ≤ 2)) hπ 2
    linarith [h, show (AiryConj.rhoM M / 2) ^ 2 = AiryConj.rhoM M ^ 2 / 4 by ring]
  have hfin : ε * AiryConj.Cstar ^ 2 / 4 * E ≤ ε * (1 - d) ^ 2 := by
    have hC2E : 0 ≤ AiryConj.Cstar ^ 2 * E := mul_nonneg (sq_nonneg _) hE0
    have h0 : AiryConj.Cstar ^ 2 * E * 1 ≤ AiryConj.Cstar ^ 2 * E * M ^ (1/2 : ℝ) :=
      mul_le_mul_of_nonneg_left hsq hC2E
    have h1 : AiryConj.Cstar ^ 2 * E ≤ AiryConj.rhoM M ^ 2 := by
      rw [hρ2]; linarith
    have h2 : AiryConj.Cstar ^ 2 * E / 4 ≤ (1 - d) ^ 2 := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hε.le
    linarith
  have hΔfin := (hΔ.trans hΔ').trans hfin
  exact (joint_ge_assoc_of_plemelj hX hd0 hd1 hε.le hΔfin)

/-- **The sign certificate.** For `0 < χ < 1` there is `M₀` such that for
`M ≥ M₀`, `1 ≤ r ≤ χ√(2M)` and any `MemLp`/trace-class proof terms,
`0 < X = 1 − det₁(I − K̃₁) − det₁(I − K̃₂) + det₁(I − K̃∪)` (indeed
`X ≥ π₁²/2 ≥ ρ(M)²/8`). -/
theorem twoInt_joint_pos_eventually {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ M₀ : ℝ, ∀ {M r : ℝ}, M₀ ≤ M → 1 ≤ r → r ≤ χ * Real.sqrt (2*M) →
      ∀ (hk1 : MemLp (k1KerT (Real.sqrt (2*M)) M) 2 (volume.prod volume))
        (hk2 : MemLp (k2KerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume))
        (hkcup : MemLp (kcupKerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume))
        (hk1t : IsTraceClass (kernelOperator hk1)) (hk2t : IsTraceClass (kernelOperator hk2))
        (hkcupt : IsTraceClass (kernelOperator hkcup)),
        0 < 1 - fredholmDetOne (kernelOperator hk1) hk1t 1
              - fredholmDetOne (kernelOperator hk2) hk2t 1
              + fredholmDetOne (kernelOperator hkcup) hkcupt 1 := by
  obtain ⟨M₀, H⟩ := twoInt_joint_ge_assoc_eventually hχ0 hχ1 (by norm_num : (0:ℝ) < 1/2)
  obtain ⟨Ma, hMa⟩ := exists_admissible_M₀ hχ0 hχ1
  refine ⟨max M₀ Ma, ?_⟩
  intro M r hM hr hrM hk1 hk2 hkcup hk1t hk2t hkcupt
  obtain ⟨hπ, hX⟩ := H (le_trans (le_max_left _ _) hM) hr hrM hk1 hk2 hkcup hk1t hk2t hkcupt
  obtain ⟨_, _, hM1⟩ := hMa M r (le_trans (le_max_right _ _) hM) hr hrM
  have hρ : 0 < AiryConj.rhoM M := AiryConj.rhoM_pos (by linarith)
  have hπ0 : 0 < 1 - fredholmDetOne (kernelOperator hk1) hk1t 1 := by linarith
  have := pow_pos hπ0 2
  linarith

end AiryTwoInt
