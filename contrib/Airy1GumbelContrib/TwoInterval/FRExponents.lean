/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.AiryKernel.GaussianSaddle
import Airy1GumbelContrib.AiryKernel.ConjugateV
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# FR-sector exponent calculus

Part of the two-interval layer (`TwoInterval/`) of the Airy1–Gumbel contrib library: the pure
exponent analysis of the FR sector of the two-interval trace, in the trace step of the paper's
separated-block estimate.  This module contains the exponent calculus
(items C0–C8 below) and the pure-calculus inner-form bounds (B2, B3, B5), with **no trace
plumbing** — the kernels, exact inner evaluations, and piece assembly are in
`SectorFR.lean`, which imports this module.  The labels B2–B5 and C0–C8 index the sections
of this module.

## Correspondence with the paper

* The paper's bound on `J`: `J(α, β) ≤ C S⁻¹ᐟ² e^{−α²/(4L) − β²/4}` — `frI1_Jbound` (B2).
* The `K(α, γ)` analog of the paper's Gaussian convolution lemma — `heatKernel_conv_cdf_Ioi`
  (B3, a reflection corollary of the proved `AiryConj.heatKernel_conv_cdf`).
* The paper's bound on `K` and the γ-integration —
  `frI2_Kbound`, `frI2_gamma_int_le` (B5).
* `H₁(α, β)` on `D₊ = {α, β ≥ 0, 2M + α − β + S² ≥ 0}` —
  `h1Exp`, `h1Dom` (C1).
* The `d`-split lower bounds — `h1Exp_ge_quadratic_of_d_nonneg` (C2),
  `h1Exp_ge_quadratic_of_d_neg` (C3), and the `D₊` Gaussian mass
  `frI1Plus_exp_int_le` (C4).
* The negative-Airy `G₁` package — `g1Exp`, `g1Exp_deriv_beta_ge`,
  `g1Exp_boundary_eq`, `g1Exp_boundary_ge_E0`, `g1Exp_quadratic_beta`,
  `frI1Minus_E0_ge`, `frI1Minus_int_beta_le`,
  `frI1Minus_int_alpha_le` (C6).
* The `I₂⁻` package — `g2Minus`, `g2Minus_deriv_ge`, `g2Minus_boundary_eq`,
  `frI2Minus_E20_ge`, `g2Minus_ge_linear` (C7).
* The exact decomposition `H̃₂ = F(δ) + v²/2` —
  `h2Tilde`, `h2Tilde_eq_saddleF_add`, `h2Tilde_ge` (C8).
* The absorption `J_M(r) = O_χ(a³)` — `saddleJ_le_rpow`.
* The Airy glue `|Ai(u)| ≤ C e^{−(2/3)u^{3/2}}` for `u ≥ 0` —
  `airyAiReal_abs_le_exp32` (C0).

Throughout `L = r+1`, `S = r+2`, `a² = 2M` is inlined, and `r` is a real
parameter (the paper's integer restriction is unnecessary).

## The `D₊` Gaussian mass by an elementary route

Where the paper uses a Hessian/constrained-minimizer/Taylor argument
(proving `H₁(p) ≥ J + |p − p₀|²/(4L)` and paying `∫ e^{−|v|²/4L} dv = 4πL`), the Lean proof
uses an elementary bound via the `d`-split that the paper
itself uses, keeping one more term of slack:

* on `d := α − β ≥ 0` (parametrize `t := β`): `(d+t)²/(4L) ≥ d²/(4L)` and the
  rest `R(d) = S(2M+d) + (2/3)S³ + (2/3)(2M+d+S²)^{3/2}` is increasing
  (`R'(d) = S + √(2M+d+S²) > 0`) with `R(0) = F(0) ≥ J`
  (`saddleF_ge` at `δ = 0`), giving `H₁(d+t, t) ≥ J + d²/(4L) + t²/4` (C2);
* on `d < 0` (parametrize `t := α`, `δ := (β−α)/2 ∈ (0, δmax]`):
  `(t+2δ)²/4 ≥ δ²` and `R(−2δ) = F(δ) − δ²/2` (pure algebra), so `saddleF_ge`
  gives `H₁(t, t+2δ) ≥ J + (δ−δ*)²/2 + t²/(4L)` (C3).

Both dominating integrands are nonnegative products, so the region integrals are
pure Tonelli with two sequential 1D affine substitutions, evaluating to
`O(√L)·e^{−J}` (C4).  The Hessian bound `∇²H₁ ≥ (2L)⁻¹I` is weaker than the true
curvature in the β-direction (`∇²H₁ ≈ diag((2L)⁻¹, ½)` near the minimizer, so the
true local Gaussian mass is `O(√L)`, while the comparison yields `4πL`).  The resulting
bound `Ce^{−J}` implies the paper's FR-sector bound `C(1+r)^{1/2}e^{−J}`
(`(r+1)^{1/2}` here vs `(1+r)^{1/2}` there).

## Further notes

* **Inherited side hypothesis.**  Every use of the proved
  `AiryConj.saddleF_ge` carries `2 ≤ saddleR M r` (the bound fails at
  `M = r = 1`).  C2, C3, C4, C8 thread it explicitly;
  `two_le_saddleR` discharges it from `2 ≤ M`, and the headline's `M₀` absorbs it.
* **Explicit constants.**
  `∂_βG₁ ≥ (2M+3)/2` for ALL `M > 0`, `r ≥ 1` (the paper states `≥ a²/4`
  "for all sufficiently large `a`"); `G'_{2,−} ≥ M/2 = a²/4`
  for `M ≥ 3`.  Only the `E₀ ≥ c_χa⁴`-type bounds genuinely need
  largeness (`M₀(χ)`); χ-admissibility (`r ≤ χ√(2M)`, `0 < χ < 1`) appears only
  in `frI1Minus_E0_ge`, `frI2Minus_E20_ge`, `saddleJ_le_rpow`.
* **Φ-form wrapper.**  The Gaussian tail bound `Φ(−t) ≤ ½e^{−t²/2}` is the
  proved `AiryConj.gaussianTail_chernoff` up to the `√(2π)` division
  (`√(π/2)/√(2π) = ½`); used inline in B2/B5.
* Real powers are `Real.rpow` throughout: `x^(3/2 : ℝ)` (never the ℕ-division
  literal).  Constants are existential (`∃ C, 0 < C ∧ …`); no explicit values
  are chased.
-/

namespace AiryTwoInt

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal

open AiryConj

/-! ### C0: the positive-Airy exponential bound -/

/-- **C0**: the positive-half-line Airy bound in the form
used throughout the FR analysis, `|Ai(u)| ≤ C e^{−(2/3)u^{3/2}}` for `0 ≤ u`.
Glue of the proved pieces: on `[1, ∞)` use `airyAiReal_le` (with `u^{−1/4} ≤ 1`)
and positivity `airyAiReal_pos_of_nonneg`; on `[0, 1]` use the global bound
`airyAiReal_abs_le` with `e^{−(2/3)u^{3/2}} ≥ e^{−2/3}`. -/
theorem airyAiReal_abs_le_exp32 :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : ℝ}, 0 ≤ u →
      |airyAiReal u| ≤ C * Real.exp (-(2/3)*u^(3/2 : ℝ)) := by
  obtain ⟨C₁, hC₁⟩ := airyAiReal_le
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le
  refine ⟨|C₀| * Real.exp (2/3 : ℝ) + |C₁| + 1, by positivity, ?_⟩
  intro u hu
  rcases le_or_gt 1 u with hu1 | hu1
  · -- the decay region `1 ≤ u`
    have hpos : 0 < airyAiReal u := airyAiReal_pos_of_nonneg (zero_le_one.trans hu1)
    rw [abs_of_pos hpos]
    have h1 := hC₁ u hu1
    rw [show -(2/3 * u^(3/2 : ℝ)) = -(2/3 : ℝ) * u^(3/2 : ℝ) by ring] at h1
    have hr1 : (0:ℝ) ≤ u^(-1/4 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hu1) _
    have hr2 : u^(-1/4 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
    have hstep : C₁ * u^(-1/4 : ℝ) ≤ |C₁| := by
      calc C₁ * u^(-1/4 : ℝ) ≤ |C₁| * u^(-1/4 : ℝ) :=
            mul_le_mul_of_nonneg_right (le_abs_self C₁) hr1
        _ ≤ |C₁| * 1 := mul_le_mul_of_nonneg_left hr2 (abs_nonneg C₁)
        _ = |C₁| := mul_one _
    calc airyAiReal u ≤ C₁ * u^(-1/4 : ℝ) * Real.exp (-(2/3 : ℝ) * u^(3/2 : ℝ)) := h1
      _ ≤ |C₁| * Real.exp (-(2/3 : ℝ) * u^(3/2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le
      _ ≤ (|C₀| * Real.exp (2/3 : ℝ) + |C₁| + 1) * Real.exp (-(2/3 : ℝ) * u^(3/2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have hnn : (0:ℝ) ≤ |C₀| * Real.exp (2/3 : ℝ) :=
            mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
          linarith
  · -- the compact region `0 ≤ u ≤ 1`
    have hle : |airyAiReal u| ≤ C₀ := hC₀ u
    have hpow : u^(3/2 : ℝ) ≤ (1:ℝ)^(3/2 : ℝ) :=
      Real.rpow_le_rpow hu hu1.le (by norm_num)
    rw [Real.one_rpow] at hpow
    have hexp : Real.exp (-(2/3 : ℝ) * 1) ≤ Real.exp (-(2/3 : ℝ) * u^(3/2 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have : -(2/3 : ℝ) * u^(3/2 : ℝ) ≥ -(2/3 : ℝ) * 1 := by nlinarith [hpow]
      linarith
    have hC0nn : (0:ℝ) ≤ |C₀| * Real.exp (2/3 : ℝ) := by positivity
    calc |airyAiReal u| ≤ C₀ := hle
      _ ≤ |C₀| := le_abs_self _
      _ = |C₀| * Real.exp (2/3 : ℝ) * Real.exp (-(2/3 : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add, show (2/3 : ℝ) + -(2/3) = 0 by norm_num,
            Real.exp_zero, mul_one]
      _ ≤ |C₀| * Real.exp (2/3 : ℝ) * Real.exp (-(2/3 : ℝ) * u^(3/2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hC0nn
          convert hexp using 2
          norm_num
      _ ≤ (|C₀| * Real.exp (2/3 : ℝ) + |C₁| + 1) * Real.exp (-(2/3 : ℝ) * u^(3/2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          linarith [abs_nonneg C₁]

/-! ### C1: the `H₁` exponent and its domain -/

/-- **C1**: the `I₁⁺` dominating exponent
`H₁(α, β) = α²/(4L) + β²/4 + S(2M+α−β) + (2/3)S³ + (2/3)(2M+α−β+S²)^{3/2}`
with `L = r+1`, `S = r+2`, `a² = 2M` inlined (the `saddleF` convention). -/
noncomputable def h1Exp (M r : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1^2/(4*(r+1)) + p.2^2/4 + (r+2)*(2*M + p.1 - p.2) + (2/3)*(r+2)^3
    + (2/3)*(2*M + p.1 - p.2 + (r+2)^2)^(3/2 : ℝ)

/-- **C1**: the positive-Airy quadrant domain
`D₊ = {α ≥ 0, β ≥ 0, 2M+α−β+S² ≥ 0}`. -/
def h1Dom (M r : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 0 ≤ 2*M + p.1 - p.2 + (r+2)^2}

/-- `h1Exp M r` is continuous on all of `ℝ²` (the `rpow` with exponent `3/2 > 0`
is continuous everywhere — the `continuous_saddleG` trick). -/
theorem continuous_h1Exp (M r : ℝ) : Continuous (h1Exp M r) := by
  have hrpow : Continuous fun p : ℝ × ℝ => (2*M + p.1 - p.2 + (r+2)^2)^(3/2 : ℝ) :=
    continuous_iff_continuousAt.mpr fun p =>
      (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num : (0:ℝ) ≤ 3/2))).comp
        (by fun_prop : ContinuousAt (fun p : ℝ × ℝ => 2*M + p.1 - p.2 + (r+2)^2) p)
  have h1 : Continuous fun p : ℝ × ℝ => p.1^2/(4*(r+1)) :=
    (continuous_fst.pow 2).div_const _
  have h2 : Continuous fun p : ℝ × ℝ => p.2^2/4 := (continuous_snd.pow 2).div_const _
  have h3 : Continuous fun p : ℝ × ℝ => (r+2)*(2*M + p.1 - p.2) :=
    continuous_const.mul ((continuous_const.add continuous_fst).sub continuous_snd)
  have h4 : Continuous fun _ : ℝ × ℝ => (2/3)*(r+2)^3 := continuous_const
  have h5 : Continuous fun p : ℝ × ℝ => (2/3)*(2*M + p.1 - p.2 + (r+2)^2)^(3/2 : ℝ) :=
    continuous_const.mul hrpow
  exact ((((h1.add h2).add h3).add h4).add h5)

/-- `h1Exp M r` is measurable. -/
theorem measurable_h1Exp (M r : ℝ) : Measurable (h1Exp M r) :=
  (continuous_h1Exp M r).measurable

/-- `h1Exp M r` is continuous on `h1Dom M r` (in fact on all of `ℝ²`). -/
theorem continuousOn_h1Exp (M r : ℝ) : ContinuousOn (h1Exp M r) (h1Dom M r) :=
  (continuous_h1Exp M r).continuousOn

/-- `h1Dom M r` is closed, hence measurable. -/
theorem measurableSet_h1Dom (M r : ℝ) : MeasurableSet (h1Dom M r) := by
  have h : h1Dom M r = (Set.Ici (0:ℝ) ×ˢ Set.Ici (0:ℝ)) ∩
      ((fun p : ℝ × ℝ => 2*M + p.1 - p.2 + (r+2)^2) ⁻¹' Set.Ici 0) := by
    ext p
    exact ⟨fun hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩, fun hp => ⟨hp.1.1, hp.1.2, hp.2⟩⟩
  rw [h]
  exact (measurableSet_Ici.prod measurableSet_Ici).inter
    (measurableSet_Ici.preimage (by fun_prop :
      Measurable fun p : ℝ × ℝ => 2*M + p.1 - p.2 + (r+2)^2))

/-- **Discharge of the side hypothesis**: the `saddleF_ge` side hypothesis
`2 ≤ saddleR M r` follows from `2 ≤ M` (with `1 ≤ r`): then `2M + r² ≥ 5 > 4`,
so `√(2M+r²) ≥ 2`.  The positive-piece lemmas C2/C3/C4/C8 carry `hR`
explicitly; callers at `2 ≤ M` use this to discharge them. -/
theorem two_le_saddleR (hM : 2 ≤ M) (hr : 1 ≤ r) : 2 ≤ saddleR M r := by
  have hr2 : (1:ℝ) ≤ r^2 := by nlinarith [sq_nonneg (r - 1), hr]
  unfold saddleR
  apply Real.le_sqrt_of_sq_le
  nlinarith [hM, hr2]

/-! ### C2/C3: the sharp `d`-split quadratic lower bounds -/

/-- The `d`-dependent part of `H₁` after dropping the quadratic terms (the
`R(d)` of the `d`-split route): `R(d) = S(2M+d) + (2/3)S³ + (2/3)(2M+d+S²)^{3/2}`. -/
noncomputable def h1Rest (M r d : ℝ) : ℝ :=
  (r+2)*(2*M + d) + (2/3)*(r+2)^3 + (2/3)*(2*M + d + (r+2)^2)^(3/2 : ℝ)

/-- `R(0) = F(0)` (: the `d ≥ 0` minimum sits at `d = 0` with
value `F(0)`). -/
theorem h1Rest_zero (M r : ℝ) : h1Rest M r 0 = saddleF M r 0 := by
  have harg : 2*M + 0 + (r+2)^2 = 2*M - 2*0 + (r+2)^2 := by ring
  show (r+2)*(2*M + 0) + (2/3)*(r+2)^3 + (2/3)*(2*M + 0 + (r+2)^2)^(3/2 : ℝ)
    = 0^2/2 + 2*(r+2)*(M-0) + (2/3)*(r+2)^3 + (2/3)*(2*M - 2*0 + (r+2)^2)^(3/2 : ℝ)
  rw [harg]
  ring

/-- The derivative of `h1Rest M r` at a point with positive radicand:
`R'(d) = S + √(2M+d+S²)`. -/
theorem h1Rest_hasDeriv (M r d : ℝ) (hd : 0 < 2*M + d + (r+2)^2) :
    HasDerivAt (h1Rest M r) ((r+2) + Real.sqrt (2*M + d + (r+2)^2)) d := by
  unfold h1Rest
  have t1 : HasDerivAt (fun d : ℝ => (r+2)*(2*M + d)) (r+2) d := by
    simpa using (((hasDerivAt_const d (2*M)).add (hasDerivAt_id' d)).const_mul (r+2))
  have t4 : HasDerivAt (fun d : ℝ => (2/3)*(2*M + d + (r+2)^2)^(3/2 : ℝ))
      (Real.sqrt (2*M + d + (r+2)^2)) d := by
    have hin : HasDerivAt (fun d : ℝ => 2*M + d + (r+2)^2) 1 d := by
      simpa using (((hasDerivAt_const d (2*M)).add (hasDerivAt_id' d)).add_const ((r+2)^2))
    have hpow : HasDerivAt (fun x : ℝ => x^(3/2 : ℝ))
        ((3/2) * (2*M + d + (r+2)^2)^(1/2 : ℝ)) (2*M + d + (r+2)^2) := by
      have h2 := Real.hasDerivAt_rpow_const (x := 2*M + d + (r+2)^2) (p := (3:ℝ)/2)
        (Or.inl hd.ne')
      rw [show (3/2 : ℝ) - 1 = 1/2 by norm_num] at h2
      exact h2
    have h3 := hpow.comp d hin
    have h4 := h3.const_mul (2/3)
    have hval : (2/3 : ℝ) * ((3/2) * (2*M + d + (r+2)^2)^(1/2 : ℝ) * 1)
        = Real.sqrt (2*M + d + (r+2)^2) := by
      rw [Real.sqrt_eq_rpow]
      ring
    rwa [hval] at h4
  have htot := (t1.add (hasDerivAt_const d ((2/3)*(r+2)^3))).add t4
  have hval : ((r+2) + 0) + Real.sqrt (2*M + d + (r+2)^2)
      = (r+2) + Real.sqrt (2*M + d + (r+2)^2) := by ring
  rwa [hval] at htot

/-- `h1Rest M r` is continuous (the `rpow`-at-`3/2 > 0` trick). -/
theorem continuous_h1Rest (M r : ℝ) : Continuous (h1Rest M r) := by
  have hrpow : Continuous fun d : ℝ => (2*M + d + (r+2)^2)^(3/2 : ℝ) :=
    continuous_iff_continuousAt.mpr fun d =>
      (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num : (0:ℝ) ≤ 3/2))).comp
        (by fun_prop : ContinuousAt (fun d : ℝ => 2*M + d + (r+2)^2) d)
  have h1 : Continuous fun d : ℝ => (r+2)*(2*M + d) :=
    continuous_const.mul (continuous_const.add continuous_id)
  have h2 : Continuous fun _ : ℝ => (2/3)*(r+2)^3 := continuous_const
  have h3 : Continuous fun d : ℝ => (2/3)*(2*M + d + (r+2)^2)^(3/2 : ℝ) :=
    continuous_const.mul hrpow
  exact (h1.add h2).add h3

/-- `R` is increasing on `[0, ∞)` (`R'(d) = S + √(2M+d+S²) > 0`) via `monotoneOn_of_deriv_nonneg` — the `saddleF_ge`
first-derivative pattern. -/
theorem h1Rest_mono_on (hM : 0 < M) (hr : 0 ≤ r) :
    MonotoneOn (h1Rest M r) (Set.Ici 0) := by
  have hpos : ∀ d : ℝ, 0 < d → 0 < 2*M + d + (r+2)^2 := fun d hd => by
    nlinarith [hM, hd, sq_nonneg (r+2)]
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (continuous_h1Rest M r).continuousOn
    ?_ ?_
  · rw [interior_Ici]
    intro d hd
    exact (h1Rest_hasDeriv M r d (hpos d hd)).hasDerivWithinAt.differentiableWithinAt
  · rw [interior_Ici]
    intro d hd
    rw [(h1Rest_hasDeriv M r d (hpos d hd)).deriv]
    have hsqrt : (0:ℝ) ≤ Real.sqrt (2*M + d + (r+2)^2) := Real.sqrt_nonneg _
    linarith

/-- **C2** (the `d ≥ 0` region — sharp form keeping the
`β²/4 = t²/4` slack): for `d, t ≥ 0`,
`H₁(d+t, t) ≥ J_M(r) + d²/(4L) + t²/4`.
Route: `(d+t)²/(4L) ≥ d²/(4L)`; `R(d) ≥ R(0) = F(0) ≥ J_M(r)`
(`h1Rest_mono_on`, `h1Rest_zero`, `saddleF_ge` at `δ = 0`). -/
theorem h1Exp_ge_quadratic_of_d_nonneg (hM : 1 ≤ M) (hr : 1 ≤ r)
    (hR : 2 ≤ saddleR M r) {d t : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t) :
    saddleJ M r + d^2/(4*(r+1)) + t^2/4 ≤ h1Exp M r (d+t, t) := by
  have hL : (0:ℝ) < 4*(r+1) := by linarith [hr]
  have hEq : h1Exp M r (d+t, t) = (d+t)^2/(4*(r+1)) + t^2/4 + h1Rest M r d := by
    have harg : 2*M + (d+t) - t + (r+2)^2 = 2*M + d + (r+2)^2 := by ring
    show (d+t)^2/(4*(r+1)) + t^2/4 + (r+2)*(2*M + (d+t) - t) + (2/3)*(r+2)^3
        + (2/3)*(2*M + (d+t) - t + (r+2)^2)^(3/2 : ℝ)
      = (d+t)^2/(4*(r+1)) + t^2/4 + ((r+2)*(2*M + d) + (2/3)*(r+2)^3
        + (2/3)*(2*M + d + (r+2)^2)^(3/2 : ℝ))
    rw [harg]
    ring
  have hsq : d^2/(4*(r+1)) ≤ (d+t)^2/(4*(r+1)) := by
    have h1 : d^2 ≤ (d+t)^2 := by nlinarith [mul_nonneg hd ht, sq_nonneg t]
    exact div_le_div_of_nonneg_right h1 hL.le
  have hR0 : saddleJ M r ≤ h1Rest M r 0 := by
    have hδmax : (0:ℝ) ≤ (2*M + (r+2)^2)/2 := by
      nlinarith [hM, sq_nonneg (r+2)]
    have hF := saddleF_ge hM hr hR 0 ⟨le_refl 0, hδmax⟩
    have hsq0 : (0:ℝ) ≤ (0 - 2*(r + saddleR M r))^2/2 := by positivity
    linarith [hF, h1Rest_zero M r]
  have hRd : h1Rest M r 0 ≤ h1Rest M r d :=
    h1Rest_mono_on (lt_of_lt_of_le one_pos hM) (le_trans zero_le_one hr)
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hd) hd
  rw [hEq]
  linarith [hsq, hR0, hRd]

/-- **C3** (the `d < 0` region — sharp form keeping the
`α²/(4L) = t²/(4L)` slack): for `t ≥ 0` and `δ ∈ [0, δmax]`,
`H₁(t, t+2δ) ≥ J_M(r) + (δ−δ*)²/2 + t²/(4L)` with `δ* = 2(r+R)`.
Route: `(t+2δ)²/4 ≥ δ²`; `R(−2δ) = F(δ) − δ²/2` (pure algebra); `saddleF_ge`. -/
theorem h1Exp_ge_quadratic_of_d_neg (hM : 1 ≤ M) (hr : 1 ≤ r)
    (hR : 2 ≤ saddleR M r) {t δ : ℝ} (ht : 0 ≤ t)
    (hδ : δ ∈ Set.Icc 0 ((2*M + (r+2)^2)/2)) :
    saddleJ M r + (δ - 2*(r + saddleR M r))^2/2 + t^2/(4*(r+1))
      ≤ h1Exp M r (t, t + 2*δ) := by
  have hL : (0:ℝ) < 4*(r+1) := by linarith [hr]
  have hEq : h1Exp M r (t, t + 2*δ)
      = t^2/(4*(r+1)) + (t + 2*δ)^2/4 + h1Rest M r (-(2*δ)) := by
    have harg : 2*M + t - (t + 2*δ) + (r+2)^2 = 2*M + -(2*δ) + (r+2)^2 := by ring
    show t^2/(4*(r+1)) + (t+2*δ)^2/4 + (r+2)*(2*M + t - (t+2*δ)) + (2/3)*(r+2)^3
        + (2/3)*(2*M + t - (t+2*δ) + (r+2)^2)^(3/2 : ℝ)
      = t^2/(4*(r+1)) + (t+2*δ)^2/4 + ((r+2)*(2*M + -(2*δ)) + (2/3)*(r+2)^3
        + (2/3)*(2*M + -(2*δ) + (r+2)^2)^(3/2 : ℝ))
    rw [harg]
    ring
  have hRest : h1Rest M r (-(2*δ)) = saddleF M r δ - δ^2/2 := by
    have harg : 2*M + -(2*δ) + (r+2)^2 = 2*M - 2*δ + (r+2)^2 := by ring
    show (r+2)*(2*M + -(2*δ)) + (2/3)*(r+2)^3 + (2/3)*(2*M + -(2*δ) + (r+2)^2)^(3/2 : ℝ)
      = δ^2/2 + 2*(r+2)*(M-δ) + (2/3)*(r+2)^3 + (2/3)*(2*M - 2*δ + (r+2)^2)^(3/2 : ℝ) - δ^2/2
    rw [harg]
    ring
  have hsq4 : δ^2 ≤ (t + 2*δ)^2/4 := by
    nlinarith [mul_nonneg ht hδ.1, sq_nonneg t]
  have hF := saddleF_ge hM hr hR δ hδ
  rw [hEq, hRest]
  linarith [hsq4, hF, sq_nonneg δ]

/-! ### C4: the `D₊` Gaussian mass (by the elementary `d`-split route) -/

/-- `∫₀^∞ e^{−x²/(4c)} dx = √(πc)` for `0 < c` (the half-Gaussian mass,
`integral_gaussian_Ioi`). -/
theorem integral_exp_neg_sq_div_four_mul_Ioi (c : ℝ) (hc : 0 < c) :
    ∫ x in Set.Ioi 0, Real.exp (-x^2/(4*c)) = Real.sqrt (Real.pi * c) := by
  have hcong : (fun x : ℝ => Real.exp (-x^2/(4*c)))
      = fun x => Real.exp (-((4*c)⁻¹) * x^2) := by
    funext x
    congr 1
    field_simp [hc.ne']
  rw [hcong, integral_gaussian_Ioi]
  have h1 : Real.pi / (4*c)⁻¹ = 4 * (Real.pi * c) := by field_simp [hc.ne']
  rw [h1]
  have h2 : Real.sqrt (4 * (Real.pi * c)) = 2 * Real.sqrt (Real.pi * c) := by
    rw [show (4:ℝ) * (Real.pi * c) = 2^2 * (Real.pi * c) by ring,
      Real.sqrt_mul (sq_nonneg 2), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [h2]
  ring

/-- On `D₊`, the quadratic dominator bound `H₁(p) ≥ p.1²/(4L) + p.2²/4 − S³/3`
(the radicand is `≥ 0` on `D₊`, so `(2/3)rad^{3/2} ≥ 0` and
`S(2M+α−β) = S·rad − S³ ≥ −S³`).  This drives the integrability of
`exp(−H₁)`; the sharp lower bounds are C2/C3. -/
theorem h1Exp_ge_quadratic_sub (hr : 0 < r) {p : ℝ × ℝ}
    (hp : p ∈ h1Dom M r) :
    p.1^2/(4*(r+1)) + p.2^2/4 - (r+2)^3/3 ≤ h1Exp M r p := by
  obtain ⟨hα, hβ, hrad⟩ := hp
  have hS : (0:ℝ) ≤ r+2 := by linarith
  have h1 : (0:ℝ) ≤ (2/3)*(2*M + p.1 - p.2 + (r+2)^2)^(3/2 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hrad _)
  have h3 : (r+2)*(2*M + p.1 - p.2)
      = (r+2)*(2*M + p.1 - p.2 + (r+2)^2) - (r+2)^3 := by ring
  have h4 : (0:ℝ) ≤ (r+2)*(2*M + p.1 - p.2 + (r+2)^2) := mul_nonneg hS hrad
  show p.1^2/(4*(r+1)) + p.2^2/4 - (r+2)^3/3
    ≤ p.1^2/(4*(r+1)) + p.2^2/4 + (r+2)*(2*M + p.1 - p.2) + (2/3)*(r+2)^3
      + (2/3)*(2*M + p.1 - p.2 + (r+2)^2)^(3/2 : ℝ)
  linarith

/-- **C4 integrability helper**: `exp(−H₁)` is integrable on `D₊ = h1Dom M r`,
dominated by `e^{S³/3} · e^{−α²/(4L)} · e^{−β²/4}`
(`h1Exp_ge_quadratic_sub`; the dominator is a product of 1D Gaussians,
integrable by `Integrable.smul_prod`). -/
theorem integrableOn_exp_neg_h1Exp (hr : 0 < r) :
    IntegrableOn (fun p => Real.exp (-h1Exp M r p)) (h1Dom M r) := by
  have hL : (0:ℝ) < 4*(r+1) := by linarith
  have hGint : Integrable (fun p : ℝ × ℝ => Real.exp ((r+2)^3/3)
      * (Real.exp (-(4*(r+1))⁻¹ * p.1^2) * Real.exp (-(1/4 : ℝ) * p.2^2)))
      (volume.prod volume) := by
    have h1 : Integrable fun α : ℝ =>
        Real.exp ((r+2)^3/3) * Real.exp (-(4*(r+1))⁻¹ * α^2) :=
      ((integrable_exp_neg_mul_sq (inv_pos.mpr hL))).const_mul _
    have h2 : Integrable fun β : ℝ => Real.exp (-(1/4 : ℝ) * β^2) :=
      integrable_exp_neg_mul_sq (by norm_num)
    have h3 := h1.smul_prod h2
    convert h3 using 1
    funext p
    simp only [smul_eq_mul]
    ring
  rw [IntegrableOn]
  apply hGint.integrableOn.mono' (f := fun p => Real.exp (-h1Exp M r p))
  · exact ((Real.continuous_exp.comp (continuous_h1Exp M r).neg).aestronglyMeasurable)
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_h1Dom M r)] with p hp
    have hbound := h1Exp_ge_quadratic_sub hr hp
    have hnn1 : (0:ℝ) ≤ Real.exp (-h1Exp M r p) := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn1]
    have hfact : Real.exp ((r+2)^3/3)
        * (Real.exp (-(4*(r+1))⁻¹ * p.1^2) * Real.exp (-(1/4 : ℝ) * p.2^2))
        = Real.exp ((r+2)^3/3 + (-(p.1^2/(4*(r+1)))) + (-(p.2^2/4))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hfact]
    apply Real.exp_le_exp.mpr
    -- goal: -h1Exp ≤ S³/3 + (-p.1²/(4L)) + (-p.2²/4)
    have : (r+2)^3/3 + -(p.1^2/(4*(r+1))) + -(p.2^2/4)
        = -(p.1^2/(4*(r+1)) + p.2^2/4 - (r+2)^3/3) := by ring
    rw [this]
    exact neg_le_neg hbound

/-- The pointwise Gaussian dominator bound for `exp(−H₁)` on `D₊`
(the exponential form of `h1Exp_ge_quadratic_sub`). -/
theorem exp_neg_h1Exp_le (hr : 0 < r) {p : ℝ × ℝ} (hp : p ∈ h1Dom M r) :
    Real.exp (-h1Exp M r p)
      ≤ Real.exp ((r+2)^3/3) * (Real.exp (-(4*(r+1))⁻¹ * p.1^2)
        * Real.exp (-(1/4 : ℝ) * p.2^2)) := by
  have hL : (0:ℝ) < 4*(r+1) := by linarith
  have hbound := h1Exp_ge_quadratic_sub hr hp
  have hfact : Real.exp ((r+2)^3/3)
      * (Real.exp (-(4*(r+1))⁻¹ * p.1^2) * Real.exp (-(1/4 : ℝ) * p.2^2))
      = Real.exp ((r+2)^3/3 + (-(p.1^2/(4*(r+1)))) + (-(p.2^2/4))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hfact]
  apply Real.exp_le_exp.mpr
  have h : (r+2)^3/3 + -(p.1^2/(4*(r+1))) + -(p.2^2/4)
      = -(p.1^2/(4*(r+1)) + p.2^2/4 - (r+2)^3/3) := by ring
  rw [h]
  exact neg_le_neg hbound

/-- Slice integrability of `exp(−H₁(·, β))` on `Ioi β` for `0 ≤ β` (the `d ≥ 0`
slice): on this slice `(α, β) ∈ D₊`, so `exp_neg_h1Exp_le` dominates. -/
theorem integrableOn_exp_neg_h1Exp_fst_Ioi (hM : 0 ≤ M) (hr : 0 < r) {β : ℝ} (hβ : 0 ≤ β) :
    IntegrableOn (fun α => Real.exp (-h1Exp M r (α, β))) (Set.Ioi β) := by
  have hL : (0:ℝ) < 4*(r+1) := by linarith
  have hdom : Integrable (fun α : ℝ => Real.exp ((r+2)^3/3)
      * (Real.exp (-(4*(r+1))⁻¹ * α^2) * Real.exp (-(1/4 : ℝ) * β^2))) :=
    ((integrable_exp_neg_mul_sq (inv_pos.mpr hL)).mul_const _).const_mul _
  have hcont : Continuous fun α : ℝ => Real.exp (-h1Exp M r (α, β)) :=
    Real.continuous_exp.comp (((continuous_h1Exp M r).comp
      (continuous_id.prodMk continuous_const)).neg)
  rw [IntegrableOn]
  apply (hdom.integrableOn (s := Set.Ioi β)).mono' hcont.aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with α hα
  have hαβ : β < α := hα
  have hp : (α, β) ∈ h1Dom M r := by
    refine ⟨le_trans hβ hαβ.le, hβ, ?_⟩
    show (0:ℝ) ≤ 2*M + α - β + (r+2)^2
    nlinarith [hM, hαβ, hβ, sq_nonneg (r+2)]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact exp_neg_h1Exp_le hr hp

/-- **C4, region `d ≥ 0`** (via the `d`-split route): on
`D₊ ∩ {β ≤ α}`, C2 dominates the integrand by
`e^{−J} e^{−(α−β)²/(4L)} e^{−β²/4}` (Tonelli with the `β`-outer iteration, then
the 1D shift `d = α − β`), whose mass is `e^{−J} · √(πL) · √π`. -/
theorem frI1Plus_exp_int_dge_le (hM : 1 ≤ M) (hr : 1 ≤ r) (hR : 2 ≤ saddleR M r) :
    ∫ p in h1Dom M r ∩ {p : ℝ × ℝ | p.2 ≤ p.1}, Real.exp (-h1Exp M r p)
      ≤ Real.exp (-saddleJ M r) * Real.sqrt (Real.pi * (r+1)) * Real.sqrt Real.pi := by
  have hL : (0:ℝ) < r + 1 := by linarith
  have hL4 : (0:ℝ) < 4*(r+1) := by linarith
  set f : ℝ × ℝ → ℝ := fun p => Real.exp (-h1Exp M r p) with hf
  set Dge : Set (ℝ × ℝ) := h1Dom M r ∩ {p : ℝ × ℝ | p.2 ≤ p.1} with hDge
  have hDge_meas : MeasurableSet Dge :=
    (measurableSet_h1Dom M r).inter (measurableSet_le measurable_snd measurable_fst)
  have hfint : IntegrableOn f Dge :=
    (integrableOn_exp_neg_h1Exp (lt_of_lt_of_le one_pos hr)).mono_set
      Set.inter_subset_left
  -- step 1: to indicator form and iterate (`β` outer, `α` inner)
  have hiter : (∫ p in Dge, f p) = ∫ β : ℝ, ∫ α : ℝ, Dge.indicator f (α, β) := by
    rw [Measure.volume_eq_prod, ← MeasureTheory.integral_indicator hDge_meas,
      MeasureTheory.integral_prod_symm _ (hfint.integrable_indicator hDge_meas)]
  -- step 2: the inner integral is over the section
  have hsec_meas : ∀ β : ℝ, MeasurableSet {α : ℝ | (α, β) ∈ Dge} := fun β =>
    hDge_meas.preimage measurable_prodMk_right
  have hinner : ∀ β : ℝ, (∫ α : ℝ, Dge.indicator f (α, β))
      = ∫ α in {α : ℝ | (α, β) ∈ Dge}, f (α, β) := by
    intro β
    have hpt : (fun α : ℝ => Dge.indicator f (α, β))
        = ({α : ℝ | (α, β) ∈ Dge}).indicator (fun α => f (α, β)) := by
      funext α
      by_cases h : (α, β) ∈ Dge
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_mem (show α ∈ {α : ℝ | (α, β) ∈ Dge} from h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show α ∉ {α : ℝ | (α, β) ∈ Dge} from h)]
    rw [hpt, MeasureTheory.integral_indicator (hsec_meas β)]
  -- step 3: the section is `Ici β` for `β ≥ 0` and empty for `β < 0`
  have hsec_ge : ∀ {β : ℝ}, 0 ≤ β → {α : ℝ | (α, β) ∈ Dge} = Set.Ici β := by
    intro β hβ
    ext α
    constructor
    · intro h
      exact Set.mem_Ici.mpr h.2
    · intro h
      have hαβ : β ≤ α := Set.mem_Ici.mp h
      have hα : (0:ℝ) ≤ α := le_trans hβ hαβ
      have hrad : (0:ℝ) ≤ 2*M + α - β + (r+2)^2 := by
        nlinarith [hM, hβ, hαβ, sq_nonneg (r+2)]
      exact ⟨⟨hα, hβ, hrad⟩, hαβ⟩
  have hsec_lt : ∀ {β : ℝ}, β < 0 → {α : ℝ | (α, β) ∈ Dge} = ∅ := by
    intro β hβ
    ext α
    constructor
    · intro h
      exact absurd h.1.2.1 (not_le.mpr hβ)
    · intro h
      exact absurd h (Set.notMem_empty α)
  -- step 4: the outer function, supported on `Ici 0`
  have houter : ∀ β : ℝ, (∫ α in {α : ℝ | (α, β) ∈ Dge}, f (α, β))
      = (Set.Ici 0).indicator (fun β => ∫ α in Set.Ici β, f (α, β)) β := by
    intro β
    by_cases hβ : 0 ≤ β
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hβ), hsec_ge hβ]
    · have hβ' : β < 0 := lt_of_not_ge hβ
      rw [Set.indicator_of_notMem
        (show β ∉ Set.Ici 0 from fun h => (not_le.mpr hβ') (Set.mem_Ici.mp h)),
        hsec_lt hβ', setIntegral_empty]
  -- step 5: the pointwise inner bound (C2) and its evaluation
  have hinner_bound : ∀ {β : ℝ}, 0 ≤ β →
      (∫ α in Set.Ici β, f (α, β))
        ≤ Real.exp (-saddleJ M r) * Real.exp (-β^2/4)
          * Real.sqrt (Real.pi * (r+1)) := by
    intro β hβ
    have hLHS : IntegrableOn (fun α => f (α, β)) (Set.Ioi β) :=
      integrableOn_exp_neg_h1Exp_fst_Ioi (le_trans zero_le_one hM)
        (lt_of_lt_of_le one_pos hr) hβ
    have hRHS : IntegrableOn (fun α : ℝ => Real.exp (-saddleJ M r)
        * Real.exp (-(α-β)^2/(4*(r+1))) * Real.exp (-β^2/4)) (Set.Ioi β) := by
      have h0 : Integrable fun α : ℝ => Real.exp (-(α-β)^2/(4*(r+1))) := by
        apply ((integrable_exp_neg_mul_sq (inv_pos.mpr hL4)).comp_sub_right β).congr
        filter_upwards with α
        congr 1
        field_simp [hL4.ne']
      have h1 : Integrable fun α : ℝ => (Real.exp (-saddleJ M r) * Real.exp (-β^2/4))
          * Real.exp (-(α-β)^2/(4*(r+1))) := h0.const_mul _
      apply h1.integrableOn.congr
      filter_upwards with α
      ring
    have hpt : ∀ α ∈ Set.Ioi β, f (α, β) ≤ Real.exp (-saddleJ M r)
        * Real.exp (-(α-β)^2/(4*(r+1))) * Real.exp (-β^2/4) := by
      intro α hα
      have hαβ : (0:ℝ) ≤ α - β := sub_nonneg.mpr hα.le
      have hC2 := h1Exp_ge_quadratic_of_d_nonneg hM hr hR hαβ hβ
      rw [sub_add_cancel] at hC2
      show Real.exp (-h1Exp M r (α, β)) ≤ _
      rw [show Real.exp (-saddleJ M r) * Real.exp (-(α-β)^2/(4*(r+1))) * Real.exp (-β^2/4)
          = Real.exp (-(saddleJ M r + (α-β)^2/(4*(r+1)) + β^2/4)) by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring]
      exact Real.exp_le_exp.mpr (neg_le_neg hC2)
    calc (∫ α in Set.Ici β, f (α, β))
        = ∫ α in Set.Ioi β, f (α, β) := integral_Ici_eq_integral_Ioi
      _ ≤ ∫ α in Set.Ioi β, Real.exp (-saddleJ M r)
            * Real.exp (-(α-β)^2/(4*(r+1))) * Real.exp (-β^2/4) :=
          setIntegral_mono_on hLHS hRHS measurableSet_Ioi hpt
      _ = (Real.exp (-saddleJ M r) * Real.exp (-β^2/4))
            * ∫ α in Set.Ioi β, Real.exp (-(α-β)^2/(4*(r+1))) := by
          rw [← integral_const_mul]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro α _
          ring
      _ = (Real.exp (-saddleJ M r) * Real.exp (-β^2/4))
            * ∫ d in Set.Ioi 0, Real.exp (-d^2/(4*(r+1))) := by
          congr 1
          exact integral_Ioi_comp_sub (fun d => Real.exp (-d^2/(4*(r+1)))) β
      _ = (Real.exp (-saddleJ M r) * Real.exp (-β^2/4))
            * Real.sqrt (Real.pi * (r+1)) := by
          rw [integral_exp_neg_sq_div_four_mul_Ioi _ hL]
      _ = Real.exp (-saddleJ M r) * Real.exp (-β^2/4)
          * Real.sqrt (Real.pi * (r+1)) := by ring
  -- step 6: outer monotonicity and evaluation
  have hGint : IntegrableOn (fun β => ∫ α in Set.Ici β, f (α, β)) (Set.Ici 0) := by
    have hint : Integrable fun β : ℝ => ∫ α : ℝ, Dge.indicator f (α, β) :=
      MeasureTheory.Integrable.integral_prod_right (hfint.integrable_indicator hDge_meas)
    rw [← integrable_indicator_iff measurableSet_Ici]
    apply hint.congr
    filter_upwards with β
    rw [hinner β, houter β]
  have hHint : IntegrableOn (fun β : ℝ => Real.exp (-saddleJ M r)
      * Real.exp (-β^2/4) * Real.sqrt (Real.pi * (r+1))) (Set.Ici 0) := by
    have h0 : Integrable fun β : ℝ => Real.exp (-β^2/4) := by
      apply (integrable_exp_neg_mul_sq (show (0:ℝ) < 1/4 by norm_num)).congr
      filter_upwards with β
      congr 1
      ring
    have h1 : Integrable fun β : ℝ => (Real.exp (-saddleJ M r)
        * Real.sqrt (Real.pi * (r+1))) * Real.exp (-β^2/4) := h0.const_mul _
    apply h1.integrableOn.congr
    filter_upwards with β
    ring
  calc ∫ p in Dge, f p
      = ∫ β : ℝ, ∫ α : ℝ, Dge.indicator f (α, β) := hiter
    _ = ∫ β : ℝ, (Set.Ici 0).indicator (fun β => ∫ α in Set.Ici β, f (α, β)) β := by
        apply integral_congr_ae
        filter_upwards with β
        rw [hinner β, houter β]
    _ = ∫ β in Set.Ici 0, ∫ α in Set.Ici β, f (α, β) :=
        MeasureTheory.integral_indicator measurableSet_Ici
    _ ≤ ∫ β in Set.Ici 0, Real.exp (-saddleJ M r) * Real.exp (-β^2/4)
          * Real.sqrt (Real.pi * (r+1)) :=
        setIntegral_mono_on hGint hHint measurableSet_Ici
          (fun β hβ => hinner_bound (Set.mem_Ici.mp hβ))
    _ = Real.exp (-saddleJ M r) * Real.sqrt (Real.pi * (r+1)) * Real.sqrt Real.pi := by
        have h1 : (∫ β in Set.Ioi 0, Real.exp (-β^2/4)) = Real.sqrt Real.pi := by
          simpa only [mul_one] using integral_exp_neg_sq_div_four_mul_Ioi 1 one_pos
        have heval : ∫ β in Set.Ici 0, Real.exp (-saddleJ M r) * Real.exp (-β^2/4)
            * Real.sqrt (Real.pi * (r+1))
            = (Real.exp (-saddleJ M r) * Real.sqrt (Real.pi * (r+1)))
              * ∫ β in Set.Ici 0, Real.exp (-β^2/4) := by
          rw [← integral_const_mul]
          apply setIntegral_congr_fun measurableSet_Ici
          intro β _
          ring
        rw [heval, integral_Ici_eq_integral_Ioi, h1]

/-- Slice integrability of `exp(−H₁(α, ·))` on `Ioc α (α + (2M+S²))` for
`0 ≤ α` (the `d < 0` slice): on this slice `(α, β) ∈ D₊`, so
`exp_neg_h1Exp_le` dominates. -/
theorem integrableOn_exp_neg_h1Exp_snd_Ioc (hr : 0 < r) {α : ℝ} (hα : 0 ≤ α) :
    IntegrableOn (fun β => Real.exp (-h1Exp M r (α, β)))
      (Set.Ioc α (α + (2*M + (r+2)^2))) := by
  have hL : (0:ℝ) < 4*(r+1) := by linarith
  have hdom : Integrable (fun β : ℝ => Real.exp ((r+2)^3/3)
      * (Real.exp (-(4*(r+1))⁻¹ * α^2) * Real.exp (-(1/4 : ℝ) * β^2))) :=
    ((integrable_exp_neg_mul_sq (show (0:ℝ) < 1/4 by norm_num)).const_mul _).const_mul _
  have hcont : Continuous fun β : ℝ => Real.exp (-h1Exp M r (α, β)) :=
    Real.continuous_exp.comp (((continuous_h1Exp M r).comp
      (continuous_const.prodMk continuous_id)).neg)
  rw [IntegrableOn]
  apply (hdom.integrableOn (s := Set.Ioc α (α + (2*M + (r+2)^2)))).mono'
    hcont.aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with β hβ
  have hαβ : α < β := hβ.1
  have hβle : β ≤ α + (2*M + (r+2)^2) := hβ.2
  have hp : (α, β) ∈ h1Dom M r := by
    refine ⟨hα, le_trans hα hαβ.le, ?_⟩
    show (0:ℝ) ≤ 2*M + α - β + (r+2)^2
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact exp_neg_h1Exp_le hr hp

/-- **C4, region `d < 0`** (via the `d`-split route): on
`D₊ ∩ {α < β}`, C3 dominates the integrand by
`e^{−J} e^{−(δ−δ*)²/2} e^{−α²/(4L)}` with `δ = (β−α)/2 ∈ [0, δmax]` (Tonelli with
the `α`-outer iteration, then the affine substitution `δ = (β−α)/2` with
Jacobian 2, then enlargement of the shifted Gaussian to `ℝ`), whose mass is
`e^{−J} · 2√(2π) · √(πL)`. -/
theorem frI1Plus_exp_int_dlt_le (hM : 1 ≤ M) (hr : 1 ≤ r) (hR : 2 ≤ saddleR M r) :
    ∫ p in h1Dom M r ∩ {p : ℝ × ℝ | p.1 < p.2}, Real.exp (-h1Exp M r p)
      ≤ Real.exp (-saddleJ M r) * (2 * Real.sqrt (2*Real.pi))
        * Real.sqrt (Real.pi * (r+1)) := by
  have hL : (0:ℝ) < r + 1 := by linarith
  have hL4 : (0:ℝ) < 4*(r+1) := by linarith
  set f : ℝ × ℝ → ℝ := fun p => Real.exp (-h1Exp M r p) with hf
  set Dlt : Set (ℝ × ℝ) := h1Dom M r ∩ {p : ℝ × ℝ | p.1 < p.2} with hDlt
  set δs : ℝ := 2*(r + saddleR M r) with hδs
  set B : ℝ := 2*M + (r+2)^2 with hB
  have hDlt_meas : MeasurableSet Dlt :=
    (measurableSet_h1Dom M r).inter (measurableSet_lt measurable_fst measurable_snd)
  have hfint : IntegrableOn f Dlt :=
    (integrableOn_exp_neg_h1Exp (lt_of_lt_of_le one_pos hr)).mono_set
      Set.inter_subset_left
  -- step 1: to indicator form and iterate (`α` outer, `β` inner)
  have hiter : (∫ p in Dlt, f p) = ∫ α : ℝ, ∫ β : ℝ, Dlt.indicator f (α, β) := by
    rw [Measure.volume_eq_prod, ← MeasureTheory.integral_indicator hDlt_meas,
      MeasureTheory.integral_prod _ (hfint.integrable_indicator hDlt_meas)]
  -- step 2: the inner integral is over the section
  have hsec_meas : ∀ α : ℝ, MeasurableSet {β : ℝ | (α, β) ∈ Dlt} := fun α =>
    hDlt_meas.preimage measurable_prodMk_left
  have hinner : ∀ α : ℝ, (∫ β : ℝ, Dlt.indicator f (α, β))
      = ∫ β in {β : ℝ | (α, β) ∈ Dlt}, f (α, β) := by
    intro α
    have hpt : (fun β : ℝ => Dlt.indicator f (α, β))
        = ({β : ℝ | (α, β) ∈ Dlt}).indicator (fun β => f (α, β)) := by
      funext β
      by_cases h : (α, β) ∈ Dlt
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_mem (show β ∈ {β : ℝ | (α, β) ∈ Dlt} from h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show β ∉ {β : ℝ | (α, β) ∈ Dlt} from h)]
    rw [hpt, MeasureTheory.integral_indicator (hsec_meas α)]
  -- step 3: the section is `Ioc α (α + B)` for `α ≥ 0` and empty for `α < 0`
  have hsec_ge : ∀ {α : ℝ}, 0 ≤ α → {β : ℝ | (α, β) ∈ Dlt} = Set.Ioc α (α + B) := by
    intro α hα
    ext β
    constructor
    · intro h
      exact Set.mem_Ioc.mpr ⟨h.2, by
        have hrad := h.1.2.2
        show β ≤ α + (2*M + (r+2)^2)
        linarith⟩
    · intro h
      have hlt : α < β := (Set.mem_Ioc.mp h).1
      have hle : β ≤ α + B := (Set.mem_Ioc.mp h).2
      have hβ : (0:ℝ) ≤ β := le_trans hα hlt.le
      refine ⟨⟨hα, hβ, ?_⟩, hlt⟩
      show (0:ℝ) ≤ 2*M + α - β + (r+2)^2
      rw [hB] at hle
      linarith
  have hsec_lt : ∀ {α : ℝ}, α < 0 → {β : ℝ | (α, β) ∈ Dlt} = ∅ := by
    intro α hα
    ext β
    constructor
    · intro h
      exact absurd h.1.1 (not_le.mpr hα)
    · intro h
      exact absurd h (Set.notMem_empty β)
  -- step 4: the outer function, supported on `Ici 0`
  have houter : ∀ α : ℝ, (∫ β in {β : ℝ | (α, β) ∈ Dlt}, f (α, β))
      = (Set.Ici 0).indicator (fun α => ∫ β in Set.Ioc α (α + B), f (α, β)) α := by
    intro α
    by_cases hα : 0 ≤ α
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hα), hsec_ge hα]
    · have hα' : α < 0 := lt_of_not_ge hα
      rw [Set.indicator_of_notMem
        (show α ∉ Set.Ici 0 from fun h => (not_le.mpr hα') (Set.mem_Ici.mp h)),
        hsec_lt hα', setIntegral_empty]
  -- step 5: the pointwise inner bound (C3) and its evaluation
  have hinner_bound : ∀ {α : ℝ}, 0 ≤ α →
      (∫ β in Set.Ioc α (α + B), f (α, β))
        ≤ Real.exp (-saddleJ M r) * (2 * Real.sqrt (2*Real.pi))
          * Real.exp (-α^2/(4*(r+1))) := by
    intro α hα
    -- integrability inputs
    have hLHS : IntegrableOn (fun β => f (α, β)) (Set.Ioc α (α + B)) :=
      integrableOn_exp_neg_h1Exp_snd_Ioc (lt_of_lt_of_le one_pos hr) hα
    have hg0 : Integrable fun δ : ℝ => Real.exp (-(δ - δs)^2/2) := by
      apply ((integrable_exp_neg_mul_sq
        (show (0:ℝ) < 1/2 by norm_num)).comp_sub_right δs).congr
      filter_upwards with δ
      congr 1
      ring
    have hscale : IntegrableOn (fun u : ℝ => Real.exp (-(u/2 - δs)^2/2)) (Set.Ioi 0) := by
      have h1 : IntegrableOn (fun u : ℝ => Real.exp (-((1/2)*u - δs)^2/2)) (Set.Ioi 0) :=
        (integrableOn_Ioi_comp_mul_left_iff _ 0 one_half_pos).mpr
          (by simpa using hg0.integrableOn)
      exact h1.congr_fun (fun u _ => by ring) measurableSet_Ioi
    have hIoi : IntegrableOn (fun β : ℝ => Real.exp (-((β - α)/2 - δs)^2/2))
        (Set.Ioi α) := by
      rw [← integrable_indicator_iff measurableSet_Ioi]
      have hpt : (Set.Ioi α).indicator (fun β : ℝ => Real.exp (-((β - α)/2 - δs)^2/2))
          = fun β => ((Set.Ioi 0).indicator fun u : ℝ =>
              Real.exp (-(u/2 - δs)^2/2)) (β - α) := by
        funext β
        by_cases h : α < β
        · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h),
            Set.indicator_of_mem (Set.mem_Ioi.mpr (sub_pos.mpr h))]
        · rw [Set.indicator_of_notMem (fun hh => h (Set.mem_Ioi.mp hh)),
            Set.indicator_of_notMem (fun hh => h (sub_pos.mp (Set.mem_Ioi.mp hh)))]
      rw [hpt]
      exact ((integrable_indicator_iff measurableSet_Ioi).mpr hscale).comp_sub_right α
    have hRHS : IntegrableOn (fun β : ℝ => Real.exp (-saddleJ M r)
        * Real.exp (-((β-α)/2 - δs)^2/2) * Real.exp (-α^2/(4*(r+1))))
        (Set.Ioc α (α + B)) := by
      have h1 : IntegrableOn (fun β : ℝ => (Real.exp (-saddleJ M r)
          * Real.exp (-α^2/(4*(r+1)))) * Real.exp (-((β-α)/2 - δs)^2/2))
          (Set.Ioi α) := hIoi.const_mul _
      apply (h1.mono_set Set.Ioc_subset_Ioi_self).congr
      filter_upwards with β
      ring
    -- the pointwise bound from C3
    have hpt : ∀ β ∈ Set.Ioc α (α + B), f (α, β) ≤ Real.exp (-saddleJ M r)
        * Real.exp (-((β-α)/2 - δs)^2/2) * Real.exp (-α^2/(4*(r+1))) := by
      intro β hβ
      have hαβ : α < β := hβ.1
      have hδ0 : (0:ℝ) ≤ (β - α)/2 := by linarith
      have hδmax : (β - α)/2 ≤ (2*M + (r+2)^2)/2 := by
        have hle := hβ.2
        rw [hB] at hle
        linarith
      have hC3 := h1Exp_ge_quadratic_of_d_neg hM hr hR hα ⟨hδ0, hδmax⟩
      rw [show α + 2*((β - α)/2) = β by ring] at hC3
      rw [← hδs] at hC3
      show Real.exp (-h1Exp M r (α, β)) ≤ _
      rw [show Real.exp (-saddleJ M r) * Real.exp (-((β-α)/2 - δs)^2/2)
          * Real.exp (-α^2/(4*(r+1)))
          = Real.exp (-(saddleJ M r + ((β-α)/2 - δs)^2/2 + α^2/(4*(r+1)))) by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring]
      exact Real.exp_le_exp.mpr (neg_le_neg hC3)
    -- the inner evaluation
    have heval : (∫ β in Set.Ioc α (α + B), Real.exp (-saddleJ M r)
        * Real.exp (-((β-α)/2 - δs)^2/2) * Real.exp (-α^2/(4*(r+1))))
        = (Real.exp (-saddleJ M r) * Real.exp (-α^2/(4*(r+1))))
          * ∫ β in Set.Ioc α (α + B), Real.exp (-((β-α)/2 - δs)^2/2) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro β _
      ring
    have hshift : (∫ β in Set.Ioi α, Real.exp (-((β - α)/2 - δs)^2/2))
        = ∫ u in Set.Ioi 0, Real.exp (-(u/2 - δs)^2/2) :=
      integral_Ioi_comp_sub (fun u => Real.exp (-(u/2 - δs)^2/2)) α
    have hscaleeq : (∫ u in Set.Ioi 0, Real.exp (-(u/2 - δs)^2/2))
        = 2 * ∫ δ in Set.Ioi 0, Real.exp (-(δ - δs)^2/2) := by
      have h := MeasureTheory.integral_comp_mul_left_Ioi
        (fun δ : ℝ => Real.exp (-(δ - δs)^2/2)) 0 one_half_pos
      rw [mul_zero, smul_eq_mul] at h
      have h' : (∫ u in Set.Ioi 0, Real.exp (-((1/2)*u - δs)^2/2))
          = (1/2)⁻¹ * ∫ δ in Set.Ioi 0, Real.exp (-(δ - δs)^2/2) := h
      calc ∫ u in Set.Ioi 0, Real.exp (-(u/2 - δs)^2/2)
          = ∫ u in Set.Ioi 0, Real.exp (-((1/2)*u - δs)^2/2) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro u _
            ring
        _ = (1/2)⁻¹ * ∫ δ in Set.Ioi 0, Real.exp (-(δ - δs)^2/2) := h'
        _ = 2 * ∫ δ in Set.Ioi 0, Real.exp (-(δ - δs)^2/2) := by
            rw [show ((1:ℝ)/2)⁻¹ = 2 by norm_num]
    have henlarge : (∫ δ in Set.Ioi 0, Real.exp (-(δ - δs)^2/2))
        ≤ Real.sqrt (2*Real.pi) := by
      have h1 : (∫ δ in Set.Ioi 0, Real.exp (-(δ - δs)^2/2))
          ≤ ∫ δ : ℝ, Real.exp (-(δ - δs)^2/2) := by
        have h2 : (∫ δ in Set.Ioi 0, Real.exp (-(δ - δs)^2/2))
            ≤ ∫ δ in Set.univ, Real.exp (-(δ - δs)^2/2) :=
          setIntegral_mono_set hg0.integrableOn
            (Filter.Eventually.of_forall fun δ => (Real.exp_pos _).le)
            (Filter.Eventually.of_forall fun δ _ => Set.mem_univ δ)
        rwa [setIntegral_univ] at h2
      have h3 : (∫ δ : ℝ, Real.exp (-(δ - δs)^2/2)) = Real.sqrt (2*Real.pi) := by
        have h4 : (∫ δ : ℝ, Real.exp (-(δ - δs)^2/2)) = ∫ x : ℝ, Real.exp (-x^2/2) :=
          MeasureTheory.integral_sub_right_eq_self (μ := volume)
            (fun x : ℝ => Real.exp (-x^2/2)) δs
        rw [h4]
        have h5 : (fun x : ℝ => Real.exp (-x^2/2))
            = fun x : ℝ => Real.exp (-(1/2)*x^2) := by
          funext x
          congr 1
          ring
        rw [h5, integral_gaussian]
        congr 1
        ring_nf
      exact h1.trans_eq h3
    calc (∫ β in Set.Ioc α (α + B), f (α, β))
        ≤ ∫ β in Set.Ioc α (α + B), Real.exp (-saddleJ M r)
            * Real.exp (-((β-α)/2 - δs)^2/2) * Real.exp (-α^2/(4*(r+1))) :=
          setIntegral_mono_on hLHS hRHS measurableSet_Ioc hpt
      _ = (Real.exp (-saddleJ M r) * Real.exp (-α^2/(4*(r+1))))
            * ∫ β in Set.Ioc α (α + B), Real.exp (-((β-α)/2 - δs)^2/2) := heval
      _ ≤ (Real.exp (-saddleJ M r) * Real.exp (-α^2/(4*(r+1))))
            * ∫ β in Set.Ioi α, Real.exp (-((β-α)/2 - δs)^2/2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact setIntegral_mono_set hIoi
            (Filter.Eventually.of_forall fun β => (Real.exp_pos _).le)
            (Filter.Eventually.of_forall fun β hβ => Set.Ioc_subset_Ioi_self hβ)
      _ = (Real.exp (-saddleJ M r) * Real.exp (-α^2/(4*(r+1))))
            * (2 * ∫ δ in Set.Ioi 0, Real.exp (-(δ - δs)^2/2)) := by
          rw [hshift, hscaleeq]
      _ ≤ (Real.exp (-saddleJ M r) * Real.exp (-α^2/(4*(r+1))))
            * (2 * Real.sqrt (2*Real.pi)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left henlarge (by norm_num)) (by positivity)
      _ = Real.exp (-saddleJ M r) * (2 * Real.sqrt (2*Real.pi))
            * Real.exp (-α^2/(4*(r+1))) := by ring
  -- step 6: outer monotonicity and evaluation
  have hGint : IntegrableOn (fun α => ∫ β in Set.Ioc α (α + B), f (α, β))
      (Set.Ici 0) := by
    have hint : Integrable fun α : ℝ => ∫ β : ℝ, Dlt.indicator f (α, β) :=
      MeasureTheory.Integrable.integral_prod_left (hfint.integrable_indicator hDlt_meas)
    rw [← integrable_indicator_iff measurableSet_Ici]
    apply hint.congr
    filter_upwards with α
    rw [hinner α, houter α]
  have hHint : IntegrableOn (fun α : ℝ => Real.exp (-saddleJ M r)
      * (2 * Real.sqrt (2*Real.pi)) * Real.exp (-α^2/(4*(r+1)))) (Set.Ici 0) := by
    have h0 : Integrable fun α : ℝ => Real.exp (-α^2/(4*(r+1))) := by
      apply (integrable_exp_neg_mul_sq (inv_pos.mpr hL4)).congr
      filter_upwards with α
      congr 1
      field_simp [hL4.ne']
    have h1 : Integrable fun α : ℝ => (Real.exp (-saddleJ M r)
        * (2 * Real.sqrt (2*Real.pi))) * Real.exp (-α^2/(4*(r+1))) := h0.const_mul _
    apply h1.integrableOn.congr
    filter_upwards with α
    ring
  calc ∫ p in Dlt, f p
      = ∫ α : ℝ, ∫ β : ℝ, Dlt.indicator f (α, β) := hiter
    _ = ∫ α : ℝ, (Set.Ici 0).indicator
          (fun α => ∫ β in Set.Ioc α (α + B), f (α, β)) α := by
        apply integral_congr_ae
        filter_upwards with α
        rw [hinner α, houter α]
    _ = ∫ α in Set.Ici 0, ∫ β in Set.Ioc α (α + B), f (α, β) :=
        MeasureTheory.integral_indicator measurableSet_Ici
    _ ≤ ∫ α in Set.Ici 0, Real.exp (-saddleJ M r) * (2 * Real.sqrt (2*Real.pi))
          * Real.exp (-α^2/(4*(r+1))) :=
        setIntegral_mono_on hGint hHint measurableSet_Ici
          (fun α hα => hinner_bound (Set.mem_Ici.mp hα))
    _ = Real.exp (-saddleJ M r) * (2 * Real.sqrt (2*Real.pi))
          * Real.sqrt (Real.pi * (r+1)) := by
        have heval : ∫ α in Set.Ici 0, Real.exp (-saddleJ M r)
            * (2 * Real.sqrt (2*Real.pi)) * Real.exp (-α^2/(4*(r+1)))
            = (Real.exp (-saddleJ M r) * (2 * Real.sqrt (2*Real.pi)))
              * ∫ α in Set.Ici 0, Real.exp (-α^2/(4*(r+1))) := by
          -- `rw [← integral_const_mul]` closes this by rfl (associations coincide)
          rw [← integral_const_mul]
        rw [heval]
        rw [integral_Ici_eq_integral_Ioi]
        rw [integral_exp_neg_sq_div_four_mul_Ioi _ hL]

/-- **C4** (by the `d`-split route, in place of the
Hessian/constrained-minimizer/Taylor argument; see the module
docstring): the `D₊` Gaussian mass of `e^{−H₁}` is `O(√L)·e^{−J_M(r)}`.
The Hessian comparison pays `4πL`; the `d`-split with the retained slack
pays only `π√L + 2√(2π)√(πL)` (`frI1Plus_exp_int_dge_le` /
`frI1Plus_exp_int_dlt_le`), which implies the paper's form of the bound
(`(r+1)^{1/2} ≤ (1+r)^{1/2}`). -/
theorem frI1Plus_exp_int_le (hM : 1 ≤ M) (hr : 1 ≤ r) (hR : 2 ≤ saddleR M r) :
    ∃ C : ℝ, 0 < C ∧
      ∫ p in h1Dom M r, Real.exp (-h1Exp M r p)
        ≤ C * (r+1)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
  have hDlt_meas : MeasurableSet (h1Dom M r ∩ {p : ℝ × ℝ | p.1 < p.2}) :=
    (measurableSet_h1Dom M r).inter (measurableSet_lt measurable_fst measurable_snd)
  have hfint : IntegrableOn (fun p => Real.exp (-h1Exp M r p)) (h1Dom M r) :=
    integrableOn_exp_neg_h1Exp (lt_of_lt_of_le one_pos hr)
  have hU : h1Dom M r ∩ {p : ℝ × ℝ | p.2 ≤ p.1}
      ∪ (h1Dom M r ∩ {p : ℝ × ℝ | p.1 < p.2}) = h1Dom M r := by
    ext p
    constructor
    · intro h
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact h1
    · intro hp
      rcases le_or_gt p.2 p.1 with h | h
      · exact (Set.mem_union _ _ _).mpr (Or.inl ⟨hp, h⟩)
      · exact (Set.mem_union _ _ _).mpr (Or.inr ⟨hp, h⟩)
  have hDisj : Disjoint (h1Dom M r ∩ {p : ℝ × ℝ | p.2 ≤ p.1})
      (h1Dom M r ∩ {p : ℝ × ℝ | p.1 < p.2}) := by
    rw [Set.disjoint_left]
    rintro p ⟨-, hle⟩ ⟨-, hlt⟩
    exact (not_le.mpr (show p.1 < p.2 from hlt)) (show p.2 ≤ p.1 from hle)
  have hunion : ∫ p in h1Dom M r, Real.exp (-h1Exp M r p)
      = (∫ p in h1Dom M r ∩ {p : ℝ × ℝ | p.2 ≤ p.1}, Real.exp (-h1Exp M r p))
        + (∫ p in h1Dom M r ∩ {p : ℝ × ℝ | p.1 < p.2}, Real.exp (-h1Exp M r p)) := by
    have h := setIntegral_union hDisj hDlt_meas (hfint.mono_set Set.inter_subset_left)
      (hfint.mono_set Set.inter_subset_left)
    rwa [hU] at h
  have hge := frI1Plus_exp_int_dge_le hM hr hR
  have hlt := frI1Plus_exp_int_dlt_le hM hr hR
  refine ⟨Real.sqrt Real.pi * (Real.sqrt Real.pi + 2 * Real.sqrt (2*Real.pi)),
    by positivity, ?_⟩
  have hsqrt : Real.sqrt (Real.pi * (r+1))
      = Real.sqrt Real.pi * (r+1)^(1/2 : ℝ) := by
    rw [Real.sqrt_mul Real.pi_nonneg]
    congr 1
    exact Real.sqrt_eq_rpow _
  rw [hunion]
  calc (∫ p in h1Dom M r ∩ {p : ℝ × ℝ | p.2 ≤ p.1}, Real.exp (-h1Exp M r p))
        + (∫ p in h1Dom M r ∩ {p : ℝ × ℝ | p.1 < p.2}, Real.exp (-h1Exp M r p))
      ≤ (Real.exp (-saddleJ M r) * Real.sqrt (Real.pi * (r+1)) * Real.sqrt Real.pi)
        + (Real.exp (-saddleJ M r) * (2 * Real.sqrt (2*Real.pi))
          * Real.sqrt (Real.pi * (r+1))) := add_le_add hge hlt
    _ = Real.sqrt Real.pi * (Real.sqrt Real.pi + 2 * Real.sqrt (2*Real.pi))
          * (r+1)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
        rw [hsqrt]
        ring

/-! ### C6: the negative-Airy `G₁` package -/

/-- **C6** (the paper's exponent `G₁`): the `I₁⁻` exponent
`G₁(α, β) = α²/(4L) + β²/4 + S(2M+α−β) + (2/3)S³` with `L = r+1`, `S = r+2`,
`a² = 2M` inlined. -/
noncomputable def g1Exp (M r : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1^2/(4*(r+1)) + p.2^2/4 + (r+2)*(2*M + p.1 - p.2) + (2/3)*(r+2)^3

/-- The `G₁` boundary point `A(α) = 2M + S² + α`. -/
def g1Boundary (M r α : ℝ) : ℝ := 2*M + (r+2)^2 + α

/-- The `β`-derivative of `G₁`: `∂_βG₁ = β/2 − S`. -/
theorem hasDerivAt_g1Exp_beta (M r α β : ℝ) :
    HasDerivAt (fun β' => g1Exp M r (α, β')) (β/2 - (r+2)) β := by
  have t1 : HasDerivAt (fun β' : ℝ => β'^2/4) (β/2) β := by
    refine ((hasDerivAt_pow 2 β).div_const 4).congr_deriv ?_
    ring
  have t2 : HasDerivAt (fun β' : ℝ => (r+2)*(2*M + α - β')) (-(r+2)) β := by
    refine (((hasDerivAt_const β (2*M + α)).sub (hasDerivAt_id' β)).const_mul
      (r+2)).congr_deriv ?_
    ring
  have htot := ((hasDerivAt_const β (α^2/(4*(r+1)))).add t1).add t2
    |>.add (hasDerivAt_const β ((2/3)*(r+2)^3))
  have hval : ((0 : ℝ) + β/2 + -(r+2)) + 0 = β/2 - (r+2) := by ring
  rwa [hval] at htot

/-- **C6, explicit constant**: for
`β ≥ A(α)`, `∂_βG₁ = β/2 − S ≥ (2M+3)/2`, valid for ALL `M`, `r ≥ 1`
(the paper has `≥ a²/4` "for all sufficiently large `a`"; the sharp form
follows from `A(α) − 2S = 2M + (S−1)² − 1 + α ≥ 2M + 3`). -/
theorem g1Exp_deriv_beta_ge (hr : 1 ≤ r) (hα : 0 ≤ α) {β : ℝ}
    (hβ : g1Boundary M r α ≤ β) :
    (2*M+3)/2 ≤ deriv (fun β' => g1Exp M r (α, β')) β := by
  rw [(hasDerivAt_g1Exp_beta M r α β).deriv]
  have h1 : (4:ℝ) ≤ (r+1)^2 := by nlinarith [hr, sq_nonneg (r-1)]
  unfold g1Boundary at hβ
  nlinarith [hβ, hα, h1]

/-- **C6** (the boundary value of `G₁`):
`G₁(α, A(α)) = α²/(4L) + (2M+S²+α)²/4 − S³/3` (pure algebra). -/
theorem g1Exp_boundary_eq (M r α : ℝ) :
    g1Exp M r (α, g1Boundary M r α)
      = α^2/(4*(r+1)) + (2*M + (r+2)^2 + α)^2/4 - (r+2)^3/3 := by
  simp only [g1Exp, g1Boundary]
  ring

/-- **C6**: `G₁(α, A(α)) ≥ E₀ := (2M+S²)²/4 − S³/3`. -/
theorem g1Exp_boundary_ge_E0 (hM : 0 < M) (hr : 0 < r) (hα : 0 ≤ α) :
    (2*M + (r+2)^2)^2/4 - (r+2)^3/3 ≤ g1Exp M r (α, g1Boundary M r α) := by
  rw [g1Exp_boundary_eq]
  have hX : (0:ℝ) ≤ 2*M + (r+2)^2 := by nlinarith [hM, sq_nonneg (r+2)]
  have h1 : (0:ℝ) ≤ α^2/(4*(r+1)) :=
    div_nonneg (sq_nonneg α) (by linarith)
  nlinarith [h1, mul_nonneg hX hα, sq_nonneg α]

/-- **C6** (the exact quadratic expansion in `β`):
`G₁(α, A(α)+t) = G₁(α, A(α)) + (A(α)/2 − S)·t + t²/4` (pure algebra). -/
theorem g1Exp_quadratic_beta (M r α t : ℝ) :
    g1Exp M r (α, g1Boundary M r α + t)
      = g1Exp M r (α, g1Boundary M r α)
        + (g1Boundary M r α/2 - (r+2))*t + t^2/4 := by
  simp only [g1Exp, g1Boundary]
  ring

/-- **C6** (the genuine χ-dependent largeness):
in the subcritical range `r ≤ χa` with `a = √(2M)`,
`E₀ = (2M+S²)²/4 − S³/3 ≥ a⁴/8 = (2M)²/8` for `a ≥ 8(χ+2)³/3`
(`S ≤ χa+2 ≤ (χ+2)a`, so `S³ ≤ (χ+2)³a³`, and `(2M+S²)² ≥ (2M)² = a⁴`). -/
theorem frI1Minus_E0_ge {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ c a₀ : ℝ, 0 < c ∧ ∀ {M r : ℝ}, a₀ ≤ Real.sqrt (2*M) → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      c * (2*M)^2 ≤ (2*M + (r+2)^2)^2/4 - (r+2)^3/3 := by
  refine ⟨1/8, max 1 (8*(χ+2)^3/3), by norm_num, ?_⟩
  intro M r ha₀ hr hradm
  have ha1 : (1:ℝ) ≤ Real.sqrt (2*M) := le_trans (le_max_left _ _) ha₀
  have hM0 : (0:ℝ) ≤ 2*M := by
    rcases le_or_gt 0 (2*M) with h | h
    · exact h
    · rw [Real.sqrt_eq_zero_of_nonpos h.le] at ha1
      linarith
  set a := Real.sqrt (2*M) with ha
  have ha0 : (0:ℝ) ≤ a := Real.sqrt_nonneg _
  have ha2 : a^2 = 2*M := Real.sq_sqrt hM0
  have ha0' : (0:ℝ) < a := lt_of_lt_of_le one_pos ha1
  have hSle : r + 2 ≤ (χ+2) * a := by
    have h2 : (2:ℝ) ≤ 2*a := by linarith [ha1]
    nlinarith [hradm, h2, hχ0, ha0]
  have hS3 : (r+2)^3 ≤ (χ+2)^3 * a^3 := by
    have h1 : (r+2)^3 ≤ ((χ+2) * a)^3 :=
      pow_le_pow_left₀ (by linarith [hr] : (0:ℝ) ≤ r+2) hSle 3
    rwa [mul_pow] at h1
  have hbound : (χ+2)^3 * a^3/3 ≤ a^4/8 := by
    have h1 : 8*(χ+2)^3/3 ≤ a := le_trans (le_max_right _ _) ha₀
    have h3 : (χ+2)^3/3 ≤ a/8 := by linarith [h1]
    have h4 : ((χ+2)^3/3) * a^3 ≤ (a/8) * a^3 :=
      mul_le_mul_of_nonneg_right h3 (pow_nonneg ha0 3)
    calc (χ+2)^3 * a^3/3 = ((χ+2)^3/3) * a^3 := by ring
      _ ≤ (a/8) * a^3 := h4
      _ = a^4/8 := by ring
  have ha4 : a^4 = (2*M)^2 := by
    calc a^4 = (a^2)^2 := by ring
      _ = (2*M)^2 := by rw [ha2]
  have hs1 : (2*M)^2 ≤ (2*M + (r+2)^2)^2 := by
    nlinarith [hM0, sq_nonneg (r+2), mul_nonneg hM0 (sq_nonneg (r+2))]
  have hs2 : (r+2)^3/3 ≤ (χ+2)^3 * a^3/3 :=
    div_le_div_of_nonneg_right hS3 (by norm_num : (0:ℝ) ≤ 3)
  nlinarith [ha4, hs1, hs2, hbound]

/-- **C6**: the `β`-integration at the sharp slope:
`∫₀^∞ e^{−((2M+3)/2)t − t²/4} dt ≤ 1/M` (drop `−t²/4 ≤ 0`, then the exact
exponential integral `2/(2M+3) ≤ 1/M`). -/
theorem frI1Minus_int_beta_le (hM : 0 < M) :
    ∫ t in Set.Ioi 0, Real.exp (-(((2*M+3)/2) * t) - t^2/4) ≤ 1/M := by
  have h2M3 : (0:ℝ) < 2*M+3 := by linarith
  have hk : (0:ℝ) < (2*M+3)/2 := by linarith
  have hexpint : IntegrableOn (fun t : ℝ => Real.exp (-(((2*M+3)/2) * t)))
      (Set.Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => Real.exp (-u)) 0 hk).mpr
      (by simpa using integrableOn_exp_neg_Ioi (0:ℝ))
    exact h
  have hcont : Continuous fun t : ℝ => Real.exp (-(((2*M+3)/2) * t) - t^2/4) :=
    Real.continuous_exp.comp (by fun_prop)
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(((2*M+3)/2) * t) - t^2/4))
      (Set.Ioi 0) := by
    apply hexpint.mono' hcont.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])
  calc ∫ t in Set.Ioi 0, Real.exp (-(((2*M+3)/2) * t) - t^2/4)
      ≤ ∫ t in Set.Ioi 0, Real.exp (-(((2*M+3)/2) * t)) :=
        setIntegral_mono_on hint hexpint measurableSet_Ioi
          (fun t ht => Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t]))
    _ = 1/((2*M+3)/2) := integral_exp_neg_mul_Ioi hk
    _ ≤ 1/M := by
        rw [show (1:ℝ)/((2*M+3)/2) = 2/(2*M+3) by field_simp [h2M3.ne'],
          show (1:ℝ)/M = 2/(2*M) by field_simp [hM.ne']]
        exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2)
          (by positivity : (0:ℝ) < 2*M) (by linarith)

/-- **C6**: the `α`-integration `∫₀^∞ e^{−Mα} dα = 1/M`
(slope `a²/2 = M`). -/
theorem frI1Minus_int_alpha_le (hM : 0 < M) :
    ∫ α in Set.Ioi 0, Real.exp (-(M * α)) ≤ 1/M :=
  le_of_eq (integral_exp_neg_mul_Ioi hM)

/-! ### C7: the `I₂⁻` exponent `G_{2,−}` -/

/-- **C7**: `G_{2,−}(δ) = δ²/2 − 2Sδ + S·a² + (2/3)S³`
with `a² = 2M` inlined. -/
noncomputable def g2Minus (M r δ : ℝ) : ℝ :=
  δ^2/2 - 2*(r+2)*δ + (r+2)*(2*M) + (2/3)*(r+2)^3

/-- The derivative `G'_{2,−}(δ) = δ − 2S`. -/
theorem hasDerivAt_g2Minus (M r δ : ℝ) :
    HasDerivAt (g2Minus M r) (δ - 2*(r+2)) δ := by
  have t1 : HasDerivAt (fun δ : ℝ => δ^2/2) δ δ := by
    refine ((hasDerivAt_pow 2 δ).div_const 2).congr_deriv ?_
    ring
  have t2 : HasDerivAt (fun δ : ℝ => 2*(r+2)*δ) (2*(r+2)) δ := by
    simpa using (hasDerivAt_id' δ).const_mul (2*(r+2))
  have htot := (t1.sub t2).add
    (hasDerivAt_const δ ((r+2)*(2*M) + (2/3)*(r+2)^3))
  have hval : (δ - 2*(r+2)) + 0 = δ - 2*(r+2) := by ring
  rw [hval] at htot
  show HasDerivAt (fun δ : ℝ => δ^2/2 - 2*(r+2)*δ + (r+2)*(2*M) + (2/3)*(r+2)^3) _ _
  convert htot using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- **C7, explicit constant**: for
`δ ≥ δmax = (2M+S²)/2` and `M ≥ 3`,
`G'_{2,−}(δ) = δ − 2S ≥ (2M + r² − 4)/2 ≥ M/2 = a²/4`
(the paper has `≥ ca²` "for all sufficiently large `a`"). -/
theorem g2Minus_deriv_ge (hM : 3 ≤ M) (hr : 1 ≤ r) {δ : ℝ}
    (hδ : (2*M + (r+2)^2)/2 ≤ δ) :
    M/2 ≤ deriv (g2Minus M r) δ := by
  rw [(hasDerivAt_g2Minus M r δ).deriv]
  nlinarith [hδ, hM, hr, sq_nonneg (r - 1)]

/-- **C7**: the boundary value
`G_{2,−}(δmax) = (2M+S²)²/8 − S³/3` (pure algebra). -/
theorem g2Minus_boundary_eq (M r : ℝ) :
    g2Minus M r ((2*M + (r+2)^2)/2) = (2*M + (r+2)^2)^2/8 - (r+2)^3/3 := by
  simp only [g2Minus]
  ring

/-- **C7** (the genuine χ-dependent
largeness): in the subcritical range `r ≤ χa` with `a = √(2M)`,
`E_{2,0} = (2M+S²)²/8 − S³/3 ≥ a⁴/16 = (2M)²/16` for `a ≥ 16(χ+2)³/3`. -/
theorem frI2Minus_E20_ge {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ c a₀ : ℝ, 0 < c ∧ ∀ {M r : ℝ}, a₀ ≤ Real.sqrt (2*M) → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      c * (2*M)^2 ≤ (2*M + (r+2)^2)^2/8 - (r+2)^3/3 := by
  refine ⟨1/16, max 1 (16*(χ+2)^3/3), by norm_num, ?_⟩
  intro M r ha₀ hr hradm
  have ha1 : (1:ℝ) ≤ Real.sqrt (2*M) := le_trans (le_max_left _ _) ha₀
  have hM0 : (0:ℝ) ≤ 2*M := by
    rcases le_or_gt 0 (2*M) with h | h
    · exact h
    · rw [Real.sqrt_eq_zero_of_nonpos h.le] at ha1
      linarith
  set a := Real.sqrt (2*M) with ha
  have ha0 : (0:ℝ) ≤ a := Real.sqrt_nonneg _
  have ha2 : a^2 = 2*M := Real.sq_sqrt hM0
  have hSle : r + 2 ≤ (χ+2) * a := by
    have h2 : (2:ℝ) ≤ 2*a := by linarith [ha1]
    nlinarith [hradm, h2, hχ0, ha0]
  have hS3 : (r+2)^3 ≤ (χ+2)^3 * a^3 := by
    have h1 : (r+2)^3 ≤ ((χ+2) * a)^3 :=
      pow_le_pow_left₀ (by linarith [hr] : (0:ℝ) ≤ r+2) hSle 3
    rwa [mul_pow] at h1
  have hbound : (χ+2)^3 * a^3/3 ≤ a^4/16 := by
    have h1 : 16*(χ+2)^3/3 ≤ a := le_trans (le_max_right _ _) ha₀
    have h3 : (χ+2)^3/3 ≤ a/16 := by linarith [h1]
    have h4 : ((χ+2)^3/3) * a^3 ≤ (a/16) * a^3 :=
      mul_le_mul_of_nonneg_right h3 (pow_nonneg ha0 3)
    calc (χ+2)^3 * a^3/3 = ((χ+2)^3/3) * a^3 := by ring
      _ ≤ (a/16) * a^3 := h4
      _ = a^4/16 := by ring
  have ha4 : a^4 = (2*M)^2 := by
    calc a^4 = (a^2)^2 := by ring
      _ = (2*M)^2 := by rw [ha2]
  have hs1 : (2*M)^2 ≤ (2*M + (r+2)^2)^2 := by
    nlinarith [hM0, sq_nonneg (r+2), mul_nonneg hM0 (sq_nonneg (r+2))]
  have hs2 : (r+2)^3/3 ≤ (χ+2)^3 * a^3/3 :=
    div_le_div_of_nonneg_right hS3 (by norm_num : (0:ℝ) ≤ 3)
  nlinarith [ha4, hs1, hs2, hbound]

/-- **C7** (the linear growth): for `δ ≥ δmax`,
`G_{2,−}(δ) ≥ G_{2,−}(δmax) + (M/2)(δ − δmax)`.
Via the exact quadratic expansion
`G_{2,−}(δmax + s) = G_{2,−}(δmax) + (δmax − 2S)s + s²/2` (pure algebra),
the boundary slope bound `δmax − 2S ≥ M/2` (`M ≥ 3`), and `s²/2 ≥ 0`. -/
theorem g2Minus_ge_linear (hM : 3 ≤ M) (hr : 1 ≤ r) {δ : ℝ}
    (hδ : (2*M + (r+2)^2)/2 ≤ δ) :
    g2Minus M r ((2*M + (r+2)^2)/2) + (M/2)*(δ - (2*M + (r+2)^2)/2)
      ≤ g2Minus M r δ := by
  have hexpand : g2Minus M r δ = g2Minus M r ((2*M + (r+2)^2)/2)
      + (((2*M + (r+2)^2)/2) - 2*(r+2))*(δ - (2*M + (r+2)^2)/2)
      + (δ - (2*M + (r+2)^2)/2)^2/2 := by
    simp only [g2Minus]
    ring
  have hslope : M/2 ≤ (2*M + (r+2)^2)/2 - 2*(r+2) := by
    nlinarith [hM, hr, sq_nonneg (r - 1)]
  have hs : (0:ℝ) ≤ δ - (2*M + (r+2)^2)/2 := sub_nonneg.mpr hδ
  rw [hexpand]
  nlinarith [mul_le_mul_of_nonneg_right hslope hs,
    sq_nonneg (δ - (2*M + (r+2)^2)/2)]

/-! ### C8: the `I₂⁺` exponent `H̃₂` and its reduction to `F` -/

/-- **C8**:
`H̃₂(α, β) = (α²+β²)/4 + S(2M−α−β) + (2/3)S³ + (2/3)(2M−α−β+S²)^{3/2}`
with `S = r+2`, `a² = 2M` inlined. -/
noncomputable def h2Tilde (M r : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.1^2 + p.2^2)/4 + (r+2)*(2*M - p.1 - p.2) + (2/3)*(r+2)^3
    + (2/3)*(2*M - p.1 - p.2 + (r+2)^2)^(3/2 : ℝ)

/-- **C8** (the exact decomposition of `H̃₂`): with
`δ = (α+β)/2`, `v = (α−β)/2`, `H̃₂(α, β) = F(δ) + v²/2` exactly
(`(α²+β²)/4 = (δ²+v²)/2` and the radicand congruence; pure algebra). -/
theorem h2Tilde_eq_saddleF_add (M r α β : ℝ) :
    h2Tilde M r (α, β) = saddleF M r ((α+β)/2) + ((α-β)/2)^2/2 := by
  have harg : 2*M - α - β + (r+2)^2 = 2*M - 2*((α+β)/2) + (r+2)^2 := by ring
  simp only [h2Tilde, saddleF]
  rw [harg]
  ring

/-- **C8**: on the positive-Airy region
(`α, β ≥ 0`, `2M−α−β+S² ≥ 0` — i.e. exactly `δ = (α+β)/2 ∈ [0, δmax]`),
`H̃₂ ≥ J_M(r) + (δ−δ*)²/2 + v²/2` by `saddleF_ge`. -/
theorem h2Tilde_ge (hM : 1 ≤ M) (hr : 1 ≤ r) (hR : 2 ≤ saddleR M r)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hpos : 0 ≤ 2*M - α - β + (r+2)^2) :
    saddleJ M r + ((α+β)/2 - 2*(r + saddleR M r))^2/2 + ((α-β)/2)^2/2
      ≤ h2Tilde M r (α, β) := by
  rw [h2Tilde_eq_saddleF_add]
  have hδ : (α+β)/2 ∈ Set.Icc 0 ((2*M + (r+2)^2)/2) := by
    refine ⟨?_, ?_⟩ <;> nlinarith [hα, hβ, hpos]
  have hF := saddleF_ge hM hr hR ((α+β)/2) hδ
  linarith [hF]

/-! ### B3: the `K(α,γ)` reflection corollary of the Gaussian convolution lemma -/

/-- **B3** (the paper's "the same calculation as in
the proof of" its Gaussian convolution lemma): the reflected truncated convolution
`K(α,γ) = ∫_{w>0} p₁(α+w)p_r(γ+w)dw = p_{r+1}(γ−α)·Φ(−(rα+γ)/√(2r(r+1)))`.
A reflection corollary of the proved `AiryConj.heatKernel_conv_cdf` at `(L, M, α, β) ↦ (r, 0, γ, α)` via the substitution `z ↦ −w`
(`AiryConj.integral_Iic_comp_const_sub` at `M = 0`) and `mul_comm`. -/
theorem heatKernel_conv_cdf_Ioi (hr : 0 < r) (α γ : ℝ) :
    ∫ w in Set.Ioi 0, heatKernel 1 (α+w) * heatKernel r (γ+w)
      = heatKernel (r+1) (γ-α)
        * (gaussianTail (1/2) ((r*α+γ) / Real.sqrt (2*r*(r+1)))
            / Real.sqrt (2*Real.pi)) := by
  have h := AiryConj.integral_Iic_comp_const_sub
    (fun w => heatKernel 1 (α+w) * heatKernel r (γ+w)) 0
  have h' : (∫ w in Set.Ioi 0, heatKernel 1 (α+w) * heatKernel r (γ+w))
      = ∫ z in Set.Iic 0, heatKernel 1 (α+(0-z)) * heatKernel r (γ+(0-z)) := h.symm
  rw [h']
  have hcong : (∫ z in Set.Iic 0, heatKernel 1 (α+(0-z)) * heatKernel r (γ+(0-z)))
      = ∫ z in Set.Iic 0, heatKernel r (0+γ-z) * heatKernel 1 (0-z+α) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro z _
    show heatKernel 1 (α+(0-z)) * heatKernel r (γ+(0-z))
      = heatKernel r (0+γ-z) * heatKernel 1 (0-z+α)
    rw [show γ + (0 - z) = 0 + γ - z by ring, show α + (0 - z) = 0 - z + α by ring,
      mul_comm]
  rw [hcong, AiryConj.heatKernel_conv_cdf hr 0 γ α]
  rw [show γ + r*α = r*α+γ by ring]

/-! ### B2: the `boundJ` Chernoff bound -/

/-- **B2** (the paper's bound on `J`): for `α, β ≥ 0`,
`p_{S}(α−β)·Φ(−(α+Lβ)/√(2LS)) ≤ C·S^{−1/2}·e^{−α²/(4L)−β²/4}` with
`L = r+1`, `S = r+2`.  Chernoff (`AiryConj.gaussianTail_chernoff` with the
`√(2π)`-division — `√(π/2)/√(2π) = 1/2`) plus the exact identity
`(α−β)²/(4S) + (α+Lβ)²/(4LS) = α²/(4L) + β²/4`
(`field_simp; ring`). -/
theorem frI1_Jbound (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : ℝ}, 0 ≤ α → 0 ≤ β →
      heatKernel (r+2) (α-β)
        * (gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
            / Real.sqrt (2*Real.pi))
        ≤ C * (r+2)^(-1/2 : ℝ) * Real.exp (-α^2/(4*(r+1)) - β^2/4) := by
  have hL : (0:ℝ) < r + 1 := by linarith
  have hS : (0:ℝ) < r + 2 := by linarith
  refine ⟨(4*Real.pi)^(-1/2 : ℝ) / 2, by positivity, ?_⟩
  intro α β hα hβ
  have harg : (0:ℝ) ≤ (α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)) :=
    div_nonneg (add_nonneg hα (mul_nonneg (by linarith) hβ)) (Real.sqrt_nonneg _)
  have hcher := gaussianTail_chernoff ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2))) harg
  have hsqrt : Real.sqrt (Real.pi/2) / Real.sqrt (2*Real.pi) = 1/2 := by
    rw [← Real.sqrt_div (by positivity : (0:ℝ) ≤ Real.pi/2) (2*Real.pi),
      show (Real.pi/2) / (2*Real.pi) = (1/2)^2 by field_simp [Real.pi_ne_zero],
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]
  have htail : gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
      / Real.sqrt (2*Real.pi)
      ≤ (1/2) * Real.exp (-((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2) := by
    calc gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
          / Real.sqrt (2*Real.pi)
        ≤ (Real.sqrt (Real.pi/2)
          * Real.exp (-((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2))
          / Real.sqrt (2*Real.pi) :=
          div_le_div_of_nonneg_right hcher
            (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*Real.pi)).le
      _ = (1/2) * Real.exp (-((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2) := by
          rw [show Real.sqrt (Real.pi/2)
              * Real.exp (-((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2)
              / Real.sqrt (2*Real.pi)
            = (Real.sqrt (Real.pi/2) / Real.sqrt (2*Real.pi))
              * Real.exp (-((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2) by ring,
            hsqrt]
  have htsq : ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2
      = (α + (r+1)*β)^2/(4*(r+1)*(r+2)) := by
    rw [div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*(r+1)*(r+2))]
    field_simp [hL.ne', hS.ne']
    ring
  have hid : (α-β)^2/(4*(r+2)) + (α + (r+1)*β)^2/(4*(r+1)*(r+2))
      = α^2/(4*(r+1)) + β^2/4 := by
    field_simp [hL.ne', hS.ne']
    ring
  calc heatKernel (r+2) (α-β)
        * (gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
          / Real.sqrt (2*Real.pi))
      = (4*Real.pi*(r+2))^(-1/2 : ℝ) * Real.exp (-(α-β)^2/(4*(r+2)))
          * (gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
            / Real.sqrt (2*Real.pi)) := by unfold heatKernel; rfl
    _ ≤ (4*Real.pi*(r+2))^(-1/2 : ℝ) * Real.exp (-(α-β)^2/(4*(r+2)))
          * ((1/2) * Real.exp (-((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2)) :=
        mul_le_mul_of_nonneg_left htail
          (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by positivity) hS.le) _)
            (Real.exp_pos _).le)
    _ = (1/2) * (4*Real.pi*(r+2))^(-1/2 : ℝ)
          * Real.exp (-(α-β)^2/(4*(r+2)) + -((α + (r+1)*β)^2/(4*(r+1)*(r+2)))) := by
        have h2 : -((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2
            = -((α + (r+1)*β)^2/(4*(r+1)*(r+2))) := by
          rw [show -((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2
              = -(((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2) by ring, htsq]
        rw [h2]
        rw [show (4*Real.pi*(r+2))^(-1/2 : ℝ) * Real.exp (-(α-β)^2/(4*(r+2)))
            * ((1/2) * Real.exp (-((α + (r+1)*β)^2/(4*(r+1)*(r+2)))))
          = (1/2) * (4*Real.pi*(r+2))^(-1/2 : ℝ)
            * (Real.exp (-(α-β)^2/(4*(r+2)))
              * Real.exp (-((α + (r+1)*β)^2/(4*(r+1)*(r+2))))) by ring]
        rw [← Real.exp_add]
    _ = ((4*Real.pi)^(-1/2 : ℝ) / 2) * (r+2)^(-1/2 : ℝ)
          * Real.exp (-α^2/(4*(r+1)) - β^2/4) := by
        have hexp : Real.exp (-(α-β)^2/(4*(r+2)) + -((α + (r+1)*β)^2/(4*(r+1)*(r+2))))
            = Real.exp (-α^2/(4*(r+1)) - β^2/4) := by
          congr 1
          have h2 : -(α-β)^2/(4*(r+2)) + -((α + (r+1)*β)^2/(4*(r+1)*(r+2)))
              = -((α-β)^2/(4*(r+2)) + (α + (r+1)*β)^2/(4*(r+1)*(r+2))) := by ring
          rw [h2, hid]
          ring
        rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4*Real.pi) hS.le, hexp]
        ring

/-! ### B5: the `Kbound` Chernoff bound and the `γ`-integration -/

/-- **B5a** (the paper's bound on `K`): for `α, γ ≥ 0`,
`p_{L}(γ−α)·Φ(−(rα+γ)/√(2rL)) ≤ C·L^{−1/2}·e^{−α²/4−γ²/(4r)}` with `L = r+1`.
Chernoff plus the exact identity
`(γ−α)²/(4L) + (rα+γ)²/(4rL) = α²/4 + γ²/(4r)` (`field_simp; ring`). -/
theorem frI2_Kbound (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α γ : ℝ}, 0 ≤ α → 0 ≤ γ →
      heatKernel (r+1) (γ-α)
        * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
        ≤ C * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4 - γ^2/(4*r)) := by
  have hL : (0:ℝ) < r + 1 := by linarith
  refine ⟨(4*Real.pi)^(-1/2 : ℝ) / 2, by positivity, ?_⟩
  intro α γ hα hγ
  have harg : (0:ℝ) ≤ (r*α+γ)/Real.sqrt (2*r*(r+1)) :=
    div_nonneg (add_nonneg (mul_nonneg hr.le hα) hγ) (Real.sqrt_nonneg _)
  have hcher := gaussianTail_chernoff ((r*α+γ)/Real.sqrt (2*r*(r+1))) harg
  have hsqrt : Real.sqrt (Real.pi/2) / Real.sqrt (2*Real.pi) = 1/2 := by
    rw [← Real.sqrt_div (by positivity : (0:ℝ) ≤ Real.pi/2) (2*Real.pi),
      show (Real.pi/2) / (2*Real.pi) = (1/2)^2 by field_simp [Real.pi_ne_zero],
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]
  have htail : gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1)))
      / Real.sqrt (2*Real.pi)
      ≤ (1/2) * Real.exp (-((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2) := by
    calc gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi)
        ≤ (Real.sqrt (Real.pi/2)
          * Real.exp (-((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2)) / Real.sqrt (2*Real.pi) :=
          div_le_div_of_nonneg_right hcher
            (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*Real.pi)).le
      _ = (1/2) * Real.exp (-((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2) := by
          rw [show Real.sqrt (Real.pi/2)
              * Real.exp (-((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2) / Real.sqrt (2*Real.pi)
            = (Real.sqrt (Real.pi/2) / Real.sqrt (2*Real.pi))
              * Real.exp (-((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2) by ring, hsqrt]
  have htsq : ((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2 = (r*α+γ)^2/(4*r*(r+1)) := by
    rw [div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*r*(r+1))]
    field_simp [hr.ne', hL.ne']
    ring
  have hid : (γ-α)^2/(4*(r+1)) + (r*α+γ)^2/(4*r*(r+1)) = α^2/4 + γ^2/(4*r) := by
    field_simp [hr.ne', hL.ne']
    ring
  calc heatKernel (r+1) (γ-α)
        * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
      = (4*Real.pi*(r+1))^(-1/2 : ℝ) * Real.exp (-(γ-α)^2/(4*(r+1)))
          * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1)))
            / Real.sqrt (2*Real.pi)) := by
        unfold heatKernel
        rfl
    _ ≤ (4*Real.pi*(r+1))^(-1/2 : ℝ) * Real.exp (-(γ-α)^2/(4*(r+1)))
          * ((1/2) * Real.exp (-((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2)) :=
        mul_le_mul_of_nonneg_left htail
          (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by positivity) hL.le) _)
            (Real.exp_pos _).le)
    _ = (1/2) * (4*Real.pi*(r+1))^(-1/2 : ℝ)
          * Real.exp (-(γ-α)^2/(4*(r+1)) + -((r*α+γ)^2/(4*r*(r+1)))) := by
        have h2 : -((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2
            = -((r*α+γ)^2/(4*r*(r+1))) := by
          rw [show -((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2
              = -(((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2) by ring, htsq]
        rw [h2]
        rw [show (4*Real.pi*(r+1))^(-1/2 : ℝ) * Real.exp (-(γ-α)^2/(4*(r+1)))
            * ((1/2) * Real.exp (-((r*α+γ)^2/(4*r*(r+1)))))
          = (1/2) * (4*Real.pi*(r+1))^(-1/2 : ℝ)
            * (Real.exp (-(γ-α)^2/(4*(r+1))) * Real.exp (-((r*α+γ)^2/(4*r*(r+1))))) by ring]
        rw [← Real.exp_add]
    _ = ((4*Real.pi)^(-1/2 : ℝ) / 2) * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4 - γ^2/(4*r)) := by
        have hexp : Real.exp (-(γ-α)^2/(4*(r+1)) + -((r*α+γ)^2/(4*r*(r+1))))
            = Real.exp (-α^2/4 - γ^2/(4*r)) := by
          congr 1
          have h2 : -(γ-α)^2/(4*(r+1)) + -((r*α+γ)^2/(4*r*(r+1)))
              = -((γ-α)^2/(4*(r+1)) + (r*α+γ)^2/(4*r*(r+1))) := by ring
          rw [h2, hid]
          ring
        rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4*Real.pi) hL.le, hexp]
        ring

/-- **B5** (the paper's `γ`-integration, with its prefactor): for
`α, β ≥ 0`, the `γ`-integrated I₂ inner factor is `O(e^{−(α²+β²)/4})`.

The route is the paper's: `frI2_Kbound`, then
`heatKernel 1 (γ+β) = (4π)^{−1/2}e^{−(γ+β)²/4}`, the completed square
`γ²/(4r) + (γ+β)²/4 = (L/(4r))(γ + rβ/L)² + β²/(4L)`, the affine
substitution `u = √(L/4r)(γ + rβ/L)` (shift by `integral_Ioi_add_const`, scale
by `integral_comp_mul_left_Ioi`), the proved `gaussian_tail_std_sq_bound` with
`(1+x)⁻¹ ≤ 1`, `β²/(4L) + rβ²/(4L) = β²/4`, and the
prefactor absorption `L^{−1/2}√(r/L) = √r/(r+1) ≤ 1`. -/
theorem frI2_gamma_int_le (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : ℝ}, 0 ≤ α → 0 ≤ β →
      ∫ γ in Set.Ioi 0, heatKernel (r+1) (γ-α)
          * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
          * heatKernel 1 (γ+β)
        ≤ C * Real.exp (-(α^2+β^2)/4) := by
  have hL : (0:ℝ) < r + 1 := by linarith
  obtain ⟨CK, hCKpos, hCK⟩ := frI2_Kbound hr
  obtain ⟨Ct, hCtpos, hCt⟩ := gaussian_tail_std_sq_bound
  refine ⟨2 * CK * Ct * (4*Real.pi)^(-1/2 : ℝ), by positivity, ?_⟩
  intro α β hα hβ
  -- the completed square
  have hsq : ∀ γ : ℝ, γ^2/(4*r) + (γ+β)^2/4
      = ((r+1)/(4*r))*(γ + r*β/(r+1))^2 + β^2/(4*(r+1)) := by
    intro γ
    field_simp [hr.ne', hL.ne']
    ring
  -- the pointwise factorization of the `γ`-dependent Gaussian product
  have hpt : ∀ γ : ℝ, Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)
      = (4*Real.pi)^(-1/2 : ℝ) * (Real.exp (-β^2/(4*(r+1)))
        * Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2)) := by
    intro γ
    have hk1 : heatKernel 1 (γ+β)
        = (4*Real.pi)^(-1/2 : ℝ) * Real.exp (-(γ+β)^2/4) := by
      unfold heatKernel
      rw [show (4:ℝ)*Real.pi*1 = 4*Real.pi by ring]
      congr 1
      ring
    rw [hk1,
      show Real.exp (-γ^2/(4*r)) * ((4*Real.pi)^(-1/2 : ℝ) * Real.exp (-(γ+β)^2/4))
        = (4*Real.pi)^(-1/2 : ℝ)
          * (Real.exp (-γ^2/(4*r)) * Real.exp (-(γ+β)^2/4)) by ring,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    congr 1
    have h2 := hsq γ
    rw [show -β^2/(4*(r+1)) + -((r+1)/(4*r))*(γ + r*β/(r+1))^2
        = -(γ^2/(4*r) + (γ+β)^2/4) by rw [h2]; ring]
    ring
  -- the `γ`-integral: shift then scale
  set cc : ℝ := Real.sqrt ((r+1)/(4*r)) with hcc
  have hccpos : 0 < cc := Real.sqrt_pos.mpr (div_pos hL (by linarith))
  have hcc2 : cc^2 = (r+1)/(4*r) := Real.sq_sqrt (div_nonneg hL.le (by positivity))
  have hstep1 : ∫ γ in Set.Ioi 0, Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)
      = (4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1)))
        * ∫ γ in Set.Ioi 0, Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro γ _
    show Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)
      = (4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1)))
        * Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2)
    rw [hpt γ]
    ring
  have hstep2 : ∫ γ in Set.Ioi 0, Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2)
      = ∫ v in Set.Ioi (r*β/(r+1)), Real.exp (-((r+1)/(4*r))*v^2) := by
    have h := AiryConj.integral_Ioi_add_const
      (fun v => Real.exp (-((r+1)/(4*r))*v^2)) 0 (r*β/(r+1))
    rw [zero_add] at h
    exact h
  have hstep3 : ∫ v in Set.Ioi (r*β/(r+1)), Real.exp (-((r+1)/(4*r))*v^2)
      = cc⁻¹ * ∫ u in Set.Ioi (cc * (r*β/(r+1))), Real.exp (-u^2) := by
    have hcongr : (fun v : ℝ => Real.exp (-((r+1)/(4*r))*v^2))
        = fun v => Real.exp (-(cc * v)^2) := by
      funext v
      congr 1
      rw [mul_pow, hcc2]
      ring
    rw [hcongr]
    have h := MeasureTheory.integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u^2))
      (r*β/(r+1)) hccpos
    rw [smul_eq_mul] at h
    exact h
  -- the cc⁻¹ prefactor (= 2√(r/L))
  have hccinv : cc⁻¹ = 2 * Real.sqrt (r/(r+1)) := by
    rw [hcc]
    have h1 : Real.sqrt ((r+1)/(4*r)) = Real.sqrt (r+1)/(2 * Real.sqrt r) := by
      rw [Real.sqrt_div hL.le]
      congr 1
      rw [show (4:ℝ)*r = 2^2 * r by ring, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2^2),
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [h1, inv_div, Real.sqrt_div hr.le]
    ring
  -- the tail bound with `(1+x)⁻¹ ≤ 1`
  have hx : (0:ℝ) ≤ cc * (r*β/(r+1)) :=
    mul_nonneg hccpos.le (div_nonneg (mul_nonneg hr.le hβ) hL.le)
  have hx2 : (cc * (r*β/(r+1)))^2 = r*β^2/(4*(r+1)) := by
    rw [mul_pow, hcc2]
    field_simp [hr.ne', hL.ne']
  have htail : ∫ u in Set.Ioi (cc * (r*β/(r+1))), Real.exp (-u^2)
      ≤ Ct * Real.exp (-(r*β^2/(4*(r+1)))) := by
    calc ∫ u in Set.Ioi (cc * (r*β/(r+1))), Real.exp (-u^2)
        ≤ Ct * (1 + cc * (r*β/(r+1)))⁻¹ * Real.exp (-(cc * (r*β/(r+1)))^2) :=
          hCt _ hx
      _ ≤ Ct * 1 * Real.exp (-(cc * (r*β/(r+1)))^2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_left _ hCtpos.le
          exact inv_le_one_of_one_le₀ (by linarith [hx])
      _ = Ct * Real.exp (-(r*β^2/(4*(r+1)))) := by
          rw [mul_one]
          congr 1
          rw [hx2]
  -- the `γ`-integral bound, assembled
  have hgamma : ∫ γ in Set.Ioi 0, Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)
      ≤ (4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1))) * cc⁻¹
        * (Ct * Real.exp (-(r*β^2/(4*(r+1))))) := by
    rw [hstep1, hstep2, hstep3]
    rw [show (4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1))) * cc⁻¹
        * (Ct * Real.exp (-(r*β^2/(4*(r+1)))))
        = ((4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1))))
          * (cc⁻¹ * (Ct * Real.exp (-(r*β^2/(4*(r+1)))))) by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr hccpos.le)
  -- integrability inputs for the `γ`-level monotonicity
  have hGint0 : Integrable fun γ : ℝ => Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2) := by
    have h0 := integrable_exp_neg_mul_sq (div_pos hL (by linarith) : (0:ℝ) < (r+1)/(4*r))
    exact h0.comp_add_right (r*β/(r+1))
  have hRHS : IntegrableOn (fun γ : ℝ => (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4))
      * (Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β))) (Set.Ioi 0) := by
    have h1 : Integrable fun γ : ℝ => Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β) := by
      have hcong : (fun γ : ℝ => Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β))
          = fun γ => ((4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1))))
            * Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2) := by
        funext γ
        show Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)
          = ((4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1))))
            * Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2)
        rw [hpt γ]
        ring
      rw [hcong]
      exact hGint0.const_mul _
    exact (h1.const_mul _).integrableOn
  have hmono : Antitone fun γ : ℝ =>
      gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) := by
    intro a b hab
    apply gaussianTail_mono (by norm_num : (0:ℝ) < 1/2)
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    linarith [hab]
  have hmeas : Measurable fun γ : ℝ => heatKernel (r+1) (γ-α)
      * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
      * heatKernel 1 (γ+β) :=
    (((continuous_heatKernel (r+1)).comp
      (continuous_id.sub continuous_const)).measurable.mul
      (hmono.measurable.div_const _)).mul
      ((continuous_heatKernel 1).comp (continuous_id.add continuous_const)).measurable
  -- the pointwise bound from `frI2_Kbound`
  have hptbound : ∀ γ ∈ Set.Ioi 0, heatKernel (r+1) (γ-α)
      * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
      * heatKernel 1 (γ+β)
      ≤ (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4))
        * (Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)) := by
    intro γ hγ
    have hγ0 : (0:ℝ) ≤ γ := (Set.mem_Ioi.mp hγ).le
    have h2 := hCK hα hγ0
    have h3 := mul_le_mul_of_nonneg_right h2 (heatKernel_pos one_pos (γ+β)).le
    calc heatKernel (r+1) (γ-α)
          * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
          * heatKernel 1 (γ+β)
        ≤ (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4 - γ^2/(4*r)))
          * heatKernel 1 (γ+β) := h3
      _ = (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4))
          * (Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)) := by
          rw [show Real.exp (-α^2/4 - γ^2/(4*r))
              = Real.exp (-α^2/4) * Real.exp (-γ^2/(4*r)) by
            rw [← Real.exp_add]
            congr 1
            ring]
          ring
  have hLHS : IntegrableOn (fun γ : ℝ => heatKernel (r+1) (γ-α)
      * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
      * heatKernel 1 (γ+β)) (Set.Ioi 0) := by
    rw [IntegrableOn]
    apply hRHS.mono' hmeas.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with γ hγ
    have hgT : (0:ℝ) ≤ gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) := by
      unfold gaussianTail
      apply setIntegral_nonneg measurableSet_Ioi
      intro d _
      exact (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg
      (heatKernel_pos hL _).le (div_nonneg hgT (Real.sqrt_nonneg _)))
      (heatKernel_pos one_pos _).le)]
    exact hptbound γ hγ
  -- the prefactor absorption `L^{−1/2}√(r/L) = √r/(r+1) ≤ 1`
  have hsqrtle : (r+1)^(-1/2 : ℝ) * Real.sqrt (r/(r+1)) ≤ 1 := by
    have h1 : (r+1)^(-1/2 : ℝ) = (Real.sqrt (r+1))⁻¹ := by
      rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by norm_num, Real.rpow_neg hL.le,
        Real.sqrt_eq_rpow]
    have h2 : Real.sqrt (r/(r+1)) = Real.sqrt r / Real.sqrt (r+1) :=
      Real.sqrt_div hr.le _
    have h4 : Real.sqrt r ≤ r + 1 := by
      have h5 : Real.sqrt r ≤ Real.sqrt ((r+1)^2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg r, hr])
      rwa [Real.sqrt_sq hL.le] at h5
    have h3 : (Real.sqrt (r+1))⁻¹ * (Real.sqrt r / Real.sqrt (r+1))
        = Real.sqrt r / (r+1) := by
      have h6 : (Real.sqrt (r+1))⁻¹ * (Real.sqrt r * (Real.sqrt (r+1))⁻¹)
          = Real.sqrt r * (r+1)⁻¹ := by
        rw [show (Real.sqrt (r+1))⁻¹ * (Real.sqrt r * (Real.sqrt (r+1))⁻¹)
            = Real.sqrt r * ((Real.sqrt (r+1))⁻¹ * (Real.sqrt (r+1))⁻¹) by ring]
        rw [← mul_inv, Real.mul_self_sqrt hL.le]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact h6
    calc (r+1)^(-1/2 : ℝ) * Real.sqrt (r/(r+1))
        = Real.sqrt r / (r+1) := by rw [h1, h2, h3]
      _ ≤ 1 := (div_le_one hL).mpr h4
  have hC0 : (0:ℝ) ≤ 2 * CK * Ct * (4*Real.pi)^(-1/2 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCKpos.le) hCtpos.le)
      (Real.rpow_nonneg (by positivity) _)
  -- the full assembly
  calc ∫ γ in Set.Ioi 0, heatKernel (r+1) (γ-α)
          * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
          * heatKernel 1 (γ+β)
      ≤ ∫ γ in Set.Ioi 0, (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4))
          * (Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)) :=
        setIntegral_mono_on hLHS hRHS measurableSet_Ioi hptbound
    _ = (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4))
          * ∫ γ in Set.Ioi 0, Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β) :=
        integral_const_mul _ _
    _ ≤ (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4))
          * ((4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1))) * cc⁻¹
            * (Ct * Real.exp (-(r*β^2/(4*(r+1)))))) :=
        mul_le_mul_of_nonneg_left hgamma (by positivity)
    _ = (2 * CK * Ct * (4*Real.pi)^(-1/2 : ℝ))
          * ((r+1)^(-1/2 : ℝ) * Real.sqrt (r/(r+1)))
          * (Real.exp (-α^2/4) * Real.exp (-β^2/4)) := by
        rw [hccinv]
        rw [show CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4)
            * ((4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1)))
              * (2 * Real.sqrt (r/(r+1))) * (Ct * Real.exp (-(r*β^2/(4*(r+1))))))
          = (2 * CK * Ct * (4*Real.pi)^(-1/2 : ℝ)) * ((r+1)^(-1/2 : ℝ)
              * Real.sqrt (r/(r+1)))
            * (Real.exp (-α^2/4) * (Real.exp (-β^2/(4*(r+1)))
              * Real.exp (-(r*β^2/(4*(r+1)))))) by ring]
        rw [show Real.exp (-β^2/(4*(r+1))) * Real.exp (-(r*β^2/(4*(r+1))))
            = Real.exp (-β^2/4) by
          rw [← Real.exp_add]
          congr 1
          field_simp [hL.ne', show (4:ℝ)*(r+1) ≠ 0 from mul_ne_zero (by norm_num) hL.ne']
          ring]
    _ ≤ (2 * CK * Ct * (4*Real.pi)^(-1/2 : ℝ)) * 1
          * (Real.exp (-α^2/4) * Real.exp (-β^2/4)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hsqrtle hC0
    _ = (2 * CK * Ct * (4*Real.pi)^(-1/2 : ℝ)) * Real.exp (-(α^2+β^2)/4) := by
        rw [mul_one, ← Real.exp_add]
        congr 1
        ring

/-! ### The `J_M(r) = O_χ(a³)` absorption helper -/

/-- **`saddleJ_le_rpow`** (the absorption behind the
single-term form of the paper's FR-sector bound): in the subcritical range `r ≤ χa`
with `a = √(2M)`, `J_M(r) ≤ C_χ·(2M)^{3/2}` (`= C_χ·a³`).
From `2M + r² ≤ (1+χ²)·(2M)` (so `(2M+r²)^{3/2} ≤ (1+χ²)^{3/2}(2M)^{3/2}`),
`2Mr ≤ χa·a² = χ·(2M)^{3/2}`, and `r³ ≤ χ³a³ = χ³(2M)^{3/2}`. -/
theorem saddleJ_le_rpow {χ : ℝ} (hχ0 : 0 < χ) :
    ∃ C : ℝ, ∀ {M r : ℝ}, 1 ≤ M → 1 ≤ r → r ≤ χ * Real.sqrt (2*M) →
      saddleJ M r ≤ C * (2*M)^(3/2 : ℝ) := by
  refine ⟨(2/3)*(1+χ^2)^(3/2 : ℝ) + χ + (2/3)*χ^3, ?_⟩
  intro M r hM hr hradm
  have hM0 : (0:ℝ) ≤ 2*M := by linarith
  set a := Real.sqrt (2*M) with ha
  have ha0 : (0:ℝ) ≤ a := Real.sqrt_nonneg _
  have ha2 : a^2 = 2*M := Real.sq_sqrt hM0
  have ha1 : (1:ℝ) ≤ a := by
    have h2 : (1:ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    have h1 : Real.sqrt 2 ≤ a := by
      rw [ha]
      apply Real.sqrt_le_sqrt
      linarith
    linarith
  -- `(2M)^{3/2} = a³` (the `saddleF_min_eq` rpow pattern)
  have ha32 : (2*M)^(3/2 : ℝ) = a^3 := by
    rw [← ha2, ← Real.rpow_natCast a 2, ← Real.rpow_mul ha0,
      show ((2:ℕ):ℝ)*(3/2) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hbound1 : (2*M + r^2)^(3/2 : ℝ) ≤ (1+χ^2)^(3/2 : ℝ) * (2*M)^(3/2 : ℝ) := by
    have hr2 : r^2 ≤ χ^2 * (2*M) := by
      have h1 : r^2 ≤ (χ*a)^2 := pow_le_pow_left₀ (by linarith) hradm 2
      rwa [mul_pow, ha2] at h1
    have h1 : 2*M + r^2 ≤ (1+χ^2) * (2*M) := by nlinarith [hr2, hM0]
    calc (2*M + r^2)^(3/2 : ℝ) ≤ ((1+χ^2) * (2*M))^(3/2 : ℝ) :=
        Real.rpow_le_rpow (add_nonneg hM0 (sq_nonneg r)) h1 (by norm_num)
      _ = (1+χ^2)^(3/2 : ℝ) * (2*M)^(3/2 : ℝ) :=
        Real.mul_rpow (by positivity) hM0
  have hbound2 : 2*M*r ≤ χ * (2*M)^(3/2 : ℝ) := by
    have h2 : 2*M*r ≤ 2*M * (χ*a) := mul_le_mul_of_nonneg_left hradm hM0
    have h3 : 2*M * (χ*a) = χ * a^3 := by
      rw [← ha2]
      ring
    calc 2*M*r ≤ 2*M * (χ*a) := h2
      _ = χ * (2*M)^(3/2 : ℝ) := by rw [h3, ha32]
  have hbound3 : r^3 ≤ χ^3 * (2*M)^(3/2 : ℝ) := by
    have h2 : r^3 ≤ (χ*a)^3 := pow_le_pow_left₀ (by linarith) hradm 3
    calc r^3 ≤ (χ*a)^3 := h2
      _ = χ^3 * a^3 := mul_pow _ _ _
      _ = χ^3 * (2*M)^(3/2 : ℝ) := by rw [ha32]
  unfold saddleJ
  have hX : (0:ℝ) ≤ (2*M)^(3/2 : ℝ) := Real.rpow_nonneg hM0 _
  nlinarith [hbound1, hbound2, hbound3, hX]

end AiryTwoInt
