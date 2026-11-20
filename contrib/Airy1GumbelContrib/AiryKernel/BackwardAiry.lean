/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryIdentity
import Airy1GumbelContrib.Airy.AiryLaplaceFull
import Airy1GumbelContrib.Gaussian.MillsRatio
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # The backward Airy kernel and heat–Airy convolution identities

Part of the Airy kernel layer (`AiryKernel/`) of the Airy1–Gumbel contrib library: the scalar
analysis behind the paper's backward-kernel representation, i.e. Quastel–Remenik [Prop 1.2 / (1.9)].  With the heat kernel

  `heatKernel T v = (4πT)^{-1/2} exp(-v²/(4T))`     (`T > 0`)

and the **backward Airy kernel**

  `backwardAiry T s = exp(-(2/3) T³ - T s) · Ai(s + T²)`,

(which is the paper's `g_T(s)`; the backward heat operator applied to the Airy
initial profile is `(P_{-T} B_0)(z, y) = backwardAiry T (z + y)`), we prove:

* `backwardAiry` solves the **backward heat equation**
  `∂_T g_T = -∂²_s g_T` (`backwardAiry_pde`), while `heatKernel` solves the forward
  heat equation (`heatKernel_heat_eq`);
* **(1)** `heat_airy_conv`: the heat–Airy convolution identity
  `∫ s, heatKernel T (x - s) * backwardAiry T s = airyAiReal x` for `0 < T`,
  proved by showing the convolution is constant in `T` (differentiate under the
  integral, use the two heat equations, integrate by parts twice) and evaluating
  the `T → 0⁺` mollifier limit;
* **(2)** `heat_airy_conv_moment`: the first-moment companion
  `∫ s, (A - s) heatKernel T (A - s) backwardAiry T s = -(2T) (deriv airyAiReal) A`,
  by differentiating (1) in `x`;
* **(3)** `heat_airy_conv_tail`: the Gaussian-tail companion
  `∫ s, gaussianTail T (A - s) * backwardAiry T s = √(4πT) ∫ u in Ioi A, airyAiReal u`,
  by integrating (1) over `u ∈ (A, ∞)` (one Fubini swap);
* **(4)** `heat_airy_conv_backward`: (1) restated in the `(P_{-T} B_0)` form.

## Proof outline for (1)

For `F(T) = ∫ s, heatKernel T (x-s) * backwardAiry T s`:
(i) the integral converges absolutely since the Gaussian kills the `e^{T|s|}` growth of
    `backwardAiry` at `-∞`;
(ii) `F` is differentiable on `(0, ∞)` with `deriv F = 0`: differentiation under the
    integral (dominated by a Gaussian×polynomial×exponential envelope, uniform for `T`
    in compact subintervals) turns `∂_T F` into `∫ [∂²_s p · g - p · ∂²_s g] ds = 0`
    by two integrations by parts on the line (`integral_derivTwo_mul_eq_mul_derivTwo`);
(iii) `F(T) → Ai(x)` as `T → 0⁺` by the mollifier argument
    `F(T) - Ai(x) = ∫ p_T(v) (g_T(x-v) - Ai x) dv`, splitting `|v| ≤ δ` (uniform
    continuity of `g` on compacts) against `|v| > δ` (Gaussian tails, via the Gaussian
    Mills bound (`Gaussian/`));
(iv) `F` is then the constant `Ai(x)`.

## Reference

J. Quastel and D. Remenik, *How flat is flat in random interface growth?*,
Prop. 1.2 and Eq. (1.9).
-/

open Asymptotics Filter MeasureTheory Set

open scoped Asymptotics Topology

/-! ## The heat kernel

Basic calculus of `heatKernel T v = (4πT)^{-1/2} exp(-v²/(4T))`: positivity,
normalization (`integral_heatKernel`), and the forward heat equation
(`heatKernel_heat_eq`). -/

section HeatKernel

/-- The heat kernel at temperature `T`: `(4πT)^{-1/2} exp(-v²/(4T))`.  Theorems are
stated for `0 < T`. -/
noncomputable def heatKernel (T v : ℝ) : ℝ :=
  (4 * Real.pi * T)^(-1/2 : ℝ) * Real.exp (-v^2 / (4 * T))

/-- The heat kernel is positive for `0 < T`. -/
theorem heatKernel_pos (hT : 0 < T) (v : ℝ) : 0 < heatKernel T v := by
  unfold heatKernel
  apply mul_pos _ (Real.exp_pos _)
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The heat kernel is nonnegative for `0 < T`. -/
theorem heatKernel_nonneg (hT : 0 < T) (v : ℝ) : 0 ≤ heatKernel T v :=
  (heatKernel_pos hT v).le

/-- `v ↦ heatKernel T v` is continuous. -/
theorem continuous_heatKernel (T : ℝ) : Continuous fun v : ℝ => heatKernel T v := by
  unfold heatKernel
  exact continuous_const.mul ((Real.continuous_exp.comp
    (((continuous_pow 2).neg).div_const (4 * T))))

/-- The temperature derivative of the heat kernel, in factored form:
`∂_T heatKernel T v = (-1/(2T) + v²/(4T²)) · heatKernel T v`. -/
theorem hasDerivAt_heatKernel_T (hT : 0 < T) (v : ℝ) :
    HasDerivAt (fun T : ℝ => heatKernel T v)
      ((-1/(2*T) + v^2/(4*T^2)) * heatKernel T v) T := by
  have h4πT : (0:ℝ) < 4 * Real.pi * T := by positivity
  have hT' : T ≠ 0 := hT.ne'
  have h1 : HasDerivAt (fun T : ℝ => (4 * Real.pi * T)^(-1/2 : ℝ))
      ((4 * Real.pi * 1) * (-1/2) * (4 * Real.pi * T)^(-1/2 - 1 : ℝ)) T :=
    ((hasDerivAt_id' T).const_mul (4 * Real.pi)).rpow_const (Or.inl h4πT.ne')
  have h2 : HasDerivAt (fun T : ℝ => Real.exp (-v^2/(4*T)))
      (Real.exp (-v^2/(4*T)) * (v^2/(4*T^2))) T := by
    have h := (Real.hasDerivAt_exp (-v^2/(4*T))).comp T
      ((hasDerivAt_const T (-v^2)).div ((hasDerivAt_id' T).const_mul 4)
        (by positivity : (4 : ℝ) * T ≠ 0))
    convert h using 1
    · ext T'
      rfl
    · field_simp
      ring
  have h := h1.mul h2
  convert h using 1
  · ext T'
    simp only [heatKernel, Pi.mul_apply]
  · unfold heatKernel
    rw [show (4 * Real.pi * T)^(-1/2 - 1 : ℝ)
        = (4 * Real.pi * T)^(-1/2 : ℝ) * (4 * Real.pi * T)⁻¹ by
      rw [show (-1/2 - 1 : ℝ) = -1/2 + (-1 : ℝ) by ring,
        Real.rpow_add h4πT, Real.rpow_neg_one]]
    set X := (4 * Real.pi * T)^(-1/2 : ℝ)
    field_simp

/-- The spatial derivative of the heat kernel:
`∂_v heatKernel T v = -(v/(2T)) · heatKernel T v`. -/
theorem hasDerivAt_heatKernel_v (hT : 0 < T) (v : ℝ) :
    HasDerivAt (heatKernel T) (-(v/(2*T)) * heatKernel T v) v := by
  have h2 : HasDerivAt (fun v : ℝ => Real.exp (-v^2/(4*T)))
      (Real.exp (-v^2/(4*T)) * (-(v/(2*T)))) v := by
    have h := (Real.hasDerivAt_exp (-v^2/(4*T))).comp v
      (((hasDerivAt_pow 2 v).neg).div_const (4*T))
    convert h using 1
    · ext v'
      rfl
    · field_simp
      ring
  have h := h2.const_mul ((4 * Real.pi * T)^(-1/2 : ℝ))
  convert h using 1
  · ext v'
    rfl
  · unfold heatKernel
    ring

/-- The second spatial derivative of the heat kernel:
`∂²_v heatKernel T v = (v²/(4T²) - 1/(2T)) · heatKernel T v`. -/
theorem hasDerivAt_deriv_heatKernel_v (hT : 0 < T) (v : ℝ) :
    HasDerivAt (deriv (heatKernel T))
      ((v^2/(4*T^2) - 1/(2*T)) * heatKernel T v) v := by
  have hder : deriv (heatKernel T)
      = fun v : ℝ => -(v/(2*T)) * heatKernel T v :=
    funext fun v => (hasDerivAt_heatKernel_v hT v).deriv
  have h2 : HasDerivAt (fun v : ℝ => (-(v/(2*T))) * heatKernel T v)
      ((v^2/(4*T^2) - 1/(2*T)) * heatKernel T v) v := by
    have h1 : HasDerivAt (fun v : ℝ => -(v/(2*T))) (-(1/(2*T))) v :=
      ((hasDerivAt_id' v).div_const (2*T)).neg
    have h := h1.mul (hasDerivAt_heatKernel_v hT v)
    convert h using 1
    unfold heatKernel
    set X := (4 * Real.pi * T)^(-1/2 : ℝ)
    field_simp
    ring
  rw [hder]
  exact h2

/-- **The heat equation**: `∂_T heatKernel = ∂²_v heatKernel` for `0 < T`. -/
theorem heatKernel_heat_eq (hT : 0 < T) (v : ℝ) :
    deriv (heatKernel · v) T = iteratedDeriv 2 (heatKernel T) v := by
  rw [(hasDerivAt_heatKernel_T hT v).deriv, iteratedDeriv_succ, iteratedDeriv_one,
    (hasDerivAt_deriv_heatKernel_v hT v).deriv]
  ring_nf

/-- The heat kernel is integrable for `0 < T`. -/
theorem integrable_heatKernel (hT : 0 < T) :
    Integrable fun v : ℝ => heatKernel T v := by
  have h2 : Integrable (fun v : ℝ => (4 * Real.pi * T)^(-1/2 : ℝ)
      * Real.exp (-(4*T)⁻¹ * v^2)) :=
    (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < (4*T)⁻¹)).const_mul _
  convert h2 using 1
  ext v
  unfold heatKernel
  congr 2
  ring

/-- The heat kernel has total mass `1`: `∫ v, heatKernel T v = 1` for `0 < T`. -/
theorem integral_heatKernel (hT : 0 < T) :
    ∫ v : ℝ, heatKernel T v = 1 := by
  have h4πT : (0:ℝ) < 4 * Real.pi * T := by positivity
  have h : (∫ v : ℝ, Real.exp (-v^2/(4*T))) = Real.sqrt (4 * Real.pi * T) := by
    have h1 : (∫ v : ℝ, Real.exp (-(4*T)⁻¹ * v^2))
        = Real.sqrt (Real.pi / (4*T)⁻¹) := integral_gaussian (4*T)⁻¹
    have h2 : (fun v : ℝ => Real.exp (-v^2/(4*T)))
        = fun v => Real.exp (-(4*T)⁻¹ * v^2) := by
      funext v
      congr 1
      ring
    rw [h2, h1]
    congr 1
    field_simp
  unfold heatKernel
  rw [integral_const_mul, h, Real.sqrt_eq_rpow, ← Real.rpow_add h4πT,
    show (-1/2 : ℝ) + 1/2 = 0 by norm_num, Real.rpow_zero]

end HeatKernel

/-! ## Airy function bounds

Auxiliary estimates for `airyAiReal` and its derivative: global boundedness of `Ai`
(`airyAiReal_abs_le`) and the at-most-quadratic growth of `Ai'`
(`deriv_airyAiReal_abs_le`).  Also continuity of `Ai`, `Ai'`, and the Airy ODE in
`HasDerivAt` value form. -/

section AiryBounds

/-- `airyAiReal` is continuous. -/
theorem continuous_airyAiReal : Continuous airyAiReal :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiReal x).continuousAt

/-- `deriv airyAiReal` is continuous. -/
theorem continuous_deriv_airyAiReal : Continuous (deriv airyAiReal) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_deriv_airyAiReal x).continuousAt

/-- The Airy ODE `Ai'' = x · Ai` in `HasDerivAt` value form. -/
theorem hasDerivAt_deriv_airyAiReal' (x : ℝ) :
    HasDerivAt (deriv airyAiReal) (x * airyAiReal x) x := by
  have hval : (deriv (deriv Complex.airyAi) (x : ℂ)).re = x * airyAiReal x := by
    have h2 := iteratedDeriv_two_airyAiReal x
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
      (hasDerivAt_deriv_airyAiReal x).deriv] at h2
    exact h2
  rw [← hval]
  exact hasDerivAt_deriv_airyAiReal x

/-- `Ai` is globally bounded on `ℝ`: it decays on `[1, ∞)` (`airyAiReal_le`), is
bounded on `(-∞, 0]` (`airyAiReal_abs_le_nonpos`), and on the compact middle `[0, 1]`
by continuity. -/
theorem airyAiReal_abs_le : ∃ C : ℝ, ∀ u : ℝ, |airyAiReal u| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := airyAiReal_le
  obtain ⟨C₂, hC₂⟩ := airyAiReal_abs_le_nonpos
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) (continuous_airyAiReal.abs.continuousOn)
  refine ⟨|C₂| + |C₁| + |airyAiReal x₀|, fun u => ?_⟩
  rcases le_total u 0 with hu | hu
  · exact (hC₂ u hu).trans (by
      calc C₂ ≤ |C₂| := le_abs_self _
        _ ≤ |C₂| + |C₁| := le_add_of_nonneg_right (abs_nonneg _)
        _ ≤ |C₂| + |C₁| + |airyAiReal x₀| := le_add_of_nonneg_right (abs_nonneg _))
  · rcases le_total u 1 with hu1 | hu1
    · exact (hmax ⟨hu, hu1⟩).trans (le_add_of_nonneg_left (by positivity))
    · have hAi : airyAiReal u ≤ |C₁| := by
        have hrpow : u^(-1/4 : ℝ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
        have hexp : Real.exp (-(2/3 * u^(3/2 : ℝ))) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          apply neg_nonpos.mpr
          positivity
        have hX : u^(-1/4 : ℝ) * Real.exp (-(2/3 * u^(3/2 : ℝ))) ≤ 1 := by
          calc u^(-1/4 : ℝ) * Real.exp (-(2/3 * u^(3/2 : ℝ)))
              ≤ 1 * 1 := mul_le_mul hrpow hexp (Real.exp_pos _).le zero_le_one
            _ = 1 := mul_one 1
        calc airyAiReal u
            ≤ C₁ * (u^(-1/4 : ℝ) * Real.exp (-(2/3 * u^(3/2 : ℝ)))) := by
              convert hC₁ u hu1 using 1
              ring
          _ ≤ |C₁| * 1 := by
              calc C₁ * (u^(-1/4 : ℝ) * Real.exp (-(2/3 * u^(3/2 : ℝ))))
                  ≤ |C₁| * (u^(-1/4 : ℝ) * Real.exp (-(2/3 * u^(3/2 : ℝ)))) :=
                    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
                _ ≤ |C₁| * 1 := mul_le_mul_of_nonneg_left hX (abs_nonneg _)
          _ = |C₁| := mul_one _
      have hpos : 0 < airyAiReal u := airyAiReal_pos_of_nonneg hu
      rw [abs_of_pos hpos]
      exact hAi.trans (by
        calc |C₁| ≤ |C₂| + |C₁| := le_add_of_nonneg_left (abs_nonneg _)
          _ ≤ |C₂| + |C₁| + |airyAiReal x₀| := le_add_of_nonneg_right (abs_nonneg _))

/-- `Ai'` grows at most quadratically: `|Ai'(u)| ≤ C (1 + u²)`.  By the Airy ODE and
FTC, `Ai'(u) = Ai'(0) + ∫ t in 0..u, t · Ai t dt`, and the integrand is bounded by the
global `Ai` bound. -/
theorem deriv_airyAiReal_abs_le : ∃ C : ℝ, ∀ u : ℝ,
    |deriv airyAiReal u| ≤ C * (1 + u^2) := by
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le
  have hC₀nn : 0 ≤ C₀ := le_trans (abs_nonneg _) (hC₀ 0)
  have hftc : ∀ u : ℝ, deriv airyAiReal u
      = deriv airyAiReal 0 + ∫ t in (0:ℝ)..u, t * airyAiReal t := by
    intro u
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_deriv_airyAiReal' x)
      ((continuous_id.mul continuous_airyAiReal).intervalIntegrable (0:ℝ) u)
    rw [h]
    ring
  refine ⟨|deriv airyAiReal 0| + C₀, fun u => ?_⟩
  rw [hftc u]
  have hbound : |∫ t in (0:ℝ)..u, t * airyAiReal t| ≤ C₀ * u^2 := by
    have hK : ∀ t ∈ Set.uIoc 0 u, ‖t * airyAiReal t‖ ≤ C₀ * |u| := by
      intro t ht
      have ht2 : |t| ≤ |u| := by
        rcases le_total 0 u with hu | hu
        · rw [Set.uIoc_of_le hu] at ht
          rw [abs_of_nonneg ht.1.le, abs_of_nonneg hu]
          exact ht.2
        · rw [Set.uIoc_comm, Set.uIoc_of_le hu] at ht
          rw [abs_of_nonpos ht.2, abs_of_nonpos hu]
          exact (neg_lt_neg ht.1).le
      calc ‖t * airyAiReal t‖ = |t| * |airyAiReal t| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |u| * C₀ := mul_le_mul ht2 (hC₀ t) (abs_nonneg _) (abs_nonneg _)
        _ = C₀ * |u| := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hK
    calc |∫ t in (0:ℝ)..u, t * airyAiReal t|
        = ‖∫ t in (0:ℝ)..u, t * airyAiReal t‖ := (Real.norm_eq_abs _).symm
      _ ≤ (C₀ * |u|) * |u - 0| := h
      _ = C₀ * u^2 := by
          rw [sub_zero, mul_assoc, ← abs_mul, abs_mul_self, ← pow_two]
  calc |deriv airyAiReal 0 + ∫ t in (0:ℝ)..u, t * airyAiReal t|
      ≤ |deriv airyAiReal 0| + |∫ t in (0:ℝ)..u, t * airyAiReal t| := abs_add_le _ _
    _ ≤ |deriv airyAiReal 0| + C₀ * u^2 := add_le_add le_rfl hbound
    _ ≤ (|deriv airyAiReal 0| + C₀) * (1 + u^2) := by
        have e : (|deriv airyAiReal 0| + C₀) * (1 + u^2)
            = |deriv airyAiReal 0| + |deriv airyAiReal 0| * u^2 + C₀ + C₀ * u^2 := by
          ring
        rw [e]
        have h1 : C₀ * u^2 ≤ C₀ * u^2 := le_rfl
        nlinarith [sq_nonneg u, hC₀nn, abs_nonneg (deriv airyAiReal 0)]

end AiryBounds

/-! ## Gaussian-times-exponential envelopes

The domination envelopes used throughout: `s ↦ (1 + s²) · exp(-b(s-m)² + c|s|)` is
integrable and tends to `0` at `±∞` for `0 < b`.  These power every dominated
convergence / differentiation-under-the-integral step below. -/

section Envelopes

/-- `1 + t² ≤ (1 + δ⁻¹) e^{δ t²}` for `0 < δ` (from `1 + x ≤ e^x`). -/
theorem one_add_sq_le_exp {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    1 + t^2 ≤ (1 + δ⁻¹) * Real.exp (δ * t^2) := by
  have h : 1 + δ * t^2 ≤ Real.exp (δ * t^2) := by
    rw [add_comm]
    exact Real.add_one_le_exp _
  have hnn : 0 ≤ δ * t^2 := mul_nonneg hδ.le (sq_nonneg t)
  have ht2 : t^2 ≤ δ⁻¹ * Real.exp (δ * t^2) := by
    have h1 : δ * t^2 ≤ Real.exp (δ * t^2) := le_trans (le_add_of_nonneg_left zero_le_one) h
    calc t^2 = δ⁻¹ * (δ * t^2) := by field_simp
      _ ≤ δ⁻¹ * Real.exp (δ * t^2) := mul_le_mul_of_nonneg_left h1 (by positivity)
  calc 1 + t^2 ≤ Real.exp (δ * t^2) + δ⁻¹ * Real.exp (δ * t^2) :=
        add_le_add (by linarith) ht2
    _ = (1 + δ⁻¹) * Real.exp (δ * t^2) := by ring

/-- Polynomials are beaten by exponentials: `|s|^k ≤ (k!/c^k) e^{c|s|}` for `0 < c`. -/
theorem abs_pow_le_factorial_mul_exp (k : ℕ) {c : ℝ} (hc : 0 < c) (s : ℝ) :
    |s|^k ≤ (k.factorial : ℝ) / c^k * Real.exp (c * |s|) := by
  have hck : (0:ℝ) < c^k := by positivity
  have hfact : (0:ℝ) < k.factorial := by positivity
  have h := Real.pow_div_factorial_le_exp (c * |s|) (by positivity) k
  rw [mul_pow] at h
  have h2 : c^k * |s|^k ≤ Real.exp (c * |s|) * k.factorial :=
    (div_le_iff₀ hfact).mp h
  calc |s|^k ≤ (Real.exp (c * |s|) * k.factorial) / c^k := by
        rw [le_div_iff₀ hck]
        calc |s|^k * c^k = c^k * |s|^k := by ring
          _ ≤ Real.exp (c * |s|) * k.factorial := h2
    _ = (k.factorial : ℝ) / c^k * Real.exp (c * |s|) := by
        rw [div_eq_inv_mul, div_eq_inv_mul]
        ring

/-- Splitting `e^{c|s|}` across the two signs. -/
theorem exp_neg_sq_add_abs_le_sum (b c m s : ℝ) :
    Real.exp (-b*(s-m)^2 + c*|s|)
      ≤ Real.exp (-b*(s-m)^2 + c*s) + Real.exp (-b*(s-m)^2 - c*s) := by
  have h1 : Real.exp (c * |s|) ≤ Real.exp (c * s) + Real.exp (-(c * s)) := by
    rcases le_total 0 s with hs | hs
    · rw [abs_of_nonneg hs]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos hs, show c * -s = -(c * s) by ring]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  calc Real.exp (-b*(s-m)^2 + c*|s|)
      = Real.exp (-b*(s-m)^2) * Real.exp (c*|s|) := by rw [Real.exp_add]
    _ ≤ Real.exp (-b*(s-m)^2) * (Real.exp (c*s) + Real.exp (-(c*s))) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (-b*(s-m)^2 + c*s) + Real.exp (-b*(s-m)^2 - c*s) := by
        rw [left_distrib, ← Real.exp_add, ← Real.exp_add,
          show -b*(s-m)^2 - c*s = -b*(s-m)^2 + -(c*s) from sub_eq_add_neg _ _]

/-- The master envelope `exp(-b(s-m)² + c|s|)` is integrable for `0 < b`. -/
theorem integrable_exp_neg_sq_add_abs {b : ℝ} (hb : 0 < b) (c m : ℝ) :
    Integrable fun s : ℝ => Real.exp (-b*(s-m)^2 + c*|s|) := by
  have hcont : Continuous fun s : ℝ => Real.exp (-b*(s-m)^2 + c*|s|) := by fun_prop
  have hplus : Integrable fun s : ℝ => Real.exp (-b*(s-m)^2 + c*s) := by
    have hsq : ∀ s : ℝ, -b*(s-m)^2 + c*s
        = -b*(s - (m + c/(2*b)))^2 + (c*m + c^2/(4*b)) := by
      intro s
      field_simp
      ring
    rw [show (fun s : ℝ => Real.exp (-b*(s-m)^2 + c*s))
        = fun s => Real.exp (c*m + c^2/(4*b)) * Real.exp (-b*(s - (m + c/(2*b)))^2) from
      funext fun s => by rw [hsq s, Real.exp_add, mul_comm]]
    exact (Integrable.comp_sub_right (integrable_exp_neg_mul_sq hb) _).const_mul _
  have hminus : Integrable fun s : ℝ => Real.exp (-b*(s-m)^2 - c*s) := by
    have hsq : ∀ s : ℝ, -b*(s-m)^2 - c*s
        = -b*(s - (m - c/(2*b)))^2 + (-(c*m) + c^2/(4*b)) := by
      intro s
      field_simp
      ring
    rw [show (fun s : ℝ => Real.exp (-b*(s-m)^2 - c*s))
        = fun s => Real.exp (-(c*m) + c^2/(4*b)) * Real.exp (-b*(s - (m - c/(2*b)))^2)
        from funext fun s => by rw [hsq s, Real.exp_add, mul_comm]]
    exact (Integrable.comp_sub_right (integrable_exp_neg_mul_sq hb) _).const_mul _
  exact (hplus.add hminus).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact exp_neg_sq_add_abs_le_sum b c m s)

/-- The polynomial-weighted master envelope is integrable for `0 < b`. -/
theorem integrable_one_add_sq_mul_exp_neg_sq_add_abs {b : ℝ} (hb : 0 < b) (c m : ℝ) :
    Integrable fun s : ℝ => (1 + s^2) * Real.exp (-b*(s-m)^2 + c*|s|) := by
  have hb2 : (0:ℝ) < b/2 := by positivity
  have hbound : ∀ s : ℝ, (1 + s^2) * Real.exp (-b*(s-m)^2 + c*|s|)
      ≤ (2*(1+m^2)*(1+2/b)) * Real.exp (-(b/2)*(s-m)^2 + c*|s|) := by
    intro s
    have hsq : 1 + s^2 ≤ 2*(1+m^2)*(1+(s-m)^2) := by
      nlinarith [sq_nonneg (s - 2*m), sq_nonneg (s - m), sq_nonneg m]
    have hle2 : (1:ℝ) + (s-m)^2 ≤ (1 + (b/2)⁻¹) * Real.exp ((b/2)*(s-m)^2) :=
      one_add_sq_le_exp hb2 _
    rw [show ((b/2 : ℝ)⁻¹) = 2/b by field_simp] at hle2
    have hE : Real.exp (-b*(s-m)^2 + c*|s|) * Real.exp ((b/2)*(s-m)^2)
        = Real.exp (-(b/2)*(s-m)^2 + c*|s|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc (1 + s^2) * Real.exp (-b*(s-m)^2 + c*|s|)
        = (2*(1+m^2)) * ((1+(s-m)^2) * Real.exp (-b*(s-m)^2 + c*|s|)) -
          ((2*(1+m^2)*(1+(s-m)^2)) - (1+s^2)) * Real.exp (-b*(s-m)^2 + c*|s|) := by
            ring
      _ ≤ (2*(1+m^2)) * ((1+(s-m)^2) * Real.exp (-b*(s-m)^2 + c*|s|)) := by
            apply sub_le_self
            exact mul_nonneg (by nlinarith [hsq]) (Real.exp_pos _).le
      _ ≤ (2*(1+m^2)) * ((1+2/b) * (Real.exp (-b*(s-m)^2 + c*|s|)
            * Real.exp ((b/2)*(s-m)^2))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 2*(1+m^2))
            calc (1+(s-m)^2) * Real.exp (-b*(s-m)^2 + c*|s|)
                ≤ ((1+2/b) * Real.exp ((b/2)*(s-m)^2))
                    * Real.exp (-b*(s-m)^2 + c*|s|) :=
                  mul_le_mul_of_nonneg_right hle2 (Real.exp_pos _).le
              _ = (1+2/b) * (Real.exp (-b*(s-m)^2 + c*|s|)
                  * Real.exp ((b/2)*(s-m)^2)) := by ring
      _ = (2*(1+m^2)*(1+2/b)) * Real.exp (-(b/2)*(s-m)^2 + c*|s|) := by
            rw [hE]
            ring
  exact ((integrable_exp_neg_sq_add_abs hb2 c m).const_mul _).mono'
    (by fun_prop : Continuous fun s : ℝ => (1 + s^2) * Real.exp (-b*(s-m)^2 + c*|s|)
      ).aestronglyMeasurable
    (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound s)

/-- The completed-square Gaussian vanishes at `+∞`. -/
theorem tendsto_exp_neg_sq_atTop {b : ℝ} (hb : 0 < b) (m : ℝ) :
    Tendsto (fun s : ℝ => Real.exp (-b*(s-m)^2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => s - m) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-m) tendsto_id).congr'
      (Eventually.of_forall fun s => by simp only [id, sub_eq_add_neg])
  have h2 : Tendsto (fun s : ℝ => (s - m)^2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp h1
  have h3 : Tendsto (fun s : ℝ => -b*(s-m)^2) atTop atBot := by
    have h4 : Tendsto (fun s : ℝ => (s-m)^2 * b) atTop atTop := h2.atTop_mul_const hb
    have h5 : Tendsto (fun s : ℝ => -((s-m)^2 * b)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp h4
    exact h5.congr' (Eventually.of_forall fun s => by ring)
  exact Real.tendsto_exp_atBot.comp h3

/-- The completed-square Gaussian vanishes at `-∞`. -/
theorem tendsto_exp_neg_sq_atBot {b : ℝ} (hb : 0 < b) (m : ℝ) :
    Tendsto (fun s : ℝ => Real.exp (-b*(s-m)^2)) atBot (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => m - s) atBot atTop := by
    have h := tendsto_atTop_add_const_left atBot m tendsto_neg_atBot_atTop
    exact h.congr' (Eventually.of_forall fun s => by simp only [sub_eq_add_neg])
  have h2 : Tendsto (fun s : ℝ => (m - s)^2) atBot atTop :=
    (tendsto_pow_atTop two_ne_zero).comp h1
  have h2' : Tendsto (fun s : ℝ => (s - m)^2) atBot atTop :=
    h2.congr' (Eventually.of_forall fun s => by ring)
  have h3 : Tendsto (fun s : ℝ => -b*(s-m)^2) atBot atBot := by
    have h4 : Tendsto (fun s : ℝ => (s-m)^2 * b) atBot atTop := h2'.atTop_mul_const hb
    have h5 : Tendsto (fun s : ℝ => -((s-m)^2 * b)) atBot atBot :=
      tendsto_neg_atTop_atBot.comp h4
    exact h5.congr' (Eventually.of_forall fun s => by ring)
  exact Real.tendsto_exp_atBot.comp h3

/-- The master envelope vanishes at `+∞`. -/
theorem tendsto_exp_neg_sq_add_abs_atTop {b : ℝ} (hb : 0 < b) (c m : ℝ) :
    Tendsto (fun s : ℝ => Real.exp (-b*(s-m)^2 + c*|s|)) atTop (𝓝 0) := by
  have hplus : Tendsto (fun s : ℝ => Real.exp (-b*(s-m)^2 + c*s)) atTop (𝓝 0) := by
    have hsq : ∀ s : ℝ, -b*(s-m)^2 + c*s
        = -b*(s - (m + c/(2*b)))^2 + (c*m + c^2/(4*b)) := by
      intro s
      field_simp
      ring
    have h : Tendsto (fun s : ℝ => Real.exp (c*m + c^2/(4*b))
        * Real.exp (-b*(s - (m + c/(2*b)))^2)) atTop (𝓝 (Real.exp (c*m + c^2/(4*b)) * 0)) :=
      (tendsto_exp_neg_sq_atTop hb _).const_mul _
    rw [mul_zero] at h
    convert h using 1
    · ext s
      rw [hsq s, Real.exp_add, mul_comm]
  have hminus : Tendsto (fun s : ℝ => Real.exp (-b*(s-m)^2 - c*s)) atTop (𝓝 0) := by
    have hsq : ∀ s : ℝ, -b*(s-m)^2 - c*s
        = -b*(s - (m - c/(2*b)))^2 + (-(c*m) + c^2/(4*b)) := by
      intro s
      field_simp
      ring
    have h : Tendsto (fun s : ℝ => Real.exp (-(c*m) + c^2/(4*b))
        * Real.exp (-b*(s - (m - c/(2*b)))^2)) atTop (𝓝 (Real.exp (-(c*m) + c^2/(4*b)) * 0)) :=
      (tendsto_exp_neg_sq_atTop hb _).const_mul _
    rw [mul_zero] at h
    convert h using 1
    · ext s
      rw [hsq s, Real.exp_add, mul_comm]
  exact squeeze_zero' (Eventually.of_forall fun s => (Real.exp_pos _).le)
    (Eventually.of_forall fun s => exp_neg_sq_add_abs_le_sum b c m s)
    (by simpa using hplus.add hminus)

/-- The master envelope vanishes at `-∞`. -/
theorem tendsto_exp_neg_sq_add_abs_atBot {b : ℝ} (hb : 0 < b) (c m : ℝ) :
    Tendsto (fun s : ℝ => Real.exp (-b*(s-m)^2 + c*|s|)) atBot (𝓝 0) := by
  have hplus : Tendsto (fun s : ℝ => Real.exp (-b*(s-m)^2 + c*s)) atBot (𝓝 0) := by
    have hsq : ∀ s : ℝ, -b*(s-m)^2 + c*s
        = -b*(s - (m + c/(2*b)))^2 + (c*m + c^2/(4*b)) := by
      intro s
      field_simp
      ring
    have h : Tendsto (fun s : ℝ => Real.exp (c*m + c^2/(4*b))
        * Real.exp (-b*(s - (m + c/(2*b)))^2)) atBot (𝓝 (Real.exp (c*m + c^2/(4*b)) * 0)) :=
      (tendsto_exp_neg_sq_atBot hb _).const_mul _
    rw [mul_zero] at h
    convert h using 1
    · ext s
      rw [hsq s, Real.exp_add, mul_comm]
  have hminus : Tendsto (fun s : ℝ => Real.exp (-b*(s-m)^2 - c*s)) atBot (𝓝 0) := by
    have hsq : ∀ s : ℝ, -b*(s-m)^2 - c*s
        = -b*(s - (m - c/(2*b)))^2 + (-(c*m) + c^2/(4*b)) := by
      intro s
      field_simp
      ring
    have h : Tendsto (fun s : ℝ => Real.exp (-(c*m) + c^2/(4*b))
        * Real.exp (-b*(s - (m - c/(2*b)))^2)) atBot (𝓝 (Real.exp (-(c*m) + c^2/(4*b)) * 0)) :=
      (tendsto_exp_neg_sq_atBot hb _).const_mul _
    rw [mul_zero] at h
    convert h using 1
    · ext s
      rw [hsq s, Real.exp_add, mul_comm]
  exact squeeze_zero' (Eventually.of_forall fun s => (Real.exp_pos _).le)
    (Eventually.of_forall fun s => exp_neg_sq_add_abs_le_sum b c m s)
    (by simpa using hplus.add hminus)

end Envelopes

/-! ## The backward Airy kernel

`backwardAiry T s = exp(-(2/3) T³ - T s) · Ai(s + T²)` — the paper's `g_T(s)` —
its calculus (C¹ in `T`, C² in `s`, backward heat equation), and its decay bounds. -/

section BackwardAiryKernel

/-- The backward Airy kernel `g_T(s) = exp(-(2/3) T³ - T s) · Ai(s + T²)`. -/
noncomputable def backwardAiry (T s : ℝ) : ℝ :=
  Real.exp (-(2/3)*T^3 - T*s) * airyAiReal (s + T^2)

/-- The `T`-derivative of the exponential factor. -/
theorem hasDerivAt_backwardAiryExp_T (s T : ℝ) :
    HasDerivAt (fun T : ℝ => Real.exp (-(2/3)*T^3 - T*s))
      (Real.exp (-(2/3)*T^3 - T*s) * (-2*T^2 - s)) T := by
  have h := (Real.hasDerivAt_exp (-(2/3)*T^3 - T*s)).comp T
    (((hasDerivAt_pow 3 T).const_mul (-(2/3) : ℝ)).sub ((hasDerivAt_id' T).mul_const s))
  convert h using 1
  · ext T'
    rfl
  · ring

/-- The `s`-derivative of the exponential factor. -/
theorem hasDerivAt_backwardAiryExp_s (T s : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(2/3)*T^3 - T*s))
      (Real.exp (-(2/3)*T^3 - T*s) * (-T)) s := by
  have h := (Real.hasDerivAt_exp (-(2/3)*T^3 - T*s)).comp s
    ((hasDerivAt_const s (-(2/3)*T^3)).sub ((hasDerivAt_id' s).const_mul T))
  convert h using 1
  · ext s'
    rfl
  · ring

/-- The `s`-derivative of `s ↦ Ai(s + u)`. -/
theorem hasDerivAt_airyAiReal_add_const (u s : ℝ) :
    HasDerivAt (fun s : ℝ => airyAiReal (s + u)) (deriv airyAiReal (s + u)) s := by
  have h := (hasDerivAt_airyAiReal (s + u)).comp s ((hasDerivAt_id' s).add_const u)
  convert h using 1
  · ext s'
    rfl
  · rw [(hasDerivAt_airyAiReal (s + u)).deriv, mul_one]

/-- The `T`-derivative of `T ↦ Ai(s + T²)`. -/
theorem hasDerivAt_airyAiReal_const_add_sq (s T : ℝ) :
    HasDerivAt (fun T : ℝ => airyAiReal (s + T^2))
      (deriv airyAiReal (s + T^2) * (2*T)) T := by
  have h := (hasDerivAt_airyAiReal (s + T^2)).comp T
    ((hasDerivAt_const T s).add (hasDerivAt_pow 2 T))
  convert h using 1
  · ext T'
    rfl
  · rw [(hasDerivAt_airyAiReal (s + T^2)).deriv]
    ring

/-- The `s`-derivative of `s ↦ Ai'(s + u)` (by the Airy ODE). -/
theorem hasDerivAt_deriv_airyAiReal_add_const (u s : ℝ) :
    HasDerivAt (fun s : ℝ => deriv airyAiReal (s + u))
      ((s + u) * airyAiReal (s + u)) s := by
  have h := (hasDerivAt_deriv_airyAiReal' (s + u)).comp s ((hasDerivAt_id' s).add_const u)
  convert h using 1
  · ext s'
    rfl
  · ring

/-- The `T`-derivative of `backwardAiry`:
`∂_T g_T(s) = e^{-(2/3)T³-Ts} ((-2T² - s) Ai(s+T²) + 2T Ai'(s+T²))`. -/
theorem hasDerivAt_backwardAiry_T (s T : ℝ) :
    HasDerivAt (fun T : ℝ => backwardAiry T s)
      (Real.exp (-(2/3)*T^3 - T*s) * ((-2*T^2 - s) * airyAiReal (s + T^2)
        + 2*T * deriv airyAiReal (s + T^2))) T := by
  have h := (hasDerivAt_backwardAiryExp_T s T).mul (hasDerivAt_airyAiReal_const_add_sq s T)
  convert h using 1
  · ext T'
    simp only [backwardAiry, Pi.mul_apply]
  · ring

/-- The `s`-derivative of `backwardAiry`:
`∂_s g_T(s) = e^{-(2/3)T³-Ts} (-T Ai(s+T²) + Ai'(s+T²))`. -/
theorem hasDerivAt_backwardAiry_s (T s : ℝ) :
    HasDerivAt (backwardAiry T)
      (Real.exp (-(2/3)*T^3 - T*s) * (-T * airyAiReal (s + T^2)
        + deriv airyAiReal (s + T^2))) s := by
  have h := (hasDerivAt_backwardAiryExp_s T s).mul (hasDerivAt_airyAiReal_add_const (T^2) s)
  convert h using 1
  · ext s'
    simp only [backwardAiry, Pi.mul_apply]
  · ring

/-- The second `s`-derivative of `backwardAiry`:
`∂²_s g_T(s) = e^{-(2/3)T³-Ts} ((s + 2T²) Ai(s+T²) - 2T Ai'(s+T²))`
(using the Airy ODE `Ai''(u) = u Ai(u)`). -/
theorem hasDerivAt_deriv_backwardAiry_s (T s : ℝ) :
    HasDerivAt (deriv (backwardAiry T))
      (Real.exp (-(2/3)*T^3 - T*s) * ((s + 2*T^2) * airyAiReal (s + T^2)
        - 2*T * deriv airyAiReal (s + T^2))) s := by
  have hder : deriv (backwardAiry T) = fun s : ℝ =>
      Real.exp (-(2/3)*T^3 - T*s) * (-T * airyAiReal (s + T^2)
        + deriv airyAiReal (s + T^2)) :=
    funext fun s => (hasDerivAt_backwardAiry_s T s).deriv
  have hAi : HasDerivAt (fun s : ℝ => -T * airyAiReal (s + T^2)
        + deriv airyAiReal (s + T^2))
      (-T * deriv airyAiReal (s + T^2) + (s + T^2) * airyAiReal (s + T^2)) s := by
    have h := ((hasDerivAt_airyAiReal_add_const (T^2) s).const_mul (-T)).add
      (hasDerivAt_deriv_airyAiReal_add_const (T^2) s)
    convert h using 1
  have h := (hasDerivAt_backwardAiryExp_s T s).mul hAi
  rw [hder]
  convert h using 1
  all_goals ring

/-- **The backward heat equation** for `backwardAiry`:
`∂_T g_T(s) = -∂²_s g_T(s)`. -/
theorem backwardAiry_pde (T s : ℝ) :
    deriv (backwardAiry · s) T = -iteratedDeriv 2 (backwardAiry T) s := by
  rw [(hasDerivAt_backwardAiry_T s T).deriv, iteratedDeriv_succ, iteratedDeriv_one,
    (hasDerivAt_deriv_backwardAiry_s T s).deriv]
  ring

/-- `backwardAiry` is jointly continuous on `ℝ × ℝ`. -/
theorem continuous_backwardAiry : Continuous fun p : ℝ × ℝ => backwardAiry p.1 p.2 := by
  unfold backwardAiry
  apply Continuous.mul _ (continuous_airyAiReal.comp (by fun_prop))
  exact Real.continuous_exp.comp (by fun_prop)

/-- `T ↦ backwardAiry T s` is continuous. -/
theorem continuous_backwardAiry_T (s : ℝ) : Continuous fun T : ℝ => backwardAiry T s :=
  continuous_backwardAiry.comp (continuous_id.prodMk continuous_const)

/-- `s ↦ backwardAiry T s` is continuous. -/
theorem continuous_backwardAiry_s (T : ℝ) : Continuous (backwardAiry T) :=
  continuous_backwardAiry.comp (continuous_const.prodMk continuous_id)

/-- `s ↦ deriv (backwardAiry T) s` is continuous. -/
theorem continuous_deriv_backwardAiry_s (T : ℝ) : Continuous (deriv (backwardAiry T)) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_deriv_backwardAiry_s T s).continuousAt

/-- Auxiliary: `|s| ≤ 1 + s²`. -/
theorem abs_le_one_add_sq (s : ℝ) : |s| ≤ 1 + s^2 := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]
    nlinarith [sq_nonneg (s - 1/2)]
  · rw [abs_of_nonpos hs]
    nlinarith [sq_nonneg (s + 1/2)]

/-- **Decay bound for `backwardAiry`**: for `T` in any bounded interval `[0, T₁]`,
`|g_T(s)| ≤ C e^{T₁ |s|}` with `C` a global bound on `Ai`.  (The Gaussian decay of `Ai`
at `+∞` makes the bound much better for `s ≥ 0`, but this uniform bound is what the
convolution estimates below need.) -/
theorem backwardAiry_abs_le_exp (T₁ : ℝ) :
    ∃ C : ℝ, ∀ T ∈ Set.Icc 0 T₁, ∀ s : ℝ, |backwardAiry T s| ≤ C * Real.exp (T₁ * |s|) := by
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le
  have hC₀nn : 0 ≤ C₀ := le_trans (abs_nonneg _) (hC₀ 0)
  refine ⟨C₀, fun T hT s => ?_⟩
  have hT0 : 0 ≤ T := hT.1
  have hT1 : T ≤ T₁ := hT.2
  unfold backwardAiry
  rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-(2/3)*T^3 - T*s) * |airyAiReal (s + T^2)|
      ≤ Real.exp (-(2/3)*T^3 - T*s) * C₀ :=
        mul_le_mul_of_nonneg_left (hC₀ _) (Real.exp_pos _).le
    _ ≤ Real.exp (T₁ * |s|) * C₀ := by
        apply mul_le_mul_of_nonneg_right _ hC₀nn
        apply Real.exp_le_exp.mpr
        have h2 : -(T*s) ≤ T * |s| := by
          rw [← neg_mul]
          calc (-T) * s ≤ |(-T) * s| := le_abs_self _
            _ = T * |s| := by rw [abs_mul, abs_neg, abs_of_nonneg hT0]
        have h3 : T * |s| ≤ T₁ * |s| := mul_le_mul_of_nonneg_right hT1 (abs_nonneg _)
        have h1 : -(2/3)*T^3 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hT0 3)
        linarith
    _ = C₀ * Real.exp (T₁ * |s|) := by ring

/-- **Decay bound for `∂_T backwardAiry`**: for `T ∈ [t₀, T₁]` with `0 < t₀`,
`|∂_T g_T(s)| ≤ C (1 + s²) e^{T₁ |s|}`. -/
theorem backwardAiry_deriv_T_abs_le_exp (T₁ : ℝ) :
    ∃ C : ℝ, ∀ T ∈ Set.Icc 0 T₁, ∀ s : ℝ,
      |Real.exp (-(2/3)*T^3 - T*s) * ((-2*T^2 - s) * airyAiReal (s + T^2)
        + 2*T * deriv airyAiReal (s + T^2))| ≤ C * (1 + s^2) * Real.exp (T₁ * |s|) := by
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le
  obtain ⟨C₁, hC₁⟩ := deriv_airyAiReal_abs_le
  have hC₀nn : 0 ≤ C₀ := le_trans (abs_nonneg _) (hC₀ 0)
  have hC₁nn : 0 ≤ C₁ := by
    have h := hC₁ 0
    have hpos : (0:ℝ) ≤ |deriv airyAiReal 0| := abs_nonneg _
    have hle : (0:ℝ) ≤ C₁ * (1 + (0:ℝ)^2) := le_trans hpos h
    simp only [zero_pow two_ne_zero, add_zero, mul_one] at hle
    exact hle
  refine ⟨(2*T₁^2 + 1) * C₀ + 2*T₁ * C₁ * (2*(1 + T₁^4)), fun T hT s => ?_⟩
  have hT0 : 0 ≤ T := hT.1
  have hT1 : T ≤ T₁ := hT.2
  have hT₁nn : 0 ≤ T₁ := le_trans hT0 hT1
  rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  have hE : Real.exp (-(2/3)*T^3 - T*s) ≤ Real.exp (T₁ * |s|) := by
    apply Real.exp_le_exp.mpr
    have h2 : -(T*s) ≤ T * |s| := by
      rw [← neg_mul]
      calc (-T) * s ≤ |(-T) * s| := le_abs_self _
        _ = T * |s| := by rw [abs_mul, abs_neg, abs_of_nonneg hT0]
    have h3 : T * |s| ≤ T₁ * |s| := mul_le_mul_of_nonneg_right hT1 (abs_nonneg _)
    have h1 : -(2/3)*T^3 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hT0 3)
    linarith
  have hpoly : |(-2*T^2 - s) * airyAiReal (s + T^2) + 2*T * deriv airyAiReal (s + T^2)|
      ≤ ((2*T₁^2 + 1) * C₀ + 2*T₁ * C₁ * (2*(1 + T₁^4))) * (1 + s^2) := by
    have habs1 : |-2*T^2 - s| ≤ (2*T₁^2 + 1) * (1 + s^2) := by
      have h1 : |-2*T^2 - s| ≤ |-2*T^2| + |s| := by
        rw [sub_eq_add_neg, ← abs_neg s]
        exact abs_add_le _ _
      have h2 : |-2*T^2| = 2*T^2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg T)]
        norm_num
      rw [h2] at h1
      calc |-2*T^2 - s| ≤ 2*T^2 + |s| := h1
        _ ≤ 2*T₁^2 + (1 + s^2) := by
            apply add_le_add _ (abs_le_one_add_sq s)
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT0 hT1 2) (by norm_num)
        _ ≤ (2*T₁^2 + 1) * (1 + s^2) := by
            have hs2 : 0 ≤ s^2 := sq_nonneg s
            have hT2 : 0 ≤ T₁^2 := sq_nonneg T₁
            nlinarith
    have hAi' : |deriv airyAiReal (s + T^2)| ≤ C₁ * (2*(1 + T₁^4)) * (1 + s^2) := by
      calc |deriv airyAiReal (s + T^2)|
          ≤ C₁ * (1 + (s + T^2)^2) := hC₁ _
        _ ≤ C₁ * (2*(1 + T₁^4)) * (1 + s^2) := by
            rw [mul_assoc]
            apply mul_le_mul_of_nonneg_left _ hC₁nn
            have hT4 : T^4 ≤ T₁^4 := pow_le_pow_left₀ hT0 hT1 4
            have hT4' : (T^2)^2 ≤ T₁^4 := by
              have e : (T^2)^2 = T^4 := by ring
              rw [e]
              exact hT4
            have hs2 : 0 ≤ s^2 := sq_nonneg s
            have hT14 : 0 ≤ T₁^4 := by positivity
            have hT14s2 : 0 ≤ T₁^4 * s^2 := mul_nonneg hT14 hs2
            nlinarith [sq_nonneg (s - T^2), hT4']
    have hpart1 : |(-2*T^2 - s) * airyAiReal (s + T^2)|
        ≤ (2*T₁^2 + 1) * (1 + s^2) * C₀ := by
      rw [abs_mul]
      exact mul_le_mul habs1 (hC₀ _) (abs_nonneg _) (by positivity)
    have hpart2 : |2*T * deriv airyAiReal (s + T^2)|
        ≤ 2*T₁ * (C₁ * (2*(1 + T₁^4)) * (1 + s^2)) := by
      have h2T : |2*T| = 2*T := abs_of_nonneg (by positivity)
      rw [abs_mul, h2T]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hT1 (by norm_num)) hAi'
        (abs_nonneg _) (by positivity)
    calc |(-2*T^2 - s) * airyAiReal (s + T^2) + 2*T * deriv airyAiReal (s + T^2)|
        ≤ |(-2*T^2 - s) * airyAiReal (s + T^2)| + |2*T * deriv airyAiReal (s + T^2)| :=
          abs_add_le _ _
      _ ≤ (2*T₁^2 + 1) * (1 + s^2) * C₀ + 2*T₁ * (C₁ * (2*(1 + T₁^4)) * (1 + s^2)) :=
          add_le_add hpart1 hpart2
      _ = ((2*T₁^2 + 1) * C₀ + 2*T₁ * C₁ * (2*(1 + T₁^4))) * (1 + s^2) := by ring
  calc Real.exp (-(2/3)*T^3 - T*s) *
        |(-2*T^2 - s) * airyAiReal (s + T^2) + 2*T * deriv airyAiReal (s + T^2)|
      ≤ Real.exp (T₁ * |s|) *
        (((2*T₁^2 + 1) * C₀ + 2*T₁ * C₁ * (2*(1 + T₁^4))) * (1 + s^2)) :=
        mul_le_mul hE hpoly (by positivity) (Real.exp_pos _).le
    _ = ((2*T₁^2 + 1) * C₀ + 2*T₁ * C₁ * (2*(1 + T₁^4))) * (1 + s^2)
        * Real.exp (T₁ * |s|) := by
        ring

/-- The `s`-derivative of `backwardAiry` decays: `|∂_s g_T(s)| ≤ C (1+s²) e^{T|s|}`. -/
theorem backwardAiry_deriv_s_abs_le_exp (hT : 0 < T) :
    ∃ C : ℝ, ∀ s : ℝ, |deriv (backwardAiry T) s| ≤ C * (1 + s^2) * Real.exp (T * |s|) := by
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le
  obtain ⟨C₁, hC₁⟩ := deriv_airyAiReal_abs_le
  have hC₁nn : 0 ≤ C₁ := by
    have h := hC₁ 0
    have hle : (0:ℝ) ≤ C₁ * (1 + (0:ℝ)^2) := le_trans (abs_nonneg _) h
    simp only [zero_pow two_ne_zero, add_zero, mul_one] at hle
    exact hle
  refine ⟨T * C₀ + C₁ * (2*(1 + T^4)), fun s => ?_⟩
  rw [(hasDerivAt_backwardAiry_s T s).deriv, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  have hE : Real.exp (-(2/3)*T^3 - T*s) ≤ Real.exp (T * |s|) := by
    apply Real.exp_le_exp.mpr
    have h2 : -(T*s) ≤ T * |s| := by
      rw [← neg_mul]
      calc (-T) * s ≤ |(-T) * s| := le_abs_self _
        _ = T * |s| := by rw [abs_mul, abs_neg, abs_of_nonneg hT.le]
    have h1 : -(2/3)*T^3 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hT.le 3)
    linarith
  have hsq : (s + T^2)^2 ≤ 2*s^2 + 2*T^4 := by
    have e : (s + T^2)^2 = s^2 + 2*s*T^2 + (T^2)^2 := by ring
    have e4 : (T^2)^2 = T^4 := by ring
    nlinarith [sq_nonneg (s - T^2), sq_nonneg (s + T^2)]
  have hAi' : |deriv airyAiReal (s + T^2)| ≤ C₁ * (2*(1 + T^4)) * (1 + s^2) := by
    calc |deriv airyAiReal (s + T^2)|
        ≤ C₁ * (1 + (s + T^2)^2) := hC₁ _
      _ ≤ C₁ * (2*(1 + T^4)) * (1 + s^2) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hC₁nn
          have hs2 : 0 ≤ s^2 := sq_nonneg s
          have hT14 : 0 ≤ T^4 := by positivity
          nlinarith [hsq]
  have hpoly : |-T * airyAiReal (s + T^2) + deriv airyAiReal (s + T^2)|
      ≤ (T * C₀ + C₁ * (2*(1 + T^4))) * (1 + s^2) := by
    have hpart1 : |-T * airyAiReal (s + T^2)| ≤ T * C₀ * (1 + s^2) := by
      rw [abs_mul]
      have hC₀nn : 0 ≤ C₀ := le_trans (abs_nonneg _) (hC₀ 0)
      have h1 : |(-T)| * |airyAiReal (s + T^2)| ≤ T * C₀ :=
        mul_le_mul (le_of_eq (by rw [abs_neg, abs_of_nonneg hT.le])) (hC₀ _) (abs_nonneg _)
          hT.le
      calc |(-T)| * |airyAiReal (s + T^2)|
          ≤ T * C₀ := h1
        _ ≤ T * C₀ * (1 + s^2) := by
            apply le_mul_of_one_le_right (mul_nonneg hT.le hC₀nn)
            nlinarith [sq_nonneg s]
    have hpart2 : |deriv airyAiReal (s + T^2)| ≤ C₁ * (2*(1 + T^4)) * (1 + s^2) := hAi'
    calc |-T * airyAiReal (s + T^2) + deriv airyAiReal (s + T^2)|
        ≤ |-T * airyAiReal (s + T^2)| + |deriv airyAiReal (s + T^2)| := abs_add_le _ _
      _ ≤ T * C₀ * (1 + s^2) + C₁ * (2*(1 + T^4)) * (1 + s^2) := add_le_add hpart1 hpart2
      _ = (T * C₀ + C₁ * (2*(1 + T^4))) * (1 + s^2) := by ring
  calc Real.exp (-(2/3)*T^3 - T*s) * |-T * airyAiReal (s + T^2) + deriv airyAiReal (s + T^2)|
      ≤ Real.exp (T * |s|) * ((T * C₀ + C₁ * (2*(1 + T^4))) * (1 + s^2)) :=
        mul_le_mul hE hpoly (by positivity) (Real.exp_pos _).le
    _ = (T * C₀ + C₁ * (2*(1 + T^4))) * (1 + s^2) * Real.exp (T * |s|) := by ring

/-- The second `s`-derivative of `backwardAiry` decays:
`|∂²_s g_T(s)| ≤ C (1+s²) e^{T|s|}`. -/
theorem backwardAiry_deriv_two_s_abs_le_exp (hT : 0 < T) :
    ∃ C : ℝ, ∀ s : ℝ, |iteratedDeriv 2 (backwardAiry T) s|
      ≤ C * (1 + s^2) * Real.exp (T * |s|) := by
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le
  obtain ⟨C₁, hC₁⟩ := deriv_airyAiReal_abs_le
  have hC₁nn : 0 ≤ C₁ := by
    have h := hC₁ 0
    have hle : (0:ℝ) ≤ C₁ * (1 + (0:ℝ)^2) := le_trans (abs_nonneg _) h
    simp only [zero_pow two_ne_zero, add_zero, mul_one] at hle
    exact hle
  refine ⟨(1 + 2*T^2) * C₀ + 2*T * C₁ * (2*(1 + T^4)), fun s => ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one, (hasDerivAt_deriv_backwardAiry_s T s).deriv,
    abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  have hE : Real.exp (-(2/3)*T^3 - T*s) ≤ Real.exp (T * |s|) := by
    apply Real.exp_le_exp.mpr
    have h2 : -(T*s) ≤ T * |s| := by
      rw [← neg_mul]
      calc (-T) * s ≤ |(-T) * s| := le_abs_self _
        _ = T * |s| := by rw [abs_mul, abs_neg, abs_of_nonneg hT.le]
    have h1 : -(2/3)*T^3 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hT.le 3)
    linarith
  have hsq : (s + T^2)^2 ≤ 2*s^2 + 2*T^4 := by
    have e : (s + T^2)^2 = s^2 + 2*s*T^2 + (T^2)^2 := by ring
    have e4 : (T^2)^2 = T^4 := by ring
    nlinarith [sq_nonneg (s - T^2), sq_nonneg (s + T^2)]
  have hAi' : |deriv airyAiReal (s + T^2)| ≤ C₁ * (2*(1 + T^4)) * (1 + s^2) := by
    calc |deriv airyAiReal (s + T^2)|
        ≤ C₁ * (1 + (s + T^2)^2) := hC₁ _
      _ ≤ C₁ * (2*(1 + T^4)) * (1 + s^2) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hC₁nn
          have hs2 : 0 ≤ s^2 := sq_nonneg s
          have hT14 : 0 ≤ T^4 := by positivity
          nlinarith [hsq]
  have habs1 : |s + 2*T^2| ≤ (1 + 2*T^2) * (1 + s^2) := by
    calc |s + 2*T^2| ≤ |s| + |2*T^2| := abs_add_le _ _
      _ ≤ (1 + s^2) + 2*T^2 := by
          apply add_le_add (abs_le_one_add_sq s)
          rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*T^2)]
      _ ≤ (1 + 2*T^2) * (1 + s^2) := by
          have hs2 : 0 ≤ s^2 := sq_nonneg s
          have hT22 : 0 ≤ T^2 := sq_nonneg T
          nlinarith
  have hpoly : |(s + 2*T^2) * airyAiReal (s + T^2) - 2*T * deriv airyAiReal (s + T^2)|
      ≤ ((1 + 2*T^2) * C₀ + 2*T * C₁ * (2*(1 + T^4))) * (1 + s^2) := by
    have hpart1 : |(s + 2*T^2) * airyAiReal (s + T^2)|
        ≤ (1 + 2*T^2) * (1 + s^2) * C₀ := by
      rw [abs_mul]
      exact mul_le_mul habs1 (hC₀ _) (abs_nonneg _) (by positivity)
    have hpart2 : |2*T * deriv airyAiReal (s + T^2)|
        ≤ 2*T * (C₁ * (2*(1 + T^4)) * (1 + s^2)) := by
      have h2T : |2*T| = 2*T := abs_of_nonneg (by positivity)
      rw [abs_mul, h2T]
      exact mul_le_mul_of_nonneg_left hAi' (by positivity)
    calc |(s + 2*T^2) * airyAiReal (s + T^2) - 2*T * deriv airyAiReal (s + T^2)|
        ≤ |(s + 2*T^2) * airyAiReal (s + T^2)| + |2*T * deriv airyAiReal (s + T^2)| := by
          rw [sub_eq_add_neg, ← abs_neg (2*T * deriv airyAiReal (s + T^2))]
          exact abs_add_le _ _
      _ ≤ (1 + 2*T^2) * (1 + s^2) * C₀ + 2*T * (C₁ * (2*(1 + T^4)) * (1 + s^2)) :=
          add_le_add hpart1 hpart2
      _ = ((1 + 2*T^2) * C₀ + 2*T * C₁ * (2*(1 + T^4))) * (1 + s^2) := by ring
  calc Real.exp (-(2/3)*T^3 - T*s) *
        |(s + 2*T^2) * airyAiReal (s + T^2) - 2*T * deriv airyAiReal (s + T^2)|
      ≤ Real.exp (T * |s|) *
        (((1 + 2*T^2) * C₀ + 2*T * C₁ * (2*(1 + T^4))) * (1 + s^2)) :=
        mul_le_mul hE hpoly (by positivity) (Real.exp_pos _).le
    _ = ((1 + 2*T^2) * C₀ + 2*T * C₁ * (2*(1 + T^4))) * (1 + s^2) * Real.exp (T * |s|) := by
        ring

end BackwardAiryKernel

/-! ## Step (i) of (1): integrability and the `T`-derivative of the convolution -/

section HeatAiryConvolution

/-- The `T`-derivative of the heat–Airy convolution integrand
`s ↦ heatKernel T (x - s) * backwardAiry T s`. -/
noncomputable def heatAiryConvDerivT (T x s : ℝ) : ℝ :=
  ((-1/(2*T) + (x - s)^2/(4*T^2)) * heatKernel T (x - s)) * backwardAiry T s
    + heatKernel T (x - s) * (Real.exp (-(2/3)*T^3 - T*s)
      * ((-2*T^2 - s) * airyAiReal (s + T^2) + 2*T * deriv airyAiReal (s + T^2)))

/-- Pointwise `T`-derivative of the integrand. -/
theorem hasDerivAt_heatAiryConv_integrand_T (hT : 0 < T) (x s : ℝ) :
    HasDerivAt (fun T : ℝ => heatKernel T (x - s) * backwardAiry T s)
      (heatAiryConvDerivT T x s) T := by
  have h := (hasDerivAt_heatKernel_T hT (x - s)).mul (hasDerivAt_backwardAiry_T s T)
  convert h using 1
  unfold heatAiryConvDerivT
  ring

/-- `s ↦ heatAiryConvDerivT T x s` is continuous. -/
theorem continuous_heatAiryConvDerivT (T x : ℝ) :
    Continuous fun s : ℝ => heatAiryConvDerivT T x s := by
  unfold heatAiryConvDerivT
  apply Continuous.add
  · apply Continuous.mul (Continuous.mul _ ((continuous_heatKernel T).comp (by fun_prop)))
      (continuous_backwardAiry_s T)
    fun_prop
  · apply Continuous.mul ((continuous_heatKernel T).comp (by fun_prop))
    apply Continuous.mul (by fun_prop)
    apply Continuous.add
    · apply Continuous.mul (by fun_prop) (continuous_airyAiReal.comp (by fun_prop))
    · apply Continuous.mul (by fun_prop) (continuous_deriv_airyAiReal.comp (by fun_prop))

/-- **Step (i) of (1)**: the heat–Airy convolution integrand is integrable for `0 < T`. -/
theorem integrable_heatKernel_mul_backwardAiry (hT : 0 < T) (x : ℝ) :
    Integrable fun s : ℝ => heatKernel T (x - s) * backwardAiry T s := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp T
  have hmeas : AEStronglyMeasurable (fun s : ℝ => heatKernel T (x - s) * backwardAiry T s) :=
    (((continuous_heatKernel T).comp (by fun_prop)).mul
      (continuous_backwardAiry_s T)).aestronglyMeasurable
  apply ((integrable_exp_neg_sq_add_abs (b := 1/(4*T)) (by positivity) T x).const_mul
    ((4*Real.pi*T)^(-1/2:ℝ) * C₀)).mono' hmeas
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hT _)]
  have hg := hC₀ T ⟨hT.le, le_rfl⟩ s
  calc heatKernel T (x - s) * |backwardAiry T s|
      ≤ heatKernel T (x - s) * (C₀ * Real.exp (T * |s|)) :=
        mul_le_mul_of_nonneg_left hg (heatKernel_nonneg hT _)
    _ = (4*Real.pi*T)^(-1/2:ℝ) * C₀ * Real.exp (-(1/(4*T))*(s - x)^2 + T*|s|) := by
        have hexp : -(x - s)^2/(4*T) = -(1/(4*T))*(s - x)^2 := by ring
        unfold heatKernel
        rw [show ((4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-(x-s)^2/(4*T))) * (C₀ * Real.exp (T*|s|))
            = (4*Real.pi*T)^(-1/2:ℝ) * C₀ * (Real.exp (-(x-s)^2/(4*T)) * Real.exp (T*|s|))
            from by ring]
        rw [← Real.exp_add, hexp]

/-- Domination of the `T`-derivative of the integrand, uniformly for
`T ∈ [t₀, T₁]` with `0 < t₀`: bounded by `C (1+s²) e^{-(s-x)²/(8T₁) + T₁|s|}`. -/
theorem heatAiryConvDerivT_abs_le {t₀ T₁ : ℝ} (ht₀ : 0 < t₀) (h : t₀ ≤ T₁) (x : ℝ) :
    ∃ C : ℝ, ∀ T ∈ Set.Icc t₀ T₁, ∀ s : ℝ,
      |heatAiryConvDerivT T x s|
        ≤ C * (1 + s^2) * Real.exp (-(1/(8*T₁))*(s - x)^2 + T₁*|s|) := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp T₁
  obtain ⟨C₂, hC₂⟩ := backwardAiry_deriv_T_abs_le_exp T₁
  have ht₀T₁ : 0 < T₁ := ht₀.trans_le h
  have hC₀nn : 0 ≤ C₀ := by
    have h0 := hC₀ 0 ⟨le_rfl, ht₀T₁.le⟩ 0
    rw [abs_zero, mul_zero, Real.exp_zero, mul_one] at h0
    have e : backwardAiry 0 0 = airyAiReal 0 := by simp [backwardAiry]
    rw [e] at h0
    exact le_trans (abs_nonneg _) h0
  refine ⟨((1/(2*t₀) + 1/(4*t₀^2)) * (4*Real.pi*t₀)^(-1/2:ℝ) * C₀ * (2*(1+x^2))
      + (4*Real.pi*t₀)^(-1/2:ℝ) * C₂), fun T hT s => ?_⟩
  have hTt₀ : t₀ ≤ T := hT.1
  have hTT₁ : T ≤ T₁ := hT.2
  have hTpos : 0 < T := ht₀.trans_le hTt₀
  have hrpow : (4 * Real.pi * T)^(-1/2 : ℝ) ≤ (4 * Real.pi * t₀)^(-1/2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (mul_le_mul_of_nonneg_left hTt₀ (by positivity)) (by norm_num)
  have hexp1 : Real.exp (-(x - s)^2/(4*T)) ≤ Real.exp (-(x - s)^2/(8*T₁)) := by
    apply Real.exp_le_exp.mpr
    have h1 : (x - s)^2/(4*T₁) ≤ (x - s)^2/(4*T) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left hTT₁ (by norm_num))
    have h2 : (x - s)^2/(8*T₁) ≤ (x - s)^2/(4*T₁) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (by nlinarith [ht₀T₁])
    rw [show -(x - s)^2/(4*T) = -((x - s)^2/(4*T)) by ring,
      show -(x - s)^2/(8*T₁) = -((x - s)^2/(8*T₁)) by ring]
    exact neg_le_neg (h2.trans h1)
  have hhk : heatKernel T (x - s)
      ≤ (4*Real.pi*t₀)^(-1/2:ℝ) * Real.exp (-(x - s)^2/(8*T₁)) := by
    unfold heatKernel
    exact mul_le_mul hrpow hexp1 (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _)
  have hA : |-1/(2*T) + (x - s)^2/(4*T^2)| ≤ (1/(2*t₀) + 1/(4*t₀^2)) * (1 + (x - s)^2) := by
    have h1 : |-1/(2*T)| ≤ 1/(2*t₀) := by
      have e : |-1/(2*T)| = 1/(2*T) := by
        rw [abs_div, abs_neg, abs_one, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*T)]
      rw [e]
      exact div_le_div_of_nonneg_left zero_le_one (by positivity)
        (mul_le_mul_of_nonneg_left hTt₀ (by norm_num))
    have h2 : |(x - s)^2/(4*T^2)| ≤ (x - s)^2/(4*t₀^2) := by
      have e : |(x - s)^2/(4*T^2)| = (x - s)^2/(4*T^2) :=
        abs_of_nonneg (by positivity)
      rw [e]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht₀.le hTt₀ 2) (by norm_num))
    calc |-1/(2*T) + (x - s)^2/(4*T^2)|
        ≤ |-1/(2*T)| + |(x - s)^2/(4*T^2)| := abs_add_le _ _
      _ ≤ 1/(2*t₀) + (x - s)^2/(4*t₀^2) := add_le_add h1 h2
      _ ≤ (1/(2*t₀) + 1/(4*t₀^2)) * (1 + (x - s)^2) := by
          have hA0 : (0:ℝ) ≤ 1/(2*t₀) := by positivity
          have hB0 : (0:ℝ) ≤ 1/(4*t₀^2) := by positivity
          have hq1 : (1:ℝ) ≤ 1 + (x - s)^2 := le_add_of_nonneg_right (sq_nonneg _)
          calc 1/(2*t₀) + (x - s)^2/(4*t₀^2)
              ≤ 1/(2*t₀) * (1 + (x - s)^2) + (1/(4*t₀^2)) * (1 + (x - s)^2) :=
                add_le_add (le_mul_of_one_le_right hA0 hq1)
                  (by rw [show (x - s)^2/(4*t₀^2) = (1/(4*t₀^2)) * (x - s)^2 by ring]
                      exact mul_le_mul_of_nonneg_left
                        (le_add_of_nonneg_left zero_le_one) hB0)
            _ = (1/(2*t₀) + 1/(4*t₀^2)) * (1 + (x - s)^2) := by ring
  have hsub : 1 + (x - s)^2 ≤ 2*(1+x^2)*(1+s^2) := by
    nlinarith [sq_nonneg (x - s), sq_nonneg (x + s), sq_nonneg x, sq_nonneg s,
      sq_nonneg (x * s)]
  have hterm1 : |(-1/(2*T) + (x - s)^2/(4*T^2))| * heatKernel T (x - s) * |backwardAiry T s|
      ≤ ((1/(2*t₀) + 1/(4*t₀^2)) * (4*Real.pi*t₀)^(-1/2:ℝ) * C₀ * (2*(1+x^2))) * (1 + s^2)
        * (Real.exp (-(x - s)^2/(8*T₁)) * Real.exp (T₁*|s|)) := by
    have hle1 : |(-1/(2*T) + (x - s)^2/(4*T^2))| * heatKernel T (x - s) * |backwardAiry T s|
        ≤ ((1/(2*t₀) + 1/(4*t₀^2)) * (1 + (x - s)^2))
          * ((4*Real.pi*t₀)^(-1/2:ℝ) * Real.exp (-(x - s)^2/(8*T₁)))
          * (C₀ * Real.exp (T₁ * |s|)) :=
      mul_le_mul (mul_le_mul hA hhk (heatKernel_nonneg hTpos _)
        (mul_nonneg (by positivity) (by positivity)))
        (hC₀ T ⟨hTpos.le, hTT₁⟩ s) (abs_nonneg _)
        (mul_nonneg (by positivity) (by positivity))
    calc |(-1/(2*T) + (x - s)^2/(4*T^2))| * heatKernel T (x - s) * |backwardAiry T s|
        ≤ ((1/(2*t₀) + 1/(4*t₀^2)) * (1 + (x - s)^2))
          * ((4*Real.pi*t₀)^(-1/2:ℝ) * Real.exp (-(x - s)^2/(8*T₁)))
          * (C₀ * Real.exp (T₁ * |s|)) := hle1
      _ = ((1/(2*t₀) + 1/(4*t₀^2)) * (4*Real.pi*t₀)^(-1/2:ℝ) * C₀) * (1 + (x - s)^2)
          * (Real.exp (-(x - s)^2/(8*T₁)) * Real.exp (T₁*|s|)) := by ring
      _ ≤ ((1/(2*t₀) + 1/(4*t₀^2)) * (4*Real.pi*t₀)^(-1/2:ℝ) * C₀) * (2*(1+x^2)*(1+s^2))
          * (Real.exp (-(x - s)^2/(8*T₁)) * Real.exp (T₁*|s|)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsub (by positivity)) (by positivity)
      _ = ((1/(2*t₀) + 1/(4*t₀^2)) * (4*Real.pi*t₀)^(-1/2:ℝ) * C₀ * (2*(1+x^2))) * (1 + s^2)
          * (Real.exp (-(x - s)^2/(8*T₁)) * Real.exp (T₁*|s|)) := by ring
  have hterm2 : heatKernel T (x - s) * |Real.exp (-(2/3)*T^3 - T*s)
        * ((-2*T^2 - s) * airyAiReal (s + T^2) + 2*T * deriv airyAiReal (s + T^2))|
      ≤ ((4*Real.pi*t₀)^(-1/2:ℝ) * C₂) * (1 + s^2)
        * (Real.exp (-(x - s)^2/(8*T₁)) * Real.exp (T₁*|s|)) := by
    have hle2 := mul_le_mul hhk (hC₂ T ⟨hTpos.le, hTT₁⟩ s)
      (by positivity) (by positivity)
    calc heatKernel T (x - s) * |Real.exp (-(2/3)*T^3 - T*s)
          * ((-2*T^2 - s) * airyAiReal (s + T^2) + 2*T * deriv airyAiReal (s + T^2))|
        ≤ ((4*Real.pi*t₀)^(-1/2:ℝ) * Real.exp (-(x - s)^2/(8*T₁)))
          * (C₂ * (1 + s^2) * Real.exp (T₁ * |s|)) := hle2
      _ = ((4*Real.pi*t₀)^(-1/2:ℝ) * C₂) * (1 + s^2)
          * (Real.exp (-(x - s)^2/(8*T₁)) * Real.exp (T₁*|s|)) := by ring
  have hsplit : |((-1/(2*T) + (x - s)^2/(4*T^2)) * heatKernel T (x - s)) * backwardAiry T s
      + heatKernel T (x - s) * (Real.exp (-(2/3)*T^3 - T*s)
        * ((-2*T^2 - s) * airyAiReal (s + T^2) + 2*T * deriv airyAiReal (s + T^2)))|
      ≤ |(-1/(2*T) + (x - s)^2/(4*T^2))| * heatKernel T (x - s) * |backwardAiry T s|
        + heatKernel T (x - s) * |Real.exp (-(2/3)*T^3 - T*s)
          * ((-2*T^2 - s) * airyAiReal (s + T^2) + 2*T * deriv airyAiReal (s + T^2))| := by
    refine (abs_add_le _ _).trans ?_
    apply add_le_add
    · rw [abs_mul, abs_mul, abs_of_nonneg (heatKernel_nonneg hTpos _)]
    · rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hTpos _)]
  unfold heatAiryConvDerivT
  calc |((-1/(2*T) + (x - s)^2/(4*T^2)) * heatKernel T (x - s)) * backwardAiry T s
      + heatKernel T (x - s) * (Real.exp (-(2/3)*T^3 - T*s)
        * ((-2*T^2 - s) * airyAiReal (s + T^2) + 2*T * deriv airyAiReal (s + T^2)))|
      ≤ |(-1/(2*T) + (x - s)^2/(4*T^2))| * heatKernel T (x - s) * |backwardAiry T s|
        + heatKernel T (x - s) * |Real.exp (-(2/3)*T^3 - T*s)
          * ((-2*T^2 - s) * airyAiReal (s + T^2) + 2*T * deriv airyAiReal (s + T^2))| :=
        hsplit
    _ ≤ (((1/(2*t₀) + 1/(4*t₀^2)) * (4*Real.pi*t₀)^(-1/2:ℝ) * C₀ * (2*(1+x^2))) * (1 + s^2)
          * (Real.exp (-(x - s)^2/(8*T₁)) * Real.exp (T₁*|s|)))
        + (((4*Real.pi*t₀)^(-1/2:ℝ) * C₂) * (1 + s^2)
          * (Real.exp (-(x - s)^2/(8*T₁)) * Real.exp (T₁*|s|))) :=
        add_le_add hterm1 hterm2
    _ = (((1/(2*t₀) + 1/(4*t₀^2)) * (4*Real.pi*t₀)^(-1/2:ℝ) * C₀ * (2*(1+x^2)))
          + (4*Real.pi*t₀)^(-1/2:ℝ) * C₂) * (1 + s^2)
          * Real.exp (-(1/(8*T₁))*(s - x)^2 + T₁*|s|) := by
        have hexp : -(1/(8*T₁))*(s - x)^2 + T₁*|s| = -(x - s)^2/(8*T₁) + T₁*|s| := by ring
        rw [hexp, ← Real.exp_add]
        ring

/-- **Differentiation under the integral in `T`**, full form: for `0 < T₀`,
`F(T) = ∫ s, heatKernel T (x-s) * backwardAiry T s` is differentiable at `T₀` with
derivative `∫ s, heatAiryConvDerivT T₀ x s`, and the latter is integrable. -/
theorem hasDerivAt_integral_heatAiryConv' (hT₀ : 0 < T₀) (x : ℝ) :
    Integrable (fun s : ℝ => heatAiryConvDerivT T₀ x s) ∧
      HasDerivAt (fun T : ℝ => ∫ s : ℝ, heatKernel T (x - s) * backwardAiry T s)
        (∫ s : ℝ, heatAiryConvDerivT T₀ x s) T₀ := by
  obtain ⟨C₅, hC₅⟩ := heatAiryConvDerivT_abs_le (t₀ := T₀/2) (T₁ := 2*T₀) (by positivity)
    (by linarith) x
  have hbound : ∀ᵐ s : ℝ, ∀ T ∈ Set.Icc (T₀/2) (2*T₀),
      ‖heatAiryConvDerivT T x s‖ ≤ C₅ * ((1 + s^2) *
        Real.exp (-(1/(8*(2*T₀)))*(s - x)^2 + (2*T₀)*|s|)) :=
    Eventually.of_forall fun s T hT => by
      rw [Real.norm_eq_abs]
      exact (hC₅ T hT s).trans_eq (by ring)
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds (by linarith : T₀/2 < T₀) (by linarith : T₀ < 2*T₀))
    (Eventually.of_forall fun T =>
      (((continuous_heatKernel T).comp (by fun_prop)).mul
        (continuous_backwardAiry_s T)).aestronglyMeasurable)
    (integrable_heatKernel_mul_backwardAiry hT₀ x)
    (continuous_heatAiryConvDerivT T₀ x).aestronglyMeasurable
    hbound
    ((integrable_one_add_sq_mul_exp_neg_sq_add_abs (b := 1/(8*(2*T₀))) (by positivity)
      (2*T₀) x).const_mul C₅)
    (Eventually.of_forall fun s T hT =>
      hasDerivAt_heatAiryConv_integrand_T (lt_of_lt_of_le (by positivity) hT.1) x s)

/-- **Differentiation under the integral in `T`**: for `0 < T₀`,
`F(T) = ∫ s, heatKernel T (x-s) * backwardAiry T s` is differentiable at `T₀` with
derivative `∫ s, heatAiryConvDerivT T₀ x s`. -/
theorem hasDerivAt_integral_heatAiryConv (hT₀ : 0 < T₀) (x : ℝ) :
    HasDerivAt (fun T : ℝ => ∫ s : ℝ, heatKernel T (x - s) * backwardAiry T s)
      (∫ s : ℝ, heatAiryConvDerivT T₀ x s) T₀ :=
  (hasDerivAt_integral_heatAiryConv' hT₀ x).2

/-- The `T`-derivative of the integrand is integrable. -/
theorem integrable_heatAiryConvDerivT (hT₀ : 0 < T₀) (x : ℝ) :
    Integrable fun s : ℝ => heatAiryConvDerivT T₀ x s :=
  (hasDerivAt_integral_heatAiryConv' hT₀ x).1

/-- The pointwise identity: the `T`-derivative of the integrand equals
`∂²_s[heatKernel] · g − heatKernel · ∂²_s g` (the two heat equations). -/
theorem heatAiryConvDerivT_eq (hT : 0 < T) (x s : ℝ) :
    heatAiryConvDerivT T x s = iteratedDeriv 2 (heatKernel T) (x - s) * backwardAiry T s
      - heatKernel T (x - s) * iteratedDeriv 2 (backwardAiry T) s := by
  unfold heatAiryConvDerivT
  rw [iteratedDeriv_succ, iteratedDeriv_one, (hasDerivAt_deriv_heatKernel_v hT (x - s)).deriv,
    iteratedDeriv_succ, iteratedDeriv_one, (hasDerivAt_deriv_backwardAiry_s T s).deriv]
  ring

end HeatAiryConvolution

/-! ## Integration by parts on the whole real line -/

/-- Integration by parts on the whole real line for `C²` pairs with vanishing
boundary terms: `∫ u'' v = ∫ u v''`. -/
theorem integral_derivTwo_mul_eq_mul_derivTwo {u u' u'' v v' v'' : ℝ → ℝ}
    (hu : ∀ s : ℝ, HasDerivAt u (u' s) s) (hu' : ∀ s : ℝ, HasDerivAt u' (u'' s) s)
    (hv : ∀ s : ℝ, HasDerivAt v (v' s) s) (hv' : ∀ s : ℝ, HasDerivAt v' (v'' s) s)
    (hu''c : Continuous u'') (hv''c : Continuous v'')
    (hu''v : Integrable fun s => u'' s * v s) (huv'' : Integrable fun s => u s * v'' s)
    (hW1 : Tendsto (fun s => u' s * v s - u s * v' s) atTop (𝓝 0))
    (hW2 : Tendsto (fun s => u' s * v s - u s * v' s) atBot (𝓝 0)) :
    (∫ s : ℝ, u'' s * v s) = ∫ s : ℝ, u s * v'' s := by
  have hcont_u : Continuous u := continuous_iff_continuousAt.mpr fun s => (hu s).continuousAt
  have hcont_u' : Continuous u' := continuous_iff_continuousAt.mpr fun s => (hu' s).continuousAt
  have hcont_v : Continuous v := continuous_iff_continuousAt.mpr fun s => (hv s).continuousAt
  have hcont_v' : Continuous v' := continuous_iff_continuousAt.mpr fun s => (hv' s).continuousAt
  -- The Lagrange identity on every interval: `d/ds (u'v - uv') = u''v - uv''`,
  -- so FTC gives the identity directly.
  have hid : ∀ a b : ℝ, ∫ s in a..b, (u'' s * v s - u s * v'' s)
      = (u' b * v b - u b * v' b) - (u' a * v a - u a * v' a) := by
    intro a b
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _
      convert ((hu' x).mul (hv x)).sub ((hu x).mul (hv' x)) using 1
      ring
    · exact ((hu''c.mul hcont_v).sub (hcont_u.mul hv''c)).intervalIntegrable (μ := volume) a b
  set φ : ℝ → ℝ := fun s => u'' s * v s - u s * v'' s with hφ
  have hφint : Integrable φ := hu''v.sub huv''
  -- `∫ s in a..b φ → ∫ s in Iic b φ` as `a → -∞`
  have hleft : ∀ b : ℝ, Tendsto (fun a : ℝ => ∫ s in a..b, φ s) atBot
      (𝓝 (∫ s in Set.Iic b, φ s)) := by
    intro b
    have hconv : Tendsto (fun a : ℝ => ∫ s : ℝ, (Set.Ioc a b).indicator φ s) atBot
        (𝓝 (∫ s : ℝ, (Set.Iic b).indicator φ s)) := by
      apply tendsto_integral_filter_of_dominated_convergence (fun s => |φ s|)
      · exact Eventually.of_forall fun a =>
          hφint.aestronglyMeasurable.indicator measurableSet_Ioc
      · exact Eventually.of_forall fun a => Eventually.of_forall fun s =>
          (norm_indicator_le_norm_self _ _).trans_eq (Real.norm_eq_abs _)
      · exact hφint.abs
      · exact Eventually.of_forall fun s => by
          by_cases hs : s ≤ b
          · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hs) φ]
            apply Tendsto.congr' _ tendsto_const_nhds
            filter_upwards [eventually_le_atBot (s - 1)] with a ha
            rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨by linarith, hs⟩) φ]
          · have h1 : (Set.Iic b).indicator φ s = 0 :=
              Set.indicator_of_notMem (by simpa using hs) φ
            have h2 : (fun a : ℝ => (Set.Ioc a b).indicator φ s) = fun _ => 0 :=
              funext fun a => Set.indicator_of_notMem (fun h : s ∈ Set.Ioc a b => hs h.2) φ
            rw [h1, h2]
            exact tendsto_const_nhds
    rw [MeasureTheory.integral_indicator measurableSet_Iic] at hconv
    apply hconv.congr'
    filter_upwards [eventually_le_atBot b] with a ha
    rw [intervalIntegral.integral_of_le ha,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
  -- hence `∫ s in Iic b φ = u' b * v b - u b * v' b`
  have hstep : ∀ b : ℝ, (∫ s in Set.Iic b, φ s) = u' b * v b - u b * v' b := by
    intro b
    have h2' : Tendsto (fun a : ℝ => (u' b * v b - u b * v' b) - (u' a * v a - u a * v' a))
        atBot (𝓝 ((u' b * v b - u b * v' b) - 0)) := tendsto_const_nhds.sub hW2
    have h2 : Tendsto (fun a : ℝ => ∫ s in a..b, φ s) atBot
        (𝓝 ((u' b * v b - u b * v' b) - 0)) := by
      apply h2'.congr'
      filter_upwards [eventually_le_atBot b] with a ha
      exact (hid a b).symm
    have h3 := tendsto_nhds_unique (hleft b) h2
    rwa [sub_zero] at h3
  -- and `∫ s in Iic b φ → ∫ φ` as `b → ∞`, while the boundary vanishes
  have hright : Tendsto (fun b : ℝ => ∫ s in Set.Iic b, φ s) atTop (𝓝 (∫ s, φ s)) := by
    have hconv : Tendsto (fun b : ℝ => ∫ s : ℝ, (Set.Iic b).indicator φ s) atTop
        (𝓝 (∫ s : ℝ, φ s)) := by
      apply tendsto_integral_filter_of_dominated_convergence (fun s => |φ s|)
      · exact Eventually.of_forall fun b =>
          hφint.aestronglyMeasurable.indicator measurableSet_Iic
      · exact Eventually.of_forall fun b => Eventually.of_forall fun s =>
          (norm_indicator_le_norm_self _ _).trans_eq (Real.norm_eq_abs _)
      · exact hφint.abs
      · exact Eventually.of_forall fun s => by
          apply Tendsto.congr' _ tendsto_const_nhds
          filter_upwards [eventually_ge_atTop s] with b hb
          rw [Set.indicator_of_mem (Set.mem_Iic.mpr hb) φ]
    apply hconv.congr'
    refine Eventually.of_forall fun b => ?_
    show ∫ s : ℝ, (Set.Iic b).indicator φ s = ∫ s in Set.Iic b, φ s
    rw [← MeasureTheory.integral_indicator measurableSet_Iic]
  have htot : Tendsto (fun b : ℝ => ∫ s in Set.Iic b, φ s) atTop (𝓝 0) := by
    apply hW1.congr'
    exact Eventually.of_forall fun b => (hstep b).symm
  have hzero : (∫ s, φ s) = 0 := tendsto_nhds_unique hright htot
  rw [hφ, integral_sub hu''v huv''] at hzero
  exact sub_eq_zero.mp hzero

/-! ## Step (ii) of (1): the convolution is constant in `T` -/

section HeatAiryConvolutionIBP

/-- The pointwise value of `∂²_v heatKernel`. -/
theorem iterDerivTwo_heatKernel (hT : 0 < T) (v : ℝ) :
    iteratedDeriv 2 (heatKernel T) v = (v^2/(4*T^2) - 1/(2*T)) * heatKernel T v := by
  have h2 : iteratedDeriv 2 (heatKernel T) v = deriv (deriv (heatKernel T)) v := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, (hasDerivAt_deriv_heatKernel_v hT v).deriv]

/-- The pointwise value of `∂²_s backwardAiry`. -/
theorem iterDerivTwo_backwardAiry (T s : ℝ) :
    iteratedDeriv 2 (backwardAiry T) s = Real.exp (-(2/3)*T^3 - T*s)
      * ((s + 2*T^2) * airyAiReal (s + T^2) - 2*T * deriv airyAiReal (s + T^2)) := by
  have h2 : iteratedDeriv 2 (backwardAiry T) s = deriv (deriv (backwardAiry T)) s := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, (hasDerivAt_deriv_backwardAiry_s T s).deriv]

/-- `s ↦ ∂²_s[heatKernel T (x-s)]` is continuous. -/
theorem continuous_iterDerivTwo_heatKernel_sub (hT : 0 < T) (x : ℝ) :
    Continuous fun s : ℝ => iteratedDeriv 2 (heatKernel T) (x - s) := by
  rw [show (fun s : ℝ => iteratedDeriv 2 (heatKernel T) (x - s))
      = fun s => ((x - s)^2/(4*T^2) - 1/(2*T)) * heatKernel T (x - s)
      from funext fun s => iterDerivTwo_heatKernel hT (x - s)]
  exact ((by fun_prop : Continuous fun s : ℝ => (x - s)^2/(4*T^2) - 1/(2*T)).mul
    ((continuous_heatKernel T).comp (by fun_prop)))

/-- `s ↦ ∂²_s g_T(s)` is continuous. -/
theorem continuous_iterDerivTwo_backwardAiry (T : ℝ) :
    Continuous fun s : ℝ => iteratedDeriv 2 (backwardAiry T) s := by
  rw [show (fun s : ℝ => iteratedDeriv 2 (backwardAiry T) s)
      = fun s => Real.exp (-(2/3)*T^3 - T*s) * ((s + 2*T^2) * airyAiReal (s + T^2)
        - 2*T * deriv airyAiReal (s + T^2))
      from funext fun s => iterDerivTwo_backwardAiry T s]
  exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-(2/3)*T^3 - T*s)).mul
    (((by fun_prop : Continuous fun s : ℝ => s + 2*T^2).mul
      (continuous_airyAiReal.comp (by fun_prop))).sub
    ((by fun_prop : Continuous fun s : ℝ => 2*T).mul
      (continuous_deriv_airyAiReal.comp (by fun_prop))))

/-- Integrability of `∂²_s[heatKernel] · g_T`. -/
theorem integrable_iterDerivTwo_heatKernel_mul_backwardAiry (hT : 0 < T) (x : ℝ) :
    Integrable fun s : ℝ => iteratedDeriv 2 (heatKernel T) (x - s) * backwardAiry T s := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp T
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0 ⟨le_rfl, hT.le⟩ 0
    rw [abs_zero, mul_zero, Real.exp_zero, mul_one] at h
    have e : backwardAiry 0 0 = airyAiReal 0 := by simp [backwardAiry]
    rw [e] at h
    exact le_trans (abs_nonneg _) h
  have henvelope : Integrable fun s : ℝ =>
      ((1/(2*T) + 1/(4*T^2)) * (4*Real.pi*T)^(-1/2:ℝ) * C₀ * (2*(1+x^2))) * ((1 + s^2)
        * Real.exp (-(1/(4*T))*(s - x)^2 + T*|s|)) :=
    (integrable_one_add_sq_mul_exp_neg_sq_add_abs (b := 1/(4*T)) (by positivity) T x).const_mul _
  apply henvelope.mono'
  · exact ((continuous_iterDerivTwo_heatKernel_sub hT x).mul
      (continuous_backwardAiry_s T)).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_mul]
    have hg := hC₀ T ⟨hT.le, le_rfl⟩ s
    have hA : |(x - s)^2/(4*T^2) - 1/(2*T)| ≤ (1/(2*T) + 1/(4*T^2)) * (1 + (x - s)^2) := by
      have hpa : |(x - s)^2/(4*T^2)| ≤ (1/(4*T^2)) * (1 + (x - s)^2) := by
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (x - s)^2/(4*T^2))]
        rw [show (x - s)^2/(4*T^2) = (1/(4*T^2)) * (x - s)^2 by ring]
        exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (x - s)]) (by positivity)
      have hpb : |1/(2*T)| ≤ (1/(2*T)) * (1 + (x - s)^2) := by
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(2*T))]
        exact le_mul_of_one_le_right (by positivity) (by nlinarith [sq_nonneg (x - s)])
      calc |(x - s)^2/(4*T^2) - 1/(2*T)|
          = |(x - s)^2/(4*T^2) + -(1/(2*T))| := by rw [sub_eq_add_neg]
        _ ≤ |(x - s)^2/(4*T^2)| + |-(1/(2*T))| := abs_add_le _ _
        _ = |(x - s)^2/(4*T^2)| + |1/(2*T)| := by rw [abs_neg]
        _ ≤ (1/(4*T^2)) * (1 + (x - s)^2) + (1/(2*T)) * (1 + (x - s)^2) :=
            add_le_add hpa hpb
        _ = (1/(2*T) + 1/(4*T^2)) * (1 + (x - s)^2) := by ring
    have hsub : 1 + (x - s)^2 ≤ 2*(1+x^2)*(1+s^2) := by
      nlinarith [sq_nonneg (x - s), sq_nonneg (x + s), sq_nonneg x, sq_nonneg s,
        sq_nonneg (x * s)]
    calc |iteratedDeriv 2 (heatKernel T) (x - s)| * |backwardAiry T s|
        = |(x - s)^2/(4*T^2) - 1/(2*T)| * heatKernel T (x - s) * |backwardAiry T s| := by
          rw [iterDerivTwo_heatKernel hT (x - s), abs_mul,
            abs_of_nonneg (heatKernel_nonneg hT _)]
      _ ≤ ((1/(2*T) + 1/(4*T^2)) * (1 + (x - s)^2)) * ((4*Real.pi*T)^(-1/2:ℝ)
            * Real.exp (-(x - s)^2/(4*T))) * (C₀ * Real.exp (T * |s|)) :=
          mul_le_mul (mul_le_mul hA (le_rfl) (heatKernel_nonneg hT _)
            (by positivity)) hg (abs_nonneg _)
            (mul_nonneg (by positivity) (mul_nonneg (by positivity) (Real.exp_pos _).le))
      _ = ((1/(2*T) + 1/(4*T^2)) * (4*Real.pi*T)^(-1/2:ℝ) * C₀) * (1 + (x - s)^2)
            * (Real.exp (-(x - s)^2/(4*T)) * Real.exp (T * |s|)) := by ring
      _ ≤ ((1/(2*T) + 1/(4*T^2)) * (4*Real.pi*T)^(-1/2:ℝ) * C₀) * (2*(1+x^2)*(1+s^2))
            * (Real.exp (-(x - s)^2/(4*T)) * Real.exp (T * |s|)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsub (by positivity)) (by positivity)
      _ = ((1/(2*T) + 1/(4*T^2)) * (4*Real.pi*T)^(-1/2:ℝ) * C₀ * (2*(1+x^2)))
            * ((1 + s^2) * Real.exp (-(1/(4*T))*(s - x)^2 + T*|s|)) := by
          have hexp : -(x - s)^2/(4*T) = -(1/(4*T))*(s - x)^2 := by ring
          rw [← Real.exp_add, hexp]
          ring

/-- Integrability of `heatKernel · ∂²_s g_T`. -/
theorem integrable_heatKernel_mul_iterDerivTwo_backwardAiry (hT : 0 < T) (x : ℝ) :
    Integrable fun s : ℝ => heatKernel T (x - s) * iteratedDeriv 2 (backwardAiry T) s := by
  obtain ⟨C₂, hC₂⟩ := backwardAiry_deriv_two_s_abs_le_exp hT
  have hC₂nn : 0 ≤ C₂ := by
    have h := hC₂ 0
    rw [abs_zero, mul_zero, Real.exp_zero, mul_one, zero_pow two_ne_zero, add_zero,
      mul_one] at h
    exact le_trans (abs_nonneg _) h
  have henvelope : Integrable fun s : ℝ =>
      ((4*Real.pi*T)^(-1/2:ℝ) * C₂) * ((1 + s^2)
        * Real.exp (-(1/(4*T))*(s - x)^2 + T*|s|)) :=
    (integrable_one_add_sq_mul_exp_neg_sq_add_abs (b := 1/(4*T)) (by positivity) T x).const_mul _
  apply henvelope.mono'
  · exact (((continuous_heatKernel T).comp (by fun_prop)).mul
      (continuous_iterDerivTwo_backwardAiry T)).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hT _)]
    have hg := hC₂ s
    calc heatKernel T (x - s) * |iteratedDeriv 2 (backwardAiry T) s|
        ≤ heatKernel T (x - s) * (C₂ * (1 + s^2) * Real.exp (T * |s|)) :=
          mul_le_mul_of_nonneg_left hg (heatKernel_nonneg hT _)
      _ = ((4*Real.pi*T)^(-1/2:ℝ) * C₂) * ((1 + s^2) * Real.exp (-(1/(4*T))*(s - x)^2 + T*|s|)) := by
          unfold heatKernel
          have hexp : -(x - s)^2/(4*T) = -(1/(4*T))*(s - x)^2 := by ring
          rw [hexp, show (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-(1/(4*T))*(s - x)^2)
                * (C₂ * (1 + s^2) * Real.exp (T*|s|))
              = ((4*Real.pi*T)^(-1/2:ℝ) * C₂ * (1 + s^2))
                * (Real.exp (-(1/(4*T))*(s - x)^2) * Real.exp (T*|s|)) from by ring,
            ← Real.exp_add]
          ring
      _ = (4*Real.pi*T)^(-1/2:ℝ) * C₂ * ((1 + s^2)
            * Real.exp (-(1/(4*T))*(s - x)^2 + T*|s|)) := by ring

end HeatAiryConvolutionIBP

/-! ## Step (ii) of (1) concluded: the boundary terms vanish and `deriv F = 0` -/

section HeatAiryConvolutionConst

/-- The IBP boundary function `W(s) = u' s · v s − u s · v' s` for
`u = heatKernel T (x - ·)`, `v = backwardAiry T` vanishes at `+∞` and `-∞`. -/
theorem heatAiryConv_boundary_tendsto_zero (hT : 0 < T) (x : ℝ) :
    Tendsto (fun s : ℝ => (-deriv (heatKernel T) (x - s)) * backwardAiry T s
        - heatKernel T (x - s) * deriv (backwardAiry T) s) atTop (𝓝 0)
    ∧ Tendsto (fun s : ℝ => (-deriv (heatKernel T) (x - s)) * backwardAiry T s
        - heatKernel T (x - s) * deriv (backwardAiry T) s) atBot (𝓝 0) := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp T
  obtain ⟨C₁, hC₁⟩ := backwardAiry_deriv_s_abs_le_exp hT
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0 ⟨le_rfl, hT.le⟩ 0
    rw [abs_zero, mul_zero, Real.exp_zero, mul_one] at h
    have e : backwardAiry 0 0 = airyAiReal 0 := by simp [backwardAiry]
    rw [e] at h
    exact le_trans (abs_nonneg _) h
  have hC₁nn : 0 ≤ C₁ := by
    have h := hC₁ 0
    rw [abs_zero, mul_zero, Real.exp_zero, mul_one, zero_pow two_ne_zero, add_zero,
      mul_one] at h
    exact le_trans (abs_nonneg _) h
  -- the polynomial absorb: `1 + s² ≤ (1 + 2/T²) e^{T|s|}`
  have hpoly : ∀ s : ℝ, 1 + s^2 ≤ (1 + 2/T^2) * Real.exp (T * |s|) := by
    intro s
    have h2 := abs_pow_le_factorial_mul_exp 2 hT s
    rw [show ((2 : ℕ).factorial : ℝ) = 2 by norm_num [Nat.factorial], sq_abs] at h2
    calc 1 + s^2 ≤ Real.exp (T * |s|) + (2/T^2) * Real.exp (T * |s|) :=
          add_le_add (Real.one_le_exp (by positivity)) h2
      _ = (1 + 2/T^2) * Real.exp (T * |s|) := by ring
  -- the pointwise bound on `W`
  have hbound : ∀ s : ℝ, |(-deriv (heatKernel T) (x - s)) * backwardAiry T s
        - heatKernel T (x - s) * deriv (backwardAiry T) s|
      ≤ ((4*Real.pi*T)^(-1/2:ℝ) * ((2*(1+x^2))/(2*T) * C₀ + C₁) * (1 + 2/T^2))
        * Real.exp (-(x - s)^2/(4*T) + (2*T)*|s|) := by
    intro s
    have hu' : |deriv (heatKernel T) (x - s)|
        ≤ (1/(2*T)) * (1 + (x - s)^2) * heatKernel T (x - s) := by
      rw [(hasDerivAt_heatKernel_v hT (x - s)).deriv, abs_mul,
        abs_of_nonneg (heatKernel_nonneg hT _)]
      calc |(-((x - s)/(2*T)))| * heatKernel T (x - s)
          = (|x - s|/(2*T)) * heatKernel T (x - s) := by
            congr 1
            rw [abs_neg, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*T)]
        _ ≤ ((1 + (x - s)^2)/(2*T)) * heatKernel T (x - s) := by
            rw [div_eq_inv_mul, div_eq_inv_mul]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (abs_le_one_add_sq _) (by positivity))
              (heatKernel_nonneg hT _)
        _ = (1/(2*T)) * (1 + (x - s)^2) * heatKernel T (x - s) := by ring
    have hsub : 1 + (x - s)^2 ≤ 2*(1+x^2)*(1+s^2) := by
      nlinarith [sq_nonneg (x - s), sq_nonneg (x + s), sq_nonneg x, sq_nonneg s,
        sq_nonneg (x * s)]
    have hbound1 : |(-deriv (heatKernel T) (x - s)) * backwardAiry T s|
        ≤ ((2*(1+x^2))/(2*T) * C₀ * (4*Real.pi*T)^(-1/2:ℝ))
          * ((1 + s^2) * Real.exp (-(x - s)^2/(4*T) + T*|s|)) := by
      have h1 : |(-deriv (heatKernel T) (x - s)) * backwardAiry T s|
          = |deriv (heatKernel T) (x - s)| * |backwardAiry T s| := by
        rw [neg_mul, abs_neg, abs_mul]
      have h2 : |deriv (heatKernel T) (x - s)| * |backwardAiry T s|
          ≤ ((1/(2*T)) * (1 + (x - s)^2) * heatKernel T (x - s))
            * (C₀ * Real.exp (T * |s|)) :=
        mul_le_mul hu' (hC₀ T ⟨hT.le, le_rfl⟩ s) (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (heatKernel_nonneg hT _))
      have h3 : ((1/(2*T)) * (1 + (x - s)^2) * heatKernel T (x - s))
            * (C₀ * Real.exp (T * |s|))
          = ((1/(2*T)) * C₀) * (1 + (x - s)^2)
            * (heatKernel T (x - s) * Real.exp (T * |s|)) := by ring
      have h4 : ((1/(2*T)) * C₀) * (1 + (x - s)^2)
            * (heatKernel T (x - s) * Real.exp (T * |s|))
          ≤ ((1/(2*T)) * C₀) * (2*(1+x^2)*(1+s^2))
            * (heatKernel T (x - s) * Real.exp (T * |s|)) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg (heatKernel_nonneg hT _) (Real.exp_pos _).le)
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) hC₀nn)
        exact hsub
      rw [h1]
      calc |deriv (heatKernel T) (x - s)| * |backwardAiry T s|
          ≤ ((1/(2*T)) * (1 + (x - s)^2) * heatKernel T (x - s))
            * (C₀ * Real.exp (T * |s|)) := h2
        _ = ((1/(2*T)) * C₀) * (1 + (x - s)^2)
            * (heatKernel T (x - s) * Real.exp (T * |s|)) := h3
        _ ≤ ((1/(2*T)) * C₀) * (2*(1+x^2)*(1+s^2))
            * (heatKernel T (x - s) * Real.exp (T * |s|)) := h4
        _ = ((2*(1+x^2))/(2*T) * C₀ * (4*Real.pi*T)^(-1/2:ℝ))
            * ((1 + s^2) * Real.exp (-(x - s)^2/(4*T) + T*|s|)) := by
            unfold heatKernel
            rw [Real.exp_add]
            ring
    have hbound2 : |heatKernel T (x - s) * deriv (backwardAiry T) s|
        ≤ ((4*Real.pi*T)^(-1/2:ℝ) * C₁)
          * ((1 + s^2) * Real.exp (-(x - s)^2/(4*T) + T*|s|)) := by
      have h1 : |heatKernel T (x - s) * deriv (backwardAiry T) s|
          ≤ heatKernel T (x - s) * (C₁ * (1 + s^2) * Real.exp (T * |s|)) := by
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hT _)]
        exact mul_le_mul_of_nonneg_left (hC₁ s) (heatKernel_nonneg hT _)
      calc |heatKernel T (x - s) * deriv (backwardAiry T) s|
          ≤ heatKernel T (x - s) * (C₁ * (1 + s^2) * Real.exp (T * |s|)) := h1
        _ = ((4*Real.pi*T)^(-1/2:ℝ) * C₁)
            * ((1 + s^2) * Real.exp (-(x - s)^2/(4*T) + T*|s|)) := by
            unfold heatKernel
            rw [Real.exp_add]
            ring
    calc |(-deriv (heatKernel T) (x - s)) * backwardAiry T s
          - heatKernel T (x - s) * deriv (backwardAiry T) s|
        ≤ |(-deriv (heatKernel T) (x - s)) * backwardAiry T s|
          + |heatKernel T (x - s) * deriv (backwardAiry T) s| := by
          rw [sub_eq_add_neg, ← abs_neg (heatKernel T (x - s) * deriv (backwardAiry T) s)]
          exact abs_add_le _ _
      _ ≤ ((2*(1+x^2))/(2*T) * C₀ * (4*Real.pi*T)^(-1/2:ℝ))
            * ((1 + s^2) * Real.exp (-(x - s)^2/(4*T) + T*|s|))
          + ((4*Real.pi*T)^(-1/2:ℝ) * C₁)
            * ((1 + s^2) * Real.exp (-(x - s)^2/(4*T) + T*|s|)) :=
          add_le_add hbound1 hbound2
      _ = ((4*Real.pi*T)^(-1/2:ℝ) * ((2*(1+x^2))/(2*T) * C₀ + C₁))
          * ((1 + s^2) * Real.exp (-(x - s)^2/(4*T) + T*|s|)) := by ring
      _ ≤ ((4*Real.pi*T)^(-1/2:ℝ) * ((2*(1+x^2))/(2*T) * C₀ + C₁))
          * ((1 + 2/T^2) * Real.exp (-(x - s)^2/(4*T) + (2*T)*|s|)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc (1 + s^2) * Real.exp (-(x - s)^2/(4*T) + T*|s|)
              = Real.exp (-(x - s)^2/(4*T)) * ((1 + s^2) * Real.exp (T*|s|)) := by
                rw [Real.exp_add]
                ring
            _ ≤ Real.exp (-(x - s)^2/(4*T))
                * (((1 + 2/T^2) * Real.exp (T*|s|)) * Real.exp (T*|s|)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul (hpoly s) le_rfl (Real.exp_pos _).le (by positivity))
                  (Real.exp_pos _).le
            _ = (1 + 2/T^2) * Real.exp (-(x - s)^2/(4*T) + (2*T)*|s|) := by
                rw [Real.exp_add,
                  mul_assoc ((1:ℝ) + 2/T^2) (Real.exp (T*|s|)) (Real.exp (T*|s|)),
                  ← Real.exp_add, show T*|s| + T*|s| = 2*T*|s| by ring]
                ring
      _ = ((4*Real.pi*T)^(-1/2:ℝ) * ((2*(1+x^2))/(2*T) * C₀ + C₁) * (1 + 2/T^2))
          * Real.exp (-(x - s)^2/(4*T) + (2*T)*|s|) := by ring
  -- conclude by squeezing against the master envelope
  have hE : Tendsto (fun s : ℝ => ((4*Real.pi*T)^(-1/2:ℝ) * ((2*(1+x^2))/(2*T) * C₀ + C₁)
        * (1 + 2/T^2)) * Real.exp (-(x - s)^2/(4*T) + (2*T)*|s|)) atTop (𝓝 0)
      ∧ Tendsto (fun s : ℝ => ((4*Real.pi*T)^(-1/2:ℝ) * ((2*(1+x^2))/(2*T) * C₀ + C₁)
        * (1 + 2/T^2)) * Real.exp (-(x - s)^2/(4*T) + (2*T)*|s|)) atBot (𝓝 0) := by
    have hexp : ∀ s : ℝ, -(1/(4*T))*(s - x)^2 + (2*T)*|s|
        = -(x - s)^2/(4*T) + (2*T)*|s| := fun s => by ring
    have h1 := tendsto_exp_neg_sq_add_abs_atTop (b := 1/(4*T)) (by positivity) (2*T) x
    have h2 := tendsto_exp_neg_sq_add_abs_atBot (b := 1/(4*T)) (by positivity) (2*T) x
    constructor
    · have h := h1.const_mul ((4*Real.pi*T)^(-1/2:ℝ) * ((2*(1+x^2))/(2*T) * C₀ + C₁)
        * (1 + 2/T^2))
      rw [mul_zero] at h
      exact h.congr' (Eventually.of_forall fun s =>
        congrArg (fun E : ℝ => ((4*Real.pi*T)^(-1/2:ℝ) * ((2*(1+x^2))/(2*T) * C₀ + C₁)
          * (1 + 2/T^2)) * Real.exp E) (hexp s))
    · have h := h2.const_mul ((4*Real.pi*T)^(-1/2:ℝ) * ((2*(1+x^2))/(2*T) * C₀ + C₁)
        * (1 + 2/T^2))
      rw [mul_zero] at h
      exact h.congr' (Eventually.of_forall fun s =>
        congrArg (fun E : ℝ => ((4*Real.pi*T)^(-1/2:ℝ) * ((2*(1+x^2))/(2*T) * C₀ + C₁)
          * (1 + 2/T^2)) * Real.exp E) (hexp s))
  constructor
  · apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    exact squeeze_zero' (Eventually.of_forall fun s => abs_nonneg _)
      (Eventually.of_forall fun s => hbound s) hE.1
  · apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    exact squeeze_zero' (Eventually.of_forall fun s => abs_nonneg _)
      (Eventually.of_forall fun s => hbound s) hE.2

/-- **Step (ii) of (1)**: the `T`-derivative of the heat–Airy convolution vanishes on `(0, ∞)`. -/
theorem heatAiryConv_deriv_eq_zero (hT : 0 < T) (x : ℝ) :
    deriv (fun T : ℝ => ∫ s : ℝ, heatKernel T (x - s) * backwardAiry T s) T = 0 := by
  obtain ⟨hW1, hW2⟩ := heatAiryConv_boundary_tendsto_zero hT x
  have hu : ∀ s : ℝ, HasDerivAt (fun s : ℝ => heatKernel T (x - s))
      (-deriv (heatKernel T) (x - s)) s := by
    intro s
    have h := (hasDerivAt_heatKernel_v hT (x - s)).comp s
      ((hasDerivAt_const s x).sub (hasDerivAt_id' s))
    convert h using 1
    · ext s'
      rfl
    · rw [(hasDerivAt_heatKernel_v hT (x - s)).deriv]
      ring
  have hu' : ∀ s : ℝ, HasDerivAt (fun s : ℝ => -deriv (heatKernel T) (x - s))
      (iteratedDeriv 2 (heatKernel T) (x - s)) s := by
    intro s
    have h := (hasDerivAt_deriv_heatKernel_v hT (x - s)).comp s
      ((hasDerivAt_const s x).sub (hasDerivAt_id' s))
    convert h.neg using 1
    · ext s'
      rfl
    · rw [iterDerivTwo_heatKernel hT (x - s)]
      ring
  have hv : ∀ s : ℝ, HasDerivAt (backwardAiry T) (deriv (backwardAiry T) s) s := by
    intro s
    convert hasDerivAt_backwardAiry_s T s using 1
    exact (hasDerivAt_backwardAiry_s T s).deriv
  have hv' : ∀ s : ℝ, HasDerivAt (deriv (backwardAiry T))
      (iteratedDeriv 2 (backwardAiry T) s) s := by
    intro s
    convert hasDerivAt_deriv_backwardAiry_s T s using 1
    rw [iterDerivTwo_backwardAiry]
  have hibp := integral_derivTwo_mul_eq_mul_derivTwo hu hu' hv hv'
    (continuous_iterDerivTwo_heatKernel_sub hT x) (continuous_iterDerivTwo_backwardAiry T)
    (integrable_iterDerivTwo_heatKernel_mul_backwardAiry hT x)
    (integrable_heatKernel_mul_iterDerivTwo_backwardAiry hT x) hW1 hW2
  rw [(hasDerivAt_integral_heatAiryConv hT x).deriv,
    show (∫ s : ℝ, heatAiryConvDerivT T x s)
      = ∫ s : ℝ, (iteratedDeriv 2 (heatKernel T) (x - s)) * backwardAiry T s
        - heatKernel T (x - s) * iteratedDeriv 2 (backwardAiry T) s from
      integral_congr_ae (Eventually.of_forall fun s => heatAiryConvDerivT_eq hT x s),
    integral_sub (integrable_iterDerivTwo_heatKernel_mul_backwardAiry hT x)
      (integrable_heatKernel_mul_iterDerivTwo_backwardAiry hT x),
    hibp]
  exact sub_self _

/-- **Step (iv) of (1)**: the heat–Airy convolution is constant in `T` on `(0, ∞)`. -/
theorem heatAiryConv_eq_of_pos (x : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ s : ℝ, heatKernel a (x - s) * backwardAiry a s)
      = ∫ s : ℝ, heatKernel b (x - s) * backwardAiry b s := by
  have key : ∀ {a b : ℝ}, 0 < a → a < b →
      (∫ s : ℝ, heatKernel a (x - s) * backwardAiry a s)
        = ∫ s : ℝ, heatKernel b (x - s) * backwardAiry b s := by
    intro a b ha hab
    obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_slope
      (fun T : ℝ => ∫ s : ℝ, heatKernel T (x - s) * backwardAiry T s) hab
      (fun T hT => ((hasDerivAt_integral_heatAiryConv (ha.trans_le hT.1)
        x).continuousAt).continuousWithinAt)
      (fun T hT => ((hasDerivAt_integral_heatAiryConv (ha.trans (Set.mem_Ioo.mp hT).1)
        x).differentiableAt).differentiableWithinAt)
    have hzero : deriv (fun T : ℝ => ∫ s : ℝ, heatKernel T (x - s) * backwardAiry T s) c
        = 0 := heatAiryConv_deriv_eq_zero (ha.trans (Set.mem_Ioo.mp hc).1) x
    rw [hzero, eq_comm, div_eq_zero_iff] at hderiv
    rcases hderiv with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h (sub_ne_zero.mpr hab.ne')
  rcases le_total a b with h | h
  · rcases h.eq_or_lt with rfl | hlt
    · rfl
    · exact key ha hlt
  · rcases h.eq_or_lt with rfl | hlt
    · rfl
    · exact (key hb hlt).symm

end HeatAiryConvolutionConst

/-! ## Step (iii) of (1): the mollifier limit `T → 0⁺` -/

section Mollifier

/-- Dominated-on-a-set integrability transfer (whole-line `mono'` through
indicators). -/
theorem integrableOn_of_abs_le_on {f g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hg : IntegrableOn g s) (hf : AEStronglyMeasurable f)
    (hbound : ∀ a ∈ s, |f a| ≤ g a) : IntegrableOn f s := by
  rw [← integrable_indicator_iff hs]
  rw [← integrable_indicator_iff hs] at hg
  exact hg.mono' (hf.indicator hs) (Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs]
    rcases em (a ∈ s) with ha | ha
    · rw [Set.indicator_of_mem ha f, Set.indicator_of_mem ha g]
      exact hbound a ha
    · rw [Set.indicator_of_notMem ha f, Set.indicator_of_notMem ha g, abs_zero])

/-- `T^{3/2} → 0` on `𝓝[>] 0`. -/
theorem tendsto_rpow_three_halves_nhdsWithin_Ioi_zero :
    Tendsto (fun T : ℝ => T^((3/2 : ℝ))) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun T : ℝ => T^((3/2 : ℝ))) (𝓝[>] 0) (𝓝 (0^((3/2 : ℝ)))) :=
    (Real.continuousAt_rpow_const (0:ℝ) (3/2) (Or.inr (by norm_num))).mono_left
      nhdsWithin_le_nhds
  rwa [Real.zero_rpow (by norm_num : (3/2:ℝ) ≠ 0)] at h

/-- **Pointwise Gaussian-tail domination**: for `T ≤ δ/(8(|K|+1))` and `v > δ`,
`heatKernel T v · e^{Kv} ≤ (4πT)^{-1/2} e^{-v²/(8T)}`. -/
theorem heatKernel_mul_exp_le {δ : ℝ} (hδ : 0 < δ) (K : ℝ)
    {T : ℝ} (hT : T ∈ Set.Ioc 0 (δ / (8*(|K| + 1)))) {v : ℝ} (hv : v ∈ Set.Ioi δ) :
    heatKernel T v * Real.exp (K * v)
      ≤ (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-v^2/(8*T)) := by
  have hTpos : 0 < T := hT.1
  have hvpos : 0 < v := hδ.trans hv
  set K' := |K| + 1 with hK'
  have hK'pos : 0 < K' := by positivity
  have hKv : K * v ≤ v^2/(8*T) := by
    have h2 : 8*K'*T ≤ v := by
      calc 8*K'*T ≤ 8*K'*(δ / (8*K')) :=
          mul_le_mul_of_nonneg_left hT.2 (by positivity)
        _ = δ := by field_simp [hK'pos.ne']
        _ ≤ v := hv.le
    have h3 : (8*T) * K' ≤ v := by
      calc (8*T) * K' = 8*K'*T := by ring
        _ ≤ v := h2
    have h4 : K' * v ≤ v * (v/(8*T)) := by
      rw [mul_comm K' v]
      apply mul_le_mul_of_nonneg_left _ hvpos.le
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 8*T)]
      calc K' * (8*T) = (8*T) * K' := by ring
        _ ≤ v := h3
    calc K * v ≤ K' * v :=
        mul_le_mul_of_nonneg_right
          (by rw [hK']; exact (le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))
          hvpos.le
      _ ≤ v * (v/(8*T)) := h4
      _ = v^2/(8*T) := by field_simp
  have hexp : -v^2/(4*T) + K*v ≤ -v^2/(8*T) := by
    have h6 : K*v ≤ v^2/(4*T) - v^2/(8*T) := by
      have e : v^2/(4*T) - v^2/(8*T) = v^2/(8*T) := by field_simp; ring
      rw [e]
      exact hKv
    calc -v^2/(4*T) + K*v ≤ -v^2/(4*T) + (v^2/(4*T) - v^2/(8*T)) :=
          add_le_add le_rfl h6
      _ = -v^2/(8*T) := by ring
  unfold heatKernel
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (Real.rpow_nonneg (by positivity) _)

/-- **The weighted Gaussian tail vanishes as `T → 0⁺`**:
for `0 < δ` and any `K`, `∫ v > δ, heatKernel T v · e^{Kv} → 0` as `T → 0⁺`. -/
theorem tendsto_integral_heatKernel_mul_exp_Ioi_zero {δ : ℝ} (hδ : 0 < δ) (K : ℝ) :
    Tendsto (fun T : ℝ => ∫ v in Set.Ioi δ, heatKernel T v * Real.exp (K * v))
      (𝓝[>] 0) (𝓝 0) := by
  set K' := |K| + 1 with hK'
  have hK'pos : 0 < K' := by positivity
  have hT₀pos : 0 < δ / (8 * K') := by positivity
  -- the pointwise bound is `heatKernel_mul_exp_le`
  have hpt : ∀ T ∈ Set.Ioc 0 (δ / (8*K')), ∀ v ∈ Set.Ioi δ,
      heatKernel T v * Real.exp (K * v)
        ≤ (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-v^2/(8*T)) :=
    fun T hT v hv => heatKernel_mul_exp_le hδ K hT hv
  -- the tail bound: `Tail T ≤ C·T^{3/2}`
  have hbound : ∀ T ∈ Set.Ioc 0 (δ / (8*K')),
      (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (K * v))
        ≤ (4/(δ * (4*Real.pi)^((1/2 : ℝ)))) * (8/δ^2) * T^((3/2 : ℝ)) := by
    intro T hT
    have hTpos : 0 < T := hT.1
    have hintR : IntegrableOn (fun v : ℝ => (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-v^2/(8*T)))
        (Set.Ioi δ) := by
      have h2T : (0:ℝ) < 2*T := by positivity
      have h := integrableOn_exp_neg_sq_div_Ioi h2T δ
      have heq : (fun d : ℝ => Real.exp (-d^2/(4*(2*T))))
          = fun d => Real.exp (-d^2/(8*T)) := by
        funext d
        congr 1
        ring
      rw [heq] at h
      exact h.const_mul _
    have hintL : IntegrableOn (fun v : ℝ => heatKernel T v * Real.exp (K * v))
        (Set.Ioi δ) := by
      apply integrableOn_of_abs_le_on measurableSet_Ioi hintR
      · exact ((continuous_heatKernel T).mul (by fun_prop)).aestronglyMeasurable
      · intro v hv
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hTpos _),
          abs_of_nonneg (Real.exp_pos _).le]
        exact hpt T hT v hv
    have hle : ∫ v in Set.Ioi δ, heatKernel T v * Real.exp (K * v)
        ≤ ∫ v in Set.Ioi δ, (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-v^2/(8*T)) :=
      setIntegral_mono_on hintL hintR measurableSet_Ioi (hpt T hT)
    have hR : ∫ v in Set.Ioi δ, (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-v^2/(8*T))
        = (4*Real.pi*T)^(-1/2:ℝ) * gaussianTail (2*T) δ := by
      rw [integral_const_mul]
      congr 1
      unfold gaussianTail
      congr 1
      ext d
      congr 1
      ring
    rw [hR] at hle
    have hG : gaussianTail (2*T) δ ≤ (2*(2*T)/δ) * Real.exp (-δ^2/(4*(2*T))) :=
      gaussianTail_le (by positivity) hδ
    have hE : Real.exp (-δ^2/(4*(2*T))) ≤ 8*T/δ^2 := by
      have h1 : δ^2/(8*T) ≤ Real.exp (δ^2/(8*T)) :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
      have hX : 0 < δ^2/(8*T) := by positivity
      have e : -δ^2/(4*(2*T)) = -(δ^2/(8*T)) := by ring
      rw [e, Real.exp_neg, show (8*T/δ^2) = (δ^2/(8*T))⁻¹ by rw [inv_div]]
      exact (inv_le_inv₀ (Real.exp_pos _) hX).mpr h1
    have e3 : T^(-1/2 : ℝ) * T * T = T^(3/2 : ℝ) := by
      have h1 : T^(-1/2 : ℝ) * T^(1:ℝ) * T^(1:ℝ) = T^((-1/2:ℝ) + 1 + 1) := by
        rw [Real.rpow_add hTpos, Real.rpow_add hTpos]
      rw [show ((-1/2:ℝ) + 1 + 1) = 3/2 by norm_num, Real.rpow_one] at h1
      exact h1
    have e4 : (4*Real.pi*T)^(-1/2:ℝ) = (4*Real.pi)^(-1/2:ℝ) * T^(-1/2 : ℝ) :=
      Real.mul_rpow (by positivity) (by positivity)
    calc ∫ v in Set.Ioi δ, heatKernel T v * Real.exp (K * v)
        ≤ (4*Real.pi*T)^(-1/2:ℝ) * gaussianTail (2*T) δ := hle
      _ ≤ (4*Real.pi*T)^(-1/2:ℝ) * ((2*(2*T)/δ) * Real.exp (-δ^2/(4*(2*T)))) :=
          mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg (by positivity) _)
      _ ≤ (4*Real.pi*T)^(-1/2:ℝ) * ((2*(2*T)/δ) * (8*T/δ^2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hE (by positivity)) (Real.rpow_nonneg (by positivity) _)
      _ = (4/(δ * (4*Real.pi)^((1/2 : ℝ)))) * (8/δ^2) * T^((3/2 : ℝ)) := by
          rw [e4]
          calc (4*Real.pi)^(-1/2:ℝ) * T^(-1/2:ℝ) * ((2*(2*T)/δ) * (8*T/δ^2))
              = (4*Real.pi)^(-1/2:ℝ) * (32/(δ*δ^2)) * (T^(-1/2:ℝ) * T * T) := by ring
            _ = (4/(δ * (4*Real.pi)^((1/2 : ℝ)))) * (8/δ^2) * T^((3/2 : ℝ)) := by
                rw [e3, show (-1/2 : ℝ) = -(1/2 : ℝ) by ring,
                  Real.rpow_neg (by positivity : (0:ℝ) ≤ 4*Real.pi)]
                field_simp
                ring
  -- squeeze
  apply squeeze_zero'
  · filter_upwards [self_mem_nhdsWithin] with T hT
    exact setIntegral_nonneg measurableSet_Ioi
      (fun v _ => mul_nonneg (heatKernel_nonneg hT _) (Real.exp_pos _).le)
  · filter_upwards [Ioo_mem_nhdsGT hT₀pos] with T hT
    exact hbound T ⟨hT.1, hT.2.le⟩
  · have h := tendsto_rpow_three_halves_nhdsWithin_Ioi_zero.const_mul
      ((4/(δ * (4*Real.pi)^((1/2 : ℝ)))) * (8/δ^2))
    rwa [mul_zero] at h

/-- The substitution `v = x - s`: the convolution equals
`∫ v, heatKernel T v · backwardAiry T (x - v)`. -/
theorem heatAiryConv_eq_conv_sub (x T : ℝ) :
    (∫ s : ℝ, heatKernel T (x - s) * backwardAiry T s)
      = ∫ v : ℝ, heatKernel T v * backwardAiry T (x - v) := by
  set G : ℝ → ℝ := fun v => heatKernel T v * backwardAiry T (x - v) with hG
  have heq : (fun s : ℝ => heatKernel T (x - s) * backwardAiry T s)
      = fun s => G (x - s) := by
    funext s
    show heatKernel T (x - s) * backwardAiry T s
        = heatKernel T (x - s) * backwardAiry T (x - (x - s))
    rw [show x - (x - s) = s by ring]
  rw [heq]
  have h2 : (∫ s : ℝ, G (x - s)) = ∫ s : ℝ, G (-s) := by
    have h3 := MeasureTheory.integral_sub_right_eq_self (μ := volume) (fun s : ℝ => G (-s)) x
    have h4 : (fun s : ℝ => G (x - s)) = fun s : ℝ => G (-(s - x)) := by
      funext s
      congr 1
      ring
    rw [h4]
    exact h3
  have h5 : (∫ s : ℝ, G (-s)) = ∫ s : ℝ, G s :=
    MeasureTheory.integral_neg_eq_self G volume
  exact h2.trans h5

/-- Integrability of the `v`-form of the convolution. -/
theorem integrable_heatKernel_mul_backwardAiry_sub (hT : 0 < T) (x : ℝ) :
    Integrable fun v : ℝ => heatKernel T v * backwardAiry T (x - v) := by
  have hH := integrable_heatKernel_mul_backwardAiry hT x
  have h1 : Integrable fun v : ℝ => heatKernel T (x - -(v - x)) * backwardAiry T (-(v - x)) :=
    (hH.comp_neg).comp_sub_right x
  convert h1 using 1
  funext v
  congr 2
  · congr 1
    ring
  · ring

/-- The mollifier error identity: `F(T) - Ai(x) = ∫ v, p_T(v)·(g_T(x-v) - Ai x)`. -/
theorem heatAiryConv_sub_eq (hT : 0 < T) (x : ℝ) :
    (∫ s : ℝ, heatKernel T (x - s) * backwardAiry T s) - airyAiReal x
      = ∫ v : ℝ, heatKernel T v * (backwardAiry T (x - v) - airyAiReal x) := by
  rw [heatAiryConv_eq_conv_sub]
  have h1 : airyAiReal x = ∫ v : ℝ, heatKernel T v * airyAiReal x := by
    rw [integral_mul_const, integral_heatKernel hT, one_mul]
  nth_rewrite 1 [h1]
  rw [← integral_sub (integrable_heatKernel_mul_backwardAiry_sub hT x)
    ((integrable_heatKernel hT).mul_const _)]
  apply integral_congr_ae
  filter_upwards with v
  ring

/-- `backwardAiry 0 = Ai` pointwise. -/
theorem backwardAiry_zero (s : ℝ) : backwardAiry 0 s = airyAiReal s := by
  simp [backwardAiry]

/-- **Step (iii) of (1)**: the mollifier limit: `F(T) → Ai(x)` as `T → 0⁺`. -/
theorem tendsto_heatAiryConv_zero (x : ℝ) :
    Tendsto (fun T : ℝ => ∫ s : ℝ, heatKernel T (x - s) * backwardAiry T s)
      (𝓝[>] 0) (𝓝 (airyAiReal x)) := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp 1
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0 ⟨le_rfl, zero_le_one⟩ 0
    rw [abs_zero, one_mul, Real.exp_zero, mul_one] at h
    have e : backwardAiry 0 0 = airyAiReal 0 := by simp [backwardAiry]
    rw [e] at h
    exact le_trans (abs_nonneg _) h
  -- uniform continuity of `(T, s) ↦ backwardAiry T s` on the compact `[0,1]×[x−1, x+1]`
  have hUC : UniformContinuousOn (fun p : ℝ × ℝ => backwardAiry p.1 p.2)
      (Set.Icc 0 1 ×ˢ Set.Icc (x-1) (x+1)) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
      continuous_backwardAiry.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hUC (ε/2) (by positivity)
  -- the width used for the central region and the tails
  set δ : ℝ := min (δ₀/2) 1 with hδ
  have hδpos : 0 < δ := by positivity
  -- tail thresholds
  set M : ℝ := C₀ * Real.exp |x| + |airyAiReal x| + 1 with hM
  have hMpos : 0 < M := by positivity
  obtain ⟨δ₁a, hδ₁apos, hδ₁a⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp (tendsto_integral_heatKernel_mul_exp_Ioi_zero hδpos 1)
      (ε/(8*M)) (by positivity)
  obtain ⟨δ₁b, hδ₁bpos, hδ₁b⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp (tendsto_integral_heatKernel_mul_exp_Ioi_zero hδpos 0)
      (ε/(8*M)) (by positivity)
  refine ⟨min (min (δ₀/2) 1) (min (min δ₁a δ₁b) (δ/16)),
    by positivity, fun T hT hT' => ?_⟩
  have hTpos : 0 < T := hT
  have hTlt1 : T < δ₀/2 ∧ T < 1 ∧ T < min δ₁a δ₁b ∧ T < δ/16 := by
    have h1 : dist T 0 = T := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hTpos.le]
    rw [h1] at hT'
    exact ⟨hT'.trans_le ((min_le_left _ _).trans (min_le_left _ _)),
      hT'.trans_le ((min_le_left _ _).trans (min_le_right _ _)),
      hT'.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      hT'.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hT1 : T ≤ 1 := hTlt1.2.1.le
  -- the error decomposition
  rw [Real.dist_eq]
  rw [heatAiryConv_sub_eq hTpos x]
  apply lt_of_le_of_lt (abs_integral_le_integral_abs)
  -- set up the integrand `φ`
  set φ : ℝ → ℝ := fun v => heatKernel T v * |backwardAiry T (x - v) - airyAiReal x| with hφ
  -- pointwise: `|g_T(x−v) − Ai x| ≤ ε/2` on `Icc (−δ) δ`
  have hsmall : ∀ v ∈ Set.Icc (-δ) δ,
      |backwardAiry T (x - v) - airyAiReal x| ≤ ε/2 := by
    intro v hv
    have hvabs : |v| ≤ δ := abs_le.mpr hv
    have hvmem : (T, x - v) ∈ Set.Icc 0 1 ×ˢ Set.Icc (x-1) (x+1) := by
      have hδ1 : δ ≤ 1 := by rw [hδ]; exact min_le_right _ _
      constructor
      · exact ⟨hTpos.le, hT1⟩
      · exact ⟨by nlinarith [hvabs, le_abs_self v, hδ1],
          by nlinarith [hvabs, neg_le_abs v, hδ1]⟩
    have h0mem : (0, x) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (x-1) (x+1) :=
      ⟨Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩,
        Set.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩
    have hδδ : δ ≤ δ₀/2 := by rw [hδ]; exact min_le_left _ _
    have hdist : dist (T, x - v) (0, x) < δ₀ := by
      rw [Prod.dist_eq]
      show max (dist T 0) (dist (x - v) x) < δ₀
      rw [Real.dist_eq, Real.dist_eq, sub_zero, show (x - v) - x = -v from by ring,
        abs_of_nonneg hTpos.le, abs_neg]
      exact max_lt (hTlt1.1.trans (by nlinarith [hδ₀pos]))
        (hvabs.trans_lt (hδδ.trans_lt (by nlinarith [hδ₀pos])))
    have h := hδ₀ (T, x - v) hvmem (0, x) h0mem hdist
    have e : backwardAiry 0 x = airyAiReal x := backwardAiry_zero x
    rw [e, Real.dist_eq] at h
    exact h.le
  -- pointwise: `|g_T(x−v) − Ai x| ≤ C₀ e^{|x|} e^{|v|} + |Ai x|` everywhere
  have hbig : ∀ v : ℝ, |backwardAiry T (x - v) - airyAiReal x|
      ≤ C₀ * Real.exp |x| * Real.exp |v| + |airyAiReal x| := by
    intro v
    have hg := hC₀ T ⟨hTpos.le, hT1⟩ (x - v)
    have hexp : Real.exp (1 * |x - v|) ≤ Real.exp |x| * Real.exp |v| := by
      rw [one_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      exact abs_sub x v
    calc |backwardAiry T (x - v) - airyAiReal x|
        ≤ |backwardAiry T (x - v)| + |airyAiReal x| := abs_sub _ _
      _ ≤ C₀ * Real.exp (1 * |x - v|) + |airyAiReal x| := add_le_add hg le_rfl
      _ ≤ C₀ * (Real.exp |x| * Real.exp |v|) + |airyAiReal x| :=
          add_le_add (mul_le_mul_of_nonneg_left hexp hC₀nn) le_rfl
      _ = C₀ * Real.exp |x| * Real.exp |v| + |airyAiReal x| := by ring
  -- integrability of `φ` (for the split)
  have hφint : Integrable φ := by
    apply ((integrable_exp_neg_sq_add_abs (b := 1/(4*T)) (by positivity) (1:ℝ) 0).const_mul
      ((4*Real.pi*T)^(-1/2:ℝ) * (C₀ * Real.exp |x| + |airyAiReal x|))).mono'
    · exact ((continuous_heatKernel T).mul ((((continuous_backwardAiry_s T).comp
        (by fun_prop)).sub continuous_const).abs)).aestronglyMeasurable
    · filter_upwards with v
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hTpos _), abs_abs]
      have h1 : C₀ * Real.exp |x| * Real.exp |v| + |airyAiReal x|
          ≤ (C₀ * Real.exp |x| + |airyAiReal x|) * Real.exp |v| := by
        have hle : |airyAiReal x| ≤ |airyAiReal x| * Real.exp |v| :=
          le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (abs_nonneg _))
        have hA : 0 ≤ C₀ * Real.exp |x| * Real.exp |v| := by positivity
        have hB : 0 ≤ |airyAiReal x| * Real.exp |v| := by positivity
        nlinarith [hle]
      calc heatKernel T v * |backwardAiry T (x - v) - airyAiReal x|
          ≤ heatKernel T v * (C₀ * Real.exp |x| * Real.exp |v| + |airyAiReal x|) :=
            mul_le_mul_of_nonneg_left (hbig v) (heatKernel_nonneg hTpos _)
        _ ≤ heatKernel T v * ((C₀ * Real.exp |x| + |airyAiReal x|) * Real.exp |v|) :=
            mul_le_mul_of_nonneg_left h1 (heatKernel_nonneg hTpos _)
        _ = (4*Real.pi*T)^(-1/2:ℝ) * (C₀ * Real.exp |x| + |airyAiReal x|)
            * Real.exp (-(1/(4*T))*(v - 0)^2 + 1*|v|) := by
            unfold heatKernel
            have hexp : -v^2/(4*T) = -(1/(4*T))*(v - 0)^2 := by ring
            rw [hexp, Real.exp_add, one_mul]
            ring
  -- the three pieces
  have hIcc : ∫ v in Set.Icc (-δ) δ, φ v ≤ ε/2 := by
    have h1 : ∫ v in Set.Icc (-δ) δ, φ v ≤ ∫ v in Set.Icc (-δ) δ, heatKernel T v * (ε/2) := by
      apply setIntegral_mono_on hφint.integrableOn
        (((continuous_heatKernel T).continuousOn.mul continuousOn_const).integrableOn_Icc)
        measurableSet_Icc
      intro v hv
      exact mul_le_mul_of_nonneg_left (hsmall v hv) (heatKernel_nonneg hTpos _)
    calc ∫ v in Set.Icc (-δ) δ, φ v ≤ ∫ v in Set.Icc (-δ) δ, heatKernel T v * (ε/2) := h1
      _ ≤ ∫ v : ℝ, heatKernel T v * (ε/2) :=
          setIntegral_le_integral ((integrable_heatKernel hTpos).mul_const _)
            (Eventually.of_forall fun v => mul_nonneg (heatKernel_nonneg hTpos _)
              (by positivity))
      _ = ε/2 := by
          rw [integral_mul_const, integral_heatKernel hTpos, one_mul]
  -- the tail pieces: `∫ v in Ioi δ, φ ≤ C₀ e^{|x|} Tail₁ + |Ai x| Tail₀`
  have hT16 : T ≤ δ/16 := hTlt1.2.2.2.le
  have hbound_tail : ∀ v ∈ Set.Ioi δ, φ v
      ≤ heatKernel T v * (C₀ * Real.exp |x| * Real.exp (1 * v)
        + |airyAiReal x| * Real.exp (0 * v)) := by
    intro v hv
    have hvpos : 0 < v := hδpos.trans hv
    have heq : C₀ * Real.exp |x| * Real.exp (1 * v) + |airyAiReal x| * Real.exp (0 * v)
        = C₀ * Real.exp |x| * Real.exp |v| + |airyAiReal x| := by
      rw [one_mul, abs_of_nonneg hvpos.le, zero_mul, Real.exp_zero, mul_one]
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hbig v) (heatKernel_nonneg hTpos _)
  have hint1 : IntegrableOn (fun v : ℝ => heatKernel T v * Real.exp (1 * v))
      (Set.Ioi δ) := by
    have hTle : T ∈ Set.Ioc 0 (δ / (8*(|1| + 1))) := by
      refine ⟨hTpos, ?_⟩
      calc T ≤ δ/16 := hT16
        _ = δ / (8*(|1| + 1)) := by norm_num
    have hR : IntegrableOn (fun v : ℝ => (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-v^2/(8*T)))
        (Set.Ioi δ) := by
      have h2T : (0:ℝ) < 2*T := by positivity
      have h := integrableOn_exp_neg_sq_div_Ioi h2T δ
      have heq : (fun d : ℝ => Real.exp (-d^2/(4*(2*T))))
          = fun d => Real.exp (-d^2/(8*T)) := by
        funext d
        congr 1
        ring
      rw [heq] at h
      exact h.const_mul _
    apply integrableOn_of_abs_le_on measurableSet_Ioi hR
    · exact ((continuous_heatKernel T).mul (by fun_prop)).aestronglyMeasurable
    · intro v hv
      rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hTpos _),
        abs_of_nonneg (Real.exp_pos _).le]
      exact heatKernel_mul_exp_le hδpos 1 hTle hv
  have hint0 : IntegrableOn (fun v : ℝ => heatKernel T v * Real.exp (0 * v))
      (Set.Ioi δ) := by
    have hTle : T ∈ Set.Ioc 0 (δ / (8*(|0| + 1))) := by
      refine ⟨hTpos, ?_⟩
      calc T ≤ δ/16 := hT16
        _ ≤ δ / (8*(|0| + 1)) :=
          div_le_div_of_nonneg_left hδpos.le (by norm_num) (by norm_num)
    have hR : IntegrableOn (fun v : ℝ => (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-v^2/(8*T)))
        (Set.Ioi δ) := by
      have h2T : (0:ℝ) < 2*T := by positivity
      have h := integrableOn_exp_neg_sq_div_Ioi h2T δ
      have heq : (fun d : ℝ => Real.exp (-d^2/(4*(2*T))))
          = fun d => Real.exp (-d^2/(8*T)) := by
        funext d
        congr 1
        ring
      rw [heq] at h
      exact h.const_mul _
    apply integrableOn_of_abs_le_on measurableSet_Ioi hR
    · exact ((continuous_heatKernel T).mul (by fun_prop)).aestronglyMeasurable
    · intro v hv
      rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hTpos _),
        abs_of_nonneg (Real.exp_pos _).le]
      exact heatKernel_mul_exp_le hδpos 0 hTle hv
  have hint : IntegrableOn (fun v : ℝ => heatKernel T v * (C₀ * Real.exp |x| * Real.exp (1 * v)
        + |airyAiReal x| * Real.exp (0 * v))) (Set.Ioi δ) := by
    have hintA : IntegrableOn (fun v : ℝ => C₀ * Real.exp |x| * (heatKernel T v * Real.exp (1 * v)))
        (Set.Ioi δ) := Integrable.const_mul hint1 _
    have hintB : IntegrableOn (fun v : ℝ => |airyAiReal x| * (heatKernel T v * Real.exp (0 * v)))
        (Set.Ioi δ) := Integrable.const_mul hint0 _
    convert hintA.add hintB using 1
    ext v
    show heatKernel T v * (C₀ * Real.exp |x| * Real.exp (1 * v)
          + |airyAiReal x| * Real.exp (0 * v))
        = C₀ * Real.exp |x| * (heatKernel T v * Real.exp (1 * v))
          + |airyAiReal x| * (heatKernel T v * Real.exp (0 * v))
    ring
  have hIoi : ∫ v in Set.Ioi δ, φ v
      ≤ C₀ * Real.exp |x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (1 * v))
        + |airyAiReal x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (0 * v)) := by
    have hintA : IntegrableOn (fun v : ℝ => C₀ * Real.exp |x| * (heatKernel T v * Real.exp (1 * v)))
        (Set.Ioi δ) := Integrable.const_mul hint1 _
    have hintB : IntegrableOn (fun v : ℝ => |airyAiReal x| * (heatKernel T v * Real.exp (0 * v)))
        (Set.Ioi δ) := Integrable.const_mul hint0 _
    calc ∫ v in Set.Ioi δ, φ v
        ≤ ∫ v in Set.Ioi δ, heatKernel T v * (C₀ * Real.exp |x| * Real.exp (1 * v)
          + |airyAiReal x| * Real.exp (0 * v)) :=
          setIntegral_mono_on hφint.integrableOn hint measurableSet_Ioi hbound_tail
      _ = C₀ * Real.exp |x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (1 * v))
          + |airyAiReal x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (0 * v)) := by
        rw [show (fun v : ℝ => heatKernel T v * (C₀ * Real.exp |x| * Real.exp (1 * v)
              + |airyAiReal x| * Real.exp (0 * v)))
            = (fun v : ℝ => (C₀ * Real.exp |x| * (heatKernel T v * Real.exp (1 * v))
              + |airyAiReal x| * (heatKernel T v * Real.exp (0 * v)))) from
          funext fun v => by ring]
        rw [integral_add hintA hintB, integral_const_mul, integral_const_mul]
  have hIio : ∫ v in Set.Iio (-δ), φ v
      ≤ C₀ * Real.exp |x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (1 * v))
        + |airyAiReal x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (0 * v)) := by
    have hφeq : ∀ v : ℝ, φ v = heatKernel T v * |backwardAiry T (x - v) - airyAiReal x| :=
      fun v => rfl
    have hrefl : ∫ v in Set.Iio (-δ), φ v = ∫ v in Set.Ioi δ, φ (-v) := by
      rw [← MeasureTheory.integral_Iic_eq_integral_Iio]
      exact (integral_comp_neg_Ioi δ φ).symm
    have hbound2 : ∀ v ∈ Set.Ioi δ, φ (-v)
        ≤ heatKernel T v * (C₀ * Real.exp |x| * Real.exp (1 * v)
          + |airyAiReal x| * Real.exp (0 * v)) := by
      intro v hv
      have hvpos : 0 < v := hδpos.trans hv
      rw [hφeq]
      have heven : heatKernel T (-v) = heatKernel T v := by
        unfold heatKernel
        rw [neg_sq]
      rw [heven, show x - -v = x + v by ring]
      have h2 := hbig (-v)
      rw [show x - -v = x + v by ring, abs_neg] at h2
      have h3 : heatKernel T v * |backwardAiry T (x + v) - airyAiReal x|
          ≤ heatKernel T v * (C₀ * Real.exp |x| * Real.exp |v| + |airyAiReal x|) :=
        mul_le_mul_of_nonneg_left h2 (heatKernel_nonneg hTpos _)
      calc heatKernel T v * |backwardAiry T (x + v) - airyAiReal x|
          ≤ heatKernel T v * (C₀ * Real.exp |x| * Real.exp |v| + |airyAiReal x|) := h3
        _ = heatKernel T v * (C₀ * Real.exp |x| * Real.exp (1 * v)
            + |airyAiReal x| * Real.exp (0 * v)) := by
            rw [one_mul, abs_of_nonneg hvpos.le, zero_mul, Real.exp_zero, mul_one]
    calc ∫ v in Set.Iio (-δ), φ v = ∫ v in Set.Ioi δ, φ (-v) := hrefl
      _ ≤ ∫ v in Set.Ioi δ, heatKernel T v * (C₀ * Real.exp |x| * Real.exp (1 * v)
          + |airyAiReal x| * Real.exp (0 * v)) :=
          setIntegral_mono_on (hφint.comp_neg.integrableOn) hint measurableSet_Ioi hbound2
      _ = C₀ * Real.exp |x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (1 * v))
          + |airyAiReal x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (0 * v)) := by
        have hintA : IntegrableOn (fun v : ℝ => C₀ * Real.exp |x| * (heatKernel T v * Real.exp (1 * v)))
            (Set.Ioi δ) := Integrable.const_mul hint1 _
        have hintB : IntegrableOn (fun v : ℝ => |airyAiReal x| * (heatKernel T v * Real.exp (0 * v)))
            (Set.Ioi δ) := Integrable.const_mul hint0 _
        rw [show (fun v : ℝ => heatKernel T v * (C₀ * Real.exp |x| * Real.exp (1 * v)
              + |airyAiReal x| * Real.exp (0 * v)))
            = (fun v : ℝ => (C₀ * Real.exp |x| * (heatKernel T v * Real.exp (1 * v))
              + |airyAiReal x| * (heatKernel T v * Real.exp (0 * v)))) from
          funext fun v => by ring]
        rw [integral_add hintA hintB, integral_const_mul, integral_const_mul]
  -- the split into the three regions
  have hsplit : (∫ v : ℝ, φ v)
      = (∫ v in Set.Icc (-δ) δ, φ v) + (∫ v in Set.Ioi δ, φ v) + (∫ v in Set.Iio (-δ), φ v) := by
    have h1 : ∀ v : ℝ, (Set.Icc (-δ) δ).indicator φ v + (Set.Ioi δ).indicator φ v
        + (Set.Iio (-δ)).indicator φ v = φ v := by
      intro v
      by_cases h1 : v ≤ δ
      · by_cases h2 : -δ ≤ v
        · rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨h2, h1⟩) φ,
            Set.indicator_of_notMem (show v ∉ Set.Ioi δ from
              by simp only [Set.mem_Ioi, not_lt]; exact h1) φ,
            Set.indicator_of_notMem (show v ∉ Set.Iio (-δ) from
              by simp only [Set.mem_Iio, not_lt]; exact h2) φ]
          simp
        · push_neg at h2
          rw [Set.indicator_of_notMem (show v ∉ Set.Icc (-δ) δ from
              by simp only [Set.mem_Icc, not_and, not_le]; exact fun h => absurd h (not_le_of_gt h2)) φ,
            Set.indicator_of_notMem (show v ∉ Set.Ioi δ from
              by simp only [Set.mem_Ioi, not_lt]; exact h2.le.trans (by linarith [hδpos])) φ,
            Set.indicator_of_mem (Set.mem_Iio.mpr h2) φ]
          simp
      · push_neg at h1
        rw [Set.indicator_of_notMem (show v ∉ Set.Icc (-δ) δ from
            by simp only [Set.mem_Icc, not_and, not_le]; exact fun _ => h1) φ,
          Set.indicator_of_mem (Set.mem_Ioi.mpr h1) φ,
          Set.indicator_of_notMem (show v ∉ Set.Iio (-δ) from
            by simp only [Set.mem_Iio, not_lt]; linarith [hδpos, h1]) φ]
        simp
    have hsum : (∫ v : ℝ, φ v)
        = (∫ v : ℝ, (Set.Icc (-δ) δ).indicator φ v)
          + (∫ v : ℝ, (Set.Ioi δ).indicator φ v)
          + (∫ v : ℝ, (Set.Iio (-δ)).indicator φ v) := by
      rw [integral_congr_ae (Eventually.of_forall fun v => (h1 v).symm)]
      have hf₁ : Integrable fun v : ℝ =>
          (Set.Icc (-δ) δ).indicator φ v + (Set.Ioi δ).indicator φ v := by
        convert ((hφint.indicator measurableSet_Icc).add (hφint.indicator measurableSet_Ioi)) using 1
      rw [integral_add hf₁ (hφint.indicator measurableSet_Iio)]
      rw [integral_add (hφint.indicator measurableSet_Icc) (hφint.indicator measurableSet_Ioi)]
    rw [hsum]
    rw [MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_indicator measurableSet_Ioi,
      MeasureTheory.integral_indicator measurableSet_Iio]
  -- the tail bounds are small
  have hTdist : dist T 0 = T := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hTpos.le]
  have hTail1 : ∫ v in Set.Ioi δ, heatKernel T v * Real.exp (1 * v) < ε/(8*M) := by
    have h := hδ₁a hT (by rw [hTdist]; exact hTlt1.2.2.1.trans_le (min_le_left _ _))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioi
      (fun v _ => mul_nonneg (heatKernel_nonneg hTpos _) (Real.exp_pos _).le))] at h
    exact h
  have hTail0 : ∫ v in Set.Ioi δ, heatKernel T v * Real.exp (0 * v) < ε/(8*M) := by
    have h := hδ₁b hT (by rw [hTdist]; exact hTlt1.2.2.1.trans_le (min_le_right _ _))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioi
      (fun v _ => mul_nonneg (heatKernel_nonneg hTpos _) (Real.exp_pos _).le))] at h
    exact h
  have htail : C₀ * Real.exp |x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (1 * v))
      + |airyAiReal x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (0 * v)) < ε/8 := by
    have h1 : C₀ * Real.exp |x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (1 * v))
        ≤ C₀ * Real.exp |x| * (ε/(8*M)) :=
      mul_le_mul_of_nonneg_left hTail1.le (by positivity)
    have h2 : |airyAiReal x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (0 * v))
        ≤ |airyAiReal x| * (ε/(8*M)) :=
      mul_le_mul_of_nonneg_left hTail0.le (abs_nonneg _)
    have h3 : (C₀ * Real.exp |x| + |airyAiReal x|) * (ε/(8*M)) < ε/8 := by
      have hM' : C₀ * Real.exp |x| + |airyAiReal x| < M := by rw [hM]; exact lt_add_one _
      calc (C₀ * Real.exp |x| + |airyAiReal x|) * (ε/(8*M))
          < M * (ε/(8*M)) := mul_lt_mul_of_pos_right hM' (by positivity)
        _ = ε/8 := by field_simp
    calc C₀ * Real.exp |x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (1 * v))
          + |airyAiReal x| * (∫ v in Set.Ioi δ, heatKernel T v * Real.exp (0 * v))
        ≤ (C₀ * Real.exp |x| + |airyAiReal x|) * (ε/(8*M)) := by
          rw [show (C₀ * Real.exp |x| + |airyAiReal x|) * (ε/(8*M))
              = C₀ * Real.exp |x| * (ε/(8*M)) + |airyAiReal x| * (ε/(8*M)) from by ring]
          exact add_le_add h1 h2
      _ < ε/8 := h3
  -- conclude
  have hcong : (∫ v : ℝ, |heatKernel T v * (backwardAiry T (x - v) - airyAiReal x)|)
      = ∫ v : ℝ, φ v := by
    apply integral_congr_ae
    filter_upwards with v
    rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hTpos _)]
  rw [hcong]
  calc (∫ v : ℝ, φ v)
      = (∫ v in Set.Icc (-δ) δ, φ v) + (∫ v in Set.Ioi δ, φ v) + (∫ v in Set.Iio (-δ), φ v) :=
        hsplit
    _ ≤ ε/2 + (ε/8) + (ε/8) :=
        add_le_add (add_le_add hIcc (lt_of_le_of_lt hIoi htail).le)
          (lt_of_le_of_lt hIio htail).le
    _ < ε := by linarith [hε]

end Mollifier

/-! ## (1) and (4): the heat–Airy convolution identity and the backward-kernel form -/

section HeatAiryConvolutionMain

/-- **(1)** (Quastel–Remenik, Prop. 1.2 / (1.9)): the heat–Airy convolution identity
`∫ s, heatKernel T (x - s) * backwardAiry T s = airyAiReal x` for `0 < T`. -/
theorem heat_airy_conv (T : ℝ) (hT : 0 < T) (x : ℝ) :
    ∫ s : ℝ, heatKernel T (x - s) * backwardAiry T s = airyAiReal x := by
  have hmol := tendsto_heatAiryConv_zero x
  have hT2 : (0:ℝ) < T/2 := by positivity
  have h1 : (∫ s : ℝ, heatKernel T (x - s) * backwardAiry T s)
      = ∫ s : ℝ, heatKernel (T/2) (x - s) * backwardAiry (T/2) s :=
    heatAiryConv_eq_of_pos x hT hT2
  have hconst : ∀ᶠ t in 𝓝[>] 0,
      (∫ s : ℝ, heatKernel t (x - s) * backwardAiry t s)
        = ∫ s : ℝ, heatKernel (T/2) (x - s) * backwardAiry (T/2) s := by
    filter_upwards [Ioo_mem_nhdsGT hT2] with t ht
    exact heatAiryConv_eq_of_pos x ht.1 hT2
  have h2 : (∫ s : ℝ, heatKernel (T/2) (x - s) * backwardAiry (T/2) s) = airyAiReal x := by
    have h3 : Tendsto (fun t : ℝ => ∫ s : ℝ, heatKernel t (x - s) * backwardAiry t s)
        (𝓝[>] 0) (𝓝 (∫ s : ℝ, heatKernel (T/2) (x - s) * backwardAiry (T/2) s)) :=
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hconst)
    exact (tendsto_nhds_unique hmol h3).symm
  rw [h1]
  exact h2

/-- **(4)** (the shape of the paper's backward Airy kernel identity): the forward heat
evolution of the backward Airy kernel returns `Ai`:
`∫ w, heatKernel T (y - w) * backwardAiry T (z + w) = airyAiReal (z + y)`. -/
theorem heat_airy_conv_backward (T : ℝ) (hT : 0 < T) (z y : ℝ) :
    ∫ w : ℝ, heatKernel T (y - w) * backwardAiry T (z + w) = airyAiReal (z + y) := by
  have h1 := heat_airy_conv T hT (z + y)
  have h2 : (∫ w : ℝ, heatKernel T (y - w) * backwardAiry T (z + w))
      = ∫ s : ℝ, heatKernel T (z + y - s) * backwardAiry T s := by
    have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
      (fun w : ℝ => heatKernel T (y - w) * backwardAiry T (z + w)) z
    have heq : (fun s : ℝ => heatKernel T (y - (s - z)) * backwardAiry T (z + (s - z)))
        = fun s : ℝ => heatKernel T (z + y - s) * backwardAiry T s := by
      funext s
      congr 1
      · congr 1
        ring
      · congr 1
        ring
    rw [heq] at h
    exact h.symm
  rw [h2]
  exact h1

end HeatAiryConvolutionMain

/-! ## (2): the moment identity -/

section HeatAiryConvolutionMoment

/-- The `x`-derivative of the heat–Airy convolution integrand. -/
theorem hasDerivAt_heatAiryConv_integrand_x (hT : 0 < T) (x s : ℝ) :
    HasDerivAt (fun x : ℝ => heatKernel T (x - s) * backwardAiry T s)
      ((-(x - s)/(2*T)) * heatKernel T (x - s) * backwardAiry T s) x := by
  have h := ((hasDerivAt_heatKernel_v hT (x - s)).comp x
    ((hasDerivAt_id' x).sub_const s)).mul (hasDerivAt_const x (backwardAiry T s))
  convert h using 1
  · ext x'
    rfl
  · ring

/-- The key quadratic inequality for the `x`-domination: for `|x - A| ≤ 1`,
`(A-s)²/2 - 1 ≤ (x-s)²`. -/
theorem quad_sub_sq_half_sub_one_le {A x s : ℝ} (hx : |x - A| ≤ 1) :
    (A - s)^2/2 - 1 ≤ (x - s)^2 := by
  have h1 : |x - s| ≥ |A - s| - 1 := by
    have h := abs_sub_abs_le_abs_sub (A - s) (x - s)
    rw [show (A - s) - (x - s) = A - x by ring, abs_sub_comm A x] at h
    have h2 : |A - s| - |x - s| ≤ 1 := h.trans hx
    linarith [abs_nonneg (x - s)]
  by_cases h3 : 1 ≤ |A - s|
  · have h4 : (x - s)^2 ≥ (|A - s| - 1)^2 := by
      rw [← sq_abs (x - s)]
      exact pow_le_pow_left₀ (by linarith) h1 2
    nlinarith [sq_nonneg (|A - s| - 2), sq_abs (A - s), h4]
  · have h3' : |A - s| < 1 := not_le.mp h3
    have h4 : (A - s)^2 < 1 := by
      have h5 : |A - s|^2 < 1 := (sq_lt_one_iff₀ (abs_nonneg _)).mpr h3'
      rwa [sq_abs] at h5
    nlinarith [sq_nonneg (x - s), h4]

/-- **(2), preliminary step**: differentiation of the heat–Airy convolution in `x`. -/
theorem hasDerivAt_integral_heatAiryConv_x (hT : 0 < T) (A : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ s : ℝ, heatKernel T (x - s) * backwardAiry T s)
      (∫ s : ℝ, (-(A - s)/(2*T)) * heatKernel T (A - s) * backwardAiry T s) A := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp T
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0 ⟨le_rfl, hT.le⟩ 0
    rw [abs_zero, mul_zero, Real.exp_zero, mul_one] at h
    have e : backwardAiry 0 0 = airyAiReal 0 := by simp [backwardAiry]
    rw [e] at h
    exact le_trans (abs_nonneg _) h
  have hbound : ∀ᵐ s : ℝ, ∀ x ∈ Metric.ball A 1,
      ‖(-(x - s)/(2*T)) * heatKernel T (x - s) * backwardAiry T s‖
        ≤ ((1/(2*T)) * (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (1/(4*T)) * C₀ * (2*(1+(|A|+1)^2)))
          * ((1 + s^2) * Real.exp (-(1/(8*T))*(s - A)^2 + T*|s|)) := by
    filter_upwards with s
    intro x hx
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (heatKernel_nonneg hT _),
      abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2*T)]
    have hx' : |x - A| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hx
      exact hx.le
    have hsq := quad_sub_sq_half_sub_one_le (A := A) (x := x) (s := s) hx'
    have hexp : Real.exp (-(x - s)^2/(4*T)) ≤ Real.exp (1/(4*T)) * Real.exp (-(A - s)^2/(8*T)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hsq' : (A - s)^2 ≤ 2*(x - s)^2 + 2 := by linarith [hsq]
      rw [show -(x - s)^2/(4*T) = (-2*(x - s)^2)/(8*T) by field_simp; ring,
        show 1/(4*T) + -(A - s)^2/(8*T) = (2 - (A - s)^2)/(8*T) by field_simp; ring,
        div_eq_inv_mul, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (show (-2*(x - s)^2) ≤ (2 - (A - s)^2) by linarith [hsq'])
        (show (0:ℝ) ≤ (8*T)⁻¹ by positivity)
    have habs : |x - s|/(2*T) ≤ (1/(2*T)) * (1 + (x - s)^2) := by
      rw [show (1/(2*T)) * (1 + (x - s)^2) = (1 + (x - s)^2)/(2*T) by ring,
        div_eq_inv_mul, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (abs_le_one_add_sq _) (by positivity)
    have hsub : (1 + (x - s)^2) ≤ 2*(1+(|A|+1)^2)*(1+s^2) := by
      have hx2 : x^2 ≤ (|A|+1)^2 := by
        rw [sq_le_sq]
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ |A|+1)]
        calc |x| = |(x - A) + A| := by ring
          _ ≤ |x - A| + |A| := abs_add_le _ _
          _ ≤ 1 + |A| := add_le_add hx' le_rfl
          _ = |A| + 1 := by ring
      nlinarith [sq_nonneg (x - s), sq_nonneg (x + s), sq_nonneg x, sq_nonneg s,
        sq_nonneg (x * s), sq_nonneg A, hx2]
    have hkhk : heatKernel T (x - s)
        ≤ (4*Real.pi*T)^(-1/2:ℝ) * (Real.exp (1/(4*T)) * Real.exp (-(A - s)^2/(8*T))) := by
      unfold heatKernel
      exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (by positivity) _)
    calc |x - s| / (2*T) * heatKernel T (x - s) * |backwardAiry T s|
        ≤ (((1/(2*T)) * (1 + (x - s)^2)) * ((4*Real.pi*T)^(-1/2:ℝ)
            * (Real.exp (1/(4*T)) * Real.exp (-(A - s)^2/(8*T))))) * (C₀ * Real.exp (T * |s|)) :=
          mul_le_mul (mul_le_mul habs hkhk (heatKernel_nonneg hT _)
            (mul_nonneg (by positivity) (by positivity)))
            (hC₀ T ⟨hT.le, le_rfl⟩ s) (abs_nonneg _)
            (mul_nonneg (by positivity) (by positivity))
      _ = ((1/(2*T)) * (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (1/(4*T)) * C₀) * (1 + (x - s)^2)
          * (Real.exp (-(A - s)^2/(8*T)) * Real.exp (T*|s|)) := by
          ring
      _ ≤ ((1/(2*T)) * (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (1/(4*T)) * C₀) * (2*(1+(|A|+1)^2)*(1+s^2))
          * (Real.exp (-(A - s)^2/(8*T)) * Real.exp (T*|s|)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsub (by positivity)) (by positivity)
      _ = ((1/(2*T)) * (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (1/(4*T)) * C₀ * (2*(1+(|A|+1)^2)))
          * ((1 + s^2) * Real.exp (-(1/(8*T))*(s - A)^2 + T*|s|)) := by
          have hexp' : -(A - s)^2/(8*T) + T*|s| = -(1/(8*T))*(s - A)^2 + T*|s| := by ring
          rw [← Real.exp_add, hexp']
          ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds A one_pos)
    (Eventually.of_forall fun x =>
      (((continuous_heatKernel T).comp (by fun_prop)).mul
        (continuous_backwardAiry_s T)).aestronglyMeasurable)
    (integrable_heatKernel_mul_backwardAiry hT A)
    (show AEStronglyMeasurable (fun s : ℝ => (-(A - s)/(2*T)) * heatKernel T (A - s) * backwardAiry T s) volume from
      ((by fun_prop : Continuous fun s : ℝ => -(A - s)/(2*T)).mul
        ((continuous_heatKernel T).comp (by fun_prop : Continuous fun s : ℝ => A - s))
        |>.mul (continuous_backwardAiry_s T)).aestronglyMeasurable)
    hbound
    ((integrable_one_add_sq_mul_exp_neg_sq_add_abs (b := 1/(8*T)) (by positivity) T A).const_mul _)
    (Eventually.of_forall fun s x hx => hasDerivAt_heatAiryConv_integrand_x hT x s)).2

/-- **(2)** (the first-moment companion of `heat_airy_conv`):
`∫ s, (A - s) heatKernel T (A - s) backwardAiry T s = -(2T) Ai'(A)`. -/
theorem heat_airy_conv_moment (hT : 0 < T) (A : ℝ) :
    ∫ s : ℝ, (A - s) * heatKernel T (A - s) * backwardAiry T s
      = -(2*T) * deriv airyAiReal A := by
  have hderiv := hasDerivAt_integral_heatAiryConv_x hT A
  have hfun : (fun x : ℝ => ∫ s : ℝ, heatKernel T (x - s) * backwardAiry T s)
      = airyAiReal := funext fun x => heat_airy_conv T hT x
  have h2 : deriv airyAiReal A
      = ∫ s : ℝ, (-(A - s)/(2*T)) * heatKernel T (A - s) * backwardAiry T s := by
    rw [← hderiv.deriv, hfun]
  -- pull out the `-1/(2T)` factor
  have h3 : (∫ s : ℝ, (-(A - s)/(2*T)) * heatKernel T (A - s) * backwardAiry T s)
      = -(1/(2*T)) * ∫ s : ℝ, (A - s) * heatKernel T (A - s) * backwardAiry T s := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    ring
  rw [h2, h3]
  field_simp [hT.ne']

end HeatAiryConvolutionMoment

/-! ## (3): the Gaussian-tail convolution identity -/

section HeatAiryConvolutionTail

/-- Half-line shift identity: `∫ d in Ioi (A−s), f d = ∫ u in Ioi A, f (u−s) du`. -/
theorem integral_Ioi_comp_sub (s A : ℝ) (f : ℝ → ℝ) :
    (∫ d in Set.Ioi (A - s), f d) = ∫ u in Set.Ioi A, f (u - s) := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi]
  have h := (MeasureTheory.integral_sub_right_eq_self (μ := volume)
    ((Set.Ioi (A - s)).indicator f) s).symm
  rw [h]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Set.Ioi A
  · have hu' : u - s ∈ Set.Ioi (A - s) := by
      simp only [Set.mem_Ioi] at hu ⊢
      linarith
    rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu']
  · have hu' : u - s ∉ Set.Ioi (A - s) := by
      simp only [Set.mem_Ioi] at hu ⊢
      linarith
    rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']

/-- `gaussianTail T (A−s)` in terms of the heat kernel integrated over `(A, ∞)`:
`gaussianTail T (A−s) = √(4πT) · ∫ u in Ioi A, heatKernel T (u−s) du`. -/
theorem gaussianTail_eq_sqrt_mul_integral_heatKernel_sub (hT : 0 < T) (A s : ℝ) :
    gaussianTail T (A - s)
      = Real.sqrt (4 * Real.pi * T) * ∫ u in Set.Ioi A, heatKernel T (u - s) := by
  have h1 : ∫ u in Set.Ioi A, heatKernel T (u - s)
      = (4*Real.pi*T)^(-1/2:ℝ) * gaussianTail T (A - s) := by
    unfold heatKernel gaussianTail
    rw [integral_const_mul, ← integral_Ioi_comp_sub s A (fun d => Real.exp (-d^2/(4*T)))]
  rw [h1]
  rw [Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add (by positivity : (0:ℝ) < 4*Real.pi*T),
    show (1/2 : ℝ) + (-1/2 : ℝ) = 0 by ring, Real.rpow_zero, one_mul]

/-- **Global one-sided bound**: `|g_T(s)| ≤ C₀ · e^{-Ts}` for all `s` (since
`e^{-(2/3)T³} ≤ 1` and `Ai` is globally bounded). -/
theorem backwardAiry_abs_le_exp_neg {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, ∀ s : ℝ, |backwardAiry T s| ≤ C * Real.exp (-T * s) := by
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le
  have hC₀nn : 0 ≤ C₀ := le_trans (abs_nonneg _) (hC₀ 0)
  refine ⟨C₀, fun s => ?_⟩
  unfold backwardAiry
  rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-(2/3)*T^3 - T*s) * |airyAiReal (s + T^2)|
      ≤ Real.exp (-(2/3)*T^3 - T*s) * C₀ :=
        mul_le_mul_of_nonneg_left (hC₀ _) (Real.exp_pos _).le
    _ ≤ Real.exp (-T*s) * C₀ := by
        apply mul_le_mul_of_nonneg_right _ hC₀nn
        apply Real.exp_le_exp.mpr
        have h1 : -(2/3)*T^3 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hT.le 3)
        linarith
    _ = C₀ * Real.exp (-T * s) := by ring

/-- The pointwise completed-square identity behind
`integral_heatKernel_mul_exp_neg_sub`:
`heatKernel T (u−s) · e^{-Ts} = (4πT)^{-1/2} e^{-Tu+T³} · e^{-(s-(u-2T²))²/(4T)}`. -/
theorem heatKernel_mul_exp_neg_sub_eq (hT : 0 < T) (u s : ℝ) :
    heatKernel T (u - s) * Real.exp (-T * s)
      = (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-T*u + T^3)
        * Real.exp (-(s - (u - 2*T^2))^2/(4*T)) := by
  unfold heatKernel
  rw [mul_assoc ((4*Real.pi*T)^(-1/2:ℝ)) (Real.exp (-(u - s)^2/(4*T))) (Real.exp (-T * s)),
    ← Real.exp_add,
    mul_assoc ((4*Real.pi*T)^(-1/2:ℝ)) (Real.exp (-T*u + T^3))
      (Real.exp (-(s - (u - 2*T^2))^2/(4*T))), ← Real.exp_add]
  congr 1
  congr 1
  field_simp
  ring

/-- **The Gaussian moment of `e^{-Ts}` against the shifted heat kernel**:
`∫ s, heatKernel T (u−s) · e^{-Ts} ds = e^{-Tu + T³}` (completing the square:
`-(u-s)²/(4T) - Ts = -(s - (u-2T²))²/(4T) + (-Tu + T³)`). -/
theorem integral_heatKernel_mul_exp_neg_sub (hT : 0 < T) (u : ℝ) :
    ∫ s : ℝ, heatKernel T (u - s) * Real.exp (-T * s) = Real.exp (-T * u + T^3) := by
  have hpt := heatKernel_mul_exp_neg_sub_eq hT u
  rw [show (fun s : ℝ => heatKernel T (u - s) * Real.exp (-T * s))
      = fun s => (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-T*u + T^3)
        * Real.exp (-(s - (u - 2*T^2))^2/(4*T)) from funext fun s => hpt s]
  rw [integral_const_mul]
  have hG : (∫ s : ℝ, Real.exp (-(s - (u - 2*T^2))^2/(4*T))) = Real.sqrt (4*Real.pi*T) := by
    have h1 : (∫ s : ℝ, Real.exp (-(s - (u - 2*T^2))^2/(4*T)))
        = ∫ s : ℝ, Real.exp (-(4*T)⁻¹ * s^2) := by
      have h2 : (∫ s : ℝ, Real.exp (-(4*T)⁻¹ * (s - (u - 2*T^2))^2))
          = ∫ s : ℝ, Real.exp (-(4*T)⁻¹ * s^2) :=
        MeasureTheory.integral_sub_right_eq_self (μ := volume)
          (fun s => Real.exp (-(4*T)⁻¹ * s^2)) (u - 2*T^2)
      have h3 : (fun s : ℝ => Real.exp (-(s - (u - 2*T^2))^2/(4*T)))
          = fun s => Real.exp (-(4*T)⁻¹ * (s - (u - 2*T^2))^2) := by
        funext s
        congr 1
        ring
      rw [h3]
      exact h2
    rw [h1, integral_gaussian]
    congr 1
    field_simp
  rw [hG, Real.sqrt_eq_rpow]
  have h1 : (4*Real.pi*T)^(-1/2:ℝ) * (4*Real.pi*T)^((1/2 : ℝ)) = 1 := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < 4*Real.pi*T),
      show (-1/2 : ℝ) + 1/2 = 0 by ring, Real.rpow_zero]
  rw [show (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-T*u + T^3) * (4*Real.pi*T)^((1/2 : ℝ))
      = ((4*Real.pi*T)^(-1/2:ℝ) * (4*Real.pi*T)^((1/2 : ℝ))) * Real.exp (-T*u + T^3)
      from by ring]
  rw [h1, one_mul]

end HeatAiryConvolutionTail

/-- The absolute convolution is bounded by the exact Gaussian moment, uniformly in
`u`: `∫ s, hk T (u−s)·|g_T(s)| ds ≤ C·e^{-Tu+T³}`. -/
theorem integral_heatKernel_mul_abs_backwardAiry_sub_le (hT : 0 < T) :
    ∃ C : ℝ, ∀ u : ℝ, (∫ s : ℝ, heatKernel T (u - s) * |backwardAiry T s|)
      ≤ C * Real.exp (-T * u + T^3) := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp_neg hT
  refine ⟨C₀, fun u => ?_⟩
  have hle : ∀ s : ℝ, heatKernel T (u - s) * |backwardAiry T s|
      ≤ heatKernel T (u - s) * (C₀ * Real.exp (-T * s)) :=
    fun s => mul_le_mul_of_nonneg_left (hC₀ s) (heatKernel_nonneg hT _)
  have hRHS : Integrable fun s : ℝ => heatKernel T (u - s) * (C₀ * Real.exp (-T * s)) := by
    have h1 : Integrable fun s : ℝ => Real.exp (-(4*T)⁻¹ * (s - (u - 2*T^2))^2) :=
      (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < (4*T)⁻¹)).comp_sub_right (u - 2*T^2)
    have h2 : Integrable fun s : ℝ =>
        (C₀ * (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-T*u + T^3))
          * Real.exp (-(4*T)⁻¹ * (s - (u - 2*T^2))^2) := h1.const_mul _
    convert h2 using 1
    ext s
    calc heatKernel T (u - s) * (C₀ * Real.exp (-T * s))
        = C₀ * (heatKernel T (u - s) * Real.exp (-T * s)) := by ring
      _ = C₀ * ((4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-T*u + T^3)
          * Real.exp (-(s - (u - 2*T^2))^2/(4*T))) := by
          rw [heatKernel_mul_exp_neg_sub_eq hT u s]
      _ = (C₀ * (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-T*u + T^3))
          * Real.exp (-(4*T)⁻¹ * (s - (u - 2*T^2))^2) := by
          rw [show -(s - (u - 2*T^2))^2/(4*T) = -(4*T)⁻¹ * (s - (u - 2*T^2))^2 by
            rw [div_eq_inv_mul]; ring]
          ring
  have hLHS : Integrable fun s : ℝ => heatKernel T (u - s) * |backwardAiry T s| := by
    apply hRHS.mono' ?_ ?_
    · exact (((continuous_heatKernel T).comp (by fun_prop)).mul
        (continuous_backwardAiry_s T).abs).aestronglyMeasurable
    · filter_upwards with s
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hT _), abs_abs]
      exact hle s
  calc ∫ s : ℝ, heatKernel T (u - s) * |backwardAiry T s|
      ≤ ∫ s : ℝ, heatKernel T (u - s) * (C₀ * Real.exp (-T * s)) :=
        integral_mono hLHS hRHS hle
    _ = C₀ * Real.exp (-T * u + T^3) := by
        rw [show (fun s : ℝ => heatKernel T (u - s) * (C₀ * Real.exp (-T * s)))
            = fun s => C₀ * (heatKernel T (u - s) * Real.exp (-T * s)) from
          funext fun s => by ring]
        rw [integral_const_mul, integral_heatKernel_mul_exp_neg_sub hT u]

/-- The joint integrability justifying the Fubini swap in (3): the integrand
`hk T (u−s) · g_T(s)` is integrable on `ℝ × (A, ∞)` (product measure with the
`s`-coordinate first).  The `s`-sections are the integrands of (1); the norm integral
`u ↦ ∫ s, ‖hk T (u−s)·g_T(s)‖` is bounded by `C·e^{-Tu+T³}` on `(A, ∞)`. -/
theorem integrable_heatKernel_backwardAiry_prod_Ioi (hT : 0 < T) (A : ℝ) :
    Integrable (Function.uncurry fun s u : ℝ => heatKernel T (u - s) * backwardAiry T s)
      (volume.prod (volume.restrict (Set.Ioi A))) := by
  obtain ⟨C, hC⟩ := integral_heatKernel_mul_abs_backwardAiry_sub_le hT
  have hcont : Continuous (Function.uncurry fun s u : ℝ =>
      heatKernel T (u - s) * backwardAiry T s) :=
    ((continuous_heatKernel T).comp (continuous_snd.sub continuous_fst)).mul
      (continuous_backwardAiry.comp (continuous_const.prodMk continuous_fst))
  refine (integrable_prod_iff' hcont.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun u _ =>
      integrable_heatKernel_mul_backwardAiry hT u
  · -- integrability of `u ↦ ∫ s, ‖hk T (u−s)·g_T(s)‖` on `(A, ∞)`
    have hB : Integrable (fun u : ℝ => C * Real.exp (T^3) * Real.exp (-T*u))
        (volume.restrict (Set.Ioi A)) :=
      Integrable.const_mul (exp_neg_integrableOn_Ioi A hT) _
    apply hB.mono' ?_ ?_
    · -- measurability of the partial norm-integral
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          ‖heatKernel T (p.1 - p.2) * backwardAiry T p.2‖)
          ((volume.restrict (Set.Ioi A)).prod volume) :=
        (((continuous_heatKernel T).comp (continuous_fst.sub continuous_snd)).mul
          (continuous_backwardAiry.comp
            (continuous_const.prodMk continuous_snd))).norm.aestronglyMeasurable
      exact h1.integral_prod_right'
    · -- pointwise bound
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => by
        have hnorm : ∀ s : ℝ, ‖heatKernel T (u - s) * backwardAiry T s‖
            = heatKernel T (u - s) * |backwardAiry T s| := by
          intro s
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hT _)]
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun s => norm_nonneg _)]
        calc (∫ s : ℝ, ‖heatKernel T (u - s) * backwardAiry T s‖)
            = ∫ s : ℝ, heatKernel T (u - s) * |backwardAiry T s| :=
              integral_congr_ae (Eventually.of_forall fun s => hnorm s)
          _ ≤ C * Real.exp (-T * u + T^3) := hC u
          _ = C * Real.exp (T^3) * Real.exp (-T*u) := by
              rw [Real.exp_add]
              ring

/-- **(3)** (the Gaussian-tail companion of `heat_airy_conv`):
`∫ s, gaussianTail T (A − s) · g_T(s) ds = √(4πT) ∫ u in (A, ∞), Ai(u) du`,
by expanding the Gaussian tail, swapping the two integrals (Fubini, justified by
`integrable_heatKernel_backwardAiry_prod_Ioi`) and applying (1) pointwise. -/
theorem heat_airy_conv_tail (hT : 0 < T) (A : ℝ) :
    ∫ s : ℝ, gaussianTail T (A - s) * backwardAiry T s
      = Real.sqrt (4 * Real.pi * T) * ∫ u in Set.Ioi A, airyAiReal u := by
  have h1 : (fun s : ℝ => gaussianTail T (A - s) * backwardAiry T s)
      = fun s : ℝ => Real.sqrt (4 * Real.pi * T)
          * ∫ u in Set.Ioi A, heatKernel T (u - s) * backwardAiry T s := by
    funext s
    rw [gaussianTail_eq_sqrt_mul_integral_heatKernel_sub hT A s, mul_assoc,
      ← integral_mul_const]
  rw [h1, integral_const_mul]
  congr 1
  rw [integral_integral_swap (μ := volume) (ν := volume.restrict (Set.Ioi A))
    (f := fun s u : ℝ => heatKernel T (u - s) * backwardAiry T s)
    (integrable_heatKernel_backwardAiry_prod_Ioi hT A)]
  exact setIntegral_congr_fun measurableSet_Ioi fun u _ => heat_airy_conv T hT u
