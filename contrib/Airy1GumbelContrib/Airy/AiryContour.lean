/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryBessel
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The contour-integral representation of `Ai`

For every `c > 0` and every `z : ℂ`,
`Ai(z) = (1/2πi) ∫_{c−i∞}^{c+i∞} exp(t³/3 − z t) dt
       = (1/2π) ∫_ℝ exp((c+is)³/3 − z(c+is)) ds`
(DLMF 9.5.4, with the contour straightened to the vertical line `Re t = c`).  Here `Ai` is
contrib's series-defined `Complex.airyAi` (`Airy/Airy.lean`, DLMF 9.4.1).

## Main definitions and results

* `AiryContour.airyContour c z`: the vertical-line integral `(1/2π) ∫_ℝ e^{(c+is)³/3 − z(c+is)} ds`.
* `integrable_airyContour_integrand`: the integrand is integrable for `c > 0`
  (`Re (c+is)³ = c³ − 3cs²` gives Gaussian decay).
* `differentiable_airyContour`, `deriv_airyContour`: it is entire, differentiation under the
  integral sign.
* `iteratedDeriv_two_airyContour`: the Airy equation `I'' = z I`
  (integrate the exact derivative of `e^{t³/3 − zt}` along the line).
* `airyContour_zero`, `deriv_airyContour_zero`: `I(0) = Ai(0)`, `I'(0) = Ai'(0)`, by deforming
  the line onto the ray `arg t = π/3` (rotation, then translation of the vertex) where the
  integrals are Γ-integrals.
* `eq_zero_of_iteratedDeriv_two_eq_mul`: an entire solution of `D'' = z D` with
  `D(0) = D'(0) = 0` vanishes (all Taylor coefficients at `0` vanish, by the recursion
  `D^{(n+2)}(0) = n D^{(n−1)}(0)`).
* `airyContour_eq_airyAi`: **`airyContour c = Complex.airyAi`** for every `c > 0`.
* `airyAiReal_eq_integral`: the real-variable form
  `Ai(x) = (1/2π) ∫_ℝ Re exp((c+is)³/3 − x(c+is)) ds`.

This file gives a contour representation of the series-defined `Ai`, the
entry point for a Fourier-side treatment of the Airy transform.  Nothing downstream in this
package uses it yet.
-/

open MeasureTheory Set Filter Topology Complex Metric

noncomputable section

namespace AiryContour

/-! ## A Gaussian-type dominator -/

/-- `K (1+|s|)^m exp(A + B|s| − a s²)`. -/
private def gdom (K A B a : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  K * (1 + |s|) ^ m * Real.exp (A + B * |s| - a * s ^ 2)

private lemma gdom_succ (K A B a : ℝ) (m : ℕ) (s : ℝ) :
    gdom K A B a m s * (1 + |s|) = gdom K A B a (m + 1) s := by
  unfold gdom; ring

private lemma integrable_exp_quad (a β : ℝ) (ha : 0 < a) :
    Integrable (fun s : ℝ => Real.exp (β * s - a * s ^ 2)) := by
  have h := integrable_cexp_quadratic (b := (a : ℂ)) (by simpa using ha) (β : ℂ) 0
  refine h.norm.congr (Eventually.of_forall fun s => ?_)
  simp only [Complex.norm_exp]
  rw [show -(a : ℂ) * (s : ℂ) ^ 2 + β * s + 0 = ((β * s - a * s ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

private lemma integrable_gdom (K A B a : ℝ) (m : ℕ) (ha : 0 < a) : Integrable (gdom K A B a m) := by
  have hb : Integrable (fun s : ℝ => (|K| * m.factorial * Real.exp (A + 1)) *
      (Real.exp ((B + 1) * s - a * s ^ 2) + Real.exp (-(B + 1) * s - a * s ^ 2))) :=
    ((integrable_exp_quad a (B + 1) ha).add (integrable_exp_quad a (-(B + 1)) ha)).const_mul _
  refine hb.mono' (by unfold gdom; fun_prop : Continuous (gdom K A B a m)).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  have h1 : (1 + |s|) ^ m ≤ m.factorial * Real.exp (1 + |s|) := by
    have := Real.pow_div_factorial_le_exp (x := 1 + |s|) (by positivity) m
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have h2 : Real.exp ((B + 1) * |s| - a * s ^ 2) ≤
      Real.exp ((B + 1) * s - a * s ^ 2) + Real.exp (-(B + 1) * s - a * s ^ 2) := by
    rcases abs_choice s with h | h <;> rw [h]
    · exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [show (B + 1) * -s = -(B + 1) * s by ring]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have h3 : Real.exp (A + B * |s| - a * s ^ 2) * Real.exp (1 + |s|) =
      Real.exp (A + 1) * Real.exp ((B + 1) * |s| - a * s ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [Real.norm_eq_abs, gdom, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + |s|) ^ m),
    abs_of_nonneg (Real.exp_pos _).le]
  calc |K| * (1 + |s|) ^ m * Real.exp (A + B * |s| - a * s ^ 2)
      ≤ |K| * (m.factorial * Real.exp (1 + |s|)) * Real.exp (A + B * |s| - a * s ^ 2) := by
        gcongr
    _ = |K| * m.factorial * (Real.exp (A + B * |s| - a * s ^ 2) * Real.exp (1 + |s|)) := by ring
    _ = |K| * m.factorial * Real.exp (A + 1) * Real.exp ((B + 1) * |s| - a * s ^ 2) := by
        rw [h3]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ## Cube of a complex number in Cartesian form -/

private lemma cube_eq (a b : ℝ) : ((a : ℂ) + b * I) ^ 3 =
    ((a ^ 3 - 3 * a * b ^ 2 : ℝ) : ℂ) + ((3 * a ^ 2 * b - b ^ 3 : ℝ) : ℂ) * I := by
  push_cast
  linear_combination (3 * (a : ℂ) * (b : ℂ) ^ 2 + (b : ℂ) ^ 3 * I) * Complex.I_sq

private lemma re_cube (a b : ℝ) : (((a : ℂ) + b * I) ^ 3).re = a ^ 3 - 3 * a * b ^ 2 := by
  rw [cube_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-! ## The vertical-line integral -/

variable (c : ℝ)

/-- The point `c + is` of the vertical contour. -/
private def tv (s : ℝ) : ℂ := (c : ℂ) + s * I

/-- The weighted integrand `t^k e^{t³/3 − zt}`, `t = c + is`. -/
private def Ek (k : ℕ) (z : ℂ) (s : ℝ) : ℂ := tv c s ^ k * cexp (tv c s ^ 3 / 3 - z * tv c s)

/-- `J k z = ∫ t^k e^{t³/3 − zt} ds`. -/
private def J (k : ℕ) (z : ℂ) : ℂ := ∫ s : ℝ, Ek c k z s

/-- The contour-integral Airy function `(1/2πi) ∫_{c−i∞}^{c+i∞} e^{t³/3 − zt} dt`. -/
def airyContour (z : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * ∫ s : ℝ, cexp (((c : ℂ) + s * I) ^ 3 / 3 - z * ((c : ℂ) + s * I))

private lemma airyContour_eq (z : ℂ) : airyContour c z = (1 / (2 * (Real.pi : ℂ))) * J c 0 z := by
  simp [airyContour, J, Ek, tv]

private lemma continuous_Ek (k : ℕ) (z : ℂ) : Continuous (Ek c k z) := by
  unfold Ek tv; fun_prop

private lemma norm_tv_le (hc : 0 < c) (s : ℝ) : ‖tv c s‖ ≤ c + |s| := by
  unfold tv
  calc ‖(c : ℂ) + s * I‖ ≤ ‖(c : ℂ)‖ + ‖(s : ℂ) * I‖ := norm_add_le _ _
    _ = c + |s| := by simp [abs_of_pos hc]

private lemma re_tv_cube (s : ℝ) : (tv c s ^ 3 / 3).re = (c ^ 3 - 3 * c * s ^ 2) / 3 := by
  unfold tv
  rw [Complex.div_ofNat_re, re_cube]

private lemma norm_Ek_le (hc : 0 < c) (k : ℕ) (z : ℂ) (R : ℝ) (hz : ‖z‖ ≤ R) (s : ℝ) :
    ‖Ek c k z s‖ ≤ gdom ((1 + c) ^ k) (c ^ 3 / 3 + R * c) R c k s := by
  have ht := norm_tv_le c hc s
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hz
  have h2 : -(z * tv c s).re ≤ R * (c + |s|) := by
    calc -(z * tv c s).re ≤ ‖z * tv c s‖ := by
          have := Complex.abs_re_le_norm (z * tv c s); linarith [neg_abs_le (z * tv c s).re]
      _ = ‖z‖ * ‖tv c s‖ := norm_mul _ _
      _ ≤ R * (c + |s|) := mul_le_mul hz ht (norm_nonneg _) hR
  have hre : (tv c s ^ 3 / 3 - z * tv c s).re ≤ c ^ 3 / 3 + R * c + R * |s| - c * s ^ 2 := by
    rw [Complex.sub_re, re_tv_cube]; nlinarith
  have hp : ‖tv c s‖ ^ k ≤ (1 + c) ^ k * (1 + |s|) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (by nlinarith [abs_nonneg s]) k
  rw [Ek, norm_mul, norm_pow, Complex.norm_exp, gdom]
  calc ‖tv c s‖ ^ k * Real.exp (tv c s ^ 3 / 3 - z * tv c s).re
      ≤ ((1 + c) ^ k * (1 + |s|) ^ k) * Real.exp (c ^ 3 / 3 + R * c + R * |s| - c * s ^ 2) :=
        mul_le_mul hp (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le (by positivity)
    _ = _ := by ring_nf

private lemma integrable_Ek (hc : 0 < c) (k : ℕ) (z : ℂ) : Integrable (Ek c k z) :=
  (integrable_gdom _ _ _ _ k hc).mono' (continuous_Ek c k z).aestronglyMeasurable
    (Eventually.of_forall fun s => norm_Ek_le c hc k z ‖z‖ le_rfl s)

private lemma hasDerivAt_Ek_z (k : ℕ) (z : ℂ) (s : ℝ) :
    HasDerivAt (fun z => Ek c k z s) (-(Ek c (k + 1) z s)) z := by
  have h := ((((hasDerivAt_id z).mul_const (tv c s)).const_sub (tv c s ^ 3 / 3)).cexp).const_mul
    (tv c s ^ k)
  convert h using 1
  · rfl
  show -(tv c s ^ (k + 1) * cexp (tv c s ^ 3 / 3 - z * tv c s)) = _
  simp only [id]
  ring

/-- `J k` is complex-differentiable with `J k' = −J (k+1)`. -/
private lemma hasDerivAt_J (hc : 0 < c) (k : ℕ) (z₀ : ℂ) :
    HasDerivAt (J c k) (-(J c (k + 1) z₀)) z₀ := by
  set R := ‖z₀‖ + 1
  have hball : ∀ z ∈ ball z₀ 1, ‖z‖ ≤ R := fun z hz => by
    rw [mem_ball, dist_eq_norm] at hz
    have := norm_sub_norm_le z z₀
    simp only [R]; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z s => Ek c k z s) (F' := fun z s => -(Ek c (k + 1) z s)) (x₀ := z₀)
    (bound := gdom ((1 + c) ^ (k + 1)) (c ^ 3 / 3 + R * c) R c (k + 1))
    (ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (continuous_Ek c k z).aestronglyMeasurable)
    (integrable_Ek c hc k z₀)
    ((continuous_Ek c (k + 1) z₀).neg.aestronglyMeasurable)
    (Eventually.of_forall fun s z hz => by
      rw [norm_neg]; exact norm_Ek_le c hc (k + 1) z R (hball z hz) s)
    (integrable_gdom _ _ _ _ _ hc)
    (Eventually.of_forall fun s z _ => hasDerivAt_Ek_z c k z s)
  have h2 := key.2
  rw [integral_neg] at h2
  exact h2

private lemma hasDerivAt_Ek0_s (z : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Ek c 0 z s) (I * (Ek c 2 z s - z * Ek c 0 z s)) s := by
  have ht : HasDerivAt (fun s : ℝ => tv c s) I s := by
    have := ((hasDerivAt_id s).ofReal_comp.mul_const I).const_add (c : ℂ)
    simpa [tv] using this
  have h := (((ht.pow 3).div_const 3).sub (ht.const_mul z)).cexp
  convert h using 1
  · funext s; simp [Ek]
  · simp only [Ek, Pi.sub_apply, Pi.pow_apply, pow_zero, one_mul]; norm_num; ring

/-- `∫ (t² − z) e^{t³/3 − zt} ds = 0`. -/
private lemma J_two (hc : 0 < c) (z : ℂ) : J c 2 z = z * J c 0 z := by
  have h := integral_eq_zero_of_hasDerivAt_of_integrable (fun s => hasDerivAt_Ek0_s c z s)
    (((integrable_Ek c hc 2 z).sub ((integrable_Ek c hc 0 z).const_mul z)).const_mul I)
    (integrable_Ek c hc 0 z)
  rw [integral_const_mul, integral_sub (integrable_Ek c hc 2 z)
    ((integrable_Ek c hc 0 z).const_mul z), integral_const_mul] at h
  have := (mul_eq_zero.mp h).resolve_left I_ne_zero
  unfold J; linear_combination this

/-! ## Integrability, holomorphy and the Airy equation -/

/-- The contour integrand is integrable for every `z`. -/
theorem integrable_airyContour_integrand (hc : 0 < c) (z : ℂ) :
    Integrable (fun s : ℝ => cexp (((c : ℂ) + s * I) ^ 3 / 3 - z * ((c : ℂ) + s * I))) := by
  refine (integrable_Ek c hc 0 z).congr (Eventually.of_forall fun s => ?_)
  simp [Ek, tv]

private theorem hasDerivAt_airyContour (hc : 0 < c) (z : ℂ) :
    HasDerivAt (airyContour c) ((1 / (2 * (Real.pi : ℂ))) * -(J c 1 z)) z := by
  have h := (hasDerivAt_J c hc 0 z).const_mul (1 / (2 * (Real.pi : ℂ)))
  rw [show airyContour c = fun z => (1 / (2 * (Real.pi : ℂ))) * J c 0 z from
    funext (airyContour_eq c)]
  exact h

/-- `airyContour c` is entire. -/
theorem differentiable_airyContour (hc : 0 < c) : Differentiable ℂ (airyContour c) :=
  fun z => (hasDerivAt_airyContour c hc z).differentiableAt

/-- `I'(z) = (1/2π) ∫ −t e^{t³/3 − zt} ds`. -/
theorem deriv_airyContour (hc : 0 < c) (z : ℂ) :
    deriv (airyContour c) z = (1 / (2 * (Real.pi : ℂ))) *
      ∫ s : ℝ, -(((c : ℂ) + s * I) * cexp (((c : ℂ) + s * I) ^ 3 / 3 - z * ((c : ℂ) + s * I))) := by
  rw [(hasDerivAt_airyContour c hc z).deriv, integral_neg]
  simp [J, Ek, tv]

/-- The Airy equation `I'' = z I`. -/
theorem iteratedDeriv_two_airyContour (hc : 0 < c) (z : ℂ) :
    iteratedDeriv 2 (airyContour c) z = z * airyContour c z := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hd : deriv (airyContour c) = fun z => (1 / (2 * (Real.pi : ℂ))) * -(J c 1 z) :=
    funext fun z => (hasDerivAt_airyContour c hc z).deriv
  rw [hd]
  have h2 : HasDerivAt (fun z => (1 / (2 * (Real.pi : ℂ))) * -(J c 1 z))
      ((1 / (2 * (Real.pi : ℂ))) * -(-(J c 2 z))) z :=
    ((hasDerivAt_J c hc 1 z).neg).const_mul _
  rw [h2.deriv, airyContour_eq, J_two c hc z]
  ring

/-! ## Initial data, by rotating and translating rays

The vertical line `c + iℝ` is deformed, inside the sector where `e^{t³/3}` decays, first by
rotating the upper half-ray about `c` from `arg = π/2` to `arg = π/3`, then by translating its
vertex from `c` to `0`.  Only the imaginary parts are tracked; the conjugate symmetry
`f(t̄) = f(t)‾` recovers the full line.  On the ray `r e^{iπ/3}` the integrand is a
Γ-integral. -/

/-- `∫_0^∞ f(v μ + r w μ) w μ dr`: a family of rays `v μ + ℝ₊ w μ`. -/
private def rayInt (f : ℂ → ℂ) (v w : ℝ → ℂ) (μ : ℝ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), f (v μ + r * w μ) * w μ

private lemma norm_lin_le {p q : ℂ} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (r : ℝ) : ‖p + r * q‖ ≤ 1 + |r| := by
  calc ‖p + r * q‖ ≤ ‖p‖ + ‖(r : ℂ) * q‖ := norm_add_le _ _
    _ = ‖p‖ + |r| * ‖q‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 + |r| * 1 := by gcongr
    _ = 1 + |r| := by ring

private lemma continuousOn_rayInt {f : ℂ → ℂ} (hfc : Continuous f) {v w : ℝ → ℂ} (hvc : Continuous v)
    (hwc : Continuous w) {S : Set ℝ} {K A B a : ℝ} {m : ℕ} (ha : 0 < a)
    (hb : ∀ μ ∈ S, ∀ r : ℝ, 0 < r → ‖f (v μ + r * w μ)‖ ≤ gdom K A B a m r)
    (hw1 : ∀ μ ∈ S, ‖w μ‖ ≤ 1) :
    ContinuousOn (rayInt f v w) S := by
  apply continuousOn_of_dominated (bound := gdom K A B a m)
  · intro μ _
    exact (by fun_prop : Continuous fun r : ℝ => f (v μ + r * w μ) * w μ).aestronglyMeasurable
  · intro μ hμ
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun r hr => ?_
    have h1 := hb μ hμ r hr
    rw [norm_mul]
    calc _ ≤ gdom K A B a m r * 1 :=
          mul_le_mul h1 (hw1 μ hμ) (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = _ := mul_one _
  · exact (integrable_gdom K A B a m ha).integrableOn
  · exact Eventually.of_forall fun r =>
      (by fun_prop : Continuous fun μ => f (v μ + r * w μ) * w μ).continuousOn

/-- **Ray homotopy.** `d/dμ ∫_0^∞ f(v + r w) w dr = −f(v) v'`, because the `μ`-derivative of the
integrand is the `r`-derivative of `f(v + r w)(v' + r w')`. -/
private lemma hasDerivAt_rayInt {f f' : ℂ → ℂ} (hf : ∀ t, HasDerivAt f (f' t) t) (hf'c : Continuous f')
    {v w v' w' : ℝ → ℂ} (hv : ∀ μ, HasDerivAt v (v' μ) μ) (hw : ∀ μ, HasDerivAt w (w' μ) μ)
    {μ₀ ε K A B a : ℝ} {m : ℕ} (hε : 0 < ε) (ha : 0 < a)
    (hb : ∀ μ ∈ ball μ₀ ε, ∀ r : ℝ, 0 < r →
      ‖f (v μ + r * w μ)‖ ≤ gdom K A B a m r ∧ ‖f' (v μ + r * w μ)‖ ≤ gdom K A B a m r)
    (hw1 : ∀ μ ∈ ball μ₀ ε, ‖w μ‖ ≤ 1 ∧ ‖v' μ‖ ≤ 1 ∧ ‖w' μ‖ ≤ 1) :
    HasDerivAt (rayInt f v w) (-(f (v μ₀) * v' μ₀)) μ₀ := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun t => (hv t).continuousAt
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun t => (hw t).continuousAt
  have hμ₀ : μ₀ ∈ ball μ₀ ε := mem_ball_self hε
  set F' : ℝ → ℝ → ℂ := fun μ r =>
    f' (v μ + r * w μ) * (v' μ + r * w' μ) * w μ + f (v μ + r * w μ) * w' μ with hF'
  have hderiv : ∀ μ r : ℝ, HasDerivAt (fun μ => f (v μ + r * w μ) * w μ) (F' μ r) μ := by
    intro μ r
    have h1 : HasDerivAt (fun μ => v μ + (r : ℂ) * w μ) (v' μ + r * w' μ) μ :=
      (hv μ).add ((hw μ).const_mul _)
    exact ((hf _).comp μ h1).mul (hw μ)
  have hF'b : ∀ μ ∈ ball μ₀ ε, ∀ r : ℝ, 0 < r → ‖F' μ r‖ ≤ gdom (2 * K) A B a (m + 1) r := by
    intro μ hμ r hr
    obtain ⟨h1, h2⟩ := hb μ hμ r hr
    obtain ⟨hw', hv', hw''⟩ := hw1 μ hμ
    have hG : 0 ≤ gdom K A B a m r := (norm_nonneg _).trans h1
    have hlin := norm_lin_le hv' hw'' r
    calc ‖F' μ r‖ ≤ ‖f' (v μ + r * w μ)‖ * ‖v' μ + r * w' μ‖ * ‖w μ‖ +
          ‖f (v μ + r * w μ)‖ * ‖w' μ‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul, norm_mul]
      _ ≤ gdom K A B a m r * (1 + |r|) * 1 + gdom K A B a m r * 1 := by gcongr
      _ ≤ 2 * (gdom K A B a m r * (1 + |r|)) := by nlinarith [abs_nonneg r]
      _ = gdom (2 * K) A B a (m + 1) r := by rw [gdom_succ]; unfold gdom; ring
  have hF'meas : AEStronglyMeasurable (F' μ₀) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous fun r : ℝ => f' (v μ₀ + r * w μ₀) * (v' μ₀ + r * w' μ₀) * w μ₀ +
      f (v μ₀ + r * w μ₀) * w' μ₀).aestronglyMeasurable
  have hFint : IntegrableOn (fun r : ℝ => f (v μ₀ + r * w μ₀) * w μ₀) (Ioi 0) := by
    refine ((integrable_gdom K A B a m ha).integrableOn).mono'
      (by fun_prop : Continuous fun r : ℝ => f (v μ₀ + r * w μ₀) * w μ₀).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun r hr => ?_
    have h1 := (hb μ₀ hμ₀ r hr).1
    rw [norm_mul]
    calc _ ≤ gdom K A B a m r * 1 :=
          mul_le_mul h1 (hw1 μ₀ hμ₀).1 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = _ := mul_one _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun μ r => f (v μ + r * w μ) * w μ) (F' := F') (x₀ := μ₀)
    (bound := gdom (2 * K) A B a (m + 1)) (ball_mem_nhds μ₀ hε)
    (Eventually.of_forall fun μ =>
      (by fun_prop : Continuous fun r : ℝ => f (v μ + r * w μ) * w μ).aestronglyMeasurable)
    hFint hF'meas
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun r hr μ hμ => hF'b μ hμ r hr)
    (integrable_gdom _ _ _ _ _ ha).integrableOn
    (Eventually.of_forall fun r μ _ => hderiv μ r)
  set g : ℝ → ℂ := fun r => f (v μ₀ + r * w μ₀) * (v' μ₀ + r * w' μ₀) with hg
  have hgd : ∀ r : ℝ, HasDerivAt g (F' μ₀ r) r := by
    intro r
    have hγ : HasDerivAt (fun r : ℝ => v μ₀ + (r : ℂ) * w μ₀) (w μ₀) r := by
      simpa using ((hasDerivAt_id r).ofReal_comp.mul_const (w μ₀)).const_add (v μ₀)
    have hl : HasDerivAt (fun r : ℝ => v' μ₀ + (r : ℂ) * w' μ₀) (w' μ₀) r := by
      simpa using ((hasDerivAt_id r).ofReal_comp.mul_const (w' μ₀)).const_add (v' μ₀)
    convert ((hf _).comp r hγ).mul hl using 1
    · rfl
    · simp only [hF', Function.comp]; ring
  have hgint : IntegrableOn g (Ioi 0) := by
    refine ((integrable_gdom K A B a (m + 1) ha).integrableOn).mono'
      (by simp only [hg]; fun_prop : Continuous g).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun r hr => ?_
    have h1 := (hb μ₀ hμ₀ r hr).1
    obtain ⟨_, hv', hw''⟩ := hw1 μ₀ hμ₀
    rw [norm_mul, ← gdom_succ]
    exact mul_le_mul h1 (norm_lin_le hv' hw'' r) (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hlim := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun r _ => hgd r) key.1 hgint
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto (hgd 0).continuousAt.continuousWithinAt
    (fun r _ => hgd r) key.1 hlim
  have h2 := key.2
  rw [hftc] at h2
  have h3 : -(f (v μ₀) * v' μ₀) = 0 - g 0 := by simp [hg]
  rw [h3]
  exact h2

/-! ### The integrands `t^k e^{t³/3}` -/

private def fk (k : ℕ) (t : ℂ) : ℂ := t ^ k * cexp (t ^ 3 / 3)

private def fk' (k : ℕ) (t : ℂ) : ℂ := (k * t ^ (k - 1) + t ^ (k + 2)) * cexp (t ^ 3 / 3)

private lemma hasDerivAt_fk (k : ℕ) (t : ℂ) : HasDerivAt (fk k) (fk' k t) t := by
  show HasDerivAt (fun t => t ^ k * cexp (t ^ 3 / 3)) _ t
  have h := (hasDerivAt_pow k t).mul (((hasDerivAt_pow 3 t).div_const 3).cexp)
  convert h using 1
  simp only [fk']; norm_num; ring

private lemma continuous_fk (k : ℕ) : Continuous (fk k) := by unfold fk; fun_prop

private lemma continuous_fk' (k : ℕ) : Continuous (fk' k) := by unfold fk'; fun_prop

private lemma fk_conj (k : ℕ) (t : ℂ) : fk k ((starRingEnd ℂ) t) = (starRingEnd ℂ) (fk k t) := by
  unfold fk
  rw [map_mul, map_pow, ← Complex.exp_conj, map_div₀, map_pow, map_ofNat]

private lemma fk_ofReal_im (k : ℕ) (x : ℝ) : (fk k (x : ℂ)).im = 0 := by
  have : fk k (x : ℂ) = ((x ^ k * Real.exp (x ^ 3 / 3) : ℝ) : ℂ) := by
    unfold fk; push_cast; rfl
  rw [this, Complex.ofReal_im]

private lemma norm_cexp_cube (t : ℂ) : ‖cexp (t ^ 3 / 3)‖ = Real.exp ((t ^ 3).re / 3) := by
  rw [Complex.norm_exp, Complex.div_ofNat_re]

private lemma norm_fk_le (k : ℕ) {t : ℂ} {c r A a : ℝ} (hc : 0 ≤ c) (hr : 0 < r) (ht : ‖t‖ ≤ c + r)
    (hre : (t ^ 3).re / 3 ≤ A + c ^ 2 / 2 * r - a * r ^ 2) :
    ‖fk k t‖ ≤ gdom ((k + 1) * (1 + c) ^ (k + 2)) A (c ^ 2 / 2) a (k + 2) r ∧
    ‖fk' k t‖ ≤ gdom ((k + 1) * (1 + c) ^ (k + 2)) A (c ^ 2 / 2) a (k + 2) r := by
  have h1 : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have hP : (1 + ‖t‖) ^ (k + 2) ≤ (1 + c) ^ (k + 2) * (1 + |r|) ^ (k + 2) := by
    rw [← mul_pow, abs_of_pos hr]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have hE : Real.exp ((t ^ 3).re / 3) ≤ Real.exp (A + c ^ 2 / 2 * |r| - a * r ^ 2) := by
    rw [abs_of_pos hr]; exact Real.exp_le_exp.mpr hre
  have hpow : ∀ j ≤ k + 2, ‖t‖ ^ j ≤ (1 + ‖t‖) ^ (k + 2) := fun j hj =>
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith) j).trans (pow_le_pow_right₀ h1 hj)
  have hfin : ∀ X : ℝ, 0 ≤ X → X ≤ (k + 1) * (1 + ‖t‖) ^ (k + 2) →
      X * Real.exp ((t ^ 3).re / 3) ≤ gdom ((k + 1) * (1 + c) ^ (k + 2)) A (c ^ 2 / 2) a (k + 2) r := by
    intro X hX0 hX
    unfold gdom
    calc X * Real.exp ((t ^ 3).re / 3)
        ≤ ((k + 1) * ((1 + c) ^ (k + 2) * (1 + |r|) ^ (k + 2))) *
            Real.exp (A + c ^ 2 / 2 * |r| - a * r ^ 2) := by
          gcongr
          exact hX.trans (by gcongr)
      _ = _ := by ring
  constructor
  · rw [fk, norm_mul, norm_cexp_cube, norm_pow]
    refine hfin _ (by positivity) ?_
    have := hpow k (by omega)
    nlinarith [pow_nonneg (norm_nonneg t) k]
  · rw [fk', norm_mul, norm_cexp_cube]
    refine hfin _ (norm_nonneg _) ?_
    calc ‖(k : ℂ) * t ^ (k - 1) + t ^ (k + 2)‖ ≤ k * ‖t‖ ^ (k - 1) + ‖t‖ ^ (k + 2) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
      _ ≤ k * (1 + ‖t‖) ^ (k + 2) + (1 + ‖t‖) ^ (k + 2) :=
          add_le_add (mul_le_mul_of_nonneg_left (hpow _ (by omega)) (Nat.cast_nonneg k))
            (hpow _ le_rfl)
      _ = _ := by ring

private lemma re_cube_ray_le {c v u σ r : ℝ} (hv0 : 0 ≤ v) (hvc : v ≤ c) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2)
    (hus : u ^ 2 + σ ^ 2 = 1) (hr : 0 ≤ r) :
    (((v : ℂ) + r * ((u : ℂ) + σ * I)) ^ 3).re ≤
      c ^ 3 + 3 / 2 * c ^ 2 * r - 3 / 2 * v * r ^ 2 + r ^ 3 * (4 * u ^ 3 - 3 * u) := by
  rw [show (v : ℂ) + r * ((u : ℂ) + σ * I) = ((v + r * u : ℝ) : ℂ) + ((r * σ : ℝ) : ℂ) * I by
    push_cast; ring, re_cube]
  have hσ : σ ^ 2 = 1 - u ^ 2 := by linarith
  have e : (v + r * u) ^ 3 - 3 * (v + r * u) * (r * σ) ^ 2 =
      v ^ 3 + 3 * v ^ 2 * r * u + v * r ^ 2 * (6 * u ^ 2 - 3) + r ^ 3 * (4 * u ^ 3 - 3 * u) := by
    rw [mul_pow, hσ]; ring
  rw [e]
  have h1 : v ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ hv0 hvc 3
  have hv2 : v ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hv0 hvc 2
  have h2 : v ^ 2 * r * u ≤ c ^ 2 * r * (1 / 2) := by gcongr
  have h3 : 6 * u ^ 2 - 3 ≤ -(3 / 2) := by nlinarith
  have hvr : 0 ≤ v * r ^ 2 := by positivity
  nlinarith

private lemma cexp_mul_I_eq (θ : ℝ) : cexp (θ * I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma hasDerivAt_cexp_mul_I (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => cexp (θ * I)) (cexp (θ * I) * I) θ := by
  simpa using ((hasDerivAt_id θ).ofReal_comp.mul_const I).cexp

private lemma im_eq_of_deriv {g d : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hcont : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (d x) x) (hd0 : ∀ x ∈ Ioo a b, (d x).im = 0) :
    (g b).im = (g a).im := by
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope (fun x => (g x).im) (fun x => (d x).im) hab
    (Complex.continuous_im.comp_continuousOn hcont)
    (fun x hx => by
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hd x hx)
      exact this)
  rw [hd0 ξ hξ, eq_comm, div_eq_zero_iff] at h
  rcases h with h | h <;> linarith

/-! ### Rotation about `c` from `π/2` to `π/3` -/

private lemma rot_bound (hc : 0 < c) (k : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 3) (Real.pi / 2)) {r : ℝ}
    (hr : 0 < r) :
    ‖fk k ((c : ℂ) + r * cexp (θ * I))‖ ≤
        gdom ((k + 1) * (1 + c) ^ (k + 2)) (c ^ 3 / 3) (c ^ 2 / 2) (c / 2) (k + 2) r ∧
    ‖fk' k ((c : ℂ) + r * cexp (θ * I))‖ ≤
        gdom ((k + 1) * (1 + c) ^ (k + 2)) (c ^ 3 / 3) (c ^ 2 / 2) (c / 2) (k + 2) r := by
  have hu0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hu : Real.cos θ ≤ 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [hθ.2, Real.pi_pos]) hθ.1
  refine norm_fk_le k hc.le hr ?_ ?_
  · calc ‖(c : ℂ) + r * cexp (θ * I)‖ ≤ ‖(c : ℂ)‖ + ‖(r : ℂ) * cexp (θ * I)‖ := norm_add_le _ _
      _ = c + r := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hc.le, Real.norm_of_nonneg hr.le, mul_one]
  · rw [cexp_mul_I_eq]
    have h := re_cube_ray_le (c := c) hc.le le_rfl hu0 hu (Real.cos_sq_add_sin_sq θ) hr.le
    have : r ^ 3 * (4 * Real.cos θ ^ 3 - 3 * Real.cos θ) ≤ 0 := by
      have : 0 ≤ Real.cos θ * (3 - 4 * Real.cos θ ^ 2) := mul_nonneg hu0 (by nlinarith)
      nlinarith [pow_pos hr 3]
    linarith

/-- The rotated ray integral `Φ(θ) = ∫_0^∞ f(c + r e^{iθ}) e^{iθ} dr`. -/
private def Φ (k : ℕ) : ℝ → ℂ := rayInt (fk k) (fun _ => (c : ℂ)) (fun θ => cexp (θ * I))

private lemma Φ_im_rotate (hc : 0 < c) (k : ℕ) :
    (Φ c k (Real.pi / 2)).im = (Φ c k (Real.pi / 3)).im := by
  have hab : Real.pi / 3 < Real.pi / 2 := by linarith [Real.pi_pos]
  refine im_eq_of_deriv (d := fun _ => -(fk k c * 0)) hab ?_ ?_ (fun _ _ => by simp)
  · exact continuousOn_rayInt (continuous_fk k) continuous_const (by fun_prop)
      (half_pos hc) (fun θ hθ r hr => (rot_bound c hc k hθ hr).1)
      (fun θ _ => (Complex.norm_exp_ofReal_mul_I θ).le)
  · intro x hx
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp isOpen_Ioo x hx
    exact hasDerivAt_rayInt (hasDerivAt_fk k) (continuous_fk' k)
      (v' := fun _ => 0) (fun _ => hasDerivAt_const _ _) hasDerivAt_cexp_mul_I hε (half_pos hc)
      (fun θ hθ r hr => rot_bound c hc k (Ioo_subset_Icc_self (hsub hθ)) hr)
      (fun θ _ => ⟨(Complex.norm_exp_ofReal_mul_I θ).le, by simp, by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, one_mul]⟩)

/-! ### Translation of the vertex from `c` to `0` along `arg t = π/3` -/

/-- `ω = e^{iπ/3}`. -/
private def ω : ℂ := cexp (((Real.pi / 3 : ℝ) : ℂ) * I)

private lemma ω_eq : ω = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
  rw [ω, cexp_mul_I_eq, Real.cos_pi_div_three, Real.sin_pi_div_three]

private lemma trans_bound (hc : 0 < c) (k : ℕ) {l : ℝ} (hl : l ∈ Icc 0 c) {r : ℝ} (hr : 0 < r) :
    ‖fk k ((l : ℂ) + r * ω)‖ ≤
        gdom ((k + 1) * (1 + c) ^ (k + 2)) ((c ^ 3 + 1) / 3) (c ^ 2 / 2) (1 / 3) (k + 2) r ∧
    ‖fk' k ((l : ℂ) + r * ω)‖ ≤
        gdom ((k + 1) * (1 + c) ^ (k + 2)) ((c ^ 3 + 1) / 3) (c ^ 2 / 2) (1 / 3) (k + 2) r := by
  refine norm_fk_le k hc.le hr ?_ ?_
  · calc ‖(l : ℂ) + r * ω‖ ≤ ‖(l : ℂ)‖ + ‖(r : ℂ) * ω‖ := norm_add_le _ _
      _ ≤ c + r := by
        rw [norm_mul, ω, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hl.1, Real.norm_of_nonneg hr.le, mul_one]
        linarith [hl.2]
  · rw [ω_eq]
    have hus : (1 / 2 : ℝ) ^ 2 + (Real.sqrt 3 / 2) ^ 2 = 1 := by
      have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      linear_combination h / 4
    have h := re_cube_ray_le (c := c) hl.1 hl.2 (by norm_num) le_rfl hus hr.le
    have h3 : r ^ 2 - 1 ≤ r ^ 3 := by
      rcases le_total r 1 with h | h
      · nlinarith [sq_nonneg r]
      · nlinarith [sq_nonneg r]
    have hlr : 0 ≤ l * r ^ 2 := mul_nonneg hl.1 (sq_nonneg r)
    nlinarith

/-- The translated ray integral `H(λ) = ∫_0^∞ f(λ + r ω) ω dr`. -/
private def H (k : ℕ) : ℝ → ℂ := rayInt (fk k) (fun l => (l : ℂ)) (fun _ => ω)

private lemma H_im_translate (hc : 0 < c) (k : ℕ) : (H k c).im = (H k 0).im := by
  refine im_eq_of_deriv (d := fun l => -(fk k (l : ℂ) * 1)) hc ?_ ?_
    (fun l _ => by simp [fk_ofReal_im])
  · exact continuousOn_rayInt (continuous_fk k) (by fun_prop) continuous_const
      (by norm_num : (0 : ℝ) < 1 / 3) (fun l hl r hr => (trans_bound c hc k hl hr).1)
      (fun _ _ => by rw [ω, Complex.norm_exp_ofReal_mul_I])
  · intro x hx
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp isOpen_Ioo x hx
    exact hasDerivAt_rayInt (hasDerivAt_fk k) (continuous_fk' k)
      (v' := fun _ => 1) (w' := fun _ => 0)
      (fun l => by simpa using (hasDerivAt_id l).ofReal_comp) (fun _ => hasDerivAt_const _ _)
      hε (by norm_num : (0 : ℝ) < 1 / 3)
      (fun l hl r hr => trans_bound c hc k (Ioo_subset_Icc_self (hsub hl)) hr)
      (fun _ _ => ⟨by rw [ω, Complex.norm_exp_ofReal_mul_I], by simp, by simp⟩)

/-! ### Rays from the origin: Γ-integrals -/

private lemma ω_cube : ω ^ 3 = -1 := by
  rw [ω, ← Complex.exp_nat_mul, show ((3 : ℕ) : ℂ) * (((Real.pi / 3 : ℝ) : ℂ) * I) =
    (Real.pi : ℂ) * I by push_cast; ring, Complex.exp_pi_mul_I]

/-- `G k = ∫_0^∞ r^k e^{−r³/3} dr`. -/
private def G (k : ℕ) : ℝ := (1 / 3 : ℝ) ^ (-((k : ℝ) + 1) / 3) * (1 / 3) * Real.Gamma (((k : ℝ) + 1) / 3)

private lemma integral_G (k : ℕ) :
    ∫ r in Ioi (0 : ℝ), r ^ k * Real.exp (-(1 / 3) * r ^ 3) = G k := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 3) (q := k) (b := 1 / 3) (by norm_num)
    (by have := k.cast_nonneg (α := ℝ); linarith) (by norm_num)
  simp only [Real.rpow_natCast, Real.rpow_ofNat] at h
  rw [h, G]

private lemma H_zero (k : ℕ) : H k 0 = ω ^ (k + 1) * (G k : ℂ) := by
  have hpt : ∀ r : ℝ, fk k ((((0 : ℝ) : ℂ)) + r * ω) * ω =
      ω ^ (k + 1) * ((r ^ k * Real.exp (-(1 / 3) * r ^ 3) : ℝ) : ℂ) := by
    intro r
    have h3 : ((r : ℂ) * ω) ^ 3 / 3 = ((-(1 / 3) * r ^ 3 : ℝ) : ℂ) := by
      rw [mul_pow, ω_cube]; push_cast; ring
    unfold fk
    rw [Complex.ofReal_zero, zero_add, h3, ← Complex.ofReal_exp]
    push_cast; ring
  unfold H rayInt
  simp_rw [hpt]
  rw [integral_const_mul, integral_complex_ofReal, integral_G]

private lemma H_zero_im (k : ℕ) : (H k 0).im = Real.sin (((k : ℝ) + 1) * (Real.pi / 3)) * G k := by
  rw [H_zero, Complex.im_mul_ofReal, ω, ← Complex.exp_nat_mul,
    show ((k + 1 : ℕ) : ℂ) * (((Real.pi / 3 : ℝ) : ℂ) * I) =
      ((((k : ℝ) + 1) * (Real.pi / 3) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_im]

/-! ### From the vertical line to the rays -/

private lemma J_zero_eq (hc : 0 < c) (k : ℕ) :
    J c k 0 = ((2 * (Real.sin (((k : ℝ) + 1) * (Real.pi / 3)) * G k) : ℝ) : ℂ) := by
  have hE : ∀ s, Ek c k 0 s = fk k ((c : ℂ) + s * I) := fun s => by simp [Ek, tv, fk]
  have hint : Integrable (fun s : ℝ => fk k ((c : ℂ) + s * I)) :=
    (integrable_Ek c hc k 0).congr (Eventually.of_forall hE)
  set X := ∫ r in Ioi (0 : ℝ), fk k ((c : ℂ) + r * I) with hX
  have hneg : ∫ s in Iic (0 : ℝ), fk k ((c : ℂ) + s * I) = (starRingEnd ℂ) X := by
    rw [← neg_zero, ← integral_comp_neg_Ioi, hX, ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [← fk_conj]
    congr 1
    simp [Complex.conj_ofReal]
  have hsplit : J c k 0 = X + (starRingEnd ℂ) X := by
    unfold J
    simp_rw [hE]
    rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn, hneg, add_comm]
  have hΦ : Φ c k (Real.pi / 2) = X * I := by
    have hI : cexp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
      rw [cexp_mul_I_eq, Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
    unfold Φ rayInt
    simp_rw [hI]
    rw [integral_mul_const]
  have hre : X.re = (H k 0).im := by
    rw [← H_im_translate c hc k, show H k c = Φ c k (Real.pi / 3) from rfl,
      ← Φ_im_rotate c hc k, hΦ, Complex.mul_I_im]
  rw [hsplit, Complex.add_conj, hre, H_zero_im]

private lemma sqrt_three_rpow_one : Real.sqrt 3 * (1 / 3 : ℝ) ^ (-((0 : ℝ) + 1) / 3) * (1 / 3) =
    (3 : ℝ) ^ (-1 / 6 : ℝ) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [show (1 / 3 : ℝ) = 3⁻¹ by norm_num, Real.sqrt_eq_rpow, Real.inv_rpow h3.le, ← Real.rpow_neg h3.le,
    ← Real.rpow_neg_one, ← Real.rpow_add h3, ← Real.rpow_add h3]
  norm_num

private lemma sqrt_three_rpow_two : Real.sqrt 3 * (1 / 3 : ℝ) ^ (-((1 : ℝ) + 1) / 3) * (1 / 3) =
    (3 : ℝ) ^ (1 / 6 : ℝ) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [show (1 / 3 : ℝ) = 3⁻¹ by norm_num, Real.sqrt_eq_rpow, Real.inv_rpow h3.le, ← Real.rpow_neg h3.le,
    ← Real.rpow_neg_one, ← Real.rpow_add h3, ← Real.rpow_add h3]
  norm_num

/-- `I(0) = Ai(0)`. -/
theorem airyContour_zero (hc : 0 < c) : airyContour c 0 = Complex.airyAi 0 := by
  have hAi : Complex.airyAi 0 = ((Real.Gamma (1 / 3) * 3 ^ (-1 / 6 : ℝ) / 2 / Real.pi : ℝ) : ℂ) := by
    rw [← Complex.ofReal_zero, ← airyAiReal_ofReal, airyBesselY0_eq]
    congr 1; field_simp
  rw [airyContour_eq, J_zero_eq c hc 0, hAi, G]
  simp only [Nat.cast_zero]
  rw [show ((0 : ℝ) + 1) * (Real.pi / 3) = Real.pi / 3 by ring, Real.sin_pi_div_three,
    show ((0 : ℝ) + 1) / 3 = 1 / 3 by ring]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← sqrt_three_rpow_one]
  field_simp
  push_cast
  field_simp

/-- `I'(0) = Ai'(0)`. -/
theorem deriv_airyContour_zero (hc : 0 < c) :
    deriv (airyContour c) 0 = deriv Complex.airyAi 0 := by
  have hreal : deriv Complex.airyAi 0 = ((deriv airyAiReal 0 : ℝ) : ℂ) := by
    rw [deriv_airyAiReal_zero, Complex.deriv_airyAi_zero,
      show (-4 / 3 : ℂ) = ((-4 / 3 : ℝ) : ℂ) by norm_num, Complex.three_cpow_ofReal,
      show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal]
    push_cast; ring
  have hAi : deriv Complex.airyAi 0 =
      ((-(3 ^ (1 / 6 : ℝ)) * Real.Gamma (2 / 3) / 2 / Real.pi : ℝ) : ℂ) := by
    rw [hreal, airyBesselY1_eq]
    congr 1; field_simp
  rw [(hasDerivAt_airyContour c hc 0).deriv, J_zero_eq c hc 1, hAi, G]
  simp only [Nat.cast_one]
  rw [show ((1 : ℝ) + 1) * (Real.pi / 3) = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
    Real.sin_pi_div_three, show ((1 : ℝ) + 1) / 3 = 2 / 3 by ring]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← sqrt_three_rpow_two]
  field_simp
  push_cast
  field_simp

/-! ## Uniqueness for the Airy equation on `ℂ` -/

/-- Leibniz for `D'' = z D`: `D^{(n+2)}(z) = z D^{(n)}(z) + n D^{(n−1)}(z)`. -/
private lemma iteratedDeriv_add_two_eq {D : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hode : ∀ z, iteratedDeriv 2 D z = z * D z) (n : ℕ) (z : ℂ) :
    iteratedDeriv (n + 2) D z = z * iteratedDeriv n D z + n * iteratedDeriv (n - 1) D z := by
  have hdiff : ∀ k, Differentiable ℂ (iteratedDeriv k D) := fun k => by
    rw [iteratedDeriv_eq_iterate]; exact ((hD.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).iterate_deriv k).differentiable (by simp)
  have hhas : ∀ k w, HasDerivAt (iteratedDeriv k D) (iteratedDeriv (k + 1) D w) w := by
    intro k w; rw [iteratedDeriv_succ]; exact (hdiff k w).hasDerivAt
  induction n generalizing z with
  | zero => simp [hode z]
  | succ n ih =>
    have hfun : iteratedDeriv (n + 2) D =
        fun z => z * iteratedDeriv n D z + (n : ℂ) * iteratedDeriv (n - 1) D z := funext ih
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, iteratedDeriv_succ, hfun]
    have h : HasDerivAt (fun z => z * iteratedDeriv n D z + (n : ℂ) * iteratedDeriv (n - 1) D z)
        (1 * iteratedDeriv n D z + z * iteratedDeriv (n + 1) D z +
          (n : ℂ) * iteratedDeriv (n - 1 + 1) D z) z :=
      ((hasDerivAt_id' z).mul (hhas n z)).add ((hhas (n - 1) z).const_mul (n : ℂ))
    rw [h.deriv]
    rcases n with _ | m
    · simp; ring
    · simp only [Nat.add_sub_cancel]
      push_cast; ring

/-- **Uniqueness for the Airy equation.** An entire `D` with `D'' = z D` and
`D(0) = D'(0) = 0` is identically zero. -/
theorem eq_zero_of_iteratedDeriv_two_eq_mul {D : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hode : ∀ z, iteratedDeriv 2 D z = z * D z) (h0 : D 0 = 0) (h1 : deriv D 0 = 0) :
    D = 0 := by
  have hzero : ∀ n, iteratedDeriv n D 0 = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, ih with
      | 0, _ => simpa using h0
      | 1, _ => simpa using h1
      | k + 2, ih =>
        rw [iteratedDeriv_add_two_eq hD hode k 0, ih (k - 1) (by omega)]
        simp
  funext z
  rw [← taylorSeries_eq_of_entire' 0 z hD, Pi.zero_apply]
  simp [hzero]

/-- **The contour integral is `Ai`.** For every `c > 0`,
`(1/2π) ∫_ℝ exp((c+is)³/3 − z(c+is)) ds = Ai(z)` for all `z : ℂ` (DLMF 9.5.4). -/
theorem airyContour_eq_airyAi (hc : 0 < c) : airyContour c = Complex.airyAi := by
  have hA := differentiable_airyContour c hc
  have hB : Differentiable ℂ Complex.airyAi := fun z => (Complex.analyticAt_airyAi z).differentiableAt
  have hD : Differentiable ℂ (fun z => airyContour c z - Complex.airyAi z) := hA.sub hB
  have hode : ∀ z, iteratedDeriv 2 (fun z => airyContour c z - Complex.airyAi z) z =
      z * (airyContour c z - Complex.airyAi z) := by
    intro z
    rw [iteratedDeriv_fun_sub hA.contDiff.contDiffAt hB.contDiff.contDiffAt,
      iteratedDeriv_two_airyContour c hc, Complex.iteratedDeriv_two_airyAi]
    ring
  have h0 : airyContour c 0 - Complex.airyAi 0 = 0 := by rw [airyContour_zero c hc, sub_self]
  have h1 : deriv (fun z => airyContour c z - Complex.airyAi z) 0 = 0 := by
    rw [deriv_fun_sub (hA 0) (hB 0), deriv_airyContour_zero c hc, sub_self]
  have := eq_zero_of_iteratedDeriv_two_eq_mul hD hode h0 h1
  funext z
  exact sub_eq_zero.mp (congrFun this z)

/-- `Ai(z) = (1/2π) ∫_ℝ exp((c+is)³/3 − z(c+is)) ds` for every `c > 0` and `z : ℂ`. -/
theorem airyAi_eq_integral (hc : 0 < c) (z : ℂ) :
    Complex.airyAi z = (1 / (2 * (Real.pi : ℂ))) *
      ∫ s : ℝ, cexp (((c : ℂ) + s * I) ^ 3 / 3 - z * ((c : ℂ) + s * I)) := by
  rw [← airyContour_eq_airyAi c hc]; rfl

/-- Real form: for `x : ℝ` and `c > 0`,
`Ai(x) = (1/2π) ∫_ℝ Re exp((c+is)³/3 − x(c+is)) ds`. -/
theorem airyAiReal_eq_integral (hc : 0 < c) (x : ℝ) :
    airyAiReal x = (1 / (2 * Real.pi)) *
      ∫ s : ℝ, (cexp (((c : ℂ) + s * I) ^ 3 / 3 - (x : ℂ) * ((c : ℂ) + s * I))).re := by
  have hint := integrable_airyContour_integrand c hc (x : ℂ)
  have h := integral_re hint
  simp only [RCLike.re_to_complex] at h
  rw [airyAiReal, airyAi_eq_integral c hc, h,
    show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul]

end AiryContour

end
