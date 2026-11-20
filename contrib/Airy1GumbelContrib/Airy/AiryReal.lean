/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryODE
import Mathlib.Analysis.Complex.RealDeriv

/-! # Real-valued Airy functions

The Airy functions `Complex.airyAi` and `Complex.airyBi` are real-valued on the real axis
(all coefficients of their defining `₀F̃₁` series are real, cf. `Complex.airyAi_conj` and
`Complex.airyBi_conj` in `Airy1GumbelContrib.Airy.AiryODE`).  This file introduces the
real restrictions `airyAiReal, airyBiReal : ℝ → ℝ`, transfers the Airy differential
equation to them, and evaluates the derivatives at the origin.

## Main results

* `airyAiReal_ofReal`, `airyBiReal_ofReal`: `↑(airyAiReal x) = Complex.airyAi ↑x`
  (and the `Bi` analogue): the real functions really are the restrictions.
* `hasDerivAt_airyAiReal`, `hasDerivAt_airyBiReal`: real differentiability, with derivative
  the real part of the complex derivative (`HasDerivAt.real_of_complex`).
* `iteratedDeriv_two_airyAiReal`, `iteratedDeriv_two_airyBiReal`: the real Airy ODE
  `iteratedDeriv 2 airyAiReal x = x * airyAiReal x`.
* `deriv_airyAi_zero`, `deriv_airyBi_zero`: the derivative values at `0`,
  `Ai'(0) = -3^(-4/3)/Γ(4/3)` and `Bi'(0) = 3^(-5/6)/Γ(4/3)` (DLMF 9.2, using
  `Γ(4/3) = Γ(1/3)/3`), and the real versions `deriv_airyAiReal_zero`, `deriv_airyBiReal_zero`.
* `airyAiReal_zero_pos`, `deriv_airyAiReal_zero_neg`, `airyBiReal_zero_pos`,
  `deriv_airyBiReal_zero_pos`: signs at the origin.
* `Complex.Gamma_four_thirds`, `Real.Gamma_four_thirds`: `Γ(4/3) = Γ(1/3)/3`.
-/

open scoped Topology

namespace Complex

/-- For real `t`, the complex power `(3 : ℂ) ^ (t : ℂ)` is the cast of the real power
`3 ^ t`. -/
theorem three_cpow_ofReal (t : ℝ) : (3 : ℂ) ^ (t : ℂ) = ((3 ^ t : ℝ) : ℂ) := by
  rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, ← ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3) t]

/-- `Γ(4/3) = Γ(1/3)/3` (complex). -/
theorem Gamma_four_thirds : Complex.Gamma (4/3 : ℂ) = Complex.Gamma (1/3 : ℂ) / 3 := by
  have h := Complex.Gamma_add_one (1/3 : ℂ) (by norm_num)
  rw [show (1/3 : ℂ) + 1 = 4/3 by norm_num] at h
  rw [h]
  ring

/-- The singleton regularized hypergeometric function at `0`: `₀F̃₁(; b; 0) = 1/Γ(b)`. -/
theorem regularizedHGFun_zero_singleton_apply_zero (b : ℂ) :
    regularizedHGFun 0 {b} 0 = 1 / Complex.Gamma b := by
  rw [regularizedHGFun_zero]
  simp [regularizedHGFunCoeff]

/-- The derivative of `Ai` at `0`: `Ai'(0) = -3^(-4/3)/Γ(4/3)` (DLMF 9.2.4, using
`Γ(4/3) = Γ(1/3)/3`; the first hypergeometric summand contributes `0` since its derivative
carries a factor `z²/3`). -/
theorem deriv_airyAi_zero :
    deriv airyAi 0 = -((3 : ℂ)^(-4/3 : ℂ) / Complex.Gamma (4/3 : ℂ)) := by
  have h03 : (0 : ℂ)^3/9 = 0 := by norm_num
  have h1 := hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (2/3 : ℂ) 0
  have h2 := hasDerivAt_z_mul_four_thirds 0
  have h := (h1.const_mul ((3:ℂ)^(-2/3 : ℂ))).sub (h2.const_mul ((3:ℂ)^(-4/3 : ℂ)))
  rw [airyAi_eq]
  convert h.deriv using 1
  rw [h03, regularizedHGFun_zero_singleton_apply_zero (4/3 : ℂ)]
  ring

/-- The derivative of `Bi` at `0`: `Bi'(0) = 3^(-5/6)/Γ(4/3)` (DLMF 9.2.4). -/
theorem deriv_airyBi_zero :
    deriv airyBi 0 = (3 : ℂ)^(-5/6 : ℂ) / Complex.Gamma (4/3 : ℂ) := by
  have h03 : (0 : ℂ)^3/9 = 0 := by norm_num
  have h1 := hasDerivAt_regularizedHGFun_zero_singleton_comp_cube_div_nine (2/3 : ℂ) 0
  have h2 := hasDerivAt_z_mul_four_thirds 0
  have h := (h1.const_mul ((3:ℂ)^(-1/6 : ℂ))).add (h2.const_mul ((3:ℂ)^(-5/6 : ℂ)))
  rw [airyBi_eq]
  convert h.deriv using 1
  rw [h03, regularizedHGFun_zero_singleton_apply_zero (4/3 : ℂ)]
  ring

/-- `deriv (deriv airyAi)` exists everywhere (it equals `z * airyAi z`). -/
theorem differentiableAt_deriv_airyAi (z : ℂ) : DifferentiableAt ℂ (deriv airyAi) z := by
  rw [deriv_airyAi]
  exact ((hasDerivAt_deriv_u_two_thirds z).differentiableAt.const_mul _).sub
    ((hasDerivAt_deriv_z_mul_four_thirds z).differentiableAt.const_mul _)

/-- `deriv (deriv airyBi)` exists everywhere. -/
theorem differentiableAt_deriv_airyBi (z : ℂ) : DifferentiableAt ℂ (deriv airyBi) z := by
  rw [deriv_airyBi]
  exact ((hasDerivAt_deriv_u_two_thirds z).differentiableAt.const_mul _).add
    ((hasDerivAt_deriv_z_mul_four_thirds z).differentiableAt.const_mul _)

end Complex

/-- The real-valued Airy function of the first kind on `ℝ`.  It equals `Complex.airyAi` at
real points (`airyAiReal_ofReal`). -/
noncomputable def airyAiReal (x : ℝ) : ℝ := (Complex.airyAi (x : ℂ)).re

/-- The real-valued Airy function of the second kind on `ℝ`. -/
noncomputable def airyBiReal (x : ℝ) : ℝ := (Complex.airyBi (x : ℂ)).re

/-- `Ai` is real-valued on the real axis: `↑(airyAiReal x) = airyAi ↑x`. -/
theorem airyAiReal_ofReal (x : ℝ) : ((airyAiReal x : ℝ) : ℂ) = Complex.airyAi (x : ℂ) := by
  have h : star (Complex.airyAi (x : ℂ)) = Complex.airyAi (x : ℂ) := by
    have h' := Complex.airyAi_conj (x : ℂ)
    rw [show star (x : ℂ) = (x : ℂ) by simp] at h'
    exact h'.symm
  have him : (Complex.airyAi (x : ℂ)).im = 0 := by
    have h2 := congrArg Complex.im h
    have h3 : (star (Complex.airyAi (x : ℂ))).im = -(Complex.airyAi (x : ℂ)).im := by
      simp
    linarith
  unfold airyAiReal
  rw [Complex.ext_iff]
  constructor <;> simp [him]

/-- `Bi` is real-valued on the real axis: `↑(airyBiReal x) = airyBi ↑x`. -/
theorem airyBiReal_ofReal (x : ℝ) : ((airyBiReal x : ℝ) : ℂ) = Complex.airyBi (x : ℂ) := by
  have h : star (Complex.airyBi (x : ℂ)) = Complex.airyBi (x : ℂ) := by
    have h' := Complex.airyBi_conj (x : ℂ)
    rw [show star (x : ℂ) = (x : ℂ) by simp] at h'
    exact h'.symm
  have him : (Complex.airyBi (x : ℂ)).im = 0 := by
    have h2 := congrArg Complex.im h
    have h3 : (star (Complex.airyBi (x : ℂ))).im = -(Complex.airyBi (x : ℂ)).im := by
      simp
    linarith
  unfold airyBiReal
  rw [Complex.ext_iff]
  constructor <;> simp [him]

/-- Real differentiability of `airyAiReal`: the derivative is the real part of the complex
derivative. -/
theorem hasDerivAt_airyAiReal (x : ℝ) :
    HasDerivAt airyAiReal ((deriv Complex.airyAi (x : ℂ)).re) x := by
  show HasDerivAt (fun y : ℝ => (Complex.airyAi (y : ℂ)).re) _ _
  exact ((Complex.analyticAt_airyAi _).differentiableAt.hasDerivAt).real_of_complex

/-- Real differentiability of `airyBiReal`. -/
theorem hasDerivAt_airyBiReal (x : ℝ) :
    HasDerivAt airyBiReal ((deriv Complex.airyBi (x : ℂ)).re) x := by
  show HasDerivAt (fun y : ℝ => (Complex.airyBi (y : ℂ)).re) _ _
  exact ((Complex.analyticAt_airyBi _).differentiableAt.hasDerivAt).real_of_complex

/-- The derivative of `airyAiReal`, as a function. -/
theorem deriv_airyAiReal :
    deriv airyAiReal = fun x : ℝ => (deriv Complex.airyAi (x : ℂ)).re :=
  funext fun x => (hasDerivAt_airyAiReal x).deriv

/-- The derivative of `airyBiReal`, as a function. -/
theorem deriv_airyBiReal :
    deriv airyBiReal = fun x : ℝ => (deriv Complex.airyBi (x : ℂ)).re :=
  funext fun x => (hasDerivAt_airyBiReal x).deriv

/-- The derivative of `deriv airyAiReal` is the real part of the second complex
derivative. -/
theorem hasDerivAt_deriv_airyAiReal (x : ℝ) :
    HasDerivAt (deriv airyAiReal) ((deriv (deriv Complex.airyAi) (x : ℂ)).re) x := by
  rw [deriv_airyAiReal]
  exact (Complex.differentiableAt_deriv_airyAi _).hasDerivAt.real_of_complex

/-- The derivative of `deriv airyBiReal`. -/
theorem hasDerivAt_deriv_airyBiReal (x : ℝ) :
    HasDerivAt (deriv airyBiReal) ((deriv (deriv Complex.airyBi) (x : ℂ)).re) x := by
  rw [deriv_airyBiReal]
  exact (Complex.differentiableAt_deriv_airyBi _).hasDerivAt.real_of_complex

/-- The real Airy differential equation for `Ai`: `Ai'' = x · Ai` on `ℝ`. -/
theorem iteratedDeriv_two_airyAiReal (x : ℝ) :
    iteratedDeriv 2 airyAiReal x = x * airyAiReal x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    (hasDerivAt_deriv_airyAiReal x).deriv]
  have h := Complex.iteratedDeriv_two_airyAi (x : ℂ)
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
  rw [h, Complex.mul_re]
  simp [airyAiReal]

/-- The real Airy differential equation for `Bi`: `Bi'' = x · Bi` on `ℝ`. -/
theorem iteratedDeriv_two_airyBiReal (x : ℝ) :
    iteratedDeriv 2 airyBiReal x = x * airyBiReal x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    (hasDerivAt_deriv_airyBiReal x).deriv]
  have h := Complex.iteratedDeriv_two_airyBi (x : ℂ)
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
  rw [h, Complex.mul_re]
  simp [airyBiReal]

/-- The value `Ai'(0) = -3^(-4/3)/Γ(4/3)`, real version. -/
theorem deriv_airyAiReal_zero : deriv airyAiReal 0 = -(3 ^ (-4/3 : ℝ) / Real.Gamma (4/3)) := by
  have hval : (3 : ℂ)^(-4/3 : ℂ) / Complex.Gamma (4/3 : ℂ)
      = ((3 ^ (-4/3 : ℝ) / Real.Gamma (4/3) : ℝ) : ℂ) := by
    rw [show (-4/3 : ℂ) = ((-4/3 : ℝ) : ℂ) by norm_num, Complex.three_cpow_ofReal,
      show (4/3 : ℂ) = ((4/3 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal]
    push_cast
    ring
  rw [(hasDerivAt_airyAiReal 0).deriv, show ((0 : ℝ) : ℂ) = (0 : ℂ) by norm_cast,
    Complex.deriv_airyAi_zero, hval]
  simp

/-- The value `Bi'(0) = 3^(-5/6)/Γ(4/3)`, real version. -/
theorem deriv_airyBiReal_zero : deriv airyBiReal 0 = 3 ^ (-5/6 : ℝ) / Real.Gamma (4/3) := by
  have hval : (3 : ℂ)^(-5/6 : ℂ) / Complex.Gamma (4/3 : ℂ)
      = ((3 ^ (-5/6 : ℝ) / Real.Gamma (4/3) : ℝ) : ℂ) := by
    rw [show (-5/6 : ℂ) = ((-5/6 : ℝ) : ℂ) by norm_num, Complex.three_cpow_ofReal,
      show (4/3 : ℂ) = ((4/3 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal]
    push_cast
    ring
  rw [(hasDerivAt_airyBiReal 0).deriv, show ((0 : ℝ) : ℂ) = (0 : ℂ) by norm_cast,
    Complex.deriv_airyBi_zero, hval]
  simp

/-- The value `Ai(0) = 3^(-2/3)/Γ(2/3)`, real version. -/
theorem airyAiReal_zero : airyAiReal 0 = 3 ^ (-2/3 : ℝ) / Real.Gamma (2/3) := by
  have h1 : Complex.airyAi 0 = ((3 ^ (-2/3 : ℝ) / Real.Gamma (2/3) : ℝ) : ℂ) := by
    rw [Complex.airyAi_zero]
    rw [show (-2/3 : ℂ) = ((-2/3 : ℝ) : ℂ) by norm_num, Complex.three_cpow_ofReal,
      show (2/3 : ℂ) = ((2/3 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal]
    push_cast
    ring
  show (Complex.airyAi 0).re = 3 ^ (-2/3 : ℝ) / Real.Gamma (2/3)
  rw [h1, Complex.ofReal_re]

/-- The value `Bi(0) = 3^(-1/6)/Γ(2/3)`, real version. -/
theorem airyBiReal_zero : airyBiReal 0 = 3 ^ (-1/6 : ℝ) / Real.Gamma (2/3) := by
  have h1 : Complex.airyBi 0 = ((3 ^ (-1/6 : ℝ) / Real.Gamma (2/3) : ℝ) : ℂ) := by
    rw [Complex.airyBi_zero]
    rw [show (-1/6 : ℂ) = ((-1/6 : ℝ) : ℂ) by norm_num, Complex.three_cpow_ofReal,
      show (2/3 : ℂ) = ((2/3 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal]
    push_cast
    ring
  show (Complex.airyBi 0).re = 3 ^ (-1/6 : ℝ) / Real.Gamma (2/3)
  rw [h1, Complex.ofReal_re]

/-- `Γ(4/3) = Γ(1/3)/3` (real). -/
theorem Real.Gamma_four_thirds : Real.Gamma (4/3) = Real.Gamma (1/3) / 3 := by
  have h := Real.Gamma_add_one (by norm_num : (1/3 : ℝ) ≠ 0)
  rw [show (1/3 : ℝ) + 1 = 4/3 by norm_num] at h
  rw [h]
  ring

/-- `Ai(0) > 0`. -/
theorem airyAiReal_zero_pos : 0 < airyAiReal 0 := by
  rw [airyAiReal_zero]
  positivity

/-- `Ai'(0) < 0`. -/
theorem deriv_airyAiReal_zero_neg : deriv airyAiReal 0 < 0 := by
  rw [deriv_airyAiReal_zero]
  exact neg_lt_zero.mpr (by positivity)

/-- `Bi(0) > 0`. -/
theorem airyBiReal_zero_pos : 0 < airyBiReal 0 := by
  rw [airyBiReal_zero]
  positivity

/-- `Bi'(0) > 0`. -/
theorem deriv_airyBiReal_zero_pos : 0 < deriv airyBiReal 0 := by
  rw [deriv_airyBiReal_zero]
  positivity
