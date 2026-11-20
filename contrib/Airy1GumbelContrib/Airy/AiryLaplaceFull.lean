/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryLaplace

open MeasureTheory Set Filter
open scoped Topology

/-! # Boundedness of `Ai` on `ℝ₋` and the full Airy–Laplace bound

Boundedness of `Ai` on `ℝ₋` by energy monotonicity, and the full Laplace bound on `ℝ`
by combining the negative half (the exponential weight is integrable against the uniform
bound) with the positive half `airyAiReal_laplace_half`.

## Main statements

* `airyAiReal_abs_le_nonpos`: `∃ C, ∀ u ≤ 0, |airyAiReal u| ≤ C`.
  For `u ≤ -1` the energy `F u = Ai(u)² + Ai'(u)²/(−u)` has derivative `Ai'(u)²/u² ≥ 0`
  (the ODE `Ai'' = u·Ai` kills the cross term), so `(Ai u)² ≤ F u ≤ F (-1)`; on
  `[-1, 0]` the continuous `|Ai|` attains a maximum.
* `airyAiReal_laplace` (the paper's Airy–Laplace bound on all of `ℝ`): `∃ C, ∀ β ≥ 1,
  ∫ u : ℝ, Real.exp (2*β*u) * (airyAiReal u)^2 ≤ C * Real.exp ((2/3)*β^3)`.
  The integral splits at `0` (`Set.Iic_union_Ioi`); the negative half is bounded by
  `C₀² ∫_{(-∞,0]} e^{2βu} du = C₀²/(2β) ≤ (C₀²/2) e^{(2/3)β³}`, the positive half is
  `airyAiReal_laplace_half`, and the witness is `Cp + C₀²/2`. -/

/-- The energy `F u = Ai(u)^2 + Ai'(u)^2 / (-u)`, whose derivative is `Ai'(u)^2 / u^2`. -/
private noncomputable def airyEnergy (u : ℝ) : ℝ :=
  (airyAiReal u)^2 + (deriv airyAiReal u)^2 * (-u)⁻¹

/-- For `u < 0`, `F'(u) = (Ai'(u))^2 / u^2`: the quotient-rule term `2 Ai' Ai'' (-u)`
uses the ODE `Ai'' = u·Ai` and cancels `d/du [Ai^2] = 2 Ai Ai'`. -/
private theorem hasDerivAt_airyEnergy (u : ℝ) (hu : u < 0) :
    HasDerivAt airyEnergy ((deriv airyAiReal u)^2 / u^2) u := by
  have hu0 : u ≠ 0 := hu.ne
  have hu0' : (-u) ≠ 0 := neg_ne_zero.mpr hu0
  have hODE : deriv (deriv airyAiReal) u = u * airyAiReal u := by
    have h := iteratedDeriv_two_airyAiReal u
    rwa [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
  have hA : HasDerivAt airyAiReal (deriv airyAiReal u) u := by
    rw [deriv_airyAiReal]
    exact hasDerivAt_airyAiReal u
  have hB : HasDerivAt (deriv airyAiReal) (u * airyAiReal u) u := by
    have h := hasDerivAt_deriv_airyAiReal u
    have hval : (deriv (deriv Complex.airyAi) (u : ℂ)).re = u * airyAiReal u :=
      ((hasDerivAt_deriv_airyAiReal u).deriv).symm.trans hODE
    rwa [hval] at h
  have h1 : HasDerivAt (fun u : ℝ => (airyAiReal u)^2)
      (2 * airyAiReal u * deriv airyAiReal u) u := by
    have h := hA.fun_mul hA
    have e1 : (fun u : ℝ => (airyAiReal u)^2) = fun u => airyAiReal u * airyAiReal u :=
      funext fun u => pow_two _
    have e2 : 2 * airyAiReal u * deriv airyAiReal u
        = deriv airyAiReal u * airyAiReal u + airyAiReal u * deriv airyAiReal u := by
      ring
    rwa [e1, e2]
  have hg : HasDerivAt (fun u : ℝ => (deriv airyAiReal u)^2)
      (2 * u * airyAiReal u * deriv airyAiReal u) u := by
    have h := hB.fun_mul hB
    have e1 : (fun u : ℝ => (deriv airyAiReal u)^2)
        = fun u => deriv airyAiReal u * deriv airyAiReal u :=
      funext fun u => pow_two _
    have e2 : 2 * u * airyAiReal u * deriv airyAiReal u
        = (u * airyAiReal u) * deriv airyAiReal u
          + deriv airyAiReal u * (u * airyAiReal u) := by
      ring
    rwa [e1, e2]
  have hinv : HasDerivAt (fun u : ℝ => (-u)⁻¹) (1 / u^2) u := by
    have hn : HasDerivAt (fun x : ℝ => -x) (-1) u := hasDerivAt_neg' u
    have h := hn.fun_inv hu0'
    have e2 : (1:ℝ) / u^2 = -(-1) / (-u)^2 := by rw [neg_neg, neg_sq]
    rwa [e2]
  have h2 : HasDerivAt (fun u : ℝ => (deriv airyAiReal u)^2 * (-u)⁻¹)
      ((deriv airyAiReal u)^2 / u^2 - 2 * airyAiReal u * deriv airyAiReal u) u := by
    have h := hg.fun_mul hinv
    have e2 : (deriv airyAiReal u)^2 / u^2 - 2 * airyAiReal u * deriv airyAiReal u
        = (2 * u * airyAiReal u * deriv airyAiReal u) * (-u)⁻¹
          + (deriv airyAiReal u)^2 * (1 / u^2) := by
      field_simp
      ring
    rwa [e2]
  have h := h1.fun_add h2
  have e2 : (deriv airyAiReal u)^2 / u^2
      = 2 * airyAiReal u * deriv airyAiReal u
        + ((deriv airyAiReal u)^2 / u^2 - 2 * airyAiReal u * deriv airyAiReal u) := by
    ring
  rwa [e2]

/-- The energy is monotone on `(-∞, -1]`: it is continuous there, differentiable on the
interior `(-∞, -1)`, and its derivative `(Ai')^2 / u^2` is nonnegative. -/
private theorem airyEnergy_monotoneOn : MonotoneOn airyEnergy (Set.Iic (-1)) := by
  have hAic : Continuous airyAiReal :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiReal x).continuousAt
  have hAic' : Continuous (deriv airyAiReal) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_deriv_airyAiReal x).continuousAt
  have hFcont : ContinuousOn airyEnergy (Set.Iic (-1)) := by
    have h1c : ContinuousOn (fun u : ℝ => (airyAiReal u)^2) (Set.Iic (-1)) :=
      (hAic.pow 2).continuousOn
    have h2c : ContinuousOn (fun u : ℝ => (deriv airyAiReal u)^2 * (-u)⁻¹)
        (Set.Iic (-1)) := by
      apply ContinuousOn.mul (hAic'.pow 2).continuousOn
      apply ContinuousOn.inv₀ (continuous_id.neg).continuousOn
      intro x hx
      exact neg_ne_zero.mpr (ne_of_lt (lt_of_le_of_lt (mem_Iic.mp hx) (by norm_num)))
    exact h1c.add h2c
  have hdifF : DifferentiableOn ℝ airyEnergy (interior (Set.Iic (-1))) := by
    rw [interior_Iic]
    intro x hx
    exact (hasDerivAt_airyEnergy x
      (lt_trans (mem_Iio.mp hx) (by norm_num : (-1:ℝ) < 0))).differentiableAt
      |>.differentiableWithinAt
  have hderF : ∀ x ∈ interior (Set.Iic (-1)), 0 ≤ deriv airyEnergy x := by
    rw [interior_Iic]
    intro x hx
    have hx0 : x < 0 := lt_trans (mem_Iio.mp hx) (by norm_num : (-1:ℝ) < 0)
    rw [(hasDerivAt_airyEnergy x hx0).deriv]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  exact monotoneOn_of_deriv_nonneg (convex_Iic (-1)) hFcont hdifF hderF

/-- **Negative-half Airy bound**: `Ai` is uniformly bounded on `(-∞, 0]`.
For `u ≤ -1`, `(Ai u)^2 ≤ F u ≤ F (-1)` by energy monotonicity; on `[-1, 0]` the
continuous `|Ai|` attains a maximum. -/
theorem airyAiReal_abs_le_nonpos : ∃ C : ℝ, ∀ u : ℝ, u ≤ 0 → |airyAiReal u| ≤ C := by
  have hAic : Continuous airyAiReal :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiReal x).continuousAt
  have hEn : ∀ u : ℝ, u ≤ -1 → |airyAiReal u| ≤ Real.sqrt (airyEnergy (-1)) := by
    intro u hu
    have hu0 : u ≤ 0 := by linarith
    have hnn : 0 ≤ (deriv airyAiReal u)^2 * (-u)⁻¹ :=
      mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (neg_nonneg.mpr hu0))
    have hsle : (airyAiReal u)^2 ≤ airyEnergy u := le_add_of_nonneg_right hnn
    have hmono : airyEnergy u ≤ airyEnergy (-1) :=
      airyEnergy_monotoneOn (mem_Iic.mpr hu) (mem_Iic.mpr le_rfl) hu
    calc |airyAiReal u| = Real.sqrt ((airyAiReal u)^2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (airyEnergy u) := Real.sqrt_le_sqrt hsle
      _ ≤ Real.sqrt (airyEnergy (-1)) := Real.sqrt_le_sqrt hmono
  have hcontabs : ContinuousOn (fun u => |airyAiReal u|) (Set.Icc (-1) 0) :=
    hAic.abs.continuousOn
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (-1:ℝ) ≤ 0)) hcontabs
  refine ⟨Real.sqrt (airyEnergy (-1)) + |airyAiReal x₀|, fun u hu => ?_⟩
  by_cases hu1 : u ≤ -1
  · exact (hEn u hu1).trans (le_add_of_nonneg_right (abs_nonneg _))
  · have humem : u ∈ Set.Icc (-1) 0 := ⟨le_of_not_ge hu1, hu⟩
    exact (hmax humem).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))

/-- **Full Airy–Laplace bound** (the paper's Airy–Laplace lemma): for some `C`, all `1 ≤ β`,
`∫_ℝ e^{2βu} Ai(u)^2 du ≤ C e^{(2/3) β³}`. The integral splits at `0`; the negative half
is bounded by `C₀^2 ∫_{(-∞,0]} e^{2βu} du = C₀^2 / (2β) ≤ (C₀^2/2) e^{(2/3)β³}`, and the
positive half is `airyAiReal_laplace_half`. -/
theorem airyAiReal_laplace : ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β →
    ∫ u : ℝ, Real.exp (2*β*u) * (airyAiReal u)^2 ≤ C * Real.exp ((2/3)*β^3) := by
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le_nonpos
  obtain ⟨C₁, hC₁⟩ := airyAiReal_le
  obtain ⟨Cp, hCp⟩ := airyAiReal_laplace_half
  have hAic : Continuous airyAiReal :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiReal x).continuousAt
  refine ⟨Cp + C₀^2 / 2, fun β hβ => ?_⟩
  have hβ0 : 0 < β := by linarith
  have hgexp : Continuous fun u : ℝ => Real.exp (2*β*u) := by fun_prop
  have hgcont : Continuous (fun u : ℝ => Real.exp (2*β*u) * (airyAiReal u)^2) :=
    hgexp.mul (hAic.pow 2)
  -- negative half: pointwise domination by `C₀^2 e^{2βu}`
  have hbound : ∀ u : ℝ, u ≤ 0 →
      Real.exp (2*β*u) * (airyAiReal u)^2 ≤ C₀^2 * Real.exp (2*β*u) := by
    intro u hu
    have hsq : (airyAiReal u)^2 ≤ C₀^2 := by
      rw [← sq_abs (airyAiReal u)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC₀ u hu) 2
    calc Real.exp (2*β*u) * (airyAiReal u)^2
        ≤ Real.exp (2*β*u) * C₀^2 :=
          mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = C₀^2 * Real.exp (2*β*u) := by ring
  have hgIic : IntegrableOn (fun u : ℝ => Real.exp (2*β*u) * (airyAiReal u)^2)
      (Set.Iic 0) volume := by
    apply Integrable.mono'
      ((integrableOn_exp_mul_Iic (show (0:ℝ) < 2*β by positivity) 0).const_mul (C₀^2))
      hgcont.aestronglyMeasurable
    refine ae_restrict_of_forall_mem measurableSet_Iic fun u hu => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact hbound u (mem_Iic.mp hu)
  -- positive tail `u > 9β²`: domination by `C₁^2 e^{-(2/3)u}` via `airyAiReal_le`
  have htail : ∀ u : ℝ, u ∈ Set.Ioi (9*β^2) →
      Real.exp (2*β*u) * (airyAiReal u)^2 ≤ C₁^2 * Real.exp (-(2/3)*u) := by
    intro u hu
    have hu9 : 9*β^2 < u := mem_Ioi.mp hu
    have hβ2 : 1 ≤ β^2 := by nlinarith [hβ]
    have hu1 : 1 ≤ u := by nlinarith [hu9, hβ2]
    have hu0 : 0 < u := by linarith [hu1]
    have hsq : (airyAiReal u)^2
        ≤ (C₁ * u^(-1/4:ℝ) * Real.exp (-(2/3 * u^(3/2:ℝ))))^2 :=
      pow_le_pow_left₀ (airyAiReal_pos_of_nonneg hu0.le).le (hC₁ u hu1) 2
    have h1e : (u^(-1/4:ℝ))^2 = u^(-1/2:ℝ) := by
      rw [← Real.rpow_natCast (u^(-1/4:ℝ)) 2, ← Real.rpow_mul hu0.le]
      norm_num
    have h2e : (Real.exp (-(2/3 * u^(3/2:ℝ))))^2
        = Real.exp (-(4/3) * u^(3/2:ℝ)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hsq2 : (airyAiReal u)^2
        ≤ C₁^2 * u^(-1/2:ℝ) * Real.exp (-(4/3) * u^(3/2:ℝ)) := by
      calc (airyAiReal u)^2
          ≤ (C₁ * u^(-1/4:ℝ) * Real.exp (-(2/3 * u^(3/2:ℝ))))^2 := hsq
        _ = C₁^2 * (u^(-1/4:ℝ))^2 * (Real.exp (-(2/3 * u^(3/2:ℝ))))^2 := by ring
        _ = C₁^2 * u^(-1/2:ℝ) * Real.exp (-(4/3) * u^(3/2:ℝ)) := by rw [h1e, h2e]
    have hsqrt : ((3*β)^2)^(1/2:ℝ) = 3*β := by
      rw [← Real.rpow_natCast (3*β) 2, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 3*β),
        show ((2:ℕ):ℝ) * (1/2) = 1 by norm_num, Real.rpow_one]
    have hU : (3*β)^2 ≤ u := by nlinarith [hu9]
    have h12 : 3*β ≤ u^(1/2:ℝ) := by
      rw [← hsqrt]
      exact Real.rpow_le_rpow (sq_nonneg _) hU (by norm_num : (0:ℝ) ≤ 1/2)
    have hr32 : u^(3/2:ℝ) = u * u^(1/2:ℝ) := by
      rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hu0, Real.rpow_one]
    have h32 : 3*β*u ≤ u^(3/2:ℝ) := by
      have h' := mul_le_mul_of_nonneg_left h12 hu0.le
      rw [hr32]
      linarith [h']
    have h1le : u ≤ 3*β*u := by
      have h' := mul_le_mul_of_nonneg_right hβ hu0.le
      nlinarith [h']
    have hfin : 2*β*u + -(4/3)*u^(3/2:ℝ) ≤ -(2/3)*u := by nlinarith [h32, h1le]
    calc Real.exp (2*β*u) * (airyAiReal u)^2
        ≤ Real.exp (2*β*u) * (C₁^2 * u^(-1/2:ℝ) * Real.exp (-(4/3) * u^(3/2:ℝ))) :=
          mul_le_mul_of_nonneg_left hsq2 (Real.exp_pos _).le
      _ ≤ Real.exp (2*β*u) * (C₁^2 * 1 * Real.exp (-(4/3) * u^(3/2:ℝ))) := by
          apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num : (-1/2 : ℝ) ≤ 0))
            (sq_nonneg C₁)
      _ = C₁^2 * (Real.exp (2*β*u) * Real.exp (-(4/3) * u^(3/2:ℝ))) := by ring
      _ = C₁^2 * Real.exp (2*β*u + -(4/3) * u^(3/2:ℝ)) := by rw [← Real.exp_add]
      _ ≤ C₁^2 * Real.exp (-(2/3)*u) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hfin) (sq_nonneg C₁)
  have hgIoiU : IntegrableOn (fun u : ℝ => Real.exp (2*β*u) * (airyAiReal u)^2)
      (Set.Ioi (9*β^2)) volume := by
    apply Integrable.mono'
      ((integrableOn_exp_mul_Ioi (show (-(2/3):ℝ) < 0 by norm_num) (9*β^2)).const_mul
        (C₁^2))
      hgcont.aestronglyMeasurable
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact htail u hu
  have hgIoc : IntegrableOn (fun u : ℝ => Real.exp (2*β*u) * (airyAiReal u)^2)
      (Set.Ioc 0 (9*β^2)) volume :=
    hgcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hgIoi : IntegrableOn (fun u : ℝ => Real.exp (2*β*u) * (airyAiReal u)^2)
      (Set.Ioi 0) volume := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0:ℝ) ≤ 9*β^2 by positivity)]
    exact hgIoc.union hgIoiU
  -- split `∫_ℝ` at `0`
  have hsplit : ∫ u : ℝ, Real.exp (2*β*u) * (airyAiReal u)^2
      = (∫ u in Set.Iic (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2)
        + (∫ u in Set.Ioi (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2) := by
    rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := (0:ℝ)),
      setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hgIic hgIoi]
  -- negative-half estimate
  have h1 : ∫ u in Set.Iic (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2
      ≤ ∫ u in Set.Iic (0:ℝ), C₀^2 * Real.exp (2*β*u) :=
    setIntegral_mono_on hgIic
      ((integrableOn_exp_mul_Iic (show (0:ℝ) < 2*β by positivity) 0).const_mul (C₀^2))
      measurableSet_Iic fun u hu => hbound u (mem_Iic.mp hu)
  have hexp0 : ∫ u in Set.Iic (0:ℝ), Real.exp (2*β*u) = 1 / (2*β) := by
    have h := integral_exp_mul_Iic (show (0:ℝ) < 2*β by positivity) 0
    rwa [mul_zero, Real.exp_zero] at h
  have h2 : ∫ u in Set.Iic (0:ℝ), C₀^2 * Real.exp (2*β*u) = C₀^2 / (2*β) := by
    rw [integral_const_mul, hexp0]
    ring
  have h3 : C₀^2 / (2*β) ≤ C₀^2 / 2 :=
    div_le_div_of_nonneg_left (sq_nonneg C₀) (by norm_num : (0:ℝ) < 2)
      (by linarith : (2:ℝ) ≤ 2*β)
  have h4 : C₀^2 / 2 ≤ (C₀^2 / 2) * Real.exp ((2/3)*β^3) :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
  have hneg : ∫ u in Set.Iic (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2
      ≤ (C₀^2 / 2) * Real.exp ((2/3)*β^3) :=
    calc ∫ u in Set.Iic (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2
        ≤ ∫ u in Set.Iic (0:ℝ), C₀^2 * Real.exp (2*β*u) := h1
      _ = C₀^2 / (2*β) := h2
      _ ≤ C₀^2 / 2 := h3
      _ ≤ (C₀^2 / 2) * Real.exp ((2/3)*β^3) := h4
  calc ∫ u : ℝ, Real.exp (2*β*u) * (airyAiReal u)^2
      = (∫ u in Set.Iic (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2)
        + (∫ u in Set.Ioi (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2) := hsplit
    _ ≤ (C₀^2 / 2) * Real.exp ((2/3)*β^3) + Cp * Real.exp ((2/3)*β^3) :=
        add_le_add hneg (hCp β hβ)
    _ = (Cp + C₀^2 / 2) * Real.exp ((2/3)*β^3) := by ring
