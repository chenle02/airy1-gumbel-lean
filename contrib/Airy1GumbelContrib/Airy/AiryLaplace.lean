/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryIdentity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory Set Filter
open scoped Topology

/-! # The Airy Laplace bound on the positive half-line

The Laplace bound `∫₀^∞ e^{2βu} Ai(u)² du ≤ C e^{(2/3) β³}` for `β ≥ 1`, following the
paper's proof: substitute `u = v²`, bound `Ai(v²)² ≤ C₂ (1+v²)^{-1/2} e^{-(4/3)v³}`
(two branches: `airyAiReal_le` for `v ≥ 1`, compactness of `[0,1]` for `v ≤ 1`), use the
weight `2v (1+v²)^{-1/2} ≤ 2`, and finish with the exact factorization
`2βv² - (4/3)v³ = (2/3)β³ - (2/3)(v-β)²(β+2v)` and the Gaussian integral.

## Main statement

* `airyAiReal_laplace_half`: `∃ C, ∀ β ≥ 1,
  ∫ u in Ioi 0, exp (2βu) * (airyAiReal u)^2 ≤ C * exp ((2/3) β³)`.

## See also

* `Airy/AiryLaplaceFull.lean`: the negative half (`|Ai|` bounded on `ℝ₋`)
  and the full Laplace bound on `ℝ` (`airyAiReal_laplace`). -/

/-- The exact algebraic identity `2βv² - (4/3)v³ = (2/3)β³ - (2/3)(v-β)²(β+2v)`
(pure `ring`; written in the `+ -` form to match `Real.exp_add` output). -/
private theorem airyLaplace_exp_identity (v β : ℝ) :
    2*β*v^2 + -(4/3)*v^3 = (2/3)*β^3 + -(2/3)*(v-β)^2*(β+2*v) := by ring

/-- The weight bound: for `0 ≤ v`, `2v (1+v²)^{-1/2} ≤ 2` (i.e. `v ≤ √(1+v²)`). -/
private theorem airyLaplace_weight_le {v : ℝ} (hv : 0 ≤ v) :
    2 * v * (Real.sqrt (1 + v^2))⁻¹ ≤ 2 := by
  have hs : v ≤ Real.sqrt (1 + v^2) := by
    calc v = Real.sqrt (v^2) := (Real.sqrt_sq hv).symm
      _ ≤ Real.sqrt (1 + v^2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg v])
  have hpos : 0 < Real.sqrt (1 + v^2) := Real.sqrt_pos_of_pos (by positivity)
  calc 2 * v * (Real.sqrt (1 + v^2))⁻¹
      ≤ 2 * Real.sqrt (1 + v^2) * (Real.sqrt (1 + v^2))⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) (by positivity)
    _ = 2 := by
        rw [show 2 * Real.sqrt (1 + v^2) * (Real.sqrt (1 + v^2))⁻¹
            = 2 * (Real.sqrt (1 + v^2) * (Real.sqrt (1 + v^2))⁻¹) from by ring,
          mul_inv_cancel₀ hpos.ne', mul_one]

/-- The squared Airy bound in the `v`-variable: some `0 ≤ C₂` with
`Ai(v²)² ≤ C₂ (1+v²)^{-1/2} e^{-(4/3) v³}` for all `0 ≤ v`. The large-`v` branch squares
`airyAiReal_le` (and `(v²)^{-1/4} = v^{-1/2}`, `(v²)^{3/2} = v³`,
`v^{-1} ≤ 2 (1+v²)^{-1/2}` for `v ≥ 1`); the small-`v` branch uses the maximum of the
continuous `Ai` on the compact interval `[0, 1]`. -/
private theorem airyAiReal_sq_le :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ v : ℝ, 0 ≤ v →
      (airyAiReal (v^2))^2 ≤ C₂ * (Real.sqrt (1 + v^2))⁻¹ * Real.exp (-(4/3)*v^3) := by
  obtain ⟨C₁, hC₁⟩ := airyAiReal_le
  have hcont : ContinuousOn airyAiReal (Set.Icc 0 1) := fun x _ =>
    (hasDerivAt_airyAiReal x).continuousAt.continuousWithinAt
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) hcont
  have hMnn : (0:ℝ) ≤ (airyAiReal x₀)^2 := sq_nonneg _
  refine ⟨2*C₁^2 + Real.sqrt 2 * Real.exp (4/3) * (airyAiReal x₀)^2,
    add_nonneg (mul_nonneg (by norm_num) (sq_nonneg C₁))
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.exp_pos _).le) hMnn), fun v hv => ?_⟩
  have hsq : 0 ≤ airyAiReal (v^2) := (airyAiReal_pos_of_nonneg (sq_nonneg v)).le
  by_cases hv1 : 1 ≤ v
  · -- branch `1 ≤ v`: square `airyAiReal_le`
    have hv0 : 0 < v := by linarith
    have hv2 : 1 ≤ v^2 := by nlinarith [hv1, sq_nonneg v]
    have e1 : (v^2)^(-1/4:ℝ) = v^(-1/2:ℝ) := by
      rw [← Real.rpow_natCast v 2, ← Real.rpow_mul hv0.le]
      norm_num
    have e2 : (v^2)^(3/2:ℝ) = v^3 := by
      rw [← Real.rpow_natCast v 2, ← Real.rpow_mul hv0.le]
      norm_num [Real.rpow_natCast]
    have h1 : airyAiReal (v^2) ≤ C₁ * v^(-1/2:ℝ) * Real.exp (-(2/3) * v^3) := by
      have hAi := hC₁ (v^2) hv2
      rwa [e1, e2, show -(2/3 * v^3) = -(2/3) * v^3 from by ring] at hAi
    have hsquare : (airyAiReal (v^2))^2
        ≤ C₁^2 * v^(-1:ℝ) * Real.exp (-(4/3) * v^3) := by
      have hsqle := pow_le_pow_left₀ hsq h1 2
      have h1e : (v^(-1/2:ℝ))^2 = v^(-1:ℝ) := by
        rw [← Real.rpow_natCast (v^(-1/2:ℝ)) 2, ← Real.rpow_mul hv0.le]
        norm_num
      have h2e : (Real.exp (-(2/3) * v^3))^2 = Real.exp (-(4/3) * v^3) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      calc (airyAiReal (v^2))^2 ≤ (C₁ * v^(-1/2:ℝ) * Real.exp (-(2/3) * v^3))^2 := hsqle
        _ = C₁^2 * (v^(-1/2:ℝ))^2 * (Real.exp (-(2/3) * v^3))^2 := by ring
        _ = C₁^2 * v^(-1:ℝ) * Real.exp (-(4/3) * v^3) := by rw [h1e, h2e]
    have hw : v^(-1:ℝ) ≤ 2 * (Real.sqrt (1 + v^2))⁻¹ := by
      have h2v : Real.sqrt (1 + v^2) ≤ 2 * v := by
        have hle : 1 + v^2 ≤ (2*v)^2 := by nlinarith [hv1, sq_nonneg v]
        calc Real.sqrt (1 + v^2) ≤ Real.sqrt ((2*v)^2) := Real.sqrt_le_sqrt hle
          _ = 2 * v := Real.sqrt_sq (by linarith)
      have hpos : (0:ℝ) < Real.sqrt (1 + v^2) := Real.sqrt_pos_of_pos (by positivity)
      calc v^(-1:ℝ) = v⁻¹ := Real.rpow_neg_one v
        _ = (Real.sqrt (1 + v^2))⁻¹ * (Real.sqrt (1 + v^2) * v⁻¹) := by
            rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
        _ ≤ (Real.sqrt (1 + v^2))⁻¹ * (2 * v * v⁻¹) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h2v (by positivity)) (by positivity)
        _ = 2 * (Real.sqrt (1 + v^2))⁻¹ := by
            rw [show (2:ℝ) * v * v⁻¹ = 2 * (v * v⁻¹) from by ring,
              mul_inv_cancel₀ hv0.ne', mul_one, mul_comm]
    calc (airyAiReal (v^2))^2 ≤ C₁^2 * v^(-1:ℝ) * Real.exp (-(4/3) * v^3) := hsquare
      _ ≤ (2*C₁^2) * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3) * v^3) := by
          have he : (2:ℝ)*C₁^2 * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3) * v^3)
              = C₁^2 * (2 * (Real.sqrt (1+v^2))⁻¹) * Real.exp (-(4/3) * v^3) := by ring
          rw [he]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hw (sq_nonneg C₁)) (Real.exp_pos _).le
      _ ≤ (2*C₁^2 + Real.sqrt 2 * Real.exp (4/3) * (airyAiReal x₀)^2)
            * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3) * v^3) := by
          apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.exp_pos _).le) hMnn)
  · -- branch `0 ≤ v ≤ 1`: the compact-interval maximum
    have hv1' : v ≤ 1 := le_of_not_ge hv1
    have hv2mem : v^2 ∈ Set.Icc (0:ℝ) 1 := ⟨sq_nonneg v, by nlinarith [hv, hv1']⟩
    have hM : airyAiReal (v^2) ≤ airyAiReal x₀ := hmax hv2mem
    have hsqM : (airyAiReal (v^2))^2 ≤ (airyAiReal x₀)^2 := pow_le_pow_left₀ hsq hM 2
    have hfac : 1 ≤ Real.sqrt 2 * Real.exp (4/3) * (Real.sqrt (1+v^2))⁻¹
        * Real.exp (-(4/3)*v^3) := by
      have h1 : (Real.sqrt 2)⁻¹ ≤ (Real.sqrt (1+v^2))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le (Real.sqrt_pos_of_pos (by positivity : (0:ℝ) < 1 + v^2))
          (Real.sqrt_le_sqrt (by nlinarith [hv1', sq_nonneg v]))
      have h2 : Real.exp (-(4/3)) ≤ Real.exp (-(4/3)*v^3) := by
        apply Real.exp_le_exp.2
        have hv3 : v^3 ≤ 1 := by
          calc v^3 = v * v^2 := by ring
            _ ≤ 1 * v^2 := mul_le_mul_of_nonneg_right hv1' (sq_nonneg v)
            _ = v^2 := one_mul _
            _ ≤ 1 := by nlinarith [hv, hv1']
        nlinarith [hv3]
      have hfac0 : (1:ℝ)
          = Real.sqrt 2 * Real.exp (4/3) * (Real.sqrt 2)⁻¹ * Real.exp (-(4/3)) := by
        have he : Real.sqrt 2 * Real.exp (4/3) * (Real.sqrt 2)⁻¹ * Real.exp (-(4/3))
            = (Real.sqrt 2 * (Real.sqrt 2)⁻¹) * (Real.exp (4/3) * Real.exp (-(4/3))) := by
          ring
        rw [he, mul_inv_cancel₀ (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2)).ne',
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      calc (1:ℝ) = Real.sqrt 2 * Real.exp (4/3) * (Real.sqrt 2)⁻¹ * Real.exp (-(4/3)) :=
          hfac0
        _ ≤ Real.sqrt 2 * Real.exp (4/3) * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3)*v^3) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
              (Real.exp_pos _).le (by positivity)
    calc (airyAiReal (v^2))^2 ≤ (airyAiReal x₀)^2 := hsqM
      _ ≤ (Real.sqrt 2 * Real.exp (4/3) * (airyAiReal x₀)^2)
            * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3)*v^3) := by
          calc (airyAiReal x₀)^2 = (airyAiReal x₀)^2 * 1 := by rw [mul_one]
            _ ≤ (airyAiReal x₀)^2
                  * (Real.sqrt 2 * Real.exp (4/3) * (Real.sqrt (1+v^2))⁻¹
                    * Real.exp (-(4/3)*v^3)) :=
                mul_le_mul_of_nonneg_left hfac hMnn
            _ = (Real.sqrt 2 * Real.exp (4/3) * (airyAiReal x₀)^2)
                  * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3)*v^3) := by ring
      _ ≤ (2*C₁^2 + Real.sqrt 2 * Real.exp (4/3) * (airyAiReal x₀)^2)
            * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3)*v^3) := by
          apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (sq_nonneg C₁))

/-- The substitution `u = v²` for the Laplace integral:
`∫₀^∞ e^{2βu} Ai(u)² du = ∫₀^∞ 2v e^{2βv²} Ai(v²)² dv`. -/
private theorem airyLaplace_sq_subst (β : ℝ) :
    ∫ u in Set.Ioi (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2
      = ∫ v in Set.Ioi (0:ℝ), 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2) := by
  set f : ℝ → ℝ := fun v => v^2 with hf
  have hf' : ∀ v ∈ Set.Ioi (0:ℝ), HasDerivWithinAt f (2*v) (Set.Ioi 0) v := by
    intro v _
    have h : HasDerivAt (fun x : ℝ => x^2) (2*v) v := by
      convert hasDerivAt_pow 2 v using 1
      norm_num [pow_one]
    exact h.hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioi 0) := by
    have hmono : StrictMonoOn f (Set.Ioi 0) := by
      intro a ha b hb hab
      exact pow_lt_pow_left₀ hab (le_of_lt ha) (by norm_num : (2:ℕ) ≠ 0)
    exact hmono.injOn
  have himg : f '' Set.Ioi 0 = Set.Ioi 0 := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact pow_pos hv 2
    · intro hu
      exact ⟨Real.sqrt u, Real.sqrt_pos_of_pos hu, Real.sq_sqrt (le_of_lt hu)⟩
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hf' hinj, himg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  have hv0 : (0:ℝ) < v := hv
  dsimp only [f]
  rw [abs_of_pos (by positivity : (0:ℝ) < 2*v), smul_eq_mul]

/-- **Airy Laplace bound, positive half**: for some constant `C`,
`∫₀^∞ e^{2βu} Ai(u)² du ≤ C e^{(2/3) β³}` for all `1 ≤ β`. -/
theorem airyAiReal_laplace_half : ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β →
    ∫ u in Set.Ioi (0:ℝ), Real.exp (2*β*u) * (airyAiReal u)^2
      ≤ C * Real.exp ((2/3)*β^3) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := airyAiReal_sq_le
  refine ⟨2 * C₂ * Real.sqrt (3 * Real.pi / 2), fun β hβ => ?_⟩
  have hβ0 : 0 < β := by linarith
  rw [airyLaplace_sq_subst β]
  have hgauss : Integrable (fun v : ℝ => Real.exp (-(2/3) * (v-β)^2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 2/3)).comp_sub_right β
  have h3 : ∀ v : ℝ, 0 ≤ v →
      Real.exp (-(2/3)*(v-β)^2*(β+2*v)) ≤ Real.exp (-(2/3)*(v-β)^2) := by
    intro v hv
    apply Real.exp_le_exp.2
    have hX : (0:ℝ) ≤ (2/3)*(v-β)^2 := by positivity
    have h1 : (1:ℝ) ≤ β + 2*v := by linarith
    have hle : (2/3)*(v-β)^2 ≤ (2/3)*(v-β)^2*(β+2*v) := by
      calc (2/3)*(v-β)^2 = (2/3)*(v-β)^2 * 1 := by rw [mul_one]
        _ ≤ (2/3)*(v-β)^2*(β+2*v) := mul_le_mul_of_nonneg_left h1 hX
    linarith
  have h2 : ∀ v : ℝ, 0 ≤ v → 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2)
      ≤ 2*C₂ * Real.exp ((2/3)*β^3) * Real.exp (-(2/3)*(v-β)^2*(β+2*v)) := by
    intro v hv
    calc 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2)
        ≤ 2*v * (Real.exp (2*β*v^2)
            * (C₂ * (Real.sqrt (1+v^2))⁻¹ * Real.exp (-(4/3)*v^3))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hC₂ v hv) (Real.exp_pos _).le) (by linarith)
      _ = C₂ * (2*v*(Real.sqrt (1+v^2))⁻¹)
            * (Real.exp (2*β*v^2) * Real.exp (-(4/3)*v^3)) := by ring
      _ ≤ C₂ * 2 * (Real.exp (2*β*v^2) * Real.exp (-(4/3)*v^3)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (airyLaplace_weight_le hv) hC₂0) (by positivity)
      _ = 2*C₂ * Real.exp (2*β*v^2 + -(4/3)*v^3) := by
          rw [← Real.exp_add]; ring
      _ = 2*C₂ * (Real.exp ((2/3)*β^3) * Real.exp (-(2/3)*(v-β)^2*(β+2*v))) := by
          rw [← Real.exp_add, airyLaplace_exp_identity v β]
      _ = 2*C₂ * Real.exp ((2/3)*β^3) * Real.exp (-(2/3)*(v-β)^2*(β+2*v)) := by ring
  have hdom2 : IntegrableOn (fun v => 2*C₂ * Real.exp ((2/3)*β^3)
      * Real.exp (-(2/3)*(v-β)^2*(β+2*v))) (Set.Ioi 0) := by
    apply Integrable.mono' ((hgauss.integrableOn).const_mul (2*C₂ * Real.exp ((2/3)*β^3)))
      ?_ ?_
    · exact ((by fun_prop : Continuous fun v : ℝ =>
        Real.exp (-(2/3)*(v-β)^2*(β+2*v))).const_mul _).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun v hv => ?_
      have hnn : (0:ℝ) ≤ 2*C₂ * Real.exp ((2/3)*β^3)
          * Real.exp (-(2/3)*(v-β)^2*(β+2*v)) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (h3 v (le_of_lt hv))
        (mul_nonneg (mul_nonneg (by norm_num) hC₂0) (Real.exp_pos _).le)
  have hint1 : IntegrableOn (fun v => 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2))
      (Set.Ioi 0) := by
    apply Integrable.mono' hdom2 ?_ ?_
    · have hAi0 : Continuous airyAiReal :=
        continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAiReal x).continuousAt
      have hAi : Continuous fun v : ℝ => airyAiReal (v^2) := hAi0.comp (continuous_pow 2)
      have hcont : Continuous fun v : ℝ =>
          2*v * Real.exp (2*β*v^2) * (airyAiReal (v^2))^2 :=
        ((by fun_prop : Continuous fun v : ℝ => 2*v * Real.exp (2*β*v^2))).mul (hAi.pow 2)
      have heq : (fun v : ℝ => 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2))
          = fun v => 2*v * Real.exp (2*β*v^2) * (airyAiReal (v^2))^2 :=
        funext fun v => by ring
      rw [heq]
      exact hcont.aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun v hv => ?_
      have hv0 : (0:ℝ) < v := hv
      have hnn : (0:ℝ) ≤ 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2) :=
        mul_nonneg (by linarith [hv0]) (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact h2 v (le_of_lt hv)
  calc ∫ v in Set.Ioi 0, 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2)
      ≤ ∫ v in Set.Ioi 0, 2*C₂ * Real.exp ((2/3)*β^3) * Real.exp (-(2/3)*(v-β)^2) := by
        apply setIntegral_mono_on hint1 ((hgauss.integrableOn).const_mul _)
          measurableSet_Ioi
        intro v hv
        calc 2*v * (Real.exp (2*β*v^2) * (airyAiReal (v^2))^2)
            ≤ 2*C₂ * Real.exp ((2/3)*β^3) * Real.exp (-(2/3)*(v-β)^2*(β+2*v)) :=
              h2 v (le_of_lt hv)
          _ ≤ 2*C₂ * Real.exp ((2/3)*β^3) * Real.exp (-(2/3)*(v-β)^2) :=
              mul_le_mul_of_nonneg_left (h3 v (le_of_lt hv))
                (mul_nonneg (mul_nonneg (by norm_num) hC₂0) (Real.exp_pos _).le)
      _ = 2*C₂ * Real.exp ((2/3)*β^3) * ∫ v in Set.Ioi 0, Real.exp (-(2/3)*(v-β)^2) := by
          rw [integral_const_mul]
      _ ≤ 2*C₂ * Real.exp ((2/3)*β^3) * ∫ v : ℝ, Real.exp (-(2/3)*(v-β)^2) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          apply setIntegral_le_integral hgauss
          exact Filter.Eventually.of_forall fun v => (Real.exp_pos _).le
      _ = 2*C₂ * Real.exp ((2/3)*β^3) * ∫ x : ℝ, Real.exp (-(2/3)*x^2) := by
          congr 1
          exact integral_sub_right_eq_self (fun x : ℝ => Real.exp (-(2/3) * x^2)) β
      _ = 2*C₂ * Real.exp ((2/3)*β^3) * Real.sqrt (3*Real.pi/2) := by
          congr 1
          have hval : (∫ x : ℝ, Real.exp (-(2/3) * x^2)) = Real.sqrt (3*Real.pi/2) := by
            have h := integral_gaussian (2/3)
            rwa [show (Real.pi / (2/3)) = 3*Real.pi/2 by ring] at h
          exact hval
      _ = (2 * C₂ * Real.sqrt (3*Real.pi/2)) * Real.exp ((2/3)*β^3) := by ring
