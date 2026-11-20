/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoInterval.TwoIntervalOps

/-!
# Gaussian tools for the `n`-time fdd kernel

One-dimensional Gaussian/exponential calculus and plane-integrability criteria used by the
`L²` bound on the fdd `V` kernel (`Fdd/FddVBound.lean`):

* closed forms: `∫ e^{βv} p_t(u − v) dv = e^{βu + tβ²}` and the Chernoff closed form
  `∫ p_g(u − w) e^{θ(w − c)} p_τ(w − v) dw = e^{θ(u − c) + gθ²} p_{g+τ}(u − v + 2gθ)`
  (completed square + Chapman–Kolmogorov);
* the polynomial weight `1 + v² ≤ (1 + 2/δ²)(e^{δv} + e^{−δv})`;
* plane integrability of three dominator families: the half-planes `{u > m}`, `{v > m}`
  (`1_{·>m} e^{αu + βv} p_t(u − v)`, `α + β < 0`, by Tonelli) and the quadrant
  (`1_{u≤m} e^{αu} 1_{v≤m} e^{βv}`, `α, β > 0`);
* `memLp_of_sq_le`: `L²` from an integrable pointwise bound on the square.
-/

namespace AiryFdd

open MeasureTheory Real Set Filter

/-- `v ↦ e^{βv} p_t(u - v)` is integrable. -/
theorem integrable_exp_mul_heatKernel {t : ℝ} (ht : 0 < t) (β u : ℝ) :
    Integrable fun v : ℝ => Real.exp (β * v) * heatKernel t (u - v) := by
  have heq : (fun v : ℝ => Real.exp (β * v) * heatKernel t (u - v))
      = fun v => Real.exp (β * u) * AiryConj.conjugateHeatKernel t β (u - v) := by
    funext v
    rw [AiryConj.conjugateHeatKernel, show β * v = β * u + (-β) * (u - v) by ring, Real.exp_add]
    ring
  rw [heq]
  exact ((AiryConj.integrable_conjugateHeatKernel ht β).comp_sub_left u).const_mul _

/-- `∫ e^{βv} p_t(u - v) dv = e^{βu + tβ²}`. -/
theorem integral_exp_mul_heatKernel {t : ℝ} (ht : 0 < t) (β u : ℝ) :
    ∫ v : ℝ, Real.exp (β * v) * heatKernel t (u - v) = Real.exp (β * u + t * β ^ 2) := by
  rw [← AiryTwoInt.integral_heatKernel_mul_exp ht β u]
  exact integral_congr_ae (Eventually.of_forall fun v => mul_comm _ _)

/-- The polynomial weight is dominated by two exponentials of arbitrary small rate:
`1 + v² ≤ (1 + 2/δ²)(e^{δv} + e^{-δv})`. -/
theorem one_add_sq_le_exp {δ : ℝ} (hδ : 0 < δ) (v : ℝ) :
    1 + v ^ 2 ≤ (1 + 2 / δ ^ 2) * (Real.exp (δ * v) + Real.exp (-(δ * v))) := by
  have h0 : 0 ≤ δ * |v| := mul_nonneg hδ.le (abs_nonneg v)
  have h1 : 1 + δ * |v| + (δ * |v|) ^ 2 / 2 ≤ Real.exp (δ * |v|) :=
    Real.quadratic_le_exp_of_nonneg h0
  have h2 : Real.exp (δ * |v|) ≤ Real.exp (δ * v) + Real.exp (-(δ * v)) :=
    AiryTwoInt.exp_mul_abs_le δ v
  have hsq : (δ * |v|) ^ 2 = δ ^ 2 * v ^ 2 := by rw [mul_pow, sq_abs]
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h3 : 1 + v ^ 2 ≤ (1 + 2 / δ ^ 2) * (1 + δ ^ 2 * v ^ 2 / 2) := by
    have e : (1 + 2 / δ ^ 2) * (1 + δ ^ 2 * v ^ 2 / 2)
        = 1 + v ^ 2 + 2 / δ ^ 2 + δ ^ 2 * v ^ 2 / 2 := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ 2 / δ ^ 2 := by positivity
    have : 0 ≤ δ ^ 2 * v ^ 2 / 2 := by positivity
    linarith
  have h4 : 1 + δ ^ 2 * v ^ 2 / 2 ≤ Real.exp (δ * v) + Real.exp (-(δ * v)) := by
    rw [← hsq]; linarith
  calc 1 + v ^ 2 ≤ (1 + 2 / δ ^ 2) * (1 + δ ^ 2 * v ^ 2 / 2) := h3
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

/-- **Half-plane integrability** `{u > m}`: for `α + β < 0`,
`1_{u > m} e^{αu} e^{βv} p_t(u - v)` is integrable on the plane (Tonelli, inner integral in
closed form). -/
theorem integrable_halfplane_fst {t : ℝ} (ht : 0 < t) (m α β : ℝ) (hαβ : α + β < 0) :
    Integrable (fun p : ℝ × ℝ => (Ioi m).indicator (fun u => Real.exp (α * u)) p.1
      * (Real.exp (β * p.2) * heatKernel t (p.1 - p.2))) (volume.prod volume) := by
  have hind : Measurable ((Ioi m).indicator (fun u : ℝ => Real.exp (α * u))) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.indicator
      measurableSet_Ioi
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Ioi m).indicator (fun u => Real.exp (α * u)) p.1
        * (Real.exp (β * p.2) * heatKernel t (p.1 - p.2))) (volume.prod volume) :=
    ((hind.comp measurable_fst).mul ((Real.continuous_exp.comp
      (continuous_const.mul continuous_snd)).mul ((continuous_heatKernel t).comp
        (continuous_fst.sub continuous_snd))).measurable).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · exact Eventually.of_forall fun u =>
      (integrable_exp_mul_heatKernel ht β u).const_mul
        ((Ioi m).indicator (fun u => Real.exp (α * u)) u)
  · have hval : ∀ u : ℝ, (∫ v : ℝ, ‖(Ioi m).indicator (fun u => Real.exp (α * u)) u
        * (Real.exp (β * v) * heatKernel t (u - v))‖)
        = (Ioi m).indicator (fun u => Real.exp (t * β ^ 2) * Real.exp (-(-(α + β)) * u)) u := by
      intro u
      have hI : 0 ≤ (Ioi m).indicator (fun u => Real.exp (α * u)) u :=
        Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) u
      have hnn : ∀ v : ℝ, 0 ≤ (Ioi m).indicator (fun u => Real.exp (α * u)) u
          * (Real.exp (β * v) * heatKernel t (u - v)) := fun v =>
        mul_nonneg hI (mul_nonneg (Real.exp_pos _).le (heatKernel_pos ht _).le)
      rw [integral_congr_ae (Eventually.of_forall fun v =>
        (by rw [Real.norm_eq_abs, abs_of_nonneg (hnn v)] :
          ‖(Ioi m).indicator (fun u => Real.exp (α * u)) u
            * (Real.exp (β * v) * heatKernel t (u - v))‖
          = (Ioi m).indicator (fun u => Real.exp (α * u)) u
            * (Real.exp (β * v) * heatKernel t (u - v))))]
      rw [integral_const_mul, integral_exp_mul_heatKernel ht β u]
      by_cases hu : u ∈ Ioi m
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
    have hint : Integrable ((Ioi m).indicator
        (fun u => Real.exp (t * β ^ 2) * Real.exp (-(-(α + β)) * u))) :=
      (integrable_indicator_iff measurableSet_Ioi).2
        ((exp_neg_integrableOn_Ioi m (neg_pos.2 hαβ)).const_mul _)
    refine hint.congr (Eventually.of_forall fun u => ?_)
    exact (hval u).symm

/-- **Half-plane integrability** `{v > m}` (by the swap symmetry and evenness of `p_t`). -/
theorem integrable_halfplane_snd {t : ℝ} (ht : 0 < t) (m α β : ℝ) (hαβ : α + β < 0) :
    Integrable (fun p : ℝ × ℝ => (Ioi m).indicator (fun v => Real.exp (β * v)) p.2
      * (Real.exp (α * p.1) * heatKernel t (p.1 - p.2))) (volume.prod volume) := by
  have h := (integrable_halfplane_fst ht m β α (by linarith)).swap
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
  rw [show p.2 - p.1 = -(p.1 - p.2) by ring, AiryTwoInt.heatKernel_even]

/-- **Quadrant integrability**: for `α, β > 0`, `1_{u ≤ m} e^{αu} 1_{v ≤ m} e^{βv}` is
integrable on the plane (a product of one-dimensional integrable functions). -/
theorem integrable_quadrant (m : ℝ) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Integrable (fun p : ℝ × ℝ => (Iic m).indicator (fun u => Real.exp (α * u)) p.1
      * (Iic m).indicator (fun v => Real.exp (β * v)) p.2) (volume.prod volume) :=
  Integrable.mul_prod ((integrable_indicator_iff measurableSet_Iic).2
    (integrableOn_exp_mul_Iic hα m)) ((integrable_indicator_iff measurableSet_Iic).2
    (integrableOn_exp_mul_Iic hβ m))

/-- `L²` from a pointwise integrable bound on the square. -/
theorem memLp_of_sq_le {V F : ℝ × ℝ → ℝ} (hV : Measurable V)
    (hF : Integrable F (volume.prod volume)) (h : ∀ p, V p ^ 2 ≤ F p) :
    MemLp V 2 (volume.prod volume) :=
  (memLp_two_iff_integrable_sq hV.aestronglyMeasurable).2
    (hF.mono' (hV.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h p))

/-- The heat-kernel sup constant `c₀ = (4πS)^{-1/2}`. -/
noncomputable def c0 (S : ℝ) : ℝ := (4 * Real.pi * S) ^ (-1 / 2 : ℝ)

theorem c0_pos {S : ℝ} (hS : 0 < S) : 0 < c0 S := Real.rpow_pos_of_pos (by positivity) _

theorem integrable_heat_mul_heat {g τ : ℝ} (hg : 0 < g) (hτ : 0 < τ) (u v : ℝ) :
    Integrable fun w : ℝ => heatKernel g (u - w) * heatKernel τ (w - v) :=
  AiryTwoInt.integrable_pair_mul_of_heatKernel_le hg hτ (AiryTwoInt.measurable_heatKerTwo g)
    (AiryTwoInt.measurable_heatKerTwo τ)
    (fun a b => AiryTwoInt.heatKerTwo_abs_le_self hg (a, b))
    (fun a b => AiryTwoInt.heatKerTwo_abs_le_self hτ (a, b)) u v

/-- The completed-square/Chapman–Kolmogorov integrand identity. -/
theorem heat_exp_heat_eq (g τ θ c u v w : ℝ) :
    heatKernel g (u - w) * (Real.exp (θ * (w - c)) * heatKernel τ (w - v))
      = Real.exp (θ * (u - c) + g * θ ^ 2)
        * (heatKernel g ((u + 2 * g * θ) - w) * heatKernel τ (w - v)) := by
  have h := AiryTwoInt.heatKernel_mul_exp_neg_eq g (-θ) u w
  rw [show u - 2 * g * -θ = u + 2 * g * θ by ring, show -(-θ * w) = θ * w by ring,
    show -(-θ * u) + g * (-θ) ^ 2 = θ * u + g * θ ^ 2 by ring] at h
  calc heatKernel g (u - w) * (Real.exp (θ * (w - c)) * heatKernel τ (w - v))
      = Real.exp (-(θ * c)) * (heatKernel g (u - w) * Real.exp (θ * w))
          * heatKernel τ (w - v) := by
        rw [show θ * (w - c) = -(θ * c) + θ * w by ring, Real.exp_add]; ring
    _ = Real.exp (-(θ * c)) * (Real.exp (θ * u + g * θ ^ 2)
          * heatKernel g (u + 2 * g * θ - w)) * heatKernel τ (w - v) := by rw [h]
    _ = _ := by
        rw [show Real.exp (θ * (u - c) + g * θ ^ 2)
            = Real.exp (-(θ * c)) * Real.exp (θ * u + g * θ ^ 2) by
          rw [← Real.exp_add]; congr 1; ring]
        ring

/-- **Chernoff closed form**:
`∫ p_g(u - w) e^{θ(w - c)} p_τ(w - v) dw = e^{θ(u - c) + gθ²} p_{g+τ}(u - v + 2gθ)`. -/
theorem integral_heat_exp_heat {g τ : ℝ} (hg : 0 < g) (hτ : 0 < τ) (θ c u v : ℝ) :
    ∫ w : ℝ, heatKernel g (u - w) * (Real.exp (θ * (w - c)) * heatKernel τ (w - v))
      = Real.exp (θ * (u - c) + g * θ ^ 2) * heatKernel (g + τ) (u + 2 * g * θ - v) := by
  simp_rw [heat_exp_heat_eq g τ θ c u v]
  rw [integral_const_mul, AiryTwoInt.heatKernel_conv hg hτ]

theorem integrable_heat_exp_heat {g τ : ℝ} (hg : 0 < g) (hτ : 0 < τ) (θ c u v : ℝ) :
    Integrable fun w : ℝ =>
      heatKernel g (u - w) * (Real.exp (θ * (w - c)) * heatKernel τ (w - v)) := by
  simp_rw [heat_exp_heat_eq g τ θ c u v]
  exact (integrable_heat_mul_heat hg hτ (u + 2 * g * θ) v).const_mul _

/-- The shifted heat kernel: `p_S(z + d) = p_S(z) e^{-(2zd + d²)/(4S)}`. -/
theorem heatKernel_add_eq (S z d : ℝ) :
    heatKernel S (z + d) = heatKernel S z * Real.exp (-(2 * z * d + d ^ 2) / (4 * S)) := by
  unfold heatKernel
  rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
  congr 2
  ring

theorem indicator_exp_nonneg (s : Set ℝ) (c x : ℝ) :
    0 ≤ s.indicator (fun u => Real.exp (c * u)) x :=
  Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x

theorem integrable_list_sum_map {ι : Type*} (f : ι → ℝ × ℝ → ℝ) :
    ∀ l : List ι, (∀ i ∈ l, Integrable (f i) (volume.prod volume)) →
      Integrable (fun p => (l.map fun i => f i p).sum) (volume.prod volume)
  | [], _ => by simp
  | i :: l, h => by
    have := ((h i List.mem_cons_self).add
      (integrable_list_sum_map f l fun j hj => h j (List.mem_cons_of_mem _ hj)))
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp


end AiryFdd
