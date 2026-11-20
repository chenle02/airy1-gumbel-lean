/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoTime.TwoTimeBridge

/-! # `L²` tools for the two-time block estimates

Generic one-dimensional and plane tools used by `TwoTimeKernel` and `TwoTimeEst`:

* the exponential half-line integrals `∫_{(w,∞)} e^{−ax} = e^{−aw}/a`,
  `∫_{(−∞,w]} e^{ay} = e^{aw}/a` and their `lintegral` forms;
* **Jensen for a sub-probability weight** (`sq_integral_mul_le`):
  `(∫ f p)² ≤ ∫ f² p` for `p ≥ 0`, `∫ p ≤ 1`;
* the `L²` norm of a real function as `(∫⁻ ofReal (K²))^{1/2}`, and the bounds
  `eLpNorm K 2 ≤ ofReal √B` from a `lintegral` bound;
* **the Jensen–Tonelli contraction** (`lintegral_sq_compKernel_le`): for a composite kernel
  `(F ⋆ P)(z, m) = ∫ F(z, y) P(y, m) dy` with a sub-probability column weight `P`,
  `∫∫ (F ⋆ P)² ≤ ∫∫ F(z, y)² (∫ P(y, m) dm) dz dy`.  This is how a non-Hilbert–Schmidt
  contraction such as `T = P e^{dΔ} P` is absorbed into a Hilbert–Schmidt neighbour as one
  kernel (`compKernel`), never as an operator product.
-/

namespace AiryFdd

open MeasureTheory Real Set Filter
open scoped ENNReal

/-! ## Exponential half-line integrals -/

/-- `∫_{(w,∞)} e^{−ax} dx = e^{−aw}/a` for `a > 0`. -/
theorem integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) (w : ℝ) :
    ∫ x in Ioi w, Real.exp (-a * x) = Real.exp (-a * w) / a := by
  have h := integral_comp_neg_Ioi w (fun x => Real.exp (a * x))
  rw [show (fun x => Real.exp (-a * x)) = fun x => Real.exp (a * -x) by funext x; ring_nf]
  rw [h, integral_exp_mul_Iic ha]
  ring_nf

theorem integrable_indicator_exp_Ioi {a : ℝ} (ha : 0 < a) (w : ℝ) :
    Integrable ((Ioi w).indicator fun x => Real.exp (-a * x)) :=
  (integrable_indicator_iff measurableSet_Ioi).2 (exp_neg_integrableOn_Ioi w ha)

theorem integrable_indicator_exp_Iic {a : ℝ} (ha : 0 < a) (w : ℝ) :
    Integrable ((Iic w).indicator fun x => Real.exp (a * x)) :=
  (integrable_indicator_iff measurableSet_Iic).2 (integrableOn_exp_mul_Iic ha w)

/-- `∫⁻ 1_{x > w} e^{−ax} = e^{−aw}/a`. -/
theorem lintegral_indicator_exp_Ioi {a : ℝ} (ha : 0 < a) (w : ℝ) :
    ∫⁻ x, ENNReal.ofReal ((Ioi w).indicator (fun x => Real.exp (-a * x)) x)
      = ENNReal.ofReal (Real.exp (-a * w) / a) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_indicator_exp_Ioi ha w)
    (Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x),
    integral_indicator measurableSet_Ioi, integral_exp_neg_mul_Ioi ha]

/-- `∫⁻ 1_{y ≤ w} e^{ay} = e^{aw}/a`. -/
theorem lintegral_indicator_exp_Iic {a : ℝ} (ha : 0 < a) (w : ℝ) :
    ∫⁻ x, ENNReal.ofReal ((Iic w).indicator (fun x => Real.exp (a * x)) x)
      = ENNReal.ofReal (Real.exp (a * w) / a) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_indicator_exp_Iic ha w)
    (Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x),
    integral_indicator measurableSet_Iic, integral_exp_mul_Iic ha]

/-! ## Jensen for a sub-probability weight -/

/-- **Jensen**: `(∫ f p)² ≤ ∫ f² p` for `p ≥ 0` with `∫ p ≤ 1`.  Proof: `0 ≤ ∫ (f − c)² p`
with `c = ∫ f p`. -/
theorem sq_integral_mul_le {f p : ℝ → ℝ} (hp0 : ∀ y, 0 ≤ p y) (hp : Integrable p)
    (hp1 : ∫ y, p y ≤ 1) (hfp : Integrable fun y => f y * p y)
    (hf2p : Integrable fun y => f y ^ 2 * p y) :
    (∫ y, f y * p y) ^ 2 ≤ ∫ y, f y ^ 2 * p y := by
  set c := ∫ y, f y * p y with hc
  have h0 : 0 ≤ ∫ y, (f y - c) ^ 2 * p y :=
    integral_nonneg fun y => mul_nonneg (sq_nonneg _) (hp0 y)
  have hexp : (fun y => (f y - c) ^ 2 * p y)
      = fun y => (f y ^ 2 * p y - (2 * c) * (f y * p y)) + c ^ 2 * p y := by
    funext y; ring
  have hval : ∫ y, (f y - c) ^ 2 * p y
      = (∫ y, f y ^ 2 * p y) - (2 * c) * c + c ^ 2 * ∫ y, p y := by
    rw [hexp, integral_add (f := fun y => f y ^ 2 * p y - (2 * c) * (f y * p y))
      (g := fun y => c ^ 2 * p y) (hf2p.sub (hfp.const_mul _)) (hp.const_mul _),
      integral_sub (f := fun y => f y ^ 2 * p y) (g := fun y => (2 * c) * (f y * p y)) hf2p
        (hfp.const_mul _), integral_const_mul, integral_const_mul, ← hc]
  rw [hval] at h0
  have h1 : c ^ 2 * ∫ y, p y ≤ c ^ 2 :=
    (mul_le_mul_of_nonneg_left hp1 (sq_nonneg _)).trans_eq (mul_one _)
  nlinarith

/-! ## `L²` norms through `lintegral`s of squares -/

theorem eLpNorm_two_eq_lintegral_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {K : α → ℝ} (hK : AEStronglyMeasurable K μ) :
    eLpNorm K 2 μ = (∫⁻ p, ENNReal.ofReal (K p ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hK,
    show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  congr 1
  exact lintegral_congr fun p => by
    rw [HilbertSchmidt.enorm_rpow_two, enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      sq_abs]

/-- `eLpNorm K 2 ≤ ofReal √B` from `∫⁻ ofReal (K²) ≤ ofReal B`. -/
theorem eLpNorm_le_of_lintegral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {K : α → ℝ} (hK : AEStronglyMeasurable K μ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ p, ENNReal.ofReal (K p ^ 2) ∂μ ≤ ENNReal.ofReal B) :
    eLpNorm K 2 μ ≤ ENNReal.ofReal (Real.sqrt B) := by
  rw [eLpNorm_two_eq_lintegral_sq hK, Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg hB (by norm_num)]
  exact ENNReal.rpow_le_rpow h (by norm_num)

theorem memLp_of_lintegral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {K : α → ℝ} (hK : AEStronglyMeasurable K μ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ p, ENNReal.ofReal (K p ^ 2) ∂μ ≤ ENNReal.ofReal B) : MemLp K 2 μ :=
  (eLpNorm_le_of_lintegral_sq_le hK hB h).trans_lt ENNReal.ofReal_lt_top

/-- Comparison of `L²` norms through the `lintegral`s of the squares. -/
theorem eLpNorm_le_of_lintegral_sq_le_lintegral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {K K' : α → ℝ} (hK : AEStronglyMeasurable K μ)
    (hK' : AEStronglyMeasurable K' μ)
    (h : ∫⁻ p, ENNReal.ofReal (K p ^ 2) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (K' p ^ 2) ∂μ) :
    eLpNorm K 2 μ ≤ eLpNorm K' 2 μ := by
  rw [eLpNorm_two_eq_lintegral_sq hK, eLpNorm_two_eq_lintegral_sq hK']
  exact ENNReal.rpow_le_rpow h (by norm_num)

/-! ## The Jensen–Tonelli contraction for composite kernels -/

/-- **Jensen–Tonelli**: for a composite kernel `F ⋆ P` with a sub-probability column weight
`P ≥ 0` (`∫ P(y, m) dy ≤ 1`),
`∫∫ (F ⋆ P)² ≤ ∫∫ F(z, y)² · (∫⁻ P(y, m) dm) dz dy`. -/
theorem lintegral_sq_compKernel_le {F P : ℝ × ℝ → ℝ} (hF : Measurable F) (hP : Measurable P)
    (hP0 : ∀ q, 0 ≤ P q) (hP1 : ∀ m, ∫ y, P (y, m) ≤ 1)
    (hPi : ∀ m, Integrable fun y => P (y, m))
    (hFP : ∀ z m, Integrable fun y => F (z, y) * P (y, m))
    (hF2P : ∀ z m, Integrable fun y => F (z, y) ^ 2 * P (y, m)) :
    ∫⁻ q, ENNReal.ofReal (AiryConj.compKernel F P q ^ 2) ∂(volume.prod volume)
      ≤ ∫⁻ q, (ENNReal.ofReal (F q ^ 2) * ∫⁻ m, ENNReal.ofReal (P (q.2, m)))
          ∂(volume.prod volume) := by
  have hpt : ∀ q : ℝ × ℝ, ENNReal.ofReal (AiryConj.compKernel F P q ^ 2)
      ≤ ∫⁻ y, ENNReal.ofReal (F (q.1, y) ^ 2) * ENNReal.ofReal (P (y, q.2)) := by
    intro q
    obtain ⟨z, m⟩ := q
    have hJ := sq_integral_mul_le (fun y => hP0 (y, m)) (hPi m) (hP1 m) (hFP z m) (hF2P z m)
    calc ENNReal.ofReal (AiryConj.compKernel F P (z, m) ^ 2)
        ≤ ENNReal.ofReal (∫ y, F (z, y) ^ 2 * P (y, m)) := ENNReal.ofReal_le_ofReal hJ
      _ = ∫⁻ y, ENNReal.ofReal (F (z, y) ^ 2 * P (y, m)) :=
          ofReal_integral_eq_lintegral_ofReal (hF2P z m)
            (Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (hP0 _))
      _ = _ := lintegral_congr fun y => ENNReal.ofReal_mul (sq_nonneg _)
  have hF2 : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (F q ^ 2) :=
    ENNReal.measurable_ofReal.comp (hF.pow_const 2)
  have hPm : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (P q) :=
    ENNReal.measurable_ofReal.comp hP
  -- `((z, m), y) ↦ F(z, y)² P(y, m)`
  have hG : Measurable fun x : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (F (x.1.1, x.2) ^ 2) * ENNReal.ofReal (P (x.2, x.1.2)) :=
    (hF2.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hPm.comp (measurable_snd.prodMk measurable_fst.snd))
  have hGm : Measurable fun q : ℝ × ℝ =>
      ∫⁻ y, ENNReal.ofReal (F (q.1, y) ^ 2) * ENNReal.ofReal (P (y, q.2)) :=
    hG.lintegral_prod_right'
  have hR : Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal (F q ^ 2) * ∫⁻ m, ENNReal.ofReal (P (q.2, m)) :=
    hF2.mul ((Measurable.lintegral_prod_right' (f := fun x : ℝ × ℝ => ENNReal.ofReal (P x))
      hPm).comp measurable_snd)
  calc ∫⁻ q, ENNReal.ofReal (AiryConj.compKernel F P q ^ 2) ∂(volume.prod volume)
      ≤ ∫⁻ q : ℝ × ℝ, (∫⁻ y, ENNReal.ofReal (F (q.1, y) ^ 2) * ENNReal.ofReal (P (y, q.2)))
          ∂(volume.prod volume) := lintegral_mono hpt
    _ = ∫⁻ z, ∫⁻ m, ∫⁻ y, ENNReal.ofReal (F (z, y) ^ 2) * ENNReal.ofReal (P (y, m)) := by
        rw [lintegral_prod _ hGm.aemeasurable]
    _ = ∫⁻ z, ∫⁻ y, ∫⁻ m, ENNReal.ofReal (F (z, y) ^ 2) * ENNReal.ofReal (P (y, m)) := by
        refine lintegral_congr fun z => ?_
        refine lintegral_lintegral_swap ?_
        exact ((hF2.comp (measurable_const.prodMk measurable_snd)).mul
          (hPm.comp (measurable_snd.prodMk measurable_fst))).aemeasurable
    _ = ∫⁻ z, ∫⁻ y, ENNReal.ofReal (F (z, y) ^ 2) * ∫⁻ m, ENNReal.ofReal (P (y, m)) := by
        refine lintegral_congr fun z => lintegral_congr fun y => ?_
        exact lintegral_const_mul _ (hPm.comp (measurable_const.prodMk measurable_id))
    _ = ∫⁻ q, (ENNReal.ofReal (F q ^ 2) * ∫⁻ m, ENNReal.ofReal (P (q.2, m)))
          ∂(volume.prod volume) := (lintegral_prod _ hR.aemeasurable).symm

end AiryFdd
