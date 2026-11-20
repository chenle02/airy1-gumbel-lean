/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.HilbertSchmidt.HilbertSchmidt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod

/-! # Kernel operators on `L²` are Hilbert–Schmidt

For a scalar kernel `K : X × X → 𝕜` (with `𝕜` an `RCLike` field) which is square-integrable
for the product measure (`MemLp K 2 (μ.prod μ)`), the integral operator

  `T_K f x = ∫ y, K (x, y) * f y ∂μ`,     `kernelOperator hK : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ`,

is Hilbert–Schmidt, and its Hilbert–Schmidt sum of squares equals the squared `L²`-norm of
the kernel.

## Main results

* `HilbertSchmidt.enorm_kernelOperator_le`: the operator norm of `T_K` is at most the `L²` norm
  of the kernel (Cauchy–Schwarz/Hölder on each slice).
* `HilbertSchmidt.sumSq_kernelOperator_le`: the general bound
  `sumSq (T_K) b ≤ (eLpNorm K 2 (μ.prod μ))²` for *every* Hilbert basis `b` of `L²(μ)`
  (no countability assumptions), hence `IsHilbertSchmidt (T_K)` and
  `hsENorm (T_K) ≤ eLpNorm K 2 (μ.prod μ)`; also the operator norm bound
  `HilbertSchmidt.enorm_kernelOperator_le`.
* `HilbertSchmidt.sumSq_kernelOperator_eq`: the norm **equality** for a *countable* Hilbert
  basis of `L²(μ)`, via Parseval inside the integral and Tonelli;
  `HilbertSchmidt.hsENorm_kernelOperator`: `hsENorm (T_K) = eLpNorm K 2 (μ.prod μ)`.

## Proof notes

The operator is defined pointwise and packaged with `LinearMap.mkContinuous`. The
sum-of-squares computation goes through the slices `K (x, ·)`: for a.e. `x` the slice is in
`L²(μ)` (Tonelli + `ae_lt_top'`), and `T_K f x = ⟪slice_x, f⟫_𝕜` a.e., so
`‖T_K bᵢ‖² = ∫ ‖⟪slice_x, bᵢ⟫_𝕜‖² dx`; the sum over `i` then uses Bessel's inequality (for
`≤`) or Parseval (for `=`, where the `∑ᵢ`-`∫` swap is `lintegral_tsum`, which requires
countability — a non-separable generalization would need monotone convergence over a
non-countable directed set, which is false in general measure spaces).

## Possible extensions

* The bilinear-form evaluation `⟪T_K f, g⟫_𝕜 = ∫ p, conj (K p) * conj (f p.2) * g p.1`
  (the `mercerForm` pattern) for trace computations in `TraceClass/`.
-/

open MeasureTheory Filter
open scoped ENNReal InnerProduct InnerProductSpace
open scoped Classical

namespace MeasureTheory

/-- For an a.e.-strongly-measurable `f`, `(eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ`. -/
theorem eLpNorm_two_sq_eq_lintegral {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  simp_rw [show ∀ x : α, ‖f x‖ₑ ^ (2:ℝ) = ‖f x‖ₑ ^ 2 from fun x => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]]
  rw [← ENNReal.rpow_natCast _ (2 : ℕ), show ((2 : ℕ) : ℝ) = 2 by norm_num,
    ← ENNReal.rpow_mul, show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

end MeasureTheory

namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜] [BorelSpace 𝕜]
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

/-- `X ^ (2 : ℝ) = X ^ 2` for `X : ℝ≥0∞`. -/
theorem enorm_rpow_two (X : ℝ≥0∞) : X ^ (2 : ℝ) = X ^ 2 := by
  rw [← ENNReal.rpow_natCast]
  norm_num

/-- `(X ^ (1/2 : ℝ)) ^ 2 = X` for `X : ℝ≥0∞`. -/
theorem rpow_half_sq (X : ℝ≥0∞) : (X ^ (1/2 : ℝ)) ^ 2 = X := by
  rw [← ENNReal.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num, ← ENNReal.rpow_mul,
    show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

/-- `(X ^ 2) ^ (1/2 : ℝ) = X` for `X : ℝ≥0∞`. -/
theorem rpow_half_sq' (X : ℝ≥0∞) : (X ^ 2) ^ (1/2 : ℝ) = X := by
  rw [← ENNReal.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num, ← ENNReal.rpow_mul,
    show (2 : ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one]

omit [BorelSpace 𝕜] in
/-- For a.e. `x`, the slice `K (x, ·)` of a product-`L²` kernel is a.e.-strongly-measurable
with finite second moment. -/
theorem slice_measurable_finite_ae {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => K (x, y)) μ
      ∧ (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ) < ⊤ := by
  have hmeas : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => K (x, y)) μ :=
    AEStronglyMeasurable.prodMk_left hK.aestronglyMeasurable
  have hKnorm : AEMeasurable (fun p => ‖K p‖ₑ ^ 2) (μ.prod μ) :=
    (hK.aestronglyMeasurable.enorm).pow_const (2 : ℕ)
  have hfin : ∀ᵐ x ∂μ, (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ) < ⊤ := by
    apply ae_lt_top' hKnorm.lintegral_prod_right'
    rw [(MeasureTheory.lintegral_prod _ hKnorm).symm,
      ← MeasureTheory.eLpNorm_two_sq_eq_lintegral hK.aestronglyMeasurable, pow_two]
    exact ENNReal.mul_ne_top hK.eLpNorm_ne_top hK.eLpNorm_ne_top
  filter_upwards [hmeas, hfin] with x h1 h2
  exact ⟨h1, h2⟩

omit [BorelSpace 𝕜] in
/-- For a.e. `x`, the conjugated slice `star ∘ K (x, ·)` is in `L²(μ)`. -/
theorem memLp_conj_slice_ae {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y => star (K (x, y))) 2 μ := by
  filter_upwards [slice_measurable_finite_ae hK] with x hx
  rw [memLp_iff]
  have hnorm : eLpNorm (fun y => star (K (x, y))) 2 μ = eLpNorm (fun y => K (x, y)) 2 μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (continuous_star.comp_aestronglyMeasurable hx.1),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hx.1]
    congr 1
    apply lintegral_congr
    intro y
    simp
  rw [hnorm]
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hx.1).2 ?_
  rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  simp_rw [enorm_rpow_two]
  exact hx.2

/-- The conjugated slice of the kernel at `x`, as an element of `Lp 𝕜 2 μ`
(junk value `0` when the slice is not in `L²`). -/
noncomputable def sliceLp (μ : Measure X) (K : X × X → 𝕜) (x : X) : Lp 𝕜 2 μ :=
  if h : MemLp (fun y => star (K (x, y))) 2 μ then MemLp.toLp (fun y => star (K (x, y))) h else 0

omit [BorelSpace 𝕜] [SFinite μ] in
/-- The slice at `x` is the `toLp` of the conjugated slice of `K` when that is in `L²`. -/
theorem sliceLp_eq_toLp {K : X × X → 𝕜} {x : X}
    (hx : MemLp (fun y => star (K (x, y))) 2 μ) :
    sliceLp μ K x = MemLp.toLp (fun y => star (K (x, y))) hx := by
  unfold sliceLp
  exact dite_eq_left hx

omit [BorelSpace 𝕜] [SFinite μ] in
/-- The slice as a function is a.e. the conjugated slice of `K` at `x` when that is in
`L²`. -/
theorem sliceLp_apply_ae {K : X × X → 𝕜} {x : X}
    (hx : MemLp (fun y => star (K (x, y))) 2 μ) :
    ∀ᵐ y ∂μ, (sliceLp μ K x) y = star (K (x, y)) := by
  rw [sliceLp_eq_toLp hx]
  exact MemLp.coeFn_toLp hx

omit [BorelSpace 𝕜] in
/-- The `L²`-norm of the slice: `‖sliceLp μ K x‖ₑ ^ 2 = ∫⁻ y, ‖K (x, y)‖ₑ ^ 2` for a.e. `x`. -/
theorem enorm_sliceLp_sq {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, ‖sliceLp μ K x‖ₑ ^ 2 = ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ := by
  filter_upwards [memLp_conj_slice_ae hK] with x hxs
  have h0 : ‖sliceLp μ K x‖ₑ ^ 2 = (eLpNorm (sliceLp μ K x) 2 μ) ^ 2 := by rw [Lp.enorm_def]
  rw [h0, MeasureTheory.eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable _)]
  apply lintegral_congr_ae
  filter_upwards [sliceLp_apply_ae hxs] with y hy
  rw [hy]
  simp

/-- The pointwise kernel integral `x ↦ ∫ y, K (x, y) * f y ∂μ`. -/
noncomputable def kernelIntegralFun (K : X × X → 𝕜) (f : Lp 𝕜 2 μ) : X → 𝕜 :=
  fun x => ∫ y, K (x, y) * f y ∂μ

omit [BorelSpace 𝕜] in
/-- The pointwise kernel integral is a.e.-strongly-measurable. -/
theorem kernelIntegralFun_aestronglyMeasurable {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ))
    (f : Lp 𝕜 2 μ) :
    AEStronglyMeasurable (kernelIntegralFun K f) μ :=
  (hK.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).comp_snd)).integral_prod_right'

omit [BorelSpace 𝕜] in
/-- For a.e. `x`, the integrand `K (x, ·) * f` of the kernel integral is integrable. -/
theorem integrable_kernelFun_slice_ae {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ))
    (f : Lp 𝕜 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * f y) μ := by
  filter_upwards [memLp_conj_slice_ae hK] with x hxs
  have h := MeasureTheory.L2.integrable_inner (𝕜 := 𝕜) (sliceLp μ K x) f
  apply h.congr
  filter_upwards [sliceLp_apply_ae hxs] with y hy
  rw [RCLike.inner_apply', hy]
  simp

omit [BorelSpace 𝕜] in
/-- Pointwise bound for the kernel integral:
`‖T f x‖ₑ ^ 2 ≤ (∫⁻ y, ‖K (x, y)‖ₑ ^ 2) * (eLpNorm f 2 μ) ^ 2` for a.e. `x`. -/
theorem kernelIntegralFun_enorm_sq_le {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ))
    (f : Lp 𝕜 2 μ) :
    ∀ᵐ x ∂μ, ‖kernelIntegralFun K f x‖ₑ ^ 2
      ≤ (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ) * (eLpNorm f 2 μ) ^ 2 := by
  filter_upwards [slice_measurable_finite_ae hK] with x hx
  have hnorm : AEMeasurable (fun y => ‖K (x, y)‖ₑ) μ := hx.1.enorm
  have hnormf : AEMeasurable (fun y => ‖f y‖ₑ) μ := (Lp.aestronglyMeasurable f).enorm
  have hstep : ‖kernelIntegralFun K f x‖ₑ ≤ ∫⁻ y, ‖K (x, y)‖ₑ * ‖f y‖ₑ ∂μ :=
    (enorm_integral_le_lintegral_enorm _).trans_eq
      (lintegral_congr fun y => enorm_mul _ _)
  have hholder : ∫⁻ y, ‖K (x, y)‖ₑ * ‖f y‖ₑ ∂μ
      ≤ (∫⁻ y, (‖K (x, y)‖ₑ) ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) * (∫⁻ y, (‖f y‖ₑ) ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hnorm hnormf
  calc ‖kernelIntegralFun K f x‖ₑ ^ 2
      ≤ (∫⁻ y, ‖K (x, y)‖ₑ * ‖f y‖ₑ ∂μ) ^ 2 := by gcongr
    _ ≤ ((∫⁻ y, (‖K (x, y)‖ₑ) ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) * (∫⁻ y, (‖f y‖ₑ) ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ y, (‖K (x, y)‖ₑ) ^ (2:ℝ) ∂μ) * (∫⁻ y, (‖f y‖ₑ) ^ (2:ℝ) ∂μ) := by
        rw [mul_pow, rpow_half_sq, rpow_half_sq]
    _ = (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ) * (∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) := by
        congr 1 <;> · apply lintegral_congr; intro y; rw [enorm_rpow_two]
    _ = (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ) * (eLpNorm f 2 μ) ^ 2 := by
        rw [MeasureTheory.eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable f)]

omit [BorelSpace 𝕜] in
/-- The `L²`-bound for the kernel integral:
`eLpNorm (T f) ≤ eLpNorm K * eLpNorm f`. -/
theorem eLpNorm_kernelIntegral_le {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) (f : Lp 𝕜 2 μ) :
    eLpNorm (kernelIntegralFun K f) 2 μ ≤ eLpNorm K 2 (μ.prod μ) * eLpNorm f 2 μ := by
  have hmeas := kernelIntegralFun_aestronglyMeasurable hK f
  have hKnorm : AEMeasurable (fun p => ‖K p‖ₑ) (μ.prod μ) := hK.aestronglyMeasurable.enorm
  have hmain : (∫⁻ x, ‖kernelIntegralFun K f x‖ₑ ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ)
      ≤ ((eLpNorm K 2 (μ.prod μ)) ^ 2 * (eLpNorm f 2 μ) ^ 2) ^ (1/2 : ℝ) := by
    apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 1/2)
    calc (∫⁻ x, ‖kernelIntegralFun K f x‖ₑ ^ (2:ℝ) ∂μ)
        ≤ ∫⁻ x, (∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ) * (eLpNorm f 2 μ) ^ 2 ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [kernelIntegralFun_enorm_sq_le hK f] with x hx
          rwa [enorm_rpow_two]
      _ = (∫⁻ x, ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ ∂μ) * (eLpNorm f 2 μ) ^ 2 := by
          rw [lintegral_mul_const'' _ ((hKnorm.pow_const (2:ℕ)).lintegral_prod_right')]
      _ = (∫⁻ p, ‖K p‖ₑ ^ 2 ∂(μ.prod μ)) * (eLpNorm f 2 μ) ^ 2 := by
          rw [MeasureTheory.lintegral_prod _ ((hKnorm.pow_const (2:ℕ)))]
      _ = (eLpNorm K 2 (μ.prod μ)) ^ 2 * (eLpNorm f 2 μ) ^ 2 := by
          rw [MeasureTheory.eLpNorm_two_sq_eq_lintegral hK.aestronglyMeasurable]
  calc eLpNorm (kernelIntegralFun K f) 2 μ
      = (∫⁻ x, ‖kernelIntegralFun K f x‖ₑ ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) :=
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmeas
    _ ≤ ((eLpNorm K 2 (μ.prod μ)) ^ 2 * (eLpNorm f 2 μ) ^ 2) ^ (1/2 : ℝ) := hmain
    _ = (eLpNorm K 2 (μ.prod μ)) * (eLpNorm f 2 μ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2), rpow_half_sq',
          rpow_half_sq']

omit [BorelSpace 𝕜] in
/-- The pointwise kernel integral is in `L²(μ)`. -/
theorem memLp_kernelIntegral {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) (f : Lp 𝕜 2 μ) :
    MemLp (kernelIntegralFun K f) 2 μ := by
  rw [memLp_iff]
  exact (eLpNorm_kernelIntegral_le hK f).trans_lt
    (ENNReal.mul_lt_top hK.eLpNorm_lt_top (Lp.eLpNorm_lt_top f))

omit [BorelSpace 𝕜] in
/-- For a.e. `x`, the pointwise kernel integral equals the inner product against the slice. -/
theorem kernelIntegralFun_eq_inner_ae {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ))
    (f : Lp 𝕜 2 μ) :
    ∀ᵐ x ∂μ, kernelIntegralFun K f x = ⟪sliceLp μ K x, f⟫_𝕜 := by
  filter_upwards [memLp_conj_slice_ae hK] with x hxs
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sliceLp_apply_ae hxs] with y hy
  rw [RCLike.inner_apply', hy]
  simp

omit [BorelSpace 𝕜] in
/-- The kernel integral is additive in `f` (a.e.). -/
theorem kernelIntegralFun_add_ae {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ))
    (f g : Lp 𝕜 2 μ) :
    (fun x => ∫ y, K (x, y) * (f + g) y ∂μ) =ᵐ[μ]
      fun x => (∫ y, K (x, y) * f y ∂μ) + (∫ y, K (x, y) * g y ∂μ) := by
  filter_upwards [integrable_kernelFun_slice_ae hK f, integrable_kernelFun_slice_ae hK g]
    with x hxf hxg
  have h : (∫ y, K (x, y) * (f + g) y ∂μ) = ∫ y, K (x, y) * f y + K (x, y) * g y ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy, Pi.add_apply]
    ring
  rw [h, integral_add hxf hxg]

omit [BorelSpace 𝕜] in
/-- The kernel integral is homogeneous in `f` (a.e.). -/
theorem kernelIntegralFun_smul_ae {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) (c : 𝕜)
    (f : Lp 𝕜 2 μ) :
    (fun x => ∫ y, K (x, y) * (c • f) y ∂μ) =ᵐ[μ] fun x => c * (∫ y, K (x, y) * f y ∂μ) := by
  filter_upwards [integrable_kernelFun_slice_ae hK f] with x hxf
  have h : (∫ y, K (x, y) * (c • f) y ∂μ) = ∫ y, c * (K (x, y) * f y) ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, MeasureTheory.integral_const_mul]

/-- The kernel integral operator as a continuous linear map on `L²(μ)`. -/
noncomputable def kernelOperator {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) :
    Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => MemLp.toLp _ (memLp_kernelIntegral hK f)
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_kernelIntegral hK (f + g)),
          MemLp.coeFn_toLp (memLp_kernelIntegral hK f),
          MemLp.coeFn_toLp (memLp_kernelIntegral hK g),
          Lp.coeFn_add (MemLp.toLp _ (memLp_kernelIntegral hK f))
            (MemLp.toLp _ (memLp_kernelIntegral hK g)),
          kernelIntegralFun_add_ae hK f g] with x hfg hf' hg' hadd hsplit
        rw [hfg, hadd, Pi.add_apply, hf', hg']
        exact hsplit
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_kernelIntegral hK (c • f)),
          MemLp.coeFn_toLp (memLp_kernelIntegral hK f),
          Lp.coeFn_smul c (MemLp.toLp _ (memLp_kernelIntegral hK f)),
          kernelIntegralFun_smul_ae hK c f] with x hcf hf' hsmul hsplit
        rw [hcf, RingHom.id_apply, hsmul, Pi.smul_apply, hf', smul_eq_mul]
        exact hsplit }
    ((eLpNorm K 2 (μ.prod μ)).toReal)
    (fun f => by
      have hb := eLpNorm_kernelIntegral_le hK f
      have hfin : eLpNorm K 2 (μ.prod μ) * eLpNorm f 2 μ ≠ ⊤ :=
        ENNReal.mul_ne_top hK.eLpNorm_ne_top (Lp.eLpNorm_ne_top f)
      calc ‖MemLp.toLp _ (memLp_kernelIntegral hK f)‖
          = (eLpNorm (kernelIntegralFun K f) 2 μ).toReal := by
            rw [Lp.norm_def]
            congr 1
            exact eLpNorm_congr_ae (MemLp.coeFn_toLp _)
        _ ≤ (eLpNorm K 2 (μ.prod μ) * eLpNorm f 2 μ).toReal :=
            ENNReal.toReal_mono hfin hb
        _ = (eLpNorm K 2 (μ.prod μ)).toReal * (eLpNorm f 2 μ).toReal := ENNReal.toReal_mul
        _ = (eLpNorm K 2 (μ.prod μ)).toReal * ‖f‖ := by rw [Lp.norm_def])

omit [BorelSpace 𝕜] in
/-- The operator applied to `f` is a.e. the pointwise kernel integral. -/
theorem kernelOperator_apply_ae {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) (f : Lp 𝕜 2 μ) :
    ∀ᵐ x ∂μ, (kernelOperator hK f) x = kernelIntegralFun K f x := by
  have h : kernelOperator hK f = MemLp.toLp _ (memLp_kernelIntegral hK f) := rfl
  rw [h]
  exact MemLp.coeFn_toLp _

omit [BorelSpace 𝕜] in
/-- For a.e. `x`, `(T_K f) x = ⟪sliceLp μ K x, f⟫_𝕜`. -/
theorem kernelOperator_eval_inner_ae {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ))
    (f : Lp 𝕜 2 μ) :
    ∀ᵐ x ∂μ, (kernelOperator hK f) x = ⟪sliceLp μ K x, f⟫_𝕜 := by
  filter_upwards [kernelOperator_apply_ae hK f, kernelIntegralFun_eq_inner_ae hK f]
    with x h1 h2
  rw [h1, h2]

omit [BorelSpace 𝕜] in
/-- The operator norm of the kernel operator is bounded by the `L²`-norm of the kernel. -/
theorem enorm_kernelOperator_le {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) :
    ‖kernelOperator hK‖ₑ ≤ eLpNorm K 2 (μ.prod μ) := by
  apply ContinuousLinearMap.opENorm_le_bound
  intro f
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (kernelOperator_apply_ae hK f)]
  exact eLpNorm_kernelIntegral_le hK f

omit [BorelSpace 𝕜] in
/-- The Hilbert–Schmidt sum of squares of the kernel operator is bounded by the squared
`L²`-norm of the kernel.  No countability assumption is needed: finite partial sums are
estimated by Bessel's inequality pointwise in `x`, and the bound is closed by Tonelli. -/
theorem sumSq_kernelOperator_le {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) {ι : Type*}
    (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) :
    sumSq (kernelOperator hK) b ≤ (eLpNorm K 2 (μ.prod μ)) ^ 2 := by
  have hKnorm : AEMeasurable (fun p => ‖K p‖ₑ ^ 2) (μ.prod μ) :=
    (hK.aestronglyMeasurable.enorm).pow_const (2 : ℕ)
  rw [show (eLpNorm K 2 (μ.prod μ)) ^ 2 = ∫⁻ p, ‖K p‖ₑ ^ 2 ∂(μ.prod μ) from
    MeasureTheory.eLpNorm_two_sq_eq_lintegral hK.aestronglyMeasurable]
  unfold sumSq
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  calc ∑ i ∈ s, ‖kernelOperator hK (b i)‖ₑ ^ 2
      = ∑ i ∈ s, ∫⁻ x, ‖(kernelOperator hK (b i)) x‖ₑ ^ 2 ∂μ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Lp.enorm_def, MeasureTheory.eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable _)]
    _ = ∫⁻ x, ∑ i ∈ s, ‖(kernelOperator hK (b i)) x‖ₑ ^ 2 ∂μ := by
        rw [lintegral_finsetSum' s (fun i _ =>
          ((Lp.aestronglyMeasurable _).enorm).pow_const (2 : ℕ))]
    _ ≤ ∫⁻ x, ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ ∂μ := by
        apply lintegral_mono_ae
        have hb : ∀ i, i ∈ s → ∀ᵐ x ∂μ, (kernelOperator hK (b i)) x = ⟪sliceLp μ K x, b i⟫_𝕜 :=
          fun i _ => kernelOperator_eval_inner_ae hK (b i)
        filter_upwards [ae_ball_iff (Finset.countable_toSet s) |>.2 hb, enorm_sliceLp_sq hK]
          with x hx hxn
        calc ∑ i ∈ s, ‖(kernelOperator hK (b i)) x‖ₑ ^ 2
            = ∑ i ∈ s, ‖⟪b i, sliceLp μ K x⟫_𝕜‖ₑ ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hx i hi, ← inner_conj_symm (sliceLp μ K x) (b i), RCLike.enorm_conj]
          _ ≤ ‖sliceLp μ K x‖ₑ ^ 2 := by
              rw [show (∑ i ∈ s, ‖⟪b i, sliceLp μ K x⟫_𝕜‖ₑ ^ 2)
                  = ENNReal.ofReal (∑ i ∈ s, ‖⟪b i, sliceLp μ K x⟫_𝕜‖ ^ 2) from
                (Finset.sum_congr rfl fun i _ => enorm_sq_eq_ofReal _).trans
                  (ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity).symm,
                enorm_sq_eq_ofReal (sliceLp μ K x)]
              apply ENNReal.ofReal_le_ofReal
              exact (HilbertBasis.orthonormal b).sum_inner_products_le _
          _ = ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ := hxn
    _ = ∫⁻ p, ‖K p‖ₑ ^ 2 ∂(μ.prod μ) := (MeasureTheory.lintegral_prod _ hKnorm).symm

omit [BorelSpace 𝕜] in
/-- The kernel operator is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_kernelOperator {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) :
    IsHilbertSchmidt (kernelOperator hK) := by
  unfold IsHilbertSchmidt hsENorm
  apply ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  refine ne_of_lt ((sumSq_kernelOperator_le hK (canonicalBasis 𝕜 (Lp 𝕜 2 μ))).trans_lt ?_)
  exact ENNReal.pow_lt_top hK.eLpNorm_lt_top

omit [BorelSpace 𝕜] in
/-- The Hilbert–Schmidt enorm of the kernel operator is bounded by the `L²`-norm of the
kernel. -/
theorem hsENorm_kernelOperator_le {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) :
    hsENorm (kernelOperator hK) ≤ eLpNorm K 2 (μ.prod μ) := by
  unfold hsENorm
  calc (sumSq (kernelOperator hK) (canonicalBasis 𝕜 (Lp 𝕜 2 μ))) ^ (1/2 : ℝ)
      ≤ ((eLpNorm K 2 (μ.prod μ)) ^ 2) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow (sumSq_kernelOperator_le hK _) (by norm_num)
    _ = eLpNorm K 2 (μ.prod μ) := rpow_half_sq' _

omit [BorelSpace 𝕜] in
/-- The headline equality: on a *countable* Hilbert basis of `L²(μ)`, the Hilbert–Schmidt sum
of squares of the kernel operator equals the squared `L²`-norm of the kernel. -/
theorem sumSq_kernelOperator_eq {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) {ι : Type*}
    [Countable ι] (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) :
    sumSq (kernelOperator hK) b = (eLpNorm K 2 (μ.prod μ)) ^ 2 := by
  have hKnorm : AEMeasurable (fun p => ‖K p‖ₑ ^ 2) (μ.prod μ) :=
    (hK.aestronglyMeasurable.enorm).pow_const (2 : ℕ)
  rw [show (eLpNorm K 2 (μ.prod μ)) ^ 2 = ∫⁻ p, ‖K p‖ₑ ^ 2 ∂(μ.prod μ) from
    MeasureTheory.eLpNorm_two_sq_eq_lintegral hK.aestronglyMeasurable]
  calc sumSq (kernelOperator hK) b
      = ∑' i, ∫⁻ x, ‖(kernelOperator hK (b i)) x‖ₑ ^ 2 ∂μ :=
        tsum_congr fun i => by
          rw [Lp.enorm_def, MeasureTheory.eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable _)]
    _ = ∑' i, ∫⁻ x, ‖⟪sliceLp μ K x, b i⟫_𝕜‖ₑ ^ 2 ∂μ :=
        tsum_congr fun i =>
          lintegral_congr_ae ((kernelOperator_eval_inner_ae hK (b i)).mono fun x hx => by
            dsimp only
            rw [hx])
    _ = ∫⁻ x, ∑' i, ‖⟪sliceLp μ K x, b i⟫_𝕜‖ₑ ^ 2 ∂μ := by
        symm
        apply lintegral_tsum
        intro i
        exact (((Lp.aestronglyMeasurable _).enorm).pow_const (2 : ℕ)).congr
          ((kernelOperator_eval_inner_ae hK (b i)).mono fun x hx => by
            dsimp only
            rw [hx])
    _ = ∫⁻ x, ‖sliceLp μ K x‖ₑ ^ 2 ∂μ := by
        apply lintegral_congr
        intro x
        rw [show (∑' i, ‖⟪sliceLp μ K x, b i⟫_𝕜‖ₑ ^ 2)
            = ∑' i, ‖⟪b i, sliceLp μ K x⟫_𝕜‖ₑ ^ 2 from
          tsum_congr fun i => by
            rw [← inner_conj_symm (sliceLp μ K x) (b i), RCLike.enorm_conj]]
        exact HilbertBasis.enorm_sq_eq_tsum b (sliceLp μ K x)
    _ = ∫⁻ x, ∫⁻ y, ‖K (x, y)‖ₑ ^ 2 ∂μ ∂μ := lintegral_congr_ae (enorm_sliceLp_sq hK)
    _ = ∫⁻ p, ‖K p‖ₑ ^ 2 ∂(μ.prod μ) := (MeasureTheory.lintegral_prod _ hKnorm).symm

omit [BorelSpace 𝕜] in
/-- The Hilbert–Schmidt enorm of the kernel operator equals the `L²`-norm of the kernel
(on a countable Hilbert basis). -/
theorem hsENorm_kernelOperator {K : X × X → 𝕜} (hK : MemLp K 2 (μ.prod μ)) {ι : Type*}
    [Countable ι] (b : HilbertBasis ι 𝕜 (Lp 𝕜 2 μ)) :
    hsENorm (kernelOperator hK) = eLpNorm K 2 (μ.prod μ) := by
  rw [hsENorm_eq_tsum_basis (kernelOperator hK) b]
  show (sumSq (kernelOperator hK) b) ^ (1/2 : ℝ) = eLpNorm K 2 (μ.prod μ)
  rw [sumSq_kernelOperator_eq hK b, rpow_half_sq']

end HilbertSchmidt
