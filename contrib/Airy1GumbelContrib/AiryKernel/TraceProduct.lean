/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TraceClass.TraceClass
import Airy1GumbelContrib.HilbertSchmidt.KernelHS
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Trace of a product of kernel operators

The trace formula for the product of two Hilbert–Schmidt integral operators
on `L²(ℝ)`: `Tr(T_K ∘ T_K') = ∫∫ K(x, z) K'(z, x) dz dx`. This is the
standard trace formula that the paper uses for the trace of a product of two
Hilbert–Schmidt kernel operators.

## Proof outline

Pick a *countable* Hilbert basis `b` of `Lp ℝ 2 volume` (one exists because `L²(ℝ)` is
second-countable, so every orthonormal family is countable — see
`exists_countable_hilbertBasis_L2R`).  Then

  `Tr(T_K T_K') = Σᵢ ⟪b i, T_K (T_K' bᵢ)⟫ = Σᵢ ⟪(T_K)† bᵢ, T_K' bᵢ⟫`.

The adjoint of a real kernel operator is the operator of the flipped kernel
(`kernelOperator_adjoint`, via Fubini), so each summand is the `L²` inner product of two
kernel images, i.e. an integral of a pointwise product (`MeasureTheory.L2.inner_def`).
The sum is swapped with the integral by `MeasureTheory.integral_tsum`; the required
summability bound follows from the pointwise AM–GM inequality
(`ennreal_two_mul_mul_le_add_sq`) and the Hilbert–Schmidt sum-of-squares bound
`HilbertSchmidt.sumSq_kernelOperator_le`, which holds for arbitrary bases.  For a.e. `x`
the summed series collapses by Parseval (`HilbertBasis.tsum_inner_mul_inner`) to the inner
product of the two kernel slices, i.e. to `∫ z, K (z, x) * K' (x, z)`.  A final Fubini
swap (`MeasureTheory.integral_integral_swap`) gives the stated symmetric form.
-/

namespace AiryConj

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal InnerProduct InnerProductSpace
open scoped Classical
open HilbertSchmidt

/-- The composite kernel `K''(x, y) = ∫ z, K (x, z) * K' (z, y)` of two
Hilbert–Schmidt kernels (real-valued, Lebesgue measure). -/
noncomputable def compKernel (K K' : ℝ × ℝ → ℝ) (xy : ℝ × ℝ) : ℝ :=
  ∫ z : ℝ, K (xy.1, z) * K' (z, xy.2)

/-- The flipped kernel `Kᵀ(x, y) = K(y, x)`: the kernel of the adjoint operator. -/
noncomputable def kernelFlip (K : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := K (p.2, p.1)

/-- The flip of an `L²` kernel on the product space is still `L²` (the swap map is
measure-preserving). -/
theorem memLp_kernelFlip {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume)) :
    MemLp (kernelFlip K) 2 (volume.prod volume) :=
  hK.comp_measurePreserving MeasureTheory.Measure.measurePreserving_swap

/-- AM–GM in `ℝ≥0∞`, division-free form: `2 * (a * b) ≤ a² + b²`. -/
theorem ennreal_two_mul_mul_le_add_sq (a b : ℝ≥0∞) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne (a ^ 2 + b ^ 2) ⊤ with htop | hfin
  · rw [htop]
    exact le_top
  have ha : a ≠ ⊤ := by
    intro ha
    exact hfin (by rw [ha]; simp [pow_two])
  have hb : b ≠ ⊤ := by
    intro hb
    exact hfin (by rw [hb]; simp [pow_two])
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ))]

/-- The pointwise product of the two coordinate projections of two `L²` functions is
square-integrable on the product space: `‖(x, y) ↦ f y * g x‖₂² = ‖f‖₂² * ‖g‖₂²`. -/
theorem memLp_mul_snd_fst (f g : Lp ℝ 2 (volume : Measure ℝ)) :
    MemLp (fun p : ℝ × ℝ => f p.2 * g p.1) 2 (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2 * g p.1) (volume.prod volume) :=
    ((Lp.aestronglyMeasurable f).comp_snd).mul ((Lp.aestronglyMeasurable g).comp_fst)
  have key : (∫⁻ p : ℝ × ℝ, ‖f p.2‖ₑ ^ 2 * ‖g p.1‖ₑ ^ 2 ∂(volume.prod volume))
      = (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 ∂volume) * (∫⁻ x : ℝ, ‖g x‖ₑ ^ 2 ∂volume) :=
    (lintegral_congr fun p => mul_comm _ _).trans
      ((lintegral_prod_mul (((Lp.aestronglyMeasurable g).enorm).pow_const 2)
        (((Lp.aestronglyMeasurable f).enorm).pow_const 2)).trans (mul_comm _ _))
  have hsq : (eLpNorm (fun p : ℝ × ℝ => f p.2 * g p.1) 2 (volume.prod volume)) ^ 2
      = (eLpNorm f 2 volume) ^ 2 * (eLpNorm g 2 volume) ^ 2 := by
    rw [eLpNorm_two_sq_eq_lintegral hmeas, eLpNorm_two_sq_eq_lintegral
      (Lp.aestronglyMeasurable f), eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable g)]
    rw [show (∫⁻ p : ℝ × ℝ, ‖f p.2 * g p.1‖ₑ ^ 2 ∂(volume.prod volume))
        = ∫⁻ p : ℝ × ℝ, ‖f p.2‖ₑ ^ 2 * ‖g p.1‖ₑ ^ 2 ∂(volume.prod volume) from
      lintegral_congr fun p => by rw [enorm_mul, mul_pow]]
    exact key
  have hfin : (eLpNorm (fun p : ℝ × ℝ => f p.2 * g p.1) 2 (volume.prod volume)) ^ 2 ≠ ⊤ := by
    rw [hsq]
    exact ENNReal.mul_ne_top
      (lt_top_iff_ne_top.1 (ENNReal.pow_lt_top (Lp.eLpNorm_lt_top f)))
      (lt_top_iff_ne_top.1 (ENNReal.pow_lt_top (Lp.eLpNorm_lt_top g)))
  rw [memLp_iff, lt_top_iff_ne_top]
  intro htop
  exact hfin (by rw [htop, pow_two, ENNReal.top_mul_top])

/-- The product integrand `(x, z) ↦ K (z, x) * f z * g x` of a real `L²` kernel against two
`L²` functions is integrable on the product space (Cauchy–Schwarz). -/
theorem integrable_prod_mul {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume))
    (f g : Lp ℝ 2 (volume : Measure ℝ)) :
    Integrable (Function.uncurry fun x z : ℝ => K (z, x) * f z * g x) (volume.prod volume) := by
  have h := MemLp.integrable_mul (memLp_kernelFlip hK) (memLp_mul_snd_fst f g)
  convert h using 1
  ext p
  show K (p.2, p.1) * f p.2 * g p.1 = K (p.2, p.1) * (f p.2 * g p.1)
  rw [mul_assoc]

/-- The bilinear form of a kernel operator equals that of the flipped kernel with the
arguments swapped: `⟪T_{Kᵀ} f, g⟫ = ⟪f, T_K g⟫` (Fubini). -/
theorem inner_kernelOperator_flip {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume))
    (f g : Lp ℝ 2 (volume : Measure ℝ)) :
    ⟪kernelOperator (memLp_kernelFlip hK) f, g⟫_ℝ = ⟪f, kernelOperator hK g⟫_ℝ := by
  have hInt := integrable_prod_mul hK f g
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have lhs : ∀ᵐ x : ℝ ∂volume, ⟪(kernelOperator (memLp_kernelFlip hK) f) x, g x⟫_ℝ
      = ∫ z : ℝ, K (z, x) * f z * g x := by
    filter_upwards [kernelOperator_apply_ae (memLp_kernelFlip hK) f] with x hx
    rw [hx, Real.inner_apply]
    show (∫ z : ℝ, kernelFlip K (x, z) * f z) * g x = ∫ z : ℝ, K (z, x) * f z * g x
    rw [← integral_mul_const]
    simp only [kernelFlip]
  calc ∫ a : ℝ, ⟪(kernelOperator (memLp_kernelFlip hK) f) a, g a⟫_ℝ ∂volume
      = ∫ x : ℝ, ∫ z : ℝ, K (z, x) * f z * g x ∂volume ∂volume := integral_congr_ae lhs
    _ = ∫ z : ℝ, ∫ x : ℝ, K (z, x) * f z * g x ∂volume ∂volume :=
        integral_integral_swap hInt
    _ = ∫ z : ℝ, f z * (∫ x : ℝ, K (z, x) * g x ∂volume) ∂volume := by
        apply integral_congr_ae
        filter_upwards with z
        rw [show (∫ x : ℝ, K (z, x) * f z * g x ∂volume)
            = ∫ x : ℝ, f z * (K (z, x) * g x) ∂volume from
          integral_congr_ae (ae_of_all _ fun x => by ring)]
        rw [integral_const_mul]
    _ = ∫ z : ℝ, ⟪f z, (kernelOperator hK g) z⟫_ℝ ∂volume := by
        apply integral_congr_ae
        filter_upwards [kernelOperator_apply_ae hK g] with z hz
        rw [hz, Real.inner_apply]
        rfl

/-- The adjoint of a real kernel operator is the operator of the flipped kernel:
`(T_K)† = T_{Kᵀ}` where `Kᵀ(x, y) = K(y, x)`. -/
theorem kernelOperator_adjoint {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume)) :
    (kernelOperator hK)† = kernelOperator (memLp_kernelFlip hK) := by
  have key := (ContinuousLinearMap.eq_adjoint_iff (kernelOperator (memLp_kernelFlip hK))
    (kernelOperator hK)).2 (inner_kernelOperator_flip hK)
  exact key.symm

/-- A countable Hilbert basis of `L²(ℝ)` exists: `L²(ℝ)` is second-countable, hence
separable, and an orthonormal family in a separable space is countable (the balls of
radius `1/2` around the basis vectors are pairwise disjoint, nonempty and open). -/
theorem exists_countable_hilbertBasis_L2R :
    ∃ (ι : Type) (_ : Countable ι), Nonempty (HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure ℝ))) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ (Lp ℝ 2 (volume : Measure ℝ))
  have hd : Pairwise (Function.onFun Disjoint fun i : w => Metric.ball (b i) (1/2 : ℝ)) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hbij : b i ≠ b j := by
      intro h
      have h1 : ⟪b i, b j⟫_ℝ = (0 : ℝ) := b.orthonormal.2 hij
      rw [← h, real_inner_self_eq_norm_sq, b.orthonormal.1 i] at h1
      norm_num at h1
    have h2 : ‖b i - b j‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, b.orthonormal.2 hij, b.orthonormal.1 i, b.orthonormal.1 j]
      norm_num
    have hdist : (1 : ℝ) ≤ dist (b i) (b j) := by
      rw [dist_eq_norm]
      by_contra hlt
      push Not at hlt
      nlinarith [norm_nonneg (b i - b j)]
    calc (1/2 : ℝ) + 1/2 = 1 := by norm_num
      _ ≤ dist (b i) (b j) := hdist
  have hcount : Countable w :=
    Pairwise.countable_of_isOpen_disjoint hd (fun _ => Metric.isOpen_ball)
      (fun _ => Metric.nonempty_ball.2 (by norm_num))
  exact ⟨↥w, hcount, ⟨b⟩⟩

/-- The trace of a product of two real kernel operators is the cross-integrated kernel
product: `Tr(T_K ∘ T_K') = ∫ x, ∫ z, K (x, z) K' (z, x)`. -/
theorem trace_kernelOperator_comp {K K' : ℝ × ℝ → ℝ}
    (hK : MemLp K 2 (volume.prod volume)) (hK' : MemLp K' 2 (volume.prod volume)) :
    trace (kernelOperator hK ∘L kernelOperator hK') =
      ∫ x : ℝ, ∫ z : ℝ, K (x, z) * K' (z, x) := by
  obtain ⟨ι, hι, ⟨b⟩⟩ := exists_countable_hilbertBasis_L2R
  letI := hι
  have hTC : IsTraceClass (kernelOperator hK ∘L kernelOperator hK') :=
    ⟨kernelOperator hK, kernelOperator hK', isHilbertSchmidt_kernelOperator hK,
      isHilbertSchmidt_kernelOperator hK', rfl⟩
  have hGmeas : ∀ i : ι, AEStronglyMeasurable
      (fun a : ℝ => (kernelOperator (memLp_kernelFlip hK) (b i)) a
        * (kernelOperator hK' (b i)) a) volume :=
    fun i => (Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _)
  have hbound : (∑' i : ι, ∫⁻ a : ℝ,
      ‖(kernelOperator (memLp_kernelFlip hK) (b i)) a * (kernelOperator hK' (b i)) a‖ₑ
        ∂volume) ≠ ⊤ := by
    have hpt : ∀ i : ι, 2 * (∫⁻ a : ℝ, ‖(kernelOperator (memLp_kernelFlip hK) (b i)) a
          * (kernelOperator hK' (b i)) a‖ₑ ∂volume)
        ≤ (∫⁻ a : ℝ, ‖(kernelOperator (memLp_kernelFlip hK) (b i)) a‖ₑ ^ 2 ∂volume)
          + (∫⁻ a : ℝ, ‖(kernelOperator hK' (b i)) a‖ₑ ^ 2 ∂volume) := by
      intro i
      rw [← lintegral_const_mul'' 2 (hGmeas i).enorm]
      calc ∫⁻ a : ℝ, 2 * ‖(kernelOperator (memLp_kernelFlip hK) (b i)) a
              * (kernelOperator hK' (b i)) a‖ₑ ∂volume
          ≤ ∫⁻ a : ℝ, (‖(kernelOperator (memLp_kernelFlip hK) (b i)) a‖ₑ ^ 2
              + ‖(kernelOperator hK' (b i)) a‖ₑ ^ 2) ∂volume :=
            lintegral_mono_ae (ae_of_all _ fun a => by
              rw [enorm_mul]
              exact ennreal_two_mul_mul_le_add_sq _ _)
        _ = (∫⁻ a : ℝ, ‖(kernelOperator (memLp_kernelFlip hK) (b i)) a‖ₑ ^ 2 ∂volume)
            + (∫⁻ a : ℝ, ‖(kernelOperator hK' (b i)) a‖ₑ ^ 2 ∂volume) :=
            lintegral_add_right' _ (((Lp.aestronglyMeasurable _).enorm).pow_const 2)
    have hsumTT : (∑' i : ι, ∫⁻ a : ℝ,
        ‖(kernelOperator (memLp_kernelFlip hK) (b i)) a‖ₑ ^ 2 ∂volume)
        = sumSq (kernelOperator (memLp_kernelFlip hK)) b :=
      tsum_congr fun i => by
        rw [Lp.enorm_def]
        exact (eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable _)).symm
    have hsumT' : (∑' i : ι, ∫⁻ a : ℝ, ‖(kernelOperator hK' (b i)) a‖ₑ ^ 2 ∂volume)
        = sumSq (kernelOperator hK') b :=
      tsum_congr fun i => by
        rw [Lp.enorm_def]
        exact (eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable _)).symm
    have h2 : 2 * (∑' i : ι, ∫⁻ a : ℝ, ‖(kernelOperator (memLp_kernelFlip hK) (b i)) a
        * (kernelOperator hK' (b i)) a‖ₑ ∂volume) ≠ ⊤ := by
      rw [← ENNReal.tsum_mul_left]
      refine ne_of_lt ((ENNReal.tsum_le_tsum hpt).trans_lt ?_)
      rw [ENNReal.tsum_add, hsumTT, hsumT']
      exact ENNReal.add_lt_top.2
        ⟨lt_of_le_of_lt (sumSq_kernelOperator_le (memLp_kernelFlip hK) b)
          (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 (memLp_kernelFlip hK).eLpNorm_ne_top)),
         lt_of_le_of_lt (sumSq_kernelOperator_le hK' b)
          (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 hK'.eLpNorm_ne_top))⟩
    intro hS
    exact h2 (by rw [hS]; exact ENNReal.mul_top (by norm_num))
  have hev : ∀ᵐ x : ℝ ∂volume, ∀ i : ι,
      (kernelOperator (memLp_kernelFlip hK) (b i)) x = ⟪sliceLp volume (kernelFlip K) x, b i⟫_ℝ
        ∧ (kernelOperator hK' (b i)) x = ⟪sliceLp volume K' x, b i⟫_ℝ := by
    rw [ae_all_iff]
    intro i
    filter_upwards [kernelOperator_eval_inner_ae (memLp_kernelFlip hK) (b i),
      kernelOperator_eval_inner_ae hK' (b i)] with x h1 h2
    exact ⟨h1, h2⟩
  have hcollapse : ∀ᵐ x : ℝ ∂volume,
      ∑' i : ι, (kernelOperator (memLp_kernelFlip hK) (b i)) x * (kernelOperator hK' (b i)) x
        = ∫ z : ℝ, K (z, x) * K' (x, z) := by
    filter_upwards [hev, memLp_conj_slice_ae (memLp_kernelFlip hK),
      memLp_conj_slice_ae hK'] with x hx hmemT hmem'
    calc ∑' i : ι, (kernelOperator (memLp_kernelFlip hK) (b i)) x
            * (kernelOperator hK' (b i)) x
        = ∑' i : ι, ⟪sliceLp volume (kernelFlip K) x, b i⟫_ℝ
            * ⟪b i, sliceLp volume K' x⟫_ℝ :=
          tsum_congr fun i => by
            rw [(hx i).1, (hx i).2, real_inner_comm (b i) (sliceLp volume K' x)]
      _ = ⟪sliceLp volume (kernelFlip K) x, sliceLp volume K' x⟫_ℝ :=
          HilbertBasis.tsum_inner_mul_inner b _ _
      _ = ∫ z : ℝ, K (z, x) * K' (x, z) := by
          rw [MeasureTheory.L2.inner_def]
          apply integral_congr_ae
          filter_upwards [sliceLp_apply_ae hmemT, sliceLp_apply_ae hmem'] with z hz1 hz2
          rw [hz1, hz2, Real.inner_apply]
          simp only [star_trivial, kernelFlip]
  have hdiag : ∀ i : ι, ⟪b i, (kernelOperator hK ∘L kernelOperator hK') (b i)⟫_ℝ
      = ∫ x : ℝ, (kernelOperator (memLp_kernelFlip hK) (b i)) x
        * (kernelOperator hK' (b i)) x ∂volume := by
    intro i
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
      kernelOperator_adjoint hK, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards with x
    exact Real.inner_apply _ _
  have hIntFinal : Integrable (Function.uncurry fun x z : ℝ => K (z, x) * K' (x, z))
      (volume.prod volume) := by
    have h := MemLp.integrable_mul (memLp_kernelFlip hK) hK'
    convert h using 1
    ext p
    show K (p.2, p.1) * K' (p.1, p.2) = kernelFlip K p * K' p
    rfl
  rw [trace_eq_tsum_inner hTC b, tsum_congr hdiag, ← integral_tsum hGmeas hbound,
    integral_congr_ae hcollapse]
  exact integral_integral_swap hIntFinal

end AiryConj
