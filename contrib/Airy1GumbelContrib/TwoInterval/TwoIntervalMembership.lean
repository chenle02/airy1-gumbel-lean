/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoInterval.TwoIntervalTrace
import Airy1GumbelContrib.AiryKernel.ConjugateUPhi
import Airy1GumbelContrib.AiryKernel.TraceExpansion

/-!
# Trace-class membership of the two-interval operators

Part of `TwoInterval/`: the `L²`/trace-class membership of the four conjugated two-interval
operators `K̃₁, K̃₂, C̃_r, K̃∪` of the paper's joint-determinant lemma and separated-block
estimate, discharging the four `MemLp` and four `IsTraceClass` hypotheses of the conditional
trace cancellation `trace_twoIntKCup` and of the conditional trace formula `trace_crKerT_eq`.

## Correspondence with the paper

* The joint-determinant lemma: the admissibility side condition is `√(2M) ≥ r + 3` with
  `a = √(2M)`; at `T = 1` this reads `a ≥ S + 1` for `S = 2 + r` (used for the `W`-bound) and
  implies `a ≥ 2 = T + 1` (used for the `V`- and `W`-bounds at `T = 1`).  We keep `a` as a
  free parameter and state the side condition as `r + 3 ≤ a`; the paper's `a = √(2M)` is the
  intended specialization.
* Step 3 of the separated-block estimate: the HS factorizations
  `K̃₁ = (U_aQU_aΦ)(Φ⁻¹U_a⁻¹P_{-1}B₀U_a⁻¹)`,
  `K̃₂ = (U_aP_LU_a⁻¹)(U_aQU_aΦ)(Φ⁻¹U_a⁻¹P_{-S}B₀U_a⁻¹)` with `L = r + 1`,
  `C̃_r = A_r·W_{S,a}` with `A_r = U_aQP_rQU_aΦ` and `0 ≤ QP_rQ ≤ QP_L`, and
  `K̃∪ = Ṽ_{D,r}·W_{S,a}` with `Ṽ_{D,r} = U_aD_rU_aΦ`, `0 ≤ D_r ≤ QP_L + P_LQ` (this is also
  the factorization behind the trace-class property of `K̃∪`).
* Inputs: the paper's `V`-bound (`vKernel_sq_integral_le`), `W`-bound
  (`wKernel_sq_integral_le`), conjugated-heat bound (`eLpNorm_conjugateHeat_conv_le`) and
  `UΦ`-bound (infrastructure of `uphi_hs_le`).  Here the `V`- and `W`-bounds are the
  Hilbert–Schmidt bounds for the kernels `V_{T,a}` and `W_{T,a}`, the conjugated-heat bound is
  the `L²` bound for `U_aP_LU_a⁻¹`, and the `UΦ`-bound is the Hilbert–Schmidt bound for
  `U_aQ_{M,T}P_LU_aΦ`.

## Scope

The determinant identities themselves (the paper's two-interval determinant formula and the
one-block formulas of Quastel–Remenik) are not proved here; they enter the main package as
hypothesis records (`ExternalInputs.lean`).  This module proves membership facts only.

## Notes on the proofs

* The trace-class layer (`TraceClass/`) provides `trace_add` / `trace_sub` (linearity of the
  trace functional) and `IsHilbertSchmidt.sub`, but no `IsTraceClass.add`/`IsTraceClass.sub`:
  with the factorization definition `IsTraceClass T := ∃ A B, HS A ∧ HS B ∧ T = A ∘L B` on a
  *fixed* space `E`, sum-closure needs a direct-sum construction (see
  `FredholmDet/TraceClassAdd.lean`).  We therefore prove
  `IsTraceClass (kernelOperator (kcupKerT a M r))` directly from the factorization
  `K̃∪ = Ṽ_{D,r} · W_{S,a}`, via the domination `0 ≤ D_r ≤ QP_L + P_LQ` and the `V`-,
  conjugated-heat and `UΦ` `L²` bounds.  The `MemLp` half for `K̃∪` is done via
  `twoIntKCup_decomp` + `MemLp.add`/`MemLp.sub`.
* `MemLp (aRKer a M r)` (the "A_r is Hilbert–Schmidt" step) is proved at the *kernel* level:
  `uphi_hs_le` is an operator-level enorm bound and there is no HS-operator → `L²`-kernel
  extraction lemma, so we replay the proof of the `UΦ`-bound (the `V`-bound × the Young
  convolution bound for `kUPhi`) to get `MemLp` of the dominating kernel `uphiKer` and
  conclude by domination.  `isHilbertSchmidt_uphiComposite` records the direct corollary of
  `uphi_hs_le` for the operator-level form.
-/

namespace AiryTwoInt

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal InnerProduct InnerProductSpace
open HilbertSchmidt

/-! ## General `L²` kernel machinery -/

/-- The conjugated heat kernel `uConj a (heatKerTwo L)` (the kernel of
`U_a P_L U_a⁻¹`, the conjugated-heat bound) is the convolution kernel
`v ↦ e^{-av} p_L(v)` evaluated at the difference of the arguments. -/
theorem uConj_heatKerTwo_eq (a L : ℝ) (p : ℝ × ℝ) :
    uConj a (heatKerTwo L) p = AiryConj.conjugateHeatKernel L a (p.1 - p.2) := by
  show Real.exp (-a * p.1) * heatKernel L (p.1 - p.2) * Real.exp (a * p.2) = _
  rw [show Real.exp (-a * p.1) * heatKernel L (p.1 - p.2) * Real.exp (a * p.2)
      = (Real.exp (-a * p.1) * Real.exp (a * p.2)) * heatKernel L (p.1 - p.2) from by ring,
    ← Real.exp_add, show -a * p.1 + a * p.2 = -a * (p.1 - p.2) by ring]
  rfl

/-- Square-integrable real functions are `L²` (the one-dimensional companion of
`AiryConj.memLp_of_sq_integrable`). -/
theorem memLp_two_of_sq_integrable {f : ℝ → ℝ} (hf : Measurable f)
    (h2 : Integrable (fun x : ℝ => (f x) ^ 2) volume) :
    MemLp f 2 volume :=
  (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr h2

/-- The conjugated heat kernel `e^{-av} p_L(v)` is in `L²(ℝ)` for `0 < L`: by the
completed square (`conjugateHeatKernel_eq`) it is a constant times a
translated Gaussian. -/
theorem memLp_conjugateHeatKernel_two (hL : 0 < L) (a : ℝ) :
    MemLp (AiryConj.conjugateHeatKernel L a) 2 volume := by
  apply memLp_two_of_sq_integrable
    (AiryConj.continuous_conjugateHeatKernel L a).measurable
  have hbase : Integrable (fun v : ℝ => Real.exp (-((2 * L)⁻¹) * (v - -2 * L * a) ^ 2))
      volume :=
    (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < (2 * L)⁻¹)).comp_sub_right
      (-2 * L * a)
  apply (hbase.const_mul (((4 * Real.pi * L)^(-1/2 : ℝ) * Real.exp (L * a ^ 2)) ^ 2)).congr
  filter_upwards with v
  rw [AiryConj.conjugateHeatKernel_eq hL a v]
  have hE : (Real.exp (-(v + 2 * L * a) ^ 2 / (4 * L))) ^ 2
      = Real.exp (-((2 * L)⁻¹) * (v - -2 * L * a) ^ 2) := by
    rw [show (Real.exp (-(v + 2 * L * a) ^ 2 / (4 * L))) ^ 2
        = Real.exp (-(v + 2 * L * a) ^ 2 / (4 * L))
          * Real.exp (-(v + 2 * L * a) ^ 2 / (4 * L)) from pow_two _,
      ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [mul_pow, mul_pow, hE]
  ring

/-- For a.e. `x`, the second-variable slice `z ↦ K (x, z)` of a product-`L²` kernel is
in `L²(ℝ)` (the real-valued case of the `memLp_conj_slice_ae`). -/
theorem memLp_slice_snd_ae {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume)) :
    ∀ᵐ x : ℝ ∂volume, MemLp (fun z : ℝ => K (x, z)) 2 volume := by
  filter_upwards [HilbertSchmidt.memLp_conj_slice_ae hK] with x hx
  have : (fun z : ℝ => star (K (x, z))) = fun z => K (x, z) := funext fun z => star_trivial _
  rwa [this] at hx

/-- For a.e. `y`, the first-variable slice `z ↦ G (z, y)` of a product-`L²` kernel is
in `L²(ℝ)` (via the kernel flip). -/
theorem memLp_slice_fst_ae {G : ℝ × ℝ → ℝ} (hG : MemLp G 2 (volume.prod volume)) :
    ∀ᵐ y : ℝ ∂volume, MemLp (fun z : ℝ => G (z, y)) 2 volume := by
  filter_upwards [HilbertSchmidt.memLp_conj_slice_ae (AiryConj.memLp_kernelFlip hG)]
    with y hy
  have : (fun z : ℝ => star (AiryConj.kernelFlip G (y, z))) = fun z => G (z, y) :=
    funext fun z => by simp [AiryConj.kernelFlip, star_trivial]
  rwa [this] at hy

/-- **The composite of two `L²(ℝ²)` kernels is `L²(ℝ²)`** (Cauchy–Schwarz on each
slice, then Tonelli): the kernel-level form of "Hilbert–Schmidt ∘ Hilbert–Schmidt is
Hilbert–Schmidt", with `‖compKernel K K'‖₂ ≤ ‖K‖₂ · ‖K'‖₂`. -/
theorem memLp_compKernel {K K' : ℝ × ℝ → ℝ} (hKmeas : Measurable K) (hK'meas : Measurable K')
    (hK : MemLp K 2 (volume.prod volume)) (hK' : MemLp K' 2 (volume.prod volume)) :
    MemLp (AiryConj.compKernel K K') 2 (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (AiryConj.compKernel K K') (volume.prod volume) :=
    (measurable_compKernel hKmeas hK'meas).aestronglyMeasurable
  -- pointwise Cauchy–Schwarz bound on the enorm of the composite kernel
  have hpt : ∀ p : ℝ × ℝ, ‖AiryConj.compKernel K K' p‖ₑ
      ≤ (∫⁻ z : ℝ, ‖K (p.1, z)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)
        * (∫⁻ z : ℝ, ‖K' (z, p.2)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) := by
    intro p
    calc ‖AiryConj.compKernel K K' p‖ₑ
        = ‖∫ z : ℝ, K (p.1, z) * K' (z, p.2)‖ₑ := rfl
      _ ≤ ∫⁻ z : ℝ, ‖K (p.1, z) * K' (z, p.2)‖ₑ ∂volume :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ z : ℝ, ‖K (p.1, z)‖ₑ * ‖K' (z, p.2)‖ₑ ∂volume :=
          lintegral_congr fun z => enorm_mul _ _
      _ ≤ (∫⁻ z : ℝ, ‖K (p.1, z)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)
          * (∫⁻ z : ℝ, ‖K' (z, p.2)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
            ((hKmeas.comp (continuous_const.prodMk continuous_id).measurable).enorm.aemeasurable)
            ((hK'meas.comp (continuous_id.prodMk continuous_const).measurable).enorm.aemeasurable)
  -- squaring and integrating: Tonelli separates the two factors
  have hKn : AEMeasurable (fun p : ℝ × ℝ => ‖K p‖ₑ ^ (2:ℝ)) (volume.prod volume) :=
    (hKmeas.enorm.pow_const (2:ℝ)).aemeasurable
  have hK'f : MemLp (AiryConj.kernelFlip K') 2 (volume.prod volume) :=
    AiryConj.memLp_kernelFlip hK'
  have hK'fn : AEMeasurable (fun p : ℝ × ℝ => ‖AiryConj.kernelFlip K' p‖ₑ ^ (2:ℝ))
      (volume.prod volume) := (hK'f.aestronglyMeasurable.enorm).pow_const (2:ℝ)
  have hfin : (∫⁻ p : ℝ × ℝ, ‖AiryConj.compKernel K K' p‖ₑ ^ (2:ℝ) ∂(volume.prod volume))
      < ⊤ := by
    calc (∫⁻ p : ℝ × ℝ, ‖AiryConj.compKernel K K' p‖ₑ ^ (2:ℝ) ∂(volume.prod volume))
        ≤ ∫⁻ p : ℝ × ℝ, ((∫⁻ z : ℝ, ‖K (p.1, z)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)
            * (∫⁻ z : ℝ, ‖K' (z, p.2)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)) ^ (2:ℝ)
            ∂(volume.prod volume) :=
          lintegral_mono fun p => ENNReal.rpow_le_rpow (hpt p) (by norm_num)
      _ = ∫⁻ p : ℝ × ℝ, (∫⁻ z : ℝ, ‖K (p.1, z)‖ₑ ^ (2:ℝ) ∂volume)
            * (∫⁻ z : ℝ, ‖K' (z, p.2)‖ₑ ^ (2:ℝ) ∂volume) ∂(volume.prod volume) :=
          lintegral_congr fun p => by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
              ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, show (1/2 : ℝ) * 2 = 1 by norm_num,
              ENNReal.rpow_one, ENNReal.rpow_one]
      _ = (∫⁻ x : ℝ, ∫⁻ z : ℝ, ‖K (x, z)‖ₑ ^ (2:ℝ) ∂volume ∂volume)
            * (∫⁻ y : ℝ, ∫⁻ z : ℝ, ‖AiryConj.kernelFlip K' (y, z)‖ₑ ^ (2:ℝ) ∂volume
              ∂volume) :=
          MeasureTheory.lintegral_prod_mul hKn.lintegral_prod_right'
            hK'fn.lintegral_prod_right'
      _ = (∫⁻ p : ℝ × ℝ, ‖K p‖ₑ ^ (2:ℝ) ∂(volume.prod volume))
            * (∫⁻ p : ℝ × ℝ, ‖AiryConj.kernelFlip K' p‖ₑ ^ (2:ℝ) ∂(volume.prod volume)) := by
            congr 1
            · exact (MeasureTheory.lintegral_prod _ hKn).symm
            · exact (MeasureTheory.lintegral_prod _ hK'fn).symm
      _ < ⊤ := by
          rw [show (∫⁻ p : ℝ × ℝ, ‖K p‖ₑ ^ (2:ℝ) ∂(volume.prod volume))
              = (eLpNorm K 2 (volume.prod volume)) ^ 2 from by
            rw [lintegral_congr fun p => enorm_rpow_two _,
              MeasureTheory.eLpNorm_two_sq_eq_lintegral hK.aestronglyMeasurable],
            show (∫⁻ p : ℝ × ℝ, ‖AiryConj.kernelFlip K' p‖ₑ ^ (2:ℝ) ∂(volume.prod volume))
              = (eLpNorm (AiryConj.kernelFlip K') 2 (volume.prod volume)) ^ 2 from by
            rw [lintegral_congr fun p => enorm_rpow_two _,
              MeasureTheory.eLpNorm_two_sq_eq_lintegral hK'f.aestronglyMeasurable]]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hK.eLpNorm_lt_top)
            (ENNReal.pow_lt_top hK'f.eLpNorm_lt_top)
  -- conclude
  rw [MeasureTheory.memLp_iff,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmeas]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

/-! ## The conjugated heat operator as a CLM (packaging the conjugated-heat bound)

The lemma `eLpNorm_conjugateHeat_conv_le` (the conjugated-heat bound) is a
function-level bound; here we package it as a continuous linear map on `L²(ℝ)`,
following the `bPhiCLM` pattern of `AiryKernel/ConjugateUPhi.lean`. -/

/-- The pointwise action of the conjugated heat operator `U_a P_L U_a⁻¹`
(the conjugated-heat bound): `x ↦ ∫ z, e^{-a(x-z)} p_L(x−z) · f z`. -/
noncomputable def conjHeatApply (L a : ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) (x : ℝ) : ℝ :=
  ∫ z : ℝ, AiryConj.conjugateHeatKernel L a (x - z) * f z

/-- The section `z ↦ e^{-a(x-z)} p_L(x−z) f(z)` is integrable for `f ∈ L²(ℝ)`
(the conjugated kernel is in `L²`, `memLp_conjugateHeatKernel_two`; Cauchy–Schwarz). -/
theorem integrable_conjHeatApply_section (hL : 0 < L) (a : ℝ)
    (f : Lp ℝ 2 (volume : Measure ℝ)) (x : ℝ) :
    Integrable (fun z : ℝ => AiryConj.conjugateHeatKernel L a (x - z) * f z) volume := by
  have hk2 : MemLp (fun z : ℝ => AiryConj.conjugateHeatKernel L a (x - z)) 2 volume :=
    (memLp_conjugateHeatKernel_two hL a).comp_measurePreserving
      (MeasureTheory.Measure.measurePreserving_sub_left volume x)
  exact MemLp.integrable_mul hk2 (Lp.memLp f)

/-- The pointwise action is the convolution with `k(v) = e^{-av} p_L(v)`:
`∫ z, k(x−z) f(z) = (k ⋆ f)(x)` (translation invariance of Lebesgue measure). -/
theorem conjHeatApply_eq_convolution (L a : ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) (x : ℝ) :
    conjHeatApply L a f x
      = MeasureTheory.convolution (AiryConj.conjugateHeatKernel L a) (fun z => f z)
          (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  show (∫ z : ℝ, AiryConj.conjugateHeatKernel L a (x - z) * f z) = _
  rw [MeasureTheory.convolution_mul]
  have key := MeasureTheory.integral_sub_left_eq_self
    (fun t : ℝ => AiryConj.conjugateHeatKernel L a t * f (x - t)) volume x
  simp only [sub_sub_self] at key
  exact key

/-- The pointwise action lands in `L²(ℝ)` (the membership half of the conjugated-heat bound). -/
theorem memLp_conjHeatApply (hL : 0 < L) (a : ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    MemLp (conjHeatApply L a f) 2 volume := by
  have h := (AiryConj.eLpNorm_conjugateHeat_conv_le hL a (fun z => f z) (Lp.memLp f)).1
  rw [show conjHeatApply L a f = fun x => MeasureTheory.convolution
      (AiryConj.conjugateHeatKernel L a) (fun z => f z) (ContinuousLinearMap.mul ℝ ℝ)
        volume x
    from funext fun x => conjHeatApply_eq_convolution L a f x]
  exact h

/-- The `L²` operator bound for the pointwise action (the conjugated-heat bound):
`‖x ↦ ∫ z, e^{-a(x-z)}p_L(x−z) f(z)‖₂ ≤ e^{L a²} ‖f‖₂`. -/
theorem eLpNorm_conjHeatApply_le (hL : 0 < L) (a : ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    eLpNorm (conjHeatApply L a f) 2 volume
      ≤ ENNReal.ofReal (Real.exp (L * a ^ 2)) * eLpNorm f 2 volume := by
  have h := (AiryConj.eLpNorm_conjugateHeat_conv_le hL a (fun z => f z) (Lp.memLp f)).2
  rwa [eLpNorm_congr_ae (Eventually.of_forall fun x => conjHeatApply_eq_convolution L a f x)]

/-- The conjugated heat operator `U_a P_L U_a⁻¹` as a continuous linear map on `L²(ℝ)`
(the conjugated-heat bound), packaged by `LinearMap.mkContinuous` with
operator-norm bound `e^{L a²}` (`integral_conjugateHeatKernel`). -/
noncomputable def conjHeatCLM (L : ℝ) (hL : 0 < L) (a : ℝ) :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => MemLp.toLp _ (memLp_conjHeatApply hL a f)
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_conjHeatApply hL a (f + g)),
          MemLp.coeFn_toLp (memLp_conjHeatApply hL a f),
          MemLp.coeFn_toLp (memLp_conjHeatApply hL a g),
          Lp.coeFn_add (MemLp.toLp _ (memLp_conjHeatApply hL a f))
            (MemLp.toLp _ (memLp_conjHeatApply hL a g))] with x hfg hf hg hadd
        rw [hfg, hadd, Pi.add_apply, hf, hg]
        show (∫ z : ℝ, AiryConj.conjugateHeatKernel L a (x - z) * (f + g) z)
          = (∫ z : ℝ, AiryConj.conjugateHeatKernel L a (x - z) * f z)
            + ∫ z : ℝ, AiryConj.conjugateHeatKernel L a (x - z) * g z
        rw [← integral_add (integrable_conjHeatApply_section hL a f x)
          (integrable_conjHeatApply_section hL a g x)]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with z hz
        rw [hz, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_conjHeatApply hL a (c • f)),
          MemLp.coeFn_toLp (memLp_conjHeatApply hL a f),
          Lp.coeFn_smul c (MemLp.toLp _ (memLp_conjHeatApply hL a f))] with x hcf hf hsmul
        rw [hcf, RingHom.id_apply, hsmul, Pi.smul_apply, hf, smul_eq_mul]
        show (∫ z : ℝ, AiryConj.conjugateHeatKernel L a (x - z) * (c • f) z)
          = c * ∫ z : ℝ, AiryConj.conjugateHeatKernel L a (x - z) * f z
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with z hz
        rw [hz, Pi.smul_apply, smul_eq_mul]
        ring }
    (Real.exp (L * a ^ 2))
    (fun f => by
      have hb := eLpNorm_conjHeatApply_le hL a f
      have hfin : ENNReal.ofReal (Real.exp (L * a ^ 2)) * eLpNorm f 2 volume ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)
      calc ‖MemLp.toLp _ (memLp_conjHeatApply hL a f)‖
          = (eLpNorm (conjHeatApply L a f) 2 volume).toReal := by
            rw [Lp.norm_def]
            congr 1
            exact eLpNorm_congr_ae (MemLp.coeFn_toLp _)
        _ ≤ (ENNReal.ofReal (Real.exp (L * a ^ 2)) * eLpNorm f 2 volume).toReal :=
            ENNReal.toReal_mono hfin hb
        _ = Real.exp (L * a ^ 2) * (eLpNorm f 2 volume).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
        _ = Real.exp (L * a ^ 2) * ‖f‖ := by rw [Lp.norm_def])

/-- The action of `conjHeatCLM` is a.e. the pointwise kernel integral. -/
theorem conjHeatCLM_apply_ae (L : ℝ) (hL : 0 < L) (a : ℝ)
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ∀ᵐ x : ℝ ∂volume, (conjHeatCLM L hL a f) x = conjHeatApply L a f x := by
  have h : conjHeatCLM L hL a f = MemLp.toLp _ (memLp_conjHeatApply hL a f) := rfl
  rw [h]
  exact MemLp.coeFn_toLp _

/-- The operator-norm bound for `conjHeatCLM` (the conjugated-heat bound):
`‖U_a P_L U_a⁻¹‖ₑ ≤ ofReal (e^{L a²})`. -/
theorem enorm_conjHeatCLM_le (L : ℝ) (hL : 0 < L) (a : ℝ) :
    ‖conjHeatCLM L hL a‖ₑ ≤ ENNReal.ofReal (Real.exp (L * a ^ 2)) := by
  apply ContinuousLinearMap.opENorm_le_bound
  intro f
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (conjHeatCLM_apply_ae L hL a f)]
  exact eLpNorm_conjHeatApply_le hL a f

/-- Pointwise convolution form of the left-conjugated-heat composite kernel:
`compKernel (uConj a (heatKerTwo L)) G (x, y) = (k_a ⋆ G(·, y))(x)`. -/
theorem compKernel_uConjHeat_eq_convolution (a L x y : ℝ) (G : ℝ × ℝ → ℝ) :
    AiryConj.compKernel (uConj a (heatKerTwo L)) G (x, y)
      = MeasureTheory.convolution (AiryConj.conjugateHeatKernel L a) (fun z => G (z, y))
          (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  show (∫ z : ℝ, uConj a (heatKerTwo L) (x, z) * G (z, y)) = _
  rw [show (fun z : ℝ => uConj a (heatKerTwo L) (x, z) * G (z, y))
      = fun z => AiryConj.conjugateHeatKernel L a (x - z) * G (z, y) from
    funext fun z => by rw [uConj_heatKerTwo_eq]]
  rw [MeasureTheory.convolution_mul]
  have key := MeasureTheory.integral_sub_left_eq_self
    (fun t : ℝ => AiryConj.conjugateHeatKernel L a t * G (x - t, y)) volume x
  simp only [sub_sub_self] at key
  exact key

/-- The Fubini input for the left-conjugated-heat operator identity: for every `x`,
the integrand `(z, y) ↦ k_a(x−z) · G (z, y) · f y` is jointly integrable on `ℝ²`
(Hölder first in `y` against the `L²`-slice of `G`, then in `z` against the slice-norm
function of `G`, whose `L²`-norm is `eLpNorm G 2 (volume.prod volume)`). -/
theorem integrable_uConjHeat_mul (hL : 0 < L) (a : ℝ) {G : ℝ × ℝ → ℝ}
    (hG : MemLp G 2 (volume.prod volume)) (f : Lp ℝ 2 (volume : Measure ℝ)) (x : ℝ) :
    Integrable (Function.uncurry fun z y : ℝ =>
        AiryConj.conjugateHeatKernel L a (x - z) * (G (z, y) * f y))
      (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun z y : ℝ =>
        AiryConj.conjugateHeatKernel L a (x - z) * (G (z, y) * f y))
      (volume.prod volume) :=
    ((((AiryConj.continuous_conjugateHeatKernel L a).comp
        (continuous_const.sub continuous_fst)).aestronglyMeasurable).mul
      (hG.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f).comp_snd))
  refine ⟨hmeas, ?_⟩
  -- the slice-norm function `g2 z := (∫⁻ y, ‖G (z, y)‖ₑ ^ 2)^{1/2}`
  set g2 : ℝ → ℝ≥0∞ := fun z => (∫⁻ y : ℝ, ‖G (z, y)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) with hg2
  have hGnorm : AEMeasurable (fun p : ℝ × ℝ => ‖G p‖ₑ ^ (2:ℝ)) (volume.prod volume) :=
    (hG.aestronglyMeasurable.enorm).pow_const (2:ℝ)
  have hG2 : AEMeasurable g2 volume :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hGnorm.lintegral_prod_right'
  have hf2 : (∫⁻ y : ℝ, ‖f y‖ₑ ^ (2:ℝ) ∂volume) < ⊤ := by
    rw [lintegral_congr fun y => enorm_rpow_two _,
      ← MeasureTheory.eLpNorm_two_sq_eq_lintegral (Lp.aestronglyMeasurable f)]
    exact ENNReal.pow_lt_top (Lp.eLpNorm_lt_top f)
  have hGfin : (∫⁻ p : ℝ × ℝ, ‖G p‖ₑ ^ (2:ℝ) ∂(volume.prod volume)) < ⊤ := by
    rw [lintegral_congr fun p => enorm_rpow_two _,
      ← MeasureTheory.eLpNorm_two_sq_eq_lintegral hG.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hG.eLpNorm_lt_top
  have hGslice : ∀ᵐ z : ℝ ∂volume, AEMeasurable (fun y : ℝ => ‖G (z, y)‖ₑ) volume := by
    filter_upwards [AEStronglyMeasurable.prodMk_left hG.aestronglyMeasurable] with z hz
    exact hz.enorm
  have hk2 : AEMeasurable (fun z : ℝ => ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ)
      volume :=
    (((AiryConj.continuous_conjugateHeatKernel L a).comp
      (continuous_const.sub continuous_id)).measurable.enorm).aemeasurable
  -- the inner Hölder step (in `y`, for a.e. `z`)
  have hstep : ∀ᵐ z : ℝ ∂volume, ∫⁻ y : ℝ, ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ
        * (‖G (z, y)‖ₑ * ‖f y‖ₑ) ∂volume
      ≤ ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ * (g2 z
        * (∫⁻ y : ℝ, ‖f y‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)) := by
    filter_upwards [hGslice] with z hz
    have hholder : (∫⁻ y : ℝ, ‖G (z, y)‖ₑ * ‖f y‖ₑ ∂volume)
        ≤ (∫⁻ y : ℝ, (‖G (z, y)‖ₑ) ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)
          * (∫⁻ y : ℝ, (‖f y‖ₑ) ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hz
        (Lp.aestronglyMeasurable f).enorm
    calc ∫⁻ y : ℝ, ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ * (‖G (z, y)‖ₑ * ‖f y‖ₑ)
        = ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ
          * ∫⁻ y : ℝ, ‖G (z, y)‖ₑ * ‖f y‖ₑ ∂volume :=
          lintegral_const_mul'' _ (hz.mul (Lp.aestronglyMeasurable f).enorm)
      _ ≤ ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ
          * ((∫⁻ y : ℝ, (‖G (z, y)‖ₑ) ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)
            * (∫⁻ y : ℝ, (‖f y‖ₑ) ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)) :=
          mul_le_mul_of_nonneg_left hholder bot_le
      _ = ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ * (g2 z
          * (∫⁻ y : ℝ, ‖f y‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)) := rfl
  -- the outer Hölder step (in `z`)
  have hout : (∫⁻ z : ℝ, ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ * (g2 z
        * (∫⁻ y : ℝ, ‖f y‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)) ∂volume)
      ≤ ((∫⁻ z : ℝ, (‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ) ^ (2:ℝ) ∂volume)
          ^ (1/2:ℝ))
        * ((∫⁻ z : ℝ, (g2 z) ^ (2:ℝ) ∂volume) ^ (1/2:ℝ))
        * (∫⁻ y : ℝ, ‖f y‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) := by
    have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
      hk2 hG2
    calc (∫⁻ z : ℝ, ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ * (g2 z
            * (∫⁻ y : ℝ, ‖f y‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)) ∂volume)
        = (∫⁻ y : ℝ, ‖f y‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)
          * ∫⁻ z : ℝ, ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ * g2 z ∂volume := by
          rw [show (fun z : ℝ => ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ * (g2 z
                * (∫⁻ y : ℝ, ‖f y‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)))
              = fun z => (∫⁻ y : ℝ, ‖f y‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)
                * (‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ * g2 z) from
            funext fun z => by ring]
          rw [lintegral_const_mul'' _
            (show AEMeasurable (fun z : ℝ =>
                ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ * g2 z) volume from
              hk2.mul hG2)]
      _ ≤ (∫⁻ y : ℝ, ‖f y‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)
          * ((∫⁻ z : ℝ, (‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ) ^ (2:ℝ) ∂volume)
              ^ (1/2:ℝ)
            * (∫⁻ z : ℝ, (g2 z) ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)) :=
          mul_le_mul_of_nonneg_left hholder bot_le
      _ = _ := by ring
  -- finiteness of the outer bound
  have hkfin : (∫⁻ z : ℝ, (‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ) ^ (2:ℝ) ∂volume)
      = ∫⁻ z : ℝ, (‖AiryConj.conjugateHeatKernel L a z‖ₑ) ^ (2:ℝ) ∂volume := by
    exact MeasureTheory.lintegral_sub_left_eq_self
      (fun z : ℝ => (‖AiryConj.conjugateHeatKernel L a z‖ₑ) ^ (2:ℝ)) x
  have hkg2fin : (∫⁻ z : ℝ, (‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ) ^ (2:ℝ) ∂volume)
        < ⊤ := by
    rw [hkfin, lintegral_congr fun z => enorm_rpow_two _,
      ← MeasureTheory.eLpNorm_two_sq_eq_lintegral
        (AiryConj.continuous_conjugateHeatKernel L a).aestronglyMeasurable]
    exact ENNReal.pow_lt_top (memLp_conjugateHeatKernel_two hL a).eLpNorm_lt_top
  have hg2fin : (∫⁻ z : ℝ, (g2 z) ^ (2:ℝ) ∂volume) < ⊤ := by
    rw [lintegral_congr fun z => by
        rw [hg2, ← ENNReal.rpow_mul, show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]]
    rw [← MeasureTheory.lintegral_prod _ hGnorm]
    exact hGfin
  calc (∫⁻ p : ℝ × ℝ, ‖Function.uncurry (fun z y : ℝ =>
          AiryConj.conjugateHeatKernel L a (x - z) * (G (z, y) * f y)) p‖ₑ
          ∂(volume.prod volume))
      = ∫⁻ z : ℝ, ∫⁻ y : ℝ, ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ
          * (‖G (z, y)‖ₑ * ‖f y‖ₑ) ∂volume ∂volume := by
        rw [MeasureTheory.lintegral_prod _ hmeas.enorm]
        apply lintegral_congr; intro z
        apply lintegral_congr; intro y
        show ‖AiryConj.conjugateHeatKernel L a (x - z) * (G (z, y) * f y)‖ₑ = _
        rw [enorm_mul, enorm_mul]
    _ ≤ ∫⁻ z : ℝ, ‖AiryConj.conjugateHeatKernel L a (x - z)‖ₑ * (g2 z
          * (∫⁻ y : ℝ, ‖f y‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)) ∂volume :=
        lintegral_mono_ae hstep
    _ ≤ _ := hout
    _ < ⊤ := by
        apply ENNReal.mul_lt_top (ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hkg2fin.ne)
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hg2fin.ne))
        exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hf2.ne

/-- **The operator of `compKernel (uConj a (heatKerTwo L)) G` is the composition
`conjHeatCLM ∘L kernelOperator G`** (a.e. Fubini via `integrable_uConjHeat_mul`):
the kernel-level form of the `(U_aP_LU_a⁻¹) ∘ (HS)` compositions
and. -/
theorem kernelOperator_compKernel_uConjHeat (hL : 0 < L) (a : ℝ) {G : ℝ × ℝ → ℝ}
    (hG : MemLp G 2 (volume.prod volume))
    (hcomp : MemLp (AiryConj.compKernel (uConj a (heatKerTwo L)) G) 2 (volume.prod volume)) :
    kernelOperator hcomp = conjHeatCLM L hL a ∘L kernelOperator hG := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae hcomp f,
    conjHeatCLM_apply_ae L hL a (kernelOperator hG f)] with x hxcomp hxCLM
  rw [ContinuousLinearMap.comp_apply, hxcomp, hxCLM]
  show (∫ y : ℝ, AiryConj.compKernel (uConj a (heatKerTwo L)) G (x, y) * f y)
    = conjHeatApply L a (kernelOperator hG f) x
  calc (∫ y : ℝ, AiryConj.compKernel (uConj a (heatKerTwo L)) G (x, y) * f y)
      = ∫ y : ℝ, ∫ z : ℝ, AiryConj.conjugateHeatKernel L a (x - z) * (G (z, y) * f y) := by
        apply integral_congr_ae
        filter_upwards with y
        show (∫ z : ℝ, uConj a (heatKerTwo L) (x, z) * G (z, y)) * f y = _
        rw [show (fun z : ℝ => uConj a (heatKerTwo L) (x, z) * G (z, y))
            = fun z => AiryConj.conjugateHeatKernel L a (x - z) * G (z, y) from
          funext fun z => by rw [uConj_heatKerTwo_eq]]
        rw [← MeasureTheory.integral_mul_const]
        apply integral_congr_ae
        filter_upwards with z
        ring
    _ = ∫ z : ℝ, ∫ y : ℝ, AiryConj.conjugateHeatKernel L a (x - z) * (G (z, y) * f y) := by
        exact (MeasureTheory.integral_integral_swap
          (f := fun z y : ℝ => AiryConj.conjugateHeatKernel L a (x - z) * (G (z, y) * f y))
          (integrable_uConjHeat_mul hL a hG f x)).symm
    _ = ∫ z : ℝ, AiryConj.conjugateHeatKernel L a (x - z)
          * (∫ y : ℝ, G (z, y) * f y) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [integral_const_mul]
    _ = ∫ z : ℝ, AiryConj.conjugateHeatKernel L a (x - z) * (kernelOperator hG f) z := by
        apply integral_congr_ae
        filter_upwards [kernelOperator_apply_ae hG f] with z hz
        rw [hz]
        rfl

/-- **The kernel of `(U_aP_LU_a⁻¹) ∘ T_G` is `L²(ℝ²)`** for `G ∈ L²(ℝ²)`: the conjugated-heat bound
applied slice-by-slice in the second variable, then Tonelli
(`‖compKernel (uConj a (heatKerTwo L)) G‖₂ ≤ e^{La²} ‖G‖₂`).  This is the membership
half of the `(U_aP_LU_a⁻¹)·(HS)` estimates and. -/
theorem memLp_compKernel_uConjHeat (hL : 0 < L) (a : ℝ) {G : ℝ × ℝ → ℝ}
    (hGmeas : Measurable G) (hG : MemLp G 2 (volume.prod volume)) :
    MemLp (AiryConj.compKernel (uConj a (heatKerTwo L)) G) 2 (volume.prod volume) := by
  have hcompmeas : Measurable (AiryConj.compKernel (uConj a (heatKerTwo L)) G) :=
    measurable_compKernel (measurable_uConj a (measurable_heatKerTwo L)) hGmeas
  rw [MeasureTheory.memLp_iff,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hcompmeas.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  -- the slice bound: for a.e. `y`, the `x`-slice norm is bounded by the conjugated-heat bound
  have hsq : ∀ᵐ y : ℝ ∂volume,
      (∫⁻ x : ℝ, ‖AiryConj.compKernel (uConj a (heatKerTwo L)) G (x, y)‖ₑ ^ (2:ℝ) ∂volume)
        ≤ (ENNReal.ofReal (Real.exp (L * a ^ 2))) ^ (2:ℝ)
          * (∫⁻ z : ℝ, ‖G (z, y)‖ₑ ^ (2:ℝ) ∂volume) := by
    filter_upwards [memLp_slice_fst_ae hG] with y hy
    have hconv := (AiryConj.eLpNorm_conjugateHeat_conv_le hL a (fun z => G (z, y)) hy).2
    have heq : (fun x : ℝ => AiryConj.compKernel (uConj a (heatKerTwo L)) G (x, y))
        = fun x => MeasureTheory.convolution (AiryConj.conjugateHeatKernel L a)
            (fun z => G (z, y)) (ContinuousLinearMap.mul ℝ ℝ) volume x :=
      funext fun x => compKernel_uConjHeat_eq_convolution a L x y G
    have hslice : AEStronglyMeasurable
        (fun x : ℝ => AiryConj.compKernel (uConj a (heatKerTwo L)) G (x, y)) volume :=
      (hcompmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    have hA : (eLpNorm (fun x : ℝ => AiryConj.compKernel (uConj a (heatKerTwo L)) G (x, y))
          2 volume) ^ (2:ℝ)
        = ∫⁻ x : ℝ, ‖AiryConj.compKernel (uConj a (heatKerTwo L)) G (x, y)‖ₑ ^ (2:ℝ)
          ∂volume := by
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          hslice, ENNReal.toReal_ofNat, ← ENNReal.rpow_mul,
        show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    have hB : (ENNReal.ofReal (Real.exp (L * a ^ 2)) * eLpNorm (fun z => G (z, y)) 2 volume)
          ^ (2:ℝ)
        = (ENNReal.ofReal (Real.exp (L * a ^ 2))) ^ (2:ℝ)
          * (∫⁻ z : ℝ, ‖G (z, y)‖ₑ ^ (2:ℝ) ∂volume) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          hy.aestronglyMeasurable, ENNReal.toReal_ofNat, ← ENNReal.rpow_mul,
        show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    rw [← hA, heq, ← hB]
    exact ENNReal.rpow_le_rpow hconv (by norm_num)
  -- integrate the slice bound over `y` and close by Tonelli
  have hGnorm : AEMeasurable (fun p : ℝ × ℝ => ‖G p‖ₑ ^ (2:ℝ)) (volume.prod volume) :=
    (hG.aestronglyMeasurable.enorm).pow_const (2:ℝ)
  have hGnorm2 : AEMeasurable (fun p : ℝ × ℝ => ‖G p‖ₑ ^ 2) (volume.prod volume) :=
    (hG.aestronglyMeasurable.enorm).pow_const (2 : ℕ)
  have hG2prod : (∫⁻ y : ℝ, ∫⁻ z : ℝ, ‖G (z, y)‖ₑ ^ (2:ℝ) ∂volume ∂volume)
      = (eLpNorm G 2 (volume.prod volume)) ^ (2:ℝ) := by
    rw [lintegral_congr fun y => lintegral_congr fun z => enorm_rpow_two _,
      MeasureTheory.lintegral_lintegral_swap
        (show AEMeasurable (Function.uncurry fun y z : ℝ => ‖G (z, y)‖ₑ ^ 2)
          (volume.prod volume) from
          hGnorm2.comp_quasiMeasurePreserving
            (MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving)),
      ← MeasureTheory.lintegral_prod _ hGnorm2,
      ← MeasureTheory.eLpNorm_two_sq_eq_lintegral hG.aestronglyMeasurable]
    exact (enorm_rpow_two _).symm
  have hfin : (∫⁻ p : ℝ × ℝ,
        ‖AiryConj.compKernel (uConj a (heatKerTwo L)) G p‖ₑ ^ (2:ℝ) ∂(volume.prod volume))
      ≤ (ENNReal.ofReal (Real.exp (L * a ^ 2)) * eLpNorm G 2 (volume.prod volume))
        ^ (2:ℝ) := by
    calc (∫⁻ p : ℝ × ℝ, ‖AiryConj.compKernel (uConj a (heatKerTwo L)) G p‖ₑ ^ (2:ℝ)
            ∂(volume.prod volume))
        = ∫⁻ y : ℝ, ∫⁻ x : ℝ,
            ‖AiryConj.compKernel (uConj a (heatKerTwo L)) G (x, y)‖ₑ ^ (2:ℝ) ∂volume
            ∂volume := by
          rw [MeasureTheory.lintegral_prod _
            (hcompmeas.enorm.pow_const (2:ℝ)).aemeasurable]
          exact MeasureTheory.lintegral_lintegral_swap
            (hcompmeas.enorm.pow_const (2:ℝ)).aemeasurable
      _ ≤ ∫⁻ y : ℝ, (ENNReal.ofReal (Real.exp (L * a ^ 2))) ^ (2:ℝ)
            * (∫⁻ z : ℝ, ‖G (z, y)‖ₑ ^ (2:ℝ) ∂volume) ∂volume :=
          lintegral_mono_ae hsq
      _ = (ENNReal.ofReal (Real.exp (L * a ^ 2))) ^ (2:ℝ)
            * (∫⁻ y : ℝ, ∫⁻ z : ℝ, ‖G (z, y)‖ₑ ^ (2:ℝ) ∂volume ∂volume) :=
          lintegral_const_mul'' _ hGnorm.lintegral_prod_left'
      _ = (ENNReal.ofReal (Real.exp (L * a ^ 2)) * eLpNorm G 2 (volume.prod volume))
            ^ (2:ℝ) := by
          rw [hG2prod, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  exact (hfin.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.eLpNorm_ne_top))).ne

/-! ## The right-`ℬ_{L,a}` composite kernel (kernel-level membership for the `UΦ`-bound)

The lemma `uphi_hs_le` (the `UΦ`-bound) is an operator-level enorm bound;
for the kernel membership we replay its proof content: `|ℬ(z, w)| ≤ k(z − w)`
(`bPhiKernel_abs_le`) with `k = kUPhi` integrable, so by Young the
composite kernel `compKernel V (bPhiKernel L a)` of an `L²` kernel `V` with `ℬ` is again
`L²`, with `‖·‖₂ ≤ ‖k‖₁ · ‖V‖₂`. -/

/-- **The composite kernel of an `L²(ℝ²)` kernel with `bPhiKernel` is `L²(ℝ²)`**:
slice-by-slice Young (`eLpNorm_conv_le`, the generic form behind the conjugated-heat bound and
the `UΦ`-bound) in the second variable, then Tonelli. -/
theorem memLp_compKernel_bPhi (hL : 0 < L) (a : ℝ) {V : ℝ × ℝ → ℝ}
    (hVmeas : Measurable V) (hV : MemLp V 2 (volume.prod volume)) :
    MemLp (AiryConj.compKernel V (AiryConj.bPhiKernel L a)) 2 (volume.prod volume) := by
  have hcompmeas : Measurable (AiryConj.compKernel V (AiryConj.bPhiKernel L a)) :=
    measurable_compKernel hVmeas (AiryConj.measurable_bPhiKernel L a)
  rw [MeasureTheory.memLp_iff,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hcompmeas.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  -- the flipped dominating kernel `k̃ v := k (−v)`, integrable with `∫ k̃ = ∫ k`
  have hkTint : Integrable (fun v : ℝ => AiryConj.kUPhi L a (-v)) volume :=
    (AiryConj.integrable_kUPhi hL a).comp_neg
  have hkTmeas : AEStronglyMeasurable (fun v : ℝ => AiryConj.kUPhi L a (-v)) volume :=
    ((AiryConj.continuous_kUPhi L a).comp continuous_neg).aestronglyMeasurable
  have hkTnn : ∀ v : ℝ, 0 ≤ AiryConj.kUPhi L a (-v) := fun v => AiryConj.kUPhi_nonneg hL a _
  have hkTint_eval : (∫ v : ℝ, AiryConj.kUPhi L a (-v)) = ∫ v : ℝ, AiryConj.kUPhi L a v :=
    MeasureTheory.integral_neg_eq_self (AiryConj.kUPhi L a) volume
  have hVnorm : AEMeasurable (fun p : ℝ × ℝ => ‖V p‖ₑ ^ (2:ℝ)) (volume.prod volume) :=
    (hVmeas.enorm.pow_const (2:ℝ)).aemeasurable
  -- the slice bound: for a.e. `x` (those with `V (x, ·) ∈ L²`), Young in `w`
  have hsq : ∀ᵐ x : ℝ ∂volume,
      (∫⁻ w : ℝ, ‖AiryConj.compKernel V (AiryConj.bPhiKernel L a) (x, w)‖ₑ ^ (2:ℝ) ∂volume)
        ≤ (ENNReal.ofReal (∫ v : ℝ, AiryConj.kUPhi L a v)) ^ (2:ℝ)
          * (∫⁻ z : ℝ, ‖V (x, z)‖ₑ ^ (2:ℝ) ∂volume) := by
    filter_upwards [memLp_slice_snd_ae hV] with x hx
    have hk2 : MemLp (AiryConj.kUPhi L a) 2 volume :=
      AiryConj.memLp_kUPhi_two hL a
    -- pointwise domination: `|comp (x, w)| ≤ (k̃ ⋆ |V (x, ·)|)(w)` for every `w`
    have hpt : ∀ w : ℝ, ‖AiryConj.compKernel V (AiryConj.bPhiKernel L a) (x, w)‖
        ≤ MeasureTheory.convolution (fun v => AiryConj.kUPhi L a (-v)) (fun z => |V (x, z)|)
            (ContinuousLinearMap.mul ℝ ℝ) volume w := by
      intro w
      have hk2w : MemLp (fun z : ℝ => AiryConj.kUPhi L a (z - w)) 2 volume :=
        hk2.comp_measurePreserving
          (MeasureTheory.measurePreserving_sub_right volume w)
      have hprod : Integrable (fun z : ℝ => |V (x, z)| * AiryConj.kUPhi L a (z - w))
          volume := MemLp.integrable_mul hx.abs hk2w
      have hsec : Integrable (fun z : ℝ => V (x, z) * AiryConj.bPhiKernel L a (z, w))
          volume := by
        apply hprod.mono' (((hVmeas.comp
          (continuous_const.prodMk continuous_id).measurable).mul
          ((AiryConj.measurable_bPhiKernel L a).comp
            (continuous_id.prodMk continuous_const).measurable)).aestronglyMeasurable)
        filter_upwards with z
        show |V (x, z) * AiryConj.bPhiKernel L a (z, w)|
          ≤ |V (x, z)| * AiryConj.kUPhi L a (z - w)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (AiryConj.bPhiKernel_abs_le hL a z w) (abs_nonneg _)
      calc ‖AiryConj.compKernel V (AiryConj.bPhiKernel L a) (x, w)‖
          = |∫ z : ℝ, V (x, z) * AiryConj.bPhiKernel L a (z, w)| := Real.norm_eq_abs _
        _ ≤ ∫ z : ℝ, |V (x, z) * AiryConj.bPhiKernel L a (z, w)| :=
            MeasureTheory.abs_integral_le_integral_abs
        _ ≤ ∫ z : ℝ, |V (x, z)| * AiryConj.kUPhi L a (z - w) := by
            apply integral_mono hsec.abs hprod
            intro z
            show |V (x, z) * AiryConj.bPhiKernel L a (z, w)|
              ≤ |V (x, z)| * AiryConj.kUPhi L a (z - w)
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (AiryConj.bPhiKernel_abs_le hL a z w)
              (abs_nonneg _)
        _ = MeasureTheory.convolution (fun v => AiryConj.kUPhi L a (-v)) (fun z => |V (x, z)|)
              (ContinuousLinearMap.mul ℝ ℝ) volume w := by
            rw [MeasureTheory.convolution_mul]
            have key := MeasureTheory.integral_sub_left_eq_self
              (fun t : ℝ => AiryConj.kUPhi L a (-t) * |V (x, w - t)|) volume w
            simp only [neg_sub, sub_sub_self] at key
            rw [show (∫ z : ℝ, |V (x, z)| * AiryConj.kUPhi L a (z - w))
                = ∫ z : ℝ, AiryConj.kUPhi L a (z - w) * |V (x, z)| from
              integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)]
            exact key
    -- Young's bound for the dominator
    have hYoung := AiryConj.eLpNorm_conv_le (fun v => AiryConj.kUPhi L a (-v)) hkTmeas
      hkTint hkTnn (fun z => |V (x, z)|) hx.abs
    have hnorm_eq : eLpNorm (fun z => |V (x, z)|) 2 volume
        = eLpNorm (fun z => V (x, z)) 2 volume := by
      apply MeasureTheory.eLpNorm_congr_enorm_ae
        (continuous_abs.comp_aestronglyMeasurable hx.aestronglyMeasurable)
        hx.aestronglyMeasurable
      filter_upwards with z
      exact enorm_abs _
    have hsliceAESM : AEStronglyMeasurable
        (fun w : ℝ => AiryConj.compKernel V (AiryConj.bPhiKernel L a) (x, w)) volume :=
      (hcompmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have hconvnn : ∀ w : ℝ, 0 ≤ MeasureTheory.convolution (fun v => AiryConj.kUPhi L a (-v))
        (fun z => |V (x, z)|) (ContinuousLinearMap.mul ℝ ℝ) volume w := by
      intro w
      rw [MeasureTheory.convolution_mul]
      exact integral_nonneg fun t => mul_nonneg (hkTnn _) (abs_nonneg _)
    have hA : (eLpNorm (fun w : ℝ => AiryConj.compKernel V (AiryConj.bPhiKernel L a) (x, w))
          2 volume) ^ (2:ℝ)
        = ∫⁻ w : ℝ, ‖AiryConj.compKernel V (AiryConj.bPhiKernel L a) (x, w)‖ₑ ^ (2:ℝ)
          ∂volume := by
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          hsliceAESM, ENNReal.toReal_ofNat, ← ENNReal.rpow_mul,
        show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    calc (∫⁻ w : ℝ, ‖AiryConj.compKernel V (AiryConj.bPhiKernel L a) (x, w)‖ₑ ^ (2:ℝ)
            ∂volume)
        = (eLpNorm (fun w : ℝ => AiryConj.compKernel V (AiryConj.bPhiKernel L a) (x, w))
            2 volume) ^ (2:ℝ) := hA.symm
      _ ≤ (eLpNorm (MeasureTheory.convolution (fun v => AiryConj.kUPhi L a (-v))
              (fun z => |V (x, z)|) (ContinuousLinearMap.mul ℝ ℝ) volume)
            2 volume) ^ (2:ℝ) := by
          apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 2)
          apply MeasureTheory.eLpNorm_mono_enorm hsliceAESM
          intro w
          rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal (hconvnn w)]
          exact ENNReal.ofReal_le_ofReal ((Real.norm_eq_abs _).trans_le (hpt w))
      _ ≤ (ENNReal.ofReal (∫ v : ℝ, AiryConj.kUPhi L a v)
              * eLpNorm (fun z => V (x, z)) 2 volume) ^ (2:ℝ) := by
          apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 2)
          rw [← hkTint_eval, ← hnorm_eq]
          exact hYoung.2
      _ = (ENNReal.ofReal (∫ v : ℝ, AiryConj.kUPhi L a v)) ^ (2:ℝ)
            * (∫⁻ z : ℝ, ‖V (x, z)‖ₑ ^ (2:ℝ) ∂volume) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
          congr 1
          rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
              hx.aestronglyMeasurable, ENNReal.toReal_ofNat, ← ENNReal.rpow_mul,
            show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  -- integrate the slice bound over `x` and close by Tonelli
  have hV2prod : (∫⁻ x : ℝ, ∫⁻ z : ℝ, ‖V (x, z)‖ₑ ^ (2:ℝ) ∂volume ∂volume)
      = (eLpNorm V 2 (volume.prod volume)) ^ (2:ℝ) := by
    rw [← MeasureTheory.lintegral_prod _ hVnorm,
      lintegral_congr fun p => enorm_rpow_two _,
      ← MeasureTheory.eLpNorm_two_sq_eq_lintegral hV.aestronglyMeasurable]
    exact (enorm_rpow_two _).symm
  have hfin : (∫⁻ p : ℝ × ℝ,
        ‖AiryConj.compKernel V (AiryConj.bPhiKernel L a) p‖ₑ ^ (2:ℝ) ∂(volume.prod volume))
      ≤ (ENNReal.ofReal (∫ v : ℝ, AiryConj.kUPhi L a v) * eLpNorm V 2 (volume.prod volume))
        ^ (2:ℝ) := by
    calc (∫⁻ p : ℝ × ℝ, ‖AiryConj.compKernel V (AiryConj.bPhiKernel L a) p‖ₑ ^ (2:ℝ)
            ∂(volume.prod volume))
        = ∫⁻ x : ℝ, ∫⁻ w : ℝ,
            ‖AiryConj.compKernel V (AiryConj.bPhiKernel L a) (x, w)‖ₑ ^ (2:ℝ) ∂volume
            ∂volume :=
          MeasureTheory.lintegral_prod _ (hcompmeas.enorm.pow_const (2:ℝ)).aemeasurable
      _ ≤ ∫⁻ x : ℝ, (ENNReal.ofReal (∫ v : ℝ, AiryConj.kUPhi L a v)) ^ (2:ℝ)
            * (∫⁻ z : ℝ, ‖V (x, z)‖ₑ ^ (2:ℝ) ∂volume) ∂volume :=
          lintegral_mono_ae hsq
      _ = (ENNReal.ofReal (∫ v : ℝ, AiryConj.kUPhi L a v)) ^ (2:ℝ)
            * (∫⁻ x : ℝ, ∫⁻ z : ℝ, ‖V (x, z)‖ₑ ^ (2:ℝ) ∂volume ∂volume) :=
          lintegral_const_mul'' _ hVnorm.lintegral_prod_right'
      _ = (ENNReal.ofReal (∫ v : ℝ, AiryConj.kUPhi L a v) * eLpNorm V 2 (volume.prod volume))
            ^ (2:ℝ) := by
          rw [hV2prod, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  exact (hfin.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV.eLpNorm_ne_top))).ne

/-! ## `K̃₁` membership

`K̃₁ = (U_aQU_aΦ)(Φ⁻¹U_a⁻¹P_{-1}B₀U_a⁻¹)` is the product of the two HS kernels of
the `V`-bound and the `W`-bound at `T = 1`.  The side condition `a ≥ T + 1` of
the `V`- and `W`-bounds reads `2 ≤ a`, which follows from the admissibility condition
`√(2M) ≥ r + 3` of the joint-determinant lemma at the specialization `a = √(2M)`. -/

/-- The mismatched `V·W` factorization (the same pointwise φ/exp cancellation as
`compKernel_vKernel_wKernel`, with the heat parameter `T` of the `Q`-factor and
the backward-Airy parameter `S` independent — the version is the diagonal
`T = S`): the kernel-level `(U_aQ_{M,T}U_aΦ)(Φ⁻¹U_a⁻¹P_{-S}B₀U_a⁻¹)`. -/
theorem compKernel_vKernel_wKernel_mismatch (T S a M : ℝ) (p : ℝ × ℝ) :
    AiryConj.compKernel (AiryConj.vKernel T a M) (AiryConj.wKernel S a) p
      = uConj a (AiryConj.compKernel (fun q => AiryConj.qMT M T q.1 q.2)
          (AiryConj.backwardAiryPair S)) p := by
  obtain ⟨x, y⟩ := p
  rw [uConj_compKernel]
  show (∫ z : ℝ, AiryConj.vKernel T a M (x, z) * AiryConj.wKernel S a (z, y))
    = ∫ z : ℝ, uConj a (fun q => AiryConj.qMT M T q.1 q.2) (x, z)
        * uConj a (AiryConj.backwardAiryPair S) (z, y)
  apply integral_congr_ae
  filter_upwards with z
  have hφ : AiryConj.phiWeight z * (AiryConj.phiWeight z)⁻¹ = 1 :=
    mul_inv_cancel₀ (AiryConj.phiWeight_pos z).ne'
  have he : Real.exp (-a * z) * Real.exp (a * z) = 1 := by
    rw [← Real.exp_add, show -a * z + a * z = (0:ℝ) by ring, Real.exp_zero]
  have h1 : AiryConj.vKernel T a M (x, z) * AiryConj.wKernel S a (z, y)
      = Real.exp (-a * x) * (AiryConj.qMT M T x z * backwardAiry S (z + y))
        * Real.exp (a * y) := by
    unfold AiryConj.vKernel AiryConj.wKernel
    calc Real.exp (-a * x) * AiryConj.qMT M T x z * Real.exp (-a * z) * AiryConj.phiWeight z
          * ((AiryConj.phiWeight z)⁻¹ * Real.exp (a * z) * backwardAiry S (z + y)
            * Real.exp (a * y))
        = Real.exp (-a * x) * (AiryConj.qMT M T x z * backwardAiry S (z + y))
          * Real.exp (a * y) * (AiryConj.phiWeight z * (AiryConj.phiWeight z)⁻¹)
          * (Real.exp (-a * z) * Real.exp (a * z)) := by ring
      _ = Real.exp (-a * x) * (AiryConj.qMT M T x z * backwardAiry S (z + y))
          * Real.exp (a * y) := by rw [hφ, he, mul_one, mul_one]
  have h2 : uConj a (fun q => AiryConj.qMT M T q.1 q.2) (x, z)
        * uConj a (AiryConj.backwardAiryPair S) (z, y)
      = Real.exp (-a * x) * (AiryConj.qMT M T x z * backwardAiry S (z + y))
        * Real.exp (a * y) := by
    unfold uConj AiryConj.backwardAiryPair
    calc (Real.exp (-a * x) * AiryConj.qMT M T x z * Real.exp (a * z))
          * (Real.exp (-a * z) * backwardAiry S (z + y) * Real.exp (a * y))
        = Real.exp (-a * x) * (AiryConj.qMT M T x z * backwardAiry S (z + y))
          * Real.exp (a * y) * (Real.exp (a * z) * Real.exp (-a * z)) := by ring
      _ = Real.exp (-a * x) * (AiryConj.qMT M T x z * backwardAiry S (z + y))
          * Real.exp (a * y) := by
            rw [← Real.exp_add, show a * z + -a * z = (0:ℝ) by ring, Real.exp_zero]
            ring
  rw [h1, h2]

/-- The inner `V·W` factorization at heat parameter `1` and backward-Airy parameter
`S` ('s inner two factors, and the `T = 1` case of the
`K̃₁`-factorization). -/
theorem uConj_compKernel_qKerTwo_bAiryKer (a M S : ℝ) :
    uConj a (AiryConj.compKernel (qKerTwo M) (bAiryKer S))
      = AiryConj.compKernel (AiryConj.vKernel 1 a M) (AiryConj.wKernel S a) := by
  funext p
  rw [uConj_compKernel, compKernel_vKernel_wKernel_mismatch 1 S a M p]
  have hq : qKerTwo M = fun q => AiryConj.qMT M 1 q.1 q.2 := rfl
  have hb : bAiryKer S = AiryConj.backwardAiryPair S := rfl
  rw [hq, hb]
  exact (uConj_compKernel a _ _ p).symm

/-- **The `K̃₁` kernel factorization**:
`K̃₁ = V_{1,a} W_{1,a}` at kernel level (`compKernel_vKernel_wKernel` at
`T = 1`). -/
theorem k1KerT_eq_compKernel_vKernel_wKernel (a M : ℝ) :
    k1KerT a M = AiryConj.compKernel (AiryConj.vKernel 1 a M) (AiryConj.wKernel 1 a) := by
  funext p
  rw [compKernel_vKernel_wKernel 1 a M p]
  rfl

/-- **K̃₁ is `L²`** (the `V`-bound ⊗ the `W`-bound at `T = 1`, via the
square-integrability bounds `vKernel_sq_integral_le`/`wKernel_sq_integral_le`; the side
condition `a ≥ T + 1` reads `2 ≤ a`). -/
theorem memLp_k1KerT (hM : 0 < M) {a : ℝ} (ha : 2 ≤ a) :
    MemLp (k1KerT a M) 2 (volume.prod volume) := by
  have hcomp : MemLp (AiryConj.compKernel (AiryConj.vKernel 1 a M) (AiryConj.wKernel 1 a))
      2 (volume.prod volume) :=
    memLp_compKernel (AiryConj.measurable_vKernel 1 a M)
      (AiryConj.continuous_wKernel 1 a).measurable
      (AiryConj.vKernel_memLp one_pos hM (by linarith))
      (AiryConj.memLp_wKernel one_pos (by linarith))
  exact (memLp_congr_ae (Eventually.of_forall fun p =>
    congrFun (k1KerT_eq_compKernel_vKernel_wKernel a M) p)).mpr hcomp

/-- **K̃₁ is trace class**: the composition of the
two Hilbert–Schmidt kernel operators of the `V`-bound and the `W`-bound. -/
theorem isTraceClass_k1KerT (hM : 0 < M) {a : ℝ} (ha : 2 ≤ a)
    (h₁ : MemLp (k1KerT a M) 2 (volume.prod volume)) :
    IsTraceClass (kernelOperator h₁) := by
  have hv : MemLp (AiryConj.vKernel 1 a M) 2 (volume.prod volume) :=
    AiryConj.vKernel_memLp one_pos hM (by linarith)
  have hw : MemLp (AiryConj.wKernel 1 a) 2 (volume.prod volume) :=
    AiryConj.memLp_wKernel one_pos (by linarith)
  have hcomp : MemLp (AiryConj.compKernel (AiryConj.vKernel 1 a M) (AiryConj.wKernel 1 a))
      2 (volume.prod volume) :=
    memLp_compKernel (AiryConj.measurable_vKernel 1 a M)
      (AiryConj.continuous_wKernel 1 a).measurable hv hw
  rw [kernelOperator_congr (k1KerT_eq_compKernel_vKernel_wKernel a M) h₁ hcomp,
    kernelOperator_compKernel hv hw hcomp]
  exact ⟨kernelOperator hv, kernelOperator hw, isHilbertSchmidt_kernelOperator hv,
    isHilbertSchmidt_kernelOperator hw, rfl⟩

/-! ## `K̃₂` membership

`K̃₂ = (U_aP_LU_a⁻¹)(U_aQU_aΦ)(Φ⁻¹U_a⁻¹P_{-S}B₀U_a⁻¹)` with `L = 1 + r` and
`S = 2 + r`: the first factor is bounded by the conjugated-heat bound (`conjHeatCLM`), and the
product
of the last two is trace class by the `V`-bound ⊗ the `W`-bound.  The `W`-bound side condition at
`S` is
`a ≥ S + 1 = r + 3` — exactly the admissibility condition `√(2M) ≥ r + 3` of the joint-determinant
lemma. -/

/-- **The `K̃₂` kernel factorization**: conjugation is a
similarity on compositions (`uConj_compKernel`), and the inner two factors are
`vKernel 1 a M` / `wKernel (2+r) a` by the pointwise φ/exp cancellation. -/
theorem k2KerT_eq_compKernel (a M r : ℝ) :
    k2KerT a M r = AiryConj.compKernel (uConj a (heatKerTwo (1 + r)))
      (AiryConj.compKernel (AiryConj.vKernel 1 a M) (AiryConj.wKernel (2 + r) a)) := by
  funext p
  show uConj a (AiryConj.compKernel (heatKerTwo (1 + r))
      (AiryConj.compKernel (qKerTwo M) (bAiryKer (2 + r)))) p = _
  rw [uConj_compKernel, uConj_compKernel_qKerTwo_bAiryKer]

/-- **K̃₂ is `L²`** (the conjugated-heat bound at `L = 1 + r` on the left of the
`L²` kernel from the `V`-bound ⊗ the `W`-bound; side conditions `2 ≤ a` and `r + 3 ≤ a`, the
latter being the admissibility condition of the joint-determinant lemma). -/
theorem memLp_k2KerT (hr : 0 < r) (hM : 0 < M) {a : ℝ} (hadr : r + 3 ≤ a) :
    MemLp (k2KerT a M r) 2 (volume.prod volume) := by
  have hS : (0:ℝ) < 2 + r := by linarith
  have hL : (0:ℝ) < 1 + r := by linarith
  have hv : MemLp (AiryConj.vKernel 1 a M) 2 (volume.prod volume) :=
    AiryConj.vKernel_memLp one_pos hM (by linarith)
  have hw : MemLp (AiryConj.wKernel (2 + r) a) 2 (volume.prod volume) :=
    AiryConj.memLp_wKernel hS (by linarith)
  have hGmeas : Measurable (AiryConj.compKernel (AiryConj.vKernel 1 a M)
      (AiryConj.wKernel (2 + r) a)) :=
    measurable_compKernel (AiryConj.measurable_vKernel 1 a M)
      (AiryConj.continuous_wKernel (2 + r) a).measurable
  have hG : MemLp (AiryConj.compKernel (AiryConj.vKernel 1 a M)
      (AiryConj.wKernel (2 + r) a)) 2 (volume.prod volume) :=
    memLp_compKernel (AiryConj.measurable_vKernel 1 a M)
      (AiryConj.continuous_wKernel (2 + r) a).measurable hv hw
  have hcomp : MemLp (AiryConj.compKernel (uConj a (heatKerTwo (1 + r)))
      (AiryConj.compKernel (AiryConj.vKernel 1 a M) (AiryConj.wKernel (2 + r) a))) 2
      (volume.prod volume) :=
    memLp_compKernel_uConjHeat hL a hGmeas hG
  exact (memLp_congr_ae (Eventually.of_forall fun p =>
    congrFun (k2KerT_eq_compKernel a M r) p)).mpr hcomp

/-- **K̃₂ is trace class**: the operator is
`B ∘L (V ∘L W) = (B ∘L V) ∘L W` with `B = U_aP_LU_a⁻¹` bounded (the conjugated-heat bound, packaged
as
`conjHeatCLM`) and `V`, `W` Hilbert–Schmidt (the `V`-bound, the `W`-bound); `B ∘L V` is HS since HS
is
a left ideal (`IsHilbertSchmidt.comp_left`, `TraceClass/`), so the product is HS ∘ HS. -/
theorem isTraceClass_k2KerT (hr : 0 < r) (hM : 0 < M) {a : ℝ} (hadr : r + 3 ≤ a)
    (h₂ : MemLp (k2KerT a M r) 2 (volume.prod volume)) :
    IsTraceClass (kernelOperator h₂) := by
  have hS : (0:ℝ) < 2 + r := by linarith
  have hL : (0:ℝ) < 1 + r := by linarith
  have hv : MemLp (AiryConj.vKernel 1 a M) 2 (volume.prod volume) :=
    AiryConj.vKernel_memLp one_pos hM (by linarith)
  have hw : MemLp (AiryConj.wKernel (2 + r) a) 2 (volume.prod volume) :=
    AiryConj.memLp_wKernel hS (by linarith)
  have hGmeas : Measurable (AiryConj.compKernel (AiryConj.vKernel 1 a M)
      (AiryConj.wKernel (2 + r) a)) :=
    measurable_compKernel (AiryConj.measurable_vKernel 1 a M)
      (AiryConj.continuous_wKernel (2 + r) a).measurable
  have hG : MemLp (AiryConj.compKernel (AiryConj.vKernel 1 a M)
      (AiryConj.wKernel (2 + r) a)) 2 (volume.prod volume) :=
    memLp_compKernel (AiryConj.measurable_vKernel 1 a M)
      (AiryConj.continuous_wKernel (2 + r) a).measurable hv hw
  have hcomp : MemLp (AiryConj.compKernel (uConj a (heatKerTwo (1 + r)))
      (AiryConj.compKernel (AiryConj.vKernel 1 a M) (AiryConj.wKernel (2 + r) a))) 2
      (volume.prod volume) :=
    memLp_compKernel_uConjHeat hL a hGmeas hG
  rw [kernelOperator_congr (k2KerT_eq_compKernel a M r) h₂ hcomp,
    kernelOperator_compKernel_uConjHeat hL a hG hcomp, kernelOperator_compKernel hv hw hG]
  exact ⟨conjHeatCLM (1 + r) hL a ∘L kernelOperator hv, kernelOperator hw,
    (isHilbertSchmidt_kernelOperator hv).comp_left _, isHilbertSchmidt_kernelOperator hw,
    (ContinuousLinearMap.comp_assoc _ _ _).symm⟩

/-! ## `C̃_r` membership (the `A_r · W_{S,a}` factorization)

`C̃_r = A_r W_{S,a}` with `A_r = U_aQP_rQU_aΦ` and `W_{S,a} = Φ⁻¹U_a⁻¹P_{-S}B₀U_a⁻¹`
(`S = 2 + r`).  The paper proves `A_r` Hilbert–Schmidt from the domination
`0 ≤ QP_rQ ≤ QP_L` (`L = r + 1`) plus the `V`-bound and the `UΦ`-bound, and `W_{S,a}`
Hilbert–Schmidt from the `W`-bound (`a ≥ S + 1` — exactly the admissibility condition of the
joint-determinant lemma,
`√(2M) ≥ r + 3`/stated here as `r + 3 ≤ a`). -/

/-- The kernel of `U_a Q_{M,T} P_L U_a Φ` (the operator of the `UΦ`-bound):
the composite of the `V`-kernel `vKernel T a M` with the `ℬ_{L,a}` kernel
`bPhiKernel L a`. -/
noncomputable def uphiKer (T a M L : ℝ) : ℝ × ℝ → ℝ :=
  AiryConj.compKernel (AiryConj.vKernel T a M) (AiryConj.bPhiKernel L a)

/-- The pointwise weighted form of `uphiKer` (the φ/exp cancellation of the factorization through
`ℬ_{L,a}`): `uphiKer T a M L (x, w) = e^{-ax} (Q_{M,T} P_L)(x, w) e^{-aw} φ(w)`. -/
theorem uphiKer_eq (T a M L : ℝ) (x w : ℝ) :
    uphiKer T a M L (x, w)
      = Real.exp (-a * x) * (AiryConj.compKernel (fun q => AiryConj.qMT M T q.1 q.2)
          (heatKerTwo L) (x, w)) * Real.exp (-a * w) * AiryConj.phiWeight w := by
  have hpt : ∀ z : ℝ, AiryConj.vKernel T a M (x, z) * AiryConj.bPhiKernel L a (z, w)
      = (Real.exp (-a * x) * Real.exp (-a * w) * AiryConj.phiWeight w)
        * (AiryConj.qMT M T x z * heatKernel L (z - w)) := by
    intro z
    have hφ : AiryConj.phiWeight z * (AiryConj.phiWeight z)⁻¹ = 1 :=
      mul_inv_cancel₀ (AiryConj.phiWeight_pos z).ne'
    have he : Real.exp (-a * z) * Real.exp (a * (z - w)) = Real.exp (-a * w) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold AiryConj.vKernel AiryConj.bPhiKernel
    rw [div_eq_mul_inv]
    calc (Real.exp (-a * x) * AiryConj.qMT M T x z * Real.exp (-a * z) * AiryConj.phiWeight z)
        * (AiryConj.phiWeight w * (AiryConj.phiWeight z)⁻¹
          * Real.exp (a * (z - w)) * heatKernel L (z - w))
      = Real.exp (-a * x) * AiryConj.qMT M T x z
          * (Real.exp (-a * z) * Real.exp (a * (z - w)))
          * (AiryConj.phiWeight z * (AiryConj.phiWeight z)⁻¹)
          * AiryConj.phiWeight w * heatKernel L (z - w) := by ring
    _ = Real.exp (-a * x) * AiryConj.qMT M T x z * Real.exp (-a * w) * 1
          * AiryConj.phiWeight w * heatKernel L (z - w) := by rw [he, hφ]
    _ = (Real.exp (-a * x) * Real.exp (-a * w) * AiryConj.phiWeight w)
          * (AiryConj.qMT M T x z * heatKernel L (z - w)) := by ring
  show (∫ z : ℝ, AiryConj.vKernel T a M (x, z) * AiryConj.bPhiKernel L a (z, w)) = _
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  rw [show AiryConj.compKernel (fun q => AiryConj.qMT M T q.1 q.2) (heatKerTwo L) (x, w)
      = ∫ z : ℝ, AiryConj.qMT M T x z * heatKernel L (z - w) from rfl]
  rw [show Real.exp (-a * x) * (∫ z : ℝ, AiryConj.qMT M T x z * heatKernel L (z - w))
        * Real.exp (-a * w) * AiryConj.phiWeight w
      = (Real.exp (-a * x) * Real.exp (-a * w) * AiryConj.phiWeight w)
        * (∫ z : ℝ, AiryConj.qMT M T x z * heatKernel L (z - w)) from by ring]
  rw [← integral_const_mul]

/-- The `UΦ`-bound kernel at `T = 1` is pointwise nonnegative (`Q ≥ 0`, `p_L ≥ 0`). -/
theorem uphiKer_one_nonneg (a M L : ℝ) (hL : 0 < L) (p : ℝ × ℝ) :
    0 ≤ uphiKer 1 a M L p := by
  have hq : qKerTwo M = fun q => AiryConj.qMT M 1 q.1 q.2 := rfl
  rw [uphiKer_eq 1 a M L p.1 p.2, ← hq]
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (integral_nonneg fun y => mul_nonneg (qKerTwo_nonneg M _) (heatKernel_pos hL _).le))
    (Real.exp_pos _).le) (AiryConj.phiWeight_nonneg _)

/-- **The kernel of the `UΦ`-bound is `L²`** (the kernel-level membership content of the
`UΦ`-bound): `compKernel (vKernel T a M) (bPhiKernel L a)` is `L²` from the `V`-bound
(`vKernel_memLp`) and the Young convolution bound for `kUPhi`
(`memLp_compKernel_bPhi`).  The quantitative operator-level form is as
`AiryConj.uphi_hs_le`. -/
theorem memLp_uphiKer (T a M L : ℝ) (hT : 0 < T) (hM : 0 < M) (hL : 0 < L)
    (ha : T + 1 ≤ a) :
    MemLp (uphiKer T a M L) 2 (volume.prod volume) :=
  memLp_compKernel_bPhi hL a (AiryConj.measurable_vKernel T a M)
    (AiryConj.vKernel_memLp hT hM ha)

/-- The operator-level membership for the `UΦ`-bound, direct from `uphi_hs_le`: the composite
`(U_aQ_{M,T}U_aΦ) ∘ ℬ_{L,a}` is Hilbert–Schmidt.
(The kernel membership `memLp_uphiKer` above is what the `C̃_r`/`K̃∪` dominations
consume; this records the direct corollary of `uphi_hs_le`.) -/
theorem isHilbertSchmidt_uphiComposite (T : ℝ) (hT : 0 < T) (M L a : ℝ) (hM : 0 < M)
    (hL : 0 < L) (haeq : a = Real.sqrt (2 * M)) (ha : T + 1 ≤ a) :
    IsHilbertSchmidt (kernelOperator (AiryConj.memLp_vKernel T a M hT hM ha) ∘L
      AiryConj.bPhiCLM L hL a) := by
  obtain ⟨C, hC, K, hbound⟩ := AiryConj.uphi_hs_le T hT
  exact ne_of_lt ((hbound M L a hM hL haeq ha).trans_lt ENNReal.ofReal_lt_top)

/-- `0 ≤ (QP_rQ)(x, w) ≤ (QP_{r+1})(x, w)` (`0 ≤ Q ≤ P_1` gives
`QP_rQ ≤ QP_L` for `L = r + 1`, since `P_rQ ≤ P_{r+1}` by Chapman–Kolmogorov). -/
theorem qPrQKer_le_qPL (hr : 0 < r) (M : ℝ) (x w : ℝ) :
    qPrQKer M r (x, w)
      ≤ AiryConj.compKernel (qKerTwo M) (heatKerTwo (r + 1)) (x, w) := by
  have h1 : Integrable fun y : ℝ => qKerTwo M (x, y)
      * AiryConj.compKernel (heatKerTwo r) (qKerTwo M) (y, w) :=
    integrable_pair_mul_of_heatKernel_le one_pos (by linarith : (0:ℝ) < r + 1)
      (measurable_qKerTwo M)
      (measurable_compKernel (measurable_heatKerTwo r) (measurable_qKerTwo M))
      (fun a b => qKerTwo_abs_le M (a, b))
      (fun a b => compKernel_heatKerTwo_qKerTwo_abs_le hr M a b) x w
  have h2 : Integrable fun y : ℝ => qKerTwo M (x, y) * heatKerTwo (r + 1) (y, w) :=
    integrable_pair_mul_of_heatKernel_le one_pos (by linarith) (measurable_qKerTwo M)
      (measurable_heatKerTwo (r + 1)) (fun a b => qKerTwo_abs_le M (a, b))
      (fun a b => heatKerTwo_abs_le_self (by linarith) (a, b)) x w
  calc qPrQKer M r (x, w)
      = ∫ y : ℝ, qKerTwo M (x, y)
          * AiryConj.compKernel (heatKerTwo r) (qKerTwo M) (y, w) := rfl
    _ ≤ ∫ y : ℝ, qKerTwo M (x, y) * heatKerTwo (r + 1) (y, w) :=
        integral_mono h1 h2 fun y =>
          mul_le_mul_of_nonneg_left (compKernel_heatKerTwo_qKerTwo_le hr M y w)
            (qKerTwo_nonneg M (x, y))
    _ = AiryConj.compKernel (qKerTwo M) (heatKerTwo (r + 1)) (x, w) := rfl

/-- The kernel of `A_r` is nonnegative. -/
theorem aRKer_nonneg (hr : 0 < r) (a M : ℝ) (p : ℝ × ℝ) : 0 ≤ aRKer a M r p := by
  unfold aRKer
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (qPrQKer_nonneg hr M p))
    (Real.exp_pos _).le) (AiryConj.phiWeight_nonneg p.2)

/-- The kernel domination behind "A_r is Hilbert–Schmidt":
`0 ≤ aRKer ≤ uphiKer` for `L = r + 1`. -/
theorem aRKer_le_uphiKer (hr : 0 < r) (a M : ℝ) (p : ℝ × ℝ) :
    aRKer a M r p ≤ uphiKer 1 a M (r + 1) p := by
  have hq : qKerTwo M = fun q => AiryConj.qMT M 1 q.1 q.2 := rfl
  rw [uphiKer_eq 1 a M (r + 1) p.1 p.2, ← hq]
  unfold aRKer
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (qPrQKer_le_qPL hr M p.1 p.2) (Real.exp_pos _).le)
    (Real.exp_pos _).le) (AiryConj.phiWeight_nonneg p.2)

/-- **The `A_r` kernel is `L²`** (the paper's step "the `V`- and `UΦ`-bounds imply that
A_r is Hilbert–Schmidt", kernel-level form): domination by the kernel of the `UΦ`-bound at
`L = r + 1` (which is `L²` by the `V`-bound ⊗ Young).  This discharges the `hA` hypothesis of
`trace_crKerT_eq`. -/
theorem memLp_aRKer (hr : 0 < r) (hM : 0 < M) {a : ℝ} (ha : 2 ≤ a) :
    MemLp (aRKer a M r) 2 (volume.prod volume) := by
  have hup : MemLp (uphiKer 1 a M (r + 1)) 2 (volume.prod volume) :=
    memLp_compKernel_bPhi (by linarith : (0:ℝ) < r + 1) a
      (AiryConj.measurable_vKernel 1 a M) (AiryConj.vKernel_memLp one_pos hM (by linarith))
  rw [MeasureTheory.memLp_iff]
  exact (MeasureTheory.eLpNorm_mono_enorm (measurable_aRKer a M r).aestronglyMeasurable
    (fun p => by
      rw [Real.enorm_eq_ofReal (aRKer_nonneg hr a M p),
        Real.enorm_eq_ofReal (uphiKer_one_nonneg a M (r + 1) (by linarith) p)]
      exact ENNReal.ofReal_le_ofReal (aRKer_le_uphiKer hr a M p))).trans_lt hup

/-- **The `W_{S,a}` kernel is `L²`** (the paper's step "the `W`-bound gives the same property
for `W_{S,a}` because `a ≥ S + 1`", with `S = 2 + r`): the admissibility condition
`r + 3 ≤ a` is exactly `a ≥ S + 1`.  This discharges the `hW` hypothesis of
`trace_crKerT_eq`. -/
theorem memLp_wSKer (hr : 0 < r) {a : ℝ} (hadr : r + 3 ≤ a) :
    MemLp (wSKer (2 + r) a) 2 (volume.prod volume) :=
  AiryConj.memLp_wKernel (by linarith) (by linarith)

/-- **C̃_r is `L²`**: `C̃_r = A_r W_{S,a}` with both factors `L²`
(`memLp_aRKer`, `memLp_wSKer`), so the composite kernel is `L²` (`memLp_compKernel`);
the identification is `crKerT_eq_compKernel_aRKer_wSKer`. -/
theorem memLp_crKerT (hr : 0 < r) (hM : 0 < M) {a : ℝ} (hadr : r + 3 ≤ a) :
    MemLp (crKerT a M r) 2 (volume.prod volume) := by
  have hcomp : MemLp (AiryConj.compKernel (aRKer a M r) (wSKer (2 + r) a)) 2
      (volume.prod volume) :=
    memLp_compKernel (measurable_aRKer a M r) (measurable_wSKer (2 + r) a)
      (memLp_aRKer hr hM (by linarith)) (memLp_wSKer hr hadr)
  exact (memLp_congr_ae (Eventually.of_forall fun p =>
    congrFun (crKerT_eq_compKernel_aRKer_wSKer hr a M) p)).mpr hcomp

/-- **C̃_r is trace class**: the composition of the two
Hilbert–Schmidt kernel operators of `A_r` and `W_{S,a}`. -/
theorem isTraceClass_crKerT (hr : 0 < r) (hM : 0 < M) {a : ℝ} (hadr : r + 3 ≤ a)
    (hcr : MemLp (crKerT a M r) 2 (volume.prod volume)) :
    IsTraceClass (kernelOperator hcr) := by
  have hA : MemLp (aRKer a M r) 2 (volume.prod volume) := memLp_aRKer hr hM (by linarith)
  have hW : MemLp (wSKer (2 + r) a) 2 (volume.prod volume) := memLp_wSKer hr hadr
  have hcomp : MemLp (AiryConj.compKernel (aRKer a M r) (wSKer (2 + r) a)) 2
      (volume.prod volume) :=
    memLp_compKernel (measurable_aRKer a M r) (measurable_wSKer (2 + r) a) hA hW
  rw [kernelOperator_congr (crKerT_eq_compKernel_aRKer_wSKer hr a M) hcr hcomp,
    kernelOperator_compKernel hA hW hcomp]
  exact ⟨kernelOperator hA, kernelOperator hW, isHilbertSchmidt_kernelOperator hA,
    isHilbertSchmidt_kernelOperator hW, rfl⟩

/-! ## `K̃∪` membership

`K̃∪ = Ṽ_{D,r} · W_{S,a}` with `Ṽ_{D,r} = U_a D_r U_a Φ` and
`D_r := P₁P_rP₁ − ΛP_rΛ = QP_rP₁ + P₁P_rQ − QP_rQ`, `0 ≤ D_r ≤ QP_L + P_LQ`
(`L = r + 1`).  The two dominators are `L²` by the `UΦ`-bound (`memLp_uphiKer`) and by
the conjugated-heat bound ∘ the `V`-bound (`memLp_compKernel_uConjHeat` on `vKernel`), respectively.
-/

/-- The kernel of `D_r = P₁P_rP₁ − ΛP_rΛ` (at `T = 1`). -/
noncomputable def dRKer (M r : ℝ) : ℝ × ℝ → ℝ :=
  fun q => AiryConj.compKernel (heatKerTwo 1)
      (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1)) q
    - AiryConj.compKernel (lamKerTwo M)
      (AiryConj.compKernel (heatKerTwo r) (lamKerTwo M)) q

/-- `dRKer` is measurable. -/
theorem measurable_dRKer (M r : ℝ) : Measurable (dRKer M r) :=
  (measurable_compKernel (measurable_heatKerTwo 1)
    (measurable_compKernel (measurable_heatKerTwo r) (measurable_heatKerTwo 1))).sub
    (measurable_compKernel (measurable_lamKerTwo M)
      (measurable_compKernel (measurable_heatKerTwo r) (measurable_lamKerTwo M)))

/-- **The `D_r` split**: `D_r = P₁P_rQ + QP_rΛ` pointwise (from
`kcupDiffKer_eq` and `Λ = P₁ − Q`). -/
theorem dRKer_eq_add (hr : 0 < r) (M : ℝ) (u z : ℝ) :
    dRKer M r (u, z)
      = AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M))
          (u, z)
        + AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (lamKerTwo M))
          (u, z) := by
  have hLam : AiryConj.compKernel (heatKerTwo r) (lamKerTwo M)
      = fun p => AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1) p
        - AiryConj.compKernel (heatKerTwo r) (qKerTwo M) p := by
    funext p
    rw [show lamKerTwo M = fun q => heatKerTwo 1 q - qKerTwo M q from
      funext fun q => lamKerTwo_eq_sub M q]
    exact compKernel_sub_right p.1 p.2
      (integrable_pair_mul_of_heatKernel_le hr one_pos (measurable_heatKerTwo r)
        (measurable_heatKerTwo 1) (fun a b => heatKerTwo_abs_le_self hr (a, b))
        (fun a b => heatKerTwo_abs_le_self one_pos (a, b)) p.1 p.2)
      (integrable_pair_mul_of_heatKernel_le hr one_pos (measurable_heatKerTwo r)
        (measurable_qKerTwo M) (fun a b => heatKerTwo_abs_le_self hr (a, b))
        (fun a b => qKerTwo_abs_le M (a, b)) p.1 p.2)
  have hsub : AiryConj.compKernel (qKerTwo M)
        (AiryConj.compKernel (heatKerTwo r) (lamKerTwo M)) (u, z)
      = AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1))
          (u, z)
        - AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M))
          (u, z) := by
    rw [hLam]
    exact compKernel_sub_right u z
      (integrable_pair_mul_of_heatKernel_le one_pos (by linarith : (0:ℝ) < r + 1)
        (measurable_qKerTwo M)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_heatKerTwo 1))
        (fun a b => qKerTwo_abs_le M (a, b))
        (fun a b => by
          rw [heatKerTwo_comp hr one_pos]
          exact heatKerTwo_abs_le_self (by linarith) (a, b)) u z)
      (integrable_pair_mul_of_heatKernel_le one_pos (by linarith : (0:ℝ) < r + 1)
        (measurable_qKerTwo M)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_qKerTwo M))
        (fun a b => qKerTwo_abs_le M (a, b))
        (fun a b => compKernel_heatKerTwo_qKerTwo_abs_le hr M a b) u z)
  show AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r)
        (heatKerTwo 1)) (u, z)
      - AiryConj.compKernel (lamKerTwo M) (AiryConj.compKernel (heatKerTwo r)
        (lamKerTwo M)) (u, z) = _
  rw [kcupDiffKer_eq hr M u z, hsub]
  ring

/-- `0 ≤ D_r` pointwise: `D_r = P₁P_rQ + QP_rΛ`, a sum of two
nonnegative composites. -/
theorem dRKer_nonneg (hr : 0 < r) (M : ℝ) (u z : ℝ) : 0 ≤ dRKer M r (u, z) := by
  rw [dRKer_eq_add hr M u z]
  apply add_nonneg
  · exact integral_nonneg fun w => mul_nonneg (heatKernel_pos one_pos _).le
      (compKernel_heatKerTwo_qKerTwo_nonneg hr M _ _)
  · exact integral_nonneg fun w => mul_nonneg (qKerTwo_nonneg M _)
      (compKernel_heatKerTwo_lamKerTwo_nonneg hr M _ _)

/-- **`0 ≤ D_r ≤ QP_L + P_LQ`** with `L = r + 1`: `P₁P_rQ = P_L Q`
(Chapman–Kolmogorov, `heatKerTwo_comp` + reassociation) and `QP_rΛ ≤ QP_rP₁ = QP_L`
(from `0 ≤ Λ ≤ P₁`, `lamKerTwo_le`). -/
theorem dRKer_le (hr : 0 < r) (M : ℝ) (u z : ℝ) :
    dRKer M r (u, z)
      ≤ AiryConj.compKernel (qKerTwo M) (heatKerTwo (r + 1)) (u, z)
        + AiryConj.compKernel (heatKerTwo (r + 1)) (qKerTwo M) (u, z) := by
  rw [dRKer_eq_add hr M u z]
  have hA : AiryConj.compKernel (heatKerTwo 1)
        (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) (u, z)
      = AiryConj.compKernel (heatKerTwo (r + 1)) (qKerTwo M) (u, z) := by
    rw [show AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r)
          (qKerTwo M))
        = AiryConj.compKernel (AiryConj.compKernel (heatKerTwo 1) (heatKerTwo r))
          (qKerTwo M) from
        funext fun p => (compKernel_assoc p.1 p.2
          (integrable_assoc_P1_Pr_Q hr M p.1 p.2)).symm]
    rw [heatKerTwo_comp one_pos hr, show (1:ℝ) + r = r + 1 from by ring]
  have hB : AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r)
        (lamKerTwo M)) (u, z)
      ≤ AiryConj.compKernel (qKerTwo M) (heatKerTwo (r + 1)) (u, z) := by
    have h1 : Integrable fun w : ℝ => qKerTwo M (u, w)
        * AiryConj.compKernel (heatKerTwo r) (lamKerTwo M) (w, z) :=
      integrable_pair_mul_of_heatKernel_le one_pos (by linarith : (0:ℝ) < r + 1)
        (measurable_qKerTwo M)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_lamKerTwo M))
        (fun a b => qKerTwo_abs_le M (a, b))
        (fun a b => compKernel_heatKerTwo_lamKerTwo_abs_le hr M a b) u z
    have h2 : Integrable fun w : ℝ => qKerTwo M (u, w)
        * AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1) (w, z) :=
      integrable_pair_mul_of_heatKernel_le one_pos (by linarith : (0:ℝ) < r + 1)
        (measurable_qKerTwo M)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_heatKerTwo 1))
        (fun a b => qKerTwo_abs_le M (a, b))
        (fun a b => by
          rw [heatKerTwo_comp hr one_pos]
          exact heatKerTwo_abs_le_self (by linarith) (a, b)) u z
    calc AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (lamKerTwo M))
          (u, z)
        ≤ ∫ w : ℝ, qKerTwo M (u, w)
            * AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1) (w, z) :=
          integral_mono h1 h2 fun w =>
            mul_le_mul_of_nonneg_left ((compKernel_heatKerTwo_lamKerTwo_le hr M w z).trans_eq
              (by rw [heatKerTwo_comp hr one_pos]; rfl)) (qKerTwo_nonneg M (u, w))
      _ = AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r)
            (heatKerTwo 1)) (u, z) := rfl
      _ = AiryConj.compKernel (qKerTwo M) (heatKerTwo (r + 1)) (u, z) := by
          rw [heatKerTwo_comp hr one_pos]
  rw [hA]
  linarith

/-- The kernel of `Ṽ_{D,r} := U_a D_r U_a Φ`:
`e^{-ax} · D_r(x, z) · e^{-az} · φ(z)`. -/
noncomputable def vdRKer (a M r : ℝ) : ℝ × ℝ → ℝ :=
  fun p => Real.exp (-a * p.1) * dRKer M r p * Real.exp (-a * p.2) * AiryConj.phiWeight p.2

/-- `vdRKer` is measurable. -/
theorem measurable_vdRKer (a M r : ℝ) : Measurable (vdRKer a M r) :=
  (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).measurable.mul
    (measurable_dRKer M r)).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).measurable).mul
    (AiryConj.continuous_phiWeight.comp continuous_snd).measurable

/-- The kernel of `U_a P_L Q U_a Φ` (`(U_aP_LU_a⁻¹)(U_aQU_aΦ)` at
kernel level): `compKernel (uConj a (heatKerTwo L)) (vKernel 1 a M)`. -/
noncomputable def plqKer (a M L : ℝ) : ℝ × ℝ → ℝ :=
  AiryConj.compKernel (uConj a (heatKerTwo L)) (AiryConj.vKernel 1 a M)

/-- The pointwise weighted form of `plqKer` (the exp cancellation):
`plqKer a M L (x, z) = e^{-ax} (P_L Q)(x, z) e^{-az} φ(z)`. -/
theorem plqKer_eq (a M L : ℝ) (x z : ℝ) :
    plqKer a M L (x, z)
      = Real.exp (-a * x) * (AiryConj.compKernel (heatKerTwo L) (qKerTwo M) (x, z))
        * Real.exp (-a * z) * AiryConj.phiWeight z := by
  show (∫ u : ℝ, uConj a (heatKerTwo L) (x, u) * AiryConj.vKernel 1 a M (u, z)) = _
  rw [show AiryConj.compKernel (heatKerTwo L) (qKerTwo M) (x, z)
      = ∫ u : ℝ, heatKerTwo L (x, u) * qKerTwo M (u, z) from rfl]
  have hpt : ∀ u : ℝ, uConj a (heatKerTwo L) (x, u) * AiryConj.vKernel 1 a M (u, z)
      = (Real.exp (-a * x) * Real.exp (-a * z) * AiryConj.phiWeight z)
        * (heatKerTwo L (x, u) * qKerTwo M (u, z)) := by
    intro u
    have he : Real.exp (a * u) * Real.exp (-a * u) = 1 := by
      rw [← Real.exp_add, show a * u + -a * u = (0:ℝ) by ring, Real.exp_zero]
    show (Real.exp (-a * x) * heatKerTwo L (x, u) * Real.exp (a * u))
        * (Real.exp (-a * u) * AiryConj.qMT M 1 u z * Real.exp (-a * z)
          * AiryConj.phiWeight z) = _
    calc (Real.exp (-a * x) * heatKerTwo L (x, u) * Real.exp (a * u))
        * (Real.exp (-a * u) * AiryConj.qMT M 1 u z * Real.exp (-a * z)
          * AiryConj.phiWeight z)
      = (Real.exp (-a * x) * Real.exp (-a * z) * AiryConj.phiWeight z)
        * (heatKerTwo L (x, u) * AiryConj.qMT M 1 u z)
        * (Real.exp (a * u) * Real.exp (-a * u)) := by ring
    _ = (Real.exp (-a * x) * Real.exp (-a * z) * AiryConj.phiWeight z)
        * (heatKerTwo L (x, u) * AiryConj.qMT M 1 u z) := by rw [he, mul_one]
    _ = _ := rfl
  rw [integral_congr_ae (Eventually.of_forall hpt),
    show Real.exp (-a * x) * (∫ u : ℝ, heatKerTwo L (x, u) * qKerTwo M (u, z))
        * Real.exp (-a * z) * AiryConj.phiWeight z
      = (Real.exp (-a * x) * Real.exp (-a * z) * AiryConj.phiWeight z)
        * (∫ u : ℝ, heatKerTwo L (x, u) * qKerTwo M (u, z)) from by ring,
    ← integral_const_mul]

/-- `plqKer` is pointwise nonnegative. -/
theorem plqKer_nonneg (a M L : ℝ) (hL : 0 < L) (p : ℝ × ℝ) : 0 ≤ plqKer a M L p := by
  rw [plqKer_eq a M L p.1 p.2]
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (integral_nonneg fun u => mul_nonneg (heatKernel_pos hL _).le (qKerTwo_nonneg M _)))
    (Real.exp_pos _).le) (AiryConj.phiWeight_nonneg _)

/-- `0 ≤ vdRKer` pointwise (from `dRKer_nonneg`). -/
theorem vdRKer_nonneg (hr : 0 < r) (a M : ℝ) (p : ℝ × ℝ) : 0 ≤ vdRKer a M r p := by
  unfold vdRKer
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (dRKer_nonneg hr M p.1 p.2))
    (Real.exp_pos _).le) (AiryConj.phiWeight_nonneg p.2)

/-- The kernel domination behind "Ṽ_{D,r} is HS" (the domination
`0 ≤ D_r ≤ QP_L + P_LQ` with `L = r + 1`): `vdRKer ≤ uphiKer + plqKer` pointwise. -/
theorem vdRKer_le (hr : 0 < r) (a M : ℝ) (p : ℝ × ℝ) :
    vdRKer a M r p ≤ uphiKer 1 a M (r + 1) p + plqKer a M (r + 1) p := by
  obtain ⟨x, z⟩ := p
  rw [uphiKer_eq 1 a M (r + 1) x z, plqKer_eq a M (r + 1) x z]
  have hq : qKerTwo M = fun q => AiryConj.qMT M 1 q.1 q.2 := rfl
  rw [← hq]
  have hle := dRKer_le hr M x z
  calc Real.exp (-a * x) * dRKer M r (x, z) * Real.exp (-a * z) * AiryConj.phiWeight z
      ≤ Real.exp (-a * x) * (AiryConj.compKernel (qKerTwo M) (heatKerTwo (r + 1)) (x, z)
          + AiryConj.compKernel (heatKerTwo (r + 1)) (qKerTwo M) (x, z))
        * Real.exp (-a * z) * AiryConj.phiWeight z := by
        apply mul_le_mul_of_nonneg_right _ (AiryConj.phiWeight_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    _ = Real.exp (-a * x) * AiryConj.compKernel (qKerTwo M) (heatKerTwo (r + 1)) (x, z)
          * Real.exp (-a * z) * AiryConj.phiWeight z
        + Real.exp (-a * x) * AiryConj.compKernel (heatKerTwo (r + 1)) (qKerTwo M) (x, z)
          * Real.exp (-a * z) * AiryConj.phiWeight z := by ring

/-- **Ṽ_{D,r} is `L²`**: domination by `uphiKer + plqKer`, both
`L²` (`memLp_uphiKer` from the `UΦ`-bound; the conjugated-heat bound ∘ the `V`-bound via
`memLp_compKernel_uConjHeat`). -/
theorem memLp_vdRKer (hr : 0 < r) (hM : 0 < M) {a : ℝ} (hadr : r + 3 ≤ a) :
    MemLp (vdRKer a M r) 2 (volume.prod volume) := by
  have hup : MemLp (uphiKer 1 a M (r + 1)) 2 (volume.prod volume) :=
    memLp_uphiKer 1 a M (r + 1) one_pos hM (by linarith) (by linarith)
  have hplq : MemLp (plqKer a M (r + 1)) 2 (volume.prod volume) :=
    memLp_compKernel_uConjHeat (by linarith : (0:ℝ) < r + 1) a
      (AiryConj.measurable_vKernel 1 a M) (AiryConj.vKernel_memLp one_pos hM (by linarith))
  have hsum : MemLp (uphiKer 1 a M (r + 1) + plqKer a M (r + 1)) 2 (volume.prod volume) :=
    hup.add hplq
  rw [MeasureTheory.memLp_iff]
  exact (MeasureTheory.eLpNorm_mono_enorm (measurable_vdRKer a M r).aestronglyMeasurable
    (fun p => by
      rw [Real.enorm_eq_ofReal (vdRKer_nonneg hr a M p), Pi.add_apply,
        Real.enorm_eq_ofReal (add_nonneg (uphiKer_one_nonneg a M (r + 1) (by linarith) p)
          (plqKer_nonneg a M (r + 1) (by linarith) p))]
      exact ENNReal.ofReal_le_ofReal (vdRKer_le hr a M p))).trans_lt hsum

/-- **The K̃∪ kernel factorization**:
`K̃∪ = Ṽ_{D,r} · W_{S,a}` at kernel level (conjugation similarity `uConj_compKernel`
plus the pointwise φ/exp cancellation). -/
theorem kcupKerT_eq_compKernel_vdRKer_wSKer (a M r : ℝ) :
    kcupKerT a M r = AiryConj.compKernel (vdRKer a M r) (wSKer (2 + r) a) := by
  funext p
  obtain ⟨x, y⟩ := p
  show uConj a (AiryConj.compKernel (dRKer M r) (bAiryKer (2 + r))) (x, y) = _
  rw [uConj_compKernel]
  show (∫ z : ℝ, uConj a (dRKer M r) (x, z) * uConj a (bAiryKer (2 + r)) (z, y))
    = ∫ z : ℝ, vdRKer a M r (x, z) * wSKer (2 + r) a (z, y)
  apply integral_congr_ae
  filter_upwards with z
  have hφ : AiryConj.phiWeight z * (AiryConj.phiWeight z)⁻¹ = 1 :=
    mul_inv_cancel₀ (AiryConj.phiWeight_pos z).ne'
  have he : Real.exp (-a * z) * Real.exp (a * z) = 1 := by
    rw [← Real.exp_add, show -a * z + a * z = (0:ℝ) by ring, Real.exp_zero]
  have h1 : (Real.exp (-a * x) * dRKer M r (x, z) * Real.exp (-a * z)
        * AiryConj.phiWeight z)
      * ((AiryConj.phiWeight z)⁻¹ * Real.exp (a * z) * backwardAiry (2 + r) (z + y)
        * Real.exp (a * y))
      = Real.exp (-a * x) * (dRKer M r (x, z) * backwardAiry (2 + r) (z + y))
        * Real.exp (a * y) := by
    calc (Real.exp (-a * x) * dRKer M r (x, z) * Real.exp (-a * z)
          * AiryConj.phiWeight z)
        * ((AiryConj.phiWeight z)⁻¹ * Real.exp (a * z) * backwardAiry (2 + r) (z + y)
          * Real.exp (a * y))
      = Real.exp (-a * x) * (dRKer M r (x, z) * backwardAiry (2 + r) (z + y))
          * Real.exp (a * y) * (AiryConj.phiWeight z * (AiryConj.phiWeight z)⁻¹)
          * (Real.exp (-a * z) * Real.exp (a * z)) := by ring
    _ = Real.exp (-a * x) * (dRKer M r (x, z) * backwardAiry (2 + r) (z + y))
          * Real.exp (a * y) := by rw [hφ, he, mul_one, mul_one]
  have h2 : (Real.exp (-a * x) * dRKer M r (x, z) * Real.exp (a * z))
      * (Real.exp (-a * z) * backwardAiry (2 + r) (z + y) * Real.exp (a * y))
      = Real.exp (-a * x) * (dRKer M r (x, z) * backwardAiry (2 + r) (z + y))
        * Real.exp (a * y) := by
    calc (Real.exp (-a * x) * dRKer M r (x, z) * Real.exp (a * z))
        * (Real.exp (-a * z) * backwardAiry (2 + r) (z + y) * Real.exp (a * y))
      = Real.exp (-a * x) * (dRKer M r (x, z) * backwardAiry (2 + r) (z + y))
          * Real.exp (a * y) * (Real.exp (a * z) * Real.exp (-a * z)) := by ring
    _ = Real.exp (-a * x) * (dRKer M r (x, z) * backwardAiry (2 + r) (z + y))
          * Real.exp (a * y) := by
        rw [← Real.exp_add, show a * z + -a * z = (0:ℝ) by ring, Real.exp_zero]
        ring
  show (Real.exp (-a * x) * dRKer M r (x, z) * Real.exp (a * z))
      * (Real.exp (-a * z) * backwardAiry (2 + r) (z + y) * Real.exp (a * y))
    = (Real.exp (-a * x) * dRKer M r (x, z) * Real.exp (-a * z) * AiryConj.phiWeight z)
      * ((AiryConj.phiWeight z)⁻¹ * Real.exp (a * z) * backwardAiry (2 + r) (z + y)
        * Real.exp (a * y))
  rw [h2, h1]

/-- **K̃∪ is `L²`**: via
`twoIntKCup_decomp` (`K̃∪ = K̃₁ + K̃₂ − C̃_r`) plus `MemLp.add` /
`MemLp.sub` closure. -/
theorem memLp_kcupKerT (hr : 0 < r) (hM : 0 < M) {a : ℝ} (hadr : r + 3 ≤ a) :
    MemLp (kcupKerT a M r) 2 (volume.prod volume) := by
  have h1 : MemLp (k1KerT a M) 2 (volume.prod volume) := memLp_k1KerT hM (by linarith)
  have h2 : MemLp (k2KerT a M r) 2 (volume.prod volume) := memLp_k2KerT hr hM hadr
  have hcr : MemLp (crKerT a M r) 2 (volume.prod volume) := memLp_crKerT hr hM hadr
  exact (memLp_congr_ae (Eventually.of_forall fun p =>
    congrFun (twoIntKCup_decomp hr a M) p)).mpr ((h1.add h2).sub hcr)

/-- **K̃∪ is trace class**: `K̃∪ = Ṽ_{D,r} · W_{S,a}` with `Ṽ_{D,r}` Hilbert–Schmidt
(`memLp_vdRKer`)
and `W_{S,a}` Hilbert–Schmidt (the `W`-bound at `S = 2 + r`, using the admissibility
`r + 3 ≤ a`). -/
theorem isTraceClass_kcupKerT (hr : 0 < r) (hM : 0 < M) {a : ℝ} (hadr : r + 3 ≤ a)
    (hcup : MemLp (kcupKerT a M r) 2 (volume.prod volume)) :
    IsTraceClass (kernelOperator hcup) := by
  have hV : MemLp (vdRKer a M r) 2 (volume.prod volume) := memLp_vdRKer hr hM hadr
  have hW : MemLp (wSKer (2 + r) a) 2 (volume.prod volume) := memLp_wSKer hr hadr
  have hcomp : MemLp (AiryConj.compKernel (vdRKer a M r) (wSKer (2 + r) a)) 2
      (volume.prod volume) :=
    (memLp_congr_ae (Eventually.of_forall fun p =>
      congrFun (kcupKerT_eq_compKernel_vdRKer_wSKer a M r) p)).mp hcup
  rw [kernelOperator_congr (kcupKerT_eq_compKernel_vdRKer_wSKer a M r) hcup hcomp,
    kernelOperator_compKernel hV hW hcomp]
  exact ⟨kernelOperator hV, kernelOperator hW, isHilbertSchmidt_kernelOperator hV,
    isHilbertSchmidt_kernelOperator hW, rfl⟩

/-! ## the discharged trace cancellation -/

/-- **The discharged two-interval trace cancellation** (the Step-1
algebra of the paper's separated-block estimate): given `0 < r`, `0 < M` and the admissibility
condition `r + 3 ≤ a` of the joint-determinant lemma (the paper's `√(2M) ≥ r + 3` at
`a = √(2M)`),

  `Tr K̃₁ + Tr K̃₂ − Tr K̃∪ = Tr C̃_r`.

This is `trace_twoIntKCup` with all four `MemLp` hypotheses discharged by
`memLp_k1KerT` / `memLp_k2KerT` / `memLp_kcupKerT` / `memLp_crKerT` and all four
`IsTraceClass` hypotheses discharged by `isTraceClass_k1KerT` / `isTraceClass_k2KerT` /
`isTraceClass_kcupKerT` / `isTraceClass_crKerT`. -/
theorem trace_twoIntKCup_discharged (hr : 0 < r) (hM : 0 < M) {a : ℝ} (hadr : r + 3 ≤ a) :
    trace (kernelOperator (memLp_k1KerT hM (by linarith : (2:ℝ) ≤ a)))
      + trace (kernelOperator (memLp_k2KerT hr hM hadr))
      - trace (kernelOperator (memLp_kcupKerT hr hM hadr))
      = trace (kernelOperator (memLp_crKerT hr hM hadr)) :=
  trace_twoIntKCup hr a M _ _ _ _
    (isTraceClass_k1KerT hM (by linarith) _)
    (isTraceClass_k2KerT hr hM hadr _)
    (isTraceClass_kcupKerT hr hM hadr _)
    (isTraceClass_crKerT hr hM hadr _)

end AiryTwoInt
