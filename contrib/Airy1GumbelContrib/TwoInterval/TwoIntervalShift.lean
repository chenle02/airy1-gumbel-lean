/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoInterval.TwoIntervalDetRem

/-!
# The second-block determinant equals the first: `det₁(I − K̃₂) = det₁(I − K̃₁)`

Part of the two-interval modules (`TwoInterval/`): the determinant-level stationarity step
inside the proof of the paper's two-block lemma, namely

  `det(I − K̃₂) = det(I − K̃₁)`,

with `K̃₁ = U_a Q P_{-1}B₀ U_a⁻¹` and `K̃₂ = U_a P_{1+r} Q P_{-(2+r)}B₀ U_a⁻¹`.

## The paper's argument, formalized step by step

With `L = 1 + r`, `S = 2 + r = L + 1`:

* `K̃₂ = A_{r,a} B_{r,a}` with `A_{r,a} = (U_aP_LU_a⁻¹)(U_aQU_aΦ)` (bounded ∘ HS, hence
  HS) and `B_{r,a} = W_{S,a}` (HS); this is `kernelOperator_k2KerT_eq`.
* Simon's cyclicity (contrib `fredholmDetOne_cyclic`):
  `det(I − K̃₂) = det(I − B_{r,a}A_{r,a})`.
* The scalar heat–Airy identity `P_{-S}B₀P_L = P_{-1}B₀` (QR12 Prop. 1.2)
  gives `B_{r,a}A_{r,a} = W_{1,a} V_{1,a}`.  At operator level this is
  the new **right-factor identity** `kW_{S} ∘L conjHeat_L = kW_{S−L}`
  (`kernelOperator_wKernel_comp_conjHeatCLM`), from the kernel identity
  `compKernel_wKernel_uConjHeat` (= `heatAiryConv_offset`, through
  `heatKerTwo_comp_bAiryKer`) plus the right-factor Fubini lemma
  `kernelOperator_compKernel_uConjHeat_right` (Young + Hölder, the pattern of
  `kernelOperator_uphiKer`).
* Cyclicity once more: `det(I − W_{1,a}V_{1,a}) = det(I − V_{1,a}W_{1,a})
  = det(I − K̃₁)` (the factorization `K̃₁ = V_{1,a}W_{1,a}`).

## Notes

* The identity holds for every spectral parameter `z` (cyclicity is termwise on the
  Plemelj series); the `z = 1` case is the paper's statement.
* The weight `a` is free: only the side conditions `0 < r`, `0 < M`, `r + 3 ≤ a`
  are used (they make `V_{1,a}`, `W_{1,a}`, `W_{2+r,a}` Hilbert–Schmidt).  The
  `separated` bridge applies it at `a = √(2M)`.
* `fredholmDetOne_congr` is the missing congruence helper (the `IsTraceClass` argument
  is a `Prop`, so the value does not depend on it).
-/

namespace AiryTwoInt

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal InnerProduct InnerProductSpace
open HilbertSchmidt

/-! ### Congruence for `fredholmDetOne` -/

/-- `fredholmDetOne` respects equality of operators, for any choice of the trace-class
proofs (the proof argument is a `Prop`). -/
theorem fredholmDetOne_congr {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A B : E →L[𝕜] E} (h : A = B)
    (hA : IsTraceClass A) (hB : IsTraceClass B) (z : 𝕜) :
    fredholmDetOne A hA z = fredholmDetOne B hB z := by
  subst h
  rfl

/-! ### The right-factor conjugated-heat Fubini lemma -/

/-- **The Fubini input for the right-factor identity**: for `x` with the `V`-slice in
`L²`, the triple product `(z, w) ↦ V(x, z) · k(z − w) · f w` (with
`k(v) = e^{−av} p_L(v)` the conjugated heat kernel) is
jointly integrable on `ℝ²`.  Tonelli in `z`; the inner `w`-integral is the Young
convolution `(k ⋆ |f|)(z)` (`eLpNorm_conv_le`, `k ≥ 0` integrable); Hölder in `z`.
This is `integrable_bPhiKer_mul` with `ℬ_{L,a}` replaced by
`U_aP_LU_a⁻¹` (whose kernel is exactly `k(z − w)`, so the domination is an equality). -/
theorem integrable_conjHeatKer_right_mul (hL : 0 < L) (a : ℝ) {V : ℝ × ℝ → ℝ}
    (hVmeas : Measurable V) (x : ℝ) (hx : MemLp (fun z => V (x, z)) 2 volume)
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    Integrable (Function.uncurry fun z w : ℝ =>
        V (x, z) * (AiryConj.conjugateHeatKernel L a (z - w) * f w))
      (volume.prod volume) := by
  have hkc := AiryConj.continuous_conjugateHeatKernel L a
  have hmeas : AEStronglyMeasurable (Function.uncurry fun z w : ℝ =>
        V (x, z) * (AiryConj.conjugateHeatKernel L a (z - w) * f w)) (volume.prod volume) :=
    ((hVmeas.comp (measurable_const.prodMk measurable_fst)).aestronglyMeasurable).mul
      ((hkc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f).comp_snd)
  refine ⟨hmeas, ?_⟩
  have hknn : ∀ v : ℝ, 0 ≤ AiryConj.conjugateHeatKernel L a v :=
    AiryConj.conjugateHeatKernel_nonneg hL a
  have hkmeas : AEStronglyMeasurable (AiryConj.conjugateHeatKernel L a) volume :=
    hkc.aestronglyMeasurable
  have hkint : Integrable (AiryConj.conjugateHeatKernel L a) volume :=
    AiryConj.integrable_conjugateHeatKernel hL a
  have hk2 : MemLp (AiryConj.conjugateHeatKernel L a) 2 volume :=
    memLp_conjugateHeatKernel_two hL a
  have hfabs : MemLp (fun w : ℝ => |f w|) 2 volume := (Lp.memLp f).abs
  -- the Young convolution dominator `g = k ⋆ |f|` and its `L²` bound
  set g : ℝ → ℝ := fun z => MeasureTheory.convolution (AiryConj.conjugateHeatKernel L a)
    (fun w => |f w|) (ContinuousLinearMap.mul ℝ ℝ) volume z with hg
  obtain ⟨hgmem, -⟩ := AiryConj.eLpNorm_conv_le (AiryConj.conjugateHeatKernel L a) hkmeas
    hkint hknn (fun w => |f w|) hfabs
  have hgnn : ∀ z : ℝ, 0 ≤ g z := by
    intro z
    rw [hg]
    show (0:ℝ) ≤ MeasureTheory.convolution (AiryConj.conjugateHeatKernel L a)
      (fun w => |f w|) (ContinuousLinearMap.mul ℝ ℝ) volume z
    rw [MeasureTheory.convolution_mul]
    exact integral_nonneg fun t => mul_nonneg (hknn t) (abs_nonneg _)
  have hint_w : ∀ z : ℝ, Integrable
      (fun w : ℝ => AiryConj.conjugateHeatKernel L a (z - w) * |f w|) volume := fun z =>
    MemLp.integrable_mul (hk2.comp_measurePreserving
      (MeasureTheory.Measure.measurePreserving_sub_left volume z)) hfabs
  -- the inner `w`-lintegral equals `ofReal (g z)`
  have hinner : ∀ z : ℝ, (∫⁻ w : ℝ, ENNReal.ofReal (AiryConj.conjugateHeatKernel L a (z - w))
        * ‖f w‖ₑ ∂volume)
      = ENNReal.ofReal (g z) := by
    intro z
    have hpt : ∀ w : ℝ, ENNReal.ofReal (AiryConj.conjugateHeatKernel L a (z - w)) * ‖f w‖ₑ
        = ENNReal.ofReal (AiryConj.conjugateHeatKernel L a (z - w) * |f w|) := by
      intro w
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (hknn _)]
    rw [lintegral_congr hpt, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint_w z)
      (Eventually.of_forall fun w => mul_nonneg (hknn _) (abs_nonneg _))]
    congr 1
    rw [hg]
    show (∫ w : ℝ, AiryConj.conjugateHeatKernel L a (z - w) * |f w|)
      = MeasureTheory.convolution (AiryConj.conjugateHeatKernel L a) (fun w => |f w|)
          (ContinuousLinearMap.mul ℝ ℝ) volume z
    rw [MeasureTheory.convolution_mul]
    have h := MeasureTheory.integral_sub_left_eq_self (μ := volume)
      (fun w : ℝ => AiryConj.conjugateHeatKernel L a w * |f (z - w)|) z
    simp_rw [show ∀ w : ℝ, z - (z - w) = w from fun w => by ring] at h
    exact h
  -- the per-`z` step
  have hstep : ∀ z : ℝ, (∫⁻ w : ℝ, ‖V (x, z)‖ₑ
        * (‖AiryConj.conjugateHeatKernel L a (z - w)‖ₑ * ‖f w‖ₑ) ∂volume)
      ≤ ‖V (x, z)‖ₑ * ENNReal.ofReal (g z) := by
    intro z
    have hBmeas : AEMeasurable (fun w : ℝ =>
          ‖AiryConj.conjugateHeatKernel L a (z - w)‖ₑ * ‖f w‖ₑ) volume :=
      ((hkc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.enorm).mul
        (Lp.aestronglyMeasurable f).enorm
    rw [lintegral_const_mul'' _ hBmeas, ← hinner z]
    apply le_of_eq
    congr 1
    apply lintegral_congr
    intro w
    rw [Real.enorm_eq_ofReal (hknn _)]
  -- the outer Hölder step (in `z`)
  have hVz : AEMeasurable (fun z : ℝ => ‖V (x, z)‖ₑ) volume := hx.aestronglyMeasurable.enorm
  have hgz : AEMeasurable (fun z : ℝ => ENNReal.ofReal (g z)) volume :=
    hgmem.aestronglyMeasurable.enorm.congr
      (Eventually.of_forall fun z => Real.enorm_eq_ofReal (hgnn z))
  have hout : (∫⁻ z : ℝ, ‖V (x, z)‖ₑ * ENNReal.ofReal (g z) ∂volume)
      ≤ (∫⁻ z : ℝ, ‖V (x, z)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)
        * (∫⁻ z : ℝ, (ENNReal.ofReal (g z)) ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hVz hgz
  have hsqV : (eLpNorm (fun z => V (x, z)) 2 volume) ^ (2:ℝ)
      = ∫⁻ z : ℝ, ‖V (x, z)‖ₑ ^ (2:ℝ) ∂volume := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        hx.aestronglyMeasurable, ENNReal.toReal_ofNat, ← ENNReal.rpow_mul,
      show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hVfin : (∫⁻ z : ℝ, ‖V (x, z)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) < ⊤ := by
    rw [← hsqV]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0:ℝ) ≤ 2) hx.eLpNorm_ne_top).ne
  have hsqg : (eLpNorm g 2 volume) ^ (2:ℝ) = ∫⁻ z : ℝ, ‖g z‖ₑ ^ (2:ℝ) ∂volume := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        hgmem.aestronglyMeasurable, ENNReal.toReal_ofNat, ← ENNReal.rpow_mul,
      show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hgfin : (∫⁻ z : ℝ, (ENNReal.ofReal (g z)) ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) < ⊤ := by
    have hB : (∫⁻ z : ℝ, (ENNReal.ofReal (g z)) ^ (2:ℝ) ∂volume)
        = ∫⁻ z : ℝ, ‖g z‖ₑ ^ (2:ℝ) ∂volume := by
      apply lintegral_congr
      intro z
      rw [← Real.enorm_eq_ofReal (hgnn z)]
    rw [hB, ← hsqg]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0:ℝ) ≤ 2) hgmem.eLpNorm_ne_top).ne
  calc (∫⁻ p : ℝ × ℝ, ‖Function.uncurry (fun z w : ℝ =>
          V (x, z) * (AiryConj.conjugateHeatKernel L a (z - w) * f w)) p‖ₑ
          ∂(volume.prod volume))
      = ∫⁻ z : ℝ, ∫⁻ w : ℝ, ‖V (x, z)‖ₑ
          * (‖AiryConj.conjugateHeatKernel L a (z - w)‖ₑ * ‖f w‖ₑ) ∂volume ∂volume := by
        rw [MeasureTheory.lintegral_prod _ hmeas.enorm]
        apply lintegral_congr
        intro z
        apply lintegral_congr
        intro w
        show ‖V (x, z) * (AiryConj.conjugateHeatKernel L a (z - w) * f w)‖ₑ = _
        rw [enorm_mul, enorm_mul]
    _ ≤ ∫⁻ z : ℝ, ‖V (x, z)‖ₑ * ENNReal.ofReal (g z) ∂volume := lintegral_mono hstep
    _ ≤ _ := hout
    _ < ⊤ := ENNReal.mul_lt_top hVfin hgfin

/-- **The right-factor conjugated-heat operator identity**: for an `L²(ℝ²)` kernel `V`,
the operator of `compKernel V (uConj a (heatKerTwo L))` is
`kernelOperator V ∘L conjHeatCLM L hL a`, i.e. `T_V ∘ (U_aP_LU_a⁻¹)`.  This is the
right-factor counterpart of `kernelOperator_compKernel_uConjHeat`
(TwoIntervalMembership.lean) and is proved like `kernelOperator_uphiKer`
(pointwise-a.e. Fubini via `integrable_conjHeatKer_right_mul`). -/
theorem kernelOperator_compKernel_uConjHeat_right (hL : 0 < L) (a : ℝ) {V : ℝ × ℝ → ℝ}
    (hVmeas : Measurable V) (hV : MemLp V 2 (volume.prod volume))
    (hcomp : MemLp (AiryConj.compKernel V (uConj a (heatKerTwo L))) 2 (volume.prod volume)) :
    kernelOperator hcomp = kernelOperator hV ∘L conjHeatCLM L hL a := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae hcomp f,
    kernelOperator_apply_ae hV (conjHeatCLM L hL a f),
    memLp_slice_snd_ae hV] with x hxcomp hxV hxslice
  rw [ContinuousLinearMap.comp_apply, hxcomp, hxV]
  calc (∫ w : ℝ, AiryConj.compKernel V (uConj a (heatKerTwo L)) (x, w) * f w)
      = ∫ w : ℝ, ∫ z : ℝ, V (x, z)
          * (AiryConj.conjugateHeatKernel L a (z - w) * f w) := by
        apply integral_congr_ae
        filter_upwards with w
        show (∫ z : ℝ, V (x, z) * uConj a (heatKerTwo L) (z, w)) * f w = _
        rw [← MeasureTheory.integral_mul_const]
        apply integral_congr_ae
        filter_upwards with z
        rw [uConj_heatKerTwo_eq]
        ring
    _ = ∫ z : ℝ, ∫ w : ℝ, V (x, z)
          * (AiryConj.conjugateHeatKernel L a (z - w) * f w) := by
        exact (MeasureTheory.integral_integral_swap
          (f := fun z w : ℝ => V (x, z) * (AiryConj.conjugateHeatKernel L a (z - w) * f w))
          (integrable_conjHeatKer_right_mul hL a hVmeas x hxslice f)).symm
    _ = ∫ z : ℝ, V (x, z) * (∫ w : ℝ, AiryConj.conjugateHeatKernel L a (z - w) * f w) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [integral_const_mul]
    _ = ∫ z : ℝ, V (x, z) * (conjHeatCLM L hL a f) z := by
        apply integral_congr_ae
        filter_upwards [conjHeatCLM_apply_ae L hL a f] with z hz
        rw [hz]
        rfl

/-! ### The kernel identity `W_{S,a} (U_aP_tU_a⁻¹) = W_{S−t,a}` -/

/-- **The right-factor heat–Airy kernel identity** (QR12 Prop. 1.2 in the form
`P_{-S}B₀P_t = P_{-(S−t)}B₀`, conjugated by `U_a` and weighted by
`Φ⁻¹`): `compKernel (W_{S,a}) (uConj a (heatKerTwo t)) = W_{S−t,a}` for `0 < t ≤ S`.
The `e^{±aw}` factors cancel pointwise and the remaining `w`-integral is
`heatKerTwo_comp_bAiryKer` (= `heatAiryConv_offset`) after the evenness of `p_t`. -/
theorem compKernel_wKernel_uConjHeat {t S : ℝ} (ht : 0 < t) (htS : t ≤ S) (a : ℝ) :
    AiryConj.compKernel (AiryConj.wKernel S a) (uConj a (heatKerTwo t))
      = AiryConj.wKernel (S - t) a := by
  funext p
  obtain ⟨z, y⟩ := p
  show (∫ w : ℝ, AiryConj.wKernel S a (z, w) * uConj a (heatKerTwo t) (w, y))
    = AiryConj.wKernel (S - t) a (z, y)
  have hpt : ∀ w : ℝ, AiryConj.wKernel S a (z, w) * uConj a (heatKerTwo t) (w, y)
      = ((AiryConj.phiWeight z)⁻¹ * Real.exp (a * z) * Real.exp (a * y))
        * (heatKerTwo t (y, w) * bAiryKer S (w, z)) := by
    intro w
    have he : Real.exp (a * w) * Real.exp (-a * w) = 1 := by
      rw [← Real.exp_add, show a * w + -a * w = (0:ℝ) by ring, Real.exp_zero]
    have hh : heatKernel t (w - y) = heatKernel t (y - w) := by
      rw [show w - y = -(y - w) by ring, heatKernel_even]
    unfold AiryConj.wKernel uConj heatKerTwo bAiryKer
    simp only
    rw [hh, show z + w = w + z by ring]
    calc (AiryConj.phiWeight z)⁻¹ * Real.exp (a * z) * backwardAiry S (w + z)
          * Real.exp (a * w) * (Real.exp (-a * w) * heatKernel t (y - w) * Real.exp (a * y))
        = ((AiryConj.phiWeight z)⁻¹ * Real.exp (a * z) * Real.exp (a * y))
          * (heatKernel t (y - w) * backwardAiry S (w + z))
          * (Real.exp (a * w) * Real.exp (-a * w)) := by ring
      _ = _ := by rw [he, mul_one]
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
  have hconv := congrFun (heatKerTwo_comp_bAiryKer (S := S) ht htS) (y, z)
  rw [show (∫ w : ℝ, heatKerTwo t (y, w) * bAiryKer S (w, z))
      = AiryConj.compKernel (heatKerTwo t) (bAiryKer S) (y, z) from rfl, hconv]
  unfold AiryConj.wKernel bAiryKer
  simp only
  rw [show y + z = z + y by ring]
  ring

/-- The `S = 2 + r`, `t = 1 + r` case of `compKernel_wKernel_uConjHeat`:
`W_{2+r,a} (U_aP_{1+r}U_a⁻¹) = W_{1,a}` at kernel level (`S − L = 1`). -/
theorem compKernel_wKernel_two_add_uConjHeat (hr : 0 < r) (a : ℝ) :
    AiryConj.compKernel (AiryConj.wKernel (2 + r) a) (uConj a (heatKerTwo (1 + r)))
      = AiryConj.wKernel 1 a := by
  have h := compKernel_wKernel_uConjHeat (by linarith : (0:ℝ) < 1 + r)
    (by linarith : (1:ℝ) + r ≤ 2 + r) a
  rwa [show (2:ℝ) + r - (1 + r) = 1 by ring] at h

/-- **The operator identity `W_{2+r,a} ∘ (U_aP_{1+r}U_a⁻¹) = W_{1,a}`** — the
`B_{r,a}A_{r,a} = D_aC_a` step of the paper's argument (the factor `U_aQU_aΦ` is carried
separately): `kernelOperator (W_{2+r,a}) ∘L conjHeatCLM (1+r) _ a = kernelOperator (W_{1,a})`. -/
theorem kernelOperator_wKernel_comp_conjHeatCLM (hr : 0 < r) {a : ℝ} (hadr : r + 3 ≤ a) :
    kernelOperator (AiryConj.memLp_wKernel (by linarith : (0:ℝ) < 2 + r)
        (by linarith : 2 + r + 1 ≤ a))
      ∘L conjHeatCLM (1 + r) (by linarith : (0:ℝ) < 1 + r) a
      = kernelOperator (AiryConj.memLp_wKernel one_pos (by linarith : (1:ℝ) + 1 ≤ a)) := by
  have hw1 : MemLp (AiryConj.wKernel 1 a) 2 (volume.prod volume) :=
    AiryConj.memLp_wKernel one_pos (by linarith)
  have hcomp : MemLp (AiryConj.compKernel (AiryConj.wKernel (2 + r) a)
      (uConj a (heatKerTwo (1 + r)))) 2 (volume.prod volume) := by
    rw [compKernel_wKernel_two_add_uConjHeat hr a]
    exact hw1
  rw [← kernelOperator_compKernel_uConjHeat_right (by linarith : (0:ℝ) < 1 + r) a
    (AiryConj.continuous_wKernel (2 + r) a).measurable _ hcomp]
  exact kernelOperator_congr (compKernel_wKernel_two_add_uConjHeat hr a) hcomp _

/-! ### The headline: `det₁(I − K̃₂) = det₁(I − K̃₁)` -/

/-- **The second-block determinant equals the first** (from the proof of the paper's
two-block lemma): for `0 < r`, `0 < M`, `r + 3 ≤ a`, every spectral
parameter `z`, and any `MemLp`/`IsTraceClass` proofs,

  `det₁(1 − z K̃₂) = det₁(1 − z K̃₁)`.

Route (the paper's): `kernelOperator_k2KerT_eq` writes `K̃₂ = (C ∘ V) ∘ W_{2+r}`
(`C = U_aP_{1+r}U_a⁻¹` bounded, `V = V_{1,a}` and `W_{2+r} = W_{2+r,a}` HS); cyclicity
moves `W_{2+r}` to the front; `W_{2+r} ∘ C = W_1`
(`kernelOperator_wKernel_comp_conjHeatCLM`); cyclicity again gives
`V ∘ W_1 = K̃₁` (the one-block factorization). -/
theorem fredholmDetOne_k2KerT_eq_k1KerT (hr : 0 < r) (hM : 0 < M) {a : ℝ}
    (hadr : r + 3 ≤ a)
    (h₁ : MemLp (k1KerT a M) 2 (volume.prod volume))
    (h₂ : MemLp (k2KerT a M r) 2 (volume.prod volume))
    (ht₁ : IsTraceClass (kernelOperator h₁)) (ht₂ : IsTraceClass (kernelOperator h₂))
    (z : ℝ) :
    fredholmDetOne (kernelOperator h₂) ht₂ z = fredholmDetOne (kernelOperator h₁) ht₁ z := by
  have hS : (0:ℝ) < 2 + r := by linarith
  have hL : (0:ℝ) < 1 + r := by linarith
  have hv : MemLp (AiryConj.vKernel 1 a M) 2 (volume.prod volume) :=
    AiryConj.vKernel_memLp one_pos hM (by linarith)
  have hw2 : MemLp (AiryConj.wKernel (2 + r) a) 2 (volume.prod volume) :=
    AiryConj.memLp_wKernel hS (by linarith)
  have hw1 : MemLp (AiryConj.wKernel 1 a) 2 (volume.prod volume) :=
    AiryConj.memLp_wKernel one_pos (by linarith)
  set V := kernelOperator hv with hVdef
  set W₂ := kernelOperator hw2 with hW₂def
  set W₁ := kernelOperator hw1 with hW₁def
  set C := conjHeatCLM (1 + r) hL a with hCdef
  have hVhs : IsHilbertSchmidt V := isHilbertSchmidt_kernelOperator hv
  have hW₂hs : IsHilbertSchmidt W₂ := isHilbertSchmidt_kernelOperator hw2
  have hW₁hs : IsHilbertSchmidt W₁ := isHilbertSchmidt_kernelOperator hw1
  have hCVhs : IsHilbertSchmidt (C ∘L V) := hVhs.comp_left C
  -- `kernelOperator_k2KerT_eq`: `K̃₂ = (C ∘ V) ∘ W₂`
  have hK₂ : kernelOperator h₂ = (C ∘L V) ∘L W₂ := by
    rw [ContinuousLinearMap.comp_assoc]
    exact kernelOperator_k2KerT_eq hr hM hadr
  -- the right-factor identity `W₂ ∘ C = W₁`
  have hWC : W₂ ∘L C = W₁ := kernelOperator_wKernel_comp_conjHeatCLM hr hadr
  have hmid : W₂ ∘L (C ∘L V) = W₁ ∘L V := by
    rw [← ContinuousLinearMap.comp_assoc, hWC]
  -- one-block factorization: `K̃₁ = V ∘ W₁`
  have hK₁ : kernelOperator h₁ = V ∘L W₁ := by
    have hcomp : MemLp (AiryConj.compKernel (AiryConj.vKernel 1 a M) (AiryConj.wKernel 1 a))
        2 (volume.prod volume) :=
      memLp_compKernel (AiryConj.measurable_vKernel 1 a M)
        (AiryConj.continuous_wKernel 1 a).measurable hv hw1
    rw [kernelOperator_congr (k1KerT_eq_compKernel_vKernel_wKernel a M) h₁ hcomp,
      kernelOperator_compKernel hv hw1 hcomp]
  calc fredholmDetOne (kernelOperator h₂) ht₂ z
      = fredholmDetOne ((C ∘L V) ∘L W₂) (IsHilbertSchmidt.isTraceClass_comp hCVhs hW₂hs) z :=
        fredholmDetOne_congr hK₂ _ _ z
    _ = fredholmDetOne (W₂ ∘L (C ∘L V)) (IsHilbertSchmidt.isTraceClass_comp hW₂hs hCVhs) z :=
        fredholmDetOne_cyclic hCVhs hW₂hs z
    _ = fredholmDetOne (W₁ ∘L V) (IsHilbertSchmidt.isTraceClass_comp hW₁hs hVhs) z :=
        fredholmDetOne_congr hmid _ _ z
    _ = fredholmDetOne (V ∘L W₁) (IsHilbertSchmidt.isTraceClass_comp hVhs hW₁hs) z :=
        fredholmDetOne_cyclic hW₁hs hVhs z
    _ = fredholmDetOne (kernelOperator h₁) ht₁ z :=
        fredholmDetOne_congr hK₁.symm _ _ z

/-- **The case `z = 1`, with the standard membership proofs**:
`det(I − K̃₂) = det(I − K̃₁)` for `0 < r`, `0 < M`, `r + 3 ≤ a` — the form consumed by
the `separated` bridge at `a = √(2M)` (where `r + 3 ≤ √(2M)` is the
admissibility condition of the paper's two-block lemma). -/
theorem fredholmDetOne_k2KerT_eq_k1KerT_one (hr : 0 < r) (hM : 0 < M) {a : ℝ}
    (hadr : r + 3 ≤ a) :
    fredholmDetOne (kernelOperator (memLp_k2KerT hr hM hadr))
        (isTraceClass_k2KerT hr hM hadr (memLp_k2KerT hr hM hadr)) 1
      = fredholmDetOne (kernelOperator (memLp_k1KerT hM (by linarith : (2:ℝ) ≤ a)))
        (isTraceClass_k1KerT hM (by linarith : (2:ℝ) ≤ a)
          (memLp_k1KerT hM (by linarith : (2:ℝ) ≤ a))) 1 :=
  fredholmDetOne_k2KerT_eq_k1KerT hr hM hadr _ _ _ _ 1

end AiryTwoInt
