/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoInterval.TwoIntervalMembership

/-!
# Steps 1, 3, 4 of the separated-block estimate, determinant side

Part of the two-interval determinant analysis (`TwoInterval/`): the det₁-linearization
algebra (Step 1 of the proof of the paper's separated-block estimate), the three
Hilbert–Schmidt norm bounds (Step 3), and the `η_{M,r} → 0` remainder assembly (Step 4), all
at **operator level**, ending in the headline `joint_detOne_comb_abs_le`:

  `|(1 − det₁(K̃₁)) − (1 − det₁(K̃₂)) + (1 − det₁(K̃∪)) − Tr C̃_r|`
  `  = |−R(K̃₁) − R(K̃₂) + R(K̃∪)| ≤ C M^K (1+r)^K e^{−2κM^{3/2}}`,

uniformly for `1 ≤ r ≤ χ√(2M)`, `M ≥ M₀(χ)`, with
`κ = 4√2/3` (kept written out as `4 * Real.sqrt 2 / 3`, not a named
constant).

## Correspondence with the paper's proof

* Step 1: `R(H) = det(I−H) − 1 + Tr H` is `detOneLinRem`; the
  three-determinant combination `1 − det₁(K̃₁) − det₁(K̃₂) + det₁(K̃∪)
  = Tr C̃_r + (−R(K̃₁) − R(K̃₂) + R(K̃∪))` is
  `joint_detOne_comb_eq` / `joint_detOne_comb_twoInt_eq`, consuming the
  trace cancellation `trace_twoIntKCup_discharged`.
* Step 3: the HS bounds for `K̃₁` (`twoInt_k1_bounds`),
  `K̃₂` (`twoInt_k2_bounds`), `K̃∪` (`twoInt_kcup_bounds`),
  packaged as `twoInt_stepThree`.
* Step 4: `η_{M,r} := C M^K (1+r)^K e^{-(2/3)a³}`, the
  admissibility threshold `a ≥ 3/(1−χ)` (`exists_admissible_M₀`), the uniform
  `η → 0` (`etaMr_tendsto_zero_uniform`), and `|ℛ_{M,r}| ≤ C M^{K'} (1+r)^{K'}
  e^{-2κM^{3/2}}` (`twoInt_rem_abs_le`).

## Helper lemmas H1–H4

* **H1** `hsENorm_comp_left_le` / `hsNorm_comp_left_le`: the bounded-left-factor HS
  bound replacing the trace-ideal bound `‖AT‖₁ ≤ ‖A‖_{2→2} ‖T‖₁` — the first two
  lines of the `hsENorm_comp_le` proof (FredholmTwo.lean), with the
  `opENorm ≤ hsENorm` step dropped.
* **H2** `kernelOperator_uphiKer`: the operator of the composite kernel
  `uphiKer = compKernel (vKernel T a M) (bPhiKernel L a)` is
  `kernelOperator (vKernel) ∘L bPhiCLM` — the bounded-RIGHT-factor analogue of
  `kernelOperator_compKernel_uConjHeat` (TwoIntervalMembership.lean), with the
  Fubini input (domination
  `|ℬ(z,w)| ≤ k(z−w)` = `bPhiKernel_abs_le`, Young convolution `eLpNorm_conv_le`,
  Hölder in `z`).
* **H3** `hsENorm_kernelOperator_eq`: `hsENorm (kernelOperator hK) = eLpNorm K 2`
  (`hsENorm_kernelOperator` at a countable basis from
  `exists_countable_hilbertBasis_L2R`).
* **H4** `rpow_sqrt_two_mul_cube`: `(√(2M))³ = (2M)^{3/2}` for `0 ≤ M`.

## Scope boundary

The probability identity `P(A∩B) = 1 − det₁(K̃₁) − det₁(K̃₂) + det₁(K̃∪)` (the paper's
joint-exceedance lemma) is an external record of the main package
(`ExternalInputs.lean`) and is NOT formalized here: this module works at
operator level only — the algebraic identity
`1 − det₁(K̃₁) − det₁(K̃₂) + det₁(K̃∪) = Tr C̃_r + ℛ` and the bound on `|ℛ|`.
Step 2 (the `Tr C̃_r` estimates) is handled elsewhere in `TwoInterval/` and not consumed here.

## Remarks on the formalization

* **Remark 1 (Hilbert–Schmidt norms in place of trace norms).**  Every `‖·‖₁` of
  Steps 3–4 is replaced by `hsNorm`; the ideal-property chain
  (`‖AT‖₁ ≤ ‖A‖_{2→2}‖T‖₁`, `‖BC‖₁ ≤ ‖B‖₂‖C‖₂`) becomes H1 +
  `hsNorm_comp_le`; and because the first-order expansion remainder also contains
  `‖trace A‖`, separate `|Tr K̃ᵢ|` bounds are proved via `norm_trace_comp_le`, where
  the trace-norm route has `|Tr H| ≤ ‖H‖₁`.  Same numerics throughout.
* **Remark 2 (remainder shape).**  The bound `|R(H)| ≤ ½‖H‖₁² e^{‖H‖₁}`
  (Simon, Ch. 3) is replaced by the Hilbert–Schmidt form
  `(|tr| + h²)²/2 · e^{|tr|+h²} + h²` under the side condition `h := hsNorm A ≤ 1/2`;
  the side condition is discharged by the
  η-uniformity at `M ≥ M₀(χ)` (for large `M`, `η_{M,r} ≤ 1`).  The final statement is
  the same.
* **Remark 3 (explicit thresholds).**  "For all sufficiently large M"
  becomes explicit `M₀ = 9/(2(1−χ)²)`-type thresholds, existential-packaged.
* **Remark 4 (`χ > (1/2)^{1/3}` unused).**  Steps 1/3/4/5 need only `0 < χ`
  (plus `χ < 1` where the admissibility threshold matters); the stronger hypothesis
  serves the mesoscopic regime and is not propagated.  Where
  the bound route does not even use `χ < 1`, the hypothesis is kept only for
  signature uniformity across `TwoInterval/`.
* **Remark 5 (`r` real).**  The paper's gap is `r ∈ ℕ`, while the contrib
  kernels take a real parameter: everything here is at `r : ℝ`.
* The κ-identity `(2/3)(2M)^{3/2} = (4√2/3) M^{3/2}` is
  duplicated from `TwoIntervalSumEst.kappa_rpow_identity` as a private lemma
  (`kappa_rpow_identity'`) so that the two modules stay import-independent.
* **Statement presentation (no mathematical content).**  The operators are carried
  with their `MemLp`/`IsTraceClass` proofs as explicit ∀-binders (any two choices are
  bridged by `kernelOperator_congr`; this avoids Lean proof-term fragility at
  the consumers).  In `twoInt_stepThree`, `χ` is bound explicitly as `(χ : ℝ)` — the
  statement body does not mention `χ`, so autoImplicit would otherwise default it to
  `ℕ`.  The shared `η` is written inline, not via a `let`.
-/

namespace AiryTwoInt

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal InnerProduct InnerProductSpace
open HilbertSchmidt

/-! ### H1: the bounded-left-factor Hilbert–Schmidt bound -/

/-- **H1 (enorm form)**: `hsENorm (S ∘L T) ≤ ‖S‖ₑ * hsENorm T` — the
bounded-left-factor HS bound replacing the trace-ideal bound `‖AT‖₁ ≤ ‖A‖_{2→2} ‖T‖₁`.  This is the first two lines
of `hsENorm_comp_le`
(`sumSq_comp_le` + the ENNReal rpow algebra), dropping the final `‖S‖ₑ ≤ hsENorm S`
step.  Junk-value safe: if `T` is not HS the right side is `⊤` unless `S = 0`. -/
theorem hsENorm_comp_left_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (S T : E →L[ℝ] E) :
    hsENorm (S ∘L T) ≤ ‖S‖ₑ * hsENorm T := by
  unfold hsENorm
  calc (sumSq (S ∘L T) (canonicalBasis ℝ E)) ^ (1/2 : ℝ)
      ≤ (‖S‖ₑ ^ 2 * sumSq T (canonicalBasis ℝ E)) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow (sumSq_comp_le S T (canonicalBasis ℝ E)) (by norm_num)
    _ = ‖S‖ₑ * (sumSq T (canonicalBasis ℝ E)) ^ (1/2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2), rpow_half_sq']

/-- **H1 (real form)**: `hsNorm (S ∘L T) ≤ ‖S‖ * hsNorm T` for `T` Hilbert–Schmidt
(the `hT` hypothesis keeps the right side finite for the `toReal`). -/
theorem hsNorm_comp_left_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (S T : E →L[ℝ] E) (hT : IsHilbertSchmidt T) :
    hsNorm (S ∘L T) ≤ ‖S‖ * hsNorm T := by
  have hfin : ‖S‖ₑ * hsENorm T ≠ ⊤ := ENNReal.mul_ne_top enorm_ne_top hT
  calc hsNorm (S ∘L T) = (hsENorm (S ∘L T)).toReal := rfl
    _ ≤ (‖S‖ₑ * hsENorm T).toReal := ENNReal.toReal_mono hfin (hsENorm_comp_left_le S T)
    _ = ‖S‖ * hsNorm T := by rw [ENNReal.toReal_mul, toReal_enorm]; rfl

/-! ### H3: the kernel-operator HS norm equality at a countable basis -/

/-- **H3**: `hsENorm (kernelOperator hK) = eLpNorm K 2 (volume.prod volume)` —
`hsENorm_kernelOperator` (KernelHS.lean, which needs a countable Hilbert basis)
instantiated at the countable basis of `L²(ℝ)` from
`exists_countable_hilbertBasis_L2R` (TraceProduct.lean). -/
theorem hsENorm_kernelOperator_eq {K : ℝ × ℝ → ℝ}
    (hK : MemLp K 2 (volume.prod volume)) :
    hsENorm (kernelOperator hK) = eLpNorm K 2 (volume.prod volume) := by
  obtain ⟨ι, hι, ⟨b⟩⟩ := AiryConj.exists_countable_hilbertBasis_L2R
  exact hsENorm_kernelOperator hK b

/-! ### H2: the operator of the `UΦ` composite kernel

The the paper's `UΦ` Hilbert–Schmidt lemma kernel `uphiKer = compKernel (vKernel T a M) (bPhiKernel L a)`
(TwoIntervalMembership.lean) has a bounded *right* factor `ℬ_{L,a}` (not in `L²(ℝ²)`:
its kernel is a convolution kernel), so `kernelOperator_compKernel` does not apply; the
identification `kernelOperator uphiKer = kernelOperator (vKernel) ∘L bPhiCLM` is the
right-factor analogue of `kernelOperator_compKernel_uConjHeat`. -/

/-- **The Fubini input for H2** (mirroring `integrable_uConjHeat_mul`): for
`x` with the `V`-section in `L²`, the triple product `(z, w) ↦ V(x, z) · ℬ(z, w) · f w`
is jointly integrable on `ℝ²`.  Tonelli in `z`, pointwise `|ℬ(z, w)| ≤ k(z − w)`
(`bPhiKernel_abs_le`), the inner `w`-integral is the Young convolution
`(k ⋆ |f|)(z)` (`eLpNorm_conv_le`, the generic form behind the paper's `UΦ` Hilbert–Schmidt
lemma), and the outer
`z`-integral closes by Hölder: `‖V(x, ·)‖₂ · ‖k ⋆ |f|‖₂ < ∞`. -/
theorem integrable_bPhiKer_mul (hL : 0 < L) (a : ℝ) {V : ℝ × ℝ → ℝ}
    (hVmeas : Measurable V) (x : ℝ) (hx : MemLp (fun z => V (x, z)) 2 volume)
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    Integrable (Function.uncurry fun z w : ℝ =>
        V (x, z) * (AiryConj.bPhiKernel L a (z, w) * f w))
      (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun z w : ℝ =>
        V (x, z) * (AiryConj.bPhiKernel L a (z, w) * f w)) (volume.prod volume) :=
    ((hVmeas.comp (measurable_const.prodMk measurable_fst)).aestronglyMeasurable).mul
      ((AiryConj.continuous_bPhiKernel L a).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f).comp_snd)
  refine ⟨hmeas, ?_⟩
  have hknn : ∀ v : ℝ, 0 ≤ AiryConj.kUPhi L a v := AiryConj.kUPhi_nonneg hL a
  have hkmeas : AEStronglyMeasurable (AiryConj.kUPhi L a) volume :=
    (AiryConj.continuous_kUPhi L a).aestronglyMeasurable
  have hkint : Integrable (AiryConj.kUPhi L a) volume := AiryConj.integrable_kUPhi hL a
  have hk2 : MemLp (AiryConj.kUPhi L a) 2 volume := AiryConj.memLp_kUPhi_two hL a
  have hfabs : MemLp (fun w : ℝ => |f w|) 2 volume := (Lp.memLp f).abs
  -- the Young convolution dominator `g = k ⋆ |f|` and its `L²` bound
  set g : ℝ → ℝ := fun z => MeasureTheory.convolution (AiryConj.kUPhi L a)
    (fun w => |f w|) (ContinuousLinearMap.mul ℝ ℝ) volume z with hg
  obtain ⟨hgmem, hgbound⟩ := AiryConj.eLpNorm_conv_le (AiryConj.kUPhi L a) hkmeas hkint
    hknn (fun w => |f w|) hfabs
  have hgnn : ∀ z : ℝ, 0 ≤ g z := by
    intro z
    rw [hg]
    show (0:ℝ) ≤ MeasureTheory.convolution (AiryConj.kUPhi L a) (fun w => |f w|)
      (ContinuousLinearMap.mul ℝ ℝ) volume z
    rw [MeasureTheory.convolution_mul]
    exact integral_nonneg fun t => mul_nonneg (hknn t) (abs_nonneg _)
  have hint_w : ∀ z : ℝ, Integrable (fun w : ℝ => AiryConj.kUPhi L a (z - w) * |f w|)
      volume := fun z =>
    MemLp.integrable_mul (hk2.comp_measurePreserving
      (MeasureTheory.Measure.measurePreserving_sub_left volume z)) hfabs
  -- the inner `w`-lintegral equals `ofReal (g z)`
  have hinner : ∀ z : ℝ, (∫⁻ w : ℝ, ENNReal.ofReal (AiryConj.kUPhi L a (z - w))
        * ‖f w‖ₑ ∂volume)
      = ENNReal.ofReal (g z) := by
    intro z
    have hpt : ∀ w : ℝ, ENNReal.ofReal (AiryConj.kUPhi L a (z - w)) * ‖f w‖ₑ
        = ENNReal.ofReal (AiryConj.kUPhi L a (z - w) * |f w|) := by
      intro w
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (hknn _)]
    rw [lintegral_congr hpt, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint_w z)
      (Eventually.of_forall fun w => mul_nonneg (hknn _) (abs_nonneg _))]
    congr 1
    rw [hg]
    show (∫ w : ℝ, AiryConj.kUPhi L a (z - w) * |f w|)
      = MeasureTheory.convolution (AiryConj.kUPhi L a) (fun w => |f w|)
          (ContinuousLinearMap.mul ℝ ℝ) volume z
    rw [MeasureTheory.convolution_mul]
    have h := MeasureTheory.integral_sub_left_eq_self (μ := volume)
      (fun w : ℝ => AiryConj.kUPhi L a w * |f (z - w)|) z
    simp_rw [show ∀ w : ℝ, z - (z - w) = w from fun w => by ring] at h
    exact h
  -- the per-`z` domination step
  have hstep : ∀ z : ℝ, (∫⁻ w : ℝ, ‖V (x, z)‖ₑ
        * (‖AiryConj.bPhiKernel L a (z, w)‖ₑ * ‖f w‖ₑ) ∂volume)
      ≤ ‖V (x, z)‖ₑ * ENNReal.ofReal (g z) := by
    intro z
    have hBmeas : AEMeasurable (fun w : ℝ =>
          ‖AiryConj.bPhiKernel L a (z, w)‖ₑ * ‖f w‖ₑ) volume :=
      (((AiryConj.continuous_bPhiKernel L a).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable.enorm).mul
        (Lp.aestronglyMeasurable f).enorm
    rw [lintegral_const_mul'' _ hBmeas, ← hinner z]
    apply mul_le_mul_of_nonneg_left _ bot_le
    apply lintegral_mono
    intro w
    apply mul_le_mul_of_nonneg_right _ bot_le
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (AiryConj.bPhiKernel_abs_le hL a z w)
  -- the outer Hölder step (in `z`)
  have hVz : AEMeasurable (fun z : ℝ => ‖V (x, z)‖ₑ) volume := hx.aestronglyMeasurable.enorm
  have hgz : AEMeasurable (fun z : ℝ => ENNReal.ofReal (g z)) volume :=
    hgmem.aestronglyMeasurable.enorm.congr
      (Eventually.of_forall fun z => Real.enorm_eq_ofReal (hgnn z))
  have hout : (∫⁻ z : ℝ, ‖V (x, z)‖ₑ * ENNReal.ofReal (g z) ∂volume)
      ≤ (∫⁻ z : ℝ, ‖V (x, z)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)
        * (∫⁻ z : ℝ, (ENNReal.ofReal (g z)) ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hVz hgz
  -- finiteness of both Hölder factors
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
  -- assemble: Tonelli in `z`, the domination, Hölder, finiteness
  calc (∫⁻ p : ℝ × ℝ, ‖Function.uncurry (fun z w : ℝ =>
          V (x, z) * (AiryConj.bPhiKernel L a (z, w) * f w)) p‖ₑ ∂(volume.prod volume))
      = ∫⁻ z : ℝ, ∫⁻ w : ℝ, ‖V (x, z)‖ₑ
          * (‖AiryConj.bPhiKernel L a (z, w)‖ₑ * ‖f w‖ₑ) ∂volume ∂volume := by
        rw [MeasureTheory.lintegral_prod _ hmeas.enorm]
        apply lintegral_congr
        intro z
        apply lintegral_congr
        intro w
        show ‖V (x, z) * (AiryConj.bPhiKernel L a (z, w) * f w)‖ₑ = _
        rw [enorm_mul, enorm_mul]
    _ ≤ ∫⁻ z : ℝ, ‖V (x, z)‖ₑ * ENNReal.ofReal (g z) ∂volume := lintegral_mono hstep
    _ ≤ (∫⁻ z : ℝ, ‖V (x, z)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)
          * (∫⁻ z : ℝ, (ENNReal.ofReal (g z)) ^ (2:ℝ) ∂volume) ^ (1/2:ℝ) := hout
    _ < ⊤ := ENNReal.mul_lt_top hVfin hgfin

/-- **H2**: the operator of the `UΦ` composite kernel `uphiKer T a M L`
(`compKernel (vKernel T a M) (bPhiKernel L a)`, TwoIntervalMembership.lean) is
`kernelOperator (vKernel) ∘L bPhiCLM L hL a` (the paper's
factorization `U_a Q_{M,T} P_L U_a Φ = (U_aQU_aΦ) ∘ ℬ_{L,a}`).
Proof: pointwise-a.e. Fubini via `integrable_bPhiKer_mul`, mirroring
`kernelOperator_compKernel_uConjHeat` line by line. -/
theorem kernelOperator_uphiKer (T a M L : ℝ) (hT : 0 < T) (hM : 0 < M)
    (hL : 0 < L) (ha : T + 1 ≤ a) :
    kernelOperator (memLp_uphiKer T a M L hT hM hL ha)
      = kernelOperator (AiryConj.memLp_vKernel T a M hT hM ha) ∘L AiryConj.bPhiCLM L hL a := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae (memLp_uphiKer T a M L hT hM hL ha) f,
    kernelOperator_apply_ae (AiryConj.memLp_vKernel T a M hT hM ha) (AiryConj.bPhiCLM L hL a f),
    memLp_slice_snd_ae (AiryConj.memLp_vKernel T a M hT hM ha)] with x hxcomp hxV hxslice
  rw [ContinuousLinearMap.comp_apply, hxcomp, hxV]
  calc (∫ w : ℝ, uphiKer T a M L (x, w) * f w)
      = ∫ w : ℝ, ∫ z : ℝ, AiryConj.vKernel T a M (x, z)
          * (AiryConj.bPhiKernel L a (z, w) * f w) := by
        apply integral_congr_ae
        filter_upwards with w
        rw [show uphiKer T a M L (x, w)
            = ∫ z : ℝ, AiryConj.vKernel T a M (x, z) * AiryConj.bPhiKernel L a (z, w) from rfl]
        rw [← MeasureTheory.integral_mul_const]
        apply integral_congr_ae
        filter_upwards with z
        ring
    _ = ∫ z : ℝ, ∫ w : ℝ, AiryConj.vKernel T a M (x, z)
          * (AiryConj.bPhiKernel L a (z, w) * f w) := by
        exact (MeasureTheory.integral_integral_swap
          (f := fun z w : ℝ => AiryConj.vKernel T a M (x, z)
            * (AiryConj.bPhiKernel L a (z, w) * f w))
          (integrable_bPhiKer_mul hL a (AiryConj.measurable_vKernel T a M) x hxslice f)).symm
    _ = ∫ z : ℝ, AiryConj.vKernel T a M (x, z)
          * (∫ w : ℝ, AiryConj.bPhiKernel L a (z, w) * f w) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [integral_const_mul]
    _ = ∫ z : ℝ, AiryConj.vKernel T a M (x, z) * (AiryConj.bPhiCLM L hL a f) z := by
        apply integral_congr_ae
        filter_upwards [AiryConj.bPhiCLM_apply_ae L hL a f] with z hz
        rw [hz]
        rfl

/-! ### The operator identifications (O1, O2, O3) -/

/-- **O1**: `K̃₁`'s operator at `T = 1` is the one-block operator `airyTildeOp M 1 a`
(the one-block Step-3 template, TraceExpansion.lean). -/
theorem kernelOperator_k1KerT_eq_airyTildeOp (hM : 0 < M) {a : ℝ} (ha : 2 ≤ a) :
    kernelOperator (memLp_k1KerT hM ha)
      = AiryConj.airyTildeOp M 1 a one_pos hM (by linarith : (1:ℝ) + 1 ≤ a) := by
  have hv : MemLp (AiryConj.vKernel 1 a M) 2 (volume.prod volume) :=
    AiryConj.vKernel_memLp one_pos hM (by linarith)
  have hw : MemLp (AiryConj.wKernel 1 a) 2 (volume.prod volume) :=
    AiryConj.memLp_wKernel one_pos (by linarith)
  have hcomp : MemLp (AiryConj.compKernel (AiryConj.vKernel 1 a M) (AiryConj.wKernel 1 a)) 2
      (volume.prod volume) :=
    memLp_compKernel (AiryConj.measurable_vKernel 1 a M)
      (AiryConj.continuous_wKernel 1 a).measurable hv hw
  rw [kernelOperator_congr (k1KerT_eq_compKernel_vKernel_wKernel a M) _ hcomp,
    kernelOperator_compKernel hv hw hcomp]
  rfl

/-- **O2**: `K̃₂`'s operator is `(U_aP_LU_a⁻¹) ∘L (kV ∘L kW)` with `L = 1 + r` —
from `k2KerT_eq_compKernel` +
`kernelOperator_compKernel_uConjHeat` + `kernelOperator_compKernel`. -/
theorem kernelOperator_k2KerT_eq (hr : 0 < r) (hM : 0 < M) {a : ℝ} (hadr : r + 3 ≤ a) :
    kernelOperator (memLp_k2KerT hr hM hadr)
      = conjHeatCLM (1 + r) (by linarith : (0:ℝ) < 1 + r) a
        ∘L (kernelOperator (AiryConj.vKernel_memLp one_pos hM (by linarith : (1:ℝ)+1 ≤ a))
            ∘L kernelOperator (AiryConj.memLp_wKernel (by linarith : (0:ℝ) < 2 + r)
              (by linarith : 2 + r + 1 ≤ a))) := by
  have hS : (0:ℝ) < 2 + r := by linarith
  have hL : (0:ℝ) < 1 + r := by linarith
  have hv : MemLp (AiryConj.vKernel 1 a M) 2 (volume.prod volume) :=
    AiryConj.vKernel_memLp one_pos hM (by linarith)
  have hw : MemLp (AiryConj.wKernel (2 + r) a) 2 (volume.prod volume) :=
    AiryConj.memLp_wKernel hS (by linarith)
  have hG : MemLp (AiryConj.compKernel (AiryConj.vKernel 1 a M) (AiryConj.wKernel (2 + r) a)) 2
      (volume.prod volume) :=
    memLp_compKernel (AiryConj.measurable_vKernel 1 a M)
      (AiryConj.continuous_wKernel (2 + r) a).measurable hv hw
  have hcomp : MemLp (AiryConj.compKernel (uConj a (heatKerTwo (1 + r)))
      (AiryConj.compKernel (AiryConj.vKernel 1 a M) (AiryConj.wKernel (2 + r) a))) 2
      (volume.prod volume) :=
    memLp_compKernel_uConjHeat hL a
      (measurable_compKernel (AiryConj.measurable_vKernel 1 a M)
        (AiryConj.continuous_wKernel (2 + r) a).measurable) hG
  rw [kernelOperator_congr (k2KerT_eq_compKernel a M r) _ hcomp,
    kernelOperator_compKernel_uConjHeat hL a hG hcomp, kernelOperator_compKernel hv hw hG]

/-- **O3**: `K̃∪`'s operator is `kVdR ∘L kWS` — from
`kcupKerT_eq_compKernel_vdRKer_wSKer` + `kernelOperator_compKernel`. -/
theorem kernelOperator_kcupKerT_eq_comp (hr : 0 < r) (hM : 0 < M) {a : ℝ}
    (hadr : r + 3 ≤ a) :
    kernelOperator (memLp_kcupKerT hr hM hadr)
      = kernelOperator (memLp_vdRKer hr hM hadr)
        ∘L kernelOperator (memLp_wSKer hr hadr) := by
  have hV : MemLp (vdRKer a M r) 2 (volume.prod volume) := memLp_vdRKer hr hM hadr
  have hW : MemLp (wSKer (2 + r) a) 2 (volume.prod volume) := memLp_wSKer hr hadr
  have hcomp : MemLp (AiryConj.compKernel (vdRKer a M r) (wSKer (2 + r) a)) 2
      (volume.prod volume) :=
    (memLp_congr_ae (Eventually.of_forall fun p =>
      congrFun (kcupKerT_eq_compKernel_vdRKer_wSKer a M r) p)).mp (memLp_kcupKerT hr hM hadr)
  rw [kernelOperator_congr (kcupKerT_eq_compKernel_vdRKer_wSKer a M r) _ hcomp,
    kernelOperator_compKernel hV hW hcomp]

/-! ### H4 and the polynomial-absorption helpers (Step-4 numerics) -/

/-- **H4**: `(√(2M))³ = (2M)^{3/2}` for `0 ≤ M` (the `a³ = (2M)^{3/2}` step
`(2/3)a³ = (2/3)(2M)^{3/2} = κM^{3/2}`). -/
theorem rpow_sqrt_two_mul_cube {M : ℝ} (hM : 0 ≤ M) :
    (Real.sqrt (2*M))^3 = (2*M)^(3/2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((2*M)^(1/2 : ℝ)) 3,
    ← Real.rpow_mul (mul_nonneg (by norm_num) hM),
    show ((1/2 : ℝ) * ((3:ℕ):ℝ)) = 3/2 from by norm_num]

/-- Private copy of `TwoIntervalSumEst.kappa_rpow_identity`, so
the two modules stay import-independent:
`(2/3)·(2M)^{3/2} = (4√2/3)·M^{3/2}` for `0 ≤ M`. -/
private theorem kappa_rpow_identity' {M : ℝ} (hM : 0 ≤ M) :
    (2/3) * (2*M)^(3/2 : ℝ) = (4 * Real.sqrt 2 / 3) * M^(3/2 : ℝ) := by
  have h2 : (2:ℝ)^(3/2 : ℝ) = 2 * Real.sqrt 2 := by
    rw [show (3/2 : ℝ) = 1 + 1/2 from by norm_num, Real.rpow_add (by norm_num),
      Real.rpow_one, Real.sqrt_eq_rpow]
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hM, h2]
  ring

/-- For `1 ≤ M` and `a = √(2M)`: `√(1 + a³) ≤ 2·M^{3/4}` — with H4,
`a³ = (2M)^{3/2} = 2√2·M^{3/2} ≤ 3·M^{3/2}`, so `1 + a³ ≤ 4·M^{3/2}` and
`√(4·M^{3/2}) = 2·M^{3/4}`.  (Loose constants: the packaging is existential.) -/
private theorem sqrt_one_add_a_cube_le {M : ℝ} (hM : 1 ≤ M) {a : ℝ}
    (haeq : a = Real.sqrt (2*M)) :
    Real.sqrt (1 + a^3) ≤ 2 * M^(3/4 : ℝ) := by
  have hM0 : (0:ℝ) < M := by linarith
  have ha3 : a^3 = (2*M)^(3/2 : ℝ) := by
    rw [haeq]
    exact rpow_sqrt_two_mul_cube (by linarith)
  have h2sqrt : (2:ℝ)^(3/2 : ℝ) = 2 * Real.sqrt 2 := by
    rw [show (3/2 : ℝ) = 1 + 1/2 from by norm_num, Real.rpow_add (by norm_num),
      Real.rpow_one, Real.sqrt_eq_rpow]
  have hsqrt2 : Real.sqrt 2 ≤ 3/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hM32 : (1:ℝ) ≤ M^(3/2 : ℝ) := Real.one_le_rpow hM (by norm_num)
  have hbound : 1 + a^3 ≤ 4 * M^(3/2 : ℝ) := by
    rw [ha3, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hM0.le, h2sqrt]
    nlinarith [hsqrt2, Real.sqrt_nonneg 2, hM32, Real.rpow_nonneg hM0.le (3/2 : ℝ)]
  calc Real.sqrt (1 + a^3) ≤ Real.sqrt (4 * M^(3/2 : ℝ)) := Real.sqrt_le_sqrt hbound
    _ = 2 * M^(3/4 : ℝ) := by
        have h4 : Real.sqrt (4:ℝ) = 2 := by
          rw [show (4:ℝ) = 2^2 from by norm_num]
          exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) (M^(3/2 : ℝ)), h4,
          Real.sqrt_eq_rpow, ← Real.rpow_mul hM0.le,
          show ((3/2 : ℝ) * (1/2) = 3/4) from by norm_num]

/-- `(1 + M)·√(1+a³) ≤ 8·M^{7/4} ≤ 8·M^{4}` for `1 ≤ M`, `a = √(2M)` (the polynomial factor of the
Hilbert–Schmidt bound for `V` absorbed into the existential `M^K` packaging). -/
private theorem one_add_mul_sqrt_one_add_a_cube_le {M : ℝ} (hM : 1 ≤ M) {a : ℝ}
    (haeq : a = Real.sqrt (2*M)) :
    (1 + M) * Real.sqrt (1 + a^3) ≤ 8 * M^(4 : ℝ) := by
  have hM0 : (0:ℝ) < M := by linarith
  have h1 : 1 + M ≤ 2 * M := by linarith
  have h2 := sqrt_one_add_a_cube_le hM haeq
  have h3 : (1 + M) * Real.sqrt (1 + a^3) ≤ (2*M) * (2 * M^(3/4 : ℝ)) :=
    mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by linarith : (0:ℝ) ≤ 2 * M)
  have h4 : (2*M) * (2 * M^(3/4 : ℝ)) = 4 * M^(7/4 : ℝ) := by
    rw [show (7/4 : ℝ) = 1 + 3/4 from by norm_num, Real.rpow_add hM0, Real.rpow_one]
    ring
  have h5 : M^(7/4 : ℝ) ≤ M^(4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM (by norm_num)
  calc (1 + M) * Real.sqrt (1 + a^3) ≤ 4 * M^(7/4 : ℝ) := by linarith [h3, h4]
    _ ≤ 4 * M^(4 : ℝ) := by
        exact mul_le_mul_of_nonneg_left h5 (by norm_num : (0:ℝ) ≤ 4)
    _ ≤ 8 * M^(4 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by norm_num : (4:ℝ) ≤ 8)
          (Real.rpow_nonneg hM0.le _)


/-! ### Step 3: shared packaging and the three operator bounds -/

/-- The `hsNorm` bound for a `vKernel` operator at temperature `T` from a square-integral
bound for `V` (the toReal form of `eLpNorm_vKernel_le_of_bound`):
`hsNorm kV ≤ √C · (1+M) · √(1+a³) · e^{T a² − 2Ma}`. -/
private theorem hsNorm_vKernel_le_of {T M a : ℝ} (hT : 0 < T) (hM : 0 < M)
    (ha : T + 1 ≤ a) {C : ℝ} (hC : 0 < C)
    (hbound : ∫ p : ℝ × ℝ, (AiryConj.vKernel T a M p)^2 ∂(volume.prod volume) ≤
      C * (1+M)^2 * (1+a^3) * Real.exp (2*T*a^2 - 4*M*a)) :
    hsNorm (kernelOperator (AiryConj.vKernel_memLp hT hM ha))
      ≤ Real.sqrt C * (1 + M) * Real.sqrt (1 + a^3) * Real.exp (T*a^2 - 2*M*a) := by
  have hV := AiryConj.eLpNorm_vKernel_le_of_bound T a M hT hM ha hC hbound
  have hle := (hsENorm_kernelOperator_le (AiryConj.vKernel_memLp hT hM ha)).trans hV
  have hnn : (0:ℝ) ≤ Real.sqrt C * (1 + M) * Real.sqrt (1 + a^3) * Real.exp (T*a^2 - 2*M*a) := by
    have h1 : (0:ℝ) ≤ Real.sqrt C := Real.sqrt_nonneg _
    have h2 : (0:ℝ) ≤ 1 + M := by linarith
    have h3 : (0:ℝ) ≤ Real.sqrt (1 + a^3) := Real.sqrt_nonneg _
    have h4 : (0:ℝ) ≤ Real.exp (T*a^2 - 2*M*a) := (Real.exp_pos _).le
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  calc hsNorm (kernelOperator (AiryConj.vKernel_memLp hT hM ha))
      = (hsENorm (kernelOperator (AiryConj.vKernel_memLp hT hM ha))).toReal := rfl
    _ ≤ (ENNReal.ofReal (Real.sqrt C * (1 + M) * Real.sqrt (1 + a^3)
          * Real.exp (T*a^2 - 2*M*a))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = Real.sqrt C * (1 + M) * Real.sqrt (1 + a^3) * Real.exp (T*a^2 - 2*M*a) :=
        ENNReal.toReal_ofReal hnn

/-- The `hsNorm` bound for a `wKernel` operator at temperature `T` from a the Hilbert–Schmidt bound for 
square-integral bound: `hsNorm kW ≤ √C · e^{a³/3 − T a²}`. -/
private theorem hsNorm_wKernel_le_of {T a : ℝ} (hT : 0 < T) (ha : T + 1 ≤ a)
    {C : ℝ} (hC : 0 < C)
    (hint : Integrable (fun p : ℝ × ℝ => (AiryConj.wKernel T a p)^2) (volume.prod volume))
    (hbound : ∫ p : ℝ × ℝ, (AiryConj.wKernel T a p)^2 ∂(volume.prod volume) ≤
      C * Real.exp ((2/3)*a^3 - 2*T*a^2)) :
    hsNorm (kernelOperator (AiryConj.memLp_wKernel hT ha))
      ≤ Real.sqrt C * Real.exp (a^3/3 - T*a^2) := by
  calc hsNorm (kernelOperator (AiryConj.memLp_wKernel hT ha))
      ≤ Real.sqrt (∫ p : ℝ × ℝ, (AiryConj.wKernel T a p)^2 ∂(volume.prod volume)) :=
        AiryConj.hsNorm_kernelOperator_le_sqrt _ hint
    _ ≤ Real.sqrt (C * Real.exp ((2/3)*a^3 - 2*T*a^2)) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt C * Real.exp (a^3/3 - T*a^2) := by
        rw [Real.sqrt_mul hC.le, Real.sqrt_eq_rpow (Real.exp ((2/3)*a^3 - 2*T*a^2)),
          ← Real.exp_mul]
        congr 1
        congr 1
        ring

/-- **The packaging step** (shared by the three Step-3 operator bounds): from an
input of the shape `bnd ≤ Cop · (1+M)·√(1+a³) · e^{a³/3−2Ma}` with `0 ≤ Cop ≤ Ctop`,
conclude `bnd ≤ 8·Ctop·M⁴·(1+r)⁴·e^{−(2/3)a³}` at `a = √(2M)` (the exponent identity
`a³/3 − 2Ma = −(2/3)a³`, the polynomial absorption
`(1+M)√(1+a³) ≤ 8·M⁴`, and `(1+r)⁴ ≥ 1`). -/
private theorem le_packaged_of_le {M r : ℝ} (hM1 : 1 ≤ M) (hr1 : 1 ≤ r) {a : ℝ}
    (haeq : a = Real.sqrt (2*M)) {Cop Ctop : ℝ} (hCop : 0 ≤ Cop) (hCopC : Cop ≤ Ctop)
    (hCtop : 0 ≤ Ctop) {bnd : ℝ}
    (hb : bnd ≤ Cop * (1+M) * Real.sqrt (1+a^3) * Real.exp (a^3/3 - 2*M*a)) :
    bnd ≤ 8 * Ctop * M^(4:ℝ) * (1+r)^(4:ℝ) * Real.exp (-(2/3)*a^3) := by
  have hM : 0 < M := by linarith
  have hMnn : (0:ℝ) ≤ M := hM.le
  have ha2eq : a^2 = 2*M := by rw [haeq]; exact Real.sq_sqrt (by linarith)
  have hexp : a^3/3 - 2*M*a = -(2/3)*a^3 := by
    have h1 : a^3 = 2*M*a := by
      rw [show a^3 = a^2 * a from by ring, ha2eq]
    linarith [h1]
  have hpoly := one_add_mul_sqrt_one_add_a_cube_le hM1 haeq
  have hexpnn : (0:ℝ) ≤ Real.exp (-(2/3)*a^3) := (Real.exp_pos _).le
  have hM4nn : (0:ℝ) ≤ M^(4:ℝ) := Real.rpow_nonneg hMnn _
  have h14 : (1:ℝ) ≤ (1+r)^(4:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  calc bnd ≤ Cop * (1+M) * Real.sqrt (1+a^3) * Real.exp (a^3/3 - 2*M*a) := hb
    _ = Cop * ((1+M) * Real.sqrt (1+a^3)) * Real.exp (a^3/3 - 2*M*a) := by ring
    _ ≤ Cop * (8 * M^(4:ℝ)) * Real.exp (a^3/3 - 2*M*a) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hpoly hCop
    _ ≤ Ctop * (8 * M^(4:ℝ)) * Real.exp (a^3/3 - 2*M*a) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have h8 : (0:ℝ) ≤ 8 := by norm_num
        exact mul_le_mul_of_nonneg_right hCopC (mul_nonneg h8 hM4nn)
    _ = Ctop * (8 * M^(4:ℝ)) * Real.exp (-(2/3)*a^3) := by rw [hexp]
    _ ≤ (Ctop * (8 * M^(4:ℝ)) * Real.exp (-(2/3)*a^3)) * (1+r)^(4:ℝ) := by
        have h8M : (0:ℝ) ≤ 8 * M^(4:ℝ) := mul_nonneg (by norm_num) hM4nn
        have hnn : (0:ℝ) ≤ Ctop * (8 * M^(4:ℝ)) * Real.exp (-(2/3)*a^3) :=
          mul_nonneg (mul_nonneg hCtop h8M) hexpnn
        exact le_mul_of_one_le_right hnn h14
    _ = 8 * Ctop * M^(4:ℝ) * (1+r)^(4:ℝ) * Real.exp (-(2/3)*a^3) := by ring

/-- **Step 3 for K̃₁** (HS form, Remark 1): with
O1 (`kernelOperator_k1KerT_eq_airyTildeOp`), the one-block template
`hsNorm_airyTilde_le` gives `hsNorm K̃₁ ≤ C(1+M)√(1+a³) e^{a³/3−2Ma}`; the trace bound
`|Tr K̃₁| ≤ hsNorm kV · hsNorm kW` (`norm_trace_comp_le`, replacing the
paper's free `|Tr H| ≤ ‖H‖₁`) has the same form. -/
theorem twoInt_k1_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {M r a : ℝ} (hM1 : 1 ≤ M) (hr1 : 1 ≤ r) (hadr : r + 3 ≤ a)
      (haeq : a = Real.sqrt (2*M)) (hk : MemLp (k1KerT a M) 2 (volume.prod volume)),
      |trace (kernelOperator hk)| ≤ C * M^(4:ℝ) * (1+r)^(4:ℝ) * Real.exp (-(2/3)*a^3) ∧
      hsNorm (kernelOperator hk) ≤ C * M^(4:ℝ) * (1+r)^(4:ℝ) * Real.exp (-(2/3)*a^3) := by
  obtain ⟨C₁, hC₁, H₁⟩ := AiryConj.hsNorm_airyTilde_le 1 one_pos
  obtain ⟨CV, hCV, HV⟩ := AiryConj.vKernel_sq_integral_le 1 one_pos
  obtain ⟨CW, hCW, HW⟩ := AiryConj.wKernel_sq_integral_le
  have hCtop : (0:ℝ) ≤ C₁ + Real.sqrt (CV*CW) :=
    add_nonneg hC₁.le (Real.sqrt_nonneg _)
  refine ⟨8 * (C₁ + Real.sqrt (CV*CW)), by positivity, fun {M r a} hM1 hr1 hadr haeq hk => ?_⟩
  have hM : 0 < M := by linarith
  have ha2 : 2 ≤ a := by linarith
  have ha1 : (1:ℝ) + 1 ≤ a := by linarith
  -- identify the operator with the one-block operator (O1)
  have hcongr : kernelOperator hk = kernelOperator (memLp_k1KerT hM ha2) :=
    kernelOperator_congr rfl hk (memLp_k1KerT hM ha2)
  rw [hcongr, kernelOperator_k1KerT_eq_airyTildeOp hM ha2]
  -- the hsNorm bound (template)
  have hHS : hsNorm (AiryConj.airyTildeOp M 1 a one_pos hM ha1)
      ≤ C₁ * (1+M) * Real.sqrt (1+a^3) * Real.exp (a^3/3 - 2*M*a) := H₁ M a hM ha1
  -- the trace bound: `|Tr (kV ∘L kW)| ≤ hsNorm kV · hsNorm kW`
  have hv : MemLp (AiryConj.vKernel 1 a M) 2 (volume.prod volume) :=
    AiryConj.vKernel_memLp one_pos hM ha1
  have hw : MemLp (AiryConj.wKernel 1 a) 2 (volume.prod volume) :=
    AiryConj.memLp_wKernel one_pos ha1
  have hsV := hsNorm_vKernel_le_of one_pos hM ha1 hCV (HV M a hM ha1).2
  have hsW := hsNorm_wKernel_le_of one_pos ha1 hCW (HW 1 a one_pos ha1).1 (HW 1 a one_pos ha1).2
  have hTR : |trace (AiryConj.airyTildeOp M 1 a one_pos hM ha1)|
      ≤ hsNorm (kernelOperator hv) * hsNorm (kernelOperator hw) := by
    have h := norm_trace_comp_le (isHilbertSchmidt_kernelOperator hv)
      (isHilbertSchmidt_kernelOperator hw)
    rw [Real.norm_eq_abs] at h
    calc |trace (AiryConj.airyTildeOp M 1 a one_pos hM ha1)|
        = |trace (kernelOperator hv ∘L kernelOperator hw)| := rfl
      _ ≤ hsNorm (kernelOperator hv) * hsNorm (kernelOperator hw) := h
  have hTR2 : |trace (AiryConj.airyTildeOp M 1 a one_pos hM ha1)|
      ≤ Real.sqrt (CV*CW) * (1+M) * Real.sqrt (1+a^3) * Real.exp (a^3/3 - 2*M*a) := by
    calc |trace (AiryConj.airyTildeOp M 1 a one_pos hM ha1)|
        ≤ hsNorm (kernelOperator hv) * hsNorm (kernelOperator hw) := hTR
      _ ≤ (Real.sqrt CV * (1+M) * Real.sqrt (1+a^3) * Real.exp (1*a^2 - 2*M*a))
            * (Real.sqrt CW * Real.exp (a^3/3 - 1*a^2)) := by
          have h2 : (0:ℝ) ≤ 1 + M := by linarith [hM.le]
          have hbnn : (0:ℝ) ≤ Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)
              * Real.exp (1*a^2 - 2*M*a) :=
            mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h2)
              (Real.sqrt_nonneg _)) (Real.exp_pos _).le
          exact mul_le_mul hsV hsW (hsNorm_nonneg _) hbnn
      _ = Real.sqrt (CV*CW) * (1+M) * Real.sqrt (1+a^3) * Real.exp (a^3/3 - 2*M*a) := by
          have hz : Real.exp (1*a^2 - 2*M*a) * Real.exp (a^3/3 - 1*a^2)
              = Real.exp (a^3/3 - 2*M*a) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [Real.sqrt_mul hCV.le, ← hz]
          ring
  refine ⟨?_, ?_⟩
  · exact le_packaged_of_le hM1 hr1 haeq (Real.sqrt_nonneg _)
      (by linarith [hC₁.le] : Real.sqrt (CV*CW) ≤ C₁ + Real.sqrt (CV*CW)) hCtop hTR2
  · exact le_packaged_of_le hM1 hr1 haeq hC₁.le
      (by linarith [Real.sqrt_nonneg (CV*CW)] : C₁ ≤ C₁ + Real.sqrt (CV*CW)) hCtop hHS

/-- **Step 3 for K̃₂** (HS form, Remark 1): with O2
(`kernelOperator_k2KerT_eq`), H1 (`hsNorm_comp_left_le`) replaces
`‖AT‖₁ ≤ ‖A‖_{2→2}‖T‖₁`, the `L² → L²` conjugation lemma (`enorm_conjHeatCLM_le`) gives
`‖B‖ ≤ e^{(1+r)a²}`, and the Hilbert–Schmidt bounds for `V` and `W` give the rest; the exponent is
`(1+r)a² + (a²−2Ma) + (a³/3−(2+r)a²) = a³/3 − 2Ma` (the `La² + a² − Sa² = 0`
cancellation).  The trace bound `|Tr K̃₂| ≤ hsNorm (B∘kV)·hsNorm kW`
(replacing the free `|Tr H| ≤ ‖H‖₁`) has the same form. -/
theorem twoInt_k2_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {M r a : ℝ} (hM1 : 1 ≤ M) (hr1 : 1 ≤ r) (hadr : r + 3 ≤ a)
      (haeq : a = Real.sqrt (2*M)) (hk : MemLp (k2KerT a M r) 2 (volume.prod volume)),
      |trace (kernelOperator hk)| ≤ C * M^(4:ℝ) * (1+r)^(4:ℝ) * Real.exp (-(2/3)*a^3) ∧
      hsNorm (kernelOperator hk) ≤ C * M^(4:ℝ) * (1+r)^(4:ℝ) * Real.exp (-(2/3)*a^3) := by
  obtain ⟨CV, hCV, HV⟩ := AiryConj.vKernel_sq_integral_le 1 one_pos
  obtain ⟨CW, hCW, HW⟩ := AiryConj.wKernel_sq_integral_le
  have hCtop : (0:ℝ) ≤ Real.sqrt (CV*CW) := Real.sqrt_nonneg _
  refine ⟨8 * Real.sqrt (CV*CW), by positivity, fun {M r a} hM1 hr1 hadr haeq hk => ?_⟩
  have hM : 0 < M := by linarith
  have hr : 0 < r := by linarith
  have ha1 : (1:ℝ) + 1 ≤ a := by linarith
  have hL : (0:ℝ) < 1 + r := by linarith
  have hS : (0:ℝ) < 2 + r := by linarith
  have hSa : 2 + r + 1 ≤ a := by linarith
  -- the factors with our own proof terms
  have hv : MemLp (AiryConj.vKernel 1 a M) 2 (volume.prod volume) :=
    AiryConj.vKernel_memLp one_pos hM ha1
  have hw : MemLp (AiryConj.wKernel (2 + r) a) 2 (volume.prod volume) :=
    AiryConj.memLp_wKernel hS hSa
  have hcongr : kernelOperator hk = kernelOperator (memLp_k2KerT hr hM hadr) :=
    kernelOperator_congr rfl hk (memLp_k2KerT hr hM hadr)
  have heq : kernelOperator hk
      = conjHeatCLM (1 + r) hL a ∘L (kernelOperator hv ∘L kernelOperator hw) :=
    hcongr.trans (kernelOperator_k2KerT_eq hr hM hadr)
  rw [heq]
  -- the factor bounds
  have hBnorm : ‖conjHeatCLM (1 + r) hL a‖ ≤ Real.exp ((1+r) * a^2) := by
    have h := enorm_conjHeatCLM_le (1 + r) hL a
    calc ‖conjHeatCLM (1 + r) hL a‖ = (‖conjHeatCLM (1 + r) hL a‖ₑ).toReal :=
          (toReal_enorm _).symm
      _ ≤ (ENNReal.ofReal (Real.exp ((1+r) * a^2))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = Real.exp ((1+r) * a^2) := ENNReal.toReal_ofReal (Real.exp_pos _).le
  have hsV := hsNorm_vKernel_le_of one_pos hM ha1 hCV (HV M a hM ha1).2
  have hsW := hsNorm_wKernel_le_of hS hSa hCW (HW (2+r) a hS hSa).1 (HW (2+r) a hS hSa).2
  have h2 : (0:ℝ) ≤ 1 + M := by linarith [hM.le]
  have hbnnV : (0:ℝ) ≤ Real.sqrt CV * (1+M) * Real.sqrt (1+a^3) * Real.exp (1*a^2 - 2*M*a) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h2) (Real.sqrt_nonneg _))
      (Real.exp_pos _).le
  -- the product-of-factors bound, with the exponent cancellation
  have hexp3 : Real.exp ((1+r) * a^2) * (Real.exp (1*a^2 - 2*M*a) * Real.exp (a^3/3 - (2+r)*a^2))
      = Real.exp (a^3/3 - 2*M*a) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hfactor : ‖conjHeatCLM (1 + r) hL a‖ * (hsNorm (kernelOperator hv)
        * hsNorm (kernelOperator hw))
      ≤ Real.sqrt (CV*CW) * (1+M) * Real.sqrt (1+a^3) * Real.exp (a^3/3 - 2*M*a) := by
    calc ‖conjHeatCLM (1 + r) hL a‖ * (hsNorm (kernelOperator hv) * hsNorm (kernelOperator hw))
        ≤ Real.exp ((1+r) * a^2) * ((Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)
              * Real.exp (1*a^2 - 2*M*a)) * (Real.sqrt CW * Real.exp (a^3/3 - (2+r)*a^2))) :=
          mul_le_mul hBnorm (mul_le_mul hsV hsW (hsNorm_nonneg _) hbnnV)
            (mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _)) (Real.exp_pos _).le
      _ = Real.sqrt (CV*CW) * (1+M) * Real.sqrt (1+a^3) * Real.exp (a^3/3 - 2*M*a) := by
          rw [Real.sqrt_mul hCV.le, ← hexp3]
          ring
  -- the hsNorm bound: H1 then the `hsNorm_comp_le`
  have hHSVW : IsHilbertSchmidt (kernelOperator hv ∘L kernelOperator hw) :=
    (isHilbertSchmidt_kernelOperator hw).comp_left _
  have hVW : hsNorm (kernelOperator hv ∘L kernelOperator hw)
      ≤ hsNorm (kernelOperator hv) * hsNorm (kernelOperator hw) :=
    hsNorm_comp_le (isHilbertSchmidt_kernelOperator hv) (isHilbertSchmidt_kernelOperator hw)
  have hmain : hsNorm (conjHeatCLM (1 + r) hL a ∘L (kernelOperator hv ∘L kernelOperator hw))
      ≤ ‖conjHeatCLM (1 + r) hL a‖ * (hsNorm (kernelOperator hv) * hsNorm (kernelOperator hw)) :=
    (hsNorm_comp_left_le _ _ hHSVW).trans
      (mul_le_mul_of_nonneg_left hVW (norm_nonneg _))
  -- the trace bound: `|Tr ((B∘kV)∘kW)| ≤ hsNorm (B∘kV)·hsNorm kW ≤ ‖B‖·hsNorm kV·hsNorm kW`
  have hTR : |trace (conjHeatCLM (1 + r) hL a ∘L (kernelOperator hv ∘L kernelOperator hw))|
      ≤ ‖conjHeatCLM (1 + r) hL a‖ * (hsNorm (kernelOperator hv) * hsNorm (kernelOperator hw)) := by
    have hBcomp : IsHilbertSchmidt (conjHeatCLM (1 + r) hL a ∘L kernelOperator hv) :=
      (isHilbertSchmidt_kernelOperator hv).comp_left _
    have h := norm_trace_comp_le hBcomp (isHilbertSchmidt_kernelOperator hw)
    rw [Real.norm_eq_abs] at h
    calc |trace (conjHeatCLM (1 + r) hL a ∘L (kernelOperator hv ∘L kernelOperator hw))|
        = |trace ((conjHeatCLM (1 + r) hL a ∘L kernelOperator hv) ∘L kernelOperator hw)| := by
            rw [ContinuousLinearMap.comp_assoc]
      _ ≤ hsNorm (conjHeatCLM (1 + r) hL a ∘L kernelOperator hv)
            * hsNorm (kernelOperator hw) := h
      _ ≤ (‖conjHeatCLM (1 + r) hL a‖ * hsNorm (kernelOperator hv))
            * hsNorm (kernelOperator hw) :=
          mul_le_mul_of_nonneg_right (hsNorm_comp_left_le _ _ (isHilbertSchmidt_kernelOperator hv))
            (hsNorm_nonneg _)
      _ = ‖conjHeatCLM (1 + r) hL a‖ * (hsNorm (kernelOperator hv) * hsNorm (kernelOperator hw)) :=
          by ring
  refine ⟨?_, ?_⟩
  · exact le_packaged_of_le hM1 hr1 haeq (Real.sqrt_nonneg _) le_rfl hCtop (hTR.trans hfactor)
  · exact le_packaged_of_le hM1 hr1 haeq (Real.sqrt_nonneg _) le_rfl hCtop (hmain.trans hfactor)

/-- rpow bump for nat powers: `M^n ≤ M^{(n:ℝ)+c}` for `1 ≤ M`, `0 ≤ c` (the
existential-exponent packaging step). -/
private theorem natPow_le_rpow_add {M : ℝ} (hM1 : 1 ≤ M) (n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    M^n ≤ M^((n:ℝ) + c) := by
  rw [← Real.rpow_natCast M n]
  exact Real.rpow_le_rpow_of_exponent_le hM1
    (by linarith [show (0:ℝ) ≤ (n:ℝ) from by positivity])

/-- rpow bump for the fixed exponent `4`: `M^{4:ℝ} ≤ M^{(4:ℝ)+c}` for `1 ≤ M`, `0 ≤ c`. -/
private theorem rpow_four_le_rpow_add {M : ℝ} (hM1 : 1 ≤ M) (c : ℝ) (hc : 0 ≤ c) :
    M^(4:ℝ) ≤ M^((4:ℝ) + c) :=
  Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)

/-- **Step 3 for K̃∪** (HS form, Remark 1): with O3
(`kernelOperator_kcupKerT_eq_comp`), `hsNorm K̃∪ ≤ hsNorm kVdR · hsNorm kWS`.  For the
Ṽ_{D,r} factor `hsENorm_kernelOperator_le` gives `hsENorm ≤ eLpNorm`, then
the domination `0 ≤ vdRKer ≤ uphiKer + plqKer` with Minkowski splits the
`L²` norm; the `QP_L` piece is the paper's `UΦ` Hilbert–Schmidt lemma (`uphi_hs_le`, via H2 + H3)
and the `P_LQ` piece is the `L² → L²` conjugation lemma composed with the Hilbert–Schmidt
bound for `V` (via
`kernelOperator_compKernel_uConjHeat` + H1 + `enorm_conjHeatCLM_le` +
`eLpNorm_vKernel_le_of_bound`).  Both pieces share the exponent `(r+1)a² + a² − a³` at
`a = √(2M)` (`2Ma = a³`), and multiplying by the W-factor `e^{a³/3−(2+r)a²}` gives
`e^{−(2/3)a³}`.  The trace bound `|Tr K̃∪| ≤ hsNorm kVdR · hsNorm kWS`
(`norm_trace_comp_le`) has the same form. -/
theorem twoInt_kcup_bounds :
    ∃ C K : ℝ, 0 < C ∧ (4:ℝ) ≤ K ∧ ∀ {M r a : ℝ} (hM1 : 1 ≤ M) (hr1 : 1 ≤ r) (hadr : r + 3 ≤ a)
      (haeq : a = Real.sqrt (2*M)) (hk : MemLp (kcupKerT a M r) 2 (volume.prod volume)),
      |trace (kernelOperator hk)| ≤ C * M^K * (1+r)^K * Real.exp (-(2/3)*a^3) ∧
      hsNorm (kernelOperator hk) ≤ C * M^K * (1+r)^K * Real.exp (-(2/3)*a^3) := by
  obtain ⟨CU, hCU, KU, HU⟩ := AiryConj.uphi_hs_le 1 one_pos
  obtain ⟨CV, hCV, HV⟩ := AiryConj.vKernel_sq_integral_le 1 one_pos
  obtain ⟨CW, hCW, HW⟩ := AiryConj.wKernel_sq_integral_le
  have hK3 : (4:ℝ) ≤ (KU:ℝ) + 4 := by
    have h := show (0:ℝ) ≤ (KU:ℝ) from by positivity
    linarith
  refine ⟨(CU * 2^KU + 8 * Real.sqrt CV) * Real.sqrt CW, (KU:ℝ) + 4, by positivity, hK3,
    fun {M r a} hM1 hr1 hadr haeq hk => ?_⟩
  have hM : 0 < M := by linarith
  have hr : 0 < r := by linarith
  have hMnn : (0:ℝ) ≤ M := hM.le
  have ha1 : (1:ℝ) + 1 ≤ a := by linarith
  have hL1 : (0:ℝ) < r + 1 := by linarith
  have hS : (0:ℝ) < 2 + r := by linarith
  have hSa : 2 + r + 1 ≤ a := by linarith
  have h1r : (1:ℝ) ≤ 1 + r := by linarith
  have ha2eq : a^2 = 2*M := by rw [haeq]; exact Real.sq_sqrt (by linarith)
  have h2Ma : 2*M*a = a^3 := by rw [← ha2eq]; ring
  -- operator identification (O3)
  have hcongr : kernelOperator hk = kernelOperator (memLp_kcupKerT hr hM hadr) :=
    kernelOperator_congr rfl hk (memLp_kcupKerT hr hM hadr)
  have hVdR : MemLp (vdRKer a M r) 2 (volume.prod volume) := memLp_vdRKer hr hM hadr
  have hWS : MemLp (wSKer (2 + r) a) 2 (volume.prod volume) := memLp_wSKer hr hadr
  have heq : kernelOperator hk = kernelOperator hVdR ∘L kernelOperator hWS :=
    hcongr.trans (kernelOperator_kcupKerT_eq_comp hr hM hadr)
  rw [heq]
  -- the W factor (wSKer is definitionally wKernel)
  have hWSconv : kernelOperator hWS = kernelOperator (AiryConj.memLp_wKernel hS hSa) :=
    kernelOperator_congr rfl hWS (AiryConj.memLp_wKernel hS hSa)
  have hsW : hsNorm (kernelOperator hWS)
      ≤ Real.sqrt CW * Real.exp (a^3/3 - (2+r)*a^2) := by
    rw [hWSconv]
    exact hsNorm_wKernel_le_of hS hSa hCW (HW (2+r) a hS hSa).1 (HW (2+r) a hS hSa).2
  -- the shared exponent of the two Ṽ_{D,r} pieces
  have hEeq : Real.exp ((r+1) * a^2 + 1 * a^2 - a^3) = Real.exp ((r+1)*a^2 + a^2 - a^3) := by
    congr 1
    ring
  -- the `uphiKer` (`QP_L`) piece: H3, H2, then `uphi_hs_le`
  have hupmem : MemLp (uphiKer 1 a M (r+1)) 2 (volume.prod volume) :=
    memLp_uphiKer 1 a M (r+1) one_pos hM hL1 ha1
  have hup : eLpNorm (uphiKer 1 a M (r+1)) 2 (volume.prod volume)
      ≤ ENNReal.ofReal (CU * (1 + M + (r+1))^KU * Real.exp ((r+1)*a^2 + a^2 - a^3)) := by
    rw [← hsENorm_kernelOperator_eq hupmem, kernelOperator_uphiKer 1 a M (r+1) one_pos hM hL1 ha1]
    have h := HU M (r+1) a hM hL1 haeq ha1
    rwa [hEeq] at h
  -- the `plqKer` (`P_LQ`) piece: H3, the left-factor identification, H1,
  -- the `L² → L²` conjugation lemma, the Hilbert–Schmidt bound for `V`
  have hplqeq : plqKer a M (r+1)
      = AiryConj.compKernel (uConj a (heatKerTwo (r+1))) (AiryConj.vKernel 1 a M) := rfl
  have hplqmem : MemLp (AiryConj.compKernel (uConj a (heatKerTwo (r+1)))
      (AiryConj.vKernel 1 a M)) 2 (volume.prod volume) :=
    memLp_compKernel_uConjHeat hL1 a (AiryConj.measurable_vKernel 1 a M)
      (AiryConj.vKernel_memLp one_pos hM ha1)
  have hexp2 : Real.exp ((r+1) * a^2) * Real.exp (1*a^2 - 2*M*a)
      = Real.exp ((r+1)*a^2 + a^2 - a^3) := by
    rw [← Real.exp_add]
    congr 1
    rw [h2Ma]
    ring
  have hplq : eLpNorm (plqKer a M (r+1)) 2 (volume.prod volume)
      ≤ ENNReal.ofReal (Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)
          * Real.exp ((r+1)*a^2 + a^2 - a^3)) := by
    rw [hplqeq, ← hsENorm_kernelOperator_eq hplqmem, kernelOperator_compKernel_uConjHeat hL1 a
      (AiryConj.vKernel_memLp one_pos hM ha1) hplqmem]
    have hB' := enorm_conjHeatCLM_le (r+1) hL1 a
    have hVk : hsENorm (kernelOperator (AiryConj.vKernel_memLp one_pos hM ha1))
        ≤ eLpNorm (AiryConj.vKernel 1 a M) 2 (volume.prod volume) :=
      hsENorm_kernelOperator_le _
    have hVb := AiryConj.eLpNorm_vKernel_le_of_bound 1 a M one_pos hM ha1 hCV (HV M a hM ha1).2
    calc hsENorm (conjHeatCLM (r+1) hL1 a ∘L kernelOperator (AiryConj.vKernel_memLp one_pos hM ha1))
        ≤ ‖conjHeatCLM (r+1) hL1 a‖ₑ
            * hsENorm (kernelOperator (AiryConj.vKernel_memLp one_pos hM ha1)) :=
          hsENorm_comp_left_le _ _
      _ ≤ ENNReal.ofReal (Real.exp ((r+1) * a^2))
            * eLpNorm (AiryConj.vKernel 1 a M) 2 (volume.prod volume) :=
          mul_le_mul' hB' hVk
      _ ≤ ENNReal.ofReal (Real.exp ((r+1) * a^2))
            * ENNReal.ofReal (Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)
              * Real.exp (1*a^2 - 2*M*a)) :=
          mul_le_mul' le_rfl hVb
      _ = ENNReal.ofReal (Real.exp ((r+1) * a^2)
            * (Real.sqrt CV * (1+M) * Real.sqrt (1+a^3) * Real.exp (1*a^2 - 2*M*a))) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ = ENNReal.ofReal (Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)
            * Real.exp ((r+1)*a^2 + a^2 - a^3)) := by
          congr 1
          calc Real.exp ((r+1) * a^2) * (Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)
                * Real.exp (1*a^2 - 2*M*a))
            = (Real.sqrt CV * (1+M) * Real.sqrt (1+a^3))
                * (Real.exp ((r+1) * a^2) * Real.exp (1*a^2 - 2*M*a)) := by ring
          _ = (Real.sqrt CV * (1+M) * Real.sqrt (1+a^3))
                * Real.exp ((r+1)*a^2 + a^2 - a^3) := by rw [hexp2]
          _ = Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)
                * Real.exp ((r+1)*a^2 + a^2 - a^3) := by ring
  -- the domination chain for the Ṽ_{D,r} kernel + Minkowski
  have hdom : eLpNorm (vdRKer a M r) 2 (volume.prod volume)
      ≤ eLpNorm (uphiKer 1 a M (r+1)) 2 (volume.prod volume)
        + eLpNorm (plqKer a M (r+1)) 2 (volume.prod volume) := by
    have h1 : eLpNorm (vdRKer a M r) 2 (volume.prod volume)
        ≤ eLpNorm (uphiKer 1 a M (r+1) + plqKer a M (r+1)) 2 (volume.prod volume) :=
      MeasureTheory.eLpNorm_mono_enorm (measurable_vdRKer a M r).aestronglyMeasurable
        (fun p => by
          rw [Real.enorm_eq_ofReal (vdRKer_nonneg hr a M p), Pi.add_apply,
            Real.enorm_eq_ofReal (add_nonneg (uphiKer_one_nonneg a M (r+1) hL1 p)
              (plqKer_nonneg a M (r+1) hL1 p))]
          exact ENNReal.ofReal_le_ofReal (vdRKer_le hr a M p))
    exact h1.trans (MeasureTheory.eLpNorm_add_le (by norm_num : (1:ℝ≥0∞) ≤ 2))
  -- the assembled `hsNorm kVdR` bound (toReal of the ofReal sum)
  have hbase1 : (0:ℝ) ≤ 1 + M + (r+1) := by linarith
  have h1M : (0:ℝ) ≤ 1 + M := by linarith
  have hPnn : (0:ℝ) ≤ CU * (1 + M + (r+1))^KU + Real.sqrt CV * (1+M) * Real.sqrt (1+a^3) :=
    add_nonneg (mul_nonneg hCU.le (pow_nonneg hbase1 _))
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h1M) (Real.sqrt_nonneg _))
  have hEnn : (0:ℝ) ≤ Real.exp ((r+1)*a^2 + a^2 - a^3) := (Real.exp_pos _).le
  have hA0 : (0:ℝ) ≤ CU * (1 + M + (r+1))^KU * Real.exp ((r+1)*a^2 + a^2 - a^3) :=
    mul_nonneg (mul_nonneg hCU.le (pow_nonneg hbase1 _)) hEnn
  have hB0 : (0:ℝ) ≤ Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)
      * Real.exp ((r+1)*a^2 + a^2 - a^3) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h1M) (Real.sqrt_nonneg _)) hEnn
  have hVdRbound : hsNorm (kernelOperator hVdR)
      ≤ (CU * (1 + M + (r+1))^KU + Real.sqrt CV * (1+M) * Real.sqrt (1+a^3))
        * Real.exp ((r+1)*a^2 + a^2 - a^3) := by
    calc hsNorm (kernelOperator hVdR) = (hsENorm (kernelOperator hVdR)).toReal := rfl
      _ ≤ (eLpNorm (vdRKer a M r) 2 (volume.prod volume)).toReal :=
          ENNReal.toReal_mono hVdR.eLpNorm_ne_top (hsENorm_kernelOperator_le hVdR)
      _ ≤ (eLpNorm (uphiKer 1 a M (r+1)) 2 (volume.prod volume)
            + eLpNorm (plqKer a M (r+1)) 2 (volume.prod volume)).toReal :=
          ENNReal.toReal_mono
            (ENNReal.add_ne_top.mpr ⟨hupmem.eLpNorm_ne_top, hplqmem.eLpNorm_ne_top⟩) hdom
      _ ≤ (ENNReal.ofReal (CU * (1 + M + (r+1))^KU * Real.exp ((r+1)*a^2 + a^2 - a^3))
            + ENNReal.ofReal (Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)
              * Real.exp ((r+1)*a^2 + a^2 - a^3))).toReal :=
          ENNReal.toReal_mono
            (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
            (add_le_add hup hplq)
      _ = (CU * (1 + M + (r+1))^KU + Real.sqrt CV * (1+M) * Real.sqrt (1+a^3))
            * Real.exp ((r+1)*a^2 + a^2 - a^3) := by
          rw [← ENNReal.ofReal_add hA0 hB0, ENNReal.toReal_ofReal (add_nonneg hA0 hB0)]
          ring
  -- multiply by the W factor: the exponent cancellation
  have hexpW : Real.exp ((r+1)*a^2 + a^2 - a^3) * Real.exp (a^3/3 - (2+r)*a^2)
      = Real.exp (-(2/3)*a^3) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : hsNorm (kernelOperator hVdR) * hsNorm (kernelOperator hWS)
      ≤ ((CU * (1 + M + (r+1))^KU + Real.sqrt CV * (1+M) * Real.sqrt (1+a^3))
          * Real.sqrt CW) * Real.exp (-(2/3)*a^3) := by
    calc hsNorm (kernelOperator hVdR) * hsNorm (kernelOperator hWS)
        ≤ ((CU * (1 + M + (r+1))^KU + Real.sqrt CV * (1+M) * Real.sqrt (1+a^3))
            * Real.exp ((r+1)*a^2 + a^2 - a^3))
          * (Real.sqrt CW * Real.exp (a^3/3 - (2+r)*a^2)) :=
          mul_le_mul hVdRbound hsW (hsNorm_nonneg _) (mul_nonneg hPnn hEnn)
      _ = ((CU * (1 + M + (r+1))^KU + Real.sqrt CV * (1+M) * Real.sqrt (1+a^3))
            * Real.sqrt CW) * Real.exp (-(2/3)*a^3) := by
          rw [← hexpW]
          ring
  -- the polynomial packaging at `K = KU + 4`
  have hK3eq : (4:ℝ) + (KU:ℝ) = (KU:ℝ) + 4 := by ring
  have hKU0 : (0:ℝ) ≤ (KU:ℝ) := Nat.cast_nonneg _
  have hMr : (1:ℝ) * 1 ≤ M * r := mul_le_mul hM1 hr1 (by norm_num) (by linarith)
  have hbase : 1 + M + (r+1) ≤ (1+M) * (1+r) := by nlinarith [hMr]
  have hA1 : (1 + M + (r+1))^KU ≤ (2:ℝ)^KU * (M^KU * (1+r)^KU) := by
    calc (1 + M + (r+1))^KU ≤ ((1+M) * (1+r))^KU :=
          pow_le_pow_left₀ hbase1 hbase KU
      _ = (1+M)^KU * (1+r)^KU := mul_pow _ _ _
      _ ≤ (2*M)^KU * (1+r)^KU := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
          exact pow_le_pow_left₀ h1M (by linarith) KU
      _ = (2:ℝ)^KU * (M^KU * (1+r)^KU) := by rw [mul_pow]; ring
  have hA2 : (M^KU * (1+r)^KU) ≤ M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4) := by
    exact mul_le_mul (natPow_le_rpow_add hM1 KU 4 (by norm_num))
      (natPow_le_rpow_add h1r KU 4 (by norm_num))
      (pow_nonneg (by linarith) _) (Real.rpow_nonneg hMnn _)
  have hB1 : Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)
      ≤ Real.sqrt CV * (8 * (M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4))) := by
    have h' : (1+M) * Real.sqrt (1+a^3) ≤ 8 * (M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4)) :=
      (one_add_mul_sqrt_one_add_a_cube_le hM1 haeq).trans (by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 8)
        calc M^(4:ℝ) ≤ M^((KU:ℝ)+4) := by
              rw [← hK3eq]; exact rpow_four_le_rpow_add hM1 _ hKU0
          _ ≤ M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4) :=
              le_mul_of_one_le_right (Real.rpow_nonneg hMnn _)
                (Real.one_le_rpow h1r (by linarith)))
    calc Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)
        = Real.sqrt CV * ((1+M) * Real.sqrt (1+a^3)) := by ring
      _ ≤ Real.sqrt CV * (8 * (M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4))) :=
          mul_le_mul_of_nonneg_left h' (Real.sqrt_nonneg _)
  -- assemble the packaged polynomial bound
  have hpack : (CU * (1 + M + (r+1))^KU + Real.sqrt CV * (1+M) * Real.sqrt (1+a^3))
        * Real.sqrt CW
      ≤ ((CU * 2^KU + 8 * Real.sqrt CV) * Real.sqrt CW)
        * M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4) := by
    have hstep : CU * (1 + M + (r+1))^KU + Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)
        ≤ CU * ((2:ℝ)^KU * (M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4)))
          + Real.sqrt CV * (8 * (M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4))) := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left hA1 hCU.le).trans
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA2 (by positivity)) hCU.le)
      · exact hB1
    calc (CU * (1 + M + (r+1))^KU + Real.sqrt CV * (1+M) * Real.sqrt (1+a^3)) * Real.sqrt CW
        ≤ (CU * ((2:ℝ)^KU * (M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4)))
            + Real.sqrt CV * (8 * (M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4)))) * Real.sqrt CW :=
          mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg _)
      _ = ((CU * 2^KU + 8 * Real.sqrt CV) * Real.sqrt CW)
            * M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4) := by ring
  -- the final two bounds
  have hCWnn : (0:ℝ) ≤ Real.sqrt CW := Real.sqrt_nonneg _
  have hfinal : hsNorm (kernelOperator hVdR) * hsNorm (kernelOperator hWS)
      ≤ (CU * 2^KU + 8 * Real.sqrt CV) * Real.sqrt CW
        * M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4) * Real.exp (-(2/3)*a^3) := by
    calc hsNorm (kernelOperator hVdR) * hsNorm (kernelOperator hWS)
        ≤ ((CU * (1 + M + (r+1))^KU + Real.sqrt CV * (1+M) * Real.sqrt (1+a^3))
            * Real.sqrt CW) * Real.exp (-(2/3)*a^3) := hprod
      _ ≤ (((CU * 2^KU + 8 * Real.sqrt CV) * Real.sqrt CW)
            * M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4)) * Real.exp (-(2/3)*a^3) := by
          exact mul_le_mul_of_nonneg_right hpack (Real.exp_pos _).le
      _ = (CU * 2^KU + 8 * Real.sqrt CV) * Real.sqrt CW
            * M^((KU:ℝ)+4) * (1+r)^((KU:ℝ)+4) * Real.exp (-(2/3)*a^3) := by ring
  refine ⟨?_, ?_⟩
  · have hTR : |trace (kernelOperator hVdR ∘L kernelOperator hWS)|
        ≤ hsNorm (kernelOperator hVdR) * hsNorm (kernelOperator hWS) := by
      have h := norm_trace_comp_le (isHilbertSchmidt_kernelOperator hVdR)
        (isHilbertSchmidt_kernelOperator hWS)
      rwa [Real.norm_eq_abs] at h
    exact hTR.trans hfinal
  · exact (hsNorm_comp_le (isHilbertSchmidt_kernelOperator hVdR)
      (isHilbertSchmidt_kernelOperator hWS)).trans hfinal

/-- **Exponent/constant bump**: a bound at `(Cᵢ, K₁)` implies the bound at any
`(C, K₂)` with `Cᵢ ≤ C`, `K₁ ≤ K₂` (bases `M, 1+r ≥ 1`, so rpow is exponent-monotone,
`Real.rpow_le_rpow_of_exponent_le`).  This is the "enlarging K" step and the
`Cᵢ ≤ C₁+C₂+C₃` step of the paper's proof. -/
private theorem bump_eta {M r a Cᵢ bnd : ℝ} (hM1 : 1 ≤ M) (hr1 : 1 ≤ r)
    {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂) (hC0 : 0 ≤ Cᵢ) {C : ℝ} (hCC : Cᵢ ≤ C) (hCnn : 0 ≤ C)
    (hb : bnd ≤ Cᵢ * M^(K₁:ℝ) * (1+r)^(K₁:ℝ) * Real.exp (-(2/3)*a^3)) :
    bnd ≤ C * M^(K₂:ℝ) * (1+r)^(K₂:ℝ) * Real.exp (-(2/3)*a^3) := by
  have hMnn : (0:ℝ) ≤ M := by linarith
  have h1r : (1:ℝ) ≤ 1 + r := by linarith
  have hMK : M^(K₁:ℝ) ≤ M^(K₂:ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 hK
  have hrK : (1+r)^(K₁:ℝ) ≤ (1+r)^(K₂:ℝ) := Real.rpow_le_rpow_of_exponent_le h1r hK
  have hM1nn : (0:ℝ) ≤ M^(K₁:ℝ) := Real.rpow_nonneg hMnn _
  have hr1nn : (0:ℝ) ≤ (1+r)^(K₁:ℝ) := Real.rpow_nonneg (by linarith) _
  have hexpnn : (0:ℝ) ≤ Real.exp (-(2/3)*a^3) := (Real.exp_pos _).le
  have hC1 : Cᵢ * M^(K₁:ℝ) ≤ C * M^(K₂:ℝ) :=
    mul_le_mul hCC hMK hM1nn hCnn
  have hC2 : (Cᵢ * M^(K₁:ℝ)) * (1+r)^(K₁:ℝ) ≤ (C * M^(K₂:ℝ)) * (1+r)^(K₂:ℝ) :=
    mul_le_mul hC1 hrK hr1nn (mul_nonneg hCnn (Real.rpow_nonneg hMnn _))
  exact hb.trans (mul_le_mul_of_nonneg_right hC2 hexpnn)


/-- **The Step-3 packaged headline** (HS
form, Remark 1): there are `C > 0` and `K ≥ 0` such that for all `1 ≤ M`,
`1 ≤ r`, `r + 3 ≤ a`, `a = √(2M)`, writing `η = C M^K (1+r)^K e^{−(2/3)a³}`, all three
operators satisfy `|Tr K̃ᵢ| ≤ η` and `hsNorm K̃ᵢ ≤ η`.  (The `(1+r)^K` factor is needed
only for K̃∪ — one shared `K` is the paper's packaging; η is written inline rather
than via a `let` for ease of rewriting downstream.) -/
theorem twoInt_stepThree (χ : ℝ) (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ {M r a : ℝ} (hM1 : 1 ≤ M) (hr1 : 1 ≤ r) (hadr : r + 3 ≤ a)
      (haeq : a = Real.sqrt (2*M))
      (hk1 : MemLp (k1KerT a M) 2 (volume.prod volume))
      (hk2 : MemLp (k2KerT a M r) 2 (volume.prod volume))
      (hkcup : MemLp (kcupKerT a M r) 2 (volume.prod volume)),
      |trace (kernelOperator hk1)| ≤ C * M^K * (1+r)^(K:ℝ) * Real.exp (-(2/3)*a^3) ∧
      hsNorm (kernelOperator hk1) ≤ C * M^K * (1+r)^(K:ℝ) * Real.exp (-(2/3)*a^3) ∧
      |trace (kernelOperator hk2)| ≤ C * M^K * (1+r)^(K:ℝ) * Real.exp (-(2/3)*a^3) ∧
      hsNorm (kernelOperator hk2) ≤ C * M^K * (1+r)^(K:ℝ) * Real.exp (-(2/3)*a^3) ∧
      |trace (kernelOperator hkcup)| ≤ C * M^K * (1+r)^(K:ℝ) * Real.exp (-(2/3)*a^3) ∧
      hsNorm (kernelOperator hkcup) ≤ C * M^K * (1+r)^(K:ℝ) * Real.exp (-(2/3)*a^3) := by
  obtain ⟨C₁, hC₁, H₁⟩ := twoInt_k1_bounds
  obtain ⟨C₂, hC₂, H₂⟩ := twoInt_k2_bounds
  obtain ⟨C₃, K₃, hC₃, hK₃, H₃⟩ := twoInt_kcup_bounds
  have hCnn : (0:ℝ) ≤ C₁ + C₂ + C₃ := by linarith [hC₁.le, hC₂.le, hC₃.le]
  have hCpos : (0:ℝ) < C₁ + C₂ + C₃ := by linarith [hC₁, hC₂.le, hC₃.le]
  have hC1le : C₁ ≤ C₁ + C₂ + C₃ := by linarith [hC₂.le, hC₃.le]
  have hC2le : C₂ ≤ C₁ + C₂ + C₃ := by linarith [hC₁.le, hC₃.le]
  have hC3le : C₃ ≤ C₁ + C₂ + C₃ := by linarith [hC₁.le, hC₂.le]
  refine ⟨C₁ + C₂ + C₃, K₃, hCpos, by linarith, fun hM1 hr1 hadr haeq hk1 hk2 hkcup => ?_⟩
  obtain ⟨h1tr, h1hs⟩ := H₁ hM1 hr1 hadr haeq hk1
  obtain ⟨h2tr, h2hs⟩ := H₂ hM1 hr1 hadr haeq hk2
  obtain ⟨h3tr, h3hs⟩ := H₃ hM1 hr1 hadr haeq hkcup
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bump_eta hM1 hr1 hK₃ hC₁.le hC1le hCnn h1tr
  · exact bump_eta hM1 hr1 hK₃ hC₁.le hC1le hCnn h1hs
  · exact bump_eta hM1 hr1 hK₃ hC₂.le hC2le hCnn h2tr
  · exact bump_eta hM1 hr1 hK₃ hC₂.le hC2le hCnn h2hs
  · exact bump_eta hM1 hr1 le_rfl hC₃.le hC3le hCnn h3tr
  · exact bump_eta hM1 hr1 le_rfl hC₃.le hC3le hCnn h3hs

/-! ### Step 1: the det₁-linearization algebra -/

/-- **Step 1, the determinant-linearization remainder**: the paper's
`R(H) = det(I−H) − 1 + Tr H`, written with `fredholmDetOne A hA 1`
(`= det₁(I − A)`, FredholmOne.lean).  (Sign convention: the first-order expansion
bound is on `‖1 − det₁ − Tr‖`; the paper's `R(H)` is its negative — the bound
transfers by `abs_neg`.) -/
noncomputable def detOneLinRem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (hA : IsTraceClass A) : ℝ :=
  fredholmDetOne A hA 1 - 1 + trace A

/-- The first-order expansion first-order expansion bound rewritten for `detOneLinRem`
(Remark 2: the trace-norm bound `|R(H)| ≤ ½‖H‖₁² e^{‖H‖₁}` (Simon, Ch. 3)
is replaced by the HS-form bound
`(|tr| + h²)²/2 · e^{|tr|+h²} + h²` under the side condition `hsNorm A ≤ 1/2`). -/
theorem abs_detOneLinRem_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {A : E →L[ℝ] E} (hA : IsTraceClass A)
    (hz : hsNorm A < 1) (h2 : hsNorm A ≤ 1/2) :
    |detOneLinRem A hA|
      ≤ (|trace A| + hsNorm A ^ 2) ^ 2 / 2 * Real.exp (|trace A| + hsNorm A ^ 2)
        + hsNorm A ^ 2 := by
  have h := norm_one_sub_fredholmDetOne_one_sub_trace_le hA hz h2
  simp only [Real.norm_eq_abs] at h
  rw [show detOneLinRem A hA = -(1 - fredholmDetOne A hA 1 - trace A) from by
    unfold detOneLinRem; ring, abs_neg]
  exact h

/-- **The three-determinant combination**: over any three trace-class
operators with the trace relation `Tr K₁ + Tr K₂ − Tr K∪ = Tr Cr`,
`1 − det₁(K₁) − det₁(K₂) + det₁(K∪) = Tr Cr + (−R(K₁) − R(K₂) + R(K∪))`
(the paper's sign pattern exactly; pure algebra after unfolding `detOneLinRem`). -/
theorem joint_detOne_comb_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {K1 K2 Kcup Cr : E →L[ℝ] E}
    (h1 : IsTraceClass K1) (h2 : IsTraceClass K2) (hcup : IsTraceClass Kcup)
    (htr : trace K1 + trace K2 - trace Kcup = trace Cr) :
    1 - fredholmDetOne K1 h1 1 - fredholmDetOne K2 h2 1 + fredholmDetOne Kcup hcup 1
      = trace Cr + (-detOneLinRem K1 h1 - detOneLinRem K2 h2 + detOneLinRem Kcup hcup) := by
  unfold detOneLinRem
  linear_combination htr

/-- **The two-interval instantiation** (the operator-level form of
`P(A∩B) = Tr C̃_r + ℛ_{M,r}`): the trace cancellation
`trace_twoIntKCup_discharged` supplies the trace
relation.  Scope boundary: the probability identity `P(A∩B) = …` itself is an external
bridge record for the main package, NOT formalized here. -/
theorem joint_detOne_comb_twoInt_eq (hr : 0 < r) (hM : 0 < M) {a : ℝ} (hadr : r + 3 ≤ a)
    (hk1 : MemLp (k1KerT a M) 2 (volume.prod volume))
    (hk2 : MemLp (k2KerT a M r) 2 (volume.prod volume))
    (hkcup : MemLp (kcupKerT a M r) 2 (volume.prod volume))
    (hcr : MemLp (crKerT a M r) 2 (volume.prod volume))
    (hk1t : IsTraceClass (kernelOperator hk1)) (hk2t : IsTraceClass (kernelOperator hk2))
    (hkcupt : IsTraceClass (kernelOperator hkcup)) :
    1 - fredholmDetOne (kernelOperator hk1) hk1t 1
        - fredholmDetOne (kernelOperator hk2) hk2t 1
        + fredholmDetOne (kernelOperator hkcup) hkcupt 1
      = trace (kernelOperator hcr)
        + (-detOneLinRem (kernelOperator hk1) hk1t - detOneLinRem (kernelOperator hk2) hk2t
          + detOneLinRem (kernelOperator hkcup) hkcupt) := by
  have hc1 : kernelOperator hk1 = kernelOperator (memLp_k1KerT hM (by linarith : (2:ℝ) ≤ a)) :=
    kernelOperator_congr rfl hk1 _
  have hc2 : kernelOperator hk2 = kernelOperator (memLp_k2KerT hr hM hadr) :=
    kernelOperator_congr rfl hk2 _
  have hcc : kernelOperator hkcup = kernelOperator (memLp_kcupKerT hr hM hadr) :=
    kernelOperator_congr rfl hkcup _
  have hccr : kernelOperator hcr = kernelOperator (memLp_crKerT hr hM hadr) :=
    kernelOperator_congr rfl hcr _
  have htr : trace (kernelOperator hk1) + trace (kernelOperator hk2)
      - trace (kernelOperator hkcup) = trace (kernelOperator hcr) := by
    rw [hc1, hc2, hcc, hccr]
    exact trace_twoIntKCup_discharged hr hM hadr
  exact joint_detOne_comb_eq hk1t hk2t hkcupt htr

/-! ### Step 4: admissibility, η-uniformity, and the remainder assembly -/

/-- **Admissibility** (explicit-threshold form, Remark 3): once
`M ≥ 9/(2(1−χ)²)` — the paper's `a ≥ 3/(1−χ)` — the range `1 ≤ r ≤ χ√(2M)` gives
`√(2M) − r ≥ (1−χ)√(2M) ≥ 3`, hence the admissibility `r + 3 ≤ √(2M)` of the paper's joint-exceedance lemma and
`2 ≤ √(2M)`, `1 ≤ M`. -/
theorem exists_admissible_M₀ (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ M₀ : ℝ, ∀ M r : ℝ, M₀ ≤ M → 1 ≤ r → r ≤ χ * Real.sqrt (2*M) →
      r + 3 ≤ Real.sqrt (2*M) ∧ 2 ≤ Real.sqrt (2*M) ∧ 1 ≤ M := by
  have h1χ : (0:ℝ) < 1 - χ := by linarith
  refine ⟨9 / (2 * (1-χ)^2), fun M r hM0 hr1 hrM => ?_⟩
  have hM0nn : (0:ℝ) ≤ 9 / (2 * (1-χ)^2) :=
    div_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg (1-χ)))
  have hMnn : (0:ℝ) ≤ M := hM0nn.trans hM0
  have hne : (1-χ)^2 ≠ 0 := pow_ne_zero 2 h1χ.ne'
  have h2M0 : 2 * (9 / (2 * (1-χ)^2)) = (3 / (1-χ))^2 := by
    rw [div_pow]
    field_simp [hne]
    ring
  have hsqrt0 : Real.sqrt (2 * (9 / (2 * (1-χ)^2))) = 3 / (1-χ) := by
    rw [h2M0, Real.sqrt_sq (div_nonneg (by norm_num) h1χ.le)]
  have hsqrtM : 3 / (1-χ) ≤ Real.sqrt (2*M) := by
    rw [← hsqrt0]
    exact Real.sqrt_le_sqrt (by linarith [hM0])
  have hkey : 3 ≤ (1-χ) * Real.sqrt (2*M) := by
    calc 3 = (1-χ) * (3 / (1-χ)) := by field_simp [h1χ.ne']
      _ ≤ (1-χ) * Real.sqrt (2*M) := mul_le_mul_of_nonneg_left hsqrtM h1χ.le
  have h4 : (4:ℝ) ≤ Real.sqrt (2*M) := by
    have h1 : Real.sqrt (2*M) = χ * Real.sqrt (2*M) + (1-χ) * Real.sqrt (2*M) := by ring
    calc (4:ℝ) = χ * Real.sqrt (2*M) + 3 - 3 + 4 - χ * Real.sqrt (2*M) := by ring
      _ ≤ Real.sqrt (2*M) := by nlinarith [hkey, hrM, hr1, Real.sqrt_nonneg (2*M), hχ0]
  have h1 : r + 3 ≤ Real.sqrt (2*M) := by
    calc r + 3 ≤ χ * Real.sqrt (2*M) + (1-χ) * Real.sqrt (2*M) :=
          add_le_add hrM hkey
      _ = Real.sqrt (2*M) := by ring
  refine ⟨h1, by linarith, ?_⟩
  have hsq : (Real.sqrt (2*M))^2 = 2*M := Real.sq_sqrt (by linarith [hMnn])
  nlinarith [hsq, h4]

/-- **η-uniformity** (explicit-threshold form, Remark 3): for
`1 ≤ r ≤ χ√(2M)`, the polynomial factor is at most polynomial in `M`
(`(1+r)^K ≤ (1+χ√2)^K · M^{K/2}` since `1 + r ≤ (1+χ√2)√M`), and with
`(2/3)(2M)^{3/2} = κM^{3/2}` (`kappa_rpow_identity'`) and
`M^{3/2} ≥ M` the exponential is `≤ e^{−κM}`; hence
`η ≤ C' M^{3K/2} e^{−κM} → 0` (mathlib `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`),
so eventually `η ≤ ε`.  (`hχ1` only matches the hypotheses of the consumers: the bound uses only `0 < χ`.) -/
theorem etaMr_tendsto_zero_uniform {C : ℝ} (hC : 0 < C) (K : ℝ) (hK : 0 ≤ K)
    (hχ0 : 0 < χ) (hχ1 : χ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℝ, ∀ M r : ℝ, M₀ ≤ M → 1 ≤ r → r ≤ χ * Real.sqrt (2*M) →
      C * M^K * (1+r)^(K:ℝ) * Real.exp (-(2/3) * (2*M)^(3/2 : ℝ)) ≤ ε := by
  set κ : ℝ := 4 * Real.sqrt 2 / 3 with hκ
  have hκ0 : (0:ℝ) < κ := by rw [hκ]; positivity
  have hbound : ∀ M r : ℝ, 1 ≤ M → 1 ≤ r → r ≤ χ * Real.sqrt (2*M) →
      C * M^K * (1+r)^(K:ℝ) * Real.exp (-(2/3) * (2*M)^(3/2 : ℝ))
        ≤ (C * (1 + χ * Real.sqrt 2)^(K:ℝ)) * (M^((3*K)/2 : ℝ) * Real.exp (-κ * M)) := by
    intro M r hM hr1 hrM
    have hM0 : (0:ℝ) < M := by linarith
    have hsqrt : Real.sqrt (2*M) = Real.sqrt 2 * Real.sqrt M :=
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) M
    have h1rM : 1 + r ≤ (1 + χ * Real.sqrt 2) * Real.sqrt M := by
      have h1 : (1:ℝ) ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM
      have h2 : r ≤ χ * Real.sqrt 2 * Real.sqrt M := hrM.trans (le_of_eq (by rw [hsqrt]; ring))
      calc 1 + r ≤ Real.sqrt M + χ * Real.sqrt 2 * Real.sqrt M := add_le_add h1 h2
        _ = (1 + χ * Real.sqrt 2) * Real.sqrt M := by ring
    have hrpow : (1+r)^(K:ℝ) ≤ (1 + χ * Real.sqrt 2)^(K:ℝ) * M^(K/2 : ℝ) := by
      calc (1+r)^(K:ℝ) ≤ ((1 + χ * Real.sqrt 2) * Real.sqrt M)^(K:ℝ) :=
            Real.rpow_le_rpow (by linarith) h1rM hK
        _ = (1 + χ * Real.sqrt 2)^(K:ℝ) * (Real.sqrt M)^(K:ℝ) :=
            Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)
        _ = (1 + χ * Real.sqrt 2)^(K:ℝ) * M^(K/2 : ℝ) := by
            congr 1
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hM0.le]
            congr 1
            ring
    have hexp : Real.exp (-(2/3) * (2*M)^(3/2 : ℝ)) ≤ Real.exp (-κ * M) := by
      apply Real.exp_le_exp.mpr
      have h32 : M ≤ M^(3/2 : ℝ) := by
        calc M = M^(1 : ℝ) := (Real.rpow_one M).symm
          _ ≤ M^(3/2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM (by norm_num)
      have hκnn : (0:ℝ) ≤ 4 * Real.sqrt 2 / 3 := by positivity
      have h := mul_le_mul_of_nonneg_left h32 hκnn
      rw [show (-(2/3 : ℝ)) * (2*M)^(3/2 : ℝ) = -((2/3) * (2*M)^(3/2 : ℝ)) from
        neg_mul _ _, kappa_rpow_identity' hM0.le, hκ]
      linarith [h]
    have hχ2nn : (0:ℝ) ≤ 1 + χ * Real.sqrt 2 := by
      have h1 : (0:ℝ) ≤ χ * Real.sqrt 2 := mul_nonneg hχ0.le (Real.sqrt_nonneg 2)
      linarith
    have hPnn : (0:ℝ) ≤ C * M^K * ((1 + χ * Real.sqrt 2)^(K:ℝ) * M^(K/2 : ℝ)) :=
      mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hM0.le _))
        (mul_nonneg (Real.rpow_nonneg hχ2nn _) (Real.rpow_nonneg hM0.le _))
    calc C * M^K * (1+r)^(K:ℝ) * Real.exp (-(2/3) * (2*M)^(3/2 : ℝ))
        ≤ C * M^K * ((1 + χ * Real.sqrt 2)^(K:ℝ) * M^(K/2 : ℝ))
            * Real.exp (-(2/3) * (2*M)^(3/2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrpow (mul_nonneg hC.le (Real.rpow_nonneg hM0.le _)))
            (Real.exp_pos _).le
      _ ≤ C * M^K * ((1 + χ * Real.sqrt 2)^(K:ℝ) * M^(K/2 : ℝ)) * Real.exp (-κ * M) :=
          mul_le_mul_of_nonneg_left hexp hPnn
      _ = (C * (1 + χ * Real.sqrt 2)^(K:ℝ)) * (M^((3*K)/2 : ℝ) * Real.exp (-κ * M)) := by
          rw [show (3*K)/2 = K + K/2 from by ring, Real.rpow_add hM0]
          ring
  have htend : Tendsto
      (fun M : ℝ => (C * (1 + χ * Real.sqrt 2)^(K:ℝ)) * (M^((3*K)/2 : ℝ) * Real.exp (-κ * M)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((3*K)/2) κ hκ0).const_mul
      (C * (1 + χ * Real.sqrt 2)^(K:ℝ))
    rwa [mul_zero] at h
  have hev := htend.eventually (Iio_mem_nhds hε)
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp hev
  refine ⟨max M₁ 1, fun M r hM0 hr1 hrM => ?_⟩
  have hM1 : 1 ≤ M := (le_max_right M₁ 1).trans hM0
  exact (hbound M r hM1 hr1 hrM).trans (hM₁ M ((le_max_left M₁ 1).trans hM0)).le

/-- **The per-operator Step-4 estimate**: from `|Tr A| ≤ η` and
`hsNorm A ≤ η ≤ 1/2`, the first-order expansion bound (`abs_detOneLinRem_le`) gives
`|R(A)| ≤ (η + η²)²/2 · e^{η+η²} + η² ≤ (2e+1)·η²`
(using `η + η² ≤ (3/2)η`, `(3/2)²/2 = 9/8 ≤ 2`, and `e^{η+η²} ≤ e^{3/4} ≤ e`;
constants are existential — no optimization). -/
private theorem abs_detOneLinRem_le_of_le_eta {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {A : E →L[ℝ] E} (hA : IsTraceClass A)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1/2) (htr : |trace A| ≤ η) (hhs : hsNorm A ≤ η) :
    |detOneLinRem A hA| ≤ (2 * Real.exp 1 + 1) * η^2 := by
  have hhs0 : 0 ≤ hsNorm A := hsNorm_nonneg _
  have ht0 : 0 ≤ |trace A| := abs_nonneg _
  have hz : hsNorm A < 1 := lt_of_le_of_lt hhs (by linarith)
  have h2 : hsNorm A ≤ 1/2 := hhs.trans hη
  have hmain := abs_detOneLinRem_le hA hz h2
  have hsq : (|trace A| + hsNorm A ^ 2)^2 ≤ (η + η^2)^2 := by
    apply pow_le_pow_left₀ (add_nonneg ht0 (sq_nonneg _))
    exact add_le_add htr (pow_le_pow_left₀ hhs0 hhs 2)
  have hexp : Real.exp (|trace A| + hsNorm A ^ 2) ≤ Real.exp (η + η^2) :=
    Real.exp_le_exp.mpr (add_le_add htr (pow_le_pow_left₀ hhs0 hhs 2))
  have hdiv : (|trace A| + hsNorm A ^ 2)^2 / 2 ≤ (η + η^2)^2 / 2 :=
    div_le_div_of_nonneg_right hsq (by norm_num : (0:ℝ) ≤ 2)
  have hprod : (|trace A| + hsNorm A ^ 2)^2 / 2 * Real.exp (|trace A| + hsNorm A ^ 2)
      ≤ (η + η^2)^2 / 2 * Real.exp (η + η^2) :=
    mul_le_mul hdiv hexp (Real.exp_pos _).le (div_nonneg (sq_nonneg _) (by norm_num))
  have hη2 : η^2 ≤ η * (1/2) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hη hη0
  have hηη : η + η^2 ≤ (3/2) * η := by linarith [hη2]
  have hη34 : η + η^2 ≤ 3/4 := by nlinarith [hη2, hη]
  have hfin : (η + η^2)^2 / 2 * Real.exp (η + η^2) + η^2 ≤ (2 * Real.exp 1 + 1) * η^2 := by
    have h1 : (η + η^2)^2 / 2 ≤ 2 * η^2 := by
      have h2 : (η + η^2)^2 ≤ ((3/2) * η)^2 :=
        pow_le_pow_left₀ (add_nonneg hη0 (sq_nonneg _)) hηη 2
      nlinarith [h2, sq_nonneg η]
    have h3 : Real.exp (η + η^2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith [hη34])
    calc (η + η^2)^2 / 2 * Real.exp (η + η^2) + η^2
        ≤ (2 * η^2) * Real.exp 1 + η^2 := by
          exact add_le_add (mul_le_mul h1 h3 (Real.exp_pos _).le (by nlinarith [sq_nonneg η]))
            le_rfl
      _ = (2 * Real.exp 1 + 1) * η^2 := by ring
  exact hmain.trans ((add_le_add hprod (pow_le_pow_left₀ hhs0 hhs 2)).trans hfin)

/-- **Step 4, the remainder bound**: with `C₀, K₀` from
`twoInt_stepThree` and the threshold from `etaMr_tendsto_zero_uniform` at `ε = 1/2`
(so `η ≤ 1/2` discharges the first-order expansion side conditions `hsNorm A < 1`, `hsNorm A ≤ 1/2`),
each of the three remainders is `≤ (2e+1)·η²`, and
`η² = C₀² M^{2K₀} (1+r)^{2K₀} e^{−2κM^{3/2}}` (H4 `rpow_sqrt_two_mul_cube` + the
κ-identity; the rpow-square `(M^{K₀})² = M^{2K₀}` via `← Real.rpow_natCast` +
`← Real.rpow_mul`).  The paper's "enlarging K" is `K := 2K₀`. -/
theorem twoInt_rem_abs_le (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C K M₀ : ℝ, 0 < C ∧ ∀ {M r : ℝ} (hM0 : M₀ ≤ M) (hr : 1 ≤ r)
      (hrM : r ≤ χ * Real.sqrt (2*M)) (hadr : r + 3 ≤ Real.sqrt (2*M))
      (hk1 : MemLp (k1KerT (Real.sqrt (2*M)) M) 2 (volume.prod volume))
      (hk2 : MemLp (k2KerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume))
      (hkcup : MemLp (kcupKerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume))
      (hk1t : IsTraceClass (kernelOperator hk1)) (hk2t : IsTraceClass (kernelOperator hk2))
      (hkcupt : IsTraceClass (kernelOperator hkcup)),
      |detOneLinRem (kernelOperator hk1) hk1t| + |detOneLinRem (kernelOperator hk2) hk2t|
          + |detOneLinRem (kernelOperator hkcup) hkcupt|
        ≤ C * M^K * (1+r)^(K:ℝ) * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
  obtain ⟨C₀, K₀, hC₀, hK₀, H₀⟩ := twoInt_stepThree χ hχ0 hχ1
  obtain ⟨M₁, hM₁⟩ := etaMr_tendsto_zero_uniform hC₀ K₀ hK₀ hχ0 hχ1 (1/2) (by norm_num)
  refine ⟨3 * (2 * Real.exp 1 + 1) * C₀^2, 2*K₀, max M₁ 1, by positivity,
    fun {M r} hM0 hr hrM hadr hk1 hk2 hkcup hk1t hk2t hkcupt => ?_⟩
  have hM1 : 1 ≤ M := (le_max_right M₁ 1).trans hM0
  have hM : 0 < M := by linarith
  have hMnn : (0:ℝ) ≤ M := hM.le
  have hr0 : (0:ℝ) < r := by linarith
  have h1r0 : (0:ℝ) ≤ 1 + r := by linarith
  -- the Step-3 η bounds at `a = √(2M)`
  obtain ⟨h1tr, h1hs, h2tr, h2hs, h3tr, h3hs⟩ := H₀ hM1 hr hadr rfl hk1 hk2 hkcup
  -- η ≤ 1/2 by the η-uniformity (exponent rewritten by H4)
  have hη12 : C₀ * M^K₀ * (1+r)^(K₀:ℝ) * Real.exp (-(2/3) * (Real.sqrt (2*M))^3) ≤ 1/2 := by
    have h := hM₁ M r ((le_max_left M₁ 1).trans hM0) hr hrM
    rwa [← rpow_sqrt_two_mul_cube hMnn] at h
  have hη0 : (0:ℝ) ≤ C₀ * M^K₀ * (1+r)^(K₀:ℝ) * Real.exp (-(2/3) * (Real.sqrt (2*M))^3) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₀.le (Real.rpow_nonneg hMnn _))
      (Real.rpow_nonneg h1r0 _)) (Real.exp_pos _).le
  -- per operator
  have h1 := abs_detOneLinRem_le_of_le_eta hk1t hη0 hη12 h1tr h1hs
  have h2 := abs_detOneLinRem_le_of_le_eta hk2t hη0 hη12 h2tr h2hs
  have h3 := abs_detOneLinRem_le_of_le_eta hkcupt hη0 hη12 h3tr h3hs
  -- the η² packaging
  have hMpow : (M^K₀)^2 = M^(2*K₀) := by
    calc (M^K₀)^2 = (M^(K₀:ℝ))^((2:ℕ):ℝ) := (Real.rpow_natCast (M^K₀) 2).symm
      _ = M^(K₀ * ((2:ℕ):ℝ)) := by rw [← Real.rpow_mul hMnn]
      _ = M^(2*K₀) := by congr 1; norm_num; ring
  have hrpow : ((1+r)^(K₀:ℝ))^2 = (1+r)^(2*K₀) := by
    calc ((1+r)^(K₀:ℝ))^2 = ((1+r)^(K₀:ℝ))^((2:ℕ):ℝ) := (Real.rpow_natCast _ 2).symm
      _ = (1+r)^(K₀ * ((2:ℕ):ℝ)) := by rw [← Real.rpow_mul h1r0]
      _ = (1+r)^(2*K₀) := by congr 1; norm_num; ring
  have hexp2 : (Real.exp (-(2/3) * (Real.sqrt (2*M))^3))^2
      = Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
    have h1 : (Real.exp (-(2/3) * (Real.sqrt (2*M))^3))^2
        = Real.exp (2 * (-(2/3) * (Real.sqrt (2*M))^3)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [h1]
    congr 1
    rw [rpow_sqrt_two_mul_cube hMnn, show (-(2/3 : ℝ)) * (2*M)^(3/2 : ℝ)
        = -((2/3) * (2*M)^(3/2 : ℝ)) from neg_mul _ _, kappa_rpow_identity' hMnn]
    ring
  have hηsq : (C₀ * M^K₀ * (1+r)^(K₀:ℝ) * Real.exp (-(2/3) * (Real.sqrt (2*M))^3))^2
      = C₀^2 * M^(2*K₀) * (1+r)^(2*K₀)
        * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
    rw [mul_pow, mul_pow, mul_pow, hMpow, hrpow, hexp2]
  calc |detOneLinRem (kernelOperator hk1) hk1t| + |detOneLinRem (kernelOperator hk2) hk2t|
        + |detOneLinRem (kernelOperator hkcup) hkcupt|
      ≤ ((2 * Real.exp 1 + 1) * (C₀ * M^K₀ * (1+r)^(K₀:ℝ)
            * Real.exp (-(2/3) * (Real.sqrt (2*M))^3))^2
          + (2 * Real.exp 1 + 1) * (C₀ * M^K₀ * (1+r)^(K₀:ℝ)
            * Real.exp (-(2/3) * (Real.sqrt (2*M))^3))^2)
        + (2 * Real.exp 1 + 1) * (C₀ * M^K₀ * (1+r)^(K₀:ℝ)
            * Real.exp (-(2/3) * (Real.sqrt (2*M))^3))^2 :=
        add_le_add (add_le_add h1 h2) h3
    _ = (3 * (2 * Real.exp 1 + 1) * C₀^2) * M^(2*K₀) * (1+r)^(2*K₀)
          * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
        rw [hηsq]
        ring

/-- **The headline** (operator-level Step 1+4 estimate of the paper's separated-block
estimate): the determinant combination minus `Tr C̃_r` is exactly the
`−R(K̃₁) − R(K̃₂) + R(K̃∪)` remainder (`joint_detOne_comb_twoInt_eq`), bounded
by `twoInt_rem_abs_le`.  Consumed by the main package (`Separated.lean`) together with
the bound `|Tr C̃_r| ≤ C_χ (1+r)^{1/2} e^{−𝒥_M(r)}` and the external bridge records
(`P(A∩B) = …` is NOT formalized here — see the module docstring). -/
theorem joint_detOne_comb_abs_le (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C K M₀ : ℝ, 0 < C ∧ ∀ {M r : ℝ} (hM0 : M₀ ≤ M) (hr : 1 ≤ r)
      (hrM : r ≤ χ * Real.sqrt (2*M)) (hadr : r + 3 ≤ Real.sqrt (2*M))
      (hk1 : MemLp (k1KerT (Real.sqrt (2*M)) M) 2 (volume.prod volume))
      (hk2 : MemLp (k2KerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume))
      (hkcup : MemLp (kcupKerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume))
      (hcr : MemLp (crKerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume))
      (hk1t : IsTraceClass (kernelOperator hk1)) (hk2t : IsTraceClass (kernelOperator hk2))
      (hkcupt : IsTraceClass (kernelOperator hkcup)),
      |1 - fredholmDetOne (kernelOperator hk1) hk1t 1
          - fredholmDetOne (kernelOperator hk2) hk2t 1
          + fredholmDetOne (kernelOperator hkcup) hkcupt 1
          - trace (kernelOperator hcr)|
        ≤ C * M^K * (1+r)^(K:ℝ) * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
  obtain ⟨C, K, M₀, hC, H⟩ := twoInt_rem_abs_le hχ0 hχ1
  refine ⟨C, K, M₀, hC, fun {M r} hM0 hr hrM hadr hk1 hk2 hkcup hcr hk1t hk2t hkcupt => ?_⟩
  have hM : 0 < M := by
    by_contra hneg
    push Not at hneg
    have hzero : Real.sqrt (2*M) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    linarith [hadr, hr]
  rw [joint_detOne_comb_twoInt_eq (by linarith : (0:ℝ) < r) hM hadr hk1 hk2 hkcup hcr
    hk1t hk2t hkcupt, add_sub_cancel_left]
  calc |-detOneLinRem (kernelOperator hk1) hk1t - detOneLinRem (kernelOperator hk2) hk2t
        + detOneLinRem (kernelOperator hkcup) hkcupt|
      ≤ |detOneLinRem (kernelOperator hk1) hk1t| + |detOneLinRem (kernelOperator hk2) hk2t|
        + |detOneLinRem (kernelOperator hkcup) hkcupt| := by
        have key : |-detOneLinRem (kernelOperator hk1) hk1t
              - detOneLinRem (kernelOperator hk2) hk2t
              + detOneLinRem (kernelOperator hkcup) hkcupt|
            ≤ |detOneLinRem (kernelOperator hk1) hk1t| + |detOneLinRem (kernelOperator hk2) hk2t|
              + |detOneLinRem (kernelOperator hkcup) hkcupt| := by
          have h1 : |-detOneLinRem (kernelOperator hk1) hk1t
                - detOneLinRem (kernelOperator hk2) hk2t
                + detOneLinRem (kernelOperator hkcup) hkcupt|
              ≤ |-detOneLinRem (kernelOperator hk1) hk1t|
                + |-detOneLinRem (kernelOperator hk2) hk2t|
                + |detOneLinRem (kernelOperator hkcup) hkcupt| := by
            calc |-detOneLinRem (kernelOperator hk1) hk1t
                  - detOneLinRem (kernelOperator hk2) hk2t
                  + detOneLinRem (kernelOperator hkcup) hkcupt|
                = |-detOneLinRem (kernelOperator hk1) hk1t
                  + -detOneLinRem (kernelOperator hk2) hk2t
                  + detOneLinRem (kernelOperator hkcup) hkcupt| := by congr 1
              _ ≤ (|-detOneLinRem (kernelOperator hk1) hk1t|
                    + |-detOneLinRem (kernelOperator hk2) hk2t|)
                  + |detOneLinRem (kernelOperator hkcup) hkcupt| :=
                  (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
              _ = |-detOneLinRem (kernelOperator hk1) hk1t|
                    + |-detOneLinRem (kernelOperator hk2) hk2t|
                    + |detOneLinRem (kernelOperator hkcup) hkcupt| := by ring
          rwa [abs_neg, abs_neg] at h1
        exact key
    _ ≤ C * M^K * (1+r)^(K:ℝ) * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) :=
        H hM0 hr hrM hadr hk1 hk2 hkcup hk1t hk2t hkcupt

end AiryTwoInt
