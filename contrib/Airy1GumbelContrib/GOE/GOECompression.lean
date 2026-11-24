/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryTransformL2
import Airy1GumbelContrib.Fdd.FddGOE
import Airy1GumbelContrib.GOE.GOEHermiteLeakage
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Compression of the real Airy involution

The GOE kernel operator is the Airy involution compressed to a right half-line.
The localized Hermite packets supply an orthonormal family with small defect.
-/

namespace GOELocalization

open MeasureTheory Set Filter AiryTransform
open scoped ENNReal FourierTransform SchwartzMap Topology InnerProductSpace RealInnerProductSpace

/-- The norm of a Lebesgue L² class, in terms of the chosen representative. -/
theorem norm_goeToLp {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜}
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    ‖hf.toLp f‖ = (eLpNorm f 2 volume).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]

/-- Multiplication by the indicator of a right open half-line on real Lebesgue L². -/
noncomputable def goeCutCLM (x : ℝ) : GOERealL2 →L[ℝ] GOERealL2 := by
  let cut (f : GOERealL2) := ((Lp.memLp f).indicator measurableSet_Ioi.nullMeasurableSet).toLp
    ((Ioi x).indicator (f : ℝ → ℝ))
  have hcut (f : GOERealL2) : (cut f : ℝ → ℝ) =ᵐ[volume] (Ioi x).indicator (f : ℝ → ℝ) :=
    MemLp.coeFn_toLp _
  refine LinearMap.mkContinuous { toFun := cut, map_add' := ?_, map_smul' := ?_ } 1 ?_
  · intro f g
    apply Lp.ext
    filter_upwards [hcut (f + g), hcut f, hcut g, Lp.coeFn_add f g, Lp.coeFn_add (cut f) (cut g)]
      with u hfg hf hg h₁ h₂
    by_cases hu : u ∈ Ioi x <;> simp_all [Pi.add_apply]
  · intro a f
    apply Lp.ext
    filter_upwards [hcut (a • f), hcut f, Lp.coeFn_smul a f, Lp.coeFn_smul a (cut f)]
      with u haf hf h₁ h₂
    by_cases hu : u ∈ Ioi x <;> simp_all [Pi.smul_apply]
  · intro f
    change ‖cut f‖ ≤ 1 * ‖f‖
    rw [one_mul, Lp.norm_def, eLpNorm_congr_ae (hcut f), Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_indicator_le _ measurableSet_Ioi.nullMeasurableSet)

/-- The representative of the cut is the indicated function almost everywhere. -/
theorem goeCutCLM_apply_ae (x : ℝ) (f : GOERealL2) :
    (goeCutCLM x f : ℝ → ℝ) =ᵐ[volume] (Set.Ioi x).indicator (f : ℝ → ℝ) :=
  MemLp.coeFn_toLp ((Lp.memLp f).indicator measurableSet_Ioi.nullMeasurableSet)

/-- A right half-line cut is a contraction. -/
theorem norm_goeCutCLM_le (x : ℝ) (f : GOERealL2) : ‖goeCutCLM x f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (goeCutCLM_apply_ae x f), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_indicator_le _ measurableSet_Ioi.nullMeasurableSet)

/-- A second cut at the same level leaves the function unchanged. -/
theorem goeCutCLM_idem (x : ℝ) (f : GOERealL2) : goeCutCLM x (goeCutCLM x f) = goeCutCLM x f := by
  apply Lp.ext
  filter_upwards [goeCutCLM_apply_ae x (goeCutCLM x f), goeCutCLM_apply_ae x f] with t h₁ h₂
  by_cases ht : t ∈ Ioi x <;> simp_all

/-- Right-cut multiplication is symmetric for the real L² inner product. -/
theorem goeCutCLM_symmetric (x : ℝ) (f g : GOERealL2) :
    ⟪goeCutCLM x f, g⟫_ℝ = ⟪f, goeCutCLM x g⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [goeCutCLM_apply_ae x f, goeCutCLM_apply_ae x g] with t hf hg
  by_cases ht : t ∈ Ioi x <;> simp_all

/-- The Airy integral on an integrable L² representative belongs to L². -/
theorem memLp_goeAiryTransformFun {k : ℝ → ℂ} (h₁ : Integrable k)
    (h₂ : MemLp k 2 volume) : MemLp (airyTransformFun k) 2 volume := by
  rw [memLp_iff]
  exact (eLpNorm_airyTransformFun_le h₁ h₂).trans_lt h₂.eLpNorm_lt_top

/-- The Airy integral is additive across differences of integrable inputs. -/
theorem goeAiryTransformFun_sub {k g : ℝ → ℂ} (hk : Integrable k) (hg : Integrable g) :
    airyTransformFun (k - g) = airyTransformFun k - airyTransformFun g := by
  ext x
  unfold airyTransformFun
  simpa only [Pi.sub_apply, mul_sub] using
    (integral_sub (integrable_airyAiReal_add_mul hk x) (integrable_airyAiReal_add_mul hg x))

/-- On integrable complex L² inputs, the Airy involution has the ordinary Airy integral
representative. Density in L² suffices because the integral is contractive on L¹ ∩ L². -/
theorem goeAiryInvolution_airyTransform_ae {k : ℝ → ℂ} (h₁ : Integrable k)
    (h₂ : MemLp k 2 volume) :
    (goeAiryInvolution (h₂.toLp k) : ℝ → ℂ) =ᵐ[volume] airyTransformFun k := by
  let v := (memLp_goeAiryTransformFun h₁ h₂).toLp (airyTransformFun k)
  have he (g : 𝓢(ℝ, ℂ)) : goeAiryInvolution (g.toLp 2 volume) =
      (memLp_goeAiryTransformFun g.integrable (g.memLp 2)).toLp (airyTransformFun g) := by
    apply Lp.ext
    exact (goeAiryInvolution_toLp_ae g).trans (MemLp.coeFn_toLp _).symm
  have hc (g : 𝓢(ℝ, ℂ)) : dist (goeAiryInvolution (g.toLp 2 volume)) v ≤
      dist (g.toLp 2 volume) (h₂.toLp k) := by
    rw [dist_eq_norm, dist_eq_norm, he g]
    unfold v
    have hg : MemLp (g : ℝ → ℂ) 2 (volume : Measure ℝ) := g.memLp 2
    change _ ≤ ‖hg.toLp (g : ℝ → ℂ) - h₂.toLp k‖
    rw [← MemLp.toLp_sub, ← MemLp.toLp_sub, norm_goeToLp, norm_goeToLp,
      ← goeAiryTransformFun_sub g.integrable h₁]
    exact ENNReal.toReal_mono ((g.memLp 2).sub h₂).eLpNorm_ne_top
      (eLpNorm_airyTransformFun_le (g.integrable.sub h₁) ((g.memLp 2).sub h₂))
  have hv : goeAiryInvolution (h₂.toLp k) = v := by
    by_contra hne
    let d := dist (goeAiryInvolution (h₂.toLp k)) v
    have hd : 0 < d := dist_pos.mpr hne
    obtain ⟨g, hg⟩ := (SchwartzMap.denseRange_toLpCLM (μ := volume)
      (E := ℝ) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top).exists_dist_lt (h₂.toLp k)
        (show 0 < d / 2 by positivity)
    rw [dist_comm] at hg
    change dist (g.toLp 2 volume) (h₂.toLp k) < d / 2 at hg
    have ht := dist_triangle (goeAiryInvolution (h₂.toLp k))
      (goeAiryInvolution (g.toLp 2 volume)) v
    rw [goeAiryInvolution.isometry.dist_eq, dist_comm (h₂.toLp k)] at ht
    change d ≤ _ at ht
    linarith [hc g]
  rw [hv]
  exact MemLp.coeFn_toLp _

/-- Complexification of a real L² representative, as a real linear map. -/
noncomputable def goeComplexify : GOERealL2 →L[ℝ] GOEComplexL2 :=
  Complex.ofRealCLM.compLpL 2 volume

/-- Pointwise formula for L² complexification. -/
theorem goeComplexify_apply_ae (f : GOERealL2) :
    (goeComplexify f : ℝ → ℂ) =ᵐ[volume] fun t => (f t : ℂ) :=
  Complex.ofRealCLM.coeFn_compLp' f

/-- Taking real parts of complex L² representatives. -/
noncomputable def goeRealPart : GOEComplexL2 →L[ℝ] GOERealL2 :=
  Complex.reCLM.compLpL 2 volume

/-- Pointwise formula for the real part in L². -/
theorem goeRealPart_apply_ae (f : GOEComplexL2) :
    (goeRealPart f : ℝ → ℝ) =ᵐ[volume] fun t => (f t).re :=
  Complex.reCLM.coeFn_compLp' f

/-- The real-part map is a left inverse to complexification. -/
theorem goeRealPart_complexify (f : GOERealL2) : goeRealPart (goeComplexify f) = f := by
  apply Lp.ext
  filter_upwards [goeRealPart_apply_ae (goeComplexify f), goeComplexify_apply_ae f] with t ht hs
  rw [ht, hs, Complex.ofReal_re]

/-- Complexification preserves the L² norm. -/
theorem norm_goeComplexify (f : GOERealL2) : ‖goeComplexify f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_
  filter_upwards [goeComplexify_apply_ae f] with t ht
  rw [ht, Complex.norm_real]

/-- A complex L² representative which is real almost everywhere comes from its real part. -/
theorem goeComplexify_realPart_of_ae (f : GOEComplexL2) (hf : ∀ᵐ t ∂volume, (f t).im = 0) :
    goeComplexify (goeRealPart f) = f := by
  apply Lp.ext
  filter_upwards [goeComplexify_apply_ae (goeRealPart f), goeRealPart_apply_ae f, hf] with t ht hs hz
  rw [ht, hs]
  exact Complex.ext (Complex.ofReal_re _) (by simpa using hz.symm)

/-- On a real Schwartz representative, complexification is composition with `Complex.ofReal`. -/
theorem goeComplexify_schwartz_toLp (f : 𝓢(ℝ, ℝ)) :
    goeComplexify (f.toLp 2 volume) = (f.postcompCLM Complex.ofRealCLM).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [goeComplexify_apply_ae (f.toLp 2 volume), f.coeFn_toLp 2 volume,
    (f.postcompCLM Complex.ofRealCLM).coeFn_toLp 2 volume] with t h₁ h₂ h₃
  rw [h₁, h₂, h₃, SchwartzMap.postcompCLM_apply]
  rfl

/-- The complex Airy involution maps the real subspace into itself. -/
theorem goeAiryInvolution_preserves_real (f : GOERealL2) :
    goeComplexify (goeRealPart (goeAiryInvolution (goeComplexify f))) =
      goeAiryInvolution (goeComplexify f) := by
  refine (SchwartzMap.denseRange_toLpCLM (μ := volume) (E := ℝ) (F := ℝ)
    (p := 2) ENNReal.ofNat_ne_top).induction_on f (isClosed_eq ?_ ?_) ?_
  · exact goeComplexify.continuous.comp (goeRealPart.continuous.comp
      (goeAiryInvolution.continuous.comp goeComplexify.continuous))
  · exact goeAiryInvolution.continuous.comp goeComplexify.continuous
  · intro g
    change goeComplexify (goeRealPart (goeAiryInvolution (goeComplexify (g.toLp 2 volume)))) = _
    rw [goeComplexify_schwartz_toLp]
    apply goeComplexify_realPart_of_ae
    filter_upwards [goeAiryInvolution_toLp_ae (g.postcompCLM Complex.ofRealCLM)] with t ht
    rw [ht]
    simp only [SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, ← Complex.ofReal_mul,
      integral_complex_ofReal, Complex.ofReal_im]

/-- The complex Airy transform squares to the identity. -/
theorem goeAiryInvolution_involutive : Function.Involutive goeAiryInvolution := by
  let F := Lp.fourierTransformₗᵢ ℝ ℂ
  let V := goeFrequencyHalfPhase
  let R := goeFourierReflection
  have hF (f : GOEComplexL2) : F (goeAiryInvolution f) = V (R (V.symm (F f))) := by
    simpa only [F, V, R, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
      using DFunLike.congr_fun goeAiryInvolution_frequency (F f)
  have hR (g : GOEComplexL2) : R (R g) = g := by
    apply Lp.ext
    filter_upwards [goeFourierReflection_apply_ae (R g),
      (goeFourierReflection_apply_ae g).comp_tendsto
        goeMeasurePreserving_neg.quasiMeasurePreserving.tendsto_ae] with t h₁ h₂
    simpa using h₁.trans h₂
  intro f
  apply F.injective
  rw [hF, hF, V.symm_apply_apply, hR, V.apply_symm_apply]

/-- The real-linear transport of the existing complex Airy involution. -/
noncomputable def goeRealAiryTransport : GOERealL2 →L[ℝ] GOERealL2 :=
  goeRealPart ∘L (goeAiryInvolution.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
    ∘L goeComplexify

/-- The real transport intertwines with the complex Airy involution. -/
theorem goeComplexify_realAiryTransport (f : GOERealL2) :
    goeComplexify (goeRealAiryTransport f) = goeAiryInvolution (goeComplexify f) :=
  goeAiryInvolution_preserves_real f

/-- The Airy involution on real L² obtained by restricting the complex isometry
to the invariant real subspace. -/
noncomputable def goeRealAiryInvolution : GOERealL2 ≃ₗᵢ[ℝ] GOERealL2 := by
  have hi : Function.Involutive goeRealAiryTransport := by
    intro f
    apply (Function.LeftInverse.injective goeRealPart_complexify)
    rw [goeComplexify_realAiryTransport, goeComplexify_realAiryTransport, goeAiryInvolution_involutive]
  exact { goeRealAiryTransport.toLinearMap with
    invFun := goeRealAiryTransport
    left_inv := hi
    right_inv := hi
    norm_map' := fun f => by
      change ‖goeRealAiryTransport f‖ = ‖f‖
      rw [← norm_goeComplexify (goeRealAiryTransport f), goeComplexify_realAiryTransport,
        goeAiryInvolution.norm_map, norm_goeComplexify] }

/-- Complexification intertwines the real and complex Airy involutions. -/
theorem goeComplexify_realAiryInvolution (f : GOERealL2) :
    goeComplexify (goeRealAiryInvolution f) = goeAiryInvolution (goeComplexify f) :=
  goeComplexify_realAiryTransport f

/-- The real Airy transport is an involution. -/
theorem goeRealAiryInvolution_involutive : Function.Involutive goeRealAiryInvolution :=
  goeRealAiryInvolution.left_inv

/-- The Airy involution is symmetric on the real L² space. -/
theorem goeRealAiryInvolution_symmetric (f g : GOERealL2) :
    ⟪goeRealAiryInvolution f, g⟫_ℝ = ⟪f, goeRealAiryInvolution g⟫_ℝ := by
  conv_lhs => rw [← goeRealAiryInvolution_involutive g]
  exact goeRealAiryInvolution.inner_map_map f (goeRealAiryInvolution g)

/-- The real involution has the ordinary Airy kernel representative on integrable inputs. -/
theorem goeRealAiryInvolution_apply_ae (f : GOERealL2) (hf : Integrable (f : ℝ → ℝ)) :
    (goeRealAiryInvolution f : ℝ → ℝ) =ᵐ[volume] fun u => ∫ v, airyAiReal (u + v) * f v := by
  let k (t : ℝ) : ℂ := (f t : ℂ)
  have hk : MemLp k 2 volume := (Lp.memLp (goeComplexify f)).ae_eq (goeComplexify_apply_ae f)
  have he : goeComplexify f = hk.toLp k :=
    Lp.ext ((goeComplexify_apply_ae f).trans hk.coeFn_toLp.symm)
  have hU : (goeAiryInvolution (goeComplexify f) : ℝ → ℂ) =ᵐ[volume] airyTransformFun k := by
    rw [he]
    exact goeAiryInvolution_airyTransform_ae hf.ofReal hk
  filter_upwards [goeComplexify_apply_ae (goeRealAiryInvolution f), hU] with t h₁ h₂
  rw [goeComplexify_realAiryInvolution] at h₁
  have h := h₁.symm.trans h₂
  apply Complex.ofReal_injective
  simpa only [airyTransformFun, k, ← Complex.ofReal_mul, integral_complex_ofReal] using h

/-- The existing GOE kernel operator equals the Airy involution with a cut on each side. -/
theorem goeOp_eq_cut_involution (M : ℝ) :
    AiryFdd.goeOp (-M) =
      goeCutCLM (-M) ∘L goeRealAiryInvolution.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        goeCutCLM (-M) := by
  let P := goeCutCLM (-M)
  let U := goeRealAiryInvolution
  let A := AiryFdd.goeOp (-M)
  let B := P ∘L U.toContinuousLinearEquiv.toContinuousLinearMap ∘L P
  change A = B
  ext1 f
  refine (SchwartzMap.denseRange_toLpCLM (μ := volume) (E := ℝ) (F := ℝ)
    (p := 2) ENNReal.ofNat_ne_top).induction_on f (isClosed_eq A.continuous B.continuous) ?_
  intro g
  let h := g.toLp 2 volume
  change A h = P (U (P h))
  have hI : Integrable (P h : ℝ → ℝ) := by
    refine (g.integrable.indicator (measurableSet_Ioi (a := -M))).congr ?_
    filter_upwards [goeCutCLM_apply_ae (-M) h, g.coeFn_toLp 2 volume] with t h₁ h₂
    by_cases ht : t ∈ Ioi (-M) <;> simp_all [h, P]
  apply Lp.ext
  filter_upwards [HilbertSchmidt.kernelOperator_apply_ae (AiryFdd.memLp_goeKer (-M)) h,
    goeCutCLM_apply_ae (-M) (U (P h)), goeRealAiryInvolution_apply_ae (P h) hI] with t hA hP hU
  change (A h : ℝ → ℝ) t = ∫ v, AiryFdd.goeKer (-M) (t, v) * h v at hA
  change (P (U (P h)) : ℝ → ℝ) t = _ at hP
  rw [hA, hP]
  by_cases ht : t ∈ Ioi (-M)
  · rw [Set.indicator_of_mem ht, hU]
    apply integral_congr_ae
    filter_upwards [goeCutCLM_apply_ae (-M) h] with y hy
    change P h y = (Ioi (-M)).indicator (h : ℝ → ℝ) y at hy
    by_cases hm : y ∈ Ioi (-M) <;> simp [AiryFdd.goeKer, ht, hm, hy]
  · rw [Set.indicator_of_notMem ht]
    simp [AiryFdd.goeKer, ht]

/-- The GOE operator is self-adjoint. -/
theorem goeOp_isSelfAdjoint (x : ℝ) : IsSelfAdjoint (AiryFdd.goeOp x) := by
  have h := goeOp_eq_cut_involution (-x)
  rw [neg_neg] at h
  rw [h, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change ⟪goeCutCLM x (goeRealAiryInvolution (goeCutCLM x f)), g⟫_ℝ =
    ⟪f, goeCutCLM x (goeRealAiryInvolution (goeCutCLM x g))⟫_ℝ
  rw [goeCutCLM_symmetric, goeRealAiryInvolution_symmetric, goeCutCLM_symmetric]

/-- The GOE compression of the Airy involution is contractive in operator norm. -/
theorem norm_goeOp_le_one (x : ℝ) : ‖AiryFdd.goeOp x‖ ≤ 1 := by
  have h := goeOp_eq_cut_involution (-x)
  rw [neg_neg] at h
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [h, one_mul]
  change ‖goeCutCLM x (goeRealAiryInvolution (goeCutCLM x f))‖ ≤ ‖f‖
  exact (norm_goeCutCLM_le _ _).trans ((goeRealAiryInvolution.norm_map _).le.trans (norm_goeCutCLM_le _ _))

/-- On the unshifted line the Schwartz Hermite profile depends real-linearly on its coefficients. -/
noncomputable def goeHermiteFrequencyLM {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (Fin N → ℝ) →ₗ[ℝ] 𝓢(ℝ, ℂ) where
  toFun c := halfAiryFrequencySchwartz ℓ c 0 (by nlinarith [sq_pos_of_pos hℓ])
  map_add' c d := by
    ext t
    simp only [add_apply, halfAiryFrequencySchwartz_apply, halfAiryFrequencyProfile,
      lowerFrequency_zero, hermiteEvenSum, Pi.add_apply, Complex.ofReal_add, add_mul,
      Finset.sum_add_distrib, mul_add]
  map_smul' r c := by
    ext t
    simp only [RingHom.id_apply, smul_apply, halfAiryFrequencySchwartz_apply,
      halfAiryFrequencyProfile, lowerFrequency_zero, hermiteEvenSum, Pi.smul_apply,
      smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The real L² packet map from the finite-dimensional Hermite coefficient space. -/
noncomputable def goePacketLM {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (Fin N → ℝ) →ₗ[ℝ] GOERealL2 :=
  goeRealPart.toLinearMap ∘ₗ
    ((Lp.fourierTransformₗᵢ ℝ ℂ).symm.toLinearEquiv.toLinearMap.restrictScalars ℝ) ∘ₗ
      (SchwartzMap.toLpCLM ℝ ℂ 2 volume).toLinearMap ∘ₗ goeHermiteFrequencyLM ℓ hℓ

/-- The real packet map takes the real part of the Schwartz packet in L². -/
theorem goePacketLM_eq_realPart {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (c : Fin N → ℝ) :
    goePacketLM ℓ hℓ c = goeRealPart ((halfAiryPacketSchwartz ℓ hℓ c).toLp 2 volume) := by
  change goeRealPart ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
    ((halfAiryFrequencySchwartz ℓ c 0 (by nlinarith [sq_pos_of_pos hℓ])).toLp 2 volume)) = _
  rw [goeFourierInv_toLp, halfAiryPacketSchwartz]

/-- Complexifying the real packet recovers the original packet's L² class. -/
theorem goeComplexify_packetLM {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (c : Fin N → ℝ) :
    goeComplexify (goePacketLM ℓ hℓ c) = (halfAiryPacketSchwartz ℓ hℓ c).toLp 2 volume := by
  rw [goePacketLM_eq_realPart]
  apply goeComplexify_realPart_of_ae
  filter_upwards [(halfAiryPacketSchwartz ℓ hℓ c).coeFn_toLp 2 volume] with x hx
  rw [hx, halfAiryPacketSchwartz_apply, halfAiryPacket_real ℓ hℓ c]

/-- A real packet is fixed by the real Airy involution. -/
theorem goeRealAiryInvolution_packetLM {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (c : Fin N → ℝ) :
    goeRealAiryInvolution (goePacketLM ℓ hℓ c) = goePacketLM ℓ hℓ c := by
  apply (Function.LeftInverse.injective goeRealPart_complexify)
  rw [goeComplexify_realAiryInvolution, goeComplexify_packetLM,
    goeAiryInvolution_halfAiryPacket_toLp]

/-- The real packet has the squared Euclidean norm of its coefficients. -/
theorem norm_sq_goePacketLM {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (c : Fin N → ℝ) :
    ‖goePacketLM ℓ hℓ c‖ ^ 2 = ∑ j, (c j) ^ 2 := by
  rw [← norm_goeComplexify (goePacketLM ℓ hℓ c), goeComplexify_packetLM, norm_sq_schwartz_toLp]
  simp only [halfAiryPacketSchwartz_apply, integral_norm_sq_halfAiryPacket ℓ hℓ c]

/-- The squared norm of a real L² class is the integral of the squared representative. -/
theorem norm_sq_goeRealL2 (f : GOERealL2) : ‖f‖ ^ 2 = ∫ t : ℝ, f t ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

/-- Subtracting the open right cut leaves the complementary closed left cut. -/
theorem goeCutCLM_compl_apply_ae (x : ℝ) (f : GOERealL2) :
    ((f - goeCutCLM x f : GOERealL2) : ℝ → ℝ) =ᵐ[volume] (Iic x).indicator (f : ℝ → ℝ) := by
  filter_upwards [Lp.coeFn_sub f (goeCutCLM x f), goeCutCLM_apply_ae x f] with t h₁ h₂
  rw [h₁, Pi.sub_apply, h₂]
  by_cases ht : x < t
  · simp [ht, not_le_of_gt ht]
  · simp [ht, le_of_not_gt ht]

/-- The real packet's discarded squared norm is exactly the leakage integral. -/
theorem norm_sq_goePacketLM_cut_compl {N : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ)
    (c : Fin N → ℝ) (x : ℝ) :
    ‖goePacketLM ℓ hℓ c - goeCutCLM x (goePacketLM ℓ hℓ c)‖ ^ 2 =
      ∫ t in Iic x, ‖halfAiryPacket ℓ c t‖ ^ 2 := by
  let f := goePacketLM ℓ hℓ c
  change ‖f - goeCutCLM x f‖ ^ 2 = _
  rw [norm_sq_goeRealL2, ← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards [goeCutCLM_compl_apply_ae x f, goeComplexify_apply_ae f,
    (halfAiryPacketSchwartz ℓ hℓ c).coeFn_toLp 2 volume] with t ht hc hrep
  change (goeComplexify (goePacketLM ℓ hℓ c) : ℝ → ℂ) t = (f t : ℂ) at hc
  rw [goeComplexify_packetLM, hrep, halfAiryPacketSchwartz_apply] at hc
  by_cases hm : t ∈ Iic x
  · rw [ht, Set.indicator_of_mem hm, Set.indicator_of_mem hm,
      hc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · rw [ht, Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
    simp

/-- Orthogonal decomposition into the right cut and its complement. -/
theorem goeCut_norm_sq_add_compl (x : ℝ) (ψ : GOERealL2) :
    ‖goeCutCLM x ψ‖ ^ 2 + ‖ψ - goeCutCLM x ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  have horth : ⟪goeCutCLM x ψ, ψ - goeCutCLM x ψ⟫_ℝ = 0 := by
    rw [inner_sub_right, goeCutCLM_symmetric x ψ ψ,
      goeCutCLM_symmetric x ψ (goeCutCLM x ψ), goeCutCLM_idem, sub_self]
  have hsum : goeCutCLM x ψ + (ψ - goeCutCLM x ψ) = ψ := by abel
  have hn := norm_add_sq_real (goeCutCLM x ψ) (ψ - goeCutCLM x ψ)
  rw [hsum, horth, mul_zero, add_zero] at hn
  exact hn.symm

/-- For a fixed vector of the full Airy involution, the compressed defect
is the defect of the portion removed by the cut. -/
theorem goeCut_defect_eq_compl (x : ℝ) (ψ : GOERealL2) (hψ : goeRealAiryInvolution ψ = ψ) :
    ⟪goeCutCLM x ψ, goeCutCLM x ψ - AiryFdd.goeOp x (goeCutCLM x ψ)⟫_ℝ =
      ⟪ψ - goeCutCLM x ψ,
        (ψ - goeCutCLM x ψ) - goeRealAiryInvolution (ψ - goeCutCLM x ψ)⟫_ℝ := by
  let f := goeCutCLM x ψ
  let r := ψ - f
  let U := goeRealAiryInvolution
  change ⟪f, f - AiryFdd.goeOp x f⟫_ℝ = ⟪r, r - U r⟫_ℝ
  have hp : goeCutCLM x f = f := goeCutCLM_idem x ψ
  have hcomp := goeOp_eq_cut_involution (-x)
  rw [neg_neg] at hcomp
  have hB : AiryFdd.goeOp x f = goeCutCLM x (U f) := by
    rw [hcomp]
    change goeCutCLM x (U (goeCutCLM x f)) = _
    rw [hp]
  have hremove : f - U f = -(r - U r) := by
    dsimp only [r, U]
    rw [map_sub, hψ]
    abel
  have hzero : ⟪ψ, r - U r⟫_ℝ = 0 := by
    rw [inner_sub_right, ← goeRealAiryInvolution_symmetric ψ r, hψ, sub_self]
  have hfr : f = ψ - r := by dsimp only [r]; abel
  calc
    _ = ⟪f, f - U f⟫_ℝ := by
      rw [hB, inner_sub_right, inner_sub_right, ← goeCutCLM_symmetric x f (U f), hp]
    _ = _ := by
      rw [hremove, inner_neg_right, hfr, inner_sub_left, hzero, zero_sub, neg_neg]

/-- The defect of any vector under the full involution is at most twice its squared norm. -/
theorem goeAiry_defect_le (r : GOERealL2) :
    ⟪r, r - goeRealAiryInvolution r⟫_ℝ ≤ 2 * ‖r‖ ^ 2 := by
  have h := abs_real_inner_le_norm r (goeRealAiryInvolution r)
  rw [goeRealAiryInvolution.norm_map, ← sq] at h
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  linarith [(neg_le_neg h).trans (neg_abs_le ⟪r, goeRealAiryInvolution r⟫_ℝ)]

/-- The exponential leakage coefficient at the cutoffs used for the packet family is at most one half. -/
theorem goeLeakage_delta_le_half (M : ℝ) (hM : 16 ≤ M) :
    Real.exp (-(M * Real.sqrt M) / 16) ≤ 1 / 2 := by
  have hM₀ : 0 ≤ M := by linarith
  have hs : 1 ≤ Real.sqrt M := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith)
  have hT : 16 ≤ M * Real.sqrt M := hM.trans (by nlinarith [mul_nonneg hM₀ (sub_nonneg.mpr hs)])
  rw [show -(M * Real.sqrt M) / 16 = -(M * Real.sqrt M / 16) by ring,
    Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  linarith [Real.add_one_le_exp (M * Real.sqrt M / 16)]

/-- The image of the retained Hermite packet space has full dimension and uniformly small defect. -/
theorem goeOp_small_defect_family (M : ℝ) (hM : 16 ≤ M) :
    ∃ e : Fin (goeModeCount M) → GOERealL2, Orthonormal ℝ e ∧
      ∀ j, ⟪e j, e j - AiryFdd.goeOp (-M) (e j)⟫_ℝ ≤
        4 * Real.exp (-(M * Real.sqrt M) / 16) := by
  let N := goeModeCount M
  let ℓ := goeEll M
  have hℓ : 0 < ℓ := Real.sqrt_pos.2 (Real.sqrt_pos.2 (by linarith))
  let δ := Real.exp (-(M * Real.sqrt M) / 16)
  have hδ₀ : 0 ≤ δ := Real.exp_nonneg _
  have hδ : δ ≤ 1 / 2 := goeLeakage_delta_le_half M hM
  have hgap : 0 < 1 - δ := by linarith
  let ψ : (Fin N → ℝ) →ₗ[ℝ] GOERealL2 := goePacketLM ℓ hℓ
  let P := goeCutCLM (-M)
  let L := P.toLinearMap ∘ₗ ψ
  have hrem (c : Fin N → ℝ) : ‖ψ c - P (ψ c)‖ ^ 2 ≤ δ * ‖ψ c‖ ^ 2 := by
    change ‖goePacketLM ℓ hℓ c - goeCutCLM (-M) (goePacketLM ℓ hℓ c)‖ ^ 2 ≤
      δ * ‖goePacketLM ℓ hℓ c‖ ^ 2
    rw [norm_sq_goePacketLM_cut_compl, norm_sq_goePacketLM]
    exact halfAiryPacket_leakage M hM c
  have hnorm (c : Fin N → ℝ) : (1 - δ) * ‖ψ c‖ ^ 2 ≤ ‖L c‖ ^ 2 := by
    change (1 - δ) * ‖ψ c‖ ^ 2 ≤ ‖P (ψ c)‖ ^ 2
    linarith [goeCut_norm_sq_add_compl (-M) (ψ c), hrem c]
  have hRayleigh (c : Fin N → ℝ) :
      ⟪L c, L c - AiryFdd.goeOp (-M) (L c)⟫_ℝ ≤ (4 * δ) * ‖L c‖ ^ 2 := by
    change ⟪P (ψ c), P (ψ c) - AiryFdd.goeOp (-M) (P (ψ c))⟫_ℝ ≤ (4 * δ) * ‖L c‖ ^ 2
    rw [goeCut_defect_eq_compl (-M) (ψ c) (goeRealAiryInvolution_packetLM ℓ hℓ c)]
    have hn : ‖ψ c‖ ^ 2 ≤ 2 * ‖L c‖ ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right (show 1 / 2 ≤ 1 - δ by linarith) (sq_nonneg ‖ψ c‖)
      linarith [hnorm c]
    calc
      _ ≤ 2 * ‖ψ c - P (ψ c)‖ ^ 2 := goeAiry_defect_le _
      _ ≤ 2 * (δ * ‖ψ c‖ ^ 2) := by gcongr; exact hrem c
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hn hδ₀]
  have hinj : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro c hc
    have hc' : L c = 0 := LinearMap.mem_ker.mp hc
    have hn := hnorm c
    rw [hc', norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hn
    have hψzero : ψ c = 0 := by
      by_contra hne
      exact (not_lt_of_ge hn) (mul_pos hgap (sq_pos_of_pos (norm_pos_iff.mpr hne)))
    have hs := norm_sq_goePacketLM ℓ hℓ c
    change ‖ψ c‖ ^ 2 = _ at hs
    simp only [hψzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).mp hs.symm
    ext j
    by_contra hne
    exact (pow_ne_zero 2 hne) (hz j (Finset.mem_univ _))
  have hdim : Module.finrank ℝ L.range = N := (LinearMap.finrank_range_of_inj hinj).trans (by simp)
  let b := (stdOrthonormalBasis ℝ L.range).reindex (finCongr hdim)
  let e (j : Fin N) : GOERealL2 := (b j).val
  have ho : Orthonormal ℝ e := L.range.subtypeₗᵢ.orthonormal_comp_iff.mpr b.orthonormal
  refine ⟨e, ho, ?_⟩
  intro j
  obtain ⟨c, hc⟩ := (b j).property
  have hq := hRayleigh c
  change L c = e j at hc
  rw [hc, ho.norm_eq_one j, one_pow, mul_one] at hq
  exact hq

end GOELocalization
