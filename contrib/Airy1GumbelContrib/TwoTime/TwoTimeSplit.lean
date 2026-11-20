/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FredholmDet.BlockDet
import Airy1GumbelContrib.Fdd.FddGOE

/-! # Two-time fdd: the kernel split `H = P p_S + P̄ p_d P p_1`

For the two-time entries `[(x₁, d), (x₂, 1)]` (levels `x₁` at time `0`, `x₂` at time `d`,
padding `1`, total time `S = d + 1`) the hitting kernel splits as

  `H(u, z) = 1_{u > x₁} p_S(u − z) + 1_{u ≤ x₁} ∫ p_d(u − m) 1_{m > x₂} p_1(m − z) dm`,

i.e. `H = P₁ p_S + P̄₁ p_d P₂ p_1`.  At the level of the weighted fdd kernel
`V = e^{−au} H e^{−az} φ(z)` this reads (`fddVKer_two_level_eq`)

  `V = m(u) · s₁ + r ⋆ s₂`,

with the bounded multiplier `m(u) = 1_{u > x₁} e^{−au}`, the Hilbert–Schmidt kernels
`s₁ = sKer x₁ S a`, `s₂ = sKer x₂ 1 a` (`sKer x τ a (u, z) = 1_{u > x} p_τ(u − z) e^{−az} φ(z)`)
and `r = rKer x₁ x₂ d a` (`r(u, m) = e^{−au} 1_{u ≤ x₁} p_d(u − m) 1_{m > x₂}`).  Hence
(`kernelOperator_fddVKer_two_level`) `T_V = M ∘ T_{s₁} + T_r ∘ T_{s₂}`, where `M = mulOp` is
the multiplication operator (bounded, **not** Hilbert–Schmidt).

Generic tools (used here and in `TwoTimeBlock`): multiplication operators `mulOp` by bounded
measurable functions on `L²(ℝ)`, their composition with kernel operators on either side, and
closure of Hilbert–Schmidt maps between different spaces under addition.
-/

namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

theorem isHilbertSchmidt_iff_sumSq (T : E →L[𝕜] F) :
    IsHilbertSchmidt T ↔ sumSq T (canonicalBasis 𝕜 E) ≠ ⊤ := by
  unfold IsHilbertSchmidt hsENorm
  constructor
  · intro h h'
    apply h
    rw [h']
    exact ENNReal.top_rpow_of_pos (by norm_num)
  · intro h
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) h

/-- **Hilbert–Schmidt maps between (possibly different) Hilbert spaces are closed under
addition.** -/
theorem IsHilbertSchmidt.add' {A B : E →L[𝕜] F} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : IsHilbertSchmidt (A + B) := by
  rw [isHilbertSchmidt_iff_sumSq] at *
  set b := canonicalBasis 𝕜 E
  have hle : sumSq (A + B) b ≤ 4 * (sumSq A b + sumSq B b) := by
    calc sumSq (A + B) b = ∑' i, ‖(A + B) (b i)‖ₑ ^ 2 := rfl
      _ ≤ ∑' i, 4 * (‖A (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2) := by
          apply ENNReal.tsum_le_tsum
          intro i
          rw [add_apply]
          have h1 : ‖A (b i) + B (b i)‖ₑ ≤ ‖A (b i)‖ₑ + ‖B (b i)‖ₑ := enorm_add_le _ _
          refine (pow_le_pow_left' h1 2).trans ?_
          have hsup : (‖A (b i)‖ₑ ⊔ ‖B (b i)‖ₑ) ^ 2 ≤ ‖A (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2 := by
            rcases le_total ‖A (b i)‖ₑ ‖B (b i)‖ₑ with h | h
            · rw [sup_eq_right.2 h]; exact self_le_add_left _ _
            · rw [sup_eq_left.2 h]; exact self_le_add_right _ _
          calc (‖A (b i)‖ₑ + ‖B (b i)‖ₑ) ^ 2
              ≤ (2 * (‖A (b i)‖ₑ ⊔ ‖B (b i)‖ₑ)) ^ 2 := by
                apply pow_le_pow_left'
                rw [two_mul]
                exact add_le_add le_sup_left le_sup_right
            _ = 2 ^ 2 * (‖A (b i)‖ₑ ⊔ ‖B (b i)‖ₑ) ^ 2 := mul_pow _ _ _
            _ ≤ 2 ^ 2 * (‖A (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2) := mul_le_mul' le_rfl hsup
            _ = 4 * (‖A (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2) := by
                rw [show (2 : ENNReal) ^ 2 = 4 from by norm_num]
      _ = 4 * (sumSq A b + sumSq B b) := by
          unfold sumSq
          rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
  exact ne_of_lt (lt_of_le_of_lt hle
    (ENNReal.mul_lt_top (Ne.lt_top ENNReal.ofNat_ne_top)
      (ENNReal.add_lt_top.2 ⟨hA.lt_top, hB.lt_top⟩)))

end HilbertSchmidt

namespace AiryFdd

open MeasureTheory Real Set Filter
open HilbertSchmidt

/-! ## Multiplication operators on `L²(ℝ)` -/

theorem memLp_mul_of_bound {φ : ℝ → ℝ} (hφ : Measurable φ) {c : ℝ} (hc : ∀ x, |φ x| ≤ c)
    (f : Lp ℝ 2 (volume : Measure ℝ)) : MemLp (fun x => φ x * f x) 2 volume :=
  (Lp.memLp f).of_le_mul (hφ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _))

/-- **Multiplication by a bounded measurable function** `φ` (`|φ| ≤ c`) on `L²(ℝ)`. -/
noncomputable def mulOp {φ : ℝ → ℝ} (hφ : Measurable φ) {c : ℝ} (hc : ∀ x, |φ x| ≤ c) :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mul_of_bound hφ hc f).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_mul_of_bound hφ hc (f + g)),
          MemLp.coeFn_toLp (memLp_mul_of_bound hφ hc f),
          MemLp.coeFn_toLp (memLp_mul_of_bound hφ hc g),
          Lp.coeFn_add ((memLp_mul_of_bound hφ hc f).toLp _)
            ((memLp_mul_of_bound hφ hc g).toLp _),
          Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply, mul_add]
      map_smul' := fun r f => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_mul_of_bound hφ hc (r • f)),
          MemLp.coeFn_toLp (memLp_mul_of_bound hφ hc f),
          Lp.coeFn_smul r ((memLp_mul_of_bound hφ hc f).toLp _),
          Lp.coeFn_smul r f] with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, h4, Pi.smul_apply, smul_eq_mul,
          smul_eq_mul]
        ring }
    c (fun f => by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [MemLp.coeFn_toLp (memLp_mul_of_bound hφ hc f)] with x hx
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [hx, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _))

theorem mulOp_apply_ae {φ : ℝ → ℝ} (hφ : Measurable φ) {c : ℝ} (hc : ∀ x, |φ x| ≤ c)
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    (mulOp hφ hc f : ℝ → ℝ) =ᵐ[volume] fun x => φ x * f x :=
  MemLp.coeFn_toLp (memLp_mul_of_bound hφ hc f)

/-- A kernel times a bounded function of the second variable is still `L²`. -/
theorem memLp_mul_snd {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume)) {φ : ℝ → ℝ}
    (hφ : Measurable φ) {c : ℝ} (hc : ∀ x, |φ x| ≤ c) :
    MemLp (fun p : ℝ × ℝ => K p * φ p.2) 2 (volume.prod volume) :=
  hK.of_le_mul (hK.aestronglyMeasurable.mul (hφ.comp measurable_snd).aestronglyMeasurable)
    (Eventually.of_forall fun p => by
      rw [norm_mul, Real.norm_eq_abs (φ _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hc _) (norm_nonneg _))

/-- A kernel times a bounded function of the first variable is still `L²`. -/
theorem memLp_mul_fst {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume)) {φ : ℝ → ℝ}
    (hφ : Measurable φ) {c : ℝ} (hc : ∀ x, |φ x| ≤ c) :
    MemLp (fun p : ℝ × ℝ => φ p.1 * K p) 2 (volume.prod volume) :=
  hK.of_le_mul ((hφ.comp measurable_fst).aestronglyMeasurable.mul hK.aestronglyMeasurable)
    (Eventually.of_forall fun p => by
      rw [norm_mul, Real.norm_eq_abs (φ _)]
      exact mul_le_mul_of_nonneg_right (hc _) (norm_nonneg _))

/-- `T_K ∘ M_φ = T_{K(x, y) φ(y)}`. -/
theorem kernelOperator_comp_mulOp {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume))
    {φ : ℝ → ℝ} (hφ : Measurable φ) {c : ℝ} (hc : ∀ x, |φ x| ≤ c)
    (hKφ : MemLp (fun p : ℝ × ℝ => K p * φ p.2) 2 (volume.prod volume)) :
    kernelOperator hK ∘L mulOp hφ hc = kernelOperator hKφ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae hK (mulOp hφ hc f), kernelOperator_apply_ae hKφ f]
    with x h1 h2
  rw [ContinuousLinearMap.comp_apply, h1, h2]
  show (∫ y, K (x, y) * (mulOp hφ hc f) y) = ∫ y, K (x, y) * φ y * f y
  refine integral_congr_ae ((mulOp_apply_ae hφ hc f).mono fun y hy => ?_)
  simp only
  rw [hy]
  ring

/-- `M_φ ∘ T_K = T_{φ(x) K(x, y)}`. -/
theorem mulOp_comp_kernelOperator {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume))
    {φ : ℝ → ℝ} (hφ : Measurable φ) {c : ℝ} (hc : ∀ x, |φ x| ≤ c)
    (hφK : MemLp (fun p : ℝ × ℝ => φ p.1 * K p) 2 (volume.prod volume)) :
    mulOp hφ hc ∘L kernelOperator hK = kernelOperator hφK := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [mulOp_apply_ae hφ hc (kernelOperator hK f), kernelOperator_apply_ae hK f,
    kernelOperator_apply_ae hφK f] with x h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, h1, h2, h3]
  show φ x * (∫ y, K (x, y) * f y) = ∫ y, φ x * K (x, y) * f y
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

/-! ## The kernels of the split -/

/-- The bounded multiplier `m(u) = 1_{u > x} e^{−au}`. -/
noncomputable def mFun (x a : ℝ) (u : ℝ) : ℝ :=
  (Ioi x).indicator (fun u => Real.exp (-a * u)) u

theorem measurable_mFun (x a : ℝ) : Measurable (mFun x a) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.indicator
    measurableSet_Ioi

theorem abs_mFun_le {a : ℝ} (ha : 0 ≤ a) (x u : ℝ) : |mFun x a u| ≤ Real.exp (-a * x) := by
  unfold mFun
  by_cases hu : u ∈ Ioi x
  · rw [Set.indicator_of_mem hu, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    have : x < u := hu
    nlinarith
  · rw [Set.indicator_of_notMem hu, abs_zero]; exact (Real.exp_pos _).le

/-- `sKer x τ a (u, z) = 1_{u > x} p_τ(u − z) e^{−az} φ(z)` (an fdd `V`-kernel without its outer
weight `e^{−au}`; `goeVKer x = sKer x 1 2`). -/
noncomputable def sKer (x τ a : ℝ) (p : ℝ × ℝ) : ℝ :=
  hitKer1 x τ p * Real.exp (-a * p.2) * AiryConj.phiWeight p.2

theorem measurable_sKer (x τ a : ℝ) : Measurable (sKer x τ a) :=
  ((measurable_hitKer1 x τ).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).measurable).mul
    (AiryConj.continuous_phiWeight.comp continuous_snd).measurable

theorem sKer_eq_zero_of_le (x τ a : ℝ) {p : ℝ × ℝ} (h : p.1 ≤ x) : sKer x τ a p = 0 := by
  unfold sKer
  rw [hitKer1_eq, Set.indicator_of_notMem (show p.1 ∉ Ioi x from not_lt.2 h)]
  ring

/-- `sKer` is `L²` on the plane for `τ, a > 0`. -/
theorem memLp_sKer (x : ℝ) {τ a : ℝ} (hτ : 0 < τ) (ha : 0 < a) :
    MemLp (sKer x τ a) 2 (volume.prod volume) := by
  have h1 := integrable_halfplane_fst hτ x 0 (-a) (by linarith)
  have h2 := integrable_halfplane_fst hτ x 0 (-(3 * a)) (by linarith)
  refine memLp_of_sq_le (measurable_sKer x τ a)
    ((h1.add h2).const_mul (c0 τ * (1 + 2 / a ^ 2))) fun p => ?_
  obtain ⟨u, z⟩ := p
  simp only [Pi.add_apply]
  by_cases hu : u ∈ Ioi x
  · have hp := (heatKernel_pos hτ (u - z)).le
    have hH : hitKer1 x τ (u, z) = heatKernel τ (u - z) := by
      rw [hitKer1_eq]; simp [Set.indicator_of_mem hu]
    have hsq : heatKernel τ (u - z) ^ 2 ≤ c0 τ * heatKernel τ (u - z) := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (AiryTwoInt.heatKernel_le hτ _) hp
    have hw := one_add_sq_le_exp ha z
    simp only [Set.indicator_of_mem hu, zero_mul, Real.exp_zero, one_mul]
    unfold sKer
    rw [hH, mul_pow, mul_pow, AiryConj.phiWeight_sq]
    have e4 : Real.exp (-a * z) ^ 2 = Real.exp (-(2 * a) * z) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [e4]
    have hE := (Real.exp_pos (-(2 * a) * z)).le
    have hc := (c0_pos hτ).le
    calc heatKernel τ (u - z) ^ 2 * Real.exp (-(2 * a) * z) * (1 + z ^ 2)
        ≤ (c0 τ * heatKernel τ (u - z)) * Real.exp (-(2 * a) * z)
            * ((1 + 2 / a ^ 2) * (Real.exp (a * z) + Real.exp (-(a * z)))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hsq hE) hw (by positivity)
            (by positivity)
      _ = c0 τ * (1 + 2 / a ^ 2) * (Real.exp (-a * z) * heatKernel τ (u - z)
            + Real.exp (-(3 * a) * z) * heatKernel τ (u - z)) := by
          have e1 : Real.exp (-(2 * a) * z) * Real.exp (a * z) = Real.exp (-a * z) := by
            rw [← Real.exp_add]; congr 1; ring
          have e2 : Real.exp (-(2 * a) * z) * Real.exp (-(a * z)) = Real.exp (-(3 * a) * z) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [← e1, ← e2]
          ring
  · rw [sKer_eq_zero_of_le x τ a (show (u, z).1 ≤ x from not_lt.1 hu)]
    simp only [Set.indicator_of_notMem hu, zero_mul, add_zero, mul_zero]
    norm_num

/-- `rKer x₁ x₂ d a (u, m) = e^{−au} 1_{u ≤ x₁} p_d(u − m) 1_{m > x₂}` (the kernel of
`U P̄₁ e^{dΔ} P₂`). -/
noncomputable def rKer (x₁ x₂ d a : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-a * p.1) * (Iic x₁).indicator (fun _ => (1 : ℝ)) p.1 * heatKernel d (p.1 - p.2)
    * (Ioi x₂).indicator (fun _ => (1 : ℝ)) p.2

theorem measurable_rKer (x₁ x₂ d a : ℝ) : Measurable (rKer x₁ x₂ d a) :=
  ((((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).measurable).mul
    ((measurable_const.indicator measurableSet_Iic).comp measurable_fst)).mul
    ((continuous_heatKernel d).comp (continuous_fst.sub continuous_snd)).measurable).mul
    ((measurable_const.indicator measurableSet_Ioi).comp measurable_snd)

/-- `rKer` is `L²` on the plane for `d, a > 0`. -/
theorem memLp_rKer (x₁ x₂ : ℝ) {d a : ℝ} (hd : 0 < d) (ha : 0 < a) :
    MemLp (rKer x₁ x₂ d a) 2 (volume.prod volume) := by
  have h := integrable_halfplane_snd hd x₂ (-(2 * a)) a (by linarith)
  refine memLp_of_sq_le (measurable_rKer x₁ x₂ d a)
    (h.const_mul (c0 d * Real.exp (-a * x₂))) fun p => ?_
  obtain ⟨u, v⟩ := p
  have hp := (heatKernel_pos hd (u - v)).le
  have hc := (c0_pos hd).le
  have hsq : heatKernel d (u - v) ^ 2 ≤ c0 d * heatKernel d (u - v) := by
    rw [sq]; exact mul_le_mul_of_nonneg_right (AiryTwoInt.heatKernel_le hd _) hp
  have hI : (Iic x₁).indicator (fun _ => (1 : ℝ)) u ^ 2 ≤ 1 := by
    by_cases hu : u ∈ Iic x₁ <;> simp [hu]
  have e2 : Real.exp (-a * u) ^ 2 = Real.exp (-(2 * a) * u) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hE := (Real.exp_pos (-(2 * a) * u)).le
  simp only
  unfold rKer
  by_cases hv : v ∈ Ioi x₂
  · have hev : 1 ≤ Real.exp (-a * x₂) * Real.exp (a * v) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; have : x₂ < v := hv; nlinarith
    rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
    calc (Real.exp (-a * u) * (Iic x₁).indicator (fun _ => (1 : ℝ)) u * heatKernel d (u - v)
          * 1) ^ 2
        = Real.exp (-(2 * a) * u) * (Iic x₁).indicator (fun _ => (1 : ℝ)) u ^ 2
            * heatKernel d (u - v) ^ 2 := by rw [← e2]; ring
      _ ≤ Real.exp (-(2 * a) * u) * 1 * (c0 d * heatKernel d (u - v)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hI hE) hsq (sq_nonneg _) (by positivity)
      _ ≤ Real.exp (-(2 * a) * u) * 1 * (c0 d * heatKernel d (u - v))
            * (Real.exp (-a * x₂) * Real.exp (a * v)) :=
          le_mul_of_one_le_right (by positivity) hev
      _ = c0 d * Real.exp (-a * x₂) * (Real.exp (a * v)
            * (Real.exp (-(2 * a) * u) * heatKernel d (u - v))) := by ring
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]
    simp

/-! ## The split of the weighted two-time `V`-kernel -/

/-- **The split (kernel level).**  For the two-time entries `[(x₁, d), (x₂, 1)]`:
`V = e^{−au} H e^{−az} φ(z) = m(u) · s₁(u, z) + (r ⋆ s₂)(u, z)` with `S = d + 1`. -/
theorem fddVKer_two_level_eq (x₁ x₂ : ℝ) {d : ℝ} (hd : 0 < d) (a : ℝ) (p : ℝ × ℝ) :
    fddVKer (hitKerN (x₁, d) [(x₂, 1)]) a p
      = mFun x₁ a p.1 * sKer x₁ (d + 1) a p
        + AiryConj.compKernel (rKer x₁ x₂ d a) (sKer x₂ 1 a) p := by
  obtain ⟨u, z⟩ := p
  by_cases hu : u ≤ x₁
  · have hm : mFun x₁ a u = 0 := by
      unfold mFun; rw [Set.indicator_of_notMem (show u ∉ Ioi x₁ from not_lt.2 hu)]
    simp only
    rw [hm, zero_mul, zero_add]
    have hH := hitKerN_cons_eq_integral (e := (x₁, d)) (y := (x₂, 1)) (L := []) hd one_pos
      (fun _ h => absurd h List.not_mem_nil) hu z
    show Real.exp (-a * u) * hitKerN (x₁, d) [(x₂, 1)] (u, z) * Real.exp (-a * z)
        * AiryConj.phiWeight z = ∫ m, rKer x₁ x₂ d a (u, m) * sKer x₂ 1 a (m, z)
    rw [hH]
    have hpt : ∀ m, rKer x₁ x₂ d a (u, m) * sKer x₂ 1 a (m, z)
        = Real.exp (-a * u) * (heatKernel d (u - m) * hitKerN (x₂, 1) [] (m, z))
          * (Real.exp (-a * z) * AiryConj.phiWeight z) := by
      intro m
      simp only [rKer, sKer, hitKerN_nil]
      rw [Set.indicator_of_mem (show u ∈ Iic x₁ from hu), hitKer1_eq]
      by_cases hm : m ∈ Ioi x₂
      · rw [Set.indicator_of_mem hm]; ring
      · rw [Set.indicator_of_notMem hm]; ring
    simp_rw [hpt]
    rw [integral_mul_const, integral_const_mul]
    ring
  · have hu' : x₁ < u := not_le.1 hu
    have hm : mFun x₁ a u = Real.exp (-a * u) := by
      unfold mFun; rw [Set.indicator_of_mem (show u ∈ Ioi x₁ from hu')]
    have h0 : AiryConj.compKernel (rKer x₁ x₂ d a) (sKer x₂ 1 a) (u, z) = 0 := by
      show ∫ m, rKer x₁ x₂ d a (u, m) * sKer x₂ 1 a (m, z) = 0
      have : ∀ m, rKer x₁ x₂ d a (u, m) * sKer x₂ 1 a (m, z) = 0 := fun m => by
        simp only [rKer]
        rw [Set.indicator_of_notMem (show u ∉ Iic x₁ from hu)]
        ring
      simp [this]
    simp only
    rw [h0, add_zero, hm]
    have hH : hitKerN (x₁, d) [(x₂, 1)] (u, z) = hitKer1 x₁ (d + 1) (u, z) := by
      rw [hitKer1_eq, Set.indicator_of_mem (show u ∈ Ioi x₁ from hu'), one_mul]
      show heatKernel (d + 1) (u - z) - (Iic x₁).indicator (fun _ => (1 : ℝ)) u * _ = _
      rw [Set.indicator_of_notMem (show u ∉ Iic x₁ from hu), zero_mul, sub_zero]
    show Real.exp (-a * u) * hitKerN (x₁, d) [(x₂, 1)] (u, z) * Real.exp (-a * z)
        * AiryConj.phiWeight z
      = Real.exp (-a * u) * (hitKer1 x₁ (d + 1) (u, z) * Real.exp (-a * z)
        * AiryConj.phiWeight z)
    rw [hH]
    ring

/-- The composite `r ⋆ s₂` is `L²`. -/
theorem memLp_compKernel_rKer_sKer (x₁ x₂ : ℝ) {d a : ℝ} (hd : 0 < d) (ha : 0 < a) :
    MemLp (AiryConj.compKernel (rKer x₁ x₂ d a) (sKer x₂ 1 a)) 2 (volume.prod volume) :=
  AiryTwoInt.memLp_compKernel (measurable_rKer x₁ x₂ d a) (measurable_sKer x₂ 1 a)
    (memLp_rKer x₁ x₂ hd ha) (memLp_sKer x₂ one_pos ha)

/-- `m(u) s₁(u, z)` is `L²`. -/
theorem memLp_mFun_mul_sKer (x₁ : ℝ) {S a : ℝ} (hS : 0 < S) (ha : 0 < a) :
    MemLp (fun p : ℝ × ℝ => mFun x₁ a p.1 * sKer x₁ S a p) 2 (volume.prod volume) :=
  memLp_mul_fst (memLp_sKer x₁ hS ha) (measurable_mFun x₁ a) (abs_mFun_le ha.le x₁)

/-- **The split (operator level).**  `T_V = M_m ∘ T_{s₁} + T_r ∘ T_{s₂}` for the two-time `V`-kernel
at any weight `a > 0`. -/
theorem kernelOperator_fddVKer_two_level (x₁ x₂ : ℝ) {d a : ℝ} (hd : 0 < d) (ha : 0 < a)
    (hV : MemLp (fddVKer (hitKerN (x₁, d) [(x₂, 1)]) a) 2 (volume.prod volume)) :
    kernelOperator hV
      = mulOp (measurable_mFun x₁ a) (abs_mFun_le ha.le x₁) ∘L
          kernelOperator (memLp_sKer x₁ (by linarith : (0 : ℝ) < d + 1) ha)
        + kernelOperator (memLp_rKer x₁ x₂ hd ha) ∘L kernelOperator (memLp_sKer x₂ one_pos ha) := by
  have hS : (0 : ℝ) < d + 1 := by linarith
  have h1 := memLp_mFun_mul_sKer x₁ hS ha
  have h2 := memLp_compKernel_rKer_sKer x₁ x₂ hd ha
  rw [mulOp_comp_kernelOperator (memLp_sKer x₁ hS ha) _ _ h1,
    ← AiryTwoInt.kernelOperator_compKernel (memLp_rKer x₁ x₂ hd ha) (memLp_sKer x₂ one_pos ha) h2,
    ← AiryTwoInt.kernelOperator_add h1 h2]
  exact AiryTwoInt.kernelOperator_congr (funext (fddVKer_two_level_eq x₁ x₂ hd a)) _ _

end AiryFdd
