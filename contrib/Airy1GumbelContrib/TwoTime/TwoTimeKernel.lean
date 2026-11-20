/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoTime.TwoTimeL2

/-! # Two-time blocks: integrability, the kernel identity `D − B = −K₂₁T`, and the tuned heat
split

* **Integrability of the inner sections**.  `qKer` and `dKer` contain
  the Bochner integral `∫ G(u + y) 1_{y ≤ x₁} p_d(y − m) dy`; it is a genuine integral (not the
  junk value `0`) because the integrand is integrable for `G = Ai` and `G = g_d`
  (`integrable_qKer_integrand`, `integrable_dKer_integrand`).
* **`D − B = −K₂₁T`** at equal levels `x₁ = x₂ = w` (`dOp_sub_goeOp`).  Here
  `T = P e^{dΔ} P` (kernel `tKer`) is *not* Hilbert–Schmidt, so `K₂₁T` is formed as one kernel,
  `k21TKer = compKernel k21Ker tKer`, which is `L²` (`memLp_k21TKer`); the identity comes from the
  heat–Airy semigroup `∫ g_d(u + y) p_d(y − m) dy = Ai(u + m)` split along `1 = 1_{y≤w} + 1_{y>w}`.
* **The heat split with a free weight** `γ` (`compKernel_kaKer_kbKer`):
  `K₂₁ = K_a ⋆ K_b`, `K_a(x, z) = 1_{x>w} p_1(x − z) e^{−γz}`,
  `K_b(z, y) = e^{γz} g_{d+1}(z + y) 1_{y>w}`, valid for every `d` and every `γ` (the weights cancel
  pointwise).  `TwoTimeEst` tunes `γ = s + √(2w + s²)`, `s = d + 1` (for estimate (K1)); the fixed
  weight `a = 2(d + 1)` of `TwoTimeBridge` is not reused.  Re-association with `T`
  (`k21TKer_eq_compKernel`) puts `K₂₁T = K_a ⋆ (K_b ⋆ T)`.
-/

namespace AiryFdd

open MeasureTheory Real Set Filter
open HilbertSchmidt

theorem abs_indicator_one_le (s : Set ℝ) (x : ℝ) :
    |s.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
  by_cases h : x ∈ s <;> simp [h]

theorem indicator_one_nonneg (s : Set ℝ) (x : ℝ) : 0 ≤ s.indicator (fun _ => (1 : ℝ)) x :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) x

theorem measurable_indicator_one (s : Set ℝ) (hs : MeasurableSet s) :
    Measurable (s.indicator fun _ => (1 : ℝ)) :=
  measurable_const.indicator hs

/-! ## 1. Integrability of the inner sections of `qKer` and `dKer` -/

/-- `y ↦ G(u + y) p_d(y − m)` is integrable when `|G(t)| ≤ C e^{−βt}`. -/
theorem integrable_comp_add_mul_heatKernel {G : ℝ → ℝ} (hG : Measurable G) {C β : ℝ}
    (hGb : ∀ t, |G t| ≤ C * Real.exp (-β * t)) {d : ℝ} (hd : 0 < d) (u m : ℝ) :
    Integrable fun y => G (u + y) * heatKernel d (y - m) := by
  have hdom : Integrable fun y =>
      C * Real.exp (-β * u) * (Real.exp (-β * y) * heatKernel d (m - y)) :=
    (integrable_exp_mul_heatKernel hd (-β) m).const_mul _
  refine hdom.mono' ((hG.comp (measurable_const.add measurable_id)).mul
    ((continuous_heatKernel d).comp (continuous_id.sub continuous_const)).measurable).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hd _),
    show m - y = -(y - m) by ring, AiryTwoInt.heatKernel_even]
  calc |G (u + y)| * heatKernel d (y - m)
      ≤ C * Real.exp (-β * (u + y)) * heatKernel d (y - m) :=
        mul_le_mul_of_nonneg_right (hGb _) (heatKernel_nonneg hd _)
    _ = _ := by rw [show -β * (u + y) = -β * u + -β * y by ring, Real.exp_add]; ring

/-- The same with a measurable cut `1_S(y)` in front of the heat kernel. -/
theorem integrable_comp_add_mul_indicator_heatKernel {G : ℝ → ℝ} (hG : Measurable G) {C β : ℝ}
    (hGb : ∀ t, |G t| ≤ C * Real.exp (-β * t)) {d : ℝ} (hd : 0 < d) (u m : ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    Integrable fun y => G (u + y) * (S.indicator (fun _ => (1 : ℝ)) y * heatKernel d (y - m)) := by
  refine ((integrable_comp_add_mul_heatKernel hG hGb hd u m).indicator hS).congr
    (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ S <;> simp [hy]

theorem airy_abs_le_exp_zero : ∃ C : ℝ, ∀ t, |airyAiReal t| ≤ C * Real.exp (-0 * t) := by
  obtain ⟨C, -, hC⟩ := AiryTwoInt.airyAiReal_abs_le'
  exact ⟨C, fun t => by simpa using hC t⟩

/-- **Inner integrability, `Q`**: the inner section of `qKer`,
`y ↦ Ai(u + y) 1_{y ≤ x₁} p_d(y − m)`, is integrable, so `qKer` is the genuine integral. -/
theorem integrable_qKer_integrand (x₁ : ℝ) {d : ℝ} (hd : 0 < d) (u m : ℝ) :
    Integrable fun y => airyAiReal (u + y)
      * ((Iic x₁).indicator (fun _ => (1 : ℝ)) y * heatKernel d (y - m)) := by
  obtain ⟨C, hC⟩ := airy_abs_le_exp_zero
  exact integrable_comp_add_mul_indicator_heatKernel AiryConj.continuous_airyAiReal.measurable hC
    hd u m measurableSet_Iic

/-- **Inner integrability, `D`**: the inner section of `dKer`,
`y ↦ g_d(u + y) 1_{y ≤ x₁} p_d(y − m)`, is integrable (`e^{−dy}` growth against a Gaussian). -/
theorem integrable_dKer_integrand (x₁ : ℝ) {d : ℝ} (hd : 0 < d) (u m : ℝ) :
    Integrable fun y => backwardAiry d (u + y)
      * ((Iic x₁).indicator (fun _ => (1 : ℝ)) y * heatKernel d (y - m)) := by
  obtain ⟨C, hC⟩ := backwardAiry_abs_le_exp_neg hd
  exact integrable_comp_add_mul_indicator_heatKernel (continuous_backwardAiry_s d).measurable hC
    hd u m measurableSet_Iic

/-! ## 2. `T = P e^{dΔ} P` and the kernel `K₂₁T` -/

theorem measurable_k21Ker (x₁ x₂ d : ℝ) : Measurable (k21Ker x₁ x₂ d) :=
  (((measurable_indicator_one _ measurableSet_Ioi).comp measurable_fst).mul
    ((continuous_backwardAiry_s d).comp (continuous_fst.add continuous_snd)).measurable).mul
    ((measurable_indicator_one _ measurableSet_Ioi).comp measurable_snd)

/-- `T(y, m) = 1_{y > w} p_d(y − m) 1_{m > w}`, the kernel of `P e^{dΔ} P` (not `L²`). -/
noncomputable def tKer (w d : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Ioi w).indicator (fun _ => (1 : ℝ)) p.1 * heatKernel d (p.1 - p.2)
    * (Ioi w).indicator (fun _ => (1 : ℝ)) p.2

theorem measurable_tKer (w d : ℝ) : Measurable (tKer w d) :=
  (((measurable_indicator_one _ measurableSet_Ioi).comp measurable_fst).mul
    ((continuous_heatKernel d).comp (continuous_fst.sub continuous_snd)).measurable).mul
    ((measurable_indicator_one _ measurableSet_Ioi).comp measurable_snd)

theorem tKer_nonneg (w : ℝ) {d : ℝ} (hd : 0 < d) (p : ℝ × ℝ) : 0 ≤ tKer w d p :=
  mul_nonneg (mul_nonneg (indicator_one_nonneg _ _) (heatKernel_nonneg hd _))
    (indicator_one_nonneg _ _)

theorem tKer_le (w : ℝ) {d : ℝ} (hd : 0 < d) (p : ℝ × ℝ) : tKer w d p ≤ heatKernel d (p.1 - p.2) := by
  unfold tKer
  have h1 := abs_indicator_one_le (Ioi w) p.1
  have h2 := abs_indicator_one_le (Ioi w) p.2
  have h1' := indicator_one_nonneg (Ioi w) p.1
  have h2' := indicator_one_nonneg (Ioi w) p.2
  rw [abs_of_nonneg h1'] at h1
  rw [abs_of_nonneg h2'] at h2
  have hp := heatKernel_nonneg hd (p.1 - p.2)
  calc _ ≤ 1 * heatKernel d (p.1 - p.2) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 hp) h2 h2' (by positivity)
    _ = _ := by ring

/-- **`K₂₁T`** as one kernel: `(K₂₁T)(u, m) = ∫ K₂₁(u, y) T(y, m) dy`. -/
noncomputable def k21TKer (w d : ℝ) : ℝ × ℝ → ℝ :=
  AiryConj.compKernel (k21Ker w w d) (tKer w d)

/-- **The kernel identity `D = B − K₂₁T`** at equal levels `x₁ = x₂ = w` (pointwise). -/
theorem dKer_eq_goeKer_sub_k21TKer (w : ℝ) {d : ℝ} (hd : 0 < d) :
    dKer w w d = fun p => goeKer w p - k21TKer w d p := by
  funext p
  obtain ⟨u, m⟩ := p
  simp only [dKer, blkKer, goeKer, k21TKer, AiryConj.compKernel, k21Ker, tKer]
  by_cases hu : u ∈ Ioi w
  · by_cases hm : m ∈ Ioi w
    · simp only [Set.indicator_of_mem hu, Set.indicator_of_mem hm, one_mul, mul_one]
      -- the full heat–Airy semigroup
      have hfull : ∫ y, backwardAiry d (u + y) * heatKernel d (y - m) = airyAiReal (u + m) := by
        rw [← heat_airy_conv_backward d hd u m]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        rw [show m - y = -(y - m) by ring, AiryTwoInt.heatKernel_even]
        ring
      obtain ⟨C, hC⟩ := backwardAiry_abs_le_exp_neg hd
      have hmeas := (continuous_backwardAiry_s d).measurable
      have hI1 := integrable_comp_add_mul_indicator_heatKernel hmeas hC hd u m
        (measurableSet_Iic (a := w))
      have hI2 := integrable_comp_add_mul_indicator_heatKernel hmeas hC hd u m
        (measurableSet_Ioi (a := w))
      have hsplit : ∫ y, backwardAiry d (u + y) * heatKernel d (y - m)
          = (∫ y, backwardAiry d (u + y)
              * ((Iic w).indicator (fun _ => (1 : ℝ)) y * heatKernel d (y - m)))
            + ∫ y, backwardAiry d (u + y) * (Ioi w).indicator (fun _ => (1 : ℝ)) y
              * ((Ioi w).indicator (fun _ => (1 : ℝ)) y * heatKernel d (y - m)) := by
        rw [← integral_add hI1 (hI2.congr (Eventually.of_forall fun y => by
          by_cases hy : y ∈ Ioi w <;> simp [hy]))]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        by_cases hy : y ≤ w
        · have hy' : y ∉ Ioi w := not_lt.2 hy
          simp [Set.indicator_of_mem (show y ∈ Iic w from hy), Set.indicator_of_notMem hy']
        · have hy' : y ∈ Ioi w := lt_of_not_ge hy
          simp [Set.indicator_of_notMem (show y ∉ Iic w from hy), Set.indicator_of_mem hy']
      rw [hfull] at hsplit
      linarith
    · simp [Set.indicator_of_notMem hm]
  · simp [Set.indicator_of_notMem hu]

theorem memLp_k21TKer (w : ℝ) {d : ℝ} (hd : 0 < d) :
    MemLp (k21TKer w d) 2 (volume.prod volume) := by
  have h := (memLp_goeKer w).sub (memLp_dKer w w hd)
  have e : (goeKer w - dKer w w d) = k21TKer w d := by
    rw [dKer_eq_goeKer_sub_k21TKer w hd]
    funext p
    simp
  rwa [e] at h

/-- **`K₂₁T`** on `L²(ℝ)`, a Hilbert–Schmidt kernel operator built from the single kernel
`k21TKer` (never `k21Op ∘ T`). -/
noncomputable def k21TOp (w : ℝ) {d : ℝ} (hd : 0 < d) :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  kernelOperator (memLp_k21TKer w hd)

/-- **Deliverable 2: `D − B = −K₂₁T`** (equal levels `x₁ = x₂ = w`, any gap `d > 0`). -/
theorem dOp_sub_goeOp (w : ℝ) {d : ℝ} (hd : 0 < d) :
    dOp w w hd - goeOp w = -k21TOp w hd := by
  have h : dOp w w hd = goeOp w - k21TOp w hd := by
    unfold dOp goeOp k21TOp
    rw [← AiryTwoInt.kernelOperator_sub]
    exact AiryTwoInt.kernelOperator_congr (dKer_eq_goeKer_sub_k21TKer w hd) _ _
  rw [h]
  abel

/-! ## 3. The heat split `K₂₁ = K_a ⋆ K_b` with a free weight `γ` -/

/-- `K_a(x, z) = 1_{x > w} p_1(x − z) e^{−γz}`. -/
noncomputable def kaKer (w γ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Ioi w).indicator (fun _ => (1 : ℝ)) p.1 * heatKernel 1 (p.1 - p.2) * Real.exp (-γ * p.2)

/-- `K_b(z, y) = e^{γz} g_s(z + y) 1_{y > w}`. -/
noncomputable def kbKer (w s γ : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (γ * p.1) * backwardAiry s (p.1 + p.2) * (Ioi w).indicator (fun _ => (1 : ℝ)) p.2

theorem measurable_kaKer (w γ : ℝ) : Measurable (kaKer w γ) :=
  (((measurable_indicator_one _ measurableSet_Ioi).comp measurable_fst).mul
    ((continuous_heatKernel 1).comp (continuous_fst.sub continuous_snd)).measurable).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).measurable

theorem measurable_kbKer (w s γ : ℝ) : Measurable (kbKer w s γ) :=
  (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).measurable).mul
    ((continuous_backwardAiry_s s).comp (continuous_fst.add continuous_snd)).measurable).mul
    ((measurable_indicator_one _ measurableSet_Ioi).comp measurable_snd)

/-- **Heat split**: `K_a ⋆ K_b = K₂₁` (`s = d + 1`, any `d`, any weight `γ`). -/
theorem compKernel_kaKer_kbKer (w d γ : ℝ) :
    AiryConj.compKernel (kaKer w γ) (kbKer w (d + 1) γ) = k21Ker w w d := by
  funext p
  obtain ⟨u, y⟩ := p
  show ∫ z : ℝ, kaKer w γ (u, z) * kbKer w (d + 1) γ (z, y) = _
  have h : ∀ z : ℝ, kaKer w γ (u, z) * kbKer w (d + 1) γ (z, y)
      = (Ioi w).indicator (fun _ => (1 : ℝ)) u
          * (heatKernel 1 (u - z) * backwardAiry (d + 1) (z + y))
          * (Ioi w).indicator (fun _ => (1 : ℝ)) y := by
    intro z
    have e : Real.exp (-γ * z) * Real.exp (γ * z) = 1 := by
      rw [← Real.exp_add, show -γ * z + γ * z = 0 by ring, Real.exp_zero]
    simp only [kaKer, kbKer]
    calc (Ioi w).indicator (fun _ => (1 : ℝ)) u * heatKernel 1 (u - z) * Real.exp (-γ * z)
          * (Real.exp (γ * z) * backwardAiry (d + 1) (z + y)
            * (Ioi w).indicator (fun _ => (1 : ℝ)) y)
        = (Ioi w).indicator (fun _ => (1 : ℝ)) u
            * (heatKernel 1 (u - z) * backwardAiry (d + 1) (z + y))
            * (Ioi w).indicator (fun _ => (1 : ℝ)) y * (Real.exp (-γ * z) * Real.exp (γ * z)) := by
          ring
      _ = _ := by rw [e, mul_one]
  simp_rw [h]
  rw [integral_mul_const, integral_const_mul]
  have hs := congrFun (AiryTwoInt.heatKerTwo_comp_bAiryKer_any one_pos (d + 1)) (u, y)
  have hs' : (∫ z : ℝ, heatKernel 1 (u - z) * backwardAiry (d + 1) (z + y))
      = backwardAiry (d + 1 - 1) (u + y) := hs
  rw [hs', add_sub_cancel_right]
  rfl

/-- `g_0 = Ai`: the GOE kernel is the `d = 0` member of the family. -/
theorem goeKer_eq_k21Ker_zero (w : ℝ) : goeKer w = k21Ker w w 0 := by
  funext p
  simp only [goeKer, k21Ker, backwardAiry_zero]

/-- The domination behind every Fubini step: `|K_a(x, z) K_b(z, y) T(y, m)|` is bounded by a
product `C (e^{−sz} p_1(x − z)) (e^{−sy} p_d(m − y))`. -/
theorem integrable_assoc_ka_kb_t (w γ : ℝ) {d : ℝ} (hd : 0 < d) (x m : ℝ) :
    Integrable (Function.uncurry fun z y : ℝ =>
      kaKer w γ (x, z) * (kbKer w (d + 1) γ (z, y) * tKer w d (y, m))) (volume.prod volume) := by
  obtain ⟨Cg, hCg⟩ := backwardAiry_abs_le_exp_neg (show (0 : ℝ) < d + 1 by linarith)
  have hdom : Integrable (fun q : ℝ × ℝ =>
      Cg * ((Real.exp (-(d + 1) * q.1) * heatKernel 1 (x - q.1))
        * (Real.exp (-(d + 1) * q.2) * heatKernel d (m - q.2)))) (volume.prod volume) :=
    ((integrable_exp_mul_heatKernel one_pos (-(d + 1)) x).mul_prod
      (integrable_exp_mul_heatKernel hd (-(d + 1)) m)).const_mul Cg
  have hmeas : Measurable (Function.uncurry fun z y : ℝ =>
      kaKer w γ (x, z) * (kbKer w (d + 1) γ (z, y) * tKer w d (y, m))) :=
    ((measurable_kaKer w γ).comp (measurable_const.prodMk measurable_fst)).mul
      ((measurable_kbKer w (d + 1) γ).mul
        ((measurable_tKer w d).comp (measurable_snd.prodMk measurable_const)))
  refine hdom.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
  obtain ⟨z, y⟩ := q
  simp only [Function.uncurry_apply_pair, kaKer, kbKer, tKer]
  have e : Real.exp (-γ * z) * Real.exp (γ * z) = 1 := by
    rw [← Real.exp_add, show -γ * z + γ * z = 0 by ring, Real.exp_zero]
  set I₁ := (Ioi w).indicator (fun _ => (1 : ℝ)) x
  set I₂ := (Ioi w).indicator (fun _ => (1 : ℝ)) y
  set I₃ := (Ioi w).indicator (fun _ => (1 : ℝ)) m
  have hrw : I₁ * heatKernel 1 (x - z) * Real.exp (-γ * z)
      * (Real.exp (γ * z) * backwardAiry (d + 1) (z + y) * I₂ * (I₂ * heatKernel d (y - m) * I₃))
      = (I₁ * I₂ * I₂ * I₃) * (heatKernel 1 (x - z) * (backwardAiry (d + 1) (z + y)
          * heatKernel d (y - m))) * (Real.exp (-γ * z) * Real.exp (γ * z)) := by ring
  have hp1 := heatKernel_nonneg one_pos (x - z)
  have hpd := heatKernel_nonneg hd (y - m)
  rw [hrw, e, mul_one, Real.norm_eq_abs, abs_mul (I₁ * I₂ * I₂ * I₃),
    abs_mul (heatKernel 1 (x - z)), abs_mul (backwardAiry (d + 1) (z + y)),
    abs_of_nonneg hp1, abs_of_nonneg hpd]
  have hI : |I₁ * I₂ * I₂ * I₃| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_mul]
    have := abs_indicator_one_le (Ioi w) x
    have := abs_indicator_one_le (Ioi w) y
    have := abs_indicator_one_le (Ioi w) m
    have h1 : |I₁| * |I₂| ≤ 1 := by nlinarith [abs_nonneg I₁, abs_nonneg I₂]
    have h2 : |I₁| * |I₂| * |I₂| ≤ 1 := by nlinarith [abs_nonneg I₂, mul_nonneg (abs_nonneg I₁) (abs_nonneg I₂)]
    nlinarith [abs_nonneg I₃, mul_nonneg (mul_nonneg (abs_nonneg I₁) (abs_nonneg I₂)) (abs_nonneg I₂)]
  have hg := hCg (z + y)
  rw [show m - y = -(y - m) by ring, AiryTwoInt.heatKernel_even]
  have hgexp : Real.exp (-(d + 1) * (z + y))
      = Real.exp (-(d + 1) * z) * Real.exp (-(d + 1) * y) := by
    rw [← Real.exp_add]; ring_nf
  calc |I₁ * I₂ * I₂ * I₃| * (heatKernel 1 (x - z) * (|backwardAiry (d + 1) (z + y)|
        * heatKernel d (y - m)))
      ≤ 1 * (heatKernel 1 (x - z) * (Cg * Real.exp (-(d + 1) * (z + y))
          * heatKernel d (y - m))) := by
        apply mul_le_mul hI _ (by positivity) zero_le_one
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg hpd) hp1
    _ = _ := by rw [hgexp]; ring

/-- **Re-association**: `K₂₁T = K_a ⋆ (K_b ⋆ T)` as kernels (any weight `γ`). -/
theorem k21TKer_eq_compKernel (w γ : ℝ) {d : ℝ} (hd : 0 < d) :
    k21TKer w d = AiryConj.compKernel (kaKer w γ)
      (AiryConj.compKernel (kbKer w (d + 1) γ) (tKer w d)) := by
  unfold k21TKer
  rw [← compKernel_kaKer_kbKer w d γ]
  funext p
  obtain ⟨x, m⟩ := p
  exact AiryTwoInt.compKernel_assoc x m (integrable_assoc_ka_kb_t w γ hd x m)

end AiryFdd
