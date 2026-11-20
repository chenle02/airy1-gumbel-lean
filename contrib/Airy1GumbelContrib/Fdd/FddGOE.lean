/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Fdd.FddOp
import Airy1GumbelContrib.FredholmDet.DiskAgreement
import Airy1GumbelContrib.TwoInterval.TwoIntervalTrace
import Airy1GumbelContrib.AiryKernel.AiryKernel
import Airy1GumbelContrib.FredholmDet.DetIsometry

/-!
# The `n = 1` GOE anchor of the fdd

The one-time candidate CDF is the
Ferrari–Spohn GOE determinant:

  `airy1FinCdf {t} x = det(I − P_x B₀ P_x)_{L²(ℝ)}`,

where `P_x B₀ P_x` is the integral operator `goeOp x` with kernel
`goeKer x (u, v) = 1_{u > x} Ai(u + v) 1_{v > x}` (`airy1FinCdf_singleton_eq_goe`).  Under the
shift `u = x + a`, `v = x + b` this is `B_{2x}(a, b) = Ai(a + b + 2x)` on `(0, ∞)²`
(`goeKer_shift`), so the right side is Ferrari–Spohn's `det(I − B_{2x})_{L²(0,∞)} = F_GOE(2x)`
(QR 2013 §1, `P(A₁(0) ≤ m) = F_GOE(2m)`).

## Route (no trace-power argument)

`fddOp = T_V T_W` with `V = e^{−2u} V₁`, `V₁(u, z) = 1_{u > x} p₁(u − z) e^{−2z} φ(z)`.  The
outer weight `e^{−2u}` can be moved across: with `W'(z, y) = W(z, y) 1_{y > x} e^{−2y}`,

  `T_W T_V = T_{W'} T_{V₁}`   (`kernelOperator_wKernel_comp_eq`, the integrands agree a.e.),

and `T_{V₁} T_{W'} = goeOp x` (`compKernel_goeVKer_goeWKer`: heat–Airy convolution).  Two
applications of cyclicity (`fredholmDet_comp_comm`) give
`det(1 − z·fddOp) = det(1 − z·goeOp x)` for every coupling `z`
(`fredholmDet_fddOp_one_level`).  `goeOp x` is trace class (`isTraceClass_goeOp`).

## Ferrari–Spohn form on `L²(0, ∞)`

`fsOp s` is the integral operator `B_s(a, b) = Ai(a + b + s)` on `L²(0, ∞)` (the
`halfLineMeasure` of `AiryKernel/`).  The shift–extension isometry `shiftExt x f (u) = 1_{u > x} f(u − x)`
satisfies `goeOp x ∘ shiftExt x = shiftExt x ∘ fsOp (2x)` (`goeOp_shiftExt`) and `goeOp x`
kills `(range shiftExt x)ᗮ` (`goeOp_eq_zero_of_perp`), so
`fredholmDet_eq_of_isometry_intertwine` (`FredholmDet/`) gives `det(1 − z·goeOp x) = det(1 − z·B_{2x})`
(`fredholmDet_goeOp_eq_fsOp`) and

  `airy1FinCdf {t} x = det(I − B_{2x})_{L²(0,∞)}`   (`airy1FinCdf_singleton_eq_fsGOE`),

the Ferrari–Spohn expression for `F_GOE(2x)`.  That `det(I − B_s)` *is* the GOE Tracy–Widom
distribution is the cited literature identity (Ferrari–Spohn 2005), not proved here.  The
`AiryKernel/` operator `airyKernelOp = T_s T_s*` is the GUE Airy kernel, not a GOE object, so no tie to it is claimed.
-/

namespace AiryFdd

open MeasureTheory Real Set Filter
open HilbertSchmidt
open scoped InnerProductSpace

/-! ## The GOE kernel `P_x B₀ P_x` on `L²(ℝ)` -/

/-- The GOE kernel `1_{u > x} Ai(u + v) 1_{v > x}` (the kernel of `P_x B₀ P_x`). -/
noncomputable def goeKer (x : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Ioi x).indicator (fun _ => (1 : ℝ)) p.1 * airyAiReal (p.1 + p.2)
    * (Ioi x).indicator (fun _ => (1 : ℝ)) p.2

/-- **Ferrari–Spohn shift**: on `(0, ∞)²`, `goeKer x (x + a, x + b) = Ai(a + b + 2x)`, the
kernel `B_{2x}` of `F_GOE(2x) = det(I − B_{2x})_{L²(0,∞)}`. -/
theorem goeKer_shift (x : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    goeKer x (x + a, x + b) = airyAiReal (a + b + 2 * x) := by
  unfold goeKer
  rw [Set.indicator_of_mem (show x + a ∈ Ioi x by simp [ha]),
    Set.indicator_of_mem (show x + b ∈ Ioi x by simp [hb])]
  simp only [one_mul, mul_one]
  congr 1
  ring

/-- Outside `(x, ∞)²` the GOE kernel vanishes. -/
theorem goeKer_eq_zero_of_le (x : ℝ) {p : ℝ × ℝ} (h : p.1 ≤ x ∨ p.2 ≤ x) : goeKer x p = 0 := by
  unfold goeKer
  rcases h with h | h
  · rw [Set.indicator_of_notMem (show p.1 ∉ Ioi x from not_lt.2 h)]; ring
  · rw [Set.indicator_of_notMem (show p.2 ∉ Ioi x from not_lt.2 h)]; ring

theorem measurable_goeKer (x : ℝ) : Measurable (goeKer x) := by
  unfold goeKer
  exact (((measurable_const.indicator measurableSet_Ioi).comp measurable_fst).mul
    (AiryKernel.measurable_airyAiReal.comp (measurable_fst.add measurable_snd))).mul
    ((measurable_const.indicator measurableSet_Ioi).comp measurable_snd)

/-- The GOE kernel is `L²` on the plane (`|Ai(w)| ≤ C e^{−w}`). -/
theorem memLp_goeKer (x : ℝ) : MemLp (goeKer x) 2 (volume.prod volume) := by
  obtain ⟨C, hCpos, hC⟩ := AiryKernel.airyAiReal_abs_le_exp'
  have hI : Integrable (fun u : ℝ => (Ioi x).indicator (fun u => Real.exp (-2 * u)) u) :=
    (integrable_indicator_iff measurableSet_Ioi).2 (exp_neg_integrableOn_Ioi x two_pos)
  refine memLp_of_sq_le (measurable_goeKer x) ((hI.mul_prod hI).const_mul (C ^ 2)) fun p => ?_
  obtain ⟨u, v⟩ := p
  simp only
  by_cases hu : u ∈ Ioi x
  · by_cases hv : v ∈ Ioi x
    · unfold goeKer
      simp only [Set.indicator_of_mem hu, Set.indicator_of_mem hv, one_mul, mul_one]
      have h1 : |airyAiReal (u + v)| ^ 2 ≤ (C * Real.exp (-(u + v))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hC _) 2
      rw [sq_abs] at h1
      calc airyAiReal (u + v) ^ 2 ≤ (C * Real.exp (-(u + v))) ^ 2 := h1
        _ = C ^ 2 * (Real.exp (-2 * u) * Real.exp (-2 * v)) := by
          rw [mul_pow, sq (Real.exp _), ← Real.exp_add, ← Real.exp_add]
          congr 2
          ring
    · rw [goeKer_eq_zero_of_le x (Or.inr (show v ≤ x from not_lt.1 hv)), Set.indicator_of_notMem hv]
      simp
  · rw [goeKer_eq_zero_of_le x (Or.inl (show u ≤ x from not_lt.1 hu)), Set.indicator_of_notMem hu]
    simp

/-- **The GOE operator** `P_x B₀ P_x` on `L²(ℝ)` (kernel `goeKer x`). -/
noncomputable def goeOp (x : ℝ) : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  kernelOperator (memLp_goeKer x)

/-! ## The weight-shifted factors `V₁`, `W'` -/

/-- `V₁(u, z) = 1_{u > x} p₁(u − z) e^{−2z} φ(z)` (the fdd `V` without its outer `e^{−2u}`). -/
noncomputable def goeVKer (x : ℝ) (p : ℝ × ℝ) : ℝ :=
  hitKerN (x, 1) [] p * Real.exp (-2 * p.2) * AiryConj.phiWeight p.2

/-- `W'(z, y) = W_{1,2}(z, y) 1_{y > x} e^{−2y}`. -/
noncomputable def goeWKer (x : ℝ) (p : ℝ × ℝ) : ℝ :=
  AiryConj.wKernel 1 2 p * (Ioi x).indicator (fun y => Real.exp (-2 * y)) p.2

theorem goeVKer_eq_zero_of_le (x : ℝ) {p : ℝ × ℝ} (h : p.1 ≤ x) : goeVKer x p = 0 := by
  unfold goeVKer
  rw [hitKerN_one, Set.indicator_of_notMem (show p.1 ∉ Ioi x from not_lt.2 h)]
  ring

theorem measurable_goeVKer (x : ℝ) : Measurable (goeVKer x) :=
  ((measurable_hitKerN (e := (x, 1)) (L := []) one_pos (fun _ h => absurd h List.not_mem_nil)).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).measurable).mul
    (AiryConj.continuous_phiWeight.comp continuous_snd).measurable

/-- `V₁` is `L²`: `V₁² ≤ (3/2) c₀ 1_{u > x} (e^{−2z} + e^{−6z}) p₁(u − z)`. -/
theorem memLp_goeVKer (x : ℝ) : MemLp (goeVKer x) 2 (volume.prod volume) := by
  have h1 := integrable_halfplane_fst one_pos x 0 (-2) (by norm_num)
  have h2 := integrable_halfplane_fst one_pos x 0 (-6) (by norm_num)
  refine memLp_of_sq_le (measurable_goeVKer x) ((h1.add h2).const_mul (c0 1 * (1 + 2 / 2 ^ 2)))
    fun p => ?_
  obtain ⟨u, z⟩ := p
  simp only [Pi.add_apply]
  by_cases hu : u ∈ Ioi x
  · have hp := (heatKernel_pos one_pos (u - z)).le
    have hc := (c0_pos (S := 1) one_pos).le
    have hH : hitKerN (x, 1) [] (u, z) = heatKernel 1 (u - z) := by
      rw [hitKerN_one]; simp [Set.indicator_of_mem hu]
    have hsq : heatKernel 1 (u - z) ^ 2 ≤ c0 1 * heatKernel 1 (u - z) := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (AiryTwoInt.heatKernel_le one_pos _) hp
    have hw := one_add_sq_le_exp (δ := 2) two_pos z
    simp only [Set.indicator_of_mem hu, zero_mul, Real.exp_zero, one_mul]
    unfold goeVKer
    rw [hH, mul_pow, mul_pow, AiryConj.phiWeight_sq]
    have e4 : Real.exp (-2 * z) ^ 2 = Real.exp (-4 * z) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [e4]
    have hE := (Real.exp_pos (-4 * z)).le
    calc heatKernel 1 (u - z) ^ 2 * Real.exp (-4 * z) * (1 + z ^ 2)
        ≤ (c0 1 * heatKernel 1 (u - z)) * Real.exp (-4 * z)
            * ((1 + 2 / 2 ^ 2) * (Real.exp (2 * z) + Real.exp (-(2 * z)))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hsq hE) hw (by positivity)
            (by positivity)
      _ = c0 1 * (1 + 2 / 2 ^ 2) * (Real.exp (-2 * z) * heatKernel 1 (u - z)
            + Real.exp (-6 * z) * heatKernel 1 (u - z)) := by
          have e1 : Real.exp (-4 * z) * Real.exp (2 * z) = Real.exp (-2 * z) := by
            rw [← Real.exp_add]; congr 1; ring
          have e2 : Real.exp (-4 * z) * Real.exp (-(2 * z)) = Real.exp (-6 * z) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [← e1, ← e2]
          ring
  · rw [goeVKer_eq_zero_of_le x (show u ≤ x from not_lt.1 hu)]
    simp only [Set.indicator_of_notMem hu, zero_mul, add_zero, mul_zero]
    norm_num

theorem measurable_goeWKer (x : ℝ) : Measurable (goeWKer x) :=
  (AiryConj.continuous_wKernel 1 2).measurable.mul
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.indicator
      measurableSet_Ioi).comp measurable_snd)

/-- `W'` is `L²` (dominated by `e^{−2x} |W_{1,2}|`). -/
theorem memLp_goeWKer (x : ℝ) : MemLp (goeWKer x) 2 (volume.prod volume) := by
  have hW : MemLp (AiryConj.wKernel 1 2) 2 (volume.prod volume) :=
    AiryConj.memLp_wKernel one_pos (by norm_num)
  refine (hW.const_mul (Real.exp (-2 * x))).of_le (measurable_goeWKer x).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  unfold goeWKer
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, mul_comm (|Real.exp _|)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [abs_of_pos (Real.exp_pos _)]
  by_cases hp : p.2 ∈ Ioi x
  · rw [Set.indicator_of_mem hp, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by have : x < p.2 := hp; linarith)
  · rw [Set.indicator_of_notMem hp, abs_zero]; exact (Real.exp_pos _).le

/-! ## Kernel identities -/

/-- The heat–Airy convolution against the one-level hitting kernel:
`∫ H(u, z) g₁(z + y) dz = 1_{u > x} Ai(u + y)`. -/
theorem integral_hitKerN_one_backwardAiry (x u y : ℝ) :
    ∫ z : ℝ, hitKerN (x, 1) [] (u, z) * backwardAiry 1 (z + y)
      = (Ioi x).indicator (fun _ => (1 : ℝ)) u * airyAiReal (u + y) := by
  simp_rw [hitKerN_one, mul_assoc]
  rw [integral_const_mul]
  congr 1
  have h := MeasureTheory.integral_add_right_eq_self (μ := volume)
    (fun s : ℝ => heatKernel 1 (u + y - s) * backwardAiry 1 s) y
  rw [← heat_airy_conv 1 one_pos (u + y), ← h]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [show u + y - (z + y) = u - z by ring]

/-- `V₁ ⋆ W' = goeKer x` (the weights `e^{∓2z} φ^{±1}(z)` cancel, `e^{2y} 1_{y>x} e^{−2y} = 1_{y>x}`). -/
theorem compKernel_goeVKer_goeWKer (x : ℝ) :
    AiryConj.compKernel (goeVKer x) (goeWKer x) = goeKer x := by
  funext p
  obtain ⟨u, y⟩ := p
  show ∫ z : ℝ, goeVKer x (u, z) * goeWKer x (z, y) = goeKer x (u, y)
  have hind : Real.exp (2 * y) * (Ioi x).indicator (fun y => Real.exp (-2 * y)) y
      = (Ioi x).indicator (fun _ => (1 : ℝ)) y := by
    by_cases hy : y ∈ Ioi x
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, ← Real.exp_add,
        show 2 * y + -2 * y = 0 by ring, Real.exp_zero]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  have h : ∀ z : ℝ, goeVKer x (u, z) * goeWKer x (z, y)
      = hitKerN (x, 1) [] (u, z) * backwardAiry 1 (z + y)
        * (Real.exp (2 * y) * (Ioi x).indicator (fun y => Real.exp (-2 * y)) y) := by
    intro z
    have hφ : AiryConj.phiWeight z ≠ 0 := (AiryConj.phiWeight_pos z).ne'
    have e : Real.exp (-2 * z) * Real.exp (2 * z) = 1 := by
      rw [← Real.exp_add, show -2 * z + 2 * z = 0 by ring, Real.exp_zero]
    simp only [goeVKer, goeWKer, AiryConj.wKernel]
    calc hitKerN (x, 1) [] (u, z) * Real.exp (-2 * z) * AiryConj.phiWeight z
          * ((AiryConj.phiWeight z)⁻¹ * Real.exp (2 * z) * backwardAiry 1 (z + y)
            * Real.exp (2 * y) * (Ioi x).indicator (fun y => Real.exp (-2 * y)) y)
        = hitKerN (x, 1) [] (u, z) * backwardAiry 1 (z + y)
            * (Real.exp (2 * y) * (Ioi x).indicator (fun y => Real.exp (-2 * y)) y)
            * (Real.exp (-2 * z) * Real.exp (2 * z))
            * (AiryConj.phiWeight z * (AiryConj.phiWeight z)⁻¹) := by ring
      _ = _ := by rw [e, mul_inv_cancel₀ hφ, mul_one, mul_one]
  simp_rw [h]
  rw [integral_mul_const, integral_hitKerN_one_backwardAiry, hind]
  rfl

/-- `T_{V₁} T_{W'} = P_x B₀ P_x`. -/
theorem goeOp_eq_comp (x : ℝ) :
    goeOp x = kernelOperator (memLp_goeVKer x) ∘L kernelOperator (memLp_goeWKer x) := by
  have hcomp : MemLp (AiryConj.compKernel (goeVKer x) (goeWKer x)) 2 (volume.prod volume) := by
    rw [compKernel_goeVKer_goeWKer]; exact memLp_goeKer x
  rw [← AiryTwoInt.kernelOperator_compKernel (memLp_goeVKer x) (memLp_goeWKer x) hcomp]
  exact AiryTwoInt.kernelOperator_congr (compKernel_goeVKer_goeWKer x).symm _ _

/-- **`P_x B₀ P_x` is trace class** on `L²(ℝ)`. -/
theorem isTraceClass_goeOp (x : ℝ) : IsTraceClass (goeOp x) :=
  ⟨_, _, isHilbertSchmidt_kernelOperator _, isHilbertSchmidt_kernelOperator _, goeOp_eq_comp x⟩

/-! ## Moving the outer weight across: `T_W T_V = T_{W'} T_{V₁}` -/

/-- The fdd `V` kernel at one level is `e^{−2u} V₁`. -/
theorem fddVKer_one_level_eq (x : ℝ) (p : ℝ × ℝ) :
    fddVKer (hitKerN (x, 1) []) 2 p = Real.exp (-2 * p.1) * goeVKer x p := by
  unfold fddVKer goeVKer
  ring

theorem memLp_fddVKer_one_level (x : ℝ) :
    MemLp (fddVKer (hitKerN (x, 1) []) 2) 2 (volume.prod volume) := by
  have h := memLp_fddVKer_two_mul (x, 1) [] one_pos (fun _ h => absurd h List.not_mem_nil)
  have e : (2 : ℝ) * gapSum (x, 1) [] = 2 := by simp [gapSum]
  rwa [e] at h

/-- `T_W T_V = T_{W'} T_{V₁}`: for a.e. `y`, `W(z, y) (T_V f)(y) = W'(z, y) (T_{V₁} f)(y)`
(`(T_V f)(y) = e^{−2y} (T_{V₁} f)(y)`, and `T_{V₁} f` vanishes on `y ≤ x`). -/
theorem kernelOperator_wKernel_comp_eq (x : ℝ)
    (hW : MemLp (AiryConj.wKernel 1 2) 2 (volume.prod volume)) :
    kernelOperator hW ∘L kernelOperator (memLp_fddVKer_one_level x)
      = kernelOperator (memLp_goeWKer x) ∘L kernelOperator (memLp_goeVKer x) := by
  apply ContinuousLinearMap.ext
  intro f
  set g := kernelOperator (memLp_fddVKer_one_level x) f
  set g₁ := kernelOperator (memLp_goeVKer x) f
  have hpt : ∀ᵐ y : ℝ ∂volume, ∀ z : ℝ,
      AiryConj.wKernel 1 2 (z, y) * g y = goeWKer x (z, y) * g₁ y := by
    filter_upwards [kernelOperator_apply_ae (memLp_fddVKer_one_level x) f,
      kernelOperator_apply_ae (memLp_goeVKer x) f] with y hy hy₁ z
    have hgy : g y = Real.exp (-2 * y) * g₁ y := by
      rw [hy, hy₁]
      show (∫ w : ℝ, fddVKer (hitKerN (x, 1) []) 2 (y, w) * f w)
        = Real.exp (-2 * y) * ∫ w : ℝ, goeVKer x (y, w) * f w
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only
      rw [fddVKer_one_level_eq]
      ring
    unfold goeWKer
    by_cases hyx : y ∈ Ioi x
    · rw [hgy, Set.indicator_of_mem hyx]; ring
    · have h0 : g₁ y = 0 := by
        rw [hy₁]
        show (∫ w : ℝ, goeVKer x (y, w) * f w) = 0
        simp [goeVKer_eq_zero_of_le x (show (y, _).1 ≤ x from not_lt.1 hyx)]
      rw [hgy, h0, Set.indicator_of_notMem hyx]; ring
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae hW g, kernelOperator_apply_ae (memLp_goeWKer x) g₁]
    with z hz hz'
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hz, hz']
  show (∫ y : ℝ, AiryConj.wKernel 1 2 (z, y) * g y) = ∫ y : ℝ, goeWKer x (z, y) * g₁ y
  exact integral_congr_ae (hpt.mono fun y hy => hy z)

/-! ## The anchor -/

/-- **The one-level fdd determinant is the GOE determinant**, at every coupling `z`:
`det(1 − z·fddOp) = det(1 − z·P_x B₀ P_x)` on `L²(ℝ)` (two cyclicity steps around
`T_W T_V = T_{W'} T_{V₁}`). -/
theorem fredholmDet_fddOp_one_level (x z : ℝ) :
    fredholmDet (fddOp (x, 1) [] one_pos (fun _ h => absurd h List.not_mem_nil) le_rfl) z
      = fredholmDet (goeOp x) z := by
  have hW : MemLp (AiryConj.wKernel 1 2) 2 (volume.prod volume) :=
    AiryConj.memLp_wKernel one_pos (by norm_num)
  have hop : fddOp (x, 1) [] one_pos (fun _ h => absurd h List.not_mem_nil) le_rfl
      = kernelOperator (memLp_fddVKer_one_level x) ∘L kernelOperator hW := by
    unfold fddOp
    congr 1
    · exact AiryTwoInt.kernelOperator_congr (by simp [gapSum]) _ _
    · exact AiryTwoInt.kernelOperator_congr (by simp [gapSum]) _ _
  rw [hop, fredholmDet_comp_comm (isHilbertSchmidt_kernelOperator _)
      (isHilbertSchmidt_kernelOperator _) z, kernelOperator_wKernel_comp_eq x hW,
    fredholmDet_comp_comm (isHilbertSchmidt_kernelOperator _)
      (isHilbertSchmidt_kernelOperator _) z, goeOp_eq_comp]

/-- **`n = 1` GOE anchor.**  The one-time candidate CDF is the Ferrari–Spohn GOE
determinant `det(I − P_x B₀ P_x)_{L²(ℝ)}` at the level `x = x_t`; by `goeKer_shift` this is
`det(I − B_{2x})_{L²(0,∞)} = F_GOE(2x)`. -/
theorem airy1FinCdf_singleton_eq_goe (t : ℝ) (x : ({t} : Finset ℝ) → ℝ) :
    airy1FinCdf {t} x = fredholmDet (goeOp (x ⟨t, Finset.mem_singleton_self t⟩)) 1 := by
  rw [airy1FinCdf_singleton, fredholmDet_fddOp_one_level]


/-! ## Transport to `L²(0, ∞)`: Ferrari–Spohn's `det(I − B_{2x})`

The isometry `shiftExt x : L²(0, ∞) → L²(ℝ)`, `f ↦ 1_{u > x} f(u − x)`, intertwines
`B_{2x}` with `P_x B₀ P_x`, and `P_x B₀ P_x` kills `(range shiftExt)ᗮ`;
`fredholmDet_eq_of_isometry_intertwine` then identifies the two determinants. -/

/-- The Ferrari–Spohn kernel `B_s(a, b) = Ai(a + b + s)` (on `(0, ∞)²`). -/
noncomputable def fsKer (s : ℝ) (p : ℝ × ℝ) : ℝ := airyAiReal (p.1 + p.2 + s)

theorem measurable_fsKer (s : ℝ) : Measurable (fsKer s) :=
  AiryKernel.measurable_airyAiReal.comp ((measurable_fst.add measurable_snd).add_const s)

/-- `B_s` is `L²` on `(0, ∞)²`. -/
theorem memLp_fsKer (s : ℝ) :
    MemLp (fsKer s) 2 (AiryKernel.halfLineMeasure.prod AiryKernel.halfLineMeasure) := by
  obtain ⟨C, -, hC⟩ := AiryKernel.airyAiReal_abs_le_exp'
  have hI : Integrable (fun u : ℝ => Real.exp (-2 * u)) AiryKernel.halfLineMeasure :=
    exp_neg_integrableOn_Ioi 0 two_pos
  have hF := (hI.mul_prod hI).const_mul (C ^ 2 * Real.exp (-2 * s))
  refine (memLp_two_iff_integrable_sq (measurable_fsKer s).aestronglyMeasurable).2
    (hF.mono' ((measurable_fsKer s).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : |fsKer s p| ^ 2 ≤ (C * Real.exp (-(p.1 + p.2 + s))) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hC _) 2
  rw [sq_abs] at h1
  refine h1.trans (le_of_eq ?_)
  have e : Real.exp (-(p.1 + p.2 + s)) ^ 2
      = Real.exp (-2 * s) * (Real.exp (-2 * p.1) * Real.exp (-2 * p.2)) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, e]
  ring

/-- **Ferrari–Spohn's operator** `B_s` on `L²(0, ∞)`; `F_GOE(s) = det(I − B_s)`. -/
noncomputable def fsOp (s : ℝ) :
    Lp ℝ 2 AiryKernel.halfLineMeasure →L[ℝ] Lp ℝ 2 AiryKernel.halfLineMeasure :=
  kernelOperator (memLp_fsKer s)

/-- `jFun x f (u) = 1_{u > x} f(u − x)` (shift by `x`, extension by zero). -/
noncomputable def jFun (x : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := (Ioi x).indicator fun u => f (u - x)

theorem measurePreserving_shift (x : ℝ) :
    MeasurePreserving (fun u : ℝ => u - x) (volume.restrict (Ioi x))
      AiryKernel.halfLineMeasure := by
  have h := (measurePreserving_sub_right (volume : Measure ℝ) x).restrict_preimage
    (measurableSet_Ioi (a := (0 : ℝ)))
  have hpre : (fun u : ℝ => u - x) ⁻¹' Ioi 0 = Ioi x := by
    ext u; simp
  rwa [hpre] at h

theorem memLp_jFun (x : ℝ) {f : ℝ → ℝ} (hf : MemLp f 2 AiryKernel.halfLineMeasure) :
    MemLp (jFun x f) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2
    (hf.comp_measurePreserving (measurePreserving_shift x))

theorem eLpNorm_jFun (x : ℝ) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f AiryKernel.halfLineMeasure) :
    eLpNorm (jFun x f) 2 volume = eLpNorm f 2 AiryKernel.halfLineMeasure := by
  unfold jFun
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi.nullMeasurableSet]
  exact eLpNorm_comp_measurePreserving hf (measurePreserving_shift x)

theorem jFun_ae_congr (x : ℝ) {f g : ℝ → ℝ} (h : f =ᵐ[AiryKernel.halfLineMeasure] g) :
    jFun x f =ᵐ[volume] jFun x g := by
  have h' := (measurePreserving_shift x).quasiMeasurePreserving.ae_eq_comp h
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi] at h'
  filter_upwards [h'] with u hu
  unfold jFun
  by_cases hux : u ∈ Ioi x
  · rw [Set.indicator_of_mem hux, Set.indicator_of_mem hux]; exact hu hux
  · rw [Set.indicator_of_notMem hux, Set.indicator_of_notMem hux]

/-- **The shift–extension isometry** `L²(0, ∞) → L²(ℝ)`, `f ↦ 1_{u > x} f(u − x)`. -/
noncomputable def shiftExt (x : ℝ) :
    Lp ℝ 2 AiryKernel.halfLineMeasure →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ) where
  toFun f := (memLp_jFun x (Lp.memLp f)).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_jFun x (Lp.memLp (f + g))),
      Lp.coeFn_add ((memLp_jFun x (Lp.memLp f)).toLp _) ((memLp_jFun x (Lp.memLp g)).toLp _),
      MemLp.coeFn_toLp (memLp_jFun x (Lp.memLp f)), MemLp.coeFn_toLp (memLp_jFun x (Lp.memLp g)),
      jFun_ae_congr x (Lp.coeFn_add f g)] with u h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5]
    unfold jFun
    by_cases hux : u ∈ Ioi x
    · simp [Set.indicator_of_mem hux]
    · simp [Set.indicator_of_notMem hux]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_jFun x (Lp.memLp (c • f))),
      Lp.coeFn_smul c ((memLp_jFun x (Lp.memLp f)).toLp _),
      MemLp.coeFn_toLp (memLp_jFun x (Lp.memLp f)),
      jFun_ae_congr x (Lp.coeFn_smul c f)] with u h1 h2 h3 h5
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h5]
    unfold jFun
    by_cases hux : u ∈ Ioi x
    · simp [Set.indicator_of_mem hux]
    · simp [Set.indicator_of_notMem hux]
  norm_map' f := by
    show ‖(memLp_jFun x (Lp.memLp f)).toLp (jFun x f)‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _),
      eLpNorm_jFun x (Lp.aestronglyMeasurable f)]

theorem shiftExt_ae (x : ℝ) (f : Lp ℝ 2 AiryKernel.halfLineMeasure) :
    shiftExt x f =ᵐ[volume] jFun x f :=
  MemLp.coeFn_toLp (memLp_jFun x (Lp.memLp f))

/-- **Intertwining**: `P_x B₀ P_x ∘ shiftExt = shiftExt ∘ B_{2x}`. -/
theorem goeOp_shiftExt (x : ℝ) (g : Lp ℝ 2 AiryKernel.halfLineMeasure) :
    goeOp x (shiftExt x g) = shiftExt x (fsOp (2 * x) g) := by
  apply Lp.ext
  have hR : ∀ᵐ u ∂volume, shiftExt x (fsOp (2 * x) g) u
      = (Ioi x).indicator
          (fun u => ∫ s, fsKer (2 * x) (u - x, s) * g s ∂AiryKernel.halfLineMeasure) u := by
    filter_upwards [shiftExt_ae x (fsOp (2 * x) g),
      jFun_ae_congr x (kernelOperator_apply_ae (memLp_fsKer (2 * x)) g)] with u h1 h2
    rw [h1]
    exact h2
  filter_upwards [kernelOperator_apply_ae (memLp_goeKer x) (shiftExt x g), hR] with u h1 h2
  show kernelOperator (memLp_goeKer x) (shiftExt x g) u = _
  rw [h1, h2]
  show (∫ v, goeKer x (u, v) * (shiftExt x g) v) = _
  rw [integral_congr_ae ((shiftExt_ae x g).mono fun v hv => by
    show goeKer x (u, v) * (shiftExt x g) v = goeKer x (u, v) * jFun x g v
    rw [hv])]
  by_cases hux : u ∈ Ioi x
  · rw [Set.indicator_of_mem hux]
    have hpt : ∀ v, goeKer x (u, v) * jFun x g v = (Ioi 0).indicator
        (fun s => fsKer (2 * x) (u - x, s) * g s) (v - x) := by
      intro v
      unfold goeKer jFun fsKer
      by_cases hv : v ∈ Ioi x
      · have hv0 : v - x ∈ Ioi (0 : ℝ) := by
          have : x < v := hv
          show 0 < v - x
          linarith
        rw [Set.indicator_of_mem hux, Set.indicator_of_mem hv, Set.indicator_of_mem hv,
          Set.indicator_of_mem hv0]
        simp only
        rw [show u - x + (v - x) + 2 * x = u + v by ring]
        ring
      · have hv0 : v - x ∉ Ioi (0 : ℝ) := by
          have : ¬ x < v := hv
          show ¬ 0 < v - x
          linarith
        rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv,
          Set.indicator_of_notMem hv0]
        ring
    simp_rw [hpt]
    rw [integral_sub_right_eq_self (fun v => (Ioi (0 : ℝ)).indicator
      (fun s => fsKer (2 * x) (u - x, s) * g s) v) x, integral_indicator measurableSet_Ioi]
  · rw [Set.indicator_of_notMem hux]
    have h0 : ∀ v, goeKer x (u, v) * jFun x g v = 0 := fun v => by
      rw [goeKer_eq_zero_of_le x (Or.inl (show u ≤ x from not_lt.1 hux)), zero_mul]
    simp_rw [h0, integral_zero]

theorem goeKer_sq_le (x : ℝ) (p : ℝ × ℝ) : goeKer x p ^ 2 ≤ airyAiReal (p.1 + p.2) ^ 2 := by
  by_cases h : p.1 ≤ x ∨ p.2 ≤ x
  · rw [goeKer_eq_zero_of_le x h, zero_pow two_ne_zero]; exact sq_nonneg _
  · push Not at h
    unfold goeKer
    rw [Set.indicator_of_mem (show p.1 ∈ Ioi x from h.1),
      Set.indicator_of_mem (show p.2 ∈ Ioi x from h.2)]
    simp

/-- The section `s ↦ goeKer x (u, s + x)` is in `L²(0, ∞)`. -/
theorem memLp_goeKer_slice (x u : ℝ) :
    MemLp (fun s => goeKer x (u, s + x)) 2 AiryKernel.halfLineMeasure := by
  obtain ⟨C, -, hC⟩ := AiryKernel.airyAiReal_abs_le_exp'
  have hI : Integrable (fun s : ℝ => Real.exp (-2 * s)) AiryKernel.halfLineMeasure :=
    exp_neg_integrableOn_Ioi 0 two_pos
  have hm : Measurable fun s => goeKer x (u, s + x) :=
    (measurable_goeKer x).comp (measurable_const.prodMk (measurable_id.add_const x))
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
    ((hI.const_mul (C ^ 2 * Real.exp (-2 * (u + x)))).mono' (hm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun s => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  refine (goeKer_sq_le x (u, s + x)).trans ?_
  have h1 : |airyAiReal (u + (s + x))| ^ 2 ≤ (C * Real.exp (-(u + (s + x)))) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hC _) 2
  rw [sq_abs] at h1
  refine h1.trans (le_of_eq ?_)
  have e : Real.exp (-(u + (s + x))) ^ 2 = Real.exp (-2 * (u + x)) * Real.exp (-2 * s) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, e]
  ring

/-- `P_x B₀ P_x` kills `(range shiftExt)ᗮ`: `(goeOp e)(u) = ⟪shiftExt k_u, e⟫` with
`k_u(s) = goeKer x (u, s + x)`. -/
theorem goeOp_eq_zero_of_perp (x : ℝ) (e : Lp ℝ 2 (volume : Measure ℝ))
    (he : ∀ v, ⟪e, shiftExt x v⟫_ℝ = 0) : goeOp x e = 0 := by
  have hint : ∀ u, ∫ v, goeKer x (u, v) * e v = 0 := by
    intro u
    set k := (memLp_goeKer_slice x u).toLp _
    have hk : jFun x k =ᵐ[volume] fun v => goeKer x (u, v) := by
      filter_upwards [jFun_ae_congr x (MemLp.coeFn_toLp (memLp_goeKer_slice x u))] with v hv
      rw [hv]
      unfold jFun
      by_cases hvx : v ∈ Ioi x
      · rw [Set.indicator_of_mem hvx]
        simp only
        rw [sub_add_cancel]
      · rw [Set.indicator_of_notMem hvx,
          goeKer_eq_zero_of_le x (Or.inr (show v ≤ x from not_lt.1 hvx))]
    have h := he k
    rw [MeasureTheory.L2.inner_def] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [shiftExt_ae x k, hk] with v h1 h2
    rw [RCLike.inner_apply, conj_trivial, h1, h2]
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae (memLp_goeKer x) e,
    Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with u h1 h2
  show kernelOperator (memLp_goeKer x) e u = _
  rw [h1, h2]
  exact hint u

/-- **`P_x B₀ P_x` on `L²(ℝ)` and Ferrari–Spohn's `B_{2x}` on `L²(0, ∞)` have the same
entire determinant.** -/
theorem fredholmDet_goeOp_eq_fsOp (x z : ℝ) :
    fredholmDet (goeOp x) z = fredholmDet (fsOp (2 * x)) z :=
  fredholmDet_eq_of_isometry_intertwine (shiftExt x) (isTraceClass_goeOp x) (fsOp (2 * x))
    (goeOp_shiftExt x) (goeOp_eq_zero_of_perp x) z

/-- **`n = 1` GOE anchor, Ferrari–Spohn form.**  The one-time candidate CDF is `det(I − B_{2x})_{L²(0,∞)}`,
`B_{2x}(a, b) = Ai(a + b + 2x)`, i.e. `F_GOE(2x)` (Ferrari–Spohn 2005; QR 2013 §1). -/
theorem airy1FinCdf_singleton_eq_fsGOE (t : ℝ) (x : ({t} : Finset ℝ) → ℝ) :
    airy1FinCdf {t} x = fredholmDet (fsOp (2 * x ⟨t, Finset.mem_singleton_self t⟩)) 1 := by
  rw [airy1FinCdf_singleton_eq_goe, fredholmDet_goeOp_eq_fsOp]

/-! ## Non-vacuity checks -/

/-- Non-vacuity: the GOE kernel is genuinely `Ai(u + v)` on `(x, ∞)²` (not a junk zero kernel). -/
theorem goeKer_of_lt (x : ℝ) {u v : ℝ} (hu : x < u) (hv : x < v) :
    goeKer x (u, v) = airyAiReal (u + v) := by
  unfold goeKer
  rw [Set.indicator_of_mem (show u ∈ Ioi x from hu), Set.indicator_of_mem (show v ∈ Ioi x from hv)]
  ring

/-- Non-vacuity: the GOE kernel is nonzero somewhere (`Ai > 0` on `[0, ∞)`), for every level. -/
theorem goeKer_ne_zero (x : ℝ) : goeKer x (|x| + 1, |x| + 1) ≠ 0 := by
  have h1 : x < |x| + 1 := by have := le_abs_self x; linarith
  rw [goeKer_of_lt x h1 h1]
  exact (airyAiReal_pos_of_nonneg (by positivity)).ne'

end AiryFdd
