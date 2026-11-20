/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.SmallWeight.TwoTimeDefect
import Airy1GumbelContrib.Fdd.FddDrop

/-!
# The two-time CDF defect bound, reverse order

Reverse order `b ≤ a`: `G(b) − F(a, b) = P(A(x) > a, A(x+t) ≤ b)` with `G(b) = F_{{x+t}}(b)`
(the one-time CDF at the **second** time). At a fixed lower level `b ≥ −m₀`:
`|G(b) − F(a, b)| ≤ C(m₀) e^{−(a − b)²/(8t)}` for `0 < t ≤ 1` (`airy1FinCdf_twoTime_defect_rev`).
This avoids time reversal.

Route (same as the forward file, weight-parametric in `w > S = t + τ`):
* the first-time-`⊤` kernel `topKer = p_t ⋆ H_{(b,τ)}` lives in the two-time frame; its
  determinant is the one-time determinant at `(b, τ)` by FddDrop's weight-agnostic
  `fredholmDet_swap_heat` (`W_S ⋆ V_{p_t ⋆ H} = W_{S−t} ⋆ V_H`);
* `H₂ − topKer = 1_{u > a} ∫ p_t(u − x) 1_{x ≤ b} p_τ(x − v) dx` (`revKer`), bounded by the
  reflected Gaussian split, `√2 e^{−(a−b)²/8t} e^{−(u−a)²/8t} p_{2t+τ}(u − v)`, so the generic
  bound `integral_sq_fddVKer_le_gaussDom` applies with centre `a`;
* `‖V_top‖₂² ≤ C_D(w, t, τ, m₀) + C₁(w, t + τ, m₀)`: below `b` the kernel is the defect kernel
  `defectKer b b t τ` (Gaussian bound with `E = 1`), above `b` it is `≤ p_{t+τ}`, the one-time
  kernel at level `b`;
* triangle inequality and the Lipschitz determinant bound.
-/

namespace AiryFdd

open MeasureTheory Real Set Filter
open HilbertSchmidt

/-! ## The first-time-`⊤` kernel -/

/-- The two-time hitting kernel with first level `⊤`: `p_t ⋆ H_{(b,τ)}`. -/
noncomputable def topKer (b t τ : ℝ) : ℝ × ℝ → ℝ :=
  AiryConj.compKernel (AiryTwoInt.heatKerTwo t) (hitKerN (b, τ) [])

theorem measurable_topKer {b t τ : ℝ} (hτ : 0 < τ) : Measurable (topKer b t τ) :=
  AiryTwoInt.measurable_compKernel (AiryTwoInt.measurable_heatKerTwo t)
    (measurable_hitKerN (e := (b, τ)) hτ pos_of_mem_nil)

theorem topKer_mem {b t τ : ℝ} (ht : 0 < t) (hτ : 0 < τ) (p : ℝ × ℝ) :
    0 ≤ topKer b t τ p ∧ topKer b t τ p ≤ heatKernel (t + τ) (p.1 - p.2) :=
  compKernel_heat_mem ht hτ (measurable_hitKerN (e := (b, τ)) hτ pos_of_mem_nil)
    (hitKerN_nonneg (e := (b, τ)) hτ pos_of_mem_nil)
    (fun q => (le_abs_self _).trans (abs_hitKerN_le (e := (b, τ)) hτ pos_of_mem_nil q)) p

theorem topKer_apply (b t τ u v : ℝ) :
    topKer b t τ (u, v) = ∫ w : ℝ, heatKernel t (u - w) * hitKer1 b τ (w, v) := rfl

/-- Below `b` the first-time-`⊤` kernel is the defect kernel at levels `(b, b)`. -/
theorem topKer_eq_defectKer {b t τ u : ℝ} (ht : 0 < t) (hτ : 0 < τ) (hu : u ≤ b) (v : ℝ) :
    topKer b t τ (u, v) = defectKer b b t τ (u, v) := by
  rw [topKer_apply, defectKer_of_le ht hτ hu]

/-! ## The reverse defect kernel -/

/-- The **reverse defect kernel**: two-time hitting kernel minus the first-time-`⊤` kernel. -/
noncomputable def revKer (a b t τ : ℝ) (p : ℝ × ℝ) : ℝ :=
  hitKerN (a, t) [(b, τ)] p - topKer b t τ p

theorem measurable_revKer {a b t τ : ℝ} (ht : 0 < t) (hτ : 0 < τ) :
    Measurable (revKer a b t τ) :=
  (measurable_hitKerN (e := (a, t)) ht (pos_of_mem_single hτ)).sub (measurable_topKer hτ)

theorem revKer_of_le {a b t τ u : ℝ} (ht : 0 < t) (hτ : 0 < τ) (hu : u ≤ a) (v : ℝ) :
    revKer a b t τ (u, v) = 0 := by
  unfold revKer
  rw [hitKerN_cons_eq_integral (e := (a, t)) (y := (b, τ)) (L := []) ht hτ pos_of_mem_nil hu v,
    sub_eq_zero]
  rfl

theorem integrable_heat_mul_lamKer1 {g τ : ℝ} (hg : 0 < g) (hτ : 0 < τ) (b u v : ℝ) :
    Integrable fun w : ℝ => heatKernel g (u - w) * lamKer1 b τ (w, v) :=
  AiryTwoInt.integrable_pair_mul_of_heatKernel_le hg hτ (AiryTwoInt.measurable_heatKerTwo g)
    (measurable_lamKer1 b τ) (fun a b => AiryTwoInt.heatKerTwo_abs_le_self hg (a, b))
    (fun a c => by rw [abs_of_nonneg (lamKer1_nonneg hτ _ _)]; exact lamKer1_le hτ b (a, c)) u v

/-- Above the first level: `R(u, v) = ∫ p_t(u − w) 1_{w ≤ b} p_τ(w − v) dw`. -/
theorem revKer_of_lt {a b t τ u : ℝ} (ht : 0 < t) (hτ : 0 < τ) (hu : a < u) (v : ℝ) :
    revKer a b t τ (u, v) = ∫ w : ℝ, heatKernel t (u - w) * lamKer1 b τ (w, v) := by
  have hn : u ∉ Iic a := not_le.2 hu
  have h2 : hitKerN (a, t) [(b, τ)] (u, v) = heatKernel (t + τ) (u - v) := by
    simp only [hitKerN, lamKerN, gapSum, Set.indicator_of_notMem hn, zero_mul, sub_zero]
  have hsplit : ∀ w : ℝ, heatKernel t (u - w) * hitKer1 b τ (w, v)
      = heatKernel t (u - w) * heatKernel τ (w - v)
        - heatKernel t (u - w) * lamKer1 b τ (w, v) := fun w => by
    simp only [hitKer1]; ring
  unfold revKer
  rw [h2, topKer_apply]
  simp_rw [hsplit]
  rw [integral_sub (integrable_heat_mul_heat ht hτ u v) (integrable_heat_mul_lamKer1 ht hτ b u v),
    AiryTwoInt.heatKernel_conv ht hτ]
  ring

/-- **Pointwise reverse defect bound** (`b ≤ a`):
`0 ≤ R(u, v) ≤ √2 e^{−(b−a)²/8t} e^{−(a−u)²/8t} p_{2t+τ}(u − v)`. -/
theorem revKer_nonneg_le {a b t τ : ℝ} (ht : 0 < t) (hτ : 0 < τ) (hba : b ≤ a) (u v : ℝ) :
    0 ≤ revKer a b t τ (u, v) ∧ revKer a b t τ (u, v) ≤
      Real.sqrt 2 * Real.exp (-(b - a) ^ 2 / (8 * t)) * Real.exp (-(a - u) ^ 2 / (8 * t)) *
        heatKernel (2 * t + τ) (u - v) := by
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have hR : 0 ≤ Real.sqrt 2 * Real.exp (-(b - a) ^ 2 / (8 * t)) *
      Real.exp (-(a - u) ^ 2 / (8 * t)) * heatKernel (2 * t + τ) (u - v) :=
    mul_nonneg (by positivity) (heatKernel_pos (by positivity) _).le
  rcases le_or_gt u a with hu | hu
  · rw [revKer_of_le ht hτ hu]
    exact ⟨le_rfl, hR⟩
  · rw [revKer_of_lt ht hτ hu]
    set K := Real.sqrt 2 * Real.exp (-(b - a) ^ 2 / (8 * t)) *
      Real.exp (-(a - u) ^ 2 / (8 * t)) with hK
    have hK0 : 0 ≤ K := by positivity
    have hint1 := integrable_heat_mul_lamKer1 ht hτ b u v
    have hint2 := (integrable_heat_mul_heat h2t hτ u v).const_mul K
    refine ⟨integral_nonneg fun w => mul_nonneg (heatKernel_pos ht _).le
      (lamKer1_nonneg hτ _ _), ?_⟩
    calc ∫ w : ℝ, heatKernel t (u - w) * lamKer1 b τ (w, v)
        ≤ ∫ w : ℝ, K * (heatKernel (2 * t) (u - w) * heatKernel τ (w - v)) := by
          refine integral_mono hint1 hint2 fun w => ?_
          simp only [lamKer1]
          by_cases hw : w ∈ Iic b
          · rw [Set.indicator_of_mem hw, one_mul]
            have hs := heatKernel_le_split ht (a := -a) (b := -b) (u := -u) (w := -w)
              (by linarith) (by linarith) (by simp only [mem_Iic] at hw; linarith)
            rw [show -u - -w = -(u - w) by ring, AiryTwoInt.heatKernel_even,
              AiryTwoInt.heatKernel_even, show (-b - -a) ^ 2 = (b - a) ^ 2 by ring,
              show (-a - -u) ^ 2 = (a - u) ^ 2 by ring] at hs
            calc heatKernel t (u - w) * heatKernel τ (w - v)
                ≤ (K * heatKernel (2 * t) (u - w)) * heatKernel τ (w - v) :=
                  mul_le_mul_of_nonneg_right hs (heatKernel_pos hτ _).le
              _ = _ := by ring
          · rw [Set.indicator_of_notMem hw, zero_mul, mul_zero]
            exact mul_nonneg hK0 (mul_nonneg (heatKernel_pos h2t _).le
              (heatKernel_pos hτ _).le)
      _ = _ := by
          rw [integral_const_mul, AiryTwoInt.heatKernel_conv h2t hτ]

/-! ## The `V` bounds -/

/-- **Reverse `V`-difference bound**: `∫∫ V_R² ≤ C_D(w, t, τ, m₀) e^{−(b−a)²/(4t)}`. -/
theorem integral_sq_fddVKer_revKer_le {a b t τ w m₀ : ℝ} (ht : 0 < t) (hτ : 0 < τ)
    (hw : 0 < w) (ha : -m₀ ≤ a) (hba : b ≤ a) :
    Integrable (fun p => fddVKer (revKer a b t τ) w p ^ 2) (volume.prod volume) ∧
    ∫ p, fddVKer (revKer a b t τ) w p ^ 2 ∂(volume.prod volume) ≤
      defectConst w t τ m₀ * Real.exp (-(b - a) ^ 2 / (4 * t)) :=
  integral_sq_fddVKer_le_gaussDom ht hτ hw ha (measurable_revKer ht hτ)
    fun p => revKer_nonneg_le ht hτ hba p.1 p.2

/-- **The first-time-`⊤` `V` bound**: for `b ≥ −m₀`, `V_top` is `L²` with
`∫∫ V_top² ≤ C_D(w, t, τ, m₀) + C₁(w, t + τ, m₀)`. -/
theorem integral_sq_fddVKer_topKer_le {b t τ w m₀ : ℝ} (ht : 0 < t) (hτ : 0 < τ) (hw : 0 < w)
    (hb : -m₀ ≤ b) :
    Integrable (fun p => fddVKer (topKer b t τ) w p ^ 2) (volume.prod volume) ∧
    ∫ p, fddVKer (topKer b t τ) w p ^ 2 ∂(volume.prod volume) ≤
      defectConst w t τ m₀ + oneTimeConst w (t + τ) m₀ := by
  set R₁ : ℝ × ℝ → ℝ := fun p => if p.1 ≤ b then topKer b t τ p else 0 with hR₁
  set R₂ : ℝ × ℝ → ℝ := fun p => if p.1 ≤ b then 0 else topKer b t τ p with hR₂
  have hmb : MeasurableSet {p : ℝ × ℝ | p.1 ≤ b} := measurableSet_le measurable_fst
    measurable_const
  have hm₁ : Measurable R₁ := Measurable.ite hmb (measurable_topKer hτ) measurable_const
  have hm₂ : Measurable R₂ := Measurable.ite hmb measurable_const (measurable_topKer hτ)
  -- the Gaussian part (below `b`)
  have hG : ∀ p, 0 ≤ R₁ p ∧ R₁ p ≤ Real.sqrt 2 * Real.exp (-(b - b) ^ 2 / (8 * t))
      * Real.exp (-(b - p.1) ^ 2 / (8 * t)) * heatKernel (2 * t + τ) (p.1 - p.2) := by
    intro p
    obtain ⟨u, v⟩ := p
    by_cases hu : u ≤ b
    · simp only [hR₁, hu, ite_true]
      rw [topKer_eq_defectKer ht hτ hu]
      exact defectKer_nonneg_le ht hτ le_rfl u v
    · simp only [hR₁, hu, ite_false]
      exact ⟨le_rfl, mul_nonneg (by positivity) (heatKernel_pos (by positivity) _).le⟩
  obtain ⟨hi₁, hb₁⟩ := integral_sq_fddVKer_le_gaussDom (m₀ := m₀) ht hτ hw hb hm₁ hG
  rw [sub_self, show (-(0:ℝ) ^ 2 / (4 * t)) = 0 by ring, Real.exp_zero, mul_one] at hb₁
  -- the one-time part (above `b`)
  obtain ⟨hio, hbo⟩ := integral_sq_fddVKer_oneTime_le (a := b) (m₀ := m₀) (add_pos ht hτ) hw hb
  have hsq₂ : ∀ p, fddVKer R₂ w p ^ 2 ≤ fddVKer (hitKerN (b, t + τ) []) w p ^ 2 := by
    intro p
    obtain ⟨u, v⟩ := p
    have hle : R₂ (u, v) ^ 2 ≤ hitKerN (b, t + τ) [] (u, v) ^ 2 := by
      by_cases hu : u ≤ b
      · simp only [hR₂, hu, ite_true]
        rw [sq (0:ℝ), zero_mul]; exact sq_nonneg _
      · simp only [hR₂, hu, ite_false]
        obtain ⟨h0, h1⟩ := topKer_mem (b := b) ht hτ (u, v)
        refine pow_le_pow_left₀ h0 ?_ 2
        rw [hitKerN_nil, hitKer1_eq, Set.indicator_of_mem (show u ∈ Ioi b from not_le.1 hu),
          one_mul]
        exact h1
    rw [sq_fddVKer, sq_fddVKer]
    have := Real.exp_pos (-(2 * w) * u)
    have := Real.exp_pos (-(2 * w) * v)
    have hv : 0 ≤ 1 + v ^ 2 := by positivity
    gcongr
  have hmeas₂ : AEStronglyMeasurable (fun p => fddVKer R₂ w p ^ 2) (volume.prod volume) :=
    ((measurable_fddVKer hm₂ w).pow_const 2).aestronglyMeasurable
  have hi₂ : Integrable (fun p => fddVKer R₂ w p ^ 2) (volume.prod volume) :=
    hio.mono' hmeas₂ (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsq₂ p)
  have hb₂ : ∫ p, fddVKer R₂ w p ^ 2 ∂(volume.prod volume) ≤ oneTimeConst w (t + τ) m₀ :=
    (integral_mono hi₂ hio hsq₂).trans hbo
  -- split
  have hsplit : ∀ p, fddVKer (topKer b t τ) w p ^ 2 = fddVKer R₁ w p ^ 2 + fddVKer R₂ w p ^ 2 := by
    intro p
    by_cases hu : p.1 ≤ b
    · simp only [hR₁, hR₂, hu, ite_true, fddVKer, mul_zero, zero_mul]; ring
    · simp only [hR₁, hR₂, hu, ite_false, fddVKer, mul_zero, zero_mul]; ring
  have hint : Integrable (fun p => fddVKer (topKer b t τ) w p ^ 2) (volume.prod volume) :=
    (hi₁.add hi₂).congr (Eventually.of_forall fun p => (hsplit p).symm)
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae (Eventually.of_forall hsplit), integral_add hi₁ hi₂]
  exact add_le_add hb₁ hb₂

/-! ## Assembly -/

/-- **The reverse two-time determinant defect, weight-parametric** (`b ≤ a`, `b ≥ −m₀`): in the
frame `(a, t), (b, τ)` at weight `w > t + τ`, against the one-time determinant at `(b, τ)`, with
`N ≥ ‖W_{t+τ,w}‖₂`:
`|det(I − Q₂) − det(I − Q_b)| ≤ 2 √C_D N e^{−(b−a)²/8t} exp(2(√C_D N + 2 √(C_D + C₁) N))`. -/
theorem twoTime_det_defect_rev_le {a b t τ w m₀ N : ℝ} (ht : 0 < t) (hτ : 0 < τ)
    (hw : t + τ < w) (hwτ : τ < w) (hb : -m₀ ≤ b) (hba : b ≤ a)
    (hN : hsNorm (kernelOperator (memLp_wKernel_lt hw)) ≤ N) :
    |fredholmDet (fddOpLt (a, t) [(b, τ)] ht (pos_of_mem_single hτ) w hw) 1
      - fredholmDet (fddOpLt (b, τ) [] hτ pos_of_mem_nil w hwτ) 1|
      ≤ 2 * (Real.sqrt (defectConst w t τ m₀) * N) * Real.exp (-(b - a) ^ 2 / (8 * t))
        * Real.exp (2 * (Real.sqrt (defectConst w t τ m₀) * N
          + 2 * (Real.sqrt (defectConst w t τ m₀ + oneTimeConst w (t + τ) m₀) * N))) := by
  have hw0 : 0 < w := by linarith
  have ha : -m₀ ≤ a := hb.trans hba
  set W := kernelOperator (memLp_wKernel_lt hw) with hWdef
  have hV2 := memLp_fddVKer (a, t) [(b, τ)] ht (pos_of_mem_single hτ) hw0
  obtain ⟨hiT, hbT⟩ := integral_sq_fddVKer_topKer_le (b := b) (m₀ := m₀) ht hτ hw0 hb
  have hVT : MemLp (fddVKer (topKer b t τ) w) 2 (volume.prod volume) :=
    memLp_of_sq_le (measurable_fddVKer (measurable_topKer hτ) w) hiT fun _ => le_rfl
  -- the `⊤` determinant is the one-time determinant at `(b, τ)`
  have hW' : MemLp (AiryConj.wKernel (t + τ - t) w) 2 (volume.prod volume) :=
    memLp_wKernel_lt (by linarith)
  have hVb := memLp_fddVKer (b, τ) [] hτ pos_of_mem_nil hw0
  have hswap := fredholmDet_swap_heat (S := t + τ) (g := t) (T := τ) (a := w) ht hτ
    (by linarith) (measurable_hitKerN (e := (b, τ)) hτ pos_of_mem_nil)
    (abs_hitKerN_le (e := (b, τ)) hτ pos_of_mem_nil) hVT (memLp_wKernel_lt hw) hVb hW' 1
  have hWb : kernelOperator hW' = kernelOperator (memLp_wKernel_lt (T := τ) hwτ) :=
    AiryTwoInt.kernelOperator_congr (by rw [show t + τ - t = τ by ring]) _ _
  have hQb : fddOpLt (b, τ) [] hτ pos_of_mem_nil w hwτ
      = kernelOperator hVb ∘L kernelOperator (memLp_wKernel_lt (T := τ) hwτ) := rfl
  have hQ2 : fddOpLt (a, t) [(b, τ)] ht (pos_of_mem_single hτ) w hw = kernelOperator hV2 ∘L W :=
    rfl
  rw [hQ2, hQb, ← hWb, ← hswap]
  have hHW : IsHilbertSchmidt W := isHilbertSchmidt_kernelOperator _
  have hN0 : 0 ≤ N := (hsNorm_nonneg _).trans hN
  have hpt : ∀ p, (fddVKer (hitKerN (a, t) [(b, τ)]) w - fddVKer (topKer b t τ) w) p
      = fddVKer (revKer a b t τ) w p := fun p => by
    simp only [Pi.sub_apply, fddVKer, revKer]; ring
  have hdiff : kernelOperator hV2 ∘L W - kernelOperator hVT ∘L W
      = kernelOperator (hV2.sub hVT) ∘L W := by
    rw [AiryTwoInt.kernelOperator_sub hV2 hVT, ContinuousLinearMap.sub_comp]
  obtain ⟨hiD, hbD⟩ := integral_sq_fddVKer_revKer_le (m₀ := m₀) ht hτ hw0 ha hba
  have hiD' : Integrable (fun p => (fddVKer (hitKerN (a, t) [(b, τ)]) w
      - fddVKer (topKer b t τ) w) p ^ 2) (volume.prod volume) :=
    hiD.congr (Eventually.of_forall fun p => by simp only [hpt])
  have hEsq : Real.exp (-(b - a) ^ 2 / (8 * t))
      = Real.sqrt (Real.exp (-(b - a) ^ 2 / (4 * t))) := by
    rw [← Real.sqrt_sq (Real.exp_pos (-(b - a) ^ 2 / (8 * t))).le, sq, ← Real.exp_add]
    congr 2
    field_simp
    ring
  have hsD : hsNorm (kernelOperator (hV2.sub hVT))
      ≤ Real.sqrt (defectConst w t τ m₀) * Real.exp (-(b - a) ^ 2 / (8 * t)) := by
    refine (AiryConj.hsNorm_kernelOperator_le_sqrt (hV2.sub hVT) hiD').trans ?_
    have heq : ∫ p, (fddVKer (hitKerN (a, t) [(b, τ)]) w
        - fddVKer (topKer b t τ) w) p ^ 2 ∂(volume.prod volume)
        = ∫ p, fddVKer (revKer a b t τ) w p ^ 2 ∂(volume.prod volume) :=
      integral_congr_ae (Eventually.of_forall fun p => by simp only [hpt])
    rw [heq, hEsq, ← Real.sqrt_mul (defectConst_nonneg ht hτ)]
    exact Real.sqrt_le_sqrt hbD
  have hsT : hsNorm (kernelOperator hVT)
      ≤ Real.sqrt (defectConst w t τ m₀ + oneTimeConst w (t + τ) m₀) :=
    (AiryConj.hsNorm_kernelOperator_le_sqrt hVT hiT).trans (Real.sqrt_le_sqrt hbT)
  have f2 : traceENorm (kernelOperator hV2 ∘L W) ≠ ⊤ :=
    IsTraceClass.traceENorm_ne_top ⟨_, _, isHilbertSchmidt_kernelOperator _, hHW, rfl⟩
  have f1 : traceENorm (kernelOperator hVT ∘L W) ≠ ⊤ :=
    IsTraceClass.traceENorm_ne_top ⟨_, _, isHilbertSchmidt_kernelOperator _, hHW, rfl⟩
  have fD := traceENorm_sub_ne_top f2 f1
  set E := Real.exp (-(b - a) ^ 2 / (8 * t)) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.2 (sq_nonneg _)) (by positivity))
  set cD := Real.sqrt (defectConst w t τ m₀)
  set cT := Real.sqrt (defectConst w t τ m₀ + oneTimeConst w (t + τ) m₀)
  have hcD : 0 ≤ cD := Real.sqrt_nonneg _
  have hcT : 0 ≤ cT := Real.sqrt_nonneg _
  have tD : traceNorm (kernelOperator hV2 ∘L W - kernelOperator hVT ∘L W) ≤ cD * E * N := by
    rw [hdiff]
    exact (traceNorm_comp_le (isHilbertSchmidt_kernelOperator _) hHW).trans
      (mul_le_mul hsD hN (hsNorm_nonneg _) (by positivity))
  have t1 : traceNorm (kernelOperator hVT ∘L W) ≤ cT * N :=
    (traceNorm_comp_le (isHilbertSchmidt_kernelOperator _) hHW).trans
      (mul_le_mul hsT hN (hsNorm_nonneg _) hcT)
  have t2 : traceNorm (kernelOperator hV2 ∘L W) ≤ traceNorm (kernelOperator hV2 ∘L W
      - kernelOperator hVT ∘L W) + traceNorm (kernelOperator hVT ∘L W) := by
    have h := traceNorm_add_le fD f1
    rwa [sub_add_cancel] at h
  have hS := norm_fredholmDet_sub_le f2 f1 (1 : ℝ)
  rw [Real.norm_eq_abs, norm_one, mul_one] at hS
  refine hS.trans ?_
  have hDn := traceNorm_nonneg (kernelOperator hV2 ∘L W - kernelOperator hVT ∘L W)
  have hEN : cD * E * N ≤ cD * N := by
    have := mul_le_mul_of_nonneg_left hE1 hcD
    nlinarith
  calc 2 * traceNorm (kernelOperator hV2 ∘L W - kernelOperator hVT ∘L W)
        * Real.exp (2 * (traceNorm (kernelOperator hV2 ∘L W) + traceNorm (kernelOperator hVT ∘L W)))
      ≤ 2 * (cD * E * N) * Real.exp (2 * (cD * N + 2 * (cT * N))) := by
        apply mul_le_mul (by linarith) (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
        positivity
    _ = _ := by ring

/-! ## The Finset (CDF) form -/

/-- **The reverse two-time CDF defect, weight-parametric** (`b ≤ a`, `b ≥ −m₀`): with
`G(b) = F_{{x+t}}(b)`, for any padding `τ > 0`, weight `w > t + τ`, `N ≥ ‖W_{t+τ,w}‖₂`,
`|G(b) − F_{{x,x+t}}(a, b)| ≤ 2 √C_D N exp(2(√C_D N + 2√(C_D + C₁) N)) · e^{−(a−b)²/8t}`. -/
theorem airy1FinCdf_twoTime_defect_rev_le {x t τ w m₀ N a b : ℝ} (ht : 0 < t) (hτ : 0 < τ)
    (hw : t + τ < w) (hN : hsNorm (kernelOperator (memLp_wKernel_lt hw)) ≤ N)
    (hb : -m₀ ≤ b) (hba : b ≤ a) (y : ({x, x + t} : Finset ℝ) → ℝ)
    (hya : ∀ h, y ⟨x, h⟩ = a) (hyb : ∀ h, y ⟨x + t, h⟩ = b) :
    |airy1FinCdf {x + t} (fun _ => b) - airy1FinCdf {x, x + t} y|
      ≤ 2 * (Real.sqrt (defectConst w t τ m₀) * N) * Real.exp (-(a - b) ^ 2 / (8 * t))
        * Real.exp (2 * (Real.sqrt (defectConst w t τ m₀) * N
          + 2 * (Real.sqrt (defectConst w t τ m₀ + oneTimeConst w (t + τ) m₀) * N))) := by
  have hwτ : τ < w := by linarith
  have hsp2 : SamePad (a, t) [(b, 1)] (a, t) [(b, τ)] := ⟨rfl, rfl⟩
  have hsp1 : SamePad (b, 1) [] (b, τ) [] := rfl
  rw [airy1FinCdf_eq_fredholmDet_fddOpLt {x, x + t} y (finEntries_pair ht y hya hyb) hsp2 ht
      (pos_of_mem_single hτ) (a := w) hw,
    airy1FinCdf_eq_fredholmDet_fddOpLt {x + t} _ (finEntries_singleton (x + t) b) hsp1 hτ
      pos_of_mem_nil (a := w) hwτ, abs_sub_comm, show (a - b) ^ 2 = (b - a) ^ 2 by ring]
  exact twoTime_det_defect_rev_le ht hτ hw hwτ hb hba hN

/-- **Two-time defect bound, reverse order (fixed lower level)**: for every `m₀` there is `C` such
that
for all `x`, `0 < t ≤ 1` and levels `−m₀ ≤ b ≤ a`,
`|G(b) − F(a, b)| ≤ C e^{−(a−b)²/(8t)}`, where `G(b) = F_{{x+t}}(b)` and
`F(a, b) = F_{{x,x+t}}(a, b)`; `G(b) − F(a, b)` is the reverse defect
`P(A(x) > a, A(x+t) ≤ b)`. -/
theorem airy1FinCdf_twoTime_defect_rev (m₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x t a b : ℝ) (y : ({x, x + t} : Finset ℝ) → ℝ), 0 < t → t ≤ 1 →
      -m₀ ≤ b → b ≤ a → (∀ h, y ⟨x, h⟩ = a) → (∀ h, y ⟨x + t, h⟩ = b) →
      |airy1FinCdf {x + t} (fun _ => b) - airy1FinCdf {x, x + t} y|
        ≤ C * Real.exp (-(a - b) ^ 2 / (8 * t)) := by
  have hc01 := c0_pos (S := 1) one_pos
  obtain ⟨CW, hCW, hWb⟩ := hsNorm_wKernel_three_le
  have hCD0 := defectConstMax_pos m₀
  have hO0 : 0 ≤ oneTimeConstMax m₀ := by unfold oneTimeConstMax; positivity
  refine ⟨2 * (Real.sqrt (defectConstMax m₀) * CW) * Real.exp (2 * (Real.sqrt (defectConstMax m₀)
    * CW + 2 * (Real.sqrt (defectConstMax m₀ + oneTimeConstMax m₀) * CW))), by positivity, ?_⟩
  intro x t a b y ht ht1 hb hba hya hyb
  have hw : t + 1 < 3 := by linarith
  refine (airy1FinCdf_twoTime_defect_rev_le ht one_pos hw (hWb t ht ht1 hw) hb hba y hya
    hyb).trans ?_
  have hDle := defectConst_three_le ht ht1 m₀
  have h1le := oneTimeConst_three_le ht ht1 m₀
  have hE := (Real.exp_pos (-(a - b) ^ 2 / (8 * t))).le
  calc 2 * (Real.sqrt (defectConst 3 t 1 m₀) * CW) * Real.exp (-(a - b) ^ 2 / (8 * t))
        * Real.exp (2 * (Real.sqrt (defectConst 3 t 1 m₀) * CW
          + 2 * (Real.sqrt (defectConst 3 t 1 m₀ + oneTimeConst 3 (t + 1) m₀) * CW)))
      ≤ 2 * (Real.sqrt (defectConstMax m₀) * CW) * Real.exp (-(a - b) ^ 2 / (8 * t))
        * Real.exp (2 * (Real.sqrt (defectConstMax m₀) * CW
          + 2 * (Real.sqrt (defectConstMax m₀ + oneTimeConstMax m₀) * CW))) := by
        gcongr
    _ = _ := by ring

end AiryFdd
