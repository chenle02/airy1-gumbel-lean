/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Fdd.FddOp
import Airy1GumbelContrib.TwoInterval.TwoIntervalN2
import Airy1GumbelContrib.FredholmDet.TracePowDet

/-!
# Padding and weight independence of the `n`-time fdd determinant

* **Composition with the Airy kernel.** `compKernel_lamKerN_bAiry`: `Λ e^{τΔ} ⋆ g_S = Λ ⋆ g_{S−τ}`
  for every `S ≥ 0`, where `lamAiry e L G` is the kernel of `P̄_{x₁} e^{g₁Δ} ⋯ P̄_{x_n} g_G` (the last gap
  `τ` is *not* used).  Hence (`compKernel_hitKerN_bAiry`)
  `(H ⋆ g_S)(u, y) = Ai(u + y) − lamAiry e L (S − τ) (u, y) =: fddAiryKer e L (u, y)`, and
  `V ⋆ W = e^{−au} fddAiryKer(u, y) e^{ay}` (QR's `U J U⁻¹` kernel).
* **Padding.** `SamePad e L e' L'`: same levels and interior gaps, arbitrary last gaps.  Then
  `fddAiryKer e L = fddAiryKer e' L'`, so at any common admissible weight the operators are
  equal (`fddOpAt_of_samePad`); no determinant theory is needed.
* **Weight independence.** `fddOpAt e L … a ha` is `T_V ∘ T_W` at any weight `a ≥ S + 1` (`fddOp` is
  the case `a = 2S`).  Every power is the kernel operator of the conjugated iterated kernel, so
  `tr(J̃_a^m)` is weight-free (`trace_pow_fddOpAt_indep`), and
  `fredholmDet_eq_of_trace_pow_eq` (`FredholmDet/`) gives `fredholmDet_fddOpAt_indep`.
* A padding change changes `S` and so the canonical weight `2S`; padding and weight independence
  together give `fredholmDet_fddOp_of_samePad`, and for the user-facing CDF
  `airy1FinCdf_eq_fredholmDet_fddOpAt` (any admissible padding and weight).
-/

namespace AiryFdd

open MeasureTheory Real Set Filter
open HilbertSchmidt

/-! ## L3: the τ-free composite kernel -/

/-- The kernel of `P̄_{x₁} e^{g₁Δ} P̄_{x₂} ⋯ e^{g_{n−1}Δ} P̄_{x_n} g_G` (`g_G = P_{−G}B₀`);
the last gap (the padding) is not used. -/
noncomputable def lamAiry : ℝ × ℝ → List (ℝ × ℝ) → ℝ → ℝ × ℝ → ℝ
  | e, [], G => fun p => (Iic e.1).indicator (fun _ => (1 : ℝ)) p.1 * backwardAiry G (p.1 + p.2)
  | e, y :: L, G => fun p => (Iic e.1).indicator (fun _ => (1 : ℝ)) p.1
      * AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (lamAiry y L G) p

/-- Slice integrability of a heat-dominated kernel against `g_S`. -/
theorem integrable_mul_bAiry {t S : ℝ} (ht : 0 < t) (hS : 0 ≤ S) {K : ℝ × ℝ → ℝ}
    (hK : Measurable K) (hb : ∀ p, |K p| ≤ heatKernel t (p.1 - p.2)) (u y : ℝ) :
    Integrable fun z : ℝ => K (u, z) * backwardAiry S (z + y) := by
  obtain ⟨C, hC⟩ := AiryTwoInt.bAiryKer_abs_le_exp hS y
  refine ((AiryTwoInt.integrable_heatKernel_mul_exp_abs ht S u).const_mul C).mono' ?_ ?_
  · exact ((hK.comp (measurable_const.prodMk measurable_id)).mul
      ((continuous_backwardAiry_s S).comp
        (continuous_id.add continuous_const)).measurable).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |K (u, z)| ≤ heatKernel t (u - z) := hb (u, z)
    have h2 : |backwardAiry S (z + y)| ≤ C * Real.exp (S * |z|) := hC z
    calc |K (u, z)| * |backwardAiry S (z + y)|
        ≤ heatKernel t (u - z) * (C * Real.exp (S * |z|)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (heatKernel_pos ht _).le
      _ = C * (heatKernel t (u - z) * Real.exp (S * |z|)) := by ring

/-- **`Λ e^{τΔ} ⋆ g_S = Λ ⋆ g_{S−τ}`** (input for padding independence, `heatAiryConv_any` at the
last level, Fubini at the others): the composite of `lamKerN` with `g_S` is `lamAiry` at `S − τ`. -/
theorem compKernel_lamKerN_bAiry : ∀ (L : List (ℝ × ℝ)) (e : ℝ × ℝ), 0 < e.2 →
    (∀ y ∈ L, 0 < y.2) → ∀ {S : ℝ}, 0 ≤ S →
    AiryConj.compKernel (lamKerN e L) (AiryConj.backwardAiryPair S)
      = lamAiry e L (S - lastGap e L)
  | [], e, he, _, S, _ => by
    funext p
    obtain ⟨u, y⟩ := p
    have h := congrFun (AiryTwoInt.heatKerTwo_comp_bAiryKer_any he S) (u, y)
    show ∫ z : ℝ, lamKer1 e.1 e.2 (u, z) * backwardAiry S (z + y)
      = (Iic e.1).indicator (fun _ => (1 : ℝ)) u * backwardAiry (S - e.2) (u + y)
    have hfun : (fun z : ℝ => lamKer1 e.1 e.2 (u, z) * backwardAiry S (z + y))
        = fun z => (Iic e.1).indicator (fun _ => (1 : ℝ)) u
          * (heatKernel e.2 (u - z) * backwardAiry S (z + y)) := by
      funext z
      simp only [lamKer1]
      ring
    rw [hfun, integral_const_mul]
    congr 1
  | y :: L, e, he, hL, S, hS => by
    have hy : 0 < y.2 := hL y List.mem_cons_self
    have hL' : ∀ z ∈ L, 0 < z.2 := fun z hz => hL z (List.mem_cons_of_mem _ hz)
    obtain ⟨hm, h0, h1⟩ := lamKerN_props L y hy hL'
    have hS' := gapSum_pos L y hy hL'
    have ih := compKernel_lamKerN_bAiry L y hy hL' hS
    funext p
    obtain ⟨u, v⟩ := p
    show ∫ z : ℝ, ((Iic e.1).indicator (fun _ => (1 : ℝ)) u
        * AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (lamKerN y L) (u, z))
          * AiryConj.backwardAiryPair S (z, v)
      = (Iic e.1).indicator (fun _ => (1 : ℝ)) u
        * AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (lamAiry y L (S - lastGap y L)) (u, v)
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    congr 1
    obtain ⟨C, hC⟩ := AiryTwoInt.bAiryKer_abs_le_exp hS v
    have hInt := AiryTwoInt.integrable_uncurry_of_abs_le he hS' hS u
      (AiryTwoInt.measurable_heatKerTwo e.2)
      (fun z => AiryTwoInt.heatKerTwo_abs_le_self he (u, z)) hm
      (fun z₁ z₂ => by rw [abs_of_nonneg (h0 _)]; exact h1 (z₁, z₂))
      (φ := fun z => AiryConj.backwardAiryPair S (z, v))
      ((AiryConj.measurable_backwardAiryPair S).comp (measurable_id.prodMk measurable_const))
      C hC
    have hassoc := AiryTwoInt.compKernel_assoc (A := AiryTwoInt.heatKerTwo e.2)
      (B := lamKerN y L) (C := AiryConj.backwardAiryPair S) u v hInt
    rw [← ih]
    exact hassoc

/-- The τ-free composite kernel `Ai(u + y) − (Λ ⋆ g_{S−τ})(u, y)` (QR Thm 1's kernel before
the `U`-conjugation). -/
noncomputable def fddAiryKer (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (p : ℝ × ℝ) : ℝ :=
  airyAiReal (p.1 + p.2) - lamAiry e L (gapSum e L - lastGap e L) p

/-- **L3 (second half)**: `(H ⋆ g_S)(u, y) = Ai(u + y) − (Λ e^{τΔ} ⋆ g_S)(u, y)
= Ai(u + y) − (Λ ⋆ g_{S−τ})(u, y)` with `S = Σ gaps`. -/
theorem compKernel_hitKerN_bAiry (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) :
    AiryConj.compKernel (hitKerN e L) (AiryConj.backwardAiryPair (gapSum e L))
      = fddAiryKer e L := by
  have hS := gapSum_pos L e he hL
  obtain ⟨hm, h0, h1⟩ := lamKerN_props L e he hL
  have hlam := compKernel_lamKerN_bAiry L e he hL hS.le
  funext p
  obtain ⟨u, y⟩ := p
  have hheat := congrFun (AiryTwoInt.heatKerTwo_comp_bAiryKer_any hS (gapSum e L)) (u, y)
  rw [sub_self] at hheat
  have hI1 : Integrable fun z : ℝ =>
      heatKernel (gapSum e L) (u - z) * backwardAiry (gapSum e L) (z + y) :=
    integrable_mul_bAiry hS hS.le (AiryTwoInt.measurable_heatKerTwo _)
      (fun p => AiryTwoInt.heatKerTwo_abs_le_self hS p) u y
  have hI2 : Integrable fun z : ℝ => lamKerN e L (u, z) * backwardAiry (gapSum e L) (z + y) :=
    integrable_mul_bAiry hS hS.le hm (fun p => by rw [abs_of_nonneg (h0 p)]; exact h1 p) u y
  show ∫ z : ℝ, hitKerN e L (u, z) * backwardAiry (gapSum e L) (z + y)
    = airyAiReal (u + y) - lamAiry e L (gapSum e L - lastGap e L) (u, y)
  have e1 : (∫ z : ℝ, hitKerN e L (u, z) * backwardAiry (gapSum e L) (z + y))
      = (∫ z : ℝ, heatKernel (gapSum e L) (u - z) * backwardAiry (gapSum e L) (z + y))
        - ∫ z : ℝ, lamKerN e L (u, z) * backwardAiry (gapSum e L) (z + y) := by
    rw [← integral_sub hI1 hI2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hitKerN]
    ring
  rw [e1]
  congr 1
  · rw [← backwardAiry_zero]
    exact hheat
  · exact congrFun hlam (u, y)

/-- **L3 (full)**: the `V W` composite is the `e^{∓a}`-conjugate of the τ-free kernel. -/
theorem compKernel_fddVKer_wKernel_eq (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) (a : ℝ) :
    AiryConj.compKernel (fddVKer (hitKerN e L) a) (AiryConj.wKernel (gapSum e L) a)
      = AiryConj.expConjKernel a (fddAiryKer e L) := by
  rw [compKernel_fddVKer_wKernel, compKernel_hitKerN_bAiry e L he hL]

/-! ## L4: paddings -/

/-- Two entry lists with the same levels and the same interior gaps (last gaps arbitrary). -/
def SamePad : ℝ × ℝ → List (ℝ × ℝ) → ℝ × ℝ → List (ℝ × ℝ) → Prop
  | e, [], e', [] => e.1 = e'.1
  | e, y :: L, e', y' :: L' => e = e' ∧ SamePad y L y' L'
  | _, [], _, _ :: _ => False
  | _, _ :: _, _, [] => False

theorem samePad_refl : ∀ (L : List (ℝ × ℝ)) (e : ℝ × ℝ), SamePad e L e L
  | [], _ => by simp only [SamePad]
  | y :: L, e => by simp only [SamePad, true_and]; exact samePad_refl L y

theorem lamAiry_of_samePad : ∀ (L : List (ℝ × ℝ)) (e e' : ℝ × ℝ) (L' : List (ℝ × ℝ)),
    SamePad e L e' L' → ∀ G : ℝ, lamAiry e L G = lamAiry e' L' G
  | [], e, e', [], h, G => by
    simp only [SamePad] at h
    funext p
    simp only [lamAiry, h]
  | y :: L, e, e', y' :: L', h, G => by
    simp only [SamePad] at h
    obtain ⟨rfl, h⟩ := h
    funext p
    simp only [lamAiry, lamAiry_of_samePad L y y' L' h G]
  | [], _, _, _ :: _, h, _ => by simp only [SamePad] at h
  | _ :: _, _, _, [], h, _ => by simp only [SamePad] at h

theorem interior_of_samePad : ∀ (L : List (ℝ × ℝ)) (e e' : ℝ × ℝ) (L' : List (ℝ × ℝ)),
    SamePad e L e' L' → gapSum e L - lastGap e L = gapSum e' L' - lastGap e' L'
  | [], e, e', [], _ => by simp only [gapSum, lastGap, sub_self]
  | y :: L, e, e', y' :: L', h => by
    simp only [SamePad] at h
    obtain ⟨rfl, h⟩ := h
    have := interior_of_samePad L y y' L' h
    simp only [gapSum, lastGap]
    linarith
  | [], _, _, _ :: _, h => by simp only [SamePad] at h
  | _ :: _, _, _, [], h => by simp only [SamePad] at h

/-- **L4 (kernel form)**: the τ-free kernel depends only on the levels and interior gaps. -/
theorem fddAiryKer_of_samePad {e e' : ℝ × ℝ} {L L' : List (ℝ × ℝ)} (h : SamePad e L e' L') :
    fddAiryKer e L = fddAiryKer e' L' := by
  funext p
  simp only [fddAiryKer, interior_of_samePad L e e' L' h,
    lamAiry_of_samePad L e e' L' h]

/-! ## The fdd operator at a general admissible weight -/

theorem weight_pos {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2) (hL : ∀ y ∈ L, 0 < y.2)
    {a : ℝ} (ha : gapSum e L + 1 ≤ a) : 0 < a := by
  have := gapSum_pos L e he hL
  linarith

/-- The fdd operator `T_V ∘ T_W` at an arbitrary admissible weight `a ≥ S + 1`. -/
noncomputable def fddOpAt (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) (a : ℝ) (ha : gapSum e L + 1 ≤ a) :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  kernelOperator (memLp_fddVKer e L he hL (weight_pos he hL ha)) ∘L
    kernelOperator (AiryTwoInt.memLp_wKernel_any ha)

/-- `fddOp` is `fddOpAt` at the canonical weight `a = 2S`. -/
theorem fddOp_eq_fddOpAt (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) (h1 : 1 ≤ gapSum e L) :
    fddOp e L he hL h1 = fddOpAt e L he hL (2 * gapSum e L) (by linarith) := rfl

theorem isTraceClass_fddOpAt (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) {a : ℝ} (ha : gapSum e L + 1 ≤ a) :
    IsTraceClass (fddOpAt e L he hL a ha) :=
  ⟨_, _, isHilbertSchmidt_kernelOperator _, isHilbertSchmidt_kernelOperator _, rfl⟩

theorem memLp_expConj_fddAiryKer (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) {a : ℝ} (ha : gapSum e L + 1 ≤ a) :
    MemLp (AiryConj.expConjKernel a (fddAiryKer e L)) 2 (volume.prod volume) := by
  rw [← compKernel_fddVKer_wKernel_eq e L he hL a]
  exact AiryTwoInt.memLp_compKernel (measurable_fddVKer (measurable_hitKerN he hL) a)
    (AiryConj.continuous_wKernel _ a).measurable (memLp_fddVKer e L he hL (weight_pos he hL ha))
    (AiryTwoInt.memLp_wKernel_any ha)

/-- `fddOpAt` is the kernel operator of `e^{−au} fddAiryKer(u, y) e^{ay}`. -/
theorem fddOpAt_eq_kernelOperator (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) {a : ℝ} (ha : gapSum e L + 1 ≤ a) :
    fddOpAt e L he hL a ha = kernelOperator (memLp_expConj_fddAiryKer e L he hL ha) := by
  have hcomp : MemLp (AiryConj.compKernel (fddVKer (hitKerN e L) a)
      (AiryConj.wKernel (gapSum e L) a)) 2 (volume.prod volume) :=
    AiryTwoInt.memLp_compKernel (measurable_fddVKer (measurable_hitKerN he hL) a)
      (AiryConj.continuous_wKernel _ a).measurable (memLp_fddVKer e L he hL (weight_pos he hL ha))
      (AiryTwoInt.memLp_wKernel_any ha)
  unfold fddOpAt
  rw [← AiryTwoInt.kernelOperator_compKernel _ _ hcomp]
  exact AiryTwoInt.kernelOperator_congr (compKernel_fddVKer_wKernel_eq e L he hL a) hcomp _

/-- **L4 (operator form)**: two paddings of the same levels and interior gaps give the same
operator at any common admissible weight. -/
theorem fddOpAt_of_samePad {e e' : ℝ × ℝ} {L L' : List (ℝ × ℝ)} (h : SamePad e L e' L')
    (he : 0 < e.2) (hL : ∀ y ∈ L, 0 < y.2) (he' : 0 < e'.2) (hL' : ∀ y ∈ L', 0 < y.2)
    {a : ℝ} (ha : gapSum e L + 1 ≤ a) (ha' : gapSum e' L' + 1 ≤ a) :
    fddOpAt e L he hL a ha = fddOpAt e' L' he' hL' a ha' := by
  rw [fddOpAt_eq_kernelOperator, fddOpAt_eq_kernelOperator]
  exact AiryTwoInt.kernelOperator_congr (by rw [fddAiryKer_of_samePad h]) _ _

/-! ## L5: weight independence -/

/-- The unweighted iterated kernels: `fddAiryIter e L m` is the `(m+1)`-fold composite of
`fddAiryKer e L`. -/
noncomputable def fddAiryIter (e : ℝ × ℝ) (L : List (ℝ × ℝ)) : ℕ → ℝ × ℝ → ℝ
  | 0 => fddAiryKer e L
  | m + 1 => AiryConj.compKernel (fddAiryIter e L m) (fddAiryKer e L)

theorem measurable_fddAiryKer {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) : Measurable (fddAiryKer e L) := by
  rw [← compKernel_hitKerN_bAiry e L he hL]
  exact AiryTwoInt.measurable_compKernel (measurable_hitKerN he hL)
    (AiryConj.measurable_backwardAiryPair _)

theorem measurable_fddAiryIter {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) (m : ℕ) : Measurable (fddAiryIter e L m) := by
  induction m with
  | zero => exact measurable_fddAiryKer he hL
  | succ m ih => exact AiryTwoInt.measurable_compKernel ih (measurable_fddAiryKer he hL)

theorem memLp_expConj_fddAiryIter {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) {a : ℝ} (ha : gapSum e L + 1 ≤ a) (m : ℕ) :
    MemLp (AiryConj.expConjKernel a (fddAiryIter e L m)) 2 (volume.prod volume) := by
  induction m with
  | zero => exact memLp_expConj_fddAiryKer e L he hL ha
  | succ m ih =>
    show MemLp (AiryConj.expConjKernel a
      (AiryConj.compKernel (fddAiryIter e L m) (fddAiryKer e L))) 2 (volume.prod volume)
    rw [← AiryConj.compKernel_expConjKernel]
    exact AiryTwoInt.memLp_compKernel
      (AiryConj.measurable_expConjKernel a (measurable_fddAiryIter he hL m))
      (AiryConj.measurable_expConjKernel a (measurable_fddAiryKer he hL)) ih
      (memLp_expConj_fddAiryKer e L he hL ha)

/-- The kernel of `J̃_a^(m+1)` is the conjugate of the weight-free iterated kernel. -/
theorem fddOpAt_pow_eq {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) {a : ℝ} (ha : gapSum e L + 1 ≤ a) (m : ℕ) :
    (fddOpAt e L he hL a ha) ^ (m + 1)
      = kernelOperator (memLp_expConj_fddAiryIter he hL ha m) := by
  induction m with
  | zero =>
    rw [zero_add, pow_one, fddOpAt_eq_kernelOperator]
    exact AiryTwoInt.kernelOperator_congr rfl _ _
  | succ m ih =>
    have hcomp : MemLp (AiryConj.compKernel (AiryConj.expConjKernel a (fddAiryIter e L m))
        (AiryConj.expConjKernel a (fddAiryKer e L))) 2 (volume.prod volume) := by
      rw [AiryConj.compKernel_expConjKernel]
      exact memLp_expConj_fddAiryIter he hL ha (m + 1)
    rw [pow_succ, ih, ContinuousLinearMap.mul_def, fddOpAt_eq_kernelOperator,
      ← AiryTwoInt.kernelOperator_compKernel (memLp_expConj_fddAiryIter he hL ha m)
        (memLp_expConj_fddAiryKer e L he hL ha) hcomp]
    exact AiryTwoInt.kernelOperator_congr (AiryConj.compKernel_expConjKernel a _ _) hcomp _

/-- The trace integrand of `V W` is weight-free, pointwise. -/
theorem fddVKer_mul_wKernel_swap (H : ℝ × ℝ → ℝ) (S a x z : ℝ) :
    fddVKer H a (x, z) * AiryConj.wKernel S a (z, x) = H (x, z) * backwardAiry S (z + x) := by
  have hφ : AiryConj.phiWeight z ≠ 0 := (AiryConj.phiWeight_pos z).ne'
  have e1 : Real.exp (-a * x) * Real.exp (a * x) = 1 := by
    rw [← Real.exp_add, show -a * x + a * x = 0 by ring, Real.exp_zero]
  have e2 : Real.exp (-a * z) * Real.exp (a * z) = 1 := by
    rw [← Real.exp_add, show -a * z + a * z = 0 by ring, Real.exp_zero]
  simp only [fddVKer, AiryConj.wKernel]
  calc Real.exp (-a * x) * H (x, z) * Real.exp (-a * z) * AiryConj.phiWeight z
        * ((AiryConj.phiWeight z)⁻¹ * Real.exp (a * z) * backwardAiry S (z + x)
          * Real.exp (a * x))
      = H (x, z) * backwardAiry S (z + x) * (Real.exp (-a * x) * Real.exp (a * x))
          * (Real.exp (-a * z) * Real.exp (a * z))
          * (AiryConj.phiWeight z * (AiryConj.phiWeight z)⁻¹) := by ring
    _ = H (x, z) * backwardAiry S (z + x) := by
        rw [e1, e2, mul_inv_cancel₀ hφ, mul_one, mul_one, mul_one]

/-- `tr J̃_a = ∫∫ H(x, z) g_S(z + x)`, weight-free. -/
theorem trace_fddOpAt {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) {a : ℝ} (ha : gapSum e L + 1 ≤ a) :
    trace (fddOpAt e L he hL a ha)
      = ∫ x : ℝ, ∫ z : ℝ, hitKerN e L (x, z) * backwardAiry (gapSum e L) (z + x) := by
  unfold fddOpAt
  rw [AiryConj.trace_kernelOperator_comp]
  apply integral_congr_ae
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards with z
  exact fddVKer_mul_wKernel_swap _ _ _ x z

/-- `tr J̃_a^(m+2) = ∫∫ K_{m+1}(x, z) K_1(z, x)`, weight-free. -/
theorem trace_pow_add_two_fddOpAt {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) {a : ℝ} (ha : gapSum e L + 1 ≤ a) (m : ℕ) :
    trace ((fddOpAt e L he hL a ha) ^ (m + 1 + 1))
      = ∫ x : ℝ, ∫ z : ℝ, fddAiryIter e L m (x, z) * fddAiryKer e L (z, x) := by
  rw [pow_succ, fddOpAt_pow_eq he hL ha m, ContinuousLinearMap.mul_def,
    fddOpAt_eq_kernelOperator, AiryConj.trace_kernelOperator_comp]
  apply integral_congr_ae
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards with z
  exact AiryConj.expConjKernel_mul_swap a _ _ x z

/-- **L5 (traces)**: `tr(J̃_a^m) = tr(J̃_b^m)` for all admissible `a, b` and `m ≥ 1`. -/
theorem trace_pow_fddOpAt_indep {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) {a b : ℝ} (ha : gapSum e L + 1 ≤ a) (hb : gapSum e L + 1 ≤ b)
    {m : ℕ} (hm : 1 ≤ m) :
    trace ((fddOpAt e L he hL a ha) ^ m) = trace ((fddOpAt e L he hL b hb) ^ m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  cases k with
  | zero => rw [zero_add, pow_one, pow_one, trace_fddOpAt, trace_fddOpAt]
  | succ k => rw [trace_pow_add_two_fddOpAt, trace_pow_add_two_fddOpAt]

/-- **L5**: the entire Fredholm determinant of the fdd operator does not depend on the
admissible weight. -/
theorem fredholmDet_fddOpAt_indep {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) {a b : ℝ} (ha : gapSum e L + 1 ≤ a) (hb : gapSum e L + 1 ≤ b)
    (z : ℝ) :
    fredholmDet (fddOpAt e L he hL a ha) z = fredholmDet (fddOpAt e L he hL b hb) z :=
  fredholmDet_eq_of_trace_pow_eq (isTraceClass_fddOpAt e L he hL ha)
    (isTraceClass_fddOpAt e L he hL hb) (fun _ hm => trace_pow_fddOpAt_indep he hL ha hb hm) z

/-! ## L4 + L5 together, and the user-facing CDF -/

/-- **L4 + L5**: same levels and interior gaps, any paddings, any admissible weights. -/
theorem fredholmDet_fddOpAt_of_samePad {e e' : ℝ × ℝ} {L L' : List (ℝ × ℝ)}
    (h : SamePad e L e' L') (he : 0 < e.2) (hL : ∀ y ∈ L, 0 < y.2) (he' : 0 < e'.2)
    (hL' : ∀ y ∈ L', 0 < y.2) {a b : ℝ} (ha : gapSum e L + 1 ≤ a)
    (hb : gapSum e' L' + 1 ≤ b) (z : ℝ) :
    fredholmDet (fddOpAt e L he hL a ha) z = fredholmDet (fddOpAt e' L' he' hL' b hb) z := by
  have hc : gapSum e L + 1 ≤ max a b := ha.trans (le_max_left _ _)
  have hc' : gapSum e' L' + 1 ≤ max a b := hb.trans (le_max_right _ _)
  rw [fredholmDet_fddOpAt_indep he hL ha hc z, fddOpAt_of_samePad h he hL he' hL' hc hc',
    fredholmDet_fddOpAt_indep he' hL' hc' hb z]

/-- Padding independence of the canonical operator (its weight `2S` moves with `τ`). -/
theorem fredholmDet_fddOp_of_samePad {e e' : ℝ × ℝ} {L L' : List (ℝ × ℝ)}
    (h : SamePad e L e' L') (he : 0 < e.2) (hL : ∀ y ∈ L, 0 < y.2) (h1 : 1 ≤ gapSum e L)
    (he' : 0 < e'.2) (hL' : ∀ y ∈ L', 0 < y.2) (h1' : 1 ≤ gapSum e' L') (z : ℝ) :
    fredholmDet (fddOp e L he hL h1) z = fredholmDet (fddOp e' L' he' hL' h1') z := by
  rw [fddOp_eq_fddOpAt, fddOp_eq_fddOpAt]
  exact fredholmDet_fddOpAt_of_samePad h he hL he' hL' _ _ z

/-- **`airy1FinCdf` at any admissible padding and weight** (input for dropping a time from `I`):
if the sorted entries of `I` are `e :: L` and `(e', L')` has the same levels and interior gaps
(any positive padding), then `F_I(x) = det(I − J̃)` for `fddOpAt e' L'` at any weight
`a ≥ S' + 1`. -/
theorem airy1FinCdf_eq_fredholmDet_fddOpAt (I : Finset ℝ) (x : I → ℝ) {e : ℝ × ℝ}
    {L : List (ℝ × ℝ)} (h : finEntries I x = e :: L) {e' : ℝ × ℝ} {L' : List (ℝ × ℝ)}
    (hsp : SamePad e L e' L') (he' : 0 < e'.2) (hL' : ∀ y ∈ L', 0 < y.2) {a : ℝ}
    (ha : gapSum e' L' + 1 ≤ a) :
    airy1FinCdf I x = fredholmDet (fddOpAt e' L' he' hL' a ha) 1 := by
  have he : 0 < e.2 := finEntries_pos I x e (by rw [h]; exact List.mem_cons_self)
  have hL : ∀ y ∈ L, 0 < y.2 := fun y hy =>
    finEntries_pos I x y (by rw [h]; exact List.mem_cons_of_mem _ hy)
  have h1 : 1 ≤ gapSum e L := one_le_gapSum he hL (finEntries_lastGap I x e L h)
  unfold airy1FinCdf
  rw [cdfOfEntries_cons h (finEntries_pos I x) (finEntries_lastGap I x) he hL h1,
    fddOp_eq_fddOpAt]
  exact fredholmDet_fddOpAt_of_samePad hsp he hL he' hL' _ ha 1

/-- Weight-only form: `F_I(x) = det(I − J̃_a)` at any admissible weight `a`. -/
theorem airy1FinCdf_eq_fredholmDet_fddOpAt_weight (I : Finset ℝ) (x : I → ℝ) {e : ℝ × ℝ}
    {L : List (ℝ × ℝ)} (h : finEntries I x = e :: L) (he : 0 < e.2) (hL : ∀ y ∈ L, 0 < y.2)
    {a : ℝ} (ha : gapSum e L + 1 ≤ a) :
    airy1FinCdf I x = fredholmDet (fddOpAt e L he hL a ha) 1 :=
  airy1FinCdf_eq_fredholmDet_fddOpAt I x h (samePad_refl L e) he hL ha

end AiryFdd
