/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Fdd.GaussTools

/-!
# The `n`-time discrete hitting kernel

The data of an `n`-time fdd is a nonempty list of
`(level, gap)` entries `e :: L`: `(x_i, t_{i+1} − t_i)` for `i < n` and `(x_n, τ)` with the
padding `τ` as last gap.  With `S = Σ gaps`:

* `lamKerN` — the kernel of `Λ e^{τΔ} = P̄_{x₁} e^{g₁Δ} P̄_{x₂} ⋯ P̄_{x_n} e^{τΔ}` by the list
  recursion `lamKerN (x,g) (y :: L) (u,v) = 1_{u ≤ x} ∫ p_g(u − w) lamKerN y L (w, v) dw`
  (`P̄_x` = projection onto `(−∞, x]`; the operator `Λ` of Quastel–Remenik);
* `hitKerN = p_S − lamKerN` (operator form `H = e^{SΔ} − Λ e^{τΔ}`); `0 ≤ H ≤ p_S`;
* on `u ≤ x₁`: `H_{e :: y :: L}(u, v) = ∫ p_{g₁}(u − w) H_{y :: L}(w, v) dw` (exact).

The kernel depends on the gaps only (time-shift invariance is definitional).  Any real
levels are allowed.
-/

namespace AiryFdd

open MeasureTheory Real Set Filter

/-- `Λ e^{τΔ}` for one level: `1_{u ≤ x} p_τ(u - v)` (`P̄_x e^{τΔ}`). -/
noncomputable def lamKer1 (x τ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Iic x).indicator (fun _ => (1 : ℝ)) p.1 * heatKernel τ (p.1 - p.2)

/-- The one-level hitting kernel `H = p_τ − P̄_x p_τ` (operator form `H = p_S − Λ e^{τΔ}`, `S = τ`). -/
noncomputable def hitKer1 (x τ : ℝ) (p : ℝ × ℝ) : ℝ :=
  heatKernel τ (p.1 - p.2) - lamKer1 x τ p

theorem measurable_lamKer1 (x τ : ℝ) : Measurable (lamKer1 x τ) :=
  ((measurable_const.indicator measurableSet_Iic).comp measurable_fst).mul
    ((continuous_heatKernel τ).comp (continuous_fst.sub continuous_snd)).measurable

theorem measurable_hitKer1 (x τ : ℝ) : Measurable (hitKer1 x τ) :=
  ((continuous_heatKernel τ).comp (continuous_fst.sub continuous_snd)).measurable.sub
    (measurable_lamKer1 x τ)

theorem lamKer1_nonneg {τ : ℝ} (hτ : 0 < τ) (x : ℝ) (p : ℝ × ℝ) : 0 ≤ lamKer1 x τ p :=
  mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (heatKernel_pos hτ _).le

theorem lamKer1_le {τ : ℝ} (hτ : 0 < τ) (x : ℝ) (p : ℝ × ℝ) :
    lamKer1 x τ p ≤ heatKernel τ (p.1 - p.2) := by
  unfold lamKer1
  by_cases h : p.1 ∈ Iic x
  · rw [Set.indicator_of_mem h, one_mul]
  · rw [Set.indicator_of_notMem h, zero_mul]; exact (heatKernel_pos hτ _).le

/-- `H = 1_{u > x} p_τ(u - v)`. -/
theorem hitKer1_eq (x τ : ℝ) (p : ℝ × ℝ) :
    hitKer1 x τ p = (Ioi x).indicator (fun _ => (1 : ℝ)) p.1 * heatKernel τ (p.1 - p.2) := by
  unfold hitKer1 lamKer1
  by_cases h : p.1 ≤ x
  · rw [Set.indicator_of_mem (show p.1 ∈ Iic x from h),
      Set.indicator_of_notMem (show p.1 ∉ Ioi x from not_lt.2 h)]
    ring
  · rw [Set.indicator_of_notMem (show p.1 ∉ Iic x from h),
      Set.indicator_of_mem (show p.1 ∈ Ioi x from not_le.1 h)]
    ring

theorem hitKer1_nonneg {τ : ℝ} (hτ : 0 < τ) (x : ℝ) (p : ℝ × ℝ) : 0 ≤ hitKer1 x τ p :=
  sub_nonneg.2 (lamKer1_le hτ x p)

theorem abs_hitKer1_le {τ : ℝ} (hτ : 0 < τ) (x : ℝ) (p : ℝ × ℝ) :
    |hitKer1 x τ p| ≤ heatKernel τ (p.1 - p.2) := by
  rw [abs_of_nonneg (hitKer1_nonneg hτ x p)]
  exact sub_le_self _ (lamKer1_nonneg hτ x p)

/-- Chernoff at one level: `H(w, v) ≤ e^{θ(w - x)} p_τ(w - v)` for `θ ≥ 0`. -/
theorem hitKer1_le_exp {τ θ : ℝ} (hτ : 0 < τ) (hθ : 0 ≤ θ) (x : ℝ) (p : ℝ × ℝ) :
    hitKer1 x τ p ≤ Real.exp (θ * (p.1 - x)) * heatKernel τ (p.1 - p.2) := by
  rw [hitKer1_eq]
  apply mul_le_mul_of_nonneg_right _ (heatKernel_pos hτ _).le
  by_cases h : p.1 ∈ Ioi x
  · rw [Set.indicator_of_mem h]
    exact Real.one_le_exp (mul_nonneg hθ (sub_nonneg.2 (le_of_lt h)))
  · rw [Set.indicator_of_notMem h]; exact (Real.exp_pos _).le

theorem integrable_heat_mul_hitKer1 {g τ : ℝ} (hg : 0 < g) (hτ : 0 < τ) (x₂ u v : ℝ) :
    Integrable fun w : ℝ => heatKernel g (u - w) * hitKer1 x₂ τ (w, v) :=
  AiryTwoInt.integrable_pair_mul_of_heatKernel_le hg hτ (AiryTwoInt.measurable_heatKerTwo g)
    (measurable_hitKer1 x₂ τ) (fun a b => AiryTwoInt.heatKerTwo_abs_le_self hg (a, b))
    (fun a b => abs_hitKer1_le hτ x₂ (a, b)) u v

/-- Total time `S = Σ gaps` (the last gap is the padding `τ`). -/
def gapSum : ℝ × ℝ → List (ℝ × ℝ) → ℝ
  | e, [] => e.2
  | e, y :: L => e.2 + gapSum y L

/-- The last gap (the padding `τ`). -/
def lastGap : ℝ × ℝ → List (ℝ × ℝ) → ℝ
  | e, [] => e.2
  | _, y :: L => lastGap y L

/-- The list recursion for the kernel of `Λ e^{τΔ}`. -/
noncomputable def lamKerN : ℝ × ℝ → List (ℝ × ℝ) → ℝ × ℝ → ℝ
  | e, [] => lamKer1 e.1 e.2
  | e, y :: L => fun p => (Iic e.1).indicator (fun _ => (1 : ℝ)) p.1
      * AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (lamKerN y L) p

/-- The `n`-level hitting kernel `H = p_S − Λ e^{τΔ}`. -/
noncomputable def hitKerN (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (p : ℝ × ℝ) : ℝ :=
  heatKernel (gapSum e L) (p.1 - p.2) - lamKerN e L p

theorem hitKerN_nil (e : ℝ × ℝ) : hitKerN e [] = hitKer1 e.1 e.2 := rfl

theorem gapSum_pos : ∀ (L : List (ℝ × ℝ)) (e : ℝ × ℝ), 0 < e.2 → (∀ y ∈ L, 0 < y.2) →
    0 < gapSum e L
  | [], _, he, _ => he
  | y :: L, e, he, hL => by
    have := gapSum_pos L y (hL y List.mem_cons_self)
      (fun z hz => hL z (List.mem_cons_of_mem _ hz))
    show 0 < e.2 + gapSum y L
    linarith

theorem lastGap_pos : ∀ (L : List (ℝ × ℝ)) (e : ℝ × ℝ), 0 < e.2 → (∀ y ∈ L, 0 < y.2) →
    0 < lastGap e L
  | [], _, he, _ => he
  | y :: L, _, _, hL => lastGap_pos L y (hL y List.mem_cons_self)
      (fun z hz => hL z (List.mem_cons_of_mem _ hz))

theorem lastGap_le_gapSum : ∀ (L : List (ℝ × ℝ)) (e : ℝ × ℝ), 0 < e.2 → (∀ y ∈ L, 0 < y.2) →
    lastGap e L ≤ gapSum e L
  | [], _, _, _ => le_rfl
  | y :: L, e, he, hL => by
    have := lastGap_le_gapSum L y (hL y List.mem_cons_self)
      (fun z hz => hL z (List.mem_cons_of_mem _ hz))
    show lastGap y L ≤ e.2 + gapSum y L
    linarith

theorem compKernel_heat_mem {g t : ℝ} (hg : 0 < g) (ht : 0 < t) {K : ℝ × ℝ → ℝ}
    (hK : Measurable K) (h0 : ∀ p, 0 ≤ K p) (h1 : ∀ p, K p ≤ heatKernel t (p.1 - p.2))
    (p : ℝ × ℝ) :
    0 ≤ AiryConj.compKernel (AiryTwoInt.heatKerTwo g) K p ∧
      AiryConj.compKernel (AiryTwoInt.heatKerTwo g) K p ≤ heatKernel (g + t) (p.1 - p.2) := by
  obtain ⟨u, v⟩ := p
  have hint : Integrable fun w : ℝ => heatKernel g (u - w) * K (w, v) :=
    AiryTwoInt.integrable_pair_mul_of_heatKernel_le hg ht (AiryTwoInt.measurable_heatKerTwo g)
      hK (fun a b => AiryTwoInt.heatKerTwo_abs_le_self hg (a, b))
      (fun a b => by rw [abs_of_nonneg (h0 _)]; exact h1 (a, b)) u v
  show 0 ≤ ∫ w : ℝ, heatKernel g (u - w) * K (w, v) ∧
    (∫ w : ℝ, heatKernel g (u - w) * K (w, v)) ≤ heatKernel (g + t) (u - v)
  refine ⟨integral_nonneg fun w => mul_nonneg (heatKernel_pos hg _).le (h0 _), ?_⟩
  rw [← AiryTwoInt.heatKernel_conv hg ht u v]
  exact integral_mono hint (integrable_heat_mul_heat hg ht u v)
    fun w => mul_le_mul_of_nonneg_left (h1 (w, v)) (heatKernel_pos hg _).le

theorem lamKerN_props : ∀ (L : List (ℝ × ℝ)) (e : ℝ × ℝ), 0 < e.2 → (∀ y ∈ L, 0 < y.2) →
    Measurable (lamKerN e L) ∧ (∀ p, 0 ≤ lamKerN e L p) ∧
      (∀ p, lamKerN e L p ≤ heatKernel (gapSum e L) (p.1 - p.2))
  | [], e, he, _ => ⟨measurable_lamKer1 _ _, lamKer1_nonneg he _, lamKer1_le he _⟩
  | y :: L, e, he, hL => by
    have hy : 0 < y.2 := hL y List.mem_cons_self
    have hL' : ∀ z ∈ L, 0 < z.2 := fun z hz => hL z (List.mem_cons_of_mem _ hz)
    obtain ⟨hm, h0, h1⟩ := lamKerN_props L y hy hL'
    have hS := gapSum_pos L y hy hL'
    have hI0 : ∀ r : ℝ, 0 ≤ (Iic e.1).indicator (fun _ => (1 : ℝ)) r :=
      fun r => Set.indicator_nonneg (fun _ _ => zero_le_one) r
    have hI1 : ∀ r : ℝ, (Iic e.1).indicator (fun _ => (1 : ℝ)) r ≤ 1 :=
      fun r => Set.indicator_le_self' (fun _ _ => zero_le_one) r
    refine ⟨?_, fun p => ?_, fun p => ?_⟩
    · exact ((measurable_const.indicator measurableSet_Iic).comp measurable_fst).mul
        (AiryTwoInt.measurable_compKernel (AiryTwoInt.measurable_heatKerTwo _) hm)
    · exact mul_nonneg (hI0 _) (compKernel_heat_mem he hS hm h0 h1 p).1
    · exact (mul_le_of_le_one_left (compKernel_heat_mem he hS hm h0 h1 p).1 (hI1 _)).trans
        (compKernel_heat_mem he hS hm h0 h1 p).2

theorem measurable_hitKerN {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) : Measurable (hitKerN e L) :=
  ((continuous_heatKernel _).comp (continuous_fst.sub continuous_snd)).measurable.sub
    (lamKerN_props L e he hL).1

theorem hitKerN_nonneg {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) (p : ℝ × ℝ) : 0 ≤ hitKerN e L p :=
  sub_nonneg.2 ((lamKerN_props L e he hL).2.2 p)

theorem abs_hitKerN_le {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2)
    (hL : ∀ y ∈ L, 0 < y.2) (p : ℝ × ℝ) :
    |hitKerN e L p| ≤ heatKernel (gapSum e L) (p.1 - p.2) := by
  rw [abs_of_nonneg (hitKerN_nonneg he hL p)]
  exact sub_le_self _ ((lamKerN_props L e he hL).2.1 p)

/-- On `u ≤ x₁`: `H_{e::y::L}(u, v) = ∫ p_{g₁}(u − w) H_{y::L}(w, v) dw`. -/
theorem hitKerN_cons_eq_integral {e y : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2)
    (hy : 0 < y.2) (hL : ∀ z ∈ L, 0 < z.2) {u : ℝ} (hu : u ≤ e.1) (v : ℝ) :
    hitKerN e (y :: L) (u, v) = ∫ w : ℝ, heatKernel e.2 (u - w) * hitKerN y L (w, v) := by
  obtain ⟨hm, h0, h1⟩ := lamKerN_props L y hy hL
  have hS := gapSum_pos L y hy hL
  have hintL : Integrable fun w : ℝ => heatKernel e.2 (u - w) * lamKerN y L (w, v) :=
    AiryTwoInt.integrable_pair_mul_of_heatKernel_le he hS (AiryTwoInt.measurable_heatKerTwo _)
      hm (fun a b => AiryTwoInt.heatKerTwo_abs_le_self he (a, b))
      (fun a b => by rw [abs_of_nonneg (h0 _)]; exact h1 (a, b)) u v
  show heatKernel (e.2 + gapSum y L) (u - v) - (Iic e.1).indicator (fun _ => (1 : ℝ)) u
      * ∫ w : ℝ, heatKernel e.2 (u - w) * lamKerN y L (w, v) = _
  rw [Set.indicator_of_mem (show u ∈ Iic e.1 from hu), one_mul,
    ← AiryTwoInt.heatKernel_conv he hS u v,
    ← integral_sub (integrable_heat_mul_heat he hS u v) hintL]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [hitKerN]
  ring


end AiryFdd
