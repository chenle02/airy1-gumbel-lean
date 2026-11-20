/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Process.Kolmogorov
import Airy1Gumbel.Airy1Process
import Airy1GumbelContrib.SmallWeight.TwoTimeDefectRev

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal

namespace Airy1Gumbel

/-!
# Truncated increment moments of the Airy₁ process law

For clamp levels `L ≤ U` let `X_s = clamp_{[L,U]}(f s)` be the clamped coordinate process on
`(ℝ → ℝ, airy1Law h)`. We prove a Kolmogorov-type moment bound, for every real `p > 1`,
uniformly in `x` and `0 < t ≤ 1`:

`𝔼|X_{x+t} − X_x|^p ≤ K(C, U − L, p) · t^{(p−1)/2}`,
`K(C, D, p) = p · C · (D · 32^{(p−1)/2} Γ((p−1)/2) + 32^{p/2} Γ(p/2)/2)`
(`truncMomentConst`), **linear in the clamp width** `D = U − L`; `C = C_fwd + C_rev` is the sum
of the two-time defect constants at the lower level `L` (contrib `SmallWeight/TwoTimeDefect*`), and does not
depend on `U`. So `q = (p−1)/2 = 1 + β` with `β = (p−3)/2 > 0` for `p > 3`.

Method (no densities, no time reversal, no Hoeffding second-derivative identity):
* **defect → probability** (`airy1Law_fwd_le`, `airy1Law_rev_le`): by `airy1Law_fdd`,
  `P(f x ≤ a, f(x+t) > b) = G_x(a) − F(a, b)` and `P(f x > a, f(x+t) ≤ b) = G_{x+t}(b) − F(a, b)`;
  the two-time defect bounds (both orders, `L ≤ min a b`) give `≤ C e^{−(b−a)²/8t}`;
* **grid union bound** (`airy1Law_clamp_gap_le`): if `|X_{x+t} − X_x| > z` then for the grid
  `g_k = L + (k+1) z/2`, `k < ⌈2D/z⌉`, some pair `(g_k, g_k + z/2)` is crossed upward or downward,
  so `P(|ΔX| > z) ≤ (C_fwd + C_rev)(2D/z + 1) e^{−z²/32t}`;
* **layer cake** (`lintegral_rpow_eq_lintegral_meas_lt_mul`) and the Gaussian moments
  `∫₀^∞ z^s e^{−b z²} dz = b^{−(s+1)/2} Γ((s+1)/2)/2`.

The moment bound is stated for abstract defect hypotheses `FwdDefectBound L C`,
`RevDefectBound L C'` (`lintegral_clamp_incr_rpow_le`), so that any weight-parametric defect constant
(contrib `airy1FinCdf_twoTime_defect_le` / `_rev_le`, e.g. the small-weight constants of
`SmallWeightDefect` with `L = −M`) can be fed in;
the fixed-frame `w = 3` statements give them for every fixed `L` (`fwdDefectBound_exists`,
`revDefectBound_exists`; that constant is doubly exponential in `−L`).

Kolmogorov–Chentsov interface (Mathlib `ProbabilityTheory.IsKolmogorovProcess`, the hypothesis
of BrownianMotion's `exists_modification_holder` / `countable_kolmogorov_chentsov` via
`IsKolmogorovProcess.IsAEKolmogorovProcess`):
* local form, on any index set of diameter `≤ 1`, with constant `K` (linear in `D`):
  `isKolmogorovProcess_clamp_of_diam_le`;
* global form on `ℝ` and on `ℝ≥0` with constant `K + D^p` (`|ΔX| ≤ D` for `|s − u| > 1`):
  `isKolmogorovProcess_clamp`, `isKolmogorovProcess_clamp_nnreal`.
-/

/-! ## The clamp -/

/-- The clamp `v ↦ max L (min U v)` to `[L, U]`. -/
noncomputable def clampTo (L U v : ℝ) : ℝ := max L (min U v)

theorem clampTo_mem {L U : ℝ} (hLU : L ≤ U) (v : ℝ) : clampTo L U v ∈ Icc L U :=
  ⟨le_max_left _ _, max_le hLU (min_le_left _ _)⟩

theorem le_of_clampTo_le {L U v a : ℝ} (haU : a < U) (h : clampTo L U v ≤ a) : v ≤ a := by
  by_contra hv
  push Not at hv
  have : a < min U v := lt_min haU hv
  exact absurd h (not_le.2 (this.trans_le (le_max_right _ _)))

theorem lt_of_lt_clampTo {L U v b : ℝ} (hLb : L ≤ b) (h : b < clampTo L U v) : b < v := by
  by_contra hv
  push Not at hv
  exact absurd h (not_lt.2 (max_le hLb ((min_le_right U v).trans hv)))

theorem measurable_clampTo (L U : ℝ) : Measurable (clampTo L U) :=
  (continuous_const.max (continuous_const.min continuous_id)).measurable

theorem abs_clampTo_sub_le {L U : ℝ} (hLU : L ≤ U) (v w : ℝ) :
    |clampTo L U v - clampTo L U w| ≤ U - L := by
  have h1 := clampTo_mem hLU v
  have h2 := clampTo_mem hLU w
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## One-point bridge

The reverse two-time defect bound is against the one-time CDF at the second time `x + t`; one-point CDFs do
not depend on the time. (The moment bound below uses `G_{x+t}` directly, so it does not need
this.) -/

theorem cdfOfEntries_congr {L₁ L₂ : List (ℝ × ℝ)} (h : L₁ = L₂) (p₁ : ∀ y ∈ L₁, 0 < y.2)
    (q₁ : ∀ e L', L₁ = e :: L' → AiryFdd.lastGap e L' = 1) (p₂ : ∀ y ∈ L₂, 0 < y.2)
    (q₂ : ∀ e L', L₂ = e :: L' → AiryFdd.lastGap e L' = 1) :
    AiryFdd.cdfOfEntries L₁ p₁ q₁ = AiryFdd.cdfOfEntries L₂ p₂ q₂ := by
  subst h; rfl

/-- One-point Airy₁ CDFs do not depend on the time: `F_{{x}}(c) = F_{{x'}}(c)`. -/
theorem airy1FinCdf_singleton_eq (x x' c : ℝ) :
    AiryFdd.airy1FinCdf {x} (fun _ => c) = AiryFdd.airy1FinCdf {x'} (fun _ => c) := by
  unfold AiryFdd.airy1FinCdf
  exact cdfOfEntries_congr
    ((AiryFdd.finEntries_singleton x c).trans (AiryFdd.finEntries_singleton x' c).symm) _ _ _ _

/-! ## The two-time defect hypotheses -/

/-- Forward two-time defect bound at lower level `L` with constant `C` (shape of contrib
`AiryFdd.airy1FinCdf_twoTime_defect`, with `−m₀ = L`). -/
def FwdDefectBound (L C : ℝ) : Prop :=
  ∀ (x t a b : ℝ) (y : ({x, x + t} : Finset ℝ) → ℝ), 0 < t → t ≤ 1 →
    L ≤ a → a ≤ b → (∀ h, y ⟨x, h⟩ = a) → (∀ h, y ⟨x + t, h⟩ = b) →
    |AiryFdd.airy1FinCdf {x} (fun _ => a) - AiryFdd.airy1FinCdf {x, x + t} y|
      ≤ C * Real.exp (-(b - a) ^ 2 / (8 * t))

/-- Reverse two-time defect bound at lower level `L` with constant `C` (shape of contrib
`AiryFdd.airy1FinCdf_twoTime_defect_rev`, with `−m₀ = L`). -/
def RevDefectBound (L C : ℝ) : Prop :=
  ∀ (x t a b : ℝ) (y : ({x, x + t} : Finset ℝ) → ℝ), 0 < t → t ≤ 1 →
    L ≤ b → b ≤ a → (∀ h, y ⟨x, h⟩ = a) → (∀ h, y ⟨x + t, h⟩ = b) →
    |AiryFdd.airy1FinCdf {x + t} (fun _ => b) - AiryFdd.airy1FinCdf {x, x + t} y|
      ≤ C * Real.exp (-(a - b) ^ 2 / (8 * t))

/-- Forward two-time defect bound (fixed frame `τ = 1`, `w = 3`) in the `FwdDefectBound` shape. -/
theorem fwdDefectBound_exists (L : ℝ) : ∃ C : ℝ, 0 < C ∧ FwdDefectBound L C := by
  obtain ⟨C, hC, H⟩ := AiryFdd.airy1FinCdf_twoTime_defect (-L)
  exact ⟨C, hC, fun x t a b y ht ht1 ha hab hya hyb =>
    H x t a b y ht ht1 (by rw [neg_neg]; exact ha) hab hya hyb⟩

/-- Reverse two-time defect bound (fixed frame `τ = 1`, `w = 3`) in the `RevDefectBound` shape. -/
theorem revDefectBound_exists (L : ℝ) : ∃ C : ℝ, 0 < C ∧ RevDefectBound L C := by
  obtain ⟨C, hC, H⟩ := AiryFdd.airy1FinCdf_twoTime_defect_rev (-L)
  exact ⟨C, hC, fun x t a b y ht ht1 hb hba hya hyb =>
    H x t a b y ht ht1 (by rw [neg_neg]; exact hb) hba hya hyb⟩

/-! ## Defects as probabilities -/

theorem measurableSet_le_eval (x a : ℝ) : MeasurableSet {f : ℝ → ℝ | f x ≤ a} :=
  measurableSet_le (measurable_pi_apply x) measurable_const

/-- **Forward crossing probability**: `P(f x ≤ a, f(x+t) > b) ≤ C e^{−(b−a)²/8t}` for
`L ≤ a ≤ b`, `0 < t ≤ 1`. -/
theorem airy1Law_fwd_le (h : Airy1FddPositive) {L C : ℝ} (hF : FwdDefectBound L C)
    {x t a b : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (ha : L ≤ a) (hab : a ≤ b) :
    airy1Law h {f : ℝ → ℝ | f x ≤ a ∧ b < f (x + t)}
      ≤ ENNReal.ofReal (C * Real.exp (-(b - a) ^ 2 / (8 * t))) := by
  classical
  have hne : x + t ≠ x := ne_of_gt (by linarith)
  let lev : ℝ → ℝ := fun s => if s = x then a else b
  have hA : (airy1Law h).real {f : ℝ → ℝ | ∀ s ∈ ({x} : Finset ℝ), f s ≤ (fun _ => a) s}
      = AiryFdd.airy1FinCdf {x} (fun _ => a) := airy1Law_fdd h {x} (fun _ => a)
  have hB : (airy1Law h).real {f : ℝ → ℝ | ∀ s ∈ ({x, x + t} : Finset ℝ), f s ≤ lev s}
      = AiryFdd.airy1FinCdf {x, x + t} (fun i => lev i) := airy1Law_fdd h {x, x + t} lev
  have hset : {f : ℝ → ℝ | f x ≤ a ∧ b < f (x + t)}
      = {f : ℝ → ℝ | ∀ s ∈ ({x} : Finset ℝ), f s ≤ (fun _ => a) s}
        \ {f : ℝ → ℝ | ∀ s ∈ ({x, x + t} : Finset ℝ), f s ≤ lev s} := by
    ext f
    simp only [lev, mem_ofPred_eq, Set.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      forall_eq_or_imp, forall_eq, hne, reduceIte, not_and, not_le]
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
  have hsub : {f : ℝ → ℝ | ∀ s ∈ ({x, x + t} : Finset ℝ), f s ≤ lev s}
      ⊆ {f : ℝ → ℝ | ∀ s ∈ ({x} : Finset ℝ), f s ≤ (fun _ => a) s} := by
    intro f hf s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    have := hf s (by simp)
    simpa [lev] using this
  rw [hset, ← ofReal_measureReal, measureReal_sdiff hsub
    (measurableSet_setOf_forall_mem_finset_le _ _), hA, hB]
  refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
  exact hF x t a b (fun i => lev i) ht ht1 ha hab (fun _ => by simp [lev])
    (fun _ => by simp [lev, hne])

/-- **Reverse crossing probability**: `P(f x > a, f(x+t) ≤ b) ≤ C e^{−(a−b)²/8t}` for
`L ≤ b ≤ a`, `0 < t ≤ 1`. -/
theorem airy1Law_rev_le (h : Airy1FddPositive) {L C : ℝ} (hR : RevDefectBound L C)
    {x t a b : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hb : L ≤ b) (hba : b ≤ a) :
    airy1Law h {f : ℝ → ℝ | a < f x ∧ f (x + t) ≤ b}
      ≤ ENNReal.ofReal (C * Real.exp (-(a - b) ^ 2 / (8 * t))) := by
  classical
  have hne : x + t ≠ x := ne_of_gt (by linarith)
  let lev : ℝ → ℝ := fun s => if s = x then a else b
  have hA : (airy1Law h).real {f : ℝ → ℝ | ∀ s ∈ ({x + t} : Finset ℝ), f s ≤ (fun _ => b) s}
      = AiryFdd.airy1FinCdf {x + t} (fun _ => b) := airy1Law_fdd h {x + t} (fun _ => b)
  have hB : (airy1Law h).real {f : ℝ → ℝ | ∀ s ∈ ({x, x + t} : Finset ℝ), f s ≤ lev s}
      = AiryFdd.airy1FinCdf {x, x + t} (fun i => lev i) := airy1Law_fdd h {x, x + t} lev
  have hset : {f : ℝ → ℝ | a < f x ∧ f (x + t) ≤ b}
      = {f : ℝ → ℝ | ∀ s ∈ ({x + t} : Finset ℝ), f s ≤ (fun _ => b) s}
        \ {f : ℝ → ℝ | ∀ s ∈ ({x, x + t} : Finset ℝ), f s ≤ lev s} := by
    ext f
    simp only [lev, mem_ofPred_eq, Set.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      forall_eq_or_imp, forall_eq, hne, reduceIte, not_and, not_le]
    exact ⟨fun h => ⟨h.2, fun h' => absurd h' (not_le.2 h.1)⟩,
      fun h => ⟨lt_of_not_ge fun h' => absurd h.1 (not_le.2 (h.2 h')), h.1⟩⟩
  have hsub : {f : ℝ → ℝ | ∀ s ∈ ({x, x + t} : Finset ℝ), f s ≤ lev s}
      ⊆ {f : ℝ → ℝ | ∀ s ∈ ({x + t} : Finset ℝ), f s ≤ (fun _ => b) s} := by
    intro f hf s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    have := hf (x + t) (by simp)
    simpa [lev, hne] using this
  rw [hset, ← ofReal_measureReal, measureReal_sdiff hsub
    (measurableSet_setOf_forall_mem_finset_le _ _), hA, hB]
  refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
  exact hR x t a b (fun i => lev i) ht ht1 hb hba (fun _ => by simp [lev])
    (fun _ => by simp [lev, hne])

/-! ## Increment tail of the clamped process (grid union bound) -/

/-- **Tail of the clamped increment**: for `L ≤ U`, `z > 0`, `0 < t ≤ 1`,
`P(|X_{x+t} − X_x| > z) ≤ (C + C')(2(U − L)/z + 1) e^{−z²/32t}`. -/
theorem airy1Law_clamp_gap_le (h : Airy1FddPositive) {L U C C' : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C) (hR : RevDefectBound L C')
    {x t z : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hz : 0 < z) :
    airy1Law h {f : ℝ → ℝ | z < |clampTo L U (f (x + t)) - clampTo L U (f x)|}
      ≤ ENNReal.ofReal ((C + C') * (2 * (U - L) / z + 1) * Real.exp (-z ^ 2 / (32 * t))) := by
  have hδ0 : 0 < z / 2 := by positivity
  let N : ℕ := ⌈(U - L) / (z / 2)⌉₊
  let g : ℕ → ℝ := fun k => L + ((k : ℝ) + 1) * (z / 2)
  have hLg : ∀ k : ℕ, L ≤ g k := fun k => by
    have : 0 ≤ ((k : ℝ) + 1) * (z / 2) := by positivity
    simp only [g]; linarith
  have hexp : ∀ k : ℕ, Real.exp (-(g k + z / 2 - g k) ^ 2 / (8 * t))
      = Real.exp (-z ^ 2 / (32 * t)) := fun k => by
    congr 1
    rw [show g k + z / 2 - g k = z / 2 by ring]
    field_simp
    ring
  have hsub : {f : ℝ → ℝ | z < |clampTo L U (f (x + t)) - clampTo L U (f x)|}
      ⊆ ⋃ k ∈ Finset.range N, ({f : ℝ → ℝ | f x ≤ g k ∧ g k + z / 2 < f (x + t)}
        ∪ {f : ℝ → ℝ | g k + z / 2 < f x ∧ f (x + t) ≤ g k}) := by
    intro f hf
    simp only [mem_ofPred_eq] at hf
    simp only [mem_iUnion, Finset.mem_range, mem_union, mem_ofPred_eq]
    have hX := clampTo_mem hLU (f x)
    have hY := clampTo_mem hLU (f (x + t))
    rcases lt_abs.1 hf with h1 | h1
    · -- upward crossing: grid cell of `X_x`
      obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, (k : ℝ) * (z / 2) ≤ clampTo L U (f x) - L ∧
          clampTo L U (f x) - L < ((k : ℝ) + 1) * (z / 2) := by
        refine ⟨⌊(clampTo L U (f x) - L) / (z / 2)⌋₊, ?_, ?_⟩
        · rw [← le_div_iff₀ hδ0]
          exact Nat.floor_le (div_nonneg (by linarith [hX.1]) hδ0.le)
        · rw [← div_lt_iff₀ hδ0]
          exact Nat.lt_floor_add_one _
      have hgk : g k + z / 2 = L + (k : ℝ) * (z / 2) + z := by simp only [g]; ring
      have hXa : clampTo L U (f x) < g k := by simp only [g]; linarith
      have hYa : g k + z / 2 < clampTo L U (f (x + t)) := by rw [hgk]; linarith
      have hkN : k < N := by
        have hk' : (k : ℝ) < (U - L) / (z / 2) := by
          rw [lt_div_iff₀ hδ0]; linarith [hY.2]
        exact_mod_cast hk'.trans_le (Nat.le_ceil _)
      refine ⟨k, hkN, Or.inl ⟨le_of_clampTo_le ?_ hXa.le, lt_of_lt_clampTo ?_ hYa⟩⟩
      · linarith [hY.2]
      · linarith [hLg k]
    · -- downward crossing: grid cell of `X_{x+t}`
      obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, (k : ℝ) * (z / 2) ≤ clampTo L U (f (x + t)) - L ∧
          clampTo L U (f (x + t)) - L < ((k : ℝ) + 1) * (z / 2) := by
        refine ⟨⌊(clampTo L U (f (x + t)) - L) / (z / 2)⌋₊, ?_, ?_⟩
        · rw [← le_div_iff₀ hδ0]
          exact Nat.floor_le (div_nonneg (by linarith [hY.1]) hδ0.le)
        · rw [← div_lt_iff₀ hδ0]
          exact Nat.lt_floor_add_one _
      have hgk : g k + z / 2 = L + (k : ℝ) * (z / 2) + z := by simp only [g]; ring
      have hYa : clampTo L U (f (x + t)) < g k := by simp only [g]; linarith
      have hXa : g k + z / 2 < clampTo L U (f x) := by rw [hgk]; linarith
      have hkN : k < N := by
        have hk' : (k : ℝ) < (U - L) / (z / 2) := by
          rw [lt_div_iff₀ hδ0]; linarith [hX.2]
        exact_mod_cast hk'.trans_le (Nat.le_ceil _)
      refine ⟨k, hkN, Or.inr ⟨lt_of_lt_clampTo ?_ hXa, le_of_clampTo_le ?_ hYa.le⟩⟩
      · linarith [hLg k]
      · linarith [hX.2]
  have hE := (Real.exp_pos (-z ^ 2 / (32 * t))).le
  calc airy1Law h {f : ℝ → ℝ | z < |clampTo L U (f (x + t)) - clampTo L U (f x)|}
      ≤ airy1Law h (⋃ k ∈ Finset.range N, ({f : ℝ → ℝ | f x ≤ g k ∧ g k + z / 2 < f (x + t)}
        ∪ {f : ℝ → ℝ | g k + z / 2 < f x ∧ f (x + t) ≤ g k})) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range N, airy1Law h ({f : ℝ → ℝ | f x ≤ g k ∧ g k + z / 2 < f (x + t)}
        ∪ {f : ℝ → ℝ | g k + z / 2 < f x ∧ f (x + t) ≤ g k}) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, ENNReal.ofReal ((C + C') * Real.exp (-z ^ 2 / (32 * t))) := by
        refine Finset.sum_le_sum fun k _ => (measure_union_le _ _).trans ?_
        have e1 := airy1Law_fwd_le h hF (x := x) ht ht1 (hLg k)
          (show g k ≤ g k + z / 2 by linarith)
        have e2 := airy1Law_rev_le h hR (x := x) ht ht1 (hLg k)
          (show g k ≤ g k + z / 2 by linarith)
        rw [hexp k] at e1 e2
        refine (add_le_add e1 e2).trans (le_of_eq ?_)
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]
    _ = ENNReal.ofReal ((N : ℝ) * ((C + C') * Real.exp (-z ^ 2 / (32 * t)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((C + C') * (2 * (U - L) / z + 1) * Real.exp (-z ^ 2 / (32 * t))) := by
        apply ENNReal.ofReal_le_ofReal
        have hN : (N : ℝ) ≤ 2 * (U - L) / z + 1 := by
          have h1 := Nat.ceil_lt_add_one (div_nonneg (by linarith : 0 ≤ U - L) hδ0.le)
          have h2 : (U - L) / (z / 2) = 2 * (U - L) / z := by field_simp
          refine h1.le.trans (le_of_eq ?_)
          rw [h2]
        have hCE : 0 ≤ (C + C') * Real.exp (-z ^ 2 / (32 * t)) := by positivity
        calc (N : ℝ) * ((C + C') * Real.exp (-z ^ 2 / (32 * t)))
            ≤ (2 * (U - L) / z + 1) * ((C + C') * Real.exp (-z ^ 2 / (32 * t))) :=
              mul_le_mul_of_nonneg_right hN hCE
          _ = _ := by ring

/-! ## The moment bound -/

/-- The truncated-moment constant `K(C, D, p) = p C (D 32^{(p−1)/2} Γ((p−1)/2) +
32^{p/2} Γ(p/2)/2)`, linear in the clamp width `D`. -/
noncomputable def truncMomentConst (C D p : ℝ) : ℝ :=
  p * C * (D * (32 : ℝ) ^ ((p - 1) / 2) * Real.Gamma ((p - 1) / 2)
    + (32 : ℝ) ^ (p / 2) * Real.Gamma (p / 2) / 2)

theorem truncMomentConst_nonneg {C D p : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hp : 1 < p) :
    0 ≤ truncMomentConst C D p := by
  have h1 := Real.Gamma_pos_of_pos (show 0 < (p - 1) / 2 by linarith)
  have h2 := Real.Gamma_pos_of_pos (show 0 < p / 2 by linarith)
  unfold truncMomentConst
  have : 0 ≤ p := by linarith
  positivity

/-- `(1/(32t))^{−r} = 32^r t^r`. -/
theorem one_div_rpow_neg {t : ℝ} (ht : 0 < t) (r : ℝ) :
    (1 / (32 * t)) ^ (-r) = (32 : ℝ) ^ r * t ^ r := by
  rw [Real.rpow_neg (by positivity), one_div, Real.inv_rpow (by positivity), inv_inv,
    Real.mul_rpow (by norm_num) ht.le]

/-- **Truncated-moment bound** (abstract defect constants). For `L ≤ U`, real `p > 1`, all
`x` and `0 < t ≤ 1`:
`𝔼|clamp(f(x+t)) − clamp(f x)|^p ≤ K(C + C', U − L, p) t^{(p−1)/2}` under `airy1Law h`. -/
theorem lintegral_clamp_incr_rpow_le (h : Airy1FddPositive) {L U C C' p : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C) (hR : RevDefectBound L C')
    (hp : 1 < p) {x t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∫⁻ f, ENNReal.ofReal (|clampTo L U (f (x + t)) - clampTo L U (f x)| ^ p) ∂airy1Law h
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p * t ^ ((p - 1) / 2)) := by
  have hb0 : 0 < 1 / (32 * t) := by positivity
  have hC2 : 0 ≤ C + C' := by linarith
  have hD : 0 ≤ U - L := by linarith
  have hFm : Measurable fun f : ℝ → ℝ => |clampTo L U (f (x + t)) - clampTo L U (f x)| :=
    continuous_abs.measurable.comp (((measurable_clampTo L U).comp (measurable_pi_apply _)).sub
      ((measurable_clampTo L U).comp (measurable_pi_apply _)))
  have hi1 : IntegrableOn (fun z : ℝ => z ^ (p - 2) * Real.exp (-(1 / (32 * t)) * z ^ (2 : ℝ)))
      (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) two_pos hb0
  have hi2 : IntegrableOn (fun z : ℝ => z ^ (p - 1) * Real.exp (-(1 / (32 * t)) * z ^ (2 : ℝ)))
      (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) two_pos hb0
  let G : ℝ → ℝ := fun z => (C + C') * (2 * (U - L) *
    (z ^ (p - 2) * Real.exp (-(1 / (32 * t)) * z ^ (2 : ℝ)))
      + z ^ (p - 1) * Real.exp (-(1 / (32 * t)) * z ^ (2 : ℝ)))
  have hGi : IntegrableOn G (Ioi 0) := ((hi1.const_mul _).add hi2).const_mul _
  have hGnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz : 0 < z := hz
    simp only [G, Pi.zero_apply]
    have := Real.rpow_pos_of_pos hz (p - 2)
    have := Real.rpow_pos_of_pos hz (p - 1)
    positivity
  have hpt : ∀ z ∈ Ioi (0 : ℝ),
      airy1Law h {f : ℝ → ℝ | z < |clampTo L U (f (x + t)) - clampTo L U (f x)|}
        * ENNReal.ofReal (z ^ (p - 1)) ≤ ENNReal.ofReal (G z) := by
    intro z hz
    have hz : 0 < z := hz
    refine le_trans (mul_le_mul_of_nonneg_right
      (airy1Law_clamp_gap_le h hLU hC hC' hF hR ht ht1 hz) (by positivity)) ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply le_of_eq
    congr 1
    have e1 : Real.exp (-z ^ 2 / (32 * t)) = Real.exp (-(1 / (32 * t)) * z ^ (2 : ℝ)) := by
      rw [Real.rpow_two]; congr 1; ring
    have e2 : z ^ (p - 1) = z ^ (p - 2) * z := by
      rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one hz.ne']
    simp only [G]
    rw [e1, e2]
    field_simp
  have hI1 := integral_rpow_mul_exp_neg_mul_rpow (q := p - 2) two_pos (by linarith) hb0
  have hI2 := integral_rpow_mul_exp_neg_mul_rpow (q := p - 1) two_pos (by linarith) hb0
  have hintG : ∫ z in Ioi (0 : ℝ), G z = (C + C') * (2 * (U - L) *
      ((1 / (32 * t)) ^ (-(p - 2 + 1) / 2) * (1 / 2) * Real.Gamma ((p - 2 + 1) / 2))
        + (1 / (32 * t)) ^ (-(p - 1 + 1) / 2) * (1 / 2) * Real.Gamma ((p - 1 + 1) / 2)) := by
    simp only [G]
    rw [integral_const_mul, integral_add (hi1.const_mul _) hi2, integral_const_mul, hI1, hI2]
  calc ∫⁻ f, ENNReal.ofReal (|clampTo L U (f (x + t)) - clampTo L U (f x)| ^ p) ∂airy1Law h
      = ENNReal.ofReal p * ∫⁻ z in Ioi 0,
          airy1Law h {f : ℝ → ℝ | z < |clampTo L U (f (x + t)) - clampTo L U (f x)|}
            * ENNReal.ofReal (z ^ (p - 1)) :=
        lintegral_rpow_eq_lintegral_meas_lt_mul (airy1Law h)
          (f := fun f : ℝ → ℝ => |clampTo L U (f (x + t)) - clampTo L U (f x)|)
          (ae_of_all _ fun f => abs_nonneg _) hFm.aemeasurable (by linarith)
    _ ≤ ENNReal.ofReal p * ∫⁻ z in Ioi 0, ENNReal.ofReal (G z) :=
        mul_le_mul_of_nonneg_left (setLIntegral_mono' measurableSet_Ioi hpt) (by positivity)
    _ = ENNReal.ofReal (p * ∫ z in Ioi (0 : ℝ), G z) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hGi hGnn, ← ENNReal.ofReal_mul (by linarith)]
    _ ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p * t ^ ((p - 1) / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hintG, show -(p - 2 + 1) / 2 = -((p - 1) / 2) by ring,
          show -(p - 1 + 1) / 2 = -(p / 2) by ring, show (p - 2 + 1) / 2 = (p - 1) / 2 by ring,
          show (p - 1 + 1) / 2 = p / 2 by ring, one_div_rpow_neg ht, one_div_rpow_neg ht]
        have hG1 := (Real.Gamma_pos_of_pos (show 0 < (p - 1) / 2 by linarith)).le
        have hG2 := (Real.Gamma_pos_of_pos (show 0 < p / 2 by linarith)).le
        have ht12 : t ^ (p / 2) ≤ t ^ ((p - 1) / 2) :=
          Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
        have hB : 0 ≤ p * (C + C') * ((32 : ℝ) ^ (p / 2) * Real.Gamma (p / 2) / 2) := by
          have : 0 ≤ p := by linarith
          positivity
        have key := mul_le_mul_of_nonneg_left ht12 hB
        unfold truncMomentConst
        have e : p * ((C + C') * (2 * (U - L) * ((32 : ℝ) ^ ((p - 1) / 2) * t ^ ((p - 1) / 2)
              * (1 / 2) * Real.Gamma ((p - 1) / 2)) + (32 : ℝ) ^ (p / 2) * t ^ (p / 2) * (1 / 2)
              * Real.Gamma (p / 2)))
            = p * (C + C') * ((U - L) * (32 : ℝ) ^ ((p - 1) / 2) * Real.Gamma ((p - 1) / 2))
                * t ^ ((p - 1) / 2)
              + p * (C + C') * ((32 : ℝ) ^ (p / 2) * Real.Gamma (p / 2) / 2) * t ^ (p / 2) := by
          ring
        rw [e]
        have e' : p * (C + C') * ((U - L) * (32 : ℝ) ^ ((p - 1) / 2) * Real.Gamma ((p - 1) / 2)
              + (32 : ℝ) ^ (p / 2) * Real.Gamma (p / 2) / 2) * t ^ ((p - 1) / 2)
            = p * (C + C') * ((U - L) * (32 : ℝ) ^ ((p - 1) / 2) * Real.Gamma ((p - 1) / 2))
                * t ^ ((p - 1) / 2)
              + p * (C + C') * ((32 : ℝ) ^ (p / 2) * Real.Gamma (p / 2) / 2)
                * t ^ ((p - 1) / 2) := by
          ring
        rw [e']
        exact add_le_add (le_refl _) key

/-- **Truncated-moment bound, fixed lower level** (fixed lower clamp level `L`): there is `C > 0`
(the sum of the forward and reverse two-time defect constants at level `L`) such that for every upper level `U ≥ L`, real `p > 1`,
`x` and `0 < t ≤ 1`,
`𝔼|clamp_{[L,U]}(f(x+t)) − clamp_{[L,U]}(f x)|^p ≤ K(C, U − L, p) t^{(p−1)/2}`. -/
theorem airy1Law_clamp_moment (h : Airy1FddPositive) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U p x t : ℝ), L ≤ U → 1 < p → 0 < t → t ≤ 1 →
      ∫⁻ f, ENNReal.ofReal (|clampTo L U (f (x + t)) - clampTo L U (f x)| ^ p) ∂airy1Law h
        ≤ ENNReal.ofReal (truncMomentConst C (U - L) p * t ^ ((p - 1) / 2)) := by
  obtain ⟨C, hC, hF⟩ := fwdDefectBound_exists L
  obtain ⟨C', hC', hR⟩ := revDefectBound_exists L
  exact ⟨C + C', by linarith, fun U p x t hLU hp ht ht1 =>
    lintegral_clamp_incr_rpow_le h hLU hC.le hC'.le hF hR hp ht ht1⟩

/-! ## Kolmogorov-condition form -/

theorem lintegral_edist_clamp_le_of_lt (h : Airy1FddPositive) {L U C C' p : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C) (hR : RevDefectBound L C')
    (hp : 1 < p) {s u : ℝ} (hsu : s < u) (hsu1 : u - s ≤ 1) :
    ∫⁻ f, edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p ∂airy1Law h
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p) * edist s u ^ ((p - 1) / 2) := by
  have H := lintegral_clamp_incr_rpow_le h hLU hC hC' hF hR hp (x := s) (t := u - s)
    (by linarith) hsu1
  rw [show s + (u - s) = u by ring] at H
  have hK := truncMomentConst_nonneg (add_nonneg hC hC') (by linarith : 0 ≤ U - L) hp
  have hlhs : (fun f : ℝ → ℝ => edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p)
      = fun f => ENNReal.ofReal (|clampTo L U (f u) - clampTo L U (f s)| ^ p) := by
    funext f
    rw [edist_dist, Real.dist_eq, abs_sub_comm,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by linarith)]
  rw [hlhs]
  refine H.trans (le_of_eq ?_)
  rw [edist_dist, Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith),
    ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith), ENNReal.ofReal_mul hK]

/-- **Kolmogorov condition, local form** (`|s − u| ≤ 1`), constant `K(C + C', U − L, p)`. -/
theorem lintegral_edist_clamp_le (h : Airy1FddPositive) {L U C C' p : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C) (hR : RevDefectBound L C')
    (hp : 1 < p) {s u : ℝ} (hsu1 : dist s u ≤ 1) :
    ∫⁻ f, edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p ∂airy1Law h
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p) * edist s u ^ ((p - 1) / 2) := by
  rw [Real.dist_eq] at hsu1
  rcases lt_trichotomy s u with hsu | rfl | hsu
  · exact lintegral_edist_clamp_le_of_lt h hLU hC hC' hF hR hp hsu
      (by rw [abs_sub_comm, abs_of_pos (by linarith)] at hsu1; exact hsu1)
  · simp [ENNReal.zero_rpow_of_pos (show 0 < p by linarith)]
  · have H := lintegral_edist_clamp_le_of_lt h hLU hC hC' hF hR hp hsu
      (by rw [abs_of_pos (by linarith)] at hsu1; exact hsu1)
    have e : (fun f : ℝ → ℝ => edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p)
        = fun f => edist (clampTo L U (f u)) (clampTo L U (f s)) ^ p := by
      funext f; rw [edist_comm]
    rw [e, edist_comm s u]
    exact H

/-- **Kolmogorov condition, global form**: constant `K(C + C', U − L, p) + (U − L)^p`. -/
theorem lintegral_edist_clamp_le_global (h : Airy1FddPositive) {L U C C' p : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C) (hR : RevDefectBound L C')
    (hp : 1 < p) (s u : ℝ) :
    ∫⁻ f, edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p ∂airy1Law h
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p + (U - L) ^ p)
        * edist s u ^ ((p - 1) / 2) := by
  have hK := truncMomentConst_nonneg (add_nonneg hC hC') (by linarith : 0 ≤ U - L) hp
  have hDp : 0 ≤ (U - L) ^ p := Real.rpow_nonneg (by linarith) _
  rcases le_or_gt (dist s u) 1 with h1 | h1
  · refine (lintegral_edist_clamp_le h hLU hC hC' hF hR hp h1).trans ?_
    gcongr
    linarith
  · have hpt : ∀ f : ℝ → ℝ, edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p
        ≤ ENNReal.ofReal ((U - L) ^ p) := fun f => by
      rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by linarith)]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (abs_nonneg _) (abs_clampTo_sub_le hLU _ _) (by linarith))
    have hq : 1 ≤ edist s u ^ ((p - 1) / 2) := by
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by linarith)]
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow h1.le (by linarith))
    calc ∫⁻ f, edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p ∂airy1Law h
        ≤ ∫⁻ _f, ENNReal.ofReal ((U - L) ^ p) ∂airy1Law h := lintegral_mono hpt
      _ = ENNReal.ofReal ((U - L) ^ p) := by simp
      _ ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p + (U - L) ^ p) * 1 := by
          rw [mul_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ _ := by gcongr

/-- **The clamped coordinate process is a Kolmogorov process on `ℝ`** (Mathlib
`IsKolmogorovProcess`, exponents `p` and `q = (p − 1)/2`, constant `K + (U − L)^p`), for every
fixed lower level `L`, upper level `U ≥ L` and real `p > 1`. KC needs `q > 1`, i.e. `p > 3`. -/
theorem isKolmogorovProcess_clamp (h : Airy1FddPositive) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U p : ℝ), L ≤ U → 1 < p →
      IsKolmogorovProcess (fun (s : ℝ) (f : ℝ → ℝ) => clampTo L U (f s)) (airy1Law h)
        p ((p - 1) / 2) (truncMomentConst C (U - L) p + (U - L) ^ p).toNNReal := by
  obtain ⟨C, hC, hF⟩ := fwdDefectBound_exists L
  obtain ⟨C', hC', hR⟩ := revDefectBound_exists L
  refine ⟨C + C', by linarith, fun U p hLU hp => ?_⟩
  refine IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun s => (measurable_clampTo L U).comp (measurable_pi_apply s)) (fun s u => ?_)
    (by linarith) (by linarith)
  exact lintegral_edist_clamp_le_global h hLU hC.le hC'.le hF hR hp s u

/-- **Kolmogorov process on `ℝ≥0`** (the index set of BrownianMotion's covering API). -/
theorem isKolmogorovProcess_clamp_nnreal (h : Airy1FddPositive) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U p : ℝ), L ≤ U → 1 < p →
      IsKolmogorovProcess (fun (s : ℝ≥0) (f : ℝ → ℝ) => clampTo L U (f s)) (airy1Law h)
        p ((p - 1) / 2) (truncMomentConst C (U - L) p + (U - L) ^ p).toNNReal := by
  obtain ⟨C, hC, hF⟩ := fwdDefectBound_exists L
  obtain ⟨C', hC', hR⟩ := revDefectBound_exists L
  refine ⟨C + C', by linarith, fun U p hLU hp => ?_⟩
  refine IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun s => (measurable_clampTo L U).comp (measurable_pi_apply (s : ℝ))) (fun s u => ?_)
    (by linarith) (by linarith)
  exact lintegral_edist_clamp_le_global h hLU hC.le hC'.le hF hR hp (s : ℝ) (u : ℝ)

/-- **Local Kolmogorov process** on any index set `S ⊆ ℝ` of diameter `≤ 1` (e.g. a unit
interval), with the constant `K(C, U − L, p)` that is **linear in the clamp width** (the form
needed for upper boundedness), for abstract defect constants. -/
theorem isKolmogorovProcess_clamp_of_diam_le (h : Airy1FddPositive) {L U C C' p : ℝ}
    (hLU : L ≤ U) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C)
    (hR : RevDefectBound L C') (hp : 1 < p) {S : Set ℝ}
    (hS : ∀ s ∈ S, ∀ u ∈ S, dist s u ≤ 1) :
    IsKolmogorovProcess (fun (s : S) (f : ℝ → ℝ) => clampTo L U (f s)) (airy1Law h)
      p ((p - 1) / 2) (truncMomentConst (C + C') (U - L) p).toNNReal := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun s => (measurable_clampTo L U).comp (measurable_pi_apply (s : ℝ))) (fun s u => ?_)
    (by linarith) (by linarith)
  exact lintegral_edist_clamp_le h hLU hC hC' hF hR hp (hS s s.2 u u.2)

end Airy1Gumbel
