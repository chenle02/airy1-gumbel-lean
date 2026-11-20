/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace Airy1Gumbel

/-!
# Newman's covariance inequality from positive quadrant dependence

General probability, independent of the Airy₁ setting. For real random variables
`X, Y` with finite second moments whose bounded monotone transforms are
nonnegatively correlated (positive quadrant dependence, in the test-function
form delivered by association), and for Lipschitz `f, g : ℝ → ℝ`,

`|Cov(f(X), g(Y))| ≤ Lip(f) · Lip(g) · Cov(X, Y)`.

This is [newman:80:normal, Lemma 3] (Newman, CMP 74 (1980), Lemma 3: positive
quadrant dependent `X, Y` with finite variance, `f, g` `C¹` with bounded
derivatives) in the real-valued Lipschitz form of Bulinski (1996), which contains
the `C¹`, bounded-derivative case with the same constant `‖f'‖_∞ ‖g'‖_∞`.

* `cov_nonneg_of_monotone_lipschitz` (step N1): the premise, stated for bounded
  monotone measurable test functions, extends to monotone Lipschitz functions
  of `L²` variables. Proof: truncate the *variable*, `φ ∘ truncAt n`, and pass
  to the limit by dominated convergence in `E[UV] - E[U] E[V]`.
* `newman_lemma3` (step N2): the four-corner trick. `L_f · id ± f` and
  `L_g · id ± g` are monotone and Lipschitz, so N1 applies to the four pairs;
  adding them gives `|Cov(f X, g Y)| ≤ L_f L_g Cov(X, Y)`, with the sharp constant
  and no monotonicity of `f, g`.

**Not formalized:** the complex-valued case of Lemma 3 and Newman's
characteristic-function corollary (his eqs. (20)-(21)). Neither is used.

**The `MemLp` hypotheses are essential.** Mathlib's `covariance` is a Bochner
integral with junk value `0` off `L¹`. Without `MemLp X 2`, `MemLp Y 2` the
inequality is false: `X = Y = 1_{(0,1/2)} ω⁻¹` on Lebesgue `[0,1]` is
nonnegatively self-correlated (`covariance_comp_monotone_nonneg`) but
`Cov(X, X)` is the junk `0` while `Var(min(X, 1)) = 1/4`, so the inequality
without the finite-variance hypothesis is refuted. The regression control
`not_memLp_two_inv_indicator`
below shows that this `X` fails the `MemLp` premise, so `newman_lemma3` cannot be
applied to it.
-/

section Truncation

/-- Truncation of a real number to `[-n, n]`. -/
noncomputable def truncAt (n t : ℝ) : ℝ := max (min t n) (-n)

theorem abs_truncAt_le {n : ℝ} (hn : 0 ≤ n) (t : ℝ) : |truncAt n t| ≤ |t| := by
  unfold truncAt
  rw [abs_le]
  constructor
  · rcases le_total n |t| with h | h
    · exact le_max_of_le_right (neg_le_neg h)
    · exact le_max_of_le_left (le_min (neg_abs_le t) (by linarith [abs_nonneg t]))
  · exact max_le ((min_le_left _ _).trans (le_abs_self t)) (by linarith [abs_nonneg t])

theorem abs_truncAt_le_bound {n : ℝ} (hn : 0 ≤ n) (t : ℝ) : |truncAt n t| ≤ n := by
  unfold truncAt
  rw [abs_le]
  exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩

theorem truncAt_of_abs_le {n t : ℝ} (h : |t| ≤ n) : truncAt n t = t := by
  unfold truncAt
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_left h.1]

theorem monotone_truncAt (n : ℝ) : Monotone (truncAt n) :=
  fun _ _ h => max_le_max (min_le_min h le_rfl) le_rfl

theorem lipschitzWith_truncAt (n : ℝ) : LipschitzWith 1 (truncAt n) :=
  (LipschitzWith.id.min_const n).max_const (-n)

theorem eventually_truncAt_eq (t : ℝ) : ∀ᶠ n : ℕ in atTop, truncAt n t = t :=
  (eventually_ge_atTop ⌈|t|⌉₊).mono fun _ hn =>
    truncAt_of_abs_le ((Nat.le_ceil _).trans (by exact_mod_cast hn))

end Truncation

section Lipschitz

theorem norm_le_add_of_lipschitzWith {φ : ℝ → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (t : ℝ) :
    ‖φ t‖ ≤ ‖φ 0‖ + L * ‖t‖ := by
  have h := hφ.dist_le_mul t 0
  rw [dist_eq_norm, dist_eq_norm, sub_zero] at h
  have := norm_le_norm_add_norm_sub' (φ t) (φ 0)
  linarith [norm_sub_rev (φ t) (φ 0)]

/-- A Lipschitz function of an `L²` variable is in `L²`. -/
theorem memLp_two_comp_lipschitz {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) {φ : ℝ → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) : MemLp (φ ∘ X) 2 P := by
  refine ((memLp_const ‖φ 0‖).add (hX.norm.const_mul (L : ℝ))).of_le
    (hφ.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ ‖φ 0‖ + (L : ℝ) * ‖X ω‖ := by positivity
  simp only [Pi.add_apply, Function.comp_apply]
  rw [Real.norm_of_nonneg h0]
  exact norm_le_add_of_lipschitzWith hφ (X ω)

end Lipschitz

section Newman

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Dominated convergence for a Lipschitz function of a variable truncated at
level `n`: `E[φ(truncAt n X)] → E[φ(X)]`. -/
theorem tendsto_integral_comp_truncAt {X : Ω → ℝ} (hX : MemLp X 2 P) {φ : ℝ → ℝ}
    {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    Tendsto (fun n : ℕ => ∫ ω, φ (truncAt n (X ω)) ∂P) atTop (𝓝 (∫ ω, φ (X ω) ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun ω => ‖φ 0‖ + L * ‖X ω‖)
    (fun n => ((hφ.comp (lipschitzWith_truncAt n)).continuous).comp_aestronglyMeasurable
      hX.aestronglyMeasurable)
    (((memLp_const ‖φ 0‖).add (hX.norm.const_mul (L : ℝ))).integrable one_le_two)
    (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
  · exact (norm_le_add_of_lipschitzWith hφ _).trans (by
      gcongr
      simpa only [Real.norm_eq_abs] using abs_truncAt_le n.cast_nonneg (X ω))
  · exact tendsto_const_nhds.congr' ((eventually_truncAt_eq (X ω)).mono fun n h => by
      simp only [h])

/-- **N1.** Association extended from bounded to Lipschitz monotone functions of
`L²` variables: if bounded monotone measurable transforms of `X` and `Y` are
nonnegatively correlated, so are monotone Lipschitz transforms. -/
theorem cov_nonneg_of_monotone_lipschitz {X Y : Ω → ℝ} (hX : MemLp X 2 P)
    (hY : MemLp Y 2 P)
    (hpqd : ∀ (f₀ g₀ : ℝ → ℝ), Monotone f₀ → Monotone g₀ → Measurable f₀ →
      Measurable g₀ → (∃ B : ℝ, ∀ x, |f₀ x| ≤ B) → (∃ B : ℝ, ∀ x, |g₀ x| ≤ B) →
      0 ≤ covariance (f₀ ∘ X) (g₀ ∘ Y) P)
    {φ ψ : ℝ → ℝ} {Lφ Lψ : ℝ≥0} (hφ : Monotone φ) (hψ : Monotone ψ)
    (hφL : LipschitzWith Lφ φ) (hψL : LipschitzWith Lψ ψ) :
    0 ≤ covariance (φ ∘ X) (ψ ∘ Y) P := by
  -- truncated transforms
  have hφn : ∀ n : ℕ, LipschitzWith (Lφ * 1) (φ ∘ truncAt n) :=
    fun n => hφL.comp (lipschitzWith_truncAt n)
  have hψn : ∀ n : ℕ, LipschitzWith (Lψ * 1) (ψ ∘ truncAt n) :=
    fun n => hψL.comp (lipschitzWith_truncAt n)
  have hbd : ∀ (χ : ℝ → ℝ) (L : ℝ≥0), LipschitzWith L χ → ∀ n : ℕ,
      ∃ B : ℝ, ∀ t, |(χ ∘ truncAt n) t| ≤ B := by
    intro χ L hχ n
    refine ⟨‖χ 0‖ + L * n, fun t => ?_⟩
    rw [← Real.norm_eq_abs]
    refine (norm_le_add_of_lipschitzWith hχ _).trans ?_
    gcongr
    simpa only [Real.norm_eq_abs] using abs_truncAt_le_bound n.cast_nonneg t
  -- nonnegativity at each truncation level
  have hnn : ∀ n : ℕ, 0 ≤ (∫ ω, φ (truncAt n (X ω)) * ψ (truncAt n (Y ω)) ∂P)
      - (∫ ω, φ (truncAt n (X ω)) ∂P) * (∫ ω, ψ (truncAt n (Y ω)) ∂P) := by
    intro n
    have h := hpqd (φ ∘ truncAt n) (ψ ∘ truncAt n) (hφ.comp (monotone_truncAt n))
      (hψ.comp (monotone_truncAt n)) (hφn n).continuous.measurable
      (hψn n).continuous.measurable (hbd φ Lφ hφL n) (hbd ψ Lψ hψL n)
    rw [covariance_eq_sub (memLp_two_comp_lipschitz hX (hφn n))
      (memLp_two_comp_lipschitz hY (hψn n))] at h
    exact h
  -- the product term, by dominated convergence
  have hprod : Tendsto (fun n : ℕ => ∫ ω, φ (truncAt n (X ω)) * ψ (truncAt n (Y ω)) ∂P)
      atTop (𝓝 (∫ ω, φ (X ω) * ψ (Y ω) ∂P)) := by
    have hg₁ : MemLp (fun ω => ‖φ 0‖ + (Lφ : ℝ) * ‖X ω‖) 2 P :=
      (memLp_const ‖φ 0‖).add (hX.norm.const_mul (Lφ : ℝ))
    have hg₂ : MemLp (fun ω => ‖ψ 0‖ + (Lψ : ℝ) * ‖Y ω‖) 2 P :=
      (memLp_const ‖ψ 0‖).add (hY.norm.const_mul (Lψ : ℝ))
    refine tendsto_integral_of_dominated_convergence
      (fun ω => (‖φ 0‖ + Lφ * ‖X ω‖) * (‖ψ 0‖ + Lψ * ‖Y ω‖))
      (fun n => ((hφn n).continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable).mul
        ((hψn n).continuous.comp_aestronglyMeasurable hY.aestronglyMeasurable))
      (hg₁.integrable_mul hg₂) (fun n => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => ?_)
    · rw [norm_mul]
      have h1 : ‖φ (truncAt n (X ω))‖ ≤ ‖φ 0‖ + Lφ * ‖X ω‖ :=
        (norm_le_add_of_lipschitzWith hφL _).trans (by
          gcongr
          simpa only [Real.norm_eq_abs] using abs_truncAt_le n.cast_nonneg (X ω))
      have h2 : ‖ψ (truncAt n (Y ω))‖ ≤ ‖ψ 0‖ + Lψ * ‖Y ω‖ :=
        (norm_le_add_of_lipschitzWith hψL _).trans (by
          gcongr
          simpa only [Real.norm_eq_abs] using abs_truncAt_le n.cast_nonneg (Y ω))
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    · exact tendsto_const_nhds.congr' (((eventually_truncAt_eq (X ω)).and
        (eventually_truncAt_eq (Y ω))).mono fun n h => by simp only [h.1, h.2])
  have hlim := hprod.sub ((tendsto_integral_comp_truncAt hX hφL).mul
    (tendsto_integral_comp_truncAt hY hψL))
  have h0 := ge_of_tendsto hlim (Eventually.of_forall hnn)
  rw [covariance_eq_sub (memLp_two_comp_lipschitz hX hφL) (memLp_two_comp_lipschitz hY hψL)]
  exact h0

/-- `L · id + f` is monotone when `f` is `L`-Lipschitz. -/
theorem monotone_const_mul_add_of_lipschitz {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Monotone (fun t => (L : ℝ) * t + f t) := by
  intro x y hxy
  have h := hf.dist_le_mul y x
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)] at h
  have := neg_abs_le (f y - f x)
  nlinarith

/-- `L · id - f` is monotone when `f` is `L`-Lipschitz. -/
theorem monotone_const_mul_sub_of_lipschitz {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Monotone (fun t => (L : ℝ) * t - f t) := by
  intro x y hxy
  have h := hf.dist_le_mul y x
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)] at h
  have := le_abs_self (f y - f x)
  nlinarith

/-- `L · id ± f` is `2L`-Lipschitz when `f` is `L`-Lipschitz (`s = ±1`). -/
theorem lipschitzWith_const_mul_add_smul {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {s : ℝ} (hs : |s| = 1) : LipschitzWith (L + L) (fun t => (L : ℝ) * t + s * f t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := hf.dist_le_mul x y
  rw [Real.dist_eq] at h ⊢
  rw [Real.dist_eq] at h ⊢
  push_cast
  calc |(L : ℝ) * x + s * f x - ((L : ℝ) * y + s * f y)|
      = |(L : ℝ) * (x - y) + s * (f x - f y)| := by ring_nf
    _ ≤ |(L : ℝ) * (x - y)| + |s * (f x - f y)| := abs_add_le _ _
    _ = (L : ℝ) * |x - y| + |f x - f y| := by
        rw [abs_mul, abs_mul, hs, one_mul, abs_of_nonneg L.coe_nonneg]
    _ ≤ ((L : ℝ) + L) * |x - y| := by linarith

/-- **[newman:80:normal, Lemma 3]**, real-valued Lipschitz form (Bulinski 1996),
**proved**: for `X, Y` with finite second moments whose bounded monotone measurable
transforms are nonnegatively correlated (positive quadrant dependence, in the
test-function form that association delivers), and Lipschitz `f, g : ℝ → ℝ`,
`|Cov(f(X), g(Y))| ≤ Lip(f) · Lip(g) · Cov(X, Y)`.

Source: Newman, CMP 74 (1980) 119-128, Lemma 3: "Suppose X, Y are positive
quadrant dependent with finite variance and f, g are C¹ complex valued functions
on ℝ¹ with f', g' bounded. Then |Cov(f(X), g(Y))| ≤ ‖f'‖_∞ ‖g'‖_∞ Cov(X, Y)";
restated verbatim in [Pu2025], which
notes Bulinski's extension to Lipschitz `f, g`. The premise `hpqd` implies PQD
(take indicator-type monotone `f₀ = 1_{(x,∞)}`, `g₀ = 1_{(y,∞)}`) and follows
from it (Hoeffding/Lehmann), so it is an equivalent form. Only the real-valued
case is formalized; the complex-valued case and eqs. (20)-(21) are not.

Without the finite variance hypothesis the inequality is false (see the
module docstring and `not_memLp_two_inv_indicator`).
The constant `Lf · Lg` is sharp (equality for `f = g = id`), and `f, g` need not be
monotone. -/
theorem newman_lemma3 {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hpqd : ∀ (f₀ g₀ : ℝ → ℝ), Monotone f₀ → Monotone g₀ → Measurable f₀ →
      Measurable g₀ → (∃ B : ℝ, ∀ x, |f₀ x| ≤ B) → (∃ B : ℝ, ∀ x, |g₀ x| ≤ B) →
      0 ≤ covariance (f₀ ∘ X) (g₀ ∘ Y) P)
    {f g : ℝ → ℝ} {Lf Lg : ℝ≥0} (hfL : LipschitzWith Lf f) (hgL : LipschitzWith Lg g) :
    |covariance (f ∘ X) (g ∘ Y) P| ≤ (Lf : ℝ) * (Lg : ℝ) * covariance X Y P := by
  -- the four monotone Lipschitz corners
  have one_abs : |(1 : ℝ)| = 1 := abs_one
  have neg_one_abs : |(-1 : ℝ)| = 1 := by norm_num
  have fp := lipschitzWith_const_mul_add_smul hfL one_abs
  have fm := lipschitzWith_const_mul_add_smul hfL neg_one_abs
  have gp := lipschitzWith_const_mul_add_smul hgL one_abs
  have gm := lipschitzWith_const_mul_add_smul hgL neg_one_abs
  have mfp : Monotone (fun t => (Lf : ℝ) * t + 1 * f t) := by
    simpa only [one_mul] using monotone_const_mul_add_of_lipschitz hfL
  have mfm : Monotone (fun t => (Lf : ℝ) * t + -1 * f t) := by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using monotone_const_mul_sub_of_lipschitz hfL
  have mgp : Monotone (fun t => (Lg : ℝ) * t + 1 * g t) := by
    simpa only [one_mul] using monotone_const_mul_add_of_lipschitz hgL
  have mgm : Monotone (fun t => (Lg : ℝ) * t + -1 * g t) := by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using monotone_const_mul_sub_of_lipschitz hgL
  have h₁ := cov_nonneg_of_monotone_lipschitz hX hY hpqd mfp mgp fp gp
  have h₂ := cov_nonneg_of_monotone_lipschitz hX hY hpqd mfm mgm fm gm
  have h₃ := cov_nonneg_of_monotone_lipschitz hX hY hpqd mfp mgm fp gm
  have h₄ := cov_nonneg_of_monotone_lipschitz hX hY hpqd mfm mgp fm gp
  -- bilinear expansion
  set a : Ω → ℝ := fun ω => (Lf : ℝ) * X ω
  set b : Ω → ℝ := f ∘ X
  set c : Ω → ℝ := fun ω => (Lg : ℝ) * Y ω
  set d : Ω → ℝ := g ∘ Y
  have ha : MemLp a 2 P := hX.const_mul _
  have hb : MemLp b 2 P := memLp_two_comp_lipschitz hX hfL
  have hc : MemLp c 2 P := hY.const_mul _
  have hd : MemLp d 2 P := memLp_two_comp_lipschitz hY hgL
  have e : ∀ s t : ℝ, covariance ((fun x => (Lf : ℝ) * x + s * f x) ∘ X)
      ((fun y => (Lg : ℝ) * y + t * g y) ∘ Y) P
      = covariance a c P + t * covariance a d P + s * covariance b c P
        + s * t * covariance b d P := by
    intro s t
    have hsb : MemLp (fun ω => s * b ω) 2 P := hb.const_mul s
    have htd : MemLp (fun ω => t * d ω) 2 P := hd.const_mul t
    have hU : (fun x => (Lf : ℝ) * x + s * f x) ∘ X = a + fun ω => s * b ω := rfl
    have hV : (fun y => (Lg : ℝ) * y + t * g y) ∘ Y = c + fun ω => t * d ω := rfl
    rw [hU, hV, covariance_add_left ha hsb (hc.add htd), covariance_add_right ha hc htd,
      covariance_add_right hsb hc htd]
    simp only [a, c, covariance_const_mul_left, covariance_const_mul_right]
    ring
  have hac : covariance a c P = (Lf : ℝ) * (Lg : ℝ) * covariance X Y P := by
    simp only [a, c, covariance_const_mul_left, covariance_const_mul_right]
    ring
  rw [e, hac] at h₁ h₂ h₃ h₄
  rw [abs_le]
  constructor <;> nlinarith

/-- Chebyshev's association inequality for a single variable: monotone bounded
measurable functions of the same random variable are nonnegatively correlated.
(It supplies the positive control that `newman_lemma3`'s premise is satisfiable for `X = Y`.) -/
theorem covariance_comp_monotone_nonneg (X : Ω → ℝ) (hX : Measurable X) (f g : ℝ → ℝ)
    (hf : Monotone f) (hg : Monotone g) (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∃ B : ℝ, ∀ x, |f x| ≤ B) (hgb : ∃ B : ℝ, ∀ x, |g x| ≤ B) :
    0 ≤ covariance (f ∘ X) (g ∘ X) P := by
  obtain ⟨Bf, hBf⟩ := hfb
  obtain ⟨Bg, hBg⟩ := hgb
  have hFi : Integrable (f ∘ X) P :=
    Integrable.of_bound (hfm.comp hX).aestronglyMeasurable Bf
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hBf (X ω))
  set m := P[f ∘ X] with hm
  set S : Set ℝ := {x | f x < m}
  obtain ⟨k, hkS, hkSc⟩ : ∃ k : ℝ, (∀ x ∈ S, g x ≤ k) ∧ (∀ y ∉ S, k ≤ g y) := by
    by_cases hS : S.Nonempty
    · have hbdd : BddAbove (g '' S) :=
        ⟨Bg, by rintro _ ⟨x, -, rfl⟩; exact (le_abs_self _).trans (hBg x)⟩
      refine ⟨sSup (g '' S), fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩, fun y hy => ?_⟩
      refine csSup_le (hS.image g) ?_
      rintro _ ⟨x, hx, rfl⟩
      have hx' : f x < m := hx
      have hy' : m ≤ f y := not_lt.mp hy
      exact hg (hf.reflect_lt (hx'.trans_le hy')).le
    · refine ⟨-Bg, fun x hx => (hS ⟨x, hx⟩).elim, fun y _ => ?_⟩
      exact (neg_le_neg (hBg y)).trans (neg_abs_le _)
  have hpt : ∀ ω, 0 ≤ (f (X ω) - m) * (g (X ω) - k) := by
    intro ω
    by_cases h : f (X ω) < m
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hkS (X ω) h])
    · exact mul_nonneg (by linarith [not_lt.mp h]) (by linarith [hkSc (X ω) h])
  have hsplit : covariance (f ∘ X) (g ∘ X) P
      = ∫ ω, (f (X ω) - m) * (g (X ω) - k) ∂P
        + ∫ ω, (f (X ω) - m) * (k - P[g ∘ X]) ∂P := by
    have h1 : Integrable (fun ω => (f (X ω) - m) * (g (X ω) - k)) P := by
      refine Integrable.of_bound ?_ ((Bf + |m|) * (Bg + |k|)) (Eventually.of_forall ?_)
      · exact (((hfm.comp hX).sub_const m).mul ((hgm.comp hX).sub_const k)).aestronglyMeasurable
      · intro ω
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul ((abs_sub _ _).trans (add_le_add (hBf _) le_rfl))
          ((abs_sub _ _).trans (add_le_add (hBg _) le_rfl)) (abs_nonneg _)
          ((abs_nonneg _).trans (hBf 0) |>.trans (le_add_of_nonneg_right (abs_nonneg _)))
    have h2 : Integrable (fun ω => (f (X ω) - m) * (k - P[g ∘ X])) P :=
      (hFi.sub (integrable_const m)).mul_const _
    rw [covariance, ← integral_add h1 h2]
    congr 1
    ext ω
    simp only [Function.comp_apply, hm]
    ring
  have hzero : ∫ ω, (f (X ω) - m) * (k - P[g ∘ X]) ∂P = 0 := by
    rw [integral_mul_const, integral_sub (f := fun a => f (X a)) hFi (integrable_const m)]
    simp [hm]
  rw [hsplit, hzero, add_zero]
  exact integral_nonneg hpt

/-- Positive control: `X = Y` in `L²` satisfies the premise of `newman_lemma3`
(Chebyshev), which then gives the known bound `|Cov(f X, g X)| ≤ L_f L_g Var X`. -/
example (X : Ω → ℝ) (hXm : Measurable X) (hX : MemLp X 2 P) {f g : ℝ → ℝ} {Lf Lg : ℝ≥0}
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g) :
    |covariance (f ∘ X) (g ∘ X) P| ≤ (Lf : ℝ) * Lg * covariance X X P :=
  newman_lemma3 hX hX (fun f₀ g₀ hf₀ hg₀ hfm hgm hfb hgb =>
    covariance_comp_monotone_nonneg X hXm f₀ g₀ hf₀ hg₀ hfm hgm hfb hgb) hf hg

end Newman

section Regression

/-- Regression control for the inequality without finite variance: the
counterexample variable `X₀ = 1_{(0,1/2)} ω⁻¹` of the module docstring, on Lebesgue measure on
`[0,1]`, is not in `L²`, so the `MemLp` premise of `newman_lemma3` blocks it. -/
theorem not_memLp_two_inv_indicator :
    ¬ MemLp ((Set.Ioo (0 : ℝ) (1 / 2)).indicator fun ω : ℝ => ω⁻¹) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  intro hL
  have h := hL.integrable one_le_two
  have h1 : IntegrableOn ((Set.Ioo (0 : ℝ) (1 / 2)).indicator fun ω : ℝ => ω⁻¹)
      (Set.Ioo (0 : ℝ) (1 / 2)) := by
    have := h.integrableOn (s := Set.Ioo (0 : ℝ) (1 / 2))
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.mpr (Set.Ioo_subset_Icc_self.trans
        (Set.Icc_subset_Icc le_rfl (by norm_num)))] at this
    exact this
  have h2 : IntegrableOn (fun ω : ℝ => ω⁻¹) (Set.Ioo (0 : ℝ) (1 / 2)) :=
    h1.congr_fun (fun ω hω => Set.indicator_of_mem hω _) measurableSet_Ioo
  have h3 : IntervalIntegrable (fun ω : ℝ => ω⁻¹) volume 0 (1 / 2) := by
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
  simp at h3

end Regression

end Airy1Gumbel
