/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.ExternalInputs
import Airy1Gumbel.Newman
import Mathlib.Probability.IdentDistrib

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace Airy1Gumbel

/-!
# Mesoscopic external inputs: derived forms and record audits

Derived lemmas for the mesoscopic input records consumed by the later `mesoscopic` discharge,
so that
`ExternalInputs.lean` stays records-only:

* `CubicCovarianceDecay.theta_bound`: the paper's cubic covariance bound,
  `Cov(A₀, A_d) ≤ e^{-θ d³}` for `θ < 4/3` and `d ≥ d₀`,
  from the exact [BasuBusaniFerrari2023, Theorem 1.1] upper bound;
* `CubicCovarianceDecay.memLp`: `A x ∈ L²` for every `x`;
* `PairStationary.cov_shift`: `Cov(A x, A (x + d)) = Cov(A 0, A d)`;
* `ProcessAssociated.pair_pqd`: the premise of `newman_lemma3` for `(A x, A y)`;
* `newman_pair`: Newman's inequality for a pair of process values.

The non-vacuity witnesses (`*_const*`) show that each record is satisfiable by
a constant process, so none is uninhabitable; `Newman.lean` proves the
counterexample showing that Newman's inequality needs the finite-variance hypothesis.
-/

section Derived

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : StationaryRealProcess P}

/-- The paper's cubic covariance bound: for every `θ < 4/3` there is `d₀` with
`Cov(A₀, A_d) ≤ e^{-θ d³}` for `d ≥ d₀`. This is the former statement of the
`CubicCovarianceDecay` record, now derived from BBF's Theorem 1.1:
`c d² - (4/3) d³ ≤ -θ d³` once `d ≥ c / (4/3 - θ)`. -/
theorem CubicCovarianceDecay.theta_bound (h : CubicCovarianceDecay X) :
    ∀ θ : ℝ, θ < 4 / 3 → ∃ d₀ : ℝ, ∀ d : ℝ, d₀ ≤ d →
      covariance (X.A 0) (X.A d) P ≤ Real.exp (-θ * d ^ 3) := by
  intro θ hθ
  have hgap : 0 < 4 / 3 - θ := by linarith
  refine ⟨max 2 (h.c / (4 / 3 - θ)), fun d hd => ?_⟩
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hdc : h.c / (4 / 3 - θ) ≤ d := (le_max_right _ _).trans hd
  refine (h.bound d (by linarith)).trans (Real.exp_le_exp.mpr ?_)
  have h1 : h.c ≤ (4 / 3 - θ) * d := by
    rw [div_le_iff₀ hgap] at hdc
    linarith
  have h2 : h.c * d ^ 2 ≤ (4 / 3 - θ) * d * d ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (sq_nonneg d)
  have e : d ^ 3 = d * d ^ 2 := by ring
  rw [e]
  nlinarith

/-- Every one-point marginal is in `L²`: `X.stat` transfers `memLp_zero`. -/
theorem CubicCovarianceDecay.memLp (h : CubicCovarianceDecay X) (x : ℝ) :
    MemLp (X.A x) 2 P := by
  have hx := X.stat 0 x
  rw [zero_add] at hx
  have hid : IdentDistrib (X.A x) (X.A 0) P P :=
    ⟨(X.A_meas x).aemeasurable, (X.A_meas 0).aemeasurable, hx⟩
  exact hid.memLp_iff.2 h.memLp_zero

/-- Two-point stationarity shifts covariances: `Cov(A x, A (x + d)) = Cov(A 0, A d)`. -/
theorem PairStationary.cov_shift (h : PairStationary X) (x d : ℝ) :
    covariance (X.A x) (X.A (x + d)) P = covariance (X.A 0) (X.A d) P := by
  have hs := h.stat_pair 0 d x
  rw [zero_add, add_comm d x] at hs
  have m₁ : Measurable fun ω => (X.A x ω, X.A (x + d) ω) :=
    (X.A_meas x).prodMk (X.A_meas (x + d))
  have m₀ : Measurable fun ω => (X.A 0 ω, X.A d ω) :=
    (X.A_meas 0).prodMk (X.A_meas d)
  calc covariance (X.A x) (X.A (x + d)) P
      = covariance Prod.fst Prod.snd (P.map fun ω => (X.A x ω, X.A (x + d) ω)) :=
        (covariance_map measurable_fst.aestronglyMeasurable
          measurable_snd.aestronglyMeasurable m₁.aemeasurable).symm
    _ = covariance Prod.fst Prod.snd (P.map fun ω => (X.A 0 ω, X.A d ω)) := by rw [hs]
    _ = covariance (X.A 0) (X.A d) P :=
        covariance_map measurable_fst.aestronglyMeasurable
          measurable_snd.aestronglyMeasurable m₀.aemeasurable

/-- Association of the pair `(A x, A y)` in the test-function form of the premise of
`newman_lemma3`: `ProcessAssociated` at `n = 2`, `s = ![x, y]`. -/
theorem ProcessAssociated.pair_pqd (hA : ProcessAssociated X) (x y : ℝ) :
    ∀ (f₀ g₀ : ℝ → ℝ), Monotone f₀ → Monotone g₀ → Measurable f₀ → Measurable g₀ →
      (∃ B : ℝ, ∀ t, |f₀ t| ≤ B) → (∃ B : ℝ, ∀ t, |g₀ t| ≤ B) →
      0 ≤ covariance (f₀ ∘ X.A x) (g₀ ∘ X.A y) P := by
  rintro f₀ g₀ hf hg hfm hgm ⟨Bf, hBf⟩ ⟨Bg, hBg⟩
  exact hA.assoc 2 ![x, y] (fun v => f₀ (v 0)) (fun v => g₀ (v 1))
    (fun _ _ h => hf (h 0)) (fun _ _ h => hg (h 1))
    (hfm.comp (measurable_pi_apply 0)) (hgm.comp (measurable_pi_apply 1))
    ⟨Bf, fun _ => hBf _⟩ ⟨Bg, fun _ => hBg _⟩

/-- Newman's inequality for two values of an associated process with `L²`
marginals: `|Cov(f(A x), g(A y))| ≤ Lip f · Lip g · Cov(A x, A y)`
(`newman_lemma3` + `ProcessAssociated.pair_pqd`). -/
theorem newman_pair (hA : ProcessAssociated X) (hL2 : ∀ x, MemLp (X.A x) 2 P) (x y : ℝ)
    {f g : ℝ → ℝ} {Lf Lg : ℝ≥0} (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g) :
    |covariance (f ∘ X.A x) (g ∘ X.A y) P|
      ≤ (Lf : ℝ) * (Lg : ℝ) * covariance (X.A x) (X.A y) P :=
  newman_lemma3 (hL2 x) (hL2 y) (hA.pair_pqd x y) hf hg

end Derived

section Audit

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The constant process `A ≡ 0`, the trivial non-vacuity witness. -/
def constZeroProcess : StationaryRealProcess P where
  A := fun _ _ => 0
  A_meas := fun _ => measurable_const
  stat := fun _ _ => rfl

/-- Non-vacuity witness: `PairStationary` is satisfiable (constant process). -/
theorem pairStationary_const : PairStationary (constZeroProcess P) :=
  ⟨fun _ _ _ => rfl⟩

/-- Non-vacuity witness: `CubicCovarianceDecay` is satisfiable (constant process,
covariance `0`). -/
theorem cubicCovarianceDecay_const_nonempty :
    Nonempty (CubicCovarianceDecay (constZeroProcess P)) :=
  ⟨{ memLp_zero := memLp_const 0
     c := 1
     c_pos := one_pos
     bound := fun d _ => by
       simp only [constZeroProcess, covariance_const_left]
       exact (Real.exp_pos _).le }⟩

/-- Non-vacuity witness: `LocalModulusEstimate` is satisfiable (constant process: the
oscillation event is empty). -/
theorem localModulusEstimate_const_nonempty :
    Nonempty (LocalModulusEstimate (constZeroProcess P)) :=
  ⟨{ C₀ := 1
     C₀_pos := one_pos
     c₀ := 1
     c₀_pos := one_pos
     bound := (eventually_ge_atTop 0).mono fun ℓ hℓ c s hs _ => by
       have hempty : {ω : Ω | ∃ t₁ t₂ : ℝ, |t₁ - c| ≤ s ∧ |t₂ - c| ≤ s ∧
           1 * ℓ * Real.sqrt s <
             |(constZeroProcess P).A t₁ ω - (constZeroProcess P).A t₂ ω|} = ∅ := by
         ext ω
         simp only [constZeroProcess, sub_self, abs_zero, Set.mem_ofPred_eq,
           Set.mem_empty_iff_false, iff_false, not_exists, not_and, not_lt]
         intro _ _ _ _
         exact mul_nonneg (by linarith) (Real.sqrt_nonneg s)
       rw [hempty, measureReal_empty]
       exact mul_nonneg zero_le_one (Real.exp_pos _).le }⟩

/-- Non-vacuity witness: `ProcessAssociated` is satisfiable (constant process). -/
theorem processAssociated_const_nonempty :
    Nonempty (ProcessAssociated (constZeroProcess P)) :=
  ⟨{ assoc := fun _ _ f _ _ _ _ _ _ _ => by
       simp only [constZeroProcess]
       rw [covariance_const_left] }⟩

end Audit

end Airy1Gumbel
