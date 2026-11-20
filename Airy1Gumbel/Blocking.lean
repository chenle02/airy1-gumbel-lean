/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

open Filter
open scoped Topology BigOperators

namespace Airy1Gumbel

/-- A two-scale approximation proves convergence without assuming that the
inner sequence converges for any fixed outer parameter. -/
theorem tendsto_of_two_scale
    {f center error : ℕ → ℝ} {L : ℝ}
    (hcenter : Tendsto center atTop (𝓝 L))
    (herror : Tendsto error atTop (𝓝 0))
    (happrox : ∀ᶠ k : ℕ in atTop, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, |f n - center k| ≤ error k + ε) :
    Tendsto f atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hc : ∀ᶠ k : ℕ in atTop, |center k - L| < ε / 3 := by
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.mp hcenter) (ε / 3) hε3
  have he : ∀ᶠ k : ℕ in atTop, |error k| < ε / 3 := by
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.mp herror) (ε / 3) hε3
  obtain ⟨k, hkcenter, hkerror, hkapprox⟩ := (hc.and (he.and happrox)).exists
  filter_upwards [hkapprox (ε / 3) hε3] with n hn
  rw [Real.dist_eq]
  have htriangle : |f n - L| ≤ |f n - center k| + |center k - L| := by
    calc
      |f n - L| = |(f n - center k) + (center k - L)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have herr : error k ≤ |error k| := le_abs_self _
  linarith

/-- The final blocking step, conditional on the event-level
approximation budget supplied by the probabilistic estimates. This does not
assert that those estimates hold for the Airy₁ process. -/
theorem gumbel_of_two_scale
    {f error : ℕ → ℝ} (τ : ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (happrox : ∀ᶠ k : ℕ in atTop, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, |f n - (1 - τ / (k : ℝ)) ^ k| ≤ error k + ε) :
    Tendsto f atTop (𝓝 (Real.exp (-τ))) := by
  apply tendsto_of_two_scale (center := fun k : ℕ => (1 - τ / (k : ℝ)) ^ k)
  · simpa [sub_eq_add_neg, neg_div] using Real.tendsto_one_add_div_pow_exp (-τ)
  · exact herror
  · exact happrox

/-- Product perturbation for core-event probabilities; all factors lie in [0,1]. -/
theorem abs_prod_sub_prod_le_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hg : ∀ i, 0 ≤ g i ∧ g i ≤ 1) :
    |(∏ i ∈ s, f i) - (∏ i ∈ s, g i)| ≤ ∑ i ∈ s, |f i - g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hprod0 : 0 ≤ ∏ j ∈ s, g j := Finset.prod_nonneg (fun j _ => (hg j).1)
    have hprod1 : ∏ j ∈ s, g j ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ => (hg j).1) (fun j _ => (hg j).2)
    have hfi : |f i| ≤ 1 := by rw [abs_of_nonneg (hf i).1]; exact (hf i).2
    have hgp : |∏ j ∈ s, g j| ≤ 1 := by rw [abs_of_nonneg hprod0]; exact hprod1
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      |f i * (∏ j ∈ s, f j) - g i * (∏ j ∈ s, g j)| =
          |f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) +
            (f i - g i) * (∏ j ∈ s, g j)| := by congr 1; ring
      _ ≤ |f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j)| +
          |(f i - g i) * (∏ j ∈ s, g j)| := abs_add_le _ _
      _ = |f i| * |(∏ j ∈ s, f j) - ∏ j ∈ s, g j| +
          |f i - g i| * |∏ j ∈ s, g j| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (∑ j ∈ s, |f j - g j|) + |f i - g i| * 1 := by
        exact add_le_add (mul_le_mul hfi ih (abs_nonneg _) (by norm_num))
          (mul_le_mul_of_nonneg_left hgp (abs_nonneg _))
      _ = |f i - g i| + ∑ j ∈ s, |f j - g j| := by ring

/-- Conditional blocking theorem from individual core bounds and a vanishing
product-approximation error. Neither a fixed-k core limit nor convergence of
its Bonferroni remainder is assumed. The Airy-specific hypotheses are supplied by the
`Airy1BlockExtremes` bundle (`GumbelLimit.lean`) and discharged downstream. -/
theorem gumbel_of_core_bounds
    (f : ℕ → ℝ) (core : ℕ → ℕ → ℕ → ℝ) (error : ℕ → ℝ)
    (τ : ℝ) (hτ : 0 < τ)
    (hcore01 : ∀ n k i, 0 ≤ core n k i ∧ core n k i ≤ 1)
    (herror : Tendsto error atTop (𝓝 0))
    (hcore : ∀ᶠ k : ℕ in atTop, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.range k,
        |core n k i - (1 - τ / (k : ℝ))| ≤ error k / (k : ℝ) + ε)
    (hproduct : ∀ᶠ k : ℕ in atTop, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        |f n - ∏ i ∈ Finset.range k, core n k i| ≤ ε) :
    Tendsto f atTop (𝓝 (Real.exp (-τ))) := by
  apply gumbel_of_two_scale τ herror
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ k : ℕ in atTop, τ ≤ (k : ℝ) ∧ 0 < (k : ℝ) :=
    (hcast.eventually (eventually_ge_atTop τ)).and
      (hcast.eventually (eventually_gt_atTop 0))
  filter_upwards [hlarge, hcore, hproduct] with k hk hkc hkp
  intro ε hε
  let η : ℝ := ε / (2 * ((k : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hb : 0 ≤ 1 - τ / (k : ℝ) ∧ 1 - τ / (k : ℝ) ≤ 1 := by
    constructor
    · exact sub_nonneg.mpr ((div_le_one hk.2).mpr hk.1)
    · have hdiv : 0 ≤ τ / (k : ℝ) := div_nonneg hτ.le hk.2.le
      linarith
  filter_upwards [hkc η hη, hkp η hη] with n hncore hnproduct
  have hperturb :
      |(∏ i ∈ Finset.range k, core n k i) - (1 - τ / (k : ℝ)) ^ k| ≤
        ∑ i ∈ Finset.range k, |core n k i - (1 - τ / (k : ℝ))| := by
    simpa using abs_prod_sub_prod_le_sum (Finset.range k) (core n k)
      (fun _ => 1 - τ / (k : ℝ)) (hcore01 n k) (fun _ => hb)
  have hsum : (∑ i ∈ Finset.range k,
      |core n k i - (1 - τ / (k : ℝ))|) ≤
      (k : ℝ) * (error k / (k : ℝ) + η) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range k, (error k / (k : ℝ) + η) :=
        Finset.sum_le_sum (fun i hi => hncore i hi)
      _ = _ := by simp [mul_add]
  have htriangle :
      |f n - (1 - τ / (k : ℝ)) ^ k| ≤
      |f n - ∏ i ∈ Finset.range k, core n k i| +
      |(∏ i ∈ Finset.range k, core n k i) - (1 - τ / (k : ℝ)) ^ k| := by
    calc
      _ = |(f n - ∏ i ∈ Finset.range k, core n k i) +
          ((∏ i ∈ Finset.range k, core n k i) - (1 - τ / (k : ℝ)) ^ k)| := by
        congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hcancel : (k : ℝ) * (error k / (k : ℝ)) = error k := by
    field_simp [ne_of_gt hk.2]
  have hηeq : ((k : ℝ) + 1) * η = ε / 2 := by
    dsimp [η]
    field_simp [show (k : ℝ) + 1 ≠ 0 by linarith]
  nlinarith

end Airy1Gumbel
