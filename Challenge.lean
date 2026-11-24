/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import ChallengeDefs.Airy1Gumbel.Process

/-!
# Comparator challenge: the Gumbel limit of the normalized Airy₁ maximum

The trusted statements of the comparator check. They use Mathlib and the definitions modules
`ChallengeDefs.Airy1Gumbel.Analytic` and `ChallengeDefs.Airy1Gumbel.Process` only (both import
Mathlib only and contain no proof); `Solution.lean` proves each statement from the package.

The first two theorems state the conclusion of Theorem 1.1 of Le Chen and Fei Pu, *Gumbel
Fluctuations of the Maximum of the Airy₁ Process* (arXiv 2611.23658v1), in its normalized
real-length form, under the three named inputs `Airy1FddPositive`, `GOELeftTail` and
`CubicStrongMixing`. The inputs are assumptions, so the comparator check verifies the headline
under these inputs; it does not verify the inputs themselves.

Since v0.9.0 two more statements are compared. `airy1FddPositive_of_goeLeftTail` states that the
first input follows from the second: under `GOELeftTail` alone, the Airy₁ finite-dimensional
laws exist. `gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_input` is the first
theorem without the hypothesis `Airy1FddPositive`, so its conclusion holds under `GOELeftTail`
and `CubicStrongMixing` only. Neither proves `GOELeftTail` or `CubicStrongMixing`.

Since v0.10.0 three more statements are compared. `goeLeftTail_holds` states the second input,
`GOELeftTail`, with no hypothesis, and `airy1FddPositive_holds` states the first input,
`Airy1FddPositive`, with no hypothesis.
`gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_goe_input` is the first theorem
without the hypotheses `Airy1FddPositive` and `GOELeftTail`, so its conclusion holds under
`CubicStrongMixing` only. None of them proves `CubicStrongMixing`.

Both theorems assert, from `Airy1FddPositive` and `GOELeftTail` alone, that an Airy₁ process
law exists. They differ in where the mixing input enters.

* In `gumbel_limit_continuum_real_normalized_airy1_final₂`, the first two inputs also give, for
  every Airy₁ law `μ`, a version with continuous paths on `[0, ∞)`. The mixing input is assumed
  on a continuous version `Y`, and the limit
  `μ{max_{x ∈ [0, T]} (Y x − a_T)/b_T ≤ z} → exp(−e^{−z})` as `T → ∞` is asserted for every
  continuous version `Y` on which `CubicStrongMixing` holds and every real `z`.
* In `gumbel_limit_continuum_real_normalized_airy1_final₂_coord`, the mixing input is a premise
  on each law: it is assumed on the coordinate process of `μ`, and it comes before both the
  existence of a continuous version and the limit. For every Airy₁ law `μ` whose coordinate
  process satisfies `CubicStrongMixing`, a continuous version exists and the limit holds for
  every continuous version `Y` and every real `z`.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Airy1GumbelAudit.Airy1Gumbel

open Airy1GumbelSpec

/-- **Theorem 1.1 (arXiv 2611.23658v1), mixing assumed on the continuous version.** Under
`Airy1FddPositive` and `GOELeftTail`, an Airy₁ process law exists; for every Airy₁ law `μ` a
version `Y` with paths continuous on `[0, ∞)` exists; and for every such version on which
`CubicStrongMixing` holds, and every real `z`,
`μ{f : (Y x f − a_T)/b_T ≤ z for all x ∈ [0, T]} → exp(−e^{−z})` as `T → ∞`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_final₂
    (h : Airy1FddPositive) (hT : GOELeftTail) :
    (∃ μ : Measure (ℝ → ℝ), IsAiry1Law μ) ∧
      ∀ μ : Measure (ℝ → ℝ), IsAiry1Law μ →
        (∃ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y) ∧
          ∀ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y → CubicStrongMixing μ Y →
            ∀ z : ℝ, Tendsto (fun T : ℝ => μ.real {f | ∀ x ∈ Icc (0 : ℝ) T,
              (Y x f - gumbelAR T) / gumbelBR T ≤ z})
              atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  sorry

/-- **Theorem 1.1 (arXiv 2611.23658v1), mixing assumed on the coordinate process.** Under
`Airy1FddPositive` and `GOELeftTail`, an Airy₁ process law exists; for every Airy₁ law `μ` whose
coordinate process `x ↦ (f ↦ f x)` satisfies `CubicStrongMixing`, a version `Y` with paths
continuous on `[0, ∞)` exists, and for every such version and every real `z`,
`μ{f : (Y x f − a_T)/b_T ≤ z for all x ∈ [0, T]} → exp(−e^{−z})` as `T → ∞`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_final₂_coord
    (h : Airy1FddPositive) (hT : GOELeftTail) :
    (∃ μ : Measure (ℝ → ℝ), IsAiry1Law μ) ∧
      ∀ μ : Measure (ℝ → ℝ), IsAiry1Law μ → CubicStrongMixing μ (fun x f => f x) →
        (∃ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y) ∧
          ∀ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y →
            ∀ z : ℝ, Tendsto (fun T : ℝ => μ.real {f | ∀ x ∈ Icc (0 : ℝ) T,
              (Y x f - gumbelAR T) / gumbelBR T ≤ z})
              atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  sorry

/-- **The first input from the second (since v0.9.0).** Under `GOELeftTail`, for every finite
time set `I` there is a probability measure on `I → ℝ` whose distribution function is
`airy1FinCdf I`: the Airy₁ finite-dimensional laws exist. -/
theorem airy1FddPositive_of_goeLeftTail (hT : GOELeftTail) : Airy1FddPositive := by
  sorry

/-- **Theorem 1.1 (arXiv 2611.23658v1) under `GOELeftTail` and `CubicStrongMixing` only (since
v0.9.0).** Under `GOELeftTail` alone, an Airy₁ process law exists; for every Airy₁ law `μ` a
version `Y` with paths continuous on `[0, ∞)` exists; and for every such version on which
`CubicStrongMixing` holds, and every real `z`,
`μ{f : (Y x f − a_T)/b_T ≤ z for all x ∈ [0, T]} → exp(−e^{−z})` as `T → ∞`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_input (hT : GOELeftTail) :
    (∃ μ : Measure (ℝ → ℝ), IsAiry1Law μ) ∧
      ∀ μ : Measure (ℝ → ℝ), IsAiry1Law μ →
        (∃ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y) ∧
          ∀ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y → CubicStrongMixing μ Y →
            ∀ z : ℝ, Tendsto (fun T : ℝ => μ.real {f | ∀ x ∈ Icc (0 : ℝ) T,
              (Y x f - gumbelAR T) / gumbelBR T ≤ z})
              atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  sorry

/-- **The second input, proved (since v0.10.0).** There are `C, c > 0` with
`airy1FinCdf {0} (fun _ => −M) ≤ C e^{−cM³}` for every `M ≥ 0`. -/
theorem goeLeftTail_holds : GOELeftTail := by
  sorry

/-- **The first input, proved (since v0.10.0).** For every finite time set `I` there is a
probability measure on `I → ℝ` whose distribution function is `airy1FinCdf I`: the Airy₁
finite-dimensional laws exist. -/
theorem airy1FddPositive_holds : Airy1FddPositive := by
  sorry

/-- **Theorem 1.1 (arXiv 2611.23658v1) under `CubicStrongMixing` only (since v0.10.0).** An Airy₁
process law exists; for every Airy₁ law `μ` a version `Y` with paths continuous on `[0, ∞)`
exists; and for every such version on which `CubicStrongMixing` holds, and every real `z`,
`μ{f : (Y x f − a_T)/b_T ≤ z for all x ∈ [0, T]} → exp(−e^{−z})` as `T → ∞`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_goe_input :
    (∃ μ : Measure (ℝ → ℝ), IsAiry1Law μ) ∧
      ∀ μ : Measure (ℝ → ℝ), IsAiry1Law μ →
        (∃ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y) ∧
          ∀ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y → CubicStrongMixing μ Y →
            ∀ z : ℝ, Tendsto (fun T : ℝ => μ.real {f | ∀ x ∈ Icc (0 : ℝ) T,
              (Y x f - gumbelAR T) / gumbelBR T ≤ z})
              atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  sorry

end Airy1GumbelAudit.Airy1Gumbel
