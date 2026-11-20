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

Both theorems are Theorem 1.1 of Le Chen and Fei Pu, *Gumbel Fluctuations of the Maximum of the
Airy₁ Process* (arXiv 2611.23658v1), in its normalized real-length form, under the three named
inputs `Airy1FddPositive`, `GOELeftTail` and `CubicStrongMixing`. Each asserts that an Airy₁
process law and a version with continuous paths on `[0, ∞)` exist, and that for every such law
`μ`, every such version `Y` and every `z`,
`μ{max_{x ∈ [0, T]} (Y x − a_T)/b_T ≤ z} → exp(−e^{−z})` as `T → ∞`.
The two theorems differ only in the process on which the mixing input is assumed: the version
`Y` itself, or the coordinate process of `μ`.
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

end Airy1GumbelAudit.Airy1Gumbel
