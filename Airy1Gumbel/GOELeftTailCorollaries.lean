/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.FddFromTasep
import Airy1Gumbel.GOELeftTailDischarge
import Airy1Gumbel.FinalHeadlineTP
import Airy1Gumbel.FddFromTasepCorollaries
import Airy1Gumbel.BlockLawUnconditional
import Airy1Gumbel.TwoIntervalLaw
import Airy1Gumbel.BlockModulus
import Airy1Gumbel.TailSensitiveNewman
import Airy1Gumbel.MesoscopicStandalone
import Airy1Gumbel.FerrariLiuRoute

/-!
# Airy₁ corollaries using the proved GOE left tail

The flat TASEP limit supplies the finite-dimensional law after the GOE left
tail is proved. The corollaries instantiate those two records in the
paper-numbered results.
-/

open Asymptotics Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators

namespace Airy1Gumbel

/-- The Airy₁ finite-dimensional laws follow from flat TASEP and the cubic GOE left tail. -/
theorem airy1FddPositive_holds : Airy1FddPositive :=
  airy1FddPositive_of_goeLeftTail goeLeftTail_holds

/-- Corollary of `gumbel_limit_continuum_real_normalized_airy1_final₂` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. Kept input records are `CubicStrongMixing`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_goe_input
    (M : CubicStrongMixing (airy1SRP airy1FddPositive_holds goeLeftTail_holds)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law airy1FddPositive_holds).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR airy1FddPositive_holds x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  gumbel_limit_continuum_real_normalized_airy1_final₂ airy1FddPositive_holds goeLeftTail_holds M z

/-- Corollary of `gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_input` using
`goeLeftTail_holds` and the finite-dimensional law
`airy1FddPositive_of_goeLeftTail goeLeftTail_holds`. The mixing hypothesis is `CubicStrongMixing`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_input_no_goe_input
    (M : CubicStrongMixing (airy1SRP (airy1FddPositive_of_goeLeftTail goeLeftTail_holds) goeLeftTail_holds)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail goeLeftTail_holds)).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR (airy1FddPositive_of_goeLeftTail goeLeftTail_holds) x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_input goeLeftTail_holds M z

/-- Corollary of `airy1Law_sup_le_eq_fredholmDet'` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. All input records are discharged. -/
theorem airy1Law_sup_le_eq_fredholmDet'_no_fdd_goe_input {x M T : ℝ}
    (hx : 0 ≤ x) (hT1 : 1 ≤ T) (hM : 0 < M) :
    (airy1Law airy1FddPositive_holds).real {f | ∀ t ∈ Icc x (x + T), airy1ContR airy1FddPositive_holds t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1 :=
  airy1Law_sup_le_eq_fredholmDet' airy1FddPositive_holds goeLeftTail_holds hx hT1 hM

/-- Corollary of `qrUnitBlockLaw_airy1'` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. All input records are discharged. -/
theorem qrUnitBlockLaw_airy1'_no_fdd_goe_input :
    QRUnitBlockLaw (airy1BlockMax airy1FddPositive_holds) (airy1Law airy1FddPositive_holds) :=
  qrUnitBlockLaw_airy1' airy1FddPositive_holds goeLeftTail_holds

/-- Corollary of `qrTwoBlockLaw_airy1'` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. All input records are discharged. -/
theorem qrTwoBlockLaw_airy1'_no_fdd_goe_input :
    QRTwoBlockLaw (airy1BlockMax airy1FddPositive_holds) (airy1Law airy1FddPositive_holds) :=
  qrTwoBlockLaw_airy1' airy1FddPositive_holds goeLeftTail_holds

/-- Corollary of `airy1Law_two_blocks_le_eq_fredholmDet` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. All input records are discharged. -/
theorem airy1Law_two_blocks_le_eq_fredholmDet_no_fdd_goe_input
    {x M r a : ℝ} (hx : 0 ≤ x) (hr : 0 < r) (hM : 0 < M) (ha : r + 3 ≤ a) :
    (airy1Law airy1FddPositive_holds).real {f | (∀ t ∈ Icc x (x + 1), airy1ContR airy1FddPositive_holds t f ≤ M) ∧
        ∀ t ∈ Icc (x + 1 + r) (x + 1 + r + 1), airy1ContR airy1FddPositive_holds t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (HilbertSchmidt.kernelOperator (AiryTwoInt.memLp_kcupKerT hr hM ha)) 1 :=
  airy1Law_two_blocks_le_eq_fredholmDet airy1FddPositive_holds goeLeftTail_holds hx hr hM ha

/-- Corollary of `qrTwoIntervalLaw_airy1` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. All input records are discharged. -/
theorem qrTwoIntervalLaw_airy1_no_fdd_goe_input :
    QRTwoIntervalLaw (airy1BlockMax airy1FddPositive_holds) (airy1Law airy1FddPositive_holds) :=
  qrTwoIntervalLaw_airy1 airy1FddPositive_holds goeLeftTail_holds

/-- Corollary of `airy1Law_two_blocks_le_eq_fredholmDet_of_length` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. All input records are discharged. -/
theorem airy1Law_two_blocks_le_eq_fredholmDet_of_length_no_fdd_goe_input
    {x M T r a : ℝ} (hx : 0 ≤ x) (hT : 0 < T) (hr : 0 < r)
    (hM : 0 < M) (ha : 2 * T + r + 1 ≤ a) :
    (airy1Law airy1FddPositive_holds).real {f | (∀ t ∈ Icc x (x + T), airy1ContR airy1FddPositive_holds t f ≤ M) ∧
        ∀ t ∈ Icc (x + T + r) (x + T + r + T), airy1ContR airy1FddPositive_holds t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (HilbertSchmidt.kernelOperator (AiryFdd.memLp_kcupKerT_of_length hT hr hM ha)) 1 :=
  airy1Law_two_blocks_le_eq_fredholmDet_of_length airy1FddPositive_holds goeLeftTail_holds hx hT hr hM ha

/-- Corollary of `block_modulus_airy1` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. Kept input records are `NonnegativeWindowModulusEstimate`. -/
theorem block_modulus_airy1_no_fdd_goe_input
    (L : NonnegativeWindowModulusEstimate (airy1Law airy1FddPositive_holds) (airy1SRP airy1FddPositive_holds goeLeftTail_holds).A) :
    ∃ C c h₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < h₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ h₀ →
        (airy1Law airy1FddPositive_holds).real
          {f | ∃ x y : ℝ, x ∈ Icc (0 : ℝ) 1 ∧ y ∈ Icc (0 : ℝ) 1 ∧
            |x - y| ≤ 2 * δ ∧ 1 < |airy1ContR airy1FddPositive_holds x f - airy1ContR airy1FddPositive_holds y f|}
          ≤ C * δ⁻¹ * Real.exp (-c * δ ^ (-(1 / 2 : ℝ))) :=
  block_modulus_airy1 airy1FddPositive_holds goeLeftTail_holds L

/-- Corollary of `tail_sensitive_newman_airy1` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. Kept input records are `ProcessAssociated`. -/
theorem tail_sensitive_newman_airy1_no_fdd_goe_input
    (As : ProcessAssociated (airy1SRP airy1FddPositive_holds goeLeftTail_holds)) :
    ∃ C u₀ : ℝ, 0 < C ∧ ∀ u d : ℝ, u₀ ≤ u → 0 ≤ d →
      (airy1Law airy1FddPositive_holds).real {f | u < airy1ContR airy1FddPositive_holds 0 f ∧ u < airy1ContR airy1FddPositive_holds d f}
        ≤ C * ((airy1Law airy1FddPositive_holds).real {f | u < airy1ContR airy1FddPositive_holds 0 f}) ^ 2 +
          C * u * covariance (airy1ContR airy1FddPositive_holds 0) (airy1ContR airy1FddPositive_holds d) (airy1Law airy1FddPositive_holds) :=
  tail_sensitive_newman_airy1 airy1FddPositive_holds goeLeftTail_holds As

/-- Corollary of `mesoscopic_sum_airy1` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. Kept input records are `NonnegativeWindowModulusEstimate`, `ProcessAssociated`, `CubicCovarianceDecay`. -/
theorem mesoscopic_sum_airy1_no_fdd_goe_input
    (L : NonnegativeWindowModulusEstimate (airy1Law airy1FddPositive_holds) (airy1SRP airy1FddPositive_holds goeLeftTail_holds).A)
    (As : ProcessAssociated (airy1SRP airy1FddPositive_holds goeLeftTail_holds))
    (Cov : CubicCovarianceDecay (airy1SRP airy1FddPositive_holds goeLeftTail_holds))
    (χ : ℝ) (hχ : (1 / 2 : ℝ) ^ (1 / 3 : ℝ) < χ) (hχ₁ : χ < 1)
    (R : ℝ → ℝ) (hR : R =O[atTop] fun M => Real.sqrt M) :
    (fun M : ℝ =>
      ∑ j ∈ Finset.Icc ⌈χ * Real.sqrt (2 * M)⌉₊ ⌊R M⌋₊,
        (airy1Law airy1FddPositive_holds).real {f | M < airy1BlockMax airy1FddPositive_holds 0 f ∧ M < airy1BlockMax airy1FddPositive_holds j f})
      =o[atTop] AiryConj.rhoM :=
  mesoscopic_sum_airy1 airy1FddPositive_holds goeLeftTail_holds L As Cov χ hχ hχ₁ R hR

/-- Corollary of `one_point_tail_minus_one_airy1` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. All input records are discharged. -/
theorem one_point_tail_minus_one_airy1_no_fdd_goe_input :
    ∃ B E U : ℝ, 0 < B ∧ 0 < E ∧ 0 < U ∧
      ∀ M : ℝ, U ≤ M →
        (airy1Law airy1FddPositive_holds).real {f | M - 1 < airy1ContR airy1FddPositive_holds 0 f} ≤
          B * M ^ (-3 / 4 : ℝ) *
            Real.exp (-AiryConj.kappaC * M ^ (3 / 2 : ℝ) + E * Real.sqrt M) :=
  one_point_tail_minus_one_airy1 airy1FddPositive_holds goeLeftTail_holds

/-- Corollary of `gumbel_limit_continuum_airy1_ferrariLiu` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. Kept input records are `FerrariLiuPersistence`. -/
theorem gumbel_limit_continuum_airy1_ferrariLiu_no_fdd_goe_input
    (FL : FerrariLiuPersistence (airy1Law airy1FddPositive_holds) (airy1SRP airy1FddPositive_holds goeLeftTail_holds).A) (z : ℝ) :
    Tendsto (fun N : ℕ => (airy1Law airy1FddPositive_holds).real
        {f | ∀ x ∈ Icc (0 : ℝ) N, airy1ContR airy1FddPositive_holds x f ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  gumbel_limit_continuum_airy1_ferrariLiu airy1FddPositive_holds goeLeftTail_holds FL z

/-- Corollary of `block_pair_grid_cover_airy1_no_fdd_input` using
`goeLeftTail_holds` and the finite-dimensional law
`airy1FddPositive_of_goeLeftTail goeLeftTail_holds`. No other input. -/
theorem block_pair_grid_cover_airy1_no_fdd_input_no_goe_input
    (j n : ℕ) (hn : 0 < n)
    (δ M : ℝ) (hmesh : 1 / (n : ℝ) ≤ 2 * δ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail goeLeftTail_holds)).real {f | M < airy1BlockMax (airy1FddPositive_of_goeLeftTail goeLeftTail_holds) 0 f ∧ M < airy1BlockMax (airy1FddPositive_of_goeLeftTail goeLeftTail_holds) j f} ≤
      (airy1Law (airy1FddPositive_of_goeLeftTail goeLeftTail_holds)).real (unit_block_oscillation_event (airy1FddPositive_of_goeLeftTail goeLeftTail_holds) 0 δ) +
      (airy1Law (airy1FddPositive_of_goeLeftTail goeLeftTail_holds)).real (unit_block_oscillation_event (airy1FddPositive_of_goeLeftTail goeLeftTail_holds) j δ) +
      ∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
        (airy1Law (airy1FddPositive_of_goeLeftTail goeLeftTail_holds)).real {f | M - 1 < airy1ContR (airy1FddPositive_of_goeLeftTail goeLeftTail_holds) (gridPt 0 n k) f ∧
          M - 1 < airy1ContR (airy1FddPositive_of_goeLeftTail goeLeftTail_holds) (gridPt j n k') f} :=
  block_pair_grid_cover_airy1_no_fdd_input goeLeftTail_holds j n hn δ M hmesh

/-- Corollary of `airy1Law_interval_tail_sub_traceLead_isLittleO` with `Airy1FddPositive` and `GOELeftTail` discharged
by `airy1FddPositive_holds` and `goeLeftTail_holds`. No other input. -/
theorem airy1Law_interval_tail_sub_traceLead_isLittleO_no_fdd_goe_input
    (T : ℝ) (hT : 0 < T) :
    (fun M : ℝ => (airy1Law airy1FddPositive_holds).real {f | ∃ t ∈ Icc (0 : ℝ) T, M < airy1ContR airy1FddPositive_holds t f}
      - AiryConj.traceLead M T) =o[atTop] (fun M => AiryConj.rhoM M / M) :=
  airy1Law_interval_tail_sub_traceLead_isLittleO airy1FddPositive_holds goeLeftTail_holds T hT

end Airy1Gumbel
