/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.TruncatedMoment
import Airy1Gumbel.BlockLawUnconditional

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

/-!
# The high-level upcrossing tail as a theorem

The record `HighLevelUpcrossingTail` (`ExternalInputs.lean`) is **discharged** for the concrete
continuous Airy₁ process `airy1SRP h hT` (`Ã = airy1ContR h` under `airy1Law h`), conditional
only on `Airy1FddPositive` and `GOELeftTail`:

* `airy1SRP_upcrossing_le`: for every `x : ℝ`, `0 < h ≤ 1`, `a ≥ a₀` and `η > 0`,
  `ℙ(Ã x ≤ a, a + η < Ã(x+h)) ≤ C e^{−η²/(8h)}`;
* `highLevelUpcrossingTail_airy1SRP`: the record, with `a₀ = 0`, `C` the constant of the contrib
  two-time defect bound (`AiryFdd.airy1FinCdf_twoTime_defect 0`, via `fwdDefectBound_exists 0`),
  `k = 0`,
  `c₁ = 1/8`;
* `gumbel_limit_continuum_real_normalized_airy1_of_QR₉`: the `_of_QR₈` headline with `U`
  discharged.

Route: the event is a.s. equal (two times `x`, `x + h`; `airy1ContR_ae_eq` holds at every real
time, including `x < 0`, where `Ã` is the raw coordinate) to the coordinate event
`{f x ≤ a ∧ a + η < f (x + h)}`, whose `airy1Law`-probability is the forward two-time defect
`G(a) − F(a, a + η)` (`airy1Law_fwd_le`, built from `airy1Law_fdd` and the contrib two-time defect
bound).
-/

namespace Airy1Gumbel

/-- The continuous-version upcrossing event equals the coordinate event a.s. -/
theorem airy1ContR_upcrossing_ae_eq (h : Airy1FddPositive) (hT : GOELeftTail) (x t a b : ℝ) :
    {f : ℝ → ℝ | airy1ContR h x f ≤ a ∧ b < airy1ContR h (x + t) f}
      =ᵐ[airy1Law h] {f : ℝ → ℝ | f x ≤ a ∧ b < f (x + t)} := by
  filter_upwards [airy1ContR_ae_eq h hT x, airy1ContR_ae_eq h hT (x + t)] with f h1 h2
  rw [h1, h2]

/-- **Forward upcrossing bound on `Ã`**: with `C` from `FwdDefectBound L C`, for every real
`x`, `0 < t ≤ 1`, `L ≤ a ≤ b`: `ℙ(Ã x ≤ a, b < Ã(x+t)) ≤ C e^{−(b−a)²/(8t)}`. -/
theorem airy1SRP_upcrossing_le (h : Airy1FddPositive) (hT : GOELeftTail) {L C : ℝ}
    (hC : 0 < C) (hF : FwdDefectBound L C) {x t a b : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (ha : L ≤ a) (hab : a ≤ b) :
    (airy1Law h).real {f : ℝ → ℝ | (airy1SRP h hT).A x f ≤ a ∧ b < (airy1SRP h hT).A (x + t) f}
      ≤ C * Real.exp (-(b - a) ^ 2 / (8 * t)) := by
  change (airy1Law h).real {f : ℝ → ℝ | airy1ContR h x f ≤ a ∧ b < airy1ContR h (x + t) f} ≤ _
  rw [measureReal_congr (airy1ContR_upcrossing_ae_eq h hT x t a b)]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (airy1Law_fwd_le h hF ht ht1 ha hab)

/-- **`HighLevelUpcrossingTail` on the concrete Airy₁ process is a theorem**,
conditional only on `Airy1FddPositive` and `GOELeftTail`: `a₀ = 0`, `C` from the contrib two-time
defect bound,
`k = 0`, `c₁ = 1/8`. -/
theorem highLevelUpcrossingTail_airy1SRP (h : Airy1FddPositive) (hT : GOELeftTail) :
    HighLevelUpcrossingTail (airy1SRP h hT) := by
  obtain ⟨C, hC, hF⟩ := fwdDefectBound_exists 0
  refine ⟨⟨0, C, 0, 1 / 8, hC, le_rfl, by norm_num, ?_⟩⟩
  intro a ha t ht ht1 η hη x
  have key := airy1SRP_upcrossing_le h hT hC hF (x := x) (b := a + η) ht ht1 ha (by linarith)
  have hexp : -(a + η - a) ^ 2 / (8 * t) = -(1 / 8) * η ^ 2 / t := by
    field_simp
    ring
  rw [hexp] at key
  simpa [neg_zero, Real.rpow_zero, mul_one] using key

/-- **Headline `_of_QR₉` on the Airy₁ law** (the paper's main theorem (Theorem 1.1), normalized
real-length
form, on `Ã = airy1ContR h`): `gumbel_limit_continuum_real_normalized_airy1_of_QR₈` with
`HighLevelUpcrossingTail` discharged by `highLevelUpcrossingTail_airy1SRP`. Remaining
hypotheses: `Airy1FddPositive`, `GOELeftTail`, `QRTwoIntervalLaw`, `CubicStrongMixing`,
`CubicCovarianceDecay` and `ProcessAssociated` on `Ã`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_of_QR₉ (h : Airy1FddPositive)
    (hT : GOELeftTail)
    (two : QRTwoIntervalLaw (airy1BlockMax h) (airy1Law h))
    (M : CubicStrongMixing (airy1SRP h hT)) (Cov : CubicCovarianceDecay (airy1SRP h hT))
    (As : ProcessAssociated (airy1SRP h hT)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law h).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR h x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  gumbel_limit_continuum_real_normalized_airy1_of_QR₈ h hT two M Cov As
    (highLevelUpcrossingTail_airy1SRP h hT) z

end Airy1Gumbel
