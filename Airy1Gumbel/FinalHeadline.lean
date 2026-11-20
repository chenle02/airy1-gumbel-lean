/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.TwoIntervalLaw
import Airy1Gumbel.UpcrossingTheorem

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

/-!
# The final Gumbel headline for the concrete Airy₁ process

`gumbel_limit_continuum_real_normalized_airy1_final` combines two discharges:

* `TwoIntervalLaw.lean`: `QRTwoIntervalLaw (airy1BlockMax h) (airy1Law h)` is the theorem
  `qrTwoIntervalLaw_airy1 h hT`;
* `UpcrossingTheorem.lean`: `HighLevelUpcrossingTail (airy1SRP h hT)` is the theorem
  `highLevelUpcrossingTail_airy1SRP h hT`, used inside the upcrossing-based headline `_of_QR₉`.

The headline is `_of_QR₉` applied to `qrTwoIntervalLaw_airy1 h hT`.
-/

namespace Airy1Gumbel

/-- **The Gumbel headline for the concrete Airy₁ process** (the paper's main theorem, Theorem 1.1,
normalized real-length form, on `Ã = airy1ContR h` under `airy1Law h`): for every `z`,
`ℙ(max_{x ∈ [0,T]} (Ã x − a_T)/b_T ≤ z) → exp(−e^{−z})` as `T → ∞`.

The only remaining hypotheses are the records
* `Airy1FddPositive` (`h`),
* `GOELeftTail` (`hT`),
* `CubicStrongMixing (airy1SRP h hT)` (`M`),
* `CubicCovarianceDecay (airy1SRP h hT)` (`Cov`),
* `ProcessAssociated (airy1SRP h hT)` (`As`).

Discharged or retired: all QR block-law records (`QRUnitBlockLaw`, `QRTwoBlockLaw` via
`meshHittingLimit`, `QRTwoIntervalLaw` via `qrTwoIntervalLaw_airy1`), `PairStationary`, the
mesoscopic records, and `LocalModulusEstimate` / `HighLevelUpcrossingTail` (via
`highLevelUpcrossingTail_airy1SRP`). -/
theorem gumbel_limit_continuum_real_normalized_airy1_final (h : Airy1FddPositive)
    (hT : GOELeftTail)
    (M : CubicStrongMixing (airy1SRP h hT)) (Cov : CubicCovarianceDecay (airy1SRP h hT))
    (As : ProcessAssociated (airy1SRP h hT)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law h).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR h x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  gumbel_limit_continuum_real_normalized_airy1_of_QR₉ h hT (qrTwoIntervalLaw_airy1 h hT)
    M Cov As z

end Airy1Gumbel
