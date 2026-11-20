/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.Upcrossing
import Airy1Gumbel.ContinuousInstance

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators NNReal

/-!
# The `mesoscopic` discharge via `HighLevelUpcrossingTail`: `ofQR₆` and the `_of_QR₆` headlines

`MesoscopicBounds.ofRecords₆` assembles the bundle exactly as
`MesoscopicBounds.ofRecords` (`MesoscopicRecord.lean`), with the path-level
`LocalModulusEstimate` replaced by the two-point fdd record `HighLevelUpcrossingTail`
(from [QuastelRemenik2013], in the proof of their truncation lemma, at a fixed lowest level)
through `cover_of_upcrossing`
(`Upcrossing.lean`): the covering holds at levels `v ≥ coverLevel` (the record's `a₀ + 1`), with
`modC = modc = 1`. `mesoscopic_of_records₆` states the `Airy1BlockExtremes.mesoscopic` field
exactly; `Airy1BlockExtremes.ofQR₆` and the six `_of_QR₆` headlines are the `_of_QR₅` ones with
`LocalModulusEstimate` replaced by `HighLevelUpcrossingTail` (same record count). The
`_of_QR₅` headlines are unchanged.

Unlike `LocalModulusEstimate` (uninhabited on the coordinate process and on the continuous
version: `isEmpty_localModulusEstimate_airy1Process`, `isEmpty_localModulusEstimate_airy1SRP`),
the new record is a statement about two-point laws, so it is not refuted by either carrier.
`gumbel_limit_continuum_real_normalized_airy1_of_QR₆` specialises the normalized real-length
headline to the continuous version `Ã = airy1ContR h` under `airy1Law h`; the covering route
evaluates `Ã` only at times in `[0, ∞)` (grid points `j + k/n` and dyadic points of
sub-intervals of `[j, j+1]`, `j ≥ 0`), so the raw coordinates on `(-∞, 0)` never enter.
Its remaining hypotheses are the QR-law records, `CubicStrongMixing`, `CubicCovarianceDecay`,
`ProcessAssociated` and `HighLevelUpcrossingTail` on `Ã`; `PairStationary` is discharged
(`pairStationary_airy1SRP`).
-/

namespace Airy1Gumbel

section Bridge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The bundle from the records, with `HighLevelUpcrossingTail` in place of
`LocalModulusEstimate`: `cover` from `cover_of_upcrossing` at the level threshold
it provides, `modC = modc = 1`; the other fields as in `MesoscopicBounds.ofRecords`. -/
noncomputable def MesoscopicBounds.ofRecords₆ (C : Airy1ContinuousMax P)
    (X : StationaryRealProcess P) (hA : X.A = C.A) (Cov : CubicCovarianceDecay X)
    (PS : PairStationary X) (As : ProcessAssociated X) (U : HighLevelUpcrossingTail X)
    (qr : QRUnitBlockLaw C.Y P) : MesoscopicBounds P C.Y C.A where
  modC := 1
  modC_pos := one_pos
  modc := 1
  modc_pos := one_pos
  coverLevel := Classical.choose (cover_of_upcrossing C X hA U)
  cover := Classical.choose_spec (cover_of_upcrossing C X hA U)
  pair := by
    rw [← hA]
    exact grid_pair_bound As Cov.memLp PS
  cov_decay := by
    rw [← hA]
    exact Cov.theta_bound
  one_point := C.one_point_le_block
  sharp_tail := sharp_tail_of_QRUnitBlockLaw qr

/-- **`mesoscopic` from the records, upcrossing route** — EXACTLY the
`Airy1BlockExtremes.mesoscopic` field for `Y = C.Y`. Inputs as in `mesoscopic_of_records`, with
the two-point upcrossing estimate of [QuastelRemenik2013] (`HighLevelUpcrossingTail`) and path
continuity (`C.path_cont`) in place of the BB2024-derived `LocalModulusEstimate`. -/
theorem mesoscopic_of_records₆ (C : Airy1ContinuousMax P) (X : StationaryRealProcess P)
    (hA : X.A = C.A) (Cov : CubicCovarianceDecay X) (PS : PairStationary X)
    (As : ProcessAssociated X) (U : HighLevelUpcrossingTail X) (qr : QRUnitBlockLaw C.Y P) :
    ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
      Tendsto (fun N : ℕ =>
        (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          P.real {ω | C.Y 0 ω > gumbelU N z ∧ C.Y j ω > gumbelU N z}) atTop (𝓝 0) :=
  mesoscopic_of_bounds (MesoscopicBounds.ofRecords₆ C X hA Cov PS As U qr)

section OfQR₆

variable (Y : ℕ → Ω → ℝ) (Y_meas : ∀ j, Measurable (Y j))
  (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
  (stat_pair : ∀ (u : ℝ) (i d : ℕ),
    P {ω | Y i ω > u ∧ Y (i + d) ω > u} = P {ω | Y 0 ω > u ∧ Y d ω > u})
  (qr : QRUnitBlockLaw Y P) (qr₂ : QRTwoBlockLaw Y P) (two : QRTwoIntervalLaw Y P)
  (C : Airy1ContinuousMax P) (hY : Y = C.Y)
  (X : StationaryRealProcess P) (hA : X.A = C.A) (M : CubicStrongMixing X)
  (Cov : CubicCovarianceDecay X) (PS : PairStationary X) (As : ProcessAssociated X)
  (U : HighLevelUpcrossingTail X)

include Y_meas stat_marginal stat_pair qr qr₂ two hY hA M Cov PS As U

/-- Smart constructor with **every** field of `Airy1BlockExtremes` discharged from
records: `ofQR₄` with `mesoscopic := mesoscopic_of_records₆` (the `HighLevelUpcrossingTail` route). -/
noncomputable def Airy1BlockExtremes.ofQR₆ : Airy1BlockExtremes P := by
  subst hY
  exact Airy1BlockExtremes.ofQR₄ C.Y Y_meas stat_marginal stat_pair qr qr₂ two
    (mesoscopic_of_records₆ C X hA Cov PS As U qr) C rfl X hA M

/-- **Headline shape, `_of_QR₆`** (the paper's main theorem, Theorem 1.1, normalized
real-length):
`(M_T - a_T)/b_T ⇒ Gumbel` with no `mesoscopic` and no mixing hypothesis. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QR₆ (z : ℝ) :
    Tendsto (fun T : ℝ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (C.A x ω - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_records₆ C X hA Cov PS As U qr) C rfl
    X hA M z

/-- **Block-maxima Gumbel limit, `_of_QR₆`** (Theorem 1.1 of the paper): the `_of_QR₄`
headline with `mesoscopic := mesoscopic_of_records₆ …`; no `mesoscopic` and no mixing
hypothesis. -/
theorem Airy1BlockExtremes.gumbel_limit_of_QR₆ (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ j ∈ Finset.range N, Y j ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1BlockExtremes.gumbel_limit_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_records₆ C X hA Cov PS As U qr) C rfl
    X hA M z

/-- **Integer-length continuum Gumbel limit, `_of_QR₆`** (Theorem 1.1 of the paper): the `_of_QR₄`
headline with `mesoscopic := mesoscopic_of_records₆ …`; no `mesoscopic` and no mixing
hypothesis. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_QR₆ (z : ℝ) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1ContinuousMax.gumbel_limit_continuum_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_records₆ C X hA Cov PS As U qr) C rfl
    X hA M z

/-- **Normalized integer-length Gumbel limit, `_of_QR₆`** (Theorem 1.1 of the paper): the `_of_QR₄`
headline with `mesoscopic := mesoscopic_of_records₆ …`; no `mesoscopic` and no mixing
hypothesis. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_normalized_of_QR₆ (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ),
      (C.A x ω - gumbelA N) / gumbelB N ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1ContinuousMax.gumbel_limit_continuum_normalized_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_records₆ C X hA Cov PS As U qr) C rfl
    X hA M z

/-- **Gumbel limit along a convergent level sequence, `_of_QR₆`** (Theorem 1.1 of the paper):
the `_of_QR₄` headline with `mesoscopic := mesoscopic_of_records₆ …`; no `mesoscopic` and no mixing
hypothesis. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto_of_QR₆ (z : ℝ) (w : ℕ → ℝ)
    (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N (w N)})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_records₆ C X hA Cov PS As U qr) C rfl
    X hA M z w hw

/-- **Real-length continuum Gumbel limit, `_of_QR₆`** (Theorem 1.1 of the paper): the `_of_QR₄`
headline with `mesoscopic := mesoscopic_of_records₆ …`; no `mesoscopic` and no mixing
hypothesis. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_of_QR₆ (z : ℝ) :
    Tendsto (fun T : ℝ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T, C.A x ω ≤ gumbelUR T z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1ContinuousMax.gumbel_limit_continuum_real_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_records₆ C X hA Cov PS As U qr) C rfl
    X hA M z

end OfQR₆

end Bridge

/-! ## The `_of_QR₆` headline on the Airy₁ law -/

/-- **Headline `_of_QR₆` specialised to the Airy₁ law** (the paper's main theorem, Theorem 1.1,
normalized real-length form) on the continuous version `Ã = airy1ContR h`. `Y_meas`,
`stat_marginal`,
`stat_pair`, `path_cont`, `Y_eq`, `hY`, `hA` and `PairStationary` are discharged (from
`Airy1FddPositive` and `GOELeftTail`); `mesoscopic` is discharged through
`mesoscopic_of_records₆`. Remaining hypotheses: the QR-law records, `CubicStrongMixing`,
`CubicCovarianceDecay`, `ProcessAssociated` and `HighLevelUpcrossingTail` on `Ã`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_of_QR₆ (h : Airy1FddPositive)
    (hT : GOELeftTail)
    (qr : QRUnitBlockLaw (airy1BlockMax h) (airy1Law h))
    (qr₂ : QRTwoBlockLaw (airy1BlockMax h) (airy1Law h))
    (two : QRTwoIntervalLaw (airy1BlockMax h) (airy1Law h))
    (M : CubicStrongMixing (airy1SRP h hT)) (Cov : CubicCovarianceDecay (airy1SRP h hT))
    (As : ProcessAssociated (airy1SRP h hT)) (U : HighLevelUpcrossingTail (airy1SRP h hT))
    (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law h).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR h x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QR₆ (airy1BlockMax h)
    (measurable_airy1BlockMax h) (airy1BlockMax_stat_marginal h hT)
    (airy1BlockMax_stat_pair h hT) qr qr₂ two (airy1CMax h) rfl (airy1SRP h hT) rfl M Cov
    (pairStationary_airy1SRP h hT) As U z

end Airy1Gumbel
