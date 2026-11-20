/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.MesoscopicTP
import Airy1Gumbel.TwoPointBound
import Airy1Gumbel.CarrierTransfer

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators

/-!
# The Gumbel headline with three records: `_final₂`

`gumbel_limit_continuum_real_normalized_airy1_final` (`FinalHeadline.lean`) assumes five
records: `Airy1FddPositive`, `GOELeftTail`, `CubicStrongMixing`, `CubicCovarianceDecay` and
`ProcessAssociated`. The last two enter only through the mesoscopic bundle `MesoscopicBounds`
(fields `pair`, from Newman's inequality under association, and `cov_decay`). This file
replaces that bundle by `MesoscopicBoundsTP` (`MesoscopicTP.lean`), whose single new field
`pairTP` is the theorem `pairTP_airy1SRP_field` (two-point bound TP from the Schur
factorisation and trace-norm estimates of contrib `TwoTime/`). Hence:

* `MesoscopicBoundsTP.ofRecordsTP`: the bundle from `HighLevelUpcrossingTail` (cover),
  `PairTPBound` (pairTP) and `QRUnitBlockLaw` (sharp tail), as in `ofRecords₆`;
* `mesoscopic_of_recordsTP`, `mesoscopic_airy1TP`: the `mesoscopic` field, generic and on the
  concrete Airy₁ law (only `Airy1FddPositive`, `GOELeftTail`);
* `Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QRTP`: the TP twin of
  `_of_QR₆` (normalized real-length);
* `gumbel_limit_continuum_real_normalized_airy1_of_QRTP`: on the Airy₁ law with the QR records;
* **`gumbel_limit_continuum_real_normalized_airy1_final₂`**: the QR records discharged as in
  `_of_QR₁₀`; the only records left are `Airy1FddPositive`, `GOELeftTail` and
  `CubicStrongMixing`;
* `gumbel_limit_continuum_real_normalized_airy1_final₂_coord`: the same with
  `CubicStrongMixing` on the coordinate process `airy1Process h` (carrier transfer).

The headlines `_final`, `_final_coord`, `_of_QR₄ … _of_QR₁₀` remain available unchanged.
-/

namespace Airy1Gumbel

section Bridge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The TP bundle from the records (TP twin of `MesoscopicBounds.ofRecords₆`): `cover` from
`cover_of_upcrossing` (`HighLevelUpcrossingTail`), `modC = modc = 1`; `pairTP` from the
two-point bound `PairTPBound P X.A`; `one_point` from path continuity; `sharp_tail` from
`QRUnitBlockLaw`. No `ProcessAssociated`, no `CubicCovarianceDecay`. -/
noncomputable def MesoscopicBoundsTP.ofRecordsTP (C : Airy1ContinuousMax P)
    (X : StationaryRealProcess P) (hA : X.A = C.A) (U : HighLevelUpcrossingTail X)
    (TP : PairTPBound P X.A) (qr : QRUnitBlockLaw C.Y P) : MesoscopicBoundsTP P C.Y C.A where
  modC := 1
  modC_pos := one_pos
  modc := 1
  modc_pos := one_pos
  coverLevel := Classical.choose (cover_of_upcrossing C X hA U)
  cover := Classical.choose_spec (cover_of_upcrossing C X hA U)
  pairTP := by
    rw [← hA]
    exact TP
  one_point := C.one_point_le_block
  sharp_tail := sharp_tail_of_QRUnitBlockLaw qr

/-- **`mesoscopic` from the records, TP route** — EXACTLY the `Airy1BlockExtremes.mesoscopic`
field for `Y = C.Y`, from `HighLevelUpcrossingTail`, the two-point bound and `QRUnitBlockLaw`. -/
theorem mesoscopic_of_recordsTP (C : Airy1ContinuousMax P) (X : StationaryRealProcess P)
    (hA : X.A = C.A) (U : HighLevelUpcrossingTail X) (TP : PairTPBound P X.A)
    (qr : QRUnitBlockLaw C.Y P) :
    ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
      Tendsto (fun N : ℕ =>
        (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          P.real {ω | C.Y 0 ω > gumbelU N z ∧ C.Y j ω > gumbelU N z}) atTop (𝓝 0) :=
  mesoscopic_of_boundsTP (MesoscopicBoundsTP.ofRecordsTP C X hA U TP qr)

section OfQRTP

variable (Y : ℕ → Ω → ℝ) (Y_meas : ∀ j, Measurable (Y j))
  (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
  (stat_pair : ∀ (u : ℝ) (i d : ℕ),
    P {ω | Y i ω > u ∧ Y (i + d) ω > u} = P {ω | Y 0 ω > u ∧ Y d ω > u})
  (qr : QRUnitBlockLaw Y P) (qr₂ : QRTwoBlockLaw Y P) (two : QRTwoIntervalLaw Y P)
  (C : Airy1ContinuousMax P) (hY : Y = C.Y)
  (X : StationaryRealProcess P) (hA : X.A = C.A) (M : CubicStrongMixing X)
  (U : HighLevelUpcrossingTail X) (TP : PairTPBound P X.A)

include Y_meas stat_marginal stat_pair qr qr₂ two hY hA M U TP

/-- **Headline shape, TP twin of `_of_QR₆`** (the paper's main theorem, Theorem 1.1, normalized
real-length form):
`_of_QR₄` with `mesoscopic := mesoscopic_of_recordsTP …`. Compared with `_of_QR₆`, the records
`CubicCovarianceDecay`, `PairStationary` and `ProcessAssociated` are replaced by the two-point
bound `PairTPBound P X.A`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QRTP (z : ℝ) :
    Tendsto (fun T : ℝ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (C.A x ω - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_recordsTP C X hA U TP qr) C rfl
    X hA M z

end OfQRTP

end Bridge

/-! ## On the Airy₁ law -/

/-- **The `mesoscopic` field for the concrete Airy₁ block maxima**, conditional only on
`Airy1FddPositive` and `GOELeftTail`: `mesoscopic_of_recordsTP` with
`HighLevelUpcrossingTail` = `highLevelUpcrossingTail_airy1SRP`, TP = `pairTP_airy1SRP_field`
and `QRUnitBlockLaw` = `qrUnitBlockLaw_airy1` (unconditional mesh hitting). -/
theorem mesoscopic_airy1TP (h : Airy1FddPositive) (hT : GOELeftTail) :
    ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
      Tendsto (fun N : ℕ =>
        (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          (airy1Law h).real {f | airy1BlockMax h 0 f > gumbelU N z ∧
            airy1BlockMax h j f > gumbelU N z}) atTop (𝓝 0) :=
  mesoscopic_of_recordsTP (airy1CMax h) (airy1SRP h hT) rfl
    (highLevelUpcrossingTail_airy1SRP h hT) (pairTP_airy1SRP_field h hT)
    (qrUnitBlockLaw_airy1 h hT (forall_meshHittingLimit one_pos))

/-- **Headline, TP route, with the QR records** (the paper's main theorem, Theorem 1.1, normalized
real-length form, on `Ã = airy1ContR h`): `gumbel_limit_continuum_real_normalized_airy1` with
`mesoscopic := mesoscopic_airy1TP h hT`. Remaining hypotheses: `h`, `hT`, the three QR-law
records and `CubicStrongMixing` on `Ã`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_of_QRTP (h : Airy1FddPositive)
    (hT : GOELeftTail)
    (qr : QRUnitBlockLaw (airy1BlockMax h) (airy1Law h))
    (qr₂ : QRTwoBlockLaw (airy1BlockMax h) (airy1Law h))
    (two : QRTwoIntervalLaw (airy1BlockMax h) (airy1Law h))
    (M : CubicStrongMixing (airy1SRP h hT)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law h).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR h x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  gumbel_limit_continuum_real_normalized_airy1 h hT qr qr₂ two (mesoscopic_airy1TP h hT) M z

/-- **The Gumbel headline for the concrete Airy₁ process, three records** (the
paper's main theorem, Theorem 1.1, normalized real-length form, on `Ã = airy1ContR h` under
`airy1Law h`): for every `z`, `ℙ(max_{x ∈ [0,T]} (Ã x − a_T)/b_T ≤ z) → exp(−e^{−z})`.

The only remaining hypotheses are the records
* `Airy1FddPositive` (`h`),
* `GOELeftTail` (`hT`),
* `CubicStrongMixing (airy1SRP h hT)` (`M`).

Compared with `gumbel_limit_continuum_real_normalized_airy1_final`, `CubicCovarianceDecay` and
`ProcessAssociated` are no longer needed: the mesoscopic pairs are controlled by the two-point
bound TP (`pairTP_airy1SRP_field`). The QR block-law records are discharged
as in `_of_QR₁₀`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_final₂ (h : Airy1FddPositive)
    (hT : GOELeftTail) (M : CubicStrongMixing (airy1SRP h hT)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law h).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR h x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  gumbel_limit_continuum_real_normalized_airy1_of_QRTP h hT
    (qrUnitBlockLaw_airy1 h hT (forall_meshHittingLimit one_pos))
    (qrTwoBlockLaw_airy1 h hT (forall_meshHittingLimit two_pos))
    (qrTwoIntervalLaw_airy1 h hT) M z

/-- **`_final₂` with `CubicStrongMixing` on the coordinate process** `airy1Process h` (i.e. as a
statement about the Airy₁ law alone), transferred to `Ã` by `CubicStrongMixing.ofModification`
and `airy1SRP_ae_eq_airy1Process`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_final₂_coord (h : Airy1FddPositive)
    (hT : GOELeftTail) (M : CubicStrongMixing (airy1Process h)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law h).real {f | ∀ x ∈ Icc (0 : ℝ) T,
        (airy1ContR h x f - gumbelAR T) / gumbelBR T ≤ z}) atTop
      (nhds (Real.exp (-Real.exp (-z)))) :=
  gumbel_limit_continuum_real_normalized_airy1_final₂ h hT
    (M.ofModification (airy1SRP_ae_eq_airy1Process h hT)) z

end Airy1Gumbel
