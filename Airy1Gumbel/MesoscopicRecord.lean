/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.MesoscopicCover
import Airy1Gumbel.MesoscopicPair
import Airy1Gumbel.MesoscopicSum

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators NNReal

/-!
# The `mesoscopic` field from records: bridge, `ofQR₅` and the `_of_QR₅` corollaries

`MesoscopicBounds.ofRecords` assembles the bundle from the records
(`LocalModulusEstimate`, `CubicCovarianceDecay`, `PairStationary`, `ProcessAssociated`,
`newman_lemma3`) and `QRUnitBlockLaw`; `mesoscopic_of_records` states the
`Airy1BlockExtremes.mesoscopic` field exactly (the paper's mesoscopic estimate).
`Airy1BlockExtremes.ofQR₅` supplies **every** field from records; the six `_of_QR₅`
headlines carry no `sharp_tail`, `touching`, `separated`, mixing or `mesoscopic`
hypothesis.
-/

namespace Airy1Gumbel

/-! ## Bridge: records → `MesoscopicBounds` → the `mesoscopic` field -/

section Bridge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The bundle from the records, through the link `X.A = C.A`. -/
noncomputable def MesoscopicBounds.ofRecords (C : Airy1ContinuousMax P)
    (X : StationaryRealProcess P) (hA : X.A = C.A) (Cov : CubicCovarianceDecay X)
    (PS : PairStationary X) (As : ProcessAssociated X) (L : LocalModulusEstimate X)
    (qr : QRUnitBlockLaw C.Y P) : MesoscopicBounds P C.Y C.A where
  modC := L.C₀
  modC_pos := L.C₀_pos
  modc := L.c₀
  modc_pos := L.c₀_pos
  coverLevel := 0
  cover := (cover_of_LocalModulusEstimate C X hA L).mono fun _ h j v _ => h j v
  pair := by
    rw [← hA]
    exact grid_pair_bound As Cov.memLp PS
  cov_decay := by
    rw [← hA]
    exact Cov.theta_bound
  one_point := C.one_point_le_block
  sharp_tail := sharp_tail_of_QRUnitBlockLaw qr

/-- **`mesoscopic` from the records** — EXACTLY the `Airy1BlockExtremes.mesoscopic`
field for `Y = C.Y`. Inputs: [BasuBusaniFerrari2023, Thm 1.1] (`CubicCovarianceDecay`),
two-point stationarity (`PairStationary`), [Pu2025, Thm 1.2] (`ProcessAssociated`),
the BB2024-derived local modulus with the Portmanteau and centre
transfer proved in the paper (`LocalModulusEstimate`), and [QuastelRemenik2012, Thm 4]
(`QRUnitBlockLaw`, via `sharp_tail`). Newman's inequality is proved, not assumed. -/
theorem mesoscopic_of_records (C : Airy1ContinuousMax P) (X : StationaryRealProcess P)
    (hA : X.A = C.A) (Cov : CubicCovarianceDecay X) (PS : PairStationary X)
    (As : ProcessAssociated X) (L : LocalModulusEstimate X) (qr : QRUnitBlockLaw C.Y P) :
    ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
      Tendsto (fun N : ℕ =>
        (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          P.real {ω | C.Y 0 ω > gumbelU N z ∧ C.Y j ω > gumbelU N z}) atTop (𝓝 0) :=
  mesoscopic_of_bounds (MesoscopicBounds.ofRecords C X hA Cov PS As L qr)

section OfQR₅

variable (Y : ℕ → Ω → ℝ) (Y_meas : ∀ j, Measurable (Y j))
  (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
  (stat_pair : ∀ (u : ℝ) (i d : ℕ),
    P {ω | Y i ω > u ∧ Y (i + d) ω > u} = P {ω | Y 0 ω > u ∧ Y d ω > u})
  (qr : QRUnitBlockLaw Y P) (qr₂ : QRTwoBlockLaw Y P) (two : QRTwoIntervalLaw Y P)
  (C : Airy1ContinuousMax P) (hY : Y = C.Y)
  (X : StationaryRealProcess P) (hA : X.A = C.A) (M : CubicStrongMixing X)
  (Cov : CubicCovarianceDecay X) (PS : PairStationary X) (As : ProcessAssociated X)
  (L : LocalModulusEstimate X)

include Y_meas stat_marginal stat_pair qr qr₂ two hY hA M Cov PS As L

/-- Smart constructor with **every** field of `Airy1BlockExtremes` discharged from
records: `ofQR₄` with `mesoscopic := mesoscopic_of_records`. -/
noncomputable def Airy1BlockExtremes.ofQR₅ : Airy1BlockExtremes P := by
  subst hY
  exact Airy1BlockExtremes.ofQR₄ C.Y Y_meas stat_marginal stat_pair qr qr₂ two
    (mesoscopic_of_records C X hA Cov PS As L qr) C rfl X hA M

/-- **Main-theorem shape, `_of_QR₅`** (Theorem 1.1 of the paper, normalized real-length):
`(M_T - a_T)/b_T ⇒ Gumbel` with no `mesoscopic` and no mixing hypothesis. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QR₅ (z : ℝ) :
    Tendsto (fun T : ℝ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (C.A x ω - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_records C X hA Cov PS As L qr) C rfl
    X hA M z

/-- **Block-maxima Gumbel limit, `_of_QR₅`** (Theorem 1.1 of the paper): the `_of_QR₄`
headline with `mesoscopic := mesoscopic_of_records …`; no `mesoscopic` and no mixing
hypothesis. -/
theorem Airy1BlockExtremes.gumbel_limit_of_QR₅ (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ j ∈ Finset.range N, Y j ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1BlockExtremes.gumbel_limit_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_records C X hA Cov PS As L qr) C rfl
    X hA M z

/-- **Integer-length continuum Gumbel limit, `_of_QR₅`** (Theorem 1.1 of the paper): the `_of_QR₄`
headline with `mesoscopic := mesoscopic_of_records …`; no `mesoscopic` and no mixing
hypothesis. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_QR₅ (z : ℝ) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1ContinuousMax.gumbel_limit_continuum_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_records C X hA Cov PS As L qr) C rfl
    X hA M z

/-- **Normalized integer-length Gumbel limit, `_of_QR₅`** (Theorem 1.1 of the paper): the `_of_QR₄`
headline with `mesoscopic := mesoscopic_of_records …`; no `mesoscopic` and no mixing
hypothesis. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_normalized_of_QR₅ (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ),
      (C.A x ω - gumbelA N) / gumbelB N ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1ContinuousMax.gumbel_limit_continuum_normalized_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_records C X hA Cov PS As L qr) C rfl
    X hA M z

/-- **Gumbel limit along a convergent level sequence, `_of_QR₅`** (Theorem 1.1 of the paper): the `_of_QR₄`
headline with `mesoscopic := mesoscopic_of_records …`; no `mesoscopic` and no mixing
hypothesis. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto_of_QR₅ (z : ℝ) (w : ℕ → ℝ)
    (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N (w N)})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_records C X hA Cov PS As L qr) C rfl
    X hA M z w hw

/-- **Real-length continuum Gumbel limit, `_of_QR₅`** (Theorem 1.1 of the paper): the `_of_QR₄`
headline with `mesoscopic := mesoscopic_of_records …`; no `mesoscopic` and no mixing
hypothesis. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_of_QR₅ (z : ℝ) :
    Tendsto (fun T : ℝ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T, C.A x ω ≤ gumbelUR T z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  subst hY
  exact Airy1ContinuousMax.gumbel_limit_continuum_real_of_QR₄ C.Y Y_meas
    stat_marginal stat_pair qr qr₂ two (mesoscopic_of_records C X hA Cov PS As L qr) C rfl
    X hA M z

end OfQR₅

end Bridge

end Airy1Gumbel
