/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.FinalHeadline

open Filter MeasureTheory ProbabilityTheory Set

/-!
# Carrier transfer of the three literature records

The final headline `gumbel_limit_continuum_real_normalized_airy1_final` assumes
`CubicStrongMixing`, `CubicCovarianceDecay` and `ProcessAssociated` on the continuous version
`Ã = airy1SRP h hT`, while the literature states them for the Airy₁ process, i.e. for its law.
This module proves that each record holds on `Ã` iff it holds on the coordinate process
`airy1Process h` (the canonical process with law `airy1Law h`), with the same constants.

All three transfers are instances of one generic fact: if two `StationaryRealProcess`es on the
same probability space are modifications of each other (`X.A t =ᵐ[P] Y.A t` for every real `t`),
then the records transfer.

* `CubicCovarianceDecay` and `ProcessAssociated` see the process only through finitely many
  times, and `covariance`/`MemLp` are invariant under a.e. modification.
* `CubicStrongMixing` quantifies over **all** events of the generated σ-algebras
  `pastSigma X.A a` / `futureSigma X.A b`. For `Ã` these are **not** sub-σ-algebras of the
  coordinate ones (`Ã_y` for `y ≥ 0` reads the whole path through `goodLowSet`). The transfer
  uses null-set approximation instead: `aeClosure P m` is the σ-algebra of sets a.e. equal to an
  `m`-measurable set, and `pastSigma X.A a ≤ aeClosure P (pastSigma Y.A a)` because every
  generator `X.A y ⁻¹' U` is a.e. equal to `Y.A y ⁻¹' U`. Since `P.real` (the outer measure for
  non-measurable sets as well) is invariant under a.e. equality of sets (`measureReal_congr`),
  the bound `|P(E ∩ F) − P(E) P(F)|` transfers event by event.
-/

namespace Airy1Gumbel

section Generic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The σ-algebra of sets that are `P`-a.e. equal to an `m`-measurable set (the `P`-null
modification closure of `m`; no measurability in the ambient σ-algebra is required). -/
@[instance_reducible]
def aeClosure (P : Measure Ω) (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' E := ∃ E', MeasurableSet[m] E' ∧ E =ᵐ[P] E'
  measurableSet_empty := ⟨∅, m.measurableSet_empty, EventuallyEqSet.rfl⟩
  measurableSet_compl E := fun ⟨E', hE', hEE'⟩ =>
    ⟨E'ᶜ, m.measurableSet_compl E' hE', hEE'.compl⟩
  measurableSet_iUnion f hf := by
    choose g hg hfg using hf
    exact ⟨⋃ i, g i, m.measurableSet_iUnion g hg, EventuallyEqSet.countable_iUnion hfg⟩

variable {P : Measure Ω}

/-- The past σ-algebra of a modification lies in the null-set closure of the past σ-algebra. -/
theorem pastSigma_le_aeClosure {A B : ℝ → Ω → ℝ} (hAB : ∀ t, A t =ᵐ[P] B t) (a : ℝ) :
    pastSigma A a ≤ aeClosure P (pastSigma B a) := by
  refine iSup₂_le fun y hy => ?_
  intro E hE
  obtain ⟨U, hU, rfl⟩ := hE
  refine ⟨B y ⁻¹' U, ?_, (hAB y).preimage U⟩
  exact le_iSup₂ (f := fun (y : ℝ) (_ : y ≤ a) =>
    MeasurableSpace.comap (B y) Real.measurableSpace) y hy _ ⟨U, hU, rfl⟩

/-- The future σ-algebra of a modification lies in the null-set closure of the future σ-algebra. -/
theorem futureSigma_le_aeClosure {A B : ℝ → Ω → ℝ} (hAB : ∀ t, A t =ᵐ[P] B t) (b : ℝ) :
    futureSigma A b ≤ aeClosure P (futureSigma B b) := by
  refine iSup₂_le fun y hy => ?_
  intro E hE
  obtain ⟨U, hU, rfl⟩ := hE
  refine ⟨B y ⁻¹' U, ?_, (hAB y).preimage U⟩
  exact le_iSup₂ (f := fun (y : ℝ) (_ : b ≤ y) =>
    MeasurableSpace.comap (B y) Real.measurableSpace) y hy _ ⟨U, hU, rfl⟩

/-- `covariance` is invariant under a.e. modification of both arguments. -/
theorem covariance_congr_ae {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') :
    covariance X Y P = covariance X' Y' P := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω h1 h2
  rw [h1, h2]

variable [IsProbabilityMeasure P]

/-- **`CubicStrongMixing` transfers to a modification**, with the same constants. -/
def CubicStrongMixing.ofModification {X Y : StationaryRealProcess P}
    (hXY : ∀ t, X.A t =ᵐ[P] Y.A t) (M : CubicStrongMixing Y) : CubicStrongMixing X where
  mixC := M.mixC
  mixC_pos := M.mixC_pos
  mixc := M.mixc
  mixc_pos := M.mixc_pos
  bound a d hd E F hE hF := by
    obtain ⟨E', hE', hEE'⟩ := pastSigma_le_aeClosure hXY a E hE
    obtain ⟨F', hF', hFF'⟩ := futureSigma_le_aeClosure hXY (a + d) F hF
    rw [measureReal_congr (hEE'.inter hFF'), measureReal_congr hEE', measureReal_congr hFF']
    exact M.bound a d hd E' F' hE' hF'

/-- **`CubicCovarianceDecay` transfers to a modification**, with the same constant. -/
def CubicCovarianceDecay.ofModification {X Y : StationaryRealProcess P}
    (hXY : ∀ t, X.A t =ᵐ[P] Y.A t) (Cov : CubicCovarianceDecay Y) :
    CubicCovarianceDecay X where
  memLp_zero := Cov.memLp_zero.ae_eq (hXY 0).symm
  c := Cov.c
  c_pos := Cov.c_pos
  bound d hd := by
    rw [covariance_congr_ae (hXY 0) (hXY d)]
    exact Cov.bound d hd

/-- **`ProcessAssociated` transfers to a modification.** -/
theorem ProcessAssociated.ofModification {X Y : StationaryRealProcess P}
    (hXY : ∀ t, X.A t =ᵐ[P] Y.A t) (As : ProcessAssociated Y) : ProcessAssociated X where
  assoc n s f g hf hg hfm hgm hfb hgb := by
    have hall : ∀ᵐ ω ∂P, ∀ i, X.A (s i) ω = Y.A (s i) ω := ae_all_iff.2 fun i => hXY (s i)
    have hf' : (fun ω => f fun i => X.A (s i) ω) =ᵐ[P] fun ω => f fun i => Y.A (s i) ω := by
      filter_upwards [hall] with ω hω
      simp only [hω]
    have hg' : (fun ω => g fun i => X.A (s i) ω) =ᵐ[P] fun ω => g fun i => Y.A (s i) ω := by
      filter_upwards [hall] with ω hω
      simp only [hω]
    rw [covariance_congr_ae hf' hg']
    exact As.assoc n s f g hf hg hfm hgm hfb hgb

theorem nonempty_cubicStrongMixing_iff_of_modification {X Y : StationaryRealProcess P}
    (hXY : ∀ t, X.A t =ᵐ[P] Y.A t) :
    Nonempty (CubicStrongMixing X) ↔ Nonempty (CubicStrongMixing Y) :=
  ⟨fun ⟨M⟩ => ⟨M.ofModification fun t => (hXY t).symm⟩, fun ⟨M⟩ => ⟨M.ofModification hXY⟩⟩

theorem nonempty_cubicCovarianceDecay_iff_of_modification {X Y : StationaryRealProcess P}
    (hXY : ∀ t, X.A t =ᵐ[P] Y.A t) :
    Nonempty (CubicCovarianceDecay X) ↔ Nonempty (CubicCovarianceDecay Y) :=
  ⟨fun ⟨C⟩ => ⟨C.ofModification fun t => (hXY t).symm⟩, fun ⟨C⟩ => ⟨C.ofModification hXY⟩⟩

theorem processAssociated_iff_of_modification {X Y : StationaryRealProcess P}
    (hXY : ∀ t, X.A t =ᵐ[P] Y.A t) : ProcessAssociated X ↔ ProcessAssociated Y :=
  ⟨fun A => A.ofModification fun t => (hXY t).symm, fun A => A.ofModification hXY⟩

end Generic

/-! ## The concrete Airy₁ carriers -/

/-- `Ã = airy1SRP h hT` is a modification of the coordinate process `airy1Process h` at every
real time (including `t < 0`, where `Ã` is the raw coordinate). -/
theorem airy1SRP_ae_eq_airy1Process (h : Airy1FddPositive) (hT : GOELeftTail) (t : ℝ) :
    (airy1SRP h hT).A t =ᵐ[airy1Law h] (airy1Process h).A t :=
  airy1ContR_ae_eq h hT t

/-- **Carrier transfer of [ChenPu2026, Proposition 3.1]**: the cubic strong-mixing record holds
on the continuous version `Ã` iff it holds on the coordinate process (same constants). -/
theorem cubicStrongMixing_airy1SRP_iff (h : Airy1FddPositive) (hT : GOELeftTail) :
    Nonempty (CubicStrongMixing (airy1SRP h hT)) ↔
      Nonempty (CubicStrongMixing (airy1Process h)) :=
  nonempty_cubicStrongMixing_iff_of_modification (airy1SRP_ae_eq_airy1Process h hT)

/-- **Carrier transfer of [BasuBusaniFerrari2023, Theorem 1.1]**: the covariance-decay record
holds on `Ã` iff it holds on the coordinate process (same constant). -/
theorem cubicCovarianceDecay_airy1SRP_iff (h : Airy1FddPositive) (hT : GOELeftTail) :
    Nonempty (CubicCovarianceDecay (airy1SRP h hT)) ↔
      Nonempty (CubicCovarianceDecay (airy1Process h)) :=
  nonempty_cubicCovarianceDecay_iff_of_modification (airy1SRP_ae_eq_airy1Process h hT)

/-- **Carrier transfer of [Pu2025, Theorem 1.2]**: the association record holds on `Ã` iff it
holds on the coordinate process. -/
theorem processAssociated_airy1SRP_iff (h : Airy1FddPositive) (hT : GOELeftTail) :
    ProcessAssociated (airy1SRP h hT) ↔ ProcessAssociated (airy1Process h) :=
  processAssociated_iff_of_modification (airy1SRP_ae_eq_airy1Process h hT)

/-- **The final headline with the three literature records on the coordinate process**
`airy1Process h` (i.e. as statements about the Airy₁ law `airy1Law h` alone), transferred to
`Ã` by the carrier-transfer lemmas. -/
theorem gumbel_limit_continuum_real_normalized_airy1_final_coord (h : Airy1FddPositive)
    (hT : GOELeftTail)
    (M : CubicStrongMixing (airy1Process h)) (Cov : CubicCovarianceDecay (airy1Process h))
    (As : ProcessAssociated (airy1Process h)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law h).real {f | ∀ x ∈ Icc (0 : ℝ) T,
        (airy1ContR h x f - gumbelAR T) / gumbelBR T ≤ z}) atTop
      (nhds (Real.exp (-Real.exp (-z)))) :=
  gumbel_limit_continuum_real_normalized_airy1_final h hT
    (M.ofModification (airy1SRP_ae_eq_airy1Process h hT))
    (Cov.ofModification (airy1SRP_ae_eq_airy1Process h hT))
    (As.ofModification (airy1SRP_ae_eq_airy1Process h hT)) z

end Airy1Gumbel
