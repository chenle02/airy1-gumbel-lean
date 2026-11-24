/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.FddFromTasep
import Airy1Gumbel.Airy1Process
import Airy1Gumbel.BlockLaw
import Airy1Gumbel.BlockLawUnconditional
import Airy1Gumbel.BlockModulus
import Airy1Gumbel.CarrierTransfer
import Airy1Gumbel.ContinuousInstance
import Airy1Gumbel.ContinuousVersion
import Airy1Gumbel.FddRecord
import Airy1Gumbel.FerrariLiuRoute
import Airy1Gumbel.FinalHeadline
import Airy1Gumbel.FinalHeadlineTP
import Airy1Gumbel.GOELeftTail
import Airy1Gumbel.LowerBound
import Airy1Gumbel.MesoscopicStandalone
import Airy1Gumbel.TailSensitiveNewman
import Airy1Gumbel.TruncatedMoment
import Airy1Gumbel.TwoIntervalLaw
import Airy1Gumbel.TwoPointBound
import Airy1Gumbel.TwoPointSharp
import Airy1Gumbel.TwoPointSharpD
import Airy1Gumbel.TwoPointSharpE
import Airy1Gumbel.TwoPointSharpSqrt
import Airy1Gumbel.UpcrossingRecord
import Airy1Gumbel.UpcrossingTheorem

/-!
# Airy₁ corollaries from flat TASEP

These corollaries instantiate the Airy₁ finite-dimensional law using the GOE left tail.
Their remaining hypotheses are those of the corresponding theorems.
-/

open AiryConj AiryFdd Asymptotics Filter Function HilbertSchmidt MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Asymptotics BigOperators ENNReal NNReal Topology

namespace Airy1Gumbel

theorem airy1Fdd_map_restrict₂_no_fdd_input (hGoe : GOELeftTail)
    {I J : Finset ℝ} (hJI : J ⊆ I) :
    (airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe) I).map (Finset.restrict₂ (π := fun _ : ℝ => ℝ) hJI) = airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe) J :=
  @airy1Fdd_map_restrict₂ (airy1FddPositive_of_goeLeftTail hGoe) I J hJI

theorem isProjectiveMeasureFamily_airy1Fdd_no_fdd_input (hGoe : GOELeftTail) :
    IsProjectiveMeasureFamily (α := fun _ : ℝ => ℝ) (airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe)) :=
  @isProjectiveMeasureFamily_airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe)

theorem isProjectiveLimit_airy1Law_no_fdd_input (hGoe : GOELeftTail) :
    IsProjectiveLimit (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)) (airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe)) :=
  @isProjectiveLimit_airy1Law (airy1FddPositive_of_goeLeftTail hGoe)

theorem airy1Law_map_restrict_no_fdd_input (hGoe : GOELeftTail)
    (I : Finset ℝ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).map I.restrict = airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe) I :=
  @airy1Law_map_restrict (airy1FddPositive_of_goeLeftTail hGoe) I

theorem eq_airy1Law_of_isProjectiveLimit_no_fdd_input (hGoe : GOELeftTail)
    {μ : Measure (ℝ → ℝ)}
    (hμ : IsProjectiveLimit μ (airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe))) : μ = airy1Law (airy1FddPositive_of_goeLeftTail hGoe) :=
  @eq_airy1Law_of_isProjectiveLimit (airy1FddPositive_of_goeLeftTail hGoe) μ hμ

theorem airy1Law_orthant_no_fdd_input (hGoe : GOELeftTail)
    (I : Finset ℝ) (x : I → ℝ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f | ∀ t : I, f t ≤ x t} = AiryFdd.airy1FinCdf I x :=
  @airy1Law_orthant (airy1FddPositive_of_goeLeftTail hGoe) I x

theorem airy1Law_fdd_no_fdd_input (hGoe : GOELeftTail)
    (I : Finset ℝ) (y : ℝ → ℝ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f | ∀ t ∈ I, f t ≤ y t} = AiryFdd.airy1FinCdf I (fun i => y i) :=
  @airy1Law_fdd (airy1FddPositive_of_goeLeftTail hGoe) I y

theorem eq_airy1Law_of_fdd_no_fdd_input (hGoe : GOELeftTail)
    (μ : Measure (ℝ → ℝ))
    [IsProbabilityMeasure μ]
    (hμ : ∀ (I : Finset ℝ) (y : ℝ → ℝ),
      μ.real {f | ∀ t ∈ I, f t ≤ y t} = AiryFdd.airy1FinCdf I (fun i => y i)) :
    μ = airy1Law (airy1FddPositive_of_goeLeftTail hGoe) :=
  @eq_airy1Law_of_fdd (airy1FddPositive_of_goeLeftTail hGoe) μ inferInstance hμ

theorem airy1Law_map_timeShift_no_fdd_input (hGoe : GOELeftTail)
    (c : ℝ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).map (timeShift c) = airy1Law (airy1FddPositive_of_goeLeftTail hGoe) :=
  @airy1Law_map_timeShift (airy1FddPositive_of_goeLeftTail hGoe) c

theorem pairStationary_airy1Process_no_fdd_input (hGoe : GOELeftTail) :
    PairStationary (airy1Process (airy1FddPositive_of_goeLeftTail hGoe)) :=
  @pairStationary_airy1Process (airy1FddPositive_of_goeLeftTail hGoe)

theorem measurableSet_meshEvent_no_fdd_input (hGoe : GOELeftTail)
    (x T M : ℝ) (n : ℕ) :
    MeasurableSet (meshEvent (airy1FddPositive_of_goeLeftTail hGoe) x T M n) :=
  @measurableSet_meshEvent (airy1FddPositive_of_goeLeftTail hGoe) x T M n

theorem antitone_meshEvent_no_fdd_input (hGoe : GOELeftTail)
    (x T M : ℝ) :
    Antitone (meshEvent (airy1FddPositive_of_goeLeftTail hGoe) x T M) :=
  @antitone_meshEvent (airy1FddPositive_of_goeLeftTail hGoe) x T M

theorem setOf_forall_Icc_le_eq_iInter_no_fdd_input (hGoe : GOELeftTail)
    {x T M : ℝ} (hx : 0 ≤ x)
    (hT : 0 < T) :
    {f | ∀ t ∈ Icc x (x + T), airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) t f ≤ M} = ⋂ n, meshEvent (airy1FddPositive_of_goeLeftTail hGoe) x T M n :=
  @setOf_forall_Icc_le_eq_iInter (airy1FddPositive_of_goeLeftTail hGoe) x T M hx hT

theorem airy1Law_meshEvent_no_fdd_input (hT : GOELeftTail)
    (x T M : ℝ) (n : ℕ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real (meshEvent (airy1FddPositive_of_goeLeftTail hT) x T M n)
      = AiryFdd.airy1FinCdf (AiryFdd.meshSet x T n) (fun _ => M) :=
  @airy1Law_meshEvent (airy1FddPositive_of_goeLeftTail hT) hT x T M n

theorem airy1Law_sup_le_eq_fredholmDet_at_weight_no_fdd_input (hT : GOELeftTail)
    {x M T a : ℝ}
    (hx : 0 ≤ x) (hT0 : 0 < T) (hM : 0 < M)
    (ha : T + 1 ≤ a) (hK : AiryFdd.MeshHittingLimit M T) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ t ∈ Icc x (x + T), airy1ContR (airy1FddPositive_of_goeLeftTail hT) t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (AiryConj.airyTildeOp M T a hT0 hM ha) 1 :=
  @airy1Law_sup_le_eq_fredholmDet_at_weight (airy1FddPositive_of_goeLeftTail hT) hT x M T a hx hT0 hM ha hK

theorem airy1Law_sup_le_eq_fredholmDet_no_fdd_input (hT : GOELeftTail)
    {x M T : ℝ}
    (hx : 0 ≤ x) (hT1 : 1 ≤ T) (hM : 0 < M) (hK : AiryFdd.MeshHittingLimit M T) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ t ∈ Icc x (x + T), airy1ContR (airy1FddPositive_of_goeLeftTail hT) t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1 :=
  @airy1Law_sup_le_eq_fredholmDet (airy1FddPositive_of_goeLeftTail hT) hT x M T hx hT1 hM hK

theorem airy1BlockMax_zero_le_iff_no_fdd_input (hGoe : GOELeftTail)
    (f : ℝ → ℝ) (u : ℝ) :
    airy1BlockMax (airy1FddPositive_of_goeLeftTail hGoe) 0 f ≤ u ↔ ∀ t ∈ Icc (0 : ℝ) (0 + 1), airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) t f ≤ u :=
  @airy1BlockMax_zero_le_iff (airy1FddPositive_of_goeLeftTail hGoe) f u

theorem qrUnitBlockLaw_airy1_no_fdd_input (hT : GOELeftTail)
    (hK : ∀ M > 0, AiryFdd.MeshHittingLimit M 1) :
    QRUnitBlockLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)) :=
  @qrUnitBlockLaw_airy1 (airy1FddPositive_of_goeLeftTail hT) hT hK

theorem qrTwoBlockLaw_airy1_no_fdd_input (hT : GOELeftTail)
    (hK₂ : ∀ M > 0, AiryFdd.MeshHittingLimit M 2) :
    QRTwoBlockLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)) :=
  @qrTwoBlockLaw_airy1 (airy1FddPositive_of_goeLeftTail hT) hT hK₂

theorem gumbel_limit_continuum_real_normalized_airy1_of_QR₇_no_fdd_input (hT : GOELeftTail)
    (hK : ∀ M > 0, AiryFdd.MeshHittingLimit M 1)
    (hK₂ : ∀ M > 0, AiryFdd.MeshHittingLimit M 2)
    (two : QRTwoIntervalLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)))
    (M : CubicStrongMixing (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (Cov : CubicCovarianceDecay (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT))
    (As : ProcessAssociated (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (U : HighLevelUpcrossingTail (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT))
    (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  @gumbel_limit_continuum_real_normalized_airy1_of_QR₇ (airy1FddPositive_of_goeLeftTail hT) hT hK hK₂ two M Cov As
    U z

theorem airy1Law_sup_le_eq_fredholmDet_at_weight'_no_fdd_input (hLeft : GOELeftTail)
    {x M T a : ℝ} (hx : 0 ≤ x) (hT : 0 < T) (hM : 0 < M) (ha : T + 1 ≤ a) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hLeft)).real {f | ∀ t ∈ Icc x (x + T), airy1ContR (airy1FddPositive_of_goeLeftTail hLeft) t f ≤ M}
      = HilbertSchmidt.fredholmDet (AiryConj.airyTildeOp M T a hT hM ha) 1 :=
  @airy1Law_sup_le_eq_fredholmDet_at_weight' (airy1FddPositive_of_goeLeftTail hLeft) hLeft x M T a hx hT hM ha

theorem airy1Law_sup_le_eq_fredholmDet'_no_fdd_input (hT : GOELeftTail)
    {x M T : ℝ}
    (hx : 0 ≤ x) (hT1 : 1 ≤ T) (hM : 0 < M) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ t ∈ Icc x (x + T), airy1ContR (airy1FddPositive_of_goeLeftTail hT) t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1 :=
  @airy1Law_sup_le_eq_fredholmDet' (airy1FddPositive_of_goeLeftTail hT) hT x M T hx hT1 hM

theorem airy1Law_interval_tail_sub_traceLead_isLittleO_no_fdd_input (hLeft : GOELeftTail)
    (T : ℝ) (hT : 0 < T) :
    (fun M : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hLeft)).real {f | ∃ t ∈ Icc (0 : ℝ) T, M < airy1ContR (airy1FddPositive_of_goeLeftTail hLeft) t f}
      - AiryConj.traceLead M T) =o[atTop] (fun M => AiryConj.rhoM M / M) :=
  @airy1Law_interval_tail_sub_traceLead_isLittleO (airy1FddPositive_of_goeLeftTail hLeft) hLeft T hT

theorem qrUnitBlockLaw_airy1'_no_fdd_input (hT : GOELeftTail) :
    QRUnitBlockLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)) :=
  @qrUnitBlockLaw_airy1' (airy1FddPositive_of_goeLeftTail hT) hT

theorem qrTwoBlockLaw_airy1'_no_fdd_input (hT : GOELeftTail) :
    QRTwoBlockLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)) :=
  @qrTwoBlockLaw_airy1' (airy1FddPositive_of_goeLeftTail hT) hT

theorem gumbel_limit_continuum_real_normalized_airy1_of_QR₈_no_fdd_input (hT : GOELeftTail)
    (two : QRTwoIntervalLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)))
    (M : CubicStrongMixing (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (Cov : CubicCovarianceDecay (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT))
    (As : ProcessAssociated (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (U : HighLevelUpcrossingTail (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT))
    (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  @gumbel_limit_continuum_real_normalized_airy1_of_QR₈ (airy1FddPositive_of_goeLeftTail hT) hT two M Cov As U z

theorem block_modulus_airy1_no_fdd_input (hT : GOELeftTail)
    (L : NonnegativeWindowModulusEstimate (airy1Law (airy1FddPositive_of_goeLeftTail hT)) (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A) :
    ∃ C c h₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < h₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ h₀ →
        (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real
          {f | ∃ x y : ℝ, x ∈ Icc (0 : ℝ) 1 ∧ y ∈ Icc (0 : ℝ) 1 ∧
            |x - y| ≤ 2 * δ ∧ 1 < |airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - airy1ContR (airy1FddPositive_of_goeLeftTail hT) y f|}
          ≤ C * δ⁻¹ * Real.exp (-c * δ ^ (-(1 / 2 : ℝ))) :=
  @block_modulus_airy1 (airy1FddPositive_of_goeLeftTail hT) hT L

theorem airy1SRP_ae_eq_airy1Process_no_fdd_input (hT : GOELeftTail)
    (t : ℝ) :
    (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A t =ᵐ[airy1Law (airy1FddPositive_of_goeLeftTail hT)] (airy1Process (airy1FddPositive_of_goeLeftTail hT)).A t :=
  @airy1SRP_ae_eq_airy1Process (airy1FddPositive_of_goeLeftTail hT) hT t

theorem cubicStrongMixing_airy1SRP_iff_no_fdd_input (hT : GOELeftTail) :
    Nonempty (CubicStrongMixing (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) ↔
      Nonempty (CubicStrongMixing (airy1Process (airy1FddPositive_of_goeLeftTail hT))) :=
  @cubicStrongMixing_airy1SRP_iff (airy1FddPositive_of_goeLeftTail hT) hT

theorem cubicCovarianceDecay_airy1SRP_iff_no_fdd_input (hT : GOELeftTail) :
    Nonempty (CubicCovarianceDecay (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) ↔
      Nonempty (CubicCovarianceDecay (airy1Process (airy1FddPositive_of_goeLeftTail hT))) :=
  @cubicCovarianceDecay_airy1SRP_iff (airy1FddPositive_of_goeLeftTail hT) hT

theorem processAssociated_airy1SRP_iff_no_fdd_input (hT : GOELeftTail) :
    ProcessAssociated (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT) ↔ ProcessAssociated (airy1Process (airy1FddPositive_of_goeLeftTail hT)) :=
  @processAssociated_airy1SRP_iff (airy1FddPositive_of_goeLeftTail hT) hT

theorem gumbel_limit_continuum_real_normalized_airy1_final_coord_no_fdd_input (hT : GOELeftTail)
    (M : CubicStrongMixing (airy1Process (airy1FddPositive_of_goeLeftTail hT))) (Cov : CubicCovarianceDecay (airy1Process (airy1FddPositive_of_goeLeftTail hT)))
    (As : ProcessAssociated (airy1Process (airy1FddPositive_of_goeLeftTail hT))) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ x ∈ Icc (0 : ℝ) T,
        (airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - gumbelAR T) / gumbelBR T ≤ z}) atTop
      (nhds (Real.exp (-Real.exp (-z)))) :=
  @gumbel_limit_continuum_real_normalized_airy1_final_coord (airy1FddPositive_of_goeLeftTail hT) hT M Cov As z

theorem isEmpty_localModulusEstimate_airy1Process_no_fdd_input (hGoe : GOELeftTail) :
    IsEmpty (LocalModulusEstimate (airy1Process (airy1FddPositive_of_goeLeftTail hGoe))) :=
  @isEmpty_localModulusEstimate_airy1Process (airy1FddPositive_of_goeLeftTail hGoe)

theorem airy1ContR_of_nonneg_no_fdd_input (hGoe : GOELeftTail)
    {x : ℝ} (hx : 0 ≤ x) :
    airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) x = airy1Cont (airy1FddPositive_of_goeLeftTail hGoe) x.toNNReal :=
  @airy1ContR_of_nonneg (airy1FddPositive_of_goeLeftTail hGoe) x hx

theorem airy1ContR_of_not_nonneg_no_fdd_input (hGoe : GOELeftTail)
    {x : ℝ} (hx : ¬ 0 ≤ x) :
    airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) x = fun f => f x :=
  @airy1ContR_of_not_nonneg (airy1FddPositive_of_goeLeftTail hGoe) x hx

theorem measurable_airy1ContR_no_fdd_input (hGoe : GOELeftTail)
    (x : ℝ) : Measurable (airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) x) :=
  @measurable_airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) x

theorem airy1ContR_ae_eq_no_fdd_input (hT : GOELeftTail)
    (x : ℝ) :
    airy1ContR (airy1FddPositive_of_goeLeftTail hT) x =ᵐ[airy1Law (airy1FddPositive_of_goeLeftTail hT)] fun f => f x :=
  @airy1ContR_ae_eq (airy1FddPositive_of_goeLeftTail hT) hT x

theorem continuousOn_airy1ContR_no_fdd_input (hGoe : GOELeftTail)
    (f : ℝ → ℝ) :
    ContinuousOn (fun x => airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) x f) (Ici 0) :=
  @continuousOn_airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) f

theorem airy1BlockMax_gt_iff_no_fdd_input (hGoe : GOELeftTail)
    (j : ℕ) (f : ℝ → ℝ) (u : ℝ) :
    u < airy1BlockMax (airy1FddPositive_of_goeLeftTail hGoe) j f ↔
      ∃ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) 1 ∧ u < airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) (q + j) f :=
  @airy1BlockMax_gt_iff (airy1FddPositive_of_goeLeftTail hGoe) j f u

theorem measurable_airy1BlockMax_no_fdd_input (hGoe : GOELeftTail)
    (j : ℕ) :
    Measurable (airy1BlockMax (airy1FddPositive_of_goeLeftTail hGoe) j) :=
  @measurable_airy1BlockMax (airy1FddPositive_of_goeLeftTail hGoe) j

theorem airy1CMax_Y_no_fdd_input (hGoe : GOELeftTail) : airy1BlockMax (airy1FddPositive_of_goeLeftTail hGoe) = (airy1CMax (airy1FddPositive_of_goeLeftTail hGoe)).Y :=
  @airy1CMax_Y (airy1FddPositive_of_goeLeftTail hGoe)

theorem airy1Law_timeShift_preimage_no_fdd_input (hGoe : GOELeftTail)
    (c : ℝ) {E : Set (ℝ → ℝ)}
    (hE : MeasurableSet E) : airy1Law (airy1FddPositive_of_goeLeftTail hGoe) (timeShift c ⁻¹' E) = airy1Law (airy1FddPositive_of_goeLeftTail hGoe) E :=
  @airy1Law_timeShift_preimage (airy1FddPositive_of_goeLeftTail hGoe) c E hE

theorem ae_airy1ContR_rat_no_fdd_input (hT : GOELeftTail) :
    ∀ᵐ f ∂airy1Law (airy1FddPositive_of_goeLeftTail hT), ∀ q : ℚ, ∀ j : ℕ, airy1ContR (airy1FddPositive_of_goeLeftTail hT) (q + j) f = f (q + j) :=
  @ae_airy1ContR_rat (airy1FddPositive_of_goeLeftTail hT) hT

theorem airy1BlockMax_event_ae_no_fdd_input (hT : GOELeftTail)
    (u : ℝ) (j : ℕ) :
    {f | airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) j f > u} =ᵐ[airy1Law (airy1FddPositive_of_goeLeftTail hT)] ratExc u j :=
  @airy1BlockMax_event_ae (airy1FddPositive_of_goeLeftTail hT) hT u j

theorem airy1BlockMax_stat_marginal_no_fdd_input (hT : GOELeftTail)
    (u : ℝ) (i : ℕ) :
    airy1Law (airy1FddPositive_of_goeLeftTail hT) {f | airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) i f > u} = airy1Law (airy1FddPositive_of_goeLeftTail hT) {f | airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) 0 f > u} :=
  @airy1BlockMax_stat_marginal (airy1FddPositive_of_goeLeftTail hT) hT u i

theorem airy1BlockMax_stat_pair_no_fdd_input (hT : GOELeftTail)
    (u : ℝ) (i d : ℕ) :
    airy1Law (airy1FddPositive_of_goeLeftTail hT) {f | airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) i f > u ∧ airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) (i + d) f > u}
      = airy1Law (airy1FddPositive_of_goeLeftTail hT) {f | airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) 0 f > u ∧ airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) d f > u} :=
  @airy1BlockMax_stat_pair (airy1FddPositive_of_goeLeftTail hT) hT u i d

theorem airy1SRP_A_no_fdd_input (hT : GOELeftTail) :
    (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A = (airy1CMax (airy1FddPositive_of_goeLeftTail hT)).A :=
  @airy1SRP_A (airy1FddPositive_of_goeLeftTail hT) hT

theorem pairStationary_airy1SRP_no_fdd_input (hT : GOELeftTail) :
    PairStationary (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT) :=
  @pairStationary_airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT

theorem isEmpty_localModulusEstimate_airy1SRP_no_fdd_input (hT : GOELeftTail) :
    IsEmpty (LocalModulusEstimate (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) :=
  @isEmpty_localModulusEstimate_airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT

theorem gumbel_limit_continuum_real_normalized_airy1_no_fdd_input (hT : GOELeftTail)
    (qr : QRUnitBlockLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)))
    (qr₂ : QRTwoBlockLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)))
    (two : QRTwoIntervalLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)))
    (mesoscopic : ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
      Tendsto (fun N : ℕ =>
        (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) 0 f > gumbelU N z ∧
            airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) j f > gumbelU N z}) atTop (𝓝 0))
    (M : CubicStrongMixing (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  @gumbel_limit_continuum_real_normalized_airy1 (airy1FddPositive_of_goeLeftTail hT) hT qr qr₂ two mesoscopic M z

theorem isKolmogorovProcess_windowProc_no_fdd_input (hGoe : GOELeftTail)
    {L U C C' p : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C) (hR : RevDefectBound L C')
    (hp : 1 < p) (a : ℝ) :
    IsKolmogorovProcess (windowProc L U a) (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)) p ((p - 1) / 2)
      (truncMomentConst (C + C') (U - L) p).toNNReal :=
  @isKolmogorovProcess_windowProc (airy1FddPositive_of_goeLeftTail hGoe) L U C C' p hLU hC hC' hF hR hp a

theorem window_tail_le_no_fdd_input (hGoe : GOELeftTail)
    {L K C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hF : FwdDefectBound L C) (hR : RevDefectBound L C') (hK : 0 < K) (hLK : L ≤ K / 2)
    (a : ℝ) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) {f : ℝ → ℝ | f a ≤ K / 2 ∧ ∃ s ∈ winPts, K < f (a + s)}
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (K - L) 4
          * (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal / (K / 2) ^ (4 : ℝ)) :=
  @window_tail_le (airy1FddPositive_of_goeLeftTail hGoe) L K C C' hC hC' hF hR hK hLK a

theorem airy1Law_gt_eq_no_fdd_input (hGoe : GOELeftTail)
    (x c : ℝ) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) {f : ℝ → ℝ | c < f x}
      = ENNReal.ofReal (1 - AiryFdd.airy1FinCdf {0} (fun _ => c)) :=
  @airy1Law_gt_eq (airy1FddPositive_of_goeLeftTail hGoe) x c

theorem measure_unbddEvent_le_no_fdd_input (hGoe : GOELeftTail)
    {L C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hF : FwdDefectBound L C) (hR : RevDefectBound L C') (N : ℕ) {K : ℝ} (hK : 0 < K)
    (hLK : L ≤ K / 2) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) (unbddEvent N)
      ≤ ENNReal.ofReal (((N : ℝ) + 1) * ((1 - AiryFdd.airy1FinCdf {0} (fun _ => K / 2))
          + truncMomentConst (C + C') (K - L) 4
            * (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal / (K / 2) ^ (4 : ℝ))) :=
  @measure_unbddEvent_le (airy1FddPositive_of_goeLeftTail hGoe) L C C' hC hC' hF hR N K hK hLK

theorem airy1Law_unbddEvent_no_fdd_input (hGoe : GOELeftTail)
    (N : ℕ) : airy1Law (airy1FddPositive_of_goeLeftTail hGoe) (unbddEvent N) = 0 :=
  @airy1Law_unbddEvent (airy1FddPositive_of_goeLeftTail hGoe) N

theorem ae_bddAbove_rat_no_fdd_input (hGoe : GOELeftTail) :
    ∀ᵐ f ∂airy1Law (airy1FddPositive_of_goeLeftTail hGoe), ∀ N : ℕ, ∃ B : ℕ, ∀ q : ℚ, Real.toNNReal q ≤ N →
      f (Real.toNNReal q) ≤ (B : ℝ) :=
  @ae_bddAbove_rat (airy1FddPositive_of_goeLeftTail hGoe)

theorem exists_holder_modification_clamp_no_fdd_input (hGoe : GOELeftTail)
    (L U : ℝ) (hLU : L ≤ U) :
    ∃ Y : ℝ≥0 → (ℝ → ℝ) → ℝ, (∀ t, Measurable (Y t))
      ∧ (∀ t, Y t =ᵐ[airy1Law (airy1FddPositive_of_goeLeftTail hGoe)] fun f => clampTo L U (f t))
      ∧ ∀ f t (β : ℝ≥0), 0 < β → (β : ℝ) < 1 / 2 →
        ∃ V ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · f) V :=
  @exists_holder_modification_clamp (airy1FddPositive_of_goeLeftTail hGoe) L U hLU

theorem measurable_clampMod_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) (n : ℕ) (t : ℝ≥0) :
    Measurable (clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n t) :=
  @measurable_clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n t

theorem clampMod_ae_eq_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) (n : ℕ) (t : ℝ≥0) :
    clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n t =ᵐ[airy1Law (airy1FddPositive_of_goeLeftTail hGoe)] fun f => clampTo L (L + n) (f t) :=
  @clampMod_ae_eq (airy1FddPositive_of_goeLeftTail hGoe) L n t

theorem holder_clampMod_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) (n : ℕ) (f : ℝ → ℝ) (t : ℝ≥0)
    (β : ℝ≥0) (hβ : 0 < β) (hβ2 : (β : ℝ) < 1 / 2) :
    ∃ V ∈ 𝓝 t, ∃ C, HolderOnWith C β (clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n · f) V :=
  @holder_clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n f t β hβ hβ2

theorem continuous_clampMod_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) (n : ℕ) (f : ℝ → ℝ) :
    Continuous (clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n · f) :=
  @continuous_clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n f

theorem measurableSet_goodSet_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) :
    MeasurableSet (goodSet (airy1FddPositive_of_goeLeftTail hGoe) L) :=
  @measurableSet_goodSet (airy1FddPositive_of_goeLeftTail hGoe) L

theorem ae_mem_goodSet_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) : ∀ᵐ f ∂airy1Law (airy1FddPositive_of_goeLeftTail hGoe), f ∈ goodSet (airy1FddPositive_of_goeLeftTail hGoe) L :=
  @ae_mem_goodSet (airy1FddPositive_of_goeLeftTail hGoe) L

theorem clampMod_eq_clampTo_no_fdd_input (hGoe : GOELeftTail)
    {L : ℝ} {f : ℝ → ℝ} (hf : f ∈ goodSet (airy1FddPositive_of_goeLeftTail hGoe) L) {n m : ℕ} (hnm : n ≤ m) (t : ℝ≥0) :
    clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n t f = clampTo L (L + n) (clampMod (airy1FddPositive_of_goeLeftTail hGoe) L m t f) :=
  @clampMod_eq_clampTo (airy1FddPositive_of_goeLeftTail hGoe) L f hf n m hnm t

theorem clampMod_mem_no_fdd_input (hGoe : GOELeftTail)
    {L : ℝ} {f : ℝ → ℝ} (hf : f ∈ goodSet (airy1FddPositive_of_goeLeftTail hGoe) L) (n : ℕ) (t : ℝ≥0) :
    clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n t f ∈ Icc L (L + n) :=
  @clampMod_mem (airy1FddPositive_of_goeLeftTail hGoe) L f hf n t

theorem clampMod_mono_no_fdd_input (hGoe : GOELeftTail)
    {L : ℝ} {f : ℝ → ℝ} (hf : f ∈ goodSet (airy1FddPositive_of_goeLeftTail hGoe) L) {n m : ℕ} (hnm : n ≤ m) (t : ℝ≥0) :
    clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n t f ≤ clampMod (airy1FddPositive_of_goeLeftTail hGoe) L m t f :=
  @clampMod_mono (airy1FddPositive_of_goeLeftTail hGoe) L f hf n m hnm t

theorem clampMod_le_of_bound_no_fdd_input (hGoe : GOELeftTail)
    {L : ℝ} {f : ℝ → ℝ} (hf : f ∈ goodSet (airy1FddPositive_of_goeLeftTail hGoe) L) {N B : ℕ}
    (hB : ∀ q : ℚ, Real.toNNReal q ≤ N → f (Real.toNNReal q) ≤ (B : ℝ)) (n : ℕ) {t : ℝ≥0}
    (ht : t < N) : clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n t f ≤ max L B :=
  @clampMod_le_of_bound (airy1FddPositive_of_goeLeftTail hGoe) L f hf N B hB n t ht

theorem exists_clampMod_stable_no_fdd_input (hGoe : GOELeftTail)
    {L : ℝ} {f : ℝ → ℝ} (hf : f ∈ goodSet (airy1FddPositive_of_goeLeftTail hGoe) L) (N : ℕ) :
    ∃ n₀ : ℕ, ∀ t : ℝ≥0, t < N → ∀ m : ℕ, clampMod (airy1FddPositive_of_goeLeftTail hGoe) L m t f ≤ clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n₀ t f
      ∧ (n₀ ≤ m → clampMod (airy1FddPositive_of_goeLeftTail hGoe) L m t f = clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n₀ t f) :=
  @exists_clampMod_stable (airy1FddPositive_of_goeLeftTail hGoe) L f hf N

theorem measurable_airy1ContL_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) (t : ℝ≥0) :
    Measurable (airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) L t) :=
  @measurable_airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) L t

theorem airy1ContL_eq_clampMod_no_fdd_input (hGoe : GOELeftTail)
    {L : ℝ} {f : ℝ → ℝ}
    (hf : f ∈ goodSet (airy1FddPositive_of_goeLeftTail hGoe) L) (N : ℕ) :
    ∃ n₀ : ℕ, ∀ t : ℝ≥0, t < N → airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) L t f = clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n₀ t f :=
  @airy1ContL_eq_clampMod (airy1FddPositive_of_goeLeftTail hGoe) L f hf N

theorem airy1ContL_eventuallyEq_no_fdd_input (hGoe : GOELeftTail)
    {L : ℝ} {f : ℝ → ℝ}
    (hf : f ∈ goodSet (airy1FddPositive_of_goeLeftTail hGoe) L) (t : ℝ≥0) :
    ∃ n₀ : ℕ, ∃ V ∈ 𝓝 t, ∀ s ∈ V, airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) L s f = clampMod (airy1FddPositive_of_goeLeftTail hGoe) L n₀ s f :=
  @airy1ContL_eventuallyEq (airy1FddPositive_of_goeLeftTail hGoe) L f hf t

theorem continuous_airy1ContL_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) (f : ℝ → ℝ) :
    Continuous (airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) L · f) :=
  @continuous_airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) L f

theorem holder_airy1ContL_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) (f : ℝ → ℝ) (t : ℝ≥0) (β : ℝ≥0)
    (hβ : 0 < β) (hβ2 : (β : ℝ) < 1 / 2) :
    ∃ V ∈ 𝓝 t, ∃ C, HolderOnWith C β (airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) L · f) V :=
  @holder_airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) L f t β hβ hβ2

theorem airy1ContL_ge_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) (t : ℝ≥0) (f : ℝ → ℝ) :
    L ≤ airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) L t f :=
  @airy1ContL_ge (airy1FddPositive_of_goeLeftTail hGoe) L t f

theorem airy1ContL_ae_eq_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) (t : ℝ≥0) :
    airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) L t =ᵐ[airy1Law (airy1FddPositive_of_goeLeftTail hGoe)] fun f => max L (f t) :=
  @airy1ContL_ae_eq (airy1FddPositive_of_goeLeftTail hGoe) L t

theorem exists_continuous_version_max_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) :
    ∃ A : ℝ≥0 → (ℝ → ℝ) → ℝ, (∀ t, Measurable (A t))
      ∧ (∀ t, A t =ᵐ[airy1Law (airy1FddPositive_of_goeLeftTail hGoe)] fun f => max L (f t))
      ∧ (∀ f, Continuous (A · f))
      ∧ (∀ f t, L ≤ A t f)
      ∧ ∀ f t (β : ℝ≥0), 0 < β → (β : ℝ) < 1 / 2 →
        ∃ V ∈ 𝓝 t, ∃ C, HolderOnWith C β (A · f) V :=
  @exists_continuous_version_max (airy1FddPositive_of_goeLeftTail hGoe) L

theorem isProbabilityMeasure_airy1Fdd_no_fdd_input (hGoe : GOELeftTail)
    (I : Finset ℝ) :
    IsProbabilityMeasure (airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe) I) :=
  @isProbabilityMeasure_airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe) I

theorem airy1Fdd_orthant_no_fdd_input (hGoe : GOELeftTail)
    (I : Finset ℝ) (x : I → ℝ) :
    (airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe) I).real (Set.pi Set.univ fun i => Set.Iic (x i)) = AiryFdd.airy1FinCdf I x :=
  @airy1Fdd_orthant (airy1FddPositive_of_goeLeftTail hGoe) I x

theorem airy1Fdd_unique_no_fdd_input (hGoe : GOELeftTail)
    {I : Finset ℝ} (μ : Measure (I → ℝ))
    [IsProbabilityMeasure μ]
    (hμ : ∀ x : I → ℝ, μ.real (Set.pi Set.univ fun i => Set.Iic (x i))
      = AiryFdd.airy1FinCdf I x) : μ = airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe) I :=
  @airy1Fdd_unique (airy1FddPositive_of_goeLeftTail hGoe) I μ inferInstance hμ

theorem Airy1FddPositive.airy1FinCdf_nonneg_no_fdd_input (hGoe : GOELeftTail)
    (I : Finset ℝ)
    (x : I → ℝ) : 0 ≤ AiryFdd.airy1FinCdf I x :=
  @Airy1FddPositive.airy1FinCdf_nonneg (airy1FddPositive_of_goeLeftTail hGoe) I x

theorem Airy1FddPositive.airy1FinCdf_le_one_no_fdd_input (hGoe : GOELeftTail)
    (I : Finset ℝ)
    (x : I → ℝ) : AiryFdd.airy1FinCdf I x ≤ 1 :=
  @Airy1FddPositive.airy1FinCdf_le_one (airy1FddPositive_of_goeLeftTail hGoe) I x

theorem Airy1FddPositive.monotone_airy1FinCdf_no_fdd_input (hGoe : GOELeftTail)
    (I : Finset ℝ) :
    Monotone (AiryFdd.airy1FinCdf I) :=
  @Airy1FddPositive.monotone_airy1FinCdf (airy1FddPositive_of_goeLeftTail hGoe) I

theorem Airy1FddPositive.tendsto_airy1FinCdf_zero_no_fdd_input (hGoe : GOELeftTail)
    (I : Finset ℝ)
    (t : I) {α : Type*} {l : Filter α} {xn : α → I → ℝ}
    (ht : Tendsto (fun n => xn n t) l atBot) :
    Tendsto (fun n => AiryFdd.airy1FinCdf I (xn n)) l (𝓝 0) :=
  @Airy1FddPositive.tendsto_airy1FinCdf_zero (airy1FddPositive_of_goeLeftTail hGoe) I t α l xn ht

theorem airy1Fdd_singleton_orthant_no_fdd_input (hGoe : GOELeftTail)
    (t : ℝ)
    (x : ({t} : Finset ℝ) → ℝ) :
    (airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe) {t}).real (Set.pi Set.univ fun i => Set.Iic (x i))
      = HilbertSchmidt.fredholmDet (AiryFdd.fsOp (2 * x ⟨t, Finset.mem_singleton_self t⟩)) 1 :=
  @airy1Fdd_singleton_orthant (airy1FddPositive_of_goeLeftTail hGoe) t x

theorem airy1Fdd_map_erase_no_fdd_input (hGoe : GOELeftTail)
    (I : Finset ℝ) {t : ℝ} (ht : t ∈ I) :
    (airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe) I).map (restrictErase I t) = airy1Fdd (airy1FddPositive_of_goeLeftTail hGoe) (I.erase t) :=
  @airy1Fdd_map_erase (airy1FddPositive_of_goeLeftTail hGoe) I t ht

theorem ferrariLiu_event_measurable_airy1_no_fdd_input (hGoe : GOELeftTail)
    (c L : ℝ) (hL : 1 ≤ L) :
    MeasurableSet {f | ∀ x ∈ Icc (0 : ℝ) L, airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) x f ≤ c} :=
  @ferrariLiu_event_measurable_airy1 (airy1FddPositive_of_goeLeftTail hGoe) c L hL

theorem gumbel_limit_continuum_airy1_ferrariLiu_no_fdd_input (hT : GOELeftTail)
    (FL : FerrariLiuPersistence (airy1Law (airy1FddPositive_of_goeLeftTail hT)) (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A) (z : ℝ) :
    Tendsto (fun N : ℕ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real
        {f | ∀ x ∈ Icc (0 : ℝ) N, airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  @gumbel_limit_continuum_airy1_ferrariLiu (airy1FddPositive_of_goeLeftTail hT) hT FL z

theorem gumbel_limit_continuum_real_normalized_airy1_final_no_fdd_input (hT : GOELeftTail)
    (M : CubicStrongMixing (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (Cov : CubicCovarianceDecay (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT))
    (As : ProcessAssociated (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  @gumbel_limit_continuum_real_normalized_airy1_final (airy1FddPositive_of_goeLeftTail hT) hT M Cov As z

theorem mesoscopic_airy1TP_no_fdd_input (hT : GOELeftTail) :
    ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
      Tendsto (fun N : ℕ =>
        (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) 0 f > gumbelU N z ∧
            airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) j f > gumbelU N z}) atTop (𝓝 0) :=
  @mesoscopic_airy1TP (airy1FddPositive_of_goeLeftTail hT) hT

theorem gumbel_limit_continuum_real_normalized_airy1_of_QRTP_no_fdd_input (hT : GOELeftTail)
    (qr : QRUnitBlockLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)))
    (qr₂ : QRTwoBlockLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)))
    (two : QRTwoIntervalLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)))
    (M : CubicStrongMixing (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  @gumbel_limit_continuum_real_normalized_airy1_of_QRTP (airy1FddPositive_of_goeLeftTail hT) hT qr qr₂ two M z

theorem gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_input (hT : GOELeftTail)
    (M : CubicStrongMixing (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  @gumbel_limit_continuum_real_normalized_airy1_final₂ (airy1FddPositive_of_goeLeftTail hT) hT M z

theorem gumbel_limit_continuum_real_normalized_airy1_final₂_coord_no_fdd_input (hT : GOELeftTail)
    (M : CubicStrongMixing (airy1Process (airy1FddPositive_of_goeLeftTail hT))) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ x ∈ Icc (0 : ℝ) T,
        (airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - gumbelAR T) / gumbelBR T ≤ z}) atTop
      (nhds (Real.exp (-Real.exp (-z)))) :=
  @gumbel_limit_continuum_real_normalized_airy1_final₂_coord (airy1FddPositive_of_goeLeftTail hT) hT M z

theorem goeLeftTail_consistent_no_fdd_input (hGoe : GOELeftTail) :
    (∀ M : ℝ, AiryFdd.airy1FinCdf {0} (fun _ => -M) ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun M : ℝ => AiryFdd.airy1FinCdf {0} (fun _ => -M)) atTop (𝓝 0) :=
  @goeLeftTail_consistent (airy1FddPositive_of_goeLeftTail hGoe)

theorem goeLeftTail_iff_eventually_no_fdd_input (hGoe : GOELeftTail) :
    GOELeftTail ↔ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ M in atTop,
      AiryFdd.airy1FinCdf {0} (fun _ => -M) ≤ C * Real.exp (-c * M ^ 3) :=
  @goeLeftTail_iff_eventually (airy1FddPositive_of_goeLeftTail hGoe)

theorem airy1Law_le_eq_no_fdd_input (hGoe : GOELeftTail)
    (t m : ℝ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f t ≤ m} = AiryFdd.airy1FinCdf {0} (fun _ => m) :=
  @airy1Law_le_eq (airy1FddPositive_of_goeLeftTail hGoe) t m

theorem GOELeftTail.airy1Law_le_no_fdd_input (hT : GOELeftTail) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t M : ℝ, 0 ≤ M →
      (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f : ℝ → ℝ | f t ≤ -M} ≤ C * Real.exp (-c * M ^ 3) :=
  @GOELeftTail.airy1Law_le hT (airy1FddPositive_of_goeLeftTail hT)

theorem GOELeftTail.airy1Law_le_ofReal_no_fdd_input (hT : GOELeftTail) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t M : ℝ, 0 ≤ M →
      airy1Law (airy1FddPositive_of_goeLeftTail hT) {f : ℝ → ℝ | f t ≤ -M} ≤ ENNReal.ofReal (C * Real.exp (-c * M ^ 3)) :=
  @GOELeftTail.airy1Law_le_ofReal hT (airy1FddPositive_of_goeLeftTail hT)

theorem airy1Law_fwd_le_on_no_fdd_input (hGoe : GOELeftTail)
    {L δ C : ℝ}
    (hF : AiryFdd.FwdDefectBoundOn L δ C)
    {x t a b : ℝ} (ht : 0 < t) (htδ : t ≤ δ) (ha : L ≤ a) (hab : a ≤ b) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) {f : ℝ → ℝ | f x ≤ a ∧ b < f (x + t)}
      ≤ ENNReal.ofReal (C * Real.exp (-(b - a) ^ 2 / (8 * t))) :=
  @airy1Law_fwd_le_on (airy1FddPositive_of_goeLeftTail hGoe) L δ C hF x t a b ht htδ ha hab

theorem airy1Law_rev_le_on_no_fdd_input (hGoe : GOELeftTail)
    {L δ C : ℝ}
    (hR : AiryFdd.RevDefectBoundOn L δ C)
    {x t a b : ℝ} (ht : 0 < t) (htδ : t ≤ δ) (hb : L ≤ b) (hba : b ≤ a) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) {f : ℝ → ℝ | a < f x ∧ f (x + t) ≤ b}
      ≤ ENNReal.ofReal (C * Real.exp (-(a - b) ^ 2 / (8 * t))) :=
  @airy1Law_rev_le_on (airy1FddPositive_of_goeLeftTail hGoe) L δ C hR x t a b ht htδ hb hba

theorem airy1Law_clamp_gap_le_on_no_fdd_input (hGoe : GOELeftTail)
    {L U δ C C' : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn L δ C)
    (hR : AiryFdd.RevDefectBoundOn L δ C')
    {x t z : ℝ} (ht : 0 < t) (htδ : t ≤ δ) (hz : 0 < z) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) {f : ℝ → ℝ | z < |clampTo L U (f (x + t)) - clampTo L U (f x)|}
      ≤ ENNReal.ofReal ((C + C') * (2 * (U - L) / z + 1) * Real.exp (-z ^ 2 / (32 * t))) :=
  @airy1Law_clamp_gap_le_on (airy1FddPositive_of_goeLeftTail hGoe) L U δ C C' hLU hC hC' hF hR x t z ht htδ hz

theorem lintegral_clamp_incr_rpow_le_on_no_fdd_input (hGoe : GOELeftTail)
    {L U δ C C' p : ℝ}
    (hLU : L ≤ U) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn L δ C)
    (hR : AiryFdd.RevDefectBoundOn L δ C') (hδ1 : δ ≤ 1) (hp : 1 < p) {x t : ℝ} (ht : 0 < t)
    (htδ : t ≤ δ) :
    ∫⁻ f, ENNReal.ofReal (|clampTo L U (f (x + t)) - clampTo L U (f x)| ^ p) ∂airy1Law (airy1FddPositive_of_goeLeftTail hGoe)
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p * t ^ ((p - 1) / 2)) :=
  @lintegral_clamp_incr_rpow_le_on (airy1FddPositive_of_goeLeftTail hGoe) L U δ C C' p hLU hC hC' hF hR hδ1 hp x t
    ht htδ

theorem lintegral_edist_clamp_le_on_of_lt_no_fdd_input (hGoe : GOELeftTail)
    {L U δ C C' p : ℝ}
    (hLU : L ≤ U) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn L δ C)
    (hR : AiryFdd.RevDefectBoundOn L δ C') (hδ1 : δ ≤ 1) (hp : 1 < p) {s u : ℝ} (hsu : s < u)
    (hsuδ : u - s ≤ δ) :
    ∫⁻ f, edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p ∂airy1Law (airy1FddPositive_of_goeLeftTail hGoe)
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p) * edist s u ^ ((p - 1) / 2) :=
  @lintegral_edist_clamp_le_on_of_lt (airy1FddPositive_of_goeLeftTail hGoe) L U δ C C' p hLU hC hC' hF hR hδ1 hp s
    u hsu hsuδ

theorem lintegral_edist_clamp_le_on_no_fdd_input (hGoe : GOELeftTail)
    {L U δ C C' p : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn L δ C)
    (hR : AiryFdd.RevDefectBoundOn L δ C')
    (hδ1 : δ ≤ 1) (hp : 1 < p) {s u : ℝ} (hsuδ : dist s u ≤ δ) :
    ∫⁻ f, edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p ∂airy1Law (airy1FddPositive_of_goeLeftTail hGoe)
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p) * edist s u ^ ((p - 1) / 2) :=
  @lintegral_edist_clamp_le_on (airy1FddPositive_of_goeLeftTail hGoe) L U δ C C' p hLU hC hC' hF hR hδ1 hp s u hsuδ

theorem isKolmogorovProcess_windowProcS_no_fdd_input (hGoe : GOELeftTail)
    {L U δ C C' p ℓ : ℝ}
    (hLU : L ≤ U) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn L δ C)
    (hR : AiryFdd.RevDefectBoundOn L δ C') (hδ1 : δ ≤ 1) (hp : 1 < p) (hℓ : 0 ≤ ℓ) (hℓδ : ℓ ≤ δ)
    (a : ℝ) :
    IsKolmogorovProcess (windowProcS L U a ℓ) (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)) p ((p - 1) / 2)
      (truncMomentConst (C + C') (U - L) p * ℓ ^ ((p - 1) / 2)).toNNReal :=
  @isKolmogorovProcess_windowProcS (airy1FddPositive_of_goeLeftTail hGoe) L U δ C C' p ℓ hLU hC hC' hF hR hδ1 hp hℓ
    hℓδ a

theorem window_low_tail_le_no_fdd_input (hGoe : GOELeftTail)
    {M δ ℓ C C' : ℝ} (hM : 0 < M) (hC : 0 ≤ C)
    (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn (-(2 * M)) δ C)
    (hR : AiryFdd.RevDefectBoundOn (-(2 * M)) δ C')
    (hδ1 : δ ≤ 1) (hℓ : 0 ≤ ℓ) (hℓδ : ℓ ≤ δ) (a : ℝ) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) {f : ℝ → ℝ | -M < f a ∧ ∃ s ∈ winPts, f (a + ℓ * s) < -(2 * M)}
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (2 * M) 4 * ℓ ^ (3 / 2 : ℝ)
          * (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal / M ^ (4 : ℝ)) :=
  @window_low_tail_le (airy1FddPositive_of_goeLeftTail hGoe) M δ ℓ C C' hM hC hC' hF hR hδ1 hℓ hℓδ a

theorem airy1Law_le_eq_ofReal_no_fdd_input (hGoe : GOELeftTail)
    (x c : ℝ) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) {f : ℝ → ℝ | f x ≤ c} = ENNReal.ofReal (AiryFdd.airy1FinCdf {0} (fun _ => c)) :=
  @airy1Law_le_eq_ofReal (airy1FddPositive_of_goeLeftTail hGoe) x c

theorem airy1FinCdf_singleton_nonneg_no_fdd_input (hGoe : GOELeftTail)
    (c : ℝ) :
    0 ≤ AiryFdd.airy1FinCdf {0} (fun _ => c) :=
  @airy1FinCdf_singleton_nonneg (airy1FddPositive_of_goeLeftTail hGoe) c

theorem measure_lowEvent_le_no_fdd_input (hGoe : GOELeftTail)
    {M δ C C' : ℝ} (hM : 0 < M) (hC : 0 ≤ C)
    (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn (-(2 * M)) δ C)
    (hR : AiryFdd.RevDefectBoundOn (-(2 * M)) δ C')
    (hδ1 : δ ≤ 1) (N n : ℕ) (hn : 0 < n) (hnδ : 1 / (n : ℝ) ≤ δ) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) (lowEvent N)
      ≤ ENNReal.ofReal (((n : ℝ) * N + 1) * (AiryFdd.airy1FinCdf {0} (fun _ => -M)
          + truncMomentConst (C + C') (2 * M) 4 * (1 / (n : ℝ)) ^ (3 / 2 : ℝ)
            * (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal / M ^ (4 : ℝ))) :=
  @measure_lowEvent_le (airy1FddPositive_of_goeLeftTail hGoe) M δ C C' hM hC hC' hF hR hδ1 N n hn hnδ

theorem airy1Law_lowEvent_of_no_fdd_input (hGoe : GOELeftTail)
    (hLT : ∃ C c, 0 < C ∧ 0 < c ∧ ∀ M ≥ 0,
      AiryFdd.airy1FinCdf {0} (fun _ => -M) ≤ C * Real.exp (-c * M ^ 3))
    {CM : ℝ → ℝ} {K α : ℝ} (hα : α < 3)
    (hDef : ∀ M ≥ (2 : ℝ), AiryFdd.FwdDefectBoundOn (-(2 * M)) (1 / (2 * M)) (CM M)
      ∧ AiryFdd.RevDefectBoundOn (-(2 * M)) (1 / (2 * M)) (CM M))
    (hCM : ∀ M ≥ (2 : ℝ), Real.log (CM M) ≤ K * M ^ α) (N : ℕ) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) (lowEvent N) = 0 :=
  @airy1Law_lowEvent_of (airy1FddPositive_of_goeLeftTail hGoe) hLT CM K α hα hDef hCM N

theorem ae_bddBelow_rat_of_no_fdd_input (hGoe : GOELeftTail)
    (hlow : ∀ N, airy1Law (airy1FddPositive_of_goeLeftTail hGoe) (lowEvent N) = 0) :
    ∀ᵐ f ∂airy1Law (airy1FddPositive_of_goeLeftTail hGoe), ∀ N : ℕ, ∃ B : ℕ, ∀ q : ℚ, Real.toNNReal q ≤ N →
      -(B : ℝ) ≤ f (Real.toNNReal q) :=
  @ae_bddBelow_rat_of (airy1FddPositive_of_goeLeftTail hGoe) hlow

theorem measurableSet_goodLowSet_no_fdd_input (hGoe : GOELeftTail) : MeasurableSet (goodLowSet (airy1FddPositive_of_goeLeftTail hGoe)) :=
  @measurableSet_goodLowSet (airy1FddPositive_of_goeLeftTail hGoe)

theorem ae_mem_goodLowSet_of_no_fdd_input (hGoe : GOELeftTail)
    (hlow : ∀ N, airy1Law (airy1FddPositive_of_goeLeftTail hGoe) (lowEvent N) = 0) :
    ∀ᵐ f ∂airy1Law (airy1FddPositive_of_goeLeftTail hGoe), f ∈ goodLowSet (airy1FddPositive_of_goeLeftTail hGoe) :=
  @ae_mem_goodLowSet_of (airy1FddPositive_of_goeLeftTail hGoe) hlow

theorem airy1ContL_eq_max_no_fdd_input (hGoe : GOELeftTail)
    {f : ℝ → ℝ} (hf : f ∈ goodLowSet (airy1FddPositive_of_goeLeftTail hGoe)) {m m' : ℕ} (hmm : m ≤ m') (t : ℝ≥0) :
    airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) (-(m : ℝ)) t f = max (-(m : ℝ)) (airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) (-(m' : ℝ)) t f) :=
  @airy1ContL_eq_max (airy1FddPositive_of_goeLeftTail hGoe) f hf m m' hmm t

theorem airy1ContL_ge_of_bound_no_fdd_input (hGoe : GOELeftTail)
    {f : ℝ → ℝ} (hf : f ∈ goodLowSet (airy1FddPositive_of_goeLeftTail hGoe)) {N B : ℕ}
    (hB : ∀ q : ℚ, Real.toNNReal q ≤ N → -(B : ℝ) ≤ f (Real.toNNReal q)) (m : ℕ) {t : ℝ≥0}
    (ht : t < N) : -(B : ℝ) ≤ airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) (-(m : ℝ)) t f :=
  @airy1ContL_ge_of_bound (airy1FddPositive_of_goeLeftTail hGoe) f hf N B hB m t ht

theorem exists_airy1ContL_stable_no_fdd_input (hGoe : GOELeftTail)
    {f : ℝ → ℝ} (hf : f ∈ goodLowSet (airy1FddPositive_of_goeLeftTail hGoe)) (N : ℕ) :
    ∃ m₀ : ℕ, ∀ t : ℝ≥0, t < N → ∀ m : ℕ,
      airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) (-(m₀ : ℝ)) t f ≤ airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) (-(m : ℝ)) t f
      ∧ (m₀ ≤ m → airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) (-(m : ℝ)) t f = airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) (-(m₀ : ℝ)) t f) :=
  @exists_airy1ContL_stable (airy1FddPositive_of_goeLeftTail hGoe) f hf N

theorem measurable_airy1Cont_no_fdd_input (hGoe : GOELeftTail)
    (t : ℝ≥0) :
    Measurable (airy1Cont (airy1FddPositive_of_goeLeftTail hGoe) t) :=
  @measurable_airy1Cont (airy1FddPositive_of_goeLeftTail hGoe) t

theorem airy1Cont_eq_airy1ContL_no_fdd_input (hGoe : GOELeftTail)
    {f : ℝ → ℝ} (hf : f ∈ goodLowSet (airy1FddPositive_of_goeLeftTail hGoe))
    (N : ℕ) : ∃ m₀ : ℕ, ∀ t : ℝ≥0, t < N → airy1Cont (airy1FddPositive_of_goeLeftTail hGoe) t f = airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) (-(m₀ : ℝ)) t f :=
  @airy1Cont_eq_airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) f hf N

theorem airy1Cont_eventuallyEq_no_fdd_input (hGoe : GOELeftTail)
    {f : ℝ → ℝ} (hf : f ∈ goodLowSet (airy1FddPositive_of_goeLeftTail hGoe))
    (t : ℝ≥0) : ∃ m₀ : ℕ, ∃ V ∈ 𝓝 t, ∀ s ∈ V, airy1Cont (airy1FddPositive_of_goeLeftTail hGoe) s f = airy1ContL (airy1FddPositive_of_goeLeftTail hGoe) (-(m₀ : ℝ)) s f :=
  @airy1Cont_eventuallyEq (airy1FddPositive_of_goeLeftTail hGoe) f hf t

theorem continuous_airy1Cont_no_fdd_input (hGoe : GOELeftTail)
    (f : ℝ → ℝ) :
    Continuous (airy1Cont (airy1FddPositive_of_goeLeftTail hGoe) · f) :=
  @continuous_airy1Cont (airy1FddPositive_of_goeLeftTail hGoe) f

theorem holder_airy1Cont_no_fdd_input (hGoe : GOELeftTail)
    (f : ℝ → ℝ) (t : ℝ≥0) (β : ℝ≥0)
    (hβ : 0 < β) (hβ2 : (β : ℝ) < 1 / 2) :
    ∃ V ∈ 𝓝 t, ∃ C, HolderOnWith C β (airy1Cont (airy1FddPositive_of_goeLeftTail hGoe) · f) V :=
  @holder_airy1Cont (airy1FddPositive_of_goeLeftTail hGoe) f t β hβ hβ2

theorem airy1Cont_ae_eq_of_no_fdd_input (hGoe : GOELeftTail)
    (hlow : ∀ N, airy1Law (airy1FddPositive_of_goeLeftTail hGoe) (lowEvent N) = 0)
    (t : ℝ≥0) : airy1Cont (airy1FddPositive_of_goeLeftTail hGoe) t =ᵐ[airy1Law (airy1FddPositive_of_goeLeftTail hGoe)] fun f => f t :=
  @airy1Cont_ae_eq_of (airy1FddPositive_of_goeLeftTail hGoe) hlow t

theorem airy1Law_lowEvent_no_fdd_input (hT : GOELeftTail)
    (N : ℕ) :
    airy1Law (airy1FddPositive_of_goeLeftTail hT) (lowEvent N) = 0 :=
  @airy1Law_lowEvent (airy1FddPositive_of_goeLeftTail hT) hT N

theorem ae_bddBelow_rat_no_fdd_input (hT : GOELeftTail) :
    ∀ᵐ f ∂airy1Law (airy1FddPositive_of_goeLeftTail hT), ∀ N : ℕ, ∃ B : ℕ, ∀ q : ℚ, Real.toNNReal q ≤ N →
      -(B : ℝ) ≤ f (Real.toNNReal q) :=
  @ae_bddBelow_rat (airy1FddPositive_of_goeLeftTail hT) hT

theorem airy1Cont_ae_eq_no_fdd_input (hT : GOELeftTail)
    (t : ℝ≥0) :
    airy1Cont (airy1FddPositive_of_goeLeftTail hT) t =ᵐ[airy1Law (airy1FddPositive_of_goeLeftTail hT)] fun f => f t :=
  @airy1Cont_ae_eq (airy1FddPositive_of_goeLeftTail hT) hT t

theorem exists_continuous_version_no_fdd_input (hT : GOELeftTail) :
    ∃ A : ℝ≥0 → (ℝ → ℝ) → ℝ, (∀ t, Measurable (A t))
      ∧ (∀ t, A t =ᵐ[airy1Law (airy1FddPositive_of_goeLeftTail hT)] fun f => f t)
      ∧ (∀ f, Continuous (A · f))
      ∧ ∀ f t (β : ℝ≥0), 0 < β → (β : ℝ) < 1 / 2 →
        ∃ V ∈ 𝓝 t, ∃ C, HolderOnWith C β (A · f) V :=
  @exists_continuous_version (airy1FddPositive_of_goeLeftTail hT) hT

theorem block_oscillation_probability_shift_airy1_no_fdd_input (hT : GOELeftTail)
    (j : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real (unit_block_oscillation_event (airy1FddPositive_of_goeLeftTail hT) j δ) =
      (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real (unit_block_oscillation_event (airy1FddPositive_of_goeLeftTail hT) 0 δ) :=
  @block_oscillation_probability_shift_airy1 (airy1FddPositive_of_goeLeftTail hT) hT j δ hδ

theorem block_pair_grid_cover_airy1_no_fdd_input (hGoe : GOELeftTail)
    (j n : ℕ) (hn : 0 < n)
    (δ M : ℝ) (hmesh : 1 / (n : ℝ) ≤ 2 * δ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f | M < airy1BlockMax (airy1FddPositive_of_goeLeftTail hGoe) 0 f ∧ M < airy1BlockMax (airy1FddPositive_of_goeLeftTail hGoe) j f} ≤
      (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real (unit_block_oscillation_event (airy1FddPositive_of_goeLeftTail hGoe) 0 δ) +
      (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real (unit_block_oscillation_event (airy1FddPositive_of_goeLeftTail hGoe) j δ) +
      ∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
        (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f | M - 1 < airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) (gridPt 0 n k) f ∧
          M - 1 < airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) (gridPt j n k') f} :=
  @block_pair_grid_cover_airy1 (airy1FddPositive_of_goeLeftTail hGoe) j n hn δ M hmesh

theorem one_point_tail_minus_one_airy1_no_fdd_input (hT : GOELeftTail) :
    ∃ B E U : ℝ, 0 < B ∧ 0 < E ∧ 0 < U ∧
      ∀ M : ℝ, U ≤ M →
        (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | M - 1 < airy1ContR (airy1FddPositive_of_goeLeftTail hT) 0 f} ≤
          B * M ^ (-3 / 4 : ℝ) *
            Real.exp (-AiryConj.kappaC * M ^ (3 / 2 : ℝ) + E * Real.sqrt M) :=
  @one_point_tail_minus_one_airy1 (airy1FddPositive_of_goeLeftTail hT) hT

theorem mesoscopic_sum_airy1_no_fdd_input (hT : GOELeftTail)
    (L : NonnegativeWindowModulusEstimate (airy1Law (airy1FddPositive_of_goeLeftTail hT)) (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A)
    (As : ProcessAssociated (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT))
    (Cov : CubicCovarianceDecay (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT))
    (χ : ℝ) (hχ : (1 / 2 : ℝ) ^ (1 / 3 : ℝ) < χ) (hχ₁ : χ < 1)
    (R : ℝ → ℝ) (hR : R =O[atTop] fun M => Real.sqrt M) :
    (fun M : ℝ =>
      ∑ j ∈ Finset.Icc ⌈χ * Real.sqrt (2 * M)⌉₊ ⌊R M⌋₊,
        (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | M < airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) 0 f ∧ M < airy1BlockMax (airy1FddPositive_of_goeLeftTail hT) j f})
      =o[atTop] AiryConj.rhoM :=
  @mesoscopic_sum_airy1 (airy1FddPositive_of_goeLeftTail hT) hT L As Cov χ hχ hχ₁ R hR

theorem one_point_tail_profile_bounds_airy1_no_fdd_input (hT : GOELeftTail) :
    ∃ A B u₀ : ℝ, 0 < A ∧ 0 < B ∧ 0 < u₀ ∧
      ∀ u : ℝ, u₀ ≤ u →
        A * (AiryConj.rhoM u / u) ≤
          (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | u < airy1ContR (airy1FddPositive_of_goeLeftTail hT) 0 f} ∧
        (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | u < airy1ContR (airy1FddPositive_of_goeLeftTail hT) 0 f} ≤ B * (AiryConj.rhoM u / u) :=
  @one_point_tail_profile_bounds_airy1 (airy1FddPositive_of_goeLeftTail hT) hT

theorem one_point_tail_shift_le_airy1_no_fdd_input (hT : GOELeftTail) :
    ∃ K u₀ : ℝ, 0 < K ∧ 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | u - (Real.sqrt u)⁻¹ < airy1ContR (airy1FddPositive_of_goeLeftTail hT) 0 f}
        ≤ K * (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | u < airy1ContR (airy1FddPositive_of_goeLeftTail hT) 0 f} :=
  @one_point_tail_shift_le_airy1 (airy1FddPositive_of_goeLeftTail hT) hT

theorem memLp_two_airy1ContR_no_fdd_input (hT : GOELeftTail)
    (t : ℝ) :
    MemLp (airy1ContR (airy1FddPositive_of_goeLeftTail hT) t) 2 (airy1Law (airy1FddPositive_of_goeLeftTail hT)) :=
  @memLp_two_airy1ContR (airy1FddPositive_of_goeLeftTail hT) hT t

theorem tail_sensitive_newman_airy1_no_fdd_input (hT : GOELeftTail)
    (As : ProcessAssociated (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) :
    ∃ C u₀ : ℝ, 0 < C ∧ ∀ u d : ℝ, u₀ ≤ u → 0 ≤ d →
      (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | u < airy1ContR (airy1FddPositive_of_goeLeftTail hT) 0 f ∧ u < airy1ContR (airy1FddPositive_of_goeLeftTail hT) d f}
        ≤ C * ((airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | u < airy1ContR (airy1FddPositive_of_goeLeftTail hT) 0 f}) ^ 2 +
          C * u * covariance (airy1ContR (airy1FddPositive_of_goeLeftTail hT) 0) (airy1ContR (airy1FddPositive_of_goeLeftTail hT) d) (airy1Law (airy1FddPositive_of_goeLeftTail hT)) :=
  @tail_sensitive_newman_airy1 (airy1FddPositive_of_goeLeftTail hT) hT As

theorem airy1Law_fwd_le_no_fdd_input (hGoe : GOELeftTail)
    {L C : ℝ} (hF : FwdDefectBound L C)
    {x t a b : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (ha : L ≤ a) (hab : a ≤ b) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) {f : ℝ → ℝ | f x ≤ a ∧ b < f (x + t)}
      ≤ ENNReal.ofReal (C * Real.exp (-(b - a) ^ 2 / (8 * t))) :=
  @airy1Law_fwd_le (airy1FddPositive_of_goeLeftTail hGoe) L C hF x t a b ht ht1 ha hab

theorem airy1Law_rev_le_no_fdd_input (hGoe : GOELeftTail)
    {L C : ℝ} (hR : RevDefectBound L C)
    {x t a b : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hb : L ≤ b) (hba : b ≤ a) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) {f : ℝ → ℝ | a < f x ∧ f (x + t) ≤ b}
      ≤ ENNReal.ofReal (C * Real.exp (-(a - b) ^ 2 / (8 * t))) :=
  @airy1Law_rev_le (airy1FddPositive_of_goeLeftTail hGoe) L C hR x t a b ht ht1 hb hba

theorem airy1Law_clamp_gap_le_no_fdd_input (hGoe : GOELeftTail)
    {L U C C' : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C) (hR : RevDefectBound L C')
    {x t z : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hz : 0 < z) :
    airy1Law (airy1FddPositive_of_goeLeftTail hGoe) {f : ℝ → ℝ | z < |clampTo L U (f (x + t)) - clampTo L U (f x)|}
      ≤ ENNReal.ofReal ((C + C') * (2 * (U - L) / z + 1) * Real.exp (-z ^ 2 / (32 * t))) :=
  @airy1Law_clamp_gap_le (airy1FddPositive_of_goeLeftTail hGoe) L U C C' hLU hC hC' hF hR x t z ht ht1 hz

theorem lintegral_clamp_incr_rpow_le_no_fdd_input (hGoe : GOELeftTail)
    {L U C C' p : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C) (hR : RevDefectBound L C')
    (hp : 1 < p) {x t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∫⁻ f, ENNReal.ofReal (|clampTo L U (f (x + t)) - clampTo L U (f x)| ^ p) ∂airy1Law (airy1FddPositive_of_goeLeftTail hGoe)
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p * t ^ ((p - 1) / 2)) :=
  @lintegral_clamp_incr_rpow_le (airy1FddPositive_of_goeLeftTail hGoe) L U C C' p hLU hC hC' hF hR hp x t ht ht1

theorem airy1Law_clamp_moment_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U p x t : ℝ), L ≤ U → 1 < p → 0 < t → t ≤ 1 →
      ∫⁻ f, ENNReal.ofReal (|clampTo L U (f (x + t)) - clampTo L U (f x)| ^ p) ∂airy1Law (airy1FddPositive_of_goeLeftTail hGoe)
        ≤ ENNReal.ofReal (truncMomentConst C (U - L) p * t ^ ((p - 1) / 2)) :=
  @airy1Law_clamp_moment (airy1FddPositive_of_goeLeftTail hGoe) L

theorem lintegral_edist_clamp_le_of_lt_no_fdd_input (hGoe : GOELeftTail)
    {L U C C' p : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C) (hR : RevDefectBound L C')
    (hp : 1 < p) {s u : ℝ} (hsu : s < u) (hsu1 : u - s ≤ 1) :
    ∫⁻ f, edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p ∂airy1Law (airy1FddPositive_of_goeLeftTail hGoe)
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p) * edist s u ^ ((p - 1) / 2) :=
  @lintegral_edist_clamp_le_of_lt (airy1FddPositive_of_goeLeftTail hGoe) L U C C' p hLU hC hC' hF hR hp s u hsu
    hsu1

theorem lintegral_edist_clamp_le_no_fdd_input (hGoe : GOELeftTail)
    {L U C C' p : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C) (hR : RevDefectBound L C')
    (hp : 1 < p) {s u : ℝ} (hsu1 : dist s u ≤ 1) :
    ∫⁻ f, edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p ∂airy1Law (airy1FddPositive_of_goeLeftTail hGoe)
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p) * edist s u ^ ((p - 1) / 2) :=
  @lintegral_edist_clamp_le (airy1FddPositive_of_goeLeftTail hGoe) L U C C' p hLU hC hC' hF hR hp s u hsu1

theorem lintegral_edist_clamp_le_global_no_fdd_input (hGoe : GOELeftTail)
    {L U C C' p : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C) (hR : RevDefectBound L C')
    (hp : 1 < p) (s u : ℝ) :
    ∫⁻ f, edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p ∂airy1Law (airy1FddPositive_of_goeLeftTail hGoe)
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p + (U - L) ^ p)
        * edist s u ^ ((p - 1) / 2) :=
  @lintegral_edist_clamp_le_global (airy1FddPositive_of_goeLeftTail hGoe) L U C C' p hLU hC hC' hF hR hp s u

theorem isKolmogorovProcess_clamp_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U p : ℝ), L ≤ U → 1 < p →
      IsKolmogorovProcess (fun (s : ℝ) (f : ℝ → ℝ) => clampTo L U (f s)) (airy1Law (airy1FddPositive_of_goeLeftTail hGoe))
        p ((p - 1) / 2) (truncMomentConst C (U - L) p + (U - L) ^ p).toNNReal :=
  @isKolmogorovProcess_clamp (airy1FddPositive_of_goeLeftTail hGoe) L

theorem isKolmogorovProcess_clamp_nnreal_no_fdd_input (hGoe : GOELeftTail)
    (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U p : ℝ), L ≤ U → 1 < p →
      IsKolmogorovProcess (fun (s : ℝ≥0) (f : ℝ → ℝ) => clampTo L U (f s)) (airy1Law (airy1FddPositive_of_goeLeftTail hGoe))
        p ((p - 1) / 2) (truncMomentConst C (U - L) p + (U - L) ^ p).toNNReal :=
  @isKolmogorovProcess_clamp_nnreal (airy1FddPositive_of_goeLeftTail hGoe) L

theorem isKolmogorovProcess_clamp_of_diam_le_no_fdd_input (hGoe : GOELeftTail)
    {L U C C' p : ℝ}
    (hLU : L ≤ U) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C)
    (hR : RevDefectBound L C') (hp : 1 < p) {S : Set ℝ}
    (hS : ∀ s ∈ S, ∀ u ∈ S, dist s u ≤ 1) :
    IsKolmogorovProcess (fun (s : S) (f : ℝ → ℝ) => clampTo L U (f s)) (airy1Law (airy1FddPositive_of_goeLeftTail hGoe))
      p ((p - 1) / 2) (truncMomentConst (C + C') (U - L) p).toNNReal :=
  @isKolmogorovProcess_clamp_of_diam_le (airy1FddPositive_of_goeLeftTail hGoe) L U C C' p hLU hC hC' hF hR hp S hS

theorem airy1BlockMax_le_iff_no_fdd_input (hGoe : GOELeftTail)
    (j : ℕ) (f : ℝ → ℝ) (u : ℝ) :
    airy1BlockMax (airy1FddPositive_of_goeLeftTail hGoe) j f ≤ u ↔ ∀ t ∈ Icc (j : ℝ) (j + 1), airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) t f ≤ u :=
  @airy1BlockMax_le_iff (airy1FddPositive_of_goeLeftTail hGoe) j f u

theorem setOf_two_blocks_eq_iInter_no_fdd_input (hGoe : GOELeftTail)
    {x y M : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    {f | (∀ t ∈ Icc x (x + 1), airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) t f ≤ M) ∧
        ∀ t ∈ Icc y (y + 1), airy1ContR (airy1FddPositive_of_goeLeftTail hGoe) t f ≤ M}
      = ⋂ n, (meshEvent (airy1FddPositive_of_goeLeftTail hGoe) x 1 M (n + 1) ∩ meshEvent (airy1FddPositive_of_goeLeftTail hGoe) y 1 M (n + 1)) :=
  @setOf_two_blocks_eq_iInter (airy1FddPositive_of_goeLeftTail hGoe) x y M hx hy

theorem airy1Law_twoMeshEvent_no_fdd_input (hT : GOELeftTail)
    (x y M : ℝ) (n : ℕ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real (meshEvent (airy1FddPositive_of_goeLeftTail hT) x 1 M n ∩ meshEvent (airy1FddPositive_of_goeLeftTail hT) y 1 M n)
      = AiryFdd.airy1FinCdf (AiryFdd.meshSet x 1 n ∪ AiryFdd.meshSet y 1 n) (fun _ => M) :=
  @airy1Law_twoMeshEvent (airy1FddPositive_of_goeLeftTail hT) hT x y M n

theorem airy1Law_two_blocks_le_eq_fredholmDet_of_length_no_fdd_input (hLeft : GOELeftTail)
    {x M T r a : ℝ} (hx : 0 ≤ x) (hT : 0 < T) (hr : 0 < r)
    (hM : 0 < M) (ha : 2 * T + r + 1 ≤ a) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hLeft)).real {f | (∀ t ∈ Icc x (x + T), airy1ContR (airy1FddPositive_of_goeLeftTail hLeft) t f ≤ M) ∧
        ∀ t ∈ Icc (x + T + r) (x + T + r + T), airy1ContR (airy1FddPositive_of_goeLeftTail hLeft) t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (HilbertSchmidt.kernelOperator (AiryFdd.memLp_kcupKerT_of_length hT hr hM ha)) 1 :=
  @airy1Law_two_blocks_le_eq_fredholmDet_of_length (airy1FddPositive_of_goeLeftTail hLeft) hLeft x M T r a hx hT hr
    hM ha

theorem airy1Law_two_blocks_le_eq_fredholmDet_no_fdd_input (hT : GOELeftTail)
    {x M r a : ℝ} (hx : 0 ≤ x) (hr : 0 < r) (hM : 0 < M) (ha : r + 3 ≤ a) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | (∀ t ∈ Icc x (x + 1), airy1ContR (airy1FddPositive_of_goeLeftTail hT) t f ≤ M) ∧
        ∀ t ∈ Icc (x + 1 + r) (x + 1 + r + 1), airy1ContR (airy1FddPositive_of_goeLeftTail hT) t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (HilbertSchmidt.kernelOperator (AiryTwoInt.memLp_kcupKerT hr hM ha)) 1 :=
  @airy1Law_two_blocks_le_eq_fredholmDet (airy1FddPositive_of_goeLeftTail hT) hT x M r a hx hr hM ha

theorem qrTwoIntervalLaw_airy1_no_fdd_input (hT : GOELeftTail) :
    QRTwoIntervalLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)) :=
  @qrTwoIntervalLaw_airy1 (airy1FddPositive_of_goeLeftTail hT) hT

theorem gumbel_limit_continuum_real_normalized_airy1_of_QR₁₀_no_fdd_input (hT : GOELeftTail)
    (M : CubicStrongMixing (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (Cov : CubicCovarianceDecay (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT))
    (As : ProcessAssociated (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (U : HighLevelUpcrossingTail (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT))
    (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  @gumbel_limit_continuum_real_normalized_airy1_of_QR₁₀ (airy1FddPositive_of_goeLeftTail hT) hT M Cov As U z

theorem airy1Law_coord_le_no_fdd_input (hGoe : GOELeftTail)
    (t w : ℝ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f t ≤ w} = airy1FinCdf {0} (fun _ => w) :=
  @airy1Law_coord_le (airy1FddPositive_of_goeLeftTail hGoe) t w

theorem airy1Law_pair_le_no_fdd_input (hGoe : GOELeftTail)
    (d w : ℝ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 ≤ w ∧ f d ≤ w} = airy1FinCdf {0, d} (fun _ => w) :=
  @airy1Law_pair_le (airy1FddPositive_of_goeLeftTail hGoe) d w

theorem airy1Law_coord_gt_no_fdd_input (hGoe : GOELeftTail)
    (t w : ℝ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f t > w} = 1 - airy1FinCdf {0} (fun _ => w) :=
  @airy1Law_coord_gt (airy1FddPositive_of_goeLeftTail hGoe) t w

theorem airy1Law_pair_gt_no_fdd_input (hGoe : GOELeftTail)
    (d w : ℝ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w ∧ f d > w}
      = 1 - 2 * airy1FinCdf {0} (fun _ => w) + airy1FinCdf {0, d} (fun _ => w) :=
  @airy1Law_pair_gt (airy1FddPositive_of_goeLeftTail hGoe) d w

theorem airy1Law_twoPoint_sub_sq_no_fdd_input (hGoe : GOELeftTail)
    (d w : ℝ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w ∧ f d > w}
        - ((airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w}) ^ 2
      = airy1FinCdf {0, d} (fun _ => w) - airy1FinCdf {0} (fun _ => w) ^ 2 :=
  @airy1Law_twoPoint_sub_sq (airy1FddPositive_of_goeLeftTail hGoe) d w

theorem abs_airy1FinCdf_singleton_le_one_no_fdd_input (hGoe : GOELeftTail)
    (w : ℝ) :
    |airy1FinCdf {0} (fun _ => w)| ≤ 1 :=
  @abs_airy1FinCdf_singleton_le_one (airy1FddPositive_of_goeLeftTail hGoe) w

theorem twoPointExcess_airy1_no_fdd_input (hGoe : GOELeftTail) :
    ∃ w₀ C C' : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ 0 ≤ C' ∧ ∀ w : ℝ, w₀ ≤ w → ∀ d : ℝ, 0 < d →
      |(airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w ∧ f d > w}
          - ((airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w}) ^ 2|
        ≤ C * Real.exp (-rateI w - 2 * w * d + C' * (1 + w + d ^ 2)) :=
  @twoPointExcess_airy1 (airy1FddPositive_of_goeLeftTail hGoe)

theorem airy1SRP_pair_gt_eq_no_fdd_input (hT : GOELeftTail)
    (x y v : ℝ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A x f > v ∧ (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A y f > v}
      = (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f : ℝ → ℝ | f 0 > v ∧ f (y - x) > v} :=
  @airy1SRP_pair_gt_eq (airy1FddPositive_of_goeLeftTail hT) hT x y v

theorem airy1SRP_gt_eq_no_fdd_input (hT : GOELeftTail)
    (v : ℝ) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A 0 f > v}
      = (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f : ℝ → ℝ | f 0 > v} :=
  @airy1SRP_gt_eq (airy1FddPositive_of_goeLeftTail hT) hT v

theorem pairTP_airy1SRP_no_fdd_input (hT : GOELeftTail) :
    ∃ w₀ C C' : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ 0 ≤ C' ∧ ∀ x y v : ℝ, w₀ ≤ v → x < y →
      (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {ω | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A x ω > v ∧ (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A y ω > v}
        ≤ (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {ω | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A 0 ω > v} ^ 2
          + C * Real.exp (-((2 / 3) * (2 * v) ^ (3 / 2 : ℝ)) - 2 * v * (y - x)
              + C' * (1 + v + (y - x) ^ 2)) :=
  @pairTP_airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT

theorem pairTP_airy1SRP_field_no_fdd_input (hT : GOELeftTail) :
    ∃ w₀ C C' : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ 0 ≤ C' ∧ ∀ x y v : ℝ, w₀ ≤ v → x + 1 ≤ y →
      (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {ω | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A x ω > v ∧ (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A y ω > v}
        ≤ (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {ω | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A 0 ω > v} ^ 2
          + C * Real.exp (-((2 / 3) * (2 * v) ^ (3 / 2 : ℝ)) - 2 * v * (y - x)
              + C' * (1 + v + (y - x) ^ 2)) :=
  @pairTP_airy1SRP_field (airy1FddPositive_of_goeLeftTail hT) hT

theorem twoPointExcess_airy1_sharp_no_fdd_input (hGoe : GOELeftTail) :
    ∃ w₀ C : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ ∀ w : ℝ, w₀ ≤ w → ∀ d : ℝ, 0 < d →
      |(airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w ∧ f d > w}
          - ((airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w}) ^ 2|
        ≤ C * (1 + w + d) ^ 2
          * Real.exp (-((2 / 3) * (2 * w + d ^ 2) ^ (3 / 2 : ℝ) + 2 * w * d + (2 / 3) * d ^ 3)) :=
  @twoPointExcess_airy1_sharp (airy1FddPositive_of_goeLeftTail hGoe)

theorem pairTP_airy1SRP_sharp_no_fdd_input (hT : GOELeftTail) :
    ∃ w₀ C : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ ∀ x y v : ℝ, w₀ ≤ v → x < y →
      (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {ω | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A x ω > v ∧ (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A y ω > v}
        ≤ (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {ω | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A 0 ω > v} ^ 2
          + C * (1 + v + (y - x)) ^ 2
            * Real.exp (-((2 / 3) * (2 * v + (y - x) ^ 2) ^ (3 / 2 : ℝ) + 2 * v * (y - x)
                + (2 / 3) * (y - x) ^ 3)) :=
  @pairTP_airy1SRP_sharp (airy1FddPositive_of_goeLeftTail hT) hT

theorem twoPointExcess_airy1_sharp_d_no_fdd_input (hGoe : GOELeftTail) :
    ∃ w₀ C : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ ∀ w : ℝ, w₀ ≤ w → ∀ d : ℝ, 0 < d →
      |(airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w ∧ f d > w}
          - ((airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w}) ^ 2|
        ≤ C * Real.sqrt (1 + d)
          * Real.exp (-((2 / 3) * (2 * w + d ^ 2) ^ (3 / 2 : ℝ) + 2 * w * d + (2 / 3) * d ^ 3)) :=
  @twoPointExcess_airy1_sharp_d (airy1FddPositive_of_goeLeftTail hGoe)

theorem pairTP_airy1SRP_sharp_d_no_fdd_input (hT : GOELeftTail) :
    ∃ w₀ C : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ ∀ x y v : ℝ, w₀ ≤ v → x < y →
      (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {ω | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A x ω > v ∧ (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A y ω > v}
        ≤ (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {ω | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A 0 ω > v} ^ 2
          + C * Real.sqrt (1 + (y - x))
            * Real.exp (-((2 / 3) * (2 * v + (y - x) ^ 2) ^ (3 / 2 : ℝ) + 2 * v * (y - x)
                + (2 / 3) * (y - x) ^ 3)) :=
  @pairTP_airy1SRP_sharp_d (airy1FddPositive_of_goeLeftTail hT) hT

theorem twoPointExcess_airy1_sharp_e_no_fdd_input (hGoe : GOELeftTail) :
    ∃ w₀ C : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ ∀ w : ℝ, w₀ ≤ w → ∀ d : ℝ, 0 < d →
      |(airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w ∧ f d > w}
          - ((airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w}) ^ 2|
        ≤ C * Real.exp (-((2 / 3) * (2 * w + d ^ 2) ^ (3 / 2 : ℝ) + 2 * w * d
            + (2 / 3) * d ^ 3)) :=
  @twoPointExcess_airy1_sharp_e (airy1FddPositive_of_goeLeftTail hGoe)

theorem pairTP_airy1SRP_sharp_e_no_fdd_input (hT : GOELeftTail) :
    ∃ w₀ C : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ ∀ x y v : ℝ, w₀ ≤ v → x < y →
      (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {ω | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A x ω > v ∧ (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A y ω > v}
        ≤ (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {ω | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A 0 ω > v} ^ 2
          + C * Real.exp (-((2 / 3) * (2 * v + (y - x) ^ 2) ^ (3 / 2 : ℝ) + 2 * v * (y - x)
              + (2 / 3) * (y - x) ^ 3)) :=
  @pairTP_airy1SRP_sharp_e (airy1FddPositive_of_goeLeftTail hT) hT

theorem twoPointExcess_airy1_sharp_sqrt_no_fdd_input (hGoe : GOELeftTail) :
    ∃ w₀ C : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ ∀ w : ℝ, w₀ ≤ w → ∀ d : ℝ, 0 < d →
      |(airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w ∧ f d > w}
          - ((airy1Law (airy1FddPositive_of_goeLeftTail hGoe)).real {f : ℝ → ℝ | f 0 > w}) ^ 2|
        ≤ C * Real.sqrt (1 + w + d) * Real.sqrt (1 + d)
          * Real.exp (-((2 / 3) * (2 * w + d ^ 2) ^ (3 / 2 : ℝ) + 2 * w * d + (2 / 3) * d ^ 3)) :=
  @twoPointExcess_airy1_sharp_sqrt (airy1FddPositive_of_goeLeftTail hGoe)

theorem pairTP_airy1SRP_sharp_sqrt_no_fdd_input (hT : GOELeftTail) :
    ∃ w₀ C : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ ∀ x y v : ℝ, w₀ ≤ v → x < y →
      (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {ω | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A x ω > v ∧ (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A y ω > v}
        ≤ (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {ω | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A 0 ω > v} ^ 2
          + C * Real.sqrt (1 + v + (y - x)) * Real.sqrt (1 + (y - x))
            * Real.exp (-((2 / 3) * (2 * v + (y - x) ^ 2) ^ (3 / 2 : ℝ) + 2 * v * (y - x)
                + (2 / 3) * (y - x) ^ 3)) :=
  @pairTP_airy1SRP_sharp_sqrt (airy1FddPositive_of_goeLeftTail hT) hT

theorem gumbel_limit_continuum_real_normalized_airy1_of_QR₆_no_fdd_input (hT : GOELeftTail)
    (qr : QRUnitBlockLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)))
    (qr₂ : QRTwoBlockLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)))
    (two : QRTwoIntervalLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)))
    (M : CubicStrongMixing (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (Cov : CubicCovarianceDecay (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT))
    (As : ProcessAssociated (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (U : HighLevelUpcrossingTail (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT))
    (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  @gumbel_limit_continuum_real_normalized_airy1_of_QR₆ (airy1FddPositive_of_goeLeftTail hT) hT qr qr₂ two M Cov As
    U z

theorem airy1ContR_upcrossing_ae_eq_no_fdd_input (hT : GOELeftTail)
    (x t a b : ℝ) :
    {f : ℝ → ℝ | airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f ≤ a ∧ b < airy1ContR (airy1FddPositive_of_goeLeftTail hT) (x + t) f}
      =ᵐ[airy1Law (airy1FddPositive_of_goeLeftTail hT)] {f : ℝ → ℝ | f x ≤ a ∧ b < f (x + t)} :=
  @airy1ContR_upcrossing_ae_eq (airy1FddPositive_of_goeLeftTail hT) hT x t a b

theorem airy1SRP_upcrossing_le_no_fdd_input (hT : GOELeftTail)
    {L C : ℝ}
    (hC : 0 < C) (hF : FwdDefectBound L C) {x t a b : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (ha : L ≤ a) (hab : a ≤ b) :
    (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f : ℝ → ℝ | (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A x f ≤ a ∧ b < (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT).A (x + t) f}
      ≤ C * Real.exp (-(b - a) ^ 2 / (8 * t)) :=
  @airy1SRP_upcrossing_le (airy1FddPositive_of_goeLeftTail hT) hT L C hC hF x t a b ht ht1 ha hab

theorem highLevelUpcrossingTail_airy1SRP_no_fdd_input (hT : GOELeftTail) :
    HighLevelUpcrossingTail (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT) :=
  @highLevelUpcrossingTail_airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT

theorem gumbel_limit_continuum_real_normalized_airy1_of_QR₉_no_fdd_input (hT : GOELeftTail)
    (two : QRTwoIntervalLaw (airy1BlockMax (airy1FddPositive_of_goeLeftTail hT)) (airy1Law (airy1FddPositive_of_goeLeftTail hT)))
    (M : CubicStrongMixing (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (Cov : CubicCovarianceDecay (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT))
    (As : ProcessAssociated (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  @gumbel_limit_continuum_real_normalized_airy1_of_QR₉ (airy1FddPositive_of_goeLeftTail hT) hT two M Cov As z

end Airy1Gumbel
