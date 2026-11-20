/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.BlockLaw
import Airy1Gumbel.MeshHitting

open Asymptotics Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

/-!
# The QR block laws without the kernel hypothesis

`Airy1Gumbel.BlockLaw` proves the core law and the QR block-law records on the concrete
Airy₁ process conditional on contrib's dyadic hitting-kernel limit `AiryFdd.MeshHittingLimit`
(K). `Airy1Gumbel.MeshHitting` proves K for every level `M` and every `T > 0`. This module
combines the two: the QR block-law records `QRUnitBlockLaw` and `QRTwoBlockLaw` are now
**theorems** for the concrete Airy₁ process `Ã = airy1ContR h` under `airy1Law h`, conditional
only on `Airy1FddPositive` and `GOELeftTail`.

* `airy1Law_sup_le_eq_fredholmDet'`: the core law, no K;
* `qrUnitBlockLaw_airy1'`, `qrTwoBlockLaw_airy1'`: the block-law records, no K;
* `gumbel_limit_continuum_real_normalized_airy1_of_QR₈`: the `_of_QR₇` headline with both
  kernel hypotheses discharged.
-/

namespace Airy1Gumbel

/-- The interval hitting law for any positive length and any fixed admissible weight. -/
theorem airy1Law_sup_le_eq_fredholmDet_at_weight' (h : Airy1FddPositive) (hLeft : GOELeftTail)
    {x M T a : ℝ} (hx : 0 ≤ x) (hT : 0 < T) (hM : 0 < M) (ha : T + 1 ≤ a) :
    (airy1Law h).real {f | ∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet (AiryConj.airyTildeOp M T a hT hM ha) 1 :=
  airy1Law_sup_le_eq_fredholmDet_at_weight h hLeft hx hT hM ha (meshHittingLimit M hT)

/-- **Core law, unconditional in K.** Under `Airy1FddPositive` and `GOELeftTail` only, for
`T ≥ 1`, `M > 0` and `x ≥ 0`: `ℙ(Ã(t) ≤ M ∀ t ∈ [x, x+T]) = det(I − Ã_{M,T})` with
`Ã_{M,T} = airyTildeOp M T (2T)` (QR 2012 Theorem 4 at block length `T`). -/
theorem airy1Law_sup_le_eq_fredholmDet' (h : Airy1FddPositive) (hT : GOELeftTail) {x M T : ℝ}
    (hx : 0 ≤ x) (hT1 : 1 ≤ T) (hM : 0 < M) :
    (airy1Law h).real {f | ∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1 :=
  airy1Law_sup_le_eq_fredholmDet_at_weight' h hT hx (by linarith) hM (by linarith)

/-- Proposition 1.2 of arXiv:2611.23658v1. For each fixed positive interval length, the
exceedance probability has the two-term expansion with remainder `o(ρ(M) / M)`. -/
theorem airy1Law_interval_tail_sub_traceLead_isLittleO
    (h : Airy1FddPositive) (hLeft : GOELeftTail) (T : ℝ) (hT : 0 < T) :
    (fun M : ℝ => (airy1Law h).real {f | ∃ t ∈ Icc (0 : ℝ) T, M < airy1ContR h t f}
      - AiryConj.traceLead M T) =o[atTop] (fun M => AiryConj.rhoM M / M) := by
  have htail := AiryConj.piT_sub_traceLead_isLittleO T hT
    (fun M => 1 - AiryConj.detOneAiryTilde M T) (fun _ => rfl)
  refine htail.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_fredholmDet_airyTildeOp_eq hT (le_refl (T + 1)),
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop ((T + 1) ^ 2 / 2)] with M hdet hM hlarge
  have hsqrt : T + 1 ≤ Real.sqrt (2 * M) := Real.le_sqrt_of_sq_le (by linarith)
  have hbelow := airy1Law_sup_le_eq_fredholmDet_at_weight' h hLeft
    (le_refl (0 : ℝ)) hT hM (le_refl (T + 1))
  simp only [zero_add] at hbelow
  have hmeas : MeasurableSet {f | ∀ t ∈ Icc (0 : ℝ) T, airy1ContR h t f ≤ M} := by
    have hmesh := setOf_forall_Icc_le_eq_iInter h (M := M) (le_refl (0 : ℝ)) hT
    rw [zero_add] at hmesh
    rw [hmesh]
    exact MeasurableSet.iInter (fun n => measurableSet_meshEvent h 0 T M n)
  have hcompl : {f | ∃ t ∈ Icc (0 : ℝ) T, M < airy1ContR h t f}
      = {f | ∀ t ∈ Icc (0 : ℝ) T, airy1ContR h t f ≤ M}ᶜ := by
    ext f
    simp only [mem_ofPred_eq, mem_compl_iff, not_forall, not_le, exists_prop]
  rw [hcompl, Airy1Gumbel.measureReal_compl hmeas, hbelow, hdet hM,
    AiryConj.detOneAiryTilde_eq_fredholmDetOne hT hM hsqrt (le_refl (T + 1))]

/-- **`QRUnitBlockLaw` on the concrete Airy₁ process is a theorem**, conditional only on
`Airy1FddPositive` and `GOELeftTail` (the kernel fact K at `T = 1` is `forall_meshHittingLimit`). -/
theorem qrUnitBlockLaw_airy1' (h : Airy1FddPositive) (hT : GOELeftTail) :
    QRUnitBlockLaw (airy1BlockMax h) (airy1Law h) :=
  qrUnitBlockLaw_airy1 h hT (forall_meshHittingLimit one_pos)

/-- **`QRTwoBlockLaw` on the concrete Airy₁ process is a theorem**, conditional only on
`Airy1FddPositive` and `GOELeftTail` (the kernel fact K at `T = 2` is `forall_meshHittingLimit`). -/
theorem qrTwoBlockLaw_airy1' (h : Airy1FddPositive) (hT : GOELeftTail) :
    QRTwoBlockLaw (airy1BlockMax h) (airy1Law h) :=
  qrTwoBlockLaw_airy1 h hT (forall_meshHittingLimit two_pos)

/-- **Headline `_of_QR₈` on the Airy₁ law** (the paper's main theorem (Theorem 1.1), normalized
real-length
form, on `Ã = airy1ContR h`): `gumbel_limit_continuum_real_normalized_airy1_of_QR₇` with both
dyadic hitting-kernel hypotheses (`T = 1`, `T = 2`) discharged by `forall_meshHittingLimit`.
The QR block-law records are now theorems for the concrete process. Remaining hypotheses:
`Airy1FddPositive`, `GOELeftTail`, `QRTwoIntervalLaw`, `CubicStrongMixing`,
`CubicCovarianceDecay`, `ProcessAssociated` and `HighLevelUpcrossingTail` on `Ã`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_of_QR₈ (h : Airy1FddPositive)
    (hT : GOELeftTail)
    (two : QRTwoIntervalLaw (airy1BlockMax h) (airy1Law h))
    (M : CubicStrongMixing (airy1SRP h hT)) (Cov : CubicCovarianceDecay (airy1SRP h hT))
    (As : ProcessAssociated (airy1SRP h hT)) (U : HighLevelUpcrossingTail (airy1SRP h hT))
    (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law h).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR h x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  gumbel_limit_continuum_real_normalized_airy1_of_QR₇ h hT (forall_meshHittingLimit one_pos)
    (forall_meshHittingLimit two_pos) two M Cov As U z

end Airy1Gumbel
