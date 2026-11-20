/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.BlockLaw
import Airy1Gumbel.MeshHitting

open Filter MeasureTheory ProbabilityTheory Set
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

/-- **Core law, unconditional in K.** Under `Airy1FddPositive` and `GOELeftTail` only, for
`T ≥ 1`, `M > 0` and `x ≥ 0`: `ℙ(Ã(t) ≤ M ∀ t ∈ [x, x+T]) = det(I − Ã_{M,T})` with
`Ã_{M,T} = airyTildeOp M T (2T)` (QR 2012 Theorem 4 at block length `T`). -/
theorem airy1Law_sup_le_eq_fredholmDet' (h : Airy1FddPositive) (hT : GOELeftTail) {x M T : ℝ}
    (hx : 0 ≤ x) (hT1 : 1 ≤ T) (hM : 0 < M) :
    (airy1Law h).real {f | ∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1 :=
  airy1Law_sup_le_eq_fredholmDet h hT hx hT1 hM (meshHittingLimit M (by linarith))

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
