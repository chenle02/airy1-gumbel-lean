/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import BrownianMotion.Gaussian.BrownianMotion
import Airy1GumbelContrib.Mesh.Reflection

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Airy1Gumbel

/-!
# The dyadic hitting-kernel limit as a theorem via Brownian motion

The contrib theorem `AiryFdd.meshHittingLimit_of_isBrownianReal` proves the kernel fact
`AiryFdd.MeshHittingLimit M T` ((K1) `H_n ≤ Q_{M,T}` a.e. for every `n`, (K2) `H_n → Q_{M,T}`
a.e.) from any Brownian motion with measurable coordinates (weak Markov at grid times,
first-crossing decomposition, Gaussian symmetry, path continuity).  The kernel fact itself is a
deterministic statement about Gaussian iterated integrals; here it is instantiated with the
BrownianMotion package's `brownian` on `gaussianLimit` (continuous and measurable for every
path), so it holds unconditionally:

* `meshHittingLimit`: `MeshHittingLimit M T` for every `M` and every `T > 0`;
* `tendsto_airy1FinCdf_meshSet_of_pos`: the constant-level fdd on the dyadic mesh
  `{x + kT/2ⁿ : k < 2ⁿ}` converges to `det(I − Ã_{M,T})` (weight `2T`) for `T ≥ 1`, `M > 0`,
  with no kernel hypothesis left (the contrib mesh-limit reduction plus this theorem).
-/

/-- **The dyadic hitting-kernel limit (K1 + K2) holds for every level and every `T > 0`.** -/
theorem meshHittingLimit (M : ℝ) {T : ℝ} (hT : 0 < T) : AiryFdd.MeshHittingLimit M T :=
  AiryFdd.meshHittingLimit_of_isBrownianReal isBrownianReal_brownian measurable_brownian M hT

/-- The binder shape used by the mesh-limit reduction: `∀ M > 0, MeshHittingLimit M T` for `T > 0`.
-/
theorem forall_meshHittingLimit {T : ℝ} (hT : 0 < T) :
    ∀ M > 0, AiryFdd.MeshHittingLimit M T :=
  fun M _ => meshHittingLimit M hT

/-- **Unconditional dyadic mesh limit**: for `T ≥ 1`, `M > 0` and every base point `x`,
`F_{I_n}(M, …, M) → det(I − Ã_{M,T})` at weight `2T`, `I_n = {x + kT/2ⁿ : k < 2ⁿ}`. -/
theorem tendsto_airy1FinCdf_meshSet_of_pos (x : ℝ) {M T : ℝ} (hT : 1 ≤ T) (hM : 0 < M) :
    Tendsto (fun n => AiryFdd.airy1FinCdf (AiryFdd.meshSet x T n) (fun _ => M)) atTop
      (𝓝 (HilbertSchmidt.fredholmDet
        (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1)) :=
  AiryFdd.tendsto_airy1FinCdf_meshSet x hT hM (meshHittingLimit M (by linarith))

end Airy1Gumbel
