/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.AiryKernel.TailAsymptotic

/-! # The touching-block estimate in determinant form

The paper's touching-block estimate states
`ℙ(Y₀ > M, Y₁ > M) ~ ρ(M)/(4M)` as `M → ∞`, where `Y_j = sup_{j ≤ x ≤ j+1} A₁(x)`.
Its proof is stationarity plus inclusion–exclusion,

  `ℙ(Y₀ > M, Y₁ > M) = 2π₁(M) − π₂(M)`,  `π_T(M) = ℙ{sup_{0≤x≤T} A₁(x) > M}`,

followed by the paper's sharp one-block tail at `T = 1` and `T = 2`.

This module proves the analytic half: with `π_T` replaced by its determinant
form `1 − det₁(1 − Ã_{M,T})` (contrib `detOneAiryTilde`), the combination
`touchDet M = 2π₁(M) − π₂(M)` satisfies

  `touchDet M ~ ρ(M)/(4M)`.

The only input used is the two-term expansion `piT_sub_traceLead_isLittleO`
(AiryKernel/TailAsymptotic.lean), at `T = 1` and `T = 2`.

## What is proved here

* `two_traceLead_one_sub_traceLead_two`: the lead cancellation
  `2·(ρ + ρ/(4M)) − (2ρ + ρ/(4M)) = ρ/(4M)`: the `Tρ` terms cancel and the
  `T`-independent `ρ/(4M)` term survives with coefficient `2 − 1 = 1`.
* `touchDet_sub_isLittleO`: `touchDet M − ρ(M)/(4M) = o(ρ(M)/M)`.
* `touchDet_isEquivalent`: the touching-block estimate in determinant form,
  `touchDet ~ ρ/(4M)`.
* `touchDet_isBigO`: `touchDet = O(ρ(M)/M)`, the form the main-package field
  discharge (`Airy1Gumbel.touching_of_QR`) consumes.

## Remarks on the formalization

1. **No two-interval argument.** The touching estimate is the gap-`0` case. The
   paper's two-interval determinant formula and joint-tail estimate assume a
   positive gap, as do the contrib two-interval declarations (`TwoInterval/`); the
   paper handles the touching case separately, using only the sharp one-block tail
   at `T = 1, 2`, and so does this module. Nothing from `TwoInterval/` is imported.
2. **`π_T` in determinant form.** The paper applies the sharp one-block tail to the
   probabilities `π₁, π₂`. Here the two-term expansion is applied to the totalized
   functions `1 − detOneAiryTilde · T`, so `hpi` is `rfl`. The probabilistic
   identifications `π₁(u) = ℙ(Y₀ > u)` and `π₂(u) = ℙ(Y₀ > u ∨ Y₁ > u)` enter in
   the main package through the records `QRUnitBlockLaw` and `QRTwoBlockLaw`
   (see `Airy1Gumbel.SharpTail`).
3. **No eventual restriction here.** `touchDet` is built from the totalized
   determinant (junk value `0` off `T + 1 ≤ √(2M)`, i.e. `M ≥ 9/2` at `T = 2`).
   The identity `2·traceLead M 1 − traceLead M 2 = ρ(M)/(4M)` holds for every
   `M`, so the cancellation needs no `eventually`; the two-term expansion already
   absorbs the junk region.
4. **Only `O(ρ/M)` is used downstream.** The equivalence `~ ρ/(4M)` is proved as
   well (`touchDet_isEquivalent`), but the Gumbel-limit field discharge uses only
   `touchDet_isBigO`.
-/

namespace AiryConj

open Filter Asymptotics
open scoped Topology

/-- The two-term trace lead cancellation behind the touching-block estimate
(with the lead `traceLead M T = Tρ(M) + ρ(M)/(4M)` of
the sharp one-block tail):
`2·traceLead M 1 − traceLead M 2 = ρ(M)/(4M)` for every `M`. -/
theorem two_traceLead_one_sub_traceLead_two (M : ℝ) :
    2 * traceLead M 1 - traceLead M 2 = rhoM M / (4 * M) := by
  unfold traceLead
  ring

/-- The touching combination `2π₁(M) − π₂(M)` in determinant
form: `π_T(M) = 1 − det₁(1 − Ã_{M,T})` at
`T = 1` and `T = 2`, with the totalized contrib determinant `detOneAiryTilde`. -/
noncomputable def touchDet (M : ℝ) : ℝ :=
  2 * (1 - detOneAiryTilde M 1) - (1 - detOneAiryTilde M 2)

/-- The remainder of the touching-block estimate in determinant
form: `touchDet M − ρ(M)/(4M) = o(ρ(M)/M)`. Proof: the two-term expansion
(`piT_sub_traceLead_isLittleO`, the sharp one-block tail)
at `T = 1` and `T = 2`, combined as `2·(expansion at 1) − (expansion at 2)`, plus the lead
cancellation `two_traceLead_one_sub_traceLead_two`. -/
theorem touchDet_sub_isLittleO :
    (fun M => touchDet M - rhoM M / (4 * M)) =o[atTop] fun M => rhoM M / M := by
  have h1 := piT_sub_traceLead_isLittleO 1 one_pos
    (fun M => 1 - detOneAiryTilde M 1) (fun _ => rfl)
  have h2 := piT_sub_traceLead_isLittleO 2 two_pos
    (fun M => 1 - detOneAiryTilde M 2) (fun _ => rfl)
  refine ((h1.const_mul_left 2).sub h2).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards with M
  have hc := two_traceLead_one_sub_traceLead_two M
  simp only [touchDet]
  linear_combination (-1 : ℝ) * hc

/-- **The touching-block estimate in determinant form**:
`2π₁(M) − π₂(M) ~ ρ(M)/(4M)` as `M → ∞`, with `π_T = 1 − det₁(1 − Ã_{·,T})`.
Proof: `touchDet_sub_isLittleO` and
`ρ(M)/M = 4·(ρ(M)/(4M))`. -/
theorem touchDet_isEquivalent :
    touchDet ~[atTop] fun M => rhoM M / (4 * M) := by
  have hO : (fun M : ℝ => rhoM M / M) =O[atTop] fun M => rhoM M / (4 * M) := by
    have h := isBigO_const_mul_self (4 : ℝ) (fun M : ℝ => rhoM M / (4 * M)) atTop
    refine h.congr_left fun M => ?_
    rw [mul_div_assoc', mul_div_mul_left _ _ (four_ne_zero (α := ℝ))]
  exact touchDet_sub_isLittleO.trans_isBigO hO

/-- The `O(ρ(M)/M)` form of the touching-block estimate in
determinant form: `2π₁(M) − π₂(M) = O(ρ(M)/M)`. This is the bound the
main-package discharge of the `touching` field consumes. -/
theorem touchDet_isBigO :
    touchDet =O[atTop] fun M => rhoM M / M := by
  have h2 : (fun M : ℝ => rhoM M / (4 * M)) =O[atTop] fun M => rhoM M / M := by
    have h := isBigO_const_mul_self ((1 : ℝ) / 4) (fun M : ℝ => rhoM M / M) atTop
    refine h.congr_left fun M => ?_
    ring
  exact (touchDet_sub_isLittleO.isBigO.add h2).congr_left fun M => sub_add_cancel _ _

end AiryConj
