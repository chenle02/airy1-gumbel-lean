/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.Separated
import Airy1GumbelContrib.TwoInterval.TwoIntervalSign

open Filter MeasureTheory Asymptotics
open scoped Topology BigOperators
open HilbertSchmidt

namespace Airy1Gumbel

/-!
# Sanity theorems for the three QR external-input records

`ExternalInputs.lean` states three QR records as hypotheses: `QRUnitBlockLaw`
(record 1), `QRTwoBlockLaw` (record 2) and `QRTwoIntervalLaw` (record 3). Each
equates a probability with contrib's **entire** Fredholm
determinant `HilbertSchmidt.fredholmDet` at coupling `1` (principal-minor series,
no junk value; `detKCup` for record 3). The consumers use the exp-trace
(Plemelj) determinant `HilbertSchmidt.fredholmDetOne`, obtained from each record
by the disk agreement (`QRUnitBlockLaw.law_detOne`, `QRTwoBlockLaw.law_detOne`,
`QRTwoIntervalLaw.law_detOne`; each restatement is an equivalence,
`*.iff_law_detOne`). The exp-trace determinant has a junk value (a divergent
Plemelj series has `tsum = 0`, so `det₁ = 1`), and the entire determinant over
`ℝ` need not be positive, so both forms still need range checks. The build and
the axiom audit check proofs, not whether a record can be
satisfied. A later edit to a kernel, a weight or a definition could make a
record junk-valued, outside `[0, 1]`, or inconsistent with another record, so
that no process satisfies it and every `_of_QR*` headline becomes vacuously
true. The theorems below are the regression guard for that failure. Each is a
consequence of contrib lemmas only, with no record assumed. If an edit
breaks the property a theorem guards, the theorem stops compiling and the
build fails.

Contents:

* Records 1 and 2 at QR's weights `a = 2T`: the Plemelj series is eventually
  summable, so the derived exp-trace form never uses the junk value, and the
  records' right-hand side `1 − det` (entire determinant) is eventually in
  `(0, 1)`.
* Joint consistency of records 1 and 2: with `π_T = 1 − det₁(I − Ã_{u,T})`,
  eventually `0 < π₁ < π₂ < 2π₁`. These are the inequalities
  `ℙ(Y₀ > u) ≤ ℙ(Y₀ > u ∨ Y₁ > u) ≤ 2ℙ(Y₀ > u)` that any stationary model
  must satisfy, made strict.
* Record 3: the guard arithmetic, positivity of the exp-trace form on the
  guard and eventual positivity of the record's `detKCup` uniformly in `j`,
  eventual `‖K̃∪‖₂ < ε` and `|tr K̃∪| < ε` uniformly over every
  admissible block index `j` (`qrTwoInterval_guard` and
  `qrTwoInterval_kcup_small_uniform` live in `Separated.lean`, where
  `QRTwoIntervalLaw.law_detOne` consumes them), the uniform Plemelj
  summability that follows,
  a two-sided envelope for the implied joint exceedance
  `X = 1 − 2 det₁(I − K̃₁) + det₁(I − K̃∪)`
  (`qrTwoInterval_implied_joint_abs_le`), and its sign: eventually
  `X ≥ (1 − ε) π₁² > 0` for `j − 1 ≤ χ√(2u)`, every `χ < 1`, `ε > 0`
  (`qrTwoInterval_implied_joint_ge_assoc`, `qrTwoInterval_implied_joint_pos`).
  The upper compatibility `X ≤ π₁` is NOT certified.
-/

/-! ### The exp-trace determinant is positive over `ℝ` -/

/-- Over `ℝ`, `det₁(I − A) = exp(−∑ tr(Aᵐ)/m)` is a real exponential, so it is
positive whether or not the Plemelj series converges. This is the reason each
`1 − det₁` right-hand side below is `< 1`.

Guards against: a redefinition of `fredholmDetOne` that can vanish or go
negative. Such a change would let a record force a probability `≥ 1`, or
force `ℙ(both ≤ u) ≤ 0`. -/
theorem fredholmDetOne_one_pos
    {A : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ)}
    (hA : IsTraceClass A) : 0 < fredholmDetOne A hA 1 := by
  unfold fredholmDetOne
  rw [← Real.exp_eq_exp_ℝ]
  exact Real.exp_pos _

/-! ### Records 1 and 2: summability at QR's weight (no junk value) -/

/-- **Record 1 (`QRUnitBlockLaw`): no junk value.** Eventually in `u`, the
Plemelj series `∑ tr(Ãᵐ⁺¹)/(m+1)` of QR's operator `Ã_{u,1,2}` (weight
`a = 2`) is summable. So the derived exp-trace form
(`QRUnitBlockLaw.law_detOne`) has `fredholmDetOne` the exponential of a
genuine sum, not the `tsum = 0` junk value. (The record itself, over the entire
`fredholmDet`, has no junk value.)

Guards against: an edit to `vKernel`/`wKernel`, to the weight or to
`hsNorm_airyTilde_le` that pushes `Ã_{u,1,2}` off the Hilbert–Schmidt unit disk
for large `u`. -/
theorem qrUnitBlockLaw_rhs_summable :
    ∀ᶠ u in atTop, ∀ hu : 0 < u,
      Summable fun m : ℕ =>
        trace ((AiryConj.airyTildeOp u 1 2 one_pos hu (by norm_num)) ^ (m + 1))
          / ((m + 1 : ℕ) : ℝ) := by
  filter_upwards [eventually_hsNorm_airyTildeOp_lt one_pos (by norm_num : (1 : ℝ) + 1 ≤ 2)
    one_pos] with u h hu
  exact summable_trace_pow_div (AiryConj.isTraceClass_airyTildeOp one_pos hu (by norm_num))
    (h hu)

/-- **Record 2 (`QRTwoBlockLaw`): no junk value.** Eventually in `u`, the
Plemelj series of QR's operator `Ã_{u,2,4}` (weight `a = 4`) is summable, so
the derived exp-trace form (`QRTwoBlockLaw.law_detOne`) never uses the junk
value `det₁ = 1`.

Guards against: the same kernel, weight or bound edits as
`qrUnitBlockLaw_rhs_summable`, at `T = 2`. -/
theorem qrTwoBlockLaw_rhs_summable :
    ∀ᶠ u in atTop, ∀ hu : 0 < u,
      Summable fun m : ℕ =>
        trace ((AiryConj.airyTildeOp u 2 4 two_pos hu (by norm_num)) ^ (m + 1))
          / ((m + 1 : ℕ) : ℝ) := by
  filter_upwards [eventually_hsNorm_airyTildeOp_lt two_pos (by norm_num : (2 : ℝ) + 1 ≤ 4)
    one_pos] with u h hu
  exact summable_trace_pow_div (AiryConj.isTraceClass_airyTildeOp two_pos hu (by norm_num))
    (h hu)

/-! ### Records 1 and 2: the right-hand sides are probabilities, jointly consistent -/

/-- The contrib sharp-tail expansion `AiryConj.piT_sub_traceLead_isLittleO`, quantified
at `ε = 1/16`: eventually `u ≥ 1` and
`|π_T(u) − (Tρ(u) + ρ(u)/(4u))| ≤ (1/16) ρ(u)/u`, where
`π_T = 1 − det₁(I − Ã_{u,T})` at `a = √(2u)`.

Guards against: an edit that loses or weakens the sharp-tail expansion at a fixed `T`. Every
range and consistency theorem below goes through this one. -/
theorem eventually_abs_piT_sub_traceLead_le (T : ℝ) (hT : 0 < T) :
    ∀ᶠ u in atTop, 1 ≤ u ∧
      |(1 - AiryConj.detOneAiryTilde u T) - AiryConj.traceLead u T|
        ≤ 1 / 16 * (AiryConj.rhoM u / u) := by
  have h := (AiryConj.piT_sub_traceLead_isLittleO T hT
    (fun M => 1 - AiryConj.detOneAiryTilde M T) (fun _ => rfl)).def
    (by norm_num : (0 : ℝ) < 1 / 16)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with u h1 hu
  refine ⟨hu, ?_⟩
  have hq : 0 < AiryConj.rhoM u / u := div_pos (AiryConj.rhoM_pos (by linarith)) (by linarith)
  have h1' : |(1 - AiryConj.detOneAiryTilde u T) - AiryConj.traceLead u T|
      ≤ 1 / 16 * |AiryConj.rhoM u / u| := by
    simpa only [Real.norm_eq_abs] using h1
  rwa [abs_of_pos hq] at h1'

/-- **Joint consistency of records 1 and 2 (the paper's weight `a = √(2u)`).**
Write `π_T(u) = 1 − det₁(I − Ã_{u,T})`. Eventually in `u`,
`0 < π₁ < π₂ < 2π₁`. By the bridges `QRUnitBlockLaw.detOne_form` and
`QRTwoBlockLaw.detOne_form`, `π₁ = ℙ(Y₀ > u)` and `π₂ = ℙ(Y₀ > u ∨ Y₁ > u)`.
Any stationary model needs `ℙ(Y₀ > u) ≤ ℙ(Y₀ > u ∨ Y₁ > u) ≤ 2ℙ(Y₀ > u)`.
Proof: the sharp-tail expansion at `T = 1, 2` with `ε = 1/16`. Then `π₂ − π₁ ≥ ρ − ρ/(8u) > 0` and
`2π₁ − π₂ ≥ ρ/(16u) > 0`. The upper margin is thin: it is the touching
probability `~ ρ/(4u)`.

Guards against: an edit to the `T = 1` or `T = 2` kernels, or to their weights,
that makes the two records contradict each other (`π₂ < π₁` or `π₂ > 2π₁`).
No process satisfies a contradictory pair, so every theorem assuming both
records would hold vacuously. -/
theorem eventually_piT_joint_consistent :
    ∀ᶠ u in atTop,
      0 < 1 - AiryConj.detOneAiryTilde u 1 ∧
      1 - AiryConj.detOneAiryTilde u 1 < 1 - AiryConj.detOneAiryTilde u 2 ∧
      1 - AiryConj.detOneAiryTilde u 2 < 2 * (1 - AiryConj.detOneAiryTilde u 1) := by
  filter_upwards [eventually_abs_piT_sub_traceLead_le 1 one_pos,
    eventually_abs_piT_sub_traceLead_le 2 two_pos] with u ⟨hu1, h1⟩ ⟨_, h2⟩
  have hu0 : 0 < u := by linarith
  have hρ : 0 < AiryConj.rhoM u := AiryConj.rhoM_pos hu0
  set ρ := AiryConj.rhoM u with hρdef
  set q := ρ / u with hqdef
  have hq : 0 < q := div_pos hρ hu0
  have hqρ : q ≤ ρ := div_le_self hρ.le hu1
  have h4 : ρ / (4 * u) = q / 4 := by rw [hqdef]; field_simp
  have hL1 : AiryConj.traceLead u 1 = ρ + q / 4 := by
    simp only [AiryConj.traceLead, ← hρdef, h4, one_mul]
  have hL2 : AiryConj.traceLead u 2 = 2 * ρ + q / 4 := by
    simp only [AiryConj.traceLead, ← hρdef, h4]
  rw [hL1] at h1
  rw [hL2] at h2
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **Record 1 right-hand side is a probability.** Eventually in `u`, the
right-hand side `1 − det(I − Ã_{u,1,2})` of `QRUnitBlockLaw` (entire
determinant), at QR's weight `a = 2`, lies strictly in `(0, 1)`. The positive
lower bound means the record forces a nontrivial tail, so no `Y` with
`ℙ(Y₀ > u) = 0` satisfies it. The upper bound `< 1` holds because, on the disk
(`eventually_fredholmDet_airyTildeOp_eq`), the entire determinant equals the
exp-trace determinant, which is positive.

Guards against: a sign or normalization slip in the `T = 1` kernel, or in the
weight-`2` re-weighting (`AiryConj.eventually_detOneAiryTilde_one_eq_weight_two`),
that pushes the right-hand side out of `[0, 1]`. A record forcing a negative
probability is false, and the `_of_QR` headlines would then be vacuous. -/
theorem qrUnitBlockLaw_rhs_mem_Ioo :
    ∀ᶠ u in atTop, ∀ hu : 0 < u,
      0 < 1 - fredholmDet (AiryConj.airyTildeOp u 1 2 one_pos hu (by norm_num)) 1 ∧
      1 - fredholmDet (AiryConj.airyTildeOp u 1 2 one_pos hu (by norm_num)) 1 < 1 := by
  filter_upwards [eventually_piT_joint_consistent,
    AiryConj.eventually_detOneAiryTilde_one_eq_weight_two,
    eventually_fredholmDet_airyTildeOp_eq one_pos (by norm_num : (1 : ℝ) + 1 ≤ 2)]
    with u h hdet hent hu
  rw [hent hu]
  refine ⟨?_, ?_⟩
  · rw [← hdet hu]
    exact h.1
  · have := fredholmDetOne_one_pos (AiryConj.isTraceClass_airyTildeOp one_pos hu
      (by norm_num : (1 : ℝ) + 1 ≤ 2))
    linarith

/-- **Record 2 right-hand side is a probability.** Eventually in `u`, the
right-hand side `1 − det(I − Ã_{u,2,4})` of `QRTwoBlockLaw` (entire
determinant), at QR's weight `a = 4`, lies strictly in `(0, 1)`.

Guards against: a sign or normalization slip in the `T = 2` kernel, or in the
weight-`4` re-weighting (`eventually_detOneAiryTilde_two_eq_weight_four`), that
pushes the right-hand side out of `[0, 1]`. -/
theorem qrTwoBlockLaw_rhs_mem_Ioo :
    ∀ᶠ u in atTop, ∀ hu : 0 < u,
      0 < 1 - fredholmDet (AiryConj.airyTildeOp u 2 4 two_pos hu (by norm_num)) 1 ∧
      1 - fredholmDet (AiryConj.airyTildeOp u 2 4 two_pos hu (by norm_num)) 1 < 1 := by
  filter_upwards [eventually_piT_joint_consistent,
    eventually_detOneAiryTilde_two_eq_weight_four,
    eventually_fredholmDet_airyTildeOp_eq two_pos (by norm_num : (2 : ℝ) + 1 ≤ 4)]
    with u h hdet hent hu
  rw [hent hu]
  refine ⟨?_, ?_⟩
  · rw [← hdet hu]
    linarith [h.1, h.2.1]
  · have := fredholmDetOne_one_pos (AiryConj.isTraceClass_airyTildeOp two_pos hu
      (by norm_num : (2 : ℝ) + 1 ≤ 4))
    linarith

/-- **Joint consistency of records 1 and 2, at QR's own weights.** This is
`eventually_piT_joint_consistent` restated in the exact form the records
assert (entire determinant). With `π₁ = 1 − det(I − Ã_{u,1,2})`
(record 1) and `π₂ = 1 − det(I − Ã_{u,2,4})` (record 2), eventually
`0 < π₁ < π₂ < 2π₁`.

Guards against: the records becoming jointly unsatisfiable through an edit
that moves either weight-bridge lemma, not only through a kernel edit. -/
theorem qrRecords_joint_consistent :
    ∀ᶠ u in atTop, ∀ hu : 0 < u,
      0 < 1 - fredholmDet (AiryConj.airyTildeOp u 1 2 one_pos hu (by norm_num)) 1 ∧
      1 - fredholmDet (AiryConj.airyTildeOp u 1 2 one_pos hu (by norm_num)) 1
        < 1 - fredholmDet (AiryConj.airyTildeOp u 2 4 two_pos hu (by norm_num)) 1 ∧
      1 - fredholmDet (AiryConj.airyTildeOp u 2 4 two_pos hu (by norm_num)) 1
        < 2 * (1 - fredholmDet (AiryConj.airyTildeOp u 1 2 one_pos hu (by norm_num)) 1) := by
  filter_upwards [eventually_piT_joint_consistent,
    AiryConj.eventually_detOneAiryTilde_one_eq_weight_two,
    eventually_detOneAiryTilde_two_eq_weight_four,
    eventually_fredholmDet_airyTildeOp_eq one_pos (by norm_num : (1 : ℝ) + 1 ≤ 2),
    eventually_fredholmDet_airyTildeOp_eq two_pos (by norm_num : (2 : ℝ) + 1 ≤ 4)]
    with u h hd1 hd2 he1 he2 hu
  rw [he1 hu, he2 hu, ← hd1 hu, ← hd2 hu]
  exact h

/-! ### Record 3 (`QRTwoIntervalLaw`): guard, range and uniform summability -/

/-- **Record 3 is never vacuous in `u`.** For every `u ≥ 8`, the block index
`j = 2` is admissible (`2 + 2 ≤ √(2u)`). So at every large level the record
constrains at least one pair `(Y₀, Y₂)`.

Guards against: a guard edit that makes the record's `∀ j` range empty for
all large `u`. The record would then be trivially true and carry no
information. -/
theorem qrTwoInterval_two_admissible {u : ℝ} (hu : 8 ≤ u) :
    2 ≤ (2 : ℕ) ∧ ((2 : ℕ) : ℝ) + 2 ≤ Real.sqrt (2 * u) := by
  refine ⟨le_rfl, ?_⟩
  push_cast
  exact Real.le_sqrt_of_sq_le (by nlinarith)

/-- **Record 3 right-hand side is positive on the guard.** If `2 ≤ j` and
`j + 2 ≤ √(2u)`, then `detOneKCup u (j − 1)` is the genuine exp-trace
determinant of `K̃∪`, not the junk `0`, and it is positive. So record 3 never
forces `ℙ(Y₀ ≤ u ∧ Y_j ≤ u) ≤ 0`.

Guards against: an edit to `detOneKCup` (its admissibility test or its junk
branch) that makes the record's right-hand side `0` or negative on the guard. -/
theorem detOneKCup_pos_of_guard {u : ℝ} {j : ℕ} (hj : 2 ≤ j)
    (hju : (j : ℝ) + 2 ≤ Real.sqrt (2 * u)) :
    0 < detOneKCup u ((j : ℝ) - 1) := by
  obtain ⟨hr1, hu, hadr⟩ := qrTwoInterval_guard hj hju
  have hr0 : (0 : ℝ) < (j : ℝ) - 1 := by linarith
  rw [detOneKCup, dite_eq_left ⟨hr0, hu, hadr⟩]
  exact fredholmDetOne_one_pos _

/-- **Record 3 right-hand side (entire determinant) is eventually positive,
uniformly in `j`.** Eventually in `u`, for every `j` with `2 ≤ j` and
`j + 2 ≤ √(2u)`, `0 < detKCup u (j − 1)`. So record 3, as stated with the
entire determinant, never forces `ℙ(Y₀ ≤ u ∧ Y_j ≤ u) ≤ 0` at large
`u`. Unlike the exp-trace form, the entire determinant over `ℝ` is not positive
by construction; positivity comes from the disk agreement
`eventually_detKCup_eq_detOneKCup` and `detOneKCup_pos_of_guard`.

Guards against: an edit to `detKCup` (its admissibility test, junk branch or
operator) that makes the record's right-hand side `0` or negative on the guard,
or that breaks its agreement with `detOneKCup` on the disk. -/
theorem detKCup_pos_eventually :
    ∀ᶠ u in atTop, ∀ j : ℕ, 2 ≤ j → (j : ℝ) + 2 ≤ Real.sqrt (2 * u) →
      0 < detKCup u ((j : ℝ) - 1) := by
  filter_upwards [eventually_detKCup_eq_detOneKCup] with u h j hj hju
  rw [h j hj hju]
  exact detOneKCup_pos_of_guard hj hju

/-- **Record 3: Plemelj summability, uniformly over the admissible `j`.**
Eventually in `u`, for every admissible block index `j` and every
`L²` proof of `K̃∪(u, j − 1)`, the Plemelj series
`∑ tr(K̃∪ᵐ⁺¹)/(m+1)` is summable. So `QRTwoIntervalLaw` never uses the
`tsum = 0` junk value of `fredholmDetOne`, at any admissible `j`. This is
`qrTwoInterval_kcup_small_uniform` at `ε = 1`, with contrib
`summable_trace_pow_div`. (The record itself is stated with the
entire `detKCup`; this guards the derived exp-trace form
`QRTwoIntervalLaw.law_detOne`.)

Guards against: the same edits as `qrTwoInterval_kcup_small_uniform`. The
junk value would make the record assert `ℙ(Y₀ ≤ u ∧ Y_j ≤ u) = 1`. -/
theorem qrTwoInterval_plemeljSummable_uniform :
    ∀ᶠ u in atTop, ∀ j : ℕ, 2 ≤ j → (j : ℝ) + 2 ≤ Real.sqrt (2 * u) →
      ∀ hk : MemLp (AiryTwoInt.kcupKerT (Real.sqrt (2 * u)) u ((j : ℝ) - 1)) 2
          (volume.prod volume),
        Summable fun m : ℕ => trace ((kernelOperator hk) ^ (m + 1)) / ((m + 1 : ℕ) : ℝ) := by
  filter_upwards [qrTwoInterval_kcup_small_uniform one_pos] with u h j hj hju hk
  obtain ⟨hr1, hu0, hadr⟩ := qrTwoInterval_guard hj hju
  exact summable_trace_pow_div
    (AiryTwoInt.isTraceClass_kcupKerT (by linarith) hu0 hadr hk) (h j hj hju hk).1

/-! ### Record 3: the implied joint exceedance (envelope and sign) -/

/-- **Record 3: two-sided envelope for the implied joint exceedance.** Take
records 1 and 3, a probability measure and stationarity. Then
`joint_exceed_eq_detComb` forces
`ℙ(Y₀ > u ∧ Y_j > u) = X(u, j) := 1 − 2 det₁(I − K̃₁) + det₁(I − K̃∪(u, j − 1))`,
after `det₁(I − K̃₂) = det₁(I − K̃₁)` (contrib
`AiryTwoInt.fredholmDetOne_k2KerT_eq_k1KerT`) and the operator identification
`det₁(I − K̃₁) = AiryConj.detOneAiryTilde u 1`. A probability needs
`0 ≤ X ≤ π₁`. This theorem proves, without any record, for `0 < χ < 1`, that
eventually in `u` and for every `j ≥ 2` with `j − 1 ≤ χ√(2u)`,
`|X(u, j)| ≤ C₁ u^K (1+r)^K e^{−2κu^{3/2}} + C₂ (1+r)^{1/2} e^{−𝒥_u(r)}`,
with `r = j − 1`. So `X ≥ −(that envelope)`: the implied probability is
non-negative up to an error far smaller than `ρ(u)`.

**Sign: certified (see `qrTwoInterval_implied_joint_pos` below).** The envelope
alone does not fix the sign: `X = tr C̃_r + R`, and `R` holds the positive
independence term `≈ π₁²`, bounded here only in absolute value. The sign is
certified separately by the second-order Plemelj route: contrib
`AiryTwoInt.twoInt_joint_ge_plemelj_eventually` (exact `δ`-algebra and assembly,
with the near-sign bound `AiryTwoInt.trace_crKerT_ge_neg_discharged_a`),
`AiryTwoInt.trace_k1k2_le_discharged` (`tr(K̃₁K̃₂) = o(ρ²)`),
`AiryTwoInt.hsNorm_crKerT_le_discharged` (`‖C̃_r‖₂ = o(ρ)`), and the absorption
against the sharp-tail expansion `AiryTwoInt.twoInt_joint_ge_assoc_eventually`
(`X ≥ (1 − ε)π₁²`, `π₁ ≥ ρ(u)/2`).

**What is still NOT certified.** (i) The compatibility `X ≤ π₁`, i.e.
`det₁(I − K̃∪) ≤ det₁(I − K̃₁)`. (ii) The strip `χ√(2u) < j − 1 ≤ √(2u) − 3` of
the record's guard: every result here holds for `j − 1 ≤ χ√(2u)` with a fixed
`χ < 1`, and the thresholds grow as `χ → 1`. (iii) The exact association bound
`X ≥ π₁²` (`ProcessAssociated`); only `X ≥ (1 − ε)π₁²` is proved.

Guards against: an edit to `kcupKer`, `k1Ker`/`k2Ker` or `crKer` that makes
the implied joint probability large in absolute value, of order `ρ(u)` or
bigger, for some admissible `j`. In particular it catches a sign error large
enough to put the implied probability visibly below `0`. -/
theorem qrTwoInterval_implied_joint_abs_le {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C₁ K C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ u in atTop, ∀ j : ℕ, 2 ≤ j →
      (j : ℝ) - 1 ≤ χ * Real.sqrt (2 * u) →
      (j : ℝ) + 2 ≤ Real.sqrt (2 * u) ∧
      |1 - 2 * AiryConj.detOneAiryTilde u 1 + detOneKCup u ((j : ℝ) - 1)|
        ≤ C₁ * u ^ K * (1 + ((j : ℝ) - 1)) ^ K
              * Real.exp (-2 * ((4 * Real.sqrt 2 / 3) * u ^ (3 / 2 : ℝ)))
          + C₂ * (1 + ((j : ℝ) - 1)) ^ (1 / 2 : ℝ)
              * Real.exp (-AiryConj.saddleJ u ((j : ℝ) - 1)) := by
  obtain ⟨C₁, K, M₁, hC₁, H1⟩ := AiryTwoInt.joint_detOne_comb_abs_le hχ0 hχ1
  obtain ⟨C₂, M₂, hC₂, H2⟩ := AiryTwoInt.abs_trace_crKerT_le_discharged hχ0 hχ1
  obtain ⟨Ma, hMa⟩ := AiryTwoInt.exists_admissible_M₀ hχ0 hχ1
  refine ⟨C₁, K, C₂, hC₁, hC₂, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max M₁ M₂) Ma)] with u hu j hj hrM
  have hM₁ : M₁ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have hM₂ : M₂ ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hMa' : Ma ≤ u := le_trans (le_max_right _ _) hu
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  set r : ℝ := (j : ℝ) - 1 with hr
  have hr1 : (1 : ℝ) ≤ r := by linarith
  obtain ⟨hadr, ha2, hu1⟩ := hMa u r hMa' hr1 hrM
  have hu0 : (0 : ℝ) < u := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  refine ⟨by linarith, ?_⟩
  have hk1 := AiryTwoInt.memLp_k1KerT hu0 ha2
  have hk2 := AiryTwoInt.memLp_k2KerT hr0 hu0 hadr
  have hkcup := AiryTwoInt.memLp_kcupKerT hr0 hu0 hadr
  have hcr := AiryTwoInt.memLp_crKerT hr0 hu0 hadr
  have hk1t := AiryTwoInt.isTraceClass_k1KerT hu0 ha2 hk1
  have hk2t := AiryTwoInt.isTraceClass_k2KerT hr0 hu0 hadr hk2
  have hkcupt := AiryTwoInt.isTraceClass_kcupKerT hr0 hu0 hadr hkcup
  have hb1 := H1 hM₁ hr1 hrM hadr hk1 hk2 hkcup hcr hk1t hk2t hkcupt
  have hb2 := H2 hM₂ hr1 hrM hcr
  -- `det₁(I − K̃₂) = det₁(I − K̃₁)`
  have hd21 : fredholmDetOne (kernelOperator hk2) hk2t 1
      = fredholmDetOne (kernelOperator hk1) hk1t 1 :=
    AiryTwoInt.fredholmDetOne_k2KerT_eq_k1KerT hr0 hu0 hadr hk1 hk2 hk1t hk2t 1
  -- operator identification: `det₁(I − K̃₁) = detOneAiryTilde u 1`
  have hd1 : AiryConj.detOneAiryTilde u 1 = fredholmDetOne (kernelOperator hk1) hk1t 1 := by
    have h2 : (1 : ℝ) + 1 ≤ Real.sqrt (2 * u) := by linarith
    rw [AiryConj.detOneAiryTilde, dite_eq_left ⟨one_pos, hu0, h2⟩]
    exact AiryTwoInt.fredholmDetOne_congr
      (AiryTwoInt.kernelOperator_k1KerT_eq_airyTildeOp hu0 ha2).symm _ _ 1
  -- the record's right-hand side
  have hdc : detOneKCup u r = fredholmDetOne (kernelOperator hkcup) hkcupt 1 := by
    rw [detOneKCup, dite_eq_left ⟨hr0, hu0, hadr⟩]
  rw [hd1, hdc]
  set X := 1 - fredholmDetOne (kernelOperator hk1) hk1t 1
    - fredholmDetOne (kernelOperator hk2) hk2t 1
    + fredholmDetOne (kernelOperator hkcup) hkcupt 1 with hX
  have hXeq : 1 - 2 * fredholmDetOne (kernelOperator hk1) hk1t 1
      + fredholmDetOne (kernelOperator hkcup) hkcupt 1 = X := by
    rw [hX, hd21]; ring
  rw [hXeq]
  set Tr := trace (kernelOperator hcr)
  have htri : |X| ≤ |X - Tr| + |Tr| := by
    have h := abs_add_le (X - Tr) Tr
    rwa [sub_add_cancel] at h
  linarith

/-- **Record 3: the implied joint exceedance in association shape.** For
`0 < χ < 1` and `ε > 0`, eventually in `u`, for every `j ≥ 2` with
`j − 1 ≤ χ√(2u)`: `π₁ = 1 − det₁(I − Ã_{u,1}) ≥ ρ(u)/2` and
`X(u, j) = 1 − 2 det₁(I − K̃₁) + det₁(I − K̃∪(u, j − 1)) ≥ (1 − ε) π₁²`.
No record is assumed. This is the association consistency `X ≥ π₁²(1 − o(1))`.
Proof: contrib `AiryTwoInt.twoInt_joint_ge_assoc_eventually` (Plemelj route,
the trace and Hilbert–Schmidt bounds above, the sharp-tail expansion), transported by
`det₁(I − K̃₂) = det₁(I − K̃₁)` and the operator
identification, exactly as in `qrTwoInterval_implied_joint_abs_le`.

Guards against: an edit to `kcupKer`, `k1Ker`/`k2Ker`, `crKer` or the weights
that pushes the implied joint probability below `(1 − ε) π₁²` for some
admissible `j`, in particular below `0`. -/
theorem qrTwoInterval_implied_joint_ge_assoc {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u in atTop, ∀ j : ℕ, 2 ≤ j → (j : ℝ) - 1 ≤ χ * Real.sqrt (2 * u) →
      AiryConj.rhoM u / 2 ≤ 1 - AiryConj.detOneAiryTilde u 1 ∧
      (1 - ε) * (1 - AiryConj.detOneAiryTilde u 1) ^ 2
        ≤ 1 - 2 * AiryConj.detOneAiryTilde u 1 + detOneKCup u ((j : ℝ) - 1) := by
  obtain ⟨M₀, H⟩ := AiryTwoInt.twoInt_joint_ge_assoc_eventually hχ0 hχ1 hε
  obtain ⟨Ma, hMa⟩ := AiryTwoInt.exists_admissible_M₀ hχ0 hχ1
  filter_upwards [eventually_ge_atTop (max M₀ Ma)] with u hu j hj hrM
  have hM₀ : M₀ ≤ u := le_trans (le_max_left _ _) hu
  have hMa' : Ma ≤ u := le_trans (le_max_right _ _) hu
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  set r : ℝ := (j : ℝ) - 1 with hr
  have hr1 : (1 : ℝ) ≤ r := by linarith
  obtain ⟨hadr, ha2, hu1⟩ := hMa u r hMa' hr1 hrM
  have hu0 : (0 : ℝ) < u := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have hk1 := AiryTwoInt.memLp_k1KerT hu0 ha2
  have hk2 := AiryTwoInt.memLp_k2KerT hr0 hu0 hadr
  have hkcup := AiryTwoInt.memLp_kcupKerT hr0 hu0 hadr
  have hk1t := AiryTwoInt.isTraceClass_k1KerT hu0 ha2 hk1
  have hk2t := AiryTwoInt.isTraceClass_k2KerT hr0 hu0 hadr hk2
  have hkcupt := AiryTwoInt.isTraceClass_kcupKerT hr0 hu0 hadr hkcup
  obtain ⟨hπ, hX⟩ := H hM₀ hr1 hrM hk1 hk2 hkcup hk1t hk2t hkcupt
  have hd21 : fredholmDetOne (kernelOperator hk2) hk2t 1
      = fredholmDetOne (kernelOperator hk1) hk1t 1 :=
    AiryTwoInt.fredholmDetOne_k2KerT_eq_k1KerT hr0 hu0 hadr hk1 hk2 hk1t hk2t 1
  have hd1 : AiryConj.detOneAiryTilde u 1 = fredholmDetOne (kernelOperator hk1) hk1t 1 :=
    (AiryTwoInt.fredholmDetOne_k1KerT_eq_detOneAiryTilde hu0 ha2 hk1 hk1t).symm
  have hdc : detOneKCup u r = fredholmDetOne (kernelOperator hkcup) hkcupt 1 := by
    rw [detOneKCup, dite_eq_left ⟨hr0, hu0, hadr⟩]
  rw [hd1, hdc]
  have hXeq : 1 - 2 * fredholmDetOne (kernelOperator hk1) hk1t 1
      + fredholmDetOne (kernelOperator hkcup) hkcupt 1
      = 1 - fredholmDetOne (kernelOperator hk1) hk1t 1
        - fredholmDetOne (kernelOperator hk2) hk2t 1
        + fredholmDetOne (kernelOperator hkcup) hkcupt 1 := by
    rw [hd21]; ring
  rw [hXeq]
  exact ⟨hπ, hX⟩

/-- **Record 3: the implied joint exceedance is eventually positive.** For
`0 < χ < 1`, eventually in `u`, for every `j ≥ 2` with `j − 1 ≤ χ√(2u)`,
`0 < 1 − 2 det₁(I − K̃₁) + det₁(I − K̃∪(u, j − 1))` (indeed `≥ π₁²/2 ≥ ρ(u)²/8`).
No record is assumed. With records 1 and 3 this is `ℙ(Y₀ > u ∧ Y_j > u) > 0`.

Guards against: an edit that makes record 3 force a negative (impossible) joint
probability for some admissible `j`. -/
theorem qrTwoInterval_implied_joint_pos {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∀ᶠ u in atTop, ∀ j : ℕ, 2 ≤ j → (j : ℝ) - 1 ≤ χ * Real.sqrt (2 * u) →
      0 < 1 - 2 * AiryConj.detOneAiryTilde u 1 + detOneKCup u ((j : ℝ) - 1) := by
  filter_upwards [qrTwoInterval_implied_joint_ge_assoc hχ0 hχ1 (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_gt_atTop (0 : ℝ)] with u h hu0 j hj hrM
  obtain ⟨hπ, hX⟩ := h j hj hrM
  have hρ : 0 < AiryConj.rhoM u := AiryConj.rhoM_pos hu0
  have hπ0 : 0 < 1 - AiryConj.detOneAiryTilde u 1 := by linarith
  have := pow_pos hπ0 2
  linarith

/-- **Record 3: the implied joint exceedance is eventually non-negative** (the
`0 ≤ X` form of `qrTwoInterval_implied_joint_pos`). -/
theorem qrTwoInterval_implied_joint_nonneg {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∀ᶠ u in atTop, ∀ j : ℕ, 2 ≤ j → (j : ℝ) - 1 ≤ χ * Real.sqrt (2 * u) →
      0 ≤ 1 - 2 * AiryConj.detOneAiryTilde u 1 + detOneKCup u ((j : ℝ) - 1) := by
  filter_upwards [qrTwoInterval_implied_joint_pos hχ0 hχ1] with u h j hj hrM
  exact (h j hj hrM).le

end Airy1Gumbel
