/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.SharpTail
import Airy1GumbelContrib.AiryKernel.Touching

open Filter MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace Airy1Gumbel

/-!
# Discharging `touching` from the QR block laws

The `touching` field of `Airy1BlockExtremes` (`BlockExtremes.lean`) asserts
`N · ℙ(Y₀ > u_N(z), Y₁ > u_N(z)) → 0`. The paper obtains it from
its touching-block estimate,

  `ℙ(Y₀ > M, Y₁ > M) ~ ρ(M)/(4M)`,

whose proof is stationarity plus inclusion–exclusion,
`ℙ(Y₀ > M, Y₁ > M) = 2π₁(M) − π₂(M)`, followed by the paper's sharp one-block tail
at `T = 1` and `T = 2`. Here
`π_T(M) = ℙ{sup_{0≤x≤T} A₁(x) > M}` and
`Y_j = sup_{j≤x≤j+1} A₁(x)`. The block laws are
[QuastelRemenik2012, Theorem 4] (the one-block determinant formula) at QR's own
conjugation weight `a = 2T`; the paper's determinant form
(weight `√(2u)`) is derived from them.

* `detOneAiryTilde_two_eq_weight_four`, `eventually_detOneAiryTilde_two_eq_weight_four`:
  the `T = 2` re-weighting `det₁(I − Ã_{u,2})` at `a = √(2u)` equals the
  exp-trace determinant at QR's weight `a = 4`, for `u ≥ 9/2` (from contrib
  `AiryConj.detOneAiryTilde_eq_fredholmDetOne`).
* `QRTwoBlockLaw.law_detOne`, `QRTwoBlockLaw.iff_law_detOne` the
  record, stated with contrib's entire `fredholmDet`, is equivalent to its
  former exp-trace form at `a = 4`.
* `QRTwoBlockLaw.detOne_form`, `QRTwoBlockLaw.iff_detOne_form`: the record at
  `a = 4` is equivalent to the paper's determinant form
  `ℙ(Y₀ > u ∨ Y₁ > u) = 1 − detOneAiryTilde u 2`.

* `pair_adjacent_eq`: inclusion–exclusion with stationarity,
  `ℙ(Y₀ > u ∧ Y₁ > u) = 2ℙ(Y₀ > u) − ℙ(Y₀ > u ∨ Y₁ > u)`.
* `QRTwoBlockLaw.of_continuum`: the pathwise block identification
  `max(Y₀, Y₁) = sup_{[0,2]} A₁` (the block-identification step behind `QRTwoBlockLaw`),
  discharged from a continuum-level `[0, 2]` law for an `Airy1ContinuousMax`
  bundle.
* `pair_adjacent_isEquivalent`: the paper's touching-block estimate,
  `ℙ(Y₀ > u ∧ Y₁ > u) ~ ρ(u)/(4u)`, from `QRUnitBlockLaw`, `QRTwoBlockLaw` and
  the contrib determinant-form Corollary `AiryConj.touchDet_isEquivalent`.
* `pair_adjacent_isBigO`: the `O(ρ(u)/u)` form, from `AiryConj.touchDet_isBigO`.
* `touching_of_QR`: the `touching` field. It combines the `O(ρ/u)` bound with
  `N ρ(u_N(z)) → e^{-z}` (`gumbel_normalization`, `exp_neg_airyH_eq`) and
  `1/u_N(z) → 0`.
* `Airy1BlockExtremes.ofQR₂`: a smart constructor taking every field of
  `Airy1BlockExtremes` except `sharp_tail` and `touching`, plus
  `QRUnitBlockLaw` and `QRTwoBlockLaw`.
* `Airy1BlockExtremes.gumbel_limit_of_QR₂` and the five
  `Airy1ContinuousMax.gumbel_limit_continuum*_of_QR₂` corollaries: the headline
  conditional Gumbel limits (the paper's main theorem (Theorem 1.1)) with neither `sharp_tail`
  nor `touching` in the hypothesis list.

The `Airy1BlockExtremes` structure, `Airy1BlockExtremes.ofQR` and the `_of_QR`
corollaries (`SharpTail.lean`) are untouched.

## Remarks on the formalization

1. **No two-interval route.** The touching-block estimate is the gap-`0` case. The
   two-interval lemmas (the paper's two-interval determinant formula, `r > 0`;
   the paper's joint-exceedance lemma, `r ≥ 1`) and every declaration of `TwoInterval/`
   exclude it, and the paper handles it separately. Its proof
   uses only the paper's sharp one-block tail at `T = 1, 2`. Nothing here routes
   through `TwoInterval/`.
2. **The `T = 2` input is a hypothesis record, mirroring the one-block case.** The paper
   applies the paper's sharp one-block tail to `π₂` directly. Lean applies the determinant-form sharp tail of the contrib library to
   `1 − detOneAiryTilde · 2`, and the identification
   `π₂(u) = ℙ(Y₀ > u ∨ Y₁ > u)` enters through `QRTwoBlockLaw`, exactly as the one-block
   case handles `π₁` through `QRUnitBlockLaw`.
3. **Eventual records.** Both laws are asserted `∀ᶠ u in atTop`. At QR's
   weight `a = 2T` there is no weight threshold. The records
   use contrib's entire `fredholmDet`; the exp-trace `det₁` the consumers use
   agrees with it on the Hilbert–Schmidt disk, which the operators enter
   eventually (`eventually_hsNorm_airyTildeOp_lt`,
   `eventually_fredholmDet_airyTildeOp_eq`). The re-weighting to
   `detOneAiryTilde u 2` needs `u ≥ 9/2`.
4. **The field consumes only `O(ρ/u)`.** The `~ ρ/(4u)` of the Corollary is
   proved (`pair_adjacent_isEquivalent`) for fidelity, but `touching_of_QR`
   uses only `pair_adjacent_isBigO`. The sharp constant `1/4` is not
   load-bearing for the Gumbel limit.
5. **Stationarity is used once,** at `i = 1`, through `stat_marginal` in
   `Measure` form, converted to `P.real`. `stat_pair` is not used.
6. **Measurability in `QRTwoBlockLaw.of_continuum`.** `Airy1ContinuousMax`
   carries no measurability of the block maxima, and the complement step
   `ℙ(Sᶜ) = 1 − ℙ(S)` needs it, so that theorem takes
   `Y_meas : ∀ j, Measurable (C.Y j)` (the bundle field `Y_meas` of
   `Airy1BlockExtremes`).
-/

/-! ### QR's weight at `T = 2`: the re-weighting bridge -/

/-- **QR's weight at `T = 2`** ([QuastelRemenik2012], their trace-class proposition, `U = e^{-2(r-ℓ)x}`, here
`a = 2T = 4`): for `M ≥ 9/2`, the paper's `det₁(I − Ã_{M,2})` at
`a = √(2M)` equals the exp-trace determinant of `airyTildeOp M 2 4`. The
weight `a = 4` is admissible at `T = 2` for every `M > 0` (`T + 1 = 3 ≤ 4`);
`M ≥ 9/2` gives `3 ≤ √(2M)`, the validity condition of `detOneAiryTilde M 2`.
The `T = 2` analogue of contrib `AiryConj.detOneAiryTilde_one_eq_weight_two`,
from contrib `AiryConj.detOneAiryTilde_eq_fredholmDetOne`. -/
theorem detOneAiryTilde_two_eq_weight_four {M : ℝ} (hM : 9 / 2 ≤ M) (hM0 : 0 < M) :
    AiryConj.detOneAiryTilde M 2 = HilbertSchmidt.fredholmDetOne
      (AiryConj.airyTildeOp M 2 4 two_pos hM0 (by norm_num))
      (AiryConj.isTraceClass_airyTildeOp two_pos hM0 (by norm_num)) 1 := by
  have hsq : (2 : ℝ) + 1 ≤ Real.sqrt (2 * M) := Real.le_sqrt_of_sq_le (by linarith)
  exact AiryConj.detOneAiryTilde_eq_fredholmDetOne two_pos hM0 hsq (by norm_num)

/-- Eventual form of `detOneAiryTilde_two_eq_weight_four`, for the `atTop`
records. -/
theorem eventually_detOneAiryTilde_two_eq_weight_four :
    ∀ᶠ M : ℝ in atTop, ∀ hM0 : 0 < M,
      AiryConj.detOneAiryTilde M 2 = HilbertSchmidt.fredholmDetOne
        (AiryConj.airyTildeOp M 2 4 two_pos hM0 (by norm_num))
        (AiryConj.isTraceClass_airyTildeOp two_pos hM0 (by norm_num)) 1 := by
  filter_upwards [eventually_ge_atTop (9 / 2 : ℝ)] with M hM hM0
  exact detOneAiryTilde_two_eq_weight_four hM hM0

/-- **`QRTwoBlockLaw` in exp-trace form**: `QRTwoBlockLaw`, stated with the
entire determinant, gives the former exp-trace law
`ℙ(Y₀ > u ∨ Y₁ > u) = 1 − det₁(I − Ã_{u,2,4})` eventually in `u`, by the disk
agreement `eventually_fredholmDet_airyTildeOp_eq` at `T = 2`, `a = 4`. -/
theorem QRTwoBlockLaw.law_detOne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} (h : QRTwoBlockLaw Y P) :
    ∀ᶠ u in atTop, ∀ hu : 0 < u,
      P.real {ω | Y 0 ω > u ∨ Y 1 ω > u} = 1 - HilbertSchmidt.fredholmDetOne
        (AiryConj.airyTildeOp u 2 4 two_pos hu (by norm_num))
        (AiryConj.isTraceClass_airyTildeOp two_pos hu (by norm_num)) 1 := by
  filter_upwards [h.law, eventually_fredholmDet_airyTildeOp_eq two_pos
    (by norm_num : (2 : ℝ) + 1 ≤ 4)] with u hlaw hdet hu
  rw [hlaw hu, hdet hu]

/-- **The entire-determinant statement is equivalent to the exp-trace one, `T = 2`**: `QRTwoBlockLaw` (entire
determinant) holds iff the former exp-trace record
`∀ᶠ u, ∀ hu, ℙ(Y₀ > u ∨ Y₁ > u) = 1 − det₁(I − Ã_{u,2,4})` holds. -/
theorem QRTwoBlockLaw.iff_law_detOne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} :
    QRTwoBlockLaw Y P ↔ ∀ᶠ u in atTop, ∀ hu : 0 < u,
      P.real {ω | Y 0 ω > u ∨ Y 1 ω > u} = 1 - HilbertSchmidt.fredholmDetOne
        (AiryConj.airyTildeOp u 2 4 two_pos hu (by norm_num))
        (AiryConj.isTraceClass_airyTildeOp two_pos hu (by norm_num)) 1 := by
  refine ⟨fun h => h.law_detOne, fun h => ⟨?_⟩⟩
  filter_upwards [h, eventually_fredholmDet_airyTildeOp_eq two_pos
    (by norm_num : (2 : ℝ) + 1 ≤ 4)] with u hlaw hdet hu
  rw [hlaw hu, hdet hu]

/-- **Re-weighting bridge, `T = 2`** (the paper's determinant form): the
record `QRTwoBlockLaw`, stated at QR's weight `a = 4`, yields the paper's
form `ℙ(Y₀ > u ∨ Y₁ > u) = 1 − det₁(I − Ã_{u,2})` at `a = √(2u)`, eventually
in `u` (`u ≥ 9/2`). -/
theorem QRTwoBlockLaw.detOne_form {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} (h : QRTwoBlockLaw Y P) :
    ∀ᶠ u in atTop,
      P.real {ω | Y 0 ω > u ∨ Y 1 ω > u} = 1 - AiryConj.detOneAiryTilde u 2 := by
  filter_upwards [h.law_detOne, eventually_detOneAiryTilde_two_eq_weight_four,
    eventually_gt_atTop (0 : ℝ)] with u hlaw hdet hu
  rw [hlaw hu, hdet hu]

/-- **The re-weighting is an equivalence, `T = 2`**: `QRTwoBlockLaw` (QR's
weight `a = 4`) holds iff the form
`∀ᶠ u, ℙ(Y₀ > u ∨ Y₁ > u) = 1 − detOneAiryTilde u 2` (weight `√(2u)`) holds. -/
theorem QRTwoBlockLaw.iff_detOne_form {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} :
    QRTwoBlockLaw Y P ↔ ∀ᶠ u in atTop,
      P.real {ω | Y 0 ω > u ∨ Y 1 ω > u} = 1 - AiryConj.detOneAiryTilde u 2 := by
  refine ⟨fun h => h.detOne_form, fun h => QRTwoBlockLaw.iff_law_detOne.mpr ?_⟩
  filter_upwards [h, eventually_detOneAiryTilde_two_eq_weight_four] with u hlaw hdet hu
  rw [hlaw, hdet hu]

/-! ### Inclusion–exclusion and the block identification -/

/-- **Inclusion–exclusion with stationarity** (proof of the paper's touching-block
estimate, "By stationarity and inclusion–exclusion"):
`ℙ(Y₀ > u ∧ Y₁ > u) = 2ℙ(Y₀ > u) − ℙ(Y₀ > u ∨ Y₁ > u)`. Stationarity is used
once, as `ℙ(Y₁ > u) = ℙ(Y₀ > u)` (`stat_marginal` at `i = 1`). -/
theorem pair_adjacent_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
    (u : ℝ) :
    P.real {ω | Y 0 ω > u ∧ Y 1 ω > u}
      = 2 * P.real {ω | Y 0 ω > u} - P.real {ω | Y 0 ω > u ∨ Y 1 ω > u} := by
  have hU := Airy1Gumbel.measureReal_union_add_inter (P := P) {ω | Y 0 ω > u}
    {ω | Y 1 ω > u} (measurableSet_lt measurable_const (Y_meas 1))
  have hS : P.real {ω | Y 1 ω > u} = P.real {ω | Y 0 ω > u} := by
    rw [measureReal_def, measureReal_def, stat_marginal u 1]
  have hI : {ω | Y 0 ω > u ∧ Y 1 ω > u} = {ω | Y 0 ω > u} ∩ {ω | Y 1 ω > u} := rfl
  have hO : {ω | Y 0 ω > u ∨ Y 1 ω > u} = {ω | Y 0 ω > u} ∪ {ω | Y 1 ω > u} := rfl
  rw [hI, hO]
  linarith

/-- **Block identification for the two-block law** (the identification
behind `QRTwoBlockLaw`): if the continuum process of
an `Airy1ContinuousMax` bundle satisfies the [QuastelRemenik2012, Theorem 4]
law on `[0, 2]` (the one-block determinant formula) at QR's weight `a = 4`,
`ℙ{A(x) ≤ u, 0 ≤ x ≤ 2} = det(I − Ã_{u,2,4})` eventually (contrib's entire
determinant `HilbertSchmidt.fredholmDet`, as in the record), then its block
maxima satisfy `QRTwoBlockLaw`. The step `{Y₀ > u ∨ Y₁ > u} = {sup_{[0,2]} A > u}`
holds a.s. by `Airy1ContinuousMax.continuum_event_eq` at `N = 2`. -/
theorem QRTwoBlockLaw.of_continuum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (C : Airy1ContinuousMax P)
    (Y_meas : ∀ j, Measurable (C.Y j))
    (h : ∀ᶠ u in atTop, ∀ hu : 0 < u,
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) 2, C.A x ω ≤ u} = HilbertSchmidt.fredholmDet
        (AiryConj.airyTildeOp u 2 4 two_pos hu (by norm_num)) 1) :
    QRTwoBlockLaw C.Y P where
  law := by
    filter_upwards [h] with u hu hu0
    have hset : {ω | C.Y 0 ω > u ∨ C.Y 1 ω > u}
        = {ω | ∀ j ∈ Finset.range 2, C.Y j ω ≤ u}ᶜ := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Finset.mem_range, not_forall, not_le]
      constructor
      · rintro (h0 | h1)
        · exact ⟨0, by norm_num, h0⟩
        · exact ⟨1, by norm_num, h1⟩
      · rintro ⟨j, hj, hjy⟩
        interval_cases j
        · exact Or.inl hjy
        · exact Or.inr hjy
    have hmeas : MeasurableSet {ω | ∀ j ∈ Finset.range 2, C.Y j ω ≤ u} := by
      have he : {ω | ∀ j ∈ Finset.range 2, C.Y j ω ≤ u}
          = ⋂ j ∈ Finset.range 2, {ω | C.Y j ω ≤ u} := by
        ext ω
        simp
      rw [he]
      exact Finset.measurableSet_biInter _ fun j _ =>
        measurableSet_le (Y_meas j) measurable_const
    have hae := C.continuum_event_eq (N := 2) (by norm_num) u
    simp only [Nat.cast_ofNat] at hae
    have hcong : P.real {ω | ∀ j ∈ Finset.range 2, C.Y j ω ≤ u}
        = P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) 2, C.A x ω ≤ u} := by
      rw [measureReal_def, measureReal_def, measure_congr hae]
    rw [hset, Airy1Gumbel.measureReal_compl hmeas, hcong, hu hu0]

/-! ### The touching-block estimate -/

/-- **The paper's touching-block estimate**: if `ℙ(Y₀ > u)` and
`ℙ(Y₀ > u ∨ Y₁ > u)` are eventually `1 − det₁(I − Ã_{u,1})` and
`1 − det₁(I − Ã_{u,2})` (`QRUnitBlockLaw`, `QRTwoBlockLaw`: the one-block determinant
formula at QR's weight `a = 2T`, re-weighted to the paper's determinant form by
`QRUnitBlockLaw.detOne_form`
and `QRTwoBlockLaw.detOne_form`), then `ℙ(Y₀ > u ∧ Y₁ > u) ~ ρ(u)/(4u)`.
Proof: `pair_adjacent_eq` identifies the probability with
`AiryConj.touchDet u = 2π₁(u) − π₂(u)` eventually, and
`AiryConj.touchDet_isEquivalent` is the contrib determinant-form estimate
(the determinant-form sharp tail at `T = 1, 2`). -/
theorem pair_adjacent_isEquivalent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
    (qr : QRUnitBlockLaw Y P) (qr₂ : QRTwoBlockLaw Y P) :
    (fun u => P.real {ω | Y 0 ω > u ∧ Y 1 ω > u})
      ~[atTop] fun u => AiryConj.rhoM u / (4 * u) := by
  have hev : AiryConj.touchDet =ᶠ[atTop] fun u => P.real {ω | Y 0 ω > u ∧ Y 1 ω > u} := by
    filter_upwards [qr.detOne_form, qr₂.detOne_form] with u h1 h2
    rw [pair_adjacent_eq Y_meas stat_marginal u, h1, h2]
    rfl
  exact AiryConj.touchDet_isEquivalent.congr_left hev

/-- **The paper's touching-block estimate, `O` form**: under the records
`QRUnitBlockLaw` and `QRTwoBlockLaw`,
`ℙ(Y₀ > u ∧ Y₁ > u) = O(ρ(u)/u)`. This is the only form the `touching` field
discharge consumes; it comes from `AiryConj.touchDet_isBigO`. -/
theorem pair_adjacent_isBigO {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
    (qr : QRUnitBlockLaw Y P) (qr₂ : QRTwoBlockLaw Y P) :
    (fun u => P.real {ω | Y 0 ω > u ∧ Y 1 ω > u})
      =O[atTop] fun u => AiryConj.rhoM u / u := by
  have hev : AiryConj.touchDet =ᶠ[atTop] fun u => P.real {ω | Y 0 ω > u ∧ Y 1 ω > u} := by
    filter_upwards [qr.detOne_form, qr₂.detOne_form] with u h1 h2
    rw [pair_adjacent_eq Y_meas stat_marginal u, h1, h2]
    rfl
  exact AiryConj.touchDet_isBigO.congr' hev EventuallyEq.rfl

/-! ### The discharge -/

/-- **`touching` from the QR block laws** (the paper's touching-block
estimate, on the Gumbel scale `u_N(z) = a_N + b_N z`):
`N · ℙ(Y₀ > u_N(z) ∧ Y₁ > u_N(z)) → 0`. Proof: by `pair_adjacent_isBigO`
composed with `u_N(z) → ∞`, the quantity is `O(N ρ(u_N)/u_N)`; and
`N ρ(u_N) = N e^{-H(u_N)} → e^{-z}` (`gumbel_normalization`,
`exp_neg_airyH_eq`, the definition of `ρ`) while `1/u_N → 0`. -/
theorem touching_of_QR {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
    (qr : QRUnitBlockLaw Y P) (qr₂ : QRTwoBlockLaw Y P) (z : ℝ) :
    Tendsto (fun N : ℕ =>
      (N : ℝ) * P.real {ω | Y 0 ω > gumbelU N z ∧ Y 1 ω > gumbelU N z}) atTop (𝓝 0) := by
  have hu := gumbelU_tendsto_atTop z
  have hO := (pair_adjacent_isBigO Y_meas stat_marginal qr qr₂).comp_tendsto hu
  have hO' := (isBigO_refl (fun N : ℕ => (N : ℝ)) atTop).mul hO
  have hρ : Tendsto (fun N : ℕ => (N : ℝ) * AiryConj.rhoM (gumbelU N z)) atTop
      (𝓝 (Real.exp (-z))) := by
    refine (gumbel_normalization z).congr' ?_
    filter_upwards [hu.eventually_gt_atTop 0] with N hN
    rw [exp_neg_airyH_eq hN]
  have hinv : Tendsto (fun N : ℕ => (gumbelU N z)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hu
  have hlim : Tendsto (fun N : ℕ =>
      (N : ℝ) * (AiryConj.rhoM (gumbelU N z) / gumbelU N z)) atTop (𝓝 0) := by
    have h := hρ.mul hinv
    rw [mul_zero] at h
    refine h.congr fun N => ?_
    rw [div_eq_mul_inv, mul_assoc]
  exact hO'.trans_tendsto hlim

/-! ### Smart constructor and `_of_QR₂` headline corollaries -/

section OfQR₂

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (Y : ℕ → Ω → ℝ) (Y_meas : ∀ j, Measurable (Y j))
  (alpha : ℕ → ℝ) (alpha_nonneg : ∀ m, 0 ≤ alpha m)
  (mixC : ℝ) (mixC_pos : 0 < mixC) (mixc : ℝ) (mixc_pos : 0 < mixc)
  (alpha_bound : ∀ m, alpha m ≤ mixC * Real.exp (-mixc * ((m : ℝ) - 1) ^ 3))
  (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
  (stat_pair : ∀ (u : ℝ) (i d : ℕ),
    P {ω | Y i ω > u ∧ Y (i + d) ω > u} = P {ω | Y 0 ω > u ∧ Y d ω > u})
  (qr : QRUnitBlockLaw Y P) (qr₂ : QRTwoBlockLaw Y P)
  (mixing_tail : ∃ A : ℝ, 0 < A ∧ 1 < mixc * A ^ 3 ∧
    Tendsto (fun N : ℕ => (N : ℝ) * ∑' j : ℕ, alpha (qN A N + j)) atTop (𝓝 0))
  (separated : ∀ (z χ : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 →
    Tendsto (fun N : ℕ =>
      (N : ℝ) * ∑ j ∈ Finset.Icc 2 (mN χ z N),
        P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0))
  (mesoscopic : ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
    Tendsto (fun N : ℕ =>
      (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
        P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0))
  (decouple : ∀ (S T : Finset ℕ) (q : ℕ) (u : ℝ),
    (∀ s ∈ S, ∀ t ∈ T, s + q ≤ t) →
    |P.real ({ω | ∀ s ∈ S, Y s ω ≤ u} ∩ {ω | ∀ t ∈ T, Y t ω ≤ u}) -
      P.real {ω | ∀ s ∈ S, Y s ω ≤ u} * P.real {ω | ∀ t ∈ T, Y t ω ≤ u}|
      ≤ alpha q)
  (pair_mix : ∀ (u : ℝ) (j : ℕ),
    P.real {ω | Y 0 ω > u ∧ Y j ω > u} ≤ P.real {ω | Y 0 ω > u} ^ 2 + alpha j)

include Y_meas alpha_nonneg mixC_pos mixc_pos alpha_bound stat_marginal stat_pair qr qr₂
  mixing_tail separated mesoscopic decouple pair_mix

/-- Smart constructor for `Airy1BlockExtremes`: every
field except `sharp_tail` and `touching` is supplied directly. `sharp_tail` is
discharged from `QRUnitBlockLaw` by `sharp_tail_of_QRUnitBlockLaw`
(the paper's sharp one-block tail), and `touching` from
`QRUnitBlockLaw` + `QRTwoBlockLaw` by `touching_of_QR` (the paper's touching-block estimate).
Both records are [QuastelRemenik2012, Theorem 4] at `T = 1` and `T = 2`, each at QR's
weight `a = 2T`. -/
def Airy1BlockExtremes.ofQR₂ : Airy1BlockExtremes P where
  Y := Y
  Y_meas := Y_meas
  alpha := alpha
  alpha_nonneg := alpha_nonneg
  mixC := mixC
  mixC_pos := mixC_pos
  mixc := mixc
  mixc_pos := mixc_pos
  alpha_bound := alpha_bound
  stat_marginal := stat_marginal
  stat_pair := stat_pair
  sharp_tail := sharp_tail_of_QRUnitBlockLaw qr
  touching := touching_of_QR Y_meas stat_marginal qr qr₂
  mixing_tail := mixing_tail
  separated := separated
  mesoscopic := mesoscopic
  decouple := decouple
  pair_mix := pair_mix

/-- **Conditional Gumbel limit, integer-block form, with `sharp_tail` and
`touching` discharged** (the paper's main theorem (Theorem 1.1); block form of
`Airy1BlockExtremes.gumbel_limit`): the hypothesis list carries
`QRUnitBlockLaw` and `QRTwoBlockLaw` ([QuastelRemenik2012, Theorem 4] at
`T = 1, 2`, QR's weight `a = 2T`) in place of `sharp_tail` and
`touching` (the paper's sharp one-block tail and touching-block estimate). -/
theorem Airy1BlockExtremes.gumbel_limit_of_QR₂ (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ j ∈ Finset.range N, Y j ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  (Airy1BlockExtremes.ofQR₂ Y Y_meas alpha alpha_nonneg mixC mixC_pos mixc mixc_pos
    alpha_bound stat_marginal stat_pair qr qr₂ mixing_tail separated mesoscopic
    decouple pair_mix).gumbel_limit z

/-- **Conditional Gumbel limit, continuum integer-length form, with
`sharp_tail` and `touching` discharged** (the paper's main theorem (Theorem 1.1); corollary of
`Airy1ContinuousMax.gumbel_limit_continuum`): `ℙ(M_N ≤ u_N(z)) → e^{-e^{-z}}`,
with `QRUnitBlockLaw` and `QRTwoBlockLaw` in place of
`sharp_tail` and `touching`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_QR₂ (C : Airy1ContinuousMax P)
    (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum (Airy1BlockExtremes.ofQR₂ Y Y_meas alpha alpha_nonneg mixC
    mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂ mixing_tail
    separated mesoscopic decouple pair_mix) hY z

/-- **Normalized integer-length Gumbel limit, with `sharp_tail` and `touching`
discharged** (the paper's main theorem (Theorem 1.1); corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_normalized`): `(M_N - a_N)/b_N`
converges in law to the standard Gumbel distribution, with `QRUnitBlockLaw`
and `QRTwoBlockLaw` in place of `sharp_tail` and `touching`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_normalized_of_QR₂
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ),
      (C.A x ω - gumbelA N) / gumbelB N ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_normalized (Airy1BlockExtremes.ofQR₂ Y Y_meas alpha
    alpha_nonneg mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂
    mixing_tail separated mesoscopic decouple pair_mix) hY z

/-- **Perturbed-level integer-length Gumbel limit, with `sharp_tail` and
`touching` discharged** (the first step of the real-length extension of
the paper's main theorem (Theorem 1.1); corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto`), with `QRUnitBlockLaw`
and `QRTwoBlockLaw` in place of `sharp_tail` and `touching`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto_of_QR₂
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) (w : ℕ → ℝ)
    (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N (w N)})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_of_tendsto (Airy1BlockExtremes.ofQR₂ Y Y_meas alpha
    alpha_nonneg mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂
    mixing_tail separated mesoscopic decouple pair_mix) hY z w hw

/-- **Real-length conditional Gumbel limit, with `sharp_tail` and `touching`
discharged** (the paper's main theorem (Theorem 1.1), real `T → ∞`; corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_real`):
`ℙ(M_T ≤ u_T(z)) → e^{-e^{-z}}`, with `QRUnitBlockLaw` and `QRTwoBlockLaw` in place of
`sharp_tail` and `touching`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_of_QR₂
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun T : ℝ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T, C.A x ω ≤ gumbelUR T z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_real (Airy1BlockExtremes.ofQR₂ Y Y_meas alpha alpha_nonneg
    mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂
    mixing_tail separated mesoscopic decouple pair_mix) hY z

/-- **The paper's headline, with `sharp_tail` and `touching` discharged**
(the paper's main theorem (Theorem 1.1), normalized real-length shape; corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_real_normalized`): `(M_T - a_T)/b_T`
converges in law to the standard Gumbel distribution as `T → ∞`, with
`QRUnitBlockLaw` and `QRTwoBlockLaw` in place of
`sharp_tail` and `touching`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QR₂
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun T : ℝ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (C.A x ω - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_real_normalized (Airy1BlockExtremes.ofQR₂ Y Y_meas alpha
    alpha_nonneg mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂
    mixing_tail separated mesoscopic decouple pair_mix) hY z

end OfQR₂

end Airy1Gumbel
