/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.Touching
import Airy1GumbelContrib.TwoInterval.TwoIntervalShift
import Airy1GumbelContrib.TwoInterval.TwoIntervalSumEst
import Airy1GumbelContrib.TwoInterval.TwoIntervalTraceBound

open Filter MeasureTheory
open scoped Topology BigOperators
open HilbertSchmidt

namespace Airy1Gumbel

/-!
# Discharging `separated` from the QR records

The `separated` field of `Airy1BlockExtremes` (`BlockExtremes.lean`) asserts,
for `χ ∈ ((1/2)^{1/3}, 1)`,
`N · ∑_{2 ≤ j ≤ m_N} ℙ(Y₀ > u_N(z), Y_j > u_N(z)) → 0`, with
`m_N = ⌊χ√(2u_N(z))⌋`. The paper obtains it from its
separated-block estimate: a pointwise bound for `ℙ(Y₀ > M, Y_{r+1} > M)`,
`1 ≤ r ≤ χ√(2M)`, summed over `r`. (Step numbers in this file and in
`TwoInterval/` label the stages of the Lean proof, not those of the posted paper.) The pointwise bound starts from
the paper's joint-exceedance lemma, the inclusion–exclusion formula
`ℙ(Y₀ > M, Y_{r+1} > M) = 1 − det(I − K̃₁) − det(I − K̃₂) + det(I − K̃∪)`.

The proof is assembled in eight steps G1–G8:

* **G1** is the record `QRTwoIntervalLaw` (`ExternalInputs.lean`),
  the paper's two-interval determinant formula. It is proved in the paper
  (in an appendix), not a literature theorem. It is stated with the entire `detKCup`; `QRTwoIntervalLaw.law_detOne`
  (with `qrTwoInterval_guard`, `qrTwoInterval_kcup_small_uniform`,
  `detKCup_eq_detOneKCup`, `eventually_detKCup_eq_detOneKCup`,
  `QRTwoIntervalLaw.iff_law_detOne`) gives the exp-trace form used below.
* **G2** `prob_Y0_le_eq_detOne_k1`: `ℙ(Y₀ ≤ u) = det₁(I − K̃₁)` from
  `QRUnitBlockLaw` and the factorization
  `AiryTwoInt.kernelOperator_k1KerT_eq_airyTildeOp`.
* **G3** is the contrib theorem `AiryTwoInt.fredholmDetOne_k2KerT_eq_k1KerT`, used as is.
* **G4** `joint_exceed_eq_detComb`: inclusion–exclusion with stationarity, i.e.
  the inclusion–exclusion formula of the paper's joint-exceedance lemma.
* **G5 + G7** `separated_pair_bound`: the paper's pointwise separated-pair bound, by
  a triangle step between the contrib headlines
  `AiryTwoInt.joint_detOne_comb_abs_le` and
  `AiryTwoInt.abs_trace_crKerT_le_discharged`, with the exponent lifted to
  `max K 0` and the factor `M^{1/2}` inserted so that both terms have the shape
  of the Step-5 sums.
* **G6** `sum_Icc_two_le_sum_Icc_one`: the reindexing `j = r + 1`.
* **G8** `separated_sum_tendsto_zero`: composition of the Step-5 headlines
  `AiryTwoInt.stepFive_first_sum_ratio_tendsto_zero` /
  `AiryTwoInt.stepFive_second_sum_ratio_tendsto_zero` with
  `gumbelU_tendsto_atTop`, `gumbel_normalization` and `exp_neg_airyH_eq`.
* `separated_of_QR`: the `separated` field, verbatim.
* `Airy1BlockExtremes.ofQR₃` and the six `_of_QR₃` headline corollaries: the
  conditional Gumbel limits (the paper's main theorem (Theorem 1.1)) with none of
  `sharp_tail`, `touching`, `separated` in the hypothesis list.

The `Airy1BlockExtremes` structure, `ofQR`/`ofQR₂` and their corollaries are
untouched.

## Remarks on the formalization

1. **`χ` range.** The field quantifies over `χ ∈ ((1/2)^{1/3}, 1)`, and
   `separated_sum_tendsto_zero` proves the limit for every `χ ∈ (0, 1)`. The
   lower bound `(1/2)^{1/3}` is used by the paper in the mesoscopic
   section, not here; every contrib headline needs only `0 < χ < 1`.
2. **`M^{1/2}` insertion (G7).** The trace term
   `C(1 + r)^{1/2} e^{−𝒥_M(r)}` is bounded by `C M^{1/2}(1 + r)^{1/2} e^{−𝒥_M(r)}`
   for `M ≥ 1`, so that the first Step-5 headline applies at `K = 1/2`. The
   paper's pointwise separated-pair bound instead absorbs both terms into one
   `C M^K (1+r)^K`; the two forms are equivalent for the sum.
3. **Sign of `K`.** `AiryTwoInt.joint_detOne_comb_abs_le` returns an unsigned
   `K`; the second Step-5 headline needs `0 ≤ K`. It is lifted to `max K 0`
   using `M ≥ 1` and `1 + r ≥ 1`.
4. **Reindexing.** The field sums over `j ∈ [2, m_N]`, and the Step-5 headlines sum
   over `r ∈ [1, m_N]`. The shift `r = j − 1` lands in `[1, m_N − 1]`, and the
   extra term `r = m_N` is nonnegative, so it is added (`sum_Icc_two_le_sum_Icc_one`).
-/

/-! ### Elementary helpers -/

/-- If `c ≤ √(2u)` with `c > 0` then `u > 0` (`Real.sqrt` is `0` on
nonpositive arguments). Used to read `0 < M` off the admissibility condition of the paper's
joint-exceedance lemma
`r + 3 ≤ √(2M)`. -/
theorem pos_of_le_sqrt_two_mul {u c : ℝ} (hc : 0 < c) (h : c ≤ Real.sqrt (2 * u)) :
    0 < u := by
  by_contra hneg
  have hz : Real.sqrt (2 * u) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith [not_lt.mp hneg])
  linarith

/-- **G6, the reindexing `j = r + 1`** (Step 5 of the proof of the paper's separated-block
estimate, where the pair `(Y₀, Y_{r+1})` has gap `r`): a sum over
`j ∈ [2, m]` of terms dominated by `g (j − 1)` is at most the sum of `g` over
`r ∈ [1, m]`, provided `g ≥ 0` there. -/
theorem sum_Icc_two_le_sum_Icc_one {f g : ℕ → ℝ} {m : ℕ}
    (hg : ∀ r ∈ Finset.Icc 1 m, 0 ≤ g r)
    (hfg : ∀ r : ℕ, 1 ≤ r → r + 1 ≤ m → f (r + 1) ≤ g r) :
    ∑ j ∈ Finset.Icc 2 m, f j ≤ ∑ r ∈ Finset.Icc 1 m, g r := by
  calc ∑ j ∈ Finset.Icc 2 m, f j ≤ ∑ j ∈ Finset.Icc 2 m, g (j - 1) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_Icc] at hj
        have h := hfg (j - 1) (by omega) (by omega)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ j)] at h
    _ = ∑ r ∈ (Finset.Icc 2 m).image (fun j => j - 1), g r := by
        rw [Finset.sum_image]
        intro x hx y hy hxy
        have hx' := Finset.mem_Icc.mp (Finset.mem_coe.mp hx)
        have hy' := Finset.mem_Icc.mp (Finset.mem_coe.mp hy)
        simp only at hxy
        omega
    _ ≤ ∑ r ∈ Finset.Icc 1 m, g r := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr
          rw [Finset.mem_image] at hr
          obtain ⟨j, hj, rfl⟩ := hr
          rw [Finset.mem_Icc] at hj ⊢
          omega
        · intro r hr _
          exact hg r hr

/-! ### G1 in exp-trace form

`QRTwoIntervalLaw` is stated with contrib's entire determinant (`detKCup`).
The consumers below use the exp-trace form `detOneKCup`. The two agree on the
Hilbert–Schmidt disk (contrib `fredholmDet_eq_fredholmDetOne`), and every
admissible `K̃∪` lies there eventually, uniformly in the block index
(`qrTwoInterval_kcup_small_uniform`). -/

/-- **Guard arithmetic for `QRTwoIntervalLaw`.** If `2 ≤ j` and `j + 2 ≤ √(2u)`, then the gap
`r = j − 1` satisfies `r ≥ 1`, and `u > 0` and `r + 3 ≤ √(2u)`. These are
exactly the conditions under which `detOneKCup u r` takes its genuine branch.
Guards against: an edit to the guard of `QRTwoIntervalLaw` or to the
admissibility test of `detOneKCup` that lets the record reach the junk value
`0`. There the record would assert `ℙ(Y₀ ≤ u ∧ Y_j ≤ u) = 0`. -/
theorem qrTwoInterval_guard {u : ℝ} {j : ℕ} (hj : 2 ≤ j)
    (hju : (j : ℝ) + 2 ≤ Real.sqrt (2 * u)) :
    1 ≤ (j : ℝ) - 1 ∧ 0 < u ∧ ((j : ℝ) - 1) + 3 ≤ Real.sqrt (2 * u) := by
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  refine ⟨by linarith, pos_of_le_sqrt_two_mul (by linarith : (0 : ℝ) < (j : ℝ) + 2) hju,
    by linarith⟩

/-- **`QRTwoIntervalLaw`: `K̃∪` is small, uniformly over the admissible `j`.** For every
`ε > 0`, eventually in `u`, for every block index `j` with `2 ≤ j` and
`j + 2 ≤ √(2u)`, and every `L²` proof `hk` of the kernel
`kcupKerT √(2u) u (j − 1)`, both `‖K̃∪‖₂ < ε` and `|tr K̃∪| < ε` hold. The
`eventually` sits outside `∀ j`, so the threshold in `u` does not depend on
`j`.

Proof: contrib `AiryTwoInt.twoInt_kcup_bounds` gives the bound
`C u^K (1+r)^K e^{−(2/3)a³}` with `a = √(2u)`. The guard gives
`1 + r ≤ a`, and `a² = 2u` gives `u(1+r) ≤ ua = a³/2 ≤ a³`. So the bound is
at most `C (a³)^K e^{−(2/3)a³}`, which tends to `0` as `a³ → ∞`, with no
dependence on `r`.

Guards against: an edit to `kcupKer`, to the conjugation `uConj` or to
`twoInt_kcup_bounds` that leaves `K̃∪` off the Hilbert–Schmidt unit disk for
some admissible `j`. There the exp-trace `det₁` need not be the Fredholm
determinant. This lemma is load-bearing, since it is how
`QRTwoIntervalLaw.law_detOne` places every consumed `K̃∪` inside the disk
where the entire `detKCup` equals the exp-trace `detOneKCup`. -/
theorem qrTwoInterval_kcup_small_uniform {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u in atTop, ∀ j : ℕ, 2 ≤ j → (j : ℝ) + 2 ≤ Real.sqrt (2 * u) →
      ∀ hk : MemLp (AiryTwoInt.kcupKerT (Real.sqrt (2 * u)) u ((j : ℝ) - 1)) 2
          (volume.prod volume),
        hsNorm (kernelOperator hk) < ε ∧ |trace (kernelOperator hk)| < ε := by
  obtain ⟨C, K, hC, hK4, H⟩ := AiryTwoInt.twoInt_kcup_bounds
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hlim : Tendsto (fun x : ℝ => x ^ K * Real.exp (-(2 / 3) * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero K (2 / 3) (by norm_num)
  have ht : Tendsto (fun u : ℝ => Real.sqrt (2 * u) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have hC0 : Tendsto (fun u : ℝ => C * (Real.sqrt (2 * u) ^ 3) ^ K
      * Real.exp (-(2 / 3) * Real.sqrt (2 * u) ^ 3)) atTop (𝓝 0) := by
    have := (hlim.comp ht).const_mul C
    rw [mul_zero] at this
    refine this.congr fun u => ?_
    simp only [Function.comp]
    ring
  filter_upwards [hC0.eventually (gt_mem_nhds hε), eventually_ge_atTop (1 : ℝ)]
    with u hlt hu1 j hj hju hk
  obtain ⟨hr1, hu0, hadr⟩ := qrTwoInterval_guard hj hju
  obtain ⟨htr, hhs⟩ := H hu1 hr1 hadr rfl hk
  set a := Real.sqrt (2 * u) with ha
  set r : ℝ := (j : ℝ) - 1 with hr
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * u := Real.sq_sqrt (by linarith)
  have ha3 : a ^ 3 = 2 * u * a := by rw [pow_succ, ha2]
  have h1ra : 1 + r ≤ a := by linarith
  have hprod : u * (1 + r) ≤ a ^ 3 := by
    have h1 : u * (1 + r) ≤ u * a := mul_le_mul_of_nonneg_left h1ra hu0.le
    have h2 : 0 ≤ u * a := mul_nonneg hu0.le ha0
    linarith
  have hpow : u ^ K * (1 + r) ^ K ≤ (a ^ 3) ^ K := by
    rw [← Real.mul_rpow hu0.le (by linarith)]
    exact Real.rpow_le_rpow (by positivity) hprod hK0
  have hE : 0 ≤ Real.exp (-(2 / 3) * a ^ 3) := (Real.exp_pos _).le
  have hB : C * u ^ K * (1 + r) ^ K * Real.exp (-(2 / 3) * a ^ 3)
      ≤ C * (a ^ 3) ^ K * Real.exp (-(2 / 3) * a ^ 3) := by
    calc C * u ^ K * (1 + r) ^ K * Real.exp (-(2 / 3) * a ^ 3)
        = C * ((u ^ K * (1 + r) ^ K) * Real.exp (-(2 / 3) * a ^ 3)) := by ring
      _ ≤ C * ((a ^ 3) ^ K * Real.exp (-(2 / 3) * a ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hE) hC.le
      _ = C * (a ^ 3) ^ K * Real.exp (-(2 / 3) * a ^ 3) := by ring
  exact ⟨lt_of_le_of_lt (hhs.trans hB) hlt, lt_of_le_of_lt (htr.trans hB) hlt⟩

/-- **`detKCup = detOneKCup` on the disk.** On the admissible region, if
`‖K̃∪‖₂ < 1`, the entire determinant `det(I − K̃∪)` equals the exp-trace
`det₁(I − K̃∪)` (contrib `HilbertSchmidt.fredholmDet_eq_fredholmDetOne` at
coupling `1`). -/
theorem detKCup_eq_detOneKCup {M r : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hadr : r + 3 ≤ Real.sqrt (2 * M))
    (hs : hsNorm (kernelOperator (AiryTwoInt.memLp_kcupKerT hr hM hadr)) < 1) :
    detKCup M r = detOneKCup M r := by
  unfold detKCup detOneKCup
  rw [dite_eq_left ⟨hr, hM, hadr⟩, dite_eq_left ⟨hr, hM, hadr⟩]
  exact fredholmDet_eq_fredholmDetOne _ (by rw [norm_one, one_mul]; exact hs)

/-- **The `QRTwoIntervalLaw` operators lie on the disk, uniformly.** Eventually in `u`, for every
block index `j` with `2 ≤ j` and `j + 2 ≤ √(2u)`,
`detKCup u (j − 1) = detOneKCup u (j − 1)`. The threshold in `u` does not
depend on `j`. -/
theorem eventually_detKCup_eq_detOneKCup :
    ∀ᶠ u in atTop, ∀ j : ℕ, 2 ≤ j → (j : ℝ) + 2 ≤ Real.sqrt (2 * u) →
      detKCup u ((j : ℝ) - 1) = detOneKCup u ((j : ℝ) - 1) := by
  filter_upwards [qrTwoInterval_kcup_small_uniform one_pos] with u h j hj hju
  obtain ⟨hr1, hu0, hadr⟩ := qrTwoInterval_guard hj hju
  exact detKCup_eq_detOneKCup (by linarith) hu0 hadr
    (h j hj hju (AiryTwoInt.memLp_kcupKerT (by linarith) hu0 hadr)).1

/-- **`QRTwoIntervalLaw` in exp-trace form**: `QRTwoIntervalLaw`, stated with the
entire determinant `detKCup`, gives the former exp-trace law
`ℙ(Y₀ ≤ u ∧ Y_j ≤ u) = det₁(I − K̃∪(u, j − 1))` eventually in `u`, for every
admissible `j`. -/
theorem QRTwoIntervalLaw.law_detOne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} (h : QRTwoIntervalLaw Y P) :
    ∀ᶠ u in atTop, ∀ j : ℕ, 2 ≤ j → (j : ℝ) + 2 ≤ Real.sqrt (2 * u) →
      P.real {ω | Y 0 ω ≤ u ∧ Y j ω ≤ u} = detOneKCup u ((j : ℝ) - 1) := by
  filter_upwards [h.law, eventually_detKCup_eq_detOneKCup] with u hlaw hdet j hj hju
  rw [hlaw j hj hju, hdet j hj hju]

/-- **The entire-determinant statement is equivalent to the exp-trace one, `QRTwoIntervalLaw`**: `QRTwoIntervalLaw`
(entire determinant `detKCup`) holds iff the former exp-trace record
`∀ᶠ u, ∀ j ≥ 2, j + 2 ≤ √(2u) → ℙ(Y₀ ≤ u ∧ Y_j ≤ u) = detOneKCup u (j − 1)`
holds. -/
theorem QRTwoIntervalLaw.iff_law_detOne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} :
    QRTwoIntervalLaw Y P ↔ ∀ᶠ u in atTop, ∀ j : ℕ, 2 ≤ j → (j : ℝ) + 2 ≤ Real.sqrt (2 * u) →
      P.real {ω | Y 0 ω ≤ u ∧ Y j ω ≤ u} = detOneKCup u ((j : ℝ) - 1) := by
  refine ⟨fun h => h.law_detOne, fun h => ⟨?_⟩⟩
  filter_upwards [h, eventually_detKCup_eq_detOneKCup] with u hlaw hdet j hj hju
  rw [hlaw j hj hju, hdet j hj hju]

/-! ### G2 and G4: the paper's joint-exceedance lemma -/

/-- **G2: the one-block law as `det₁(I − K̃₁)`** (proof of the paper's joint-exceedance
lemma, "Formula (1.14) of QR2012"): eventually in `u`, whenever
`2 ≤ √(2u)`, `ℙ(Y₀ ≤ u) = det₁(I − K̃₁)` for any `L²`/trace-class proofs of the
contrib kernel `AiryTwoInt.k1KerT`. Proof: the complement of
`QRUnitBlockLaw.detOne_form` (the record at QR's weight `a = 2`, re-weighted to
the paper's determinant form by the proved re-weighting bridge) gives
`AiryConj.detOneAiryTilde u 1`, and the factorization
`AiryTwoInt.kernelOperator_k1KerT_eq_airyTildeOp`
identifies the operator. -/
theorem prob_Y0_le_eq_detOne_k1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    (qr : QRUnitBlockLaw Y P) :
    ∀ᶠ u in atTop, 2 ≤ Real.sqrt (2 * u) →
      ∀ (hk1 : MemLp (AiryTwoInt.k1KerT (Real.sqrt (2 * u)) u) 2 (volume.prod volume))
      (hk1t : IsTraceClass (kernelOperator hk1)),
      P.real {ω | Y 0 ω ≤ u} = fredholmDetOne (kernelOperator hk1) hk1t 1 := by
  filter_upwards [qr.detOne_form] with u hlaw ha hk1 hk1t
  have hu : 0 < u := pos_of_le_sqrt_two_mul two_pos ha
  have hset : {ω | Y 0 ω ≤ u} = {ω | Y 0 ω > u}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [hset, Airy1Gumbel.measureReal_compl (measurableSet_lt measurable_const (Y_meas 0)),
    hlaw, sub_sub_cancel]
  have h2 : (1 : ℝ) + 1 ≤ Real.sqrt (2 * u) := by linarith
  rw [AiryConj.detOneAiryTilde, dite_eq_left ⟨one_pos, hu, h2⟩]
  exact AiryTwoInt.fredholmDetOne_congr
    (AiryTwoInt.kernelOperator_k1KerT_eq_airyTildeOp hu ha).symm _ _ 1

/-- **G4: the inclusion–exclusion formula of the paper's joint-exceedance lemma**: eventually in `u`, for every integer gap `r ≥ 1` with
`r + 3 ≤ √(2u)` and any `L²`/trace-class proofs of the contrib kernels,
`ℙ(Y₀ > u ∧ Y_{r+1} > u) = 1 − det₁(I − K̃₁) − det₁(I − K̃₂) + det₁(I − K̃∪)`.
Inputs: inclusion–exclusion; stationarity `ℙ(Y_{r+1} > u) = ℙ(Y₀ > u)`; G2
(`prob_Y0_le_eq_detOne_k1`); G3 `det₁(I − K̃₂) = det₁(I − K̃₁)` (contrib
`AiryTwoInt.fredholmDetOne_k2KerT_eq_k1KerT`); and the
record `QRTwoIntervalLaw` (the paper's two-interval determinant formula) at `j = r + 1`. -/
theorem joint_exceed_eq_detComb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
    (qr : QRUnitBlockLaw Y P) (two : QRTwoIntervalLaw Y P) :
    ∀ᶠ u in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) + 3 ≤ Real.sqrt (2 * u) →
      ∀ (hk1 : MemLp (AiryTwoInt.k1KerT (Real.sqrt (2 * u)) u) 2 (volume.prod volume))
        (hk2 : MemLp (AiryTwoInt.k2KerT (Real.sqrt (2 * u)) u r) 2 (volume.prod volume))
        (hkcup : MemLp (AiryTwoInt.kcupKerT (Real.sqrt (2 * u)) u r) 2 (volume.prod volume))
        (hk1t : IsTraceClass (kernelOperator hk1)) (hk2t : IsTraceClass (kernelOperator hk2))
        (hkcupt : IsTraceClass (kernelOperator hkcup)),
      P.real {ω | Y 0 ω > u ∧ Y (r + 1) ω > u}
        = 1 - fredholmDetOne (kernelOperator hk1) hk1t 1
          - fredholmDetOne (kernelOperator hk2) hk2t 1
          + fredholmDetOne (kernelOperator hkcup) hkcupt 1 := by
  filter_upwards [prob_Y0_le_eq_detOne_k1 Y_meas qr, two.law_detOne] with u hG2 hlaw
  intro r hr1 hadr hk1 hk2 hkcup hk1t hk2t hkcupt
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have ha2 : (2 : ℝ) ≤ Real.sqrt (2 * u) := by linarith
  have hu : 0 < u := pos_of_le_sqrt_two_mul two_pos ha2
  -- G2
  have h1 : P.real {ω | Y 0 ω ≤ u} = fredholmDetOne (kernelOperator hk1) hk1t 1 :=
    hG2 ha2 hk1 hk1t
  -- G3
  have h2 : fredholmDetOne (kernelOperator hk2) hk2t 1
      = fredholmDetOne (kernelOperator hk1) hk1t 1 :=
    AiryTwoInt.fredholmDetOne_k2KerT_eq_k1KerT hr0 hu hadr hk1 hk2 hk1t hk2t 1
  -- G1 (the record) at `j = r + 1`
  have hjr : (((r + 1 : ℕ) : ℝ)) + 2 ≤ Real.sqrt (2 * u) := by push_cast; linarith
  have h3 := hlaw (r + 1) (by omega) hjr
  have hcast : (((r + 1 : ℕ) : ℝ)) - 1 = r := by push_cast; ring
  rw [hcast] at h3
  have h3' : detOneKCup u r = fredholmDetOne (kernelOperator hkcup) hkcupt 1 := by
    rw [detOneKCup, dite_eq_left ⟨hr0, hu, hadr⟩]
  -- stationarity
  have hS : P.real {ω | Y (r + 1) ω > u} = P.real {ω | Y 0 ω > u} := by
    rw [measureReal_def, measureReal_def, stat_marginal u (r + 1)]
  -- inclusion–exclusion
  have hA : MeasurableSet {ω | Y 0 ω > u} := measurableSet_lt measurable_const (Y_meas 0)
  have hB : MeasurableSet {ω | Y (r + 1) ω > u} :=
    measurableSet_lt measurable_const (Y_meas (r + 1))
  have hU := Airy1Gumbel.measureReal_union_add_inter (P := P) {ω | Y 0 ω > u}
    {ω | Y (r + 1) ω > u} hB
  have hle0 : {ω | Y 0 ω ≤ u} = {ω | Y 0 ω > u}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  have hc0 : P.real {ω | Y 0 ω ≤ u} = 1 - P.real {ω | Y 0 ω > u} := by
    rw [hle0, Airy1Gumbel.measureReal_compl hA]
  have hboth : {ω | Y 0 ω ≤ u ∧ Y (r + 1) ω ≤ u}
      = ({ω | Y 0 ω > u} ∪ {ω | Y (r + 1) ω > u})ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union, not_or, not_lt]
  have hcb : P.real {ω | Y 0 ω ≤ u ∧ Y (r + 1) ω ≤ u}
      = 1 - P.real ({ω | Y 0 ω > u} ∪ {ω | Y (r + 1) ω > u}) := by
    rw [hboth, Airy1Gumbel.measureReal_compl (hA.union hB)]
  have hI : {ω | Y 0 ω > u ∧ Y (r + 1) ω > u}
      = {ω | Y 0 ω > u} ∩ {ω | Y (r + 1) ω > u} := rfl
  rw [hI]
  linarith

/-! ### G5 + G7: the paper's pointwise separated-pair bound -/

/-- **G5 + G7: the paper's pointwise separated-pair bound** (via a triangle step): for
`0 < χ < 1` there are `C₁, K, C₂ ≥ 0` such that,
eventually in `u`, for every integer `r` with `1 ≤ r ≤ χ√(2u)`,

  `ℙ(Y₀ > u ∧ Y_{r+1} > u) ≤ C₁ u^K ((1+r)^K e^{−2κu^{3/2}})
      + C₂ u^{1/2} ((1+r)^{1/2} e^{−𝒥_u(r)})`,

with `κ = 4√2/3` and `𝒥` = `AiryConj.saddleJ` (the paper's saddle exponent). The
probability is the determinant combination of G4 (`joint_exceed_eq_detComb`),
which is `≤ |comb − Tr C̃_r| + |Tr C̃_r|`. The first term is bounded by the contrib
`AiryTwoInt.joint_detOne_comb_abs_le` (Steps 1/3/4), the second by
`AiryTwoInt.abs_trace_crKerT_le_discharged` (Step 2). The admissibility
`r + 3 ≤ √(2u)` comes from `AiryTwoInt.exists_admissible_M₀`, and all kernel
binders are filled with the `memLp_*`/`isTraceClass_*` lemmas. The exponent
is lifted to `max K 0` and the factor `u^{1/2} ≥ 1` is inserted (Remarks 2-3 of the module docstring). -/
theorem separated_pair_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
    (qr : QRUnitBlockLaw Y P) (two : QRTwoIntervalLaw Y P) {χ : ℝ}
    (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C₁ K C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ K ∧ 0 ≤ C₂ ∧ ∀ᶠ u in atTop, 1 ≤ u ∧
      ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ χ * Real.sqrt (2 * u) →
      P.real {ω | Y 0 ω > u ∧ Y (r + 1) ω > u}
        ≤ C₁ * u ^ K * ((1 + (r : ℝ)) ^ K
              * Real.exp (-2 * ((4 * Real.sqrt 2 / 3) * u ^ (3 / 2 : ℝ))))
          + C₂ * u ^ (1 / 2 : ℝ) * ((1 + (r : ℝ)) ^ (1 / 2 : ℝ)
              * Real.exp (-AiryConj.saddleJ u r)) := by
  obtain ⟨C₁, K, M₁, hC₁, H1⟩ := AiryTwoInt.joint_detOne_comb_abs_le hχ0 hχ1
  obtain ⟨C₂, M₂, hC₂, H2⟩ := AiryTwoInt.abs_trace_crKerT_le_discharged hχ0 hχ1
  obtain ⟨Ma, hMa⟩ := AiryTwoInt.exists_admissible_M₀ hχ0 hχ1
  refine ⟨C₁, max K 0, C₂, hC₁.le, le_max_right _ _, hC₂.le, ?_⟩
  filter_upwards [joint_exceed_eq_detComb Y_meas stat_marginal qr two,
    eventually_ge_atTop (max (max M₁ M₂) (max Ma 1))] with u hjoint hu
  have hM₁ : M₁ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have hM₂ : M₂ ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hMa' : Ma ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hu
  have hu1 : 1 ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hu
  refine ⟨hu1, ?_⟩
  intro r hr1 hrM
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  obtain ⟨hadr, ha2, -⟩ := hMa u r hMa' hr1' hrM
  have hu0 : (0 : ℝ) < u := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have hk1 := AiryTwoInt.memLp_k1KerT hu0 ha2
  have hk2 := AiryTwoInt.memLp_k2KerT hr0 hu0 hadr
  have hkcup := AiryTwoInt.memLp_kcupKerT hr0 hu0 hadr
  have hcr := AiryTwoInt.memLp_crKerT hr0 hu0 hadr
  have hk1t := AiryTwoInt.isTraceClass_k1KerT hu0 ha2 hk1
  have hk2t := AiryTwoInt.isTraceClass_k2KerT hr0 hu0 hadr hk2
  have hkcupt := AiryTwoInt.isTraceClass_kcupKerT hr0 hu0 hadr hkcup
  have heq := hjoint r hr1 hadr hk1 hk2 hkcup hk1t hk2t hkcupt
  have hb1 := H1 hM₁ hr1' hrM hadr hk1 hk2 hkcup hcr hk1t hk2t hkcupt
  have hb2 := H2 hM₂ hr1' hrM hcr
  set X := 1 - fredholmDetOne (kernelOperator hk1) hk1t 1
    - fredholmDetOne (kernelOperator hk2) hk2t 1
    + fredholmDetOne (kernelOperator hkcup) hkcupt 1 with hX
  set Tr := trace (kernelOperator hcr) with hTr
  set E := Real.exp (-2 * ((4 * Real.sqrt 2 / 3) * u ^ (3 / 2 : ℝ))) with hE
  set e := Real.exp (-AiryConj.saddleJ u r) with he
  -- the triangle step
  have htri : X ≤ |X - Tr| + |Tr| := by
    have h := abs_add_le (X - Tr) Tr
    rw [sub_add_cancel] at h
    linarith [le_abs_self X]
  -- G7: lift `K` to `max K 0`
  have h1r : (1 : ℝ) ≤ 1 + r := by linarith
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hlift : C₁ * u ^ K * (1 + (r : ℝ)) ^ (K : ℝ) * E
      ≤ C₁ * u ^ (max K 0) * ((1 + (r : ℝ)) ^ (max K 0) * E) := by
    have hp1 : u ^ K ≤ u ^ (max K 0) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (le_max_left _ _)
    have hp2 : (1 + (r : ℝ)) ^ K ≤ (1 + (r : ℝ)) ^ (max K 0) :=
      Real.rpow_le_rpow_of_exponent_le h1r (le_max_left _ _)
    have hq1 : 0 ≤ u ^ K := Real.rpow_nonneg hu0.le _
    have hq2 : 0 ≤ (1 + (r : ℝ)) ^ K := Real.rpow_nonneg (by linarith) _
    have hq3 : 0 ≤ u ^ (max K 0) := Real.rpow_nonneg hu0.le _
    calc C₁ * u ^ K * (1 + (r : ℝ)) ^ (K : ℝ) * E
        = C₁ * (u ^ K * ((1 + (r : ℝ)) ^ K * E)) := by ring
      _ ≤ C₁ * (u ^ (max K 0) * ((1 + (r : ℝ)) ^ (max K 0) * E)) := by
          apply mul_le_mul_of_nonneg_left _ hC₁.le
          apply mul_le_mul hp1 _ (mul_nonneg hq2 hE0) hq3
          exact mul_le_mul_of_nonneg_right hp2 hE0
      _ = C₁ * u ^ (max K 0) * ((1 + (r : ℝ)) ^ (max K 0) * E) := by ring
  -- G7: insert `u^{1/2} ≥ 1`
  have hhalf : C₂ * (1 + (r : ℝ)) ^ (1 / 2 : ℝ) * e
      ≤ C₂ * u ^ (1 / 2 : ℝ) * ((1 + (r : ℝ)) ^ (1 / 2 : ℝ) * e) := by
    have hY0 : 0 ≤ C₂ * ((1 + (r : ℝ)) ^ (1 / 2 : ℝ) * e) :=
      mul_nonneg hC₂.le (mul_nonneg (Real.rpow_nonneg (by linarith) _) he0)
    have h1u : (1 : ℝ) ≤ u ^ (1 / 2 : ℝ) := Real.one_le_rpow hu1 (by norm_num)
    calc C₂ * (1 + (r : ℝ)) ^ (1 / 2 : ℝ) * e
        = C₂ * ((1 + (r : ℝ)) ^ (1 / 2 : ℝ) * e) * 1 := by ring
      _ ≤ C₂ * ((1 + (r : ℝ)) ^ (1 / 2 : ℝ) * e) * u ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left h1u hY0
      _ = C₂ * u ^ (1 / 2 : ℝ) * ((1 + (r : ℝ)) ^ (1 / 2 : ℝ) * e) := by ring
  rw [heq]
  linarith

/-! ### G8: the Step-5 sum and the `N`-normalization -/

/-- The ρ-profile `ρ̂(M) = M^{1/4} e^{−κM^{3/2}}` (the definition of `ρ`,
without the constant `C_*`) of the contrib Step-5 headlines equals
`ρ(M)/C_*`: `AiryConj.rhoM M = C_* · ρ̂(M)`. -/
theorem rhoM_eq_Cstar_mul_profile (M : ℝ) :
    AiryConj.rhoM M
      = AiryConj.Cstar * (M ^ (1 / 4 : ℝ) * Real.exp (-(4 * Real.sqrt 2 / 3) * M ^ (3 / 2 : ℝ))) := by
  unfold AiryConj.rhoM AiryConj.kappaC
  ring

/-- **G8: the `separated` limit for every `χ ∈ (0, 1)`** (Step 5 of the paper's
separated-block estimate, on the Gumbel scale `u_N(z) = a_N + b_N z`):
`N · ∑_{2 ≤ j ≤ m_N} ℙ(Y₀ > u_N, Y_j > u_N) → 0`, where
`m_N = ⌊χ√(2u_N)⌋` (`mN`), which is the Step-5 floor `⌊χ√(2M)⌋` at
`M = u_N`. Proof: eventually in `N`, the reindexed sum (`sum_Icc_two_le_sum_Icc_one`) is
bounded termwise by `separated_pair_bound`, which gives `S₁(u_N) + S₂(u_N)` with
`S_i` the two Step-5 sums. Then `N S_i(u_N) = (S_i/ρ̂)(u_N) · Nρ̂(u_N)`, where
`(S_i/ρ̂)(M) → 0` (`AiryTwoInt.stepFive_first_sum_ratio_tendsto_zero` at
`K = 1/2`, `AiryTwoInt.stepFive_second_sum_ratio_tendsto_zero`) and
`Nρ̂(u_N) = Nρ(u_N)/C_* → e^{−z}/C_*` (`gumbel_normalization`,
`exp_neg_airyH_eq`). Squeeze with `0 ≤ ℙ`. -/
theorem separated_sum_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
    (qr : QRUnitBlockLaw Y P) (two : QRTwoIntervalLaw Y P) (z : ℝ) {χ : ℝ}
    (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    Tendsto (fun N : ℕ =>
      (N : ℝ) * ∑ j ∈ Finset.Icc 2 (mN χ z N),
        P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0) := by
  obtain ⟨C₁, K, C₂, hC₁, hK, hC₂, hev⟩ :=
    separated_pair_bound Y_meas stat_marginal qr two hχ0 hχ1
  -- the profile and the two Step-5 sums
  set ρh : ℝ → ℝ := fun M =>
    M ^ (1 / 4 : ℝ) * Real.exp (-(4 * Real.sqrt 2 / 3) * M ^ (3 / 2 : ℝ)) with hρh
  set S₁ : ℝ → ℝ := fun M => C₂ * M ^ (1 / 2 : ℝ) *
    ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2 * M)⌋₊,
      (1 + (r : ℝ)) ^ (1 / 2 : ℝ) * Real.exp (-AiryConj.saddleJ M (r : ℝ)) with hS₁
  set S₂ : ℝ → ℝ := fun M => C₁ * M ^ K *
    ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2 * M)⌋₊,
      (1 + (r : ℝ)) ^ (K : ℝ) * Real.exp (-2 * ((4 * Real.sqrt 2 / 3) * M ^ (3 / 2 : ℝ)))
    with hS₂
  have hT1 : Tendsto (fun M => S₁ M / ρh M) atTop (𝓝 0) :=
    AiryTwoInt.stepFive_first_sum_ratio_tendsto_zero C₂ (1 / 2) hχ0
  have hT2 : Tendsto (fun M => S₂ M / ρh M) atTop (𝓝 0) :=
    AiryTwoInt.stepFive_second_sum_ratio_tendsto_zero C₁ K hK hχ0
  have hu := gumbelU_tendsto_atTop z
  -- `N ρ̂(u_N) → e^{-z}/C_*`
  have hρ : Tendsto (fun N : ℕ => (N : ℝ) * AiryConj.rhoM (gumbelU N z)) atTop
      (𝓝 (Real.exp (-z))) := by
    refine (gumbel_normalization z).congr' ?_
    filter_upwards [hu.eventually_gt_atTop 0] with N hN
    rw [exp_neg_airyH_eq hN]
  have hCs : AiryConj.Cstar ≠ 0 := by
    unfold AiryConj.Cstar
    positivity
  have hNρh : Tendsto (fun N : ℕ => (N : ℝ) * ρh (gumbelU N z)) atTop
      (𝓝 (Real.exp (-z) / AiryConj.Cstar)) := by
    refine (hρ.div_const AiryConj.Cstar).congr fun N => ?_
    rw [rhoM_eq_Cstar_mul_profile, hρh]
    field_simp
  -- the majorant tends to `0`
  have hG : Tendsto (fun N : ℕ =>
      (S₁ (gumbelU N z) / ρh (gumbelU N z) + S₂ (gumbelU N z) / ρh (gumbelU N z))
        * ((N : ℝ) * ρh (gumbelU N z))) atTop (𝓝 0) := by
    have h := ((hT1.comp hu).add (hT2.comp hu)).mul hNρh
    rw [add_zero, zero_mul] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hG ?_ ?_
  · exact Eventually.of_forall fun N =>
      mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => measureReal_nonneg _)
  · filter_upwards [hu.eventually hev] with N hN
    obtain ⟨hu1, hb⟩ := hN
    set u := gumbelU N z with hudef
    have hu0 : 0 < u := by linarith
    have hρpos : 0 < ρh u := mul_pos (Real.rpow_pos_of_pos hu0 _) (Real.exp_pos _)
    -- the reindexed termwise bound
    have hsum : ∑ j ∈ Finset.Icc 2 (mN χ z N), P.real {ω | Y 0 ω > u ∧ Y j ω > u}
        ≤ S₂ u + S₁ u := by
      have hm : mN χ z N = ⌊χ * Real.sqrt (2 * u)⌋₊ := rfl
      have hfloor : ((⌊χ * Real.sqrt (2 * u)⌋₊ : ℕ) : ℝ) ≤ χ * Real.sqrt (2 * u) :=
        Nat.floor_le (mul_nonneg hχ0.le (Real.sqrt_nonneg _))
      calc ∑ j ∈ Finset.Icc 2 (mN χ z N), P.real {ω | Y 0 ω > u ∧ Y j ω > u}
          ≤ ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2 * u)⌋₊,
              (C₁ * u ^ K * ((1 + (r : ℝ)) ^ K
                  * Real.exp (-2 * ((4 * Real.sqrt 2 / 3) * u ^ (3 / 2 : ℝ))))
                + C₂ * u ^ (1 / 2 : ℝ) * ((1 + (r : ℝ)) ^ (1 / 2 : ℝ)
                  * Real.exp (-AiryConj.saddleJ u r))) := by
            rw [hm]
            apply sum_Icc_two_le_sum_Icc_one
            · intro r _
              have h1 : 0 ≤ (1 + (r : ℝ)) := by positivity
              have := Real.rpow_nonneg hu0.le K
              have := Real.rpow_nonneg hu0.le (1 / 2 : ℝ)
              have := Real.rpow_nonneg h1 K
              have := Real.rpow_nonneg h1 (1 / 2 : ℝ)
              positivity
            · intro r hr1 hrm
              apply hb r hr1
              have : ((r : ℕ) : ℝ) + 1 ≤ ((⌊χ * Real.sqrt (2 * u)⌋₊ : ℕ) : ℝ) := by
                exact_mod_cast hrm
              linarith
        _ = S₂ u + S₁ u := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc (N : ℝ) * ∑ j ∈ Finset.Icc 2 (mN χ z N), P.real {ω | Y 0 ω > u ∧ Y j ω > u}
        ≤ (N : ℝ) * (S₂ u + S₁ u) :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
      _ = (S₁ u / ρh u + S₂ u / ρh u) * ((N : ℝ) * ρh u) := by
          field_simp
          ring

/-- **`separated` from the QR records** (the paper's separated-block estimate,
summed in Step 5, on the Gumbel scale): exactly
the `separated` field of `Airy1BlockExtremes`. The inputs are `QRUnitBlockLaw`
([QuastelRemenik2012, Theorem 4] + the paper's determinant form) and the
record `QRTwoIntervalLaw` (the paper's two-interval determinant formula, proved in an
appendix of the paper). The hypothesis
`(1/2)^{1/3} < χ` is used only to get `0 < χ`
(`separated_sum_tendsto_zero` holds on all of `(0, 1)`; Remark 1 of the module docstring). -/
theorem separated_of_QR {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
    (qr : QRUnitBlockLaw Y P) (two : QRTwoIntervalLaw Y P) :
    ∀ (z χ : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 →
      Tendsto (fun N : ℕ =>
        (N : ℝ) * ∑ j ∈ Finset.Icc 2 (mN χ z N),
          P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0) := by
  intro z χ hχ hχ1
  have hχ0 : 0 < χ := lt_trans (Real.rpow_pos_of_pos (by norm_num) _) hχ
  exact separated_sum_tendsto_zero Y_meas stat_marginal qr two z hχ0 hχ1

/-! ### Smart constructor and `_of_QR₃` headline corollaries -/

section OfQR₃

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (Y : ℕ → Ω → ℝ) (Y_meas : ∀ j, Measurable (Y j))
  (alpha : ℕ → ℝ) (alpha_nonneg : ∀ m, 0 ≤ alpha m)
  (mixC : ℝ) (mixC_pos : 0 < mixC) (mixc : ℝ) (mixc_pos : 0 < mixc)
  (alpha_bound : ∀ m, alpha m ≤ mixC * Real.exp (-mixc * ((m : ℝ) - 1) ^ 3))
  (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
  (stat_pair : ∀ (u : ℝ) (i d : ℕ),
    P {ω | Y i ω > u ∧ Y (i + d) ω > u} = P {ω | Y 0 ω > u ∧ Y d ω > u})
  (qr : QRUnitBlockLaw Y P) (qr₂ : QRTwoBlockLaw Y P) (two : QRTwoIntervalLaw Y P)
  (mixing_tail : ∃ A : ℝ, 0 < A ∧ 1 < mixc * A ^ 3 ∧
    Tendsto (fun N : ℕ => (N : ℝ) * ∑' j : ℕ, alpha (qN A N + j)) atTop (𝓝 0))
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

include Y_meas alpha_nonneg mixC_pos mixc_pos alpha_bound stat_marginal stat_pair qr qr₂ two
  mixing_tail mesoscopic decouple pair_mix

/-- Smart constructor for `Airy1BlockExtremes`: every field
except `sharp_tail`, `touching` and `separated` is supplied directly.
`sharp_tail` is discharged from `QRUnitBlockLaw` by `sharp_tail_of_QRUnitBlockLaw`
(the paper's sharp one-block tail); `touching` from `QRUnitBlockLaw` +
`QRTwoBlockLaw` by `touching_of_QR` (the paper's touching-block estimate);
and `separated` from `QRUnitBlockLaw` + `QRTwoIntervalLaw` by `separated_of_QR`
(the paper's separated-block estimate). The first two records are
[QuastelRemenik2012, Theorem 4] + the paper's determinant form. The third is
the paper's two-interval determinant formula, proved in the paper. -/
def Airy1BlockExtremes.ofQR₃ : Airy1BlockExtremes P where
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
  separated := separated_of_QR Y_meas stat_marginal qr two
  mesoscopic := mesoscopic
  decouple := decouple
  pair_mix := pair_mix

/-- **Conditional Gumbel limit, integer-block form, with `sharp_tail`,
`touching` and `separated` discharged** (the paper's main theorem (Theorem 1.1); block form of
`Airy1BlockExtremes.gumbel_limit`): the hypothesis list carries `QRUnitBlockLaw`,
`QRTwoBlockLaw` ([QuastelRemenik2012, Theorem 4] + the paper's determinant form at
`T = 1, 2`) and the record `QRTwoIntervalLaw`
(the paper's two-interval determinant formula) in place of `sharp_tail`,
`touching` and `separated`. -/
theorem Airy1BlockExtremes.gumbel_limit_of_QR₃ (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ j ∈ Finset.range N, Y j ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  (Airy1BlockExtremes.ofQR₃ Y Y_meas alpha alpha_nonneg mixC mixC_pos mixc mixc_pos
    alpha_bound stat_marginal stat_pair qr qr₂ two mixing_tail mesoscopic
    decouple pair_mix).gumbel_limit z

/-- **Conditional Gumbel limit, continuum integer-length form, with
`sharp_tail`, `touching` and `separated` discharged** (the paper's main theorem (Theorem 1.1);
corollary of `Airy1ContinuousMax.gumbel_limit_continuum`):
`ℙ(M_N ≤ u_N(z)) → e^{-e^{-z}}`, with `QRUnitBlockLaw`, `QRTwoBlockLaw` and the record
`QRTwoIntervalLaw` in place of the three fields. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_QR₃ (C : Airy1ContinuousMax P)
    (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum (Airy1BlockExtremes.ofQR₃ Y Y_meas alpha alpha_nonneg mixC
    mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂ two mixing_tail
    mesoscopic decouple pair_mix) hY z

/-- **Normalized integer-length Gumbel limit, with `sharp_tail`, `touching` and
`separated` discharged** (the paper's main theorem (Theorem 1.1); corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_normalized`): `(M_N - a_N)/b_N`
converges in law to the standard Gumbel distribution, with `QRUnitBlockLaw`,
`QRTwoBlockLaw` and the record
`QRTwoIntervalLaw` in place of the three fields. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_normalized_of_QR₃
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ),
      (C.A x ω - gumbelA N) / gumbelB N ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_normalized (Airy1BlockExtremes.ofQR₃ Y Y_meas alpha
    alpha_nonneg mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂
    two mixing_tail mesoscopic decouple pair_mix) hY z

/-- **Perturbed-level integer-length Gumbel limit, with `sharp_tail`,
`touching` and `separated` discharged** (the first step of the real-length
extension of the paper's main theorem (Theorem 1.1); corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto`), with `QRUnitBlockLaw`,
`QRTwoBlockLaw` and the record
`QRTwoIntervalLaw` in place of the three fields. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto_of_QR₃
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) (w : ℕ → ℝ)
    (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N (w N)})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_of_tendsto (Airy1BlockExtremes.ofQR₃ Y Y_meas alpha
    alpha_nonneg mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂
    two mixing_tail mesoscopic decouple pair_mix) hY z w hw

/-- **Real-length conditional Gumbel limit, with `sharp_tail`, `touching` and
`separated` discharged** (the paper's main theorem (Theorem 1.1), real `T → ∞`; corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_real`): `ℙ(M_T ≤ u_T(z)) → e^{-e^{-z}}`,
with `QRUnitBlockLaw`, `QRTwoBlockLaw` and the
the record `QRTwoIntervalLaw` in place of the three
fields. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_of_QR₃
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun T : ℝ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T, C.A x ω ≤ gumbelUR T z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_real (Airy1BlockExtremes.ofQR₃ Y Y_meas alpha alpha_nonneg
    mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂ two
    mixing_tail mesoscopic decouple pair_mix) hY z

/-- **The paper's headline, with `sharp_tail`, `touching` and `separated`
discharged** (the paper's main theorem (Theorem 1.1), normalized real-length shape; corollary
of `Airy1ContinuousMax.gumbel_limit_continuum_real_normalized`):
`(M_T - a_T)/b_T` converges in law to the standard Gumbel distribution as
`T → ∞`, with `QRUnitBlockLaw`, `QRTwoBlockLaw` and the
the record `QRTwoIntervalLaw` in place of the three
fields. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QR₃
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun T : ℝ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (C.A x ω - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_real_normalized (Airy1BlockExtremes.ofQR₃ Y Y_meas alpha
    alpha_nonneg mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂
    two mixing_tail mesoscopic decouple pair_mix) hY z

end OfQR₃

end Airy1Gumbel
