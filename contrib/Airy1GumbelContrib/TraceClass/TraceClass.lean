/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.HilbertSchmidt.KernelHS
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! # Trace-class operators via Hilbert–Schmidt factorization

Building on `Airy1GumbelContrib.HilbertSchmidt.HilbertSchmidt` (the sum-of-squares Hilbert–Schmidt
enorm `HilbertSchmidt.sumSq` / `HilbertSchmidt.hsENorm`, with basis independence), this file
develops the next layer of the operator-ideal ladder on a Hilbert space `E` over an
`RCLike` field `𝕜`.

## Main definitions

* `HilbertSchmidt.IsTraceClass T`: `T : E →L[𝕜] E` factors as `T = A ∘L B` with `A`, `B`
  Hilbert–Schmidt.  (On Hilbert spaces this is equivalent to the singular-value definition
  `∑' n, sₙ(T) < ⊤`; the factorization form is what the Fredholm-determinant layer needs.)
* `HilbertSchmidt.trace T`: the sum of the diagonal matrix elements `⟪bᵢ, T bᵢ⟫` in the
  canonical Hilbert basis (junk value from `tsum` when the series is not summable).
* `HilbertSchmidt.basisTruncation T b s`: the finite-rank truncation
  `x ↦ ∑ i ∈ s, ⟪b i, x⟫ • T (b i)` of `T` onto the basis vectors indexed by `s : Finset ι`.

## Main results

* `HilbertSchmidt.sumSq_comp_le`, `HilbertSchmidt.sumSq_comp_le_right`: composition with a
  bounded operator on either side multiplies the sum of squares by at most the squared
  operator enorm — the Hilbert–Schmidt class is a two-sided ideal
  (`HilbertSchmidt.IsHilbertSchmidt.comp_left`, `HilbertSchmidt.IsHilbertSchmidt.comp_right`).
* `HilbertSchmidt.enorm_sq_apply_le_sumSq_mul`, `HilbertSchmidt.opENorm_le_sumSq_rpow_half`:
  the operator enorm is bounded by the Hilbert–Schmidt enorm.
* `HilbertSchmidt.IsHilbertSchmidt.isCompactOperator`: Hilbert–Schmidt operators are
  compact, by finite-rank truncation with the tail vanishing
  (`ENNReal.tendsto_tsum_compl_atTop_zero`) and `isCompactOperator_of_tendsto`.
* `HilbertSchmidt.summable_norm_inner_diagonal`: the diagonal series of a trace-class
  operator is absolutely summable (via AM–GM, no separability hypothesis).
* `HilbertSchmidt.tsum_inner_comp_eq`: the trace-swap engine
  `∑' i, ⟪b i, A (B (b i))⟫ = ∑' j, ⟪c j, B (A (c j))⟫` (Parseval + an absolutely
  convergent interchange).
* `HilbertSchmidt.trace_eq_tsum_inner`: basis independence of the trace on trace-class
  operators; `HilbertSchmidt.trace_comp_comm`: `trace (A ∘L B) = trace (B ∘L A)`.
* `HilbertSchmidt.IsTraceClass.isHilbertSchmidt`: trace class implies Hilbert–Schmidt.
  (The converse is false in infinite dimension: the identity on `ℓ²` is not Hilbert–Schmidt,
  and e.g. the diagonal operator `(1/n)` on `ℓ²(ℕ)` is Hilbert–Schmidt but not trace class.)

## Possible extensions

* The evaluation of the 2-regularized Fredholm determinant `det₂(1 - K)` (built for
  Hilbert–Schmidt `K` in `FredholmTwo.lean`) on the Airy-kernel operator.
-/

open Filter
open scoped Topology ENNReal InnerProduct InnerProductSpace
open scoped Classical

namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]

section Composition

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- Composing on the left by a bounded operator: `sumSq (S ∘L T) b ≤ ‖S‖ₑ² * sumSq T b`. -/
theorem sumSq_comp_le (S : F →L[𝕜] G) (T : E →L[𝕜] F) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    sumSq (S ∘L T) b ≤ ‖S‖ₑ ^ 2 * sumSq T b := by
  unfold sumSq
  calc ∑' i, ‖(S ∘L T) (b i)‖ₑ ^ 2
      ≤ ∑' i, (‖S‖ₑ * ‖T (b i)‖ₑ) ^ 2 := by
        apply ENNReal.tsum_le_tsum
        intro i
        rw [ContinuousLinearMap.comp_apply]
        exact pow_le_pow_left' (ContinuousLinearMap.le_opENorm S (T (b i))) 2
    _ = ∑' i, ‖S‖ₑ ^ 2 * ‖T (b i)‖ₑ ^ 2 := tsum_congr fun i => mul_pow _ _ _
    _ = ‖S‖ₑ ^ 2 * ∑' i, ‖T (b i)‖ₑ ^ 2 := ENNReal.tsum_mul_left

/-- The adjoint is an isometry: `‖T†‖ₑ = ‖T‖ₑ`. -/
theorem enorm_adjoint [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F) :
    ‖T†‖ₑ = ‖T‖ₑ :=
  (ContinuousLinearMap.adjoint).enorm_map T

/-- Composing on the right by a bounded operator: `sumSq (S ∘L T) b ≤ ‖T‖ₑ² * sumSq S c`,
via two adjoint flips. -/
theorem sumSq_comp_le_right [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    (S : F →L[𝕜] G) (T : E →L[𝕜] F) {ι ι' : Type*} (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis ι' 𝕜 F) :
    sumSq (S ∘L T) b ≤ ‖T‖ₑ ^ 2 * sumSq S c := by
  calc sumSq (S ∘L T) b
      = sumSq ((S ∘L T)†) (canonicalBasis 𝕜 G) := sumSq_eq_sumSq_adjoint _ b _
    _ = sumSq ((T†) ∘L (S†)) (canonicalBasis 𝕜 G) := by
        rw [ContinuousLinearMap.adjoint_comp]
    _ ≤ ‖T†‖ₑ ^ 2 * sumSq (S†) (canonicalBasis 𝕜 G) := sumSq_comp_le _ _ _
    _ = ‖T‖ₑ ^ 2 * sumSq (S†) (canonicalBasis 𝕜 G) := by rw [enorm_adjoint]
    _ = ‖T‖ₑ ^ 2 * sumSq S c := by
        rw [← sumSq_eq_sumSq_adjoint S c (canonicalBasis 𝕜 G)]

end Composition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- If `T` is Hilbert–Schmidt, its sum of squares on the canonical basis is finite. -/
theorem IsHilbertSchmidt.sumSq_ne_top {T : E →L[𝕜] E} (hT : IsHilbertSchmidt T) :
    sumSq T (canonicalBasis 𝕜 E) ≠ ⊤ := by
  intro h
  apply hT
  show (sumSq T (canonicalBasis 𝕜 E)) ^ (1/2 : ℝ) = ⊤
  rw [h]
  exact ENNReal.top_rpow_of_pos (by norm_num)

/-- If `T` is Hilbert–Schmidt, its sum of squares on any Hilbert basis is finite. -/
theorem IsHilbertSchmidt.sumSq_ne_top_basis {T : E →L[𝕜] E} (hT : IsHilbertSchmidt T)
    {ι : Type*} (b : HilbertBasis ι 𝕜 E) : sumSq T b ≠ ⊤ := by
  rw [sumSq_independent T b (canonicalBasis 𝕜 E)]
  exact hT.sumSq_ne_top

/-- Finiteness of the canonical-basis sum of squares suffices for Hilbert–Schmidt. -/
theorem isHilbertSchmidt_of_sumSq_ne_top (T : E →L[𝕜] E)
    (h : sumSq T (canonicalBasis 𝕜 E) ≠ ⊤) : IsHilbertSchmidt T :=
  ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2) h

/-- The adjoint of a Hilbert–Schmidt operator is Hilbert–Schmidt. -/
theorem IsHilbertSchmidt.adjoint {T : E →L[𝕜] E} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (T†) := by
  apply isHilbertSchmidt_of_sumSq_ne_top
  rw [sumSq_eq_sumSq_adjoint (T†) (canonicalBasis 𝕜 E) (canonicalBasis 𝕜 E),
    ContinuousLinearMap.adjoint_adjoint]
  exact hT.sumSq_ne_top

/-- The Hilbert–Schmidt class is closed under left composition by bounded operators. -/
theorem IsHilbertSchmidt.comp_left {T : E →L[𝕜] E} (hT : IsHilbertSchmidt T)
    (S : E →L[𝕜] E) : IsHilbertSchmidt (S ∘L T) := by
  apply isHilbertSchmidt_of_sumSq_ne_top
  exact ne_of_lt ((sumSq_comp_le S T (canonicalBasis 𝕜 E)).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 enorm_ne_top))
      (lt_top_iff_ne_top.2 hT.sumSq_ne_top)))

/-- The Hilbert–Schmidt class is closed under right composition by bounded operators. -/
theorem IsHilbertSchmidt.comp_right {S : E →L[𝕜] E} (hS : IsHilbertSchmidt S)
    (T : E →L[𝕜] E) : IsHilbertSchmidt (S ∘L T) := by
  apply isHilbertSchmidt_of_sumSq_ne_top
  exact ne_of_lt ((sumSq_comp_le_right S T (canonicalBasis 𝕜 E) (canonicalBasis 𝕜 E)).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 enorm_ne_top))
      (lt_top_iff_ne_top.2 hS.sumSq_ne_top)))

/-- The squared enorm of `T x` is bounded by the sum of squares times `‖x‖ₑ²`
(Parseval on `T x` plus pointwise Cauchy–Schwarz, via the adjoint). -/
theorem enorm_sq_apply_le_sumSq_mul (T : E →L[𝕜] E) {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    (x : E) : ‖T x‖ₑ ^ 2 ≤ sumSq T b * ‖x‖ₑ ^ 2 := by
  calc ‖T x‖ₑ ^ 2
      = ∑' i, ‖⟪b i, T x⟫_𝕜‖ₑ ^ 2 := (HilbertBasis.enorm_sq_eq_tsum b (T x)).symm
    _ = ∑' i, ‖⟪(T†) (b i), x⟫_𝕜‖ₑ ^ 2 := tsum_congr fun i => by
        rw [← ContinuousLinearMap.adjoint_inner_left]
    _ ≤ ∑' i, (‖(T†) (b i)‖ₑ * ‖x‖ₑ) ^ 2 := ENNReal.tsum_le_tsum fun i =>
        pow_le_pow_left' (enorm_inner_le_enorm _ _) 2
    _ = ∑' i, ‖(T†) (b i)‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := tsum_congr fun i => mul_pow _ _ _
    _ = sumSq (T†) b * ‖x‖ₑ ^ 2 := ENNReal.tsum_mul_right
    _ = sumSq T b * ‖x‖ₑ ^ 2 := by
        rw [sumSq_eq_sumSq_adjoint T b b]

/-- The operator enorm is bounded by the Hilbert–Schmidt sum of squares' square root. -/
theorem opENorm_le_sumSq_rpow_half (T : E →L[𝕜] E) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    ‖T‖ₑ ≤ (sumSq T b) ^ (1/2 : ℝ) := by
  apply ContinuousLinearMap.opENorm_le_bound
  intro x
  have h := ENNReal.rpow_le_rpow (enorm_sq_apply_le_sumSq_mul T b x) (by norm_num : (0:ℝ) ≤ 1/2)
  rw [rpow_half_sq', ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    rpow_half_sq'] at h
  exact h

/-- An operator is *trace class* if it factors as a composition of two Hilbert–Schmidt
operators. -/
def IsTraceClass (T : E →L[𝕜] E) : Prop :=
  ∃ A B : E →L[𝕜] E, IsHilbertSchmidt A ∧ IsHilbertSchmidt B ∧ T = A ∘L B

/-- Trace-class operators are Hilbert–Schmidt (Hilbert–Schmidt is a left ideal).  The
converse fails in infinite dimension. -/
theorem IsTraceClass.isHilbertSchmidt {T : E →L[𝕜] E} (hT : IsTraceClass T) :
    IsHilbertSchmidt T := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  exact hB.comp_left A

/-- The squared norms of the basis images of a Hilbert–Schmidt operator are summable. -/
theorem summable_norm_sq_apply_basis {T : E →L[𝕜] E} (hT : IsHilbertSchmidt T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) : Summable fun i => ‖T (b i)‖ ^ 2 := by
  have h := ENNReal.summable_toReal (hT.sumSq_ne_top_basis b)
  exact h.congr fun i => by rw [enorm_sq_eq_ofReal, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- The diagonal series of a trace-class operator is absolutely summable. -/
theorem summable_norm_inner_diagonal {T : E →L[𝕜] E} (hT : IsTraceClass T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) : Summable fun i => ‖⟪b i, T (b i)⟫_𝕜‖ := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  have hAm := summable_norm_sq_apply_basis hA.adjoint b
  have hBm := summable_norm_sq_apply_basis hB b
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_)
    ((hAm.add hBm).div_const 2)
  rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left]
  calc ‖⟪(A†) (b i), B (b i)⟫_𝕜‖ ≤ ‖(A†) (b i)‖ * ‖B (b i)‖ := norm_inner_le_norm _ _
    _ ≤ (‖(A†) (b i)‖ ^ 2 + ‖B (b i)‖ ^ 2) / 2 := by
        have h := two_mul_le_add_pow_two ‖(A†) (b i)‖ ‖B (b i)‖
        linarith

/-- The diagonal series of a trace-class operator is summable. -/
theorem summable_inner_diagonal {T : E →L[𝕜] E} (hT : IsTraceClass T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) : Summable fun i => ⟪b i, T (b i)⟫_𝕜 :=
  (summable_norm_inner_diagonal hT b).of_norm

/-- Squared inner products `⟪A† bᵢ, cⱼ⟫` over the product of two basis index sets are
summable (Parseval in `j`, then the Hilbert–Schmidt sum in `i`). -/
theorem summable_norm_sq_inner_adjoint_fst {A : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    {ι ι' : Type*} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 E) :
    Summable fun p : ι × ι' => ‖⟪(A†) (b p.1), c p.2⟫_𝕜‖ ^ 2 := by
  have hfin : (∑' p : ι × ι', ‖⟪(A†) (b p.1), c p.2⟫_𝕜‖ₑ ^ 2) ≠ ⊤ := by
    have step : ∀ i, (∑' j, ‖⟪(A†) (b i), c j⟫_𝕜‖ₑ ^ 2) = ‖(A†) (b i)‖ₑ ^ 2 := fun i => by
      rw [tsum_congr fun j => show ‖⟪(A†) (b i), c j⟫_𝕜‖ₑ ^ 2 = ‖⟪c j, (A†) (b i)⟫_𝕜‖ₑ ^ 2 by
        rw [← inner_conj_symm, RCLike.enorm_conj]]
      exact HilbertBasis.enorm_sq_eq_tsum c ((A†) (b i))
    have htot : (∑' p : ι × ι', ‖⟪(A†) (b p.1), c p.2⟫_𝕜‖ₑ ^ 2)
        = ∑' i, ‖(A†) (b i)‖ₑ ^ 2 := by
      rw [ENNReal.tsum_prod']
      exact tsum_congr step
    rw [htot]
    exact hA.adjoint.sumSq_ne_top_basis b
  exact (ENNReal.summable_toReal hfin).congr fun p => by
    rw [enorm_sq_eq_ofReal, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- Squared inner products `⟪cⱼ, B bᵢ⟫` over the product of two basis index sets are
summable (Parseval in `j`, then the Hilbert–Schmidt sum in `i`). -/
theorem summable_norm_sq_inner_snd {B : E →L[𝕜] E} (hB : IsHilbertSchmidt B) {ι ι' : Type*}
    (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 E) :
    Summable fun p : ι × ι' => ‖⟪c p.2, B (b p.1)⟫_𝕜‖ ^ 2 := by
  have hfin : (∑' p : ι × ι', ‖⟪c p.2, B (b p.1)⟫_𝕜‖ₑ ^ 2) ≠ ⊤ := by
    have step : ∀ i, (∑' j, ‖⟪c j, B (b i)⟫_𝕜‖ₑ ^ 2) = ‖B (b i)‖ₑ ^ 2 := fun i =>
      HilbertBasis.enorm_sq_eq_tsum c (B (b i))
    have htot : (∑' p : ι × ι', ‖⟪c p.2, B (b p.1)⟫_𝕜‖ₑ ^ 2) = ∑' i, ‖B (b i)‖ₑ ^ 2 := by
      rw [ENNReal.tsum_prod']
      exact tsum_congr step
    rw [htot]
    exact hB.sumSq_ne_top_basis b
  exact (ENNReal.summable_toReal hfin).congr fun p => by
    rw [enorm_sq_eq_ofReal, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- Absolute summability of the double Parseval expansion of `A ∘L B`, justifying the
index swap in `tsum_inner_comp_eq`. -/
theorem summable_uncurry_inner_mul_inner {A B : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) {ι ι' : Type*} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 E) :
    Summable (Function.uncurry fun i j => ⟪(A†) (b i), c j⟫_𝕜 * ⟪c j, B (b i)⟫_𝕜) := by
  apply Summable.of_norm
  have h1 := summable_norm_sq_inner_adjoint_fst hA b c
  have h2 := summable_norm_sq_inner_snd hB b c
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    ((h1.add h2).div_const 2)
  show ‖⟪(A†) (b p.1), c p.2⟫_𝕜 * ⟪c p.2, B (b p.1)⟫_𝕜‖ ≤ _
  rw [norm_mul]
  have h := two_mul_le_add_pow_two ‖⟪(A†) (b p.1), c p.2⟫_𝕜‖ ‖⟪c p.2, B (b p.1)⟫_𝕜‖
  linarith

/-- The trace-swap identity for a product of two Hilbert–Schmidt operators, computed on
two arbitrary Hilbert bases. -/
theorem tsum_inner_comp_eq {A B : E →L[𝕜] E} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B)
    {ι ι' : Type*} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 E) :
    ∑' i, ⟪b i, (A ∘L B) (b i)⟫_𝕜 = ∑' j, ⟪c j, (B ∘L A) (c j)⟫_𝕜 := by
  have hsum := summable_uncurry_inner_mul_inner hA hB b c
  calc ∑' i, ⟪b i, (A ∘L B) (b i)⟫_𝕜
      = ∑' i, ⟪(A†) (b i), B (b i)⟫_𝕜 := tsum_congr fun i => by
        rw [ContinuousLinearMap.comp_apply]
        exact (ContinuousLinearMap.adjoint_inner_left A (B (b i)) (b i)).symm
    _ = ∑' i, ∑' j, ⟪(A†) (b i), c j⟫_𝕜 * ⟪c j, B (b i)⟫_𝕜 :=
        tsum_congr fun i => (HilbertBasis.tsum_inner_mul_inner c ((A†) (b i)) (B (b i))).symm
    _ = ∑' j, ∑' i, ⟪(A†) (b i), c j⟫_𝕜 * ⟪c j, B (b i)⟫_𝕜 := (Summable.tsum_comm hsum).symm
    _ = ∑' j, ∑' i, ⟪(B†) (c j), b i⟫_𝕜 * ⟪b i, A (c j)⟫_𝕜 := tsum_congr fun j =>
        tsum_congr fun i => by
          rw [ContinuousLinearMap.adjoint_inner_left A (c j) (b i),
            ← ContinuousLinearMap.adjoint_inner_left B (b i) (c j), mul_comm]
    _ = ∑' j, ⟪(B†) (c j), A (c j)⟫_𝕜 :=
        tsum_congr fun j => HilbertBasis.tsum_inner_mul_inner b ((B†) (c j)) (A (c j))
    _ = ∑' j, ⟪c j, (B ∘L A) (c j)⟫_𝕜 := tsum_congr fun j =>
        ContinuousLinearMap.adjoint_inner_left B (A (c j)) (c j)

/-- The trace of an operator on a Hilbert space: the sum of the diagonal matrix elements
in the canonical Hilbert basis.  For trace-class operators this is basis-independent
(`trace_eq_tsum_inner`) and cyclic (`trace_comp_comm`). -/
noncomputable def trace (T : E →L[𝕜] E) : 𝕜 :=
  ∑' i, ⟪canonicalBasis 𝕜 E i, T (canonicalBasis 𝕜 E i)⟫_𝕜

/-- The trace of a trace-class operator can be computed in any Hilbert basis. -/
theorem trace_eq_tsum_inner {T : E →L[𝕜] E} (hT : IsTraceClass T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) : trace T = ∑' i, ⟪b i, T (b i)⟫_𝕜 := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  unfold trace
  rw [tsum_inner_comp_eq hA hB (canonicalBasis 𝕜 E) (canonicalBasis 𝕜 E)]
  exact (tsum_inner_comp_eq hA hB b (canonicalBasis 𝕜 E)).symm

/-- The trace is cyclic on Hilbert–Schmidt factors. -/
theorem trace_comp_comm {A B : E →L[𝕜] E} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    trace (A ∘L B) = trace (B ∘L A) :=
  tsum_inner_comp_eq hA hB (canonicalBasis 𝕜 E) (canonicalBasis 𝕜 E)

/-- The truncation of `T` onto the span of the basis vectors indexed by `s`. -/
noncomputable def basisTruncation (T : E →L[𝕜] E) {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    (s : Finset ι) : E →L[𝕜] E :=
  ∑ i ∈ s, rankOne 𝕜 (b i) (T (b i))

omit [CompleteSpace E] in
/-- The truncation evaluated at a basis vector. -/
theorem basisTruncation_apply_basis (T : E →L[𝕜] E) {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    (s : Finset ι) (j : ι) :
    basisTruncation T b s (b j) = if j ∈ s then T (b j) else 0 := by
  classical
  simp only [basisTruncation, sum_apply, rankOne_apply]
  rw [show (∑ i ∈ s, ⟪b i, b j⟫_𝕜 • T (b i)) = ∑ i ∈ s, if i = j then T (b i) else 0 from
    Finset.sum_congr rfl fun i _ => by
      by_cases hij : i = j
      · rcases hij with rfl
        have h1 : ⟪b i, b i⟫_𝕜 = 1 := by
          rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; norm_num
        rw [h1, one_smul, ite_eq_left rfl]
      · rw [b.orthonormal.2 hij, zero_smul, ite_eq_right hij]]
  exact Finset.sum_ite_eq' s j _

omit [CompleteSpace E] in
/-- The `sumSq` of `T` minus its truncation is the tail of the sum-of-squares series. -/
theorem sumSq_sub_basisTruncation (T : E →L[𝕜] E) {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    (s : Finset ι) :
    sumSq (T - basisTruncation T b s) b = ∑' j, if j ∈ s then 0 else ‖T (b j)‖ₑ ^ 2 := by
  classical
  unfold sumSq
  apply tsum_congr
  intro j
  rw [sub_apply, basisTruncation_apply_basis]
  by_cases hj : j ∈ s
  · rw [ite_eq_left hj, ite_eq_left hj, sub_self]
    simp
  · rw [ite_eq_right hj, ite_eq_right hj, sub_zero]

/-- The tail of the sum-of-squares series of a Hilbert–Schmidt operator vanishes along
the directed set of finite subsets. -/
theorem tendsto_sumSq_tail (T : E →L[𝕜] E) (hT : IsHilbertSchmidt T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) :
    Tendsto (fun s : Finset ι => ∑' j, if j ∈ s then 0 else ‖T (b j)‖ₑ ^ 2) atTop (𝓝 0) := by
  classical
  have hfin : (∑' j, ‖T (b j)‖ₑ ^ 2) ≠ ⊤ := hT.sumSq_ne_top_basis b
  have h := ENNReal.tendsto_tsum_compl_atTop_zero hfin
  apply h.congr
  intro s
  have hsub : Function.support (fun j => if j ∈ s then 0 else ‖T (b j)‖ₑ ^ 2)
      ⊆ {x : ι | x ∉ s} := by
    intro j hj hjs
    exact hj (ite_eq_left hjs)
  rw [← tsum_subtype_eq_of_support_subset hsub]
  apply tsum_congr
  rintro ⟨j, hj⟩
  rw [ite_eq_right hj]

/-- The square root of the truncated tail tends to zero. -/
theorem tendsto_sumSq_tail_rpow (T : E →L[𝕜] E) (hT : IsHilbertSchmidt T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) :
    Tendsto (fun s : Finset ι => (sumSq (T - basisTruncation T b s) b) ^ (1/2 : ℝ)) atTop
      (𝓝 0) := by
  classical
  have hanti : Antitone (fun s : Finset ι => (sumSq (T - basisTruncation T b s) b) ^ (1/2 : ℝ)) := by
    intro s s' hss'
    apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 1/2)
    rw [sumSq_sub_basisTruncation, sumSq_sub_basisTruncation]
    apply ENNReal.tsum_le_tsum
    intro j
    by_cases hj : j ∈ s'
    · rw [ite_eq_left hj]
      exact zero_le
    · rw [ite_eq_right hj, ite_eq_right fun h => hj (Finset.mem_of_subset hss' h)]
  refine (ENNReal.tendsto_atTop_zero_iff_le_of_antitone hanti).2 fun ε hε => ?_
  rcases eq_top_or_lt_top ε with rfl | hεtop
  · exact ⟨∅, le_top⟩
  · have htail := tendsto_sumSq_tail T hT b
    have hpos : (0 : ℝ≥0∞) < ε ^ 2 := pos_iff_ne_zero.2 (pow_ne_zero 2 (ne_of_gt hε))
    rcases (htail.eventually (Iio_mem_nhds hpos)).exists with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [sumSq_sub_basisTruncation]
    exact (ENNReal.rpow_le_rpow hs.le (by norm_num : (0:ℝ) ≤ 1/2)).trans_eq (rpow_half_sq' ε)

/-- The truncations converge to `T` in operator norm. -/
theorem tendsto_basisTruncation (T : E →L[𝕜] E) (hT : IsHilbertSchmidt T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) :
    Tendsto (fun s : Finset ι => basisTruncation T b s) atTop (𝓝 T) := by
  have htail := tendsto_sumSq_tail_rpow T hT b
  have hen : Tendsto (fun s : Finset ι => ‖T - basisTruncation T b s‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun s => zero_le) (fun s => opENorm_le_sumSq_rpow_half _ _)
  have hreal : Tendsto (fun s : Finset ι => ‖T - basisTruncation T b s‖) atTop (𝓝 0) := by
    have hc := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hen
    rw [ENNReal.toReal_zero] at hc
    exact hc.congr fun s => by simp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using hreal

omit [CompleteSpace E] in
/-- Rank-one operators `x ↦ ⟪v, x⟫ • a` are compact: they factor through the locally
compact scalar field. -/
theorem isCompactOperator_inner_smul (v a : E) :
    IsCompactOperator (fun x => ⟪v, x⟫_𝕜 • a) := by
  have h1 : IsCompactOperator ⇑((ContinuousLinearMap.id 𝕜 𝕜).smulRight a) :=
    isCompactOperator_of_locallyCompactSpace_rng _
  have h2 := h1.comp_clm (innerSL 𝕜 v)
  have heq : ⇑((ContinuousLinearMap.id 𝕜 𝕜).smulRight a) ∘ ⇑(innerSL 𝕜 v)
      = fun x => ⟪v, x⟫_𝕜 • a := funext fun _ => rfl
  rwa [heq] at h2

omit [CompleteSpace E] in
/-- Finite-rank truncations of `T` are compact operators. -/
theorem isCompactOperator_basisTruncation (T : E →L[𝕜] E) {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    (s : Finset ι) : IsCompactOperator ⇑(basisTruncation T b s) := by
  classical
  have heq : ∀ s : Finset ι,
      ⇑(basisTruncation T b s) = fun x => ∑ i ∈ s, ⟪b i, x⟫_𝕜 • T (b i) :=
    fun s => funext fun x => by simp only [basisTruncation, sum_apply, rankOne_apply]
  rw [heq]
  induction s using Finset.induction with
  | empty =>
      rw [show (fun x => ∑ i ∈ (∅ : Finset ι), ⟪b i, x⟫_𝕜 • T (b i)) = (0 : E → E) from
        funext fun x => by simp]
      exact isCompactOperator_zero
  | insert a s ha ih =>
      rw [show (fun x => ∑ i ∈ insert a s, ⟪b i, x⟫_𝕜 • T (b i))
          = (fun x => ⟪b a, x⟫_𝕜 • T (b a)) + fun x => ∑ i ∈ s, ⟪b i, x⟫_𝕜 • T (b i) from
        funext fun x => by rw [Finset.sum_insert ha]; rfl]
      exact IsCompactOperator.add (isCompactOperator_inner_smul _ _) ih

/-- Hilbert–Schmidt operators are compact: their finite-rank truncations converge to them
in operator norm, and compact operators are closed under operator-norm limits. -/
theorem IsHilbertSchmidt.isCompactOperator {T : E →L[𝕜] E} (hT : IsHilbertSchmidt T) :
    IsCompactOperator T :=
  isCompactOperator_of_tendsto (tendsto_basisTruncation T hT (canonicalBasis 𝕜 E))
    (Eventually.of_forall fun s => isCompactOperator_basisTruncation T (canonicalBasis 𝕜 E) s)

/-- Trace-class operators are compact. -/
theorem IsTraceClass.isCompactOperator {T : E →L[𝕜] E} (hT : IsTraceClass T) :
    IsCompactOperator T :=
  hT.isHilbertSchmidt.isCompactOperator

end HilbertSchmidt
