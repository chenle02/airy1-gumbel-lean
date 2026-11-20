/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TraceClass.FredholmTwo

/-! # The 1-regularized Fredholm determinant for trace-class operators

For a trace-class operator `A : E →L[𝕜] E` on a Hilbert space over `𝕜 = ℝ` or `ℂ`
(`RCLike 𝕜`), the Plemelj trace series

  `− ∑_{m=1}^∞ z^m · tr(A^m) / m`

is absolutely convergent on the open disk `‖z‖ * ‖A‖₂ < 1` (the `m = 1` term is finite
since `A` is trace class; for `m ≥ 2`, `‖tr(A^m)‖ ≤ ‖A‖₂^m` by `norm_trace_pow_le`,
`TraceClass/FredholmTwo.lean`), and the
**1-regularized Fredholm determinant** is

  `det₁(1 - zA) := exp (− ∑_{m ≥ 1} z^m tr(A^m) / m)`.

## What is proved here

* Trace linearity: `trace_add`, `trace_sub`, `trace_smul`, `trace_sum`
  (diagonal-tsum manipulations from `summable_inner_diagonal`, `TraceClass/TraceClass.lean`).
* Closure/ideal lemmas: `IsHilbertSchmidt.neg`, `IsHilbertSchmidt.sub`,
  `IsHilbertSchmidt.isTraceClass_comp`, `hsNorm_comp_le`, `hsNorm_neg`.
* `plemeljSummable`: summability of the Plemelj series on the disk `‖z‖ * ‖A‖₂ < 1`,
  with the `z = 1` specializations `summable_trace_pow_div`,
  `summable_norm_trace_pow_div`, and the tail bounds
  `tsum_norm_trace_pow_div_tail_le`, `norm_tsum_trace_pow_div_tail_le`.
* `fredholmDetOne`: the definition; `fredholmDetOne_zero`: the value `1` at `z = 0`.
* `fredholmDetOne_eq_exp_neg_trace_mul_detTwo`: on `hsNorm A < 1`, the classical
  relation `det₁(1 - A) = exp(−tr A) · det₂(1 - A)` between the two regularizations
  (with `fredholmDetTwo (-A) 1 = det₂(1 - A)` in the `det₂(1 + zK)` convention of
  `FredholmTwo.lean`).
* `norm_one_sub_fredholmDetOne_one_sub_trace_le`: the first-order expansion
  `1 − det₁(1−A) = tr A + remainder` with the explicit bound
  `‖1 − det₁(1−A) − tr A‖ ≤ (‖tr A‖ + ‖A‖₂²)²/2 · e^{‖tr A‖ + ‖A‖₂²} + ‖A‖₂²`
  for `‖A‖₂ ≤ 1/2`.
* `trace_pow_comp_comm` and `fredholmDetOne_cyclic`: `tr((AB)^m) = tr((BA)^m)` for
  Hilbert–Schmidt `A, B` and every `m ≥ 1`, hence `det₁(1 − AB) = det₁(1 − BA)`
  (Simon's cyclicity; termwise equality of the series, so no disk hypothesis).
* `norm_trace_pow_div_tail_sub_le`: the `m ≥ 2` Plemelj tail (equivalently, by `fredholmDetOne_eq_exp_neg_trace_mul_detTwo`, the
  `det₂` exponent series) is Hilbert–Schmidt Lipschitz on the disk `‖A‖₂, ‖B‖₂ ≤ R < 1`,
  via the telescoping factorization `A^n − B^n = ∑_{i<n} A^i (A−B) B^{n−1−i}`;
  `norm_exp_neg_trace_pow_div_tail_sub_le` is the same estimate after `exp`.

## Scope note

As in `FredholmTwo.lean`, everything takes place on the disk of convergence of the
Plemelj trace series; the entire extension of `det₁` for trace-class `A` (via the
eigenvalue product `∏ (1 − zλ_j)` or the Plemelj–Smithies exterior-power series) is
future work and nothing here claims it.

`det₁` itself is NOT Hilbert–Schmidt Lipschitz: the `m = 1` term `tr A` is not
controlled by `‖A‖₂` (e.g. `X_N = N^{-1/2} diag(1, …, 1)` on `𝕜^N` has
`‖X_N‖₂ = 1` but `tr X_N = √N`), so a continuity statement for `det₁` needs the extra
`|tr A − tr B|` term or factorized (trace-norm) convergence.  The `m ≥ 2` tail —
which is what `det₂` sees — has no such obstruction.
-/

open Filter
open scoped ENNReal NNReal InnerProduct InnerProductSpace

namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

section Helpers

/-- The trace is additive (given summability of the two diagonal series). -/
theorem trace_add_of_summable {S T : E →L[𝕜] E}
    (hS : Summable fun i => ⟪canonicalBasis 𝕜 E i, S (canonicalBasis 𝕜 E i)⟫_𝕜)
    (hT : Summable fun i => ⟪canonicalBasis 𝕜 E i, T (canonicalBasis 𝕜 E i)⟫_𝕜) :
    trace (S + T) = trace S + trace T := by
  unfold trace
  rw [← Summable.tsum_add hS hT]
  exact tsum_congr fun i => by rw [add_apply, inner_add_right]

/-- The trace is additive on trace-class operators. -/
theorem trace_add {S T : E →L[𝕜] E} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    trace (S + T) = trace S + trace T :=
  trace_add_of_summable (summable_inner_diagonal hS _) (summable_inner_diagonal hT _)

/-- The trace is subtractive on trace-class operators. -/
theorem trace_sub {S T : E →L[𝕜] E} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    trace (S - T) = trace S - trace T := by
  unfold trace
  rw [← Summable.tsum_sub (summable_inner_diagonal hS _) (summable_inner_diagonal hT _)]
  exact tsum_congr fun i => by rw [sub_apply, inner_sub_right]

/-- The trace is homogeneous. -/
theorem trace_smul (c : 𝕜) (T : E →L[𝕜] E) : trace (c • T) = c * trace T := by
  unfold trace
  rw [← tsum_mul_left]
  exact tsum_congr fun i => by rw [smul_apply, inner_smul_right]

/-- The trace of a finite sum of operators is the sum of the traces (given summability
of each diagonal series). -/
theorem trace_sum {ι : Type*} (s : Finset ι) {T : ι → E →L[𝕜] E}
    (hT : ∀ i ∈ s, Summable fun j => ⟪canonicalBasis 𝕜 E j, T i (canonicalBasis 𝕜 E j)⟫_𝕜) :
    trace (∑ i ∈ s, T i) = ∑ i ∈ s, trace (T i) := by
  unfold trace
  have step : ∀ j, ⟪canonicalBasis 𝕜 E j, (∑ i ∈ s, T i) (canonicalBasis 𝕜 E j)⟫_𝕜
      = ∑ i ∈ s, ⟪canonicalBasis 𝕜 E j, T i (canonicalBasis 𝕜 E j)⟫_𝕜 := fun j => by
    rw [sum_apply, inner_sum]
  rw [tsum_congr step, Summable.tsum_finsetSum fun i hi => hT i hi]

omit [CompleteSpace E] in
/-- Powers of scalar multiples of an operator: `(c • A) ^ m = c ^ m • A ^ m`. -/
theorem smul_pow_clm (c : 𝕜) (A : E →L[𝕜] E) (m : ℕ) : (c • A) ^ m = c ^ m • A ^ m :=
  smul_pow c A m

omit [CompleteSpace E] in
/-- Powers of the negative of an operator: `(-A) ^ m = (-1) ^ m • A ^ m`. -/
theorem neg_pow_clm (A : E →L[𝕜] E) (m : ℕ) : (-A) ^ m = (-1 : 𝕜) ^ m • A ^ m := by
  have h : -A = (-1 : 𝕜) • A := (neg_one_smul 𝕜 A).symm
  rw [h, smul_pow_clm]

/-- The Hilbert–Schmidt enorm is even: `‖−T‖₂,ₑ = ‖T‖₂,ₑ`. -/
theorem hsENorm_neg (T : E →L[𝕜] E) : hsENorm (-T) = hsENorm T := by
  unfold hsENorm
  congr 1
  unfold sumSq
  exact tsum_congr fun i => by rw [neg_apply, enorm_neg]

/-- The real Hilbert–Schmidt norm is even. -/
theorem hsNorm_neg (T : E →L[𝕜] E) : hsNorm (-T) = hsNorm T := by
  unfold hsNorm
  rw [hsENorm_neg]

/-- The Hilbert–Schmidt class is closed under negation. -/
theorem IsHilbertSchmidt.neg {T : E →L[𝕜] E} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (-T) := by
  show hsENorm (-T) ≠ ⊤
  rwa [hsENorm_neg]

/-- A composition of two Hilbert–Schmidt operators is trace class. -/
theorem IsHilbertSchmidt.isTraceClass_comp {A B : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : IsTraceClass (A ∘L B) :=
  ⟨A, B, hA, hB, rfl⟩

/-- The real Hilbert–Schmidt norm is submultiplicative on Hilbert–Schmidt operators. -/
theorem hsNorm_comp_le {S T : E →L[𝕜] E} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : hsNorm (S ∘L T) ≤ hsNorm S * hsNorm T := by
  unfold hsNorm
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hS hT) (hsENorm_comp_le S T)

/-- The Hilbert–Schmidt class is closed under subtraction. -/
theorem IsHilbertSchmidt.sub {S T : E →L[𝕜] E} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (S - T) := by
  apply isHilbertSchmidt_of_sumSq_ne_top
  have hle : sumSq (S - T) (canonicalBasis 𝕜 E) ≤
      4 * (sumSq S (canonicalBasis 𝕜 E) + sumSq T (canonicalBasis 𝕜 E)) := by
    calc sumSq (S - T) (canonicalBasis 𝕜 E)
        = ∑' i, ‖(S - T) (canonicalBasis 𝕜 E i)‖ₑ ^ 2 := rfl
      _ ≤ ∑' i, 4 * (‖S (canonicalBasis 𝕜 E i)‖ₑ ^ 2 + ‖T (canonicalBasis 𝕜 E i)‖ₑ ^ 2) := by
          apply ENNReal.tsum_le_tsum
          intro i
          rw [sub_apply]
          have h1 : ‖S (canonicalBasis 𝕜 E i) - T (canonicalBasis 𝕜 E i)‖ₑ
              ≤ ‖S (canonicalBasis 𝕜 E i)‖ₑ + ‖T (canonicalBasis 𝕜 E i)‖ₑ := enorm_sub_le
          refine (pow_le_pow_left' h1 2).trans ?_
          have hsup : (‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ) ^ 2
              ≤ ‖S (canonicalBasis 𝕜 E i)‖ₑ ^ 2 + ‖T (canonicalBasis 𝕜 E i)‖ₑ ^ 2 := by
            rcases le_total ‖S (canonicalBasis 𝕜 E i)‖ₑ ‖T (canonicalBasis 𝕜 E i)‖ₑ with h | h
            · rw [sup_eq_right.2 h]
              exact self_le_add_left (‖T (canonicalBasis 𝕜 E i)‖ₑ ^ 2)
                (‖S (canonicalBasis 𝕜 E i)‖ₑ ^ 2)
            · rw [sup_eq_left.2 h]
              exact self_le_add_right (‖S (canonicalBasis 𝕜 E i)‖ₑ ^ 2)
                (‖T (canonicalBasis 𝕜 E i)‖ₑ ^ 2)
          calc (‖S (canonicalBasis 𝕜 E i)‖ₑ + ‖T (canonicalBasis 𝕜 E i)‖ₑ) ^ 2
              ≤ (2 * (‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ)) ^ 2 := by
                apply pow_le_pow_left'
                have hs1 : ‖S (canonicalBasis 𝕜 E i)‖ₑ ≤
                    ‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ := le_sup_left
                have hs2 : ‖T (canonicalBasis 𝕜 E i)‖ₑ ≤
                    ‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ := le_sup_right
                calc ‖S (canonicalBasis 𝕜 E i)‖ₑ + ‖T (canonicalBasis 𝕜 E i)‖ₑ
                    ≤ (‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ) +
                        (‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ) :=
                      add_le_add hs1 hs2
                  _ = 2 * (‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ) :=
                      (two_mul _).symm
            _ = 2 ^ 2 * (‖S (canonicalBasis 𝕜 E i)‖ₑ ⊔ ‖T (canonicalBasis 𝕜 E i)‖ₑ) ^ 2 :=
                mul_pow _ _ _
            _ ≤ 2 ^ 2 * (‖S (canonicalBasis 𝕜 E i)‖ₑ ^ 2 + ‖T (canonicalBasis 𝕜 E i)‖ₑ ^ 2) :=
                mul_le_mul' le_rfl hsup
            _ = 4 * (‖S (canonicalBasis 𝕜 E i)‖ₑ ^ 2 + ‖T (canonicalBasis 𝕜 E i)‖ₑ ^ 2) := by
                rw [show (2 : ℝ≥0∞) ^ 2 = 4 from by norm_num]
      _ = 4 * (sumSq S (canonicalBasis 𝕜 E) + sumSq T (canonicalBasis 𝕜 E)) := by
          unfold sumSq
          rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
  exact ne_of_lt (lt_of_le_of_lt hle
    (ENNReal.mul_lt_top (Ne.lt_top ENNReal.ofNat_ne_top)
      (ENNReal.add_lt_top.2 ⟨hS.sumSq_ne_top.lt_top, hT.sumSq_ne_top.lt_top⟩)))

/-- The trace is cyclic on powers of a product of two Hilbert–Schmidt operators:
`tr ((A ∘L B) ^ n) = tr ((B ∘L A) ^ n)` for `1 ≤ n`.  For `n = 1` this is
`trace_comp_comm`; in general one rewrites `(A∘LB)^n = A ∘L ((B∘LA)^{n−1} ∘L B)` and
cycles once. -/
theorem trace_pow_comp_comm {A B : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) {n : ℕ} (hn : 1 ≤ n) :
    trace ((A ∘L B) ^ n) = trace ((B ∘L A) ^ n) := by
  rcases hn.eq_or_lt with hn1 | hn2
  · rw [← hn1, pow_one, pow_one]
    exact trace_comp_comm hA hB
  · have hAB : IsHilbertSchmidt (A ∘L B) := hB.comp_left A
    have aux : ∀ k : ℕ, B ∘L (A ∘L B) ^ k = ((B ∘L A) ^ k) ∘L B := by
      intro k
      induction k with
      | zero =>
          rw [pow_zero, pow_zero]
          exact (mul_one B).trans (one_mul B).symm
      | succ k ih =>
          rw [pow_succ_eq_comp _ k, ← ContinuousLinearMap.comp_assoc, ih,
            ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc B A B,
            ← ContinuousLinearMap.comp_assoc, ← pow_succ_eq_comp _ k]
    have hYn : IsHilbertSchmidt (B ∘L (A ∘L B) ^ (n - 1)) :=
      (hAB.pow (by omega : 1 ≤ n - 1)).comp_left B
    calc trace ((A ∘L B) ^ n)
        = trace (A ∘L (B ∘L (A ∘L B) ^ (n - 1))) := by
          rw [pow_eq_comp_one_sub _ hn, ContinuousLinearMap.comp_assoc]
      _ = trace ((B ∘L (A ∘L B) ^ (n - 1)) ∘L A) := trace_comp_comm hA hYn
      _ = trace ((((B ∘L A) ^ (n - 1)) ∘L B) ∘L A) := by rw [aux (n - 1)]
      _ = trace (((B ∘L A) ^ (n - 1)) ∘L (B ∘L A)) := by
          rw [ContinuousLinearMap.comp_assoc]
      _ = trace ((B ∘L A) ^ n) := by
          rw [← pow_succ_eq_comp _ (n - 1), Nat.sub_add_cancel hn]

end Helpers

section Plemelj

/-- **Plemelj summability.** The Plemelj trace series `∑_{m ≥ 1} z^m tr(A^m)/m` of a trace-class operator
is summable on the open disk `‖z‖ * ‖A‖₂ < 1`.  The `m = 1` term is a single finite
value; the `m ≥ 2` tail is dominated termwise by the geometric series of ratio
`‖z‖ * ‖A‖₂` via `norm_trace_pow_le`. -/
theorem plemeljSummable {A : E →L[𝕜] E} (hA : IsTraceClass A) {z : 𝕜}
    (hz : ‖z‖ * hsNorm A < 1) :
    Summable fun m : ℕ => z ^ (m + 1) * trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) := by
  have hA2 : IsHilbertSchmidt A := hA.isHilbertSchmidt
  have hr0 : 0 ≤ ‖z‖ * hsNorm A := mul_nonneg (norm_nonneg z) (hsNorm_nonneg A)
  have hgeo : Summable fun m : ℕ => (‖z‖ * hsNorm A) ^ m :=
    summable_geometric_of_lt_one hr0 hz
  have htail : Summable fun m : ℕ =>
      z ^ (m + 1 + 1) * trace (A ^ (m + 1 + 1)) / ((m + 1 + 1 : ℕ) : 𝕜) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
      (hgeo.mul_left ((‖z‖ * hsNorm A) ^ 2))
    rw [norm_div, norm_mul, norm_pow, RCLike.norm_natCast]
    have hm1 : (1 : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ m + 1 + 1 by omega)
    calc ‖z‖ ^ (m + 1 + 1) * ‖trace (A ^ (m + 1 + 1))‖ / ((m + 1 + 1 : ℕ) : ℝ)
        ≤ ‖z‖ ^ (m + 1 + 1) * hsNorm A ^ (m + 1 + 1) / ((m + 1 + 1 : ℕ) : ℝ) :=
          (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (show 0 < m + 1 + 1 by omega))).2
            (mul_le_mul_of_nonneg_left (norm_trace_pow_le hA2 (show 2 ≤ m + 1 + 1 by omega))
              (pow_nonneg (norm_nonneg z) _))
      _ ≤ ‖z‖ ^ (m + 1 + 1) * hsNorm A ^ (m + 1 + 1) :=
          div_le_self (mul_nonneg (pow_nonneg (norm_nonneg z) _)
            (pow_nonneg (hsNorm_nonneg _) _)) hm1
      _ = (‖z‖ * hsNorm A) ^ 2 * (‖z‖ * hsNorm A) ^ m := by
          rw [← mul_pow, show m + 1 + 1 = 2 + m from by omega, pow_add]
  exact (summable_nat_add_iff 1).mp htail

/-- The `z = 1` Plemelj series of a trace-class operator is summable on `‖A‖₂ < 1`. -/
theorem summable_trace_pow_div {A : E →L[𝕜] E} (hA : IsTraceClass A)
    (hz : hsNorm A < 1) : Summable fun m : ℕ => trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) := by
  have h := plemeljSummable hA (z := 1) (by rwa [norm_one, one_mul])
  exact h.congr fun m => by rw [one_pow, one_mul]

/-- The `z = 1` Plemelj series converges absolutely on `‖A‖₂ < 1`. -/
theorem summable_norm_trace_pow_div {A : E →L[𝕜] E} (hA : IsTraceClass A)
    (hz : hsNorm A < 1) :
    Summable fun m : ℕ => ‖trace (A ^ (m + 1))‖ / ((m + 1 : ℕ) : ℝ) := by
  have hA2 : IsHilbertSchmidt A := hA.isHilbertSchmidt
  have hgeo : Summable fun m : ℕ => hsNorm A ^ m :=
    summable_geometric_of_lt_one (hsNorm_nonneg A) hz
  have htail : Summable fun m : ℕ => ‖trace (A ^ (m + 1 + 1))‖ / ((m + 1 + 1 : ℕ) : ℝ) := by
    refine Summable.of_nonneg_of_le
      (fun m => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (fun m => ?_)
      (hgeo.mul_left (hsNorm A ^ 2))
    have hm1 : (1 : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ m + 1 + 1 by omega)
    calc ‖trace (A ^ (m + 1 + 1))‖ / ((m + 1 + 1 : ℕ) : ℝ)
        ≤ hsNorm A ^ (m + 1 + 1) / ((m + 1 + 1 : ℕ) : ℝ) :=
          (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (show 0 < m + 1 + 1 by omega))).2
            (norm_trace_pow_le hA2 (show 2 ≤ m + 1 + 1 by omega))
      _ ≤ hsNorm A ^ (m + 1 + 1) := div_le_self (pow_nonneg (hsNorm_nonneg _) _) hm1
      _ = hsNorm A ^ 2 * hsNorm A ^ m := by
          rw [show m + 1 + 1 = 2 + m from by omega, pow_add]
  exact (summable_nat_add_iff 1).mp htail

/-- The tail of the absolute `z = 1` Plemelj series is summable. -/
theorem summable_norm_trace_pow_div_tail {A : E →L[𝕜] E} (hA : IsTraceClass A)
    (hz : hsNorm A < 1) :
    Summable fun m : ℕ => ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) := by
  have hA2 : IsHilbertSchmidt A := hA.isHilbertSchmidt
  refine Summable.of_nonneg_of_le
    (fun m => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (fun m => ?_)
    ((summable_geometric_of_lt_one (hsNorm_nonneg A) hz).mul_left (hsNorm A ^ 2))
  calc ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
      ≤ hsNorm A ^ (m + 2) / ((m + 2 : ℕ) : ℝ) :=
        (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (show 0 < m + 2 by omega))).2
          (norm_trace_pow_le hA2 (show 2 ≤ m + 2 by omega))
    _ ≤ hsNorm A ^ (m + 2) :=
        div_le_self (pow_nonneg (hsNorm_nonneg _) _)
          (by exact_mod_cast (show 1 ≤ m + 2 by omega))
    _ = hsNorm A ^ 2 * hsNorm A ^ m := by
        rw [show m + 2 = 2 + m from by omega, pow_add]

/-- The tail of the `z = 1` Plemelj series (indices `m ≥ 2`) is summable. -/
theorem summable_trace_pow_div_tail {A : E →L[𝕜] E} (hA : IsTraceClass A)
    (hz : hsNorm A < 1) : Summable fun m : ℕ => trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) := by
  apply Summable.of_norm
  exact (summable_norm_trace_pow_div_tail hA hz).congr fun m => by
    rw [norm_div, RCLike.norm_natCast]

/-- The tail of the absolute `z = 1` Plemelj series:
`∑'_{m ≥ 2} ‖tr(A^m)‖/m ≤ ‖A‖₂² / (2 (1 − ‖A‖₂))`. -/
theorem tsum_norm_trace_pow_div_tail_le {A : E →L[𝕜] E} (hA : IsTraceClass A)
    (hz : hsNorm A < 1) :
    ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) ≤
      hsNorm A ^ 2 / (2 * (1 - hsNorm A)) := by
  have hA2 : IsHilbertSchmidt A := hA.isHilbertSchmidt
  have bound : ∀ m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) ≤
      (hsNorm A ^ 2 / 2) * hsNorm A ^ m := by
    intro m
    calc ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
        ≤ hsNorm A ^ (m + 2) / ((m + 2 : ℕ) : ℝ) :=
          (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (show 0 < m + 2 by omega))).2
            (norm_trace_pow_le hA2 (show 2 ≤ m + 2 by omega))
      _ ≤ hsNorm A ^ (m + 2) / 2 :=
          div_le_div_of_nonneg_left (pow_nonneg (hsNorm_nonneg _) _) (by norm_num)
            (by exact_mod_cast (show 2 ≤ m + 2 by omega))
      _ = (hsNorm A ^ 2 / 2) * hsNorm A ^ m := by
          rw [show m + 2 = 2 + m from by omega, pow_add, div_mul_eq_mul_div]
  have h1 : Summable fun m : ℕ => (hsNorm A ^ 2 / 2) * hsNorm A ^ m :=
    (summable_geometric_of_lt_one (hsNorm_nonneg A) hz).mul_left _
  have h2 : Summable fun m : ℕ => ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) :=
    Summable.of_nonneg_of_le (fun m => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
      bound h1
  calc ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
      ≤ ∑' m : ℕ, (hsNorm A ^ 2 / 2) * hsNorm A ^ m := h2.tsum_le_tsum bound h1
    _ = (hsNorm A ^ 2 / 2) * ∑' m : ℕ, hsNorm A ^ m := by rw [← tsum_mul_left]
    _ = (hsNorm A ^ 2 / 2) * (1 - hsNorm A)⁻¹ := by
        rw [tsum_geometric_of_lt_one (hsNorm_nonneg A) hz]
    _ = hsNorm A ^ 2 / (2 * (1 - hsNorm A)) :=
        (div_eq_mul_inv _ _).symm.trans (div_div _ _ _)

/-- The tail bound simplifies to `‖A‖₂²` when `‖A‖₂ ≤ 1/2`. -/
theorem tsum_norm_trace_pow_div_tail_le_of_le_half {A : E →L[𝕜] E} (hA : IsTraceClass A)
    (hz : hsNorm A < 1) (h2 : hsNorm A ≤ 1 / 2) :
    ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) ≤ hsNorm A ^ 2 := by
  refine (tsum_norm_trace_pow_div_tail_le hA hz).trans ?_
  have h1 : (1 : ℝ) ≤ 2 * (1 - hsNorm A) := by linarith [hsNorm_nonneg A]
  exact div_le_self (pow_nonneg (hsNorm_nonneg _) _) h1

/-- The norm of the tail of the `z = 1` Plemelj series:
`‖∑'_{m ≥ 2} tr(A^m)/m‖ ≤ ‖A‖₂² / (2 (1 − ‖A‖₂))`. -/
theorem norm_tsum_trace_pow_div_tail_le {A : E →L[𝕜] E} (hA : IsTraceClass A)
    (hz : hsNorm A < 1) :
    ‖∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ ≤
      hsNorm A ^ 2 / (2 * (1 - hsNorm A)) := by
  have hsumnorm : Summable fun m : ℕ => ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ :=
    (summable_norm_trace_pow_div_tail hA hz).congr fun m => by
      rw [norm_div, RCLike.norm_natCast]
  calc ‖∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖
      ≤ ∑' m : ℕ, ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ := norm_tsum_le_tsum_norm hsumnorm
    _ = ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) := tsum_congr fun m => by
        rw [norm_div, RCLike.norm_natCast]
    _ ≤ hsNorm A ^ 2 / (2 * (1 - hsNorm A)) := tsum_norm_trace_pow_div_tail_le hA hz

/-- The norm of the tail of the `z = 1` Plemelj series is at most `‖A‖₂²` when
`‖A‖₂ ≤ 1/2`. -/
theorem norm_tsum_trace_pow_div_tail_le_of_le_half {A : E →L[𝕜] E} (hA : IsTraceClass A)
    (hz : hsNorm A < 1) (h2 : hsNorm A ≤ 1 / 2) :
    ‖∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ ≤ hsNorm A ^ 2 := by
  refine (norm_tsum_trace_pow_div_tail_le hA hz).trans ?_
  have h1 : (1 : ℝ) ≤ 2 * (1 - hsNorm A) := by linarith [hsNorm_nonneg A]
  exact div_le_self (pow_nonneg (hsNorm_nonneg _) _) h1

/-- Peeling the `m = 1` term off the `z = 1` Plemelj series:
`∑'_{m ≥ 1} tr(A^m)/m = tr A + ∑'_{m ≥ 2} tr(A^m)/m`. -/
theorem tsum_trace_pow_div_eq_trace_add_tail {A : E →L[𝕜] E} (hA : IsTraceClass A)
    (hz : hsNorm A < 1) :
    ∑' m : ℕ, trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) =
      trace A + ∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) := by
  have hsum := summable_trace_pow_div hA hz
  rw [hsum.tsum_eq_zero_add]
  have hg0 : trace (A ^ (0 + 1)) / ((0 + 1 : ℕ) : 𝕜) = trace A := by
    rw [show 0 + 1 = 1 from rfl, pow_one, Nat.cast_one, div_one]
  have htail : (∑' m : ℕ, trace (A ^ (m + 1 + 1)) / ((m + 1 + 1 : ℕ) : 𝕜)) =
      ∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) :=
    tsum_congr fun m => by rw [show m + 1 + 1 = m + 2 from rfl]
  rw [hg0, htail]

end Plemelj

section ExpBounds

/-- The exponential series in `𝕜`: `NormedSpace.exp w = ∑' n, w ^ n / n !`. -/
theorem hasSum_pow_div_factorial (w : 𝕜) :
    HasSum (fun n : ℕ => w ^ n / (n.factorial : 𝕜)) (NormedSpace.exp w) := by
  simpa only [NormedSpace.expSeries_apply_eq_div] using
    NormedSpace.expSeries_hasSum_exp (𝕂 := 𝕜) w

/-- The exponential series is summable. -/
theorem summable_pow_div_factorial (w : 𝕜) : Summable fun n : ℕ => w ^ n / (n.factorial : 𝕜) :=
  (hasSum_pow_div_factorial w).summable

/-- The exponential series sums to `NormedSpace.exp w`. -/
theorem tsum_pow_div_factorial (w : 𝕜) :
    ∑' n : ℕ, w ^ n / (n.factorial : 𝕜) = NormedSpace.exp w :=
  (hasSum_pow_div_factorial w).tsum_eq

/-- The real exponential series of a norm is summable. -/
theorem summable_norm_pow_div_factorial (w : 𝕜) :
    Summable fun n : ℕ => ‖w‖ ^ n / (n.factorial : ℝ) := by
  have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) (𝔸 := ℝ) ‖w‖
  refine h.congr fun n => ?_
  rw [smul_eq_mul, mul_comm, div_eq_mul_inv]

/-- The real exponential series of a norm sums to `Real.exp ‖w‖`. -/
theorem tsum_norm_pow_div_factorial (w : 𝕜) :
    ∑' n : ℕ, ‖w‖ ^ n / (n.factorial : ℝ) = Real.exp ‖w‖ := by
  have h : HasSum (fun n : ℕ => ‖w‖ ^ n / (n.factorial : ℝ)) (NormedSpace.exp ‖w‖) := by
    simpa only [NormedSpace.expSeries_apply_eq_div] using
      NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (𝔸 := ℝ) ‖w‖
  rw [Real.exp_eq_exp_ℝ]
  exact h.tsum_eq

/-- `‖exp w‖ ≤ e^{‖w‖}` for `w : 𝕜`. -/
theorem norm_exp_le (w : 𝕜) : ‖NormedSpace.exp w‖ ≤ Real.exp ‖w‖ := by
  have hnorm : ∀ n : ℕ, ‖w ^ n / (n.factorial : 𝕜)‖ = ‖w‖ ^ n / (n.factorial : ℝ) := fun n => by
    rw [norm_div, norm_pow, RCLike.norm_natCast]
  have hsum : Summable fun n : ℕ => ‖w ^ n / (n.factorial : 𝕜)‖ :=
    (summable_norm_pow_div_factorial w).congr fun n => (hnorm n).symm
  calc ‖NormedSpace.exp w‖ = ‖∑' n : ℕ, w ^ n / (n.factorial : 𝕜)‖ := by rw [tsum_pow_div_factorial]
    _ ≤ ∑' n : ℕ, ‖w ^ n / (n.factorial : 𝕜)‖ := norm_tsum_le_tsum_norm hsum
    _ = ∑' n : ℕ, ‖w‖ ^ n / (n.factorial : ℝ) := tsum_congr hnorm
    _ = Real.exp ‖w‖ := tsum_norm_pow_div_factorial w

/-- First-order remainder for `exp` in `𝕜`: `‖exp w − 1‖ ≤ ‖w‖ · e^{‖w‖}`. -/
theorem norm_exp_sub_one_le (w : 𝕜) :
    ‖NormedSpace.exp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  have hsplit : NormedSpace.exp w - 1 = ∑' n : ℕ, w ^ (n + 1) / ((n + 1).factorial : 𝕜) := by
    rw [← tsum_pow_div_factorial w, (summable_pow_div_factorial w).tsum_eq_zero_add]
    have h0 : w ^ 0 / (Nat.factorial 0 : 𝕜) = 1 := by
      rw [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [h0, add_sub_cancel_left]
  have hnorm : ∀ n : ℕ, ‖w ^ (n + 1) / ((n + 1).factorial : 𝕜)‖ = ‖w‖ ^ (n + 1) / ((n + 1).factorial : ℝ) :=
    fun n => by rw [norm_div, norm_pow, RCLike.norm_natCast]
  have bound : ∀ n : ℕ, ‖w‖ ^ (n + 1) / ((n + 1).factorial : ℝ) ≤ ‖w‖ ^ (n + 1) / (n.factorial : ℝ) := by
    intro n
    exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
      (Nat.cast_pos.mpr (Nat.factorial_pos _))
      (by exact_mod_cast Nat.factorial_le (Nat.le_succ n))
  have hsum1 : Summable fun n : ℕ => ‖w‖ ^ (n + 1) / (n.factorial : ℝ) :=
    ((summable_norm_pow_div_factorial w).mul_left ‖w‖).congr fun n => by
      rw [pow_succ', mul_div_assoc]

  have hsum2 : Summable fun n : ℕ => ‖w‖ ^ (n + 1) / ((n + 1).factorial : ℝ) :=
    Summable.of_nonneg_of_le (fun n => div_nonneg (pow_nonneg (norm_nonneg _) _)
      (Nat.cast_nonneg _)) bound hsum1
  have hsum0 : Summable fun n : ℕ => ‖w ^ (n + 1) / ((n + 1).factorial : 𝕜)‖ :=
    hsum2.congr fun n => (hnorm n).symm
  calc ‖NormedSpace.exp w - 1‖
      = ‖∑' n : ℕ, w ^ (n + 1) / ((n + 1).factorial : 𝕜)‖ := by rw [hsplit]
    _ ≤ ∑' n : ℕ, ‖w ^ (n + 1) / ((n + 1).factorial : 𝕜)‖ := norm_tsum_le_tsum_norm hsum0
    _ = ∑' n : ℕ, ‖w‖ ^ (n + 1) / ((n + 1).factorial : ℝ) := tsum_congr hnorm
    _ ≤ ∑' n : ℕ, ‖w‖ ^ (n + 1) / (n.factorial : ℝ) := hsum2.tsum_le_tsum bound hsum1
    _ = ‖w‖ * ∑' n : ℕ, ‖w‖ ^ n / (n.factorial : ℝ) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun n => by rw [pow_succ', mul_div_assoc]
    _ = ‖w‖ * Real.exp ‖w‖ := by rw [tsum_norm_pow_div_factorial]

/-- Second-order remainder for `exp` in `𝕜`: `‖exp w − 1 − w‖ ≤ ‖w‖²/2 · e^{‖w‖}`. -/
theorem norm_exp_sub_one_sub_le (w : 𝕜) :
    ‖NormedSpace.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 / 2 * Real.exp ‖w‖ := by
  have hsplit : NormedSpace.exp w - 1 - w = ∑' n : ℕ, w ^ (n + 2) / ((n + 2).factorial : 𝕜) := by
    have h := (summable_pow_div_factorial w).sum_add_tsum_nat_add 2
    have hstart : ∑ i ∈ Finset.range 2, w ^ i / (i.factorial : 𝕜) = 1 + w := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp [pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one]
    rw [← tsum_pow_div_factorial w, ← h, hstart]
    ring
  have hnorm : ∀ n : ℕ, ‖w ^ (n + 2) / ((n + 2).factorial : 𝕜)‖ = ‖w‖ ^ (n + 2) / ((n + 2).factorial : ℝ) :=
    fun n => by rw [norm_div, norm_pow, RCLike.norm_natCast]
  have hfact : ∀ n : ℕ, ‖w‖ ^ 2 / 2 * (‖w‖ ^ n / (n.factorial : ℝ)) =
      ‖w‖ ^ (n + 2) / (2 * n.factorial : ℝ) := by
    intro n
    rw [div_mul_eq_mul_div, ← mul_div_assoc, div_div, ← pow_add,
      show 2 + n = n + 2 from by omega, mul_comm ((n.factorial : ℝ)) 2]
  have bound : ∀ n : ℕ, ‖w‖ ^ (n + 2) / ((n + 2).factorial : ℝ) ≤ ‖w‖ ^ (n + 2) / (2 * n.factorial : ℝ) := by
    intro n
    apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
      (mul_pos (by norm_num : (0 : ℝ) < 2) (Nat.cast_pos.mpr (Nat.factorial_pos n)))
    have h : 2 * n.factorial ≤ (n + 2).factorial := by
      have e : (n + 2).factorial = (n + 2) * (n + 1) * n.factorial := by
        rw [Nat.factorial_succ, Nat.factorial_succ, mul_assoc]
      rw [e]
      have h2 : (2 : ℕ) ≤ (n + 2) * (n + 1) :=
        calc (2 : ℕ) = 2 * 1 := rfl
          _ ≤ (n + 2) * (n + 1) :=
            Nat.mul_le_mul (by omega : 2 ≤ n + 2) (by omega : 1 ≤ n + 1)
      exact mul_le_mul h2 le_rfl (Nat.zero_le _) (Nat.zero_le _)
    exact_mod_cast h
  have hsum2 : Summable fun n : ℕ => ‖w‖ ^ (n + 2) / (2 * n.factorial : ℝ) :=
    ((summable_norm_pow_div_factorial w).mul_left (‖w‖ ^ 2 / 2)).congr hfact
  have hsum1 : Summable fun n : ℕ => ‖w‖ ^ (n + 2) / ((n + 2).factorial : ℝ) :=
    Summable.of_nonneg_of_le (fun n => div_nonneg (pow_nonneg (norm_nonneg _) _)
      (Nat.cast_nonneg _)) bound hsum2
  have hsum0 : Summable fun n : ℕ => ‖w ^ (n + 2) / ((n + 2).factorial : 𝕜)‖ :=
    hsum1.congr fun n => (hnorm n).symm
  calc ‖NormedSpace.exp w - 1 - w‖
      = ‖∑' n : ℕ, w ^ (n + 2) / ((n + 2).factorial : 𝕜)‖ := by rw [hsplit]
    _ ≤ ∑' n : ℕ, ‖w ^ (n + 2) / ((n + 2).factorial : 𝕜)‖ := norm_tsum_le_tsum_norm hsum0
    _ = ∑' n : ℕ, ‖w‖ ^ (n + 2) / ((n + 2).factorial : ℝ) := tsum_congr hnorm
    _ ≤ ∑' n : ℕ, ‖w‖ ^ (n + 2) / (2 * n.factorial : ℝ) := hsum1.tsum_le_tsum bound hsum2
    _ = ‖w‖ ^ 2 / 2 * ∑' n : ℕ, ‖w‖ ^ n / (n.factorial : ℝ) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun n => (hfact n).symm
    _ = ‖w‖ ^ 2 / 2 * Real.exp ‖w‖ := by rw [tsum_norm_pow_div_factorial]

end ExpBounds

section Determinant

/-- The 1-regularized Fredholm determinant of a trace-class operator:

  `det₁(1 - zA) := exp (− ∑_{m ≥ 1} z^m tr(A^m)/m)`,

defined for all `z` as the exponential of the Plemelj-series sum (the sum takes the
junk value `0` when the series is not summable; the meaningful values are on the open
disk `‖z‖ * ‖A‖₂ < 1`, see `plemeljSummable`).  The trace-class proof argument is
present for API uniformity; the value does not depend on it. -/
noncomputable def fredholmDetOne (A : E →L[𝕜] E) (_hA : IsTraceClass A) (z : 𝕜) : 𝕜 :=
  NormedSpace.exp (-∑' m : ℕ, z ^ (m + 1) * trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜))

/-- `det₁(1 - 0·A) = 1`. -/
@[simp]
theorem fredholmDetOne_zero (A : E →L[𝕜] E) (hA : IsTraceClass A) :
    fredholmDetOne A hA 0 = 1 := by
  have h0 : (fun m : ℕ => (0 : 𝕜) ^ (m + 1) * trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜))
      = fun _ => 0 := by
    ext m
    rw [zero_pow (show m + 1 ≠ 0 by omega), zero_mul, zero_div]
  unfold fredholmDetOne
  rw [h0, tsum_zero, neg_zero, NormedSpace.exp_zero]

/-- The `z = 1` specialization: `det₁(1 - A) = exp (− ∑'_{m ≥ 1} tr(A^m)/m)`. -/
theorem fredholmDetOne_one_eq_exp_neg_tsum (A : E →L[𝕜] E) (hA : IsTraceClass A) :
    fredholmDetOne A hA 1 =
      NormedSpace.exp (-∑' m : ℕ, trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜)) := by
  unfold fredholmDetOne
  congr 1
  congr 1
  exact tsum_congr fun m => by rw [one_pow, one_mul]

/-- **`det₁` versus `det₂`.** The classical relation between the two regularizations: on the disk
`‖A‖₂ < 1`,
`det₁(1 - A) = exp(−tr A) · det₂(1 - A)`.

Here `fredholmDetTwo (-A) 1` is `det₂(1 - A)` in the `det₂(1 + zK)` convention of
`FredholmTwo.lean`: the det₂ coefficient of `−A` at `m ≥ 2` is
`(−1)^{m+1} tr((−A)^m)/m = −tr(A^m)/m`, matching the det₁ tail, while the missing
`m = 1` term is exactly `exp (−tr A)`. -/
theorem fredholmDetOne_eq_exp_neg_trace_mul_detTwo {A : E →L[𝕜] E} (hA : IsTraceClass A)
    (hz : hsNorm A < 1) :
    fredholmDetOne A hA 1 = NormedSpace.exp (-(trace A)) * fredholmDetTwo (-A) 1 := by
  set f : ℕ → 𝕜 := fun m => -trace (A ^ m) / (m : 𝕜) with hf
  have h1 : Summable fun m : ℕ => trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) :=
    summable_trace_pow_div hA hz
  have hf1 : Summable fun m : ℕ => f (m + 1) := by
    refine h1.neg.congr fun m => ?_
    show -(trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜)) =
      -trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜)
    rw [neg_div]
  have hf0 : Summable f := (summable_nat_add_iff 1).mp hf1
  have hf2 : Summable fun m : ℕ => f (m + 2) := (summable_nat_add_iff 2).mpr hf0
  have hcoeff : ∀ m : ℕ, fredholmDetTwoCoeff (-A) m = if 2 ≤ m then f m else 0 := by
    intro m
    by_cases hm : 2 ≤ m
    · rw [fredholmDetTwoCoeff, ite_eq_left hm, ite_eq_left hm]
      show (-1 : 𝕜) ^ (m + 1) * trace ((-A) ^ m) / (m : 𝕜) = -trace (A ^ m) / (m : 𝕜)
      rw [neg_pow_clm, trace_smul]
      have hsign : (-1 : 𝕜) ^ (m + 1) * (-1 : 𝕜) ^ m = -1 := by
        rw [← pow_add, show m + 1 + m = 2 * m + 1 from by omega, pow_add, pow_one,
          pow_mul, show (-1 : 𝕜) ^ 2 = 1 from by ring, one_pow, one_mul]
      rw [← mul_assoc, hsign, neg_one_mul]
    · rw [fredholmDetTwoCoeff, ite_eq_right hm, ite_eq_right hm]
  have hge : Summable fun m : ℕ => if 2 ≤ m then f m else 0 := by
    apply (summable_nat_add_iff 2).mp
    exact hf2.congr fun m => (ite_eq_left (show 2 ≤ m + 2 by omega)).symm
  have hsplit2 : (∑' m : ℕ, if 2 ≤ m then f m else 0) = ∑' m : ℕ, f (m + 2) := by
    have h := hge.sum_add_tsum_nat_add 2
    have hstart : ∑ i ∈ Finset.range 2, (if 2 ≤ i then f i else 0) = 0 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one, ite_eq_right (show ¬ 2 ≤ 1 by omega),
        ite_eq_right (show ¬ 2 ≤ 0 by omega), add_zero]
    rw [← h, hstart, zero_add]
    exact tsum_congr fun m => ite_eq_left (show 2 ≤ m + 2 by omega)
  have key : (∑' m : ℕ, f (m + 1)) =
      -∑' m : ℕ, trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) := by
    rw [← tsum_neg]
    exact tsum_congr fun m => by
      show -trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) =
        -(trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜))
      rw [neg_div]
  have he1 : -∑' m : ℕ, trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) =
      -trace A + ∑' m : ℕ, f (m + 2) := by
    have hpeel : (∑' m : ℕ, f (m + 1)) = f 1 + ∑' m : ℕ, f (m + 2) := hf1.tsum_eq_zero_add
    have hf1' : f 1 = -trace A := by
      show -trace (A ^ 1) / ((1 : ℕ) : 𝕜) = -trace A
      rw [pow_one, Nat.cast_one, div_one]
    rw [← key, hpeel, hf1']
  have he2 : (∑' m : ℕ, fredholmDetTwoCoeff (-A) m * (1 : 𝕜) ^ m) =
      ∑' m : ℕ, f (m + 2) := by
    rw [tsum_congr fun m => by rw [hcoeff m, one_pow, mul_one], hsplit2]
  rw [fredholmDetOne_one_eq_exp_neg_tsum, he1, NormedSpace.exp_add,
    fredholmDetTwo_eq_exp_tsum, he2]

/-- **Simon's cyclicity** for the 1-regularized determinant: for Hilbert–Schmidt
`A, B`, `det₁(1 − zAB) = det₁(1 − zBA)` for every `z`.  The Plemelj series agree
termwise by `trace_pow_comp_comm`, so the (possibly non-summable) `tsum`s agree; no
disk hypothesis is needed. -/
theorem fredholmDetOne_cyclic {A B : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) (z : 𝕜) :
    fredholmDetOne (A ∘L B) (IsHilbertSchmidt.isTraceClass_comp hA hB) z =
      fredholmDetOne (B ∘L A) (IsHilbertSchmidt.isTraceClass_comp hB hA) z := by
  unfold fredholmDetOne
  have htsum : (∑' m : ℕ, z ^ (m + 1) * trace ((A ∘L B) ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜)) =
      ∑' m : ℕ, z ^ (m + 1) * trace ((B ∘L A) ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) :=
    tsum_congr fun m => by rw [trace_pow_comp_comm hA hB (by omega : 1 ≤ m + 1)]
  rw [htsum]

/-- The first-order expansion of `det₁` at `z = 1` (the remainder form used by the
paper's determinant estimates): for `‖A‖₂ ≤ 1/2`,

  `1 − det₁(1−A) = tr A + R(A)` with
  `‖R(A)‖ ≤ (‖tr A‖ + ‖A‖₂²)²/2 · e^{‖tr A‖ + ‖A‖₂²} + ‖A‖₂²`.

Indeed `1 − exp(−S) = S + O(‖S‖² e^{‖S‖})` for the Plemelj sum `S = tr A + T`, and the
tail satisfies `‖T‖ ≤ ‖A‖₂²` by `norm_tsum_trace_pow_div_tail_le_of_le_half`. -/
theorem norm_one_sub_fredholmDetOne_one_sub_trace_le {A : E →L[𝕜] E} (hA : IsTraceClass A)
    (hz : hsNorm A < 1) (h2 : hsNorm A ≤ 1 / 2) :
    ‖1 - fredholmDetOne A hA 1 - trace A‖ ≤
      (‖trace A‖ + hsNorm A ^ 2) ^ 2 / 2 * Real.exp (‖trace A‖ + hsNorm A ^ 2)
        + hsNorm A ^ 2 := by
  rw [fredholmDetOne_one_eq_exp_neg_tsum]
  have hsplit := tsum_trace_pow_div_eq_trace_add_tail hA hz
  set T : 𝕜 := ∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) with hTdef
  set S : 𝕜 := ∑' m : ℕ, trace (A ^ (m + 1)) / ((m + 1 : ℕ) : 𝕜) with hSdef
  have hSeq : S = trace A + T := hsplit
  have hnormT : ‖T‖ ≤ hsNorm A ^ 2 := norm_tsum_trace_pow_div_tail_le_of_le_half hA hz h2
  have hnormS : ‖S‖ ≤ ‖trace A‖ + hsNorm A ^ 2 := by
    calc ‖S‖ = ‖trace A + T‖ := by rw [hSeq]
      _ ≤ ‖trace A‖ + ‖T‖ := norm_add_le _ _
      _ ≤ ‖trace A‖ + hsNorm A ^ 2 := add_le_add le_rfl hnormT
  have hexp : 1 - NormedSpace.exp (-S) - trace A
      = T - (NormedSpace.exp (-S) - 1 - (-S)) := by
    rw [hSeq]; ring
  rw [hexp]
  calc ‖T - (NormedSpace.exp (-S) - 1 - (-S))‖
      ≤ ‖T‖ + ‖NormedSpace.exp (-S) - 1 - (-S)‖ := norm_sub_le _ _
    _ ≤ hsNorm A ^ 2 + (‖-S‖ ^ 2 / 2 * Real.exp ‖-S‖) :=
        add_le_add hnormT (norm_exp_sub_one_sub_le (-S))
    _ = hsNorm A ^ 2 + (‖S‖ ^ 2 / 2 * Real.exp ‖S‖) := by rw [norm_neg]
    _ ≤ hsNorm A ^ 2 + ((‖trace A‖ + hsNorm A ^ 2) ^ 2 / 2
        * Real.exp (‖trace A‖ + hsNorm A ^ 2)) := by
        apply add_le_add le_rfl
        have hnnS : 0 ≤ ‖S‖ := norm_nonneg _
        have hnnX : 0 ≤ ‖trace A‖ + hsNorm A ^ 2 :=
          add_nonneg (norm_nonneg _) (pow_nonneg (hsNorm_nonneg _) _)
        have hsq : ‖S‖ ^ 2 / 2 ≤ (‖trace A‖ + hsNorm A ^ 2) ^ 2 / 2 := by
          have hpow := pow_le_pow_left₀ hnnS hnormS 2
          linarith
        exact mul_le_mul hsq (Real.exp_le_exp.mpr hnormS) (Real.exp_nonneg _)
          (div_nonneg (pow_nonneg hnnX _) two_pos.le)
    _ = (‖trace A‖ + hsNorm A ^ 2) ^ 2 / 2 * Real.exp (‖trace A‖ + hsNorm A ^ 2)
        + hsNorm A ^ 2 := by ring

end Determinant

section LipschitzTail

omit [CompleteSpace E] in
/-- Left composition distributes over a finite sum of operators. -/
theorem comp_sum {ι : Type*} (s : Finset ι) (T : ι → E →L[𝕜] E) (A : E →L[𝕜] E) :
    A ∘L (∑ i ∈ s, T i) = ∑ i ∈ s, A ∘L T i := by
  ext x
  rw [ContinuousLinearMap.comp_apply, sum_apply, map_sum, sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
/-- The telescoping factorization of a difference of powers in the composition monoid:
`A ^ n - B ^ n = ∑_{i < n} (A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i))`. -/
theorem sub_pow_eq_sum_comp (A B : E →L[𝕜] E) (n : ℕ) :
    A ^ n - B ^ n = ∑ i ∈ Finset.range n, (A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i)) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, sub_self, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
      have key : A ^ (n + 1) - B ^ (n + 1) = A ∘L (A ^ n - B ^ n) + (A - B) ∘L B ^ n := by
        rw [pow_succ', pow_succ']
        show A * A ^ n - B * B ^ n = A * (A ^ n - B ^ n) + (A - B) * B ^ n
        noncomm_ring
      have hsplit : (∑ i ∈ Finset.range (n + 1),
            (A ^ i) ∘L ((A - B) ∘L B ^ (n + 1 - 1 - i)))
          = (∑ i ∈ Finset.range n, (A ^ (i + 1)) ∘L ((A - B) ∘L B ^ (n - 1 - i))) +
              (A - B) ∘L B ^ n := by
        rw [Finset.sum_range_succ']
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by
            rw [show n + 1 - 1 - (i + 1) = n - 1 - i from by omega]
      rw [key, ih, comp_sum, hsplit]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by
        rw [← ContinuousLinearMap.comp_assoc,
          show A ∘L A ^ i = A ^ (i + 1) from (pow_succ' A i).symm]

/-- The trace-of-power-difference bound: for Hilbert–Schmidt `A, B` with
`‖A‖₂, ‖B‖₂ ≤ R` and `n ≥ 2`,
`‖tr (A ^ n) − tr (B ^ n)‖ ≤ n · R ^ (n−1) · ‖A − B‖₂`.

Via the noncommutative telescoping `A^n − B^n = ∑_{i<n} A^i (A−B) B^{n−1−i}`
(`sub_pow_eq_sum_comp`), `norm_trace_comp_le` on each summand, and `hsNorm_pow_le`. -/
theorem norm_trace_sub_pow_le {A B : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) {R : ℝ} (hRA : hsNorm A ≤ R) (hRB : hsNorm B ≤ R) {n : ℕ}
    (hn : 2 ≤ n) :
    ‖trace (A ^ n) - trace (B ^ n)‖ ≤ (n : ℝ) * R ^ (n - 1) * hsNorm (A - B) := by
  have hAB : IsHilbertSchmidt (A - B) := hA.sub hB
  have hR0 : 0 ≤ R := (hsNorm_nonneg A).trans hRA
  have hTC : ∀ i ∈ Finset.range n, IsTraceClass ((A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rcases eq_zero_or_pos i with hi0 | hi0
    · rw [hi0, pow_zero, Nat.sub_zero]
      show IsTraceClass ((1 : E →L[𝕜] E) ∘L ((A - B) ∘L B ^ (n - 1)))
      rw [show (1 : E →L[𝕜] E) ∘L ((A - B) ∘L B ^ (n - 1)) = (A - B) ∘L B ^ (n - 1) from
        one_mul _]
      exact hAB.isTraceClass_comp (hB.pow (by omega : 1 ≤ n - 1))
    · exact ⟨A ^ i, (A - B) ∘L B ^ (n - 1 - i), hA.pow hi0, hAB.comp_right _, rfl⟩
  have hbound : ∀ i ∈ Finset.range n,
      ‖trace ((A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i)))‖ ≤ R ^ (n - 1) * hsNorm (A - B) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rcases eq_zero_or_pos i with hi0 | hi0
    · rw [hi0, pow_zero, Nat.sub_zero]
      show ‖trace ((1 : E →L[𝕜] E) ∘L ((A - B) ∘L B ^ (n - 1)))‖ ≤ _
      rw [show (1 : E →L[𝕜] E) ∘L ((A - B) ∘L B ^ (n - 1)) = (A - B) ∘L B ^ (n - 1) from
        one_mul _]
      calc ‖trace ((A - B) ∘L B ^ (n - 1))‖
          ≤ hsNorm (A - B) * hsNorm (B ^ (n - 1)) :=
            norm_trace_comp_le hAB (hB.pow (by omega : 1 ≤ n - 1))
        _ ≤ hsNorm (A - B) * hsNorm B ^ (n - 1) :=
            mul_le_mul_of_nonneg_left (hsNorm_pow_le hB (by omega : 1 ≤ n - 1))
              (hsNorm_nonneg _)
        _ ≤ hsNorm (A - B) * R ^ (n - 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hsNorm_nonneg _) hRB _)
              (hsNorm_nonneg _)
        _ = R ^ (n - 1) * hsNorm (A - B) := mul_comm _ _
    · rcases eq_or_lt_of_le (show i ≤ n - 1 by omega) with hi1 | hi1
      · rw [hi1]
        have hb0 : (A - B) ∘L B ^ (n - 1 - (n - 1)) = A - B := by
          rw [show n - 1 - (n - 1) = 0 from by omega, pow_zero]
          show (A - B) ∘L (1 : E →L[𝕜] E) = A - B
          exact mul_one _
        rw [hb0]
        calc ‖trace ((A ^ (n - 1)) ∘L (A - B))‖
            ≤ hsNorm (A ^ (n - 1)) * hsNorm (A - B) :=
              norm_trace_comp_le (hA.pow (by omega : 1 ≤ n - 1)) hAB
          _ ≤ hsNorm A ^ (n - 1) * hsNorm (A - B) :=
              mul_le_mul_of_nonneg_right (hsNorm_pow_le hA (by omega : 1 ≤ n - 1))
                (hsNorm_nonneg _)
          _ ≤ R ^ (n - 1) * hsNorm (A - B) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hsNorm_nonneg _) hRA _)
                (hsNorm_nonneg _)
      · have hj : 1 ≤ n - 1 - i := by omega
        calc ‖trace ((A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i)))‖
            ≤ hsNorm (A ^ i) * hsNorm ((A - B) ∘L B ^ (n - 1 - i)) :=
              norm_trace_comp_le (hA.pow hi0) (hAB.comp_right _)
          _ ≤ hsNorm A ^ i * (hsNorm (A - B) * hsNorm (B ^ (n - 1 - i))) :=
              mul_le_mul (hsNorm_pow_le hA hi0) (hsNorm_comp_le hAB (hB.pow hj))
                (hsNorm_nonneg _) (pow_nonneg (hsNorm_nonneg _) _)
          _ ≤ hsNorm A ^ i * (hsNorm (A - B) * hsNorm B ^ (n - 1 - i)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hsNorm_pow_le hB hj) (hsNorm_nonneg _))
                (pow_nonneg (hsNorm_nonneg _) _)
          _ ≤ R ^ i * (hsNorm (A - B) * R ^ (n - 1 - i)) :=
              mul_le_mul (pow_le_pow_left₀ (hsNorm_nonneg _) hRA _)
                (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hsNorm_nonneg _) hRB _)
                  (hsNorm_nonneg _))
                (mul_nonneg (hsNorm_nonneg _) (pow_nonneg (hsNorm_nonneg _) _))
                (pow_nonneg hR0 _)
          _ = R ^ (n - 1) * hsNorm (A - B) := by
              rw [mul_left_comm, ← pow_add, show i + (n - 1 - i) = n - 1 from by omega,
                mul_comm]
  have htr : trace (A ^ n) - trace (B ^ n) =
      ∑ i ∈ Finset.range n, trace ((A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i))) := by
    rw [← trace_sub (hA.isTraceClass_pow hn) (hB.isTraceClass_pow hn),
      sub_pow_eq_sum_comp A B n,
      trace_sum _ fun i hi => summable_inner_diagonal (hTC i hi) _]
  calc ‖trace (A ^ n) - trace (B ^ n)‖
      = ‖∑ i ∈ Finset.range n, trace ((A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i)))‖ := by rw [htr]
    _ ≤ ∑ i ∈ Finset.range n, ‖trace ((A ^ i) ∘L ((A - B) ∘L B ^ (n - 1 - i)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, R ^ (n - 1) * hsNorm (A - B) := Finset.sum_le_sum hbound
    _ = (n : ℝ) * R ^ (n - 1) * hsNorm (A - B) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]

/-- The tail of the absolute `z = 1` Plemelj series is summable for a Hilbert–Schmidt
operator (all powers `A ^ (m + 2)` are trace class by `IsHilbertSchmidt.isTraceClass_pow`,
so no trace-class hypothesis on `A` is needed). -/
theorem summable_norm_trace_pow_div_tail_of_hs {A : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    (hz : hsNorm A < 1) :
    Summable fun m : ℕ => ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) := by
  refine Summable.of_nonneg_of_le
    (fun m => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (fun m => ?_)
    ((summable_geometric_of_lt_one (hsNorm_nonneg A) hz).mul_left (hsNorm A ^ 2))
  calc ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
      ≤ hsNorm A ^ (m + 2) / ((m + 2 : ℕ) : ℝ) :=
        (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (show 0 < m + 2 by omega))).2
          (norm_trace_pow_le hA (show 2 ≤ m + 2 by omega))
    _ ≤ hsNorm A ^ (m + 2) :=
        div_le_self (pow_nonneg (hsNorm_nonneg _) _)
          (by exact_mod_cast (show 1 ≤ m + 2 by omega))
    _ = hsNorm A ^ 2 * hsNorm A ^ m := by
        rw [show m + 2 = 2 + m from by omega, pow_add]

/-- The tail of the `z = 1` Plemelj series (indices `m ≥ 2`) is summable for a
Hilbert–Schmidt operator. -/
theorem summable_trace_pow_div_tail_of_hs {A : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    (hz : hsNorm A < 1) : Summable fun m : ℕ => trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) := by
  apply Summable.of_norm
  exact (summable_norm_trace_pow_div_tail_of_hs hA hz).congr fun m => by
    rw [norm_div, RCLike.norm_natCast]

/-- The tail of the absolute `z = 1` Plemelj series of a Hilbert–Schmidt operator:
`∑'_{m ≥ 2} ‖tr(A^m)‖/m ≤ ‖A‖₂² / (2 (1 − ‖A‖₂))`. -/
theorem tsum_norm_trace_pow_div_tail_le_of_hs {A : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    (hz : hsNorm A < 1) :
    ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) ≤
      hsNorm A ^ 2 / (2 * (1 - hsNorm A)) := by
  have bound : ∀ m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) ≤
      (hsNorm A ^ 2 / 2) * hsNorm A ^ m := by
    intro m
    calc ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
        ≤ hsNorm A ^ (m + 2) / ((m + 2 : ℕ) : ℝ) :=
          (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (show 0 < m + 2 by omega))).2
            (norm_trace_pow_le hA (show 2 ≤ m + 2 by omega))
      _ ≤ hsNorm A ^ (m + 2) / 2 :=
          div_le_div_of_nonneg_left (pow_nonneg (hsNorm_nonneg _) _) (by norm_num)
            (by exact_mod_cast (show 2 ≤ m + 2 by omega))
      _ = (hsNorm A ^ 2 / 2) * hsNorm A ^ m := by
          rw [show m + 2 = 2 + m from by omega, pow_add, div_mul_eq_mul_div]
  have h1 : Summable fun m : ℕ => (hsNorm A ^ 2 / 2) * hsNorm A ^ m :=
    (summable_geometric_of_lt_one (hsNorm_nonneg A) hz).mul_left _
  calc ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
      ≤ ∑' m : ℕ, (hsNorm A ^ 2 / 2) * hsNorm A ^ m :=
        (summable_norm_trace_pow_div_tail_of_hs hA hz).tsum_le_tsum bound h1
    _ = (hsNorm A ^ 2 / 2) * ∑' m : ℕ, hsNorm A ^ m := by rw [← tsum_mul_left]
    _ = (hsNorm A ^ 2 / 2) * (1 - hsNorm A)⁻¹ := by
        rw [tsum_geometric_of_lt_one (hsNorm_nonneg A) hz]
    _ = hsNorm A ^ 2 / (2 * (1 - hsNorm A)) :=
        (div_eq_mul_inv _ _).symm.trans (div_div _ _ _)

/-- The norm of the tail of the `z = 1` Plemelj series of a Hilbert–Schmidt operator:
`‖∑'_{m ≥ 2} tr(A^m)/m‖ ≤ ‖A‖₂² / (2 (1 − ‖A‖₂))`. -/
theorem norm_tsum_trace_pow_div_tail_le_of_hs {A : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    (hz : hsNorm A < 1) :
    ‖∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ ≤
      hsNorm A ^ 2 / (2 * (1 - hsNorm A)) := by
  have hsumnorm : Summable fun m : ℕ => ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ :=
    (summable_norm_trace_pow_div_tail_of_hs hA hz).congr fun m => by
      rw [norm_div, RCLike.norm_natCast]
  calc ‖∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖
      ≤ ∑' m : ℕ, ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ := norm_tsum_le_tsum_norm hsumnorm
    _ = ∑' m : ℕ, ‖trace (A ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ) := tsum_congr fun m => by
        rw [norm_div, RCLike.norm_natCast]
    _ ≤ hsNorm A ^ 2 / (2 * (1 - hsNorm A)) := tsum_norm_trace_pow_div_tail_le_of_hs hA hz

/-- **Lipschitz bound for the Plemelj tail.**  The `m ≥ 2` Plemelj tail series — equivalently, by
`fredholmDetOne_eq_exp_neg_trace_mul_detTwo`, minus the `det₂` exponent series of `−A`
at `z = 1` — is Hilbert–Schmidt Lipschitz on the disk: for Hilbert–Schmidt `A, B` with
`‖A‖₂, ‖B‖₂ ≤ R < 1`, -/
theorem norm_trace_pow_div_tail_sub_le {A B : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) {R : ℝ} (hRA : hsNorm A ≤ R) (hRB : hsNorm B ≤ R)
    (hR : R < 1) :
    ‖(∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)) -
        ∑' m : ℕ, trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ ≤
      R / (1 - R) * hsNorm (A - B) := by
  have hR0 : 0 ≤ R := (hsNorm_nonneg A).trans hRA
  have hA1 : hsNorm A < 1 := hRA.trans_lt hR
  have hB1 : hsNorm B < 1 := hRB.trans_lt hR
  have hsA := summable_trace_pow_div_tail_of_hs hA hA1
  have hsB := summable_trace_pow_div_tail_of_hs hB hB1
  have hgeo : Summable fun m : ℕ => R ^ (m + 1) * hsNorm (A - B) :=
    (((summable_geometric_of_lt_one hR0 hR).mul_left R).congr fun m =>
      (pow_succ' R m).symm).mul_right _
  have hbound : ∀ m : ℕ,
      ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) - trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖
        ≤ R ^ (m + 1) * hsNorm (A - B) := by
    intro m
    rw [← sub_div, norm_div, RCLike.norm_natCast]
    have h := norm_trace_sub_pow_le hA hB hRA hRB (n := m + 2) (show 2 ≤ m + 2 by omega)
    have hm2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    calc ‖trace (A ^ (m + 2)) - trace (B ^ (m + 2))‖ / ((m + 2 : ℕ) : ℝ)
        ≤ ((m + 2 : ℕ) * R ^ (m + 1) * hsNorm (A - B)) / ((m + 2 : ℕ) : ℝ) :=
          (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr (by omega))).2 h
      _ = R ^ (m + 1) * hsNorm (A - B) := by
          rw [mul_assoc, mul_div_cancel_left₀ _ hm2]
  have hsumnorm : Summable fun m : ℕ =>
      ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) - trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound hgeo
  rw [← Summable.tsum_sub hsA hsB]
  calc ‖∑' m : ℕ, (trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) -
          trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜))‖
      ≤ ∑' m : ℕ, ‖trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) -
          trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)‖ := norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' m : ℕ, R ^ (m + 1) * hsNorm (A - B) := hsumnorm.tsum_le_tsum hbound hgeo
    _ = hsNorm (A - B) * R * ∑' m : ℕ, R ^ m := by
        rw [← tsum_mul_left]
        exact tsum_congr fun m => by rw [pow_succ']; ring
    _ = hsNorm (A - B) * R * (1 - R)⁻¹ := by
        rw [tsum_geometric_of_lt_one hR0 hR]
    _ = R / (1 - R) * hsNorm (A - B) := by rw [div_eq_mul_inv]; ring

/-- The exponential of the `m ≥ 2` Plemelj tail is Hilbert–Schmidt Lipschitz on the
disk: for Hilbert–Schmidt `A, B` with `‖A‖₂, ‖B‖₂ ≤ R < 1`, writing
`S̃(A) = ∑'_{m ≥ 2} tr(A^m)/m`, -/
theorem norm_exp_neg_trace_pow_div_tail_sub_le {A B : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) {R : ℝ} (hRA : hsNorm A ≤ R) (hRB : hsNorm B ≤ R)
    (hR : R < 1) :
    ‖NormedSpace.exp (-∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜)) -
        NormedSpace.exp (-∑' m : ℕ, trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜))‖ ≤
      Real.exp (hsNorm B ^ 2 / (2 * (1 - hsNorm B))) *
        ((R / (1 - R) * hsNorm (A - B)) * Real.exp (R / (1 - R) * hsNorm (A - B))) := by
  have hR0 : 0 ≤ R := (hsNorm_nonneg A).trans hRA
  have hA1 : hsNorm A < 1 := hRA.trans_lt hR
  have hB1 : hsNorm B < 1 := hRB.trans_lt hR
  set SA : 𝕜 := ∑' m : ℕ, trace (A ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) with hSA
  set SB : 𝕜 := ∑' m : ℕ, trace (B ^ (m + 2)) / ((m + 2 : ℕ) : 𝕜) with hSB
  have hSBA : ‖SA - SB‖ ≤ R / (1 - R) * hsNorm (A - B) :=
    norm_trace_pow_div_tail_sub_le hA hB hRA hRB hR
  have hSBn : ‖SB‖ ≤ hsNorm B ^ 2 / (2 * (1 - hsNorm B)) :=
    norm_tsum_trace_pow_div_tail_le_of_hs hB hB1
  have hD0 : 0 ≤ R / (1 - R) * hsNorm (A - B) :=
    mul_nonneg (div_nonneg hR0 (by linarith)) (hsNorm_nonneg _)
  have hfact : NormedSpace.exp (-SA) - NormedSpace.exp (-SB) =
      NormedSpace.exp (-SB) * (NormedSpace.exp (SB - SA) - 1) := by
    have h1 : NormedSpace.exp (-SB) * NormedSpace.exp (SB - SA) = NormedSpace.exp (-SA) := by
      rw [← NormedSpace.exp_add]
      congr 1
      ring
    rw [← h1]
    ring
  rw [hfact, norm_mul]
  have h2 := norm_exp_sub_one_le (SB - SA)
  rw [show ‖SB - SA‖ = ‖SA - SB‖ from norm_sub_rev _ _] at h2
  have h1 : ‖NormedSpace.exp (-SB)‖ ≤ Real.exp (hsNorm B ^ 2 / (2 * (1 - hsNorm B))) :=
    (norm_exp_le _).trans (Real.exp_le_exp.mpr (by rw [norm_neg]; exact hSBn))
  calc ‖NormedSpace.exp (-SB)‖ * ‖NormedSpace.exp (SB - SA) - 1‖
      ≤ Real.exp (hsNorm B ^ 2 / (2 * (1 - hsNorm B))) *
          (‖SA - SB‖ * Real.exp ‖SA - SB‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_nonneg _)
    _ ≤ Real.exp (hsNorm B ^ 2 / (2 * (1 - hsNorm B))) *
          ((R / (1 - R) * hsNorm (A - B)) * Real.exp (R / (1 - R) * hsNorm (A - B))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hSBA (Real.exp_le_exp.mpr hSBA) (Real.exp_nonneg _) hD0)
          (Real.exp_nonneg _)

end LipschitzTail

end HilbertSchmidt
