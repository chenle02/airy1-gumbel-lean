/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TraceClass.TraceClass
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # The 2-regularized Fredholm determinant for Hilbert–Schmidt operators

For a Hilbert–Schmidt operator `K : E →L[𝕜] E` on a Hilbert space over `𝕜 = ℝ` or `ℂ`
(`RCLike 𝕜`), the powers `K ^ m` are trace class for `m ≥ 2` (`TraceClass/TraceClass.lean`), so the
Plemelj-type trace series

  `∑_{m=2}^∞ (−1)^{m+1} z^m · tr(K^m) / m`

is well-defined term by term, and the **2-regularized Fredholm determinant** is

  `det₂(1 + zK) := exp (∑_{m ≥ 2} (−1)^{m+1} z^m tr(K^m) / m)`.

## What is proved here

* `HilbertSchmidt.IsTraceClass.comp_right`, `HilbertSchmidt.IsTraceClass.comp_left`: the
  trace class is a two-sided ideal among bounded operators.
* `HilbertSchmidt.IsHilbertSchmidt.isTraceClass_pow`: for `2 ≤ m`, `K ^ m` is trace class
  when `K` is Hilbert–Schmidt (it factors as `K² ∘L K^{m-2}`).
* `HilbertSchmidt.hsENorm_comp_le`, `HilbertSchmidt.hsENorm_pow_le`,
  `HilbertSchmidt.hsNorm_pow_le`: submultiplicativity of the Hilbert–Schmidt norm,
  `‖K ^ j‖₂ ≤ ‖K‖₂ ^ j` for `1 ≤ j`.
* `HilbertSchmidt.norm_trace_comp_le`: `‖tr (A ∘L B)‖ ≤ ‖A‖₂ ‖B‖₂` (Cauchy–Schwarz on the
  diagonal, through the adjoint factorization), and
  `HilbertSchmidt.norm_trace_pow_le`: `‖tr (K ^ m)‖ ≤ ‖K‖₂ ^ m` for `2 ≤ m`.
* `HilbertSchmidt.summable_norm_fredholmDetTwoTerm`: the series converges **absolutely**
  on the open disk `‖z‖ * ‖K‖₂ < 1`, and
  `HilbertSchmidt.inv_hsNorm_le_radius`: the associated formal power series has radius of
  convergence at least `(‖K‖₂)⁻¹` (with `(0)⁻¹ = ⊤`, so the radius is infinite when
  `K = 0`).
* `HilbertSchmidt.fredholmDetTwo`: the definition `det₂ K z = exp (series-sum)`.
* `HilbertSchmidt.differentiableOn_fredholmDetTwo`: `z ↦ det₂ K z` is differentiable on the
  open ball `Metric.eball 0 (‖K‖₂)⁻¹`; `HilbertSchmidt.fredholmDetTwo_zero`: the value at
  `z = 0` is `1`; `HilbertSchmidt.hasFDerivAt_fredholmDetTwo_zero` and
  `HilbertSchmidt.deriv_fredholmDetTwo_zero`: the derivative at `z = 0` is `0` (the
  coefficient of `z¹` vanishes — this is exactly the 2-regularization).
* `HilbertSchmidt.differentiable_fredholmDetTwo_of_hsNorm_eq_zero`: in the degenerate case
  `‖K‖₂ = 0` (i.e. `K = 0`), `det₂ K` is the constant function `1`, hence differentiable
  everywhere.

## What is NOT proved here (scope note)

The Plemelj trace series has radius of convergence `1 / spr(K)` in general (`spr` the
spectral radius), so `det₂(1 + zK)` *as defined by this series* is genuinely analytic only
on a disk: for `K = diag(1, 1/2, 1/3, …)` on `ℓ²(ℕ)` (Hilbert–Schmidt), `tr(K^m) = ζ(m) → 1`
and the series has radius exactly `1`. The classical fact that `det₂` extends to an *entire*
function for Hilbert–Schmidt `K` requires a different global definition (the Hadamard
product over eigenvalues `(1 + zλ_j) e^{−zλ_j}`, or equivalently the Plemelj–Smithies
exterior-power series, which has `1/n!` factors and converges everywhere) plus the equality
with the trace series on the disk. That entire extension is future work; nothing in this
file claims it.

## Possible extensions

* The entire extension of `det₂` via the Hadamard product or the Plemelj–Smithies series.
* `det₂(1 + zK) = det((1 + zK) ∘ exp(−zK))` for trace-class `K`.
* Multiplicative properties: `det₂((1 + zA)(1 + zB)) = det₂(1 + zA) det₂(1 + zB)
  exp(z² tr(AB))`-type identities, as needed by the Airy-kernel application.
-/

open Filter
open scoped ENNReal NNReal InnerProduct InnerProductSpace

namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

section TraceClassIdeal

/-- The trace class is a right ideal: a trace-class operator composed on the right with a
bounded operator is trace class. -/
theorem IsTraceClass.comp_right {T : E →L[𝕜] E} (hT : IsTraceClass T) (S : E →L[𝕜] E) :
    IsTraceClass (T ∘L S) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  exact ⟨A, B ∘L S, hA, hB.comp_right S, ContinuousLinearMap.comp_assoc A B S⟩

/-- The trace class is a left ideal: a trace-class operator composed on the left with a
bounded operator is trace class. -/
theorem IsTraceClass.comp_left {T : E →L[𝕜] E} (hT : IsTraceClass T) (S : E →L[𝕜] E) :
    IsTraceClass (S ∘L T) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  exact ⟨S ∘L A, B, hA.comp_left S, hB, (ContinuousLinearMap.comp_assoc S A B).symm⟩

omit [CompleteSpace E] in
/-- For `1 ≤ m`, the `m`-th power splits as `K ^ m = K ∘L K ^ (m - 1)`. -/
theorem pow_eq_comp_one_sub (K : E →L[𝕜] E) {m : ℕ} (hm : 1 ≤ m) :
    K ^ m = K ∘L K ^ (m - 1) := by
  conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ']
  rfl

/-- Powers of exponent at least `2` of a Hilbert–Schmidt operator are trace class:
`K ^ m = (K ∘L K) ∘L K ^ (m - 2)` factors through the trace-class `K ^ 2`. -/
theorem IsHilbertSchmidt.isTraceClass_pow {K : E →L[𝕜] E} (hK : IsHilbertSchmidt K) {m : ℕ}
    (hm : 2 ≤ m) : IsTraceClass (K ^ m) := by
  have h2 : IsTraceClass (K ^ 2) := by
    rw [pow_two]
    exact ⟨K, K, hK, hK, rfl⟩
  rw [show m = 2 + (m - 2) from (Nat.add_sub_cancel' hm).symm, pow_add]
  exact h2.comp_right _

end TraceClassIdeal

section HSNorm

/-- The real-valued Hilbert–Schmidt norm `‖T‖₂`: the `toReal` of the `ℝ≥0∞`-valued
Hilbert–Schmidt enorm.  It is finite (i.e. the enorm is not `⊤`) exactly when `T` is
Hilbert–Schmidt. -/
noncomputable def hsNorm (T : E →L[𝕜] E) : ℝ := (hsENorm T).toReal

/-- The Hilbert–Schmidt norm is nonnegative. -/
theorem hsNorm_nonneg (T : E →L[𝕜] E) : 0 ≤ hsNorm T := ENNReal.toReal_nonneg

/-- The Hilbert–Schmidt enorm of the adjoint equals that of the operator. -/
theorem hsENorm_adjoint (T : E →L[𝕜] E) : hsENorm (T†) = hsENorm T := by
  unfold hsENorm
  rw [sumSq_eq_sumSq_adjoint (T†) (canonicalBasis 𝕜 E) (canonicalBasis 𝕜 E),
    ContinuousLinearMap.adjoint_adjoint]

/-- The real Hilbert–Schmidt norm of the adjoint equals that of the operator. -/
theorem hsNorm_adjoint (T : E →L[𝕜] E) : hsNorm (T†) = hsNorm T := by
  unfold hsNorm
  rw [hsENorm_adjoint]

/-- The Hilbert–Schmidt enorm is submultiplicative: `‖S ∘L T‖₂ ≤ ‖S‖₂ * ‖T‖₂`. -/
theorem hsENorm_comp_le (S T : E →L[𝕜] E) : hsENorm (S ∘L T) ≤ hsENorm S * hsENorm T := by
  unfold hsENorm
  calc (sumSq (S ∘L T) (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ)
      ≤ (‖S‖ₑ ^ 2 * sumSq T (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (sumSq_comp_le S T (canonicalBasis 𝕜 E))
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
    _ = ‖S‖ₑ * (sumSq T (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), rpow_half_sq']
    _ ≤ (sumSq S (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ) *
          (sumSq T (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ) :=
        mul_le_mul_left (opENorm_le_sumSq_rpow_half S (canonicalBasis 𝕜 E)) _

/-- `(x ^ n).toReal = (x.toReal) ^ n` for `x : ℝ≥0∞`. -/
theorem toReal_pow (x : ℝ≥0∞) (n : ℕ) : (x ^ n).toReal = x.toReal ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ENNReal.toReal_mul, ih, pow_succ]

omit [CompleteSpace E] in
/-- For `1 ≤ j`, `K ^ (j + 1) = K ^ j ∘L K` (the monoid multiplication on `E →L[𝕜] E` is
composition). -/
theorem pow_succ_eq_comp (K : E →L[𝕜] E) (j : ℕ) : K ^ (j + 1) = (K ^ j) ∘L K := by
  conv_lhs => rw [pow_succ]
  rfl

/-- Powers have submultiplicative Hilbert–Schmidt enorm: `‖K ^ j‖₂ ≤ ‖K‖₂ ^ j` for
`1 ≤ j`. -/
theorem hsENorm_pow_le (K : E →L[𝕜] E) {j : ℕ} (hj : 1 ≤ j) :
    hsENorm (K ^ j) ≤ hsENorm K ^ j := by
  induction j, hj using Nat.le_induction with
  | base => rw [pow_one, pow_one]
  | succ j hj ih =>
      rw [pow_succ_eq_comp K j]
      calc hsENorm ((K ^ j) ∘L K) ≤ hsENorm (K ^ j) * hsENorm K := hsENorm_comp_le _ _
        _ ≤ hsENorm K ^ j * hsENorm K := mul_le_mul_left ih _
        _ = hsENorm K ^ (j + 1) := by rw [pow_succ]

/-- The real-valued power bound: `‖K ^ j‖₂ ≤ ‖K‖₂ ^ j` for `1 ≤ j` and Hilbert–Schmidt
`K`. -/
theorem hsNorm_pow_le {K : E →L[𝕜] E} (hK : IsHilbertSchmidt K) {j : ℕ} (hj : 1 ≤ j) :
    hsNorm (K ^ j) ≤ hsNorm K ^ j := by
  have htop : hsENorm K ^ j ≠ ⊤ :=
    lt_top_iff_ne_top.1 (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 hK))
  have h := ENNReal.toReal_mono htop (hsENorm_pow_le K hj)
  rw [toReal_pow] at h
  exact h

/-- Powers of exponent at least `1` of a Hilbert–Schmidt operator are Hilbert–Schmidt. -/
theorem IsHilbertSchmidt.pow {K : E →L[𝕜] E} (hK : IsHilbertSchmidt K) {j : ℕ}
    (hj : 1 ≤ j) : IsHilbertSchmidt (K ^ j) :=
  lt_top_iff_ne_top.1 (lt_of_le_of_lt (hsENorm_pow_le K hj)
    (ENNReal.pow_lt_top (lt_top_iff_ne_top.2 hK)))

end HSNorm

section TraceBound

/-- Squared Cauchy–Schwarz for `tsum`: for nonnegative real families with summable
squares, `(∑' i, a i * b i) ^ 2 ≤ (∑' i, a i ^ 2) * (∑' i, b i ^ 2)`. -/
theorem tsum_mul_sq_le {ι : Type*} {a b : ι → ℝ}
    (ha : Summable fun i => a i ^ 2) (hb : Summable fun i => b i ^ 2)
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i) :
    (∑' i, a i * b i) ^ 2 ≤ (∑' i, a i ^ 2) * (∑' i, b i ^ 2) := by
  have hab : Summable fun i => a i * b i := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (ha0 i) (hb0 i)) _
        ((ha.add hb).div_const 2)
    intro i
    have h := two_mul_le_add_pow_two (a i) (b i)
    calc a i * b i = 2 * a i * b i / 2 := by ring
      _ ≤ (a i ^ 2 + b i ^ 2) / 2 := by linarith
  have hX : (∑' i, a i * b i) ≤ Real.sqrt ((∑' i, a i ^ 2) * (∑' i, b i ^ 2)) := by
    apply hab.tsum_le_of_sum_le
    intro s
    calc ∑ i ∈ s, a i * b i
        ≤ Real.sqrt ((∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2)) :=
          (Real.le_sqrt (Finset.sum_nonneg fun i _ => mul_nonneg (ha0 i) (hb0 i))
            (mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
              (Finset.sum_nonneg fun i _ => sq_nonneg _))).2
            (Finset.sum_mul_sq_le_sq_mul_sq s a b)
      _ ≤ Real.sqrt ((∑' i, a i ^ 2) * (∑' i, b i ^ 2)) := by
          apply Real.sqrt_le_sqrt
          exact mul_le_mul (ha.sum_le_tsum s fun i _ => sq_nonneg _)
            (hb.sum_le_tsum s fun i _ => sq_nonneg _)
            (Finset.sum_nonneg fun i _ => sq_nonneg _)
            (tsum_nonneg fun i => sq_nonneg _)
  calc (∑' i, a i * b i) ^ 2
      ≤ (Real.sqrt ((∑' i, a i ^ 2) * (∑' i, b i ^ 2))) ^ 2 :=
        pow_le_pow_left₀ (tsum_nonneg fun i => mul_nonneg (ha0 i) (hb0 i)) hX 2
    _ = (∑' i, a i ^ 2) * (∑' i, b i ^ 2) :=
        Real.sq_sqrt (mul_nonneg (tsum_nonneg fun i => sq_nonneg _)
          (tsum_nonneg fun i => sq_nonneg _))

/-- The trace of a product of two Hilbert–Schmidt operators is bounded by the product of
their Hilbert–Schmidt norms: `‖tr (A ∘L B)‖ ≤ ‖A‖₂ * ‖B‖₂`.  This is the Hilbert–Schmidt
factorization form of the trace-norm bound `‖T‖₁ ≤ ‖A‖₂ ‖B‖₂` for `T = A ∘L B`. -/
theorem norm_trace_comp_le {A B : E →L[𝕜] E} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) :
    ‖trace (A ∘L B)‖ ≤ hsNorm A * hsNorm B := by
  have hT : IsTraceClass (A ∘L B) := ⟨A, B, hA, hB, rfl⟩
  have hsum1 : Summable fun i =>
      ‖⟪canonicalBasis 𝕜 E i, (A ∘L B) (canonicalBasis 𝕜 E i)⟫_𝕜‖ :=
    summable_norm_inner_diagonal hT _
  have hsumA : Summable fun i => ‖(A†) (canonicalBasis 𝕜 E i)‖ ^ 2 :=
    summable_norm_sq_apply_basis hA.adjoint _
  have hsumB : Summable fun i => ‖B (canonicalBasis 𝕜 E i)‖ ^ 2 :=
    summable_norm_sq_apply_basis hB _
  have hsum1' : Summable fun i =>
      ‖⟪(A†) (canonicalBasis 𝕜 E i), B (canonicalBasis 𝕜 E i)⟫_𝕜‖ :=
    hsum1.congr fun i => by
      rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left]
  have hprod : Summable fun i =>
      ‖(A†) (canonicalBasis 𝕜 E i)‖ * ‖B (canonicalBasis 𝕜 E i)‖ := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
      ((hsumA.add hsumB).div_const 2)
    intro i
    have h := two_mul_le_add_pow_two ‖(A†) (canonicalBasis 𝕜 E i)‖ ‖B (canonicalBasis 𝕜 E i)‖
    calc ‖(A†) (canonicalBasis 𝕜 E i)‖ * ‖B (canonicalBasis 𝕜 E i)‖
        = 2 * ‖(A†) (canonicalBasis 𝕜 E i)‖ * ‖B (canonicalBasis 𝕜 E i)‖ / 2 := by ring
      _ ≤ (‖(A†) (canonicalBasis 𝕜 E i)‖ ^ 2 + ‖B (canonicalBasis 𝕜 E i)‖ ^ 2) / 2 := by
          linarith
  have heval : ∀ {T : E →L[𝕜] E}, IsHilbertSchmidt T →
      (∑' i, ‖T (canonicalBasis 𝕜 E i)‖ ^ 2) = hsNorm T ^ 2 := by
    intro T hT
    have h1 : ENNReal.ofReal (∑' i, ‖T (canonicalBasis 𝕜 E i)‖ ^ 2)
        = sumSq T (canonicalBasis 𝕜 E) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
        (summable_norm_sq_apply_basis hT _)]
      exact tsum_congr fun i => (enorm_sq_eq_ofReal _).symm
    have h2 : hsNorm T ^ 2 = (sumSq T (canonicalBasis 𝕜 E)).toReal := by
      unfold hsNorm hsENorm
      rw [← toReal_pow _ 2, rpow_half_sq]
    rw [← h1] at h2
    rw [h2, ENNReal.toReal_ofReal (tsum_nonneg fun i => sq_nonneg _)]
  have hsq : ‖trace (A ∘L B)‖ ^ 2 ≤ (hsNorm A * hsNorm B) ^ 2 := by
    calc ‖trace (A ∘L B)‖ ^ 2
        = ‖∑' i, ⟪canonicalBasis 𝕜 E i, (A ∘L B) (canonicalBasis 𝕜 E i)⟫_𝕜‖ ^ 2 := rfl
      _ ≤ (∑' i, ‖⟪canonicalBasis 𝕜 E i, (A ∘L B) (canonicalBasis 𝕜 E i)⟫_𝕜‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_tsum_le_tsum_norm hsum1) 2
      _ = (∑' i, ‖⟪(A†) (canonicalBasis 𝕜 E i), B (canonicalBasis 𝕜 E i)⟫_𝕜‖) ^ 2 := by
            congr 1
            exact tsum_congr fun i => by
              rw [ContinuousLinearMap.comp_apply,
                ← ContinuousLinearMap.adjoint_inner_left]
      _ ≤ (∑' i, ‖(A†) (canonicalBasis 𝕜 E i)‖ * ‖B (canonicalBasis 𝕜 E i)‖) ^ 2 :=
          pow_le_pow_left₀ (tsum_nonneg fun i => norm_nonneg _)
            (hsum1'.tsum_le_tsum (fun i => norm_inner_le_norm _ _) hprod) 2
      _ ≤ (∑' i, ‖(A†) (canonicalBasis 𝕜 E i)‖ ^ 2) *
            (∑' i, ‖B (canonicalBasis 𝕜 E i)‖ ^ 2) :=
          tsum_mul_sq_le hsumA hsumB (fun i => norm_nonneg _) (fun i => norm_nonneg _)
      _ = hsNorm A ^ 2 * hsNorm B ^ 2 := by
            rw [heval hA.adjoint, heval hB, hsNorm_adjoint]
      _ = (hsNorm A * hsNorm B) ^ 2 := (mul_pow ..).symm
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _))] at h

/-- The trace-of-power bound `‖tr (K ^ m)‖ ≤ ‖K‖₂ ^ m` for `2 ≤ m`, from
`K ^ m = K ∘L K ^ (m - 1)` and `norm_trace_comp_le`. -/
theorem norm_trace_pow_le {K : E →L[𝕜] E} (hK : IsHilbertSchmidt K) {m : ℕ} (hm : 2 ≤ m) :
    ‖trace (K ^ m)‖ ≤ hsNorm K ^ m := by
  have hm1 : 1 ≤ m - 1 := by omega
  have hKj : IsHilbertSchmidt (K ^ (m - 1)) := hK.pow hm1
  calc ‖trace (K ^ m)‖ = ‖trace (K ∘L K ^ (m - 1))‖ := by rw [pow_eq_comp_one_sub K (by omega)]
    _ ≤ hsNorm K * hsNorm (K ^ (m - 1)) := norm_trace_comp_le hK hKj
    _ ≤ hsNorm K * hsNorm K ^ (m - 1) :=
        mul_le_mul_of_nonneg_left (hsNorm_pow_le hK hm1) (hsNorm_nonneg K)
    _ = hsNorm K ^ m := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]

end TraceBound

section Coefficient

/-- The coefficients of the Plemelj-type series of the 2-regularized determinant:
`cₘ = (−1)^{m+1} · tr(K ^ m) / m` for `m ≥ 2`, and `c₀ = c₁ = 0`.  The vanishing of the
first two coefficients is exactly the 2-regularization. -/
noncomputable def fredholmDetTwoCoeff (K : E →L[𝕜] E) (m : ℕ) : 𝕜 :=
  if 2 ≤ m then (-1 : 𝕜) ^ (m + 1) * trace (K ^ m) / m else 0

/-- The first coefficient vanishes. -/
theorem fredholmDetTwoCoeff_zero (K : E →L[𝕜] E) : fredholmDetTwoCoeff K 0 = 0 := by
  unfold fredholmDetTwoCoeff
  norm_num

/-- The second coefficient vanishes. -/
theorem fredholmDetTwoCoeff_one (K : E →L[𝕜] E) : fredholmDetTwoCoeff K 1 = 0 := by
  unfold fredholmDetTwoCoeff
  norm_num

/-- The coefficient bound `‖cₘ‖ ≤ ‖K‖₂ ^ m / m` for `2 ≤ m`. -/
theorem norm_fredholmDetTwoCoeff_le {K : E →L[𝕜] E} (hK : IsHilbertSchmidt K) {m : ℕ}
    (hm : 2 ≤ m) :
    ‖fredholmDetTwoCoeff K m‖ ≤ hsNorm K ^ m / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [fredholmDetTwoCoeff, ite_eq_left hm, norm_div, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, RCLike.norm_natCast]
  exact (div_le_div_iff_of_pos_right hm0).2 (norm_trace_pow_le hK hm)

/-- Absolute convergence of the coefficient series weighted by `r ^ m` for real `r` with
`r * ‖K‖₂ < 1`: comparison with the geometric series of ratio `r * ‖K‖₂`. -/
theorem summable_norm_fredholmDetTwoCoeff_mul_pow {K : E →L[𝕜] E} (hK : IsHilbertSchmidt K)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r * hsNorm K < 1) :
    Summable fun m => ‖fredholmDetTwoCoeff K m‖ * r ^ m := by
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 _)) _
    (summable_geometric_of_lt_one (mul_nonneg hr0 (hsNorm_nonneg K)) hr)
  intro m
  by_cases hm : 2 ≤ m
  · calc ‖fredholmDetTwoCoeff K m‖ * r ^ m
        ≤ (hsNorm K ^ m / m) * r ^ m :=
          mul_le_mul_of_nonneg_right (norm_fredholmDetTwoCoeff_le hK hm) (pow_nonneg hr0 m)
      _ ≤ hsNorm K ^ m * r ^ m :=
          mul_le_mul_of_nonneg_right
            (div_le_self (pow_nonneg (hsNorm_nonneg _) _)
              (by exact_mod_cast (by omega : 1 ≤ m))) (pow_nonneg hr0 m)
      _ = (r * hsNorm K) ^ m := by
          rw [← mul_pow, mul_comm (hsNorm K) r]
  · rw [fredholmDetTwoCoeff, ite_eq_right hm, norm_zero, zero_mul]
    exact pow_nonneg (mul_nonneg hr0 (hsNorm_nonneg K)) m

/-- Absolute convergence of the Plemelj series on the open disk `‖z‖ * ‖K‖₂ < 1`:
`∑' m, ‖cₘ z ^ m‖ < ∞`. -/
theorem summable_norm_fredholmDetTwoTerm {K : E →L[𝕜] E} (hK : IsHilbertSchmidt K) {z : 𝕜}
    (hz : ‖z‖ * hsNorm K < 1) :
    Summable fun m => ‖fredholmDetTwoCoeff K m * z ^ m‖ := by
  have h := summable_norm_fredholmDetTwoCoeff_mul_pow hK (norm_nonneg z) hz
  apply h.congr
  intro m
  rw [norm_mul, norm_pow]

end Coefficient

section Series

/-- The Plemelj-type formal power series `∑ cₘ x ^ m` of the 2-regularized
log-determinant. -/
noncomputable def fredholmDetTwoSeries (K : E →L[𝕜] E) : FormalMultilinearSeries 𝕜 𝕜 𝕜 :=
  .ofScalars 𝕜 (fredholmDetTwoCoeff K)

/-- The radius of convergence of the Plemelj series is at least `(‖K‖₂)⁻¹` (read as `⊤`
when `‖K‖₂ = 0`). -/
theorem inv_hsNorm_le_radius {K : E →L[𝕜] E} (hK : IsHilbertSchmidt K) :
    (ENNReal.ofReal (hsNorm K))⁻¹ ≤ (fredholmDetTwoSeries K).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have hr1 : (r : ℝ) * hsNorm K < 1 := by
    have h1 : (r : ℝ≥0∞) * ENNReal.ofReal (hsNorm K) < 1 := by
      have hr' : (r : ℝ≥0∞) < 1 / ENNReal.ofReal (hsNorm K) := by
        rw [one_div]
        exact hr
      exact (ENNReal.lt_div_iff_mul_lt (Or.inr ENNReal.coe_ne_top)
        (Or.inl ENNReal.ofReal_ne_top)).1 hr'
    have h2 : (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := ENNReal.ofReal_coe_nnreal.symm
    rw [h2, ← ENNReal.ofReal_mul (NNReal.coe_nonneg r)] at h1
    exact ENNReal.ofReal_lt_one.1 h1
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have hs := summable_norm_fredholmDetTwoCoeff_mul_pow hK (NNReal.coe_nonneg r) hr1
  apply hs.congr
  intro m
  rw [fredholmDetTwoSeries, FormalMultilinearSeries.ofScalars_norm]

/-- The radius of convergence of the Plemelj series is positive. -/
theorem fredholmDetTwoSeries_radius_pos {K : E →L[𝕜] E} (hK : IsHilbertSchmidt K) :
    0 < (fredholmDetTwoSeries K).radius :=
  (ENNReal.inv_pos.2 ENNReal.ofReal_ne_top).trans_le (inv_hsNorm_le_radius hK)

end Series

section Determinant

/-- The 2-regularized Fredholm determinant of a Hilbert–Schmidt operator:

  `det₂(1 + zK) := exp (∑_{m ≥ 2} (−1)^{m+1} z^m tr(K^m) / m)`,

defined for all `z` as the exponential of the sum of the formal power series
`fredholmDetTwoSeries K` (the sum takes the junk value `0` outside the disk of
convergence, so `det₂ K z = 1` there by convention; the meaningful values are on the open
disk `‖z‖ * ‖K‖₂ < 1`, see `summable_norm_fredholmDetTwoTerm` and
`inv_hsNorm_le_radius`). -/
noncomputable def fredholmDetTwo (K : E →L[𝕜] E) (z : 𝕜) : 𝕜 :=
  NormedSpace.exp ((fredholmDetTwoSeries K).sum z)

/-- The series representation: `det₂ K z = exp (∑' m, cₘ * z ^ m)`. -/
theorem fredholmDetTwo_eq_exp_tsum (K : E →L[𝕜] E) (z : 𝕜) :
    fredholmDetTwo K z = NormedSpace.exp (∑' m, fredholmDetTwoCoeff K m * z ^ m) := by
  unfold fredholmDetTwo fredholmDetTwoSeries
  congr 1
  exact tsum_congr fun m => by
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- `det₂ K 0 = 1`. -/
@[simp]
theorem fredholmDetTwo_zero (K : E →L[𝕜] E) : fredholmDetTwo K 0 = 1 := by
  have h0 : (fredholmDetTwoSeries K).sum 0 = 0 := by
    have h := FormalMultilinearSeries.ofScalarsSum_zero (E := 𝕜) (c := fredholmDetTwoCoeff K)
    rw [fredholmDetTwoCoeff_zero K] at h
    rw [zero_smul] at h
    exact h
  rw [fredholmDetTwo, h0, NormedSpace.exp_zero]

/-- `det₂ K` has derivative `0` at `z = 0`: the coefficient of `z ^ 1` vanishes. -/
theorem hasFDerivAt_fredholmDetTwo_zero {K : E →L[𝕜] E} (hK : IsHilbertSchmidt K) :
    HasFDerivAt (fredholmDetTwo K) (0 : 𝕜 →L[𝕜] 𝕜) 0 := by
  have hp := ((fredholmDetTwoSeries K).hasFPowerSeriesOnBall
    (fredholmDetTwoSeries_radius_pos hK)).hasFPowerSeriesAt.hasFDerivAt
  have hL : continuousMultilinearCurryFin1 𝕜 𝕜 𝕜 (fredholmDetTwoSeries K 1) = 0 := by
    have h1 : fredholmDetTwoSeries K 1 = 0 := by
      show FormalMultilinearSeries.ofScalars 𝕜 (fredholmDetTwoCoeff K) 1 = 0
      exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero 𝕜
        (fredholmDetTwoCoeff_one K)
    rw [h1, map_zero]
  rw [hL] at hp
  have hcomp := (hasFDerivAt_exp (𝕂 := 𝕜)).comp 0 hp
  rw [ContinuousLinearMap.comp_zero] at hcomp
  exact hcomp

/-- The scalar derivative of `det₂ K` at `z = 0` is `0`. -/
theorem deriv_fredholmDetTwo_zero {K : E →L[𝕜] E} (hK : IsHilbertSchmidt K) :
    deriv (fredholmDetTwo K) 0 = 0 := by
  have h := (hasFDerivAt_fredholmDetTwo_zero hK).hasDerivAt
  rw [h.deriv]
  simp

/-- `z ↦ det₂ K z` is differentiable on the open ball of radius `(‖K‖₂)⁻¹` centered at
`0` (the whole space when `‖K‖₂ = 0`). -/
theorem differentiableOn_fredholmDetTwo {K : E →L[𝕜] E} (hK : IsHilbertSchmidt K) :
    DifferentiableOn 𝕜 (fredholmDetTwo K)
      (Metric.eball 0 (ENNReal.ofReal (hsNorm K))⁻¹) := by
  have hp := ((fredholmDetTwoSeries K).hasFPowerSeriesOnBall
    (fredholmDetTwoSeries_radius_pos hK)).differentiableOn
  have hsub : Metric.eball (0 : 𝕜) (ENNReal.ofReal (hsNorm K))⁻¹ ⊆
      Metric.eball (0 : 𝕜) (fredholmDetTwoSeries K).radius :=
    Metric.eball_subset_eball (inv_hsNorm_le_radius hK)
  have hexp : Differentiable 𝕜 (NormedSpace.exp : 𝕜 → 𝕜) :=
    fun _ => hasFDerivAt_exp.differentiableAt
  exact hexp.comp_differentiableOn (hp.mono hsub)

/-- In the degenerate case `‖K‖₂ = 0` (equivalently `K = 0`), `det₂ K` is differentiable
everywhere: the ball is the whole space. -/
theorem differentiable_fredholmDetTwo_of_hsNorm_eq_zero {K : E →L[𝕜] E}
    (hK : IsHilbertSchmidt K) (h0 : hsNorm K = 0) :
    Differentiable 𝕜 (fredholmDetTwo K) := by
  rw [← differentiableOn_univ]
  have huniv : (Set.univ : Set 𝕜) = Metric.eball 0 (ENNReal.ofReal (hsNorm K))⁻¹ := by
    rw [h0, ENNReal.ofReal_zero, ENNReal.inv_zero]
    ext z
    simp
  rw [huniv]
  exact differentiableOn_fredholmDetTwo hK

end Determinant

end HilbertSchmidt
