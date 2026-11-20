/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Hilbert–Schmidt operators: the sum-of-squares enorm

For a continuous linear map `T : E →L[𝕜] F` between inner product spaces over an `RCLike`
field `𝕜`, and a Hilbert basis `b : HilbertBasis ι 𝕜 E` of the domain, we define the
Hilbert–Schmidt sum of squares

  `HS²(T, b) := ∑' i, ‖T (b i)‖ₑ ^ 2`,

and prove that it is **independent of the basis** (`HilbertSchmidt.sumSq_independent`).
This is the enorm side of the design prescribed in the review of mathlib PR #41477: the
Hilbert–Schmidt norm is defined on plain continuous linear maps (an `ℝ≥0∞`-valued enorm),
without a separate type and without a `NormedAddCommGroup` structure (which exists only in
finite dimension).

## Proof outline for basis independence

With `c` any Hilbert basis of `F`, two applications of Parseval
(`HilbertBasis.norm_sq_eq_tsum_norm_inner`, proved from
`HilbertBasis.tsum_inner_mul_inner`) plus Tonelli for the double sum of nonnegative reals
(`ENNReal.tsum_comm`) give

  `∑ᵢ ‖T bᵢ‖² = ∑ᵢ∑ⱼ |⟪cⱼ, T bᵢ⟫|² = ∑ᵢ∑ⱼ |⟪T† cⱼ, bᵢ⟫|² = ∑ⱼ ‖T† cⱼ‖²`

(`HilbertSchmidt.sumSq_eq_sumSq_adjoint`), and the right-hand side does not involve `b`.

## Main definitions

* `HilbertSchmidt.canonicalIndex`, `HilbertSchmidt.canonicalBasis`: a Hilbert basis of an
  arbitrary inner product space over an `RCLike` field, chosen via `Classical.choice`
  applied to `exists_hilbertBasis`.  Note that no separability hypothesis is needed on the
  pin: `exists_hilbertBasis` builds a basis indexed by a subset of the space.
* `HilbertSchmidt.sumSq T b`: the basis-relative sum of squares `∑' i, ‖T (b i)‖ₑ ^ 2`.
* `HilbertSchmidt.hsENorm T`: `(∑' i, ‖T (canonicalBasis i)‖ₑ ^ 2) ^ (1/2 : ℝ)`.
* `HilbertSchmidt.IsHilbertSchmidt T`: `hsENorm T ≠ ⊤`.
* `HilbertSchmidt.rankOne 𝕜 v a`: the rank-one operator `x ↦ ⟪v, x⟫ • a`.

## Main results

* `HilbertBasis.norm_sq_eq_tsum_norm_inner`: Parseval in norm form,
  `‖x‖² = ∑' i, ‖⟪b i, x⟫‖²` (also in `ℝ≥0∞`: `HilbertBasis.enorm_sq_eq_tsum`).
* `HilbertSchmidt.sumSq_eq_sumSq_adjoint`: the adjoint flip identity.
* `HilbertSchmidt.sumSq_independent`, `HilbertSchmidt.hsENorm_eq_tsum_basis`:
  basis independence.
* `HilbertSchmidt.isHilbertSchmidt_rankOne`: rank-one operators are Hilbert–Schmidt.

## Possible extensions

* `IsHilbertSchmidt ⇒ IsCompactOperator` (truncate onto finite basis subsets and estimate
  the operator norm of the tail by the tail sum of squares).
* The eventual type-synonym packaging `HilbertSchmidt 𝕜 E F` (mathlib PR #41477 design).
-/

open scoped ENNReal InnerProduct InnerProductSpace

/-- The squared enorm is `ENNReal.ofReal` of the squared norm. -/
theorem enorm_sq_eq_ofReal {G : Type*} [NormedAddCommGroup G] (v : G) :
    ‖v‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  simp

namespace HilbertBasis

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The inner-product summand identity behind Parseval:
`⟪x, b i⟫ * ⟪b i, x⟫ = (‖⟪b i, x⟫‖ ^ 2 : 𝕜)`. -/
theorem inner_mul_inner_eq_norm_sq {ι : Type*} (b : HilbertBasis ι 𝕜 E) (x : E) (i : ι) :
    ⟪x, b i⟫_𝕜 * ⟪b i, x⟫_𝕜 = ((‖⟪b i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← inner_conj_symm x (b i), RCLike.conj_mul]
  push_cast
  ring

/-- Parseval's identity in norm form: `‖x‖² = ∑' i, ‖⟪b i, x⟫‖²`. -/
theorem norm_sq_eq_tsum_norm_inner {ι : Type*} (b : HilbertBasis ι 𝕜 E) (x : E) :
    ‖x‖ ^ 2 = ∑' i, ‖⟪b i, x⟫_𝕜‖ ^ 2 := by
  have hsum : Summable fun i => ((‖⟪b i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) :=
    (HilbertBasis.summable_inner_mul_inner b x x).congr (inner_mul_inner_eq_norm_sq b x)
  have h := HilbertBasis.tsum_inner_mul_inner b x x
  rw [tsum_congr (inner_mul_inner_eq_norm_sq b x), ← RCLike.ofReal_tsum] at h
  have h' := congrArg RCLike.re h
  rw [RCLike.ofReal_re, inner_self_eq_norm_sq] at h'
  exact h'.symm

/-- The squared norms of the inner products against a Hilbert basis are summable. -/
theorem summable_norm_inner_sq {ι : Type*} (b : HilbertBasis ι 𝕜 E) (x : E) :
    Summable fun i => ‖⟪b i, x⟫_𝕜‖ ^ 2 :=
  (RCLike.summable_ofReal 𝕜).1
    ((HilbertBasis.summable_inner_mul_inner b x x).congr (inner_mul_inner_eq_norm_sq b x))

/-- Parseval's identity in `ℝ≥0∞`: `∑' i, ‖⟪b i, x⟫‖ₑ² = ‖x‖ₑ²`. -/
theorem enorm_sq_eq_tsum {ι : Type*} (b : HilbertBasis ι 𝕜 E) (x : E) :
    ∑' i, ‖⟪b i, x⟫_𝕜‖ₑ ^ 2 = ‖x‖ₑ ^ 2 := by
  calc ∑' i, ‖⟪b i, x⟫_𝕜‖ₑ ^ 2
      = ∑' i, ENNReal.ofReal (‖⟪b i, x⟫_𝕜‖ ^ 2) := tsum_congr fun i => enorm_sq_eq_ofReal _
    _ = ENNReal.ofReal (∑' i, ‖⟪b i, x⟫_𝕜‖ ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
          (HilbertBasis.summable_norm_inner_sq b x)).symm
    _ = ENNReal.ofReal (‖x‖ ^ 2) := by rw [HilbertBasis.norm_sq_eq_tsum_norm_inner b x]
    _ = ‖x‖ₑ ^ 2 := (enorm_sq_eq_ofReal x).symm

end HilbertBasis

namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The Hilbert–Schmidt sum of squares of `T` relative to a Hilbert basis `b` of the
domain. -/
noncomputable def sumSq {ι : Type*} (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) : ℝ≥0∞ :=
  ∑' i, ‖T (b i)‖ₑ ^ 2

/-- The flip identity: the Hilbert–Schmidt sum of squares of `T` relative to a Hilbert basis
`b` of the domain equals that of the adjoint `T†` relative to any Hilbert basis `c` of the
codomain. -/
theorem sumSq_eq_sumSq_adjoint [CompleteSpace E] [CompleteSpace F] {ι ι' : Type*}
    (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F) :
    sumSq T b = sumSq (T†) c := by
  have hadj : ∀ (j : ι') (i : ι), ‖⟪c j, T (b i)⟫_𝕜‖ ^ 2 = ‖⟪b i, (T†) (c j)⟫_𝕜‖ ^ 2 := by
    intro j i
    rw [← ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm ((T†) (c j)) (b i),
      RCLike.norm_conj]
  calc ∑' i, ‖T (b i)‖ₑ ^ 2
      = ∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2) := tsum_congr fun i => enorm_sq_eq_ofReal _
    _ = ∑' i, ENNReal.ofReal (∑' j, ‖⟪c j, T (b i)⟫_𝕜‖ ^ 2) :=
        tsum_congr fun i => by rw [HilbertBasis.norm_sq_eq_tsum_norm_inner c (T (b i))]
    _ = ∑' i, ∑' j, ENNReal.ofReal (‖⟪c j, T (b i)⟫_𝕜‖ ^ 2) :=
        tsum_congr fun i => ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          (HilbertBasis.summable_norm_inner_sq c (T (b i)))
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪c j, T (b i)⟫_𝕜‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪b i, (T†) (c j)⟫_𝕜‖ ^ 2) :=
        tsum_congr fun j => tsum_congr fun i => by rw [hadj j i]
    _ = ∑' j, ENNReal.ofReal (∑' i, ‖⟪b i, (T†) (c j)⟫_𝕜‖ ^ 2) :=
        tsum_congr fun j => (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
          (HilbertBasis.summable_norm_inner_sq b ((T†) (c j)))).symm
    _ = ∑' j, ENNReal.ofReal (‖(T†) (c j)‖ ^ 2) :=
        tsum_congr fun j => by rw [← HilbertBasis.norm_sq_eq_tsum_norm_inner b ((T†) (c j))]
    _ = ∑' j, ‖(T†) (c j)‖ₑ ^ 2 := tsum_congr fun j => (enorm_sq_eq_ofReal _).symm

/-- The index type of the canonical Hilbert basis of `E` (chosen via `Classical.choice`). -/
noncomputable def canonicalIndex (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] :=
  Classical.choose (exists_hilbertBasis (𝕜 := 𝕜) (E := E))

/-- The canonical Hilbert basis of an inner product space `E` over an `RCLike` field `𝕜`. -/
noncomputable def canonicalBasis (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] : HilbertBasis (canonicalIndex 𝕜 E) 𝕜 E :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis (𝕜 := 𝕜) (E := E)))

/-- Basis independence of the Hilbert–Schmidt sum of squares. -/
theorem sumSq_independent [CompleteSpace E] [CompleteSpace F] {ι ι' : Type*}
    (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) (b' : HilbertBasis ι' 𝕜 E) :
    sumSq T b = sumSq T b' := by
  rw [sumSq_eq_sumSq_adjoint T b (canonicalBasis 𝕜 F),
    sumSq_eq_sumSq_adjoint T b' (canonicalBasis 𝕜 F)]

/-- The Hilbert–Schmidt enorm of a continuous linear map between Hilbert spaces: the square
root of the sum of squared norms on a Hilbert basis.  By `hsENorm_eq_tsum_basis`, any
Hilbert basis gives the same value. -/
noncomputable def hsENorm [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F) : ℝ≥0∞ :=
  (sumSq T (canonicalBasis 𝕜 E)) ^ (1/2 : ℝ)

/-- The Hilbert–Schmidt enorm computed on an arbitrary Hilbert basis. -/
theorem hsENorm_eq_tsum_basis [CompleteSpace E] [CompleteSpace F] {ι : Type*}
    (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    hsENorm T = (∑' i, ‖T (b i)‖ₑ ^ 2) ^ (1/2 : ℝ) :=
  congrArg (· ^ (1/2 : ℝ)) (sumSq_independent T (canonicalBasis 𝕜 E) b)

/-- A continuous linear map between Hilbert spaces is Hilbert–Schmidt if its Hilbert–Schmidt
enorm is finite. -/
def IsHilbertSchmidt [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F) : Prop :=
  hsENorm T ≠ ⊤

/-- The rank-one continuous linear map `x ↦ ⟪v, x⟫ • a`. -/
noncomputable def rankOne (𝕜 : Type*) [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] (v : E) (a : F) :
    E →L[𝕜] F :=
  (innerSL 𝕜 v).smulRight a

@[simp]
theorem rankOne_apply (𝕜 : Type*) [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] (v : E) (a : F)
    (x : E) :
    rankOne 𝕜 v a x = ⟪v, x⟫_𝕜 • a := rfl

/-- The Hilbert–Schmidt sum of squares of the rank-one operator `x ↦ ⟪v, x⟫ • a` is
`‖v‖ₑ² * ‖a‖ₑ²`. -/
theorem sumSq_rankOne {ι : Type*} (b : HilbertBasis ι 𝕜 E) (v : E) (a : F) :
    sumSq (rankOne 𝕜 v a) b = ‖v‖ₑ ^ 2 * ‖a‖ₑ ^ 2 := by
  calc ∑' i, ‖rankOne 𝕜 v a (b i)‖ₑ ^ 2
      = ∑' i, ‖⟪b i, v⟫_𝕜‖ₑ ^ 2 * ‖a‖ₑ ^ 2 := tsum_congr fun i => by
        rw [rankOne_apply, enorm_smul, mul_pow, ← inner_conj_symm v (b i), RCLike.enorm_conj]
    _ = (∑' i, ‖⟪b i, v⟫_𝕜‖ₑ ^ 2) * ‖a‖ₑ ^ 2 := ENNReal.tsum_mul_right
    _ = ‖v‖ₑ ^ 2 * ‖a‖ₑ ^ 2 := by rw [HilbertBasis.enorm_sq_eq_tsum b v]

/-- Rank-one operators are Hilbert–Schmidt. -/
theorem isHilbertSchmidt_rankOne [CompleteSpace E] [CompleteSpace F] (v : E) (a : F) :
    IsHilbertSchmidt (rankOne 𝕜 v a) := by
  unfold IsHilbertSchmidt hsENorm
  apply ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  rw [sumSq_rankOne]
  refine ENNReal.mul_ne_top ?_ ?_
  · rw [enorm_sq_eq_ofReal v]
    exact ENNReal.ofReal_ne_top
  · rw [enorm_sq_eq_ofReal a]
    exact ENNReal.ofReal_ne_top

end HilbertSchmidt
