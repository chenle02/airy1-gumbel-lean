/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TraceClass.FredholmOne
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # The trace norm

For `A : E →L[𝕜] E` on a Hilbert space `E : Type u` over an `RCLike` field we define the
**trace norm**

  `‖A‖₁ := inf { (‖B‖₂² + ‖C‖₂²) / 2 : A = B ∘ C, C : E → F, B : F → E Hilbert–Schmidt }`,

the infimum running over Hilbert–Schmidt factorizations through **any** Hilbert space
`F : Type u` (`HSFactorization A`).  `traceENorm A : ℝ≥0∞` is the infimum (`⊤` if `A` has no
such factorization) and `traceNorm A := (traceENorm A).toReal`.

## Definition choice

Three candidate definitions were considered:

* **sup form** `sup |∑ᵢ ⟪fᵢ, A eᵢ⟫|` over pairs of orthonormal families.  The triangle
  inequality is free, but the link to contrib's `IsTraceClass` (a factorization `A = B ∘ C`
  with Hilbert–Schmidt `B, C : E → E`) and the Hadamard weights needed by the determinant
  bound `|det(1 − A)| ≤ exp ‖A‖₁` both require a polar decomposition / singular-value
  decomposition, which is not available at the Mathlib pin.
* **inf over factorizations through `E` itself** (contrib's `IsTraceClass` shape).  The link
  to `IsTraceClass` is free, but the triangle inequality needs a common factorization of
  `A + D`, i.e. an isometric copy of `E ⊕ E` inside `E`; this fails in finite dimension and
  needs cardinal arithmetic on Hilbert bases in infinite dimension.
* **inf over factorizations through an arbitrary auxiliary space** — CHOSEN.  Factorizations
  through `F₁` and `F₂` combine to one through `WithLp 2 (F₁ × F₂)`
  (`HSFactorization.add`), and the AM–GM cost `(‖B‖₂² + ‖C‖₂²)/2` is *additive* under that
  combination, so the triangle inequality is a one-line infimum argument
  (`traceENorm_add_le`).  The cost is also exactly the Hadamard weight sum
  `∑ᵢ (‖B† bᵢ‖² + ‖C bᵢ‖²)/2 ≥ ∑ᵢ ‖B† bᵢ‖ ‖C bᵢ‖`, in **any** Hilbert basis
  `b` (arbitrary, possibly uncountable index type), which is what the determinant bounds of
  `FredholmDet/SimonBound.lean` consume.  The quantification over `F : Type u` is a structure
  field (`HSFactorization`), so no choice of a universal auxiliary space is needed.

The value agrees with the classical trace norm `∑ sₙ(A)` (Simon, *Trace Ideals*, 2nd ed.,
Thm 2.7 / (2.4): `‖BC‖₁ ≤ ‖B‖₂‖C‖₂` with equality at `B = U|A|^{1/2}, C = |A|^{1/2}`); that
identification is **not** formalized here (it needs the polar decomposition).

## Main results

* `traceENorm_add_le`: triangle inequality; `traceENorm_smul_le`, `traceENorm_neg`.
* `traceENorm_comp_le`: `‖BC‖₁ ≤ ‖B‖₂ ‖C‖₂` for Hilbert–Schmidt `B : F → E`, `C : E → F`
  (by rescaling a factorization, `HSFactorization.rescale`); `traceNorm_comp_le` for
  contrib's real `hsNorm`.
* `traceENorm_comp_left_le`, `traceENorm_comp_right_le`: the ideal property
  `‖XA‖₁ ≤ ‖X‖ ‖A‖₁`, `‖AX‖₁ ≤ ‖A‖₁ ‖X‖`.
* `hsENorm_le_traceENorm`, `opENorm_le_traceENorm`: `‖A‖₂ ≤ ‖A‖₁`, `‖A‖ ≤ ‖A‖₁`.
* `norm_tsum_inner_le_traceNorm`, `norm_trace_le_traceNorm`: `|∑ᵢ ⟪bᵢ, A bᵢ⟫| ≤ ‖A‖₁` in any
  Hilbert basis, in particular `|tr A| ≤ ‖A‖₁`.
* `IsTraceClass.traceENorm_ne_top`: contrib's trace-class operators have finite trace norm.
  The converse (a factorization through some `F` yields one through `E`) is **not** proved:
  it needs the polar decomposition.  Nothing downstream needs it: the determinant bounds of
  `SimonBound.lean` are stated under `traceENorm A ≠ ⊤`, which is the weaker hypothesis.
-/

open Filter Topology
open scoped ENNReal NNReal InnerProduct InnerProductSpace

universe u

namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]

section General

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The squared Hilbert–Schmidt enorm as a sum over an arbitrary Hilbert basis. -/
theorem hsENorm_sq_eq_tsum (T : E →L[𝕜] F) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    hsENorm T ^ 2 = ∑' i, ‖T (b i)‖ₑ ^ 2 := by
  rw [hsENorm_eq_tsum_basis T b, rpow_half_sq]

/-- The adjoint preserves the Hilbert–Schmidt enorm (maps between two spaces). -/
theorem hsENorm_adjoint_eq (T : E →L[𝕜] F) : hsENorm (T†) = hsENorm T := by
  unfold hsENorm
  rw [← sumSq_eq_sumSq_adjoint T (canonicalBasis 𝕜 E) (canonicalBasis 𝕜 F)]

/-- The adjoint of a Hilbert–Schmidt map between two spaces is Hilbert–Schmidt. -/
theorem IsHilbertSchmidt.adjoint' {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (T†) := by
  unfold IsHilbertSchmidt
  rw [hsENorm_adjoint_eq]
  exact hT

/-- The squared norms of the basis images of a Hilbert–Schmidt map are summable. -/
theorem summable_norm_sq_of_hs {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) : Summable fun i => ‖T (b i)‖ ^ 2 := by
  have hfin : (∑' i, ‖T (b i)‖ₑ ^ 2) ≠ ⊤ := by
    rw [← hsENorm_sq_eq_tsum T b]
    exact ENNReal.pow_ne_top hT
  exact (ENNReal.summable_toReal hfin).congr fun i => by
    rw [enorm_sq_eq_ofReal, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- The squared Hilbert–Schmidt enorm of a Hilbert–Schmidt map as a real basis sum. -/
theorem hsENorm_sq_eq_ofReal {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) : hsENorm T ^ 2 = ENNReal.ofReal (∑' i, ‖T (b i)‖ ^ 2) := by
  rw [hsENorm_sq_eq_tsum T b, ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
    (summable_norm_sq_of_hs hT b)]
  exact tsum_congr fun i => enorm_sq_eq_ofReal _

/-- Homogeneity of the Hilbert–Schmidt enorm. -/
theorem hsENorm_smul (c : 𝕜) (T : E →L[𝕜] F) : hsENorm (c • T) = ‖c‖ₑ * hsENorm T := by
  have h : sumSq (c • T) (canonicalBasis 𝕜 E) = ‖c‖ₑ ^ 2 * sumSq T (canonicalBasis 𝕜 E) := by
    unfold sumSq
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [ContinuousLinearMap.smul_apply, enorm_smul, mul_pow]
  unfold hsENorm
  rw [h, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), rpow_half_sq']

/-- The zero map has Hilbert–Schmidt enorm `0`. -/
theorem hsENorm_zero' : hsENorm (0 : E →L[𝕜] F) = 0 := by
  simpa using hsENorm_smul (0 : 𝕜) (0 : E →L[𝕜] F)

/-- Composing on the left by a bounded map: `‖S T‖₂ ≤ ‖S‖ ‖T‖₂`. -/
theorem hsENorm_comp_left_le {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [CompleteSpace G] (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    hsENorm (S ∘L T) ≤ ‖S‖ₑ * hsENorm T := by
  unfold hsENorm
  calc (sumSq (S ∘L T) (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ)
      ≤ (‖S‖ₑ ^ 2 * sumSq T (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (sumSq_comp_le S T _) (by norm_num)
    _ = ‖S‖ₑ * (sumSq T (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), rpow_half_sq']

/-- Composing on the right by a bounded map: `‖S T‖₂ ≤ ‖S‖₂ ‖T‖`. -/
theorem hsENorm_comp_right_le {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [CompleteSpace G] (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    hsENorm (S ∘L T) ≤ hsENorm S * ‖T‖ₑ := by
  unfold hsENorm
  calc (sumSq (S ∘L T) (canonicalBasis 𝕜 E)) ^ (1 / 2 : ℝ)
      ≤ (‖T‖ₑ ^ 2 * sumSq S (canonicalBasis 𝕜 F)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (sumSq_comp_le_right S T _ _) (by norm_num)
    _ = (sumSq S (canonicalBasis 𝕜 F)) ^ (1 / 2 : ℝ) * ‖T‖ₑ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), rpow_half_sq',
          mul_comm]

/-- The operator enorm is bounded by the Hilbert–Schmidt enorm (maps between two spaces). -/
theorem opENorm_le_hsENorm (T : E →L[𝕜] F) : ‖T‖ₑ ≤ hsENorm T := by
  apply ContinuousLinearMap.opENorm_le_bound
  intro x
  set c := canonicalBasis 𝕜 F
  have key : ‖T x‖ₑ ^ 2 ≤ sumSq T (canonicalBasis 𝕜 E) * ‖x‖ₑ ^ 2 := by
    calc ‖T x‖ₑ ^ 2 = ∑' i, ‖⟪c i, T x⟫_𝕜‖ₑ ^ 2 := (HilbertBasis.enorm_sq_eq_tsum c (T x)).symm
      _ = ∑' i, ‖⟪(T†) (c i), x⟫_𝕜‖ₑ ^ 2 := tsum_congr fun i => by
          rw [ContinuousLinearMap.adjoint_inner_left]
      _ ≤ ∑' i, (‖(T†) (c i)‖ₑ * ‖x‖ₑ) ^ 2 := ENNReal.tsum_le_tsum fun i =>
          pow_le_pow_left' (enorm_inner_le_enorm _ _) 2
      _ = ∑' i, ‖(T†) (c i)‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := tsum_congr fun i => mul_pow _ _ _
      _ = sumSq (T†) c * ‖x‖ₑ ^ 2 := ENNReal.tsum_mul_right
      _ = sumSq T (canonicalBasis 𝕜 E) * ‖x‖ₑ ^ 2 := by
          rw [← sumSq_eq_sumSq_adjoint T (canonicalBasis 𝕜 E) c]
  have h := ENNReal.rpow_le_rpow key (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [rpow_half_sq', ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    rpow_half_sq'] at h
  exact h

/-- Submultiplicativity through an auxiliary space: `‖B C‖₂ ≤ ‖B‖₂ ‖C‖₂`. -/
theorem hsENorm_comp_le_hsENorm {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [CompleteSpace G] (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    hsENorm (S ∘L T) ≤ hsENorm S * hsENorm T :=
  (hsENorm_comp_left_le S T).trans (mul_le_mul_left (opENorm_le_hsENorm S) _)

end General

/-- AM–GM in `ℝ≥0∞`: `a b ≤ (a² + b²) / 2`. -/
theorem ennreal_mul_le_add_sq_div_two (a b : ℝ≥0∞) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · rcases eq_or_ne b 0 with rfl | hb
    · simp
    · simp [ENNReal.top_pow two_ne_zero, ENNReal.top_div_of_ne_top]
  rcases eq_or_ne b ⊤ with rfl | hb
  · rcases eq_or_ne a 0 with rfl | ha'
    · simp
    · simp [ENNReal.top_pow two_ne_zero, ENNReal.top_div_of_ne_top]
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
  have h : (a : ℝ) * b * 2 ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℝ) - b)]
  have h' : a * b * 2 ≤ a ^ 2 + b ^ 2 := by exact_mod_cast h
  exact_mod_cast h'

section TraceNorm

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A **Hilbert–Schmidt factorization** `A = B ∘L C` of `A : E →L[𝕜] E` through an auxiliary
Hilbert space `F` in the universe of `E`, with `B : F → E` and `C : E → F` Hilbert–Schmidt. -/
structure HSFactorization (A : E →L[𝕜] E) where
  /-- The auxiliary Hilbert space. -/
  F : Type u
  [instNormedAddCommGroup : NormedAddCommGroup F]
  [instInnerProductSpace : InnerProductSpace 𝕜 F]
  [instCompleteSpace : CompleteSpace F]
  /-- The left factor `B : F → E`. -/
  left : F →L[𝕜] E
  /-- The right factor `C : E → F`. -/
  right : E →L[𝕜] F
  isHilbertSchmidt_left : IsHilbertSchmidt left
  isHilbertSchmidt_right : IsHilbertSchmidt right
  eq_comp : A = left ∘L right

attribute [instance] HSFactorization.instNormedAddCommGroup
  HSFactorization.instInnerProductSpace HSFactorization.instCompleteSpace

namespace HSFactorization

variable {A D : E →L[𝕜] E}

/-- The AM–GM cost `(‖B‖₂² + ‖C‖₂²) / 2` of a factorization. -/
noncomputable def cost (f : HSFactorization A) : ℝ≥0∞ :=
  (hsENorm f.left ^ 2 + hsENorm f.right ^ 2) / 2

/-- The cost computed in a Hilbert basis `b` of `E`, as a real number:
`(∑ᵢ ‖B† bᵢ‖² + ∑ᵢ ‖C bᵢ‖²) / 2`. -/
noncomputable def costIn (f : HSFactorization A) {ι : Type*} (b : HilbertBasis ι 𝕜 E) : ℝ :=
  ((∑' i, ‖(f.left†) (b i)‖ ^ 2) + ∑' i, ‖f.right (b i)‖ ^ 2) / 2

theorem apply_eq (f : HSFactorization A) (x : E) : A x = f.left (f.right x) :=
  DFunLike.congr_fun f.eq_comp x

/-- Matrix elements through a factorization: `⟪x, A y⟫ = ⟪B† x, C y⟫`. -/
theorem inner_apply (f : HSFactorization A) (x y : E) :
    ⟪x, A y⟫_𝕜 = ⟪(f.left†) x, f.right y⟫_𝕜 := by
  rw [f.apply_eq, ContinuousLinearMap.adjoint_inner_left]

theorem summable_left (f : HSFactorization A) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    Summable fun i => ‖(f.left†) (b i)‖ ^ 2 :=
  summable_norm_sq_of_hs f.isHilbertSchmidt_left.adjoint' b

theorem summable_right (f : HSFactorization A) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    Summable fun i => ‖f.right (b i)‖ ^ 2 :=
  summable_norm_sq_of_hs f.isHilbertSchmidt_right b

theorem costIn_nonneg (f : HSFactorization A) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    0 ≤ f.costIn b := by
  unfold costIn
  have h1 : 0 ≤ ∑' i, ‖(f.left†) (b i)‖ ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have h2 : 0 ≤ ∑' i, ‖f.right (b i)‖ ^ 2 := tsum_nonneg fun i => sq_nonneg _
  positivity

/-- The cost does not depend on the basis used to compute it. -/
theorem cost_eq_ofReal (f : HSFactorization A) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    f.cost = ENNReal.ofReal (f.costIn b) := by
  unfold cost costIn
  rw [← hsENorm_adjoint_eq f.left, hsENorm_sq_eq_ofReal f.isHilbertSchmidt_left.adjoint' b,
    hsENorm_sq_eq_ofReal f.isHilbertSchmidt_right b,
    ← ENNReal.ofReal_add (tsum_nonneg fun i => sq_nonneg _) (tsum_nonneg fun i => sq_nonneg _),
    ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]

theorem cost_ne_top (f : HSFactorization A) : f.cost ≠ ⊤ := by
  rw [f.cost_eq_ofReal (canonicalBasis 𝕜 E)]
  exact ENNReal.ofReal_ne_top

/-- The factorization `B ∘L C` itself. -/
noncomputable def ofComp {F : Type u} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F] (B : F →L[𝕜] E) (C : E →L[𝕜] F) (hB : IsHilbertSchmidt B)
    (hC : IsHilbertSchmidt C) : HSFactorization (B ∘L C) where
  F := F
  left := B
  right := C
  isHilbertSchmidt_left := hB
  isHilbertSchmidt_right := hC
  eq_comp := rfl

/-- Transport a factorization along an equality of operators. -/
noncomputable def copy (f : HSFactorization A) (h : A = D) : HSFactorization D where
  F := f.F
  left := f.left
  right := f.right
  isHilbertSchmidt_left := f.isHilbertSchmidt_left
  isHilbertSchmidt_right := f.isHilbertSchmidt_right
  eq_comp := h ▸ f.eq_comp

theorem cost_copy (f : HSFactorization A) (h : A = D) : (f.copy h).cost = f.cost := rfl

/-- Rescaling a factorization: `A = (t⁻¹ B) ∘ (t C)` for real `t ≠ 0`. -/
noncomputable def rescale (f : HSFactorization A) (t : ℝ) (ht : t ≠ 0) : HSFactorization A where
  F := f.F
  left := ((t⁻¹ : ℝ) : 𝕜) • f.left
  right := ((t : ℝ) : 𝕜) • f.right
  isHilbertSchmidt_left := by
    unfold IsHilbertSchmidt
    rw [hsENorm_smul]
    exact ENNReal.mul_ne_top enorm_ne_top f.isHilbertSchmidt_left
  isHilbertSchmidt_right := by
    unfold IsHilbertSchmidt
    rw [hsENorm_smul]
    exact ENNReal.mul_ne_top enorm_ne_top f.isHilbertSchmidt_right
  eq_comp := by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
      ← RCLike.ofReal_mul, inv_mul_cancel₀ ht, RCLike.ofReal_one, one_smul]
    exact f.eq_comp

theorem costIn_rescale (f : HSFactorization A) (t : ℝ) (ht : t ≠ 0) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) :
    (f.rescale t ht).costIn b =
      ((t⁻¹) ^ 2 * ∑' i, ‖(f.left†) (b i)‖ ^ 2 + t ^ 2 * ∑' i, ‖f.right (b i)‖ ^ 2) / 2 := by
  unfold costIn
  congr 2
  · rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    show ‖((((t⁻¹ : ℝ) : 𝕜) • f.left)†) (b i)‖ ^ 2 = _
    rw [map_smulₛₗ, ContinuousLinearMap.smul_apply, norm_smul, RCLike.conj_ofReal,
      RCLike.norm_ofReal, mul_pow, sq_abs]
  · rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    show ‖(((t : ℝ) : 𝕜) • f.right) (b i)‖ ^ 2 = _
    rw [ContinuousLinearMap.smul_apply, norm_smul, RCLike.norm_ofReal, mul_pow, sq_abs]

end HSFactorization

/-- **Trace norm** (`ℝ≥0∞`-valued): the infimum of the AM–GM cost `(‖B‖₂² + ‖C‖₂²)/2` over
all Hilbert–Schmidt factorizations `A = B ∘L C` through Hilbert spaces in the universe of `E`;
`⊤` if there is none. -/
noncomputable def traceENorm (A : E →L[𝕜] E) : ℝ≥0∞ :=
  ⨅ f : HSFactorization A, f.cost

/-- **Trace norm** `‖A‖₁` (real-valued; junk `0` when `traceENorm A = ⊤`). -/
noncomputable def traceNorm (A : E →L[𝕜] E) : ℝ :=
  (traceENorm A).toReal

variable {A D : E →L[𝕜] E}

theorem traceENorm_le_cost (f : HSFactorization A) : traceENorm A ≤ f.cost :=
  iInf_le (fun f : HSFactorization A => f.cost) f

theorem traceENorm_ne_top_of_factorization (f : HSFactorization A) : traceENorm A ≠ ⊤ :=
  ne_top_of_le_ne_top f.cost_ne_top (traceENorm_le_cost f)

theorem traceNorm_nonneg (A : E →L[𝕜] E) : 0 ≤ traceNorm A := ENNReal.toReal_nonneg

theorem traceENorm_eq_ofReal (hA : traceENorm A ≠ ⊤) :
    traceENorm A = ENNReal.ofReal (traceNorm A) :=
  (ENNReal.ofReal_toReal hA).symm

/-- Every factorization bounds the trace norm, in any basis. -/
theorem traceNorm_le_costIn (f : HSFactorization A) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    traceNorm A ≤ f.costIn b :=
  ENNReal.toReal_le_of_le_ofReal (f.costIn_nonneg b)
    ((traceENorm_le_cost f).trans (f.cost_eq_ofReal b).le)

/-- **Approximate minimizers**: for finite trace norm and `ε > 0` there is a factorization
whose cost (in any prescribed basis) is within `ε` of `‖A‖₁`. -/
theorem exists_costIn_lt (hA : traceENorm A ≠ ⊤) {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    {ε : ℝ} (hε : 0 < ε) : ∃ f : HSFactorization A, f.costIn b < traceNorm A + ε := by
  have hpos : 0 < traceNorm A + ε := by linarith [traceNorm_nonneg A]
  have hlt : (⨅ f : HSFactorization A, f.cost) < ENNReal.ofReal (traceNorm A + ε) := by
    change traceENorm A < _
    rw [traceENorm_eq_ofReal hA]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by linarith)
  obtain ⟨f, hf⟩ := iInf_lt_iff.1 hlt
  refine ⟨f, ?_⟩
  rw [f.cost_eq_ofReal b] at hf
  exact (ENNReal.ofReal_lt_ofReal_iff hpos).1 hf

/-- `‖0‖₁ = 0`. -/
theorem traceENorm_zero : traceENorm (0 : E →L[𝕜] E) = 0 := by
  have hz : IsHilbertSchmidt (0 : E →L[𝕜] E) := by
    unfold IsHilbertSchmidt
    rw [hsENorm_zero']
    exact ENNReal.zero_ne_top
  let f := (HSFactorization.ofComp (0 : E →L[𝕜] E) (0 : E →L[𝕜] E) hz hz).copy
    (ContinuousLinearMap.zero_comp _)
  refine le_antisymm ((traceENorm_le_cost f).trans (le_of_eq ?_)) zero_le
  show (hsENorm (0 : E →L[𝕜] E) ^ 2 + hsENorm (0 : E →L[𝕜] E) ^ 2) / 2 = 0
  simp [hsENorm_zero']

theorem traceNorm_zero : traceNorm (0 : E →L[𝕜] E) = 0 := by
  simp [traceNorm, traceENorm_zero]

section Joint

variable {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

/-- The column map `x ↦ (S x, T x)` into the `L²` product. -/
noncomputable def jointCol (S : E →L[𝕜] F₁) (T : E →L[𝕜] F₂) :
    E →L[𝕜] WithLp 2 (F₁ × F₂) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 F₁ F₂).symm.toContinuousLinearMap ∘L S.prod T

omit [CompleteSpace E] in
@[simp]
theorem jointCol_apply (S : E →L[𝕜] F₁) (T : E →L[𝕜] F₂) (x : E) :
    jointCol S T x = WithLp.toLp 2 (S x, T x) := rfl

omit [InnerProductSpace 𝕜 F₁] [InnerProductSpace 𝕜 F₂] in
theorem norm_toLp_sq (a : F₁) (c : F₂) :
    ‖WithLp.toLp 2 (a, c)‖ ^ 2 = ‖a‖ ^ 2 + ‖c‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

omit [InnerProductSpace 𝕜 F₁] [InnerProductSpace 𝕜 F₂] in
theorem enorm_toLp_sq (a : F₁) (c : F₂) :
    ‖WithLp.toLp 2 (a, c)‖ₑ ^ 2 = ‖a‖ₑ ^ 2 + ‖c‖ₑ ^ 2 := by
  rw [enorm_sq_eq_ofReal, norm_toLp_sq, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← enorm_sq_eq_ofReal, ← enorm_sq_eq_ofReal]

theorem inner_toLp (a a' : F₁) (c c' : F₂) :
    ⟪WithLp.toLp 2 (a, c), WithLp.toLp 2 (a', c')⟫_𝕜 = ⟪a, a'⟫_𝕜 + ⟪c, c'⟫_𝕜 := rfl

omit [CompleteSpace E] in
theorem sumSq_jointCol (S : E →L[𝕜] F₁) (T : E →L[𝕜] F₂) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) : sumSq (jointCol S T) b = sumSq S b + sumSq T b := by
  unfold sumSq
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun i => enorm_toLp_sq _ _

theorem hsENorm_jointCol_sq [CompleteSpace F₁] [CompleteSpace F₂] (S : E →L[𝕜] F₁)
    (T : E →L[𝕜] F₂) : hsENorm (jointCol S T) ^ 2 = hsENorm S ^ 2 + hsENorm T ^ 2 := by
  rw [hsENorm_sq_eq_tsum _ (canonicalBasis 𝕜 E), hsENorm_sq_eq_tsum S (canonicalBasis 𝕜 E),
    hsENorm_sq_eq_tsum T (canonicalBasis 𝕜 E)]
  exact sumSq_jointCol S T _

end Joint

theorem ne_top_of_sq_ne_top {x : ℝ≥0∞} (hx : x ^ 2 ≠ ⊤) : x ≠ ⊤ := by
  intro h
  apply hx
  rw [h]
  exact ENNReal.top_pow two_ne_zero

namespace HSFactorization

/-- **Combining two factorizations**: `A = B₁C₁` through `F₁` and `D = B₂C₂` through `F₂`
give `A + D = [B₁ B₂] ∘ (C₁, C₂)` through `WithLp 2 (F₁ × F₂)`. -/
noncomputable def add (f₁ : HSFactorization A) (f₂ : HSFactorization D) :
    HSFactorization (A + D) where
  F := WithLp 2 (f₁.F × f₂.F)
  left := (jointCol (f₁.left†) (f₂.left†))†
  right := jointCol f₁.right f₂.right
  isHilbertSchmidt_left := by
    unfold IsHilbertSchmidt
    rw [hsENorm_adjoint_eq]
    apply ne_top_of_sq_ne_top
    rw [hsENorm_jointCol_sq, hsENorm_adjoint_eq, hsENorm_adjoint_eq]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top f₁.isHilbertSchmidt_left,
      ENNReal.pow_ne_top f₂.isHilbertSchmidt_left⟩
  isHilbertSchmidt_right := by
    unfold IsHilbertSchmidt
    apply ne_top_of_sq_ne_top
    rw [hsENorm_jointCol_sq]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top f₁.isHilbertSchmidt_right,
      ENNReal.pow_ne_top f₂.isHilbertSchmidt_right⟩
  eq_comp := by
    ext x
    refine ext_inner_left 𝕜 fun y => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      jointCol_apply, jointCol_apply, inner_toLp, ContinuousLinearMap.add_apply,
      inner_add_right, f₁.inner_apply, f₂.inner_apply]

/-- The cost is additive under combination. -/
theorem cost_add (f₁ : HSFactorization A) (f₂ : HSFactorization D) :
    (f₁.add f₂).cost = f₁.cost + f₂.cost := by
  show (hsENorm ((jointCol (f₁.left†) (f₂.left†))†) ^ 2 +
      hsENorm (jointCol f₁.right f₂.right) ^ 2) / 2 = _
  rw [hsENorm_adjoint_eq, hsENorm_jointCol_sq, hsENorm_jointCol_sq, hsENorm_adjoint_eq,
    hsENorm_adjoint_eq, add_add_add_comm, ENNReal.add_div]
  rfl

end HSFactorization

/-- **Triangle inequality** for the trace norm. -/
theorem traceENorm_add_le (A D : E →L[𝕜] E) :
    traceENorm (A + D) ≤ traceENorm A + traceENorm D :=
  ENNReal.le_iInf_add_iInf fun f₁ f₂ =>
    (traceENorm_le_cost (f₁.add f₂)).trans (f₁.cost_add f₂).le

theorem traceENorm_add_ne_top (hA : traceENorm A ≠ ⊤) (hD : traceENorm D ≠ ⊤) :
    traceENorm (A + D) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hA, hD⟩) (traceENorm_add_le A D)

theorem traceNorm_add_le (hA : traceENorm A ≠ ⊤) (hD : traceENorm D ≠ ⊤) :
    traceNorm (A + D) ≤ traceNorm A + traceNorm D := by
  unfold traceNorm
  rw [← ENNReal.toReal_add hA hD]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hA, hD⟩) (traceENorm_add_le A D)

/-- **`‖BC‖₁ ≤ ‖B‖₂ ‖C‖₂`** for Hilbert–Schmidt `B : F → E`, `C : E → F` (Simon, *Trace
Ideals*, Thm 2.7(c)/(2.4)).  Proof: rescaling `(B, C) ↦ (B/t, tC)` gives
`2‖BC‖₁ s ≤ P + s² Q` for every `s = t² > 0` (`P = ‖B‖₂²`, `Q = ‖C‖₂²`), whence
`‖BC‖₁² ≤ P Q`. -/
theorem traceENorm_comp_le {F : Type u} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F] {B : F →L[𝕜] E} {C : E →L[𝕜] F} (hB : IsHilbertSchmidt B)
    (hC : IsHilbertSchmidt C) : traceENorm (B ∘L C) ≤ hsENorm B * hsENorm C := by
  set f := HSFactorization.ofComp B C hB hC
  set b := canonicalBasis 𝕜 E
  set P := ∑' i, ‖(B†) (b i)‖ ^ 2 with hP
  set Q := ∑' i, ‖C (b i)‖ ^ 2 with hQ
  set X := traceNorm (B ∘L C) with hX
  have hP0 : 0 ≤ P := tsum_nonneg fun i => sq_nonneg _
  have hQ0 : 0 ≤ Q := tsum_nonneg fun i => sq_nonneg _
  have hX0 : 0 ≤ X := traceNorm_nonneg _
  have key : ∀ s : ℝ, 0 < s → 2 * X * s ≤ P + s ^ 2 * Q := by
    intro s hs
    have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
    have ht2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
    have h := traceNorm_le_costIn (f.rescale (Real.sqrt s) ht.ne') b
    rw [HSFactorization.costIn_rescale, inv_pow, ht2] at h
    change X ≤ (s⁻¹ * P + s * Q) / 2 at h
    have h2 : 2 * X * s ≤ (s⁻¹ * P + s * Q) * s := by nlinarith
    calc 2 * X * s ≤ (s⁻¹ * P + s * Q) * s := h2
      _ = P + s ^ 2 * Q := by field_simp
  have hsq : X ^ 2 ≤ P * Q := by
    rcases eq_or_lt_of_le hX0 with hX' | hX'
    · rw [← hX']; nlinarith
    rcases eq_or_lt_of_le hQ0 with hQ' | hQ'
    · exfalso
      have h := key ((P + 1) / X) (by positivity)
      rw [← hQ', mul_zero, add_zero] at h
      have : 2 * X * ((P + 1) / X) = 2 * (P + 1) := by field_simp
      linarith
    · have h := key (X / Q) (div_pos hX' hQ')
      have h' : 2 * X * (X / Q) * Q ≤ (P + (X / Q) ^ 2 * Q) * Q :=
        mul_le_mul_of_nonneg_right h hQ0
      have e1 : 2 * X * (X / Q) * Q = 2 * X ^ 2 := by field_simp
      have e2 : (P + (X / Q) ^ 2 * Q) * Q = P * Q + X ^ 2 := by field_simp
      linarith
  have hfin : traceENorm (B ∘L C) ≠ ⊤ := traceENorm_ne_top_of_factorization f
  have hBsq : hsENorm B ^ 2 = ENNReal.ofReal P := by
    rw [← hsENorm_adjoint_eq B, hsENorm_sq_eq_ofReal hB.adjoint' b]
  have hCsq : hsENorm C ^ 2 = ENNReal.ofReal Q := hsENorm_sq_eq_ofReal hC b
  have hsq' : traceENorm (B ∘L C) ^ 2 ≤ (hsENorm B * hsENorm C) ^ 2 := by
    rw [mul_pow, hBsq, hCsq, ← ENNReal.ofReal_mul hP0, traceENorm_eq_ofReal hfin,
      ← ENNReal.ofReal_pow hX0]
    exact ENNReal.ofReal_le_ofReal hsq
  have h := ENNReal.rpow_le_rpow hsq' (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [rpow_half_sq', rpow_half_sq'] at h

/-- Contrib's trace-class operators have finite trace norm. -/
theorem IsTraceClass.traceENorm_ne_top (hA : IsTraceClass A) : traceENorm A ≠ ⊤ := by
  obtain ⟨B, C, hB, hC, rfl⟩ := hA
  exact traceENorm_ne_top_of_factorization (HSFactorization.ofComp B C hB hC)

/-- `‖BC‖₁ ≤ ‖B‖₂ ‖C‖₂` with contrib's real Hilbert–Schmidt norm. -/
theorem traceNorm_comp_le {B C : E →L[𝕜] E} (hB : IsHilbertSchmidt B)
    (hC : IsHilbertSchmidt C) : traceNorm (B ∘L C) ≤ hsNorm B * hsNorm C := by
  unfold traceNorm hsNorm
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hB hC) (traceENorm_comp_le hB hC)

/-- **Left ideal property**: `‖X A‖₁ ≤ ‖X‖ ‖A‖₁`. -/
theorem traceENorm_comp_left_le (X A : E →L[𝕜] E) :
    traceENorm (X ∘L A) ≤ ‖X‖ₑ * traceENorm A := by
  rcases eq_or_ne ‖X‖ₑ 0 with h0 | h0
  · have hX : X = 0 := by
      have h1 : ‖X‖ = 0 := by rw [← toReal_enorm, h0, ENNReal.toReal_zero]
      exact norm_eq_zero.1 h1
    subst hX
    rw [ContinuousLinearMap.zero_comp, traceENorm_zero]
    exact zero_le
  show traceENorm (X ∘L A) ≤ ‖X‖ₑ * ⨅ f : HSFactorization A, f.cost
  rw [ENNReal.mul_iInf_of_ne h0 enorm_ne_top]
  refine le_iInf fun f => ?_
  have hXA : X ∘L A = (X ∘L f.left) ∘L f.right := by
    ext x
    simp [f.apply_eq]
  have hXB : IsHilbertSchmidt (X ∘L f.left) := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top enorm_ne_top f.isHilbertSchmidt_left) (hsENorm_comp_left_le X f.left)
  calc traceENorm (X ∘L A) = traceENorm ((X ∘L f.left) ∘L f.right) := by rw [hXA]
    _ ≤ hsENorm (X ∘L f.left) * hsENorm f.right :=
        traceENorm_comp_le hXB f.isHilbertSchmidt_right
    _ ≤ ‖X‖ₑ * hsENorm f.left * hsENorm f.right :=
        mul_le_mul_left (hsENorm_comp_left_le X f.left) _
    _ ≤ ‖X‖ₑ * f.cost := by
        rw [mul_assoc]
        exact mul_le_mul_right (ennreal_mul_le_add_sq_div_two _ _) _

/-- **Right ideal property**: `‖A X‖₁ ≤ ‖A‖₁ ‖X‖`. -/
theorem traceENorm_comp_right_le (A X : E →L[𝕜] E) :
    traceENorm (A ∘L X) ≤ traceENorm A * ‖X‖ₑ := by
  rcases eq_or_ne ‖X‖ₑ 0 with h0 | h0
  · have hX : X = 0 := by
      have h1 : ‖X‖ = 0 := by rw [← toReal_enorm, h0, ENNReal.toReal_zero]
      exact norm_eq_zero.1 h1
    subst hX
    rw [ContinuousLinearMap.comp_zero, traceENorm_zero]
    exact zero_le
  show traceENorm (A ∘L X) ≤ (⨅ f : HSFactorization A, f.cost) * ‖X‖ₑ
  rw [ENNReal.iInf_mul_of_ne h0 enorm_ne_top]
  refine le_iInf fun f => ?_
  have hAX : A ∘L X = f.left ∘L (f.right ∘L X) := by
    ext x
    simp [f.apply_eq]
  have hCX : IsHilbertSchmidt (f.right ∘L X) := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top f.isHilbertSchmidt_right enorm_ne_top)
    (hsENorm_comp_right_le f.right X)
  calc traceENorm (A ∘L X) = traceENorm (f.left ∘L (f.right ∘L X)) := by rw [hAX]
    _ ≤ hsENorm f.left * hsENorm (f.right ∘L X) :=
        traceENorm_comp_le f.isHilbertSchmidt_left hCX
    _ ≤ hsENorm f.left * (hsENorm f.right * ‖X‖ₑ) :=
        mul_le_mul_right (hsENorm_comp_right_le f.right X) _
    _ ≤ f.cost * ‖X‖ₑ := by
        rw [← mul_assoc]
        exact mul_le_mul_left (ennreal_mul_le_add_sq_div_two _ _) _

/-- Homogeneity bound `‖c A‖₁ ≤ |c| ‖A‖₁`. -/
theorem traceENorm_smul_le (c : 𝕜) (A : E →L[𝕜] E) :
    traceENorm (c • A) ≤ ‖c‖ₑ * traceENorm A := by
  have h : c • A = (c • ContinuousLinearMap.id 𝕜 E) ∘L A := by
    ext x
    simp
  have hid : ‖c • ContinuousLinearMap.id 𝕜 E‖ₑ ≤ ‖c‖ₑ := by
    refine ContinuousLinearMap.opENorm_le_bound _ fun x => ?_
    simp [enorm_smul]
  rw [h]
  exact (traceENorm_comp_left_le _ A).trans (mul_le_mul_left hid _)

/-- `‖−A‖₁ = ‖A‖₁`. -/
theorem traceENorm_neg (A : E →L[𝕜] E) : traceENorm (-A) = traceENorm A := by
  refine le_antisymm ?_ ?_
  · simpa using traceENorm_smul_le (-1 : 𝕜) A
  · simpa using traceENorm_smul_le (-1 : 𝕜) (-A)

theorem traceNorm_neg (A : E →L[𝕜] E) : traceNorm (-A) = traceNorm A := by
  simp [traceNorm, traceENorm_neg]

theorem traceENorm_smul_ne_top (c : 𝕜) (hA : traceENorm A ≠ ⊤) : traceENorm (c • A) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top enorm_ne_top hA) (traceENorm_smul_le c A)

theorem traceNorm_smul_le (c : 𝕜) (hA : traceENorm A ≠ ⊤) :
    traceNorm (c • A) ≤ ‖c‖ * traceNorm A := by
  unfold traceNorm
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top hA) (traceENorm_smul_le c A)
  rwa [ENNReal.toReal_mul, toReal_enorm] at h

theorem traceENorm_neg_ne_top (hA : traceENorm A ≠ ⊤) : traceENorm (-A) ≠ ⊤ := by
  rwa [traceENorm_neg]

theorem traceENorm_sub_ne_top (hA : traceENorm A ≠ ⊤) (hD : traceENorm D ≠ ⊤) :
    traceENorm (A - D) ≠ ⊤ := by
  rw [sub_eq_add_neg]
  exact traceENorm_add_ne_top hA (traceENorm_neg_ne_top hD)

theorem traceNorm_sub_le (hA : traceENorm A ≠ ⊤) (hD : traceENorm D ≠ ⊤) :
    traceNorm (A - D) ≤ traceNorm A + traceNorm D := by
  rw [sub_eq_add_neg, ← traceNorm_neg D]
  exact traceNorm_add_le hA (traceENorm_neg_ne_top hD)

theorem traceNorm_sub_comm (A D : E →L[𝕜] E) : traceNorm (A - D) = traceNorm (D - A) := by
  rw [← neg_sub, traceNorm_neg]

/-- **`‖A‖₂ ≤ ‖A‖₁`.** -/
theorem hsENorm_le_traceENorm (A : E →L[𝕜] E) : hsENorm A ≤ traceENorm A := by
  refine le_iInf fun f => ?_
  calc hsENorm A = hsENorm (f.left ∘L f.right) := congrArg hsENorm f.eq_comp
    _ ≤ hsENorm f.left * hsENorm f.right := hsENorm_comp_le_hsENorm _ _
    _ ≤ f.cost := ennreal_mul_le_add_sq_div_two _ _

/-- **`‖A‖ ≤ ‖A‖₁`.** -/
theorem opENorm_le_traceENorm (A : E →L[𝕜] E) : ‖A‖ₑ ≤ traceENorm A :=
  (opENorm_le_hsENorm A).trans (hsENorm_le_traceENorm A)

/-- Trace-norm-finite operators are Hilbert–Schmidt. -/
theorem isHilbertSchmidt_of_traceENorm_ne_top (hA : traceENorm A ≠ ⊤) : IsHilbertSchmidt A :=
  ne_top_of_le_ne_top hA (hsENorm_le_traceENorm A)

theorem hsNorm_le_traceNorm (hA : traceENorm A ≠ ⊤) : hsNorm A ≤ traceNorm A :=
  ENNReal.toReal_mono hA (hsENorm_le_traceENorm A)

theorem norm_le_traceNorm (hA : traceENorm A ≠ ⊤) : ‖A‖ ≤ traceNorm A := by
  have h := ENNReal.toReal_mono hA (opENorm_le_traceENorm A)
  rwa [toReal_enorm] at h

/-- The diagonal of a factorized operator is absolutely summable, with sum bounded by the
cost: `∑ᵢ |⟪bᵢ, A bᵢ⟫| ≤ (∑ᵢ ‖B† bᵢ‖² + ∑ᵢ ‖C bᵢ‖²)/2`. -/
theorem HSFactorization.summable_norm_inner_diag (f : HSFactorization A) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) : Summable fun i => ‖⟪b i, A (b i)⟫_𝕜‖ := by
  refine (((f.summable_left b).add (f.summable_right b)).div_const 2).of_nonneg_of_le
    (fun i => norm_nonneg _) (fun i => ?_)
  rw [f.inner_apply]
  have h := norm_inner_le_norm (𝕜 := 𝕜) ((f.left†) (b i)) (f.right (b i))
  nlinarith [sq_nonneg (‖(f.left†) (b i)‖ - ‖f.right (b i)‖)]

theorem HSFactorization.tsum_norm_inner_diag_le (f : HSFactorization A) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) : ∑' i, ‖⟪b i, A (b i)⟫_𝕜‖ ≤ f.costIn b := by
  have hs := ((f.summable_left b).add (f.summable_right b)).div_const 2
  calc ∑' i, ‖⟪b i, A (b i)⟫_𝕜‖
      ≤ ∑' i, (‖(f.left†) (b i)‖ ^ 2 + ‖f.right (b i)‖ ^ 2) / 2 :=
        Summable.tsum_le_tsum (fun i => by
          rw [f.inner_apply]
          have h := norm_inner_le_norm (𝕜 := 𝕜) ((f.left†) (b i)) (f.right (b i))
          nlinarith [sq_nonneg (‖(f.left†) (b i)‖ - ‖f.right (b i)‖)])
          (f.summable_norm_inner_diag b) hs
    _ = f.costIn b := by
        rw [tsum_div_const, Summable.tsum_add (f.summable_left b) (f.summable_right b)]
        rfl

/-- **`|∑ᵢ ⟪bᵢ, A bᵢ⟫| ≤ ‖A‖₁`** in any Hilbert basis (arbitrary index type). -/
theorem norm_tsum_inner_le_traceNorm (hA : traceENorm A ≠ ⊤) {ι : Type*}
    (b : HilbertBasis ι 𝕜 E) : ‖∑' i, ⟪b i, A (b i)⟫_𝕜‖ ≤ traceNorm A := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨f, hf⟩ := exists_costIn_lt hA b hε
  calc ‖∑' i, ⟪b i, A (b i)⟫_𝕜‖ ≤ ∑' i, ‖⟪b i, A (b i)⟫_𝕜‖ :=
        norm_tsum_le_tsum_norm (f.summable_norm_inner_diag b)
    _ ≤ f.costIn b := f.tsum_norm_inner_diag_le b
    _ < traceNorm A + ε := hf

/-- **`|tr A| ≤ ‖A‖₁`.** -/
theorem norm_trace_le_traceNorm (hA : traceENorm A ≠ ⊤) : ‖trace A‖ ≤ traceNorm A :=
  norm_tsum_inner_le_traceNorm hA (canonicalBasis 𝕜 E)

/-- `|tr A| ≤ ‖A‖₁` in `ℝ≥0∞` (no finiteness hypothesis). -/
theorem enorm_trace_le_traceENorm (A : E →L[𝕜] E) : ‖trace A‖ₑ ≤ traceENorm A := by
  rcases eq_or_ne (traceENorm A) ⊤ with h | h
  · rw [h]; exact le_top
  · rw [traceENorm_eq_ofReal h, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (norm_trace_le_traceNorm h)

end TraceNorm

end HilbertSchmidt
