/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FredholmDet.TraceNorm
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # Trace class is closed under addition

`IsTraceClass T` (`TraceClass/`) asks for a Hilbert–Schmidt factorization `T = S ∘ R` through the
*same* space `E`, while the trace norm (`FredholmDet/TraceNorm.lean`) allows factorizations through
any auxiliary
Hilbert space.  Sums are the point where the two differ: `S₁R₁ + S₂R₂` factors naturally through
`E ⊕ E` (`HSFactorization.add`), not through `E`.

**Main theorem** (`IsTraceClass.add`): trace-class operators are closed under addition.

## Proof

Split on the dimension of `E`, measured by the canonical Hilbert basis index `ι`.

* `ι` finite: every operator is Hilbert–Schmidt (`isHilbertSchmidt_of_finite`), so
  `A + D = (A + D) ∘ id` is trace class.
* `ι` infinite: `ι ⊕ ι ≃ ι` (cardinal arithmetic), and the summand-adapted orthonormal family
  `(bᵢ, 0), (0, bᵢ)` is a Hilbert basis of `WithLp 2 (E × E)` (`exists_prod_self_equiv`), so
  `WithLp 2 (E × E) ≃ₗᵢ E`; transporting the `E ⊕ E` factorization of `HSFactorization.add`
  along it gives a factorization through `E` (`isTraceClass_of_factor_equiv`).

Also collected here: the two-sided bounded ideal property of Hilbert–Schmidt maps between
different spaces (`IsHilbertSchmidt.sandwich`) and the extensionality lemma `wlp_ext` for
`WithLp 2 (E × F)`.
-/

open scoped ENNReal NNReal InnerProductSpace

universe u

namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]

section Ideal

variable {E₁ E₂ F₁ F₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]

/-- Two-sided bounded ideal property of Hilbert–Schmidt maps between possibly different
Hilbert spaces: `L ∘ X ∘ R` is Hilbert–Schmidt when `X` is. -/
theorem IsHilbertSchmidt.sandwich {X : E₂ →L[𝕜] F₁} (hX : IsHilbertSchmidt X)
    (L : F₁ →L[𝕜] F₂) (R : E₁ →L[𝕜] E₂) : IsHilbertSchmidt (L ∘L X ∘L R) := by
  unfold IsHilbertSchmidt
  have h1 := hsENorm_comp_left_le L (X ∘L R)
  have h2 := hsENorm_comp_right_le X R
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top enorm_ne_top
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top hX enorm_ne_top) h2)) h1

/-- Left bounded composition of a Hilbert–Schmidt map (different spaces). -/
theorem IsHilbertSchmidt.comp_left' {X : E₁ →L[𝕜] F₁} (hX : IsHilbertSchmidt X)
    (L : F₁ →L[𝕜] F₂) : IsHilbertSchmidt (L ∘L X) := by
  simpa using hX.sandwich L (ContinuousLinearMap.id 𝕜 E₁)

/-- Right bounded composition of a Hilbert–Schmidt map (different spaces). -/
theorem IsHilbertSchmidt.comp_right' {X : E₂ →L[𝕜] F₁} (hX : IsHilbertSchmidt X)
    (R : E₁ →L[𝕜] E₂) : IsHilbertSchmidt (X ∘L R) := by
  simpa using hX.sandwich (ContinuousLinearMap.id 𝕜 F₁) R

end Ideal

section Ext

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

omit [NormedAddCommGroup E] [NormedAddCommGroup F] in
/-- Extensionality for `WithLp 2 (E × F)`. -/
theorem wlp_ext {E F : Type*} [AddCommGroup E] [AddCommGroup F] {v w : WithLp 2 (E × F)}
    (h1 : v.fst = w.fst) (h2 : v.snd = w.snd) : v = w := by
  cases v with
  | toLp a => cases w with
    | toLp b => exact congrArg (WithLp.toLp 2) (Prod.ext h1 h2)

end Ext

section Add

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- An operator with a Hilbert–Schmidt factorization through a space isometric to `E` is trace
class: `T = L R = (L V⁻¹)(V R)`. -/
theorem isTraceClass_of_factor_equiv {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [CompleteSpace K] {T : E →L[𝕜] E} {L : K →L[𝕜] E} {R : E →L[𝕜] K}
    (hL : IsHilbertSchmidt L) (hR : IsHilbertSchmidt R) (hT : T = L ∘L R)
    (V : K ≃ₗᵢ[𝕜] E) : IsTraceClass T := by
  refine ⟨L ∘L (V.symm.toContinuousLinearEquiv : E →L[𝕜] K),
    (V.toContinuousLinearEquiv : K →L[𝕜] E) ∘L R, hL.comp_right' _, hR.comp_left' _, ?_⟩
  ext x
  simp [hT]

/-- In finite dimension (finite canonical index) every operator is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_of_finite {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F] [Finite (canonicalIndex 𝕜 E)] (T : E →L[𝕜] F) : IsHilbertSchmidt T := by
  have : Fintype (canonicalIndex 𝕜 E) := Fintype.ofFinite _
  unfold IsHilbertSchmidt hsENorm sumSq
  refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top enorm_ne_top

/-- In infinite dimension, `E ⊕ E ≅ E` isometrically: the summand-adapted orthonormal family is a
Hilbert basis of `WithLp 2 (E × E)` indexed (after `ι ⊕ ι ≃ ι`) by the canonical index of `E`. -/
theorem exists_prod_self_equiv [Infinite (canonicalIndex 𝕜 E)] :
    Nonempty (WithLp 2 (E × E) ≃ₗᵢ[𝕜] E) := by
  classical
  set ι := canonicalIndex 𝕜 E
  set b := canonicalBasis 𝕜 E
  obtain ⟨e⟩ : Nonempty (ι ≃ ι ⊕ ι) := by
    apply Cardinal.eq.1
    rw [Cardinal.mk_sum, Cardinal.lift_id,
      Cardinal.add_eq_self (Cardinal.infinite_iff.1 inferInstance)]
  let c₀ : ι ⊕ ι → WithLp 2 (E × E) :=
    Sum.elim (fun i => WithLp.toLp 2 (b i, 0)) (fun i => WithLp.toLp 2 (0, b i))
  have hon₀ : Orthonormal 𝕜 c₀ := by
    rw [orthonormal_iff_ite]
    have hb := orthonormal_iff_ite.1 b.orthonormal
    rintro (i | i) (j | j) <;> by_cases hij : i = j <;> simp [c₀, hb, hij, b.orthonormal.1 j]
  have hon : Orthonormal 𝕜 (c₀ ∘ e) := hon₀.comp e e.injective
  have hsp : (Submodule.span 𝕜 (Set.range (c₀ ∘ e)))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hj : ∀ j, ⟪c₀ j, x⟫_𝕜 = 0 := fun j =>
      Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range.2 ⟨e.symm j, by simp⟩) :
          c₀ j ∈ Submodule.span 𝕜 (Set.range (c₀ ∘ e))) hx
    have hz : ∀ y : E, (∀ i, ⟪b i, y⟫_𝕜 = 0) → y = 0 := fun y hy => by
      have h := HilbertBasis.norm_sq_eq_tsum_norm_inner b y
      simp only [hy, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        tsum_zero, pow_eq_zero_iff, norm_eq_zero] at h
      exact h
    refine wlp_ext (hz _ fun i => ?_) (hz _ fun i => ?_)
    · simpa [c₀] using hj (Sum.inl i)
    · simpa [c₀] using hj (Sum.inr i)
  exact ⟨(HilbertBasis.mkOfOrthogonalEqBot hon hsp).repr.trans b.repr.symm⟩

/-- **Trace class is closed under addition.** -/
theorem IsTraceClass.add {A D : E →L[𝕜] E} (hA : IsTraceClass A) (hD : IsTraceClass D) :
    IsTraceClass (A + D) := by
  rcases finite_or_infinite (canonicalIndex 𝕜 E) with h | h
  · exact ⟨A + D, ContinuousLinearMap.id 𝕜 E, isHilbertSchmidt_of_finite _,
      isHilbertSchmidt_of_finite _, by ext; simp⟩
  · obtain ⟨V⟩ := exists_prod_self_equiv (𝕜 := 𝕜) (E := E)
    obtain ⟨S₁, T₁, h₁, h₁', rfl⟩ := hA
    obtain ⟨S₂, T₂, h₂, h₂', rfl⟩ := hD
    let f := (HSFactorization.ofComp S₁ T₁ h₁ h₁').add (HSFactorization.ofComp S₂ T₂ h₂ h₂')
    exact isTraceClass_of_factor_equiv f.isHilbertSchmidt_left f.isHilbertSchmidt_right
      f.eq_comp V

/-- Trace class is closed under subtraction. -/
theorem IsTraceClass.sub {A D : E →L[𝕜] E} (hA : IsTraceClass A) (hD : IsTraceClass D) :
    IsTraceClass (A - D) := by
  obtain ⟨S, T, hS, hT, rfl⟩ := hD
  rw [sub_eq_add_neg]
  refine hA.add ⟨-S, T, hS.neg, hT, ?_⟩
  ext x
  simp

end Add

end HilbertSchmidt
