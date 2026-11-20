/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FredholmDet.DiskAgreement

/-! # A rank-one witness for the entire determinant

A concrete, non-small, nondegenerate witness that the entire determinant `fredholmDet` is a genuine
entire object and is **not** the disk-only `fredholmDetOne` in disguise.

For any Hilbert basis vector `e = b i₀` put `A = 2 · |e⟩⟨e|` (`x ↦ 2⟪e, x⟫ e`).  Then `A` is
trace class, and for **every** coupling `z`

  `fredholmDet A z = 1 − 2z`,

the classical rank-one determinant.  At `z = 1/2` (on the boundary of the disk
`‖z‖‖A‖₂ < 1`, since `‖A‖₂ = 2`) the entire determinant vanishes — `1 − A/2` is the
projection onto `e^⊥`, not invertible — while `fredholmDetOne A (1/2)` is an exponential,
hence nonzero.  So the two objects genuinely differ off the disk, and the entire one gives the
correct (vanishing) value there.
-/

open scoped InnerProduct InnerProductSpace
open scoped Classical

namespace HilbertSchmidt

namespace Probe

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {ι : Type*}

/-- The rank-one witness `A = 2 |e⟩⟨e|` with `e = b i₀`. -/
noncomputable def rankTwoProj (b : HilbertBasis ι 𝕜 E) (i₀ : ι) : E →L[𝕜] E :=
  rankOne 𝕜 (b i₀) ((2 : 𝕜) • b i₀)

omit [CompleteSpace E] in
theorem inner_self_basis (b : HilbertBasis ι 𝕜 E) (i : ι) : ⟪b i, b i⟫_𝕜 = 1 := by
  rw [orthonormal_iff_ite.mp b.orthonormal, ite_eq_left rfl]

/-- The witness is trace class: `A = (2|e⟩⟨e|) ∘ (|e⟩⟨e|)`, a product of two
Hilbert–Schmidt rank-one operators. -/
theorem isTraceClass_rankTwoProj (b : HilbertBasis ι 𝕜 E) (i₀ : ι) :
    IsTraceClass (rankTwoProj b i₀) := by
  refine ⟨rankOne 𝕜 (b i₀) ((2 : 𝕜) • b i₀), rankOne 𝕜 (b i₀) (b i₀),
    isHilbertSchmidt_rankOne _ _, isHilbertSchmidt_rankOne _ _, ?_⟩
  ext x
  simp only [rankTwoProj, ContinuousLinearMap.comp_apply, rankOne_apply, inner_smul_right,
    inner_self_basis, mul_one]

/-- `det(1 − zA) = 1 − 2z` for every coupling `z`. -/
theorem fredholmDet_rankTwoProj (b : HilbertBasis ι 𝕜 E) (i₀ : ι) (z : 𝕜) :
    fredholmDet (rankTwoProj b i₀) z = 1 - 2 * z := by
  have hA := isTraceClass_rankTwoProj b i₀
  rw [← fredholmDetIn_eq_fredholmDet hA b z,
    fredholmDetIn_eq_matrix_det_of_support b _ {i₀} ?_ z]
  · have hU : Unique (({i₀} : Finset ι) : Type _) :=
      ⟨⟨⟨i₀, Finset.mem_singleton_self _⟩⟩, fun x => Subtype.ext (Finset.mem_singleton.1 x.2)⟩
    rw [Matrix.det_unique]
    have hd : (default : ({i₀} : Finset ι)).1 = i₀ :=
      Finset.mem_singleton.1 (default : ({i₀} : Finset ι)).2
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, compressMatrix,
      Matrix.of_apply, hd, rankTwoProj, rankOne_apply, inner_smul_right, inner_self_basis,
      smul_eq_mul, mul_one]
    ring
  · intro j hj
    rw [Finset.mem_singleton] at hj
    simp only [rankTwoProj, rankOne_apply, orthonormal_iff_ite.mp b.orthonormal,
      ite_eq_right (Ne.symm hj), zero_smul]

/-- `exp` never vanishes on `𝕜`. -/
theorem exp_ne_zero (x : 𝕜) : NormedSpace.exp x ≠ 0 := by
  intro h
  have h1 : NormedSpace.exp x * NormedSpace.exp (-x) = 1 := by
    rw [← NormedSpace.exp_add, add_neg_cancel, NormedSpace.exp_zero]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- **Rank-one witness.**  The entire determinant vanishes at `z = 1/2` (where
`1 − A/2` is not invertible), while the disk-only `fredholmDetOne` does not: the two
determinants genuinely differ off the disk. -/
theorem probe_entire_ne_detOne (b : HilbertBasis ι 𝕜 E) (i₀ : ι) :
    fredholmDet (rankTwoProj b i₀) (1 / 2) = 0 ∧
      fredholmDetOne (rankTwoProj b i₀) (isTraceClass_rankTwoProj b i₀) (1 / 2) ≠ 0 := by
  refine ⟨?_, exp_ne_zero _⟩
  rw [fredholmDet_rankTwoProj]
  ring

end Probe

end HilbertSchmidt
