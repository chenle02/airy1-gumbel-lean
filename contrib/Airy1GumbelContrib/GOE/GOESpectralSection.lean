/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.GOE.GOECompression
import Airy1GumbelContrib.FredholmDet.DiskAgreement
import Mathlib.Analysis.Matrix.Order

/-!
# Hadamard's inequality and a Fredholm determinant bound

On each finite section, an orthonormal family with small defect controls
the selected diagonal factors. The remaining factors are bounded through
the diagonal trace sum.
-/

namespace GOELocalization

open Filter HilbertSchmidt Matrix
open scoped InnerProductSpace RealInnerProductSpace Topology

/-- Hadamard's inequality for a real positive semidefinite matrix, using the
columns of its positive square root as a Gram family. -/
theorem det_le_prod_diag_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : A.det ≤ ∏ i, A i i := by
  open scoped MatrixOrder in
  let S := CFC.sqrt A
  have hS : S.conjTranspose = S := by
    open scoped MatrixOrder in
    exact ((Matrix.nonneg_iff_posSemidef).mp (CFC.sqrt_nonneg A)).isHermitian
  have hSq : S * S = A := by
    open scoped MatrixOrder in
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  let u (j : ι) : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => S i j)
  have hgram (i j : ι) : ⟪u i, u j⟫_ℝ = A i j := by
    calc
      _ = (S.conjTranspose * S) i j := by
        simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply,
          dotProduct, Matrix.conjTranspose_apply, u, Pi.star_apply, star_trivial]
        exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      _ = _ := by rw [hS, hSq]
  have hmat : (Matrix.of fun i j => ⟪u i, u j⟫_ℝ) = A := Matrix.ext hgram
  have h := HilbertSchmidt.Hadamard.crossGram_det_bound (𝕜 := ℝ) u u
  rw [hmat, ← Finset.prod_mul_distrib] at h
  refine (le_abs_self A.det).trans ?_
  rw [← Real.norm_eq_abs]
  refine h.trans_eq ?_
  apply Finset.prod_congr rfl
  intro i _
  rw [← sq, ← real_inner_self_eq_norm_sq, hgram]

section Compression

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A contraction has quadratic form bounded above by the squared norm. -/
theorem real_inner_apply_le_norm_sq {B : E →L[ℝ] E} (hnorm : ‖B‖ ≤ 1) (v : E) :
    ⟪v, B v⟫_ℝ ≤ ‖v‖ ^ 2 := by
  have h := (B.le_opNorm v).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
  rw [one_mul] at h
  exact (real_inner_le_norm _ _).trans (by
    rw [sq]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg v))

/-- The entries of the finite defect matrix are the inner products with the defect operator. -/
theorem one_sub_compressMatrix_apply {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℝ E) (B : E →L[ℝ] E) (s : Finset ι) (i j : s) :
    (1 - compressMatrix b B s) i j = ⟪b i, b j - B (b j)⟫_ℝ := by
  have hb := (orthonormal_iff_ite.mp b.orthonormal) (i : ι) (j : ι)
  simp only [Matrix.sub_apply, compressMatrix, Matrix.of_apply, inner_sub_right, hb, Matrix.one_apply]
  simp only [Subtype.ext_iff]

/-- A finite section of the defect of a self-adjoint contraction is positive semidefinite. -/
theorem posSemidef_one_sub_compressMatrix [CompleteSpace E] {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℝ E) {B : E →L[ℝ] E} (hself : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1)
    (s : Finset ι) : (1 - compressMatrix b B s).PosSemidef := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, one_sub_compressMatrix_apply, inner_sub_right]
    have hB : ⟪B (b i), b j⟫_ℝ = ⟪b i, B (b j)⟫_ℝ := hsym (b i) (b j)
    rw [real_inner_comm (b i) (b j), real_inner_comm (B (b i)) (b j), hB]
  · intro x
    let D : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - B
    let v : E := ∑ i : s, x i • b i
    have hD (i j : s) : (1 - compressMatrix b B s) i j = ⟪b i, D (b j)⟫_ℝ :=
      one_sub_compressMatrix_apply b B s i j
    have hQ : star x ⬝ᵥ ((1 - compressMatrix b B s) *ᵥ x) = ⟪v, D v⟫_ℝ := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, hD, Finset.mul_sum, v,
        map_sum, map_smul]
      rw [sum_inner]
      simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hQ]
    change 0 ≤ ⟪v, v - B v⟫_ℝ
    rw [inner_sub_right, real_inner_self_eq_norm_sq, sub_nonneg]
    exact real_inner_apply_le_norm_sq hnorm v

end Compression

/-- Split the selected factors from the remaining diagonal factors in a finite section.
The unselected factors are bounded by the exponential of their negative diagonal sum. -/
theorem prod_one_sub_le_of_selected {ι : Type*} [DecidableEq ι]
    (d : ι → ℝ) {t s : Finset ι} (hts : t ⊆ s) {q : ℝ} (hq : 0 ≤ q)
    (hd : ∀ i ∈ s, d i ≤ 1) (hsel : ∀ i ∈ t, 1 - d i ≤ q) :
    (∏ i ∈ s, (1 - d i)) ≤ q ^ t.card * Real.exp ((t.card : ℝ) - ∑ i ∈ s, d i) := by
  have hselected : (∏ i ∈ t, (1 - d i)) ≤ q ^ t.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i hi => sub_nonneg.mpr (hd i (hts hi))) hsel
  have hrest : (∏ i ∈ s \ t, (1 - d i)) ≤ Real.exp (-(∑ i ∈ s \ t, d i)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod₀
      (fun i hi => sub_nonneg.mpr (hd i (Finset.mem_sdiff.mp hi).1))
      (fun i _ => by simpa only [sub_eq_add_neg, add_comm (1 : ℝ)] using Real.add_one_le_exp (-d i))
  have hsum : (∑ i ∈ s \ t, d i) + (∑ i ∈ t, d i) = ∑ i ∈ s, d i :=
    Finset.sum_sdiff hts
  have hdiag : (∑ i ∈ t, d i) ≤ (t.card : ℝ) := by
    exact (Finset.sum_le_sum (fun i hi => hd i (hts hi))).trans_eq (by simp)
  calc
    _ = (∏ i ∈ t, (1 - d i)) * ∏ i ∈ s \ t, (1 - d i) :=
      (Finset.prod_sdiff hts).symm.trans (mul_comm _ _)
    _ ≤ q ^ t.card * Real.exp (-(∑ i ∈ s \ t, d i)) := by
      exact mul_le_mul hselected hrest
        (Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (hd i (Finset.mem_sdiff.mp hi).1)))
        (pow_nonneg hq _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (pow_nonneg hq _)

/-- Hadamard's bound on a finite section containing all the marked indices of small defect. -/
theorem det_one_sub_compressMatrix_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℝ E)
    {B : E →L[ℝ] E} (hself : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1)
    {t s : Finset ι} (hts : t ⊆ s) {q : ℝ} (hq : 0 ≤ q)
    (hsel : ∀ i ∈ t, ⟪b i, b i - B (b i)⟫_ℝ ≤ q) :
    (1 - compressMatrix b B s).det ≤
      q ^ t.card * Real.exp ((t.card : ℝ) - ∑ i ∈ s, ⟪b i, B (b i)⟫_ℝ) := by
  let d (i : ι) := ⟪b i, B (b i)⟫_ℝ
  have hentry (i : s) : (1 - compressMatrix b B s) i i = 1 - d i := by
    rw [one_sub_compressMatrix_apply, inner_sub_right, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one,
      one_pow]
  calc
    _ ≤ ∏ i : s, (1 - compressMatrix b B s) i i :=
      det_le_prod_diag_of_posSemidef (posSemidef_one_sub_compressMatrix b hself hnorm s)
    _ = ∏ i : s, (1 - d i) := Finset.prod_congr rfl (fun i _ => hentry i)
    _ = ∏ i ∈ s, (1 - d i) := Finset.prod_coe_sort s (fun i => 1 - d i)
    _ ≤ _ := by
      apply prod_one_sub_le_of_selected d hts hq
      · intro i _
        have h := real_inner_apply_le_norm_sq hnorm (b i)
        simpa only [d, b.orthonormal.norm_eq_one, one_pow] using h
      · intro i hi
        simpa only [d, inner_sub_right, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one,
          one_pow] using hsel i hi

/-- The Fredholm determinant at unit coupling is bounded by the marked defects
and the exponential of the complementary trace contribution. -/
theorem fredholmDet_le_of_orthonormal_defect {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {B : E →L[ℝ] E} (hB : HilbertSchmidt.IsTraceClass B)
    (hself : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1)
    {N : ℕ} (e : Fin N → E) (he : Orthonormal ℝ e)
    {q : ℝ} (hq : 0 ≤ q)
    (hsmall : ∀ j, ⟪e j, e j - B (e j)⟫_ℝ ≤ q) :
    HilbertSchmidt.fredholmDet B 1 ≤
      q ^ N * Real.exp ((N : ℝ) - HilbertSchmidt.trace B) := by
  classical
  have hinj := he.linearIndependent.injective
  have hor : Orthonormal ℝ ((↑) : Set.range e → E) :=
    (orthonormal_subtype_range hinj).mpr he
  obtain ⟨w, b, hsub, hb⟩ := hor.exists_hilbertBasis_extension
  -- Use the same equality decision as the finite-section convergence theorem.
  let _ : DecidableEq w := Classical.decEq w
  let em : Fin N ↪ w :=
    ⟨fun j => ⟨e j, hsub (Set.mem_range_self j)⟩, fun _ _ hj => hinj (congrArg Subtype.val hj)⟩
  let t : Finset w := Finset.univ.map em
  have hcard : t.card = N := by simp [t]
  have hdr (i : w) (hi : i ∈ t) : ⟪b i, b i - B (b i)⟫_ℝ ≤ q := by
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
    have hbe : b (em j) = e j := congrFun hb (em j)
    rw [hbe]
    exact hsmall j
  let d (i : w) := ⟪b i, B (b i)⟫_ℝ
  have hsum : Tendsto (fun s : Finset w => ∑ i ∈ s, d i) atTop (𝓝 (trace B)) := by
    rw [trace_eq_tsum_inner hB b]
    exact (summable_inner_diagonal hB b).hasSum
  have hlim := tendsto_fredholmDetIn_matrix_det hB b (1 : ℝ)
  rw [fredholmDetIn_eq_fredholmDet hB b] at hlim
  have hlim' : Tendsto (fun s : Finset w => (1 - compressMatrix b B s).det) atTop
      (𝓝 (fredholmDet B 1)) := by
    simpa only [one_smul] using hlim
  have hright : Tendsto (fun s : Finset w => q ^ N * Real.exp ((N : ℝ) - ∑ i ∈ s, d i))
      atTop (𝓝 (q ^ N * Real.exp ((N : ℝ) - trace B))) :=
    (Real.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := (N : ℝ))).sub hsum)).const_mul _
  apply le_of_tendsto_of_tendsto hlim' hright
  filter_upwards [eventually_ge_atTop t] with s hs
  simpa only [hcard, d] using det_one_sub_compressMatrix_le b hself hnorm hs hq hdr

/-- The generic defect bound applied to the localized GOE packet family. -/
theorem fredholmDet_goeOp_le_defect (M : ℝ) (hM : 16 ≤ M) :
    fredholmDet (AiryFdd.goeOp (-M)) 1 ≤
      (4 * Real.exp (-(M * Real.sqrt M) / 16)) ^ goeModeCount M *
        Real.exp ((goeModeCount M : ℝ) - trace (AiryFdd.goeOp (-M))) := by
  obtain ⟨e, he, hsmall⟩ := goeOp_small_defect_family M hM
  exact fredholmDet_le_of_orthonormal_defect (AiryFdd.isTraceClass_goeOp (-M))
    (goeOp_isSelfAdjoint (-M)) (norm_goeOp_le_one (-M)) e he (by positivity) hsmall

end GOELocalization
