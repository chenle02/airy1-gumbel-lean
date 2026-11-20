/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FredholmDet.DiskAgreement

/-! # Fredholm determinants across an isometric embedding

**Main theorem** (`fredholmDet_eq_of_isometry_intertwine`): let `J : E →ₗᵢ F` be a linear
isometry between Hilbert spaces, `X` trace class on `F` and `Y` any operator on `E` with

* `X ∘ J = J ∘ Y` (intertwining), and
* `X e = 0` whenever `e ⊥ range J`.

Then `det_F(1 − zX) = det_E(1 − zY)` for every `z ∈ 𝕜`.  (Equivalently `X = J Y J*`.)  This
compares determinants on two *different* Hilbert spaces, e.g. `L²(0, ∞)` and `L²(ℝ)`.

## Proof

Extend the orthonormal family `J(b i)` (`b` the canonical basis of `E`) to a Hilbert basis `b'`
of `F` (`Orthonormal.exists_hilbertBasis_extension`).  In `b'` every principal minor of `X`
containing an index outside `J(b)` has a zero column (`X b'_j = 0`), and the minors on
`J(b)`-indices coincide with those of `Y` in `b` (`⟪J bᵢ, X J bⱼ⟫ = ⟪J bᵢ, J Y bⱼ⟫ =
⟪bᵢ, Y bⱼ⟫`).  So the two minor series agree term by term after reindexing
(`Function.Injective.tsum_eq`), and basis independence (`fredholmDetIn_eq_fredholmDet`)
finishes.  No trace-class hypothesis on `Y` is needed (it is inherited).
-/

open Filter Topology
open scoped InnerProductSpace

namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A vector orthogonal to every `J (b i)` is orthogonal to the whole range of `J`. -/
theorem inner_map_eq_zero_of_basis {ι : Type*} (b : HilbertBasis ι 𝕜 E) (J : E →ₗᵢ[𝕜] F)
    {e : F} (he : ∀ i, ⟪e, J (b i)⟫_𝕜 = 0) (v : E) : ⟪e, J v⟫_𝕜 = 0 := by
  have h := (b.hasSum_repr v).mapL ((innerSL 𝕜 e).comp J.toContinuousLinearMap)
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    innerSL_apply_apply, map_smul, he, smul_zero] at h
  exact h.unique hasSum_zero

omit [CompleteSpace E] [CompleteSpace F] in
open scoped Classical in
/-- Principal minors along an index embedding `g` agree when the matrix entries do. -/
theorem detMinor_map {ι ι' : Type*} (b : HilbertBasis ι 𝕜 E) (b' : HilbertBasis ι' 𝕜 F)
    (A : E →L[𝕜] E) (B : F →L[𝕜] F) (g : ι ↪ ι')
    (h : ∀ i j, ⟪b' (g i), B (b' (g j))⟫_𝕜 = ⟪b i, A (b j)⟫_𝕜) (s : Finset ι) :
    detMinor b' B (s.map g) = detMinor b A s := by
  let e : s ≃ s.map g := Equiv.ofBijective (fun i => ⟨g i, Finset.mem_map_of_mem _ i.2⟩)
    ⟨fun i j hij => Subtype.ext (g.injective (congrArg Subtype.val hij)), fun j => by
      obtain ⟨a, ha, haj⟩ := Finset.mem_map.1 j.2
      exact ⟨⟨a, ha⟩, Subtype.ext haj⟩⟩
  unfold detMinor
  convert (Matrix.det_submatrix_equiv_self e
    (Matrix.of fun i j : s.map g => ⟪b' i, B (b' j)⟫_𝕜)).symm using 2
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, e]
  exact (h i j).symm

omit [CompleteSpace F] in
open scoped Classical in
/-- A principal minor containing an index whose basis vector `B` kills is zero. -/
theorem detMinor_eq_zero_of_apply_eq_zero {ι' : Type*} (b' : HilbertBasis ι' 𝕜 F)
    (B : F →L[𝕜] F) {t : Finset ι'} {j : ι'} (hj : j ∈ t) (h0 : B (b' j) = 0) :
    detMinor b' B t = 0 := by
  unfold detMinor
  convert Matrix.det_eq_zero_of_column_eq_zero (⟨j, hj⟩ : t) fun i => ?_
  simp [h0]

/-- **Determinants across an isometric embedding.**  If `X ∘ J = J ∘ Y` and `X` kills
`(range J)ᗮ`, then `det(1 − zX) = det(1 − zY)` (trace-class `X`). -/
theorem fredholmDet_eq_of_isometry_intertwine (J : E →ₗᵢ[𝕜] F) {X : F →L[𝕜] F}
    (hX : IsTraceClass X) (Y : E →L[𝕜] E) (hXJ : ∀ v, X (J v) = J (Y v))
    (hperp : ∀ e, (∀ v, ⟪e, J v⟫_𝕜 = 0) → X e = 0) (z : 𝕜) :
    fredholmDet X z = fredholmDet Y z := by
  classical
  set b := canonicalBasis 𝕜 E
  have hon : Orthonormal 𝕜 (fun i => J (b i)) := b.orthonormal.comp_linearIsometry J
  have hinj : Function.Injective (fun i => J (b i)) := hon.linearIndependent.injective
  obtain ⟨w, b', hsub, hb'⟩ :=
    ((orthonormal_subtype_range hinj).2 hon).exists_hilbertBasis_extension
  -- the index embedding `i ↦ J (b i)`
  let g : canonicalIndex 𝕜 E → w := fun i => ⟨J (b i), hsub ⟨i, rfl⟩⟩
  have hg : Function.Injective g := fun i j h => hinj (congrArg Subtype.val h)
  let gE : canonicalIndex 𝕜 E ↪ w := ⟨g, hg⟩
  have hb'g : ∀ i, b' (gE i) = J (b i) := fun i => by rw [hb']; rfl
  -- columns outside the range of `g` vanish
  have hcol : ∀ j : w, j ∉ Set.range gE → X (b' j) = 0 := by
    intro j hj
    refine hperp _ (inner_map_eq_zero_of_basis b J fun i => ?_)
    rw [← hb'g]
    exact b'.orthonormal.2 fun h => hj ⟨i, h.symm⟩
  have hmin : ∀ s : Finset (canonicalIndex 𝕜 E), detMinor b' X (s.map gE) = detMinor b Y s :=
    detMinor_map b b' Y X gE fun i j => by
      rw [hb'g, hb'g, hXJ, LinearIsometry.inner_map_map]
  set f : Finset w → 𝕜 := fun t => (-z) ^ t.card * detMinor b' X t with hf
  -- terms outside the range vanish
  have hsupp : Function.support f ⊆ Set.range (fun s : Finset (canonicalIndex 𝕜 E) => s.map gE) := by
    intro t ht
    by_cases hall : ∀ j ∈ t, j ∈ Set.range gE
    · refine ⟨t.preimage gE gE.injective.injOn, ?_⟩
      ext j
      simp only [Finset.mem_map, Finset.mem_preimage]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hj
        obtain ⟨a, rfl⟩ := hall j hj
        exact ⟨a, hj, rfl⟩
    · push Not at hall
      obtain ⟨j, hjt, hj⟩ := hall
      exfalso
      apply ht
      simp only [hf]
      rw [detMinor_eq_zero_of_apply_eq_zero b' X hjt (hcol j hj), mul_zero]
  calc fredholmDet X z = fredholmDetIn b' X z := (fredholmDetIn_eq_fredholmDet hX b' z).symm
    _ = ∑' t, f t := rfl
    _ = ∑' s : Finset (canonicalIndex 𝕜 E), f (s.map gE) := ((Finset.map_injective gE).tsum_eq hsupp).symm
    _ = ∑' s : Finset (canonicalIndex 𝕜 E), (-z) ^ s.card * detMinor b Y s := by
        refine tsum_congr fun s => ?_
        show (-z) ^ (s.map gE).card * detMinor b' X (s.map gE) = _
        rw [hmin s, Finset.card_map]
    _ = fredholmDet Y z := rfl

end HilbertSchmidt
