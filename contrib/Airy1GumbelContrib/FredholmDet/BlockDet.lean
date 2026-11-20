/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FredholmDet.TracePowDet
import Airy1GumbelContrib.FredholmDet.DetIsometry
import Airy1GumbelContrib.FredholmDet.Multiplicativity
import Airy1GumbelContrib.FredholmDet.TraceClassAdd

/-! # Block-operator determinant algebra

Abstract and convention-free: no Airy content.  Everything lives on the `L²` product
`WithLp 2 (E × F)` of two Hilbert spaces, which is again a Hilbert space (Mathlib's
`WithLp.instProdInnerProductSpace`), so the entire Fredholm determinant `fredholmDet` (`FredholmDet/`) applies to it
unchanged.

## Main results

* `fredholmDet_comp_comm_rect`: **rectangular Sylvester**: for Hilbert–Schmidt
  `A : F →L E` and `B : E →L F` between *different* Hilbert spaces,
  `det_E(1 − z AB) = det_F(1 − z BA)`.  The variants `fredholmDet_comp_comm_rect_right`,
  `fredholmDet_comp_comm_rect_left` allow one factor to be merely bounded when the other is
  (rectangular) trace class.
* `blockOp A B C D`: the block operator `[[A, B], [C, D]]` on `WithLp 2 (E × F)`, with
  `blockOp_comp_blockOp` (block multiplication) and `trace_blockOp` (`tr = tr A + tr D`).
* `fredholmDet_blockOp_upper` / `fredholmDet_blockOp_lower`: **block-triangular determinant**
  `det(1 − z[[A, X], [0, D]]) = det(1 − zA) · det(1 − zD)` (and the lower twin).
* `fredholmDet_blockOp_schur`: **block Schur / LU step**: if `R (1 − A) = 1` then
  `det(1 − [[A, B], [C, D]]) = det(1 − A) · det(1 − (D + C R B))`.

## Trace class off the diagonal

`IsTraceClass` is a same-space notion (`T = S ∘ R`, both Hilbert–Schmidt on `E`).  For an
off-diagonal block `X : F →L E` we use `IsRectTraceClass X`: `X = S ∘ T` with `S : E →L E`,
`T : F →L E` Hilbert–Schmidt; for `E = F` this is literally `IsTraceClass`
(`IsTraceClass.isRectTraceClass`).  Every corner `ι_i ∘ X ∘ π_j` of `WithLp 2 (E × F)` is then
trace class on the product (`isTraceClass_sandwich`).

## Proof strategy

* Rectangular Sylvester: embed `A`, `B` as corners `[[0, A], [0, 0]]`, `[[0, 0], [B, 0]]`,
  apply same-space cyclicity `fredholmDet_comp_comm` on the product, and pull both sides back
  along the isometric summand inclusions with `fredholmDet_eq_of_isometry_intertwine`.
* Triangular determinant: `1 − zU = (1 − z(R + N))(1 − zP)` and
  `1 − z(R + N) = (1 − zR)(1 − zN)` with the corners `P = [[A,0],[0,0]]`, `R = [[0,0],[0,D]]`,
  `N = [[0,X],[0,0]]` (the cross products vanish), multiplicativity
  `fredholmDet_add_sub_smul_comp`, the corner transfer `fredholmDet_corner_inl/inr`, and
  `det(1 − zN) = 1` for the square-zero, trace-zero corner (`fredholmDet_eq_one_of_sq_eq_zero`,
  via `fredholmDet_eq_of_trace_pow_eq`).
* Schur: `[[A,B],[C,D]] = M + W − MW` with `M = [[0,0],[CR,0]]`, `W = [[A,B],[0,Z]]`.

No traces of block operators are needed for the determinant results; the trace of a corner
is computed from the determinant identity (`trace_corner_inl`).
-/

open Filter Topology
open scoped ENNReal NNReal InnerProductSpace

universe u

namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]

section Rect

variable {E F N : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup N] [InnerProductSpace 𝕜 N] [CompleteSpace N]

/-- **Rectangular trace class**: `X : F →L E` factors as `S ∘ T` with `S : E →L E` and
`T : F →L E` Hilbert–Schmidt.  For `E = F` this is `IsTraceClass`. -/
def IsRectTraceClass (X : F →L[𝕜] E) : Prop :=
  ∃ (S : E →L[𝕜] E) (T : F →L[𝕜] E), IsHilbertSchmidt S ∧ IsHilbertSchmidt T ∧ X = S ∘L T

theorem IsTraceClass.isRectTraceClass {X : E →L[𝕜] E} (h : IsTraceClass X) :
    IsRectTraceClass X := h

theorem IsRectTraceClass.isTraceClass {X : E →L[𝕜] E} (h : IsRectTraceClass X) :
    IsTraceClass X := h

/-- A rectangular trace-class map stays so under right composition by a bounded map. -/
theorem IsRectTraceClass.comp_right {X : F →L[𝕜] E} (hX : IsRectTraceClass X)
    (R : N →L[𝕜] F) : IsRectTraceClass (X ∘L R) := by
  obtain ⟨S, T, hS, hT, rfl⟩ := hX
  exact ⟨S, T ∘L R, hS, hT.comp_right' R, rfl⟩

/-- Rectangular trace class maps are Hilbert–Schmidt. -/
theorem IsRectTraceClass.isHilbertSchmidt {X : F →L[𝕜] E} (hX : IsRectTraceClass X) :
    IsHilbertSchmidt X := by
  obtain ⟨S, T, -, hT, rfl⟩ := hX
  exact hT.comp_left' S

/-- A rectangular trace-class `X : F →L E` composed with any bounded `Y : E →L F` is trace class
on `E`. -/
theorem IsRectTraceClass.isTraceClass_comp {X : F →L[𝕜] E} (hX : IsRectTraceClass X)
    (Y : E →L[𝕜] F) : IsTraceClass (X ∘L Y) := by
  obtain ⟨S, T, hS, hT, rfl⟩ := hX
  exact ⟨S, T ∘L Y, hS, hT.comp_right' Y, rfl⟩

/-- **Corners are trace class.**  If `J : K → N` has a bounded left inverse `P` and `X : M → K`
is rectangular trace class, then `J ∘ X ∘ Q : N → N` is trace class for every bounded
`Q : N → M`: `J S T Q = (J S P)(J T Q)`. -/
theorem isTraceClass_sandwich {K M : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [CompleteSpace K] [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [CompleteSpace M]
    {X : M →L[𝕜] K} (hX : IsRectTraceClass X) (J : K →L[𝕜] N) (P : N →L[𝕜] K)
    (hPJ : P ∘L J = ContinuousLinearMap.id 𝕜 K) (Q : N →L[𝕜] M) :
    IsTraceClass (J ∘L X ∘L Q) := by
  obtain ⟨S, T, hS, hT, rfl⟩ := hX
  refine ⟨J ∘L S ∘L P, J ∘L T ∘L Q, hS.sandwich J P, hT.sandwich J Q, ?_⟩
  ext v
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.comp_apply P J, hPJ, ContinuousLinearMap.id_apply]

/-- **Rectangular Sylvester / cyclicity** (helper on the product; see
`fredholmDet_comp_comm_rect`). -/
theorem trace_comp_comm_of_isTraceClass {T : E →L[𝕜] E} (hT : IsTraceClass T)
    (X : E →L[𝕜] E) : trace (X ∘L T) = trace (T ∘L X) := by
  obtain ⟨S, R, hS, hR, rfl⟩ := hT
  calc trace (X ∘L (S ∘L R)) = trace ((X ∘L S) ∘L R) := by rw [ContinuousLinearMap.comp_assoc]
    _ = trace (R ∘L (X ∘L S)) := trace_comp_comm (hS.comp_left X) hR
    _ = trace ((R ∘L X) ∘L S) := by rw [ContinuousLinearMap.comp_assoc]
    _ = trace (S ∘L (R ∘L X)) := trace_comp_comm (hR.comp_right X) hS
    _ = trace ((S ∘L R) ∘L X) := by rw [ContinuousLinearMap.comp_assoc]

theorem trace_zero_op : trace (0 : E →L[𝕜] E) = 0 := by
  simp [trace]

theorem isTraceClass_zero : IsTraceClass (0 : E →L[𝕜] E) :=
  ⟨0, 0, by simp [IsHilbertSchmidt, hsENorm_zero'], by simp [IsHilbertSchmidt, hsENorm_zero'],
    by simp⟩

/-- A square-zero, trace-zero trace-class operator has `det(1 − zN) = 1` for every `z`
(all power traces vanish). -/
theorem fredholmDet_eq_one_of_sq_eq_zero {T : E →L[𝕜] E} (hT : IsTraceClass T)
    (h2 : T ∘L T = 0) (htr : trace T = 0) (z : 𝕜) : fredholmDet T z = 1 := by
  rw [fredholmDet_eq_of_trace_pow_eq hT isTraceClass_zero ?_ z, fredholmDet_zero_op]
  intro m hm
  rcases Nat.lt_or_ge m 2 with h | h
  · obtain rfl : m = 1 := by omega
    simp [htr, trace_zero_op]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have : T ^ (k + 2) = 0 := by
      rw [pow_add, pow_two]
      change T ^ k * (T ∘L T) = 0
      rw [h2, mul_zero]
    rw [this, zero_pow (by omega)]

end Rect

section Block

variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Inclusion `x ↦ (x, 0)` of the first summand of `WithLp 2 (E × F)`. -/
noncomputable def blockInl : E →L[𝕜] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl 𝕜 E F

/-- Inclusion `y ↦ (0, y)` of the second summand of `WithLp 2 (E × F)`. -/
noncomputable def blockInr : F →L[𝕜] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr 𝕜 E F

/-- First coordinate of `WithLp 2 (E × F)`. -/
noncomputable def blockFst : WithLp 2 (E × F) →L[𝕜] E := WithLp.fstL 2 𝕜 E F

/-- Second coordinate of `WithLp 2 (E × F)`. -/
noncomputable def blockSnd : WithLp 2 (E × F) →L[𝕜] F := WithLp.sndL 2 𝕜 E F

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem blockInl_apply (x : E) :
    (blockInl (𝕜 := 𝕜) x : WithLp 2 (E × F)) = WithLp.toLp 2 (x, (0 : F)) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem blockInr_apply (y : F) :
    (blockInr (𝕜 := 𝕜) y : WithLp 2 (E × F)) = WithLp.toLp 2 ((0 : E), y) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem blockFst_apply (v : WithLp 2 (E × F)) : (blockFst (𝕜 := 𝕜) v : E) = v.fst := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem blockSnd_apply (v : WithLp 2 (E × F)) : (blockSnd (𝕜 := 𝕜) v : F) = v.snd := rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem blockFst_comp_blockInl :
    ((blockFst : WithLp 2 (E × F) →L[𝕜] E) ∘L blockInl) = ContinuousLinearMap.id 𝕜 E := by
  ext x; simp

omit [CompleteSpace E] [CompleteSpace F] in
theorem blockSnd_comp_blockInr :
    ((blockSnd : WithLp 2 (E × F) →L[𝕜] F) ∘L blockInr) = ContinuousLinearMap.id 𝕜 F := by
  ext x; simp

/-- The summand inclusion `x ↦ (x, 0)` as a linear isometry. -/
noncomputable def blockInlₗᵢ : E →ₗᵢ[𝕜] WithLp 2 (E × F) where
  toLinearMap := (blockInl : E →L[𝕜] WithLp 2 (E × F)).toLinearMap
  norm_map' x := WithLp.norm_toLp_fst 2 E F x

/-- The summand inclusion `y ↦ (0, y)` as a linear isometry. -/
noncomputable def blockInrₗᵢ : F →ₗᵢ[𝕜] WithLp 2 (E × F) where
  toLinearMap := (blockInr : F →L[𝕜] WithLp 2 (E × F)).toLinearMap
  norm_map' y := WithLp.norm_toLp_snd 2 E F y

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem blockInlₗᵢ_apply (x : E) :
    (blockInlₗᵢ (𝕜 := 𝕜) x : WithLp 2 (E × F)) = WithLp.toLp 2 (x, (0 : F)) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem blockInrₗᵢ_apply (y : F) :
    (blockInrₗᵢ (𝕜 := 𝕜) y : WithLp 2 (E × F)) = WithLp.toLp 2 ((0 : E), y) := rfl

/-- **Corner transfer, first summand**: `det_{E⊕F}(1 − z[[T, 0], [0, 0]]) = det_E(1 − zT)`. -/
theorem fredholmDet_corner_inl {T : E →L[𝕜] E}
    (hT : IsTraceClass (blockInl ∘L T ∘L blockFst : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)))
    (z : 𝕜) :
    fredholmDet (blockInl ∘L T ∘L blockFst : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) z =
      fredholmDet T z := by
  refine fredholmDet_eq_of_isometry_intertwine blockInlₗᵢ hT T (fun v => by simp) ?_ z
  intro e he
  have h0 : e.fst = 0 := by
    have h := he e.fst
    simp only [blockInlₗᵢ_apply, WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
      inner_zero_right, add_zero] at h
    exact inner_self_eq_zero.1 h
  simp [h0]

/-- **Corner transfer, second summand**: `det_{E⊕F}(1 − z[[0, 0], [0, T]]) = det_F(1 − zT)`. -/
theorem fredholmDet_corner_inr {T : F →L[𝕜] F}
    (hT : IsTraceClass (blockInr ∘L T ∘L blockSnd : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)))
    (z : 𝕜) :
    fredholmDet (blockInr ∘L T ∘L blockSnd : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) z =
      fredholmDet T z := by
  refine fredholmDet_eq_of_isometry_intertwine blockInrₗᵢ hT T (fun v => by simp) ?_ z
  intro e he
  have h0 : e.snd = 0 := by
    have h := he e.snd
    simp only [blockInrₗᵢ_apply, WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
      inner_zero_right, zero_add] at h
    exact inner_self_eq_zero.1 h
  simp [h0]

/-! ### Rectangular Sylvester -/

/-- **Rectangular Sylvester identity**: for Hilbert–Schmidt `A : F →L E` and `B : E →L F`
between possibly different Hilbert spaces, `det_E(1 − z AB) = det_F(1 − z BA)`. -/
theorem fredholmDet_comp_comm_rect {A : F →L[𝕜] E} {B : E →L[𝕜] F} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) (z : 𝕜) :
    fredholmDet (A ∘L B) z = fredholmDet (B ∘L A) z := by
  set X : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) := blockInl ∘L A ∘L blockSnd
  set Y : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) := blockInr ∘L B ∘L blockFst
  have hX : IsHilbertSchmidt X := hA.sandwich _ _
  have hY : IsHilbertSchmidt Y := hB.sandwich _ _
  have hXY : X ∘L Y = blockInl ∘L (A ∘L B) ∘L blockFst := by ext v; simp [X, Y]
  have hYX : Y ∘L X = blockInr ∘L (B ∘L A) ∘L blockSnd := by ext v; simp [X, Y]
  have h := fredholmDet_comp_comm hX hY z
  rw [hXY, hYX] at h
  have tXY := IsHilbertSchmidt.isTraceClass_comp hX hY
  have tYX := IsHilbertSchmidt.isTraceClass_comp hY hX
  rw [hXY] at tXY
  rw [hYX] at tYX
  rwa [fredholmDet_corner_inl tXY, fredholmDet_corner_inr tYX] at h

/-- Rectangular Sylvester with a merely **bounded** left factor and a rectangular trace-class
right factor: `det_E(1 − z RC) = det_F(1 − z CR)`. -/
theorem fredholmDet_comp_comm_rect_right (R : F →L[𝕜] E) {C : E →L[𝕜] F}
    (hC : IsRectTraceClass C) (z : 𝕜) :
    fredholmDet (R ∘L C) z = fredholmDet (C ∘L R) z := by
  obtain ⟨S, T, hS, hT, rfl⟩ := hC
  calc fredholmDet (R ∘L (S ∘L T)) z = fredholmDet ((R ∘L S) ∘L T) z := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = fredholmDet (T ∘L (R ∘L S)) z := fredholmDet_comp_comm_rect (hS.comp_left' R) hT z
    _ = fredholmDet ((T ∘L R) ∘L S) z := by rw [ContinuousLinearMap.comp_assoc]
    _ = fredholmDet (S ∘L (T ∘L R)) z := fredholmDet_comp_comm (hT.comp_right' R) hS z
    _ = fredholmDet ((S ∘L T) ∘L R) z := by rw [ContinuousLinearMap.comp_assoc]

/-- Rectangular Sylvester with a rectangular trace-class left factor and a merely **bounded**
right factor: `det_E(1 − z XC) = det_F(1 − z CX)`. -/
theorem fredholmDet_comp_comm_rect_left {X : F →L[𝕜] E} (hX : IsRectTraceClass X)
    (C : E →L[𝕜] F) (z : 𝕜) :
    fredholmDet (X ∘L C) z = fredholmDet (C ∘L X) z := by
  obtain ⟨S, T, hS, hT, rfl⟩ := hX
  calc fredholmDet ((S ∘L T) ∘L C) z = fredholmDet (S ∘L (T ∘L C)) z := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = fredholmDet ((T ∘L C) ∘L S) z := fredholmDet_comp_comm hS (hT.comp_right' C) z
    _ = fredholmDet (T ∘L (C ∘L S)) z := by rw [ContinuousLinearMap.comp_assoc]
    _ = fredholmDet ((C ∘L S) ∘L T) z := fredholmDet_comp_comm_rect hT (hS.comp_left' C) z
    _ = fredholmDet (C ∘L (S ∘L T)) z := by rw [ContinuousLinearMap.comp_assoc]

/-! ### Block operators -/

/-- The block operator `[[A, B], [C, D]]` on `WithLp 2 (E × F)`:
`(x, y) ↦ (A x + B y, C x + D y)`. -/
noncomputable def blockOp (A : E →L[𝕜] E) (B : F →L[𝕜] E) (C : E →L[𝕜] F) (D : F →L[𝕜] F) :
    WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) :=
  blockInl ∘L A ∘L blockFst + blockInl ∘L B ∘L blockSnd + blockInr ∘L C ∘L blockFst +
    blockInr ∘L D ∘L blockSnd

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem blockOp_apply_fst (A : E →L[𝕜] E) (B : F →L[𝕜] E) (C : E →L[𝕜] F)
    (D : F →L[𝕜] F) (v : WithLp 2 (E × F)) :
    (blockOp A B C D v).fst = A v.fst + B v.snd := by
  simp [blockOp]

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem blockOp_apply_snd (A : E →L[𝕜] E) (B : F →L[𝕜] E) (C : E →L[𝕜] F)
    (D : F →L[𝕜] F) (v : WithLp 2 (E × F)) :
    (blockOp A B C D v).snd = C v.fst + D v.snd := by
  simp [blockOp]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Block multiplication.** -/
theorem blockOp_comp_blockOp (A : E →L[𝕜] E) (B : F →L[𝕜] E) (C : E →L[𝕜] F)
    (D : F →L[𝕜] F) (A' : E →L[𝕜] E) (B' : F →L[𝕜] E) (C' : E →L[𝕜] F) (D' : F →L[𝕜] F) :
    blockOp A B C D ∘L blockOp A' B' C' D' =
      blockOp (A ∘L A' + B ∘L C') (A ∘L B' + B ∘L D') (C ∘L A' + D ∘L C')
        (C ∘L B' + D ∘L D') := by
  refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_ <;>
    · simp only [ContinuousLinearMap.comp_apply, blockOp_apply_fst, blockOp_apply_snd,
        add_apply, map_add]
      abel

theorem isRectTraceClass_zero : IsRectTraceClass (0 : F →L[𝕜] E) :=
  ⟨0, 0, by simp [IsHilbertSchmidt, hsENorm_zero'], by simp [IsHilbertSchmidt, hsENorm_zero'],
    by simp⟩

/-! ### The four corners are trace class -/

theorem isTraceClass_corner_inl_fst {X : E →L[𝕜] E} (hX : IsRectTraceClass X) :
    IsTraceClass (blockInl ∘L X ∘L blockFst : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) :=
  isTraceClass_sandwich (N := WithLp 2 (E × F)) hX blockInl blockFst blockFst_comp_blockInl blockFst

theorem isTraceClass_corner_inl_snd {X : F →L[𝕜] E} (hX : IsRectTraceClass X) :
    IsTraceClass (blockInl ∘L X ∘L blockSnd : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) :=
  isTraceClass_sandwich (N := WithLp 2 (E × F)) hX blockInl blockFst blockFst_comp_blockInl blockSnd

theorem isTraceClass_corner_inr_fst {X : E →L[𝕜] F} (hX : IsRectTraceClass X) :
    IsTraceClass (blockInr ∘L X ∘L blockFst : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) :=
  isTraceClass_sandwich (N := WithLp 2 (E × F)) hX blockInr blockSnd blockSnd_comp_blockInr blockFst

theorem isTraceClass_corner_inr_snd {X : F →L[𝕜] F} (hX : IsRectTraceClass X) :
    IsTraceClass (blockInr ∘L X ∘L blockSnd : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) :=
  isTraceClass_sandwich (N := WithLp 2 (E × F)) hX blockInr blockSnd blockSnd_comp_blockInr blockSnd

/-- A block operator with (rectangular) trace-class blocks has finite trace norm. -/
theorem traceENorm_blockOp_ne_top {A : E →L[𝕜] E} {B : F →L[𝕜] E} {C : E →L[𝕜] F}
    {D : F →L[𝕜] F} (hA : IsRectTraceClass A) (hB : IsRectTraceClass B)
    (hC : IsRectTraceClass C) (hD : IsRectTraceClass D) :
    traceENorm (blockOp A B C D) ≠ ⊤ :=
  traceENorm_add_ne_top (traceENorm_add_ne_top (traceENorm_add_ne_top
    (isTraceClass_corner_inl_fst hA).traceENorm_ne_top
    (isTraceClass_corner_inl_snd hB).traceENorm_ne_top)
    (isTraceClass_corner_inr_fst hC).traceENorm_ne_top)
    (isTraceClass_corner_inr_snd hD).traceENorm_ne_top

/-! ### Off-diagonal corners: trace zero, determinant one -/

/-- The upper off-diagonal corner `[[0, X], [0, 0]]` has trace `0`. -/
theorem trace_corner_inl_snd {X : F →L[𝕜] E} (hX : IsRectTraceClass X) :
    trace (blockInl ∘L X ∘L blockSnd : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) = 0 := by
  have hN := isTraceClass_corner_inl_snd (F := F) hX
  have h1 : ((blockInl : E →L[𝕜] WithLp 2 (E × F)) ∘L (blockFst : WithLp 2 (E × F) →L[𝕜] E)) ∘L
      (blockInl ∘L X ∘L blockSnd) = (blockInl ∘L X ∘L blockSnd : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) := by
    refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_ <;> simp
  have h2 : (blockInl ∘L X ∘L blockSnd : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) ∘L
      ((blockInl : E →L[𝕜] WithLp 2 (E × F)) ∘L (blockFst : WithLp 2 (E × F) →L[𝕜] E)) = 0 := by
    refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_ <;> simp
  rw [← h1, trace_comp_comm_of_isTraceClass hN, h2, trace_zero_op]

/-- The lower off-diagonal corner `[[0, 0], [X, 0]]` has trace `0`. -/
theorem trace_corner_inr_fst {X : E →L[𝕜] F} (hX : IsRectTraceClass X) :
    trace (blockInr ∘L X ∘L blockFst : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) = 0 := by
  have hN := isTraceClass_corner_inr_fst (E := E) hX
  have h1 : ((blockInr : F →L[𝕜] WithLp 2 (E × F)) ∘L (blockSnd : WithLp 2 (E × F) →L[𝕜] F)) ∘L
      (blockInr ∘L X ∘L blockFst) = (blockInr ∘L X ∘L blockFst : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) := by
    refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_ <;> simp
  have h2 : (blockInr ∘L X ∘L blockFst : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) ∘L
      ((blockInr : F →L[𝕜] WithLp 2 (E × F)) ∘L (blockSnd : WithLp 2 (E × F) →L[𝕜] F)) = 0 := by
    refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_ <;> simp
  rw [← h1, trace_comp_comm_of_isTraceClass hN, h2, trace_zero_op]

/-- `det(1 − z[[0, X], [0, 0]]) = 1`. -/
theorem fredholmDet_corner_inl_snd {X : F →L[𝕜] E} (hX : IsRectTraceClass X) (z : 𝕜) :
    fredholmDet (blockInl ∘L X ∘L blockSnd : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) z = 1 :=
  fredholmDet_eq_one_of_sq_eq_zero (isTraceClass_corner_inl_snd hX)
    (by refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_ <;> simp)
    (trace_corner_inl_snd hX) z

/-- `det(1 − z[[0, 0], [X, 0]]) = 1`. -/
theorem fredholmDet_corner_inr_fst {X : E →L[𝕜] F} (hX : IsRectTraceClass X) (z : 𝕜) :
    fredholmDet (blockInr ∘L X ∘L blockFst : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) z = 1 :=
  fredholmDet_eq_one_of_sq_eq_zero (isTraceClass_corner_inr_fst hX)
    (by refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_ <;> simp)
    (trace_corner_inr_fst hX) z

/-! ### Block-triangular determinants -/

/-- **Block upper-triangular determinant**: for trace-class `A`, `D` and rectangular
trace-class `X`, `det(1 − z[[A, X], [0, D]]) = det(1 − zA) · det(1 − zD)`. -/
theorem fredholmDet_blockOp_upper {A : E →L[𝕜] E} {X : F →L[𝕜] E} {D : F →L[𝕜] F}
    (hA : IsTraceClass A) (hX : IsRectTraceClass X) (hD : IsTraceClass D) (z : 𝕜) :
    fredholmDet (blockOp A X 0 D) z = fredholmDet A z * fredholmDet D z := by
  have hP := isTraceClass_corner_inl_fst (F := F) hA.isRectTraceClass
  have hN := isTraceClass_corner_inl_snd hX
  have hR := isTraceClass_corner_inr_snd (E := E) hD.isRectTraceClass
  set P : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) := blockInl ∘L A ∘L blockFst with hPd
  set N : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) := blockInl ∘L X ∘L blockSnd with hNd
  set R : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) := blockInr ∘L D ∘L blockSnd with hRd
  have hRNP : (R + N) ∘L P = 0 := by
    refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_ <;> simp [hPd, hNd, hRd]
  have hRN0 : R ∘L N = 0 := by
    refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_ <;> simp [hNd, hRd]
  have e1 : blockOp A X 0 D = (R + N) + P - z • ((R + N) ∘L P) := by
    rw [hRNP]
    refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_
    · simp [hPd, hNd, hRd]
      abel
    · simp [hPd, hNd, hRd]
  have e2 : R + N = R + N - z • (R ∘L N) := by
    rw [hRN0]; refine ContinuousLinearMap.ext fun v => ?_; simp
  have hRN : traceENorm (R + N) ≠ ⊤ :=
    traceENorm_add_ne_top hR.traceENorm_ne_top hN.traceENorm_ne_top
  rw [e1, fredholmDet_add_sub_smul_comp hRN hP.traceENorm_ne_top z, e2,
    fredholmDet_add_sub_smul_comp hR.traceENorm_ne_top hN.traceENorm_ne_top z,
    fredholmDet_corner_inl hP, fredholmDet_corner_inr hR, fredholmDet_corner_inl_snd hX]
  ring

/-- **Block lower-triangular determinant**: for trace-class `A`, `D` and rectangular
trace-class `C`, `det(1 − z[[A, 0], [C, D]]) = det(1 − zA) · det(1 − zD)`. -/
theorem fredholmDet_blockOp_lower {A : E →L[𝕜] E} {C : E →L[𝕜] F} {D : F →L[𝕜] F}
    (hA : IsTraceClass A) (hC : IsRectTraceClass C) (hD : IsTraceClass D) (z : 𝕜) :
    fredholmDet (blockOp A 0 C D) z = fredholmDet A z * fredholmDet D z := by
  have hP := isTraceClass_corner_inl_fst (F := F) hA.isRectTraceClass
  have hM := isTraceClass_corner_inr_fst hC
  have hR := isTraceClass_corner_inr_snd (E := E) hD.isRectTraceClass
  set P : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) := blockInl ∘L A ∘L blockFst with hPd
  set M : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) := blockInr ∘L C ∘L blockFst with hMd
  set R : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) := blockInr ∘L D ∘L blockSnd with hRd
  have hPMR : P ∘L (M + R) = 0 := by
    refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_ <;> simp [hPd, hMd, hRd]
  have hMR0 : M ∘L R = 0 := by
    refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_ <;> simp [hMd, hRd]
  have e1 : blockOp A 0 C D = P + (M + R) - z • (P ∘L (M + R)) := by
    rw [hPMR]
    refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_ <;> simp [hPd, hMd, hRd]
  have e2 : M + R = M + R - z • (M ∘L R) := by
    rw [hMR0]; refine ContinuousLinearMap.ext fun v => ?_; simp
  have hMR : traceENorm (M + R) ≠ ⊤ :=
    traceENorm_add_ne_top hM.traceENorm_ne_top hR.traceENorm_ne_top
  rw [e1, fredholmDet_add_sub_smul_comp hP.traceENorm_ne_top hMR z, e2,
    fredholmDet_add_sub_smul_comp hM.traceENorm_ne_top hR.traceENorm_ne_top z,
    fredholmDet_corner_inl hP, fredholmDet_corner_inr hR, fredholmDet_corner_inr_fst hC]
  ring

/-! ### Block Schur (LU) step -/

/-- **Block Schur / LU factorization of the determinant.**  Let `A` be trace class with a
bounded left inverse `R` of `1 − A` (`R (1 − A) = 1`), `B`, `C` rectangular trace class, and
assume the Schur complement block `Z = D + C R B` is trace class.  Then
`det(1 − [[A, B], [C, D]]) = det(1 − A) · det(1 − Z)`.

Proof: `[[A, B], [C, D]] = M + W − MW` with `M = [[0, 0], [CR, 0]]` and `W = [[A, B], [0, Z]]`
(i.e. `1 − 𝒦 = (1 − M)(1 − W)`), multiplicativity, `det(1 − M) = 1` and the upper-triangular
formula for `W`. -/
theorem fredholmDet_blockOp_schur {A : E →L[𝕜] E} {B : F →L[𝕜] E} {C : E →L[𝕜] F}
    {D : F →L[𝕜] F} (hA : IsTraceClass A) (hB : IsRectTraceClass B) (hC : IsRectTraceClass C)
    {R : E →L[𝕜] E} (hR : R * (1 - A) = 1) (hZ : IsTraceClass (D + C ∘L R ∘L B)) :
    fredholmDet (blockOp A B C D) 1 = fredholmDet A 1 * fredholmDet (D + C ∘L R ∘L B) 1 := by
  have hRv : ∀ x, R x - R (A x) = x := fun x => by
    have h := congrArg (fun T : E →L[𝕜] E => T x) hR
    simpa [map_sub] using h
  set Z : F →L[𝕜] F := D + C ∘L R ∘L B with hZd
  have hCR : IsRectTraceClass (C ∘L R) := hC.comp_right R
  have hM := traceENorm_blockOp_ne_top (isRectTraceClass_zero (E := E) (F := E))
    (isRectTraceClass_zero (E := E) (F := F)) hCR (isRectTraceClass_zero (E := F) (F := F))
  have hW := traceENorm_blockOp_ne_top hA.isRectTraceClass hB
    (isRectTraceClass_zero (E := F) (F := E)) hZ.isRectTraceClass
  have e : blockOp A B C D = blockOp 0 0 (C ∘L R) 0 + blockOp A B 0 Z -
      blockOp 0 0 (C ∘L R) 0 ∘L blockOp A B 0 Z := by
    refine ContinuousLinearMap.ext fun v => wlp_ext ?_ ?_
    · simp
    · simp only [blockOp_apply_snd, sub_apply,
        add_apply, ContinuousLinearMap.comp_apply, WithLp.sub_snd,
        WithLp.add_snd, blockOp_apply_fst, zero_apply, hZd, map_add]
      have h1 := hRv v.fst
      have h2 : C (R v.fst) - C (R (A v.fst)) = C v.fst := by rw [← map_sub, h1]
      rw [← h2]
      abel
  rw [e, fredholmDet_add_sub_comp hM hW,
    fredholmDet_blockOp_lower isTraceClass_zero hCR isTraceClass_zero,
    fredholmDet_blockOp_upper hA hB hZ, fredholmDet_zero_op, fredholmDet_zero_op]
  ring

/-- A block operator with trace-class diagonal and rectangular trace-class off-diagonal blocks is
trace class on `WithLp 2 (E × F)` (uses `IsTraceClass.add`). -/
theorem isTraceClass_blockOp {A : E →L[𝕜] E} {B : F →L[𝕜] E} {C : E →L[𝕜] F} {D : F →L[𝕜] F}
    (hA : IsTraceClass A) (hB : IsRectTraceClass B) (hC : IsRectTraceClass C)
    (hD : IsTraceClass D) : IsTraceClass (blockOp A B C D) :=
  (((isTraceClass_corner_inl_fst hA.isRectTraceClass).add (isTraceClass_corner_inl_snd hB)).add
    (isTraceClass_corner_inr_fst hC)).add (isTraceClass_corner_inr_snd hD.isRectTraceClass)

/-- **Block Schur step, unconditional form**: for trace-class `A`, `D`, rectangular trace-class
`B`, `C`, and a bounded left inverse `R` of `1 − A`,
`det(1 − [[A, B], [C, D]]) = det(1 − A) · det(1 − (D + C R B))`.  (The Schur complement is
trace class by `IsTraceClass.add`.) -/
theorem fredholmDet_blockOp_schur' {A : E →L[𝕜] E} {B : F →L[𝕜] E} {C : E →L[𝕜] F}
    {D : F →L[𝕜] F} (hA : IsTraceClass A) (hB : IsRectTraceClass B) (hC : IsRectTraceClass C)
    (hD : IsTraceClass D) {R : E →L[𝕜] E} (hR : R * (1 - A) = 1) :
    fredholmDet (blockOp A B C D) 1 = fredholmDet A 1 * fredholmDet (D + C ∘L R ∘L B) 1 :=
  fredholmDet_blockOp_schur hA hB hC hR (hD.add (hC.isTraceClass_comp (R ∘L B)))

/-- The Schur step with `R = (1 − A)⁻¹` supplied by `‖A‖ < 1` (Neumann series,
`Units.oneSub`). -/
theorem fredholmDet_blockOp_schur_of_norm_lt_one {A : E →L[𝕜] E} {B : F →L[𝕜] E}
    {C : E →L[𝕜] F} {D : F →L[𝕜] F} (hA : IsTraceClass A) (hB : IsRectTraceClass B)
    (hC : IsRectTraceClass C) (hD : IsTraceClass D) (hAn : ‖A‖ < 1) :
    fredholmDet (blockOp A B C D) 1 = fredholmDet A 1 *
      fredholmDet (D + C ∘L ((↑(Units.oneSub A hAn)⁻¹ : E →L[𝕜] E)) ∘L B) 1 :=
  fredholmDet_blockOp_schur' hA hB hC hD (by
    rw [← Units.val_oneSub A hAn]
    exact (Units.oneSub A hAn).inv_mul)

/-! ### Trace of a block operator -/

/-- Equal entire determinants (on possibly different spaces) force equal traces. -/
theorem trace_eq_of_fredholmDet_eq_rect {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    (hA : IsTraceClass A) (hB : IsTraceClass B) (h : fredholmDet A = fredholmDet B) :
    trace A = trace B := by
  have hpA := hasFPowerSeriesAt_fredholmDet hA
  have hpB := hasFPowerSeriesAt_fredholmDet hB
  rw [h] at hpA
  have hp := hpA.eq_formalMultilinearSeries hpB
  have h1 := congrArg (fun p : FormalMultilinearSeries 𝕜 𝕜 𝕜 => p.coeff 1) hp
  simp only [FormalMultilinearSeries.coeff_ofScalars,
    fredholmDetCoeff_one_eq_neg_trace hA, fredholmDetCoeff_one_eq_neg_trace hB] at h1
  exact neg_injective h1

theorem trace_corner_inl {T : E →L[𝕜] E} (hT : IsTraceClass T) :
    trace (blockInl ∘L T ∘L blockFst : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) = trace T :=
  trace_eq_of_fredholmDet_eq_rect (isTraceClass_corner_inl_fst hT.isRectTraceClass) hT
    (funext (fredholmDet_corner_inl (isTraceClass_corner_inl_fst hT.isRectTraceClass)))

theorem trace_corner_inr {T : F →L[𝕜] F} (hT : IsTraceClass T) :
    trace (blockInr ∘L T ∘L blockSnd : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)) = trace T :=
  trace_eq_of_fredholmDet_eq_rect (isTraceClass_corner_inr_snd hT.isRectTraceClass) hT
    (funext (fredholmDet_corner_inr (isTraceClass_corner_inr_snd hT.isRectTraceClass)))

/-- **Trace of a block operator**: `tr [[A, B], [C, D]] = tr A + tr D`. -/
theorem trace_blockOp {A : E →L[𝕜] E} {B : F →L[𝕜] E} {C : E →L[𝕜] F} {D : F →L[𝕜] F}
    (hA : IsTraceClass A) (hB : IsRectTraceClass B) (hC : IsRectTraceClass C)
    (hD : IsTraceClass D) : trace (blockOp A B C D) = trace A + trace D := by
  set b := canonicalBasis 𝕜 (WithLp 2 (E × F))
  have s1 := summable_inner_diagonal (isTraceClass_corner_inl_fst (F := F) hA.isRectTraceClass) b
  have s2 := summable_inner_diagonal (isTraceClass_corner_inl_snd hB) b
  have s3 := summable_inner_diagonal (isTraceClass_corner_inr_fst hC) b
  have s4 := summable_inner_diagonal
    (isTraceClass_corner_inr_snd (E := E) hD.isRectTraceClass) b
  have hsum : ∀ (S T : WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F)),
      (Summable fun i => ⟪b i, S (b i)⟫_𝕜) → (Summable fun i => ⟪b i, T (b i)⟫_𝕜) →
      Summable fun i => ⟪b i, (S + T) (b i)⟫_𝕜 := fun S T hS hT =>
    (hS.add hT).congr fun i => by rw [add_apply, inner_add_right]
  unfold blockOp
  rw [trace_add_of_summable (hsum _ _ (hsum _ _ s1 s2) s3) s4,
    trace_add_of_summable (hsum _ _ s1 s2) s3, trace_add_of_summable s1 s2,
    trace_corner_inl hA, trace_corner_inl_snd hB, trace_corner_inr_fst hC, trace_corner_inr hD]
  ring

end Block

end HilbertSchmidt
