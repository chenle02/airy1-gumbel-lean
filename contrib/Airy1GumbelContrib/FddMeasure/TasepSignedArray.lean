/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FddMeasure.TasepTransition
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Fin.Tuple.Finset

open Filter Function Matrix MeasureTheory Set
open scoped BigOperators ENNReal

/-!
# Signed interlacing arrays for finite backward sequential TASEP

Finite differences contract the signed arrays to their physical marginals.
The principal minors of the layer matrix enumerate those arrays, including
a mandatory virtual site at each level. A complementary minor of the inverse
then gives the finite gap determinant.
-/

namespace AiryFdd

/-- A level of size `k + 1` is indexed from its leftmost entry to its rightmost entry. -/
abbrev TasepArray (m : ℕ) :=
  (k : Fin m) → Fin (k.1 + 1) → ℤ

/-- The terminal determinant has no entries below the smallest initial position on its
leftmost row. Every terminal row is supported below the rightmost position plus `N`. -/
def tasepCropLo {m : ℕ} (y : Fin m → ℤ) : ℤ :=
  if h : 0 < m then y ⟨m - 1, by omega⟩ else 0

def tasepCropHi {m : ℕ} (N : ℕ) (y : Fin m → ℤ) : ℤ :=
  if h : 0 < m then y ⟨0, h⟩ + N else 0

/-- Strictly ordered rows with the half-open inequalities (B_i<A_i≤B_{i+1}) between
each row `A` and the next row `B`, in the convention of Borodin–Ferrari–Prähofer–Sasamoto. -/
def tasepInterlaces {m : ℕ} (A : TasepArray m) : Prop :=
  (∀ k, StrictMono (A k)) ∧
    ∀ k (hk : k + 1 < m) (i : Fin (k + 1)),
      A ⟨k + 1, hk⟩ i.castSucc < A ⟨k, by omega⟩ i ∧
        A ⟨k, by omega⟩ i ≤ A ⟨k + 1, hk⟩ i.succ

/-- The finite crop of interlacing arrays used for a system starting at `y`. -/
noncomputable def tasepArrayCrop {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    Finset (TasepArray m) :=
  open Classical in
  let C := (Finset.Icc (tasepCropLo y) (tasepCropHi N y) : Finset ℤ)
  ((Finset.univ : Finset ((k : Fin m) → Fin (k.1 + 1) → C)).image
      (fun A k i => (A k i).1)).filter tasepInterlaces

/-- The leftmost site at each level is a physical particle, in decreasing order of position. -/
def tasepArrayPositions {m : ℕ} (A : TasepArray m) : Fin m → ℤ :=
  fun k => A k ⟨0, by omega⟩

/-- The signed interlacing-array weight of Borodin–Ferrari–Prähofer–Sasamoto. On ordered
interlacing arrays the product of adjacent-level determinants is one, and the terminal
determinant has row `i`, column `j` entry `F₋ⱼ(Aᵢ−Yⱼ)`, with initial positions
`Y` ordered from left to right. Invalid arrays have weight zero. -/
noncomputable def signedArrayWeight {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (A : (k : Fin m) → Fin (k.1 + 1) → ℤ) : ℝ :=
  open Classical in
  if tasepInterlaces A then
    Matrix.det (Matrix.of (fun i j : Fin m =>
      tasepF (-(j.1 : ℤ))
        ((if h : 0 < m then A ⟨m - 1, by omega⟩ ⟨i.1, by change i.1 < m - 1 + 1; have := i.2; omega⟩ else 0) - y j.rev) N))
  else 0

/-- The finite ambient lattice of level-tagged, cropped sites. -/
abbrev TasepFiniteSite {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :=
  Fin m × ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y))

/-- The sites forbidden by the event that the selected particle positions are at least
their integer cutoffs. The forbidden side is strictly below the cutoff. -/
def finiteBadSites {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (J : Finset (Fin m)) (a : J → ℤ) : Finset (TasepFiniteSite N y) :=
  Finset.univ.filter fun p => if h : p.1 ∈ J then p.2.1 < a ⟨p.1, h⟩ else False

/-- One layer of the strictly ordered interlacing transfer. -/
noncomputable def finiteLevelTransfer {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    Matrix (TasepFiniteSite N y) (TasepFiniteSite N y) ℝ :=
  Matrix.of (fun p q => if q.1.1 = p.1.1 + 1 ∧ q.2.1 < p.2.1 then 1 else 0)

/-- Birth of one virtual particle at each level. -/
noncomputable def finiteLevelBirth {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    Matrix (Fin m) (TasepFiniteSite N y) ℝ :=
  Matrix.of fun i p => if i = p.1 then 1 else 0

/-- Terminal signed functions placed on the last level. -/
noncomputable def finiteLevelTerminal {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    Matrix (TasepFiniteSite N y) (Fin m) ℝ :=
  Matrix.of fun p j => if p.1.1 + 1 = m then tasepF (-(j.1 : ℤ)) (p.2.1 - y j.rev) N else 0

/-- The finite nilpotent propagation through the level set. -/
noncomputable def finiteLevelPropagation {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    Matrix (TasepFiniteSite N y) (TasepFiniteSite N y) ℝ :=
  ∑ k ∈ Finset.range (m + 1), finiteLevelTransfer N y ^ k

/-- The biorthogonal finite-system correlation kernel, restricted to the forbidden sites.
The inverse overlap matrix pairs the propagated birth rows with the terminal columns. -/
noncomputable def finiteLevelKernel {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (J : Finset (Fin m)) (a : J → ℤ) :
    Matrix (finiteBadSites N y J a) (finiteBadSites N y J a) ℝ :=
  let R := finiteLevelPropagation N y
  let B := finiteLevelBirth N y
  let C := finiteLevelTerminal N y
  (1 - R + R * C * (B * R * C)⁻¹ * B * R).submatrix Subtype.val Subtype.val


theorem tasepArrayCrop_mem_iff {m : ℕ} (N : ℕ) (y : Fin m → ℤ) (A : TasepArray m) :
    A ∈ tasepArrayCrop N y ↔ tasepInterlaces A ∧
      ∀ k i, A k i ∈ Finset.Icc (tasepCropLo y) (tasepCropHi N y) := by
  classical
  unfold tasepArrayCrop
  rw [Finset.mem_filter]
  refine and_comm.trans (?_ : _)
  constructor
  · rintro ⟨h, hC⟩
    refine ⟨h, ?_⟩
    obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hC
    exact fun k i => (B k i).2
  · rintro ⟨h, hC⟩
    exact ⟨h, Finset.mem_image.mpr ⟨fun k i => ⟨A k i, hC k i⟩, Finset.mem_univ _, rfl⟩⟩

theorem tasepArrayPositions_strictAnti {m : ℕ} (A : TasepArray m) (hA : tasepInterlaces A) :
    StrictAnti (tasepArrayPositions A) := by
  cases m with
  | zero => exact fun {_} i _ => Fin.elim0 i
  | succ m =>
    refine Fin.strictAnti_iff_succ_lt.mpr fun i => ?_
    exact (hA.2 i.1 (by have := i.2; omega) (0 : Fin (i.1 + 1))).1

theorem tasep_sum_Ico_diff (f : ℤ → ℝ) {l u : ℤ} (hlu : l ≤ u) :
    ∑ z ∈ Finset.Ico l u, (f z - f (z + 1)) = f l - f u := by
  have he : u = l + ((u-l).toNat : ℤ) := by omega
  rw [he]
  generalize (u - l).toNat = n
  induction n with
  | zero => simp
  | succ n ih =>
    have hset : Finset.Ico l (l + ((n + 1 : ℕ) : ℤ)) =
        insert (l + (n : ℤ)) (Finset.Ico l (l + (n : ℤ))) := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_Ico, Nat.cast_add, Nat.cast_one]
      omega
    rw [hset, Finset.sum_insert (by simp), ih]
    rw [show l + ((n + 1 : ℕ) : ℤ) = l + (n : ℤ) + 1 by omega]
    ring

/-- A one-sided kernel sum over an integer crop, with the final term beyond the
kernel's upper support. -/
theorem tasepF_sum_Icc {j l u y : ℤ} (N : ℕ) (hlu : l ≤ u) (hu : y + N ≤ u) :
    ∑ z ∈ Finset.Icc l u, tasepF j (z - y) N = tasepF (j + 1) (l - y) N := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  have h (a : ℤ) :
      tasepF j (a - y) N =
        tasepF (j + 1) (a - y) N - tasepF (j + 1) ((a + 1) - y) N := by
    have ht := tasepF_sub_succ (j + 1) (a - y) N
    rw [add_sub_cancel_right, show a - y + 1 = a + 1 - y by ring] at ht
    exact ht
  simp_rw [h]
  have hl : l ≤ u + 1 := by omega
  have he := tasep_sum_Ico_diff (fun z => tasepF (j + 1) (z - y) N) hl
  have hend : tasepF (j + 1) (u + 1 - y) N = 0 := tasepF_eq_zero_above _ _ (by omega)
  linarith

theorem tasepF_sum_Ico {j l u y : ℤ} (N : ℕ) (hlu : l ≤ u) :
    ∑ z ∈ Finset.Ico l u, tasepF j (z - y) N =
      tasepF (j + 1) (l - y) N - tasepF (j + 1) (u - y) N := by
  have h (a : ℤ) :
      tasepF j (a - y) N =
        tasepF (j + 1) (a - y) N - tasepF (j + 1) ((a + 1) - y) N := by
    have ht := tasepF_sub_succ (j + 1) (a - y) N
    rw [add_sub_cancel_right, show a - y + 1 = a + 1 - y by ring] at ht
    exact ht
  simp_rw [h]
  have he := tasep_sum_Ico_diff (fun z => tasepF (j + 1) (z - y) N) hlu
  linarith

/-- Sum a determinant over independent choices of each row. -/
theorem tasepDet_sum_row_grid {m : ℕ} (s : Fin m → Finset ℤ)
    (a : Fin m → ℤ → Fin m → ℝ) :
    (∑ z ∈ Fintype.piFinset s, Matrix.det (Matrix.of (fun i j => a i (z i) j))) =
      Matrix.det (Matrix.of (fun i j => ∑ v ∈ s i, a i v j)) := by
  have h := (Matrix.detRowAlternating (n := Fin m) (R := ℝ)).toMultilinearMap.map_sum_finset a s
  calc
    _ = ∑ z ∈ Fintype.piFinset s, Matrix.detRowAlternating (fun i => a i (z i)) := rfl
    _ = Matrix.detRowAlternating (fun i => ∑ v ∈ s i, a i v) := h.symm
    _ = _ := by
      apply congrArg Matrix.detRowAlternating
      funext i j
      exact Finset.sum_apply _ _ _

/-- Convolution support increases by the number of strictly upper-triangular steps. -/
theorem finiteLevelTransfer_pow_zero {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (k : ℕ) (p q : TasepFiniteSite N y) (h : p.1.1 + k ≠ q.1.1) :
    (finiteLevelTransfer N y ^ k) p q = 0 := by
  classical
  induction k generalizing p q with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    apply ite_eq_right
    intro he
    exact h (by simp [he])
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro r _
    by_cases he : r.1.1 + 1 = q.1.1
    · rw [ih p r (by omega), zero_mul]
    · unfold finiteLevelTransfer
      simp [Matrix.of_apply, show ¬q.1.1 = r.1.1 + 1 by omega]

theorem finiteLevelTransfer_nilpotent {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    finiteLevelTransfer N y ^ (m + 1) = 0 := by
  ext p q
  change (finiteLevelTransfer N y ^ (m + 1)) p q = 0
  exact finiteLevelTransfer_pow_zero N y (m + 1) p q (by have := q.1.2; omega)


/-- The principal determinant is independent of the finite enumeration. -/
theorem tasepDet_instance_eq {ι : Type*} (A : Matrix ι ι ℝ)
    (d₁ d₂ : DecidableEq ι) (f₁ f₂ : Fintype ι) :
    @Matrix.det ι d₁ f₁ ℝ _ A = @Matrix.det ι d₂ f₂ ℝ _ A := by
  cases (Subsingleton.elim d₁ d₂)
  cases (Subsingleton.elim f₁ f₂)
  rfl

/-- Replacing rows outside the retained set by diagonal rows leaves the retained
principal determinant times the product of the other diagonal entries. -/
theorem tasepDet_piecewise_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (S : Finset ι) (d : ι → ℝ) :
    Matrix.det (Matrix.of (S.piecewise A (Matrix.diagonal d))) =
      Matrix.det (A.toSquareBlockProp (fun i => i ∈ S)) * ∏ i ∈ Sᶜ, d i := by
  let M : Matrix ι ι ℝ := Matrix.of (S.piecewise A (Matrix.diagonal d))
  change M.det = _
  have h₀ : ∀ i, i ∉ S → ∀ j, j ∈ S → M i j = 0 := by
    intro i hi j hj
    have hne : i ≠ j := fun he => hi (he.symm ▸ hj)
    simp [M, Matrix.of_apply, Finset.piecewise, hi, Matrix.diagonal_apply_ne, hne]
  have hAA : M.toSquareBlockProp (fun i => i ∈ S) = A.toSquareBlockProp (fun i => i ∈ S) := by
    ext i j
    change M i.1 j.1 = A i.1 j.1
    simp [M, Matrix.of_apply, Finset.piecewise, i.2]
  have hDD : M.toSquareBlockProp (fun i => i ∉ S) = Matrix.diagonal (fun i => d i.1) := by
    ext i j
    change M i.1 j.1 = Matrix.diagonal (fun i : {i // i ∉ S} => d i.1) i j
    by_cases hij : i = j
    · subst j
      simp [M, Matrix.of_apply, Finset.piecewise, i.2]
    · have hd : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [M, Matrix.of_apply, Finset.piecewise, i.2, Matrix.diagonal_apply_ne, hd, hij]
  rw [M.twoBlockTriangular_det (fun i => i ∈ S) h₀, hAA, hDD, Matrix.det_diagonal]
  refine congrArg₂ (· * ·) (tasepDet_instance_eq _ _ _ _ _) ?_
  exact (Finset.prod_subtype Sᶜ (fun _ => Finset.mem_compl) d).symm

/-- Principal-minor expansion about a possibly zero diagonal. A zero diagonal on
a virtual vertex forces that vertex to be retained. -/
theorem tasepDet_add_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) :
    (A + Matrix.diagonal d).det =
      ∑ S ∈ (Finset.univ : Finset ι).powerset,
        Matrix.det (A.toSquareBlockProp (fun i => i ∈ S)) * ∏ i ∈ Sᶜ, d i := by
  let f : MultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
    (Matrix.detRowAlternating (n := ι) (R := ℝ)).toMultilinearMap
  let V : ι → ι → ℝ := A
  let D : ι → ι → ℝ := Matrix.diagonal d
  have h := f.map_add_univ V D
  calc
    _ = f (V + D) := rfl
    _ = ∑ S ∈ (Finset.univ : Finset ι).powerset, f (S.piecewise V D) := h
    _ = _ := Finset.sum_congr rfl (fun S _ => tasepDet_piecewise_diagonal A S d)

theorem finiteLevelPropagation_mul {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    finiteLevelPropagation N y * (1 - finiteLevelTransfer N y) = 1 := by
  have h := geom_sum_mul (finiteLevelTransfer N y) (m + 1)
  unfold finiteLevelPropagation
  rw [show (1 - finiteLevelTransfer N y) = -(finiteLevelTransfer N y - 1) by abel,
    mul_neg, h, finiteLevelTransfer_nilpotent, zero_sub, neg_neg]

theorem finiteLevelPropagation_eq_inv {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    finiteLevelPropagation N y = (1 - finiteLevelTransfer N y)⁻¹ := by
  exact (Matrix.inv_eq_left_inv (finiteLevelPropagation_mul N y)).symm

theorem finiteLevelTransfer_det_one_sub {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    (1 - finiteLevelTransfer N y).det = 1 := by
  have hc : Matrix.BlockTriangular (1 - finiteLevelTransfer N y)
      (fun p : TasepFiniteSite N y => p.1.1) := by
    intro i j hij
    change j.1.1 < i.1.1 at hij
    have hn : i ≠ j := fun h => by simp [h] at hij
    rw [Matrix.sub_apply, Matrix.one_apply_ne hn]
    simp [finiteLevelTransfer, Matrix.of_apply, show ¬j.1.1 = i.1.1 + 1 by omega]
  rw [hc.det]
  apply Finset.prod_eq_one
  intro k _
  suffices (1 - finiteLevelTransfer N y).toSquareBlock (fun p : TasepFiniteSite N y => p.1.1) k = 1 by
    rw [this, Matrix.det_one]
  ext i j
  have ht : (i.1.1 : ℕ) = (j.1.1 : ℕ) := i.2.trans j.2.symm
  have hm : ¬(j.1.1 : ℕ) = (i.1.1 : ℕ) + 1 := by omega
  change (1 - finiteLevelTransfer N y) i.1 j.1 = _
  simp [Matrix.sub_apply, finiteLevelTransfer, Matrix.one_apply, Matrix.of_apply, hm, Subtype.coe_inj]


/-- The determinant of ordered prefix-indicator rows is one when they form
the full staircase, and zero otherwise. -/
theorem tasepDet_prefix_indicator {m : ℕ} (c : Fin m → ℕ)
    (hc : Monotone c) (hbound : ∀ i, c i ≤ m) :
    Matrix.det (Matrix.of (fun i j : Fin m => if j.1 < c i then (1 : ℝ) else 0)) =
      if ∀ i, c i = i.1 + 1 then 1 else 0 := by
  classical
  let A : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => if j.1 < c i then 1 else 0
  change A.det = _
  by_cases h : ∀ i, c i = i.1 + 1
  · rw [ite_eq_left h, Matrix.det_of_isLowerTriangular]
    · simp [A, Matrix.of_apply, h]
    · intro i j hij
      change (if j.1 < c i then (1 : ℝ) else 0) = 0
      have hij' : i.1 < j.1 := hij
      rw [h i, ite_eq_right (by omega)]
  · rw [ite_eq_right h]
    by_cases hz : ∃ i, c i = 0
    · obtain ⟨i, hi⟩ := hz
      exact Matrix.det_eq_zero_of_row_eq_zero i (by simp [A, Matrix.of_apply, hi])
    by_cases hdup : ∃ i j, i ≠ j ∧ c i = c j
    · obtain ⟨i, j, hne, he⟩ := hdup
      apply Matrix.det_zero_of_row_eq hne
      funext k
      simp [A, Matrix.of_apply, he]
    · exfalso
      apply h
      intro i
      have hmk : 0 < m := by have := i.2; omega
      let a : Fin m := ⟨0, hmk⟩
      let b : Fin m := ⟨m - 1, by omega⟩
      have hm : StrictMono c := by
        intro j k hjk
        refine lt_of_le_of_ne (hc hjk.le) ?_
        exact fun hEq => hdup ⟨j,k,hjk.ne,hEq⟩
      have hant : StrictAnti (fun j => -(c j : ℤ)) := by
        intro j k hjk
        have h' := hm hjk
        change -(c k : ℤ) < -(c j : ℤ)
        omega
      have hl := tasep_strictAnti_gap (fun j => -(c j : ℤ)) hant a i
        (show a.1 ≤ i.1 from Nat.zero_le _)
      have hu := tasep_strictAnti_gap (fun j => -(c j : ℤ)) hant i b
        (show i.1 ≤ b.1 by have := i.2; dsimp [b]; omega)
      have hza : c a ≠ 0 := fun he => hz ⟨a,he⟩
      have hzb := hbound b
      change -(c i : ℤ) + ((i.1 : ℤ) - 0) ≤ -(c a : ℤ) at hl
      change -(c b : ℤ) + ((↑(m - 1) : ℤ) - (i.1 : ℤ)) ≤ -(c i : ℤ) at hu
      omega

/-- For a strictly ordered tuple, the entries below a real threshold are an initial
segment of its index set. -/
theorem tasepFilter_prefix_iff {n : ℕ} (b : Fin n → ℤ) (hb : StrictMono b)
    (t : ℤ) (j : Fin n) :
    b j < t ↔ j.1 < (Finset.univ.filter fun i => b i < t).card := by
  let S := Finset.univ.filter fun i => b i < t
  change b j < t ↔ j.1 < S.card
  constructor
  · intro hj
    have hs : Finset.Iic j ⊆ S := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hb.monotone (Finset.mem_Iic.mp hi)).trans_lt hj⟩
    have h := Finset.card_le_card hs
    rw [Fin.card_Iic] at h
    omega
  · intro hj
    by_contra! h
    have hs : S ⊆ Finset.Iio j := by
      intro i hi
      apply Finset.mem_Iio.mpr
      by_contra! hji
      exact (not_lt_of_ge (h.trans (hb.monotone hji))) (Finset.mem_filter.mp hi).2
    have hh := Finset.card_le_card hs
    rw [Fin.card_Iio] at hh
    omega

/-- The adjacent-level determinant of the strict order transfer with a virtual row
of ones is the indicator of the half-open interlacing inequalities. -/
theorem tasepDet_interlace_transfer {n : ℕ} (a : Fin n → ℤ) (b : Fin (n + 1) → ℤ)
    (ha : StrictMono a) (hb : StrictMono b) :
    Matrix.det (Matrix.of (fun i j : Fin (n + 1) =>
      if h : i.1 < n then if b j < a ⟨i.1,h⟩ then (1 : ℝ) else 0 else 1)) =
        if ∀ i : Fin n, b i.castSucc < a i ∧ a i ≤ b i.succ then 1 else 0 := by
  let c (i : Fin (n + 1)) :=
    if h : i.1 < n then (Finset.univ.filter fun j => b j < a ⟨i.1,h⟩).card else n + 1
  have hc : Monotone c := by
    intro i j hij
    have hij' : i.1 ≤ j.1 := hij
    by_cases hj : j.1 < n
    · have hi : i.1 < n := lt_of_le_of_lt hij' hj
      simp only [c, dite_eq_left hj, dite_eq_left hi]
      exact Finset.card_le_card (by
        intro k hk
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact (Finset.mem_filter.mp hk).2.trans_le (ha.monotone hij))
    · have hbound (h : i.1 < n) : (Finset.univ.filter fun k => b k < a ⟨i.1,h⟩).card ≤ n+1 := by
        simpa using Finset.card_filter_le (Finset.univ : Finset (Fin (n + 1)))
          (fun (k : Fin (n + 1)) => b k < a ⟨i.1,h⟩)
      by_cases hi : i.1 < n <;> simp [c, hj, hi, hbound]
  have hbound (i : Fin (n + 1)) : c i ≤ n + 1 := by
    by_cases hi : i.1 < n
    · simp only [c, dite_eq_left hi]
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin (n + 1))) (fun k => b k < a ⟨i.1,hi⟩)
    · simp [c, hi]
  have hm : (Matrix.of (fun i j : Fin (n + 1) =>
      if h : i.1 < n then if b j < a ⟨i.1,h⟩ then (1 : ℝ) else 0 else 1)) =
      Matrix.of (fun i j : Fin (n + 1) => if j.1 < c i then (1 : ℝ) else 0) := by
    ext i j
    simp only [Matrix.of_apply]
    by_cases hi : i.1 < n
    · simp only [c, dite_eq_left hi]
      apply if_congr
      · exact tasepFilter_prefix_iff b hb _ j
      · simp
      · simp
    · simp [c, hi, j.2]
  rw [hm, tasepDet_prefix_indicator c hc hbound]
  congr 1
  apply propext
  constructor
  · intro h i
    have hp : c i.castSucc = i.1 + 1 := h i.castSucc
    have hi : i.castSucc.1 < n := i.2
    simp only [c, dite_eq_left hi] at hp
    change (Finset.univ.filter (fun j => b j < a i)).card = i.1 + 1 at hp
    refine ⟨(tasepFilter_prefix_iff b hb _ _).2 (by rw [hp]; exact Nat.lt_succ_self _), ?_⟩
    by_contra! hl
    have ht := (tasepFilter_prefix_iff b hb _ _).1 hl
    rw [hp] at ht
    change i.1 + 1 < i.1 + 1 at ht
    omega
  · intro h i
    by_cases hi : i.1 < n
    · let j : Fin n := ⟨i.1, hi⟩
      have h1 := (tasepFilter_prefix_iff b hb (a j) j.castSucc).1 (h j).1
      have h2 : ¬j.succ.1 < (Finset.univ.filter fun k => b k < a j).card :=
        fun ht => (not_lt_of_ge (h j).2) ((tasepFilter_prefix_iff b hb (a j) j.succ).2 ht)
      simp only [c, dite_eq_left hi]
      change (Finset.univ.filter (fun k => b k < a j)).card = j.1 + 1
      change j.1 < _ at h1
      change ¬j.1 + 1 < _ at h2
      omega
    · simp [c, show i.1 = n by have := i.2; omega]


/-- The principal determinant after removing a finite set equals the full
determinant times the complementary principal determinant of the inverse. -/
theorem tasepDet_complement_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (S : Finset ι) (hG : IsUnit G.det) :
    (G.toSquareBlockProp (fun i => i ∈ S)).det =
      G.det * (G⁻¹.toSquareBlockProp (fun i => i ∈ Sᶜ)).det := by
  let H : Matrix ι ι ℝ := Matrix.of (S.piecewise G (1 : Matrix ι ι ℝ))
  have hH : H.det = (G.toSquareBlockProp (fun i => i ∈ S)).det := by
    simpa [H] using tasepDet_piecewise_diagonal G S (fun _ => 1)
  have hprod : H * G⁻¹ = Matrix.of (Sᶜ.piecewise (G⁻¹ : Matrix ι ι ℝ) (1 : Matrix ι ι ℝ)) := by
    ext i j
    by_cases hi : i ∈ S
    · have hm := congrArg (fun A : Matrix ι ι ℝ => A i j) (G.mul_nonsing_inv hG)
      simpa only [H, Matrix.mul_apply, Matrix.of_apply, Finset.piecewise, hi,
        Finset.mem_compl, not_true_eq_false, ite_true, ite_false] using hm
    · have hm := congrArg (fun A : Matrix ι ι ℝ => A i j) (Matrix.one_mul (G⁻¹))
      simpa only [H, Matrix.mul_apply, Matrix.of_apply, Finset.piecewise, hi,
        Finset.mem_compl, not_false_eq_true, ite_true, ite_false] using hm
  have h := congrArg Matrix.det hprod
  rw [Matrix.det_mul, hH] at h
  have h₂ : (Matrix.of (Sᶜ.piecewise (G⁻¹ : Matrix ι ι ℝ) (1 : Matrix ι ι ℝ))).det =
      (G⁻¹.toSquareBlockProp (fun i => i ∈ Sᶜ)).det := by
    simpa using tasepDet_piecewise_diagonal G⁻¹ Sᶜ (fun _ => 1)
  rw [h₂] at h
  calc
    _ = (G.toSquareBlockProp (fun i => i ∈ S)).det * (G⁻¹.det * G.det) := by
      rw [G.det_nonsing_inv_mul_det hG, mul_one]
    _ = _ := by rw [← mul_assoc, h, mul_comm]

/-- The auxiliary matrix with one mandatory virtual vertex per level. The
unweighted diagonal is present only on the finite physical lattice. -/
noncomputable def finiteLevelAnchor {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    Matrix (Fin m ⊕ TasepFiniteSite N y) (Fin m ⊕ TasepFiniteSite N y) ℝ :=
  Matrix.fromBlocks 0 (finiteLevelBirth N y) (finiteLevelTerminal N y)
    (1 - finiteLevelTransfer N y)

/-- The retained indices are the virtual vertices and all physical sites not
forbidden by the gap event. -/
noncomputable def finiteLevelAllowed {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (J : Finset (Fin m)) (a : J → ℤ) : Finset (Fin m ⊕ TasepFiniteSite N y) :=
  open Classical in Finset.univ.filter (Sum.elim (fun _ => True) (fun p => p ∉ finiteBadSites N y J a))

theorem finiteLevelAnchor_det {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    (finiteLevelAnchor N y).det =
      (-(finiteLevelBirth N y * finiteLevelPropagation N y * finiteLevelTerminal N y)).det := by
  let D := 1 - finiteLevelTransfer N y
  have hd : D.det = 1 := finiteLevelTransfer_det_one_sub N y
  have unitD : IsUnit D.det := by rw [hd]; exact isUnit_one
  let _ : Invertible D := ((Matrix.isUnit_iff_isUnit_det D).mpr unitD).invertible
  unfold finiteLevelAnchor
  change (Matrix.fromBlocks 0 (finiteLevelBirth N y) (finiteLevelTerminal N y) D).det = _
  rw [Matrix.det_fromBlocks₂₂, hd, one_mul, zero_sub, Matrix.invOf_eq_nonsing_inv]
  rw [finiteLevelPropagation_eq_inv]

theorem finiteLevelAnchor_inv_site {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (hG : IsUnit (finiteLevelAnchor N y).det) :
    (finiteLevelAnchor N y)⁻¹.toBlocks₂₂ =
      let R := finiteLevelPropagation N y
      let B := finiteLevelBirth N y
      let C := finiteLevelTerminal N y
      R - R * C * (B * R * C)⁻¹ * B * R := by
  let D := 1 - finiteLevelTransfer N y
  let B := finiteLevelBirth N y
  let C := finiteLevelTerminal N y
  let R := finiteLevelPropagation N y
  have hd : IsUnit D.det := by
    change IsUnit (1 - finiteLevelTransfer N y).det
    rw [finiteLevelTransfer_det_one_sub]; exact isUnit_one
  let _ : Invertible D := ((Matrix.isUnit_iff_isUnit_det D).mpr hd).invertible
  have hR : ⅟D = R := (Matrix.invOf_eq_nonsing_inv D).trans (finiteLevelPropagation_eq_inv N y).symm
  let G := Matrix.fromBlocks 0 B C D
  have hg : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).mpr hG
  have hM : IsUnit (0 - B * ⅟D * C).det := by
    rw [hR, zero_sub]
    exact (finiteLevelAnchor_det N y) ▸ hG
  let _ : Invertible (0 - B * ⅟D * C) := ((Matrix.isUnit_iff_isUnit_det _).mpr hM).invertible
  let _ : Invertible G := hg.invertible
  change G⁻¹.toBlocks₂₂ = R - R * C * (B * R * C)⁻¹ * B * R
  have hBlock := Matrix.invOf_fromBlocks₂₂_eq (0 : Matrix (Fin m) (Fin m) ℝ) B C D
  have h22 := congrArg Matrix.toBlocks₂₂ hBlock
  change (⅟G).toBlocks₂₂ = _ at h22
  rw [← Matrix.invOf_eq_nonsing_inv, h22]
  change ⅟D + ⅟D * C * ⅟(0 - B * ⅟D * C) * B * ⅟D = _
  rw [Matrix.invOf_eq_nonsing_inv (0 - B * ⅟D * C), hR, zero_sub]
  have hM' : IsUnit (B * R * C).det := by
    rw [hR, zero_sub] at hM
    exact (Matrix.isUnit_iff_isUnit_det (B * R * C)).mp
      ((IsUnit.neg_iff _).mp ((Matrix.isUnit_iff_isUnit_det (-(B * R * C))).mpr hM))
  have hInv : (-(B * R * C))⁻¹ = -((B * R * C)⁻¹) :=
    Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul _ hM'])
  rw [hInv]
  simp only [Matrix.mul_neg, Matrix.neg_mul, ← sub_eq_add_neg]

/-- Take successive differences in a suffix of the rows of a square matrix. -/
noncomputable def tasepRowDifference {m : ℕ} (p : ℕ) (A : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => if h : p ≤ i.1 ∧ i.1 + 1 < m then
    A i j - A ⟨i.1 + 1, h.2⟩ j else A i j

theorem tasepRowDifference_det {m : ℕ} (p : ℕ) (A : Matrix (Fin m) (Fin m) ℝ) :
    (tasepRowDifference p A).det = A.det := by
  let R : Matrix (Fin m) (Fin m) ℝ :=
    1 - Matrix.of (fun i j => if p ≤ i.1 ∧ i.1 + 1 = j.1 then 1 else 0)
  have hr : R.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · simp [R, Matrix.sub_apply]
    · intro i j hj
      have hji : j.1 < i.1 := hj
      have hne : i ≠ j := fun h => by rw [h] at hji; exact (lt_irrefl _ hji)
      simp [R, Matrix.sub_apply, Matrix.one_apply_ne hne, Matrix.of_apply,
        show i.1 + 1 ≠ j.1 by omega]
  let U : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.of fun i j => if p ≤ i.1 ∧ i.1 + 1 = j.1 then 1 else 0
  have hRA : R * A = A - U * A := by
    change (1 - U) * A = _
    rw [sub_mul, Matrix.one_mul]
  have hA : R * A = tasepRowDifference p A := by
    rw [hRA]
    ext i j
    simp only [Matrix.sub_apply, tasepRowDifference, U, Matrix.of_apply, Matrix.mul_apply]
    by_cases hi : p ≤ i.1 ∧ i.1 + 1 < m
    · rw [dite_eq_left hi, Finset.sum_eq_single ⟨i.1 + 1, hi.2⟩]
      · simp [hi.1]
      · intro k _ hk
        have hh : i.1 + 1 ≠ k.1 := fun h => hk (Fin.ext h.symm)
        simp [hh]
      · simp
    · rw [dite_eq_right hi, Finset.sum_eq_zero, sub_zero]
      intro k _
      simp [show ¬(p ≤ i.1 ∧ i.1 + 1 = k.1) from fun h => hi ⟨h.1, h.2.symm ▸ k.2⟩]
  rw [← hA, Matrix.det_mul, hr, one_mul]

/-- A stage of terminal-row summation. There are `p` already fixed rows at the
physical particle positions in reverse order. The remaining rows are all at
the current index `p` of the propagated kernel. -/
noncomputable def tasepRowStage {m : ℕ} (N : ℕ) (y z : Fin m → ℤ) (p : ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => tasepF (((min p i.1 : ℕ) : ℤ) - j.1) (z i - y j.rev) N

/-- In a row-summation step the already determined coordinates are singletons.
The live coordinates lie in consecutive intervals of the preceding row. -/
def tasepRowStageGrid {m : ℕ} (N : ℕ) (y x a : Fin m → ℤ) (p : ℕ)
    (i : Fin m) : Finset ℤ :=
  if i.1 ≤ p then {x i.rev}
  else if h : i.1 + 1 < m then Finset.Ico (a i) (a ⟨i.1 + 1, h⟩)
  else Finset.Icc (a i) (tasepCropHi N y)

/-- Integrating the terminal row over its interlacing intervals advances the
kernel index of every remaining live row. The interval differences cancel
through a triangular row operation. -/
theorem tasepRowStage_contract {m : ℕ} (N : ℕ) (y x a : Fin m → ℤ) (p : ℕ)
    (hy : StrictAnti y)
    (ha : ∀ i j : Fin m, p < i.1 → i ≤ j → a i ≤ a j)
    (hupper : ∀ i : Fin m, p < i.1 → a i ≤ tasepCropHi N y) :
    (∑ z ∈ Fintype.piFinset (tasepRowStageGrid N y x a p),
      (tasepRowStage N y z p).det) =
      (tasepRowStage N y (fun i => if i.1 ≤ p then x i.rev else a i) (p + 1)).det := by
  let W := tasepRowStage N y (fun i => if i.1 ≤ p then x i.rev else a i) (p + 1)
  have hsum := tasepDet_sum_row_grid (tasepRowStageGrid N y x a p)
    (fun i v j => tasepF (((min p i.1 : ℕ) : ℤ) - j.1) (v - y j.rev) N)
  change (∑ z ∈ Fintype.piFinset (tasepRowStageGrid N y x a p), (tasepRowStage N y z p).det) = _ at hsum
  rw [hsum]
  have hm : Matrix.of (fun i j : Fin m => ∑ v ∈ tasepRowStageGrid N y x a p i,
      tasepF (((min p i.1 : ℕ) : ℤ) - j.1) (v - y j.rev) N) = tasepRowDifference (p + 1) W := by
    ext i j
    simp only [Matrix.of_apply, tasepRowStageGrid, tasepRowDifference]
    by_cases hp : i.1 ≤ p
    · have hd : ¬(p + 1 ≤ i.1 ∧ i.1 + 1 < m) := by omega
      rw [ite_eq_left hp, dite_eq_right hd, Finset.sum_singleton]
      simp only [W, tasepRowStage, Matrix.of_apply, hp, ite_true, min_eq_right hp,
        min_eq_right (le_trans hp (Nat.le_succ p))]
    · have hpi : p + 1 ≤ i.1 := by omega
      have hpmin : min p i.1 = p := min_eq_left (by omega)
      have hdmin : min (p + 1) i.1 = p + 1 := min_eq_left hpi
      by_cases hi : i.1 + 1 < m
      · let k : Fin m := ⟨i.1 + 1, hi⟩
        have hpk : ¬k.1 ≤ p := by change ¬i.1 + 1 ≤ p; omega
        have hkmin : min (p + 1) k.1 = p + 1 := min_eq_left (by change p + 1 ≤ i.1 + 1; omega)
        have hle := ha i k (by omega) (show i.1 ≤ k.1 by change i.1 ≤ i.1 + 1; omega)
        rw [ite_eq_right hp, dite_eq_left hi, dite_eq_left ⟨hpi, hi⟩, hpmin]
        change (∑ v ∈ Finset.Ico (a i) (a k), tasepF ((p : ℤ) - j.1) (v - y j.rev) N) =
          W i j - W k j
        rw [tasepF_sum_Ico N hle]
        simp only [W, tasepRowStage, Matrix.of_apply, hp, hpk, ite_false, hdmin, hkmin, Nat.cast_add,
          Nat.cast_one]
        rw [show (p : ℤ) - (j.1 : ℤ) + 1 = (p : ℤ) + 1 - (j.1 : ℤ) by ring]
      · have hU : y j.rev + N ≤ tasepCropHi N y := by
          have hm : 0 < m := by have := j.2; omega
          rw [tasepCropHi, dite_eq_left hm]
          exact add_le_add (hy.antitone (show (⟨0, hm⟩ : Fin m) ≤ j.rev from Nat.zero_le _)) le_rfl
        rw [ite_eq_right hp, dite_eq_right hi, dite_eq_right (fun h => hi h.2), hpmin]
        rw [tasepF_sum_Icc N (hupper i (by omega)) hU]
        simp only [W, tasepRowStage, Matrix.of_apply, hp, ite_false, hdmin, Nat.cast_add, Nat.cast_one]
        rw [show (p : ℤ) - (j.1 : ℤ) + 1 = (p : ℤ) + 1 - (j.1 : ℤ) by ring]
  rw [hm, tasepRowDifference_det]


/-- A tuple of cropped coordinates at each level in a prefix of the array. -/
abbrev TasepCroppedPrefix {m : ℕ} (N : ℕ) (y : Fin m → ℤ) (d : ℕ) :=
  (k : Fin d) → Fin (k.1 + 1) → ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y))

def tasepPrefixValues {m d : ℕ} {N : ℕ} {y : Fin m → ℤ}
    (A : TasepCroppedPrefix N y d) : TasepArray d :=
  fun k i => (A k i).1

/-- Fix the physical coordinates at all levels of a cropped prefix. -/
def tasepPrefixFixed {m d : ℕ} {N : ℕ} {y : Fin m → ℤ}
    (A : TasepCroppedPrefix N y d) (x : Fin m → ℤ) (hd : d ≤ m) : Prop :=
  ∀ k : Fin d, (A k 0).1 = x (Fin.castLE hd k)

/-- Fill the full row vector from the already fixed particles and the final row
of the given prefix. Rows outside the live suffix are taken in reverse particle order. -/
def tasepPrefixRowVector {m d N : ℕ} {y : Fin m → ℤ} (A : TasepCroppedPrefix N y (d + 1))
    (x : Fin m → ℤ) (h : d + 1 ≤ m) : Fin m → ℤ :=
  fun i => if hi : m - (d + 1) ≤ i.1 then
    (A (Fin.last d) ⟨i.1 - (m - (d + 1)), by
      change i.1 - (m - (d + 1)) < d + 1
      have := i.2
      omega⟩).1
  else x i.rev

/-- The weighted sum of cropped prefix arrays at a fixed physical observation. -/
noncomputable def tasepPrefixSum {m : ℕ} (N : ℕ) (y x : Fin m → ℤ) (d : ℕ)
    (hd : d + 1 ≤ m) : ℝ :=
  open Classical in
  ∑ A : TasepCroppedPrefix N y (d + 1),
    if tasepInterlaces (tasepPrefixValues A) ∧ tasepPrefixFixed A x hd then
      (tasepRowStage N y (tasepPrefixRowVector A x hd) (m - (d + 1))).det
    else 0

/-- The last old level and the appended row, with the empty prefix as a separate case. -/
def tasepAppendedInterlaces : {d : ℕ} → TasepArray d → (Fin (d+1) → ℤ) → Prop
  | 0, _, _ => True
  | n+1, A, B => ∀ i : Fin (n+1),
      B i.castSucc < A (Fin.last n) i ∧ A (Fin.last n) i ≤ B i.succ

theorem tasepInterlaces_snoc {d : ℕ} (A : TasepArray d) (B : Fin (d + 1) → ℤ) :
    tasepInterlaces (Fin.snoc A B : TasepArray (d + 1)) ↔
      tasepInterlaces A ∧ StrictMono B ∧ tasepAppendedInterlaces A B := by
  constructor
  · intro h
    refine ⟨⟨fun k => ?_, fun k hk i => ?_⟩, ?_, ?_⟩
    · simpa only [Fin.snoc_castSucc] using h.1 k.castSucc
    · have hk' : k + 1 < d + 1 := by omega
      have hl := h.2 k hk' i
      change (Fin.snoc A B : TasepArray (d+1)) (⟨k + 1,hk⟩ : Fin d).castSucc i.castSucc <
          (Fin.snoc A B : TasepArray (d+1)) (⟨k, by omega⟩ : Fin d).castSucc i ∧
        (Fin.snoc A B : TasepArray (d+1)) (⟨k, by omega⟩ : Fin d).castSucc i ≤
          (Fin.snoc A B : TasepArray (d+1)) (⟨k + 1,hk⟩ : Fin d).castSucc i.succ at hl
      simpa only [Fin.snoc_castSucc] using hl
    · simpa only [Fin.snoc_last] using h.1 (Fin.last d)
    · cases d with
      | zero => trivial
      | succ d =>
        intro i
        have hl := h.2 d (by omega) i
        change (Fin.snoc A B : TasepArray (d+2)) (Fin.last (d+1)) i.castSucc <
            (Fin.snoc A B : TasepArray (d+2)) (Fin.last d).castSucc i ∧
          (Fin.snoc A B : TasepArray (d+2)) (Fin.last d).castSucc i ≤
            (Fin.snoc A B : TasepArray (d+2)) (Fin.last (d+1)) i.succ at hl
        simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hl
  · rintro ⟨hA, hB, hlast⟩
    constructor
    · intro k
      induction k using Fin.lastCases with
      | last => simpa only [Fin.snoc_last] using hB
      | cast k => simpa only [Fin.snoc_castSucc] using hA.1 k
    · intro k hk i
      by_cases he : k + 1 < d
      · change (Fin.snoc A B : TasepArray (d+1)) (⟨k+1,he⟩ : Fin d).castSucc i.castSucc <
            (Fin.snoc A B : TasepArray (d+1)) (⟨k, by omega⟩ : Fin d).castSucc i ∧
          (Fin.snoc A B : TasepArray (d+1)) (⟨k, by omega⟩ : Fin d).castSucc i ≤
            (Fin.snoc A B : TasepArray (d+1)) (⟨k+1,he⟩ : Fin d).castSucc i.succ
        simpa only [Fin.snoc_castSucc] using hA.2 k he i
      · have hEq : d = k + 1 := by omega
        subst d
        change (Fin.snoc A B : TasepArray (k+2)) (Fin.last (k+1)) i.castSucc <
            (Fin.snoc A B : TasepArray (k+2)) (Fin.last k).castSucc i ∧
          (Fin.snoc A B : TasepArray (k+2)) (Fin.last k).castSucc i ≤
            (Fin.snoc A B : TasepArray (k+2)) (Fin.last (k+1)) i.succ
        simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hlast i

theorem tasepPrefixValues_snoc {m d N : ℕ} {y : Fin m → ℤ}
    (A : TasepCroppedPrefix N y d) (B : Fin (d + 1) → ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y))) :
    tasepPrefixValues (Fin.snoc A B) =
      Fin.snoc (tasepPrefixValues A) (fun i => (B i).1) := by
  funext k i
  induction k using Fin.lastCases with
  | last => simp [tasepPrefixValues]
  | cast j => simp [tasepPrefixValues]

theorem tasepPrefixFixed_snoc {m d N : ℕ} {y : Fin m → ℤ}
    (A : TasepCroppedPrefix N y d) (B : Fin (d + 1) → ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y)))
    (x : Fin m → ℤ) (h : d + 1 ≤ m) :
    tasepPrefixFixed (Fin.snoc A B) x h ↔
      tasepPrefixFixed A x (by omega) ∧ (B 0).1 = x ⟨d, by omega⟩ := by
  have he (k : Fin d) : Fin.castLE h k.castSucc =
      Fin.castLE (show d ≤ m by omega) k := Fin.ext rfl
  have hlast : Fin.castLE h (Fin.last d) = (⟨d, by omega⟩ : Fin m) := Fin.ext rfl
  constructor
  · intro hx
    refine ⟨fun k => ?_, ?_⟩
    · simpa only [Fin.snoc_castSucc, he k] using hx k.castSucc
    · simpa only [Fin.snoc_last, hlast] using hx (Fin.last d)
  · rintro ⟨hA,hB⟩ k
    induction k using Fin.lastCases with
    | last => simpa only [Fin.snoc_last, hlast] using hB
    | cast j => simpa only [Fin.snoc_castSucc, he j] using hA j

/-- Once the leftmost entry is fixed below the preceding row, the rest of the
new row can be summed independently over the preceding row's consecutive intervals. -/
theorem tasepInterlace_last_iff_intervals {d : ℕ} (A : Fin (d + 1) → ℤ)
    (B : Fin (d + 2) → ℤ) (hB : B 0 < A 0) :
    (StrictMono B ∧ ∀ i : Fin (d + 1), B i.castSucc < A i ∧ A i ≤ B i.succ) ↔
      (∀ i : Fin (d + 1), A i ≤ B i.succ) ∧
        ∀ i : Fin d, B i.castSucc.succ < A i.succ := by
  constructor
  · rintro ⟨_, h⟩
    exact ⟨fun i => (h i).2, fun i => (h i.succ).1⟩
  · rintro ⟨h₁, h₂⟩
    have h (i : Fin (d + 1)) : B i.castSucc < A i := by
      induction i using Fin.cases with
      | zero => exact hB
      | succ i => exact h₂ i
    exact ⟨Fin.strictMono_iff_lt_succ.mpr fun i => (h i).trans_le (h₁ i),
      fun i => ⟨h i, h₁ i⟩⟩


/-- The live suffix of a full row vector, indexed from zero. -/
def tasepSuffixIndex {m d : ℕ} (h : d ≤ m) (i : Fin d) : Fin m :=
  ⟨m - d + i.1, by have := i.2; omega⟩

/-- Fill the non-frozen rows of a full vector with the live row. -/
def tasepPackRow {m d : ℕ} (h : d ≤ m) (x : Fin m → ℤ) (B : Fin d → ℤ) :
    Fin m → ℤ :=
  fun i => if hi : m - d ≤ i.1 then B ⟨i.1 - (m-d), by have := i.2; omega⟩ else x i.rev

theorem tasepPackRow_apply_suffix {m d : ℕ} (h : d ≤ m) (x : Fin m → ℤ) (B : Fin d → ℤ)
    (i : Fin d) : tasepPackRow h x B (tasepSuffixIndex h i) = B i := by
  unfold tasepPackRow
  rw [dite_eq_left (by change m - d ≤ m - d + i.1; omega)]
  congr 1
  apply Fin.ext
  change m - d + i.1 - (m - d) = i.1
  omega

theorem tasepPackRow_apply_frozen {m d : ℕ} (h : d ≤ m) (x : Fin m → ℤ) (B : Fin d → ℤ)
    (i : Fin m) (hi : i.1 < m - d) : tasepPackRow h x B i = x i.rev := by
  unfold tasepPackRow
  rw [dite_eq_right (not_le_of_gt hi)]

theorem tasepSuffixIndex_rev_zero {m d : ℕ} (hd : d + 1 ≤ m) :
    (tasepSuffixIndex hd (0 : Fin (d + 1))).rev = ⟨d, by omega⟩ := by
  apply Fin.ext
  rw [Fin.val_rev]
  change m - (m - (d + 1) + 0 + 1) = d
  omega

theorem tasepPrefixRowVector_eq_pack {m d N : ℕ} {y : Fin m → ℤ}
    (A : TasepCroppedPrefix N y (d + 1)) (x : Fin m → ℤ) (hd : d + 1 ≤ m) :
    tasepPrefixRowVector A x hd = tasepPackRow hd x (fun i => (A (Fin.last d) i).1) := rfl

/-- Independent interval conditions for the new row of a cropped array. -/
def tasepNewRowIntervals {m d N : ℕ} {y : Fin m → ℤ} (A : Fin (d + 1) → ℤ)
    (left : ℤ) (B : Fin (d + 2) → ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y))) : Prop :=
  (B 0).1 = left ∧
    (∀ i : Fin (d + 1), A i ≤ (B i.succ).1) ∧
    ∀ i : Fin d, (B i.castSucc.succ).1 < A i.succ

/-- The term for one possible last row, zero outside the interlacing intervals. -/
noncomputable def tasepIntervalRowWeight {m d N : ℕ} {y : Fin m → ℤ}
    (x : Fin m → ℤ)
    (A : Fin (d+1) → ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y))) (hd : d+2 ≤ m)
    (B : Fin (d+2) → ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y))) : ℝ :=
  open Classical in
  if tasepNewRowIntervals (fun i => (A i).1) (x ⟨d+1, by omega⟩) B then
    (tasepRowStage N y (tasepPackRow hd x (fun i => (B i).1)) (m - (d+2))).det
  else 0

open Classical in
theorem tasepIntervalRow_sum_grid {m d N : ℕ} {y : Fin m → ℤ} (x : Fin m → ℤ)
    (A : Fin (d + 1) → ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y))) (hd : d + 2 ≤ m)
    (hx : ∀ i, x i ∈ Finset.Icc (tasepCropLo y) (tasepCropHi N y)) :
    let p := m - (d + 2)
    let a := tasepPackRow (show d + 1 ≤ m by omega) x (fun i => (A i).1)
    (∑ B : Fin (d + 2) → ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y)),
      tasepIntervalRowWeight x A hd B) =
      ∑ z ∈ Fintype.piFinset (tasepRowStageGrid N y x a p),
        (tasepRowStage N y z p).det := by
  classical
  dsimp [tasepIntervalRowWeight]
  let p := m - (d + 2)
  let a := tasepPackRow (show d + 1 ≤ m by omega) x (fun i => (A i).1)
  let L := tasepCropLo y
  let U := tasepCropHi N y
  let C := ↥(Finset.Icc L U)
  let grid := Fintype.piFinset (tasepRowStageGrid N y x a p)
  let left := x ⟨d + 1, by omega⟩
  let pick := tasepSuffixIndex hd
  have hp : p + (d + 2) = m := by dsimp [p]; omega
  have heval (i : Fin (d + 1)) : a (pick i.succ) = (A i).1 := by
    have hi : pick i.succ = tasepSuffixIndex (show d + 1 ≤ m by omega) i := by
      apply Fin.ext
      change m - (d + 2) + (i.1 + 1) = m - (d + 1) + i.1
      omega
    rw [hi]
    exact tasepPackRow_apply_suffix _ x _ i
  have hleft : x (pick 0).rev = left := by rw [tasepSuffixIndex_rev_zero]
  have hval (i : Fin (d + 2)) : (pick i).1 = p + i.1 := rfl
  have hgrid (z : Fin m → ℤ) :
      z ∈ grid ↔
        (∀ i : Fin m, i.1 < p → z i = x i.rev) ∧ z (pick 0) = left ∧
        (∀ i : Fin (d + 1), (A i).1 ≤ z (pick i.succ)) ∧
        (∀ i : Fin d, z (pick i.castSucc.succ) < (A i.succ).1) ∧
        z (pick (Fin.last (d + 1))) ≤ U := by
    constructor
    · intro hz
      have hmem := Fintype.mem_piFinset.mp hz
      refine ⟨fun i hi => ?_, ?_, fun i => ?_, fun i => ?_, ?_⟩
      · have hi' : i.1 ≤ p := hi.le
        simpa [tasepRowStageGrid, hi'] using hmem i
      · have h₀ : (pick 0).1 ≤ p := by rw [hval]; simp
        simpa [tasepRowStageGrid, h₀, hleft] using hmem (pick 0)
      · have hpi : ¬ (pick i.succ).1 ≤ p := by rw [hval]; change ¬p + (i.1 + 1) ≤ p; omega
        have hi := hmem (pick i.succ)
        unfold tasepRowStageGrid at hi
        rw [ite_eq_right hpi] at hi
        split at hi
        · rw [Finset.mem_Ico, heval] at hi
          exact hi.1
        · rw [Finset.mem_Icc, heval] at hi
          exact hi.1
      · let j := pick i.castSucc.succ
        have hj : j.1 + 1 < m := by change p + (i.1 + 1) + 1 < m; have := i.2; omega
        have hpi : ¬j.1 ≤ p := by change ¬p + (i.1 + 1) ≤ p; omega
        have hnext : (⟨j.1 + 1, hj⟩ : Fin m) = pick i.succ.succ := by
          apply Fin.ext
          change p + (i.1+1) + 1 = p + (i.1+1+1)
          omega
        have h' := hmem j
        rw [tasepRowStageGrid, ite_eq_right hpi, dite_eq_left hj, Finset.mem_Ico, hnext, heval i.succ] at h'
        exact h'.2
      · let j := pick (Fin.last (d+1))
        have hj : ¬j.1 + 1 < m := by change ¬p + (d+1) + 1 < m; omega
        have hpi : ¬j.1 ≤ p := by change ¬p + (d+1) ≤ p; omega
        have h' := hmem j
        rw [tasepRowStageGrid, ite_eq_right hpi, dite_eq_right hj, Finset.mem_Icc] at h'
        exact h'.2
    · rintro ⟨hf, h0, hlow, hupp, hlast⟩
      apply Fintype.mem_piFinset.mpr
      intro i
      by_cases hi : i.1 ≤ p
      · rw [tasepRowStageGrid, ite_eq_left hi, Finset.mem_singleton]
        rcases lt_or_eq_of_le hi with hp'|he
        · exact hf i hp'
        · have hEq : i = pick 0 := Fin.ext (by rw [hval]; simpa using he)
          rw [hEq, h0, hleft]
      · let j : Fin (d + 1) := ⟨i.1-p-1, by have := i.2; omega⟩
        have he : i = pick j.succ := by apply Fin.ext; change i.1 = p + (i.1-p-1+1); omega
        rw [he, tasepRowStageGrid, ite_eq_right (by rw [← he]; exact hi), heval]
        by_cases hn : (pick j.succ).1 + 1 < m
        · let k : Fin d := ⟨j.1, by
              have h' : p + (j.1+1) + 1 < m := hn
              omega⟩
          have h₁ : k.castSucc = j := Fin.ext rfl
          have h₂ : (⟨(pick j.succ).1 + 1, hn⟩ : Fin m) = pick k.succ.succ := by
            apply Fin.ext
            change p + (j.1+1) + 1 = p + (j.1+1+1)
            omega
          rw [dite_eq_left hn, Finset.mem_Ico, h₂, heval]
          exact ⟨hlow j, by simpa only [h₁] using hupp k⟩
        · rw [dite_eq_right hn, Finset.mem_Icc]
          have hEq : j.succ = Fin.last (d+1) := by
            apply Fin.ext
            have h' : ¬p + (j.1+1) + 1 < m := hn
            have := j.2
            change j.1 + 1 = d + 1
            omega
          exact ⟨hlow j, hEq.symm ▸ hlast⟩
  classical
  let S : Finset (Fin (d+2) → C) :=
    Finset.univ.filter (tasepNewRowIntervals (fun j => (A j).1) left)
  let pack (B : Fin (d+2) → C) := tasepPackRow hd x (fun j => (B j).1)
  rw [← Finset.sum_filter]
  change (∑ B ∈ S, (tasepRowStage N y (pack B) p).det) =
    ∑ z ∈ grid, (tasepRowStage N y z p).det
  refine Finset.sum_bij (fun B _ => pack B) (fun B hB => ?_) ?_ ?_ (fun _ _ => rfl)
  · have hb := (Finset.mem_filter.mp hB).2
    change (B 0).1 = left ∧ _ ∧ _ at hb
    rcases hb with ⟨hB0, hB1, hB2⟩
    apply (hgrid _).mpr
    refine ⟨fun i hi => tasepPackRow_apply_frozen _ _ _ _ hi, ?_, fun i => ?_, fun i => ?_, ?_⟩
    · rw [show pack B (pick 0) = (B 0).1 from tasepPackRow_apply_suffix _ _ _ _]
      exact hB0
    · change (A i).1 ≤ tasepPackRow _ _ _ (tasepSuffixIndex hd i.succ)
      rw [tasepPackRow_apply_suffix]
      exact hB1 i
    · change tasepPackRow _ _ _ (tasepSuffixIndex hd i.castSucc.succ) < (A i.succ).1
      rw [tasepPackRow_apply_suffix]
      exact hB2 i
    · change tasepPackRow _ _ _ (tasepSuffixIndex hd (Fin.last (d+1))) ≤ U
      rw [tasepPackRow_apply_suffix]
      exact (Finset.mem_Icc.mp (B _).2).2
  · intro A' _ B' _ he
    funext i
    apply Subtype.ext
    have h := congrFun he (pick i)
    change tasepPackRow _ _ _ (tasepSuffixIndex hd i) = tasepPackRow _ _ _ (tasepSuffixIndex hd i) at h
    simpa only [tasepPackRow_apply_suffix] using h
  · intro z hz
    obtain ⟨hf,h0,hl,hu,hU⟩ := (hgrid z).mp hz
    have hc (j : Fin (d+2)) : z (pick j) ∈ Finset.Icc L U := by
      induction j using Fin.cases with
      | zero =>
        rw [h0]
        exact hx _
      | succ i =>
        apply Finset.mem_Icc.mpr
        refine ⟨(Finset.mem_Icc.mp (A i).2).1.trans (hl i), ?_⟩
        induction i using Fin.lastCases with
        | last => exact hU
        | cast i => exact (hu i).le.trans (Finset.mem_Icc.mp (A i.succ).2).2
    let B : Fin (d+2) → C := fun i => ⟨z (pick i), hc i⟩
    refine ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨h0,hl,hu⟩⟩, ?_⟩
    funext i
    by_cases hi : i.1 < p
    · exact (tasepPackRow_apply_frozen _ _ _ _ hi).trans (hf i hi).symm
    · let j : Fin (d+2) := ⟨i.1-p, by have := i.2; omega⟩
      have he : i = pick j := by apply Fin.ext; change i.1 = p + (i.1-p); omega
      rw [he]
      exact tasepPackRow_apply_suffix _ _ _ _


theorem tasepPrefix_valid_snoc_iff {m d N : ℕ} {y : Fin m → ℤ}
    (A : TasepCroppedPrefix N y (d + 1))
    (B : Fin (d+2) → ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y)))
    (x : Fin m → ℤ) (hd : d + 2 ≤ m) (hx : StrictAnti x) :
    (tasepInterlaces (tasepPrefixValues (Fin.snoc A B)) ∧ tasepPrefixFixed (Fin.snoc A B) x hd) ↔
      (tasepInterlaces (tasepPrefixValues A) ∧ tasepPrefixFixed A x (by omega)) ∧
        tasepNewRowIntervals (fun i => (A (Fin.last d) i).1) (x ⟨d+1, by omega⟩) B := by
  let a : Fin (d+1) → ℤ := fun i => (A (Fin.last d) i).1
  let b : Fin (d+2) → ℤ := fun i => (B i).1
  rw [tasepPrefixValues_snoc, tasepInterlaces_snoc, tasepPrefixFixed_snoc]
  change (tasepInterlaces (tasepPrefixValues A) ∧ StrictMono b ∧
      (∀ i : Fin (d+1), b i.castSucc < a i ∧ a i ≤ b i.succ)) ∧
    (tasepPrefixFixed A x _ ∧ b 0 = x ⟨d+1, by omega⟩) ↔ _
  have hstart (hA : tasepPrefixFixed A x (by omega)) (hb : b 0 = x ⟨d+1, by omega⟩) :
      b 0 < a 0 := by
    have ha := hA (Fin.last d)
    change a 0 = x ⟨d, by omega⟩ at ha
    rw [ha,hb]
    exact hx (show (⟨d, by omega⟩ : Fin m) < ⟨d+1, by omega⟩ from Nat.lt_succ_self d)
  constructor
  · rintro ⟨⟨hA,hB,hrel⟩,hfix,h0⟩
    exact ⟨⟨hA,hfix⟩, h0, (tasepInterlace_last_iff_intervals a b (hstart hfix h0)).1 ⟨hB,hrel⟩⟩
  · rintro ⟨⟨hA,hfix⟩,h0,hint⟩
    obtain ⟨hB,hrel⟩ := (tasepInterlace_last_iff_intervals a b (hstart hfix h0)).2 hint
    exact ⟨⟨hA,hB,hrel⟩,hfix,h0⟩

theorem tasepPrefixSum_succ {m : ℕ} (N : ℕ) (y x : Fin m → ℤ) (d : ℕ)
    (hd : d + 2 ≤ m) (hy : StrictAnti y) (hx : StrictAnti x)
    (hcrop : ∀ i, x i ∈ Finset.Icc (tasepCropLo y) (tasepCropHi N y)) :
    tasepPrefixSum N y x (d+1) hd = tasepPrefixSum N y x d (by omega) := by
  classical
  let P := fun k : Fin (d+2) => Fin (k.1+1) →
    ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y))
  let e := Fin.snocEquiv P
  let W (A : TasepCroppedPrefix N y (d+2)) : ℝ :=
    if tasepInterlaces (tasepPrefixValues A) ∧ tasepPrefixFixed A x hd then
      (tasepRowStage N y (tasepPrefixRowVector A x hd) (m - (d+2))).det else 0
  have he : (∑ A, W A) = ∑ A : TasepCroppedPrefix N y (d+1),
      ∑ B : P (Fin.last (d+1)), W (Fin.snoc A B) := by
    have h := Fintype.sum_equiv e (fun (p : _ × _) => W (Fin.snoc p.2 p.1)) W (fun _ => rfl)
    rw [Fintype.sum_prod_type] at h
    exact h.symm.trans Finset.sum_comm
  change (∑ A, W A) = _
  rw [he, tasepPrefixSum]
  refine Finset.sum_congr rfl fun A _ => ?_
  let p := m - (d+2)
  let a := tasepPrefixRowVector A x (show d+1 ≤ m by omega)
  let b : Fin (d+1) → ℤ := fun i => (A (Fin.last d) i).1
  simp only [W, tasepPrefix_valid_snoc_iff A _ x hd hx]
  by_cases hA : tasepInterlaces (tasepPrefixValues A) ∧ tasepPrefixFixed A x (by omega)
  · simp only [hA, true_and, ite_true]
    have hterm (B : P (Fin.last (d+1))) :
        tasepPrefixRowVector (Fin.snoc A B) x hd = tasepPackRow hd x (fun i => (B i).1) := by
      simp only [tasepPrefixRowVector_eq_pack, Fin.snoc_last]
    simp only [hterm]
    have hp : p + 1 = m - (d+1) := by dsimp [p]; omega
    have ha : a = tasepPackRow (show d+1 ≤ m by omega) x b := tasepPrefixRowVector_eq_pack _ _ _
    have hai (i : Fin m) (hi : p < i.1) :
        a i = b ⟨i.1-(p+1), by have := i.2; omega⟩ := by
      rw [ha]
      unfold tasepPackRow
      rw [dite_eq_left (by omega : m-(d+1) ≤ i.1)]
      congr 1
      apply Fin.ext
      change i.1 - (m-(d+1)) = i.1 - (p+1)
      rw [hp]
    have haMono (i j : Fin m) (hi : p < i.1) (hij : i ≤ j) : a i ≤ a j := by
      have hij' : i.1 ≤ j.1 := hij
      rw [hai i hi, hai j (by omega)]
      apply (hA.1.1 (Fin.last d)).monotone
      change i.1 - (p+1) ≤ j.1 - (p+1)
      omega
    have hu (i : Fin m) (hi : p < i.1) : a i ≤ tasepCropHi N y := by
      rw [hai i hi]
      exact (Finset.mem_Icc.mp (A (Fin.last d) _).2).2
    have hgrid := tasepIntervalRow_sum_grid (d := d) x (A (Fin.last d)) hd hcrop
    have hLeft :
        (∑ B : P (Fin.last (d+1)),
          if tasepNewRowIntervals (fun i => (A (Fin.last d) i).1) (x ⟨d+1, by omega⟩) B then
            (tasepRowStage N y (tasepPackRow hd x (fun i => (B i).1)) p).det else 0) =
        ∑ B : Fin (d+2) → ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y)),
          tasepIntervalRowWeight x (A (Fin.last d)) hd B := by
      apply Finset.sum_congr rfl
      intro B _
      by_cases hB : tasepNewRowIntervals (fun i => (A (Fin.last d) i).1) (x ⟨d+1, by omega⟩) B
      <;> simp only [tasepIntervalRowWeight, Fin.val_last, hB, ite_true, ite_false, p]
    refine hLeft.trans (hgrid.trans ?_)
    change (∑ z ∈ Fintype.piFinset (tasepRowStageGrid N y x a p), (tasepRowStage N y z p).det) = _
    rw [tasepRowStage_contract N y x a p hy haMono hu, hp]
    congr 2
    funext i
    by_cases hi : i.1 ≤ p
    · rw [ite_eq_left hi]
      change x i.rev = a i
      rw [ha]
      exact (tasepPackRow_apply_frozen _ _ _ _ (by omega)).symm
    · rw [ite_eq_right hi]
  · simp [hA]


theorem tasepDiff_iter_eq_zero_below (N k : ℕ) {x : ℤ} (hx : x < -(k : ℤ)) :
    (tasepDiff^[k]) (tasepFZero N) x = 0 := by
  induction k generalizing x with
  | zero => simp [tasepFZero, show ¬0 ≤ x by omega]
  | succ k ih =>
    rw [iterate_succ_apply', tasepDiff, ih (by omega : x < -(k : ℤ)),
      ih (by omega : x + 1 < -(k : ℤ)), sub_self]

theorem tasepF_eq_zero_below {j x : ℤ} (N : ℕ) (hj : j ≤ 0) (hx : x < j) :
    tasepF j x N = 0 := by
  cases j with
  | ofNat k =>
    have h : k = 0 := by change (k : ℤ) ≤ 0 at hj; omega
    subst k
    exact tasepDiff_iter_eq_zero_below N 0 (by omega)
  | negSucc k => exact tasepDiff_iter_eq_zero_below N (k+1) (by omega)

/-- The transition determinant vanishes if the ordered target leaves the
finite crop needed by the array expansion. -/
theorem tasepTransitionDet_eq_zero_of_not_crop {m : ℕ} (N : ℕ) (y x : Fin m → ℤ)
    (hy : StrictAnti y) (hx : StrictAnti x)
    (h : ¬∀ i, x i ∈ Finset.Icc (tasepCropLo y) (tasepCropHi N y)) :
    tasepTransitionDet N y x = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp h
  have hm : 0 < m := by have := i.2; omega
  simp only [Finset.mem_Icc, not_and_or, not_le] at hi
  rw [tasepTransitionDet]
  rcases hi with hi | hi
  · let L : Fin m := ⟨m-1, by omega⟩
    have hiL : i ≤ L := by change i.1 ≤ m-1; have := i.2; omega
    have hxL := (hx.antitone hiL).trans_lt hi
    rw [tasepCropLo, dite_eq_left hm] at hxL
    change x L < y L at hxL
    apply Matrix.det_eq_zero_of_row_eq_zero L
    intro j
    have hjL : j ≤ L := by change j.1 ≤ m-1; have := j.2; omega
    have hg := tasep_strictAnti_gap y hy j L hjL
    change tasepF ((j.1 : ℤ) - L.1) (x L - y j) N = 0
    apply tasepF_eq_zero_below N <;> (change j.1 ≤ L.1 at hjL; omega)
  · rw [tasepCropHi, dite_eq_left hm] at hi
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    have hyj := hy.antitone (show (⟨0,hm⟩ : Fin m) ≤ j from Nat.zero_le _)
    change tasepF ((j.1 : ℤ) - i.1) (x i - y j) N = 0
    apply tasepF_eq_zero_above
    omega

theorem tasepPrefixSum_base {m : ℕ} (N : ℕ) (y x : Fin m → ℤ) (hm : 1 ≤ m)
    (hcrop : ∀ i, x i ∈ Finset.Icc (tasepCropLo y) (tasepCropHi N y)) :
    tasepPrefixSum N y x 0 hm = tasepTransitionDet N y x := by
  classical
  let x₀ := x ⟨0, by omega⟩
  let A₀ : TasepCroppedPrefix N y 1 := fun _ _ => ⟨x₀, hcrop _⟩
  unfold tasepPrefixSum
  rw [Finset.sum_eq_single A₀]
  · have hI : tasepInterlaces (tasepPrefixValues A₀) := by
      refine ⟨fun k => ?_, fun k hk _ => (by omega : False).elim⟩
      have hk : k = 0 := Fin.eq_zero k
      subst k
      intro i j hij
      rw [Fin.eq_zero i, Fin.eq_zero j] at hij
      exact (lt_irrefl _ hij).elim
    have hF : tasepPrefixFixed A₀ x hm := by
      intro k
      have h := Fin.eq_zero k
      subst k
      rfl
    rw [ite_eq_left ⟨hI,hF⟩]
    unfold tasepTransitionDet
    nth_rewrite 2 [← Matrix.det_submatrix_equiv_self Fin.revPerm]
    congr 1
    ext i j
    have hmin : min (m - (0 + 1)) i.1 = i.1 := min_eq_right (by have := i.2; omega)
    have hv : tasepPrefixRowVector A₀ x hm i = x i.rev := by
      unfold tasepPrefixRowVector
      split
      · have he : i.rev = (⟨0, by omega⟩ : Fin m) := by
          apply Fin.ext
          rw [Fin.val_rev]
          change m - (i.1 + 1) = 0
          have := i.2
          omega
        rw [he]
      · rfl
    simp only [tasepRowStage, Matrix.of_apply, hv, hmin, Matrix.submatrix_apply,
      tasepTransitionMatrix, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    have hi := i.2
    have hj := j.2
    omega
  · intro A _ hA
    refine ite_eq_right (fun h => hA ?_)
    funext k i
    have hk : k = 0 := Fin.eq_zero k
    subst k
    have hi : i = 0 := Fin.eq_zero i
    subst i
    apply Subtype.ext
    exact h.2 0
  · simp

theorem tasepPrefixSum_eq_det {m : ℕ} (N : ℕ) (y x : Fin m → ℤ) (d : ℕ)
    (hd : d + 1 ≤ m) (hy : StrictAnti y) (hx : StrictAnti x)
    (hcrop : ∀ i, x i ∈ Finset.Icc (tasepCropLo y) (tasepCropHi N y)) :
    tasepPrefixSum N y x d hd = tasepTransitionDet N y x := by
  induction d with
  | zero => exact tasepPrefixSum_base N y x hd hcrop
  | succ d ih =>
    exact (tasepPrefixSum_succ N y x d hd hy hx hcrop).trans (ih (by omega))

/-- The physical marginal of the signed array equals the genuine transition determinant. -/
theorem signedArray_marginal {m : ℕ} (N : ℕ) (y x : Fin m → ℤ) (hy : StrictAnti y)
    (hx : StrictAnti x) :
    tasepTransitionDet N y x =
      ∑ A ∈ (tasepArrayCrop N y).filter (fun A => tasepArrayPositions A = x),
        signedArrayWeight N y A := by
  classical
  cases m with
  | zero =>
    have hA (A : TasepArray 0) : tasepInterlaces A :=
      ⟨fun k => Fin.elim0 k, fun k hk => (by omega : False).elim⟩
    have hxA (A : TasepArray 0) : tasepArrayPositions A = x := Subsingleton.elim _ _
    simp [tasepTransitionDet, tasepArrayCrop, signedArrayWeight, hA, hxA]
  | succ m =>
    by_cases hcrop : ∀ i, x i ∈ Finset.Icc (tasepCropLo y) (tasepCropHi N y)
    · rw [← tasepPrefixSum_eq_det N y x m (by omega) hy hx hcrop]
      unfold tasepPrefixSum tasepArrayCrop
      rw [Finset.filter_filter]
      -- Transfer the summation from cropped tuples to their integer-valued arrays.
      let e : TasepCroppedPrefix N y (m+1) → TasepArray (m+1) := tasepPrefixValues
      have hinj : Injective e := by
        intro A B he
        funext k i
        apply Subtype.ext
        exact congrFun (congrFun he k) i
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun A _ => e A) ?_ ?_ ?_ ?_
      · intro A hA
        rw [Finset.mem_filter] at hA ⊢
        refine ⟨Finset.mem_image.mpr ⟨A, Finset.mem_univ _, rfl⟩, hA.2.1, ?_⟩
        funext k
        exact hA.2.2 k
      · exact fun A _ B _ h => hinj h
      · intro A hA
        rw [Finset.mem_filter] at hA
        obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hA.1
        exact ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA.2.1, fun i => congrFun hA.2.2 i⟩, rfl⟩
      · intro A hA
        have hi := (Finset.mem_filter.mp hA).2.1
        rw [signedArrayWeight, ite_eq_left hi]
        congr 1
        ext i j
        simp only [tasepRowStage, Matrix.of_apply, tasepPrefixRowVector, Nat.sub_self,
          Nat.zero_le, dite_eq_left, Nat.sub_zero, min_eq_left, Nat.cast_zero, zero_sub,
          tasepPrefixValues, e]
        rfl
    · rw [tasepTransitionDet_eq_zero_of_not_crop N y x hy hx hcrop]
      refine (Finset.sum_eq_zero fun A hA => ?_).symm
      obtain ⟨hm, he⟩ := Finset.mem_filter.mp hA
      have hgood := ((tasepArrayCrop_mem_iff N y A).mp hm).2
      exact (hcrop (fun i => by
        rw [← he]
        exact hgood i 0)).elim


/-- The raw layer matrix before inserting identity entries at physical sites. -/
noncomputable def finiteLevelRaw {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    Matrix (Fin m ⊕ TasepFiniteSite N y) (Fin m ⊕ TasepFiniteSite N y) ℝ :=
  Matrix.fromBlocks 0 (finiteLevelBirth N y) (finiteLevelTerminal N y)
    (-finiteLevelTransfer N y)

theorem tasepDet_columns_diagonal_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (S : Finset ι) :
    (Matrix.of (fun i j => if j ∈ S then A i j else (1 : Matrix ι ι ℝ) i j)).det =
      (A.toSquareBlockProp (fun i => i ∈ S)).det := by
  have hp := tasepDet_piecewise_diagonal Aᵀ S (fun _ => 1)
  have hm : (Matrix.of (fun i j => if j ∈ S then A i j else (1 : Matrix ι ι ℝ) i j))ᵀ =
      Matrix.of (S.piecewise Aᵀ (1 : Matrix ι ι ℝ)) := by
    ext i j
    by_cases h : i ∈ S
    · simp [Finset.piecewise, Matrix.of_apply, Matrix.transpose_apply, h]
    · simp [Finset.piecewise, Matrix.of_apply, Matrix.transpose_apply, h, Matrix.one_apply, eq_comm]
  have hd : (Aᵀ.toSquareBlockProp (fun i => i ∈ S)) =
      (A.toSquareBlockProp (fun i => i ∈ S))ᵀ := rfl
  rw [← Matrix.det_transpose, hm]
  rwa [hd, Matrix.det_transpose, show Matrix.diagonal (fun _ : ι => (1 : ℝ)) = 1 from Matrix.diagonal_one,
    Finset.prod_const_one, mul_one] at hp

theorem tasepBlock_diag_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) (S : Finset ι) :
    ((A * Matrix.diagonal v).toSquareBlockProp (fun i => i ∈ S)).det =
      (A.toSquareBlockProp (fun i => i ∈ S)).det * ∏ i ∈ S, v i := by
  have h : (A * Matrix.diagonal v).toSquareBlockProp (fun i => i ∈ S) =
      A.toSquareBlockProp (fun i => i ∈ S) * Matrix.diagonal (fun i : {i // i ∈ S} => v i.1) := by
    ext i j
    change (A * Matrix.diagonal v) i.1 j.1 =
      (A.toSquareBlockProp (fun i => i ∈ S) * Matrix.diagonal (fun i : {i // i ∈ S} => v i.1)) i j
    simp only [Matrix.mul_diagonal]
    rfl
  rw [h, Matrix.det_mul, Matrix.det_diagonal]
  refine congrArg₂ (· * ·) (tasepDet_instance_eq _ _ _ _ _) ?_
  exact (Finset.prod_subtype S (fun _ => Iff.rfl) v).symm

/-- Mark physical sites by the indicator of allowed sites and keep all virtual sites. -/
def tasepVertexMark {ι : Type*} [DecidableEq ι] (S : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then 1 else 0

theorem tasepVertexMark_prod {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    (∏ i ∈ T, tasepVertexMark S i) = if T ⊆ S then 1 else 0 := by
  by_cases h : T ⊆ S
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one fun i hi => ite_eq_left (h hi)
  · rw [ite_eq_right h]
    obtain ⟨i, hi, hS⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (ite_eq_right hS)

theorem finiteLevel_sum_principal {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (S : Finset (Fin m ⊕ TasepFiniteSite N y)) (hS : ∀ i : Fin m, Sum.inl i ∈ S) :
    ((finiteLevelAnchor N y).toSquareBlockProp (fun i => i ∈ S)).det =
      ∑ T ∈ S.powerset,
        if ∀ i : Fin m, Sum.inl i ∈ T then
          ((finiteLevelRaw N y).toSquareBlockProp (fun i => i ∈ T)).det else 0 := by
  classical
  let V := Fin m ⊕ TasepFiniteSite N y
  let U : Finset V := Finset.univ.filter (Sum.elim (fun _ => False) (fun _ => True))
  let G := finiteLevelAnchor N y
  let L := finiteLevelRaw N y
  let v := tasepVertexMark S
  let w := tasepVertexMark U
  have he : L * Matrix.diagonal v + Matrix.diagonal w =
      Matrix.of (fun i j => if j ∈ S then G i j else (1 : Matrix V V ℝ) i j) := by
    ext i j
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.of_apply]
    rcases j with j | j
    · simp only [v, tasepVertexMark, hS j, ite_true, mul_one]
      cases i <;> simp [G, L, finiteLevelAnchor, finiteLevelRaw, w, tasepVertexMark, U, Matrix.diagonal_apply]
    · by_cases hj : Sum.inr j ∈ S <;> cases i <;>
        simp [v, w, U, G, L, tasepVertexMark, hj, finiteLevelAnchor, finiteLevelRaw,
          Matrix.one_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.diagonal_apply,
          sub_eq_neg_add] <;>
        exact if_congr (⟨Sum.inr.inj, congrArg Sum.inr⟩) rfl rfl
  rw [← tasepDet_columns_diagonal_one G S, ← he, tasepDet_add_diagonal]
  change (∑ T : Finset V, ((L * Matrix.diagonal v).toSquareBlockProp (fun i => i ∈ T)).det *
    (∏ i ∈ Tᶜ, w i)) = _
  simp_rw [tasepBlock_diag_mul]
  dsimp only [v, w]
  simp_rw [tasepVertexMark_prod]
  have hp (T : Finset V) : Tᶜ ⊆ U ↔ ∀ i : Fin m, Sum.inl i ∈ T := by
    constructor
    · intro h i
      by_contra hi
      have hu := h (Finset.mem_compl.mpr hi)
      simp [U] at hu
    · intro h p hp
      cases p with
      | inl i => exact ((Finset.mem_compl.mp hp) (h i)).elim
      | inr j => simp [U]
  simp_rw [hp]
  have hPow : S.powerset = (Finset.univ : Finset (Finset V)).filter (fun T => T ⊆ S) := by
    ext T
    simp
  rw [hPow]
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : T ⊆ S <;> by_cases hU : ∀ i : Fin m, Sum.inl i ∈ T <;> simp [hT,hU,L]


/-- The common template for a diagram with precisely `k+1` sites in each level
and one virtual vertex for each birth. -/
abbrev TasepVertexTemplate (m : ℕ) := Fin m ⊕ (Σ k : Fin m, Fin (k.1+1))

/-- Rows and columns of each successive birth block, followed by the terminal block. -/
abbrev TasepGroupedTemplate (m : ℕ) :=
  Σ k : Fin (m+1), Fin (if k.1 < m then k.1+1 else m)

private theorem tasepFin_heq {a b : ℕ} (hab : a = b) {i : Fin a} {j : Fin b}
    (h : i.1 = j.1) : HEq i j := by
  subst b
  exact heq_of_eq (Fin.ext h)

def tasepGroupColumn {m : ℕ} (p : TasepGroupedTemplate m) : TasepVertexTemplate m :=
  if hk : p.1.1 < m then
    Sum.inr ⟨⟨p.1.1,hk⟩,⟨p.2.1,by simpa only [ite_eq_left hk] using p.2.2⟩⟩
  else Sum.inl ⟨p.2.1, by simpa only [ite_eq_right hk] using p.2.2⟩

def tasepUngroupColumn {m : ℕ} (p : TasepVertexTemplate m) : TasepGroupedTemplate m :=
  match p with
  | .inl i => ⟨Fin.last m, ⟨i.1, by simp⟩⟩
  | .inr ⟨k,i⟩ => ⟨k.castSucc, ⟨i.1, by simpa [k.2] using i.2⟩⟩

/-- Columns are grouped by their receiving level, with virtual columns terminal. -/
def tasepGroupColumnEquiv (m : ℕ) : TasepGroupedTemplate m ≃ TasepVertexTemplate m where
  toFun := tasepGroupColumn
  invFun := tasepUngroupColumn
  left_inv := by
    rintro ⟨k,i⟩
    by_cases hk : k.1 < m
    · simp only [tasepGroupColumn, dite_eq_left hk, tasepUngroupColumn]
      apply Sigma.ext
      · apply Fin.ext; rfl
      · exact tasepFin_heq (congrArg (fun k : Fin (m+1) => if k.1 < m then k.1+1 else m) (by apply Fin.ext; first | rfl | (simp; omega))) rfl
    · simp only [tasepGroupColumn, dite_eq_right hk, tasepUngroupColumn]
      apply Sigma.ext
      · apply Fin.ext
        change m = k.1
        have := k.2
        omega
      · exact tasepFin_heq (congrArg (fun k : Fin (m+1) => if k.1 < m then k.1+1 else m) (by apply Fin.ext; first | rfl | (simp; omega))) rfl
  right_inv := by
    rintro (i|⟨k,i⟩)
    · simp [tasepUngroupColumn,tasepGroupColumn]
    · unfold tasepGroupColumn
      split
      · rfl
      · rename_i hh
        exact (hh k.2).elim

def tasepGroupRow {m : ℕ} (p : TasepGroupedTemplate m) : TasepVertexTemplate m :=
  if hbirth : p.1.1 < m ∧ p.2.1 = p.1.1 then Sum.inl ⟨p.1.1,hbirth.1⟩
  else Sum.inr ⟨⟨p.1.1 - 1, by
      have hk := p.1.2
      have hi := p.2.2
      by_cases h : p.1.1 < m
      · omega
      · simp only [ite_eq_right h] at hi
        omega⟩,
    ⟨p.2.1, by
      change p.2.1 < p.1.1 - 1 + 1
      have hi := p.2.2
      have hk := p.1.2
      by_cases h : p.1.1 < m
      · simp only [ite_eq_left h] at hi
        by_contra! hc
        exact hbirth ⟨h, by omega⟩
      · simp only [ite_eq_right h] at hi
        omega⟩⟩

def tasepUngroupRow {m : ℕ} (p : TasepVertexTemplate m) : TasepGroupedTemplate m :=
  match p with
  | .inl i => ⟨i.castSucc, ⟨i.1, by simp [i.2]⟩⟩
  | .inr ⟨k,i⟩ => ⟨k.succ, ⟨i.1, by
      change i.1 < if k.1 + 1 < m then k.1 + 1 + 1 else m
      split <;> have := i.2 <;> have := k.2 <;> omega⟩⟩

/-- The rows at a receiving level consist of the preceding level's sites and
that level's virtual birth row. -/
def tasepGroupRowEquiv (m : ℕ) : TasepGroupedTemplate m ≃ TasepVertexTemplate m where
  toFun := tasepGroupRow
  invFun := tasepUngroupRow
  left_inv := by
    rintro ⟨k,i⟩
    by_cases h : k.1 < m ∧ i.1 = k.1
    · simp only [tasepGroupRow,dite_eq_left h,tasepUngroupRow]
      apply Sigma.ext
      · exact Fin.ext rfl
      · exact tasepFin_heq rfl h.2.symm
    · simp only [tasepGroupRow,dite_eq_right h,tasepUngroupRow]
      have hk : k.1 ≠ 0 := by
        intro hn
        have hi := i.2
        by_cases hm : 0 < m
        · exact h ⟨by omega, by simp only [ite_eq_left (by omega : k.1 < m)] at hi; omega⟩
        · simp only [ite_eq_right (by omega : ¬k.1 < m)] at hi
          omega
      have he : k.1 - 1 + 1 = k.1 := by omega
      apply Sigma.ext
      · exact Fin.ext he
      · exact tasepFin_heq (congrArg (fun j : Fin (m+1) => if j.1 < m then j.1+1 else m)
          (Fin.ext he)) rfl
  right_inv := by
    rintro (i|⟨k,i⟩)
    · simp [tasepUngroupRow,tasepGroupRow,i.2]
    · unfold tasepGroupRow
      split
      · rename_i h
        have hv : i.1 = k.1 + 1 := h.2
        exact ((Nat.ne_of_lt i.2) hv).elim
      · apply congrArg Sum.inr
        have he : (⟨k.1 + 1 - 1, by have := k.2; omega⟩ : Fin m) = k :=
          Fin.ext (by change k.1 + 1 - 1 = k.1; omega)
        apply Sigma.ext he
        exact tasepFin_heq (congrArg (fun j : Fin m => j.1 + 1) he) rfl


/-- An occupied spatial fibre of a principal submatrix of the raw layer matrix. -/
def tasepLayerSites {m : ℕ} {N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (k : Fin m) :
    Finset (Finset.Icc (tasepCropLo y) (tasepCropHi N y)) :=
  Finset.univ.filter fun s => Sum.inr (k,s) ∈ T

private def tasepRawRowGroup {m : ℕ} {N : ℕ} {y : Fin m → ℤ}
    (p : Fin m ⊕ TasepFiniteSite N y) : Fin (m + 1) :=
  p.elim Fin.castSucc fun p => p.1.succ

private def tasepRawColGroup {m : ℕ} {N : ℕ} {y : Fin m → ℤ}
    (p : Fin m ⊕ TasepFiniteSite N y) : Fin (m + 1) :=
  p.elim (fun _ => Fin.last m) fun p => p.1.castSucc

private theorem tasepRaw_support {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (p q : Fin m ⊕ TasepFiniteSite N y) (h : finiteLevelRaw N y p q ≠ 0) :
    tasepRawRowGroup p = tasepRawColGroup q := by
  rcases p with i | ⟨i,s⟩ <;> rcases q with j | ⟨j,t⟩
  · exact (h rfl).elim
  · by_cases h' : i = j
    · simpa [tasepRawRowGroup, tasepRawColGroup] using congrArg Fin.castSucc h'
    · exact (h (by simp [finiteLevelRaw, finiteLevelBirth, h'])).elim
  · by_cases h' : i.1 + 1 = m
    · exact Fin.ext h'
    · exact (h (by simp [finiteLevelRaw, finiteLevelTerminal, h'])).elim
  · by_cases h' : j.1 = i.1 + 1
    · exact Fin.ext h'.symm
    · exact (h (by simp [finiteLevelRaw, finiteLevelTransfer, h'])).elim

private def tasepGroupFibresEquiv {V : Type*} {G : Type*} (e : Equiv.Perm V)
    (r c : V → G) (h : ∀ i, r i = c (e i)) (k : G) :
    {i // r i = k} ≃ {i // c i = k} where
  toFun i := ⟨e i.1, (h i.1).symm.trans i.2⟩
  invFun j := ⟨e.symm j.1, (h (e.symm j.1)).trans (by simpa using j.2)⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i.1)
  right_inv j := Subtype.ext (e.apply_symm_apply j.1)

private def tasepColumnFibre {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (k : Fin m) :
    (tasepLayerSites T k) ≃ {p : T // tasepRawColGroup p.1 = k.castSucc} where
  toFun s := ⟨⟨Sum.inr (k,s.1), (Finset.mem_filter.mp s.2).2⟩, rfl⟩
  invFun p := by
    obtain ⟨⟨i|⟨i,s⟩, hp⟩, h⟩ := p
    · have hv := congrArg Fin.val h
      change m = k.1 at hv
      exact ((Nat.ne_of_lt k.2) hv.symm).elim
    · have hv : i = k := Fin.ext (congrArg (fun j : Fin (m+1) => j.1) h)
      subst i
      exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  left_inv s := by
    apply Subtype.ext
    rfl
  right_inv p := by
    obtain ⟨⟨i|⟨i,s⟩, hp⟩, h⟩ := p
    · have hv := congrArg Fin.val h
      change m = k.1 at hv
      exact ((Nat.ne_of_lt k.2) hv.symm).elim
    · have hv : i = k := Fin.ext (congrArg (fun j : Fin (m+1) => j.1) h)
      subst i
      rfl

private def tasepRowFibre {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ i, Sum.inl i ∈ T)
    (k : Fin m) (l : Fin m) (hl : l.1 + 1 = k.1) :
    (Unit ⊕ tasepLayerSites T l) ≃ {p : T // tasepRawRowGroup p.1 = k.castSucc} where
  toFun q := match q with
    | .inl _ => ⟨⟨Sum.inl k, hT k⟩, rfl⟩
    | .inr s => ⟨⟨Sum.inr (l,s.1), (Finset.mem_filter.mp s.2).2⟩, Fin.ext hl⟩
  invFun p := by
    obtain ⟨⟨i|⟨i,s⟩, hp⟩, h⟩ := p
    · exact Sum.inl ()
    · have hv : i = l := Fin.ext (by
        have hh := congrArg Fin.val h
        change i.1 + 1 = k.1 at hh
        omega)
      subst i
      exact Sum.inr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  left_inv q := by
    rcases q with ⟨⟩ | s <;> rfl
  right_inv p := by
    obtain ⟨⟨i|⟨i,s⟩, hp⟩, h⟩ := p
    · have hv : i = k := Fin.ext (congrArg (fun j : Fin (m+1) => j.1) h)
      subst i
      rfl
    · have hv : i = l := Fin.ext (by
        have hh := congrArg Fin.val h
        change i.1 + 1 = k.1 at hh
        omega)
      subst i
      rfl

private def tasepRowFibreZero {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ i, Sum.inl i ∈ T)
    (k : Fin m) (hk : k.1 = 0) :
    Unit ≃ {p : T // tasepRawRowGroup p.1 = k.castSucc} where
  toFun _ := ⟨⟨Sum.inl k, hT k⟩, rfl⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨⟨i|⟨i,s⟩, hp⟩, h⟩ := p
    · have hv : i = k := Fin.ext (congrArg (fun j : Fin (m+1) => j.1) h)
      subst i
      rfl
    · have hh := congrArg Fin.val h
      change i.1 + 1 = k.1 at hh
      omega

/-- A principal minor containing the virtual sites can be nonzero only if each
physical level contains exactly its prescribed number of sites. -/
theorem tasepPrincipal_layerCard {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ i, Sum.inl i ∈ T)
    (hdet : ((finiteLevelRaw N y).toSquareBlockProp (fun i => i ∈ T)).det ≠ 0) :
    ∀ k : Fin m, (tasepLayerSites T k).card = k.1 + 1 := by
  classical
  let A : Matrix T T ℝ := (finiteLevelRaw N y).toSquareBlockProp (fun i => i ∈ T)
  have hA : A.det ≠ 0 := hdet
  rw [Matrix.det_apply'] at hA
  obtain ⟨e, he⟩ : ∃ e : Equiv.Perm T, ∀ i : T, A (e i) i ≠ 0 := by
    by_contra! h
    apply hA
    apply Finset.sum_eq_zero
    intro e _
    obtain ⟨i, hi⟩ := h e
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (f := fun j : T => A (e j) j) (Finset.mem_univ i) hi)
  let r (p : T) := tasepRawRowGroup p.1
  let c (p : T) := tasepRawColGroup p.1
  have hrc (i : T) : r i = c (e.symm i) := by
    have hh := tasepRaw_support N y _ _ (he (e.symm i))
    simpa [r,c] using hh
  have hc (k : Fin m) : Fintype.card {p : T // r p = k.castSucc} =
      (tasepLayerSites T k).card := by
    exact (Fintype.card_congr (tasepGroupFibresEquiv e.symm r c hrc k.castSucc)).trans
      ((Fintype.card_congr (tasepColumnFibre T k).symm).trans (Fintype.card_coe _))
  have hsize (n : ℕ) : ∀ hn : n < m,
      (tasepLayerSites T (⟨n,hn⟩ : Fin m)).card = n+1 := by
    induction n with
    | zero =>
      intro hn
      rw [← hc]
      simpa using (Fintype.card_congr
        (tasepRowFibreZero T hT ⟨0,hn⟩ rfl)).symm
    | succ n ih =>
      intro hn
      rw [← hc]
      have hl : n < m := by omega
      rw [← Fintype.card_congr (tasepRowFibre T hT ⟨n+1,hn⟩ ⟨n,hl⟩ rfl)]
      rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_coe, ih hl]
      omega
  exact fun k => hsize k.1 k.2


private noncomputable def tasepOrderedLayer {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y))
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) (k : Fin m) :
    Fin (k.1+1) ≃o tasepLayerSites T k :=
  (tasepLayerSites T k).orderIsoOfFin (h k)

private noncomputable def tasepPrincipalEquiv {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ j, Sum.inl j ∈ T)
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) :
    TasepVertexTemplate m ≃ T where
  toFun p := match p with
    | .inl k => ⟨Sum.inl k,hT k⟩
    | .inr ⟨k,i⟩ => ⟨Sum.inr (k,(tasepOrderedLayer T h k i).1),
        (Finset.mem_filter.mp (tasepOrderedLayer T h k i).2).2⟩
  invFun p := match p with
    | ⟨.inl k,_⟩ => Sum.inl k
    | ⟨.inr (k,s),hp⟩ => Sum.inr ⟨k,
        (tasepOrderedLayer T h k).symm ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩⟩
  left_inv p := by
    rcases p with k|⟨k,i⟩
    · rfl
    · change (Sum.inr ⟨k,(tasepOrderedLayer T h k).symm (tasepOrderedLayer T h k i)⟩ : TasepVertexTemplate m) = _
      rw [OrderIso.symm_apply_apply]
  right_inv p := by
    obtain ⟨k|⟨k,s⟩,hp⟩ := p
    · rfl
    · apply Subtype.ext
      change Sum.inr (k,((tasepOrderedLayer T h k)
        ((tasepOrderedLayer T h k).symm ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩)).1) = _
      rw [OrderIso.apply_symm_apply]

private def tasepGroupedFibreEquiv (m : ℕ) (k : Fin (m+1)) :
    Fin (if k.1 < m then k.1+1 else m) ≃ {p : TasepGroupedTemplate m // p.1 = k} where
  toFun i := ⟨⟨k,i⟩,rfl⟩
  invFun p := p.2 ▸ p.1.2
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨k',i⟩,rfl⟩; rfl

private theorem tasepPrincipal_row_group {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ j, Sum.inl j ∈ T)
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) (p : TasepGroupedTemplate m) :
    tasepRawRowGroup ((tasepPrincipalEquiv T hT h) (tasepGroupRow p)).1 = p.1 := by
  cases p with
  | mk k i =>
    unfold tasepGroupRow
    split
    · exact Fin.ext rfl
    · rename_i hbirth
      change ¬(k.1 < m ∧ i.1 = k.1) at hbirth
      change (⟨k.1 - 1 + 1, _⟩ : Fin (m+1)) = k
      apply Fin.ext
      change k.1 - 1 + 1 = k.1
      have hk : k.1 ≠ 0 := by
        intro hz
        have hi := i.2
        by_cases h : (k.1 : ℕ) < m
        · simp only [ite_eq_left h] at hi
          exact hbirth ⟨h, by omega⟩
        · simp only [ite_eq_right h] at hi
          omega
      omega

private theorem tasepPrincipal_col_group {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ j, Sum.inl j ∈ T)
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) (p : TasepGroupedTemplate m) :
    tasepRawColGroup ((tasepPrincipalEquiv T hT h) (tasepGroupColumn p)).1 = p.1 := by
  unfold tasepGroupColumn
  split
  · exact Fin.ext rfl
  · rename_i hh
    apply Fin.ext
    change m = p.1.1
    have := p.1.2
    omega

private theorem tasepDet_grouped {m : ℕ} (A : Matrix (TasepVertexTemplate m) (TasepVertexTemplate m) ℝ) :
    (A.submatrix (tasepGroupRowEquiv m) (tasepGroupColumnEquiv m)).det = ↑↑(Equiv.Perm.sign ((tasepGroupRowEquiv m).trans (tasepGroupColumnEquiv m).symm)) *
      A.det := by
  have he : A.submatrix (tasepGroupRowEquiv m) (tasepGroupColumnEquiv m) = (A.submatrix (tasepGroupColumnEquiv m)
      (tasepGroupColumnEquiv m)).submatrix
        ((tasepGroupRowEquiv m).trans (tasepGroupColumnEquiv m).symm) id := by
    ext i j
    simp [Matrix.submatrix_apply]
  rw [he, Matrix.det_permute, Matrix.det_submatrix_equiv_self]

/-- The integer array attached to an occupied set with the correct size at each level. -/
noncomputable def tasepPrincipalArray {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y))
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) : TasepArray m :=
  fun k i => (tasepOrderedLayer T h k i).1.1

private theorem tasepPrincipalArray_mono {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y))
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) (k : Fin m) :
    StrictMono (tasepPrincipalArray T h k) :=
  fun _ _ hij => (tasepOrderedLayer T h k).strictMono hij

private def tasepPreviousArrayRow {m : ℕ} (A : TasepArray m) (k : Fin m) :
    Fin k.1 → ℤ := fun i =>
  A ⟨k.1 - 1, by have := k.2; omega⟩
    ⟨i.1, by change i.1 < k.1 - 1 + 1; have := i.2; omega⟩

private def tasepAdjacentArrayTest {m : ℕ} (A : TasepArray m) (k : Fin m) : Prop :=
  ∀ i : Fin k.1, A k i.castSucc < tasepPreviousArrayRow A k i ∧
    tasepPreviousArrayRow A k i ≤ A k i.succ

private theorem tasepAdjacentArrayTest_iff {m : ℕ} (A : TasepArray m)
    (hA : ∀ k, StrictMono (A k)) :
    (∀ k, tasepAdjacentArrayTest A k) ↔ tasepInterlaces A := by
  constructor
  · intro h
    refine ⟨hA, fun k hk i => ?_⟩
    exact h ⟨k+1,hk⟩ i
  · intro h k
    obtain ⟨n,hn⟩ := k
    cases n with
    | zero => intro i; exact Fin.elim0 i
    | succ n =>
      intro i
      exact h.2 n hn i

private noncomputable def tasepPrincipalGrouped {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ j, Sum.inl j ∈ T)
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) :
    Matrix (TasepGroupedTemplate m) (TasepGroupedTemplate m) ℝ :=
  ((finiteLevelRaw N y).toSquareBlockProp (fun i => i ∈ T)).submatrix
    (fun p => tasepPrincipalEquiv T hT h (tasepGroupRow p))
    (fun p => tasepPrincipalEquiv T hT h (tasepGroupColumn p))

private theorem tasepPrincipalGrouped_triangular {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ j, Sum.inl j ∈ T)
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) :
    (tasepPrincipalGrouped T hT h).BlockTriangular Sigma.fst := by
  intro p q hpq
  by_contra he
  have hs := tasepRaw_support N y _ _ he
  rw [tasepPrincipal_row_group T hT h, tasepPrincipal_col_group T hT h] at hs
  exact (ne_of_lt hpq) hs.symm

private def tasepGroupedOfLevel {m : ℕ} (k : Fin m) (i : Fin (k.1+1)) :
    TasepGroupedTemplate m := ⟨k.castSucc, ⟨i.1, by simpa only [Fin.val_castSucc, ite_eq_left k.2] using i.2⟩⟩

private theorem tasepPrincipalGrouped_level {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ j, Sum.inl j ∈ T)
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) (k : Fin m)
    (i j : Fin (k.1+1)) :
    tasepPrincipalGrouped T hT h (tasepGroupedOfLevel k i) (tasepGroupedOfLevel k j) =
      if hi : i.1 < k.1 then
        -(if tasepPrincipalArray T h k j <
          tasepPreviousArrayRow (tasepPrincipalArray T h) k ⟨i.1,hi⟩ then 1 else 0)
      else 1 := by
  unfold tasepPrincipalGrouped
  change finiteLevelRaw N y
    (tasepPrincipalEquiv T hT h (tasepGroupRow (tasepGroupedOfLevel k i))).1
    (tasepPrincipalEquiv T hT h (tasepGroupColumn (tasepGroupedOfLevel k j))).1 = _
  have hcol : tasepGroupColumn (tasepGroupedOfLevel k j) = Sum.inr ⟨k,j⟩ := by
    unfold tasepGroupColumn
    split
    · rfl
    · rename_i hh
      exact (hh k.2).elim
  rw [hcol]
  unfold tasepGroupRow
  split
  · rename_i hh
    have hi : ¬i.1 < k.1 := not_lt_of_ge hh.2.ge
    simp [hi, tasepPrincipalEquiv, finiteLevelRaw, finiteLevelBirth, tasepGroupedOfLevel]
  · rename_i hh
    have hi : i.1 < k.1 := by
      have hi := i.2
      have hne : i.1 ≠ k.1 := fun he => hh ⟨k.2,he⟩
      omega
    have hk : k.1 - 1 + 1 = k.1 := by omega
    rw [dite_eq_left hi]
    change -(if k.1 = k.1-1+1 ∧ tasepPrincipalArray T h k j <
      tasepPreviousArrayRow (tasepPrincipalArray T h) k ⟨i.1,hi⟩ then 1 else 0) = _
    simp only [hk, true_and]

private def tasepGroupedOfTerminal {m : ℕ} (i : Fin m) :
    TasepGroupedTemplate m := ⟨Fin.last m, ⟨i.1, by simpa using i.2⟩⟩

private theorem tasepPrincipalGrouped_terminal {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ j, Sum.inl j ∈ T)
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) (i j : Fin m) :
    tasepPrincipalGrouped T hT h (tasepGroupedOfTerminal i) (tasepGroupedOfTerminal j) =
      tasepF (-(j.1 : ℤ)) ((if hm : 0 < m then
        tasepPrincipalArray T h ⟨m - 1, by omega⟩
          ⟨i.1, by change i.1 < m-1+1; have := i.2; omega⟩ else 0) - y j.rev) N := by
  have hm : 0 < m := by have := i.2; omega
  unfold tasepPrincipalGrouped
  change finiteLevelRaw N y
    (tasepPrincipalEquiv T hT h (tasepGroupRow (tasepGroupedOfTerminal i))).1
    (tasepPrincipalEquiv T hT h (tasepGroupColumn (tasepGroupedOfTerminal j))).1 = _
  have hcol : tasepGroupColumn (tasepGroupedOfTerminal j) = Sum.inl j := by
    unfold tasepGroupColumn
    split
    · rename_i hh
      exact ((Nat.lt_irrefl m) hh).elim
    · rfl
  rw [hcol]
  unfold tasepGroupRow
  split
  · rename_i hh
    exact ((Nat.lt_irrefl m) hh.1).elim
  · have hm' : m - 1 + 1 = m := by omega
    change (if m-1+1 = m then tasepF (-(j.1 : ℤ)) ((tasepPrincipalArray T h
      ⟨m-1, by omega⟩ ⟨i.1, by change i.1 < m-1+1; have := i.2; omega⟩) - y j.rev) N else 0) = _
    rw [ite_eq_left hm']


private def tasepGroupedRowSign {m : ℕ} (p : TasepGroupedTemplate m) : ℝ :=
  if p.1.1 < m ∧ p.2.1 < p.1.1 then -1 else 1

private noncomputable def tasepNormalizedGrouped {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ j, Sum.inl j ∈ T)
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) :
    Matrix (TasepGroupedTemplate m) (TasepGroupedTemplate m) ℝ :=
  Matrix.diagonal tasepGroupedRowSign * tasepPrincipalGrouped T hT h

private theorem tasepGroupedRowSign_level {m : ℕ} (k : Fin m) (i : Fin (k.1+1)) :
    tasepGroupedRowSign (tasepGroupedOfLevel k i) = if i.1 < k.1 then -1 else 1 := by
  simp [tasepGroupedRowSign, tasepGroupedOfLevel,k.2]

private theorem tasepGroupedRowSign_terminal {m : ℕ} (i : Fin m) :
    tasepGroupedRowSign (tasepGroupedOfTerminal i) = 1 := by
  simp [tasepGroupedRowSign,tasepGroupedOfTerminal]

private def tasepGroupedFibreLevel {m : ℕ} (k : Fin m) :
    Fin (k.1+1) ≃ {p : TasepGroupedTemplate m // p.1 = k.castSucc} :=
  (finCongr (by simp [k.2])).trans (tasepGroupedFibreEquiv m k.castSucc)

private def tasepGroupedFibreTerminal (m : ℕ) :
    Fin m ≃ {p : TasepGroupedTemplate m // p.1 = Fin.last m} :=
  (finCongr (by simp)).trans (tasepGroupedFibreEquiv m (Fin.last m))

private theorem tasepNormalizedGrouped_det {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ j, Sum.inl j ∈ T)
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) :
    (tasepNormalizedGrouped T hT h).det = signedArrayWeight N y (tasepPrincipalArray T h) := by
  classical
  let A := tasepPrincipalArray T h
  let M := tasepNormalizedGrouped T hT h
  have htri : M.BlockTriangular Sigma.fst := by
    intro i j hij
    change (Matrix.diagonal (tasepGroupedRowSign (m := m)) * tasepPrincipalGrouped T hT h :
        Matrix (TasepGroupedTemplate m) (TasepGroupedTemplate m) ℝ) i j = 0
    rw [Matrix.diagonal_mul, tasepPrincipalGrouped_triangular T hT h hij, mul_zero]
  have hlevel (k : Fin m) :
      (M.toSquareBlock Sigma.fst k.castSucc).det = if tasepAdjacentArrayTest A k then 1 else 0 := by
    rw [← Matrix.det_submatrix_equiv_self (tasepGroupedFibreLevel k)]
    have hp : StrictMono (tasepPreviousArrayRow A k) := by
      intro i j hij
      apply tasepPrincipalArray_mono T h
      exact hij
    let Qk := Matrix.of (fun i j : Fin (k.1+1) =>
      if hi : i.1 < k.1 then if A k j < tasepPreviousArrayRow A k ⟨i.1,hi⟩
        then (1 : ℝ) else 0 else 1)
    have hv : Qk.det = (if tasepAdjacentArrayTest A k then 1 else 0) := by
      have he := tasepDet_interlace_transfer (tasepPreviousArrayRow A k) (A k) hp
        (tasepPrincipalArray_mono T h k)
      have htest : tasepAdjacentArrayTest A k ↔ ∀ i : Fin k.1,
          A k i.castSucc < tasepPreviousArrayRow A k i ∧ tasepPreviousArrayRow A k i ≤ A k i.succ := Iff.rfl
      simpa only [Qk, htest] using he
    refine Eq.trans ?_ hv
    congr 1
    ext i j
    change (Matrix.diagonal (tasepGroupedRowSign (m := m)) * tasepPrincipalGrouped T hT h :
      Matrix (TasepGroupedTemplate m) (TasepGroupedTemplate m) ℝ)
      (tasepGroupedOfLevel k i) (tasepGroupedOfLevel k j) = _
    rw [Matrix.diagonal_mul, tasepGroupedRowSign_level, tasepPrincipalGrouped_level]
    change _ = Qk i j
    dsimp only [Qk, Matrix.of_apply]
    by_cases hi : i.1 < k.1
    · by_cases hlt : A k j < tasepPreviousArrayRow A k ⟨i.1,hi⟩ <;> simp [hi,A,hlt]
    · simp [hi]
  let Q := Matrix.of (fun i j : Fin m => tasepF (-(j.1 : ℤ))
    ((if hm : 0 < m then A ⟨m-1,by omega⟩
      ⟨i.1,by change i.1 < m-1+1; have := i.2; omega⟩ else 0)-y j.rev) N)
  have hterm : (M.toSquareBlock Sigma.fst (Fin.last m)).det = Q.det := by
    rw [← Matrix.det_submatrix_equiv_self (tasepGroupedFibreTerminal m)]
    congr 1
    ext i j
    change (Matrix.diagonal (tasepGroupedRowSign (m := m)) * tasepPrincipalGrouped T hT h :
        Matrix (TasepGroupedTemplate m) (TasepGroupedTemplate m) ℝ)
      (tasepGroupedOfTerminal i) (tasepGroupedOfTerminal j) = Q i j
    rw [Matrix.diagonal_mul, tasepGroupedRowSign_terminal, one_mul, tasepPrincipalGrouped_terminal]
    rfl
  rw [show (tasepNormalizedGrouped T hT h).det = M.det from rfl, htri.det_fintype, Fin.prod_univ_castSucc, hterm]
  simp_rw [hlevel]
  by_cases hI : tasepInterlaces A
  · have htest := (tasepAdjacentArrayTest_iff A (tasepPrincipalArray_mono T h)).2 hI
    simp [htest,signedArrayWeight,A,Q,hI]
  · obtain ⟨k,hk⟩ : ∃ k, ¬tasepAdjacentArrayTest A k := by
      by_contra! he
      exact hI ((tasepAdjacentArrayTest_iff A (tasepPrincipalArray_mono T h)).1 he)
    have he : (∏ k : Fin m, if tasepAdjacentArrayTest A k then (1 : ℝ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)
    rw [he, zero_mul]
    exact (ite_eq_right hI).symm

private noncomputable def tasepPrincipalSign (m : ℕ) : ℝ :=
  (∏ p : TasepGroupedTemplate m, tasepGroupedRowSign p) *
    ↑↑(Equiv.Perm.sign ((tasepGroupRowEquiv m).trans (tasepGroupColumnEquiv m).symm))

/-- An occupied set with the prescribed sizes contributes the signed array weight,
up to a nonzero factor that depends only on the templates of the levels. -/
private theorem tasepPrincipal_weight {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ j, Sum.inl j ∈ T)
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) :
    signedArrayWeight N y (tasepPrincipalArray T h) = tasepPrincipalSign m *
      ((finiteLevelRaw N y).toSquareBlockProp (fun i => i ∈ T)).det := by
  rw [← tasepNormalizedGrouped_det T hT h, tasepNormalizedGrouped, Matrix.det_mul, Matrix.det_diagonal]
  let A := (finiteLevelRaw N y).toSquareBlockProp (fun i => i ∈ T)
  change (∏ p : TasepGroupedTemplate m, tasepGroupedRowSign p) *
    ((A.submatrix (tasepPrincipalEquiv T hT h) (tasepPrincipalEquiv T hT h)).submatrix
      (tasepGroupRowEquiv m) (tasepGroupColumnEquiv m)).det = _
  rw [tasepDet_grouped, Matrix.det_submatrix_equiv_self]
  exact (mul_assoc _ _ _).symm


open Classical in
private theorem tasepArraySum_measure {m : ℕ} (N : ℕ) (y : Fin m → ℤ) (hy : StrictAnti y)
    (P : (Fin m → ℤ) → Prop) (hP : MeasurableSet {x | P x}) :
    (∑ A ∈ (tasepArrayCrop N y).filter (fun A => P (tasepArrayPositions A)),
      signedArrayWeight N y A) = (finiteSeqLaw N y).real {x | P x} := by
  classical
  let S := (tasepArrayCrop N y).filter (fun A => P (tasepArrayPositions A))
  let X := S.image tasepArrayPositions
  let Y := (Finset.univ : Finset (Fin N → Fin m → Bool)).image (runSeqTasep y)
  have hAtom (x : Fin m → ℤ) :
      (∑ A ∈ S.filter (fun A => tasepArrayPositions A = x), signedArrayWeight N y A) =
      if P x then (finiteSeqLaw N y).real {x} else 0 := by
    by_cases hp : P x
    · have hEq : S.filter (fun A => tasepArrayPositions A = x) =
          (tasepArrayCrop N y).filter (fun A => tasepArrayPositions A = x) := by
        ext A
        simp only [S,Finset.mem_filter]
        constructor
        · rintro ⟨⟨hA,_⟩, h⟩
          exact ⟨hA,h⟩
        · rintro ⟨hA,h⟩
          exact ⟨⟨hA,h ▸ hp⟩,h⟩
      rw [hEq, ite_eq_left hp]
      by_cases hx : StrictAnti x
      · rw [finiteSeqLaw_atom_eq_det N y x hy hx, signedArray_marginal N y x hy hx]
      · have hEmpty : (tasepArrayCrop N y).filter (fun A => tasepArrayPositions A = x) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro A hA
          obtain ⟨hc, hh⟩ := Finset.mem_filter.mp hA
          apply hx
          rw [← hh]
          exact tasepArrayPositions_strictAnti A ((tasepArrayCrop_mem_iff N y A).mp hc).1
        rw [hEmpty, Finset.sum_empty,finiteSeqLaw_measureReal_apply N y _ (measurableSet_singleton _)]
        symm
        apply mul_eq_zero_of_right
        apply Finset.sum_eq_zero
        intro c _
        have hn : runSeqTasep y c ≠ x := by
          intro hh
          exact hx (hh ▸ strictAnti_runSeqTasep y hy c)
        simp [hn]
    · rw [ite_eq_right hp]
      apply Finset.sum_eq_zero
      intro A hA
      obtain ⟨hg,he⟩ := Finset.mem_filter.mp hA
      exact (hp (he ▸ (Finset.mem_filter.mp hg).2)).elim
  calc
    _ = ∑ x ∈ X ∪ Y, ∑ A ∈ S.filter (fun A => tasepArrayPositions A = x), signedArrayWeight N y A := by
      exact (Finset.sum_fiberwise_of_maps_to (fun A hA =>
        Finset.mem_union_left Y (Finset.mem_image_of_mem _ hA)) (signedArrayWeight N y)).symm
    _ = ∑ x ∈ X ∪ Y, if P x then (finiteSeqLaw N y).real {x} else 0 :=
      Finset.sum_congr rfl (fun x _ => hAtom x)
    _ = _ := by
      rw [finiteSeqLaw_measureReal_apply N y _ hP]
      simp_rw [finiteSeqLaw_measureReal_apply N y _ (measurableSet_singleton _)]
      rw [Finset.mul_sum]
      calc
        _ = ∑ x ∈ X ∪ Y, ∑ c : Fin N → Fin m → Bool,
              if P x ∧ runSeqTasep y c = x then (1/2 : ℝ) ^ (N*m) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          by_cases hx : P x
          · rw [ite_eq_left hx]
            apply Finset.sum_congr rfl
            intro c _
            by_cases hh : runSeqTasep y c = x <;> simp [hx,hh]
          · rw [ite_eq_right hx]
            simp [hx]
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_eq_single (runSeqTasep y c)]
          · by_cases hp : P (runSeqTasep y c) <;> simp [hp]
          · intro z _ hz
            simp [hz.symm]
          · intro hn
            exact (hn (Finset.mem_union_right X (Finset.mem_image_of_mem _ (Finset.mem_univ c)))).elim


private noncomputable def tasepArrayOccupied {m N : ℕ} {y : Fin m → ℤ}
    (A : TasepArray m) : Finset (Fin m ⊕ TasepFiniteSite N y) :=
  by
    classical
    exact Finset.univ.filter fun p => p.elim (fun _ => True) (fun p => ∃ i, A p.1 i = p.2.1)

private theorem tasepArrayOccupied_virtual {m N : ℕ} {y : Fin m → ℤ}
    (A : TasepArray m) (i : Fin m) : Sum.inl i ∈ tasepArrayOccupied (N := N) (y := y) A := by
  simp [tasepArrayOccupied]

private theorem tasepArrayOccupied_site {m N : ℕ} {y : Fin m → ℤ}
    (A : TasepArray m) (p : TasepFiniteSite N y) :
    Sum.inr p ∈ tasepArrayOccupied A ↔ ∃ i, A p.1 i = p.2.1 := by
  simp [tasepArrayOccupied]

private theorem tasepArrayOccupied_layer_eq {m N : ℕ} {y : Fin m → ℤ}
    (A : TasepArray m) (hA : A ∈ tasepArrayCrop N y) (k : Fin m) :
    tasepLayerSites (tasepArrayOccupied A) k =
      Finset.univ.image (fun i : Fin (k.1+1) =>
        (⟨A k i, ((tasepArrayCrop_mem_iff N y A).mp hA).2 k i⟩ :
          ↥(Finset.Icc (tasepCropLo y) (tasepCropHi N y)))) := by
  ext s
  simp only [tasepLayerSites, Finset.mem_filter, Finset.mem_univ, true_and,
    tasepArrayOccupied_site, Finset.mem_image, Subtype.ext_iff]

private theorem tasepArrayOccupied_sizes {m N : ℕ} {y : Fin m → ℤ}
    (A : TasepArray m) (hA : A ∈ tasepArrayCrop N y) :
    ∀ k, (tasepLayerSites (tasepArrayOccupied (N := N) (y := y) A) k).card = k.1+1 := by
  intro k
  have hmono := ((tasepArrayCrop_mem_iff N y A).mp hA).1.1 k
  rw [tasepArrayOccupied_layer_eq A hA k, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact hmono.injective (congrArg Subtype.val hij)

private theorem tasepPrincipalArray_occupied {m N : ℕ} {y : Fin m → ℤ}
    (A : TasepArray m) (hA : A ∈ tasepArrayCrop N y) :
    tasepPrincipalArray (tasepArrayOccupied A) (tasepArrayOccupied_sizes A hA) = A := by
  funext k i
  let e : Fin (k.1+1) ≃o tasepLayerSites (tasepArrayOccupied A) k :=
    tasepOrderedLayer _ (tasepArrayOccupied_sizes A hA) k
  let a : Fin (k.1+1) → tasepLayerSites (tasepArrayOccupied A) k := fun j =>
    ⟨⟨A k j, ((tasepArrayCrop_mem_iff N y A).mp hA).2 k j⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (tasepArrayOccupied_site A _).mpr ⟨j,rfl⟩⟩⟩
  have ha : StrictMono a := ((tasepArrayCrop_mem_iff N y A).mp hA).1.1 k
  have hmono : StrictMono (e.symm ∘ a) := e.symm.strictMono.comp ha
  have he : e.symm (a i) = i := congrFun hmono.eq_id i
  have hh := congrArg e he
  rw [e.apply_symm_apply] at hh
  exact (congrArg (fun p : tasepLayerSites (tasepArrayOccupied A) k => p.1.1) hh).symm

private theorem tasepArrayOccupied_principal {m N : ℕ} {y : Fin m → ℤ}
    (T : Finset (Fin m ⊕ TasepFiniteSite N y)) (hT : ∀ j, Sum.inl j ∈ T)
    (h : ∀ k, (tasepLayerSites T k).card = k.1+1) :
    tasepArrayOccupied (tasepPrincipalArray T h) = T := by
  ext p
  rcases p with j | ⟨k,s⟩
  · exact iff_of_true (tasepArrayOccupied_virtual _ j) (hT j)
  · rw [tasepArrayOccupied_site]
    constructor
    · rintro ⟨i,hi⟩
      have he : (tasepOrderedLayer T h k i).1 = s := Subtype.ext hi
      rw [← he]
      exact (Finset.mem_filter.mp (tasepOrderedLayer T h k i).2).2
    · intro hs
      let p : tasepLayerSites T k := ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩⟩
      obtain ⟨i,hi⟩ := (tasepOrderedLayer T h k).surjective p
      exact ⟨i, congrArg (fun q : tasepLayerSites T k => q.1.1) hi⟩


private theorem tasepSignedSum_principal {m N : ℕ} {y : Fin m → ℤ}
    (S : Finset (Fin m ⊕ TasepFiniteSite N y)) (hS : ∀ j, Sum.inl j ∈ S) :
    tasepPrincipalSign m * ((finiteLevelAnchor N y).toSquareBlockProp (fun i => i ∈ S)).det =
      ∑ A ∈ (tasepArrayCrop N y).filter (fun A => tasepArrayOccupied A ⊆ S), signedArrayWeight N y A := by
  classical
  rw [finiteLevel_sum_principal N y S hS, Finset.mul_sum]
  let Good (T : Finset (Fin m ⊕ TasepFiniteSite N y)) :=
    (∀ j, Sum.inl j ∈ T) ∧ ∃ h : ∀ k, (tasepLayerSites T k).card = k.1+1,
      tasepInterlaces (tasepPrincipalArray T h)
  rw [← Finset.sum_filter_add_sum_filter_not S.powerset Good]
  have hz : (∑ T ∈ S.powerset.filter (fun T => ¬Good T), tasepPrincipalSign m *
      (if ∀ i : Fin m, Sum.inl i ∈ T then
        ((finiteLevelRaw N y).toSquareBlockProp (fun i => i ∈ T)).det else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    have hg := (Finset.mem_filter.mp hT).2
    by_cases hv : ∀ i : Fin m, Sum.inl i ∈ T
    · rw [ite_eq_left hv]
      by_cases hd : ((finiteLevelRaw N y).toSquareBlockProp (fun i => i ∈ T)).det = 0
      · rw [hd, mul_zero]
      · have hsize := tasepPrincipal_layerCard N y T hv hd
        rw [← tasepPrincipal_weight T hv hsize]
        exact ite_eq_right (fun hi => hg ⟨hv,hsize,hi⟩)
    · rw [ite_eq_right hv, mul_zero]
  rw [hz, add_zero]
  symm
  refine Finset.sum_bij (fun A _ => tasepArrayOccupied A) ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨hc,hs⟩ := Finset.mem_filter.mp hA
    have ha := tasepArrayOccupied_sizes A hc
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs, tasepArrayOccupied_virtual A, ha, ?_⟩
    rw [tasepPrincipalArray_occupied A hc]
    exact ((tasepArrayCrop_mem_iff N y A).mp hc).1
  · intro A hA B hB hEq
    let hAc := (Finset.mem_filter.mp hA).1
    let hBc := (Finset.mem_filter.mp hB).1
    rw [← tasepPrincipalArray_occupied A hAc, ← tasepPrincipalArray_occupied B hBc]
    congr 1
  · intro T hT
    obtain ⟨hS',hv,hsize,hi⟩ := Finset.mem_filter.mp hT
    let A := tasepPrincipalArray T hsize
    have he : tasepArrayOccupied A = T := tasepArrayOccupied_principal T hv hsize
    refine ⟨A, Finset.mem_filter.mpr ⟨(tasepArrayCrop_mem_iff N y A).mpr ⟨hi,?_⟩, ?_⟩, he⟩
    · exact fun k i => (tasepOrderedLayer T hsize k i).1.2
    · exact he ▸ Finset.mem_powerset.mp hS'
  · intro A hA
    have hc := (Finset.mem_filter.mp hA).1
    rw [ite_eq_left (tasepArrayOccupied_virtual A)]
    have hw := tasepPrincipal_weight (tasepArrayOccupied (N := N) (y := y) A)
      (tasepArrayOccupied_virtual A) (tasepArrayOccupied_sizes A hc)
    rwa [tasepPrincipalArray_occupied A hc] at hw

private theorem tasepArrayOccupied_allowed {m N : ℕ} {y : Fin m → ℤ}
    (J : Finset (Fin m)) (a : J → ℤ) (A : TasepArray m) (hA : A ∈ tasepArrayCrop N y) :
    tasepArrayOccupied A ⊆ finiteLevelAllowed N y J a ↔
      ∀ j : J, a j ≤ tasepArrayPositions A j.1 := by
  have hc := (tasepArrayCrop_mem_iff N y A).mp hA
  have hm (p : TasepFiniteSite N y) : Sum.inr p ∈ finiteLevelAllowed N y J a ↔
      p ∉ finiteBadSites N y J a := by
    simp only [finiteLevelAllowed, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  constructor
  · intro h j
    let p : TasepFiniteSite N y := (j.1, ⟨A j.1 0,hc.2 j.1 0⟩)
    have hp := h ((tasepArrayOccupied_site A p).mpr ⟨0,rfl⟩)
    simpa [finiteBadSites,p,j.2,tasepArrayPositions] using (hm p).mp hp
  · intro h p hp
    rcases p with i | ⟨k,s⟩
    · simp [finiteLevelAllowed]
    · apply (hm (k,s)).mpr
      obtain ⟨i,hi⟩ := (tasepArrayOccupied_site A (k,s)).mp hp
      change A k i = s.1 at hi
      by_cases hk : k ∈ J
      · have hle := (h ⟨k,hk⟩).trans ((hc.1.1 k).monotone (Fin.zero_le i))
        simpa [finiteLevelAllowed, finiteBadSites,hk,← hi,tasepArrayPositions] using hle
      · simp [finiteLevelAllowed,finiteBadSites,hk]

private theorem tasepUniv_principal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) :
    (G.toSquareBlockProp (fun i => i ∈ (Finset.univ : Finset ι))).det = G.det := by
  let e : ι ≃ (Finset.univ : Finset ι) :=
    ⟨fun i => ⟨i,Finset.mem_univ _⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩
  exact (Matrix.det_submatrix_equiv_self e
    (G.toSquareBlockProp (fun i => i ∈ (Finset.univ : Finset ι)))).symm

private theorem finiteLevelAllowed_inl {m : ℕ} {N : ℕ} {y : Fin m → ℤ}
    (J : Finset (Fin m)) (a : J → ℤ) (i : Fin m) :
    Sum.inl i ∈ finiteLevelAllowed N y J a := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,trivial⟩

private theorem finiteLevelAllowed_inr {m : ℕ} {N : ℕ} {y : Fin m → ℤ}
    (J : Finset (Fin m)) (a : J → ℤ) (p : TasepFiniteSite N y) :
    Sum.inr p ∈ finiteLevelAllowed N y J a ↔ p ∉ finiteBadSites N y J a := by
  classical
  rw [finiteLevelAllowed, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨Finset.mem_univ _, h⟩⟩

private noncomputable def finiteBadAllowedEquiv {m : ℕ} {N : ℕ} {y : Fin m → ℤ}
    (J : Finset (Fin m)) (a : J → ℤ) :
    ↥(finiteBadSites N y J a) ≃ ↥((finiteLevelAllowed N y J a)ᶜ) where
  toFun p := ⟨Sum.inr p.1, Finset.mem_compl.mpr (fun hp => ((finiteLevelAllowed_inr J a _).mp hp) p.2)⟩
  invFun p := by
    obtain ⟨i|q,hq⟩ := p
    · exact ((Finset.mem_compl.mp hq) (finiteLevelAllowed_inl J a i)).elim
    · exact ⟨q, Classical.byContradiction fun h => (Finset.mem_compl.mp hq) ((finiteLevelAllowed_inr J a q).mpr h)⟩
  left_inv p := by cases p; rfl
  right_inv p := by
    obtain ⟨i|q,hq⟩ := p
    · exact ((Finset.mem_compl.mp hq) (finiteLevelAllowed_inl J a i)).elim
    · rfl

private theorem tasepFiniteAnchor_normalization {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (hy : StrictAnti y) : tasepPrincipalSign m * (finiteLevelAnchor N y).det = 1 := by
  classical
  let _ := finiteSeqLaw_isProbabilityMeasure N y
  have h := tasepSignedSum_principal (Finset.univ : Finset (Fin m ⊕ TasepFiniteSite N y))
    (fun i => Finset.mem_univ _)
  have hm := tasepArraySum_measure N y hy (fun _ => True) MeasurableSet.univ
  rw [Set.ofPred_true, probReal_univ] at hm
  rw [tasepUniv_principal] at h
  refine h.trans (Eq.trans ?_ hm)
  apply Finset.sum_congr
  · ext A
    simp [Finset.mem_filter]
  · intro A _; rfl

/-- The finite overlap matrix is invertible for every strictly ordered start. -/
theorem finiteLevelOverlap_isUnit {m : ℕ} (N : ℕ) (y : Fin m → ℤ) (hy : StrictAnti y) :
    IsUnit (finiteLevelBirth N y * finiteLevelPropagation N y * finiteLevelTerminal N y).det := by
  have full := tasepFiniteAnchor_normalization N y hy
  have hG : IsUnit (finiteLevelAnchor N y).det :=
    isUnit_iff_ne_zero.mpr (fun hz => by rw [hz,mul_zero] at full; exact zero_ne_one full)
  rw [finiteLevelAnchor_det] at hG
  let M := finiteLevelBirth N y * finiteLevelPropagation N y * finiteLevelTerminal N y
  exact (Matrix.isUnit_iff_isUnit_det M).mp
    ((IsUnit.neg_iff _).mp ((Matrix.isUnit_iff_isUnit_det (-M)).mpr hG))

/-- The genuine finite TASEP upper-gap event is the determinant of the explicit
biorthogonal kernel on sites strictly below the selected cutoffs. -/
theorem finiteSeqLaw_gap_eq_matrix_det {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (hy : StrictAnti y) (J : Finset (Fin m)) (a : J → ℤ) :
    (finiteSeqLaw N y).real {x | ∀ j : J, a j ≤ x j.1} =
      Matrix.det (1 - finiteLevelKernel N y J a) := by
  classical
  let _ := finiteSeqLaw_isProbabilityMeasure N y
  let G := finiteLevelAnchor N y
  let S := finiteLevelAllowed N y J a
  let bad := finiteBadSites N y J a
  let P : (Fin m → ℤ) → Prop := fun x => ∀ j : J, a j ≤ x j.1
  have full : tasepPrincipalSign m * G.det = 1 := tasepFiniteAnchor_normalization N y hy
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr fun hz => by rw [hz, mul_zero] at full; exact zero_ne_one full
  have hsum := tasepSignedSum_principal S (finiteLevelAllowed_inl J a)
  have hFilt : (tasepArrayCrop N y).filter (fun A => tasepArrayOccupied A ⊆ S) =
      (tasepArrayCrop N y).filter (fun A => P (tasepArrayPositions A)) :=
    Finset.filter_congr fun A hA => tasepArrayOccupied_allowed J a A hA
  rw [hFilt] at hsum
  have hm := tasepArraySum_measure N y hy P MeasurableSet.of_discrete
  have hM : (finiteSeqLaw N y).real {x | ∀ j : J, a j ≤ x j.1} =
      tasepPrincipalSign m * (G.toSquareBlockProp (fun i => i ∈ S)).det := by
    refine hm.symm.trans (Eq.trans ?_ hsum.symm)
    apply Finset.sum_congr
    · ext A
      simp only [Finset.mem_filter]
    · intro A _; rfl
  rw [hM, tasepDet_complement_inverse G S hG, ← mul_assoc, full, one_mul]
  let e : ↥bad ≃ ↥(Sᶜ) := finiteBadAllowedEquiv J a
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext i j
  have hsub := congrArg (fun A : Matrix (TasepFiniteSite N y) (TasepFiniteSite N y) ℝ =>
    A i.1 j.1) (finiteLevelAnchor_inv_site N y hG)
  change G⁻¹ (Sum.inr i.1) (Sum.inr j.1) = (1 - finiteLevelKernel N y J a) i j
  rw [show G⁻¹ (Sum.inr i.1) (Sum.inr j.1) = _ from hsub]
  simp only [finiteLevelKernel, Matrix.sub_apply, Matrix.add_apply, Matrix.submatrix_apply]
  rw [show (1 : Matrix (↥bad) (↥bad) ℝ) i j =
      (1 : Matrix (TasepFiniteSite N y) (TasepFiniteSite N y) ℝ) i.1 j.1 by
    simp only [Matrix.one_apply]
    exact if_congr (Subtype.ext_iff) rfl rfl]
  ring

end AiryFdd
