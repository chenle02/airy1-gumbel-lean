/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FddMeasure.FlatTasep
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Nat.Choose.Basic

open Filter Function Matrix MeasureTheory Set
open scoped BigOperators ENNReal

namespace AiryFdd

/-- The transition mass of a single fair-coin particle after `N` moves. -/
noncomputable def tasepFZero (N : ℕ) (x : ℤ) : ℝ :=
  if 0 ≤ x then (1 / 2 : ℝ) ^ N * (N.choose x.toNat : ℝ) else 0

/-- The signed difference in the backward sequential transition kernel. -/
def tasepDiff (f : ℤ → ℝ) (x : ℤ) : ℝ := f x - f (x + 1)

/-- The one-sided finite sum of a kernel supported on positions at most `N`. -/
noncomputable def tasepRightSum (N : ℕ) (f : ℤ → ℝ) (x : ℤ) : ℝ :=
  ∑ r ∈ Finset.range ((N : ℤ) - x + 1).toNat, f (x + (r : ℤ))

/-- The kernel of Borodin–Ferrari–Prähofer (2007), Section 3, at jump probability
one half. Index zero is the binomial transition. Negative indices are successive
signed finite differences and positive indices are successive upper-tail sums. -/
noncomputable def tasepF (j x : ℤ) (N : ℕ) : ℝ :=
  match j with
  | .ofNat k => ((tasepRightSum N)^[k]) (tasepFZero N) x
  | .negSucc k => (tasepDiff^[k + 1]) (tasepFZero N) x

theorem tasepF_ofNat (k N : ℕ) (x : ℤ) :
    tasepF (k : ℤ) x N = ((tasepRightSum N)^[k]) (tasepFZero N) x := rfl

theorem tasepF_negSucc (k N : ℕ) (x : ℤ) :
    tasepF (Int.negSucc k) x N = (tasepDiff^[k + 1]) (tasepFZero N) x := rfl

theorem tasepFZero_eq_zero_above (N : ℕ) {x : ℤ} (hx : (N : ℤ) < x) :
    tasepFZero N x = 0 := by
  have hx₀ : 0 ≤ x := by omega
  have hn : N < x.toNat := by omega
  simp [tasepFZero, hx₀, Nat.choose_eq_zero_of_lt hn]

theorem tasepRightSum_eq_zero_above (N : ℕ) (f : ℤ → ℝ) {x : ℤ} (hx : (N : ℤ) < x) :
    tasepRightSum N f x = 0 := by
  have h : ((N : ℤ) - x + 1).toNat = 0 := by omega
  simp [tasepRightSum, h]

theorem tasepRightSum_iter_eq_zero_above (N k : ℕ) {x : ℤ} (hx : (N : ℤ) < x) :
    ((tasepRightSum N)^[k]) (tasepFZero N) x = 0 := by
  cases k with
  | zero => exact tasepFZero_eq_zero_above N hx
  | succ k =>
    rw [iterate_succ_apply']
    exact tasepRightSum_eq_zero_above N _ hx

theorem tasepDiff_iter_eq_zero_above (N k : ℕ) {x : ℤ} (hx : (N : ℤ) < x) :
    (tasepDiff^[k]) (tasepFZero N) x = 0 := by
  induction k generalizing x with
  | zero => exact tasepFZero_eq_zero_above N hx
  | succ k ih =>
    rw [iterate_succ_apply', tasepDiff, ih hx, ih (by omega : (N : ℤ) < x + 1), sub_self]

theorem tasepF_eq_zero_above (j : ℤ) (N : ℕ) {x : ℤ} (hx : (N : ℤ) < x) :
    tasepF j x N = 0 := by
  cases j with
  | ofNat k => exact tasepRightSum_iter_eq_zero_above N k hx
  | negSucc k => exact tasepDiff_iter_eq_zero_above N (k + 1) hx

theorem tasepFZero_time (N : ℕ) (x : ℤ) :
    tasepFZero (N + 1) x = (tasepFZero N x + tasepFZero N (x - 1)) / 2 := by
  by_cases hneg : x < 0
  · simp only [tasepFZero, not_le.mpr hneg, show ¬0 ≤ x - 1 by omega,
      ite_false, add_zero, zero_div]
  · have hx : 0 ≤ x := le_of_not_gt hneg
    by_cases hzero : x = 0
    · subst x
      simp [tasepFZero, pow_succ]
      ring
    · have hx' : 0 ≤ x - 1 := by omega
      have hcast : x.toNat = (x - 1).toNat + 1 := by omega
      simp only [tasepFZero, hx, hx', ite_true]
      rw [hcast, Nat.choose_succ_succ, Nat.cast_add, pow_succ]
      ring

theorem tasepRightSum_eq_self_add (N : ℕ) (f : ℤ → ℝ) (x : ℤ)
    (hf : ∀ z : ℤ, (N : ℤ) < z → f z = 0) :
    tasepRightSum N f x = f x + tasepRightSum N f (x + 1) := by
  by_cases hx : (N : ℤ) < x
  · rw [tasepRightSum_eq_zero_above N f hx, hf x hx,
      tasepRightSum_eq_zero_above N f (by omega), add_zero]
  · have hlen : ((N : ℤ) - x + 1).toNat = ((N : ℤ) - (x + 1) + 1).toNat + 1 := by
      omega
    simp only [tasepRightSum, hlen, Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
    rw [add_comm (f x)]
    congr 1
    exact Finset.sum_congr rfl (fun _ _ => by ring_nf)

theorem tasepRightSum_next_eq (N : ℕ) (f : ℤ → ℝ) (x : ℤ)
    (hf : ∀ z : ℤ, (N : ℤ) < z → f z = 0) :
    tasepRightSum (N + 1) f x = tasepRightSum N f x := by
  by_cases hx : ((N + 1 : ℕ) : ℤ) < x
  · rw [tasepRightSum_eq_zero_above (N + 1) f hx, tasepRightSum_eq_zero_above N f (by omega)]
  · have hlen : (((N + 1 : ℕ) : ℤ) - x + 1).toNat = ((N : ℤ) - x + 1).toNat + 1 := by omega
    unfold tasepRightSum
    rw [hlen, Finset.sum_range_succ, hf _ (by omega), add_zero]

theorem tasepRightSum_time (N : ℕ) (f : ℤ → ℝ) (x : ℤ)
    (hf : ∀ z : ℤ, (N : ℤ) < z → f z = 0) :
    tasepRightSum (N + 1) (fun z => (f z + f (z - 1)) / 2) x =
      (tasepRightSum N f x + tasepRightSum N f (x - 1)) / 2 := by
  have hlen : (((N + 1 : ℕ) : ℤ) - x + 1).toNat = ((N : ℤ) - (x - 1) + 1).toNat := by omega
  simp_rw [tasepRightSum, ← Finset.sum_div, Finset.sum_add_distrib]
  congr 1
  congr 1
  · exact tasepRightSum_next_eq N f x hf
  · rw [hlen]
    exact Finset.sum_congr rfl (fun _ _ => by ring_nf)

theorem tasepRightSum_iter_time (N k : ℕ) (x : ℤ) :
    ((tasepRightSum (N + 1))^[k]) (tasepFZero (N + 1)) x =
      (((tasepRightSum N)^[k]) (tasepFZero N) x +
        ((tasepRightSum N)^[k]) (tasepFZero N) (x - 1)) / 2 := by
  induction k generalizing x with
  | zero => exact tasepFZero_time N x
  | succ k ih =>
    simp only [iterate_succ_apply']
    have h := funext ih
    rw [h]
    exact tasepRightSum_time N _ x (fun z hz => tasepRightSum_iter_eq_zero_above N k hz)

theorem tasepDiff_iter_time (N k : ℕ) (x : ℤ) :
    (tasepDiff^[k]) (tasepFZero (N + 1)) x =
      ((tasepDiff^[k]) (tasepFZero N) x + (tasepDiff^[k]) (tasepFZero N) (x - 1)) / 2 := by
  induction k generalizing x with
  | zero => exact tasepFZero_time N x
  | succ k ih =>
    simp only [iterate_succ_apply', tasepDiff]
    rw [ih x, ih (x + 1)]
    rw [show x + 1 - 1 = x by ring]
    ring

/-- The free Bernoulli time recurrence before imposing the exclusion boundary. -/
theorem tasepF_time (j x : ℤ) (N : ℕ) :
    tasepF j x (N + 1) = (tasepF j x N + tasepF j (x - 1) N) / 2 := by
  cases j with
  | ofNat k => exact tasepRightSum_iter_time N k x
  | negSucc k => exact tasepDiff_iter_time N (k + 1) x

/-- The signed spatial difference reduces the index by one. This identity imposes the
adjacent-particle boundary condition in the transition determinant. -/
theorem tasepF_sub_succ (j x : ℤ) (N : ℕ) :
    tasepF (j - 1) x N = tasepF j x N - tasepF j (x + 1) N := by
  cases j with
  | ofNat k =>
    cases k with
    | zero => rfl
    | succ k =>
      have h : (Int.ofNat (k + 1) : ℤ) - 1 = (k : ℤ) := by
        change ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ)
        omega
      rw [h]
      simp only [tasepF_ofNat, show Int.ofNat (k + 1) = ((k + 1 : ℕ) : ℤ) from rfl,
        iterate_succ_apply']
      nth_rewrite 1 [tasepRightSum_eq_self_add N _ x (fun _ hz => tasepRightSum_iter_eq_zero_above N k hz)]
      ring
  | negSucc k =>
    have h : Int.negSucc k - 1 = Int.negSucc (k + 1) := by omega
    rw [h, tasepF_negSucc, iterate_succ_apply']
    rfl

/-- Transition matrix in decreasing particle-position order. -/
noncomputable def tasepTransitionMatrix {m : ℕ} (N : ℕ) (y x : Fin m → ℤ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of (fun i j => tasepF ((j.1 : ℤ) - (i.1 : ℤ)) (x i - y j) N)

/-- BFP's signed transition determinant in right-to-left label order. Reversing both
index orders gives the displayed BFP matrix. The column index selects the initial position. -/
noncomputable def tasepTransitionDet {m : ℕ} (N : ℕ) (y x : Fin m → ℤ) : ℝ :=
  (tasepTransitionMatrix N y x).det


theorem tasepFZero_zero (x : ℤ) : tasepFZero 0 x = if x = 0 then 1 else 0 := by
  by_cases h : x = 0
  · simp [h, tasepFZero]
  by_cases hn : 0 ≤ x
  · have hp : 0 < x.toNat := by omega
    simp [tasepFZero, h, hn, Nat.choose_eq_zero_of_lt hp]
  · simp [tasepFZero, h, hn]

theorem tasepDiff_iter_zero_time_eq_zero_below (k : ℕ) {x : ℤ} (hx : x < -(k : ℤ)) :
    (tasepDiff^[k]) (tasepFZero 0) x = 0 := by
  induction k generalizing x with
  | zero =>
    simp [tasepFZero_zero, show x ≠ 0 by omega]
  | succ k ih =>
    rw [iterate_succ_apply', tasepDiff, ih (by omega : x < -(k : ℤ)),
      ih (by omega : x + 1 < -(k : ℤ)), sub_self]

theorem tasepF_zero_time_eq_zero_below {j x : ℤ} (hj : j ≤ 0) (hx : x < j) :
    tasepF j x 0 = 0 := by
  cases j with
  | ofNat k =>
    have hk : k = 0 := by
      change (k : ℤ) ≤ 0 at hj
      omega
    subst k
    exact tasepDiff_iter_zero_time_eq_zero_below 0 (by omega)
  | negSucc k =>
    rw [tasepF_negSucc]
    exact tasepDiff_iter_zero_time_eq_zero_below (k + 1) (by omega)

/-- Integer strict order gives at least the index separation between positions. -/
theorem tasep_strictAnti_gap {m : ℕ} (x : Fin m → ℤ) (hx : StrictAnti x)
    (i j : Fin m) (hij : i ≤ j) :
    x j + ((j.1 : ℤ) - (i.1 : ℤ)) ≤ x i := by
  have step (l : ℕ) (hli : i.1 ≤ l) (hlm : l < m) :
      x ⟨l, hlm⟩ + ((l : ℤ) - (i.1 : ℤ)) ≤ x i := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hli
    induction d with
    | zero =>
      have he : (⟨i.1 + 0, hlm⟩ : Fin m) = i := Fin.ext (by simp)
      rw [he]
      simp
    | succ d ih =>
      let k : Fin m := ⟨i.1 + d, by omega⟩
      let k' : Fin m := ⟨i.1 + (d + 1), hlm⟩
      have h₁ := ih (Nat.le_add_right _ _) k.2
      have h₂ := hx (show k < k' by change i.1 + d < i.1 + (d + 1); omega)
      change x k + ((↑(i.1 + d) : ℤ) - ↑i.1) ≤ x i at h₁
      change x k' + ((↑(i.1 + (d + 1)) : ℤ) - ↑i.1) ≤ x i
      omega
  exact step j.1 hij j.2

/-- A rectangular zero region of a matrix kills its determinant when there are too few
columns left for the designated rows. -/
theorem tasep_det_eq_zero_of_row_support {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (S T : Finset (Fin m)) (hcard : T.card < S.card)
    (hzero : ∀ i ∈ S, ∀ j ∉ T, A i j = 0) : A.det = 0 := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hex : ∃ i ∈ S, σ i ∉ T := by
    by_contra! h
    exact (not_le_of_gt hcard) (Finset.card_le_card_of_injOn σ
      (fun i hi => h i hi) σ.injective.injOn)
  obtain ⟨i, hi, hn⟩ := hex
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (hzero i hi (σ i) hn), smul_zero]

/-- The signed determinant at time zero is exactly the identity transition on ordered states. -/
theorem tasepTransitionDet_zero {m : ℕ} (y x : Fin m → ℤ)
    (hy : StrictAnti y) (hx : StrictAnti x) :
    tasepTransitionDet 0 y x = if x = y then 1 else 0 := by
  classical
  by_cases he : x = y
  · subst x
    rw [ite_eq_left rfl, tasepTransitionDet]
    rw [Matrix.det_of_isLowerTriangular]
    · simp [tasepTransitionMatrix, tasepF, tasepFZero_zero]
    · intro i j hij
      change tasepF _ (y i - y j) 0 = 0
      apply tasepF_eq_zero_above
      have hlt : y j < y i := hy (show i < j from hij)
      omega
  · rw [ite_eq_right he, tasepTransitionDet]
    have hk : ∃ k : Fin m, x k ≠ y k := by
      by_contra! h
      exact he (funext h)
    obtain ⟨k, hk⟩ := hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · apply tasep_det_eq_zero_of_row_support _ (Finset.Ici k) (Finset.Ioi k)
      · simp only [Fin.card_Ioi, Fin.card_Ici]
        omega
      · intro i hi j hj
        have hki : k ≤ i := Finset.mem_Ici.mp hi
        have hjk : j ≤ k := le_of_not_gt (fun h => hj (Finset.mem_Ioi.mpr h))
        have hxi := tasep_strictAnti_gap x hx k i hki
        have hyj := tasep_strictAnti_gap y hy j k hjk
        change k.1 ≤ i.1 at hki
        change j.1 ≤ k.1 at hjk
        change tasepF ((j.1 : ℤ) - (i.1 : ℤ)) (x i - y j) 0 = 0
        apply tasepF_zero_time_eq_zero_below <;> omega
    · apply tasep_det_eq_zero_of_row_support _ (Finset.Iic k) (Finset.Iio k)
      · simp only [Fin.card_Iic, Fin.card_Iio]
        omega
      · intro i hi j hj
        have hik : i ≤ k := Finset.mem_Iic.mp hi
        have hkj : k ≤ j := le_of_not_gt (fun h => hj (Finset.mem_Iio.mpr h))
        have hxi := hx.antitone hik
        have hyj := hy.antitone hkj
        change tasepF _ (x i - y j) 0 = 0
        apply tasepF_eq_zero_above
        omega

/-- The two possibilities for a displacement in one update, encoded by a coin. -/
def tasepBit (b : Bool) : ℤ := if b then 1 else 0

/-- The candidate predecessor at one update, before enforcing exclusion. -/
def tasepPredecessor {m : ℕ} (x : Fin m → ℤ) (b : Fin m → Bool) : Fin m → ℤ :=
  fun i => x i - tasepBit (b i)

/-- Expand the determinant of the rowwise Bernoulli averages into a free sum over coin rows. -/
theorem tasepTransitionDet_free_time {m : ℕ} (N : ℕ) (y x : Fin m → ℤ) :
    tasepTransitionDet (N + 1) y x =
      (1 / 2 : ℝ) ^ m * ∑ b : Fin m → Bool, tasepTransitionDet N y (tasepPredecessor x b) := by
  classical
  let M (c : Fin m → Bool) : Matrix (Fin m) (Fin m) ℝ :=
    fun i j => tasepF ((j.1 : ℤ) - (i.1 : ℤ)) (x i - tasepBit (c i) - y j) N
  unfold tasepTransitionDet
  change (tasepTransitionMatrix (N + 1) y x).det = (1 / 2 : ℝ) ^ m * ∑ c, (M c).det
  have hdet (A : Matrix (Fin m) (Fin m) ℝ) :
      A.det = ∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℝ) * ∏ i, A i (σ i) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  simp_rw [hdet, Finset.mul_sum, tasepTransitionMatrix, Matrix.of_apply]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin m → Bool))]
  apply Finset.sum_congr rfl
  intro σ _
  have havg (i : Fin m) :
      tasepF (((σ i).1 : ℤ) - (i.1 : ℤ)) (x i - y (σ i)) (N + 1) =
        ∑ b : Bool, (1 / 2 : ℝ) *
          tasepF (((σ i).1 : ℤ) - (i.1 : ℤ)) (x i - tasepBit b - y (σ i)) N := by
    rw [tasepF_time]
    simp [tasepBit]
    rw [show x i - 1 - y (σ i) = x i - y (σ i) - 1 by ring]
    ring
  simp_rw [havg, Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, M]
  ring

/-- If adjacent predecessor positions collide, raising the right particle by one leaves the
transition determinant unchanged. The difference between the two rows equals the next row. -/
theorem tasepTransitionDet_collision {m : ℕ} (N : ℕ) (y z : Fin m → ℤ)
    (i j : Fin m) (hij : j.1 = i.1 + 1) (hz : z i = z j) :
    tasepTransitionDet N y z = tasepTransitionDet N y (update z i (z i + 1)) := by
  let A := tasepTransitionMatrix N y (update z i (z i + 1))
  have hne : i ≠ j := fun he => by rw [← he] at hij; omega
  have hA : tasepTransitionMatrix N y z = A.updateRow i (A i + A j) := by
    ext k l
    by_cases hk : k = i
    · subst k
      rw [Matrix.updateRow_self]
      change tasepF ((l.1 : ℤ) - (i.1 : ℤ)) (z i - y l) N = A i l + A j l
      simp only [A, tasepTransitionMatrix, Matrix.of_apply, update_self, update_of_ne hne.symm, ← hz]
      rw [show ((l.1 : ℤ) - (j.1 : ℤ)) = ((l.1 : ℤ) - (i.1 : ℤ)) - 1 by omega,
        tasepF_sub_succ, show z i + 1 - y l = (z i - y l) + 1 by ring]
      ring
    · rw [Matrix.updateRow_ne hk]
      simp [tasepTransitionMatrix, A, update_of_ne hk]
  unfold tasepTransitionDet
  rw [hA, Matrix.det_updateRow_add_self _ hne]


/-- A gap of one between consecutive labels in the destination state. -/
def tasepAdjacent {m : ℕ} (x : Fin m → ℤ) (k : ℕ) : Prop :=
  ∃ h : k + 1 < m, x ⟨k, by omega⟩ = x ⟨k + 1, h⟩ + 1

theorem tasepAdjacent_iff {m : ℕ} (x : Fin m → ℤ) (k : ℕ) (hk : k + 1 < m) :
    tasepAdjacent x k ↔ x ⟨k, by omega⟩ = x ⟨k + 1, hk⟩ + 1 :=
  ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨hk, hh⟩⟩

/-- A free coin is retained precisely when all coins from that label through the end of its
cluster are successes. This is the collision elimination sweep from larger to smaller indices. -/
noncomputable def tasepCollapsed {m : ℕ} (x : Fin m → ℤ) (b : Fin m → Bool) (i : Fin m) : Bool :=
  open Classical in decide (∀ j : Fin m, i ≤ j →
    (∀ k : ℕ, i.1 ≤ k → k < j.1 → tasepAdjacent x k) → b j = true)

theorem tasepCollapsed_eq_true_iff {m : ℕ} (x : Fin m → ℤ) (b : Fin m → Bool) (i : Fin m) :
    tasepCollapsed x b i = true ↔ b i = true ∧
      ∀ j : Fin m, j.1 = i.1 + 1 → tasepAdjacent x i.1 → tasepCollapsed x b j = true := by
  classical
  simp only [tasepCollapsed, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨h i le_rfl (fun _ h₁ h₂ => by omega), ?_⟩
    intro j hj ha l hjl hl
    apply h l
    · change j.1 ≤ l.1 at hjl
      change i.1 ≤ l.1
      omega
    · intro k hk hkl
      by_cases he : k = i.1
      · exact he ▸ ha
      · exact hl k (by omega) hkl
  · rintro ⟨hi, hs⟩ j hij hj
    change i.1 ≤ j.1 at hij
    by_cases he : i = j
    · simpa [he] using hi
    · have hlt : i.1 < j.1 := by
        have hn : i.1 ≠ j.1 := fun h => he (Fin.ext h)
        omega
      let next : Fin m := ⟨i.1 + 1, by have := j.2; omega⟩
      exact hs next rfl (hj i.1 le_rfl hlt) j
        (show next.1 ≤ j.1 by dsimp [next]; omega)
        (fun k hk hkj => hj k (by dsimp [next] at hk; omega) hkj)

theorem tasepCollapsed_here {m : ℕ} (x : Fin m → ℤ) (b : Fin m → Bool) (k : ℕ)
    (hk : k + 1 < m) :
    tasepCollapsed x b ⟨k, by omega⟩ = true ↔
      b ⟨k, by omega⟩ = true ∧
      (tasepAdjacent x k → tasepCollapsed x b ⟨k + 1, hk⟩ = true) := by
  rw [tasepCollapsed_eq_true_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂ _ rfl⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun j hj h => (Fin.ext hj : j = ⟨k + 1, hk⟩) ▸ h₂ h⟩

theorem tasepCollapsed_at_end {m : ℕ} (x : Fin m → ℤ) (b : Fin m → Bool) (i : Fin m)
    (hEnd : ¬tasepAdjacent x i.1) : tasepCollapsed x b i = b i := by
  apply Bool.eq_iff_iff.mpr
  rw [tasepCollapsed_eq_true_iff]
  simp [hEnd]

/-- A predecessor is ordered precisely when the displacement bits are nondecreasing along
each cluster of adjacent destination positions. -/
theorem tasepPredecessor_strictAnti_iff {m : ℕ} (x : Fin m → ℤ) (hx : StrictAnti x)
    (b : Fin m → Bool) :
    StrictAnti (tasepPredecessor x b) ↔
      ∀ k (hk : k + 1 < m), tasepAdjacent x k →
        b ⟨k, by omega⟩ = true → b ⟨k + 1, hk⟩ = true := by
  cases m with
  | zero => exact ⟨fun _ _ hk => by omega, fun _ {i} => Fin.elim0 i⟩
  | succ m =>
    rw [Fin.strictAnti_iff_succ_lt]
    constructor
    · intro h k hk hadj h₁
      let i : Fin m := ⟨k, by omega⟩
      have hp := h i
      have he := (tasepAdjacent_iff x k hk).mp hadj
      change x ⟨k + 1, hk⟩ - tasepBit (b ⟨k + 1, hk⟩) <
        x ⟨k, by omega⟩ - tasepBit (b ⟨k, by omega⟩) at hp
      rw [he, h₁] at hp
      cases h₂ : b ⟨k + 1, hk⟩ <;> simp [tasepBit, h₂] at hp ⊢
    · intro h i
      let k := i.1
      have hk : k + 1 < m + 1 := by have := i.2; omega
      have hgap := hx (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
      change x ⟨k + 1, hk⟩ < x ⟨k, by omega⟩ at hgap
      change x ⟨k + 1, hk⟩ - tasepBit (b ⟨k + 1, hk⟩) <
        x ⟨k, by omega⟩ - tasepBit (b ⟨k, by omega⟩)
      cases h₁ : b ⟨k, by omega⟩ <;> cases h₂ : b ⟨k + 1, hk⟩ <;>
        simp only [h₁, h₂, tasepBit, Bool.false_eq_true, ite_false, ite_true, sub_zero]
      all_goals try omega
      have hn : ¬tasepAdjacent x k := fun ha => by
        have hh := h k hk ha h₁
        rw [h₂] at hh
        contradiction
      rw [tasepAdjacent_iff x k hk] at hn
      omega

theorem tasepCollapsed_ordered {m : ℕ} (x : Fin m → ℤ) (hx : StrictAnti x)
    (b : Fin m → Bool) : StrictAnti (tasepPredecessor x (tasepCollapsed x b)) := by
  apply (tasepPredecessor_strictAnti_iff x hx _).2
  intro k hk hgap hb
  exact ((tasepCollapsed_here x b k hk).1 hb).2 hgap

/-- Retain the original bits before `k` and the corrected bits from `k` onward. -/
noncomputable def tasepMaskAtCut {m : ℕ} (x : Fin m → ℤ) (b : Fin m → Bool)
    (k : ℕ) : Fin m → Bool := fun i => if k ≤ i.1 then tasepCollapsed x b i else b i

theorem tasepTransitionDet_cut_eq {m : ℕ} (N : ℕ) (y x : Fin m → ℤ) (b : Fin m → Bool)
    (k : ℕ) :
    tasepTransitionDet N y (tasepPredecessor x (tasepMaskAtCut x b (k + 1))) =
      tasepTransitionDet N y (tasepPredecessor x (tasepMaskAtCut x b k)) := by
  classical
  by_cases hk : k < m
  · let i : Fin m := ⟨k, hk⟩
    have hSame (j : Fin m) (hj : j ≠ i) :
        tasepMaskAtCut x b (k + 1) j = tasepMaskAtCut x b k j := by
      have hv : j.1 ≠ k := fun h => hj (Fin.ext h)
      unfold tasepMaskAtCut
      by_cases hle : k + 1 ≤ j.1
      · simp [hle, show k ≤ j.1 by omega]
      · simp [hle, show ¬k ≤ j.1 by omega]
    by_cases he : tasepCollapsed x b i = b i
    · congr 2
      funext j
      by_cases hj : j = i
      · subst j
        simp [tasepMaskAtCut, i, he]
      · exact hSame j hj
    · have htrue : b i = true := by
        cases h : b i
        · exact False.elim (he (by
            rw [h]
            apply Bool.eq_false_iff.mpr
            intro hc
            have := ((tasepCollapsed_eq_true_iff x b i).1 hc).1
            simp [h] at this))
        · rfl
      have hfalse : tasepCollapsed x b i = false := by
        rw [htrue] at he
        exact Bool.eq_false_iff.mpr he
      obtain ⟨j, hj, hadj, hnext⟩ : ∃ j : Fin m, j.1 = i.1 + 1 ∧
          tasepAdjacent x i.1 ∧ tasepCollapsed x b j ≠ true := by
        have hn : ¬∀ j : Fin m, j.1 = i.1 + 1 → tasepAdjacent x i.1 →
            tasepCollapsed x b j = true := by
          intro hh
          have hc := (tasepCollapsed_eq_true_iff x b i).2 ⟨htrue, hh⟩
          simp [hfalse] at hc
        push Not at hn
        exact hn
      let z := tasepPredecessor x (tasepMaskAtCut x b (k + 1))
      have hz : z i = z j := by
        have hjk : k + 1 ≤ j.1 := by dsimp [i] at hj; omega
        have hj' : j = ⟨k + 1, by have := j.2; change j.1 = k + 1 at hj; omega⟩ := Fin.ext hj
        have hgap : x i = x j + 1 := by
          have h := (tasepAdjacent_iff x k (by have := j.2; change j.1 = k + 1 at hj; omega)).1 hadj
          rw [hj']
          exact h
        simp [z, tasepPredecessor, tasepMaskAtCut, tasepBit, i, hjk,
          htrue, Bool.eq_false_iff.mpr hnext, hgap]
      have hup : update z i (z i + 1) = tasepPredecessor x (tasepMaskAtCut x b k) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [z, tasepPredecessor, tasepMaskAtCut, tasepBit, i, htrue, hfalse]
        · rw [update_of_ne hji]
          simp only [z, tasepPredecessor, hSame j hji]
      exact (tasepTransitionDet_collision N y z i j hj hz).trans (congrArg _ hup)
  · congr 2
    funext i
    have hi := i.2
    simp [tasepMaskAtCut, show ¬k + 1 ≤ i.1 by omega, show ¬k ≤ i.1 by omega]

/-- The free determinant is unchanged by correcting every colliding predecessor. -/
theorem tasepTransitionDet_eq_collapsed {m : ℕ} (N : ℕ) (y x : Fin m → ℤ) (b : Fin m → Bool) :
    tasepTransitionDet N y (tasepPredecessor x b) =
      tasepTransitionDet N y (tasepPredecessor x (tasepCollapsed x b)) := by
  let f (k : ℕ) := tasepTransitionDet N y (tasepPredecessor x (tasepMaskAtCut x b k))
  have h (k : ℕ) : f k = f 0 := by
    induction k with
    | zero => rfl
    | succ k ih => exact (tasepTransitionDet_cut_eq N y x b k).trans ih
  have hm : tasepMaskAtCut x b m = b := by funext i; simp [tasepMaskAtCut, not_le_of_gt i.2]
  have h0 : tasepMaskAtCut x b 0 = tasepCollapsed x b := by funext i; simp [tasepMaskAtCut]
  simpa only [f, hm, h0] using h m


/-- Whether a particle has a right neighbour one site away in the destination state. -/
def tasepAdjacentBefore {m : ℕ} (x : Fin m → ℤ) (i : Fin m) : Prop :=
  0 < i.1 ∧ tasepAdjacent x (i.1 - 1)

theorem tasepAdjacentBefore_succ {m : ℕ} (x : Fin m → ℤ) (k : ℕ) (h : k + 1 < m) :
    tasepAdjacentBefore x ⟨k + 1, h⟩ ↔ tasepAdjacent x k := by
  simp [tasepAdjacentBefore]

/-- A compatible coin succeeds at every moved particle and fails at every unblocked
particle that stayed. The coins at blocked particles can take either value. -/
def tasepCoinRowOK {m : ℕ} (x : Fin m → ℤ) (b c : Fin m → Bool) : Prop :=
  ∀ i, (b i = true → c i = true) ∧
    (b i = false → ¬tasepAdjacentBefore x i → c i = false)

theorem tasepLocalUpdate_eq_iff (x p : ℤ) (hp : x < p) (b c : Bool) :
    (if c = true ∧ x - tasepBit b + 1 < p then x - tasepBit b + 1 else x - tasepBit b) = x ↔
      (b = true → c = true) ∧ (b = false → p ≠ x + 1 → c = false) := by
  cases b <;> cases c <;> simp [tasepBit] <;> omega

theorem tasepFirstUpdate_eq_iff (x : ℤ) (b c : Bool) :
    (if c then x - tasepBit b + 1 else x - tasepBit b) = x ↔
      (b = true → c = true) ∧ (b = false → c = false) := by
  cases b <;> cases c <;> simp [tasepBit]

theorem seqTasepStep_predecessor_eq_iff {m : ℕ} (x : Fin m → ℤ) (hx : StrictAnti x)
    (b c : Fin m → Bool) :
    seqTasepStep (tasepPredecessor x b) c = x ↔ tasepCoinRowOK x b c := by
  let z := tasepPredecessor x b
  have h (i : Fin m) (hp : ∀ k : Fin m, k < i → seqTasepStep z c k = x k) :
      seqTasepStep z c i = x i ↔
        (b i = true → c i = true) ∧ (b i = false → ¬tasepAdjacentBefore x i → c i = false) := by
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero =>
      rw [seqTasepStep_zero]
      dsimp only [z, tasepPredecessor]
      rw [tasepFirstUpdate_eq_iff]
      simp [tasepAdjacentBefore]
    | succ k =>
      let j : Fin m := ⟨k, by omega⟩
      let i : Fin m := ⟨k + 1, hi⟩
      have hji : j < i := by change k < k + 1; omega
      have hEq := hp j hji
      rw [seqTasepStep_succ]
      change (if c i = true ∧ x i - tasepBit (b i) + 1 < seqTasepStep z c j
          then x i - tasepBit (b i) + 1 else x i - tasepBit (b i)) = x i ↔ _
      rw [hEq, tasepLocalUpdate_eq_iff _ _ (hx hji), tasepAdjacentBefore_succ, tasepAdjacent_iff x k hi]
  constructor
  · intro he i
    exact (h i fun j _ => congrFun he j).1 (congrFun he i)
  · intro hrows
    funext i
    induction i using WellFounded.induction (InvImage.wf (fun i : Fin m => i.1) Nat.lt_wfRel.wf) with
    | h i ih =>
      exact (h i (fun j hj => ih j (show j.1 < i.1 from hj))).2 (hrows i)

noncomputable def tasepActualCoins {m : ℕ} (x : Fin m → ℤ)
    (b raw : Fin m → Bool) (i : Fin m) : Bool :=
  open Classical in
  if b i then true
  else if tasepAdjacentBefore x i then raw ⟨i.1 - 1, by have := i.2; omega⟩ else false

noncomputable def tasepRecoverCoins {m : ℕ} (x : Fin m → ℤ)
    (b c : Fin m → Bool) (i : Fin m) : Bool :=
  open Classical in
  if b i then true
  else if h : i.1 + 1 < m then
    if tasepAdjacent x i.1 ∧ b ⟨i.1 + 1, h⟩ = false then c ⟨i.1 + 1, h⟩ else false
  else false

theorem tasepActualCoins_ok {m : ℕ} (x : Fin m → ℤ) (b raw : Fin m → Bool) :
    tasepCoinRowOK x b (tasepActualCoins x b raw) := by
  intro i
  constructor
  · intro h
    simp [tasepActualCoins, h]
  · intro h hi
    simp [tasepActualCoins, h, hi]

theorem tasepRecover_actual {m : ℕ} (x : Fin m → ℤ) (raw : Fin m → Bool) :
    tasepRecoverCoins x (tasepCollapsed x raw) (tasepActualCoins x (tasepCollapsed x raw) raw)
      = raw := by
  classical
  funext i
  let b := tasepCollapsed x raw
  by_cases hbi : b i = true
  · have hraw := ((tasepCollapsed_eq_true_iff x raw i).1 hbi).1
    change tasepRecoverCoins x b (tasepActualCoins x b raw) i = raw i
    simp [tasepRecoverCoins, hbi, hraw]
  · have hfalse := Bool.eq_false_iff.mpr hbi
    by_cases hn : i.1 + 1 < m
    · let j : Fin m := ⟨i.1 + 1, hn⟩
      by_cases h : tasepAdjacent x i.1 ∧ b j = false
      · have ha : tasepAdjacentBefore x j := (tasepAdjacentBefore_succ x i.1 hn).2 h.1
        have hEq : (⟨j.1 - 1, by have := j.2; omega⟩ : Fin m) = i := Fin.ext (by
          change i.1 + 1 - 1 = i.1
          omega)
        change tasepRecoverCoins x b (tasepActualCoins x b raw) i = raw i
        simp [tasepRecoverCoins, hfalse, hn, h, j, tasepActualCoins, ha]
      · have hs : ∀ j : Fin m, j.1 = i.1 + 1 → tasepAdjacent x i.1 → b j = true := by
          intro j' hj' ha
          have hEq : j' = j := Fin.ext hj'
          subst j'
          by_contra hb
          exact h ⟨ha, Bool.eq_false_iff.mpr hb⟩
        have hraw : raw i = false := Bool.eq_false_iff.mpr fun htrue =>
          hbi ((tasepCollapsed_eq_true_iff x raw i).2 ⟨htrue, hs⟩)
        change tasepRecoverCoins x b (tasepActualCoins x b raw) i = raw i
        simp [tasepRecoverCoins, hfalse, hn, h, j, hraw]
    · have hEnd : ¬tasepAdjacent x i.1 := fun ⟨k, _⟩ => hn k
      have hraw : raw i = false := (tasepCollapsed_at_end x raw i hEnd).symm.trans hfalse
      change tasepRecoverCoins x b (tasepActualCoins x b raw) i = raw i
      simp [tasepRecoverCoins, hfalse, hn, hraw]

theorem tasepCollapsed_recover {m : ℕ} (x : Fin m → ℤ) (hx : StrictAnti x)
    (b c : Fin m → Bool) (hb : StrictAnti (tasepPredecessor x b)) :
    tasepCollapsed x (tasepRecoverCoins x b c) = b := by
  classical
  let raw := tasepRecoverCoins x b c
  funext i
  induction i using WellFounded.induction (InvImage.wf (fun i : Fin m => m - i.1) Nat.lt_wfRel.wf) with
  | h i ih =>
    apply Bool.eq_iff_iff.mpr
    rw [tasepCollapsed_eq_true_iff]
    have hNext (j : Fin m) (hj : j.1 = i.1 + 1) : tasepCollapsed x raw j = b j :=
      ih j (show m - j.1 < m - i.1 by have := j.2; omega)
    constructor
    · rintro ⟨hraw, hrem⟩
      by_contra hbi
      have hfalse := Bool.eq_false_iff.mpr hbi
      by_cases hn : i.1 + 1 < m
      · let j : Fin m := ⟨i.1 + 1, hn⟩
        by_cases hclose : tasepAdjacent x i.1 ∧ b j = false
        · have ht := hrem j rfl hclose.1
          rw [hNext j rfl, hclose.2] at ht
          contradiction
        · change raw i = true at hraw
          simp [raw, tasepRecoverCoins, hfalse, hn, hclose, j] at hraw
      · change raw i = true at hraw
        simp [raw, tasepRecoverCoins, hfalse, hn] at hraw
    · intro hbi
      refine ⟨by simp [tasepRecoverCoins, hbi], fun j hj ha => ?_⟩
      rw [hNext j hj]
      have hk : i.1 + 1 < m := by have := j.2; omega
      have h := (tasepPredecessor_strictAnti_iff x hx _).1 hb i.1 hk ha hbi
      exact (Fin.ext hj : j = ⟨i.1 + 1, hk⟩) ▸ h

theorem tasepActual_recover {m : ℕ} (x : Fin m → ℤ) (hx : StrictAnti x)
    (b c : Fin m → Bool) (hb : StrictAnti (tasepPredecessor x b))
    (hc : tasepCoinRowOK x b c) :
    tasepActualCoins x b (tasepRecoverCoins x b c) = c := by
  classical
  funext i
  by_cases hi : b i = true
  · simp [tasepActualCoins, hi, (hc i).1 hi]
  · have hf := Bool.eq_false_iff.mpr hi
    by_cases hadj : tasepAdjacentBefore x i
    · have hpos := hadj.1
      have hgap := hadj.2
      let j : Fin m := ⟨i.1 - 1, by have := i.2; omega⟩
      have hjk : j.1 + 1 = i.1 := by dsimp [j]; omega
      have hn : j.1 + 1 < m := hjk ▸ i.2
      have he : (⟨j.1 + 1, hn⟩ : Fin m) = i := Fin.ext hjk
      have hfalse : b j = false := Bool.eq_false_iff.mpr fun ht => by
        have h := (tasepPredecessor_strictAnti_iff x hx _).1 hb j.1 hn hgap ht
        rw [he, hf] at h
        contradiction
      simp only [tasepActualCoins, hf, Bool.false_eq_true, ite_false, ite_eq_left hadj]
      change tasepRecoverCoins x b c j = c i
      unfold tasepRecoverCoins
      rw [ite_eq_right (by simpa [hfalse]), dite_eq_left hn, he, ite_eq_left ⟨hgap,hf⟩]
    · simp [tasepActualCoins, hf, hadj, (hc i).2 hf hadj]

/-- An ordered predecessor paired with a coin row that sends it to the target state. -/
abbrev TasepValidPredecessor {m : ℕ} (x : Fin m → ℤ) :=
  {p : (Fin m → Bool) × (Fin m → Bool) //
    StrictAnti (tasepPredecessor x p.1) ∧ seqTasepStep (tasepPredecessor x p.1) p.2 = x}

/-- The free masks enumerate exactly the ordered predecessors together with the coin rows
that send them to the specified destination. A blocked coin carries the preceding free bit. -/
noncomputable def tasepFreeMaskEquiv {m : ℕ} (x : Fin m → ℤ) (hx : StrictAnti x) :
    (Fin m → Bool) ≃ TasepValidPredecessor x where
  toFun raw := ⟨(tasepCollapsed x raw, tasepActualCoins x (tasepCollapsed x raw) raw),
    tasepCollapsed_ordered x hx raw,
    (seqTasepStep_predecessor_eq_iff x hx _ _).2 (tasepActualCoins_ok x _ _)⟩
  invFun p := tasepRecoverCoins x p.1.1 p.1.2
  left_inv := tasepRecover_actual x
  right_inv p := by
    apply Subtype.ext
    have h := tasepCollapsed_recover x hx p.1.1 p.1.2 p.2.1
    change (tasepCollapsed x (tasepRecoverCoins x p.1.1 p.1.2),
      tasepActualCoins x (tasepCollapsed x (tasepRecoverCoins x p.1.1 p.1.2))
        (tasepRecoverCoins x p.1.1 p.1.2)) = (p.1.1, p.1.2)
    rw [h, tasepActual_recover x hx p.1.1 p.1.2 p.2.1
      ((seqTasepStep_predecessor_eq_iff x hx _ _).1 p.2.2)]


open Classical in
theorem finiteSeqLaw_measureReal_apply {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (s : Set (Fin m → ℤ)) (hs : MeasurableSet s) :
    (finiteSeqLaw N y).real s =
      (1 / 2 : ℝ) ^ (N * m) * ∑ c : Fin N → Fin m → Bool,
        if runSeqTasep y c ∈ s then 1 else 0 := by
  classical
  rw [measureReal_def, finiteSeqLaw, Measure.finsetSum_apply, Finset.mul_sum, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro c _
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_inv]
    by_cases h : runSeqTasep y c ∈ s <;> simp [indicator_apply, one_div, h]
  · intro c _
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
    apply ENNReal.mul_ne_top
    · exact ENNReal.pow_ne_top (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ ⊤)
    · rw [indicator_apply]; split <;> simp

theorem tasepPredecessor_existsUnique_of_step {m : ℕ} (z x : Fin m → ℤ) (c : Fin m → Bool)
    (h : seqTasepStep z c = x) :
    ∃! b : Fin m → Bool, tasepPredecessor x b = z := by
  classical
  let b : Fin m → Bool := fun i => decide (x i = z i + 1)
  have hz (i : Fin m) : z i ≤ x i ∧ x i ≤ z i + 1 := by
    rw [← h]
    exact seqTasepStep_bounds z c i
  refine ⟨b, ?_, ?_⟩
  · funext i
    have hi := hz i
    by_cases hv : x i = z i + 1
    · simp [tasepPredecessor, tasepBit, b, hv]
    · have he : x i = z i := by omega
      simp [tasepPredecessor, tasepBit, b, hv, he]
  · intro b' hb'
    funext i
    have hp := congrFun hb' i
    cases hi : b' i <;> simp [tasepPredecessor, tasepBit, hi] at hp <;>
      simp [b, hi] <;> omega

theorem tasepStepIndicator_eq_sum_valid {m : ℕ} (z x : Fin m → ℤ) (c : Fin m → Bool)
    (hz : StrictAnti z) :
    (if seqTasepStep z c = x then (1 : ℝ) else 0) =
      ∑ p : TasepValidPredecessor x,
        if p.1.2 = c ∧ tasepPredecessor x p.1.1 = z then 1 else 0 := by
  classical
  by_cases h : seqTasepStep z c = x
  · obtain ⟨b, hb, huniq⟩ := tasepPredecessor_existsUnique_of_step z x c h
    let p : TasepValidPredecessor x := ⟨(b,c), show StrictAnti (tasepPredecessor x b) ∧
        seqTasepStep (tasepPredecessor x b) c = x by rw [hb]; exact ⟨hz,h⟩⟩
    rw [ite_eq_left h, Finset.sum_eq_single p]
    · simp [p, hb]
    · intro q _ hqp
      refine ite_eq_right ?_
      rintro ⟨h1,h2⟩
      exact hqp (Subtype.ext (Prod.ext (huniq _ h2) h1))
    · simp
  · rw [ite_eq_right h]
    refine (Finset.sum_eq_zero fun p _ => ite_eq_right ?_).symm
    rintro ⟨h1,h2⟩
    exact h (by simpa only [h1,h2] using p.2.2)

theorem finiteSeqLaw_real_succ {m : ℕ} (N : ℕ) (y x : Fin m → ℤ) (hy : StrictAnti y) :
    (finiteSeqLaw (N + 1) y).real {x} =
      (1 / 2 : ℝ) ^ m *
        ∑ p : TasepValidPredecessor x,
          (finiteSeqLaw N y).real {tasepPredecessor x p.1.1} := by
  classical
  let e := Fin.snocEquiv (fun _ : Fin (N + 1) => Fin m → Bool)
  have hsum : ∑ a : Fin (N + 1) → Fin m → Bool, (if runSeqTasep y a = x then (1 : ℝ) else 0) =
      ∑ c : Fin m → Bool, ∑ a : Fin N → Fin m → Bool,
        if seqTasepStep (runSeqTasep y a) c = x then 1 else 0 := by
    have h := Fintype.sum_equiv e
      (fun p => if seqTasepStep (runSeqTasep y p.2) p.1 = x then (1 : ℝ) else 0)
      (fun a => if runSeqTasep y a = x then (1 : ℝ) else 0) (fun p => by
        simp [e, Fin.snocEquiv_apply, runSeqTasep_succ, Fin.snoc_castSucc])
    rw [Fintype.sum_prod_type] at h
    exact h.symm
  let G (c : Fin m → Bool) (a : Fin N → Fin m → Bool) (p : TasepValidPredecessor x) : ℝ :=
    if p.1.2 = c ∧ tasepPredecessor x p.1.1 = runSeqTasep y a then 1 else 0
  have hG : (∑ c : Fin m → Bool, ∑ a : Fin N → Fin m → Bool,
        if seqTasepStep (runSeqTasep y a) c = x then (1 : ℝ) else 0) =
      ∑ p : TasepValidPredecessor x, ∑ a : Fin N → Fin m → Bool,
        if runSeqTasep y a = tasepPredecessor x p.1.1 then 1 else 0 := by
    calc
      _ = ∑ c, ∑ a, ∑ p, G c a p := by
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro a _
        exact tasepStepIndicator_eq_sum_valid _ _ _ (strictAnti_runSeqTasep y hy a)
      _ = ∑ p, ∑ a, ∑ c, G c a p := by
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin N → Fin m → Bool)))
          (t := (Finset.univ : Finset (TasepValidPredecessor x)))]
        rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m → Bool)))
          (t := (Finset.univ : Finset (TasepValidPredecessor x)))]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_eq_single p.1.2]
        · simp [G, eq_comm]
        · intro c _ hc
          simp [G, Ne.symm hc]
        · simp
  simp_rw [finiteSeqLaw_measureReal_apply _ _ _ (measurableSet_singleton _), mem_singleton_iff]
  rw [hsum, hG, Nat.add_mul, one_mul, pow_add, ← Finset.mul_sum]
  ring

/-- BFP's determinant is the atom mass of the actual backward sequential process. -/
theorem finiteSeqLaw_atom_eq_det {m : ℕ} (N : ℕ) (y x : Fin m → ℤ)
    (hy : StrictAnti y) (hx : StrictAnti x) :
    (finiteSeqLaw N y).real {x} = tasepTransitionDet N y x := by
  classical
  induction N generalizing x with
  | zero =>
    rw [tasepTransitionDet_zero y x hy hx,
      finiteSeqLaw_measureReal_apply 0 y _ (measurableSet_singleton _)]
    simp [runSeqTasep, Fintype.sum_unique, eq_comm]
  | succ N ih =>
    rw [finiteSeqLaw_real_succ N y x hy, tasepTransitionDet_free_time]
    congr 1
    have he := Fintype.sum_equiv (tasepFreeMaskEquiv x hx)
      (fun b => tasepTransitionDet N y (tasepPredecessor x b))
      (fun p => (finiteSeqLaw N y).real {tasepPredecessor x p.1.1}) (fun b => by
        change tasepTransitionDet N y (tasepPredecessor x b) =
          (finiteSeqLaw N y).real {tasepPredecessor x (tasepCollapsed x b)}
        rw [tasepTransitionDet_eq_collapsed, ih _ (tasepCollapsed_ordered x hx b)])
    exact he.symm

end AiryFdd
