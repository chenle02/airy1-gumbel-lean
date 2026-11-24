/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FddMeasure.BoxCdf
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Dirac.Basic

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace AiryFdd

/-- Position of a particle after updating the particles to its right and then the particle itself. -/
def seqTasepAt {m : ℕ} (x : Fin m → ℤ) (coin : Fin m → Bool) :
    (k : ℕ) → k < m → ℤ
  | 0, h => if coin ⟨0, h⟩ then x ⟨0, h⟩ + 1 else x ⟨0, h⟩
  | k + 1, h =>
    if coin ⟨k + 1, h⟩ = true ∧ x ⟨k + 1, h⟩ + 1 < seqTasepAt x coin k (by omega) then
      x ⟨k + 1, h⟩ + 1
    else x ⟨k + 1, h⟩

/-- One backward sequential TASEP update (Borodin–Ferrari–Prähofer 2007, Section 2).
In increasing index order, a successful coin moves its particle one site right when that target
is empty after updating its right neighbour. The rightmost particle has no blocking neighbour. -/
def seqTasepStep {m : ℕ} (x : Fin m → ℤ) (coin : Fin m → Bool) : Fin m → ℤ :=
  fun i => seqTasepAt x coin i.1 i.2

/-- Iterate backward sequential updates in the order of the `N` rows of independent fair coins. -/
def runSeqTasep {m N : ℕ} (y : Fin m → ℤ)
    (coin : Fin N → Fin m → Bool) : Fin m → ℤ :=
  match N with
  | 0 => y
  | n + 1 => seqTasepStep (runSeqTasep y (fun i : Fin n => coin i.castSucc)) (coin (Fin.last n))

/-- The finite trajectory law, a sum of Dirac masses over the coin arrays.
Each array has weight `2⁻¹` to the power `N * m`. -/
noncomputable def finiteSeqLaw {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    Measure (Fin m → ℤ) :=
  ∑ coin : Fin N → Fin m → Bool, ((2 : ℝ≥0∞)⁻¹ ^ (N * m)) • Measure.dirac (runSeqTasep y coin)

/-- A sufficient number of predecessor labels to include at the front of a finite window. -/
def tasepFrontMargin (N : ℕ) : ℕ := N * (N + 1) / 2

/-- Restrict a contiguous particle window starting at label `lo` to the requested labels `J`. -/
def localPosMap {m : ℕ} (lo : ℤ) (J : Finset ℤ) (hlo : ∀ j : J, lo ≤ j.1)
    (hhi : ∀ j : J, j.1 < lo + (m : ℤ)) (y : Fin m → ℤ) : J → ℤ :=
  fun j => y ⟨(j.1 - lo).toNat, by have := hlo j; have := hhi j; omega⟩

/-- Initially there is one particle every two sites, with label one at the origin. -/
def flatInitial (n : ℤ) : ℤ := -2 * (n - 1)

/-- Pick the front of a finite window containing the requested labels and their predecessors. -/
def flatWindowFront (N : ℕ) (J : Finset ℤ) : ℤ :=
  if h : J.Nonempty then J.min' h - (tasepFrontMargin N : ℤ) else 0

/-- The chosen window ends at the largest requested label. -/
def flatWindowSize (N : ℕ) (J : Finset ℤ) : ℕ :=
  if h : J.Nonempty then (J.max' h - flatWindowFront N J + 1).toNat else 0

theorem flatWindowFront_le (N : ℕ) (J : Finset ℤ) (j : J) :
    flatWindowFront N J + (tasepFrontMargin N : ℤ) ≤ j.1 := by
  have h : J.Nonempty := ⟨j.1, j.2⟩
  simpa [flatWindowFront, h] using J.min'_le j.1 j.2

theorem flatWindowSize_gt (N : ℕ) (J : Finset ℤ) (j : J) :
    j.1 < flatWindowFront N J + (flatWindowSize N J : ℤ) := by
  have h : J.Nonempty := ⟨j.1, j.2⟩
  have hp := J.le_max' j.1 j.2
  have hl := flatWindowFront_le N J j
  simp only [flatWindowSize, dite_eq_left h]
  omega

/-- The flat-initial law at the requested labels, obtained from a finite contiguous window
with at least `tasepFrontMargin N` extra labels at the front. The window coupling proves
independence from the particular choice of such a window. -/
noncomputable def flatPosLaw (N : ℕ) (J : Finset ℤ) : Measure (J → ℤ) :=
  (finiteSeqLaw (m := flatWindowSize N J) N
      (fun i => flatInitial (flatWindowFront N J + (i.1 : ℤ)))).map
    (localPosMap (flatWindowFront N J) J
      (fun j => (le_add_of_nonneg_right (by positivity)).trans (flatWindowFront_le N J j))
      (flatWindowSize_gt N J))

theorem seqTasepStep_zero {m : ℕ} (x : Fin m → ℤ) (coin : Fin m → Bool) (h : 0 < m) :
    seqTasepStep x coin ⟨0, h⟩ = if coin ⟨0, h⟩ then x ⟨0, h⟩ + 1 else x ⟨0, h⟩ := rfl

theorem seqTasepStep_succ {m : ℕ} (x : Fin m → ℤ) (coin : Fin m → Bool)
    (k : ℕ) (h : k + 1 < m) :
    seqTasepStep x coin ⟨k + 1, h⟩ =
      if coin ⟨k + 1, h⟩ = true ∧
          x ⟨k + 1, h⟩ + 1 < seqTasepStep x coin ⟨k, by omega⟩
      then x ⟨k + 1, h⟩ + 1 else x ⟨k + 1, h⟩ := rfl

theorem seqTasepStep_bounds {m : ℕ} (x : Fin m → ℤ) (coin : Fin m → Bool) (i : Fin m) :
    x i ≤ seqTasepStep x coin i ∧ seqTasepStep x coin i ≤ x i + 1 := by
  obtain ⟨k, hk⟩ := i
  cases k with
  | zero => rw [seqTasepStep_zero]; split <;> omega
  | succ k => rw [seqTasepStep_succ]; split <;> omega

/-- Backward sequential updates preserve strict particle order. -/
theorem strictAnti_seqTasepStep {m : ℕ} {x : Fin m → ℤ}
    (hx : StrictAnti x) (coin : Fin m → Bool) : StrictAnti (seqTasepStep x coin) := by
  cases m with
  | zero => exact fun {_} j _ => Fin.elim0 j
  | succ m =>
    refine Fin.strictAnti_iff_succ_lt.mpr ?_
    intro i
    have hi := hx (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
    have hprev := (seqTasepStep_bounds x coin i.castSucc).1
    change seqTasepStep x coin i.succ < seqTasepStep x coin i.castSucc
    rw [show i.succ = ⟨i.1 + 1, by omega⟩ from rfl, seqTasepStep_succ]
    split
    · rename_i h
      exact h.2
    · exact hi.trans_le hprev

theorem runSeqTasep_succ {m N : ℕ} (y : Fin m → ℤ) (coin : Fin (N + 1) → Fin m → Bool) :
    runSeqTasep y coin =
      seqTasepStep (runSeqTasep y (fun i : Fin N => coin i.castSucc)) (coin (Fin.last N)) := rfl

theorem runSeqTasep_order_bounds {m N : ℕ} (y : Fin m → ℤ) (hy : StrictAnti y)
    (coin : Fin N → Fin m → Bool) :
    StrictAnti (runSeqTasep y coin) ∧
      ∀ i : Fin m, y i ≤ runSeqTasep y coin i ∧ runSeqTasep y coin i ≤ y i + N := by
  induction N with
  | zero => exact ⟨hy, fun i => by simp [runSeqTasep]⟩
  | succ n ih =>
    rw [runSeqTasep_succ]
    obtain ⟨horder, hbounds⟩ := ih (fun i : Fin n => coin i.castSucc)
    refine ⟨strictAnti_seqTasepStep horder _, fun i => ?_⟩
    have h := hbounds i
    have hs := seqTasepStep_bounds (runSeqTasep y (fun i : Fin n => coin i.castSucc))
      (coin (Fin.last n)) i
    push_cast
    omega

/-- Every particle has nonnegative displacement, at most one per time step. -/
theorem runSeqTasep_displacement {m N : ℕ} (y : Fin m → ℤ) (hy : StrictAnti y)
    (coin : Fin N → Fin m → Bool) (i : Fin m) :
    y i ≤ runSeqTasep y coin i ∧ runSeqTasep y coin i ≤ y i + N :=
  (runSeqTasep_order_bounds y hy coin).2 i

theorem strictAnti_runSeqTasep {m N : ℕ} (y : Fin m → ℤ) (hy : StrictAnti y)
    (coin : Fin N → Fin m → Bool) : StrictAnti (runSeqTasep y coin) :=
  (runSeqTasep_order_bounds y hy coin).1

/-- An order-preserving inclusion of a contiguous window at an offset inside a larger window. -/
def tasepShift {m M : ℕ} (w : ℕ) (hw : w + m ≤ M) : Fin m ↪ Fin M where
  toFun i := ⟨w + i.1, by omega⟩
  inj' i j h := Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem tasepFrontMargin_succ (N : ℕ) :
    tasepFrontMargin (N + 1) = tasepFrontMargin N + (N + 1) := by
  unfold tasepFrontMargin
  rw [show (N + 1) * (N + 1 + 1) = N * (N + 1) + (N + 1) * 2 by ring]
  omega

@[simp]
theorem tasepShift_val {m M : ℕ} (w : ℕ) (hw : w + m ≤ M) (i : Fin m) :
    (tasepShift w hw i).1 = w + i.1 := rfl

/-- If the two current states agree along a sampled block, disagreement after updating its last
particle forces all gaps in that block to be one. -/
theorem seqTasepStep_ne_forces_gap {m M : ℕ} (w : ℕ) (hw : w + m ≤ M)
    (x : Fin m → ℤ) (X : Fin M → ℤ) (coin : Fin M → Bool)
    (hx : StrictAnti x) (a d : ℕ) (hb : a + d < m)
    (h : ∀ k (hk : k < m), a ≤ k → k ≤ a + d →
      x ⟨k, hk⟩ = X (tasepShift w hw ⟨k, hk⟩))
    (hne : seqTasepStep x (coin ∘ tasepShift w hw) ⟨a + d, hb⟩ ≠
      seqTasepStep X coin (tasepShift w hw ⟨a + d, hb⟩)) :
    x ⟨a, by omega⟩ = x ⟨a + d, hb⟩ + d := by
  induction d with
  | zero => simp
  | succ d ih =>
    let first : Fin m := ⟨a, by omega⟩
    let j : Fin m := ⟨a + d, by omega⟩
    let k : Fin m := ⟨a + (d + 1), hb⟩
    let J := tasepShift w hw j
    let K := tasepShift w hw k
    have hj : x j = X J := h _ j.2 (by dsimp [j]; omega) (by dsimp [j]; omega)
    have hk : x k = X K := h _ k.2 (by dsimp [k]; omega) le_rfl
    have hstep :
        seqTasepStep x (coin ∘ tasepShift w hw) k =
          if coin K = true ∧ x k + 1 < seqTasepStep x (coin ∘ tasepShift w hw) j
          then x k + 1 else x k := by
      exact seqTasepStep_succ x _ (a + d) (by omega)
    have hStep :
        seqTasepStep X coin K =
          if coin K = true ∧ x k + 1 < seqTasepStep X coin J
          then x k + 1 else x k := by
      rw [hk]
      have hK : K = ⟨w + (a + d) + 1, by omega⟩ := by
        apply Fin.ext
        change w + (a + (d + 1)) = w + (a + d) + 1
        omega
      have hJ : J = ⟨w + (a + d), by omega⟩ := rfl
      simp only [hK, hJ]
      exact seqTasepStep_succ X coin _ _
    change seqTasepStep x (coin ∘ tasepShift w hw) k ≠ seqTasepStep X coin K at hne
    have hjk : x k < x j := hx (show j < k by change a + d < a + (d + 1); omega)
    have htight : x j = x k + 1 := by
      by_contra hgap
      have h₂ : x k + 1 < x j := by omega
      have h₁ := (seqTasepStep_bounds x (coin ∘ tasepShift w hw) j).1
      have h₀ := (seqTasepStep_bounds X coin J).1
      rw [← hj] at h₀
      exact hne (by rw [hstep, hStep]; simp [(h₂.trans_le h₁), (h₂.trans_le h₀)])
    have hpred : seqTasepStep x (coin ∘ tasepShift w hw) j ≠ seqTasepStep X coin J := by
      intro heq
      exact hne (by rw [hstep, hStep, heq])
    have hchain := ih (hb := j.2)
      (fun i hi ha hd => h i hi ha (by omega)) hpred
    change x first = x j + (d : ℤ) at hchain
    change x first = x k + (↑(d + 1) : ℤ)
    rw [hchain, htight, Nat.cast_succ]
    ring

/-- Starting from equally spaced particles, a larger window gives identical positions beyond the
finite dependence margin when the two evolutions use the same coins at their common labels. -/
theorem runSeqTasep_flat_shift {m M N : ℕ} (lo : ℤ) (w : ℕ) (hw : w + m ≤ M)
    (coin : Fin N → Fin M → Bool) (i : Fin m) (hi : tasepFrontMargin N ≤ i.1) :
    runSeqTasep (fun j : Fin m => flatInitial (lo + (w : ℤ) + (j.1 : ℤ)))
      (fun t => coin t ∘ tasepShift w hw) i =
    runSeqTasep (fun j : Fin M => flatInitial (lo + (j.1 : ℤ))) coin (tasepShift w hw i) := by
  induction N generalizing i with
  | zero => simp [runSeqTasep, Nat.cast_add, add_assoc]
  | succ N ih =>
    rw [runSeqTasep_succ, runSeqTasep_succ]
    have hmargin : tasepFrontMargin N + (N + 1) ≤ i.1 := tasepFrontMargin_succ N ▸ hi
    let a := i.1 - (N + 1)
    have ha : a + (N + 1) = i.1 := by dsimp [a]; omega
    let first : Fin m := ⟨a, by omega⟩
    let y := fun j : Fin m => flatInitial (lo + (w : ℤ) + (j.1 : ℤ))
    let x := runSeqTasep y (fun t : Fin N => coin t.castSucc ∘ tasepShift w hw)
    let X := runSeqTasep (fun j : Fin M => flatInitial (lo + (j.1 : ℤ)))
      (fun t : Fin N => coin t.castSucc)
    have hy : StrictAnti y := by
      intro j k hjk
      change j.1 < k.1 at hjk
      simp only [y, flatInitial]
      omega
    by_contra hne
    have hgap := seqTasepStep_ne_forces_gap w hw x X (coin (Fin.last N))
      (strictAnti_runSeqTasep y hy _) a (N + 1) (ha ▸ i.2)
      (fun k hk hak _ => ih (fun t : Fin N => coin t.castSucc) ⟨k, hk⟩ (by dsimp [a] at *; omega))
      (by simpa only [ha] using hne)
    have hstart := (runSeqTasep_displacement y hy
      (fun t : Fin N => coin t.castSucc ∘ tasepShift w hw) first).1
    have hend := (runSeqTasep_displacement y hy
      (fun t : Fin N => coin t.castSucc ∘ tasepShift w hw) i).2
    change y first ≤ x first at hstart
    change x i ≤ y i + N at hend
    simp only [ha] at hgap
    change x first = x i + (↑(N + 1) : ℤ) at hgap
    have hiInt : (a : ℤ) + ((N + 1 : ℕ) : ℤ) = (i.1 : ℤ) := by exact_mod_cast ha
    have hineq : y first ≤ y i + (N : ℤ) + ((N + 1 : ℕ) : ℤ) := by
      calc
        _ ≤ x first := hstart
        _ = x i + ((N + 1 : ℕ) : ℤ) := hgap
        _ ≤ _ := add_le_add hend le_rfl
    simp only [y, flatInitial, first] at hineq
    push_cast at hiInt hineq
    linarith only [hineq, hiInt]

/-- Fair Bernoulli law on the two Boolean coin values. -/
noncomputable def tasepFairCoin : Measure Bool :=
  ((2 : ℝ≥0∞)⁻¹) • Measure.count

instance : IsProbabilityMeasure tasepFairCoin := by
  constructor
  rw [tasepFairCoin, Measure.smul_apply, smul_eq_mul, Measure.count_univ]
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_bool]
  change (2 : ℝ≥0∞)⁻¹ * 2 = 1
  exact ENNReal.inv_mul_cancel (by norm_num) (by simp)

theorem tasepFairCoin_apply_singleton (b : Bool) : tasepFairCoin {b} = (2 : ℝ≥0∞)⁻¹ := by
  simp [tasepFairCoin, Measure.smul_apply]

/-- Independent coin arrays indexed by time and by the finite window's particle labels. -/
noncomputable def tasepCoinLaw (N m : ℕ) : Measure (Fin N → Fin m → Bool) :=
  Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin m => tasepFairCoin

instance (N m : ℕ) : IsProbabilityMeasure (tasepCoinLaw N m) := by
  unfold tasepCoinLaw
  infer_instance

theorem tasepCoinLaw_apply_singleton (N m : ℕ) (coin : Fin N → Fin m → Bool) :
    tasepCoinLaw N m {coin} = (2 : ℝ≥0∞)⁻¹ ^ (N * m) := by
  unfold tasepCoinLaw
  rw [← Set.univ_pi_singleton, Measure.pi_pi]
  simp only [← Set.univ_pi_singleton, Measure.pi_pi, tasepFairCoin_apply_singleton,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

theorem tasepCoinLaw_eq_sum_dirac (N m : ℕ) :
    tasepCoinLaw N m =
      ∑ c : Fin N → Fin m → Bool, ((2 : ℝ≥0∞)⁻¹ ^ (N * m)) • Measure.dirac c := by
  classical
  apply Measure.ext_of_singleton
  intro c
  rw [tasepCoinLaw_apply_singleton, Measure.finsetSum_apply _ _ _]
  rw [Finset.sum_eq_single c]
  · simp [Measure.smul_apply]
  · intro d _ hd
    simp [Measure.smul_apply, hd]
  · simp

theorem finiteSeqLaw_eq_map_coinLaw {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    finiteSeqLaw N y = (tasepCoinLaw N m).map (runSeqTasep y) := by
  have hf : Measurable (runSeqTasep y : (Fin N → Fin m → Bool) → Fin m → ℤ) :=
    measurable_of_countable _
  rw [tasepCoinLaw_eq_sum_dirac, ← Measure.mapₗ_apply_of_measurable hf, map_sum]
  unfold finiteSeqLaw
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Measure.mapₗ_apply_of_measurable hf, Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf]

/-- The finite trajectory law has unit mass, including empty time and particle windows. -/
theorem finiteSeqLaw_isProbabilityMeasure {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    IsProbabilityMeasure (finiteSeqLaw N y) := by
  rw [finiteSeqLaw_eq_map_coinLaw]
  infer_instance

/-- Restricting an independent row of fair coins along an injection preserves its product law. -/
theorem tasepFairRow_map_embedding {m M : ℕ} (e : Fin m ↪ Fin M) :
    (Measure.pi (fun _ : Fin M => tasepFairCoin)).map
      (fun c : Fin M → Bool => fun i : Fin m => c (e i)) =
        Measure.pi (fun _ : Fin m => tasepFairCoin) := by
  classical
  apply Measure.ext_of_singleton
  intro c
  let R (j : Fin M) : Set Bool :=
    if h : ∃ i, e i = j then {c h.choose} else univ
  have he (i : Fin m) : R (e i) = {c i} := by
    have hx : ∃ k, e k = e i := ⟨i, rfl⟩
    rw [show R (e i) = {c hx.choose} by unfold R; rw [dite_eq_left hx],
      e.injective hx.choose_spec]
  have hpreimage :
      (fun r : Fin M → Bool => fun i : Fin m => r (e i)) ⁻¹' {c} = univ.pi R := by
    ext r
    simp only [mem_preimage, mem_singleton_iff, mem_univ_pi]
    constructor
    · intro hr j
      by_cases h : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := h
        rw [he, mem_singleton_iff]
        exact congrFun hr i
      · simp [R, h]
    · intro hr
      funext i
      have hi := hr (e i)
      rwa [he, mem_singleton_iff] at hi
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), hpreimage,
    Measure.pi_pi, ← Set.univ_pi_singleton, Measure.pi_pi]
  symm
  apply Finset.prod_of_injOn e e.injective.injOn
  · simp
  · intro j _ hj
    have h : ¬∃ i, e i = j := by simpa using hj
    rw [show R j = univ by unfold R; rw [dite_eq_right h], measure_univ]
  · intro i _
    rw [he]

theorem tasepCoinLaw_map_embedding {N m M : ℕ} (e : Fin m ↪ Fin M) :
    (tasepCoinLaw N M).map
      (fun c : Fin N → Fin M → Bool => fun t i => c t (e i)) = tasepCoinLaw N m := by
  let ν (k : ℕ) := Measure.pi (fun _ : Fin k => tasepFairCoin)
  let f : (Fin M → Bool) → (Fin m → Bool) := fun c i => c (e i)
  have hf : (ν M).map f = ν m := tasepFairRow_map_embedding e
  let _ : ∀ _ : Fin N, SigmaFinite ((ν M).map f) := fun _ => by rw [hf]; infer_instance
  change (Measure.pi fun _ : Fin N => ν M).map (fun c t => f (c t)) =
    Measure.pi (fun _ : Fin N => ν m)
  rw [Measure.pi_map_pi (fun _ => (measurable_of_countable f).aemeasurable)]
  simp only [hf]

/-- A window's observed law agrees with the corresponding restriction of any containing
window when all sampled labels are past the smaller window's dependence margin. -/
theorem flatWindow_map_eq_of_shift (N m M : ℕ) (lo : ℤ) (w : ℕ)
    (hw : w + m ≤ M) (l : ℤ) (hoffset : lo + (w : ℤ) = l) (J : Finset ℤ)
    (hlo : ∀ j : J, l + (tasepFrontMargin N : ℤ) ≤ j.1)
    (hhi : ∀ j : J, j.1 < l + (m : ℤ)) :
    (finiteSeqLaw N (fun i : Fin m => flatInitial (l + (i.1 : ℤ)))).map
      (localPosMap l J (fun j => by have := hlo j; omega) hhi) =
    (finiteSeqLaw N (fun i : Fin M => flatInitial (lo + (i.1 : ℤ)))).map
      (localPosMap lo J (fun j => by have := hlo j; omega) (fun j => by have := hhi j; omega)) := by
  subst l
  let y : Fin m → ℤ := fun i => flatInitial (lo + (w : ℤ) + (i.1 : ℤ))
  let Y : Fin M → ℤ := fun i => flatInitial (lo + (i.1 : ℤ))
  let e := tasepShift w hw
  let B : (Fin N → Fin M → Bool) → (Fin N → Fin m → Bool) := fun c t i => c t (e i)
  let p := localPosMap (m := m) (lo + (w : ℤ)) J (fun j => by have := hlo j; omega) hhi
  let P := localPosMap (m := M) lo J (fun j => by have := hlo j; omega)
    (fun j => by have := hhi j; omega)
  change (finiteSeqLaw N y).map p = (finiteSeqLaw N Y).map P
  rw [finiteSeqLaw_eq_map_coinLaw, finiteSeqLaw_eq_map_coinLaw,
    ← tasepCoinLaw_map_embedding (N := N) e]
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext c j
  let i : Fin m := ⟨(j.1 - (lo + (w : ℤ))).toNat, by have := hlo j; have := hhi j; omega⟩
  let k : Fin M := ⟨(j.1 - lo).toNat, by have := hlo j; have := hhi j; omega⟩
  have hk : k = e i := by
    apply Fin.ext
    change (j.1 - lo).toNat = w + (j.1 - (lo + (w : ℤ))).toNat
    have := hlo j
    omega
  have hi : tasepFrontMargin N ≤ i.1 := by
    dsimp [i]
    have := hlo j
    omega
  change runSeqTasep y (B c) i = runSeqTasep Y c k
  rw [hk]
  exact runSeqTasep_flat_shift lo w hw c i hi

/-- Any contiguous window with the required margins gives the same law on the sampled labels. -/
theorem flatPosLaw_eq_map_finiteSeqLaw (N m : ℕ) (J : Finset ℤ) (lo : ℤ)
    (hlo : ∀ j : J, lo + (tasepFrontMargin N : ℤ) ≤ j.1)
    (hhi : ∀ j : J, j.1 < lo + (m : ℤ)) :
    flatPosLaw N J = Measure.map
      (localPosMap lo J (fun j => le_trans (by exact le_add_of_nonneg_right (by positivity))
        (hlo j)) hhi)
      (finiteSeqLaw N (fun i : Fin m => flatInitial (lo + (i.1 : ℤ)))) := by
  let lo₀ := flatWindowFront N J
  let m₀ := flatWindowSize N J
  let L := min lo₀ lo
  let M := (max (lo₀ + (m₀ : ℤ)) (lo + (m : ℤ)) - L).toNat
  have common (l : ℤ) (n : ℕ) (hL : L ≤ l)
      (hM : l + (n : ℤ) ≤ max (lo₀ + (m₀ : ℤ)) (lo + (m : ℤ)))
      (hl₁ : ∀ j : J, l + (tasepFrontMargin N : ℤ) ≤ j.1)
      (hl₂ : ∀ j : J, j.1 < l + (n : ℤ)) :
      (finiteSeqLaw N (fun i : Fin n => flatInitial (l + (i.1 : ℤ)))).map
        (localPosMap l J (fun j => by have := hl₁ j; omega) hl₂) =
      (finiteSeqLaw N (fun i : Fin M => flatInitial (L + (i.1 : ℤ)))).map
        (localPosMap L J (fun j => by have := hl₁ j; omega)
          (fun j => by
            have h := hl₂ j
            dsimp [M]
            omega)) := by
    let w := (l - L).toNat
    have hEq : L + (w : ℤ) = l := by dsimp [w]; omega
    have hw : w + n ≤ M := by dsimp [w, M]; omega
    exact flatWindow_map_eq_of_shift N n M L w hw l hEq J hl₁ hl₂
  unfold flatPosLaw
  exact (common lo₀ m₀ (min_le_left _ _) (le_max_left _ _)
    (flatWindowFront_le N J) (flatWindowSize_gt N J)).trans
    (common lo m (min_le_right _ _) (le_max_right _ _) hlo hhi).symm

noncomputable def bfpKappa : ℝ := (2 : ℝ) ^ (4 / 3 : ℝ) / 3
noncomputable def bfpLabel (N : ℕ) (u : ℝ) : ℤ :=
  ⌊(N : ℝ) / 6 + bfpKappa ^ 2 * u * (N : ℝ) ^ (2 / 3 : ℝ)⌋
noncomputable def bfpCenter (N : ℕ) (u : ℝ) : ℝ :=
  -2 * bfpKappa ^ 2 * u * (N : ℝ) ^ (2 / 3 : ℝ)
noncomputable def bfpScale (N : ℕ) : ℝ := bfpKappa * (N : ℝ) ^ (1 / 3 : ℝ)
noncomputable def bfpCut (N : ℕ) (u x : ℝ) : ℤ :=
  ⌈bfpCenter N u - bfpScale N * x⌉

/-- The scaled observation map uses particle labels at a common lattice observation time. -/
noncomputable def flatTasepObservation (N : ℕ) (I : Finset ℝ) :
    (I.image (bfpLabel N) → ℤ) → (I → ℝ) :=
  fun y u => (bfpCenter N u - (y ⟨bfpLabel N u, Finset.mem_image_of_mem _ u.2⟩ : ℝ)) / bfpScale N

/-- Push the flat lattice law forward by the centred and rescaled particle positions of
Borodin–Ferrari–Prähofer, Theorem 2.5. At time zero this still defines a pushforward,
using total division in the observation map. -/
noncomputable def flatTasepLaw (N : ℕ) (I : Finset ℝ) : Measure (I → ℝ) :=
  (flatPosLaw N (I.image (bfpLabel N))).map (flatTasepObservation N I)

/-- The lower-orthant probability of the rescaled finite vector. -/
noncomputable def flatTasepCdf (N : ℕ) (I : Finset ℝ) (x : I → ℝ) : ℝ :=
  (flatTasepLaw N I).real (orthant x)

/-- The scaled spatial observation is a probability law, even if some labels coincide. -/
theorem flatTasepLaw_isProbabilityMeasure (N : ℕ) (I : Finset ℝ) :
    IsProbabilityMeasure (flatTasepLaw N I) := by
  unfold flatTasepLaw flatPosLaw
  let _ := finiteSeqLaw_isProbabilityMeasure N
    (fun i : Fin (flatWindowSize N (I.image (bfpLabel N))) =>
      flatInitial (flatWindowFront N (I.image (bfpLabel N)) + (i.1 : ℤ)))
  infer_instance

theorem bfpKappa_pos : 0 < bfpKappa := by unfold bfpKappa; positivity

theorem bfpScale_pos {N : ℕ} (hN : 0 < N) : 0 < bfpScale N := by
  unfold bfpScale
  exact mul_pos bfpKappa_pos (Real.rpow_pos_of_pos (by exact_mod_cast hN) _)

/-- Every fixed finite set of distinct observation locations eventually uses distinct labels,
in increasing order. -/
theorem bfpLabel_eventually_strictMono (I : Finset ℝ) :
    ∀ᶠ N : ℕ in atTop, StrictMono (fun u : I => bfpLabel N u) := by
  have hPair (u v : I) :
      ∀ᶠ N : ℕ in atTop, u < v → bfpLabel N u < bfpLabel N v := by
    by_cases huv : u < v
    · have hUV : (u : ℝ) < v := huv
      have hpos : 0 < bfpKappa ^ 2 * ((v : ℝ) - u) :=
        mul_pos (pow_pos bfpKappa_pos _) (sub_pos.mpr hUV)
      have hlim : Tendsto (fun N : ℕ => (bfpKappa ^ 2 * ((v : ℝ) - u)) *
          (N : ℝ) ^ (2 / 3 : ℝ)) atTop atTop :=
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
          tendsto_natCast_atTop_atTop).const_mul_atTop hpos
      filter_upwards [hlim.eventually_ge_atTop 1] with N hN _
      unfold bfpLabel
      apply Int.lt_of_add_one_le
      rw [← Int.floor_add_one]
      apply Int.floor_mono
      nlinarith only [hN]
    · exact Eventually.of_forall fun _ h => (huv h).elim
  filter_upwards [eventually_all.2 fun u : I => eventually_all.2 (hPair u)] with N hN
  exact fun {u v} => hN u v

/-- The minus sign in the BFP scaling sends lower orthants to integer upper cutoffs. -/
theorem flatTasepCdf_eq_raw_cut {N : ℕ} (hN : 0 < N) (I : Finset ℝ) (x : I → ℝ) :
    flatTasepCdf N I x =
      (flatPosLaw N (I.image (bfpLabel N))).real
        {y | ∀ u : I, bfpCut N u (x u) ≤ y ⟨bfpLabel N u, Finset.mem_image_of_mem _ u.2⟩} := by
  rw [flatTasepCdf, flatTasepLaw, map_measureReal_apply
    (measurable_of_countable _) (measurableSet_orthant _)]
  congr 1
  ext y
  simp only [mem_preimage, orthant, mem_univ_pi, mem_Iic, flatTasepObservation, mem_ofPred_eq,
    bfpCut, Int.ceil_le, div_le_iff₀ (bfpScale_pos hN)]
  apply forall_congr'
  intro u
  constructor <;> intro h <;> linarith

/-- Every prelimit rectangle increment is nonnegative because it is the mass of a box. -/
theorem flatTasepCdf_rectangle_nonneg (N : ℕ) (I : Finset ℝ) {a b : I → ℝ}
    (hab : a ≤ b) : 0 ≤ boxCdfIncrement (flatTasepCdf N I) a b := by
  let _ := flatTasepLaw_isProbabilityMeasure N I
  change 0 ≤ boxCdfIncrement (fun x => (flatTasepLaw N I).real (orthant x)) a b
  rw [boxCdfIncrement_of_measure (flatTasepLaw N I) hab]
  exact measureReal_nonneg

end AiryFdd
