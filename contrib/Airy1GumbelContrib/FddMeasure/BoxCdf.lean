/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Analysis.BoxIntegral.Partition.Additive
import Mathlib.Analysis.BoxIntegral.Partition.Measure
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

open BoxIntegral Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace AiryFdd

/-- A finite product of half-open intervals. -/
def halfOpenBox {ι : Type*} (a b : ι → ℝ) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (a i) (b i))

/-- The closed lower orthant with upper endpoint `b`. -/
def orthant {ι : Type*} (b : ι → ℝ) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun i => Set.Iic (b i))

/-- The alternating sum of a box CDF at the corners of a half-open box. -/
noncomputable def boxCdfIncrement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (a b : ι → ℝ) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset ι).powerset,
    (-1 : ℝ) ^ (Fintype.card ι - s.card) *
      F (fun i => if i ∈ s then b i else a i)

section Corners

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pair the two corners in each fibre of the chosen coordinate. -/
theorem boxCdfIncrement_eq_sum_update (F : (ι → ℝ) → ℝ) (a b : ι → ℝ) (i : ι) :
    boxCdfIncrement F a b =
      ∑ s ∈ (Finset.univ.erase i).powerset,
        (-1 : ℝ) ^ ((Finset.univ.erase i).card - s.card) *
          (F (update (fun j => if j ∈ s then b j else a j) i (b i)) -
           F (update (fun j => if j ∈ s then b j else a j) i (a i))) := by
  let t : Finset ι := Finset.univ.erase i
  have hit : i ∉ t := Finset.notMem_erase _ _
  have huni : insert i t = Finset.univ := Finset.insert_erase (Finset.mem_univ i)
  have hcard : Fintype.card ι = t.card + 1 := by
    simpa only [huni, Finset.card_univ] using Finset.card_insert_of_notMem hit
  unfold boxCdfIncrement
  nth_rewrite 1 [← huni]
  rw [Finset.sum_powerset_insert hit, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hst := Finset.mem_powerset.mp hs
  have his : i ∉ s := fun hi => hit (hst hi)
  have hsle := Finset.card_le_card hst
  have hu : (fun j => if j ∈ insert i s then b j else a j) =
      update (fun j => if j ∈ s then b j else a j) i (b i) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj, update_of_ne]
  have hl : (fun j => if j ∈ s then b j else a j) =
      update (fun j => if j ∈ s then b j else a j) i (a i) := by
    funext j
    by_cases hj : j = i
    · subst j; simp [his]
    · simp [hj, update_of_ne]
  rw [Finset.card_insert_of_notMem his, hcard,
      show t.card + 1 - s.card = (t.card - s.card) + 1 by omega,
      Nat.add_sub_add_right, pow_succ, hu]
  nth_rewrite 1 [hl]
  ring

/-- Splitting one coordinate at a new endpoint telescopes the corner sum. -/
theorem boxCdfIncrement_split (F : (ι → ℝ) → ℝ) (a b : ι → ℝ) (i : ι) (v : ℝ) :
    boxCdfIncrement F a (update b i v) + boxCdfIncrement F (update a i v) b =
      boxCdfIncrement F a b := by
  rw [boxCdfIncrement_eq_sum_update F a _ i, boxCdfIncrement_eq_sum_update F _ b i,
    boxCdfIncrement_eq_sum_update F a b i, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have huv (w : ℝ) :
      update (fun j => if j ∈ s then update b i v j else a j) i w =
        update (fun j => if j ∈ s then b j else a j) i w := by
    funext j
    by_cases hj : j = i <;> simp [hj, update_of_ne]
  have hlv (w : ℝ) :
      update (fun j => if j ∈ s then b j else update a i v j) i w =
        update (fun j => if j ∈ s then b j else a j) i w := by
    funext j
    by_cases hj : j = i <;> simp [hj, update_of_ne]
  simp only [update_self, huv, hlv]
  ring

theorem boxCdfIncrement_eq_zero_of_endpoint_eq (F : (ι → ℝ) → ℝ) (a b : ι → ℝ)
    (i : ι) (hi : a i = b i) : boxCdfIncrement F a b = 0 := by
  simp [boxCdfIncrement_eq_sum_update F a b i, hi]

theorem continuous_boxCdfIncrement (F : (ι → ℝ) → ℝ) (hF : Continuous F) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => boxCdfIncrement F p.1 p.2) := by
  unfold boxCdfIncrement
  refine continuous_finsetSum _ fun s _ => continuous_const.mul (hF.comp ?_)
  refine continuous_pi fun i => ?_
  by_cases hi : i ∈ s <;> simp only [hi, ite_true, ite_false] <;> fun_prop

omit [DecidableEq ι] in
theorem measurableSet_orthant (x : ι → ℝ) : MeasurableSet (orthant x) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Iic

omit [DecidableEq ι] in
theorem measurableSet_halfOpenBox (a b : ι → ℝ) : MeasurableSet (halfOpenBox a b) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem prod_zero_one (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (∏ i ∈ s, if p i then (1 : ℝ) else 0) = if ∀ i ∈ s, p i then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, ih]
    simp only [Finset.forall_mem_insert]
    by_cases h : p i <;> simp [h]

/-- Inclusion–exclusion for the indicator of an actual half-open box. -/
theorem indicator_halfOpenBox_eq_increment {a b : ι → ℝ} (hab : a ≤ b) (z : ι → ℝ) :
    (halfOpenBox a b).indicator (fun _ => (1 : ℝ)) z =
      boxCdfIncrement (fun x => (orthant x).indicator (fun _ => (1 : ℝ)) z) a b := by
  classical
  let f : ι → ℝ := fun i => if z i ≤ b i then 1 else 0
  let g : ι → ℝ := fun i => if z i ≤ a i then 1 else 0
  have hcoord (i : ι) : f i - g i = if z i ∈ Ioc (a i) (b i) then 1 else 0 := by
    by_cases ha : z i ≤ a i
    · have hb := ha.trans (hab i)
      simp [f, g, ha, hb, not_lt_of_ge ha]
    · by_cases hb : z i ≤ b i <;> simp [f, g, ha, hb, lt_of_not_ge ha]
  have hcorner (s : Finset ι) :
      (orthant (fun i => if i ∈ s then b i else a i)).indicator (fun _ => (1 : ℝ)) z =
        (∏ i ∈ s, f i) * ∏ i ∈ sᶜ, g i := by
    have A : (∀ i, z i ≤ (if i ∈ s then b i else a i)) ↔
        (∀ i ∈ s, z i ≤ b i) ∧ (∀ i ∈ sᶜ, z i ≤ a i) := by
      constructor
      · intro h
        exact ⟨fun i hi => by simpa [hi] using h i,
          fun i hi => by simpa [Finset.mem_compl.mp hi] using h i⟩
      · rintro ⟨hb, ha⟩ i
        by_cases hi : i ∈ s
        · simpa [hi] using hb i hi
        · simpa [hi] using ha i (Finset.mem_compl.mpr hi)
    rw [Set.indicator_apply]
    simp only [orthant, mem_univ_pi, mem_Iic, A, f, g, prod_zero_one, Finset.mem_compl]
    by_cases h₁ : ∀ i ∈ s, z i ≤ b i
    · by_cases h₂ : ∀ i ∉ s, z i ≤ a i
      · rw [ite_eq_left (And.intro h₁ h₂), ite_eq_left h₁, ite_eq_left h₂, one_mul]
      · rw [ite_eq_right (fun h => h₂ h.2), ite_eq_right h₂, mul_zero]
    · rw [ite_eq_right (fun h => h₁ h.1), ite_eq_right h₁, zero_mul]
  calc
    _ = ∏ i, (f i - g i) := by
      rw [Set.indicator_apply]
      simp only [hcoord, halfOpenBox, Set.mem_univ_pi, prod_zero_one,
        Finset.mem_univ, true_implies]
    _ = _ := by
      rw [Finset.prod_sub]
      unfold boxCdfIncrement
      refine Finset.sum_bij (fun s _ => sᶜ) (fun s _ => Finset.mem_powerset.mpr (Finset.subset_univ _))
        (fun s _ t _ h => compl_injective h) ?_ ?_
      · intro s hs
        exact ⟨sᶜ, Finset.mem_powerset.mpr (Finset.subset_univ _), compl_compl _⟩
      · intro s hs
        dsimp only
        rw [hcorner, compl_compl, Finset.card_compl, Nat.sub_sub_self (Finset.card_le_univ _)]
        change ((-1 : ℝ) ^ s.card * (∏ i ∈ sᶜ, f i)) * (∏ i ∈ s, g i) = _
        ring

/-- For a finite measure, the mixed increment is the mass of the half-open box. -/
theorem boxCdfIncrement_of_measure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] {a b : ι → ℝ} (hab : a ≤ b) :
    boxCdfIncrement (fun x => μ.real (orthant x)) a b = μ.real (halfOpenBox a b) := by
  classical
  let q (s : Finset ι) : (ι → ℝ) → ℝ :=
    fun z => (-1 : ℝ) ^ (Fintype.card ι - s.card) *
      (orthant (fun i => if i ∈ s then b i else a i)).indicator (fun _ => (1 : ℝ)) z
  have hq (s : Finset ι) : Integrable (q s) μ :=
    ((integrable_const (1 : ℝ)).indicator (measurableSet_orthant _)).const_mul _
  unfold boxCdfIncrement
  calc
    _ = ∑ s ∈ (Finset.univ : Finset ι).powerset, ∫ z, q s z ∂μ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [show (fun z => q s z) = fun z => (-1 : ℝ) ^ (Fintype.card ι - s.card) *
        (orthant (fun i => if i ∈ s then b i else a i)).indicator (fun _ => (1 : ℝ)) z from rfl,
        integral_const_mul]
      have h : (∫ z, (orthant (fun i => if i ∈ s then b i else a i)).indicator
          (fun _ => (1 : ℝ)) z ∂μ) = μ.real (orthant (fun i => if i ∈ s then b i else a i)) :=
        integral_indicator_one (measurableSet_orthant _)
      rw [h]
    _ = ∫ z, ∑ s ∈ (Finset.univ : Finset ι).powerset, q s z ∂μ :=
      (integral_finsetSum _ fun s _ => hq s).symm
    _ = _ := by
      change (∫ z, boxCdfIncrement (fun x => (orthant x).indicator (fun _ => (1 : ℝ)) z) a b ∂μ) = _
      simp_rw [← indicator_halfOpenBox_eq_increment hab]
      exact integral_indicator_one (measurableSet_halfOpenBox a b)

end Corners

section Content

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The nonempty half-open boxes and the empty set. -/
def boundedBoxes (ι : Type*) : Set (Set (ι → ℝ)) :=
  Set.range (fun B : WithBot (Box ι) => (B : Set (ι → ℝ)))

omit [Fintype ι] [DecidableEq ι] in
theorem halfOpenBox_mem_boundedBoxes (a b : ι → ℝ) : halfOpenBox a b ∈ boundedBoxes ι :=
  ⟨Box.mk' a b, Box.coe_mk' _ _⟩

omit [DecidableEq ι] in
theorem boundedBoxes_isSetSemiring : IsSetSemiring (boundedBoxes ι) := by
  classical
  refine ⟨⟨⊥, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨I, rfl⟩ _ ⟨J, rfl⟩
    exact ⟨I ⊓ J, Box.coe_inf I J⟩
  · rintro _ ⟨I, rfl⟩ _ ⟨J, rfl⟩
    induction I with
    | bot => exact ⟨∅, by simp, by simp, by simp⟩
    | coe I =>
      induction J with
      | bot =>
        refine ⟨{(I : Set (ι → ℝ))}, ?_, by simp, by simp⟩
        intro s hs
        have hs' : s = (I : Set (ι → ℝ)) := Finset.mem_singleton.mp hs
        subst s
        exact ⟨↑I, rfl⟩
      | coe J =>
        let π := ((⊤ : Prepartition J).restrict I).compl
        let toSet := fun B : Box ι => (B : Set (ι → ℝ))
        refine ⟨π.boxes.image toSet, ?_, ?_, ?_⟩
        · intro s hs
          obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hs
          exact ⟨↑B, rfl⟩
        · intro s hs t ht hst
          obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hs
          obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp ht
          exact π.pairwiseDisjoint hB hC (fun h => hst (congrArg toSet h))
        · rw [Finset.coe_image, sUnion_image]
          change (I : Set (ι → ℝ)) \ J = π.iUnion
          rw [Prepartition.iUnion_compl, Prepartition.iUnion_restrict, Prepartition.iUnion_top]
          rw [inter_comm, sdiff_inter_self_eq_sdiff]

omit [DecidableEq ι] in
theorem boundedBoxes_generateFrom :
    MeasurableSpace.generateFrom (boundedBoxes ι) = (inferInstance : MeasurableSpace (ι → ℝ)) := by
  classical
  let C : Set (Set ℝ) := {s | ∃ a b : ℝ, a ≤ b ∧ Ioc a b = s}
  have hgen : MeasurableSpace.generateFrom C = borel ℝ := (borel_eq_generateFrom_Ioc_le ℝ).symm
  have hspan : IsCountablySpanning C := by
    refine ⟨fun n : ℕ => Ioc (-(n : ℝ)) (n : ℝ), fun n => ⟨_, _, neg_nonpos_of_nonneg (Nat.cast_nonneg n) |>.trans (Nat.cast_nonneg n), rfl⟩, ?_⟩
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact mem_iUnion.2 ⟨n, by
      rw [mem_Ioc]
      exact ⟨by linarith [neg_abs_le x], (le_abs_self x).trans hn.le⟩⟩
  have hp := generateFrom_eq_pi (α := fun _ : ι => ℝ)
    (C := fun _ => C) (fun _ => hgen) (fun _ => hspan)
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro _ ⟨B, rfl⟩
    induction B with
    | bot => exact MeasurableSet.empty
    | coe B => exact B.measurableSet_coe
  · rw [← hp]
    apply MeasurableSpace.generateFrom_le
    rintro _ ⟨s, hs, rfl⟩
    have h (i : ι) : ∃ a b : ℝ, a ≤ b ∧ Ioc a b = s i := hs i (mem_univ _)
    choose a b _ hEq using h
    have heq : s = fun i => Ioc (a i) (b i) := funext fun i => (hEq i).symm
    rw [heq]
    exact MeasurableSpace.measurableSet_generateFrom (halfOpenBox_mem_boundedBoxes a b)

/-- The corner sum is additive over rectangular partitions. -/
noncomputable def boxCdfAdditive (F : (ι → ℝ) → ℝ) : BoxAdditiveMap ι ℝ ⊤ :=
  BoxAdditiveMap.ofMapSplitAdd (fun I => boxCdfIncrement F I.lower I.upper) ⊤
    (fun I _ i x hx => by
      rw [Box.splitLower_def (I := I) hx, Box.splitUpper_def (I := I) hx]
      exact boxCdfIncrement_split F I.lower I.upper i x)

noncomputable def asCdfBox (s : Set (ι → ℝ)) : WithBot (Box ι) :=
  invFun (fun B : WithBot (Box ι) => (B : Set (ι → ℝ))) s

omit [Fintype ι] [DecidableEq ι] in
theorem asCdfBox_coe (B : WithBot (Box ι)) :
    asCdfBox (B : Set (ι → ℝ)) = B :=
  leftInverse_invFun (fun _ _ h => Box.withBotCoe_inj.1 h) B

omit [Fintype ι] [DecidableEq ι] in
theorem coe_asCdfBox {s : Set (ι → ℝ)} (hs : s ∈ boundedBoxes ι) :
    (asCdfBox s : Set (ι → ℝ)) = s := by
  obtain ⟨B, rfl⟩ := hs
  rw [asCdfBox_coe]

/-- The nonnegative mixed increments as a finite additive content. -/
noncomputable def boxIncrementContent (F : (ι → ℝ) → ℝ)
    (hrect : ∀ a b : ι → ℝ, a ≤ b → 0 ≤ boxCdfIncrement F a b) :
    AddContent ℝ≥0∞ (boundedBoxes ι) where
  toFun s := (asCdfBox s).elim' 0 (fun B => ENNReal.ofReal (boxCdfAdditive F B))
  empty' := by rw [← Box.coe_bot, asCdfBox_coe]; rfl
  sUnion' J hJ hd hu := by
    classical
    let value : WithBot (Box ι) → ℝ≥0∞ :=
      fun B => B.elim' 0 (fun B => ENNReal.ofReal (boxCdfAdditive F B))
    have hes := coe_asCdfBox hu
    cases hB : asCdfBox (⋃₀ (↑J : Set (Set (ι → ℝ)))) with
    | bot =>
      have he : ⋃₀ (↑J : Set (Set (ι → ℝ))) = ∅ := (hes.symm.trans (congrArg _ hB))
      change 0 = ∑ s ∈ J, value (asCdfBox s)
      refine (Finset.sum_eq_zero fun s hs => ?_).symm
      have hsub := subset_sUnion_of_mem (show s ∈ (↑J : Set _) from hs)
      have hs0 : s = ∅ := subset_empty_iff.mp (he ▸ hsub)
      rw [hs0, ← Box.coe_bot, asCdfBox_coe]
      rfl
    | coe B =>
      have hcover : (B : Set (ι → ℝ)) = ⋃₀ (↑J : Set (Set (ι → ℝ))) := by simpa [hB] using hes
      let K := J.image asCdfBox
      have hK : ∀ Q ∈ K, Q ≤ (↑B : WithBot (Box ι)) := by
        intro Q hQ
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hQ
        rw [← Box.withBotCoe_subset_iff, coe_asCdfBox (hJ hs), Box.coe_coe, hcover]
        exact subset_sUnion_of_mem hs
      have hdK : (↑K : Set (WithBot (Box ι))).Pairwise Disjoint := by
        intro Q hQ R hR hne
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hR
        rw [← Box.disjoint_withBotCoe]
        rw [coe_asCdfBox (hJ hs), coe_asCdfBox (hJ ht)]
        exact hd hs ht (fun heq => hne (congrArg asCdfBox heq))
      let π := Prepartition.ofWithBot K hK hdK
      have hπ : π.IsPartition := by
        apply Prepartition.isPartition_iff_iUnion_eq.2
        dsimp [π]
        rw [Prepartition.iUnion_ofWithBot, hcover, sUnion_eq_biUnion]
        ext z
        constructor
        · simp only [mem_iUnion, exists_prop]
          rintro ⟨Q, hQ, hz⟩
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hQ
          exact ⟨s, hs, (coe_asCdfBox (hJ hs)) ▸ hz⟩
        · simp only [mem_iUnion, exists_prop]
          rintro ⟨s, hs, hz⟩
          exact ⟨asCdfBox s, Finset.mem_image_of_mem _ hs, (coe_asCdfBox (hJ hs)).symm ▸ hz⟩
      change value (↑B : WithBot (Box ι)) = ∑ s ∈ J, value (asCdfBox s)
      rw [← Finset.sum_image (g := asCdfBox)]
      · change ENNReal.ofReal (boxCdfAdditive F B) = ∑ Q ∈ K, value Q
        rw [← Prepartition.sum_ofWithBot K hK hdK]
        rw [← (boxCdfAdditive F).sum_partition_boxes le_top hπ]
        exact ENNReal.ofReal_sum_of_nonneg (fun Q _ => hrect _ _ Q.lower_le_upper)
      · intro s hs t ht hst
        rw [← coe_asCdfBox (hJ hs), ← coe_asCdfBox (hJ ht), hst]

theorem boxIncrementContent_apply (F : (ι → ℝ) → ℝ)
    (hrect : ∀ a b : ι → ℝ, a ≤ b → 0 ≤ boxCdfIncrement F a b)
    {a b : ι → ℝ} (hab : a ≤ b) :
    boxIncrementContent F hrect (halfOpenBox a b) = ENNReal.ofReal (boxCdfIncrement F a b) := by
  classical
  change (asCdfBox (halfOpenBox a b)).elim' 0
    (fun B => ENNReal.ofReal (boxCdfAdditive F B)) = _
  rw [show halfOpenBox a b = (Box.mk' a b : Set (ι → ℝ)) from (Box.coe_mk' _ _).symm,
    asCdfBox_coe, Box.mk']
  split_ifs with h
  · rfl
  · obtain ⟨i, hi⟩ := not_forall.mp h
    have hi' : a i = b i := (hab i).antisymm (le_of_not_gt hi)
    rw [boxCdfIncrement_eq_zero_of_endpoint_eq F a b i hi', ENNReal.ofReal_zero]
    rfl


/-- Enlarge a half-open box to an open neighbourhood at arbitrarily small content cost. -/
theorem boxIncrementContent_openCover (F : (ι → ℝ) → ℝ) (hcont : Continuous F)
    (hrect : ∀ a b : ι → ℝ, a ≤ b → 0 ≤ boxCdfIncrement F a b)
    {s : Set (ι → ℝ)} (hs : s ∈ boundedBoxes ι) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ V W : Set (ι → ℝ), IsOpen V ∧ s ⊆ V ∧ V ⊆ W ∧ W ∈ boundedBoxes ι ∧
      boxIncrementContent F hrect W ≤ boxIncrementContent F hrect s + ε := by
  obtain ⟨B, rfl⟩ := hs
  induction B with
  | bot =>
    exact ⟨∅, ∅, isOpen_empty, subset_rfl, subset_rfl, ⟨⊥, rfl⟩, le_self_add⟩
  | coe B =>
    let upper (δ : ℝ) := fun i => B.upper i + δ
    have hlim : Tendsto (fun δ => ENNReal.ofReal (boxCdfIncrement F B.lower (upper δ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (boxCdfIncrement F B.lower B.upper))) := by
      have hUpper : Continuous upper := continuous_pi fun _ => continuous_const.add continuous_id
      have h : Continuous (fun δ => ENNReal.ofReal (boxCdfIncrement F B.lower (upper δ))) :=
        ENNReal.continuous_ofReal.comp <| (continuous_boxCdfIncrement F hcont).comp
          (continuous_const.prodMk hUpper)
      have h' := (h.continuousAt (x := (0 : ℝ))).continuousWithinAt (s := Ioi 0)
      have hzero : upper 0 = B.upper := funext fun _ => add_zero _
      simpa only [hzero] using h'.tendsto
    have hlt : ENNReal.ofReal (boxCdfIncrement F B.lower B.upper) <
        ENNReal.ofReal (boxCdfIncrement F B.lower B.upper) + ε :=
      ENNReal.lt_add_right ENNReal.ofReal_ne_top hε.ne'
    obtain ⟨δ, hδ, hcost⟩ :
        ∃ δ > 0, ENNReal.ofReal (boxCdfIncrement F B.lower (upper δ)) <
          ENNReal.ofReal (boxCdfIncrement F B.lower B.upper) + ε :=
      ((show ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin).and
        (hlim.eventually (gt_mem_nhds hlt))).exists
    let C : Box ι := ⟨B.lower, upper δ, fun i =>
      (B.lower_lt_upper i).trans_le (le_add_of_nonneg_right hδ.le)⟩
    refine ⟨Box.Ioo C, C, (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo), ?_, C.Ioo_subset_coe, ⟨↑C, rfl⟩, ?_⟩
    · intro z hz
      exact mem_univ_pi.mpr fun i => ⟨(hz i).1, (hz i).2.trans_lt (lt_add_of_pos_right _ hδ)⟩
    · change boxIncrementContent F hrect (C : Set (ι → ℝ)) ≤
        boxIncrementContent F hrect (B : Set (ι → ℝ)) + ε
      rw [show (C : Set (ι → ℝ)) = halfOpenBox B.lower (upper δ) from C.coe_eq_pi,
        show (B : Set (ι → ℝ)) = halfOpenBox B.lower B.upper from B.coe_eq_pi]
      rw [boxIncrementContent_apply F hrect C.lower_le_upper,
        boxIncrementContent_apply F hrect B.lower_le_upper]
      exact hcost.le

theorem sum_image_le_sum_ennreal {α β : Type*} [DecidableEq β]
    (J : Finset α) (W : α → β) (f : β → ℝ≥0∞) :
    (∑ s ∈ J.image W, f s) ≤ ∑ j ∈ J, f (W j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert j J hj ih =>
    rw [Finset.image_insert, Finset.sum_insert hj]
    by_cases h : W j ∈ J.image W
    · rw [Finset.insert_eq_of_mem h]
      exact ih.trans (le_add_left le_rfl)
    · rw [Finset.sum_insert h]
      exact add_le_add le_rfl ih

/-- Continuity upgrades finite rectangular additivity to countable-cover subadditivity. -/
theorem boxIncrementContent_countableCover (F : (ι → ℝ) → ℝ) (hcont : Continuous F)
    (hrect : ∀ a b : ι → ℝ, a ≤ b → 0 ≤ boxCdfIncrement F a b)
    {s : Set (ι → ℝ)} (hs : s ∈ boundedBoxes ι)
    {Q : ℕ → Set (ι → ℝ)} (hQ : ∀ n, Q n ∈ boundedBoxes ι) (hcover : s ⊆ ⋃ n, Q n) :
    boxIncrementContent F hrect s ≤ ∑' n, boxIncrementContent F hrect (Q n) := by
  classical
  let m := boxIncrementContent F hrect
  obtain ⟨B, rfl⟩ := hs
  induction B with
  | bot => simp [Box.coe_bot]
  | coe B =>
    change m B ≤ ∑' n, m (Q n)
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨δ, hδ, hδsum⟩ := ENNReal.exists_pos_sum_of_countable'
      (ENNReal.coe_ne_zero.mpr hε.ne') ℕ
    choose V W hVo hQV hVW hW hcost using
      fun n => boxIncrementContent_openCover F hcont hrect (hQ n) (hδ n)
    have hVs : (B : Set (ι → ℝ)) ⊆ ⋃ n, V n := hcover.trans (iUnion_mono hQV)
    let lower (t : ℝ) := fun i => B.lower i + t * (B.upper i - B.lower i)
    have hLower : Continuous lower := by
      exact continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const)
    have hlim : Tendsto (fun t => ENNReal.ofReal (boxCdfIncrement F (lower t) B.upper))
        (𝓝[>] (0 : ℝ)) (𝓝 (m B)) := by
      rw [Box.coe_eq_pi]
      change Tendsto _ _ (𝓝 (m (halfOpenBox B.lower B.upper)))
      rw [show m (halfOpenBox B.lower B.upper) = _ from
        boxIncrementContent_apply F hrect B.lower_le_upper]
      have h : Continuous (fun t => ENNReal.ofReal (boxCdfIncrement F (lower t) B.upper)) :=
        ENNReal.continuous_ofReal.comp <| (continuous_boxCdfIncrement F hcont).comp
          (hLower.prodMk continuous_const)
      have h' := (h.continuousAt (x := (0 : ℝ))).continuousWithinAt (s := Ioi 0)
      have hzero : lower 0 = B.lower := funext fun _ => by simp [lower]
      simpa only [hzero] using h'.tendsto
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with t ht₀ ht₁
    have ht : 0 < t := ht₀
    have hl (i : ι) : B.lower i < lower t i :=
      lt_add_of_pos_right _ (mul_pos ht (sub_pos.mpr (B.lower_lt_upper i)))
    have hu (i : ι) : lower t i ≤ B.upper i := by
      dsimp [lower]
      have := mul_le_mul_of_nonneg_right ht₁.le (sub_nonneg.mpr (B.lower_le_upper i))
      linarith
    have hsub : Icc (lower t) B.upper ⊆ (B : Set (ι → ℝ)) := by
      intro z hz
      exact fun i => ⟨(hl i).trans_le (hz.1 i), hz.2 i⟩
    obtain ⟨J, hJ⟩ := isCompact_Icc.elim_finite_subcover V hVo (hsub.trans hVs)
    have hfinite : halfOpenBox (lower t) B.upper ⊆ ⋃₀ (↑(J.image W) : Set (Set (ι → ℝ))) := by
      intro z hz
      obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp (hJ (show z ∈ Icc (lower t) B.upper from
        ⟨fun i => ((mem_univ_pi.mp hz) i).1.le, fun i => ((mem_univ_pi.mp hz) i).2⟩))
      exact mem_sUnion_of_mem (hVW j hzj) (Finset.mem_image_of_mem W hj)
    calc
      _ = m (halfOpenBox (lower t) B.upper) := (boxIncrementContent_apply F hrect hu).symm
      _ ≤ ∑ s ∈ J.image W, m s := addContent_le_sum_of_subset_sUnion
        boundedBoxes_isSetSemiring (by
          intro s hs
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
          exact hW j)
        (halfOpenBox_mem_boundedBoxes _ _) hfinite
      _ ≤ ∑ j ∈ J, m (W j) := sum_image_le_sum_ennreal J W m
      _ ≤ ∑ j ∈ J, (m (Q j) + δ j) := Finset.sum_le_sum fun j _ => hcost j
      _ ≤ ∑' j, (m (Q j) + δ j) := ENNReal.sum_le_tsum J
      _ ≤ _ := by rw [ENNReal.tsum_add]; exact add_le_add le_rfl hδsum.le


/-- Sending every lower endpoint to minus infinity leaves only the upper corner. -/
theorem tendsto_boxCdfIncrement_lower (F : (ι → ℝ) → ℝ)
    (hnonneg : ∀ x, 0 ≤ F x) (hmono : Monotone F)
    (hlo : ∀ (i : ι) (x : ι → ℝ),
      Tendsto (fun r : ℝ => F (Function.update x i r)) atBot (𝓝 0))
    (b : ι → ℝ) :
    Tendsto (fun n : ℕ => boxCdfIncrement F (fun i => min (b i) (-(n : ℝ))) b)
      atTop (𝓝 (F b)) := by
  classical
  have hneg : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  let G (s : Finset ι) := if s = Finset.univ then F b else 0
  have hs : ∑ s ∈ (Finset.univ : Finset ι).powerset, G s = F b := by
    simp [G]
  rw [← hs]
  unfold boxCdfIncrement
  refine tendsto_finsetSum _ fun s _ => ?_
  by_cases h : s = Finset.univ
  · subst s
    simp [G]
  · have hi : ∃ i, i ∉ s := by
      by_contra! hs
      exact h (Finset.eq_univ_of_forall hs)
    obtain ⟨i, hi⟩ := hi
    let corner (n : ℕ) := fun j => if j ∈ s then b j else min (b j) (-(n : ℝ))
    have hmin : Tendsto (fun n : ℕ => min (b i) (-(n : ℝ))) atTop atBot := by
      refine hneg.congr' ?_
      filter_upwards [hneg.eventually_le_atBot (b i)] with n hn
      exact (min_eq_right hn).symm
    have hbound : ∀ n, F (corner n) ≤ F (update b i (min (b i) (-(n : ℝ)))) := by
      intro n
      apply hmono
      intro j
      by_cases hj : j = i
      · subst j; simp [corner, hi]
      · rw [update_of_ne hj]
        by_cases hj' : j ∈ s <;> simp [corner, hj']
    have hcorner : Tendsto (fun n => F (corner n)) atTop (𝓝 0) :=
      squeeze_zero (fun n => hnonneg _) hbound ((hlo i b).comp hmin)
    simpa [G, h, corner] using hcorner.const_mul ((-1 : ℝ) ^ (Fintype.card ι - s.card))

/-- A continuous grounded finite-dimensional box CDF defines a probability measure. -/
theorem exists_measure_of_box_cdf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (hcont : Continuous F)
    (hnonneg : ∀ x, 0 ≤ F x) (hmono : Monotone F)
    (hrect : ∀ a b : ι → ℝ, a ≤ b → 0 ≤ boxCdfIncrement F a b)
    (hlo : ∀ (i : ι) (x : ι → ℝ),
      Tendsto (fun r : ℝ => F (Function.update x i r)) atBot (𝓝 0))
    (hhi : Tendsto (fun r : ℝ => F (fun _ => r)) atTop (𝓝 1)) :
    ∃ μ : Measure (ι → ℝ), IsProbabilityMeasure μ ∧
      ∀ x : ι → ℝ, μ.real (orthant x) = F x := by
  let m := boxIncrementContent F hrect
  have hadd : m.IsSigmaSubadditive :=
    fun _ hQ hUn => boxIncrementContent_countableCover F hcont hrect hUn hQ subset_rfl
  let μ := m.measure boundedBoxes_isSetSemiring boundedBoxes_generateFrom.symm.le hadd
  have hμ {a b : ι → ℝ} (hab : a ≤ b) :
      μ (halfOpenBox a b) = ENNReal.ofReal (boxCdfIncrement F a b) :=
    (m.measure_eq boundedBoxes_isSetSemiring boundedBoxes_generateFrom.symm hadd
      (halfOpenBox_mem_boundedBoxes a b)).trans (boxIncrementContent_apply F hrect hab)
  have horth (b : ι → ℝ) : μ (orthant b) = ENNReal.ofReal (F b) := by
    let A (n : ℕ) := halfOpenBox (fun i => min (b i) (-(n : ℝ))) b
    have hA : Monotone A := by
      intro n m hnm z hz
      apply mem_univ_pi.mpr
      intro i
      have hi := mem_univ_pi.mp hz i
      exact ⟨(min_le_min_left _ (neg_le_neg (Nat.cast_le.mpr hnm))).trans_lt hi.1, hi.2⟩
    have hUn : ⋃ n, A n = orthant b := by
      ext z
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := mem_iUnion.mp hz
        exact mem_univ_pi.mpr fun i => (mem_univ_pi.mp hn i).2
      · intro hz
        obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ i, -z i < (n : ℝ) := by
          have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
          exact ((Filter.eventually_all.2 fun i => ht.eventually_gt_atTop (-z i))).exists
        exact mem_iUnion.mpr ⟨n, mem_univ_pi.mpr fun i =>
          ⟨(min_le_right _ _).trans_lt (by linarith [hn i]), mem_univ_pi.mp hz i⟩⟩
    have hlim := tendsto_measure_iUnion_atTop (μ := μ) hA
    rw [hUn] at hlim
    refine tendsto_nhds_unique hlim ?_
    have ht := ENNReal.tendsto_ofReal (tendsto_boxCdfIncrement_lower F hnonneg hmono hlo b)
    exact ht.congr fun n => (hμ (fun i => min_le_left (b i) (-(n : ℝ)))).symm
  have htotal : μ univ = 1 := by
    let U (n : ℕ) := orthant (fun _ : ι => (n : ℝ))
    have hU : Monotone U := by
      intro n m hnm z hz
      exact mem_univ_pi.mpr fun i =>
        show z i ≤ (m : ℝ) from (show z i ≤ (n : ℝ) from mem_univ_pi.mp hz i).trans
          (Nat.cast_le.mpr hnm)
    have hUn : ⋃ n, U n = univ := by
      apply eq_univ_of_forall
      intro z
      have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ i, z i ≤ (n : ℝ) :=
        (Filter.eventually_all.2 fun i => ht.eventually_ge_atTop (z i)).exists
      exact mem_iUnion.mpr ⟨n, mem_univ_pi.mpr hn⟩
    have hlim := tendsto_measure_iUnion_atTop (μ := μ) hU
    rw [hUn] at hlim
    refine tendsto_nhds_unique hlim ?_
    have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (F (fun _ => (n : ℝ)))) atTop
        (𝓝 (ENNReal.ofReal 1)) :=
      ENNReal.tendsto_ofReal (hhi.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    rw [ENNReal.ofReal_one] at ht
    exact ht.congr fun n => (horth (fun _ => (n : ℝ))).symm
  refine ⟨μ, ⟨htotal⟩, fun b => ?_⟩
  rw [measureReal_def, horth, ENNReal.toReal_ofReal (hnonneg b)]

end Content

end AiryFdd
