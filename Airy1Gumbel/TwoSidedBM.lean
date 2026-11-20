/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import BrownianMotion.Gaussian.BrownianMotion
import Mathlib.Probability.Process.FiniteDimensionalLaws

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Airy1Gumbel

/-!
# Two-sided Brownian motion from two independent one-sided copies

This module constructs two-sided Brownian motion on the real line by gluing
two independent one-sided copies at the origin, and proves the facts needed
downstream for variational (sup-minus-parabola) constructions:

* `twoSidedBM`: the glued process on the sample space
  `TwoSidedΩ := (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)` under the product measure
  `twoSidedBMMeasure := gaussianLimit.prod gaussianLimit` of the
  `BrownianMotion` dependency;
* per-time and joint measurability, almost-sure path continuity on all of ℝ,
  and `B(0) = 0` a.s.;
* the increment law `twoSidedBM t − twoSidedBM s ~ gaussianReal 0 (t − s)` for
  `s ≤ t` and `HasIndepIncrements` on ℝ;
* shift invariance: for every `h : ℝ`, the shifted-increment process
  `y ↦ twoSidedBM (y + h) − twoSidedBM h` has the same law as `twoSidedBM`,
  both at the level of finite-dimensional distributions
  (`map_restrict_twoSidedBM_shift_incr`) and as measures on the path space
  (`map_twoSidedBM_shift_incr`).

The gluing is done in two steps. The process `twoSidedBMAux`,
`t ↦ B₁(t⁺) + B₂(t⁻)`, is pathwise continuous for *every* `ω` and agrees with
the case-split definition `twoSidedBM` on the full-measure event where both
one-sided copies vanish at `0`. All law-level facts are proved for the aux
process first (where increments decompose exactly as a sum of a positive-part
and a negative-part increment) and transferred across the a.s. equality.

Shift invariance follows from the general master lemma
`map_restrict_eq_of_indep_incr`: any two processes on ℝ that are pinned at `0`
a.s., have independent increments, and share the same increment laws have the
same finite-dimensional distributions; applied to `twoSidedBM` and its shifted
increment process.
-/

/-- The sample space for the two-sided construction: two independent one-sided
Brownian path spaces. -/
abbrev TwoSidedΩ : Type := (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)

/-- The two-sided Brownian measure: the product of two copies of
`gaussianLimit`, the canonical Wiener measure of the `BrownianMotion`
dependency. -/
noncomputable def twoSidedBMMeasure : Measure TwoSidedΩ :=
  gaussianLimit.prod gaussianLimit

instance : IsProbabilityMeasure twoSidedBMMeasure := by
  unfold twoSidedBMMeasure
  infer_instance

/-- Two-sided Brownian motion: the first copy on `t ≥ 0`, the second copy run
backwards on `t < 0`. -/
noncomputable def twoSidedBM (t : ℝ) (ω : TwoSidedΩ) : ℝ :=
  if 0 ≤ t then brownian t.toNNReal ω.1 else brownian (-t).toNNReal ω.2

/-- The pathwise-continuous representative of `twoSidedBM`:
`t ↦ B₁(t⁺) + B₂(t⁻)`. It agrees with `twoSidedBM` on the full-measure event
where both copies vanish at `0` (`twoSidedBM_ae_eq_aux`), and every path is
continuous, which makes it the convenient object for exact (non-a.s.)
algebraic manipulations. -/
noncomputable def twoSidedBMAux (t : ℝ) (ω : TwoSidedΩ) : ℝ :=
  brownian t.toNNReal ω.1 + brownian (-t).toNNReal ω.2

/-! ## Measurability and path regularity -/

lemma measurable_twoSidedBM (t : ℝ) : Measurable (twoSidedBM t) := by
  unfold twoSidedBM
  split_ifs with h
  · exact (measurable_brownian _).comp measurable_fst
  · exact (measurable_brownian _).comp measurable_snd

lemma measurable_twoSidedBMAux (t : ℝ) : Measurable (twoSidedBMAux t) :=
  ((measurable_brownian _).comp measurable_fst).add
    ((measurable_brownian _).comp measurable_snd)

lemma measurable_twoSidedBM_uncurry : Measurable twoSidedBM.uncurry := by
  have hs : MeasurableSet {p : ℝ × TwoSidedΩ | 0 ≤ p.1} :=
    measurableSet_Ici.preimage measurable_fst
  have h1 : Measurable fun p : ℝ × TwoSidedΩ ↦ brownian p.1.toNNReal p.2.1 :=
    measurable_brownian_uncurry.comp
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))
  have h2 : Measurable fun p : ℝ × TwoSidedΩ ↦ brownian (-p.1).toNNReal p.2.2 :=
    measurable_brownian_uncurry.comp
      (((continuous_real_toNNReal.measurable.comp measurable_neg).comp
        measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  rw [Function.uncurry_def]
  exact Measurable.piecewise hs h1 h2

/-- Every path of the aux process is continuous, by composition. -/
lemma continuous_twoSidedBMAux (ω : TwoSidedΩ) : Continuous (twoSidedBMAux · ω) :=
  ((continuous_brownian ω.1).comp continuous_real_toNNReal).add
    ((continuous_brownian ω.2).comp (continuous_real_toNNReal.comp continuous_neg))

/-! ## The two copies vanish at zero, a.s. -/

lemma brownian_zero_ae : ∀ᵐ ω ∂gaussianLimit, brownian 0 ω = 0 :=
  (hasLaw_brownian_eval (t := 0)).ae_eq_const_of_gaussianReal

lemma twoSidedBMMeasure_fst_zero : ∀ᵐ ω ∂twoSidedBMMeasure, brownian 0 ω.1 = 0 :=
  ((hasLaw_brownian_eval (t := 0)).comp
    measurePreserving_fst.hasLaw).ae_eq_const_of_gaussianReal

lemma twoSidedBMMeasure_snd_zero : ∀ᵐ ω ∂twoSidedBMMeasure, brownian 0 ω.2 = 0 :=
  ((hasLaw_brownian_eval (t := 0)).comp
    measurePreserving_snd.hasLaw).ae_eq_const_of_gaussianReal

/-- On the full-measure event where both copies vanish at `0`, the case-split
definition and the aux process agree at *every* time. -/
lemma twoSidedBM_ae_eq_aux :
    ∀ᵐ ω ∂twoSidedBMMeasure, ∀ t, twoSidedBM t ω = twoSidedBMAux t ω := by
  filter_upwards [twoSidedBMMeasure_fst_zero, twoSidedBMMeasure_snd_zero]
    with ω h1 h2 t
  by_cases h : 0 ≤ t
  · rw [twoSidedBM, if_pos h, twoSidedBMAux,
      Real.toNNReal_of_nonpos (by linarith : -t ≤ 0), h2, add_zero]
  · rw [twoSidedBM, if_neg h, twoSidedBMAux,
      Real.toNNReal_of_nonpos (by linarith : t ≤ 0), h1, zero_add]

/-- Almost every path of `twoSidedBM` is continuous on all of ℝ. -/
lemma continuous_twoSidedBM :
    ∀ᵐ ω ∂twoSidedBMMeasure, Continuous (twoSidedBM · ω) := by
  filter_upwards [twoSidedBM_ae_eq_aux] with ω hω
  rw [show (twoSidedBM · ω) = (twoSidedBMAux · ω) from funext hω]
  exact continuous_twoSidedBMAux ω

/-- The glued process is pinned at the origin: `B(0) = 0` a.s. -/
lemma twoSidedBM_zero : ∀ᵐ ω ∂twoSidedBMMeasure, twoSidedBM 0 ω = 0 := by
  filter_upwards [twoSidedBM_ae_eq_aux, twoSidedBMMeasure_fst_zero,
    twoSidedBMMeasure_snd_zero] with ω h h1 h2
  rw [h 0, twoSidedBMAux]
  simp [Real.toNNReal_zero, h1, h2]

/-! ## Increment law -/

/-- The two one-sided increment variances add to the full increment variance:
for `s ≤ t`, `|t⁺ − s⁺| + |(−t)⁺ − (−s)⁺| = t − s` as nonnegative reals. -/
lemma nndist_toNNReal_add_toNNReal_neg {s t : ℝ} (hst : s ≤ t) :
    nndist (t.toNNReal : ℝ) (s.toNNReal : ℝ)
      + nndist ((-t).toNNReal : ℝ) ((-s).toNNReal : ℝ)
      = NNReal.mk (t - s) (sub_nonneg.mpr hst) := by
  have key : ∀ x : ℝ, max x 0 - max (-x) 0 = x := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith : -x ≤ 0)]
      linarith
    · rw [max_eq_right hx, max_eq_left (by linarith : 0 ≤ -x)]
      linarith
  rw [NNReal.eq_iff, NNReal.coe_add, NNReal.coe_mk, coe_nndist, coe_nndist,
    Real.dist_eq, Real.dist_eq, Real.coe_toNNReal', Real.coe_toNNReal',
    Real.coe_toNNReal', Real.coe_toNNReal']
  rw [abs_of_nonneg (sub_nonneg.mpr (max_le_max hst le_rfl)),
    abs_of_nonpos (sub_nonpos.mpr (max_le_max (neg_le_neg hst) le_rfl)), neg_sub]
  have h1 := key t
  have h2 := key s
  linarith

/-- Increments of the aux process: for `s ≤ t`,
`twoSidedBMAux t − twoSidedBM s` has law `gaussianReal 0 (t − s)`. The proof
splits the increment into the positive-part increment (first copy) plus the
negative-part increment (second copy), independent under the product measure,
and adds the Gaussian variances. -/
lemma hasLaw_twoSidedBMAux_sub {s t : ℝ} (hst : s ≤ t) :
    HasLaw (fun ω ↦ twoSidedBMAux t ω - twoSidedBMAux s ω)
      (gaussianReal 0 (⟨t - s, by linarith⟩ : ℝ≥0)) twoSidedBMMeasure := by
  have hfun : (fun ω ↦ twoSidedBMAux t ω - twoSidedBMAux s ω)
      = (fun ω ↦ brownian t.toNNReal ω.1 - brownian s.toNNReal ω.1)
        + (fun ω ↦ brownian (-t).toNNReal ω.2 - brownian (-s).toNNReal ω.2) := by
    funext ω
    simp only [twoSidedBMAux, Pi.add_apply]
    ring
  have hA : HasLaw (fun ω ↦ brownian t.toNNReal ω.1 - brownian s.toNNReal ω.1)
      (gaussianReal 0 (nndist (t.toNNReal : ℝ) (s.toNNReal : ℝ))) twoSidedBMMeasure :=
    (hasLaw_brownian_sub (s := t.toNNReal) (t := s.toNNReal)).comp
      (measurePreserving_fst (μ := gaussianLimit) (ν := gaussianLimit)).hasLaw
  have hC : HasLaw (fun ω ↦ brownian (-t).toNNReal ω.2 - brownian (-s).toNNReal ω.2)
      (gaussianReal 0 (nndist ((-t).toNNReal : ℝ) ((-s).toNNReal : ℝ)))
        twoSidedBMMeasure :=
    (hasLaw_brownian_sub (s := (-t).toNNReal) (t := (-s).toNNReal)).comp
      (measurePreserving_snd (μ := gaussianLimit) (ν := gaussianLimit)).hasLaw
  have hAC : IndepFun (fun ω ↦ brownian t.toNNReal ω.1 - brownian s.toNNReal ω.1)
      (fun ω ↦ brownian (-t).toNNReal ω.2 - brownian (-s).toNNReal ω.2)
      twoSidedBMMeasure :=
    indepFun_prod ((measurable_brownian _).sub (measurable_brownian _))
      ((measurable_brownian _).sub (measurable_brownian _))
  rw [hfun]
  refine ⟨hA.aemeasurable.add hC.aemeasurable, ?_⟩
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hAC hA hC
  rw [add_zero, nndist_toNNReal_add_toNNReal_neg hst] at hsum
  exact hsum

/-- Increment law of the two-sided Brownian motion: for `s ≤ t`,
`twoSidedBM t − twoSidedBM s ~ gaussianReal 0 (t − s)`. -/
lemma hasLaw_twoSidedBM_sub {s t : ℝ} (hst : s ≤ t) :
    HasLaw (fun ω ↦ twoSidedBM t ω - twoSidedBM s ω)
      (gaussianReal 0 (⟨t - s, by linarith⟩ : ℝ≥0)) twoSidedBMMeasure := by
  refine (hasLaw_twoSidedBMAux_sub hst).congr ?_
  filter_upwards [twoSidedBM_ae_eq_aux] with ω h
  rw [h t, h s]

/-! ## Independent increments on ℝ -/

/-- Families of measurable random variables independent under `μ` stay
independent when pulled back to a product space along the first projection. -/
lemma iIndepFun_fst_prod {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {X : ∀ i, Ω → β i} (hX : ∀ i, Measurable (X i)) (h : iIndepFun X μ) :
    iIndepFun (fun i ω ↦ X i ω.1) (μ.prod ν) := by
  have hfst : (μ.prod ν).map Prod.fst = μ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  refine (iIndepFun_iff_map_fun_eq_pi_map (f := fun i (ω : Ω × Ω') ↦ X i ω.1)
    (fun i ↦ ((hX i).comp measurable_fst).aemeasurable)).mpr ?_
  have hg : AEMeasurable (fun ω i ↦ X i ω) ((μ.prod ν).map Prod.fst) :=
    hfst ▸ AEMeasurable.of_eval (fun i ↦ (hX i).aemeasurable)
  rw [show (fun ω : Ω × Ω' ↦ fun i ↦ X i ω.1) = (fun ω i ↦ X i ω) ∘ Prod.fst from rfl,
    ← AEMeasurable.map_map_of_aemeasurable hg measurable_fst.aemeasurable, hfst,
    iIndepFun.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable) h]
  refine congrArg Measure.pi ?_
  funext i
  rw [show (fun ω : Ω × Ω' ↦ X i ω.1) = X i ∘ Prod.fst from rfl,
    ← AEMeasurable.map_map_of_aemeasurable (hfst ▸ (hX i).aemeasurable)
      measurable_fst.aemeasurable, hfst]

/-- Families of measurable random variables independent under `ν` stay
independent when pulled back to a product space along the second
projection. -/
lemma iIndepFun_snd_prod {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {X : ∀ i, Ω' → β i} (hX : ∀ i, Measurable (X i)) (h : iIndepFun X ν) :
    iIndepFun (fun i ω ↦ X i ω.2) (μ.prod ν) := by
  have hsnd : (μ.prod ν).map Prod.snd = ν := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  refine (iIndepFun_iff_map_fun_eq_pi_map (f := fun i (ω : Ω × Ω') ↦ X i ω.2)
    (fun i ↦ ((hX i).comp measurable_snd).aemeasurable)).mpr ?_
  have hg : AEMeasurable (fun ω i ↦ X i ω) ((μ.prod ν).map Prod.snd) :=
    hsnd ▸ AEMeasurable.of_eval (fun i ↦ (hX i).aemeasurable)
  rw [show (fun ω : Ω × Ω' ↦ fun i ↦ X i ω.2) = (fun ω i ↦ X i ω) ∘ Prod.snd from rfl,
    ← AEMeasurable.map_map_of_aemeasurable hg measurable_snd.aemeasurable, hsnd,
    iIndepFun.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable) h]
  refine congrArg Measure.pi ?_
  funext i
  rw [show (fun ω : Ω × Ω' ↦ X i ω.2) = X i ∘ Prod.snd from rfl,
    ← AEMeasurable.map_map_of_aemeasurable (hsnd ▸ (hX i).aemeasurable)
      measurable_snd.aemeasurable, hsnd]

/-- Increments of `brownian` along an *antitone* sequence of times are
independent: reverse the index set with `Fin.rev`. -/
lemma iIndepFun_brownian_incr_antitone {n : ℕ} {u : Fin (n + 1) → ℝ≥0}
    (hu : Antitone u) :
    iIndepFun (fun (i : Fin n) ω ↦ brownian (u i.succ) ω - brownian (u i.castSucc) ω)
      gaussianLimit := by
  have hũ : Monotone (fun (i : Fin (n + 1)) ↦ u i.rev) :=
    fun i j hij ↦ hu (Fin.rev_le_rev.mpr hij)
  have hE : iIndepFun (fun (j : Fin n) ω ↦ brownian (u j.succ.rev) ω
      - brownian (u j.castSucc.rev) ω) gaussianLimit :=
    hasIndepIncrements_brownian n (fun (i : Fin (n + 1)) ↦ u i.rev) hũ
  have hpoint : ∀ i : Fin n, ∀ ω,
      brownian (u i.succ) ω - brownian (u i.castSucc) ω
        = -(brownian (u (i.rev).succ.rev) ω - brownian (u (i.rev).castSucc.rev) ω) := by
    intro i ω
    rw [show (i.rev).succ.rev = i.castSucc from by rw [Fin.rev_succ, Fin.rev_rev],
      show (i.rev).castSucc.rev = i.succ from by rw [← Fin.rev_succ, Fin.rev_rev]]
    ring
  have hC : (fun (i : Fin n) ω ↦ brownian (u i.succ) ω - brownian (u i.castSucc) ω)
      = (fun (i : Fin n) ↦ (fun x : ℝ ↦ -x)
          ∘ (((fun (j : Fin n) ω ↦ brownian (u j.succ.rev) ω
            - brownian (u j.castSucc.rev) ω)) ∘ Fin.rev) i) := by
    funext i ω
    simp only [Function.comp_apply]
    exact hpoint i ω
  rw [hC]
  exact (hE.precomp Fin.rev_injective).comp (fun _ ↦ fun x : ℝ ↦ -x) (fun _ ↦ measurable_neg)

/-- If two families of real random variables are each mutually independent and
the two family-vectors are independent, then the family of pairs is mutually
independent. Proved through the rectangle π-systems generating the
σ-algebras of the pairs. -/
lemma iIndepFun_pair_of_indep {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Countable ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A C : ι → Ω → ℝ}
    (hmA : ∀ i, Measurable (A i)) (hmC : ∀ i, Measurable (C i))
    (hA : iIndepFun A μ) (hC : iIndepFun C μ)
    (hAC : IndepFun (fun ω i ↦ A i ω) (fun ω i ↦ C i ω) μ) :
    iIndepFun (fun i ω ↦ (A i ω, C i ω)) μ := by
  classical
  -- the rectangle π-systems
  set π : ι → Set (Set Ω) := fun i ↦
    {S | ∃ s₁ s₂ : Set ℝ, MeasurableSet s₁ ∧ MeasurableSet s₂ ∧
      S = (A i ⁻¹' s₁) ∩ (C i ⁻¹' s₂)} with hπdef
  set m : ι → MeasurableSpace Ω := fun i ↦ MeasurableSpace.comap
    (fun ω ↦ (A i ω, C i ω)) (inferInstance : MeasurableSpace (ℝ × ℝ)) with hmdef
  have hpreimage : ∀ (i : ι) (s₁ s₂ : Set ℝ),
      (fun ω ↦ (A i ω, C i ω)) ⁻¹' (s₁ ×ˢ s₂) = (A i ⁻¹' s₁) ∩ (C i ⁻¹' s₂) := by
    intro i s₁ s₂
    ext ω
    simp [Set.mem_prod, Set.mem_inter_iff]
  have hgen : ∀ i, m i = MeasurableSpace.generateFrom (π i) := by
    intro i
    rw [hmdef]
    show MeasurableSpace.comap (fun ω ↦ (A i ω, C i ω))
        (inferInstance : MeasurableSpace (ℝ × ℝ))
        = MeasurableSpace.generateFrom (π i)
    rw [← generateFrom_prod, MeasurableSpace.comap_generateFrom]
    refine congrArg MeasurableSpace.generateFrom ?_
    ext S
    simp only [Set.mem_image, Set.mem_image2, Set.mem_ofPred_eq, hπdef]
    constructor
    · rintro ⟨T, ⟨s₁, hs₁, s₂, hs₂, rfl⟩, rfl⟩
      exact ⟨s₁, s₂, hs₁, hs₂, hpreimage i s₁ s₂⟩
    · rintro ⟨s₁, s₂, hs₁, hs₂, rfl⟩
      exact ⟨s₁ ×ˢ s₂, ⟨s₁, hs₁, s₂, hs₂, rfl⟩, hpreimage i s₁ s₂⟩
  have hpi : ∀ i, IsPiSystem (π i) := by
    intro i S hS T hT _
    rw [hπdef] at hS hT ⊢
    obtain ⟨s₁, s₂, hs₁, hs₂, rfl⟩ := hS
    obtain ⟨t₁, t₂, ht₁, ht₂, rfl⟩ := hT
    exact ⟨s₁ ∩ t₁, s₂ ∩ t₂, hs₁.inter ht₁, hs₂.inter ht₂, by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨h1, h3⟩, h2, h4⟩
      · rintro ⟨⟨h1, h3⟩, h2, h4⟩
        exact ⟨⟨h1, h2⟩, h3, h4⟩⟩
  -- the intersection of rectangle preimages factorises
  have hindep : iIndepSets π μ := by
    intro s f hf
    have hf' : ∀ i ∈ s, ∃ s₁ s₂ : Set ℝ, MeasurableSet s₁ ∧ MeasurableSet s₂ ∧
        f i = (A i ⁻¹' s₁) ∩ (C i ⁻¹' s₂) := by
      intro i hi
      have hfi := hf i hi
      simp only [hπdef] at hfi
      exact hfi
    -- reindex the witnesses as plain functions of i
    have hf'' : ∀ i, ∃ s₁ s₂ : Set ℝ, i ∈ s →
        (MeasurableSet s₁ ∧ MeasurableSet s₂ ∧ f i = (A i ⁻¹' s₁) ∩ (C i ⁻¹' s₂)) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨a, b, ha, hb, hfab⟩ := hf' i hi
        exact ⟨a, b, fun _ ↦ ⟨ha, hb, hfab⟩⟩
      · exact ⟨univ, univ, fun hi' ↦ (hi hi').elim⟩
    choose s₁ s₂ hfS using hf''
    have hs₁ : ∀ i ∈ s, MeasurableSet (s₁ i) := fun i hi ↦ (hfS i hi).1
    have hs₂ : ∀ i ∈ s, MeasurableSet (s₂ i) := fun i hi ↦ (hfS i hi).2.1
    have hfi : ∀ i ∈ s, f i = (A i ⁻¹' s₁ i) ∩ (C i ⁻¹' s₂ i) :=
      fun i hi ↦ (hfS i hi).2.2
    have hsplit : (⋂ i ∈ s, f i)
        = (⋂ i ∈ s, A i ⁻¹' s₁ i) ∩ (⋂ i ∈ s, C i ⁻¹' s₂ i) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · intro h
        exact ⟨fun i hi ↦ (hfi i hi ▸ h i hi).1, fun i hi ↦ (hfi i hi ▸ h i hi).2⟩
      · rintro ⟨h1, h2⟩ i hi
        rw [hfi i hi]
        exact ⟨h1 i hi, h2 i hi⟩
    -- comap-measurability of big intersections via pi-set witnesses
    have hmem : ∀ (D : ι → Ω → ℝ) (t : ι → Set ℝ), (∀ i ∈ s, MeasurableSet (t i)) →
        MeasurableSet[MeasurableSpace.comap (fun ω j ↦ D j ω) inferInstance]
          (⋂ i ∈ s, D i ⁻¹' t i) := by
      intro D t ht
      refine ⟨univ.pi (fun i ↦ if i ∈ s then t i else univ), ?_, ?_⟩
      · exact MeasurableSet.univ_pi fun i ↦ by
          by_cases hi : i ∈ s
          · rw [if_pos hi]; exact ht i hi
          · rw [if_neg hi]; exact MeasurableSet.univ
      · ext ω
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_iInter,
          forall_const]
        constructor
        · intro h i hi
          have := h i
          rw [if_pos hi] at this
          exact this
        · intro h i
          by_cases hi : i ∈ s
          · rw [if_pos hi]; exact h i hi
          · rw [if_neg hi]; exact Set.mem_univ _
    -- per-index factorisation of single rectangle preimages
    have hfactor : ∀ i ∈ s, μ (f i) = μ (A i ⁻¹' s₁ i) * μ (C i ⁻¹' s₂ i) := by
      intro i hi
      rw [hfi i hi]
      have h1i : MeasurableSet[MeasurableSpace.comap (fun ω j ↦ A j ω) inferInstance]
          (A i ⁻¹' s₁ i) :=
        ⟨(fun f : ι → ℝ ↦ f i) ⁻¹' s₁ i,
          (hs₁ i hi).preimage (measurable_pi_apply i),
          by ext ω; simp [Set.mem_preimage]⟩
      have h2i : MeasurableSet[MeasurableSpace.comap (fun ω j ↦ C j ω) inferInstance]
          (C i ⁻¹' s₂ i) :=
        ⟨(fun f : ι → ℝ ↦ f i) ⁻¹' s₂ i,
          (hs₂ i hi).preimage (measurable_pi_apply i),
          by ext ω; simp [Set.mem_preimage]⟩
      exact hAC.meas_inter h1i h2i
    have hprod := hAC.meas_inter (hmem A s₁ hs₁) (hmem C s₂ hs₂)
    have hprodA : μ (⋂ i ∈ s, A i ⁻¹' s₁ i) = ∏ i ∈ s, μ (A i ⁻¹' s₁ i) :=
      (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hA) s (fun i hi ↦ hs₁ i hi)
    have hprodC : μ (⋂ i ∈ s, C i ⁻¹' s₂ i) = ∏ i ∈ s, μ (C i ⁻¹' s₂ i) :=
      (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hC) s (fun i hi ↦ hs₂ i hi)
    have key : μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i) := by
      rw [hsplit, hprod, hprodA, hprodC, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i hi ↦ (hfactor i hi).symm)
    filter_upwards with a
    simp only [Kernel.const_apply]
    exact key
  have hle : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω) := by
    intro i
    rw [hmdef]
    show MeasurableSpace.comap (fun ω ↦ (A i ω, C i ω)) _ ≤ _
    exact measurable_iff_comap_le.mp ((hmA i).prodMk (hmC i))
  have hI : iIndep m μ := iIndepSets.iIndep hle π hpi hgen hindep
  exact (iIndepFun_iff_iIndep (fun _ ↦ inferInstance) (fun i ω ↦ (A i ω, C i ω)) μ).mpr hI

/-- The aux process has independent increments over ordered times: each
increment splits into a positive-part increment (first copy) plus a
negative-part increment (second copy), and the four ingredients — independence
within each copy and independence of the copies — combine via
`iIndepFun_pair_of_indep`. -/
lemma hasIndepIncrements_twoSidedBMAux :
    HasIndepIncrements twoSidedBMAux twoSidedBMMeasure := by
  intro n t ht
  -- one-sided measurability (for the projection transfers)
  have hmA : ∀ i : Fin n, Measurable
      (fun (ω : ℝ≥0 → ℝ) ↦
        brownian (t i.succ).toNNReal ω - brownian (t i.castSucc).toNNReal ω) :=
    fun i ↦ (measurable_brownian _).sub (measurable_brownian _)
  have hmC : ∀ i : Fin n, Measurable
      (fun (ω : ℝ≥0 → ℝ) ↦
        brownian (-(t i.succ)).toNNReal ω - brownian (-(t i.castSucc)).toNNReal ω) :=
    fun i ↦ (measurable_brownian _).sub (measurable_brownian _)
  -- product-space measurability (for the pairing)
  have hmAP : ∀ i : Fin n, Measurable (fun (ω : TwoSidedΩ) ↦
      brownian (t i.succ).toNNReal ω.1 - brownian (t i.castSucc).toNNReal ω.1) :=
    fun i ↦ ((measurable_brownian _).comp measurable_fst).sub
      ((measurable_brownian _).comp measurable_fst)
  have hmCP : ∀ i : Fin n, Measurable (fun (ω : TwoSidedΩ) ↦
      brownian (-(t i.succ)).toNNReal ω.2 - brownian (-(t i.castSucc)).toNNReal ω.2) :=
    fun i ↦ ((measurable_brownian _).comp measurable_snd).sub
      ((measurable_brownian _).comp measurable_snd)
  have hA : iIndepFun
      (fun (i : Fin n) (ω : TwoSidedΩ) ↦
        brownian (t i.succ).toNNReal ω.1 - brownian (t i.castSucc).toNNReal ω.1)
      twoSidedBMMeasure :=
    iIndepFun_fst_prod hmA
      (hasIndepIncrements_brownian n (fun (i : Fin (n + 1)) ↦ (t i).toNNReal)
        (fun i j hij ↦ Real.toNNReal_mono (ht hij)))
  have hC : iIndepFun
      (fun (i : Fin n) (ω : TwoSidedΩ) ↦
        brownian (-(t i.succ)).toNNReal ω.2 - brownian (-(t i.castSucc)).toNNReal ω.2)
      twoSidedBMMeasure :=
    iIndepFun_snd_prod hmC
      (iIndepFun_brownian_incr_antitone
        (fun i j hij ↦ Real.toNNReal_mono (neg_le_neg (ht hij))))
  have hAC : IndepFun
      (fun (ω : TwoSidedΩ) (i : Fin n) ↦
        brownian (t i.succ).toNNReal ω.1 - brownian (t i.castSucc).toNNReal ω.1)
      (fun (ω : TwoSidedΩ) (i : Fin n) ↦
        brownian (-(t i.succ)).toNNReal ω.2 - brownian (-(t i.castSucc)).toNNReal ω.2)
      twoSidedBMMeasure :=
    indepFun_prod (Measurable.of_eval hmA) (Measurable.of_eval hmC)
  have hD := iIndepFun_pair_of_indep hmAP hmCP hA hC hAC
  have hsum := hD.comp (fun _ ↦ fun p : ℝ × ℝ ↦ p.1 + p.2) (fun _ ↦ measurable_add)
  apply (iIndepFun_congr ?_).mpr hsum
  intro i
  exact EventuallyEq.of_eq (funext fun (ω : TwoSidedΩ) ↦ by
    simp only [twoSidedBMAux, Function.comp_apply]
    ring)

/-- The glued two-sided Brownian motion has independent increments over
ordered times on ℝ. -/
lemma hasIndepIncrements_twoSidedBM :
    HasIndepIncrements twoSidedBM twoSidedBMMeasure := by
  intro n t ht
  apply (iIndepFun_congr ?_).mpr (hasIndepIncrements_twoSidedBMAux n t ht)
  intro i
  filter_upwards [twoSidedBM_ae_eq_aux] with ω h
  rw [h (t i.succ), h (t i.castSucc)]

/-! ## Finite-dimensional laws from increments -/

/-- Telescoping identity for a real sequence: for `a ≤ b`, `f b − f a` is the
sum of consecutive increments over `Ico a b`. -/
lemma sub_eq_sum_Ico_incr {f : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) :
    f b - f a = ∑ k ∈ Finset.Ico a b, (f (k + 1) - f k) := by
  rw [Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub, Finset.sum_range_sub]
  ring

/-- **Master lemma**: two processes on ℝ that are pinned at `0` a.s., have
independent increments, and share the same increment laws have the same
finite-dimensional distributions. The proof sorts `I ∪ {0}`, expresses the
values as a fixed measurable image of the consecutive-increment vector
(telescoping), and uses that the increment vector's law is the product of the
one-dimensional increment laws. -/
theorem map_restrict_eq_of_indep_incr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : ℝ → Ω → ℝ}
    (hX0 : X 0 =ᵐ[P] 0) (hY0 : Y 0 =ᵐ[P] 0)
    (hXi : HasIndepIncrements X P) (hYi : HasIndepIncrements Y P)
    (hlaw : ∀ s t : ℝ, s ≤ t →
      P.map (fun ω ↦ X t ω - X s ω) = P.map (fun ω ↦ Y t ω - Y s ω))
    (hXm : ∀ t, AEMeasurable (X t) P) (hYm : ∀ t, AEMeasurable (Y t) P)
    (I : Finset ℝ) :
    P.map (fun ω ↦ I.restrict (X · ω)) = P.map (fun ω ↦ I.restrict (Y · ω)) := by
  classical
  -- extend to a finset containing 0 and sort it
  set J : Finset ℝ := I ∪ {0} with hJdef
  have h0mem : 0 ∈ J := Finset.mem_union_right I (Finset.mem_singleton_self 0)
  have hcard : 0 < J.card := Finset.card_pos.mpr ⟨0, h0mem⟩
  set m : ℕ := J.card - 1 with hmdef
  have hJcard : J.card = m + 1 := (Nat.succ_pred_eq_of_pos hcard).symm
  set e : Fin (m + 1) ≃o J := J.orderIsoOfFin hJcard with hedef
  set j : Fin (m + 1) → ℝ := fun i ↦ (e i : ℝ) with hjdef
  have hjmono : StrictMono j := by
    intro i i' h
    have h1 : e i < e i' := (e.lt_iff_lt).mpr h
    exact h1
  set ℓ : Fin (m + 1) := e.symm ⟨0, h0mem⟩ with hℓdef
  have hjℓ : j ℓ = 0 := by
    have h1 : e ℓ = ⟨0, h0mem⟩ := by
      rw [hℓdef]
      exact OrderIso.apply_symm_apply e _
    show (↑(e ℓ) : ℝ) = 0
    rw [h1]
  -- laws of the increment vectors coincide
  have hincreq : P.map (fun (ω : Ω) (k : Fin m) ↦ (X (j k.succ) - X (j k.castSucc)) ω)
      = P.map (fun (ω : Ω) (k : Fin m) ↦ (Y (j k.succ) - Y (j k.castSucc)) ω) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun k ↦ (hXm _).sub (hXm _))
        (hXi m j hjmono.monotone),
      iIndepFun.map_fun_eq_pi_map (fun k ↦ (hYm _).sub (hYm _))
        (hYi m j hjmono.monotone)]
    refine congrArg Measure.pi ?_
    funext k
    exact hlaw (j k.castSucc) (j k.succ) (hjmono.monotone (Fin.castSucc_le_succ k))
  -- the ℕ-lifted sequence of evaluation points, bridging Fin and ℕ indices
  set jN : ℕ → ℝ := fun k ↦ if h : k < m + 1 then j ⟨k, h⟩ else 0 with hjNdef
  have hjval : ∀ i : Fin (m + 1), jN i.val = j i := by
    intro i
    show (if h : i.val < m + 1 then j ⟨i.val, h⟩ else 0) = j i
    rw [dif_pos i.isLt]
  -- extension by zero of a Fin-vector, and the cumsum map
  set Extend : (Fin m → ℝ) → (ℕ → ℝ) := fun d k ↦ if h : k < m then d ⟨k, h⟩ else 0
    with hExtenddef
  set ΨN : (ℕ → ℝ) → (Fin (m + 1) → ℝ) := fun d i₀ ↦
    if i₀ ≤ ℓ then -(∑ k ∈ Finset.Ico i₀.val ℓ.val, d k)
    else ∑ k ∈ Finset.Ico ℓ.val i₀.val, d k with hΨNdef
  set Ψ : (Fin m → ℝ) → (Fin (m + 1) → ℝ) := ΨN ∘ Extend with hΨdef
  have hExtendmeas : Measurable Extend := by
    rw [hExtenddef]
    refine Measurable.of_eval fun k ↦ ?_
    by_cases hk : k < m
    · have hdite : (fun (d : Fin m → ℝ) ↦ if h : k < m then d ⟨k, h⟩ else 0)
          = fun (d : Fin m → ℝ) ↦ d ⟨k, hk⟩ := by
        funext d
        exact dif_pos hk
      rw [hdite]
      exact measurable_pi_apply (⟨k, hk⟩ : Fin m)
    · have hdite : (fun (d : Fin m → ℝ) ↦ if h : k < m then d ⟨k, h⟩ else 0)
          = fun (_ : Fin m → ℝ) ↦ 0 := by
        funext d
        exact dif_neg hk
      rw [hdite]
      exact measurable_const
  have hΨNmeas : Measurable ΨN := by
    rw [hΨNdef]
    refine Measurable.of_eval fun i₀ ↦ ?_
    by_cases hi : i₀ ≤ ℓ
    · have hite : (fun (d : ℕ → ℝ) ↦ if i₀ ≤ ℓ then -(∑ k ∈ Finset.Ico i₀.val ℓ.val, d k)
            else ∑ k ∈ Finset.Ico ℓ.val i₀.val, d k)
          = fun (d : ℕ → ℝ) ↦ -(∑ k ∈ Finset.Ico i₀.val ℓ.val, d k) := by
        funext d
        exact if_pos hi
      rw [hite]
      exact (Finset.measurable_sum _ fun k _ ↦ measurable_pi_apply k).neg
    · have hite : (fun (d : ℕ → ℝ) ↦ if i₀ ≤ ℓ then -(∑ k ∈ Finset.Ico i₀.val ℓ.val, d k)
            else ∑ k ∈ Finset.Ico ℓ.val i₀.val, d k)
          = fun (d : ℕ → ℝ) ↦ ∑ k ∈ Finset.Ico ℓ.val i₀.val, d k := by
        funext d
        exact if_neg hi
      rw [hite]
      exact Finset.measurable_sum _ fun k _ ↦ measurable_pi_apply k
  have hΨmeas : Measurable Ψ := hΨNmeas.comp hExtendmeas
  -- value recovery: each value of a pinned process is the cumsum of the
  -- consecutive increments, a.s.
  have hval_of {Z : ℝ → Ω → ℝ} (hZ0 : Z 0 =ᵐ[P] 0) :
      ∀ᵐ ω ∂P, ∀ i₀ : Fin (m + 1), Z (j i₀) ω = Ψ (fun (k : Fin m) ↦ Z (j k.succ) ω
        - Z (j k.castSucc) ω) i₀ := by
    filter_upwards [hZ0] with ω h0 i₀
    have hZℓ : Z (jN ℓ.val) ω = 0 := by rw [hjval ℓ, hjℓ]; exact h0
    -- the increment vector evaluated inside the Ico ranges, against f := Z ∘ jN
    set f : ℕ → ℝ := fun k ↦ Z (jN k) ω with hfdef
    have hExt : ∀ a b : ℕ, b ≤ m → ∀ k ∈ Finset.Ico a b,
        Extend (fun (k' : Fin m) ↦ Z (j k'.succ) ω - Z (j k'.castSucc) ω) k
        = f (k + 1) - f k := by
      intro a b hb k hk
      rw [Finset.mem_Ico] at hk
      have hkm : k < m := lt_of_lt_of_le hk.2 hb
      have hdite : (if h : k < m then
            (fun (k' : Fin m) ↦ Z (j k'.succ) ω - Z (j k'.castSucc) ω) ⟨k, h⟩ else 0)
          = f (k + 1) - f k := by
        rw [dif_pos hkm]
        show Z (j (⟨k, hkm⟩ : Fin m).succ) ω - Z (j (⟨k, hkm⟩ : Fin m).castSucc) ω = _
        rw [Fin.succ_mk, Fin.castSucc_mk]
        rw [← hjval, ← hjval]
      show Extend (fun (k' : Fin m) ↦ Z (j k'.succ) ω - Z (j k'.castSucc) ω) k = _
      rw [hExtenddef]
      exact hdite
    -- case split on the position of i₀ relative to the anchor ℓ
    show Z (j i₀) ω = Ψ (fun (k : Fin m) ↦ Z (j k.succ) ω - Z (j k.castSucc) ω) i₀
    rw [hΨdef]
    show Z (j i₀) ω = ΨN (Extend (fun (k : Fin m) ↦ Z (j k.succ) ω
      - Z (j k.castSucc) ω)) i₀
    rw [hΨNdef]
    show Z (j i₀) ω = (if i₀ ≤ ℓ
      then -(∑ k ∈ Finset.Ico i₀.val ℓ.val,
        Extend (fun (k : Fin m) ↦ Z (j k.succ) ω - Z (j k.castSucc) ω) k)
      else ∑ k ∈ Finset.Ico ℓ.val i₀.val,
        Extend (fun (k : Fin m) ↦ Z (j k.succ) ω - Z (j k.castSucc) ω) k)
    by_cases hcase : i₀ ≤ ℓ
    · -- below (or at) the anchor: − sum over Ico i₀ ℓ
      rw [if_pos hcase]
      have hle : i₀.val ≤ ℓ.val := Fin.le_def.mp hcase
      have hb : ℓ.val ≤ m := Nat.le_of_lt_succ ℓ.isLt
      rw [Finset.sum_congr rfl (hExt i₀.val ℓ.val hb)]
      rw [← sub_eq_sum_Ico_incr (f := f) hle]
      rw [hfdef]
      show Z (j i₀) ω = -(Z (jN ℓ.val) ω - Z (jN i₀.val) ω)
      rw [hZℓ, hjval i₀]
      ring
    · -- above the anchor: sum over Ico ℓ i₀
      rw [if_neg hcase]
      have hlt : ℓ.val < i₀.val := Fin.lt_def.mp (not_le.mp hcase)
      have hle : ℓ.val ≤ i₀.val := hlt.le
      have hb : i₀.val ≤ m := Nat.le_of_lt_succ i₀.isLt
      rw [Finset.sum_congr rfl (hExt ℓ.val i₀.val hb)]
      rw [← sub_eq_sum_Ico_incr (f := f) hle]
      rw [hfdef]
      show Z (j i₀) ω = Z (jN i₀.val) ω - Z (jN ℓ.val) ω
      rw [hZℓ, hjval i₀]
      ring
  have hvalX := hval_of hX0
  have hvalY := hval_of hY0
  -- laws of the Fin-value vectors
  have hFinlaw : P.map (fun ω i₀ ↦ X (j i₀) ω) = P.map (fun ω i₀ ↦ Y (j i₀) ω) := by
    have hcongX : (fun ω i₀ ↦ X (j i₀) ω) =ᵐ[P]
        Ψ ∘ (fun (ω : Ω) (k : Fin m) ↦ (X (j k.succ) - X (j k.castSucc)) ω) := by
      filter_upwards [hvalX] with ω h
      funext i₀
      exact h i₀
    have hcongY : (fun ω i₀ ↦ Y (j i₀) ω) =ᵐ[P]
        Ψ ∘ (fun (ω : Ω) (k : Fin m) ↦ (Y (j k.succ) - Y (j k.castSucc)) ω) := by
      filter_upwards [hvalY] with ω h
      funext i₀
      exact h i₀
    rw [Measure.map_congr hcongX, Measure.map_congr hcongY]
    rw [← AEMeasurable.map_map_of_aemeasurable hΨmeas.aemeasurable
        (AEMeasurable.of_eval fun k ↦ (hXm _).sub (hXm _)),
      ← AEMeasurable.map_map_of_aemeasurable hΨmeas.aemeasurable
        (AEMeasurable.of_eval fun k ↦ (hYm _).sub (hYm _))]
    rw [hincreq]
  -- convert to the finset-indexed restrictions on J
  have hJlaw : P.map (fun ω ↦ J.restrict (X · ω)) = P.map (fun ω ↦ J.restrict (Y · ω)) := by
    set ΦJ : (Fin (m + 1) → ℝ) → (J → ℝ) := fun v x ↦ v (e.symm x) with hΦJdef
    have hΦJmeas : Measurable ΦJ :=
      Measurable.of_eval fun x ↦ measurable_pi_apply (e.symm x)
    have hconvX : (fun ω ↦ J.restrict (X · ω)) = ΦJ ∘ (fun ω i₀ ↦ X (j i₀) ω) := by
      funext ω x
      show X (x : ℝ) ω = X (j (e.symm x)) ω
      simp only [hjdef]
      rw [OrderIso.apply_symm_apply]
    have hconvY : (fun ω ↦ J.restrict (Y · ω)) = ΦJ ∘ (fun ω i₀ ↦ Y (j i₀) ω) := by
      funext ω x
      show Y (x : ℝ) ω = Y (j (e.symm x)) ω
      simp only [hjdef]
      rw [OrderIso.apply_symm_apply]
    rw [hconvX, hconvY]
    rw [← AEMeasurable.map_map_of_aemeasurable hΦJmeas.aemeasurable
        (AEMeasurable.of_eval fun i₀ ↦ hXm (j i₀)),
      ← AEMeasurable.map_map_of_aemeasurable hΦJmeas.aemeasurable
        (AEMeasurable.of_eval fun i₀ ↦ hYm (j i₀))]
    rw [hFinlaw]
  -- restrict from J to I
  have hIJ : I ⊆ J := Finset.subset_union_left
  have hrestrict_map : ∀ (Z : ℝ → Ω → ℝ), (∀ t, AEMeasurable (Z t) P) →
      P.map (fun ω ↦ I.restrict (Z · ω))
        = (P.map (fun ω ↦ J.restrict (Z · ω))).map
          (fun (v : (i : ↥J) → ℝ) (x : ↥I) ↦ v ⟨x.val, hIJ x.property⟩) := by
    intro Z hZ
    have hρmeas :
        Measurable (fun (v : (i : ↥J) → ℝ) (x : ↥I) ↦ v ⟨x.val, hIJ x.property⟩) :=
      Measurable.of_eval fun x ↦ measurable_pi_apply (⟨x.val, hIJ x.property⟩ : ↥J)
    have hfun : ((fun (v : (i : ↥J) → ℝ) (x : ↥I) ↦ v ⟨x.val, hIJ x.property⟩)
        ∘ fun ω ↦ J.restrict (Z · ω)) = fun ω ↦ I.restrict (Z · ω) := by
      funext ω x
      rfl
    rw [AEMeasurable.map_map_of_aemeasurable hρmeas.aemeasurable
      (AEMeasurable.of_eval (f := fun ω ↦ J.restrict (Z · ω)) (fun x ↦ hZ (x : ℝ))), hfun]
  rw [hrestrict_map X hXm, hrestrict_map Y hYm, hJlaw]

/-! ## Shift invariance -/

/-- **Shift invariance of the finite-dimensional distributions**: for every
`h : ℝ`, the shifted-increment process `y ↦ twoSidedBM (y + h) − twoSidedBM h`
has the same finite-dimensional distributions as `twoSidedBM`. This is the key
input for the stationarity of variational suprema built from `twoSidedBM`. -/
theorem map_restrict_twoSidedBM_shift_incr (h : ℝ) (I : Finset ℝ) :
    twoSidedBMMeasure.map
        (fun ω ↦ I.restrict (fun y ↦ twoSidedBM (y + h) ω - twoSidedBM h ω))
      = twoSidedBMMeasure.map (fun ω ↦ I.restrict (twoSidedBM · ω)) := by
  apply map_restrict_eq_of_indep_incr
    (X := fun y ω ↦ twoSidedBM (y + h) ω - twoSidedBM h ω) (Y := twoSidedBM)
  · -- pinned at 0, pointwise
    exact EventuallyEq.of_eq (funext fun (ω : TwoSidedΩ) ↦ by
      show twoSidedBM (0 + h) ω - twoSidedBM h ω = 0
      rw [zero_add]
      exact sub_self _)
  · exact twoSidedBM_zero
  · -- independent increments of the shifted process
    intro n t ht
    have hshift := hasIndepIncrements_twoSidedBM n (fun i ↦ t i + h) (ht.add_const h)
    apply (iIndepFun_congr ?_).mpr hshift
    intro i
    exact EventuallyEq.of_eq (funext fun (ω : TwoSidedΩ) ↦ by ring)
  · exact hasIndepIncrements_twoSidedBM
  · -- increment laws coincide
    intro s t hst
    have hfun : (fun ω ↦ (twoSidedBM (t + h) ω - twoSidedBM h ω)
        - (twoSidedBM (s + h) ω - twoSidedBM h ω))
        = fun ω ↦ twoSidedBM (t + h) ω - twoSidedBM (s + h) ω := by
      funext ω
      ring
    rw [hfun]
    rw [(hasLaw_twoSidedBM_sub (s := s + h) (t := t + h) (by linarith)).map_eq,
      (hasLaw_twoSidedBM_sub (s := s) (t := t) hst).map_eq]
    congr 1
    apply NNReal.eq_iff.mpr
    show (t + h) - (s + h) = t - s
    ring
  · intro t
    exact ((measurable_twoSidedBM _).sub (measurable_twoSidedBM _)).aemeasurable
  · intro t
    exact (measurable_twoSidedBM _).aemeasurable

/-- **Shift invariance as processes on ℝ**: the law of the shifted-increment
process `y ↦ twoSidedBM (y + h) − twoSidedBM h` equals the law of `twoSidedBM`
as measures on the path space `ℝ → ℝ`. -/
theorem map_twoSidedBM_shift_incr (h : ℝ) :
    twoSidedBMMeasure.map (fun ω y ↦ twoSidedBM (y + h) ω - twoSidedBM h ω)
      = twoSidedBMMeasure.map (fun ω y ↦ twoSidedBM y ω) := by
  have hpathX : AEMeasurable (fun ω y ↦ twoSidedBM (y + h) ω - twoSidedBM h ω)
      twoSidedBMMeasure :=
    (Measurable.of_eval fun y ↦
      (measurable_twoSidedBM _).sub (measurable_twoSidedBM _)).aemeasurable
  have hpathB : AEMeasurable (fun ω y ↦ twoSidedBM y ω) twoSidedBMMeasure :=
    (Measurable.of_eval fun y ↦ measurable_twoSidedBM y).aemeasurable
  rw [map_eq_iff_forall_finset_map_restrict_eq hpathX hpathB]
  exact map_restrict_twoSidedBM_shift_incr h

end Airy1Gumbel
