/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import KolmogorovExtension4.KolmogorovExtension
import Airy1Gumbel.ExternalInputs
import Airy1Gumbel.FddRecord
import Airy1GumbelContrib.Fdd.FddShift

open Filter MeasureTheory Set

namespace Airy1Gumbel

/-!
# The Airy₁ process law on `ℝ → ℝ` (Kolmogorov extension)

Under the external-input record `Airy1FddPositive` (`FddRecord.lean`), the canonical laws
`airy1Fdd h I` on `I → ℝ` form a projective family (`airy1Fdd_map_restrict₂`, by induction on
`I \ J` from the one-point drop `airy1Fdd_map_erase`). The Kolmogorov extension theorem of the
`kolmogorov_extension4` package (`MeasureTheory.projectiveLimit`,
`isProjectiveLimit_projectiveLimit`; fibres `ℝ`, Polish) then gives

* `airy1Law h : Measure (ℝ → ℝ)`, a probability measure whose finite-dimensional marginals are
  `airy1Fdd h` (`isProjectiveLimit_airy1Law`), hence whose coordinate process has the Airy₁
  finite-dimensional distribution functions: `airy1Law h {f | ∀ t ∈ I, f t ≤ y t} =
  airy1FinCdf I y` (`airy1Law_fdd`, `airy1Law_orthant`);
* uniqueness: a probability measure on `ℝ → ℝ` with these box probabilities is `airy1Law h`
  (`eq_airy1Law_of_fdd`; Mathlib `IsProjectiveLimit.unique`);
* stationarity: `airy1Law h` is invariant under every time shift `θ_c f = f (· + c)`
  (`airy1Law_map_timeShift`), with **no extra hypothesis**: the needed shift invariance of the
  Fredholm-determinant fdd functions is the deterministic contrib theorem
  `AiryFdd.airy1FinCdf_shift_of_eq` (module `Fdd/FddShift`), combined with
  fdd-uniqueness.

All statements are conditional only on the law-form record `h : Airy1FddPositive` (existence of
probability laws with box-CDFs `airy1FinCdf`); nothing else is assumed.

## Relation to the external-input records (`ExternalInputs.lean`)

The coordinate process on `(ℝ → ℝ, airy1Law h)` is packaged as
`airy1Process h : StationaryRealProcess (airy1Law h)`, and the record `PairStationary` holds for
it as a **theorem** (`pairStationary_airy1Process`): on the canonical process the two-point
stationarity record is discharged, modulo `Airy1FddPositive` alone. The remaining process
records are not treated in this module; they concern finer properties of this canonical
process:

* `LocalModulusEstimate` and path continuity: `airy1Law` lives on the product σ-algebra of
  `ℝ → ℝ`, where path properties such as continuity are not even measurable events; one needs a
  continuous modification (Kolmogorov–Chentsov from increment moment bounds).
* `QRUnitBlockLaw` / `QRTwoBlockLaw` / `QRTwoIntervalLaw`: these concern block maxima
  `sup_{t ∈ [a,b]} A₁(t)`, an uncountable supremum, which is a well-defined random variable with
  the intended law only on a continuous version — so these records depend on path continuity.
* `ProcessAssociated`, `CubicStrongMixing`, `CubicCovarianceDecay` remain literature records
  (their sources are LPP/TASEP limits).
-/

/-! ## Projectivity -/

/-- **Projectivity for all `J ⊆ I`.** The image of `airy1Fdd h I` under restriction to `J` is
`airy1Fdd h J`. Induction on `#(I \ J)`, peeling one time at a time with `airy1Fdd_map_erase`. -/
theorem airy1Fdd_map_restrict₂ (h : Airy1FddPositive) {I J : Finset ℝ} (hJI : J ⊆ I) :
    (airy1Fdd h I).map (Finset.restrict₂ (π := fun _ : ℝ => ℝ) hJI) = airy1Fdd h J := by
  classical
  suffices H : ∀ n : ℕ, ∀ I : Finset ℝ, ∀ hJI : J ⊆ I, (I \ J).card = n →
      (airy1Fdd h I).map (Finset.restrict₂ (π := fun _ : ℝ => ℝ) hJI) = airy1Fdd h J from
    H _ I hJI rfl
  intro n
  induction n with
  | zero =>
    intro I hJI hn
    have hIJ : I = J :=
      le_antisymm (Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hn)) hJI
    subst hIJ
    have hid : (Finset.restrict₂ (π := fun _ : ℝ => ℝ) hJI : (I → ℝ) → (I → ℝ)) = id := rfl
    rw [hid, Measure.map_id]
  | succ n ih =>
    intro I hJI hn
    obtain ⟨t, ht⟩ : (I \ J).Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨htI, htJ⟩ := Finset.mem_sdiff.1 ht
    have hJE : J ⊆ I.erase t := fun s hs =>
      Finset.mem_erase.2 ⟨fun hst => htJ (hst ▸ hs), hJI hs⟩
    have hcard : (I.erase t \ J).card = n := by
      rw [Finset.erase_sdiff_comm, Finset.card_erase_of_mem ht, hn]; rfl
    have hcomp : (Finset.restrict₂ (π := fun _ : ℝ => ℝ) hJI : (I → ℝ) → (J → ℝ)) =
        Finset.restrict₂ (π := fun _ : ℝ => ℝ) hJE ∘ restrictErase I t := rfl
    rw [hcomp, ← Measure.map_map
      (Finset.measurable_restrict₂ hJE : Measurable (Finset.restrict₂ (π := fun _ : ℝ => ℝ) hJE))
      (measurable_restrictErase I t), airy1Fdd_map_erase h I htI, ih _ hJE hcard]

/-- The Airy₁ laws form a projective measure family (Mathlib form, constant fibre `ℝ`). -/
theorem isProjectiveMeasureFamily_airy1Fdd (h : Airy1FddPositive) :
    IsProjectiveMeasureFamily (α := fun _ : ℝ => ℝ) (airy1Fdd h) :=
  fun _ _ hJI => (airy1Fdd_map_restrict₂ h hJI).symm

/-! ## The process law -/

/-- **The Airy₁ process law** on path space `ℝ → ℝ` (product σ-algebra): the Kolmogorov
projective limit of the Airy₁ finite-dimensional laws. -/
noncomputable def airy1Law (h : Airy1FddPositive) : Measure (ℝ → ℝ) :=
  projectiveLimit (airy1Fdd h) (isProjectiveMeasureFamily_airy1Fdd h)

/-- **Kolmogorov extension.** The finite-dimensional marginals of `airy1Law h` are the Airy₁
laws: `(airy1Law h).map I.restrict = airy1Fdd h I` for every finite `I`. -/
theorem isProjectiveLimit_airy1Law (h : Airy1FddPositive) :
    IsProjectiveLimit (airy1Law h) (airy1Fdd h) :=
  isProjectiveLimit_projectiveLimit _

/-- `airy1Law h` is a probability measure. -/
instance isProbabilityMeasure_airy1Law (h : Airy1FddPositive) :
    IsProbabilityMeasure (airy1Law h) :=
  isProbabilityMeasure_projectiveLimit _

/-- Marginal form of `isProjectiveLimit_airy1Law`. -/
theorem airy1Law_map_restrict (h : Airy1FddPositive) (I : Finset ℝ) :
    (airy1Law h).map I.restrict = airy1Fdd h I :=
  isProjectiveLimit_airy1Law h I

/-- **Kolmogorov uniqueness.** Any measure on `ℝ → ℝ` with marginals `airy1Fdd h` is
`airy1Law h`. -/
theorem eq_airy1Law_of_isProjectiveLimit (h : Airy1FddPositive) {μ : Measure (ℝ → ℝ)}
    (hμ : IsProjectiveLimit μ (airy1Fdd h)) : μ = airy1Law h :=
  hμ.unique (isProjectiveLimit_airy1Law h)

/-- The event `{f | f t ≤ x t ∀ t ∈ I}` is the cylinder over the box of `x`. -/
theorem setOf_forall_le_eq_cylinder (I : Finset ℝ) (x : I → ℝ) :
    {f : ℝ → ℝ | ∀ t : I, f t ≤ x t} = cylinder I (Set.pi Set.univ fun i => Set.Iic (x i)) := by
  ext f
  exact ⟨fun hf i _ => hf i, fun hf i => hf i (mem_univ i)⟩

/-- Same, with levels given by a function on all of `ℝ`. -/
theorem setOf_forall_mem_le_eq_cylinder (I : Finset ℝ) (y : ℝ → ℝ) :
    {f : ℝ → ℝ | ∀ t ∈ I, f t ≤ y t}
      = cylinder I (Set.pi Set.univ fun i : I => Set.Iic (y i)) := by
  rw [← setOf_forall_le_eq_cylinder]
  ext f
  simp

theorem measurableSet_setOf_forall_mem_finset_le (I : Finset ℝ) (y : ℝ → ℝ) :
    MeasurableSet {f : ℝ → ℝ | ∀ t ∈ I, f t ≤ y t} := by
  rw [setOf_forall_mem_le_eq_cylinder]
  exact Finset.measurable_restrict I (measurableSet_orthant _)

/-- **The coordinate process has the Airy₁ fdd** (box form, levels on `I`). -/
theorem airy1Law_orthant (h : Airy1FddPositive) (I : Finset ℝ) (x : I → ℝ) :
    (airy1Law h).real {f | ∀ t : I, f t ≤ x t} = AiryFdd.airy1FinCdf I x := by
  rw [setOf_forall_le_eq_cylinder, measureReal_def,
    (isProjectiveLimit_airy1Law h).measure_cylinder I (measurableSet_orthant x),
    ← measureReal_def, airy1Fdd_orthant]

/-- **The coordinate process has the Airy₁ fdd**: for finite `I` and levels `y`,
`airy1Law h {f : f t ≤ y t ∀ t ∈ I} = airy1FinCdf I y`. -/
theorem airy1Law_fdd (h : Airy1FddPositive) (I : Finset ℝ) (y : ℝ → ℝ) :
    (airy1Law h).real {f | ∀ t ∈ I, f t ≤ y t} = AiryFdd.airy1FinCdf I (fun i => y i) := by
  rw [← airy1Law_orthant h I (fun i => y i)]
  congr 1
  ext f
  simp

/-- Extension of a level vector on `I` to all times (`0` off `I`). -/
noncomputable def extendLevels (I : Finset ℝ) (x : I → ℝ) : ℝ → ℝ :=
  fun s => if hs : s ∈ I then x ⟨s, hs⟩ else 0

@[simp] theorem extendLevels_apply (I : Finset ℝ) (x : I → ℝ) (i : I) :
    extendLevels I x i = x i := by
  simp [extendLevels, i.2]

/-- **Uniqueness by the fdd.** A probability measure on `ℝ → ℝ` whose coordinate process has
the Airy₁ finite-dimensional distribution functions is `airy1Law h`. -/
theorem eq_airy1Law_of_fdd (h : Airy1FddPositive) (μ : Measure (ℝ → ℝ))
    [IsProbabilityMeasure μ]
    (hμ : ∀ (I : Finset ℝ) (y : ℝ → ℝ),
      μ.real {f | ∀ t ∈ I, f t ≤ y t} = AiryFdd.airy1FinCdf I (fun i => y i)) :
    μ = airy1Law h := by
  refine eq_airy1Law_of_isProjectiveLimit h fun I => ?_
  refine airy1Fdd_unique h _ fun x => ?_
  rw [map_measureReal_apply (Finset.measurable_restrict I) (measurableSet_orthant x)]
  have := hμ I (extendLevels I x)
  rw [setOf_forall_mem_le_eq_cylinder] at this
  simp only [extendLevels_apply] at this
  exact this

/-! ## Stationarity -/

/-- The time shift `θ_c f = f (· + c)` on path space. -/
def timeShift (c : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun s => f (s + c)

theorem measurable_timeShift (c : ℝ) : Measurable (timeShift c) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- **Stationarity of the Airy₁ process law** (unconditional beyond `Airy1FddPositive`):
`airy1Law h` is invariant under every time shift. Proof: the shifted law has the box
probabilities of the shifted time sets, which equal the unshifted ones by the deterministic
shift invariance of the Fredholm determinant (contrib `AiryFdd.airy1FinCdf_shift_of_eq`,
module `Fdd/FddShift`); conclude by fdd-uniqueness (`eq_airy1Law_of_fdd`). -/
theorem airy1Law_map_timeShift (h : Airy1FddPositive) (c : ℝ) :
    (airy1Law h).map (timeShift c) = airy1Law h := by
  refine eq_airy1Law_of_fdd h _ fun I y => ?_
  rw [map_measureReal_apply (measurable_timeShift c)
    (measurableSet_setOf_forall_mem_finset_le I y)]
  have hset : timeShift c ⁻¹' {f | ∀ t ∈ I, f t ≤ y t}
      = {f | ∀ t ∈ I.map (addRightEmbedding c), f t ≤ y (t - c)} := by
    ext f
    simp only [mem_preimage, mem_ofPred_eq, timeShift, Finset.mem_map, addRightEmbedding_apply,
      forall_exists_index, and_imp]
    constructor
    · rintro hf _ a ha rfl
      simpa using hf a ha
    · intro hf t ht
      simpa using hf (t + c) t ht rfl
  rw [hset, airy1Law_fdd]
  exact AiryFdd.airy1FinCdf_shift_of_eq I c (fun i => y i) (fun j => y (j - c)) fun t _ => by simp

/-! ## The canonical stationary process -/

/-- **The canonical Airy₁ process**: the coordinate process on `(ℝ → ℝ, airy1Law h)`, as a
`StationaryRealProcess` (one-dimensional stationarity from `airy1Law_map_timeShift`). -/
noncomputable def airy1Process (h : Airy1FddPositive) :
    StationaryRealProcess (airy1Law h) where
  A x f := f x
  A_meas x := measurable_pi_apply x
  stat x s := by
    have hcomp : (fun f : ℝ → ℝ => f (x + s)) = (fun f : ℝ → ℝ => f x) ∘ timeShift s := rfl
    rw [hcomp, ← Measure.map_map (measurable_pi_apply x) (measurable_timeShift s),
      airy1Law_map_timeShift h]

/-- **`PairStationary` is a theorem for the canonical process** (retires the record on
`airy1Process`, modulo `Airy1FddPositive` only). -/
theorem pairStationary_airy1Process (h : Airy1FddPositive) :
    PairStationary (airy1Process h) where
  stat_pair x y s := by
    have hcomp : (fun f : ℝ → ℝ => (f (x + s), f (y + s)))
        = (fun f : ℝ → ℝ => (f x, f y)) ∘ timeShift s := rfl
    change (airy1Law h).map (fun f : ℝ → ℝ => (f (x + s), f (y + s)))
      = (airy1Law h).map (fun f : ℝ → ℝ => (f x, f y))
    rw [hcomp, ← Measure.map_map ((measurable_pi_apply x).prodMk (measurable_pi_apply y))
      (measurable_timeShift s), airy1Law_map_timeShift h]

end Airy1Gumbel
