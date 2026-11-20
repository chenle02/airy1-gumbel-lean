/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.LowerBound
import Airy1Gumbel.MesoscopicRecord
import Mathlib.Analysis.Real.Cardinality

open MeasureTheory Set Filter ProbabilityTheory Topology
open scoped ENNReal NNReal BigOperators

namespace Airy1Gumbel

/-!
# The path-level interface on the continuous Airy₁ version

On `(ℝ → ℝ, airy1Law h)` the coordinate process `airy1Process h` is the wrong carrier for
path-level statements: a supremum over uncountably many times is not determined by the product
σ-algebra. This file re-instances the path-level interface on the continuous version
`airy1Cont h` (`exists_continuous_version`) and records, as a theorem, why the
coordinate process cannot carry the local-modulus record.

**Part A — the regression.**
* `countablyDetermined_of_measurableSet`: every set in the product σ-algebra on `∀ i, β i`
  is determined by countably many coordinates (the countably determined sets form a
  σ-algebra containing the generating cylinders).
* `measure_eq_one_of_update_mem`: a set that can be entered from every path by changing one
  coordinate in an uncountable time set has outer measure `1` under every probability measure.
* `isEmpty_localModulusEstimate_of_coord`: a `StationaryRealProcess` on `ℝ → ℝ` that is the
  coordinate process on some window `[c - s, c + s]`, `0 < s ≤ 1`, admits **no**
  `LocalModulusEstimate`: the oscillation event has outer measure `1` for every `ℓ`, while the
  bound tends to `0`.
* `isEmpty_localModulusEstimate_airy1Process`: hence `LocalModulusEstimate (airy1Process h)` is
  uninhabited (needs only `Airy1FddPositive`).
* `isEmpty_localModulusEstimate_airy1SRP`: the same holds for the continuous re-instance
  `airy1SRP h hT` below. The cause is that
  `Ã = airy1ContR h` is the raw coordinate on `(-∞, 0)`; the witness is stated at the centre
  `c = -2`, but the defect is NOT the record's all-centres quantifier: the record's only
  consumer `cover_of_LocalModulusEstimate` uses the centre `gridPt 0 n 0 = 0` with radius
  `1/n`, whose window `[-1/n, 1/n]` already reaches the raw coordinates, so restricting the
  record to centres `c ≥ 0` would not help. Fixes: a two-sided continuous version, one-sided
  windows for block `0`, or replacing the record (`HighLevelUpcrossingTail`, whose
  route only evaluates `Ã` at times in `[0, ∞)`).

**Part B — the continuous re-instance.** With `Ã = airy1ContR h` (`airy1Cont h` on `[0, ∞)`,
the coordinates on `(-∞, 0)`) and the block maxima
`airy1BlockMax h j f = sSup (Ã · f '' [j, j+1])`:
* `airy1CMax h : Airy1ContinuousMax (airy1Law h)`: `path_cont` holds for **every** path (by
  construction: off the full-measure set `goodLowSet` the version is the constant path `0`),
  `Y_eq` by definition (both need only `Airy1FddPositive`);
* `measurable_airy1BlockMax` (`Y_meas`; only `Airy1FddPositive`): a block supremum of a
  continuous path is decided on the rational times of the block (`lt_sSup_image_Icc_iff_rat`);
* `airy1BlockMax_stat_marginal`, `airy1BlockMax_stat_pair` (`stat_marginal`, `stat_pair`;
  under `GOELeftTail`): a.s. the block-exceedance events coincide with the rational-time path
  events `ratExc`, whose laws are shift invariant by `airy1Law_map_timeShift`;
* `airy1SRP h hT : StationaryRealProcess (airy1Law h)` with `A = Ã`, and
  `pairStationary_airy1SRP` (`PairStationary` on `Ã`), from the modification property;
* `hY : airy1BlockMax h = (airy1CMax h).Y` and `hA : (airy1SRP h hT).A = (airy1CMax h).A`
  hold by `rfl`;
* `gumbel_limit_continuum_real_normalized_airy1`: the `_of_QR₄` headline specialised to
  `airy1Law h`, carrying only the QR-law records (`QRUnitBlockLaw`, `QRTwoBlockLaw`,
  `QRTwoIntervalLaw`), the `mesoscopic` field and `CubicStrongMixing` on `Ã`. The `_of_QR₅`
  specialisation is deliberately not stated: its `LocalModulusEstimate` hypothesis on `Ã` is
  uninhabited (`isEmpty_localModulusEstimate_airy1SRP`), so it would be vacuous. The `_of_QR₆`
  specialisation (`HighLevelUpcrossingTail` in its place) is
  `gumbel_limit_continuum_real_normalized_airy1_of_QR₆` (`UpcrossingRecord.lean`).
-/

/-! ## Part A: countably determined sets and the regression theorem -/

section CountablyDetermined

variable {ι : Type*} {β : ι → Type*}

/-- A set of functions is *countably determined* if membership depends only on the values on
some countable index set. -/
def CountablyDetermined (T : Set (∀ i, β i)) : Prop :=
  ∃ I : Set ι, I.Countable ∧ ∀ f g : ∀ i, β i, (∀ i ∈ I, f i = g i) → (f ∈ T ↔ g ∈ T)

/-- The σ-algebra of countably determined sets. -/
@[instance_reducible]
def countablyDeterminedSpace : MeasurableSpace (∀ i, β i) where
  MeasurableSet' := CountablyDetermined
  measurableSet_empty := ⟨∅, countable_empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl T := by
    rintro ⟨I, hI, h⟩
    exact ⟨I, hI, fun f g hfg => not_congr (h f g hfg)⟩
  measurableSet_iUnion T hT := by
    choose I hI h using hT
    refine ⟨⋃ n, I n, countable_iUnion hI, fun f g hfg => ?_⟩
    simp only [mem_iUnion]
    exact exists_congr fun n => h n f g fun i hi => hfg i (mem_iUnion.2 ⟨n, hi⟩)

/-- **Every product-measurable set is determined by countably many coordinates.** -/
theorem countablyDetermined_of_measurableSet [∀ i, MeasurableSpace (β i)]
    {T : Set (∀ i, β i)} (hT : MeasurableSet T) : CountablyDetermined T := by
  have hle : (MeasurableSpace.pi : MeasurableSpace (∀ i, β i)) ≤ countablyDeterminedSpace := by
    refine iSup_le fun i => ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    intro B _
    refine ⟨{i}, countable_singleton i, fun f g hfg => ?_⟩
    change f i ∈ B ↔ g i ∈ B
    rw [hfg i rfl]
  exact hle T hT

end CountablyDetermined

/-- **Outer measure one.** If from every path `f` and every time `t` in an uncountable set `J`
one enters `E` by changing the single coordinate `f t`, then `P E = 1` for every probability
measure `P` on `ℝ → ℝ` (`P E` is the outer measure; `E` need not be measurable): the measurable
hull of `E` is determined by countably many coordinates, so it contains every path. -/
theorem measure_eq_one_of_update_mem {P : Measure (ℝ → ℝ)} [IsProbabilityMeasure P]
    {E : Set (ℝ → ℝ)} {J : Set ℝ} (hJ : ¬ J.Countable)
    (hE : ∀ f : ℝ → ℝ, ∀ t ∈ J, ∃ y : ℝ, Function.update f t y ∈ E) : P E = 1 := by
  obtain ⟨I, hI, hdet⟩ :=
    countablyDetermined_of_measurableSet (measurableSet_toMeasurable P E)
  have hT : toMeasurable P E = univ := by
    refine eq_univ_of_forall fun f => ?_
    obtain ⟨t, htJ, htI⟩ : ∃ t ∈ J, t ∉ I := by
      by_contra hcon
      push Not at hcon
      exact hJ (hI.mono hcon)
    obtain ⟨y, hy⟩ := hE f t htJ
    refine (hdet f (Function.update f t y) fun i hi => ?_).2 (subset_toMeasurable P E hy)
    exact (Function.update_of_ne (ne_of_mem_of_not_mem hi htI) _ _).symm
  rw [← measure_toMeasurable, hT, measure_univ]

/-- **Regression.** A stationary process on `(ℝ → ℝ, P)` that is the
coordinate process on a window `[c - s, c + s]` with `0 < s ≤ 1` has no
`LocalModulusEstimate`: for every `ℓ` the oscillation event at centre `c` and radius `s` has
outer measure `1` (change one coordinate in `(c - s, c)`), while the record bounds it by
`C₀ e^{-c₀ ℓ} → 0`. -/
theorem isEmpty_localModulusEstimate_of_coord {P : Measure (ℝ → ℝ)} [IsProbabilityMeasure P]
    (X : StationaryRealProcess P) {c s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hX : ∀ t ∈ Icc (c - s) (c + s), ∀ f : ℝ → ℝ, X.A t f = f t) :
    IsEmpty (LocalModulusEstimate X) := by
  refine ⟨fun L => ?_⟩
  have hone : ∀ ℓ : ℝ, P.real {ω | ∃ t₁ t₂ : ℝ, |t₁ - c| ≤ s ∧ |t₂ - c| ≤ s ∧
      L.C₀ * ℓ * Real.sqrt s < |X.A t₁ ω - X.A t₂ ω|} = 1 := by
    intro ℓ
    set K := L.C₀ * ℓ * Real.sqrt s
    rw [measureReal_def, measure_eq_one_of_update_mem (J := Ioo (c - s) c) ?_ ?_,
      ENNReal.toReal_one]
    · rw [Cardinal.Real.Ioo_countable_iff, not_le]
      linarith
    · intro f t ht
      refine ⟨f c + |K| + 1, t, c, ?_, by simp [hs.le], ?_⟩
      · rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      · have htc : c ≠ t := ne_of_gt ht.2
        rw [hX t ⟨by linarith [ht.1], by linarith [ht.2]⟩, hX c ⟨by linarith, by linarith⟩,
          Function.update_self, Function.update_of_ne htc]
        have hsub : f c + |K| + 1 - f c = |K| + 1 := by ring
        rw [hsub, abs_of_pos (by positivity)]
        linarith [le_abs_self K]
  have hlim : Tendsto (fun ℓ : ℝ => L.C₀ * Real.exp (-L.c₀ * ℓ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun ℓ : ℝ => -L.c₀ * ℓ) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos L.c₀_pos)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul L.C₀
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := (L.bound.and (hlim.eventually (gt_mem_nhds one_pos))).exists
  have := hℓ1 c s hs hs1
  rw [hone ℓ] at this
  linarith

/-- **`LocalModulusEstimate` is uninhabited on the coordinate process** (needs
only `Airy1FddPositive`): the record is false for `airy1Process h`, so it can only be carried
by a continuous version. -/
theorem isEmpty_localModulusEstimate_airy1Process (h : Airy1FddPositive) :
    IsEmpty (LocalModulusEstimate (airy1Process h)) :=
  isEmpty_localModulusEstimate_of_coord (airy1Process h) (c := 0) one_pos le_rfl
    fun _ _ _ => rfl

/-! ## Part B: the continuous version as a process on `ℝ` and its block maxima -/

/-- The continuous Airy₁ version extended to `ℝ`: `airy1Cont h` at times `x ≥ 0`, the raw
coordinate at `x < 0` (the continuum interface only uses `[0, ∞)`). -/
noncomputable def airy1ContR (h : Airy1FddPositive) (x : ℝ) : (ℝ → ℝ) → ℝ :=
  if 0 ≤ x then airy1Cont h x.toNNReal else fun f => f x

theorem airy1ContR_of_nonneg (h : Airy1FddPositive) {x : ℝ} (hx : 0 ≤ x) :
    airy1ContR h x = airy1Cont h x.toNNReal := by
  unfold airy1ContR
  simp [hx]

theorem airy1ContR_of_not_nonneg (h : Airy1FddPositive) {x : ℝ} (hx : ¬ 0 ≤ x) :
    airy1ContR h x = fun f => f x := by
  unfold airy1ContR
  simp [hx]

theorem measurable_airy1ContR (h : Airy1FddPositive) (x : ℝ) : Measurable (airy1ContR h x) := by
  by_cases hx : 0 ≤ x
  · rw [airy1ContR_of_nonneg h hx]
    exact measurable_airy1Cont h _
  · rw [airy1ContR_of_not_nonneg h hx]
    exact measurable_pi_apply x

/-- `Ã` is a modification of the coordinates at every real time (under `GOELeftTail`). -/
theorem airy1ContR_ae_eq (h : Airy1FddPositive) (hT : GOELeftTail) (x : ℝ) :
    airy1ContR h x =ᵐ[airy1Law h] fun f => f x := by
  by_cases hx : 0 ≤ x
  · rw [airy1ContR_of_nonneg h hx]
    filter_upwards [airy1Cont_ae_eq h hT x.toNNReal] with f hf
    rw [hf, Real.coe_toNNReal x hx]
  · rw [airy1ContR_of_not_nonneg h hx]

/-- Every path of `Ã` is continuous on `[0, ∞)` (by construction: off the full-measure set
`goodLowSet` the version `airy1Cont h` is the constant path `0`). -/
theorem continuousOn_airy1ContR (h : Airy1FddPositive) (f : ℝ → ℝ) :
    ContinuousOn (fun x => airy1ContR h x f) (Ici 0) := by
  refine ((continuous_airy1Cont h f).comp continuous_real_toNNReal).continuousOn.congr
    fun x hx => ?_
  change airy1ContR h x f = airy1Cont h x.toNNReal f
  rw [airy1ContR_of_nonneg h hx]

/-- **Rational reduction of a block supremum.** For `g` continuous on `[a, a+1]`,
`u < sup g([a, a+1])` iff `u < g(q + a)` for some rational `q ∈ [0, 1]`. -/
theorem lt_sSup_image_Icc_iff_rat {g : ℝ → ℝ} {a : ℝ} (hg : ContinuousOn g (Icc a (a + 1)))
    (u : ℝ) :
    u < sSup (g '' Icc a (a + 1)) ↔ ∃ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) 1 ∧ u < g (q + a) := by
  have hbdd : BddAbove (g '' Icc a (a + 1)) := (isCompact_Icc.image_of_continuousOn hg).bddAbove
  have hne : (g '' Icc a (a + 1)).Nonempty := (nonempty_Icc.2 (by linarith)).image g
  constructor
  · intro hu
    obtain ⟨_, ⟨x, hx, rfl⟩, hux⟩ := (lt_csSup_iff hbdd hne).1 hu
    obtain ⟨U, hUo, hxU, hU⟩ := mem_nhdsWithin.1 ((hg x hx).eventually (lt_mem_nhds hux))
    have hxcl : x ∈ closure (Ioo a (a + 1)) := by
      rwa [closure_Ioo (lt_add_one a).ne]
    obtain ⟨y, hyU, hyIoo⟩ := mem_closure_iff.1 hxcl U hUo hxU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hUo.inter isOpen_Ioo) y ⟨hyU, hyIoo⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y - a - ε < y - a by linarith)
    have hmem : (q : ℝ) + a ∈ U ∩ Ioo a (a + 1) := by
      refine hball ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    refine ⟨q, ⟨?_, ?_⟩, hU ⟨hmem.1, Ioo_subset_Icc_self hmem.2⟩⟩
    · linarith [hmem.2.1]
    · linarith [hmem.2.2]
  · rintro ⟨q, hq, hu⟩
    exact hu.trans_le (le_csSup hbdd ⟨_, ⟨by linarith [hq.1], by linarith [hq.2]⟩, rfl⟩)

/-- The block maximum of `Ã` over `[j, j+1]`. -/
noncomputable def airy1BlockMax (h : Airy1FddPositive) (j : ℕ) (f : ℝ → ℝ) : ℝ :=
  sSup ((fun x => airy1ContR h x f) '' Icc (j : ℝ) (j + 1))

theorem airy1BlockMax_gt_iff (h : Airy1FddPositive) (j : ℕ) (f : ℝ → ℝ) (u : ℝ) :
    u < airy1BlockMax h j f ↔
      ∃ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) 1 ∧ u < airy1ContR h (q + j) f :=
  lt_sSup_image_Icc_iff_rat
    ((continuousOn_airy1ContR h f).mono fun _ hx => (Nat.cast_nonneg j).trans hx.1) u

/-- **`Y_meas` on `Ã`** (only `Airy1FddPositive`): the block maxima are measurable, since each
exceedance event is a countable union over rational times. -/
theorem measurable_airy1BlockMax (h : Airy1FddPositive) (j : ℕ) :
    Measurable (airy1BlockMax h j) := by
  refine measurable_of_Ioi fun u => ?_
  have hset : airy1BlockMax h j ⁻¹' Ioi u =
      ⋃ q : ℚ, ⋃ (_ : (q : ℝ) ∈ Icc (0 : ℝ) 1), {f | u < airy1ContR h (q + j) f} := by
    ext f
    simp only [mem_preimage, mem_Ioi, airy1BlockMax_gt_iff, mem_iUnion, mem_ofPred_eq,
      exists_prop]
  rw [hset]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    measurableSet_lt measurable_const (measurable_airy1ContR h _)

/-- **The continuum interface on `Ã`** (only `Airy1FddPositive`): every path is continuous on
`[0, ∞)` (by construction; the constant path `0` off `goodLowSet`) and `Y j` is the block
supremum by definition. -/
noncomputable def airy1CMax (h : Airy1FddPositive) : Airy1ContinuousMax (airy1Law h) where
  A := airy1ContR h
  path_cont := ae_of_all _ (continuousOn_airy1ContR h)
  Y := airy1BlockMax h
  Y_eq := ae_of_all _ fun _ _ => rfl

/-- The link `hY : Y = C.Y` holds by definition. -/
theorem airy1CMax_Y (h : Airy1FddPositive) : airy1BlockMax h = (airy1CMax h).Y := rfl

/-! ### Stationarity of the block maxima -/

/-- The rational-time exceedance event of the block `[a, a+1]` on path space. -/
def ratExc (u a : ℝ) : Set (ℝ → ℝ) :=
  {f | ∃ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) 1 ∧ u < f (q + a)}

theorem measurableSet_ratExc (u a : ℝ) : MeasurableSet (ratExc u a) := by
  have hset : ratExc u a =
      ⋃ q : ℚ, ⋃ (_ : (q : ℝ) ∈ Icc (0 : ℝ) 1), {f : ℝ → ℝ | u < f (q + a)} := by
    ext f
    simp only [ratExc, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [hset]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    measurableSet_lt measurable_const (measurable_pi_apply _)

theorem timeShift_preimage_ratExc (u a c : ℝ) :
    timeShift c ⁻¹' ratExc u a = ratExc u (a + c) := by
  ext f
  simp only [ratExc, mem_preimage, mem_ofPred_eq, timeShift, add_assoc]

/-- Shift invariance of the rational-time block events under `airy1Law h`. -/
theorem airy1Law_timeShift_preimage (h : Airy1FddPositive) (c : ℝ) {E : Set (ℝ → ℝ)}
    (hE : MeasurableSet E) : airy1Law h (timeShift c ⁻¹' E) = airy1Law h E := by
  rw [← Measure.map_apply (measurable_timeShift c) hE, airy1Law_map_timeShift]

/-- Almost surely `Ã` agrees with the coordinates at all times `q + j`, `q ∈ ℚ`, `j ∈ ℕ`. -/
theorem ae_airy1ContR_rat (h : Airy1FddPositive) (hT : GOELeftTail) :
    ∀ᵐ f ∂airy1Law h, ∀ q : ℚ, ∀ j : ℕ, airy1ContR h (q + j) f = f (q + j) := by
  rw [ae_all_iff]
  intro q
  rw [ae_all_iff]
  intro j
  exact airy1ContR_ae_eq h hT _

/-- A.s. the exceedance event of `Y j` is the rational-time path event `ratExc u j`. -/
theorem airy1BlockMax_event_ae (h : Airy1FddPositive) (hT : GOELeftTail) (u : ℝ) (j : ℕ) :
    {f | airy1BlockMax h j f > u} =ᵐ[airy1Law h] ratExc u j := by
  filter_upwards [ae_airy1ContR_rat h hT] with f hf
  refine propext ?_
  change u < airy1BlockMax h j f ↔ ∃ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) 1 ∧ u < f (q + j)
  rw [airy1BlockMax_gt_iff]
  simp only [hf]

/-- **`stat_marginal` on `Ã`** (under `GOELeftTail`). -/
theorem airy1BlockMax_stat_marginal (h : Airy1FddPositive) (hT : GOELeftTail) (u : ℝ) (i : ℕ) :
    airy1Law h {f | airy1BlockMax h i f > u} = airy1Law h {f | airy1BlockMax h 0 f > u} := by
  rw [measure_congr (airy1BlockMax_event_ae h hT u i),
    measure_congr (airy1BlockMax_event_ae h hT u 0), Nat.cast_zero,
    ← airy1Law_timeShift_preimage h (i : ℝ) (measurableSet_ratExc u 0),
    timeShift_preimage_ratExc, zero_add]

/-- **`stat_pair` on `Ã`** (under `GOELeftTail`). -/
theorem airy1BlockMax_stat_pair (h : Airy1FddPositive) (hT : GOELeftTail) (u : ℝ) (i d : ℕ) :
    airy1Law h {f | airy1BlockMax h i f > u ∧ airy1BlockMax h (i + d) f > u}
      = airy1Law h {f | airy1BlockMax h 0 f > u ∧ airy1BlockMax h d f > u} := by
  rw [ofPred_and, ofPred_and,
    measure_congr ((airy1BlockMax_event_ae h hT u i).inter
      (airy1BlockMax_event_ae h hT u (i + d))),
    measure_congr ((airy1BlockMax_event_ae h hT u 0).inter (airy1BlockMax_event_ae h hT u d)),
    Nat.cast_zero,
    ← airy1Law_timeShift_preimage h (i : ℝ)
      ((measurableSet_ratExc u 0).inter (measurableSet_ratExc u d)),
    preimage_inter, timeShift_preimage_ratExc, timeShift_preimage_ratExc, zero_add,
    Nat.cast_add, add_comm (d : ℝ)]

/-! ### The stationary process on `Ã` -/

/-- **`Ã` as a `StationaryRealProcess`** (under `GOELeftTail`): one-dimensional stationarity
transfers from the coordinates through the modification property. -/
noncomputable def airy1SRP (h : Airy1FddPositive) (hT : GOELeftTail) :
    StationaryRealProcess (airy1Law h) where
  A := airy1ContR h
  A_meas := measurable_airy1ContR h
  stat x s := by
    rw [Measure.map_congr (airy1ContR_ae_eq h hT (x + s)),
      Measure.map_congr (airy1ContR_ae_eq h hT x)]
    exact (airy1Process h).stat x s

/-- The link `hA : X.A = C.A` holds by definition. -/
theorem airy1SRP_A (h : Airy1FddPositive) (hT : GOELeftTail) :
    (airy1SRP h hT).A = (airy1CMax h).A := rfl

/-- **`PairStationary` on `Ã`** (under `GOELeftTail`). -/
theorem pairStationary_airy1SRP (h : Airy1FddPositive) (hT : GOELeftTail) :
    PairStationary (airy1SRP h hT) where
  stat_pair x y s := by
    have hp : ∀ a b : ℝ, (fun f => ((airy1SRP h hT).A a f, (airy1SRP h hT).A b f))
        =ᵐ[airy1Law h] fun f : ℝ → ℝ => (f a, f b) :=
      fun a b => (airy1ContR_ae_eq h hT a).prodMk (airy1ContR_ae_eq h hT b)
    rw [Measure.map_congr (hp (x + s) (y + s)), Measure.map_congr (hp x y)]
    exact (pairStationary_airy1Process h).stat_pair x y s

/-- **Witness on the continuous version.** `LocalModulusEstimate` is uninhabited on `Ã` as well,
because `Ã` is the raw coordinate on `(-∞, 0)`; the witness uses the centre `c = -2` (window `[-3, -1]`). This is not
an artefact of the record's all-centres quantifier: the consumer `cover_of_LocalModulusEstimate`
needs the centre `gridPt 0 n 0 = 0` with radius `1/n`, and `[-1/n, 1/n]` already reaches the raw
coordinates, so restricting the record to `c ≥ 0` would not help. Fixes: a two-sided continuous
version, one-sided windows for block `0`, or replacing the record by
`HighLevelUpcrossingTail`, whose consumer `cover_of_upcrossing` only evaluates `Ã` on `[0, ∞)`. -/
theorem isEmpty_localModulusEstimate_airy1SRP (h : Airy1FddPositive) (hT : GOELeftTail) :
    IsEmpty (LocalModulusEstimate (airy1SRP h hT)) :=
  isEmpty_localModulusEstimate_of_coord (airy1SRP h hT) (c := -2) one_pos le_rfl
    fun t ht f => by
      have ht0 : ¬ 0 ≤ t := by linarith [ht.2]
      change airy1ContR h t f = f t
      rw [airy1ContR_of_not_nonneg h ht0]

/-! ### The headline on `airy1Law` -/

/-- **Headline `_of_QR₄` specialised to the Airy₁ law** (the paper's main theorem, Theorem 1.1,
normalized real-length form) on the continuous version `Ã`. `Y_meas`, `stat_marginal`, `stat_pair`,
`path_cont`, `Y_eq`, `hY` and `hA` are discharged (from `Airy1FddPositive` and `GOELeftTail`);
the remaining hypotheses are the QR-law records, the `mesoscopic` field and
`CubicStrongMixing` on `Ã`. -/
theorem gumbel_limit_continuum_real_normalized_airy1 (h : Airy1FddPositive) (hT : GOELeftTail)
    (qr : QRUnitBlockLaw (airy1BlockMax h) (airy1Law h))
    (qr₂ : QRTwoBlockLaw (airy1BlockMax h) (airy1Law h))
    (two : QRTwoIntervalLaw (airy1BlockMax h) (airy1Law h))
    (mesoscopic : ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
      Tendsto (fun N : ℕ =>
        (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          (airy1Law h).real {f | airy1BlockMax h 0 f > gumbelU N z ∧
            airy1BlockMax h j f > gumbelU N z}) atTop (𝓝 0))
    (M : CubicStrongMixing (airy1SRP h hT)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law h).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR h x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QR₄ (airy1BlockMax h)
    (measurable_airy1BlockMax h) (airy1BlockMax_stat_marginal h hT)
    (airy1BlockMax_stat_pair h hT) qr qr₂ two mesoscopic (airy1CMax h) rfl (airy1SRP h hT) rfl
    M z

end Airy1Gumbel
