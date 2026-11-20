/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Probability.CDF
import Airy1GumbelContrib.Fdd.FddDrop
import Airy1GumbelContrib.Fdd.FddGOE

open Filter MeasureTheory Set
open scoped Topology

namespace Airy1Gumbel

/-!
# The Airy₁ finite-dimensional laws — external-input record `Airy1FddPositive`

The contrib modules `Fdd/` (namespace `AiryFdd`) define, for every finite time set `I : Finset ℝ`
and level
vector `x : I → ℝ`, the real number `AiryFdd.airy1FinCdf I x`: the entire Fredholm
determinant of the trace-class conjugate of QR's path-integral operator
`I − B₀ + Λ^x_t e^{−(t_n−t₁)Δ} B₀` (QR Thm 1, read through their conjugated operator `J̃`).
Nothing in that definition makes `airy1FinCdf I` a distribution function: the extended kernel
defines a *signed* determinantal process, and positivity of the finite-dimensional laws comes
only from a probabilistic limit (TASEP). This module therefore records the existence of the
laws as an **external-input record** (`Airy1FddPositive`, in law form), and proves what follows
from it:

* `airy1Fdd h I` — the canonical law (`Classical.choose`), a probability measure on `I → ℝ`,
  unique among measures with that box-CDF (`airy1Fdd_unique`, via the π-system of boxes);
* `0 ≤ F ≤ 1`, monotonicity, and `F → 0` when one level tends to `−∞`;
* the GOE one-point anchor for `airy1Fdd h {t}` (contrib `airy1FinCdf_singleton_eq_fsGOE`);
* projectivity: the image of `airy1Fdd h I` under restriction to `I.erase t` is
  `airy1Fdd h (I.erase t)` (`airy1Fdd_map_erase`) — the consistency condition used by the
  Kolmogorov extension in `Airy1Process.lean`.

Vacuity and falsity checks for the record:

* Falsity witness: the same law-form schema with negated levels,
  `x ↦ airy1FinCdf I (−x)`, is refuted in Lean (`not_hasBoxCdfLaw_airy1FinCdf_neg`): a box-CDF
  must vanish as a level tends to `−∞`, while the reflected function tends to `1`
  (contrib `tendsto_airy1FinCdf_one`).
* Schema sanity: the constant `2` is refuted (`not_hasBoxCdfLaw_const_two`).
* Non-vacuity where checkable: the record's conclusion at `I = ∅` holds outright
  (`airy1FinCdf_law_empty`, a Dirac mass).

The record is the first hypothesis `h` of every headline on the concrete process, including
`gumbel_limit_continuum_real_normalized_airy1_final₂` (`FinalHeadlineTP.lean`).
-/

/-- The law-form schema for a family `F I : (I → ℝ) → ℝ` of would-be joint distribution
functions: for every finite time set `I` there is a probability measure on `I → ℝ` whose
lower-orthant (box) probabilities are `F I`. `Airy1FddPositive` is this schema at
`F = AiryFdd.airy1FinCdf` (`airy1FddPositive_iff`); the schema form is what the falsity
witnesses below refute for corrupted `F`. -/
def HasBoxCdfLaw (F : ∀ I : Finset ℝ, (I → ℝ) → ℝ) : Prop :=
  ∀ I : Finset ℝ, ∃ μ : Measure (I → ℝ), IsProbabilityMeasure μ ∧
    ∀ x : I → ℝ, μ.real (Set.pi Set.univ fun i => Set.Iic (x i)) = F I x

/-- **External-input record: the Airy₁ finite-dimensional laws exist.**
For every finite time set `I ⊂ ℝ` there is a probability measure `μ` on `I → ℝ` with
`μ{y : y s ≤ x s ∀ s ∈ I} = airy1FinCdf I x` for every level vector `x`.

*Provenance (justified by, not literally stated in, the sources).* The Airy₁ process is
defined by Sasamoto (2005) through its finite-dimensional distributions, given by the
extended-kernel Fredholm determinant `det(1 − χ_s K_{F1} χ_s)` on `L²({u₁<…<u_m} × ℝ)`
(Borodin–Ferrari–Prähofer, IMRP 2007, rpm002, MR2334008, arXiv:math-ph/0611071, Def. 2.3,
eqs. (2.5)–(2.6); this determinant is understood as its absolutely convergent Fredholm series,
equivalently as the Fredholm determinant of the trace-class conjugate of their App. A,
Prop. A.1, Lemmas A.2–A.3). BFP07 Thm 2.5 (proof, eqs. (5.9)–(5.14)) shows that for every
finite ordered time set and **every** level vector this series is the pointwise limit of
genuine joint distribution functions of rescaled discrete-time TASEP particle positions.
Limits of distribution functions can lose mass at `−∞`; this is excluded by the one-point
law `P(A₁(t) ≤ s) = F_GOE(2s)` (Ferrari–Spohn 2005; Tracy–Widom 1996), since
`F_I ≤ F_{{t}}` for `t ∈ I`. With continuity of the series this yields a probability measure
on `ℝ^I` with that box-CDF; this last step is standard and is not stated in the sources, hence
"justified by". Quastel–Remenik (PTRF 2013, Thm 1 and its proof, which starts
from the BFP07 extended kernel and its trace-class conjugation) identify the same quantity with
the path-integral determinant `det(I − B₀ + Λ^x_t e^{−(t_n−t₁)Δ} B₀)_{L²(ℝ)}` read through
their conjugate `J̃` (the conjugation remark following QR Thm 1; the displayed
finite-dimensional formula there has a heat-factor typo, `e^{−(t₂−t₁)Δ}` for `e^{−(t₂−t₃)Δ}`, which
Lean does not inherit).

*What the Lean right-hand side is.* `airy1FinCdf I x` is contrib's **entire** Fredholm
determinant `HilbertSchmidt.fredholmDet` (principal-minor series, no junk value) of the
V·W-factored trace-class conjugate at padding `τ = 1` and weight `a = 2S`. It is independent
of the padding and of the admissible weight (contrib `airy1FinCdf_eq_fredholmDet_fddOpAt`,
module `Fdd/FddIndep`). QR's determinant is therefore *computed via* `airy1FinCdf`
modulo the standard identity "entire determinant = integral-kernel Fredholm series", which is
**not** proved in Lean (the general-`n` `1/n!` expansion is not formalized). The one-point case is
anchored in Lean:
`airy1FinCdf {t} x = det(I − B_{2x})_{L²(0,∞)}`, Ferrari–Spohn's operator
(`AiryFdd.airy1FinCdf_singleton_eq_fsGOE`); `F_GOE(s) = det(I − B_s)` itself remains the cited
Ferrari–Spohn identity. BFP07 theorem numbers follow the arXiv v1 preprint.

*Scope.* Weaker than the sources: one law per finite `I`, with no process, path continuity or
stationarity asserted. The record is bound to the concrete `airy1FinCdf`, with no reachable
junk value; the two falsity witnesses below are proved; the conclusion holds outright at
`I = ∅`. -/
structure Airy1FddPositive : Prop where
  law : ∀ I : Finset ℝ, ∃ μ : Measure (I → ℝ), IsProbabilityMeasure μ ∧
    ∀ x : I → ℝ, μ.real (Set.pi Set.univ fun i => Set.Iic (x i)) = AiryFdd.airy1FinCdf I x

/-- The record is the law-form schema at `F = airy1FinCdf`. -/
theorem airy1FddPositive_iff : Airy1FddPositive ↔ HasBoxCdfLaw AiryFdd.airy1FinCdf :=
  ⟨fun h => h.law, fun h => ⟨h⟩⟩

/-! ## Generic facts about box-CDFs of finite-dimensional laws -/

/-- Lower-orthant boxes are measurable. -/
theorem measurableSet_orthant {ι : Type*} [Countable ι] (x : ι → ℝ) :
    MeasurableSet (Set.pi Set.univ fun i => Set.Iic (x i)) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Iic

/-- Two finite measures on `ι → ℝ` (`ι` finite) agreeing on all lower-orthant boxes and on
`univ` are equal: boxes `∏ Iic (x i)` form a π-system generating the product σ-algebra. -/
theorem ext_of_orthant {ι : Type*} [Finite ι] {μ ν : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (h : ∀ x : ι → ℝ, μ (Set.pi Set.univ fun i => Set.Iic (x i))
      = ν (Set.pi Set.univ fun i => Set.Iic (x i)))
    (huniv : μ univ = ν univ) : μ = ν := by
  refine ext_of_generate_finite (pi univ '' pi univ fun _ : ι => range (Iic : ℝ → Set ℝ))
    ?_ (IsPiSystem.pi fun _ => isPiSystem_Iic) ?_ huniv
  · refine (generateFrom_eq_pi (fun _ => ?_) (fun _ => ?_)).symm
    · exact (borel_eq_generateFrom_Iic ℝ).symm
    · refine ⟨fun n : ℕ => Iic (n : ℝ), fun n => ⟨_, rfl⟩, ?_⟩
      exact eq_univ_of_forall fun y => mem_iUnion.2 ⟨⌈y⌉₊, mem_Iic.2 (Nat.le_ceil y)⟩
  · rintro _ ⟨s, hs, rfl⟩
    have hs' : ∀ i, ∃ a : ℝ, Iic a = s i := fun i => hs i (mem_univ i)
    choose x hx using hs'
    have : s = fun i => Iic (x i) := funext fun i => (hx i).symm
    subst this
    exact h x

/-- Two probability measures on `ι → ℝ` (`ι` finite) with the same box-CDF are equal. -/
theorem eq_of_orthant_real {ι : Type*} [Finite ι] {μ ν : Measure (ι → ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x : ι → ℝ, μ.real (Set.pi Set.univ fun i => Set.Iic (x i))
      = ν.real (Set.pi Set.univ fun i => Set.Iic (x i))) : μ = ν :=
  ext_of_orthant (fun x => (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (measure_ne_top _ _)).1 (h x)) (by simp)

/-- The box-CDF of a probability measure on `ι → ℝ` tends to `0` when one level tends to
`−∞` (no mass at `−∞`): it is dominated by the one-dimensional CDF of that coordinate. -/
theorem tendsto_measureReal_orthant_zero {ι : Type*} (μ : Measure (ι → ℝ))
    [IsProbabilityMeasure μ] (t : ι) {α : Type*} {l : Filter α} {xn : α → ι → ℝ}
    (ht : Tendsto (fun n => xn n t) l atBot) :
    Tendsto (fun n => μ.real (Set.pi Set.univ fun i => Set.Iic (xn n i))) l (𝓝 0) := by
  have hmeas : Measurable fun y : ι → ℝ => y t := measurable_pi_apply t
  have hc := (ProbabilityTheory.tendsto_cdf_atBot (μ.map fun y : ι → ℝ => y t)).comp ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    (fun _ => measureReal_nonneg) (fun n => ?_)
  rw [Function.comp_apply, ProbabilityTheory.cdf_eq_real,
    map_measureReal_apply hmeas measurableSet_Iic]
  exact measureReal_mono (fun y hy => hy t (mem_univ t))

/-- Any family with a law-form box-CDF vanishes as one level tends to `−∞`. -/
theorem HasBoxCdfLaw.tendsto_zero {F : ∀ I : Finset ℝ, (I → ℝ) → ℝ} (hF : HasBoxCdfLaw F)
    (I : Finset ℝ) (t : I) {α : Type*} {l : Filter α} {xn : α → I → ℝ}
    (ht : Tendsto (fun n => xn n t) l atBot) : Tendsto (fun n => F I (xn n)) l (𝓝 0) := by
  obtain ⟨μ, hμ, hbox⟩ := hF I
  simpa only [hbox] using tendsto_measureReal_orthant_zero μ t ht

/-! ## Falsity witnesses and non-vacuity at `I = ∅` -/

/-- **Falsity witness.** The law-form schema with the levels negated,
`F' I x := airy1FinCdf I (−x)`, is false: at `I = {0}` and constant levels `c → −∞`, a box-CDF
must tend to `0`, but `F'` tends to `1` (contrib `tendsto_airy1FinCdf_one`). So the record's
content genuinely depends on the orientation of `airy1FinCdf`, and it is not satisfiable by
an arbitrary corrupted bounded function of the levels. -/
theorem not_hasBoxCdfLaw_airy1FinCdf_neg :
    ¬ HasBoxCdfLaw (fun I x => AiryFdd.airy1FinCdf I (-x)) := by
  intro hF
  have h0 := hF.tendsto_zero {0} ⟨0, Finset.mem_singleton_self 0⟩
    (xn := fun c : ℝ => fun _ => c) tendsto_id
  have h1 : Tendsto (fun c : ℝ => AiryFdd.airy1FinCdf {0} (fun _ => -c)) atBot (𝓝 1) :=
    AiryFdd.tendsto_airy1FinCdf_one {0} (fun _ => tendsto_neg_atBot_atTop)
  exact one_ne_zero (tendsto_nhds_unique h1 h0)

/-- **Falsity witness, every nonempty time set.** For every nonempty `I`, no probability measure on
`I → ℝ` has box-CDF `x ↦ airy1FinCdf I (−x)`. -/
theorem not_exists_law_airy1FinCdf_neg (I : Finset ℝ) (hI : I.Nonempty) :
    ¬ ∃ μ : Measure (I → ℝ), IsProbabilityMeasure μ ∧
      ∀ x : I → ℝ, μ.real (Set.pi Set.univ fun i => Set.Iic (x i))
        = AiryFdd.airy1FinCdf I (-x) := by
  rintro ⟨μ, hμ, hbox⟩
  obtain ⟨t, ht⟩ := hI
  have h0 := tendsto_measureReal_orthant_zero μ ⟨t, ht⟩
    (xn := fun c : ℝ => fun _ => c) tendsto_id
  simp only [hbox] at h0
  have h1 : Tendsto (fun c : ℝ => AiryFdd.airy1FinCdf I (fun _ => -c)) atBot (𝓝 1) :=
    AiryFdd.tendsto_airy1FinCdf_one I (fun _ => tendsto_neg_atBot_atTop)
  exact one_ne_zero (tendsto_nhds_unique h1 h0)

/-- **Schema sanity.** The constant `2` is not a box-CDF (a probability is `≤ 1`). -/
theorem not_hasBoxCdfLaw_const_two : ¬ HasBoxCdfLaw (fun _ _ => (2 : ℝ)) := by
  intro hF
  obtain ⟨μ, hμ, hbox⟩ := hF ∅
  have h := hbox (fun i => (Finset.notMem_empty _ i.2).elim)
  have : μ.real (Set.pi Set.univ fun i => Set.Iic
      ((fun i : (∅ : Finset ℝ) => (Finset.notMem_empty _ i.2).elim : (∅ : Finset ℝ) → ℝ) i))
      ≤ 1 := measureReal_le_one
  linarith

/-- **Non-vacuity at `I = ∅`.** The record's conclusion holds outright for the empty time
set: the Dirac mass at the unique point of `∅ → ℝ` has box-CDF `1 = airy1FinCdf ∅ x`. -/
theorem airy1FinCdf_law_empty :
    ∃ μ : Measure ((∅ : Finset ℝ) → ℝ), IsProbabilityMeasure μ ∧
      ∀ x : (∅ : Finset ℝ) → ℝ, μ.real (Set.pi Set.univ fun i => Set.Iic (x i))
        = AiryFdd.airy1FinCdf ∅ x := by
  refine ⟨Measure.dirac fun i => (Finset.notMem_empty _ i.2).elim, inferInstance, fun x => ?_⟩
  have hbox : (Set.pi Set.univ fun i => Set.Iic (x i)) = univ :=
    eq_univ_of_forall fun _ i => (Finset.notMem_empty _ i.2).elim
  rw [hbox, probReal_univ, AiryFdd.airy1FinCdf_empty]

/-! ## Consequences of the record -/

/-- The canonical Airy₁ finite-dimensional law on `I → ℝ` (choice is canonical by
`airy1Fdd_unique`). -/
noncomputable def airy1Fdd (h : Airy1FddPositive) (I : Finset ℝ) : Measure (I → ℝ) :=
  Classical.choose (h.law I)

/-- `airy1Fdd h I` is a probability measure. -/
theorem isProbabilityMeasure_airy1Fdd (h : Airy1FddPositive) (I : Finset ℝ) :
    IsProbabilityMeasure (airy1Fdd h I) :=
  (Classical.choose_spec (h.law I)).1

instance (h : Airy1FddPositive) (I : Finset ℝ) : IsProbabilityMeasure (airy1Fdd h I) :=
  isProbabilityMeasure_airy1Fdd h I

/-- The box-CDF of `airy1Fdd h I` is `airy1FinCdf I`. -/
theorem airy1Fdd_orthant (h : Airy1FddPositive) (I : Finset ℝ) (x : I → ℝ) :
    (airy1Fdd h I).real (Set.pi Set.univ fun i => Set.Iic (x i)) = AiryFdd.airy1FinCdf I x :=
  (Classical.choose_spec (h.law I)).2 x

/-- Uniqueness: any probability measure with box-CDF `airy1FinCdf I` is `airy1Fdd h I`. -/
theorem airy1Fdd_unique (h : Airy1FddPositive) {I : Finset ℝ} (μ : Measure (I → ℝ))
    [IsProbabilityMeasure μ]
    (hμ : ∀ x : I → ℝ, μ.real (Set.pi Set.univ fun i => Set.Iic (x i))
      = AiryFdd.airy1FinCdf I x) : μ = airy1Fdd h I :=
  eq_of_orthant_real fun x => by rw [hμ, airy1Fdd_orthant]

/-- Under the record, `0 ≤ airy1FinCdf I x`. -/
theorem Airy1FddPositive.airy1FinCdf_nonneg (h : Airy1FddPositive) (I : Finset ℝ)
    (x : I → ℝ) : 0 ≤ AiryFdd.airy1FinCdf I x := by
  rw [← airy1Fdd_orthant h]; exact measureReal_nonneg

/-- Under the record, `airy1FinCdf I x ≤ 1`. -/
theorem Airy1FddPositive.airy1FinCdf_le_one (h : Airy1FddPositive) (I : Finset ℝ)
    (x : I → ℝ) : AiryFdd.airy1FinCdf I x ≤ 1 := by
  rw [← airy1Fdd_orthant h]; exact measureReal_le_one

/-- Under the record, `airy1FinCdf I` is monotone in the levels (coordinatewise order). -/
theorem Airy1FddPositive.monotone_airy1FinCdf (h : Airy1FddPositive) (I : Finset ℝ) :
    Monotone (AiryFdd.airy1FinCdf I) := fun x y hxy => by
  rw [← airy1Fdd_orthant h, ← airy1Fdd_orthant h]
  exact measureReal_mono fun z hz i _ => (hz i (mem_univ i)).trans (hxy i)

/-- Under the record, `airy1FinCdf I` tends to `0` when one level tends to `−∞`. -/
theorem Airy1FddPositive.tendsto_airy1FinCdf_zero (h : Airy1FddPositive) (I : Finset ℝ)
    (t : I) {α : Type*} {l : Filter α} {xn : α → I → ℝ}
    (ht : Tendsto (fun n => xn n t) l atBot) :
    Tendsto (fun n => AiryFdd.airy1FinCdf I (xn n)) l (𝓝 0) :=
  (airy1FddPositive_iff.1 h).tendsto_zero I t ht

/-- **GOE one-point anchor.** The one-point law `airy1Fdd h {t}` has box-CDF
`det(I − B_{2x})_{L²(0,∞)}`, Ferrari–Spohn's GOE operator at `2x` (contrib
`airy1FinCdf_singleton_eq_fsGOE`): `P(A₁(t) ≤ x) = F_GOE(2x)` modulo the cited identity
`F_GOE(s) = det(I − B_s)`. -/
theorem airy1Fdd_singleton_orthant (h : Airy1FddPositive) (t : ℝ)
    (x : ({t} : Finset ℝ) → ℝ) :
    (airy1Fdd h {t}).real (Set.pi Set.univ fun i => Set.Iic (x i))
      = HilbertSchmidt.fredholmDet (AiryFdd.fsOp (2 * x ⟨t, Finset.mem_singleton_self t⟩)) 1 := by
  rw [airy1Fdd_orthant, AiryFdd.airy1FinCdf_singleton_eq_fsGOE]

/-! ## Projectivity -/

/-- Restriction of a level/path vector on `I` to `I.erase t`. -/
def restrictErase (I : Finset ℝ) (t : ℝ) (y : I → ℝ) : I.erase t → ℝ :=
  fun s => y ⟨s.1, Finset.mem_of_mem_erase s.2⟩

theorem measurable_restrictErase (I : Finset ℝ) (t : ℝ) : Measurable (restrictErase I t) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- **Projectivity.** Under the record, the image of `airy1Fdd h I` under restriction to
`I.erase t` (`t ∈ I`) is `airy1Fdd h (I.erase t)`. Proof: both are probability measures; the
preimage of a box of `I.erase t` is the increasing union of the boxes of `I` with level `n` at
`t`, so by continuity from below its mass is `lim_n airy1FinCdf I (x, n)`, which is
`airy1FinCdf (I.erase t) x` by contrib `tendsto_airy1FinCdf_erase`; conclude by box-uniqueness.
This is the consistency condition used by the Kolmogorov extension in `Airy1Process.lean`. -/
theorem airy1Fdd_map_erase (h : Airy1FddPositive) (I : Finset ℝ) {t : ℝ} (ht : t ∈ I) :
    (airy1Fdd h I).map (restrictErase I t) = airy1Fdd h (I.erase t) := by
  refine airy1Fdd_unique h _ fun x' => ?_
  rw [map_measureReal_apply (measurable_restrictErase I t) (measurableSet_orthant x')]
  -- extend `x'` to `I` (value at `t` irrelevant) and raise the level at `t` to `n`
  set x : I → ℝ := fun s => if hs : s.1 = t then 0 else x' ⟨s.1, Finset.mem_erase.2 ⟨hs, s.2⟩⟩
    with hxdef
  set xn : ℕ → I → ℝ := fun n s => if s.1 = t then (n : ℝ) else x s with hxndef
  set B : ℕ → Set (I → ℝ) := fun n => Set.pi Set.univ fun i => Set.Iic (xn n i) with hBdef
  have hBmono : Monotone B := by
    intro n m hnm y hy i _
    have := hy i (mem_univ i)
    simp only [hxndef, mem_Iic] at this ⊢
    split_ifs at this ⊢ with hi
    · exact this.trans (by exact_mod_cast hnm)
    · exact this
  have hU : (⋃ n, B n) = restrictErase I t ⁻¹' Set.pi Set.univ fun i => Set.Iic (x' i) := by
    ext y
    simp only [mem_iUnion, mem_preimage, mem_univ_pi, mem_Iic, hBdef, hxndef, hxdef,
      restrictErase]
    constructor
    · rintro ⟨n, hn⟩ s
      have := hn ⟨s.1, Finset.mem_of_mem_erase s.2⟩
      have hst : s.1 ≠ t := (Finset.mem_erase.1 s.2).1
      simpa [hst] using this
    · intro hy
      refine ⟨⌈y ⟨t, ht⟩⌉₊, fun s => ?_⟩
      by_cases hst : s.1 = t
      · simp only [hst, ite_true]
        have : s = ⟨t, ht⟩ := Subtype.ext hst
        subst this
        exact Nat.le_ceil _
      · simp only [hst, ite_false, dite_false]
        exact hy ⟨s.1, Finset.mem_erase.2 ⟨hst, s.2⟩⟩
  have hlim : Tendsto (fun n => (airy1Fdd h I).real (B n)) atTop
      (𝓝 ((airy1Fdd h I).real (⋃ n, B n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_iUnion_atTop hBmono)
  have hF : Tendsto (fun n => AiryFdd.airy1FinCdf I (xn n)) atTop
      (𝓝 (AiryFdd.airy1FinCdf (I.erase t)
        (fun s => x ⟨s.1, Finset.mem_of_mem_erase s.2⟩))) := by
    refine AiryFdd.tendsto_airy1FinCdf_erase I ht x (fun s hs => ?_) ?_
    · simp only [hxndef, hs, ite_false]; exact tendsto_const_nhds
    · simp only [hxndef, ite_true]; exact tendsto_natCast_atTop_atTop
  have hx' : (fun s : I.erase t => x ⟨s.1, Finset.mem_of_mem_erase s.2⟩) = x' := by
    funext s
    have hst : s.1 ≠ t := (Finset.mem_erase.1 s.2).1
    simp [hxdef, hst]
  rw [hx'] at hF
  simp only [hBdef, airy1Fdd_orthant] at hlim
  rw [← hU]
  exact tendsto_nhds_unique hlim hF

end Airy1Gumbel
