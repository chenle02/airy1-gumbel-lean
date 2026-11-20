/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.TwoSidedBM

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Airy1Gumbel

/-!
# The Groeneboom process: parabolically penalized suprema of two-sided
Brownian motion

This module formalizes the *Groeneboom process* as a path functional on the
two-sided Brownian motion built in `Airy1Gumbel.TwoSidedBM`:

* `groeneboomU t ω := sSup_x { √2 (B(x) − B(t)) − (x−t)² }` — the recentered
  supremum (Groeneboom's "Brownian motion minus a parabola" maximum;
  Groeneboom 1989), written as a `sSup` over the range of the integrand;
* `groeneboomS t ω := √2 B(t) + groeneboomU t ω` — the raw supremum
  `sSup_x { √2 B(x) − (x−t)² }`.

Main results:

* `groeneboom_nonneg`: `0 ≤ groeneboomU t ω` for *every* path (the integrand
  at `x = t` equals `0`, and ℝ's `sSup` convention assigns `0` to unbounded
  sets). This is the support-mismatch witness against the GOE Tracy–Widom
  law `F₁(2·)`: the one-point marginal of the recentered object is supported
  on `[0, ∞)`, whereas the Airy₁ one-point marginal has full support (so the
  two one-point laws differ).
* `aemeasurable_groeneboomU`: `groeneboomU t` is almost-everywhere measurable
  (equal a.s. to the rational supremum `groeneboomSupQ (shiftIncr t ·)`, which
  is measurable);
* `groeneboom_bddAbove` / `groeneboomU_attained`: on the full-measure event
  `groeneboomGoodEvent` (continuous paths, sublinear growth at both ends, and
  pinned at 0), the integrand's range is bounded above and the supremum is
  attained;
* `groeneboom_stationary`: **the recentered process is stationary**: the law
  of `groeneboomU t` under `twoSidedBMMeasure` equals that of `groeneboomU 0`
  for every `t`. The proof reindexes `x = y + t` and applies the shift
  invariance of the two-sided Brownian motion (`map_twoSidedBM_shift_incr`).
* `groeneboom_stationary_fdd`: **full finite-dimensional
  stationarity** — for `t : Fin k → ℝ` and shift `s`, the laws of the vectors
  `(groeneboomU (t i + s))ᵢ` and `(groeneboomU (t i))ᵢ` on `Fin k → ℝ`
  coincide (plus `groeneboom_stationary_pair`, the `k = 2` corollary on
  `ℝ × ℝ`, and `groeneboomSupQ_stationary_fdd`, the algebraic core at the
  measurable-supremum level).
* `groeneboomU_continuous_ae`: **a.s. path continuity** —
  `t ↦ groeneboomU t ω` is continuous for almost every `ω`, via the uniform
  negativity scale (`groeneboom_neg_bound_uniform`), localization to the
  compact window (`groeneboomU_eq_compactSup`), and the continuity of the
  compact supremum (`groeneboomCompactSup_continuous`). Together with
  `groeneboom_stationary_fdd`, the recentered Groeneboom process is a
  stationary process with a.s. continuous paths (fdd version;
  Kolmogorov–Chentsov strengthening not claimed).

The raw process `groeneboomS` is *not* stationary: it is the sum of the
stationary recentered process and `√2 B(t)`, whose law is Gaussian with
variance `2|t|` (`hasLaw_sqrt_two_mul_twoSidedBM`), visibly drifting with `t`
(B(t) and U(t) are dependent; a fully rigorous non-stationarity proof would
require controlling that dependence, which we record as an open remark).
-/

/-- The integrand of the recentered Groeneboom supremum:
`x ↦ √2 (B(x) − B(t)) − (x−t)²`. -/
noncomputable def groeneboomIntegrand (t : ℝ) (ω : TwoSidedΩ) (x : ℝ) : ℝ :=
  Real.sqrt 2 * (twoSidedBM x ω - twoSidedBM t ω) - (x - t)^2

/-- The recentered Groeneboom supremum `U(B, t)`. -/
noncomputable def groeneboomU (t : ℝ) (ω : TwoSidedΩ) : ℝ :=
  sSup (Set.range (groeneboomIntegrand t ω))

/-- The raw parabolic supremum process `S(B, t) := √2 B(t) + U(B, t)`. -/
noncomputable def groeneboomS (t : ℝ) (ω : TwoSidedΩ) : ℝ :=
  Real.sqrt 2 * twoSidedBM t ω + groeneboomU t ω

/-- The path-level supremum `sSup_y { √2 f(y) − y² }` over the reals. -/
noncomputable def groeneboomSup (f : ℝ → ℝ) : ℝ :=
  sSup (Set.range fun y : ℝ ↦ Real.sqrt 2 * f y - y^2)

/-- The path-level supremum over the rationals — this one is measurable in the
path for the product σ-algebra. -/
noncomputable def groeneboomSupQ (f : ℝ → ℝ) : ℝ :=
  sSup (Set.range fun q : ℚ ↦ Real.sqrt 2 * f (q : ℝ) - (q : ℝ)^2)

/-- The shifted-increment path map `ω ↦ (y ↦ B(y + t) ω − B(t) ω)`. -/
noncomputable def shiftIncr (t : ℝ) (ω : TwoSidedΩ) : ℝ → ℝ :=
  fun y ↦ twoSidedBM (y + t) ω - twoSidedBM t ω

/-! ## Nonnegativity and the raw decomposition -/

/-- The integrand vanishes at `x = t`, for every path. -/
lemma groeneboomIntegrand_self (t : ℝ) (ω : TwoSidedΩ) :
    groeneboomIntegrand t ω t = 0 := by
  simp [groeneboomIntegrand]

/-- **Nonnegativity**: `0 ≤ U(B, t)` for every path `ω`. This is the
support-mismatch witness against the GOE law `F₁(2·)`: the recentered Groeneboom marginal is supported on `[0, ∞)`. -/
lemma groeneboom_nonneg (t : ℝ) (ω : TwoSidedΩ) : 0 ≤ groeneboomU t ω := by
  by_cases hbdd : BddAbove (Set.range (groeneboomIntegrand t ω))
  · rw [← groeneboomIntegrand_self t ω]
    exact le_csSup hbdd ⟨t, rfl⟩
  · rw [groeneboomU, Real.sSup_of_not_bddAbove hbdd]

/-- The raw process dominates the Gaussian part: `√2 B(t) ≤ S(B, t)`. -/
lemma sqrt_two_mul_le_groeneboomS (t : ℝ) (ω : TwoSidedΩ) :
    Real.sqrt 2 * twoSidedBM t ω ≤ groeneboomS t ω :=
  le_add_of_nonneg_right (groeneboom_nonneg t ω)

/-- At time `0`, the raw process coincides with the recentered supremum, a.s. -/
lemma groeneboomS_zero_ae :
    ∀ᵐ ω ∂twoSidedBMMeasure, groeneboomS 0 ω = groeneboomU 0 ω := by
  filter_upwards [twoSidedBM_zero] with ω hω
  rw [groeneboomS, hω, mul_zero, zero_add]

/-! ## The one-dimensional law of `B(t)` and of `√2 B(t)` -/

/-- The one-dimensional marginal of the two-sided Brownian motion:
`B(t) ~ N(0, |t|)`. -/
lemma hasLaw_twoSidedBM_eval (t : ℝ) :
    HasLaw (fun ω ↦ twoSidedBM t ω)
      (gaussianReal 0 (NNReal.mk |t| (abs_nonneg t))) twoSidedBMMeasure := by
  rcases lt_or_ge t 0 with ht | ht
  swap
  · -- on the positive side, `twoSidedBM t = brownian ⟨t⟩ ∘ Prod.fst`
    have hfun : (fun ω ↦ twoSidedBM t ω) = fun ω ↦ brownian t.toNNReal ω.1 := by
      funext ω
      rw [twoSidedBM, if_pos ht]
    rw [hfun]
    have h := (hasLaw_brownian_eval (t := t.toNNReal)).comp
      (measurePreserving_fst (μ := gaussianLimit) (ν := gaussianLimit)).hasLaw
    have hvar : gaussianReal 0 t.toNNReal = gaussianReal 0 (NNReal.mk |t| (abs_nonneg t)) := by
      congr 1
      apply NNReal.eq_iff.mpr
      rw [Real.coe_toNNReal t ht, NNReal.coe_mk]
      exact (abs_of_nonneg ht).symm
    rw [hvar] at h
    show HasLaw (fun ω ↦ brownian t.toNNReal ω.1) (gaussianReal 0 (NNReal.mk |t| (abs_nonneg t)))
      (gaussianLimit.prod gaussianLimit)
    exact h
  · -- on the negative side, `twoSidedBM t = brownian ⟨-t⟩ ∘ Prod.snd`
    have hfun : (fun ω ↦ twoSidedBM t ω) = fun ω ↦ brownian (-t).toNNReal ω.2 := by
      funext ω
      rw [twoSidedBM, if_neg (not_le.mpr ht)]
    rw [hfun]
    have h := (hasLaw_brownian_eval (t := (-t).toNNReal)).comp
      (measurePreserving_snd (μ := gaussianLimit) (ν := gaussianLimit)).hasLaw
    have hvar : gaussianReal 0 (-t).toNNReal = gaussianReal 0 (NNReal.mk |t| (abs_nonneg t)) := by
      congr 1
      apply NNReal.eq_iff.mpr
      have hnn : 0 ≤ -t := by linarith
      rw [Real.coe_toNNReal (-t) hnn, NNReal.coe_mk]
      exact (abs_of_neg ht).symm
    rw [hvar] at h
    show HasLaw (fun ω ↦ brownian (-t).toNNReal ω.2) (gaussianReal 0 (NNReal.mk |t| (abs_nonneg t)))
      (gaussianLimit.prod gaussianLimit)
    exact h

/-- The Gaussian part of the raw Groeneboom process: `√2 B(t) ~ N(0, 2|t|)`.
The variance `2|t|` drifts with `t`: this is the quantitative content behind
the non-stationarity of the raw process `groeneboomS` (see its docstring). -/
lemma hasLaw_sqrt_two_mul_twoSidedBM (t : ℝ) :
    HasLaw (fun ω ↦ Real.sqrt 2 * twoSidedBM t ω)
      (gaussianReal 0 (NNReal.mk (Real.sqrt 2 ^ 2) (sq_nonneg _) * NNReal.mk |t| (abs_nonneg t)))
      twoSidedBMMeasure := by
  have hmeas : Measurable fun x : ℝ ↦ Real.sqrt 2 * x := measurable_const.mul measurable_id
  have hmap0 := hasLaw_map (P := gaussianReal 0 (NNReal.mk |t| (abs_nonneg t)))
    hmeas.aemeasurable
  rw [gaussianReal_map_const_mul] at hmap0
  rw [mul_zero] at hmap0
  exact hmap0.comp (hasLaw_twoSidedBM_eval t)


/-! ## Brownian growth on the two-sided process

The one-sided growth bound `B(u)/u → 0` (`IsBrownianReal.tendsto_div_id_atTop`
in the dependency) transferred to the product space and assembled at both
ends. -/

/-- Almost-everywhere transfer through the first projection of a product
measure. -/
lemma ae_fst_prod {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure ν] {p : Ω → Prop}
    (h : ∀ᵐ ω ∂μ, p ω) : ∀ᵐ ω ∂(μ.prod ν), p ω.1 := by
  rw [ae_iff] at h ⊢
  have hset : {ω : Ω × Ω' | ¬ p ω.1} = {ω | ¬ p ω} ×ˢ univ := by
    ext ω
    simp [Set.mem_prod]
  rw [hset, Measure.prod_prod, h]
  simp

/-- Almost-everywhere transfer through the second projection of a product
measure. -/
lemma ae_snd_prod {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {p : Ω' → Prop} (h : ∀ᵐ ω ∂ν, p ω) : ∀ᵐ ω ∂(μ.prod ν), p ω.2 := by
  rw [ae_iff] at h ⊢
  have hset : {ω : Ω × Ω' | ¬ p ω.2} = univ ×ˢ {ω | ¬ p ω} := by
    ext ω
    simp [Set.mem_prod]
  rw [hset, Measure.prod_prod, h]
  simp

/-- The one-sided growth bound on the first coordinate. -/
lemma brownian_div_atTop_fst : ∀ᵐ ω ∂twoSidedBMMeasure,
    Tendsto (fun u : ℝ≥0 ↦ brownian u ω.1 / (u : ℝ)) atTop (𝓝 0) :=
  ae_fst_prod isBrownianReal_brownian.tendsto_div_id_atTop

/-- The one-sided growth bound on the second coordinate. -/
lemma brownian_div_atTop_snd : ∀ᵐ ω ∂twoSidedBMMeasure,
    Tendsto (fun u : ℝ≥0 ↦ brownian u ω.2 / (u : ℝ)) atTop (𝓝 0) :=
  ae_snd_prod isBrownianReal_brownian.tendsto_div_id_atTop

/-- `Real.toNNReal` tends to `atTop` along `atTop`. -/
lemma tendsto_real_toNNReal_atTop : Tendsto Real.toNNReal atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b : ℝ)] with x hx
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal x (b.coe_nonneg.trans hx)]
  exact hx

/-- The aux process is sublinear at `+∞`, a.s. -/
lemma aux_div_atTop : ∀ᵐ ω ∂twoSidedBMMeasure,
    Tendsto (fun x : ℝ ↦ twoSidedBMAux x ω / x) atTop (𝓝 0) := by
  filter_upwards [brownian_div_atTop_fst] with ω hω
  have h1 : Tendsto (fun x : ℝ ↦ brownian x.toNNReal ω.1 / x) atTop (𝓝 0) := by
    have hcomp := hω.comp tendsto_real_toNNReal_atTop
    refine hcomp.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    simp [Real.coe_toNNReal x hx]
  have h2 : Tendsto (fun x : ℝ ↦ brownian (-x).toNNReal ω.2 / x) atTop (𝓝 0) := by
    have heq : (fun x : ℝ ↦ brownian 0 ω.2 / x) =ᶠ[atTop]
        fun x ↦ brownian (-x).toNNReal ω.2 / x := by
      filter_upwards [eventually_ge_atTop 0] with x hx
      rw [Real.toNNReal_of_nonpos (by linarith : -x ≤ 0)]
    refine Tendsto.congr' heq ?_
    have hdiv : Tendsto (fun x : ℝ ↦ brownian 0 ω.2 * x⁻¹) atTop (𝓝 (brownian 0 ω.2 * 0)) :=
      Tendsto.const_mul (brownian 0 ω.2) tendsto_inv_atTop_zero
    rwa [mul_zero, show (fun x : ℝ ↦ brownian 0 ω.2 * x⁻¹) = fun x ↦ brownian 0 ω.2 / x from
      funext fun x ↦ div_eq_mul_inv _ _] at hdiv
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards with x
  rw [twoSidedBMAux]
  exact (add_div _ _ _).symm

/-- The aux process is sublinear at `−∞`, a.s. -/
lemma aux_div_atBot : ∀ᵐ ω ∂twoSidedBMMeasure,
    Tendsto (fun x : ℝ ↦ twoSidedBMAux x ω / x) atBot (𝓝 0) := by
  filter_upwards [brownian_div_atTop_snd] with ω hω
  have h1 : Tendsto (fun x : ℝ ↦ brownian x.toNNReal ω.1 / x) atBot (𝓝 0) := by
    have heq : (fun x : ℝ ↦ brownian 0 ω.1 / x) =ᶠ[atBot]
        fun x ↦ brownian x.toNNReal ω.1 / x := by
      filter_upwards [eventually_le_atBot 0] with x hx
      rw [Real.toNNReal_of_nonpos hx]
    refine Tendsto.congr' heq ?_
    have hdiv : Tendsto (fun x : ℝ ↦ brownian 0 ω.1 * x⁻¹) atBot (𝓝 (brownian 0 ω.1 * 0)) :=
      Tendsto.const_mul (brownian 0 ω.1) tendsto_inv_atBot_zero
    rwa [mul_zero, show (fun x : ℝ ↦ brownian 0 ω.1 * x⁻¹) = fun x ↦ brownian 0 ω.1 / x from
      funext fun x ↦ div_eq_mul_inv _ _] at hdiv
  have h2 : Tendsto (fun x : ℝ ↦ brownian (-x).toNNReal ω.2 / x) atBot (𝓝 0) := by
    have hG : Tendsto ((fun u : ℝ≥0 ↦ brownian u ω.2 / (u : ℝ)) ∘ (Real.toNNReal ∘ Neg.neg))
        atBot (𝓝 0) := hω.comp (tendsto_real_toNNReal_atTop.comp tendsto_neg_atBot_atTop)
    have heq : (fun x : ℝ ↦
        -(((fun u : ℝ≥0 ↦ brownian u ω.2 / (u : ℝ)) ∘ (Real.toNNReal ∘ Neg.neg)) x)) =ᶠ[atBot]
        fun x ↦ brownian (-x).toNNReal ω.2 / x := by
      filter_upwards [eventually_le_atBot 0] with x hx
      have hnn : 0 ≤ -x := by linarith
      simp only [Function.comp_apply]
      rw [Real.coe_toNNReal (-x) hnn, div_neg, neg_neg]
    refine Tendsto.congr' heq ?_
    have hneg := hG.neg
    rwa [neg_zero] at hneg
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards with x
  rw [twoSidedBMAux]
  exact (add_div _ _ _).symm

/-- Sublinear growth of the two-sided Brownian motion at `+∞`, a.s. -/
lemma twoSidedBM_div_atTop : ∀ᵐ ω ∂twoSidedBMMeasure,
    Tendsto (fun x : ℝ ↦ twoSidedBM x ω / x) atTop (𝓝 0) := by
  filter_upwards [twoSidedBM_ae_eq_aux, aux_div_atTop] with ω h1 h2
  have hfun : (fun x : ℝ ↦ twoSidedBM x ω / x) = (fun x ↦ twoSidedBMAux x ω / x) :=
    funext fun x ↦ by rw [h1 x]
  rw [hfun]
  exact h2

/-- Sublinear growth of the two-sided Brownian motion at `−∞`, a.s. -/
lemma twoSidedBM_div_atBot : ∀ᵐ ω ∂twoSidedBMMeasure,
    Tendsto (fun x : ℝ ↦ twoSidedBM x ω / x) atBot (𝓝 0) := by
  filter_upwards [twoSidedBM_ae_eq_aux, aux_div_atBot] with ω h1 h2
  have hfun : (fun x : ℝ ↦ twoSidedBM x ω / x) = (fun x ↦ twoSidedBMAux x ω / x) :=
    funext fun x ↦ by rw [h1 x]
  rw [hfun]
  exact h2


/-! ## The good event: boundedness and attainment of the supremum -/

/-- The full-measure event of good paths for the Groeneboom construction:
continuous, sublinear at both ends, and pinned at `0`. -/
def groeneboomGoodEvent : Set TwoSidedΩ :=
  {ω | Continuous (twoSidedBM · ω)}
    ∩ {ω | Tendsto (fun x ↦ twoSidedBM x ω / x) atTop (𝓝 0)}
    ∩ {ω | Tendsto (fun x ↦ twoSidedBM x ω / x) atBot (𝓝 0)}
    ∩ {ω | twoSidedBM 0 ω = 0}

/-- The good event has full measure. -/
lemma groeneboomGoodEvent_ae :
    ∀ᵐ ω ∂twoSidedBMMeasure, ω ∈ groeneboomGoodEvent := by
  filter_upwards [continuous_twoSidedBM, twoSidedBM_div_atTop, twoSidedBM_div_atBot,
    twoSidedBM_zero] with ω h1 h2 h3 h4
  exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- The integrand is continuous for a continuous path. -/
lemma continuous_groeneboomIntegrand {ω : TwoSidedΩ}
    (hω : Continuous (twoSidedBM · ω)) (t : ℝ) :
    Continuous (groeneboomIntegrand t ω) :=
  ((continuous_const.mul (hω.sub continuous_const)).sub
    ((continuous_id.sub continuous_const).pow 2))

/-- Coercivity ratio: for a path with sublinear growth, the integrand divided
by `x²` tends to `−1` along any filter where `x⁻¹ → 0` and `x ≠ 0`
eventually. -/
lemma groeneboomIntegrand_ratio (ω : TwoSidedΩ) (t : ℝ)
    {F : Filter ℝ}
    (hgrowth : Tendsto (fun x ↦ twoSidedBM x ω / x) F (𝓝 0))
    (hinv : Tendsto (fun x ↦ x⁻¹) F (𝓝 0))
    (hne : ∀ᶠ x in F, x ≠ 0) :
    Tendsto (fun x ↦ groeneboomIntegrand t ω x / x^2) F (𝓝 (-1)) := by
  have h1 : Tendsto (fun x ↦ Real.sqrt 2 * (twoSidedBM x ω / x * x⁻¹)) F (𝓝 (√2 * (0 * 0))) :=
    (hgrowth.mul hinv).const_mul (Real.sqrt 2)
  have h2 : Tendsto (fun x ↦ Real.sqrt 2 * (twoSidedBM t ω * (x^2)⁻¹)) F
      (𝓝 (√2 * (twoSidedBM t ω * 0))) := by
    have hmul : Tendsto (fun x : ℝ ↦ x⁻¹ * x⁻¹) F (𝓝 (0 * 0)) := hinv.mul hinv
    rw [mul_zero] at hmul
    have hcast : Tendsto (fun x : ℝ ↦ (x^2)⁻¹) F (𝓝 0) := by
      refine hmul.congr' ?_
      filter_upwards with x
      rw [pow_two, mul_inv_rev]
    exact (hcast.const_mul (twoSidedBM t ω)).const_mul (Real.sqrt 2)
  have h3 : Tendsto (fun x ↦ (1 - t * x⁻¹)^2) F (𝓝 ((1 - 0)^2)) := by
    have hmul : Tendsto (fun x ↦ t * x⁻¹) F (𝓝 (t * 0)) := hinv.const_mul t
    rw [mul_zero] at hmul
    exact (tendsto_const_nhds.sub hmul).pow 2
  have h := (h1.sub h2).sub h3
  simp only [mul_zero, one_pow, sub_zero, zero_sub] at h
  refine h.congr' ?_
  filter_upwards [hne] with x hx0
  have hx2 : x^2 ≠ 0 := pow_ne_zero 2 hx0
  rw [groeneboomIntegrand]
  field_simp

/-- On the good event the integrand is eventually negative at `+∞`. -/
lemma groeneboomIntegrand_neg_atTop {ω : TwoSidedΩ} (hω : ω ∈ groeneboomGoodEvent) (t : ℝ) :
    ∀ᶠ x : ℝ in atTop, groeneboomIntegrand t ω x < 0 := by
  have htop := hω.1.1.2
  have hne : ∀ᶠ x : ℝ in atTop, x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact ne_of_gt hx
  have hratio := groeneboomIntegrand_ratio ω t htop tendsto_inv_atTop_zero hne
  have hlt : ∀ᶠ x : ℝ in atTop, groeneboomIntegrand t ω x / x^2 < 0 :=
    hratio.eventually_lt_const (by norm_num : (-1 : ℝ) < 0)
  filter_upwards [hlt, eventually_gt_atTop 0] with x hx hxpos
  have hsq : (0 : ℝ) < x^2 := sq_pos_of_pos hxpos
  have hneg : groeneboomIntegrand t ω x / x^2 * x^2 < 0 :=
    mul_neg_of_neg_of_pos hx hsq
  rwa [div_mul_cancel₀ _ (ne_of_gt hsq)] at hneg

/-- On the good event the integrand is eventually negative at `−∞`. -/
lemma groeneboomIntegrand_neg_atBot {ω : TwoSidedΩ} (hω : ω ∈ groeneboomGoodEvent) (t : ℝ) :
    ∀ᶠ x : ℝ in atBot, groeneboomIntegrand t ω x < 0 := by
  have hbot := hω.1.2
  have hne : ∀ᶠ x : ℝ in atBot, x ≠ 0 := by
    filter_upwards [eventually_le_atBot (-1)] with x hx
    exact ne_of_lt (by linarith)
  have hratio := groeneboomIntegrand_ratio ω t hbot tendsto_inv_atBot_zero hne
  have hlt : ∀ᶠ x : ℝ in atBot, groeneboomIntegrand t ω x / x^2 < 0 :=
    hratio.eventually_lt_const (by norm_num : (-1 : ℝ) < 0)
  filter_upwards [hlt, eventually_le_atBot (-1)] with x hx hxneg
  have hx0 : x ≠ 0 := by linarith
  have hsq : (0 : ℝ) < x^2 := sq_pos_of_ne_zero hx0
  have hneg : groeneboomIntegrand t ω x / x^2 * x^2 < 0 :=
    mul_neg_of_neg_of_pos hx hsq
  rwa [div_mul_cancel₀ _ (ne_of_gt hsq)] at hneg

/-- The boundary scale: on the good event there is an `M ≥ |t| + 1` beyond
which the integrand is negative. -/
lemma groeneboom_exists_neg_bound {ω : TwoSidedΩ} (hω : ω ∈ groeneboomGoodEvent) (t : ℝ) :
    ∃ M : ℝ, |t| + 1 ≤ M ∧ (∀ x : ℝ, M < x → groeneboomIntegrand t ω x < 0)
      ∧ (∀ x : ℝ, x < -M → groeneboomIntegrand t ω x < 0) := by
  obtain ⟨M1, hM1⟩ := eventually_atTop.mp (groeneboomIntegrand_neg_atTop hω t)
  obtain ⟨M2, hM2⟩ := eventually_atBot.mp (groeneboomIntegrand_neg_atBot hω t)
  refine ⟨max (max M1 (-M2)) (|t| + 1), le_max_right _ _, fun x hx ↦ hM1 x ?_, fun x hx ↦ hM2 x ?_⟩
  · exact le_of_lt (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
  · have h1 : -M2 ≤ max (max M1 (-M2)) (|t| + 1) :=
      le_trans (le_max_right M1 _) (le_max_left _ _)
    have h2 : x < M2 := lt_of_lt_of_le hx (by
      calc -max (max M1 (-M2)) (|t| + 1) ≤ -(-M2) := neg_le_neg h1
      _ = M2 := neg_neg M2)
    exact h2.le

/-- On the good event the integrand's range is bounded above (the integrand
is continuous and eventually negative at both ends). -/
lemma groeneboom_bddAbove {ω : TwoSidedΩ} (hω : ω ∈ groeneboomGoodEvent) (t : ℝ) :
    BddAbove (Set.range (groeneboomIntegrand t ω)) := by
  obtain ⟨M, hMt, hpos, hneg⟩ := groeneboom_exists_neg_bound hω t
  have hgcont : Continuous (groeneboomIntegrand t ω) :=
    continuous_groeneboomIntegrand hω.1.1.1 t
  have hM0 : 0 ≤ M := le_trans (by positivity) hMt
  refine ⟨max 0 (sSup (groeneboomIntegrand t ω '' Set.Icc (-M) M)), ?_⟩
  rintro y ⟨x, rfl⟩
  by_cases hx : x ∈ Set.Icc (-M) M
  · exact le_trans
      (le_csSup (IsCompact.bddAbove_image isCompact_Icc hgcont.continuousOn) ⟨x, hx, rfl⟩)
      (le_max_right _ _)
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · exact le_trans (hneg x h).le (le_max_left _ _)
    · exact le_trans (hpos x h).le (le_max_left _ _)

/-- On the good event the supremum is attained: the integrand is continuous,
tends to `−∞` at both ends, and equals `0` at `x = t`, so the superlevel set
`{g ≥ 0}` is compact and nonempty, and its maximizer maximizes globally. -/
lemma groeneboomU_attained {ω : TwoSidedΩ} (hω : ω ∈ groeneboomGoodEvent) (t : ℝ) :
    ∃ x : ℝ, groeneboomIntegrand t ω x = groeneboomU t ω := by
  obtain ⟨M, hMt, hpos, hneg⟩ := groeneboom_exists_neg_bound hω t
  have hgcont : Continuous (groeneboomIntegrand t ω) :=
    continuous_groeneboomIntegrand hω.1.1.1 t
  have hbdd := groeneboom_bddAbove hω t
  have htK : t ∈ (groeneboomIntegrand t ω) ⁻¹' Set.Ici 0 := by
    show (0 : ℝ) ≤ groeneboomIntegrand t ω t
    rw [groeneboomIntegrand_self]
  have hKcomp : IsCompact ((groeneboomIntegrand t ω) ⁻¹' Set.Ici 0) := by
    refine IsCompact.of_isClosed_subset (isCompact_Icc (a := -M) (b := M))
      (isClosed_Ici.preimage hgcont) ?_
    intro x hx
    by_contra hcon
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hcon
    have h0x : (0 : ℝ) ≤ groeneboomIntegrand t ω x := hx
    rcases hcon with h | h
    · exact absurd (lt_of_le_of_lt h0x (hneg x h)) (lt_irrefl 0)
    · exact absurd (lt_of_le_of_lt h0x (hpos x h)) (lt_irrefl 0)
  obtain ⟨x, hxK, hmax⟩ := hKcomp.exists_isMaxOn ⟨t, htK⟩ hgcont.continuousOn
  refine ⟨x, ?_⟩
  have hx0 : (0 : ℝ) ≤ groeneboomIntegrand t ω x := hxK
  show groeneboomIntegrand t ω x = sSup (Set.range (groeneboomIntegrand t ω))
  apply le_antisymm
  · exact le_csSup hbdd ⟨x, rfl⟩
  · apply csSup_le (Set.range_nonempty _)
    rintro y ⟨x', rfl⟩
    by_cases hx' : x' ∈ (groeneboomIntegrand t ω) ⁻¹' Set.Ici 0
    · exact isMaxOn_iff.mp hmax x' hx'
    · have hlt : groeneboomIntegrand t ω x' < 0 := by
        by_contra h
        exact hx' (not_lt.mp h)
      exact hlt.le.trans hx0

/-! ## Measurability via the rational supremum -/

/-- Supremum of a continuous function over ℝ equals the supremum over ℚ:
the bounded case is density, and the unbounded case is the common `sSup = 0`
convention for the reals. -/
lemma csSup_range_eq_csSup_ratCast_range {g : ℝ → ℝ} (hg : Continuous g) :
    sSup (Set.range g) = sSup (Set.range fun q : ℚ ↦ g (q : ℝ)) := by
  by_cases hbdd : BddAbove (Set.range g)
  · apply le_antisymm
    · apply csSup_le (Set.range_nonempty g)
      rintro y ⟨x, rfl⟩
      have hdense : x ∈ closure (Set.range (Rat.cast : ℚ → ℝ)) := by
        rw [Rat.denseRange_cast.closure_eq]
        exact Set.mem_univ x
      obtain ⟨a, ha, haT⟩ := mem_closure_iff_seq_limit.mp hdense
      choose q hq using ha
      have hT : Tendsto (fun n ↦ g (a n)) atTop (𝓝 (g x)) := (hg.tendsto x).comp haT
      refine le_of_tendsto' hT fun n ↦ le_csSup ?_ ?_
      · exact hbdd.mono (Set.range_comp_subset_range _ _)
      · exact ⟨q n, congrArg g (hq n)⟩
    · exact csSup_le_csSup hbdd (Set.range_nonempty _) (Set.range_comp_subset_range _ _)
  · have hT : ¬ BddAbove (Set.range fun q : ℚ ↦ g (q : ℝ)) := by
      intro hT
      obtain ⟨C, hC⟩ := hT
      apply hbdd
      refine ⟨C, ?_⟩
      rintro y ⟨x, rfl⟩
      have hdense : x ∈ closure (Set.range (Rat.cast : ℚ → ℝ)) := by
        rw [Rat.denseRange_cast.closure_eq]
        exact Set.mem_univ x
      obtain ⟨a, ha, haT⟩ := mem_closure_iff_seq_limit.mp hdense
      choose q hq using ha
      have hlim : Tendsto (fun n ↦ g (a n)) atTop (𝓝 (g x)) := (hg.tendsto x).comp haT
      refine le_of_tendsto' hlim fun n ↦ hC ?_
      exact ⟨q n, congrArg g (hq n)⟩
    rw [Real.sSup_of_not_bddAbove hbdd, Real.sSup_of_not_bddAbove hT]

/-- On a continuous path, the real and rational suprema agree. -/
lemma groeneboomSup_eq_supQ_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    groeneboomSup f = groeneboomSupQ f := by
  unfold groeneboomSup groeneboomSupQ
  exact csSup_range_eq_csSup_ratCast_range ((continuous_const.mul hf).sub (continuous_id.pow 2))

/-- The shifted-suprema presentation of `groeneboomU`: reindexing `x = y + t`. -/
lemma groeneboomU_eq_sup_shiftIncr (t : ℝ) (ω : TwoSidedΩ) :
    groeneboomU t ω = groeneboomSup (shiftIncr t ω) := by
  unfold groeneboomU groeneboomSup shiftIncr groeneboomIntegrand
  congr 1
  have hsurj : Set.range (fun x : ℝ ↦ x - t) = Set.univ :=
    Function.Surjective.range_eq (f := fun x : ℝ ↦ x - t) (fun y ↦ ⟨y + t, by ring⟩)
  have hcomp : ((fun y : ℝ ↦ Real.sqrt 2 * (twoSidedBM (y + t) ω - twoSidedBM t ω) - y^2)
      ∘ (fun x : ℝ ↦ x - t))
      = fun x : ℝ ↦ Real.sqrt 2 * (twoSidedBM x ω - twoSidedBM t ω) - (x - t)^2 := by
    funext x
    simp only [Function.comp_apply]
    ring_nf
  rw [← hcomp, Set.range_comp, hsurj, Set.image_univ]

/-- The shifted-increment path map is measurable. -/
lemma measurable_shiftIncr (t : ℝ) : Measurable (shiftIncr t) :=
  Measurable.of_eval fun _y ↦ (measurable_twoSidedBM _).sub (measurable_twoSidedBM _)

/-- The rational supremum is measurable in the path. -/
lemma measurable_groeneboomSupQ : Measurable groeneboomSupQ := by
  have h := Measurable.sSup (Set.countable_univ (α := ℚ))
    (f := fun (q : ℚ) (f : ℝ → ℝ) ↦ Real.sqrt 2 * f (q : ℝ) - (q : ℝ)^2)
    (fun q _ ↦ (measurable_const.mul (measurable_pi_apply (q : ℝ))).sub measurable_const)
  unfold groeneboomSupQ
  convert h using 1
  ext f
  rw [Set.image_univ]

/-- The composition is measurable. -/
lemma measurable_groeneboomSupQ_comp_shiftIncr (t : ℝ) :
    Measurable (fun ω ↦ groeneboomSupQ (shiftIncr t ω)) :=
  measurable_groeneboomSupQ.comp (measurable_shiftIncr t)

/-- On continuous paths, the rational supremum equals `groeneboomU t`. -/
lemma groeneboomU_ae_eq_supQ (t : ℝ) :
    (fun ω ↦ groeneboomSupQ (shiftIncr t ω)) =ᵐ[twoSidedBMMeasure] (groeneboomU t) := by
  filter_upwards [continuous_twoSidedBM] with ω hω
  rw [groeneboomU_eq_sup_shiftIncr]
  exact (groeneboomSup_eq_supQ_of_continuous
    ((hω.comp (continuous_add_const t)).sub continuous_const)).symm

/-- **Measurability of the Groeneboom supremum** (almost-everywhere form). -/
lemma aemeasurable_groeneboomU (t : ℝ) :
    AEMeasurable (groeneboomU t) twoSidedBMMeasure :=
  (measurable_groeneboomSupQ_comp_shiftIncr t).aemeasurable.congr
    (groeneboomU_ae_eq_supQ t)

/-! ## Stationarity -/

/-- The path map `ω ↦ (y ↦ twoSidedBM y ω)` is measurable. -/
lemma measurable_twoSidedBM_path : Measurable (fun ω y ↦ twoSidedBM y ω) :=
  Measurable.of_eval fun (y : ℝ) ↦ measurable_twoSidedBM y

/-- On the good event, the rational supremum of the path equals
`groeneboomU 0`. -/
lemma groeneboomSupQ_path_ae_eq :
    (fun ω ↦ groeneboomSupQ (twoSidedBM · ω)) =ᵐ[twoSidedBMMeasure] (groeneboomU 0) := by
  filter_upwards [continuous_twoSidedBM, twoSidedBM_zero] with ω hcont h0
  rw [groeneboomU_eq_sup_shiftIncr]
  show groeneboomSupQ (twoSidedBM · ω) = groeneboomSup (shiftIncr 0 ω)
  rw [← groeneboomSup_eq_supQ_of_continuous hcont]
  congr 1
  funext x
  simp only [shiftIncr, h0, sub_zero, add_zero]

/-- **Stationarity of the recentered Groeneboom process**: for every `t`, the
law of `groeneboomU t` under `twoSidedBMMeasure` equals the law of
`groeneboomU 0`. The proof reindexes `x = y + t` and uses the shift invariance
of the two-sided Brownian motion. -/
theorem groeneboom_stationary (t : ℝ) :
    twoSidedBMMeasure.map (groeneboomU t) = twoSidedBMMeasure.map (groeneboomU 0) := by
  calc twoSidedBMMeasure.map (groeneboomU t)
      = twoSidedBMMeasure.map (fun ω ↦ groeneboomSupQ (shiftIncr t ω)) := by
        exact Measure.map_congr (groeneboomU_ae_eq_supQ t).symm
    _ = (twoSidedBMMeasure.map (shiftIncr t)).map groeneboomSupQ :=
        (Measure.map_map measurable_groeneboomSupQ (measurable_shiftIncr t)).symm
    _ = (twoSidedBMMeasure.map (fun ω y ↦ twoSidedBM (y + t) ω - twoSidedBM t ω)).map
          groeneboomSupQ := by
        rw [show (shiftIncr t) = (fun ω y ↦ twoSidedBM (y + t) ω - twoSidedBM t ω) from rfl]
    _ = (twoSidedBMMeasure.map (fun ω y ↦ twoSidedBM y ω)).map groeneboomSupQ := by
        rw [map_twoSidedBM_shift_incr t]
    _ = twoSidedBMMeasure.map (fun ω ↦ groeneboomSupQ (twoSidedBM · ω)) :=
        Measure.map_map measurable_groeneboomSupQ measurable_twoSidedBM_path
    _ = twoSidedBMMeasure.map (groeneboomU 0) :=
        Measure.map_congr groeneboomSupQ_path_ae_eq

/-! ## Finite-dimensional stationarity -/

/-- Path-level time-shift of increments: `f ↦ (y ↦ f (y + t) − f t)`. Unlike
`shiftIncr`, which is specific to the Brownian path space `TwoSidedΩ`, this
acts on an arbitrary path `f : ℝ → ℝ` and is measurable for the cylinder
σ-algebra. -/
noncomputable def pathShift (t : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y ↦ f (y + t) - f t

/-- The Brownian shift map agrees with the path-level shift. -/
lemma shiftIncr_eq_pathShift (t : ℝ) (ω : TwoSidedΩ) :
    shiftIncr t ω = pathShift t (twoSidedBM · ω) :=
  rfl

/-- Iterated time-shifts compose: shifting by `t + s` is shifting by `s` and
then by `t`. -/
lemma pathShift_comp (t s : ℝ) (f : ℝ → ℝ) :
    pathShift (t + s) f = pathShift t (pathShift s f) := by
  funext y
  simp only [pathShift]
  rw [add_assoc y t s]
  ring

/-- Shift of shifted increments, at the Brownian level:
`shiftIncr (t + s) ω = pathShift t (shiftIncr s ω)`. -/
lemma shiftIncr_add (t s : ℝ) (ω : TwoSidedΩ) :
    shiftIncr (t + s) ω = pathShift t (shiftIncr s ω) := by
  funext y
  simp only [shiftIncr, pathShift]
  rw [add_assoc y t s]
  ring

/-- The measurable vector of rational suprema of shifted increments:
`f ↦ (i ↦ groeneboomSupQ (pathShift (t i) f))`. -/
noncomputable def groeneboomShiftVec {k : ℕ} (t : Fin k → ℝ) (f : ℝ → ℝ) :
    Fin k → ℝ :=
  fun i ↦ groeneboomSupQ (pathShift (t i) f)

/-- The path-level shift is measurable. -/
lemma measurable_pathShift (t : ℝ) : Measurable (pathShift t) :=
  Measurable.of_eval fun y ↦ (measurable_pi_apply (y + t)).sub (measurable_pi_apply t)

/-- The shifted-supremum vector is measurable. -/
lemma measurable_groeneboomShiftVec {k : ℕ} (t : Fin k → ℝ) :
    Measurable (groeneboomShiftVec t) :=
  Measurable.of_eval fun i ↦
    measurable_groeneboomSupQ.comp (measurable_pathShift (t i))

/-- **Finite-dimensional stationarity of the recentered Groeneboom process**:
for `k : ℕ`, `t : Fin k → ℝ`, and shift `s : ℝ`, the laws of the vectors
`(groeneboomU (t i + s))ᵢ` and `(groeneboomU (t i))ᵢ` on `Fin k → ℝ` coincide.
The proof bridges componentwise to the measurable rational suprema, rewrites
`shiftIncr (t i + s) ω = pathShift (t i) (shiftIncr s ω)` (shift of shifted
increments), and consumes the path-space shift invariance
`map_twoSidedBM_shift_incr`. The case `k = 1` recovers
`groeneboom_stationary` (the one-dimensional version). -/
theorem groeneboom_stationary_fdd {k : ℕ} (t : Fin k → ℝ) (s : ℝ) :
    twoSidedBMMeasure.map (fun ω i ↦ groeneboomU (t i + s) ω)
      = twoSidedBMMeasure.map (fun ω i ↦ groeneboomU (t i) ω) := by
  calc twoSidedBMMeasure.map (fun ω i ↦ groeneboomU (t i + s) ω)
      = twoSidedBMMeasure.map ((groeneboomShiftVec t) ∘ (shiftIncr s)) := by
        refine Measure.map_congr ?_
        filter_upwards [ae_all_iff.mpr fun i ↦ groeneboomU_ae_eq_supQ (t i + s)]
          with ω hω
        funext i
        show groeneboomU (t i + s) ω = ((groeneboomShiftVec t) ∘ (shiftIncr s)) ω i
        rw [← hω i]
        exact congrArg groeneboomSupQ (shiftIncr_add (t i) s ω)
    _ = (twoSidedBMMeasure.map (shiftIncr s)).map (groeneboomShiftVec t) :=
        (Measure.map_map (measurable_groeneboomShiftVec t)
          (measurable_shiftIncr s)).symm
    _ = (twoSidedBMMeasure.map (fun ω y ↦ twoSidedBM (y + s) ω - twoSidedBM s ω)).map
          (groeneboomShiftVec t) := by
        rw [show (shiftIncr s) = (fun ω y ↦ twoSidedBM (y + s) ω - twoSidedBM s ω)
          from rfl]
    _ = (twoSidedBMMeasure.map (fun ω y ↦ twoSidedBM y ω)).map (groeneboomShiftVec t) := by
        rw [map_twoSidedBM_shift_incr s]
    _ = twoSidedBMMeasure.map ((groeneboomShiftVec t) ∘ (fun ω y ↦ twoSidedBM y ω)) :=
        Measure.map_map (measurable_groeneboomShiftVec t) measurable_twoSidedBM_path
    _ = twoSidedBMMeasure.map (fun ω i ↦ groeneboomSupQ (shiftIncr (t i) ω)) := by
        refine Measure.map_congr ?_
        filter_upwards with ω
        funext i
        show ((groeneboomShiftVec t) ∘ (fun ω y ↦ twoSidedBM y ω)) ω i
          = groeneboomSupQ (shiftIncr (t i) ω)
        exact congrArg groeneboomSupQ (shiftIncr_eq_pathShift (t i) ω).symm
    _ = twoSidedBMMeasure.map (fun ω i ↦ groeneboomU (t i) ω) := by
        refine Measure.map_congr ?_
        filter_upwards [ae_all_iff.mpr fun i ↦ groeneboomU_ae_eq_supQ (t i)] with ω hω
        funext i
        exact hω i

/-- **Finite-dimensional stationarity at the measurable-supremum level**: the
same statement as `groeneboom_stationary_fdd` for the measurable rational
suprema, proved by the algebraic core of that proof (shift of shifted
increments plus path-space shift invariance). -/
lemma groeneboomSupQ_stationary_fdd {k : ℕ} (t : Fin k → ℝ) (s : ℝ) :
    twoSidedBMMeasure.map (fun ω i ↦ groeneboomSupQ (shiftIncr (t i + s) ω))
      = twoSidedBMMeasure.map (fun ω i ↦ groeneboomSupQ (shiftIncr (t i) ω)) := by
  calc twoSidedBMMeasure.map (fun ω i ↦ groeneboomSupQ (shiftIncr (t i + s) ω))
      = twoSidedBMMeasure.map ((groeneboomShiftVec t) ∘ (shiftIncr s)) := by
        refine Measure.map_congr ?_
        filter_upwards with ω
        funext i
        show groeneboomSupQ (shiftIncr (t i + s) ω) = ((groeneboomShiftVec t) ∘ (shiftIncr s)) ω i
        exact congrArg groeneboomSupQ (shiftIncr_add (t i) s ω)
    _ = (twoSidedBMMeasure.map (shiftIncr s)).map (groeneboomShiftVec t) :=
        (Measure.map_map (measurable_groeneboomShiftVec t)
          (measurable_shiftIncr s)).symm
    _ = (twoSidedBMMeasure.map (fun ω y ↦ twoSidedBM (y + s) ω - twoSidedBM s ω)).map
          (groeneboomShiftVec t) := by
        rw [show (shiftIncr s) = (fun ω y ↦ twoSidedBM (y + s) ω - twoSidedBM s ω)
          from rfl]
    _ = (twoSidedBMMeasure.map (fun ω y ↦ twoSidedBM y ω)).map (groeneboomShiftVec t) := by
        rw [map_twoSidedBM_shift_incr s]
    _ = twoSidedBMMeasure.map ((groeneboomShiftVec t) ∘ (fun ω y ↦ twoSidedBM y ω)) :=
        Measure.map_map (measurable_groeneboomShiftVec t) measurable_twoSidedBM_path
    _ = twoSidedBMMeasure.map (fun ω i ↦ groeneboomSupQ (shiftIncr (t i) ω)) := by
        refine Measure.map_congr ?_
        filter_upwards with ω
        funext i
        show ((groeneboomShiftVec t) ∘ (fun ω y ↦ twoSidedBM y ω)) ω i
          = groeneboomSupQ (shiftIncr (t i) ω)
        exact congrArg groeneboomSupQ (shiftIncr_eq_pathShift (t i) ω).symm

/-- **Two-time stationarity of the recentered Groeneboom process**: for
`t₁, t₂, s : ℝ`, the joint law of `(groeneboomU (t₁ + s), groeneboomU (t₂ + s))`
on `ℝ × ℝ` equals that of `(groeneboomU t₁, groeneboomU t₂)`. This is the
`k = 2` instance of `groeneboom_stationary_fdd`, transported across the
`Fin 2 → ℝ ≃ᵐ ℝ × ℝ` measurable equivalence. -/
theorem groeneboom_stationary_pair (t₁ t₂ s : ℝ) :
    twoSidedBMMeasure.map (fun ω ↦ (groeneboomU (t₁ + s) ω, groeneboomU (t₂ + s) ω))
      = twoSidedBMMeasure.map (fun ω ↦ (groeneboomU t₁ ω, groeneboomU t₂ ω)) := by
  have hfdd := groeneboomSupQ_stationary_fdd (![t₁, t₂]) s
  have hbridge : ∀ (a b : ℝ),
      (fun ω ↦ (groeneboomSupQ (shiftIncr a ω), groeneboomSupQ (shiftIncr b ω)))
        =ᵐ[twoSidedBMMeasure] (fun ω ↦ (groeneboomU a ω, groeneboomU b ω)) := by
    intro a b
    filter_upwards [groeneboomU_ae_eq_supQ a, groeneboomU_ae_eq_supQ b] with ω h1 h2
    exact Prod.ext h1 h2
  have hconv : ∀ (u v : ℝ), ∀ ω : TwoSidedΩ,
      (groeneboomSupQ (shiftIncr (u + s) ω), groeneboomSupQ (shiftIncr (v + s) ω))
        = (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ))
            (fun i ↦ groeneboomSupQ (shiftIncr ((![u, v] i) + s) ω)) := by
    intro u v ω
    apply Prod.ext
    · show groeneboomSupQ (shiftIncr (u + s) ω)
        = groeneboomSupQ (shiftIncr ((![u, v] 0) + s) ω)
      simp
    · show groeneboomSupQ (shiftIncr (v + s) ω)
        = groeneboomSupQ (shiftIncr ((![u, v] 1) + s) ω)
      simp
  have hconv' : ∀ (u v : ℝ), ∀ ω : TwoSidedΩ,
      (groeneboomSupQ (shiftIncr u ω), groeneboomSupQ (shiftIncr v ω))
        = (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ))
            (fun i ↦ groeneboomSupQ (shiftIncr ((![u, v] i)) ω)) := by
    intro u v ω
    apply Prod.ext
    · show groeneboomSupQ (shiftIncr u ω) = groeneboomSupQ (shiftIncr (![u, v] 0) ω)
      simp
    · show groeneboomSupQ (shiftIncr v ω) = groeneboomSupQ (shiftIncr (![u, v] 1) ω)
      simp
  have hmeas : ∀ u v : ℝ, Measurable
      (fun ω i ↦ groeneboomSupQ (shiftIncr ((![u, v] i) + s) ω)) := by
    intro u v
    exact Measurable.of_eval fun i ↦
      measurable_groeneboomSupQ_comp_shiftIncr ((![u, v] i) + s)
  have hmeas' : ∀ u v : ℝ, Measurable
      (fun ω i ↦ groeneboomSupQ (shiftIncr ((![u, v] i)) ω)) := by
    intro u v
    exact Measurable.of_eval fun i ↦
      measurable_groeneboomSupQ_comp_shiftIncr ((![u, v] i))
  calc twoSidedBMMeasure.map (fun ω ↦ (groeneboomU (t₁ + s) ω, groeneboomU (t₂ + s) ω))
      = twoSidedBMMeasure.map
          (fun ω ↦ (groeneboomSupQ (shiftIncr (t₁ + s) ω), groeneboomSupQ (shiftIncr (t₂ + s) ω))) :=
        Measure.map_congr (hbridge (t₁ + s) (t₂ + s)).symm
    _ = (twoSidedBMMeasure.map (fun ω i ↦ groeneboomSupQ (shiftIncr ((![t₁, t₂] i) + s) ω))).map
          (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)) := by
        rw [show (fun ω ↦ (groeneboomSupQ (shiftIncr (t₁ + s) ω), groeneboomSupQ (shiftIncr (t₂ + s) ω)))
            = (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)) ∘
              (fun ω i ↦ groeneboomSupQ (shiftIncr ((![t₁, t₂] i) + s) ω))
            from funext fun ω ↦ hconv t₁ t₂ ω]
        exact (Measure.map_map (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).measurable
          (hmeas t₁ t₂)).symm
    _ = (twoSidedBMMeasure.map (fun ω i ↦ groeneboomSupQ (shiftIncr ((![t₁, t₂] i)) ω))).map
          (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)) := by
        rw [hfdd]
    _ = twoSidedBMMeasure.map
          (fun ω ↦ (groeneboomSupQ (shiftIncr t₁ ω), groeneboomSupQ (shiftIncr t₂ ω))) := by
        rw [Measure.map_map (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).measurable
          (hmeas' t₁ t₂)]
        refine Measure.map_congr ?_
        filter_upwards with ω
        exact hconv' t₁ t₂ ω
    _ = twoSidedBMMeasure.map (fun ω ↦ (groeneboomU t₁ ω, groeneboomU t₂ ω)) :=
        Measure.map_congr (hbridge t₁ t₂)

/-! ## Path regularity: a.s. continuity of the Groeneboom process -/

/-- The finite supremum of `|B|` over a compact interval, on continuous
paths. -/
noncomputable def groeneboomAbsSup (ω : TwoSidedΩ) (T : ℝ) : ℝ :=
  sSup ((fun s ↦ |twoSidedBM s ω|) '' Set.Icc (-T) T)

/-- The image is bounded above (compactness). -/
lemma groeneboomAbsSup_bddAbove {ω : TwoSidedΩ} (hcont : Continuous (twoSidedBM · ω)) (T : ℝ) :
    BddAbove ((fun s ↦ |twoSidedBM s ω|) '' Set.Icc (-T) T) :=
  IsCompact.bddAbove_image isCompact_Icc ((hcont.abs).continuousOn)

/-- The supremum is nonnegative (the interval contains `0`, and `|B 0| = 0` a.s. on the good event — in general any value of the image is nonnegative). -/
lemma groeneboomAbsSup_nonneg {ω : TwoSidedΩ} (hcont : Continuous (twoSidedBM · ω))
    {T : ℝ} (hT : 0 ≤ T) : 0 ≤ groeneboomAbsSup ω T := by
  refine le_trans (abs_nonneg (twoSidedBM 0 ω))
    (le_csSup (groeneboomAbsSup_bddAbove hcont T) ?_)
  exact ⟨0, Set.mem_Icc.mpr ⟨by linarith, hT⟩, rfl⟩

/-- **Uniform-in-t majorant**: on the good event, for `t ∈ Icc (-T) T` and
`|x| ≥ T`, the integrand is dominated by a `t`-free majorant. -/
lemma groeneboomIntegrand_le_majorant {ω : TwoSidedΩ} (hω : ω ∈ groeneboomGoodEvent)
    {T : ℝ} (_hT : 0 < T) {t x : ℝ} (ht : t ∈ Set.Icc (-T) T) (hx : T ≤ |x|) :
    groeneboomIntegrand t ω x
      ≤ Real.sqrt 2 * twoSidedBM x ω + Real.sqrt 2 * groeneboomAbsSup ω T - (|x| - T)^2 := by
  have hcont := hω.1.1.1
  have habs : |twoSidedBM t ω| ≤ groeneboomAbsSup ω T :=
    le_csSup (groeneboomAbsSup_bddAbove hcont T) ⟨t, ht, rfl⟩
  have htT : |t| ≤ T := abs_le.mpr ht
  have hpen : (|x| - T)^2 ≤ (x - t)^2 := by
    have h1 : |x| - |t| ≤ |x - t| := abs_sub_abs_le_abs_sub x t
    have h2 : 0 ≤ |x| - T := by linarith
    have h3 : |x| - T ≤ |x - t| := by linarith
    calc (|x| - T)^2 ≤ |x - t|^2 := (sq_le_sq₀ h2 (abs_nonneg (x - t))).mpr h3
    _ = (x - t)^2 := sq_abs (x - t)
  have h2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold groeneboomIntegrand
  have h1 : Real.sqrt 2 * (twoSidedBM x ω - twoSidedBM t ω)
      ≤ Real.sqrt 2 * (twoSidedBM x ω + |twoSidedBM t ω|) :=
    mul_le_mul_of_nonneg_left (by linarith [neg_abs_le (twoSidedBM t ω)]) h2nn
  have h2 : Real.sqrt 2 * (twoSidedBM x ω + |twoSidedBM t ω|)
      ≤ Real.sqrt 2 * (twoSidedBM x ω + groeneboomAbsSup ω T) :=
    mul_le_mul_of_nonneg_left (by linarith) h2nn
  have h3 : -((x - t)^2) ≤ -((|x| - T)^2) := neg_le_neg hpen
  calc Real.sqrt 2 * (twoSidedBM x ω - twoSidedBM t ω) - (x - t)^2
      ≤ Real.sqrt 2 * (twoSidedBM x ω + groeneboomAbsSup ω T) - (x - t)^2 := by linarith
    _ ≤ Real.sqrt 2 * (twoSidedBM x ω + groeneboomAbsSup ω T) - (|x| - T)^2 := by linarith
    _ = Real.sqrt 2 * twoSidedBM x ω + Real.sqrt 2 * groeneboomAbsSup ω T - (|x| - T)^2 := by
        rw [mul_add]

/-- The majorant is eventually negative at `+∞` (the ratio `H(x)/x² → −1`). -/
lemma groeneboom_majorant_neg_atTop {ω : TwoSidedΩ}
    (hgrowth : Tendsto (fun x ↦ twoSidedBM x ω / x) atTop (𝓝 0))
    (T C : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt 2 * twoSidedBM x ω + Real.sqrt 2 * C - (|x| - T)^2 < 0 := by
  -- the ratio to −1, on the eventual region `|x| = x`
  have h1 : Tendsto (fun x ↦ Real.sqrt 2 * (twoSidedBM x ω / x * x⁻¹)) atTop (𝓝 (√2 * (0 * 0))) :=
    (hgrowth.mul tendsto_inv_atTop_zero).const_mul (Real.sqrt 2)
  have h2 : Tendsto (fun x ↦ Real.sqrt 2 * (C * (x^2)⁻¹)) atTop (𝓝 (√2 * (C * 0))) := by
    have hmul : Tendsto (fun x : ℝ ↦ x⁻¹ * x⁻¹) atTop (𝓝 (0 * 0)) :=
      tendsto_inv_atTop_zero.mul tendsto_inv_atTop_zero
    rw [mul_zero] at hmul
    have hcast : Tendsto (fun x : ℝ ↦ (x^2)⁻¹) atTop (𝓝 0) := by
      refine hmul.congr' ?_
      filter_upwards with x
      rw [pow_two, mul_inv_rev]
    exact (hcast.const_mul C).const_mul (Real.sqrt 2)
  have h3 : Tendsto (fun x ↦ (1 - T * x⁻¹)^2) atTop (𝓝 1) := by
    have hmul : Tendsto (fun x ↦ T * x⁻¹) atTop (𝓝 (T * 0)) :=
      tendsto_inv_atTop_zero.const_mul T
    rw [mul_zero] at hmul
    have hsub : Tendsto (fun x : ℝ ↦ (1 : ℝ) - T * x⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hmul
    have hpow := hsub.pow 2
    rwa [sub_zero, one_pow] at hpow
  have h := (h1.add h2).sub h3
  simp only [mul_zero, zero_add, zero_sub] at h
  have hlt : ∀ᶠ x : ℝ in atTop,
      (Real.sqrt 2 * (twoSidedBM x ω / x * x⁻¹) + Real.sqrt 2 * (C * (x^2)⁻¹) - (1 - T * x⁻¹)^2)
        < 0 := h.eventually_lt_const (by norm_num : (-1 : ℝ) < 0)
  filter_upwards [hlt, eventually_gt_atTop 0] with x hx hxpos
  have hsq : (0 : ℝ) < x^2 := sq_pos_of_pos hxpos
  have hmul := mul_neg_of_neg_of_pos hx hsq
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have p1 : √2 * (twoSidedBM x ω / x * x⁻¹) * x^2 = √2 * twoSidedBM x ω := by
    rw [show √2 * (twoSidedBM x ω / x * x⁻¹) * x^2 = √2 * (twoSidedBM x ω / x) * (x⁻¹ * x^2)
        from by ring]
    rw [show x⁻¹ * x^2 = x from by field_simp]
    rw [mul_assoc, div_mul_cancel₀ _ hx0]
  have p2 : √2 * (C * (x^2)⁻¹) * x^2 = √2 * C := by
    rw [show √2 * (C * (x^2)⁻¹) * x^2 = √2 * C * ((x^2)⁻¹ * x^2) from by ring]
    rw [inv_mul_cancel₀ (pow_ne_zero 2 hx0), mul_one]
  have p3 : (1 - T * x⁻¹)^2 * x^2 = (x - T)^2 := by
    rw [← mul_pow, show (1 - T * x⁻¹) * x = x - T from by field_simp]
  have hident : (√2 * (twoSidedBM x ω / x * x⁻¹) + √2 * (C * (x^2)⁻¹) - (1 - T * x⁻¹)^2) * x^2
      = Real.sqrt 2 * twoSidedBM x ω + Real.sqrt 2 * C - (x - T)^2 := by
    rw [sub_mul, add_mul, p1, p2, p3]
  rw [hident] at hmul
  rwa [abs_of_nonneg hxpos.le]

/-- The majorant is eventually negative at `−∞` (same ratio argument on the
region `|x| = −x`). -/
lemma groeneboom_majorant_neg_atBot {ω : TwoSidedΩ}
    (hgrowth : Tendsto (fun x ↦ twoSidedBM x ω / x) atBot (𝓝 0))
    (T C : ℝ) :
    ∀ᶠ x : ℝ in atBot, Real.sqrt 2 * twoSidedBM x ω + Real.sqrt 2 * C - (|x| - T)^2 < 0 := by
  have h1 : Tendsto (fun x ↦ Real.sqrt 2 * (twoSidedBM x ω / x * x⁻¹)) atBot (𝓝 (√2 * (0 * 0))) :=
    (hgrowth.mul tendsto_inv_atBot_zero).const_mul (Real.sqrt 2)
  have h2 : Tendsto (fun x ↦ Real.sqrt 2 * (C * (x^2)⁻¹)) atBot (𝓝 (√2 * (C * 0))) := by
    have hmul : Tendsto (fun x : ℝ ↦ x⁻¹ * x⁻¹) atBot (𝓝 (0 * 0)) :=
      tendsto_inv_atBot_zero.mul tendsto_inv_atBot_zero
    rw [mul_zero] at hmul
    have hcast : Tendsto (fun x : ℝ ↦ (x^2)⁻¹) atBot (𝓝 0) := by
      refine hmul.congr' ?_
      filter_upwards with x
      rw [pow_two, mul_inv_rev]
    exact (hcast.const_mul C).const_mul (Real.sqrt 2)
  have h3 : Tendsto (fun x ↦ (-1 - T * x⁻¹)^2) atBot (𝓝 1) := by
    have hmul : Tendsto (fun x ↦ T * x⁻¹) atBot (𝓝 (T * 0)) :=
      tendsto_inv_atBot_zero.const_mul T
    rw [mul_zero] at hmul
    have hsub : Tendsto (fun x : ℝ ↦ (-1 : ℝ) - T * x⁻¹) atBot (𝓝 (-1 - 0)) :=
      tendsto_const_nhds.sub hmul
    have hpow := hsub.pow 2
    rwa [sub_zero, show ((-1 : ℝ)^2) = 1 from by norm_num] at hpow
  have h := (h1.add h2).sub h3
  simp only [mul_zero, zero_add, zero_sub] at h
  have hlt : ∀ᶠ x : ℝ in atBot,
      (Real.sqrt 2 * (twoSidedBM x ω / x * x⁻¹) + Real.sqrt 2 * (C * (x^2)⁻¹) - (-1 - T * x⁻¹)^2)
        < 0 := h.eventually_lt_const (by norm_num : (-1 : ℝ) < 0)
  filter_upwards [hlt, eventually_lt_atBot 0] with x hx hxneg
  have hsq : (0 : ℝ) < x^2 := sq_pos_of_neg hxneg
  have hmul := mul_neg_of_neg_of_pos hx hsq
  have hx0 : x ≠ 0 := ne_of_lt hxneg
  have p1 : √2 * (twoSidedBM x ω / x * x⁻¹) * x^2 = √2 * twoSidedBM x ω := by
    rw [show √2 * (twoSidedBM x ω / x * x⁻¹) * x^2 = √2 * (twoSidedBM x ω / x) * (x⁻¹ * x^2)
        from by ring]
    rw [show x⁻¹ * x^2 = x from by field_simp]
    rw [mul_assoc, div_mul_cancel₀ _ hx0]
  have p2 : √2 * (C * (x^2)⁻¹) * x^2 = √2 * C := by
    rw [show √2 * (C * (x^2)⁻¹) * x^2 = √2 * C * ((x^2)⁻¹ * x^2) from by ring]
    rw [inv_mul_cancel₀ (pow_ne_zero 2 hx0), mul_one]
  have p3 : (-1 - T * x⁻¹)^2 * x^2 = (-x - T)^2 := by
    rw [← mul_pow, show (-1 - T * x⁻¹) * x = -x - T from by field_simp]
  have hident : (√2 * (twoSidedBM x ω / x * x⁻¹) + √2 * (C * (x^2)⁻¹) - (-1 - T * x⁻¹)^2) * x^2
      = Real.sqrt 2 * twoSidedBM x ω + Real.sqrt 2 * C - (-x - T)^2 := by
    rw [sub_mul, add_mul, p1, p2, p3]
  rw [hident] at hmul
  rwa [abs_of_nonpos hxneg.le]

/-- **Uniform-in-t negativity scale**: on the good event, for `T > 0` there is
an `M ≥ T + 1` such that for every `t ∈ Icc (-T) T` and every `x` with
`|x| > M`, the integrand is negative. -/
lemma groeneboom_neg_bound_uniform {ω : TwoSidedΩ} (hω : ω ∈ groeneboomGoodEvent)
    {T : ℝ} (hT : 0 < T) :
    ∃ M : ℝ, T + 1 ≤ M ∧ ∀ t ∈ Set.Icc (-T) T, ∀ x : ℝ, M < |x| →
      groeneboomIntegrand t ω x < 0 := by
  have htop := hω.1.1.2
  have hbot := hω.1.2
  obtain ⟨M1, hM1⟩ := eventually_atTop.mp
    (groeneboom_majorant_neg_atTop htop T (groeneboomAbsSup ω T))
  obtain ⟨M2, hM2⟩ := eventually_atBot.mp
    (groeneboom_majorant_neg_atBot hbot T (groeneboomAbsSup ω T))
  refine ⟨max (max M1 (-M2)) (T + 1), le_max_right _ _, fun t ht x hx ↦ ?_⟩
  have hxT : T ≤ |x| :=
    le_trans (by linarith) (le_trans (le_max_right (max M1 (-M2)) (T + 1)) (le_of_lt hx))
  have hle := groeneboomIntegrand_le_majorant hω hT ht hxT
  rcases le_total 0 x with h0x | h0x
  · -- `x ≥ 0`, so `x > M ≥ M1`
    have hM1x : max (max M1 (-M2)) (T + 1) < x := by rwa [abs_of_nonneg h0x] at hx
    have hx1 : M1 ≤ x :=
      le_of_lt (lt_of_le_of_lt (le_trans (le_max_left M1 _) (le_max_left _ _)) hM1x)
    exact hle.trans_lt (hM1 x hx1)
  · -- `x ≤ 0`, so `x < −M ≤ M2`
    have hxM : x < -max (max M1 (-M2)) (T + 1) := by
      rw [abs_of_nonpos h0x] at hx
      linarith
    have h1 : -M2 ≤ max (max M1 (-M2)) (T + 1) := le_trans (le_max_right M1 _) (le_max_left _ _)
    have hx2 : x ≤ M2 := le_of_lt (lt_of_lt_of_le hxM (by
      calc -max (max M1 (-M2)) (T + 1) ≤ -(-M2) := neg_le_neg h1
      _ = M2 := neg_neg M2))
    exact hle.trans_lt (hM2 x hx2)

/-- The supremum of the integrand over the compact window `Icc (-M) M`. -/
noncomputable def groeneboomCompactSup (ω : TwoSidedΩ) (M : ℝ) (t : ℝ) : ℝ :=
  sSup ((groeneboomIntegrand t ω) '' Set.Icc (-M) M)

/-- **Localization**: on the good event with the uniform negativity scale `M`,
for `t ∈ Icc (-T) T` the global supremum equals the compact-window supremum
(since the integrand is negative outside the window and vanishes at `x = t`). -/
lemma groeneboomU_eq_compactSup {ω : TwoSidedΩ} (hω : ω ∈ groeneboomGoodEvent)
    {T M : ℝ} (hTM : T + 1 ≤ M)
    (hneg : ∀ t ∈ Set.Icc (-T) T, ∀ x : ℝ, M < |x| → groeneboomIntegrand t ω x < 0)
    {t : ℝ} (ht : t ∈ Set.Icc (-T) T) :
    groeneboomU t ω = groeneboomCompactSup ω M t := by
  have hbdd := groeneboom_bddAbove hω t
  have hcont : Continuous (groeneboomIntegrand t ω) := continuous_groeneboomIntegrand hω.1.1.1 t
  have himg : BddAbove ((groeneboomIntegrand t ω) '' Set.Icc (-M) M) :=
    IsCompact.bddAbove_image isCompact_Icc hcont.continuousOn
  have htT : |t| ≤ T := abs_le.mpr ht
  have hT0 : 0 ≤ T := by have h1 := ht.1; have h2 := ht.2; linarith
  have hM0 : 0 ≤ M := by linarith
  have htM : t ∈ Set.Icc (-M) M := by
    have h1 := abs_le.mp htT
    rw [Set.mem_Icc]
    constructor <;> linarith
  have h0in : (0:ℝ) ∈ (groeneboomIntegrand t ω) '' Set.Icc (-M) M :=
    ⟨t, htM, groeneboomIntegrand_self t ω⟩
  have h0le : (0:ℝ) ≤ groeneboomCompactSup ω M t := le_csSup himg h0in
  show sSup (Set.range (groeneboomIntegrand t ω)) = groeneboomCompactSup ω M t
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro y ⟨x, rfl⟩
    by_cases hx : x ∈ Set.Icc (-M) M
    · exact le_csSup himg ⟨x, hx, rfl⟩
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      have hxM : M < |x| := by
        rcases hx with h | h
        · rw [abs_of_nonpos (by linarith : x ≤ 0)]
          linarith
        · rw [abs_of_nonneg (by linarith : 0 ≤ x)]
          exact h
      exact le_trans (hneg t ht x hxM).le h0le
  · exact csSup_le_csSup hbdd ((Set.nonempty_Icc.mpr (by linarith : -M ≤ M)).image _) (Set.image_subset_range _ _)

/-- Pointwise difference bound of the integrand in `t`, uniform over the
compact window. -/
lemma groeneboomIntegrand_sub_le (ω : TwoSidedΩ) {M : ℝ} (_hM : 0 ≤ M) (t t' x : ℝ)
    (hx : x ∈ Set.Icc (-M) M) :
    |groeneboomIntegrand t ω x - groeneboomIntegrand t' ω x|
      ≤ Real.sqrt 2 * |twoSidedBM t ω - twoSidedBM t' ω| + |t' - t| * (2 * M + |t| + |t'|) := by
  have hxM : |x| ≤ M := abs_le.mpr hx
  have h2 : (x - t)^2 - (x - t')^2 = (t' - t) * (2 * x - t - t') := by ring
  have h4 : |2 * x - t - t'| ≤ 2 * M + |t| + |t'| := by
    have h5 : |2 * x| = 2 * |x| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc |2 * x - t - t'| = |2 * x - (t + t')| := by ring_nf
    _ ≤ |2 * x| + |t + t'| := abs_sub _ _
    _ ≤ 2 * |x| + (|t| + |t'|) := by
        rw [h5]
        gcongr
        exact abs_add_le t t'
    _ ≤ 2 * M + |t| + |t'| := by linarith
  have h3 : |(x - t)^2 - (x - t')^2| ≤ |t' - t| * (2 * M + |t| + |t'|) := by
    rw [h2, abs_mul]
    exact mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
  have h6 : |Real.sqrt 2 * (twoSidedBM t ω - twoSidedBM t' ω)|
      = Real.sqrt 2 * |twoSidedBM t ω - twoSidedBM t' ω| := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  have h1 : groeneboomIntegrand t ω x - groeneboomIntegrand t' ω x
      = -(Real.sqrt 2 * (twoSidedBM t ω - twoSidedBM t' ω) + ((x - t)^2 - (x - t')^2)) := by
    unfold groeneboomIntegrand
    ring
  rw [h1, abs_neg]
  calc |Real.sqrt 2 * (twoSidedBM t ω - twoSidedBM t' ω) + ((x - t)^2 - (x - t')^2)|
      ≤ |Real.sqrt 2 * (twoSidedBM t ω - twoSidedBM t' ω)| + |(x - t)^2 - (x - t')^2| :=
        abs_add_le _ _
    _ = Real.sqrt 2 * |twoSidedBM t ω - twoSidedBM t' ω| + |(x - t)^2 - (x - t')^2| := by rw [h6]
    _ ≤ Real.sqrt 2 * |twoSidedBM t ω - twoSidedBM t' ω| + |t' - t| * (2 * M + |t| + |t'|) := by
        gcongr

/-- The compact-window supremum is attained (nonempty compact, continuous
integrand). -/
lemma groeneboomCompactSup_attained (ω : TwoSidedΩ) (hcont : Continuous (twoSidedBM · ω))
    {M : ℝ} (hM : 0 ≤ M) (t : ℝ) :
    ∃ x : ℝ, x ∈ Set.Icc (-M) M ∧ IsMaxOn (groeneboomIntegrand t ω) (Set.Icc (-M) M) x
      ∧ groeneboomIntegrand t ω x = groeneboomCompactSup ω M t := by
  have hg : Continuous (groeneboomIntegrand t ω) := continuous_groeneboomIntegrand hcont t
  obtain ⟨x, hx, hmax⟩ := IsCompact.exists_isMaxOn isCompact_Icc
    (Set.nonempty_Icc.mpr (by linarith : -M ≤ M)) hg.continuousOn
  refine ⟨x, hx, hmax, ?_⟩
  have himg : BddAbove ((groeneboomIntegrand t ω) '' Set.Icc (-M) M) :=
    IsCompact.bddAbove_image isCompact_Icc hg.continuousOn
  have hmax' := isMaxOn_iff.mp hmax
  show groeneboomIntegrand t ω x = sSup ((groeneboomIntegrand t ω) '' Set.Icc (-M) M)
  apply le_antisymm
  · exact le_csSup himg ⟨x, hx, rfl⟩
  · apply csSup_le ((Set.nonempty_Icc.mpr (by linarith : -M ≤ M)).image _)
    rintro y ⟨x', hx', rfl⟩
    exact hmax' x' hx'

/-- The sup-difference bound over the common compact window. -/
lemma groeneboomCompactSup_sub_le (ω : TwoSidedΩ) (hcont : Continuous (twoSidedBM · ω))
    {M : ℝ} (hM : 0 ≤ M) (t t' : ℝ) :
    |groeneboomCompactSup ω M t - groeneboomCompactSup ω M t'|
      ≤ Real.sqrt 2 * |twoSidedBM t ω - twoSidedBM t' ω| + |t' - t| * (2 * M + |t| + |t'|) := by
  obtain ⟨x₀, hx₀, hmax₀, hval₀⟩ := groeneboomCompactSup_attained ω hcont hM t
  obtain ⟨x₁, hx₁, hmax₁, hval₁⟩ := groeneboomCompactSup_attained ω hcont hM t'
  have hpt := groeneboomIntegrand_sub_le ω hM t t'
  have hmax₀' := isMaxOn_iff.mp hmax₀
  have hmax₁' := isMaxOn_iff.mp hmax₁
  have hside : groeneboomCompactSup ω M t - groeneboomCompactSup ω M t'
      ≤ Real.sqrt 2 * |twoSidedBM t ω - twoSidedBM t' ω| + |t' - t| * (2 * M + |t| + |t'|) := by
    rw [← hval₀, ← hval₁]
    calc groeneboomIntegrand t ω x₀ - groeneboomIntegrand t' ω x₁
        ≤ groeneboomIntegrand t ω x₀ - groeneboomIntegrand t' ω x₀ := by
          have h := hmax₁' x₀ hx₀
          linarith
      _ ≤ |groeneboomIntegrand t ω x₀ - groeneboomIntegrand t' ω x₀| := le_abs_self _
      _ ≤ Real.sqrt 2 * |twoSidedBM t ω - twoSidedBM t' ω| + |t' - t| * (2 * M + |t| + |t'|) :=
          hpt x₀ hx₀
  have hside' : groeneboomCompactSup ω M t' - groeneboomCompactSup ω M t
      ≤ Real.sqrt 2 * |twoSidedBM t ω - twoSidedBM t' ω| + |t' - t| * (2 * M + |t| + |t'|) := by
    rw [← hval₀, ← hval₁]
    calc groeneboomIntegrand t' ω x₁ - groeneboomIntegrand t ω x₀
        ≤ groeneboomIntegrand t' ω x₁ - groeneboomIntegrand t ω x₁ := by
          have h := hmax₀' x₁ hx₁
          linarith
      _ ≤ |groeneboomIntegrand t' ω x₁ - groeneboomIntegrand t ω x₁| := le_abs_self _
      _ = |groeneboomIntegrand t ω x₁ - groeneboomIntegrand t' ω x₁| := abs_sub_comm _ _
      _ ≤ Real.sqrt 2 * |twoSidedBM t ω - twoSidedBM t' ω| + |t' - t| * (2 * M + |t| + |t'|) :=
          hpt x₁ hx₁
  have hD : 0 ≤ Real.sqrt 2 * |twoSidedBM t ω - twoSidedBM t' ω| + |t' - t| * (2 * M + |t| + |t'|) := by
    apply add_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (abs_nonneg _))
    exact mul_nonneg (abs_nonneg _) (by linarith [abs_nonneg t, abs_nonneg t'])
  rw [abs_le]
  constructor <;> linarith

/-- The compact-window supremum is continuous in `t`: squeeze the difference
bound against the `t' → t` limit. -/
lemma groeneboomCompactSup_continuous (ω : TwoSidedΩ) (hcont : Continuous (twoSidedBM · ω))
    {M : ℝ} (hM : 0 ≤ M) :
    Continuous (groeneboomCompactSup ω M) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hB : Tendsto (fun t' : ℝ ↦ twoSidedBM t' ω) (𝓝 t) (𝓝 (twoSidedBM t ω)) := hcont.tendsto t
  have h1 : Tendsto (fun t' : ℝ ↦ |twoSidedBM t ω - twoSidedBM t' ω|) (𝓝 t) (𝓝 0) := by
    have hsub : Tendsto (fun t' : ℝ ↦ twoSidedBM t ω - twoSidedBM t' ω) (𝓝 t)
        (𝓝 (twoSidedBM t ω - twoSidedBM t ω)) := tendsto_const_nhds.sub hB
    rw [sub_self] at hsub
    have habs := hsub.abs
    rwa [abs_zero] at habs
  have h2 : Tendsto (fun t' : ℝ ↦ |t' - t|) (𝓝 t) (𝓝 0) := by
    have hsub : Tendsto (fun t' : ℝ ↦ t' - t) (𝓝 t) (𝓝 (t - t)) := tendsto_id.sub tendsto_const_nhds
    rw [sub_self] at hsub
    have habs := hsub.abs
    rwa [abs_zero] at habs
  have h3 : Tendsto (fun t' : ℝ ↦ 2 * M + |t| + |t'|) (𝓝 t) (𝓝 (2 * M + |t| + |t|)) := by
    have hconst : Tendsto (fun _ : ℝ ↦ 2 * M + |t|) (𝓝 t) (𝓝 (2 * M + |t|)) := tendsto_const_nhds
    exact hconst.add tendsto_id.abs
  have h4 : Tendsto (fun t' : ℝ ↦ |t' - t| * (2 * M + |t| + |t'|)) (𝓝 t)
      (𝓝 (0 * (2 * M + |t| + |t|))) := h2.mul h3
  have h5 : Tendsto (fun t' : ℝ ↦ Real.sqrt 2 * |twoSidedBM t ω - twoSidedBM t' ω|) (𝓝 t)
      (𝓝 (√2 * 0)) := h1.const_mul (√2)
  have h6 := h5.add h4
  rw [mul_zero, zero_mul, add_zero] at h6
  have hineq : ∀ t' : ℝ, |groeneboomCompactSup ω M t - groeneboomCompactSup ω M t'|
      ≤ Real.sqrt 2 * |twoSidedBM t ω - twoSidedBM t' ω| + |t' - t| * (2 * M + |t| + |t'|) :=
    fun t' ↦ groeneboomCompactSup_sub_le ω hcont hM t t'
  have h0 : ∀ t' : ℝ, 0 ≤ |groeneboomCompactSup ω M t - groeneboomCompactSup ω M t'| :=
    fun t' ↦ abs_nonneg _
  have hlim := squeeze_zero h0 hineq h6
  show Tendsto (groeneboomCompactSup ω M) (𝓝 t) (𝓝 (groeneboomCompactSup ω M t))
  rw [tendsto_iff_dist_tendsto_zero]
  have heq : (fun t' : ℝ ↦ dist (groeneboomCompactSup ω M t') (groeneboomCompactSup ω M t))
      = fun t' ↦ |groeneboomCompactSup ω M t' - groeneboomCompactSup ω M t| :=
    funext fun t' ↦ Real.dist_eq _ _
  rw [heq]
  have hcomm : (fun t' : ℝ ↦ |groeneboomCompactSup ω M t' - groeneboomCompactSup ω M t|)
      = fun t' ↦ |groeneboomCompactSup ω M t - groeneboomCompactSup ω M t'| :=
    funext fun t' ↦ abs_sub_comm _ _
  rw [hcomm]
  exact hlim

/-- On the good event, the recentered Groeneboom process is continuous on
every compact interval `Icc (-T) T`: localize the supremum to the common
compact window (uniform negativity) and use the continuity of the compact
supremum. -/
lemma groeneboomU_continuousOn_of_good {ω : TwoSidedΩ} (hω : ω ∈ groeneboomGoodEvent)
    {T : ℝ} (hT : 0 < T) :
    ContinuousOn (fun t ↦ groeneboomU t ω) (Set.Icc (-T) T) := by
  obtain ⟨M, hTM, hneg⟩ := groeneboom_neg_bound_uniform hω hT
  have hloc : ∀ t ∈ Set.Icc (-T) T, groeneboomU t ω = groeneboomCompactSup ω M t :=
    fun t ht ↦ groeneboomU_eq_compactSup hω hTM hneg ht
  have hcont := hω.1.1.1
  have hM0 : 0 ≤ M := by linarith
  intro t ht
  have hwithin : ContinuousWithinAt (groeneboomCompactSup ω M) (Set.Icc (-T) T) t :=
    (groeneboomCompactSup_continuous ω hcont hM0).continuousWithinAt
  have hEq : (fun t ↦ groeneboomU t ω) =ᶠ[𝓝[Set.Icc (-T) T] t]
      (groeneboomCompactSup ω M) :=
    eventually_of_mem self_mem_nhdsWithin fun x hx ↦ hloc x hx
  exact hwithin.congr_of_eventuallyEq hEq (hloc t ht)

/-- On the good event, the recentered Groeneboom process is continuous on all
of ℝ (continuity is pointwise; every point is interior to some `Icc (-T) T`). -/
lemma groeneboomU_continuous_of_good {ω : TwoSidedΩ} (hω : ω ∈ groeneboomGoodEvent) :
    Continuous (fun t ↦ groeneboomU t ω) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hT : (0 : ℝ) < |t| + 1 := by positivity
  have hcont := groeneboomU_continuousOn_of_good hω hT
  apply hcont.continuousAt
  exact Filter.mem_of_superset (Ioo_mem_nhds (by have h := neg_abs_le t; linarith)
    (by have h' := le_abs_self t; linarith)) Set.Ioo_subset_Icc_self

/-- **A.s. path continuity of the recentered Groeneboom process**.
Together with `groeneboom_stationary_fdd`,
the recentered Groeneboom process is a stationary process with a.s. continuous
paths (fdd version; Kolmogorov–Chentsov strengthening is not claimed). -/
lemma groeneboomU_continuous_ae :
    ∀ᵐ ω ∂twoSidedBMMeasure, Continuous (fun t ↦ groeneboomU t ω) := by
  filter_upwards [groeneboomGoodEvent_ae] with ω hω
  exact groeneboomU_continuous_of_good hω

end Airy1Gumbel
