/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.GumbelLimit
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Airy1Gumbel

/-!
# Continuum maximum: from integer block maxima to `max_{x ∈ [0,T]} A(x)`

This file is the continuum wrapper for the conditional assembly. The
Airy-specific inputs remain named hypotheses via the `bundle` argument (an
`Airy1BlockExtremes` structure on the block maxima); the process `A` is
abstract here; the concrete Airy₁ process is constructed in `Airy1Process.lean` and
`LowerBound.lean` and instantiated in `ContinuousInstance.lean`. The bridge
content is that on the a.s.-continuous event (where each `Y j` is the supremum
of `A` over the unit block `[j, j+1]`), the continuum max event
`{ω | ∀ x ∈ [0, N], A x ω ≤ u}` equals the integer block event
`{ω | ∀ j < N, Y j ω ≤ u}` up to measure zero, so the conditional Gumbel
limit for the block maxima transfers to the continuum maximum
`M_N = max_{x ∈ [0,N]} A(x)`. A real-length squeeze of the normalization
then upgrades the integer-length limit to the paper's real-length statement
`M_T = max_{x ∈ [0,T]} A(x)` with real `T → ∞`.

* `Airy1ContinuousMax.mem_unit_block`: the unit blocks `[j, j+1]`, `j < N`,
  cover `[0, N]`;
* `Airy1ContinuousMax.block_bddAbove`, `Airy1ContinuousMax.le_block_sup` and
  `Airy1ContinuousMax.block_sup_le`: the supremum calculus on one block on the
  continuous-path event;
* `Airy1ContinuousMax.continuum_event_eq`: the a.e. equality of the two
  events;
* `Airy1ContinuousMax.gumbel_limit_continuum`: the headline conditional Gumbel
  limit for `max_{x ∈ [0,N]} A(x)` (integer lengths, the shape of the paper's main
  theorem, Theorem 1.1);
* `Airy1ContinuousMax.normalized_event_eq` and
  `Airy1ContinuousMax.gumbel_limit_continuum_normalized`: the paper's exact
  normalized shape `(M_N - a_N)/b_N ≤ z`;
* `Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto`: stability of the
  integer-length limit under a level perturbation `w_N → z` (L1);
* `gumbelAR_main_sub_div_tendsto`, `gumbelAR_corr_sub_div_tendsto`,
  `gumbelAR_sub_div_tendsto`, `gumbelUR_eventually_le_gumbelU_succ` and
  `gumbelU_floor_eventually_le_gumbelUR`: the real-length squeeze of the
  level (L2) — eventually
  `u_{⌊T⌋₊}(z - ε) ≤ u_T(z) ≤ u_{⌊T⌋₊+1}(z + ε)`, proved from the T3/T4
  integer-step analyses composed with `T ↦ ⌊T⌋₊`;
* `Airy1ContinuousMax.gumbel_limit_continuum_real`: the headline conditional
  Gumbel limit for `max_{x ∈ [0,T]} A(x)` as the REAL `T → ∞` (L3, the
  paper's main theorem, Theorem 1.1) — the integer-length restriction of
  `gumbel_limit_continuum` is removed;
* `Airy1ContinuousMax.normalized_event_eq_real` and
  `Airy1ContinuousMax.gumbel_limit_continuum_real_normalized`: the normalized
  real-length shape `(M_T - a_T)/b_T ≤ z` (L4).

There is deliberately no measurability field on `Airy1ContinuousMax`:
measurability obligations live in the `Airy1BlockExtremes` bundle argument
(`Y_meas`); `Measure.real` of the continuum event is well-defined without
measurability, and `MeasureTheory.measure_congr` transfers it across
a.e.-equal sets.
-/

/-- Process-level bridge: `A` is an a.s.-path-continuous process on `[0,∞)`
and `Y j` is, for a.e. `ω`, the supremum of `A` over the unit block
`[j, j+1]`. -/
structure Airy1ContinuousMax {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] where
  /-- The underlying process. -/
  A : ℝ → Ω → ℝ
  /-- Almost every path is continuous on `[0, ∞)`. -/
  path_cont : ∀ᵐ ω ∂P, ContinuousOn (fun x => A x ω) (Set.Ici 0)
  /-- The block maxima. -/
  Y : ℕ → Ω → ℝ
  /-- For a.e. `ω`, `Y j ω` is the supremum of the path over `[j, j+1]`. -/
  Y_eq : ∀ᵐ ω ∂P, ∀ j : ℕ,
    Y j ω = sSup ((fun x => A x ω) '' Set.Icc (j : ℝ) (j + 1))

/-- The unit blocks `[j, j+1]`, `j < N`, cover `[0, N]`: a point with
`x < N` lies in block `⌊x⌋₊`, and the endpoint `x = N` lies in block
`N - 1`. -/
theorem Airy1ContinuousMax.mem_unit_block {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (N : ℝ)) :
    ∃ j : ℕ, j < N ∧ x ∈ Set.Icc (j : ℝ) (j + 1) := by
  rw [Set.mem_Icc] at hx
  obtain ⟨hx0, hxN⟩ := hx
  rcases lt_or_eq_of_le hxN with hlt | heq
  · exact ⟨⌊x⌋₊, (Nat.floor_lt hx0).mpr hlt,
      Set.mem_Icc.mpr ⟨Nat.floor_le hx0, (Nat.lt_floor_add_one x).le⟩⟩
  · refine ⟨N - 1, by omega, Set.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · rw [Nat.cast_sub hN, Nat.cast_one, heq]
      linarith
    · rw [Nat.cast_sub hN, Nat.cast_one, heq]
      linarith

/-- On a continuous path, the image of a unit block is bounded above (the
block is compact). -/
theorem Airy1ContinuousMax.block_bddAbove {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (C : Airy1ContinuousMax P) {ω : Ω}
    (hcont : ContinuousOn (fun x => C.A x ω) (Set.Ici 0)) (j : ℕ) :
    BddAbove ((fun x => C.A x ω) '' Set.Icc (j : ℝ) (j + 1)) :=
  (isCompact_Icc.image_of_continuousOn (hcont.mono fun _ hx =>
    le_trans (Nat.cast_nonneg j) hx.1)).bddAbove

/-- On the continuous-path event, every value of `A` in block `j` is at most
`Y j ω`. -/
theorem Airy1ContinuousMax.le_block_sup {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (C : Airy1ContinuousMax P) {ω : Ω}
    (hcont : ContinuousOn (fun x => C.A x ω) (Set.Ici 0))
    (hY : ∀ j : ℕ, C.Y j ω = sSup ((fun x => C.A x ω) '' Set.Icc (j : ℝ) (j + 1)))
    (j : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (j : ℝ) (j + 1)) :
    C.A x ω ≤ C.Y j ω := by
  rw [hY j]
  exact le_csSup (C.block_bddAbove hcont j) ⟨x, hx, rfl⟩

/-- On the block-supremum event, if `A` is at most `u` throughout block `j`,
then `Y j ω ≤ u` (the image is nonempty, so `csSup_le` applies). -/
theorem Airy1ContinuousMax.block_sup_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (C : Airy1ContinuousMax P) {ω : Ω}
    (hY : ∀ j : ℕ, C.Y j ω = sSup ((fun x => C.A x ω) '' Set.Icc (j : ℝ) (j + 1)))
    (j : ℕ) {u : ℝ} (hu : ∀ x ∈ Set.Icc (j : ℝ) (j + 1), C.A x ω ≤ u) :
    C.Y j ω ≤ u := by
  rw [hY j]
  apply csSup_le
  · exact (Set.nonempty_Icc.mpr (by linarith : (j : ℝ) ≤ (j : ℝ) + 1)).image _
  · rintro b ⟨x, hx, rfl⟩
    exact hu x hx

/-- On the full-measure event where the paths are continuous and each `Y j`
is the block supremum, the continuum max event over `[0, N]` coincides with
the integer block-max event: the two events are a.e. equal. -/
theorem Airy1ContinuousMax.continuum_event_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (C : Airy1ContinuousMax P) {N : ℕ}
    (hN : 1 ≤ N) (u : ℝ) :
    {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ u} =ᵐ[P]
      {ω | ∀ j ∈ Finset.range N, C.Y j ω ≤ u} := by
  filter_upwards [C.path_cont, C.Y_eq] with ω hcont hY
  apply propext
  constructor
  · intro h j hj
    rw [Finset.mem_range] at hj
    apply C.block_sup_le hY j
    intro x hx
    apply h x
    rw [Set.mem_Icc] at hx ⊢
    have hjN : (j : ℝ) + 1 ≤ (N : ℝ) := by
      have h' : j + 1 ≤ N := hj
      exact_mod_cast h'
    exact ⟨le_trans (Nat.cast_nonneg j) hx.1, hx.2.trans hjN⟩
  · intro h x hx
    obtain ⟨j, hjN, hjx⟩ := Airy1ContinuousMax.mem_unit_block hN hx
    exact (C.le_block_sup hcont hY j hjx).trans (h j (Finset.mem_range.mpr hjN))

/-- **Conditional Gumbel limit, continuum form** (the shape of the paper's
main theorem, Theorem 1.1): for the continuum maximum `M_N = max_{x ∈ [0,N]} A(x)`, the
probabilities `ℙ(M_N ≤ u_N(z))` converge to `exp (-exp (-z))`, conditionally
on the Airy-specific inputs carried by `bundle`. The proof transports the
integer-block limit `Airy1BlockExtremes.gumbel_limit` across the a.e. event
equality `continuum_event_eq`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Airy1ContinuousMax P) (bundle : Airy1BlockExtremes P)
    (hY : bundle.Y = C.Y) (z : ℝ) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  have hlim := bundle.gumbel_limit z
  rw [hY] at hlim
  apply Tendsto.congr' _ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (congrArg ENNReal.toReal
    (C.continuum_event_eq hN (gumbelU N z)).measure_eq).symm

/-- The normalized event is pointwise equal to the `u_N(z)` event, since
`b_N > 0` for `N ≥ 2` (`gumbelU N z = gumbelA N + gumbelB N * z`). -/
theorem Airy1ContinuousMax.normalized_event_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (C : Airy1ContinuousMax P) {N : ℕ}
    (hN : 2 ≤ N) (z : ℝ) :
    {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), (C.A x ω - gumbelA N) / gumbelB N ≤ z} =
      {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N z} := by
  ext ω
  constructor
  · intro h x hx
    have h1 := (div_le_iff₀ (gumbelB_pos hN)).mp (h x hx)
    show C.A x ω ≤ gumbelA N + gumbelB N * z
    linarith
  · intro h x hx
    apply (div_le_iff₀ (gumbelB_pos hN)).mpr
    have h1 : C.A x ω ≤ gumbelA N + gumbelB N * z := h x hx
    linarith

/-- The paper's exact normalized shape: `(M_N - a_N)/b_N` converges in law to
the standard Gumbel distribution, conditionally on the Airy-specific inputs
carried by `bundle`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_normalized
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Airy1ContinuousMax P) (bundle : Airy1BlockExtremes P)
    (hY : bundle.Y = C.Y) (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ),
      (C.A x ω - gumbelA N) / gumbelB N ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  apply Tendsto.congr' _ (C.gumbel_limit_continuum bundle hY z)
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [C.normalized_event_eq hN z]

/-! ### Real-length extension: squeeze infrastructure and the perturbed limit

The remaining results extend `gumbel_limit_continuum` from integer lengths
`N` to real lengths `T → ∞`, matching the paper's main theorem (Theorem 1.1). The analytic
content is the real squeeze of the level proved in the next section: for
`N = ⌊T⌋₊`, eventually `u_N(z - ε) ≤ u_T(z) ≤ u_{N+1}(z + ε)`, because both
the centering and the scaling vary by `o(b_N)` across one unit interval
(the T3/T4 analyses of `BlockExtremes.lean` composed with `T ↦ ⌊T⌋₊`). -/

/-- `⌊T⌋₊ → ∞` as the real `T → ∞`. -/
lemma tendsto_nat_floor_atTop : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨(b : ℝ), fun a ha => Nat.le_floor ha⟩

/-- `M ↦ M - 1` tends to `atTop` on `ℕ`. -/
lemma tendsto_nat_pred_atTop : Tendsto (fun M : ℕ => M - 1) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨b + 1, fun M hM => by omega⟩

/-- The standard Gumbel cdf `z ↦ exp (-exp (-z))` is continuous. -/
lemma continuous_gumbelCDF : Continuous (fun z : ℝ => Real.exp (-Real.exp (-z))) :=
  Real.continuous_exp.comp ((Real.continuous_exp.comp continuous_neg).neg)

/-- For `a` below the Gumbel cdf at `z`, a small downward shift of `z` still
exceeds `a`. -/
lemma exists_gumbelCDF_gt {a z : ℝ} (h : a < Real.exp (-Real.exp (-z))) :
    ∃ ε > 0, a < Real.exp (-Real.exp (-(z - ε))) := by
  have hcont : Tendsto (fun ε : ℝ => Real.exp (-Real.exp (-(z - ε)))) (𝓝 0)
      (𝓝 (Real.exp (-Real.exp (-z)))) := by
    have h1 : Tendsto (fun ε : ℝ => z - ε) (𝓝 0) (𝓝 z) := by
      have hc : Tendsto (fun _ : ℝ => z) (𝓝 (0 : ℝ)) (𝓝 z) := tendsto_const_nhds
      have hid : Tendsto (fun ε : ℝ => ε) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
      have h := hc.sub hid
      simpa using h
    exact (continuous_gumbelCDF.tendsto z).comp h1
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp (hcont.eventually (Ioi_mem_nhds h))
  refine ⟨δ / 2, half_pos hδ0, hδ ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (half_pos hδ0).le]
  exact half_lt_self hδ0

/-- For `b` above the Gumbel cdf at `z`, a small upward shift of `z` stays
below `b`. -/
lemma exists_gumbelCDF_lt {b z : ℝ} (h : Real.exp (-Real.exp (-z)) < b) :
    ∃ ε > 0, Real.exp (-Real.exp (-(z + ε))) < b := by
  have hcont : Tendsto (fun ε : ℝ => Real.exp (-Real.exp (-(z + ε)))) (𝓝 0)
      (𝓝 (Real.exp (-Real.exp (-z)))) := by
    have h1 : Tendsto (fun ε : ℝ => z + ε) (𝓝 0) (𝓝 z) := by
      have hc : Tendsto (fun _ : ℝ => z) (𝓝 (0 : ℝ)) (𝓝 z) := tendsto_const_nhds
      have hid : Tendsto (fun ε : ℝ => ε) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
      have h := hc.add hid
      simpa using h
    exact (continuous_gumbelCDF.tendsto z).comp h1
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp (hcont.eventually (Iio_mem_nhds h))
  refine ⟨δ / 2, half_pos hδ0, hδ ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (half_pos hδ0).le]
  exact half_lt_self hδ0

/-- L1: the integer-length continuum Gumbel limit is stable under an
asymptotically constant level perturbation `w_N → z`. For each `ε > 0`,
eventually `z - ε < w N < z + ε`, and since `b_N > 0` the perturbed event is
sandwiched between the fixed-level events at `z ∓ ε`; the sandwich closes by
the continuity of the Gumbel cdf (`exists_gumbelCDF_gt/lt`). -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Airy1ContinuousMax P) (bundle : Airy1BlockExtremes P)
    (hY : bundle.Y = C.Y) (z : ℝ) (w : ℕ → ℝ) (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N (w N)})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  have preal_mono : ∀ {s t : Set Ω}, s ⊆ t → P.real s ≤ P.real t :=
    fun h => ENNReal.toReal_mono (measure_ne_top P _) (measure_mono h)
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨ε, hε0, hε⟩ := exists_gumbelCDF_gt ha
    have hlim := C.gumbel_limit_continuum bundle hY (z - ε)
    filter_upwards [hlim.eventually (Ioi_mem_nhds hε),
      hw.eventually (Ioi_mem_nhds (by linarith : z - ε < z)), eventually_ge_atTop 2]
      with N hN1 hN2 hN3
    refine hN1.trans_le (preal_mono ?_)
    intro ω hω x hx
    apply (hω x hx).trans
    show gumbelA N + gumbelB N * (z - ε) ≤ gumbelA N + gumbelB N * w N
    linarith [mul_le_mul_of_nonneg_left hN2.le (gumbelB_pos hN3).le]
  · obtain ⟨ε, hε0, hε⟩ := exists_gumbelCDF_lt hb
    have hlim := C.gumbel_limit_continuum bundle hY (z + ε)
    filter_upwards [hlim.eventually (Iio_mem_nhds hε),
      hw.eventually (Iio_mem_nhds (by linarith : z < z + ε)), eventually_ge_atTop 2]
      with N hN1 hN2 hN3
    refine (preal_mono ?_).trans_lt hN1
    intro ω hω x hx
    apply (hω x hx).trans
    show gumbelA N + gumbelB N * w N ≤ gumbelA N + gumbelB N * (z + ε)
    linarith [mul_le_mul_of_nonneg_left hN2.le (gumbelB_pos hN3).le]

/-! ### Real-length extension: the level squeeze (L2) -/

/-- T3 inverted: `b_n / b_{n+1} → 1`. -/
lemma gumbelB_ratio_inv :
    Tendsto (fun n : ℕ => gumbelB n / gumbelB (n + 1)) atTop (𝓝 1) := by
  have h := gumbelB_succ_ratio.inv₀ one_ne_zero
  rw [inv_one] at h
  exact Tendsto.congr' (Eventually.of_forall fun n => inv_div _ _) h

/-- The T4 difference against the next scale:
`(a_n - a_{n+1})/b_{n+1} → 0`. -/
lemma gumbelA_diff_succ_ratio :
    Tendsto (fun n : ℕ => (gumbelA n - gumbelA (n + 1)) / gumbelB (n + 1)) atTop (𝓝 0) := by
  have h := (gumbelA_succ_diff.mul gumbelB_ratio_inv).neg
  simp only [zero_mul, neg_zero] at h
  apply Tendsto.congr' _ h
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hb1 := (gumbelB_pos hn).ne'
  have hb2 := (gumbelB_pos (by omega : 2 ≤ n + 1)).ne'
  field_simp [hb1, hb2]
  ring

/-- T3 along `T ↦ ⌊T⌋₊`: `b_{⌊T⌋₊+1}/b_{⌊T⌋₊} → 1`. -/
lemma gumbelB_succ_ratio_floor :
    Tendsto (fun T : ℝ => gumbelB (⌊T⌋₊ + 1) / gumbelB ⌊T⌋₊) atTop (𝓝 1) :=
  gumbelB_succ_ratio.comp tendsto_nat_floor_atTop

/-- Inverted T3 along `T ↦ ⌊T⌋₊`: `b_{⌊T⌋₊}/b_{⌊T⌋₊+1} → 1`. -/
lemma gumbelB_ratio_inv_floor :
    Tendsto (fun T : ℝ => gumbelB ⌊T⌋₊ / gumbelB (⌊T⌋₊ + 1)) atTop (𝓝 1) :=
  gumbelB_ratio_inv.comp tendsto_nat_floor_atTop

/-- T4 along `T ↦ ⌊T⌋₊`: `(a_{⌊T⌋₊+1} - a_{⌊T⌋₊})/b_{⌊T⌋₊} → 0`. -/
lemma gumbelA_succ_diff_floor :
    Tendsto (fun T : ℝ => (gumbelA (⌊T⌋₊ + 1) - gumbelA ⌊T⌋₊) / gumbelB ⌊T⌋₊)
      atTop (𝓝 0) :=
  gumbelA_succ_diff.comp tendsto_nat_floor_atTop

/-- The reciprocal of the scaling: `1/b_N = (3/(2γ)) · (log N)^{1/3}`. -/
lemma gumbelB_inv_eq {N : ℕ} (hN : 2 ≤ N) :
    (gumbelB N)⁻¹ = (3 / (2 * airyGamma)) * (Real.log ↑N) ^ ((1 : ℝ) / 3) := by
  have hlogN := log_nat_pos hN
  have e : gumbelB N = (2 * airyGamma / 3) * ((Real.log ↑N) ^ ((1 : ℝ) / 3))⁻¹ := by
    unfold gumbelB
    rw [rpow_neg_one_third hlogN.le]
  rw [e, mul_inv_rev, inv_inv, inv_div,
    mul_comm ((Real.log ↑N) ^ ((1 : ℝ) / 3)) (3 / (2 * airyGamma))]

/-- L2(a): the real scaling is squeezed between the two adjacent integer
scalings, `b_{⌊T⌋₊+1} ≤ b_T ≤ b_{⌊T⌋₊}`, since the factor `(log x)^{-1/3}`
is antitone for `x > 1`. -/
lemma gumbelBR_squeeze {T : ℝ} (hT : 2 ≤ T) :
    gumbelB (⌊T⌋₊ + 1) ≤ gumbelBR T ∧ gumbelBR T ≤ gumbelB ⌊T⌋₊ := by
  have hN2 : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
  have hT0 : (0 : ℝ) ≤ T := zero_le_two.trans hT
  have hle1 : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le hT0
  have hle2 : T ≤ ((⌊T⌋₊ + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add_one]
    exact (Nat.lt_floor_add_one T).le
  have hNpos : (0 : ℝ) < (⌊T⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊T⌋₊)
  have hN1 : (1 : ℝ) < (⌊T⌋₊ : ℝ) := by exact_mod_cast (by omega : 1 < ⌊T⌋₊)
  have hlogN : 0 < Real.log ⌊T⌋₊ := Real.log_pos hN1
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogN1 : 0 < Real.log ↑(⌊T⌋₊ + 1) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < ⌊T⌋₊ + 1))
  have hγ3 : (0 : ℝ) ≤ 2 * airyGamma / 3 :=
    div_nonneg (mul_nonneg (by norm_num) airyGamma_pos.le) (by norm_num)
  have h1 : (Real.log T) ^ (-(1 : ℝ) / 3) ≤ (Real.log ↑⌊T⌋₊) ^ (-(1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hlogN (Real.log_le_log hNpos hle1) (by norm_num)
  have h2 : (Real.log ↑(⌊T⌋₊ + 1)) ^ (-(1 : ℝ) / 3) ≤ (Real.log T) ^ (-(1 : ℝ) / 3) := by
    apply Real.rpow_le_rpow_of_nonpos hlogT _ (by norm_num)
    exact Real.log_le_log (by linarith) hle2
  exact ⟨mul_le_mul_of_nonneg_left h2 hγ3, mul_le_mul_of_nonneg_left h1 hγ3⟩

/-- L2(b), main part: the gap of the `γ L^{2/3}` term of the centering across
`[⌊T⌋₊, T]`, divided by `b_{⌊T⌋₊}`, tends to `0`: it is bounded by the
integer-step main gap (the T4 component `gumbelA_diff_main_tendsto`). -/
lemma gumbelAR_main_sub_div_tendsto :
    Tendsto (fun T : ℝ =>
      ((Real.log T) ^ ((2 : ℝ) / 3) - (Real.log ↑⌊T⌋₊) ^ ((2 : ℝ) / 3)) / gumbelB ⌊T⌋₊)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => (3 / (2 * airyGamma)) *
      (((Real.log ↑(⌊T⌋₊ + 1)) ^ ((2 : ℝ) / 3) - (Real.log ↑⌊T⌋₊) ^ ((2 : ℝ) / 3)) *
        (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3))) atTop (𝓝 0) := by
    have h := (gumbelA_diff_main_tendsto.const_mul (3 / (2 * airyGamma))).comp
      tendsto_nat_floor_atTop
    simpa [Function.comp_def, mul_zero] using h
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    have hN2 : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
    have hN1 : (1 : ℝ) < (⌊T⌋₊ : ℝ) := by exact_mod_cast (by omega : 1 < ⌊T⌋₊)
    have hlogN : 0 < Real.log ⌊T⌋₊ := Real.log_pos hN1
    have hNpos : (0 : ℝ) < (⌊T⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊T⌋₊)
    have hle : (Real.log ↑⌊T⌋₊) ^ ((2 : ℝ) / 3) ≤ (Real.log T) ^ ((2 : ℝ) / 3) := by
      apply Real.rpow_le_rpow hlogN.le _ (by norm_num)
      exact Real.log_le_log hNpos (Nat.floor_le (by linarith))
    exact div_nonneg (sub_nonneg.mpr hle) (gumbelB_pos hN2).le
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    have hN2 : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
    have hN1 : (1 : ℝ) < (⌊T⌋₊ : ℝ) := by exact_mod_cast (by omega : 1 < ⌊T⌋₊)
    have hlogN : 0 < Real.log ⌊T⌋₊ := Real.log_pos hN1
    have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
    have hle : (Real.log T) ^ ((2 : ℝ) / 3) ≤ (Real.log ↑(⌊T⌋₊ + 1)) ^ ((2 : ℝ) / 3) := by
      apply Real.rpow_le_rpow hlogT.le _ (by norm_num)
      apply Real.log_le_log (by linarith : (0 : ℝ) < T)
      rw [Nat.cast_add_one]
      exact (Nat.lt_floor_add_one T).le
    calc ((Real.log T) ^ ((2 : ℝ) / 3) - (Real.log ↑⌊T⌋₊) ^ ((2 : ℝ) / 3)) / gumbelB ⌊T⌋₊
        = ((Real.log T) ^ ((2 : ℝ) / 3) - (Real.log ↑⌊T⌋₊) ^ ((2 : ℝ) / 3)) *
            ((3 / (2 * airyGamma)) * (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3)) := by
          rw [div_eq_mul_inv, gumbelB_inv_eq hN2]
      _ ≤ ((Real.log ↑(⌊T⌋₊ + 1)) ^ ((2 : ℝ) / 3) - (Real.log ↑⌊T⌋₊) ^ ((2 : ℝ) / 3)) *
            ((3 / (2 * airyGamma)) * (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3)) := by
          apply mul_le_mul_of_nonneg_right (sub_le_sub_right hle _)
          have h3 : (0 : ℝ) ≤ 3 / (2 * airyGamma) :=
            div_nonneg (by norm_num) (mul_nonneg (by norm_num) airyGamma_pos.le)
          exact mul_nonneg h3 (Real.rpow_nonneg hlogN.le _)
      _ = (3 / (2 * airyGamma)) *
            (((Real.log ↑(⌊T⌋₊ + 1)) ^ ((2 : ℝ) / 3) - (Real.log ↑⌊T⌋₊) ^ ((2 : ℝ) / 3)) *
              (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3)) := by ring

/-- The increment of `g(x) = log log x + log (3/(2π³))` over one integer step
equals `log (log (n+1)/log n)`, hence tends to `0`. -/
lemma gumbelAR_corr_step1_tendsto :
    Tendsto (fun n : ℕ =>
      (Real.log (Real.log (↑(n + 1))) + Real.log (3 / (2 * Real.pi ^ 3))) -
        (Real.log (Real.log (↑n)) + Real.log (3 / (2 * Real.pi ^ 3)))) atTop (𝓝 0) := by
  have hρ1 : Tendsto (fun n : ℕ => Real.log (Real.log (↑(n + 1)) / Real.log (↑n)))
      atTop (𝓝 0) := by
    have hg : Tendsto Real.log (𝓝 1) (𝓝 (Real.log 1)) := Real.continuousAt_log one_ne_zero
    have h := hg.comp tendsto_log_ratio_one
    simpa [Function.comp_def, Real.log_one] using h
  apply Tendsto.congr' _ hρ1
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hL := log_nat_pos hn
  have hL' := log_nat_pos (by omega : 2 ≤ n + 1)
  have hρ0 : (0 : ℝ) < Real.log (↑(n + 1)) / Real.log (↑n) := div_pos hL' hL
  have hL'eq : Real.log (↑(n + 1)) = Real.log (↑(n + 1)) / Real.log (↑n) * Real.log (↑n) :=
    (div_mul_cancel₀ _ hL.ne').symm
  have h1 : Real.log (Real.log (↑(n + 1))) =
      Real.log (Real.log (↑(n + 1)) / Real.log (↑n)) + Real.log (Real.log (↑n)) := by
    conv_lhs => rw [hL'eq]
    exact Real.log_mul hρ0.ne' hL.ne'
  rw [h1]
  ring

/-- `g(N+1) · (1 - ρ_N^{-1/3}) → 0` with `ρ_N = log (N+1)/log N`: it equals
`(g(N+1) - g(N)) - (g(N+1)·ρ_N^{-1/3} - g(N))`, the difference of the step
increment and the T4 correction increment (`gumbelA_diff_corr_tendsto`). -/
lemma gumbelAR_corr_step2_tendsto :
    Tendsto (fun n : ℕ =>
      (Real.log (Real.log (↑(n + 1))) + Real.log (3 / (2 * Real.pi ^ 3))) *
        (1 - (Real.log (↑(n + 1)) / Real.log (↑n)) ^ (-(1 : ℝ) / 3))) atTop (𝓝 0) := by
  have h := gumbelAR_corr_step1_tendsto.sub gumbelA_diff_corr_tendsto
  simp only [sub_zero] at h
  apply Tendsto.congr' _ h
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hL := log_nat_pos hn
  have hL' := log_nat_pos (by omega : 2 ≤ n + 1)
  have hρpow : (Real.log (↑(n + 1)) / Real.log (↑n)) ^ (-(1 : ℝ) / 3) =
      (Real.log (↑(n + 1))) ^ (-(1 : ℝ) / 3) * (Real.log (↑n)) ^ ((1 : ℝ) / 3) := by
    rw [Real.div_rpow hL'.le hL.le, div_eq_mul_inv,
      show (-(1 : ℝ) / 3 : ℝ) = -((1 : ℝ) / 3) by norm_num, Real.rpow_neg hL'.le,
      Real.rpow_neg hL.le, inv_inv]
  rw [hρpow]
  ring

/-- L2(b), correction part: the gap of the correction term
`f(x) = (log log x + c₀)·(log x)^{-1/3}` of the centering across `[⌊T⌋₊, T]`,
divided by `b_{⌊T⌋₊}`, tends to `0`. With `g = log log + c₀` and
`h = (log ·)^{1/3}` (both increasing, `h > 0`), the decomposition
`f(T) − f(N) = (g(T) − g(N))/h(T) + g(N)·(1/h(T) − 1/h(N))` bounds the gap by
`(g(N+1) − g(N))/h(N) + g(N+1)·(1/h(N) − 1/h(N+1))`, which is `o(b_N)` by the
T4 component analyses (`gumbelAR_corr_step1/2_tendsto`). -/
lemma gumbelAR_corr_sub_div_tendsto :
    Tendsto (fun T : ℝ =>
      (((Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) *
            (Real.log T) ^ (-(1 : ℝ) / 3) -
          (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3))) *
            (Real.log ↑⌊T⌋₊) ^ (-(1 : ℝ) / 3)) / gumbelB ⌊T⌋₊)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => (3 / (2 * airyGamma)) *
      (((Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) -
          (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) +
        (Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (1 - (Real.log ↑(⌊T⌋₊ + 1) / Real.log ↑⌊T⌋₊) ^ (-(1 : ℝ) / 3)))) atTop (𝓝 0) := by
    have h := (gumbelAR_corr_step1_tendsto.add gumbelAR_corr_step2_tendsto).const_mul
      (3 / (2 * airyGamma))
    have h2 := h.comp tendsto_nat_floor_atTop
    simpa [Function.comp_def, add_zero, mul_zero] using h2
  have hg0 : ∀ᶠ T : ℝ in atTop,
      0 ≤ Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)) := by
    have hlogL : Tendsto (fun n : ℕ => Real.log (Real.log (↑n))) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_L_atTop
    have h := tendsto_nat_floor_atTop.eventually
      (hlogL.eventually_ge_atTop |Real.log (3 / (2 * Real.pi ^ 3))|)
    filter_upwards [h] with T hT
    have h1 : -Real.log (3 / (2 * Real.pi ^ 3)) ≤ |Real.log (3 / (2 * Real.pi ^ 3))| :=
      neg_le_abs _
    linarith [hT, h1]
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ), hg0] with T hT hgN
  have hN2 : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
  have hT0 : (0 : ℝ) ≤ T := zero_le_two.trans hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hle1 : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le hT0
  have hle2 : T ≤ ((⌊T⌋₊ + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add_one]
    exact (Nat.lt_floor_add_one T).le
  have hNpos : (0 : ℝ) < (⌊T⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊T⌋₊)
  have hN1 : (1 : ℝ) < (⌊T⌋₊ : ℝ) := by exact_mod_cast (by omega : 1 < ⌊T⌋₊)
  have hlogN : 0 < Real.log ⌊T⌋₊ := Real.log_pos hN1
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogN1 : 0 < Real.log ↑(⌊T⌋₊ + 1) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < ⌊T⌋₊ + 1))
  have hbN := gumbelB_pos hN2
  -- monotonicity of `g` and `h`
  have hgNT : Real.log (Real.log ↑⌊T⌋₊) ≤ Real.log (Real.log T) :=
    Real.log_le_log hlogN (Real.log_le_log hNpos hle1)
  have hgTN1 : Real.log (Real.log T) ≤ Real.log (Real.log ↑(⌊T⌋₊ + 1)) :=
    Real.log_le_log hlogT (Real.log_le_log hTpos hle2)
  have hgNN1 : Real.log (Real.log ↑⌊T⌋₊) ≤ Real.log (Real.log ↑(⌊T⌋₊ + 1)) :=
    hgNT.trans hgTN1
  have hhNT : (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) ≤ (Real.log T) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hlogN.le (Real.log_le_log hNpos hle1) (by norm_num)
  have hhTN1 : (Real.log T) ^ ((1 : ℝ) / 3) ≤ (Real.log ↑(⌊T⌋₊ + 1)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hlogT.le (Real.log_le_log hTpos hle2) (by norm_num)
  have hhNN1 : (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) ≤ (Real.log ↑(⌊T⌋₊ + 1)) ^ ((1 : ℝ) / 3) :=
    hhNT.trans hhTN1
  have hposN : 0 < (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hlogN _
  have hposT : 0 < (Real.log T) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hlogT _
  have hposN1 : 0 < (Real.log ↑(⌊T⌋₊ + 1)) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hlogN1 _
  have hgN0 : 0 ≤ Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)) := hgN
  have hgN10 : 0 ≤ Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3)) := by
    linarith [hgN0, hgNN1]
  -- the pointwise bound on `|f(T) − f(N)|`
  have hcore : |(Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) *
        (Real.log T) ^ (-(1 : ℝ) / 3) -
      (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3))) *
        (Real.log ↑⌊T⌋₊) ^ (-(1 : ℝ) / 3)| ≤
      ((Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) -
          (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
        (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) +
      (Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) *
        (1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) -
          1 / (Real.log ↑(⌊T⌋₊ + 1)) ^ ((1 : ℝ) / 3)) := by
    have hdecomp : (Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (Real.log T) ^ (-(1 : ℝ) / 3) -
        (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (Real.log ↑⌊T⌋₊) ^ (-(1 : ℝ) / 3) =
        ((Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) -
            (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
          (Real.log T) ^ ((1 : ℝ) / 3) +
        (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (1 / (Real.log T) ^ ((1 : ℝ) / 3) - 1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3)) := by
      rw [rpow_neg_one_third hlogT.le, rpow_neg_one_third hlogN.le]
      field_simp [hposT.ne', hposN.ne']
      ring
    rw [hdecomp]
    have hA0 : (0 : ℝ) ≤
        ((Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) -
          (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
        (Real.log T) ^ ((1 : ℝ) / 3) :=
      div_nonneg (by linarith [hgNT]) hposT.le
    have hA1 : ((Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) -
          (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
        (Real.log T) ^ ((1 : ℝ) / 3) ≤
        ((Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) -
          (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
        (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) := by
      calc ((Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) -
            (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
          (Real.log T) ^ ((1 : ℝ) / 3)
          ≤ ((Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) -
              (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
            (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) :=
            div_le_div_of_nonneg_left (by linarith [hgNT]) hposN hhNT
        _ ≤ ((Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) -
              (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
            (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) :=
            (div_le_div_iff_of_pos_right hposN).mpr (by linarith [hgTN1])
    have hB1 : |(Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (1 / (Real.log T) ^ ((1 : ℝ) / 3) - 1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3))| =
        (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) - 1 / (Real.log T) ^ ((1 : ℝ) / 3)) := by
      rw [abs_mul, abs_of_nonneg hgN0,
        abs_of_nonpos (sub_nonpos.mpr (one_div_le_one_div_of_le hposN hhNT))]
      ring
    have hB2 : (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) - 1 / (Real.log T) ^ ((1 : ℝ) / 3)) ≤
        (Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) -
            1 / (Real.log ↑(⌊T⌋₊ + 1)) ^ ((1 : ℝ) / 3)) := by
      have h1 : (1 : ℝ) / (Real.log ↑(⌊T⌋₊ + 1)) ^ ((1 : ℝ) / 3) ≤
          1 / (Real.log T) ^ ((1 : ℝ) / 3) := one_div_le_one_div_of_le hposT hhTN1
      have h2 : 1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) - 1 / (Real.log T) ^ ((1 : ℝ) / 3) ≤
          1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) -
            1 / (Real.log ↑(⌊T⌋₊ + 1)) ^ ((1 : ℝ) / 3) := by linarith [h1]
      have h3 := mul_le_mul_of_nonneg_left h2 hgN0
      have h4 : (0 : ℝ) ≤ 1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) -
          1 / (Real.log ↑(⌊T⌋₊ + 1)) ^ ((1 : ℝ) / 3) :=
        sub_nonneg.mpr (one_div_le_one_div_of_le hposN hhNN1)
      have h5 := mul_le_mul_of_nonneg_right (by linarith [hgNN1] :
        Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)) ≤
          Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) h4
      exact h3.trans h5
    calc |((Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) -
            (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
          (Real.log T) ^ ((1 : ℝ) / 3) +
        (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (1 / (Real.log T) ^ ((1 : ℝ) / 3) - 1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3))|
        ≤ |((Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) -
              (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
            (Real.log T) ^ ((1 : ℝ) / 3)| +
          |(Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3))) *
            (1 / (Real.log T) ^ ((1 : ℝ) / 3) - 1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3))| :=
          abs_add_le _ _
      _ = ((Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) -
              (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
            (Real.log T) ^ ((1 : ℝ) / 3) +
          (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3))) *
            (1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) - 1 / (Real.log T) ^ ((1 : ℝ) / 3)) := by
          rw [abs_of_nonneg hA0, hB1]
      _ ≤ ((Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) -
              (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
            (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) +
          (Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) *
            (1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) -
              1 / (Real.log ↑(⌊T⌋₊ + 1)) ^ ((1 : ℝ) / 3)) := add_le_add hA1 hB2
  -- `ρ^{-1/3}` through `h`: `h(N)/h(N+1) = (log (N+1)/log N)^{-1/3}`
  have hratio : (Real.log ↑(⌊T⌋₊ + 1) / Real.log ↑⌊T⌋₊) ^ (-(1 : ℝ) / 3) *
      (Real.log ↑(⌊T⌋₊ + 1)) ^ ((1 : ℝ) / 3) = (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) := by
    rw [Real.div_rpow hlogN1.le hlogN.le, div_mul_eq_mul_div,
      show (-(1 : ℝ) / 3 : ℝ) = -((1 : ℝ) / 3) by norm_num, Real.rpow_neg hlogN1.le,
      Real.rpow_neg hlogN.le, inv_mul_cancel₀ hposN1.ne', one_div, inv_inv]
  have hratio' : (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) / (Real.log ↑(⌊T⌋₊ + 1)) ^ ((1 : ℝ) / 3) =
      (Real.log ↑(⌊T⌋₊ + 1) / Real.log ↑⌊T⌋₊) ^ (-(1 : ℝ) / 3) := by
    rw [div_eq_iff hposN1.ne']
    exact hratio.symm
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hbN]
  calc |(Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (Real.log T) ^ (-(1 : ℝ) / 3) -
        (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (Real.log ↑⌊T⌋₊) ^ (-(1 : ℝ) / 3)| / gumbelB ⌊T⌋₊
      = |(Real.log (Real.log T) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (Real.log T) ^ (-(1 : ℝ) / 3) -
        (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (Real.log ↑⌊T⌋₊) ^ (-(1 : ℝ) / 3)| *
          ((3 / (2 * airyGamma)) * (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3)) := by
        rw [div_eq_mul_inv, gumbelB_inv_eq hN2]
    _ ≤ (((Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) -
            (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) /
          (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) +
        (Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) *
          (1 / (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3) -
            1 / (Real.log ↑(⌊T⌋₊ + 1)) ^ ((1 : ℝ) / 3))) *
          ((3 / (2 * airyGamma)) * (Real.log ↑⌊T⌋₊) ^ ((1 : ℝ) / 3)) := by
        apply mul_le_mul_of_nonneg_right hcore
        have h3 : (0 : ℝ) ≤ 3 / (2 * airyGamma) :=
          div_nonneg (by norm_num) (mul_nonneg (by norm_num) airyGamma_pos.le)
        exact mul_nonneg h3 (Real.rpow_nonneg hlogN.le _)
    _ = (3 / (2 * airyGamma)) *
        (((Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) -
            (Real.log (Real.log ↑⌊T⌋₊) + Real.log (3 / (2 * Real.pi ^ 3)))) +
          (Real.log (Real.log ↑(⌊T⌋₊ + 1)) + Real.log (3 / (2 * Real.pi ^ 3))) *
            (1 - (Real.log ↑(⌊T⌋₊ + 1) / Real.log ↑⌊T⌋₊) ^ (-(1 : ℝ) / 3))) := by
        rw [← hratio']
        field_simp [hposN.ne', hposN1.ne', mul_ne_zero two_ne_zero airyGamma_pos.ne']

/-- L2(b) assembled: `(a_T − a_{⌊T⌋₊})/b_{⌊T⌋₊} → 0`. -/
lemma gumbelAR_sub_div_tendsto :
    Tendsto (fun T : ℝ => (gumbelAR T - gumbelA ⌊T⌋₊) / gumbelB ⌊T⌋₊) atTop (𝓝 0) := by
  have h := (gumbelAR_main_sub_div_tendsto.const_mul airyGamma).add
    (gumbelAR_corr_sub_div_tendsto.const_mul (airyGamma / 9))
  simp only [mul_zero, add_zero] at h
  apply Tendsto.congr' _ h
  filter_upwards with T
  unfold gumbelAR gumbelA
  ring

/-- L2(c), upper inequality: for every `ε > 0`, eventually along the real
`T → ∞`, `u_T(z) ≤ u_{⌊T⌋₊+1}(z + ε)`. The defect decomposes as
`(a_T − a_{N+1}) + (b_T − b_{N+1})·z − ε·b_{N+1}` with `N = ⌊T⌋₊`, where the
first two terms are `o(b_{N+1})` by L2(b) and T3/T4, so the `−ε·b_{N+1}`
term dominates. -/
lemma gumbelUR_eventually_le_gumbelU_succ (z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, gumbelUR T z ≤ gumbelU (⌊T⌋₊ + 1) (z + ε) := by
  have hN2 : ∀ᶠ T : ℝ in atTop, 2 ≤ ⌊T⌋₊ :=
    tendsto_nat_floor_atTop.eventually_ge_atTop 2
  have hA : ∀ᶠ T : ℝ in atTop,
      |gumbelAR T - gumbelA ⌊T⌋₊| ≤ (ε / 3) * gumbelB (⌊T⌋₊ + 1) := by
    have h1 : ∀ᶠ T : ℝ in atTop,
        |(gumbelAR T - gumbelA ⌊T⌋₊) / gumbelB ⌊T⌋₊| < ε / 6 := by
      have h := (Metric.tendsto_nhds.mp gumbelAR_sub_div_tendsto) (ε / 6) (by positivity)
      filter_upwards [h] with T hT
      rwa [Real.dist_eq, sub_zero] at hT
    have h2 : ∀ᶠ T : ℝ in atTop, gumbelB ⌊T⌋₊ ≤ 2 * gumbelB (⌊T⌋₊ + 1) := by
      have h := (Metric.tendsto_nhds.mp gumbelB_ratio_inv_floor) 1 one_pos
      filter_upwards [h, hN2] with T hT hN
      have hb1 := gumbelB_pos (by omega : 2 ≤ ⌊T⌋₊ + 1)
      rw [Real.dist_eq] at hT
      have h4 : gumbelB ⌊T⌋₊ / gumbelB (⌊T⌋₊ + 1) < 2 := by
        have h5 := (abs_lt.mp hT).2
        linarith [h5]
      exact ((div_lt_iff₀ hb1).mp h4).le
    filter_upwards [h1, h2, hN2] with T h1 h2 hN
    have hb := gumbelB_pos hN
    rw [abs_div, abs_of_pos hb] at h1
    have h3 : |gumbelAR T - gumbelA ⌊T⌋₊| < (ε / 6) * gumbelB ⌊T⌋₊ := by
      have h4 := mul_lt_mul_of_pos_right h1 hb
      rwa [div_mul_cancel₀ _ hb.ne'] at h4
    exact le_of_lt (calc |gumbelAR T - gumbelA ⌊T⌋₊| < (ε / 6) * gumbelB ⌊T⌋₊ := h3
      _ ≤ (ε / 6) * (2 * gumbelB (⌊T⌋₊ + 1)) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg hε.le (by norm_num))
      _ = (ε / 3) * gumbelB (⌊T⌋₊ + 1) := by ring)
  have hB : ∀ᶠ T : ℝ in atTop,
      |gumbelA (⌊T⌋₊ + 1) - gumbelA ⌊T⌋₊| ≤ (ε / 3) * gumbelB (⌊T⌋₊ + 1) := by
    have h1 : ∀ᶠ T : ℝ in atTop,
        |(gumbelA (⌊T⌋₊ + 1) - gumbelA ⌊T⌋₊) / gumbelB ⌊T⌋₊| < ε / 6 := by
      have h := (Metric.tendsto_nhds.mp gumbelA_succ_diff_floor) (ε / 6) (by positivity)
      filter_upwards [h] with T hT
      rwa [Real.dist_eq, sub_zero] at hT
    have h2 : ∀ᶠ T : ℝ in atTop, gumbelB ⌊T⌋₊ ≤ 2 * gumbelB (⌊T⌋₊ + 1) := by
      have h := (Metric.tendsto_nhds.mp gumbelB_ratio_inv_floor) 1 one_pos
      filter_upwards [h, hN2] with T hT hN
      have hb1 := gumbelB_pos (by omega : 2 ≤ ⌊T⌋₊ + 1)
      rw [Real.dist_eq] at hT
      have h4 : gumbelB ⌊T⌋₊ / gumbelB (⌊T⌋₊ + 1) < 2 := by
        have h5 := (abs_lt.mp hT).2
        linarith [h5]
      exact ((div_lt_iff₀ hb1).mp h4).le
    filter_upwards [h1, h2, hN2] with T h1 h2 hN
    have hb := gumbelB_pos hN
    rw [abs_div, abs_of_pos hb] at h1
    have h3 : |gumbelA (⌊T⌋₊ + 1) - gumbelA ⌊T⌋₊| < (ε / 6) * gumbelB ⌊T⌋₊ := by
      have h4 := mul_lt_mul_of_pos_right h1 hb
      rwa [div_mul_cancel₀ _ hb.ne'] at h4
    exact le_of_lt (calc |gumbelA (⌊T⌋₊ + 1) - gumbelA ⌊T⌋₊|
        < (ε / 6) * gumbelB ⌊T⌋₊ := h3
      _ ≤ (ε / 6) * (2 * gumbelB (⌊T⌋₊ + 1)) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg hε.le (by norm_num))
      _ = (ε / 3) * gumbelB (⌊T⌋₊ + 1) := by ring)
  have hC : ∀ᶠ T : ℝ in atTop,
      (gumbelB ⌊T⌋₊ - gumbelB (⌊T⌋₊ + 1)) * |z| ≤ (ε / 3) * gumbelB (⌊T⌋₊ + 1) := by
    have h1 : ∀ᶠ T : ℝ in atTop,
        gumbelB ⌊T⌋₊ / gumbelB (⌊T⌋₊ + 1) < 1 + (ε / 3) / (|z| + 1) := by
      have h := (Metric.tendsto_nhds.mp gumbelB_ratio_inv_floor) ((ε / 3) / (|z| + 1))
        (by positivity)
      filter_upwards [h] with T hT
      rw [Real.dist_eq] at hT
      have h2 := (abs_lt.mp hT).2
      linarith [h2]
    filter_upwards [h1, hN2] with T h1 hN
    have hb1 := gumbelB_pos (by omega : 2 ≤ ⌊T⌋₊ + 1)
    have h3 : (ε / 3) / (|z| + 1) * |z| ≤ ε / 3 := by
      have hz1 : (0 : ℝ) < |z| + 1 := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hz1]
      exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg z])
        (div_nonneg hε.le (by norm_num))
    have h5 : gumbelB ⌊T⌋₊ - gumbelB (⌊T⌋₊ + 1) <
        ((ε / 3) / (|z| + 1)) * gumbelB (⌊T⌋₊ + 1) := by
      rw [div_lt_iff₀ hb1] at h1
      linarith [h1]
    calc (gumbelB ⌊T⌋₊ - gumbelB (⌊T⌋₊ + 1)) * |z|
        ≤ ((ε / 3) / (|z| + 1)) * gumbelB (⌊T⌋₊ + 1) * |z| :=
          mul_le_mul_of_nonneg_right h5.le (abs_nonneg z)
      _ = ((ε / 3) / (|z| + 1) * |z|) * gumbelB (⌊T⌋₊ + 1) := by ring
      _ ≤ (ε / 3) * gumbelB (⌊T⌋₊ + 1) := mul_le_mul_of_nonneg_right h3 hb1.le
  filter_upwards [hA, hB, hC, hN2, eventually_ge_atTop (2 : ℝ)] with T hA hB hC hN hT2
  obtain ⟨hsq1, hsq2⟩ := gumbelBR_squeeze hT2
  have hdecomp : gumbelUR T z - gumbelU (⌊T⌋₊ + 1) (z + ε) =
      (gumbelAR T - gumbelA (⌊T⌋₊ + 1)) + (gumbelBR T - gumbelB (⌊T⌋₊ + 1)) * z -
        ε * gumbelB (⌊T⌋₊ + 1) := by
    unfold gumbelUR gumbelU
    ring
  rw [← sub_nonpos, hdecomp]
  have h1 : gumbelAR T - gumbelA (⌊T⌋₊ + 1) ≤ (2 * ε / 3) * gumbelB (⌊T⌋₊ + 1) := by
    have e1 : gumbelAR T - gumbelA (⌊T⌋₊ + 1) =
        (gumbelAR T - gumbelA ⌊T⌋₊) - (gumbelA (⌊T⌋₊ + 1) - gumbelA ⌊T⌋₊) := by ring
    have e2 := (abs_le.mp hA).2
    have e3 := (abs_le.mp hB).1
    linarith [e1, e2, e3]
  have h2 : (gumbelBR T - gumbelB (⌊T⌋₊ + 1)) * z ≤ (ε / 3) * gumbelB (⌊T⌋₊ + 1) := by
    have e1 : (0 : ℝ) ≤ gumbelBR T - gumbelB (⌊T⌋₊ + 1) := sub_nonneg.mpr hsq1
    have e2 : gumbelBR T - gumbelB (⌊T⌋₊ + 1) ≤ gumbelB ⌊T⌋₊ - gumbelB (⌊T⌋₊ + 1) :=
      sub_le_sub_right hsq2 _
    calc (gumbelBR T - gumbelB (⌊T⌋₊ + 1)) * z
        ≤ (gumbelBR T - gumbelB (⌊T⌋₊ + 1)) * |z| :=
          mul_le_mul_of_nonneg_left (le_abs_self z) e1
      _ ≤ (gumbelB ⌊T⌋₊ - gumbelB (⌊T⌋₊ + 1)) * |z| :=
          mul_le_mul_of_nonneg_right e2 (abs_nonneg z)
      _ ≤ (ε / 3) * gumbelB (⌊T⌋₊ + 1) := hC
  linarith [h1, h2]

/-- L2(c), lower inequality: for every `ε > 0`, eventually along the real
`T → ∞`, `u_{⌊T⌋₊}(z - ε) ≤ u_T(z)`. -/
lemma gumbelU_floor_eventually_le_gumbelUR (z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, gumbelU ⌊T⌋₊ (z - ε) ≤ gumbelUR T z := by
  have hN2 : ∀ᶠ T : ℝ in atTop, 2 ≤ ⌊T⌋₊ :=
    tendsto_nat_floor_atTop.eventually_ge_atTop 2
  have hA : ∀ᶠ T : ℝ in atTop,
      |gumbelAR T - gumbelA ⌊T⌋₊| ≤ (ε / 2) * gumbelB ⌊T⌋₊ := by
    have h1 : ∀ᶠ T : ℝ in atTop,
        |(gumbelAR T - gumbelA ⌊T⌋₊) / gumbelB ⌊T⌋₊| < ε / 2 := by
      have h := (Metric.tendsto_nhds.mp gumbelAR_sub_div_tendsto) (ε / 2) (by positivity)
      filter_upwards [h] with T hT
      rwa [Real.dist_eq, sub_zero] at hT
    filter_upwards [h1, hN2] with T h1 hN
    have hb := gumbelB_pos hN
    rw [abs_div, abs_of_pos hb] at h1
    have h3 : |gumbelAR T - gumbelA ⌊T⌋₊| < (ε / 2) * gumbelB ⌊T⌋₊ := by
      have h4 := mul_lt_mul_of_pos_right h1 hb
      rwa [div_mul_cancel₀ _ hb.ne'] at h4
    exact h3.le
  have hC : ∀ᶠ T : ℝ in atTop,
      (gumbelB ⌊T⌋₊ - gumbelB (⌊T⌋₊ + 1)) * |z| ≤ (ε / 2) * gumbelB ⌊T⌋₊ := by
    have h1 : ∀ᶠ T : ℝ in atTop,
        1 - (ε / 2) / (|z| + 1) < gumbelB (⌊T⌋₊ + 1) / gumbelB ⌊T⌋₊ := by
      have h := (Metric.tendsto_nhds.mp gumbelB_succ_ratio_floor) ((ε / 2) / (|z| + 1))
        (by positivity)
      filter_upwards [h] with T hT
      rw [Real.dist_eq] at hT
      have h2 := (abs_lt.mp hT).1
      linarith [h2]
    filter_upwards [h1, hN2] with T h1 hN
    have hb := gumbelB_pos hN
    have h3 : (ε / 2) / (|z| + 1) * |z| ≤ ε / 2 := by
      have hz1 : (0 : ℝ) < |z| + 1 := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hz1]
      exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg z])
        (div_nonneg hε.le (by norm_num))
    have h5 : gumbelB ⌊T⌋₊ - gumbelB (⌊T⌋₊ + 1) <
        ((ε / 2) / (|z| + 1)) * gumbelB ⌊T⌋₊ := by
      rw [lt_div_iff₀ hb] at h1
      linarith [h1]
    calc (gumbelB ⌊T⌋₊ - gumbelB (⌊T⌋₊ + 1)) * |z|
        ≤ ((ε / 2) / (|z| + 1)) * gumbelB ⌊T⌋₊ * |z| :=
          mul_le_mul_of_nonneg_right h5.le (abs_nonneg z)
      _ = ((ε / 2) / (|z| + 1) * |z|) * gumbelB ⌊T⌋₊ := by ring
      _ ≤ (ε / 2) * gumbelB ⌊T⌋₊ := mul_le_mul_of_nonneg_right h3 hb.le
  filter_upwards [hA, hC, hN2, eventually_ge_atTop (2 : ℝ)] with T hA hC hN hT2
  obtain ⟨hsq1, hsq2⟩ := gumbelBR_squeeze hT2
  have hdecomp : gumbelU ⌊T⌋₊ (z - ε) - gumbelUR T z =
      (gumbelA ⌊T⌋₊ - gumbelAR T) + (gumbelB ⌊T⌋₊ - gumbelBR T) * z -
        ε * gumbelB ⌊T⌋₊ := by
    unfold gumbelUR gumbelU
    ring
  rw [← sub_nonpos, hdecomp]
  have h1 : gumbelA ⌊T⌋₊ - gumbelAR T ≤ (ε / 2) * gumbelB ⌊T⌋₊ := by
    have e := (abs_le.mp hA).1
    linarith [e]
  have h2 : (gumbelB ⌊T⌋₊ - gumbelBR T) * z ≤ (ε / 2) * gumbelB ⌊T⌋₊ := by
    have e1 : (0 : ℝ) ≤ gumbelB ⌊T⌋₊ - gumbelBR T := sub_nonneg.mpr hsq2
    have e2 : gumbelB ⌊T⌋₊ - gumbelBR T ≤ gumbelB ⌊T⌋₊ - gumbelB (⌊T⌋₊ + 1) :=
      sub_le_sub_left hsq1 _
    calc (gumbelB ⌊T⌋₊ - gumbelBR T) * z
        ≤ (gumbelB ⌊T⌋₊ - gumbelBR T) * |z| :=
          mul_le_mul_of_nonneg_left (le_abs_self z) e1
      _ ≤ (gumbelB ⌊T⌋₊ - gumbelB (⌊T⌋₊ + 1)) * |z| :=
          mul_le_mul_of_nonneg_right e2 (abs_nonneg z)
      _ ≤ (ε / 2) * gumbelB ⌊T⌋₊ := hC
  linarith [h1, h2]

/-! ### L3/L4: the real-length continuum Gumbel limit -/

/-- The level-shift identity for the lower envelope: at index `N + 1`, the
level `w₂ N = (a_N - a_{N+1})/b_{N+1} + (b_N/b_{N+1})·(z - ε)` reproduces
`u_N (z - ε)`. -/
lemma gumbelU_succ_w₂ (z ε : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    gumbelU (N + 1) ((gumbelA N - gumbelA (N + 1)) / gumbelB (N + 1) +
      (gumbelB N / gumbelB (N + 1)) * (z - ε)) = gumbelU N (z - ε) := by
  have hb2 := (gumbelB_pos (by omega : 2 ≤ N + 1)).ne'
  unfold gumbelU
  field_simp [hb2]
  ring

/-- The level-shift identity for the upper envelope: at index `N`, the level
`w₁ N = (a_{N+1} - a_N)/b_N + (b_{N+1}/b_N)·(z + ε)` reproduces
`u_{N+1} (z + ε)`. -/
lemma gumbelU_w₁_succ (z ε : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    gumbelU N ((gumbelA (N + 1) - gumbelA N) / gumbelB N +
      (gumbelB (N + 1) / gumbelB N) * (z + ε)) = gumbelU (N + 1) (z + ε) := by
  have hb := (gumbelB_pos hN).ne'
  unfold gumbelU
  field_simp [hb]
  ring

/-- **Conditional Gumbel limit, real-length continuum form** (the paper's
main theorem, Theorem 1.1): for the continuum maximum `M_T = max_{x ∈ [0,T]} A(x)`, the
probabilities `ℙ(M_T ≤ u_T(z))` converge to `exp (-exp (-z))` as the REAL
`T → ∞`, conditionally on the Airy-specific inputs carried by `bundle`. The
proof squeezes the real-length event between the integer-length events at
`⌊T⌋₊` and `⌊T⌋₊ + 1` with levels `z ∓ ε` (the L2 squeeze
`gumbelU_floor_eventually_le_gumbelUR` / `gumbelUR_eventually_le_gumbelU_succ`)
and closes with the perturbed integer limit
`gumbel_limit_continuum_of_tendsto`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Airy1ContinuousMax P) (bundle : Airy1BlockExtremes P)
    (hY : bundle.Y = C.Y) (z : ℝ) :
    Tendsto (fun T : ℝ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T, C.A x ω ≤ gumbelUR T z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  have preal_mono : ∀ {s t : Set Ω}, s ⊆ t → P.real s ≤ P.real t :=
    fun h => ENNReal.toReal_mono (measure_ne_top P _) (measure_mono h)
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨ε, hε0, hε⟩ := exists_gumbelCDF_gt ha
    -- the lower-envelope level sequence `w₂ M = (a_{M-1} - a_M)/b_M + (b_{M-1}/b_M)(z-ε)`
    have hw₂ : Tendsto (fun N : ℕ => (gumbelA N - gumbelA (N + 1)) / gumbelB (N + 1) +
        (gumbelB N / gumbelB (N + 1)) * (z - ε)) atTop (𝓝 (z - ε)) := by
      have h := gumbelA_diff_succ_ratio.add
        (gumbelB_ratio_inv.mul (tendsto_const_nhds (x := z - ε)))
      simpa using h
    have hL1 := C.gumbel_limit_continuum_of_tendsto bundle hY (z - ε) _
      (hw₂.comp tendsto_nat_pred_atTop)
    have hL2 : Tendsto (fun N : ℕ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (↑(N + 1)),
        C.A x ω ≤ gumbelU (N + 1) ((gumbelA N - gumbelA (N + 1)) / gumbelB (N + 1) +
          (gumbelB N / gumbelB (N + 1)) * (z - ε))}) atTop
        (𝓝 (Real.exp (-Real.exp (-(z - ε))))) := by
      have h := hL1.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using h
    have hL3 : Tendsto (fun N : ℕ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (↑(N + 1)),
        C.A x ω ≤ gumbelU N (z - ε)}) atTop (𝓝 (Real.exp (-Real.exp (-(z - ε))))) := by
      apply Tendsto.congr' _ hL2
      filter_upwards [eventually_ge_atTop 2] with N hN
      rw [gumbelU_succ_w₂ z ε hN]
    have hL4 := hL3.comp tendsto_nat_floor_atTop
    filter_upwards [hL4.eventually (Ioi_mem_nhds hε),
      gumbelU_floor_eventually_le_gumbelUR z hε0, eventually_ge_atTop (0 : ℝ)]
      with T hT1 hT2 hT3
    refine hT1.trans_le (preal_mono ?_)
    intro ω hω x hx
    apply (hω x ?_).trans hT2
    rw [Set.mem_Icc] at hx ⊢
    have hle : T ≤ ((⌊T⌋₊ + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add_one]
      exact (Nat.lt_floor_add_one T).le
    exact ⟨hx.1, hx.2.trans hle⟩
  · obtain ⟨ε, hε0, hε⟩ := exists_gumbelCDF_lt hb
    have hw₁ : Tendsto (fun N : ℕ => (gumbelA (N + 1) - gumbelA N) / gumbelB N +
        (gumbelB (N + 1) / gumbelB N) * (z + ε)) atTop (𝓝 (z + ε)) := by
      have h := gumbelA_succ_diff.add
        (gumbelB_succ_ratio.mul (tendsto_const_nhds (x := z + ε)))
      simpa using h
    have hU1 := C.gumbel_limit_continuum_of_tendsto bundle hY (z + ε) _ hw₁
    have hU2 : Tendsto (fun N : ℕ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (↑N),
        C.A x ω ≤ gumbelU (N + 1) (z + ε)}) atTop
        (𝓝 (Real.exp (-Real.exp (-(z + ε))))) := by
      apply Tendsto.congr' _ hU1
      filter_upwards [eventually_ge_atTop 2] with N hN
      rw [gumbelU_w₁_succ z ε hN]
    have hU3 := hU2.comp tendsto_nat_floor_atTop
    filter_upwards [hU3.eventually (Iio_mem_nhds hε),
      gumbelUR_eventually_le_gumbelU_succ z hε0, eventually_ge_atTop (0 : ℝ)]
      with T hT1 hT2 hT3
    refine (preal_mono ?_).trans_lt hT1
    intro ω hω x hx
    apply (hω x ?_).trans hT2
    rw [Set.mem_Icc] at hx ⊢
    exact ⟨hx.1, hx.2.trans (Nat.floor_le hT3)⟩

/-- The normalized real-length event is pointwise equal to the `u_T(z)`
event, since `b_T > 0` for `T > 1` (`gumbelUR T z = gumbelAR T + gumbelBR T * z`). -/
theorem Airy1ContinuousMax.normalized_event_eq_real {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (C : Airy1ContinuousMax P) {T : ℝ}
    (hT : 1 < T) (z : ℝ) :
    {ω | ∀ x ∈ Set.Icc (0 : ℝ) T, (C.A x ω - gumbelAR T) / gumbelBR T ≤ z} =
      {ω | ∀ x ∈ Set.Icc (0 : ℝ) T, C.A x ω ≤ gumbelUR T z} := by
  ext ω
  constructor
  · intro h x hx
    have h1 := (div_le_iff₀ (gumbelBR_pos hT)).mp (h x hx)
    show C.A x ω ≤ gumbelAR T + gumbelBR T * z
    linarith
  · intro h x hx
    apply (div_le_iff₀ (gumbelBR_pos hT)).mpr
    have h1 : C.A x ω ≤ gumbelAR T + gumbelBR T * z := h x hx
    linarith

/-- The paper's exact normalized shape in real length: `(M_T - a_T)/b_T`
converges in law to the standard Gumbel distribution, conditionally on the
Airy-specific inputs carried by `bundle`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_normalized
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Airy1ContinuousMax P) (bundle : Airy1BlockExtremes P)
    (hY : bundle.Y = C.Y) (z : ℝ) :
    Tendsto (fun T : ℝ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (C.A x ω - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  apply Tendsto.congr' _ (C.gumbel_limit_continuum_real bundle hY z)
  filter_upwards [eventually_gt_atTop 1] with T hT
  rw [C.normalized_event_eq_real hT z]

end Airy1Gumbel
