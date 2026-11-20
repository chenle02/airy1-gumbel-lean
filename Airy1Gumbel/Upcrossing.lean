/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.MesoscopicCover
import Airy1Gumbel.MesoscopicInputs
import Mathlib.Probability.Distributions.Gaussian.Real

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal

namespace Airy1Gumbel

/-!
# Block-to-grid covering from a two-point upcrossing tail

Replaces the path-level `LocalModulusEstimate` in the block-to-grid step of the `mesoscopic`
field (`MesoscopicSpec.lean`) by the two-point fdd record `HighLevelUpcrossingTail`
(`ExternalInputs.lean`; a two-point estimate of Quastel–Remenik 2013, at a fixed lowest level)
plus path continuity (`Airy1ContinuousMax.path_cont`).

**The argument.** Fix a unit block `[j, j+1]`, the mesh `n`, the sub-intervals
`[g, g + 1/n]` with `g = gridPt j n k`, `k < n`, and a level `v`. If `Y_j > v`, some `t` in the
block has `A t > v`. Either the left grid point `g` of its sub-interval has `A g > v - 1` (the
grid term of `cover`), or `A g ≤ v - 1 < v < A t`, an upcrossing of the band `[v-1, v]`:
* (a) `exists_dyadic_gt_of_continuousOn`: by continuity, a dyadic point
  `g + m s 2^{-M}`, `m < 2^M`, has `A > v`;
* (b) `dyadic_chain_le` / `exists_bad_dyadic_step`: on `Z = bandClamp v ∘ A` (the clamp to
  `[v-1, v]`), `Z` rises by `1` from `g` to that point, while `∑_{i<M} upEta i < 1`; the
  binary-digit chain then has a step `x ↦ x + s 2^{-(i+1)}` at level `i` with a rise
  `> upEta i` (`upEta i = (1/4)(3/4)^i`);
* (c) `exists_level_of_bandClamp_gap`: a rise of the clamp by `> η` gives a mesh level
  `a = v - 1 + r η/2 ≥ v - 1` with `A x ≤ a` and `A (x + h) > a + η/2`;
* (d) the record bounds each such two-point event; (e) the union over levels, dyadic
  positions and mesh levels is geometric (`upLevel_term_le`,
  `measureReal_iUnion_le_of_le_geom`), so each sub-interval fails with probability
  `≤ 2 upD n = O(n^K e^{-c₁ n/32})`, eventually `≤ modFail 1 1 n = e^{-√n}`.

Only forward time and levels `≥ v - 1` enter, and `A` is evaluated only at times in
`[0, ∞)`. The result `cover_of_upcrossing` is the level-thresholded `cover` field of
`MesoscopicBounds` (threshold `a₀ + 1`), with `modC = modc = 1`.

Non-vacuity witnesses and refutations for the record are at the end of the file.
-/

/-! ## Definitions -/

section Defs

/-- The gap budget at dyadic level `i`: `η_i = (1/4)(3/4)^i`, so `∑_i η_i = 1` and
`η_i² 2^i = (1/16)(9/8)^i` grows. -/
noncomputable def upEta (i : ℕ) : ℝ := 1 / 4 * (3 / 4) ^ i

/-- The clamp of `t` to the band `[v - 1, v]`. -/
noncomputable def bandClamp (v t : ℝ) : ℝ := max (v - 1) (min v t)

/-- The level-`i` failure set of the sub-interval `[g, g + s]` at level `v`: some dyadic
position `x = g + m s 2^{-i}` (`m < 2^i`) and some mesh level
`a = v - 1 + r η_i/2` (`r ≤ ⌈2/η_i⌉₊`) with `A x ≤ a` and `A (x + s 2^{-(i+1)}) > a + η_i/2`. -/
noncomputable def upLevel {Ω : Type*} (A : ℝ → Ω → ℝ) (g s v : ℝ) (i : ℕ) : Set Ω :=
  ⋃ m ∈ Finset.range (2 ^ i), ⋃ r ∈ Finset.range (⌈2 / upEta i⌉₊ + 1),
    {ω | A (g + m * (s / 2 ^ i)) ω ≤ v - 1 + r * (upEta i / 2) ∧
      v - 1 + r * (upEta i / 2) + upEta i / 2 < A (g + m * (s / 2 ^ i) + s / 2 ^ (i + 1)) ω}

/-- The upcrossing failure set of the sub-interval `[g, g + s]` at level `v`. -/
noncomputable def upBad {Ω : Type*} (A : ℝ → Ω → ℝ) (g s v : ℝ) : Set Ω :=
  ⋃ i : ℕ, upLevel A g s v i

/-- Geometric amplitude of the level bound at mesh `n` (`K = ⌈k⌉₊`). -/
noncomputable def upD (C k c₁ : ℝ) (n : ℕ) : ℝ :=
  10 * C * 2 ^ ⌈k⌉₊ * (n : ℝ) ^ ⌈k⌉₊ * Real.exp (-(c₁ / 32 * n))

/-- Geometric ratio of the level bound at mesh `n` (`K = ⌈k⌉₊`). -/
noncomputable def upRho (k c₁ : ℝ) (n : ℕ) : ℝ :=
  8 / 3 * 2 ^ ⌈k⌉₊ * Real.exp (-(c₁ / 256 * n))

end Defs

/-! ## The gap budget and the clamp -/

section Budget

theorem upEta_pos (i : ℕ) : 0 < upEta i := by
  unfold upEta
  positivity

/-- `∑_{i<M} η_i = 1 - (3/4)^M`. -/
theorem sum_upEta (M : ℕ) : ∑ i ∈ Finset.range M, upEta i = 1 - (3 / 4 : ℝ) ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, upEta, pow_succ]
    ring

/-- The partial sums of the budget stay below `1`. -/
theorem sum_upEta_lt_one (M : ℕ) : ∑ i ∈ Finset.range M, upEta i < 1 := by
  rw [sum_upEta]
  have : (0 : ℝ) < (3 / 4) ^ M := by positivity
  linarith

theorem bandClamp_of_le {v t : ℝ} (ht : t ≤ v - 1) : bandClamp v t = v - 1 := by
  unfold bandClamp
  rw [min_eq_right (by linarith)]
  exact max_eq_left ht

theorem bandClamp_of_ge {v t : ℝ} (ht : v ≤ t) : bandClamp v t = v := by
  unfold bandClamp
  rw [min_eq_left ht]
  exact max_eq_right (by linarith)

/-- **Level mesh (step (c)).** If the clamp to `[v-1, v]` rises by more than `η` from `p` to
`q`, then some mesh level `a = v - 1 + r η/2`, `r ≤ ⌈2/η⌉₊`, has `p ≤ a` and `q > a + η/2`. -/
theorem exists_level_of_bandClamp_gap {v η p q : ℝ} (hη : 0 < η)
    (h : η < bandClamp v q - bandClamp v p) :
    ∃ r ∈ Finset.range (⌈2 / η⌉₊ + 1),
      p ≤ v - 1 + r * (η / 2) ∧ v - 1 + r * (η / 2) + η / 2 < q := by
  have hq1 : bandClamp v q ≤ v := max_le (by linarith) (min_le_left _ _)
  have hp0 : v - 1 ≤ bandClamp v p := le_max_left _ _
  have hp1 : bandClamp v p ≤ v := max_le (by linarith) (min_le_left _ _)
  have hpv : p ≤ v := by
    by_contra hpv
    push_neg at hpv
    have := bandClamp_of_ge hpv.le
    linarith
  have hpz : p ≤ bandClamp v p := by
    unfold bandClamp
    rw [min_eq_right hpv]
    exact le_max_right _ _
  have hqz : bandClamp v q ≤ q := by
    rcases le_total (min v q) (v - 1) with hc | hc
    · have : bandClamp v q = v - 1 := max_eq_left hc
      linarith
    · have : bandClamp v q = min v q := max_eq_right hc
      rw [this]
      exact min_le_right _ _
  have hη2 : 0 < η / 2 := by linarith
  set z := bandClamp v p with hz
  set y := (z - (v - 1)) / (η / 2) with hy
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hη2.le
  have hyz : y * (η / 2) = z - (v - 1) := div_mul_cancel₀ _ hη2.ne'
  have hr1 : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have hr2 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  refine ⟨⌈y⌉₊, ?_, ?_, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.ceil_mono
    rw [hy, div_le_iff₀ hη2]
    have : 2 / η * (η / 2) = 1 := by field_simp
    linarith
  · have := mul_le_mul_of_nonneg_right hr1 hη2.le
    linarith
  · have := mul_lt_mul_of_pos_right hr2 hη2
    linarith

end Budget

/-! ## The dyadic chain (step (b)) -/

section Chain

/-- **Binary-digit chain.** If at every level `i < M` every step from a level-`i` dyadic
point `g + m s 2^{-i}` to its right child `g + m s 2^{-i} + s 2^{-(i+1)}` raises `F` by at most
`η i`, then every level-`M` dyadic point `g + m s 2^{-M}`, `m < 2^M`, has
`F (·) - F g ≤ ∑_{i<M} η i`. -/
theorem dyadic_chain_le (F : ℝ → ℝ) (g s : ℝ) (η : ℕ → ℝ) (hη : ∀ i, 0 ≤ η i) :
    ∀ M : ℕ, (∀ i < M, ∀ m : ℕ, m < 2 ^ i →
      F (g + m * (s / 2 ^ i) + s / 2 ^ (i + 1)) - F (g + m * (s / 2 ^ i)) ≤ η i) →
    ∀ m : ℕ, m < 2 ^ M → F (g + m * (s / 2 ^ M)) - F g ≤ ∑ i ∈ Finset.range M, η i := by
  intro M
  induction M with
  | zero =>
    intro _ m hm
    have : m = 0 := by simpa using hm
    subst this
    simp
  | succ M ih =>
    intro hgood m hm
    have hgood' : ∀ i < M, ∀ m : ℕ, m < 2 ^ i →
        F (g + m * (s / 2 ^ i) + s / 2 ^ (i + 1)) - F (g + m * (s / 2 ^ i)) ≤ η i :=
      fun i hi => hgood i (Nat.lt_succ_of_lt hi)
    rw [Finset.sum_range_succ]
    have hpow : (2 : ℕ) ^ (M + 1) = 2 * 2 ^ M := by rw [pow_succ]; ring
    rcases Nat.even_or_odd' m with ⟨m', rfl | rfl⟩
    · have hm' : m' < 2 ^ M := by rw [hpow] at hm; omega
      have IH := ih hgood' m' hm'
      have hpt : g + ((2 * m' : ℕ) : ℝ) * (s / 2 ^ (M + 1)) = g + (m' : ℝ) * (s / 2 ^ M) := by
        push_cast
        rw [pow_succ]
        field_simp
      rw [hpt]
      linarith [hη M]
    · have hm' : m' < 2 ^ M := by rw [hpow] at hm; omega
      have IH := ih hgood' m' hm'
      have hstep := hgood M (Nat.lt_succ_self M) m' hm'
      have hpt : g + ((2 * m' + 1 : ℕ) : ℝ) * (s / 2 ^ (M + 1)) =
          g + (m' : ℝ) * (s / 2 ^ M) + s / 2 ^ (M + 1) := by
        push_cast
        rw [pow_succ]
        field_simp
        ring
      rw [hpt]
      linarith

/-- Contrapositive of `dyadic_chain_le`: a rise above the budget forces a bad step. -/
theorem exists_bad_dyadic_step (F : ℝ → ℝ) (g s : ℝ) (η : ℕ → ℝ) (hη : ∀ i, 0 ≤ η i)
    {M m : ℕ} (hm : m < 2 ^ M)
    (hgap : ∑ i ∈ Finset.range M, η i < F (g + m * (s / 2 ^ M)) - F g) :
    ∃ i < M, ∃ m' : ℕ, m' < 2 ^ i ∧
      η i < F (g + m' * (s / 2 ^ i) + s / 2 ^ (i + 1)) - F (g + m' * (s / 2 ^ i)) := by
  by_contra hcon
  push_neg at hcon
  have := dyadic_chain_le F g s η hη M hcon m hm
  linarith

end Chain

/-! ## Pathwise reduction (steps (a)-(c)) -/

section Pathwise

/-- **Dyadic witness (step (a)).** If `f` is continuous on `[0, ∞)`, `0 ≤ g ≤ t < g + s` and
`f t > v`, then some dyadic point `g + m s 2^{-M}`, `m < 2^M`, has `f > v`. -/
theorem exists_dyadic_gt_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0))
    {g s t v : ℝ} (hg : 0 ≤ g) (hs : 0 < s) (hgt : g ≤ t) (hts : t < g + s) (hv : v < f t) :
    ∃ M : ℕ, ∃ m : ℕ, m < 2 ^ M ∧ v < f (g + m * (s / 2 ^ M)) := by
  have ht0 : t ∈ Ici (0 : ℝ) := le_trans hg hgt
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.continuousWithinAt_iff.mp (hf t ht0) (f t - v) (by linarith)
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (s / δ) (by norm_num : (1 : ℝ) < 2)
  have h2M : (0 : ℝ) < 2 ^ M := by positivity
  have hw0 : 0 < s / 2 ^ M := by positivity
  have hwδ : s / 2 ^ M < δ := by
    rw [div_lt_iff₀ h2M]
    rw [div_lt_iff₀ hδ] at hM
    linarith
  have hx0 : 0 ≤ (t - g) / (s / 2 ^ M) := div_nonneg (by linarith) hw0.le
  have hmle : (⌊(t - g) / (s / 2 ^ M)⌋₊ : ℝ) ≤ (t - g) / (s / 2 ^ M) := Nat.floor_le hx0
  have hmlt : (t - g) / (s / 2 ^ M) < ⌊(t - g) / (s / 2 ^ M)⌋₊ + 1 := Nat.lt_floor_add_one _
  refine ⟨M, ⌊(t - g) / (s / 2 ^ M)⌋₊, ?_, ?_⟩
  · rw [Nat.floor_lt hx0, div_lt_iff₀ hw0]
    push_cast
    rw [show (2 : ℝ) ^ M * (s / 2 ^ M) = s by field_simp]
    linarith
  · set m := ⌊(t - g) / (s / 2 ^ M)⌋₊
    set w := s / 2 ^ M
    have h1 : (m : ℝ) * w ≤ t - g := by rwa [le_div_iff₀ hw0] at hmle
    have h2 : t - g < (m : ℝ) * w + w := by
      rw [div_lt_iff₀ hw0, add_mul, one_mul] at hmlt
      exact hmlt
    have hy0 : g + m * w ∈ Ici (0 : ℝ) := by
      show 0 ≤ g + m * w
      positivity
    have hd : dist (g + m * w) t < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
    have := hball hy0 hd
    rw [Real.dist_eq, abs_sub_lt_iff] at this
    linarith [this.2]

/-- **Pathwise upcrossing.** On a path continuous on `[0, ∞)`, an upcrossing
`A g ≤ v - 1 < v < A t` with `0 ≤ g ≤ t < g + s` puts the path in `upBad A g s v`. -/
theorem mem_upBad_of_cross {Ω : Type*} (A : ℝ → Ω → ℝ) {ω : Ω}
    (hcont : ContinuousOn (fun x => A x ω) (Ici 0)) {g s t v : ℝ} (hg : 0 ≤ g) (hs : 0 < s)
    (hgt : g ≤ t) (hts : t < g + s) (hlow : A g ω ≤ v - 1) (hv : v < A t ω) :
    ω ∈ upBad A g s v := by
  obtain ⟨M, m, hm, hy⟩ := exists_dyadic_gt_of_continuousOn hcont hg hs hgt hts hv
  have hgap : ∑ i ∈ Finset.range M, upEta i <
      (fun x => bandClamp v (A x ω)) (g + m * (s / 2 ^ M)) -
        (fun x => bandClamp v (A x ω)) g := by
    simp only
    rw [bandClamp_of_ge hy.le, bandClamp_of_le hlow]
    have := sum_upEta_lt_one M
    linarith
  obtain ⟨i, -, m', hm', hstep⟩ := exists_bad_dyadic_step (fun x => bandClamp v (A x ω)) g s
    upEta (fun i => (upEta_pos i).le) hm hgap
  obtain ⟨r, hr, h1, h2⟩ := exists_level_of_bandClamp_gap
    (p := A (g + m' * (s / 2 ^ i)) ω) (q := A (g + m' * (s / 2 ^ i) + s / 2 ^ (i + 1)) ω)
    (upEta_pos i) hstep
  simp only [upBad, upLevel, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  exact ⟨i, m', Finset.mem_range.mpr hm', r, hr, h1, h2⟩

/-- **Block reduction.** On a path continuous on `[0, ∞)`, if the block supremum of `[j, j+1]`
exceeds `v`, then either a grid point `gridPt j n k`, `k ≤ n`, has `A > v - 1`, or the
upcrossing set of a sub-interval `[gridPt j n k, gridPt j n k + 1/n]`, `k < n`, occurs. -/
theorem grid_or_upBad_of_block_gt {Ω : Type*} (A : ℝ → Ω → ℝ) {ω : Ω}
    (hcont : ContinuousOn (fun x => A x ω) (Ici 0)) {j n : ℕ} (hn : 0 < n) {y v : ℝ}
    (hy : y = sSup ((fun x => A x ω) '' Set.Icc (j : ℝ) (j + 1))) (hyv : v < y) :
    (∃ k ∈ Finset.range (n + 1), v - 1 < A (gridPt j n k) ω) ∨
      ∃ k ∈ Finset.range n, ω ∈ upBad A (gridPt j n k) (1 / (n : ℝ)) v := by
  rw [hy] at hyv
  have hne : ((fun x => A x ω) '' Set.Icc (j : ℝ) (j + 1)).Nonempty :=
    (Set.nonempty_Icc.mpr (by linarith : (j : ℝ) ≤ (j : ℝ) + 1)).image _
  obtain ⟨_, ⟨t, ht, rfl⟩, hvt⟩ := exists_lt_of_lt_csSup hne hyv
  have hvt : v < A t ω := hvt
  obtain ⟨ht0, ht1⟩ := ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ (n : ℝ) * (t - j) := mul_nonneg hnR.le (by linarith)
  have hkx : (⌊(n : ℝ) * (t - j)⌋₊ : ℝ) ≤ (n : ℝ) * (t - j) := Nat.floor_le hx0
  have hxk : (n : ℝ) * (t - j) < ⌊(n : ℝ) * (t - j)⌋₊ + 1 := Nat.lt_floor_add_one _
  have hcomm : (n : ℝ) * (t - j) = (t - j) * n := mul_comm _ _
  have hxn : (n : ℝ) * (t - j) ≤ n := by nlinarith
  set k := ⌊(n : ℝ) * (t - j)⌋₊ with hk
  have hkn : k ≤ n := by
    have : (k : ℝ) ≤ n := hkx.trans hxn
    exact_mod_cast this
  have hgle : gridPt j n k ≤ t := by
    unfold gridPt
    have : (k : ℝ) / n ≤ t - j := by
      rw [div_le_iff₀ hnR]
      linarith
    linarith
  have hglt : t < gridPt j n k + 1 / (n : ℝ) := by
    unfold gridPt
    have : t - j < ((k : ℝ) + 1) / n := by
      rw [lt_div_iff₀ hnR]
      linarith
    rw [add_div] at this
    linarith
  have hg0 : 0 ≤ gridPt j n k := by unfold gridPt; positivity
  rcases lt_or_eq_of_le hkn with hlt | heq
  · by_cases hlow : v - 1 < A (gridPt j n k) ω
    · exact Or.inl ⟨k, Finset.mem_range.mpr (by omega), hlow⟩
    · refine Or.inr ⟨k, Finset.mem_range.mpr hlt, ?_⟩
      exact mem_upBad_of_cross A hcont hg0 (by positivity) hgle hglt (not_lt.mp hlow) hvt
  · -- `k = n`: then `t = j + 1 = gridPt j n n`.
    refine Or.inl ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), ?_⟩
    have hgn : gridPt j n n = (j : ℝ) + 1 := by
      unfold gridPt
      rw [div_self hnR.ne']
    have hgk : gridPt j n k = gridPt j n n := by rw [heq]
    have htj : t = (j : ℝ) + 1 := by
      have := hgle
      rw [hgk, hgn] at this
      linarith
    rw [hgn, ← htj]
    linarith

end Pathwise

/-! ## Probability of the failure sets (steps (d)-(e)) -/

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Level bound (step (d)).** Under the record's two-point bound at levels `≥ a₀`, for
`v ≥ a₀ + 1` and `0 < s ≤ 1`, the level-`i` failure set has probability at most
`2^i (⌈2/η_i⌉₊ + 1) · C h_i^{-k} e^{-c₁ (η_i/2)² / h_i}`, `h_i = s 2^{-(i+1)}`. -/
theorem measureReal_upLevel_le (A : ℝ → Ω → ℝ) {a₀ C k c₁ : ℝ}
    (hrec : ∀ a : ℝ, a₀ ≤ a → ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ η : ℝ, 0 < η → ∀ x : ℝ,
      P.real {ω | A x ω ≤ a ∧ a + η < A (x + h) ω} ≤
        C * h ^ (-k) * Real.exp (-c₁ * η ^ 2 / h))
    {g s v : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hv : a₀ + 1 ≤ v) (i : ℕ) :
    P.real (upLevel A g s v i) ≤ ((2 : ℝ) ^ i * ((⌈2 / upEta i⌉₊ : ℝ) + 1)) *
      (C * (s / 2 ^ (i + 1)) ^ (-k) *
        Real.exp (-c₁ * (upEta i / 2) ^ 2 / (s / 2 ^ (i + 1)))) := by
  have hh0 : 0 < s / 2 ^ (i + 1) := by positivity
  have hh1 : s / 2 ^ (i + 1) ≤ 1 :=
    (div_le_self hs.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans hs1
  have hη : 0 < upEta i / 2 := by have := upEta_pos i; linarith
  set T := C * (s / 2 ^ (i + 1)) ^ (-k) *
    Real.exp (-c₁ * (upEta i / 2) ^ 2 / (s / 2 ^ (i + 1))) with hT
  have hterm : ∀ m ∈ Finset.range (2 ^ i), ∀ r ∈ Finset.range (⌈2 / upEta i⌉₊ + 1),
      P.real {ω | A (g + m * (s / 2 ^ i)) ω ≤ v - 1 + r * (upEta i / 2) ∧
        v - 1 + r * (upEta i / 2) + upEta i / 2 <
          A (g + m * (s / 2 ^ i) + s / 2 ^ (i + 1)) ω} ≤ T := by
    intro m _ r _
    refine hrec _ ?_ _ hh0 hh1 _ hη _
    have : (0 : ℝ) ≤ r * (upEta i / 2) := mul_nonneg (Nat.cast_nonneg r) hη.le
    linarith
  unfold upLevel
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  refine (Finset.sum_le_sum fun m hm => (measureReal_biUnion_finset_le _ _).trans
    (Finset.sum_le_sum fun r hr => hterm m hm r hr)).trans ?_
  rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range, nsmul_eq_mul,
    nsmul_eq_mul]
  push_cast
  exact le_of_eq (by ring)

/-- **Arithmetic of the level bound (step (e)).** At `s = 1/n`, `n ≥ 1`, the level-`i` bound
is at most `upD C k c₁ n · upRho k c₁ n ^ i`. -/
theorem upLevel_term_le {C k c₁ : ℝ} (hC : 0 < C) (hk : 0 ≤ k) (hc₁ : 0 < c₁) {n : ℕ}
    (hn : 1 ≤ n) (i : ℕ) :
    ((2 : ℝ) ^ i * ((⌈2 / upEta i⌉₊ : ℝ) + 1)) *
      (C * (1 / (n : ℝ) / 2 ^ (i + 1)) ^ (-k) *
        Real.exp (-c₁ * (upEta i / 2) ^ 2 / (1 / (n : ℝ) / 2 ^ (i + 1)))) ≤
      upD C k c₁ n * upRho k c₁ n ^ i := by
  set K := ⌈k⌉₊ with hK
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  -- (i) the mesh count
  have hxy : ((4 : ℝ) / 3) ^ i * (3 / 4) ^ i = 1 := by rw [← mul_pow]; norm_num
  have hy1 : (1 : ℝ) ≤ (4 / 3) ^ i := one_le_pow₀ (by norm_num)
  have h2η : 2 / upEta i = 8 * (4 / 3 : ℝ) ^ i := by
    rw [div_eq_iff (upEta_pos i).ne']
    unfold upEta
    linear_combination (-2 : ℝ) * hxy
  have hcount : (⌈2 / upEta i⌉₊ : ℝ) + 1 ≤ 10 * (4 / 3 : ℝ) ^ i := by
    have := Nat.ceil_lt_add_one (div_pos two_pos (upEta_pos i)).le
    rw [h2η] at this ⊢
    linarith
  -- (ii) the power of the lag
  set H := 1 / (n : ℝ) / 2 ^ (i + 1) with hH
  have hH0 : 0 < H := by positivity
  have hHinv : H⁻¹ = (n : ℝ) * 2 ^ (i + 1) := by rw [hH]; field_simp
  have hHinv1 : (1 : ℝ) ≤ H⁻¹ := by
    rw [hHinv]
    have : (1 : ℝ) ≤ 2 ^ (i + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hpow : H ^ (-k) ≤ (n : ℝ) ^ K * 2 ^ K * (2 ^ K) ^ i := by
    rw [Real.rpow_neg hH0.le, ← Real.inv_rpow hH0.le]
    calc H⁻¹ ^ k ≤ H⁻¹ ^ (K : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hHinv1 (Nat.le_ceil k)
      _ = H⁻¹ ^ K := Real.rpow_natCast _ _
      _ = (n : ℝ) ^ K * 2 ^ K * (2 ^ K) ^ i := by
          rw [hHinv, mul_pow, ← pow_mul, mul_comm (i + 1) K, pow_mul, pow_succ]
          ring
  -- (iii) the Gaussian factor
  have h98 : (((3 : ℝ) / 4) ^ i) ^ 2 * 2 ^ i = (9 / 8) ^ i := by
    rw [← pow_mul, mul_comm i 2, pow_mul, ← mul_pow]
    norm_num
  have hid : (upEta i / 2) ^ 2 / H = (n : ℝ) / 32 * (9 / 8 : ℝ) ^ i := by
    rw [← h98, hH]
    unfold upEta
    rw [pow_succ]
    field_simp
    ring
  have hbern : 1 + (i : ℝ) * (1 / 8) ≤ (9 / 8 : ℝ) ^ i := by
    have := one_add_mul_le_pow (a := (1 / 8 : ℝ)) (by norm_num) i
    norm_num at this ⊢
    linarith
  have hexp : Real.exp (-c₁ * (upEta i / 2) ^ 2 / H) ≤
      Real.exp (-(c₁ / 32 * n)) * Real.exp (-(c₁ / 256 * n)) ^ i := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, mul_div_assoc, hid]
    apply Real.exp_le_exp.mpr
    have hcn : 0 ≤ c₁ * n := by positivity
    have := mul_le_mul_of_nonneg_left hbern hcn
    nlinarith
  -- combine
  have h83 : ((8 : ℝ) / 3) ^ i = 2 ^ i * (4 / 3) ^ i := by rw [← mul_pow]; norm_num
  calc ((2 : ℝ) ^ i * ((⌈2 / upEta i⌉₊ : ℝ) + 1)) *
        (C * H ^ (-k) * Real.exp (-c₁ * (upEta i / 2) ^ 2 / H))
      ≤ ((2 : ℝ) ^ i * (10 * (4 / 3 : ℝ) ^ i)) *
        (C * ((n : ℝ) ^ K * 2 ^ K * (2 ^ K) ^ i) *
          (Real.exp (-(c₁ / 32 * n)) * Real.exp (-(c₁ / 256 * n)) ^ i)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hcount (by positivity))
          (mul_le_mul (mul_le_mul_of_nonneg_left hpow hC.le) hexp (Real.exp_pos _).le
            (mul_nonneg hC.le (by positivity)))
          (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hH0.le _)) (Real.exp_pos _).le)
          (by positivity)
    _ = upD C k c₁ n * upRho k c₁ n ^ i := by
        unfold upD upRho
        rw [← hK, mul_pow, mul_pow, h83]
        ring

/-- **Geometric countable union.** If `P(E i) ≤ D ρ^i` with `0 ≤ ρ ≤ 1/2`, then
`P(⋃ E i) ≤ 2 D` (outer measure; no measurability needed). -/
theorem measureReal_iUnion_le_of_le_geom (E : ℕ → Set Ω) {D ρ : ℝ} (hD : 0 ≤ D)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) (h : ∀ i, P.real (E i) ≤ D * ρ ^ i) :
    P.real (⋃ i, E i) ≤ 2 * D := by
  have hρ1 : ρ < 1 := by linarith
  have hsum : Summable fun i : ℕ => D * ρ ^ i :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left D
  have htsum : ∑' i : ℕ, D * ρ ^ i ≤ 2 * D := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    have h1 : (1 - ρ)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    nlinarith
  have hle : P (⋃ i, E i) ≤ ENNReal.ofReal (2 * D) := by
    calc P (⋃ i, E i) ≤ ∑' i, P (E i) := measure_iUnion_le _
      _ ≤ ∑' i, ENNReal.ofReal (D * ρ ^ i) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          rw [← ofReal_measureReal (measure_ne_top P (E i))]
          exact ENNReal.ofReal_le_ofReal (h i)
      _ = ENNReal.ofReal (∑' i : ℕ, D * ρ ^ i) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum).symm
      _ ≤ ENNReal.ofReal (2 * D) := ENNReal.ofReal_le_ofReal htsum
  exact ENNReal.toReal_le_of_le_ofReal (by linarith) hle

/-- The geometric ratio is eventually at most `1/2`. -/
theorem eventually_upRho_le (k : ℝ) {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∀ᶠ n : ℕ in atTop, upRho k c₁ n ≤ 1 / 2 := by
  have h1 : Tendsto (fun n : ℕ => c₁ / 256 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (8 / 3 * 2 ^ ⌈k⌉₊)
  rw [mul_zero] at h2
  filter_upwards [h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
  exact hn.le

/-- Twice the amplitude is eventually below `modFail 1 1 n = e^{-√n}`. -/
theorem eventually_two_upD_le (C k : ℝ) {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∀ᶠ n : ℕ in atTop, 2 * upD C k c₁ n ≤ modFail 1 1 n := by
  have hlim := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (⌈k⌉₊ : ℝ) (c₁ / 64)
    (by positivity)).comp tendsto_natCast_atTop_atTop).const_mul (20 * C * 2 ^ ⌈k⌉₊)
  rw [mul_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds one_pos),
    eventually_ge_atTop ⌈(64 / c₁) ^ 2⌉₊] with n h1 hn
  simp only [Function.comp_apply, Real.rpow_natCast] at h1
  have hsq : 64 / c₁ ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by positivity) (Nat.cast_nonneg n)]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hsn : Real.sqrt n ≤ c₁ / 64 * n := by
    have hs := Real.mul_self_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have h0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have : 1 ≤ c₁ / 64 * Real.sqrt n := by
      rw [div_le_iff₀ hc₁] at hsq
      linarith
    calc Real.sqrt n = 1 * Real.sqrt n := (one_mul _).symm
      _ ≤ (c₁ / 64 * Real.sqrt n) * Real.sqrt n := mul_le_mul_of_nonneg_right this h0
      _ = c₁ / 64 * n := by rw [mul_assoc, hs]
  have hE : Real.exp (-(c₁ / 64) * n) ≤ Real.exp (-Real.sqrt n) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsplit : 2 * upD C k c₁ n =
      (20 * C * 2 ^ ⌈k⌉₊ * ((n : ℝ) ^ ⌈k⌉₊ * Real.exp (-(c₁ / 64) * n))) *
        Real.exp (-(c₁ / 64) * n) := by
    unfold upD
    rw [show -(c₁ / 32 * (n : ℝ)) = -(c₁ / 64) * n + -(c₁ / 64) * n by ring, Real.exp_add]
    ring
  have hmf : modFail 1 1 n = 1 * Real.exp (-Real.sqrt n) := by
    unfold modFail
    rw [div_one, neg_one_mul]
  rw [hsplit, hmf]
  exact mul_le_mul h1.le hE (Real.exp_pos _).le zero_le_one

/-- **Per-sub-interval failure bound.** Under the record's two-point bound, eventually in `n`,
for every left end `g` and every level `v ≥ a₀ + 1`,
`P(upBad A g (1/n) v) ≤ modFail 1 1 n`. -/
theorem eventually_measureReal_upBad_le (A : ℝ → Ω → ℝ) {a₀ C k c₁ : ℝ} (hC : 0 < C)
    (hk : 0 ≤ k) (hc₁ : 0 < c₁)
    (hrec : ∀ a : ℝ, a₀ ≤ a → ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ η : ℝ, 0 < η → ∀ x : ℝ,
      P.real {ω | A x ω ≤ a ∧ a + η < A (x + h) ω} ≤
        C * h ^ (-k) * Real.exp (-c₁ * η ^ 2 / h)) :
    ∀ᶠ n : ℕ in atTop, ∀ g v : ℝ, a₀ + 1 ≤ v →
      P.real (upBad A g (1 / (n : ℝ)) v) ≤ modFail 1 1 n := by
  filter_upwards [eventually_ge_atTop 1, eventually_upRho_le k hc₁,
    eventually_two_upD_le C k hc₁] with n hn1 hρ hD g v hv
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hD0 : 0 ≤ upD C k c₁ n := by
    unfold upD
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC.le) (by positivity))
      (by positivity)) (Real.exp_pos _).le
  have hρ0 : 0 ≤ upRho k c₁ n := by unfold upRho; positivity
  show P.real (⋃ i, upLevel A g (1 / (n : ℝ)) v i) ≤ _
  refine (measureReal_iUnion_le_of_le_geom _ hD0 hρ0 hρ fun i => ?_).trans hD
  exact (measureReal_upLevel_le A hrec (by positivity)
    (by rw [div_le_one (by linarith)]; exact hnR) hv i).trans (upLevel_term_le hC hk hc₁ hn1 i)

end Prob

/-! ## The level-thresholded block-to-grid covering -/

section Cover

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Block-to-grid covering from `HighLevelUpcrossingTail`** (replaces
`cover_of_LocalModulusEstimate`; the paper's block-to-grid reduction). There is a level
`v₀` (namely `a₀ + 1`) such that for all large `n`, uniformly in the block `j` and in the
levels `v ≥ v₀`,
`ℙ(Y₀ > v, Y_j > v) ≤ Σ_{k,k' ≤ n} ℙ(A(k/n) > v-1, A(j + k'/n) > v-1) + 2 (n+1) e^{-√n}`.
Inputs: the record and path continuity on `[0, ∞)` (`C.path_cont`); `A` is evaluated only at
times in `[0, ∞)`. This is the `cover` field of `MesoscopicBounds` with
`modC = modc = 1` and `coverLevel = v₀`. -/
theorem cover_of_upcrossing (C : Airy1ContinuousMax P) (X : StationaryRealProcess P)
    (hA : X.A = C.A) (U : HighLevelUpcrossingTail X) :
    ∃ v₀ : ℝ, ∀ᶠ n : ℕ in atTop, ∀ (j : ℕ) (v : ℝ), v₀ ≤ v →
      P.real {ω | C.Y 0 ω > v ∧ C.Y j ω > v} ≤
        (∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
          P.real {ω | C.A (gridPt 0 n k) ω > v - 1 ∧ C.A (gridPt j n k') ω > v - 1}) +
        2 * ((n : ℝ) + 1) * modFail 1 1 n := by
  obtain ⟨a₀, Cc, k, c₁, hC, hk, hc₁, hrec⟩ := U.tail
  rw [hA] at hrec
  refine ⟨a₀ + 1, ?_⟩
  filter_upwards [eventually_measureReal_upBad_le C.A hC hk hc₁ hrec, eventually_ge_atTop 1]
    with n hfail hn1 j v hv
  have hn : 0 < n := hn1
  have hmf0 : 0 ≤ modFail 1 1 n := by unfold modFail; positivity
  set G : Set Ω := ⋃ k ∈ Finset.range (n + 1), ⋃ k' ∈ Finset.range (n + 1),
    {ω | C.A (gridPt 0 n k) ω > v - 1 ∧ C.A (gridPt j n k') ω > v - 1} with hG
  set O₀ : Set Ω := ⋃ k ∈ Finset.range n, upBad C.A (gridPt 0 n k) (1 / (n : ℝ)) v with hO₀
  set Oⱼ : Set Ω := ⋃ k ∈ Finset.range n, upBad C.A (gridPt j n k) (1 / (n : ℝ)) v with hOⱼ
  have hsub : {ω | C.Y 0 ω > v ∧ C.Y j ω > v} ≤ᵐ[P] (G ∪ (O₀ ∪ Oⱼ) : Set Ω) := by
    filter_upwards [C.Y_eq, C.path_cont] with ω hω hcont hmem
    obtain ⟨h0, hj⟩ := hmem
    rcases grid_or_upBad_of_block_gt C.A hcont hn (hω 0) h0 with ⟨k, hk, hk'⟩ | ⟨k, hk, hk'⟩
    · rcases grid_or_upBad_of_block_gt C.A hcont hn (hω j) hj with
        ⟨k', hkj, hkj'⟩ | ⟨k', hkj, hkj'⟩
      · refine Or.inl ?_
        simp only [hG, Set.mem_iUnion]
        exact ⟨k, hk, k', hkj, hk', hkj'⟩
      · exact Or.inr (Or.inr (Set.mem_biUnion hkj hkj'))
    · exact Or.inr (Or.inl (Set.mem_biUnion hk hk'))
  have hmono : P.real {ω | C.Y 0 ω > v ∧ C.Y j ω > v} ≤ P.real (G ∪ (O₀ ∪ Oⱼ)) := by
    simp only [Measure.real]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hGle : P.real G ≤ ∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
      P.real {ω | C.A (gridPt 0 n k) ω > v - 1 ∧ C.A (gridPt j n k') ω > v - 1} :=
    (measureReal_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum fun k _ => measureReal_biUnion_finset_le _ _)
  have hOle : ∀ i : ℕ, P.real (⋃ k ∈ Finset.range n,
      upBad C.A (gridPt i n k) (1 / (n : ℝ)) v) ≤ ((n : ℝ) + 1) * modFail 1 1 n := by
    intro i
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hfail (gridPt i n k) v hv).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    nlinarith
  calc P.real {ω | C.Y 0 ω > v ∧ C.Y j ω > v}
      ≤ P.real (G ∪ (O₀ ∪ Oⱼ)) := hmono
    _ ≤ P.real G + (P.real O₀ + P.real Oⱼ) :=
        (measureReal_union_le _ _).trans (add_le_add_right (measureReal_union_le _ _) _)
    _ ≤ _ := by
        have h0 := hOle 0
        have hj := hOle j
        rw [← hO₀] at h0
        rw [← hOⱼ] at hj
        linarith

end Cover

/-! ## Audit witnesses for `HighLevelUpcrossingTail` (non-vacuity, refutation, falsity) -/

section Audit

/-- **Small-lag escape.** For `C, c₁, η > 0`, `k ≥ 0` and `p > 0` there is a lag
`0 < h ≤ 1` with `C h^{-k} e^{-c₁ η²/h} < p`: the record's envelope vanishes as `h → 0`. -/
theorem exists_lag_envelope_lt {C k c₁ η p : ℝ} (hc₁ : 0 < c₁) (hη : 0 < η) (hp : 0 < p) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ C * h ^ (-k) * Real.exp (-c₁ * η ^ 2 / h) < p := by
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k (c₁ * η ^ 2)
    (by positivity)).const_mul C
  rw [mul_zero] at hlim
  obtain ⟨y, hy⟩ := ((hlim.eventually (gt_mem_nhds hp)).and (eventually_ge_atTop 1)).exists
  obtain ⟨hyp, hy1⟩ := hy
  have hy0 : 0 < y := by linarith
  refine ⟨y⁻¹, inv_pos.mpr hy0, inv_le_one_of_one_le₀ hy1, ?_⟩
  have e1 : (y⁻¹) ^ (-k) = y ^ k := by
    rw [Real.rpow_neg (inv_nonneg.mpr hy0.le), Real.inv_rpow hy0.le, inv_inv]
  have e2 : -c₁ * η ^ 2 / y⁻¹ = -(c₁ * η ^ 2) * y := by
    rw [div_inv_eq_mul]
    ring
  rw [e1, e2, mul_assoc]
  exact hyp

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- **Non-vacuity of the schema.** The constant process satisfies the record: the event
`{0 ≤ a ∧ a + η < 0}` is empty for `a ≥ 0`, `η > 0`. -/
theorem highLevelUpcrossingTail_const : HighLevelUpcrossingTail (constZeroProcess P) := by
  refine ⟨⟨0, 1, 0, 1, one_pos, le_rfl, one_pos, fun a ha h hh _ η hη x => ?_⟩⟩
  have hempty : {ω : Ω | (constZeroProcess P).A x ω ≤ a ∧
      a + η < (constZeroProcess P).A (x + h) ω} = ∅ := by
    ext ω
    simp only [constZeroProcess, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_and, not_lt]
    intro _
    linarith
  rw [hempty, measureReal_empty]
  exact mul_nonneg (mul_nonneg zero_le_one (Real.rpow_nonneg hh.le _)) (Real.exp_pos _).le

/-- A time-constant process `A x = ξ` for a measurable random variable `ξ`. -/
def timeConstProcess {ξ : Ω → ℝ} (hξ : Measurable ξ) : StationaryRealProcess P where
  A := fun _ => ξ
  A_meas := fun _ => hξ
  stat := fun _ _ => rfl

/-- **Non-vacuity, nondegenerate.** Every time-constant process satisfies the record (a path that
does
not move never upcrosses), whatever the law of `ξ`. -/
theorem highLevelUpcrossingTail_timeConst {ξ : Ω → ℝ} (hξ : Measurable ξ) :
    HighLevelUpcrossingTail (timeConstProcess P hξ) := by
  refine ⟨⟨0, 1, 0, 1, one_pos, le_rfl, one_pos, fun a _ h hh _ η hη x => ?_⟩⟩
  have hempty : {ω : Ω | (timeConstProcess P hξ).A x ω ≤ a ∧
      a + η < (timeConstProcess P hξ).A (x + h) ω} = ∅ := by
    ext ω
    simp only [timeConstProcess, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_and, not_lt]
    intro h1
    linarith
  rw [hempty, measureReal_empty]
  exact mul_nonneg (mul_nonneg zero_le_one (Real.rpow_nonneg hh.le _)) (Real.exp_pos _).le

/-- **The orientation-flipped variant** (`a ≤ A x` in place of `A x ≤ a`), i.e. the
record without the upcrossing. -/
def FlippedUpcrossingTail (X : StationaryRealProcess P) : Prop :=
  ∃ a₀ C k c₁ : ℝ, 0 < C ∧ 0 ≤ k ∧ 0 < c₁ ∧
    ∀ a : ℝ, a₀ ≤ a → ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ η : ℝ, 0 < η → ∀ x : ℝ,
      P.real {ω | a ≤ X.A x ω ∧ a + η < X.A (x + h) ω} ≤
        C * h ^ (-k) * Real.exp (-c₁ * η ^ 2 / h)

/-- Under the standard Gaussian, every set of positive Lebesgue measure has positive
probability. -/
theorem gaussianReal_real_pos {S : Set ℝ} (hS : volume S ≠ 0) :
    0 < (gaussianReal 0 1).real S :=
  ENNReal.toReal_pos (fun h0 => hS ((gaussianReal_absolutelyContinuous' 0 one_ne_zero) h0))
    (measure_ne_top _ _)

/-- **Refutation of the orientation-flipped variant.** On the time-constant standard Gaussian
process
(on which the record itself holds, `highLevelUpcrossingTail_timeConst`), the orientation-flipped
variant fails: its event is `{ξ > a + η}`, of positive probability independent of the lag. -/
theorem not_flippedUpcrossingTail_timeConst :
    ¬ FlippedUpcrossingTail (gaussianReal 0 1) (timeConstProcess (gaussianReal 0 1)
      (measurable_id : Measurable (fun x : ℝ => x))) := by
  rintro ⟨a₀, C, k, c₁, hC, hk, hc₁, hb⟩
  have hp : 0 < (gaussianReal 0 1).real (Ioi (a₀ + 1)) := gaussianReal_real_pos (by simp)
  obtain ⟨h, hh0, hh1, hlt⟩ := exists_lag_envelope_lt (C := C) (k := k) hc₁ one_pos hp
  have := hb a₀ le_rfl h hh0 hh1 1 one_pos 0
  have hset : {ω : ℝ | a₀ ≤ (timeConstProcess (gaussianReal 0 1)
      (measurable_id : Measurable (fun x : ℝ => x))).A 0 ω ∧
      a₀ + 1 < (timeConstProcess (gaussianReal 0 1)
        (measurable_id : Measurable (fun x : ℝ => x))).A (0 + h) ω} = Ioi (a₀ + 1) := by
    ext ω
    simp only [timeConstProcess, id, Set.mem_ofPred_eq, Set.mem_Ioi]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by linarith, h⟩
  rw [hset] at this
  linarith

/-- The **independent switch process** on `ℝ × ℝ` under the product of two standard Gaussians:
`A x = ω.1` for `x ≤ 0` and `A x = ω.2` for `x > 0`. Every one-dimensional marginal is standard
Gaussian, but the values on the two sides of `0` are independent. -/
noncomputable def switchProcess :
    StationaryRealProcess ((gaussianReal 0 1).prod (gaussianReal 0 1)) where
  A := fun x ω => if x ≤ 0 then ω.1 else ω.2
  A_meas := fun x => by
    by_cases hx : x ≤ 0
    · simp only [hx, ↓reduceIte]
      exact measurable_fst
    · simp only [hx, ↓reduceIte]
      exact measurable_snd
  stat := fun x s => by
    have hm : ∀ y : ℝ, ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun ω : ℝ × ℝ => if y ≤ 0 then ω.1 else ω.2) = gaussianReal 0 1 := by
      intro y
      by_cases hy : y ≤ 0
      · simp only [hy, ↓reduceIte]
        rw [Measure.map_fst_prod, measure_univ, one_smul]
      · simp only [hy, ↓reduceIte]
        rw [Measure.map_snd_prod, measure_univ, one_smul]
    rw [hm, hm]

/-- **Falsity witness (the record is not trivially true).** The independent switch process
violates the record: at `x = 0`, every lag `h > 0` gives
`ℙ(A 0 ≤ a, A h > a + η) = Φ(a) (1 - Φ(a + η)) > 0`, independent of `h`, while the envelope
`C h^{-k} e^{-c₁ η²/h} → 0`. -/
theorem not_highLevelUpcrossingTail_switch : ¬ HighLevelUpcrossingTail switchProcess := by
  rintro ⟨a₀, C, k, c₁, hC, hk, hc₁, hb⟩
  set μ := gaussianReal 0 1
  have hp1 : 0 < μ.real (Iic a₀) := gaussianReal_real_pos (by simp)
  have hp2 : 0 < μ.real (Ioi (a₀ + 1)) := gaussianReal_real_pos (by simp)
  obtain ⟨h, hh0, hh1, hlt⟩ :=
    exists_lag_envelope_lt (C := C) (k := k) hc₁ one_pos (mul_pos hp1 hp2)
  have := hb a₀ le_rfl h hh0 hh1 1 one_pos 0
  have hh : ¬ (0 + h ≤ 0) := by linarith
  have hset : {ω : ℝ × ℝ | switchProcess.A 0 ω ≤ a₀ ∧ a₀ + 1 < switchProcess.A (0 + h) ω} =
      Iic a₀ ×ˢ Ioi (a₀ + 1) := by
    ext ω
    simp only [switchProcess, le_refl, hh, ↓reduceIte, Set.mem_ofPred_eq,
      Set.mem_prod, Set.mem_Iic, Set.mem_Ioi]
  rw [hset, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul] at this
  rw [measureReal_def] at hp1 hp2
  rw [measureReal_def, measureReal_def] at hlt
  linarith

end Audit

end Airy1Gumbel
