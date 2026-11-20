/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.MesoscopicSpec

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

namespace Airy1Gumbel

/-!
# Block-to-grid covering (for the `mesoscopic` field)

Lean form of the block-to-grid step of the paper's mesoscopic estimate (the local
Brownian-bridge modulus bound and the block-to-grid reduction; see the Lean form of the
step in `Airy1Gumbel/MesoscopicSpec.lean`). For a unit block `[j, j+1]` and a
mesh `n ≥ 1`, the centres are `gridPt j n k = j + k/n`, `k ≤ n`. If the block maximum
`Y_j` exceeds `v`, some `t ∈ [j, j+1]` has `A t > v` (`exists_lt_of_lt_csSup`; only
nonemptiness of the block is used, no `BddAbove`). The centre `k = ⌊n (t - j)⌋₊`
satisfies `k ≤ n` and `|t - gridPt j n k| ≤ 1/n`, so either `A (gridPt j n k) > v - 1`
or the oscillation event of radius `1/n` and threshold `1` occurs at that centre.
`LocalModulusEstimate` at `ℓ = √n / C₀`, `s = 1/n` (so `C₀ ℓ √s = 1`) bounds each
oscillation event by `modFail C₀ c₀ n`, and outer-measure subadditivity closes the
estimate. No measurability of any event is needed.
-/

/-- The grid centre `k = ⌊n (t - j)⌋₊` of a point `t ∈ [j, j+1]` lies in
`Finset.range (n + 1)` and is within `1/n` of `t` (the mesh of the paper's
block-to-grid step). -/
theorem gridPt_floor_mem_close {j n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc (j : ℝ) (j + 1)) :
    ⌊(n : ℝ) * (t - j)⌋₊ ∈ Finset.range (n + 1) ∧
      |t - gridPt j n ⌊(n : ℝ) * (t - j)⌋₊| ≤ 1 / (n : ℝ) := by
  obtain ⟨ht0, ht1⟩ := ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set x : ℝ := (n : ℝ) * (t - j) with hx
  have hx0 : 0 ≤ x := mul_nonneg hnR.le (by linarith)
  have hxn : x ≤ n := by
    have : t - j ≤ 1 := by linarith
    calc x = (n : ℝ) * (t - j) := rfl
      _ ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left this hnR.le
      _ = n := mul_one _
  have hk_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hk_lt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    have : (⌊x⌋₊ : ℝ) ≤ n := hk_le.trans hxn
    exact_mod_cast this
  · have hdiff : t - gridPt j n ⌊x⌋₊ = (x - ⌊x⌋₊) / n := by
      unfold gridPt
      rw [hx]
      field_simp
      ring
    rw [hdiff, abs_of_nonneg (div_nonneg (by linarith) hnR.le)]
    exact div_le_div_of_nonneg_right (by linarith) hnR.le

/-- If `A t > v` at some `t` within `s` of the centre `c`, then either
`A c > v - 1` or the oscillation event of radius `s` and threshold `1` occurs at `c`
(the case split of the block-to-grid step; threshold `C₀ ℓ √s = 1` in the local
modulus bound). -/
theorem gt_sub_one_or_mem_oscEvent {Ω : Type*} (A : ℝ → Ω → ℝ) {ω : Ω} {c s t v : ℝ}
    (hs : 0 ≤ s) (htc : |t - c| ≤ s) (hv : v < A t ω) :
    v - 1 < A c ω ∨ ω ∈ oscEvent A c s 1 := by
  by_cases h : v - 1 < A c ω
  · exact Or.inl h
  · refine Or.inr ⟨t, c, htc, by simpa using hs, ?_⟩
    rw [not_lt] at h
    rw [abs_of_pos (by linarith)]
    linarith

/-- On the a.e. event where `Y_j` is the block supremum, `Y_j > v` yields a grid
centre `k ≤ n` of block `j` with `A (gridPt j n k) > v - 1` or the oscillation event
at that centre (radius `1/n`, threshold `1`). Uses `exists_lt_of_lt_csSup`, which needs
only nonemptiness of `A '' [j, j+1]` (the paper's block-to-grid reduction). -/
theorem exists_grid_of_block_gt {Ω : Type*} (A : ℝ → Ω → ℝ) {ω : Ω} {j n : ℕ}
    (hn : 0 < n) {y v : ℝ}
    (hy : y = sSup ((fun x => A x ω) '' Set.Icc (j : ℝ) (j + 1))) (hyv : v < y) :
    ∃ k ∈ Finset.range (n + 1),
      v - 1 < A (gridPt j n k) ω ∨ ω ∈ oscEvent A (gridPt j n k) (1 / (n : ℝ)) 1 := by
  rw [hy] at hyv
  have hne : ((fun x => A x ω) '' Set.Icc (j : ℝ) (j + 1)).Nonempty :=
    (Set.nonempty_Icc.mpr (by linarith : (j : ℝ) ≤ (j : ℝ) + 1)).image _
  obtain ⟨_, ⟨t, ht, rfl⟩, hvt⟩ := exists_lt_of_lt_csSup hne hyv
  obtain ⟨hk, hclose⟩ := gridPt_floor_mem_close hn ht
  refine ⟨_, hk, gt_sub_one_or_mem_oscEvent A ?_ hclose hvt⟩
  positivity

/-- The modulus threshold at `ℓ = √n / C₀`, `s = 1/n` is exactly `1`:
`C₀ (√n / C₀) √(1/n) = 1` for `n ≥ 1` (the local modulus bound). -/
theorem modulus_threshold_eq_one {C₀ : ℝ} (hC₀ : 0 < C₀) {n : ℕ} (hn : 0 < n) :
    C₀ * (Real.sqrt n / C₀) * Real.sqrt (1 / (n : ℝ)) = 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  rw [Real.sqrt_div' 1 hnR.le, Real.sqrt_one]
  field_simp

/-- **Block-to-grid covering** (for the `mesoscopic` field; the paper's
block-to-grid reduction with the local Brownian-bridge modulus bound, in the Lean
form of `MesoscopicSpec.lean`). For all large `n`, uniformly in the block `j` and
the level `v`,
`ℙ(Y₀ > v, Y_j > v) ≤ Σ_{k,k' ≤ n} ℙ(A(k/n) > v-1, A(j + k'/n) > v-1)
  + 2 (n+1) C₀ e^{-c₀ √n / C₀}`.
It holds at every level `v`, so it gives the (level-thresholded) `cover` field of
`MesoscopicBounds` with `coverLevel := 0` (`MesoscopicBounds.ofRecords`). -/
theorem cover_of_LocalModulusEstimate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (C : Airy1ContinuousMax P)
    (X : StationaryRealProcess P) (hA : X.A = C.A) (L : LocalModulusEstimate X) :
    ∀ᶠ n : ℕ in atTop, ∀ (j : ℕ) (v : ℝ),
      P.real {ω | C.Y 0 ω > v ∧ C.Y j ω > v} ≤
        (∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
          P.real {ω | C.A (gridPt 0 n k) ω > v - 1 ∧ C.A (gridPt j n k') ω > v - 1}) +
        2 * ((n : ℝ) + 1) * modFail L.C₀ L.c₀ n := by
  -- `ℓ = √n / C₀ → ∞`, so `L.bound` holds at `ℓ = √n / C₀` for all large `n`.
  have hℓ : Tendsto (fun n : ℕ => Real.sqrt n / L.C₀) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const L.C₀_pos
  filter_upwards [hℓ.eventually L.bound, eventually_ge_atTop 1] with n hbound hn1 j v
  have hn : 0 < n := hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- Each oscillation event (radius `1/n`, threshold `1`) has probability `≤ modFail`.
  have hosc : ∀ c : ℝ, P.real (oscEvent C.A c (1 / (n : ℝ)) 1) ≤ modFail L.C₀ L.c₀ n := by
    intro c
    have hb := hbound c (1 / (n : ℝ)) (by positivity)
      (by rw [div_le_one hnR]; exact_mod_cast hn1)
    rw [modulus_threshold_eq_one L.C₀_pos hn, hA] at hb
    exact hb
  -- The covering sets.
  set G : Set Ω := ⋃ k ∈ Finset.range (n + 1), ⋃ k' ∈ Finset.range (n + 1),
    {ω | C.A (gridPt 0 n k) ω > v - 1 ∧ C.A (gridPt j n k') ω > v - 1} with hG
  set O₀ : Set Ω := ⋃ k ∈ Finset.range (n + 1), oscEvent C.A (gridPt 0 n k) (1 / (n : ℝ)) 1
    with hO₀
  set Oⱼ : Set Ω := ⋃ k ∈ Finset.range (n + 1), oscEvent C.A (gridPt j n k) (1 / (n : ℝ)) 1
    with hOⱼ
  -- A.e. inclusion of the block event in the covering.
  have hsub : {ω | C.Y 0 ω > v ∧ C.Y j ω > v} ≤ᵐ[P] (G ∪ (O₀ ∪ Oⱼ) : Set Ω) := by
    filter_upwards [C.Y_eq] with ω hω hmem
    obtain ⟨h0, hj⟩ := hmem
    obtain ⟨k, hk, hk'⟩ := exists_grid_of_block_gt C.A hn (hω 0) h0
    obtain ⟨k', hkj, hkj'⟩ := exists_grid_of_block_gt C.A hn (hω j) hj
    rcases hk' with hk' | hk'
    · rcases hkj' with hkj' | hkj'
      · refine Or.inl ?_
        simp only [hG, Set.mem_iUnion]
        exact ⟨k, hk, k', hkj, hk', hkj'⟩
      · exact Or.inr (Or.inr (Set.mem_biUnion hkj hkj'))
    · exact Or.inr (Or.inl (Set.mem_biUnion hk hk'))
  -- Subadditivity.
  have hmono : P.real {ω | C.Y 0 ω > v ∧ C.Y j ω > v} ≤ P.real (G ∪ (O₀ ∪ Oⱼ)) := by
    simp only [Measure.real]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hGle : P.real G ≤ ∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
      P.real {ω | C.A (gridPt 0 n k) ω > v - 1 ∧ C.A (gridPt j n k') ω > v - 1} :=
    (measureReal_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum fun k _ => measureReal_biUnion_finset_le _ _)
  have hOle : ∀ i : ℕ, P.real (⋃ k ∈ Finset.range (n + 1),
      oscEvent C.A (gridPt i n k) (1 / (n : ℝ)) 1) ≤ ((n : ℝ) + 1) * modFail L.C₀ L.c₀ n := by
    intro i
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hosc (gridPt i n k)).trans ?_
    simp
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

end Airy1Gumbel
