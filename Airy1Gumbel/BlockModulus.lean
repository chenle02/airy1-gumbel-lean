/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.ContinuousInstance

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Airy1Gumbel

/-- The transferred local oscillation estimate (4.2) in arXiv:2611.23658v1, on windows
contained in `[0, ∞)`. The bound is uniform in centres `c ≥ s` and in radii `0 < s ≤ 1`,
for all sufficiently large `ℓ`.

This is the paper's transferred estimate: it uses Basu–Bhattacharjee, Lemma 5.1 with
`ε = 2/3` and Theorem 1.4, followed by deterministic Airy₁ rescaling, a Portmanteau
argument for the strict exceedance, and translation by stationarity. The time
rescaling changes the radius cap: choose the prelimit cap `s₀ ≥ 2^{2/3}` to cover
Airy₁ radii `s ≤ 1`.
The record is not a verbatim Basu–Bhattacharjee statement.
It must not be cited as "BB2024 Lemma 5.1". Cite equation (4.2) of arXiv:2611.23658v1.

The intended Airy₁ instance is the continuous version `airy1SRP`. The record is
uninhabited on the raw coordinate process `airy1Process`, whose oscillation event
on a positive-length window has outer measure one on the product σ-algebra. -/
structure NonnegativeWindowModulusEstimate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ℝ → Ω → ℝ) where
  /-- The positive threshold and amplitude constant. -/
  C₀ : ℝ
  C₀_pos : 0 < C₀
  /-- The positive exponential rate. -/
  c₀ : ℝ
  c₀_pos : 0 < c₀
  /-- The strict oscillation event on a window of radius `s` and centre `c`. -/
  bound : ∀ᶠ ℓ : ℝ in atTop, ∀ c s : ℝ, 0 < s → s ≤ 1 → s ≤ c →
    P.real {ω | ∃ t₁ t₂ : ℝ, |t₁ - c| ≤ s ∧ |t₂ - c| ≤ s ∧
        C₀ * ℓ * Real.sqrt s < |A t₁ ω - A t₂ ω|}
      ≤ C₀ * Real.exp (-c₀ * ℓ)

/-- The constant zero process satisfies the local modulus estimate. -/
theorem nonnegativeWindowModulusEstimate_const {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    Nonempty (NonnegativeWindowModulusEstimate P (fun (_ : ℝ) (_ : Ω) => (0 : ℝ))) := by
  refine ⟨⟨1, one_pos, 1, one_pos, ?_⟩⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with ℓ hℓ c s _ _ _
  have he : {ω : Ω | ∃ t₁ t₂ : ℝ, |t₁ - c| ≤ s ∧ |t₂ - c| ≤ s ∧
      1 * ℓ * Real.sqrt s < |(0 : ℝ) - 0|} = ∅ := by
    ext ω
    simp [not_lt_of_ge (mul_nonneg hℓ (Real.sqrt_nonneg s))]
  rw [he]
  simp
  positivity

/-- The deterministic quadratic process violates the uniform bound over centres. -/
theorem isEmpty_nonnegativeWindowModulusEstimate_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    IsEmpty (NonnegativeWindowModulusEstimate P (fun (t : ℝ) (_ : Ω) => t ^ 2)) := by
  refine ⟨fun L => ?_⟩
  have hlim : Tendsto (fun ℓ : ℝ => L.C₀ * Real.exp (-L.c₀ * ℓ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop L.c₀_pos)).const_mul L.C₀
  obtain ⟨ℓ, hbound, hsmall⟩ :=
    (L.bound.and (hlim.eventually (gt_mem_nhds one_pos))).exists
  let c := 1 + max 0 (L.C₀ * ℓ)
  have hc : 1 ≤ c := by dsimp [c]; linarith [le_max_left 0 (L.C₀ * ℓ)]
  have hlarge : L.C₀ * ℓ < 4 * c := by dsimp [c]; linarith [le_max_right 0 (L.C₀ * ℓ)]
  have he : {ω : Ω | ∃ t₁ t₂ : ℝ, |t₁ - c| ≤ 1 ∧ |t₂ - c| ≤ 1 ∧
      L.C₀ * ℓ * Real.sqrt 1 < |t₁ ^ 2 - t₂ ^ 2|} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    refine ⟨c + 1, c - 1, ?_, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> linarith
    · rw [abs_le]
      constructor <;> linarith
    · rw [Real.sqrt_one, mul_one]
      have hid : (c + 1) ^ 2 - (c - 1) ^ 2 = 4 * c := by ring
      rw [hid, abs_of_nonneg (by linarith)]
      exact hlarge
  have hb := hbound c 1 one_pos le_rfl hc
  change P.real {ω : Ω | ∃ t₁ t₂ : ℝ, |t₁ - c| ≤ 1 ∧ |t₂ - c| ≤ 1 ∧
      L.C₀ * ℓ * Real.sqrt 1 < |t₁ ^ 2 - t₂ ^ 2|} ≤ _ at hb
  rw [he, measureReal_univ] at hb
  exact (not_lt_of_ge hb) hsmall

/-- The block modulus estimate of Lemma 4.1, equation (4.1) of arXiv:2611.23658v1,
from the local estimate (4.2) on nonnegative windows. -/
theorem block_modulus_airy1 (h : Airy1FddPositive) (hT : GOELeftTail)
    (L : NonnegativeWindowModulusEstimate (airy1Law h) (airy1SRP h hT).A) :
    ∃ C c h₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < h₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ h₀ →
        (airy1Law h).real
          {f | ∃ x y : ℝ, x ∈ Icc (0 : ℝ) 1 ∧ y ∈ Icc (0 : ℝ) 1 ∧
            |x - y| ≤ 2 * δ ∧ 1 < |airy1ContR h x f - airy1ContR h y f|}
          ≤ C * δ⁻¹ * Real.exp (-c * δ ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨ℓ₀, hcut⟩ := eventually_atTop.mp L.bound
  let m := max 1 ℓ₀
  have hm : 0 < m := one_pos.trans_le (le_max_left 1 ℓ₀)
  let b : ℝ := 1 / (2 * L.C₀ * m)
  have hb : 0 < b := by dsimp [b]; positivity [L.C₀_pos]
  refine ⟨2 * L.C₀, L.c₀ / (2 * L.C₀), min 1 (b ^ 2),
    by positivity [L.C₀_pos], by positivity [L.c₀_pos, L.C₀_pos],
    by positivity, ?_⟩
  intro δ hδ hδ0
  have hδ1 := hδ0.trans (min_le_left _ _)
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hroot : Real.sqrt δ ≤ b := (Real.sqrt_le_left hb.le).2
    (hδ0.trans (min_le_right _ _))
  let ℓ : ℝ := 1 / (2 * L.C₀ * Real.sqrt δ)
  have hℓ : m ≤ ℓ := by
    dsimp [ℓ]
    apply (le_div_iff₀ (by positivity [L.C₀_pos] : 0 < 2 * L.C₀ * Real.sqrt δ)).2
    calc
      m * (2 * L.C₀ * Real.sqrt δ) ≤ m * (2 * L.C₀ * b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hroot
          (by positivity [L.C₀_pos])) hm.le
      _ = 1 := by dsimp [b]; field_simp [L.C₀_pos.ne', hm.ne']
  have hthreshold : L.C₀ * ℓ * Real.sqrt δ = 1 / 2 := by
    dsimp [ℓ]
    field_simp [L.C₀_pos.ne', hsqrt.ne']
  let N := ⌊1 / (2 * δ)⌋₊ + 1
  let centre (k : ℕ) : ℝ := (2 * (k : ℝ) + 1) * δ
  let window (k : ℕ) : Set ℝ := Icc (2 * (k : ℝ) * δ) (2 * ((k : ℝ) + 1) * δ)
  have hwind {k : ℕ} {t : ℝ} (ht : t ∈ window k) : |t - centre k| ≤ δ := by
    obtain ⟨h1, h2⟩ := ht
    rw [abs_le]
    dsimp [centre, window] at *
    constructor <;> linarith
  have hindex (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      let k := ⌊t / (2 * δ)⌋₊
      k < N ∧ t ∈ window k := by
    dsimp
    have hpos : 0 < 2 * δ := by positivity
    have hf0 := Nat.floor_le (div_nonneg ht.1 hpos.le)
    have hf1 := Nat.lt_floor_add_one (t / (2 * δ))
    refine ⟨Nat.lt_succ_of_le (Nat.floor_mono
      (div_le_div_of_nonneg_right ht.2 hpos.le)), ?_⟩
    have hlo := (le_div_iff₀ hpos).1 hf0
    have hhi := (div_lt_iff₀ hpos).1 hf1
    exact ⟨by linarith, by linarith⟩
  have hordered (f : ℝ → ℝ) (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
      (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x ≤ y) (hgap : y - x ≤ 2 * δ)
      (hinc : 1 < |airy1ContR h x f - airy1ContR h y f|) :
      ∃ k ∈ Finset.range N, f ∈ oscEvent (airy1ContR h) (centre k) δ (1 / 2) := by
    let k := ⌊x / (2 * δ)⌋₊
    let j := ⌊y / (2 * δ)⌋₊
    obtain ⟨hk, hxk⟩ : k < N ∧ x ∈ window k := hindex x hx
    obtain ⟨hj, hyj⟩ : j < N ∧ y ∈ window j := hindex y hy
    have hpos : 0 < 2 * δ := by positivity
    have hkj : k ≤ j := Nat.floor_mono (div_le_div_of_nonneg_right hxy hpos.le)
    have hgap' : y / (2 * δ) ≤ x / (2 * δ) + 1 := by
      rw [show x / (2 * δ) + 1 = (x + 2 * δ) / (2 * δ) by field_simp]
      exact div_le_div_of_nonneg_right (by linarith) hpos.le
    have hlt : y / (2 * δ) < ((k + 2 : ℕ) : ℝ) := by
      have hxf : x / (2 * δ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
      push_cast
      linarith
    have hkj' : j < k + 2 := (Nat.floor_lt (div_nonneg hy.1 hpos.le)).2 hlt
    have hcases : j = k ∨ j = k + 1 := by omega
    rcases hcases with hjk | hjk
    · rw [hjk] at hyj
      exact ⟨k, Finset.mem_range.2 hk, x, y, hwind hxk, hwind hyj, by linarith⟩
    · let z : ℝ := 2 * ((k : ℝ) + 1) * δ
      have hzk : z ∈ window k := ⟨by dsimp [window, z]; linarith, le_rfl⟩
      have hzj : z ∈ window j := by
        rw [hjk]
        dsimp [window, z]
        push_cast
        exact ⟨le_rfl, by linarith⟩
      by_cases hl : 1 / 2 < |airy1ContR h x f - airy1ContR h z f|
      · exact ⟨k, Finset.mem_range.2 hk, x, z, hwind hxk, hwind hzk, hl⟩
      · have htri := abs_sub_le (airy1ContR h x f) (airy1ContR h z f) (airy1ContR h y f)
        exact ⟨j, Finset.mem_range.2 hj, z, y, hwind hzj, hwind hyj, by linarith [le_of_not_gt hl]⟩
  have hcover :
      {f | ∃ x y : ℝ, x ∈ Icc (0 : ℝ) 1 ∧ y ∈ Icc (0 : ℝ) 1 ∧
        |x - y| ≤ 2 * δ ∧ 1 < |airy1ContR h x f - airy1ContR h y f|} ⊆
      ⋃ k ∈ Finset.range N, oscEvent (airy1ContR h) (centre k) δ (1 / 2) := by
    rintro f ⟨x, y, hx, hy, hgap, hinc⟩
    simp only [mem_iUnion, exists_prop]
    rcases le_total x y with hxy | hyx
    · exact hordered f x y hx hy hxy (by linarith [neg_le_abs (x - y)]) hinc
    · rw [abs_sub_comm] at hinc
      exact hordered f y x hy hx hyx ((le_abs_self _).trans hgap) hinc
  have hprob (k : ℕ) :
      (airy1Law h).real (oscEvent (airy1ContR h) (centre k) δ (1 / 2)) ≤
        L.C₀ * Real.exp (-L.c₀ * ℓ) := by
    have hcentre : δ ≤ centre k := by
      dsimp [centre]
      nlinarith [show 0 ≤ (k : ℝ) from Nat.cast_nonneg k]
    have hk := hcut ℓ ((le_max_right 1 ℓ₀).trans hℓ) (centre k) δ hδ hδ1 hcentre
    change (airy1Law h).real (oscEvent (airy1ContR h) (centre k) δ
      (L.C₀ * ℓ * Real.sqrt δ)) ≤ _ at hk
    rwa [hthreshold] at hk
  have hN : (N : ℝ) ≤ 2 / δ := by
    have hfloor := Nat.floor_le (by positivity : 0 ≤ 1 / (2 * δ))
    have hdiv : 1 / (2 * δ) + 1 ≤ 2 / δ := by
      have he : (1 / (2 * δ) + 1) * δ = 1 / 2 + δ := by field_simp
      exact (le_div_iff₀ hδ).2 (by linarith)
    dsimp [N]
    push_cast
    exact (add_le_add_left hfloor 1).trans hdiv
  have hexp : -L.c₀ * ℓ = -(L.c₀ / (2 * L.C₀)) * δ ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hδ.le, ← Real.sqrt_eq_rpow]
    dsimp [ℓ]
    ring
  refine ((measureReal_mono hcover).trans
    (measureReal_biUnion_finset_le _ _)).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.range N, L.C₀ * Real.exp (-L.c₀ * ℓ) :=
      Finset.sum_le_sum fun k _ => hprob k
    _ = (N : ℝ) * (L.C₀ * Real.exp (-L.c₀ * ℓ)) := by simp
    _ ≤ (2 / δ) * (L.C₀ * Real.exp (-L.c₀ * ℓ)) :=
      mul_le_mul_of_nonneg_right hN (by positivity [L.C₀_pos])
    _ = _ := by rw [hexp]; ring

end Airy1Gumbel
