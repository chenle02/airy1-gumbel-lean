/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.BlockModulus
import Airy1Gumbel.TailSensitiveNewman

open Asymptotics Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology BigOperators

namespace Airy1Gumbel

/-- The strict unit-block oscillation event in equation (4.9) of arXiv:2611.23658v1. -/
def unit_block_oscillation_event (h : Airy1FddPositive) (j : ℕ) (δ : ℝ) :
    Set (ℝ → ℝ) :=
  {f | ∃ x y : ℝ, x ∈ Icc (j : ℝ) ((j : ℝ) + 1) ∧
      y ∈ Icc (j : ℝ) ((j : ℝ) + 1) ∧ |x - y| ≤ 2 * δ ∧
      1 < |airy1ContR h x f - airy1ContR h y f|}

/-- The oscillation event of Lemma 4.1 of arXiv:2611.23658v1 has the same probability on
every nonnegative integer translate of the unit block, under `Airy1FddPositive` and
`GOELeftTail`. This is shift invariance of the law; Lemma 4.1 itself is not used. -/
theorem block_oscillation_probability_shift_airy1 (h : Airy1FddPositive) (hT : GOELeftTail)
    (j : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    (airy1Law h).real (unit_block_oscillation_event h j δ) =
      (airy1Law h).real (unit_block_oscillation_event h 0 δ) := by
  let K : Set (ℝ × ℝ) :=
    {p | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 1 ∧ |p.1 - p.2| ≤ 2 * δ}
  have : Nonempty K := ⟨⟨(0, 0), by simp [K, hδ]⟩⟩
  let q := denseSeq K
  have hq : DenseRange q := denseRange_denseSeq K
  let D (i : ℕ) : Set (ℝ → ℝ) :=
    {f | ∃ n : ℕ, 1 < |f ((q n).1.1 + i) - f ((q n).1.2 + i)|}
  have hDm (i : ℕ) : MeasurableSet (D i) := by
    have he : D i = ⋃ n : ℕ, {f : ℝ → ℝ |
        1 < |f ((q n).1.1 + i) - f ((q n).1.2 + i)|} := by
      ext f
      simp only [D, mem_ofPred_eq, mem_iUnion]
    rw [he]
    refine MeasurableSet.iUnion fun n => measurableSet_lt measurable_const ?_
    have hm : Measurable fun f : ℝ → ℝ => f ((q n).1.1 + i) - f ((q n).1.2 + i) :=
      (measurable_pi_apply _).sub (measurable_pi_apply _)
    simpa only [Real.norm_eq_abs] using hm.norm
  have hae (i : ℕ) : unit_block_oscillation_event h i δ =ᵐ[airy1Law h] D i := by
    have hcoord : ∀ᵐ f ∂airy1Law h, ∀ n : ℕ,
        airy1ContR h ((q n).1.1 + i) f = f ((q n).1.1 + i) ∧
          airy1ContR h ((q n).1.2 + i) f = f ((q n).1.2 + i) := by
      rw [ae_all_iff]
      intro n
      exact (airy1ContR_ae_eq h hT _).and (airy1ContR_ae_eq h hT _)
    filter_upwards [hcoord] with f hf
    refine propext ?_
    change (∃ x y : ℝ, x ∈ Icc (i : ℝ) ((i : ℝ) + 1) ∧
      y ∈ Icc (i : ℝ) ((i : ℝ) + 1) ∧ |x - y| ≤ 2 * δ ∧
      1 < |airy1ContR h x f - airy1ContR h y f|) ↔ _
    let osc (p : K) := |airy1ContR h (p.1.1 + i) f - airy1ContR h (p.1.2 + i) f|
    have hosc : Continuous osc := by
      have h₁ : Continuous (fun p : K => airy1ContR h (p.1.1 + i) f) :=
        (continuousOn_airy1ContR h f).comp_continuous
          (continuous_subtype_val.fst.add continuous_const) (fun p => by
            change 0 ≤ p.1.1 + i
            exact add_nonneg p.property.1.1 (Nat.cast_nonneg _))
      have h₂ : Continuous (fun p : K => airy1ContR h (p.1.2 + i) f) :=
        (continuousOn_airy1ContR h f).comp_continuous
          (continuous_subtype_val.snd.add continuous_const) (fun p => by
            change 0 ≤ p.1.2 + i
            exact add_nonneg p.property.2.1.1 (Nat.cast_nonneg _))
      simpa only [osc, Real.norm_eq_abs, Pi.sub_apply] using (h₁.sub h₂).norm
    constructor
    · rintro ⟨x, y, hx, hy, hgap, hinc⟩
      let p : K := ⟨(x - (i : ℝ), y - (i : ℝ)), by
        refine ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
          ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
        change |x - (i : ℝ) - (y - (i : ℝ))| ≤ 2 * δ
        rwa [sub_sub_sub_cancel_right]⟩
      have hp : 1 < osc p := by simpa only [osc, p, sub_add_cancel] using hinc
      obtain ⟨n, hn⟩ := hq.exists_mem_open (isOpen_lt continuous_const hosc) ⟨p, hp⟩
      change 1 < |airy1ContR h ((q n).1.1 + i) f - airy1ContR h ((q n).1.2 + i) f| at hn
      rw [(hf n).1, (hf n).2] at hn
      exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩
      change 1 < |f ((q n).1.1 + i) - f ((q n).1.2 + i)| at hn
      rw [← (hf n).1, ← (hf n).2] at hn
      refine ⟨(q n).1.1 + i, (q n).1.2 + i,
        ⟨by linarith [(q n).property.1.1], by linarith [(q n).property.1.2]⟩,
        ⟨by linarith [(q n).property.2.1.1], by linarith [(q n).property.2.1.2]⟩,
        ?_, hn⟩
      rw [add_sub_add_right_eq_sub]
      exact (q n).property.2.2
  have hpre : timeShift (j : ℝ) ⁻¹' D 0 = D j := by
    ext f
    simp only [D, timeShift, mem_preimage, mem_ofPred_eq, Nat.cast_zero, add_zero]
  rw [measureReal_congr (hae j), measureReal_congr (hae 0), ← hpre, measureReal_def,
    airy1Law_timeShift_preimage h (j : ℝ) (hDm 0)]
  rfl

/-- Block-to-grid covering, equation (4.10) of arXiv:2611.23658v1. -/
theorem block_pair_grid_cover_airy1 (h : Airy1FddPositive) (j n : ℕ) (hn : 0 < n)
    (δ M : ℝ) (hmesh : 1 / (n : ℝ) ≤ 2 * δ) :
    (airy1Law h).real {f | M < airy1BlockMax h 0 f ∧ M < airy1BlockMax h j f} ≤
      (airy1Law h).real (unit_block_oscillation_event h 0 δ) +
      (airy1Law h).real (unit_block_oscillation_event h j δ) +
      ∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
        (airy1Law h).real {f | M - 1 < airy1ContR h (gridPt 0 n k) f ∧
          M - 1 < airy1ContR h (gridPt j n k') f} := by
  have hgrid (i : ℕ) (f : ℝ → ℝ) (hf : M < airy1BlockMax h i f)
      (hosc : f ∉ unit_block_oscillation_event h i δ) :
      ∃ k ∈ Finset.range (n + 1), M - 1 < airy1ContR h (gridPt i n k) f := by
    obtain ⟨q, hq, hvalue⟩ := (airy1BlockMax_gt_iff h i f M).mp hf
    have ht : (q : ℝ) + i ∈ Icc (i : ℝ) ((i : ℝ) + 1) :=
      ⟨by linarith [hq.1], by linarith [hq.2]⟩
    obtain ⟨hk, hd⟩ := gridPt_floor_mem_close hn ht
    let k := ⌊(n : ℝ) * ((q : ℝ) + i - i)⌋₊
    have hkN : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkR : (k : ℝ) ≤ n := by exact_mod_cast hkN
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hg : gridPt i n k ∈ Icc (i : ℝ) ((i : ℝ) + 1) := by
      have h0 : 0 ≤ (k : ℝ) / (n : ℝ) := by positivity
      have h1 : (k : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hnR).mpr hkR
      exact ⟨by unfold gridPt; linarith, by unfold gridPt; linarith⟩
    have hinc : |airy1ContR h ((q : ℝ) + i) f - airy1ContR h (gridPt i n k) f| ≤ 1 :=
      le_of_not_gt fun habs => hosc ⟨(q : ℝ) + i, gridPt i n k, ht, hg, hd.trans hmesh, habs⟩
    refine ⟨k, hk, ?_⟩
    linarith [le_abs_self (airy1ContR h ((q : ℝ) + i) f - airy1ContR h (gridPt i n k) f)]
  let E (k k' : ℕ) : Set (ℝ → ℝ) :=
    {f | M - 1 < airy1ContR h (gridPt 0 n k) f ∧ M - 1 < airy1ContR h (gridPt j n k') f}
  let G := ⋃ k ∈ Finset.range (n + 1), ⋃ k' ∈ Finset.range (n + 1), E k k'
  have hcover : {f | M < airy1BlockMax h 0 f ∧ M < airy1BlockMax h j f} ⊆
      (unit_block_oscillation_event h 0 δ ∪ unit_block_oscillation_event h j δ) ∪ G := by
    intro f hf
    by_cases h0 : f ∈ unit_block_oscillation_event h 0 δ
    · exact Or.inl (Or.inl h0)
    by_cases hj : f ∈ unit_block_oscillation_event h j δ
    · exact Or.inl (Or.inr hj)
    obtain ⟨k, hk, hv⟩ := hgrid 0 f hf.1 h0
    obtain ⟨k', hk', hv'⟩ := hgrid j f hf.2 hj
    apply Or.inr
    simp only [G, mem_iUnion]
    exact ⟨k, hk, k', hk', hv, hv'⟩
  have hG : (airy1Law h).real G ≤
      ∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1), (airy1Law h).real (E k k') :=
    (measureReal_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum fun k _ => measureReal_biUnion_finset_le _ _)
  calc
    _ ≤ _ := Airy1Gumbel.measureReal_mono hcover
    _ ≤ _ := MeasureTheory.measureReal_union_le _ _
    _ ≤ _ := add_le_add (MeasureTheory.measureReal_union_le _ _) hG

/-- The one-point bound at level `M - 1`, equation (4.11) of arXiv:2611.23658v1.
Under `Airy1FddPositive` and `GOELeftTail`. -/
theorem one_point_tail_minus_one_airy1 (h : Airy1FddPositive) (hT : GOELeftTail) :
    ∃ B E U : ℝ, 0 < B ∧ 0 < E ∧ 0 < U ∧
      ∀ M : ℝ, U ≤ M →
        (airy1Law h).real {f | M - 1 < airy1ContR h 0 f} ≤
          B * M ^ (-3 / 4 : ℝ) *
            Real.exp (-AiryConj.kappaC * M ^ (3 / 2 : ℝ) + E * Real.sqrt M) := by
  obtain ⟨_, C, U, _, hC, hU, hb⟩ := one_point_tail_profile_bounds_airy1 h hT
  refine ⟨C * AiryConj.Cstar * (2 : ℝ) ^ (3 / 4 : ℝ), 2 * AiryConj.kappaC, max 2 (U + 1),
    by positivity [AiryConj.Cstar_pos], by positivity [AiryConj.kappaC_pos],
    two_pos.trans_le (le_max_left _ _), ?_⟩
  intro M hM
  have hM2 : 2 ≤ M := (le_max_left _ _).trans hM
  have hM0 : 0 < M := by linarith
  let v := M - 1
  have hvU : U ≤ v := by linarith [(le_max_right (2 : ℝ) (U + 1)).trans hM]
  have hv0 : 0 < v := hU.trans_le hvU
  have hhalf : M / 2 ≤ v := by dsimp [v]; linarith
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.2 hM0
  have hv_le : v ≤ M := by dsimp [v]; linarith
  have hroot_gap : Real.sqrt M - Real.sqrt v = 1 / (Real.sqrt M + Real.sqrt v) := by
    apply (eq_div_iff (by positivity : Real.sqrt M + Real.sqrt v ≠ 0)).2
    nlinarith [Real.sq_sqrt hM0.le, Real.sq_sqrt hv0.le, show M - v = 1 from sub_sub_cancel ..]
  have hweighted_gap : v * (Real.sqrt M - Real.sqrt v) ≤ Real.sqrt M := by
    rw [hroot_gap, mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < Real.sqrt M + Real.sqrt v)).2
    nlinarith [Real.sq_sqrt hM0.le, mul_nonneg hs.le (Real.sqrt_nonneg v)]
  have hp (w : ℝ) (hw : 0 ≤ w) : w ^ (3 / 2 : ℝ) = w * Real.sqrt w := by
    rw [AiryFdd.rpow_three_halves_eq hw, pow_succ, Real.sq_sqrt hw]
  have hphase : M ^ (3 / 2 : ℝ) - v ^ (3 / 2 : ℝ) ≤ 2 * Real.sqrt M := by
    rw [hp M hM0.le, hp v hv0.le]
    nlinarith [show M * Real.sqrt M - v * Real.sqrt v =
      Real.sqrt M + v * (Real.sqrt M - Real.sqrt v) by dsimp [v]; ring]
  have hpow : v ^ (-3 / 4 : ℝ) ≤ (2 : ℝ) ^ (3 / 4 : ℝ) * M ^ (-3 / 4 : ℝ) := by
    refine (Real.rpow_le_rpow_of_nonpos (half_pos hM0) hhalf (by norm_num)).trans_eq ?_
    rw [Real.div_rpow hM0.le two_pos.le,
      show (2 : ℝ) ^ (-3 / 4 : ℝ) = ((2 : ℝ) ^ (3 / 4 : ℝ))⁻¹ by
        rw [show (-3 / 4 : ℝ) = -(3 / 4) by ring, Real.rpow_neg two_pos.le]]
    simp [div_eq_mul_inv, mul_comm]
  have he : Real.exp (-AiryConj.kappaC * v ^ (3 / 2 : ℝ)) ≤
      Real.exp (-AiryConj.kappaC * M ^ (3 / 2 : ℝ) + 2 * AiryConj.kappaC * Real.sqrt M) := by
    apply Real.exp_le_exp.mpr
    linarith [mul_le_mul_of_nonneg_right hphase AiryConj.kappaC_pos.le]
  calc
    _ ≤ C * (AiryConj.rhoM v / v) := (hb v hvU).2
    _ = C * AiryConj.Cstar * v ^ (-3 / 4 : ℝ) *
          Real.exp (-AiryConj.kappaC * v ^ (3 / 2 : ℝ)) := by rw [AiryConj.rhoM_div_eq hv0]; ring
    _ ≤ _ := by
      calc
        _ ≤ (C * AiryConj.Cstar) * ((2 : ℝ) ^ (3 / 4 : ℝ) * M ^ (-3 / 4 : ℝ)) *
            Real.exp (-AiryConj.kappaC * M ^ (3 / 2 : ℝ) + 2 * AiryConj.kappaC * Real.sqrt M) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity [AiryConj.Cstar_pos]))
            he (Real.exp_pos _).le (by positivity [AiryConj.Cstar_pos])
        _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- Proposition 4.3, equation (4.6) of arXiv:2611.23658v1, with a real threshold
and an arbitrary cutoff of order at most the square root of that threshold.
Under `Airy1FddPositive`, `GOELeftTail`, `NonnegativeWindowModulusEstimate`,
`ProcessAssociated` and `CubicCovarianceDecay` only. -/
theorem mesoscopic_sum_airy1 (h : Airy1FddPositive) (hT : GOELeftTail)
    (L : NonnegativeWindowModulusEstimate (airy1Law h) (airy1SRP h hT).A)
    (As : ProcessAssociated (airy1SRP h hT))
    (Cov : CubicCovarianceDecay (airy1SRP h hT))
    (χ : ℝ) (hχ : (1 / 2 : ℝ) ^ (1 / 3 : ℝ) < χ) (hχ₁ : χ < 1)
    (R : ℝ → ℝ) (hR : R =O[atTop] fun M => Real.sqrt M) :
    (fun M : ℝ =>
      ∑ j ∈ Finset.Icc ⌈χ * Real.sqrt (2 * M)⌉₊ ⌊R M⌋₊,
        (airy1Law h).real {f | M < airy1BlockMax h 0 f ∧ M < airy1BlockMax h j f})
      =o[atTop] AiryConj.rhoM := by
  obtain ⟨C₀, c₀, δ₀, hC₀, hc₀, hδ₀, hmodulus⟩ := block_modulus_airy1 h hT L
  obtain ⟨C, U, hC, hNewman⟩ := tail_sensitive_newman_airy1 h hT As
  obtain ⟨B, E, U₁, hB, hE, _, hpointTail⟩ := one_point_tail_minus_one_airy1 h hT
  have hχ0 : 0 < χ := (Real.rpow_pos_of_pos (by norm_num) _).trans hχ
  let θ := mesoTheta χ
  have hθ0 : 0 < θ := mesoTheta_pos (by positivity)
  have hθ : θ < 4 / 3 := mesoTheta_lt (one_half_lt_cube_of_lt hχ)
  let margin := θ * χ ^ 3 - 2 / 3
  have hmargin : 0 < margin := sub_pos.mpr (mesoTheta_margin_pos hχ)
  obtain ⟨d₀, hCov⟩ := Cov.theta_bound θ hθ
  obtain ⟨K, hK, hR'⟩ := hR.exists_nonneg
  let P := airy1Law h
  let W := airy1SRP h hT
  let a (M : ℝ) := Real.sqrt (2 * M)
  let δ (M : ℝ) := (M ^ 4)⁻¹
  let J (M : ℝ) : Finset ℕ := Finset.Icc ⌈χ * a M⌉₊ ⌊R M⌋₊
  let F (M : ℝ) (j : ℕ) := P.real {f | M < airy1BlockMax h 0 f ∧ M < airy1BlockMax h j f}
  let S (M : ℝ) := ∑ j ∈ J M, F M j
  change S =o[atTop] AiryConj.rhoM
  have haT : Tendsto a atTop atTop := Real.tendsto_sqrt_atTop.comp
    ((tendsto_const_mul_atTop_of_pos two_pos).2 tendsto_id)
  have hδT : Tendsto δ atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0))
  let D := (2 * C₀ + 9 * C * B ^ 2 + 9 * C * Real.exp θ) / AiryConj.Cstar
  have hBound : ∀ᶠ M : ℝ in atTop,
      S M / AiryConj.rhoM M ≤ ((K + 1) * D) * (a M ^ 19 * Real.exp (-(a M))) := by
    filter_upwards [eventually_ge_atTop (max 1 (max (U + 1) U₁)),
      hδT.eventually (gt_mem_nhds hδ₀), haT.eventually_ge_atTop ((max d₀ 0 + 1) / χ),
      haT.eventually_ge_atTop ((5 / 3) / (c₀ / 4)),
      haT.eventually_ge_atTop (3 * E + 3),
      haT.eventually_ge_atTop ((3 * θ * χ ^ 2 + 1) / margin),
      hR'.bound] with M hM hδmax hd hmodexp hgridexp hcovexp hR_M
    have hM1 : 1 ≤ M := (le_max_left _ _).trans hM
    have hM0 : 0 < M := one_pos.trans_le hM1
    have hMlarge : max (U + 1) U₁ ≤ M := (le_max_right 1 _).trans hM
    have hU : U ≤ M - 1 := by linarith only [(le_max_left (U + 1) U₁).trans hMlarge]
    have hU₁ : U₁ ≤ M := (le_max_right (U + 1) U₁).trans hMlarge
    have ha1 : 1 ≤ a M := Real.one_le_sqrt.mpr (by linarith only [hM1])
    have ha0 : 0 ≤ a M := Real.sqrt_nonneg _
    have ha_sq : a M ^ 2 = 2 * M := Real.sq_sqrt (by positivity)
    have hMsq : M ≤ a M ^ 2 := by linarith only [ha_sq, hM1]
    have hroot : Real.sqrt M ≤ a M := Real.sqrt_le_sqrt (by linarith only [hM1])
    have hrate : AiryConj.kappaC * M ^ (3 / 2 : ℝ) = 2 / 3 * a M ^ 3 := by
      rw [← airyKappa_eq_kappaC]
      exact airyKappa_mul_rpow_three_halves hM0.le
    have hlag : max d₀ 0 ≤ χ * a M - 1 := by
      linarith only [(div_le_iff₀ hχ0).mp hd]
    have hlagnn : 0 ≤ χ * a M - 1 := (le_max_right _ _).trans hlag
    have hModExp : 2 / 3 * a M ^ 3 - (c₀ / 4) * a M ^ 4 ≤ -(a M) :=
      meso_exponent_modulus ha1 (by
        have he := (div_le_iff₀ (show 0 < c₀ / 4 by positivity)).mp hmodexp
        simpa only [mul_comm] using he)
    have hGridExp : 2 / 3 * a M ^ 3 + (-(4 / 3) * a M ^ 3 + 2 * E * a M) ≤ -(a M) := by
      have ha₂ : a M ≤ a M ^ 2 := by nlinarith only [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
      have he : 0 ≤ (2 / 3 : ℝ) * a M ^ 2 - (2 * E + 1) := by linarith only [hgridexp, ha₂]
      nlinarith only [mul_nonneg he ha0]
    have hCovExp : 2 / 3 * a M ^ 3 - θ * (χ * a M - 1) ^ 3 ≤ -(a M) + θ :=
      meso_exponent_cov hθ0 hχ0 ha1 (by
        have he := (div_le_iff₀ hmargin).mp hcovexp
        simpa only [margin, mul_comm] using he)
    let n := meshN M
    have hn : 0 < n := Nat.ceil_pos.mpr (by positivity)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnlow : M ^ 4 ≤ (n : ℝ) := Nat.le_ceil _
    have hδ0 : 0 < δ M := by dsimp [δ]; positivity
    have hmesh : 1 / (n : ℝ) ≤ 2 * δ M := by
      have hinv := inv_anti₀ (show 0 < M ^ 4 by positivity) hnlow
      rw [one_div]
      change _ ≤ 2 * (M ^ 4)⁻¹
      linarith only [hinv, inv_nonneg.mpr (show 0 ≤ M ^ 4 by positivity)]
    have hnup : (n : ℝ) + 1 ≤ 3 * a M ^ 8 := by
      have hceil : (n : ℝ) < M ^ 4 + 1 := Nat.ceil_lt_add_one (by positivity)
      have h4 : 1 ≤ M ^ 4 := one_le_pow₀ hM1
      have hpow := pow_le_pow_left₀ hM0.le hMsq 4
      nlinarith only [hceil, h4, hpow]
    have hnsq : ((n : ℝ) + 1) ^ 2 ≤ 9 * a M ^ 16 := by
      calc
        _ ≤ (3 * a M ^ 8) ^ 2 := pow_le_pow_left₀ (by positivity) hnup 2
        _ = _ := by ring
    have hδpow : δ M ^ (-(1 / 2 : ℝ)) = M ^ 2 := by
      rw [Real.rpow_neg hδ0.le, ← Real.sqrt_eq_rpow]
      dsimp [δ]
      rw [show M ^ 4 = (M ^ 2) ^ 2 by ring, Real.sqrt_inv, Real.sqrt_sq (sq_nonneg M), inv_inv]
    have hmod (j : ℕ) : P.real (unit_block_oscillation_event h j (δ M)) ≤
        C₀ * a M ^ 8 * Real.exp (-(c₀ / 4) * a M ^ 4) := by
      rw [block_oscillation_probability_shift_airy1 h hT j _ hδ0.le]
      have h0 : P.real (unit_block_oscillation_event h 0 (δ M)) ≤
          C₀ * (δ M)⁻¹ * Real.exp (-c₀ * δ M ^ (-(1 / 2 : ℝ))) := by
        simpa only [unit_block_oscillation_event, Nat.cast_zero, zero_add] using
          hmodulus (δ M) hδ0 hδmax.le
      rw [hδpow, show (δ M)⁻¹ = M ^ 4 by simp [δ]] at h0
      have h4 : M ^ 4 ≤ a M ^ 8 := by
        have h4 := pow_le_pow_left₀ hM0.le hMsq 4
        nlinarith only [h4]
      have hm2 : M ^ 2 = a M ^ 4 / 4 := by
        nlinarith only [congrArg (fun v : ℝ => v ^ 2) ha_sq]
      refine h0.trans ?_
      rw [hm2, show -c₀ * (a M ^ 4 / 4) = -(c₀ / 4) * a M ^ 4 by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hC₀.le) (Real.exp_pos _).le
    let p := P.real {f | M - 1 < airy1ContR h 0 f}
    have hp0 : 0 ≤ p := measureReal_nonneg _
    have hp : p ^ 2 ≤ B ^ 2 * Real.exp (-(4 / 3) * a M ^ 3 + 2 * E * a M) := by
      have hb := hpointTail M hU₁
      have hPpow : M ^ (-3 / 4 : ℝ) ≤ 1 := by
        simpa using Real.rpow_le_rpow_of_nonpos one_pos hM1 (by norm_num : (-3 / 4 : ℝ) ≤ 0)
      have hb' : p ≤ B * Real.exp (-(2 / 3) * a M ^ 3 + E * a M) := by
        have he : Real.exp (-AiryConj.kappaC * M ^ (3 / 2 : ℝ) + E * Real.sqrt M) ≤
            Real.exp (-(2 / 3) * a M ^ 3 + E * a M) := by
          apply Real.exp_le_exp.mpr
          linarith only [mul_le_mul_of_nonneg_left hroot hE.le, hrate]
        refine hb.trans ?_
        calc
          _ ≤ (B * 1) * Real.exp (-(2 / 3) * a M ^ 3 + E * a M) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hPpow hB.le) he (Real.exp_pos _).le
              (by positivity)
          _ = _ := by rw [mul_one]
      refine (pow_le_pow_left₀ hp0 hb' 2).trans_eq ?_
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 1
      ring
    let Q := Real.exp (-θ * (χ * a M - 1) ^ 3)
    have hQ : 0 ≤ Q := (Real.exp_pos _).le
    have hgrid (j : ℕ) (hj : j ∈ J M) (k : ℕ) (hk : k ∈ Finset.range (n + 1))
        (k' : ℕ) :
        P.real {f | M - 1 < airy1ContR h (gridPt 0 n k) f ∧
          M - 1 < airy1ContR h (gridPt j n k') f} ≤ C * p ^ 2 + C * M * Q := by
      let x := gridPt 0 n k
      let y := gridPt j n k'
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hx1 : x ≤ 1 := by
        unfold x gridPt
        simp only [Nat.cast_zero, zero_add]
        exact (div_le_one hnR).mpr (by exact_mod_cast hk')
      have hyj : (j : ℝ) ≤ y := by
        unfold y gridPt
        exact le_add_of_nonneg_right (by positivity)
      have hj' : χ * a M ≤ (j : ℝ) := (Nat.le_ceil _).trans
        (by exact_mod_cast (Finset.mem_Icc.mp hj).1)
      have hlag' : χ * a M - 1 ≤ y - x := by linarith only [hj', hyj, hx1]
      have hlag0 : 0 ≤ y - x := hlagnn.trans hlag'
      have hstat := (pairStationary_airy1SRP h hT).stat_pair 0 (y - x) x
      rw [zero_add, sub_add_cancel] at hstat
      let T : Set (ℝ × ℝ) := Ioi (M - 1) ×ˢ Ioi (M - 1)
      have hTm : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ioi
      have hpair :
          P.real {f | M - 1 < W.A x f ∧ M - 1 < W.A y f} =
            P.real {f | M - 1 < W.A 0 f ∧ M - 1 < W.A (y - x) f} := by
        change P.real ((fun f => (W.A x f, W.A y f)) ⁻¹' T) =
          P.real ((fun f => (W.A 0 f, W.A (y - x) f)) ⁻¹' T)
        rw [← map_measureReal_apply ((W.A_meas x).prodMk (W.A_meas y)) hTm,
          ← map_measureReal_apply ((W.A_meas 0).prodMk (W.A_meas (y - x))) hTm, hstat]
      have hnew := hNewman (M - 1) (y - x) hU hlag0
      have hcov : covariance (W.A 0) (W.A (y - x)) P ≤ Q := by
        refine (hCov _ ((le_max_left _ _).trans (hlag.trans hlag'))).trans ?_
        apply Real.exp_le_exp.mpr
        have hd3 := pow_le_pow_left₀ hlagnn hlag' 3
        linarith only [mul_le_mul_of_nonneg_left hd3 hθ0.le]
      change P.real {f | M - 1 < W.A x f ∧ M - 1 < W.A y f} ≤ _
      rw [hpair]
      refine hnew.trans (add_le_add le_rfl ?_)
      exact (mul_le_mul_of_nonneg_left hcov (by positivity : 0 ≤ C * (M - 1))).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only) hC.le) hQ)
    let b₁ := -(c₀ / 4) * a M ^ 4
    let b₂ := -(4 / 3) * a M ^ 3 + 2 * E * a M
    let b₃ := -θ * (χ * a M - 1) ^ 3
    have hper (j : ℕ) (hj : j ∈ J M) :
        F M j ≤ 2 * C₀ * a M ^ 8 * Real.exp b₁ +
          9 * C * B ^ 2 * a M ^ 16 * Real.exp b₂ + 9 * C * a M ^ 18 * Real.exp b₃ := by
      have hsum : (∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
          P.real {f | M - 1 < airy1ContR h (gridPt 0 n k) f ∧
            M - 1 < airy1ContR h (gridPt j n k') f}) ≤
          ((n : ℝ) + 1) ^ 2 * (C * p ^ 2 + C * M * Q) := by
        refine (Finset.sum_le_sum (fun k hk => Finset.sum_le_sum
          (fun k' _ => hgrid j hj k hk k'))).trans_eq ?_
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_succ]
        ring
      have hgridSq : ((n : ℝ) + 1) ^ 2 * (C * p ^ 2) ≤
          9 * C * B ^ 2 * a M ^ 16 * Real.exp b₂ := by
        have hh := mul_le_mul hnsq (mul_le_mul_of_nonneg_left hp hC.le)
          (by positivity) (by positivity)
        exact hh.trans_eq (by dsimp [b₂]; ring)
      have hgridCov : ((n : ℝ) + 1) ^ 2 * (C * M * Q) ≤ 9 * C * a M ^ 18 * Real.exp b₃ := by
        have hh := mul_le_mul hnsq
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMsq hC.le) hQ)
          (by positivity) (by positivity)
        exact hh.trans_eq (by dsimp [Q, b₃]; ring)
      have hcover := block_pair_grid_cover_airy1 h j n hn (δ M) M hmesh
      have hmodsum :
          P.real (unit_block_oscillation_event h 0 (δ M)) +
            P.real (unit_block_oscillation_event h j (δ M)) ≤
            2 * C₀ * a M ^ 8 * Real.exp b₁ :=
        (add_le_add (hmod 0) (hmod j)).trans_eq (by dsimp [b₁]; ring)
      calc
        _ ≤ _ := hcover
        _ ≤ 2 * C₀ * a M ^ 8 * Real.exp b₁ +
            ((n : ℝ) + 1) ^ 2 * (C * p ^ 2 + C * M * Q) := add_le_add hmodsum hsum
        _ = 2 * C₀ * a M ^ 8 * Real.exp b₁ +
            ((n : ℝ) + 1) ^ 2 * (C * p ^ 2) + ((n : ℝ) + 1) ^ 2 * (C * M * Q) := by ring
        _ ≤ _ := add_le_add (add_le_add le_rfl hgridSq) hgridCov
    have hρ : 0 < AiryConj.rhoM M := AiryConj.rhoM_pos hM0
    have hinvρ : (AiryConj.rhoM M)⁻¹ ≤ Real.exp (2 / 3 * a M ^ 3) / AiryConj.Cstar := by
      apply (inv_le_iff_one_le_mul₀ hρ).2
      have hform : (Real.exp (2 / 3 * a M ^ 3) / AiryConj.Cstar) * AiryConj.rhoM M =
          M ^ (1 / 4 : ℝ) := by
        rw [AiryConj.rhoM, show -AiryConj.kappaC * M ^ (3 / 2 : ℝ) =
            -(2 / 3 * a M ^ 3) by linarith only [hrate]]
        have he : Real.exp (2 / 3 * a M ^ 3) * Real.exp (-(2 / 3 * a M ^ 3)) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        calc
          _ = (AiryConj.Cstar / AiryConj.Cstar) * M ^ (1 / 4 : ℝ) *
              (Real.exp (2 / 3 * a M ^ 3) * Real.exp (-(2 / 3 * a M ^ 3))) := by ring
          _ = _ := by rw [he, div_self AiryConj.Cstar_pos.ne', one_mul, mul_one]
      rw [hform]
      exact Real.one_le_rpow hM1 (by norm_num)
    have hscale (k : ℕ) (hk : k ≤ 18) (A b η : ℝ) (hA : 0 ≤ A)
        (he : 2 / 3 * a M ^ 3 + b ≤ -(a M) + η) :
        A * a M ^ k * Real.exp b / AiryConj.rhoM M ≤
          (A * Real.exp η / AiryConj.Cstar) * (a M ^ 18 * Real.exp (-(a M))) := by
      have hp := pow_le_pow_right₀ ha1 hk
      calc
        _ ≤ (A * a M ^ k * Real.exp b) * (Real.exp (2 / 3 * a M ^ 3) / AiryConj.Cstar) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left hinvρ (by positivity)
        _ = (A / AiryConj.Cstar) * a M ^ k * Real.exp (2 / 3 * a M ^ 3 + b) := by
          rw [Real.exp_add]
          ring
        _ ≤ (A / AiryConj.Cstar) * a M ^ 18 * Real.exp (-(a M) + η) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity [AiryConj.Cstar_pos]))
            (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity [AiryConj.Cstar_pos])
        _ = _ := by rw [Real.exp_add]; ring
    have hnormalized (j : ℕ) (hj : j ∈ J M) :
        F M j / AiryConj.rhoM M ≤ D * (a M ^ 18 * Real.exp (-(a M))) := by
      refine (div_le_div_of_nonneg_right (hper j hj) hρ.le).trans ?_
      rw [add_div, add_div]
      have h1 := hscale 8 (by norm_num) (2 * C₀) b₁ 0 (by positivity)
        (by simpa only [b₁, add_zero, sub_eq_add_neg, neg_mul] using hModExp)
      have h2 := hscale 16 (by norm_num) (9 * C * B ^ 2) b₂ 0 (by positivity)
        (by simpa only [b₂, add_zero] using hGridExp)
      have h3 := hscale 18 (by norm_num) (9 * C) b₃ θ (by positivity)
        (by simpa only [b₃, sub_eq_add_neg, neg_mul] using hCovExp)
      simp only [Real.exp_zero, mul_one] at h1 h2
      exact (add_le_add (add_le_add h1 h2) h3).trans_eq (by dsimp [D]; ring)
    have hcard : ((J M).card : ℝ) ≤ (K + 1) * a M := by
      have hsub : J M ⊆ Finset.range (⌊R M⌋₊ + 1) := by
        intro j hj
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hj).2)
      have hf : (⌊R M⌋₊ : ℝ) ≤ |R M| := calc
        _ ≤ (⌊|R M|⌋₊ : ℝ) := by exact_mod_cast Nat.floor_mono (le_abs_self (R M))
        _ ≤ _ := Nat.floor_le (abs_nonneg _)
      have hAbs : |R M| ≤ K * Real.sqrt M := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg M)] using hR_M
      have hcardNat : (J M).card ≤ ⌊R M⌋₊ + 1 := by
        simpa only [Finset.card_range] using Finset.card_le_card hsub
      have hcardR : ((J M).card : ℝ) ≤ (⌊R M⌋₊ : ℝ) + 1 := by exact_mod_cast hcardNat
      linarith only [hcardR, hf, hAbs, ha1, mul_le_mul_of_nonneg_left hroot hK]
    calc
      S M / AiryConj.rhoM M = ∑ j ∈ J M, F M j / AiryConj.rhoM M := by
        dsimp [S]
        rw [Finset.sum_div]
      _ ≤ ∑ _j ∈ J M, D * (a M ^ 18 * Real.exp (-(a M))) :=
        Finset.sum_le_sum hnormalized
      _ = ((J M).card : ℝ) * (D * (a M ^ 18 * Real.exp (-(a M)))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((K + 1) * a M) * (D * (a M ^ 18 * Real.exp (-(a M)))) :=
        mul_le_mul_of_nonneg_right hcard (by dsimp [D]; positivity [AiryConj.Cstar_pos])
      _ = _ := by ring
  have hρ_pos : ∀ᶠ M : ℝ in atTop, 0 < AiryConj.rhoM M :=
    (eventually_gt_atTop 0).mono fun _ => AiryConj.rhoM_pos
  refine (isLittleO_iff_tendsto' (hρ_pos.mono fun _ hp hz => (hp.ne' hz).elim)).mpr ?_
  have hUpper : Tendsto (fun M => ((K + 1) * D) * (a M ^ 19 * Real.exp (-(a M))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 19).comp haT).const_mul ((K + 1) * D)
  exact squeeze_zero' (hρ_pos.mono fun M hp => div_nonneg
    (Finset.sum_nonneg fun _ _ => measureReal_nonneg _) hp.le) hBound hUpper

end Airy1Gumbel
