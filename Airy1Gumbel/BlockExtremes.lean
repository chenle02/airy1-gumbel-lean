/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.Normalization
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Airy1Gumbel

/-!
# Block extremes interface and the Gumbel-limit assembly layer

This file packages the probabilistic inputs that the proof of the Gumbel limit
for `max_{0 ≤ x ≤ N} 𝒜₁(x)` consumes about the block maxima of a stationary
continuous-path process (`Airy1BlockExtremes`), and derives from them (or from
pure analysis) four auxiliary results:

* `Airy1BlockExtremes.tail_normalized`: `N · ℙ(Y₀ > u_N(z)) → e^{-z}`, the
  reduction of the paper's normalization lemma to its analytic input `sharp_tail`;
* `mixing_tail_of_bound`: the `mixing_tail` field is implied by the elementary
  mixing-coefficient bound `alpha_bound`, so downstream users only ever need to
  verify the elementary bound;
* `gumbelB_succ_ratio` and `gumbelA_succ_diff`: the integer-extension squeeze
  data `(b_{n+1}/b_n → 1, (a_{n+1}-a_n)/b_n → 0)`, which is pure asymptotic
  analysis of the centering/scaling sequences.

The T4-type statement `(a_{n+1} - a_n)/b_n → 0` is proved with no Taylor
theorem, via the exact conjugate identities
`ρ^{2/3} - 1 = (ρ² - 1)/(w² + w + 1)` with `w = ρ^{2/3}` and
`1 - ρ^{-1/3} = (ρ - 1)/(v² + v + 1)/v`-style bounds with `v = ρ^{1/3}`.
-/

/-- The polylogarithmic block length `q_N = ⌈A (log N)^{1/3}⌉`. -/
noncomputable def qN (A : ℝ) (N : ℕ) : ℕ := ⌈A * (Real.log N) ^ ((1 : ℝ) / 3)⌉₊

/-- The mesoscopic block boundary `m_N = ⌊χ √(2 u_N(z))⌋`. -/
noncomputable def mN (χ : ℝ) (z : ℝ) (N : ℕ) : ℕ := ⌊χ * Real.sqrt (2 * gumbelU N z)⌋₊

/-- The named analytic inputs the Gumbel-limit assembly consumes about the
block maxima `Y j` of a stationary continuous-path process. Each field is a
hypothesis proved in the paper from the Airy₁ Fredholm-determinant structure;
this structure asserts none of them. -/
structure Airy1BlockExtremes {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- The block maxima. -/
  Y : ℕ → Ω → ℝ
  /-- Each block maximum is measurable. -/
  Y_meas : ∀ j, Measurable (Y j)
  /-- A mixing envelope: `alpha m` is a nonnegative sequence satisfying the
  stated decay, decoupling and pair-mixing bounds. It is not asserted to be a
  formal characterization of the supremum-of-σ-algebras strong-mixing
  coefficient of the process. -/
  alpha : ℕ → ℝ
  /-- Mixing coefficients are nonnegative. -/
  alpha_nonneg : ∀ m, 0 ≤ alpha m
  /-- Amplitude constant of the mixing bound. -/
  mixC : ℝ
  mixC_pos : 0 < mixC
  /-- Rate constant of the mixing bound. -/
  mixc : ℝ
  mixc_pos : 0 < mixc
  /-- The elementary mixing bound `α(m) ≤ C e^{-c(m-1)³}`. -/
  alpha_bound : ∀ m, alpha m ≤ mixC * Real.exp (-mixc * ((m : ℝ) - 1) ^ 3)
  /-- Stationarity of the one-block marginal tail. -/
  stat_marginal : ∀ (u : ℝ) (i : ℕ),
    P {ω | Y i ω > u} = P {ω | Y 0 ω > u}
  /-- Stationarity of the pair tail at distance `d`. -/
  stat_pair : ∀ (u : ℝ) (i d : ℕ),
    P {ω | Y i ω > u ∧ Y (i + d) ω > u} = P {ω | Y 0 ω > u ∧ Y d ω > u}
  /-- The sharp one-block tail: `ℙ(Y₀ > u) ~ e^{-H(u)}` as `u → ∞`. -/
  sharp_tail :
    Tendsto (fun u : ℝ => P.real {ω | Y 0 ω > u} / Real.exp (-airyH u)) atTop (𝓝 1)
  /-- Adjacent blocks do not touch the level simultaneously on the `N`-scale. -/
  touching : ∀ z : ℝ,
    Tendsto (fun N : ℕ =>
      (N : ℝ) * P.real {ω | Y 0 ω > gumbelU N z ∧ Y 1 ω > gumbelU N z}) atTop (𝓝 0)
  /-- The mixing tail over the polylogarithmic block is `o(1/N)`. -/
  mixing_tail : ∃ A : ℝ, 0 < A ∧ 1 < mixc * A ^ 3 ∧
    Tendsto (fun N : ℕ => (N : ℝ) * ∑' j : ℕ, alpha (qN A N + j)) atTop (𝓝 0)
  /-- Separated pairs within the mesoscopic window are negligible. -/
  separated : ∀ (z χ : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 →
    Tendsto (fun N : ℕ =>
      (N : ℝ) * ∑ j ∈ Finset.Icc 2 (mN χ z N),
        P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0)
  /-- Mesoscopic-scale pairs are negligible. -/
  mesoscopic : ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
    Tendsto (fun N : ℕ =>
      (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
        P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0)
  /-- Decoupling of `≤`-events separated by a gap `q`, with error `alpha q`. -/
  decouple : ∀ (S T : Finset ℕ) (q : ℕ) (u : ℝ),
    (∀ s ∈ S, ∀ t ∈ T, s + q ≤ t) →
    |P.real ({ω | ∀ s ∈ S, Y s ω ≤ u} ∩ {ω | ∀ t ∈ T, Y t ω ≤ u}) -
      P.real {ω | ∀ s ∈ S, Y s ω ≤ u} * P.real {ω | ∀ t ∈ T, Y t ω ≤ u}|
      ≤ alpha q
  /-- Pair-mixing bound at distance `j`. -/
  pair_mix : ∀ (u : ℝ) (j : ℕ),
    P.real {ω | Y 0 ω > u ∧ Y j ω > u} ≤ P.real {ω | Y 0 ω > u} ^ 2 + alpha j

/-! ### Power/logarithm limit infrastructure -/

/-- `L^s → ∞` for `s > 0`, where `L = log N`. -/
lemma tendsto_log_rpow_atTop (s : ℝ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => (Real.log N) ^ s) atTop atTop :=
  (tendsto_rpow_atTop hs).comp tendsto_L_atTop

/-- `L^{-1/3} → 0`, where `L = log N`. -/
lemma tendsto_log_rpow_neg_one_third :
    Tendsto (fun N : ℕ => (Real.log N) ^ (-(1 : ℝ) / 3)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).comp
    tendsto_L_atTop
  simp only [Function.comp_def] at h
  rw [show (fun N : ℕ => (Real.log ↑N) ^ (-(1 : ℝ) / 3)) =
      (fun N : ℕ => (Real.log ↑N) ^ (-(1 / 3 : ℝ))) from
        funext fun N => by rw [show (-(1 : ℝ) / 3) = -(1 / 3 : ℝ) by norm_num]]
  exact h

/-- `x^{-1/3} = (x^{1/3})⁻¹` with the exponent written in `gumbelB`'s form
(`-(1:ℝ)/3` is `(-1)/3`, not the `Neg`-of-division form `Real.rpow_neg`
pattern-matches). -/
lemma rpow_neg_one_third {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(1 : ℝ) / 3) = (x ^ ((1 : ℝ) / 3))⁻¹ := by
  rw [show (-(1 : ℝ) / 3 : ℝ) = -((1 : ℝ) / 3) by norm_num]
  exact Real.rpow_neg hx _

/-- The normalization `u_N(z) = a_N + b_N z` drifts to `+∞` for every fixed `z`. -/
lemma gumbelU_tendsto_atTop (z : ℝ) :
    Tendsto (fun N : ℕ => gumbelU N z) atTop atTop := by
  have hmain : Tendsto (fun N : ℕ => (airyGamma / 4) * (Real.log N) ^ ((2 : ℝ) / 3))
      atTop atTop :=
    Tendsto.const_mul_atTop (div_pos airyGamma_pos (by norm_num))
      (tendsto_log_rpow_atTop _ (by norm_num))
  refine tendsto_atTop_mono' atTop ?_ hmain
  filter_upwards [eventually_ge_atTop 2, epsN_eventually_le,
    tendsto_L_atTop.eventually_ge_atTop (max 1 (((8 * |z|) / 3) ^ ((3 : ℝ) / 2)))]
    with N hN hε hLb
  have hL1 : (1 : ℝ) ≤ Real.log N := (max_le_iff.mp hLb).1
  have hL0 : (0 : ℝ) < Real.log N := one_pos.trans_le hL1
  have hL23 : (8 * |z|) / 3 ≤ (Real.log N) ^ ((2 : ℝ) / 3) := by
    have hbase : (0 : ℝ) ≤ 8 * |z| / 3 := by positivity
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) (max_le_iff.mp hLb).2
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rwa [← Real.rpow_mul hbase, show (3 : ℝ) / 2 * (2 / 3) = 1 by norm_num,
      Real.rpow_one] at h1
  have hLi : (Real.log N) ^ (-(1 : ℝ) / 3) ≤ 1 := by
    rw [rpow_neg_one_third hL0.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hL1 (by norm_num))
  have hA : airyGamma * (Real.log N) ^ ((2 : ℝ) / 3) * (1 / 2) ≤ gumbelA N := by
    have h1 : (1 : ℝ) / 2 ≤ 1 + epsN N := by linarith [(abs_le.mp hε).1]
    have h2 : (0 : ℝ) ≤ airyGamma * (Real.log N) ^ ((2 : ℝ) / 3) :=
      mul_nonneg airyGamma_pos.le (Real.rpow_nonneg hL0.le _)
    calc airyGamma * (Real.log N) ^ ((2 : ℝ) / 3) * (1 / 2)
        ≤ airyGamma * (Real.log N) ^ ((2 : ℝ) / 3) * (1 + epsN N) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = gumbelA N := (gumbelA_eq hN).symm
  have hBz : |gumbelB N * z| ≤ (2 * airyGamma / 3) * |z| := by
    have h23nn : (0 : ℝ) ≤ 2 * airyGamma / 3 :=
      div_nonneg (mul_nonneg (by norm_num) airyGamma_pos.le) (by norm_num)
    have hB0 : (0 : ℝ) ≤ gumbelB N := mul_nonneg h23nn (Real.rpow_nonneg hL0.le _)
    calc |gumbelB N * z| = gumbelB N * |z| := by rw [abs_mul, abs_of_nonneg hB0]
      _ ≤ (2 * airyGamma / 3) * 1 * |z| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hLi h23nn) (abs_nonneg z)
      _ = (2 * airyGamma / 3) * |z| := by ring
  have hcomb : (airyGamma / 4) * (Real.log N) ^ ((2 : ℝ) / 3) ≤
      gumbelA N - (2 * airyGamma / 3) * |z| := by
    have h1 : (2 * airyGamma / 3) * |z| ≤ (airyGamma / 4) * (Real.log N) ^ ((2 : ℝ) / 3) := by
      calc (2 * airyGamma / 3) * |z| = (airyGamma / 4) * (8 * |z| / 3) := by ring
        _ ≤ (airyGamma / 4) * (Real.log N) ^ ((2 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_left hL23 (div_nonneg airyGamma_pos.le (by norm_num))
    linarith [hA, h1]
  calc (airyGamma / 4) * (Real.log N) ^ ((2 : ℝ) / 3)
      ≤ gumbelA N - (2 * airyGamma / 3) * |z| := hcomb
    _ ≤ gumbelA N - |gumbelB N * z| := by linarith [hBz]
    _ ≤ gumbelA N + gumbelB N * z := by linarith [neg_abs_le (gumbelB N * z)]
    _ = gumbelU N z := rfl

/-! ### T1: tail normalization from the sharp tail -/

/-- The analytic content of the paper's normalization lemma, reduced to the `sharp_tail`
input: `N · ℙ(Y₀ > u_N(z)) → e^{-z}`. -/
theorem Airy1BlockExtremes.tail_normalized
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : Airy1BlockExtremes P) (z : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * P.real {ω | D.Y 0 ω > gumbelU N z})
      atTop (𝓝 (Real.exp (-z))) := by
  have h1 : Tendsto
      (fun N : ℕ =>
        P.real {ω | D.Y 0 ω > gumbelU N z} / Real.exp (-airyH (gumbelU N z)))
      atTop (𝓝 1) := by
    have h := D.sharp_tail.comp (gumbelU_tendsto_atTop z)
    simpa [Function.comp_def] using h
  have h2 := gumbel_normalization z
  have h := h1.mul h2
  rw [one_mul] at h
  apply Tendsto.congr' _ h
  filter_upwards with N
  have he := (Real.exp_pos (-airyH (gumbelU N z))).ne'
  calc (P.real {ω | D.Y 0 ω > gumbelU N z} / Real.exp (-airyH (gumbelU N z))) *
        ((N : ℝ) * Real.exp (-airyH (gumbelU N z)))
      = P.real {ω | D.Y 0 ω > gumbelU N z} * (N : ℝ) *
          ((Real.exp (-airyH (gumbelU N z)))⁻¹ * Real.exp (-airyH (gumbelU N z))) := by
        rw [div_eq_mul_inv]; ring
    _ = P.real {ω | D.Y 0 ω > gumbelU N z} * (N : ℝ) := by
        rw [inv_mul_cancel₀ he, mul_one]
    _ = (N : ℝ) * P.real {ω | D.Y 0 ω > gumbelU N z} := mul_comm _ _

/-! ### T2: the mixing tail from the elementary bound -/

/-- The block size `qN A N` drifts to `+∞` (as a real sequence). -/
lemma tendsto_qN_atTop {A : ℝ} (hA : 0 < A) :
    Tendsto (fun N : ℕ => (qN A N : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun N : ℕ => A * (Real.log N) ^ ((1 : ℝ) / 3)) atTop atTop :=
    Tendsto.const_mul_atTop hA (tendsto_log_rpow_atTop _ (by norm_num))
  refine tendsto_atTop_mono' atTop ?_ h1
  exact Eventually.of_forall fun N => Nat.le_ceil _

/-- For `q ≥ 2`, the tail of `alpha` is dominated by an explicit geometric
series with ratio `e^{-c(q-1)²} < 1`. -/
lemma tsum_alpha_tail_le {C c : ℝ} (hC : 0 < C) (hc : 0 < c) {alpha : ℕ → ℝ}
    (hα : ∀ m, alpha m ≤ C * Real.exp (-c * ((m : ℝ) - 1) ^ 3))
    (hα0 : ∀ m, 0 ≤ alpha m) {q : ℕ} (hq : 2 ≤ q) :
    (∑' j : ℕ, alpha (q + j)) ≤
      C * Real.exp (-c * ((q : ℝ) - 1) ^ 3) *
        (1 - Real.exp (-c * ((q : ℝ) - 1) ^ 2))⁻¹ := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hr0 : 0 ≤ Real.exp (-c * ((q : ℝ) - 1) ^ 2) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c * ((q : ℝ) - 1) ^ 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hc)
      (pow_pos (by linarith : (0 : ℝ) < (q : ℝ) - 1) 2)
  have hgeo : Summable fun j : ℕ => (Real.exp (-c * ((q : ℝ) - 1) ^ 2)) ^ j :=
    summable_geometric_of_lt_one hr0 hr1
  have hgsumm : Summable fun j : ℕ =>
      C * Real.exp (-c * ((q : ℝ) - 1) ^ 3) * (Real.exp (-c * ((q : ℝ) - 1) ^ 2)) ^ j :=
    hgeo.mul_left _
  have hle : ∀ j : ℕ, alpha (q + j) ≤
      C * Real.exp (-c * ((q : ℝ) - 1) ^ 3) * (Real.exp (-c * ((q : ℝ) - 1) ^ 2)) ^ j := by
    intro j
    have hj : ((q + j : ℕ) : ℝ) = (q : ℝ) + j := Nat.cast_add _ _
    have hkey : ((q : ℝ) - 1) ^ 2 * ((q : ℝ) + j - 1) ≤ ((q : ℝ) + j - 1) ^ 3 := by
      have h1 : ((q : ℝ) - 1) ^ 2 ≤ ((q : ℝ) + j - 1) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      calc ((q : ℝ) - 1) ^ 2 * ((q : ℝ) + j - 1)
          ≤ ((q : ℝ) + j - 1) ^ 2 * ((q : ℝ) + j - 1) :=
            mul_le_mul_of_nonneg_right h1 (by linarith)
        _ = ((q : ℝ) + j - 1) ^ 3 := by ring
    calc alpha (q + j)
        ≤ C * Real.exp (-c * (((q + j : ℕ) : ℝ) - 1) ^ 3) := hα _
      _ = C * Real.exp (-c * ((q : ℝ) + j - 1) ^ 3) := by rw [hj]
      _ ≤ C * Real.exp (-c * (((q : ℝ) - 1) ^ 2 * ((q : ℝ) + j - 1))) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonpos_left hkey (neg_nonpos.mpr hc.le))
      _ = C * (Real.exp (-c * ((q : ℝ) - 1) ^ 3) *
            (Real.exp (-c * ((q : ℝ) - 1) ^ 2)) ^ j) := by
          have hexp : -c * (((q : ℝ) - 1) ^ 2 * ((q : ℝ) + j - 1)) =
              -c * ((q : ℝ) - 1) ^ 3 + (j : ℝ) * (-c * ((q : ℝ) - 1) ^ 2) := by ring
          rw [hexp, Real.exp_add, Real.exp_nat_mul]
      _ = C * Real.exp (-c * ((q : ℝ) - 1) ^ 3) *
            (Real.exp (-c * ((q : ℝ) - 1) ^ 2)) ^ j := by ring
  have hfsumm : Summable fun j : ℕ => alpha (q + j) :=
    Summable.of_nonneg_of_le (fun j => hα0 _) hle hgsumm
  calc (∑' j : ℕ, alpha (q + j))
      ≤ ∑' j : ℕ, C * Real.exp (-c * ((q : ℝ) - 1) ^ 3) *
          (Real.exp (-c * ((q : ℝ) - 1) ^ 2)) ^ j :=
        Summable.tsum_le_tsum hle hfsumm hgsumm
    _ = C * Real.exp (-c * ((q : ℝ) - 1) ^ 3) *
          ∑' j : ℕ, (Real.exp (-c * ((q : ℝ) - 1) ^ 2)) ^ j := tsum_mul_left
    _ = C * Real.exp (-c * ((q : ℝ) - 1) ^ 3) *
          (1 - Real.exp (-c * ((q : ℝ) - 1) ^ 2))⁻¹ := by
        rw [tsum_geometric_of_lt_one hr0 hr1]

/-- The `mixing_tail` field of `Airy1BlockExtremes` is implied by the
elementary bound `alpha_bound`: with `q = qN A N` and any `β ∈ (1, cA³)`,
eventually `c(q-1)³ ≥ β log N`, the tail sum is geometric with ratio
`e^{-c(q-1)²} ≤ 1/2`, and `N · e^{-β log N} = N^{-(β-1)} → 0`. -/
theorem mixing_tail_of_bound {C c : ℝ} (hC : 0 < C) (hc : 0 < c) {alpha : ℕ → ℝ}
    (hα : ∀ m, alpha m ≤ C * Real.exp (-c * ((m : ℝ) - 1) ^ 3)) (hα0 : ∀ m, 0 ≤ alpha m)
    {A : ℝ} (hA0 : 0 < A) (hA : 1 < c * A ^ 3) :
    Tendsto (fun N : ℕ => (N : ℝ) * ∑' j : ℕ, alpha (qN A N + j)) atTop (𝓝 0) := by
  set δ := (c * A ^ 3 - 1) / 2 with hδdef
  set β := (c * A ^ 3 + 1) / 2 with hβdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hβδ : c * A ^ 3 - δ = β := by rw [hδdef, hβdef]; ring
  have hβ1 : 1 < β := by rw [hβdef]; linarith
  have hqtop := tendsto_qN_atTop hA0
  have hq2 : ∀ᶠ N : ℕ in atTop, 2 ≤ qN A N := by
    filter_upwards [hqtop.eventually_ge_atTop (2 : ℝ)] with N hN
    exact_mod_cast hN
  have hx1 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ A * (Real.log N) ^ ((1 : ℝ) / 3) :=
    (Tendsto.const_mul_atTop hA0 (tendsto_log_rpow_atTop _ (by norm_num))).eventually_ge_atTop 1
  -- eventually `c(q-1)³ ≥ β L`
  have hβbound : ∀ᶠ N : ℕ in atTop, β * Real.log N ≤ c * ((qN A N : ℝ) - 1) ^ 3 := by
    have hs1 : ∀ᶠ N : ℕ in atTop, (3 * c * A ^ 2) * (Real.log N) ^ (-(1 : ℝ) / 3) ≤ δ / 2 := by
      have h := tendsto_log_rpow_neg_one_third.const_mul (3 * c * A ^ 2)
      rw [mul_zero] at h
      have h' := (Metric.tendsto_nhds.mp h) (δ / 2) (half_pos hδ)
      filter_upwards [h'] with N hN
      rw [Real.dist_eq, sub_zero] at hN
      exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hN)
    have hs2 : ∀ᶠ N : ℕ in atTop, c / Real.log N ≤ δ / 2 := by
      have h := tendsto_one_div_L.const_mul c
      rw [mul_zero] at h
      have h2 : Tendsto (fun N : ℕ => c / Real.log N) atTop (𝓝 0) := by
        apply Tendsto.congr' _ h
        filter_upwards with N
        rw [one_div, div_eq_mul_inv]
      have h' := (Metric.tendsto_nhds.mp h2) (δ / 2) (half_pos hδ)
      filter_upwards [h'] with N hN
      rw [Real.dist_eq, sub_zero] at hN
      exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hN)
    filter_upwards [eventually_ge_atTop 2, hx1, hs1, hs2] with N hN2 hx1N hs1N hs2N
    have hL0 := log_nat_pos hN2
    have hqge : A * (Real.log N) ^ ((1 : ℝ) / 3) ≤ (qN A N : ℝ) := Nat.le_ceil _
    have hx0 : (0 : ℝ) ≤ A * (Real.log N) ^ ((1 : ℝ) / 3) - 1 := by linarith
    have hqcube : (A * (Real.log N) ^ ((1 : ℝ) / 3) - 1) ^ 3 ≤ ((qN A N : ℝ) - 1) ^ 3 :=
      pow_le_pow_left₀ hx0 (by linarith) 3
    have hxpow : (A * (Real.log N) ^ ((1 : ℝ) / 3)) ^ 3 - 3 *
          (A * (Real.log N) ^ ((1 : ℝ) / 3)) ^ 2 - 1 ≤
        (A * (Real.log N) ^ ((1 : ℝ) / 3) - 1) ^ 3 := by
      have hexp : (A * (Real.log N) ^ ((1 : ℝ) / 3) - 1) ^ 3 =
          (A * (Real.log N) ^ ((1 : ℝ) / 3)) ^ 3 -
            3 * (A * (Real.log N) ^ ((1 : ℝ) / 3)) ^ 2 +
              3 * (A * (Real.log N) ^ ((1 : ℝ) / 3)) - 1 := by ring
      linarith [hexp, hx1N]
    have hx3 : (A * (Real.log N) ^ ((1 : ℝ) / 3)) ^ 3 = A ^ 3 * Real.log N := by
      rw [mul_pow]
      congr 1
      rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow hL0.le (by norm_num)
    have hx2 : (A * (Real.log N) ^ ((1 : ℝ) / 3)) ^ 2 =
        A ^ 2 * (Real.log N) ^ ((2 : ℝ) / 3) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
        show (1 : ℝ) / 3 * ((2 : ℕ) : ℝ) = 2 / 3 by norm_num]
    have hsplit1 : (Real.log N) ^ (-(1 : ℝ) / 3) * Real.log N =
        (Real.log N) ^ ((2 : ℝ) / 3) := by
      have h1 := Real.rpow_add hL0 (-(1 : ℝ) / 3) (1 : ℝ)
      rw [Real.rpow_one, show (-(1 : ℝ) / 3) + 1 = 2 / 3 by norm_num] at h1
      exact h1.symm
    have hsplit2 : (c / Real.log N) * Real.log N = c := div_mul_cancel₀ c hL0.ne'
    have hδL : 3 * c * A ^ 2 * (Real.log N) ^ ((2 : ℝ) / 3) + c ≤ δ * Real.log N := by
      calc 3 * c * A ^ 2 * (Real.log N) ^ ((2 : ℝ) / 3) + c
          = (3 * c * A ^ 2 * (Real.log N) ^ (-(1 : ℝ) / 3)) * Real.log N +
              (c / Real.log N) * Real.log N := by
            rw [show (3 * c * A ^ 2 * (Real.log N) ^ (-(1 : ℝ) / 3)) * Real.log N =
                3 * c * A ^ 2 * ((Real.log N) ^ (-(1 : ℝ) / 3) * Real.log N) by ring,
              hsplit1, hsplit2]
        _ ≤ (δ / 2) * Real.log N + (δ / 2) * Real.log N :=
            add_le_add (mul_le_mul_of_nonneg_right hs1N hL0.le)
              (mul_le_mul_of_nonneg_right hs2N hL0.le)
        _ = δ * Real.log N := by ring
    calc β * Real.log N = (c * A ^ 3 - δ) * Real.log N := by rw [hβδ]
      _ = c * A ^ 3 * Real.log N - δ * Real.log N := by ring
      _ ≤ c * A ^ 3 * Real.log N -
            (3 * c * A ^ 2 * (Real.log N) ^ ((2 : ℝ) / 3) + c) := by linarith [hδL]
      _ = c * ((A * (Real.log N) ^ ((1 : ℝ) / 3)) ^ 3 -
            3 * (A * (Real.log N) ^ ((1 : ℝ) / 3)) ^ 2 - 1) := by rw [hx3, hx2]; ring
      _ ≤ c * ((qN A N : ℝ) - 1) ^ 3 :=
          mul_le_mul_of_nonneg_left (hxpow.trans hqcube) hc.le
  -- eventually the geometric ratio is at most `1/2`
  have hr_half : ∀ᶠ N : ℕ in atTop, Real.exp (-c * ((qN A N : ℝ) - 1) ^ 2) ≤ 1 / 2 := by
    have hK : ∀ᶠ N : ℕ in atTop,
        1 + Real.log 2 / c + 1 ≤ (qN A N : ℝ) := hqtop.eventually_ge_atTop _
    filter_upwards [hK, hq2] with N hN hq2N
    have hq1 : (1 : ℝ) ≤ (qN A N : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ (qN A N : ℝ) := by exact_mod_cast hq2N
      linarith
    have hcq1 : Real.log 2 ≤ c * ((qN A N : ℝ) - 1) := by
      have h2 : c * (Real.log 2 / c + 1) = Real.log 2 + c := by
        rw [mul_add, mul_comm c (Real.log 2 / c), div_mul_cancel₀ _ hc.ne', mul_one]
      have h1 : Real.log 2 + c ≤ c * ((qN A N : ℝ) - 1) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left (by linarith) hc.le
      linarith
    have hsq : (qN A N : ℝ) - 1 ≤ ((qN A N : ℝ) - 1) ^ 2 := by
      calc (qN A N : ℝ) - 1 = ((qN A N : ℝ) - 1) * 1 := (mul_one _).symm
        _ ≤ ((qN A N : ℝ) - 1) * ((qN A N : ℝ) - 1) :=
            mul_le_mul_of_nonneg_left hq1 (by linarith)
        _ = ((qN A N : ℝ) - 1) ^ 2 := (pow_two _).symm
    have hcq2 : Real.log 2 ≤ c * ((qN A N : ℝ) - 1) ^ 2 :=
      hcq1.trans (mul_le_mul_of_nonneg_left hsq hc.le)
    calc Real.exp (-c * ((qN A N : ℝ) - 1) ^ 2)
        ≤ Real.exp (-Real.log 2) := by
          apply Real.exp_le_exp.mpr
          rw [neg_mul]
          exact neg_le_neg hcq2
      _ = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          norm_num
  -- the squeezing sequence `2C · N^{-(β-1)} → 0`
  have hconv : ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) * Real.exp (-β * Real.log N) = (N : ℝ) ^ (-(β - 1 : ℝ)) := by
    intro N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    calc (N : ℝ) * Real.exp (-β * Real.log N)
        = Real.exp (Real.log N) * Real.exp (-β * Real.log N) := by rw [Real.exp_log hN0]
      _ = Real.exp (Real.log N + (-β) * Real.log N) := (Real.exp_add _ _).symm
      _ = Real.exp ((1 - β) * Real.log N) := by congr 1; ring
      _ = (N : ℝ) ^ ((1 - β : ℝ)) := by
          rw [Real.rpow_def_of_pos hN0]; congr 1; ring
      _ = (N : ℝ) ^ (-(β - 1 : ℝ)) := by rw [show ((1 : ℝ) - β) = -(β - 1) by ring]
  have hfin : Tendsto (fun N : ℕ => (2 * C) * ((N : ℝ) ^ (-(β - 1 : ℝ)))) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) < β - 1 := by linarith
    have h := (tendsto_rpow_neg_atTop h0).comp tendsto_natCast_atTop_atTop
    have h2 := h.const_mul (2 * C)
    simpa [Function.comp_def, mul_zero] using h2
  apply squeeze_zero'
  · filter_upwards with N
    exact mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg fun j => hα0 _)
  · filter_upwards [hq2, hβbound, hr_half, eventually_ge_atTop 1] with N hq2N hβN hrN hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hinv2 : (1 - Real.exp (-c * ((qN A N : ℝ) - 1) ^ 2))⁻¹ ≤ 2 := by
      calc (1 - Real.exp (-c * ((qN A N : ℝ) - 1) ^ 2))⁻¹
          = 1 / (1 - Real.exp (-c * ((qN A N : ℝ) - 1) ^ 2)) := inv_eq_one_div _
        _ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) (by linarith)
        _ = 2 := by norm_num
    calc (N : ℝ) * ∑' j : ℕ, alpha (qN A N + j)
        ≤ (N : ℝ) * (C * Real.exp (-c * ((qN A N : ℝ) - 1) ^ 3) *
            (1 - Real.exp (-c * ((qN A N : ℝ) - 1) ^ 2))⁻¹) :=
          mul_le_mul_of_nonneg_left (tsum_alpha_tail_le hC hc hα hα0 hq2N)
            (Nat.cast_nonneg _)
      _ ≤ (N : ℝ) * (C * Real.exp (-c * ((qN A N : ℝ) - 1) ^ 3) * 2) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left hinv2 (mul_nonneg hC.le (Real.exp_pos _).le)
      _ ≤ (N : ℝ) * (C * Real.exp (-β * Real.log N) * 2) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
          apply mul_le_mul_of_nonneg_left _ hC.le
          apply Real.exp_le_exp.mpr
          rw [neg_mul, neg_mul]
          exact neg_le_neg hβN
      _ = (2 * C) * ((N : ℝ) * Real.exp (-β * Real.log N)) := by ring
      _ = (2 * C) * ((N : ℝ) ^ (-(β - 1 : ℝ))) := by rw [hconv N hN1]
  · exact hfin

/-! ### T3/T4: integer-extension squeeze data -/

/-- `ηₙ = log(1 + 1/n) → 0`. -/
lemma tendsto_log_one_add_div :
    Tendsto (fun n : ℕ => Real.log (1 + 1 / (n : ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  have hg : Tendsto Real.log (𝓝 (1 + 0 : ℝ)) (𝓝 (Real.log (1 + 0 : ℝ))) :=
    Real.continuousAt_log (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have h := hg.comp h1
  simpa [Function.comp_def, Real.log_one] using h

/-- `log(n+1) - log n = log(1 + 1/n)`. -/
lemma log_succ_sub_log {n : ℕ} (hn : 1 ≤ n) :
    Real.log (↑(n + 1)) - Real.log (↑n) = Real.log (1 + 1 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Nat.cast_add_one]
  have h1 : ((n : ℝ) + 1) / (n : ℝ) = 1 + 1 / (n : ℝ) := by
    field_simp [hn0.ne']
  rw [← h1, Real.log_div (by linarith : ((n : ℝ) + 1) ≠ 0) hn0.ne']

/-- The successive-log ratio tends to `1`. -/
lemma tendsto_log_ratio_one :
    Tendsto (fun n : ℕ => Real.log (↑(n + 1)) / Real.log (↑n)) atTop (𝓝 1) := by
  have hηL : Tendsto (fun n : ℕ => Real.log (1 + 1 / (n : ℝ)) / Real.log (↑n))
      atTop (𝓝 0) := by
    have h := tendsto_log_one_add_div.mul tendsto_one_div_L
    simp only [mul_zero] at h
    apply Tendsto.congr' _ h
    filter_upwards with n
    rw [mul_one_div]
  have h : Tendsto (fun n : ℕ => 1 + Real.log (1 + 1 / (n : ℝ)) / Real.log (↑n))
      atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hηL
  simp only [add_zero] at h
  apply Tendsto.congr' _ h
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hL := (log_nat_pos hn).ne'
  have hsum : 1 + Real.log (1 + 1 / (n : ℝ)) / Real.log (↑n) =
      (Real.log (↑n) + Real.log (1 + 1 / (n : ℝ))) / Real.log (↑n) := by
    rw [add_div, div_self hL]
  rw [hsum, div_eq_div_iff hL hL]
  linear_combination (Real.log (↑n)) * (log_succ_sub_log (show 1 ≤ n by omega)).symm

/-- Any fixed real power of the successive-log ratio tends to `1`. -/
lemma tendsto_log_ratio_rpow (p : ℝ) :
    Tendsto (fun n : ℕ => (Real.log (↑(n + 1)) / Real.log (↑n)) ^ p) atTop (𝓝 1) := by
  have hcont : ContinuousAt (fun x : ℝ => x ^ p) 1 :=
    ContinuousAt.rpow_const continuousAt_id (Or.inl one_ne_zero)
  have h := hcont.tendsto.comp tendsto_log_ratio_one
  simpa [Function.comp_def, Real.one_rpow] using h

/-- Conjugate bound for the exponent `2/3`: for `ρ ≥ 1`,
`0 ≤ ρ^{2/3} - 1 ≤ (ρ² - 1)/3`, exact via `w³ - 1 = (w - 1)(w² + w + 1)`
with `w = ρ^{2/3}` (so `w³ = ρ²`). -/
lemma rpow_two_thirds_sub_one_bounds {ρ : ℝ} (hρ : 1 ≤ ρ) :
    0 ≤ ρ ^ ((2 : ℝ) / 3) - 1 ∧ ρ ^ ((2 : ℝ) / 3) - 1 ≤ (ρ ^ 2 - 1) / 3 := by
  have hρ0 : (0 : ℝ) ≤ ρ := zero_le_one.trans hρ
  have hw1 : 1 ≤ ρ ^ ((2 : ℝ) / 3) := Real.one_le_rpow hρ (by norm_num)
  have hw3 : (ρ ^ ((2 : ℝ) / 3)) ^ 3 = ρ ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0,
      show (2 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 2 by norm_num, Real.rpow_two]
  have hpos : (0 : ℝ) < (ρ ^ ((2 : ℝ) / 3)) ^ 2 + ρ ^ ((2 : ℝ) / 3) + 1 := by
    nlinarith [hw1]
  have hden3 : (3 : ℝ) ≤ (ρ ^ ((2 : ℝ) / 3)) ^ 2 + ρ ^ ((2 : ℝ) / 3) + 1 := by
    nlinarith [hw1]
  have hnum : (0 : ℝ) ≤ ρ ^ 2 - 1 := by nlinarith [hρ]
  refine ⟨by linarith, ?_⟩
  have hsub : ρ ^ ((2 : ℝ) / 3) - 1 =
      (ρ ^ 2 - 1) / ((ρ ^ ((2 : ℝ) / 3)) ^ 2 + ρ ^ ((2 : ℝ) / 3) + 1) := by
    rw [eq_div_iff hpos.ne']
    linear_combination hw3
  rw [hsub]
  exact div_le_div_of_nonneg_left hnum (by norm_num) hden3

/-- Conjugate bound for the exponent `-1/3`: for `ρ ≥ 1`,
`0 ≤ 1 - ρ^{-1/3} ≤ (ρ - 1)/3`, via `ρ - 1 = (v - 1)(v² + v + 1)` with
`v = ρ^{1/3}` and `1 - v⁻¹ = (v - 1)/v ≤ v - 1`. -/
lemma one_sub_rpow_neg_third_bounds {ρ : ℝ} (hρ : 1 ≤ ρ) :
    0 ≤ 1 - ρ ^ (-(1 : ℝ) / 3) ∧ 1 - ρ ^ (-(1 : ℝ) / 3) ≤ (ρ - 1) / 3 := by
  have hρ0 : (0 : ℝ) ≤ ρ := zero_le_one.trans hρ
  have hv1 : 1 ≤ ρ ^ ((1 : ℝ) / 3) := Real.one_le_rpow hρ (by norm_num)
  have hv3 : (ρ ^ ((1 : ℝ) / 3)) ^ 3 = ρ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0,
      show (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hpos : (0 : ℝ) < (ρ ^ ((1 : ℝ) / 3)) ^ 2 + ρ ^ ((1 : ℝ) / 3) + 1 := by
    nlinarith [hv1]
  have hden3 : (3 : ℝ) ≤ (ρ ^ ((1 : ℝ) / 3)) ^ 2 + ρ ^ ((1 : ℝ) / 3) + 1 := by
    nlinarith [hv1]
  have hnum : (0 : ℝ) ≤ ρ - 1 := by linarith
  have hrneg : ρ ^ (-(1 : ℝ) / 3) = (ρ ^ ((1 : ℝ) / 3))⁻¹ := rpow_neg_one_third hρ0
  constructor
  · rw [hrneg]
    have h := inv_le_one_of_one_le₀ hv1
    linarith
  · rw [hrneg]
    have h1 : 1 - (ρ ^ ((1 : ℝ) / 3))⁻¹ = (ρ ^ ((1 : ℝ) / 3) - 1) / ρ ^ ((1 : ℝ) / 3) := by
      rw [eq_div_iff (zero_lt_one.trans_le hv1).ne', sub_mul,
        inv_mul_cancel₀ (zero_lt_one.trans_le hv1).ne']
      ring
    rw [h1]
    calc (ρ ^ ((1 : ℝ) / 3) - 1) / ρ ^ ((1 : ℝ) / 3)
        ≤ ρ ^ ((1 : ℝ) / 3) - 1 := div_le_self (by linarith) hv1
      _ = (ρ - 1) / ((ρ ^ ((1 : ℝ) / 3)) ^ 2 + ρ ^ ((1 : ℝ) / 3) + 1) := by
          rw [eq_div_iff hpos.ne']
          linear_combination hv3
      _ ≤ (ρ - 1) / 3 := div_le_div_of_nonneg_left hnum (by norm_num) hden3

/-- T3: `b_{n+1} / b_n → 1`. -/
theorem gumbelB_succ_ratio :
    Tendsto (fun n : ℕ => gumbelB (n + 1) / gumbelB n) atTop (𝓝 1) := by
  apply Tendsto.congr' _ (tendsto_log_ratio_rpow (-(1 : ℝ) / 3))
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hL := log_nat_pos hn
  have hL' := log_nat_pos (by omega : 2 ≤ n + 1)
  have hγ := airyGamma_pos.ne'
  have hE := (Real.rpow_pos_of_pos hL (-(1 : ℝ) / 3)).ne'
  have h23 : (2 * airyGamma / 3 : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hγ) (by norm_num)
  show (Real.log (↑(n + 1)) / Real.log (↑n)) ^ (-(1 : ℝ) / 3) = gumbelB (n + 1) / gumbelB n
  rw [Real.div_rpow hL'.le hL.le (-(1 : ℝ) / 3)]
  unfold gumbelB
  rw [div_eq_div_iff hE (mul_ne_zero h23 hE)]
  ring

/-- The main term `(L'^{2/3} - L^{2/3}) L^{1/3}` of `(a_{n+1} - a_n)/b_n`
tends to `0`: it equals `L (ρ^{2/3} - 1)` for `ρ = L'/L`, and the conjugate
bound gives `0 ≤ L(ρ^{2/3} - 1) ≤ η (ρ+1)/3 ≤ η` with `η = log(1+1/n)`. -/
lemma gumbelA_diff_main_tendsto :
    Tendsto (fun n : ℕ =>
      ((Real.log (↑(n + 1))) ^ ((2 : ℝ) / 3) - (Real.log (↑n)) ^ ((2 : ℝ) / 3)) *
        (Real.log (↑n)) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
  have hρ2 : ∀ᶠ n : ℕ in atTop, Real.log (↑(n + 1)) / Real.log (↑n) ≤ 2 := by
    have h := (Metric.tendsto_nhds.mp tendsto_log_ratio_one) 1 one_pos
    filter_upwards [h] with n hn
    rw [Real.dist_eq] at hn
    have h1 := le_abs_self (Real.log (↑(n + 1)) / Real.log (↑n) - 1)
    linarith
  apply squeeze_zero_norm' _ tendsto_log_one_add_div
  filter_upwards [eventually_ge_atTop 2, hρ2] with n hn hρ2n
  have hL := log_nat_pos hn
  have hL' := log_nat_pos (by omega : 2 ≤ n + 1)
  have hρ : (0 : ℝ) < Real.log (↑(n + 1)) / Real.log (↑n) := div_pos hL' hL
  have hρ1 : 1 ≤ Real.log (↑(n + 1)) / Real.log (↑n) := by
    rw [one_le_div hL]
    exact Real.log_le_log (by exact_mod_cast (show (1 : ℕ) ≤ n by omega))
      (by exact_mod_cast (show n ≤ n + 1 by omega))
  have hηnn : 0 ≤ Real.log (1 + 1 / (n : ℝ)) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ)))
  have hρ1eq : Real.log (↑(n + 1)) / Real.log (↑n) - 1 =
      Real.log (1 + 1 / (n : ℝ)) / Real.log (↑n) := by
    have h3 := log_succ_sub_log (show 1 ≤ n by omega)
    rw [show Real.log (↑(n + 1)) / Real.log (↑n) - 1 =
        (Real.log (↑(n + 1)) - Real.log (↑n)) / Real.log (↑n) by field_simp [hL.ne'], h3]
  have hid : ((Real.log (↑(n + 1))) ^ ((2 : ℝ) / 3) - (Real.log (↑n)) ^ ((2 : ℝ) / 3)) *
        (Real.log (↑n)) ^ ((1 : ℝ) / 3) =
      Real.log (↑n) * ((Real.log (↑(n + 1)) / Real.log (↑n)) ^ ((2 : ℝ) / 3) - 1) := by
    have hL'eq : Real.log (↑(n + 1)) =
        (Real.log (↑(n + 1)) / Real.log (↑n)) * Real.log (↑n) :=
      (div_mul_cancel₀ _ hL.ne').symm
    conv_lhs => rw [hL'eq]
    rw [Real.mul_rpow hρ.le hL.le]
    have hsum : (Real.log (↑n)) ^ ((2 : ℝ) / 3) * (Real.log (↑n)) ^ ((1 : ℝ) / 3) =
        Real.log (↑n) := by
      rw [← Real.rpow_add hL, show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num, Real.rpow_one]
    linear_combination ((Real.log (↑(n + 1)) / Real.log (↑n)) ^ ((2 : ℝ) / 3) - 1) * hsum
  have hbnd := rpow_two_thirds_sub_one_bounds hρ1
  have hLρ : Real.log (↑n) * (Real.log (↑(n + 1)) / Real.log (↑n) - 1) =
      Real.log (1 + 1 / (n : ℝ)) := by
    rw [hρ1eq, ← mul_div_assoc, mul_div_cancel_left₀ _ hL.ne']
  rw [Real.norm_eq_abs, hid]
  have hT0 : (0 : ℝ) ≤ Real.log (↑n) *
      ((Real.log (↑(n + 1)) / Real.log (↑n)) ^ ((2 : ℝ) / 3) - 1) :=
    mul_nonneg hL.le hbnd.1
  rw [abs_of_nonneg hT0]
  calc Real.log (↑n) * ((Real.log (↑(n + 1)) / Real.log (↑n)) ^ ((2 : ℝ) / 3) - 1)
      ≤ Real.log (↑n) * (((Real.log (↑(n + 1)) / Real.log (↑n)) ^ 2 - 1) / 3) :=
        mul_le_mul_of_nonneg_left hbnd.2 hL.le
    _ = (Real.log (↑n) * (Real.log (↑(n + 1)) / Real.log (↑n) - 1)) *
          (Real.log (↑(n + 1)) / Real.log (↑n) + 1) / 3 := by ring
    _ = Real.log (1 + 1 / (n : ℝ)) *
          ((Real.log (↑(n + 1)) / Real.log (↑n) + 1) / 3) := by rw [hLρ, mul_div_assoc]
    _ ≤ Real.log (1 + 1 / (n : ℝ)) * 1 := by
        apply mul_le_mul_of_nonneg_left _ hηnn
        rw [div_le_one (by norm_num : (0 : ℝ) < 3)]
        linarith
    _ = Real.log (1 + 1 / (n : ℝ)) := mul_one _

/-- The correction term of `(a_{n+1} - a_n)/b_n`,
`(log L' + c₀)(L'/L)^{-1/3} - (log L + c₀)` with `c₀ = log(3/(2π³))`, tends
to `0`: it equals `log ρ · ρ^{-1/3} + (log L + c₀)(ρ^{-1/3} - 1)`, where the
first summand is `0 · 1` and the second is bounded by `(2/3) η (log L / L)`. -/
lemma gumbelA_diff_corr_tendsto :
    Tendsto (fun n : ℕ =>
      (Real.log (Real.log (↑(n + 1))) + Real.log (3 / (2 * Real.pi ^ 3))) *
        ((Real.log (↑(n + 1))) ^ (-(1 : ℝ) / 3) * (Real.log (↑n)) ^ ((1 : ℝ) / 3)) -
        (Real.log (Real.log (↑n)) + Real.log (3 / (2 * Real.pi ^ 3)))) atTop (𝓝 0) := by
  have hlogρ : Tendsto (fun n : ℕ => Real.log (Real.log (↑(n + 1)) / Real.log (↑n)))
      atTop (𝓝 0) := by
    have hg : Tendsto Real.log (𝓝 1) (𝓝 (Real.log 1)) := Real.continuousAt_log one_ne_zero
    have h := hg.comp tendsto_log_ratio_one
    simpa [Function.comp_def, Real.log_one] using h
  have hρpow := tendsto_log_ratio_rpow (-(1 : ℝ) / 3)
  have hP1 : Tendsto (fun n : ℕ =>
      Real.log (Real.log (↑(n + 1)) / Real.log (↑n)) *
        (Real.log (↑(n + 1)) / Real.log (↑n)) ^ (-(1 : ℝ) / 3)) atTop (𝓝 0) := by
    have h := hlogρ.mul hρpow
    simpa using h
  have hlogL : Tendsto (fun n : ℕ => Real.log (Real.log (↑n))) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_L_atTop
  have hP2 : Tendsto (fun n : ℕ =>
      (Real.log (Real.log (↑n)) + Real.log (3 / (2 * Real.pi ^ 3))) *
        ((Real.log (↑(n + 1)) / Real.log (↑n)) ^ (-(1 : ℝ) / 3) - 1)) atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ =>
        (2 / 3) * (Real.log (1 + 1 / (n : ℝ)) *
          (Real.log (Real.log (↑n)) / Real.log (↑n)))) atTop (𝓝 0) := by
      have h := tendsto_log_one_add_div.mul tendsto_logL_div_L
      simp only [mul_zero] at h
      have h2 := h.const_mul (2 / 3)
      rwa [mul_zero] at h2
    apply squeeze_zero_norm' _ hg
    filter_upwards [eventually_ge_atTop 2,
      hlogL.eventually_ge_atTop (max 0 |Real.log (3 / (2 * Real.pi ^ 3))|)] with n hn hlogLn
    have hL := log_nat_pos hn
    have hL' := log_nat_pos (by omega : 2 ≤ n + 1)
    have hρ1 : 1 ≤ Real.log (↑(n + 1)) / Real.log (↑n) := by
      rw [one_le_div hL]
      exact Real.log_le_log (by exact_mod_cast (show (1 : ℕ) ≤ n by omega))
        (by exact_mod_cast (show n ≤ n + 1 by omega))
    have hbnd := one_sub_rpow_neg_third_bounds hρ1
    have hη0 : 0 ≤ Real.log (1 + 1 / (n : ℝ)) :=
      Real.log_nonneg (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ)))
    have hlogL0 : 0 ≤ Real.log (Real.log (↑n)) := (max_le_iff.mp hlogLn).1
    have hρ1eq : Real.log (↑(n + 1)) / Real.log (↑n) - 1 =
        Real.log (1 + 1 / (n : ℝ)) / Real.log (↑n) := by
      have h3 := log_succ_sub_log (show 1 ≤ n by omega)
      rw [show Real.log (↑(n + 1)) / Real.log (↑n) - 1 =
          (Real.log (↑(n + 1)) - Real.log (↑n)) / Real.log (↑n) by field_simp [hL.ne'], h3]
    have habs1 : |(Real.log (↑(n + 1)) / Real.log (↑n)) ^ (-(1 : ℝ) / 3) - 1| ≤
        Real.log (1 + 1 / (n : ℝ)) / Real.log (↑n) / 3 := by
      rw [abs_sub_comm, abs_of_nonneg hbnd.1]
      calc 1 - (Real.log (↑(n + 1)) / Real.log (↑n)) ^ (-(1 : ℝ) / 3)
          ≤ (Real.log (↑(n + 1)) / Real.log (↑n) - 1) / 3 := hbnd.2
        _ = Real.log (1 + 1 / (n : ℝ)) / Real.log (↑n) / 3 := by rw [hρ1eq]
    have habs0 : |Real.log (Real.log (↑n)) + Real.log (3 / (2 * Real.pi ^ 3))| ≤
        2 * Real.log (Real.log (↑n)) := by
      have h1 : |Real.log (3 / (2 * Real.pi ^ 3))| ≤ Real.log (Real.log (↑n)) :=
        (max_le_iff.mp hlogLn).2
      calc |Real.log (Real.log (↑n)) + Real.log (3 / (2 * Real.pi ^ 3))|
          ≤ |Real.log (Real.log (↑n))| + |Real.log (3 / (2 * Real.pi ^ 3))| := abs_add_le _ _
        _ = Real.log (Real.log (↑n)) + |Real.log (3 / (2 * Real.pi ^ 3))| := by
            rw [abs_of_nonneg hlogL0]
        _ ≤ 2 * Real.log (Real.log (↑n)) := by linarith
    rw [Real.norm_eq_abs, abs_mul]
    calc |Real.log (Real.log (↑n)) + Real.log (3 / (2 * Real.pi ^ 3))| *
          |(Real.log (↑(n + 1)) / Real.log (↑n)) ^ (-(1 : ℝ) / 3) - 1|
        ≤ (2 * Real.log (Real.log (↑n))) *
            (Real.log (1 + 1 / (n : ℝ)) / Real.log (↑n) / 3) :=
          mul_le_mul habs0 habs1 (abs_nonneg _) (by linarith)
      _ = (2 / 3) * (Real.log (1 + 1 / (n : ℝ)) *
            (Real.log (Real.log (↑n)) / Real.log (↑n))) := by
          field_simp [hL.ne']
  have hsum := hP1.add hP2
  simp only [add_zero] at hsum
  apply Tendsto.congr' _ hsum
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hL := log_nat_pos hn
  have hL' := log_nat_pos (by omega : 2 ≤ n + 1)
  have hρ0 : (0 : ℝ) < Real.log (↑(n + 1)) / Real.log (↑n) := div_pos hL' hL
  have hL'eq : Real.log (↑(n + 1)) =
      (Real.log (↑(n + 1)) / Real.log (↑n)) * Real.log (↑n) :=
    (div_mul_cancel₀ _ hL.ne').symm
  have hlogL' : Real.log (Real.log (↑(n + 1))) =
      Real.log (Real.log (↑(n + 1)) / Real.log (↑n)) + Real.log (Real.log (↑n)) := by
    conv_lhs => rw [hL'eq]
    exact Real.log_mul hρ0.ne' hL.ne'
  have hpow : (Real.log (↑(n + 1))) ^ (-(1 : ℝ) / 3) * (Real.log (↑n)) ^ ((1 : ℝ) / 3) =
      (Real.log (↑(n + 1)) / Real.log (↑n)) ^ (-(1 : ℝ) / 3) := by
    have h3' : (Real.log (↑n)) ^ (-(1 : ℝ) / 3) * (Real.log (↑n)) ^ ((1 : ℝ) / 3) = 1 := by
      rw [← Real.rpow_add hL, show (-(1 : ℝ) / 3) + 1 / 3 = 0 by norm_num, Real.rpow_zero]
    conv_lhs => rw [hL'eq]
    rw [Real.mul_rpow hρ0.le hL.le, mul_assoc, h3', mul_one]
  rw [hlogL', hpow]
  ring

/-- The exact algebraic identity behind T4, valid for `n ≥ 2`:
`(a_{n+1} - a_n)/b_n = (3/2)(L'^{2/3} - L^{2/3})L^{1/3} +
(1/6)((log L' + c₀)L'^{-1/3}L^{1/3} - (log L + c₀))`. -/
lemma gumbelA_succ_diff_eq {n : ℕ} (hn : 2 ≤ n) :
    (gumbelA (n + 1) - gumbelA n) / gumbelB n =
      (3 / 2) * (((Real.log (↑(n + 1))) ^ ((2 : ℝ) / 3) - (Real.log (↑n)) ^ ((2 : ℝ) / 3)) *
          (Real.log (↑n)) ^ ((1 : ℝ) / 3)) +
        (1 / 6) * ((Real.log (Real.log (↑(n + 1))) + Real.log (3 / (2 * Real.pi ^ 3))) *
            ((Real.log (↑(n + 1))) ^ (-(1 : ℝ) / 3) * (Real.log (↑n)) ^ ((1 : ℝ) / 3)) -
          (Real.log (Real.log (↑n)) + Real.log (3 / (2 * Real.pi ^ 3)))) := by
  have hL := log_nat_pos hn
  have hγ := airyGamma_pos.ne'
  have hE := (Real.rpow_pos_of_pos hL (-(1 : ℝ) / 3)).ne'
  have h23 : (2 * airyGamma / 3 : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hγ) (by norm_num)
  have hB0 : ((2 * airyGamma / 3) * (Real.log (↑n)) ^ (-(1 : ℝ) / 3)) ≠ 0 :=
    mul_ne_zero h23 hE
  have hnum : gumbelA (n + 1) - gumbelA n =
      airyGamma * ((Real.log (↑(n + 1))) ^ ((2 : ℝ) / 3) - (Real.log (↑n)) ^ ((2 : ℝ) / 3)) +
        (airyGamma / 9) *
          ((Real.log (Real.log (↑(n + 1))) + Real.log (3 / (2 * Real.pi ^ 3))) *
              (Real.log (↑(n + 1))) ^ (-(1 : ℝ) / 3) -
            (Real.log (Real.log (↑n)) + Real.log (3 / (2 * Real.pi ^ 3))) *
              (Real.log (↑n)) ^ (-(1 : ℝ) / 3)) := by
    unfold gumbelA
    push_cast
    ring
  have hB : gumbelB n = (2 * airyGamma / 3) * (Real.log (↑n)) ^ (-(1 : ℝ) / 3) := rfl
  have h3' : (Real.log (↑n)) ^ ((1 : ℝ) / 3) * (Real.log (↑n)) ^ (-(1 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add hL, show (1 : ℝ) / 3 + -(1 : ℝ) / 3 = 0 by norm_num,
      Real.rpow_zero]
  rw [hnum, hB, div_eq_iff hB0]
  linear_combination
    (-(airyGamma *
        ((Real.log (↑(n + 1))) ^ ((2 : ℝ) / 3) - (Real.log (↑n)) ^ ((2 : ℝ) / 3)) +
      airyGamma / 9 * (Real.log (Real.log (↑(n + 1))) + Real.log (3 / (2 * Real.pi ^ 3))) *
        (Real.log (↑(n + 1))) ^ (-(1 : ℝ) / 3))) * h3'

/-- T4: `(a_{n+1} - a_n) / b_n → 0`. -/
theorem gumbelA_succ_diff :
    Tendsto (fun n : ℕ => (gumbelA (n + 1) - gumbelA n) / gumbelB n) atTop (𝓝 0) := by
  have h := (gumbelA_diff_main_tendsto.const_mul (3 / 2)).add
    (gumbelA_diff_corr_tendsto.const_mul (1 / 6))
  simp only [mul_zero, add_zero] at h
  apply Tendsto.congr' _ h
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (gumbelA_succ_diff_eq hn).symm

end Airy1Gumbel
