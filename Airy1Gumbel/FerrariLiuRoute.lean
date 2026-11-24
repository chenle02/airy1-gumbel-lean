/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.BlockLaw
import Airy1Gumbel.SharpTail

open Filter MeasureTheory Set Asymptotics
open scoped Topology BigOperators Asymptotics

namespace Airy1Gumbel

/-- The positive-integer summand in the persistence rate of Ferrari and Liu (2024),
Theorem 1.1. -/
noncomputable def ferrariLiuRateTerm (c : ℝ) (n : ℕ) : ℝ :=
  -2 * (n : ℝ) ^ (-5 / 3 : ℝ) *
    deriv airyAiReal (2 * (n : ℝ) ^ (2 / 3 : ℝ) * c)

/-- The persistence rate of Ferrari and Liu (2024), Theorem 1.1, as used in
Remark 5.3 of arXiv:2611.23658v1. -/
noncomputable def ferrariLiuKappa (c : ℝ) : ℝ :=
  ∑' j : ℕ, ferrariLiuRateTerm c (j + 1)

/-- Persistence probability for the event that the path stays at or below `c`
on the whole closed interval `[0, L]`. -/
noncomputable def ferrariLiuP {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℝ → Ω → ℝ) (c L : ℝ) : ℝ :=
  μ.real {ω | ∀ t ∈ Icc (0 : ℝ) L, A t ω ≤ c}

/-- The two-branch bound parameter of Ferrari and Liu (2024), Section 2.4,
at `r = √(2c)`. -/
noncomputable def ferrariLiuBeta (c : ℝ) : ℝ :=
  let r := Real.sqrt (2 * c)
  max (2 * Real.exp (r ^ 3 / 3 - 2 * r * c))
    (Real.exp ((r - 1 / 7) ^ 3 / 3 - 2 * (r - 1 / 7) * c))

/-- The higher-degree trace remainder majorant at a positive index. -/
noncomputable def ferrariLiuErrorTerm (c L : ℝ) (n : ℕ) : ℝ :=
  (7 : ℝ) ^ (n + 1) * ferrariLiuBeta c ^ n / (n : ℝ) *
    Real.exp (-4 * L ^ 3 / (3 * (n : ℝ) ^ 2))

/-- The trace remainder majorant from Remark 5.3 of arXiv:2611.23658v1,
using Proposition 2.5 and Section 2.4 of Ferrari and Liu (2024). -/
noncomputable def ferrariLiuErrorBound (c L : ℝ) : ℝ :=
  2 * Real.exp (-4 * L ^ 3 / 3) +
    ∑' j : ℕ, ferrariLiuErrorTerm c L (j + 2)

/-- The finite-length persistence expansion used in Remark 5.3 of
arXiv:2611.23658v1. The bounds come from Proposition 2.5 and Section 2.4 of
Ferrari and Liu (2024), with the exact two-branch parameter at `r = √(2c)`.
The Airy₁ instance uses the continuous paths on `[0, ∞)` and the convention
with one-point CDF `F₁(2s)`. The fields give the raw estimates for real
`c ≥ 3/2` and `L ≥ 1`.

The expansion assumes the Ferrari–Liu trace-log identity
`log det(1 - K) = -Σ Tr(K^n)/n`, used without proof in their (2.10)
(Section 2) and (2.110) (Section 2.4).
Ferrari–Liu's equation (2.66) has a sign typo.
The rate uses the sign in their Lemma 2.6 and in the assembled trace formulas:
(2.58), Proposition 2.13, and the definition of `κₙ` after (2.114).
The degree-one error uses coefficient 2. The display in Proposition 2.5
prints 1, and the intermediate estimates give
`(1 + β) exp(-4 L³/3) ≤ 2 exp(-4 L³/3)`.
Equation, lemma and proposition numbers are those of the published paper
(Electron. J. Probab. 29 (2024), paper 149; the same in arXiv:2402.10661v2). -/
structure FerrariLiuPersistence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ℝ → Ω → ℝ) where
  S : ℝ → ℝ
  E : ℝ → ℝ → ℝ
  measurable_event : ∀ c L : ℝ, (3 / 2 : ℝ) ≤ c → 1 ≤ L →
    MeasurableSet {ω | ∀ t ∈ Icc (0 : ℝ) L, A t ω ≤ c}
  expansion : ∀ c L : ℝ, (3 / 2 : ℝ) ≤ c → 1 ≤ L →
    ferrariLiuP μ A c L = Real.exp (-(L * ferrariLiuKappa c) - S c + E c L)
  offset_bound : ∀ c : ℝ, (3 / 2 : ℝ) ≤ c →
    |S c| ≤ -6 * Real.log (1 - 2 * ferrariLiuBeta c)
  error_bound : ∀ c L : ℝ, (3 / 2 : ℝ) ≤ c → 1 ≤ L →
    |E c L| ≤ ferrariLiuErrorBound c L

/-- The persistence event of the continuous Airy₁ version is measurable for every
interval length in the persistence expansion. -/
theorem ferrariLiu_event_measurable_airy1 (h : Airy1FddPositive)
    (c L : ℝ) (hL : 1 ≤ L) :
    MeasurableSet {f | ∀ x ∈ Icc (0 : ℝ) L, airy1ContR h x f ≤ c} := by
  have hmesh := setOf_forall_Icc_le_eq_iInter h (M := c) (le_refl (0 : ℝ))
    (zero_lt_one.trans_le hL)
  rw [zero_add] at hmesh
  rw [hmesh]
  exact MeasurableSet.iInter (fun n => measurableSet_meshEvent h 0 L c n)

/-- The corrected exponential envelope bounds both branches of the Ferrari–Liu parameter. -/
theorem ferrariLiuBeta_envelope {c : ℝ} (hc : (3 / 2 : ℝ) ≤ c) :
    0 < ferrariLiuBeta c ∧ ferrariLiuBeta c ≤
      2 * Real.exp (-AiryConj.kappaC * c ^ (3 / 2 : ℝ) + Real.sqrt (2 * c) / 49) := by
  have hc0 : 0 < c := by linarith
  let r := Real.sqrt (2 * c)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 2 * c := Real.sq_sqrt (by positivity)
  have hpow : (2 * c) ^ (3 / 2 : ℝ) = (2 * c) * r := by
    dsimp [r]
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by positivity : 0 < 2 * c), Real.rpow_one]
  have hmain : r ^ 3 / 3 - 2 * r * c = -AiryConj.kappaC * c ^ (3 / 2 : ℝ) := by
    rw [neg_mul, AiryConj.kappaC_mul_rpow_eq hc0.le, hpow, pow_succ, hr2]
    ring
  have hshift :
      (r - 1 / 7) ^ 3 / 3 - 2 * (r - 1 / 7) * c =
        (r ^ 3 / 3 - 2 * r * c) + r / 49 - 1 / 1029 := by
    linear_combination -(1 / 7 : ℝ) * hr2
  unfold ferrariLiuBeta
  change 0 < max (2 * Real.exp _) (Real.exp _) ∧
    max (2 * Real.exp (r ^ 3 / 3 - 2 * r * c))
      (Real.exp ((r - 1 / 7) ^ 3 / 3 - 2 * (r - 1 / 7) * c)) ≤
      2 * Real.exp (-AiryConj.kappaC * c ^ (3 / 2 : ℝ) + r / 49)
  refine ⟨lt_of_lt_of_le (mul_pos two_pos (Real.exp_pos _)) (le_max_left _ _),
    max_le ?_ ?_⟩
  · rw [hmain]
    gcongr
    linarith
  · rw [hshift, hmain]
    calc
      _ ≤ Real.exp (-AiryConj.kappaC * c ^ (3 / 2 : ℝ) + r / 49) :=
        Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by linarith [Real.exp_nonneg (-AiryConj.kappaC * c ^ (3 / 2 : ℝ) + r / 49)]

/-- The envelope exponent is bounded above by a negative multiple of the square root. -/
theorem ferrariLiuBeta_exponent_le {c : ℝ} (hc : (3 / 2 : ℝ) ≤ c) :
    -AiryConj.kappaC * c ^ (3 / 2 : ℝ) + Real.sqrt (2 * c) / 49 ≤
      -(97 / 49 : ℝ) * Real.sqrt (2 * c) := by
  have hc0 : 0 < c := by linarith
  rw [neg_mul, AiryConj.kappaC_mul_rpow_eq hc0.le,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity : 0 < 2 * c),
    Real.rpow_one, ← Real.sqrt_eq_rpow]
  nlinarith [mul_nonneg (show 0 ≤ 2 * c - 3 by linarith) (Real.sqrt_nonneg (2 * c))]

/-- The uniform upper bound on the geometric ratio in the trace remainder. -/
theorem ferrariLiuBeta_uniform {c : ℝ} (hc : (3 / 2 : ℝ) ≤ c) :
    7 * ferrariLiuBeta c ≤ (7 / 8 : ℝ) := by
  have hs : (5 / 3 : ℝ) ≤ Real.sqrt (2 * c) := Real.le_sqrt_of_sq_le (by linarith)
  have h : -AiryConj.kappaC * c ^ (3 / 2 : ℝ) + Real.sqrt (2 * c) / 49 ≤ -3 :=
    (ferrariLiuBeta_exponent_le hc).trans (by linarith)
  have hexp : (16 : ℝ) ≤ Real.exp 3 := by
    calc
      (16 : ℝ) ≤ ∑ i ∈ Finset.range 5, (3 : ℝ) ^ i / i.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ _ := Real.sum_le_exp_of_nonneg (by norm_num) 5
  calc
    7 * ferrariLiuBeta c ≤ 14 * Real.exp (-3) := by
      have hb := (ferrariLiuBeta_envelope hc).2
      have he := Real.exp_le_exp.mpr h
      linarith
    _ ≤ (7 / 8 : ℝ) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      linarith

/-- The two-branch parameter vanishes as the threshold tends to infinity. -/
theorem ferrariLiuBeta_tendsto :
    Tendsto ferrariLiuBeta atTop (𝓝 0) := by
  have hs : Tendsto (fun c : ℝ => Real.sqrt (2 * c)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id)
  have he : Tendsto (fun c : ℝ => 2 * Real.exp (-Real.sqrt (2 * c))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hs)).const_mul 2
  refine squeeze_zero' ?_ ?_ he
  · filter_upwards [eventually_ge_atTop (3 / 2 : ℝ)] with c hc
    exact (ferrariLiuBeta_envelope hc).1.le
  · filter_upwards [eventually_ge_atTop (3 / 2 : ℝ)] with c hc
    refine (ferrariLiuBeta_envelope hc).2.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr ((ferrariLiuBeta_exponent_le hc).trans ?_)) two_pos.le)
    linarith [Real.sqrt_nonneg (2 * c)]

/-- Bound on a higher-degree error term before summation. -/
theorem ferrariLiuErrorTerm_le_geometric {c L : ℝ}
    (hc : (3 / 2 : ℝ) ≤ c) (_hL : 1 ≤ L) {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ ferrariLiuErrorTerm c L n ∧
      ferrariLiuErrorTerm c L n ≤
        7 * (7 * ferrariLiuBeta c) ^ n * Real.exp (-4 * L ^ 3 / (3 * (n : ℝ) ^ 2)) := by
  have hb := (ferrariLiuBeta_envelope hc).1.le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  unfold ferrariLiuErrorTerm
  rw [pow_succ', mul_assoc, ← mul_pow]
  refine ⟨by positivity, mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)⟩
  rw [div_le_iff₀ (zero_lt_one.trans_le hn1)]
  exact le_mul_of_one_le_right (by positivity) hn1

/-- The higher-degree error majorant is summable in the persistence regime. -/
theorem ferrariLiuErrorTerm_summable {c L : ℝ}
    (hc : (3 / 2 : ℝ) ≤ c) (hL : 1 ≤ L) :
    Summable (fun j : ℕ => ferrariLiuErrorTerm c L (j + 2)) := by
  let q : ℝ := 7 * ferrariLiuBeta c
  have hq0 : 0 ≤ q := mul_nonneg (by norm_num) (ferrariLiuBeta_envelope hc).1.le
  have hq1 : q < 1 := (ferrariLiuBeta_uniform hc).trans_lt (by norm_num)
  refine Summable.of_nonneg_of_le (fun j =>
    (ferrariLiuErrorTerm_le_geometric hc hL (n := j + 2) (by omega)).1) ?_
    ((summable_geometric_of_lt_one hq0 hq1).mul_left 7)
  intro j
  have h := (ferrariLiuErrorTerm_le_geometric hc hL (n := j + 2) (by omega)).2
  have hL0 : 0 ≤ L := by linarith
  refine h.trans ((mul_le_of_le_one_right (by positivity : 0 ≤ 7 * q ^ (j + 2))
    (Real.exp_le_one_iff.mpr (by rw [neg_mul, neg_div]; exact neg_nonpos.mpr (by positivity) :
      -4 * L ^ 3 / (3 * ((j + 2 : ℕ) : ℝ) ^ 2) ≤ 0))).trans ?_)
  rw [pow_add]
  gcongr
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hq0 hq1.le)

/-- The raw error majorant decays exponentially in length, uniformly over the thresholds. -/
theorem ferrariLiuErrorBound_uniform :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ c L : ℝ, (3 / 2 : ℝ) ≤ c → 1 ≤ L →
        ferrariLiuErrorBound c L ≤ C * Real.exp (-(δ * L)) := by
  let a := Real.sqrt (7 / 8 : ℝ)
  have ha0 : 0 < a := Real.sqrt_pos.2 (by norm_num)
  have ha1 : a < 1 := Real.sqrt_lt' (by norm_num) |>.2 (by norm_num)
  have ha2 : a ^ 2 = (7 / 8 : ℝ) := Real.sq_sqrt (by norm_num)
  let δ := min (1 : ℝ) (-Real.log a)
  have hδ0 : 0 < δ := lt_min one_pos (neg_pos.mpr (Real.log_neg ha0 ha1))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδa : δ ≤ -Real.log a := min_le_right _ _
  refine ⟨2 + 7 / (1 - a), δ, by positivity, hδ0, ?_⟩
  intro c L hc hL
  have hL0 : 0 ≤ L := by linarith
  let e := Real.exp (-(δ * L))
  have he0 : 0 ≤ e := Real.exp_nonneg _
  have hsum := ferrariLiuErrorTerm_summable hc hL
  have hgeom := ((summable_geometric_of_lt_one ha0.le ha1).mul_left 7).mul_right e
  have hpoint : ∀ j : ℕ, ferrariLiuErrorTerm c L (j + 2) ≤ (7 * a ^ j) * e := by
    intro j
    let n := j + 2
    have hn : 2 ≤ n := by dsimp [n]; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hb := (ferrariLiuBeta_envelope hc).1.le
    have hq : (7 * ferrariLiuBeta c) ^ n ≤ a ^ n * a ^ n := by
      rw [← mul_pow, ← pow_two, ha2]
      exact pow_le_pow_left₀ (by positivity) (ferrariLiuBeta_uniform hc) n
    have hpow : a ^ n ≤ a ^ j := by
      dsimp [n]
      rw [pow_add]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ ha0.le ha1.le)
    have hp := (ferrariLiuErrorTerm_le_geometric hc hL hn).2
    change ferrariLiuErrorTerm c L n ≤ _
    by_cases hnL : (n : ℝ) ≤ L
    · have hnSq : (n : ℝ) ^ 2 ≤ L ^ 2 := by gcongr
      have hfrac : L ≤ 4 * L ^ 3 / (3 * (n : ℝ) ^ 2) := by
        rw [le_div_iff₀ (by positivity : 0 < 3 * (n : ℝ) ^ 2)]
        nlinarith [mul_le_mul_of_nonneg_left hnSq hL0, pow_nonneg hL0 3]
      have hExp : Real.exp (-4 * L ^ 3 / (3 * (n : ℝ) ^ 2)) ≤ e := by
        refine Real.exp_le_exp.mpr ?_
        rw [neg_mul, neg_div]
        linarith [mul_le_mul_of_nonneg_right hδ1 hL0]
      calc
        _ ≤ _ := hp
        _ ≤ (7 * a ^ j) * e := by
          gcongr
          exact hq.trans ((mul_le_of_le_one_right (by positivity : 0 ≤ a ^ n)
            (pow_le_one₀ ha0.le ha1.le)).trans hpow)
    · have hExp : Real.exp (-4 * L ^ 3 / (3 * (n : ℝ) ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by rw [neg_mul, neg_div]; exact neg_nonpos.mpr (by positivity))
      have haExp : a ^ n ≤ e := by
        rw [← Real.exp_log ha0, ← Real.exp_nat_mul]
        refine Real.exp_le_exp.mpr ?_
        calc
          (n : ℝ) * Real.log a ≤ L * Real.log a :=
            mul_le_mul_of_nonpos_right (le_of_not_ge hnL) (Real.log_neg ha0 ha1).le
          _ ≤ -(δ * L) := by nlinarith [mul_le_mul_of_nonneg_right hδa hL0]
      calc
        _ ≤ _ := hp
        _ ≤ (7 * (a ^ j * e)) * 1 := by
          gcongr
          exact hq.trans (mul_le_mul hpow haExp (by positivity) (by positivity))
        _ = (7 * a ^ j) * e := by ring
  have hfirst : Real.exp (-4 * L ^ 3 / 3) ≤ e := by
    apply Real.exp_le_exp.mpr
    have hL2 : 1 ≤ L ^ 2 := by simpa using pow_le_pow_left₀ (by norm_num) hL 2
    nlinarith [mul_le_mul_of_nonneg_left hL2 hL0, mul_le_mul_of_nonneg_right hδ1 hL0]
  have htsum := hsum.tsum_le_tsum hpoint hgeom
  unfold ferrariLiuErrorBound
  calc
    _ ≤ 2 * e + ∑' j : ℕ, (7 * a ^ j) * e := add_le_add (by gcongr) htsum
    _ = (2 + 7 / (1 - a)) * e := by
      rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one ha0.le ha1]
      ring

/-- The raw Ferrari–Liu bounds give a vanishing offset and a length remainder
with constants uniform over all thresholds in the expansion. -/
theorem ferrariLiu_remainders {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A : ℝ → Ω → ℝ}
    (FL : FerrariLiuPersistence μ A) :
    Tendsto FL.S atTop (𝓝 0) ∧
      ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
        ∀ c L : ℝ, (3 / 2 : ℝ) ≤ c → 1 ≤ L →
          |FL.E c L| ≤ C * Real.exp (-(δ * L)) := by
  obtain ⟨C, δ, hC, hδ, hbound⟩ := ferrariLiuErrorBound_uniform
  refine ⟨?_, C, δ, hC, hδ, fun c L hc hL => (FL.error_bound c L hc hL).trans (hbound c L hc hL)⟩
  have harg : Tendsto (fun c => 1 - 2 * ferrariLiuBeta c) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (ferrariLiuBeta_tendsto.const_mul 2)
  have hlog : Tendsto (fun c => -6 * Real.log (1 - 2 * ferrariLiuBeta c)) atTop (𝓝 0) := by
    simpa using ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg).const_mul (-6)
  refine squeeze_zero_norm' ?_ hlog
  filter_upwards [eventually_ge_atTop (3 / 2 : ℝ)] with c hc
  simpa only [Real.norm_eq_abs] using FL.offset_bound c hc

/-- The leading Airy derivative estimate bounds each rate term above its argument cutoff. -/
theorem ferrariLiuRateTerm_bound :
    ∃ D a : ℝ, 0 < D ∧ 0 < a ∧
      ∀ (c : ℝ) (n : ℕ), 0 < c → 1 ≤ n → a ≤ 2 * (n : ℝ) ^ (2 / 3 : ℝ) * c →
        |ferrariLiuRateTerm c n| ≤
          D * c ^ (1 / 4 : ℝ) * Real.exp (-AiryConj.kappaC * c ^ (3 / 2 : ℝ)) ^ n := by
  obtain ⟨C, hC, hbound⟩ := isBigO_iff'.mp deriv_airyAiReal_isEquivalent.isBigO
  obtain ⟨a, ha⟩ := eventually_atTop.mp hbound
  refine ⟨C * AiryConj.Cstar, max a 1, mul_pos hC AiryConj.Cstar_pos,
    one_pos.trans_le (le_max_right _ _), ?_⟩
  intro c n hc hn hlarge
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  let m := (n : ℝ) ^ (2 / 3 : ℝ) * c
  have hm : 0 < m := by positivity
  have hb := ha (2 * m) ((le_max_left _ _).trans (by simpa [m, mul_assoc] using hlarge))
  have hlead : -(1 / (2 * Real.sqrt Real.pi)) * (2 * m) ^ (1 / 4 : ℝ) *
      Real.exp (-(2 / 3) * (2 * m) ^ (3 / 2 : ℝ)) = -(AiryConj.leadAiDeriv (2 * m)) := by
    unfold AiryConj.leadAiDeriv
    ring
  rw [hlead, norm_neg, Real.norm_eq_abs, Real.norm_of_nonneg
    (AiryConj.leadAiDeriv_pos (by positivity : 0 < 2 * m)).le] at hb
  have hmPow : m ^ (3 / 2 : ℝ) = (n : ℝ) * c ^ (3 / 2 : ℝ) := by
    dsimp [m]
    rw [Real.mul_rpow (by positivity) hc.le, ← Real.rpow_mul hn0.le]
    norm_num
  have hpref :
      (n : ℝ) ^ (-5 / 3 : ℝ) * m ^ (1 / 4 : ℝ) =
        (n : ℝ) ^ (-3 / 2 : ℝ) * c ^ (1 / 4 : ℝ) := by
    dsimp [m]
    rw [Real.mul_rpow (by positivity) hc.le, ← Real.rpow_mul hn0.le, ← mul_assoc,
      ← Real.rpow_add hn0]
    norm_num
  have hnPow : (n : ℝ) ^ (-3 / 2 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-3 / 2 : ℝ) ≤ 0)
  calc
    _ = 2 * (n : ℝ) ^ (-5 / 3 : ℝ) * |deriv airyAiReal (2 * m)| := by
      unfold ferrariLiuRateTerm
      rw [show 2 * (n : ℝ) ^ (2 / 3 : ℝ) * c = 2 * m by dsimp [m]; ring,
        abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hn0.le _)]
      norm_num
    _ ≤ 2 * (n : ℝ) ^ (-5 / 3 : ℝ) * (C * AiryConj.leadAiDeriv (2 * m)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C * ((n : ℝ) ^ (-5 / 3 : ℝ) * AiryConj.rhoM m) := by
      rw [← AiryConj.two_mul_leadAiDeriv_two_mul hm]
      ring
    _ = (n : ℝ) ^ (-3 / 2 : ℝ) *
        (C * AiryConj.Cstar * c ^ (1 / 4 : ℝ) *
          Real.exp (-AiryConj.kappaC * c ^ (3 / 2 : ℝ)) ^ n) := by
      rw [AiryConj.rhoM, hmPow, ← Real.exp_nat_mul,
        show -(AiryConj.kappaC) * ((n : ℝ) * c ^ (3 / 2 : ℝ)) =
          (n : ℝ) * (-(AiryConj.kappaC) * c ^ (3 / 2 : ℝ)) by ring]
      linear_combination C * AiryConj.Cstar *
        Real.exp ((n : ℝ) * (-AiryConj.kappaC * c ^ (3 / 2 : ℝ))) * hpref
    _ ≤ _ := mul_le_of_le_one_left (by
      have := AiryConj.Cstar_pos
      positivity) hnPow

/-- The Ferrari–Liu rate series is summable for every strictly positive threshold. -/
theorem ferrariLiuKappa_summable {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℕ =>
      -2 * ((j + 1 : ℕ) : ℝ) ^ (-5 / 3 : ℝ) *
        deriv airyAiReal (2 * ((j + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) * c)) := by
  change Summable (fun j : ℕ => ferrariLiuRateTerm c (j + 1))
  obtain ⟨D, a, hD, _, hbound⟩ := ferrariLiuRateTerm_bound
  let t := Real.exp (-AiryConj.kappaC * c ^ (3 / 2 : ℝ))
  have hκ : 0 < AiryConj.kappaC := AiryConj.kappaC_pos
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by
    rw [neg_mul]
    exact neg_lt_zero.mpr (by positivity))
  have hn : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hlarge : Tendsto (fun j : ℕ => 2 * ((j + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) * c)
      atTop atTop :=
    (((tendsto_rpow_atTop (by norm_num : 0 < (2 / 3 : ℝ))).comp hn).const_mul_atTop
      two_pos).atTop_mul_const hc
  refine ((summable_geometric_of_lt_one ht0.le ht1).mul_left
    (D * c ^ (1 / 4 : ℝ) * t)).of_norm_bounded_eventually_nat ?_
  filter_upwards [hlarge.eventually_ge_atTop a] with j hj
  have hb := hbound c (j + 1) hc (by omega) hj
  rw [Real.norm_eq_abs]
  convert hb using 1
  rw [pow_succ]
  ring

/-- Split the persistence rate into its degree-one term and the remaining series. -/
theorem ferrariLiuKappa_eq_head_add_tail {c : ℝ} (hc : 0 < c) :
    ferrariLiuKappa c = -2 * deriv airyAiReal (2 * c) +
      ∑' j : ℕ, ferrariLiuRateTerm c (j + 2) := by
  unfold ferrariLiuKappa
  have hs : Summable (fun j : ℕ => ferrariLiuRateTerm c (j + 1)) := ferrariLiuKappa_summable hc
  rw [hs.tsum_eq_zero_add]
  change ferrariLiuRateTerm c 1 + (∑' j : ℕ, ferrariLiuRateTerm c (j + 2)) = _
  congr 1
  unfold ferrariLiuRateTerm
  simp

/-- The exponential factor in the Airy right-tail rate tends to zero. -/
theorem ferrariLiuDecay_tendsto :
    Tendsto (fun c : ℝ => Real.exp (-AiryConj.kappaC * c ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul_atTop
    AiryConj.kappaC_pos
  refine (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h)).congr (fun c => ?_)
  simp only [Function.comp_apply, neg_mul]

/-- The higher-degree rate series has twice the leading exponential decay exponent. -/
theorem ferrariLiuKappa_tail_isBigO :
    (fun c : ℝ => ∑' j : ℕ, ferrariLiuRateTerm c (j + 2)) =O[atTop]
      (fun c : ℝ => c ^ (1 / 4 : ℝ) *
        Real.exp (-(2 * AiryConj.kappaC) * c ^ (3 / 2 : ℝ))) := by
  obtain ⟨D, a, hD, ha, hbound⟩ := ferrariLiuRateTerm_bound
  refine isBigO_iff.mpr ⟨2 * D, ?_⟩
  filter_upwards [eventually_ge_atTop a, (tendsto_order.mp ferrariLiuDecay_tendsto).2
    (1 / 2 : ℝ) (by norm_num)] with c hc ht
  have hc0 := ha.trans_le hc
  let t := Real.exp (-AiryConj.kappaC * c ^ (3 / 2 : ℝ))
  have ht0 : 0 < t := Real.exp_pos _
  have ht2 : t ≤ 1 / 2 := ht.le
  have ht1 : t < 1 := ht2.trans_lt (by norm_num)
  let majorant := fun j : ℕ => (D * c ^ (1 / 4 : ℝ) * t ^ 2) * t ^ j
  have hgeom : Summable majorant := (summable_geometric_of_lt_one ht0.le ht1).mul_left _
  have hpoint : ∀ j : ℕ, ‖ferrariLiuRateTerm c (j + 2)‖ ≤ majorant j := by
    intro j
    have hj : (1 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j + 2 by omega)
    have hpow := Real.one_le_rpow hj (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have harg : a ≤ 2 * ((j + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ) * c := by
      nlinarith [mul_le_mul_of_nonneg_right hpow hc0.le]
    have hb := hbound c (j + 2) hc0 (by omega) harg
    rw [Real.norm_eq_abs]
    convert hb using 1
    dsimp [majorant]
    rw [pow_add]
    ring
  have hsum : Summable (fun j : ℕ => ferrariLiuRateTerm c (j + 2)) :=
    hgeom.of_norm_bounded hpoint
  have hden : 0 < 1 - t := sub_pos.mpr ht1
  have hinv : (1 - t)⁻¹ ≤ 2 := by
    rw [← one_div, div_le_iff₀ hden]
    linarith
  calc
    _ ≤ ∑' j : ℕ, ‖ferrariLiuRateTerm c (j + 2)‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' j : ℕ, majorant j := hsum.norm.tsum_le_tsum hpoint hgeom
    _ = (D * c ^ (1 / 4 : ℝ) * t ^ 2) * (1 - t)⁻¹ := by
      simp only [majorant, tsum_mul_left, tsum_geometric_of_lt_one ht0.le ht1]
    _ ≤ (D * c ^ (1 / 4 : ℝ) * t ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by
      rw [Real.norm_of_nonneg (by positivity), show t ^ 2 =
        Real.exp (-(2 * AiryConj.kappaC) * c ^ (3 / 2 : ℝ)) by
        dsimp [t]
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring]
      ring

/-- A multiplier tending to zero gives a lower-order term relative to the tail rate. -/
theorem ferrariLiu_mul_rhoM_isLittleO {f : ℝ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) :
    (fun c => f c * AiryConj.rhoM c) =o[atTop] AiryConj.rhoM := by
  simpa only [one_mul] using ((isLittleO_one_iff ℝ).mpr hf).mul_isBigO (isBigO_refl AiryConj.rhoM atTop)

/-- The persistence rate is asymptotic to the one-block tail rate at large thresholds. -/
theorem ferrariLiuKappa_div_rhoM_tendsto :
    Tendsto (fun c : ℝ => ferrariLiuKappa c / AiryConj.rhoM c) atTop (𝓝 1) := by
  have hheadO : (fun c : ℝ => -2 * deriv airyAiReal (2 * c) - AiryConj.rhoM c) =O[atTop]
      (fun c => c ^ (-3 / 2 : ℝ) * AiryConj.rhoM c) := by
    simpa using AiryConj.neg_two_mul_T_deriv_sub_T_rhoM_isBigO 1 one_pos
  have hpow : Tendsto (fun c : ℝ => c ^ (-3 / 2 : ℝ)) atTop (𝓝 0) := by
    convert tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2) using 1
    norm_num
  have hhead := hheadO.trans_isLittleO (ferrariLiu_mul_rhoM_isLittleO hpow)
  have hscale :
      (fun c : ℝ => c ^ (1 / 4 : ℝ) *
        Real.exp (-(2 * AiryConj.kappaC) * c ^ (3 / 2 : ℝ))) =o[atTop] AiryConj.rhoM := by
    have hdecay : Tendsto (fun c : ℝ =>
        Real.exp (-AiryConj.kappaC * c ^ (3 / 2 : ℝ)) / AiryConj.Cstar) atTop (𝓝 0) := by
      simpa using ferrariLiuDecay_tendsto.div_const AiryConj.Cstar
    refine (ferrariLiu_mul_rhoM_isLittleO hdecay).congr_left (fun c => ?_)
    unfold AiryConj.rhoM
    rw [show -(2 * AiryConj.kappaC) * c ^ (3 / 2 : ℝ) =
      (-AiryConj.kappaC * c ^ (3 / 2 : ℝ)) + (-AiryConj.kappaC * c ^ (3 / 2 : ℝ)) by ring,
      Real.exp_add]
    field_simp [AiryConj.Cstar_pos.ne']
  have htail := ferrariLiuKappa_tail_isBigO.trans_isLittleO hscale
  have hsum : (fun c => ferrariLiuKappa c - AiryConj.rhoM c) =o[atTop] AiryConj.rhoM := by
    refine (hhead.add htail).congr' ?_ (EventuallyEq.rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    rw [ferrariLiuKappa_eq_head_add_tail hc]
    ring
  have hlim := hsum.tendsto_div_nhds_zero.add (tendsto_const_nhds (x := (1 : ℝ)))
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  field_simp [AiryConj.rhoM_pos hc |>.ne']
  ring

/-- The Ferrari–Liu rate at the Gumbel levels, multiplied by the interval length,
has the same limit as the normalized one-block tail rate. -/
theorem ferrariLiuKappa_gumbel_normalization (z : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * ferrariLiuKappa (gumbelU N z))
      atTop (𝓝 (Real.exp (-z))) := by
  have hu := gumbelU_tendsto_atTop z
  have hρ : Tendsto (fun N : ℕ => (N : ℝ) * AiryConj.rhoM (gumbelU N z)) atTop
      (𝓝 (Real.exp (-z))) := by
    refine (gumbel_normalization z).congr' ?_
    filter_upwards [hu.eventually_gt_atTop 0] with N hN
    rw [exp_neg_airyH_eq hN]
  have hlim := hρ.mul (ferrariLiuKappa_div_rhoM_tendsto.comp hu)
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hu.eventually_gt_atTop 0] with N hN
  change (N : ℝ) * AiryConj.rhoM (gumbelU N z) *
    (ferrariLiuKappa (gumbelU N z) / AiryConj.rhoM (gumbelU N z)) = _
  field_simp [AiryConj.rhoM_pos hN |>.ne']

/-- Remark 5.3 of arXiv:2611.23658v1. The persistence expansion gives the
Gumbel limit of the continuous Airy₁ maximum over integer interval lengths. -/
theorem gumbel_limit_continuum_airy1_ferrariLiu
    (h : Airy1FddPositive) (hT : GOELeftTail)
    (FL : FerrariLiuPersistence (airy1Law h) (airy1SRP h hT).A) (z : ℝ) :
    Tendsto (fun N : ℕ => (airy1Law h).real
        {f | ∀ x ∈ Icc (0 : ℝ) N, airy1ContR h x f ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  have hu := gumbelU_tendsto_atTop z
  obtain ⟨hS, C, δ, _, hδ, hbound⟩ := ferrariLiu_remainders FL
  have hcL : ∀ᶠ N : ℕ in atTop, (3 / 2 : ℝ) ≤ gumbelU N z ∧ 1 ≤ (N : ℝ) :=
    (hu.eventually_ge_atTop _).and
      ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop 1)
  have he : Tendsto (fun N : ℕ => C * Real.exp (-(δ * (N : ℝ)))) atTop (𝓝 0) := by
    have hneg := tendsto_neg_atTop_atBot.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hδ)
    simpa only [mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp hneg).const_mul C
  have hE : Tendsto (fun N : ℕ => FL.E (gumbelU N z) N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ he
    filter_upwards [hcL] with N hN
    simpa only [Real.norm_eq_abs] using hbound (gumbelU N z) N hN.1 hN.2
  have hexp := ((ferrariLiuKappa_gumbel_normalization z).neg.sub (hS.comp hu)).add hE
  rw [sub_zero, add_zero] at hexp
  refine (Real.continuous_exp.continuousAt.tendsto.comp hexp).congr' ?_
  filter_upwards [hcL] with N hN
  exact (FL.expansion _ _ hN.1 hN.2).symm

end Airy1Gumbel
