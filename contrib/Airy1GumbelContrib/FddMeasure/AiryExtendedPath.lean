/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.HilbertSchmidt.KernelHS
import Airy1GumbelContrib.AiryKernel.BackwardAiry
import Airy1GumbelContrib.TwoInterval.FRExponents
import Airy1GumbelContrib.TwoInterval.TwoIntervalN2
import Airy1GumbelContrib.FredholmDet.BlockDet
import Airy1GumbelContrib.FredholmDet.Multiplicativity
import Airy1GumbelContrib.FredholmDet.SimonBound
import Airy1GumbelContrib.FredholmDet.TracePowDet
import Airy1GumbelContrib.Fdd.GaussTools
import Airy1GumbelContrib.Fdd.FddIndep
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.MeasureTheory.Group.Prod
import Airy1GumbelContrib.FddMeasure.FredholmSeries
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace AiryFdd

/-- Counting measure on observation times times Lebesgue measure on the spatial coordinate. -/
noncomputable def airySiteMeasure (I : Finset ℝ) : Measure (I × ℝ) :=
  (Measure.count : Measure I).prod volume

/-- The extended Airy₁ kernel, with the heat term on strictly increasing time pairs. -/
noncomputable def airyExtendedKer (u v s₁ s₂ : ℝ) : ℝ :=
  Real.exp ((v - u) * (s₁ + s₂) + (2 / 3) * (v - u) ^ 3) *
    airyAiReal (s₁ + s₂ + (v - u) ^ 2) -
  (if u < v then heatKernel (v - u) (s₁ - s₂) else 0)

/-- The zero-based rank of an observation time in increasing order. -/
noncomputable def airyTimeRank (I : Finset ℝ) (i : I) : ℕ :=
  (I.filter (fun u => u < (i : ℝ))).card

/-- The polynomial weight at a tagged site, increasing in the time rank. -/
noncomputable def airyRankGauge (I : Finset ℝ) (i : I) (s : ℝ) : ℝ :=
  (1 + s ^ 2) ^ (2 * airyTimeRank I i)

/-- The extended Airy₁ kernel restricted to the open upper half-lines, with the row weight
divided by the column weight. -/
noncomputable def airyRankCutKer (I : Finset ℝ) (x : I → ℝ) :
    (I × ℝ) → (I × ℝ) → ℝ :=
  fun p q =>
    if x p.1 < p.2 ∧ x q.1 < q.2 then
      airyRankGauge I p.1 p.2 / airyRankGauge I q.1 q.2 *
        airyExtendedKer (p.1 : ℝ) (q.1 : ℝ) p.2 q.2
    else 0

/-- Time ranks strictly increase along the observation times. -/
theorem airyTimeRank_lt_of_lt (I : Finset ℝ) {i j : I} (hij : (i : ℝ) < (j : ℝ)) :
    airyTimeRank I i < airyTimeRank I j := by
  unfold airyTimeRank
  apply Finset.card_lt_card
  refine lt_of_le_of_ne ?_ ?_
  · intro u hu
    obtain ⟨huI, hui⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨huI, hui.trans hij⟩
  · intro heq
    have hi : (i : ℝ) ∈ I.filter (fun u => u < (j : ℝ)) :=
      Finset.mem_filter.mpr ⟨i.property, hij⟩
    rw [← heq] at hi
    exact (lt_irrefl (i : ℝ)) (Finset.mem_filter.mp hi).2

/-- The weight used in the rank gauge is strictly positive. -/
theorem airyRankGauge_pos (I : Finset ℝ) (i : I) (s : ℝ) :
    0 < airyRankGauge I i s := by
  unfold airyRankGauge
  positivity

/-- Cutting the extended kernel restricts both the row and column. -/
theorem airyRankCutKer_supported (I : Finset ℝ) (x : I → ℝ) :
    cutKernelSupported I x (airyRankCutKer I x) := by
  intro p q h
  unfold airyRankCutKer
  apply ite_eq_right
  rintro ⟨hp, hq⟩
  exact h.elim (fun hp' => (not_lt_of_ge hp') hp) (fun hq' => (not_lt_of_ge hq') hq)

/-- At fixed times the extended kernel is continuous in both spatial coordinates. -/
theorem continuous_airyExtendedKer (u v : ℝ) :
    Continuous (fun p : ℝ × ℝ => airyExtendedKer u v p.1 p.2) := by
  have hAi : Continuous airyAiReal :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_airyAiReal s).continuousAt
  have hsum : Continuous (fun p : ℝ × ℝ => p.1 + p.2) :=
    continuous_fst.add continuous_snd
  have hpole : Continuous (fun p : ℝ × ℝ =>
      Real.exp ((v - u) * (p.1 + p.2) + (2 / 3) * (v - u) ^ 3) *
        airyAiReal (p.1 + p.2 + (v - u) ^ 2)) :=
    (Real.continuous_exp.comp ((hsum.const_mul (v - u)).add_const _)).mul
      (hAi.comp (hsum.add_const _))
  by_cases h : u < v
  · have hdiff : Continuous (fun p : ℝ × ℝ => p.1 - p.2) :=
      continuous_fst.sub continuous_snd
    have hheat : Continuous (fun p : ℝ × ℝ => heatKernel (v - u) (p.1 - p.2)) :=
      (continuous_heatKernel (v - u)).comp hdiff
    simpa only [Pi.sub_def, airyExtendedKer, ite_eq_left h] using hpole.sub hheat
  · simpa only [airyExtendedKer, ite_eq_right h, sub_zero] using hpole

/-- Each cut block extends continuously across the boundary of its active quadrant. -/
theorem airyRankCutKer_continuous (I : Finset ℝ) (x : I → ℝ) :
    cutKernelContinuous I x (airyRankCutKer I x) := by
  intro i j
  refine ⟨fun p => airyRankGauge I i p.1 / airyRankGauge I j p.2 *
    airyExtendedKer (i : ℝ) (j : ℝ) p.1 p.2, ?_, ?_⟩
  · have hW (k : I) : Continuous (airyRankGauge I k) := by
      unfold airyRankGauge
      exact (continuous_const.add (continuous_id.pow 2)).pow _
    exact (((hW i).comp continuous_fst).div ((hW j).comp continuous_snd)
      (fun p => (airyRankGauge_pos I j p.2).ne')).mul
        (continuous_airyExtendedKer _ _) |>.continuousOn
  · intro s t hs ht
    simp only [airyRankCutKer, ite_eq_left (And.intro hs ht)]

/-- A polynomial in a nonnegative variable is bounded after multiplication by its
decaying exponential. -/
theorem add_one_pow_mul_exp_neg_le (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) ^ m * Real.exp (-y) ≤ (m.factorial : ℝ) * Real.exp 1 := by
  have hm : 0 < (m.factorial : ℝ) := by positivity
  have h := Real.pow_div_factorial_le_exp (1 + y) (by positivity) m
  have hb := (div_le_iff₀ hm).mp h
  calc
    (1 + y) ^ m * Real.exp (-y) ≤
        (Real.exp (1 + y) * m.factorial) * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = (m.factorial : ℝ) * Real.exp 1 := by
      rw [mul_comm (Real.exp (1 + y)), mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The Gaussian heat kernel absorbs any fixed polynomial in the spatial difference. -/
theorem heatKernel_mul_weight_le (m : ℕ) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, (1 + d ^ 2) ^ m * heatKernel T d ≤ C := by
  let scale : ℝ := 1 + 4 * T
  let prefactor : ℝ := (4 * Real.pi * T) ^ (-1 / 2 : ℝ)
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hprefactor : 0 ≤ prefactor := by dsimp [prefactor]; positivity
  refine ⟨prefactor * scale ^ m * ((m.factorial : ℝ) * Real.exp 1), by positivity, ?_⟩
  intro d
  let y : ℝ := d ^ 2 / (4 * T)
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hd : d ^ 2 = 4 * T * y := by
    dsimp [y]
    field_simp
  have hbase : 1 + d ^ 2 ≤ scale * (1 + y) := by
    dsimp [scale]
    rw [hd]
    nlinarith
  rw [heatKernel]
  change (1 + d ^ 2) ^ m * (prefactor * Real.exp (-d ^ 2 / (4 * T))) ≤ _
  rw [neg_div]
  change (1 + d ^ 2) ^ m * (prefactor * Real.exp (-y)) ≤ _
  calc
    _ ≤ (scale * (1 + y)) ^ m * (prefactor * Real.exp (-y)) := by gcongr
    _ = prefactor * scale ^ m * ((1 + y) ^ m * Real.exp (-y)) := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_one_pow_mul_exp_neg_le m hy) (by positivity)

/-- Along a forward-time heat block, the gap of the ranks leaves an integrable row
weight after absorbing the polynomial in the spatial difference. -/
theorem heatKernel_rank_row_bound (I : Finset ℝ) {i j : I}
    (hij : (i : ℝ) < (j : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ,
      airyRankGauge I i s / airyRankGauge I j t * heatKernel ((j : ℝ) - i) (s - t)
        ≤ C * (1 + s ^ 2)⁻¹ := by
  let m := 2 * airyTimeRank I i + 1
  let n := 2 * airyTimeRank I j
  have hmn : m ≤ n := by
    have hr := airyTimeRank_lt_of_lt I hij
    dsimp [m, n]
    omega
  have hT : 0 < (j : ℝ) - i := sub_pos.mpr hij
  obtain ⟨C, hC, hheat⟩ := heatKernel_mul_weight_le m hT
  refine ⟨2 ^ m * C, by positivity, ?_⟩
  intro s t
  have hbase : 1 + s ^ 2 ≤ 2 * (1 + t ^ 2) * (1 + (s - t) ^ 2) := by
    nlinarith [sq_nonneg (s - 2 * t), mul_nonneg (sq_nonneg t) (sq_nonneg (s - t))]
  have hcomp : (1 + s ^ 2) ^ m ≤
      2 ^ m * (1 + t ^ 2) ^ n * (1 + (s - t) ^ 2) ^ m := by
    calc
      _ ≤ (2 * (1 + t ^ 2) * (1 + (s - t) ^ 2)) ^ m := by gcongr
      _ = 2 ^ m * (1 + t ^ 2) ^ m * (1 + (s - t) ^ 2) ^ m := by
        rw [mul_pow, mul_pow]
      _ ≤ _ := by
        have hpow : (1 + t ^ 2) ^ m ≤ (1 + t ^ 2) ^ n :=
          pow_le_pow_right₀ (by linarith [sq_nonneg t]) hmn
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  unfold airyRankGauge
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + s ^ 2)]
  have hden : 0 < (1 + t ^ 2) ^ n := by positivity
  have hh := heatKernel_nonneg hT (s - t)
  change ((1 + s ^ 2) ^ (2 * airyTimeRank I i) / (1 + t ^ 2) ^ n *
      heatKernel ((j : ℝ) - i) (s - t)) * (1 + s ^ 2) ≤ _
  calc
    _ = (1 + s ^ 2) ^ m / (1 + t ^ 2) ^ n * heatKernel ((j : ℝ) - i) (s - t) := by
      dsimp [m]
      rw [pow_succ]
      ring
    _ ≤ (2 ^ m * (1 + t ^ 2) ^ n * (1 + (s - t) ^ 2) ^ m) / (1 + t ^ 2) ^ n *
          heatKernel ((j : ℝ) - i) (s - t) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcomp hden.le) hh
    _ = 2 ^ m * ((1 + (s - t) ^ 2) ^ m * heatKernel ((j : ℝ) - i) (s - t)) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hheat (s - t)) (by positivity)

/-- The Airy profile is bounded by an exponential of any prescribed positive rate. -/
theorem airyAiReal_abs_le_exp_rate {a : ℝ} (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, |airyAiReal z| ≤ C * Real.exp (-a * z) := by
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le
  obtain ⟨C₁, hC₁, hAi⟩ := AiryTwoInt.airyAiReal_abs_le_exp32
  let M : ℝ := (3 * a / 2) ^ 2
  refine ⟨|C₀| * Real.exp (a * M) + C₁, by positivity, ?_⟩
  intro z
  by_cases hz : M ≤ z
  · have hz0 : 0 ≤ z := (sq_nonneg _).trans hz
    have hsqrt : 3 * a / 2 ≤ Real.sqrt z := Real.le_sqrt_of_sq_le hz
    have hpow : z ^ (3 / 2 : ℝ) = z * Real.sqrt z := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hz0 (by norm_num),
        Real.rpow_one, Real.sqrt_eq_rpow]
    have hdecay : -(2 / 3 : ℝ) * z ^ (3 / 2 : ℝ) ≤ -a * z := by
      rw [hpow]
      nlinarith [mul_le_mul_of_nonneg_left hsqrt hz0]
    exact (hAi hz0).trans <| mul_le_mul (le_add_of_nonneg_left (by positivity))
      (Real.exp_le_exp.mpr hdecay)
      (Real.exp_pos _).le (by positivity)
  · calc
      _ ≤ |C₀| := (hC₀ z).trans (le_abs_self _)
      _ = |C₀| * Real.exp (a * M + -a * M) := by simp
      _ ≤ (|C₀| * Real.exp (a * M) + C₁) * Real.exp (-a * z) := by
        rw [Real.exp_add, add_mul]
        have hdecay : -a * M ≤ -a * z :=
          mul_le_mul_of_nonpos_left (le_of_not_ge hz) (neg_nonpos.mpr ha)
        have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdecay)
          (by positivity : 0 ≤ |C₀| * Real.exp (a * M))
        linarith [mul_nonneg hC₁.le (Real.exp_pos (-a * z)).le]

/-- The weighted Airy part admits the same row envelope as the heat part on upper cuts. -/
theorem airyPole_rank_row_bound (I : Finset ℝ) (x : I → ℝ) (i j : I) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ, x i < s → x j < t →
      airyRankGauge I i s / airyRankGauge I j t *
        |Real.exp (((j : ℝ) - i) * (s + t) + (2 / 3) * ((j : ℝ) - i) ^ 3) *
          airyAiReal (s + t + ((j : ℝ) - i) ^ 2)| ≤ C * (1 + s ^ 2)⁻¹ := by
  let d : ℝ := (j : ℝ) - i
  let a : ℝ := |d| + 1
  let m : ℕ := 2 * airyTimeRank I i + 1
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hrate : d - a ≤ -1 := by dsimp [a]; linarith [le_abs_self d]
  obtain ⟨C, hC, hAi⟩ := airyAiReal_abs_le_exp_rate ha
  let b : ℝ := (d - a + 1) * x i + (d - a) * x j +
    (2 / 3) * d ^ 3 - a * d ^ 2 + 2 * |x i|
  refine ⟨C * Real.exp b * (((2 * m).factorial : ℝ) * Real.exp 1), by positivity, ?_⟩
  intro s t hs ht
  have hsum : d * (s + t) + (2 / 3) * d ^ 3 + -a * (s + t + d ^ 2) ≤
      b - |s| := by
    have hs' := mul_le_mul_of_nonpos_left hs.le (show d - a + 1 ≤ 0 by linarith)
    have ht' := mul_le_mul_of_nonpos_left ht.le (show d - a ≤ 0 by linarith)
    have habs : |s| - s ≤ 2 * |x i| := by
      rcases le_or_gt 0 s with h | h
      · rw [abs_of_nonneg h]
        linarith [abs_nonneg (x i)]
      · rw [abs_of_neg h]
        linarith [neg_le_abs (x i)]
    dsimp [b]
    linarith
  have hpole :
      |Real.exp (d * (s + t) + (2 / 3) * d ^ 3) * airyAiReal (s + t + d ^ 2)| ≤
        C * Real.exp b * Real.exp (-|s|) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (d * (s + t) + (2 / 3) * d ^ 3) *
          (C * Real.exp (-a * (s + t + d ^ 2))) :=
        mul_le_mul_of_nonneg_left (hAi _) (Real.exp_pos _).le
      _ = C * Real.exp (d * (s + t) + (2 / 3) * d ^ 3 + -a * (s + t + d ^ 2)) := by
        rw [Real.exp_add (d * (s + t) + (2 / 3) * d ^ 3) (-a * (s + t + d ^ 2))]
        ring
      _ ≤ _ := by
        rw [mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) hC
  have hW : 1 ≤ airyRankGauge I j t := by
    unfold airyRankGauge
    exact one_le_pow₀ (by linarith [sq_nonneg t])
  have hpoly : (1 + s ^ 2) ^ m * Real.exp (-|s|) ≤
      ((2 * m).factorial : ℝ) * Real.exp 1 := by
    have hbase : 1 + s ^ 2 ≤ (1 + |s|) ^ 2 := by
      nlinarith [abs_nonneg s, sq_abs s]
    refine le_trans ?_ (add_one_pow_mul_exp_neg_le (2 * m) (abs_nonneg s))
    rw [pow_mul]
    gcongr
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + s ^ 2)]
  change (airyRankGauge I i s / airyRankGauge I j t *
    |Real.exp (d * (s + t) + (2 / 3) * d ^ 3) * airyAiReal (s + t + d ^ 2)|) *
      (1 + s ^ 2) ≤ _
  calc
    _ ≤ (airyRankGauge I i s * (C * Real.exp b * Real.exp (-|s|))) *
        (1 + s ^ 2) := by
      have hd : airyRankGauge I i s / airyRankGauge I j t ≤ airyRankGauge I i s :=
        div_le_self (airyRankGauge_pos I i s).le hW
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hd hpole (abs_nonneg _) (airyRankGauge_pos I i s).le) (by positivity)
    _ = C * Real.exp b * ((1 + s ^ 2) ^ m * Real.exp (-|s|)) := by
      unfold airyRankGauge
      dsimp [m]
      rw [pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpoly (by positivity)

/-- On the active upper half-lines the cut extended kernel decays in the row coordinate
at the rate required for the Hadamard bound. -/
theorem airyRankCutKer_rowEnvelope (I : Finset ℝ) (x : I → ℝ) :
    cutKernelRowEnvelope I x (airyRankCutKer I x) := by
  classical
  have hblock (i j : I) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ, x i < s → x j < t →
      |airyRankCutKer I x (i, s) (j, t)| ≤ C * (1 + s ^ 2)⁻¹ := by
    obtain ⟨C, hC, hPole⟩ := airyPole_rank_row_bound I x i j
    by_cases hij : (i : ℝ) < (j : ℝ)
    · obtain ⟨H, hH, hHeat⟩ := heatKernel_rank_row_bound I hij
      refine ⟨C + H, add_nonneg hC hH, ?_⟩
      intro s t hs ht
      have hg : 0 ≤ airyRankGauge I i s / airyRankGauge I j t := by
        exact div_nonneg (airyRankGauge_pos I i s).le (airyRankGauge_pos I j t).le
      simp only [airyRankCutKer, ite_eq_left (And.intro hs ht),
        airyExtendedKer, ite_eq_left hij, abs_mul, abs_of_nonneg hg]
      grw [abs_sub, abs_of_nonneg (heatKernel_nonneg (sub_pos.mpr hij) (s - t))]
      rw [mul_add, add_mul]
      exact add_le_add (hPole s t hs ht) (hHeat s t)
    · refine ⟨C, hC, ?_⟩
      intro s t hs ht
      have hg : 0 ≤ airyRankGauge I i s / airyRankGauge I j t := by
        exact div_nonneg (airyRankGauge_pos I i s).le (airyRankGauge_pos I j t).le
      simpa only [airyRankCutKer, Prod.fst, Prod.snd, ite_eq_left (And.intro hs ht),
        airyExtendedKer, ite_eq_right hij, sub_zero, abs_mul, abs_of_nonneg hg,
        abs_of_pos (Real.exp_pos _)] using hPole s t hs ht
  choose C hC hbound using hblock
  refine ⟨∑ p : I × I, C p.1 p.2, Finset.sum_nonneg (fun p _ => hC p.1 p.2), ?_⟩
  intro p q hp hq
  have hle : C p.1 q.1 ≤ ∑ r : I × I, C r.1 r.2 :=
    Finset.single_le_sum (f := fun r : I × I => C r.1 r.2)
      (fun r _ => hC r.1 r.2) (Finset.mem_univ (p.1, q.1))
  exact (hbound p.1 q.1 p.2 q.2 hp hq).trans
    (mul_le_mul_of_nonneg_right hle (by positivity))

/-- Counting measure on a finite set times Lebesgue measure is sigma-finite. -/
instance (I : Finset ℝ) : SigmaFinite (airySiteMeasure I) := by
  unfold airySiteMeasure
  infer_instance

/-- Square-integrable functions on the disjoint copies of the spatial axis. -/
noncomputable abbrev TaggedLp (I : Finset ℝ) := Lp ℝ 2 (airySiteMeasure I)

/-- Square-integrable functions on a single spatial axis. -/
noncomputable abbrev RealLp := Lp ℝ 2 (volume : Measure ℝ)

/-- The dyadic cells of width `2⁻ᵏ` on each active half-line, up to distance `2ᵏ`
from its cut. The first coordinate records the observation time. -/
abbrev AiryCutCell (I : Finset ℝ) (k : ℕ) := I × Fin (2 ^ (2 * k))

/-- The spatial interval for a cell is open at the left endpoint and closed at the right. -/
noncomputable def airyCutCellSet (I : Finset ℝ) (x : I → ℝ) (k : ℕ) (c : AiryCutCell I k) :
    Set (I × ℝ) :=
  {c.1} ×ˢ Set.Ioc (x c.1 + (c.2.val : ℝ) / 2 ^ k)
    (x c.1 + (c.2.val + 1 : ℝ) / 2 ^ k)

/-- Every dyadic cell is measurable in the tagged space. -/
theorem measurableSet_airyCutCellSet (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (c : AiryCutCell I k) : MeasurableSet (airyCutCellSet I x k c) :=
  (measurableSet_singleton _).prod measurableSet_Ioc

/-- The measure of a cell is its positive dyadic width. -/
theorem airySiteMeasure_airyCutCellSet (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (c : AiryCutCell I k) :
    airySiteMeasure I (airyCutCellSet I x k c) = ENNReal.ofReal ((2 : ℝ) ^ k)⁻¹ := by
  rw [airySiteMeasure, airyCutCellSet, Measure.prod_prod, Measure.count_singleton, one_mul,
    Real.volume_Ioc]
  congr 1
  have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp
  ring

/-- The normalized indicator of a dyadic cell in the tagged Hilbert space. -/
noncomputable def airyCutCellVector (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (c : AiryCutCell I k) : TaggedLp I :=
  indicatorConstLp 2 (measurableSet_airyCutCellSet I x k c)
    (by rw [airySiteMeasure_airyCutCellSet]; exact ENNReal.ofReal_ne_top)
    (Real.sqrt ((2 : ℝ) ^ k))

/-- Distinct cells at a fixed scale are disjoint, including at shared endpoints. -/
theorem disjoint_airyCutCellSet (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    {c d : AiryCutCell I k} (hcd : c ≠ d) :
    Disjoint (airyCutCellSet I x k c) (airyCutCellSet I x k d) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  have hc : p.1 = c.1 := hp.1
  have hd : p.1 = d.1 := hq.1
  have htag : c.1 = d.1 := hc.symm.trans hd
  have hindex : c.2.val ≠ d.2.val := by
    intro heq
    exact hcd (Prod.ext htag (Fin.ext heq))
  have hp' : p.2 ∈ Set.Ioc (x c.1 + (c.2.val : ℝ) / 2 ^ k)
      (x c.1 + (c.2.val + 1 : ℝ) / 2 ^ k) := hp.2
  have hq' : p.2 ∈ Set.Ioc (x d.1 + (d.2.val : ℝ) / 2 ^ k)
      (x d.1 + (d.2.val + 1 : ℝ) / 2 ^ k) := hq.2
  rw [← htag] at hq'
  have hdpos : (0 : ℝ) < 2 ^ k := by positivity
  rcases lt_or_gt_of_ne hindex with h | h
  · have hend : (c.2.val + 1 : ℝ) ≤ (d.2.val : ℝ) := by exact_mod_cast h
    exact (not_lt_of_ge (hp'.2.trans (add_le_add_right
      (div_le_div_of_nonneg_right hend hdpos.le) _))) hq'.1
  · have hend : (d.2.val + 1 : ℝ) ≤ (c.2.val : ℝ) := by exact_mod_cast h
    exact (not_lt_of_ge (hq'.2.trans (add_le_add_right
      (div_le_div_of_nonneg_right hend hdpos.le) _))) hp'.1

/-- The normalized cell indicators are an orthonormal family. -/
theorem orthonormal_airyCutCellVector (I : Finset ℝ) (x : I → ℝ) (k : ℕ) :
    Orthonormal ℝ (airyCutCellVector I x k) := by
  classical
  rw [orthonormal_iff_ite]
  intro c d
  simp only [airyCutCellVector, L2.inner_indicatorConstLp_indicatorConstLp, Real.inner_apply,
    smul_eq_mul]
  by_cases h : c = d
  · subst d
    rw [ite_eq_left rfl, Set.inter_self, measureReal_def, airySiteMeasure_airyCutCellSet,
      ENNReal.toReal_ofReal (by positivity), ← sq, Real.sq_sqrt (by positivity)]
    exact inv_mul_cancel₀ (by positivity)
  · rw [ite_eq_right h, Set.disjoint_iff_inter_eq_empty.mp (disjoint_airyCutCellSet I x k h)]
    simp

/-- The finite-rank orthogonal projection onto the span of the normalized cell indicators. -/
noncomputable def cellProjection (I : Finset ℝ) (x : I → ℝ) (k : ℕ) :
    TaggedLp I →L[ℝ] TaggedLp I := by
  let V := Submodule.span ℝ (Set.range (airyCutCellVector I x k))
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  exact V.subtypeL ∘L V.orthogonalProjectionOnto

/-- The active sites of the tagged upper-half-line space. -/
def airyCutSites (I : Finset ℝ) (x : I → ℝ) : Set (I × ℝ) :=
  {p | x p.1 < p.2}

/-- The active site set is measurable, since the threshold is measurable on the finite tag set. -/
theorem measurableSet_airyCutSites (I : Finset ℝ) (x : I → ℝ) :
    MeasurableSet (airyCutSites I x) :=
  measurableSet_lt ((measurable_of_finite x).comp measurable_fst) measurable_snd

/-- Multiplication by the indicator of the active sites on the tagged Hilbert space. -/
noncomputable def cutSpaceProjection (I : Finset ℝ) (x : I → ℝ) :
    TaggedLp I →L[ℝ] TaggedLp I := by
  let S := airyCutSites I x
  let hs := measurableSet_airyCutSites I x
  let cut (f : TaggedLp I) := (Lp.memLp f).indicator hs.nullMeasurableSet
  let P (f : TaggedLp I) := (cut f).toLp (S.indicator f)
  have hP (f : TaggedLp I) : ⇑(P f) =ᵐ[airySiteMeasure I] S.indicator f :=
    (cut f).coeFn_toLp
  refine LinearMap.mkContinuous
    { toFun := P
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · intro f g
    apply Lp.ext
    filter_upwards [hP (f + g), hP f, hP g, Lp.coeFn_add f g, Lp.coeFn_add (P f) (P g)]
      with p hfg hf hg hadd hadd'
    rw [hfg, hadd', Pi.add_apply, hf, hg]
    by_cases hp : p ∈ S
    · simpa only [Set.indicator_of_mem hp, Pi.add_apply] using hadd
    · simp only [Set.indicator_of_notMem hp, add_zero]
  · intro c f
    change P (c • f) = c • P f
    apply Lp.ext
    filter_upwards [hP (c • f), hP f, Lp.coeFn_smul c f, Lp.coeFn_smul c (P f)]
      with p hcf hf hsmul hsmul'
    rw [hcf, hsmul', Pi.smul_apply, hf]
    by_cases hp : p ∈ S
    · simpa only [Set.indicator_of_mem hp, Pi.smul_apply] using hsmul
    · simp only [Set.indicator_of_notMem hp, smul_zero]
  · intro f
    rw [one_mul]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hP f] with p hp
    change ‖P f p‖ ≤ ‖f p‖
    rw [hp]
    by_cases hp' : p ∈ S
    · rw [Set.indicator_of_mem hp']
    · rw [Set.indicator_of_notMem hp', norm_zero]
      exact norm_nonneg _

/-- Every point in the truncated active region belongs to a cell at that scale. -/
theorem exists_mem_airyCutCellSet (I : Finset ℝ) (x : I → ℝ) (k : ℕ) (p : I × ℝ)
    (hp : x p.1 < p.2) (hpk : p.2 ≤ x p.1 + 2 ^ k) :
    ∃ c, p ∈ airyCutCellSet I x k c := by
  let y : ℝ := (p.2 - x p.1) * 2 ^ k
  have hd : (0 : ℝ) < 2 ^ k := by positivity
  have hy : 0 < y := mul_pos (sub_pos.mpr hp) hd
  have hym : y ≤ ((2 ^ (2 * k) : ℕ) : ℝ) := by
    push_cast
    rw [Nat.mul_comm 2 k, pow_mul, sq]
    exact mul_le_mul_of_nonneg_right (sub_le_iff_le_add.mpr (by linarith)) hd.le
  have hceil : ⌈y⌉₊ ≠ 0 := fun h => (not_le_of_gt hy) (Nat.ceil_eq_zero.mp h)
  have hceil_le : ⌈y⌉₊ ≤ 2 ^ (2 * k) := Nat.ceil_le.mpr hym
  have hi : ⌈y⌉₊ - 1 < 2 ^ (2 * k) := by omega
  obtain ⟨hl, hr⟩ := (Nat.ceil_eq_iff hceil).mp rfl
  have hsucc : (⌈y⌉₊ - 1) + 1 = ⌈y⌉₊ := by omega
  refine ⟨(p.1, ⟨⌈y⌉₊ - 1, hi⟩), rfl, ?_⟩
  change x p.1 + ((⌈y⌉₊ - 1 : ℕ) : ℝ) / 2 ^ k < p.2 ∧
    p.2 ≤ x p.1 + (((⌈y⌉₊ - 1 : ℕ) : ℝ) + 1) / 2 ^ k
  constructor
  · have h := (div_lt_iff₀ hd).mpr hl
    dsimp [y] at h
    linarith
  · have h := (le_div_iff₀ hd).mpr hr
    rw [← hsucc] at h
    push_cast at h
    linarith

/-- Each active tagged point is eventually covered by the expanding dyadic grids. -/
theorem eventually_exists_mem_airyCutCellSet (I : Finset ℝ) (x : I → ℝ) (p : I × ℝ)
    (hp : p ∈ airyCutSites I x) :
    ∀ᶠ k : ℕ in atTop, ∃ c, p ∈ airyCutCellSet I x k c := by
  have ht : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [ht.eventually_ge_atTop (p.2 - x p.1)] with k hk
  exact exists_mem_airyCutCellSet I x k p hp (by linarith)

/-- A point in a dyadic cell has the cell's tag and lies strictly above its threshold. -/
theorem airyCutCellSet_subset (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (c : AiryCutCell I k) : airyCutCellSet I x k c ⊆ airyCutSites I x := by
  intro p hp
  have htag : p.1 = c.1 := hp.1
  have hl : x c.1 + (c.2.val : ℝ) / 2 ^ k < p.2 := hp.2.1
  change x p.1 < p.2
  rw [htag]
  exact lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hl

/-- Two points in the same cell have spatial distance at most the cell width. -/
theorem abs_sub_le_airyCutCell_width (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (c : AiryCutCell I k) {p q : I × ℝ} (hp : p ∈ airyCutCellSet I x k c)
    (hq : q ∈ airyCutCellSet I x k c) :
    |p.2 - q.2| ≤ ((2 : ℝ) ^ k)⁻¹ := by
  have hlp : x c.1 + (c.2.val : ℝ) / 2 ^ k < p.2 := hp.2.1
  have huq : q.2 ≤ x c.1 + (c.2.val + 1 : ℝ) / 2 ^ k := hq.2.2
  have hlq : x c.1 + (c.2.val : ℝ) / 2 ^ k < q.2 := hq.2.1
  have hup : p.2 ≤ x c.1 + (c.2.val + 1 : ℝ) / 2 ^ k := hp.2.2
  rw [add_div, one_div] at huq hup
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The dyadic widths tend to zero. -/
theorem tendsto_airyCutCell_width :
    Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) := by
  simp only [← inv_pow]
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)

/-- The average value of a kernel over a pair of cells of the same scale. -/
noncomputable def airyCutCellAverage (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) (c d : AiryCutCell I k) : ℝ :=
  (∫ z in airyCutCellSet I x k c ×ˢ airyCutCellSet I x k d,
    K z.1 z.2 ∂((airySiteMeasure I).prod (airySiteMeasure I))) /
      (((2 : ℝ) ^ k)⁻¹) ^ 2

/-- The step kernel of cell averages, extended by zero outside the finite grid. -/
noncomputable def airyCutAveragedKernel (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) (p q : I × ℝ) : ℝ :=
  ∑ cd : AiryCutCell I k × AiryCutCell I k,
    (airyCutCellSet I x k cd.1 ×ˢ airyCutCellSet I x k cd.2).indicator
      (fun _ => airyCutCellAverage I x k K cd.1 cd.2) (p, q)

/-- Cell averages define a measurable step kernel. -/
theorem measurable_airyCutAveragedKernel (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) :
    Measurable (fun z : (I × ℝ) × (I × ℝ) => airyCutAveragedKernel I x k K z.1 z.2) := by
  unfold airyCutAveragedKernel
  apply Finset.measurable_sum _
  intro cd _
  exact measurable_const.indicator
    ((measurableSet_airyCutCellSet I x k cd.1).prod (measurableSet_airyCutCellSet I x k cd.2))

/-- On a cell rectangle the step kernel equals the average over that rectangle. -/
theorem airyCutAveragedKernel_of_mem (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) {p q : I × ℝ} {c d : AiryCutCell I k}
    (hp : p ∈ airyCutCellSet I x k c) (hq : q ∈ airyCutCellSet I x k d) :
    airyCutAveragedKernel I x k K p q = airyCutCellAverage I x k K c d := by
  classical
  unfold airyCutAveragedKernel
  rw [Finset.sum_eq_single (c, d)]
  · have hmem : (p, q) ∈ airyCutCellSet I x k c ×ˢ airyCutCellSet I x k d := ⟨hp, hq⟩
    exact Set.indicator_of_mem hmem _
  · intro ef _ hef
    apply Set.indicator_of_notMem
    intro he
    have hc : ef.1 = c := by
      by_contra h
      exact Set.disjoint_left.mp (disjoint_airyCutCellSet I x k h) he.1 hp
    have hd : ef.2 = d := by
      by_contra h
      exact Set.disjoint_left.mp (disjoint_airyCutCellSet I x k h) he.2 hq
    exact hef (Prod.ext hc hd)
  · simp

/-- The step kernel vanishes if it has no containing cell rectangle. -/
theorem airyCutAveragedKernel_of_not_exists (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) {p q : I × ℝ}
    (h : ¬ ∃ c d, p ∈ airyCutCellSet I x k c ∧ q ∈ airyCutCellSet I x k d) :
    airyCutAveragedKernel I x k K p q = 0 := by
  unfold airyCutAveragedKernel
  apply Finset.sum_eq_zero
  intro cd _
  exact Set.indicator_of_notMem (fun hm => h ⟨cd.1, cd.2, hm⟩) _

/-- The product measure of a cell rectangle is the square of the dyadic width. -/
theorem airySiteMeasure_airyCutCellSet_prod (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (c d : AiryCutCell I k) :
    (airySiteMeasure I).prod (airySiteMeasure I)
      (airyCutCellSet I x k c ×ˢ airyCutCellSet I x k d) =
        ENNReal.ofReal ((((2 : ℝ) ^ k)⁻¹) ^ 2) := by
  rw [Measure.prod_prod, airySiteMeasure_airyCutCellSet, airySiteMeasure_airyCutCellSet,
    sq, ENNReal.ofReal_mul (by positivity)]

/-- A bound on the norm on a cell rectangle also bounds the norm of its average. -/
theorem norm_airyCutCellAverage_le (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) (c d : AiryCutCell I k) {B : ℝ}
    (hB : ∀ p ∈ airyCutCellSet I x k c, ∀ q ∈ airyCutCellSet I x k d,
      ‖K p q‖ ≤ B) :
    ‖airyCutCellAverage I x k K c d‖ ≤ B := by
  have hw : 0 < (((2 : ℝ) ^ k)⁻¹) ^ 2 := by positivity
  have hfinite : (airySiteMeasure I).prod (airySiteMeasure I)
      (airyCutCellSet I x k c ×ˢ airyCutCellSet I x k d) < ⊤ := by
    rw [airySiteMeasure_airyCutCellSet_prod]
    exact ENNReal.ofReal_lt_top
  unfold airyCutCellAverage
  rw [norm_div, Real.norm_of_nonneg hw.le, div_le_iff₀ hw]
  simpa only [measureReal_def, airySiteMeasure_airyCutCellSet_prod,
    ENNReal.toReal_ofReal hw.le] using
      (norm_setIntegral_le_of_norm_le_const (f := fun z => K z.1 z.2) hfinite
        (fun z hz => hB z.1 hz.1 z.2 hz.2))

/-- The average preserves a uniform bound on the difference from a constant. -/
theorem norm_airyCutCellAverage_sub_le (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) (c d : AiryCutCell I k) (v : ℝ) {B : ℝ}
    (hm : MemLp (fun z : (I × ℝ) × (I × ℝ) => K z.1 z.2)
      2 ((airySiteMeasure I).prod (airySiteMeasure I)))
    (hB : ∀ p ∈ airyCutCellSet I x k c, ∀ q ∈ airyCutCellSet I x k d,
      ‖K p q - v‖ ≤ B) :
    ‖airyCutCellAverage I x k K c d - v‖ ≤ B := by
  let μ := (airySiteMeasure I).prod (airySiteMeasure I)
  let S := airyCutCellSet I x k c ×ˢ airyCutCellSet I x k d
  let w : ℝ := (((2 : ℝ) ^ k)⁻¹) ^ 2
  have hw : 0 < w := by dsimp [w]; positivity
  have hμS : μ S = ENNReal.ofReal w := airySiteMeasure_airyCutCellSet_prod I x k c d
  have hfinite : μ S < ⊤ := by rw [hμS]; exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hfinite⟩
  have hK : Integrable (fun z => K z.1 z.2) (μ.restrict S) :=
    (hm.mono_measure Measure.restrict_le_self).integrable (by norm_num)
  have hconst : ∫ _z in S, v ∂μ = w * v := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def, hμS, ENNReal.toReal_ofReal hw.le]
  have hdiff : airyCutCellAverage I x k (fun p q => K p q - v) c d =
      airyCutCellAverage I x k K c d - v := by
    change (∫ z in S, K z.1 z.2 - v ∂μ) / w = (∫ z in S, K z.1 z.2 ∂μ) / w - v
    rw [integral_sub hK (integrable_const _), hconst]
    field_simp
  rw [← hdiff]
  exact norm_airyCutCellAverage_le I x k _ c d hB

/-- Cell averages converge pointwise, including the diagonal of each active block. -/
theorem tendsto_airyCutAveragedKernel (I : Finset ℝ) (x : I → ℝ)
    (K : (I × ℝ) → (I × ℝ) → ℝ)
    (hm : MemLp (fun z : (I × ℝ) × (I × ℝ) => K z.1 z.2)
      2 ((airySiteMeasure I).prod (airySiteMeasure I)))
    (hs : cutKernelSupported I x K) (hc : cutKernelContinuous I x K) (p q : I × ℝ) :
    Tendsto (fun k => airyCutAveragedKernel I x k K p q) atTop (𝓝 (K p q)) := by
  by_cases hp : p ∈ airyCutSites I x
  · by_cases hq : q ∈ airyCutSites I x
    · obtain ⟨F, hF, hval⟩ := hc p.1 q.1
      have hp' : x p.1 < p.2 := hp
      have hq' : x q.1 < q.2 := hq
      have hmem : (p.2, q.2) ∈ Set.Ici (x p.1) ×ˢ Set.Ici (x q.1) := ⟨hp'.le, hq'.le⟩
      have hv := hval p.2 q.2 hp' hq'
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hF _ hmem) (ε / 2) (by positivity)
      have hsmall : ∀ᶠ k : ℕ in atTop, ((2 : ℝ) ^ k)⁻¹ < δ :=
        tendsto_airyCutCell_width.eventually (gt_mem_nhds hδ)
      filter_upwards [hsmall, eventually_exists_mem_airyCutCellSet I x p hp,
        eventually_exists_mem_airyCutCellSet I x q hq] with k hk hpk hqk
      obtain ⟨c, hpc⟩ := hpk
      obtain ⟨d, hqd⟩ := hqk
      rw [airyCutAveragedKernel_of_mem I x k K hpc hqd, dist_eq_norm]
      refine lt_of_le_of_lt (norm_airyCutCellAverage_sub_le I x k K c d (K p q) (B := ε / 2) hm ?_) (by linarith)
      intro r hrc s hsd
      have htag₁ : r.1 = p.1 := (show r.1 = c.1 from hrc.1).trans (show p.1 = c.1 from hpc.1).symm
      have htag₂ : s.1 = q.1 := (show s.1 = d.1 from hsd.1).trans (show q.1 = d.1 from hqd.1).symm
      have hr : x r.1 < r.2 := airyCutCellSet_subset I x k c hrc
      have ht : x s.1 < s.2 := airyCutCellSet_subset I x k d hsd
      rw [htag₁] at hr
      rw [htag₂] at ht
      have hrK : F (r.2, s.2) = K r s := by
        convert hval r.2 s.2 hr ht using 1
        exact congrArg₂ K (Prod.ext htag₁ rfl) (Prod.ext htag₂ rfl)
      have hd : dist (r.2, s.2) (p.2, q.2) < δ := by
        rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
        exact ⟨(abs_sub_le_airyCutCell_width I x k c hrc hpc).trans_lt hk,
          (abs_sub_le_airyCutCell_width I x k d hsd hqd).trans_lt hk⟩
      have h := hclose (show (r.2, s.2) ∈ _ from ⟨hr.le, ht.le⟩) hd
      rw [hrK, hv, dist_eq_norm] at h
      exact h.le
    · have hq' : q.2 ≤ x q.1 := le_of_not_gt hq
      rw [hs p q (Or.inr hq')]
      have hz (k : ℕ) : airyCutAveragedKernel I x k K p q = 0 :=
        airyCutAveragedKernel_of_not_exists I x k K fun ⟨_, d, _, hqd⟩ =>
          hq (airyCutCellSet_subset I x k d hqd)
      simpa only [hz] using tendsto_const_nhds
  · have hp' : p.2 ≤ x p.1 := le_of_not_gt hp
    rw [hs p q (Or.inl hp')]
    have hz (k : ℕ) : airyCutAveragedKernel I x k K p q = 0 :=
      airyCutAveragedKernel_of_not_exists I x k K fun ⟨c, _, hpc, _⟩ =>
        hp (airyCutCellSet_subset I x k c hpc)
    simpa only [hz] using tendsto_const_nhds

/-- Averaging within cells of width at most one preserves the row envelope up to a
constant factor independent of the scale. -/
theorem airyCutAveragedKernel_row_bound (I : Finset ℝ) (x : I → ℝ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) (hb : cutKernelRowEnvelope I x K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k p q,
      ‖airyCutAveragedKernel I x k K p q‖ ≤ C * (1 + p.2 ^ 2)⁻¹ := by
  obtain ⟨C, hC, hbound⟩ := hb
  refine ⟨4 * C, by positivity, ?_⟩
  intro k p q
  by_cases h : ∃ c d, p ∈ airyCutCellSet I x k c ∧ q ∈ airyCutCellSet I x k d
  · obtain ⟨c, d, hpc, hqd⟩ := h
    rw [airyCutAveragedKernel_of_mem I x k K hpc hqd]
    apply norm_airyCutCellAverage_le
    intro r hrc t htd
    have hr : x r.1 < r.2 := airyCutCellSet_subset I x k c hrc
    have ht : x t.1 < t.2 := airyCutCellSet_subset I x k d htd
    have hwidth : ((2 : ℝ) ^ k)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hdist := (abs_sub_le_airyCutCell_width I x k c hpc hrc).trans hwidth
    have hsq : (p.2 - r.2) ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) hdist 2
      simpa only [sq_abs, one_pow] using h
    have hcompare : 1 + p.2 ^ 2 ≤ 4 * (1 + r.2 ^ 2) := by
      nlinarith [sq_nonneg (p.2 - 2 * r.2)]
    calc
      ‖K r t‖ ≤ C * (1 + r.2 ^ 2)⁻¹ := by
        rw [Real.norm_eq_abs]
        exact hbound r t hr ht
      _ ≤ 4 * C * (1 + p.2 ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, ← div_eq_mul_inv]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        calc
          _ ≤ C * (4 * (1 + r.2 ^ 2)) := mul_le_mul_of_nonneg_left hcompare hC
          _ = _ := by ring
  · rw [airyCutAveragedKernel_of_not_exists I x k K h, norm_zero]
    positivity

/-- The row weight is integrable over the tagged space. -/
theorem integrable_airySite_row_weight (I : Finset ℝ) :
    Integrable (fun p : I × ℝ => (1 + p.2 ^ 2)⁻¹) (airySiteMeasure I) := by
  unfold airySiteMeasure
  have h : Integrable (fun _ : I => (1 : ℝ)) Measure.count := integrable_const _
  simpa only [one_mul] using h.mul_prod integrable_inv_one_add_sq

/-- The Fredholm series of the cell averages tends to the literal Fredholm series
of the regular kernel over all degrees. -/
theorem tendsto_airyCutAveragedKernel_series (I : Finset ℝ) (x : I → ℝ)
    (K : (I × ℝ) → (I × ℝ) → ℝ)
    (hm : MemLp (fun z : (I × ℝ) × (I × ℝ) => K z.1 z.2)
      2 ((airySiteMeasure I).prod (airySiteMeasure I)))
    (hs : cutKernelSupported I x K) (hc : cutKernelContinuous I x K)
    (hb : cutKernelRowEnvelope I x K) :
    Tendsto (fun k => kernelFredholmSeries (airySiteMeasure I)
      (airyCutAveragedKernel I x k K)) atTop
      (𝓝 (kernelFredholmSeries (airySiteMeasure I) K)) := by
  obtain ⟨C, hC, hbound⟩ := airyCutAveragedKernel_row_bound I x K hb
  refine tendsto_kernelFredholmSeries_of_row_bound
    (fun k => measurable_airyCutAveragedKernel I x k K)
    ((integrable_airySite_row_weight I).const_mul C) (fun _ => by positivity) hbound ?_
  intro n
  exact ae_of_all _ fun p i j => tendsto_airyCutAveragedKernel I x K hm hs hc (p i) (p j)

/-- The matrix of cell averages with the cell width included for normalization. -/
noncomputable def airyCutCellMatrix (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) :
    Matrix (AiryCutCell I k) (AiryCutCell I k) ℝ :=
  Matrix.of fun c d => ((2 : ℝ) ^ k)⁻¹ * airyCutCellAverage I x k K c d

/-- At each degree the Fredholm coefficient of the step kernel is exactly the
sum of the corresponding principal minors of the normalized cell matrix. -/
theorem kernelFredholmCoeff_airyCutAveragedKernel (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) (n : ℕ) :
    kernelFredholmCoeff (airySiteMeasure I) (airyCutAveragedKernel I x k K) n =
      ∑ s ∈ (Finset.univ : Finset (AiryCutCell I k)).powersetCard n,
        ((airyCutCellMatrix I x k K).submatrix (Subtype.val : s → _) (Subtype.val : s → _)).det := by
  classical
  let μ := Measure.pi (fun _ : Fin n => airySiteMeasure I)
  let w := ((2 : ℝ) ^ k)⁻¹
  let C := AiryCutCell I k
  let raw : Matrix C C ℝ := Matrix.of (airyCutCellAverage I x k K)
  let S (f : Fin n → C) : Set (Fin n → I × ℝ) :=
    Set.univ.pi fun i => airyCutCellSet I x k (f i)
  let F (p : Fin n → I × ℝ) :=
    (Matrix.of fun i j => airyCutAveragedKernel I x k K (p i) (p j)).det
  have hS (f : Fin n → C) : MeasurableSet (S f) :=
    MeasurableSet.pi Set.countable_univ fun i _ => measurableSet_airyCutCellSet I x k (f i)
  have hμS (f : Fin n → C) : μ (S f) = ENNReal.ofReal (w ^ n) := by
    dsimp [μ, S]
    rw [Measure.pi_pi]
    simp only [airySiteMeasure_airyCutCellSet, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.ofReal_pow (by dsimp [w]; positivity)]
  have hsplit : F = fun p => ∑ f : Fin n → C,
      (S f).indicator (fun _ => (raw.submatrix f f).det) p := by
    funext p
    by_cases hp : ∀ i, ∃ c : C, p i ∈ airyCutCellSet I x k c
    · choose f hf using hp
      have hf' : p ∈ S f := fun i _ => hf i
      rw [Finset.sum_eq_single f]
      · rw [Set.indicator_of_mem hf']
        unfold F
        apply congrArg Matrix.det
        ext i j
        exact airyCutAveragedKernel_of_mem I x k K (hf i) (hf j)
      · intro g _ hgf
        apply Set.indicator_of_notMem
        intro hgp
        apply hgf
        funext i
        by_contra hi
        exact Set.disjoint_left.mp (disjoint_airyCutCellSet I x k hi)
          (hgp i (Set.mem_univ i)) (hf i)
      · simp
    · push Not at hp
      obtain ⟨i, hi⟩ := hp
      have hz : F p = 0 := by
        apply Matrix.det_eq_zero_of_row_eq_zero i
        intro j
        exact airyCutAveragedKernel_of_not_exists I x k K
          (fun ⟨c, _, hc, _⟩ => hi c hc)
      rw [hz]
      symm
      apply Finset.sum_eq_zero
      intro f _
      apply Set.indicator_of_notMem
      exact fun hf => hi (f i) (hf i (Set.mem_univ i))
  have hint (f : Fin n → C) :
      Integrable ((S f).indicator fun _ => (raw.submatrix f f).det) μ := by
    rw [integrable_indicator_iff (hS f)]
    exact integrableOn_const (by rw [hμS]; exact ENNReal.ofReal_ne_top)
  have hval (f : Fin n → C) :
      (∫ p, (S f).indicator (fun _ => (raw.submatrix f f).det) p ∂μ) =
        ((airyCutCellMatrix I x k K).submatrix f f).det := by
    rw [integral_indicator (hS f), setIntegral_const, smul_eq_mul, measureReal_def, hμS,
      ENNReal.toReal_ofReal (by dsimp [w]; positivity)]
    have hmatrix :
        (airyCutCellMatrix I x k K).submatrix f f = w • raw.submatrix f f := by
      ext i j
      rfl
    rw [hmatrix, Matrix.det_smul, Fintype.card_fin]
  change (1 / (n.factorial : ℝ)) * (∫ p, F p ∂μ) = _
  rw [hsplit, integral_finsetSum _ (fun f _ => hint f)]
  simp_rw [hval]
  rw [sum_det_over_tuples_eq_sum_principal_minors]
  field_simp
  rfl

/-- The full Fredholm series of the finite step kernel is the finite cell determinant. -/
theorem kernelFredholmSeries_airyCutAveragedKernel (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) :
    kernelFredholmSeries (airySiteMeasure I) (airyCutAveragedKernel I x k K) =
      (1 - airyCutCellMatrix I x k K).det := by
  classical
  let cells : Finset (AiryCutCell I k) := Finset.univ
  let M := airyCutCellMatrix I x k K
  let minor (s : Finset (AiryCutCell I k)) : ℝ :=
    (M.submatrix (Subtype.val : s → _) (Subtype.val : s → _)).det
  let degrees := Finset.range (cells.card + 1)
  have hmaps : ∀ s ∈ cells.powerset, s.card ∈ degrees := by
    intro s hs
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Finset.card_le_card (Finset.mem_powerset.mp hs)))
  unfold kernelFredholmSeries
  rw [tsum_eq_sum (s := degrees)]
  · simp_rw [kernelFredholmCoeff_airyCutAveragedKernel]
    change (∑ n ∈ degrees, (-1 : ℝ) ^ n * ∑ s ∈ cells.powersetCard n, minor s) = _
    rw [show 1 - M = 1 + (-1 : ℝ) • M by simp [sub_eq_add_neg]]
    rw [HilbertSchmidt.Hadamard.det_one_add_smul_eq_sum_minors]
    change _ = ∑ s ∈ cells.powerset, minor s * (-1 : ℝ) ^ s.card
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum, Finset.powersetCard_eq_filter]
    apply Finset.sum_congr rfl
    intro s hs
    rw [(Finset.mem_filter.mp hs).2, mul_comm]
  · intro n hn
    rw [kernelFredholmCoeff_airyCutAveragedKernel]
    have hzero : cells.powersetCard n = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs
      exact hn (Finset.mem_range.mpr (Nat.lt_succ_of_le
        ((Finset.mem_powersetCard.mp hs).2 ▸
          Finset.card_le_card (Finset.mem_powersetCard.mp hs).1)))
    change (-1 : ℝ) ^ n * (∑ s ∈ cells.powersetCard n, minor s) = 0
    rw [hzero, Finset.sum_empty, mul_zero]

/-- The cell indicators are an orthonormal basis of their finite-dimensional span. -/
noncomputable def airyCutCellBasis (I : Finset ℝ) (x : I → ℝ) (k : ℕ) :
    OrthonormalBasis (AiryCutCell I k) ℝ
      (Submodule.span ℝ (Set.range (airyCutCellVector I x k))) := by
  let h := orthonormal_airyCutCellVector I x k
  exact (Module.Basis.span h.linearIndependent).toOrthonormalBasis (by
    convert orthonormal_span h using 1
    funext c
    apply Subtype.ext
    exact congrArg Subtype.val (Module.Basis.span_apply h.linearIndependent c))

/-- The vectors of the cell basis are the normalized indicators in the ambient space. -/
theorem coe_airyCutCellBasis (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (c : AiryCutCell I k) :
    (airyCutCellBasis I x k c : TaggedLp I) = airyCutCellVector I x k c := by
  unfold airyCutCellBasis
  simp only [Module.Basis.coe_toOrthonormalBasis]
  exact congrArg Subtype.val
    (Module.Basis.span_apply (orthonormal_airyCutCellVector I x k).linearIndependent c)

/-- Projection onto the cell space acts by the finite orthonormal expansion. -/
theorem cellProjection_apply (I : Finset ℝ) (x : I → ℝ) (k : ℕ) (f : TaggedLp I) :
    cellProjection I x k f =
      ∑ c, inner ℝ (airyCutCellVector I x k c) f • airyCutCellVector I x k c := by
  let : FiniteDimensional ℝ (Submodule.span ℝ (Set.range (airyCutCellVector I x k))) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  unfold cellProjection
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [(airyCutCellBasis I x k).orthogonalProjectionOnto_apply_eq_sum]
  push_cast
  simp only [coe_airyCutCellBasis]

/-- The support projection acts almost everywhere by the cut indicator. -/
theorem cutSpaceProjection_apply_ae (I : Finset ℝ) (x : I → ℝ) (f : TaggedLp I) :
    ⇑(cutSpaceProjection I x f) =ᵐ[airySiteMeasure I] (airyCutSites I x).indicator f := by
  exact ((Lp.memLp f).indicator (measurableSet_airyCutSites I x).nullMeasurableSet).coeFn_toLp

/-- The normalized cell matrix consists of the matrix elements of the kernel operator. -/
theorem inner_kernelOperator_airyCutCellVector (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (K : (I × ℝ) → (I × ℝ) → ℝ)
    (hm : MemLp (fun z : (I × ℝ) × (I × ℝ) => K z.1 z.2)
      2 ((airySiteMeasure I).prod (airySiteMeasure I)))
    (c d : AiryCutCell I k) :
    inner ℝ (airyCutCellVector I x k c)
      (HilbertSchmidt.kernelOperator hm (airyCutCellVector I x k d)) =
        airyCutCellMatrix I x k K c d := by
  let μ := airySiteMeasure I
  let S := airyCutCellSet I x k c
  let T := airyCutCellSet I x k d
  let a := (2 : ℝ) ^ k
  let v := Real.sqrt a
  have hS : MeasurableSet S := measurableSet_airyCutCellSet I x k c
  have hT : MeasurableSet T := measurableSet_airyCutCellSet I x k d
  have hfinite : μ.prod μ (S ×ˢ T) < ⊤ := by
    rw [airySiteMeasure_airyCutCellSet_prod I x k c d]
    exact ENNReal.ofReal_lt_top
  let : IsFiniteMeasure ((μ.prod μ).restrict (S ×ˢ T)) := ⟨by simpa using hfinite⟩
  have hInt : Integrable (fun z => K z.1 z.2) ((μ.restrict S).prod (μ.restrict T)) := by
    rw [Measure.prod_restrict]
    exact (hm.mono_measure Measure.restrict_le_self).integrable (by norm_num)
  have hd : ⇑(airyCutCellVector I x k d) =ᵐ[μ] T.indicator (fun _ => v) := by
    unfold airyCutCellVector
    exact indicatorConstLp_coeFn
  have hEval : ∀ᵐ p ∂μ.restrict S,
      HilbertSchmidt.kernelOperator hm (airyCutCellVector I x k d) p =
        (∫ q in T, K p q ∂μ) * v := by
    apply ae_restrict_of_ae
    filter_upwards [HilbertSchmidt.kernelOperator_apply_ae hm (airyCutCellVector I x k d)]
      with p hp
    rw [hp]
    change (∫ q, K p q * airyCutCellVector I x k d q ∂μ) = _
    calc
      _ = ∫ q, T.indicator (fun r => K p r * v) q ∂μ := by
        apply integral_congr_ae
        filter_upwards [hd] with q hq
        rw [hq]
        by_cases h : q ∈ T <;> simp [Set.indicator, h]
      _ = _ := by rw [integral_indicator hT, integral_mul_const]
  have hI : (∫ p in S, ∫ q in T, K p q ∂μ ∂μ) =
      ∫ z in S ×ˢ T, K z.1 z.2 ∂(μ.prod μ) := by
    rw [← Measure.prod_restrict]
    exact (integral_prod _ hInt).symm
  change inner ℝ (airyCutCellVector I x k c)
    (HilbertSchmidt.kernelOperator hm (airyCutCellVector I x k d)) =
      a⁻¹ * ((∫ z in S ×ˢ T, K z.1 z.2 ∂(μ.prod μ)) / (a⁻¹) ^ 2)
  conv_lhs => arg 2; unfold airyCutCellVector
  rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]
  simp only [Real.inner_apply]
  have ha : 0 < a := by dsimp [a]; positivity
  calc
    _ = ∫ p in S, ((∫ q in T, K p q ∂μ) * v) * v ∂μ := by
      apply integral_congr_ae
      filter_upwards [hEval] with p hp
      rw [hp]
      change v * ((∫ q in T, K p q ∂μ) * v) = _
      ring
    _ = (∫ p in S, ∫ q in T, K p q ∂μ ∂μ) * (v * v) := by
      simp only [integral_mul_const, mul_assoc]
    _ = _ := by
      rw [hI, ← sq, Real.sq_sqrt ha.le]
      field_simp

/-- Projection fixes the cell indicators. -/
theorem cellProjection_airyCutCellVector (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (c : AiryCutCell I k) :
    cellProjection I x k (airyCutCellVector I x k c) = airyCutCellVector I x k c := by
  classical
  rw [cellProjection_apply]
  simp [(orthonormal_iff_ite.mp (orthonormal_airyCutCellVector I x k))]

/-- Pairing with a cell indicator is unchanged by the cell projection. -/
theorem inner_airyCutCellVector_cellProjection (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (c : AiryCutCell I k) (f : TaggedLp I) :
    inner ℝ (airyCutCellVector I x k c) (cellProjection I x k f) =
      inner ℝ (airyCutCellVector I x k c) f := by
  classical
  rw [cellProjection_apply, inner_sum]
  simp only [inner_smul_right, orthonormal_iff_ite.mp (orthonormal_airyCutCellVector I x k)]
  simp

/-- At each scale the Fredholm series of the averaged kernel is the determinant of the
finite-rank compression of the original operator. -/
theorem kernelFredholmSeries_airyCutAveragedKernel_eq_fredholmDet_cellCompression
    (I : Finset ℝ) (x : I → ℝ) (k : ℕ) (K : (I × ℝ) → (I × ℝ) → ℝ)
    (hm : MemLp (fun z : (I × ℝ) × (I × ℝ) => K z.1 z.2)
      2 ((airySiteMeasure I).prod (airySiteMeasure I)))
    (ht : HilbertSchmidt.IsTraceClass (HilbertSchmidt.kernelOperator hm)) :
    kernelFredholmSeries (airySiteMeasure I) (airyCutAveragedKernel I x k K) =
      HilbertSchmidt.fredholmDet
        (cellProjection I x k ∘L HilbertSchmidt.kernelOperator hm ∘L cellProjection I x k) 1 := by
  rw [kernelFredholmSeries_airyCutAveragedKernel]
  exact (fredholmDet_eq_det_of_orthonormalCompression
    (airyCutCellVector I x k) (orthonormal_airyCutCellVector I x k)
    (cellProjection I x k) (HilbertSchmidt.kernelOperator hm) ht
    (cellProjection_apply I x k) (cellProjection_airyCutCellVector I x k)
    (inner_airyCutCellVector_cellProjection I x k) (airyCutCellMatrix I x k K)
    (inner_kernelOperator_airyCutCellVector I x k K hm)).symm

/-- The finite cell projection is a contraction. -/
theorem norm_cellProjection_le (I : Finset ℝ) (x : I → ℝ) (k : ℕ) :
    ‖cellProjection I x k‖ ≤ 1 := by
  let V := Submodule.span ℝ (Set.range (airyCutCellVector I x k))
  let : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    change ‖V.starProjection f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using V.norm_starProjection_apply_le f

/-- The cell projection is self-adjoint. -/
theorem adjoint_cellProjection (I : Finset ℝ) (x : I → ℝ) (k : ℕ) :
    (cellProjection I x k).adjoint = cellProjection I x k := by
  let V := Submodule.span ℝ (Set.range (airyCutCellVector I x k))
  let : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  change V.starProjection.adjoint = V.starProjection
  exact ((ContinuousLinearMap.eq_adjoint_iff _ _).2 V.starProjection_isSymmetric).symm

/-- The support projection is a contraction. -/
theorem norm_cutSpaceProjection_le (I : Finset ℝ) (x : I → ℝ) :
    ‖cutSpaceProjection I x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cutSpaceProjection_apply_ae I x f] with p hp
  rw [hp]
  by_cases hs : p ∈ airyCutSites I x
  · rw [Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hs, norm_zero]
    exact norm_nonneg _

/-- Multiplication by the real cut indicator is self-adjoint. -/
theorem adjoint_cutSpaceProjection (I : Finset ℝ) (x : I → ℝ) :
    (cutSpaceProjection I x).adjoint = cutSpaceProjection I x := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cutSpaceProjection_apply_ae I x f, cutSpaceProjection_apply_ae I x g]
    with p hf hg
  rw [hf, hg]
  by_cases hp : p ∈ airyCutSites I x <;> simp [hp]

/-- A representative of the projected function, constant on each cell. -/
noncomputable def airyCutCellAveragedFn (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (f : (I × ℝ) → ℝ) (p : I × ℝ) : ℝ :=
  ∑ c : AiryCutCell I k, (airyCutCellSet I x k c).indicator
    (fun _ => (2 : ℝ) ^ k * ∫ r in airyCutCellSet I x k c, f r ∂(airySiteMeasure I)) p

/-- On its cells, the orthogonal projection agrees almost everywhere with averaging. -/
theorem cellProjection_apply_ae (I : Finset ℝ) (x : I → ℝ) (k : ℕ) (f : TaggedLp I) :
    ⇑(cellProjection I x k f) =ᵐ[airySiteMeasure I] airyCutCellAveragedFn I x k f := by
  rw [cellProjection_apply]
  let v := (2 : ℝ) ^ k
  let S := airyCutCellSet I x k
  have hvec (c : AiryCutCell I k) :
      ⇑(airyCutCellVector I x k c) =ᵐ[airySiteMeasure I] (S c).indicator (fun _ => Real.sqrt v) :=
    indicatorConstLp_coeFn
  have havg (c : AiryCutCell I k) :
      inner ℝ (airyCutCellVector I x k c) f = Real.sqrt v * ∫ r in S c, f r ∂(airySiteMeasure I) := by
    unfold airyCutCellVector
    rw [L2.inner_indicatorConstLp_eq_inner_setIntegral, Real.inner_apply]
  have hterms (c : AiryCutCell I k) :
      ⇑(inner ℝ (airyCutCellVector I x k c) f • airyCutCellVector I x k c) =ᵐ[airySiteMeasure I]
        (S c).indicator (fun _ => v * ∫ r in S c, f r ∂(airySiteMeasure I)) := by
    filter_upwards [Lp.coeFn_smul (inner ℝ (airyCutCellVector I x k c) f) (airyCutCellVector I x k c), hvec c]
      with p hp hv
    rw [hp, Pi.smul_apply, hv, havg]
    by_cases hp' : p ∈ S c
    · rw [Set.indicator_of_mem hp', Set.indicator_of_mem hp', smul_eq_mul]
      calc
        _ = (Real.sqrt v * Real.sqrt v) * ∫ r in S c, f r ∂(airySiteMeasure I) := by ring
        _ = _ := by rw [← sq, Real.sq_sqrt (by dsimp [v]; positivity)]
    · rw [Set.indicator_of_notMem hp', Set.indicator_of_notMem hp', smul_zero]
  refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
  filter_upwards [ae_all_iff.mpr hterms] with p hp
  exact Finset.sum_congr rfl fun c _ => hp c

/-- Outside the grid the averaged function vanishes, and within a cell it is its average. -/
theorem airyCutCellAveragedFn_of_mem (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (f : (I × ℝ) → ℝ) {p : I × ℝ} {c : AiryCutCell I k}
    (hp : p ∈ airyCutCellSet I x k c) :
    airyCutCellAveragedFn I x k f p =
      (2 : ℝ) ^ k * ∫ r in airyCutCellSet I x k c, f r ∂(airySiteMeasure I) := by
  classical
  unfold airyCutCellAveragedFn
  rw [Finset.sum_eq_single c]
  · exact Set.indicator_of_mem hp _
  · intro d _ hd
    exact Set.indicator_of_notMem
      (fun hm => Set.disjoint_left.mp (disjoint_airyCutCellSet I x k hd) hm hp) _
  · simp

/-- A point outside the finite grid is assigned zero. -/
theorem airyCutCellAveragedFn_of_not_exists (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (f : (I × ℝ) → ℝ) {p : I × ℝ}
    (hp : ¬ ∃ c, p ∈ airyCutCellSet I x k c) :
    airyCutCellAveragedFn I x k f p = 0 := by
  unfold airyCutCellAveragedFn
  exact Finset.sum_eq_zero fun c _ => Set.indicator_of_notMem (fun hm => hp ⟨c, hm⟩) _

/-- Scalar cell averages respect almost-everywhere equality of the original functions. -/
theorem airyCutCellAveragedFn_congr (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    {f g : (I × ℝ) → ℝ} (h : f =ᵐ[airySiteMeasure I] g) :
    airyCutCellAveragedFn I x k f = airyCutCellAveragedFn I x k g := by
  funext p
  unfold airyCutCellAveragedFn
  apply Finset.sum_congr rfl
  intro c _
  rw [integral_congr_ae (ae_restrict_of_ae h)]

/-- Cell averaging does not amplify a uniform bound on a cell. -/
theorem norm_airyCutCellAveragedFn_le (I : Finset ℝ) (x : I → ℝ) (k : ℕ)
    (f : (I × ℝ) → ℝ) {p : I × ℝ} {c : AiryCutCell I k}
    (hp : p ∈ airyCutCellSet I x k c) {B : ℝ}
    (hB : ∀ r ∈ airyCutCellSet I x k c, ‖f r‖ ≤ B) :
    ‖airyCutCellAveragedFn I x k f p‖ ≤ B := by
  let a := (2 : ℝ) ^ k
  have ha : 0 < a := by dsimp [a]; positivity
  have hfinite : airySiteMeasure I (airyCutCellSet I x k c) < ⊤ := by
    rw [airySiteMeasure_airyCutCellSet]
    exact ENNReal.ofReal_lt_top
  rw [airyCutCellAveragedFn_of_mem I x k f hp, norm_mul, Real.norm_of_nonneg ha.le]
  have hb := norm_setIntegral_le_of_norm_le_const hfinite hB
  rw [measureReal_def, airySiteMeasure_airyCutCellSet, ENNReal.toReal_ofReal
    (by positivity)] at hb
  exact (mul_le_mul_of_nonneg_left hb ha.le).trans_eq (by
    change a * (B * a⁻¹) = B
    rw [mul_left_comm, mul_inv_cancel₀ ha.ne', mul_one])

/-- Cell averages of a continuous function converge to its value on every active site. -/
theorem tendsto_airyCutCellAveragedFn (I : Finset ℝ) (x : I → ℝ)
    (f : (I × ℝ) → ℝ) (hf : Continuous f) (hm : MemLp f 2 (airySiteMeasure I)) (p : I × ℝ) :
    Tendsto (fun k => airyCutCellAveragedFn I x k f p) atTop
      (𝓝 ((airyCutSites I x).indicator f p)) := by
  by_cases hp : p ∈ airyCutSites I x
  · rw [Set.indicator_of_mem hp, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hf.continuousAt (ε / 2) (by positivity)
    have hsmall : ∀ᶠ k : ℕ in atTop, ((2 : ℝ) ^ k)⁻¹ < δ :=
      tendsto_airyCutCell_width.eventually (gt_mem_nhds hδ)
    filter_upwards [hsmall, eventually_exists_mem_airyCutCellSet I x p hp] with k hk hpk
    obtain ⟨c, hc⟩ := hpk
    let S := airyCutCellSet I x k c
    let a := (2 : ℝ) ^ k
    have ha : 0 < a := by dsimp [a]; positivity
    have hμS : airySiteMeasure I S = ENNReal.ofReal a⁻¹ := airySiteMeasure_airyCutCellSet I x k c
    have hfinite : airySiteMeasure I S < ⊤ := by rw [hμS]; exact ENNReal.ofReal_lt_top
    let : IsFiniteMeasure ((airySiteMeasure I).restrict S) := ⟨by simpa using hfinite⟩
    have hInt : IntegrableOn f S (airySiteMeasure I) :=
      (hm.mono_measure Measure.restrict_le_self).integrable (by norm_num)
    have he :
        airyCutCellAveragedFn I x k f p - f p =
          airyCutCellAveragedFn I x k (fun r => f r - f p) p := by
      rw [airyCutCellAveragedFn_of_mem I x k f hc,
        airyCutCellAveragedFn_of_mem I x k (fun r => f r - f p) hc,
        integral_sub hInt (integrable_const _), setIntegral_const, smul_eq_mul,
        measureReal_def, hμS, ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le)]
      change a * (∫ r in S, f r ∂(airySiteMeasure I)) - f p =
        a * ((∫ r in S, f r ∂(airySiteMeasure I)) - a⁻¹ * f p)
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    rw [dist_eq_norm, he]
    refine (norm_airyCutCellAveragedFn_le I x k _ hc (B := ε / 2) ?_).trans_lt (by linarith)
    intro r hr
    have htag : r.1 = p.1 := (show r.1 = c.1 from hr.1).trans (show p.1 = c.1 from hc.1).symm
    have hdist : dist r p < δ := by
      rw [Prod.dist_eq, htag, dist_self, max_lt_iff, Real.dist_eq]
      exact ⟨hδ, (abs_sub_le_airyCutCell_width I x k c hr hc).trans_lt hk⟩
    simpa only [dist_eq_norm] using (hclose hdist).le
  · rw [Set.indicator_of_notMem hp]
    have hz (k : ℕ) : airyCutCellAveragedFn I x k f p = 0 :=
      airyCutCellAveragedFn_of_not_exists I x k f fun ⟨c, hc⟩ =>
        hp (airyCutCellSet_subset I x k c hc)
    simpa only [hz] using tendsto_const_nhds

/-- Cell projections converge in square-integrable norm on continuous compactly supported
functions by dominated convergence in a fixed bounded slab. -/
theorem tendsto_cellProjection_toLp_of_hasCompactSupport
    (I : Finset ℝ) (x : I → ℝ) (f : I × ℝ → ℝ)
    (hf : Continuous f) (hcompact : HasCompactSupport f) (hm : MemLp f 2 (airySiteMeasure I)) :
    Tendsto (fun k => cellProjection I x k (hm.toLp f)) atTop
      (𝓝 (cutSpaceProjection I x (hm.toLp f))) := by
  obtain ⟨C₀, hC₀⟩ := hcompact.isCompact.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨R₀, hR₀⟩ := hcompact.isCompact.exists_bound_of_continuousOn
    (continuous_snd : Continuous (Prod.snd : I × ℝ → ℝ)).continuousOn
  let C := |C₀|
  let R := |R₀|
  have hfbound (p : I × ℝ) : ‖f p‖ ≤ C := by
    by_cases hp : p ∈ tsupport f
    · exact (hC₀ p hp).trans (le_abs_self _)
    · rw [image_eq_zero_of_notMem_tsupport hp, norm_zero]
      exact abs_nonneg _
  have hfzero (p : I × ℝ) (hp : R < |p.2|) : f p = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    exact (not_lt_of_ge ((hR₀ p hm).trans (le_abs_self _))) hp
  let S : Set (I × ℝ) := Set.univ ×ˢ Set.Icc (-(R + 1)) (R + 1)
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Icc
  have hSfinite : airySiteMeasure I S < ⊤ := by
    unfold airySiteMeasure
    dsimp [S]
    rw [Measure.prod_prod, Real.volume_Icc]
    exact ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top
  let G : (I × ℝ) → ℝ := S.indicator (fun _ => (2 * C) ^ 2)
  have hG : Integrable G (airySiteMeasure I) := by
    exact (integrable_indicator_iff hS).2 (integrableOn_const hSfinite.ne)
  let g := hm.toLp f
  let diff (k : ℕ) (p : I × ℝ) :=
    airyCutCellAveragedFn I x k f p - (airyCutSites I x).indicator f p
  have hae (k : ℕ) : ⇑(cellProjection I x k g - cutSpaceProjection I x g) =ᵐ[airySiteMeasure I] diff k := by
    have hco := hm.coeFn_toLp
    have hcell := cellProjection_apply_ae I x k g
    rw [airyCutCellAveragedFn_congr I x k hco] at hcell
    filter_upwards [Lp.coeFn_sub (cellProjection I x k g) (cutSpaceProjection I x g),
      hcell, cutSpaceProjection_apply_ae I x g, hco] with p hd hc hs hgp
    rw [hd, Pi.sub_apply, hc, hs]
    dsimp [diff]
    by_cases h : p ∈ airyCutSites I x
    · change g p = f p at hgp
      simp only [Set.indicator_of_mem h, hgp]
    · simp only [Set.indicator_of_notMem h]
  have hdom (k : ℕ) (p : I × ℝ) : ‖diff k p ^ 2‖ ≤ G p := by
    have hcut : ‖(airyCutSites I x).indicator f p‖ ≤ C := by
      by_cases hp : p ∈ airyCutSites I x
      · simpa only [Set.indicator_of_mem hp] using hfbound p
      · simp [Set.indicator_of_notMem hp, C]
    have havg : ‖airyCutCellAveragedFn I x k f p‖ ≤ C := by
      by_cases hi : ∃ c, p ∈ airyCutCellSet I x k c
      · obtain ⟨c, hc⟩ := hi
        exact norm_airyCutCellAveragedFn_le I x k f hc (fun r _ => hfbound r)
      · rw [airyCutCellAveragedFn_of_not_exists I x k f hi, norm_zero]
        exact abs_nonneg _
    by_cases hp : p ∈ S
    · rw [show G p = (2 * C) ^ 2 from Set.indicator_of_mem hp _, Real.norm_of_nonneg (sq_nonneg _)]
      have h := (norm_sub_le (airyCutCellAveragedFn I x k f p)
        ((airyCutSites I x).indicator f p)).trans (add_le_add havg hcut)
      have h' : ‖diff k p‖ ≤ 2 * C := by simpa only [diff, two_mul] using h
      simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) h' 2
    · have hp' : R + 1 < |p.2| := by
        apply lt_of_not_ge
        intro h
        exact hp ⟨Set.mem_univ _, abs_le.mp h⟩
      have hpzero : f p = 0 := hfzero p (by linarith)
      have hazero : airyCutCellAveragedFn I x k f p = 0 := by
        by_cases hi : ∃ c, p ∈ airyCutCellSet I x k c
        · obtain ⟨c, hc⟩ := hi
          rw [airyCutCellAveragedFn_of_mem I x k f hc]
          suffices (∫ r in airyCutCellSet I x k c, f r ∂(airySiteMeasure I)) = 0 by rw [this, mul_zero]
          rw [← integral_indicator (measurableSet_airyCutCellSet I x k c)]
          apply integral_eq_zero_of_ae
          exact ae_of_all _ fun r => by
            change (airyCutCellSet I x k c).indicator f r = (0 : ℝ)
            by_cases hr : r ∈ airyCutCellSet I x k c
            · have hd := (abs_sub_le_airyCutCell_width I x k c hc hr).trans
                (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
              have habs : |p.2| ≤ 1 + |r.2| := by
                calc
                  _ = |(p.2 - r.2) + r.2| := by ring_nf
                  _ ≤ |p.2 - r.2| + |r.2| := abs_add_le _ _
                  _ ≤ _ := by linarith
              rw [Set.indicator_of_mem hr, hfzero r (by linarith)]
            · exact Set.indicator_of_notMem hr _
        · exact airyCutCellAveragedFn_of_not_exists I x k f hi
      have hcutzero : (airyCutSites I x).indicator f p = 0 := by
        by_cases hx : p ∈ airyCutSites I x <;> simp [hx, hpzero]
      simp [diff, hazero, hcutzero, G, hp]
  have hsq (k : ℕ) : ‖cellProjection I x k g - cutSpaceProjection I x g‖ ^ 2 =
      ∫ p, diff k p ^ 2 ∂(airySiteMeasure I) := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hae k] with p hp
    rw [hp, Real.inner_apply, sq]
  have hlim : Tendsto (fun k => ∫ p, diff k p ^ 2 ∂(airySiteMeasure I)) atTop (𝓝 0) := by
    have hmeas (k : ℕ) : AEStronglyMeasurable (fun p => diff k p ^ 2) (airySiteMeasure I) :=
      ((Lp.aestronglyMeasurable (cellProjection I x k g - cutSpaceProjection I x g)).pow 2).congr
        ((hae k).mono fun p hp => congrArg (fun r : ℝ => r ^ 2) hp)
    have h := tendsto_integral_of_dominated_convergence G hmeas hG
      (fun k => ae_of_all _ (hdom k))
      (f := fun _ => (0 : ℝ)) (ae_of_all _ fun p => by
        simpa [diff] using ((tendsto_airyCutCellAveragedFn I x f hf hm p).sub
          (tendsto_const_nhds (x := (airyCutSites I x).indicator f p))).pow 2)
    simpa using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heq (k : ℕ) : ‖cellProjection I x k g - cutSpaceProjection I x g‖ =
      Real.sqrt (∫ p, diff k p ^ 2 ∂(airySiteMeasure I)) := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  change Tendsto (fun k => ‖cellProjection I x k g - cutSpaceProjection I x g‖) atTop (𝓝 0)
  simp_rw [heq]
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
  rw [Real.sqrt_zero] at h
  exact h

/-- The finite cell projections converge strongly to the support projection. -/
theorem tendsto_cellProjection (I : Finset ℝ) (x : I → ℝ) (f : TaggedLp I) :
    Tendsto (fun k => cellProjection I x k f) atTop (𝓝 (cutSpaceProjection I x f)) := by
  let : (airySiteMeasure I).Regular := by unfold airySiteMeasure; infer_instance
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, hcomp, hnear, hcont, hmem⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ((ENNReal.ofReal_pos.mpr (by positivity : 0 < ε / 4)).ne')
  let v := hmem.toLp g
  have hv : ‖f - v‖ ≤ ε / 4 := by
    rw [Lp.norm_def]
    have hae : ⇑(f - v) =ᵐ[airySiteMeasure I] (⇑f - g) := by
      filter_upwards [Lp.coeFn_sub f v, hmem.coeFn_toLp] with p hfp hvp
      change v p = g p at hvp
      simpa only [Pi.sub_apply, hvp] using hfp
    rw [eLpNorm_congr_ae hae]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnear).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hlim := tendsto_cellProjection_toLp_of_hasCompactSupport I x g hcont hcomp hmem
  filter_upwards [Metric.tendsto_nhds.mp hlim (ε / 2) (by positivity)] with k hk
  let P := cellProjection I x k
  let S := cutSpaceProjection I x
  have hP : dist (P f) (P v) ≤ ε / 4 := by
    rw [dist_eq_norm, ← map_sub]
    exact ((P.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _)
      (norm_cellProjection_le I x k))).trans hv
  have hS : dist (S v) (S f) ≤ ε / 4 := by
    rw [dist_comm, dist_eq_norm, ← map_sub]
    exact ((S.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _)
      (norm_cutSpaceProjection_le I x))).trans hv
  have ht := (dist_triangle (P f) (P v) (S f)).trans
    (add_le_add_right (dist_triangle (P v) (S v) (S f)) _)
  change dist (P f) (S f) < ε
  change dist (P v) (S v) < ε / 2 at hk
  linarith

/-- A kernel supported in both variables on the active sites is unchanged by
the two-sided support projection. -/
theorem cutSpaceProjection_comp_kernelOperator (I : Finset ℝ) (x : I → ℝ)
    (K : (I × ℝ) → (I × ℝ) → ℝ)
    (hm : MemLp (fun z : (I × ℝ) × (I × ℝ) => K z.1 z.2)
      2 ((airySiteMeasure I).prod (airySiteMeasure I)))
    (hs : cutKernelSupported I x K) :
    cutSpaceProjection I x ∘L HilbertSchmidt.kernelOperator hm ∘L cutSpaceProjection I x =
      HilbertSchmidt.kernelOperator hm := by
  let P := cutSpaceProjection I x
  let A := HilbertSchmidt.kernelOperator hm
  ext1 f
  change P (A (P f)) = A f
  apply Lp.ext
  have hPf := cutSpaceProjection_apply_ae I x f
  filter_upwards [cutSpaceProjection_apply_ae I x (A (P f)),
    HilbertSchmidt.kernelOperator_apply_ae hm (P f),
    HilbertSchmidt.kernelOperator_apply_ae hm f] with p hp hPA hA
  rw [hp, hA]
  by_cases h : p ∈ airyCutSites I x
  · rw [Set.indicator_of_mem h, hPA]
    change (∫ q, K p q * P f q ∂(airySiteMeasure I)) = ∫ q, K p q * f q ∂(airySiteMeasure I)
    apply integral_congr_ae
    filter_upwards [hPf] with q hq
    change P f q = _ at hq
    rw [hq]
    by_cases hq' : q ∈ airyCutSites I x
    · rw [Set.indicator_of_mem hq']
    · simp only [hs p q (Or.inr (le_of_not_gt hq')), zero_mul]
  · rw [Set.indicator_of_notMem h]
    change (0 : ℝ) = ∫ q, K p q * f q ∂(airySiteMeasure I)
    simp only [hs p _ (Or.inl (le_of_not_gt h)), zero_mul, integral_zero]

/-- Cell compressions converge in trace norm for operators supported on the cut space. -/
theorem tendsto_cellCompress_traceNorm (I : Finset ℝ) (x : I → ℝ)
    (A : TaggedLp I →L[ℝ] TaggedLp I) (hA : HilbertSchmidt.IsTraceClass A)
    (hs : cutSpaceProjection I x ∘L A ∘L cutSpaceProjection I x = A) :
    Tendsto (fun k : ℕ => HilbertSchmidt.traceNorm
      (cellProjection I x k ∘L A ∘L cellProjection I x k - A)) atTop (𝓝 0) :=
  tendsto_traceNorm_compression_of_strong (cellProjection I x) (cutSpaceProjection I x) A
    (norm_cellProjection_le I x) (norm_cutSpaceProjection_le I x)
    (adjoint_cellProjection I x) (adjoint_cutSpaceProjection I x)
    (tendsto_cellProjection I x) hA hs

/-- The literal regular-kernel Fredholm series equals the Fredholm determinant
of its trace-class integral operator. -/
theorem kernelFredholmSeries_eq_fredholmDet_of_cut
    (I : Finset ℝ) (x : I → ℝ) (K : (I × ℝ) → (I × ℝ) → ℝ)
    (hm : MemLp (fun p : (I × ℝ) × (I × ℝ) => K p.1 p.2)
      2 ((airySiteMeasure I).prod (airySiteMeasure I)))
    (hs : cutKernelSupported I x K) (hc : cutKernelContinuous I x K)
    (hb : cutKernelRowEnvelope I x K)
    (ht : HilbertSchmidt.IsTraceClass (HilbertSchmidt.kernelOperator hm)) :
    kernelFredholmSeries (airySiteMeasure I) K =
      HilbertSchmidt.fredholmDet (HilbertSchmidt.kernelOperator hm) 1 := by
  have hseries := tendsto_airyCutAveragedKernel_series I x K hm hs hc hb
  have htrace := tendsto_cellCompress_traceNorm I x _ ht
    (cutSpaceProjection_comp_kernelOperator I x K hm hs)
  have htc (k : ℕ) : HilbertSchmidt.traceENorm
      (cellProjection I x k ∘L HilbertSchmidt.kernelOperator hm ∘L cellProjection I x k -
        HilbertSchmidt.kernelOperator hm) ≠ ⊤ := by
    exact HilbertSchmidt.traceENorm_sub_ne_top
      ((ht.comp_right _).comp_left _).traceENorm_ne_top ht.traceENorm_ne_top
  have hdet := HilbertSchmidt.tendsto_fredholmDet_of_traceNorm ht.traceENorm_ne_top htc htrace 1
  simp_rw [kernelFredholmSeries_airyCutAveragedKernel_eq_fredholmDet_cellCompression I x _ K hm ht]
    at hseries
  exact tendsto_nhds_unique hseries hdet

/-- The finite alternating geometric sum is a left inverse for identity plus a nilpotent. -/
theorem one_add_mul_alternating_sum_of_pow_eq_zero {R : Type*} [Ring R]
    (L : R) (n : ℕ) (hL : L ^ n = 0) :
    (1 + L) * (∑ j ∈ Finset.range n, (-L) ^ j) = 1 := by
  have hpow : (-L) ^ n = 0 := by
    rw [neg_pow, hL, mul_zero]
  simpa only [sub_neg_eq_add, hpow, sub_zero] using (mul_neg_geom_sum (-L) n)

/-- The two factors multiply to identity minus the column-row term plus the upper term. -/
theorem qr_factor_mul_identity {R : Type*} [Ring R] (L Q B : R) (hQ : (1 + L) * Q = 1) :
    -L + Q * B - (-L) * (Q * B) = B - L := by
  have h : (1 + L) * Q * B = B := by rw [hQ, one_mul]
  have h' : Q * B + L * (Q * B) = B := by
    simpa only [mul_assoc, add_mul, one_mul] using h
  calc
    _ = -L + (Q * B + L * (Q * B)) := by noncomm_ring
    _ = _ := by rw [h']; abel

/-- Endomorphism multiplication agrees with iterated rectangular composition. -/
theorem qr_mul_comp_assoc {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : E →L[ℝ] E) (A : F →L[ℝ] E) (D : E →L[ℝ] F) :
    Q * (A ∘L D) = (Q ∘L A) ∘L D := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

/-- The QR factor identity for continuous linear maps. -/
theorem qr_operator_factor {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L Q : E →L[ℝ] E) (A : F →L[ℝ] E) (D : E →L[ℝ] F)
    (hQ : (1 + L) * Q = 1) :
    -L + ((Q ∘L A) ∘L D) - (-L) ∘L ((Q ∘L A) ∘L D) = A ∘L D - L := by
  have h := qr_factor_mul_identity L Q (A ∘L D) hQ
  rw [qr_mul_comp_assoc Q A D, ContinuousLinearMap.mul_def] at h
  exact h

/-- The block reduction uses Fredholm multiplicativity and the rectangular Sylvester identity. -/
theorem fredholmDet_colRow_sub_eq
    {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] E) (A : F →L[ℝ] E) (D : E →L[ℝ] F) (n : ℕ)
    (hnil : L ^ n = 0) (hL : HilbertSchmidt.IsTraceClass (-L))
    (htri : HilbertSchmidt.fredholmDet (-L) 1 = 1)
    (hA : HilbertSchmidt.IsRectTraceClass A) :
    HilbertSchmidt.fredholmDet (A ∘L D - L) 1 =
      HilbertSchmidt.fredholmDet (D ∘L (∑ j ∈ Finset.range n, (-L) ^ j) ∘L A) 1 := by
  let Q : E →L[ℝ] E := ∑ j ∈ Finset.range n, (-L) ^ j
  have hQ : (1 + L) * Q = 1 := one_add_mul_alternating_sum_of_pow_eq_zero L n hnil
  have hQA : HilbertSchmidt.IsRectTraceClass (Q ∘L A) := by
    obtain ⟨U, V, hU, hV, rfl⟩ := hA
    exact ⟨Q ∘L U, V, hU.comp_left Q, hV, ContinuousLinearMap.comp_assoc _ _ _⟩
  have hX : HilbertSchmidt.IsTraceClass ((Q ∘L A) ∘L D) := hQA.isTraceClass_comp D
  have hmult := HilbertSchmidt.fredholmDet_add_sub_comp
    (A := -L) (B := (Q ∘L A) ∘L D) hL.traceENorm_ne_top hX.traceENorm_ne_top
  rw [qr_operator_factor L Q A D hQ, htri, one_mul] at hmult
  have hswap := HilbertSchmidt.fredholmDet_comp_comm_rect_left hQA D (1 : ℝ)
  rw [← ContinuousLinearMap.comp_assoc] at hswap
  exact hmult.trans hswap

/-- The measure on one tagged copy is the pushforward of Lebesgue measure. -/
theorem map_airyTag (I : Finset ℝ) (i : I) :
    Measure.map (Prod.mk i : ℝ → I × ℝ) volume =
      (airySiteMeasure I).restrict ({i} ×ˢ (Set.univ : Set ℝ)) := by
  rw [airySiteMeasure, ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.restrict_singleton, Measure.count_singleton, one_smul, Measure.dirac_prod]

/-- Each time slice extracts a square-integrable function on the real line. -/
theorem memLp_airyTagOut (I : Finset ℝ) (i : I) (f : TaggedLp I) :
    MemLp (fun r => f (i, r)) 2 (volume : Measure ℝ) := by
  have hm : MeasurePreserving (Prod.mk i : ℝ → I × ℝ) volume
      ((airySiteMeasure I).restrict ({i} ×ˢ (Set.univ : Set ℝ))) :=
    ⟨measurable_prodMk_left, map_airyTag I i⟩
  exact ((Lp.memLp f).mono_measure Measure.restrict_le_self).comp_measurePreserving hm

/-- Restriction to a single tag is a bounded coordinate map. -/
noncomputable def airyTagOut (I : Finset ℝ) (i : I) : TaggedLp I →L[ℝ] RealLp := by
  let T (f : TaggedLp I) : RealLp :=
    (memLp_airyTagOut I i f).toLp (fun r => f (i, r))
  have hT (f : TaggedLp I) : ⇑(T f) =ᵐ[(volume : Measure ℝ)] fun r => f (i, r) :=
    (memLp_airyTagOut I i f).coeFn_toLp
  have hmap : Measure.map (Prod.mk i : ℝ → I × ℝ) volume ≤ airySiteMeasure I :=
    (map_airyTag I i).trans_le Measure.restrict_le_self
  have hmp : MeasurePreserving (Prod.mk i : ℝ → I × ℝ) volume
      (Measure.map (Prod.mk i) (volume : Measure ℝ)) := ⟨measurable_prodMk_left, rfl⟩
  have ae_tag {P : I × ℝ → Prop} (h : ∀ᵐ p ∂(airySiteMeasure I), P p) :
      ∀ᵐ r ∂(volume : Measure ℝ), P (i, r) :=
    hmp.quasiMeasurePreserving.ae (ae_mono hmap h)
  refine LinearMap.mkContinuous
    { toFun := T
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · intro f g
    apply Lp.ext
    filter_upwards [hT (f + g), hT f, hT g, ae_tag (Lp.coeFn_add f g),
      Lp.coeFn_add (T f) (T g)] with r hfg hf hg hadd hadd'
    rw [hfg, hadd', Pi.add_apply, hf, hg]
    exact hadd
  · intro c f
    change T (c • f) = c • T f
    apply Lp.ext
    filter_upwards [hT (c • f), hT f, ae_tag (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (T f)] with r hcf hf hsmul hsmul'
    rw [hcf, hsmul', Pi.smul_apply, hf]
    exact hsmul
  · intro f
    change ‖T f‖ ≤ 1 * ‖f‖
    rw [one_mul, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hT f)]
    change (eLpNorm (⇑f ∘ (Prod.mk i : ℝ → I × ℝ)) 2 volume).toReal ≤ _
    rw [eLpNorm_comp_measurePreserving ((Lp.memLp f).mono_measure hmap).aestronglyMeasurable hmp]
    exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_lt_top.ne (eLpNorm_mono_measure _ hmap)

/-- The coordinate extraction is represented by evaluation on its tagged line. -/
theorem airyTagOut_apply_ae (I : Finset ℝ) (i : I) (f : TaggedLp I) :
    ⇑(airyTagOut I i f) =ᵐ[(volume : Measure ℝ)] fun r => f (i, r) :=
  (memLp_airyTagOut I i f).coeFn_toLp

/-- Almost-everywhere statements on tagged space are equivalent to statements on each line. -/
theorem ae_airySiteMeasure_iff (I : Finset ℝ) (P : I × ℝ → Prop) :
    (∀ᵐ p ∂(airySiteMeasure I), P p) ↔ ∀ i : I, ∀ᵐ r ∂(volume : Measure ℝ), P (i, r) := by
  rw [airySiteMeasure, Measure.count, Measure.prod_sum_left, Measure.ae_sum_iff]
  exact forall_congr' fun i => by
    rw [Measure.dirac_prod, (measurableEmbedding_prodMk_left i).ae_map_iff]

/-- Extension by zero of a function on a single tagged line. -/
noncomputable def airyTagExtend (I : Finset ℝ) (i : I) (f : ℝ → ℝ) : I × ℝ → ℝ :=
  ({i} ×ˢ (Set.univ : Set ℝ)).indicator (f ∘ Prod.snd)

/-- Extension by zero preserves the square-integrable seminorm. -/
theorem eLpNorm_airyTagExtend (I : Finset ℝ) (i : I) (f : RealLp) :
    eLpNorm (airyTagExtend I i f) 2 (airySiteMeasure I) = eLpNorm f 2 volume := by
  have hs : MeasurableSet ({i} ×ˢ (Set.univ : Set ℝ)) :=
    (measurableSet_singleton _).prod MeasurableSet.univ
  have hf : AEStronglyMeasurable (⇑f ∘ Prod.snd) (airySiteMeasure I) :=
    (Lp.aestronglyMeasurable f).comp_snd
  have hmp : MeasurePreserving (Prod.mk i : ℝ → I × ℝ) volume
      ((airySiteMeasure I).restrict ({i} ×ˢ (Set.univ : Set ℝ))) :=
    ⟨measurable_prodMk_left, map_airyTag I i⟩
  rw [airyTagExtend, eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet,
    ← eLpNorm_comp_measurePreserving (hf.mono_measure Measure.restrict_le_self) hmp]
  rfl

/-- Extending a square-integrable real-line function by zero gives a tagged-space element. -/
theorem memLp_airyTagExtend (I : Finset ℝ) (i : I) (f : RealLp) :
    MemLp (airyTagExtend I i f) 2 (airySiteMeasure I) := by
  rw [memLp_iff]
  rw [eLpNorm_airyTagExtend]
  exact (Lp.memLp f).eLpNorm_lt_top

/-- Isometric injection of a real-line (L²) function into a tagged space. -/
noncomputable def airyTagIn (I : Finset ℝ) (i : I) : RealLp →L[ℝ] TaggedLp I := by
  let T (f : RealLp) : TaggedLp I :=
    (memLp_airyTagExtend I i f).toLp (airyTagExtend I i f)
  have hT (f : RealLp) : ⇑(T f) =ᵐ[airySiteMeasure I] airyTagExtend I i f :=
    (memLp_airyTagExtend I i f).coeFn_toLp
  refine LinearMap.mkContinuous
    { toFun := T
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · intro f g
    apply Lp.ext
    have hAE : ∀ᵐ p ∂(airySiteMeasure I), (f + g) p.2 = f p.2 + g p.2 :=
      (ae_airySiteMeasure_iff I _).2 fun _ => Lp.coeFn_add f g
    filter_upwards [hT (f + g), hT f, hT g, Lp.coeFn_add (T f) (T g), hAE]
      with p hfg hf hg hadd hsum
    rw [hfg, hadd, Pi.add_apply, hf, hg]
    by_cases h : p ∈ ({i} ×ˢ (Set.univ : Set ℝ))
    · simpa only [airyTagExtend, Set.indicator_of_mem h, Function.comp_apply, Pi.add_apply] using hsum
    · simp only [airyTagExtend, Set.indicator_of_notMem h, add_zero]
  · intro c f
    change T (c • f) = c • T f
    apply Lp.ext
    have hAE : ∀ᵐ p ∂(airySiteMeasure I), (c • f) p.2 = c • f p.2 :=
      (ae_airySiteMeasure_iff I _).2 fun _ => Lp.coeFn_smul c f
    filter_upwards [hT (c • f), hT f, Lp.coeFn_smul c (T f), hAE] with p hcf hf hsmul hval
    rw [hcf, hsmul, Pi.smul_apply, hf]
    by_cases h : p ∈ ({i} ×ˢ (Set.univ : Set ℝ))
    · simpa only [airyTagExtend, Set.indicator_of_mem h, Function.comp_apply, Pi.smul_apply] using hval
    · simp only [airyTagExtend, Set.indicator_of_notMem h, smul_zero]
  · intro f
    change ‖T f‖ ≤ 1 * ‖f‖
    rw [one_mul, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hT f), eLpNorm_airyTagExtend]

/-- The coordinate injection is represented by extension by zero. -/
theorem airyTagIn_apply_ae (I : Finset ℝ) (i : I) (f : RealLp) :
    ⇑(airyTagIn I i f) =ᵐ[airySiteMeasure I] airyTagExtend I i f :=
  (memLp_airyTagExtend I i f).coeFn_toLp

/-- Distinct tagged lines have disjoint coordinate maps. -/
theorem airyTagOut_comp_airyTagIn (I : Finset ℝ) (i j : I) :
    airyTagOut I i ∘L airyTagIn I j =
      if i = j then ContinuousLinearMap.id ℝ RealLp else 0 := by
  classical
  ext1 f
  apply Lp.ext
  have hin := (ae_airySiteMeasure_iff I _).1 (airyTagIn_apply_ae I j f) i
  filter_upwards [airyTagOut_apply_ae I i (airyTagIn I j f), hin] with r ho hi
  rw [ContinuousLinearMap.comp_apply, ho, hi]
  by_cases h : i = j <;> simp [h, airyTagExtend]

/-- A tagged function is the sum of the extensions of its coordinates. -/
theorem sum_airyTagIn_comp_airyTagOut (I : Finset ℝ) :
    (∑ i : I, airyTagIn I i ∘L airyTagOut I i) = ContinuousLinearMap.id ℝ (TaggedLp I) := by
  classical
  ext1 f
  rw [ContinuousLinearMap.sum_apply]
  apply Lp.ext
  apply (ae_airySiteMeasure_iff I _).2
  intro i
  have hin (j : I) := (ae_airySiteMeasure_iff I _).1
    (airyTagIn_apply_ae I j (airyTagOut I j f)) i
  have hsum := (ae_airySiteMeasure_iff I _).1
    (Lp.coeFn_fun_finsetSum Finset.univ (fun j : I => airyTagIn I j (airyTagOut I j f))) i
  filter_upwards [ae_all_iff.mpr hin, hsum, airyTagOut_apply_ae I i f] with r ha hb hc
  change (∑ j : I, airyTagIn I j (airyTagOut I j f)) (i, r) = f (i, r)
  rw [hb]
  simp_rw [ha, airyTagExtend]
  rw [Finset.sum_eq_single i]
  · simpa using hc
  · intro j _ hji
    have hn : (i, r) ∉ ({j} ×ˢ (Set.univ : Set ℝ)) := fun h => hji (Eq.symm h.1)
    exact Set.indicator_of_notMem hn _
  · simp

/-- A block family on a finite set of time tags acts by summing the coordinate maps. -/
noncomputable def airyTaggedBlocks (I : Finset ℝ) (B : I → I → RealLp →L[ℝ] RealLp) :
    TaggedLp I →L[ℝ] TaggedLp I :=
  ∑ i : I, ∑ j : I, airyTagIn I i ∘L B i j ∘L airyTagOut I j

/-- Extracting a row of a tagged block operator leaves the sum of that row's blocks. -/
theorem airyTagOut_comp_airyTaggedBlocks (I : Finset ℝ)
    (B : I → I → RealLp →L[ℝ] RealLp) (i : I) :
    airyTagOut I i ∘L airyTaggedBlocks I B = ∑ j : I, B i j ∘L airyTagOut I j := by
  classical
  unfold airyTaggedBlocks
  rw [ContinuousLinearMap.comp_finsetSum]
  rw [Finset.sum_eq_single i]
  · rw [ContinuousLinearMap.comp_finsetSum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← ContinuousLinearMap.comp_assoc, airyTagOut_comp_airyTagIn, if_pos rfl,
      ContinuousLinearMap.id_comp]
  · intro a _ ha
    rw [ContinuousLinearMap.comp_finsetSum]
    apply Finset.sum_eq_zero
    intro b _
    rw [← ContinuousLinearMap.comp_assoc, airyTagOut_comp_airyTagIn, if_neg (Ne.symm ha),
      ContinuousLinearMap.zero_comp]
  · simp

/-- A power of a strictly upper block operator raises the required column rank
by its degree. -/
theorem airyTagOut_comp_airyTaggedBlocks_pow_eq_zero (I : Finset ℝ)
    (B : I → I → RealLp →L[ℝ] RealLp)
    (hB : ∀ i j : I, ¬ ((i : ℝ) < (j : ℝ)) → B i j = 0)
    (n : ℕ) (i j : I) (hij : airyTimeRank I j < airyTimeRank I i + n) :
    airyTagOut I i ∘L ((airyTaggedBlocks I B) ^ n) ∘L airyTagIn I j = 0 := by
  classical
  induction n generalizing i with
  | zero =>
    simp only [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
      airyTagOut_comp_airyTagIn]
    apply ite_eq_right
    intro h
    subst j
    omega
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc (airyTaggedBlocks I B),
      ← ContinuousLinearMap.comp_assoc (airyTagOut I i), airyTagOut_comp_airyTaggedBlocks,
      ContinuousLinearMap.finsetSum_comp]
    apply Finset.sum_eq_zero
    intro a _
    rw [ContinuousLinearMap.comp_assoc]
    by_cases ha : (i : ℝ) < (a : ℝ)
    · have hr := airyTimeRank_lt_of_lt I ha
      have hj : airyTimeRank I j < airyTimeRank I a + n := by omega
      rw [ih a hj, ContinuousLinearMap.comp_zero]
    · rw [hB i a ha, ContinuousLinearMap.zero_comp]

/-- A strictly upper block operator is nilpotent. -/
theorem airyTaggedBlocks_pow_card_succ_eq_zero (I : Finset ℝ)
    (B : I → I → RealLp →L[ℝ] RealLp)
    (hB : ∀ i j : I, ¬ ((i : ℝ) < (j : ℝ)) → B i j = 0) :
    (airyTaggedBlocks I B) ^ (I.card + 1) = 0 := by
  let L := (airyTaggedBlocks I B) ^ (I.card + 1)
  have hf (i j : I) : airyTagOut I i ∘L L ∘L airyTagIn I j = 0 := by
    have hj : airyTimeRank I j ≤ I.card := Finset.card_filter_le _ _
    exact airyTagOut_comp_airyTaggedBlocks_pow_eq_zero I B hB _ i j (by omega)
  have hrow (i : I) : airyTagOut I i ∘L L = 0 := by
    calc
      _ = (airyTagOut I i ∘L L) ∘L (∑ j : I, airyTagIn I j ∘L airyTagOut I j) := by
        rw [sum_airyTagIn_comp_airyTagOut, ContinuousLinearMap.comp_id]
      _ = 0 := by
        rw [ContinuousLinearMap.comp_finsetSum]
        apply Finset.sum_eq_zero
        intro j _
        have hj := hf i j
        rw [← ContinuousLinearMap.comp_assoc (airyTagOut I i)] at hj
        rw [← ContinuousLinearMap.comp_assoc (airyTagOut I i ∘L L), hj,
          ContinuousLinearMap.zero_comp]
  calc
    L = (∑ i : I, airyTagIn I i ∘L airyTagOut I i) ∘L L := by
      rw [sum_airyTagIn_comp_airyTagOut, ContinuousLinearMap.id_comp]
    _ = 0 := by
      rw [ContinuousLinearMap.finsetSum_comp]
      apply Finset.sum_eq_zero
      intro i _
      rw [ContinuousLinearMap.comp_assoc, hrow, ContinuousLinearMap.comp_zero]

/-- A heat kernel times an integrable function of its second coordinate is integrable
on the plane. -/
theorem integrable_heat_sub_mul {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ => heatKernel T (p.1 - p.2) * g p.2) (volume.prod volume) := by
  have hh : Continuous (fun p : ℝ × ℝ => heatKernel T (p.1 - p.2)) :=
    (continuous_heatKernel T).comp (continuous_fst.sub continuous_snd)
  refine (integrable_prod_iff' (hh.aestronglyMeasurable.mul
    hg.aestronglyMeasurable.comp_snd)).2 ⟨?_, ?_⟩
  · exact ae_of_all _ fun y => ((integrable_heatKernel hT).comp_sub_right y).mul_const (g y)
  · have h (y : ℝ) : (∫ x, ‖heatKernel T (x - y) * g y‖) = ‖g y‖ := by
      simp_rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg hT _)]
      rw [integral_mul_const, integral_sub_right_eq_self (heatKernel T), integral_heatKernel hT, one_mul]
    change Integrable (fun y => ∫ x, ‖heatKernel T (x - y) * g y‖)
    simpa only [h] using hg.norm

/-- A polynomially conjugated heat block with weights of distinct degrees. -/
noncomputable def qrWeightedHeat (T : ℝ) (m n : ℕ) (p : ℝ × ℝ) : ℝ :=
  (1 + p.1 ^ 2) ^ m / (1 + p.2 ^ 2) ^ n * heatKernel T (p.1 - p.2)

/-- Polynomially weighted heat blocks with at least one degree of weight gap are
Hilbert–Schmidt. -/
theorem memLp_qrWeightedHeat {T : ℝ} (hT : 0 < T) {m n : ℕ} (hmn : m < n) :
    MemLp (qrWeightedHeat T m n) 2 (volume.prod volume) := by
  let T' := 2 * T
  have hT' : 0 < T' := by dsimp [T']; positivity
  obtain ⟨C, hC, hheat⟩ := heatKernel_mul_weight_le m hT'
  let R := c0 T / c0 T' ^ 2
  let B := 2 ^ m * C * R
  have hR : 0 ≤ R := div_nonneg (c0_pos hT).le (sq_nonneg _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsplit (d : ℝ) : heatKernel T d = R * heatKernel T' d * heatKernel T' d := by
    have hD : c0 T' ≠ 0 := (c0_pos hT').ne'
    have hexp : Real.exp (-d ^ 2 / (4 * T')) * Real.exp (-d ^ 2 / (4 * T')) =
        Real.exp (-d ^ 2 / (4 * T)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [T']
      ring
    change c0 T * Real.exp (-d ^ 2 / (4 * T)) =
      (c0 T / c0 T' ^ 2) * (c0 T' * Real.exp (-d ^ 2 / (4 * T'))) *
        (c0 T' * Real.exp (-d ^ 2 / (4 * T')))
    rw [← hexp]
    field_simp
  have hpoint (s t : ℝ) :
      qrWeightedHeat T m n (s, t) ≤ B * (heatKernel T' (s - t) * (1 + t ^ 2)⁻¹) := by
    have hxy : 1 + s ^ 2 ≤ 2 * (1 + t ^ 2) * (1 + (s - t) ^ 2) := by
      nlinarith [sq_nonneg (s - 2 * t), mul_nonneg (sq_nonneg t) (sq_nonneg (s - t))]
    have hpow : (1 + s ^ 2) ^ m ≤
        2 ^ m * (1 + t ^ 2) ^ m * (1 + (s - t) ^ 2) ^ m := by
      calc
        _ ≤ (2 * (1 + t ^ 2) * (1 + (s - t) ^ 2)) ^ m := by gcongr
        _ = _ := by rw [mul_pow, mul_pow]
    have hden : (1 + t ^ 2) ^ m * (1 + t ^ 2) ≤ (1 + t ^ 2) ^ n := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ (by linarith [sq_nonneg t]) hmn
    have hp : 0 < 1 + t ^ 2 := by positivity
    have hg : (1 + s ^ 2) ^ m / (1 + t ^ 2) ^ n ≤
        2 ^ m * (1 + (s - t) ^ 2) ^ m * (1 + t ^ 2)⁻¹ := by
      calc
        _ ≤ (1 + s ^ 2) ^ m / ((1 + t ^ 2) ^ m * (1 + t ^ 2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ ≤ (2 ^ m * (1 + t ^ 2) ^ m * (1 + (s - t) ^ 2) ^ m) /
            ((1 + t ^ 2) ^ m * (1 + t ^ 2)) :=
          div_le_div_of_nonneg_right hpow (by positivity)
        _ = _ := by field_simp
    calc
      _ ≤ (2 ^ m * (1 + (s - t) ^ 2) ^ m * (1 + t ^ 2)⁻¹) * heatKernel T (s - t) :=
        mul_le_mul_of_nonneg_right hg (heatKernel_nonneg hT _)
      _ = (2 ^ m * R * (heatKernel T' (s - t) * (1 + t ^ 2)⁻¹)) *
          ((1 + (s - t) ^ 2) ^ m * heatKernel T' (s - t)) := by rw [hsplit]; ring
      _ ≤ (2 ^ m * R * (heatKernel T' (s - t) * (1 + t ^ 2)⁻¹)) * C := by
        apply mul_le_mul_of_nonneg_left (hheat (s - t))
        exact mul_nonneg (mul_nonneg (by positivity) hR)
          (mul_nonneg (heatKernel_nonneg hT' _) (by positivity))
      _ = _ := by dsimp [B]; ring
  have hmeas : Measurable (qrWeightedHeat T m n) := by
    unfold qrWeightedHeat
    exact (((measurable_fst.pow_const 2).const_add 1).pow_const m).div
      (((measurable_snd.pow_const 2).const_add 1).pow_const n) |>.mul
        ((continuous_heatKernel T).measurable.comp (measurable_fst.sub measurable_snd))
  refine memLp_of_sq_le hmeas
    ((integrable_heat_sub_mul hT' integrable_inv_one_add_sq).const_mul (B ^ 2 * c0 T')) ?_
  rintro ⟨s, t⟩
  have hn : 0 ≤ qrWeightedHeat T m n (s, t) := by
    unfold qrWeightedHeat
    exact mul_nonneg (by positivity) (heatKernel_nonneg hT _)
  have hmax : heatKernel T' (s - t) * (1 + t ^ 2)⁻¹ ≤ c0 T' := by
    exact (mul_le_of_le_one_right (heatKernel_nonneg hT' _)
      (inv_le_one_of_one_le₀ (by linarith [sq_nonneg t]))).trans
      (AiryTwoInt.heatKernel_le hT' _)
  calc
    _ ≤ (B * (heatKernel T' (s - t) * (1 + t ^ 2)⁻¹)) ^ 2 :=
      pow_le_pow_left₀ hn (hpoint s t) 2
    _ ≤ _ := by
      let G := heatKernel T' (s - t) * (1 + t ^ 2)⁻¹
      have hG : 0 ≤ G := mul_nonneg (heatKernel_nonneg hT' _) (by positivity)
      change (B * G) ^ 2 ≤ B ^ 2 * c0 T' * G
      calc
        _ = (B ^ 2 * G) * G := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax (sq_nonneg B)) hG

/-- The first half of a forward heat block, with the left threshold and intermediate gauge. -/
noncomputable def qrHeatLeft (I : Finset ℝ) (x : I → ℝ) (i j : I) : ℝ × ℝ → ℝ :=
  (Prod.fst ⁻¹' Set.Ioi (x i)).indicator
    (qrWeightedHeat (((j : ℝ) - i) / 2) (2 * airyTimeRank I i)
      (airyTimeRank I i + airyTimeRank I j))

/-- The second half of a forward heat block, with the right threshold. -/
noncomputable def qrHeatRight (I : Finset ℝ) (x : I → ℝ) (i j : I) : ℝ × ℝ → ℝ :=
  (Prod.snd ⁻¹' Set.Ioi (x j)).indicator
    (qrWeightedHeat (((j : ℝ) - i) / 2) (airyTimeRank I i + airyTimeRank I j)
      (2 * airyTimeRank I j))

/-- The left heat half is square integrable for strictly increasing time tags. -/
theorem memLp_qrHeatLeft (I : Finset ℝ) (x : I → ℝ) {i j : I} (hij : (i : ℝ) < j) :
    MemLp (qrHeatLeft I x i j) 2 (volume.prod volume) := by
  have hr := airyTimeRank_lt_of_lt I hij
  exact (memLp_qrWeightedHeat (by linarith : 0 < ((j : ℝ) - i) / 2)
    (by omega : 2 * airyTimeRank I i < airyTimeRank I i + airyTimeRank I j)).indicator
      ((measurableSet_Ioi.preimage measurable_fst).nullMeasurableSet)

/-- The right heat half is square integrable for strictly increasing time tags. -/
theorem memLp_qrHeatRight (I : Finset ℝ) (x : I → ℝ) {i j : I} (hij : (i : ℝ) < j) :
    MemLp (qrHeatRight I x i j) 2 (volume.prod volume) := by
  have hr := airyTimeRank_lt_of_lt I hij
  exact (memLp_qrWeightedHeat (by linarith : 0 < ((j : ℝ) - i) / 2)
    (by omega : airyTimeRank I i + airyTimeRank I j < 2 * airyTimeRank I j)).indicator
      ((measurableSet_Ioi.preimage measurable_snd).nullMeasurableSet)

/-- The forward heat operator between two tags is the composition of the weighted halves. -/
noncomputable def airyHeatBlock (I : Finset ℝ) (x : I → ℝ) (i j : I) : RealLp →L[ℝ] RealLp :=
  if h : (i : ℝ) < j then
    HilbertSchmidt.kernelOperator (memLp_qrHeatLeft I x h) ∘L
      HilbertSchmidt.kernelOperator (memLp_qrHeatRight I x h)
  else 0

/-- The strictly upper-triangular heat operator on tagged space. -/
noncomputable def airyHeatUpper (I : Finset ℝ) (x : I → ℝ) :
    TaggedLp I →L[ℝ] TaggedLp I := airyTaggedBlocks I (airyHeatBlock I x)

/-- Every heat block is trace class. -/
theorem airyHeatBlock_isTraceClass (I : Finset ℝ) (x : I → ℝ) (i j : I) :
    HilbertSchmidt.IsTraceClass (airyHeatBlock I x i j) := by
  by_cases h : (i : ℝ) < j
  · rw [airyHeatBlock, dif_pos h]
    exact (HilbertSchmidt.isHilbertSchmidt_kernelOperator _).isTraceClass_comp
      (HilbertSchmidt.isHilbertSchmidt_kernelOperator _)
  · rw [airyHeatBlock, dif_neg h]
    exact HilbertSchmidt.isTraceClass_zero

/-- Finite sums preserve trace class. -/
theorem qr_isTraceClass_finsetSum {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (s : Finset ι) (A : ι → E →L[ℝ] E)
    (hA : ∀ i ∈ s, HilbertSchmidt.IsTraceClass (A i)) :
    HilbertSchmidt.IsTraceClass (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (HilbertSchmidt.isTraceClass_zero : HilbertSchmidt.IsTraceClass (0 : E →L[ℝ] E))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hA i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hA j (Finset.mem_insert_of_mem hj))

/-- The strictly upper-triangular heat operator is trace class. -/
theorem airyHeatUpper_isTraceClass (I : Finset ℝ) (x : I → ℝ) :
    HilbertSchmidt.IsTraceClass (airyHeatUpper I x) := by
  unfold airyHeatUpper airyTaggedBlocks
  apply qr_isTraceClass_finsetSum
  intro i _
  apply qr_isTraceClass_finsetSum
  intro j _
  have h := airyHeatBlock_isTraceClass I x i j
  apply HilbertSchmidt.isTraceClass_sandwich h.isRectTraceClass (airyTagIn I i)
    (airyTagOut I i) _ (airyTagOut I j)
  simp [airyTagOut_comp_airyTagIn]

/-- The strictly upper-triangular heat operator is nilpotent. -/
theorem airyHeatUpper_nilpotent (I : Finset ℝ) (x : I → ℝ) :
    airyHeatUpper I x ^ (I.card + 1) = 0 := by
  apply airyTaggedBlocks_pow_card_succ_eq_zero
  intro i j h
  rw [airyHeatBlock, dif_neg h]

/-- The finite alternating sum that inverts identity plus the upper heat operator. -/
noncomputable def airyUpperInv (I : Finset ℝ) (x : I → ℝ) :
    TaggedLp I →L[ℝ] TaggedLp I :=
  ∑ j ∈ Finset.range (I.card + 1), (-airyHeatUpper I x) ^ j

/-- The trace of a tagged-space operator with zero diagonal blocks is zero. -/
theorem qr_trace_eq_zero_of_diagonal (I : Finset ℝ) (A : TaggedLp I →L[ℝ] TaggedLp I)
    (hA : HilbertSchmidt.IsTraceClass A)
    (hdiag : ∀ i : I, airyTagOut I i ∘L A ∘L airyTagIn I i = 0) :
    HilbertSchmidt.trace A = 0 := by
  let P (i : I) := airyTagIn I i ∘L airyTagOut I i
  have hp (i : I) : P i ∘L P i = P i := by
    unfold P
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (airyTagOut I i),
      airyTagOut_comp_airyTagIn,
      ite_eq_left rfl, ContinuousLinearMap.id_comp]
  have hd (i : I) : P i ∘L (A ∘L P i) = 0 := by
    unfold P
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc A,
      ← ContinuousLinearMap.comp_assoc (airyTagOut I i), hdiag, ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero]
  have hh (i : I) : HilbertSchmidt.trace (A ∘L P i) = 0 := by
    have he := HilbertSchmidt.trace_comp_comm_of_isTraceClass (hA.comp_right (P i)) (P i)
    rw [hd, ContinuousLinearMap.comp_assoc, hp, HilbertSchmidt.trace_zero_op] at he
    exact he.symm
  have hs : A = ∑ i : I, A ∘L P i := by
    rw [← ContinuousLinearMap.comp_finsetSum, sum_airyTagIn_comp_airyTagOut, ContinuousLinearMap.comp_id]
  calc
    _ = HilbertSchmidt.trace (∑ i : I, A ∘L P i) := congrArg HilbertSchmidt.trace hs
    _ = _ := by
      rw [HilbertSchmidt.trace_sum _ (fun i _ =>
        HilbertSchmidt.summable_inner_diagonal (hA.comp_right (P i)) _)]
      simp only [hh, Finset.sum_const_zero]

/-- The strictly upper heat factor contributes determinant one. -/
theorem fredholmDet_neg_airyHeatUpper (I : Finset ℝ) (x : I → ℝ) :
    HilbertSchmidt.fredholmDet (-airyHeatUpper I x) 1 = 1 := by
  let L := airyHeatUpper I x
  have hL : HilbertSchmidt.IsTraceClass L := airyHeatUpper_isTraceClass I x
  have hnL : HilbertSchmidt.IsTraceClass (-L) := by
    simpa using HilbertSchmidt.isTraceClass_zero.sub hL
  refine (HilbertSchmidt.fredholmDet_eq_of_trace_pow_eq hnL
    HilbertSchmidt.isTraceClass_zero ?_ 1).trans (HilbertSchmidt.fredholmDet_zero_op 1)
  intro n hn
  have hp : HilbertSchmidt.IsTraceClass (L ^ n) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ, ContinuousLinearMap.mul_def]
    exact hL.comp_left _
  have hd (i : I) : airyTagOut I i ∘L (L ^ n) ∘L airyTagIn I i = 0 := by
    apply airyTagOut_comp_airyTaggedBlocks_pow_eq_zero I (airyHeatBlock I x)
    · intro p q h
      exact dif_neg h
    · omega
  rw [HilbertSchmidt.neg_pow_clm, HilbertSchmidt.trace_smul, qr_trace_eq_zero_of_diagonal I _ hp hd,
    mul_zero, zero_pow (by omega : n ≠ 0), HilbertSchmidt.trace_zero_op]

/-- The first observation time, with a default for the empty tag set. -/
noncomputable def airyFirstTime (I : Finset ℝ) : ℝ :=
  if h : I.Nonempty then I.min' h else 0

/-- The time span of the finite collection of tags. -/
noncomputable def airyTimeSpan (I : Finset ℝ) : ℝ :=
  if h : I.Nonempty then I.max' h - I.min' h else 0

/-- Time from the first observation to the given tag. -/
noncomputable def airyRelativeTime (I : Finset ℝ) (i : I) : ℝ :=
  (i : ℝ) - airyFirstTime I

/-- Every relative time is nonnegative and at most the time span. -/
theorem airyRelativeTime_bounds (I : Finset ℝ) (i : I) :
    0 ≤ airyRelativeTime I i ∧ airyRelativeTime I i ≤ airyTimeSpan I := by
  have hn : I.Nonempty := ⟨i, i.property⟩
  unfold airyRelativeTime airyFirstTime airyTimeSpan
  simp only [dif_pos hn]
  exact ⟨sub_nonneg.mpr (Finset.min'_le I _ i.property),
    sub_le_sub_right (Finset.le_max' I _ i.property) _⟩

/-- With a nonempty index set, admissible weights dominate every relative time plus one. -/
theorem airyRelativeTime_add_one_lt_weight (I : Finset ℝ) (i : I) {a : ℝ}
    (ha : airyTimeSpan I + 2 ≤ a) : airyRelativeTime I i + 1 < a := by
  linarith [(airyRelativeTime_bounds I i).2]

/-- Products of two square-integrable functions are square integrable on the product space. -/
theorem qr_memLp_mul_prod {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    MemLp (fun p : ℝ × ℝ => f p.1 * g p.2) 2 (volume.prod volume) := by
  have h : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 * g p.2) (volume.prod volume) :=
    hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd
  apply (memLp_two_iff_integrable_sq h).2
  simp_rw [mul_pow]
  exact ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf).mul_prod
    ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).1 hg)

/-- A polynomial times a conjugated heat profile remains square integrable. -/
theorem qr_memLp_poly_conjugateHeat {T : ℝ} (hT : 0 < T) (a : ℝ) (m : ℕ) :
    MemLp (fun d : ℝ => (1 + d ^ 2) ^ m * AiryConj.conjugateHeatKernel T a d) 2 volume := by
  obtain ⟨C, hC, hb⟩ := heatKernel_mul_weight_le (2 * m) hT
  have hcont : Continuous (fun d : ℝ => (1 + d ^ 2) ^ m *
      AiryConj.conjugateHeatKernel T a d) :=
    ((continuous_const.add (continuous_id.pow 2)).pow _).mul
      (AiryConj.continuous_conjugateHeatKernel T a)
  apply (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2
  refine ((AiryConj.integrable_conjugateHeatKernel hT (2 * a)).const_mul C).mono'
    ((hcont.pow 2).aestronglyMeasurable) (ae_of_all _ fun d => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have he : ((1 + d ^ 2) ^ m * AiryConj.conjugateHeatKernel T a d) ^ 2 =
      ((1 + d ^ 2) ^ (2 * m) * heatKernel T d) * AiryConj.conjugateHeatKernel T (2 * a) d := by
    unfold AiryConj.conjugateHeatKernel
    rw [show (- (2 * a) * d) = -a * d + -a * d by ring, Real.exp_add,
      Nat.mul_comm 2 m, pow_mul]
    simp only [mul_pow]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (hb d) (AiryConj.conjugateHeatKernel_nonneg hT _ _)

/-- A polynomial is dominated by an exponential in the absolute value with any positive rate. -/
theorem qr_poly_le_exp_abs (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, (1 + r ^ 2) ^ m ≤ C * Real.exp (a * |r|) := by
  let b := max 1 a⁻¹
  have hb : 0 ≤ b := (zero_le_one.trans (le_max_left _ _))
  refine ⟨b ^ (2 * m) * ((2 * m).factorial : ℝ) * Real.exp 1, by positivity, ?_⟩
  intro r
  have hbase : 1 + r ^ 2 ≤ (1 + |r|) ^ 2 := by
    nlinarith [abs_nonneg r, sq_abs r]
  have hab : 1 ≤ b * a := by
    have h := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) a⁻¹) ha.le
    rwa [inv_mul_cancel₀ ha.ne'] at h
  have hscale : 1 + |r| ≤ b * (1 + a * |r|) := by
    linarith [le_max_left (1 : ℝ) a⁻¹, mul_le_mul_of_nonneg_right hab (abs_nonneg r)]
  have hpoly := add_one_pow_mul_exp_neg_le (2 * m) (mul_nonneg ha.le (abs_nonneg r))
  have hexp := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (a * |r|)).le
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hexp
  calc
    _ ≤ (1 + |r|) ^ (2 * m) := by rw [pow_mul]; gcongr
    _ ≤ (b * (1 + a * |r|)) ^ (2 * m) := by gcongr
    _ = b ^ (2 * m) * (1 + a * |r|) ^ (2 * m) := by rw [mul_pow]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hexp
        (show 0 ≤ b ^ (2 * m) by positivity)

/-- A real exponential on an upper cut dominates every fixed polynomial in (L²). -/
theorem qr_memLp_cut_poly_exp (x : ℝ) {a : ℝ} (ha : 0 < a) (m : ℕ) :
    MemLp ((Set.Ioi x).indicator (fun s : ℝ => (1 + s ^ 2) ^ m * Real.exp (-a * s)))
      2 volume := by
  obtain ⟨C, hC, hc⟩ := qr_poly_le_exp_abs (2 * m) ha
  let G := (Set.Ioi x).indicator (fun s : ℝ => Real.exp (-a * s))
  have hG : Integrable G :=
    (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) x)
  have hmeas : Measurable ((Set.Ioi x).indicator
      (fun s : ℝ => (1 + s ^ 2) ^ m * Real.exp (-a * s))) := by
    apply Measurable.indicator _ measurableSet_Ioi
    fun_prop
  apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
  refine (hG.const_mul (C * Real.exp (2 * a * |x|))).mono'
    ((hmeas.pow_const 2).aestronglyMeasurable) (ae_of_all _ fun s => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  by_cases hs : s ∈ Set.Ioi x
  · rw [Set.indicator_of_mem hs]
    change ((1 + s ^ 2) ^ m * Real.exp (-a * s)) ^ 2 ≤
      (C * Real.exp (2 * a * |x|)) * (Set.Ioi x).indicator _ s
    rw [Set.indicator_of_mem hs, mul_pow, ← pow_mul, Nat.mul_comm m 2]
    rw [show (Real.exp (-a * s)) ^ 2 = Real.exp (-a * s + -a * s) by
      rw [pow_two, ← Real.exp_add]]
    have hs' : x < s := hs
    have hdis : |s| ≤ s + 2 * |x| := by
      rw [abs_le]
      constructor <;> linarith [neg_le_abs x, abs_nonneg x]
    calc
      _ ≤ (C * Real.exp (a * |s|)) * Real.exp (-a * s + -a * s) :=
        mul_le_mul_of_nonneg_right (hc s) (Real.exp_pos _).le
      _ = C * Real.exp (a * |s| - 2 * a * s) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ _ := by
        rw [mul_assoc C, ← Real.exp_add]
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hC
        nlinarith [mul_le_mul_of_nonneg_left hdis ha.le]
  · simp [G, Set.indicator_of_notMem hs]

/-- The exponentially conjugated backward Airy profile. -/
noncomputable def qrAiryProfile (r a s : ℝ) : ℝ :=
  Real.exp (a * s) * backwardAiry r s

/-- The conjugated backward Airy profile is square integrable when the gauge
exceeds the backward heat time. -/
theorem memLp_qrAiryProfile (r a : ℝ) (ha : r < a) :
    MemLp (qrAiryProfile r a) 2 volume := by
  let b := a - r + 1
  have hb : 0 ≤ b := by dsimp [b]; linarith
  obtain ⟨C₀, hC₀⟩ := airyAiReal_abs_le
  obtain ⟨C₁, hC₁, hAi⟩ := airyAiReal_abs_le_exp_rate hb
  let M₀ := |C₀| * Real.exp (-(2 / 3) * r ^ 3)
  let M₁ := C₁ * Real.exp (-(2 / 3) * r ^ 3 - b * r ^ 2)
  let g₀ := (Set.Iic (0 : ℝ)).indicator (fun s => M₀ ^ 2 * Real.exp (2 * (a - r) * s))
  let g₁ := (Set.Ioi (0 : ℝ)).indicator (fun s => M₁ ^ 2 * Real.exp (-2 * s))
  have hg₀ : Integrable g₀ := (integrable_indicator_iff measurableSet_Iic).2
    ((integrableOn_exp_mul_Iic (show 0 < 2 * (a - r) by linarith) 0).const_mul _)
  have hg₁ : Integrable g₁ := (integrable_indicator_iff measurableSet_Ioi).2
    ((integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).const_mul _)
  have hmeas : Measurable (qrAiryProfile r a) := by
    have hAiCont : Continuous airyAiReal :=
      continuous_iff_continuousAt.mpr fun s => (hasDerivAt_airyAiReal s).continuousAt
    unfold qrAiryProfile backwardAiry
    fun_prop
  apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
  refine (hg₀.add hg₁).mono' (hmeas.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun s => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
  have he : |qrAiryProfile r a s| =
      (Real.exp ((a - r) * s) * Real.exp (-(2 / 3) * r ^ 3)) * |airyAiReal (s + r ^ 2)| := by
    simp only [qrAiryProfile, backwardAiry, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  by_cases hs : s ≤ 0
  · have hz : s ∉ Set.Ioi (0 : ℝ) := not_lt_of_ge hs
    have h₀ : s ∈ Set.Iic (0 : ℝ) := hs
    change |qrAiryProfile r a s| ^ 2 ≤ g₀ s + g₁ s
    simp only [g₀, g₁, Set.indicator_of_mem h₀, Set.indicator_of_notMem hz, add_zero]
    have h := mul_le_mul_of_nonneg_left ((hC₀ (s + r ^ 2)).trans (le_abs_self C₀))
      (by positivity : 0 ≤ Real.exp ((a - r) * s) * Real.exp (-(2 / 3) * r ^ 3))
    rw [he]
    refine (pow_le_pow_left₀ (by positivity) h 2).trans_eq ?_
    dsimp [M₀]
    rw [mul_pow, mul_pow, show Real.exp ((a - r) * s) ^ 2 = Real.exp (2 * (a - r) * s) by
      rw [pow_two, ← Real.exp_add]; congr 1; ring, mul_pow]
    ring
  · have h₀ : s ∉ Set.Iic (0 : ℝ) := hs
    have h₁ : s ∈ Set.Ioi (0 : ℝ) := lt_of_not_ge hs
    change |qrAiryProfile r a s| ^ 2 ≤ g₀ s + g₁ s
    simp only [g₀, g₁, Set.indicator_of_notMem h₀, Set.indicator_of_mem h₁, zero_add]
    have h := mul_le_mul_of_nonneg_left (hAi (s + r ^ 2))
      (by positivity : 0 ≤ Real.exp ((a - r) * s) * Real.exp (-(2 / 3) * r ^ 3))
    rw [he]
    refine (pow_le_pow_left₀ (by positivity) h 2).trans_eq ?_
    have hmul :
        (Real.exp ((a - r) * s) * Real.exp (-(2 / 3) * r ^ 3)) *
          (C₁ * Real.exp (-b * (s + r ^ 2))) = M₁ * Real.exp (-s) := by
      dsimp [M₁]
      calc
        _ = C₁ * Real.exp (((a - r) * s + -(2 / 3) * r ^ 3) + -b * (s + r ^ 2)) := by
          rw [Real.exp_add, Real.exp_add]
          ring
        _ = _ := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          dsimp [b]
          ring
    rw [hmul, mul_pow, pow_two (Real.exp (-s)), ← Real.exp_add]
    congr 2
    ring

/-- The Airy half of the column factor uses a square-integrable intermediate weight. -/
noncomputable def qrColumnAiry (r a : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 + p.1 ^ 2)⁻¹ * qrAiryProfile r a (p.1 + p.2)

/-- The Airy half is square integrable by a measure-preserving shear. -/
theorem memLp_qrColumnAiry (r a : ℝ) (ha : r < a) :
    MemLp (qrColumnAiry r a) 2 (volume.prod volume) := by
  have hw : MemLp (fun z : ℝ => (1 + z ^ 2)⁻¹) 2 volume := by
    have hcont : Continuous (fun z : ℝ => (1 + z ^ 2)⁻¹) :=
      (continuous_const.add (continuous_id.pow 2)).inv₀ (fun z => (show 0 < 1 + z ^ 2 by positivity).ne')
    apply (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2
    refine integrable_inv_one_add_sq.mono' (hcont.pow 2).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_of_le_one_right (by positivity)
      (inv_le_one_of_one_le₀ (by linarith [sq_nonneg z]))
  have h := (qr_memLp_mul_prod hw (memLp_qrAiryProfile r a ha)).comp_measurePreserving
    (measurePreserving_prod_add_right (volume : Measure ℝ) (volume : Measure ℝ))
  have heq : qrColumnAiry r a = fun p => (1 + p.1 ^ 2)⁻¹ * qrAiryProfile r a (p.2 + p.1) := by
    funext p
    unfold qrColumnAiry
    rw [add_comm p.1 p.2]
  rw [heq]
  exact h

/-- A cut heat kernel with its intermediate polynomial and exponential weights. -/
noncomputable def qrCutWeightedHeat (T x a : ℝ) (m : ℕ) : ℝ × ℝ → ℝ :=
  (Prod.fst ⁻¹' Set.Ioi x).indicator (fun p =>
    (1 + p.1 ^ 2) ^ m * (heatKernel T (p.1 - p.2) * Real.exp (-a * p.2) * (1 + p.2 ^ 2)))

/-- The heat half is square integrable after separating the spatial difference from
the cutoff coordinate. -/
theorem memLp_qrCutWeightedHeat {T : ℝ} (hT : 0 < T) (x a : ℝ) (ha : 0 < a) (m : ℕ) :
    MemLp (qrCutWeightedHeat T x a m) 2 (volume.prod volume) := by
  let f := (Set.Ioi x).indicator (fun s : ℝ => (1 + s ^ 2) ^ (m + 1) * Real.exp (-a * s))
  let g := fun d : ℝ => (1 + d ^ 2) ^ 1 * AiryConj.conjugateHeatKernel T a d
  have h := (qr_memLp_mul_prod (qr_memLp_cut_poly_exp x ha (m + 1))
    (qr_memLp_poly_conjugateHeat hT a 1)).comp_measurePreserving
      (measurePreserving_prod_sub (volume : Measure ℝ) (volume : Measure ℝ))
  have hb : MemLp (fun p : ℝ × ℝ => 2 * (f p.1 * g (p.2 - p.1)))
      2 (volume.prod volume) := h.const_mul 2
  have hc : Continuous (fun p : ℝ × ℝ => heatKernel T (p.1 - p.2)) :=
    (continuous_heatKernel T).comp (continuous_fst.sub continuous_snd)
  have hm : Measurable (qrCutWeightedHeat T x a m) := by
    unfold qrCutWeightedHeat
    apply Measurable.indicator _ (measurableSet_Ioi.preimage measurable_fst)
    fun_prop
  refine hb.mono' hm.aestronglyMeasurable (ae_of_all _ fun ⟨s, z⟩ => ?_)
  change ‖qrCutWeightedHeat T x a m (s, z)‖ ≤ 2 * (f s * g (z - s))
  by_cases hs : s ∈ Set.Ioi x
  · have hs' : (s, z) ∈ Prod.fst ⁻¹' Set.Ioi x := hs
    have hpoly : 1 + z ^ 2 ≤ 2 * (1 + s ^ 2) * (1 + (z - s) ^ 2) := by
      nlinarith [sq_nonneg (z - 2 * s), mul_nonneg (sq_nonneg s) (sq_nonneg (z - s))]
    have hheat : heatKernel T (s - z) = heatKernel T (z - s) := by
      unfold heatKernel
      rw [show (s - z) ^ 2 = (z - s) ^ 2 by ring]
    simp only [qrCutWeightedHeat, Set.indicator_of_mem hs', Prod.fst, Prod.snd]
    rw [Real.norm_of_nonneg (by positivity [heatKernel_nonneg (T := T) hT (s - z)])]
    calc
      _ ≤ (1 + s ^ 2) ^ m * (heatKernel T (s - z) * Real.exp (-a * z) *
          (2 * (1 + s ^ 2) * (1 + (z - s) ^ 2))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpoly
            (mul_nonneg (heatKernel_nonneg hT _) (Real.exp_pos _).le)) (by positivity)
      _ = _ := by
        simp only [f, g, Set.indicator_of_mem hs, pow_succ, pow_one,
          AiryConj.conjugateHeatKernel, hheat]
        rw [show -a * z = -a * s + -a * (z - s) by ring, Real.exp_add]
        ring
  · have hs' : (s, z) ∉ Prod.fst ⁻¹' Set.Ioi x := hs
    simp only [qrCutWeightedHeat, Set.indicator_of_notMem hs', norm_zero, f,
      Set.indicator_of_notMem hs, zero_mul, mul_zero, le_rfl]

/-- The heat half of the column with its intermediate polynomial and exponential weights. -/
noncomputable def qrColumnHeat (x a : ℝ) (m : ℕ) : ℝ × ℝ → ℝ :=
  (Prod.fst ⁻¹' Set.Ioi x).indicator (fun p =>
    (1 + p.1 ^ 2) ^ m * (heatKernel 1 (p.1 - p.2) * Real.exp (-a * p.2) * (1 + p.2 ^ 2)))

/-- The time-one heat half of the Airy column is square integrable. -/
theorem memLp_qrColumnHeat (x a : ℝ) (ha : 0 < a) (m : ℕ) :
    MemLp (qrColumnHeat x a m) 2 (volume.prod volume) :=
  memLp_qrCutWeightedHeat one_pos x a ha m

/-- Hilbert–Schmidt operators between two spaces are closed under addition. -/
theorem qr_isHilbertSchmidt_add
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {A B : E →L[ℝ] F} (hA : HilbertSchmidt.IsHilbertSchmidt A)
    (hB : HilbertSchmidt.IsHilbertSchmidt B) :
    HilbertSchmidt.IsHilbertSchmidt (A + B) := by
  let b := HilbertSchmidt.canonicalBasis ℝ E
  have hb := ((HilbertSchmidt.summable_norm_sq_of_hs hA b).add
    (HilbertSchmidt.summable_norm_sq_of_hs hB b)).mul_left (2 : ℝ)
  have hs : Summable (fun i => ‖(A + B) (b i)‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_) hb
    rw [ContinuousLinearMap.add_apply]
    calc
      _ ≤ (‖A (b i)‖ + ‖B (b i)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _ ≤ _ := by nlinarith [sq_nonneg (‖A (b i)‖ - ‖B (b i)‖)]
  have hfin : HilbertSchmidt.hsENorm (A + B) ^ 2 ≠ ⊤ := by
    rw [HilbertSchmidt.hsENorm_sq_eq_tsum _ b]
    simp_rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  intro h
  rw [h, ENNReal.top_pow (by norm_num)] at hfin
  exact hfin rfl

/-- A finite sum of rectangular Hilbert–Schmidt maps is Hilbert–Schmidt. -/
theorem qr_isHilbertSchmidt_finsetSum {E F ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (s : Finset ι) (A : ι → E →L[ℝ] F)
    (hA : ∀ i ∈ s, HilbertSchmidt.IsHilbertSchmidt (A i)) :
    HilbertSchmidt.IsHilbertSchmidt (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HilbertSchmidt.IsHilbertSchmidt, HilbertSchmidt.hsENorm_zero']
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact qr_isHilbertSchmidt_add (hA i (Finset.mem_insert_self _ _))
      (ih fun j hj => hA j (Finset.mem_insert_of_mem hj))

/-- The heat half of the tagged Airy column, acting diagonally in the tags. -/
noncomputable def airyColumnHeatOp (I : Finset ℝ) (x : I → ℝ) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) : TaggedLp I →L[ℝ] TaggedLp I :=
  ∑ i : I, airyTagIn I i ∘L
    HilbertSchmidt.kernelOperator
      (memLp_qrColumnHeat (x i) a
        (by linarith [airyRelativeTime_add_one_lt_weight I i ha, (airyRelativeTime_bounds I i).1])
        (2 * airyTimeRank I i)) ∘L airyTagOut I i

/-- The Airy half of the column from the real line to all tagged lines. -/
noncomputable def airyColumnAiryOp (I : Finset ℝ) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) : RealLp →L[ℝ] TaggedLp I :=
  ∑ i : I, airyTagIn I i ∘L
    HilbertSchmidt.kernelOperator (memLp_qrColumnAiry (airyRelativeTime I i + 1) a
      (airyRelativeTime_add_one_lt_weight I i ha))

/-- The bounded Airy column is the composition of its two Hilbert–Schmidt halves. -/
noncomputable def airyToTagged (I : Finset ℝ) (x : I → ℝ) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) : RealLp →L[ℝ] TaggedLp I :=
  airyColumnHeatOp I x a ha ∘L airyColumnAiryOp I a ha

/-- The Airy column is rectangular trace class. -/
theorem airyToTagged_isRectTraceClass (I : Finset ℝ) (x : I → ℝ) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    HilbertSchmidt.IsRectTraceClass (airyToTagged I x a ha) := by
  refine ⟨_, _, ?_, ?_, rfl⟩
  · unfold airyColumnHeatOp
    apply qr_isHilbertSchmidt_finsetSum
    intro i _
    exact (HilbertSchmidt.isHilbertSchmidt_kernelOperator _).sandwich _ _
  · unfold airyColumnAiryOp
    apply qr_isHilbertSchmidt_finsetSum
    intro i _
    exact (HilbertSchmidt.isHilbertSchmidt_kernelOperator _).comp_left' _

/-- The positive-gap row kernel, with exponential weight on the output and polynomial
weight on the input. -/
noncomputable def qrRowHeat (x a r : ℝ) (m : ℕ) : ℝ × ℝ → ℝ :=
  (Prod.snd ⁻¹' Set.Ioi x).indicator (fun p =>
    Real.exp (-a * p.1) * heatKernel r (p.1 - p.2) / (1 + p.2 ^ 2) ^ m)

/-- The positive-gap row kernel is square integrable. -/
theorem memLp_qrRowHeat (x a r : ℝ) (ha : 0 < a) (hr : 0 < r) (m : ℕ) :
    MemLp (qrRowHeat x a r m) 2 (volume.prod volume) := by
  let f := AiryConj.conjugateHeatKernel r a
  let g := (Set.Ioi x).indicator (fun s : ℝ => Real.exp (-a * s))
  have hf : MemLp f 2 volume := by
    simpa only [pow_zero, one_mul] using qr_memLp_poly_conjugateHeat hr a 0
  have hg : MemLp g 2 volume := by
    simpa only [pow_zero, one_mul] using qr_memLp_cut_poly_exp x ha 0
  have hh : MemLp (fun p : ℝ × ℝ => f (p.1 - p.2) * g p.2) 2 (volume.prod volume) :=
    (qr_memLp_mul_prod hf hg).comp_measurePreserving
      (measurePreserving_sub_prod (volume : Measure ℝ) (volume : Measure ℝ))
  have hcont : Continuous (fun p : ℝ × ℝ => heatKernel r (p.1 - p.2)) :=
    (continuous_heatKernel r).comp (continuous_fst.sub continuous_snd)
  have hm : Measurable (qrRowHeat x a r m) := by
    unfold qrRowHeat
    apply Measurable.indicator _ (measurableSet_Ioi.preimage measurable_snd)
    exact ((Real.continuous_exp.measurable.comp (measurable_fst.const_mul (-a))).mul
      hcont.measurable).div (((measurable_snd.pow_const 2).const_add 1).pow_const m)
  refine hh.mono' hm.aestronglyMeasurable (ae_of_all _ fun ⟨s, t⟩ => ?_)
  change ‖qrRowHeat x a r m (s, t)‖ ≤ f (s - t) * g t
  by_cases ht : t ∈ Set.Ioi x
  · have ht' : (s, t) ∈ Prod.snd ⁻¹' Set.Ioi x := ht
    simp only [qrRowHeat, Set.indicator_of_mem ht', Prod.fst, Prod.snd]
    rw [Real.norm_of_nonneg (by positivity [heatKernel_nonneg hr (s - t)])]
    have hden : 1 ≤ (1 + t ^ 2) ^ m := one_le_pow₀ (by linarith [sq_nonneg t])
    calc
      _ ≤ Real.exp (-a * s) * heatKernel r (s - t) :=
        div_le_self (mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg hr _)) hden
      _ = _ := by
        simp only [f, g, Set.indicator_of_mem ht, AiryConj.conjugateHeatKernel]
        rw [show -a * s = -a * (s - t) + -a * t by ring, Real.exp_add]
        ring
  · have ht' : (s, t) ∉ Prod.snd ⁻¹' Set.Ioi x := ht
    simp only [qrRowHeat, Set.indicator_of_notMem ht', norm_zero, g,
      Set.indicator_of_notMem ht, mul_zero, le_rfl]

/-- A bounded multiplier preserves square integrability. -/
theorem memLp_qrMulOp (m : ℝ → ℝ) (hm : Measurable m) (C : ℝ)
    (hb : ∀ t, ‖m t‖ ≤ C) (f : RealLp) :
    MemLp (fun t => m t * f t) 2 (volume : Measure ℝ) :=
  ((Lp.memLp f).norm.const_mul C).mono'
    (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (ae_of_all _ fun t => by
      change ‖m t * f t‖ ≤ C * ‖f t‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _))

/-- A bounded measurable function acts by multiplication on the real-line Hilbert space. -/
noncomputable def qrMulOp (m : ℝ → ℝ) (hm : Measurable m) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖m t‖ ≤ C) : RealLp →L[ℝ] RealLp := by
  let fm (f : RealLp) : ℝ → ℝ := fun t => m t * f t
  have hmem (f : RealLp) : MemLp (fm f) 2 (volume : Measure ℝ) :=
    memLp_qrMulOp m hm C hb f
  let T (f : RealLp) : RealLp := (hmem f).toLp (fm f)
  have hT (f : RealLp) : ⇑(T f) =ᵐ[(volume : Measure ℝ)] fm f := (hmem f).coeFn_toLp
  refine LinearMap.mkContinuous
    { toFun := T, map_add' := ?_, map_smul' := ?_ } C ?_
  · intro f g
    apply Lp.ext
    filter_upwards [hT (f + g), hT f, hT g, Lp.coeFn_add f g, Lp.coeFn_add (T f) (T g)]
      with t hfg hf hg hadd hs
    rw [hfg, hs, Pi.add_apply, hf, hg]
    change m t * (f + g) t = m t * f t + m t * g t
    rw [hadd, Pi.add_apply, mul_add]
  · intro c f
    change T (c • f) = c • T f
    apply Lp.ext
    filter_upwards [hT (c • f), hT f, Lp.coeFn_smul c f, Lp.coeFn_smul c (T f)]
      with t hcf hf hsm hs
    rw [hcf, hs, Pi.smul_apply, hf]
    dsimp [fm]
    rw [hsm, Pi.smul_apply, smul_eq_mul]
    ring
  · intro f
    change ‖T f‖ ≤ C * ‖f‖
    rw [← Real.norm_of_nonneg hC, ← norm_smul]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hT f, Lp.coeFn_smul C f] with t ht hs
    rw [ht, hs, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, Real.norm_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _)

/-- The bounded multiplier has its pointwise interpretation almost everywhere. -/
theorem qrMulOp_apply_ae (m : ℝ → ℝ) (hm : Measurable m) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖m t‖ ≤ C) (f : RealLp) :
    ⇑(qrMulOp m hm C hC hb f) =ᵐ[(volume : Measure ℝ)] fun t => m t * f t :=
  (memLp_qrMulOp m hm C hb f).coeFn_toLp

/-- At the initial time the heat row is a cut exponential multiplier. -/
noncomputable def qrRowZero (x a : ℝ) (m : ℕ) : ℝ → ℝ :=
  (Set.Ioi x).indicator (fun t => Real.exp (-a * t) / (1 + t ^ 2) ^ m)

/-- The zero-gap multiplier is measurable. -/
theorem measurable_qrRowZero (x a : ℝ) (m : ℕ) : Measurable (qrRowZero x a m) := by
  unfold qrRowZero
  apply Measurable.indicator _ measurableSet_Ioi
  exact (Real.continuous_exp.measurable.comp (measurable_id.const_mul (-a))).div
    (((measurable_id.pow_const 2).const_add 1).pow_const m)

/-- The zero-gap multiplier is bounded on its active half-line. -/
theorem norm_qrRowZero_le (x a : ℝ) (ha : 0 ≤ a) (m : ℕ) (t : ℝ) :
    ‖qrRowZero x a m t‖ ≤ Real.exp (-a * x) := by
  unfold qrRowZero
  by_cases ht : t ∈ Set.Ioi x
  · rw [Set.indicator_of_mem ht, Real.norm_of_nonneg (by positivity)]
    refine (div_le_self (Real.exp_pos _).le (one_le_pow₀ (by linarith [sq_nonneg t]))).trans ?_
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.le (neg_nonpos.mpr ha))
  · rw [Set.indicator_of_notMem ht, norm_zero]
    positivity

/-- The row at each tag is a heat kernel for a positive gap and a multiplier at zero gap. -/
noncomputable def airyRowBlock (I : Finset ℝ) (x : I → ℝ) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) (i : I) : RealLp →L[ℝ] RealLp :=
  if h : 0 < airyRelativeTime I i then
    HilbertSchmidt.kernelOperator (memLp_qrRowHeat (x i) a (airyRelativeTime I i)
      (by linarith [airyRelativeTime_add_one_lt_weight I i ha, (airyRelativeTime_bounds I i).1])
      h (2 * airyTimeRank I i))
  else
    qrMulOp (qrRowZero (x i) a (2 * airyTimeRank I i)) (measurable_qrRowZero _ _ _)
      (Real.exp (-a * x i)) (Real.exp_pos _).le
      (norm_qrRowZero_le (x i) a
        (by linarith [airyRelativeTime_add_one_lt_weight I i ha, (airyRelativeTime_bounds I i).1]) _)

/-- The bounded row from tagged space to the real line. -/
noncomputable def airyFromTagged (I : Finset ℝ) (x : I → ℝ) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) : TaggedLp I →L[ℝ] RealLp :=
  ∑ i : I, airyRowBlock I x a ha i ∘L airyTagOut I i

/-- Scalar gauges at the middle coordinate cancel in kernel composition. -/
theorem qr_compKernel_cancel_weight (F G : ℝ × ℝ → ℝ) (l m r : ℝ → ℝ)
    (hm : ∀ z, m z ≠ 0) :
    AiryConj.compKernel (fun p => l p.1 * F p * (m p.2)⁻¹)
      (fun p => m p.1 * G p * r p.2) =
      fun p => l p.1 * AiryConj.compKernel F G p * r p.2 := by
  funext p
  unfold AiryConj.compKernel
  calc
    _ = ∫ z : ℝ, (l p.1 * (F (p.1, z) * G (z, p.2))) * r p.2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        dsimp only
        have hz := hm z
        field_simp
    _ = _ := by rw [integral_mul_const, integral_const_mul]

/-- Heat-kernel composition in two spatial variables. -/
theorem qr_compKernel_heat_heat {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    AiryConj.compKernel (AiryTwoInt.heatKerTwo s) (AiryTwoInt.heatKerTwo t) =
      AiryTwoInt.heatKerTwo (s + t) := by
  funext p
  change (∫ z : ℝ, heatKernel s (p.1 - z) * heatKernel t (z - p.2)) =
    heatKernel (s + t) (p.1 - p.2)
  let H (z : ℝ) := heatKernel s (p.1 - p.2 - z) * heatKernel t z
  calc
    _ = ∫ z : ℝ, H (z - p.2) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by dsimp [H]; rw [show p.1 - p.2 - (z - p.2) = p.1 - z by ring]
    _ = ∫ z : ℝ, H z := integral_sub_right_eq_self H p.2
    _ = _ := AiryConj.heatKernel_semigroup hs ht (p.1 - p.2)

/-- Backward Airy followed by positive heat subtracts the heat time from the Airy time. -/
theorem qr_compKernel_airy_heat {t : ℝ} (ht : 0 < t) (r : ℝ) :
    AiryConj.compKernel (AiryTwoInt.bAiryKer r) (AiryTwoInt.heatKerTwo t) =
      AiryTwoInt.bAiryKer (r - t) := by
  funext p
  have h := congrFun (AiryTwoInt.heatKerTwo_comp_bAiryKer_any ht r) (p.2, p.1)
  change (∫ z : ℝ, heatKernel t (p.2 - z) * backwardAiry r (z + p.1)) =
    backwardAiry (r - t) (p.2 + p.1) at h
  change (∫ z : ℝ, backwardAiry r (p.1 + z) * heatKernel t (z - p.2)) =
    backwardAiry (r - t) (p.1 + p.2)
  rw [add_comm p.1 p.2, ← h]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    dsimp only
    rw [add_comm p.1 z, mul_comm,
      show z - p.2 = -(p.2 - z) by ring, AiryTwoInt.heatKernel_even]

/-- The spatial indicator times the polynomial gauge at a given tag. -/
noncomputable def qrCutWeight (I : Finset ℝ) (x : I → ℝ) (i : I) : ℝ → ℝ :=
  (Set.Ioi (x i)).indicator (airyRankGauge I i)

/-- The spatial indicator times the inverse polynomial gauge at a given tag. -/
noncomputable def qrCutInvWeight (I : Finset ℝ) (x : I → ℝ) (i : I) : ℝ → ℝ :=
  (Set.Ioi (x i)).indicator (fun t => (airyRankGauge I i t)⁻¹)

/-- A forward heat block expressed as a single weighted kernel. -/
noncomputable def qrHeatCutKer (I : Finset ℝ) (x : I → ℝ) (i j : I) (p : ℝ × ℝ) : ℝ :=
  if (i : ℝ) < j then
    qrCutWeight I x i p.1 * heatKernel ((j : ℝ) - i) (p.1 - p.2) * qrCutInvWeight I x j p.2
  else 0

/-- The two heat halves compose to the cut heat kernel. -/
theorem qrHeatLeft_comp_qrHeatRight (I : Finset ℝ) (x : I → ℝ)
    {i j : I} (hij : (i : ℝ) < j) :
    AiryConj.compKernel (qrHeatLeft I x i j) (qrHeatRight I x i j) =
      qrHeatCutKer I x i j := by
  let R (z : ℝ) := (1 + z ^ 2) ^ (airyTimeRank I i + airyTimeRank I j)
  let T := ((j : ℝ) - i) / 2
  have ht : 0 < T := by dsimp [T]; linarith
  have hleft : qrHeatLeft I x i j =
      fun p => qrCutWeight I x i p.1 * AiryTwoInt.heatKerTwo T p * (R p.2)⁻¹ := by
    funext p
    by_cases h : p.1 ∈ Set.Ioi (x i) <;>
      simp [qrHeatLeft, qrCutWeight, qrWeightedHeat, AiryTwoInt.heatKerTwo, R, T, h,
        airyRankGauge, div_eq_mul_inv] <;> ring
  have hright : qrHeatRight I x i j =
      fun p => R p.1 * AiryTwoInt.heatKerTwo T p * qrCutInvWeight I x j p.2 := by
    funext p
    by_cases h : p.2 ∈ Set.Ioi (x j) <;>
      simp [qrHeatRight, qrCutInvWeight, qrWeightedHeat, AiryTwoInt.heatKerTwo, R, T, h,
        airyRankGauge, div_eq_mul_inv] <;> ring
  rw [hleft, hright, qr_compKernel_cancel_weight _ _ _ _ _ (by intro z; dsimp [R]; positivity),
    qr_compKernel_heat_heat ht ht]
  rw [show T + T = (j : ℝ) - i by dsimp [T]; ring]
  funext p
  simp [qrHeatCutKer, hij, AiryTwoInt.heatKerTwo]

/-- The weighted cut heat kernels are square integrable. -/
theorem memLp_qrHeatCutKer (I : Finset ℝ) (x : I → ℝ) (i j : I) :
    MemLp (qrHeatCutKer I x i j) 2 (volume.prod volume) := by
  by_cases h : (i : ℝ) < j
  · have hr := airyTimeRank_lt_of_lt I h
    have hmem := (memLp_qrWeightedHeat (sub_pos.mpr h)
      (show 2 * airyTimeRank I i < 2 * airyTimeRank I j by omega)).indicator
       (((measurableSet_Ioi.preimage measurable_fst).inter
          (measurableSet_Ioi.preimage measurable_snd)).nullMeasurableSet :
            NullMeasurableSet ((Prod.fst ⁻¹' Set.Ioi (x i)) ∩
              (Prod.snd ⁻¹' Set.Ioi (x j))) (volume.prod volume))
    convert hmem using 1
    funext p
    by_cases hp : p.1 ∈ Set.Ioi (x i) <;> by_cases hq : p.2 ∈ Set.Ioi (x j) <;>
      simp [qrHeatCutKer, h, qrCutWeight, qrCutInvWeight, qrWeightedHeat, airyRankGauge,
        hp, hq, div_eq_mul_inv] <;> ring
  · have hz : qrHeatCutKer I x i j = 0 := by
      funext p
      simp [qrHeatCutKer, h]
    rw [hz]
    simp [memLp_iff]

/-- The heat operator and its single-kernel representation agree at each tag pair. -/
theorem airyHeatBlock_eq_kernelOperator (I : Finset ℝ) (x : I → ℝ) (i j : I) :
    airyHeatBlock I x i j = HilbertSchmidt.kernelOperator (memLp_qrHeatCutKer I x i j) := by
  by_cases h : (i : ℝ) < j
  · rw [airyHeatBlock, dif_pos h]
    have hm : MemLp (AiryConj.compKernel (qrHeatLeft I x i j) (qrHeatRight I x i j))
        2 (volume.prod volume) :=
      qrHeatLeft_comp_qrHeatRight I x h ▸ memLp_qrHeatCutKer I x i j
    rw [← AiryTwoInt.kernelOperator_compKernel (memLp_qrHeatLeft I x h) (memLp_qrHeatRight I x h) hm]
    exact AiryTwoInt.kernelOperator_congr (qrHeatLeft_comp_qrHeatRight I x h) hm _
  · rw [airyHeatBlock, dif_neg h]
    symm
    ext1 f
    apply Lp.ext
    filter_upwards [HilbertSchmidt.kernelOperator_apply_ae (memLp_qrHeatCutKer I x i j) f,
      Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with p hp hz
    rw [hp]
    simpa [HilbertSchmidt.kernelIntegralFun, qrHeatCutKer, h] using hz.symm

/-- The column block after cancelling the intermediate gauge. -/
noncomputable def qrColumnKer (I : Finset ℝ) (x : I → ℝ) (i : I) (a : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  qrCutWeight I x i p.1 * backwardAiry (airyRelativeTime I i) (p.1 + p.2) *
    Real.exp (a * p.2)

/-- The two Hilbert–Schmidt factors compose to the weighted Airy column kernel. -/
theorem qrColumnHeat_comp_qrColumnAiry (I : Finset ℝ) (x : I → ℝ) (i : I) (a : ℝ) :
    AiryConj.compKernel (qrColumnHeat (x i) a (2 * airyTimeRank I i))
      (qrColumnAiry (airyRelativeTime I i + 1) a) = qrColumnKer I x i a := by
  let M (z : ℝ) := Real.exp (a * z) * (1 + z ^ 2)⁻¹
  have hm (z : ℝ) : M z ≠ 0 := by
    exact (show 0 < Real.exp (a * z) * (1 + z ^ 2)⁻¹ by positivity).ne'
  have hleft : qrColumnHeat (x i) a (2 * airyTimeRank I i) =
      fun p => qrCutWeight I x i p.1 * AiryTwoInt.heatKerTwo 1 p * (M p.2)⁻¹ := by
    funext p
    by_cases hp : p.1 ∈ Set.Ioi (x i)
    · have hp' : p ∈ Prod.fst ⁻¹' Set.Ioi (x i) := hp
      simp only [qrColumnHeat, qrCutWeight, Set.indicator_of_mem hp, Set.indicator_of_mem hp',
        airyRankGauge, AiryTwoInt.heatKerTwo, M, mul_inv_rev, inv_inv, ← Real.exp_neg]
      ring
    · have hp' : p ∉ Prod.fst ⁻¹' Set.Ioi (x i) := hp
      simp [qrColumnHeat, qrCutWeight, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
  have hright : qrColumnAiry (airyRelativeTime I i + 1) a =
      fun p => M p.1 * AiryTwoInt.bAiryKer (airyRelativeTime I i + 1) p * Real.exp (a * p.2) := by
    funext p
    unfold qrColumnAiry qrAiryProfile AiryTwoInt.bAiryKer M
    rw [mul_add, Real.exp_add]
    ring
  rw [hleft, hright, qr_compKernel_cancel_weight (AiryTwoInt.heatKerTwo 1)
    (AiryTwoInt.bAiryKer (airyRelativeTime I i + 1)) (qrCutWeight I x i) M
    (fun z => Real.exp (a * z)) hm, AiryTwoInt.heatKerTwo_comp_bAiryKer_any one_pos,
    add_sub_cancel_right]
  rfl

/-- The weighted Airy column kernel is square integrable. -/
theorem memLp_qrColumnKer (I : Finset ℝ) (x : I → ℝ) (i : I) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    MemLp (qrColumnKer I x i a) 2 (volume.prod volume) := by
  have hap : 0 < a := by
    linarith [airyRelativeTime_add_one_lt_weight I i ha, (airyRelativeTime_bounds I i).1]
  have hmeasH : Measurable (qrColumnHeat (x i) a (2 * airyTimeRank I i)) := by
    have hc : Continuous (fun p : ℝ × ℝ => heatKernel 1 (p.1 - p.2)) :=
      (continuous_heatKernel 1).comp (continuous_fst.sub continuous_snd)
    unfold qrColumnHeat
    apply Measurable.indicator _ (measurableSet_Ioi.preimage measurable_fst)
    fun_prop
  have hmeasA : Measurable (qrColumnAiry (airyRelativeTime I i + 1) a) := by
    have hAi : Continuous airyAiReal :=
      continuous_iff_continuousAt.mpr fun t => (hasDerivAt_airyAiReal t).continuousAt
    unfold qrColumnAiry qrAiryProfile backwardAiry
    apply Measurable.mul
    · exact ((measurable_fst.pow_const 2).const_add 1).inv
    · fun_prop
  rw [← qrColumnHeat_comp_qrColumnAiry I x i a]
  exact AiryTwoInt.memLp_compKernel hmeasH hmeasA (memLp_qrColumnHeat _ _ hap _)
    (memLp_qrColumnAiry _ _ (airyRelativeTime_add_one_lt_weight I i ha))

/-- The column coordinate is the integral operator of the weighted Airy column kernel. -/
theorem airyTagOut_comp_airyToTagged (I : Finset ℝ) (x : I → ℝ) (i : I) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    airyTagOut I i ∘L airyToTagged I x a ha =
      HilbertSchmidt.kernelOperator (memLp_qrColumnKer I x i a ha) := by
  classical
  have hap : 0 < a := by
    linarith [airyRelativeTime_add_one_lt_weight I i ha, (airyRelativeTime_bounds I i).1]
  have hH := memLp_qrColumnHeat (x i) a hap (2 * airyTimeRank I i)
  have hA := memLp_qrColumnAiry (airyRelativeTime I i + 1) a
    (airyRelativeTime_add_one_lt_weight I i ha)
  have hcomp : MemLp (AiryConj.compKernel (qrColumnHeat (x i) a (2 * airyTimeRank I i))
      (qrColumnAiry (airyRelativeTime I i + 1) a)) 2 (volume.prod volume) := by
    rw [qrColumnHeat_comp_qrColumnAiry]
    exact memLp_qrColumnKer I x i a ha
  have hAiry : airyTagOut I i ∘L airyColumnAiryOp I a ha =
      HilbertSchmidt.kernelOperator hA := by
    unfold airyColumnAiryOp
    rw [ContinuousLinearMap.comp_finsetSum, Finset.sum_eq_single i]
    · simp [← ContinuousLinearMap.comp_assoc, airyTagOut_comp_airyTagIn]
    · intro j _ hj
      simp [← ContinuousLinearMap.comp_assoc, airyTagOut_comp_airyTagIn, Ne.symm hj]
    · simp
  have hHeat : airyTagOut I i ∘L airyColumnHeatOp I x a ha =
      HilbertSchmidt.kernelOperator hH ∘L airyTagOut I i := by
    unfold airyColumnHeatOp
    rw [ContinuousLinearMap.comp_finsetSum, Finset.sum_eq_single i]
    · simp [← ContinuousLinearMap.comp_assoc, airyTagOut_comp_airyTagIn]
    · intro j _ hj
      simp [← ContinuousLinearMap.comp_assoc, airyTagOut_comp_airyTagIn, Ne.symm hj]
    · simp
  unfold airyToTagged
  rw [← ContinuousLinearMap.comp_assoc, hHeat, ContinuousLinearMap.comp_assoc, hAiry,
    ← AiryTwoInt.kernelOperator_compKernel hH hA hcomp]
  exact AiryTwoInt.kernelOperator_congr (qrColumnHeat_comp_qrColumnAiry I x i a) hcomp _

/-- Injecting a line before applying the Airy row selects the corresponding row block. -/
theorem airyFromTagged_comp_airyTagIn (I : Finset ℝ) (x : I → ℝ) (j : I) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    airyFromTagged I x a ha ∘L airyTagIn I j = airyRowBlock I x a ha j := by
  classical
  unfold airyFromTagged
  rw [ContinuousLinearMap.finsetSum_comp, Finset.sum_eq_single j]
  · simp [ContinuousLinearMap.comp_assoc, airyTagOut_comp_airyTagIn]
  · intro i _ hij
    simp [ContinuousLinearMap.comp_assoc, airyTagOut_comp_airyTagIn, hij]
  · simp

/-- Multiplication on the input coordinate gives the corresponding weighted kernel. -/
theorem qr_memLp_kernel_mul_snd {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume))
    (m : ℝ → ℝ) (hm : Measurable m) (C : ℝ) (hb : ∀ t, ‖m t‖ ≤ C) :
    MemLp (fun p => K p * m p.2) 2 (volume.prod volume) := by
  refine (hK.norm.const_mul C).mono' (hK.aestronglyMeasurable.mul
    (hm.comp measurable_snd).aestronglyMeasurable) (ae_of_all _ fun p => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)

/-- Precomposition by a bounded multiplier acts on the second kernel variable. -/
theorem qr_kernelOperator_comp_mul {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume))
    (m : ℝ → ℝ) (hm : Measurable m) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t, ‖m t‖ ≤ C) :
    HilbertSchmidt.kernelOperator hK ∘L qrMulOp m hm C hC hb =
      HilbertSchmidt.kernelOperator (qr_memLp_kernel_mul_snd hK m hm C hb) := by
  ext1 f
  apply Lp.ext
  filter_upwards [HilbertSchmidt.kernelOperator_apply_ae hK (qrMulOp m hm C hC hb f),
    HilbertSchmidt.kernelOperator_apply_ae (qr_memLp_kernel_mul_snd hK m hm C hb) f]
    with s hs ht
  rw [ContinuousLinearMap.comp_apply, hs, ht]
  apply integral_congr_ae
  filter_upwards [qrMulOp_apply_ae m hm C hC hb f] with t ht
  change K (s, t) * qrMulOp m hm C hC hb f t = K (s, t) * m t * f t
  rw [ht, mul_assoc]

/-- The Airy part of the extended kernel, with both spatial cuts and rank weights. -/
noncomputable def qrPoleCutKer (I : Finset ℝ) (x : I → ℝ) (i j : I) (p : ℝ × ℝ) : ℝ :=
  qrCutWeight I x i p.1 * backwardAiry ((i : ℝ) - j) (p.1 + p.2) *
    qrCutInvWeight I x j p.2

/-- Composing the column with the positive-gap row cancels the exponential gauge. -/
theorem qrColumnKer_comp_qrRowHeat (I : Finset ℝ) (x : I → ℝ) (i j : I)
    (a : ℝ) (hj : 0 < airyRelativeTime I j) :
    AiryConj.compKernel (qrColumnKer I x i a)
      (qrRowHeat (x j) a (airyRelativeTime I j) (2 * airyTimeRank I j)) = qrPoleCutKer I x i j := by
  let M (z : ℝ) := Real.exp (-a * z)
  have hleft : qrColumnKer I x i a =
      fun p => qrCutWeight I x i p.1 * AiryTwoInt.bAiryKer (airyRelativeTime I i) p * (M p.2)⁻¹ := by
    funext p
    simp [M, qrColumnKer, AiryTwoInt.bAiryKer, ← Real.exp_neg]
  have hright : qrRowHeat (x j) a (airyRelativeTime I j) (2 * airyTimeRank I j) =
      fun p => M p.1 * AiryTwoInt.heatKerTwo (airyRelativeTime I j) p * qrCutInvWeight I x j p.2 := by
    funext p
    by_cases ht : p.2 ∈ Set.Ioi (x j)
    · have ht' : p ∈ Prod.snd ⁻¹' Set.Ioi (x j) := ht
      simp [M, qrRowHeat, qrCutInvWeight, ht, ht', airyRankGauge, AiryTwoInt.heatKerTwo, div_eq_mul_inv]
    · have ht' : p ∉ Prod.snd ⁻¹' Set.Ioi (x j) := ht
      simp [qrRowHeat, qrCutInvWeight, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']
  rw [hleft, hright, qr_compKernel_cancel_weight (AiryTwoInt.bAiryKer (airyRelativeTime I i))
    (AiryTwoInt.heatKerTwo (airyRelativeTime I j)) (qrCutWeight I x i) M (qrCutInvWeight I x j)
    (fun z => (Real.exp_pos (-a * z)).ne'), qr_compKernel_airy_heat hj]
  have ht : airyRelativeTime I i - airyRelativeTime I j = (i : ℝ) - j := by
    unfold airyRelativeTime
    ring
  rw [ht]
  rfl

/-- At zero relative time the exponential gauge cancels by pointwise multiplication. -/
theorem qrColumnKer_mul_qrRowZero (I : Finset ℝ) (x : I → ℝ) (i j : I)
    (a : ℝ) (hj : airyRelativeTime I j = 0) :
    (fun p : ℝ × ℝ => qrColumnKer I x i a p *
      qrRowZero (x j) a (2 * airyTimeRank I j) p.2) = qrPoleCutKer I x i j := by
  have ht : airyRelativeTime I i = (i : ℝ) - j := by
    unfold airyRelativeTime at *
    linarith
  funext p
  by_cases hp : p.2 ∈ Set.Ioi (x j)
  · simp only [qrColumnKer, qrRowZero, qrPoleCutKer, qrCutInvWeight, ht,
      Set.indicator_of_mem hp, airyRankGauge]
    have h := Real.exp_neg (a * p.2)
    rw [show -a * p.2 = -(a * p.2) by ring, h]
    field_simp
  · simp [qrColumnKer, qrRowZero, qrPoleCutKer, qrCutInvWeight, Set.indicator_of_notMem hp]

/-- The weighted column-row composition is represented by the pole cut kernel. -/
theorem qrPoleCutKer_operator (I : Finset ℝ) (x : I → ℝ) (i j : I) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    ∃ h : MemLp (qrPoleCutKer I x i j) 2 (volume.prod volume),
      HilbertSchmidt.kernelOperator (memLp_qrColumnKer I x i a ha) ∘L airyRowBlock I x a ha j =
        HilbertSchmidt.kernelOperator h := by
  let Q := qrColumnKer I x i a
  have hQ := memLp_qrColumnKer I x i a ha
  have hapos : 0 < a := by
    linarith [airyRelativeTime_add_one_lt_weight I j ha, (airyRelativeTime_bounds I j).1]
  by_cases hj : 0 < airyRelativeTime I j
  · let R := qrRowHeat (x j) a (airyRelativeTime I j) (2 * airyTimeRank I j)
    have hR := memLp_qrRowHeat (x j) a (airyRelativeTime I j) hapos hj (2 * airyTimeRank I j)
    have hQm : Measurable Q := by
      have hm : Measurable (qrCutWeight I x i) := by
        unfold qrCutWeight airyRankGauge
        apply Measurable.indicator _ measurableSet_Ioi
        fun_prop
      have hAi : Continuous airyAiReal :=
        continuous_iff_continuousAt.mpr fun s => (hasDerivAt_airyAiReal s).continuousAt
      unfold Q qrColumnKer backwardAiry
      apply Measurable.mul (Measurable.mul (hm.comp measurable_fst) ?_) (by fun_prop)
      fun_prop
    have hRm : Measurable R := by
      have hheat : Continuous (fun p : ℝ × ℝ => heatKernel (airyRelativeTime I j) (p.1 - p.2)) :=
        (continuous_heatKernel _).comp (continuous_fst.sub continuous_snd)
      unfold R qrRowHeat
      apply Measurable.indicator _ (measurableSet_Ioi.preimage measurable_snd)
      exact ((Real.continuous_exp.measurable.comp (measurable_fst.const_mul (-a))).mul
        hheat.measurable).div (((measurable_snd.pow_const 2).const_add 1).pow_const _)
    have hc := AiryTwoInt.memLp_compKernel hQm hRm hQ hR
    have he := qrColumnKer_comp_qrRowHeat I x i j a hj
    let hp : MemLp (qrPoleCutKer I x i j) 2 (volume.prod volume) := he ▸ hc
    refine ⟨hp, ?_⟩
    rw [airyRowBlock, dite_eq_left hj]
    exact (AiryTwoInt.kernelOperator_compKernel hQ hR hc).symm.trans
      (AiryTwoInt.kernelOperator_congr he _ _)
  · let m := qrRowZero (x j) a (2 * airyTimeRank I j)
    let C := Real.exp (-a * x j)
    have hm := measurable_qrRowZero (x j) a (2 * airyTimeRank I j)
    have hb := norm_qrRowZero_le (x j) a hapos.le (2 * airyTimeRank I j)
    have hz : airyRelativeTime I j = 0 := le_antisymm (le_of_not_gt hj) (airyRelativeTime_bounds I j).1
    have hc := qr_memLp_kernel_mul_snd hQ m hm C hb
    have he := qrColumnKer_mul_qrRowZero I x i j a hz
    let hp : MemLp (qrPoleCutKer I x i j) 2 (volume.prod volume) := he ▸ hc
    refine ⟨hp, ?_⟩
    rw [airyRowBlock, dite_eq_right hj]
    exact (qr_kernelOperator_comp_mul hQ m hm C (Real.exp_pos _).le hb).trans
      (AiryTwoInt.kernelOperator_congr he _ _)

/-- A finite sum of measures preserves square integrability of a fixed function. -/
theorem qr_memLp_sum_measure {X ι : Type*} [MeasurableSpace X] [Finite ι]
    (f : X → ℝ) (μ : ι → Measure X) (h : ∀ i, MemLp f 2 (μ i)) :
    MemLp f 2 (Measure.sum μ) := by
  have hm := aestronglyMeasurable_sum_measure_iff.mpr (fun i => (h i).aestronglyMeasurable)
  apply (memLp_two_iff_integrable_sq hm).2
  exact integrable_sum_measure
    (fun i => (memLp_two_iff_integrable_sq (h i).aestronglyMeasurable).1 (h i))
    Summable.of_finite

/-- The product measure is the finite sum of the two-tag pushforwards. -/
theorem airySiteMeasure_prod_eq_sum (I : Finset ℝ) :
    (airySiteMeasure I).prod (airySiteMeasure I) =
      Measure.sum (fun ij : I × I => Measure.map
        (fun p : ℝ × ℝ => ((ij.1, p.1), (ij.2, p.2))) (volume.prod volume)) := by
  have h : airySiteMeasure I = Measure.sum (fun i : I => Measure.map (Prod.mk i) volume) := by
    unfold airySiteMeasure
    simp only [Measure.count, Measure.prod_sum_left, Measure.dirac_prod]
  rw [h, Measure.prod_sum]
  apply congrArg Measure.sum
  funext ij
  rw [Measure.map_prod_map _ _ measurable_prodMk_left measurable_prodMk_left]
  rfl

/-- Square integrability of all blocks implies square integrability on tagged space. -/
theorem memLp_airyTaggedKernel (I : Finset ℝ) (K : (I × ℝ) × (I × ℝ) → ℝ)
    (h : ∀ i j : I, MemLp (fun p : ℝ × ℝ => K ((i, p.1), (j, p.2)))
      2 (volume.prod volume)) :
    MemLp K 2 ((airySiteMeasure I).prod (airySiteMeasure I)) := by
  rw [airySiteMeasure_prod_eq_sum]
  apply qr_memLp_sum_measure
  intro ij
  exact (((measurableEmbedding_prodMk_left ij.1).prodMap
    (measurableEmbedding_prodMk_left ij.2)).memLp_map_measure_iff).2 (h ij.1 ij.2)

/-- The literal cut extended kernel is the difference of the Airy and heat blocks. -/
theorem airyRankCutKer_eq_qrPole_sub_heat (I : Finset ℝ) (x : I → ℝ) (i j : I)
    (p : ℝ × ℝ) :
    airyRankCutKer I x (i, p.1) (j, p.2) = qrPoleCutKer I x i j p - qrHeatCutKer I x i j p := by
  have hAiry : backwardAiry ((i : ℝ) - j) (p.1 + p.2) =
      Real.exp (((j : ℝ) - i) * (p.1 + p.2) + (2 / 3) * ((j : ℝ) - i) ^ 3) *
        airyAiReal (p.1 + p.2 + ((j : ℝ) - i) ^ 2) := by
    unfold backwardAiry
    congr 2 <;> ring
  by_cases hp : x i < p.1 <;> by_cases hq : x j < p.2 <;> by_cases hij : (i : ℝ) < j <;>
    simp [airyRankCutKer, qrPoleCutKer, qrHeatCutKer, qrCutWeight, qrCutInvWeight,
      airyExtendedKer, Set.mem_Ioi, hp, hq, hij, hAiry, div_eq_mul_inv] <;> ring

/-- The cut, rank-gauged extended Airy kernel is square integrable on tagged space. -/
theorem airyRankCutKer_memLp (I : Finset ℝ) (x : I → ℝ) :
    MemLp (fun p : (I × ℝ) × (I × ℝ) => airyRankCutKer I x p.1 p.2)
      2 ((airySiteMeasure I).prod (airySiteMeasure I)) := by
  apply memLp_airyTaggedKernel
  intro i j
  simp_rw [airyRankCutKer_eq_qrPole_sub_heat]
  obtain ⟨hp, _⟩ := qrPoleCutKer_operator I x i j (airyTimeSpan I + 2) le_rfl
  exact hp.sub (memLp_qrHeatCutKer I x i j)

/-- The rank-gauged cut extended Airy integral operator. -/
noncomputable def airyExtendedOp (I : Finset ℝ) (x : I → ℝ) : TaggedLp I →L[ℝ] TaggedLp I :=
  HilbertSchmidt.kernelOperator (airyRankCutKer_memLp I x)

/-- The tag blocks of a tagged integral operator are the corresponding real-line
integral operators. -/
theorem airyTagOut_comp_kernelOperator_comp_airyTagIn
    (I : Finset ℝ) (K : (I × ℝ) × (I × ℝ) → ℝ)
    (hK : MemLp K 2 ((airySiteMeasure I).prod (airySiteMeasure I))) (i j : I)
    (hij : MemLp (fun p : ℝ × ℝ => K ((i, p.1), (j, p.2))) 2 (volume.prod volume)) :
    airyTagOut I i ∘L HilbertSchmidt.kernelOperator hK ∘L airyTagIn I j =
      HilbertSchmidt.kernelOperator hij := by
  ext1 f
  apply Lp.ext
  let v := airyTagIn I j f
  have hk := (ae_airySiteMeasure_iff I _).1 (HilbertSchmidt.kernelOperator_apply_ae hK v) i
  have hv := airyTagIn_apply_ae I j f
  filter_upwards [airyTagOut_apply_ae I i (HilbertSchmidt.kernelOperator hK v),
    HilbertSchmidt.kernelOperator_apply_ae hij f, hk] with s hs hsmall hbig
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change airyTagOut I i (HilbertSchmidt.kernelOperator hK v) s = _
  rw [hs, hsmall, hbig]
  change (∫ p, K ((i, s), p) * v p ∂(airySiteMeasure I)) = ∫ t, K ((i, s), (j, t)) * f t
  let S : Set (I × ℝ) := {j} ×ˢ Set.univ
  have hS : MeasurableSet S := (measurableSet_singleton _).prod MeasurableSet.univ
  calc
    _ = ∫ p, S.indicator (fun q => K ((i, s), q) * f q.2) p ∂(airySiteMeasure I) := by
      apply integral_congr_ae
      filter_upwards [hv] with p hp
      change v p = S.indicator (⇑f ∘ Prod.snd) p at hp
      rw [hp]
      by_cases hin : p ∈ S <;> simp [hin, Function.comp_apply]
    _ = _ := by
      rw [integral_indicator hS, ← map_airyTag I j, (measurableEmbedding_prodMk_left j).integral_map]

/-- Equality of all real-line blocks determines a tagged operator. -/
theorem qr_eq_of_tagged_blocks (I : Finset ℝ) (A B : TaggedLp I →L[ℝ] TaggedLp I)
    (h : ∀ i j : I, airyTagOut I i ∘L A ∘L airyTagIn I j =
      airyTagOut I i ∘L B ∘L airyTagIn I j) : A = B := by
  have hrow (i : I) : airyTagOut I i ∘L A = airyTagOut I i ∘L B := by
    calc
      _ = ∑ j : I, (airyTagOut I i ∘L A ∘L airyTagIn I j) ∘L airyTagOut I j := by
        simp only [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_finsetSum,
          sum_airyTagIn_comp_airyTagOut, ContinuousLinearMap.comp_id]
      _ = ∑ j : I, (airyTagOut I i ∘L B ∘L airyTagIn I j) ∘L airyTagOut I j := by
        simp_rw [h]
      _ = _ := by
        simp only [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_finsetSum,
          sum_airyTagIn_comp_airyTagOut, ContinuousLinearMap.comp_id]
  calc
    A = ∑ i : I, airyTagIn I i ∘L (airyTagOut I i ∘L A) := by
      simp only [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.finsetSum_comp,
        sum_airyTagIn_comp_airyTagOut, ContinuousLinearMap.id_comp]
    _ = ∑ i : I, airyTagIn I i ∘L (airyTagOut I i ∘L B) := by simp_rw [hrow]
    _ = B := by
      simp only [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.finsetSum_comp,
        sum_airyTagIn_comp_airyTagOut, ContinuousLinearMap.id_comp]

/-- Subtraction of square-integrable kernels corresponds to subtraction of their operators. -/
theorem qr_kernelOperator_sub {K L : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume))
    (hL : MemLp L 2 (volume.prod volume)) :
    HilbertSchmidt.kernelOperator (hK.sub hL) =
      HilbertSchmidt.kernelOperator hK - HilbertSchmidt.kernelOperator hL := by
  ext1 f
  apply Lp.ext
  filter_upwards [HilbertSchmidt.kernelOperator_apply_ae (hK.sub hL) f,
    HilbertSchmidt.kernelOperator_apply_ae hK f, HilbertSchmidt.kernelOperator_apply_ae hL f,
    Lp.coeFn_sub (HilbertSchmidt.kernelOperator hK f) (HilbertSchmidt.kernelOperator hL f),
    HilbertSchmidt.integrable_kernelFun_slice_ae hK f,
    HilbertSchmidt.integrable_kernelFun_slice_ae hL f] with s hsub hk hl hLp hintK hintL
  rw [ContinuousLinearMap.sub_apply, hLp, Pi.sub_apply, hsub, hk, hl]
  change (∫ t, (K (s, t) - L (s, t)) * f t) =
    (∫ t, K (s, t) * f t) - ∫ t, L (s, t) * f t
  simp_rw [sub_mul]
  exact integral_sub hintK hintL

/-- The extended operator is the Airy column-row product minus the upper heat operator. -/
theorem airyExtendedOp_eq_colRow_sub (I : Finset ℝ) (x : I → ℝ) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    airyExtendedOp I x = airyToTagged I x a ha ∘L airyFromTagged I x a ha -
      airyHeatUpper I x := by
  classical
  apply qr_eq_of_tagged_blocks
  intro i j
  obtain ⟨hp, hPole⟩ := qrPoleCutKer_operator I x i j a ha
  have hh := memLp_qrHeatCutKer I x i j
  have he : (fun p : ℝ × ℝ => airyRankCutKer I x (i, p.1) (j, p.2)) =
      qrPoleCutKer I x i j - qrHeatCutKer I x i j :=
    funext (airyRankCutKer_eq_qrPole_sub_heat I x i j)
  have hm : MemLp (fun p : ℝ × ℝ => airyRankCutKer I x (i, p.1) (j, p.2))
      2 (volume.prod volume) := he.symm ▸ hp.sub hh
  unfold airyExtendedOp
  rw [airyTagOut_comp_kernelOperator_comp_airyTagIn I _ _ i j hm,
    AiryTwoInt.kernelOperator_congr he hm (hp.sub hh), qr_kernelOperator_sub]
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  congr 1
  · rw [ContinuousLinearMap.comp_assoc (airyToTagged I x a ha),
      airyFromTagged_comp_airyTagIn, ← ContinuousLinearMap.comp_assoc (airyTagOut I i),
      airyTagOut_comp_airyToTagged]
    exact hPole.symm
  · unfold airyHeatUpper
    rw [← ContinuousLinearMap.comp_assoc (airyTagOut I i),
      airyTagOut_comp_airyTaggedBlocks, ContinuousLinearMap.finsetSum_comp, Finset.sum_eq_single j]
    · rw [ContinuousLinearMap.comp_assoc, airyTagOut_comp_airyTagIn, ite_eq_left rfl,
        ContinuousLinearMap.comp_id, airyHeatBlock_eq_kernelOperator]
    · intro l _ hl
      rw [ContinuousLinearMap.comp_assoc, airyTagOut_comp_airyTagIn, ite_eq_right hl,
        ContinuousLinearMap.comp_zero]
    · simp

/-- The extended operator is trace class. -/
theorem airyExtendedOp_isTraceClass (I : Finset ℝ) (x : I → ℝ) :
    HilbertSchmidt.IsTraceClass (airyExtendedOp I x) := by
  rw [airyExtendedOp_eq_colRow_sub I x (airyTimeSpan I + 2) le_rfl]
  exact ((airyToTagged_isRectTraceClass I x _ le_rfl).isTraceClass_comp _).sub
    (airyHeatUpper_isTraceClass I x)

/-- The cut extended kernel's Fredholm series is the determinant of the
single-space QR operator. -/
theorem airyExtendedSeries_eq_qrDet (I : Finset ℝ) (x : I → ℝ) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    kernelFredholmSeries (airySiteMeasure I) (airyRankCutKer I x) =
      HilbertSchmidt.fredholmDet
        (airyFromTagged I x a ha ∘L airyUpperInv I x ∘L airyToTagged I x a ha) 1 := by
  have hbridge := kernelFredholmSeries_eq_fredholmDet_of_cut I x
    (airyRankCutKer I x) (airyRankCutKer_memLp I x)
    (airyRankCutKer_supported I x) (airyRankCutKer_continuous I x)
    (airyRankCutKer_rowEnvelope I x) (airyExtendedOp_isTraceClass I x)
  have hL : HilbertSchmidt.IsTraceClass (-airyHeatUpper I x) := by
    simpa using HilbertSchmidt.isTraceClass_zero.sub (airyHeatUpper_isTraceClass I x)
  have hdet := fredholmDet_colRow_sub_eq (airyHeatUpper I x) (airyToTagged I x a ha)
    (airyFromTagged I x a ha) (I.card + 1) (airyHeatUpper_nilpotent I x)
    hL (fredholmDet_neg_airyHeatUpper I x) (airyToTagged_isRectTraceClass I x a ha)
  exact hbridge.trans ((congrArg (fun A => HilbertSchmidt.fredholmDet A 1)
    (airyExtendedOp_eq_colRow_sub I x a ha)).trans hdet)

/-- The empty time case agrees with the existing path CDF. -/
theorem airyExtendedSeries_empty (x : (∅ : Finset ℝ) → ℝ) :
    kernelFredholmSeries (airySiteMeasure ∅) (airyRankCutKer ∅ x) = airy1FinCdf ∅ x := by
  rw [kernelFredholmSeries_of_isEmpty, airy1FinCdf_empty]

/-- The part of the hitting kernel assigned to a bad site at the starting time,
with good sites at all later times. -/
noncomputable def qrHitPiece (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (p : ℝ × ℝ) : ℝ :=
  (Set.Ioi e.1).indicator (fun p' : ℝ => match L with
    | [] => heatKernel e.2 (p' - p.2)
    | y :: ys => AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (lamKerN y ys) (p', p.2)) p.1

/-- The hitting kernel divides into its starting piece and the unrestricted
propagation of the later hitting kernel. -/
theorem hitKerN_eq_qrHitPiece_add (e y : ℝ × ℝ) (L : List (ℝ × ℝ))
    (he : 0 < e.2) (hy : 0 < y.2) (hL : ∀ z ∈ L, 0 < z.2) :
    hitKerN e (y :: L) = qrHitPiece e (y :: L) +
      AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (hitKerN y L) := by
  funext p
  rcases p with ⟨u, v⟩
  by_cases hu : u ≤ e.1
  · have hnot : u ∉ Set.Ioi e.1 := not_lt_of_ge hu
    change hitKerN e (y :: L) (u, v) = qrHitPiece e (y :: L) (u, v) +
      AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (hitKerN y L) (u, v)
    rw [qrHitPiece, Set.indicator_of_notMem hnot, zero_add]
    exact hitKerN_cons_eq_integral he hy hL hu v
  · have hpos : u ∈ Set.Ioi e.1 := lt_of_not_ge hu
    have hneg : u ∉ Set.Iic e.1 := hu
    have hS := gapSum_pos L y hy hL
    obtain ⟨hLm, hL0, hLb⟩ := lamKerN_props L y hy hL
    have h1 := integrable_heat_mul_heat he hS u v
    have h2 : Integrable (fun w : ℝ => heatKernel e.2 (u - w) * lamKerN y L (w, v)) :=
      AiryTwoInt.integrable_pair_mul_of_heatKernel_le he hS (AiryTwoInt.measurable_heatKerTwo _)
        hLm (fun a b => AiryTwoInt.heatKerTwo_abs_le_self he (a, b))
        (fun a b => by rw [abs_of_nonneg (hL0 _)]; exact hLb (a, b)) u v
    change hitKerN e (y :: L) (u, v) = qrHitPiece e (y :: L) (u, v) +
      AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (hitKerN y L) (u, v)
    simp only [hitKerN, lamKerN, qrHitPiece, Set.indicator_of_mem hpos, Set.indicator_of_notMem hneg,
      Set.indicator_of_notMem, zero_mul, sub_zero, gapSum, AiryConj.compKernel,
      AiryTwoInt.heatKerTwo]
    simp_rw [mul_sub]
    rw [integral_sub h1 h2, AiryTwoInt.heatKernel_conv he hS]
    ring

/-- The last hitting kernel is its single starting piece. -/
theorem hitKerN_nil_eq_qrHitPiece (e : ℝ × ℝ) : hitKerN e [] = qrHitPiece e [] := by
  funext p
  rw [hitKerN_nil, hitKer1_eq]
  by_cases hp : p.1 ∈ Set.Ioi e.1 <;> simp [qrHitPiece, hp]

/-- Each starting piece is measurable and bounded between zero and the free heat kernel. -/
theorem qrHitPiece_props (e : ℝ × ℝ) (L : List (ℝ × ℝ))
    (he : 0 < e.2) (hL : ∀ z ∈ L, 0 < z.2) :
    Measurable (qrHitPiece e L) ∧
      ∀ p, 0 ≤ qrHitPiece e L p ∧ qrHitPiece e L p ≤ heatKernel (gapSum e L) (p.1 - p.2) := by
  cases L with
  | nil =>
    have h : qrHitPiece e [] =
        (Prod.fst ⁻¹' Set.Ioi e.1).indicator (AiryTwoInt.heatKerTwo e.2) := by
      funext p
      by_cases hp : p.1 ∈ Set.Ioi e.1 <;> simp [qrHitPiece, AiryTwoInt.heatKerTwo, hp]
    rw [h]
    refine ⟨(AiryTwoInt.measurable_heatKerTwo _).indicator
      (measurableSet_Ioi.preimage measurable_fst), ?_⟩
    intro p
    by_cases hp : p.1 ∈ Set.Ioi e.1 <;>
      simp [hp, AiryTwoInt.heatKerTwo, gapSum, heatKernel_nonneg he]
  | cons e' L =>
    have hy := hL e' List.mem_cons_self
    have hz := fun z h => hL z (List.mem_cons_of_mem e' h)
    obtain ⟨hm, h0, hb⟩ := lamKerN_props L e' hy hz
    have ht := gapSum_pos L e' hy hz
    let H := AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (lamKerN e' L)
    have heq : qrHitPiece e (e' :: L) = (Prod.fst ⁻¹' Set.Ioi e.1).indicator H := by
      funext p
      by_cases hp : p.1 ∈ Set.Ioi e.1 <;> simp [qrHitPiece, hp, H]
    rw [heq]
    refine ⟨(AiryTwoInt.measurable_compKernel (AiryTwoInt.measurable_heatKerTwo _) hm).indicator
      (measurableSet_Ioi.preimage measurable_fst), ?_⟩
    rintro ⟨u, v⟩
    by_cases hp : u ∈ Set.Ioi e.1
    · have hmem : (u, v) ∈ Prod.fst ⁻¹' Set.Ioi e.1 := hp
      rw [Set.indicator_of_mem hmem]
      have hInt : Integrable (fun z : ℝ => heatKernel e.2 (u - z) * lamKerN e' L (z, v)) :=
        AiryTwoInt.integrable_pair_mul_of_heatKernel_le he ht (AiryTwoInt.measurable_heatKerTwo _) hm
          (fun a b => AiryTwoInt.heatKerTwo_abs_le_self he (a, b))
          (fun a b => by rw [abs_of_nonneg (h0 _)]; exact hb (a, b)) u v
      constructor
      · exact integral_nonneg fun z => mul_nonneg (heatKernel_nonneg he _) (h0 _)
      · change (∫ z, heatKernel e.2 (u - z) * lamKerN e' L (z, v)) ≤
          heatKernel (e.2 + gapSum e' L) (u - v)
        rw [← AiryTwoInt.heatKernel_conv he ht]
        exact integral_mono hInt (integrable_heat_mul_heat he ht _ _)
          (fun z => mul_le_mul_of_nonneg_left (hb (z, v)) (heatKernel_nonneg he _))
    · have hn : (u, v) ∉ Prod.fst ⁻¹' Set.Ioi e.1 := hp
      rw [Set.indicator_of_notMem hn]
      exact ⟨le_rfl, heatKernel_nonneg (add_pos he ht) _⟩

/-- Propagation of a kernel by free heat, with the identity at zero gap. -/
noncomputable def qrHeatPropagate (s : ℝ) (K : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  if 0 < s then AiryConj.compKernel (AiryTwoInt.heatKerTwo s) K else K

/-- Positive heat propagation preserves measurability, nonnegativity and the free
heat bound with the propagation time added. -/
theorem qrHeatPropagate_props {s τ : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    {K : ℝ × ℝ → ℝ} (hm : Measurable K)
    (hb : ∀ p, 0 ≤ K p ∧ K p ≤ heatKernel τ (p.1 - p.2)) :
    Measurable (qrHeatPropagate s K) ∧
      ∀ p, 0 ≤ qrHeatPropagate s K p ∧ qrHeatPropagate s K p ≤ heatKernel (s + τ) (p.1 - p.2) := by
  by_cases h : 0 < s
  · simp only [qrHeatPropagate, ite_eq_left h]
    refine ⟨AiryTwoInt.measurable_compKernel (AiryTwoInt.measurable_heatKerTwo _) hm, ?_⟩
    rintro ⟨u, v⟩
    have hI := AiryTwoInt.integrable_pair_mul_of_heatKernel_le h hτ
      (AiryTwoInt.measurable_heatKerTwo _) hm
      (fun a b => AiryTwoInt.heatKerTwo_abs_le_self h (a, b))
      (fun a b => by rw [abs_of_nonneg (hb _).1]; exact (hb (a, b)).2) u v
    constructor
    · exact integral_nonneg fun z => mul_nonneg (heatKernel_nonneg h _) (hb _).1
    · change (∫ z, heatKernel s (u - z) * K (z, v)) ≤ heatKernel (s + τ) (u - v)
      rw [← AiryTwoInt.heatKernel_conv h hτ]
      exact integral_mono hI (integrable_heat_mul_heat h hτ _ _)
        (fun z => mul_le_mul_of_nonneg_left (hb (z, v)).2 (heatKernel_nonneg h _))
  · have hz : s = 0 := le_antisymm (le_of_not_gt h) hs
    subst s
    simpa [qrHeatPropagate] using And.intro hm hb

/-- Heat propagation adds successive time gaps on heat-bounded kernels. -/
theorem qrHeatPropagate_add {s t τ : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hτ : 0 < τ)
    {K : ℝ × ℝ → ℝ} (hm : Measurable K)
    (hb : ∀ p, 0 ≤ K p ∧ K p ≤ heatKernel τ (p.1 - p.2)) :
    qrHeatPropagate (s + t) K = qrHeatPropagate s (qrHeatPropagate t K) := by
  rcases hs.eq_or_lt with hs | hs
  · subst s
    simp [qrHeatPropagate]
  rcases ht.eq_or_lt with ht | ht
  · subst t
    simp [qrHeatPropagate, hs]
  simp only [qrHeatPropagate, ite_eq_left hs, ite_eq_left ht, ite_eq_left (add_pos hs ht)]
  rw [← qr_compKernel_heat_heat hs ht]
  funext p
  have hmeas : Measurable (fun z : ℝ => K (z, p.2)) :=
    hm.comp (measurable_id.prodMk measurable_const)
  have hbound (z : ℝ) : |K (z, p.2)| ≤ c0 τ * Real.exp (0 * |z|) := by
    rw [abs_of_nonneg (hb _).1, zero_mul, Real.exp_zero, mul_one]
    exact (hb _).2.trans (AiryTwoInt.heatKernel_le hτ _)
  exact AiryTwoInt.compKernel_assoc p.1 p.2
    (AiryTwoInt.integrable_uncurry_of_abs_le hs ht (by norm_num : (0 : ℝ) ≤ 0) p.1
      (AiryTwoInt.measurable_heatKerTwo s) (fun z => AiryTwoInt.heatKerTwo_abs_le_self hs _)
      (AiryTwoInt.measurable_heatKerTwo t) (fun z w => AiryTwoInt.heatKerTwo_abs_le_self ht _)
      hmeas _ hbound)

/-- A finite list of heat-bounded kernels can be propagated term by term. -/
theorem qrHeatPropagate_list_sum (s : ℝ) (l : List (ℝ × ℝ → ℝ))
    (h : ∀ K ∈ l, Measurable K ∧ ∃ τ : ℝ, 0 < τ ∧
      ∀ p, 0 ≤ K p ∧ K p ≤ heatKernel τ (p.1 - p.2)) :
    qrHeatPropagate s l.sum = (l.map (qrHeatPropagate s)).sum := by
  by_cases hs : 0 < s
  · have hi (K : ℝ × ℝ → ℝ) (hK : K ∈ l) (u v : ℝ) :
        Integrable (fun z => heatKernel s (u - z) * K (z, v)) := by
      obtain ⟨hm, τ, hτ, hb⟩ := h K hK
      exact AiryTwoInt.integrable_pair_mul_of_heatKernel_le hs hτ
        (AiryTwoInt.measurable_heatKerTwo _) hm
        (fun _ _ => AiryTwoInt.heatKerTwo_abs_le_self hs _)
        (fun a b => by rw [abs_of_nonneg (hb (a, b)).1]; exact (hb (a, b)).2) u v
    clear h
    induction l with
    | nil =>
      funext p
      simp [qrHeatPropagate, hs, AiryConj.compKernel]
    | cons K l ih =>
      have htail (u v : ℝ) :
          Integrable (fun z => heatKernel s (u - z) * l.sum (z, v)) := by
        have hI (K : ℝ × ℝ → ℝ) (hK : K ∈ l) :=
          hi K (List.mem_cons_of_mem _ hK) u v
        clear hi ih
        induction l with
        | nil => simp
        | cons J l ih =>
          simp only [List.sum_cons, Pi.add_apply, mul_add]
          exact (hI J (List.mem_cons_self)).add
            (ih fun j hj => hI j (List.mem_cons_of_mem _ hj))
      funext p
      rw [List.sum_cons, List.map_cons, List.sum_cons, Pi.add_apply,
        ← ih (fun J hj => hi J (List.mem_cons_of_mem _ hj))]
      simp only [qrHeatPropagate, ite_eq_left hs, AiryConj.compKernel,
        AiryTwoInt.heatKerTwo, Pi.add_apply, mul_add]
      rw [integral_add (hi K List.mem_cons_self p.1 p.2) (htail p.1 p.2)]
  · have he : qrHeatPropagate s = id := by funext K; simp [qrHeatPropagate, hs]
    rw [he, List.map_id, id_eq]

/-- Starting pieces indexed by their chronological times. -/
noncomputable def qrHitPieces (lev : ℝ → ℝ) : List ℝ → List (ℝ × (ℝ × ℝ → ℝ))
  | [] => []
  | t :: ts =>
    (t, match fddEntries lev (t :: ts) with
      | [] => 0
      | e :: L => qrHitPiece e L) :: qrHitPieces lev ts

/-- The propagation list preserves exactly the original chronological indices. -/
theorem qrHitPieces_times (lev : ℝ → ℝ) (ts : List ℝ) :
    (qrHitPieces lev ts).map Prod.fst = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [qrHitPieces, ih]

/-- Each piece inherits a positive free heat bound from its suffix. -/
theorem qrHitPieces_props (lev : ℝ → ℝ) (ts : List ℝ) (ht : ts.Pairwise (· < ·))
    (p : ℝ × (ℝ × ℝ → ℝ)) (hp : p ∈ qrHitPieces lev ts) :
    Measurable p.2 ∧ ∃ τ : ℝ, 0 < τ ∧
      ∀ q, 0 ≤ p.2 q ∧ p.2 q ≤ heatKernel τ (q.1 - q.2) := by
  induction ts with
  | nil => simp [qrHitPieces] at hp
  | cons t ts ih =>
    simp only [qrHitPieces, List.mem_cons] at hp
    rcases hp with heq | hp
    · have hpos := fddEntries_pos lev (t :: ts) (ht.imp fun h => h.le)
        (ht.imp fun h => h.ne)
      cases h : fddEntries lev (t :: ts) with
      | nil => cases ts <;> simp [fddEntries] at h
      | cons e L =>
        rw [h] at hpos heq
        subst p
        have he := hpos e List.mem_cons_self
        have hL := fun a ha => hpos a (List.mem_cons_of_mem _ ha)
        exact ⟨(qrHitPiece_props e L he hL).1, gapSum e L, gapSum_pos L e he hL,
          (qrHitPiece_props e L he hL).2⟩
    · exact ih (List.pairwise_cons.mp ht).2 hp

/-- Propagating each starting piece from the first time and summing gives the hitting kernel. -/
theorem hitKerN_eq_sum_qrHitPieces (lev : ℝ → ℝ) (t : ℝ) (ts : List ℝ)
    (ht : (t :: ts).Pairwise (· < ·)) (e : ℝ × ℝ) (L : List (ℝ × ℝ))
    (h : fddEntries lev (t :: ts) = e :: L) :
    hitKerN e L = ((qrHitPieces lev (t :: ts)).map
      (fun p => qrHeatPropagate (p.1 - t) p.2)).sum := by
  induction ts generalizing t e L with
  | nil =>
    simp only [fddEntries, List.cons.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rw [hitKerN_nil_eq_qrHitPiece]
    simp [qrHitPieces, fddEntries, qrHeatPropagate]
  | cons s ts ih =>
    have hts := (List.pairwise_cons.mp ht).1 s List.mem_cons_self
    have htail := (List.pairwise_cons.mp ht).2
    cases he' : fddEntries lev (s :: ts) with
    | nil => cases ts <;> simp [fddEntries] at he'
    | cons y L' =>
      have hh : (lev t, s - t) :: y :: L' = e :: L := by
        simpa only [fddEntries, he'] using h
      injection hh with he hL
      subst e
      subst L
      have hpos := fddEntries_pos lev (s :: ts) (htail.imp fun h => h.le) (htail.imp fun h => h.ne)
      rw [he'] at hpos
      rw [hitKerN_eq_qrHitPiece_add _ y L' (sub_pos.mpr hts) (hpos _ List.mem_cons_self)
        (fun z hz => hpos z (List.mem_cons_of_mem _ hz)), ih s htail y L' he']
      simp only [qrHitPieces, fddEntries, he', List.map_cons, List.sum_cons,
        sub_self, qrHeatPropagate, lt_irrefl, ite_false]
      congr 1
      let Q := qrHitPieces lev (s :: ts)
      have hQ (k : ℝ × (ℝ × ℝ → ℝ)) (hk : k ∈ Q) : s ≤ k.1 := by
        have hm : k.1 ∈ s :: ts := by
          rw [← qrHitPieces_times lev (s :: ts)]
          exact List.mem_map.mpr ⟨k, hk, rfl⟩
        rcases List.mem_cons.mp hm with h | h
        · exact h.ge
        · exact ((List.pairwise_cons.mp htail).1 _ h).le
      have hadd (k : ℝ × (ℝ × ℝ → ℝ)) (hk : k ∈ Q) :
          qrHeatPropagate (s - t) (qrHeatPropagate (k.1 - s) k.2) =
            qrHeatPropagate (k.1 - t) k.2 := by
        obtain ⟨hm, τ, hτ, hb⟩ := qrHitPieces_props lev (s :: ts) htail k hk
        rw [← qrHeatPropagate_add (sub_nonneg.mpr hts.le) (sub_nonneg.mpr (hQ k hk)) hτ hm hb]
        congr 1
        ring
      have hterms : ∀ K ∈ Q.map (fun p => qrHeatPropagate (p.1 - s) p.2),
          Measurable K ∧ ∃ τ : ℝ, 0 < τ ∧
            ∀ p, 0 ≤ K p ∧ K p ≤ heatKernel τ (p.1 - p.2) := by
        intro K hK
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hK
        obtain ⟨hm, τ, hτ, hb⟩ := qrHitPieces_props lev (s :: ts) htail k hk
        have hq := qrHeatPropagate_props (sub_nonneg.mpr (hQ k hk)) hτ hm hb
        exact ⟨hq.1, (k.1 - s) + τ, by linarith [hQ k hk], hq.2⟩
      have hs := qrHeatPropagate_list_sum (s - t) _ hterms
      rw [List.map_map] at hs
      have hmap : Q.map (qrHeatPropagate (s - t) ∘ fun p => qrHeatPropagate (p.1 - s) p.2) =
          Q.map (fun p => qrHeatPropagate (p.1 - t) p.2) :=
        List.map_congr_left hadd
      rw [hmap] at hs
      simpa only [Q, qrHitPieces, he', List.map_cons, List.sum_cons, sub_self,
        qrHeatPropagate, lt_irrefl, ite_false, ite_eq_left (sub_pos.mpr hts)] using hs

/-- A first-hit piece vanishes at and below its own threshold. -/
theorem qrHitPieces_support (lev : ℝ → ℝ) (ts : List ℝ)
    (q : ℝ × (ℝ × ℝ → ℝ)) (hq : q ∈ qrHitPieces lev ts) (u v : ℝ)
    (hu : u ≤ lev q.1) : q.2 (u, v) = 0 := by
  induction ts with
  | nil => simp [qrHitPieces] at hq
  | cons t ts ih =>
    simp only [qrHitPieces, List.mem_cons] at hq
    rcases hq with rfl | hq
    · cases ts <;> simp [fddEntries, qrHitPiece, not_lt_of_ge hu]
    · exact ih hq

/-- A heat-bounded piece supported above a threshold can be weighted by a polynomial
on the output and a cut exponential on the input. -/
noncomputable def qrWeightedHitLeft (K : ℝ × ℝ → ℝ) (a : ℝ) (m : ℕ)
    (p : ℝ × ℝ) : ℝ :=
  (1 + p.1 ^ 2) ^ m * (K p * Real.exp (-a * p.2) * (1 + p.2 ^ 2))

/-- The weighted left factor of a first-hit piece is square integrable. -/
theorem memLp_qrWeightedHitLeft {K : ℝ × ℝ → ℝ} (hm : Measurable K)
    {T : ℝ} (hT : 0 < T) (x : ℝ) (hs : ∀ p, p.1 ≤ x → K p = 0)
    (hb : ∀ p, 0 ≤ K p ∧ K p ≤ heatKernel T (p.1 - p.2))
    (a : ℝ) (ha : 0 < a) (m : ℕ) :
    MemLp (qrWeightedHitLeft K a m) 2 (volume.prod volume) := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      (1 + p.1 ^ 2) ^ m * (Real.exp (-a * p.2) * (1 + p.2 ^ 2))) := by fun_prop
  have hmeas : Measurable (qrWeightedHitLeft K a m) := by
    have he : qrWeightedHitLeft K a m = fun p =>
        ((1 + p.1 ^ 2) ^ m * (Real.exp (-a * p.2) * (1 + p.2 ^ 2))) * K p := by
      funext p
      unfold qrWeightedHitLeft
      ring
    rw [he]
    exact hcont.measurable.mul hm
  refine (memLp_qrCutWeightedHeat hT x a ha m).mono' hmeas.aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  by_cases ht : x < p.1
  · have hmem : p ∈ Prod.fst ⁻¹' Set.Ioi x := ht
    rw [qrCutWeightedHeat, Set.indicator_of_mem hmem, qrWeightedHitLeft,
      Real.norm_of_nonneg (by positivity [(hb p).1])]
    gcongr
    exact (hb p).2
  · have hnot : p ∉ Prod.fst ⁻¹' Set.Ioi x := ht
    rw [qrCutWeightedHeat, Set.indicator_of_notMem hnot, qrWeightedHitLeft, hs p (le_of_not_gt ht)]
    simp

/-- Compose a heat-bounded hit piece with the backward Airy kernel in the polynomial
and exponential gauges. -/
noncomputable def qrWeightedHit (K : ℝ × ℝ → ℝ) (S a : ℝ) (m : ℕ)
    (p : ℝ × ℝ) : ℝ :=
  (1 + p.1 ^ 2) ^ m * AiryConj.compKernel K (AiryTwoInt.bAiryKer S) p * Real.exp (a * p.2)

/-- The gauges in the weighted hit factorization cancel exactly. -/
theorem qrWeightedHitLeft_comp_qrColumnAiry (K : ℝ × ℝ → ℝ) (S a : ℝ) (m : ℕ) :
    AiryConj.compKernel (qrWeightedHitLeft K a m) (qrColumnAiry S a) =
      qrWeightedHit K S a m := by
  let M (z : ℝ) := Real.exp (a * z) * (1 + z ^ 2)⁻¹
  have hm (z : ℝ) : M z ≠ 0 := (show 0 < Real.exp (a * z) * (1 + z ^ 2)⁻¹ by positivity).ne'
  have hleft : qrWeightedHitLeft K a m =
      fun p => (1 + p.1 ^ 2) ^ m * K p * (M p.2)⁻¹ := by
    funext p
    simp only [qrWeightedHitLeft, M, mul_inv_rev, inv_inv, ← Real.exp_neg]
    ring
  have hright : qrColumnAiry S a =
      fun p => M p.1 * AiryTwoInt.bAiryKer S p * Real.exp (a * p.2) := by
    funext p
    unfold qrColumnAiry qrAiryProfile AiryTwoInt.bAiryKer M
    rw [mul_add, Real.exp_add]
    ring
  rw [hleft, hright, qr_compKernel_cancel_weight K (AiryTwoInt.bAiryKer S)
    (fun z => (1 + z ^ 2) ^ m) M (fun z => Real.exp (a * z)) hm]
  rfl

/-- A weighted hit piece composed with the backward Airy profile is square integrable. -/
theorem memLp_qrWeightedHit {K : ℝ × ℝ → ℝ} (hm : Measurable K)
    {T S : ℝ} (hT : 0 < T) (x : ℝ) (hs : ∀ p, p.1 ≤ x → K p = 0)
    (hb : ∀ p, 0 ≤ K p ∧ K p ≤ heatKernel T (p.1 - p.2))
    (a : ℝ) (ha : 0 < a) (hSa : S < a) (m : ℕ) :
    MemLp (qrWeightedHit K S a m) 2 (volume.prod volume) := by
  have hL : Measurable (qrWeightedHitLeft K a m) := by
    unfold qrWeightedHitLeft
    apply Measurable.mul (by fun_prop)
    exact (hm.mul (Real.continuous_exp.measurable.comp (measurable_snd.const_mul (-a)))).mul
      ((measurable_snd.pow_const 2).const_add 1)
  have hA : Measurable (qrColumnAiry S a) := by
    have hc : Continuous airyAiReal :=
      continuous_iff_continuousAt.mpr fun s => (hasDerivAt_airyAiReal s).continuousAt
    unfold qrColumnAiry qrAiryProfile backwardAiry
    apply Measurable.mul (((measurable_fst.pow_const 2).const_add 1).inv)
    fun_prop
  rw [← qrWeightedHitLeft_comp_qrColumnAiry]
  exact AiryTwoInt.memLp_compKernel hL hA (memLp_qrWeightedHitLeft hm hT x hs hb a ha m)
    (memLp_qrColumnAiry S a hSa)

/-- Filtering starting pieces at a time threshold selects the pieces of that suffix. -/
theorem qrHitPieces_filter (lev : ℝ → ℝ) (ts : List ℝ) (ht : ts.Pairwise (· < ·)) (a : ℝ) :
    (qrHitPieces lev ts).filter (fun p => decide (a ≤ p.1)) =
      qrHitPieces lev (ts.filter (fun t => decide (a ≤ t))) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    by_cases ha : a ≤ t
    · have hlist : (t :: ts).filter (fun t => decide (a ≤ t)) = t :: ts :=
        List.filter_eq_self.mpr fun u hu => decide_eq_true (by
          rcases List.mem_cons.mp hu with rfl | hu
          · exact ha
          · exact ha.trans ((List.pairwise_cons.mp ht).1 _ hu).le)
      rw [hlist]
      exact List.filter_eq_self.mpr fun p hp => by
        have hm := List.mem_map_of_mem (f := Prod.fst) hp
        rw [qrHitPieces_times] at hm
        rcases List.mem_cons.mp hm with h | h
        · exact decide_eq_true (ha.trans_eq h.symm)
        · exact decide_eq_true (ha.trans ((List.pairwise_cons.mp ht).1 _ h).le)
    · simp only [qrHitPieces, List.filter_cons, ha, decide_false, Bool.false_eq_true, ite_false]
      exact ih (List.pairwise_cons.mp ht).2

/-- In a strictly increasing list the suffix from a member starts at that member. -/
theorem qr_filter_ge_eq_cons {ts : List ℝ} (hs : ts.Pairwise (· < ·))
    {a : ℝ} (ha : a ∈ ts) :
    ∃ l, ts.filter (fun t => decide (a ≤ t)) = a :: l := by
  induction ts with
  | nil => simp at ha
  | cons t ts ih =>
    rcases List.mem_cons.mp ha with rfl | hmem
    · refine ⟨ts, ?_⟩
      simp only [List.filter_cons, le_refl, decide_true, ite_true, List.cons.injEq, true_and]
      exact List.filter_eq_self.mpr fun u hu =>
        decide_eq_true ((List.pairwise_cons.mp hs).1 _ hu).le
    · have ht : t < a := (List.pairwise_cons.mp hs).1 _ hmem
      simpa [List.filter_cons, not_le_of_gt ht] using ih (List.pairwise_cons.mp hs).2 hmem

/-- Each time tag occurs as the index of a chronological hitting piece. -/
theorem exists_qrTagPiece (I : Finset ℝ) (x : I → ℝ) (i : I) :
    ∃ p ∈ qrHitPieces (levelFn I x) (I.sort (· ≤ ·)), p.1 = (i : ℝ) := by
  apply List.mem_map.mp
  rw [qrHitPieces_times]
  exact (Finset.mem_sort _).mpr i.property

/-- The starting piece at each tag, indexed directly on the finite time set. -/
noncomputable def qrTagPiece (I : Finset ℝ) (x : I → ℝ) (i : I) : ℝ × ℝ → ℝ :=
  (exists_qrTagPiece I x i).choose.2

/-- The time and kernel selected at a tag occur in the chronological list. -/
theorem qrTagPiece_mem (I : Finset ℝ) (x : I → ℝ) (i : I) :
    ((i : ℝ), qrTagPiece I x i) ∈ qrHitPieces (levelFn I x) (I.sort (· ≤ ·)) := by
  let q := (exists_qrTagPiece I x i).choose
  have hq := (exists_qrTagPiece I x i).choose_spec
  have he : q = ((i : ℝ), qrTagPiece I x i) := Prod.ext hq.2 rfl
  rw [← he]
  exact hq.1

/-- The selected kernels describe every chronological piece. -/
theorem qrTagPiece_eq_of_mem (I : Finset ℝ) (x : I → ℝ)
    (p : ℝ × (ℝ × ℝ → ℝ)) (hp : p ∈ qrHitPieces (levelFn I x) (I.sort (· ≤ ·))) :
    ∃ i : I, p = ((i : ℝ), qrTagPiece I x i) := by
  have hmem := List.mem_map_of_mem (f := Prod.fst) hp
  rw [qrHitPieces_times] at hmem
  let i : I := ⟨p.1, (Finset.mem_sort _).mp hmem⟩
  have hn : ((qrHitPieces (levelFn I x) (I.sort (· ≤ ·))).map Prod.fst).Nodup := by
    rw [qrHitPieces_times]
    exact Finset.sort_nodup _ _
  refine ⟨i, ?_⟩
  exact List.inj_on_of_nodup_map hn hp (qrTagPiece_mem I x i) rfl

/-- The sorted tags are strictly increasing. -/
theorem qr_sort_pairwise (I : Finset ℝ) : (I.sort (· ≤ ·)).Pairwise (· < ·) := by
  have h := Finset.pairwise_sort I (· ≤ ·)
  have hn := Finset.sort_nodup I (· ≤ ·)
  exact (List.pairwise_and_iff.mpr ⟨h, hn⟩).imp (fun h => lt_of_le_of_ne h.1 h.2)

/-- The suffix sum on a finite index set is the scalar hitting kernel at that suffix. -/
theorem qr_hitKer_eq_tagged_sum (I : Finset ℝ) (x : I → ℝ) (i : I)
    (e : ℝ × ℝ) (L : List (ℝ × ℝ))
    (h : fddEntries (levelFn I x) ((I.sort (· ≤ ·)).filter (fun t => decide ((i : ℝ) ≤ t))) = e :: L) :
    hitKerN e L = ∑ j ∈ (Finset.univ : Finset I).filter (fun j : I => (i : ℝ) ≤ (j : ℝ)),
      qrHeatPropagate ((j : ℝ) - i) (qrTagPiece I x j) := by
  classical
  let lev := levelFn I x
  let ts := I.sort (· ≤ ·)
  let tail := ts.filter (fun t => decide ((i : ℝ) ≤ t))
  have hmem : (i : ℝ) ∈ ts := (Finset.mem_sort _).mpr i.property
  obtain ⟨l, hl⟩ := qr_filter_ge_eq_cons (qr_sort_pairwise I) hmem
  have ht : tail.Pairwise (· < ·) := (qr_sort_pairwise I).filter _
  have hhit := hitKerN_eq_sum_qrHitPieces lev (i : ℝ) l (hl ▸ ht) e L (hl ▸ h)
  rw [← hl] at hhit
  let q := (qrHitPieces lev ts).filter (fun p => decide ((i : ℝ) ≤ p.1))
  have hq : q = qrHitPieces lev tail := qrHitPieces_filter lev ts (qr_sort_pairwise I) _
  rw [← hq, ← List.sum_toFinset _] at hhit
  · have he : q.toFinset = ((Finset.univ : Finset I).filter (fun j : I => (i : ℝ) ≤ (j : ℝ))).image
        (fun j : I => ((j : ℝ), qrTagPiece I x j)) := by
      ext p
      simp only [List.mem_toFinset, q, List.mem_filter, decide_eq_true_eq, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hp, hi⟩
        obtain ⟨j, rfl⟩ := qrTagPiece_eq_of_mem I x p hp
        exact ⟨j, hi, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨qrTagPiece_mem I x j, hj⟩
    rw [he, Finset.sum_image] at hhit
    · exact hhit
    · intro j _ k _ heq
      exact Subtype.ext (congrArg Prod.fst heq)
  · have hn : (qrHitPieces lev ts).Nodup :=
      List.Nodup.of_map (f := Prod.fst) (by rw [qrHitPieces_times]; exact Finset.sort_nodup _ _)
    exact hn.filter _

/-- The sum of consecutive gaps and terminal padding is the elapsed time plus one. -/
theorem qr_gapSum_fddEntries (lev : ℝ → ℝ) (t : ℝ) (ts : List ℝ)
    (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (h : fddEntries lev (t :: ts) = e :: L) :
    gapSum e L = ts.getLastD t - t + 1 := by
  induction ts generalizing t e L with
  | nil =>
    simp only [fddEntries, List.cons.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [gapSum]
  | cons z ts ih =>
    cases hz : fddEntries lev (z :: ts) with
    | nil => cases ts <;> simp [fddEntries] at hz
    | cons e' L' =>
      simp only [fddEntries, hz, List.cons.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rw [gapSum, ih z e' L' hz]
      simp only [List.getLastD_cons]
      ring

/-- Heat propagation can be regrouped with a heat-bounded hit kernel before
convolving with backward Airy. -/
theorem qr_compKernel_heat_hitAiry {K : ℝ × ℝ → ℝ} {T s S : ℝ}
    (hT : 0 < T) (hs : 0 < s) (hS : 0 ≤ S) (hm : Measurable K)
    (hb : ∀ p, 0 ≤ K p ∧ K p ≤ heatKernel T (p.1 - p.2)) :
    AiryConj.compKernel (AiryTwoInt.heatKerTwo s)
      (AiryConj.compKernel K (AiryTwoInt.bAiryKer S)) =
      AiryConj.compKernel (qrHeatPropagate s K) (AiryTwoInt.bAiryKer S) := by
  funext p
  obtain ⟨C, hC⟩ := AiryTwoInt.bAiryKer_abs_le_exp hS p.2
  have hmeas : Measurable (fun z : ℝ => backwardAiry S (z + p.2)) :=
    ((continuous_backwardAiry_s S).comp (continuous_id.add_const _)).measurable
  rw [qrHeatPropagate, ite_eq_left hs]
  exact (AiryTwoInt.compKernel_assoc p.1 p.2
    (AiryTwoInt.integrable_uncurry_of_abs_le hs hT hS p.1
      (AiryTwoInt.measurable_heatKerTwo s)
      (fun z => AiryTwoInt.heatKerTwo_abs_le_self hs _)
      hm (fun z w => by rw [abs_of_nonneg (hb (z, w)).1]; exact (hb (z, w)).2)
      hmeas C hC)).symm

/-- A weighted heat block followed by an active hit piece cancels the intermediate
tag gauge and propagates the unweighted piece. -/
theorem qr_compKernel_cut_heat_hit
    {K : ℝ × ℝ → ℝ} {T s S : ℝ} (hT : 0 < T) (hs : 0 < s) (hS : 0 ≤ S)
    (hm : Measurable K) (hb : ∀ p, 0 ≤ K p ∧ K p ≤ heatKernel T (p.1 - p.2))
    (x : ℝ) (hx : ∀ p, p.1 ≤ x → K p = 0)
    (a : ℝ) (m : ℕ) (l : ℝ → ℝ) :
    AiryConj.compKernel
      (fun p => l p.1 * AiryTwoInt.heatKerTwo s p *
        ((Set.Ioi x).indicator (fun t => ((1 + t ^ 2) ^ m)⁻¹) p.2))
      (qrWeightedHit K S a m) =
    fun p => l p.1 * AiryConj.compKernel (qrHeatPropagate s K) (AiryTwoInt.bAiryKer S) p *
      Real.exp (a * p.2) := by
  let G := AiryConj.compKernel K (AiryTwoInt.bAiryKer S)
  let W (t : ℝ) := (1 + t ^ 2) ^ m
  have hzero (p : ℝ × ℝ) (hp : p.1 ≤ x) : G p = 0 := by
    change (∫ z : ℝ, K (p.1, z) * backwardAiry S (z + p.2)) = 0
    have hK : ∀ z : ℝ, K (p.1, z) = 0 := fun z => hx (p.1, z) hp
    apply integral_eq_zero_of_ae
    exact ae_of_all _ fun z => by change K (p.1, z) * _ = (0 : ℝ); rw [hK z, zero_mul]
  have hright : qrWeightedHit K S a m =
      fun p => W p.1 * G p * Real.exp (a * p.2) := rfl
  have hcancel :
      AiryConj.compKernel
        (fun p => l p.1 * AiryTwoInt.heatKerTwo s p *
          ((Set.Ioi x).indicator (fun t => (W t)⁻¹) p.2))
        (fun p => W p.1 * G p * Real.exp (a * p.2)) =
      fun p => l p.1 * AiryConj.compKernel (AiryTwoInt.heatKerTwo s) G p * Real.exp (a * p.2) := by
    rw [← qr_compKernel_cancel_weight (AiryTwoInt.heatKerTwo s) G l W
      (fun t => Real.exp (a * t)) (fun z => by dsimp [W]; positivity)]
    funext p
    unfold AiryConj.compKernel
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      dsimp only
      by_cases hz : z ∈ Set.Ioi x
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hzero (z, p.2) (le_of_not_gt hz)]
        simp
  rw [hright, hcancel]
  simp only [G, qr_compKernel_heat_hitAiry hT hs hS hm hb]

/-- Positive-gap row propagation produces the exponentially conjugated hit kernel. -/
theorem qrRowHeat_comp_weightedHit {K : ℝ × ℝ → ℝ} {T r S : ℝ}
    (hT : 0 < T) (hr : 0 < r) (hS : 0 ≤ S) (hm : Measurable K)
    (hb : ∀ p, 0 ≤ K p ∧ K p ≤ heatKernel T (p.1 - p.2))
    (x : ℝ) (hx : ∀ p, p.1 ≤ x → K p = 0) (a : ℝ) (m : ℕ) :
    AiryConj.compKernel (qrRowHeat x a r m) (qrWeightedHit K S a m) =
      AiryConj.expConjKernel a
        (AiryConj.compKernel (qrHeatPropagate r K) (AiryTwoInt.bAiryKer S)) := by
  have he : qrRowHeat x a r m = fun p =>
      Real.exp (-a * p.1) * AiryTwoInt.heatKerTwo r p *
        (Set.Ioi x).indicator (fun t => ((1 + t ^ 2) ^ m)⁻¹) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Ioi x <;>
      simp [qrRowHeat, AiryTwoInt.heatKerTwo, hp, div_eq_mul_inv]
  rw [he, qr_compKernel_cut_heat_hit hT hr hS hm hb x hx a m (fun t => Real.exp (-a * t))]
  funext p
  unfold AiryConj.expConjKernel
  rw [show -a * p.1 = -(a * p.1) by ring]

/-- At zero gap the row multiplier cancels the tag gauge directly. -/
theorem qrRowZero_mul_weightedHit (K : ℝ × ℝ → ℝ) (S x a : ℝ) (m : ℕ)
    (hx : ∀ p, p.1 ≤ x → K p = 0) :
    (fun p : ℝ × ℝ => qrRowZero x a m p.1 * qrWeightedHit K S a m p) =
      AiryConj.expConjKernel a (AiryConj.compKernel K (AiryTwoInt.bAiryKer S)) := by
  funext p
  unfold qrRowZero qrWeightedHit AiryConj.expConjKernel
  by_cases hp : p.1 ∈ Set.Ioi x
  · rw [Set.indicator_of_mem hp, show -a * p.1 = -(a * p.1) by ring]
    have hw : (1 + p.1 ^ 2) ^ m ≠ 0 := by positivity
    field_simp
  · have hz : AiryConj.compKernel K (AiryTwoInt.bAiryKer S) p = 0 := by
      change (∫ z : ℝ, K (p.1, z) * backwardAiry S (z + p.2)) = 0
      apply integral_eq_zero_of_ae
      exact ae_of_all _ fun z => by
        change K (p.1, z) * _ = (0 : ℝ)
        rw [hx (p.1, z) (le_of_not_gt hp), zero_mul]
    rw [Set.indicator_of_notMem hp, hz]
    ring

/-- An upper heat block propagates a weighted hit piece to the earlier tag. -/
theorem qrHeatCutKer_comp_weightedHit (I : Finset ℝ) (x : I → ℝ) {i j : I}
    (hij : (i : ℝ) < j) {K : ℝ × ℝ → ℝ} {T S : ℝ} (hT : 0 < T)
    (hS : 0 ≤ S) (hm : Measurable K)
    (hb : ∀ p, 0 ≤ K p ∧ K p ≤ heatKernel T (p.1 - p.2))
    (hx : ∀ p, p.1 ≤ x j → K p = 0) (a : ℝ) :
    AiryConj.compKernel (qrHeatCutKer I x i j)
      (qrWeightedHit K S a (2 * airyTimeRank I j)) =
    fun p => qrCutWeight I x i p.1 *
      AiryConj.compKernel (qrHeatPropagate ((j : ℝ) - i) K) (AiryTwoInt.bAiryKer S) p *
        Real.exp (a * p.2) := by
  have he : qrHeatCutKer I x i j = fun p =>
      qrCutWeight I x i p.1 * AiryTwoInt.heatKerTwo ((j : ℝ) - i) p *
        (Set.Ioi (x j)).indicator (fun t => ((1 + t ^ 2) ^ (2 * airyTimeRank I j))⁻¹) p.2 := by
    funext p
    simp [qrHeatCutKer, qrCutInvWeight, airyRankGauge, hij, AiryTwoInt.heatKerTwo]
  rw [he]
  exact qr_compKernel_cut_heat_hit hT (sub_pos.mpr hij) hS hm hb (x j) hx a _
    (qrCutWeight I x i)

/-- The suffix starting at a tag has that tag's level and runs to the last time. -/
theorem qr_suffixEntries (I : Finset ℝ) (x : I → ℝ) (i : I) :
    ∃ e L, fddEntries (levelFn I x)
        ((I.sort (· ≤ ·)).filter (fun t => decide ((i : ℝ) ≤ t))) = e :: L ∧
      e.1 = x i ∧ 0 < e.2 ∧ (∀ y ∈ L, 0 < y.2) ∧
      gapSum e L = airyTimeSpan I + 1 - airyRelativeTime I i := by
  let ts := I.sort (· ≤ ·)
  let tail := ts.filter (fun t => decide ((i : ℝ) ≤ t))
  let lev := levelFn I x
  have hmem : (i : ℝ) ∈ ts := (Finset.mem_sort _).mpr i.property
  obtain ⟨l, hl⟩ := qr_filter_ge_eq_cons (qr_sort_pairwise I) hmem
  have htail : tail = (i : ℝ) :: l := hl
  have hn : I.Nonempty := ⟨i, i.property⟩
  have hmax : I.max' hn ∈ tail := List.mem_filter.mpr
    ⟨(Finset.mem_sort _).mpr (Finset.max'_mem _ _), decide_eq_true (Finset.le_max' _ _ i.property)⟩
  have hlast : l.getLastD (i : ℝ) = I.max' hn := by
    have hlastmem : l.getLastD (i : ℝ) ∈ tail := htail.symm ▸ List.getLastD_mem_cons
    have hi := Finset.le_max' I _ ((Finset.mem_sort _).mp (List.mem_filter.mp hlastmem).1)
    have hpair : tail.Pairwise (· ≤ ·) := ((qr_sort_pairwise I).imp fun h => h.le).filter _
    rw [htail] at hpair hmax
    have hj := hpair.rel_getLast hmax
    refine le_antisymm hi ?_
    change I.max' hn ≤ l.getLastD (i : ℝ)
    rw [List.getLast_eq_getLastD] at hj
    exact hj
  obtain ⟨e, L, hentry, hlev⟩ :
      ∃ e L, fddEntries lev ((i : ℝ) :: l) = e :: L ∧ e.1 = x i := by
    cases l <;> exact ⟨_, _, rfl, by simp [lev, levelFn, i.property]⟩
  have hs := ((qr_sort_pairwise I).imp fun h => h.le).filter (fun t => decide ((i : ℝ) ≤ t))
  have hd := (Finset.sort_nodup I (· ≤ ·)).filter (fun t => decide ((i : ℝ) ≤ t))
  have hpos := fddEntries_pos lev tail hs hd
  rw [htail, hentry] at hpos
  have hent : fddEntries lev tail = e :: L := by rw [htail, hentry]
  refine ⟨e, L, hent, hlev, hpos _ List.mem_cons_self,
    (fun y hy => hpos y (List.mem_cons_of_mem _ hy)), ?_⟩
  rw [qr_gapSum_fddEntries lev (i : ℝ) l e L hentry, hlast]
  simp only [airyTimeSpan, airyRelativeTime, airyFirstTime, dite_eq_left hn]
  ring

/-- The fixed weighted hit kernel at one tag is square integrable and measurable. -/
theorem qr_tagWeightedHit_props (I : Finset ℝ) (x : I → ℝ) (j : I) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    let K := qrTagPiece I x j
    let S := airyTimeSpan I + 1
    Measurable (qrWeightedHit K S a (2 * airyTimeRank I j)) ∧
      MemLp (qrWeightedHit K S a (2 * airyTimeRank I j)) 2 (volume.prod volume) := by
  obtain ⟨hm, T, hT, hb⟩ := qrHitPieces_props _ _ (qr_sort_pairwise I) _
    (qrTagPiece_mem I x j)
  have hx (p : ℝ × ℝ) (hp : p.1 ≤ x j) : qrTagPiece I x j p = 0 := by
    exact qrHitPieces_support _ _ _ (qrTagPiece_mem I x j) p.1 p.2
      (by simpa [levelFn, j.property] using hp)
  have ha' : 0 < a := by
    linarith [(airyRelativeTime_bounds I j).1, (airyRelativeTime_bounds I j).2]
  have h := AiryTwoInt.measurable_compKernel hm
    (AiryConj.measurable_backwardAiryPair (airyTimeSpan I + 1))
  exact ⟨(((measurable_fst.pow_const 2).const_add 1).pow_const _).mul h |>.mul
    (Real.continuous_exp.measurable.comp (measurable_snd.const_mul a)),
    memLp_qrWeightedHit hm hT (x j) hx hb a ha' (by linarith) _⟩

/-- The candidate triangular solution is assembled from the propagated hit pieces. -/
noncomputable def qrHitColumn (I : Finset ℝ) (x : I → ℝ) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) : RealLp →L[ℝ] TaggedLp I :=
  ∑ i : I, airyTagIn I i ∘L HilbertSchmidt.kernelOperator (qr_tagWeightedHit_props I x i a ha).2

/-- Extraction of each tag from the hit column gives its weighted hit kernel operator. -/
theorem airyTagOut_comp_qrHitColumn (I : Finset ℝ) (x : I → ℝ) (i : I) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    airyTagOut I i ∘L qrHitColumn I x a ha =
      HilbertSchmidt.kernelOperator (qr_tagWeightedHit_props I x i a ha).2 := by
  classical
  unfold qrHitColumn
  rw [ContinuousLinearMap.comp_finsetSum, Finset.sum_eq_single i]
  · simp [← ContinuousLinearMap.comp_assoc, airyTagOut_comp_airyTagIn]
  · intro j _ hj
    simp [← ContinuousLinearMap.comp_assoc, airyTagOut_comp_airyTagIn, Ne.symm hj]
  · simp

/-- A finite sum of square-integrable kernels represents the sum of their operators. -/
theorem qr_kernelOperator_finsetSum {ι : Type*} (s : Finset ι)
    (K : ι → ℝ × ℝ → ℝ)
    (hK : ∀ i, MemLp (K i) 2 (volume.prod volume))
    (h : MemLp (∑ i ∈ s, K i) 2 (volume.prod volume)) :
    HilbertSchmidt.kernelOperator h = ∑ i ∈ s, HilbertSchmidt.kernelOperator (hK i) := by
  ext1 f
  rw [ContinuousLinearMap.sum_apply]
  apply Lp.ext
  have eval (i : ι) := HilbertSchmidt.kernelOperator_apply_ae (hK i) f
  have hin (i : ι) := HilbertSchmidt.integrable_kernelFun_slice_ae (hK i) f
  have eae := Lp.coeFn_fun_finsetSum s (fun i => HilbertSchmidt.kernelOperator (hK i) f)
  filter_upwards [HilbertSchmidt.kernelOperator_apply_ae h f, eae,
    (ae_ball_iff s.countable_toSet).mpr (fun i _ => eval i),
    (ae_ball_iff s.countable_toSet).mpr (fun i _ => hin i)] with u hu he hs hi
  rw [hu, he]
  simp_rw [HilbertSchmidt.kernelIntegralFun, Finset.sum_apply, Finset.sum_mul]
  rw [integral_finsetSum _ hi]
  exact Finset.sum_congr rfl (fun i hi => (hs i hi).symm)

/-- Convolution with backward Airy distributes over a finite sum of heat-bounded kernels. -/
theorem qr_compKernel_sum_bAiry {ι : Type*} (s : Finset ι) (K : ι → ℝ × ℝ → ℝ)
    {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ i ∈ s, Measurable (K i) ∧ ∃ T : ℝ, 0 < T ∧
      ∀ p, 0 ≤ K i p ∧ K i p ≤ heatKernel T (p.1 - p.2)) :
    AiryConj.compKernel (∑ i ∈ s, K i) (AiryTwoInt.bAiryKer S) =
      ∑ i ∈ s, AiryConj.compKernel (K i) (AiryTwoInt.bAiryKer S) := by
  funext p
  simp only [AiryConj.compKernel, AiryTwoInt.bAiryKer, Finset.sum_apply, Finset.sum_mul]
  apply integral_finsetSum
  intro i hi
  obtain ⟨hm, T, hT, hb⟩ := h i hi
  exact integrable_mul_bAiry hT hS hm (fun q => by rw [abs_of_nonneg (hb q).1]; exact (hb q).2) _ _

/-- The contribution of the hit piece at a later tag to the triangular equation at a tag. -/
noncomputable def qrTriKer (I : Finset ℝ) (x : I → ℝ) (i j : I) (a : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  if (i : ℝ) ≤ j then qrCutWeight I x i p.1 *
    AiryConj.compKernel (qrHeatPropagate ((j : ℝ) - i) (qrTagPiece I x j))
      (AiryTwoInt.bAiryKer (airyTimeSpan I + 1)) p * Real.exp (a * p.2) else 0

/-- The diagonal and strictly upper contributions have their expected kernel operators. -/
theorem qrTriKer_operator (I : Finset ℝ) (x : I → ℝ) (i j : I) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    ∃ h : MemLp (qrTriKer I x i j a) 2 (volume.prod volume),
      HilbertSchmidt.kernelOperator h = (if i = j then
        HilbertSchmidt.kernelOperator (qr_tagWeightedHit_props I x j a ha).2
        else airyHeatBlock I x i j ∘L
          HilbertSchmidt.kernelOperator (qr_tagWeightedHit_props I x j a ha).2) := by
  classical
  let K := qrTagPiece I x j
  let S := airyTimeSpan I + 1
  let H := qrWeightedHit K S a (2 * airyTimeRank I j)
  have hH := (qr_tagWeightedHit_props I x j a ha).2
  have hx (p : ℝ × ℝ) (hp : p.1 ≤ x j) : K p = 0 :=
    qrHitPieces_support _ _ _ (qrTagPiece_mem I x j) p.1 p.2
      (by simpa [levelFn, j.property] using hp)
  rcases lt_trichotomy (i : ℝ) (j : ℝ) with hij | heq | hji
  · obtain ⟨hm, T, hT, hb⟩ := qrHitPieces_props _ _ (qr_sort_pairwise I) _
      (qrTagPiece_mem I x j)
    have hS : 0 ≤ S := by dsimp [S]; linarith [(airyRelativeTime_bounds I j).1, (airyRelativeTime_bounds I j).2]
    have hG : Measurable (qrHeatCutKer I x i j) := by
      have hw (k : I) : Continuous (airyRankGauge I k) := by unfold airyRankGauge; fun_prop
      have hl := (hw i).measurable.indicator (measurableSet_Ioi (a := x i))
      have hr := (hw j).measurable.inv.indicator (measurableSet_Ioi (a := x j))
      have ht := AiryTwoInt.measurable_heatKerTwo ((j : ℝ) - i)
      have hh : qrHeatCutKer I x i j = fun p => qrCutWeight I x i p.1 *
          AiryTwoInt.heatKerTwo ((j : ℝ) - i) p * qrCutInvWeight I x j p.2 := by
        funext p
        simp [qrHeatCutKer, hij, AiryTwoInt.heatKerTwo]
      rw [hh]
      exact ((hl.comp measurable_fst).mul ht).mul (hr.comp measurable_snd)
    have hc := AiryTwoInt.memLp_compKernel hG (qr_tagWeightedHit_props I x j a ha).1
      (memLp_qrHeatCutKer I x i j) hH
    have hker : AiryConj.compKernel (qrHeatCutKer I x i j) H = qrTriKer I x i j a := by
      rw [qrHeatCutKer_comp_weightedHit I x hij hT hS hm hb hx a]
      funext p
      simp [qrTriKer, hij.le, S, K]
    refine ⟨hker ▸ hc, ?_⟩
    rw [ite_eq_right (fun h => hij.ne (congrArg Subtype.val h)), airyHeatBlock_eq_kernelOperator]
    exact (AiryTwoInt.kernelOperator_congr hker hc _).symm.trans
      (AiryTwoInt.kernelOperator_compKernel (memLp_qrHeatCutKer I x i j) hH hc)
  · have h : i = j := Subtype.ext heq
    subst i
    have hker : H = qrTriKer I x j j a := by
      funext p
      have htri : qrTriKer I x j j a p =
          qrCutWeight I x j p.1 * AiryConj.compKernel K (AiryTwoInt.bAiryKer S) p *
            Real.exp (a * p.2) := by simp [qrTriKer, qrHeatPropagate, K, S]
      rw [htri]
      by_cases hp : p.1 ∈ Set.Ioi (x j)
      · simp [H, qrWeightedHit, qrCutWeight, airyRankGauge, Set.indicator_of_mem hp]
      · have hzero : AiryConj.compKernel K (AiryTwoInt.bAiryKer S) p = 0 := by
          apply integral_eq_zero_of_ae
          exact ae_of_all _ fun z => by
            change K (p.1, z) * _ = (0 : ℝ)
            rw [hx (p.1, z) (le_of_not_gt hp), zero_mul]
        simp [H, qrWeightedHit, qrCutWeight, Set.indicator_of_notMem hp, hzero]
    refine ⟨hker ▸ hH, ?_⟩
    rw [ite_eq_left rfl]
    exact (AiryTwoInt.kernelOperator_congr hker hH _).symm
  · have hzero : qrTriKer I x i j a = 0 := by
      funext p
      simp [qrTriKer, not_le_of_gt hji]
    have hm : MemLp (qrTriKer I x i j a) 2 (volume.prod volume) := by rw [hzero]; simp [memLp_iff]
    refine ⟨hm, ?_⟩
    rw [ite_eq_right (fun h => hji.ne (congrArg Subtype.val h).symm), airyHeatBlock,
      dite_eq_right (not_lt_of_ge hji.le), ContinuousLinearMap.zero_comp]
    ext1 f
    apply Lp.ext
    filter_upwards [HilbertSchmidt.kernelOperator_apply_ae hm f,
      Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with p hp hz
    rw [hp]
    simp [HilbertSchmidt.kernelIntegralFun, hzero, hz]

/-- The contributions in a triangular row sum to the original weighted Airy column. -/
theorem qrTriKer_sum_eq_column (I : Finset ℝ) (x : I → ℝ) (i : I) (a : ℝ) :
    (∑ j : I, qrTriKer I x i j a) = qrColumnKer I x i a := by
  classical
  obtain ⟨e, L, hent, hlev, he, hL, hgap⟩ := qr_suffixEntries I x i
  let s := (Finset.univ : Finset I).filter (fun j : I => (i : ℝ) ≤ (j : ℝ))
  let K (j : I) := qrHeatPropagate ((j : ℝ) - i) (qrTagPiece I x j)
  let S := airyTimeSpan I + 1
  have hS : 0 ≤ S := by
    dsimp [S]
    linarith [(airyRelativeTime_bounds I i).1, (airyRelativeTime_bounds I i).2]
  have hterms : ∀ j ∈ s, Measurable (K j) ∧ ∃ T : ℝ, 0 < T ∧
      ∀ p, 0 ≤ K j p ∧ K j p ≤ heatKernel T (p.1 - p.2) := by
    intro j hj
    obtain ⟨hm, T, ht, hb⟩ := qrHitPieces_props _ _ (qr_sort_pairwise I) _ (qrTagPiece_mem I x j)
    have hg : 0 ≤ (j : ℝ) - i := sub_nonneg.mpr (Finset.mem_filter.mp hj).2
    obtain ⟨hM, hB⟩ := qrHeatPropagate_props hg ht hm hb
    exact ⟨hM, _, add_pos_of_nonneg_of_pos hg ht, hB⟩
  have hsum := qr_compKernel_sum_bAiry s K hS hterms
  rw [← qr_hitKer_eq_tagged_sum I x i e L hent] at hsum
  funext p
  simp only [Finset.sum_apply, qrTriKer]
  rw [← Finset.sum_filter]
  change (∑ j ∈ s, qrCutWeight I x i p.1 *
      AiryConj.compKernel (K j) (AiryTwoInt.bAiryKer S) p * Real.exp (a * p.2)) = _
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_apply, ← hsum]
  by_cases hp : p.1 ∈ Set.Ioi (x i)
  · have hb : ∀ z : ℝ, hitKerN e L (p.1, z) =
        AiryTwoInt.heatKerTwo (gapSum e L) (p.1, z) := by
      intro z
      have hn : p.1 ∉ Set.Iic e.1 := by rw [hlev]; exact not_le_of_gt (show x i < p.1 from hp)
      cases L <;> simp [hitKerN, lamKerN, lamKer1, AiryTwoInt.heatKerTwo,
        Set.indicator_of_notMem hn]
    have hconv : AiryConj.compKernel (hitKerN e L) (AiryTwoInt.bAiryKer S) p =
        backwardAiry (airyRelativeTime I i) (p.1 + p.2) := by
      have htime : S - gapSum e L = airyRelativeTime I i := by dsimp [S]; linarith
      calc
        _ = AiryConj.compKernel (AiryTwoInt.heatKerTwo (gapSum e L)) (AiryTwoInt.bAiryKer S) p := by
          apply integral_congr_ae
          exact ae_of_all _ fun z => by dsimp only; rw [hb z]
        _ = _ := by
          rw [AiryTwoInt.heatKerTwo_comp_bAiryKer_any (gapSum_pos L e he hL), htime]
          rfl
    rw [hconv]
    rfl
  · simp [qrColumnKer, qrCutWeight, Set.indicator_of_notMem hp]

/-- The sum of the diagonal and upper block contributions is the column kernel operator. -/
theorem qrTriKer_sum_operator (I : Finset ℝ) (x : I → ℝ) (i : I) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    (∑ j : I, if i = j then HilbertSchmidt.kernelOperator (qr_tagWeightedHit_props I x j a ha).2
      else airyHeatBlock I x i j ∘L HilbertSchmidt.kernelOperator (qr_tagWeightedHit_props I x j a ha).2) =
      HilbertSchmidt.kernelOperator (memLp_qrColumnKer I x i a ha) := by
  classical
  choose hK hok using fun j : I => qrTriKer_operator I x i j a ha
  simp_rw [← hok]
  let K (j : I) := qrTriKer I x i j a
  have he : (∑ j : I, K j) = qrColumnKer I x i a := qrTriKer_sum_eq_column I x i a
  have hm : MemLp (∑ j : I, K j) 2 (volume.prod volume) :=
    he.symm ▸ memLp_qrColumnKer I x i a ha
  exact (qr_kernelOperator_finsetSum Finset.univ K hK hm).symm.trans
    (AiryTwoInt.kernelOperator_congr he hm _)

/-- The hit column solves the triangular QR system. -/
theorem qrHitColumn_system (I : Finset ℝ) (x : I → ℝ) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    (1 + airyHeatUpper I x) ∘L qrHitColumn I x a ha = airyToTagged I x a ha := by
  classical
  let Y := qrHitColumn I x a ha
  let A := airyToTagged I x a ha
  have hcoord (i : I) : airyTagOut I i ∘L ((1 + airyHeatUpper I x) ∘L Y) =
      airyTagOut I i ∘L A := by
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
      ← ContinuousLinearMap.comp_assoc (airyTagOut I i)]
    unfold airyHeatUpper
    rw [airyTagOut_comp_airyTaggedBlocks, ContinuousLinearMap.finsetSum_comp]
    simp only [ContinuousLinearMap.comp_assoc, Y, airyTagOut_comp_qrHitColumn, A, airyTagOut_comp_airyToTagged]
    let Yj (j : I) := HilbertSchmidt.kernelOperator (qr_tagWeightedHit_props I x j a ha).2
    have hdiag : airyHeatBlock I x i i ∘L Yj i = 0 := by
      rw [airyHeatBlock, dite_eq_right (lt_irrefl _), ContinuousLinearMap.zero_comp]
    refine Eq.trans ?_ (qrTriKer_sum_operator I x i a ha)
    have hsplit (j : I) : (if i = j then Yj j else airyHeatBlock I x i j ∘L Yj j) =
        (if i = j then Yj j else 0) + airyHeatBlock I x i j ∘L Yj j := by
      by_cases h : i = j
      · subst j
        simp [hdiag]
      · simp [h]
    change Yj i + (∑ j : I, airyHeatBlock I x i j ∘L Yj j) =
      ∑ j : I, if i = j then Yj j else airyHeatBlock I x i j ∘L Yj j
    rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
    simp
  calc
    _ = (∑ i : I, airyTagIn I i ∘L airyTagOut I i) ∘L ((1 + airyHeatUpper I x) ∘L Y) := by
      rw [sum_airyTagIn_comp_airyTagOut, ContinuousLinearMap.id_comp]
    _ = (∑ i : I, airyTagIn I i ∘L airyTagOut I i) ∘L A := by
      simp only [ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_assoc, hcoord]
    _ = _ := by rw [sum_airyTagIn_comp_airyTagOut, ContinuousLinearMap.id_comp]

/-- The alternating inverse applied to the Airy column is the weighted hit column. -/
theorem airyUpperInv_comp_airyToTagged_eq_hitColumn (I : Finset ℝ) (x : I → ℝ)
    (a : ℝ) (ha : airyTimeSpan I + 2 ≤ a) :
    airyUpperInv I x ∘L airyToTagged I x a ha = qrHitColumn I x a ha := by
  let L := airyHeatUpper I x
  have hn : (-L) ^ (I.card + 1) = 0 := by
    have hzero : L ^ (I.card + 1) = 0 := airyHeatUpper_nilpotent I x
    rw [HilbertSchmidt.neg_pow_clm, hzero, smul_zero]
  have h := geom_sum_mul_neg (-L) (I.card + 1)
  rw [sub_neg_eq_add, hn, sub_zero] at h
  have hi : airyUpperInv I x ∘L (1 + L) = 1 := h
  rw [← qrHitColumn_system I x a ha, ← ContinuousLinearMap.comp_assoc, hi,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

/-- Multiplication on the output coordinate preserves square integrability of a kernel. -/
theorem qr_memLp_kernel_mul_fst {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume))
    (m : ℝ → ℝ) (hm : Measurable m) (C : ℝ) (hb : ∀ t, ‖m t‖ ≤ C) :
    MemLp (fun p => m p.1 * K p) 2 (volume.prod volume) := by
  refine (hK.norm.const_mul C).mono'
    ((hm.comp measurable_fst).aestronglyMeasurable.mul hK.aestronglyMeasurable)
    (ae_of_all _ fun p => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)

/-- Postcomposition by a bounded multiplier acts on the first kernel variable. -/
theorem qr_mul_comp_kernelOperator {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume))
    (m : ℝ → ℝ) (hm : Measurable m) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t, ‖m t‖ ≤ C) :
    qrMulOp m hm C hC hb ∘L HilbertSchmidt.kernelOperator hK =
      HilbertSchmidt.kernelOperator (qr_memLp_kernel_mul_fst hK m hm C hb) := by
  ext1 f
  apply Lp.ext
  filter_upwards [qrMulOp_apply_ae m hm C hC hb (HilbertSchmidt.kernelOperator hK f),
    HilbertSchmidt.kernelOperator_apply_ae hK f,
    HilbertSchmidt.kernelOperator_apply_ae (qr_memLp_kernel_mul_fst hK m hm C hb) f]
    with s hm' hs ht
  rw [ContinuousLinearMap.comp_apply, hm', hs, ht]
  change m s * (∫ t, K (s, t) * f t) = ∫ t, (m s * K (s, t)) * f t
  simp_rw [mul_assoc, integral_const_mul]

/-- A propagated hit piece in the exponential path gauge. -/
noncomputable def qrRowHitKer (I : Finset ℝ) (x : I → ℝ) (j : I) (a : ℝ) :
    ℝ × ℝ → ℝ :=
  AiryConj.expConjKernel a (AiryConj.compKernel
    (qrHeatPropagate (airyRelativeTime I j) (qrTagPiece I x j))
    (AiryTwoInt.bAiryKer (airyTimeSpan I + 1)))

/-- The row block applied to its weighted hit piece has the exponential path kernel. -/
theorem qrRowHitKer_operator (I : Finset ℝ) (x : I → ℝ) (j : I) (a : ℝ)
    (ha : airyTimeSpan I + 2 ≤ a) :
    ∃ h : MemLp (qrRowHitKer I x j a) 2 (volume.prod volume),
      airyRowBlock I x a ha j ∘L HilbertSchmidt.kernelOperator
        (qr_tagWeightedHit_props I x j a ha).2 = HilbertSchmidt.kernelOperator h := by
  let K := qrTagPiece I x j
  let S := airyTimeSpan I + 1
  let m := 2 * airyTimeRank I j
  let r := airyRelativeTime I j
  have hH := (qr_tagWeightedHit_props I x j a ha).2
  have ha' : 0 < a := by linarith [(airyRelativeTime_bounds I j).1, (airyRelativeTime_bounds I j).2]
  have hS : 0 ≤ S := by dsimp [S]; linarith [(airyRelativeTime_bounds I j).1, (airyRelativeTime_bounds I j).2]
  have hx (p : ℝ × ℝ) (hp : p.1 ≤ x j) : K p = 0 :=
    qrHitPieces_support _ _ _ (qrTagPiece_mem I x j) p.1 p.2
      (by simpa [levelFn, j.property] using hp)
  by_cases hr : 0 < r
  · obtain ⟨hm, T, hT, hb⟩ := qrHitPieces_props _ _ (qr_sort_pairwise I) _
      (qrTagPiece_mem I x j)
    let R := qrRowHeat (x j) a r m
    have hR : MemLp R 2 (volume.prod volume) := memLp_qrRowHeat _ _ _ ha' hr _
    have hRm : Measurable R := by
      have hh : Continuous (fun p : ℝ × ℝ => heatKernel r (p.1 - p.2)) :=
        (continuous_heatKernel _).comp (continuous_fst.sub continuous_snd)
      unfold R qrRowHeat
      apply Measurable.indicator _ (measurableSet_Ioi.preimage measurable_snd)
      exact ((Real.continuous_exp.measurable.comp (measurable_fst.const_mul (-a))).mul
        hh.measurable).div (((measurable_snd.pow_const 2).const_add 1).pow_const _)
    have hcomp := AiryTwoInt.memLp_compKernel hRm (qr_tagWeightedHit_props I x j a ha).1 hR hH
    have he : AiryConj.compKernel R (qrWeightedHit K S a m) = qrRowHitKer I x j a :=
      qrRowHeat_comp_weightedHit hT hr hS hm hb (x j) hx a m
    refine ⟨he ▸ hcomp, ?_⟩
    rw [airyRowBlock, dite_eq_left hr]
    exact (AiryTwoInt.kernelOperator_compKernel hR hH hcomp).symm.trans
      (AiryTwoInt.kernelOperator_congr he hcomp _)
  · let M := qrRowZero (x j) a m
    let C := Real.exp (-a * x j)
    have hm := measurable_qrRowZero (x j) a m
    have hb := norm_qrRowZero_le (x j) a ha'.le m
    have hz : r = 0 := le_antisymm (le_of_not_gt hr) (airyRelativeTime_bounds I j).1
    have hcomp := qr_memLp_kernel_mul_fst hH M hm C hb
    have he : (fun p : ℝ × ℝ => M p.1 * qrWeightedHit K S a m p) = qrRowHitKer I x j a := by
      rw [qrRowZero_mul_weightedHit K S (x j) a m hx]
      simp [qrRowHitKer, show airyRelativeTime I j = 0 from hz, qrHeatPropagate, K, S]
    refine ⟨he ▸ hcomp, ?_⟩
    rw [airyRowBlock, dite_eq_right hr]
    exact (qr_mul_comp_kernelOperator hH M hm C (Real.exp_pos _).le hb).trans
      (AiryTwoInt.kernelOperator_congr he hcomp _)

/-- The full list starts at the minimum time and ends with padding one. -/
theorem qr_fullHitData (I : Finset ℝ) (x : I → ℝ) {e : ℝ × ℝ} {L : List (ℝ × ℝ)}
    (hEntries : finEntries I x = e :: L) :
    gapSum e L = airyTimeSpan I + 1 ∧
      hitKerN e L = ∑ j : I, qrHeatPropagate (airyRelativeTime I j) (qrTagPiece I x j) := by
  classical
  have hn : I.Nonempty := by
    by_contra h
    have hI := Finset.not_nonempty_iff_eq_empty.mp h
    subst I
    simp [finEntries, fddEntries] at hEntries
  let i : I := ⟨I.min' hn, I.min'_mem hn⟩
  have hle (j : I) : (i : ℝ) ≤ (j : ℝ) := Finset.min'_le I _ j.property
  have hfilter : (I.sort (· ≤ ·)).filter (fun t : ℝ => decide ((i : ℝ) ≤ t)) = I.sort (· ≤ ·) :=
    List.filter_eq_self.mpr fun t ht => decide_eq_true (hle ⟨t, (Finset.mem_sort _).mp ht⟩)
  have hrel (j : I) : airyRelativeTime I j = (j : ℝ) - i := by
    simp only [airyRelativeTime, airyFirstTime, dite_eq_left hn, i]
  have hzero : airyRelativeTime I i = 0 := by rw [hrel, sub_self]
  obtain ⟨e', L', hE, _, _, _, hgap⟩ := qr_suffixEntries I x i
  rw [hfilter, ← finEntries, hEntries] at hE
  rcases List.cons.inj hE with ⟨rfl, rfl⟩
  rw [hzero, sub_zero] at hgap
  refine ⟨hgap, ?_⟩
  have h := qr_hitKer_eq_tagged_sum I x i e L (by rw [hfilter]; exact hEntries)
  have hf : (Finset.univ : Finset I).filter (fun j : I => (i : ℝ) ≤ (j : ℝ)) = Finset.univ :=
    Finset.filter_true_of_mem (fun j _ => hle j)
  rw [hf] at h
  simpa only [hrel] using h

/-- The sum of the propagated row kernels is the exponentially conjugated path kernel. -/
theorem qrRowHitKer_sum_eq_path (I : Finset ℝ) (x : I → ℝ) {e : ℝ × ℝ} {L : List (ℝ × ℝ)}
    (hEntries : finEntries I x = e :: L) (he : 0 < e.2) (hL : ∀ y ∈ L, 0 < y.2) (a : ℝ) :
    (∑ j : I, qrRowHitKer I x j a) = AiryConj.expConjKernel a (fddAiryKer e L) := by
  obtain ⟨hgap, hsum⟩ := qr_fullHitData I x hEntries
  let K (j : I) := qrHeatPropagate (airyRelativeTime I j) (qrTagPiece I x j)
  let S := airyTimeSpan I + 1
  have hS : 0 ≤ S := by dsimp [S]; rw [← hgap]; exact (gapSum_pos L e he hL).le
  have hterms : ∀ j ∈ (Finset.univ : Finset I), Measurable (K j) ∧
      ∃ T : ℝ, 0 < T ∧ ∀ p, 0 ≤ K j p ∧ K j p ≤ heatKernel T (p.1 - p.2) := by
    intro j _
    obtain ⟨hm, T, hT, hb⟩ := qrHitPieces_props _ _ (qr_sort_pairwise I) _ (qrTagPiece_mem I x j)
    have hr := (airyRelativeTime_bounds I j).1
    obtain ⟨hM, hB⟩ := qrHeatPropagate_props hr hT hm hb
    exact ⟨hM, _, add_pos_of_nonneg_of_pos hr hT, hB⟩
  have hc := qr_compKernel_sum_bAiry Finset.univ K hS hterms
  rw [← hsum] at hc
  have hp : AiryConj.compKernel (hitKerN e L) (AiryTwoInt.bAiryKer S) = fddAiryKer e L := by
    dsimp [S]
    rw [← hgap]
    exact compKernel_hitKerN_bAiry e L he hL
  rw [hp] at hc
  funext p
  simp only [Finset.sum_apply, qrRowHitKer, AiryConj.expConjKernel]
  change (∑ j : I, Real.exp (-a * p.1) *
    AiryConj.compKernel (K j) (AiryTwoInt.bAiryKer S) p * Real.exp (a * p.2)) = _
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_apply, ← hc]

/-- The reduced QR operator equals the existing path-integral operator. -/
theorem airyFromTagged_comp_upperInv_comp_airyToTagged
    (I : Finset ℝ) (x : I → ℝ) {e : ℝ × ℝ} {L : List (ℝ × ℝ)}
    (hEntries : finEntries I x = e :: L)
    (he : 0 < e.2) (hL : ∀ v ∈ L, 0 < v.2) (a : ℝ)
    (ha : gapSum e L + 1 ≤ a) (haSpan : airyTimeSpan I + 2 ≤ a) :
    airyFromTagged I x a haSpan ∘L airyUpperInv I x ∘L airyToTagged I x a haSpan =
      fddOpAt e L he hL a ha := by
  rw [airyUpperInv_comp_airyToTagged_eq_hitColumn, fddOpAt_eq_kernelOperator]
  unfold qrHitColumn
  rw [ContinuousLinearMap.comp_finsetSum]
  simp only [← ContinuousLinearMap.comp_assoc, airyFromTagged_comp_airyTagIn]
  choose hK hok using fun j : I => qrRowHitKer_operator I x j a haSpan
  simp_rw [hok]
  have heq := qrRowHitKer_sum_eq_path I x hEntries he hL a
  have hsum : MemLp (∑ j : I, qrRowHitKer I x j a) 2 (volume.prod volume) :=
    heq.symm ▸ memLp_expConj_fddAiryKer e L he hL ha
  exact (qr_kernelOperator_finsetSum Finset.univ _ hK hsum).symm.trans
    (AiryTwoInt.kernelOperator_congr heq hsum _)

/-- For every finite time set and all thresholds, the literal extended Airy₁
Fredholm series is the path-integral CDF of Quastel and Remenik. -/
theorem airyExtendedSeries_eq_airy1FinCdf (I : Finset ℝ) (x : I → ℝ) :
    kernelFredholmSeries (airySiteMeasure I) (airyRankCutKer I x) = airy1FinCdf I x := by
  by_cases hn : I.Nonempty
  · have hp : 0 < (I.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]
      exact Finset.card_pos.mpr hn
    have hnil : finEntries I x ≠ [] := by
      unfold finEntries
      generalize I.sort (· ≤ ·) = ts at hp ⊢
      cases ts with
      | nil => simp at hp
      | cons t ts => cases ts <;> simp [fddEntries]
    obtain ⟨e, L, hEntries⟩ := List.exists_cons_of_ne_nil hnil
    have he : 0 < e.2 := finEntries_pos I x e (by rw [hEntries]; exact List.mem_cons_self)
    have hL : ∀ y ∈ L, 0 < y.2 := fun y hy =>
      finEntries_pos I x y (by rw [hEntries]; exact List.mem_cons_of_mem _ hy)
    let a := airyTimeSpan I + 2
    have ha : gapSum e L + 1 ≤ a := by
      rw [(qr_fullHitData I x hEntries).1]
      dsimp [a]
      linarith
    rw [airyExtendedSeries_eq_qrDet I x a le_rfl,
      airyFromTagged_comp_upperInv_comp_airyToTagged I x hEntries he hL a ha le_rfl,
      airy1FinCdf_eq_fredholmDet_fddOpAt_weight I x hEntries he hL ha]
  · have hI := Finset.not_nonempty_iff_eq_empty.mp hn
    subst I
    exact airyExtendedSeries_empty x

end AiryFdd
