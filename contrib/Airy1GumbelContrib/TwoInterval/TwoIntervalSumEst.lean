/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.AiryKernel.GaussianSaddle

/-!
# The summation step of the separated-block estimate: the two `o(ρ(M))` summation estimates

Part of `TwoInterval/`: the elementary summation half of the summation step
of the paper's separated-block estimate (step numbers in these files label the stages of the
Lean proof, not those of the posted paper).  After the determinant-side
estimate of `TwoIntervalDetRem.lean` (Steps 1/3/4), the joint-exceedance bound is a sum
over `1 ≤ r ≤ ⌊χ√(2M)⌋₊` of two terms, `C M^K (1+r)^K e^{-𝒥_M(r)}` and
`C M^K (1+r)^K e^{-2κM^{3/2}}`; this module proves that each sum, divided by the
`ρ`-profile `M^{1/4} e^{-κM^{3/2}}`, tends to `0` (`ratio`-`Tendsto` form of the
paper's two `o(ρ(M))` bounds).

## Correspondence with the paper

* `κ M^{3/2} = (2/3)(2M)^{3/2}`: `kappa_rpow_identity`.
* `𝒥_M(r) − κM^{3/2} ≥ 2Mr` (both dropped terms nonnegative):
  `two_mul_rpow_add_two_mul_le_saddleJ`, giving `e^{-𝒥_M(r)} ≤ e^{-κM^{3/2}} e^{-2Mr}`:
  `exp_neg_saddleJ_le`.
* The first sum: the reindexed geometric majorant
  `∑_{r≥1} (1+r)^K e^{-2Mr} = e^{-2M} ∑_{m≥0} (2+m)^K e^{-2Mm} ≤ C_K e^{-2M}`:
  `exists_two_add_rpow_mul_exp_neg_half_le` (the pointwise coefficient bound),
  `exists_summable_two_add_rpow_mul_exp_neg` (summability
  + `tsum` bound), `sum_Icc_one_add_rpow_mul_exp_neg_le` (the finite form).
* The first headline (the `o(ρ(M))` bound for the first sum):
  `stepFive_first_sum_ratio_tendsto_zero`.
* The second sum: `O(√M)` terms and `(1+r)^K ≤ C M^{K/2}`, giving
  `≤ C M^{K'} √M e^{-2κM^{3/2}}`: `sum_Icc_rpow_mul_exp_neg_two_kappa_le`.
* The second headline: `stepFive_second_sum_ratio_tendsto_zero`.

## Scope

The probability statement `P(A∩B) = …` of the paper's joint-determinant lemma is an
external bridge record for the main package and is not formalized in `TwoInterval/`;
this module is purely real-analytic (it consumes only `AiryConj.saddleJ` from the
operator stack).  The reindexing `r = j − 1` is done in the main package,
not here.  The profile `ρ(M)` itself is defined in the main package.

## Differences in form from the paper (none is a mathematical change)

* **ρ-profile without `C_*`**: the ratio statements divide by
  `M^{1/4} e^{-κM^{3/2}}`; the true `ρ(M) = C_* M^{1/4} e^{-κM^{3/2}}` differs
  by the constant `C_*`, and `o(·)` statements are constant-factor insensitive.
* **`r` real inside `saddleJ`**: the sums run over
  `Finset.Icc 1 ⌊χ√(2M)⌋₊` with the cast `(r : ℝ)` into `AiryConj.saddleJ M r`;
  the paper's `r ∈ ℕ` is the main package's specialization.
* **`χ > (1/2)^{1/3}` not used**: the statements take exactly
  `0 < χ`; `stepFive_first_sum_ratio_tendsto_zero` does not even use the upper range
  of the sum (the `Icc 1 N` bound is uniform in `N`), so `hχ0` is regime-matching
  only there.
* **Existential constants**: the paper's unnamed `C, K, K'` are
  packaged as existentials with `K : ℝ`, `0 ≤ K` where rpow-monotonicity needs it.
-/

namespace AiryTwoInt

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal

/-! ### The `κ` identity -/

/-- `(2/3)·(2M)^{3/2} = (4√2/3)·M^{3/2}` for `0 ≤ M`: `κ M^{3/2} = (2/3)(2M)^{3/2}` with `κ = 4√2/3`
(not a named
constant in contrib). -/
theorem kappa_rpow_identity {M : ℝ} (hM : 0 ≤ M) :
    (2/3) * (2*M)^(3/2 : ℝ) = (4 * Real.sqrt 2 / 3) * M^(3/2 : ℝ) := by
  have h2 : (2:ℝ)^(3/2 : ℝ) = 2 * Real.sqrt 2 := by
    rw [show (3/2 : ℝ) = 1 + 1/2 from by norm_num, Real.rpow_add (by norm_num),
      Real.rpow_one, Real.sqrt_eq_rpow]
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hM, h2]
  ring

/-! ### Step 5, first half: the `e^{-𝒥_M(r)}` sum -/

/-- Dropping the two nonnegative terms:
`(2/3)(2M)^{3/2} + 2Mr ≤ 𝒥_M(r)` for `0 ≤ M`, `0 ≤ r`, since
`(2M+r²)^{3/2} ≥ (2M)^{3/2}` (rpow monotonicity) and `(2/3)r³ ≥ 0`. -/
theorem two_mul_rpow_add_two_mul_le_saddleJ {M r : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r) :
    (2/3)*(2*M)^(3/2 : ℝ) + 2*M*r ≤ AiryConj.saddleJ M r := by
  have h1 : (2*M)^(3/2 : ℝ) ≤ (2*M + r^2)^(3/2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [sq_nonneg r]) (by norm_num)
  have h2 : (0:ℝ) ≤ (2/3) * r^3 := by positivity
  unfold AiryConj.saddleJ
  linarith [mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2/3)]

/-- **Exponential bound**: `e^{-𝒥_M(r)} ≤ e^{-κM^{3/2}} e^{-2Mr}`
for `0 ≤ M`, `0 ≤ r`. -/
theorem exp_neg_saddleJ_le {M r : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r) :
    Real.exp (-AiryConj.saddleJ M r)
      ≤ Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)) * Real.exp (-2*M*r) := by
  have hle := two_mul_rpow_add_two_mul_le_saddleJ hM hr
  rw [kappa_rpow_identity hM] at hle
  have hsplit : Real.exp (-((4 * Real.sqrt 2 / 3) * M ^ (3/2 : ℝ) + 2 * M * r))
      = Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)) * Real.exp (-(2*M*r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show -(2*M*r) = -2*M*r from by ring] at hsplit
  exact (Real.exp_le_exp.mpr (neg_le_neg hle)).trans_eq hsplit

/-! ### The geometric-majorant machinery -/

/-- Boundedness of the geometric-majorant coefficients: the null sequence
`(2+m)^K e^{-(1/2)(2+m)}` (a shift of mathlib's `x^K e^{-x/2} → 0`) is bounded, hence so
is `(2+m)^K e^{-m/2} = e · (2+m)^K e^{-(1/2)(2+m)}`. -/
theorem exists_two_add_rpow_mul_exp_neg_half_le (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, (2+(m:ℝ))^(K:ℝ) * Real.exp (-(m:ℝ)/2) ≤ C := by
  have htend : Tendsto (fun n : ℕ => (2 + (n:ℝ))^(K:ℝ) * Real.exp (-(1/2)*(2 + (n:ℝ))))
      atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero K (1/2) (by norm_num)
    exact h.comp (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have hev : ∀ᶠ n : ℕ in atTop,
      (2 + (n:ℝ))^(K:ℝ) * Real.exp (-(1/2)*(2 + (n:ℝ))) < 1 :=
    htend.eventually (Iio_mem_nhds one_pos)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  set B := ∑ n ∈ Finset.range N,
    (2 + (n:ℝ))^(K:ℝ) * Real.exp (-(1/2)*(2 + (n:ℝ))) with hB
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun n _ => by positivity
  have hterm_nn : ∀ n : ℕ, 0 ≤ (2 + (n:ℝ))^(K:ℝ) * Real.exp (-(1/2)*(2 + (n:ℝ))) :=
    fun n => by positivity
  refine ⟨Real.exp 1 * (B + 1), by positivity, fun m => ?_⟩
  have hid : (2+(m:ℝ))^(K:ℝ) * Real.exp (-(m:ℝ)/2)
      = Real.exp 1 * ((2 + (m:ℝ))^(K:ℝ) * Real.exp (-(1/2)*(2 + (m:ℝ)))) := by
    rw [show (-(1/2 : ℝ))*(2 + (m:ℝ)) = -1 + (-(m:ℝ)/2) from by ring, Real.exp_add,
      show (-1 : ℝ) = -(1 : ℝ) from rfl, Real.exp_neg]
    have h1 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    field_simp [h1.ne']
  rw [hid]
  rcases lt_or_ge m N with hm | hm
  · have hle : (2 + (m:ℝ))^(K:ℝ) * Real.exp (-(1/2)*(2 + (m:ℝ))) ≤ B :=
      Finset.single_le_sum (fun i _ => hterm_nn i) (Finset.mem_range.mpr hm)
    calc Real.exp 1 * ((2 + (m:ℝ))^(K:ℝ) * Real.exp (-(1/2)*(2 + (m:ℝ))))
        ≤ Real.exp 1 * B := mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
      _ ≤ Real.exp 1 * (B + 1) := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  · have hle : (2 + (m:ℝ))^(K:ℝ) * Real.exp (-(1/2)*(2 + (m:ℝ))) ≤ 1 := (hN m hm).le
    calc Real.exp 1 * ((2 + (m:ℝ))^(K:ℝ) * Real.exp (-(1/2)*(2 + (m:ℝ))))
        ≤ Real.exp 1 * 1 := mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
      _ ≤ Real.exp 1 * (B + 1) := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

/-- Summability and the `tsum` bound for the geometric majorant: for `1 ≤ M`,
`e^{-2Mm} ≤ e^{-m} = e^{-m/2}·e^{-m/2}`, so termwise
`(2+m)^K e^{-2Mm} ≤ C₀·(e^{-1/2})^m` and the sum is at most `C₀·(1−e^{-1/2})⁻¹`. -/
theorem exists_summable_two_add_rpow_mul_exp_neg (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M →
      Summable (fun m : ℕ => (2+(m:ℝ))^(K:ℝ) * Real.exp (-2*M*(m:ℝ))) ∧
      ∑' m : ℕ, (2+(m:ℝ))^(K:ℝ) * Real.exp (-2*M*(m:ℝ)) ≤ C := by
  obtain ⟨C₀, hC₀, hC₀bound⟩ := exists_two_add_rpow_mul_exp_neg_half_le K
  have hE : Real.exp (-1/2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hE0 : (0:ℝ) ≤ Real.exp (-1/2 : ℝ) := (Real.exp_pos _).le
  have h1E : (0:ℝ) < 1 - Real.exp (-1/2 : ℝ) := by linarith
  refine ⟨C₀ * (1 - Real.exp (-1/2))⁻¹, by positivity, fun M hM => ?_⟩
  have hpt : ∀ m : ℕ, (2+(m:ℝ))^(K:ℝ) * Real.exp (-2*M*(m:ℝ))
      ≤ C₀ * (Real.exp (-1/2))^m := by
    intro m
    have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    have h1 : Real.exp (-2*M*(m:ℝ)) ≤ Real.exp (-(m:ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hM, hm]
    have h2 : (0:ℝ) ≤ (2+(m:ℝ))^(K:ℝ) := Real.rpow_nonneg (by positivity) _
    have h3 : Real.exp (-(m:ℝ)) = Real.exp (-(m:ℝ)/2) * Real.exp (-(m:ℝ)/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc (2+(m:ℝ))^(K:ℝ) * Real.exp (-2*M*(m:ℝ))
        ≤ (2+(m:ℝ))^(K:ℝ) * Real.exp (-(m:ℝ)) := mul_le_mul_of_nonneg_left h1 h2
      _ = ((2+(m:ℝ))^(K:ℝ) * Real.exp (-(m:ℝ)/2)) * Real.exp (-(m:ℝ)/2) := by
          rw [h3]
          ring
      _ ≤ C₀ * Real.exp (-(m:ℝ)/2) :=
          mul_le_mul_of_nonneg_right (hC₀bound m) (Real.exp_pos _).le
      _ = C₀ * (Real.exp (-1/2))^m := by
          congr 1
          rw [show (-(m:ℝ)/2) = (m:ℝ) * (-1/2) from by ring, Real.exp_nat_mul]
  have hdom : Summable fun m : ℕ => C₀ * (Real.exp (-1/2))^m :=
    (summable_geometric_of_lt_one hE0 hE).mul_left C₀
  have hsum : Summable fun m : ℕ => (2+(m:ℝ))^(K:ℝ) * Real.exp (-2*M*(m:ℝ)) :=
    Summable.of_nonneg_of_le (fun m => by positivity) hpt hdom
  refine ⟨hsum, ?_⟩
  calc ∑' m : ℕ, (2+(m:ℝ))^(K:ℝ) * Real.exp (-2*M*(m:ℝ))
      ≤ ∑' m : ℕ, C₀ * (Real.exp (-1/2))^m := hsum.tsum_le_tsum hpt hdom
    _ = C₀ * (1 - Real.exp (-1/2))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hE0 hE]

/-- The `Icc 1 N → range N` reindexing `r = m + 1` (no `Finset.sum_Icc_eq_sum_range` at
this pin; proved by induction from `Finset.sum_Icc_succ_top`). -/
theorem sum_Icc_one_eq_sum_range_add_one (f : ℕ → ℝ) (N : ℕ) :
    ∑ r ∈ Finset.Icc 1 N, f r = ∑ m ∈ Finset.range N, f (m + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- **The finite first-sum bound**: factor `e^{-2M}` out of the reindexed
sum and bound the rest by the geometric majorant `tsum`. -/
theorem sum_Icc_one_add_rpow_mul_exp_neg_le (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (N : ℕ), 1 ≤ M →
      ∑ r ∈ Finset.Icc 1 N, (1+(r:ℝ))^(K:ℝ) * Real.exp (-2*M*(r:ℝ))
        ≤ C * Real.exp (-2*M) := by
  obtain ⟨C₃, hC₃, hC₃bound⟩ := exists_summable_two_add_rpow_mul_exp_neg K
  refine ⟨C₃, hC₃, fun M N hM => ?_⟩
  obtain ⟨hsumM, hboundM⟩ := hC₃bound M hM
  have hreidx : ∑ r ∈ Finset.Icc 1 N, (1+(r:ℝ))^(K:ℝ) * Real.exp (-2*M*(r:ℝ))
      = Real.exp (-2*M) * ∑ m ∈ Finset.range N,
          (2+(m:ℝ))^(K:ℝ) * Real.exp (-2*M*(m:ℝ)) := by
    rw [sum_Icc_one_eq_sum_range_add_one (fun r => (1+(r:ℝ))^(K:ℝ) * Real.exp (-2*M*(r:ℝ))) N]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    push_cast
    have h2 : Real.exp (-2*M*((m:ℝ)+1)) = Real.exp (-2*M) * Real.exp (-2*M*(m:ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show (1:ℝ) + ((m:ℝ) + 1) = 2 + (m:ℝ) from by ring, h2]
    ring
  rw [hreidx]
  have hsum := hsumM.sum_le_tsum (Finset.range N) (fun m _ => by positivity)
  calc Real.exp (-2*M) * ∑ m ∈ Finset.range N, (2+(m:ℝ))^(K:ℝ) * Real.exp (-2*M*(m:ℝ))
      ≤ Real.exp (-2*M) * ∑' m : ℕ, (2+(m:ℝ))^(K:ℝ) * Real.exp (-2*M*(m:ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ ≤ Real.exp (-2*M) * C₃ := mul_le_mul_of_nonneg_left hboundM (Real.exp_pos _).le
    _ = C₃ * Real.exp (-2*M) := by ring

/-- **The first `o(ρ(M))` headline** (the paper's `o(ρ(M))` bound for the first sum): the
`e^{-𝒥_M(r)}` half of the Step-4 bound summed over `1 ≤ r ≤ ⌊χ√(2M)⌋₊`, divided by the
ρ-profile `M^{1/4} e^{-κM^{3/2}}` (without the constant `C_*`; see the module docstring), tends to
`0`.  Termwise `e^{-𝒥_M(r)} ≤ e^{-κM^{3/2}} e^{-2Mr}` (`exp_neg_saddleJ_le`), the sum is
`≤ C₄ e^{-2M}` (`sum_Icc_one_add_rpow_mul_exp_neg_le`), the `e^{-κM^{3/2}}` cancels, and
`M^{K-1/4} e^{-2M} → 0`.  (`hχ0` is regime-matching: the bound route uses only
`M ≥ 1` — the `Icc 1 N` estimate is uniform in `N`.) -/
theorem stepFive_first_sum_ratio_tendsto_zero (C K : ℝ) (hχ0 : 0 < χ) :
    Tendsto (fun M : ℝ =>
      (C * M^K * ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
          (1+(r:ℝ))^(K:ℝ) * Real.exp (-AiryConj.saddleJ M (r:ℝ)))
        / (M^(1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ))))
      atTop (𝓝 0) := by
  obtain ⟨C₄, hC₄, hS4⟩ := sum_Icc_one_add_rpow_mul_exp_neg_le K
  have hmajor : Tendsto (fun M : ℝ => (|C| * C₄) * (M^(K - 1/4 : ℝ) * Real.exp (-2*M)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (K - 1/4) 2 two_pos).const_mul
      (|C| * C₄)
    rwa [mul_zero] at h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun M => abs_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hM0 : (0:ℝ) < M := lt_of_lt_of_le one_pos hM
  have hD : (0:ℝ) < M^(1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)) :=
    mul_pos (Real.rpow_pos_of_pos hM0 _) (Real.exp_pos _)
  have hSnn : 0 ≤ ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
      (1+(r:ℝ))^(K:ℝ) * Real.exp (-AiryConj.saddleJ M (r:ℝ)) :=
    Finset.sum_nonneg fun r _ => by positivity
  have hSbound : ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
        (1+(r:ℝ))^(K:ℝ) * Real.exp (-AiryConj.saddleJ M (r:ℝ))
      ≤ Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)) * (C₄ * Real.exp (-2*M)) := by
    calc ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
          (1+(r:ℝ))^(K:ℝ) * Real.exp (-AiryConj.saddleJ M (r:ℝ))
        ≤ ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊, (1+(r:ℝ))^(K:ℝ)
            * (Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)) * Real.exp (-2*M*(r:ℝ))) := by
          apply Finset.sum_le_sum
          intro r hr
          have hr1 : (1:ℝ) ≤ (r:ℝ) := by
            have := (Finset.mem_Icc.mp hr).1
            exact Nat.one_le_cast.mpr this
          exact mul_le_mul_of_nonneg_left
            (exp_neg_saddleJ_le hM0.le (by linarith))
            (Real.rpow_nonneg (by linarith) _)
      _ = Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ))
            * ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
              (1+(r:ℝ))^(K:ℝ) * Real.exp (-2*M*(r:ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
      _ ≤ Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)) * (C₄ * Real.exp (-2*M)) :=
          mul_le_mul_of_nonneg_left (hS4 M ⌊χ * Real.sqrt (2*M)⌋₊ hM) (Real.exp_pos _).le
  have hE : (0:ℝ) < Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)) := Real.exp_pos _
  have hM14 : (0:ℝ) < M^(1/4 : ℝ) := Real.rpow_pos_of_pos hM0 _
  have hsub : M^(K - 1/4 : ℝ) = M^K / M^(1/4:ℝ) := Real.rpow_sub hM0 _ _
  calc |(C * M^K * ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
            (1+(r:ℝ))^(K:ℝ) * Real.exp (-AiryConj.saddleJ M (r:ℝ)))
          / (M^(1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)))|
      = |C| * M^K * (∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
            (1+(r:ℝ))^(K:ℝ) * Real.exp (-AiryConj.saddleJ M (r:ℝ)))
          / (M^(1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
        rw [abs_div, abs_of_pos hD, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hM0.le _),
          abs_of_nonneg hSnn]
    _ ≤ |C| * M^K * (Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)) * (C₄ * Real.exp (-2*M)))
          / (M^(1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSbound
            (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hM0.le _))) hD.le
    _ = (|C| * C₄) * (M^(K - 1/4 : ℝ) * Real.exp (-2*M)) := by
        rw [hsub]
        field_simp [hE.ne', hM14.ne']

/-- **The second sum bound**: the summand is `r`-independent up to the
`(1+r)^K` factor; `card (Icc 1 ⌊χ√(2M)⌋₊) ≤ χ√2·M^{1/2}` (`Nat.card_Icc`,
`Nat.floor_le`, `√(2M) = √2·√M`) and `(1+r)^K ≤ (1+χ√2)^K · M^{K/2}` (rpow
monotonicity, `0 ≤ K`) give `≤ C' M^{(K+1)/2} e^{-2κM^{3/2}}`. -/
theorem sum_Icc_rpow_mul_exp_neg_two_kappa_le (K : ℝ) (hK : 0 ≤ K) (hχ0 : 0 < χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M →
      ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
          (1+(r:ℝ))^(K:ℝ) * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ)))
        ≤ C * M^((K+1)/2 : ℝ) * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
  have hχ2 : (0:ℝ) < 1 + χ * Real.sqrt 2 := by positivity
  refine ⟨χ * Real.sqrt 2 * (1 + χ * Real.sqrt 2)^(K:ℝ), by positivity, fun M hM => ?_⟩
  have hM0 : (0:ℝ) < M := lt_of_lt_of_le one_pos hM
  have hMnn : (0:ℝ) ≤ M := hM0.le
  have hχsq : (0:ℝ) ≤ χ * Real.sqrt (2*M) := by positivity
  have hN : (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ) ≤ χ * Real.sqrt (2*M) := Nat.floor_le hχsq
  have hsqrt : Real.sqrt (2*M) = Real.sqrt 2 * Real.sqrt M :=
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) M
  have hN' : (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ) ≤ χ * Real.sqrt 2 * M^(1/2 : ℝ) := by
    calc (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ) ≤ χ * Real.sqrt (2*M) := hN
      _ = χ * Real.sqrt 2 * M^(1/2 : ℝ) := by rw [hsqrt, Real.sqrt_eq_rpow M]; ring
  -- the termwise bound
  have hsummand : ∀ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
      (1+(r:ℝ))^(K:ℝ) ≤ (1 + (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ))^(K:ℝ) := by
    intro r hr
    have hrN : (r:ℝ) ≤ (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ) :=
      Nat.cast_le.mpr (Finset.mem_Icc.mp hr).2
    exact Real.rpow_le_rpow (by positivity) (by linarith) hK
  have hsum : ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊, (1+(r:ℝ))^(K:ℝ)
      ≤ ⌊χ * Real.sqrt (2*M)⌋₊ * (1 + (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ))^(K:ℝ) := by
    calc ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊, (1+(r:ℝ))^(K:ℝ)
        ≤ ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
            (1 + (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ))^(K:ℝ) := Finset.sum_le_sum hsummand
      _ = (Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊).card •
            (1 + (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ))^(K:ℝ) := Finset.sum_const _
      _ = ⌊χ * Real.sqrt (2*M)⌋₊ * (1 + (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ))^(K:ℝ) := by
          rw [Nat.card_Icc, show ⌊χ * Real.sqrt (2*M)⌋₊ + 1 - 1 = ⌊χ * Real.sqrt (2*M)⌋₊ from
            Nat.add_sub_cancel _ _, nsmul_eq_mul]
  have h1N : (1 + (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ))^(K:ℝ)
      ≤ (1 + χ * Real.sqrt 2)^(K:ℝ) * M^(K/2 : ℝ) := by
    have hbase : 1 + (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ) ≤ (1 + χ * Real.sqrt 2) * Real.sqrt M := by
      have h2 : (1:ℝ) ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM
      have h1 : (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ) ≤ χ * Real.sqrt 2 * Real.sqrt M :=
        hN.trans (le_of_eq (by rw [hsqrt]; ring))
      calc 1 + (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ)
          ≤ Real.sqrt M + (χ * Real.sqrt 2 * Real.sqrt M) := add_le_add h2 h1
        _ = (1 + χ * Real.sqrt 2) * Real.sqrt M := by ring
    calc (1 + (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ))^(K:ℝ)
        ≤ ((1 + χ * Real.sqrt 2) * Real.sqrt M)^(K:ℝ) :=
          Real.rpow_le_rpow (by positivity) hbase hK
      _ = (1 + χ * Real.sqrt 2)^(K:ℝ) * (Real.sqrt M)^(K:ℝ) :=
          Real.mul_rpow hχ2.le (Real.sqrt_nonneg _)
      _ = (1 + χ * Real.sqrt 2)^(K:ℝ) * M^(K/2 : ℝ) := by
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hMnn]
          congr 1
          ring
  have hnn2 : (0:ℝ) ≤ χ * Real.sqrt 2 * M^(1/2 : ℝ) := by positivity
  calc ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
        (1+(r:ℝ))^(K:ℝ) * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ)))
      = (∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊, (1+(r:ℝ))^(K:ℝ))
          * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ (⌊χ * Real.sqrt (2*M)⌋₊ * (1 + (⌊χ * Real.sqrt (2*M)⌋₊ : ℝ))^(K:ℝ))
          * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) :=
        mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
    _ ≤ ((χ * Real.sqrt 2 * M^(1/2 : ℝ)) * ((1 + χ * Real.sqrt 2)^(K:ℝ) * M^(K/2 : ℝ)))
          * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul hN' h1N (Real.rpow_nonneg (by positivity) _) hnn2
    _ = (χ * Real.sqrt 2 * (1 + χ * Real.sqrt 2)^(K:ℝ)) * M^((K+1)/2 : ℝ)
          * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
        rw [show (K+1)/2 = (1/2 + K/2 : ℝ) from by ring,
          Real.rpow_add hM0]
        ring

/-- **The second `o(ρ(M))` headline**: the quadratic-remainder sum
`∑_{r} C M^K (1+r)^K e^{-2κM^{3/2}}` divided by the ρ-profile tends to `0`: the ratio
is `≤ C'' M^{3K/2+1/4} e^{-κM^{3/2}} ≤ C'' M^{3K/2+1/4} e^{-κM}` for `M ≥ 1`
(`M^{3/2} ≥ M`), and `x^s e^{-κx} → 0`. -/
theorem stepFive_second_sum_ratio_tendsto_zero (C K : ℝ) (hK : 0 ≤ K) (hχ0 : 0 < χ) :
    Tendsto (fun M : ℝ =>
      (C * M^K * ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
          (1+(r:ℝ))^(K:ℝ) * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))))
        / (M^(1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ))))
      atTop (𝓝 0) := by
  obtain ⟨C', hC', hS7⟩ := sum_Icc_rpow_mul_exp_neg_two_kappa_le K hK hχ0
  have hmajor : Tendsto
      (fun M : ℝ => (|C| * C') * (M^((3*K)/2 + 1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3)*M)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((3*K)/2 + 1/4)
      (4*Real.sqrt 2/3) (by positivity)).const_mul (|C| * C')
    rwa [mul_zero] at h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun M => abs_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hM0 : (0:ℝ) < M := lt_of_lt_of_le one_pos hM
  have hD : (0:ℝ) < M^(1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)) :=
    mul_pos (Real.rpow_pos_of_pos hM0 _) (Real.exp_pos _)
  have hSnn : 0 ≤ ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
      (1+(r:ℝ))^(K:ℝ) * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) :=
    Finset.sum_nonneg fun r _ => by positivity
  have hE : (0:ℝ) < Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)) := Real.exp_pos _
  have hE2 : (0:ℝ) < Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := Real.exp_pos _
  have hM14 : (0:ℝ) < M^(1/4 : ℝ) := Real.rpow_pos_of_pos hM0 _
  -- the exponential ratio: `e^{-2κX} / e^{-κX} = e^{-κX}` with `X = M^{3/2}`
  have hE12 : Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ)))
      = Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ))
        * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  -- `e^{-κM^{3/2}} ≤ e^{-κM}` for `M ≥ 1`
  have hexp : Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ))
      ≤ Real.exp (-(4*Real.sqrt 2/3) * M) := by
    apply Real.exp_le_exp.mpr
    have h32 : M ≤ M^(3/2 : ℝ) := by
      calc M = M^(1 : ℝ) := (Real.rpow_one M).symm
        _ ≤ M^(3/2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM (by norm_num)
    have hκ : (0:ℝ) ≤ 4*Real.sqrt 2/3 := by positivity
    rw [neg_mul, neg_mul]
    exact neg_le_neg (mul_le_mul_of_nonneg_left h32 hκ)
  calc |(C * M^K * ∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
            (1+(r:ℝ))^(K:ℝ) * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))))
          / (M^(1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)))|
      = |C| * M^K * (∑ r ∈ Finset.Icc 1 ⌊χ * Real.sqrt (2*M)⌋₊,
            (1+(r:ℝ))^(K:ℝ) * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))))
          / (M^(1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
        rw [abs_div, abs_of_pos hD, abs_mul, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg hM0.le _), abs_of_nonneg hSnn]
    _ ≤ |C| * M^K * (C' * M^((K+1)/2 : ℝ) * Real.exp (-2 * ((4*Real.sqrt 2/3) * M^(3/2 : ℝ))))
          / (M^(1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hS7 M hM)
            (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hM0.le _))) hD.le
    _ = (|C| * C') * (M^((3*K)/2 + 1/4 : ℝ)
          * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ))) := by
        have hMK2 : M^K * M^((K+1)/2 : ℝ) / M^(1/4 : ℝ) = M^((3*K)/2 + 1/4 : ℝ) := by
          rw [← Real.rpow_add hM0, ← Real.rpow_sub hM0]
          congr 1
          ring
        have halg : |C| * M^K * (C' * M^((K+1)/2 : ℝ)
              * (Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ))
                * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ))))
            / (M^(1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)))
          = |C| * C' * (M^K * M^((K+1)/2 : ℝ) / M^(1/4 : ℝ))
              * Real.exp (-(4*Real.sqrt 2/3) * M^(3/2 : ℝ)) := by
          field_simp [hE.ne', hM14.ne']
        rw [hE12, halg, hMK2]
        ring
    _ ≤ (|C| * C') * (M^((3*K)/2 + 1/4 : ℝ) * Real.exp (-(4*Real.sqrt 2/3)*M)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hM0.le _))
          (mul_nonneg (abs_nonneg _) hC'.le)

end AiryTwoInt
