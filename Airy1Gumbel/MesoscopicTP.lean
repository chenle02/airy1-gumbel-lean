/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.MesoscopicSum

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators NNReal

namespace Airy1Gumbel

/-!
# The `mesoscopic` field from the two-point bound TP

`MesoscopicBounds` (`MesoscopicSpec.lean`) feeds the `mesoscopic` field through two fields that
come from records: the Newman pair bound `pair` (from `ProcessAssociated`) and the covariance
decay `cov_decay` (from `CubicCovarianceDecay`). This file replaces both by one field `pairTP`,
the two-point bound TP (`TwoPointBound.lean`, `pairTP_airy1SRP_field`):
for `v ≥ w₀`, `x + 1 ≤ y`,
`P(W x > v, W y > v) ≤ P(W 0 > v)² + C e^{−I(v) − 2v(y−x) + C'(1 + v + (y−x)²)}`,
`I(v) = (2/3)(2v)^{3/2}`. The fields `cover`, `one_point` and `sharp_tail` are unchanged.

## The arithmetic

At level `v − 1` and grid points of blocks `0` and `j` (gap `d ∈ [j − 1, j + 1]`) the TP term is
at most `C e^{−2(v−1)m + C'(v + Q²)}` for any `1 ≤ m ≤ j − 1` and `j + 1 ≤ Q`
(`MesoscopicBoundsTP.block_pair_le_TP`; the rate `I(v−1) ≥ 0` is dropped). The TP exponent
`−2(v−1)(j−1) + C'(j+1)²` is not monotone in `j`, so the two pieces are bounded separately, by
`m = m_N` and `Q = q_N + 1`. With `a = √(2u_N)`:
`N ≤ K e^{(2/3)a³}`, `m_N ≥ χa − 1`, `q_N = O(a)` (`meso_qN_le_linear`, by rpow monotonicity
on `(log N)^{1/3}`; the crude `q_N ≤ C_q a³` would give `C'(q_N+1)² = O(a⁶)`), `n² = O(a¹⁶)`.
The term-3 exponent is `(2/3)a³ − (a² − 2)(χa − 1) + O(a²) = −(χ − 2/3)a³ + O(a²)`
(`meso_exponent_TP`), negative for large `a` because `χ > (1/2)^{1/3} > 2/3`. The θ-window and
`mesoTheta` are not used.

## Main results

* `MesoscopicBoundsTP`, `PairTPBound`: the bundle.
* `MesoscopicBoundsTP.block_pair_le_TP`: the per-pair envelope `mesoPairEnvelopeTP`.
* `meso_qN_le_linear`: `q_N ≤ (A(1+B) + 1) a` when `log N ≤ B a³`.
* `meso_exponent_TP`, `meso_envelope_tendsto_zero_TP`: the real analysis.
* `mesoscopic_of_boundsTP`: EXACTLY the field `Airy1BlockExtremes.mesoscopic`.
-/

/-! ## The bundle -/

/-- The two-point bound TP as a property of a process `W` under `P` (the `pairTP` field,
with the signs `0 ≤ w₀`, `0 < C`, `0 ≤ C'` exported). -/
def PairTPBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ → Ω → ℝ) : Prop :=
  ∃ w₀ C C' : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ 0 ≤ C' ∧ ∀ x y v : ℝ, w₀ ≤ v → x + 1 ≤ y →
    P.real {ω | W x ω > v ∧ W y ω > v} ≤
      P.real {ω | W 0 ω > v} ^ 2 +
        C * Real.exp (-((2 / 3) * (2 * v) ^ (3 / 2 : ℝ)) - 2 * v * (y - x)
          + C' * (1 + v + (y - x) ^ 2))

/-- `MesoscopicBounds` with `pair` and `cov_decay` replaced by the two-point bound `pairTP`.
`cover`, `one_point` and `sharp_tail` are as in `MesoscopicBounds`. -/
structure MesoscopicBoundsTP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (W : ℝ → Ω → ℝ) where
  /-- Modulus amplitude. -/
  modC : ℝ
  modC_pos : 0 < modC
  /-- Modulus rate. -/
  modc : ℝ
  modc_pos : 0 < modc
  /-- Level threshold of the covering. -/
  coverLevel : ℝ
  /-- (A) Block-to-grid covering, as in `MesoscopicBounds.cover`. -/
  cover : ∀ᶠ n : ℕ in atTop, ∀ (j : ℕ) (v : ℝ), coverLevel ≤ v →
    P.real {ω | Y 0 ω > v ∧ Y j ω > v} ≤
      (∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
        P.real {ω | W (gridPt 0 n k) ω > v - 1 ∧ W (gridPt j n k') ω > v - 1}) +
      2 * ((n : ℝ) + 1) * modFail modC modc n
  /-- (B') The two-point bound TP (replaces `pair` and `cov_decay`). -/
  pairTP : PairTPBound P W
  /-- One-point tail below the block tail. -/
  one_point : ∀ w : ℝ, P.real {ω | W 0 ω > w} ≤ P.real {ω | Y 0 ω > w}
  /-- The sharp block tail `ℙ(Y₀ > u) ~ e^{-H(u)}`. -/
  sharp_tail :
    Tendsto (fun u : ℝ => P.real {ω | Y 0 ω > u} / Real.exp (-airyH u)) atTop (𝓝 1)

/-- Per-block-pair envelope from TP:
`(n+1)² (p² + C e^{−2(v−1)m + C'(v + Q²)}) + 2 (n+1) modFail C₀ c₀ n`
(`m ≤ j − 1`, `j + 1 ≤ Q`). -/
noncomputable def mesoPairEnvelopeTP (p C C' C₀ c₀ : ℝ) (n : ℕ) (v m Q : ℝ) : ℝ :=
  ((n : ℝ) + 1) ^ 2 * (p ^ 2 + C * Real.exp (-(2 * (v - 1) * m) + C' * (v + Q ^ 2))) +
    2 * ((n : ℝ) + 1) * modFail C₀ c₀ n

/-! ## Arithmetic -/

section MesoArithTP

/-- `χ > 2/3` on the field's `χ` range (`(1/2)^{1/3} ≈ 0.794`). -/
theorem two_thirds_lt_of_rpow_lt {χ : ℝ} (hχ : (1 / 2 : ℝ) ^ ((1 : ℝ) / 3) < χ) :
    2 / 3 < χ := by
  have h3 := one_half_lt_cube_of_lt hχ
  by_contra hc
  replace hc := not_lt.mp hc
  have hχ0 : 0 < χ := lt_trans (Real.rpow_pos_of_pos (by norm_num) _) hχ
  have := pow_le_pow_left₀ hχ0.le hc 3
  norm_num at this
  linarith

/-- **`q_N = O(a)`**: if `log N ≤ B x³`
with `x ≥ 1`, then `q_N = ⌈A (log N)^{1/3}⌉ ≤ (A(1+B) + 1) x`. By rpow monotonicity,
`(log N)^{1/3} ≤ B^{1/3} x`, and `B^{1/3} ≤ 1 + B`. -/
theorem meso_qN_le_linear {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 1 ≤ x) {N : ℕ}
    (hN : Real.log N ≤ B * x ^ 3) : (qN A N : ℝ) ≤ (A * (1 + B) + 1) * x := by
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hx0 : 0 ≤ x := by linarith
  have hq : (qN A N : ℝ) < A * Real.log N ^ ((1 : ℝ) / 3) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h1 : Real.log N ^ ((1 : ℝ) / 3) ≤ (B * x ^ 3) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hlog0 hN (by norm_num)
  have h2 : (B * x ^ 3) ^ ((1 : ℝ) / 3) = B ^ ((1 : ℝ) / 3) * x := by
    rw [Real.mul_rpow hB (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have h3 : B ^ ((1 : ℝ) / 3) ≤ 1 + B := meso_rpow_third_le hB
  have h4 : B ^ ((1 : ℝ) / 3) * x ≤ (1 + B) * x := mul_le_mul_of_nonneg_right h3 hx0
  have h5 : A * Real.log N ^ ((1 : ℝ) / 3) ≤ A * ((1 + B) * x) :=
    mul_le_mul_of_nonneg_left (h1.trans (h2 ▸ h4)) hA
  nlinarith

/-- Exponent of term 3 under TP: for `χ > 0`, `a ≥ 1` and
`E + 2χ + 2 ≤ (χ − 2/3) a`, `(2/3) a³ − (a² − 2)(χ a − 1) + E a² ≤ −a`. -/
theorem meso_exponent_TP {a χ E : ℝ} (hχ : 0 < χ) (ha1 : 1 ≤ a)
    (ha : E + 2 * χ + 2 ≤ (χ - 2 / 3) * a) :
    2 / 3 * a ^ 3 - (a ^ 2 - 2) * (χ * a - 1) + E * a ^ 2 ≤ -a := by
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have h1 : (E + 2 * χ + 2) * a ^ 2 ≤ (χ - 2 / 3) * a * a ^ 2 :=
    mul_le_mul_of_nonneg_right ha ha2
  have h2 : a ≤ a ^ 2 := by nlinarith
  have h3 : χ * a ≤ χ * a ^ 2 := mul_le_mul_of_nonneg_left h2 hχ.le
  nlinarith

end MesoArithTP

/-! ## Step 1: the per-pair envelope -/

section MesoSumTP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Per-pair envelope from TP** (clone of `MesoscopicBounds.block_pair_le`): for every block
index `j`, level `v ≥ max(coverLevel, w₀ + 1)` and reals `1 ≤ m ≤ j − 1`, `j + 1 ≤ Q`,
`P(Y₀ > v, Y_j > v) ≤ mesoPairEnvelopeTP (P(Y₀ > v − 2)) C C' modC modc n v m Q`.
Uses `cover`, `pairTP` at level `v − 1` (grid gap `d ∈ [j − 1, j + 1]`, so `d ≥ m ≥ 1`),
`P(W₀ > v − 1) ≤ P(W₀ > v − 2) ≤ P(Y₀ > v − 2)` (`one_point`), `I(v − 1) ≥ 0`,
`(v−1)d ≥ (v−1)m` and `d² ≤ Q²`. -/
theorem MesoscopicBoundsTP.block_pair_le_TP {Y : ℕ → Ω → ℝ} {W : ℝ → Ω → ℝ}
    (b : MesoscopicBoundsTP P Y W) :
    ∃ w₀ C C' : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ 0 ≤ C' ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (j : ℕ) (v m Q : ℝ), b.coverLevel ≤ v → w₀ + 1 ≤ v → 1 ≤ m → m ≤ (j : ℝ) - 1 →
        (j : ℝ) + 1 ≤ Q →
        P.real {ω | Y 0 ω > v ∧ Y j ω > v} ≤
          mesoPairEnvelopeTP (P.real {ω | Y 0 ω > v - 2}) C C' b.modC b.modc n v m Q := by
  obtain ⟨w₀, C, C', hw₀, hC, hC', hTP⟩ := b.pairTP
  refine ⟨w₀, C, C', hw₀, hC, hC', ?_⟩
  filter_upwards [b.cover] with n hn j v m Q hv hvw hm1 hmj hjQ
  set p := P.real {ω | Y 0 ω > v - 2} with hp_def
  set e := C * Real.exp (-(2 * (v - 1) * m) + C' * (v + Q ^ 2)) with he_def
  have hv1 : 0 ≤ v - 1 := by linarith
  have hterm : ∀ k ∈ Finset.range (n + 1), ∀ k' ∈ Finset.range (n + 1),
      P.real {ω | W (gridPt 0 n k) ω > v - 1 ∧ W (gridPt j n k') ω > v - 1} ≤
        p ^ 2 + e := by
    intro k hk k' hk'
    have hfrac : ∀ i ∈ Finset.range (n + 1), (i : ℝ) / n ≤ 1 := by
      intro i hi
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        simp
      · rw [div_le_one (by exact_mod_cast h)]
        exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hk1 := hfrac k hk
    have hk'1 := hfrac k' hk'
    have hk0 : 0 ≤ (k : ℝ) / n := by positivity
    have hk'0 : 0 ≤ (k' : ℝ) / n := by positivity
    have hd : (j : ℝ) - 1 ≤ gridPt j n k' - gridPt 0 n k := by
      unfold gridPt
      push_cast
      linarith
    have hd' : gridPt j n k' - gridPt 0 n k ≤ (j : ℝ) + 1 := by
      unfold gridPt
      push_cast
      linarith
    set d := gridPt j n k' - gridPt 0 n k with hd_def
    have hmd : m ≤ d := hmj.trans hd
    have hdQ : d ≤ Q := hd'.trans hjQ
    have h1 := hTP (gridPt 0 n k) (gridPt j n k') (v - 1) (by linarith) (by linarith)
    rw [← hd_def] at h1
    have h2 : P.real {ω | W 0 ω > v - 1} ≤ p := by
      refine le_trans (measureReal_mono fun ω hω => ?_) (b.one_point (v - 2))
      simp only [Set.mem_ofPred_eq] at hω ⊢
      linarith
    have h2' : P.real {ω | W 0 ω > v - 1} ^ 2 ≤ p ^ 2 :=
      pow_le_pow_left₀ (measureReal_nonneg _) h2 2
    have hI : 0 ≤ (2 / 3) * (2 * (v - 1)) ^ (3 / 2 : ℝ) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
    have hvd : (v - 1) * m ≤ (v - 1) * d := mul_le_mul_of_nonneg_left hmd hv1
    have hd2 : d ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (by linarith) hdQ 2
    have hCd : C' * d ^ 2 ≤ C' * Q ^ 2 := mul_le_mul_of_nonneg_left hd2 hC'
    have h3 : C * Real.exp (-((2 / 3) * (2 * (v - 1)) ^ (3 / 2 : ℝ)) - 2 * (v - 1) * d
        + C' * (1 + (v - 1) + d ^ 2)) ≤ e := by
      rw [he_def]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
      nlinarith
    linarith
  calc P.real {ω | Y 0 ω > v ∧ Y j ω > v}
      ≤ (∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
          P.real {ω | W (gridPt 0 n k) ω > v - 1 ∧ W (gridPt j n k') ω > v - 1}) +
        2 * ((n : ℝ) + 1) * modFail b.modC b.modc n := hn j v (by linarith)
    _ ≤ (∑ _k ∈ Finset.range (n + 1), ∑ _k' ∈ Finset.range (n + 1), (p ^ 2 + e)) +
        2 * ((n : ℝ) + 1) * modFail b.modC b.modc n := by
      gcongr with k hk k' hk'
      exact hterm k hk k' hk'
    _ = mesoPairEnvelopeTP p C C' b.modC b.modc n v m Q := by
      rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        nsmul_eq_mul]
      unfold mesoPairEnvelopeTP
      push_cast
      ring

/-! ## Step 2: the envelope sum tends to zero -/

/-- **TP envelope sum → 0** (clone of `meso_envelope_tendsto_zero`, with a new term 3):
`N q_N · mesoPairEnvelopeTP (2 e^{−H(u_N − 2)}) C C' C₀ c₀ (meshN u_N) u_N m_N (q_N + 1) → 0`
for `χ > 2/3`. Terms 1 (grid tail) and 2 (modulus) are as in `meso_envelope_tendsto_zero`;
term 3 uses `m_N ≥ χa − 1`, `q_N + 1 ≤ (D + 1)a` (`meso_qN_le_linear`) and
`meso_exponent_TP`. -/
theorem meso_envelope_tendsto_zero_TP {C₀ c₀ C C' : ℝ} (hC₀ : 0 < C₀) (hc₀ : 0 < c₀)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (z χ A : ℝ) (hχ : 2 / 3 < χ) (hA : 0 < A) :
    Tendsto (fun N : ℕ => (N : ℝ) * (qN A N : ℝ) *
      mesoPairEnvelopeTP (2 * Real.exp (-airyH (gumbelU N z - 2))) C C' C₀ c₀
        (meshN (gumbelU N z)) (gumbelU N z) (mN χ z N) ((qN A N : ℝ) + 1)) atTop (𝓝 0) := by
  -- constants
  have hχ0 : 0 < χ := by linarith
  obtain ⟨L, hL_def⟩ : ∃ L, L = Real.log airyCStar := ⟨_, rfl⟩
  obtain ⟨K, hK_def⟩ : ∃ K, K = Real.exp (-z) + 1 := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hK_def]; positivity
  obtain ⟨B, hB_def⟩ : ∃ B, B = 1 + |Real.log K| + |L| := ⟨_, rfl⟩
  have hB : 0 ≤ B := by rw [hB_def]; positivity
  obtain ⟨Cq, hCq_def⟩ : ∃ Cq, Cq = A * (B + 1) + 1 := ⟨_, rfl⟩
  have hCq : 0 < Cq := by rw [hCq_def]; positivity
  obtain ⟨D, hD_def⟩ : ∃ D, D = A * (1 + B) + 1 := ⟨_, rfl⟩
  have hD : 0 < D := by rw [hD_def]; positivity
  obtain ⟨E, hE_def⟩ : ∃ E, E = C' * (1 / 2 + (D + 1) ^ 2) := ⟨_, rfl⟩
  have hE : 0 ≤ E := by rw [hE_def]; positivity
  obtain ⟨r, hr_def⟩ : ∃ r, r = c₀ / (4 * C₀) := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hr_def]; positivity
  have hδ' : 0 < χ - 2 / 3 := by linarith
  obtain ⟨a₀, ha₀_def⟩ : ∃ a₀ : ℝ, a₀ = max 13 (max (5 / 3 / r)
      ((E + 2 * χ + 2) / (χ - 2 / 3))) := ⟨_, rfl⟩
  -- the variable `a = √(2 u_N)`
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ → ℝ, ∀ N, a N = Real.sqrt (2 * gumbelU N z) :=
    ⟨_, fun _ => rfl⟩
  have ha : Tendsto a atTop atTop := by
    rw [show a = fun N => Real.sqrt (2 * gumbelU N z) from funext ha_def]
    exact Real.tendsto_sqrt_atTop.comp ((gumbelU_tendsto_atTop z).const_mul_atTop two_pos)
  -- `N ≤ K e^{H(u_N)}` eventually
  have hNK : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≤ K * Real.exp (airyH (gumbelU N z)) := by
    have hlt : Real.exp (-z) < K := by rw [hK_def]; linarith
    filter_upwards [(gumbel_normalization z).eventually (gt_mem_nhds hlt)] with N hN
    have h := mul_le_mul_of_nonneg_right hN.le (Real.exp_pos (airyH (gumbelU N z))).le
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h
  -- split the envelope into the three contributions
  have hsplit : (fun N : ℕ => (N : ℝ) * (qN A N : ℝ) *
      mesoPairEnvelopeTP (2 * Real.exp (-airyH (gumbelU N z - 2))) C C' C₀ c₀
        (meshN (gumbelU N z)) (gumbelU N z) (mN χ z N) ((qN A N : ℝ) + 1)) =
      fun N : ℕ => ((N : ℝ) * (qN A N : ℝ) *
        (((meshN (gumbelU N z) : ℝ) + 1) ^ 2 *
          (2 * Real.exp (-airyH (gumbelU N z - 2))) ^ 2) +
        (N : ℝ) * (qN A N : ℝ) * (((meshN (gumbelU N z) : ℝ) + 1) ^ 2 *
          (C * Real.exp (-(2 * (gumbelU N z - 1) * (mN χ z N : ℝ)) +
            C' * (gumbelU N z + ((qN A N : ℝ) + 1) ^ 2))))) +
        (N : ℝ) * (qN A N : ℝ) *
          (2 * ((meshN (gumbelU N z) : ℝ) + 1) * modFail C₀ c₀ (meshN (gumbelU N z))) := by
    funext N
    simp only [mesoPairEnvelopeTP]
    ring
  -- the per-`N` bounds
  have key : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * (qN A N : ℝ) * (((meshN (gumbelU N z) : ℝ) + 1) ^ 2 *
          (2 * Real.exp (-airyH (gumbelU N z - 2))) ^ 2) ≤
        (36 * K * Cq * Real.exp (11 + L)) * (a N ^ 19 * Real.exp (-a N)) ∧
      (N : ℝ) * (qN A N : ℝ) * (((meshN (gumbelU N z) : ℝ) + 1) ^ 2 *
          (C * Real.exp (-(2 * (gumbelU N z - 1) * (mN χ z N : ℝ)) +
            C' * (gumbelU N z + ((qN A N : ℝ) + 1) ^ 2)))) ≤
        (9 * K * Cq * C * Real.exp (-L)) * (a N ^ 19 * Real.exp (-a N)) ∧
      (N : ℝ) * (qN A N : ℝ) *
          (2 * ((meshN (gumbelU N z) : ℝ) + 1) * modFail C₀ c₀ (meshN (gumbelU N z))) ≤
        (6 * K * Cq * C₀ * Real.exp (-L)) * (a N ^ 11 * Real.exp (-a N)) := by
    filter_upwards [eventually_ge_atTop 1, ha.eventually_ge_atTop a₀, hNK]
      with N hN1 haN hNK
    -- `m_N ≥ χ a - 1` (before generalizing `u_N`, which `mN` hides)
    have hm : χ * a N - 1 ≤ (mN χ z N : ℝ) := by
      have h := Nat.lt_floor_add_one (χ * Real.sqrt (2 * gumbelU N z))
      have hmN : mN χ z N = ⌊χ * Real.sqrt (2 * gumbelU N z)⌋₊ := rfl
      rw [hmN, ha_def N]
      linarith
    have hxa := ha_def N
    generalize gumbelU N z = u at *
    generalize a N = x at *
    rw [ha₀_def] at haN
    have hx13 : 13 ≤ x := (le_max_left _ _).trans haN
    have hxr : 5 / 3 / r ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans haN
    have hxc : (E + 2 * χ + 2) / (χ - 2 / 3) ≤ x :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans haN
    have hupos : 0 < 2 * u := Real.sqrt_pos.mp (by rw [← hxa]; linarith)
    have hx2 : x ^ 2 = 2 * u := by rw [hxa]; exact Real.sq_sqrt hupos.le
    have hx169 : (169 : ℝ) ≤ x ^ 2 := by
      have h := mul_le_mul hx13 hx13 (by norm_num) (by linarith)
      rw [sq]
      linarith
    have hu1 : 1 ≤ u := by linarith
    -- exponent bounds on `H`
    have hH : airyH u ≤ 2 / 3 * x ^ 3 - L := by
      rw [hxa, hL_def]
      exact meso_airyH_le hu1
    have hw : 0 < u - 2 := by linarith
    have hHw := meso_airyH_ge hw
    rw [← hL_def] at hHw
    have hsq : x - 2 ≤ Real.sqrt (2 * (u - 2)) := by
      rw [show 2 * (u - 2) = x ^ 2 - 4 by linarith]
      exact meso_sub_two_le_sqrt (by linarith)
    have hcube : (x - 2) ^ 3 ≤ Real.sqrt (2 * (u - 2)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hsq 3
    -- `log N ≤ B x³`, the crude `q_N ≤ C_q x³` and the linear `q_N ≤ D x`
    have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ (by linarith)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
    have hlogN : Real.log N ≤ Real.log K + airyH u := by
      have := Real.log_le_log hN0 hNK
      rwa [Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    have hlogB : Real.log N ≤ B * x ^ 3 := by
      have habs1 := le_abs_self (Real.log K)
      have habs2 := neg_abs_le L
      have h1 : |Real.log K| ≤ |Real.log K| * x ^ 3 :=
        le_mul_of_one_le_right (abs_nonneg _) hx3
      have h2 : |L| ≤ |L| * x ^ 3 := le_mul_of_one_le_right (abs_nonneg _) hx3
      rw [hB_def]
      linarith
    have hq : (qN A N : ℝ) ≤ Cq * x ^ 3 := by
      have hq0 : (qN A N : ℝ) < A * Real.log N ^ ((1 : ℝ) / 3) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have h13 := mul_le_mul_of_nonneg_left (meso_rpow_third_le hlogN0) hA.le
      have hBx : B ≤ B * x ^ 3 := le_mul_of_one_le_right hB hx3
      have e2 : 1 + Real.log N ≤ (B + 1) * x ^ 3 := by linarith
      have e3 := mul_le_mul_of_nonneg_left e2 hA.le
      rw [hCq_def]
      linarith
    have hqlin : (qN A N : ℝ) ≤ D * x := by
      rw [hD_def]
      exact meso_qN_le_linear hA.le hB (by linarith) hlogB
    -- the mesh `n = ⌈u⁴⌉₊`
    have hu4 : u ^ 4 = x ^ 8 / 16 := by
      have h8 : x ^ 8 = (x ^ 2) ^ 4 := by ring
      rw [h8, hx2]
      ring
    have hn_lt : (meshN u : ℝ) < u ^ 4 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hn_ge : u ^ 4 ≤ (meshN u : ℝ) := Nat.le_ceil _
    have hx8 : 1 ≤ x ^ 8 := one_le_pow₀ (by linarith)
    have hn1 : (meshN u : ℝ) + 1 ≤ 3 * x ^ 8 := by linarith
    have hsqrtn : u ^ 2 ≤ Real.sqrt (meshN u) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      calc (u ^ 2) ^ 2 = u ^ 4 := by ring
        _ ≤ _ := hn_ge
    have hmod : modFail C₀ c₀ (meshN u) ≤ C₀ * Real.exp (-(r * x ^ 4)) := by
      unfold modFail
      have h1 : r * x ^ 4 ≤ c₀ * (Real.sqrt (meshN u) / C₀) := by
        have : r * x ^ 4 = c₀ * (u ^ 2 / C₀) := by
          rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx2, hr_def]
          field_simp
          ring
        rw [this]
        gcongr
      gcongr
      linarith
    -- the one-point tail factor `p² = 4 e^{-2 H(u - 2)}`
    have hp : (2 * Real.exp (-airyH (u - 2))) ^ 2 =
        4 * Real.exp (-(2 * airyH (u - 2))) := by
      rw [show -(2 * airyH (u - 2)) = -airyH (u - 2) + -airyH (u - 2) by ring,
        Real.exp_add]
      ring
    -- the TP exponent: `−2(u−1) m_N + C'(u + (q_N+1)²) ≤ −(x²−2)(χx−1) + E x²`
    have hTPexp : -(2 * (u - 1) * (mN χ z N : ℝ)) + C' * (u + ((qN A N : ℝ) + 1) ^ 2) ≤
        -((x ^ 2 - 2) * (χ * x - 1)) + E * x ^ 2 := by
      have hx22 : 0 ≤ x ^ 2 - 2 := by linarith
      have h1 : (x ^ 2 - 2) * (χ * x - 1) ≤ (x ^ 2 - 2) * (mN χ z N : ℝ) :=
        mul_le_mul_of_nonneg_left hm hx22
      have hq1 : (qN A N : ℝ) + 1 ≤ (D + 1) * x := by linarith
      have h2 : ((qN A N : ℝ) + 1) ^ 2 ≤ ((D + 1) * x) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hq1 2
      have h3 : C' * ((qN A N : ℝ) + 1) ^ 2 ≤ C' * ((D + 1) * x) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 hC'
      have h4 : C' * u = C' * (1 / 2) * x ^ 2 := by rw [hx2]; ring
      have e1 : 2 * (u - 1) * (mN χ z N : ℝ) = (x ^ 2 - 2) * (mN χ z N : ℝ) := by
        rw [hx2]; ring
      have e2 : C' * (u + ((qN A N : ℝ) + 1) ^ 2) ≤ E * x ^ 2 := by
        calc C' * (u + ((qN A N : ℝ) + 1) ^ 2) = C' * u + C' * ((qN A N : ℝ) + 1) ^ 2 := by
              ring
          _ ≤ C' * (1 / 2) * x ^ 2 + C' * ((D + 1) * x) ^ 2 := by rw [h4]; linarith
          _ = E * x ^ 2 := by rw [hE_def]; ring
      rw [e1]
      linarith
    have E1 := meso_exponent_grid hx13
    have E2 := meso_exponent_modulus (a := x) (r := r) (by linarith)
      (by rw [div_le_iff₀ hr] at hxr; linarith)
    have E3 := meso_exponent_TP (a := x) (χ := χ) (E := E) hχ0 (by linarith)
      (by rw [div_le_iff₀ hδ'] at hxc; linarith)
    have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hqn : (0 : ℝ) ≤ (qN A N : ℝ) := Nat.cast_nonneg _
    have hmn : (0 : ℝ) ≤ (meshN u : ℝ) + 1 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · rw [hp]
      calc (N : ℝ) * (qN A N : ℝ) *
            (((meshN u : ℝ) + 1) ^ 2 * (4 * Real.exp (-(2 * airyH (u - 2)))))
          ≤ (K * Real.exp (airyH u)) * (Cq * x ^ 3) *
            ((3 * x ^ 8) ^ 2 * (4 * Real.exp (-(2 * airyH (u - 2))))) := by
            gcongr
        _ = 36 * K * Cq * x ^ 19 * Real.exp (airyH u + -(2 * airyH (u - 2))) := by
            rw [Real.exp_add]
            ring
        _ ≤ 36 * K * Cq * x ^ 19 * Real.exp (-x + (11 + L)) := by
            gcongr 36 * K * Cq * x ^ 19 * Real.exp ?_
            linarith
        _ = (36 * K * Cq * Real.exp (11 + L)) * (x ^ 19 * Real.exp (-x)) := by
            rw [Real.exp_add]
            ring
    · calc (N : ℝ) * (qN A N : ℝ) * (((meshN u : ℝ) + 1) ^ 2 *
            (C * Real.exp (-(2 * (u - 1) * (mN χ z N : ℝ)) +
              C' * (u + ((qN A N : ℝ) + 1) ^ 2))))
          ≤ (K * Real.exp (airyH u)) * (Cq * x ^ 3) *
            ((3 * x ^ 8) ^ 2 * (C * Real.exp (-((x ^ 2 - 2) * (χ * x - 1)) + E * x ^ 2))) := by
            gcongr
        _ = 9 * K * Cq * C * x ^ 19 *
            Real.exp (airyH u + (-((x ^ 2 - 2) * (χ * x - 1)) + E * x ^ 2)) := by
            rw [Real.exp_add (airyH u)]
            ring
        _ ≤ 9 * K * Cq * C * x ^ 19 * Real.exp (-x + -L) := by
            gcongr 9 * K * Cq * C * x ^ 19 * Real.exp ?_
            linarith
        _ = (9 * K * Cq * C * Real.exp (-L)) * (x ^ 19 * Real.exp (-x)) := by
            rw [Real.exp_add]
            ring
    · calc (N : ℝ) * (qN A N : ℝ) *
            (2 * ((meshN u : ℝ) + 1) * modFail C₀ c₀ (meshN u))
          ≤ (K * Real.exp (airyH u)) * (Cq * x ^ 3) *
            (2 * (3 * x ^ 8) * (C₀ * Real.exp (-(r * x ^ 4)))) := by
            have hmf : 0 ≤ modFail C₀ c₀ (meshN u) := by
              unfold modFail
              positivity
            gcongr
        _ = 6 * K * Cq * C₀ * x ^ 11 * Real.exp (airyH u + -(r * x ^ 4)) := by
            rw [Real.exp_add]
            ring
        _ ≤ 6 * K * Cq * C₀ * x ^ 11 * Real.exp (-x + -L) := by
            gcongr 6 * K * Cq * C₀ * x ^ 11 * Real.exp ?_
            linarith
        _ = (6 * K * Cq * C₀ * Real.exp (-L)) * (x ^ 11 * Real.exp (-x)) := by
            rw [Real.exp_add]
            ring
  rw [hsplit]
  have l1 := meso_tendsto_zero_of_le_pow_exp ha _ 19
    (Eventually.of_forall fun N => by positivity) (key.mono fun N h => h.1)
  have l2 := meso_tendsto_zero_of_le_pow_exp ha _ 19
    (Eventually.of_forall fun N => by positivity) (key.mono fun N h => h.2.1)
  have l3 := meso_tendsto_zero_of_le_pow_exp ha _ 11
    (Eventually.of_forall fun N => by unfold modFail; positivity) (key.mono fun N h => h.2.2)
  simpa using (l1.add l2).add l3

/-! ## Step 3: the `mesoscopic` field from the TP bundle -/

/-- **The `mesoscopic` field from `MesoscopicBoundsTP`** — EXACTLY the
field `Airy1BlockExtremes.mesoscopic`. Squeeze `0 ≤ N Σ ≤ N q_N · envelope` with the envelope
`mesoPairEnvelopeTP` at `v = u_N`, `m = m_N`, `Q = q_N + 1`, valid for every
`j ∈ [m_N + 1, q_N]` (`block_pair_le_TP`; eventually `m_N ≥ 1`, `u_N ≥ w₀ + 1`,
`u_N ≥ coverLevel`), then `meso_envelope_tendsto_zero_TP` (`χ > (1/2)^{1/3} > 2/3`). -/
theorem mesoscopic_of_boundsTP {Y : ℕ → Ω → ℝ} {W : ℝ → Ω → ℝ}
    (b : MesoscopicBoundsTP P Y W) :
    ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
      Tendsto (fun N : ℕ =>
        (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0) := by
  intro z χ A hχ _hχ1 hA
  have hχ23 := two_thirds_lt_of_rpow_lt hχ
  have hχ0 : 0 < χ := by linarith
  obtain ⟨w₀, C, C', -, hC, hC', hev⟩ := b.block_pair_le_TP
  have hu := gumbelU_tendsto_atTop z
  have hmesh : Tendsto (fun N : ℕ => meshN (gumbelU N z)) atTop atTop :=
    tendsto_nat_ceil_atTop.comp ((tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp hu)
  have hm : Tendsto (fun N : ℕ => mN χ z N) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      ((Real.tendsto_sqrt_atTop.comp (hu.const_mul_atTop two_pos)).const_mul_atTop hχ0)
  have htail : ∀ᶠ N : ℕ in atTop,
      P.real {ω | Y 0 ω > gumbelU N z - 2} ≤ 2 * Real.exp (-airyH (gumbelU N z - 2)) := by
    have h2 : Tendsto (fun N : ℕ => gumbelU N z - 2) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-2) hu
    filter_upwards [h2.eventually (b.sharp_tail.eventually
      (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)))] with N hN
    rw [div_lt_iff₀ (Real.exp_pos _)] at hN
    exact hN.le
  have hlim := meso_envelope_tendsto_zero_TP b.modC_pos b.modc_pos hC.le hC' z χ A hχ23 hA
  refine squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall fun N =>
      mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => measureReal_nonneg _)
  · filter_upwards [hmesh.eventually hev, hm.eventually (eventually_ge_atTop 1), htail,
      hu.eventually_ge_atTop b.coverLevel, hu.eventually_ge_atTop (w₀ + 1)]
      with N hn hmN hp hlev hlev2
    set env := mesoPairEnvelopeTP (2 * Real.exp (-airyH (gumbelU N z - 2))) C C' b.modC
      b.modc (meshN (gumbelU N z)) (gumbelU N z) (mN χ z N) ((qN A N : ℝ) + 1) with henv
    have henv0 : 0 ≤ env := by
      have := b.modC_pos
      rw [henv]
      unfold mesoPairEnvelopeTP modFail
      positivity
    have hbound : ∀ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
        P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z} ≤ env := by
      intro j hj
      have hj1 : mN χ z N + 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjq : j ≤ qN A N := (Finset.mem_Icc.mp hj).2
      have hjr : (mN χ z N : ℝ) ≤ (j : ℝ) - 1 := by
        have : ((mN χ z N + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj1
        push_cast at this
        linarith
      have hjQ : (j : ℝ) + 1 ≤ (qN A N : ℝ) + 1 := by
        have : (j : ℝ) ≤ (qN A N : ℝ) := by exact_mod_cast hjq
        linarith
      have hm1 : (1 : ℝ) ≤ (mN χ z N : ℝ) := by exact_mod_cast hmN
      refine (hn j (gumbelU N z) (mN χ z N) ((qN A N : ℝ) + 1) hlev hlev2 hm1 hjr hjQ).trans ?_
      rw [henv]
      unfold mesoPairEnvelopeTP
      have hp0 : 0 ≤ P.real {ω | Y 0 ω > gumbelU N z - 2} := measureReal_nonneg _
      have hsq := pow_le_pow_left₀ hp0 hp 2
      have := mul_le_mul_of_nonneg_left hsq (sq_nonneg ((meshN (gumbelU N z) : ℝ) + 1))
      nlinarith
    have hcard : ((Finset.Icc (mN χ z N + 1) (qN A N)).card : ℝ) ≤ (qN A N : ℝ) := by
      rw [Nat.card_Icc]
      exact_mod_cast (by omega : qN A N + 1 - (mN χ z N + 1) ≤ qN A N)
    calc (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}
        ≤ (N : ℝ) * ∑ _j ∈ Finset.Icc (mN χ z N + 1) (qN A N), env := by
          gcongr with j hj
          exact hbound j hj
      _ = (N : ℝ) * ((Finset.Icc (mN χ z N + 1) (qN A N)).card * env) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * ((qN A N : ℝ) * env) := by
          gcongr
      _ = (N : ℝ) * (qN A N : ℝ) * env := by
          ring

end MesoSumTP

end Airy1Gumbel
