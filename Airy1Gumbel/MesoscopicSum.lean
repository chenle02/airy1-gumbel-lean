/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.MesoscopicSpec

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators NNReal

namespace Airy1Gumbel

/-!
# The mesoscopic sum from the `MesoscopicBounds` bundle

This file proves the three statements announced in `Airy1Gumbel/MesoscopicSpec.lean`,
from the bundle `MesoscopicBounds` only:

* `MesoscopicBounds.block_pair_le` — the per-pair envelope
  (the point bound in the proof of the paper's mesoscopic estimate);
* `meso_envelope_tendsto_zero` — the real-analysis core: the three exponents of the
  spec docstring (grid tail, modulus, covariance) all tend to `-∞`;
* `mesoscopic_of_bounds` — the `Airy1BlockExtremes.mesoscopic` field from the bundle
  (the squeeze `0 ≤ N Σ ≤ N q_N · envelope(m_N + 1)`).

All asymptotics are carried out in the variable `a = √(2 u_N)`, where
`κ u^{3/2} = (2/3) a³` (`airyKappa_mul_rpow_three_halves`). Each of the three
contributions is bounded by `C · a^k · e^{-a}` for large `a`, and
`a^k e^{-a} → 0` (`Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`).
-/

/-! ## Elementary bounds on `H` and polynomial exponent inequalities -/

section MesoArith

/-- Upper bound on the exponent function for `u ≥ 1` in the variable `a = √(2u)`:
`H(u) ≤ (2/3) a³ - log c_*` (the `-(1/4) log u` term is dropped). Used for
`N ≤ K e^{H(u_N)}` in the paper's mesoscopic estimate. -/
theorem meso_airyH_le {u : ℝ} (hu : 1 ≤ u) :
    airyH u ≤ 2 / 3 * Real.sqrt (2 * u) ^ 3 - Real.log airyCStar := by
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu
  have hk := airyKappa_mul_rpow_three_halves (by linarith : (0 : ℝ) ≤ u)
  unfold airyH
  linarith

/-- Lower bound on the exponent function for `w > 0`:
`(2/3) (√(2w))³ - w/4 - log c_* ≤ H(w)` (from `log w ≤ w`). Used for the
one-point tail `p(u_N - 2) ≤ 2 e^{-H(u_N - 2)}` in the paper's mesoscopic estimate. -/
theorem meso_airyH_ge {w : ℝ} (hw : 0 < w) :
    2 / 3 * Real.sqrt (2 * w) ^ 3 - w / 4 - Real.log airyCStar ≤ airyH w := by
  have hlog : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hw
  have hk := airyKappa_mul_rpow_three_halves hw.le
  unfold airyH
  linarith

/-- `a - 2 ≤ √(a² - 4)` for `a ≥ 2`: the level shift `u ↦ u - 2` costs at most `2`
in the variable `a = √(2u)`. -/
theorem meso_sub_two_le_sqrt {a : ℝ} (ha : 2 ≤ a) : a - 2 ≤ Real.sqrt (a ^ 2 - 4) := by
  rw [Real.le_sqrt (by linarith) (by nlinarith)]
  nlinarith

/-- `x^{1/3} ≤ 1 + x` for `x ≥ 0` (crude bound for `q_N = ⌈A (log N)^{1/3}⌉`). -/
theorem meso_rpow_third_le {x : ℝ} (hx : 0 ≤ x) : x ^ ((1 : ℝ) / 3) ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_one hx h (by norm_num : (0 : ℝ) ≤ 1 / 3)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h (by norm_num : (1 : ℝ) / 3 ≤ 1)
    rw [Real.rpow_one] at this
    linarith

/-- Exponent of term 1 (grid tail, spec docstring): for `a ≥ 13`,
`(2/3) a³ - (4/3) (a - 2)³ + a²/4 ≤ -a + 11`. -/
theorem meso_exponent_grid {a : ℝ} (ha : 13 ≤ a) :
    2 / 3 * a ^ 3 - 4 / 3 * (a - 2) ^ 3 + a ^ 2 / 4 ≤ -a + 11 := by
  have h1 : a ^ 2 * 13 ≤ a ^ 2 * a := mul_le_mul_of_nonneg_left ha (sq_nonneg a)
  nlinarith

/-- Exponent of term 2 (modulus, spec docstring): for `r > 0`, `a ≥ 1`, `r a ≥ 5/3`,
`(2/3) a³ - r a⁴ ≤ -a`. -/
theorem meso_exponent_modulus {a r : ℝ} (ha1 : 1 ≤ a) (ha : 5 / 3 ≤ r * a) :
    2 / 3 * a ^ 3 - r * a ^ 4 ≤ -a := by
  have ha3 : 0 ≤ a ^ 3 := by positivity
  have h1 : 5 / 3 * a ^ 3 ≤ r * a * a ^ 3 := mul_le_mul_of_nonneg_right ha ha3
  have h2 : a ≤ a ^ 3 := by
    have : 1 ≤ a ^ 2 := by nlinarith
    nlinarith
  nlinarith

/-- Exponent of term 3 (covariance, spec docstring): with margin
`δ = θ χ³ - 2/3 > 0`, for `a ≥ 1` and `δ a ≥ 3 θ χ² + 1`,
`(2/3) a³ - θ (χ a - 1)³ ≤ -a + θ`. -/
theorem meso_exponent_cov {a θ χ : ℝ} (hθ : 0 < θ) (hχ : 0 < χ) (ha1 : 1 ≤ a)
    (ha : 3 * θ * χ ^ 2 + 1 ≤ (θ * χ ^ 3 - 2 / 3) * a) :
    2 / 3 * a ^ 3 - θ * (χ * a - 1) ^ 3 ≤ -a + θ := by
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have h1 : (3 * θ * χ ^ 2 + 1) * a ^ 2 ≤ (θ * χ ^ 3 - 2 / 3) * a * a ^ 2 :=
    mul_le_mul_of_nonneg_right ha ha2
  have h2 : a ≤ a ^ 2 := by nlinarith
  have h3 : 0 ≤ θ * χ * a := by positivity
  nlinarith

/-- Squeeze helper: if eventually `0 ≤ f N ≤ C a_N^k e^{-a_N}` with `a_N → ∞`,
then `f N → 0`. -/
theorem meso_tendsto_zero_of_le_pow_exp {f a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    (C : ℝ) (k : ℕ) (h0 : ∀ᶠ N in atTop, 0 ≤ f N)
    (h : ∀ᶠ N in atTop, f N ≤ C * (a N ^ k * Real.exp (-a N))) :
    Tendsto f atTop (𝓝 0) := by
  have hlim : Tendsto (fun N => C * (a N ^ k * Real.exp (-a N))) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp ha).const_mul C
  exact squeeze_zero' h0 h hlim

end MesoArith

/-! ## Step 1: the per-pair envelope -/

section MesoSum

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Step 1**: the per-pair envelope. Combines
`cover`, `pair` at level `v - 1`, `one_point`, `cov_decay` (for
`gridPt j n k' - gridPt 0 n k ≥ j - 1 ≥ d₀ ≥ 0`, `k, k' ≤ n`) and
`e^{-θ d³} ≤ e^{-θ (j-1)³}`. Asserted at levels `v ≥ b.coverLevel` only (the level
threshold of `cover`).

This is the point bound in the proof of the paper's mesoscopic estimate,
in the Lean form (i)–(iii′) of the `MesoscopicSpec.lean` docstring. -/
theorem MesoscopicBounds.block_pair_le {Y : ℕ → Ω → ℝ} {W : ℝ → Ω → ℝ}
    (b : MesoscopicBounds P Y W) {θ : ℝ} (hθ : θ < 4 / 3) (hθ0 : 0 < θ) :
    ∃ d₀ : ℝ, 0 ≤ d₀ ∧ ∀ᶠ n : ℕ in atTop, ∀ (j : ℕ) (v : ℝ), b.coverLevel ≤ v →
      d₀ ≤ (j : ℝ) - 1 →
      P.real {ω | Y 0 ω > v ∧ Y j ω > v} ≤
        mesoPairEnvelope (P.real {ω | Y 0 ω > v - 2}) θ b.modC b.modc n j := by
  obtain ⟨d₁, hd₁⟩ := b.cov_decay θ hθ
  refine ⟨max d₁ 0, le_max_right _ _, ?_⟩
  filter_upwards [b.cover] with n hn j v hv hj
  have hj0 : 0 ≤ (j : ℝ) - 1 := (le_max_right _ _).trans hj
  set p := P.real {ω | Y 0 ω > v - 2} with hp_def
  set e := Real.exp (-θ * ((j : ℝ) - 1) ^ 3) with he_def
  have hterm : ∀ k ∈ Finset.range (n + 1), ∀ k' ∈ Finset.range (n + 1),
      P.real {ω | W (gridPt 0 n k) ω > v - 1 ∧ W (gridPt j n k') ω > v - 1} ≤
        p ^ 2 + e := by
    intro k hk k' _
    have hk1 : (k : ℝ) / n ≤ 1 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        simp
      · rw [div_le_one (by exact_mod_cast h)]
        exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk'0 : 0 ≤ (k' : ℝ) / n := by positivity
    have hd : (j : ℝ) - 1 ≤ gridPt j n k' - gridPt 0 n k := by
      unfold gridPt
      push_cast
      linarith
    have h1 := b.pair (gridPt 0 n k) (gridPt j n k') (v - 1)
    rw [show v - 1 - 1 = v - 2 by ring] at h1
    have h2 : P.real {ω | W 0 ω > v - 2} ^ 2 ≤ p ^ 2 :=
      pow_le_pow_left₀ (measureReal_nonneg _) (b.one_point (v - 2)) 2
    have h3 := hd₁ _ ((le_max_left _ _).trans (hj.trans hd))
    have h4 : Real.exp (-θ * (gridPt j n k' - gridPt 0 n k) ^ 3) ≤ e := by
      apply Real.exp_le_exp.mpr
      have := pow_le_pow_left₀ hj0 hd 3
      nlinarith
    linarith
  calc P.real {ω | Y 0 ω > v ∧ Y j ω > v}
      ≤ (∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
          P.real {ω | W (gridPt 0 n k) ω > v - 1 ∧ W (gridPt j n k') ω > v - 1}) +
        2 * ((n : ℝ) + 1) * modFail b.modC b.modc n := hn j v hv
    _ ≤ (∑ _k ∈ Finset.range (n + 1), ∑ _k' ∈ Finset.range (n + 1), (p ^ 2 + e)) +
        2 * ((n : ℝ) + 1) * modFail b.modC b.modc n := by
      gcongr with k hk k' hk'
      exact hterm k hk k' hk'
    _ = mesoPairEnvelope p θ b.modC b.modc n j := by
      rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        nsmul_eq_mul]
      unfold mesoPairEnvelope
      push_cast
      ring

/-! ## Step 2: the envelope sum tends to zero (pure real analysis) -/

/-- **Step 2**: pure real analysis — the envelope at
`j = m_N + 1`, `n = meshN u_N`, `p = 2 e^{-H(u_N - 2)}`, times `N q_N`, tends to `0`.
This is the arithmetic of the module docstring (terms 1-3).

This is the summation step of the paper's mesoscopic estimate.
Proof: with `a = √(2 u_N)`, eventually `N ≤ K e^{H(u_N)}` (`gumbel_normalization`),
`H(u_N) ≤ (2/3) a³ - log c_*` (`meso_airyH_le`), `q_N ≤ C_q a³`, `n + 1 ≤ 3 a⁸`,
`√n ≥ u_N² = a⁴/4`, `m_N ≥ χ a - 1`; the three contributions are then each
`≤ C a^k e^{-a}` by `meso_exponent_grid`, `meso_exponent_modulus` and
`meso_exponent_cov` (the last uses the margin `θ χ³ > 2/3`, `mesoTheta_margin_pos`). -/
theorem meso_envelope_tendsto_zero {C₀ c₀ : ℝ} (hC₀ : 0 < C₀) (hc₀ : 0 < c₀)
    (z χ A : ℝ) (hχ : (1 / 2 : ℝ) ^ ((1 : ℝ) / 3) < χ) (hχ1 : χ < 1) (hA : 0 < A) :
    Tendsto (fun N : ℕ => (N : ℝ) * (qN A N : ℝ) *
      mesoPairEnvelope (2 * Real.exp (-airyH (gumbelU N z - 2))) (mesoTheta χ) C₀ c₀
        (meshN (gumbelU N z)) (mN χ z N + 1)) atTop (𝓝 0) := by
  -- constants
  have hχ0 : 0 < χ := lt_trans (Real.rpow_pos_of_pos (by norm_num) _) hχ
  have hθ0 : 0 < mesoTheta χ := mesoTheta_pos (by positivity)
  have hδ : 2 / 3 < mesoTheta χ * χ ^ 3 := mesoTheta_margin_pos hχ
  obtain ⟨θ, hθ_def⟩ : ∃ θ, θ = mesoTheta χ := ⟨_, rfl⟩
  rw [← hθ_def] at hθ0 hδ ⊢
  obtain ⟨L, hL_def⟩ : ∃ L, L = Real.log airyCStar := ⟨_, rfl⟩
  obtain ⟨K, hK_def⟩ : ∃ K, K = Real.exp (-z) + 1 := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hK_def]; positivity
  obtain ⟨B, hB_def⟩ : ∃ B, B = 1 + |Real.log K| + |L| := ⟨_, rfl⟩
  have hB : 0 ≤ B := by rw [hB_def]; positivity
  obtain ⟨Cq, hCq_def⟩ : ∃ Cq, Cq = A * (B + 1) + 1 := ⟨_, rfl⟩
  have hCq : 0 < Cq := by rw [hCq_def]; positivity
  obtain ⟨r, hr_def⟩ : ∃ r, r = c₀ / (4 * C₀) := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hr_def]; positivity
  have hδ' : 0 < θ * χ ^ 3 - 2 / 3 := by linarith
  obtain ⟨a₀, ha₀_def⟩ : ∃ a₀ : ℝ, a₀ = max 13 (max (5 / 3 / r)
      (max ((3 * θ * χ ^ 2 + 1) / (θ * χ ^ 3 - 2 / 3)) (1 / χ))) := ⟨_, rfl⟩
  -- the variable `a = √(2 u_N)`
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ → ℝ, ∀ N, a N = Real.sqrt (2 * gumbelU N z) :=
    ⟨_, fun _ => rfl⟩
  have ha : Tendsto a atTop atTop := by
    rw [show a = fun N => Real.sqrt (2 * gumbelU N z) from funext ha_def]
    exact Real.tendsto_sqrt_atTop.comp ((gumbelU_tendsto_atTop z).const_mul_atTop two_pos)
  -- `N ≤ K e^{H(u_N)}` eventually (from `gumbel_normalization`)
  have hNK : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≤ K * Real.exp (airyH (gumbelU N z)) := by
    have hlt : Real.exp (-z) < K := by rw [hK_def]; linarith
    filter_upwards [(gumbel_normalization z).eventually (gt_mem_nhds hlt)] with N hN
    have h := mul_le_mul_of_nonneg_right hN.le (Real.exp_pos (airyH (gumbelU N z))).le
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h
  -- split the envelope into the three contributions
  have hsplit : (fun N : ℕ => (N : ℝ) * (qN A N : ℝ) *
      mesoPairEnvelope (2 * Real.exp (-airyH (gumbelU N z - 2))) θ C₀ c₀
        (meshN (gumbelU N z)) (mN χ z N + 1)) =
      fun N : ℕ => ((N : ℝ) * (qN A N : ℝ) *
        (((meshN (gumbelU N z) : ℝ) + 1) ^ 2 *
          (2 * Real.exp (-airyH (gumbelU N z - 2))) ^ 2) +
        (N : ℝ) * (qN A N : ℝ) * (((meshN (gumbelU N z) : ℝ) + 1) ^ 2 *
          Real.exp (-θ * (((mN χ z N + 1 : ℕ) : ℝ) - 1) ^ 3))) +
        (N : ℝ) * (qN A N : ℝ) *
          (2 * ((meshN (gumbelU N z) : ℝ) + 1) * modFail C₀ c₀ (meshN (gumbelU N z))) := by
    funext N
    simp only [mesoPairEnvelope]
    ring
  -- the per-`N` bounds
  have key : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * (qN A N : ℝ) * (((meshN (gumbelU N z) : ℝ) + 1) ^ 2 *
          (2 * Real.exp (-airyH (gumbelU N z - 2))) ^ 2) ≤
        (36 * K * Cq * Real.exp (11 + L)) * (a N ^ 19 * Real.exp (-a N)) ∧
      (N : ℝ) * (qN A N : ℝ) * (((meshN (gumbelU N z) : ℝ) + 1) ^ 2 *
          Real.exp (-θ * (((mN χ z N + 1 : ℕ) : ℝ) - 1) ^ 3)) ≤
        (9 * K * Cq * Real.exp (θ - L)) * (a N ^ 19 * Real.exp (-a N)) ∧
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
    have hq0 : (qN A N : ℝ) < A * Real.log N ^ ((1 : ℝ) / 3) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    generalize gumbelU N z = u at *
    generalize a N = x at *
    rw [ha₀_def] at haN
    have hx13 : 13 ≤ x := (le_max_left _ _).trans haN
    have hxr : 5 / 3 / r ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans haN
    have hxc : (3 * θ * χ ^ 2 + 1) / (θ * χ ^ 3 - 2 / 3) ≤ x :=
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans haN
    have hxχ : 1 / χ ≤ x :=
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans haN
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
    -- `q_N ≤ C_q a³`
    have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ (by linarith)
    have hq : (qN A N : ℝ) ≤ Cq * x ^ 3 := by
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
      have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
      have hlogN : Real.log N ≤ Real.log K + airyH u := by
        have := Real.log_le_log hN0 hNK
        rwa [Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp] at this
      have h13 := mul_le_mul_of_nonneg_left (meso_rpow_third_le hlogN0) hA.le
      have habs1 := le_abs_self (Real.log K)
      have habs2 := neg_abs_le L
      have hBx : B ≤ B * x ^ 3 := le_mul_of_one_le_right hB hx3
      have e2 : 1 + Real.log N ≤ (B + 1) * x ^ 3 := by
        rw [hB_def] at hBx ⊢
        linarith
      have e3 := mul_le_mul_of_nonneg_left e2 hA.le
      rw [hCq_def]
      linarith
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
    -- the block-distance factor `e^{-θ m³} ≤ e^{-θ (χ a - 1)³}`
    have hχx : 0 ≤ χ * x - 1 := by
      have := mul_le_mul_of_nonneg_left hxχ hχ0.le
      rw [mul_one_div_cancel hχ0.ne'] at this
      linarith
    have hexpm : Real.exp (-θ * (((mN χ z N + 1 : ℕ) : ℝ) - 1) ^ 3) ≤
        Real.exp (-(θ * (χ * x - 1) ^ 3)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      rw [add_sub_cancel_right]
      have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hχx hm 3) hθ0.le
      linarith
    -- the three exponent inequalities
    have E1 := meso_exponent_grid hx13
    have E2 := meso_exponent_modulus (a := x) (r := r) (by linarith)
      (by rw [div_le_iff₀ hr] at hxr; linarith)
    have E3 := meso_exponent_cov (a := x) (χ := χ) hθ0 hχ0 (by linarith)
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
            Real.exp (-θ * (((mN χ z N + 1 : ℕ) : ℝ) - 1) ^ 3))
          ≤ (K * Real.exp (airyH u)) * (Cq * x ^ 3) *
            ((3 * x ^ 8) ^ 2 * Real.exp (-(θ * (χ * x - 1) ^ 3))) := by
            gcongr
        _ = 9 * K * Cq * x ^ 19 * Real.exp (airyH u + -(θ * (χ * x - 1) ^ 3)) := by
            rw [Real.exp_add]
            ring
        _ ≤ 9 * K * Cq * x ^ 19 * Real.exp (-x + (θ - L)) := by
            gcongr 9 * K * Cq * x ^ 19 * Real.exp ?_
            linarith
        _ = (9 * K * Cq * Real.exp (θ - L)) * (x ^ 19 * Real.exp (-x)) := by
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

/-! ## Step 3: the `mesoscopic` field from the bundle -/

/-- **Step 3**: the field from the bundle. Squeeze:
`0 ≤ N Σ ≤ N q_N · mesoPairEnvelope(…, m_N + 1)` eventually (card of the `Icc` is
`≤ q_N`; envelope nonincreasing in `j ≥ 1` and nondecreasing in `p ≥ 0`;
`ℙ(Y₀ > u - 2) ≤ 2 e^{-H(u-2)}` eventually from `sharp_tail`; `m_N → ∞` clears `d₀`;
`meshN u_N → ∞` enters the `cover` eventuality; `u_N → ∞` clears `coverLevel`), then
`meso_envelope_tendsto_zero`.

This is the paper's mesoscopic estimate, in the Lean form (i)–(iii′) described in
`Airy1Gumbel/MesoscopicSpec.lean`. -/
theorem mesoscopic_of_bounds {Y : ℕ → Ω → ℝ} {W : ℝ → Ω → ℝ}
    (b : MesoscopicBounds P Y W) :
    ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
      Tendsto (fun N : ℕ =>
        (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0) := by
  intro z χ A hχ hχ1 hA
  have hχ3 := one_half_lt_cube_of_lt hχ
  have hθ0 : 0 < mesoTheta χ := mesoTheta_pos (by linarith)
  have hθ := mesoTheta_lt hχ3
  obtain ⟨d₀, -, hev⟩ := b.block_pair_le hθ hθ0
  have hχ0 : 0 < χ := lt_trans (Real.rpow_pos_of_pos (by norm_num) _) hχ
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
  have hlim := meso_envelope_tendsto_zero b.modC_pos b.modc_pos z χ A hχ hχ1 hA
  refine squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall fun N =>
      mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => measureReal_nonneg _)
  · filter_upwards [hmesh.eventually hev, hm.eventually (eventually_ge_atTop ⌈d₀⌉₊), htail,
      hu.eventually_ge_atTop b.coverLevel] with N hn hmN hp hlev
    have henv0 : 0 ≤ mesoPairEnvelope (2 * Real.exp (-airyH (gumbelU N z - 2)))
        (mesoTheta χ) b.modC b.modc (meshN (gumbelU N z)) (mN χ z N + 1) := by
      have := b.modC_pos
      unfold mesoPairEnvelope modFail
      positivity
    have hbound : ∀ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
        P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z} ≤
          mesoPairEnvelope (2 * Real.exp (-airyH (gumbelU N z - 2)))
            (mesoTheta χ) b.modC b.modc (meshN (gumbelU N z)) (mN χ z N + 1) := by
      intro j hj
      have hj1 : mN χ z N + 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjr : (mN χ z N : ℝ) ≤ (j : ℝ) - 1 := by
        have : ((mN χ z N + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj1
        push_cast at this
        linarith
      have hd : d₀ ≤ (j : ℝ) - 1 :=
        ((Nat.le_ceil d₀).trans (by exact_mod_cast hmN)).trans hjr
      refine (hn j (gumbelU N z) hlev hd).trans ?_
      unfold mesoPairEnvelope
      have hp0 : 0 ≤ P.real {ω | Y 0 ω > gumbelU N z - 2} := measureReal_nonneg _
      have hexp : Real.exp (-mesoTheta χ * ((j : ℝ) - 1) ^ 3) ≤
          Real.exp (-mesoTheta χ * (((mN χ z N + 1 : ℕ) : ℝ) - 1) ^ 3) := by
        apply Real.exp_le_exp.mpr
        push_cast
        rw [add_sub_cancel_right]
        have h3 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hjr 3) hθ0.le
        linarith
      have hsum := add_le_add (pow_le_pow_left₀ hp0 hp 2) hexp
      have := mul_le_mul_of_nonneg_left hsum (sq_nonneg ((meshN (gumbelU N z) : ℝ) + 1))
      linarith
    have hcard : ((Finset.Icc (mN χ z N + 1) (qN A N)).card : ℝ) ≤ (qN A N : ℝ) := by
      rw [Nat.card_Icc]
      exact_mod_cast (by omega : qN A N + 1 - (mN χ z N + 1) ≤ qN A N)
    calc (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}
        ≤ (N : ℝ) * ∑ _j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          mesoPairEnvelope (2 * Real.exp (-airyH (gumbelU N z - 2)))
            (mesoTheta χ) b.modC b.modc (meshN (gumbelU N z)) (mN χ z N + 1) := by
          gcongr with j hj
          exact hbound j hj
      _ = (N : ℝ) * ((Finset.Icc (mN χ z N + 1) (qN A N)).card *
          mesoPairEnvelope (2 * Real.exp (-airyH (gumbelU N z - 2)))
            (mesoTheta χ) b.modC b.modc (meshN (gumbelU N z)) (mN χ z N + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * ((qN A N : ℝ) *
          mesoPairEnvelope (2 * Real.exp (-airyH (gumbelU N z - 2)))
            (mesoTheta χ) b.modC b.modc (meshN (gumbelU N z)) (mN χ z N + 1)) := by
          gcongr
      _ = (N : ℝ) * (qN A N : ℝ) *
          mesoPairEnvelope (2 * Real.exp (-airyH (gumbelU N z - 2)))
            (mesoTheta χ) b.modC b.modc (meshN (gumbelU N z)) (mN χ z N + 1) := by
          ring

end MesoSum

end Airy1Gumbel
