/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.Assembly
import Airy1Gumbel.Blocking

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Airy1Gumbel

/-!
# Assembly layer, part 2: the conditional Gumbel limit

The headline theorem `Airy1BlockExtremes.gumbel_limit`: under the
`Airy1BlockExtremes` interface (stationarity, sharp tail, touching/separated/
mesoscopic negligibility, decoupling, pair mixing), the block maxima satisfy

  `P.real {ω | ∀ j ∈ Finset.range N, D.Y j ω ≤ gumbelU N z} → exp (-exp (-z))`.

The proof applies `gumbel_of_core_bounds` (from `Airy1Gumbel.Blocking`) with
the core-block safe-event probabilities supplied by `safe_coreBlock_bounds`
(T3) and the `D_{N,k}` control `D_eventually_le` (T4) from
`Airy1Gumbel.Assembly`; the product approximation is split into a discarded
set of indices (cardinality `≤ k + k q_N`, probability `o(1)` per fixed `k`)
and a decoupling telescope with error `k · alpha (q_N)` (also `o(1)` per fixed
`k` since `alpha` decays super-geometrically).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### Safe-event algebra -/

section SafeAlgebra

/-- The safe event over a disjoint union of index sets is the intersection of
the safe events. -/
lemma Safe_union (D : Airy1BlockExtremes P) (s t : Finset ℕ) (u : ℝ) :
    Safe D (s ∪ t) u = Safe D s u ∩ Safe D t u := by
  ext ω
  constructor
  · intro h
    constructor
    · intro j hj
      exact h j (Finset.mem_union_left t hj)
    · intro j hj
      exact h j (Finset.mem_union_right s hj)
  · rintro ⟨hs, ht⟩ j hj
    rcases Finset.mem_union.mp hj with hjs | hjt
    · exact hs j hjs
    · exact ht j hjt

/-- The safe event over a `biUnion` is the intersection over the parts. -/
lemma Safe_biUnion (D : Airy1BlockExtremes P) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t : ι → Finset ℕ) (u : ℝ) :
    Safe D (s.biUnion t) u = ⋂ m ∈ s, Safe D (t m) u := by
  ext ω
  constructor
  · intro h
    rw [Set.mem_iInter₂]
    intro m hm j hj
    exact h j (Finset.mem_biUnion.mpr ⟨m, hm, hj⟩)
  · intro h j hj
    rw [Set.mem_iInter₂] at h
    rcases Finset.mem_biUnion.mp hj with ⟨m, hm, hjm⟩
    exact h m hm j hjm

/-- The block maxima event of the headline theorem is exactly `Safe`. -/
lemma Safe_range_eq (D : Airy1BlockExtremes P) (N : ℕ) (u : ℝ) :
    Safe D (Finset.range N) u = {ω | ∀ j ∈ Finset.range N, D.Y j ω ≤ u} := rfl

end SafeAlgebra

/-! ### Core-block disjointness and the core-union cardinality -/

section CoreUnion

/-- Distinct core blocks are disjoint (they are consecutive index intervals
with a deleted buffer). -/
lemma coreBlock_disjoint {A : ℝ} {k N : ℕ} {m₁ m₂ : ℕ} (hm : m₁ ≠ m₂) :
    Disjoint (coreBlock A k N m₁) (coreBlock A k N m₂) := by
  rw [Finset.disjoint_left]
  intro j hj1 hj2
  simp only [coreBlock, Finset.mem_Ico] at hj1 hj2
  obtain ⟨h1, h2⟩ := hj1
  obtain ⟨h3, h4⟩ := hj2
  rcases lt_or_gt_of_ne hm with h | h
  · have hd : (m₁ + 1) * (N / k) ≤ m₂ * (N / k) := Nat.mul_le_mul_right (N / k) (by omega)
    omega
  · have hd : (m₂ + 1) * (N / k) ≤ m₁ * (N / k) := Nat.mul_le_mul_right (N / k) (by omega)
    omega

/-- The union of the `k` core blocks has exactly `k * (N / k - qN A N)`
elements. -/
lemma card_coreUnion {A : ℝ} (k N : ℕ) (hq : qN A N ≤ N / k) :
    ((Finset.range k).biUnion (coreBlock A k N)).card = k * (N / k - qN A N) := by
  have hpd : (↑(Finset.range k) : Set ℕ).PairwiseDisjoint (coreBlock A k N) :=
    fun m₁ _ m₂ _ h => coreBlock_disjoint h
  rw [Finset.card_biUnion hpd]
  have hsum : (∑ m ∈ Finset.range k, (coreBlock A k N m).card) =
      ∑ m ∈ Finset.range k, (N / k - qN A N) :=
    Finset.sum_congr rfl (fun m _ => coreBlock_card hq)
  rw [hsum, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The discarded set of indices has at most `k + k * qN A N` elements. -/
lemma card_discarded_le {A : ℝ} (k N : ℕ) (hk : 1 ≤ k) (hq : qN A N ≤ N / k) :
    (Finset.range N \ (Finset.range k).biUnion (coreBlock A k N)).card ≤ k + k * qN A N := by
  have hsub : (Finset.range k).biUnion (coreBlock A k N) ⊆ Finset.range N := by
    intro j hj
    rcases Finset.mem_biUnion.mp hj with ⟨m, hm, hjm⟩
    exact Finset.mem_range.mpr (coreBlock_subset_range hm hjm)
  have hinter : (Finset.range k).biUnion (coreBlock A k N) ∩ Finset.range N =
      (Finset.range k).biUnion (coreBlock A k N) :=
    Finset.inter_eq_left.mpr hsub
  rw [Finset.card_sdiff, hinter, Finset.card_range, card_coreUnion k N hq]
  have hmulsub : k * (N / k - qN A N) = k * (N / k) - k * qN A N := Nat.mul_sub_left_distrib _ _ _
  have hdm := Nat.div_add_mod N k
  have hmod : N % k < k := Nat.mod_lt N (by omega)
  have hkq : k * qN A N ≤ k * (N / k) := Nat.mul_le_mul_left k hq
  omega

end CoreUnion

/-! ### Limit ingredients -/

section Limits

/-- The ratio `⌊N/k⌋/N → 1/k` (with nat division), by squeezing
`|⌊N/k⌋/N - 1/k| ≤ 1/N`. -/
lemma tendsto_nat_div_div (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => ((N / k : ℕ) : ℝ) / N) atTop (𝓝 (1 / (k : ℝ))) := by
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h0 : Tendsto (fun N : ℕ => ((N / k : ℕ) : ℝ) / N - 1 / (k : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ tendsto_one_div_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h3 : (k : ℝ) * ((N / k : ℕ) : ℝ) ≤ (N : ℝ) := by
      have h := Nat.mul_div_le N k
      exact_mod_cast h
    have h4 : (N : ℝ) < (k : ℝ) * ((N / k : ℕ) : ℝ) + (k : ℝ) := by
      have h1 := Nat.div_add_mod N k
      have h2 : N % k < k := Nat.mod_lt N (by omega)
      have h5 : ((N % k : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast h2
      have h6 : (k : ℝ) * ((N / k : ℕ) : ℝ) + ((N % k : ℕ) : ℝ) = (N : ℝ) := by
        exact_mod_cast h1
      linarith
    have hnum : |((N / k : ℕ) : ℝ) * (k : ℝ) - (N : ℝ)| < (k : ℝ) := by
      rw [abs_lt]
      constructor <;> linarith
    rw [Real.norm_eq_abs]
    have hcalc : ((N / k : ℕ) : ℝ) / (N : ℝ) - 1 / (k : ℝ) =
        (((N / k : ℕ) : ℝ) * (k : ℝ) - (N : ℝ)) / ((N : ℝ) * (k : ℝ)) := by
      field_simp [hN0.ne', hkr.ne']
    rw [hcalc, abs_div, abs_of_pos (mul_pos hN0 hkr)]
    calc |((N / k : ℕ) : ℝ) * (k : ℝ) - (N : ℝ)| / ((N : ℝ) * (k : ℝ))
        ≤ (k : ℝ) / ((N : ℝ) * (k : ℝ)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hnum.le (inv_nonneg.mpr (mul_pos hN0 hkr).le)
      _ = 1 / (N : ℝ) := by
          field_simp [hN0.ne', hkr.ne']
  have h1 := h0.add_const (1 / (k : ℝ))
  rw [zero_add] at h1
  apply Tendsto.congr' _ h1
  filter_upwards with N
  ring

/-- The one-block exceedance probability along `u_N(z)` vanishes (since
`N * p_N → e^{-z}`). -/
lemma tendsto_oneTailExc_zero (D : Airy1BlockExtremes P) (z : ℝ) :
    Tendsto (fun N : ℕ => P.real (Exc D 0 (gumbelU N z))) atTop (𝓝 0) := by
  have hTN : Tendsto (fun N : ℕ => (N : ℝ) * P.real (Exc D 0 (gumbelU N z)))
      atTop (𝓝 (Real.exp (-z))) :=
    Tendsto.congr' (Eventually.of_forall fun N => rfl) (D.tail_normalized z)
  have h := hTN.mul tendsto_one_div_atTop_nhds_zero_nat
  rw [mul_zero] at h
  apply Tendsto.congr' _ h
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  calc ((N : ℝ) * P.real (Exc D 0 (gumbelU N z))) * (1 / (N : ℝ)) =
      P.real (Exc D 0 (gumbelU N z)) * ((N : ℝ) * (1 / (N : ℝ))) := by ring
    _ = P.real (Exc D 0 (gumbelU N z)) := by
        rw [mul_one_div, div_self hN0.ne', mul_one]

/-- `(qN A N : ℝ) / N → 0` since `qN A N ≤ A (log N)^{1/3} + 1`. -/
lemma tendsto_qN_div_N {A : ℝ} (hA : 0 < A) :
    Tendsto (fun N : ℕ => (qN A N : ℝ) / N) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun N : ℕ => A * ((Real.log N) ^ ((1 : ℝ) / 3) / N) + 1 / N)
  · filter_upwards with N
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards with N
    have hlog0 : (0 : ℝ) ≤ Real.log (N : ℝ) := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h
        simp
      · exact Real.log_nonneg (by exact_mod_cast h)
    have hceil : (qN A N : ℝ) < A * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 3) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hA.le (Real.rpow_nonneg hlog0 _))
    calc (qN A N : ℝ) / (N : ℝ) = (qN A N : ℝ) * (N : ℝ)⁻¹ := div_eq_mul_inv _ _
      _ ≤ (A * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 3) + 1) * (N : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hceil.le (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = A * ((Real.log (N : ℝ)) ^ ((1 : ℝ) / 3) / N) + 1 / N := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
  · have h := (tendsto_L13_div_N.const_mul A).add tendsto_one_div_atTop_nhds_zero_nat
    simpa using h

/-- `(qN A N : ℝ) * p_N → 0`. -/
lemma tendsto_qN_mul_p_zero (D : Airy1BlockExtremes P) (z : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun N : ℕ => (qN A N : ℝ) * P.real (Exc D 0 (gumbelU N z))) atTop (𝓝 0) := by
  have hTN : Tendsto (fun N : ℕ => (N : ℝ) * P.real (Exc D 0 (gumbelU N z)))
      atTop (𝓝 (Real.exp (-z))) :=
    Tendsto.congr' (Eventually.of_forall fun N => rfl) (D.tail_normalized z)
  have h := (tendsto_qN_div_N hA).mul hTN
  rw [zero_mul] at h
  apply Tendsto.congr' _ h
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  calc ((qN A N : ℝ) / (N : ℝ)) * ((N : ℝ) * P.real (Exc D 0 (gumbelU N z))) =
      (qN A N : ℝ) * P.real (Exc D 0 (gumbelU N z)) * ((N : ℝ) / (N : ℝ)) := by ring
    _ = (qN A N : ℝ) * P.real (Exc D 0 (gumbelU N z)) := by
        rw [div_self hN0.ne', mul_one]

/-- The effective core size times the one-block probability converges to
`τ / k`: `ℓ p_N → τ/k` where `ℓ = N/k - qN A N`. -/
lemma tendsto_ell_p (D : Airy1BlockExtremes P) (z : ℝ) {A : ℝ} (hA : 0 < A) {k : ℕ}
    (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => ((N / k - qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)))
      atTop (𝓝 (Real.exp (-z) / (k : ℝ))) := by
  have hTN : Tendsto (fun N : ℕ => (N : ℝ) * P.real (Exc D 0 (gumbelU N z)))
      atTop (𝓝 (Real.exp (-z))) :=
    Tendsto.congr' (Eventually.of_forall fun N => rfl) (D.tail_normalized z)
  have h1 : Tendsto (fun N : ℕ => ((N / k : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)))
      atTop (𝓝 (Real.exp (-z) / (k : ℝ))) := by
    have hratio := tendsto_nat_div_div k hk
    have h := hratio.mul hTN
    rw [one_div_mul_eq_div] at h
    apply Tendsto.congr' _ h
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    calc (((N / k : ℕ) : ℝ) / (N : ℝ)) * ((N : ℝ) * P.real (Exc D 0 (gumbelU N z))) =
        ((N / k : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)) * ((N : ℝ) / (N : ℝ)) := by ring
      _ = ((N / k : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)) := by
          rw [div_self hN0.ne', mul_one]
  have h2 := tendsto_qN_mul_p_zero D z hA
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  apply Tendsto.congr' _ h3
  filter_upwards [eventually_qN_add_le_div hA hk 0] with N hqN
  have hq : qN A N ≤ N / k := by simpa using hqN
  rw [Nat.cast_sub hq]
  ring

/-- `alpha (qN A N) → 0`: the elementary mixing bound composed with
`qN A N → ∞`, via `exp(c·(x-1)³) → ∞` and inversion. -/
lemma tendsto_alpha_qN (D : Airy1BlockExtremes P) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun N : ℕ => D.alpha (qN A N)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun x : ℝ => x - 1) atTop atTop := by
    apply tendsto_atTop_mono' atTop _
      (Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2) tendsto_id)
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    dsimp
    linarith
  have hpow : Tendsto (fun x : ℝ => (x - 1) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hshift
  have hmul : Tendsto (fun x : ℝ => D.mixc * (x - 1) ^ 3) atTop atTop :=
    hpow.const_mul_atTop D.mixc_pos
  have hinv : Tendsto (fun x : ℝ => (Real.exp (D.mixc * (x - 1) ^ 3))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_exp_atTop.comp hmul)
  have hexp : Tendsto (fun x : ℝ => Real.exp (-D.mixc * (x - 1) ^ 3)) atTop (𝓝 0) := by
    apply Tendsto.congr' _ hinv
    filter_upwards with x
    rw [neg_mul, Real.exp_neg]
  have hcomp := hexp.comp (tendsto_qN_atTop hA)
  have hbound : Tendsto (fun N : ℕ => D.mixC * Real.exp (-D.mixc * ((qN A N : ℝ) - 1) ^ 3))
      atTop (𝓝 (D.mixC * 0)) := hcomp.const_mul D.mixC
  rw [mul_zero] at hbound
  exact squeeze_zero' (Eventually.of_forall fun N => D.alpha_nonneg _)
    (Eventually.of_forall fun N => D.alpha_bound _) hbound

end Limits

/-! ### The core estimate `hcore` -/

section HCore

/-- The per-core estimate: for fixed `k ≥ 1`, each core safe probability is
within `error k / k + o(1)` of `1 - τ/k`, where
`error k = τ²/k + 1/k` is the `D_eventually_le` bound divided by `k`. -/
lemma hcore_eventually (D : Airy1BlockExtremes P) (z : ℝ) {A : ℝ} (hA : 0 < A) {k : ℕ}
    (hk : 1 ≤ k) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ m ∈ Finset.range k,
      |P.real (Safe D (coreBlock A k N m) (gumbelU N z)) - (1 - Real.exp (-z) / (k : ℝ))| ≤
        (Real.exp (-z) ^ 2 / (k : ℝ) + 1 / (k : ℝ)) / (k : ℝ) + ε := by
  intro ε hε
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlpε : ∀ᶠ N : ℕ in atTop,
      |((N / k - qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)) -
        Real.exp (-z) / (k : ℝ)| < ε := by
    have h := (Metric.tendsto_nhds.mp (tendsto_ell_p D z hA hk)) ε hε
    filter_upwards [h] with N hN
    rw [Real.dist_eq] at hN
    exact hN
  filter_upwards [D_eventually_le D z k hk, eventually_qN_add_le_div hA hk 0,
    eventually_ge_atTop 1, hlpε] with N hDD hqN hN1 hlpN
  intro m _
  have hq : qN A N ≤ N / k := by simpa using hqN
  have hb := safe_coreBlock_bounds D (A := A) (k := k) (N := N) (m := m) hq (gumbelU N z)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hS0 : 0 ≤ ∑ r ∈ Finset.Icc 1 (N / k),
      P.real (Exc D 0 (gumbelU N z) ∩ Exc D r (gumbelU N z)) :=
    Finset.sum_nonneg (fun r _ => measureReal_nonneg _)
  have hDD0 : 0 ≤ DD D z k N := mul_nonneg (Nat.cast_nonneg _) hS0
  have hDD_eq : DD D z k N = (N : ℝ) * ∑ r ∈ Finset.Icc 1 (N / k),
      P.real (Exc D 0 (gumbelU N z) ∩ Exc D r (gumbelU N z)) := rfl
  have hSDD : (∑ r ∈ Finset.Icc 1 (N / k),
      P.real (Exc D 0 (gumbelU N z) ∩ Exc D r (gumbelU N z))) = DD D z k N / (N : ℝ) := by
    rw [hDD_eq, mul_div_cancel_left₀ _ hN0.ne']
  -- first step: distance from `core` to `1 - ℓ p` is at most `ℓ · S`
  have hstep1 : |P.real (Safe D (coreBlock A k N m) (gumbelU N z)) -
        (1 - ((N / k - qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)))| ≤
      ((N / k - qN A N : ℕ) : ℝ) * (DD D z k N / (N : ℝ)) := by
    rw [abs_of_nonneg (by linarith [hb.1] : (0 : ℝ) ≤
        P.real (Safe D (coreBlock A k N m) (gumbelU N z)) -
          (1 - ((N / k - qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z))))]
    rw [← hSDD]
    linarith [hb.2]
  -- second step: `ℓ · (DD / N) ≤ DD / k`
  have hstep2 : ((N / k - qN A N : ℕ) : ℝ) * (DD D z k N / (N : ℝ)) ≤
      DD D z k N / (k : ℝ) := by
    have h1 : ((N / k - qN A N : ℕ) : ℝ) ≤ ((N / k : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    have h2 : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := Nat.cast_div_le
    calc ((N / k - qN A N : ℕ) : ℝ) * (DD D z k N / (N : ℝ))
        ≤ ((N / k : ℕ) : ℝ) * (DD D z k N / (N : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (div_nonneg hDD0 hN0.le)
      _ ≤ ((N : ℝ) / k) * (DD D z k N / (N : ℝ)) :=
          mul_le_mul_of_nonneg_right h2 (div_nonneg hDD0 hN0.le)
      _ = DD D z k N / (k : ℝ) := by
          field_simp [hN0.ne', hkr.ne']
  -- third step: `DD / k ≤ error k / k` from `D_eventually_le`
  have hstep3 : DD D z k N / (k : ℝ) ≤
      (Real.exp (-z) ^ 2 / (k : ℝ) + 1 / (k : ℝ)) / (k : ℝ) := by
    gcongr
  -- assemble
  calc |P.real (Safe D (coreBlock A k N m) (gumbelU N z)) - (1 - Real.exp (-z) / (k : ℝ))|
      ≤ |P.real (Safe D (coreBlock A k N m) (gumbelU N z)) -
          (1 - ((N / k - qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)))| +
        |((N / k - qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)) -
          Real.exp (-z) / (k : ℝ)| := by
          have h := abs_sub_le (P.real (Safe D (coreBlock A k N m) (gumbelU N z)))
            (1 - ((N / k - qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)))
            (1 - Real.exp (-z) / (k : ℝ))
          rw [show (1 - ((N / k - qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z))) -
              (1 - Real.exp (-z) / (k : ℝ)) =
              -(((N / k - qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)) -
                Real.exp (-z) / (k : ℝ)) from by ring, abs_neg] at h
          exact h
    _ ≤ ((N / k - qN A N : ℕ) : ℝ) * (DD D z k N / (N : ℝ)) + ε :=
        add_le_add hstep1 hlpN.le
    _ ≤ DD D z k N / (k : ℝ) + ε := add_le_add hstep2 le_rfl
    _ ≤ (Real.exp (-z) ^ 2 / (k : ℝ) + 1 / (k : ℝ)) / (k : ℝ) + ε :=
        add_le_add hstep3 le_rfl

end HCore

/-! ### The product estimate `hproduct`: the decoupling telescope -/

section HProduct

/-- Splitting an `iInter` over `range (m+1)` off at the last index. -/
lemma iInter_range_succ {α : Type*} (E : ℕ → Set α) (m : ℕ) :
    (⋂ m' ∈ Finset.range (m + 1), E m') = (⋂ m' ∈ Finset.range m, E m') ∩ E m := by
  ext ω
  constructor
  · intro h
    have h' : ∀ m', m' ∈ Finset.range (m + 1) → ω ∈ E m' :=
      fun m' hm' => Set.mem_iInter₂.mp h m' hm'
    constructor
    · rw [Set.mem_iInter₂]
      intro m' hm'
      exact h' m' (Finset.mem_range.mpr (by
        simp only [Finset.mem_range] at hm'
        omega))
    · exact h' m (Finset.mem_range.mpr (Nat.lt_add_one m))
  · intro h
    rw [Set.mem_iInter₂]
    intro m' hm'
    obtain ⟨h1, h2⟩ := h
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm')) with rfl | hlt
    · exact h2
    · exact Set.mem_iInter₂.mp h1 m' (Finset.mem_range.mpr hlt)

/-- The decoupling telescope: for fixed `k, N`, the probability of the
intersection over the first `m` core blocks differs from the product of the
marginals by at most `m · alpha (qN A N)`, each step being one application of
`decouple` across the `qN`-buffer. -/
lemma decouple_telescope_aux (D : Airy1BlockExtremes P) (A : ℝ) (k N : ℕ) (u : ℝ) :
    ∀ m : ℕ, m ≤ k →
      |P.real (⋂ m' ∈ Finset.range m, Safe D (coreBlock A k N m') u) -
        ∏ m' ∈ Finset.range m, P.real (Safe D (coreBlock A k N m') u)| ≤
        (m : ℝ) * D.alpha (qN A N) := by
  intro m
  induction m with
  | zero =>
    intro _
    have huniv : (⋂ m' ∈ Finset.range 0, Safe D (coreBlock A k N m') u) = Set.univ := by
      ext ω
      simp [Finset.range_zero]
    rw [huniv, Finset.range_zero, Finset.prod_empty, measureReal_univ]
    simp
  | succ m ihm =>
    intro hmk1
    have hmk : m ≤ k := by omega
    have ih := ihm hmk
    set E : ℕ → Set Ω := fun m' => Safe D (coreBlock A k N m') u with hEdef
    set S : Finset ℕ := (Finset.range m).biUnion (coreBlock A k N) with hSdef
    set T : Finset ℕ := coreBlock A k N m with hTdef
    have hsep : ∀ s ∈ S, ∀ t ∈ T, s + qN A N ≤ t := by
      intro s hs t ht
      rcases Finset.mem_biUnion.mp hs with ⟨m', hm', hsm'⟩
      exact coreBlock_separated (Finset.mem_range.mp hm') hsm' ht
    have hdec := D.decouple S T (qN A N) u hsep
    have hdec' : |P.real ((⋂ m' ∈ Finset.range m, Safe D (coreBlock A k N m') u) ∩
        Safe D (coreBlock A k N m) u) -
        P.real (⋂ m' ∈ Finset.range m, Safe D (coreBlock A k N m') u) *
          P.real (Safe D (coreBlock A k N m) u)| ≤ D.alpha (qN A N) := by
      have hSb : Safe D S u = ⋂ m' ∈ Finset.range m, Safe D (coreBlock A k N m') u :=
        Safe_biUnion D (Finset.range m) (coreBlock A k N) u
      rw [← hSb]
      exact hdec
    have hE1 : P.real (Safe D (coreBlock A k N m) u) ≤ 1 := by
      calc P.real (Safe D (coreBlock A k N m) u) ≤ P.real Set.univ :=
            measureReal_mono (Set.subset_univ _)
        _ = 1 := measureReal_univ
    rw [iInter_range_succ, Finset.prod_range_succ]
    calc |P.real ((⋂ m' ∈ Finset.range m, Safe D (coreBlock A k N m') u) ∩
            Safe D (coreBlock A k N m) u) -
          (∏ m' ∈ Finset.range m, P.real (Safe D (coreBlock A k N m') u)) *
            P.real (Safe D (coreBlock A k N m) u)|
        = |(P.real ((⋂ m' ∈ Finset.range m, Safe D (coreBlock A k N m') u) ∩
              Safe D (coreBlock A k N m) u) -
            P.real (⋂ m' ∈ Finset.range m, Safe D (coreBlock A k N m') u) *
              P.real (Safe D (coreBlock A k N m) u)) +
          (P.real (⋂ m' ∈ Finset.range m, Safe D (coreBlock A k N m') u) *
              P.real (Safe D (coreBlock A k N m) u) -
            (∏ m' ∈ Finset.range m, P.real (Safe D (coreBlock A k N m') u)) *
              P.real (Safe D (coreBlock A k N m) u))| := by
          congr 1
          ring
      _ ≤ |P.real ((⋂ m' ∈ Finset.range m, Safe D (coreBlock A k N m') u) ∩
            Safe D (coreBlock A k N m) u) -
          P.real (⋂ m' ∈ Finset.range m, Safe D (coreBlock A k N m') u) *
            P.real (Safe D (coreBlock A k N m) u)| +
        |P.real (⋂ m' ∈ Finset.range m, Safe D (coreBlock A k N m') u) *
            P.real (Safe D (coreBlock A k N m) u) -
          (∏ m' ∈ Finset.range m, P.real (Safe D (coreBlock A k N m') u)) *
            P.real (Safe D (coreBlock A k N m) u)| := abs_add_le _ _
      _ ≤ D.alpha (qN A N) +
          |P.real (⋂ m' ∈ Finset.range m, Safe D (coreBlock A k N m') u) -
            ∏ m' ∈ Finset.range m, P.real (Safe D (coreBlock A k N m') u)| *
            P.real (Safe D (coreBlock A k N m) u) := by
        apply add_le_add hdec'
        rw [← sub_mul, abs_mul, abs_of_nonneg (measureReal_nonneg _)]
      _ ≤ D.alpha (qN A N) + ((m : ℝ) * D.alpha (qN A N)) * 1 := by
        exact add_le_add le_rfl (mul_le_mul ih hE1 (measureReal_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (D.alpha_nonneg _)))
      _ = ((m + 1 : ℕ) : ℝ) * D.alpha (qN A N) := by
        push_cast
        ring

/-- The telescope over all `k` cores, in `Safe`-of-union form. -/
lemma decouple_telescope (D : Airy1BlockExtremes P) (A : ℝ) (k N : ℕ) (u : ℝ) :
    |P.real (Safe D ((Finset.range k).biUnion (coreBlock A k N)) u) -
      ∏ m ∈ Finset.range k, P.real (Safe D (coreBlock A k N m) u)| ≤
      (k : ℝ) * D.alpha (qN A N) := by
  rw [Safe_biUnion]
  exact decouple_telescope_aux D A k N u k le_rfl

/-- Piece 1 of the product estimate: discarding the non-core indices costs at
most `(k + k * qN A N) * p_N`. -/
lemma piece1_bound (D : Airy1BlockExtremes P) (z : ℝ) {A : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (N : ℕ) (hq : qN A N ≤ N / k) :
    |P.real (Safe D (Finset.range N) (gumbelU N z)) -
      P.real (Safe D ((Finset.range k).biUnion (coreBlock A k N)) (gumbelU N z))| ≤
      ((k + k * qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)) := by
  set G : Finset ℕ := Finset.range N \ (Finset.range k).biUnion (coreBlock A k N) with hGdef
  have hsub : (Finset.range k).biUnion (coreBlock A k N) ⊆ Finset.range N := by
    intro j hj
    rcases Finset.mem_biUnion.mp hj with ⟨m, hm, hjm⟩
    exact Finset.mem_range.mpr (coreBlock_subset_range hm hjm)
  have hsplit : Finset.range N = ((Finset.range k).biUnion (coreBlock A k N)) ∪ G :=
    (Finset.union_sdiff_of_subset hsub).symm
  have hSafe_split : Safe D (Finset.range N) (gumbelU N z) =
      Safe D ((Finset.range k).biUnion (coreBlock A k N)) (gumbelU N z) ∩
        Safe D G (gumbelU N z) := by
    rw [hsplit]
    exact Safe_union D _ _ _
  rw [hSafe_split]
  have hY : MeasurableSet (Safe D G (gumbelU N z)) := measurableSafe _ _ _
  have h1 : |P.real (Safe D ((Finset.range k).biUnion (coreBlock A k N)) (gumbelU N z) ∩
      Safe D G (gumbelU N z)) -
      P.real (Safe D ((Finset.range k).biUnion (coreBlock A k N)) (gumbelU N z))| ≤
      P.real (Safe D G (gumbelU N z))ᶜ :=
    abs_measureReal_inter_sub_le_compl hY
  have hcard : G.card ≤ k + k * qN A N := by
    have h := card_discarded_le k N hk hq
    rw [hGdef]
    exact h
  have h2 : P.real (Safe D G (gumbelU N z))ᶜ ≤
      ((k + k * qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)) := by
    rw [Safe_eq_compl_biUnion, compl_compl]
    calc P.real (⋃ j ∈ G, Exc D j (gumbelU N z))
        ≤ ∑ j ∈ G, P.real (Exc D j (gumbelU N z)) := measureReal_biUnion_finset_le _ _
      _ = ∑ j ∈ G, P.real (Exc D 0 (gumbelU N z)) :=
          Finset.sum_congr rfl (fun j _ => Exc_real_eq _ _ _)
      _ = (G.card : ℝ) * P.real (Exc D 0 (gumbelU N z)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((k + k * qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (measureReal_nonneg _)
  exact h1.trans h2

/-- The product estimate `hproduct`: for fixed `k ≥ 1`, the safe probability
over `range N` is within `o(1)` of the product of the per-core safe
probabilities. -/
lemma hproduct_eventually (D : Airy1BlockExtremes P) (z : ℝ) {A : ℝ} (hA : 0 < A) {k : ℕ}
    (hk : 1 ≤ k) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      |P.real (Safe D (Finset.range N) (gumbelU N z)) -
        ∏ m ∈ Finset.range k, P.real (Safe D (coreBlock A k N m) (gumbelU N z))| ≤ ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  -- piece-1 limit: `(k + k * qN) * p_N → 0`
  have hlim1 : Tendsto (fun N : ℕ => ((k + k * qN A N : ℕ) : ℝ) *
      P.real (Exc D 0 (gumbelU N z))) atTop (𝓝 0) := by
    have h1 := (tendsto_oneTailExc_zero D z).const_mul (k : ℝ)
    have h2 := (tendsto_qN_mul_p_zero D z hA).const_mul (k : ℝ)
    have h := h1.add h2
    rw [mul_zero, add_zero] at h
    apply Tendsto.congr' _ h
    filter_upwards with N
    push_cast
    ring
  -- piece-2 limit: `k * alpha (qN) → 0`
  have hlim2 : Tendsto (fun N : ℕ => (k : ℝ) * D.alpha (qN A N)) atTop (𝓝 0) := by
    have h := (tendsto_alpha_qN D hA).const_mul (k : ℝ)
    rwa [mul_zero] at h
  have h1ε : ∀ᶠ N : ℕ in atTop, ((k + k * qN A N : ℕ) : ℝ) *
      P.real (Exc D 0 (gumbelU N z)) < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp hlim1) (ε / 2) hε2
    filter_upwards [h] with N hN
    rw [Real.dist_eq, sub_zero] at hN
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (measureReal_nonneg _))] at hN
    exact hN
  have h2ε : ∀ᶠ N : ℕ in atTop, (k : ℝ) * D.alpha (qN A N) < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp hlim2) (ε / 2) hε2
    filter_upwards [h] with N hN
    rw [Real.dist_eq, sub_zero] at hN
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (D.alpha_nonneg _))] at hN
    exact hN
  filter_upwards [h1ε, h2ε, eventually_qN_add_le_div hA hk 0] with N h1N h2N hqN
  have hq : qN A N ≤ N / k := by simpa using hqN
  have hpiece1 := piece1_bound D z hk N hq
  have hpiece2 := decouple_telescope D A k N (gumbelU N z)
  calc |P.real (Safe D (Finset.range N) (gumbelU N z)) -
        ∏ m ∈ Finset.range k, P.real (Safe D (coreBlock A k N m) (gumbelU N z))|
      ≤ |P.real (Safe D (Finset.range N) (gumbelU N z)) -
          P.real (Safe D ((Finset.range k).biUnion (coreBlock A k N)) (gumbelU N z))| +
        |P.real (Safe D ((Finset.range k).biUnion (coreBlock A k N)) (gumbelU N z)) -
          ∏ m ∈ Finset.range k, P.real (Safe D (coreBlock A k N m) (gumbelU N z))| :=
        abs_sub_le _ _ _
    _ ≤ ((k + k * qN A N : ℕ) : ℝ) * P.real (Exc D 0 (gumbelU N z)) +
          (k : ℝ) * D.alpha (qN A N) := add_le_add hpiece1 hpiece2
    _ ≤ ε / 2 + ε / 2 := add_le_add h1N.le h2N.le
    _ = ε := by ring

end HProduct

/-! ### The headline theorem -/

/-- **Conditional Gumbel limit** (the paper's main theorem (Theorem 1.1),
integer-block form). The conclusion is exactly the paper's statement for the
block maxima; the Airy-specific inputs are the named fields of
`Airy1BlockExtremes` and are NOT proved here. -/
theorem Airy1BlockExtremes.gumbel_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : Airy1BlockExtremes P) (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ j ∈ Finset.range N, D.Y j ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  obtain ⟨A₀, hA₀, hA₀c, -⟩ := D.mixing_tail
  set A : ℝ := max A₀ (Real.sqrt (6 * airyGamma)) with hAdef
  have hApos : 0 < A := hA₀.trans_le (le_max_left _ _)
  have hτ : 0 < Real.exp (-z) := Real.exp_pos _
  have herror : Tendsto (fun k : ℕ => Real.exp (-z) ^ 2 / (k : ℝ) + 1 / (k : ℝ))
      atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.exp (-z) ^ 2)).add
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    simpa using h
  have hcore01 : ∀ (N k m : ℕ),
      0 ≤ P.real (Safe D (coreBlock A k N m) (gumbelU N z)) ∧
        P.real (Safe D (coreBlock A k N m) (gumbelU N z)) ≤ 1 := by
    intro N k m
    constructor
    · exact measureReal_nonneg _
    · calc P.real (Safe D (coreBlock A k N m) (gumbelU N z)) ≤ P.real Set.univ :=
            measureReal_mono (Set.subset_univ _)
        _ = 1 := measureReal_univ
  have hcore : ∀ᶠ k : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ m ∈ Finset.range k,
        |P.real (Safe D (coreBlock A k N m) (gumbelU N z)) -
          (1 - Real.exp (-z) / (k : ℝ))| ≤
          (Real.exp (-z) ^ 2 / (k : ℝ) + 1 / (k : ℝ)) / (k : ℝ) + ε := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact hcore_eventually D z hApos hk
  have hproduct : ∀ᶠ k : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      |P.real (Safe D (Finset.range N) (gumbelU N z)) -
        ∏ m ∈ Finset.range k, P.real (Safe D (coreBlock A k N m) (gumbelU N z))| ≤ ε := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact hproduct_eventually D z hApos hk
  have h := gumbel_of_core_bounds _ _ _ _ hτ hcore01 herror hcore hproduct
  exact h

end Airy1Gumbel
