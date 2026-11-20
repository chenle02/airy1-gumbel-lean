/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.ContinuousVersion
import Airy1Gumbel.GOELeftTail
import Airy1GumbelContrib.SmallWeight.SmallWeightDefect

open MeasureTheory Set Filter ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace Airy1Gumbel

/-!
# Lower boundedness and the real-valued continuous Airy₁ version

On `(ℝ → ℝ, airy1Law h)` we prove that the coordinate path is almost surely bounded **below** on
the rational times of every `[0, N]` (`airy1Law_lowEvent`, `ae_bddBelow_rat`), and glue the
lower-clamped continuous versions `airy1ContL h (−m)` over `m` into a **real-valued**
continuous version `airy1Cont h` of the coordinate process on `ℝ≥0`
(`exists_continuous_version`): measurable marginals, `airy1Cont h t =ᵐ (· t)` for every `t`,
every path continuous and locally `β`-Hölder for every `β < 1/2`.

## Inputs

* **(H1) left tail**: the external-input record `GOELeftTail` (BBD 2008),
  `∃ C c, 0 < C ∧ 0 < c ∧ ∀ M ≥ 0, F_{0}(−M) ≤ C e^{−c M³}` (its field `tail`).
* **(H2) small-weight defect constants**: proved in contrib,
  `AiryFdd.smallWeight_defect_headline`: for `M ≥ 2` the forward and reverse two-time defect
  bounds `AiryFdd.FwdDefectBoundOn` / `AiryFdd.RevDefectBoundOn` at lower level `−2M` for gaps
  `0 < t ≤ 1/(2M)` with constant `C_M = exp(K M^{5/2})`.

The general form `airy1Law_lowEvent_of` takes (H1) as the raw `∃`-statement and (H2) as any
`CM` with `log (CM M) ≤ K M^α`, `α < 3`; the headlines `airy1Law_lowEvent`,
`exists_continuous_version` take only `GOELeftTail`, discharging (H2) at `α = 5/2`. The
construction of `airy1Cont`, its measurability, continuity and Hölder property are
unconditional; the modification property needs only almost sure lower boundedness on rationals
(`airy1Cont_ae_eq_of`).

## Route (with windows in place of a separate grid)

Fix `M ≥ 2`, the clamp `X = clamp_{[−2M, 0]}`, and windows of length `ℓ = 1/n` with
`n = ⌈e^{cM³/2} + 2M⌉₊` (so `ℓ ≤ 1/(2M)`, the gap range of (H2)). If some rational `x ∈ [0,N]`
has `f x < −2M`, then in the window `[j/n, (j+1)/n)` containing `x` either `f (j/n) ≤ −M`
(probability `≤ C e^{−cM³}` by (H1) and stationarity of one-point laws) or `X` oscillates by
`> M` inside the window. For the second event, the time-rescaled window process
`s ↦ X(j/n + ℓ min(s,1))` is a Kolmogorov process with constant `K_M ℓ^{3/2}` (the moment bound
`lintegral_clamp_incr_rpow_le`, re-run for gaps `≤ δ`: `lintegral_clamp_incr_rpow_le_on`); BM's quantitative
`countable_kolmogorov_chentsov` (order `p = 4`, `β = 1/16`) and Markov give
`≤ K_M ℓ^{3/2} L_KC / M⁴`. Summing over the `nN + 1` windows,
`P(inf_{ℚ∩[0,N]} f < −2M) ≤ (N+1)(C(e^{−cM³/2} + 2e^{M−cM³}) + 8(2A+B)L_KC e^{K M^α + M − cM³/4})`,
which tends to `0` since `α < 3` (`tendsto_exp_cubic`). Gluing: on the full-measure event
`goodLowSet` the continuous paths `Z_m = airy1ContL h (−m)` satisfy `Z_m = max(−m, Z_{m'})`
(`m ≤ m'`), are bounded below on `[0, N)` uniformly in `m`, hence stabilize; `airy1Cont` is
their infimum.
-/

/-! ## Gap-restricted defect hypotheses -/

/-- The main library's forward defect-bound shape is the gap-`1` case of contrib's
gap-restricted shape. -/
theorem fwdDefectBoundOn_one_iff {L C : ℝ} :
    AiryFdd.FwdDefectBoundOn L 1 C ↔ FwdDefectBound L C :=
  Iff.rfl

/-- The main library's reverse defect-bound shape is the gap-`1` case of contrib's
gap-restricted shape. -/
theorem revDefectBoundOn_one_iff {L C : ℝ} :
    AiryFdd.RevDefectBoundOn L 1 C ↔ RevDefectBound L C :=
  Iff.rfl

/-! ## The two-point moment bounds re-run for gaps `≤ δ` -/

/-- Forward crossing probability for gaps `0 < t ≤ δ`. -/
theorem airy1Law_fwd_le_on (h : Airy1FddPositive) {L δ C : ℝ}
    (hF : AiryFdd.FwdDefectBoundOn L δ C)
    {x t a b : ℝ} (ht : 0 < t) (htδ : t ≤ δ) (ha : L ≤ a) (hab : a ≤ b) :
    airy1Law h {f : ℝ → ℝ | f x ≤ a ∧ b < f (x + t)}
      ≤ ENNReal.ofReal (C * Real.exp (-(b - a) ^ 2 / (8 * t))) := by
  classical
  have hne : x + t ≠ x := ne_of_gt (by linarith)
  let lev : ℝ → ℝ := fun s => if s = x then a else b
  have hA : (airy1Law h).real {f : ℝ → ℝ | ∀ s ∈ ({x} : Finset ℝ), f s ≤ (fun _ => a) s}
      = AiryFdd.airy1FinCdf {x} (fun _ => a) := airy1Law_fdd h {x} (fun _ => a)
  have hB : (airy1Law h).real {f : ℝ → ℝ | ∀ s ∈ ({x, x + t} : Finset ℝ), f s ≤ lev s}
      = AiryFdd.airy1FinCdf {x, x + t} (fun i => lev i) := airy1Law_fdd h {x, x + t} lev
  have hset : {f : ℝ → ℝ | f x ≤ a ∧ b < f (x + t)}
      = {f : ℝ → ℝ | ∀ s ∈ ({x} : Finset ℝ), f s ≤ (fun _ => a) s}
        \ {f : ℝ → ℝ | ∀ s ∈ ({x, x + t} : Finset ℝ), f s ≤ lev s} := by
    ext f
    simp only [lev, mem_ofPred_eq, Set.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      forall_eq_or_imp, forall_eq, hne, reduceIte, not_and, not_le]
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
  have hsub : {f : ℝ → ℝ | ∀ s ∈ ({x, x + t} : Finset ℝ), f s ≤ lev s}
      ⊆ {f : ℝ → ℝ | ∀ s ∈ ({x} : Finset ℝ), f s ≤ (fun _ => a) s} := by
    intro f hf s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    have := hf s (by simp)
    simpa [lev] using this
  rw [hset, ← ofReal_measureReal, measureReal_sdiff hsub
    (measurableSet_setOf_forall_mem_finset_le _ _), hA, hB]
  refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
  exact hF x t a b (fun i => lev i) ht htδ ha hab (fun _ => by simp [lev])
    (fun _ => by simp [lev, hne])

/-- Reverse crossing probability for gaps `0 < t ≤ δ`. -/
theorem airy1Law_rev_le_on (h : Airy1FddPositive) {L δ C : ℝ}
    (hR : AiryFdd.RevDefectBoundOn L δ C)
    {x t a b : ℝ} (ht : 0 < t) (htδ : t ≤ δ) (hb : L ≤ b) (hba : b ≤ a) :
    airy1Law h {f : ℝ → ℝ | a < f x ∧ f (x + t) ≤ b}
      ≤ ENNReal.ofReal (C * Real.exp (-(a - b) ^ 2 / (8 * t))) := by
  classical
  have hne : x + t ≠ x := ne_of_gt (by linarith)
  let lev : ℝ → ℝ := fun s => if s = x then a else b
  have hA : (airy1Law h).real {f : ℝ → ℝ | ∀ s ∈ ({x + t} : Finset ℝ), f s ≤ (fun _ => b) s}
      = AiryFdd.airy1FinCdf {x + t} (fun _ => b) := airy1Law_fdd h {x + t} (fun _ => b)
  have hB : (airy1Law h).real {f : ℝ → ℝ | ∀ s ∈ ({x, x + t} : Finset ℝ), f s ≤ lev s}
      = AiryFdd.airy1FinCdf {x, x + t} (fun i => lev i) := airy1Law_fdd h {x, x + t} lev
  have hset : {f : ℝ → ℝ | a < f x ∧ f (x + t) ≤ b}
      = {f : ℝ → ℝ | ∀ s ∈ ({x + t} : Finset ℝ), f s ≤ (fun _ => b) s}
        \ {f : ℝ → ℝ | ∀ s ∈ ({x, x + t} : Finset ℝ), f s ≤ lev s} := by
    ext f
    simp only [lev, mem_ofPred_eq, Set.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      forall_eq_or_imp, forall_eq, hne, reduceIte, not_and, not_le]
    exact ⟨fun h => ⟨h.2, fun h' => absurd h' (not_le.2 h.1)⟩,
      fun h => ⟨lt_of_not_ge fun h' => absurd h.1 (not_le.2 (h.2 h')), h.1⟩⟩
  have hsub : {f : ℝ → ℝ | ∀ s ∈ ({x, x + t} : Finset ℝ), f s ≤ lev s}
      ⊆ {f : ℝ → ℝ | ∀ s ∈ ({x + t} : Finset ℝ), f s ≤ (fun _ => b) s} := by
    intro f hf s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    have := hf (x + t) (by simp)
    simpa [lev, hne] using this
  rw [hset, ← ofReal_measureReal, measureReal_sdiff hsub
    (measurableSet_setOf_forall_mem_finset_le _ _), hA, hB]
  refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
  exact hR x t a b (fun i => lev i) ht htδ hb hba (fun _ => by simp [lev])
    (fun _ => by simp [lev, hne])

/-- Tail of the clamped increment for gaps `0 < t ≤ δ` (grid union bound, as
`airy1Law_clamp_gap_le`). -/
theorem airy1Law_clamp_gap_le_on (h : Airy1FddPositive) {L U δ C C' : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn L δ C)
    (hR : AiryFdd.RevDefectBoundOn L δ C')
    {x t z : ℝ} (ht : 0 < t) (htδ : t ≤ δ) (hz : 0 < z) :
    airy1Law h {f : ℝ → ℝ | z < |clampTo L U (f (x + t)) - clampTo L U (f x)|}
      ≤ ENNReal.ofReal ((C + C') * (2 * (U - L) / z + 1) * Real.exp (-z ^ 2 / (32 * t))) := by
  have hδ0 : 0 < z / 2 := by positivity
  let N : ℕ := ⌈(U - L) / (z / 2)⌉₊
  let g : ℕ → ℝ := fun k => L + ((k : ℝ) + 1) * (z / 2)
  have hLg : ∀ k : ℕ, L ≤ g k := fun k => by
    have : 0 ≤ ((k : ℝ) + 1) * (z / 2) := by positivity
    simp only [g]; linarith
  have hexp : ∀ k : ℕ, Real.exp (-(g k + z / 2 - g k) ^ 2 / (8 * t))
      = Real.exp (-z ^ 2 / (32 * t)) := fun k => by
    congr 1
    rw [show g k + z / 2 - g k = z / 2 by ring]
    field_simp
    ring
  have hsub : {f : ℝ → ℝ | z < |clampTo L U (f (x + t)) - clampTo L U (f x)|}
      ⊆ ⋃ k ∈ Finset.range N, ({f : ℝ → ℝ | f x ≤ g k ∧ g k + z / 2 < f (x + t)}
        ∪ {f : ℝ → ℝ | g k + z / 2 < f x ∧ f (x + t) ≤ g k}) := by
    intro f hf
    simp only [mem_ofPred_eq] at hf
    simp only [mem_iUnion, Finset.mem_range, mem_union, mem_ofPred_eq]
    have hX := clampTo_mem hLU (f x)
    have hY := clampTo_mem hLU (f (x + t))
    rcases lt_abs.1 hf with h1 | h1
    · obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, (k : ℝ) * (z / 2) ≤ clampTo L U (f x) - L ∧
          clampTo L U (f x) - L < ((k : ℝ) + 1) * (z / 2) := by
        refine ⟨⌊(clampTo L U (f x) - L) / (z / 2)⌋₊, ?_, ?_⟩
        · rw [← le_div_iff₀ hδ0]
          exact Nat.floor_le (div_nonneg (by linarith [hX.1]) hδ0.le)
        · rw [← div_lt_iff₀ hδ0]
          exact Nat.lt_floor_add_one _
      have hgk : g k + z / 2 = L + (k : ℝ) * (z / 2) + z := by simp only [g]; ring
      have hXa : clampTo L U (f x) < g k := by simp only [g]; linarith
      have hYa : g k + z / 2 < clampTo L U (f (x + t)) := by rw [hgk]; linarith
      have hkN : k < N := by
        have hk' : (k : ℝ) < (U - L) / (z / 2) := by
          rw [lt_div_iff₀ hδ0]; linarith [hY.2]
        exact_mod_cast hk'.trans_le (Nat.le_ceil _)
      refine ⟨k, hkN, Or.inl ⟨le_of_clampTo_le ?_ hXa.le, lt_of_lt_clampTo ?_ hYa⟩⟩
      · linarith [hY.2]
      · linarith [hLg k]
    · obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, (k : ℝ) * (z / 2) ≤ clampTo L U (f (x + t)) - L ∧
          clampTo L U (f (x + t)) - L < ((k : ℝ) + 1) * (z / 2) := by
        refine ⟨⌊(clampTo L U (f (x + t)) - L) / (z / 2)⌋₊, ?_, ?_⟩
        · rw [← le_div_iff₀ hδ0]
          exact Nat.floor_le (div_nonneg (by linarith [hY.1]) hδ0.le)
        · rw [← div_lt_iff₀ hδ0]
          exact Nat.lt_floor_add_one _
      have hgk : g k + z / 2 = L + (k : ℝ) * (z / 2) + z := by simp only [g]; ring
      have hYa : clampTo L U (f (x + t)) < g k := by simp only [g]; linarith
      have hXa : g k + z / 2 < clampTo L U (f x) := by rw [hgk]; linarith
      have hkN : k < N := by
        have hk' : (k : ℝ) < (U - L) / (z / 2) := by
          rw [lt_div_iff₀ hδ0]; linarith [hX.2]
        exact_mod_cast hk'.trans_le (Nat.le_ceil _)
      refine ⟨k, hkN, Or.inr ⟨lt_of_lt_clampTo ?_ hXa, le_of_clampTo_le ?_ hYa.le⟩⟩
      · linarith [hLg k]
      · linarith [hX.2]
  have hE := (Real.exp_pos (-z ^ 2 / (32 * t))).le
  calc airy1Law h {f : ℝ → ℝ | z < |clampTo L U (f (x + t)) - clampTo L U (f x)|}
      ≤ airy1Law h (⋃ k ∈ Finset.range N, ({f : ℝ → ℝ | f x ≤ g k ∧ g k + z / 2 < f (x + t)}
        ∪ {f : ℝ → ℝ | g k + z / 2 < f x ∧ f (x + t) ≤ g k})) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range N, airy1Law h ({f : ℝ → ℝ | f x ≤ g k ∧ g k + z / 2 < f (x + t)}
        ∪ {f : ℝ → ℝ | g k + z / 2 < f x ∧ f (x + t) ≤ g k}) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, ENNReal.ofReal ((C + C') * Real.exp (-z ^ 2 / (32 * t))) := by
        refine Finset.sum_le_sum fun k _ => (measure_union_le _ _).trans ?_
        have e1 := airy1Law_fwd_le_on h hF (x := x) ht htδ (hLg k)
          (show g k ≤ g k + z / 2 by linarith)
        have e2 := airy1Law_rev_le_on h hR (x := x) ht htδ (hLg k)
          (show g k ≤ g k + z / 2 by linarith)
        rw [hexp k] at e1 e2
        refine (add_le_add e1 e2).trans (le_of_eq ?_)
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]
    _ = ENNReal.ofReal ((N : ℝ) * ((C + C') * Real.exp (-z ^ 2 / (32 * t)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((C + C') * (2 * (U - L) / z + 1) * Real.exp (-z ^ 2 / (32 * t))) := by
        apply ENNReal.ofReal_le_ofReal
        have hN : (N : ℝ) ≤ 2 * (U - L) / z + 1 := by
          have h1 := Nat.ceil_lt_add_one (div_nonneg (by linarith : 0 ≤ U - L) hδ0.le)
          have h2 : (U - L) / (z / 2) = 2 * (U - L) / z := by field_simp
          refine h1.le.trans (le_of_eq ?_)
          rw [h2]
        have hCE : 0 ≤ (C + C') * Real.exp (-z ^ 2 / (32 * t)) := by positivity
        calc (N : ℝ) * ((C + C') * Real.exp (-z ^ 2 / (32 * t)))
            ≤ (2 * (U - L) / z + 1) * ((C + C') * Real.exp (-z ^ 2 / (32 * t))) :=
              mul_le_mul_of_nonneg_right hN hCE
          _ = _ := by ring

/-- **Truncated-moment bound for gaps `0 < t ≤ δ ≤ 1`** (`lintegral_clamp_incr_rpow_le`
with gap-restricted defect hypotheses; same constant `K(C + C', U − L, p)`). -/
theorem lintegral_clamp_incr_rpow_le_on (h : Airy1FddPositive) {L U δ C C' p : ℝ}
    (hLU : L ≤ U) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn L δ C)
    (hR : AiryFdd.RevDefectBoundOn L δ C') (hδ1 : δ ≤ 1) (hp : 1 < p) {x t : ℝ} (ht : 0 < t)
    (htδ : t ≤ δ) :
    ∫⁻ f, ENNReal.ofReal (|clampTo L U (f (x + t)) - clampTo L U (f x)| ^ p) ∂airy1Law h
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p * t ^ ((p - 1) / 2)) := by
  have ht1 : t ≤ 1 := htδ.trans hδ1
  have hb0 : 0 < 1 / (32 * t) := by positivity
  have hC2 : 0 ≤ C + C' := by linarith
  have hD : 0 ≤ U - L := by linarith
  have hFm : Measurable fun f : ℝ → ℝ => |clampTo L U (f (x + t)) - clampTo L U (f x)| :=
    continuous_abs.measurable.comp (((measurable_clampTo L U).comp (measurable_pi_apply _)).sub
      ((measurable_clampTo L U).comp (measurable_pi_apply _)))
  have hi1 : IntegrableOn (fun z : ℝ => z ^ (p - 2) * Real.exp (-(1 / (32 * t)) * z ^ (2 : ℝ)))
      (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) two_pos hb0
  have hi2 : IntegrableOn (fun z : ℝ => z ^ (p - 1) * Real.exp (-(1 / (32 * t)) * z ^ (2 : ℝ)))
      (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) two_pos hb0
  let G : ℝ → ℝ := fun z => (C + C') * (2 * (U - L) *
    (z ^ (p - 2) * Real.exp (-(1 / (32 * t)) * z ^ (2 : ℝ)))
      + z ^ (p - 1) * Real.exp (-(1 / (32 * t)) * z ^ (2 : ℝ)))
  have hGi : IntegrableOn G (Ioi 0) := ((hi1.const_mul _).add hi2).const_mul _
  have hGnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz : 0 < z := hz
    simp only [G, Pi.zero_apply]
    have := Real.rpow_pos_of_pos hz (p - 2)
    have := Real.rpow_pos_of_pos hz (p - 1)
    positivity
  have hpt : ∀ z ∈ Ioi (0 : ℝ),
      airy1Law h {f : ℝ → ℝ | z < |clampTo L U (f (x + t)) - clampTo L U (f x)|}
        * ENNReal.ofReal (z ^ (p - 1)) ≤ ENNReal.ofReal (G z) := by
    intro z hz
    have hz : 0 < z := hz
    refine le_trans (mul_le_mul_of_nonneg_right
      (airy1Law_clamp_gap_le_on h hLU hC hC' hF hR ht htδ hz) (by positivity)) ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply le_of_eq
    congr 1
    have e1 : Real.exp (-z ^ 2 / (32 * t)) = Real.exp (-(1 / (32 * t)) * z ^ (2 : ℝ)) := by
      rw [Real.rpow_two]; congr 1; ring
    have e2 : z ^ (p - 1) = z ^ (p - 2) * z := by
      rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one hz.ne']
    simp only [G]
    rw [e1, e2]
    field_simp
  have hI1 := integral_rpow_mul_exp_neg_mul_rpow (q := p - 2) two_pos (by linarith) hb0
  have hI2 := integral_rpow_mul_exp_neg_mul_rpow (q := p - 1) two_pos (by linarith) hb0
  have hintG : ∫ z in Ioi (0 : ℝ), G z = (C + C') * (2 * (U - L) *
      ((1 / (32 * t)) ^ (-(p - 2 + 1) / 2) * (1 / 2) * Real.Gamma ((p - 2 + 1) / 2))
        + (1 / (32 * t)) ^ (-(p - 1 + 1) / 2) * (1 / 2) * Real.Gamma ((p - 1 + 1) / 2)) := by
    simp only [G]
    rw [integral_const_mul, integral_add (hi1.const_mul _) hi2, integral_const_mul, hI1, hI2]
  calc ∫⁻ f, ENNReal.ofReal (|clampTo L U (f (x + t)) - clampTo L U (f x)| ^ p) ∂airy1Law h
      = ENNReal.ofReal p * ∫⁻ z in Ioi 0,
          airy1Law h {f : ℝ → ℝ | z < |clampTo L U (f (x + t)) - clampTo L U (f x)|}
            * ENNReal.ofReal (z ^ (p - 1)) :=
        lintegral_rpow_eq_lintegral_meas_lt_mul (airy1Law h)
          (f := fun f : ℝ → ℝ => |clampTo L U (f (x + t)) - clampTo L U (f x)|)
          (ae_of_all _ fun f => abs_nonneg _) hFm.aemeasurable (by linarith)
    _ ≤ ENNReal.ofReal p * ∫⁻ z in Ioi 0, ENNReal.ofReal (G z) :=
        mul_le_mul_of_nonneg_left (setLIntegral_mono' measurableSet_Ioi hpt) (by positivity)
    _ = ENNReal.ofReal (p * ∫ z in Ioi (0 : ℝ), G z) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hGi hGnn, ← ENNReal.ofReal_mul (by linarith)]
    _ ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p * t ^ ((p - 1) / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hintG, show -(p - 2 + 1) / 2 = -((p - 1) / 2) by ring,
          show -(p - 1 + 1) / 2 = -(p / 2) by ring, show (p - 2 + 1) / 2 = (p - 1) / 2 by ring,
          show (p - 1 + 1) / 2 = p / 2 by ring, one_div_rpow_neg ht, one_div_rpow_neg ht]
        have hG1 := (Real.Gamma_pos_of_pos (show 0 < (p - 1) / 2 by linarith)).le
        have hG2 := (Real.Gamma_pos_of_pos (show 0 < p / 2 by linarith)).le
        have ht12 : t ^ (p / 2) ≤ t ^ ((p - 1) / 2) :=
          Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
        have hB : 0 ≤ p * (C + C') * ((32 : ℝ) ^ (p / 2) * Real.Gamma (p / 2) / 2) := by
          have : 0 ≤ p := by linarith
          positivity
        have key := mul_le_mul_of_nonneg_left ht12 hB
        unfold truncMomentConst
        have e : p * ((C + C') * (2 * (U - L) * ((32 : ℝ) ^ ((p - 1) / 2) * t ^ ((p - 1) / 2)
              * (1 / 2) * Real.Gamma ((p - 1) / 2)) + (32 : ℝ) ^ (p / 2) * t ^ (p / 2) * (1 / 2)
              * Real.Gamma (p / 2)))
            = p * (C + C') * ((U - L) * (32 : ℝ) ^ ((p - 1) / 2) * Real.Gamma ((p - 1) / 2))
                * t ^ ((p - 1) / 2)
              + p * (C + C') * ((32 : ℝ) ^ (p / 2) * Real.Gamma (p / 2) / 2) * t ^ (p / 2) := by
          ring
        rw [e]
        have e' : p * (C + C') * ((U - L) * (32 : ℝ) ^ ((p - 1) / 2) * Real.Gamma ((p - 1) / 2)
              + (32 : ℝ) ^ (p / 2) * Real.Gamma (p / 2) / 2) * t ^ ((p - 1) / 2)
            = p * (C + C') * ((U - L) * (32 : ℝ) ^ ((p - 1) / 2) * Real.Gamma ((p - 1) / 2))
                * t ^ ((p - 1) / 2)
              + p * (C + C') * ((32 : ℝ) ^ (p / 2) * Real.Gamma (p / 2) / 2)
                * t ^ ((p - 1) / 2) := by
          ring
        rw [e']
        exact add_le_add (le_refl _) key

/-- Kolmogorov condition for gaps `0 < u − s ≤ δ ≤ 1`. -/
theorem lintegral_edist_clamp_le_on_of_lt (h : Airy1FddPositive) {L U δ C C' p : ℝ}
    (hLU : L ≤ U) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn L δ C)
    (hR : AiryFdd.RevDefectBoundOn L δ C') (hδ1 : δ ≤ 1) (hp : 1 < p) {s u : ℝ} (hsu : s < u)
    (hsuδ : u - s ≤ δ) :
    ∫⁻ f, edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p ∂airy1Law h
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p) * edist s u ^ ((p - 1) / 2) := by
  have H := lintegral_clamp_incr_rpow_le_on h hLU hC hC' hF hR hδ1 hp (x := s) (t := u - s)
    (by linarith) hsuδ
  rw [show s + (u - s) = u by ring] at H
  have hK := truncMomentConst_nonneg (add_nonneg hC hC') (by linarith : 0 ≤ U - L) hp
  have hlhs : (fun f : ℝ → ℝ => edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p)
      = fun f => ENNReal.ofReal (|clampTo L U (f u) - clampTo L U (f s)| ^ p) := by
    funext f
    rw [edist_dist, Real.dist_eq, abs_sub_comm,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by linarith)]
  rw [hlhs]
  refine H.trans (le_of_eq ?_)
  rw [edist_dist, Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith),
    ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith), ENNReal.ofReal_mul hK]

/-- **Kolmogorov condition for gaps `|s − u| ≤ δ ≤ 1`**, constant `K(C + C', U − L, p)`. -/
theorem lintegral_edist_clamp_le_on (h : Airy1FddPositive) {L U δ C C' p : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn L δ C)
    (hR : AiryFdd.RevDefectBoundOn L δ C')
    (hδ1 : δ ≤ 1) (hp : 1 < p) {s u : ℝ} (hsuδ : dist s u ≤ δ) :
    ∫⁻ f, edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p ∂airy1Law h
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p) * edist s u ^ ((p - 1) / 2) := by
  rw [Real.dist_eq] at hsuδ
  rcases lt_trichotomy s u with hsu | rfl | hsu
  · exact lintegral_edist_clamp_le_on_of_lt h hLU hC hC' hF hR hδ1 hp hsu
      (by rw [abs_sub_comm, abs_of_pos (by linarith)] at hsuδ; exact hsuδ)
  · simp [ENNReal.zero_rpow_of_pos (show 0 < p by linarith)]
  · have H := lintegral_edist_clamp_le_on_of_lt h hLU hC hC' hF hR hδ1 hp hsu
      (by rw [abs_of_pos (by linarith)] at hsuδ; exact hsuδ)
    have e : (fun f : ℝ → ℝ => edist (clampTo L U (f s)) (clampTo L U (f u)) ^ p)
        = fun f => edist (clampTo L U (f u)) (clampTo L U (f s)) ^ p := by
      funext f; rw [edist_comm]
    rw [e, edist_comm s u]
    exact H

/-! ## The time-rescaled window process -/

/-- The clamped coordinate process on the window `[a, a + ℓ]`, run at speed `ℓ` and frozen after
time `1`: `s ↦ clamp_{[L,U]}(f (a + ℓ min s 1))`. -/
noncomputable def windowProcS (L U a ℓ : ℝ) (s : ℝ≥0) (f : ℝ → ℝ) : ℝ :=
  clampTo L U (f (a + ℓ * min (s : ℝ) 1))

/-- For a window length `0 ≤ ℓ ≤ δ`, the rescaled window process is a Kolmogorov process on
`ℝ≥0` with constant `K(C + C', U − L, p) ℓ^{(p−1)/2}`. -/
theorem isKolmogorovProcess_windowProcS (h : Airy1FddPositive) {L U δ C C' p ℓ : ℝ}
    (hLU : L ≤ U) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn L δ C)
    (hR : AiryFdd.RevDefectBoundOn L δ C') (hδ1 : δ ≤ 1) (hp : 1 < p) (hℓ : 0 ≤ ℓ) (hℓδ : ℓ ≤ δ)
    (a : ℝ) :
    IsKolmogorovProcess (windowProcS L U a ℓ) (airy1Law h) p ((p - 1) / 2)
      (truncMomentConst (C + C') (U - L) p * ℓ ^ ((p - 1) / 2)).toNNReal := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun s => (measurable_clampTo L U).comp (measurable_pi_apply _)) (fun s u => ?_)
    (by linarith) (by linarith)
  have hs0 : (0 : ℝ) ≤ min (s : ℝ) 1 := le_min s.2 zero_le_one
  have hu0 : (0 : ℝ) ≤ min (u : ℝ) 1 := le_min u.2 zero_le_one
  have hs1 : min (s : ℝ) 1 ≤ 1 := min_le_right _ _
  have hu1 : min (u : ℝ) 1 ≤ 1 := min_le_right _ _
  have hm1 : |min (s : ℝ) 1 - min (u : ℝ) 1| ≤ 1 := by
    rw [abs_sub_le_iff]; constructor <;> linarith
  have hm : |min (s : ℝ) 1 - min (u : ℝ) 1| ≤ |(s : ℝ) - u| :=
    (abs_min_sub_min_le_max _ _ _ _).trans (by simp)
  have hdist : dist (a + ℓ * min (s : ℝ) 1) (a + ℓ * min (u : ℝ) 1)
      = ℓ * |min (s : ℝ) 1 - min (u : ℝ) 1| := by
    rw [Real.dist_eq, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hℓ]
  have hd : dist (a + ℓ * min (s : ℝ) 1) (a + ℓ * min (u : ℝ) 1) ≤ δ := by
    rw [hdist]
    calc ℓ * |min (s : ℝ) 1 - min (u : ℝ) 1| ≤ ℓ * 1 := mul_le_mul_of_nonneg_left hm1 hℓ
      _ ≤ δ := by linarith
  have H := lintegral_edist_clamp_le_on h hLU hC hC' hF hR hδ1 hp hd
  have hq0 : 0 ≤ (p - 1) / 2 := by linarith
  have hK := truncMomentConst_nonneg (add_nonneg hC hC') (by linarith : 0 ≤ U - L) hp
  have hed : edist (a + ℓ * min (s : ℝ) 1) (a + ℓ * min (u : ℝ) 1)
      ≤ ENNReal.ofReal ℓ * edist s u := by
    rw [edist_dist, hdist, edist_dist, NNReal.dist_eq, ← ENNReal.ofReal_mul hℓ]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hm hℓ)
  change ∫⁻ ω, edist (clampTo L U (ω (a + ℓ * min (s : ℝ) 1)))
      (clampTo L U (ω (a + ℓ * min (u : ℝ) 1))) ^ p ∂airy1Law h
    ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p * ℓ ^ ((p - 1) / 2))
      * edist s u ^ ((p - 1) / 2)
  refine H.trans ?_
  calc ENNReal.ofReal (truncMomentConst (C + C') (U - L) p)
        * edist (a + ℓ * min (s : ℝ) 1) (a + ℓ * min (u : ℝ) 1) ^ ((p - 1) / 2)
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p)
        * (ENNReal.ofReal ℓ * edist s u) ^ ((p - 1) / 2) :=
        mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hed hq0) zero_le
    _ = ENNReal.ofReal (truncMomentConst (C + C') (U - L) p * ℓ ^ ((p - 1) / 2))
        * edist s u ^ ((p - 1) / 2) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0, ENNReal.ofReal_rpow_of_nonneg hℓ hq0, ← mul_assoc,
          ← ENNReal.ofReal_mul hK]

/-- **Lower window tail via quantitative KC.** For `M > 0`, a window length `0 ≤ ℓ ≤ δ ≤ 1` and
defect constants at the lower level `−2M` for gaps `≤ δ`:
`P(f a > −M, ∃ rational s ∈ [0,1), f (a + ℓ s) < −2M) ≤ K(C + C', 2M, 4) ℓ^{3/2} L_KC / M⁴`,
`L_KC = constL 3 1 4 (3/2) (1/16)`. -/
theorem window_low_tail_le (h : Airy1FddPositive) {M δ ℓ C C' : ℝ} (hM : 0 < M) (hC : 0 ≤ C)
    (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn (-(2 * M)) δ C)
    (hR : AiryFdd.RevDefectBoundOn (-(2 * M)) δ C')
    (hδ1 : δ ≤ 1) (hℓ : 0 ≤ ℓ) (hℓδ : ℓ ≤ δ) (a : ℝ) :
    airy1Law h {f : ℝ → ℝ | -M < f a ∧ ∃ s ∈ winPts, f (a + ℓ * s) < -(2 * M)}
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (2 * M) 4 * ℓ ^ (3 / 2 : ℝ)
          * (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal / M ^ (4 : ℝ)) := by
  have hLU : -(2 * M) ≤ 0 := by linarith
  set X := windowProcS (-(2 * M)) 0 a ℓ with hXdef
  have hX0 := isKolmogorovProcess_windowProcS h hLU hC hC' hF hR hδ1 (p := 4) (by norm_num)
    hℓ hℓδ a
  have e : ((4 : ℝ) - 1) / 2 = 3 / 2 := by norm_num
  have e2 : (0 : ℝ) - -(2 * M) = 2 * M := by ring
  rw [e, e2] at hX0
  have hX : IsKolmogorovProcess X (airy1Law h) 4 (3 / 2)
      (truncMomentConst (C + C') (2 * M) 4 * ℓ ^ (3 / 2 : ℝ)).toNNReal := hX0
  have : Countable winPts := winPts_countable.to_subtype
  have hKC := countable_kolmogorov_chentsov hasCoveringExponent_Ico_zero_one
    hX.IsAEKolmogorovProcess (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2)
    (β := 1 / 16) (by norm_num) winPts (fun s hs => ⟨zero_le, hs.1⟩)
  set Φ : (ℝ → ℝ) → ℝ≥0∞ := fun f => ⨆ (s : winPts) (t : winPts),
    edist (X s f) (X t f) ^ (4 : ℝ) / edist s t ^ (((1 / 16 : ℝ≥0) : ℝ) * 4) with hΦ
  have hΦm : AEMeasurable Φ (airy1Law h) := by
    refine AEMeasurable.iSup (fun s => AEMeasurable.iSup (fun t => ?_))
    exact AEMeasurable.div (hX.measurable_edist.aemeasurable.pow_const _) aemeasurable_const
  have hε0 : ENNReal.ofReal (M ^ (4 : ℝ)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hsub : {f : ℝ → ℝ | -M < f a ∧ ∃ s ∈ winPts, f (a + ℓ * s) < -(2 * M)}
      ⊆ {f | ENNReal.ofReal (M ^ (4 : ℝ)) ≤ Φ f} := by
    rintro f ⟨hfa, s, hs, hfs⟩
    simp only [mem_ofPred_eq]
    have hs1 : (s : ℝ) < 1 := by exact_mod_cast hs.1
    have hXs : X s f = -(2 * M) := by
      simp only [hXdef, windowProcS, min_eq_left hs1.le, clampTo]
      rw [min_eq_right (by linarith), max_eq_left hfs.le]
    have hX0' : -M < X 0 f := by
      simp only [hXdef, windowProcS, NNReal.coe_zero, min_eq_left zero_le_one, mul_zero,
        add_zero, clampTo]
      exact (lt_min (by linarith) hfa).trans_le (le_max_right _ _)
    have h0 : (0 : ℝ≥0) ∈ winPts := ⟨one_pos, zero_mem_ratNN⟩
    have hed : ENNReal.ofReal M ≤ edist (X s f) (X 0 f) := by
      rw [edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal
        ((by linarith : M ≤ -(X s f - X 0 f)).trans (neg_le_abs _))
    have hst : edist s (0 : ℝ≥0) ^ (((1 / 16 : ℝ≥0) : ℝ) * 4) ≤ 1 := by
      refine ENNReal.rpow_le_one ?_ (by positivity)
      rw [edist_dist, NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg s)]
      exact ENNReal.ofReal_le_one.2 hs1.le
    calc ENNReal.ofReal (M ^ (4 : ℝ))
        = ENNReal.ofReal M ^ (4 : ℝ) :=
          (ENNReal.ofReal_rpow_of_nonneg hM.le (by norm_num)).symm
      _ ≤ edist (X s f) (X 0 f) ^ (4 : ℝ) := ENNReal.rpow_le_rpow hed (by norm_num)
      _ = edist (X s f) (X 0 f) ^ (4 : ℝ) / 1 := (div_one _).symm
      _ ≤ edist (X s f) (X 0 f) ^ (4 : ℝ) / edist s (0 : ℝ≥0) ^ (((1 / 16 : ℝ≥0) : ℝ) * 4) :=
          ENNReal.div_le_div_left hst _
      _ ≤ Φ f := by
          simp only [hΦ]
          exact le_iSup₂_of_le (f := fun (s t : winPts) =>
            edist (X s f) (X t f) ^ (4 : ℝ) / edist (s : ℝ≥0) (t : ℝ≥0) ^ (((1 / 16 : ℝ≥0) : ℝ) * 4))
            ⟨s, hs⟩ ⟨0, h0⟩ le_rfl
  have hL : constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ) ≠ ∞ :=
    (constL_lt_top (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by push_cast; norm_num)).ne
  have hM4 : 0 ≤ truncMomentConst (C + C') (2 * M) 4 * ℓ ^ (3 / 2 : ℝ) :=
    mul_nonneg (truncMomentConst_nonneg (add_nonneg hC hC') (by linarith)
      (by norm_num : (1 : ℝ) < 4)) (Real.rpow_nonneg hℓ _)
  calc airy1Law h {f : ℝ → ℝ | -M < f a ∧ ∃ s ∈ winPts, f (a + ℓ * s) < -(2 * M)}
      ≤ airy1Law h {f | ENNReal.ofReal (M ^ (4 : ℝ)) ≤ Φ f} := measure_mono hsub
    _ ≤ (∫⁻ f, Φ f ∂airy1Law h) / ENNReal.ofReal (M ^ (4 : ℝ)) :=
        meas_ge_le_lintegral_div hΦm hε0 ENNReal.ofReal_ne_top
    _ ≤ ((truncMomentConst (C + C') (2 * M) 4 * ℓ ^ (3 / 2 : ℝ)).toNNReal
          * constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)) / ENNReal.ofReal (M ^ (4 : ℝ)) :=
        ENNReal.div_le_div_right hKC _
    _ = ENNReal.ofReal (truncMomentConst (C + C') (2 * M) 4 * ℓ ^ (3 / 2 : ℝ)
          * (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal / M ^ (4 : ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul hM4,
          ENNReal.ofReal_toReal hL]
        rfl

/-! ## Lower boundedness on rational times -/

/-- The event that the coordinate path is unbounded below on the rational times of `[0, N]`. -/
def lowEvent (N : ℕ) : Set (ℝ → ℝ) :=
  {f | ∀ B : ℕ, ∃ q : ℚ, Real.toNNReal q ≤ N ∧ f (Real.toNNReal q) < -(B : ℝ)}

/-- One-point lower tail: `P(f x ≤ c) = F_{0}(c)`. -/
theorem airy1Law_le_eq_ofReal (h : Airy1FddPositive) (x c : ℝ) :
    airy1Law h {f : ℝ → ℝ | f x ≤ c} = ENNReal.ofReal (AiryFdd.airy1FinCdf {0} (fun _ => c)) := by
  have e1 : {f : ℝ → ℝ | f x ≤ c} = {f | ∀ t ∈ ({x} : Finset ℝ), f t ≤ (fun _ => c) t} := by
    ext f; simp
  have hF : (airy1Law h).real {f : ℝ → ℝ | ∀ t ∈ ({x} : Finset ℝ), f t ≤ (fun _ => c) t}
      = AiryFdd.airy1FinCdf {x} (fun _ => c) := airy1Law_fdd h {x} _
  rw [e1, ← ofReal_measureReal (measure_ne_top _ _), hF, airy1FinCdf_singleton_eq x 0 c]

theorem airy1FinCdf_singleton_nonneg (h : Airy1FddPositive) (c : ℝ) :
    0 ≤ AiryFdd.airy1FinCdf {0} (fun _ => c) := by
  have hF : (airy1Law h).real {f : ℝ → ℝ | ∀ t ∈ ({0} : Finset ℝ), f t ≤ (fun _ => c) t}
      = AiryFdd.airy1FinCdf {0} (fun _ => c) := airy1Law_fdd h {0} _
  rw [← hF]
  exact measureReal_nonneg

/-- **Per-level bound** for the lower unbounded event: windows of length `1/n ≤ δ`, clamp
`[−2M, 0]`; `(nN + 1)` windows, each contributing the one-point lower tail at `−M` plus the KC
window tail. -/
theorem measure_lowEvent_le (h : Airy1FddPositive) {M δ C C' : ℝ} (hM : 0 < M) (hC : 0 ≤ C)
    (hC' : 0 ≤ C') (hF : AiryFdd.FwdDefectBoundOn (-(2 * M)) δ C)
    (hR : AiryFdd.RevDefectBoundOn (-(2 * M)) δ C')
    (hδ1 : δ ≤ 1) (N n : ℕ) (hn : 0 < n) (hnδ : 1 / (n : ℝ) ≤ δ) :
    airy1Law h (lowEvent N)
      ≤ ENNReal.ofReal (((n : ℝ) * N + 1) * (AiryFdd.airy1FinCdf {0} (fun _ => -M)
          + truncMomentConst (C + C') (2 * M) 4 * (1 / (n : ℝ)) ^ (3 / 2 : ℝ)
            * (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal / M ^ (4 : ℝ))) := by
  set A : ℝ := AiryFdd.airy1FinCdf {0} (fun _ => -M) with hA
  set ℓ : ℝ := 1 / (n : ℝ) with hℓdef
  set T : ℝ := truncMomentConst (C + C') (2 * M) 4 * ℓ ^ (3 / 2 : ℝ)
    * (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal / M ^ (4 : ℝ) with hT
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓ0 : 0 ≤ ℓ := by rw [hℓdef]; positivity
  have hA0 : 0 ≤ A := airy1FinCdf_singleton_nonneg h _
  have hT0 : 0 ≤ T := by
    have := truncMomentConst_nonneg (add_nonneg hC hC') (by linarith : 0 ≤ 2 * M)
      (by norm_num : (1 : ℝ) < 4)
    have := Real.rpow_nonneg hℓ0 (3 / 2 : ℝ)
    rw [hT]
    positivity
  have hsub : lowEvent N ⊆ ⋃ j ∈ Finset.range (n * N + 1),
      ({f : ℝ → ℝ | f ((j : ℝ) / n) ≤ -M}
        ∪ {f | -M < f ((j : ℝ) / n) ∧ ∃ s ∈ winPts, f ((j : ℝ) / n + ℓ * s) < -(2 * M)}) := by
    intro f hf
    obtain ⟨q, hqN, hqf⟩ := hf ⌈2 * M⌉₊
    have hMf : f (Real.toNNReal q) < -(2 * M) := by
      have := Nat.le_ceil (2 * M); linarith
    set x : ℝ := (Real.toNNReal q : ℝ) with hx
    have hx0 : 0 ≤ x := (Real.toNNReal q).2
    have hxN : x ≤ N := by rw [hx]; exact_mod_cast hqN
    set j : ℕ := ⌊(n : ℝ) * x⌋₊ with hj
    have hnx0 : 0 ≤ (n : ℝ) * x := by positivity
    have hjx : (j : ℝ) ≤ n * x := Nat.floor_le hnx0
    have hxj : (n : ℝ) * x < j + 1 := Nat.lt_floor_add_one _
    have hjN : j ∈ Finset.range (n * N + 1) := by
      rw [Finset.mem_range]
      have : (n : ℝ) * x < ((n * N + 1 : ℕ) : ℝ) := by
        push_cast
        nlinarith
      exact (Nat.floor_lt hnx0).2 this
    simp only [mem_iUnion, mem_union, mem_ofPred_eq]
    refine ⟨j, hjN, ?_⟩
    by_cases hfj : f ((j : ℝ) / n) ≤ -M
    · left; exact hfj
    · right
      refine ⟨lt_of_not_ge hfj, Real.toNNReal ((n : ℝ) * x - j), ⟨?_, ?_⟩, ?_⟩
      · rw [← NNReal.coe_lt_coe, NNReal.coe_one, Real.coe_toNNReal _ (by linarith)]
        linarith
      · refine ⟨(n : ℚ) * max q 0 - j, ?_⟩
        rw [hx, Real.coe_toNNReal']
        push_cast
        rfl
      · rw [Real.coe_toNNReal _ (by linarith)]
        have e : (j : ℝ) / n + ℓ * ((n : ℝ) * x - j) = x := by
          rw [hℓdef]; field_simp; ring
        rw [e]
        exact hMf
  calc airy1Law h (lowEvent N)
      ≤ airy1Law h (⋃ j ∈ Finset.range (n * N + 1),
          ({f : ℝ → ℝ | f ((j : ℝ) / n) ≤ -M}
            ∪ {f | -M < f ((j : ℝ) / n) ∧ ∃ s ∈ winPts, f ((j : ℝ) / n + ℓ * s) < -(2 * M)})) :=
        measure_mono hsub
    _ ≤ ∑ j ∈ Finset.range (n * N + 1), airy1Law h
          ({f : ℝ → ℝ | f ((j : ℝ) / n) ≤ -M}
            ∪ {f | -M < f ((j : ℝ) / n) ∧ ∃ s ∈ winPts, f ((j : ℝ) / n + ℓ * s) < -(2 * M)}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (n * N + 1), ENNReal.ofReal (A + T) := by
        refine Finset.sum_le_sum fun j _ => (measure_union_le _ _).trans ?_
        rw [airy1Law_le_eq_ofReal h ((j : ℝ) / n) (-M), ENNReal.ofReal_add hA0 hT0]
        exact add_le_add le_rfl
          (window_low_tail_le h hM hC hC' hF hR hδ1 hℓ0 (by rw [hℓdef]; exact hnδ) _)
    _ = ENNReal.ofReal (((n : ℝ) * N + 1) * (A + T)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← ENNReal.ofReal_natCast]
        push_cast
        rfl

/-! ## Asymptotics -/

/-- `exp(K M^α + a M − b M³) → 0` as `M → ∞`, for `α < 3` and `b > 0`. -/
theorem tendsto_exp_cubic (K a α b : ℝ) (hα : α < 3) (hb : 0 < b) :
    Tendsto (fun M : ℝ => Real.exp (K * M ^ α + a * M - b * M ^ 3)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun M : ℝ => K * M ^ (-(3 - α)) + a * M ^ (-(2 : ℝ)) - b) atTop
      (𝓝 (K * 0 + a * 0 - b)) :=
    (((tendsto_rpow_neg_atTop (by linarith)).const_mul K).add
      ((tendsto_rpow_neg_atTop (by norm_num)).const_mul a)).sub_const b
  rw [mul_zero, mul_zero, zero_add, zero_sub] at h1
  have h2 : Tendsto (fun M : ℝ => M ^ 3 * (K * M ^ (-(3 - α)) + a * M ^ (-(2 : ℝ)) - b))
      atTop atBot :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).atTop_mul_neg (by linarith) h1
  refine Real.tendsto_exp_atBot.comp (h2.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with M hM
  have e3 : M ^ 3 = M ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have ea : M ^ (3 : ℝ) * M ^ (-(3 - α)) = M ^ α := by
    rw [← Real.rpow_add hM]; congr 1; ring
  have eb : M ^ (3 : ℝ) * M ^ (-(2 : ℝ)) = M := by
    rw [← Real.rpow_add hM]; norm_num
  rw [e3, mul_sub, mul_add, mul_left_comm _ K, mul_left_comm _ a, ea, eb]
  ring

/-- The `p = 4` truncated-moment coefficients `A`, `B`: `K(C, D, 4) = 4 C (D A + B)`. -/
noncomputable def kcA : ℝ := (32 : ℝ) ^ (((4 : ℝ) - 1) / 2) * Real.Gamma (((4 : ℝ) - 1) / 2)

/-- See `kcA`. -/
noncomputable def kcB : ℝ := (32 : ℝ) ^ ((4 : ℝ) / 2) * Real.Gamma ((4 : ℝ) / 2) / 2

theorem kcA_nonneg : 0 ≤ kcA := by
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < ((4 : ℝ) - 1) / 2 by norm_num)
  unfold kcA; positivity

theorem kcB_nonneg : 0 ≤ kcB := by
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < (4 : ℝ) / 2 by norm_num)
  unfold kcB; positivity

theorem truncMomentConst_four (C D : ℝ) : truncMomentConst C D 4 = 4 * C * (D * kcA + kcB) := by
  unfold truncMomentConst kcA kcB; ring

/-- The explicit bound for `P(lowEvent N)` at level `M`. -/
noncomputable def lowBound (N : ℕ) (C₀ c K α cL : ℝ) (M : ℝ) : ℝ :=
  ((N : ℝ) + 1) * (C₀ * (Real.exp (0 * M ^ α + 0 * M - c / 2 * M ^ 3)
      + 2 * Real.exp (0 * M ^ α + 1 * M - c * M ^ 3))
    + 8 * (2 * kcA + kcB) * cL * Real.exp (K * M ^ α + 1 * M - c / 4 * M ^ 3))

theorem tendsto_lowBound (N : ℕ) (C₀ c K α cL : ℝ) (hα : α < 3) (hc : 0 < c) :
    Tendsto (lowBound N C₀ c K α cL) atTop (𝓝 0) := by
  have h1 := tendsto_exp_cubic 0 0 α (c / 2) hα (by positivity)
  have h2 := tendsto_exp_cubic 0 1 α c hα hc
  have h3 := tendsto_exp_cubic K 1 α (c / 4) hα (by positivity)
  have := ((h1.add (h2.const_mul 2)).const_mul C₀).add (h3.const_mul (8 * (2 * kcA + kcB) * cL))
  have := this.const_mul ((N : ℝ) + 1)
  simp only [mul_zero, add_zero] at this
  exact this

/-- The real-number estimate behind the lower-boundedness argument. -/
theorem lowEvent_real_bound {N : ℕ} {C₀ c K α M E F cL nR : ℝ} (hC₀ : 0 < C₀) (hc : 0 < c)
    (hM : 2 ≤ M) (hE0 : 0 ≤ E) (hE : E ≤ Real.exp (K * M ^ α)) (hF0 : 0 ≤ F)
    (hF : F ≤ C₀ * Real.exp (-c * M ^ 3)) (hcL : 0 ≤ cL) (hn1 : Real.exp (c / 2 * M ^ 3) ≤ nR)
    (hn2 : nR ≤ Real.exp (c / 2 * M ^ 3) + 2 * M + 1) :
    (nR * N + 1) * (F + truncMomentConst (E + E) (2 * M) 4 * (1 / nR) ^ (3 / 2 : ℝ) * cL
        / M ^ (4 : ℝ)) ≤ lowBound N C₀ c K α cL M := by
  have hA := kcA_nonneg
  have hB := kcB_nonneg
  have hnR1 : 1 ≤ nR := (Real.one_le_exp (by positivity)).trans hn1
  have hnR0 : 0 < nR := by linarith
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  have heM : M + 1 ≤ Real.exp M := Real.add_one_le_exp M
  have hnN : nR * N + 1 ≤ nR * ((N : ℝ) + 1) := by nlinarith
  -- first term
  have hT1 : (nR * N + 1) * F ≤ ((N : ℝ) + 1) * (C₀ * (Real.exp (0 * M ^ α + 0 * M - c / 2 * M ^ 3)
      + 2 * Real.exp (0 * M ^ α + 1 * M - c * M ^ 3))) := by
    have e1 : Real.exp (0 * M ^ α + 0 * M - c / 2 * M ^ 3)
        = Real.exp (c / 2 * M ^ 3) * Real.exp (-c * M ^ 3) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (0 * M ^ α + 1 * M - c * M ^ 3) = Real.exp M * Real.exp (-c * M ^ 3) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e1, e2]
    have hx := (Real.exp_pos (-c * M ^ 3)).le
    have hn3 : nR ≤ Real.exp (c / 2 * M ^ 3) + 2 * Real.exp M := by linarith
    calc (nR * N + 1) * F ≤ nR * ((N : ℝ) + 1) * (C₀ * Real.exp (-c * M ^ 3)) :=
          mul_le_mul hnN hF hF0 (by positivity)
      _ ≤ (Real.exp (c / 2 * M ^ 3) + 2 * Real.exp M) * ((N : ℝ) + 1)
            * (C₀ * Real.exp (-c * M ^ 3)) := by gcongr
      _ = _ := by ring
  -- second term
  have hM4 : 1 ≤ M ^ (4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hhalf : nR * (1 / nR) ^ (3 / 2 : ℝ) ≤ Real.exp (-(c / 4 * M ^ 3)) := by
    have e : (1 / nR) ^ (3 / 2 : ℝ) = (1 / nR) ^ (1 / 2 : ℝ) * (1 / nR) := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add_one (by positivity)]
    rw [e, mul_left_comm, mul_one_div_cancel hnR0.ne', mul_one]
    have hle : 1 / nR ≤ Real.exp (-(c / 2 * M ^ 3)) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos _) hn1
    calc (1 / nR) ^ (1 / 2 : ℝ) ≤ Real.exp (-(c / 2 * M ^ 3)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = Real.exp (-(c / 4 * M ^ 3)) := by
          rw [← Real.exp_mul]; congr 1; ring
  have hlin : 2 * M * kcA + kcB ≤ (2 * kcA + kcB) * Real.exp M := by
    have h1 : 1 ≤ Real.exp M := Real.one_le_exp (by linarith)
    nlinarith
  have hT2 : (nR * N + 1) * (truncMomentConst (E + E) (2 * M) 4 * (1 / nR) ^ (3 / 2 : ℝ) * cL
        / M ^ (4 : ℝ))
      ≤ 8 * (2 * kcA + kcB) * cL * Real.exp (K * M ^ α + 1 * M - c / 4 * M ^ 3)
        * ((N : ℝ) + 1) := by
    rw [truncMomentConst_four]
    have hP : 0 ≤ 4 * (E + E) * (2 * M * kcA + kcB) * (1 / nR) ^ (3 / 2 : ℝ) * cL := by
      have := Real.rpow_nonneg (show 0 ≤ 1 / nR by positivity) (3 / 2 : ℝ)
      have : 0 ≤ 2 * M * kcA + kcB := by nlinarith
      positivity
    have e : Real.exp (K * M ^ α + 1 * M - c / 4 * M ^ 3)
        = Real.exp (K * M ^ α) * Real.exp M * Real.exp (-(c / 4 * M ^ 3)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [e]
    have hr := (Real.rpow_nonneg (show 0 ≤ 1 / nR by positivity) (3 / 2 : ℝ))
    calc (nR * N + 1) * (4 * (E + E) * (2 * M * kcA + kcB) * (1 / nR) ^ (3 / 2 : ℝ) * cL
          / M ^ (4 : ℝ))
        ≤ nR * ((N : ℝ) + 1) * (4 * (E + E) * (2 * M * kcA + kcB) * (1 / nR) ^ (3 / 2 : ℝ) * cL) :=
          mul_le_mul hnN (div_le_self hP hM4) (div_nonneg hP (by linarith)) (by positivity)
      _ = 8 * E * (2 * M * kcA + kcB) * cL * ((N : ℝ) + 1) * (nR * (1 / nR) ^ (3 / 2 : ℝ)) := by
          ring
      _ ≤ 8 * Real.exp (K * M ^ α) * ((2 * kcA + kcB) * Real.exp M) * cL * ((N : ℝ) + 1)
            * Real.exp (-(c / 4 * M ^ 3)) := by
          have : 0 ≤ 2 * M * kcA + kcB := by nlinarith
          gcongr
      _ = _ := by ring
  unfold lowBound
  rw [mul_add]
  calc (nR * N + 1) * F + (nR * N + 1) * (truncMomentConst (E + E) (2 * M) 4
        * (1 / nR) ^ (3 / 2 : ℝ) * cL / M ^ (4 : ℝ))
      ≤ ((N : ℝ) + 1) * (C₀ * (Real.exp (0 * M ^ α + 0 * M - c / 2 * M ^ 3)
          + 2 * Real.exp (0 * M ^ α + 1 * M - c * M ^ 3)))
        + 8 * (2 * kcA + kcB) * cL * Real.exp (K * M ^ α + 1 * M - c / 4 * M ^ 3)
          * ((N : ℝ) + 1) := add_le_add hT1 hT2
    _ = _ := by ring

/-- **Lower boundedness, hypothesis form.** Under a cubic left tail (H1) and gap-restricted
defect constants `CM M` with `log CM M ≤ K M^α`, `α < 3` (H2), for every `N`, almost surely the
coordinate path is bounded below on the rational times of `[0, N]`: `P(lowEvent N) = 0`. -/
theorem airy1Law_lowEvent_of (h : Airy1FddPositive)
    (hLT : ∃ C c, 0 < C ∧ 0 < c ∧ ∀ M ≥ 0,
      AiryFdd.airy1FinCdf {0} (fun _ => -M) ≤ C * Real.exp (-c * M ^ 3))
    {CM : ℝ → ℝ} {K α : ℝ} (hα : α < 3)
    (hDef : ∀ M ≥ (2 : ℝ), AiryFdd.FwdDefectBoundOn (-(2 * M)) (1 / (2 * M)) (CM M)
      ∧ AiryFdd.RevDefectBoundOn (-(2 * M)) (1 / (2 * M)) (CM M))
    (hCM : ∀ M ≥ (2 : ℝ), Real.log (CM M) ≤ K * M ^ α) (N : ℕ) :
    airy1Law h (lowEvent N) = 0 := by
  obtain ⟨C₀, c, hC₀, hc, hLT⟩ := hLT
  set cL := (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal
  have hcL : 0 ≤ cL := ENNReal.toReal_nonneg
  refine le_antisymm ?_ zero_le
  have := ge_of_tendsto (b := airy1Law h (lowEvent N))
    (ENNReal.tendsto_ofReal (tendsto_lowBound N C₀ c K α cL hα hc)) ?_
  · simpa using this
  filter_upwards [eventually_ge_atTop 2] with M hM
  have hM0 : 0 < M := by linarith
  set E := Real.exp (K * M ^ α) with hEdef
  have hCE : CM M ≤ E := (Real.le_exp_log _).trans (Real.exp_le_exp.2 (hCM M hM))
  have hF := (hDef M hM).1.mono le_rfl le_rfl hCE
  have hR := (hDef M hM).2.mono le_rfl le_rfl hCE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hδ1 : 1 / (2 * M) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  set n : ℕ := ⌈Real.exp (c / 2 * M ^ 3) + 2 * M⌉₊ with hndef
  have hx0 : 0 ≤ Real.exp (c / 2 * M ^ 3) + 2 * M := by positivity
  have hn1 : Real.exp (c / 2 * M ^ 3) + 2 * M ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < Real.exp (c / 2 * M ^ 3) + 2 * M + 1 := Nat.ceil_lt_add_one hx0
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := by
      have := Real.exp_pos (c / 2 * M ^ 3); linarith
    exact_mod_cast this
  have hnδ : 1 / (n : ℝ) ≤ 1 / (2 * M) :=
    one_div_le_one_div_of_le (by positivity) (by linarith [Real.exp_pos (c / 2 * M ^ 3)])
  refine (measure_lowEvent_le h hM0 hE0 hE0 hF hR hδ1 N n hnpos hnδ).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact lowEvent_real_bound hC₀ hc hM hE0 le_rfl (airy1FinCdf_singleton_nonneg h _)
    (hLT M hM0.le) hcL (by linarith [Real.exp_pos (c / 2 * M ^ 3)]) hn2.le

/-- Almost surely the coordinate path is bounded below on the rational times of every `[0, N]`
(conditional on any proof that the events `lowEvent N` are null). -/
theorem ae_bddBelow_rat_of (h : Airy1FddPositive) (hlow : ∀ N, airy1Law h (lowEvent N) = 0) :
    ∀ᵐ f ∂airy1Law h, ∀ N : ℕ, ∃ B : ℕ, ∀ q : ℚ, Real.toNNReal q ≤ N →
      -(B : ℝ) ≤ f (Real.toNNReal q) := by
  refine ae_all_iff.2 fun N => ?_
  refine ae_iff.2 (measure_mono_null (fun f hf => ?_) (hlow N))
  simp only [mem_ofPred_eq, not_exists] at hf
  intro B
  by_contra hcon
  exact hf B fun q hq => le_of_not_gt fun hlt => hcon ⟨q, hq, hlt⟩

/-! ## Gluing the lower clamps -/

/-- The full-measure event on which the lower-clamped versions glue: they agree with
`max (−m) f` at rational times, and the path is bounded below on the rational times of every
`[0, N]`. -/
def goodLowSet (h : Airy1FddPositive) : Set (ℝ → ℝ) :=
  {f | (∀ m : ℕ, ∀ q : ℚ, airy1ContL h (-(m : ℝ)) (Real.toNNReal q) f
      = max (-(m : ℝ)) (f (Real.toNNReal q)))
    ∧ ∀ N : ℕ, ∃ B : ℕ, ∀ q : ℚ, Real.toNNReal q ≤ N → -(B : ℝ) ≤ f (Real.toNNReal q)}

theorem measurableSet_goodLowSet (h : Airy1FddPositive) : MeasurableSet (goodLowSet h) := by
  have e : goodLowSet h = (⋂ m : ℕ, ⋂ q : ℚ, {f : ℝ → ℝ | airy1ContL h (-(m : ℝ))
      (Real.toNNReal q) f = max (-(m : ℝ)) (f (Real.toNNReal q))})
      ∩ ⋂ N : ℕ, ⋃ B : ℕ, ⋂ q : ℚ, {f : ℝ → ℝ | Real.toNNReal q ≤ N →
        -(B : ℝ) ≤ f (Real.toNNReal q)} := by
    ext f; simp [goodLowSet]
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.iInter fun m => MeasurableSet.iInter fun q => ?_)
    (MeasurableSet.iInter fun N => MeasurableSet.iUnion fun B => MeasurableSet.iInter fun q => ?_)
  · exact measurableSet_eq_fun (measurable_airy1ContL h _ _)
      (measurable_const.max (measurable_pi_apply _))
  · by_cases hq : Real.toNNReal q ≤ N
    · simp only [hq, true_imp_iff]
      exact measurableSet_le measurable_const (measurable_pi_apply _)
    · simp [hq]

theorem ae_mem_goodLowSet_of (h : Airy1FddPositive) (hlow : ∀ N, airy1Law h (lowEvent N) = 0) :
    ∀ᵐ f ∂airy1Law h, f ∈ goodLowSet h := by
  have h1 : ∀ᵐ f ∂airy1Law h, ∀ m : ℕ, ∀ q : ℚ, airy1ContL h (-(m : ℝ)) (Real.toNNReal q) f
      = max (-(m : ℝ)) (f (Real.toNNReal q)) :=
    ae_all_iff.2 fun m => ae_all_iff.2 fun q => airy1ContL_ae_eq h _ _
  filter_upwards [h1, ae_bddBelow_rat_of h hlow] with f hf1 hf2 using ⟨hf1, hf2⟩

section DeterministicLow

variable {h : Airy1FddPositive} {f : ℝ → ℝ}

/-- On `goodLowSet`: `Z_m = max(−m, Z_{m'})` for `m ≤ m'` (continuity + density). -/
theorem airy1ContL_eq_max (hf : f ∈ goodLowSet h) {m m' : ℕ} (hmm : m ≤ m') (t : ℝ≥0) :
    airy1ContL h (-(m : ℝ)) t f = max (-(m : ℝ)) (airy1ContL h (-(m' : ℝ)) t f) := by
  have hc := Continuous.ext_on dense_ratNN (continuous_airy1ContL h (-(m : ℝ)) f)
    ((continuous_const (y := -(m : ℝ))).max (continuous_airy1ContL h (-(m' : ℝ)) f)) ?_
  · exact congrFun hc t
  rintro _ ⟨q, rfl⟩
  simp only
  rw [hf.1 m q, hf.1 m' q, ← max_assoc, max_eq_left (neg_le_neg (by exact_mod_cast hmm))]

/-- On `goodLowSet`, `Z_m ≥ −B` on `[0, N)` whenever `−B` bounds the rational values on `[0,N]`
from below. -/
theorem airy1ContL_ge_of_bound (hf : f ∈ goodLowSet h) {N B : ℕ}
    (hB : ∀ q : ℚ, Real.toNNReal q ≤ N → -(B : ℝ) ≤ f (Real.toNNReal q)) (m : ℕ) {t : ℝ≥0}
    (ht : t < N) : -(B : ℝ) ≤ airy1ContL h (-(m : ℝ)) t f := by
  have hcl : IsClosed {s : ℝ≥0 | -(B : ℝ) ≤ airy1ContL h (-(m : ℝ)) s f} :=
    isClosed_le continuous_const (continuous_airy1ContL h _ f)
  have hsub : Iio (N : ℝ≥0) ∩ ratNN ⊆ {s : ℝ≥0 | -(B : ℝ) ≤ airy1ContL h (-(m : ℝ)) s f} := by
    rintro _ ⟨hs, q, rfl⟩
    simp only [mem_ofPred_eq]
    rw [hf.1 m q]
    exact (hB q (le_of_lt hs)).trans (le_max_right _ _)
  exact closure_minimal hsub hcl (dense_ratNN.open_subset_closure_inter isOpen_Iio ht)

/-- **Stabilization.** On `goodLowSet`, for each `N` there is `m₀` with `Z_m = Z_{m₀}` on
`[0, N)` for every `m ≥ m₀`, and `Z_{m₀} ≤ Z_m` there for all `m`. -/
theorem exists_airy1ContL_stable (hf : f ∈ goodLowSet h) (N : ℕ) :
    ∃ m₀ : ℕ, ∀ t : ℝ≥0, t < N → ∀ m : ℕ,
      airy1ContL h (-(m₀ : ℝ)) t f ≤ airy1ContL h (-(m : ℝ)) t f
      ∧ (m₀ ≤ m → airy1ContL h (-(m : ℝ)) t f = airy1ContL h (-(m₀ : ℝ)) t f) := by
  obtain ⟨B, hB⟩ := hf.2 N
  refine ⟨B + 1, fun t ht m => ?_⟩
  have hstab : ∀ m, B + 1 ≤ m →
      airy1ContL h (-(m : ℝ)) t f = airy1ContL h (-((B + 1 : ℕ) : ℝ)) t f := by
    intro m hm
    rw [airy1ContL_eq_max hf hm t]
    have hge := airy1ContL_ge_of_bound hf hB m ht
    have : -((B + 1 : ℕ) : ℝ) ≤ airy1ContL h (-(m : ℝ)) t f := by
      push_cast; linarith
    exact (max_eq_right this).symm
  refine ⟨?_, hstab m⟩
  rcases le_total m (B + 1) with hm | hm
  · rw [airy1ContL_eq_max hf hm t]; exact le_max_right _ _
  · exact (hstab m hm).ge

end DeterministicLow

/-! ## The real-valued continuous version -/

open Classical in
/-- **The continuous Airy₁ process** `Ã` on `ℝ≥0`: on `goodLowSet` the infimum over `m` of the
lower-clamped continuous versions `airy1ContL h (−m)`, and `0` off it. -/
noncomputable def airy1Cont (h : Airy1FddPositive) (t : ℝ≥0) (f : ℝ → ℝ) : ℝ :=
  if f ∈ goodLowSet h then ⨅ m : ℕ, airy1ContL h (-(m : ℝ)) t f else 0

theorem measurable_airy1Cont (h : Airy1FddPositive) (t : ℝ≥0) :
    Measurable (airy1Cont h t) := by
  classical
  unfold airy1Cont
  exact Measurable.ite (measurableSet_goodLowSet h)
    (Measurable.iInf fun m => measurable_airy1ContL h _ t) measurable_const

/-- On `goodLowSet`, `Ã = Z_{m₀}` on `[0, N)`. -/
theorem airy1Cont_eq_airy1ContL {h : Airy1FddPositive} {f : ℝ → ℝ} (hf : f ∈ goodLowSet h)
    (N : ℕ) : ∃ m₀ : ℕ, ∀ t : ℝ≥0, t < N → airy1Cont h t f = airy1ContL h (-(m₀ : ℝ)) t f := by
  obtain ⟨m₀, hm₀⟩ := exists_airy1ContL_stable hf N
  refine ⟨m₀, fun t ht => ?_⟩
  simp only [airy1Cont, hf, ↓reduceIte]
  have hbdd : BddBelow (Set.range fun m : ℕ => airy1ContL h (-(m : ℝ)) t f) :=
    ⟨airy1ContL h (-(m₀ : ℝ)) t f, by rintro _ ⟨m, rfl⟩; exact (hm₀ t ht m).1⟩
  exact le_antisymm (ciInf_le hbdd m₀) (le_ciInf fun m => (hm₀ t ht m).1)

/-- Locally (near any `t`), `Ã(·, f)` coincides with a single `Z_{m₀}`. -/
theorem airy1Cont_eventuallyEq {h : Airy1FddPositive} {f : ℝ → ℝ} (hf : f ∈ goodLowSet h)
    (t : ℝ≥0) : ∃ m₀ : ℕ, ∃ V ∈ 𝓝 t, ∀ s ∈ V, airy1Cont h s f = airy1ContL h (-(m₀ : ℝ)) s f := by
  obtain ⟨m₀, hm₀⟩ := airy1Cont_eq_airy1ContL hf (⌈t⌉₊ + 1)
  refine ⟨m₀, Iio ((⌈t⌉₊ + 1 : ℕ) : ℝ≥0), Iio_mem_nhds ?_, fun s hs => hm₀ s hs⟩
  have := Nat.le_ceil t
  push_cast
  exact lt_of_le_of_lt this (lt_add_one _)

/-- **Every path of `Ã` is continuous.** -/
theorem continuous_airy1Cont (h : Airy1FddPositive) (f : ℝ → ℝ) :
    Continuous (airy1Cont h · f) := by
  classical
  by_cases hf : f ∈ goodLowSet h
  · refine continuous_iff_continuousAt.2 fun t => ?_
    obtain ⟨m₀, V, hV, hEq⟩ := airy1Cont_eventuallyEq hf t
    refine ((continuous_airy1ContL h (-(m₀ : ℝ)) f).continuousAt).congr ?_
    filter_upwards [hV] with s hs using (hEq s hs).symm
  · simp only [airy1Cont, hf, ↓reduceIte]
    exact continuous_const

/-- **Every path of `Ã` is locally `β`-Hölder for every `β < 1/2`.** -/
theorem holder_airy1Cont (h : Airy1FddPositive) (f : ℝ → ℝ) (t : ℝ≥0) (β : ℝ≥0)
    (hβ : 0 < β) (hβ2 : (β : ℝ) < 1 / 2) :
    ∃ V ∈ 𝓝 t, ∃ C, HolderOnWith C β (airy1Cont h · f) V := by
  classical
  by_cases hf : f ∈ goodLowSet h
  · obtain ⟨m₀, V, hV, hEq⟩ := airy1Cont_eventuallyEq hf t
    obtain ⟨W, hW, C, hC⟩ := holder_airy1ContL h (-(m₀ : ℝ)) f t β hβ hβ2
    refine ⟨V ∩ W, inter_mem hV hW, C, fun x hx y hy => ?_⟩
    change edist (airy1Cont h x f) (airy1Cont h y f) ≤ _
    rw [hEq x hx.1, hEq y hy.1]
    exact hC x hx.2 y hy.2
  · refine ⟨univ, univ_mem, 0, fun x _ y _ => ?_⟩
    simp [airy1Cont, hf]

/-- `⨅ m, max(−m, v) = v`. -/
theorem iInf_max_neg (v : ℝ) : ⨅ m : ℕ, max (-(m : ℝ)) v = v := by
  have hbdd : BddBelow (Set.range fun m : ℕ => max (-(m : ℝ)) v) :=
    ⟨v, by rintro _ ⟨m, rfl⟩; exact le_max_right _ _⟩
  refine le_antisymm (le_trans (ciInf_le hbdd ⌈-v⌉₊) (le_of_eq ?_))
    (le_ciInf fun m => le_max_right _ _)
  refine max_eq_right ?_
  have := Nat.le_ceil (-v)
  linarith

/-- **`Ã` is a modification of the coordinate process**, given almost sure lower boundedness. -/
theorem airy1Cont_ae_eq_of (h : Airy1FddPositive) (hlow : ∀ N, airy1Law h (lowEvent N) = 0)
    (t : ℝ≥0) : airy1Cont h t =ᵐ[airy1Law h] fun f => f t := by
  have h1 : ∀ᵐ f ∂airy1Law h, ∀ m : ℕ, airy1ContL h (-(m : ℝ)) t f = max (-(m : ℝ)) (f t) :=
    ae_all_iff.2 fun m => airy1ContL_ae_eq h _ t
  filter_upwards [h1, ae_mem_goodLowSet_of h hlow] with f hf1 hf2
  simp only [airy1Cont, hf2, ↓reduceIte, hf1]
  exact iInf_max_neg (f t)

/-- **Lower boundedness.** Under `Airy1FddPositive` and the `GOELeftTail` record,
for every `N`, almost surely the coordinate path is bounded below on the rational times of
`[0, N]`: `P(lowEvent N) = 0`. (H2) is discharged by contrib `smallWeight_defect_headline`
(`C_M = exp(K M^{5/2})`). -/
theorem airy1Law_lowEvent (h : Airy1FddPositive) (hT : GOELeftTail) (N : ℕ) :
    airy1Law h (lowEvent N) = 0 := by
  obtain ⟨K, -, hDef, -⟩ := AiryFdd.smallWeight_defect_headline
  exact airy1Law_lowEvent_of h hT.tail (CM := fun M => Real.exp (K * M ^ (5 / 2 : ℝ)))
    (K := K) (α := 5 / 2) (by norm_num) hDef (fun M _ => (Real.log_exp _).le) N

/-- Almost surely the coordinate path is bounded below on the rational times of every `[0, N]`
(under `GOELeftTail`). -/
theorem ae_bddBelow_rat (h : Airy1FddPositive) (hT : GOELeftTail) :
    ∀ᵐ f ∂airy1Law h, ∀ N : ℕ, ∃ B : ℕ, ∀ q : ℚ, Real.toNNReal q ≤ N →
      -(B : ℝ) ≤ f (Real.toNNReal q) :=
  ae_bddBelow_rat_of h (airy1Law_lowEvent h hT)

/-- **`Ã` is a modification of the coordinate process** (under `GOELeftTail`). -/
theorem airy1Cont_ae_eq (h : Airy1FddPositive) (hT : GOELeftTail) (t : ℝ≥0) :
    airy1Cont h t =ᵐ[airy1Law h] fun f => f t :=
  airy1Cont_ae_eq_of h (airy1Law_lowEvent h hT) t

/-- **Headline: the real-valued continuous version of the Airy₁ process.** Under
`Airy1FddPositive` and the `GOELeftTail` record (the small-weight defect input is proved, contrib
`smallWeight_defect_headline`), the process `Ã = airy1Cont h : ℝ≥0 → (ℝ → ℝ) → ℝ` has measurable
marginals, is a modification of the coordinate process under `airy1Law h`, and every path is
continuous and locally `β`-Hölder for all `β < 1/2`. -/
theorem exists_continuous_version (h : Airy1FddPositive) (hT : GOELeftTail) :
    ∃ A : ℝ≥0 → (ℝ → ℝ) → ℝ, (∀ t, Measurable (A t))
      ∧ (∀ t, A t =ᵐ[airy1Law h] fun f => f t)
      ∧ (∀ f, Continuous (A · f))
      ∧ ∀ f t (β : ℝ≥0), 0 < β → (β : ℝ) < 1 / 2 →
        ∃ V ∈ 𝓝 t, ∃ C, HolderOnWith C β (A · f) V :=
  ⟨airy1Cont h, measurable_airy1Cont h, airy1Cont_ae_eq h hT,
    continuous_airy1Cont h, holder_airy1Cont h⟩

end Airy1Gumbel
