/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.MixingRecord
import Airy1Gumbel.MesoscopicInputs
import Airy1Gumbel.SharpTail

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators NNReal

namespace Airy1Gumbel

/-!
# Shared definitions and the `MesoscopicBounds` bundle for the `mesoscopic` field

This file fixes the shared definitions used to derive the `mesoscopic` field of
`Airy1BlockExtremes` (the paper's mesoscopic estimate) from the records (Newman's inequality is
the proved `newman_lemma3`, not a record), the proved exponent arithmetic (the window
`θ ∈ ((2/3)/χ³, 4/3)` is nonempty exactly when `χ > (1/2)^{1/3}`, the field's strict bound), and
the bundle `MesoscopicBounds`. The proofs live in `MesoscopicCover.lean` (block-to-grid
covering), `MesoscopicPair.lean` (grid pair bound via Newman, one-point bound) and
`MesoscopicSum.lean` (the asymptotic sum); the bridge `mesoscopic_of_records`, `ofQR₅` and the
six `_of_QR₅` corollaries are in `MesoscopicRecord.lean`. No `sorry` anywhere.

Target (`Airy1BlockExtremes.mesoscopic`, `BlockExtremes.lean`):
`∀ (z χ : ℝ) (A : ℝ), (1/2)^((1:ℝ)/3) < χ → χ < 1 → 0 < A →
  Tendsto (fun N : ℕ => (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
    P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0)`,
with `mN χ z N = ⌊χ √(2 u_N)⌋₊`, `qN A N = ⌈A (log N)^{1/3}⌉₊`, `u_N = gumbelU N z`.

## Proof outline

* (i) Pair bound by a clamp: the clamp `clampInd v` is monotone,
  1-Lipschitz and `𝟙{t > v} ≤ clampInd v t ≤ 𝟙{t > v - 1}`, so
  `ℙ(A x > v, A y > v) ≤ 𝔼[g(A x) g(A y)] = 𝔼g(A x) 𝔼g(A y) + Cov(g(A x), g(A y))
   ≤ ℙ(A 0 > v - 1)² + Cov(A 0, A (y - x))`
  by `newman_pair` (Lip constants 1, 1), `PairStationary.cov_shift`, `X.stat`.
  No mollification, no density bound from [BaikBuckinghamDiFranco2008], no constant `C·u`
  in front of the covariance.
* (ii) One-point tail: `ℙ(A 0 > w) ≤ ℙ(Y₀ > w)` (path continuity, `0 ∈ [0,1]`), and
  `ℙ(Y₀ > w) ≤ 2 e^{-H(w)}` eventually from `sharp_tail` (= `sharp_tail_of_QRUnitBlockLaw`).
* (iii) Block-to-grid covering by a modulus estimate: mesh `n = meshN u = ⌈u⁴⌉₊`, centres
  `gridPt j n k = j + k/n`,
  `k ≤ n`, radius `s = 1/n`, and `LocalModulusEstimate` at `ℓ = √n / C₀`, so the
  threshold is `C₀ ℓ √s = 1` and each centre fails with probability
  `≤ C₀ e^{-c₀ √n / C₀} = modFail C₀ c₀ n`. If `Y_j > v` there is `t ∈ [j, j+1]` with
  `A t > v` (`exists_lt_of_lt_csSup`; nonemptiness only), the centre `k = ⌊n (t - j)⌋₊`
  has `|t - gridPt j n k| ≤ 1/n`, so either `A (gridPt j n k) > v - 1` or the
  oscillation event at that centre occurs.
* (iii′) Covering by upcrossings (`Upcrossing.lean`): `LocalModulusEstimate` is replaced
  by the two-point fdd record `HighLevelUpcrossingTail` plus path continuity. On each
  sub-interval `[j + k/n, j + (k+1)/n]`, either the left grid point has `A > v - 1` or the band
  `[v-1, v]` is upcrossed, which a dyadic chain on the clamp to the band reduces to two-point
  events at levels `≥ v - 1`; the failure probability is `O(n^K e^{-c₁ n/32}) ≤ e^{-√n}`
  eventually. The record holds only at levels `≥ a₀`, so the `cover` field carries a level
  threshold `coverLevel`; the consumer uses `v = u_N → ∞`.

## Exponent arithmetic (strictly inside the χ range)

Write `u = u_N`, `a = √(2u)`, `κ = airyKappa = 4√2/3`. Then **`κ u^{3/2} = (2/3) a³`**
(proved below: `airyKappa_mul_rpow_three_halves`).

Combining the four fields (`MesoscopicBounds.block_pair_le`), for `j - 1 ≥ d₀(θ)`:
`ℙ(Y₀ > u, Y_j > u) ≤ (n+1)² [p(u-2)² + e^{-θ (j-1)³}] + 2 (n+1) C₀ e^{-c₀ √n / C₀}`,
`p(w) := ℙ(Y₀ > w)`. The right side is nonincreasing in `j`, and the sum has at most
`q_N` terms, all with `j ≥ m_N + 1`, so
`N · Σ ≤ N q_N · envelope(j = m_N + 1)`. Bounds used:
* `N ≤ K e^{H(u)}` (`gumbel_normalization`), `H(u) ≤ κ u^{3/2} + O(1)` for `u ≥ 1`;
* `q_N = O(√u)` (from `u_N ≥ (γ/4)(log N)^{2/3}`, cf. `gumbelU_tendsto_atTop`);
* `n + 1 = O(u⁴)`, `√n ≥ u²`; `m_N = ⌊χ a⌋₊ > χ a - 1`.

Exponents of the three contributions (each `+ O(log u)` from polynomial factors):
1. `N q n² p(u-2)²`:   `κ u^{3/2} - 2κ (u-2)^{3/2} = -κ u^{3/2} + O(√u) → -∞`.
2. `N q n · modFail`:   `κ u^{3/2} - (c₀/C₀) u² → -∞` (mesh `√n ≥ u²` beats `u^{3/2}`;
   any `n ≥ u^{3+ε}` would do).
3. `N q n² e^{-θ m³}`:  `(2/3) a³ - θ (χ a - 1)³ = -(θχ³ - 2/3) a³ + 3θχ² a² - 3θχ a + θ`.
   This `→ -∞` **iff `θ χ³ > 2/3`** (the cubic term must win; the `+3θχ²a²` correction
   from the `-1` shift has the wrong sign).

Choice of `θ`: `cov_decay` (from the exact rate `e^{c d² - (4/3) d³}` of
[BasuBusaniFerrari2023, Theorem 1.1], via `theta_bound`)
gives every `θ < 4/3`. We need `θ ∈ ((2/3)/χ³, 4/3)`, nonempty **iff `χ³ > 1/2`**, i.e.
iff `χ > (1/2)^{1/3}`. We take `θ = mesoTheta χ = (4/3 + (2/3)/χ³)/2`; then
`θ χ³ - 2/3 = (2/3)(χ³ - 1/2)` (proved: `mesoTheta_mul_cube_sub`).

**At the field's lower bound `χ = (1/2)^{1/3}`:** `θ χ³ < (4/3)(1/2) = 2/3` for every
admissible `θ < 4/3`, the leading coefficient of 3. is `≥ 0`, and with the exact
rate the borderline `θ = 4/3` gives `(2/3)a³ - (4/3)(a/2^{1/3} - 1)³ = +4·2^{-2/3} a² + O(a)
→ +∞`. So the argument fails exactly at the endpoint and **closes for every χ strictly
above it**, which is what the field assumes (strict `<`). The constant `4/3` is
sharp for this: with any rate `θ_max < 4/3` in the record the χ-threshold would be
`(2/(3θ_max))^{1/3} > (1/2)^{1/3}` and the field as stated would NOT follow.
Numerically, `χ = 0.8` (`χ³ = 0.512`): `θ = 1.3177`, margin `θχ³ - 2/3 = 0.0080`,
so term 3's exponent is `-0.0080 a³ + 2.53 a² + …` (`3θχ² = 2.53`); it turns negative
only for `a ≳ 316` (`u ≳ 5·10⁴`). Asymptotically fine; numerically the bound is very late.

## Records: each is strong enough for its role

* `LocalModulusEstimate`: every centre, uniform in `0 < s ≤ 1`, eventually in `ℓ`;
  existential event (no `sSup` junk). Sufficient for (iii) with `s = 1/n`, `ℓ = √n/C₀`.
* `CubicCovarianceDecay`: exact rate `4/3` (needed, see above) + `memLp_zero`
  (gives `L²` everywhere, the premise of `newman_lemma3`).
* `PairStationary`: gives `cov_shift`. `ProcessAssociated`: gives `pair_pqd`.
* `QRUnitBlockLaw`: gives `sharp_tail`, hence the one-point upper tail (ii) and
  `N ≤ K e^{H(u_N)}`.
* Link `X.A = C.A` with `C : Airy1ContinuousMax P`: `Y_eq` (covering) and `path_cont`
  (only for `A 0 ≤ Y 0`, via `le_block_sup`).
-/

/-! ## Shared definitions -/

section Defs

/-- Mesh resolution at level `u`: `n(u) = ⌈u⁴⌉₊` (the paper's mesh `h_M = M^{-4}`). -/
noncomputable def meshN (u : ℝ) : ℕ := ⌈u ^ 4⌉₊

/-- Grid centre `k` of the unit block `[j, j+1]` at resolution `n`: `j + k/n`
(used for `k ∈ Finset.range (n + 1)`). -/
noncomputable def gridPt (j n k : ℕ) : ℝ := (j : ℝ) + (k : ℝ) / (n : ℝ)

/-- The clamped indicator at level `v`: `t ↦ max 0 (min 1 (t - (v - 1)))`.
Monotone, 1-Lipschitz, and `𝟙{t > v} ≤ clampInd v t ≤ 𝟙{t > v - 1}`. -/
noncomputable def clampInd (v t : ℝ) : ℝ := max 0 (min 1 (t - (v - 1)))

/-- The local oscillation event at centre `c`, radius `s`, threshold `δ`; with
`δ = C₀ ℓ √s` it is literally the event of `LocalModulusEstimate.bound`. -/
def oscEvent {Ω : Type*} (A : ℝ → Ω → ℝ) (c s δ : ℝ) : Set Ω :=
  {ω | ∃ t₁ t₂ : ℝ, |t₁ - c| ≤ s ∧ |t₂ - c| ≤ s ∧ δ < |A t₁ ω - A t₂ ω|}

/-- Per-centre modulus failure bound at resolution `n`: `C₀ e^{-c₀ √n / C₀}`
(`LocalModulusEstimate` at `ℓ = √n / C₀`, `s = 1/n`). -/
noncomputable def modFail (C₀ c₀ : ℝ) (n : ℕ) : ℝ :=
  C₀ * Real.exp (-c₀ * (Real.sqrt n / C₀))

/-- The decay rate used for a given `χ`: the midpoint of `((2/3)/χ³, 4/3)`. -/
noncomputable def mesoTheta (χ : ℝ) : ℝ := (4 / 3 + 2 / 3 / χ ^ 3) / 2

/-- Per-block-pair envelope (the paper's mesoscopic point bound, Lean form):
`(n+1)² (p² + e^{-θ (j-1)³}) + 2 (n+1) modFail C₀ c₀ n`. -/
noncomputable def mesoPairEnvelope (p θ C₀ c₀ : ℝ) (n j : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 2 * (p ^ 2 + Real.exp (-θ * ((j : ℝ) - 1) ^ 3)) +
    2 * ((n : ℝ) + 1) * modFail C₀ c₀ n

end Defs

/-! ## Proved exponent arithmetic -/

section Arithmetic

/-- `κ u^{3/2} = (2/3) (√(2u))³`: the exponent of `N` in the variable `a = √(2u)`. -/
theorem airyKappa_mul_rpow_three_halves {u : ℝ} (hu : 0 ≤ u) :
    airyKappa * u ^ ((3 : ℝ) / 2) = 2 / 3 * Real.sqrt (2 * u) ^ 3 := by
  have h1 : u ^ ((3 : ℝ) / 2) = Real.sqrt u ^ 3 := by
    rw [show (3 : ℝ) / 2 = (1 / 2) * ((3 : ℕ) : ℝ) by norm_num, Real.rpow_mul hu,
      Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have h2 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h1, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow, h2, airyKappa]
  ring

/-- The field's `χ` lower bound is exactly `χ³ > 1/2`. -/
theorem one_half_lt_cube_of_lt {χ : ℝ} (hχ : (1 / 2 : ℝ) ^ ((1 : ℝ) / 3) < χ) :
    1 / 2 < χ ^ 3 := by
  have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by norm_num) _
  have h := pow_lt_pow_left₀ hχ h0 (by norm_num : (3 : ℕ) ≠ 0)
  rwa [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    show (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one] at h

/-- `mesoTheta χ < 4/3` when `χ³ > 1/2` (so `cov_decay` applies). -/
theorem mesoTheta_lt {χ : ℝ} (hχ : 1 / 2 < χ ^ 3) : mesoTheta χ < 4 / 3 := by
  unfold mesoTheta
  have hc : 0 < χ ^ 3 := by linarith
  have : 2 / 3 / χ ^ 3 < 4 / 3 := by
    rw [div_lt_iff₀ hc]
    linarith
  linarith

/-- `mesoTheta χ > 0` when `χ³ > 0`. -/
theorem mesoTheta_pos {χ : ℝ} (hχ : 0 < χ ^ 3) : 0 < mesoTheta χ := by
  unfold mesoTheta
  have : 0 < 2 / 3 / χ ^ 3 := div_pos (by norm_num) hχ
  linarith

/-- The cubic margin: `θ χ³ - 2/3 = (2/3)(χ³ - 1/2)` at `θ = mesoTheta χ`;
positive iff `χ³ > 1/2`. -/
theorem mesoTheta_mul_cube_sub {χ : ℝ} (hχ : 0 < χ ^ 3) :
    mesoTheta χ * χ ^ 3 - 2 / 3 = 2 / 3 * (χ ^ 3 - 1 / 2) := by
  have hX : 2 / 3 / χ ^ 3 * χ ^ 3 = 2 / 3 := div_mul_cancel₀ _ hχ.ne'
  unfold mesoTheta
  linear_combination (1 / 2 : ℝ) * hX

/-- The margin is strictly positive on the field's `χ` range. -/
theorem mesoTheta_margin_pos {χ : ℝ} (hχ : (1 / 2 : ℝ) ^ ((1 : ℝ) / 3) < χ) :
    2 / 3 < mesoTheta χ * χ ^ 3 := by
  have h := one_half_lt_cube_of_lt hχ
  have e := mesoTheta_mul_cube_sub (show 0 < χ ^ 3 by linarith)
  nlinarith

end Arithmetic

/-! ## The `MesoscopicBounds` bundle -/

/-- The four estimates (plus the sharp tail) from which `MesoscopicSum.lean` derives the
`mesoscopic` field, stated for block maxima `Y` and a process `W` (in the bridge,
`Y = C.Y`, `W = C.A = X.A`). Contains no `sorry`; the fields are produced from
the records in `MesoscopicCover.lean` and `MesoscopicPair.lean` (`MesoscopicBounds.ofRecords`). -/
structure MesoscopicBounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (W : ℝ → Ω → ℝ) where
  /-- Modulus amplitude (`LocalModulusEstimate.C₀`). -/
  modC : ℝ
  modC_pos : 0 < modC
  /-- Modulus rate (`LocalModulusEstimate.c₀`). -/
  modc : ℝ
  modc_pos : 0 < modc
  /-- Level threshold of the covering: `cover` is asserted only at levels `v ≥ coverLevel`.
  The consumer uses `v = u_N → ∞`, so any finite threshold
  suffices; the `LocalModulusEstimate` route holds at every level (`coverLevel := 0`), the
  `HighLevelUpcrossingTail` route at `v ≥ a₀ + 1`. -/
  coverLevel : ℝ
  /-- (A) Block-to-grid covering (the paper's block-to-grid reduction), at every large resolution `n`,
  uniformly in the block index `j` and in the levels `v ≥ coverLevel`. -/
  cover : ∀ᶠ n : ℕ in atTop, ∀ (j : ℕ) (v : ℝ), coverLevel ≤ v →
    P.real {ω | Y 0 ω > v ∧ Y j ω > v} ≤
      (∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
        P.real {ω | W (gridPt 0 n k) ω > v - 1 ∧ W (gridPt j n k') ω > v - 1}) +
      2 * ((n : ℝ) + 1) * modFail modC modc n
  /-- (B) Grid-pair bound (Lean form (i) of the paper's pair estimate, by a clamp). -/
  pair : ∀ x y v : ℝ,
    P.real {ω | W x ω > v ∧ W y ω > v} ≤
      P.real {ω | W 0 ω > v - 1} ^ 2 + covariance (W 0) (W (y - x)) P
  /-- (B) Covariance decay: every `θ < 4/3` is eventually a covariance decay rate. -/
  cov_decay : ∀ θ : ℝ, θ < 4 / 3 → ∃ d₀ : ℝ, ∀ d : ℝ, d₀ ≤ d →
    covariance (W 0) (W d) P ≤ Real.exp (-θ * d ^ 3)
  /-- (B) One-point tail below the block tail (step (ii)). -/
  one_point : ∀ w : ℝ, P.real {ω | W 0 ω > w} ≤ P.real {ω | Y 0 ω > w}
  /-- The sharp block tail `ℙ(Y₀ > u) ~ e^{-H(u)}`. -/
  sharp_tail :
    Tendsto (fun u : ℝ => P.real {ω | Y 0 ω > u} / Real.exp (-airyH u)) atTop (𝓝 1)


end Airy1Gumbel
