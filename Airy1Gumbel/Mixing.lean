/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.Separated

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Airy1Gumbel

/-!
# Mixing, step 1: `mixing_tail` and `pair_mix` derived

The `Airy1BlockExtremes` interface carries ten mixing fields (`alpha`,
`alpha_nonneg`, `mixC`, `mixC_pos`, `mixc`, `mixc_pos`, `alpha_bound`,
`mixing_tail`, `decouple`, `pair_mix`). Two of them are consequences of the
others and are derived here, with no new trust:

* `mixing_tail_of_alpha_bound`: the `mixing_tail` field (the paper's
  summability of the mixing coefficients) from the elementary cubic bound `alpha_bound`
  (the paper's cubic mixing bound), at the explicit witness
  `A = max 1 (2 / mixc)`, via the already proved `mixing_tail_of_bound`.
* `pair_mix_of_decouple`: the `pair_mix` field ("for `j > q_N`, strong mixing
  implies") from `decouple` at `S = {0}`, `T = {j}`,
  `q = j` (the two-block case of the decoupling used in the EVT blocking
  telescope), plus `stat_marginal` and `Y_meas`, by
  complements. It holds for every `j`, including `j = 0`.
* `Airy1BlockExtremes.ofQR₃'` and the six `_of_QR₃'` headline corollaries:
  `ofQR₃`'s argument list minus `mixing_tail` and `pair_mix`.

The remaining mixing hypotheses are `alpha`, `alpha_nonneg`, `mixC*`, `mixc*`,
`alpha_bound` and `decouple`. Step 2 (`MixingRecord.lean`) restates the record
`CubicStrongMixing` and derives all of them (`Airy1BlockExtremes.ofQR₄`).
-/

/-- **`mixing_tail` from the cubic mixing bound** (the paper's cubic mixing
bound implies the summability of the mixing coefficients, in the proof of the paper's main
theorem (Theorem 1.1)): if `0 ≤ α(m) ≤ C e^{-c(m-1)³}` with `C, c > 0`, then the
`mixing_tail` field of `Airy1BlockExtremes` holds, with the explicit witness
`A = max 1 (2/c)`; since `A ≥ 1`, `c A³ ≥ c A ≥ 2 > 1`, and the limit is
`mixing_tail_of_bound`. -/
theorem mixing_tail_of_alpha_bound {C c : ℝ} (hC : 0 < C) (hc : 0 < c) {alpha : ℕ → ℝ}
    (hα : ∀ m, alpha m ≤ C * Real.exp (-c * ((m : ℝ) - 1) ^ 3)) (hα0 : ∀ m, 0 ≤ alpha m) :
    ∃ A : ℝ, 0 < A ∧ 1 < c * A ^ 3 ∧
      Tendsto (fun N : ℕ => (N : ℝ) * ∑' j : ℕ, alpha (qN A N + j)) atTop (𝓝 0) := by
  have hA1 : (1 : ℝ) ≤ max 1 (2 / c) := le_max_left _ _
  have hA2 : 2 / c ≤ max 1 (2 / c) := le_max_right _ _
  have hA0 : 0 < max 1 (2 / c) := lt_of_lt_of_le one_pos hA1
  have hcube : max 1 (2 / c) ≤ max 1 (2 / c) ^ 3 := le_self_pow₀ hA1 (by norm_num)
  have h2 : 2 ≤ c * max 1 (2 / c) := by
    rw [div_le_iff₀ hc] at hA2
    linarith
  have hA : 1 < c * max 1 (2 / c) ^ 3 := by
    have := mul_le_mul_of_nonneg_left hcube hc.le
    linarith
  exact ⟨max 1 (2 / c), hA0, hA, mixing_tail_of_bound hC hc hα hα0 hA0 hA⟩

/-- **`pair_mix` from `decouple`** (the paper: "for `j > q_N`, strong
mixing implies `ℙ(Y₀ > u_N, Y_j > u_N) ≤ p_N² + α_Y(j)`"). Apply the decoupling
bound (the two-block case of the telescope, with
`α_Y` as in the paper's cubic mixing bound) to `S = {0}`, `T = {j}`, `q = j`
(the side condition `0 + j ≤ j` holds for every `j`, including `j = 0`). With
`p₀ = ℙ(Y₀ ≤ u)`, `p_j = ℙ(Y_j ≤ u)` and `r = ℙ(Y₀ ≤ u, Y_j ≤ u)`,
complements give `ℙ(Y₀ > u, Y_j > u) = 1 - p₀ - p_j + r`, and `stat_marginal`
gives `p_j = p₀`, so the claim is `r ≤ p₀ p_j + α(j)`. The bound holds for every
`j`; the paper only uses `j > q_N`. -/
theorem pair_mix_of_decouple {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    {alpha : ℕ → ℝ}
    (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
    (decouple : ∀ (S T : Finset ℕ) (q : ℕ) (u : ℝ),
      (∀ s ∈ S, ∀ t ∈ T, s + q ≤ t) →
      |P.real ({ω | ∀ s ∈ S, Y s ω ≤ u} ∩ {ω | ∀ t ∈ T, Y t ω ≤ u}) -
        P.real {ω | ∀ s ∈ S, Y s ω ≤ u} * P.real {ω | ∀ t ∈ T, Y t ω ≤ u}|
        ≤ alpha q)
    (u : ℝ) (j : ℕ) :
    P.real {ω | Y 0 ω > u ∧ Y j ω > u} ≤ P.real {ω | Y 0 ω > u} ^ 2 + alpha j := by
  have hd := decouple {0} {j} j u (by simp)
  have hS : ∀ i : ℕ, {ω | ∀ s ∈ ({i} : Finset ℕ), Y s ω ≤ u} = {ω | Y i ω ≤ u} := by
    intro i; ext ω; simp
  rw [hS 0, hS j, abs_le] at hd
  have hm : ∀ i, MeasurableSet {ω | Y i ω ≤ u} :=
    fun i => measurableSet_le (Y_meas i) measurable_const
  have hgt : ∀ i, {ω | Y i ω > u} = {ω | Y i ω ≤ u}ᶜ := by
    intro i; ext ω; simp [not_le]
  have hpair : {ω | Y 0 ω > u ∧ Y j ω > u} = ({ω | Y 0 ω ≤ u} ∪ {ω | Y j ω ≤ u})ᶜ := by
    ext ω; simp [not_le]
  have hsm : P.real {ω | Y j ω > u} = P.real {ω | Y 0 ω > u} := by
    simp only [measureReal_def, stat_marginal u j]
  rw [hgt, hgt, measureReal_compl (hm _), measureReal_compl (hm _)] at hsm
  rw [hpair, hgt, measureReal_compl ((hm 0).union (hm j)), measureReal_compl (hm 0)]
  have hu := measureReal_union_add_inter (P := P) {ω | Y 0 ω ≤ u} _ (hm j)
  have hpj : P.real {ω | Y j ω ≤ u} = P.real {ω | Y 0 ω ≤ u} := by linarith
  rw [hpj] at hd hu
  nlinarith [hd.2]

/-! ### Smart constructor and `_of_QR₃'` headline corollaries -/

section OfQR₃'

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (Y : ℕ → Ω → ℝ) (Y_meas : ∀ j, Measurable (Y j))
  (alpha : ℕ → ℝ) (alpha_nonneg : ∀ m, 0 ≤ alpha m)
  (mixC : ℝ) (mixC_pos : 0 < mixC) (mixc : ℝ) (mixc_pos : 0 < mixc)
  (alpha_bound : ∀ m, alpha m ≤ mixC * Real.exp (-mixc * ((m : ℝ) - 1) ^ 3))
  (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
  (stat_pair : ∀ (u : ℝ) (i d : ℕ),
    P {ω | Y i ω > u ∧ Y (i + d) ω > u} = P {ω | Y 0 ω > u ∧ Y d ω > u})
  (qr : QRUnitBlockLaw Y P) (qr₂ : QRTwoBlockLaw Y P) (two : QRTwoIntervalLaw Y P)
  (mesoscopic : ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
    Tendsto (fun N : ℕ =>
      (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
        P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0))
  (decouple : ∀ (S T : Finset ℕ) (q : ℕ) (u : ℝ),
    (∀ s ∈ S, ∀ t ∈ T, s + q ≤ t) →
    |P.real ({ω | ∀ s ∈ S, Y s ω ≤ u} ∩ {ω | ∀ t ∈ T, Y t ω ≤ u}) -
      P.real {ω | ∀ s ∈ S, Y s ω ≤ u} * P.real {ω | ∀ t ∈ T, Y t ω ≤ u}|
      ≤ alpha q)

include Y_meas alpha_nonneg mixC_pos mixc_pos alpha_bound stat_marginal stat_pair qr qr₂ two
  mesoscopic decouple

/-- Smart constructor for `Airy1BlockExtremes` (mixing, step 1): `ofQR₃` with
`mixing_tail` and `pair_mix` removed from the argument list. `mixing_tail`
is derived from `alpha_bound` by `mixing_tail_of_alpha_bound`, and `pair_mix`
from `decouple`, `stat_marginal` and
`Y_meas` by `pair_mix_of_decouple`. As in `ofQR₃`, `sharp_tail`, `touching` and
`separated` are discharged from `QRUnitBlockLaw`, `QRTwoBlockLaw`
([QuastelRemenik2012, Theorem 4] with the paper's determinant formula for the
two-block law) and `QRTwoIntervalLaw` (the paper's two-interval determinant formula,
proved in the paper). -/
def Airy1BlockExtremes.ofQR₃' : Airy1BlockExtremes P :=
  Airy1BlockExtremes.ofQR₃ Y Y_meas alpha alpha_nonneg mixC mixC_pos mixc mixc_pos
    alpha_bound stat_marginal stat_pair qr qr₂ two
    (mixing_tail_of_alpha_bound mixC_pos mixc_pos alpha_bound alpha_nonneg) mesoscopic
    decouple (pair_mix_of_decouple Y_meas stat_marginal decouple)

/-- **Conditional Gumbel limit, integer-block form, with `sharp_tail`,
`touching`, `separated`, `mixing_tail` and `pair_mix` discharged** (the paper's main
theorem (Theorem 1.1); block form of `Airy1BlockExtremes.gumbel_limit`). The hypothesis
list is that of `gumbel_limit_of_QR₃` minus `mixing_tail` and `pair_mix`. -/
theorem Airy1BlockExtremes.gumbel_limit_of_QR₃' (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ j ∈ Finset.range N, Y j ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  (Airy1BlockExtremes.ofQR₃' Y Y_meas alpha alpha_nonneg mixC mixC_pos mixc mixc_pos
    alpha_bound stat_marginal stat_pair qr qr₂ two mesoscopic decouple).gumbel_limit z

/-- **Conditional Gumbel limit, continuum integer-length form, with
`sharp_tail`, `touching`, `separated`, `mixing_tail` and `pair_mix`
discharged** (the paper's main theorem (Theorem 1.1); corollary of
`Airy1ContinuousMax.gumbel_limit_continuum`): `ℙ(M_N ≤ u_N(z)) → e^{-e^{-z}}`.
The hypothesis list is that of `gumbel_limit_continuum_of_QR₃` minus
`mixing_tail` and `pair_mix`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_QR₃' (C : Airy1ContinuousMax P)
    (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum (Airy1BlockExtremes.ofQR₃' Y Y_meas alpha alpha_nonneg mixC
    mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂ two mesoscopic
    decouple) hY z

/-- **Normalized integer-length Gumbel limit, with `sharp_tail`, `touching`,
`separated`, `mixing_tail` and `pair_mix` discharged** (the paper's main theorem (Theorem 1.1);
corollary of `Airy1ContinuousMax.gumbel_limit_continuum_normalized`):
`(M_N - a_N)/b_N` converges in law to the standard Gumbel distribution. The
hypothesis list is that of `gumbel_limit_continuum_normalized_of_QR₃` minus
`mixing_tail` and `pair_mix`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_normalized_of_QR₃'
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ),
      (C.A x ω - gumbelA N) / gumbelB N ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_normalized (Airy1BlockExtremes.ofQR₃' Y Y_meas alpha
    alpha_nonneg mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂
    two mesoscopic decouple) hY z

/-- **Perturbed-level integer-length Gumbel limit, with `sharp_tail`,
`touching`, `separated`, `mixing_tail` and `pair_mix` discharged** (the first step
of the real-length extension of the paper's main theorem (Theorem 1.1);
corollary of `Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto`). The
hypothesis list is that of `gumbel_limit_continuum_of_tendsto_of_QR₃` minus
`mixing_tail` and `pair_mix`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto_of_QR₃'
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) (w : ℕ → ℝ)
    (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N (w N)})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_of_tendsto (Airy1BlockExtremes.ofQR₃' Y Y_meas alpha
    alpha_nonneg mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂
    two mesoscopic decouple) hY z w hw

/-- **Real-length conditional Gumbel limit, with `sharp_tail`, `touching`,
`separated`, `mixing_tail` and `pair_mix` discharged** (the paper's main
theorem (Theorem 1.1), real `T → ∞`; corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_real`): `ℙ(M_T ≤ u_T(z)) → e^{-e^{-z}}`.
The hypothesis list is that of `gumbel_limit_continuum_real_of_QR₃` minus
`mixing_tail` and `pair_mix`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_of_QR₃'
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun T : ℝ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T, C.A x ω ≤ gumbelUR T z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_real (Airy1BlockExtremes.ofQR₃' Y Y_meas alpha alpha_nonneg
    mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂ two
    mesoscopic decouple) hY z

/-- **The paper's headline, with `sharp_tail`, `touching`, `separated`,
`mixing_tail` and `pair_mix` discharged** (the paper's main theorem (Theorem 1.1), normalized
real-length shape; corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_real_normalized`): `(M_T - a_T)/b_T`
converges in law to the standard Gumbel distribution as `T → ∞`. The hypothesis
list is that of `gumbel_limit_continuum_real_normalized_of_QR₃` minus
`mixing_tail` and `pair_mix`; the mixing inputs left are `alpha`, `alpha_nonneg`,
`mixC*`, `mixc*`, `alpha_bound` (the paper's cubic mixing bound) and `decouple`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QR₃'
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun T : ℝ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (C.A x ω - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_real_normalized (Airy1BlockExtremes.ofQR₃' Y Y_meas alpha
    alpha_nonneg mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr qr₂
    two mesoscopic decouple) hY z

end OfQR₃'

end Airy1Gumbel
