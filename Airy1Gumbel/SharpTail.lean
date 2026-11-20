/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.ContinuumMax
import Airy1Gumbel.ExternalInputs
import Airy1GumbelContrib.AiryKernel.TailAsymptotic
import Airy1GumbelContrib.AiryKernel.TraceWeight

open Filter MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace Airy1Gumbel

/-!
# Discharging `sharp_tail` from the contrib tail asymptotic

The `sharp_tail` field of `Airy1BlockExtremes`
(`BlockExtremes.lean`) asserts `ℙ(Y₀ > u) / e^{-H(u)} → 1`, the leading order
of the paper's sharp one-block tail at block
length `T = 1`. This module derives that field from the contrib
two-term expansion `AiryConj.piT_sub_traceLead_isLittleO`
(`π_T(M) = Tρ(M) + ρ(M)/(4M) + o(ρ(M)/M)`) and the external record
`QRUnitBlockLaw` (`ExternalInputs.lean`: [QuastelRemenik2012, Theorem 4] at
QR's own conjugation weight `a = 2`). The paper's determinant form of the one-block tail
(weight `a = √(2u)`) is derived, not assumed.

* `airyKappa_eq_kappaC`, `airyCStar_eq_Cstar`: the main-package constants are
  definitionally the contrib constants (`κ = 4√2/3`, `C_* = 2^{1/4}/√π`,
  as in the paper).
* `exp_neg_airyH_eq`: `e^{-H(u)} = ρ(u)` for `u > 0` (the paper's definition of `ρ`).
* `eventually_hsNorm_airyTildeOp_lt`: at any fixed admissible weight (in
  particular QR's `a = 2T`), `‖Ã_{u,T,a}‖₂ → 0`; this locates the records'
  operators on the disk where contrib's entire `fredholmDet` equals the
  exp-trace `det₁` (`fredholmDet_eq_fredholmDetOne`).
* `eventually_fredholmDet_airyTildeOp_eq`, `QRUnitBlockLaw.law_detOne`,
  `QRUnitBlockLaw.iff_law_detOne`: the record, stated with the
  entire determinant, is equivalent to its exp-trace form.
* `QRUnitBlockLaw.detOne_form`, `QRUnitBlockLaw.iff_detOne_form`: the
  record at QR's weight `a = 2` is equivalent to the paper's determinant form
  `ℙ(Y₀ > u) = 1 - detOneAiryTilde u 1` at `a = √(2u)`, via contrib
  `AiryConj.eventually_detOneAiryTilde_one_eq_weight_two`
  (`AiryKernel/TraceWeight.lean`).
* `sharp_tail_of_QRUnitBlockLaw`: the `sharp_tail` field from the record.
* `Airy1BlockExtremes.ofQR`: a smart constructor taking every field of
  `Airy1BlockExtremes` except `sharp_tail`, plus `QRUnitBlockLaw`.
* `Airy1BlockExtremes.gumbel_limit_of_QR` and the five
  `Airy1ContinuousMax.gumbel_limit_continuum*_of_QR` corollaries: the headline
  conditional Gumbel limits (the paper's main theorem (Theorem 1.1)) with `sharp_tail`
  removed from the hypothesis list.

The `Airy1BlockExtremes` structure is used unchanged.
-/

/-! ### Constants and the rate function -/

/-- The main-package Airy-decay constant `κ = 4√2/3` (as in the paper) is
definitionally the contrib constant `AiryConj.kappaC`. -/
theorem airyKappa_eq_kappaC : airyKappa = AiryConj.kappaC := rfl

/-- The main-package prefactor constant `C_* = 2^{1/4}/√π` (as in the paper) is
definitionally the contrib constant `AiryConj.Cstar`. -/
theorem airyCStar_eq_Cstar : airyCStar = AiryConj.Cstar := rfl

/-- `e^{-H(u)} = ρ(u)` for `u > 0`, where
`H(u) = κ u^{3/2} - (1/4) log u - log C_*` (`airyH`) and
`ρ(u) = C_* u^{1/4} e^{-κ u^{3/2}}` (the paper's definition of `ρ`; contrib
`AiryConj.rhoM`). -/
theorem exp_neg_airyH_eq {u : ℝ} (hu : 0 < u) :
    Real.exp (-airyH u) = AiryConj.rhoM u := by
  unfold airyH AiryConj.rhoM
  rw [← airyKappa_eq_kappaC, ← airyCStar_eq_Cstar]
  have h : -(airyKappa * u ^ ((3 : ℝ) / 2) - 1 / 4 * Real.log u - Real.log airyCStar)
      = Real.log airyCStar + Real.log u * (1 / 4) + -airyKappa * u ^ ((3 : ℝ) / 2) := by
    ring
  rw [h, Real.exp_add, Real.exp_add, Real.exp_log airyCStar_pos,
    ← Real.rpow_def_of_pos hu]

/-! ### QR's weight: Hilbert–Schmidt smallness and the re-weighting bridge -/

/-- **The records lie on the Plemelj disk eventually.** For every fixed
admissible weight `a` (`0 < T`, `T + 1 ≤ a`; in particular QR's weight
`a = 2T` for `T ≥ 1`) and every `ε > 0`, eventually in `u`,
`‖Ã_{u,T,a}‖₂ < ε`. From contrib `AiryConj.hsNorm_airyTilde_le`
(`‖Ã‖₂ ≤ C (1+u) √(1+a³) e^{a³/3 - 2ua}`) and `1 + u ≤ eᵘ`, `a ≥ 1`:
`‖Ã‖₂ ≤ K e^{-u}`. At `ε = 1` this is the region where the exp-trace `det₁`
series converges and equals the entire determinant `fredholmDet` of
`QRUnitBlockLaw`/`QRTwoBlockLaw` (contrib `fredholmDet_eq_fredholmDetOne`). -/
theorem eventually_hsNorm_airyTildeOp_lt {T a : ℝ} (hT : 0 < T) (ha : T + 1 ≤ a)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u in atTop, ∀ hu : 0 < u,
      HilbertSchmidt.hsNorm (AiryConj.airyTildeOp u T a hT hu ha) < ε := by
  obtain ⟨C, hC, hb⟩ := AiryConj.hsNorm_airyTilde_le T hT
  have ha1 : (1 : ℝ) ≤ a := by linarith
  set K : ℝ := C * Real.sqrt (1 + a ^ 3) * Real.exp (a ^ 3 / 3) with hK
  have hKpos : 0 < K := by
    have h3 : (0 : ℝ) < 1 + a ^ 3 := by positivity
    exact mul_pos (mul_pos hC (Real.sqrt_pos.mpr h3)) (Real.exp_pos _)
  have hlim : Tendsto (fun u : ℝ => K * Real.exp (-u)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul K
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with u hu_lt hu
  refine lt_of_le_of_lt ((hb u a hu ha).trans ?_) hu_lt
  have h1 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hexp : Real.exp (a ^ 3 / 3 - 2 * u * a)
      = Real.exp (a ^ 3 / 3) * Real.exp (-(2 * u * a)) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : Real.exp u * Real.exp (-(2 * u * a)) ≤ Real.exp (-u) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hu.le (sub_nonneg.mpr ha1)]
  have hE : 0 ≤ Real.exp (-(2 * u * a)) := (Real.exp_pos _).le
  calc C * (1 + u) * Real.sqrt (1 + a ^ 3) * Real.exp (a ^ 3 / 3 - 2 * u * a)
      = K * ((1 + u) * Real.exp (-(2 * u * a))) := by rw [hexp, hK]; ring
    _ ≤ K * (Real.exp u * Real.exp (-(2 * u * a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hE) hKpos.le
    _ ≤ K * Real.exp (-u) := mul_le_mul_of_nonneg_left h2 hKpos.le

/-- **Entire vs exp-trace determinant at QR's weights**. For every
fixed admissible weight (`0 < T`, `T + 1 ≤ a`), eventually in `u`, contrib's
entire Fredholm determinant `det(I − Ã_{u,T,a})` (`HilbertSchmidt.fredholmDet`)
equals the exp-trace `det₁(I − Ã_{u,T,a})` (`HilbertSchmidt.fredholmDetOne`):
the operator lies in the disk `‖Ã‖₂ < 1` (`eventually_hsNorm_airyTildeOp_lt`),
where contrib `fredholmDet_eq_fredholmDetOne` applies. -/
theorem eventually_fredholmDet_airyTildeOp_eq {T a : ℝ} (hT : 0 < T) (ha : T + 1 ≤ a) :
    ∀ᶠ u in atTop, ∀ hu : 0 < u,
      HilbertSchmidt.fredholmDet (AiryConj.airyTildeOp u T a hT hu ha) 1
        = HilbertSchmidt.fredholmDetOne (AiryConj.airyTildeOp u T a hT hu ha)
          (AiryConj.isTraceClass_airyTildeOp hT hu ha) 1 := by
  filter_upwards [eventually_hsNorm_airyTildeOp_lt hT ha one_pos] with u hhs hu
  exact HilbertSchmidt.fredholmDet_eq_fredholmDetOne _ (by rw [norm_one, one_mul]; exact hhs hu)

/-- **Record 1 in exp-trace form**: `QRUnitBlockLaw`, stated with the
entire determinant, gives the exp-trace law
`ℙ(Y₀ > u) = 1 − det₁(I − Ã_{u,1,2})` eventually in `u`, by the disk agreement
`eventually_fredholmDet_airyTildeOp_eq` at `T = 1`, `a = 2`. -/
theorem QRUnitBlockLaw.law_detOne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} (h : QRUnitBlockLaw Y P) :
    ∀ᶠ u in atTop, ∀ hu : 0 < u,
      P.real {ω | Y 0 ω > u} = 1 - HilbertSchmidt.fredholmDetOne
        (AiryConj.airyTildeOp u 1 2 one_pos hu (by norm_num))
        (AiryConj.isTraceClass_airyTildeOp one_pos hu (by norm_num)) 1 := by
  filter_upwards [h.law, eventually_fredholmDet_airyTildeOp_eq one_pos
    (by norm_num : (1 : ℝ) + 1 ≤ 2)] with u hlaw hdet hu
  rw [hlaw hu, hdet hu]

/-- **The exp-trace form is equivalent, `T = 1`**: `QRUnitBlockLaw` (entire
determinant) holds iff the exp-trace statement
`∀ᶠ u, ∀ hu, ℙ(Y₀ > u) = 1 − det₁(I − Ã_{u,1,2})` holds. The two forms neither
strengthen nor weaken each other; stating the record with the entire determinant removes the
`det₁` fidelity sub-assumption from what the record means. -/
theorem QRUnitBlockLaw.iff_law_detOne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} :
    QRUnitBlockLaw Y P ↔ ∀ᶠ u in atTop, ∀ hu : 0 < u,
      P.real {ω | Y 0 ω > u} = 1 - HilbertSchmidt.fredholmDetOne
        (AiryConj.airyTildeOp u 1 2 one_pos hu (by norm_num))
        (AiryConj.isTraceClass_airyTildeOp one_pos hu (by norm_num)) 1 := by
  refine ⟨fun h => h.law_detOne, fun h => ⟨?_⟩⟩
  filter_upwards [h, eventually_fredholmDet_airyTildeOp_eq one_pos
    (by norm_num : (1 : ℝ) + 1 ≤ 2)] with u hlaw hdet hu
  rw [hlaw hu, hdet hu]

/-- **Re-weighting bridge, `T = 1`** (the paper's determinant form of the one-block tail): the
record `QRUnitBlockLaw`, stated at QR's weight `a = 2`, yields the paper's
form `ℙ(Y₀ > u) = 1 - det₁(I - Ã_{u,1})` at `a = √(2u)`, eventually in `u`.
The re-weighting is contrib `AiryConj.eventually_detOneAiryTilde_one_eq_weight_two`
(weight independence of every `tr(Ã_a^m)`, `AiryKernel/TraceWeight.lean`), valid
for `u ≥ 2`. -/
theorem QRUnitBlockLaw.detOne_form {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} (h : QRUnitBlockLaw Y P) :
    ∀ᶠ u in atTop, P.real {ω | Y 0 ω > u} = 1 - AiryConj.detOneAiryTilde u 1 := by
  filter_upwards [h.law_detOne, AiryConj.eventually_detOneAiryTilde_one_eq_weight_two,
    eventually_gt_atTop (0 : ℝ)] with u hlaw hdet hu
  rw [hlaw hu, hdet hu]

/-- **The re-weighted form is equivalent, `T = 1`**: `QRUnitBlockLaw` (QR's
weight `a = 2`) holds iff the re-weighted form `∀ᶠ u, ℙ(Y₀ > u) = 1 - detOneAiryTilde u 1`
(weight `√(2u)`) holds. The two forms neither strengthen nor weaken each other;
stating the record at QR's weight keeps the weight change out of the trusted statement. -/
theorem QRUnitBlockLaw.iff_detOne_form {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} :
    QRUnitBlockLaw Y P ↔
      ∀ᶠ u in atTop, P.real {ω | Y 0 ω > u} = 1 - AiryConj.detOneAiryTilde u 1 := by
  refine ⟨fun h => h.detOne_form, fun h => QRUnitBlockLaw.iff_law_detOne.mpr ?_⟩
  filter_upwards [h, AiryConj.eventually_detOneAiryTilde_one_eq_weight_two] with u hlaw hdet hu
  rw [hlaw, hdet hu]

/-! ### The discharge -/

/-- **`sharp_tail` from the QR unit-block law** (the paper's sharp one-block
tail, leading order at `T = 1`): if `ℙ(Y₀ > u)` is eventually
`1 - det(I - Ã_{u,1,2})` (`QRUnitBlockLaw`: the QR one-block law at QR's weight
`a = 2`), then `ℙ(Y₀ > u) / e^{-H(u)} → 1`.

Proof: `QRUnitBlockLaw.detOne_form` re-weights to the paper's determinant form at `a = √(2u)`;
then contrib (`AiryConj.piT_sub_traceLead_isLittleO`) at `T = 1` with
`π := 1 - det₁(I - Ã_{·,1})` gives `π - ρ - ρ/(4u) = o(ρ/u) = o(ρ)`; hence
`π/ρ = 1 + 1/(4u) + o(1) → 1`, and `e^{-H(u)} = ρ(u)` for `u > 0`. -/
theorem sharp_tail_of_QRUnitBlockLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} (h : QRUnitBlockLaw Y P) :
    Tendsto (fun u : ℝ => P.real {ω | Y 0 ω > u} / Real.exp (-airyH u)) atTop (𝓝 1) := by
  set piT : ℝ → ℝ := fun M => 1 - AiryConj.detOneAiryTilde M 1 with hpiT
  have hR8 := AiryConj.piT_sub_traceLead_isLittleO 1 one_pos piT (fun _ => rfl)
  -- `ρ(u)/u = O(ρ(u))`, so the two-term remainder is `o(ρ)`.
  have hO : (fun M : ℝ => AiryConj.rhoM M / M) =O[atTop] fun M => AiryConj.rhoM M := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with M hM
    rw [norm_div, one_mul]
    exact div_le_self (norm_nonneg _) (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; exact hM)
  have hrem : Tendsto (fun M => (piT M - AiryConj.traceLead M 1) / AiryConj.rhoM M)
      atTop (𝓝 0) := (hR8.trans_isBigO hO).tendsto_div_nhds_zero
  have hinv : Tendsto (fun M : ℝ => 1 / (4 * M)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  have hlim : Tendsto (fun M => 1 + 1 / (4 * M) +
      (piT M - AiryConj.traceLead M 1) / AiryConj.rhoM M) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hinv |>.add hrem
  refine hlim.congr' ?_
  filter_upwards [h.detOne_form, eventually_gt_atTop (0 : ℝ)] with u hlaw hu
  have hρ : AiryConj.rhoM u ≠ 0 := (AiryConj.rhoM_pos hu).ne'
  rw [hlaw, exp_neg_airyH_eq hu]
  simp only [hpiT, AiryConj.traceLead]
  field_simp
  ring

/-! ### Smart constructor and `_of_QR` headline corollaries -/

section OfQR

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (Y : ℕ → Ω → ℝ) (Y_meas : ∀ j, Measurable (Y j))
  (alpha : ℕ → ℝ) (alpha_nonneg : ∀ m, 0 ≤ alpha m)
  (mixC : ℝ) (mixC_pos : 0 < mixC) (mixc : ℝ) (mixc_pos : 0 < mixc)
  (alpha_bound : ∀ m, alpha m ≤ mixC * Real.exp (-mixc * ((m : ℝ) - 1) ^ 3))
  (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
  (stat_pair : ∀ (u : ℝ) (i d : ℕ),
    P {ω | Y i ω > u ∧ Y (i + d) ω > u} = P {ω | Y 0 ω > u ∧ Y d ω > u})
  (qr : QRUnitBlockLaw Y P)
  (touching : ∀ z : ℝ, Tendsto (fun N : ℕ =>
    (N : ℝ) * P.real {ω | Y 0 ω > gumbelU N z ∧ Y 1 ω > gumbelU N z}) atTop (𝓝 0))
  (mixing_tail : ∃ A : ℝ, 0 < A ∧ 1 < mixc * A ^ 3 ∧
    Tendsto (fun N : ℕ => (N : ℝ) * ∑' j : ℕ, alpha (qN A N + j)) atTop (𝓝 0))
  (separated : ∀ (z χ : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 →
    Tendsto (fun N : ℕ =>
      (N : ℝ) * ∑ j ∈ Finset.Icc 2 (mN χ z N),
        P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0))
  (mesoscopic : ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
    Tendsto (fun N : ℕ =>
      (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
        P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0))
  (decouple : ∀ (S T : Finset ℕ) (q : ℕ) (u : ℝ),
    (∀ s ∈ S, ∀ t ∈ T, s + q ≤ t) →
    |P.real ({ω | ∀ s ∈ S, Y s ω ≤ u} ∩ {ω | ∀ t ∈ T, Y t ω ≤ u}) -
      P.real {ω | ∀ s ∈ S, Y s ω ≤ u} * P.real {ω | ∀ t ∈ T, Y t ω ≤ u}|
      ≤ alpha q)
  (pair_mix : ∀ (u : ℝ) (j : ℕ),
    P.real {ω | Y 0 ω > u ∧ Y j ω > u} ≤ P.real {ω | Y 0 ω > u} ^ 2 + alpha j)

include Y_meas alpha_nonneg mixC_pos mixc_pos alpha_bound stat_marginal stat_pair qr
  touching mixing_tail separated mesoscopic decouple pair_mix

/-- Smart constructor for `Airy1BlockExtremes`: every field
except `sharp_tail` is supplied directly, and `sharp_tail` is discharged from
the QR unit-block law `QRUnitBlockLaw` ([QuastelRemenik2012, Theorem 4] at
QR's weight `a = 2`) by `sharp_tail_of_QRUnitBlockLaw`
(the paper's sharp one-block tail). -/
def Airy1BlockExtremes.ofQR : Airy1BlockExtremes P where
  Y := Y
  Y_meas := Y_meas
  alpha := alpha
  alpha_nonneg := alpha_nonneg
  mixC := mixC
  mixC_pos := mixC_pos
  mixc := mixc
  mixc_pos := mixc_pos
  alpha_bound := alpha_bound
  stat_marginal := stat_marginal
  stat_pair := stat_pair
  sharp_tail := sharp_tail_of_QRUnitBlockLaw qr
  touching := touching
  mixing_tail := mixing_tail
  separated := separated
  mesoscopic := mesoscopic
  decouple := decouple
  pair_mix := pair_mix

/-- **Conditional Gumbel limit, integer-block form, with `sharp_tail`
discharged** (the paper's main theorem (Theorem 1.1); block form of
`Airy1BlockExtremes.gumbel_limit`): the hypothesis list carries
`QRUnitBlockLaw` ([QuastelRemenik2012, Theorem 4] at QR's weight `a = 2`)
in place of `sharp_tail`. -/
theorem Airy1BlockExtremes.gumbel_limit_of_QR (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ j ∈ Finset.range N, Y j ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  (Airy1BlockExtremes.ofQR Y Y_meas alpha alpha_nonneg mixC mixC_pos mixc mixc_pos
    alpha_bound stat_marginal stat_pair qr touching mixing_tail separated mesoscopic
    decouple pair_mix).gumbel_limit z

/-- **Conditional Gumbel limit, continuum integer-length form, with
`sharp_tail` discharged** (the paper's main theorem (Theorem 1.1); corollary of
`Airy1ContinuousMax.gumbel_limit_continuum`): `ℙ(M_N ≤ u_N(z)) → e^{-e^{-z}}`,
with `QRUnitBlockLaw` in place of `sharp_tail`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_QR (C : Airy1ContinuousMax P)
    (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum (Airy1BlockExtremes.ofQR Y Y_meas alpha alpha_nonneg mixC
    mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr touching mixing_tail
    separated mesoscopic decouple pair_mix) hY z

/-- **Normalized integer-length Gumbel limit, with `sharp_tail` discharged**
(the paper's main theorem (Theorem 1.1); corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_normalized`): `(M_N - a_N)/b_N`
converges in law to the standard Gumbel distribution, with `QRUnitBlockLaw`
in place of `sharp_tail`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_normalized_of_QR
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ),
      (C.A x ω - gumbelA N) / gumbelB N ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_normalized (Airy1BlockExtremes.ofQR Y Y_meas alpha
    alpha_nonneg mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr
    touching mixing_tail separated mesoscopic decouple pair_mix) hY z

/-- **Perturbed-level integer-length Gumbel limit, with `sharp_tail`
discharged** (the perturbed-level step of the real-length extension of the paper's
main theorem (Theorem 1.1); corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto`), with `QRUnitBlockLaw`
in place of `sharp_tail`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto_of_QR
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) (w : ℕ → ℝ)
    (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N (w N)})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_of_tendsto (Airy1BlockExtremes.ofQR Y Y_meas alpha
    alpha_nonneg mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr
    touching mixing_tail separated mesoscopic decouple pair_mix) hY z w hw

/-- **Real-length conditional Gumbel limit, with `sharp_tail` discharged**
(the paper's main theorem (Theorem 1.1), real `T → ∞`; corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_real`):
`ℙ(M_T ≤ u_T(z)) → e^{-e^{-z}}`, with `QRUnitBlockLaw` in
place of `sharp_tail`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_of_QR
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun T : ℝ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T, C.A x ω ≤ gumbelUR T z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_real (Airy1BlockExtremes.ofQR Y Y_meas alpha alpha_nonneg
    mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr touching
    mixing_tail separated mesoscopic decouple pair_mix) hY z

/-- **The paper's headline, with `sharp_tail` discharged** (the paper's
main theorem (Theorem 1.1), normalized real-length shape; corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_real_normalized`): `(M_T - a_T)/b_T`
converges in law to the standard Gumbel distribution as `T → ∞`, with
`QRUnitBlockLaw` in place of `sharp_tail`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QR
    (C : Airy1ContinuousMax P) (hY : Y = C.Y) (z : ℝ) :
    Tendsto (fun T : ℝ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (C.A x ω - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_real_normalized (Airy1BlockExtremes.ofQR Y Y_meas alpha
    alpha_nonneg mixC mixC_pos mixc mixc_pos alpha_bound stat_marginal stat_pair qr
    touching mixing_tail separated mesoscopic decouple pair_mix) hY z

end OfQR

end Airy1Gumbel
