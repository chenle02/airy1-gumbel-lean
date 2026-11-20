/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoInterval.SectorRR
import Airy1GumbelContrib.TwoInterval.SectorFR
import Airy1GumbelContrib.TwoInterval.SectorRF
import Airy1GumbelContrib.TwoInterval.SectorFF
import Airy1GumbelContrib.TwoInterval.TwoIntervalDetRem

/-!
# The total trace bound of the paper's separated-block estimate

Part of the two-interval layer (`TwoInterval/`) of the Airy1–Gumbel contrib library: the
trace step of the paper's separated-block estimate, which combines the four sector bounds into

  `|Tr C̃_r| ≤ C_χ (1+r)^{1/2} e^{−J_M(r)}`,  `1 ≤ r ≤ χa`

(the paper's total trace bound) for the proved operator trace `trace (kernelOperator hcr)` of
the conjugated interaction kernel `crKerT a M r`, in the paper's existential-constant form,
uniformly for `1 ≤ r ≤ χ√(2M)`, `0 < χ < 1`, `M ≥ M₀(χ)`.

This is a thin assembly module: no sector estimate and no trace identity is
re-proved here.

## Correspondence with the paper

* The paper combines its two RR-sector bounds, its FR- and RF-sector bounds, its FF-sector
  bound, and `Tr C̃_r = Tr C_r` into the total trace bound.
* The five inputs and their Lean counterparts:
  - the two RR-sector bounds: the two terms of
    `trSectorRR_abs_le` (SectorRR.lean), `C₁ e^{−J} + C₂ e^{−c₂ M²}`;
  - the FR-sector bound: `abs_trSectorFR_le_absorbed` (SectorFR.lean);
  - the RF-sector bound: `abs_trSectorRF_le_absorbed` (SectorRF.lean);
  - the FF-sector bound: `trSectorFF_abs_le` (SectorFF.lean).
* `Tr C̃_r = Tr C_r` and the four-sector split: the proved
  identity `trace_crKerT_eq_sectors` (TwoIntervalTrace.lean), whose
  `Tr C̃_r = Tr C_r` half is the unconditional `trCrWeighted_eq_trCr`.
* The absorption principle `J_M(r) = O_χ(a³) = o(M²)`:
  `saddleJ_le_rpow` (FRExponents.lean).
* The consumer: the main-package assembly of the separated-block estimate combines the
  discharged headline below with `joint_detOne_comb_abs_le`
  (TwoIntervalDetRem.lean) by the triangle inequality
  `|detComb| ≤ |detComb − Tr C̃_r| + |Tr C̃_r|`; the `(1+r)^{1/2}` factor is
  swallowed there by `(1+r)^K` ("enlarging `K` if necessary").

## The two forms of the headline

* **`MemLp`-conditional form** (`abs_sector_sum_le`, `abs_trace_crKerT_le`,
  `abs_trCr_le`): general weight parameter `a`, with the hypotheses of
  `trace_crKerT_eq_sectors`,
  `hA : MemLp (aRKer a M r) 2 (volume.prod volume)` and
  `hW : MemLp (wSKer (2 + r) a) 2 (volume.prod volume)` (and, at operator level,
  the kernel binder `hcr : MemLp (crKerT a M r) 2 (volume.prod volume)`), range
  `r ∈ Set.Icc 1 (χ * √(2M))` — exactly the interface of the proved sector bounds
  and of `trace_crKerT_eq_sectors`:
  `|trace (kernelOperator hcr)| ≤ C * (1+r)^(1/2) * exp (−saddleJ M r)`.
* **Discharged form** (`abs_trace_crKerT_le_discharged`): at `a = √(2M)`, the
  hypotheses `hA`/`hW` are discharged by `memLp_aRKer` / `memLp_wSKer`,
  with the admissibility `r + 3 ≤ √(2M)`, `2 ≤ √(2M)`, `1 ≤ M` of the paper's joint-law
  lemma supplied by the proved `exists_admissible_M₀`.  The kernel binder
  `hcr : MemLp (crKerT (√(2M)) M r) 2 (volume.prod volume)` is kept as an
  explicit trailing binder, matching `joint_detOne_comb_abs_le` so the
  main-package triangle step shares one proof term.

## Presentation choices

The Lean statement follows the paper's total trace bound; the following are presentation
choices.

(i) **Existential constants with explicit thresholds**: `M₀` collects the four
    sector thresholds, the RR absorption threshold `8 (C'/c₂)²` of
    `exp_neg_mul_sq_le_exp_neg_saddleJ`, and (discharged form) the
    `9/(2(1−χ)²)` of `exists_admissible_M₀`.
(ii) **RR's internal `e^{−c₂M²}` scale** (stated as `c₂ * M^2`, the paper's
    `c_χ M²`, not the `(2M)²` convention of FR/RF/FF) is absorbed into
    `e^{−J}` here, by the argument `J = O_χ((2M)^{3/2})`, which the paper
    applies implicitly when combining the sectors.
(iii) **Sector order** `((RR + RF) + FR) + FF` follows
    `trace_crKerT_eq_sectors`, not the paper's listing order (RR, FR, RF, FF);
    the RR± split lives inside `trSectorRR_abs_le`.
(iv) **`(1+r)^{1/2}` upgrade of RR and FF**: their Lean bounds carry no
    `(1+r)^{1/2}` factor; they are upgraded by `1 ≤ (1+r)^{1/2}` (`r ≥ 1`).  The
    factor in the headline is inherited from FR/RF alone, as in the paper.
(v) **Unsigned constants normalized**: RR's `C₁, C₂` and FF's `C` carry no sign
    conjunct and are replaced by `max · 0` before summation; `0 < C` of the
    headline comes from FR's `0 < C`.
(vi) **`hcr` binder convention** in the discharged form (the library's
    statement-presentation convention); `hadr` is derived internally, not
    assumed.
(vii) **`r : ℝ`** (contrib convention; the paper takes `r ∈ ℕ`).
(viii) **`abs_trCr_le` is an additive extra**: the integral-level form of the
    bound for the four-fold integral `trCr M r`, documenting the
    `Tr C̃_r = Tr C_r` half at the estimate level.
-/

namespace AiryTwoInt

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal InnerProduct InnerProductSpace
open HilbertSchmidt
open AiryConj

/-- **The RR absorption helper** (the principle `J_M(r) = O_χ(a³)`
applied to the paper's RR scale `c_χ M²`): for any `c > 0`,
`e^{−c M²} ≤ e^{−J_M(r)}` uniformly for `1 ≤ r ≤ χ√(2M)` once `M` is large.
With `u = √(2M)`, `saddleJ_le_rpow` gives `J_M(r) ≤ C' u³`, while `c M² = c u⁴/4`;
the threshold is `M ≥ max 1 (8 (max C' 0 / c)²)`. -/
theorem exp_neg_mul_sq_le_exp_neg_saddleJ {χ : ℝ} (hχ0 : 0 < χ) {c : ℝ} (hc : 0 < c) :
    ∃ M₁ : ℝ, ∀ {M r : ℝ}, M₁ ≤ M → 1 ≤ r → r ≤ χ * Real.sqrt (2*M) →
      Real.exp (-c * M^2) ≤ Real.exp (-saddleJ M r) := by
  obtain ⟨C', hC'⟩ := saddleJ_le_rpow hχ0
  set K : ℝ := max C' 0 with hK
  have hK0 : (0:ℝ) ≤ K := le_max_right _ _
  refine ⟨max 1 (8 * (K / c)^2), ?_⟩
  intro M r hM hr hradm
  have hM1 : (1:ℝ) ≤ M := le_trans (le_max_left _ _) hM
  have hMbig : 8 * (K / c)^2 ≤ M := le_trans (le_max_right _ _) hM
  have h2M : (0:ℝ) ≤ 2*M := by linarith
  set u := Real.sqrt (2*M) with hu
  have hu0 : (0:ℝ) ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = 2*M := Real.sq_sqrt h2M
  have ha32 : (2*M)^(3/2 : ℝ) = u^3 := by
    rw [← hu2, ← Real.rpow_natCast u 2, ← Real.rpow_mul hu0,
      show ((2:ℕ):ℝ)*(3/2) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  -- `4K/c ≤ u`, i.e. `K ≤ c u / 4`
  have hKc : 4 * K / c ≤ u := by
    rw [Real.le_sqrt (div_nonneg (by positivity) hc.le) h2M]
    have : (4 * K / c)^2 = 16 * (K / c)^2 := by
      field_simp
      ring
    rw [this]
    nlinarith [hMbig, sq_nonneg (K / c)]
  have hKle : K ≤ c * u / 4 := by
    have h := mul_le_mul_of_nonneg_left hKc (by positivity : (0:ℝ) ≤ c / 4)
    calc K = c / 4 * (4 * K / c) := by field_simp
      _ ≤ c / 4 * u := h
      _ = c * u / 4 := by ring
  have hkey : saddleJ M r ≤ c * M^2 := by
    calc saddleJ M r ≤ C' * (2*M)^(3/2 : ℝ) := hC' hM1 hr hradm
      _ ≤ K * (2*M)^(3/2 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg h2M _)
      _ = K * u^3 := by rw [ha32]
      _ ≤ (c * u / 4) * u^3 := mul_le_mul_of_nonneg_right hKle (pow_nonneg hu0 3)
      _ = c * (u^2)^2 / 4 := by ring
      _ = c * M^2 := by rw [hu2]; ring
  apply Real.exp_le_exp.mpr
  rw [neg_mul]
  exact neg_le_neg hkey

/-- **The sector-sum core** (`MemLp`-conditional form):
the four proved sector bounds — the two RR-sector bounds via
`trSectorRR_abs_le`, the RF-, FR- and FF-sector bounds — combine by the triangle
inequality, in the order `((RR + RF) + FR) + FF` of `trace_crKerT_eq_sectors`, into
`|Σ sectors| ≤ C_χ (1+r)^{1/2} e^{−J_M(r)}`.  RR's `e^{−c₂M²}` term is absorbed
by `exp_neg_mul_sq_le_exp_neg_saddleJ`; RR/FF are upgraded by
`1 ≤ (1+r)^{1/2}`; unsigned constants are normalized by `max · 0`. -/
theorem abs_sector_sum_le {χ : ℝ} (hχ0 : 0 < χ) (hχ : χ < 1) :
    ∃ C M₀ : ℝ, 0 < C ∧ ∀ (a M r : ℝ), M₀ ≤ M →
      r ∈ Set.Icc 1 (χ * Real.sqrt (2*M)) →
      MemLp (aRKer a M r) 2 (volume.prod volume) →
      MemLp (wSKer (2 + r) a) 2 (volume.prod volume) →
      |trSectorRR M r + trSectorRF M r + trSectorFR M r + trSectorFF M r|
        ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
  obtain ⟨C₁, C₂, c₂, MRR, hc₂, hRR⟩ := trSectorRR_abs_le hχ0 hχ
  obtain ⟨CRF, MRF, hCRF, hRF⟩ := abs_trSectorRF_le_absorbed hχ0 hχ
  obtain ⟨CFR, MFR, hCFR, hFR⟩ := abs_trSectorFR_le_absorbed hχ0 hχ
  obtain ⟨CFF, MFF, hFF⟩ := trSectorFF_abs_le hχ0 hχ
  obtain ⟨M₁, hM₁⟩ := exp_neg_mul_sq_le_exp_neg_saddleJ hχ0 hc₂
  set D₁ : ℝ := max C₁ 0 with hD₁
  set D₂ : ℝ := max C₂ 0 with hD₂
  set DFF : ℝ := max CFF 0 with hDFF
  have hD₁0 : (0:ℝ) ≤ D₁ := le_max_right _ _
  have hD₂0 : (0:ℝ) ≤ D₂ := le_max_right _ _
  have hDFF0 : (0:ℝ) ≤ DFF := le_max_right _ _
  refine ⟨D₁ + D₂ + CRF + CFR + DFF, max (max MRR MFR) (max MRF (max MFF M₁)),
    by positivity, ?_⟩
  intro a M r hM hr hA hW
  have hMRR : MRR ≤ M := le_trans (le_max_left _ _ |>.trans (le_max_left _ _)) hM
  have hMFR : MFR ≤ M := le_trans (le_max_right _ _ |>.trans (le_max_left _ _)) hM
  have hMRF : MRF ≤ M := le_trans (le_max_left _ _ |>.trans (le_max_right _ _)) hM
  have hMFF : MFF ≤ M :=
    le_trans ((le_max_left _ _).trans (le_max_right _ _) |>.trans (le_max_right _ _)) hM
  have hMM₁ : M₁ ≤ M :=
    le_trans ((le_max_right _ _).trans (le_max_right _ _) |>.trans (le_max_right _ _)) hM
  set E : ℝ := Real.exp (-saddleJ M r) with hE
  set P : ℝ := (1+r)^(1/2 : ℝ) with hP
  have hE0 : (0:ℝ) ≤ E := (Real.exp_pos _).le
  have hP1 : (1:ℝ) ≤ P :=
    Real.one_le_rpow (by linarith [hr.1] : (1:ℝ) ≤ 1 + r) (by norm_num : (0:ℝ) ≤ 1/2)
  have hEP : E ≤ P * E := by
    calc E = 1 * E := (one_mul _).symm
      _ ≤ P * E := mul_le_mul_of_nonneg_right hP1 hE0
  -- the four sector bounds, normalized to `· * (P * E)`
  have hRR' : |trSectorRR M r| ≤ (D₁ + D₂) * (P * E) := by
    have h := hRR a M r hMRR hr hA hW
    have habs : Real.exp (-c₂ * M^2) ≤ E := hM₁ hMM₁ hr.1 hr.2
    calc |trSectorRR M r|
        ≤ C₁ * E + C₂ * Real.exp (-c₂ * M^2) := h
      _ ≤ D₁ * E + D₂ * Real.exp (-c₂ * M^2) :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0)
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      _ ≤ D₁ * E + D₂ * E := add_le_add_right (mul_le_mul_of_nonneg_left habs hD₂0) _
      _ = (D₁ + D₂) * E := by ring
      _ ≤ (D₁ + D₂) * (P * E) := mul_le_mul_of_nonneg_left hEP (add_nonneg hD₁0 hD₂0)
  have hRF' : |trSectorRF M r| ≤ CRF * (P * E) := by
    have h := hRF hMRF hr.1 hr.2 hA hW
    calc |trSectorRF M r| ≤ CRF * P * E := h
      _ = CRF * (P * E) := by ring
  have hFR' : |trSectorFR M r| ≤ CFR * (P * E) := by
    have h := hFR hMFR hr.1 hr.2 hA hW
    calc |trSectorFR M r| ≤ CFR * P * E := h
      _ = CFR * (P * E) := by ring
  have hFF' : |trSectorFF M r| ≤ DFF * (P * E) := by
    have h := hFF a M r hMFF hr hA hW
    calc |trSectorFF M r| ≤ CFF * E := h
      _ ≤ DFF * E := mul_le_mul_of_nonneg_right (le_max_left _ _) hE0
      _ ≤ DFF * (P * E) := mul_le_mul_of_nonneg_left hEP hDFF0
  -- the triangle chain along `((RR + RF) + FR) + FF`
  calc |trSectorRR M r + trSectorRF M r + trSectorFR M r + trSectorFF M r|
      ≤ |trSectorRR M r + trSectorRF M r + trSectorFR M r| + |trSectorFF M r| :=
        abs_add_le _ _
    _ ≤ (|trSectorRR M r + trSectorRF M r| + |trSectorFR M r|) + |trSectorFF M r| :=
        add_le_add_left (abs_add_le _ _) _
    _ ≤ ((|trSectorRR M r| + |trSectorRF M r|) + |trSectorFR M r|) + |trSectorFF M r| :=
        add_le_add_left (add_le_add_left (abs_add_le _ _) _) _
    _ ≤ (((D₁ + D₂) * (P * E) + CRF * (P * E)) + CFR * (P * E)) + DFF * (P * E) :=
        add_le_add (add_le_add (add_le_add hRR' hRF') hFR') hFF'
    _ = (D₁ + D₂ + CRF + CFR + DFF) * P * E := by ring

/-- **The total trace bound, `MemLp`-conditional form** (the paper's total trace
bound): `|Tr C̃_r| ≤ C_χ (1+r)^{1/2} e^{−J_M(r)}` for
`1 ≤ r ≤ χ√(2M)`, `M ≥ M₀(χ)`, at general weight parameter `a` under the
hypotheses `hA`/`hW` and the kernel binder `hcr`.  One rewrite by the proved
`trace_crKerT_eq_sectors` (`Tr C̃_r = Tr C_r` and the four-sector split),
then `abs_sector_sum_le`. -/
theorem abs_trace_crKerT_le {χ : ℝ} (hχ0 : 0 < χ) (hχ : χ < 1) :
    ∃ C M₀ : ℝ, 0 < C ∧ ∀ (a M r : ℝ), M₀ ≤ M →
      r ∈ Set.Icc 1 (χ * Real.sqrt (2*M)) →
      (hA : MemLp (aRKer a M r) 2 (volume.prod volume)) →
      (hW : MemLp (wSKer (2 + r) a) 2 (volume.prod volume)) →
      (hcr : MemLp (crKerT a M r) 2 (volume.prod volume)) →
      |trace (kernelOperator hcr)|
        ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
  obtain ⟨C, M₀, hC, H⟩ := abs_sector_sum_le hχ0 hχ
  refine ⟨C, M₀, hC, fun a M r hM hr hA hW hcr => ?_⟩
  rw [trace_crKerT_eq_sectors (lt_of_lt_of_le one_pos hr.1) a M hA hW hcr]
  exact H a M r hM hr hA hW

/-- **The total trace bound, discharged form** (the paper's total trace bound with
`a = √(2M)`): the hypotheses `hA`/`hW` are
discharged by `memLp_aRKer` (`2 ≤ a`) and `memLp_wSKer` (`r + 3 ≤ a`),
with the admissibility of the paper's joint-law lemma supplied by the proved
`exists_admissible_M₀`.  The kernel binder `hcr` is kept as an explicit trailing
binder, matching `joint_detOne_comb_abs_le` (TwoIntervalDetRem.lean) for the
main-package triangle step. -/
theorem abs_trace_crKerT_le_discharged {χ : ℝ} (hχ0 : 0 < χ) (hχ : χ < 1) :
    ∃ C M₀ : ℝ, 0 < C ∧ ∀ {M r : ℝ}, M₀ ≤ M → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      (hcr : MemLp (crKerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume)) →
      |trace (kernelOperator hcr)|
        ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
  obtain ⟨C, M₀, hC, hD3⟩ := abs_trace_crKerT_le hχ0 hχ
  obtain ⟨Ma, hMa⟩ := exists_admissible_M₀ hχ0 hχ
  refine ⟨C, max M₀ Ma, hC, ?_⟩
  intro M r hM hr hrM hcr
  have hM0 : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hMa' : Ma ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hadr, ha2, hM1⟩ := hMa M r hMa' hr hrM
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le one_pos hr
  have hMpos : (0:ℝ) < M := lt_of_lt_of_le one_pos hM1
  exact hD3 (Real.sqrt (2*M)) M r hM0 ⟨hr, hrM⟩
    (memLp_aRKer hr0 hMpos ha2) (memLp_wSKer hr0 hadr) hcr

/-- **The integral-level form** (the four-fold integral `Tr C_r`,
bounded as in the paper's total trace bound): `trCr_sum_sectors`
(the four-sector split) and `abs_sector_sum_le`.  Documents
the `Tr C̃_r = Tr C_r` half at the estimate level; needs no `hcr`. -/
theorem abs_trCr_le {χ : ℝ} (hχ0 : 0 < χ) (hχ : χ < 1) :
    ∃ C M₀ : ℝ, 0 < C ∧ ∀ (a M r : ℝ), M₀ ≤ M →
      r ∈ Set.Icc 1 (χ * Real.sqrt (2*M)) →
      MemLp (aRKer a M r) 2 (volume.prod volume) →
      MemLp (wSKer (2 + r) a) 2 (volume.prod volume) →
      |trCr M r| ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
  obtain ⟨C, M₀, hC, H⟩ := abs_sector_sum_le hχ0 hχ
  refine ⟨C, M₀, hC, fun a M r hM hr hA hW => ?_⟩
  rw [trCr_sum_sectors (lt_of_lt_of_le one_pos hr.1) a M hA hW]
  exact H a M r hM hr hA hW

end AiryTwoInt
