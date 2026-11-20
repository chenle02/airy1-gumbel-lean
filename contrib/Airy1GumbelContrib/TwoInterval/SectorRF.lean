/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoInterval.SectorFR
import Airy1GumbelContrib.TwoInterval.SectorRR

/-!
# The RF sector bound

The RF sector of the two-interval trace, one of the four sector bounds in the trace step
of the paper's separated-block estimate:

  `|Tr C_r^{RF}| ≤ C_χ (1+r)^{1/2} e^{−J_M(r)}`

for the sector trace integral `trSectorRF M r` (= `trSector (qRKerTwo M)
(qFKerTwo M) r`, see `TwoIntervalTrace.lean`), in existential-constant form,
uniformly for `1 ≤ r ≤ χ√(2M)`, `0 < χ < 1`, `M ≥ M₀(χ)`.

## Mathematical setting

* Kernel definitions: `Q^R(x, y) = 1_{x,y≤M} p₁(2M−x−y)`
  (`qRKerTwo`) and `Q^F(x, y) = 1_{x>M ∨ y>M} p₁(x−y)` (`qFKerTwo`); the sector
  operator `C_r^{αβ} := Q^α P_r Q^β P_{−S} B₀`; the four-sector split
  `C_r = C_r^{RR} + C_r^{RF} + C_r^{FR} + C_r^{FF}` (proved as
  `trCr_sum_sectors`); the generic sector trace integrand
  `Q^α(x,y) p_r(y−z) Q^β(z,w) (P_{−S}B₀)(w,x)` (`sectorIntegrand`).
* The input bound (the FR-sector bound):
  `|Tr C_r^{FR}| ≤ C_χ (1+r)^{1/2} e^{−J_M(r)}` — proved as
  `abs_trSectorFR_le_absorbed` (SectorFR.lean).
* The RF argument: under `(x,y,z,w) ↦ (w,z,y,x)` the two symmetric `Q` kernels are
  interchanged, `p_r` is even, and the Airy factor is unchanged, so
  `Tr C_r^{RF} = Tr C_r^{FR}` — three factor-wise symmetries plus
  measure invariance give the trace EQUALITY `trSectorRF_eq_trSectorFR`.
* The RF bound:
  `|Tr C_r^{RF}| ≤ C_χ (1+r)^{1/2} e^{−J_M(r)}`.  The `(1+r)^{1/2}` factor is
  inherited from the FR bound (contrast the FF bound, which carries
  no such factor).
* The assembly of the four sector bounds is in `TwoIntervalTraceBound.lean`,
  not in this module.

## The involution as a pair of swaps

The 4-D reversal `(x,y,z,w) ↦ (w,z,y,x)`, expressed in the Lean
`trSector` nesting order `(x, w, y, z)` (x outermost, z innermost, the
Tonelli order of `TwoIntervalTrace`), IS the independent pair-of-swaps
`(x,w,y,z) ↦ (w,x,z,y)`: swap the outer `(x,w)` pair and swap the inner
`(y,z)` pair.  The inner swap is the fully discharged
`sectorIntegrand_yz_swap` (SectorFR.lean, pointwise in `(x, w)`, unconditional
given `0 < r`); the outer swap is ONE application of
`MeasureTheory.integral_integral_swap` whose sole Tonelli input — product
integrability of the `(x,w)`-level inner function — is dominated pointwise by
the dominator `qPrQKer M r (x,w) * |bAiryKer (2+r) (w,x)|` of `TwoIntervalTrace`
(`sectorInnerW_abs_le`), whose product integrability under hA/hW is proved there
(`integrable_uncurry_qPrQKer_mul_abs_bAiryKer`), transported across `Prod.swap`
by `Measure.measurePreserving_swap.integrable_comp_of_integrable`
(`integrable_sectorInnerFR_comp_swap`, the only new measure theory here).  No
FR piece estimate is re-proved: the RF bound is FR's own bound with the trace
equality rewritten in.

## The `MemLp`-conditional interface

The trace equality `trSectorRF_eq_trSectorFR` and the RF bounds carry the
`MemLp` hypotheses `hA : MemLp (aRKer a M r) 2 (volume.prod volume)` and
`hW : MemLp (wSKer (2 + r) a) 2 (volume.prod volume)` — properties of the
*weight* kernels only, hence sector-blind and identical in shape to the FR
bound's; they are consumed exactly once, for the outer swap's product
integrability.  The fully discharged corollary
`abs_trSectorRF_le_absorbed_discharged` discharges them at `a = √(2M)` by
`memLp_aRKer`/`memLp_wSKer` (TwoIntervalMembership.lean), with the same discharge
argument as in SectorFR (`M₀`-padding included).

## Implementation notes

(i) **The involution implementation**: the 4-D reversal is
    implemented as the pointwise identity `sectorIntegrand_RF_eq_FR_involution`
    plus two independent pair-swaps in the Lean nesting order — the inner
    `(y,z)` swap and one outer `(x,w)` swap.  Identical content: in
    `(x,w,y,z)` coordinates the reversal IS `(x,w,y,z) ↦ (w,x,z,y)`.  No 4-D
    Bochner-involution API, no Jacobian/`|det|` lemma, no `(α,β)`
    exponent-level swap (unlike FF, RF is never reduced to exponent
    coordinates).
(ii) **The hA/hW interface on the equality**: the trace equality
    `Tr C_r^{RF} = Tr C_r^{FR}` is proved here under the `MemLp`
    hypotheses, which provide the Tonelli justification
    (needed once, for the outer swap's product integrability).
    Same shape as `trSectorFR_eq_frI1_add_frI2` (SectorFR.lean) and
    `trace_crKerT_eq_sectors` (TwoIntervalTrace.lean).
(iii) **Constants pass through unchanged:** the RF bounds reuse FR's
    existential `C, c, M₀` literally (the trace equality makes them serve
    unchanged); no new χ-analysis, no new threshold.
(iv) **Additional forms:** besides the absorbed bound, the two-term form
    `abs_trSectorRF_le` (mirroring `abs_trSectorFR_le`)
    and the fully discharged `abs_trSectorRF_le_absorbed_discharged` are provided.
-/

namespace AiryTwoInt

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal
open AiryConj

/-! ### The factor symmetries (kernel definitions) -/

/-- **Factor symmetry** (the two symmetric `Q` kernels are interchanged): the
reflected kernel `Q^R(x, y) = 1_{x,y≤M} p₁(2M−x−y)` is symmetric in
its two arguments — the region `(-∞, M] × (-∞, M]` is swap-invariant and
`2M − y − x = 2M − x − y`. -/
theorem qRKerTwo_symm (M : ℝ) (p : ℝ × ℝ) : qRKerTwo M (p.2, p.1) = qRKerTwo M p := by
  obtain ⟨x, y⟩ := p
  show qRKerTwo M (y, x) = qRKerTwo M (x, y)
  unfold qRKerTwo
  by_cases h : x ≤ M ∧ y ≤ M
  · rw [Set.indicator_of_mem (show (y, x) ∈ Set.Iic M ×ˢ Set.Iic M from
        Set.mem_prod.mpr ⟨h.2, h.1⟩),
      Set.indicator_of_mem (show (x, y) ∈ Set.Iic M ×ˢ Set.Iic M from Set.mem_prod.mpr h)]
    show heatKernel 1 (2 * M - y - x) = heatKernel 1 (2 * M - x - y)
    congr 1
    ring
  · rw [Set.indicator_of_notMem (show (y, x) ∉ Set.Iic M ×ˢ Set.Iic M from
        fun hc => h ⟨(Set.mem_prod.mp hc).2, (Set.mem_prod.mp hc).1⟩),
      Set.indicator_of_notMem (show (x, y) ∉ Set.Iic M ×ˢ Set.Iic M from
        fun hc => h (Set.mem_prod.mp hc))]

/-- **Factor symmetry** (the two symmetric `Q` kernels are interchanged): the free
kernel `Q^F(x, y) = 1_{x>M ∨ y>M} p₁(x−y)` is symmetric in its two
arguments — the region `{x > M ∨ y > M}` is swap-invariant and
`p₁(y − x) = p₁(−(x − y)) = p₁(x − y)` since `p₁` is even (`heatKernel_even`). -/
theorem qFKerTwo_symm (M : ℝ) (p : ℝ × ℝ) : qFKerTwo M (p.2, p.1) = qFKerTwo M p := by
  obtain ⟨x, y⟩ := p
  show qFKerTwo M (y, x) = qFKerTwo M (x, y)
  unfold qFKerTwo
  by_cases h : M < x ∨ M < y
  · rw [Set.indicator_of_mem (show (y, x) ∈ {p : ℝ × ℝ | M < p.1 ∨ M < p.2} from h.symm),
      Set.indicator_of_mem (show (x, y) ∈ {p : ℝ × ℝ | M < p.1 ∨ M < p.2} from h)]
    show heatKernel 1 (y - x) = heatKernel 1 (x - y)
    rw [show y - x = -(x - y) by ring, heatKernel_even]
  · rw [Set.indicator_of_notMem (show (y, x) ∉ {p : ℝ × ℝ | M < p.1 ∨ M < p.2} from
        fun hc => h hc.symm),
      Set.indicator_of_notMem (show (x, y) ∉ {p : ℝ × ℝ | M < p.1 ∨ M < p.2} from h)]

/-- **Factor symmetry** (the Airy factor is unchanged): the Airy factor
`(P_{−S}B₀)(w, x) = g_S(w + x)` (`bAiryKer`) is symmetric in its two
arguments by `add_comm` alone. -/
theorem bAiryKer_symm (S : ℝ) (p : ℝ × ℝ) : bAiryKer S (p.2, p.1) = bAiryKer S p := by
  show backwardAiry S (p.2 + p.1) = backwardAiry S (p.1 + p.2)
  rw [add_comm p.2 p.1]

/-- **Domination** (the hypothesis of the SectorFR inner swap, for `Q^F`):
`|Q^F| ≤ p₁` pointwise, from the sector domination `|Q^F| ≤ Q`
(`qFKerTwo_abs_le_qKerTwo`) and `Q ≤ p₁` (`qKerTwo_le`).  Only the
`D₁`/`D₂` piece versions are proved in SectorFR (`qF1KerTwo_abs_le_heatKernel`,
`qF2KerTwo_abs_le_heatKernel`). -/
theorem qFKerTwo_abs_le_heatKernel (M : ℝ) (p : ℝ × ℝ) :
    |qFKerTwo M p| ≤ heatKernel 1 (p.1 - p.2) :=
  (qFKerTwo_abs_le_qKerTwo M p).trans (qKerTwo_le M p)

/-! ### The pointwise involution identity -/

/-- **Involution** (factor-by-factor): the RF integrand at `(x, y, z, w)` equals
the FR integrand at the reversed `(w, z, y, x)` — `Q^R(x,y) = Q^R(y,x)`,
`p_r(y−z) = p_r(z−y)`, `Q^F(z,w) = Q^F(w,z)`, `g_S(w+x) = g_S(x+w)` by the factor symmetries and
`heatKernel_even`.  Unconditional, no integrability. -/
theorem sectorIntegrand_RF_eq_FR_involution (M r : ℝ) (x y z w : ℝ) :
    sectorIntegrand (qRKerTwo M) (qFKerTwo M) r x y z w
      = sectorIntegrand (qFKerTwo M) (qRKerTwo M) r w z y x := by
  have hqR : qRKerTwo M (x, y) = qRKerTwo M (y, x) := (qRKerTwo_symm M (x, y)).symm
  have hqF : qFKerTwo M (w, z) = qFKerTwo M (z, w) := (qFKerTwo_symm M (w, z)).symm
  have hb : bAiryKer (2 + r) (w, x) = bAiryKer (2 + r) (x, w) :=
    (bAiryKer_symm (2 + r) (w, x)).symm
  have hp : heatKernel r (z - y) = heatKernel r (y - z) := by
    rw [show z - y = -(y - z) by ring, heatKernel_even]
  unfold sectorIntegrand
  rw [hqR, hqF, hb, hp]
  ring

/-! ### The trace equality `Tr C_r^{RF} = Tr C_r^{FR}` -/

/-- **Outer-swap integrability** (the Tonelli input for the outer `(x, w)` swap, the
only new measure theory of this module): the `(x, w)`-level FR inner function with the
arguments swapped is product-integrable.  The pointwise domination is
`sectorInnerW_abs_le` at `(w, x)`; the dominator
`(x, w) ↦ qPrQKer M r (w, x) * |bAiryKer (2+r) (x, w)|` is the `TwoIntervalTrace`
dominator (`integrable_uncurry_qPrQKer_mul_abs_bAiryKer`'s Tonelli close)
transported across `Prod.swap` by
`Measure.measurePreserving_swap.integrable_comp_of_integrable`; the
measurability is SectorRR's `measurable_uncurry_sectorInnerW` composed with
`measurable_swap`. -/
theorem integrable_sectorInnerFR_comp_swap (hr : 0 < r) (a M : ℝ)
    (hA : MemLp (aRKer a M r) 2 (volume.prod volume))
    (hW : MemLp (wSKer (2 + r) a) 2 (volume.prod volume)) :
    Integrable (Function.uncurry fun x w : ℝ =>
      ∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qFKerTwo M) (qRKerTwo M) r w y z x)
      (volume.prod volume) := by
  have hdom : Integrable (Function.uncurry fun x w : ℝ =>
      qPrQKer M r (w, x) * |bAiryKer (2 + r) (x, w)|) (volume.prod volume) := by
    have h := (Measure.measurePreserving_swap (μ := volume) (ν := volume)
      ).integrable_comp_of_integrable
      (integrable_uncurry_qPrQKer_mul_abs_bAiryKer hr a M hA hW)
    apply h.congr
    filter_upwards with p
    obtain ⟨x, w⟩ := p
    rfl
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x w : ℝ =>
      ∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qFKerTwo M) (qRKerTwo M) r w y z x)
      (volume.prod volume) :=
    ((measurable_uncurry_sectorInnerW (measurable_qFKerTwo M) (measurable_qRKerTwo M) hr M
      (qFKerTwo_abs_le_qKerTwo M) (qRKerTwo_abs_le_qKerTwo M)).comp
      measurable_swap).aestronglyMeasurable
  apply hdom.mono' hmeas
  filter_upwards with p
  obtain ⟨x, w⟩ := p
  show ‖∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qFKerTwo M) (qRKerTwo M) r w y z x‖
    ≤ qPrQKer M r (w, x) * |bAiryKer (2 + r) (x, w)|
  exact sectorInnerW_abs_le hr M (measurable_qFKerTwo M) (measurable_qRKerTwo M)
    (qFKerTwo_abs_le_qKerTwo M) (qRKerTwo_abs_le_qKerTwo M) w x

/-- **Trace equality** `Tr C_r^{RF} = Tr C_r^{FR}`: the RF and FR sector
traces are equal — the 4-D reversal `(x,y,z,w) ↦ (w,z,y,x)`,
implemented in the Lean `(x, w, y, z)` nesting order as the pointwise
involution `sectorIntegrand_RF_eq_FR_involution`, the inner `(y, z)` swap (`sectorIntegrand_yz_swap`), and
one outer `(x, w)` swap (`MeasureTheory.integral_integral_swap`, Tonelli input
`integrable_sectorInnerFR_comp_swap`).  The `MemLp` hypotheses are the Tonelli-chain
interface of `TwoIntervalTrace` (needed
once, for the outer swap); same shape as `trSectorFR_eq_frI1_add_frI2`. -/
theorem trSectorRF_eq_trSectorFR (hr : 0 < r) (a M : ℝ)
    (hA : MemLp (aRKer a M r) 2 (volume.prod volume))
    (hW : MemLp (wSKer (2 + r) a) 2 (volume.prod volume)) :
    trSectorRF M r = trSectorFR M r := by
  have hInner : ∀ x w : ℝ,
      (∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qRKerTwo M) (qFKerTwo M) r x y z w)
        = ∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qFKerTwo M) (qRKerTwo M) r w y z x := by
    intro x w
    have h1 : (∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qRKerTwo M) (qFKerTwo M) r x y z w)
        = ∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qFKerTwo M) (qRKerTwo M) r w z y x :=
      integral_congr_ae (Eventually.of_forall fun y =>
        integral_congr_ae (Eventually.of_forall fun z =>
          sectorIntegrand_RF_eq_FR_involution M r x y z w))
    rw [h1]
    exact (sectorIntegrand_yz_swap hr M (measurable_qFKerTwo M)
      (qFKerTwo_abs_le_heatKernel M) w x).symm
  unfold trSectorRF trSectorFR trSector
  rw [integral_congr_ae (Eventually.of_forall fun x =>
    integral_congr_ae (Eventually.of_forall fun w => hInner x w))]
  exact MeasureTheory.integral_integral_swap
    (integrable_sectorInnerFR_comp_swap hr a M hA hW)

/-! ### The RF bounds -/

/-- **The RF bound, two-term form** (mirroring `abs_trSectorFR_le`; the absorbed
form is `abs_trSectorRF_le_absorbed`).  The `MemLp` hypotheses
are the Tonelli-chain interface of `TwoIntervalTrace`; FR's existential constants serve
unchanged via the trace equality `trSectorRF_eq_trSectorFR`. -/
theorem abs_trSectorRF_le {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ {M r a : ℝ}, M₀ ≤ M → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      MemLp (aRKer a M r) 2 (volume.prod volume) →
      MemLp (wSKer (2 + r) a) 2 (volume.prod volume) →
      |trSectorRF M r|
        ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r)
          + C * Real.exp (-c * (2*M)^2) := by
  obtain ⟨C, c, M₀, hCpos, hcpos, hD6⟩ := abs_trSectorFR_le hχ0 hχ1
  refine ⟨C, c, M₀, hCpos, hcpos, ?_⟩
  intro M r a hM0 hr hradm hA hW
  have hr0 : (0:ℝ) < r := by linarith
  rw [trSectorRF_eq_trSectorFR hr0 a M hA hW]
  exact hD6 hM0 hr hradm hA hW

/-- **The RF bound, absorbed form**: `|Tr C_r^{RF}| ≤ C_χ (1+r)^{1/2} e^{−J_M(r)}` — the
`(1+r)^{1/2}` factor inherited from FR's (contrast FF).  FR's
existential `C, M₀` pass through unchanged via the trace equality; no new
constant or largeness analysis. -/
theorem abs_trSectorRF_le_absorbed {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C M₀ : ℝ, 0 < C ∧ ∀ {M r a : ℝ}, M₀ ≤ M → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      MemLp (aRKer a M r) 2 (volume.prod volume) →
      MemLp (wSKer (2 + r) a) 2 (volume.prod volume) →
      |trSectorRF M r| ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
  obtain ⟨C, M₀, hCpos, hD6⟩ := abs_trSectorFR_le_absorbed hχ0 hχ1
  refine ⟨C, M₀, hCpos, ?_⟩
  intro M r a hM0 hr hradm hA hW
  have hr0 : (0:ℝ) < r := by linarith
  rw [trSectorRF_eq_trSectorFR hr0 a M hA hW]
  exact hD6 hM0 hr hradm hA hW

/-- **The fully discharged absorbed bound** — the `MemLp` hypotheses discharged at
`a = √(2M)` by `memLp_aRKer` (`2 ≤ a`) and `memLp_wSKer` (`r + 3 ≤ a`, from `r ≤ χa`,
`χ < 1`, and `a ≥ 3/(1−χ)`, i.e. `M` large); the discharge argument is SectorFR's
(`M₀ ↦ max M₀ (max 2 (9/(2*(1-χ)^2)))` included). -/
theorem abs_trSectorRF_le_absorbed_discharged {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C M₀ : ℝ, 0 < C ∧ ∀ {M r : ℝ}, M₀ ≤ M → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      |trSectorRF M r| ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
  obtain ⟨C, M₀, hCpos, hD6⟩ := abs_trSectorRF_le_absorbed hχ0 hχ1
  refine ⟨C, max M₀ (max 2 (9/(2*(1-χ)^2))), hCpos, ?_⟩
  intro M r hM0 hr hradm
  have hr0 : (0:ℝ) < r := by linarith
  have hM0' : M₀ ≤ M := le_trans (le_max_left _ _) hM0
  have hM2 : (2:ℝ) ≤ M := le_trans ((le_max_left 2 _).trans (le_max_right M₀ _)) hM0
  have hM0pos : (0:ℝ) < M := by linarith
  have h2M : (0:ℝ) ≤ 2*M := by linarith
  have ha2 : (2:ℝ) ≤ Real.sqrt (2*M) := by
    rw [Real.le_sqrt (by norm_num) h2M]
    nlinarith [hM2]
  have hadr : r + 3 ≤ Real.sqrt (2*M) := by
    have h1 : 9/(2*(1-χ)^2) ≤ M := le_trans ((le_max_right (2:ℝ) _).trans (le_max_right M₀ _)) hM0
    have hχ' : (0:ℝ) < 1 - χ := sub_pos.mpr hχ1
    have hsq : (3/(1-χ))^2 ≤ 2*M := by
      rw [div_pow, show (3:ℝ)^2 = 9 by norm_num]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (1-χ)^2)]
      -- `9 ≤ (2M)·(1−χ)²` from `9/(2(1−χ)²) ≤ M`
      have h2 : (0:ℝ) < (1-χ)^2 := by positivity
      have h3 := mul_le_mul_of_nonneg_right h1 h2.le
      have h4 : (9/(2*(1-χ)^2)) * (2*(1-χ)^2) = 9 := by
        field_simp [hχ'.ne']
      nlinarith [h3, h4]
    have h3 : 3/(1-χ) ≤ Real.sqrt (2*M) := by
      rw [Real.le_sqrt (by positivity) h2M]
      exact hsq
    have h4 : χ * Real.sqrt (2*M) + 3 ≤ Real.sqrt (2*M) := by
      have h5 : (3:ℝ) ≤ (1-χ) * Real.sqrt (2*M) := by
        rw [show (3:ℝ) = (1-χ) * (3/(1-χ)) by field_simp [hχ'.ne']]
        exact mul_le_mul_of_nonneg_left h3 (sub_pos.mpr hχ1).le
      nlinarith [h5, Real.sqrt_nonneg (2*M)]
    linarith [hradm, h4]
  exact hD6 hM0' hr hradm (memLp_aRKer hr0 hM0pos ha2) (memLp_wSKer hr0 hadr)

end AiryTwoInt
