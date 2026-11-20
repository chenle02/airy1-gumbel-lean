/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoInterval.FRExponents
import Airy1GumbelContrib.TwoInterval.TwoIntervalMembership
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The FR sector bound

The FR sector of the two-interval trace `Tr C_r`, one of the four sector bounds in the
trace step of the paper's separated-block estimate.  This module contains the trace
plumbing and the piece assembly; items are labelled by group letter and number
(A1, B1, …) for cross-reference within this module and `FRExponents.lean`:

* **Group A**: the `D₁`/`D₂` kernels `qF1KerTwo`, `qF2KerTwo`
  with `qFKerTwo = qF1KerTwo + qF2KerTwo`, the piece traces `frI1`, `frI2` and
  the trace-level split `trSectorFR_eq_frI1_add_frI2`, and the `(y, z)`-swap
  integrability `integrable_sectorIntegrand_yz_of_abs_le`;
* **Group B1/B4**: the exact inner evaluations
  `frI1_inner_eq` / `frI1_eq` (semigroup merge + `AiryConj.heatKernel_conv_cdf`,
  the heat–CDF convolution identity) and `frI2_inner_eq` / `frI2_eq` (the `K(α, γ)`
  convolution via `heatKernel_conv_cdf_Ioi`);
* **Group D**: the `±` domination splits (`abs_frI1_le`,
  `abs_frI2_le`), the four piece bounds (`abs_frI1_plus_le`,
  `abs_frI1_minus_le`, `abs_frI2_plus_le`,
  `abs_frI2_minus_le`) and the main bounds `abs_trSectorFR_le` /
  `abs_trSectorFR_le_absorbed` (the paper's detailed FR bound).

The pure exponent calculus (Group C: `h1Exp`/`g1Exp`/`g2Minus`/`h2Tilde` packages,
the `D₊` Gaussian mass `frI1Plus_exp_int_le`, the `E₀ ≥ c_χa⁴` largeness bounds)
and the inner-form bounds B2/B3/B5 (`frI1_Jbound`, `heatKernel_conv_cdf_Ioi`,
`frI2_Kbound`, `frI2_gamma_int_le`) are proved in
`TwoInterval/FRExponents.lean`; this module imports and consumes them — it does not
re-prove them.  The `MemLp` hypotheses `hA`/`hW` threading through the main bounds
are the Tonelli-chain interface of `TwoIntervalTrace`, discharged by `memLp_aRKer` /
`memLp_wSKer` of `TwoIntervalMembership` (the fully discharged corollaries are included).

## Relation to the exponent module

`FRExponents.lean` holds the exponent calculus and the inner-form bounds; this module
holds the kernels, the exact inner evaluations, and the piece assembly.  The elementary
quadratic lower bound used there (in place of a Hessian/Taylor expansion) gives the same
final piece bound with a sharper constant — see the `FRExponents.lean` module docstring.

## Implementation notes

* The `D₁`/`D₂` split, the exact inner evaluations, the `±` domination splits and the
  assembly follow the paper's FR-sector computation.  The inherited `saddleF_ge` side
  hypothesis (`2 ≤ saddleR M r`) is discharged from `2 ≤ M` via `two_le_saddleR`; the
  piece lemmas carry `2 ≤ M` (resp. `3 ≤ M` for the `I₂⁻` slope, see C6 below)
  and the main bounds absorb them into `M₀`.
* Packaging: the piece integrals are kept as **iterated** Bochner integrals
  (the `trSector` convention of `TwoIntervalTrace`); the `(δ, v)` change of variables
  is run as two sequential 1D affine substitutions on the
  enlarged full-plane dominating integral (`integral_mul_comp_half_add_half_sub`),
  with Jacobian factor 2 — no 2D Jacobian API is needed.
* Packaging (constant uniformity): the inner-form bounds B2/B5 and
  the `D₊` mass bound C4 of `FRExponents.lean` are packaged `∃ C` *per*
  `(M, r)`-instance, while the detailed FR bound needs constants *uniform* in `1 ≤ r`.
  Since the witnesses are `r`-independent closed forms, the replay with the
  constant moved outside `∀ r` is given in this module
  (`frI1_Jbound_uniform`, `frI2_Kbound_uniform`, `frI2_gamma_int_le_uniform`,
  `frI1Plus_exp_int_le_uniform` — see their section docstring); strengthening the
  statements in `FRExponents.lean` would collapse these to aliases.
-/

namespace AiryTwoInt

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal

open AiryConj

/-! ## Group A: the `D₁`/`D₂` kernels and the trace-level split -/

/-- **A1**: the `D₁ = {x > M}` piece of the free
kernel, `1_{M < x} p_1(x − y)` (on `D₁` the `y` variable is unrestricted). -/
noncomputable def qF1KerTwo (M : ℝ) : ℝ × ℝ → ℝ :=
  (Set.Ioi M ×ˢ Set.univ).indicator fun p => heatKernel 1 (p.1 - p.2)

/-- **A1**: the `D₂ = {x ≤ M, y > M}` piece of the
free kernel, `1_{x ≤ M, M < y} p_1(x − y)`. -/
noncomputable def qF2KerTwo (M : ℝ) : ℝ × ℝ → ℝ :=
  (Set.Iic M ×ˢ Set.Ioi M).indicator fun p => heatKernel 1 (p.1 - p.2)

/-- `qF1KerTwo` is measurable. -/
theorem measurable_qF1KerTwo (M : ℝ) : Measurable (qF1KerTwo M) :=
  Measurable.indicator
    (((continuous_heatKernel 1).comp (continuous_fst.sub continuous_snd)).measurable)
    (measurableSet_Ioi.prod MeasurableSet.univ)

/-- `qF2KerTwo` is measurable. -/
theorem measurable_qF2KerTwo (M : ℝ) : Measurable (qF2KerTwo M) :=
  Measurable.indicator
    (((continuous_heatKernel 1).comp (continuous_fst.sub continuous_snd)).measurable)
    (measurableSet_Iic.prod measurableSet_Ioi)

/-- On `D₁` (i.e. for `M < x`), the `D₁` kernel is the free heat kernel. -/
theorem qF1KerTwo_apply_of_lt {M x : ℝ} (hx : M < x) (y : ℝ) :
    qF1KerTwo M (x, y) = heatKernel 1 (x - y) :=
  Set.indicator_of_mem (Set.mem_prod.mpr ⟨hx, Set.mem_univ y⟩) _

/-- Off `D₁` (i.e. for `x ≤ M`), the `D₁` kernel vanishes. -/
theorem qF1KerTwo_eq_zero_of_le {M x : ℝ} (hx : x ≤ M) (y : ℝ) :
    qF1KerTwo M (x, y) = 0 :=
  Set.indicator_of_notMem (fun h => (not_lt.mpr hx) (Set.mem_prod.mp h).1) _

/-- For `x ≤ M`, the `D₂` kernel is the `y`-indicator of `{y > M}` times the free
heat kernel. -/
theorem qF2KerTwo_apply_of_le {M x : ℝ} (hx : x ≤ M) (y : ℝ) :
    qF2KerTwo M (x, y) = (Set.Ioi M).indicator (fun y' => heatKernel 1 (x - y')) y := by
  by_cases hy : M < y
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hy), qF2KerTwo,
      Set.indicator_of_mem (Set.mem_prod.mpr ⟨hx, hy⟩)]
  · rw [Set.indicator_of_notMem (fun h => hy (Set.mem_Ioi.mp h)), qF2KerTwo,
      Set.indicator_of_notMem (fun h => hy (Set.mem_prod.mp h).2)]

/-- Off `D₂`'s first condition (i.e. for `M < x`), the `D₂` kernel vanishes. -/
theorem qF2KerTwo_eq_zero_of_lt {M x : ℝ} (hx : M < x) (y : ℝ) :
    qF2KerTwo M (x, y) = 0 :=
  Set.indicator_of_notMem (fun h => (not_le.mpr hx) (Set.mem_prod.mp h).1) _

/-- **A1, the pointwise split**: the free region is the disjoint
union `D₁ ⊔ D₂`, so `Q^F = Q^{F₁} + Q^{F₂}` pointwise. -/
theorem qFKerTwo_eq_qF1_add_qF2 (M : ℝ) (p : ℝ × ℝ) :
    qFKerTwo M p = qF1KerTwo M p + qF2KerTwo M p := by
  obtain ⟨x, y⟩ := p
  rcases le_or_gt x M with hx | hx
  · -- `x ≤ M`: `D₁` off, `D₂` decides by `y`
    rw [qF1KerTwo_eq_zero_of_le hx y, zero_add]
    rcases lt_or_ge M y with hy | hy
    · have hmem : (x, y) ∈ {q : ℝ × ℝ | M < q.1 ∨ M < q.2} := Or.inr hy
      rw [qFKerTwo, Set.indicator_of_mem hmem, qF2KerTwo,
        Set.indicator_of_mem (Set.mem_prod.mpr ⟨hx, hy⟩)]
    · have hnmem : (x, y) ∉ {q : ℝ × ℝ | M < q.1 ∨ M < q.2} := by
        simp only [Set.mem_ofPred_eq, not_or, not_lt]
        exact ⟨hx, hy⟩
      rw [qFKerTwo, Set.indicator_of_notMem hnmem, qF2KerTwo,
        Set.indicator_of_notMem (fun h => (not_lt.mpr hy) (Set.mem_prod.mp h).2)]
  · -- `M < x`: `D₁` on, `D₂` off
    rw [qF1KerTwo_apply_of_lt hx y, qF2KerTwo_eq_zero_of_lt hx y, add_zero]
    have hmem : (x, y) ∈ {q : ℝ × ℝ | M < q.1 ∨ M < q.2} := Or.inl hx
    rw [qFKerTwo, Set.indicator_of_mem hmem]

/-- `Q^{F₁}` is pointwise nonnegative. -/
theorem qF1KerTwo_nonneg (M : ℝ) (p : ℝ × ℝ) : 0 ≤ qF1KerTwo M p := by
  unfold qF1KerTwo
  by_cases h : p ∈ Set.Ioi M ×ˢ Set.univ
  · rw [Set.indicator_of_mem h]
    exact (heatKernel_pos one_pos _).le
  · rw [Set.indicator_of_notMem h]

/-- `Q^{F₂}` is pointwise nonnegative. -/
theorem qF2KerTwo_nonneg (M : ℝ) (p : ℝ × ℝ) : 0 ≤ qF2KerTwo M p := by
  unfold qF2KerTwo
  by_cases h : p ∈ Set.Iic M ×ˢ Set.Ioi M
  · rw [Set.indicator_of_mem h]
    exact (heatKernel_pos one_pos _).le
  · rw [Set.indicator_of_notMem h]

/-- `Q^{F₁} ≤ Q` pointwise (from `Q^F = Q^{F₁} + Q^{F₂}` with `Q^{F₂} ≥ 0` and
`Q^F ≤ Q`). -/
theorem qF1KerTwo_le_qKerTwo (M : ℝ) (p : ℝ × ℝ) : qF1KerTwo M p ≤ qKerTwo M p := by
  have h := qFKerTwo_eq_qF1_add_qF2 M p
  have hF := qFKerTwo_le_qKerTwo M p
  have h2 := qF2KerTwo_nonneg M p
  linarith

/-- `Q^{F₂} ≤ Q` pointwise. -/
theorem qF2KerTwo_le_qKerTwo (M : ℝ) (p : ℝ × ℝ) : qF2KerTwo M p ≤ qKerTwo M p := by
  have h := qFKerTwo_eq_qF1_add_qF2 M p
  have hF := qFKerTwo_le_qKerTwo M p
  have h1 := qF1KerTwo_nonneg M p
  linarith

/-- **A1, the sector domination** (`|Q^{F₁}| ≤ Q`). -/
theorem qF1KerTwo_abs_le_qKerTwo (M : ℝ) (p : ℝ × ℝ) : |qF1KerTwo M p| ≤ qKerTwo M p := by
  rw [abs_of_nonneg (qF1KerTwo_nonneg M p)]
  exact qF1KerTwo_le_qKerTwo M p

/-- `|Q^{F₂}| ≤ Q` pointwise. -/
theorem qF2KerTwo_abs_le_qKerTwo (M : ℝ) (p : ℝ × ℝ) : |qF2KerTwo M p| ≤ qKerTwo M p := by
  rw [abs_of_nonneg (qF2KerTwo_nonneg M p)]
  exact qF2KerTwo_le_qKerTwo M p

/-- `|Q^{F₁}| ≤ p₁` pointwise (the indicator is dominated by the positive free
kernel — the A3 swap-integrability input). -/
theorem qF1KerTwo_abs_le_heatKernel (M : ℝ) (p : ℝ × ℝ) :
    |qF1KerTwo M p| ≤ heatKernel 1 (p.1 - p.2) := by
  rw [abs_of_nonneg (qF1KerTwo_nonneg M p)]
  unfold qF1KerTwo
  by_cases h : p ∈ Set.Ioi M ×ˢ Set.univ
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]
    exact (heatKernel_pos one_pos _).le

/-- `|Q^{F₂}| ≤ p₁` pointwise. -/
theorem qF2KerTwo_abs_le_heatKernel (M : ℝ) (p : ℝ × ℝ) :
    |qF2KerTwo M p| ≤ heatKernel 1 (p.1 - p.2) := by
  rw [abs_of_nonneg (qF2KerTwo_nonneg M p)]
  unfold qF2KerTwo
  by_cases h : p ∈ Set.Iic M ×ˢ Set.Ioi M
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]
    exact (heatKernel_pos one_pos _).le

/-! ### A3: the `(y, z)`-swap integrability -/

/-- **A3** (the Tonelli input for the `y`/`z` swap): at fixed
`(x, w)`, the sector integrand with left kernel dominated by the free heat kernel
(`|Qα p| ≤ p₁(p.1 − p.2)`) is jointly integrable in `(y, z)`.  The dominator is
`|g_S(w + x)| · p₁(x − y) · p_r(y − z) · p₁(z − w)` — jointly integrable by two
Chapman–Kolmogorov collapses (`heatKernel_conv`). -/
theorem integrable_sectorIntegrand_yz_of_abs_le (hr : 0 < r) (M : ℝ)
    {Qα : ℝ × ℝ → ℝ} (hQαmeas : Measurable Qα)
    (hQα : ∀ p : ℝ × ℝ, |Qα p| ≤ heatKernel 1 (p.1 - p.2)) (x w : ℝ) :
    Integrable (Function.uncurry fun y z : ℝ =>
      sectorIntegrand Qα (qRKerTwo M) r x y z w) (volume.prod volume) := by
  -- the dominator
  set C : ℝ := |bAiryKer (2 + r) (w, x)| with hC
  have hCnn : (0:ℝ) ≤ C := abs_nonneg _
  have hG : Integrable (fun q : ℝ × ℝ => C * (heatKernel 1 (x - q.1)
      * (heatKernel r (q.1 - q.2) * heatKernel 1 (q.2 - w)))) (volume.prod volume) := by
    have hmeas : AEStronglyMeasurable (fun q : ℝ × ℝ => C * (heatKernel 1 (x - q.1)
        * (heatKernel r (q.1 - q.2) * heatKernel 1 (q.2 - w)))) (volume.prod volume) :=
      (continuous_const.mul (((continuous_heatKernel 1).comp
        (continuous_const.sub continuous_fst)).mul (((continuous_heatKernel r).comp
        (continuous_fst.sub continuous_snd)).mul ((continuous_heatKernel 1).comp
        (continuous_snd.sub continuous_const))))).aestronglyMeasurable
    rw [MeasureTheory.integrable_prod_iff' hmeas]
    constructor
    · -- slice integrability at fixed `z` (second component), in `y`
      filter_upwards with z
      have hbase : Integrable fun y : ℝ =>
          heatKerTwo 1 (x, y) * heatKerTwo r (y, z) :=
        integrable_pair_mul_of_heatKernel_le one_pos hr (measurable_heatKerTwo 1)
          (measurable_heatKerTwo r) (fun a b => heatKerTwo_abs_le_self one_pos (a, b))
          (fun a b => heatKerTwo_abs_le_self hr (a, b)) x z
      apply (((hbase.const_mul (heatKernel 1 (z - w))).const_mul C)).congr
      filter_upwards with y
      show C * (heatKernel 1 (z - w) * (heatKernel 1 (x - y) * heatKernel r (y - z)))
        = C * (heatKernel 1 (x - y) * (heatKernel r (y - z) * heatKernel 1 (z - w)))
      ring
    · -- the outer integrability: the `y`-norm-integral collapses to `C'·p_{1+r}(x − z)`
      have hclosed : (fun z : ℝ => ∫ y : ℝ, ‖C * (heatKernel 1 (x - y)
          * (heatKernel r (y - z) * heatKernel 1 (z - w)))‖)
          = fun z : ℝ => (C * heatKernel 1 (z - w)) * heatKernel (1 + r) (x - z) := by
        funext z
        have hnn : ∀ y : ℝ, ‖C * (heatKernel 1 (x - y)
            * (heatKernel r (y - z) * heatKernel 1 (z - w)))‖
            = C * (heatKernel 1 (x - y) * (heatKernel r (y - z) * heatKernel 1 (z - w))) := by
          intro y
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hCnn,
            abs_of_nonneg (heatKernel_pos one_pos _).le, abs_mul,
            abs_of_nonneg (heatKernel_pos hr _).le, abs_of_nonneg (heatKernel_pos one_pos _).le]
        rw [integral_congr_ae (Eventually.of_forall hnn)]
        rw [show (fun y : ℝ => C * (heatKernel 1 (x - y)
            * (heatKernel r (y - z) * heatKernel 1 (z - w))))
          = fun y : ℝ => (C * heatKernel 1 (z - w))
            * (heatKernel 1 (x - y) * heatKernel r (y - z)) from funext fun y => by ring]
        rw [integral_const_mul, heatKernel_conv one_pos hr x z]
      rw [hclosed]
      have hbase : Integrable fun z : ℝ =>
          heatKerTwo (1 + r) (x, z) * heatKerTwo 1 (z, w) :=
        integrable_pair_mul_of_heatKernel_le (by linarith : (0:ℝ) < 1 + r) one_pos
          (measurable_heatKerTwo (1 + r)) (measurable_heatKerTwo 1)
          (fun a b => heatKerTwo_abs_le_self (by linarith) (a, b))
          (fun a b => heatKerTwo_abs_le_self one_pos (a, b)) x w
      apply (hbase.const_mul C).congr
      filter_upwards with z
      show C * (heatKernel (1 + r) (x - z) * heatKernel 1 (z - w))
        = (C * heatKernel 1 (z - w)) * heatKernel (1 + r) (x - z)
      ring
  apply hG.mono' ?_ ?_
  · exact (measurable_sectorIntegrand_yz hQαmeas (measurable_qRKerTwo M) r x w).aestronglyMeasurable
  · filter_upwards with q
    obtain ⟨y, z⟩ := q
    show ‖sectorIntegrand Qα (qRKerTwo M) r x y z w‖
      ≤ C * (heatKernel 1 (x - y) * (heatKernel r (y - z) * heatKernel 1 (z - w)))
    have hqR : |qRKerTwo M (z, w)| ≤ heatKernel 1 (z - w) :=
      (qRKerTwo_abs_le_qKerTwo M (z, w)).trans (qKerTwo_le M (z, w))
    have hp1 : (0:ℝ) ≤ heatKernel 1 (x - y) := (heatKernel_pos one_pos _).le
    have hpr : (0:ℝ) ≤ heatKernel r (y - z) := (heatKernel_pos hr _).le
    have hp1' : (0:ℝ) ≤ heatKernel 1 (z - w) := (heatKernel_pos one_pos _).le
    show |(Qα (x, y) * heatKernel r (y - z)) * qRKerTwo M (z, w) * bAiryKer (2 + r) (w, x)|
      ≤ C * (heatKernel 1 (x - y) * (heatKernel r (y - z) * heatKernel 1 (z - w)))
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hpr]
    show (|Qα (x, y)| * heatKernel r (y - z)) * |qRKerTwo M (z, w)| * |bAiryKer (2 + r) (w, x)|
      ≤ C * (heatKernel 1 (x - y) * (heatKernel r (y - z) * heatKernel 1 (z - w)))
    calc (|Qα (x, y)| * heatKernel r (y - z)) * |qRKerTwo M (z, w)| * |bAiryKer (2 + r) (w, x)|
        ≤ (heatKernel 1 (x - y) * heatKernel r (y - z)) * heatKernel 1 (z - w) * C :=
          mul_le_mul
            (mul_le_mul (mul_le_mul_of_nonneg_right (hQα (x, y)) hpr) hqR (abs_nonneg _)
              (mul_nonneg hp1 hpr))
            (le_refl C) (abs_nonneg _) (mul_nonneg (mul_nonneg hp1 hpr) hp1')
      _ = C * (heatKernel 1 (x - y) * (heatKernel r (y - z) * heatKernel 1 (z - w))) := by ring

/-- **A3, the swap**: at fixed `(x, w)` the `(y, z)` integration order
of the sector integrand can be exchanged (`MeasureTheory.integral_integral_swap`,
the joint integrability being `integrable_sectorIntegrand_yz_of_abs_le`). -/
theorem sectorIntegrand_yz_swap (hr : 0 < r) (M : ℝ)
    {Qα : ℝ × ℝ → ℝ} (hQαmeas : Measurable Qα)
    (hQα : ∀ p : ℝ × ℝ, |Qα p| ≤ heatKernel 1 (p.1 - p.2)) (x w : ℝ) :
    (∫ y : ℝ, ∫ z : ℝ, sectorIntegrand Qα (qRKerTwo M) r x y z w)
      = ∫ z : ℝ, ∫ y : ℝ, sectorIntegrand Qα (qRKerTwo M) r x y z w :=
  MeasureTheory.integral_integral_swap
    (integrable_sectorIntegrand_yz_of_abs_le hr M hQαmeas hQα x w)

/-- The `D₁` instance of the `(y, z)` swap. -/
theorem frI1_inner_swap (hr : 0 < r) (M : ℝ) (x w : ℝ) :
    (∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
      = ∫ z : ℝ, ∫ y : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w :=
  sectorIntegrand_yz_swap hr M (measurable_qF1KerTwo M) (qF1KerTwo_abs_le_heatKernel M) x w

/-- The `D₂` instance of the `(y, z)` swap. -/
theorem frI2_inner_swap (hr : 0 < r) (M : ℝ) (x w : ℝ) :
    (∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w)
      = ∫ z : ℝ, ∫ y : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w :=
  sectorIntegrand_yz_swap hr M (measurable_qF2KerTwo M) (qF2KerTwo_abs_le_heatKernel M) x w

/-- **A2**: the `I₁` piece trace, `trSector` of the `D₁` kernel against
`Q^R`. -/
noncomputable def frI1 (M r : ℝ) : ℝ := trSector (qF1KerTwo M) (qRKerTwo M) r

/-- **A2**: the `I₂` piece trace, `trSector` of the `D₂` kernel against
`Q^R`. -/
noncomputable def frI2 (M r : ℝ) : ℝ := trSector (qF2KerTwo M) (qRKerTwo M) r

/-- **A2, the trace-level split**: `Tr C_r^{FR} = I_1 + I_2` from the
pointwise kernel split `qFKerTwo_eq_qF1_add_qF2` by level-by-level `integral_add`
(the `trCr_sum_sectors` pattern with two pieces); the piece integrabilities are
the Tonelli chain of `TwoIntervalTrace` instantiated at `(qF1, qR)`, `(qF2, qR)` via A1's
domination, with the `w`/`x` levels conditional on the `MemLp` interface
(`hA`/`hW`). -/
theorem trSectorFR_eq_frI1_add_frI2 (hr : 0 < r) (a M : ℝ)
    (hA : MemLp (aRKer a M r) 2 (volume.prod volume))
    (hW : MemLp (wSKer (2 + r) a) 2 (volume.prod volume)) :
    trSectorFR M r = frI1 M r + frI2 M r := by
  have hsplit : ∀ x y z w : ℝ, sectorIntegrand (qFKerTwo M) (qRKerTwo M) r x y z w
      = sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w
        + sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w := by
    intro x y z w
    show qFKerTwo M (x, y) * heatKernel r (y - z) * qRKerTwo M (z, w)
        * bAiryKer (2 + r) (w, x) = _
    rw [qFKerTwo_eq_qF1_add_qF2 M (x, y)]
    unfold sectorIntegrand
    ring
  have h1 : ∀ p : ℝ × ℝ, |qF1KerTwo M p| ≤ qKerTwo M p := qF1KerTwo_abs_le_qKerTwo M
  have h2 : ∀ p : ℝ × ℝ, |qF2KerTwo M p| ≤ qKerTwo M p := qF2KerTwo_abs_le_qKerTwo M
  have hR : ∀ p : ℝ × ℝ, |qRKerTwo M p| ≤ qKerTwo M p := qRKerTwo_abs_le_qKerTwo M
  have hz1 := fun x y w => integrable_sectorIntegrand_z hr M
    (measurable_qF1KerTwo M) (measurable_qRKerTwo M) h1 hR x y w
  have hz2 := fun x y w => integrable_sectorIntegrand_z hr M
    (measurable_qF2KerTwo M) (measurable_qRKerTwo M) h2 hR x y w
  have hy1 := fun x w => integrable_sectorInnerY hr M
    (measurable_qF1KerTwo M) (measurable_qRKerTwo M) h1 hR x w
  have hy2 := fun x w => integrable_sectorInnerY hr M
    (measurable_qF2KerTwo M) (measurable_qRKerTwo M) h2 hR x w
  have hw1 := integrable_sectorInnerW_ae hr a M hA hW
    (measurable_qF1KerTwo M) (measurable_qRKerTwo M) h1 hR
  have hw2 := integrable_sectorInnerW_ae hr a M hA hW
    (measurable_qF2KerTwo M) (measurable_qRKerTwo M) h2 hR
  have hx1 := integrable_sectorInnerX hr a M hA hW
    (measurable_qF1KerTwo M) (measurable_qRKerTwo M) h1 hR
  have hx2 := integrable_sectorInnerX hr a M hA hW
    (measurable_qF2KerTwo M) (measurable_qRKerTwo M) h2 hR
  have step1 : ∀ x w y : ℝ, (∫ z : ℝ, sectorIntegrand (qFKerTwo M) (qRKerTwo M) r x y z w)
      = (∫ z : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
        + (∫ z : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w) := by
    intro x w y
    rw [show (fun z => sectorIntegrand (qFKerTwo M) (qRKerTwo M) r x y z w)
        = fun z => sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w
          + sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w from
        funext fun z => hsplit x y z w]
    exact integral_add (hz1 x y w) (hz2 x y w)
  have step2 : ∀ x w : ℝ, (∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qFKerTwo M) (qRKerTwo M) r x y z w)
      = (∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
        + (∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w) := by
    intro x w
    rw [show (fun y => ∫ z : ℝ, sectorIntegrand (qFKerTwo M) (qRKerTwo M) r x y z w)
        = fun y => (∫ z : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
          + (∫ z : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w) from
        funext fun y => step1 x w y]
    exact integral_add (hy1 x w) (hy2 x w)
  have step3 : ∀ᵐ x : ℝ ∂volume,
      (∫ w : ℝ, ∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qFKerTwo M) (qRKerTwo M) r x y z w)
      = (∫ w : ℝ, ∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
        + (∫ w : ℝ, ∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w) := by
    filter_upwards [hw1, hw2] with x hx1' hx2'
    rw [show (fun w => ∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qFKerTwo M) (qRKerTwo M) r x y z w)
        = fun w => (∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
          + (∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w) from
        funext fun w => step2 x w]
    exact integral_add hx1' hx2'
  unfold trSectorFR frI1 frI2 trSector
  rw [integral_congr_ae step3]
  exact integral_add hx1 hx2

/-! ## Group B: the exact inner evaluations -/

/-- **B1, the `J`-factor** (closed form from the heat–CDF convolution identity):
`J(α, β) = p_{r+2}(α − β) · Φ(−(α + (r+1)β)/√(2(r+1)(r+2)))` with the standard
normal tail written as `gaussianTail (1/2) · / √(2π)`. -/
noncomputable def frJ1 (r : ℝ) (α β : ℝ) : ℝ :=
  heatKernel (r+2) (α-β)
    * (gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
        / Real.sqrt (2*Real.pi))

/-- `Q^R(z, w)` at `w ≤ M` is the `z`-indicator of `(−∞, M]` times the reflected
kernel. -/
theorem qRKerTwo_apply_of_snd_le {M w : ℝ} (hw : w ≤ M) (z : ℝ) :
    qRKerTwo M (z, w) = (Set.Iic M).indicator (fun z' => heatKernel 1 (2*M - z' - w)) z := by
  by_cases hz : z ≤ M
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hz), qRKerTwo,
      Set.indicator_of_mem (Set.mem_prod.mpr ⟨hz, hw⟩)]
  · rw [Set.indicator_of_notMem (fun h => hz (Set.mem_Iic.mp h)), qRKerTwo,
      Set.indicator_of_notMem (fun h => hz (Set.mem_prod.mp h).1)]

/-- `Q^R(z, w)` vanishes for `w > M`. -/
theorem qRKerTwo_eq_zero_of_snd_lt {M w : ℝ} (hw : M < w) (z : ℝ) :
    qRKerTwo M (z, w) = 0 :=
  Set.indicator_of_notMem (fun h => (not_le.mpr hw) (Set.mem_prod.mp h).2) _

/-- **B1**: the exact `I₁` inner evaluation — the `y`/`z` swap (A3),
the semigroup `y`-merge (`heatKernel_conv`), the `qRKerTwo`
indicator, and the heat–CDF identity (`AiryConj.heatKernel_conv_cdf`) give, for `M < x`,
`w ≤ M`, the closed form `J(x−M, M−w) · g_S(w + x)`. -/
theorem frI1_inner_eq (hr : 0 < r) {M x w : ℝ} (hx : M < x) (hw : w ≤ M) :
    ∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w
      = (heatKernel (r+1+1) ((x-M)-(M-w))
          * (gaussianTail (1/2) (((x-M) + (r+1)*(M-w)) / Real.sqrt (2*(r+1)*(r+1+1)))
              / Real.sqrt (2*Real.pi)))
        * bAiryKer (2+r) (w, x) := by
  have hL : (0:ℝ) < r + 1 := by linarith
  -- step 1: swap to `z`-outer (A3)
  rw [frI1_inner_swap hr M x w]
  -- step 2: the `y`-merge at fixed `z`
  have hy : ∀ z : ℝ, (∫ y : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
      = (qRKerTwo M (z, w) * bAiryKer (2+r) (w, x)) * heatKernel (r+1) (x - z) := by
    intro z
    calc (∫ y : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
        = ∫ y : ℝ, (qRKerTwo M (z, w) * bAiryKer (2+r) (w, x))
            * (heatKernel 1 (x - y) * heatKernel r (y - z)) := by
          apply integral_congr_ae
          filter_upwards with y
          show qF1KerTwo M (x, y) * heatKernel r (y - z) * qRKerTwo M (z, w)
              * bAiryKer (2+r) (w, x) = _
          rw [qF1KerTwo_apply_of_lt hx y]
          ring
      _ = (qRKerTwo M (z, w) * bAiryKer (2+r) (w, x))
            * ∫ y : ℝ, heatKernel 1 (x - y) * heatKernel r (y - z) := integral_const_mul _ _
      _ = (qRKerTwo M (z, w) * bAiryKer (2+r) (w, x)) * heatKernel (1+r) (x - z) := by
          rw [heatKernel_conv one_pos hr x z]
      _ = (qRKerTwo M (z, w) * bAiryKer (2+r) (w, x)) * heatKernel (r+1) (x - z) := by
          rw [show (1:ℝ) + r = r + 1 by ring]
  rw [integral_congr_ae (Eventually.of_forall hy)]
  -- step 3: the `qRKerTwo` indicator, pulling out the `(w, x)`-factors
  have hz : ∀ z : ℝ, (qRKerTwo M (z, w) * bAiryKer (2+r) (w, x)) * heatKernel (r+1) (x - z)
      = bAiryKer (2+r) (w, x) * ((Set.Iic M).indicator
          (fun z' => heatKernel (r+1) (x - z') * heatKernel 1 (2*M - z' - w)) z) := by
    intro z
    rw [qRKerTwo_apply_of_snd_le hw z]
    by_cases hzm : z ≤ M
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hzm),
        Set.indicator_of_mem (Set.mem_Iic.mpr hzm)]
      ring
    · rw [Set.indicator_of_notMem (fun h => hzm (Set.mem_Iic.mp h)),
        Set.indicator_of_notMem (fun h => hzm (Set.mem_Iic.mp h))]
      ring
  rw [integral_congr_ae (Eventually.of_forall hz), integral_const_mul,
    MeasureTheory.integral_indicator measurableSet_Iic]
  -- step 4: the heat–CDF identity (`heatKernel_conv_cdf` at `L = r+1`, `α = x−M`, `β = M−w`)
  calc bAiryKer (2+r) (w, x)
        * ∫ z in Set.Iic M, heatKernel (r+1) (x - z) * heatKernel 1 (2*M - z - w)
      = bAiryKer (2+r) (w, x) * ∫ z in Set.Iic M, heatKernel (r+1) (M + (x-M) - z)
          * heatKernel 1 (M - z + (M-w)) := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Iic
        intro z _
        show heatKernel (r+1) (x - z) * heatKernel 1 (2*M - z - w)
          = heatKernel (r+1) (M + (x-M) - z) * heatKernel 1 (M - z + (M-w))
        rw [show x - z = M + (x-M) - z by ring, show 2*M - z - w = M - z + (M-w) by ring]
    _ = bAiryKer (2+r) (w, x) * (heatKernel (r+1+1) ((x-M)-(M-w))
          * (gaussianTail (1/2) (((x-M) + (r+1)*(M-w)) / Real.sqrt (2*(r+1)*(r+1+1)))
            / Real.sqrt (2*Real.pi))) := by
        rw [heatKernel_conv_cdf hL M (x-M) (M-w)]
    _ = (heatKernel (r+1+1) ((x-M)-(M-w))
          * (gaussianTail (1/2) (((x-M) + (r+1)*(M-w)) / Real.sqrt (2*(r+1)*(r+1+1)))
            / Real.sqrt (2*Real.pi))) * bAiryKer (2+r) (w, x) := by ring

/-- **B1, the `(α, β)` form**: `I₁` as the quadrant integral of
`J(α, β) · g_S((M−β) + (M+α))` with `α = x − M`, `β = M − w`.  Pure rewriting:
the indicator reductions (`integral_indicator`, unconditional) and the affine
substitutions (`integral_Iic_comp_const_sub`, `integral_Ioi_comp_sub`). -/
theorem frI1_eq (hr : 0 < r) (M : ℝ) :
    frI1 M r = ∫ α in Set.Ioi 0, ∫ β in Set.Ioi 0,
      frJ1 r α β * bAiryKer (2+r) (M-β, M+α) := by
  -- the pointwise inner reduction to the closed form on `Ioi M ×ˢ Iic M`
  have hinner : ∀ x w : ℝ, (∫ y : ℝ, ∫ z : ℝ,
        sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
      = (Set.Ioi M ×ˢ Set.Iic M).indicator
          (fun p : ℝ × ℝ => frJ1 r (p.1-M) (M-p.2) * bAiryKer (2+r) (p.2, p.1)) (x, w) := by
    intro x w
    by_cases hx : M < x
    · by_cases hw : w ≤ M
      · rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨hx, hw⟩)]
        show (∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
          = frJ1 r (x-M) (M-w) * bAiryKer (2+r) (w, x)
        rw [frI1_inner_eq hr hx hw]
        rw [show r+1+1 = r+2 by ring]
        rfl
      · rw [Set.indicator_of_notMem (fun h => hw (Set.mem_prod.mp h).2)]
        have hz0 : ∀ y : ℝ, (∫ z : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
            = 0 := by
          intro y
          rw [show (fun z => sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
              = fun _ => (0:ℝ) from funext fun z => by
            show qF1KerTwo M (x, y) * heatKernel r (y - z) * qRKerTwo M (z, w)
                * bAiryKer (2+r) (w, x) = 0
            rw [qRKerTwo_eq_zero_of_snd_lt (not_le.mp hw) z]
            simp]
          simp
        rw [show (fun y => ∫ z : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
            = fun _ => (0:ℝ) from funext hz0]
        simp
    · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_prod.mp h).1)]
      rw [show (fun y => ∫ z : ℝ, sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
          = fun _ => (0:ℝ) from funext fun y => by
        rw [show (fun z => sectorIntegrand (qF1KerTwo M) (qRKerTwo M) r x y z w)
            = fun _ => (0:ℝ) from funext fun z => by
          show qF1KerTwo M (x, y) * heatKernel r (y - z) * qRKerTwo M (z, w)
              * bAiryKer (2+r) (w, x) = 0
          rw [qF1KerTwo_eq_zero_of_le (not_lt.mp hx) y]
          simp]
        simp]
      simp
  -- assemble `frI1` and peel the product indicator level by level
  have hfr : frI1 M r = ∫ x : ℝ, ∫ w : ℝ, (Set.Ioi M ×ˢ Set.Iic M).indicator
      (fun p : ℝ × ℝ => frJ1 r (p.1-M) (M-p.2) * bAiryKer (2+r) (p.2, p.1)) (x, w) := by
    unfold frI1 trSector
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with w
    exact hinner x w
  rw [hfr]
  have hpeel : ∀ x : ℝ, (∫ w : ℝ, (Set.Ioi M ×ˢ Set.Iic M).indicator
        (fun p : ℝ × ℝ => frJ1 r (p.1-M) (M-p.2) * bAiryKer (2+r) (p.2, p.1)) (x, w))
      = (Set.Ioi M).indicator
          (fun x' => ∫ w in Set.Iic M, frJ1 r (x'-M) (M-w) * bAiryKer (2+r) (w, x')) x := by
    intro x
    by_cases hx : M < x
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hx)]
      have hwI : (fun w : ℝ => (Set.Ioi M ×ˢ Set.Iic M).indicator
            (fun p : ℝ × ℝ => frJ1 r (p.1-M) (M-p.2) * bAiryKer (2+r) (p.2, p.1)) (x, w))
          = (Set.Iic M).indicator (fun w => frJ1 r (x-M) (M-w) * bAiryKer (2+r) (w, x)) := by
        funext w
        by_cases hw : w ≤ M
        · rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨hx, Set.mem_Iic.mpr hw⟩),
            Set.indicator_of_mem (Set.mem_Iic.mpr hw)]
        · rw [Set.indicator_of_notMem (fun h => hw (Set.mem_Iic.mp (Set.mem_prod.mp h).2)),
            Set.indicator_of_notMem (fun h => hw (Set.mem_Iic.mp h))]
      rw [hwI, MeasureTheory.integral_indicator measurableSet_Iic]
    · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Ioi.mp h))]
      have hwI : (fun w : ℝ => (Set.Ioi M ×ˢ Set.Iic M).indicator
            (fun p : ℝ × ℝ => frJ1 r (p.1-M) (M-p.2) * bAiryKer (2+r) (p.2, p.1)) (x, w))
          = fun _ => (0:ℝ) :=
        funext fun w => Set.indicator_of_notMem (fun h => hx (Set.mem_prod.mp h).1) _
      rw [hwI, integral_zero]
  rw [integral_congr_ae (Eventually.of_forall hpeel),
    MeasureTheory.integral_indicator measurableSet_Ioi]
  -- the affine substitutions `w = M − β`, `x = α + M`
  have hsub1 : ∀ x : ℝ, (∫ w in Set.Iic M, frJ1 r (x-M) (M-w) * bAiryKer (2+r) (w, x))
      = ∫ β in Set.Ioi 0, frJ1 r (x-M) β * bAiryKer (2+r) (M-β, x) := by
    intro x
    have h := AiryConj.integral_Iic_comp_const_sub
      (fun β => frJ1 r (x-M) β * bAiryKer (2+r) (M-β, x)) M
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Iic
    intro w _
    show frJ1 r (x-M) (M-w) * bAiryKer (2+r) (w, x)
      = frJ1 r (x-M) (M-w) * bAiryKer (2+r) (M-(M-w), x)
    rw [show M-(M-w) = w by ring]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hsub1 x)]
  have hsub2 : (∫ x in Set.Ioi M, ∫ β in Set.Ioi 0,
        frJ1 r (x-M) β * bAiryKer (2+r) (M-β, x))
      = ∫ α in Set.Ioi 0, ∫ β in Set.Ioi 0,
          frJ1 r ((α+M)-M) β * bAiryKer (2+r) (M-β, α+M) := by
    have h := AiryConj.integral_Ioi_comp_sub
      (fun α => ∫ β in Set.Ioi 0, frJ1 r ((α+M)-M) β * bAiryKer (2+r) (M-β, α+M)) M
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    congr 1
    ring
  rw [hsub2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro α _
  apply setIntegral_congr_fun measurableSet_Ioi
  intro β _
  rw [show (α+M)-M = α by ring, show α+M = M+α by ring]

/-- **B4, the `K`-factor**: the `K(α, γ)` convolution of the `D₂`
piece, `K(α, γ) = p_{r+1}(γ − α) · Φ(−(rα + γ)/√(2r(r+1)))`. -/
noncomputable def frK2 (r : ℝ) (α γ : ℝ) : ℝ :=
  heatKernel (r+1) (γ-α)
    * (gaussianTail (1/2) ((r*α+γ) / Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))

/-- **B4**: the exact `I₂` inner evaluation — the `y`/`z` swap (A3),
the `K` convolution (B3's `heatKernel_conv_cdf_Ioi` after the substitution
`y ↦ y − M` and `heatKernel_even`), and the `qRKerTwo` indicator give, for
`x ≤ M`, `w ≤ M`, the closed form `K(M−x, M−z)` integrated against the reflected
kernel, times `g_S(w + x)`. -/
theorem frI2_inner_eq (hr : 0 < r) {M x w : ℝ} (hx : x ≤ M) (hw : w ≤ M) :
    ∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w
      = (∫ γ in Set.Ioi 0, frK2 r (M-x) γ * heatKernel 1 (γ+(M-w)))
        * bAiryKer (2+r) (w, x) := by
  -- step 1: swap to `z`-outer (A3)
  rw [frI2_inner_swap hr M x w]
  -- step 2: the `K` convolution at fixed `z`
  have hyint : ∀ z : ℝ, (∫ y : ℝ, qF2KerTwo M (x, y) * heatKernel r (y - z))
      = ∫ y in Set.Ioi M, heatKernel 1 (x - y) * heatKernel r (y - z) := by
    intro z
    rw [show (fun y => qF2KerTwo M (x, y) * heatKernel r (y - z))
        = fun y => ((Set.Ioi M).indicator (fun y' => heatKernel 1 (x - y')) y)
          * heatKernel r (y - z) from funext fun y => by rw [qF2KerTwo_apply_of_le hx y]]
    rw [show (fun y => ((Set.Ioi M).indicator (fun y' => heatKernel 1 (x - y')) y)
          * heatKernel r (y - z))
        = (Set.Ioi M).indicator (fun y => heatKernel 1 (x - y) * heatKernel r (y - z)) from
      funext fun y => by
        by_cases hym : M < y
        · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hym),
            Set.indicator_of_mem (Set.mem_Ioi.mpr hym)]
        · rw [Set.indicator_of_notMem (fun h => hym (Set.mem_Ioi.mp h)),
            Set.indicator_of_notMem (fun h => hym (Set.mem_Ioi.mp h))]
          simp]
    exact MeasureTheory.integral_indicator measurableSet_Ioi
  have hsub : ∀ z : ℝ, (∫ y in Set.Ioi M, heatKernel 1 (x - y) * heatKernel r (y - z))
      = ∫ y' in Set.Ioi 0, heatKernel 1 ((M-x)+y') * heatKernel r ((M-z)+y') := by
    intro z
    have h := AiryConj.integral_Ioi_comp_sub
      (fun y' => heatKernel 1 ((M-x)+y') * heatKernel r ((M-z)+y')) M
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    show heatKernel 1 (x - y) * heatKernel r (y - z)
      = heatKernel 1 ((M-x)+(y-M)) * heatKernel r ((M-z)+(y-M))
    rw [show (M-x)+(y-M) = y - x by ring, show (M-z)+(y-M) = y - z by ring,
      show x - y = -(y - x) by ring, heatKernel_even]
  have hy : ∀ z : ℝ, (∫ y : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w)
      = (qRKerTwo M (z, w) * bAiryKer (2+r) (w, x)) * frK2 r (M-x) (M-z) := by
    intro z
    calc (∫ y : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w)
        = ∫ y : ℝ, (qRKerTwo M (z, w) * bAiryKer (2+r) (w, x))
            * (qF2KerTwo M (x, y) * heatKernel r (y - z)) := by
          apply integral_congr_ae
          filter_upwards with y
          show qF2KerTwo M (x, y) * heatKernel r (y - z) * qRKerTwo M (z, w)
              * bAiryKer (2+r) (w, x) = _
          ring
      _ = (qRKerTwo M (z, w) * bAiryKer (2+r) (w, x))
            * ∫ y : ℝ, qF2KerTwo M (x, y) * heatKernel r (y - z) := integral_const_mul _ _
      _ = (qRKerTwo M (z, w) * bAiryKer (2+r) (w, x)) * frK2 r (M-x) (M-z) := by
          rw [hyint z, hsub z, heatKernel_conv_cdf_Ioi hr (M-x) (M-z)]
          rfl
  rw [integral_congr_ae (Eventually.of_forall hy)]
  -- step 3: the `qRKerTwo` indicator, pulling out the `(w, x)`-factor
  have hz : ∀ z : ℝ, (qRKerTwo M (z, w) * bAiryKer (2+r) (w, x)) * frK2 r (M-x) (M-z)
      = bAiryKer (2+r) (w, x) * ((Set.Iic M).indicator
          (fun z' => frK2 r (M-x) (M-z') * heatKernel 1 (2*M - z' - w)) z) := by
    intro z
    rw [qRKerTwo_apply_of_snd_le hw z]
    by_cases hzm : z ≤ M
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hzm),
        Set.indicator_of_mem (Set.mem_Iic.mpr hzm)]
      ring
    · rw [Set.indicator_of_notMem (fun h => hzm (Set.mem_Iic.mp h)),
        Set.indicator_of_notMem (fun h => hzm (Set.mem_Iic.mp h))]
      ring
  rw [integral_congr_ae (Eventually.of_forall hz), integral_const_mul,
    MeasureTheory.integral_indicator measurableSet_Iic]
  -- step 4: the substitution `z = M − γ`
  have hsub2 : (∫ z in Set.Iic M, frK2 r (M-x) (M-z) * heatKernel 1 (2*M - z - w))
      = ∫ γ in Set.Ioi 0, frK2 r (M-x) γ * heatKernel 1 (γ + (M-w)) := by
    have h := AiryConj.integral_Iic_comp_const_sub
      (fun γ => frK2 r (M-x) γ * heatKernel 1 (γ + (M-w))) M
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Iic
    intro z _
    show frK2 r (M-x) (M-z) * heatKernel 1 (2*M - z - w)
      = frK2 r (M-x) (M-z) * heatKernel 1 ((M-z) + (M-w))
    rw [show 2*M - z - w = (M-z) + (M-w) by ring]
  rw [hsub2]
  ring

/-- **B4, the `(α, β)` form**: `I₂` as the quadrant integral of
`(∫_{γ>0} K(α, γ) p_1(γ+β)) · g_S((M−β) + (M−α))` with `α = M − x`,
`β = M − w`.  Pure rewriting (unconditional indicator reductions and affine
substitutions). -/
theorem frI2_eq (hr : 0 < r) (M : ℝ) :
    frI2 M r = ∫ α in Set.Ioi 0, ∫ β in Set.Ioi 0,
      (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
        * bAiryKer (2+r) (M-β, M-α) := by
  -- the pointwise inner reduction to the closed form on `Iic M ×ˢ Iic M`
  have hinner : ∀ x w : ℝ, (∫ y : ℝ, ∫ z : ℝ,
        sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w)
      = (Set.Iic M ×ˢ Set.Iic M).indicator
          (fun p : ℝ × ℝ => (∫ γ in Set.Ioi 0, frK2 r (M-p.1) γ * heatKernel 1 (γ+(M-p.2)))
            * bAiryKer (2+r) (p.2, p.1)) (x, w) := by
    intro x w
    by_cases hx : x ≤ M
    · by_cases hw : w ≤ M
      · rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨hx, hw⟩)]
        show (∫ y : ℝ, ∫ z : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w)
          = (∫ γ in Set.Ioi 0, frK2 r (M-x) γ * heatKernel 1 (γ+(M-w)))
            * bAiryKer (2+r) (w, x)
        exact frI2_inner_eq hr hx hw
      · rw [Set.indicator_of_notMem (fun h => hw (Set.mem_prod.mp h).2)]
        have hz0 : ∀ y : ℝ, (∫ z : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w)
            = 0 := by
          intro y
          rw [show (fun z => sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w)
              = fun _ => (0:ℝ) from funext fun z => by
            show qF2KerTwo M (x, y) * heatKernel r (y - z) * qRKerTwo M (z, w)
                * bAiryKer (2+r) (w, x) = 0
            rw [qRKerTwo_eq_zero_of_snd_lt (not_le.mp hw) z]
            simp]
          simp
        rw [show (fun y => ∫ z : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w)
            = fun _ => (0:ℝ) from funext hz0]
        simp
    · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_prod.mp h).1)]
      rw [show (fun y => ∫ z : ℝ, sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w)
          = fun _ => (0:ℝ) from funext fun y => by
        rw [show (fun z => sectorIntegrand (qF2KerTwo M) (qRKerTwo M) r x y z w)
            = fun _ => (0:ℝ) from funext fun z => by
          show qF2KerTwo M (x, y) * heatKernel r (y - z) * qRKerTwo M (z, w)
              * bAiryKer (2+r) (w, x) = 0
          rw [qF2KerTwo_eq_zero_of_lt (not_le.mp hx) y]
          simp]
        simp]
      simp
  -- assemble `frI2` and peel the product indicator level by level
  have hfr : frI2 M r = ∫ x : ℝ, ∫ w : ℝ, (Set.Iic M ×ˢ Set.Iic M).indicator
      (fun p : ℝ × ℝ => (∫ γ in Set.Ioi 0, frK2 r (M-p.1) γ * heatKernel 1 (γ+(M-p.2)))
        * bAiryKer (2+r) (p.2, p.1)) (x, w) := by
    unfold frI2 trSector
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with w
    exact hinner x w
  rw [hfr]
  have hpeel : ∀ x : ℝ, (∫ w : ℝ, (Set.Iic M ×ˢ Set.Iic M).indicator
        (fun p : ℝ × ℝ => (∫ γ in Set.Ioi 0, frK2 r (M-p.1) γ * heatKernel 1 (γ+(M-p.2)))
          * bAiryKer (2+r) (p.2, p.1)) (x, w))
      = (Set.Iic M).indicator
          (fun x' => ∫ w in Set.Iic M, (∫ γ in Set.Ioi 0, frK2 r (M-x') γ
            * heatKernel 1 (γ+(M-w))) * bAiryKer (2+r) (w, x')) x := by
    intro x
    by_cases hx : x ≤ M
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx)]
      have hwI : (fun w : ℝ => (Set.Iic M ×ˢ Set.Iic M).indicator
            (fun p : ℝ × ℝ => (∫ γ in Set.Ioi 0, frK2 r (M-p.1) γ * heatKernel 1 (γ+(M-p.2)))
              * bAiryKer (2+r) (p.2, p.1)) (x, w))
          = (Set.Iic M).indicator (fun w => (∫ γ in Set.Ioi 0, frK2 r (M-x) γ
              * heatKernel 1 (γ+(M-w))) * bAiryKer (2+r) (w, x)) := by
        funext w
        by_cases hw : w ≤ M
        · rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨hx, Set.mem_Iic.mpr hw⟩),
            Set.indicator_of_mem (Set.mem_Iic.mpr hw)]
        · rw [Set.indicator_of_notMem (fun h => hw (Set.mem_Iic.mp (Set.mem_prod.mp h).2)),
            Set.indicator_of_notMem (fun h => hw (Set.mem_Iic.mp h))]
      rw [hwI, MeasureTheory.integral_indicator measurableSet_Iic]
    · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Iic.mp h))]
      have hwI : (fun w : ℝ => (Set.Iic M ×ˢ Set.Iic M).indicator
            (fun p : ℝ × ℝ => (∫ γ in Set.Ioi 0, frK2 r (M-p.1) γ * heatKernel 1 (γ+(M-p.2)))
              * bAiryKer (2+r) (p.2, p.1)) (x, w))
          = fun _ => (0:ℝ) :=
        funext fun w => Set.indicator_of_notMem (fun h => hx (Set.mem_prod.mp h).1) _
      rw [hwI, integral_zero]
  rw [integral_congr_ae (Eventually.of_forall hpeel),
    MeasureTheory.integral_indicator measurableSet_Iic]
  -- the affine substitutions `x = M − α`, `w = M − β`
  have hsub1 : (∫ x in Set.Iic M, ∫ w in Set.Iic M,
        (∫ γ in Set.Ioi 0, frK2 r (M-x) γ * heatKernel 1 (γ+(M-w))) * bAiryKer (2+r) (w, x))
      = ∫ α in Set.Ioi 0, ∫ w in Set.Iic M,
          (∫ γ in Set.Ioi 0, frK2 r (M-(M-α)) γ * heatKernel 1 (γ+(M-w)))
            * bAiryKer (2+r) (w, M-α) := by
    have h := AiryConj.integral_Iic_comp_const_sub
      (fun α => ∫ w in Set.Iic M, (∫ γ in Set.Ioi 0, frK2 r (M-(M-α)) γ
        * heatKernel 1 (γ+(M-w))) * bAiryKer (2+r) (w, M-α)) M
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Iic
    intro x _
    show (∫ w in Set.Iic M, (∫ γ in Set.Ioi 0, frK2 r (M-x) γ * heatKernel 1 (γ+(M-w)))
        * bAiryKer (2+r) (w, x))
      = ∫ w in Set.Iic M, (∫ γ in Set.Ioi 0, frK2 r (M-(M-(M-x))) γ
          * heatKernel 1 (γ+(M-w))) * bAiryKer (2+r) (w, M-(M-x))
    rw [show M-(M-x) = x by ring]
  rw [hsub1]
  have hsub2 : ∀ α : ℝ, (∫ w in Set.Iic M,
        (∫ γ in Set.Ioi 0, frK2 r (M-(M-α)) γ * heatKernel 1 (γ+(M-w)))
          * bAiryKer (2+r) (w, M-α))
      = ∫ β in Set.Ioi 0, (∫ γ in Set.Ioi 0, frK2 r (M-(M-α)) γ
          * heatKernel 1 (γ+(M-(M-β)))) * bAiryKer (2+r) (M-β, M-α) := by
    intro α
    have h := AiryConj.integral_Iic_comp_const_sub
      (fun β => (∫ γ in Set.Ioi 0, frK2 r (M-(M-α)) γ * heatKernel 1 (γ+(M-(M-β))))
        * bAiryKer (2+r) (M-β, M-α)) M
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Iic
    intro w _
    show (∫ γ in Set.Ioi 0, frK2 r (M-(M-α)) γ * heatKernel 1 (γ+(M-w)))
        * bAiryKer (2+r) (w, M-α)
      = (∫ γ in Set.Ioi 0, frK2 r (M-(M-α)) γ * heatKernel 1 (γ+(M-(M-(M-w)))))
        * bAiryKer (2+r) (M-(M-w), M-α)
    rw [show M-(M-w) = w by ring]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun α _ => hsub2 α)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro α _
  apply setIntegral_congr_fun measurableSet_Ioi
  intro β _
  show (∫ γ in Set.Ioi 0, frK2 r (M-(M-α)) γ * heatKernel 1 (γ+(M-(M-β))))
      * bAiryKer (2+r) (M-β, M-α)
    = (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β)) * bAiryKer (2+r) (M-β, M-α)
  rw [show M-(M-α) = α by ring, show M-(M-β) = β by ring]

/-! ## Group D: the piece assembly -/

/-- **The `G̃₂` exponent**:
`G̃₂(α, β) = (α²+β²)/4 + S(2M−α−β) + (2/3)S³` with `S = r+2`, `a² = 2M` inlined
(the negative-Airy `I₂` exponent after the `γ`-integration). -/
noncomputable def g2Tilde (M r : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.1^2 + p.2^2)/4 + (r+2)*(2*M - p.1 - p.2) + (2/3)*(r+2)^3

/-- **The positive-Airy domain of `I₂`**:
`{α ≥ 0, β ≥ 0, 2M−α−β+S² ≥ 0}` — exactly `δ = (α+β)/2 ∈ [0, δmax]`. -/
def h2Dom (M r : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 0 ≤ 2*M - p.1 - p.2 + (r+2)^2}

/-- **The negative-Airy domain of `I₂`**:
`{α ≥ 0, β ≥ 0, 2M−α−β+S² < 0}` — exactly `δ = (α+β)/2 > δmax`. -/
def h2MinusDom (M r : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 2*M - p.1 - p.2 + (r+2)^2 < 0}

/-- **The negative-Airy domain of `I₁`**: `{α ≥ 0, β ≥ 0, β > A(α)}`
with `A(α) = 2M + S² + α` (the complement of `h1Dom` within the closed quadrant). -/
def h1MinusDom (M r : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 2*M + p.1 - p.2 + (r+2)^2 < 0}

/-- `g2Tilde M r` is continuous. -/
theorem continuous_g2Tilde (M r : ℝ) : Continuous (g2Tilde M r) := by
  unfold g2Tilde
  fun_prop

/-- `h2Tilde M r` is continuous (the `rpow`-at-`3/2 > 0` trick, as in
`continuous_h1Exp`). -/
theorem continuous_h2Tilde (M r : ℝ) : Continuous (h2Tilde M r) := by
  have hrpow : Continuous fun p : ℝ × ℝ => (2*M - p.1 - p.2 + (r+2)^2)^(3/2 : ℝ) :=
    continuous_iff_continuousAt.mpr fun p =>
      (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num : (0:ℝ) ≤ 3/2))).comp
        (by fun_prop : ContinuousAt (fun p : ℝ × ℝ => 2*M - p.1 - p.2 + (r+2)^2) p)
  have h1 : Continuous fun p : ℝ × ℝ => (p.1^2 + p.2^2)/4 :=
    ((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const _
  have h2 : Continuous fun p : ℝ × ℝ => (r+2)*(2*M - p.1 - p.2) :=
    continuous_const.mul ((continuous_const.sub continuous_fst).sub continuous_snd)
  have h3 : Continuous fun _ : ℝ × ℝ => (2/3)*(r+2)^3 := continuous_const
  have h4 : Continuous fun p : ℝ × ℝ => (2/3)*(2*M - p.1 - p.2 + (r+2)^2)^(3/2 : ℝ) :=
    continuous_const.mul hrpow
  exact ((h1.add h2).add h3).add h4

/-- `h2Dom M r` is closed, hence measurable. -/
theorem measurableSet_h2Dom (M r : ℝ) : MeasurableSet (h2Dom M r) := by
  have h : h2Dom M r = (Set.Ici (0:ℝ) ×ˢ Set.Ici (0:ℝ)) ∩
      ((fun p : ℝ × ℝ => 2*M - p.1 - p.2 + (r+2)^2) ⁻¹' Set.Ici 0) := by
    ext p
    exact ⟨fun hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩, fun hp => ⟨hp.1.1, hp.1.2, hp.2⟩⟩
  rw [h]
  exact (measurableSet_Ici.prod measurableSet_Ici).inter
    (measurableSet_Ici.preimage (by fun_prop :
      Measurable fun p : ℝ × ℝ => 2*M - p.1 - p.2 + (r+2)^2))

/-- `h2MinusDom M r` is measurable. -/
theorem measurableSet_h2MinusDom (M r : ℝ) : MeasurableSet (h2MinusDom M r) := by
  have h : h2MinusDom M r = (Set.Ici (0:ℝ) ×ˢ Set.Ici (0:ℝ)) ∩
      ((fun p : ℝ × ℝ => 2*M - p.1 - p.2 + (r+2)^2) ⁻¹' Set.Iio 0) := by
    ext p
    exact ⟨fun hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩, fun hp => ⟨hp.1.1, hp.1.2, hp.2⟩⟩
  rw [h]
  exact (measurableSet_Ici.prod measurableSet_Ici).inter
    (measurableSet_Iio.preimage (by fun_prop :
      Measurable fun p : ℝ × ℝ => 2*M - p.1 - p.2 + (r+2)^2))

/-- `h1MinusDom M r` is measurable. -/
theorem measurableSet_h1MinusDom (M r : ℝ) : MeasurableSet (h1MinusDom M r) := by
  have h : h1MinusDom M r = (Set.Ici (0:ℝ) ×ˢ Set.Ici (0:ℝ)) ∩
      ((fun p : ℝ × ℝ => 2*M + p.1 - p.2 + (r+2)^2) ⁻¹' Set.Iio 0) := by
    ext p
    exact ⟨fun hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩, fun hp => ⟨hp.1.1, hp.1.2, hp.2⟩⟩
  rw [h]
  exact (measurableSet_Ici.prod measurableSet_Ici).inter
    (measurableSet_Iio.preimage (by fun_prop :
      Measurable fun p : ℝ × ℝ => 2*M + p.1 - p.2 + (r+2)^2))

/-- **The `G̃₂` decomposition**: with `δ = (α+β)/2`, `v = (α−β)/2`,
`G̃₂(α, β) = G_{2,−}(δ) + v²/2` exactly (pure algebra). -/
theorem g2Tilde_eq_g2Minus_add (M r α β : ℝ) :
    g2Tilde M r (α, β) = g2Minus M r ((α+β)/2) + ((α-β)/2)^2/2 := by
  simp only [g2Tilde, g2Minus]
  ring

/-- The backward-Airy kernel in absolute value:
`|g_S(w, x)| = e^{−(2/3)S³ − S(w+x)} · |Ai(w+x+S²)|`. -/
theorem abs_bAiryKer_apply (S w x : ℝ) :
    |bAiryKer S (w, x)|
      = Real.exp (-(2/3) * S ^ 3 - S * (w + x)) * |airyAiReal (w + x + S ^ 2)| := by
  rw [bAiryKer_eq, abs_mul, abs_of_nonneg (Real.exp_pos _).le]

/-! ### The `(δ, v)` change of variables (Jacobian 2)

Run as two sequential 1D affine substitutions on the iterated integral — no 2D
Jacobian API.  The plane integrability comes from Tonelli on the norms. -/

/-- Slice integrability in `β` at fixed `α` of `F((α+β)/2) · G((α−β)/2)` (the
substitution `β = α − 2v` makes it a shifted, scaled integrable product). -/
theorem integrable_mul_comp_half_add_half_sub_snd {F G : ℝ → ℝ}
    (hFmeas : Measurable F) (hFint : Integrable F)
    (hGmeas : Measurable G) (hG1 : ∀ x : ℝ, |G x| ≤ 1) (α : ℝ) :
    Integrable (fun β : ℝ => F ((α+β)/2) * G ((α-β)/2)) volume := by
  have hH : Integrable fun s : ℝ => F s * G (α - s) :=
    (hFint.norm).mono'
      (hFmeas.mul (hGmeas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        calc |F s| * |G (α - s)| ≤ |F s| * 1 :=
              mul_le_mul_of_nonneg_left (hG1 _) (abs_nonneg _)
          _ = |F s| := mul_one _)
  have h2 : Integrable (fun β : ℝ => (fun s => F s * G (α - s)) ((1/2)*β + α/2)) volume :=
    (hH.comp_add_right (α/2)).comp_mul_left' one_half_pos.ne'
  apply h2.congr
  filter_upwards with β
  show F ((1/2)*β + α/2) * G (α - ((1/2)*β + α/2)) = F ((α+β)/2) * G ((α-β)/2)
  rw [show (1/2)*β + α/2 = (α+β)/2 by ring, show α - ((α+β)/2) = (α-β)/2 by ring]

/-- The inner affine substitution `β ↦ v = (α−β)/2` with Jacobian factor 2:
`∫ β, F((α+β)/2) G((α−β)/2) = 2 ∫ s, F(s) G(α−s)`. -/
theorem integral_mul_comp_half_add_half_sub_inner {F G : ℝ → ℝ}
    (hFmeas : Measurable F) (hFint : Integrable F)
    (hGmeas : Measurable G) (hG1 : ∀ x : ℝ, |G x| ≤ 1) (α : ℝ) :
    ∫ β : ℝ, F ((α+β)/2) * G ((α-β)/2) = 2 * ∫ s : ℝ, F s * G (α - s) := by
  have hH : Integrable fun s : ℝ => F s * G (α - s) :=
    (hFint.norm).mono'
      (hFmeas.mul (hGmeas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        calc |F s| * |G (α - s)| ≤ |F s| * 1 :=
              mul_le_mul_of_nonneg_left (hG1 _) (abs_nonneg _)
          _ = |F s| := mul_one _)
  calc ∫ β : ℝ, F ((α+β)/2) * G ((α-β)/2)
      = ∫ β : ℝ, (fun s => F s * G (α - s)) ((1/2)*β + α/2) := by
        apply integral_congr_ae
        filter_upwards with β
        show F ((α+β)/2) * G ((α-β)/2) = F ((1/2)*β + α/2) * G (α - ((1/2)*β + α/2))
        rw [show (1/2)*β + α/2 = (α+β)/2 by ring, show α - ((α+β)/2) = (α-β)/2 by ring]
    _ = |(1/2 : ℝ)⁻¹| * ∫ s : ℝ, F s * G (α - s) := by
        rw [show (fun β : ℝ => (fun s => F s * G (α - s)) ((1/2)*β + α/2))
            = fun β => (fun β' => (fun s => F s * G (α - s)) (β' + α/2)) ((1/2)*β) from rfl]
        rw [MeasureTheory.Measure.integral_comp_mul_left
          (fun β' => (fun s => F s * G (α - s)) (β' + α/2)) (1/2)]
        rw [smul_eq_mul]
        congr 1
        exact MeasureTheory.integral_add_right_eq_self (μ := volume)
          (fun s : ℝ => F s * G (α - s)) (α/2)
    _ = 2 * ∫ s : ℝ, F s * G (α - s) := by
        rw [show |(1/2 : ℝ)⁻¹| = 2 by norm_num]

/-- The plane integrability of `(α, β) ↦ F((α+β)/2) · G((α−β)/2)` (Tonelli on the
norms, then the inner substitution). -/
theorem integrable_mul_comp_half_add_half_sub {F G : ℝ → ℝ}
    (hFmeas : Measurable F) (hFint : Integrable F)
    (hGmeas : Measurable G) (hGint : Integrable G) (hG1 : ∀ x : ℝ, |G x| ≤ 1) :
    Integrable (Function.uncurry fun α β : ℝ => F ((α+β)/2) * G ((α-β)/2))
      (volume.prod volume) := by
  -- the joint integrability of the norms in `(α, s)` coordinates
  have hNmeas : AEStronglyMeasurable
      (Function.uncurry fun α s : ℝ => ‖F s‖ * ‖G (α - s)‖) (volume.prod volume) :=
    ((hFmeas.norm.comp measurable_snd).mul
      (hGmeas.norm.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  have hjointN : Integrable (Function.uncurry fun α s : ℝ => ‖F s‖ * ‖G (α - s)‖)
      (volume.prod volume) := by
    rw [MeasureTheory.integrable_prod_iff' hNmeas]
    constructor
    · filter_upwards with s
      simp only [Function.uncurry_apply_pair]
      exact (hGint.norm.comp_sub_right s).const_mul _
    · have hgoal : (fun y : ℝ => ∫ x : ℝ,
            ‖Function.uncurry (fun α s => ‖F s‖ * ‖G (α - s)‖) (x, y)‖)
          = fun s => ∫ α : ℝ, ‖F s‖ * ‖G (α - s)‖ := by
        funext s
        apply integral_congr_ae
        filter_upwards with x
        simp only [Function.uncurry_apply_pair]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _),
          abs_of_nonneg (norm_nonneg _)]
      have hnorm : (fun s : ℝ => ∫ α : ℝ, ‖F s‖ * ‖G (α - s)‖)
          = fun s => ‖F s‖ * ∫ v : ℝ, ‖G v‖ := by
        funext s
        rw [integral_const_mul]
        congr 1
        exact MeasureTheory.integral_sub_right_eq_self (μ := volume) (fun v : ℝ => ‖G v‖) s
      rw [hgoal, hnorm]
      exact hFint.norm.mul_const _
  -- the `α`-marginal of the norms
  have houter : Integrable (fun α : ℝ => ∫ s : ℝ, ‖F s‖ * ‖G (α - s)‖) volume := by
    have hswap := hjointN.swap
    have h2 := ((MeasureTheory.integrable_prod_iff'
      (f := fun p : ℝ × ℝ => ‖F p.1‖ * ‖G (p.2 - p.1)‖) ?_).mp hswap).2
    · apply h2.congr
      filter_upwards with α
      rw [show (fun s : ℝ => ‖‖F s‖ * ‖G (α - s)‖‖)
          = fun s => ‖F s‖ * ‖G (α - s)‖ from funext fun s => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _),
          abs_of_nonneg (norm_nonneg _)]]
    · exact ((hFmeas.norm.comp measurable_fst).mul
        (hGmeas.norm.comp (measurable_snd.sub measurable_fst))).aestronglyMeasurable
  -- assemble via the first-factor-sliced Tonelli criterion
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun α β : ℝ => F ((α+β)/2) * G ((α-β)/2)) (volume.prod volume) :=
    ((hFmeas.comp ((measurable_fst.add measurable_snd).div_const 2)).mul
      (hGmeas.comp ((measurable_fst.sub measurable_snd).div_const 2))).aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff hmeas]
  constructor
  · filter_upwards with α
    simp only [Function.uncurry_apply_pair]
    exact integrable_mul_comp_half_add_half_sub_snd hFmeas hFint hGmeas hG1 α
  · have hgoal : (fun x : ℝ => ∫ y : ℝ,
          ‖Function.uncurry (fun α β => F ((α+β)/2) * G ((α-β)/2)) (x, y)‖)
        = fun α => ∫ β : ℝ, ‖F ((α+β)/2) * G ((α-β)/2)‖ := by
      funext α
      apply integral_congr_ae
      filter_upwards with β
      simp only [Function.uncurry_apply_pair]
    have hnorm : (fun α : ℝ => ∫ β : ℝ, ‖F ((α+β)/2) * G ((α-β)/2)‖)
        = fun α => 2 * ∫ s : ℝ, ‖F s‖ * ‖G (α - s)‖ := by
      funext α
      rw [show (fun β : ℝ => ‖F ((α+β)/2) * G ((α-β)/2)‖)
          = fun β => ‖F ((α+β)/2)‖ * ‖G ((α-β)/2)‖ from funext fun β => norm_mul _ _]
      exact integral_mul_comp_half_add_half_sub_inner hFmeas.norm hFint.norm
        hGmeas.norm (fun x => by
          rw [Real.norm_eq_abs, abs_abs]; exact hG1 x) α
    rw [hgoal, hnorm]
    exact houter.const_mul 2

/-- **The `(δ, v)` change of variables**: for integrable
`F, G` with `|G| ≤ 1`,
`∫∫_{ℝ²} F((α+β)/2) G((α−β)/2) dα dβ = 2 (∫ F)(∫ G)`
(Jacobian factor 2; two sequential 1D affine substitutions on the iterated
integral, then the swap justified by Tonelli on the norms). -/
theorem integral_mul_comp_half_add_half_sub {F G : ℝ → ℝ}
    (hFmeas : Measurable F) (hFint : Integrable F)
    (hGmeas : Measurable G) (hGint : Integrable G) (hG1 : ∀ x : ℝ, |G x| ≤ 1) :
    (∫ α : ℝ, ∫ β : ℝ, F ((α+β)/2) * G ((α-β)/2))
      = 2 * (∫ δ : ℝ, F δ) * ∫ v : ℝ, G v := by
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun α s : ℝ => F s * G (α - s)) (volume.prod volume) :=
    ((hFmeas.comp measurable_snd).mul
      (hGmeas.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  have hjoint : Integrable (Function.uncurry fun α s : ℝ => F s * G (α - s))
      (volume.prod volume) := by
    rw [MeasureTheory.integrable_prod_iff' hmeas]
    constructor
    · filter_upwards with s
      simp only [Function.uncurry_apply_pair]
      exact (hGint.comp_sub_right s).const_mul _
    · have hgoal : (fun y : ℝ => ∫ x : ℝ, ‖Function.uncurry (fun α s => F s * G (α - s)) (x, y)‖)
          = fun s => ∫ α : ℝ, ‖F s * G (α - s)‖ := by
        funext s
        apply integral_congr_ae
        filter_upwards with x
        simp only [Function.uncurry_apply_pair]
      have hnorm : (fun s : ℝ => ∫ α : ℝ, ‖F s * G (α - s)‖)
          = fun s => |F s| * ∫ v : ℝ, ‖G v‖ := by
        funext s
        rw [show (fun α : ℝ => ‖F s * G (α - s)‖)
            = fun α => |F s| * ‖G (α - s)‖ from funext fun α => by
          rw [norm_mul, Real.norm_eq_abs]]
        rw [integral_const_mul]
        congr 1
        exact MeasureTheory.integral_sub_right_eq_self (μ := volume) (fun v : ℝ => ‖G v‖) s
      rw [hgoal, hnorm]
      exact hFint.norm.mul_const _
  calc ∫ α : ℝ, ∫ β : ℝ, F ((α+β)/2) * G ((α-β)/2)
      = ∫ α : ℝ, 2 * ∫ s : ℝ, F s * G (α - s) := by
        apply integral_congr_ae
        filter_upwards with α
        exact integral_mul_comp_half_add_half_sub_inner hFmeas hFint hGmeas hG1 α
    _ = 2 * ∫ α : ℝ, ∫ s : ℝ, F s * G (α - s) := integral_const_mul _ _
    _ = 2 * ∫ s : ℝ, ∫ α : ℝ, F s * G (α - s) := by
        congr 1
        exact MeasureTheory.integral_integral_swap hjoint
    _ = 2 * ∫ s : ℝ, F s * ∫ α : ℝ, G (α - s) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with s
        exact integral_const_mul _ _
    _ = 2 * ∫ s : ℝ, F s * ∫ v : ℝ, G v := by
        congr 1
        apply integral_congr_ae
        filter_upwards with s
        congr 1
        exact MeasureTheory.integral_sub_right_eq_self (μ := volume) (fun v : ℝ => G v) s
    _ = 2 * (∫ δ : ℝ, F δ) * ∫ v : ℝ, G v := by rw [integral_mul_const]; ring

/-! ### Uniform-in-`r` strengthenings of the existential bounds of `FRExponents.lean`

`FRExponents.lean` packages the inner-form bounds B2/B5 and the `D₊` mass
C4 as `∃ C` *per* `(M, r)`-instance (e.g. `frI1_Jbound (hr : 0 < r) : ∃ C, …`).
The detailed FR bound needs the constants
*uniform* in `1 ≤ r` — and the witnesses there are in fact `r`-independent closed
forms, so the strengthenings below replay those
constructions with the constant moved outside the `∀ r`.  (Strengthening the
statements in `FRExponents.lean` — the witnesses are already uniform — would
collapse these wrappers to aliases.) -/

/-- **C4, uniform form** (the elementary quadratic lower bound): `∫_{D₊} e^{−H₁} ≤
C √(r+1) e^{−J_M(r)}` with `C` uniform — the `frI1Plus_exp_int_le`
assembly replayed at the explicit witness `√π(√π + 2√(2π))` from the (explicit)
region bounds `frI1Plus_exp_int_dge_le` / `frI1Plus_exp_int_dlt_le`. -/
theorem frI1Plus_exp_int_le_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ {M r : ℝ}, 1 ≤ M → 1 ≤ r → 2 ≤ saddleR M r →
      ∫ p in h1Dom M r, Real.exp (-h1Exp M r p)
        ≤ C * (r+1)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
  refine ⟨Real.sqrt Real.pi * (Real.sqrt Real.pi + 2 * Real.sqrt (2*Real.pi)), by positivity, ?_⟩
  intro M r hM hr hR
  have hL : (0:ℝ) < r + 1 := by linarith
  have hDlt_meas : MeasurableSet (h1Dom M r ∩ {p : ℝ × ℝ | p.1 < p.2}) :=
    (measurableSet_h1Dom M r).inter (measurableSet_lt measurable_fst measurable_snd)
  have hfint : IntegrableOn (fun p => Real.exp (-h1Exp M r p)) (h1Dom M r) :=
    integrableOn_exp_neg_h1Exp (lt_of_lt_of_le one_pos hr)
  have hU : h1Dom M r ∩ {p : ℝ × ℝ | p.2 ≤ p.1}
      ∪ (h1Dom M r ∩ {p : ℝ × ℝ | p.1 < p.2}) = h1Dom M r := by
    ext p
    constructor
    · intro h
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact h1
    · intro hp
      rcases le_or_gt p.2 p.1 with h | h
      · exact (Set.mem_union _ _ _).mpr (Or.inl ⟨hp, h⟩)
      · exact (Set.mem_union _ _ _).mpr (Or.inr ⟨hp, h⟩)
  have hDisj : Disjoint (h1Dom M r ∩ {p : ℝ × ℝ | p.2 ≤ p.1})
      (h1Dom M r ∩ {p : ℝ × ℝ | p.1 < p.2}) := by
    rw [Set.disjoint_left]
    rintro p ⟨-, hle⟩ ⟨-, hlt⟩
    exact (not_le.mpr (show p.1 < p.2 from hlt)) (show p.2 ≤ p.1 from hle)
  have hunion : ∫ p in h1Dom M r, Real.exp (-h1Exp M r p)
      = (∫ p in h1Dom M r ∩ {p : ℝ × ℝ | p.2 ≤ p.1}, Real.exp (-h1Exp M r p))
        + (∫ p in h1Dom M r ∩ {p : ℝ × ℝ | p.1 < p.2}, Real.exp (-h1Exp M r p)) := by
    have h := setIntegral_union hDisj hDlt_meas (hfint.mono_set Set.inter_subset_left)
      (hfint.mono_set Set.inter_subset_left)
    rwa [hU] at h
  have hge := frI1Plus_exp_int_dge_le hM hr hR
  have hlt := frI1Plus_exp_int_dlt_le hM hr hR
  have hsqrt : Real.sqrt (Real.pi * (r+1))
      = Real.sqrt Real.pi * (r+1)^(1/2 : ℝ) := by
    rw [Real.sqrt_mul Real.pi_nonneg]
    congr 1
    exact Real.sqrt_eq_rpow _
  rw [hunion]
  calc (∫ p in h1Dom M r ∩ {p : ℝ × ℝ | p.2 ≤ p.1}, Real.exp (-h1Exp M r p))
        + (∫ p in h1Dom M r ∩ {p : ℝ × ℝ | p.1 < p.2}, Real.exp (-h1Exp M r p))
      ≤ (Real.exp (-saddleJ M r) * Real.sqrt (Real.pi * (r+1)) * Real.sqrt Real.pi)
        + (Real.exp (-saddleJ M r) * (2 * Real.sqrt (2*Real.pi))
          * Real.sqrt (Real.pi * (r+1))) := add_le_add hge hlt
    _ = Real.sqrt Real.pi * (Real.sqrt Real.pi + 2 * Real.sqrt (2*Real.pi))
          * (r+1)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
        rw [hsqrt]
        ring

/-- **B2, uniform form** (the paper's bound on the `J`-factor):
`frI1_Jbound`'s construction replayed with the (already uniform) witness
`(4π)^{-1/2}/2` moved outside `∀ r` — Chernoff (`AiryConj.gaussianTail_chernoff`
with the `√(2π)`-division) plus the exact identity
`(α−β)²/(4S) + (α+Lβ)²/(4LS) = α²/(4L) + β²/4`. -/
theorem frI1_Jbound_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ {r : ℝ}, 0 < r → ∀ {α β : ℝ}, 0 ≤ α → 0 ≤ β →
      heatKernel (r+2) (α-β)
        * (gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
            / Real.sqrt (2*Real.pi))
        ≤ C * (r+2)^(-1/2 : ℝ) * Real.exp (-α^2/(4*(r+1)) - β^2/4) := by
  refine ⟨(4*Real.pi)^(-1/2 : ℝ) / 2, by positivity, ?_⟩
  intro r hr α β hα hβ
  have hL : (0:ℝ) < r + 1 := by linarith
  have hS : (0:ℝ) < r + 2 := by linarith
  have harg : (0:ℝ) ≤ (α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)) :=
    div_nonneg (add_nonneg hα (mul_nonneg (by linarith) hβ)) (Real.sqrt_nonneg _)
  have hcher := gaussianTail_chernoff ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2))) harg
  have hsqrt : Real.sqrt (Real.pi/2) / Real.sqrt (2*Real.pi) = 1/2 := by
    rw [← Real.sqrt_div (by positivity : (0:ℝ) ≤ Real.pi/2) (2*Real.pi),
      show (Real.pi/2) / (2*Real.pi) = (1/2)^2 by field_simp [Real.pi_ne_zero],
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]
  have htail : gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
      / Real.sqrt (2*Real.pi)
      ≤ (1/2) * Real.exp (-((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2) := by
    calc gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
          / Real.sqrt (2*Real.pi)
        ≤ (Real.sqrt (Real.pi/2)
          * Real.exp (-((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2))
          / Real.sqrt (2*Real.pi) :=
          div_le_div_of_nonneg_right hcher
            (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*Real.pi)).le
      _ = (1/2) * Real.exp (-((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2) := by
          rw [show Real.sqrt (Real.pi/2)
              * Real.exp (-((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2)
              / Real.sqrt (2*Real.pi)
            = (Real.sqrt (Real.pi/2) / Real.sqrt (2*Real.pi))
              * Real.exp (-((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2) by ring,
            hsqrt]
  have htsq : ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2
      = (α + (r+1)*β)^2/(4*(r+1)*(r+2)) := by
    rw [div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*(r+1)*(r+2))]
    field_simp [hL.ne', hS.ne']
    ring
  have hid : (α-β)^2/(4*(r+2)) + (α + (r+1)*β)^2/(4*(r+1)*(r+2))
      = α^2/(4*(r+1)) + β^2/4 := by
    field_simp [hL.ne', hS.ne']
    ring
  calc heatKernel (r+2) (α-β)
        * (gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
          / Real.sqrt (2*Real.pi))
      = (4*Real.pi*(r+2))^(-1/2 : ℝ) * Real.exp (-(α-β)^2/(4*(r+2)))
          * (gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
            / Real.sqrt (2*Real.pi)) := by unfold heatKernel; rfl
    _ ≤ (4*Real.pi*(r+2))^(-1/2 : ℝ) * Real.exp (-(α-β)^2/(4*(r+2)))
          * ((1/2) * Real.exp (-((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2)) :=
        mul_le_mul_of_nonneg_left htail
          (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by positivity) hS.le) _)
            (Real.exp_pos _).le)
    _ = (1/2) * (4*Real.pi*(r+2))^(-1/2 : ℝ)
          * Real.exp (-(α-β)^2/(4*(r+2)) + -((α + (r+1)*β)^2/(4*(r+1)*(r+2)))) := by
        have h2 : -((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2
            = -((α + (r+1)*β)^2/(4*(r+1)*(r+2))) := by
          rw [show -((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2
              = -(((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))^2/2) by ring, htsq]
        rw [h2]
        rw [show (4*Real.pi*(r+2))^(-1/2 : ℝ) * Real.exp (-(α-β)^2/(4*(r+2)))
            * ((1/2) * Real.exp (-((α + (r+1)*β)^2/(4*(r+1)*(r+2)))))
          = (1/2) * (4*Real.pi*(r+2))^(-1/2 : ℝ)
            * (Real.exp (-(α-β)^2/(4*(r+2)))
              * Real.exp (-((α + (r+1)*β)^2/(4*(r+1)*(r+2))))) by ring]
        rw [← Real.exp_add]
    _ = ((4*Real.pi)^(-1/2 : ℝ) / 2) * (r+2)^(-1/2 : ℝ)
          * Real.exp (-α^2/(4*(r+1)) - β^2/4) := by
        have hexp : Real.exp (-(α-β)^2/(4*(r+2)) + -((α + (r+1)*β)^2/(4*(r+1)*(r+2))))
            = Real.exp (-α^2/(4*(r+1)) - β^2/4) := by
          congr 1
          have h2 : -(α-β)^2/(4*(r+2)) + -((α + (r+1)*β)^2/(4*(r+1)*(r+2)))
              = -((α-β)^2/(4*(r+2)) + (α + (r+1)*β)^2/(4*(r+1)*(r+2))) := by ring
          rw [h2, hid]
          ring
        rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4*Real.pi) hS.le, hexp]
        ring

/-- **B5a, uniform form** (the paper's bound on the `K`-factor):
`frI2_Kbound`'s construction replayed with the (already uniform) witness
`(4π)^{-1/2}/2` moved outside `∀ r` — Chernoff plus the exact identity
`(γ−α)²/(4L) + (rα+γ)²/(4rL) = α²/4 + γ²/(4r)`. -/
theorem frI2_Kbound_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ {r : ℝ}, 0 < r → ∀ {α γ : ℝ}, 0 ≤ α → 0 ≤ γ →
      heatKernel (r+1) (γ-α)
        * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
        ≤ C * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4 - γ^2/(4*r)) := by
  refine ⟨(4*Real.pi)^(-1/2 : ℝ) / 2, by positivity, ?_⟩
  intro r hr α γ hα hγ
  have hL : (0:ℝ) < r + 1 := by linarith
  have harg : (0:ℝ) ≤ (r*α+γ)/Real.sqrt (2*r*(r+1)) :=
    div_nonneg (add_nonneg (mul_nonneg hr.le hα) hγ) (Real.sqrt_nonneg _)
  have hcher := gaussianTail_chernoff ((r*α+γ)/Real.sqrt (2*r*(r+1))) harg
  have hsqrt : Real.sqrt (Real.pi/2) / Real.sqrt (2*Real.pi) = 1/2 := by
    rw [← Real.sqrt_div (by positivity : (0:ℝ) ≤ Real.pi/2) (2*Real.pi),
      show (Real.pi/2) / (2*Real.pi) = (1/2)^2 by field_simp [Real.pi_ne_zero],
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]
  have htail : gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1)))
      / Real.sqrt (2*Real.pi)
      ≤ (1/2) * Real.exp (-((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2) := by
    calc gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi)
        ≤ (Real.sqrt (Real.pi/2)
          * Real.exp (-((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2)) / Real.sqrt (2*Real.pi) :=
          div_le_div_of_nonneg_right hcher
            (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*Real.pi)).le
      _ = (1/2) * Real.exp (-((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2) := by
          rw [show Real.sqrt (Real.pi/2)
              * Real.exp (-((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2) / Real.sqrt (2*Real.pi)
            = (Real.sqrt (Real.pi/2) / Real.sqrt (2*Real.pi))
              * Real.exp (-((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2) by ring, hsqrt]
  have htsq : ((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2 = (r*α+γ)^2/(4*r*(r+1)) := by
    rw [div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*r*(r+1))]
    field_simp [hr.ne', hL.ne']
    ring
  have hid : (γ-α)^2/(4*(r+1)) + (r*α+γ)^2/(4*r*(r+1)) = α^2/4 + γ^2/(4*r) := by
    field_simp [hr.ne', hL.ne']
    ring
  calc heatKernel (r+1) (γ-α)
        * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
      = (4*Real.pi*(r+1))^(-1/2 : ℝ) * Real.exp (-(γ-α)^2/(4*(r+1)))
          * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1)))
            / Real.sqrt (2*Real.pi)) := by
        unfold heatKernel
        rfl
    _ ≤ (4*Real.pi*(r+1))^(-1/2 : ℝ) * Real.exp (-(γ-α)^2/(4*(r+1)))
          * ((1/2) * Real.exp (-((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2)) :=
        mul_le_mul_of_nonneg_left htail
          (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by positivity) hL.le) _)
            (Real.exp_pos _).le)
    _ = (1/2) * (4*Real.pi*(r+1))^(-1/2 : ℝ)
          * Real.exp (-(γ-α)^2/(4*(r+1)) + -((r*α+γ)^2/(4*r*(r+1)))) := by
        have h2 : -((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2
            = -((r*α+γ)^2/(4*r*(r+1))) := by
          rw [show -((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2
              = -(((r*α+γ)/Real.sqrt (2*r*(r+1)))^2/2) by ring, htsq]
        rw [h2]
        rw [show (4*Real.pi*(r+1))^(-1/2 : ℝ) * Real.exp (-(γ-α)^2/(4*(r+1)))
            * ((1/2) * Real.exp (-((r*α+γ)^2/(4*r*(r+1)))))
          = (1/2) * (4*Real.pi*(r+1))^(-1/2 : ℝ)
            * (Real.exp (-(γ-α)^2/(4*(r+1))) * Real.exp (-((r*α+γ)^2/(4*r*(r+1))))) by ring]
        rw [← Real.exp_add]
    _ = ((4*Real.pi)^(-1/2 : ℝ) / 2) * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4 - γ^2/(4*r)) := by
        have hexp : Real.exp (-(γ-α)^2/(4*(r+1)) + -((r*α+γ)^2/(4*r*(r+1))))
            = Real.exp (-α^2/4 - γ^2/(4*r)) := by
          congr 1
          have h2 : -(γ-α)^2/(4*(r+1)) + -((r*α+γ)^2/(4*r*(r+1)))
              = -((γ-α)^2/(4*(r+1)) + (r*α+γ)^2/(4*r*(r+1))) := by ring
          rw [h2, hid]
          ring
        rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4*Real.pi) hL.le, hexp]
        ring

/-- **B5, uniform form** (the `γ`-integral bound with its prefactor):
`frI2_gamma_int_le`'s construction replayed with the
(already uniform) witness `2·C_K·C_t·(4π)^{-1/2}` moved outside `∀ r` — the
completed square, the affine substitution `u = √(L/4r)(γ + rβ/L)`
(`integral_Ioi_add_const`, then scaling), `gaussian_tail_std_sq_bound`
with `(1+x)⁻¹ ≤ 1`, `β²/(4L) + rβ²/(4L) = β²/4`, and
the prefactor absorption `L^{−1/2}√(r/L) = √r/(r+1) ≤ 1`. -/
theorem frI2_gamma_int_le_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ {r : ℝ}, 0 < r → ∀ {α β : ℝ}, 0 ≤ α → 0 ≤ β →
      ∫ γ in Set.Ioi 0, heatKernel (r+1) (γ-α)
          * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
          * heatKernel 1 (γ+β)
        ≤ C * Real.exp (-(α^2+β^2)/4) := by
  obtain ⟨CK, hCKpos, hCK⟩ := frI2_Kbound_uniform
  obtain ⟨Ct, hCtpos, hCt⟩ := gaussian_tail_std_sq_bound
  refine ⟨2 * CK * Ct * (4*Real.pi)^(-1/2 : ℝ), by positivity, ?_⟩
  intro r hr α β hα hβ
  have hL : (0:ℝ) < r + 1 := by linarith
  -- the completed square
  have hsq : ∀ γ : ℝ, γ^2/(4*r) + (γ+β)^2/4
      = ((r+1)/(4*r))*(γ + r*β/(r+1))^2 + β^2/(4*(r+1)) := by
    intro γ
    field_simp [hr.ne', hL.ne']
    ring
  -- the pointwise factorization of the `γ`-dependent Gaussian product
  have hpt : ∀ γ : ℝ, Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)
      = (4*Real.pi)^(-1/2 : ℝ) * (Real.exp (-β^2/(4*(r+1)))
        * Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2)) := by
    intro γ
    have hk1 : heatKernel 1 (γ+β)
        = (4*Real.pi)^(-1/2 : ℝ) * Real.exp (-(γ+β)^2/4) := by
      unfold heatKernel
      rw [show (4:ℝ)*Real.pi*1 = 4*Real.pi by ring]
      congr 1
      ring
    rw [hk1,
      show Real.exp (-γ^2/(4*r)) * ((4*Real.pi)^(-1/2 : ℝ) * Real.exp (-(γ+β)^2/4))
        = (4*Real.pi)^(-1/2 : ℝ)
          * (Real.exp (-γ^2/(4*r)) * Real.exp (-(γ+β)^2/4)) by ring,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    congr 1
    have h2 := hsq γ
    rw [show -β^2/(4*(r+1)) + -((r+1)/(4*r))*(γ + r*β/(r+1))^2
        = -(γ^2/(4*r) + (γ+β)^2/4) by rw [h2]; ring]
    ring
  -- the `γ`-integral: shift then scale
  set cc : ℝ := Real.sqrt ((r+1)/(4*r)) with hcc
  have hccpos : 0 < cc := Real.sqrt_pos.mpr (div_pos hL (by linarith))
  have hcc2 : cc^2 = (r+1)/(4*r) := Real.sq_sqrt (div_nonneg hL.le (by positivity))
  have hstep1 : ∫ γ in Set.Ioi 0, Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)
      = (4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1)))
        * ∫ γ in Set.Ioi 0, Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro γ _
    show Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)
      = (4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1)))
        * Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2)
    rw [hpt γ]
    ring
  have hstep2 : ∫ γ in Set.Ioi 0, Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2)
      = ∫ v in Set.Ioi (r*β/(r+1)), Real.exp (-((r+1)/(4*r))*v^2) := by
    have h := AiryConj.integral_Ioi_add_const
      (fun v => Real.exp (-((r+1)/(4*r))*v^2)) 0 (r*β/(r+1))
    rw [zero_add] at h
    exact h
  have hstep3 : ∫ v in Set.Ioi (r*β/(r+1)), Real.exp (-((r+1)/(4*r))*v^2)
      = cc⁻¹ * ∫ u in Set.Ioi (cc * (r*β/(r+1))), Real.exp (-u^2) := by
    have hcongr : (fun v : ℝ => Real.exp (-((r+1)/(4*r))*v^2))
        = fun v => Real.exp (-(cc * v)^2) := by
      funext v
      congr 1
      rw [mul_pow, hcc2]
      ring
    rw [hcongr]
    have h := MeasureTheory.integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u^2))
      (r*β/(r+1)) hccpos
    rw [smul_eq_mul] at h
    exact h
  -- the cc⁻¹ prefactor (= 2√(r/L))
  have hccinv : cc⁻¹ = 2 * Real.sqrt (r/(r+1)) := by
    rw [hcc]
    have h1 : Real.sqrt ((r+1)/(4*r)) = Real.sqrt (r+1)/(2 * Real.sqrt r) := by
      rw [Real.sqrt_div hL.le]
      congr 1
      rw [show (4:ℝ)*r = 2^2 * r by ring, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2^2),
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [h1, inv_div, Real.sqrt_div hr.le]
    ring
  -- the tail bound with `(1+x)⁻¹ ≤ 1`
  have hx : (0:ℝ) ≤ cc * (r*β/(r+1)) :=
    mul_nonneg hccpos.le (div_nonneg (mul_nonneg hr.le hβ) hL.le)
  have hx2 : (cc * (r*β/(r+1)))^2 = r*β^2/(4*(r+1)) := by
    rw [mul_pow, hcc2]
    field_simp [hr.ne', hL.ne']
  have htail : ∫ u in Set.Ioi (cc * (r*β/(r+1))), Real.exp (-u^2)
      ≤ Ct * Real.exp (-(r*β^2/(4*(r+1)))) := by
    calc ∫ u in Set.Ioi (cc * (r*β/(r+1))), Real.exp (-u^2)
        ≤ Ct * (1 + cc * (r*β/(r+1)))⁻¹ * Real.exp (-(cc * (r*β/(r+1)))^2) :=
          hCt _ hx
      _ ≤ Ct * 1 * Real.exp (-(cc * (r*β/(r+1)))^2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_left _ hCtpos.le
          exact inv_le_one_of_one_le₀ (by linarith [hx])
      _ = Ct * Real.exp (-(r*β^2/(4*(r+1)))) := by
          rw [mul_one]
          congr 1
          rw [hx2]
  -- the `γ`-integral bound, assembled
  have hgamma : ∫ γ in Set.Ioi 0, Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)
      ≤ (4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1))) * cc⁻¹
        * (Ct * Real.exp (-(r*β^2/(4*(r+1))))) := by
    rw [hstep1, hstep2, hstep3]
    rw [show (4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1))) * cc⁻¹
        * (Ct * Real.exp (-(r*β^2/(4*(r+1)))))
        = ((4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1))))
          * (cc⁻¹ * (Ct * Real.exp (-(r*β^2/(4*(r+1)))))) by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr hccpos.le)
  -- integrability inputs for the `γ`-level monotonicity
  have hGint0 : Integrable fun γ : ℝ => Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2) := by
    have h0 := integrable_exp_neg_mul_sq (div_pos hL (by linarith) : (0:ℝ) < (r+1)/(4*r))
    exact h0.comp_add_right (r*β/(r+1))
  have hRHS : IntegrableOn (fun γ : ℝ => (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4))
      * (Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β))) (Set.Ioi 0) := by
    have h1 : Integrable fun γ : ℝ => Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β) := by
      have hcong : (fun γ : ℝ => Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β))
          = fun γ => ((4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1))))
            * Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2) := by
        funext γ
        show Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)
          = ((4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1))))
            * Real.exp (-((r+1)/(4*r))*(γ + r*β/(r+1))^2)
        rw [hpt γ]
        ring
      rw [hcong]
      exact hGint0.const_mul _
    exact (h1.const_mul _).integrableOn
  have hmono : Antitone fun γ : ℝ =>
      gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) := by
    intro a b hab
    apply gaussianTail_mono (by norm_num : (0:ℝ) < 1/2)
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    linarith [hab]
  have hmeas : Measurable fun γ : ℝ => heatKernel (r+1) (γ-α)
      * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
      * heatKernel 1 (γ+β) :=
    (((continuous_heatKernel (r+1)).comp
      (continuous_id.sub continuous_const)).measurable.mul
      (hmono.measurable.div_const _)).mul
      ((continuous_heatKernel 1).comp (continuous_id.add continuous_const)).measurable
  -- the pointwise bound from `frI2_Kbound_uniform`
  have hptbound : ∀ γ ∈ Set.Ioi 0, heatKernel (r+1) (γ-α)
      * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
      * heatKernel 1 (γ+β)
      ≤ (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4))
        * (Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)) := by
    intro γ hγ
    have hγ0 : (0:ℝ) ≤ γ := (Set.mem_Ioi.mp hγ).le
    have h2 := hCK hr hα hγ0
    have h3 := mul_le_mul_of_nonneg_right h2 (heatKernel_pos one_pos (γ+β)).le
    calc heatKernel (r+1) (γ-α)
          * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
          * heatKernel 1 (γ+β)
        ≤ (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4 - γ^2/(4*r)))
          * heatKernel 1 (γ+β) := h3
      _ = (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4))
          * (Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)) := by
          rw [show Real.exp (-α^2/4 - γ^2/(4*r))
              = Real.exp (-α^2/4) * Real.exp (-γ^2/(4*r)) by
            rw [← Real.exp_add]
            congr 1
            ring]
          ring
  have hLHS : IntegrableOn (fun γ : ℝ => heatKernel (r+1) (γ-α)
      * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
      * heatKernel 1 (γ+β)) (Set.Ioi 0) := by
    rw [IntegrableOn]
    apply hRHS.mono' hmeas.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with γ hγ
    have hgT : (0:ℝ) ≤ gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) := by
      unfold gaussianTail
      apply setIntegral_nonneg measurableSet_Ioi
      intro d _
      exact (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg
      (heatKernel_pos hL _).le (div_nonneg hgT (Real.sqrt_nonneg _)))
      (heatKernel_pos one_pos _).le)]
    exact hptbound γ hγ
  -- the prefactor absorption `L^{−1/2}√(r/L) = √r/(r+1) ≤ 1`
  have hsqrtle : (r+1)^(-1/2 : ℝ) * Real.sqrt (r/(r+1)) ≤ 1 := by
    have h1 : (r+1)^(-1/2 : ℝ) = (Real.sqrt (r+1))⁻¹ := by
      rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by norm_num, Real.rpow_neg hL.le,
        Real.sqrt_eq_rpow]
    have h2 : Real.sqrt (r/(r+1)) = Real.sqrt r / Real.sqrt (r+1) :=
      Real.sqrt_div hr.le _
    have h4 : Real.sqrt r ≤ r + 1 := by
      have h5 : Real.sqrt r ≤ Real.sqrt ((r+1)^2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg r, hr])
      rwa [Real.sqrt_sq hL.le] at h5
    have h3 : (Real.sqrt (r+1))⁻¹ * (Real.sqrt r / Real.sqrt (r+1))
        = Real.sqrt r / (r+1) := by
      have h6 : (Real.sqrt (r+1))⁻¹ * (Real.sqrt r * (Real.sqrt (r+1))⁻¹)
          = Real.sqrt r * (r+1)⁻¹ := by
        rw [show (Real.sqrt (r+1))⁻¹ * (Real.sqrt r * (Real.sqrt (r+1))⁻¹)
            = Real.sqrt r * ((Real.sqrt (r+1))⁻¹ * (Real.sqrt (r+1))⁻¹) by ring]
        rw [← mul_inv, Real.mul_self_sqrt hL.le]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact h6
    calc (r+1)^(-1/2 : ℝ) * Real.sqrt (r/(r+1))
        = Real.sqrt r / (r+1) := by rw [h1, h2, h3]
      _ ≤ 1 := (div_le_one hL).mpr h4
  have hC0 : (0:ℝ) ≤ 2 * CK * Ct * (4*Real.pi)^(-1/2 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCKpos.le) hCtpos.le)
      (Real.rpow_nonneg (by positivity) _)
  -- the full assembly
  calc ∫ γ in Set.Ioi 0, heatKernel (r+1) (γ-α)
          * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
          * heatKernel 1 (γ+β)
      ≤ ∫ γ in Set.Ioi 0, (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4))
          * (Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β)) :=
        setIntegral_mono_on hLHS hRHS measurableSet_Ioi hptbound
    _ = (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4))
          * ∫ γ in Set.Ioi 0, Real.exp (-γ^2/(4*r)) * heatKernel 1 (γ+β) :=
        integral_const_mul _ _
    _ ≤ (CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4))
          * ((4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1))) * cc⁻¹
            * (Ct * Real.exp (-(r*β^2/(4*(r+1)))))) :=
        mul_le_mul_of_nonneg_left hgamma (by positivity)
    _ = (2 * CK * Ct * (4*Real.pi)^(-1/2 : ℝ))
          * ((r+1)^(-1/2 : ℝ) * Real.sqrt (r/(r+1)))
          * (Real.exp (-α^2/4) * Real.exp (-β^2/4)) := by
        rw [hccinv]
        rw [show CK * (r+1)^(-1/2 : ℝ) * Real.exp (-α^2/4)
            * ((4*Real.pi)^(-1/2 : ℝ) * Real.exp (-β^2/(4*(r+1)))
              * (2 * Real.sqrt (r/(r+1))) * (Ct * Real.exp (-(r*β^2/(4*(r+1))))))
          = (2 * CK * Ct * (4*Real.pi)^(-1/2 : ℝ)) * ((r+1)^(-1/2 : ℝ)
              * Real.sqrt (r/(r+1)))
            * (Real.exp (-α^2/4) * (Real.exp (-β^2/(4*(r+1)))
              * Real.exp (-(r*β^2/(4*(r+1)))))) by ring]
        rw [show Real.exp (-β^2/(4*(r+1))) * Real.exp (-(r*β^2/(4*(r+1))))
            = Real.exp (-β^2/4) by
          rw [← Real.exp_add]
          congr 1
          field_simp [hL.ne', show (4:ℝ)*(r+1) ≠ 0 from mul_ne_zero (by norm_num) hL.ne']
          ring]
    _ ≤ (2 * CK * Ct * (4*Real.pi)^(-1/2 : ℝ)) * 1
          * (Real.exp (-α^2/4) * Real.exp (-β^2/4)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hsqrtle hC0
    _ = (2 * CK * Ct * (4*Real.pi)^(-1/2 : ℝ)) * Real.exp (-(α^2+β^2)/4) := by
        rw [mul_one, ← Real.exp_add]
        congr 1
        ring

/-- `frJ1` is pointwise nonnegative (heat kernel positive, Gaussian tail
nonnegative, `√(2π) ≥ 0`). -/
theorem frJ1_nonneg (hr : 0 < r) (α β : ℝ) : 0 ≤ frJ1 r α β := by
  have hgT : (0:ℝ) ≤ gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2))) := by
    unfold gaussianTail
    apply setIntegral_nonneg measurableSet_Ioi
    intro d _
    exact (Real.exp_pos _).le
  exact mul_nonneg (heatKernel_pos (by linarith) _).le
    (div_nonneg hgT (Real.sqrt_nonneg _))

/-- `g1Exp M r` is continuous (a plain polynomial — no `rpow`). -/
theorem continuous_g1Exp (M r : ℝ) : Continuous (g1Exp M r) := by
  unfold g1Exp
  fun_prop

/-- `g1Exp M r` is measurable. -/
theorem measurable_g1Exp (M r : ℝ) : Measurable (g1Exp M r) :=
  (continuous_g1Exp M r).measurable

/-- **D1, the pointwise core for `I₁`** (both signs of
`u`): for `α, β ≥ 0`, the `|I₁|` integrand is dominated by the `±` split of
the exponential integrands: on `h1Dom` (i.e. `u = 2M+α−β+S² ≥ 0`) by
`CJ·C0·S^{-1/2}·e^{−H₁}` (B2's `boundJ` times C0's `|Ai| ≤ C0 e^{−(2/3)u^{3/2}}`),
and off it by `CJ·Cn·S^{-1/2}·e^{−G₁}` (B2 times the global `|Ai| ≤ Cn`). -/
theorem frJ1_mul_abs_bAiryKer_le (hr : 0 < r) (M : ℝ)
    {CJ : ℝ} (hCJnn : 0 ≤ CJ) (hCJ : ∀ {α β : ℝ}, 0 ≤ α → 0 ≤ β →
      heatKernel (r+2) (α-β)
        * (gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
            / Real.sqrt (2*Real.pi))
        ≤ CJ * (r+2)^(-1/2 : ℝ) * Real.exp (-α^2/(4*(r+1)) - β^2/4))
    {C0 : ℝ} (hC0 : ∀ {u : ℝ}, 0 ≤ u →
      |airyAiReal u| ≤ C0 * Real.exp (-(2/3)*u^(3/2 : ℝ)))
    {Cn : ℝ} (hCn : ∀ u : ℝ, |airyAiReal u| ≤ Cn)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    frJ1 r α β * |bAiryKer (2+r) (M-β, M+α)|
      ≤ CJ * (r+2)^(-1/2 : ℝ)
          * (C0 * (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β)
            + Cn * (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β)) := by
  have hS : (0:ℝ) < r + 2 := by linarith
  have hbA : |bAiryKer (2+r) (M-β, M+α)|
      = Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M + α - β))
        * |airyAiReal (2*M + α - β + (r+2)^2)| := by
    rw [abs_bAiryKer_apply, show (M-β)+(M+α) = 2*M+α-β by ring,
      show (2+r : ℝ)^2 = (r+2)^2 by ring]
  have hJbound : frJ1 r α β ≤ CJ * (r+2)^(-1/2 : ℝ) * Real.exp (-α^2/(4*(r+1)) - β^2/4) :=
    hCJ hα hβ
  by_cases hu : 0 ≤ 2*M + α - β + (r+2)^2
  · -- the positive-Airy region (`h1Dom`)
    rw [Set.indicator_of_mem (show (α, β) ∈ h1Dom M r from ⟨hα, hβ, hu⟩),
      Set.indicator_of_notMem (show (α, β) ∉ h1MinusDom M r from
        fun h => (not_lt.mpr hu) h.2.2)]
    rw [show CJ * (r+2)^(-1/2 : ℝ) * (C0 * Real.exp (-h1Exp M r (α, β)) + Cn * 0)
        = (CJ * (r+2)^(-1/2 : ℝ)) * C0 * Real.exp (-h1Exp M r (α, β)) by ring]
    have hbA_bound : |bAiryKer (2+r) (M-β, M+α)|
        ≤ Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M + α - β))
          * (C0 * Real.exp (-(2/3)*(2*M + α - β + (r+2)^2)^(3/2 : ℝ))) := by
      rw [hbA]
      exact mul_le_mul_of_nonneg_left (hC0 hu) (Real.exp_pos _).le
    calc frJ1 r α β * |bAiryKer (2+r) (M-β, M+α)|
        ≤ (CJ * (r+2)^(-1/2 : ℝ) * Real.exp (-α^2/(4*(r+1)) - β^2/4))
          * (Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M + α - β))
            * (C0 * Real.exp (-(2/3)*(2*M + α - β + (r+2)^2)^(3/2 : ℝ)))) :=
          mul_le_mul hJbound hbA_bound (abs_nonneg _)
            (mul_nonneg (mul_nonneg hCJnn (Real.rpow_nonneg hS.le _)) (Real.exp_pos _).le)
      _ = (CJ * (r+2)^(-1/2 : ℝ)) * C0 * Real.exp (-h1Exp M r (α, β)) := by
          rw [show (CJ * (r+2)^(-1/2 : ℝ) * Real.exp (-α^2/(4*(r+1)) - β^2/4))
                * (Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M + α - β))
                  * (C0 * Real.exp (-(2/3)*(2*M + α - β + (r+2)^2)^(3/2 : ℝ))))
              = (CJ * (r+2)^(-1/2 : ℝ)) * C0
                * (Real.exp (-α^2/(4*(r+1)) - β^2/4)
                  * Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M + α - β))
                  * Real.exp (-(2/3)*(2*M + α - β + (r+2)^2)^(3/2 : ℝ))) by ring]
          rw [← Real.exp_add, ← Real.exp_add]
          have hexp : -α^2/(4*(r+1)) - β^2/4 + (-(2/3)*(2+r)^3 - (2+r)*(2*M + α - β))
              + -(2/3)*(2*M + α - β + (r+2)^2)^(3/2 : ℝ)
              = -(α^2/(4*(r+1)) + β^2/4 + (r+2)*(2*M + α - β) + (2/3)*(r+2)^3
                + (2/3)*(2*M + α - β + (r+2)^2)^(3/2 : ℝ)) := by ring
          rw [hexp]
          rfl
  · -- the negative-Airy region (`h1MinusDom`)
    have hu' : 2*M + α - β + (r+2)^2 < 0 := not_le.mp hu
    rw [Set.indicator_of_notMem (show (α, β) ∉ h1Dom M r from fun h => hu h.2.2),
      Set.indicator_of_mem (show (α, β) ∈ h1MinusDom M r from ⟨hα, hβ, hu'⟩)]
    rw [show CJ * (r+2)^(-1/2 : ℝ) * (C0 * 0 + Cn * Real.exp (-g1Exp M r (α, β)))
        = (CJ * (r+2)^(-1/2 : ℝ)) * Cn * Real.exp (-g1Exp M r (α, β)) by ring]
    have hbA_bound : |bAiryKer (2+r) (M-β, M+α)|
        ≤ Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M + α - β)) * Cn := by
      rw [hbA]
      exact mul_le_mul_of_nonneg_left (hCn _) (Real.exp_pos _).le
    calc frJ1 r α β * |bAiryKer (2+r) (M-β, M+α)|
        ≤ (CJ * (r+2)^(-1/2 : ℝ) * Real.exp (-α^2/(4*(r+1)) - β^2/4))
          * (Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M + α - β)) * Cn) :=
          mul_le_mul hJbound hbA_bound (abs_nonneg _)
            (mul_nonneg (mul_nonneg hCJnn (Real.rpow_nonneg hS.le _)) (Real.exp_pos _).le)
      _ = (CJ * (r+2)^(-1/2 : ℝ)) * Cn * Real.exp (-g1Exp M r (α, β)) := by
          rw [show (CJ * (r+2)^(-1/2 : ℝ) * Real.exp (-α^2/(4*(r+1)) - β^2/4))
                * (Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M + α - β)) * Cn)
              = (CJ * (r+2)^(-1/2 : ℝ)) * Cn
                * (Real.exp (-α^2/(4*(r+1)) - β^2/4)
                  * Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M + α - β))) by ring]
          rw [← Real.exp_add]
          have hexp : -α^2/(4*(r+1)) - β^2/4 + (-(2/3)*(2+r)^3 - (2+r)*(2*M + α - β))
              = -(α^2/(4*(r+1)) + β^2/4 + (r+2)*(2*M + α - β) + (2/3)*(r+2)^3) := by ring
          rw [hexp]
          rfl

/-- `frJ1 r α ·` is measurable (the Gaussian tail is antitone in `β`, the heat
kernel continuous). -/
theorem measurable_frJ1_snd (hr : 0 < r) (α : ℝ) : Measurable fun β : ℝ => frJ1 r α β := by
  have hmono : Antitone fun β : ℝ =>
      gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2))) := by
    intro a b hab
    apply gaussianTail_mono (by norm_num : (0:ℝ) < 1/2)
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have h1 : (r+1) * a ≤ (r+1) * b := mul_le_mul_of_nonneg_left hab (by linarith)
    linarith [h1]
  exact (((continuous_heatKernel (r+2)).comp
    (continuous_const.sub continuous_id)).measurable).mul
    (hmono.measurable.div_const _)

/-- **D1 helper**: the slice-and-outer quadrant integrability of an
`E`-indicator of `e^{−f}` dominated by a Gaussian product
`K · e^{−c(α−s₁)²} · e^{−d(β−s₂)²}` (the crude dominators behind every `±`
piece; the sharp bounds are the C-packages of `FRExponents.lean`). -/
theorem indExp_quadrant_integrable {E : Set (ℝ × ℝ)} (hE : MeasurableSet E)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {c d K s₁ s₂ : ℝ} (hc : 0 < c) (hd : 0 < d) (hK : 0 ≤ K)
    (hdom : ∀ p ∈ E, Real.exp (-f p)
      ≤ K * (Real.exp (-c * (p.1 - s₁)^2) * Real.exp (-d * (p.2 - s₂)^2))) :
    (∀ α : ℝ, IntegrableOn (fun β : ℝ => E.indicator (fun p => Real.exp (-f p)) (α, β))
        (Set.Ici 0) volume)
    ∧ IntegrableOn (fun α : ℝ => ∫ β in Set.Ici 0, E.indicator (fun p => Real.exp (-f p)) (α, β))
        (Set.Ici 0) volume := by
  have hG2 : Integrable fun β : ℝ => Real.exp (-d * (β - s₂)^2) :=
    (integrable_exp_neg_mul_sq hd).comp_sub_right s₂
  have hG1 : Integrable fun α : ℝ => Real.exp (-c * (α - s₁)^2) :=
    (integrable_exp_neg_mul_sq hc).comp_sub_right s₁
  have hmeas : Measurable fun p : ℝ × ℝ => E.indicator (fun p => Real.exp (-f p)) p := by
    apply Measurable.indicator _ hE
    exact Real.measurable_exp.comp hf.neg
  have hnn : ∀ α β : ℝ, (0:ℝ) ≤ E.indicator (fun p => Real.exp (-f p)) (α, β) :=
    fun α β => Set.indicator_nonneg (fun p _ => (Real.exp_pos _).le) (α, β)
  have hpt : ∀ α β : ℝ, (E.indicator (fun p => Real.exp (-f p)) (α, β))
      ≤ K * (Real.exp (-c * (α - s₁)^2) * Real.exp (-d * (β - s₂)^2)) := by
    intro α β
    by_cases hp : (α, β) ∈ E
    · rw [Set.indicator_of_mem hp]
      exact hdom (α, β) hp
    · rw [Set.indicator_of_notMem hp]
      positivity
  have hslice : ∀ α : ℝ, Integrable (fun β : ℝ => (K * Real.exp (-c * (α - s₁)^2))
      * Real.exp (-d * (β - s₂)^2)) volume := fun α => hG2.const_mul _
  have hsliceInd : ∀ α : ℝ, IntegrableOn (fun β : ℝ => E.indicator (fun p => Real.exp (-f p)) (α, β))
      (Set.Ici 0) volume := by
    intro α
    apply (hslice α).integrableOn.mono' (hmeas.comp measurable_prodMk_left).aestronglyMeasurable
    filter_upwards with β
    show ‖E.indicator (fun p => Real.exp (-f p)) (α, β)‖
      ≤ (K * Real.exp (-c * (α - s₁)^2)) * Real.exp (-d * (β - s₂)^2)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn α β)]
    exact (hpt α β).trans_eq (mul_assoc _ _ _).symm
  refine ⟨hsliceInd, ?_⟩
  · have houterbound : ∀ α : ℝ, (∫ β in Set.Ici 0, E.indicator (fun p => Real.exp (-f p)) (α, β))
        ≤ (K * ∫ β : ℝ, Real.exp (-d * β^2)) * Real.exp (-c * (α - s₁)^2) := by
      intro α
      calc (∫ β in Set.Ici 0, E.indicator (fun p => Real.exp (-f p)) (α, β))
          ≤ ∫ β in Set.Ici 0, (K * Real.exp (-c * (α - s₁)^2)) * Real.exp (-d * (β - s₂)^2) :=
            setIntegral_mono_on (hsliceInd α) ((hslice α).integrableOn)
              measurableSet_Ici (fun β _ => (hpt α β).trans_eq (mul_assoc _ _ _).symm)
        _ = (K * Real.exp (-c * (α - s₁)^2)) * ∫ β in Set.Ici 0, Real.exp (-d * (β - s₂)^2) :=
            integral_const_mul _ _
        _ ≤ (K * Real.exp (-c * (α - s₁)^2)) * ∫ β : ℝ, Real.exp (-d * (β - s₂)^2) :=
            mul_le_mul_of_nonneg_left
              (by have hsub := setIntegral_mono_set hG2.integrableOn
                    (Filter.Eventually.of_forall fun β => (Real.exp_pos _).le)
                    (Filter.Eventually.of_forall fun β (_ : β ∈ Set.Ici 0) => Set.mem_univ β)
                  rwa [setIntegral_univ] at hsub)
              (mul_nonneg hK (Real.exp_pos _).le)
        _ = (K * ∫ β : ℝ, Real.exp (-d * β^2)) * Real.exp (-c * (α - s₁)^2) := by
            rw [MeasureTheory.integral_sub_right_eq_self (μ := volume)
              (fun β : ℝ => Real.exp (-d * β^2)) s₂]
            ring
    have houtermeas : Measurable fun α : ℝ =>
        ∫ β in Set.Ici 0, E.indicator (fun p => Real.exp (-f p)) (α, β) := by
      have hh : (fun α : ℝ => ∫ β in Set.Ici 0, E.indicator (fun p => Real.exp (-f p)) (α, β))
          = fun α => ∫ β : ℝ, (Set.univ ×ˢ Set.Ici 0).indicator
              (E.indicator (fun p => Real.exp (-f p))) (α, β) := by
        funext α
        rw [← MeasureTheory.integral_indicator measurableSet_Ici]
        apply integral_congr_ae
        filter_upwards with β
        by_cases hβ : β ∈ Set.Ici 0
        · rw [Set.indicator_of_mem hβ,
            Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_univ α, hβ⟩)]
        · rw [Set.indicator_of_notMem hβ,
            Set.indicator_of_notMem (fun h => hβ (Set.mem_prod.mp h).2)]
      rw [hh]
      have hsm : StronglyMeasurable fun p : ℝ × ℝ =>
          (Set.univ ×ˢ Set.Ici 0).indicator (E.indicator (fun p => Real.exp (-f p))) p :=
        (hmeas.indicator (MeasurableSet.univ.prod measurableSet_Ici)).stronglyMeasurable
      exact (hsm.integral_prod_right' (ν := volume)).measurable
    apply ((hG1.const_mul _).integrableOn).mono' houtermeas.aestronglyMeasurable
    filter_upwards with α
    rw [Real.norm_eq_abs,
      abs_of_nonneg (setIntegral_nonneg measurableSet_Ici (fun β _ => hnn α β))]
    exact houterbound α

/-- **D1, the `±` domination split for `I₁`**: `|I₁|` is
bounded by `C·S^{-1/2}` times the sum of the positive-Airy `e^{−H₁}` mass on
`h1Dom` and the negative-Airy `e^{−G₁}` mass on `h1MinusDom` (both iterated
quadrant integrals; `C` collects the B2/C0/Airy constants — the **uniform**
packaging: `C` is outside `∀ M r`, via `frI1_Jbound_uniform`). -/
theorem abs_frI1_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {M r : ℝ}, 0 < r →
      |frI1 M r| ≤ C * (r+2)^(-1/2 : ℝ) *
        ((∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
            (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β))
          + (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
            (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β))) := by
  obtain ⟨CJ, hCJpos, hCJ0⟩ := frI1_Jbound_uniform
  obtain ⟨C0, hC0pos, hC0⟩ := airyAiReal_abs_le_exp32
  obtain ⟨Cn, hCn⟩ := airyAiReal_abs_le
  have hCnn : (0:ℝ) ≤ Cn := le_trans (abs_nonneg _) (hCn 0)
  refine ⟨CJ * (C0 + Cn), mul_pos hCJpos (add_pos_of_pos_of_nonneg hC0pos hCnn), ?_⟩
  intro M r hr
  have hCJ : ∀ {α β : ℝ}, 0 ≤ α → 0 ≤ β →
      heatKernel (r+2) (α-β)
        * (gaussianTail (1/2) ((α + (r+1)*β) / Real.sqrt (2*(r+1)*(r+2)))
            / Real.sqrt (2*Real.pi))
        ≤ CJ * (r+2)^(-1/2 : ℝ) * Real.exp (-α^2/(4*(r+1)) - β^2/4) := hCJ0 hr
  have hS : (0:ℝ) < r + 2 := by linarith
  have hL : (0:ℝ) < r + 1 := by linarith
  have hSinv : (0:ℝ) ≤ (r+2)^(-1/2 : ℝ) := Real.rpow_nonneg hS.le _
  -- the `+` indicator's integrabilities (the `exp_neg_h1Exp_le` dominator)
  have hint1 := indExp_quadrant_integrable (measurableSet_h1Dom M r) (measurable_h1Exp M r)
    (inv_pos.mpr (by linarith : (0:ℝ) < 4*(r+1))) (by norm_num : (0:ℝ) < 1/4)
    (K := Real.exp ((r+2)^3/3)) (Real.exp_pos _).le (s₁ := 0) (s₂ := 0) (fun p hp => by
      have h := exp_neg_h1Exp_le hr hp
      rw [sub_zero, sub_zero]
      exact h)
  -- the `−` indicator's integrabilities (the completed-square dominator)
  have hint2 := indExp_quadrant_integrable (measurableSet_h1MinusDom M r) (measurable_g1Exp M r)
    (inv_pos.mpr (by linarith : (0:ℝ) < 4*(r+1))) (by norm_num : (0:ℝ) < 1/4)
    (K := Real.exp ((r+2)*|2*M| + (r+2)^2)) (Real.exp_pos _).le (s₁ := 0) (s₂ := 2*(r+2))
    (fun p hp => by
      obtain ⟨hα, hβ, hu⟩ := hp
      have hSnn : (0:ℝ) ≤ r + 2 := hS.le
      have h1 : -(r+2)*(2*M + p.1 - p.2) ≤ (r+2)*p.2 + (r+2)*|2*M| := by
        have hαr : (0:ℝ) ≤ (r+2)*p.1 := mul_nonneg hSnn hα
        have habs : -(r+2)*(2*M) ≤ (r+2)*|2*M| := by
          calc -(r+2)*(2*M) = (r+2)*(-(2*M)) := by ring
            _ ≤ (r+2)*|2*M| := mul_le_mul_of_nonneg_left (neg_le_abs (2*M)) hSnn
        nlinarith [hαr, habs]
      have hkey : -g1Exp M r p
          ≤ (r+2)*|2*M| + (r+2)^2
            + (-(4*(r+1))⁻¹ * p.1^2 + -(1/4 : ℝ) * (p.2 - 2*(r+2))^2) := by
        have hstep : -g1Exp M r p
            = -(p.1^2/(4*(r+1))) + (-p.2^2/4 + (r+2)*p.2) + (-(r+2)*p.2)
              + (-(r+2)*(2*M + p.1 - p.2)) + (-(2/3)*(r+2)^3) := by
          unfold g1Exp
          ring
        have hsq : -p.2^2/4 + (r+2)*p.2 = (r+2)^2 + -(1/4 : ℝ)*(p.2 - 2*(r+2))^2 := by ring
        have h4 : p.1^2/(4*(r+1)) = (4*(r+1))⁻¹ * p.1^2 := by rw [inv_mul_eq_div]
        rw [hstep]
        nlinarith [h1, hsq, h4, neg_nonpos.mpr
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 2/3) (pow_nonneg hSnn 3))]
      calc Real.exp (-g1Exp M r p)
          ≤ Real.exp ((r+2)*|2*M| + (r+2)^2
              + (-(4*(r+1))⁻¹ * p.1^2 + -(1/4 : ℝ) * (p.2 - 2*(r+2))^2)) :=
            Real.exp_le_exp.mpr hkey
        _ = Real.exp ((r+2)*|2*M| + (r+2)^2)
            * (Real.exp (-(4*(r+1))⁻¹ * (p.1 - 0)^2)
              * Real.exp (-(1/4 : ℝ) * (p.2 - 2*(r+2))^2)) := by
            rw [Real.exp_add, Real.exp_add, Real.exp_add,
              show (-(4*(r+1))⁻¹ : ℝ) * p.1^2 = -(4*(r+1))⁻¹ * (p.1 - 0)^2 by ring])
  -- the `(α, β)` form of `frI1` over the closed quadrant
  have hfr : frI1 M r = ∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
      frJ1 r α β * bAiryKer (2+r) (M-β, M+α) := by
    have hIci : ∀ α : ℝ, (∫ β in Set.Ioi 0, frJ1 r α β * bAiryKer (2+r) (M-β, M+α))
        = ∫ β in Set.Ici 0, frJ1 r α β * bAiryKer (2+r) (M-β, M+α) :=
      fun α => (integral_Ici_eq_integral_Ioi).symm
    rw [frI1_eq hr M, ← integral_Ici_eq_integral_Ioi,
      integral_congr_ae (Filter.Eventually.of_forall hIci)]
  -- the fine dominating function's slice/outer integrabilities
  have hsliceD : ∀ α : ℝ, IntegrableOn
      (fun β : ℝ => CJ * (r+2)^(-1/2 : ℝ)
        * (C0 * (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β)
          + Cn * (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β)))
      (Set.Ici 0) volume := by
    intro α
    have h1 : IntegrableOn (fun β : ℝ => C0 * (h1Dom M r).indicator
        (fun p => Real.exp (-h1Exp M r p)) (α, β)) (Set.Ici 0) volume :=
      ((hint1.1 α).smul C0).congr (Filter.Eventually.of_forall fun β => smul_eq_mul _ _)
    have h2 : IntegrableOn (fun β : ℝ => Cn * (h1MinusDom M r).indicator
        (fun p => Real.exp (-g1Exp M r p)) (α, β)) (Set.Ici 0) volume :=
      ((hint2.1 α).smul Cn).congr (Filter.Eventually.of_forall fun β => smul_eq_mul _ _)
    exact ((h1.add h2).smul (CJ * (r+2)^(-1/2 : ℝ))).congr (Filter.Eventually.of_forall fun β => by
      show (CJ * (r+2)^(-1/2 : ℝ)) • ((C0 * (h1Dom M r).indicator
            (fun p => Real.exp (-h1Exp M r p)) (α, β))
          + (Cn * (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β)))
        = CJ * (r+2)^(-1/2 : ℝ) * (C0 * (h1Dom M r).indicator
            (fun p => Real.exp (-h1Exp M r p)) (α, β)
          + Cn * (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β))
      rw [smul_eq_mul])
  -- the pointwise bound
  have hptbound : ∀ {α β : ℝ}, 0 ≤ α → 0 ≤ β →
      frJ1 r α β * |bAiryKer (2+r) (M-β, M+α)|
        ≤ CJ * (r+2)^(-1/2 : ℝ)
          * (C0 * (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β)
            + Cn * (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β)) :=
    fun hα hβ => frJ1_mul_abs_bAiryKer_le hr M hCJpos.le hCJ hC0 hCn hα hβ
  -- slice integrability of the dominand (level `β`, for `0 ≤ α`)
  have hsliceC : ∀ α : ℝ, 0 ≤ α → IntegrableOn
      (fun β : ℝ => ‖frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖) (Set.Ici 0) volume := by
    intro α hα
    apply (hsliceD α).mono' ?_ ?_
    · have hbk : Measurable fun β : ℝ => bAiryKer (2+r) (M-β, M+α) :=
        ((continuous_bAiryKer (2+r)).comp
          ((continuous_const.sub continuous_id).prodMk continuous_const)).measurable
      exact ((measurable_frJ1_snd hr α).mul hbk).norm.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with β hβ
      rw [norm_norm, norm_mul, Real.norm_eq_abs, abs_of_nonneg (frJ1_nonneg hr α β),
        Real.norm_eq_abs]
      exact hptbound hα (Set.mem_Ici.mp hβ)
  have houterD : IntegrableOn
      (fun α : ℝ => ∫ β in Set.Ici 0, CJ * (r+2)^(-1/2 : ℝ)
        * (C0 * (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β)
          + Cn * (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β)))
      (Set.Ici 0) volume := by
    have h1eq : ∀ α : ℝ, (∫ β in Set.Ici 0, CJ * (r+2)^(-1/2 : ℝ)
          * (C0 * (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β)
            + Cn * (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β)))
        = CJ * (r+2)^(-1/2 : ℝ) * (C0 * (∫ β in Set.Ici 0, (h1Dom M r).indicator
              (fun p => Real.exp (-h1Exp M r p)) (α, β))
            + Cn * (∫ β in Set.Ici 0, (h1MinusDom M r).indicator
              (fun p => Real.exp (-g1Exp M r p)) (α, β))) := by
      intro α
      have h1 : IntegrableOn (fun β : ℝ => C0 * (h1Dom M r).indicator
          (fun p => Real.exp (-h1Exp M r p)) (α, β)) (Set.Ici 0) volume :=
        ((hint1.1 α).smul C0).congr (Filter.Eventually.of_forall fun β => smul_eq_mul _ _)
      have h2 : IntegrableOn (fun β : ℝ => Cn * (h1MinusDom M r).indicator
          (fun p => Real.exp (-g1Exp M r p)) (α, β)) (Set.Ici 0) volume :=
        ((hint2.1 α).smul Cn).congr (Filter.Eventually.of_forall fun β => smul_eq_mul _ _)
      rw [integral_const_mul, integral_add h1 h2, integral_const_mul, integral_const_mul]
    have h1o : IntegrableOn (fun α : ℝ => C0 * (∫ β in Set.Ici 0, (h1Dom M r).indicator
        (fun p => Real.exp (-h1Exp M r p)) (α, β))) (Set.Ici 0) volume :=
      ((hint1.2).smul C0).congr (Filter.Eventually.of_forall fun α => smul_eq_mul _ _)
    have h2o : IntegrableOn (fun α : ℝ => Cn * (∫ β in Set.Ici 0, (h1MinusDom M r).indicator
        (fun p => Real.exp (-g1Exp M r p)) (α, β))) (Set.Ici 0) volume :=
      ((hint2.2).smul Cn).congr (Filter.Eventually.of_forall fun α => smul_eq_mul _ _)
    have hout : IntegrableOn (fun α : ℝ => CJ * (r+2)^(-1/2 : ℝ)
        * (C0 * (∫ β in Set.Ici 0, (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β))
          + Cn * (∫ β in Set.Ici 0, (h1MinusDom M r).indicator
            (fun p => Real.exp (-g1Exp M r p)) (α, β)))) (Set.Ici 0) volume :=
      ((h1o.add h2o).smul (CJ * (r+2)^(-1/2 : ℝ))).congr (Filter.Eventually.of_forall fun α => by
        show (CJ * (r+2)^(-1/2 : ℝ)) • ((C0 * (∫ β in Set.Ici 0, (h1Dom M r).indicator
              (fun p => Real.exp (-h1Exp M r p)) (α, β)))
            + (Cn * (∫ β in Set.Ici 0, (h1MinusDom M r).indicator
              (fun p => Real.exp (-g1Exp M r p)) (α, β))))
          = CJ * (r+2)^(-1/2 : ℝ) * (C0 * (∫ β in Set.Ici 0, (h1Dom M r).indicator
                (fun p => Real.exp (-h1Exp M r p)) (α, β))
              + Cn * (∫ β in Set.Ici 0, (h1MinusDom M r).indicator
                (fun p => Real.exp (-g1Exp M r p)) (α, β)))
        rw [smul_eq_mul])
    exact hout.congr (Filter.Eventually.of_forall fun α => (h1eq α).symm)
  -- the dominand's outer integrability (mono' against the fine dominator)
  have hRHSB : IntegrableOn (fun α : ℝ => ∫ β in Set.Ici 0,
      ‖frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖) (Set.Ici 0) volume := by
    have hmeas : Measurable fun α : ℝ => ∫ β in Set.Ici 0,
        ‖frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖ := by
      have hh : (fun α : ℝ => ∫ β in Set.Ici 0, ‖frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖)
          = fun α => ∫ β : ℝ, (Set.univ ×ˢ Set.Ici 0).indicator
              (fun p : ℝ × ℝ => ‖frJ1 r p.1 p.2 * bAiryKer (2+r) (M-p.2, M+p.1)‖) (α, β) := by
        funext α
        rw [← MeasureTheory.integral_indicator measurableSet_Ici]
        apply integral_congr_ae
        filter_upwards with β
        by_cases hβ : β ∈ Set.Ici 0
        · rw [Set.indicator_of_mem hβ,
            Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_univ α, hβ⟩)]
        · rw [Set.indicator_of_notMem hβ,
            Set.indicator_of_notMem (fun h => hβ (Set.mem_prod.mp h).2)]
      have hgt1 : Measurable (gaussianTail (1/2 : ℝ)) :=
        (show Antitone (gaussianTail (1/2 : ℝ)) from fun a b hab =>
          gaussianTail_mono (by norm_num) hab).measurable
      have hbk : Measurable fun p : ℝ × ℝ => bAiryKer (2+r) (M-p.2, M+p.1) :=
        ((continuous_bAiryKer (2+r)).comp
          ((continuous_const.sub continuous_snd).prodMk
            (continuous_const.add continuous_fst))).measurable
      have hmeas2 : Measurable fun p : ℝ × ℝ =>
          ‖frJ1 r p.1 p.2 * bAiryKer (2+r) (M-p.2, M+p.1)‖ :=
        ((((continuous_heatKernel (r+2)).comp
          (continuous_fst.sub continuous_snd)).measurable.mul
          ((hgt1.comp (by fun_prop :
            Measurable fun p : ℝ × ℝ =>
              (p.1 + (r+1)*p.2) / Real.sqrt (2*(r+1)*(r+2)))).div_const _)).mul hbk).norm
      rw [hh]
      have hsm : StronglyMeasurable fun p : ℝ × ℝ => (Set.univ ×ˢ Set.Ici 0).indicator
          (fun p => ‖frJ1 r p.1 p.2 * bAiryKer (2+r) (M-p.2, M+p.1)‖) p :=
        (hmeas2.indicator (MeasurableSet.univ.prod measurableSet_Ici)).stronglyMeasurable
      exact (hsm.integral_prod_right' (ν := volume)).measurable
    apply houterD.mono' hmeas.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with α hα
    rw [Real.norm_eq_abs,
      abs_of_nonneg (setIntegral_nonneg measurableSet_Ici
        (fun β _ => norm_nonneg _))]
    exact setIntegral_mono_on (hsliceC α (Set.mem_Ici.mp hα)) (hsliceD α) measurableSet_Ici
      (fun β hβ => by
        show ‖frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖ ≤ _
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (frJ1_nonneg hr α β), Real.norm_eq_abs]
        exact hptbound (Set.mem_Ici.mp hα) (Set.mem_Ici.mp hβ))
  -- the outer `‖·‖` level
  have hLHSB : IntegrableOn (fun α : ℝ => ‖∫ β in Set.Ici 0,
      frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖) (Set.Ici 0) volume := by
    have hmeas : Measurable fun α : ℝ => ‖∫ β in Set.Ici 0,
        frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖ := by
      have hmeas0 : Measurable fun α : ℝ => ∫ β in Set.Ici 0,
          frJ1 r α β * bAiryKer (2+r) (M-β, M+α) := by
        have hh : (fun α : ℝ => ∫ β in Set.Ici 0, frJ1 r α β * bAiryKer (2+r) (M-β, M+α))
            = fun α => ∫ β : ℝ, (Set.univ ×ˢ Set.Ici 0).indicator
                (fun p : ℝ × ℝ => frJ1 r p.1 p.2 * bAiryKer (2+r) (M-p.2, M+p.1)) (α, β) := by
          funext α
          rw [← MeasureTheory.integral_indicator measurableSet_Ici]
          apply integral_congr_ae
          filter_upwards with β
          by_cases hβ : β ∈ Set.Ici 0
          · rw [Set.indicator_of_mem hβ,
              Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_univ α, hβ⟩)]
          · rw [Set.indicator_of_notMem hβ,
              Set.indicator_of_notMem (fun h => hβ (Set.mem_prod.mp h).2)]
        have hgt1 : Measurable (gaussianTail (1/2 : ℝ)) :=
          (show Antitone (gaussianTail (1/2 : ℝ)) from fun a b hab =>
            gaussianTail_mono (by norm_num) hab).measurable
        have hbk : Measurable fun p : ℝ × ℝ => bAiryKer (2+r) (M-p.2, M+p.1) :=
          ((continuous_bAiryKer (2+r)).comp
            ((continuous_const.sub continuous_snd).prodMk
              (continuous_const.add continuous_fst))).measurable
        have hmeas2 : Measurable fun p : ℝ × ℝ =>
            frJ1 r p.1 p.2 * bAiryKer (2+r) (M-p.2, M+p.1) :=
          ((((continuous_heatKernel (r+2)).comp
            (continuous_fst.sub continuous_snd)).measurable.mul
            ((hgt1.comp (by fun_prop :
              Measurable fun p : ℝ × ℝ =>
                (p.1 + (r+1)*p.2) / Real.sqrt (2*(r+1)*(r+2)))).div_const _)).mul hbk)
        rw [hh]
        have hsm : StronglyMeasurable fun p : ℝ × ℝ => (Set.univ ×ˢ Set.Ici 0).indicator
            (fun p => frJ1 r p.1 p.2 * bAiryKer (2+r) (M-p.2, M+p.1)) p :=
          (hmeas2.indicator (MeasurableSet.univ.prod measurableSet_Ici)).stronglyMeasurable
        exact (hsm.integral_prod_right' (ν := volume)).measurable
      exact hmeas0.norm
    apply hRHSB.mono' hmeas.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with α _
    calc ‖‖∫ β in Set.Ici 0, frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖‖
        = ‖∫ β in Set.Ici 0, frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖ := norm_norm _
      _ ≤ ∫ β in Set.Ici 0, ‖frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖ :=
          norm_integral_le_integral_norm _
  -- the assembly
  calc |frI1 M r|
      = ‖∫ α in Set.Ici 0, ∫ β in Set.Ici 0, frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖ := by
        rw [hfr, Real.norm_eq_abs]
    _ ≤ ∫ α in Set.Ici 0, ‖∫ β in Set.Ici 0, frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ α in Set.Ici 0, ∫ β in Set.Ici 0, ‖frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖ :=
        setIntegral_mono_on hLHSB hRHSB measurableSet_Ici (fun α _ =>
          norm_integral_le_integral_norm _)
    _ ≤ ∫ α in Set.Ici 0, ∫ β in Set.Ici 0, CJ * (r+2)^(-1/2 : ℝ)
          * (C0 * (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β)
            + Cn * (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β)) :=
        setIntegral_mono_on hRHSB houterD measurableSet_Ici (fun α hα =>
          setIntegral_mono_on (hsliceC α (Set.mem_Ici.mp hα)) (hsliceD α) measurableSet_Ici
            (fun β hβ => by
              show ‖frJ1 r α β * bAiryKer (2+r) (M-β, M+α)‖ ≤ _
              rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (frJ1_nonneg hr α β),
                Real.norm_eq_abs]
              exact hptbound (Set.mem_Ici.mp hα) (Set.mem_Ici.mp hβ)))
    _ = CJ * (r+2)^(-1/2 : ℝ)
          * (C0 * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h1Dom M r).indicator
                (fun p => Real.exp (-h1Exp M r p)) (α, β))
            + Cn * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h1MinusDom M r).indicator
                (fun p => Real.exp (-g1Exp M r p)) (α, β))) := by
        have hinner : ∀ α : ℝ, (∫ β in Set.Ici 0, CJ * (r+2)^(-1/2 : ℝ)
              * (C0 * (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β)
                + Cn * (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β)))
            = CJ * (r+2)^(-1/2 : ℝ)
              * (C0 * (∫ β in Set.Ici 0, (h1Dom M r).indicator
                    (fun p => Real.exp (-h1Exp M r p)) (α, β))
                + Cn * (∫ β in Set.Ici 0, (h1MinusDom M r).indicator
                    (fun p => Real.exp (-g1Exp M r p)) (α, β))) := by
          intro α
          have h1 : IntegrableOn (fun β : ℝ => C0 * (h1Dom M r).indicator
              (fun p => Real.exp (-h1Exp M r p)) (α, β)) (Set.Ici 0) volume :=
            ((hint1.1 α).smul C0).congr (Filter.Eventually.of_forall fun β => smul_eq_mul _ _)
          have h2 : IntegrableOn (fun β : ℝ => Cn * (h1MinusDom M r).indicator
              (fun p => Real.exp (-g1Exp M r p)) (α, β)) (Set.Ici 0) volume :=
            ((hint2.1 α).smul Cn).congr (Filter.Eventually.of_forall fun β => smul_eq_mul _ _)
          rw [integral_const_mul, integral_add h1 h2, integral_const_mul, integral_const_mul]
        rw [setIntegral_congr_fun measurableSet_Ici (fun α _ => hinner α)]
        have h1o : IntegrableOn (fun α : ℝ => C0 * (∫ β in Set.Ici 0, (h1Dom M r).indicator
            (fun p => Real.exp (-h1Exp M r p)) (α, β))) (Set.Ici 0) volume :=
          ((hint1.2).smul C0).congr (Filter.Eventually.of_forall fun α => smul_eq_mul _ _)
        have h2o : IntegrableOn (fun α : ℝ => Cn * (∫ β in Set.Ici 0, (h1MinusDom M r).indicator
            (fun p => Real.exp (-g1Exp M r p)) (α, β))) (Set.Ici 0) volume :=
          ((hint2.2).smul Cn).congr (Filter.Eventually.of_forall fun α => smul_eq_mul _ _)
        rw [integral_const_mul, integral_add h1o h2o, integral_const_mul, integral_const_mul]
    _ ≤ (CJ * (C0 + Cn)) * (r+2)^(-1/2 : ℝ)
          * ((∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h1Dom M r).indicator
                (fun p => Real.exp (-h1Exp M r p)) (α, β))
            + (∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h1MinusDom M r).indicator
                (fun p => Real.exp (-g1Exp M r p)) (α, β))) := by
        have hJ1nn : (0:ℝ) ≤ ∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
            (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β) :=
          setIntegral_nonneg measurableSet_Ici (fun α _ =>
            setIntegral_nonneg measurableSet_Ici (fun β _ =>
              Set.indicator_nonneg (fun p _ => (Real.exp_pos _).le) (α, β)))
        have hJ2nn : (0:ℝ) ≤ ∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
            (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β) :=
          setIntegral_nonneg measurableSet_Ici (fun α _ =>
            setIntegral_nonneg measurableSet_Ici (fun β _ =>
              Set.indicator_nonneg (fun p _ => (Real.exp_pos _).le) (α, β)))
        have hle : CJ * (r+2)^(-1/2 : ℝ)
            * (C0 * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h1Dom M r).indicator
                  (fun p => Real.exp (-h1Exp M r p)) (α, β))
              + Cn * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h1MinusDom M r).indicator
                  (fun p => Real.exp (-g1Exp M r p)) (α, β)))
            ≤ CJ * (r+2)^(-1/2 : ℝ) * ((C0 + Cn) * ((∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
                  (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β))
                + (∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h1MinusDom M r).indicator
                  (fun p => Real.exp (-g1Exp M r p)) (α, β)))) :=
          mul_le_mul_of_nonneg_left (by nlinarith [hJ1nn, hJ2nn, hC0pos.le, hCnn])
            (mul_nonneg hCJpos.le hSinv)
        exact hle.trans_eq (by ring)

/-- `frK2` is pointwise nonnegative. -/
theorem frK2_nonneg (hr : 0 < r) (α γ : ℝ) : 0 ≤ frK2 r α γ := by
  have hgT : (0:ℝ) ≤ gaussianTail (1/2) ((r*α+γ) / Real.sqrt (2*r*(r+1))) := by
    unfold gaussianTail
    apply setIntegral_nonneg measurableSet_Ioi
    intro d _
    exact (Real.exp_pos _).le
  exact mul_nonneg (heatKernel_pos (by linarith) _).le (div_nonneg hgT (Real.sqrt_nonneg _))

/-- The `γ`-integrated `I₂` inner factor is nonnegative (integral of a nonneg
product). -/
theorem frI2_γint_nonneg (hr : 0 < r) (α β : ℝ) :
    0 ≤ ∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β) :=
  setIntegral_nonneg measurableSet_Ioi
    (fun γ _ => mul_nonneg (frK2_nonneg hr α γ) (heatKernel_pos one_pos _).le)

/-- **D1, the pointwise core for `I₂`** (positive and
negative regions): for `α, β ≥ 0`, writing `u₂ = 2M−α−β+S²`
(`= w + x + S²`), the `|I₂|` integrand (after the B5 `γ`-integration) is
dominated by the `±` split: on `h2Dom` by `C0·e^{−H̃₂}` (C0's positive-Airy
bound) and off it by `Cn·e^{−G̃₂}` (the global `|Ai| ≤ Cn`). -/
theorem exp_quadr_mul_abs_bAiryKer2_le (hr : 0 < r) (M : ℝ)
    {C0 : ℝ} (hC0 : ∀ {u : ℝ}, 0 ≤ u →
      |airyAiReal u| ≤ C0 * Real.exp (-(2/3)*u^(3/2 : ℝ)))
    {Cn : ℝ} (hCn : ∀ u : ℝ, |airyAiReal u| ≤ Cn)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Real.exp (-(α^2+β^2)/4) * |bAiryKer (2+r) (M-β, M-α)|
      ≤ C0 * (h2Dom M r).indicator (fun p => Real.exp (-h2Tilde M r p)) (α, β)
        + Cn * (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β) := by
  have hS : (0:ℝ) < r + 2 := by linarith
  have hbA : |bAiryKer (2+r) (M-β, M-α)|
      = Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M - α - β))
        * |airyAiReal (2*M - α - β + (r+2)^2)| := by
    rw [abs_bAiryKer_apply, show (M-β)+(M-α) = 2*M-α-β by ring,
      show (2+r : ℝ)^2 = (r+2)^2 by ring]
  by_cases hu : 0 ≤ 2*M - α - β + (r+2)^2
  · -- the positive-Airy region (`h2Dom`)
    rw [Set.indicator_of_mem (show (α, β) ∈ h2Dom M r from ⟨hα, hβ, hu⟩),
      Set.indicator_of_notMem (show (α, β) ∉ h2MinusDom M r from fun h => (not_lt.mpr hu) h.2.2)]
    rw [show C0 * Real.exp (-h2Tilde M r (α, β)) + Cn * 0
        = C0 * Real.exp (-h2Tilde M r (α, β)) by ring]
    have hbA_bound : |bAiryKer (2+r) (M-β, M-α)|
        ≤ Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M - α - β))
          * (C0 * Real.exp (-(2/3)*(2*M - α - β + (r+2)^2)^(3/2 : ℝ))) := by
      rw [hbA]
      exact mul_le_mul_of_nonneg_left (hC0 hu) (Real.exp_pos _).le
    calc Real.exp (-(α^2+β^2)/4) * |bAiryKer (2+r) (M-β, M-α)|
        ≤ Real.exp (-(α^2+β^2)/4)
          * (Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M - α - β))
            * (C0 * Real.exp (-(2/3)*(2*M - α - β + (r+2)^2)^(3/2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hbA_bound (Real.exp_pos _).le
      _ = C0 * Real.exp (-h2Tilde M r (α, β)) := by
          rw [show Real.exp (-(α^2+β^2)/4)
                * (Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M - α - β))
                  * (C0 * Real.exp (-(2/3)*(2*M - α - β + (r+2)^2)^(3/2 : ℝ))))
              = C0 * (Real.exp (-(α^2+β^2)/4)
                  * Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M - α - β))
                  * Real.exp (-(2/3)*(2*M - α - β + (r+2)^2)^(3/2 : ℝ))) by ring]
          rw [← Real.exp_add, ← Real.exp_add]
          have hexp : -(α^2+β^2)/4 + (-(2/3)*(2+r)^3 - (2+r)*(2*M - α - β))
              + -(2/3)*(2*M - α - β + (r+2)^2)^(3/2 : ℝ)
              = -((α^2 + β^2)/4 + (r+2)*(2*M - α - β) + (2/3)*(r+2)^3
                + (2/3)*(2*M - α - β + (r+2)^2)^(3/2 : ℝ)) := by ring
          rw [hexp]
          rfl
  · -- the negative-Airy region (`h2MinusDom`)
    have hu' : 2*M - α - β + (r+2)^2 < 0 := not_le.mp hu
    rw [Set.indicator_of_notMem (show (α, β) ∉ h2Dom M r from fun h => hu h.2.2),
      Set.indicator_of_mem (show (α, β) ∈ h2MinusDom M r from ⟨hα, hβ, hu'⟩)]
    rw [show C0 * 0 + Cn * Real.exp (-g2Tilde M r (α, β))
        = Cn * Real.exp (-g2Tilde M r (α, β)) by ring]
    have hbA_bound : |bAiryKer (2+r) (M-β, M-α)|
        ≤ Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M - α - β)) * Cn := by
      rw [hbA]
      exact mul_le_mul_of_nonneg_left (hCn _) (Real.exp_pos _).le
    calc Real.exp (-(α^2+β^2)/4) * |bAiryKer (2+r) (M-β, M-α)|
        ≤ Real.exp (-(α^2+β^2)/4)
          * (Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M - α - β)) * Cn) :=
          mul_le_mul_of_nonneg_left hbA_bound (Real.exp_pos _).le
      _ = Cn * Real.exp (-g2Tilde M r (α, β)) := by
          rw [show Real.exp (-(α^2+β^2)/4)
                * (Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M - α - β)) * Cn)
              = Cn * (Real.exp (-(α^2+β^2)/4)
                  * Real.exp (-(2/3)*(2+r)^3 - (2+r)*(2*M - α - β))) by ring]
          rw [← Real.exp_add]
          have hexp : -(α^2+β^2)/4 + (-(2/3)*(2+r)^3 - (2+r)*(2*M - α - β))
              = -((α^2 + β^2)/4 + (r+2)*(2*M - α - β) + (2/3)*(r+2)^3) := by ring
          rw [hexp]
          rfl

/-- The γ-integrated `I₂` inner factor is measurable in `β` (fixed `α`). -/
theorem measurable_frI2_γint_snd (α : ℝ) :
    Measurable fun β : ℝ => ∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β) := by
  have hh : (fun β : ℝ => ∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
      = fun β => ∫ γ : ℝ, (Set.univ ×ˢ Set.Ioi 0).indicator
          (fun q : ℝ × ℝ => frK2 r α q.2 * heatKernel 1 (q.2 + q.1)) (β, γ) := by
    funext β
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with γ
    by_cases hγ : γ ∈ Set.Ioi 0
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_univ β, hγ⟩)]
    · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem (fun h => hγ (Set.mem_prod.mp h).2)]
  have hgt1 : Measurable (gaussianTail (1/2 : ℝ)) :=
    (show Antitone (gaussianTail (1/2 : ℝ)) from fun a b hab =>
      gaussianTail_mono (by norm_num) hab).measurable
  have hmeas2 : Measurable fun q : ℝ × ℝ => frK2 r α q.2 * heatKernel 1 (q.2 + q.1) := by
    have hfk : Measurable fun q : ℝ × ℝ => frK2 r α q.2 := by
      have h1 : Measurable fun q : ℝ × ℝ => heatKernel (r+1) (q.2 - α) :=
        ((continuous_heatKernel (r+1)).comp (continuous_snd.sub continuous_const)).measurable
      have h2 : Measurable fun q : ℝ × ℝ =>
          gaussianTail (1/2) ((r*α + q.2)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi) :=
        (hgt1.comp (by fun_prop : Measurable fun q : ℝ × ℝ =>
          (r*α + q.2)/Real.sqrt (2*r*(r+1)))).div_const _
      exact h1.mul h2
    exact hfk.mul (((continuous_heatKernel 1).comp (continuous_snd.add continuous_fst)).measurable)
  rw [hh]
  have hsm : StronglyMeasurable fun q : ℝ × ℝ => (Set.univ ×ˢ Set.Ioi 0).indicator
      (fun q : ℝ × ℝ => frK2 r α q.2 * heatKernel 1 (q.2 + q.1)) q :=
    (hmeas2.indicator (MeasurableSet.univ.prod measurableSet_Ioi)).stronglyMeasurable
  exact (hsm.integral_prod_right' (ν := volume)).measurable

/-- The γ-integrated `I₂` inner factor is measurable in `(α, β)`. -/
theorem measurable_frI2_γint_pair :
    Measurable fun p : ℝ × ℝ => ∫ γ in Set.Ioi 0, frK2 r p.1 γ * heatKernel 1 (γ + p.2) := by
  have hh : (fun p : ℝ × ℝ => ∫ γ in Set.Ioi 0, frK2 r p.1 γ * heatKernel 1 (γ + p.2))
      = fun p => ∫ γ : ℝ, (Set.univ ×ˢ Set.Ioi 0).indicator
          (fun q : (ℝ × ℝ) × ℝ => frK2 r q.1.1 q.2 * heatKernel 1 (q.2 + q.1.2)) (p, γ) := by
    funext p
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with γ
    by_cases hγ : γ ∈ Set.Ioi 0
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_univ p, hγ⟩)]
    · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem (fun h => hγ (Set.mem_prod.mp h).2)]
  have hgt1 : Measurable (gaussianTail (1/2 : ℝ)) :=
    (show Antitone (gaussianTail (1/2 : ℝ)) from fun a b hab =>
      gaussianTail_mono (by norm_num) hab).measurable
  have hmeas3 : Measurable fun q : (ℝ × ℝ) × ℝ =>
      frK2 r q.1.1 q.2 * heatKernel 1 (q.2 + q.1.2) := by
    have hfk : Measurable fun q : (ℝ × ℝ) × ℝ => frK2 r q.1.1 q.2 := by
      have h1 : Measurable fun q : (ℝ × ℝ) × ℝ => heatKernel (r+1) (q.2 - q.1.1) :=
        ((continuous_heatKernel (r+1)).comp (continuous_snd.sub
          (continuous_fst.comp continuous_fst))).measurable
      have h2 : Measurable fun q : (ℝ × ℝ) × ℝ =>
          gaussianTail (1/2) ((r*q.1.1 + q.2)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi) :=
        (hgt1.comp (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ =>
          (r*q.1.1 + q.2)/Real.sqrt (2*r*(r+1)))).div_const _
      exact h1.mul h2
    have hk2 : Measurable fun q : (ℝ × ℝ) × ℝ => heatKernel 1 (q.2 + q.1.2) :=
      ((continuous_heatKernel 1).comp
        (continuous_snd.add (continuous_snd.comp continuous_fst))).measurable
    exact hfk.mul hk2
  rw [hh]
  have hsm : StronglyMeasurable fun q : (ℝ × ℝ) × ℝ => (Set.univ ×ˢ Set.Ioi 0).indicator
      (fun q : (ℝ × ℝ) × ℝ => frK2 r q.1.1 q.2 * heatKernel 1 (q.2 + q.1.2)) q :=
    (hmeas3.indicator (MeasurableSet.univ.prod measurableSet_Ioi)).stronglyMeasurable
  exact (hsm.integral_prod_right' (ν := volume)).measurable

/-- **D1, the `±` domination split for `I₂`**: `|I₂|` is
bounded by `C` times the sum of the positive-Airy `e^{−H̃₂}` mass on `h2Dom` and
the negative-Airy `e^{−G̃₂}` mass on `h2MinusDom` (both iterated quadrant
integrals; `C` collects the B5/C0/Airy constants — note the `L^{-1/2}` prefactor
is already absorbed inside B5's `frI2_gamma_int_le`; the **uniform** packaging:
`C` is outside `∀ M r`, via `frI2_gamma_int_le_uniform`). -/
theorem abs_frI2_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {M r : ℝ}, 0 < r →
      |frI2 M r| ≤ C *
        ((∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
            (h2Dom M r).indicator (fun p => Real.exp (-h2Tilde M r p)) (α, β))
          + (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
            (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β))) := by
  obtain ⟨Cγ, hCγpos, hCγ0⟩ := frI2_gamma_int_le_uniform
  obtain ⟨C0, hC0pos, hC0⟩ := airyAiReal_abs_le_exp32
  obtain ⟨Cn, hCn⟩ := airyAiReal_abs_le
  have hCnn : (0:ℝ) ≤ Cn := le_trans (abs_nonneg _) (hCn 0)
  refine ⟨Cγ * (C0 + Cn), mul_pos hCγpos (add_pos_of_pos_of_nonneg hC0pos hCnn), ?_⟩
  intro M r hr
  have hCγ : ∀ {α β : ℝ}, 0 ≤ α → 0 ≤ β →
      ∫ γ in Set.Ioi 0, heatKernel (r+1) (γ-α)
          * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
          * heatKernel 1 (γ+β)
        ≤ Cγ * Real.exp (-(α^2+β^2)/4) := hCγ0 hr
  -- the `+` indicator's integrabilities (crude dominator: `h2Tilde ≥ (α²+β²)/4 − S³/3`
  -- on `h2Dom`)
  have hint3 := indExp_quadrant_integrable (measurableSet_h2Dom M r) (continuous_h2Tilde M r).measurable
    (by norm_num : (0:ℝ) < 1/4) (by norm_num : (0:ℝ) < 1/4)
    (K := Real.exp ((r+2)^3/3)) (Real.exp_pos _).le (s₁ := 0) (s₂ := 0) (fun p hp => by
      obtain ⟨hα, hβ, hu⟩ := hp
      have hSnn : (0:ℝ) ≤ r + 2 := by linarith
      have hkey : -h2Tilde M r p ≤ (r+2)^3/3 + (-(1/4 : ℝ) * p.1^2 + -(1/4 : ℝ) * p.2^2) := by
        unfold h2Tilde
        have hrad : (0:ℝ) ≤ (2/3)*(2*M - p.1 - p.2 + (r+2)^2)^(3/2 : ℝ) :=
          mul_nonneg (by norm_num) (Real.rpow_nonneg hu _)
        have hlin : -(r+2)^3 ≤ (r+2)*(2*M - p.1 - p.2) := by
          have hu2 : (0:ℝ) ≤ (r+2)*(2*M - p.1 - p.2 + (r+2)^2) := mul_nonneg hSnn hu
          nlinarith [hu2, sq_nonneg (r+2)]
        nlinarith [hrad, hlin, sq_nonneg p.1, sq_nonneg p.2]
      calc Real.exp (-h2Tilde M r p)
          ≤ Real.exp ((r+2)^3/3 + (-(1/4 : ℝ) * p.1^2 + -(1/4 : ℝ) * p.2^2)) :=
            Real.exp_le_exp.mpr hkey
        _ = Real.exp ((r+2)^3/3)
            * (Real.exp (-(1/4 : ℝ) * (p.1 - 0)^2) * Real.exp (-(1/4 : ℝ) * (p.2 - 0)^2)) := by
            rw [Real.exp_add, Real.exp_add,
              show (-(1/4 : ℝ)) * p.1^2 = -(1/4 : ℝ) * (p.1 - 0)^2 by ring,
              show (-(1/4 : ℝ)) * p.2^2 = -(1/4 : ℝ) * (p.2 - 0)^2 by ring])
  -- the `−` indicator's integrabilities (the completed-square dominator)
  have hint4 := indExp_quadrant_integrable (measurableSet_h2MinusDom M r) (continuous_g2Tilde M r).measurable
    (by norm_num : (0:ℝ) < 1/4) (by norm_num : (0:ℝ) < 1/4)
    (K := Real.exp ((r+2)*|2*M| + 2*(r+2)^2)) (Real.exp_pos _).le (s₁ := 2*(r+2)) (s₂ := 2*(r+2))
    (fun p hp => by
      obtain ⟨hα, hβ, -⟩ := hp
      have hSnn : (0:ℝ) ≤ r + 2 := by linarith
      have hkey : -g2Tilde M r p
          ≤ (r+2)*|2*M| + 2*(r+2)^2
            + (-(1/4 : ℝ) * (p.1 - 2*(r+2))^2 + -(1/4 : ℝ) * (p.2 - 2*(r+2))^2) := by
        unfold g2Tilde
        have h1 : -(r+2)*(2*M - p.1 - p.2) ≤ (r+2)*(p.1 + p.2) + (r+2)*|2*M| := by
          have habs : -(r+2)*(2*M) ≤ (r+2)*|2*M| := by
            calc -(r+2)*(2*M) = (r+2)*(-(2*M)) := by ring
              _ ≤ (r+2)*|2*M| := mul_le_mul_of_nonneg_left (neg_le_abs (2*M)) hSnn
          nlinarith [habs]
        have h2 : -(p.1^2 + p.2^2)/4 + (r+2)*(p.1 + p.2)
            = 2*(r+2)^2 + (-(1/4 : ℝ)*(p.1 - 2*(r+2))^2 + -(1/4 : ℝ)*(p.2 - 2*(r+2))^2) := by ring
        nlinarith [h1, h2, neg_nonpos.mpr (mul_nonneg (by norm_num : (0:ℝ) ≤ 2/3)
          (pow_nonneg hSnn 3))]
      calc Real.exp (-g2Tilde M r p)
          ≤ Real.exp ((r+2)*|2*M| + 2*(r+2)^2
              + (-(1/4 : ℝ) * (p.1 - 2*(r+2))^2 + -(1/4 : ℝ) * (p.2 - 2*(r+2))^2)) :=
            Real.exp_le_exp.mpr hkey
        _ = Real.exp ((r+2)*|2*M| + 2*(r+2)^2)
            * (Real.exp (-(1/4 : ℝ) * (p.1 - 2*(r+2))^2)
              * Real.exp (-(1/4 : ℝ) * (p.2 - 2*(r+2))^2)) := by
            rw [Real.exp_add, Real.exp_add, Real.exp_add])
  -- the `(α, β)` form of `frI2` over the closed quadrant
  have hfr2 : frI2 M r = ∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
      (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β)) * bAiryKer (2+r) (M-β, M-α) := by
    have hIci : ∀ α : ℝ, (∫ β in Set.Ioi 0, (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
        * bAiryKer (2+r) (M-β, M-α))
        = ∫ β in Set.Ici 0, (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
          * bAiryKer (2+r) (M-β, M-α) :=
      fun α => (integral_Ici_eq_integral_Ioi).symm
    rw [frI2_eq hr M, ← integral_Ici_eq_integral_Ioi,
      integral_congr_ae (Filter.Eventually.of_forall hIci)]
  -- the pointwise bound (B5's γ-integration consumed)
  have hpt2 : ∀ {α β : ℝ}, 0 ≤ α → 0 ≤ β →
      (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β)) * |bAiryKer (2+r) (M-β, M-α)|
        ≤ Cγ * (C0 * (h2Dom M r).indicator (fun p => Real.exp (-h2Tilde M r p)) (α, β)
          + Cn * (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β)) := by
    intro α β hα hβ
    have hcong : (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
        = ∫ γ in Set.Ioi 0, heatKernel (r+1) (γ-α)
          * (gaussianTail (1/2) ((r*α+γ)/Real.sqrt (2*r*(r+1))) / Real.sqrt (2*Real.pi))
          * heatKernel 1 (γ+β) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro γ _
      rfl
    calc (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β)) * |bAiryKer (2+r) (M-β, M-α)|
        ≤ (Cγ * Real.exp (-(α^2+β^2)/4)) * |bAiryKer (2+r) (M-β, M-α)| :=
          mul_le_mul_of_nonneg_right (by rw [hcong]; exact hCγ hα hβ) (abs_nonneg _)
      _ = Cγ * (Real.exp (-(α^2+β^2)/4) * |bAiryKer (2+r) (M-β, M-α)|) := by ring
      _ ≤ Cγ * (C0 * (h2Dom M r).indicator (fun p => Real.exp (-h2Tilde M r p)) (α, β)
          + Cn * (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β)) :=
          mul_le_mul_of_nonneg_left
            (exp_quadr_mul_abs_bAiryKer2_le hr M hC0 hCn hα hβ) hCγpos.le
  -- slice integrability of the fine dominator (level `β`)
  have hsliceD2 : ∀ α : ℝ, IntegrableOn
      (fun β : ℝ => Cγ * (C0 * (h2Dom M r).indicator (fun p => Real.exp (-h2Tilde M r p)) (α, β)
          + Cn * (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β)))
      (Set.Ici 0) volume := by
    intro α
    have h1 : IntegrableOn (fun β : ℝ => C0 * (h2Dom M r).indicator
        (fun p => Real.exp (-h2Tilde M r p)) (α, β)) (Set.Ici 0) volume :=
      ((hint3.1 α).smul C0).congr (Filter.Eventually.of_forall fun β => smul_eq_mul _ _)
    have h2 : IntegrableOn (fun β : ℝ => Cn * (h2MinusDom M r).indicator
        (fun p => Real.exp (-g2Tilde M r p)) (α, β)) (Set.Ici 0) volume :=
      ((hint4.1 α).smul Cn).congr (Filter.Eventually.of_forall fun β => smul_eq_mul _ _)
    exact ((h1.add h2).smul Cγ).congr (Filter.Eventually.of_forall fun β => by
      show Cγ • ((C0 * (h2Dom M r).indicator (fun p => Real.exp (-h2Tilde M r p)) (α, β))
          + (Cn * (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β)))
        = Cγ * (C0 * (h2Dom M r).indicator (fun p => Real.exp (-h2Tilde M r p)) (α, β)
          + Cn * (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β))
      rw [smul_eq_mul])
  -- slice integrability of the dominand (level `β`, for `0 ≤ α`)
  have hsliceC2 : ∀ α : ℝ, 0 ≤ α → IntegrableOn
      (fun β : ℝ => ‖(∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
        * bAiryKer (2+r) (M-β, M-α)‖) (Set.Ici 0) volume := by
    intro α hα
    apply (hsliceD2 α).mono' ?_ ?_
    · have hbk : Measurable fun β : ℝ => bAiryKer (2+r) (M-β, M-α) :=
        ((continuous_bAiryKer (2+r)).comp
          ((continuous_const.sub continuous_id).prodMk continuous_const)).measurable
      exact ((measurable_frI2_γint_snd α).mul hbk).norm.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with β hβ
      rw [norm_norm, norm_mul, Real.norm_eq_abs, abs_of_nonneg (frI2_γint_nonneg hr α β),
        Real.norm_eq_abs]
      exact hpt2 hα (Set.mem_Ici.mp hβ)
  -- outer integrability of the fine dominator (level `α`)
  have houterD2 : IntegrableOn
      (fun α : ℝ => ∫ β in Set.Ici 0, Cγ * (C0 * (h2Dom M r).indicator
          (fun p => Real.exp (-h2Tilde M r p)) (α, β)
          + Cn * (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β)))
      (Set.Ici 0) volume := by
    have h1eq : ∀ α : ℝ, (∫ β in Set.Ici 0, Cγ * (C0 * (h2Dom M r).indicator
            (fun p => Real.exp (-h2Tilde M r p)) (α, β)
            + Cn * (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β)))
        = Cγ * (C0 * (∫ β in Set.Ici 0, (h2Dom M r).indicator
              (fun p => Real.exp (-h2Tilde M r p)) (α, β))
            + Cn * (∫ β in Set.Ici 0, (h2MinusDom M r).indicator
              (fun p => Real.exp (-g2Tilde M r p)) (α, β))) := by
      intro α
      have h1 : IntegrableOn (fun β : ℝ => C0 * (h2Dom M r).indicator
          (fun p => Real.exp (-h2Tilde M r p)) (α, β)) (Set.Ici 0) volume :=
        ((hint3.1 α).smul C0).congr (Filter.Eventually.of_forall fun β => smul_eq_mul _ _)
      have h2 : IntegrableOn (fun β : ℝ => Cn * (h2MinusDom M r).indicator
          (fun p => Real.exp (-g2Tilde M r p)) (α, β)) (Set.Ici 0) volume :=
        ((hint4.1 α).smul Cn).congr (Filter.Eventually.of_forall fun β => smul_eq_mul _ _)
      rw [integral_const_mul, integral_add h1 h2, integral_const_mul, integral_const_mul]
    have h1o : IntegrableOn (fun α : ℝ => C0 * (∫ β in Set.Ici 0, (h2Dom M r).indicator
        (fun p => Real.exp (-h2Tilde M r p)) (α, β))) (Set.Ici 0) volume :=
      ((hint3.2).smul C0).congr (Filter.Eventually.of_forall fun α => smul_eq_mul _ _)
    have h2o : IntegrableOn (fun α : ℝ => Cn * (∫ β in Set.Ici 0, (h2MinusDom M r).indicator
        (fun p => Real.exp (-g2Tilde M r p)) (α, β))) (Set.Ici 0) volume :=
      ((hint4.2).smul Cn).congr (Filter.Eventually.of_forall fun α => smul_eq_mul _ _)
    have hout : IntegrableOn (fun α : ℝ => Cγ * (C0 * (∫ β in Set.Ici 0, (h2Dom M r).indicator
          (fun p => Real.exp (-h2Tilde M r p)) (α, β))
          + Cn * (∫ β in Set.Ici 0, (h2MinusDom M r).indicator
            (fun p => Real.exp (-g2Tilde M r p)) (α, β)))) (Set.Ici 0) volume :=
      ((h1o.add h2o).smul Cγ).congr (Filter.Eventually.of_forall fun α => by
        show Cγ • ((C0 * (∫ β in Set.Ici 0, (h2Dom M r).indicator
              (fun p => Real.exp (-h2Tilde M r p)) (α, β)))
            + (Cn * (∫ β in Set.Ici 0, (h2MinusDom M r).indicator
              (fun p => Real.exp (-g2Tilde M r p)) (α, β))))
          = Cγ * (C0 * (∫ β in Set.Ici 0, (h2Dom M r).indicator
                (fun p => Real.exp (-h2Tilde M r p)) (α, β))
              + Cn * (∫ β in Set.Ici 0, (h2MinusDom M r).indicator
                (fun p => Real.exp (-g2Tilde M r p)) (α, β)))
        rw [smul_eq_mul])
    exact hout.congr (Filter.Eventually.of_forall fun α => (h1eq α).symm)
  -- the dominand's outer integrability (mono' against the fine dominator)
  have hRHSB2 : IntegrableOn (fun α : ℝ => ∫ β in Set.Ici 0,
      ‖(∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β)) * bAiryKer (2+r) (M-β, M-α)‖)
      (Set.Ici 0) volume := by
    have hmeas : Measurable fun α : ℝ => ∫ β in Set.Ici 0,
        ‖(∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β)) * bAiryKer (2+r) (M-β, M-α)‖ := by
      have hh : (fun α : ℝ => ∫ β in Set.Ici 0,
            ‖(∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β)) * bAiryKer (2+r) (M-β, M-α)‖)
          = fun α => ∫ β : ℝ, (Set.univ ×ˢ Set.Ici 0).indicator
              (fun p : ℝ × ℝ => ‖(∫ γ in Set.Ioi 0, frK2 r p.1 γ * heatKernel 1 (γ + p.2))
                * bAiryKer (2+r) (M-p.2, M-p.1)‖) (α, β) := by
        funext α
        rw [← MeasureTheory.integral_indicator measurableSet_Ici]
        apply integral_congr_ae
        filter_upwards with β
        by_cases hβ : β ∈ Set.Ici 0
        · rw [Set.indicator_of_mem hβ,
            Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_univ α, hβ⟩)]
        · rw [Set.indicator_of_notMem hβ,
            Set.indicator_of_notMem (fun h => hβ (Set.mem_prod.mp h).2)]
      have hbk : Measurable fun p : ℝ × ℝ => bAiryKer (2+r) (M-p.2, M-p.1) :=
        ((continuous_bAiryKer (2+r)).comp
          ((continuous_const.sub continuous_snd).prodMk
            (continuous_const.sub continuous_fst))).measurable
      have hmeas2 : Measurable fun p : ℝ × ℝ =>
          ‖(∫ γ in Set.Ioi 0, frK2 r p.1 γ * heatKernel 1 (γ + p.2))
            * bAiryKer (2+r) (M-p.2, M-p.1)‖ :=
        ((measurable_frI2_γint_pair).mul hbk).norm
      rw [hh]
      have hsm : StronglyMeasurable fun p : ℝ × ℝ => (Set.univ ×ˢ Set.Ici 0).indicator
          (fun p : ℝ × ℝ => ‖(∫ γ in Set.Ioi 0, frK2 r p.1 γ * heatKernel 1 (γ + p.2))
            * bAiryKer (2+r) (M-p.2, M-p.1)‖) p :=
        (hmeas2.indicator (MeasurableSet.univ.prod measurableSet_Ici)).stronglyMeasurable
      exact (hsm.integral_prod_right' (ν := volume)).measurable
    apply houterD2.mono' hmeas.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with α hα
    rw [Real.norm_eq_abs,
      abs_of_nonneg (setIntegral_nonneg measurableSet_Ici (fun β _ => norm_nonneg _))]
    exact setIntegral_mono_on (hsliceC2 α (Set.mem_Ici.mp hα)) (hsliceD2 α) measurableSet_Ici
      (fun β hβ => by
        show ‖(∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β)) * bAiryKer (2+r) (M-β, M-α)‖ ≤ _
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (frI2_γint_nonneg hr α β), Real.norm_eq_abs]
        exact hpt2 (Set.mem_Ici.mp hα) (Set.mem_Ici.mp hβ))
  -- the outer `‖·‖` level
  have hLHSB2 : IntegrableOn (fun α : ℝ => ‖∫ β in Set.Ici 0,
      (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β)) * bAiryKer (2+r) (M-β, M-α)‖)
      (Set.Ici 0) volume := by
    have hmeas : Measurable fun α : ℝ => ‖∫ β in Set.Ici 0,
        (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β)) * bAiryKer (2+r) (M-β, M-α)‖ := by
      have hmeas0 : Measurable fun α : ℝ => ∫ β in Set.Ici 0,
          (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β)) * bAiryKer (2+r) (M-β, M-α) := by
        have hh : (fun α : ℝ => ∫ β in Set.Ici 0,
              (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β)) * bAiryKer (2+r) (M-β, M-α))
            = fun α => ∫ β : ℝ, (Set.univ ×ˢ Set.Ici 0).indicator
                (fun p : ℝ × ℝ => (∫ γ in Set.Ioi 0, frK2 r p.1 γ * heatKernel 1 (γ + p.2))
                  * bAiryKer (2+r) (M-p.2, M-p.1)) (α, β) := by
          funext α
          rw [← MeasureTheory.integral_indicator measurableSet_Ici]
          apply integral_congr_ae
          filter_upwards with β
          by_cases hβ : β ∈ Set.Ici 0
          · rw [Set.indicator_of_mem hβ,
              Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_univ α, hβ⟩)]
          · rw [Set.indicator_of_notMem hβ,
              Set.indicator_of_notMem (fun h => hβ (Set.mem_prod.mp h).2)]
        have hbk : Measurable fun p : ℝ × ℝ => bAiryKer (2+r) (M-p.2, M-p.1) :=
          ((continuous_bAiryKer (2+r)).comp
            ((continuous_const.sub continuous_snd).prodMk
              (continuous_const.sub continuous_fst))).measurable
        have hmeas2 : Measurable fun p : ℝ × ℝ =>
            (∫ γ in Set.Ioi 0, frK2 r p.1 γ * heatKernel 1 (γ + p.2))
              * bAiryKer (2+r) (M-p.2, M-p.1) :=
          (measurable_frI2_γint_pair).mul hbk
        rw [hh]
        have hsm : StronglyMeasurable fun p : ℝ × ℝ => (Set.univ ×ˢ Set.Ici 0).indicator
            (fun p : ℝ × ℝ => (∫ γ in Set.Ioi 0, frK2 r p.1 γ * heatKernel 1 (γ + p.2))
              * bAiryKer (2+r) (M-p.2, M-p.1)) p :=
          (hmeas2.indicator (MeasurableSet.univ.prod measurableSet_Ici)).stronglyMeasurable
        exact (hsm.integral_prod_right' (ν := volume)).measurable
      exact hmeas0.norm
    apply hRHSB2.mono' hmeas.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with α _
    calc ‖‖∫ β in Set.Ici 0, (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
          * bAiryKer (2+r) (M-β, M-α)‖‖
        = ‖∫ β in Set.Ici 0, (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
          * bAiryKer (2+r) (M-β, M-α)‖ := norm_norm _
      _ ≤ ∫ β in Set.Ici 0, ‖(∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
          * bAiryKer (2+r) (M-β, M-α)‖ := norm_integral_le_integral_norm _
  -- the assembly
  calc |frI2 M r|
      = ‖∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
          * bAiryKer (2+r) (M-β, M-α)‖ := by
        rw [hfr2, Real.norm_eq_abs]
    _ ≤ ∫ α in Set.Ici 0, ‖∫ β in Set.Ici 0, (∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
          * bAiryKer (2+r) (M-β, M-α)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ α in Set.Ici 0, ∫ β in Set.Ici 0, ‖(∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
          * bAiryKer (2+r) (M-β, M-α)‖ :=
        setIntegral_mono_on hLHSB2 hRHSB2 measurableSet_Ici (fun α _ =>
          norm_integral_le_integral_norm _)
    _ ≤ ∫ α in Set.Ici 0, ∫ β in Set.Ici 0, Cγ * (C0 * (h2Dom M r).indicator
          (fun p => Real.exp (-h2Tilde M r p)) (α, β)
          + Cn * (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β)) :=
        setIntegral_mono_on hRHSB2 houterD2 measurableSet_Ici (fun α hα =>
          setIntegral_mono_on (hsliceC2 α (Set.mem_Ici.mp hα)) (hsliceD2 α) measurableSet_Ici
            (fun β hβ => by
              show ‖(∫ γ in Set.Ioi 0, frK2 r α γ * heatKernel 1 (γ+β))
                * bAiryKer (2+r) (M-β, M-α)‖ ≤ _
              rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (frI2_γint_nonneg hr α β),
                Real.norm_eq_abs]
              exact hpt2 (Set.mem_Ici.mp hα) (Set.mem_Ici.mp hβ)))
    _ = Cγ * (C0 * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h2Dom M r).indicator
              (fun p => Real.exp (-h2Tilde M r p)) (α, β))
            + Cn * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h2MinusDom M r).indicator
              (fun p => Real.exp (-g2Tilde M r p)) (α, β))) := by
        have hinner : ∀ α : ℝ, (∫ β in Set.Ici 0, Cγ * (C0 * (h2Dom M r).indicator
                (fun p => Real.exp (-h2Tilde M r p)) (α, β)
                + Cn * (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β)))
            = Cγ * (C0 * (∫ β in Set.Ici 0, (h2Dom M r).indicator
                  (fun p => Real.exp (-h2Tilde M r p)) (α, β))
                + Cn * (∫ β in Set.Ici 0, (h2MinusDom M r).indicator
                  (fun p => Real.exp (-g2Tilde M r p)) (α, β))) := by
          intro α
          have h1 : IntegrableOn (fun β : ℝ => C0 * (h2Dom M r).indicator
              (fun p => Real.exp (-h2Tilde M r p)) (α, β)) (Set.Ici 0) volume :=
            ((hint3.1 α).smul C0).congr (Filter.Eventually.of_forall fun β => smul_eq_mul _ _)
          have h2 : IntegrableOn (fun β : ℝ => Cn * (h2MinusDom M r).indicator
              (fun p => Real.exp (-g2Tilde M r p)) (α, β)) (Set.Ici 0) volume :=
            ((hint4.1 α).smul Cn).congr (Filter.Eventually.of_forall fun β => smul_eq_mul _ _)
          rw [integral_const_mul, integral_add h1 h2, integral_const_mul, integral_const_mul]
        rw [setIntegral_congr_fun measurableSet_Ici (fun α _ => hinner α)]
        have h1o : IntegrableOn (fun α : ℝ => C0 * (∫ β in Set.Ici 0, (h2Dom M r).indicator
            (fun p => Real.exp (-h2Tilde M r p)) (α, β))) (Set.Ici 0) volume :=
          ((hint3.2).smul C0).congr (Filter.Eventually.of_forall fun α => smul_eq_mul _ _)
        have h2o : IntegrableOn (fun α : ℝ => Cn * (∫ β in Set.Ici 0, (h2MinusDom M r).indicator
            (fun p => Real.exp (-g2Tilde M r p)) (α, β))) (Set.Ici 0) volume :=
          ((hint4.2).smul Cn).congr (Filter.Eventually.of_forall fun α => smul_eq_mul _ _)
        rw [integral_const_mul, integral_add h1o h2o, integral_const_mul, integral_const_mul]
    _ ≤ (Cγ * (C0 + Cn))
          * ((∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h2Dom M r).indicator
                (fun p => Real.exp (-h2Tilde M r p)) (α, β))
            + (∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h2MinusDom M r).indicator
                (fun p => Real.exp (-g2Tilde M r p)) (α, β))) := by
        have hJ1nn : (0:ℝ) ≤ ∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
            (h2Dom M r).indicator (fun p => Real.exp (-h2Tilde M r p)) (α, β) :=
          setIntegral_nonneg measurableSet_Ici (fun α _ =>
            setIntegral_nonneg measurableSet_Ici (fun β _ =>
              Set.indicator_nonneg (fun p _ => (Real.exp_pos _).le) (α, β)))
        have hJ2nn : (0:ℝ) ≤ ∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
            (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β) :=
          setIntegral_nonneg measurableSet_Ici (fun α _ =>
            setIntegral_nonneg measurableSet_Ici (fun β _ =>
              Set.indicator_nonneg (fun p _ => (Real.exp_pos _).le) (α, β)))
        have hle : Cγ * (C0 * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h2Dom M r).indicator
                (fun p => Real.exp (-h2Tilde M r p)) (α, β))
              + Cn * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h2MinusDom M r).indicator
                (fun p => Real.exp (-g2Tilde M r p)) (α, β)))
            ≤ Cγ * ((C0 + Cn) * ((∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h2Dom M r).indicator
                  (fun p => Real.exp (-h2Tilde M r p)) (α, β))
                + (∫ α in Set.Ici 0, ∫ β in Set.Ici 0, (h2MinusDom M r).indicator
                  (fun p => Real.exp (-g2Tilde M r p)) (α, β)))) :=
          mul_le_mul_of_nonneg_left (by nlinarith [hJ1nn, hJ2nn, hC0pos.le, hCnn]) hCγpos.le
        exact hle.trans_eq (by ring)

/-- The set-integral-over-`E` to iterated-quadrant conversion (for `E` inside the
closed quadrant): `∫ p in E, f p = ∫ α in Ici 0, ∫ β in Ici 0, 1_E f (α, β)`.
Used to move between the set-integral packages of `FRExponents.lean` (C4) and the iterated
dominating integrals of D1. -/
theorem setIntegral_ind_quadrant_eq_iterated {E : Set (ℝ × ℝ)} (hE : MeasurableSet E)
    {f : ℝ × ℝ → ℝ} (hf : Integrable (E.indicator f) (volume.prod volume))
    (hEq : ∀ p : ℝ × ℝ, p ∈ E → 0 ≤ p.1 ∧ 0 ≤ p.2) :
    (∫ p in E, f p) = ∫ α in Set.Ici 0, ∫ β in Set.Ici 0, E.indicator f (α, β) := by
  rw [← MeasureTheory.integral_indicator hE, Measure.volume_eq_prod,
    MeasureTheory.integral_prod _ hf]
  have hinner : ∀ α : ℝ, (∫ β : ℝ, E.indicator f (α, β))
      = ∫ β in Set.Ici 0, E.indicator f (α, β) := by
    intro α
    rw [← MeasureTheory.integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards with β
    by_cases hβ : 0 ≤ β
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hβ)]
    · rw [Set.indicator_of_notMem (fun h => hβ (Set.mem_Ici.mp h))]
      exact Set.indicator_of_notMem (fun hp => hβ (hEq (α, β) hp).2) _
  have houter : (∫ α : ℝ, ∫ β : ℝ, E.indicator f (α, β))
      = ∫ α in Set.Ici 0, ∫ β : ℝ, E.indicator f (α, β) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards with α
    by_cases hα : 0 ≤ α
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hα)]
    · rw [Set.indicator_of_notMem (fun h => hα (Set.mem_Ici.mp h))]
      have hz : (∫ β : ℝ, E.indicator f (α, β)) = 0 := by
        rw [show (fun β : ℝ => E.indicator f (α, β)) = fun _ => (0:ℝ) from funext fun β =>
          Set.indicator_of_notMem (fun hp => hα (hEq (α, β) hp).1) _]
        simp
      exact hz
  rw [houter]
  apply integral_congr_ae
  filter_upwards with α
  exact hinner α

/-- **D2**: the `I₁⁺` piece bound
`S^{-1/2}·(∫_{D₊} e^{−H₁}) ≤ C(1+r)^{1/2}e^{−J_M(r)}` — C4 (uniform) plus the
prefactor `(r+1)^{1/2}(r+2)^{-1/2} ≤ (1+r)^{1/2}` (square,
`(r+1)² ≤ (r+1)(r+2)`).  Constants existential; `C` uniform in `1 ≤ r`,
`2 ≤ M`. -/
theorem abs_frI1_plus_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {M r : ℝ}, 2 ≤ M → 1 ≤ r →
      (r+2)^(-1/2 : ℝ) * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
          (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β))
        ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
  obtain ⟨C4, hC4pos, hC4⟩ := frI1Plus_exp_int_le_uniform
  refine ⟨C4, hC4pos, ?_⟩
  intro M r hM hr
  have hM1 : 1 ≤ M := le_trans one_le_two hM
  have hR : 2 ≤ saddleR M r := two_le_saddleR hM hr
  have hSinv : (0:ℝ) ≤ (r+2)^(-1/2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hconv := setIntegral_ind_quadrant_eq_iterated (measurableSet_h1Dom M r)
    ((integrableOn_exp_neg_h1Exp (by linarith : (0:ℝ) < r)).integrable_indicator
      (measurableSet_h1Dom M r)) (fun p hp => ⟨hp.1, hp.2.1⟩)
  have hratio : (r+2)^(-1/2 : ℝ) * (r+1)^(1/2 : ℝ) ≤ (r+1)^(1/2 : ℝ) := by
    calc (r+2)^(-1/2 : ℝ) * (r+1)^(1/2 : ℝ)
        ≤ 1 * (r+1)^(1/2 : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_one_of_one_le_of_nonpos (by linarith : (1:ℝ) ≤ r+2)
              (by norm_num : (-1/2 : ℝ) ≤ 0))
            (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ r+1) _)
      _ = (r+1)^(1/2 : ℝ) := one_mul _
  calc (r+2)^(-1/2 : ℝ) * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
        (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β))
      = (r+2)^(-1/2 : ℝ) * (∫ p in h1Dom M r, Real.exp (-h1Exp M r p)) := by
        rw [hconv]
    _ ≤ (r+2)^(-1/2 : ℝ) * (C4 * (r+1)^(1/2 : ℝ) * Real.exp (-saddleJ M r)) :=
        mul_le_mul_of_nonneg_left (hC4 hM1 hr hR) hSinv
    _ ≤ C4 * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
        calc (r+2)^(-1/2 : ℝ) * (C4 * (r+1)^(1/2 : ℝ) * Real.exp (-saddleJ M r))
            = (C4 * Real.exp (-saddleJ M r)) * ((r+2)^(-1/2 : ℝ) * (r+1)^(1/2 : ℝ)) := by ring
          _ ≤ (C4 * Real.exp (-saddleJ M r)) * ((r+1)^(1/2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hratio (mul_nonneg hC4pos.le (Real.exp_pos _).le)
          _ = C4 * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
              rw [show (1:ℝ) + r = r + 1 by ring]
              ring

/-- The `G₁` boundary point `A(α) = 2M + S² + α` is nonnegative for `0 ≤ M`,
`0 ≤ α`. -/
theorem g1Boundary_nonneg (hM : 0 ≤ M) (hα : 0 ≤ α) :
    0 ≤ g1Boundary M r α := by
  unfold g1Boundary
  nlinarith [sq_nonneg (r+2)]

/-- **C6, the sharp boundary slope**: `A(α)/2 − S ≥ (2M+3)/2` for `1 ≤ r`, `0 ≤ α`, ALL `M`
(this implies `≥ a²/4`, `a² = 2M`, the slope used in the paper for large `a`). -/
theorem g1Boundary_half_sub_ge (hr : 1 ≤ r) (hα : 0 ≤ α) :
    (2*M+3)/2 ≤ g1Boundary M r α/2 - (r+2) := by
  unfold g1Boundary
  nlinarith [sq_nonneg (r - 1), hr, hα]

/-- **C6 glue**: `G₁(α, A(α)) ≥ E₀ + Mα`, i.e.
`≥ E₀ + (a²/2)α` with `a² = 2M` (the exact boundary expansion
`g1Exp_boundary_eq` plus `(2M+S²)/2 ≥ M`). -/
theorem g1Exp_boundary_ge_E0_add (hr : 0 < r) (hα : 0 ≤ α) :
    (2*M + (r+2)^2)^2/4 - (r+2)^3/3 + M*α ≤ g1Exp M r (α, g1Boundary M r α) := by
  rw [g1Exp_boundary_eq]
  have h1 : (0:ℝ) ≤ α^2/(4*(r+1)) := div_nonneg (sq_nonneg α) (by linarith [hr])
  have hX : (0:ℝ) ≤ ((2*M + (r+2)^2)/2) * α - M*α := by
    rw [show ((2*M + (r+2)^2)/2) * α - M*α = ((r+2)^2/2) * α by ring]
    exact mul_nonneg (by positivity) hα
  have hquad : (2*M + (r+2)^2)^2/4 + ((2*M + (r+2)^2)/2) * α
      ≤ (2*M + (r+2)^2 + α)^2/4 := by
    nlinarith [sq_nonneg α]
  nlinarith [h1, hX, hquad]

/-- **D3**: the `I₁⁻` piece bound
`S^{-1/2}·(∫∫_{h1MinusDom} e^{−G₁}) ≤ C_χ e^{−c_χ(2M)²}` — the boundary
expansion `g1Exp_quadratic_beta` at the sharp slope
(`g1Boundary_half_sub_ge`), the β-integration `frI1Minus_int_beta_le`
and α-integration `frI1Minus_int_alpha_le`, then the
χ-large absorption `frI1Minus_E0_ge`. -/
theorem abs_frI1_minus_le {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ {M r : ℝ}, M₀ ≤ M → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      (r+2)^(-1/2 : ℝ) * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
          (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β))
        ≤ C * Real.exp (-c * (2*M)^2) := by
  obtain ⟨c0, a₀, hc0pos, hE0⟩ := frI1Minus_E0_ge hχ0 hχ1
  refine ⟨1, c0, max 1 (a₀^2/2), one_pos, hc0pos, ?_⟩
  intro M r hM0 hr hradm
  have hM1 : (1:ℝ) ≤ M := le_trans (le_max_left _ _) hM0
  have hM0' : (0:ℝ) < M := lt_of_lt_of_le one_pos hM1
  have hM0nn : (0:ℝ) ≤ M := hM0'.le
  have hr0 : (0:ℝ) < r := by linarith
  have ha₀ : a₀ ≤ Real.sqrt (2*M) := by
    have h1 : a₀^2/2 ≤ M := le_trans (le_max_right _ _) hM0
    rcases le_or_gt a₀ 0 with ha | ha
    · exact le_trans ha (Real.sqrt_nonneg _)
    · rw [Real.le_sqrt ha.le (by positivity : (0:ℝ) ≤ 2*M)]
      nlinarith [h1]
  have hE0M := hE0 ha₀ hr hradm
  have hSinv : (0:ℝ) ≤ (r+2)^(-1/2 : ℝ) := Real.rpow_nonneg (by linarith) _
  -- the section conversion and the `t`-substitution (for `0 ≤ α`)
  have hsec : ∀ α : ℝ, 0 ≤ α →
      (∫ β in Set.Ici 0, (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β))
        = ∫ t in Set.Ioi 0, Real.exp (-g1Exp M r (α, g1Boundary M r α + t)) := by
    intro α hα
    have hA0 : (0:ℝ) ≤ g1Boundary M r α := g1Boundary_nonneg hM0nn hα
    have h1 : (∫ β in Set.Ici 0, (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β))
        = ∫ β in Set.Ioi (g1Boundary M r α), Real.exp (-g1Exp M r (α, β)) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ici,
        ← MeasureTheory.integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with β
      by_cases hβA : g1Boundary M r α < β
      · have hβ : (0:ℝ) ≤ β := le_trans hA0 hβA.le
        have hmem : (α, β) ∈ h1MinusDom M r := ⟨hα, hβ, by
          show 2*M + α - β + (r+2)^2 < 0
          unfold g1Boundary at hβA
          linarith⟩
        rw [Set.indicator_of_mem (Set.mem_Ici.mpr hβ), Set.indicator_of_mem hmem,
          Set.indicator_of_mem (Set.mem_Ioi.mpr hβA)]
      · rw [Set.indicator_of_notMem (fun h => hβA (Set.mem_Ioi.mp h))]
        by_cases hβ : 0 ≤ β
        · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hβ),
            Set.indicator_of_notMem (fun h => hβA (by
              have hu := h.2.2
              unfold g1Boundary
              linarith [hu]))]
        · rw [Set.indicator_of_notMem (fun h => hβ (Set.mem_Ici.mp h))]
    rw [h1]
    have hsub : (∫ β in Set.Ioi (g1Boundary M r α), Real.exp (-g1Exp M r (α, β)))
        = ∫ t in Set.Ioi 0, Real.exp (-g1Exp M r (α, t + g1Boundary M r α)) := by
      have h := AiryConj.integral_Ioi_comp_sub
        (fun t => Real.exp (-g1Exp M r (α, t + g1Boundary M r α))) (g1Boundary M r α)
      rw [← h]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro β _
      show Real.exp (-g1Exp M r (α, β))
        = Real.exp (-g1Exp M r (α, β - g1Boundary M r α + g1Boundary M r α))
      rw [show β - g1Boundary M r α + g1Boundary M r α = β by ring]
    rw [hsub]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    show Real.exp (-g1Exp M r (α, t + g1Boundary M r α))
      = Real.exp (-g1Exp M r (α, g1Boundary M r α + t))
    rw [show t + g1Boundary M r α = g1Boundary M r α + t by ring]
  have hconv : (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
        (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β))
      = ∫ α in Set.Ici 0, ∫ t in Set.Ioi 0, Real.exp (-g1Exp M r (α, g1Boundary M r α + t)) := by
    apply setIntegral_congr_fun measurableSet_Ici
    intro α hα
    exact hsec α (Set.mem_Ici.mp hα)
  -- the pointwise bound (C6: boundary + linear growth)
  have hpt : ∀ α t : ℝ, 0 ≤ α → 0 ≤ t →
      Real.exp (-g1Exp M r (α, g1Boundary M r α + t))
        ≤ Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3))
          * (Real.exp (-(M * α)) * Real.exp (-(((2*M+3)/2) * t) - t^2/4)) := by
    intro α t hα ht
    have hslope : (2*M+3)/2 ≤ g1Boundary M r α/2 - (r+2) := g1Boundary_half_sub_ge (M := M) hr hα
    have hquad := g1Exp_quadratic_beta M r α t
    have hbase := g1Exp_boundary_ge_E0_add (M := M) hr0 hα
    have hkey : (2*M + (r+2)^2)^2/4 - (r+2)^3/3 + M*α + ((2*M+3)/2)*t + t^2/4
        ≤ g1Exp M r (α, g1Boundary M r α + t) := by
      rw [hquad]
      have hslope2 : ((2*M+3)/2)*t ≤ (g1Boundary M r α/2 - (r+2))*t :=
        mul_le_mul_of_nonneg_right hslope ht
      nlinarith [hbase, hslope2]
    calc Real.exp (-g1Exp M r (α, g1Boundary M r α + t))
        ≤ Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3 + M*α + ((2*M+3)/2)*t + t^2/4)) :=
          Real.exp_le_exp.mpr (neg_le_neg hkey)
      _ = Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3))
          * (Real.exp (-(M * α)) * Real.exp (-(((2*M+3)/2) * t) - t^2/4)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  -- integrability inputs for the `t`-level
  have hexpint : IntegrableOn (fun t : ℝ => Real.exp (-(((2*M+3)/2) * t))) (Set.Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => Real.exp (-u)) 0
      (by linarith [hM0'] : (0:ℝ) < (2*M+3)/2)).mpr
      (by simpa using integrableOn_exp_neg_Ioi (0:ℝ))
  have hRHint0 : IntegrableOn (fun t : ℝ => Real.exp (-(((2*M+3)/2) * t) - t^2/4))
      (Set.Ioi 0) := by
    apply hexpint.mono' (by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-(((2*M+3)/2) * t) - t^2/4)).aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])
  have hRHint : ∀ α : ℝ, IntegrableOn (fun t : ℝ => Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3))
      * (Real.exp (-(M * α)) * Real.exp (-(((2*M+3)/2) * t) - t^2/4))) (Set.Ioi 0) :=
    fun α => (hRHint0.const_mul (Real.exp (-(M * α)))).const_mul
      (Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)))
  have hLHSint : ∀ α : ℝ, 0 ≤ α → IntegrableOn (fun t : ℝ =>
      Real.exp (-g1Exp M r (α, g1Boundary M r α + t))) (Set.Ioi 0) := by
    intro α hα
    apply (hRHint α).mono' ?_ ?_
    · exact ((Real.continuous_exp.comp (((continuous_g1Exp M r).comp
        (continuous_const.prodMk (continuous_const.add continuous_id))).neg))).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact hpt α t hα (Set.mem_Ioi.mp ht).le
  -- the `t`-integration
  have htbound : ∀ α : ℝ, 0 ≤ α →
      (∫ t in Set.Ioi 0, Real.exp (-g1Exp M r (α, g1Boundary M r α + t)))
        ≤ Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * Real.exp (-(M * α)) * (1/M) := by
    intro α hα
    calc (∫ t in Set.Ioi 0, Real.exp (-g1Exp M r (α, g1Boundary M r α + t)))
        ≤ ∫ t in Set.Ioi 0, Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3))
          * (Real.exp (-(M * α)) * Real.exp (-(((2*M+3)/2) * t) - t^2/4)) :=
          setIntegral_mono_on (hLHSint α hα) (hRHint α) measurableSet_Ioi
            (fun t ht => hpt α t hα (Set.mem_Ioi.mp ht).le)
      _ = (Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * Real.exp (-(M * α)))
          * ∫ t in Set.Ioi 0, Real.exp (-(((2*M+3)/2) * t) - t^2/4) := by
          rw [← integral_const_mul]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t _
          ring
      _ ≤ (Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * Real.exp (-(M * α))) * (1/M) :=
          mul_le_mul_of_nonneg_left (frI1Minus_int_beta_le hM0')
            (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      _ = Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * Real.exp (-(M * α)) * (1/M) := by ring
  -- integrability inputs for the `α`-level
  have hexpintα : IntegrableOn (fun α : ℝ => Real.exp (-(M * α))) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      ((integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => Real.exp (-u)) 0 hM0').mpr
        (by simpa using integrableOn_exp_neg_Ioi (0:ℝ)))
  have hRHSouter : IntegrableOn (fun α : ℝ => Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3))
      * Real.exp (-(M * α)) * (1/M)) (Set.Ici 0) :=
    ((hexpintα.const_mul (Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)))).mul_const (1/M))
  have hLHSouter : IntegrableOn (fun α : ℝ => ∫ t in Set.Ioi 0,
      Real.exp (-g1Exp M r (α, g1Boundary M r α + t))) (Set.Ici 0) := by
    apply hRHSouter.mono' ?_ ?_
    · -- measurability of `α ↦ ∫_{t > 0} e^{−G₁(α, Aα+t)}`
      have hh : (fun α : ℝ => ∫ t in Set.Ioi 0, Real.exp (-g1Exp M r (α, g1Boundary M r α + t)))
          = fun α => ∫ t : ℝ, (Set.univ ×ˢ Set.Ioi 0).indicator
              (fun q : ℝ × ℝ => Real.exp (-g1Exp M r (q.1, g1Boundary M r q.1 + q.2))) (α, t) := by
        funext α
        rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        filter_upwards with t
        by_cases ht : t ∈ Set.Ioi 0
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_univ α, ht⟩)]
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (fun h => ht (Set.mem_prod.mp h).2)]
      have hmeas2 : Measurable fun q : ℝ × ℝ =>
          Real.exp (-g1Exp M r (q.1, g1Boundary M r q.1 + q.2)) := by
        have hcont : Continuous fun q : ℝ × ℝ => (q.1, g1Boundary M r q.1 + q.2) :=
          continuous_fst.prodMk (by unfold g1Boundary; fun_prop)
        exact (Real.continuous_exp.comp ((continuous_g1Exp M r).comp hcont).neg).measurable
      rw [hh]
      have hsm : StronglyMeasurable fun q : ℝ × ℝ => (Set.univ ×ˢ Set.Ioi 0).indicator
          (fun q : ℝ × ℝ => Real.exp (-g1Exp M r (q.1, g1Boundary M r q.1 + q.2))) q :=
        (hmeas2.indicator (MeasurableSet.univ.prod measurableSet_Ioi)).stronglyMeasurable
      exact (hsm.integral_prod_right' (ν := volume)).measurable.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with α hα
      rw [Real.norm_eq_abs,
        abs_of_nonneg (setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le))]
      exact htbound α (Set.mem_Ici.mp hα)
  -- the `α`-integration
  have houterbound : (∫ α in Set.Ici 0, ∫ t in Set.Ioi 0,
        Real.exp (-g1Exp M r (α, g1Boundary M r α + t)))
      ≤ Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * (1/M) * (1/M) := by
    calc ∫ α in Set.Ici 0, ∫ t in Set.Ioi 0, Real.exp (-g1Exp M r (α, g1Boundary M r α + t))
        ≤ ∫ α in Set.Ici 0, Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3))
          * Real.exp (-(M * α)) * (1/M) :=
          setIntegral_mono_on hLHSouter hRHSouter measurableSet_Ici
            (fun α hα => htbound α (Set.mem_Ici.mp hα))
      _ = (Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * (1/M))
          * ∫ α in Set.Ici 0, Real.exp (-(M * α)) := by
          rw [← integral_const_mul]
          apply setIntegral_congr_fun measurableSet_Ici
          intro α _
          ring
      _ = (Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * (1/M))
          * ∫ α in Set.Ioi 0, Real.exp (-(M * α)) := by
          rw [integral_Ici_eq_integral_Ioi]
      _ ≤ (Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * (1/M)) * (1/M) :=
          mul_le_mul_of_nonneg_left (frI1Minus_int_alpha_le hM0')
            (mul_nonneg (Real.exp_pos _).le (div_nonneg zero_le_one hM0nn))
      _ = Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * (1/M) * (1/M) := by ring
  -- the final absorption
  have h1M : (1:ℝ)/M ≤ 1 := (div_le_one hM0').mpr (by linarith [hM1])
  have hexp : Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) ≤ Real.exp (-(c0 * (2*M)^2)) :=
    Real.exp_le_exp.mpr (neg_le_neg hE0M)
  have hstep1 : Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * (1/M) * (1/M)
      ≤ Real.exp (-(c0 * (2*M)^2)) := by
    calc Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * (1/M) * (1/M)
        ≤ Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1M (Real.exp_pos _).le) h1M
            (div_nonneg zero_le_one hM0nn) (mul_nonneg (Real.exp_pos _).le zero_le_one)
      _ = Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) := by rw [mul_one, mul_one]
      _ ≤ Real.exp (-(c0 * (2*M)^2)) := hexp
  calc (r+2)^(-1/2 : ℝ) * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
        (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β))
      = (r+2)^(-1/2 : ℝ) * (∫ α in Set.Ici 0, ∫ t in Set.Ioi 0,
          Real.exp (-g1Exp M r (α, g1Boundary M r α + t))) := by rw [hconv]
    _ ≤ (r+2)^(-1/2 : ℝ) * (Real.exp (-((2*M + (r+2)^2)^2/4 - (r+2)^3/3)) * (1/M) * (1/M)) :=
        mul_le_mul_of_nonneg_left houterbound hSinv
    _ ≤ (r+2)^(-1/2 : ℝ) * Real.exp (-(c0 * (2*M)^2)) :=
        mul_le_mul_of_nonneg_left hstep1 hSinv
    _ ≤ 1 * Real.exp (-(c0 * (2*M)^2)) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_one_of_one_le_of_nonpos (by linarith : (1:ℝ) ≤ r+2)
            (by norm_num : (-1/2 : ℝ) ≤ 0)) (Real.exp_pos _).le
    _ = 1 * Real.exp (-c0 * (2*M)^2) := by rw [neg_mul]

/-- The standard Gaussian mass `∫ v, e^{−v²/2} = √(2π)` (the `v`-integral of the
`(δ, v)` substitutions and). -/
theorem integral_exp_neg_sq_half : ∫ v : ℝ, Real.exp (-v^2/2) = Real.sqrt (2*Real.pi) := by
  rw [show (fun v : ℝ => Real.exp (-v^2/2)) = fun v => Real.exp (-(1/2 : ℝ) * v^2) from
    funext fun v => by congr 1; ring]
  rw [integral_gaussian]
  congr 1
  ring_nf

set_option maxHeartbeats 1600000 in
/-- **D4**: the `I₂⁺` piece bound
`∫∫_{h2Dom} e^{−H̃₂} ≤ C(1+r)^{1/2}e^{−J_M(r)}` — `H̃₂ ≥ J + (δ−δ*)²/2 + v²/2`
(C8's `h2Tilde_ge`), enlargement to ℝ², and the `(δ, v)`
substitution (`integral_mul_comp_half_add_half_sub`, Jacobian factor 2). -/

theorem abs_frI2_plus_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {M r : ℝ}, 2 ≤ M → 1 ≤ r →
      (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
          (h2Dom M r).indicator (fun p => Real.exp (-h2Tilde M r p)) (α, β))
        ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
  refine ⟨4 * Real.pi, by positivity, ?_⟩
  intro M r hM hr
  have hM1 : 1 ≤ M := le_trans one_le_two hM
  have hR : 2 ≤ saddleR M r := two_le_saddleR hM hr
  -- the Gaussian factors `F δ = e^{−(δ−δ*)²/2}`, `G v = e^{−v²/2}`
  have hFint : Integrable fun δ : ℝ => Real.exp (-(δ - 2*(r + saddleR M r))^2/2) := by
    apply ((integrable_exp_neg_mul_sq (show (0:ℝ) < 1/2 by norm_num)).comp_sub_right
      (2*(r + saddleR M r))).congr
    filter_upwards with δ
    congr 1
    ring
  have hGint : Integrable fun v : ℝ => Real.exp (-v^2/2) := by
    apply (integrable_exp_neg_mul_sq (show (0:ℝ) < 1/2 by norm_num)).congr
    filter_upwards with v
    congr 1
    ring
  have hFmeas : Measurable fun δ : ℝ => Real.exp (-(δ - 2*(r + saddleR M r))^2/2) := by fun_prop
  have hGmeas : Measurable fun v : ℝ => Real.exp (-v^2/2) := by fun_prop
  have hG1 : ∀ x : ℝ, |Real.exp (-x^2/2)| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by norm_num))
  have hplane : Integrable (Function.uncurry fun α β : ℝ =>
      Real.exp (-((α+β)/2 - 2*(r + saddleR M r))^2/2) * Real.exp (-((α-β)/2)^2/2))
      (volume.prod volume) :=
    integrable_mul_comp_half_add_half_sub hFmeas hFint hGmeas hGint hG1
  -- the pointwise bound on `h2Dom` (C8)
  have hpt : ∀ p : ℝ × ℝ, p ∈ h2Dom M r →
      Real.exp (-h2Tilde M r p)
        ≤ Real.exp (-saddleJ M r)
          * (Real.exp (-((p.1+p.2)/2 - 2*(r + saddleR M r))^2/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)) := by
    intro p hp
    have hge := h2Tilde_ge hM1 hr hR hp.1 hp.2.1 hp.2.2
    calc Real.exp (-h2Tilde M r p)
        ≤ Real.exp (-(saddleJ M r + ((p.1+p.2)/2 - 2*(r + saddleR M r))^2/2 + ((p.1-p.2)/2)^2/2)) :=
          Real.exp_le_exp.mpr (neg_le_neg hge)
      _ = Real.exp (-saddleJ M r)
          * (Real.exp (-((p.1+p.2)/2 - 2*(r + saddleR M r))^2/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  -- the `h2Dom` integrability of `e^{−H̃₂}`
  have hint : IntegrableOn (fun p => Real.exp (-h2Tilde M r p)) (h2Dom M r) := by
    apply ((hplane.const_mul (Real.exp (-saddleJ M r))).integrableOn).mono' ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_h2Tilde M r).neg).measurable).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_h2Dom M r)] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact hpt p hp
  -- the conversion, the evaluation of `∫ F`
  have hconv := (setIntegral_ind_quadrant_eq_iterated (measurableSet_h2Dom M r)
    (hint.integrable_indicator (measurableSet_h2Dom M r)) (fun p hp => ⟨hp.1, hp.2.1⟩)).symm
  have hFeval : ∫ δ : ℝ, Real.exp (-(δ - 2*(r + saddleR M r))^2/2) = Real.sqrt (2*Real.pi) := by
    rw [show (fun δ : ℝ => Real.exp (-(δ - 2*(r + saddleR M r))^2/2))
        = fun δ => Real.exp (-(1/2 : ℝ) * (δ - 2*(r + saddleR M r))^2) from funext fun δ => by
          congr 1
          ring]
    rw [MeasureTheory.integral_sub_right_eq_self (μ := volume)
      (fun x : ℝ => Real.exp (-(1/2 : ℝ) * x^2)) (2*(r + saddleR M r))]
    rw [integral_gaussian]
    congr 1
    ring_nf
  have hc1 : (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
        (h2Dom M r).indicator (fun p => Real.exp (-h2Tilde M r p)) (α, β))
      = ∫ p in h2Dom M r, Real.exp (-h2Tilde M r p) := hconv
  have hc2 : (∫ p in h2Dom M r, Real.exp (-h2Tilde M r p))
      ≤ ∫ p in h2Dom M r, Real.exp (-saddleJ M r)
          * (Real.exp (-((p.1+p.2)/2 - 2*(r + saddleR M r))^2/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)) :=
        setIntegral_mono_on hint ((hplane.const_mul _).integrableOn) (measurableSet_h2Dom M r) hpt
  have hc3 : (∫ p in h2Dom M r, Real.exp (-saddleJ M r)
          * (Real.exp (-((p.1+p.2)/2 - 2*(r + saddleR M r))^2/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)))
      ≤ ∫ p in (Set.univ : Set (ℝ × ℝ)), Real.exp (-saddleJ M r)
          * (Real.exp (-((p.1+p.2)/2 - 2*(r + saddleR M r))^2/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)) :=
        setIntegral_mono_set ((hplane.const_mul _).integrableOn)
          (Filter.Eventually.of_forall fun (p : ℝ × ℝ) => by positivity)
          (Filter.Eventually.of_forall fun (p : ℝ × ℝ) _ => Set.mem_univ p)
  have hc4 : (∫ p in (Set.univ : Set (ℝ × ℝ)), Real.exp (-saddleJ M r)
          * (Real.exp (-((p.1+p.2)/2 - 2*(r + saddleR M r))^2/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)))
      = ∫ p : ℝ × ℝ, Real.exp (-saddleJ M r)
          * (Real.exp (-((p.1+p.2)/2 - 2*(r + saddleR M r))^2/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)) := setIntegral_univ
  have hc5 : (∫ p : ℝ × ℝ, Real.exp (-saddleJ M r)
          * (Real.exp (-((p.1+p.2)/2 - 2*(r + saddleR M r))^2/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)))
      = Real.exp (-saddleJ M r) * (2 * Real.sqrt (2*Real.pi) * Real.sqrt (2*Real.pi)) := by
        rw [integral_const_mul, Measure.volume_eq_prod]
        rw [show (fun p : ℝ × ℝ => Real.exp (-((p.1+p.2)/2 - 2*(r + saddleR M r))^2/2)
              * Real.exp (-((p.1-p.2)/2)^2/2))
            = Function.uncurry (fun α β : ℝ => Real.exp (-((α+β)/2 - 2*(r + saddleR M r))^2/2)
              * Real.exp (-((α-β)/2)^2/2)) from funext fun p => rfl]
        rw [MeasureTheory.integral_prod _ hplane]
        simp only [Function.uncurry_apply_pair]
        rw [integral_mul_comp_half_add_half_sub hFmeas hFint hGmeas hGint hG1, hFeval,
          integral_exp_neg_sq_half]
  have hc6 : Real.exp (-saddleJ M r) * (2 * Real.sqrt (2*Real.pi) * Real.sqrt (2*Real.pi))
      = 4 * Real.pi * Real.exp (-saddleJ M r) := by
        rw [show (2:ℝ) * Real.sqrt (2*Real.pi) * Real.sqrt (2*Real.pi) = 4 * Real.pi by
          rw [mul_assoc, ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*Real.pi) (2*Real.pi),
            show (2*Real.pi) * (2*Real.pi) = (2*Real.pi)^2 by ring,
            Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2*Real.pi)]
          ring]
        ring
  have hc7 : 4 * Real.pi * Real.exp (-saddleJ M r)
      ≤ (4 * Real.pi) * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
        have h1 : (1:ℝ) ≤ (1+r)^(1/2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
        calc 4 * Real.pi * Real.exp (-saddleJ M r)
            = (4 * Real.pi * Real.exp (-saddleJ M r)) * 1 := by ring
          _ ≤ (4 * Real.pi * Real.exp (-saddleJ M r)) * ((1+r)^(1/2 : ℝ)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (4 * Real.pi) * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by ring
  exact hc1.le.trans (hc2.trans (hc3.trans (hc4.le.trans (hc5.le.trans (hc6.le.trans hc7)))))

/-- **D5**: the `I₂⁻` piece bound
`∫∫_{h2MinusDom} e^{−G̃₂} ≤ C_χ e^{−c_χ(2M)²}` — `G̃₂ = G_{2,−}(δ) + v²/2`
(`g2Tilde_eq_g2Minus_add`), the linear growth `g2Minus_ge_linear`
(sharp constant `M/2 = a²/4`), the `v`-enlargement to
ℝ and the `δ`-tail `2/M`, then the χ-large absorption
`frI2Minus_E20_ge`. -/
theorem abs_frI2_minus_le {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ {M r : ℝ}, M₀ ≤ M → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
          (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β))
        ≤ C * Real.exp (-c * (2*M)^2) := by
  obtain ⟨c0, a₀, hc0pos, hE0⟩ := frI2Minus_E20_ge hχ0 hχ1
  refine ⟨4 * Real.sqrt (2*Real.pi), c0, max 3 (a₀^2/2), by positivity, hc0pos, ?_⟩
  intro M r hM0 hr hradm
  have hM3 : (3:ℝ) ≤ M := le_trans (le_max_left _ _) hM0
  have hM1 : (1:ℝ) ≤ M := by linarith
  have hM0' : (0:ℝ) < M := by linarith
  have hM0nn : (0:ℝ) ≤ M := hM0'.le
  have ha₀ : a₀ ≤ Real.sqrt (2*M) := by
    have h1 : a₀^2/2 ≤ M := le_trans (le_max_right _ _) hM0
    rcases le_or_gt a₀ 0 with ha | ha
    · exact le_trans ha (Real.sqrt_nonneg _)
    · rw [Real.le_sqrt ha.le (by positivity : (0:ℝ) ≤ 2*M)]
      nlinarith [h1]
  have hE0M := hE0 ha₀ hr hradm
  -- the `F₂` factor (the `δ`-tail `1_{δ > δmax} e^{−(M/2)(δ−δmax)}`)
  have hF2meas : Measurable fun δ : ℝ =>
      (Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s)) (δ - (2*M + (r+2)^2)/2) := by
    have hg : Measurable fun s : ℝ => Real.exp (-(M/2)*s) := by fun_prop
    exact (hg.indicator measurableSet_Ioi).comp ((continuous_id.sub continuous_const).measurable)
  have hF2int0 : Integrable fun s : ℝ => (Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s)) s := by
    have hM2 : (0:ℝ) < M/2 := by linarith [hM0']
    rw [integrable_indicator_iff measurableSet_Ioi]
    rw [show (fun s : ℝ => Real.exp (-(M/2)*s)) = fun s => Real.exp (-(M/2 * s)) from
      funext fun s => by congr 1; rw [neg_mul]]
    exact (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => Real.exp (-u)) 0 hM2).mpr
      (by simpa using integrableOn_exp_neg_Ioi (0:ℝ))
  have hF2int : Integrable fun δ : ℝ =>
      (Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s)) (δ - (2*M + (r+2)^2)/2) :=
    hF2int0.comp_sub_right _
  have hF2le1 : ∀ δ : ℝ, |(Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s))
      (δ - (2*M + (r+2)^2)/2)| ≤ 1 := by
    intro δ
    by_cases h : 0 < δ - (2*M + (r+2)^2)/2
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h), abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (by nlinarith [hM0', h])
    · rw [Set.indicator_of_notMem (fun hh => h (Set.mem_Ioi.mp hh))]
      norm_num
  have hGmeas : Measurable fun v : ℝ => Real.exp (-v^2/2) := by fun_prop
  have hGint : Integrable fun v : ℝ => Real.exp (-v^2/2) := by
    apply (integrable_exp_neg_mul_sq (show (0:ℝ) < 1/2 by norm_num)).congr
    filter_upwards with v
    congr 1
    ring
  have hG1 : ∀ x : ℝ, |Real.exp (-x^2/2)| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by norm_num))
  have hplane : Integrable (Function.uncurry fun α β : ℝ =>
      (Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s)) ((α+β)/2 - (2*M + (r+2)^2)/2)
        * Real.exp (-((α-β)/2)^2/2)) (volume.prod volume) :=
    integrable_mul_comp_half_add_half_sub hF2meas hF2int hGmeas hGint hG1
  -- the pointwise bound on `h2MinusDom` (C7)
  have hpt : ∀ p : ℝ × ℝ, p ∈ h2MinusDom M r →
      Real.exp (-g2Tilde M r p)
        ≤ Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3))
          * ((Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s))
              ((p.1+p.2)/2 - (2*M + (r+2)^2)/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)) := by
    intro p hp
    obtain ⟨hα, hβ, hu⟩ := hp
    have hδ : (2*M + (r+2)^2)/2 ≤ (p.1 + p.2)/2 := by linarith [hu]
    have hge := g2Minus_ge_linear hM3 hr hδ
    rw [g2Minus_boundary_eq] at hge
    have hδpos : (0:ℝ) < (p.1+p.2)/2 - (2*M + (r+2)^2)/2 := by linarith [hu]
    calc Real.exp (-g2Tilde M r p)
        = Real.exp (-(g2Minus M r ((p.1+p.2)/2) + ((p.1-p.2)/2)^2/2)) :=
          congrArg (fun x => Real.exp (-x)) (g2Tilde_eq_g2Minus_add M r p.1 p.2)
      _ ≤ Real.exp (-(((2*M + (r+2)^2)^2/8 - (r+2)^3/3)
            + (M/2)*((p.1+p.2)/2 - (2*M + (r+2)^2)/2) + ((p.1-p.2)/2)^2/2)) :=
          Real.exp_le_exp.mpr (neg_le_neg (by linarith [hge]))
      _ = Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3))
          * (Real.exp (-(M/2)*((p.1+p.2)/2 - (2*M + (r+2)^2)/2))
            * Real.exp (-((p.1-p.2)/2)^2/2)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ = Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3))
          * ((Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s))
              ((p.1+p.2)/2 - (2*M + (r+2)^2)/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)) := by
          rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hδpos)]
  -- the `h2MinusDom` integrability of `e^{−G̃₂}`
  have hint : IntegrableOn (fun p => Real.exp (-g2Tilde M r p)) (h2MinusDom M r) := by
    apply ((hplane.const_mul (Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3)))).integrableOn).mono' ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_g2Tilde M r).neg).measurable).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_h2MinusDom M r)] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact hpt p hp
  -- the conversion and the `δ`-tail evaluation
  have hconv := (setIntegral_ind_quadrant_eq_iterated (measurableSet_h2MinusDom M r)
    (hint.integrable_indicator (measurableSet_h2MinusDom M r)) (fun p hp => ⟨hp.1, hp.2.1⟩)).symm
  have hF2eval : ∫ δ : ℝ, (Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s))
        (δ - (2*M + (r+2)^2)/2) = 2/M := by
    rw [MeasureTheory.integral_sub_right_eq_self (μ := volume)
      (fun δ : ℝ => (Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s)) δ) ((2*M + (r+2)^2)/2),
      MeasureTheory.integral_indicator measurableSet_Ioi]
    rw [show (fun s : ℝ => Real.exp (-(M/2)*s)) = fun s => Real.exp (-(M/2 * s)) from
      funext fun s => by congr 1; rw [neg_mul]]
    exact (integral_exp_neg_mul_Ioi (by linarith [hM0'] : (0:ℝ) < M/2)).trans
      (show (1:ℝ)/(M/2) = 2/M by field_simp [hM0'.ne'])
  have hc1 : (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
        (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β))
      = ∫ p in h2MinusDom M r, Real.exp (-g2Tilde M r p) := hconv
  have hc2 : (∫ p in h2MinusDom M r, Real.exp (-g2Tilde M r p))
      ≤ ∫ p in h2MinusDom M r, Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3))
          * ((Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s))
              ((p.1+p.2)/2 - (2*M + (r+2)^2)/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)) :=
        setIntegral_mono_on hint ((hplane.const_mul _).integrableOn)
          (measurableSet_h2MinusDom M r) hpt
  have hc3 : (∫ p in h2MinusDom M r, Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3))
          * ((Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s))
              ((p.1+p.2)/2 - (2*M + (r+2)^2)/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)))
      ≤ ∫ p in (Set.univ : Set (ℝ × ℝ)), Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3))
          * ((Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s))
              ((p.1+p.2)/2 - (2*M + (r+2)^2)/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)) :=
        setIntegral_mono_set ((hplane.const_mul _).integrableOn)
          (Filter.Eventually.of_forall fun (p : ℝ × ℝ) =>
            mul_nonneg (Real.exp_pos _).le
              (mul_nonneg (Set.indicator_nonneg (fun s _ => (Real.exp_pos _).le) _)
                (Real.exp_pos _).le))
          (Filter.Eventually.of_forall fun (p : ℝ × ℝ) _ => Set.mem_univ p)
  have hc4 : (∫ p in (Set.univ : Set (ℝ × ℝ)), Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3))
          * ((Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s))
              ((p.1+p.2)/2 - (2*M + (r+2)^2)/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)))
      = ∫ p : ℝ × ℝ, Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3))
          * ((Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s))
              ((p.1+p.2)/2 - (2*M + (r+2)^2)/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)) := setIntegral_univ
  have hc5 : (∫ p : ℝ × ℝ, Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3))
          * ((Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s))
              ((p.1+p.2)/2 - (2*M + (r+2)^2)/2)
            * Real.exp (-((p.1-p.2)/2)^2/2)))
      = Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3))
          * (2 * (2/M) * Real.sqrt (2*Real.pi)) := by
        rw [integral_const_mul, Measure.volume_eq_prod]
        rw [show (fun p : ℝ × ℝ => (Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s))
                ((p.1+p.2)/2 - (2*M + (r+2)^2)/2)
              * Real.exp (-((p.1-p.2)/2)^2/2))
            = Function.uncurry (fun α β : ℝ => (Set.Ioi 0).indicator (fun s => Real.exp (-(M/2)*s))
                ((α+β)/2 - (2*M + (r+2)^2)/2)
              * Real.exp (-((α-β)/2)^2/2)) from funext fun p => rfl]
        rw [MeasureTheory.integral_prod _ hplane]
        simp only [Function.uncurry_apply_pair]
        rw [integral_mul_comp_half_add_half_sub hF2meas hF2int hGmeas hGint hG1, hF2eval,
          integral_exp_neg_sq_half]
  have hc6 : Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3))
          * (2 * (2/M) * Real.sqrt (2*Real.pi))
      ≤ (4 * Real.sqrt (2*Real.pi)) * Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3)) := by
        have hMe : (2:ℝ) * (2/M) * Real.sqrt (2*Real.pi) ≤ 4 * Real.sqrt (2*Real.pi) := by
          rw [show (2:ℝ) * (2/M) * Real.sqrt (2*Real.pi) = (4 * Real.sqrt (2*Real.pi))/M by
            field_simp [hM0'.ne']; ring]
          exact div_le_self (by positivity) hM1
        exact mul_le_mul_of_nonneg_left hMe (Real.exp_pos _).le |>.trans_eq (by ring)
  have hc7 : (4 * Real.sqrt (2*Real.pi)) * Real.exp (-((2*M + (r+2)^2)^2/8 - (r+2)^3/3))
      ≤ (4 * Real.sqrt (2*Real.pi)) * Real.exp (-(c0 * (2*M)^2)) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (neg_le_neg hE0M)) (by positivity)
  have hc8 : (4 * Real.sqrt (2*Real.pi)) * Real.exp (-(c0 * (2*M)^2))
      = (4 * Real.sqrt (2*Real.pi)) * Real.exp (-c0 * (2*M)^2) := by rw [neg_mul]
  exact hc1.le.trans (hc2.trans (hc3.trans (hc4.le.trans (hc5.le.trans (hc6.trans (hc7.trans
    hc8.le))))))

/-! ### D6: the FR main bounds -/

/-- **D6, the FR bound** (the paper's detailed FR bound — the
two-term form).  The `MemLp` hypotheses are the Tonelli-chain interface of `TwoIntervalTrace`
(discharged by `memLp_aRKer`/`memLp_wSKer` — see the `_discharged`
corollary below).  Constants existential; χ-dependence only through `C, c, M₀`
(via `S ≤ χa + 2` in the negative-Airy pieces). -/
theorem abs_trSectorFR_le {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ {M r a : ℝ}, M₀ ≤ M → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      MemLp (aRKer a M r) 2 (volume.prod volume) →
      MemLp (wSKer (2 + r) a) 2 (volume.prod volume) →
      |trSectorFR M r|
        ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r)
          + C * Real.exp (-c * (2*M)^2) := by
  obtain ⟨C1, hC1pos, hC1⟩ := abs_frI1_le
  obtain ⟨C2, hC2pos, hC2⟩ := abs_frI2_le
  obtain ⟨C4, hC4pos, hC4⟩ := abs_frI1_plus_le
  obtain ⟨C3, c3, M₃, hC3pos, hc3pos, hC3⟩ := abs_frI1_minus_le hχ0 hχ1
  obtain ⟨C4', hC4'pos, hC4'⟩ := abs_frI2_plus_le
  obtain ⟨C5, c5, M₅, hC5pos, hc5pos, hC5⟩ := abs_frI2_minus_le hχ0 hχ1
  refine ⟨C1*C4 + C2*C4' + (C1*C3 + C2*C5), min c3 c5, max 3 (max M₃ M₅),
    by positivity, lt_min hc3pos hc5pos, ?_⟩
  intro M r a hM0 hr hradm hA hW
  have hM3 : (3:ℝ) ≤ M := le_trans (le_max_left _ _) hM0
  have hM2 : (2:ℝ) ≤ M := by linarith
  have hM1 : (1:ℝ) ≤ M := by linarith
  have hMM₃ : M₃ ≤ M := (le_max_left M₃ M₅ |>.trans (le_max_right 3 _)).trans hM0
  have hMM₅ : M₅ ≤ M := (le_max_right M₃ M₅ |>.trans (le_max_right 3 _)).trans hM0
  have hr0 : (0:ℝ) < r := by linarith
  rw [trSectorFR_eq_frI1_add_frI2 hr0 a M hA hW]
  -- the assembled bound, unpacked
  calc |frI1 M r + frI2 M r|
      ≤ |frI1 M r| + |frI2 M r| := abs_add_le _ _
    _ ≤ (C1 * (r+2)^(-1/2 : ℝ) * ((∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
              (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β))
            + (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
              (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β))))
        + (C2 * ((∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
              (h2Dom M r).indicator (fun p => Real.exp (-h2Tilde M r p)) (α, β))
            + (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
              (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β)))) :=
        add_le_add (hC1 hr0) (hC2 hr0)
    _ = (C1 * ((r+2)^(-1/2 : ℝ) * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
              (h1Dom M r).indicator (fun p => Real.exp (-h1Exp M r p)) (α, β)))
          + C1 * ((r+2)^(-1/2 : ℝ) * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
              (h1MinusDom M r).indicator (fun p => Real.exp (-g1Exp M r p)) (α, β))))
        + (C2 * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
              (h2Dom M r).indicator (fun p => Real.exp (-h2Tilde M r p)) (α, β))
          + C2 * (∫ α in Set.Ici 0, ∫ β in Set.Ici 0,
              (h2MinusDom M r).indicator (fun p => Real.exp (-g2Tilde M r p)) (α, β))) := by ring
    _ ≤ (C1 * (C4 * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r))
          + C1 * (C3 * Real.exp (-c3 * (2*M)^2)))
        + (C2 * (C4' * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r))
          + C2 * (C5 * Real.exp (-c5 * (2*M)^2))) := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left (hC4 hM2 hr) hC1pos.le
          · exact mul_le_mul_of_nonneg_left (hC3 hMM₃ hr hradm) hC1pos.le
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left (hC4' hM2 hr) hC2pos.le
          · exact mul_le_mul_of_nonneg_left (hC5 hMM₅ hr hradm) hC2pos.le
    _ ≤ (C1*C4 + C2*C4' + (C1*C3 + C2*C5)) * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r)
          + (C1*C4 + C2*C4' + (C1*C3 + C2*C5)) * Real.exp (-(min c3 c5) * (2*M)^2) := by
        -- the `min` absorption: `e^{−c3(2M)²} ≤ e^{−(min c3 c5)(2M)²}` etc.
        have hXnn : (0:ℝ) ≤ (2*M)^2 := by positivity
        have hle1 : Real.exp (-c3 * (2*M)^2) ≤ Real.exp (-(min c3 c5) * (2*M)^2) := by
          apply Real.exp_le_exp.mpr
          have : (min c3 c5) * (2*M)^2 ≤ c3 * (2*M)^2 :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hXnn
          nlinarith [this]
        have hle2 : Real.exp (-c5 * (2*M)^2) ≤ Real.exp (-(min c3 c5) * (2*M)^2) := by
          apply Real.exp_le_exp.mpr
          have : (min c3 c5) * (2*M)^2 ≤ c5 * (2*M)^2 :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hXnn
          nlinarith [this]
        have hT1nn : (0:ℝ) ≤ (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by positivity
        have hC12nn : (0:ℝ) ≤ C1*C4 + C2*C4' :=
          add_nonneg (mul_nonneg hC1pos.le hC4pos.le) (mul_nonneg hC2pos.le hC4'pos.le)
        have hC35nn : (0:ℝ) ≤ C1*C3 + C2*C5 :=
          add_nonneg (mul_nonneg hC1pos.le hC3pos.le) (mul_nonneg hC2pos.le hC5pos.le)
        calc (C1 * (C4 * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r))
              + C1 * (C3 * Real.exp (-c3 * (2*M)^2)))
            + (C2 * (C4' * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r))
              + C2 * (C5 * Real.exp (-c5 * (2*M)^2)))
          = (C1*C4 + C2*C4') * ((1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r))
              + (C1*C3 * Real.exp (-c3 * (2*M)^2) + C2*C5 * Real.exp (-c5 * (2*M)^2)) := by ring
        _ ≤ (C1*C4 + C2*C4') * ((1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r))
              + (C1*C3 * Real.exp (-(min c3 c5) * (2*M)^2)
                + C2*C5 * Real.exp (-(min c3 c5) * (2*M)^2)) := by
            apply add_le_add_right
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hle1 (mul_nonneg hC1pos.le hC3pos.le)
            · exact mul_le_mul_of_nonneg_left hle2 (mul_nonneg hC2pos.le hC5pos.le)
        _ = (C1*C4 + C2*C4') * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r)
              + (C1*C3 + C2*C5) * Real.exp (-(min c3 c5) * (2*M)^2) := by ring
        _ ≤ (C1*C4 + C2*C4' + (C1*C3 + C2*C5)) * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r)
              + (C1*C4 + C2*C4' + (C1*C3 + C2*C5)) * Real.exp (-(min c3 c5) * (2*M)^2) := by
            apply add_le_add
            · calc (C1*C4 + C2*C4') * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r)
                  = (C1*C4 + C2*C4') * ((1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r)) := by ring
                _ ≤ (C1*C4 + C2*C4' + (C1*C3 + C2*C5))
                    * ((1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r)) :=
                    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC35nn) hT1nn
                _ = (C1*C4 + C2*C4' + (C1*C3 + C2*C5)) * (1+r)^(1/2 : ℝ)
                    * Real.exp (-saddleJ M r) := by ring
            · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC12nn)
                (Real.exp_pos _).le

/-- **D6, the absorbed form** (the paper's detailed FR bound): `|Tr C_r^{FR}| ≤ C_χ(1+r)^{1/2}e^{−J_M(r)}` — the second
term `e^{−c(2M)²}` is absorbed since `J_M(r) = O_χ((2M)^{3/2})` (`saddleJ_le_rpow`)
is dominated by `c(2M)²` for `2M ≥ (C/c)²`. -/
theorem abs_trSectorFR_le_absorbed {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C M₀ : ℝ, 0 < C ∧ ∀ {M r a : ℝ}, M₀ ≤ M → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      MemLp (aRKer a M r) 2 (volume.prod volume) →
      MemLp (wSKer (2 + r) a) 2 (volume.prod volume) →
      |trSectorFR M r| ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
  obtain ⟨C, c, M₀, hCpos, hcpos, hD6⟩ := abs_trSectorFR_le hχ0 hχ1
  obtain ⟨CJ', hJ'⟩ := saddleJ_le_rpow hχ0
  refine ⟨C + C, max M₀ (max 1 ((CJ'/c)^2/2)), by positivity, ?_⟩
  intro M r a hM0 hr hradm hA hW
  have hM0' : M₀ ≤ M := le_trans (le_max_left _ _) hM0
  have h1 := hD6 hM0' hr hradm hA hW
  have hM1 : (1:ℝ) ≤ M := le_trans (le_max_left 1 _ |>.trans (le_max_right M₀ _)) hM0
  have hM0pos : (0:ℝ) < M := by linarith
  have h2M : (0:ℝ) ≤ 2*M := by linarith
  -- the absorption: `saddleJ M r ≤ c·(2M)²` for `(CJ'/c)² ≤ 2M`
  have hbig : (CJ'/c)^2 ≤ 2*M := by
    have h : (CJ'/c)^2/2 ≤ M := le_trans (le_max_right 1 _ |>.trans (le_max_right M₀ _)) hM0
    nlinarith [h]
  set u := Real.sqrt (2*M) with hu
  have hu0 : (0:ℝ) ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = 2*M := Real.sq_sqrt h2M
  have ha32 : (2*M)^(3/2 : ℝ) = u^3 := by
    rw [← hu2, ← Real.rpow_natCast u 2, ← Real.rpow_mul hu0,
      show ((2:ℕ):ℝ)*(3/2) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hCJ'nn : (0:ℝ) ≤ CJ' := by
    have hsaddleJnn : (0:ℝ) ≤ saddleJ M r := by
      unfold saddleJ
      have hr1 : (0:ℝ) ≤ (2*M + r^2)^(3/2 : ℝ) :=
        Real.rpow_nonneg (by nlinarith [hM0pos, sq_nonneg r]) _
      nlinarith [hr1, sq_nonneg r, hM0pos, hr]
    have hpos : (0:ℝ) < (2*M)^(3/2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    exact (mul_nonneg_iff_of_pos_right hpos).mp (le_trans hsaddleJnn (hJ' hM1 hr hradm))
  have hule : CJ' ≤ c * u := by
    have h2 : CJ'/c ≤ u := by
      rw [Real.le_sqrt (div_nonneg hCJ'nn hcpos.le) h2M]
      exact hbig
    calc CJ' = (CJ'/c) * c := by field_simp [hcpos.ne']
      _ ≤ u * c := mul_le_mul_of_nonneg_right h2 hcpos.le
      _ = c * u := mul_comm _ _
  have hkey : saddleJ M r ≤ c * (2*M)^2 := by
    calc saddleJ M r ≤ CJ' * (2*M)^(3/2 : ℝ) := hJ' hM1 hr hradm
      _ = CJ' * u^3 := by rw [ha32]
      _ ≤ (c * u) * u^3 := mul_le_mul_of_nonneg_right hule (pow_nonneg hu0 3)
      _ = c * (2*M)^2 := by
          rw [← hu2]
          ring
  have hexp : Real.exp (-c * (2*M)^2) ≤ Real.exp (-saddleJ M r) := by
    apply Real.exp_le_exp.mpr
    rw [neg_mul]
    exact neg_le_neg hkey
  calc |trSectorFR M r|
      ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) + C * Real.exp (-c * (2*M)^2) := h1
    _ ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r)
          + C * Real.exp (-saddleJ M r) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hexp hCpos.le) _
    _ ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r)
          + C * ((1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r)) := by
        apply add_le_add_right
        have h1 : (1:ℝ) ≤ (1+r)^(1/2 : ℝ) :=
          Real.one_le_rpow (by linarith : (1:ℝ) ≤ 1 + r) (by norm_num : (0:ℝ) ≤ 1/2)
        have h2 : Real.exp (-saddleJ M r) ≤ (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
          calc Real.exp (-saddleJ M r) = 1 * Real.exp (-saddleJ M r) := (one_mul _).symm
            _ ≤ (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left h2 hCpos.le
    _ = (C + C) * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by ring

/-- **The fully discharged two-term bound** — the `MemLp` hypotheses
discharged at `a = √(2M)` by `memLp_aRKer` (`2 ≤ a`) and `memLp_wSKer`
(`r + 3 ≤ a`, from `r ≤ χa`, `χ < 1`, and `a ≥ 3/(1−χ)`, i.e. `M` large). -/
theorem abs_trSectorFR_le_discharged {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ {M r : ℝ}, M₀ ≤ M → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      |trSectorFR M r|
        ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r)
          + C * Real.exp (-c * (2*M)^2) := by
  obtain ⟨C, c, M₀, hCpos, hcpos, hD6⟩ := abs_trSectorFR_le hχ0 hχ1
  refine ⟨C, c, max M₀ (max 2 (9/(2*(1-χ)^2))), hCpos, hcpos, ?_⟩
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
    -- `(3/(1−χ))² ≤ 2M`
    have hsq : (3/(1-χ))^2 ≤ 2*M := by
      rw [div_pow, show (3:ℝ)^2 = 9 by norm_num]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (1-χ)^2)]
      -- `9 ≤ (2M)·(1−χ)²` from `9/(2(1−χ)²) ≤ M`
      have h2 : (0:ℝ) < (1-χ)^2 := by positivity
      have h3 := mul_le_mul_of_nonneg_right h1 h2.le
      have h4 : (9/(2*(1-χ)^2)) * (2*(1-χ)^2) = 9 := by
        field_simp [hχ'.ne']
      nlinarith [h3, h4]
    -- `3/(1−χ) ≤ √(2M)`
    have h3 : 3/(1-χ) ≤ Real.sqrt (2*M) := by
      rw [Real.le_sqrt (by positivity) h2M]
      exact hsq
    -- `r + 3 ≤ χ√(2M) + 3 ≤ √(2M)` since `3 ≤ (1−χ)√(2M)`
    have h4 : χ * Real.sqrt (2*M) + 3 ≤ Real.sqrt (2*M) := by
      have h5 : (3:ℝ) ≤ (1-χ) * Real.sqrt (2*M) := by
        rw [show (3:ℝ) = (1-χ) * (3/(1-χ)) by field_simp [hχ'.ne']]
        exact mul_le_mul_of_nonneg_left h3 (sub_pos.mpr hχ1).le
      nlinarith [h5, Real.sqrt_nonneg (2*M)]
    linarith [hradm, h4]
  exact hD6 hM0' hr hradm (memLp_aRKer hr0 hM0pos ha2) (memLp_wSKer hr0 hadr)

/-- **The fully discharged absorbed bound** — both the `MemLp`
discharge (as in `_discharged`) and the `e^{−c(2M)²}` absorption (as in
`_absorbed`). -/
theorem abs_trSectorFR_le_absorbed_discharged {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C M₀ : ℝ, 0 < C ∧ ∀ {M r : ℝ}, M₀ ≤ M → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      |trSectorFR M r| ≤ C * (1+r)^(1/2 : ℝ) * Real.exp (-saddleJ M r) := by
  obtain ⟨C, M₀, hCpos, hD6⟩ := abs_trSectorFR_le_absorbed hχ0 hχ1
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
