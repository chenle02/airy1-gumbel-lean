/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.AiryKernel.Conjugates
import Airy1GumbelContrib.AiryKernel.Conjugate2to2
import Airy1GumbelContrib.AiryKernel.TraceProduct
import Airy1GumbelContrib.TraceClass.FredholmOne

/-!
# Two-interval operator algebra

Part of `TwoInterval/`: the operator-algebra layer behind the paper's joint-determinant lemma
and the trace cancellation in Step 1 of the paper's separated-block estimate.

## Correspondence with the paper

* Setup of the paper's two-interval determinant formula: `S := 2T + r` with `T = 1`,
  `Λ := Λ^M_{[0,1]}`, `Q := P_1 − Λ`, and
  `K_∪ := (P_1 P_r P_1 − Λ P_r Λ) P_{-S} B_0`.
* `K₁ := Q P_{-1} B_0`, `K₂ := P_{1+r} Q P_{-(2+r)} B_0`.
* The joint-determinant lemma: the algebraic decomposition `K_∪ = K₁ + K₂ − C_r` with
  `C_r = Q P_r Q P_{-(2+r)} B_0`, conjugated to `K̃∪ = K̃₁ + K̃₂ − C̃_r`.
* Step 1 of the separated-block estimate: the trace cancellation
  `Tr K̃₁ + Tr K̃₂ − Tr K̃∪ = Tr C̃_r`.
* The R/F splitting `Q = Q^R + Q^F` with
  `Q^R(x, y) = 1_{x ≤ M, y ≤ M} p_1(2M − x − y)` and
  `Q^F(x, y) = 1_{x > M ∨ y > M} p_1(x − y)`.

## Conjugation convention

The conjugation is the multiplication-operator similarity `K̃ := U_a K U_a⁻¹`
with `U_a f(x) = e^{−a x} f(x)`, at the weight parameter `a = √(2M)`. On kernels this is
`uConj a K (x, y) = e^{−a x} K(x, y) e^{a y}`. We keep `a` as a free real parameter
since the algebra is uniform in `a`. The `φ`-weights of the paper's Hilbert–Schmidt
factorizations (`K̃₁ = (U_a Q U_a Φ)(Φ⁻¹ U_a⁻¹ P_{-1} B_0 U_a⁻¹)`) cancel and do not appear
in the conjugated kernels themselves; `compKernel_vKernel_wKernel` records the exact relation
to the weighted kernels `V_{T,a}, W_{T,a}`, generalizing the `T = 1` case
`K̃₁ = V_{1,a} W_{1,a}`.

## What is proved here

* **Kernel definitions** (`heatKerTwo`, `lamKerTwo`, `qKerTwo`, `qRKerTwo`,
  `qFKerTwo`, `bAiryKer`, `k1Ker`, `k2Ker`, `crKer`, `kcupKer` and the conjugates
  `k1KerT`, `k2KerT`, `crKerT`, `kcupKerT`), with measurability/continuity helpers
  and the pointwise dominations `0 ≤ Q ≤ P_1`, `0 ≤ Λ ≤ P_1`.
* **The R/F splitting** `qKerTwo_eq_RF` and `qKerTwo_eq_sub` (`Q = P₁ − Λ`).
* **Gaussian calculus**: Chapman–Kolmogorov `heatKernel_conv` (`P_s P_t = P_{s+t}`),
  the translated heat–Airy identity `heat_airy_conv_translate`, and the off-diagonal
  heat–Airy identity `heatAiryConv_offset`:
  `∫ u, p_t(w − u) g_S(u) du = g_{S−t}(w)` for `0 < t ≤ S` — the kernel-level form of
  the scalar heat–Airy identity `P_t (P_{-S} B₀) = P_{-(S−t)} B₀`
  (Quastel–Remenik 2012, Prop. 1.2). The diagonal case `t = S` is
  `heat_airy_conv` (`AiryKernel/`); the strict case is reduced to the translated diagonal
  identity by completing the square (`heatKernel_mul_exp_neg_eq`), avoiding a second
  round of the IBP/mollifier analysis.
* **The kernel-composition calculus**: `compKernel_assoc` (Fubini, given joint
  integrability), the linearity lemmas, and the domination/integrability library
  that instantiates them for the present Gaussian kernels (`0 ≤ Q ≤ P_1` and
  `|g_S(s)| ≤ C e^{S|s|}` drive every estimate).
* **`twoIntKCup_decomp_unconj`**: `kcupKer = k1Ker + k2Ker − crKer` and
  **`twoIntKCup_decomp`**: `kcupKerT = k1KerT + k2KerT − crKerT`
  (funext-level kernel identities).
* **Trace cancellation**: `trace_kcup_conj_decomp` (abstract) and
  `trace_twoIntKCup` (concrete): `Tr K̃₁ + Tr K̃₂ − Tr K̃∪ = Tr C̃_r`, conditional on
  `IsTraceClass` of the four conjugated operators. The trace-class membership of
  `K̃₁, K̃₂, K̃∪, C̃_r` is proved separately in `TwoInterval/TwoIntervalMembership.lean`, from
  the square-integral bounds `vKernel_sq_integral_le` / `wKernel_sq_integral_le` of
  `AiryKernel/`; here the identity is stated with explicit hypotheses.

## Notes

* `r` is taken as a real parameter with `0 < r` (the paper uses integer
  `r ≥ 1`); the operator algebra only needs `r > 0`.
* The decomposition and the trace cancellation are formalized exactly as stated in the paper.
* `trace_comp_comm` (`TraceClass/`) is available for the cyclicity step of
  the joint-determinant lemma but is *not* needed for the trace cancellation itself;
  it is re-exported here only through the imports.
-/

namespace AiryTwoInt

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal InnerProduct InnerProductSpace
open HilbertSchmidt

/-! ## The two-interval kernels -/

/-- The kernel of the heat operator `P_t` on `L²(ℝ)`: `p_t(x − z)`. -/
noncomputable def heatKerTwo (t : ℝ) : ℝ × ℝ → ℝ := fun p => heatKernel t (p.1 - p.2)

/-- The kernel of `Λ = Λ^M_{[0,1]}` (the formula for `Λ`, at `T = 1`):
`1_{x ≤ M, z ≤ M} (p_1(x − z) − p_1(2M − x − z))`. -/
noncomputable def lamKerTwo (M : ℝ) : ℝ × ℝ → ℝ :=
  (Set.Iic M ×ˢ Set.Iic M).indicator
    fun p => heatKernel 1 (p.1 - p.2) - heatKernel 1 (2 * M - p.1 - p.2)

/-- The kernel of `Q = P_1 − Λ`: the `T = 1` case of the
piecewise kernel `Q_{M,T}`, i.e. the
`AiryConj.qMT M 1` of `AiryKernel/`. -/
noncomputable def qKerTwo (M : ℝ) : ℝ × ℝ → ℝ := fun p => AiryConj.qMT M 1 p.1 p.2

/-- The reflected piece of the R/F splitting `Q = Q^R + Q^F`:
`Q^R(x, y) = 1_{x ≤ M, y ≤ M} p_1(2M − x − y)`. -/
noncomputable def qRKerTwo (M : ℝ) : ℝ × ℝ → ℝ :=
  (Set.Iic M ×ˢ Set.Iic M).indicator fun p => heatKernel 1 (2 * M - p.1 - p.2)

/-- The free piece of the R/F splitting:
`Q^F(x, y) = 1_{x > M ∨ y > M} p_1(x − y)`. -/
noncomputable def qFKerTwo (M : ℝ) : ℝ × ℝ → ℝ :=
  {p : ℝ × ℝ | M < p.1 ∨ M < p.2}.indicator fun p => heatKernel 1 (p.1 - p.2)

/-- The kernel of `P_{-S} B_0`: `g_S(z + y)` (the backward Airy kernel formula). -/
noncomputable def bAiryKer (S : ℝ) : ℝ × ℝ → ℝ := fun p => backwardAiry S (p.1 + p.2)

/-- `heatKerTwo` is continuous. -/
theorem continuous_heatKerTwo (t : ℝ) : Continuous (heatKerTwo t) :=
  (continuous_heatKernel t).comp (continuous_fst.sub continuous_snd)

/-- `heatKerTwo` is measurable. -/
theorem measurable_heatKerTwo (t : ℝ) : Measurable (heatKerTwo t) :=
  (continuous_heatKerTwo t).measurable

/-- The free region `{p | M < p.1 ∨ M < p.2}` is measurable. -/
theorem measurableSet_freeRegion (M : ℝ) :
    MeasurableSet {p : ℝ × ℝ | M < p.1 ∨ M < p.2} := by
  have h : {p : ℝ × ℝ | M < p.1 ∨ M < p.2}
      = (Set.Ioi M) ×ˢ Set.univ ∪ Set.univ ×ˢ (Set.Ioi M) := by
    ext ⟨x, z⟩
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_prod, Set.mem_Ioi, Set.mem_univ,
      and_true, true_and]
  rw [h]
  exact (measurableSet_Ioi.prod MeasurableSet.univ).union (MeasurableSet.univ.prod measurableSet_Ioi)

/-- The reflected region `(-∞, M] × (-∞, M]` is measurable. -/
theorem measurableSet_reflectedRegion' (M : ℝ) :
    MeasurableSet (Set.Iic M ×ˢ Set.Iic M : Set (ℝ × ℝ)) :=
  measurableSet_Iic.prod measurableSet_Iic

/-- `lamKerTwo` is measurable (indicator of a continuous function over a measurable
region). -/
theorem measurable_lamKerTwo (M : ℝ) : Measurable (lamKerTwo M) :=
  Measurable.indicator
    (((continuous_heatKernel 1).comp (continuous_fst.sub continuous_snd)).sub
      ((continuous_heatKernel 1).comp ((continuous_const.sub continuous_fst).sub
        continuous_snd))).measurable
    (measurableSet_reflectedRegion' M)

/-- `qKerTwo` is measurable (`measurable_qMT`). -/
theorem measurable_qKerTwo (M : ℝ) : Measurable (qKerTwo M) :=
  AiryConj.measurable_qMT M 1

/-- `qRKerTwo` is measurable. -/
theorem measurable_qRKerTwo (M : ℝ) : Measurable (qRKerTwo M) :=
  Measurable.indicator
    (((continuous_heatKernel 1).comp
      ((continuous_const.sub continuous_fst).sub continuous_snd)).measurable)
    (measurableSet_reflectedRegion' M)

/-- `qFKerTwo` is measurable. -/
theorem measurable_qFKerTwo (M : ℝ) : Measurable (qFKerTwo M) :=
  Measurable.indicator
    (((continuous_heatKernel 1).comp (continuous_fst.sub continuous_snd)).measurable)
    (measurableSet_freeRegion M)

/-- `bAiryKer` is continuous. -/
theorem continuous_bAiryKer (S : ℝ) : Continuous (bAiryKer S) :=
  continuous_backwardAiry.comp (continuous_const.prodMk (continuous_fst.add continuous_snd))

/-- `bAiryKer` is measurable. -/
theorem measurable_bAiryKer (S : ℝ) : Measurable (bAiryKer S) :=
  (continuous_bAiryKer S).measurable

/-- On the reflected region the reflected kernel is dominated by the free one:
`p_1(2M − x − z) ≤ p_1(x − z)` for `x, z ≤ M` (the boundary factor
`e^{−(M−x)(M−z)} ≤ 1` via `AiryConj.heatKernel_reflected_eq`). -/
theorem heatKernel_reflected_le {M x z : ℝ} (hx : x ≤ M) (hz : z ≤ M) :
    heatKernel 1 (2 * M - x - z) ≤ heatKernel 1 (x - z) := by
  rw [AiryConj.heatKernel_reflected_eq one_pos]
  have hnn : (0 : ℝ) ≤ heatKernel 1 (x - z) := (heatKernel_pos one_pos _).le
  calc heatKernel 1 (x - z) * Real.exp (-(M - x) * (M - z) / 1)
      ≤ heatKernel 1 (x - z) * 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by
          rw [div_one]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr hx))
            (sub_nonneg.mpr hz))) hnn
    _ = heatKernel 1 (x - z) := mul_one _

/-- `Q` is pointwise nonnegative. -/
theorem qKerTwo_nonneg (M : ℝ) (p : ℝ × ℝ) : 0 ≤ qKerTwo M p := by
  unfold qKerTwo AiryConj.qMT
  by_cases h : p.1 ≤ M ∧ p.2 ≤ M
  · rw [ite_eq_left h]
    exact (heatKernel_pos one_pos _).le
  · rw [ite_eq_right h]
    exact (heatKernel_pos one_pos _).le

/-- `Q ≤ P_1` pointwise (`0 ≤ Q ≤ P_1`). -/
theorem qKerTwo_le (M : ℝ) (p : ℝ × ℝ) : qKerTwo M p ≤ heatKernel 1 (p.1 - p.2) := by
  unfold qKerTwo AiryConj.qMT
  by_cases h : p.1 ≤ M ∧ p.2 ≤ M
  · rw [ite_eq_left h]
    exact heatKernel_reflected_le h.1 h.2
  · rw [ite_eq_right h]

/-- `|Q| ≤ P_1` pointwise. -/
theorem qKerTwo_abs_le (M : ℝ) (p : ℝ × ℝ) : |qKerTwo M p| ≤ heatKernel 1 (p.1 - p.2) := by
  rw [abs_of_nonneg (qKerTwo_nonneg M p)]
  exact qKerTwo_le M p

/-- `Λ` is pointwise nonnegative (on the reflected region the free kernel dominates
the reflected one). -/
theorem lamKerTwo_nonneg (M : ℝ) (p : ℝ × ℝ) : 0 ≤ lamKerTwo M p := by
  unfold lamKerTwo
  by_cases h : p ∈ Set.Iic M ×ˢ Set.Iic M
  · rw [Set.indicator_of_mem h]
    have h' : p.1 ≤ M ∧ p.2 ≤ M := Set.mem_prod.mp h
    exact sub_nonneg.mpr (heatKernel_reflected_le h'.1 h'.2)
  · rw [Set.indicator_of_notMem h]

/-- `Λ ≤ P_1` pointwise. -/
theorem lamKerTwo_le (M : ℝ) (p : ℝ × ℝ) : lamKerTwo M p ≤ heatKernel 1 (p.1 - p.2) := by
  unfold lamKerTwo
  by_cases h : p ∈ Set.Iic M ×ˢ Set.Iic M
  · rw [Set.indicator_of_mem h]
    exact sub_le_self _ (heatKernel_pos one_pos _).le
  · rw [Set.indicator_of_notMem h]
    exact (heatKernel_pos one_pos _).le

/-- `|Λ| ≤ P_1` pointwise. -/
theorem lamKerTwo_abs_le (M : ℝ) (p : ℝ × ℝ) : |lamKerTwo M p| ≤ heatKernel 1 (p.1 - p.2) := by
  rw [abs_of_nonneg (lamKerTwo_nonneg M p)]
  exact lamKerTwo_le M p

/-- `Q = P_1 − Λ` as kernels. -/
theorem qKerTwo_eq_sub (M : ℝ) (p : ℝ × ℝ) :
    qKerTwo M p = heatKerTwo 1 p - lamKerTwo M p := by
  unfold qKerTwo lamKerTwo heatKerTwo AiryConj.qMT
  by_cases h : p.1 ≤ M ∧ p.2 ≤ M
  · have hmem : p ∈ Set.Iic M ×ˢ Set.Iic M := Set.mem_prod.mpr h
    rw [ite_eq_left h, Set.indicator_of_mem hmem]
    ring
  · have hmem : p ∉ Set.Iic M ×ˢ Set.Iic M := fun hm => h (Set.mem_prod.mp hm)
    rw [ite_eq_right h, Set.indicator_of_notMem hmem, sub_zero]

/-- `Λ = P_1 − Q` as kernels (the form used in the expansion). -/
theorem lamKerTwo_eq_sub (M : ℝ) (p : ℝ × ℝ) :
    lamKerTwo M p = heatKerTwo 1 p - qKerTwo M p := by
  rw [qKerTwo_eq_sub]
  ring

/-- **The R/F splitting**: `Q = Q^R + Q^F` pointwise. -/
theorem qKerTwo_eq_RF (M : ℝ) (p : ℝ × ℝ) :
    qKerTwo M p = qRKerTwo M p + qFKerTwo M p := by
  unfold qKerTwo qRKerTwo qFKerTwo AiryConj.qMT
  by_cases h : p.1 ≤ M ∧ p.2 ≤ M
  · have hmem : p ∈ Set.Iic M ×ˢ Set.Iic M := Set.mem_prod.mpr h
    have hnmem : p ∉ {q : ℝ × ℝ | M < q.1 ∨ M < q.2} := by
      simp only [Set.mem_ofPred_eq, not_or, not_lt]
      exact ⟨h.1, h.2⟩
    rw [ite_eq_left h, Set.indicator_of_mem hmem, Set.indicator_of_notMem hnmem, add_zero]
  · have hmem : p ∉ Set.Iic M ×ˢ Set.Iic M := fun hm => h (Set.mem_prod.mp hm)
    have h2 : p ∈ {q : ℝ × ℝ | M < q.1 ∨ M < q.2} := by
      simp only [Set.mem_ofPred_eq]
      exact (not_and_or.mp h).elim (fun h1 => Or.inl (not_le.mp h1))
        (fun h2 => Or.inr (not_le.mp h2))
    rw [ite_eq_right h, Set.indicator_of_notMem hmem, Set.indicator_of_mem h2, zero_add]

/-- The composite kernel is measurable: partial Bochner integrals of measurable
functions are measurable (`StronglyMeasurable.integral_prod_right'`). -/
theorem measurable_compKernel {K K' : ℝ × ℝ → ℝ} (hK : Measurable K) (hK' : Measurable K') :
    Measurable (AiryConj.compKernel K K') := by
  have hF : Measurable (fun q : (ℝ × ℝ) × ℝ => K (q.1.1, q.2) * K' (q.2, q.1.2)) :=
    (hK.comp (((continuous_fst.comp continuous_fst).prodMk continuous_snd).measurable)).mul
      (hK'.comp ((continuous_snd.prodMk (continuous_snd.comp continuous_fst)).measurable))
  have h := hF.stronglyMeasurable.integral_prod_right' (ν := volume)
  exact h.measurable

/-! ## Gaussian calculus: the semigroup law and the off-diagonal heat–Airy identity -/

/-- The heat kernel is even. -/
theorem heatKernel_even (T : ℝ) (v : ℝ) : heatKernel T (-v) = heatKernel T v := by
  unfold heatKernel
  rw [neg_sq]

/-- `|p_t| ≤ p_t` pointwise for `0 < t` (helper for the domination library). -/
theorem heatKerTwo_abs_le_self (ht : 0 < t) (p : ℝ × ℝ) :
    |heatKerTwo t p| ≤ heatKernel t (p.1 - p.2) := by
  show |heatKernel t (p.1 - p.2)| ≤ heatKernel t (p.1 - p.2)
  rw [abs_of_nonneg (heatKernel_pos ht _).le]

/-- The heat kernel is bounded by its prefactor. -/
theorem heatKernel_le (hT : 0 < T) (v : ℝ) : heatKernel T v ≤ (4 * Real.pi * T)^(-1/2 : ℝ) := by
  have h : Real.exp (-v^2 / (4 * T)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg v))
      (by positivity))
  unfold heatKernel
  calc (4 * Real.pi * T)^(-1/2 : ℝ) * Real.exp (-v^2 / (4 * T))
      ≤ (4 * Real.pi * T)^(-1/2 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by positivity) _)
    _ = (4 * Real.pi * T)^(-1/2 : ℝ) := mul_one _

/-- **Gaussian exponential moment at an arbitrary rate**:
`∫ s, p_T(u − s) e^{c s} ds = e^{c u + T c²}` — the `P_T` action on a pure exponential.
Derived from `AiryConj.integral_conjugateHeatKernel` by reflection. -/
theorem integral_heatKernel_mul_exp (hT : 0 < T) (c u : ℝ) :
    ∫ s : ℝ, heatKernel T (u - s) * Real.exp (c * s) = Real.exp (c * u + T * c ^ 2) := by
  have hrefl : (∫ s : ℝ, heatKernel T (u - s) * Real.exp (c * s))
      = ∫ v : ℝ, heatKernel T v * Real.exp (c * (u - v)) := by
    set F : ℝ → ℝ := fun v => heatKernel T v * Real.exp (c * (u - v)) with hF
    have heq : (fun s : ℝ => heatKernel T (u - s) * Real.exp (c * s)) = fun s => F (u - s) := by
      funext s
      have harg : c * s = c * (u - (u - s)) := by ring
      rw [hF, harg]
    rw [heq]
    have h2 : (∫ s : ℝ, F (u - s)) = ∫ s : ℝ, F (-s) := by
      have h3 := MeasureTheory.integral_sub_right_eq_self (μ := volume) (fun s : ℝ => F (-s)) u
      have h4 : (fun s : ℝ => F (-(s - u))) = fun s => F (u - s) := funext fun s => by
        congr 1
        ring
      rw [h4] at h3
      exact h3
    rw [h2]
    exact MeasureTheory.integral_neg_eq_self F volume
  rw [hrefl]
  have heq2 : (fun v : ℝ => heatKernel T v * Real.exp (c * (u - v)))
      = fun v => Real.exp (c * u) * AiryConj.conjugateHeatKernel T c v := by
    funext v
    rw [AiryConj.conjugateHeatKernel, show c * (u - v) = c * u + (-c) * v by ring, Real.exp_add]
    ring
  rw [heq2, integral_const_mul, AiryConj.integral_conjugateHeatKernel hT c, ← Real.exp_add]

/-- `e^{c|s|} ≤ e^{cs} + e^{−cs}` for `0 ≤ c` (splitting on the sign of `s`). -/
theorem exp_mul_abs_le (c : ℝ) (s : ℝ) :
    Real.exp (c * |s|) ≤ Real.exp (c * s) + Real.exp (-(c * s)) := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hs, show c * -s = -(c * s) by ring]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- `z ↦ p_t(x − z) e^{c|z|}` is integrable for `0 < t` (the master envelope
`integrable_exp_neg_sq_add_abs`). -/
theorem integrable_heatKernel_mul_exp_abs (ht : 0 < t) (c x : ℝ) :
    Integrable fun z : ℝ => heatKernel t (x - z) * Real.exp (c * |z|) := by
  apply ((integrable_exp_neg_sq_add_abs (b := 1 / (4 * t)) (by positivity) c x).const_mul
    ((4 * Real.pi * t)^(-1/2 : ℝ))).mono' ?_ ?_
  · exact (((continuous_heatKernel t).comp (continuous_const.sub continuous_id)).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_abs)))).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_pos ht _).le,
      abs_of_nonneg (Real.exp_pos _).le]
    unfold heatKernel
    rw [show -(x - z)^2 / (4 * t) = -(1 / (4 * t)) * (z - x)^2 by ring, Real.exp_add]
    rw [mul_assoc]

/-- The Gaussian-×-two-sided-exponential moment bound:
`∫ s, p_T(u − s) e^{c|s|} ds ≤ 2 e^{Tc²} e^{c|u|}` for `0 ≤ c`. -/
theorem integral_heatKernel_mul_exp_abs_le (hT : 0 < T) {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    ∫ s : ℝ, heatKernel T (u - s) * Real.exp (c * |s|)
      ≤ 2 * Real.exp (T * c ^ 2) * Real.exp (c * |u|) := by
  have hint1 : Integrable fun s : ℝ => heatKernel T (u - s) * Real.exp (c * s) := by
    have heq : (fun s : ℝ => heatKernel T (u - s) * Real.exp (c * s))
        = fun s => Real.exp (c * u) * AiryConj.conjugateHeatKernel T c (u - s) := by
      funext s
      rw [AiryConj.conjugateHeatKernel, show c * s = c * u + (-c) * (u - s) by ring, Real.exp_add]
      ring
    rw [heq]
    apply Integrable.const_mul
    convert ((AiryConj.integrable_conjugateHeatKernel hT c).comp_neg).comp_sub_right u using 1
    ext s
    congr 1
    ring
  have hint2 : Integrable fun s : ℝ => heatKernel T (u - s) * Real.exp ((-c) * s) := by
    have heq : (fun s : ℝ => heatKernel T (u - s) * Real.exp ((-c) * s))
        = fun s => Real.exp ((-c) * u) * AiryConj.conjugateHeatKernel T (-c) (u - s) := by
      funext s
      rw [AiryConj.conjugateHeatKernel, show (-c) * s = (-c) * u + (-(-c)) * (u - s) by ring,
        Real.exp_add]
      ring
    rw [heq]
    apply Integrable.const_mul
    convert ((AiryConj.integrable_conjugateHeatKernel hT (-c)).comp_neg).comp_sub_right u using 1
    ext s
    congr 1
    ring
  have hsum : (∫ s : ℝ, heatKernel T (u - s) * (Real.exp (c * s) + Real.exp (-(c * s))))
      = Real.exp (c * u + T * c ^ 2) + Real.exp (-(c * u) + T * c ^ 2) := by
    rw [show (fun s : ℝ => heatKernel T (u - s) * (Real.exp (c * s) + Real.exp (-(c * s))))
        = fun s : ℝ => heatKernel T (u - s) * Real.exp (c * s)
          + heatKernel T (u - s) * Real.exp ((-c) * s) from
        funext fun s => by rw [show (-c) * s = -(c * s) by ring]; ring]
    rw [integral_add hint1 hint2, integral_heatKernel_mul_exp hT c u,
      integral_heatKernel_mul_exp hT (-c) u]
    rw [show (-c) ^ 2 = c ^ 2 by ring, show (-c) * u = -(c * u) by ring]
  calc ∫ s : ℝ, heatKernel T (u - s) * Real.exp (c * |s|)
      ≤ ∫ s : ℝ, heatKernel T (u - s) * (Real.exp (c * s) + Real.exp (-(c * s))) :=
        integral_mono (integrable_heatKernel_mul_exp_abs hT c u)
          ((hint1.add hint2).congr (Eventually.of_forall fun s => by
            rw [Pi.add_apply]; rw [show (-c) * s = -(c * s) by ring]; ring))
          fun s => mul_le_mul_of_nonneg_left (exp_mul_abs_le c s) (heatKernel_pos hT _).le
    _ = Real.exp (c * u + T * c ^ 2) + Real.exp (-(c * u) + T * c ^ 2) := hsum
    _ = Real.exp (T * c ^ 2) * (Real.exp (c * u) + Real.exp (-(c * u))) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ Real.exp (T * c ^ 2) * (Real.exp (c * |u|) + Real.exp (c * |u|)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply add_le_add
        · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self u) hc)
        · rw [show -(c * u) = c * (-u) by ring, show c * |u| = c * |-u| by rw [abs_neg]]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self (-u)) hc)
    _ = 2 * Real.exp (T * c ^ 2) * Real.exp (c * |u|) := by ring

/-- The prefactor identity for the Gaussian convolution:
`(4πs)^{-1/2} (4πt)^{-1/2} (4πst/(s+t))^{1/2} = (4π(s+t))^{-1/2}`. -/
theorem rpow_prefactor_gaussian_conv (hs : 0 < s) (ht : 0 < t) :
    (4 * Real.pi * s)^(-1/2 : ℝ) * (4 * Real.pi * t)^(-1/2 : ℝ)
      * (4 * Real.pi * s * t / (s + t))^(1/2 : ℝ)
      = (4 * Real.pi * (s + t))^(-1/2 : ℝ) := by
  have hst : (0 : ℝ) < s + t := add_pos hs ht
  have e4 : (4 * Real.pi * s)^(-1/2 : ℝ) = ((4 * Real.pi * s)^(1/2 : ℝ))⁻¹ := by
    rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by norm_num, Real.rpow_neg (by positivity)]
  have e5 : (4 * Real.pi * t)^(-1/2 : ℝ) = ((4 * Real.pi * t)^(1/2 : ℝ))⁻¹ := by
    rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by norm_num, Real.rpow_neg (by positivity)]
  have e6 : (4 * Real.pi * (s + t))^(-1/2 : ℝ) = ((4 * Real.pi * (s + t))^(1/2 : ℝ))⁻¹ := by
    rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by norm_num, Real.rpow_neg (by positivity)]
  rw [e4, e5, e6, ← mul_inv,
    ← Real.mul_rpow (show (0 : ℝ) ≤ 4 * Real.pi * s by positivity)
      (show (0 : ℝ) ≤ 4 * Real.pi * t by positivity)]
  rw [mul_comm, ← div_eq_mul_inv]
  rw [← Real.div_rpow (show (0 : ℝ) ≤ 4 * Real.pi * s * t / (s + t) by positivity)
    (show (0 : ℝ) ≤ 4 * Real.pi * s * (4 * Real.pi * t) by positivity)]
  rw [show 4 * Real.pi * s * t / (s + t) / (4 * Real.pi * s * (4 * Real.pi * t))
      = (4 * Real.pi * (s + t))⁻¹ by
    field_simp [hs.ne', ht.ne', hst.ne', Real.pi_ne_zero]]
  exact Real.inv_rpow (by positivity) _

/-- **Chapman–Kolmogorov** (the heat-semigroup law `P_s P_t = P_{s+t}` at kernel level):
`∫ u, p_s(x − u) p_t(u − y) du = p_{s+t}(x − y)`, by completing the square. -/
theorem heatKernel_conv (hs : 0 < s) (ht : 0 < t) (x y : ℝ) :
    ∫ u : ℝ, heatKernel s (x - u) * heatKernel t (u - y) = heatKernel (s + t) (x - y) := by
  have hst : (0 : ℝ) < s + t := add_pos hs ht
  set u₀ : ℝ := (t * x + s * y) / (s + t) with hu₀
  have hsq : ∀ u : ℝ, heatKernel s (x - u) * heatKernel t (u - y)
      = (4 * Real.pi * s)^(-1/2 : ℝ) * (4 * Real.pi * t)^(-1/2 : ℝ)
        * (Real.exp (-(x - y)^2 / (4 * (s + t)))
          * Real.exp (-((s + t) / (4 * s * t)) * (u - u₀)^2)) := by
    intro u
    unfold heatKernel
    have hE : -(x - u)^2 / (4 * s) + -(u - y)^2 / (4 * t)
        = -(x - y)^2 / (4 * (s + t)) + -((s + t) / (4 * s * t)) * (u - u₀)^2 := by
      rw [hu₀]
      field_simp [hs.ne', ht.ne', hst.ne']
      ring
    calc (4 * Real.pi * s)^(-1/2 : ℝ) * Real.exp (-(x - u)^2 / (4 * s))
          * ((4 * Real.pi * t)^(-1/2 : ℝ) * Real.exp (-(u - y)^2 / (4 * t)))
        = (4 * Real.pi * s)^(-1/2 : ℝ) * (4 * Real.pi * t)^(-1/2 : ℝ)
          * (Real.exp (-(x - u)^2 / (4 * s)) * Real.exp (-(u - y)^2 / (4 * t))) := by ring
      _ = (4 * Real.pi * s)^(-1/2 : ℝ) * (4 * Real.pi * t)^(-1/2 : ℝ)
          * Real.exp (-(x - u)^2 / (4 * s) + -(u - y)^2 / (4 * t)) := by rw [← Real.exp_add]
      _ = (4 * Real.pi * s)^(-1/2 : ℝ) * (4 * Real.pi * t)^(-1/2 : ℝ)
          * Real.exp (-(x - y)^2 / (4 * (s + t)) + -((s + t) / (4 * s * t)) * (u - u₀)^2) := by
          rw [hE]
      _ = (4 * Real.pi * s)^(-1/2 : ℝ) * (4 * Real.pi * t)^(-1/2 : ℝ)
          * (Real.exp (-(x - y)^2 / (4 * (s + t)))
            * Real.exp (-((s + t) / (4 * s * t)) * (u - u₀)^2)) := by rw [Real.exp_add]
  rw [show (fun u : ℝ => heatKernel s (x - u) * heatKernel t (u - y))
      = fun u => (4 * Real.pi * s)^(-1/2 : ℝ) * (4 * Real.pi * t)^(-1/2 : ℝ)
        * (Real.exp (-(x - y)^2 / (4 * (s + t)))
          * Real.exp (-((s + t) / (4 * s * t)) * (u - u₀)^2)) from funext hsq]
  rw [integral_const_mul, integral_const_mul]
  have hG : (∫ u : ℝ, Real.exp (-((s + t) / (4 * s * t)) * (u - u₀)^2))
      = Real.sqrt (4 * Real.pi * s * t / (s + t)) := by
    have hb : (0 : ℝ) < (s + t) / (4 * s * t) := by positivity
    have h1 : (∫ u : ℝ, Real.exp (-((s + t) / (4 * s * t)) * (u - u₀)^2))
        = ∫ u : ℝ, Real.exp (-((s + t) / (4 * s * t)) * u^2) :=
      MeasureTheory.integral_sub_right_eq_self (μ := volume)
        (fun u : ℝ => Real.exp (-((s + t) / (4 * s * t)) * u^2)) u₀
    rw [h1, integral_gaussian]
    congr 1
    field_simp [hs.ne', ht.ne', hst.ne', Real.pi_ne_zero, ne_of_gt hb]
  rw [hG, Real.sqrt_eq_rpow]
  rw [show (4 * Real.pi * s)^(-1/2 : ℝ) * (4 * Real.pi * t)^(-1/2 : ℝ)
        * (Real.exp (-(x - y)^2 / (4 * (s + t))) * (4 * Real.pi * s * t / (s + t))^(1/2 : ℝ))
      = ((4 * Real.pi * s)^(-1/2 : ℝ) * (4 * Real.pi * t)^(-1/2 : ℝ)
        * (4 * Real.pi * s * t / (s + t))^(1/2 : ℝ))
        * Real.exp (-(x - y)^2 / (4 * (s + t))) by ring,
    rpow_prefactor_gaussian_conv hs ht]
  rfl

/-- The heat-semigroup law as a `compKernel` identity: `P_s P_t = P_{s+t}`. -/
theorem heatKerTwo_comp (hs : 0 < s) (ht : 0 < t) :
    AiryConj.compKernel (heatKerTwo s) (heatKerTwo t) = heatKerTwo (s + t) :=
  funext fun p => heatKernel_conv hs ht p.1 p.2

/-- **The translated heat–Airy identity** (★):
`∫ s, p_T(x − s) e^{−Ts} Ai(s + c) ds = e^{Tc − T³/3} Ai(x + c − T²)`, from
`heat_airy_conv` (Quastel–Remenik 2012, Prop. 1.2) by the translation
`s ↦ s − (c − T²)`. -/
theorem heat_airy_conv_translate (hT : 0 < T) (c x : ℝ) :
    ∫ s : ℝ, heatKernel T (x - s) * (Real.exp (-(T * s)) * airyAiReal (s + c))
      = Real.exp (T * c - T ^ 3 / 3) * airyAiReal (x + c - T ^ 2) := by
  have hsub := (MeasureTheory.integral_sub_right_eq_self (μ := volume)
    (fun s : ℝ => heatKernel T (x - s) * (Real.exp (-(T * s)) * airyAiReal (s + c)))
    (c - T^2)).symm
  rw [hsub]
  have hpt : ∀ s : ℝ, heatKernel T (x - (s - (c - T^2)))
      * (Real.exp (-(T * (s - (c - T^2)))) * airyAiReal (s - (c - T^2) + c))
      = Real.exp (T * c - T^3) * (heatKernel T ((x + c - T^2) - s)
        * (Real.exp (-(T * s)) * airyAiReal (s + T^2))) := by
    intro s
    rw [show x - (s - (c - T^2)) = (x + c - T^2) - s by ring,
      show s - (c - T^2) + c = s + T^2 by ring,
      show -(T * (s - (c - T^2))) = (T * c - T^3) + -(T * s) by ring, Real.exp_add]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
  have hpt2 : ∀ s : ℝ, Real.exp (-(T * s)) * airyAiReal (s + T^2)
      = Real.exp (2 * T^3 / 3) * backwardAiry T s := by
    intro s
    unfold backwardAiry
    rw [show -(2/3) * T^3 - T * s = -(2 * T^3 / 3) + -(T * s) by ring, Real.exp_add,
      show Real.exp (2 * T^3 / 3) * (Real.exp (-(2 * T^3 / 3)) * Real.exp (-(T * s))
          * airyAiReal (s + T^2))
        = (Real.exp (2 * T^3 / 3) * Real.exp (-(2 * T^3 / 3)))
          * (Real.exp (-(T * s)) * airyAiReal (s + T^2)) by ring,
      ← Real.exp_add, show 2 * T^3 / 3 + -(2 * T^3 / 3) = (0:ℝ) by ring, Real.exp_zero,
      one_mul]
  rw [integral_congr_ae (Eventually.of_forall fun s => by rw [hpt2 s]),
    integral_congr_ae (Eventually.of_forall fun s =>
      mul_left_comm (heatKernel T ((x + c - T^2) - s)) (Real.exp (2 * T^3 / 3))
        (backwardAiry T s)),
    integral_const_mul, heat_airy_conv T hT, ← mul_assoc, ← Real.exp_add,
    show T * c - T^3 + 2 * T^3 / 3 = T * c - T^3 / 3 by ring]

/-- The completed-square shift: `p_t(w − u) e^{−cu} = e^{−cw + tc²} p_t(w − 2tc − u)`. -/
theorem heatKernel_mul_exp_neg_eq (t c w u : ℝ) :
    heatKernel t (w - u) * Real.exp (-(c * u))
      = Real.exp (-(c * w) + t * c ^ 2) * heatKernel t ((w - 2 * t * c) - u) := by
  by_cases ht : t = 0
  · subst ht
    have h0 : (4 * Real.pi * (0:ℝ))^(-1/2 : ℝ) = 0 := by
      rw [mul_zero, Real.zero_rpow (by norm_num : (-1/2 : ℝ) ≠ 0)]
    unfold heatKernel
    rw [h0]
    ring
  · unfold heatKernel
    have hE : -(w - u)^2 / (4 * t) + -(c * u)
        = (-(c * w) + t * c^2) + -(w - 2 * t * c - u)^2 / (4 * t) := by
      field_simp [ht]
      ring
    calc (4 * Real.pi * t)^(-1/2 : ℝ) * Real.exp (-(w - u)^2 / (4 * t)) * Real.exp (-(c * u))
        = (4 * Real.pi * t)^(-1/2 : ℝ) * Real.exp (-(w - u)^2 / (4 * t) + -(c * u)) := by
          rw [mul_assoc, ← Real.exp_add]
      _ = (4 * Real.pi * t)^(-1/2 : ℝ)
          * Real.exp ((-(c * w) + t * c^2) + -(w - 2 * t * c - u)^2 / (4 * t)) := by rw [hE]
      _ = Real.exp (-(c * w) + t * c^2)
          * ((4 * Real.pi * t)^(-1/2 : ℝ) * Real.exp (-(w - 2 * t * c - u)^2 / (4 * t))) := by
          rw [Real.exp_add]; ring

/-- **The off-diagonal heat–Airy identity** (the scalar heat–Airy identity
`P_t (P_{-S} B₀) = P_{-(S−t)} B₀`, Quastel–Remenik 2012, Prop. 1.2):
`∫ u, p_t(w − u) g_S(u) du = g_{S−t}(w)` for `0 < t ≤ S`.

The diagonal case `t = S` is `heat_airy_conv` (since `g_0 = Ai`). For `t < S`,
absorb `e^{−(S−t)u}` into the heat kernel by completing the square
(`heatKernel_mul_exp_neg_eq`), then close by the translated diagonal identity
`heat_airy_conv_translate`. The exponent identity is
`−(2/3)S³ − (S−t)w + t(S−t)² + tS² − t³/3 = −(2/3)(S−t)³ − (S−t)w`. -/
theorem heatAiryConv_offset {t S : ℝ} (ht : 0 < t) (htS : t ≤ S) (w : ℝ) :
    ∫ u : ℝ, heatKernel t (w - u) * backwardAiry S u = backwardAiry (S - t) w := by
  rcases htS.eq_or_lt with h | h
  · subst h
    rw [show t - t = (0:ℝ) by ring, backwardAiry_zero]
    exact heat_airy_conv t ht w
  · have hcpos : 0 < S - t := sub_pos.mpr h
    have hsplit : ∀ u : ℝ, heatKernel t (w - u) * backwardAiry S u
        = Real.exp (-(2/3) * S^3)
          * (heatKernel t (w - u) * (Real.exp (-(S * u)) * airyAiReal (u + S^2))) := by
      intro u
      unfold backwardAiry
      rw [show -(2/3) * S^3 - S * u = -(2/3) * S^3 + -(S * u) by ring, Real.exp_add]
      ring
    rw [integral_congr_ae (Eventually.of_forall hsplit), integral_const_mul]
    have habs : ∀ u : ℝ, heatKernel t (w - u) * (Real.exp (-(S * u)) * airyAiReal (u + S^2))
        = Real.exp (-((S - t) * w) + t * (S - t)^2)
          * (heatKernel t ((w - 2 * t * (S - t)) - u)
            * (Real.exp (-(t * u)) * airyAiReal (u + S^2))) := by
      intro u
      rw [show -(S * u) = -((S - t) * u) + -(t * u) by ring, Real.exp_add,
        show heatKernel t (w - u) * (Real.exp (-((S - t) * u)) * Real.exp (-(t * u))
            * airyAiReal (u + S^2))
          = (heatKernel t (w - u) * Real.exp (-((S - t) * u)))
            * (Real.exp (-(t * u)) * airyAiReal (u + S^2)) by ring,
        heatKernel_mul_exp_neg_eq t (S - t) w u]
      ring
    rw [integral_congr_ae (Eventually.of_forall habs), integral_const_mul,
      heat_airy_conv_translate ht (S^2) (w - 2 * t * (S - t))]
    unfold backwardAiry
    rw [show w - 2 * t * (S - t) + S^2 - t^2 = w + (S - t)^2 by ring]
    have hmul : Real.exp (-(2/3) * S^3) * Real.exp (-((S - t) * w) + t * (S - t)^2)
        * Real.exp (t * S^2 - t^3 / 3) = Real.exp (-(2/3) * (S - t)^3 - (S - t) * w) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [show Real.exp (-(2/3) * S^3) * (Real.exp (-((S - t) * w) + t * (S - t)^2)
          * (Real.exp (t * S^2 - t^3 / 3) * airyAiReal (w + (S - t)^2)))
        = (Real.exp (-(2/3) * S^3) * Real.exp (-((S - t) * w) + t * (S - t)^2)
          * Real.exp (t * S^2 - t^3 / 3)) * airyAiReal (w + (S - t)^2) by ring, hmul]

/-- The off-diagonal heat–Airy identity as a `compKernel` identity:
`P_t (P_{-S} B₀) = P_{-(S−t)} B₀` on kernels. -/
theorem heatKerTwo_comp_bAiryKer {t S : ℝ} (ht : 0 < t) (htS : t ≤ S) :
    AiryConj.compKernel (heatKerTwo t) (bAiryKer S) = bAiryKer (S - t) := by
  funext p
  show (∫ z : ℝ, heatKernel t (p.1 - z) * backwardAiry S (z + p.2))
      = backwardAiry (S - t) (p.1 + p.2)
  have hsub : (∫ z : ℝ, heatKernel t (p.1 - z) * backwardAiry S (z + p.2))
      = ∫ u : ℝ, heatKernel t (p.1 + p.2 - u) * backwardAiry S u := by
    rw [← MeasureTheory.integral_add_right_eq_self (μ := volume)
      (fun u : ℝ => heatKernel t (p.1 + p.2 - u) * backwardAiry S u) p.2]
    apply integral_congr_ae
    filter_upwards with z
    have h : p.1 - z = p.1 + p.2 - (z + p.2) := by ring
    rw [h]
  rw [hsub]
  exact heatAiryConv_offset ht htS (p.1 + p.2)

/-! ## The kernel-composition calculus

`AiryConj.compKernel K K' (x, y) = ∫ z, K (x, z) * K' (z, y)` is the kernel of the
operator composition. We prove pointwise linearity in each argument (given slice
integrability) and pointwise associativity (given joint integrability, by Fubini), plus
the domination library that discharges the integrability side conditions for the
present Gaussian kernels. -/

/-- `|a| ≤ b` from `0 ≤ a ≤ b`. -/
theorem abs_le_of_nonneg_of_le {a b : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ b) : |a| ≤ b := by
  rw [abs_of_nonneg h0]
  exact h1

/-- Right-linearity of `compKernel` over subtraction (pointwise, given slice
integrability). -/
theorem compKernel_sub_right {A B C : ℝ × ℝ → ℝ} (x y : ℝ)
    (hB : Integrable fun z => A (x, z) * B (z, y))
    (hC : Integrable fun z => A (x, z) * C (z, y)) :
    AiryConj.compKernel A (fun p => B p - C p) (x, y)
      = AiryConj.compKernel A B (x, y) - AiryConj.compKernel A C (x, y) := by
  show (∫ z : ℝ, A (x, z) * (B (z, y) - C (z, y)))
    = (∫ z : ℝ, A (x, z) * B (z, y)) - (∫ z : ℝ, A (x, z) * C (z, y))
  rw [show (∫ z : ℝ, A (x, z) * (B (z, y) - C (z, y)))
      = ∫ z : ℝ, (A (x, z) * B (z, y) - A (x, z) * C (z, y)) from
    integral_congr_ae (Eventually.of_forall fun z => by ring)]
  exact integral_sub hB hC

/-- Left-linearity of `compKernel` over subtraction (pointwise, given slice
integrability). -/
theorem compKernel_sub_left {A B C : ℝ × ℝ → ℝ} (x y : ℝ)
    (hA : Integrable fun z => A (x, z) * C (z, y))
    (hB : Integrable fun z => B (x, z) * C (z, y)) :
    AiryConj.compKernel (fun p => A p - B p) C (x, y)
      = AiryConj.compKernel A C (x, y) - AiryConj.compKernel B C (x, y) := by
  show (∫ z : ℝ, (A (x, z) - B (x, z)) * C (z, y))
    = (∫ z : ℝ, A (x, z) * C (z, y)) - (∫ z : ℝ, B (x, z) * C (z, y))
  rw [show (∫ z : ℝ, (A (x, z) - B (x, z)) * C (z, y))
      = ∫ z : ℝ, (A (x, z) * C (z, y) - B (x, z) * C (z, y)) from
    integral_congr_ae (Eventually.of_forall fun z => by ring)]
  exact integral_sub hA hB

/-- `compKernel_sub_left` transported across a function-level equation for the left
factor (avoids rewriting the other factors). -/
theorem compKernel_sub_left' {A B C AB : ℝ × ℝ → ℝ} (hAB : AB = fun p => A p - B p) (x y : ℝ)
    (hA : Integrable fun z => A (x, z) * C (z, y))
    (hB : Integrable fun z => B (x, z) * C (z, y)) :
    AiryConj.compKernel AB C (x, y)
      = AiryConj.compKernel A C (x, y) - AiryConj.compKernel B C (x, y) := by
  rw [hAB]
  exact compKernel_sub_left x y hA hB

/-- Left-linearity of `compKernel` over addition (pointwise, given slice
integrability). -/
theorem compKernel_add_left {A B C : ℝ × ℝ → ℝ} (x y : ℝ)
    (hA : Integrable fun z => A (x, z) * C (z, y))
    (hB : Integrable fun z => B (x, z) * C (z, y)) :
    AiryConj.compKernel (fun p => A p + B p) C (x, y)
      = AiryConj.compKernel A C (x, y) + AiryConj.compKernel B C (x, y) := by
  show (∫ z : ℝ, (A (x, z) + B (x, z)) * C (z, y))
    = (∫ z : ℝ, A (x, z) * C (z, y)) + (∫ z : ℝ, B (x, z) * C (z, y))
  rw [show (∫ z : ℝ, (A (x, z) + B (x, z)) * C (z, y))
      = ∫ z : ℝ, (A (x, z) * C (z, y) + B (x, z) * C (z, y)) from
    integral_congr_ae (Eventually.of_forall fun z => by ring)]
  exact integral_add hA hB

/-- **Kernel-composition associativity** at a point, given joint integrability of the
triple product (Fubini): `((A B) C)(x, y) = (A (B C))(x, y)`. -/
theorem compKernel_assoc {A B C : ℝ × ℝ → ℝ} (x y : ℝ)
    (hInt : Integrable (Function.uncurry fun z₁ z₂ : ℝ => A (x, z₁) * (B (z₁, z₂) * C (z₂, y)))
      (volume.prod volume)) :
    AiryConj.compKernel (AiryConj.compKernel A B) C (x, y)
      = AiryConj.compKernel A (AiryConj.compKernel B C) (x, y) := by
  have hswap := MeasureTheory.integral_integral_swap (μ := volume) (ν := volume)
    (f := fun z₁ z₂ : ℝ => A (x, z₁) * (B (z₁, z₂) * C (z₂, y))) hInt
  show (∫ z₂ : ℝ, (∫ z₁ : ℝ, A (x, z₁) * B (z₁, z₂)) * C (z₂, y))
    = ∫ z₁ : ℝ, A (x, z₁) * (∫ z₂ : ℝ, B (z₁, z₂) * C (z₂, y))
  rw [show (fun z₂ : ℝ => (∫ z₁ : ℝ, A (x, z₁) * B (z₁, z₂)) * C (z₂, y))
      = fun z₂ => ∫ z₁ : ℝ, A (x, z₁) * (B (z₁, z₂) * C (z₂, y)) from funext fun z₂ => by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with z₁
    ring]
  rw [show (fun z₁ : ℝ => A (x, z₁) * (∫ z₂ : ℝ, B (z₁, z₂) * C (z₂, y)))
      = fun z₁ => ∫ z₂ : ℝ, A (x, z₁) * (B (z₁, z₂) * C (z₂, y)) from funext fun z₁ => by
    rw [integral_const_mul]]
  exact hswap.symm

/-- Slice integrability for a product of two kernels dominated by heat kernels. -/
theorem integrable_pair_mul_of_heatKernel_le (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    {K₁ K₂ : ℝ × ℝ → ℝ} (hK₁meas : Measurable K₁) (hK₂meas : Measurable K₂)
    (hK₁ : ∀ x z : ℝ, |K₁ (x, z)| ≤ heatKernel t₁ (x - z))
    (hK₂ : ∀ x z : ℝ, |K₂ (x, z)| ≤ heatKernel t₂ (x - z)) (x z : ℝ) :
    Integrable fun w : ℝ => K₁ (x, w) * K₂ (w, z) := by
  apply (((integrable_heatKernel ht₂).comp_sub_right z).const_mul
    ((4 * Real.pi * t₁)^(-1/2 : ℝ))).mono' ?_ ?_
  · exact ((hK₁meas.comp (continuous_const.prodMk continuous_id).measurable).mul
      (hK₂meas.comp (continuous_id.prodMk continuous_const).measurable)).aestronglyMeasurable
  · filter_upwards with w
    rw [Real.norm_eq_abs, abs_mul]
    calc |K₁ (x, w)| * |K₂ (w, z)|
        ≤ heatKernel t₁ (x - w) * heatKernel t₂ (w - z) :=
          mul_le_mul (hK₁ x w) (hK₂ w z) (abs_nonneg _) (heatKernel_pos ht₁ _).le
      _ ≤ (4 * Real.pi * t₁)^(-1/2 : ℝ) * heatKernel t₂ (w - z) :=
          mul_le_mul_of_nonneg_right (heatKernel_le ht₁ _) (heatKernel_pos ht₂ _).le

/-- **Master Tonelli bound**: the Gaussian–Gaussian–exponential product is jointly
integrable; it dominates every composition-regrouping integrand below. -/
theorem integrable_uncurry_heatKernel_mul_mul_exp_abs (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    {c : ℝ} (_hc : 0 ≤ c) (x : ℝ) :
    Integrable (Function.uncurry fun z₁ z₂ : ℝ =>
      heatKernel t₁ (x - z₁) * (heatKernel t₂ (z₁ - z₂) * Real.exp (c * |z₂|)))
      (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun z₁ z₂ : ℝ =>
      heatKernel t₁ (x - z₁) * (heatKernel t₂ (z₁ - z₂) * Real.exp (c * |z₂|)))
      (volume.prod volume) :=
    Continuous.aestronglyMeasurable
      (((continuous_heatKernel t₁).comp (continuous_const.sub continuous_fst)).mul
        (((continuous_heatKernel t₂).comp (continuous_fst.sub continuous_snd)).mul
          (Real.continuous_exp.comp (continuous_const.mul (continuous_snd.abs)))))
  rw [MeasureTheory.integrable_prod_iff' hmeas]
  constructor
  · -- the slice integrability, for fixed `z₂`, in `z₁`
    filter_upwards with z₂
    simp only [Function.uncurry_apply_pair]
    apply (((integrable_heatKernel ht₁).comp_sub_right x).const_mul
      ((4 * Real.pi * t₂)^(-1/2 : ℝ) * Real.exp (c * |z₂|))).mono' ?_ ?_
    · have hc1 : Continuous fun z₁ : ℝ => heatKernel t₁ (x - z₁) :=
        (continuous_heatKernel t₁).comp (continuous_const.sub continuous_id)
      have hc2 : Continuous fun z₁ : ℝ => heatKernel t₂ (z₁ - z₂) :=
        (continuous_heatKernel t₂).comp (continuous_id.sub continuous_const)
      have hc3 : Continuous fun _ : ℝ => Real.exp (c * |z₂|) := continuous_const
      exact (hc1.mul (hc2.mul hc3)).aestronglyMeasurable
    · filter_upwards with z₁
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_pos ht₁ _).le,
        abs_mul, abs_of_nonneg (heatKernel_pos ht₂ _).le, abs_of_nonneg (Real.exp_pos _).le]
      calc heatKernel t₁ (x - z₁) * (heatKernel t₂ (z₁ - z₂) * Real.exp (c * |z₂|))
          ≤ heatKernel t₁ (x - z₁) * ((4 * Real.pi * t₂)^(-1/2 : ℝ) * Real.exp (c * |z₂|)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (heatKernel_le ht₂ _) (Real.exp_pos _).le)
              (heatKernel_pos ht₁ _).le
        _ = (4 * Real.pi * t₂)^(-1/2 : ℝ) * Real.exp (c * |z₂|) * heatKernel t₁ (z₁ - x) := by
            rw [show x - z₁ = -(z₁ - x) by ring, heatKernel_even]
            ring
  · -- the outer integrability: the `z₁`-integral is a closed form by Chapman–Kolmogorov
    simp only [Function.uncurry_apply_pair]
    have hclosed : (fun z₂ : ℝ => ∫ z₁ : ℝ, ‖heatKernel t₁ (x - z₁)
        * (heatKernel t₂ (z₁ - z₂) * Real.exp (c * |z₂|))‖)
        = fun z₂ => Real.exp (c * |z₂|) * heatKernel (t₁ + t₂) (x - z₂) := by
      funext z₂
      have hnn : (∫ z₁ : ℝ, ‖heatKernel t₁ (x - z₁)
          * (heatKernel t₂ (z₁ - z₂) * Real.exp (c * |z₂|))‖)
          = ∫ z₁ : ℝ, heatKernel t₁ (x - z₁)
            * (heatKernel t₂ (z₁ - z₂) * Real.exp (c * |z₂|)) := by
        apply integral_congr_ae
        filter_upwards with z₁
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (heatKernel_pos ht₁ _).le,
          abs_of_nonneg (heatKernel_pos ht₂ _).le, abs_of_nonneg (Real.exp_pos _).le]
      rw [hnn]
      rw [show (fun z₁ : ℝ => heatKernel t₁ (x - z₁)
            * (heatKernel t₂ (z₁ - z₂) * Real.exp (c * |z₂|)))
          = fun z₁ => (heatKernel t₁ (x - z₁) * heatKernel t₂ (z₁ - z₂)) * Real.exp (c * |z₂|)
          from funext fun z₁ => by rw [mul_assoc]]
      rw [integral_mul_const, heatKernel_conv ht₁ ht₂ x z₂]
      ring
    rw [hclosed]
    exact (integrable_heatKernel_mul_exp_abs (add_pos ht₁ ht₂) c x).congr
      (Eventually.of_forall fun z₂ => mul_comm _ _)

/-- The generic regrouping integrability: products dominated by
`p_{t₁}(x − z₁) · p_{t₂}(z₁ − z₂) · C e^{c|z₂|}` are jointly integrable. -/
theorem integrable_uncurry_of_abs_le (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) {c : ℝ} (hc : 0 ≤ c)
    (x : ℝ) {A : ℝ × ℝ → ℝ} (hAmeas : Measurable A)
    (hA : ∀ z : ℝ, |A (x, z)| ≤ heatKernel t₁ (x - z))
    {B : ℝ × ℝ → ℝ} (hBmeas : Measurable B)
    (hB : ∀ z₁ z₂ : ℝ, |B (z₁, z₂)| ≤ heatKernel t₂ (z₁ - z₂))
    {φ : ℝ → ℝ} (hφmeas : Measurable φ) (C : ℝ)
    (hφ : ∀ z : ℝ, |φ z| ≤ C * Real.exp (c * |z|)) :
    Integrable (Function.uncurry fun z₁ z₂ : ℝ => A (x, z₁) * (B (z₁, z₂) * φ z₂))
      (volume.prod volume) := by
  apply ((integrable_uncurry_heatKernel_mul_mul_exp_abs ht₁ ht₂ hc x).const_mul C).mono' ?_ ?_
  · exact ((hAmeas.comp (continuous_const.prodMk continuous_fst).measurable).mul
      ((hBmeas.comp (continuous_fst.prodMk continuous_snd).measurable).mul
        (hφmeas.comp continuous_snd.measurable))).aestronglyMeasurable
  · filter_upwards with p
    obtain ⟨z₁, z₂⟩ := p
    simp only [Function.uncurry_apply_pair]
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |A (x, z₁)| * (|B (z₁, z₂)| * |φ z₂|)
        ≤ heatKernel t₁ (x - z₁) * (heatKernel t₂ (z₁ - z₂) * (C * Real.exp (c * |z₂|))) :=
          mul_le_mul (hA z₁)
            (mul_le_mul (hB z₁ z₂) (hφ z₂) (abs_nonneg _) (heatKernel_pos ht₂ _).le)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (heatKernel_pos ht₁ _).le
      _ = C * (heatKernel t₁ (x - z₁) * (heatKernel t₂ (z₁ - z₂) * Real.exp (c * |z₂|))) := by
          ring

/-- The backward-Airy pointwise exponential bound at its own temperature:
`|g_S(s)| ≤ C e^{S|s|}` for `0 ≤ S` (from `backwardAiry_abs_le_exp`). -/
theorem bAiry_abs_le_exp {S : ℝ} (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |backwardAiry S s| ≤ C * Real.exp (S * |s|) := by
  obtain ⟨C, hC⟩ := backwardAiry_abs_le_exp S
  have hCS : ∀ s : ℝ, |backwardAiry S s| ≤ C * Real.exp (S * |s|) :=
    hC S ⟨hS, le_rfl⟩
  have hCnn : 0 ≤ C := by
    have h0 := hCS 0
    simp at h0
    exact le_trans (abs_nonneg _) h0
  exact ⟨C, hCnn, hCS⟩

/-- `|g_S(z + y)| ≤ (C e^{S|y|}) e^{S|z|}` (absorbing the `y`-shift). -/
theorem bAiryKer_abs_le_exp {S : ℝ} (hS : 0 ≤ S) (y : ℝ) :
    ∃ C : ℝ, ∀ z : ℝ, |bAiryKer S (z, y)| ≤ C * Real.exp (S * |z|) := by
  obtain ⟨C, hCnn, hCS⟩ := bAiry_abs_le_exp hS
  refine ⟨C * Real.exp (S * |y|), fun z => ?_⟩
  calc |bAiryKer S (z, y)|
      = |backwardAiry S (z + y)| := rfl
    _ ≤ C * Real.exp (S * |z + y|) := hCS (z + y)
    _ ≤ C * (Real.exp (S * |y|) * Real.exp (S * |z|)) := by
        apply mul_le_mul_of_nonneg_left _ hCnn
        rw [← Real.exp_add, show S * |y| + S * |z| = S * (|z| + |y|) by ring]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_add_le z y) hS)
    _ = C * Real.exp (S * |y|) * Real.exp (S * |z|) := by ring

/-- Slice integrability against the backward-Airy factor:
`z ↦ K (x, z) · g_S(z + y)` when `|K (x, ·)| ≤ p_t(x − ·)`. -/
theorem integrable_mul_bAiryKer_of_abs_le (hS : 0 < S) (ht : 0 < t) {K : ℝ × ℝ → ℝ}
    (hKmeas : Measurable K) (x y : ℝ) (hK : ∀ z : ℝ, |K (x, z)| ≤ heatKernel t (x - z)) :
    Integrable fun z : ℝ => K (x, z) * bAiryKer S (z, y) := by
  obtain ⟨C, hC⟩ := bAiryKer_abs_le_exp hS.le y
  apply ((integrable_heatKernel_mul_exp_abs ht S x).const_mul C).mono' ?_ ?_
  · have hK1 : Measurable fun z : ℝ => K (x, z) :=
      hKmeas.comp (continuous_const.prodMk continuous_id).measurable
    have hK2 : Measurable fun z : ℝ => bAiryKer S (z, y) :=
      (measurable_bAiryKer S).comp (continuous_id.prodMk continuous_const).measurable
    exact (hK1.mul hK2).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    calc |K (x, z)| * |bAiryKer S (z, y)|
        ≤ heatKernel t (x - z) * (C * Real.exp (S * |z|)) :=
          mul_le_mul (hK z) (hC z) (abs_nonneg _) (heatKernel_pos ht _).le
      _ = C * (heatKernel t (x - z) * Real.exp (S * |z|)) := by ring

/-! ## The two-interval operators as kernels -/

/-- The kernel of `K₁ = Q P_{-1}B₀` (the definitions of `K₁, K₂`). -/
noncomputable def k1Ker (M : ℝ) : ℝ × ℝ → ℝ :=
  AiryConj.compKernel (qKerTwo M) (bAiryKer 1)

/-- The kernel of `K₂ = P_{1+r} Q P_{-(2+r)}B₀` (the definitions of `K₁, K₂`). -/
noncomputable def k2Ker (M r : ℝ) : ℝ × ℝ → ℝ :=
  AiryConj.compKernel (heatKerTwo (1 + r))
    (AiryConj.compKernel (qKerTwo M) (bAiryKer (2 + r)))

/-- The kernel of `C_r = Q P_r Q P_{-(2+r)}B₀`. -/
noncomputable def crKer (M r : ℝ) : ℝ × ℝ → ℝ :=
  AiryConj.compKernel (qKerTwo M)
    (AiryConj.compKernel (heatKerTwo r)
      (AiryConj.compKernel (qKerTwo M) (bAiryKer (2 + r))))

/-- The kernel of `K_∪ = (P_1 P_r P_1 − Λ P_r Λ) P_{-S}B₀`, `S = 2 + r`
(the definition of `K∪`, at `T = 1`). -/
noncomputable def kcupKer (M r : ℝ) : ℝ × ℝ → ℝ :=
  AiryConj.compKernel
    (fun q => AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r)
        (heatKerTwo 1)) q
      - AiryConj.compKernel (lamKerTwo M) (AiryConj.compKernel (heatKerTwo r)
        (lamKerTwo M)) q)
    (bAiryKer (2 + r))

/-- `k1Ker` is measurable. -/
theorem measurable_k1Ker (M : ℝ) : Measurable (k1Ker M) :=
  measurable_compKernel (measurable_qKerTwo M) (measurable_bAiryKer 1)

/-- `k2Ker` is measurable. -/
theorem measurable_k2Ker (M r : ℝ) : Measurable (k2Ker M r) :=
  measurable_compKernel (measurable_heatKerTwo (1 + r))
    (measurable_compKernel (measurable_qKerTwo M) (measurable_bAiryKer (2 + r)))

/-- `crKer` is measurable. -/
theorem measurable_crKer (M r : ℝ) : Measurable (crKer M r) :=
  measurable_compKernel (measurable_qKerTwo M)
    (measurable_compKernel (measurable_heatKerTwo r)
      (measurable_compKernel (measurable_qKerTwo M) (measurable_bAiryKer (2 + r))))

/-- `kcupKer` is measurable. -/
theorem measurable_kcupKer (M r : ℝ) : Measurable (kcupKer M r) :=
  measurable_compKernel
    ((measurable_compKernel (measurable_heatKerTwo 1)
      (measurable_compKernel (measurable_heatKerTwo r) (measurable_heatKerTwo 1))).sub
      (measurable_compKernel (measurable_lamKerTwo M)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_lamKerTwo M))))
    (measurable_bAiryKer (2 + r))

/-! ## The domination and regrouping-integrability library -/

/-- `0 ≤ (P_r Q)(u, z)` (both kernels nonnegative). -/
theorem compKernel_heatKerTwo_qKerTwo_nonneg (hr : 0 < r) (M : ℝ) (u z : ℝ) :
    0 ≤ AiryConj.compKernel (heatKerTwo r) (qKerTwo M) (u, z) :=
  integral_nonneg fun _ => mul_nonneg (heatKernel_pos hr _).le (qKerTwo_nonneg M _)

/-- `(P_r Q)(u, z) ≤ p_{r+1}(u − z)` (kernel-level `Q ≤ P_1` + Chapman–Kolmogorov). -/
theorem compKernel_heatKerTwo_qKerTwo_le (hr : 0 < r) (M : ℝ) (u z : ℝ) :
    AiryConj.compKernel (heatKerTwo r) (qKerTwo M) (u, z) ≤ heatKernel (r + 1) (u - z) := by
  have h1 : Integrable fun v : ℝ => heatKerTwo r (u, v) * qKerTwo M (v, z) :=
    integrable_pair_mul_of_heatKernel_le hr one_pos (measurable_heatKerTwo r)
      (measurable_qKerTwo M) (fun a b => heatKerTwo_abs_le_self hr (a, b))
      (fun a b => qKerTwo_abs_le M (a, b)) u z
  have h2 : Integrable fun v : ℝ => heatKerTwo r (u, v) * heatKerTwo 1 (v, z) :=
    integrable_pair_mul_of_heatKernel_le hr one_pos (measurable_heatKerTwo r)
      (measurable_heatKerTwo 1) (fun a b => heatKerTwo_abs_le_self hr (a, b))
      (fun a b => heatKerTwo_abs_le_self one_pos (a, b)) u z
  calc AiryConj.compKernel (heatKerTwo r) (qKerTwo M) (u, z)
      ≤ ∫ v : ℝ, heatKerTwo r (u, v) * heatKerTwo 1 (v, z) :=
        integral_mono h1 h2 fun v =>
          mul_le_mul_of_nonneg_left (qKerTwo_le M (v, z)) (heatKernel_pos hr _).le
    _ = heatKernel (r + 1) (u - z) := heatKernel_conv hr one_pos u z

/-- `|(P_r Q)(u, z)| ≤ p_{r+1}(u − z)`. -/
theorem compKernel_heatKerTwo_qKerTwo_abs_le (hr : 0 < r) (M : ℝ) (u z : ℝ) :
    |AiryConj.compKernel (heatKerTwo r) (qKerTwo M) (u, z)| ≤ heatKernel (r + 1) (u - z) :=
  abs_le_of_nonneg_of_le (compKernel_heatKerTwo_qKerTwo_nonneg hr M u z)
    (compKernel_heatKerTwo_qKerTwo_le hr M u z)

/-- `0 ≤ (P_r Λ)(u, z)`. -/
theorem compKernel_heatKerTwo_lamKerTwo_nonneg (hr : 0 < r) (M : ℝ) (u z : ℝ) :
    0 ≤ AiryConj.compKernel (heatKerTwo r) (lamKerTwo M) (u, z) :=
  integral_nonneg fun _ => mul_nonneg (heatKernel_pos hr _).le (lamKerTwo_nonneg M _)

/-- `(P_r Λ)(u, z) ≤ p_{r+1}(u − z)`. -/
theorem compKernel_heatKerTwo_lamKerTwo_le (hr : 0 < r) (M : ℝ) (u z : ℝ) :
    AiryConj.compKernel (heatKerTwo r) (lamKerTwo M) (u, z) ≤ heatKernel (r + 1) (u - z) := by
  have h1 : Integrable fun v : ℝ => heatKerTwo r (u, v) * lamKerTwo M (v, z) :=
    integrable_pair_mul_of_heatKernel_le hr one_pos (measurable_heatKerTwo r)
      (measurable_lamKerTwo M) (fun a b => heatKerTwo_abs_le_self hr (a, b))
      (fun a b => lamKerTwo_abs_le M (a, b)) u z
  have h2 : Integrable fun v : ℝ => heatKerTwo r (u, v) * heatKerTwo 1 (v, z) :=
    integrable_pair_mul_of_heatKernel_le hr one_pos (measurable_heatKerTwo r)
      (measurable_heatKerTwo 1) (fun a b => heatKerTwo_abs_le_self hr (a, b))
      (fun a b => heatKerTwo_abs_le_self one_pos (a, b)) u z
  calc AiryConj.compKernel (heatKerTwo r) (lamKerTwo M) (u, z)
      ≤ ∫ v : ℝ, heatKerTwo r (u, v) * heatKerTwo 1 (v, z) :=
        integral_mono h1 h2 fun v =>
          mul_le_mul_of_nonneg_left (lamKerTwo_le M (v, z)) (heatKernel_pos hr _).le
    _ = heatKernel (r + 1) (u - z) := heatKernel_conv hr one_pos u z

/-- `|(P_r Λ)(u, z)| ≤ p_{r+1}(u − z)`. -/
theorem compKernel_heatKerTwo_lamKerTwo_abs_le (hr : 0 < r) (M : ℝ) (u z : ℝ) :
    |AiryConj.compKernel (heatKerTwo r) (lamKerTwo M) (u, z)| ≤ heatKernel (r + 1) (u - z) :=
  abs_le_of_nonneg_of_le (compKernel_heatKerTwo_lamKerTwo_nonneg hr M u z)
    (compKernel_heatKerTwo_lamKerTwo_le hr M u z)

/-- Generic outer-composition bound: if `0 ≤ A ≤ p_1` and `0 ≤ B ≤ p_{r+1}` pointwise,
then `|(A B)(x, z)| ≤ p_{2+r}(x − z)`. -/
theorem compKernel_abs_le_two_add (hr : 0 < r) {A B : ℝ × ℝ → ℝ}
    (hAmeas : Measurable A) (hBmeas : Measurable B)
    (hAnn : ∀ x z : ℝ, 0 ≤ A (x, z)) (hA : ∀ x z : ℝ, A (x, z) ≤ heatKernel 1 (x - z))
    (hBnn : ∀ u z : ℝ, 0 ≤ B (u, z)) (hB : ∀ u z : ℝ, B (u, z) ≤ heatKernel (r + 1) (u - z))
    (x z : ℝ) :
    |AiryConj.compKernel A B (x, z)| ≤ heatKernel (2 + r) (x - z) := by
  have hnn : 0 ≤ AiryConj.compKernel A B (x, z) :=
    integral_nonneg fun w => mul_nonneg (hAnn _ _) (hBnn _ _)
  rw [abs_of_nonneg hnn]
  have h1 : Integrable fun w : ℝ => A (x, w) * B (w, z) :=
    integrable_pair_mul_of_heatKernel_le one_pos (by linarith : (0:ℝ) < r + 1) hAmeas hBmeas
      (fun a b => abs_le_of_nonneg_of_le (hAnn a b) (hA a b))
      (fun a b => abs_le_of_nonneg_of_le (hBnn a b) (hB a b)) x z
  have h2 : Integrable fun w : ℝ => heatKernel 1 (x - w) * heatKernel (r + 1) (w - z) :=
    integrable_pair_mul_of_heatKernel_le one_pos (by linarith : (0:ℝ) < r + 1)
      (measurable_heatKerTwo 1) (measurable_heatKerTwo (r + 1))
      (fun a b => heatKerTwo_abs_le_self one_pos (a, b))
      (fun a b => heatKerTwo_abs_le_self (by linarith) (a, b)) x z
  calc AiryConj.compKernel A B (x, z)
      ≤ ∫ w : ℝ, heatKernel 1 (x - w) * heatKernel (r + 1) (w - z) :=
        integral_mono h1 h2 fun w =>
          mul_le_mul (hA x w) (hB w z) (hBnn _ _) (heatKernel_pos one_pos _).le
    _ = heatKernel (1 + (r + 1)) (x - z) := heatKernel_conv one_pos (by linarith) x z
    _ = heatKernel (2 + r) (x - z) := by rw [show (1:ℝ) + (r + 1) = 2 + r by ring]

/-- `|(P_1 (P_r Q))(x, z)| ≤ p_{2+r}(x − z)`. -/
theorem compKernel_one_PrQ_abs_le (hr : 0 < r) (M : ℝ) (x z : ℝ) :
    |AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) (x, z)|
      ≤ heatKernel (2 + r) (x - z) :=
  compKernel_abs_le_two_add hr (measurable_heatKerTwo 1)
    (measurable_compKernel (measurable_heatKerTwo r) (measurable_qKerTwo M))
    (fun _ _ => (heatKernel_pos one_pos _).le) (fun _ _ => le_rfl)
    (fun a b => compKernel_heatKerTwo_qKerTwo_nonneg hr M a b)
    (fun a b => compKernel_heatKerTwo_qKerTwo_le hr M a b) x z

/-- `|(Q (P_r P_1))(x, z)| ≤ p_{2+r}(x − z)`. -/
theorem compKernel_Q_Pr_P1_abs_le (hr : 0 < r) (M : ℝ) (x z : ℝ) :
    |AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1)) (x, z)|
      ≤ heatKernel (2 + r) (x - z) := by
  rw [heatKerTwo_comp hr one_pos]
  exact compKernel_abs_le_two_add hr (measurable_qKerTwo M) (measurable_heatKerTwo (r + 1))
    (fun a b => qKerTwo_nonneg M (a, b)) (fun a b => qKerTwo_le M (a, b))
    (fun a b => (heatKernel_pos (by linarith) _).le) (fun a b => le_rfl) x z

/-- `|(Q (P_r Q))(x, z)| ≤ p_{2+r}(x − z)`. -/
theorem compKernel_Q_Pr_Q_abs_le (hr : 0 < r) (M : ℝ) (x z : ℝ) :
    |AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) (x, z)|
      ≤ heatKernel (2 + r) (x - z) :=
  compKernel_abs_le_two_add hr (measurable_qKerTwo M)
    (measurable_compKernel (measurable_heatKerTwo r) (measurable_qKerTwo M))
    (fun a b => qKerTwo_nonneg M (a, b)) (fun a b => qKerTwo_le M (a, b))
    (fun a b => compKernel_heatKerTwo_qKerTwo_nonneg hr M a b)
    (fun a b => compKernel_heatKerTwo_qKerTwo_le hr M a b) x z

/-- Joint integrability for the `(P_1 P_r) Q` reassociation. -/
theorem integrable_assoc_P1_Pr_Q (hr : 0 < r) (M u v : ℝ) :
    Integrable (Function.uncurry fun z₁ z₂ : ℝ =>
      heatKerTwo 1 (u, z₁) * (heatKerTwo r (z₁, z₂) * qKerTwo M (z₂, v)))
      (volume.prod volume) :=
  integrable_uncurry_of_abs_le one_pos hr le_rfl u (measurable_heatKerTwo 1)
    (fun z => heatKerTwo_abs_le_self one_pos (u, z))
    (measurable_heatKerTwo r) (fun z₁ z₂ => heatKerTwo_abs_le_self hr (z₁, z₂))
    ((measurable_qKerTwo M).comp (continuous_id.prodMk continuous_const).measurable)
    ((4 * Real.pi * 1)^(-1/2 : ℝ))
    (fun z => by
      rw [zero_mul, Real.exp_zero, mul_one]
      exact (qKerTwo_abs_le M (z, v)).trans (heatKernel_le one_pos _))

/-- Joint integrability for the `(P_{1+r} Q) (P_{-S}B₀)` reassociation. -/
theorem integrable_assoc_P1r_Q_GS (hr : 0 < r) (M x y : ℝ) :
    Integrable (Function.uncurry fun z₁ z₂ : ℝ =>
      heatKerTwo (1 + r) (x, z₁) * (qKerTwo M (z₁, z₂) * bAiryKer (2 + r) (z₂, y)))
      (volume.prod volume) := by
  obtain ⟨C, hC⟩ := bAiryKer_abs_le_exp (by linarith : (0:ℝ) ≤ 2 + r) y
  exact integrable_uncurry_of_abs_le (by linarith : (0:ℝ) < 1 + r) one_pos
    (by linarith : (0:ℝ) ≤ 2 + r) x (measurable_heatKerTwo (1 + r))
    (fun z => heatKerTwo_abs_le_self (by linarith) (x, z))
    (measurable_qKerTwo M) (fun z₁ z₂ => qKerTwo_abs_le M (z₁, z₂))
    ((measurable_bAiryKer (2 + r)).comp (continuous_id.prodMk continuous_const).measurable) C hC

/-- Joint integrability for the `(Q P_{r+1}) (P_{-S}B₀)` reassociation. -/
theorem integrable_assoc_Q_P1r_GS (hr : 0 < r) (M x y : ℝ) :
    Integrable (Function.uncurry fun z₁ z₂ : ℝ =>
      qKerTwo M (x, z₁) * (heatKerTwo (r + 1) (z₁, z₂) * bAiryKer (2 + r) (z₂, y)))
      (volume.prod volume) := by
  obtain ⟨C, hC⟩ := bAiryKer_abs_le_exp (by linarith : (0:ℝ) ≤ 2 + r) y
  exact integrable_uncurry_of_abs_le one_pos (by linarith : (0:ℝ) < r + 1)
    (by linarith : (0:ℝ) ≤ 2 + r) x (measurable_qKerTwo M)
    (fun z => qKerTwo_abs_le M (x, z))
    (measurable_heatKerTwo (r + 1))
    (fun z₁ z₂ => heatKerTwo_abs_le_self (by linarith) (z₁, z₂))
    ((measurable_bAiryKer (2 + r)).comp (continuous_id.prodMk continuous_const).measurable) C hC

/-- Joint integrability for the `(Q (P_r Q)) (P_{-S}B₀)` reassociation. -/
theorem integrable_assoc_Q_PrQ_GS (hr : 0 < r) (M x y : ℝ) :
    Integrable (Function.uncurry fun z₁ z₂ : ℝ =>
      qKerTwo M (x, z₁)
        * (AiryConj.compKernel (heatKerTwo r) (qKerTwo M) (z₁, z₂) * bAiryKer (2 + r) (z₂, y)))
      (volume.prod volume) := by
  obtain ⟨C, hC⟩ := bAiryKer_abs_le_exp (by linarith : (0:ℝ) ≤ 2 + r) y
  exact integrable_uncurry_of_abs_le one_pos (by linarith : (0:ℝ) < r + 1)
    (by linarith : (0:ℝ) ≤ 2 + r) x (measurable_qKerTwo M)
    (fun z => qKerTwo_abs_le M (x, z))
    (measurable_compKernel (measurable_heatKerTwo r) (measurable_qKerTwo M))
    (fun z₁ z₂ => compKernel_heatKerTwo_qKerTwo_abs_le hr M z₁ z₂)
    ((measurable_bAiryKer (2 + r)).comp (continuous_id.prodMk continuous_const).measurable) C hC

/-- Joint integrability for the `(P_r Q) (P_{-S}B₀)` reassociation. -/
theorem integrable_assoc_Pr_Q_GS (hr : 0 < r) (M u y : ℝ) :
    Integrable (Function.uncurry fun z₁ z₂ : ℝ =>
      heatKerTwo r (u, z₁) * (qKerTwo M (z₁, z₂) * bAiryKer (2 + r) (z₂, y)))
      (volume.prod volume) := by
  obtain ⟨C, hC⟩ := bAiryKer_abs_le_exp (by linarith : (0:ℝ) ≤ 2 + r) y
  exact integrable_uncurry_of_abs_le hr one_pos
    (by linarith : (0:ℝ) ≤ 2 + r) u (measurable_heatKerTwo r)
    (fun z => heatKerTwo_abs_le_self hr (u, z))
    (measurable_qKerTwo M) (fun z₁ z₂ => qKerTwo_abs_le M (z₁, z₂))
    ((measurable_bAiryKer (2 + r)).comp (continuous_id.prodMk continuous_const).measurable) C hC

/-! ## The kernel-level inclusion–exclusion and the main decomposition -/

/-- **The kernel-level inclusion–exclusion**:
`P_1 P_r P_1 − Λ P_r Λ = P_1 P_r Q + Q P_r P_1 − Q P_r Q` pointwise, from `Λ = P_1 − Q`
by linearity of the kernel composition. -/
theorem kcupDiffKer_eq (hr : 0 < r) (M : ℝ) (u z : ℝ) :
    AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1)) (u, z)
      - AiryConj.compKernel (lamKerTwo M) (AiryConj.compKernel (heatKerTwo r) (lamKerTwo M)) (u, z)
    = AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) (u, z)
      + AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1)) (u, z)
      - AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) (u, z) := by
  have hInner : ∀ w : ℝ, AiryConj.compKernel (heatKerTwo r) (lamKerTwo M) (w, z)
      = AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1) (w, z)
        - AiryConj.compKernel (heatKerTwo r) (qKerTwo M) (w, z) := by
    intro w
    rw [show lamKerTwo M = fun p => heatKerTwo 1 p - qKerTwo M p from
      funext fun p => lamKerTwo_eq_sub M p]
    exact compKernel_sub_right w z
      (integrable_pair_mul_of_heatKernel_le hr one_pos (measurable_heatKerTwo r)
        (measurable_heatKerTwo 1) (fun a b => heatKerTwo_abs_le_self hr (a, b))
        (fun a b => heatKerTwo_abs_le_self one_pos (a, b)) w z)
      (integrable_pair_mul_of_heatKernel_le hr one_pos (measurable_heatKerTwo r)
        (measurable_qKerTwo M) (fun a b => heatKerTwo_abs_le_self hr (a, b))
        (fun a b => qKerTwo_abs_le M (a, b)) w z)
  have hOuter : AiryConj.compKernel (lamKerTwo M) (AiryConj.compKernel (heatKerTwo r)
        (lamKerTwo M)) (u, z)
      = AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r) (lamKerTwo M)) (u, z)
        - AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (lamKerTwo M)) (u, z) :=
    compKernel_sub_left' (funext fun p => lamKerTwo_eq_sub M p) u z
      (integrable_pair_mul_of_heatKernel_le one_pos (by linarith : (0:ℝ) < r + 1)
        (measurable_heatKerTwo 1)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_lamKerTwo M))
        (fun a b => heatKerTwo_abs_le_self one_pos (a, b))
        (fun a b => compKernel_heatKerTwo_lamKerTwo_abs_le hr M a b) u z)
      (integrable_pair_mul_of_heatKernel_le one_pos (by linarith : (0:ℝ) < r + 1)
        (measurable_qKerTwo M)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_lamKerTwo M))
        (fun a b => qKerTwo_abs_le M (a, b))
        (fun a b => compKernel_heatKerTwo_lamKerTwo_abs_le hr M a b) u z)
  rw [hOuter]
  have h1 : AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r) (lamKerTwo M)) (u, z)
      = AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1)) (u, z)
        - AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) (u, z) := by
    have hcongr : AiryConj.compKernel (heatKerTwo 1)
        (AiryConj.compKernel (heatKerTwo r) (lamKerTwo M)) (u, z)
        = AiryConj.compKernel (heatKerTwo 1)
          (fun p => AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1) p
            - AiryConj.compKernel (heatKerTwo r) (qKerTwo M) p) (u, z) := by
      show (∫ w : ℝ, heatKerTwo 1 (u, w)
          * AiryConj.compKernel (heatKerTwo r) (lamKerTwo M) (w, z))
        = ∫ w : ℝ, heatKerTwo 1 (u, w)
          * (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1) (w, z)
            - AiryConj.compKernel (heatKerTwo r) (qKerTwo M) (w, z))
      apply integral_congr_ae
      filter_upwards with w
      rw [hInner w]
    rw [hcongr]
    exact compKernel_sub_right u z
      (integrable_pair_mul_of_heatKernel_le one_pos (show (0:ℝ) < r + 1 by linarith) (measurable_heatKerTwo 1)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_heatKerTwo 1))
        (fun a b => heatKerTwo_abs_le_self one_pos (a, b))
        (fun a b => by rw [heatKerTwo_comp hr one_pos]; exact heatKerTwo_abs_le_self (by linarith) (a, b))
        u z)
      (integrable_pair_mul_of_heatKernel_le one_pos (show (0:ℝ) < r + 1 by linarith) (measurable_heatKerTwo 1)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_qKerTwo M))
        (fun a b => heatKerTwo_abs_le_self one_pos (a, b))
        (fun a b => compKernel_heatKerTwo_qKerTwo_abs_le hr M a b) u z)
  have h2 : AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (lamKerTwo M)) (u, z)
      = AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1)) (u, z)
        - AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) (u, z) := by
    have hcongr : AiryConj.compKernel (qKerTwo M)
        (AiryConj.compKernel (heatKerTwo r) (lamKerTwo M)) (u, z)
        = AiryConj.compKernel (qKerTwo M)
          (fun p => AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1) p
            - AiryConj.compKernel (heatKerTwo r) (qKerTwo M) p) (u, z) := by
      show (∫ w : ℝ, qKerTwo M (u, w)
          * AiryConj.compKernel (heatKerTwo r) (lamKerTwo M) (w, z))
        = ∫ w : ℝ, qKerTwo M (u, w)
          * (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1) (w, z)
            - AiryConj.compKernel (heatKerTwo r) (qKerTwo M) (w, z))
      apply integral_congr_ae
      filter_upwards with w
      rw [hInner w]
    rw [hcongr]
    exact compKernel_sub_right u z
      (integrable_pair_mul_of_heatKernel_le one_pos (show (0:ℝ) < r + 1 by linarith) (measurable_qKerTwo M)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_heatKerTwo 1))
        (fun a b => qKerTwo_abs_le M (a, b))
        (fun a b => by rw [heatKerTwo_comp hr one_pos]; exact heatKerTwo_abs_le_self (by linarith) (a, b))
        u z)
      (integrable_pair_mul_of_heatKernel_le one_pos (show (0:ℝ) < r + 1 by linarith) (measurable_qKerTwo M)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_qKerTwo M))
        (fun a b => qKerTwo_abs_le M (a, b))
        (fun a b => compKernel_heatKerTwo_qKerTwo_abs_le hr M a b) u z)
  rw [h1, h2]
  ring

/-- `[Q P_r P_1] P_{-S}B₀ = K₁`: CK merges `P_r P_1 = P_{r+1}`,
Fubini reassociates, and the off-diagonal heat–Airy identity evaluates
`P_{r+1} (P_{-S}B₀) = P_{-1}B₀` (S = 2+r). -/
theorem compKernel_QPrP1_bAiryKer_eq_k1Ker (hr : 0 < r) (M : ℝ) :
    AiryConj.compKernel
      (AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1)))
      (bAiryKer (2 + r))
      = k1Ker M := by
  rw [heatKerTwo_comp hr one_pos]
  funext p
  obtain ⟨x, y⟩ := p
  rw [compKernel_assoc x y (integrable_assoc_Q_P1r_GS hr M x y),
    heatKerTwo_comp_bAiryKer (show (0:ℝ) < r + 1 by linarith) (show r + 1 ≤ 2 + r by linarith),
    show (2 + r) - (r + 1) = (1:ℝ) by ring]
  rfl

/-- `[P_1 P_r Q] P_{-S}B₀ = K₂`: Fubini reassociates
`P_1 (P_r Q) = (P_1 P_r) Q`, CK merges `P_1 P_r = P_{1+r}`, Fubini reassociates back. -/
theorem compKernel_P1PrQ_bAiryKer_eq_k2Ker (hr : 0 < r) (M : ℝ) :
    AiryConj.compKernel
      (AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)))
      (bAiryKer (2 + r))
      = k2Ker M r := by
  have hA : AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M))
      = AiryConj.compKernel (AiryConj.compKernel (heatKerTwo 1) (heatKerTwo r)) (qKerTwo M) := by
    funext q
    exact (compKernel_assoc q.1 q.2 (integrable_assoc_P1_Pr_Q hr M q.1 q.2)).symm
  rw [hA, heatKerTwo_comp one_pos hr]
  funext p
  obtain ⟨x, y⟩ := p
  rw [compKernel_assoc x y (integrable_assoc_P1r_Q_GS hr M x y)]
  rfl

/-- `[Q P_r Q] P_{-S}B₀ = C_r`: two Fubini reassociations. -/
theorem compKernel_QPrQ_bAiryKer_eq_crKer (hr : 0 < r) (M : ℝ) :
    AiryConj.compKernel
      (AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)))
      (bAiryKer (2 + r))
      = crKer M r := by
  funext p
  obtain ⟨x, y⟩ := p
  rw [compKernel_assoc x y (integrable_assoc_Q_PrQ_GS hr M x y)]
  have hinner : AiryConj.compKernel (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) (bAiryKer (2 + r))
      = AiryConj.compKernel (heatKerTwo r) (AiryConj.compKernel (qKerTwo M) (bAiryKer (2 + r))) := by
    funext q
    exact compKernel_assoc q.1 q.2 (integrable_assoc_Pr_Q_GS hr M q.1 q.2)
  rw [hinner]
  rfl

/-- **The two-interval decomposition**, unconjugated pointwise form:
`K_∪(x, y) = K_1(x, y) + K_2(x, y) - C_r(x, y)`. -/
theorem twoIntKCup_decomp_unconj_apply (hr : 0 < r) (M : ℝ) (p : ℝ × ℝ) :
    kcupKer M r p = k1Ker M p + k2Ker M r p - crKer M r p := by
  obtain ⟨x, y⟩ := p
  have hS : (0:ℝ) < 2 + r := by linarith
  have hA : Integrable fun z : ℝ =>
      AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) (x, z)
        * bAiryKer (2 + r) (z, y) :=
    integrable_mul_bAiryKer_of_abs_le hS (by linarith)
      (measurable_compKernel (measurable_heatKerTwo 1)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_qKerTwo M))) x y
      (fun z => compKernel_one_PrQ_abs_le hr M x z)
  have hB : Integrable fun z : ℝ =>
      AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1)) (x, z)
        * bAiryKer (2 + r) (z, y) :=
    integrable_mul_bAiryKer_of_abs_le hS (by linarith)
      (measurable_compKernel (measurable_qKerTwo M)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_heatKerTwo 1))) x y
      (fun z => compKernel_Q_Pr_P1_abs_le hr M x z)
  have hC : Integrable fun z : ℝ =>
      AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) (x, z)
        * bAiryKer (2 + r) (z, y) :=
    integrable_mul_bAiryKer_of_abs_le hS (by linarith)
      (measurable_compKernel (measurable_qKerTwo M)
        (measurable_compKernel (measurable_heatKerTwo r) (measurable_qKerTwo M))) x y
      (fun z => compKernel_Q_Pr_Q_abs_le hr M x z)
  show AiryConj.compKernel
      (fun q => AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r)
          (heatKerTwo 1)) q
        - AiryConj.compKernel (lamKerTwo M) (AiryConj.compKernel (heatKerTwo r)
          (lamKerTwo M)) q)
      (bAiryKer (2 + r)) (x, y) = _
  have hAB : Integrable fun z : ℝ =>
      (AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) (x, z)
        + AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1)) (x, z))
        * bAiryKer (2 + r) (z, y) :=
    (hA.add hB).congr (Eventually.of_forall fun z => by rw [Pi.add_apply]; ring)
  rw [show (fun q => AiryConj.compKernel (heatKerTwo 1) (AiryConj.compKernel (heatKerTwo r)
          (heatKerTwo 1)) q
        - AiryConj.compKernel (lamKerTwo M) (AiryConj.compKernel (heatKerTwo r)
          (lamKerTwo M)) q)
      = fun q => (AiryConj.compKernel (heatKerTwo 1)
          (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) q
        + AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (heatKerTwo 1)) q)
        - AiryConj.compKernel (qKerTwo M) (AiryConj.compKernel (heatKerTwo r) (qKerTwo M)) q from
      funext fun q => kcupDiffKer_eq hr M q.1 q.2]
  rw [compKernel_sub_left x y hAB hC, compKernel_add_left x y hA hB]
  rw [compKernel_QPrP1_bAiryKer_eq_k1Ker hr M, compKernel_P1PrQ_bAiryKer_eq_k2Ker hr M,
    compKernel_QPrQ_bAiryKer_eq_crKer hr M]
  ring

/-- The two-interval decomposition as a function identity (unconjugated). -/
theorem twoIntKCup_decomp_unconj (hr : 0 < r) (M : ℝ) :
    kcupKer M r = k1Ker M + k2Ker M r - crKer M r :=
  funext fun p => twoIntKCup_decomp_unconj_apply hr M p

/-! ## The `U_a`-conjugation and the conjugated kernels -/

/-- The `U_a`-conjugation on kernels: the kernel of `U_a K U_a⁻¹` where
`U_a f(x) = e^{−a x} f(x)` (the definition of `U_a, Φ`), i.e.
`(x, y) ↦ e^{−a x} K(x, y) e^{a y}`. This is the paper's conjugation convention
at the weight parameter `a = √(2M)`, kept here
as a free real parameter. -/
noncomputable def uConj (a : ℝ) (K : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Real.exp (-a * p.1) * K p * Real.exp (a * p.2)

/-- The pointwise conjugation-product identity: the middle factors `e^{a z} e^{−a z}`
cancel (`uConj_compKernel`'s content before integration). -/
theorem uConj_mul_uConj (a : ℝ) (K K' : ℝ × ℝ → ℝ) (x z y : ℝ) :
    (Real.exp (-a * x) * K (x, z) * Real.exp (a * z))
      * (Real.exp (-a * z) * K' (z, y) * Real.exp (a * y))
    = Real.exp (-a * x) * (K (x, z) * K' (z, y)) * Real.exp (a * y) := by
  have h1 : Real.exp (a * z) * Real.exp (-a * z) = 1 := by
    rw [← Real.exp_add, show a * z + -a * z = (0:ℝ) by ring, Real.exp_zero]
  calc (Real.exp (-a * x) * K (x, z) * Real.exp (a * z))
      * (Real.exp (-a * z) * K' (z, y) * Real.exp (a * y))
    = Real.exp (-a * x) * (K (x, z) * K' (z, y)) * Real.exp (a * y)
      * (Real.exp (a * z) * Real.exp (-a * z)) := by ring
    _ = Real.exp (-a * x) * (K (x, z) * K' (z, y)) * Real.exp (a * y) * 1 := by
        rw [h1]
    _ = Real.exp (-a * x) * (K (x, z) * K' (z, y)) * Real.exp (a * y) := mul_one _

/-- **Conjugation is a similarity on compositions**: `U(AB)U⁻¹ = (UAU⁻¹)(UBU⁻¹)` at kernel level. No
integrability is
needed: the middle factors `e^{a z} e^{−a z}` cancel pointwise. -/
theorem uConj_compKernel (a : ℝ) (K K' : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    uConj a (AiryConj.compKernel K K') p
      = AiryConj.compKernel (uConj a K) (uConj a K') p := by
  obtain ⟨x, y⟩ := p
  show Real.exp (-a * x) * (∫ z : ℝ, K (x, z) * K' (z, y)) * Real.exp (a * y)
    = ∫ z : ℝ, uConj a K (x, z) * uConj a K' (z, y)
  rw [← integral_const_mul, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with z
  exact (uConj_mul_uConj a K K' x z y).symm

/-- `uConj` distributes over addition of kernels (pointwise). -/
theorem uConj_add (a : ℝ) (K₁ K₂ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    uConj a (K₁ + K₂) p = uConj a K₁ p + uConj a K₂ p := by
  unfold uConj
  simp only [Pi.add_apply]
  ring

/-- `uConj` distributes over subtraction of kernels (pointwise). -/
theorem uConj_sub (a : ℝ) (K₁ K₂ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    uConj a (K₁ - K₂) p = uConj a K₁ p - uConj a K₂ p := by
  unfold uConj
  simp only [Pi.sub_apply]
  ring

/-- `uConj` at function level, over addition. -/
theorem uConj_add_fn (a : ℝ) (K₁ K₂ : ℝ × ℝ → ℝ) :
    uConj a (K₁ + K₂) = uConj a K₁ + uConj a K₂ :=
  funext fun p => uConj_add a K₁ K₂ p

/-- `uConj` at function level, over subtraction. -/
theorem uConj_sub_fn (a : ℝ) (K₁ K₂ : ℝ × ℝ → ℝ) :
    uConj a (K₁ - K₂) = uConj a K₁ - uConj a K₂ :=
  funext fun p => uConj_sub a K₁ K₂ p

/-- `uConj` preserves measurability. -/
theorem measurable_uConj (a : ℝ) {K : ℝ × ℝ → ℝ} (hK : Measurable K) :
    Measurable (uConj a K) :=
  (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).measurable.mul hK).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).measurable)

/-- The conjugated kernel of `K₁` (`K̃₁ = U_a K_1 U_a⁻¹`). -/
noncomputable def k1KerT (a M : ℝ) : ℝ × ℝ → ℝ := uConj a (k1Ker M)

/-- The conjugated kernel of `K₂` (`K̃₂ = U_a K_2 U_a⁻¹`). -/
noncomputable def k2KerT (a M r : ℝ) : ℝ × ℝ → ℝ := uConj a (k2Ker M r)

/-- The conjugated kernel of `C_r`. -/
noncomputable def crKerT (a M r : ℝ) : ℝ × ℝ → ℝ := uConj a (crKer M r)

/-- The conjugated kernel of `K_∪` (`K̃_∪ = U_a K_∪ U_a⁻¹`). -/
noncomputable def kcupKerT (a M r : ℝ) : ℝ × ℝ → ℝ := uConj a (kcupKer M r)

/-- `k1KerT` is measurable. -/
theorem measurable_k1KerT (a M : ℝ) : Measurable (k1KerT a M) :=
  measurable_uConj a (measurable_k1Ker M)

/-- `k2KerT` is measurable. -/
theorem measurable_k2KerT (a M r : ℝ) : Measurable (k2KerT a M r) :=
  measurable_uConj a (measurable_k2Ker M r)

/-- `crKerT` is measurable. -/
theorem measurable_crKerT (a M r : ℝ) : Measurable (crKerT a M r) :=
  measurable_uConj a (measurable_crKer M r)

/-- `kcupKerT` is measurable. -/
theorem measurable_kcupKerT (a M r : ℝ) : Measurable (kcupKerT a M r) :=
  measurable_uConj a (measurable_kcupKer M r)

/-- **The conjugated two-interval decomposition**: `K̃∪ = K̃₁ + K̃₂ − C̃_r`. Conjugation by `U_a` is
a similarity, so this
is immediate from the unconjugated identity. -/
theorem twoIntKCup_decomp (hr : 0 < r) (a M : ℝ) :
    kcupKerT a M r = k1KerT a M + k2KerT a M r - crKerT a M r := by
  show uConj a (kcupKer M r) = _
  rw [twoIntKCup_decomp_unconj hr M, uConj_sub_fn, uConj_add_fn]
  rfl

/-- The conjugated decomposition, pointwise form. -/
theorem twoIntKCup_decomp_apply (hr : 0 < r) (a M : ℝ) (p : ℝ × ℝ) :
    kcupKerT a M r p = k1KerT a M p + k2KerT a M r p - crKerT a M r p := by
  rw [twoIntKCup_decomp hr a M]
  simp only [Pi.sub_apply, Pi.add_apply]

/-- **Convention anchor**: the weighted kernels `V_{T,a}`, `W_{T,a}` compose to the `U_a`-conjugated
one-block operator: the kernel of `V_{T,a} W_{T,a}` is the kernel of
`U_a (Q_{M,T} P_{-T}B₀) U_a⁻¹`; the `φ` weights cancel pointwise (`φ > 0`). At `T = 1`
this says `V_{1,a} W_{1,a} = K̃₁`. -/
theorem compKernel_vKernel_wKernel (T a M : ℝ) (p : ℝ × ℝ) :
    AiryConj.compKernel (AiryConj.vKernel T a M) (AiryConj.wKernel T a) p
      = uConj a (AiryConj.compKernel (fun q => AiryConj.qMT M T q.1 q.2)
          (AiryConj.backwardAiryPair T)) p := by
  obtain ⟨x, y⟩ := p
  rw [uConj_compKernel]
  show (∫ z : ℝ, AiryConj.vKernel T a M (x, z) * AiryConj.wKernel T a (z, y))
    = ∫ z : ℝ, uConj a (fun q => AiryConj.qMT M T q.1 q.2) (x, z)
        * uConj a (AiryConj.backwardAiryPair T) (z, y)
  apply integral_congr_ae
  filter_upwards with z
  have hφ : AiryConj.phiWeight z * (AiryConj.phiWeight z)⁻¹ = 1 :=
    mul_inv_cancel₀ (AiryConj.phiWeight_pos z).ne'
  have he : Real.exp (-a * z) * Real.exp (a * z) = 1 := by
    rw [← Real.exp_add, show -a * z + a * z = (0:ℝ) by ring, Real.exp_zero]
  have h1 : AiryConj.vKernel T a M (x, z) * AiryConj.wKernel T a (z, y)
      = Real.exp (-a * x) * (AiryConj.qMT M T x z * backwardAiry T (z + y))
        * Real.exp (a * y) := by
    unfold AiryConj.vKernel AiryConj.wKernel
    calc Real.exp (-a * x) * AiryConj.qMT M T x z * Real.exp (-a * z) * AiryConj.phiWeight z
          * ((AiryConj.phiWeight z)⁻¹ * Real.exp (a * z) * backwardAiry T (z + y)
            * Real.exp (a * y))
        = Real.exp (-a * x) * (AiryConj.qMT M T x z * backwardAiry T (z + y))
          * Real.exp (a * y) * (AiryConj.phiWeight z * (AiryConj.phiWeight z)⁻¹)
          * (Real.exp (-a * z) * Real.exp (a * z)) := by ring
      _ = Real.exp (-a * x) * (AiryConj.qMT M T x z * backwardAiry T (z + y))
          * Real.exp (a * y) := by rw [hφ, he, mul_one, mul_one]
  have h2 : uConj a (fun q => AiryConj.qMT M T q.1 q.2) (x, z)
        * uConj a (AiryConj.backwardAiryPair T) (z, y)
      = Real.exp (-a * x) * (AiryConj.qMT M T x z * backwardAiry T (z + y))
        * Real.exp (a * y) := by
    unfold uConj AiryConj.backwardAiryPair
    calc (Real.exp (-a * x) * AiryConj.qMT M T x z * Real.exp (a * z))
          * (Real.exp (-a * z) * backwardAiry T (z + y) * Real.exp (a * y))
        = Real.exp (-a * x) * (AiryConj.qMT M T x z * backwardAiry T (z + y))
          * Real.exp (a * y) * (Real.exp (a * z) * Real.exp (-a * z)) := by ring
      _ = Real.exp (-a * x) * (AiryConj.qMT M T x z * backwardAiry T (z + y))
          * Real.exp (a * y) := by
            rw [← Real.exp_add, show a * z + -a * z = (0:ℝ) by ring, Real.exp_zero]
            ring
  rw [h1, h2]

/-! ## The operator-level identities and the trace cancellation

The lift to `HilbertSchmidt.kernelOperator` on `L²(ℝ)` is kept conditional on the
`MemLp` (square-integrability) data of the four conjugated kernels: that data is the
Hilbert–Schmidt factorization content of the paper's `V`- and `W`-bounds, supplied in
`TwoInterval/TwoIntervalMembership.lean` (the
bounds `vKernel_sq_integral_le` / `wKernel_sq_integral_le` are the analytic input).
The trace cancellation itself is then pure operator algebra from
`HilbertSchmidt.trace_add` / `HilbertSchmidt.trace_sub`. -/

/-- `kernelOperator` is insensitive to the `MemLp` proof term and to pointwise-equal
kernels. -/
theorem kernelOperator_congr {K K' : ℝ × ℝ → ℝ} (h : K = K')
    (hK : MemLp K 2 (volume.prod volume)) (hK' : MemLp K' 2 (volume.prod volume)) :
    kernelOperator hK = kernelOperator hK' := by
  subst h
  congr 1

/-- The kernel operator of a sum of kernels is the sum of the kernel operators. -/
theorem kernelOperator_add {K₁ K₂ : ℝ × ℝ → ℝ}
    (h₁ : MemLp K₁ 2 (volume.prod volume)) (h₂ : MemLp K₂ 2 (volume.prod volume)) :
    kernelOperator (h₁.add h₂) = kernelOperator h₁ + kernelOperator h₂ := by
  apply ContinuousLinearMap.ext
  intro f
  rw [add_apply]
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae (h₁.add h₂) f, kernelOperator_apply_ae h₁ f,
    kernelOperator_apply_ae h₂ f, Lp.coeFn_add (kernelOperator h₁ f) (kernelOperator h₂ f),
    integrable_kernelFun_slice_ae h₁ f, integrable_kernelFun_slice_ae h₂ f]
    with x hx hx1 hx2 hadd hxI1 hxI2
  rw [hx, hadd, Pi.add_apply, hx1, hx2]
  show (∫ z : ℝ, (K₁ + K₂) (x, z) * f z)
    = (∫ z : ℝ, K₁ (x, z) * f z) + (∫ z : ℝ, K₂ (x, z) * f z)
  rw [show (fun z : ℝ => (K₁ + K₂) (x, z) * f z)
      = fun z => K₁ (x, z) * f z + K₂ (x, z) * f z from funext fun z => by
    rw [Pi.add_apply]; ring]
  exact integral_add hxI1 hxI2

/-- The kernel operator of a difference of kernels is the difference of the kernel
operators. -/
theorem kernelOperator_sub {K₁ K₂ : ℝ × ℝ → ℝ}
    (h₁ : MemLp K₁ 2 (volume.prod volume)) (h₂ : MemLp K₂ 2 (volume.prod volume)) :
    kernelOperator (h₁.sub h₂) = kernelOperator h₁ - kernelOperator h₂ := by
  apply ContinuousLinearMap.ext
  intro f
  rw [sub_apply]
  apply Lp.ext
  filter_upwards [kernelOperator_apply_ae (h₁.sub h₂) f, kernelOperator_apply_ae h₁ f,
    kernelOperator_apply_ae h₂ f, Lp.coeFn_sub (kernelOperator h₁ f) (kernelOperator h₂ f),
    integrable_kernelFun_slice_ae h₁ f, integrable_kernelFun_slice_ae h₂ f]
    with x hx hx1 hx2 hsub hxI1 hxI2
  rw [hx, hsub, Pi.sub_apply, hx1, hx2]
  show (∫ z : ℝ, (K₁ - K₂) (x, z) * f z)
    = (∫ z : ℝ, K₁ (x, z) * f z) - (∫ z : ℝ, K₂ (x, z) * f z)
  rw [show (fun z : ℝ => (K₁ - K₂) (x, z) * f z)
      = fun z => K₁ (x, z) * f z - K₂ (x, z) * f z from funext fun z => by
    rw [Pi.sub_apply]; ring]
  exact integral_sub hxI1 hxI2

/-- The conjugated decomposition lifted to kernel operators on `L²(ℝ)` (given the `L²`
data of the four conjugated kernels — supplied in `TwoIntervalMembership.lean`). -/
theorem kernelOperator_kcupT_eq (hr : 0 < r) (a M : ℝ)
    (h₁ : MemLp (k1KerT a M) 2 (volume.prod volume))
    (h₂ : MemLp (k2KerT a M r) 2 (volume.prod volume))
    (hcup : MemLp (kcupKerT a M r) 2 (volume.prod volume))
    (hcr : MemLp (crKerT a M r) 2 (volume.prod volume)) :
    kernelOperator hcup = kernelOperator h₁ + kernelOperator h₂ - kernelOperator hcr := by
  rw [kernelOperator_congr (twoIntKCup_decomp hr a M) hcup ((h₁.add h₂).sub hcr),
    kernelOperator_sub (h₁.add h₂) hcr, kernelOperator_add h₁ h₂]

/-- **Trace cancellation**, abstract operator form: from
`Tcup + Tcr = T₁ + T₂` (the conjugated decomposition `K̃∪ = K̃₁ + K̃₂ − C̃_r`) and trace
linearity on trace-class operators,
`Tr T₁ + Tr T₂ − Tr Tcup = Tr Tcr`. -/
theorem trace_kcup_conj_decomp
    {T₁ T₂ Tcup Tcr : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 volume}
    (hdecomp : Tcup + Tcr = T₁ + T₂)
    (h₁ : IsTraceClass T₁) (h₂ : IsTraceClass T₂)
    (hcup : IsTraceClass Tcup) (hcr : IsTraceClass Tcr) :
    trace T₁ + trace T₂ - trace Tcup = trace Tcr := by
  have htr := trace_add hcup hcr
  rw [hdecomp, trace_add h₁ h₂] at htr
  linarith

/-- **The two-interval trace cancellation** (the algebra of Step 1 of
the paper's separated-block estimate): given `L²` membership of the four conjugated kernels and
trace-class
membership of their operators,
`Tr K̃₁ + Tr K̃₂ − Tr K̃∪ = Tr C̃_r`.

The `MemLp` and `IsTraceClass` hypotheses are discharged in
`TwoIntervalMembership.lean` from the paper's Hilbert–Schmidt bounds for `V` and `W`
(`K̃₁ = V_{1,a}W_{1,a}` by
`compKernel_vKernel_wKernel`, and the analogues built from the paper's HS factorizations). -/
theorem trace_twoIntKCup (hr : 0 < r) (a M : ℝ)
    (h₁ : MemLp (k1KerT a M) 2 (volume.prod volume))
    (h₂ : MemLp (k2KerT a M r) 2 (volume.prod volume))
    (hcup : MemLp (kcupKerT a M r) 2 (volume.prod volume))
    (hcr : MemLp (crKerT a M r) 2 (volume.prod volume))
    (hTC₁ : IsTraceClass (kernelOperator h₁)) (hTC₂ : IsTraceClass (kernelOperator h₂))
    (hTCcup : IsTraceClass (kernelOperator hcup)) (hTCcr : IsTraceClass (kernelOperator hcr)) :
    trace (kernelOperator h₁) + trace (kernelOperator h₂) - trace (kernelOperator hcup)
      = trace (kernelOperator hcr) := by
  apply trace_kcup_conj_decomp _ hTC₁ hTC₂ hTCcup hTCcr
  rw [kernelOperator_kcupT_eq hr a M h₁ h₂ hcup hcr, sub_add_cancel]

end AiryTwoInt



