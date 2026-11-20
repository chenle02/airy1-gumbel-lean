/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoInterval.TwoIntervalShift
import Airy1GumbelContrib.TwoInterval.TwoIntervalTraceSign

/-!
# The Plemelj-exponent algebra for the sign of the two-interval joint probability

Part of the two-interval modules (`TwoInterval/`) of the Airy1–Gumbel contrib library.
The two-interval record (`QRTwoIntervalLaw`, main package) yields the joint exceedance probability

  `X := 1 − det₁(I−K̃₁) − det₁(I−K̃₂) + det₁(I−K̃∪)`,

whose sign is not certified by the first-order linearization of
`TwoIntervalDetRem.lean` (the independence term `π₁²` sits inside the remainder).  This
module proves the **exact algebra** of the Plemelj-exponent argument: everything except the three
analytic estimates N1–N3, which enter as named real hypotheses.

## Contents

* `plemeljTau K := ∑' m, tr(K^{m+1})/(m+1)`, so that `det₁(I−K) = exp(−τ_K)`
  (`fredholmDetOne_one_eq_exp_neg_plemeljTau`, from the definition of
  `fredholmDetOne`); `plemeljTail3 K := ∑' m, tr(K^{m+3})/(m+3)`.
* **δ identity** (`joint_detOne_comb_eq_plemelj`, no hypotheses): with
  `δ := τ_U − τ_A − τ_B` and `d_K := det₁(I−K)`,
  `1 − d_A − d_B + d_U = (1 − d_A)(1 − d_B) − d_A d_B (1 − e^{−δ})`.
  For `d_B = d_A = d`, `π := 1 − d`, this is
  `X = (1 − e^{−τ₁})² + e^{−2τ₁}(e^{−δ} − 1)`.
* **Second-order expansion** (`plemeljTau_eq_split`, `plemeljDelta_eq`): for trace-class
  `A, B, C, U` with `U = A + B − C` and HS norms `< 1`,

    `δ = −tr C + tr(AB) − tr(AC) − tr(BC) + ½ tr(C²) + (T₃(U) − T₃(A) − T₃(B))`.

  Derivation of the signs: `tr U = tr A + tr B − tr C` (m = 1), and
  `U² = A² + B² + C² + AB + BA − AC − CA − BC − CB`, so by cyclicity
  `tr U² − tr A² − tr B² = tr C² + 2tr(AB) − 2tr(AC) − 2tr(BC)` (m = 2, halved).
  The order of factors in each trace is immaterial (`tr(CK₁) = tr(K₁C)` by cyclicity).
* **Tail** (`abs_plemeljTail3_le`): `|T₃(K)| ≤ η³/(3(1−η))` when `‖K‖₂ ≤ η < 1`
  (sharper than the crude `3h³/(1−h)` total: the three tails sum to
  `η³/(1−η)`).
* **Upper bound on δ** (`plemeljDelta_le`) and the **assembly**
  (`joint_detOne_comb_ge_plemelj`, abstract; `twoInt_joint_ge_plemelj`, concrete;
  `twoInt_joint_ge_plemelj_eventually`, N1 and the HS bounds discharged):

    `X ≥ π₁² − d₁² · Δ`,   `Δ := e₁ + e₂ + 2ηe₃ + e₃²/2 + η³/(1−η)`.

* **Sign / association corollaries** (`joint_nonneg_of_plemelj`,
  `joint_ge_assoc_of_plemelj`): `X ≥ 0` once `d₁²Δ ≤ π₁²`; and if `0 ≤ d₁ ≤ 1`,
  `0 ≤ ε`, `Δ ≤ ε π₁²`, then `X ≥ (1 − ε) π₁²` (the shape of the association
  consistency `X ≥ π₁²(1 − o(1))`).  Also `one_sub_exp_neg_le_self`
  (`π₁ ≤ τ₁`, as `1 − e^{−τ} ≤ τ`) and `sq_le_exp_sub_one_sq` (`τ² ≤ (e^τ − 1)²`
  for `τ ≥ 0`).

## Interface for the N2/N3 estimates

All operators are on `L²(ℝ)`, at the two-interval weight `a` (`uConj a`), built as
`kernelOperator` of the `MemLp` proofs of `k1KerT a M`, `k2KerT a M r`,
`kcupKerT a M r`, `crKerT a M r` (any proof terms; `kernelOperator_congr`).  The
pointwise theorem `twoInt_joint_ge_plemelj` needs `0 < r`, `0 < M`, `r + 3 ≤ a` and the
real hypotheses

* N1: `-e₁ ≤ trace (kernelOperator hcr)`
  (discharged at `a = √(2M)` by `trace_crKerT_ge_neg_discharged_a`, `e₁ = C e^{−a⁴/64}`);
* N2: `trace (kernelOperator hk1 ∘L kernelOperator hk2) ≤ e₂`
  (one-sided; `|tr(K̃₁K̃₂)| ≤ e₂` implies it);
* N3: `hsNorm (kernelOperator hcr) ≤ e₃`;
* HS: `hsNorm` of `K̃₁`, `K̃₂`, `K̃∪` all `≤ η`, `η < 1`
  (discharged at `a = √(2M)` by `twoInt_stepThree`, `η = C₀M^{K₀}(1+r)^{K₀}e^{−(2/3)a³}`).

The eventual form `twoInt_joint_ge_plemelj_eventually` takes N2 and N3 as the only
hypotheses, for `M ≥ M₀(χ)`, `1 ≤ r ≤ χ√(2M)`, `a = √(2M)`.  An N2/N3 theorem
stated with these operator objects plugs in directly; a statement at a different
weight must first be transported (traces are weight independent, HS norms are not).

## Scope

Pure algebra plus the trace-class and two-interval API (`TraceClass/`, `TwoInterval/`: trace
linearity on trace class, cyclicity
`trace_comp_comm`, `norm_trace_comp_le`, `norm_trace_pow_le`,
`summable_trace_pow_div`, `kernelOperator_kcupT_eq`,
`fredholmDetOne_k2KerT_eq_k1KerT`).  No multiplicativity of `det₁` is used.  The
probability identity for `X` (the two-interval record) stays in the main package.
-/

namespace AiryTwoInt

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal InnerProduct InnerProductSpace
open HilbertSchmidt

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### The Plemelj exponent and its cubic tail -/

/-- The Plemelj exponent `τ_K = ∑_{m ≥ 1} tr(K^m)/m` (the `z = 1` exponent of
`fredholmDetOne`; junk value `0` off the summability region). -/
noncomputable def plemeljTau (K : E →L[ℝ] E) : ℝ :=
  ∑' m : ℕ, trace (K ^ (m + 1)) / ((m + 1 : ℕ) : ℝ)

/-- The cubic Plemelj tail `T₃(K) = ∑_{m ≥ 3} tr(K^m)/m`. -/
noncomputable def plemeljTail3 (K : E →L[ℝ] E) : ℝ :=
  ∑' m : ℕ, trace (K ^ (m + 3)) / ((m + 3 : ℕ) : ℝ)

/-- `det₁(I − K) = exp(−τ_K)` (the definition of `fredholmDetOne` at `z = 1`). -/
theorem fredholmDetOne_one_eq_exp_neg_plemeljTau (K : E →L[ℝ] E) (hK : IsTraceClass K) :
    fredholmDetOne K hK 1 = Real.exp (-plemeljTau K) := by
  rw [fredholmDetOne_one_eq_exp_neg_tsum, Real.exp_eq_exp_ℝ]
  rfl

/-- **The δ identity**: with `d_K = det₁(I−K) = e^{−τ_K}` and
`δ = τ_U − τ_A − τ_B`,
`1 − d_A − d_B + d_U = (1 − d_A)(1 − d_B) − d_A d_B (1 − e^{−δ})`.
No hypothesis: `d_U = d_A d_B e^{−δ}` holds by definition of `δ`. -/
theorem joint_detOne_comb_eq_plemelj {A B U : E →L[ℝ] E}
    (hA : IsTraceClass A) (hB : IsTraceClass B) (hU : IsTraceClass U) :
    1 - fredholmDetOne A hA 1 - fredholmDetOne B hB 1 + fredholmDetOne U hU 1
      = (1 - fredholmDetOne A hA 1) * (1 - fredholmDetOne B hB 1)
        - fredholmDetOne A hA 1 * fredholmDetOne B hB 1
          * (1 - Real.exp (-(plemeljTau U - plemeljTau A - plemeljTau B))) := by
  rw [fredholmDetOne_one_eq_exp_neg_plemeljTau A hA,
    fredholmDetOne_one_eq_exp_neg_plemeljTau B hB,
    fredholmDetOne_one_eq_exp_neg_plemeljTau U hU]
  have h : Real.exp (-plemeljTau U)
      = Real.exp (-plemeljTau A) * Real.exp (-plemeljTau B)
        * Real.exp (-(plemeljTau U - plemeljTau A - plemeljTau B)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h]
  ring

/-- **Plemelj split**: on `‖K‖₂ < 1`, `τ_K = tr K + tr(K²)/2 + T₃(K)`. -/
theorem plemeljTau_eq_split {K : E →L[ℝ] E} (hK : IsTraceClass K) (h1 : hsNorm K < 1) :
    plemeljTau K = trace K + trace (K ∘L K) / 2 + plemeljTail3 K := by
  have hs : Summable fun m : ℕ => trace (K ^ (m + 1)) / ((m + 1 : ℕ) : ℝ) :=
    summable_trace_pow_div hK h1
  have hs1 : Summable fun m : ℕ => trace (K ^ (m + 1 + 1)) / ((m + 1 + 1 : ℕ) : ℝ) :=
    (summable_nat_add_iff 1).mpr hs
  unfold plemeljTau plemeljTail3
  rw [hs.tsum_eq_zero_add, hs1.tsum_eq_zero_add]
  have e1 : trace (K ^ (0 + 1)) / ((0 + 1 : ℕ) : ℝ) = trace K := by simp
  have e2 : trace (K ^ (0 + 1 + 1)) / ((0 + 1 + 1 : ℕ) : ℝ) = trace (K ∘L K) / 2 := by
    rw [show (0 + 1 + 1 : ℕ) = 2 from rfl, pow_two]
    norm_num
    rfl
  rw [e1, e2, add_assoc]

/-- **The cubic tail bound**: `‖K‖₂ ≤ η < 1` gives `|T₃(K)| ≤ η³/(3(1−η))`. -/
theorem abs_plemeljTail3_le {K : E →L[ℝ] E} (hK : IsHilbertSchmidt K) {η : ℝ}
    (hKη : hsNorm K ≤ η) (hη : η < 1) :
    |plemeljTail3 K| ≤ η ^ 3 / (3 * (1 - η)) := by
  have hη0 : 0 ≤ η := (hsNorm_nonneg K).trans hKη
  have bound : ∀ m : ℕ, ‖trace (K ^ (m + 3)) / ((m + 3 : ℕ) : ℝ)‖ ≤ (η ^ 3 / 3) * η ^ m := by
    intro m
    rw [norm_div, RCLike.norm_natCast]
    have h1 : ‖trace (K ^ (m + 3))‖ ≤ η ^ (m + 3) :=
      (norm_trace_pow_le hK (by omega)).trans (pow_le_pow_left₀ (hsNorm_nonneg K) hKη _)
    have h3 : (3:ℝ) ≤ ((m + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ m + 3)
    calc ‖trace (K ^ (m + 3))‖ / ((m + 3 : ℕ) : ℝ)
        ≤ η ^ (m + 3) / ((m + 3 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ η ^ (m + 3) / 3 := div_le_div_of_nonneg_left (pow_nonneg hη0 _) (by norm_num) h3
      _ = (η ^ 3 / 3) * η ^ m := by ring
  have hgeo : Summable fun m : ℕ => (η ^ 3 / 3) * η ^ m :=
    (summable_geometric_of_lt_one hη0 hη).mul_left _
  have hsn : Summable fun m : ℕ => ‖trace (K ^ (m + 3)) / ((m + 3 : ℕ) : ℝ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) bound hgeo
  have h1η : 0 < 1 - η := by linarith
  rw [← Real.norm_eq_abs]
  calc ‖plemeljTail3 K‖
      ≤ ∑' m : ℕ, ‖trace (K ^ (m + 3)) / ((m + 3 : ℕ) : ℝ)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' m : ℕ, (η ^ 3 / 3) * η ^ m := hsn.tsum_le_tsum bound hgeo
    _ = (η ^ 3 / 3) * (1 - η)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hη0 hη]
    _ = η ^ 3 / (3 * (1 - η)) := by field_simp

/-! ### Trace linearity through the diagonal series -/

private theorem hasSum_diag_trace {T : E →L[ℝ] E} (hT : IsTraceClass T) :
    HasSum (fun i => ⟪canonicalBasis ℝ E i, T (canonicalBasis ℝ E i)⟫_ℝ) (trace T) :=
  (summable_inner_diagonal hT _).hasSum

private theorem hasSum_diag_add {S T : E →L[ℝ] E} {s t : ℝ}
    (hS : HasSum (fun i => ⟪canonicalBasis ℝ E i, S (canonicalBasis ℝ E i)⟫_ℝ) s)
    (hT : HasSum (fun i => ⟪canonicalBasis ℝ E i, T (canonicalBasis ℝ E i)⟫_ℝ) t) :
    HasSum (fun i => ⟪canonicalBasis ℝ E i, (S + T) (canonicalBasis ℝ E i)⟫_ℝ) (s + t) := by
  simpa only [add_apply, inner_add_right] using hS.add hT

private theorem hasSum_diag_sub {S T : E →L[ℝ] E} {s t : ℝ}
    (hS : HasSum (fun i => ⟪canonicalBasis ℝ E i, S (canonicalBasis ℝ E i)⟫_ℝ) s)
    (hT : HasSum (fun i => ⟪canonicalBasis ℝ E i, T (canonicalBasis ℝ E i)⟫_ℝ) t) :
    HasSum (fun i => ⟪canonicalBasis ℝ E i, (S - T) (canonicalBasis ℝ E i)⟫_ℝ) (s - t) := by
  simpa only [sub_apply, inner_sub_right] using hS.sub hT

private theorem trace_eq_of_hasSum {T : E →L[ℝ] E} (hT : IsTraceClass T) {t : ℝ}
    (h : HasSum (fun i => ⟪canonicalBasis ℝ E i, T (canonicalBasis ℝ E i)⟫_ℝ) t) :
    trace T = t :=
  (hasSum_diag_trace hT).unique h

/-- **First-order term**: `U = A + B − C` gives `tr U = tr A + tr B − tr C`. -/
theorem trace_of_decomp {A B C U : E →L[ℝ] E}
    (hA : IsTraceClass A) (hB : IsTraceClass B) (hC : IsTraceClass C) (hU : IsTraceClass U)
    (hdec : U = A + B - C) :
    trace U = trace A + trace B - trace C := by
  apply trace_eq_of_hasSum hU
  rw [hdec]
  exact hasSum_diag_sub (hasSum_diag_add (hasSum_diag_trace hA) (hasSum_diag_trace hB))
    (hasSum_diag_trace hC)

/-- **Second-order term**: for Hilbert–Schmidt `A, B, C` and `U = A + B − C`,
`tr(U²) − tr(A²) − tr(B²) = tr(C²) + 2tr(AB) − 2tr(AC) − 2tr(BC)`
(bilinear expansion + cyclicity `tr(BA) = tr(AB)`, `tr(CA) = tr(AC)`,
`tr(CB) = tr(BC)`). -/
theorem trace_sq_of_decomp {A B C U : E →L[ℝ] E}
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) (hC : IsHilbertSchmidt C)
    (hdec : U = A + B - C) :
    trace (U ∘L U) - trace (A ∘L A) - trace (B ∘L B)
      = trace (C ∘L C) + 2 * trace (A ∘L B) - 2 * trace (A ∘L C)
        - 2 * trace (B ∘L C) := by
  have hexp : U ∘L U = A ∘L A + A ∘L B - A ∘L C + B ∘L A + B ∘L B - B ∘L C
      - C ∘L A - C ∘L B + C ∘L C := by
    rw [hdec]
    show (A + B - C) * (A + B - C) = A * A + A * B - A * C + B * A + B * B - B * C
      - C * A - C * B + C * C
    noncomm_ring
  have hUU : IsTraceClass (U ∘L U) := by
    rw [hdec]
    have hS : IsHilbertSchmidt (A + B - C) := by
      have hAB : IsHilbertSchmidt (A + B) := by
        have := hA.sub hB.neg
        rwa [sub_neg_eq_add] at this
      exact hAB.sub hC
    exact hS.isTraceClass_comp hS
  have htr : trace (U ∘L U) = trace (A ∘L A) + trace (A ∘L B) - trace (A ∘L C)
      + trace (B ∘L A) + trace (B ∘L B) - trace (B ∘L C) - trace (C ∘L A)
      - trace (C ∘L B) + trace (C ∘L C) := by
    have s1 := hasSum_diag_add (hasSum_diag_trace (hA.isTraceClass_comp hA))
      (hasSum_diag_trace (hA.isTraceClass_comp hB))
    have s2 := hasSum_diag_sub s1 (hasSum_diag_trace (hA.isTraceClass_comp hC))
    have s3 := hasSum_diag_add s2 (hasSum_diag_trace (hB.isTraceClass_comp hA))
    have s4 := hasSum_diag_add s3 (hasSum_diag_trace (hB.isTraceClass_comp hB))
    have s5 := hasSum_diag_sub s4 (hasSum_diag_trace (hB.isTraceClass_comp hC))
    have s6 := hasSum_diag_sub s5 (hasSum_diag_trace (hC.isTraceClass_comp hA))
    have s7 := hasSum_diag_sub s6 (hasSum_diag_trace (hC.isTraceClass_comp hB))
    have s8 := hasSum_diag_add s7 (hasSum_diag_trace (hC.isTraceClass_comp hC))
    rw [← hexp] at s8
    exact trace_eq_of_hasSum hUU s8
  rw [htr, trace_comp_comm hB hA, trace_comp_comm hC hA, trace_comp_comm hC hB]
  ring

/-- **Second-order expansion of δ** (signs derived): for trace-class
`A, B, C, U` with `U = A + B − C` and `‖A‖₂, ‖B‖₂, ‖U‖₂ < 1`,
`τ_U − τ_A − τ_B = −tr C + tr(AB) − tr(AC) − tr(BC) + ½tr(C²)
  + (T₃(U) − T₃(A) − T₃(B))`. -/
theorem plemeljDelta_eq {A B C U : E →L[ℝ] E}
    (hA : IsTraceClass A) (hB : IsTraceClass B) (hC : IsTraceClass C) (hU : IsTraceClass U)
    (hdec : U = A + B - C) (hA1 : hsNorm A < 1) (hB1 : hsNorm B < 1) (hU1 : hsNorm U < 1) :
    plemeljTau U - plemeljTau A - plemeljTau B
      = -trace C + trace (A ∘L B) - trace (A ∘L C) - trace (B ∘L C) + trace (C ∘L C) / 2
        + (plemeljTail3 U - plemeljTail3 A - plemeljTail3 B) := by
  rw [plemeljTau_eq_split hU hU1, plemeljTau_eq_split hA hA1, plemeljTau_eq_split hB hB1]
  have h1 := trace_of_decomp hA hB hC hU hdec
  have h2 := trace_sq_of_decomp hA.isHilbertSchmidt hB.isHilbertSchmidt hC.isHilbertSchmidt hdec
  linear_combination h1 + h2 / 2

/-- **Upper bound on δ** from the named analytic inputs: N1 `−e₁ ≤ tr C`,
N2 `tr(AB) ≤ e₂`, N3 `‖C‖₂ ≤ e₃`, and `‖A‖₂, ‖B‖₂, ‖U‖₂ ≤ η < 1`:
`τ_U − τ_A − τ_B ≤ e₁ + e₂ + 2ηe₃ + e₃²/2 + η³/(1−η)`. -/
theorem plemeljDelta_le {A B C U : E →L[ℝ] E}
    (hA : IsTraceClass A) (hB : IsTraceClass B) (hC : IsTraceClass C) (hU : IsTraceClass U)
    (hdec : U = A + B - C) {η e₁ e₂ e₃ : ℝ} (hη : η < 1)
    (hAη : hsNorm A ≤ η) (hBη : hsNorm B ≤ η) (hUη : hsNorm U ≤ η)
    (hN1 : -e₁ ≤ trace C) (hN2 : trace (A ∘L B) ≤ e₂) (hN3 : hsNorm C ≤ e₃) :
    plemeljTau U - plemeljTau A - plemeljTau B
      ≤ e₁ + e₂ + 2 * η * e₃ + e₃ ^ 2 / 2 + η ^ 3 / (1 - η) := by
  have hη0 : 0 ≤ η := (hsNorm_nonneg A).trans hAη
  have he₃ : 0 ≤ e₃ := (hsNorm_nonneg C).trans hN3
  have hAhs := hA.isHilbertSchmidt
  have hBhs := hB.isHilbertSchmidt
  have hChs := hC.isHilbertSchmidt
  rw [plemeljDelta_eq hA hB hC hU hdec (hAη.trans_lt hη) (hBη.trans_lt hη)
    (hUη.trans_lt hη)]
  have hAC : -trace (A ∘L C) ≤ η * e₃ := by
    have h := norm_trace_comp_le hAhs hChs
    rw [Real.norm_eq_abs] at h
    have := mul_le_mul hAη hN3 (hsNorm_nonneg C) hη0
    linarith [neg_abs_le (trace (A ∘L C))]
  have hBC : -trace (B ∘L C) ≤ η * e₃ := by
    have h := norm_trace_comp_le hBhs hChs
    rw [Real.norm_eq_abs] at h
    have := mul_le_mul hBη hN3 (hsNorm_nonneg C) hη0
    linarith [neg_abs_le (trace (B ∘L C))]
  have hCC : trace (C ∘L C) ≤ e₃ ^ 2 := by
    have h := norm_trace_comp_le hChs hChs
    rw [Real.norm_eq_abs] at h
    have := mul_le_mul hN3 hN3 (hsNorm_nonneg C) he₃
    nlinarith [le_abs_self (trace (C ∘L C))]
  have tU := abs_plemeljTail3_le hU.isHilbertSchmidt hUη hη
  have tA := abs_plemeljTail3_le hAhs hAη hη
  have tB := abs_plemeljTail3_le hBhs hBη hη
  have htail : plemeljTail3 U - plemeljTail3 A - plemeljTail3 B ≤ η ^ 3 / (1 - η) := by
    have h1η : 0 < 1 - η := by linarith
    have hsplit : η ^ 3 / (1 - η) = 3 * (η ^ 3 / (3 * (1 - η))) := by field_simp
    rw [hsplit]
    linarith [le_abs_self (plemeljTail3 U), neg_abs_le (plemeljTail3 A),
      neg_abs_le (plemeljTail3 B)]
  linarith

/-- **The abstract assembly**: under N1–N3 and the HS bounds,
`1 − d_A − d_B + d_U ≥ (1 − d_A)(1 − d_B) − d_A d_B Δ`,
`Δ = e₁ + e₂ + 2ηe₃ + e₃²/2 + η³/(1−η)`.  Route: the δ identity, monotonicity of
`δ ↦ 1 − e^{−δ}`, and `1 − e^{−Δ} ≤ Δ`. -/
theorem joint_detOne_comb_ge_plemelj {A B C U : E →L[ℝ] E}
    (hA : IsTraceClass A) (hB : IsTraceClass B) (hC : IsTraceClass C) (hU : IsTraceClass U)
    (hdec : U = A + B - C) {η e₁ e₂ e₃ : ℝ} (hη : η < 1)
    (hAη : hsNorm A ≤ η) (hBη : hsNorm B ≤ η) (hUη : hsNorm U ≤ η)
    (hN1 : -e₁ ≤ trace C) (hN2 : trace (A ∘L B) ≤ e₂) (hN3 : hsNorm C ≤ e₃) :
    (1 - fredholmDetOne A hA 1) * (1 - fredholmDetOne B hB 1)
        - fredholmDetOne A hA 1 * fredholmDetOne B hB 1
          * (e₁ + e₂ + 2 * η * e₃ + e₃ ^ 2 / 2 + η ^ 3 / (1 - η))
      ≤ 1 - fredholmDetOne A hA 1 - fredholmDetOne B hB 1 + fredholmDetOne U hU 1 := by
  rw [joint_detOne_comb_eq_plemelj hA hB hU]
  set Δ := e₁ + e₂ + 2 * η * e₃ + e₃ ^ 2 / 2 + η ^ 3 / (1 - η) with hΔ
  have hδ := plemeljDelta_le hA hB hC hU hdec hη hAη hBη hUη hN1 hN2 hN3
  have hd : 0 ≤ fredholmDetOne A hA 1 * fredholmDetOne B hB 1 := by
    rw [fredholmDetOne_one_eq_exp_neg_plemeljTau A hA,
      fredholmDetOne_one_eq_exp_neg_plemeljTau B hB]
    positivity
  have hmono : 1 - Real.exp (-(plemeljTau U - plemeljTau A - plemeljTau B)) ≤ Δ := by
    have h1 : Real.exp (-Δ) ≤ Real.exp (-(plemeljTau U - plemeljTau A - plemeljTau B)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : -Δ + 1 ≤ Real.exp (-Δ) := Real.add_one_le_exp _
    linarith
  have := mul_le_mul_of_nonneg_left hmono hd
  linarith

/-! ### Sign and association corollaries (pure real algebra) -/

/-- `X ≥ 0` from the assembly once `d²Δ ≤ π²` (`π = 1 − d`). -/
theorem joint_nonneg_of_plemelj {d X Δ : ℝ} (hX : (1 - d) ^ 2 - d ^ 2 * Δ ≤ X)
    (hmargin : d ^ 2 * Δ ≤ (1 - d) ^ 2) : 0 ≤ X := by
  linarith

/-- **Association-consistency shape**: if `0 ≤ d ≤ 1`, `0 ≤ ε` and `Δ ≤ ε π²`
(`π = 1 − d`), then `X ≥ (1 − ε) π²` — i.e. `X ≥ π₁²(1 − o(1))` once `Δ = o(π₁²)`. -/
theorem joint_ge_assoc_of_plemelj {d X Δ ε : ℝ} (hX : (1 - d) ^ 2 - d ^ 2 * Δ ≤ X)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hε : 0 ≤ ε) (hΔ : Δ ≤ ε * (1 - d) ^ 2) :
    (1 - ε) * (1 - d) ^ 2 ≤ X := by
  have hd2 : d ^ 2 ≤ 1 := by nlinarith
  have hd20 : 0 ≤ d ^ 2 := sq_nonneg d
  have hπ : 0 ≤ ε * (1 - d) ^ 2 := mul_nonneg hε (sq_nonneg _)
  have key : d ^ 2 * Δ ≤ ε * (1 - d) ^ 2 := by
    rcases le_total 0 Δ with h0 | h0
    · calc d ^ 2 * Δ ≤ 1 * Δ := mul_le_mul_of_nonneg_right hd2 h0
        _ ≤ ε * (1 - d) ^ 2 := by linarith
    · have : d ^ 2 * Δ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd20 h0
      linarith
  linarith

/-- `π = 1 − e^{−τ} ≤ τ` (any real `τ`): i.e. `τ₁ ≥ π₁`. -/
theorem one_sub_exp_neg_le_self (τ : ℝ) : 1 - Real.exp (-τ) ≤ τ := by
  linarith [Real.add_one_le_exp (-τ)]

/-- `τ² ≤ (e^τ − 1)²` for `τ ≥ 0` (i.e. `(e^{τ₁} − 1)² ≥ τ₁²`). -/
theorem sq_le_exp_sub_one_sq {τ : ℝ} (hτ : 0 ≤ τ) : τ ^ 2 ≤ (Real.exp τ - 1) ^ 2 := by
  have h : τ ≤ Real.exp τ - 1 := by linarith [Real.add_one_le_exp τ]
  exact pow_le_pow_left₀ hτ h 2

/-- The sufficient condition for `X ≥ 0` in exponent form: if `δ ≤ (e^{τ} − 1)²` then
`(1 − e^{−τ})² + e^{−2τ}(e^{−δ} − 1) ≥ 0`. -/
theorem memo_form_nonneg {τ δ : ℝ} (h : δ ≤ (Real.exp τ - 1) ^ 2) :
    0 ≤ (1 - Real.exp (-τ)) ^ 2 + Real.exp (-τ) ^ 2 * (Real.exp (-δ) - 1) := by
  have hpos : 0 < Real.exp (-τ) := Real.exp_pos _
  have hinv : Real.exp (-τ) * Real.exp τ = 1 := by
    rw [← Real.exp_add]; simp
  have hrw : (1 - Real.exp (-τ)) ^ 2 = Real.exp (-τ) ^ 2 * (Real.exp τ - 1) ^ 2 := by
    have : 1 - Real.exp (-τ) = Real.exp (-τ) * (Real.exp τ - 1) := by
      rw [mul_sub, hinv, mul_one]
    rw [this, mul_pow]
  rw [hrw]
  have hδ : -δ + 1 ≤ Real.exp (-δ) := Real.add_one_le_exp _
  have : Real.exp (-τ) ^ 2 * ((Real.exp τ - 1) ^ 2 + (Real.exp (-δ) - 1)) ≥ 0 :=
    mul_nonneg (sq_nonneg _) (by linarith)
  linarith

end Abstract

/-! ### The two-interval instance -/

/-- **The concrete assembly (pointwise interface for N2/N3)**: at weight `a` with
`0 < r`, `0 < M`, `r + 3 ≤ a`, writing `d₁ = det₁(I − K̃₁)` (`= det₁(I − K̃₂)`,
`fredholmDetOne_k2KerT_eq_k1KerT`), `X = 1 − d₁ − d₂ + d∪`, and
`Δ = e₁ + e₂ + 2ηe₃ + e₃²/2 + η³/(1−η)`:

  N1 `−e₁ ≤ Tr C̃_r`, N2 `tr(K̃₁K̃₂) ≤ e₂`, N3 `‖C̃_r‖₂ ≤ e₃`,
  `‖K̃₁‖₂, ‖K̃₂‖₂, ‖K̃∪‖₂ ≤ η < 1`  ⟹  `(1 − d₁)² − d₁² Δ ≤ X`. -/
theorem twoInt_joint_ge_plemelj {M r : ℝ} (hr : 0 < r) (hM : 0 < M) {a : ℝ}
    (hadr : r + 3 ≤ a)
    (hk1 : MemLp (k1KerT a M) 2 (volume.prod volume))
    (hk2 : MemLp (k2KerT a M r) 2 (volume.prod volume))
    (hkcup : MemLp (kcupKerT a M r) 2 (volume.prod volume))
    (hcr : MemLp (crKerT a M r) 2 (volume.prod volume))
    (hk1t : IsTraceClass (kernelOperator hk1)) (hk2t : IsTraceClass (kernelOperator hk2))
    (hkcupt : IsTraceClass (kernelOperator hkcup))
    {η e₁ e₂ e₃ : ℝ} (hη : η < 1)
    (hη1 : hsNorm (kernelOperator hk1) ≤ η) (hη2 : hsNorm (kernelOperator hk2) ≤ η)
    (hηcup : hsNorm (kernelOperator hkcup) ≤ η)
    (hN1 : -e₁ ≤ trace (kernelOperator hcr))
    (hN2 : trace (kernelOperator hk1 ∘L kernelOperator hk2) ≤ e₂)
    (hN3 : hsNorm (kernelOperator hcr) ≤ e₃) :
    (1 - fredholmDetOne (kernelOperator hk1) hk1t 1) ^ 2
        - fredholmDetOne (kernelOperator hk1) hk1t 1 ^ 2
          * (e₁ + e₂ + 2 * η * e₃ + e₃ ^ 2 / 2 + η ^ 3 / (1 - η))
      ≤ 1 - fredholmDetOne (kernelOperator hk1) hk1t 1
          - fredholmDetOne (kernelOperator hk2) hk2t 1
          + fredholmDetOne (kernelOperator hkcup) hkcupt 1 := by
  have hcrt : IsTraceClass (kernelOperator hcr) := isTraceClass_crKerT hr hM hadr hcr
  have hdec := kernelOperator_kcupT_eq hr a M hk1 hk2 hkcup hcr
  have h := joint_detOne_comb_ge_plemelj hk1t hk2t hcrt hkcupt hdec hη hη1 hη2 hηcup
    hN1 hN2 hN3
  have hd2 := fredholmDetOne_k2KerT_eq_k1KerT hr hM hadr hk1 hk2 hk1t hk2t 1
  rw [hd2] at h ⊢
  linarith [h]

/-- **The eventual assembly at `a = √(2M)`** (N1 and the HS bounds discharged): for
`0 < χ < 1` there are `C₁, C₀ > 0`, `K₀ ≥ 0`, `M₀` such that for `M ≥ M₀`,
`1 ≤ r ≤ χ√(2M)`, any `MemLp`/trace-class proof terms, and any `e₂, e₃` with
N2 `tr(K̃₁K̃₂) ≤ e₂`, N3 `‖C̃_r‖₂ ≤ e₃`:

  `(1 − d₁)² − d₁² (C₁e^{−a⁴/64} + e₂ + 2ηe₃ + e₃²/2 + η³/(1−η)) ≤ X`,

with `a = √(2M)`, `η = C₀M^{K₀}(1+r)^{K₀}e^{−(2/3)a³} ≤ 1/2`. -/
theorem twoInt_joint_ge_plemelj_eventually {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1) :
    ∃ C₁ C₀ K₀ M₀ : ℝ, 0 < C₁ ∧ 0 < C₀ ∧ 0 ≤ K₀ ∧ ∀ {M r : ℝ}, M₀ ≤ M → 1 ≤ r →
      r ≤ χ * Real.sqrt (2*M) →
      ∀ (hk1 : MemLp (k1KerT (Real.sqrt (2*M)) M) 2 (volume.prod volume))
        (hk2 : MemLp (k2KerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume))
        (hkcup : MemLp (kcupKerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume))
        (hcr : MemLp (crKerT (Real.sqrt (2*M)) M r) 2 (volume.prod volume))
        (hk1t : IsTraceClass (kernelOperator hk1)) (hk2t : IsTraceClass (kernelOperator hk2))
        (hkcupt : IsTraceClass (kernelOperator hkcup)) {e₂ e₃ : ℝ},
        trace (kernelOperator hk1 ∘L kernelOperator hk2) ≤ e₂ →
        hsNorm (kernelOperator hcr) ≤ e₃ →
        (1 - fredholmDetOne (kernelOperator hk1) hk1t 1) ^ 2
            - fredholmDetOne (kernelOperator hk1) hk1t 1 ^ 2
              * (C₁ * Real.exp (-(Real.sqrt (2*M)) ^ 4 / 64) + e₂
                + 2 * (C₀ * M ^ K₀ * (1+r) ^ (K₀:ℝ) * Real.exp (-(2/3) * (Real.sqrt (2*M)) ^ 3))
                  * e₃
                + e₃ ^ 2 / 2
                + (C₀ * M ^ K₀ * (1+r) ^ (K₀:ℝ) * Real.exp (-(2/3) * (Real.sqrt (2*M)) ^ 3))
                    ^ 3
                  / (1 - C₀ * M ^ K₀ * (1+r) ^ (K₀:ℝ)
                    * Real.exp (-(2/3) * (Real.sqrt (2*M)) ^ 3)))
          ≤ 1 - fredholmDetOne (kernelOperator hk1) hk1t 1
              - fredholmDetOne (kernelOperator hk2) hk2t 1
              + fredholmDetOne (kernelOperator hkcup) hkcupt 1 := by
  obtain ⟨C₀, K₀, hC₀, hK₀, H₀⟩ := twoInt_stepThree χ hχ0 hχ1
  obtain ⟨M₁, hM₁⟩ := etaMr_tendsto_zero_uniform hC₀ K₀ hK₀ hχ0 hχ1 (1/2) (by norm_num)
  obtain ⟨C₁, M₂, hC₁, hN1⟩ := trace_crKerT_ge_neg_discharged_a hχ0 hχ1
  obtain ⟨Ma, hMa⟩ := exists_admissible_M₀ hχ0 hχ1
  refine ⟨C₁, C₀, K₀, max (max M₁ M₂) Ma, hC₁, hC₀, hK₀, ?_⟩
  intro M r hM hr hrM hk1 hk2 hkcup hcr hk1t hk2t hkcupt e₂ e₃ hN2 hN3
  have hM1' : M₁ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hM2' : M₂ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMa' : Ma ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hadr, _, hM1⟩ := hMa M r hMa' hr hrM
  have hMpos : (0:ℝ) < M := by linarith
  have hr0 : (0:ℝ) < r := by linarith
  obtain ⟨_, h1hs, _, h2hs, _, h3hs⟩ := H₀ hM1 hr hadr rfl hk1 hk2 hkcup
  have hη12 : C₀ * M ^ K₀ * (1+r) ^ (K₀:ℝ) * Real.exp (-(2/3) * (Real.sqrt (2*M)) ^ 3)
      ≤ 1/2 := by
    have h := hM₁ M r hM1' hr hrM
    rwa [← rpow_sqrt_two_mul_cube hMpos.le] at h
  exact twoInt_joint_ge_plemelj hr0 hMpos hadr hk1 hk2 hkcup hcr hk1t hk2t hkcupt
    (by linarith) h1hs h2hs h3hs (hN1 hM2' hr hrM hcr) hN2 hN3

end AiryTwoInt
