/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.TwoPointSharpD
import Airy1GumbelContrib.TwoTime.TwoTimeSharpE

open MeasureTheory Filter Set
open AiryFdd HilbertSchmidt

/-!
# The sharp-Ψ two-point bound with no polynomial prefactor

Sharp exponent Ψ, no polynomial prefactor, improving the `√(1 + d)` of `TwoPointSharpD` (which
stays untouched).  For `w ≥ w₀ = goeLevel0` and every `d > 0`,

  `|P(A(0) > w, A(d) > w) − P(A(0) > w)²| ≤ C e^{−Ψ(d,w)}`,
  `Ψ(d, w) = (2/3)(2w + d²)^{3/2} + 2wd + (2/3)d³` (`psiTP`).

The last `√(1 + d)` came from the bound `‖Q‖ ≤ C_Q √(1 + d)`; it is removed by `‖Q‖ ≤ 1`
(`norm_qOp_le_one`), which comes from the `L¹ ∩ L²` contraction of the Airy transform (`Airy/`
`AiryTransformL2`), not from a full proof of Airy-transform unitarity on `L²`.  `C` is still very
large (inherited from the exponential factor `exp(2(‖Z‖₁ + ‖B‖₁))` of the Schur-factorization
excess bound, controlled by the uniform estimate K5, `traceENorm_twoTimeExcess_le`).  The prefactor is not
claimed optimal.  The proof is that of
`exists_abs_airy1FinCdf_pair_const_sub_sq_le_sharp_d` with the trace-norm bound
`traceENorm_twoTimeExcess_le_d` replaced by `traceENorm_twoTimeExcess_le_e`.
-/

namespace Airy1Gumbel

/-- **Schur excess bound + sharp K5 estimate**: for `w ≥ goeLevel0`, `d > 0` and `|f| ≤ 1`,
`|F_{0,d}(w, w) − f(w)²| ≤ C e^{−Ψ(d,w)}`, `C` uniform (no polynomial prefactor). -/
theorem exists_abs_airy1FinCdf_pair_const_sub_sq_le_sharp_e :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, goeLevel0 ≤ w → ∀ d : ℝ, 0 < d →
      |airy1FinCdf {0} (fun _ => w)| ≤ 1 →
      |airy1FinCdf {0, d} (fun _ => w) - airy1FinCdf {0} (fun _ => w) ^ 2|
        ≤ C * Real.exp (-psiTP d w) := by
  obtain ⟨C₅, hC₅, hK⟩ := traceENorm_twoTimeExcess_le
  obtain ⟨Cs, hCs, hKs⟩ := traceENorm_twoTimeExcess_le_e
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 2 * (C₅ * Real.exp 3020 + 2 * (tpConst * Real.exp 200)) :=
    ⟨_, rfl⟩
  refine ⟨2 * Cs * Real.exp K, by positivity, fun w hw d hd hf => ?_⟩
  have hw0 : 0 ≤ w := goeLevel0_nonneg.trans hw
  have hwh : 1 / 2 ≤ w := by
    have : (288 : ℝ) ≤ goeLevel0 := by unfold goeLevel0; exact le_max_left _ _
    linarith
  have hB := norm_goeOp_lt_one hw
  have hR := norm_goeResolvent_le_two hw hB
  have hE0 := Real.exp_pos (-psiTP d w + 20 * (1 + w + d ^ 2))
  have hS0 : 0 ≤ Cs * Real.exp (-psiTP d w) := by positivity
  have hτ : traceNorm (schurOp w w hd (goeResolvent w hB) - goeOp w)
      ≤ C₅ * Real.exp (-psiTP d w + 20 * (1 + w + d ^ 2)) := by
    rw [schurOp_sub]
    exact traceNorm_le_of_traceENorm_le (mul_nonneg hC₅.le hE0.le) (hK w hw0 d hd _ hR)
  have hτs : traceNorm (schurOp w w hd (goeResolvent w hB) - goeOp w)
      ≤ Cs * Real.exp (-psiTP d w) := by
    rw [schurOp_sub]
    exact traceNorm_le_of_traceENorm_le hS0 (hKs w hwh d hd _ hR)
  have hβ : traceNorm (goeOp w) ≤ tpConst * Real.exp 200 :=
    traceNorm_le_of_traceENorm_le (mul_nonneg tpConst_pos.le (Real.exp_pos _).le)
      (traceENorm_goeOp_le_const hw0)
  have hE : Real.exp (-psiTP d w + 20 * (1 + w + d ^ 2)) ≤ Real.exp 3020 :=
    Real.exp_le_exp.2 (neg_psiTP_add_le hw0 hd.le)
  have hτ0 := traceNorm_nonneg (schurOp w w hd (goeResolvent w hB) - goeOp w)
  have hexp : Real.exp (2 * (traceNorm (schurOp w w hd (goeResolvent w hB) - goeOp w) +
      2 * traceNorm (goeOp w))) ≤ Real.exp K := by
    apply Real.exp_le_exp.2
    have : C₅ * Real.exp (-psiTP d w + 20 * (1 + w + d ^ 2)) ≤ C₅ * Real.exp 3020 :=
      mul_le_mul_of_nonneg_left hE hC₅.le
    rw [hKdef]
    linarith
  refine (abs_airy1FinCdf_pair_const_sub_sq_le_of_norm_lt_one hd w hB hf).trans ?_
  calc 2 * traceNorm (schurOp w w hd (goeResolvent w hB) - goeOp w) *
        Real.exp (2 * (traceNorm (schurOp w w hd (goeResolvent w hB) - goeOp w) +
          2 * traceNorm (goeOp w)))
      ≤ 2 * (Cs * Real.exp (-psiTP d w)) * Real.exp K := by
        gcongr
    _ = 2 * Cs * Real.exp K * Real.exp (-psiTP d w) := by ring

/-- **The sharp-Ψ two-point bound for the Airy₁ law, no polynomial prefactor** (sharp exponent
Ψ; `‖Q‖ ≤ 1` from the `L¹ ∩ L²` Airy-transform contraction, not a full unitarity proof; `C` is
very large, inherited from the exponential factor of the Schur-factorization excess bound; not
claimed optimal): there are `w₀ ≥ 0` and `C > 0` with, for all `w ≥ w₀` and `d > 0`,
`|P(A(0) > w, A(d) > w) − P(A(0) > w)²| ≤ C e^{−Ψ(d,w)}`,
`Ψ(d, w) = (2/3)(2w + d²)^{3/2} + 2wd + (2/3)d³`. Witness `w₀ = goeLevel0`. -/
theorem twoPointExcess_airy1_sharp_e (h : Airy1FddPositive) :
    ∃ w₀ C : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ ∀ w : ℝ, w₀ ≤ w → ∀ d : ℝ, 0 < d →
      |(airy1Law h).real {f : ℝ → ℝ | f 0 > w ∧ f d > w}
          - ((airy1Law h).real {f : ℝ → ℝ | f 0 > w}) ^ 2|
        ≤ C * Real.exp (-((2 / 3) * (2 * w + d ^ 2) ^ (3 / 2 : ℝ) + 2 * w * d
            + (2 / 3) * d ^ 3)) := by
  obtain ⟨C, hC, hb⟩ := exists_abs_airy1FinCdf_pair_const_sub_sq_le_sharp_e
  refine ⟨goeLevel0, C, goeLevel0_nonneg, hC, fun w hw d hd => ?_⟩
  rw [airy1Law_twoPoint_sub_sq]
  exact hb w hw d hd (abs_airy1FinCdf_singleton_le_one h w)

section Carrier

variable (h : Airy1FddPositive) (hT : GOELeftTail)

/-- **Sharp-Ψ TP on the continuous carrier, no polynomial prefactor, every pair `x < y`** (sharp
exponent Ψ; `C` very large, not claimed optimal): with `W = Ã = (airy1SRP h hT).A`, `v ≥ w₀`,
`d = y − x`, `P(W x > v, W y > v) ≤ P(W 0 > v)² + C e^{−Ψ(d, v)}` (`Ψ` written out). -/
theorem pairTP_airy1SRP_sharp_e :
    ∃ w₀ C : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ ∀ x y v : ℝ, w₀ ≤ v → x < y →
      (airy1Law h).real {ω | (airy1SRP h hT).A x ω > v ∧ (airy1SRP h hT).A y ω > v}
        ≤ (airy1Law h).real {ω | (airy1SRP h hT).A 0 ω > v} ^ 2
          + C * Real.exp (-((2 / 3) * (2 * v + (y - x) ^ 2) ^ (3 / 2 : ℝ) + 2 * v * (y - x)
              + (2 / 3) * (y - x) ^ 3)) := by
  obtain ⟨w₀, C, hw₀, hC, hb⟩ := twoPointExcess_airy1_sharp_e h
  refine ⟨w₀, C, hw₀, hC, fun x y v hv hxy => ?_⟩
  rw [airy1SRP_pair_gt_eq, airy1SRP_gt_eq]
  have h1 := (abs_sub_le_iff.1 (hb v hv (y - x) (by linarith))).1
  linarith

end Carrier

end Airy1Gumbel
