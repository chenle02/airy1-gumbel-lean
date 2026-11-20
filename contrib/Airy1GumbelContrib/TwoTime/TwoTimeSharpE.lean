/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.TwoTime.TwoTimeSharpD
import Airy1GumbelContrib.TwoTime.TwoTimeQNorm

/-! # Sharp-Ψ two-time excess with no polynomial prefactor

Sharp exponent Ψ, no polynomial prefactor.  For `w ≥ 1/2`, `d > 0`, `Ψ = psiTP d w` and every
bounded `R` with `‖R‖ ≤ 2` (e.g. `R = (I − B)⁻¹`, see `TwoTimeSchur`),

* **K5♯** (`traceENorm_twoTimeExcess_le_e`): `‖(D − B) + K₂₁ R Q‖₁ ≤ 3√2 C♯ e^{−Ψ(d,w)}`.

This is the proof of `traceENorm_twoTimeExcess_le_d` (`TwoTimeSharpD`)
with the bound `‖Q‖ ≤ C_Q √(1 + d)` replaced by `‖Q‖ ≤ 1` (`norm_qOp_le_one`, `TwoTimeQNorm`).
That contraction bound comes from the `L¹ ∩ L²` contraction of the Airy transform
(`Airy/AiryTransformL2`), not from a full proof of the unitarity of the Airy transform on `L²`.  The
constant `3√2 C♯` is explicit but not claimed optimal.
-/

namespace AiryFdd

open MeasureTheory Real Set Filter
open HilbertSchmidt
open scoped ENNReal

/-- **K5♯**: for every bounded `R` with `‖R‖ ≤ 2` (e.g. `R = (I − B)⁻¹`),
`‖(D − B) + K₂₁ R Q‖₁ ≤ C e^{−Ψ(d,w)}` for `w ≥ 1/2`, `d > 0`, with the explicit uniform
`C = √2 C♯ (1 + 2 · 1)` (sharp exponent Ψ, no polynomial prefactor; uses `‖Q‖ ≤ 1` from the
`L¹ ∩ L²` Airy-transform contraction; `C` not claimed optimal). -/
theorem traceENorm_twoTimeExcess_le_e : ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 1 / 2 ≤ w → ∀ d : ℝ,
    ∀ hd : 0 < d, ∀ R : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ),
      ‖R‖ ≤ 2 →
      traceENorm ((dOp w w hd - goeOp w) + k21Op w w hd ∘L R ∘L qOp w w hd)
        ≤ ENNReal.ofReal (C * Real.exp (-psiTP d w)) := by
  refine ⟨Real.sqrt 2 * sharpConst * (1 + 2 * 1), by have := sharpConst_pos; positivity,
    fun w hw d hd R hR => ?_⟩
  set a := Real.sqrt 2 * sharpConst * Real.exp (-psiTP d w)
  have hsc := sharpConst_pos
  have ha : 0 ≤ a := by positivity
  have hRQr : ‖R ∘L qOp w w hd‖ ≤ 2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [norm_qOp_le_one w w hd, norm_nonneg R, norm_nonneg (qOp w w hd)])
  have hRQ : ‖R ∘L qOp w w hd‖ₑ ≤ ENNReal.ofReal 2 := by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hRQr
  rw [dOp_sub_goeOp]
  calc traceENorm (-k21TOp w hd + k21Op w w hd ∘L R ∘L qOp w w hd)
      ≤ traceENorm (-k21TOp w hd) + traceENorm (k21Op w w hd ∘L R ∘L qOp w w hd) :=
        traceENorm_add_le _ _
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal a * ENNReal.ofReal 2 := by
        rw [traceENorm_neg]
        gcongr
        · exact traceENorm_k21TOp_le_exp hw hd
        · exact (traceENorm_comp_right_le _ _).trans
            (mul_le_mul' (traceENorm_k21Op_le_exp hw hd) hRQ)
    _ = ENNReal.ofReal (a + a * 2) := by
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_add ha (by positivity)]
    _ = _ := by
        congr 1
        ring

end AiryFdd
