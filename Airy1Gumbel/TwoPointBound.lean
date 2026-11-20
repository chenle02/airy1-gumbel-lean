/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.ContinuousInstance
import Airy1GumbelContrib.TwoTime.TwoTimeSchur
import Airy1GumbelContrib.TwoTime.TwoTimeEst

open MeasureTheory Filter Set
open AiryFdd HilbertSchmidt

/-!
# The two-point bound TP for the Airy₁ law

The two-time Fredholm determinant modules of contrib (`TwoTime/`: the Schur factorisation and
the trace-norm estimates) give, at times `{0, d}` and equal levels `w`, the Schur
factorisation `F_{0,d}(w, w) = f(w) · det(I − Z)` and the trace-norm estimate
`‖Z − B‖₁ ≤ C e^{−Ψ(d,w) + 20(1+w+d²)}` (`B = goeOp w`, `Z = D + K₂₁(1 − B)⁻¹Q`). This file
glues them into a probability statement for the Airy₁ law `airy1Law h` and its continuous
version `Ã = (airy1SRP h hT).A`.

## Glue

1. `traceENorm ≤ ofReal r ⇒ traceNorm ≤ r` (`ENNReal.toReal_le_of_le_ofReal`; `traceNorm` is
   `(traceENorm ·).toReal` by definition).
2. `norm_goeOp_lt_one`, `norm_goeResolvent_le_two`: for `w ≥ goeLevel0`, `‖B‖ < 1` and
   `‖(1 − B)⁻¹‖ ≤ 2`.
3. `schurOp_sub` rewrites `Z − B` into the argument of K5.
4. `neg_psiTP_add_le`: the K5 exponent `−Ψ(d,w) + 20(1+w+d²)` is at most `3020` for
   `w, d ≥ 0`, so the factor `exp(2‖Z − B‖₁)` of the Schur excess bound is uniformly bounded. This
   uses the
   Ψ-form of K5. The rate conversion `rateI_add_le_psiTP` (`Ψ ≥ I(w) + 2wd`) is applied only
   at the end; the `_rate` form of K5 (whose exponent is unbounded in `d`) is not used.
5. `|f| ≤ 1` since `f = airy1Law h {f 0 ≤ w}` is a probability.

## Main results

* `airy1Law_twoPoint_sub_sq`: `P(A(0) > w, A(d) > w) − P(A(0) > w)² = F − f²` (inclusion–
  exclusion, `airy1Law_fdd` and stationarity `airy1Law_map_timeShift`).
* `twoPointExcess_airy1` (**TP-K**): for `w ≥ w₀ = goeLevel0`, `d > 0`,
  `|P(A(0) > w, A(d) > w) − P(A(0) > w)²| ≤ C e^{−I(w) − 2wd + 20(1 + w + d²)}`.
* `pairTP_airy1SRP`, `pairTP_airy1SRP_field`: the same on the continuous version `Ã` at any
  pair `x < y` (resp. `x + 1 ≤ y`), one-sided, in the shape of the `pairTP` field of the
  `MesoscopicBoundsTP` bundle (`MesoscopicTP.lean`).

Only `Airy1FddPositive` (and `GOELeftTail` for the carrier `Ã`) is assumed.
-/

namespace Airy1Gumbel

/-! ## Operator glue -/

/-- ENNReal → real bridge for the trace norm. -/
theorem traceNorm_le_of_traceENorm_le
    {A : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ)} {r : ℝ} (hr : 0 ≤ r)
    (h : traceENorm A ≤ ENNReal.ofReal r) : traceNorm A ≤ r :=
  ENNReal.toReal_le_of_le_ofReal hr h

theorem goeLevel0_nonneg : 0 ≤ goeLevel0 := by
  have : (288 : ℝ) ≤ goeLevel0 := by unfold goeLevel0; exact le_max_left _ _
  linarith

/-- `‖goeOp w‖ < 1` for `w ≥ goeLevel0`. -/
theorem norm_goeOp_lt_one {w : ℝ} (hw : goeLevel0 ≤ w) : ‖goeOp w‖ < 1 :=
  (norm_goeOp_le_half hw).trans_lt (by norm_num)

/-- `‖(1 − goeOp w)⁻¹‖ ≤ 2` for `w ≥ goeLevel0`. -/
theorem norm_goeResolvent_le_two {w : ℝ} (hw : goeLevel0 ≤ w) (hB : ‖goeOp w‖ < 1) :
    ‖goeResolvent w hB‖ ≤ 2 := by
  refine (norm_goeResolvent_le w hB).trans ?_
  have h := norm_goeOp_le_half hw
  calc (1 - ‖goeOp w‖)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    _ = 2 := by norm_num

/-- **The K5 exponent is bounded above**: `−Ψ(d,w) + 20(1 + w + d²) ≤ 3020` for `w, d ≥ 0`.
(`Ψ ≥ (2/3)(2w)^{3/2} + (2/3)d³`, and `−(2/3)a³ + 10a² ≤ 1000/3`,
`−(2/3)d³ + 20d² ≤ 8000/3`.) -/
theorem neg_psiTP_add_le {w d : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) :
    -psiTP d w + 20 * (1 + w + d ^ 2) ≤ 3020 := by
  unfold psiTP
  have h1 : (2 * w) ^ (3 / 2 : ℝ) ≤ (2 * w + d ^ 2) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [sq_nonneg d]) (by norm_num)
  rw [rpow_three_halves_eq (by positivity : (0 : ℝ) ≤ 2 * w)] at h1
  set a := Real.sqrt (2 * w)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * w := Real.sq_sqrt (by positivity)
  have hwd : 0 ≤ 2 * w * d := by positivity
  nlinarith [mul_nonneg (sq_nonneg (a - 10)) (by linarith : (0 : ℝ) ≤ a + 5),
    mul_nonneg (sq_nonneg (d - 20)) (by linarith : (0 : ℝ) ≤ d + 10)]

/-! ## The excess `F − f²` of the Fredholm-determinant CDFs -/

/-- **Schur excess bound + K5 assembled** (Ψ-form): for `w ≥ goeLevel0`, `d > 0` and `|f| ≤ 1`,
`|F_{0,d}(w, w) − f(w)²| ≤ C e^{−Ψ(d,w) + 20(1 + w + d²)}`, `C` uniform. -/
theorem exists_abs_airy1FinCdf_pair_const_sub_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, goeLevel0 ≤ w → ∀ d : ℝ, 0 < d →
      |airy1FinCdf {0} (fun _ => w)| ≤ 1 →
      |airy1FinCdf {0, d} (fun _ => w) - airy1FinCdf {0} (fun _ => w) ^ 2|
        ≤ C * Real.exp (-psiTP d w + 20 * (1 + w + d ^ 2)) := by
  obtain ⟨C₅, hC₅, hK⟩ := traceENorm_twoTimeExcess_le
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 2 * (C₅ * Real.exp 3020 + 2 * (tpConst * Real.exp 200)) :=
    ⟨_, rfl⟩
  refine ⟨2 * C₅ * Real.exp K, by positivity, fun w hw d hd hf => ?_⟩
  have hw0 : 0 ≤ w := goeLevel0_nonneg.trans hw
  have hB := norm_goeOp_lt_one hw
  have hR := norm_goeResolvent_le_two hw hB
  have hE0 := Real.exp_pos (-psiTP d w + 20 * (1 + w + d ^ 2))
  have hτ : traceNorm (schurOp w w hd (goeResolvent w hB) - goeOp w)
      ≤ C₅ * Real.exp (-psiTP d w + 20 * (1 + w + d ^ 2)) := by
    rw [schurOp_sub]
    exact traceNorm_le_of_traceENorm_le (mul_nonneg hC₅.le hE0.le) (hK w hw0 d hd _ hR)
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
      ≤ 2 * (C₅ * Real.exp (-psiTP d w + 20 * (1 + w + d ^ 2))) * Real.exp K := by
        gcongr
    _ = 2 * C₅ * Real.exp K * Real.exp (-psiTP d w + 20 * (1 + w + d ^ 2)) := by ring

/-! ## Inclusion–exclusion on `airy1Law` -/

section Law

variable (h : Airy1FddPositive)

theorem measurableSet_coord_le (t w : ℝ) : MeasurableSet {f : ℝ → ℝ | f t ≤ w} :=
  measurableSet_le (measurable_pi_apply t) measurable_const

/-- One-point marginal at any time (stationarity): `P(A(t) ≤ w) = airy1FinCdf {0} w`. -/
theorem airy1Law_coord_le (t w : ℝ) :
    (airy1Law h).real {f : ℝ → ℝ | f t ≤ w} = airy1FinCdf {0} (fun _ => w) := by
  have hpre : timeShift t ⁻¹' {g : ℝ → ℝ | g 0 ≤ w} = {f | f t ≤ w} := by
    ext f; simp [timeShift]
  rw [← hpre, ← map_measureReal_apply (measurable_timeShift t) (measurableSet_coord_le 0 w),
    airy1Law_map_timeShift h]
  refine Eq.trans ?_ (airy1Law_fdd h {0} (fun _ => w))
  congr 1
  ext f
  simp

/-- Two-point box probability: `P(A(0) ≤ w, A(d) ≤ w) = airy1FinCdf {0, d} (w, w)`. -/
theorem airy1Law_pair_le (d w : ℝ) :
    (airy1Law h).real {f : ℝ → ℝ | f 0 ≤ w ∧ f d ≤ w} = airy1FinCdf {0, d} (fun _ => w) := by
  refine Eq.trans ?_ (airy1Law_fdd h {0, d} (fun _ => w))
  congr 1
  ext f
  simp

theorem airy1Law_coord_gt (t w : ℝ) :
    (airy1Law h).real {f : ℝ → ℝ | f t > w} = 1 - airy1FinCdf {0} (fun _ => w) := by
  have : {f : ℝ → ℝ | f t > w} = {f | f t ≤ w}ᶜ := by ext f; simp
  rw [this, probReal_compl_eq_one_sub (measurableSet_coord_le t w), airy1Law_coord_le]

/-- Inclusion–exclusion: `P(A(0) > w, A(d) > w) = 1 − 2f + F`. -/
theorem airy1Law_pair_gt (d w : ℝ) :
    (airy1Law h).real {f : ℝ → ℝ | f 0 > w ∧ f d > w}
      = 1 - 2 * airy1FinCdf {0} (fun _ => w) + airy1FinCdf {0, d} (fun _ => w) := by
  have hS := measurableSet_coord_le 0 w
  have hT := measurableSet_coord_le d w
  have hset : {f : ℝ → ℝ | f 0 > w ∧ f d > w} = ({f | f 0 ≤ w} ∪ {f | f d ≤ w})ᶜ := by
    ext f; simp
  have hinter : {f : ℝ → ℝ | f 0 ≤ w} ∩ {f | f d ≤ w} = {f | f 0 ≤ w ∧ f d ≤ w} := rfl
  have hu := MeasureTheory.measureReal_union_add_inter (μ := airy1Law h) (s := {f : ℝ → ℝ | f 0 ≤ w}) hT
  rw [hset, probReal_compl_eq_one_sub (hS.union hT)]
  rw [hinter, airy1Law_pair_le, airy1Law_coord_le, airy1Law_coord_le] at hu
  linarith

/-- **The excess is `F − f²`**: `P(A(0) > w, A(d) > w) − P(A(0) > w)²
= airy1FinCdf {0, d} (w, w) − airy1FinCdf {0} w ²`. -/
theorem airy1Law_twoPoint_sub_sq (d w : ℝ) :
    (airy1Law h).real {f : ℝ → ℝ | f 0 > w ∧ f d > w}
        - ((airy1Law h).real {f : ℝ → ℝ | f 0 > w}) ^ 2
      = airy1FinCdf {0, d} (fun _ => w) - airy1FinCdf {0} (fun _ => w) ^ 2 := by
  rw [airy1Law_pair_gt, airy1Law_coord_gt]
  ring

end Law

/-- `|f| ≤ 1`: the one-point Fredholm CDF is a probability under `Airy1FddPositive`. -/
theorem abs_airy1FinCdf_singleton_le_one (h : Airy1FddPositive) (w : ℝ) :
    |airy1FinCdf {0} (fun _ => w)| ≤ 1 := by
  rw [← airy1Law_coord_le h 0 w, abs_of_nonneg MeasureTheory.measureReal_nonneg]
  exact measureReal_le_one

/-! ## TP on `airy1Law` -/

/-- **TP-K for the Airy₁ law**: there are `w₀ ≥ 0`, `C > 0`, `C' ≥ 0` with,
for all `w ≥ w₀` and `d > 0`,
`|P(A(0) > w, A(d) > w) − P(A(0) > w)²| ≤ C e^{−I(w) − 2wd + C'(1 + w + d²)}`,
`I(w) = (2/3)(2w)^{3/2}` (`rateI`). Witnesses: `w₀ = goeLevel0`, `C' = 20`. -/
theorem twoPointExcess_airy1 (h : Airy1FddPositive) :
    ∃ w₀ C C' : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ 0 ≤ C' ∧ ∀ w : ℝ, w₀ ≤ w → ∀ d : ℝ, 0 < d →
      |(airy1Law h).real {f : ℝ → ℝ | f 0 > w ∧ f d > w}
          - ((airy1Law h).real {f : ℝ → ℝ | f 0 > w}) ^ 2|
        ≤ C * Real.exp (-rateI w - 2 * w * d + C' * (1 + w + d ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := exists_abs_airy1FinCdf_pair_const_sub_sq_le
  refine ⟨goeLevel0, C, 20, goeLevel0_nonneg, hC, by norm_num, fun w hw d hd => ?_⟩
  rw [airy1Law_twoPoint_sub_sq]
  refine (hb w hw d hd (abs_airy1FinCdf_singleton_le_one h w)).trans ?_
  have := rateI_add_le_psiTP (goeLevel0_nonneg.trans hw) hd.le
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hC.le

/-! ## Transfer to the continuous version `Ã = airy1SRP h hT` -/

section Carrier

variable (h : Airy1FddPositive) (hT : GOELeftTail)

/-- Two-point exceedance of `Ã` at `x, y` equals the coordinate one at `0, y − x`
(modification `airy1ContR_ae_eq`, i.e.
`airy1SRP_ae_eq_airy1Process`, + stationarity). -/
theorem airy1SRP_pair_gt_eq (x y v : ℝ) :
    (airy1Law h).real {f | (airy1SRP h hT).A x f > v ∧ (airy1SRP h hT).A y f > v}
      = (airy1Law h).real {f : ℝ → ℝ | f 0 > v ∧ f (y - x) > v} := by
  have hae : {f | (airy1SRP h hT).A x f > v ∧ (airy1SRP h hT).A y f > v}
      =ᵐ[airy1Law h] {f : ℝ → ℝ | f x > v ∧ f y > v} := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [airy1ContR_ae_eq h hT x, airy1ContR_ae_eq h hT y] with f hx hy
    show airy1ContR h x f > v ∧ airy1ContR h y f > v ↔ f x > v ∧ f y > v
    rw [hx, hy]
  have hmeas : MeasurableSet {g : ℝ → ℝ | g 0 > v ∧ g (y - x) > v} :=
    (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
      (measurableSet_lt measurable_const (measurable_pi_apply _))
  have hpre : timeShift x ⁻¹' {g : ℝ → ℝ | g 0 > v ∧ g (y - x) > v}
      = {f | f x > v ∧ f y > v} := by
    ext f; simp [timeShift]
  rw [measureReal_congr hae, ← hpre, ← map_measureReal_apply (measurable_timeShift x) hmeas,
    airy1Law_map_timeShift h]

/-- One-point exceedance of `Ã` at time `0` equals the coordinate one. -/
theorem airy1SRP_gt_eq (v : ℝ) :
    (airy1Law h).real {f | (airy1SRP h hT).A 0 f > v}
      = (airy1Law h).real {f : ℝ → ℝ | f 0 > v} := by
  refine measureReal_congr ?_
  rw [Filter.eventuallyEqSet_iff]
  filter_upwards [airy1ContR_ae_eq h hT 0] with f hf
  show airy1ContR h 0 f > v ↔ f 0 > v
  rw [hf]

/-- **TP on the continuous carrier, every pair `x < y`**: with `W = Ã = (airy1SRP h hT).A`,
`P(W x > v, W y > v) ≤ P(W 0 > v)² + C e^{−I(v) − 2v(y−x) + C'(1 + v + (y−x)²)}` for
`v ≥ w₀`, `I(v) = (2/3)(2v)^{3/2}` written out (no contrib import needed downstream);
`w₀ ≥ 0`, `C > 0`, `C' ≥ 0`. -/
theorem pairTP_airy1SRP :
    ∃ w₀ C C' : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ 0 ≤ C' ∧ ∀ x y v : ℝ, w₀ ≤ v → x < y →
      (airy1Law h).real {ω | (airy1SRP h hT).A x ω > v ∧ (airy1SRP h hT).A y ω > v}
        ≤ (airy1Law h).real {ω | (airy1SRP h hT).A 0 ω > v} ^ 2
          + C * Real.exp (-((2 / 3) * (2 * v) ^ (3 / 2 : ℝ)) - 2 * v * (y - x)
              + C' * (1 + v + (y - x) ^ 2)) := by
  obtain ⟨w₀, C, C', hw₀, hC, hC', hb⟩ := twoPointExcess_airy1 h
  refine ⟨w₀, C, C', hw₀, hC, hC', fun x y v hv hxy => ?_⟩
  rw [airy1SRP_pair_gt_eq, airy1SRP_gt_eq]
  have h1 := (abs_sub_le_iff.1 (hb v hv (y - x) (by linarith))).1
  show _ ≤ _ + C * Real.exp (-rateI v - 2 * v * (y - x) + C' * (1 + v + (y - x) ^ 2))
  linarith

/-- **The `pairTP` field** (for the bundle `MesoscopicBoundsTP` with
`P = airy1Law h`, `W = (airy1SRP h hT).A = (airy1CMax h).A`):
`∃ w₀ C C', 0 ≤ w₀ ∧ 0 < C ∧ 0 ≤ C' ∧ ∀ x y v, w₀ ≤ v → x + 1 ≤ y →
P(W x > v ∧ W y > v) ≤ P(W 0 > v)² + C e^{−I(v) − 2v(y−x) + C'(1+v+(y−x)²)}`
(the signs are as `MesoscopicBoundsTP` uses them; this is `PairTPBound` of
`MesoscopicTP.lean`). -/
theorem pairTP_airy1SRP_field :
    ∃ w₀ C C' : ℝ, 0 ≤ w₀ ∧ 0 < C ∧ 0 ≤ C' ∧ ∀ x y v : ℝ, w₀ ≤ v → x + 1 ≤ y →
      (airy1Law h).real {ω | (airy1SRP h hT).A x ω > v ∧ (airy1SRP h hT).A y ω > v}
        ≤ (airy1Law h).real {ω | (airy1SRP h hT).A 0 ω > v} ^ 2
          + C * Real.exp (-((2 / 3) * (2 * v) ^ (3 / 2 : ℝ)) - 2 * v * (y - x)
              + C' * (1 + v + (y - x) ^ 2)) := by
  obtain ⟨w₀, C, C', hw₀, hC, hC', hb⟩ := pairTP_airy1SRP h hT
  exact ⟨w₀, C, C', hw₀, hC, hC', fun x y v hv hxy => hb x y v hv (by linarith)⟩

end Carrier

end Airy1Gumbel
