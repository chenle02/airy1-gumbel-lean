/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.AiryKernel.ConjugateV
import Airy1GumbelContrib.AiryKernel.Conjugate2to2
import Airy1GumbelContrib.TraceClass.TraceClass
import Airy1GumbelContrib.HilbertSchmidt.KernelHS
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Hilbert–Schmidt bound for `U_a Q_{M,T} P_L U_a Φ`

This is a lemma of the paper (the `U Φ` Hilbert–Schmidt bound), proved through the
factorization `U_a Q P_L U_a Φ = (U_a Q U_a Φ) · ℬ_{L,a}` and an `L¹` bound for the
dominating kernel of `ℬ_{L,a}`.

For each `T > 0` there are `C_T, K > 0` such that for all `M, L > 0` with
`a = √(2M) ≥ T + 1`,

  `‖U_a Q_{M,T} P_L U_a Φ‖₂ ≤ C_T (1 + M + L)^K · exp(L a² + T a² − a³)`.

## Proof route (as in the paper)

Factor `U_a Q P_L U_a Φ = (U_a Q U_a Φ) · ℬ_{L,a}` with
`ℬ_{L,a} := Φ⁻¹ U_a⁻¹ P_L U_a Φ`, whose kernel is
`ℬ(z, w) = (φ(w)/φ(z)) · e^{a(z−w)} · p_L(z−w)` (contrib `bPhiKernel`).
Since `φ` is `1`-Lipschitz and `φ ≥ 1`, `φ(w)/φ(z) ≤ 1 + |z − w|`
(`phiWeight_ratio_le`), so `|ℬ(z, w)| ≤ k(z − w)` with
`k(v) := (1 + |v|) · e^{av} · p_L(v)` (contrib `kUPhi`).  Young's convolution
inequality gives `‖ℬ‖_{2→2} ≤ ‖k‖₁` (the generic Young lemma
`eLpNorm_conv_le`, following the pattern of
`eLpNorm_conjugateHeat_conv_le`), and completing the square gives
`‖k‖₁ ≤ 2 (1 + |a| L + √L) e^{L a²}` (`integral_kUPhi_le`).  Multiplying by
the `vKernel` bound (`vKernel_sq_integral_le`,
`‖U_a Q U_a Φ‖₂² ≤ C_T (1+M)² (1+a³) e^{2Ta² − 4Ma}`) and absorbing
polynomial factors gives the headline `uphi_hs_le`, with `K = 4` and
`C_T' = 16 √C_T`.

## Packaging note

The composite operator is presented exactly as in the paper's
factorization: `kernelOperator (memLp_vKernel …)` (the HS operator of
the `vKernel`, i.e. `U_a Q U_a Φ`) composed on the right by `bPhiCLM hL a`
(the `L²`-bounded operator `ℬ_{L,a}` built from the Young bound via
`LinearMap.mkContinuous`).  The mixed composition inequality
`hsENorm_comp_op_le` (`‖S ∘L T‖_HS ≤ ‖S‖_HS · ‖T‖_op`, from
`HilbertSchmidt.sumSq_comp_le_right`) then gives the HS-norm bound.  No
density/approximation step is needed: `bPhiApply` is defined pointwise and
its `L²` bound is proved directly from Young.

## Differences from the paper's statement

* The `L¹` bound `integral_kUPhi_le` is stated for all `a : ℝ` with `|a|` in
  place of `a` (the paper only uses `a = √(2M) > 0`); the constant `2`
  is explicit.  Everything else matches the paper.
* The exponent `K = 4` and the constant `16√C_T` are explicit witnesses for
  the existential constants.
-/

namespace AiryConj

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal

/-! ## The weight ratio bound -/

/-- `1 ≤ φ(x)`: the weight `φ(x) = √(1 + x²)` is bounded below by `1`
(`φ ≥ 1`). -/
theorem one_le_phiWeight (x : ℝ) : 1 ≤ phiWeight x := by
  have h : Real.sqrt (1 : ℝ) ≤ phiWeight x := by
    unfold phiWeight
    apply Real.sqrt_le_sqrt
    have h2 := sq_nonneg x
    linarith
  rwa [Real.sqrt_one] at h

/-- `|x| ≤ φ(x)`: the weight dominates the absolute value. -/
theorem abs_le_phiWeight (x : ℝ) : |x| ≤ phiWeight x := by
  rw [← Real.sqrt_sq_eq_abs]
  unfold phiWeight
  apply Real.sqrt_le_sqrt
  have h := sq_nonneg x
  linarith

/-- `φ` is `1`-Lipschitz.  Proof: multiply
by the conjugate, `(φw − φz)(φw + φz) = w² − z²`, and use
`|w + z| ≤ |w| + |z| ≤ φw + φz`. -/
theorem phiWeight_lipschitz (w z : ℝ) : |phiWeight w - phiWeight z| ≤ |w - z| := by
  have hA : (0 : ℝ) < phiWeight w + phiWeight z := add_pos (phiWeight_pos w) (phiWeight_pos z)
  have hkey : (phiWeight w - phiWeight z) * (phiWeight w + phiWeight z) = w ^ 2 - z ^ 2 := by
    calc (phiWeight w - phiWeight z) * (phiWeight w + phiWeight z)
        = (phiWeight w) ^ 2 - (phiWeight z) ^ 2 := by ring
      _ = w ^ 2 - z ^ 2 := by rw [phiWeight_sq, phiWeight_sq]; ring
  have habs : |phiWeight w - phiWeight z|
      = |w + z| * |w - z| / (phiWeight w + phiWeight z) := by
    have h1 : phiWeight w - phiWeight z = (w ^ 2 - z ^ 2) / (phiWeight w + phiWeight z) := by
      rw [eq_div_iff hA.ne']
      exact hkey
    rw [h1, abs_div, abs_of_pos hA]
    congr 2
    rw [sq_sub_sq, abs_mul]
  rw [habs, div_le_iff₀ hA]
  calc |w + z| * |w - z| ≤ (phiWeight w + phiWeight z) * |w - z| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        calc |w + z| ≤ |w| + |z| := abs_add_le w z
          _ ≤ phiWeight w + phiWeight z := add_le_add (abs_le_phiWeight w) (abs_le_phiWeight z)
    _ = |w - z| * (phiWeight w + phiWeight z) := by ring

/-- **The ratio bound**:
`φ(w) / φ(z) ≤ 1 + |z − w|` for all `z w`. -/
theorem phiWeight_ratio_le (z w : ℝ) : phiWeight w / phiWeight z ≤ 1 + |z - w| := by
  have hB : (0 : ℝ) < phiWeight z := phiWeight_pos z
  rw [div_le_iff₀ hB]
  have h1 : 0 ≤ phiWeight z - 1 := by linarith [one_le_phiWeight z]
  have h2 : 0 ≤ |z - w| * (phiWeight z - 1) := mul_nonneg (abs_nonneg _) h1
  have hLip := phiWeight_lipschitz w z
  rw [abs_sub_comm w z] at hLip
  calc phiWeight w ≤ |phiWeight w - phiWeight z| + phiWeight z := by
        linarith [le_abs_self (phiWeight w - phiWeight z)]
    _ ≤ |z - w| + phiWeight z := by linarith
    _ = (1 + |z - w|) * phiWeight z - |z - w| * (phiWeight z - 1) := by ring
    _ ≤ (1 + |z - w|) * phiWeight z := by linarith

/-! ## The `ℬ_{L,a}` kernel and the dominating kernel `k` -/

/-- The kernel of `ℬ_{L,a} := Φ⁻¹ U_a⁻¹ P_L U_a Φ` (the second factor of the factorization):
`ℬ(z, w) = (φ(w)/φ(z)) · e^{a(z−w)} · p_L(z−w)`, with `zw = (z, w)`. -/
noncomputable def bPhiKernel (L a : ℝ) (zw : ℝ × ℝ) : ℝ :=
  (phiWeight zw.2 / phiWeight zw.1) * Real.exp (a * (zw.1 - zw.2)) * heatKernel L (zw.1 - zw.2)

/-- `ℬ` is continuous (each factor is; `φ > 0`). -/
theorem continuous_bPhiKernel (L a : ℝ) : Continuous (bPhiKernel L a) := by
  unfold bPhiKernel
  exact (((continuous_phiWeight.comp continuous_snd).mul
      ((continuous_phiWeight.comp continuous_fst).inv₀ fun p => (phiWeight_pos p.1).ne')).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_fst.sub continuous_snd)))).mul
    ((continuous_heatKernel L).comp (continuous_fst.sub continuous_snd))

/-- `ℬ` is jointly measurable. -/
theorem measurable_bPhiKernel (L a : ℝ) : Measurable (bPhiKernel L a) :=
  (continuous_bPhiKernel L a).measurable

/-- The dominating convolution kernel `k(v) := (1 + |v|) · e^{av} · p_L(v)`. -/
noncomputable def kUPhi (L a v : ℝ) : ℝ :=
  (1 + |v|) * Real.exp (a * v) * heatKernel L v

/-- `k` is nonnegative for `0 < L`. -/
theorem kUPhi_nonneg (hL : 0 < L) (a v : ℝ) : 0 ≤ kUPhi L a v :=
  mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (heatKernel_nonneg hL v)

/-- `k` is continuous. -/
theorem continuous_kUPhi (L a : ℝ) : Continuous (kUPhi L a) := by
  unfold kUPhi
  exact ((continuous_const.add continuous_abs).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul (continuous_heatKernel L)

/-- **Pointwise domination**: `|ℬ(z, w)| ≤ k(z − w)`. -/
theorem bPhiKernel_abs_le (hL : 0 < L) (a z w : ℝ) :
    |bPhiKernel L a (z, w)| ≤ kUPhi L a (z - w) := by
  have hnn : 0 ≤ Real.exp (a * (z - w)) * heatKernel L (z - w) :=
    mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg hL _)
  have h1 : bPhiKernel L a (z, w)
      = (phiWeight w / phiWeight z) * (Real.exp (a * (z - w)) * heatKernel L (z - w)) := by
    unfold bPhiKernel
    ring
  have h2 : kUPhi L a (z - w)
      = (1 + |z - w|) * (Real.exp (a * (z - w)) * heatKernel L (z - w)) := by
    unfold kUPhi
    ring
  rw [h1, h2, abs_mul, abs_of_nonneg hnn,
    abs_of_nonneg (div_nonneg (phiWeight_nonneg w) (phiWeight_pos z).le)]
  exact mul_le_mul_of_nonneg_right (phiWeight_ratio_le z w) hnn

/-! ## The sign-flipped conjugated heat kernel (`e^{+av} p_L(v)`) -/

/-- The sign-flipped conjugated kernel `e^{av} · p_L(v)` — the `e^{+av}`
variant of `conjugateHeatKernel` (completing the square,
`av − v²/4L = La² − (v − 2La)²/4L`). -/
noncomputable def expHeatKernel (L a v : ℝ) : ℝ := Real.exp (a * v) * heatKernel L v

/-- The sign-flipped kernel is `conjugateHeatKernel` at `−a`. -/
theorem expHeatKernel_eq_conjugateHeatKernel (L a : ℝ) :
    expHeatKernel L a = conjugateHeatKernel L (-a) := by
  unfold expHeatKernel conjugateHeatKernel
  rw [neg_neg]

/-- The completed-square factorization (the sign-flipped
`conjugateHeatKernel_eq`): `e^{av} p_L(v) = (4πL)^{-1/2} e^{La²}
e^{-(v-2La)²/4L}`. -/
theorem expHeatKernel_eq (hL : 0 < L) (a v : ℝ) :
    expHeatKernel L a v = (4 * Real.pi * L) ^ (-1/2 : ℝ) * Real.exp (L * a ^ 2)
      * Real.exp (-(v - 2 * L * a) ^ 2 / (4 * L)) := by
  rw [expHeatKernel_eq_conjugateHeatKernel, conjugateHeatKernel_eq hL (-a) v, neg_sq,
    show (v + 2 * L * -a) = (v - 2 * L * a) from by ring]

/-- The sign-flipped kernel is integrable for `0 < L`. -/
theorem integrable_expHeatKernel (hL : 0 < L) (a : ℝ) :
    Integrable (expHeatKernel L a) volume := by
  rw [expHeatKernel_eq_conjugateHeatKernel]
  exact integrable_conjugateHeatKernel hL _

/-- The sign-flipped kernel is continuous. -/
theorem continuous_expHeatKernel (L a : ℝ) : Continuous (expHeatKernel L a) := by
  rw [expHeatKernel_eq_conjugateHeatKernel]
  exact continuous_conjugateHeatKernel L _

/-- The exact exponential moment (the sign-flipped
`integral_conjugateHeatKernel`): `∫ v, e^{av} p_L(v) dv = e^{L a²}`. -/
theorem integral_expHeatKernel (hL : 0 < L) (a : ℝ) :
    ∫ v : ℝ, expHeatKernel L a v = Real.exp (L * a ^ 2) := by
  rw [expHeatKernel_eq_conjugateHeatKernel, integral_conjugateHeatKernel hL (-a), neg_sq]

/-! ## The first absolute moment of the Gaussian factor -/

/-- The half-line first moment of the Gaussian: `∫ r in (0, ∞), r e^{−r²/2T} = T`,
by the improper fundamental theorem of calculus with antiderivative
`F(r) = −T·e^{−r²/(2T)}`. -/
theorem integral_Ioi_mul_gaussT (hT : 0 < T) :
    ∫ r : ℝ in Set.Ioi 0, r * gaussT T r = T := by
  have hb : (0 : ℝ) < (2 * T)⁻¹ := by positivity
  have hderiv : ∀ r ∈ Set.Ici (0 : ℝ), HasDerivAt (fun x => -T * Real.exp (-(2 * T)⁻¹ * x ^ 2))
      (r * Real.exp (-(2 * T)⁻¹ * r ^ 2)) r := by
    intro r _
    have h1 : HasDerivAt (fun x : ℝ => -(2 * T)⁻¹ * x ^ 2) (-(2 * T)⁻¹ * (2 * r)) r := by
      have h := (hasDerivAt_pow 2 r).const_mul (-(2 * T)⁻¹)
      convert h using 1
      ring
    have h3 := (h1.exp).const_mul (-T)
    convert h3 using 1
    have h2T : (2 : ℝ) * T ≠ 0 := by positivity
    field_simp
  have hint : IntegrableOn (fun r : ℝ => r * Real.exp (-(2 * T)⁻¹ * r ^ 2)) (Set.Ioi 0) :=
    (integrable_mul_exp_neg_mul_sq hb).integrableOn
  have hlim : Tendsto (fun r : ℝ => -T * Real.exp (-(2 * T)⁻¹ * r ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => -(2 * T)⁻¹ * r ^ 2) atTop atBot :=
      (tendsto_pow_atTop (two_ne_zero)).const_mul_atTop_of_neg (neg_lt_zero.mpr hb)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (-T)
    rwa [mul_zero] at h2
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [show (0 : ℝ) - (-T * Real.exp (-(2 * T)⁻¹ * (0 : ℝ) ^ 2)) = T from by simp] at hmain
  calc ∫ r : ℝ in Set.Ioi 0, r * gaussT T r
      = ∫ r : ℝ in Set.Ioi 0, r * Real.exp (-(2 * T)⁻¹ * r ^ 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r _
        show r * gaussT T r = r * Real.exp (-(2 * T)⁻¹ * r ^ 2)
        rw [gaussT_eq_exp_neg_mul_sq hT]
    _ = T := hmain

/-- The first absolute moment of `gaussT T`: `∫ w, |w| e^{−w²/(2T)} = 2T`
(even extension of the half-line first moment via `integral_comp_abs`). -/
theorem integral_abs_gaussT (hT : 0 < T) : ∫ w : ℝ, |w| * gaussT T w = 2 * T := by
  have hhalf := integral_Ioi_mul_gaussT hT
  set F : ℝ → ℝ := fun x => x * Real.exp (-(2 * T)⁻¹ * x ^ 2) with hF
  have hform : (fun w : ℝ => |w| * gaussT T w) = fun w => F |w| := by
    funext w
    show |w| * gaussT T w = F |w|
    rw [hF]
    show |w| * gaussT T w = |w| * Real.exp (-(2 * T)⁻¹ * |w| ^ 2)
    rw [gaussT_eq_exp_neg_mul_sq hT, sq_abs]
  have hhalf' : ∫ x : ℝ in Set.Ioi 0, F x = T := by
    rw [← hhalf]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    show F r = r * gaussT T r
    rw [hF]
    show r * Real.exp (-(2 * T)⁻¹ * r ^ 2) = r * gaussT T r
    rw [gaussT_eq_exp_neg_mul_sq hT]
  rw [hform, integral_comp_abs, hhalf']

/-- The first absolute Gaussian moment in `gaussMoment` form:
`gaussMoment T 1 = 2T`. -/
theorem gaussMoment_one {T : ℝ} (hT : 0 < T) : gaussMoment T 1 = 2 * T := by
  have h : (fun w : ℝ => |w| ^ 1 * gaussT T w) = fun w => |w| * gaussT T w :=
    funext fun w => by rw [pow_one]
  unfold gaussMoment
  rw [h]
  exact integral_abs_gaussT hT

/-! ## Integrability and the `L¹` bound for `k` -/

/-- `kUPhi` is integrable for `0 < L` (completed-square form: a constant times
a polynomial-weighted translated Gaussian). -/
theorem integrable_kUPhi (hL : 0 < L) (a : ℝ) : Integrable (kUPhi L a) volume := by
  have h2L : (0 : ℝ) < 2 * L := by positivity
  have hc0 : (0 : ℝ) ≤ 1 + 2 * L * |a| := by positivity
  have hbase : Integrable (fun v : ℝ => (1 + |v|) * Real.exp (-(v - 2 * L * a) ^ 2 / (4 * L)))
      volume := by
    have hF : Integrable (fun w : ℝ => (1 + |w + 2 * L * a|) * gaussT (2 * L) w) volume := by
      apply MeasureTheory.Integrable.mono'
        (((integrable_gaussT h2L).const_mul (1 + 2 * L * |a|)).add
          (by simpa using integrable_abs_pow_gaussT h2L 1))
        ((continuous_const.add (continuous_abs.comp
          (continuous_id.add continuous_const))).mul (continuous_gaussT _)).aestronglyMeasurable
      filter_upwards with w
      have hg : 0 ≤ gaussT (2 * L) w := gaussT_nonneg _ _
      have h1 : 1 + |w + 2 * L * a| ≤ (1 + 2 * L * |a|) + |w| := by
        have htri : |w + 2 * L * a| ≤ |w| + |2 * L * a| := abs_add_le _ _
        have hca : |2 * L * a| = 2 * L * |a| := by
          rw [abs_mul, abs_of_pos h2L]
        linarith
      show |(1 + |w + 2 * L * a|) * gaussT (2 * L) w|
          ≤ (1 + 2 * L * |a|) * gaussT (2 * L) w + |w| * gaussT (2 * L) w
      rw [abs_of_nonneg (mul_nonneg (by positivity) hg)]
      calc (1 + |w + 2 * L * a|) * gaussT (2 * L) w
          ≤ ((1 + 2 * L * |a|) + |w|) * gaussT (2 * L) w := mul_le_mul_of_nonneg_right h1 hg
        _ = (1 + 2 * L * |a|) * gaussT (2 * L) w + |w| * gaussT (2 * L) w := by ring
    -- pull back by the translation `w = v − 2La`
    have hshift : (fun v : ℝ => (1 + |v|) * Real.exp (-(v - 2 * L * a) ^ 2 / (4 * L)))
        = fun v => (fun w : ℝ => (1 + |w + 2 * L * a|) * gaussT (2 * L) w) (v - 2 * L * a) := by
      funext v
      show (1 + |v|) * Real.exp (-(v - 2 * L * a) ^ 2 / (4 * L))
          = (1 + |v - 2 * L * a + 2 * L * a|) * gaussT (2 * L) (v - 2 * L * a)
      rw [sub_add_cancel, gaussT_eq_exp_neg_mul_sq h2L]
      congr 2
      field_simp
      ring
    rw [hshift]
    exact hF.comp_sub_right (2 * L * a)
  have hform : kUPhi L a = fun v : ℝ =>
      ((4 * Real.pi * L) ^ (-1/2 : ℝ) * Real.exp (L * a ^ 2)) *
        ((1 + |v|) * Real.exp (-(v - 2 * L * a) ^ 2 / (4 * L))) := by
    funext v
    unfold kUPhi
    rw [show (1 + |v|) * Real.exp (a * v) * heatKernel L v = (1 + |v|) * expHeatKernel L a v from by
      unfold expHeatKernel
      ring]
    rw [expHeatKernel_eq hL a v]
    ring
  rw [hform]
  exact hbase.const_mul _

/-- **The `L¹` bound** for the
dominating kernel: `∫ (1 + |v|) e^{av} p_L(v) dv ≤ 2 (1 + |a| L + √L) e^{L a²}`.

Route: complete the square (`e^{av} p_L(v) = e^{La²}` times the
`N(2La, 2L)`-density), translate (`w = v − 2La`), use `|w + 2La| ≤ |w| + 2L|a|`
with the exact moments `∫ gaussT (2L) = √(4πL)` (`gaussMoment_zero`) and
`∫ |w| gaussT (2L) = 4L` (`gaussMoment_one`); the paper's
`e^{La²}(1 + E|G|)` with `E|G| ≤ |EG| + sd(G)` corresponds to our
`1 + 2L|a| + 2√(L/π) ≤ 2(1 + |a|L + √L)`. -/
theorem integral_kUPhi_le (hL : 0 < L) (a : ℝ) :
    ∫ v : ℝ, kUPhi L a v ≤ 2 * (1 + |a| * L + Real.sqrt L) * Real.exp (L * a ^ 2) := by
  have h2L : (0 : ℝ) < 2 * L := by positivity
  have h4πL : (0 : ℝ) < 4 * Real.pi * L := by positivity
  set C0 : ℝ := (4 * Real.pi * L) ^ (-1/2 : ℝ) * Real.exp (L * a ^ 2) with hC0
  set c : ℝ := 2 * L * a with hc
  -- step 1: the completed-square form of the integral
  have hform : ∫ v : ℝ, kUPhi L a v = C0 * ∫ v : ℝ, (1 + |v|) * Real.exp (-(v - c) ^ 2 / (4 * L)) := by
    have hfun : (fun v : ℝ => kUPhi L a v) = fun v =>
        C0 * ((1 + |v|) * Real.exp (-(v - c) ^ 2 / (4 * L))) := by
      funext v
      unfold kUPhi
      rw [show (1 + |v|) * Real.exp (a * v) * heatKernel L v = (1 + |v|) * expHeatKernel L a v from by
        unfold expHeatKernel
        ring]
      rw [expHeatKernel_eq hL a v]
      rw [hC0, hc]
      ring
    rw [hfun]
    exact integral_const_mul _ _
  -- step 2: translate to centre the Gaussian (`w = v − c`)
  have htrans : ∫ v : ℝ, (1 + |v|) * Real.exp (-(v - c) ^ 2 / (4 * L))
      = ∫ w : ℝ, (1 + |w + c|) * Real.exp (-w ^ 2 / (4 * L)) := by
    have hF : (fun v : ℝ => (1 + |v|) * Real.exp (-(v - c) ^ 2 / (4 * L)))
        = fun v => (fun w : ℝ => (1 + |w + c|) * Real.exp (-w ^ 2 / (4 * L))) (v - c) := by
      funext v
      show (1 + |v|) * Real.exp (-(v - c) ^ 2 / (4 * L))
          = (1 + |v - c + c|) * Real.exp (-(v - c) ^ 2 / (4 * L))
      rw [sub_add_cancel]
    rw [hF]
    exact MeasureTheory.integral_sub_right_eq_self (μ := volume)
      (fun w : ℝ => (1 + |w + c|) * Real.exp (-w ^ 2 / (4 * L))) c
  -- step 3: bound the translated integral by the two exact moments
  have hbound : ∫ w : ℝ, (1 + |w + c|) * Real.exp (-w ^ 2 / (4 * L))
      ≤ (1 + 2 * L * |a|) * Real.sqrt (Real.pi * (2 * (2 * L))) + 2 * (2 * L) := by
    have hsplit : (fun w : ℝ => (1 + |w + c|) * Real.exp (-w ^ 2 / (4 * L)))
        = (fun w : ℝ => (1 + |w + c|) * gaussT (2 * L) w) := by
      funext w
      rw [gaussT_eq_exp_neg_mul_sq h2L]
      congr 2
      field_simp
      ring
    rw [hsplit]
    have hpt : ∀ w : ℝ, (1 + |w + c|) * gaussT (2 * L) w
        ≤ (1 + |c|) * gaussT (2 * L) w + |w| * gaussT (2 * L) w := by
      intro w
      have hg : 0 ≤ gaussT (2 * L) w := gaussT_nonneg _ _
      have h1 : 1 + |w + c| ≤ (1 + |c|) + |w| := by
        have htri : |w + c| ≤ |w| + |c| := abs_add_le _ _
        linarith
      calc (1 + |w + c|) * gaussT (2 * L) w
          ≤ ((1 + |c|) + |w|) * gaussT (2 * L) w := mul_le_mul_of_nonneg_right h1 hg
        _ = (1 + |c|) * gaussT (2 * L) w + |w| * gaussT (2 * L) w := by ring
    have hca : |c| = 2 * L * |a| := by
      rw [hc, abs_mul, abs_of_pos h2L]
    have hint1 : Integrable (fun w : ℝ => (1 + |w + c|) * gaussT (2 * L) w) volume := by
      apply MeasureTheory.Integrable.mono'
        (((integrable_gaussT h2L).const_mul (1 + |c|)).add
          (by simpa using integrable_abs_pow_gaussT h2L 1))
        ((continuous_const.add (continuous_abs.comp
          (continuous_id.add continuous_const))).mul (continuous_gaussT _)).aestronglyMeasurable
      filter_upwards with w
      show |(1 + |w + c|) * gaussT (2 * L) w|
          ≤ (1 + |c|) * gaussT (2 * L) w + |w| * gaussT (2 * L) w
      rw [abs_of_nonneg (mul_nonneg (by positivity) (gaussT_nonneg _ _))]
      exact hpt w
    have hint2 : Integrable (fun w : ℝ => (1 + |c|) * gaussT (2 * L) w + |w| * gaussT (2 * L) w)
        volume :=
      (((integrable_gaussT h2L).const_mul (1 + |c|)).add
        (by simpa using integrable_abs_pow_gaussT h2L 1))
    have hg0 : ∫ w : ℝ, gaussT (2 * L) w = gaussMoment (2 * L) 0 := by
      unfold gaussMoment
      simp
    have hg1 : ∫ w : ℝ, |w| * gaussT (2 * L) w = gaussMoment (2 * L) 1 := by
      unfold gaussMoment
      simp
    calc ∫ w : ℝ, (1 + |w + c|) * gaussT (2 * L) w
        ≤ ∫ w : ℝ, (1 + |c|) * gaussT (2 * L) w + |w| * gaussT (2 * L) w :=
          integral_mono hint1 hint2 (Pi.le_def.mpr (fun w => hpt w))
      _ = (1 + |c|) * (∫ w : ℝ, gaussT (2 * L) w) + ∫ w : ℝ, |w| * gaussT (2 * L) w := by
          rw [integral_add ((integrable_gaussT h2L).const_mul _)
            (by simpa using integrable_abs_pow_gaussT h2L 1), integral_const_mul]
      _ = (1 + |c|) * gaussMoment (2 * L) 0 + gaussMoment (2 * L) 1 := by
          rw [hg0, hg1]
      _ = (1 + 2 * L * |a|) * Real.sqrt (Real.pi * (2 * (2 * L))) + 2 * (2 * L) := by
          rw [gaussMoment_zero h2L, gaussMoment_one h2L, hca]
  -- step 4: assemble
  have hC0nn : (0 : ℝ) ≤ C0 := by
    rw [hC0]
    positivity
  have hbr1 : (4 * Real.pi * L) ^ (-1/2 : ℝ) * Real.sqrt (Real.pi * (2 * (2 * L))) = 1 := by
    rw [show Real.pi * (2 * (2 * L)) = 4 * Real.pi * L from by ring, Real.sqrt_eq_rpow,
      ← Real.rpow_add h4πL, show (-1/2 : ℝ) + 1/2 = 0 by norm_num, Real.rpow_zero]
  have hbr2 : (4 * Real.pi * L) ^ (-1/2 : ℝ) * (2 * (2 * L)) ≤ 2 * Real.sqrt L := by
    -- `4L / √(4πL) = 2√(L/π) ≤ 2√L` since `π ≥ 1`
    have h4π : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
      rw [show (4 : ℝ) * Real.pi = (2 * Real.sqrt Real.pi) ^ 2 from by
        rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
        ring]
      exact Real.sqrt_sq (by positivity)
    have hπ1 : (1 : ℝ) ≤ Real.sqrt Real.pi := by
      rw [show (1 : ℝ) = Real.sqrt (1 : ℝ) from Real.sqrt_one.symm]
      apply Real.sqrt_le_sqrt
      linarith [Real.pi_gt_three]
    have hsqrt4πL : Real.sqrt (4 * Real.pi * L) = 2 * Real.sqrt Real.pi * Real.sqrt L := by
      rw [Real.sqrt_mul (by positivity), h4π]
    have hconv : (4 * Real.pi * L) ^ (-1/2 : ℝ) = (Real.sqrt (4 * Real.pi * L))⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
      congr 1
      norm_num
    rw [hconv, hsqrt4πL]
    rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt Real.pi * Real.sqrt L)]
    calc (2 : ℝ) * (2 * L) = 4 * L := by ring
      _ ≤ 4 * (Real.sqrt Real.pi * L) := by
          have h := mul_le_mul_of_nonneg_left hπ1 (show (0 : ℝ) ≤ 4 * L by positivity)
          rw [mul_one] at h
          convert h using 1
          ring
      _ = (2 * Real.sqrt Real.pi * Real.sqrt L) * (2 * Real.sqrt L) := by
          rw [show (2 * Real.sqrt Real.pi * Real.sqrt L) * (2 * Real.sqrt L)
              = 4 * Real.sqrt Real.pi * (Real.sqrt L * Real.sqrt L) from by ring,
            Real.mul_self_sqrt hL.le]
          ring
  calc ∫ v : ℝ, kUPhi L a v
      = C0 * ∫ v : ℝ, (1 + |v|) * Real.exp (-(v - c) ^ 2 / (4 * L)) := hform
    _ = C0 * ∫ w : ℝ, (1 + |w + c|) * Real.exp (-w ^ 2 / (4 * L)) := by rw [htrans]
    _ ≤ C0 * ((1 + 2 * L * |a|) * Real.sqrt (Real.pi * (2 * (2 * L))) + 2 * (2 * L)) :=
        mul_le_mul_of_nonneg_left hbound hC0nn
    _ = (4 * Real.pi * L) ^ (-1/2 : ℝ) * Real.exp (L * a ^ 2) *
          ((1 + 2 * L * |a|) * Real.sqrt (Real.pi * (2 * (2 * L))) + 2 * (2 * L)) := by rw [hC0]
    _ = Real.exp (L * a ^ 2) * (1 + 2 * L * |a|) +
          Real.exp (L * a ^ 2) * ((4 * Real.pi * L) ^ (-1/2 : ℝ) * (2 * (2 * L))) := by
        rw [show (4 * Real.pi * L) ^ (-1/2 : ℝ) * Real.exp (L * a ^ 2) *
            ((1 + 2 * L * |a|) * Real.sqrt (Real.pi * (2 * (2 * L))) + 2 * (2 * L))
          = Real.exp (L * a ^ 2) * (1 + 2 * L * |a|) *
              ((4 * Real.pi * L) ^ (-1/2 : ℝ) * Real.sqrt (Real.pi * (2 * (2 * L))))
            + Real.exp (L * a ^ 2) * ((4 * Real.pi * L) ^ (-1/2 : ℝ) * (2 * (2 * L))) from by ring]
        rw [hbr1, mul_one]
    _ ≤ Real.exp (L * a ^ 2) * (1 + 2 * L * |a|) + Real.exp (L * a ^ 2) * (2 * Real.sqrt L) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hbr2 (Real.exp_pos _).le) _
    _ = Real.exp (L * a ^ 2) * (1 + 2 * L * |a| + 2 * Real.sqrt L) := by ring
    _ ≤ 2 * (1 + |a| * L + Real.sqrt L) * Real.exp (L * a ^ 2) := by
        have hE : (0 : ℝ) < Real.exp (L * a ^ 2) := Real.exp_pos _
        rw [show 2 * (1 + |a| * L + Real.sqrt L) * Real.exp (L * a ^ 2)
            = Real.exp (L * a ^ 2) * (2 + 2 * (|a| * L) + 2 * Real.sqrt L) from by ring]
        apply mul_le_mul_of_nonneg_left _ hE.le
        linarith [abs_nonneg a, Real.sqrt_nonneg L]

/-- The `L¹` seminorm bound in enorm form (for the Young step):
`‖k‖ₑ(1) ≤ ofReal (2 (1 + |a|L + √L) e^{La²})`. -/
theorem eLpNorm_one_kUPhi_le (hL : 0 < L) (a : ℝ) :
    eLpNorm (kUPhi L a) 1 volume
      ≤ ENNReal.ofReal (2 * (1 + |a| * L + Real.sqrt L) * Real.exp (L * a ^ 2)) := by
  have h1 : ∫⁻ v, ‖kUPhi L a v‖ₑ ∂volume = ∫⁻ v, ENNReal.ofReal (kUPhi L a v) ∂volume := by
    apply lintegral_congr_ae
    apply Eventually.of_forall
    intro v
    dsimp only
    rw [Real.enorm_eq_ofReal (kUPhi_nonneg hL a v)]
  rw [eLpNorm_one_eq_lintegral_enorm (continuous_kUPhi L a).aestronglyMeasurable, h1,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_kUPhi hL a)
      (Eventually.of_forall (fun v => kUPhi_nonneg hL a v))]
  exact ENNReal.ofReal_le_ofReal (integral_kUPhi_le hL a)

/-! ## The generic Young `L²` convolution bound (following `Conjugate2to2`) -/

/-- Pointwise Cauchy–Schwarz bound for convolution with a measurable kernel `k`
(the generic form of `enorm_convolution_conjugateHeat_le`): for every `x`,
`‖(k ⋆ f)(x)‖ₑ ≤ (∫⁻ ‖k‖ₑ)^{1/2} · (∫⁻ t, ‖k t‖ₑ ‖f (x−t)‖ₑ²)^{1/2}`. -/
theorem enorm_convolution_le (k : ℝ → ℝ) (hk_meas : AEStronglyMeasurable k volume)
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f volume) (x : ℝ) :
    ‖MeasureTheory.convolution k f (ContinuousLinearMap.mul ℝ ℝ) volume x‖ₑ
      ≤ (∫⁻ t, ‖k t‖ₑ ∂volume) ^ (1/2 : ℝ)
        * (∫⁻ t, ‖k t‖ₑ * ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2 : ℝ) := by
  have hu : AEMeasurable (fun t => ‖k t‖ₑ ^ (1/2 : ℝ)) volume :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hk_meas.enorm
  have hv : AEMeasurable (fun t => ‖k t‖ₑ ^ (1/2 : ℝ) * ‖f (x - t)‖ₑ) volume :=
    hu.mul (hf.enorm.comp_quasiMeasurePreserving
      (volume.measurePreserving_sub_left x).quasiMeasurePreserving)
  rw [MeasureTheory.convolution_mul]
  calc ‖∫ t, k t * f (x - t) ∂volume‖ₑ
      ≤ ∫⁻ t, ‖k t * f (x - t)‖ₑ ∂volume :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t, ‖k t‖ₑ ^ (1/2 : ℝ) * (‖k t‖ₑ ^ (1/2 : ℝ) * ‖f (x - t)‖ₑ) ∂volume := by
        apply lintegral_congr_ae
        apply Eventually.of_forall
        intro t
        dsimp only
        have hrw : ‖k t‖ₑ ^ (1/2 : ℝ) * (‖k t‖ₑ ^ (1/2 : ℝ) * ‖f (x - t)‖ₑ)
            = ‖k t‖ₑ * ‖f (x - t)‖ₑ := by
          rw [← mul_assoc,
            ← ENNReal.rpow_add_of_nonneg (1/2 : ℝ) (1/2 : ℝ) (by norm_num) (by norm_num),
            show (1/2 : ℝ) + 1/2 = 1 by norm_num, ENNReal.rpow_one]
        rw [enorm_mul, hrw]
    _ ≤ (∫⁻ t, (‖k t‖ₑ ^ (1/2 : ℝ)) ^ (2 : ℝ) ∂volume) ^ (1/2 : ℝ)
          * (∫⁻ t, (‖k t‖ₑ ^ (1/2 : ℝ) * ‖f (x - t)‖ₑ) ^ (2 : ℝ) ∂volume) ^ (1/2 : ℝ) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hu hv
    _ = (∫⁻ t, ‖k t‖ₑ ∂volume) ^ (1/2 : ℝ)
          * (∫⁻ t, ‖k t‖ₑ * ‖f (x - t)‖ₑ ^ (2 : ℝ) ∂volume) ^ (1/2 : ℝ) := by
        have hleft : (∫⁻ t, (‖k t‖ₑ ^ (1/2 : ℝ)) ^ (2 : ℝ) ∂volume)
            = ∫⁻ t, ‖k t‖ₑ ∂volume := by
          apply lintegral_congr_ae
          apply Eventually.of_forall
          intro t
          dsimp only
          rw [← ENNReal.rpow_mul, show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
        have hright : (∫⁻ t, (‖k t‖ₑ ^ (1/2 : ℝ) * ‖f (x - t)‖ₑ) ^ (2 : ℝ) ∂volume)
            = ∫⁻ t, ‖k t‖ₑ * ‖f (x - t)‖ₑ ^ (2 : ℝ) ∂volume := by
          apply lintegral_congr_ae
          apply Eventually.of_forall
          intro t
          dsimp only
          rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0:ℝ) ≤ 2 by norm_num),
            ← ENNReal.rpow_mul, show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
        rw [hleft, hright]

/-- The `L¹` seminorm of a nonnegative integrable kernel is `ofReal` of its
integral. -/
theorem eLpNorm_one_of_nonneg (k : ℝ → ℝ) (hk_meas : AEStronglyMeasurable k volume)
    (hk_int : Integrable k volume) (hk_nn : ∀ v, 0 ≤ k v) :
    eLpNorm k 1 volume = ENNReal.ofReal (∫ v, k v) := by
  have h1 : ∫⁻ v, ‖k v‖ₑ ∂volume = ∫⁻ v, ENNReal.ofReal (k v) ∂volume := by
    apply lintegral_congr_ae
    apply Eventually.of_forall
    intro v
    dsimp only
    rw [Real.enorm_eq_ofReal (hk_nn v)]
  rw [eLpNorm_one_eq_lintegral_enorm hk_meas, h1,
    ← ofReal_integral_eq_lintegral_ofReal hk_int (Eventually.of_forall hk_nn)]

/-- **Young's convolution inequality on `L²`** for a nonnegative integrable
kernel (the generic form of `eLpNorm_conjugateHeat_conv_le`): for `f ∈ L²(ℝ)`,
`‖k ⋆ f‖₂ ≤ (∫ k)·‖f‖₂`. -/
theorem eLpNorm_conv_le (k : ℝ → ℝ) (hk_meas : AEStronglyMeasurable k volume)
    (hk_int : Integrable k volume) (hk_nn : ∀ v, 0 ≤ k v)
    (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    MemLp (MeasureTheory.convolution k f (ContinuousLinearMap.mul ℝ ℝ) volume) 2 volume ∧
    eLpNorm (MeasureTheory.convolution k f (ContinuousLinearMap.mul ℝ ℝ) volume) 2 volume ≤
      ENNReal.ofReal (∫ v, k v) * eLpNorm f 2 volume := by
  have hf_meas : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hf_fin : eLpNorm f 2 volume < ∞ := hf
  have hconv : AEStronglyMeasurable (MeasureTheory.convolution k f
      (ContinuousLinearMap.mul ℝ ℝ) volume) volume :=
    hk_meas.convolution (ContinuousLinearMap.mul ℝ ℝ) hf_meas
  have hA : ∫⁻ t, ‖k t‖ₑ ∂volume = ENNReal.ofReal (∫ v, k v) := by
    rw [← eLpNorm_one_eq_lintegral_enorm hk_meas, eLpNorm_one_of_nonneg k hk_meas hk_int hk_nn]
  have eLpNorm_two_eq : ∀ g : ℝ → ℝ, AEStronglyMeasurable g volume →
      eLpNorm g 2 volume = (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2 : ℝ) := by
    intro g hg
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg]
    simp
  have hF : AEMeasurable (fun p : ℝ × ℝ => ‖k p.2‖ₑ * ‖f (p.1 - p.2)‖ₑ ^ (2:ℝ))
      (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : ℝ × ℝ => ‖f (p.1 - p.2)‖ₑ) (volume.prod volume) :=
      hf_meas.enorm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)
    have h2 : AEMeasurable (fun p : ℝ × ℝ => ‖f (p.1 - p.2)‖ₑ ^ (2:ℝ)) (volume.prod volume) :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable h1
    exact (hk_meas.comp_snd.enorm).mul h2
  have hB : AEMeasurable (fun x => ∫⁻ t, ‖k t‖ₑ * ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume) volume :=
    hF.lintegral_prod_right'
  have hft : ∀ t : ℝ, AEMeasurable (fun x => ‖f (x - t)‖ₑ ^ (2:ℝ)) volume := fun t =>
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (hf_meas.enorm.comp_quasiMeasurePreserving
        (MeasureTheory.measurePreserving_sub_right volume t).quasiMeasurePreserving)
  have htrans : ∀ t : ℝ, ∫⁻ x, ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume = eLpNorm f 2 volume ^ (2:ℝ) := by
    intro t
    have h1 : ∫⁻ x, ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂volume :=
      MeasureTheory.lintegral_sub_right_eq_self (μ := volume) (fun x => ‖f x‖ₑ ^ (2:ℝ)) t
    rw [h1, eLpNorm_two_eq f hf_meas, ← ENNReal.rpow_mul,
      show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hpt : ∀ x : ℝ, ‖MeasureTheory.convolution k f (ContinuousLinearMap.mul ℝ ℝ) volume x‖ₑ
        ^ (2:ℝ)
      ≤ (∫⁻ t, ‖k t‖ₑ ∂volume) * (∫⁻ t, ‖k t‖ₑ * ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume) := by
    intro x
    refine (ENNReal.rpow_le_rpow (enorm_convolution_le k hk_meas f hf_meas x)
      (show (0:ℝ) ≤ 2 by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0:ℝ) ≤ 2 by norm_num),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      show (1/2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one]
  have hmain : eLpNorm (MeasureTheory.convolution k f (ContinuousLinearMap.mul ℝ ℝ) volume)
        2 volume
      ≤ ENNReal.ofReal (∫ v, k v) * eLpNorm f 2 volume := by
    rw [eLpNorm_two_eq _ hconv]
    calc (∫⁻ x, ‖MeasureTheory.convolution k f (ContinuousLinearMap.mul ℝ ℝ) volume x‖ₑ
            ^ (2:ℝ) ∂volume) ^ (1/2 : ℝ)
        ≤ (∫⁻ x, (∫⁻ t, ‖k t‖ₑ ∂volume) * (∫⁻ t, ‖k t‖ₑ * ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume)
            ∂volume) ^ (1/2 : ℝ) :=
          ENNReal.rpow_le_rpow (lintegral_mono hpt) (show (0:ℝ) ≤ 1/2 by norm_num)
      _ = ((∫⁻ t, ‖k t‖ₑ ∂volume)
            * (∫⁻ x, ∫⁻ t, ‖k t‖ₑ * ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume ∂volume)) ^ (1/2 : ℝ) := by
          rw [lintegral_const_mul'' _ hB]
      _ = ((∫⁻ t, ‖k t‖ₑ ∂volume)
            * (∫⁻ t, ∫⁻ x, ‖k t‖ₑ * ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume ∂volume)) ^ (1/2 : ℝ) := by
          rw [lintegral_lintegral_swap hF]
      _ = ((∫⁻ t, ‖k t‖ₑ ∂volume)
            * (∫⁻ t, ‖k t‖ₑ * (∫⁻ x, ‖f (x - t)‖ₑ ^ (2:ℝ) ∂volume) ∂volume)) ^ (1/2 : ℝ) := by
          congr 2
          apply lintegral_congr_ae
          apply Eventually.of_forall
          intro t
          dsimp only
          exact lintegral_const_mul'' _ (hft t)
      _ = ((∫⁻ t, ‖k t‖ₑ ∂volume)
            * (∫⁻ t, ‖k t‖ₑ * eLpNorm f 2 volume ^ (2:ℝ) ∂volume)) ^ (1/2 : ℝ) := by
          congr 2
          apply lintegral_congr_ae
          apply Eventually.of_forall
          intro t
          dsimp only
          rw [htrans t]
      _ = ((∫⁻ t, ‖k t‖ₑ ∂volume)
            * ((∫⁻ t, ‖k t‖ₑ ∂volume) * eLpNorm f 2 volume ^ (2:ℝ))) ^ (1/2 : ℝ) := by
          rw [lintegral_mul_const'' _ hk_meas.enorm]
      _ = ENNReal.ofReal (∫ v, k v) * eLpNorm f 2 volume := by
          rw [hA]
          have h1 : ENNReal.ofReal (∫ v, k v) * (ENNReal.ofReal (∫ v, k v) * eLpNorm f 2 volume
              ^ (2:ℝ))
              = (ENNReal.ofReal (∫ v, k v) * eLpNorm f 2 volume) ^ (2:ℝ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0:ℝ) ≤ 2 by norm_num),
              ENNReal.rpow_two (ENNReal.ofReal (∫ v, k v))]
            ring
          rw [h1, ← ENNReal.rpow_mul, show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one]
  exact ⟨hmain.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf_fin), hmain⟩

/-- The Young convolution bound for `kUPhi` (the
`‖ℬ_{L,a}‖_{2→2} ≤ ‖k‖₁` step): for `f ∈ L²(ℝ)`,
`‖k ⋆ f‖₂ ≤ 2 (1 + |a|L + √L) e^{La²} ‖f‖₂`. -/
theorem eLpNorm_conv_kUPhi_le (hL : 0 < L) (a : ℝ) (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    MemLp (MeasureTheory.convolution (kUPhi L a) f (ContinuousLinearMap.mul ℝ ℝ) volume) 2 volume
    ∧ eLpNorm (MeasureTheory.convolution (kUPhi L a) f (ContinuousLinearMap.mul ℝ ℝ) volume)
        2 volume
      ≤ ENNReal.ofReal (2 * (1 + |a| * L + Real.sqrt L) * Real.exp (L * a ^ 2))
        * eLpNorm f 2 volume := by
  obtain ⟨hmem, hbound⟩ := eLpNorm_conv_le (kUPhi L a)
    (continuous_kUPhi L a).aestronglyMeasurable (integrable_kUPhi hL a) (kUPhi_nonneg hL a) f hf
  exact ⟨hmem, hbound.trans
    (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (integral_kUPhi_le hL a))
      (by positivity))⟩

/-! ## The operator `ℬ_{L,a}` as a continuous linear map on `L²(ℝ)` -/

/-- The pointwise action of `ℬ_{L,a}` on `f : L²(ℝ)`: `z ↦ ∫ w, ℬ(z, w) f(w) dw`
(the factorization's second factor).  Well-defined for every `z` since `|ℬ(z, ·)| ≤ k(z−·)`
with `k(z−·) ∈ L²` (Cauchy–Schwarz). -/
noncomputable def bPhiApply (L a : ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) (z : ℝ) : ℝ :=
  ∫ w : ℝ, bPhiKernel L a (z, w) * f w

/-- `bPhiApply f` is a.e.-strongly-measurable (joint measurability +
`integral_prod_right'`). -/
theorem bPhiApply_aestronglyMeasurable (L a : ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    AEStronglyMeasurable (bPhiApply L a f) volume :=
  ((continuous_bPhiKernel L a).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable f).comp_snd).integral_prod_right'

/-- The squared-shift-polynomial Gaussian `(1 + (w + c)²) · gaussT L w` is
integrable (expand `(w+c)² = w² + 2cw + c²`; each piece is an absolute moment). -/
theorem integrable_sq_add_gaussT (hL : 0 < L) (c : ℝ) :
    Integrable (fun w : ℝ => (1 + (w + c) ^ 2) * gaussT L w) volume := by
  have e : (fun w : ℝ => (1 + (w + c) ^ 2) * gaussT L w)
      = (fun w => gaussT L w) + (fun w => w ^ 2 * gaussT L w)
        + (fun w => (2 * c) * (w * gaussT L w)) + (fun w => c ^ 2 * gaussT L w) := by
    funext w
    simp only [Pi.add_apply]
    ring
  rw [e]
  have h0 : Integrable (fun w : ℝ => gaussT L w) volume := integrable_gaussT hL
  have h2 : Integrable (fun w : ℝ => w ^ 2 * gaussT L w) volume := by
    convert integrable_abs_pow_gaussT hL 2 using 1
    funext w
    rw [sq_abs]
  have h1 : Integrable (fun w : ℝ => w * gaussT L w) volume := by
    apply MeasureTheory.Integrable.mono' (integrable_abs_pow_gaussT hL 1)
      ((continuous_id.mul (continuous_gaussT L)).aestronglyMeasurable)
    filter_upwards with w
    show |w * gaussT L w| ≤ |w| ^ 1 * gaussT L w
    rw [abs_mul, abs_of_nonneg (gaussT_nonneg _ _), pow_one]
  exact ((h0.add h2).add (h1.const_mul (2 * c))).add (h0.const_mul (c ^ 2))

/-- `kUPhi` is in `L²(ℝ)` for `0 < L` (its square has Gaussian decay). -/
theorem memLp_kUPhi_two (hL : 0 < L) (a : ℝ) : MemLp (kUPhi L a) 2 volume := by
  have h2L : (0 : ℝ) < 2 * L := by positivity
  rw [MeasureTheory.memLp_iff]
  -- `(kUPhi)²` is integrable: completed square + polynomial Gaussian moments
  have hsq : Integrable (fun v : ℝ => (kUPhi L a v) ^ 2) volume := by
    have hform : (fun v : ℝ => (kUPhi L a v) ^ 2) = fun v : ℝ =>
        (4 * Real.pi * L)⁻¹ * Real.exp (2 * L * a ^ 2) *
          ((1 + |v|) ^ 2 * gaussT L (v - 2 * L * a)) := by
      funext v
      unfold kUPhi
      rw [show ((1 + |v|) * Real.exp (a * v) * heatKernel L v) ^ 2
          = (1 + |v|) ^ 2 * ((4 * Real.pi * L)⁻¹ * (Real.exp (2 * (a * v)) * gaussT L v)) from by
        rw [mul_pow, mul_pow, exp_sq, heatKernel_sq hL]
        ring]
      rw [show Real.exp (2 * (a * v)) * gaussT L v
          = Real.exp (2 * L * a ^ 2) * gaussT L (v - 2 * L * a) from by
        rw [gaussT_eq_exp_neg_mul_sq hL, gaussT_eq_exp_neg_mul_sq hL,
          ← Real.exp_add, ← Real.exp_add]
        congr 1
        field_simp [show (2 : ℝ) * L ≠ 0 from by positivity]
        ring]
      ring
    rw [hform]
    -- `(1+|v|)² ≤ 2 + 2v²`, then translate `v ↦ w + 2La` and use `integrable_sq_add_gaussT`
    have hF : Integrable (fun w : ℝ => (1 + |w + 2 * L * a|) ^ 2 * gaussT L w) volume := by
      apply MeasureTheory.Integrable.mono' ((integrable_sq_add_gaussT hL (2 * L * a)).const_mul 2)
        (((continuous_const.add (continuous_abs.comp
          (continuous_id.add continuous_const))).pow 2).mul (continuous_gaussT _)
          ).aestronglyMeasurable
      filter_upwards with w
      show |(1 + |w + 2 * L * a|) ^ 2 * gaussT L w|
          ≤ 2 * ((1 + (w + 2 * L * a) ^ 2) * gaussT L w)
      rw [abs_of_nonneg (mul_nonneg (by positivity) (gaussT_nonneg _ _))]
      have hg : 0 ≤ gaussT L w := gaussT_nonneg _ _
      calc (1 + |w + 2 * L * a|) ^ 2 * gaussT L w
          ≤ (2 + 2 * (w + 2 * L * a) ^ 2) * gaussT L w := by
            apply mul_le_mul_of_nonneg_right _ hg
            nlinarith [sq_nonneg (|w + 2 * L * a| - 1), sq_abs (w + 2 * L * a)]
        _ = 2 * ((1 + (w + 2 * L * a) ^ 2) * gaussT L w) := by ring
    have hshift : (fun v : ℝ => (1 + |v|) ^ 2 * gaussT L (v - 2 * L * a))
        = fun v => (fun w : ℝ => (1 + |w + 2 * L * a|) ^ 2 * gaussT L w) (v - 2 * L * a) := by
      funext v
      show (1 + |v|) ^ 2 * gaussT L (v - 2 * L * a)
          = (1 + |v - 2 * L * a + 2 * L * a|) ^ 2 * gaussT L (v - 2 * L * a)
      rw [sub_add_cancel]
    have hshiftint : Integrable (fun v : ℝ => (1 + |v|) ^ 2 * gaussT L (v - 2 * L * a)) volume := by
      rw [hshift]
      exact hF.comp_sub_right (2 * L * a)
    exact hshiftint.const_mul _
  -- conclude via the enorm identity
  have hmeas : AEStronglyMeasurable (kUPhi L a) volume :=
    (continuous_kUPhi L a).aestronglyMeasurable
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmeas]
  simp only [ENNReal.toReal_ofNat]
  have hfin : (∫⁻ v, ‖kUPhi L a v‖ₑ ^ (2:ℝ) ∂volume) < ⊤ := by
    rw [show (∫⁻ v, ‖kUPhi L a v‖ₑ ^ (2:ℝ) ∂volume)
        = ∫⁻ v, ENNReal.ofReal ((kUPhi L a v) ^ 2) ∂volume from by
      apply lintegral_congr
      intro v
      rw [HilbertSchmidt.enorm_rpow_two, Real.enorm_eq_ofReal (kUPhi_nonneg hL a v)]
      rw [show (ENNReal.ofReal (kUPhi L a v)) ^ 2
          = ENNReal.ofReal (kUPhi L a v * kUPhi L a v) from by
        rw [pow_two, ← ENNReal.ofReal_mul (kUPhi_nonneg hL a v)]]
      congr 1
      ring]
    rw [← ofReal_integral_eq_lintegral_ofReal hsq
      (Eventually.of_forall fun v => sq_nonneg _)]
    exact ENNReal.ofReal_lt_top
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

/-- For each `z`, the section `w ↦ ℬ(z, w) f(w)` is integrable
(dominated by `k(z−·)|f|`, an `L²·L²` product). -/
theorem integrable_bPhiKernel_section (hL : 0 < L) (a : ℝ) (f : Lp ℝ 2 (volume : Measure ℝ))
    (z : ℝ) :
    Integrable (fun w : ℝ => bPhiKernel L a (z, w) * f w) volume := by
  have hk2 : MemLp (fun w : ℝ => kUPhi L a (z - w)) 2 volume := by
    have h := (memLp_kUPhi_two hL a).comp_measurePreserving
      (MeasureTheory.Measure.measurePreserving_sub_left volume z)
    exact h
  have hf2 : MemLp (fun w : ℝ => |f w|) 2 volume := (Lp.memLp f).abs
  have hdom : Integrable (fun w : ℝ => kUPhi L a (z - w) * |f w|) volume :=
    MemLp.integrable_mul hk2 hf2
  apply MeasureTheory.Integrable.mono' hdom
    (((continuous_bPhiKernel L a).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f))
  filter_upwards with w
  show |bPhiKernel L a (z, w) * f w| ≤ kUPhi L a (z - w) * |f w|
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (bPhiKernel_abs_le hL a z w) (abs_nonneg _)

/-- **Pointwise domination of the action**:
`|(ℬ f)(z)| ≤ (k ⋆ |f|)(z)`. -/
theorem bPhiApply_abs_le_conv (hL : 0 < L) (a : ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) (z : ℝ) :
    |bPhiApply L a f z|
      ≤ MeasureTheory.convolution (kUPhi L a) (fun w => |f w|) (ContinuousLinearMap.mul ℝ ℝ)
        volume z := by
  unfold bPhiApply
  calc |∫ w : ℝ, bPhiKernel L a (z, w) * f w|
      ≤ ∫ w : ℝ, |bPhiKernel L a (z, w) * f w| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ w : ℝ, kUPhi L a (z - w) * |f w| := by
        have hk2 : MemLp (fun w : ℝ => kUPhi L a (z - w)) 2 volume := by
          have h := (memLp_kUPhi_two hL a).comp_measurePreserving
            (MeasureTheory.Measure.measurePreserving_sub_left volume z)
          exact h
        have hint1 : Integrable (fun w : ℝ => |bPhiKernel L a (z, w) * f w|) volume :=
          (integrable_bPhiKernel_section hL a f z).abs
        have hint2 : Integrable (fun w : ℝ => kUPhi L a (z - w) * |f w|) volume :=
          MemLp.integrable_mul hk2 (Lp.memLp f).abs
        apply integral_mono hint1 hint2
        intro w
        show |bPhiKernel L a (z, w) * f w| ≤ kUPhi L a (z - w) * |f w|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (bPhiKernel_abs_le hL a z w) (abs_nonneg _)
    _ = MeasureTheory.convolution (kUPhi L a) (fun w => |f w|) (ContinuousLinearMap.mul ℝ ℝ)
          volume z := by
        rw [MeasureTheory.convolution_mul]
        have h := MeasureTheory.integral_sub_left_eq_self (μ := volume)
          (fun w : ℝ => kUPhi L a w * |f (z - w)|) z
        simp_rw [show ∀ w : ℝ, z - (z - w) = w from fun w => by ring] at h
        exact h

/-- The `L²` bound for the action (the function-level `‖ℬ‖_{2→2} ≤ ‖k‖₁`): `‖ℬ f‖₂ ≤ ‖k‖₁ ‖f‖₂`. -/
theorem eLpNorm_bPhiApply_le (hL : 0 < L) (a : ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    eLpNorm (bPhiApply L a f) 2 volume
      ≤ ENNReal.ofReal (∫ v, kUPhi L a v) * eLpNorm f 2 volume := by
  have hf2 : MemLp (fun w : ℝ => |f w|) 2 volume := (Lp.memLp f).abs
  have hconv := eLpNorm_conv_le (kUPhi L a) (continuous_kUPhi L a).aestronglyMeasurable
    (integrable_kUPhi hL a) (kUPhi_nonneg hL a) (fun w => |f w|) hf2
  have hpt : ∀ z : ℝ, ‖bPhiApply L a f z‖
      ≤ ‖MeasureTheory.convolution (kUPhi L a) (fun w => |f w|) (ContinuousLinearMap.mul ℝ ℝ)
          volume z‖ := by
    intro z
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hnn : 0 ≤ MeasureTheory.convolution (kUPhi L a) (fun w => |f w|)
        (ContinuousLinearMap.mul ℝ ℝ) volume z := by
      rw [MeasureTheory.convolution_mul]
      apply integral_nonneg
      intro t
      exact mul_nonneg (kUPhi_nonneg hL a t) (abs_nonneg _)
    rw [abs_of_nonneg hnn]
    exact bPhiApply_abs_le_conv hL a f z
  have hnorm : eLpNorm (fun w => |f w|) 2 volume = eLpNorm f 2 volume := by
    apply MeasureTheory.eLpNorm_congr_enorm_ae
    · exact continuous_abs.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)
    · exact Lp.aestronglyMeasurable f
    · filter_upwards with w
      exact enorm_abs _
  calc eLpNorm (bPhiApply L a f) 2 volume
      ≤ eLpNorm (MeasureTheory.convolution (kUPhi L a) (fun w => |f w|)
          (ContinuousLinearMap.mul ℝ ℝ) volume) 2 volume :=
        MeasureTheory.eLpNorm_mono (bPhiApply_aestronglyMeasurable L a f) hpt
    _ ≤ ENNReal.ofReal (∫ v, kUPhi L a v) * eLpNorm (fun w => |f w|) 2 volume := hconv.2
    _ = ENNReal.ofReal (∫ v, kUPhi L a v) * eLpNorm f 2 volume := by rw [hnorm]

/-- `bPhiApply f` is in `L²(ℝ)`. -/
theorem memLp_bPhiApply (hL : 0 < L) (a : ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    MemLp (bPhiApply L a f) 2 volume := by
  rw [MeasureTheory.memLp_iff]
  exact (eLpNorm_bPhiApply_le hL a f).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f))

/-- `ℬ_{L,a}` as a continuous linear map on `L²(ℝ)` (the factorization's second
factor), packaged by `LinearMap.mkContinuous` with operator-norm
bound `‖k‖₁ = ∫ kUPhi`. -/
noncomputable def bPhiCLM (L : ℝ) (hL : 0 < L) (a : ℝ) :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => MemLp.toLp _ (memLp_bPhiApply hL a f)
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_bPhiApply hL a (f + g)),
          MemLp.coeFn_toLp (memLp_bPhiApply hL a f),
          MemLp.coeFn_toLp (memLp_bPhiApply hL a g),
          Lp.coeFn_add (MemLp.toLp _ (memLp_bPhiApply hL a f)) (MemLp.toLp _ (memLp_bPhiApply hL a g))]
          with z hfg hf hg hadd
        rw [hfg, hadd, Pi.add_apply, hf, hg]
        unfold bPhiApply
        rw [← integral_add (integrable_bPhiKernel_section hL a f z)
          (integrable_bPhiKernel_section hL a g z)]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with w hw
        rw [hw, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_bPhiApply hL a (c • f)),
          MemLp.coeFn_toLp (memLp_bPhiApply hL a f),
          Lp.coeFn_smul c (MemLp.toLp _ (memLp_bPhiApply hL a f))] with z hcf hf hsmul
        rw [hcf, RingHom.id_apply, hsmul, Pi.smul_apply, hf, smul_eq_mul]
        unfold bPhiApply
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with w hw
        rw [hw, Pi.smul_apply, smul_eq_mul]
        ring }
    (∫ v, kUPhi L a v)
    (fun f => by
      have hb := eLpNorm_bPhiApply_le hL a f
      have hfin : ENNReal.ofReal (∫ v, kUPhi L a v) * eLpNorm f 2 volume ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)
      have hk0 : (0 : ℝ) ≤ ∫ v, kUPhi L a v :=
        integral_nonneg fun v => kUPhi_nonneg hL a v
      calc ‖MemLp.toLp _ (memLp_bPhiApply hL a f)‖
          = (eLpNorm (bPhiApply L a f) 2 volume).toReal := by
            rw [Lp.norm_def]
            congr 1
            exact eLpNorm_congr_ae (MemLp.coeFn_toLp _)
        _ ≤ (ENNReal.ofReal (∫ v, kUPhi L a v) * eLpNorm f 2 volume).toReal :=
            ENNReal.toReal_mono hfin hb
        _ = (∫ v, kUPhi L a v) * (eLpNorm f 2 volume).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hk0]
        _ = (∫ v, kUPhi L a v) * ‖f‖ := by rw [Lp.norm_def])

/-- The action of `bPhiCLM` is a.e. the pointwise kernel integral. -/
theorem bPhiCLM_apply_ae (L : ℝ) (hL : 0 < L) (a : ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ∀ᵐ z ∂volume, (bPhiCLM L hL a f) z = bPhiApply L a f z := by
  have h : bPhiCLM L hL a f = MemLp.toLp _ (memLp_bPhiApply hL a f) := rfl
  rw [h]
  exact MemLp.coeFn_toLp _

/-- The operator-norm bound for `ℬ_{L,a}` (the first half of the `L¹`-bound
step): `‖ℬ‖ₑ ≤ ofReal (∫ k)`. -/
theorem enorm_bPhiCLM_le (L : ℝ) (hL : 0 < L) (a : ℝ) :
    ‖bPhiCLM L hL a‖ₑ ≤ ENNReal.ofReal (∫ v, kUPhi L a v) := by
  apply ContinuousLinearMap.opENorm_le_bound
  intro f
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (bPhiCLM_apply_ae L hL a f)]
  exact eLpNorm_bPhiApply_le hL a f

/-- The quantitative operator-norm bound for `ℬ_{L,a}` (**the `L¹` bound for
`k`**): `‖ℬ_{L,a}‖ₑ ≤ ofReal (2 (1 + |a|L + √L) e^{La²})`. -/
theorem enorm_bPhiCLM_le' (L : ℝ) (hL : 0 < L) (a : ℝ) :
    ‖bPhiCLM L hL a‖ₑ
      ≤ ENNReal.ofReal (2 * (1 + |a| * L + Real.sqrt L) * Real.exp (L * a ^ 2)) := by
  have hk0 : (0 : ℝ) ≤ ∫ v, kUPhi L a v :=
    integral_nonneg fun v => kUPhi_nonneg hL a v
  exact (enorm_bPhiCLM_le L hL a).trans
    (ENNReal.ofReal_le_ofReal (integral_kUPhi_le hL a))

/-! ## The `vKernel` side: `L²`-membership and the square-root bound -/

/-- The `vKernel` is in `L²` of the product for `0 < M`, `T + 1 ≤ a`
(the integrability half of the `vKernel` bound, `vKernel_sq_integral_le`). -/
theorem memLp_vKernel (T a M : ℝ) (hT : 0 < T) (hM : 0 < M) (ha : T + 1 ≤ a) :
    MemLp (vKernel T a M) 2 (volume.prod volume) := by
  obtain ⟨C, hC, hbound⟩ := vKernel_sq_integral_le T hT
  obtain ⟨hint, -⟩ := hbound M a hM ha
  have hmeas : AEStronglyMeasurable (vKernel T a M) (volume.prod volume) :=
    (measurable_vKernel T a M).aestronglyMeasurable
  rw [MeasureTheory.memLp_iff]
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmeas]
  simp only [ENNReal.toReal_ofNat]
  have hfin : (∫⁻ p : ℝ × ℝ, ‖vKernel T a M p‖ₑ ^ (2:ℝ) ∂(volume.prod volume)) < ⊤ := by
    rw [show (∫⁻ p : ℝ × ℝ, ‖vKernel T a M p‖ₑ ^ (2:ℝ) ∂(volume.prod volume))
        = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((vKernel T a M p) ^ 2) ∂(volume.prod volume) from by
      apply lintegral_congr
      intro p
      rw [HilbertSchmidt.enorm_rpow_two, enorm_sq_eq_ofReal, Real.norm_eq_abs, sq_abs]]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun p => sq_nonneg _)]
    exact ENNReal.ofReal_lt_top
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

/-- Square-root split of the `vKernel` bound:
`√(C·(1+M)²·(1+a³)·e^{2Ta²−4Ma}) = √C·(1+M)·√(1+a³)·e^{Ta²−2Ma}`. -/
theorem sqrt_lembound (C M T a : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (ha : 1 ≤ a) :
    Real.sqrt (C * (1 + M) ^ 2 * (1 + a ^ 3) * Real.exp (2 * T * a ^ 2 - 4 * M * a))
      = Real.sqrt C * (1 + M) * Real.sqrt (1 + a ^ 3) * Real.exp (T * a ^ 2 - 2 * M * a) := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have h1a3 : (0 : ℝ) ≤ 1 + a ^ 3 := by
    have h := pow_nonneg ha0 3
    linarith
  have hC1 : (0 : ℝ) ≤ C * (1 + M) ^ 2 := mul_nonneg hC (by positivity)
  have hC2 : (0 : ℝ) ≤ C * (1 + M) ^ 2 * (1 + a ^ 3) := mul_nonneg hC1 h1a3
  have hE : Real.exp (2 * T * a ^ 2 - 4 * M * a) = (Real.exp (T * a ^ 2 - 2 * M * a)) ^ 2 := by
    rw [exp_sq]
    congr 1
    ring
  rw [hE, Real.sqrt_mul hC2, Real.sqrt_mul hC1, Real.sqrt_mul hC,
    Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + M), Real.sqrt_sq (Real.exp_pos _).le]

/-- The `L²`-norm bound for `vKernel` in square-root form (from the `vKernel`
square-integral bound `hbound`): `‖V‖₂ ≤ √C·(1+M)·√(1+a³)·e^{Ta²−2Ma}`. -/
theorem eLpNorm_vKernel_le_of_bound (T a M : ℝ) (hT : 0 < T) (hM : 0 < M) (ha : T + 1 ≤ a)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∫ p : ℝ × ℝ, (vKernel T a M p) ^ 2 ∂(volume.prod volume) ≤
      C * (1 + M) ^ 2 * (1 + a ^ 3) * Real.exp (2 * T * a ^ 2 - 4 * M * a)) :
    eLpNorm (vKernel T a M) 2 (volume.prod volume)
      ≤ ENNReal.ofReal (Real.sqrt C * (1 + M) * Real.sqrt (1 + a ^ 3)
        * Real.exp (T * a ^ 2 - 2 * M * a)) := by
  have hmeas : AEStronglyMeasurable (vKernel T a M) (volume.prod volume) :=
    (measurable_vKernel T a M).aestronglyMeasurable
  obtain ⟨C', hC', hbound'⟩ := vKernel_sq_integral_le T hT
  obtain ⟨hint, -⟩ := hbound' M a hM ha
  have h1 : (∫⁻ p : ℝ × ℝ, ‖vKernel T a M p‖ₑ ^ (2:ℝ) ∂(volume.prod volume))
      = ENNReal.ofReal (∫ p : ℝ × ℝ, (vKernel T a M p) ^ 2 ∂(volume.prod volume)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun p => sq_nonneg _)]
    apply lintegral_congr
    intro p
    rw [HilbertSchmidt.enorm_rpow_two, enorm_sq_eq_ofReal, Real.norm_eq_abs, sq_abs]
  have hform : eLpNorm (vKernel T a M) 2 (volume.prod volume)
      = (∫⁻ p : ℝ × ℝ, ‖vKernel T a M p‖ₑ ^ (2:ℝ) ∂(volume.prod volume)) ^ (1/2 : ℝ) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmeas]
    simp
  have h1a3 : (0 : ℝ) ≤ 1 + a ^ 3 := by
    have haa0 : 0 ≤ a := by linarith
    have h := pow_nonneg haa0 3
    linarith
  rw [hform]
  calc (∫⁻ p : ℝ × ℝ, ‖vKernel T a M p‖ₑ ^ (2:ℝ) ∂(volume.prod volume)) ^ (1/2 : ℝ)
      = (ENNReal.ofReal (∫ p : ℝ × ℝ, (vKernel T a M p) ^ 2 ∂(volume.prod volume)))
          ^ (1/2 : ℝ) := by rw [h1]
    _ ≤ (ENNReal.ofReal (C * (1 + M) ^ 2 * (1 + a ^ 3) * Real.exp (2 * T * a ^ 2 - 4 * M * a)))
          ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hbound) (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (C * (1 + M) ^ 2 * (1 + a ^ 3)
          * Real.exp (2 * T * a ^ 2 - 4 * M * a))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le
          (by positivity)) h1a3) (Real.exp_pos _).le) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        congr 1
        rw [Real.sqrt_eq_rpow]
    _ = ENNReal.ofReal (Real.sqrt C * (1 + M) * Real.sqrt (1 + a ^ 3)
          * Real.exp (T * a ^ 2 - 2 * M * a)) := by
        congr 1
        exact sqrt_lembound C M T a hC.le hM.le (by linarith)

/-- The mixed Hilbert–Schmidt/operator-norm composition bound on `L²(ℝ)`:
`‖S ∘L T‖_HS ≤ ‖S‖_HS · ‖T‖_op` (from `HilbertSchmidt.sumSq_comp_le_right`;
the right-factor variant of `HilbertSchmidt.hsENorm_comp_le`). -/
theorem hsENorm_comp_op_le (S T : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ)) :
    HilbertSchmidt.hsENorm (S ∘L T) ≤ HilbertSchmidt.hsENorm S * ‖T‖ₑ := by
  unfold HilbertSchmidt.hsENorm
  rw [show S ∘L T = S ∘SL T from rfl]
  calc (HilbertSchmidt.sumSq (S ∘SL T) (HilbertSchmidt.canonicalBasis ℝ _)) ^ (1/2 : ℝ)
      ≤ (‖T‖ₑ ^ 2 * HilbertSchmidt.sumSq S (HilbertSchmidt.canonicalBasis ℝ _)) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow (HilbertSchmidt.sumSq_comp_le_right S T
          (HilbertSchmidt.canonicalBasis ℝ _) (HilbertSchmidt.canonicalBasis ℝ _)) (by norm_num)
    _ = ‖T‖ₑ * (HilbertSchmidt.sumSq S (HilbertSchmidt.canonicalBasis ℝ _)) ^ (1/2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), HilbertSchmidt.rpow_half_sq']
    _ = (HilbertSchmidt.sumSq S (HilbertSchmidt.canonicalBasis ℝ _)) ^ (1/2 : ℝ) * ‖T‖ₑ :=
        mul_comm _ _

/-- **The `U Φ` Hilbert–Schmidt bound** (a lemma of the paper): for `0 < T` there exist `C_T > 0`
and `K : ℕ` such that for all `0 < M`, `0 < L` with `a = √(2M) ≥ T + 1`,

  `‖U_a Q_{M,T} P_L U_a Φ‖₂ ≤ C_T (1+M+L)^K · exp(L a² + T a² − a³)`,

presented in the enorm form on the paper's factorization: the composite operator
`kernelOperator (vKernel) ∘L
bPhiCLM`, i.e. `(U_a Q U_a Φ) ∘ ℬ_{L,a}`.  The proof multiplies the
`vKernel` bound (via `eLpNorm_vKernel_le_of_bound` + `hsENorm_kernelOperator_le`)
by the Young-based operator bound `enorm_bPhiCLM_le'` (the `L¹` bound for `k`), and
absorbs the polynomial factors with `K = 4`, `C_T = 16√C_T(V)`, where `C_T(V)` is the constant
of the `vKernel` bound. -/
theorem uphi_hs_le (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ (M L a : ℝ) (hM : 0 < M) (hL : 0 < L) (haeq : a = Real.sqrt (2 * M)) (ha : T + 1 ≤ a),
        HilbertSchmidt.hsENorm (HilbertSchmidt.kernelOperator (memLp_vKernel T a M hT hM ha)
            ∘L bPhiCLM L hL a)
          ≤ ENNReal.ofReal (C * (1 + M + L) ^ K * Real.exp (L * a ^ 2 + T * a ^ 2 - a ^ 3)) := by
  obtain ⟨C0, hC0, hbound⟩ := vKernel_sq_integral_le T hT
  refine ⟨16 * Real.sqrt C0, by positivity, 4, fun M L a hM hL haeq ha => ?_⟩
  -- properties of `a = √(2M)`
  have ha0 : 0 ≤ a := by rw [haeq]; exact Real.sqrt_nonneg _
  have ha1 : 1 ≤ a := by linarith
  have ha2 : a ^ 2 = 2 * M := by rw [haeq]; exact Real.sq_sqrt (by positivity)
  have ha3 : a ^ 3 = 2 * M * a := by
    have h1 : a ^ 3 = a ^ 2 * a := by ring
    rw [h1, ha2]
  have haa : |a| = a := abs_of_nonneg ha0
  -- the V-side Hilbert–Schmidt bound (the `vKernel` bound in square-root form)
  have hV : eLpNorm (vKernel T a M) 2 (volume.prod volume)
      ≤ ENNReal.ofReal (Real.sqrt C0 * (1 + M) * Real.sqrt (1 + a ^ 3)
        * Real.exp (T * a ^ 2 - 2 * M * a)) :=
    eLpNorm_vKernel_le_of_bound T a M hT hM ha hC0 (hbound M a hM ha).2
  have hVhs := (HilbertSchmidt.hsENorm_kernelOperator_le (memLp_vKernel T a M hT hM ha)).trans hV
  -- the ℬ-side operator bound (the `L¹` bound for `k`)
  have hB := enorm_bPhiCLM_le' L hL a
  rw [haa] at hB
  -- the polynomial absorption (all factors nonneg)
  have hM0 : (0 : ℝ) ≤ 1 + M := by linarith [hM.le]
  have hA : (0 : ℝ) ≤ Real.sqrt C0 * (1 + M) := mul_nonneg (Real.sqrt_nonneg _) hM0
  have hau : a ≤ 1 + 2 * M := by
    rw [haeq]
    calc Real.sqrt (2 * M) ≤ Real.sqrt ((1 + 2 * M) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [hM.le, sq_nonneg M])
      _ = 1 + 2 * M := Real.sqrt_sq (by positivity)
  have h1a3sqrt : Real.sqrt (1 + a ^ 3) ≤ 2 * (1 + M) := by
    have h1 : 1 + a ^ 3 ≤ (2 * (1 + M)) ^ 2 := by
      rw [ha3]
      nlinarith [mul_le_mul_of_nonneg_left hau (by linarith [hM.le] : (0 : ℝ) ≤ 2 * M)]
    calc Real.sqrt (1 + a ^ 3) ≤ Real.sqrt ((2 * (1 + M)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = 2 * (1 + M) := Real.sqrt_sq (by positivity)
  have hLsqrt : Real.sqrt L ≤ 1 + L := by
    calc Real.sqrt L ≤ Real.sqrt ((1 + L) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hL.le, sq_nonneg L])
      _ = 1 + L := Real.sqrt_sq (by positivity)
  have haL : a * L ≤ 2 * (1 + M) * L :=
    mul_le_mul_of_nonneg_right (hau.trans (by linarith)) hL.le
  have hpoly : 1 + a * L + Real.sqrt L ≤ 4 * (1 + M + L) ^ 2 := by
    nlinarith [haL, hLsqrt, hM.le, hL.le, sq_nonneg (M - L), sq_nonneg (M + L)]
  have hY0 : (0 : ℝ) ≤ 2 * (1 + a * L + Real.sqrt L) := by
    have h1 := mul_nonneg ha0 hL.le
    have h2 := Real.sqrt_nonneg L
    linarith
  have hAX'0 : (0 : ℝ) ≤ Real.sqrt C0 * (1 + M) * (2 * (1 + M)) :=
    mul_nonneg hA (by linarith [hM0])
  have h4 : (1 + M) ^ 2 ≤ (1 + M + L) ^ 2 := by
    apply pow_le_pow_left₀ hM0
    linarith [hL.le]
  have habsorb : Real.sqrt C0 * (1 + M) * Real.sqrt (1 + a ^ 3) * (2 * (1 + a * L + Real.sqrt L))
      ≤ 16 * Real.sqrt C0 * (1 + M + L) ^ 4 := by
    calc Real.sqrt C0 * (1 + M) * Real.sqrt (1 + a ^ 3) * (2 * (1 + a * L + Real.sqrt L))
        = (Real.sqrt C0 * (1 + M)) * Real.sqrt (1 + a ^ 3) * (2 * (1 + a * L + Real.sqrt L)) :=
          by ring
      _ ≤ (Real.sqrt C0 * (1 + M)) * (2 * (1 + M)) * (8 * (1 + M + L) ^ 2) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1a3sqrt hA)
          · linarith [hpoly]
          · exact hY0
          · exact hAX'0
      _ = 16 * Real.sqrt C0 * ((1 + M) ^ 2 * (1 + M + L) ^ 2) := by ring
      _ ≤ 16 * Real.sqrt C0 * ((1 + M + L) ^ 2 * (1 + M + L) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = 16 * Real.sqrt C0 * (1 + M + L) ^ 4 := by ring
  -- assemble
  calc HilbertSchmidt.hsENorm (HilbertSchmidt.kernelOperator (memLp_vKernel T a M hT hM ha)
          ∘L bPhiCLM L hL a)
      ≤ HilbertSchmidt.hsENorm (HilbertSchmidt.kernelOperator (memLp_vKernel T a M hT hM ha))
          * ‖bPhiCLM L hL a‖ₑ := hsENorm_comp_op_le _ _
    _ ≤ ENNReal.ofReal (Real.sqrt C0 * (1 + M) * Real.sqrt (1 + a ^ 3)
          * Real.exp (T * a ^ 2 - 2 * M * a))
          * ENNReal.ofReal (2 * (1 + a * L + Real.sqrt L) * Real.exp (L * a ^ 2)) :=
        mul_le_mul hVhs hB zero_le zero_le
    _ = ENNReal.ofReal ((Real.sqrt C0 * (1 + M) * Real.sqrt (1 + a ^ 3)
          * Real.exp (T * a ^ 2 - 2 * M * a))
          * (2 * (1 + a * L + Real.sqrt L) * Real.exp (L * a ^ 2))) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hM0)
          (Real.sqrt_nonneg _)) (Real.exp_pos _).le)]
    _ = ENNReal.ofReal ((Real.sqrt C0 * (1 + M) * Real.sqrt (1 + a ^ 3)
          * (2 * (1 + a * L + Real.sqrt L))) * Real.exp (L * a ^ 2 + T * a ^ 2 - a ^ 3)) := by
        congr 1
        have hsum : (T * a ^ 2 - 2 * M * a) + (L * a ^ 2) = L * a ^ 2 + T * a ^ 2 - a ^ 3 := by
          linarith [ha3]
        rw [show Real.sqrt C0 * (1 + M) * Real.sqrt (1 + a ^ 3)
              * Real.exp (T * a ^ 2 - 2 * M * a)
              * (2 * (1 + a * L + Real.sqrt L) * Real.exp (L * a ^ 2))
            = Real.sqrt C0 * (1 + M) * Real.sqrt (1 + a ^ 3)
              * (2 * (1 + a * L + Real.sqrt L))
              * (Real.exp (T * a ^ 2 - 2 * M * a) * Real.exp (L * a ^ 2)) from by ring]
        rw [← Real.exp_add, hsum]
    _ ≤ ENNReal.ofReal (16 * Real.sqrt C0 * (1 + M + L) ^ 4
          * Real.exp (L * a ^ 2 + T * a ^ 2 - a ^ 3)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right habsorb (Real.exp_pos _).le

end AiryConj
