/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.AiryKernel.ConjugateV
import Airy1GumbelContrib.AiryKernel.ConjugateW
import Airy1GumbelContrib.AiryKernel.TraceProduct
import Airy1GumbelContrib.TraceClass.FredholmOne
import Airy1GumbelContrib.Airy.AiryLeading

/-! # Trace expansion of the conjugated Airy operator

This module formalizes **Step 2** of the proof of the paper's sharp one-block tail: the trace
of the conjugated operator

  `Ã_{M,T} := V_{T,a} W_{T,a}`,     `a ≥ T + 1`

is evaluated as an explicit scalar expansion in terms of the Airy function.  We prove:

* **Operator assembly.**  `airyTildeOp M T a`: the composition of the two
  Hilbert–Schmidt kernel operators built from `vKernel` (the kernel `V_{T,a}`) and `wKernel`
  (the kernel `W_{T,a}`); the `MemLp` evidence is extracted from the square-integral bounds
  `vKernel_sq_integral_le` (the paper's Hilbert–Schmidt bound for `V`, the `V`-bound) and
  `wKernel_sq_integral_le` (the `W`-bound).  `isTraceClass_airyTildeOp` is the paper's
  trace-class conclusion for `Ã_{M,T}`, and `hsNorm_airyTilde_le` is the Hilbert–Schmidt
  product bound behind the paper's trace-norm bound (`‖Ã‖₁ ≤ ‖V‖₂‖W‖₂`; here on the HS level):
  `hsNorm (airyTildeOp M T a) ≤ C (1+M) √(1+a³) e^{a³/3 - 2Ma}` — note the exponent
  at `a² = 2M` is `a³/3 - a³ = -2a³/3 = -κ M^{3/2}`.

* **The trace as a kernel integral** (`trace_airyTilde_eq`): the trace equals the
  unweighted kernel double integral,
  `Tr Ã_{M,T} = ∫ x, ∫ z, Q_{M,T}(x,z) · (P_{-T}B₀)(z,x)`.  The exponential and `φ`
  weights cancel pointwise: `e^{-ax}e^{-az}φ(z) · φ(z)⁻¹e^{az}e^{ax} = 1`.

* **The scalar split** (`trace_airyTilde_eq_split`; the paper's split `Tr Ã = I + R` with
  its exact formulas for `I_{M,T}`, `R⁻` and `R⁺`):
  `Tr Ã_{M,T} = I_{M,T} + (4πT)^{-1/2} · R⁻_{M,T} + R⁺_{M,T}` with

    `I_{M,T} = ∫ s ≤ 2M, (2M - s) p_T(2M - s) g_T(s) ds`
    `R⁻_{M,T} = ∫ s ≤ 2M, G_T(2M - s) g_T(s) ds`
    `R⁺_{M,T} = (1/2) ∫ s > 2M, g_T(s) ds`

  where `g_T = backwardAiry`, `p_T = heatKernel` and `G_T = gaussianTail`.
  **Constant bookkeeping note.**  The contrib `gaussianTail T v = ∫_{d > v} e^{-d²/(4T)} dd`
  (Gaussian/MillsRatio) is the *unnormalized* Gaussian tail, while the paper's
  `P̄_T(v) = ∫_v^∞ p_T(d) dd` carries the heat-kernel normalization
  `(4πT)^{-1/2}`; hence the paper's `R⁻_{M,T}` equals `(4πT)^{-1/2} · rMinusMT M T`
  here (the factor `(4πT)^{-1/2}` is displayed explicitly in `trace_airyTilde_eq_split`),
  while `I_{M,T}` (`iMT`, the `p_T` kernel supplies `e^{-(2M-s)²/(4T)}/(2√(πT))`) and
  `R⁺_{M,T}` (`rPlusMT`) match verbatim.  The derivation is the paper's
  change of variables `s = x + z`, `d = x - z` with Jacobian `1/2`: on the reflected
  region `{x ≤ M, z ≤ M} = {s + |d| ≤ 2M}` the `d`-length `2(2M-s)` cancels the `1/2`;
  on the complement the two symmetric tails `|d| > 2M - s` (for `s ≤ 2M`) combine with
  the `1/2` to the single Gaussian tail, and on `{s > 2M}` the full `d`-integral of
  `p_T` is `1`, giving the `R⁺` factor `1/2`.

* **The exact trace formula** (`trace_airyTilde_eq_heat_exact`): writing
  `A = 2M` and extending the two half-line pieces to the full line via the
  convolution identities `heat_airy_conv_moment` and `heat_airy_conv_tail`,

    `Tr Ã_{M,T} = -2T · Ai'(2M) + ∫_{2M}^∞ Ai(u) du + errorMT M T`,

    `errorMT M T := ∫ b > 0, (b · p_T(b) - ∫_{[0,b]} p_T) · g_T(2M + b) db`
    (the paper's `ℰ_{M,T}`).

* **The `O_T` remainder bound** (`errorMT_abs_le`): for `0 < T` there
  is `C_T > 0` with, for all `M ≥ 1`, writing `a = √(2M)` (so `a² = 2M = A`),

    `|ℰ_{M,T}| ≤ C_T · M^{-3/4} · exp(-T·(2M) - (2/3)(2M)^{3/2})`.

  Route: the bracket `b p_T(b) - ∫_0^b p_T` lies in `[-1/2, 0]` (the heat kernel is
  decreasing on `[0, ∞)`, and `∫_0^b p_T ≤ ∫_0^∞ p_T = 1/2`); the Airy bound
  `airyAiReal_le` plus convexity of `u ↦ u^{3/2}` (tangent at `A`, slope
  `(3/2)√A = (3/2)a`) give
  `g_T(A + b) ≤ C₁ A^{-1/4} e^{-(2/3)A^{3/2} - TA} e^{-(a + T)b}`, and
  `∫_0^∞ e^{-(a+T)b} db = (a+T)^{-1} ≤ a^{-1}`, so the prefactor is
  `A^{-1/4} a^{-1} = (2M)^{-3/4} ≤ M^{-3/4}`.  The exponent
  `(2/3)(2M)^{3/2} = (4√2/3) M^{3/2} = κ M^{3/2}` is exactly the one in
  `ρ(M) = C_* M^{1/4} e^{-κ M^{3/2}}`, so that `errorMT = o(ρ(M)/M)` reduces to a
  direct calculation.

## References

J. Quastel and D. Remenik, *How flat is flat in random interface growth?*, Prop. 1.2;
the paper, proof of the sharp one-block tail, Step 2.
-/

namespace AiryConj

open MeasureTheory Real Set Filter
open scoped Topology BigOperators ENNReal NNReal
open HilbertSchmidt

/-! ## Operator assembly: `Ã_{M,T} = V_{T,a} W_{T,a}` -/

section OperatorAssembly

/-- Square-integrable real kernels are `L²` (the `MemLp`-from-`Integrable (·)²`
bridge used to feed the paper's `V`- and `W`-bounds into `kernelOperator`). -/
theorem memLp_of_sq_integrable {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (h2 : Integrable (fun p : ℝ × ℝ => (f p) ^ 2) (volume.prod volume)) :
    MemLp f 2 (volume.prod volume) :=
  (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr h2

/-- The `V`-kernel is `L²` on the plane for `0 < M`, `T + 1 ≤ a` (the paper's `V`-bound
integrability). -/
theorem vKernel_memLp (hT : 0 < T) {M a : ℝ} (hM : 0 < M) (ha : T + 1 ≤ a) :
    MemLp (vKernel T a M) 2 (volume.prod volume) := by
  obtain ⟨C, -, hC⟩ := vKernel_sq_integral_le T hT
  exact memLp_of_sq_integrable (measurable_vKernel T a M) (hC M a hM ha).1

/-- The `W`-kernel is `L²` on the plane for `0 < T`, `T + 1 ≤ a` (the paper's `W`-bound
integrability). -/
theorem memLp_wKernel (hT : 0 < T) {a : ℝ} (ha : T + 1 ≤ a) :
    MemLp (wKernel T a) 2 (volume.prod volume) := by
  obtain ⟨C, -, hC⟩ := wKernel_sq_integral_le
  exact memLp_of_sq_integrable (continuous_wKernel T a).measurable (hC T a hT ha).1

/-- The conjugated operator `Ã_{M,T} = V_{T,a} W_{T,a}` as a
composition of Hilbert–Schmidt kernel operators on `L²(ℝ)`. -/
noncomputable def airyTildeOp (M T a : ℝ) (hT : 0 < T) (hM : 0 < M) (ha : T + 1 ≤ a) :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  kernelOperator (vKernel_memLp hT hM ha) ∘L kernelOperator (memLp_wKernel hT ha)

/-- `Ã_{M,T}` is trace class: the composition of two
Hilbert–Schmidt operators. -/
theorem isTraceClass_airyTildeOp (hT : 0 < T) (hM : 0 < M) (ha : T + 1 ≤ a) :
    IsTraceClass (airyTildeOp M T a hT hM ha) :=
  ⟨kernelOperator (vKernel_memLp hT hM ha), kernelOperator (memLp_wKernel hT ha),
    isHilbertSchmidt_kernelOperator _, isHilbertSchmidt_kernelOperator _, rfl⟩

/-- The Hilbert–Schmidt norm of a real kernel operator is bounded by the `L²` norm of
its kernel: `‖T_K‖₂ ≤ √(∫ K²)`. -/
theorem hsNorm_kernelOperator_le_sqrt {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 (volume.prod volume))
    (hK2 : Integrable (fun p : ℝ × ℝ => (K p) ^ 2) (volume.prod volume)) :
    hsNorm (kernelOperator hK) ≤ Real.sqrt (∫ p : ℝ × ℝ, (K p) ^ 2 ∂(volume.prod volume)) := by
  have hnn : 0 ≤ ∫ p : ℝ × ℝ, (K p) ^ 2 ∂(volume.prod volume) :=
    integral_nonneg fun p => sq_nonneg _
  have heq : eLpNorm K 2 (volume.prod volume)
      = ENNReal.ofReal (∫ p : ℝ × ℝ, (K p) ^ 2 ∂(volume.prod volume)) ^ (1/2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hK.aestronglyMeasurable, show (2 : ℝ≥0∞).toReal = 2 by norm_num,
      show (1 / (2 : ℝ)) = 1 / 2 by norm_num]
    congr 1
    rw [ofReal_integral_eq_lintegral_ofReal hK2 (ae_of_all _ fun p => sq_nonneg _)]
    exact lintegral_congr fun p => by
      rw [enorm_rpow_two, enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  calc hsNorm (kernelOperator hK) = (hsENorm (kernelOperator hK)).toReal := rfl
    _ ≤ (eLpNorm K 2 (volume.prod volume)).toReal :=
        ENNReal.toReal_mono hK.eLpNorm_ne_top (hsENorm_kernelOperator_le hK)
    _ = Real.sqrt (∫ p : ℝ × ℝ, (K p) ^ 2 ∂(volume.prod volume)) := by
        rw [heq, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hnn, ← Real.sqrt_eq_rpow]

/-- **The Hilbert–Schmidt product bound** (behind Step 3 of the paper's proof): there is
`C_T > 0` such that for all `0 < M` and `a ≥ T + 1`,
`‖Ã_{M,T}‖₂ ≤ C_T (1+M) √(1+a³) e^{a³/3 - 2Ma}`.
At the paper's choice `a = √(2M)` (so `a² = 2M`) the exponent is
`a³/3 - 2Ma = a³/3 - a³ = -(2/3)a³ = -κ M^{3/2}`, the `e^{-2a³/3}` of
the trace-norm bound `‖Ã‖₁ ≤ ‖V‖₂ ‖W‖₂`. -/
theorem hsNorm_airyTilde_le (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ M a : ℝ, ∀ (hM : 0 < M) (ha : T + 1 ≤ a),
      hsNorm (airyTildeOp M T a hT hM ha)
        ≤ C * (1 + M) * Real.sqrt (1 + a ^ 3) * Real.exp (a ^ 3 / 3 - 2 * M * a) := by
  obtain ⟨CV, hCV, hV⟩ := vKernel_sq_integral_le T hT
  obtain ⟨CW, hCW, hW⟩ := wKernel_sq_integral_le
  refine ⟨Real.sqrt (CV * CW), Real.sqrt_pos_of_pos (mul_pos hCV hCW), fun M a hM ha => ?_⟩
  have hVb := (hV M a hM ha).2
  have hWb := (hW T a hT ha).2
  have hVint := (hV M a hM ha).1
  have hWint := (hW T a hT ha).1
  have ha0 : (0:ℝ) < a := by linarith [hT.le, ha]
  have h1a3 : (0:ℝ) < 1 + a ^ 3 := add_pos zero_lt_one (pow_pos ha0 3)
  have h1M : (0:ℝ) < 1 + M := by linarith [hM]
  have hnn1 : (0:ℝ) ≤ CV * (1 + M) ^ 2 * (1 + a ^ 3)
      * Real.exp (2 * T * a ^ 2 - 4 * M * a) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCV.le (pow_nonneg h1M.le 2)) h1a3.le)
      (Real.exp_pos _).le
  have hsV : hsNorm (kernelOperator (vKernel_memLp hT hM ha))
      ≤ Real.sqrt (CV * (1 + M) ^ 2 * (1 + a ^ 3) * Real.exp (2 * T * a ^ 2 - 4 * M * a)) :=
    (hsNorm_kernelOperator_le_sqrt _ hVint).trans (Real.sqrt_le_sqrt hVb)
  have hsW : hsNorm (kernelOperator (memLp_wKernel hT ha))
      ≤ Real.sqrt (CW * Real.exp ((2 / 3) * a ^ 3 - 2 * T * a ^ 2)) :=
    (hsNorm_kernelOperator_le_sqrt _ hWint).trans (Real.sqrt_le_sqrt hWb)
  have hmain := hsNorm_comp_le (isHilbertSchmidt_kernelOperator (vKernel_memLp hT hM ha))
    (isHilbertSchmidt_kernelOperator (memLp_wKernel hT ha))
  refine hmain.trans ((mul_le_mul hsV hsW (hsNorm_nonneg _) (Real.sqrt_nonneg _)).trans ?_)
  have hexp : Real.sqrt (CV * (1 + M) ^ 2 * (1 + a ^ 3) * Real.exp (2 * T * a ^ 2 - 4 * M * a))
        * Real.sqrt (CW * Real.exp ((2 / 3) * a ^ 3 - 2 * T * a ^ 2))
      = Real.sqrt (CV * CW) * (1 + M) * Real.sqrt (1 + a ^ 3)
        * Real.exp (a ^ 3 / 3 - 2 * M * a) := by
    rw [← Real.sqrt_mul hnn1]
    have hsplit : CV * (1 + M) ^ 2 * (1 + a ^ 3) * Real.exp (2 * T * a ^ 2 - 4 * M * a)
        * (CW * Real.exp ((2 / 3) * a ^ 3 - 2 * T * a ^ 2))
        = (CV * CW) * (1 + M) ^ 2 * (1 + a ^ 3) * (Real.exp (a ^ 3 / 3 - 2 * M * a)) ^ 2 := by
      have hz : Real.exp (2 * T * a ^ 2 - 4 * M * a) * Real.exp ((2 / 3) * a ^ 3 - 2 * T * a ^ 2)
          = (Real.exp (a ^ 3 / 3 - 2 * M * a)) ^ 2 := by
        rw [← Real.exp_add,
          show (Real.exp (a ^ 3 / 3 - 2 * M * a)) ^ 2
            = Real.exp (a ^ 3 / 3 - 2 * M * a) * Real.exp (a ^ 3 / 3 - 2 * M * a) from pow_two _,
          ← Real.exp_add]
        congr 1
        ring
      rw [show CV * (1 + M) ^ 2 * (1 + a ^ 3) * Real.exp (2 * T * a ^ 2 - 4 * M * a)
            * (CW * Real.exp ((2 / 3) * a ^ 3 - 2 * T * a ^ 2))
          = (CV * CW) * (1 + M) ^ 2 * (1 + a ^ 3)
            * (Real.exp (2 * T * a ^ 2 - 4 * M * a)
              * Real.exp ((2 / 3) * a ^ 3 - 2 * T * a ^ 2)) from by ring, hz]
    rw [hsplit, Real.sqrt_mul (by positivity : (0:ℝ) ≤ (CV * CW) * (1 + M) ^ 2 * (1 + a ^ 3)),
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ (CV * CW) * (1 + M) ^ 2),
      Real.sqrt_mul (mul_nonneg hCV.le hCW.le), Real.sqrt_sq h1M.le,
      Real.sqrt_sq (Real.exp_pos _).le]
  exact hexp.le

end OperatorAssembly

/-! ## The trace as the unweighted kernel double integral -/

section TraceQW

/-- **Pointwise weight cancellation**: the product of the two weighted
kernels at swapped arguments is the unweighted product; the `e^{±a·}` and `φ` factors
all cancel. -/
theorem vKernel_mul_wKernel_swap (T a M : ℝ) (x z : ℝ) :
    vKernel T a M (x, z) * wKernel T a (z, x)
      = qMT M T x z * backwardAiry T (z + x) := by
  have hφ : phiWeight z ≠ 0 := (phiWeight_pos z).ne'
  have e1 : Real.exp (-a * x) * Real.exp (a * x) = 1 := by
    rw [← Real.exp_add, show -a * x + a * x = 0 by ring, Real.exp_zero]
  have e2 : Real.exp (-a * z) * Real.exp (a * z) = 1 := by
    rw [← Real.exp_add, show -a * z + a * z = 0 by ring, Real.exp_zero]
  unfold vKernel wKernel
  calc (Real.exp (-a * x) * qMT M T x z * Real.exp (-a * z) * phiWeight z)
        * ((phiWeight z)⁻¹ * Real.exp (a * z) * backwardAiry T (z + x) * Real.exp (a * x))
      = qMT M T x z * backwardAiry T (z + x) * (Real.exp (-a * x) * Real.exp (a * x))
          * (Real.exp (-a * z) * Real.exp (a * z)) * (phiWeight z * (phiWeight z)⁻¹) := by
        ring
    _ = qMT M T x z * backwardAiry T (z + x) := by
        rw [e1, e2, mul_inv_cancel₀ hφ, mul_one, mul_one, mul_one]

/-- The trace integrand `Q_{M,T}(x,z) · (P_{-T}B₀)(z,x)` is integrable on the plane
(Cauchy–Schwarz through the `L²` factors). -/
theorem integrable_qMT_mul_backwardAiry (hT : 0 < T) (hM : 0 < M) (ha : T + 1 ≤ a) :
    Integrable (fun p : ℝ × ℝ => qMT M T p.1 p.2 * backwardAiry T (p.2 + p.1))
      (volume.prod volume) := by
  have h := MemLp.integrable_mul (memLp_kernelFlip (memLp_wKernel hT ha))
    (vKernel_memLp hT hM ha)
  convert h using 1
  ext ⟨x, z⟩
  show qMT M T (x, z).1 (x, z).2 * backwardAiry T ((x, z).2 + (x, z).1)
    = (kernelFlip (wKernel T a) * vKernel T a M) (x, z)
  rw [Pi.mul_apply]
  show qMT M T x z * backwardAiry T (z + x) = wKernel T a (z, x) * vKernel T a M (x, z)
  rw [mul_comm (wKernel T a (z, x)) (vKernel T a M (x, z)), vKernel_mul_wKernel_swap]

/-- **The trace as a kernel integral**: the trace of `Ã_{M,T}` is the unweighted
kernel double integral `∫ x, ∫ z, Q_{M,T}(x,z) · (P_{-T}B₀)(z,x) dx dz`. -/
theorem trace_airyTilde_eq (hT : 0 < T) (hM : 0 < M) (ha : T + 1 ≤ a) :
    trace (airyTildeOp M T a hT hM ha)
      = ∫ x : ℝ, ∫ z : ℝ, qMT M T x z * backwardAiry T (z + x) := by
  unfold airyTildeOp
  rw [trace_kernelOperator_comp (vKernel_memLp hT hM ha) (memLp_wKernel hT ha)]
  apply integral_congr_ae
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards with z
  exact vKernel_mul_wKernel_swap T a M x z

end TraceQW

/-! ## The normalized Gaussian tail `P̄_T` and its calculus

`heatKernelTail T v = ∫_v^∞ p_T(d) dd` is the paper's `P̄_T(v)`;
contrib's `gaussianTail T v = ∫_v^∞ e^{-d²/(4T)} dd` (Gaussian/MillsRatio) is the
unnormalized form, related by `heatKernelTail T v = (4πT)^{-1/2} · gaussianTail T v`
(`heatKernelTail_eq_const_mul_gaussianTail`). -/

section GaussianTailToolkit

/-- The normalized Gaussian tail `P̄_T(v) = ∫_v^∞ p_T(d) dd`. -/
noncomputable def heatKernelTail (T v : ℝ) : ℝ := ∫ d in Set.Ioi v, heatKernel T d

/-- The unnormalized Gaussian integrand has total mass `√(4πT)`. -/
theorem integral_exp_neg_sq_div (hT : 0 < T) :
    ∫ d : ℝ, Real.exp (- d^2 / (4 * T)) = Real.sqrt (4 * Real.pi * T) := by
  have h2 : (fun d : ℝ => Real.exp (- d^2 / (4 * T))) = fun d => Real.exp (-(4*T)⁻¹ * d^2) := by
    funext d
    congr 1
    ring
  rw [h2, integral_gaussian]
  congr 1
  rw [div_inv_eq_mul]
  ring

/-- `heatKernelTail T v = (4πT)^{-1/2} · gaussianTail T v`: the normalization bridge
between the paper's `P̄_T` and contrib's `gaussianTail`. -/
theorem heatKernelTail_eq_const_mul_gaussianTail (T : ℝ) (v : ℝ) :
    heatKernelTail T v = (4*Real.pi*T)^(-1/2:ℝ) * gaussianTail T v := by
  show ∫ d in Set.Ioi v, heatKernel T d
    = (4*Real.pi*T)^(-1/2:ℝ) * ∫ d in Set.Ioi v, Real.exp (- d^2 / (4 * T))
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro d _
  rfl

/-- The Gaussian tail is nonnegative. -/
theorem heatKernelTail_nonneg (hT : 0 < T) (v : ℝ) : 0 ≤ heatKernelTail T v :=
  setIntegral_nonneg measurableSet_Ioi fun d _ => heatKernel_nonneg hT d

/-- The Gaussian tail is at most the total mass `1`. -/
theorem heatKernelTail_le_one (hT : 0 < T) (v : ℝ) : heatKernelTail T v ≤ 1 := by
  calc heatKernelTail T v ≤ ∫ d : ℝ, heatKernel T d :=
        setIntegral_le_integral (integrable_heatKernel hT)
          (ae_of_all _ fun d => heatKernel_nonneg hT d)
    _ = 1 := integral_heatKernel hT

/-- The heat kernel is even. -/
theorem heatKernel_even (T v : ℝ) : heatKernel T (-v) = heatKernel T v := by
  unfold heatKernel
  rw [neg_sq]

/-- Reflection: the tail at `-v` is the `Iic`-mass at `v`. -/
theorem heatKernelTail_neg_eq_Iic (hT : 0 < T) (v : ℝ) :
    heatKernelTail T (-v) = ∫ d in Set.Iic v, heatKernel T d := by
  show ∫ d in Set.Ioi (-v), heatKernel T d = ∫ d in Set.Iic v, heatKernel T d
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Iic]
  have h := MeasureTheory.integral_neg_eq_self (μ := volume)
    ((Set.Ioi (-v)).indicator (heatKernel T))
  rw [← h]
  calc ∫ d : ℝ, (Set.Ioi (-v)).indicator (heatKernel T) (-d)
      = ∫ d : ℝ, (Set.Iio v).indicator (heatKernel T) d := by
        apply integral_congr_ae
        filter_upwards with d
        by_cases hd : d < v
        · have h1 : d ∈ Set.Iio v := Set.mem_Iio.mpr hd
          have h2 : (-d) ∈ Set.Ioi (-v) := Set.mem_Ioi.mpr (neg_lt_neg hd)
          rw [Set.indicator_of_mem h1 _, Set.indicator_of_mem h2 _]
          exact heatKernel_even T d
        · have h1 : d ∉ Set.Iio v := by simpa using hd
          have h2 : (-d) ∉ Set.Ioi (-v) :=
            not_lt.mpr (neg_le_neg (le_of_not_gt hd))
          rw [Set.indicator_of_notMem h1 _, Set.indicator_of_notMem h2 _]
    _ = ∫ d : ℝ, (Set.Iic v).indicator (heatKernel T) d := by
        rw [MeasureTheory.integral_indicator measurableSet_Iio,
          MeasureTheory.integral_indicator measurableSet_Iic]
        exact setIntegral_congr_set MeasureTheory.Iio_ae_eq_Iic

/-- The Gaussian tails at `v` and `-v` sum to the total mass `1`
(evenness of the heat kernel). -/
theorem heatKernelTail_add_neg (hT : 0 < T) (v : ℝ) :
    heatKernelTail T v + heatKernelTail T (-v) = 1 := by
  rw [heatKernelTail_neg_eq_Iic hT v]
  have h := MeasureTheory.integral_add_compl (μ := volume) (f := heatKernel T)
    (s := Set.Iic v) measurableSet_Iic (integrable_heatKernel hT)
  rw [Set.compl_Iic, integral_heatKernel hT] at h
  unfold heatKernelTail
  rw [add_comm]
  exact h

/-- The half-line mass of the heat kernel is `1/2`. -/
theorem heatKernelTail_zero (hT : 0 < T) : heatKernelTail T 0 = 1/2 := by
  have h := heatKernelTail_add_neg hT 0
  rw [neg_zero] at h
  linarith [h]

/-- The `Iic`-mass at `b`: `∫_{(-∞, b]} p_T = 1 - P̄_T(b)`. -/
theorem integral_Iic_heatKernel (hT : 0 < T) (b : ℝ) :
    ∫ d in Set.Iic b, heatKernel T d = 1 - heatKernelTail T b := by
  have h := MeasureTheory.integral_add_compl (μ := volume) (f := heatKernel T)
    (s := Set.Iic b) measurableSet_Iic (integrable_heatKernel hT)
  rw [Set.compl_Iic, integral_heatKernel hT] at h
  unfold heatKernelTail
  linarith [h]

/-- The `Ioc`-mass of the heat kernel between `0` and `b`, for `0 ≤ b`. -/
theorem integral_Ioc_heatKernel (hT : 0 < T) {b : ℝ} (hb : 0 ≤ b) :
    ∫ d in Set.Ioc 0 b, heatKernel T d = 1/2 - heatKernelTail T b := by
  have hsplit : ∫ d in Set.Iic b, heatKernel T d
      = (∫ d in Set.Iic 0, heatKernel T d) + (∫ d in Set.Ioc 0 b, heatKernel T d) := by
    have hunion : Set.Iic (0 : ℝ) ∪ Set.Ioc 0 b = Set.Iic b := Set.Iic_union_Ioc_eq_Iic hb
    rw [← hunion]
    exact setIntegral_union (Set.disjoint_left.mpr
        fun (x : ℝ) (hx0 : x ∈ Set.Iic (0:ℝ)) (hx1 : x ∈ Set.Ioc 0 b) =>
          (not_lt_of_ge (Set.mem_Iic.mp hx0)) (Set.mem_Ioc.mp hx1).1)
      measurableSet_Ioc (integrable_heatKernel hT).integrableOn
        (integrable_heatKernel hT).integrableOn
  have h0 : ∫ d in Set.Iic 0, heatKernel T d = 1/2 := by
    rw [← heatKernelTail_neg_eq_Iic hT 0, neg_zero, heatKernelTail_zero hT]
  linarith [hsplit, integral_Iic_heatKernel hT b, h0]

/-- The `Icc`-mass of the heat kernel: for `0 ≤ b`,
`∫_{[0, b]} p_T = 1/2 - P̄_T(b)`. -/
theorem integral_Icc_heatKernel (hT : 0 < T) {b : ℝ} (hb : 0 ≤ b) :
    ∫ d in Set.Icc 0 b, heatKernel T d = 1/2 - heatKernelTail T b := by
  rw [show (∫ d in Set.Icc 0 b, heatKernel T d) = ∫ d in Set.Ioc 0 b, heatKernel T d from
    setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc.symm]
  exact integral_Ioc_heatKernel hT hb

/-- The tail at a negative argument: for `0 ≤ b`,
`P̄_T(-b) = 1/2 + ∫_{[0,b]} p_T` (evenness of the heat kernel). -/
theorem heatKernelTail_neg_eq (hT : 0 < T) {b : ℝ} (hb : 0 ≤ b) :
    heatKernelTail T (-b) = 1/2 + ∫ d in Set.Icc 0 b, heatKernel T d := by
  rw [integral_Icc_heatKernel hT hb, heatKernelTail_neg_eq_Iic hT b, integral_Iic_heatKernel hT b]
  ring


/-- The normalized Gaussian tail is continuous (dominated convergence of the
indicator functions). -/
theorem continuous_heatKernelTail (hT : 0 < T) : Continuous (heatKernelTail T) := by
  have hform : heatKernelTail T
      = fun v => ∫ d : ℝ, (Set.Ioi v).indicator (heatKernel T) d :=
    funext fun v => (MeasureTheory.integral_indicator measurableSet_Ioi).symm
  rw [hform, continuous_iff_continuousAt]
  intro v₀
  refine tendsto_integral_filter_of_dominated_convergence (heatKernel T)
    (Eventually.of_forall fun v =>
      ((continuous_heatKernel T).aestronglyMeasurable.indicator measurableSet_Ioi))
    (Eventually.of_forall fun v => Eventually.of_forall fun d =>
      (norm_indicator_le_norm_self _ _).trans_eq
        ((Real.norm_eq_abs _).trans (abs_of_nonneg (heatKernel_nonneg hT d))))
    (integrable_heatKernel hT) ?_
  filter_upwards [mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton v₀)]
    with d hd
  have hd' : d ≠ v₀ := by
    rintro rfl
    exact hd (Set.mem_singleton _)
  by_cases hd0 : v₀ < d
  · have htarget : (Set.Ioi v₀).indicator (heatKernel T) d = heatKernel T d :=
      Set.indicator_of_mem (Set.mem_Ioi.mpr hd0) _
    rw [htarget]
    apply Tendsto.congr' _ (tendsto_const_nhds (x := heatKernel T d))
    filter_upwards [isOpen_Iio.mem_nhds hd0] with v hv
    rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hv) _]
  · have hd0' : d < v₀ := lt_of_le_of_ne (le_of_not_gt hd0) hd'
    have htarget : (Set.Ioi v₀).indicator (heatKernel T) d = 0 :=
      Set.indicator_of_notMem (by simp only [Set.mem_Ioi]; linarith) _
    rw [htarget]
    apply Tendsto.congr' _ (tendsto_const_nhds (x := (0 : ℝ)))
    filter_upwards [isOpen_Ioi.mem_nhds hd0'] with v hv
    have hv' : d < v := hv
    rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi]; linarith) _]

/-- The normalized Gaussian tail is measurable. -/
theorem measurable_heatKernelTail (hT : 0 < T) : Measurable (heatKernelTail T) :=
  (continuous_heatKernelTail hT).measurable

/-- **Global Gaussian-tail bound** (used to dominate the `s ≤ 2M` pieces):
`P̄_T(w) ≤ C_T · e^{-(max w 0)²/(4T)}` for all `w`, with an explicit positive
`C_T = e^{1/(4T)} + 2T·(4πT)^{-1/2}`.  For `w ≤ 1` the tail is at most the total mass
`1` while the Gaussian factor is at least `e^{-1/(4T)}`; for `1 ≤ w` this is the Mills
bound `gaussianTail_le` times the normalization. -/
theorem heatKernelTail_le_exp_max_sq (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ,
      heatKernelTail T w ≤ C * Real.exp (-(max w 0)^2 / (4 * T)) := by
  have h4πT : (0:ℝ) < 4 * Real.pi * T := by positivity
  refine ⟨Real.exp (1/(4*T)) + (4*Real.pi*T)^(-1/2:ℝ) * (2*T), by positivity, fun w => ?_⟩
  rcases le_total w 1 with hw | hw
  · have hexp : Real.exp (-(1/(4*T))) ≤ Real.exp (-(max w 0)^2 / (4 * T)) := by
      apply Real.exp_le_exp.mpr
      have h2 : (max w 0)^2 ≤ 1 := by
        rcases le_total w 0 with hw0 | hw0
        · rw [max_eq_right hw0]; norm_num
        · rw [max_eq_left hw0]; nlinarith [hw, hw0]
      have h3 : (max w 0)^2 / (4 * T) ≤ 1 / (4 * T) :=
        (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 4 * T)).mpr h2
      rw [show -(1/(4*T)) = (-1)/(4*T) by rw [neg_div]]
      exact (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 4*T)).mpr
        (by linarith [h2])
    calc heatKernelTail T w ≤ 1 := heatKernelTail_le_one hT w
      _ = Real.exp (1/(4*T)) * Real.exp (-(1/(4*T))) := by
          rw [← Real.exp_add]; simp
      _ ≤ Real.exp (1/(4*T)) * Real.exp (-(max w 0)^2 / (4 * T)) :=
          mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ ≤ (Real.exp (1/(4*T)) + (4*Real.pi*T)^(-1/2:ℝ) * (2*T))
          * Real.exp (-(max w 0)^2 / (4 * T)) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
            (Real.exp_pos _).le
  · have hw0 : (0:ℝ) < w := by linarith
    have hG := gaussianTail_le hT hw0
    have hnorm := heatKernelTail_eq_const_mul_gaussianTail T w
    have hmax : max w 0 = w := max_eq_left hw0.le
    rw [hnorm, hmax]
    have h2Tw : (2:ℝ)*T/w ≤ 2*T := div_le_self (by positivity) hw
    calc (4*Real.pi*T)^(-1/2:ℝ) * gaussianTail T w
        ≤ (4*Real.pi*T)^(-1/2:ℝ) * ((2*T/w) * Real.exp (-w^2/(4*T))) :=
          mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg h4πT.le _)
      _ ≤ (4*Real.pi*T)^(-1/2:ℝ) * ((2*T) * Real.exp (-w^2/(4*T))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h2Tw (Real.exp_pos _).le)
            (Real.rpow_nonneg h4πT.le _)
      _ = (4*Real.pi*T)^(-1/2:ℝ) * (2*T) * Real.exp (-w^2/(4*T)) := by ring
      _ ≤ (Real.exp (1/(4*T)) + (4*Real.pi*T)^(-1/2:ℝ) * (2*T)) * Real.exp (-w^2/(4*T)) := by
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Real.exp_pos _).le)
            (Real.exp_pos _).le

end GaussianTailToolkit

/-! ## One-dimensional substitution helpers

Affine changes of variables in half-line set integrals; all are unconditional
(measure-theoretic translation/dilation invariance, valid even as junk-value
identities). -/

section SubstitutionHelpers

/-- Shift of an `Iic` set integral: `∫ z ≤ c, f (x + z) dz = ∫ s ≤ c + x, f s ds`. -/
theorem integral_Iic_comp_add (c x : ℝ) (f : ℝ → ℝ) :
    ∫ z in Set.Iic c, f (x + z) = ∫ s in Set.Iic (c + x), f s := by
  rw [← MeasureTheory.integral_indicator measurableSet_Iic,
    ← MeasureTheory.integral_indicator measurableSet_Iic]
  have h := MeasureTheory.integral_add_right_eq_self (μ := volume)
    ((Set.Iic (c + x)).indicator f) x
  rw [← h]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ≤ c
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hz) _,
      Set.indicator_of_mem (Set.mem_Iic.mpr (by linarith : z + x ≤ c + x)) _]
    congr 1
    ring
  · rw [Set.indicator_of_notMem (by simpa using hz) _,
      Set.indicator_of_notMem (by simpa using hz : ¬ z + x ≤ c + x) _]

/-- Shift of an `Ioi` set integral: `∫ z > c, f (x + z) dz = ∫ s > c + x, f s ds`. -/
theorem integral_Ioi_comp_add (c x : ℝ) (f : ℝ → ℝ) :
    ∫ z in Set.Ioi c, f (x + z) = ∫ s in Set.Ioi (c + x), f s := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi]
  have h := MeasureTheory.integral_add_right_eq_self (μ := volume)
    ((Set.Ioi (c + x)).indicator f) x
  rw [← h]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : c < z
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hz) _,
      Set.indicator_of_mem (Set.mem_Ioi.mpr (by linarith : c + x < z + x)) _]
    congr 1
    ring
  · rw [Set.indicator_of_notMem (by simpa using hz) _,
      Set.indicator_of_notMem (by simpa using hz : ¬ c + x < z + x) _]

/-- Dilation-and-shift of an `Ioi` set integral:
`∫ x > c, f (2x - s) dx = (1/2) ∫ v > 2c - s, f v dv`. -/
theorem integral_Ioi_comp_two_mul_sub (c s : ℝ) (f : ℝ → ℝ) :
    ∫ x in Set.Ioi c, f (2*x - s) = (1/2) * ∫ v in Set.Ioi (2*c - s), f v := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  have hstep1 : (fun x : ℝ => (Set.Ioi c).indicator (fun x => f (2*x - s)) x)
      = fun x => (Set.Ioi (2*c)).indicator (fun u => f (u - s)) (2 * x) := by
    funext x
    show (Set.Ioi c).indicator (fun x => f (2*x - s)) x
        = (Set.Ioi (2*c)).indicator (fun u => f (u - s)) (2*x)
    by_cases hx : c < x
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hx) _,
        Set.indicator_of_mem (Set.mem_Ioi.mpr (by linarith : 2*c < 2*x)) _]
    · rw [Set.indicator_of_notMem (by simpa using hx) _,
        Set.indicator_of_notMem (by simpa using hx : ¬ 2*c < 2*x) _]
  rw [hstep1, MeasureTheory.Measure.integral_comp_mul_left _ (2 : ℝ)]
  have hshift : (∫ u : ℝ, (Set.Ioi (2*c)).indicator (fun u => f (u - s)) u)
      = ∫ v in Set.Ioi (2*c - s), f v := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
      ((Set.Ioi (2*c - s)).indicator f) s
    rw [← h]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : 2*c < u
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hu) _,
        Set.indicator_of_mem (Set.mem_Ioi.mpr (by linarith : 2*c - s < u - s)) _]
    · rw [Set.indicator_of_notMem (by simpa using hu) _,
        Set.indicator_of_notMem (by simpa using hu : ¬ 2*c - s < u - s) _]
  rw [hshift, show |(2:ℝ)⁻¹| = 1/2 by norm_num, smul_eq_mul]

/-- Dilation-and-shift of an `Iic` set integral:
`∫ x ≤ c, f (2x - s) dx = (1/2) ∫ v ≤ 2c - s, f v dv`. -/
theorem integral_Iic_comp_two_mul_sub (c s : ℝ) (f : ℝ → ℝ) :
    ∫ x in Set.Iic c, f (2*x - s) = (1/2) * ∫ v in Set.Iic (2*c - s), f v := by
  rw [← MeasureTheory.integral_indicator measurableSet_Iic]
  have hstep1 : (fun x : ℝ => (Set.Iic c).indicator (fun x => f (2*x - s)) x)
      = fun x => (Set.Iic (2*c)).indicator (fun u => f (u - s)) (2 * x) := by
    funext x
    show (Set.Iic c).indicator (fun x => f (2*x - s)) x
        = (Set.Iic (2*c)).indicator (fun u => f (u - s)) (2*x)
    by_cases hx : x ≤ c
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx) _,
        Set.indicator_of_mem (Set.mem_Iic.mpr (by linarith : 2*x ≤ 2*c)) _]
    · rw [Set.indicator_of_notMem (by simpa using hx) _,
        Set.indicator_of_notMem (by simpa using hx : ¬ 2*x ≤ 2*c) _]
  rw [hstep1, MeasureTheory.Measure.integral_comp_mul_left _ (2 : ℝ)]
  have hshift : (∫ u : ℝ, (Set.Iic (2*c)).indicator (fun u => f (u - s)) u)
      = ∫ v in Set.Iic (2*c - s), f v := by
    rw [← MeasureTheory.integral_indicator measurableSet_Iic]
    have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
      ((Set.Iic (2*c - s)).indicator f) s
    rw [← h]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ≤ 2*c
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hu) _,
        Set.indicator_of_mem (Set.mem_Iic.mpr (by linarith : u - s ≤ 2*c - s)) _]
    · rw [Set.indicator_of_notMem (by simpa using hu) _,
        Set.indicator_of_notMem (by simpa using hu : ¬ u - s ≤ 2*c - s) _]
  rw [hshift, show |(2:ℝ)⁻¹| = 1/2 by norm_num, smul_eq_mul]

end SubstitutionHelpers
/-! ## The master envelope and the region-swap lemmas -/

section RegionSwaps

/-- The mixed exponential×Gaussian-half-line envelope
`s ↦ e^{-Ts} · e^{-(max (K - s) 0)²/(4T)}` is integrable on `ℝ`: the Gaussian decay
kills the `e^{-Ts}` growth on `(-∞, K]`, and `e^{-Ts}` decays on `[K, ∞)`. -/
theorem integrable_exp_neg_mul_exp_max_sq (hT : 0 < T) (K : ℝ) :
    Integrable (fun s : ℝ => Real.exp (-T * s) * Real.exp (-(max (K - s) 0)^2 / (4 * T)))
      volume := by
  have hG : Integrable (fun s : ℝ => Real.exp (-(s - (K - 2*T^2))^2 / (4 * T))) volume := by
    have h1 : Integrable (fun s : ℝ => Real.exp (-(4*T)⁻¹ * s^2)) volume :=
      integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < (4*T)⁻¹)
    have h2 := h1.comp_sub_right (K - 2*T^2)
    convert h2 using 1
    ext s
    congr 1
    field_simp
  have hL : IntegrableOn (fun s : ℝ => Real.exp (-T * s)
        * Real.exp (-(max (K - s) 0)^2 / (4 * T))) (Set.Iic K) volume := by
    refine IntegrableOn.congr_fun_ae
      ((hG.const_mul (Real.exp (T^3 - T*K))).integrableOn)
      (ae_restrict_of_forall_mem measurableSet_Iic fun s (hs : s ∈ Set.Iic K) => ?_)
    show Real.exp (T^3 - T*K) * Real.exp (-(s - (K - 2*T^2))^2 / (4 * T))
      = Real.exp (-T * s) * Real.exp (-(max (K - s) 0)^2 / (4 * T))
    rw [show max (K - s) 0 = K - s from max_eq_left (by linarith [Set.mem_Iic.mp hs]),
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp [hT.ne']
    ring
  have hR : IntegrableOn (fun s : ℝ => Real.exp (-T * s)
        * Real.exp (-(max (K - s) 0)^2 / (4 * T))) (Set.Ioi K) volume := by
    refine IntegrableOn.congr_fun_ae (exp_neg_integrableOn_Ioi K hT)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s (hs : s ∈ Set.Ioi K) => ?_)
    show Real.exp (-T * s)
      = Real.exp (-T * s) * Real.exp (-(max (K - s) 0)^2 / (4 * T))
    rw [show max (K - s) 0 = 0 from max_eq_right (by linarith [Set.mem_Ioi.mp hs])]
    simp
  have hU : Set.Iic K ∪ Set.Ioi K = (Set.univ : Set ℝ) := by
    ext s
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
    exact le_or_gt s K
  rw [← integrableOn_univ, ← hU]
  exact hL.union hR

/-- Measurability of the swap region `{(x, s) : x ≤ M, s ≤ M + x}`. -/
theorem measurableSet_swapRegionIic (M : ℝ) :
    MeasurableSet {p : ℝ × ℝ | p.1 ≤ M ∧ p.2 ≤ M + p.1} := by
  have e : {p : ℝ × ℝ | p.1 ≤ M ∧ p.2 ≤ M + p.1}
      = {p : ℝ × ℝ | p.1 ≤ M} ∩ {p : ℝ × ℝ | p.2 - p.1 ≤ M} := by
    ext ⟨x, s⟩
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
  rw [e]
  exact (measurableSet_Iic.preimage measurable_fst).inter
    (measurableSet_Iic.preimage (measurable_snd.sub measurable_fst))

/-- Measurability of the region `{(u, s) : M < u, s ≤ M + u}`. -/
theorem measurableSet_swapRegionIoi (M : ℝ) :
    MeasurableSet {p : ℝ × ℝ | M < p.1 ∧ p.2 ≤ M + p.1} := by
  have e : {p : ℝ × ℝ | M < p.1 ∧ p.2 ≤ M + p.1}
      = {p : ℝ × ℝ | M < p.1} ∩ {p : ℝ × ℝ | p.2 - p.1 ≤ M} := by
    ext ⟨x, s⟩
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
  rw [e]
  exact (measurableSet_Ioi.preimage measurable_fst).inter
    (measurableSet_Iic.preimage (measurable_snd.sub measurable_fst))

/-- **The reflected-region swap** (the formula for `I_{M,T}`): for `H` with the
`(1 + |s|)`-weighted envelope integrable on `(-∞, 2M]`,

  `∫ x ≤ M, ∫ s ≤ M + x, H s ds dx = ∫ s ≤ 2M, (2M - s) · H s ds`.

This is the change of variables `s = x + z`, `d = x - z` on the reflected region
`{x ≤ M, z ≤ M}`: for fixed `s` the `x`-section is `[s - M, M]`, of length `2M - s`. -/
theorem integral_Iic_Iic_add_swap (M : ℝ) (H : ℝ → ℝ) (hHm : Measurable H)
    (hH : IntegrableOn (fun s => (1 + |s|) * H s) (Set.Iic (2 * M)) volume) :
    (∫ x in Set.Iic M, ∫ s in Set.Iic (M + x), H s)
      = ∫ s in Set.Iic (2 * M), (2 * M - s) * H s := by
  set F : ℝ × ℝ → ℝ := fun p => if p.1 ≤ M ∧ p.2 ≤ M + p.1 then H p.2 else 0 with hFdef
  have hFmeas : Measurable F := Measurable.ite (measurableSet_swapRegionIic M)
    (hHm.comp measurable_snd) measurable_const
  -- the pointwise identification with the `Icc`-indicator of the `x`-section
  have hpt : ∀ s : ℝ, (fun x => F (x, s))
      = (Set.Icc (s - M) M).indicator (fun _ => H s) := by
    intro s
    funext x
    show (if x ≤ M ∧ s ≤ M + x then H s else 0)
        = (Set.Icc (s - M) M).indicator (fun _ => H s) x
    by_cases hx : x ≤ M ∧ s ≤ M + x
    · rw [ite_eq_left hx, Set.indicator_of_mem (show x ∈ Set.Icc (s - M) M from
        ⟨by linarith [hx.2], hx.1⟩) _]
    · rw [ite_eq_right hx, Set.indicator_of_notMem (show x ∉ Set.Icc (s - M) M from
        fun hmem => hx ⟨hmem.2, by linarith [hmem.1]⟩) _]
  -- the inner evaluation: for fixed `s`, the `x`-section is `[s - M, M]`
  have hinner : ∀ s : ℝ, (∫ x : ℝ, F (x, s))
      = (if s ≤ 2 * M then (2 * M - s) else 0) * H s := by
    intro s
    rw [hpt s, MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.setIntegral_const, smul_eq_mul]
    have hvol : Measure.real volume (Set.Icc (s - M) M)
        = if s ≤ 2 * M then (2 * M - s) else 0 := by
      show (volume (Set.Icc (s - M) M)).toReal = _
      rw [Real.volume_Icc]
      by_cases hs : s ≤ 2 * M
      · rw [ite_eq_left hs, ENNReal.toReal_ofReal (by linarith)]
        ring
      · rw [ite_eq_right hs, ENNReal.ofReal_of_nonpos (by linarith), ENNReal.toReal_zero]
    rw [hvol]
  -- integrability of `F` on the plane, via Tonelli in the `s`-then-`x` order
  have hFint : Integrable F (volume.prod volume) := by
    have hsec : ∀ᵐ s : ℝ, Integrable (fun x => F (x, s)) volume := by
      filter_upwards with s
      rw [hpt s]
      exact (integrableOn_const (C := H s)
        (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
        measurableSet_Icc
    have hnorm_int : Integrable (fun s : ℝ => ∫ x : ℝ, ‖F (x, s)‖) volume := by
      have hbound : ∀ s : ℝ, (∫ x : ℝ, ‖F (x, s)‖)
          = (if s ≤ 2 * M then (2 * M - s) else 0) * |H s| := by
        intro s
        have hptn : (fun x => ‖F (x, s)‖)
            = (Set.Icc (s - M) M).indicator (fun _ => |H s|) := by
          funext x
          show ‖(if x ≤ M ∧ s ≤ M + x then H s else 0)‖
              = (Set.Icc (s - M) M).indicator (fun _ => |H s|) x
          by_cases hx : x ≤ M ∧ s ≤ M + x
          · rw [ite_eq_left hx, Set.indicator_of_mem (show x ∈ Set.Icc (s - M) M from
              ⟨by linarith [hx.2], hx.1⟩) _, Real.norm_eq_abs]
          · rw [ite_eq_right hx, Set.indicator_of_notMem (show x ∉ Set.Icc (s - M) M from
              fun hmem => hx ⟨hmem.2, by linarith [hmem.1]⟩) _, Real.norm_eq_abs, abs_zero]
        rw [hptn, MeasureTheory.integral_indicator measurableSet_Icc,
          MeasureTheory.setIntegral_const, smul_eq_mul]
        have hvol : Measure.real volume (Set.Icc (s - M) M)
            = if s ≤ 2 * M then (2 * M - s) else 0 := by
          show (volume (Set.Icc (s - M) M)).toReal = _
          rw [Real.volume_Icc]
          by_cases hs : s ≤ 2 * M
          · rw [ite_eq_left hs, ENNReal.toReal_ofReal (by linarith)]
            ring
          · rw [ite_eq_right hs, ENNReal.ofReal_of_nonpos (by linarith), ENNReal.toReal_zero]
        rw [hvol]
      have hmeas : AEStronglyMeasurable (fun s : ℝ => ∫ x : ℝ, ‖F (x, s)‖) volume := by
        have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖F p‖) (volume.prod volume) :=
          hFmeas.norm.aestronglyMeasurable
        exact (h1.prod_swap).integral_prod_right'
      have hle : ∀ᵐ s : ℝ, ‖(∫ x : ℝ, ‖F (x, s)‖)‖
          ≤ (Set.Iic (2 * M)).indicator (fun s => (1 + 2 * |M|) * (1 + |s|) * |H s|) s := by
        filter_upwards with s
        rw [hbound s]
        by_cases hs : s ≤ 2 * M
        · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hs) _, ite_eq_left hs]
          rw [Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * M - s) (abs_nonneg _))]
          have hlen : (2:ℝ) * M - s ≤ (1 + 2 * |M|) * (1 + |s|) := by
            have h1 : 2 * M - s ≤ 2 * M + |s| := by linarith [neg_abs_le s, abs_nonneg s]
            have h2 : 2 * M + |s| ≤ (1 + 2 * |M|) * (1 + |s|) := by
              nlinarith [abs_nonneg M, abs_nonneg s, le_abs_self M,
                mul_nonneg (abs_nonneg M) (abs_nonneg s)]
            linarith
          exact mul_le_mul_of_nonneg_right hlen (abs_nonneg _)
        · rw [Set.indicator_of_notMem (by simpa using hs) _, ite_eq_right hs]
          simp
      have hhs : Integrable ((Set.Iic (2 * M)).indicator (fun s => (1 + 2 * |M|) * (1 + |s|)
          * |H s|)) volume := by
        rw [MeasureTheory.integrable_indicator_iff measurableSet_Iic]
        have habs : IntegrableOn (fun s => (1 + |s|) * |H s|) (Set.Iic (2 * M)) volume := by
          have h1 : IntegrableOn (fun s => ‖(1 + |s|) * H s‖) (Set.Iic (2 * M)) volume :=
            (integrable_norm_iff (hH.aestronglyMeasurable)).mpr hH
          refine h1.congr_fun_ae (ae_restrict_of_forall_mem measurableSet_Iic fun s _ => ?_)
          show ‖(1 + |s|) * H s‖ = (1 + |s|) * |H s|
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + |s|)]
        exact IntegrableOn.congr_fun_ae (habs.const_mul (1 + 2 * |M|))
          (ae_restrict_of_forall_mem measurableSet_Iic fun s _ => by ring)
      exact hhs.mono' hmeas hle
    exact (integrable_prod_iff' hFmeas.aestronglyMeasurable).mpr ⟨hsec, hnorm_int⟩
  -- the two iterated forms of the plane integral
  have hLHS : (∫ x in Set.Iic M, ∫ s in Set.Iic (M + x), H s)
      = ∫ x : ℝ, ∫ s : ℝ, F (x, s) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Iic]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ≤ M
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx) _]
      rw [← MeasureTheory.integral_indicator measurableSet_Iic]
      apply integral_congr_ae
      filter_upwards with s
      by_cases hs : s ≤ M + x
      · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hs) _]
        show H s = (if x ≤ M ∧ s ≤ M + x then H s else 0)
        rw [ite_eq_left ⟨hx, hs⟩]
      · rw [Set.indicator_of_notMem (by simpa using hs) _]
        show (0 : ℝ) = (if x ≤ M ∧ s ≤ M + x then H s else 0)
        rw [ite_eq_right (fun h => hs h.2)]
    · rw [Set.indicator_of_notMem (by simpa using hx) _]
      show (0 : ℝ) = ∫ s : ℝ, F (x, s)
      rw [show (fun s => F (x, s)) = fun _ => (0 : ℝ) from funext fun s => by
        show (if x ≤ M ∧ s ≤ M + x then H s else 0) = (0 : ℝ)
        rw [ite_eq_right (fun h => hx h.1)]]
      rw [integral_zero]
  have hswap : (∫ x : ℝ, ∫ s : ℝ, F (x, s)) = ∫ s : ℝ, ∫ x : ℝ, F (x, s) :=
    MeasureTheory.integral_integral_swap (μ := volume) (ν := volume)
      (f := fun x s => F (x, s)) hFint
  have hRHS : (∫ s : ℝ, ∫ x : ℝ, F (x, s)) = ∫ s in Set.Iic (2 * M), (2 * M - s) * H s := by
    rw [integral_congr_ae (Eventually.of_forall fun s => hinner s)]
    rw [show (fun s : ℝ => (if s ≤ 2 * M then (2 * M - s) else 0) * H s)
        = (Set.Iic (2 * M)).indicator (fun s => (2 * M - s) * H s) from
      funext fun s => by
        by_cases hs : s ≤ 2 * M
        · rw [ite_eq_left hs, Set.indicator_of_mem (Set.mem_Iic.mpr hs) _]
        · rw [ite_eq_right hs, Set.indicator_of_notMem (by simpa using hs) _, zero_mul]]
    exact MeasureTheory.integral_indicator measurableSet_Iic
  rw [hLHS, hswap, hRHS]

/-- **The complementary-region swap**: for `K` whose region-indicator is
plane-integrable, the iterated integral over `{u > M, s ≤ M + u}` swaps to `s` first,
with the `u`-section `{u > max M (s − M)}`. -/
theorem integral_Ioi_Iic_region_swap (M : ℝ) (K : ℝ × ℝ → ℝ)
    (hK : Integrable (fun p : ℝ × ℝ => if M < p.1 ∧ p.2 ≤ M + p.1 then K p else 0)
      (volume.prod volume)) :
    (∫ u in Set.Ioi M, ∫ s in Set.Iic (M + u), K (u, s))
      = ∫ s : ℝ, ∫ u in Set.Ioi (max M (s - M)), K (u, s) := by
  set F : ℝ × ℝ → ℝ := fun p => if M < p.1 ∧ p.2 ≤ M + p.1 then K p else 0 with hFdef
  have hLHS : (∫ u in Set.Ioi M, ∫ s in Set.Iic (M + u), K (u, s))
      = ∫ u : ℝ, ∫ s : ℝ, F (u, s) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : M < u
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hu) _]
      rw [← MeasureTheory.integral_indicator measurableSet_Iic]
      apply integral_congr_ae
      filter_upwards with s
      by_cases hs : s ≤ M + u
      · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hs) _]
        show K (u, s) = (if M < u ∧ s ≤ M + u then K (u, s) else 0)
        rw [ite_eq_left ⟨hu, hs⟩]
      · rw [Set.indicator_of_notMem (by simpa using hs) _]
        show (0 : ℝ) = (if M < u ∧ s ≤ M + u then K (u, s) else 0)
        rw [ite_eq_right (fun h => hs h.2)]
    · rw [Set.indicator_of_notMem (by simpa using hu) _]
      show (0 : ℝ) = ∫ s : ℝ, F (u, s)
      rw [show (fun s => F (u, s)) = fun _ => (0 : ℝ) from funext fun s => by
        show (if M < u ∧ s ≤ M + u then K (u, s) else 0) = (0 : ℝ)
        rw [ite_eq_right (fun h => hu h.1)]]
      rw [integral_zero]
  have hswap : (∫ u : ℝ, ∫ s : ℝ, F (u, s)) = ∫ s : ℝ, ∫ u : ℝ, F (u, s) :=
    MeasureTheory.integral_integral_swap (μ := volume) (ν := volume)
      (f := fun u s => F (u, s)) hK
  -- the `u`-section at fixed `s`, up to the null boundary
  have hsec : ∀ s : ℝ, (∫ u : ℝ, F (u, s))
      = ∫ u in Set.Ioi (max M (s - M)), K (u, s) := by
    intro s
    have hset : {u : ℝ | M < u ∧ s ≤ M + u} =ᵐ[volume] Set.Ioi (max M (s - M)) := by
      have hsplit : {u : ℝ | M < u ∧ s ≤ M + u} = Set.Ioi M ∩ Set.Ici (s - M) := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by linarith⟩
      have hmax : Set.Ioi (max M (s - M)) = Set.Ioi M ∩ Set.Ioi (s - M) := by
        ext u
        simp only [Set.mem_Ioi, Set.mem_inter_iff]
        exact max_lt_iff
      rw [hsplit, hmax]
      exact ae_eq_set_inter Filter.EventuallyEq.rfl (MeasureTheory.Ioi_ae_eq_Ici).symm
    have hFpt : (fun u : ℝ => F (u, s))
        = ({u : ℝ | M < u ∧ s ≤ M + u}).indicator (fun u => K (u, s)) := by
      funext u
      show (if M < u ∧ s ≤ M + u then K (u, s) else 0)
        = ({u : ℝ | M < u ∧ s ≤ M + u}).indicator (fun u => K (u, s)) u
      by_cases hu : M < u ∧ s ≤ M + u
      · rw [ite_eq_left hu, Set.indicator_of_mem hu _]
      · rw [ite_eq_right hu, Set.indicator_of_notMem hu _]
    have hmeas : MeasurableSet {u : ℝ | M < u ∧ s ≤ M + u} := by
      have e : {u : ℝ | M < u ∧ s ≤ M + u} = Set.Ioi M ∩ Set.Ici (s - M) := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by linarith⟩
      rw [e]
      exact measurableSet_Ioi.inter measurableSet_Ici
    rw [hFpt, MeasureTheory.integral_indicator hmeas]
    exact setIntegral_congr_set hset
  rw [hLHS, hswap]
  apply integral_congr_ae
  filter_upwards with s
  exact hsec s

end RegionSwaps

/-! ## The scalar split: `I_{M,T} + (4πT)^{-1/2} R⁻_{M,T} + R⁺_{M,T}`

the paper's split `Tr Ã = I + R` with its formulas for `I_{M,T}`, `R⁻` and `R⁺`.  The pieces:

  `I_{M,T} = ∫ s ≤ 2M, (2M - s) p_T(2M - s) g_T(s) ds`         (`iMT`)
  `R⁻_{M,T} = ∫ s ≤ 2M, G_T(2M - s) g_T(s) ds`                 (`rMinusMT`, UNNORMALIZED
              `G_T = gaussianTail`; the paper's `R⁻` is `(4πT)^{-1/2} · rMinusMT`)
  `R⁺_{M,T} = (1/2) ∫ s > 2M, g_T(s) ds`                       (`rPlusMT`)
-/

section ScalarSplit

/-- The reflected-region piece `I_{M,T}` (the formula for `I_{M,T}`). -/
noncomputable def iMT (M T : ℝ) : ℝ :=
  ∫ s in Set.Iic (2 * M), (2 * M - s) * heatKernel T (2 * M - s) * backwardAiry T s

/-- The `s ≤ 2M` complementary piece `R⁻_{M,T}` in the UNNORMALIZED form
(`gaussianTail T v = ∫_v^∞ e^{-d²/(4T)} dd`): the paper's `R⁻_{M,T}`
(the exact formula for `R⁻`) is `(4πT)^{-1/2} · rMinusMT M T`. -/
noncomputable def rMinusMT (M T : ℝ) : ℝ :=
  ∫ s in Set.Iic (2 * M), gaussianTail T (2 * M - s) * backwardAiry T s

/-- The `s > 2M` complementary piece `R⁺_{M,T}` (the exact formula for `R⁺`). -/
noncomputable def rPlusMT (M T : ℝ) : ℝ :=
  (1/2) * ∫ s in Set.Ioi (2 * M), backwardAiry T s

/-- The reflected kernel times `g_T`, as a function of the pair `(x, z)`. -/
noncomputable def reflKernelFun (M T : ℝ) (p : ℝ × ℝ) : ℝ :=
  heatKernel T (2 * M - p.1 - p.2) * backwardAiry T (p.2 + p.1)

/-- The free kernel times `g_T`, as a function of the pair `(x, z)`. -/
noncomputable def freeKernelFun (T : ℝ) (p : ℝ × ℝ) : ℝ :=
  heatKernel T (p.1 - p.2) * backwardAiry T (p.2 + p.1)

/-- `reflKernelFun` is continuous. -/
theorem continuous_reflKernelFun (M T : ℝ) : Continuous (reflKernelFun M T) := by
  unfold reflKernelFun
  exact ((continuous_heatKernel T).comp (by fun_prop)).mul
    (continuous_backwardAiry.comp (continuous_const.prodMk
      (continuous_snd.add continuous_fst)))

/-- `freeKernelFun` is continuous. -/
theorem continuous_freeKernelFun (T : ℝ) : Continuous (freeKernelFun T) := by
  unfold freeKernelFun
  exact ((continuous_heatKernel T).comp (by fun_prop)).mul
    (continuous_backwardAiry.comp (continuous_const.prodMk
      (continuous_snd.add continuous_fst)))

/-- The `(1 + |s|)`-weighted reflected integrand is integrable on `(-∞, 2M]`:
the envelope hypothesis of `integral_Iic_Iic_add_swap`. -/
theorem integrableOn_reflected_envelope (hT : 0 < T) (M : ℝ) :
    IntegrableOn (fun s => (1 + |s|) * (heatKernel T (2 * M - s) * backwardAiry T s))
      (Set.Iic (2 * M)) volume := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp T
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ T ⟨hT.le, le_rfl⟩ 0
    rw [abs_zero, mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have henvl := integrable_one_add_sq_mul_exp_neg_sq_add_abs (b := 1/(4*T)) (by positivity)
    T (2*M)
  have henvl' : IntegrableOn (fun s => ((4*Real.pi*T)^(-1/2:ℝ) * C₀ * 2) * ((1 + s^2)
      * Real.exp (-(1/(4*T))*(s - 2*M)^2 + T*|s|))) (Set.Iic (2 * M)) volume :=
    (henvl.const_mul _).integrableOn
  refine henvl'.mono' ?_ (Eventually.of_forall fun s => ?_)
  · exact ((continuous_const.add continuous_abs).mul
      (((continuous_heatKernel T).comp (by fun_prop)).mul
        (continuous_backwardAiry_s T))).aestronglyMeasurable
  · have hnn1 : (0:ℝ) ≤ 1 + |s| := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hnn1,
      abs_of_nonneg (heatKernel_nonneg hT _)]
    calc (1 + |s|) * (heatKernel T (2 * M - s) * |backwardAiry T s|)
        ≤ (1 + |s|) * (((4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-(2*M - s)^2/(4*T)))
            * (C₀ * Real.exp (T * |s|))) := by
          apply mul_le_mul_of_nonneg_left _ hnn1
          unfold heatKernel
          exact mul_le_mul le_rfl (hC₀ T ⟨hT.le, le_rfl⟩ s) (abs_nonneg _) (by positivity)
      _ = ((4*Real.pi*T)^(-1/2:ℝ) * C₀) * ((1 + |s|)
            * Real.exp (-(1/(4*T))*(s - 2*M)^2 + T*|s|)) := by
          rw [show -(2*M - s)^2/(4*T) = -(1/(4*T))*(s - 2*M)^2 by ring]
          rw [show (1 + |s|) * (((4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-(1/(4*T))*(s - 2*M)^2))
                * (C₀ * Real.exp (T * |s|)))
              = ((4*Real.pi*T)^(-1/2:ℝ) * C₀) * ((1 + |s|)
                * (Real.exp (-(1/(4*T))*(s - 2*M)^2) * Real.exp (T * |s|))) from by ring]
          rw [← Real.exp_add]
      _ ≤ ((4*Real.pi*T)^(-1/2:ℝ) * C₀) * ((2 * (1 + s^2))
            * Real.exp (-(1/(4*T))*(s - 2*M)^2 + T*|s|)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have h := abs_le_one_add_sq s
          nlinarith [sq_nonneg s, abs_nonneg s]
      _ = ((4*Real.pi*T)^(-1/2:ℝ) * C₀ * 2) * ((1 + s^2)
            * Real.exp (-(1/(4*T))*(s - 2*M)^2 + T*|s|)) := by ring

/-- The plane integrability of the substituted free kernel `(x, w) ↦ p_T(2x - w) g_T(w)`
on `{x > M} × ℝ` — the Fubini hypothesis for the first complementary piece. -/
theorem integrable_freeK_prod_Ioi (hT : 0 < T) (M : ℝ) :
    Integrable (fun p : ℝ × ℝ => heatKernel T (2*p.1 - p.2) * backwardAiry T p.2)
      ((volume.restrict (Set.Ioi M)).prod volume) := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp_neg hT
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0
    rw [mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  obtain ⟨CT, hCTpos, hCT⟩ := heatKernelTail_le_exp_max_sq hT
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => heatKernel T (2*p.1 - p.2)
      * backwardAiry T p.2) ((volume.restrict (Set.Ioi M)).prod volume) :=
    (((continuous_heatKernel T).comp (by fun_prop)).mul
      (continuous_backwardAiry.comp (continuous_const.prodMk continuous_snd))
      |>.aestronglyMeasurable)
  have hsec : ∀ᵐ w : ℝ, Integrable (fun x : ℝ => heatKernel T (2*x - w)
      * backwardAiry T w) (volume.restrict (Set.Ioi M)) := by
    filter_upwards with w
    have hG : Integrable (fun x : ℝ => heatKernel T (2*x - w)) volume := by
      have h1 : Integrable (fun x : ℝ => Real.exp (-(4*T)⁻¹ * x^2)) volume :=
        integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < (4*T)⁻¹)
      have h2 := h1.comp_sub_right w
      have h3 := h2.comp_mul_left' (two_ne_zero)
      have h4 : Integrable (fun x : ℝ => (4*Real.pi*T)^(-1/2:ℝ)
          * Real.exp (-(4*T)⁻¹ * (2*x - w)^2)) volume := h3.const_mul _
      convert h4 using 1
      ext x
      unfold heatKernel
      congr 1
      field_simp
    exact (hG.mul_const _).integrableOn
  have hnorm : Integrable (fun w : ℝ => ∫ x : ℝ, ‖heatKernel T (2*x - w)
      * backwardAiry T w‖ ∂(volume.restrict (Set.Ioi M))) volume := by
    have hmeas2 : AEStronglyMeasurable (fun w : ℝ => ∫ x : ℝ, ‖heatKernel T (2*x - w)
        * backwardAiry T w‖ ∂(volume.restrict (Set.Ioi M))) volume := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖heatKernel T (2*p.1 - p.2)
          * backwardAiry T p.2‖) ((volume.restrict (Set.Ioi M)).prod volume) :=
        hmeas.norm
      have h2 := h1.prod_swap
      have h3 := h2.integral_prod_right'
      exact h3
    have henvl := (integrable_exp_neg_mul_exp_max_sq hT (2*M)).const_mul
      ((1/2) * CT * C₀)
    refine henvl.mono' hmeas2 ?_
    filter_upwards with w
    have hnorm_eval : (∫ x : ℝ, ‖heatKernel T (2*x - w) * backwardAiry T w‖
        ∂(volume.restrict (Set.Ioi M)))
        = (1/2) * heatKernelTail T (2*M - w) * |backwardAiry T w| := by
      have hpt : (fun x : ℝ => ‖heatKernel T (2*x - w) * backwardAiry T w‖)
          = fun x => heatKernel T (2*x - w) * |backwardAiry T w| := by
        funext x
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hT _)]
      rw [hpt, MeasureTheory.integral_mul_const,
        integral_Ioi_comp_two_mul_sub M w (heatKernel T)]
      rfl
    rw [Real.norm_eq_abs, hnorm_eval,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (heatKernelTail_nonneg hT _))
        (abs_nonneg _))]
    calc (1/2) * heatKernelTail T (2*M - w) * |backwardAiry T w|
        ≤ ((1/2) * (CT * Real.exp (-(max (2*M - w) 0)^2 / (4 * T))))
          * (C₀ * Real.exp (-T * w)) := by
          apply mul_le_mul _ (hC₀ w) (abs_nonneg _)
            (mul_nonneg (by norm_num) (mul_nonneg hCTpos.le (Real.exp_pos _).le))
          exact mul_le_mul_of_nonneg_left (hCT _) (by norm_num)
      _ = ((1/2) * CT * C₀) * (Real.exp (-T * w)
          * Real.exp (-(max (2*M - w) 0)^2 / (4 * T))) := by ring
  exact (integrable_prod_iff' hmeas).mpr ⟨hsec, hnorm⟩

/-- Auxiliary monotonicity: `max (2M − s) 0 ≤ max (2·max M (s−M) − s) 0`. -/
theorem max_two_mul_max_sub_le (M s : ℝ) :
    max (2*M - s) 0 ≤ max (2 * max M (s - M) - s) 0 := by
  rcases le_total (2*M - s) 0 with h1 | h1
  · rw [max_eq_right h1, max_eq_right (show M ≤ s - M by linarith),
      show 2 * (s - M) - s = s - 2*M by ring, max_eq_left (show (0:ℝ) ≤ s - 2*M by linarith)]
    linarith
  · rw [max_eq_left h1, max_eq_left (show s - M ≤ M by linarith), max_eq_left h1]

/-- The `u`-section of the complementary region `{u > M, s ≤ M + u}` at fixed `s`
is, up to the null boundary, `{u > max M (s − M)}`. -/
theorem swapRegionIoi_section_ae (M s : ℝ) :
    {u : ℝ | M < u ∧ s ≤ M + u} =ᵐ[volume] Set.Ioi (max M (s - M)) := by
  have hsplit : {u : ℝ | M < u ∧ s ≤ M + u} = Set.Ioi M ∩ Set.Ici (s - M) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
  have hmax : Set.Ioi (max M (s - M)) = Set.Ioi M ∩ Set.Ioi (s - M) := by
    ext u
    simp only [Set.mem_Ioi, Set.mem_inter_iff]
    exact max_lt_iff
  rw [hsplit, hmax]
  exact ae_eq_set_inter Filter.EventuallyEq.rfl (MeasureTheory.Ioi_ae_eq_Ici).symm

/-- Measurability of the `u`-section of the complementary region. -/
theorem measurableSet_swapRegionIoi_section (M s : ℝ) :
    MeasurableSet {u : ℝ | M < u ∧ s ≤ M + u} := by
  have hsplit : {u : ℝ | M < u ∧ s ≤ M + u} = Set.Ioi M ∩ Set.Ici (s - M) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
  rw [hsplit]
  exact measurableSet_Ioi.inter measurableSet_Ici

/-- The plane integrability of the region-indicator of
`(u, s) ↦ p_T(2u - s) g_T(s)` on `{u > M, s ≤ M + u}` — the hypothesis of
`integral_Ioi_Iic_region_swap`. -/
theorem integrable_freeK_prod_region (hT : 0 < T) (M : ℝ) :
    Integrable (fun p : ℝ × ℝ => if M < p.1 ∧ p.2 ≤ M + p.1 then
      heatKernel T (2*p.1 - p.2) * backwardAiry T p.2 else 0) (volume.prod volume) := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp_neg hT
  obtain ⟨CT, hCTpos, hCT⟩ := heatKernelTail_le_exp_max_sq hT
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0
    rw [mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  set F : ℝ × ℝ → ℝ := fun p => if M < p.1 ∧ p.2 ≤ M + p.1 then
    heatKernel T (2*p.1 - p.2) * backwardAiry T p.2 else 0 with hFdef
  have hFmeas : Measurable F := Measurable.ite (measurableSet_swapRegionIoi M)
    (((continuous_heatKernel T).comp (by fun_prop)).mul
      (continuous_backwardAiry.comp (continuous_const.prodMk continuous_snd))).measurable
    measurable_const
  have hsec : ∀ᵐ s : ℝ, Integrable (fun u : ℝ => F (u, s)) volume := by
    filter_upwards with s
    have hG : Integrable (fun u : ℝ => heatKernel T (2*u - s)) volume := by
      have h1 : Integrable (fun x : ℝ => Real.exp (-(4*T)⁻¹ * x^2)) volume :=
        integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < (4*T)⁻¹)
      have h2 := h1.comp_sub_right s
      have h3 := h2.comp_mul_left' (two_ne_zero)
      have h4 : Integrable (fun x : ℝ => (4*Real.pi*T)^(-1/2:ℝ)
          * Real.exp (-(4*T)⁻¹ * (2*x - s)^2)) volume := h3.const_mul _
      convert h4 using 1
      ext x
      unfold heatKernel
      congr 1
      field_simp
    apply (hG.mul_const |backwardAiry T s|).mono'
      ((hFmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    filter_upwards with u
    show ‖F (u, s)‖ ≤ heatKernel T (2*u - s) * |backwardAiry T s|
    by_cases hu : M < u ∧ s ≤ M + u
    · show ‖(if M < u ∧ s ≤ M + u then heatKernel T (2*u - s) * backwardAiry T s else 0)‖
        ≤ heatKernel T (2*u - s) * |backwardAiry T s|
      rw [ite_eq_left hu, Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hT _)]
    · show ‖(if M < u ∧ s ≤ M + u then heatKernel T (2*u - s) * backwardAiry T s else 0)‖
        ≤ heatKernel T (2*u - s) * |backwardAiry T s|
      rw [ite_eq_right hu, Real.norm_eq_abs, abs_zero]
      exact mul_nonneg (heatKernel_nonneg hT _) (abs_nonneg _)
  have hnorm : Integrable (fun s : ℝ => ∫ u : ℝ, ‖F (u, s)‖) volume := by
    have hmeas2 : AEStronglyMeasurable (fun s : ℝ => ∫ u : ℝ, ‖F (u, s)‖) volume := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖F p‖) (volume.prod volume) :=
        hFmeas.norm.aestronglyMeasurable
      exact (h1.prod_swap).integral_prod_right'
    refine ((integrable_exp_neg_mul_exp_max_sq hT (2*M)).const_mul (C₀/2 * CT)).mono'
      hmeas2 ?_
    filter_upwards with s
    -- exact evaluation of the section norm
    have hnorm_eval : (∫ u : ℝ, ‖F (u, s)‖)
        = (1/2) * heatKernelTail T (2 * max M (s - M) - s) * |backwardAiry T s| := by
      have hpt : (fun u : ℝ => ‖F (u, s)‖)
          = ({u : ℝ | M < u ∧ s ≤ M + u}).indicator
            (fun u => heatKernel T (2*u - s) * |backwardAiry T s|) := by
        funext u
        show ‖(if M < u ∧ s ≤ M + u then heatKernel T (2*u - s) * backwardAiry T s else 0)‖
          = ({u : ℝ | M < u ∧ s ≤ M + u}).indicator
            (fun u => heatKernel T (2*u - s) * |backwardAiry T s|) u
        by_cases hu : M < u ∧ s ≤ M + u
        · rw [ite_eq_left hu, Set.indicator_of_mem hu _, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (heatKernel_nonneg hT _)]
        · rw [ite_eq_right hu, Set.indicator_of_notMem hu _, Real.norm_eq_abs, abs_zero]
      rw [hpt, MeasureTheory.integral_indicator (measurableSet_swapRegionIoi_section M s),
        setIntegral_congr_set (swapRegionIoi_section_ae M s),
        MeasureTheory.integral_mul_const,
        integral_Ioi_comp_two_mul_sub (max M (s - M)) s (heatKernel T)]
      rfl
    rw [Real.norm_eq_abs, hnorm_eval,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (heatKernelTail_nonneg hT _))
        (abs_nonneg _))]
    calc (1/2) * heatKernelTail T (2 * max M (s - M) - s) * |backwardAiry T s|
        ≤ ((1/2) * (CT * Real.exp (-(max (2*M - s) 0)^2 / (4 * T))))
          * (C₀ * Real.exp (-T * s)) := by
          apply mul_le_mul _ (hC₀ s) (abs_nonneg _)
            (mul_nonneg (by norm_num) (mul_nonneg hCTpos.le (Real.exp_pos _).le))
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
          refine (hCT _).trans (mul_le_mul_of_nonneg_left ?_ hCTpos.le)
          apply Real.exp_le_exp.mpr
          exact (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 4*T)).mpr
            (neg_le_neg_iff.mpr (pow_le_pow_left₀ (le_max_right _ _)
              (max_two_mul_max_sub_le M s) 2))
      _ = (C₀/2 * CT) * (Real.exp (-T * s) * Real.exp (-(max (2*M - s) 0)^2 / (4 * T))) := by
          ring
  exact (integrable_prod_iff' hFmeas.aestronglyMeasurable).mpr ⟨hsec, hnorm⟩

end ScalarSplit

/-! ## The scalar split: Fubini inputs for the complementary region

The complement of the reflected region `{x ≤ M ∧ z ≤ M}` is handled as the disjoint
union `{M < x} ∪ {x ≤ M ∧ M < z}`; this section supplies the
plane-integrability inputs for the two pieces. -/

section ComplementFubini

/-- Measurability of the second complementary region `{x ≤ M, M < z}`. -/
theorem measurableSet_Iic_Ioi_region (M : ℝ) :
    MeasurableSet {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2} := by
  have e : {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2}
      = {p : ℝ × ℝ | p.1 ≤ M} ∩ {p : ℝ × ℝ | M < p.2} := by
    ext ⟨x, z⟩
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [e]
  exact (measurableSet_Iic.preimage measurable_fst).inter
    (measurableSet_Ioi.preimage measurable_snd)

/-- The plane integrability of the free kernel on `{x ≤ M, M < z}` — the Fubini
hypothesis for the second complementary piece.  For `z > M ≥ x` one has
`∫_{z>M} p_T(x - z) dz = P̄_T(M - x) ≤ C_T e^{-(M-x)²/(4T)}`
(`heatKernelTail_le_exp_max_sq`), whose Gaussian decay as `x → -∞` dominates the
`e^{-Tx}` growth of `|g_T(x + z)| ≤ C₀ e^{-T(x+z)}` (`backwardAiry_abs_le_exp_neg`). -/
theorem integrable_freeK_region_Iic_Ioi (hT : 0 < T) (M : ℝ) :
    Integrable (fun p : ℝ × ℝ => if p.1 ≤ M ∧ M < p.2 then
      heatKernel T (p.1 - p.2) * backwardAiry T (p.2 + p.1) else 0)
      (volume.prod volume) := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp_neg hT
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0
    rw [mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  obtain ⟨CT, hCTpos, hCT⟩ := heatKernelTail_le_exp_max_sq hT
  set G : ℝ × ℝ → ℝ := fun p => if p.1 ≤ M ∧ M < p.2 then
    heatKernel T (p.1 - p.2) * backwardAiry T (p.2 + p.1) else 0 with hGdef
  have hGmeas : Measurable G := Measurable.ite (measurableSet_Iic_Ioi_region M)
    (continuous_freeKernelFun T).measurable measurable_const
  -- pointwise domination of the sections, valid for all `z` when `x ≤ M`
  have hpoint : ∀ x z : ℝ, x ≤ M →
      ‖G (x, z)‖ ≤ (C₀ * Real.exp (-T * M) * Real.exp (-T * x)) * heatKernel T (x - z) := by
    intro x z hx
    show ‖(if x ≤ M ∧ M < z then heatKernel T (x - z) * backwardAiry T (z + x) else 0)‖ ≤ _
    by_cases hz : M < z
    · rw [ite_eq_left ⟨hx, hz⟩, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (heatKernel_nonneg hT _)]
      calc heatKernel T (x - z) * |backwardAiry T (z + x)|
          ≤ heatKernel T (x - z) * (C₀ * Real.exp (-T * (z + x))) :=
            mul_le_mul_of_nonneg_left (hC₀ _) (heatKernel_nonneg hT _)
        _ ≤ heatKernel T (x - z) * (C₀ * Real.exp (-T * M) * Real.exp (-T * x)) := by
            apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg hT _)
            rw [show -T * (z + x) = -T * z + -T * x by ring, Real.exp_add]
            have hexp : Real.exp (-T * z) ≤ Real.exp (-T * M) :=
              Real.exp_le_exp.mpr (by nlinarith [hT, hz.le])
            calc C₀ * (Real.exp (-T * z) * Real.exp (-T * x))
                = (C₀ * Real.exp (-T * z)) * Real.exp (-T * x) := by ring
              _ ≤ (C₀ * Real.exp (-T * M)) * Real.exp (-T * x) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hexp hC₀nn) (Real.exp_pos _).le
              _ = C₀ * Real.exp (-T * M) * Real.exp (-T * x) := by ring
        _ = (C₀ * Real.exp (-T * M) * Real.exp (-T * x)) * heatKernel T (x - z) := by ring
    · rw [ite_eq_right (fun h => hz h.2), Real.norm_eq_abs, abs_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hC₀nn (Real.exp_pos _).le)
        (Real.exp_pos _).le) (heatKernel_nonneg hT _)
  -- section integrability, for every `x`
  have hsecAll : ∀ x : ℝ, Integrable (fun z : ℝ => G (x, z)) volume := by
    intro x
    by_cases hx : x ≤ M
    · have hK : Integrable (fun z : ℝ => heatKernel T (x - z)) volume := by
        have h1 : (fun z : ℝ => heatKernel T (x - z)) = fun z => heatKernel T (z - x) := by
          funext z
          rw [show x - z = -(z - x) by ring, heatKernel_even]
        rw [h1]
        exact (integrable_heatKernel hT).comp_sub_right x
      refine ((hK.const_mul (C₀ * Real.exp (-T * M) * Real.exp (-T * x)))).mono'
        ((hGmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
        (Eventually.of_forall fun z => hpoint x z hx)
    · rw [show (fun z : ℝ => G (x, z)) = fun _ => (0 : ℝ) from funext fun z => by
        show (if x ≤ M ∧ M < z then _ else (0:ℝ)) = 0
        exact ite_eq_right (fun h => hx h.1)]
      exact integrable_zero _ _ _
  -- the norm-integral bound
  have hnorm : Integrable (fun x : ℝ => ∫ z : ℝ, ‖G (x, z)‖) volume := by
    have hmeas : AEStronglyMeasurable (fun x : ℝ => ∫ z : ℝ, ‖G (x, z)‖) volume :=
      (hGmeas.norm.aestronglyMeasurable).integral_prod_right'
    refine ((integrable_exp_neg_mul_exp_max_sq hT M).const_mul
      (C₀ * Real.exp (-T * M) * CT)).mono' hmeas (Eventually.of_forall fun x => ?_)
    by_cases hx : x ≤ M
    · -- for `x ≤ M`, the `z`-mass sits in `z > M` and evaluates to `P̄_T (M - x)`
      have hNormEq : (∫ z : ℝ, ‖G (x, z)‖) = ∫ z in Set.Ioi M, ‖G (x, z)‖ := by
        rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : M < z
        · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hz) _]
        · rw [Set.indicator_of_notMem (by simpa using hz) _]
          show ‖(if x ≤ M ∧ M < z then _ else (0:ℝ))‖ = 0
          rw [ite_eq_right (fun h => hz h.2), Real.norm_eq_abs, abs_zero]
      have hK : Integrable (fun z : ℝ => heatKernel T (x - z)) volume := by
        have h1 : (fun z : ℝ => heatKernel T (x - z)) = fun z => heatKernel T (z - x) := by
          funext z
          rw [show x - z = -(z - x) by ring, heatKernel_even]
        rw [h1]
        exact (integrable_heatKernel hT).comp_sub_right x
      have hdom : ∫ z in Set.Ioi M, ‖G (x, z)‖
          ≤ ∫ z in Set.Ioi M, (C₀ * Real.exp (-T * M) * Real.exp (-T * x))
              * heatKernel T (x - z) := by
        apply setIntegral_mono_on _ _ measurableSet_Ioi fun z _ => hpoint x z hx
        · exact (hsecAll x).norm.integrableOn
        · exact (hK.const_mul _).integrableOn
      have heval : (∫ z in Set.Ioi M, (C₀ * Real.exp (-T * M) * Real.exp (-T * x))
            * heatKernel T (x - z))
          = (C₀ * Real.exp (-T * M) * Real.exp (-T * x)) * heatKernelTail T (M - x) := by
        rw [integral_const_mul]
        congr 1
        have h1 : (fun z : ℝ => heatKernel T (x - z)) = fun z => heatKernel T (-x + z) := by
          funext z
          rw [show x - z = -(-x + z) by ring, heatKernel_even]
        rw [h1, integral_Ioi_comp_add M (-x) (heatKernel T), ← sub_eq_add_neg]
        rfl
      have htail : heatKernelTail T (M - x)
          ≤ CT * Real.exp (-(max (M - x) 0)^2 / (4 * T)) := hCT (M - x)
      calc ‖∫ z : ℝ, ‖G (x, z)‖‖
          = ∫ z : ℝ, ‖G (x, z)‖ :=
            Real.norm_of_nonneg (integral_nonneg fun z => norm_nonneg _)
        _ = ∫ z in Set.Ioi M, ‖G (x, z)‖ := hNormEq
        _ ≤ (C₀ * Real.exp (-T * M) * Real.exp (-T * x)) * heatKernelTail T (M - x) :=
            hdom.trans_eq heval
        _ ≤ (C₀ * Real.exp (-T * M) * Real.exp (-T * x))
            * (CT * Real.exp (-(max (M - x) 0)^2 / (4 * T))) :=
            mul_le_mul_of_nonneg_left htail
              (mul_nonneg (mul_nonneg hC₀nn (Real.exp_pos _).le) (Real.exp_pos _).le)
        _ = (C₀ * Real.exp (-T * M) * CT)
            * (Real.exp (-T * x) * Real.exp (-(max (M - x) 0)^2 / (4 * T))) := by ring
    · -- for `x > M` the function vanishes identically
      have hNormEq : (∫ z : ℝ, ‖G (x, z)‖) = 0 := by
        rw [show (fun z : ℝ => ‖G (x, z)‖) = fun _ => (0 : ℝ) from funext fun z => by
          show ‖(if x ≤ M ∧ M < z then _ else (0:ℝ))‖ = 0
          rw [ite_eq_right (fun h => hx h.1), Real.norm_eq_abs, abs_zero]]
        exact integral_zero _ _
      rw [hNormEq, Real.norm_eq_abs, abs_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hC₀nn (Real.exp_pos _).le) hCTpos.le)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  exact (integrable_prod_iff hGmeas.aestronglyMeasurable).mpr
    ⟨Eventually.of_forall hsecAll, hnorm⟩

/-- The free kernel is plane-integrable on `{M < x} × ℝ` — the Fubini hypothesis for
the first complementary piece.  The substitution `s = x + z` identifies its
section-norm integrals with those of the substituted kernel of
`integrable_freeK_prod_Ioi`. -/
theorem integrable_freeKernelFun_Ioi_prod (hT : 0 < T) (M : ℝ) :
    Integrable (fun p : ℝ × ℝ => heatKernel T (p.1 - p.2) * backwardAiry T (p.2 + p.1))
      ((volume.restrict (Set.Ioi M)).prod volume) := by
  have hK := integrable_freeK_prod_Ioi hT M
  have hKmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => heatKernel T (2*p.1 - p.2) * backwardAiry T p.2)
      ((volume.restrict (Set.Ioi M)).prod volume) :=
    (((continuous_heatKernel T).comp (by fun_prop)).mul
      (continuous_backwardAiry.comp (continuous_const.prodMk continuous_snd))
      |>.aestronglyMeasurable)
  have hK' := (integrable_prod_iff hKmeas).mp hK
  have hFmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => heatKernel T (p.1 - p.2) * backwardAiry T (p.2 + p.1))
      ((volume.restrict (Set.Ioi M)).prod volume) :=
    (((continuous_heatKernel T).comp (continuous_fst.sub continuous_snd)).mul
      (continuous_backwardAiry.comp (continuous_const.prodMk
        (continuous_snd.add continuous_fst)))).aestronglyMeasurable
  rw [integrable_prod_iff hFmeas]
  constructor
  · -- a.e. section integrability, transferred by the translation `s = x + z`
    filter_upwards [hK'.1] with x hx
    have heq : (fun z : ℝ => heatKernel T (x - z) * backwardAiry T (z + x))
        = fun z => (fun w : ℝ => heatKernel T (2*x - w) * backwardAiry T w) (z + x) := by
      funext z
      congr 1
      · congr 1
        ring
    rw [heq]
    exact hx.comp_add_right x
  · -- the norm-integral, transferred by the same translation
    have heq : (fun x : ℝ => ∫ z : ℝ, ‖heatKernel T (x - z) * backwardAiry T (z + x)‖)
        = fun x => ∫ w : ℝ, ‖heatKernel T (2*x - w) * backwardAiry T w‖ := by
      funext x
      rw [show (fun z : ℝ => ‖heatKernel T (x - z) * backwardAiry T (z + x)‖)
          = fun z => ‖heatKernel T (2*x - (z + x)) * backwardAiry T (z + x)‖
          from funext fun z => by
        congr 1
        congr 1
        ring]
      exact MeasureTheory.integral_add_right_eq_self (μ := volume)
        (fun w : ℝ => ‖heatKernel T (2*x - w) * backwardAiry T w‖) x
    rw [heq]
    exact hK'.2

/-- The free kernel is plane-integrable on `{x ≤ M} × {M < z}` — immediate from
`integrable_freeK_region_Iic_Ioi` through the indicator characterization. -/
theorem integrable_freeKernelFun_Iic_prod_Ioi (hT : 0 < T) (M : ℝ) :
    Integrable (fun p : ℝ × ℝ => heatKernel T (p.1 - p.2) * backwardAiry T (p.2 + p.1))
      ((volume.restrict (Set.Iic M)).prod (volume.restrict (Set.Ioi M))) := by
  rw [Measure.prod_restrict]
  show IntegrableOn (fun p : ℝ × ℝ => heatKernel T (p.1 - p.2) * backwardAiry T (p.2 + p.1))
    (Set.Iic M ×ˢ Set.Ioi M) (volume.prod volume)
  rw [← MeasureTheory.integrable_indicator_iff (measurableSet_Iic.prod measurableSet_Ioi)]
  have hGeq : (Set.Iic M ×ˢ Set.Ioi M).indicator
        (fun p : ℝ × ℝ => heatKernel T (p.1 - p.2) * backwardAiry T (p.2 + p.1))
      = fun p : ℝ × ℝ => if p.1 ≤ M ∧ M < p.2 then
          heatKernel T (p.1 - p.2) * backwardAiry T (p.2 + p.1) else 0 := by
    funext ⟨x, z⟩
    by_cases hxz : x ≤ M ∧ M < z
    · rw [Set.indicator_of_mem _ _, ite_eq_left hxz]
      exact Set.mem_prod.mpr ⟨hxz.1, Set.mem_Ioi.mpr hxz.2⟩
    · rw [Set.indicator_of_notMem _ _, ite_eq_right hxz]
      intro hmem
      obtain ⟨h1, h2⟩ := Set.mem_prod.mp hmem
      exact hxz ⟨h1, Set.mem_Ioi.mp h2⟩
  rw [hGeq]
  exact integrable_freeK_region_Iic_Ioi hT M

end ComplementFubini

/-! ## The scalar split theorem: `Tr Ã = I + (4πT)^{-1/2} R⁻ + R⁺`

the paper's split `Tr Ã = I + R` with its formulas for `I_{M,T}`, `R⁻` and `R⁺`.  The reflected
piece evaluates by `integral_Iic_Iic_add_swap`
(the `s = x + z` substitution on `{x ≤ M, z ≤ M}`); the two complementary pieces are
Fubini-swapped to `s`-first order and the inner `x`-integrals evaluate to Gaussian
tails, which combine by evenness (`heatKernelTail_add_neg`). -/

section ScalarSplitMain

/-- The first complementary piece `{M < x} × ℝ` evaluates to
`(1/2) ∫ s, g_T(s) P̄_T(2M - s) ds`: substitute `s = x + z`, swap the order of
integration (`integrable_freeK_prod_Ioi`), and integrate `p_T(2x - s)` over
`x > M`. -/
theorem free_integral_Ioi_eval (hT : 0 < T) (M : ℝ) :
    (∫ x in Set.Ioi M, ∫ z : ℝ, heatKernel T (x - z) * backwardAiry T (z + x))
      = (1/2) * ∫ s : ℝ, backwardAiry T s * heatKernelTail T (2*M - s) := by
  have hinner : ∀ x : ℝ, (∫ z : ℝ, heatKernel T (x - z) * backwardAiry T (z + x))
      = ∫ s : ℝ, heatKernel T (2*x - s) * backwardAiry T s := by
    intro x
    have h1 : (fun z : ℝ => heatKernel T (x - z) * backwardAiry T (z + x))
        = fun z => (fun w : ℝ => heatKernel T (2*x - w) * backwardAiry T w) (z + x) := by
      funext z
      show heatKernel T (x - z) * backwardAiry T (z + x)
          = heatKernel T (2*x - (z + x)) * backwardAiry T (z + x)
      congr 1
      congr 1
      ring
    rw [h1]
    exact MeasureTheory.integral_add_right_eq_self (μ := volume)
      (fun w : ℝ => heatKernel T (2*x - w) * backwardAiry T w) x
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hinner x)]
  rw [MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Ioi M))
    (ν := volume) (f := fun x s : ℝ => heatKernel T (2*x - s) * backwardAiry T s)
    (integrable_freeK_prod_Ioi hT M)]
  rw [show (fun s : ℝ => ∫ x in Set.Ioi M, heatKernel T (2*x - s) * backwardAiry T s)
      = fun s => (1/2) * (backwardAiry T s * heatKernelTail T (2*M - s))
      from funext fun s => by
    rw [show (fun x : ℝ => heatKernel T (2*x - s) * backwardAiry T s)
        = fun x => backwardAiry T s * heatKernel T (2*x - s)
        from funext fun x => mul_comm _ _]
    rw [integral_const_mul, integral_Ioi_comp_two_mul_sub M s (heatKernel T)]
    show backwardAiry T s * ((1/2) * heatKernelTail T (2*M - s))
      = (1/2) * (backwardAiry T s * heatKernelTail T (2*M - s))
    ring]
  exact integral_const_mul (1/2 : ℝ) _

/-- The second complementary piece `{x ≤ M, M < z}` evaluates to
`(1/2) ∫ s, g_T(s) P̄_T(2·max M (s-M) - s) ds`: swap to `z`-first order
(`integrable_freeK_region_Iic_Ioi`), substitute `w = z + x`, apply the region swap
`integral_Ioi_Iic_region_swap`, and integrate `p_T(2z - w)` over
`z > max M (w - M)`. -/
theorem free_integral_Iic_Ioi_eval (hT : 0 < T) (M : ℝ) :
    (∫ x in Set.Iic M, ∫ z in Set.Ioi M, heatKernel T (x - z) * backwardAiry T (z + x))
      = (1/2) * ∫ s : ℝ, backwardAiry T s * heatKernelTail T (2 * max M (s - M) - s) := by
  rw [MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Iic M))
    (ν := volume.restrict (Set.Ioi M))
    (f := fun x z : ℝ => heatKernel T (x - z) * backwardAiry T (z + x))
    (integrable_freeKernelFun_Iic_prod_Ioi hT M)]
  have hinner : ∀ z : ℝ, (∫ x in Set.Iic M, heatKernel T (x - z) * backwardAiry T (z + x))
      = ∫ w in Set.Iic (M + z), heatKernel T (2*z - w) * backwardAiry T w := by
    intro z
    have h1 : (fun x : ℝ => heatKernel T (x - z) * backwardAiry T (z + x))
        = fun x => (fun w : ℝ => heatKernel T (2*z - w) * backwardAiry T w) (z + x) := by
      funext x
      show heatKernel T (x - z) * backwardAiry T (z + x)
          = heatKernel T (2*z - (z + x)) * backwardAiry T (z + x)
      congr 1
      rw [show 2*z - (z + x) = -(x - z) by ring, heatKernel_even]
    rw [h1]
    exact integral_Iic_comp_add M z (fun w : ℝ => heatKernel T (2*z - w) * backwardAiry T w)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun z _ => hinner z)]
  have hswap2 : (∫ u in Set.Ioi M, ∫ s in Set.Iic (M + u),
        heatKernel T (2*u - s) * backwardAiry T s)
      = ∫ s : ℝ, ∫ u in Set.Ioi (max M (s - M)),
        heatKernel T (2*u - s) * backwardAiry T s :=
    integral_Ioi_Iic_region_swap M _ (integrable_freeK_prod_region hT M)
  rw [hswap2]
  rw [show (fun s : ℝ => ∫ u in Set.Ioi (max M (s - M)),
        heatKernel T (2*u - s) * backwardAiry T s)
      = fun s => (1/2) * (backwardAiry T s * heatKernelTail T (2 * max M (s - M) - s))
      from funext fun s => by
    rw [show (fun u : ℝ => heatKernel T (2*u - s) * backwardAiry T s)
        = fun u => backwardAiry T s * heatKernel T (2*u - s)
        from funext fun u => mul_comm _ _]
    rw [integral_const_mul, integral_Ioi_comp_two_mul_sub (max M (s - M)) s (heatKernel T)]
    show backwardAiry T s * ((1/2) * heatKernelTail T (2 * max M (s - M) - s))
      = (1/2) * (backwardAiry T s * heatKernelTail T (2 * max M (s - M) - s))
    ring]
  exact integral_const_mul (1/2 : ℝ) _

/-- The reflected piece `{x ≤ M, z ≤ M}` evaluates to `I_{M,T}` (the formula for `I_{M,T}`):
substitute `s = x + z`, then swap the order with the section
length `2M - s` (`integral_Iic_Iic_add_swap`). -/
theorem reflected_integral_eq_iMT (hT : 0 < T) (M : ℝ) :
    (∫ x in Set.Iic M, ∫ z in Set.Iic M,
      heatKernel T (2*M - x - z) * backwardAiry T (x + z))
      = iMT M T := by
  have hinner : ∀ x : ℝ, (∫ z in Set.Iic M,
        heatKernel T (2*M - x - z) * backwardAiry T (x + z))
      = ∫ s in Set.Iic (M + x), heatKernel T (2*M - s) * backwardAiry T s := by
    intro x
    have h1 : (fun z : ℝ => heatKernel T (2*M - x - z) * backwardAiry T (x + z))
        = fun z => (fun s : ℝ => heatKernel T (2*M - s) * backwardAiry T s) (x + z) := by
      funext z
      show heatKernel T (2*M - x - z) * backwardAiry T (x + z)
          = heatKernel T (2*M - (x + z)) * backwardAiry T (x + z)
      congr 1
      congr 1
      ring
    rw [h1]
    exact integral_Iic_comp_add M x (fun s : ℝ => heatKernel T (2*M - s) * backwardAiry T s)
  rw [setIntegral_congr_fun measurableSet_Iic (fun x _ => hinner x)]
  rw [integral_Iic_Iic_add_swap M (fun s : ℝ => heatKernel T (2*M - s) * backwardAiry T s)
    (((continuous_heatKernel T).comp (by fun_prop)).mul
      (continuous_backwardAiry_s T)).measurable
    (integrableOn_reflected_envelope hT M)]
  show (∫ s in Set.Iic (2 * M), (2 * M - s) * (heatKernel T (2 * M - s) * backwardAiry T s))
    = ∫ s in Set.Iic (2 * M), (2 * M - s) * heatKernel T (2 * M - s) * backwardAiry T s
  exact setIntegral_congr_fun measurableSet_Iic fun s _ => (mul_assoc _ _ _).symm

/-- The normalized `R⁻`-piece: `(4πT)^{-1/2} · rMinusMT` in `heatKernelTail` form. -/
theorem const_mul_rMinusMT_eq (hT : 0 < T) (M : ℝ) :
    (4*Real.pi*T)^(-1/2:ℝ) * rMinusMT M T
      = ∫ s in Set.Iic (2*M), heatKernelTail T (2*M - s) * backwardAiry T s := by
  rw [show rMinusMT M T
      = ∫ s in Set.Iic (2*M), gaussianTail T (2*M - s) * backwardAiry T s from rfl]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Iic
  intro s _
  show (4*Real.pi*T)^(-1/2:ℝ) * (gaussianTail T (2*M - s) * backwardAiry T s)
      = heatKernelTail T (2*M - s) * backwardAiry T s
  rw [heatKernelTail_eq_const_mul_gaussianTail]
  ring

/-- The `s`-integrand of the first complementary piece is integrable on `ℝ`
(the Gaussian tail envelope times `|g_T(s)| ≤ C₀ e^{-Ts}`). -/
theorem integrable_backwardAiry_mul_heatKernelTail_sub (hT : 0 < T) (M : ℝ) :
    Integrable (fun s : ℝ => backwardAiry T s * heatKernelTail T (2*M - s)) volume := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp_neg hT
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0
    rw [mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  obtain ⟨CT, hCTpos, hCT⟩ := heatKernelTail_le_exp_max_sq hT
  refine ((integrable_exp_neg_mul_exp_max_sq hT (2*M)).const_mul (C₀ * CT)).mono'
    (((continuous_backwardAiry_s T).measurable.mul
      ((measurable_heatKernelTail hT).comp
        (measurable_const.sub measurable_id))).aestronglyMeasurable)
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernelTail_nonneg hT _)]
  calc |backwardAiry T s| * heatKernelTail T (2*M - s)
      ≤ (C₀ * Real.exp (-T * s)) * (CT * Real.exp (-(max (2*M - s) 0)^2 / (4 * T))) :=
        mul_le_mul (hC₀ s) (hCT _) (heatKernelTail_nonneg hT _)
          (mul_nonneg hC₀nn (Real.exp_pos _).le)
    _ = (C₀ * CT) * (Real.exp (-T * s) * Real.exp (-(max (2*M - s) 0)^2 / (4 * T))) := by ring

/-- The `s`-integrand of the second complementary piece is integrable on `ℝ`
(`max_two_mul_max_sub_le` reduces the tail argument to the first piece's envelope). -/
theorem integrable_backwardAiry_mul_heatKernelTail_max (hT : 0 < T) (M : ℝ) :
    Integrable (fun s : ℝ => backwardAiry T s * heatKernelTail T (2 * max M (s - M) - s))
      volume := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp_neg hT
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0
    rw [mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  obtain ⟨CT, hCTpos, hCT⟩ := heatKernelTail_le_exp_max_sq hT
  refine ((integrable_exp_neg_mul_exp_max_sq hT (2*M)).const_mul (C₀ * CT)).mono'
    (((continuous_backwardAiry_s T).measurable.mul
      ((measurable_heatKernelTail hT).comp
        ((measurable_const.max (measurable_id.sub measurable_const)).const_mul 2
          |>.sub measurable_id))).aestronglyMeasurable)
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernelTail_nonneg hT _)]
  calc |backwardAiry T s| * heatKernelTail T (2 * max M (s - M) - s)
      ≤ (C₀ * Real.exp (-T * s)) * (CT * Real.exp (-(max (2*M - s) 0)^2 / (4 * T))) := by
        apply mul_le_mul (hC₀ s) _ (heatKernelTail_nonneg hT _)
          (mul_nonneg hC₀nn (Real.exp_pos _).le)
        refine (hCT _).trans (mul_le_mul_of_nonneg_left ?_ hCTpos.le)
        exact Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right
          (by positivity : (0:ℝ) < 4*T)).mpr (neg_le_neg_iff.mpr
            (pow_le_pow_left₀ (le_max_right _ _) (max_two_mul_max_sub_le M s) 2)))
    _ = (C₀ * CT) * (Real.exp (-T * s) * Real.exp (-(max (2*M - s) 0)^2 / (4 * T))) := by ring

/-- `g_T` is integrable on `(A, ∞)` (`|g_T(s)| ≤ C₀ e^{-Ts}`). -/
theorem integrableOn_backwardAiry_Ioi (hT : 0 < T) (A : ℝ) :
    IntegrableOn (backwardAiry T) (Set.Ioi A) volume := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp_neg hT
  refine ((exp_neg_integrableOn_Ioi A hT).const_mul C₀).mono'
    ((continuous_backwardAiry_s T).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun s _ => ?_)
  rw [Real.norm_eq_abs]
  exact hC₀ s

/-- **The two complementary pieces combine to `(4πT)^{-1/2} R⁻ + R⁺`** (the
constant bookkeeping of the scalar split): on `{s ≤ 2M}` both tail arguments equal
`2M - s`; on `{s > 2M}` the two tails are `P̄_T(2M - s)` and `P̄_T(s - 2M)`, which sum
to `1` by evenness (`heatKernelTail_add_neg`). -/
theorem free_complement_eq (hT : 0 < T) (M : ℝ) :
    (1/2) * (∫ s : ℝ, backwardAiry T s * heatKernelTail T (2*M - s))
      + (1/2) * (∫ s : ℝ, backwardAiry T s * heatKernelTail T (2 * max M (s - M) - s))
      = (4*Real.pi*T)^(-1/2:ℝ) * rMinusMT M T + rPlusMT M T := by
  have hI1 := integrable_backwardAiry_mul_heatKernelTail_sub hT M
  have hI2 := integrable_backwardAiry_mul_heatKernelTail_max hT M
  -- split each whole-line integral at `2M`
  rw [← integral_add_compl measurableSet_Iic hI1, ← integral_add_compl measurableSet_Iic hI2,
    Set.compl_Iic]
  -- evaluate the pieces: on `{s ≤ 2M}` the two tail arguments coincide
  have hIic2 : (∫ s in Set.Iic (2*M), backwardAiry T s * heatKernelTail T (2 * max M (s - M) - s))
      = ∫ s in Set.Iic (2*M), backwardAiry T s * heatKernelTail T (2*M - s) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro s hs
    show backwardAiry T s * heatKernelTail T (2 * max M (s - M) - s)
        = backwardAiry T s * heatKernelTail T (2*M - s)
    rw [max_eq_left (by linarith [Set.mem_Iic.mp hs] : s - M ≤ M)]
  -- on `{s > 2M}` the tails are `P̄_T(2M - s)` and `P̄_T(s - 2M)`, summing to `g_T`
  have hIoi' : (∫ s in Set.Ioi (2*M), backwardAiry T s * heatKernelTail T (2*M - s))
      + ∫ s in Set.Ioi (2*M), backwardAiry T s * heatKernelTail T (2 * max M (s - M) - s)
      = ∫ s in Set.Ioi (2*M), backwardAiry T s := by
    rw [← integral_add hI1.integrableOn hI2.integrableOn]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    show backwardAiry T s * heatKernelTail T (2*M - s)
        + backwardAiry T s * heatKernelTail T (2 * max M (s - M) - s) = backwardAiry T s
    have hsM : M ≤ s - M := by linarith [Set.mem_Ioi.mp hs]
    rw [max_eq_right hsM, show 2 * (s - M) - s = s - 2*M by ring, ← mul_add,
      show s - 2*M = -(2*M - s) by ring, heatKernelTail_add_neg hT, mul_one]
  -- algebra: `(1/2)(A + B) + (1/2)(A + B') = A + (1/2)(B + B')`
  rw [hIic2]
  have halg : (1/2) * ((∫ s in Set.Iic (2*M), backwardAiry T s * heatKernelTail T (2*M - s))
        + (∫ s in Set.Ioi (2*M), backwardAiry T s * heatKernelTail T (2*M - s)))
      + (1/2) * ((∫ s in Set.Iic (2*M), backwardAiry T s * heatKernelTail T (2*M - s))
        + (∫ s in Set.Ioi (2*M), backwardAiry T s * heatKernelTail T (2 * max M (s - M) - s)))
      = (∫ s in Set.Iic (2*M), backwardAiry T s * heatKernelTail T (2*M - s))
        + (1/2) * ((∫ s in Set.Ioi (2*M), backwardAiry T s * heatKernelTail T (2*M - s))
          + (∫ s in Set.Ioi (2*M), backwardAiry T s * heatKernelTail T (2 * max M (s - M) - s))) := by
    ring
  rw [halg, hIoi']
  have hRminus : (∫ s in Set.Iic (2*M), backwardAiry T s * heatKernelTail T (2*M - s))
      = (4*Real.pi*T)^(-1/2:ℝ) * rMinusMT M T := by
    rw [const_mul_rMinusMT_eq hT M]
    apply setIntegral_congr_fun measurableSet_Iic
    intro s _
    exact mul_comm _ _
  rw [hRminus]
  rfl

/-- **The trace split `Tr Ã = I + R`**: the trace of the conjugated operator
splits as `Tr Ã_{M,T} = I_{M,T} + (4πT)^{-1/2} · R⁻_{M,T} + R⁺_{M,T}` (recall the
normalization convention: the paper's `R⁻` uses `P̄_T`, which is
`(4πT)^{-1/2} · gaussianTail`; hence the displayed factor on `rMinusMT`).

The plane trace integral (`trace_airyTilde_eq`) is partitioned over the reflected
region `{x ≤ M ∧ z ≤ M}` (evaluated by `reflected_integral_eq_iMT`) and the two
complementary regions `{M < x}` and `{x ≤ M ∧ M < z}` (evaluated by
`free_integral_Ioi_eval` / `free_integral_Iic_Ioi_eval`), and the pieces are combined
by `free_complement_eq`. -/
theorem trace_airyTilde_eq_split (hT : 0 < T) (hM : 0 < M) (ha : T + 1 ≤ a) :
    trace (airyTildeOp M T a hT hM ha)
      = iMT M T + (4*Real.pi*T)^(-1/2:ℝ) * rMinusMT M T + rPlusMT M T := by
  have hG : Integrable (fun p : ℝ × ℝ => qMT M T p.1 p.2 * backwardAiry T (p.2 + p.1))
      (volume.prod volume) := integrable_qMT_mul_backwardAiry hT hM ha
  -- integrability of the three pieces (each is an indicator of the global integrand)
  have hG1 : Integrable (fun p : ℝ × ℝ => {p : ℝ × ℝ | p.1 ≤ M ∧ p.2 ≤ M}.indicator
      (reflKernelFun M T) p) (volume.prod volume) := by
    have heq : {p : ℝ × ℝ | p.1 ≤ M ∧ p.2 ≤ M}.indicator (reflKernelFun M T)
        = {p : ℝ × ℝ | p.1 ≤ M ∧ p.2 ≤ M}.indicator
          (fun p : ℝ × ℝ => qMT M T p.1 p.2 * backwardAiry T (p.2 + p.1)) := by
      funext p
      by_cases hxz : p.1 ≤ M ∧ p.2 ≤ M
      · rw [Set.indicator_of_mem hxz _, Set.indicator_of_mem hxz _,
          qMT_eq_reflected hxz.1 hxz.2]
        rfl
      · rw [Set.indicator_of_notMem hxz _, Set.indicator_of_notMem hxz _]
    rw [heq]
    exact hG.indicator (measurableSet_reflectedRegion M)
  have hG2 : Integrable (fun p : ℝ × ℝ => {p : ℝ × ℝ | M < p.1}.indicator
      (freeKernelFun T) p) (volume.prod volume) := by
    have heq : {p : ℝ × ℝ | M < p.1}.indicator (freeKernelFun T)
        = {p : ℝ × ℝ | M < p.1}.indicator
          (fun p : ℝ × ℝ => qMT M T p.1 p.2 * backwardAiry T (p.2 + p.1)) := by
      funext p
      by_cases hx : M < p.1
      · rw [Set.indicator_of_mem hx _, Set.indicator_of_mem hx _,
          qMT_eq_free (fun h => not_lt_of_ge h.1 hx)]
        rfl
      · rw [Set.indicator_of_notMem hx _, Set.indicator_of_notMem hx _]
    rw [heq]
    exact hG.indicator (measurableSet_Ioi.preimage measurable_fst)
  have hG3 : Integrable (fun p : ℝ × ℝ => {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2}.indicator
      (freeKernelFun T) p) (volume.prod volume) := by
    have heq : {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2}.indicator (freeKernelFun T)
        = {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2}.indicator
          (fun p : ℝ × ℝ => qMT M T p.1 p.2 * backwardAiry T (p.2 + p.1)) := by
      funext p
      by_cases hxz : p.1 ≤ M ∧ M < p.2
      · rw [Set.indicator_of_mem hxz _, Set.indicator_of_mem hxz _,
          qMT_eq_free (fun h => not_lt_of_ge h.2 hxz.2)]
        rfl
      · rw [Set.indicator_of_notMem hxz _, Set.indicator_of_notMem hxz _]
    rw [heq]
    exact hG.indicator (measurableSet_Iic_Ioi_region M)
  -- the pointwise partition of the trace integrand over the three regions
  have hpart : ∀ p : ℝ × ℝ, qMT M T p.1 p.2 * backwardAiry T (p.2 + p.1)
      = {p : ℝ × ℝ | p.1 ≤ M ∧ p.2 ≤ M}.indicator (reflKernelFun M T) p
        + {p : ℝ × ℝ | M < p.1}.indicator (freeKernelFun T) p
        + {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2}.indicator (freeKernelFun T) p := by
    intro p
    by_cases h1 : p.1 ≤ M ∧ p.2 ≤ M
    · rw [Set.indicator_of_mem h1 _, qMT_eq_reflected h1.1 h1.2,
        Set.indicator_of_notMem (not_lt_of_ge h1.1 : ¬ M < p.1) _,
        Set.indicator_of_notMem (fun h => not_lt_of_ge h1.2 h.2 : ¬ (p.1 ≤ M ∧ M < p.2)) _]
      simp only [add_zero]
      rfl
    · by_cases h2 : M < p.1
      · rw [Set.indicator_of_notMem h1 _, qMT_eq_free h1, Set.indicator_of_mem h2 _,
          Set.indicator_of_notMem (fun h => not_lt_of_ge h.1 h2 : ¬ (p.1 ≤ M ∧ M < p.2)) _]
        simp only [zero_add, add_zero]
        rfl
      · have hx : p.1 ≤ M := le_of_not_gt h2
        have hz : M < p.2 := not_le.mp fun h => h1 ⟨hx, h⟩
        rw [Set.indicator_of_notMem h1 _, qMT_eq_free h1,
          Set.indicator_of_notMem (not_lt_of_ge hx : ¬ M < p.1) _,
          Set.indicator_of_mem (show p.1 ≤ M ∧ M < p.2 from ⟨hx, hz⟩) _]
        simp only [zero_add, add_zero]
        rfl
  -- the sum split of the plane integral
  have hsum : (∫ p : ℝ × ℝ, ({p : ℝ × ℝ | p.1 ≤ M ∧ p.2 ≤ M}.indicator (reflKernelFun M T) p
        + {p : ℝ × ℝ | M < p.1}.indicator (freeKernelFun T) p
        + {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2}.indicator (freeKernelFun T) p))
      = (∫ p : ℝ × ℝ, {p : ℝ × ℝ | p.1 ≤ M ∧ p.2 ≤ M}.indicator (reflKernelFun M T) p)
        + (∫ p : ℝ × ℝ, {p : ℝ × ℝ | M < p.1}.indicator (freeKernelFun T) p)
        + (∫ p : ℝ × ℝ, {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2}.indicator (freeKernelFun T) p) :=
    (integral_add (hG1.add hG2) hG3).trans
      (congrArg (fun X => X
          + ∫ p : ℝ × ℝ, {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2}.indicator (freeKernelFun T) p)
        (integral_add hG1 hG2))
  -- the three region integrals in iterated form
  have hJ1 : (∫ p : ℝ × ℝ, {p : ℝ × ℝ | p.1 ≤ M ∧ p.2 ≤ M}.indicator (reflKernelFun M T) p)
      = ∫ x in Set.Iic M, ∫ z in Set.Iic M,
        heatKernel T (2*M - x - z) * backwardAiry T (x + z) := by
    rw [MeasureTheory.integral_indicator (measurableSet_reflectedRegion M)]
    rw [show {p : ℝ × ℝ | p.1 ≤ M ∧ p.2 ≤ M} = Set.Iic M ×ˢ Set.Iic M from by
      ext ⟨x, z⟩
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic]]
    rw [show (volume : Measure (ℝ × ℝ)).restrict (Set.Iic M ×ˢ Set.Iic M)
        = (volume.restrict (Set.Iic M)).prod (volume.restrict (Set.Iic M)) from
      (Measure.prod_restrict _ _).symm]
    have hRint : Integrable (reflKernelFun M T)
        ((volume.restrict (Set.Iic M)).prod (volume.restrict (Set.Iic M))) := by
      rw [Measure.prod_restrict]
      exact (hG.integrableOn).congr_fun
        (fun p hp => congrArg (· * backwardAiry T (p.2 + p.1))
          (qMT_eq_reflected (Set.mem_prod.mp hp).1 (Set.mem_prod.mp hp).2))
        (measurableSet_Iic.prod measurableSet_Iic)
    exact (MeasureTheory.integral_prod _ hRint).trans (by
      apply setIntegral_congr_fun measurableSet_Iic
      intro x _
      apply setIntegral_congr_fun measurableSet_Iic
      intro z _
      show heatKernel T (2*M - x - z) * backwardAiry T (z + x)
          = heatKernel T (2*M - x - z) * backwardAiry T (x + z)
      rw [add_comm z x])
  have hJ2 : (∫ p : ℝ × ℝ, {p : ℝ × ℝ | M < p.1}.indicator (freeKernelFun T) p)
      = ∫ x in Set.Ioi M, ∫ z : ℝ, heatKernel T (x - z) * backwardAiry T (z + x) := by
    rw [MeasureTheory.integral_indicator (s := {p : ℝ × ℝ | M < p.1})
      (measurableSet_Ioi.preimage measurable_fst)]
    rw [show {p : ℝ × ℝ | M < p.1} = Set.Ioi M ×ˢ Set.univ from by
      ext ⟨x, z⟩
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true]]
    rw [show (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi M ×ˢ Set.univ)
        = (volume.restrict (Set.Ioi M)).prod (volume.restrict (Set.univ)) from
      (Measure.prod_restrict _ _).symm]
    rw [Measure.restrict_univ]
    exact MeasureTheory.integral_prod _ (integrable_freeKernelFun_Ioi_prod hT M)
  have hJ3 : (∫ p : ℝ × ℝ, {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2}.indicator (freeKernelFun T) p)
      = ∫ x in Set.Iic M, ∫ z in Set.Ioi M, heatKernel T (x - z) * backwardAiry T (z + x) := by
    rw [MeasureTheory.integral_indicator (measurableSet_Iic_Ioi_region M)]
    rw [show {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2} = Set.Iic M ×ˢ Set.Ioi M from by
      ext ⟨x, z⟩
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, Set.mem_Ioi]]
    rw [show (volume : Measure (ℝ × ℝ)).restrict (Set.Iic M ×ˢ Set.Ioi M)
        = (volume.restrict (Set.Iic M)).prod (volume.restrict (Set.Ioi M)) from
      (Measure.prod_restrict _ _).symm]
    exact MeasureTheory.integral_prod _ (integrable_freeKernelFun_Iic_prod_Ioi hT M)
  -- the full assembly
  calc trace (airyTildeOp M T a hT hM ha)
      = ∫ p : ℝ × ℝ, qMT M T p.1 p.2 * backwardAiry T (p.2 + p.1) := by
        rw [trace_airyTilde_eq hT hM ha]
        exact (MeasureTheory.integral_prod _ hG).symm
    _ = ∫ p : ℝ × ℝ, ({p : ℝ × ℝ | p.1 ≤ M ∧ p.2 ≤ M}.indicator (reflKernelFun M T) p
        + {p : ℝ × ℝ | M < p.1}.indicator (freeKernelFun T) p
        + {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2}.indicator (freeKernelFun T) p) :=
        integral_congr_ae (Filter.Eventually.of_forall hpart)
    _ = (∫ p : ℝ × ℝ, {p : ℝ × ℝ | p.1 ≤ M ∧ p.2 ≤ M}.indicator (reflKernelFun M T) p)
        + (∫ p : ℝ × ℝ, {p : ℝ × ℝ | M < p.1}.indicator (freeKernelFun T) p)
        + (∫ p : ℝ × ℝ, {p : ℝ × ℝ | p.1 ≤ M ∧ M < p.2}.indicator (freeKernelFun T) p) := hsum
    _ = iMT M T + (((1/2) * (∫ s : ℝ, backwardAiry T s * heatKernelTail T (2*M - s)))
        + ((1/2) * (∫ s : ℝ, backwardAiry T s * heatKernelTail T (2 * max M (s - M) - s)))) := by
        rw [hJ1, hJ2, hJ3, free_integral_Ioi_eval hT M, free_integral_Iic_Ioi_eval hT M,
          reflected_integral_eq_iMT hT M, add_assoc]
    _ = iMT M T + ((4*Real.pi*T)^(-1/2:ℝ) * rMinusMT M T + rPlusMT M T) := by
        rw [free_complement_eq hT M]
    _ = iMT M T + (4*Real.pi*T)^(-1/2:ℝ) * rMinusMT M T + rPlusMT M T := by
        rw [add_assoc]

end ScalarSplitMain

/-! ## The exact trace identity with the truncation error

Extending the two half-line pieces `I_{M,T}` and `R⁻_{M,T}` to the
full line evaluates them by the convolution identities `heat_airy_conv_moment`
and `heat_airy_conv_tail`; the `s > 2M` remainders combine with `R⁺` into
the explicit error `errorMT` (the paper's `ℰ_{M,T}`), using
`P̄_T(−b) = 1/2 + ∫_{[0,b]} p_T` (`heatKernelTail_neg_eq`, evenness of the heat
kernel). -/

section HeatExact

/-- The moment integrand `(A − s) p_T(A − s) g_T(s)` is integrable on `ℝ`. -/
theorem integrable_moment_integrand (hT : 0 < T) (A : ℝ) :
    Integrable (fun s : ℝ => (A - s) * heatKernel T (A - s) * backwardAiry T s)
      volume := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp T
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0 ⟨le_rfl, hT.le⟩ 0
    rw [abs_zero, mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have h4πT : (0:ℝ) < 4 * Real.pi * T := by positivity
  refine ((integrable_one_add_sq_mul_exp_neg_sq_add_abs (b := 1/(4*T)) (by positivity) T A).const_mul
      ((4*Real.pi*T)^(-1/2:ℝ) * C₀ * (2*(1 + A^2)))).mono'
    ((((continuous_const.sub continuous_id).mul
      ((continuous_heatKernel T).comp (continuous_const.sub continuous_id))).mul
      (continuous_backwardAiry_s T)).aestronglyMeasurable)
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (heatKernel_nonneg hT _)]
  calc |A - s| * heatKernel T (A - s) * |backwardAiry T s|
      ≤ (1 + (A - s)^2) * ((4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-(A - s)^2/(4*T)))
        * (C₀ * Real.exp (T * |s|)) := by
        apply mul_le_mul _ (hC₀ T ⟨hT.le, le_rfl⟩ s) (abs_nonneg _)
          (mul_nonneg (by positivity) (heatKernel_nonneg hT _))
        unfold heatKernel
        exact mul_le_mul (abs_le_one_add_sq (A - s)) le_rfl
          (by positivity) (by positivity)
    _ = ((4*Real.pi*T)^(-1/2:ℝ) * C₀) * ((1 + (A-s)^2)
          * Real.exp (-(A - s)^2/(4*T) + T*|s|)) := by
        rw [Real.exp_add]
        ring
    _ ≤ ((4*Real.pi*T)^(-1/2:ℝ) * C₀) * ((2*(1+A^2)) * (1+s^2)
          * Real.exp (-(A - s)^2/(4*T) + T*|s|)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have hsub : 1 + (A - s)^2 ≤ 2*(1+A^2)*(1+s^2) := by
          nlinarith [sq_nonneg (A - s), sq_nonneg (A + s), sq_nonneg A, sq_nonneg s,
            sq_nonneg (A * s)]
        calc 1 + (A - s)^2 ≤ 2*(1+A^2)*(1+s^2) := hsub
          _ = (2*(1+A^2)) * (1+s^2) := by ring
    _ = ((4*Real.pi*T)^(-1/2:ℝ) * C₀ * (2*(1 + A^2)))
        * ((1 + s^2) * Real.exp (-(1/(4*T))*(s - A)^2 + T*|s|)) := by
        rw [show -(A - s)^2/(4*T) = -(1/(4*T))*(s - A)^2 by ring]
        ring

/-- The tail integrand `P̄_T(A − s) g_T(s)` is integrable on `ℝ`. -/
theorem integrable_tail_integrand (hT : 0 < T) (A : ℝ) :
    Integrable (fun s : ℝ => heatKernelTail T (A - s) * backwardAiry T s) volume := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp_neg hT
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0
    rw [mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  obtain ⟨CT, hCTpos, hCT⟩ := heatKernelTail_le_exp_max_sq hT
  refine ((integrable_exp_neg_mul_exp_max_sq hT A).const_mul (C₀ * CT)).mono'
    ((((measurable_heatKernelTail hT).comp (measurable_const.sub measurable_id)).mul
      (continuous_backwardAiry_s T).measurable).aestronglyMeasurable)
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernelTail_nonneg hT _)]
  calc heatKernelTail T (A - s) * |backwardAiry T s|
      ≤ (CT * Real.exp (-(max (A - s) 0)^2 / (4 * T))) * (C₀ * Real.exp (-T * s)) :=
        mul_le_mul (hCT _) (hC₀ s) (abs_nonneg _)
          (mul_nonneg hCTpos.le (Real.exp_pos _).le)
    _ = (C₀ * CT) * (Real.exp (-T * s) * Real.exp (-(max (A - s) 0)^2 / (4 * T))) := by ring

/-- The shifted backward Airy kernel `b ↦ g_T(A + b)` is integrable on `(0, ∞)`. -/
theorem integrableOn_backwardAiry_shift_Ioi (hT : 0 < T) (A : ℝ) :
    IntegrableOn (fun b => backwardAiry T (A + b)) (Set.Ioi 0) volume := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp_neg hT
  refine ((exp_neg_integrableOn_Ioi 0 hT).const_mul (C₀ * Real.exp (-T * A))).mono'
    (((continuous_backwardAiry_s T).comp (continuous_const.add continuous_id)
      |>.measurable).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun b _ => ?_)
  rw [Real.norm_eq_abs]
  calc |backwardAiry T (A + b)| ≤ C₀ * Real.exp (-T * (A + b)) := hC₀ _
    _ = (C₀ * Real.exp (-T * A)) * Real.exp (-T * b) := by
        rw [show -T * (A + b) = -T * A + -T * b by ring, Real.exp_add]
        ring

/-- The integrand `b · p_T(b) · g_T(2M + b)` is integrable on `(0, ∞)`: the factor
`b` is absorbed by `b ≤ T⁻¹ e^{Tb}`, cancelling the `e^{-Tb}` decay of `g_T`. -/
theorem integrableOn_mul_heatKernel_backwardAiry_shift (hT : 0 < T) (M : ℝ) :
    IntegrableOn (fun b => b * heatKernel T b * backwardAiry T (2*M + b)) (Set.Ioi 0)
      volume := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp_neg hT
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0
    rw [mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have h4πT : (0:ℝ) < 4 * Real.pi * T := by positivity
  refine ((integrableOn_exp_neg_sq_div_Ioi hT 0).const_mul
      ((4*Real.pi*T)^(-1/2:ℝ) * T⁻¹ * C₀ * Real.exp (-T * (2*M)))).mono'
    (((measurable_id.mul ((continuous_heatKernel T).measurable)).mul
      (((continuous_backwardAiry_s T).measurable).comp
        (measurable_const.add measurable_id))).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun b hb => ?_)
  have hb0 : 0 ≤ b := (Set.mem_Ioi.mp hb).le
  have hbb : b ≤ T⁻¹ * Real.exp (T * b) := by
    have h := abs_pow_le_factorial_mul_exp 1 hT b
    rw [pow_one, abs_of_nonneg hb0, Nat.factorial_one, Nat.cast_one, one_div, pow_one] at h
    exact h
  unfold heatKernel
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hb0,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-b^2/(4*T)))]
  calc b * ((4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-b^2/(4*T))) * |backwardAiry T (2*M + b)|
      ≤ b * ((4*Real.pi*T)^(-1/2:ℝ) * Real.exp (-b^2/(4*T)))
        * (C₀ * Real.exp (-T * (2*M + b))) :=
        mul_le_mul_of_nonneg_left (hC₀ _)
          (mul_nonneg hb0 (by positivity))
    _ = (4*Real.pi*T)^(-1/2:ℝ) * C₀ * Real.exp (-T * (2*M))
        * ((b * Real.exp (-T * b)) * Real.exp (-b^2/(4*T))) := by
        rw [show -T * (2*M + b) = -T * (2*M) + -T * b by ring, Real.exp_add]
        ring
    _ ≤ (4*Real.pi*T)^(-1/2:ℝ) * C₀ * Real.exp (-T * (2*M))
        * ((T⁻¹ * Real.exp (T * b) * Real.exp (-T * b)) * Real.exp (-b^2/(4*T))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul hbb le_rfl
          (Real.exp_pos _).le (mul_nonneg (by positivity) (Real.exp_pos _).le)
    _ = ((4*Real.pi*T)^(-1/2:ℝ) * T⁻¹ * C₀ * Real.exp (-T * (2*M)))
        * Real.exp (-b^2/(4*T)) := by
        rw [show T⁻¹ * Real.exp (T * b) * Real.exp (-T * b)
            = T⁻¹ * (Real.exp (T * b) * Real.exp (-(T * b))) by
          rw [show -T * b = -(T * b) by ring, mul_assoc]]
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        ring

/-- The integrand `(1/2 + ∫_{[0,b]} p_T) · g_T(2M + b)` is integrable on `(0, ∞)`:
the bracket lies in `[1/2, 3/2]`. -/
theorem integrableOn_IccMass_mul_backwardAiry_shift (hT : 0 < T) (M : ℝ) :
    IntegrableOn (fun b => (1/2 + ∫ d in Set.Icc 0 b, heatKernel T d)
      * backwardAiry T (2*M + b)) (Set.Ioi 0) volume := by
  obtain ⟨C₀, hC₀⟩ := backwardAiry_abs_le_exp_neg hT
  have hC₀nn : 0 ≤ C₀ := by
    have h := hC₀ 0
    rw [mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hmeas : Measurable (fun b : ℝ => (1/2 + ∫ d in Set.Icc 0 b, heatKernel T d)
      * backwardAiry T (2*M + b)) := by
    have hIcc : ∀ b : ℝ, (∫ d in Set.Icc 0 b, heatKernel T d)
        = if 0 ≤ b then (1/2 - heatKernelTail T b) else 0 := by
      intro b
      by_cases hb : 0 ≤ b
      · rw [if_pos hb, integral_Icc_heatKernel hT hb]
      · rw [if_neg hb, show Set.Icc 0 b = ∅ from Set.Icc_eq_empty hb,
          setIntegral_empty]
    rw [show (fun b : ℝ => (1/2 + ∫ d in Set.Icc 0 b, heatKernel T d)
          * backwardAiry T (2*M + b))
        = fun b => (1/2 + (if 0 ≤ b then (1/2 - heatKernelTail T b) else 0))
          * backwardAiry T (2*M + b) from funext fun b => by rw [hIcc b]]
    exact ((measurable_const.add (Measurable.ite measurableSet_Ici
      (measurable_const.sub (measurable_heatKernelTail hT)) measurable_const)).mul
      ((continuous_backwardAiry_s T).measurable.comp (measurable_const.add measurable_id)))
  refine ((exp_neg_integrableOn_Ioi 0 hT).const_mul ((3/2) * C₀
      * Real.exp (-T * (2*M)))).mono'
    (hmeas.aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun b hb => ?_)
  have hb0 : 0 ≤ b := (Set.mem_Ioi.mp hb).le
  have hnn : (0:ℝ) ≤ ∫ d in Set.Icc 0 b, heatKernel T d :=
    setIntegral_nonneg measurableSet_Icc fun d _ => heatKernel_nonneg hT d
  have hle : ∫ d in Set.Icc 0 b, heatKernel T d ≤ 1 :=
    (setIntegral_le_integral (integrable_heatKernel hT)
      (ae_of_all _ fun d => heatKernel_nonneg hT d)).trans_eq (integral_heatKernel hT)
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 1/2 + ∫ d in Set.Icc 0 b, heatKernel T d)]
  calc (1/2 + ∫ d in Set.Icc 0 b, heatKernel T d) * |backwardAiry T (2*M + b)|
      ≤ (3/2) * (C₀ * Real.exp (-T * (2*M + b))) := by
        apply mul_le_mul _ (hC₀ _) (abs_nonneg _) (by positivity)
        linarith
    _ = ((3/2) * C₀ * Real.exp (-T * (2*M))) * Real.exp (-T * b) := by
        rw [show -T * (2*M + b) = -T * (2*M) + -T * b by ring, Real.exp_add]
        ring

/-- The truncation error `ℰ_{M,T}`:
`ℰ_{M,T} = ∫_{b>0} (b·p_T(b) − ∫_{[0,b]} p_T) · g_T(2M + b) db`. -/
noncomputable def errorMT (M T : ℝ) : ℝ :=
  ∫ b in Set.Ioi 0, (b * heatKernel T b - ∫ d in Set.Icc 0 b, heatKernel T d)
    * backwardAiry T (2*M + b)

/-- The error decomposition: shifting the three `s > 2M`
remainders to `b = s - 2M > 0` and using `P̄_T(−b) = 1/2 + ∫_{[0,b]} p_T` (evenness of
the heat kernel) plus `p_T(−b) = p_T(b)`. -/
theorem errorMT_eq (hT : 0 < T) (M : ℝ) :
    errorMT M T = rPlusMT M T
      - (∫ s in Set.Ioi (2*M), (2*M - s) * heatKernel T (2*M - s) * backwardAiry T s)
      - (∫ s in Set.Ioi (2*M), heatKernelTail T (2*M - s) * backwardAiry T s) := by
  have hshift : ∀ f : ℝ → ℝ, (∫ s in Set.Ioi (2*M), f s)
      = ∫ b in Set.Ioi 0, f (2*M + b) := by
    intro f
    have h := integral_Ioi_comp_add (0 : ℝ) (2*M) f
    rw [zero_add] at h
    exact h.symm
  have hshift_g : rPlusMT M T = ∫ b in Set.Ioi 0, (1/2) * backwardAiry T (2*M + b) := by
    show (1/2) * ∫ s in Set.Ioi (2*M), backwardAiry T s = _
    rw [← integral_const_mul, hshift (fun s => (1/2) * backwardAiry T s)]
  have hshift_I : (∫ s in Set.Ioi (2*M), (2*M - s) * heatKernel T (2*M - s)
        * backwardAiry T s)
      = ∫ b in Set.Ioi 0, -(b * heatKernel T b * backwardAiry T (2*M + b)) := by
    rw [hshift (fun s => (2*M - s) * heatKernel T (2*M - s) * backwardAiry T s)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro b _
    show (2*M - (2*M + b)) * heatKernel T (2*M - (2*M + b)) * backwardAiry T (2*M + b)
        = -(b * heatKernel T b * backwardAiry T (2*M + b))
    rw [show 2*M - (2*M + b) = -b by ring, show heatKernel T (-b) = heatKernel T b from
      heatKernel_even T b]
    ring
  have hshift_R : (∫ s in Set.Ioi (2*M), heatKernelTail T (2*M - s) * backwardAiry T s)
      = ∫ b in Set.Ioi 0, (1/2 + ∫ d in Set.Icc 0 b, heatKernel T d)
        * backwardAiry T (2*M + b) := by
    rw [hshift (fun s => heatKernelTail T (2*M - s) * backwardAiry T s)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro b hb
    show heatKernelTail T (2*M - (2*M + b)) * backwardAiry T (2*M + b)
        = (1/2 + ∫ d in Set.Icc 0 b, heatKernel T d) * backwardAiry T (2*M + b)
    rw [show 2*M - (2*M + b) = -b by ring,
      heatKernelTail_neg_eq hT (Set.mem_Ioi.mp hb).le]
  rw [show errorMT M T = ∫ b in Set.Ioi 0, (b * heatKernel T b
        - ∫ d in Set.Icc 0 b, heatKernel T d) * backwardAiry T (2*M + b) from rfl,
    hshift_g, hshift_I, hshift_R]
  have hP : IntegrableOn (fun b => (1/2) * backwardAiry T (2*M + b)) (Set.Ioi 0)
      volume := (integrableOn_backwardAiry_shift_Ioi hT (2*M)).const_mul _
  have hI := integrableOn_mul_heatKernel_backwardAiry_shift hT M
  have hR := integrableOn_IccMass_mul_backwardAiry_shift hT M
  have hcombine : (∫ b in Set.Ioi 0, (1/2) * backwardAiry T (2*M + b))
      - (∫ b in Set.Ioi 0, -(b * heatKernel T b * backwardAiry T (2*M + b)))
      - (∫ b in Set.Ioi 0, (1/2 + ∫ d in Set.Icc 0 b, heatKernel T d)
        * backwardAiry T (2*M + b))
      = ∫ b in Set.Ioi 0, (b * heatKernel T b - ∫ d in Set.Icc 0 b, heatKernel T d)
        * backwardAiry T (2*M + b) := by
    have hPI : IntegrableOn (fun b => (1/2) * backwardAiry T (2*M + b)
        + b * heatKernel T b * backwardAiry T (2*M + b)) (Set.Ioi 0) volume :=
      hP.add hI
    rw [integral_neg, sub_neg_eq_add, ← integral_add hP hI, ← integral_sub hPI hR]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro b _
    show (1/2) * backwardAiry T (2*M + b) + b * heatKernel T b * backwardAiry T (2*M + b)
        - (1/2 + ∫ d in Set.Icc 0 b, heatKernel T d) * backwardAiry T (2*M + b)
      = (b * heatKernel T b - ∫ d in Set.Icc 0 b, heatKernel T d) * backwardAiry T (2*M + b)
    ring
  exact hcombine.symm

/-- **The exact trace formula**: with `A = 2M`,
`Tr Ã_{M,T} = −2T·Ai'(2M) + ∫_{2M}^∞ Ai + ℰ_{M,T}`. -/
theorem trace_airyTilde_eq_heat_exact (hT : 0 < T) (hM : 0 < M) (ha : T + 1 ≤ a) :
    trace (airyTildeOp M T a hT hM ha)
      = -(2*T) * deriv airyAiReal (2*M) + (∫ u in Set.Ioi (2*M), airyAiReal u)
        + errorMT M T := by
  rw [trace_airyTilde_eq_split hT hM ha]
  have hsplit_I : iMT M T = (-(2*T) * deriv airyAiReal (2*M))
      - (∫ s in Set.Ioi (2*M), (2*M - s) * heatKernel T (2*M - s) * backwardAiry T s) := by
    have hI := integral_add_compl (s := Set.Iic (2*M)) measurableSet_Iic
      (integrable_moment_integrand hT (2*M))
    rw [Set.compl_Iic, heat_airy_conv_moment hT (2*M)] at hI
    rw [show (∫ s in Set.Iic (2*M), (2*M - s) * heatKernel T (2*M - s) * backwardAiry T s)
        = iMT M T from rfl] at hI
    exact eq_sub_of_add_eq hI
  have hsplit_R : (4*Real.pi*T)^(-1/2:ℝ) * rMinusMT M T
      = (∫ u in Set.Ioi (2*M), airyAiReal u)
        - (∫ s in Set.Ioi (2*M), heatKernelTail T (2*M - s) * backwardAiry T s) := by
    have hfull : (∫ s : ℝ, heatKernelTail T (2*M - s) * backwardAiry T s)
        = ∫ u in Set.Ioi (2*M), airyAiReal u := by
      rw [show (fun s : ℝ => heatKernelTail T (2*M - s) * backwardAiry T s)
          = fun s => (4*Real.pi*T)^(-1/2:ℝ) * (gaussianTail T (2*M - s) * backwardAiry T s)
          from funext fun s => by rw [heatKernelTail_eq_const_mul_gaussianTail]; ring]
      rw [integral_const_mul, heat_airy_conv_tail hT (2*M)]
      rw [Real.sqrt_eq_rpow, ← mul_assoc,
        ← Real.rpow_add (by positivity : (0:ℝ) < 4*Real.pi*T),
        show (-1/2 : ℝ) + 1/2 = 0 by norm_num, Real.rpow_zero, one_mul]
    have hR := integral_add_compl (s := Set.Iic (2*M)) measurableSet_Iic
      (integrable_tail_integrand hT (2*M))
    rw [Set.compl_Iic, hfull] at hR
    rw [← const_mul_rMinusMT_eq hT M] at hR
    exact eq_sub_of_add_eq hR
  rw [hsplit_I, hsplit_R, errorMT_eq hT M]
  ring

/-! ### The `O_T` remainder bound -/

/-- The heat kernel is decreasing on `[0, ∞)` (the Gaussian factor is). -/
theorem heatKernel_anti_on (hT : 0 < T) {d b : ℝ} (hd : 0 ≤ d) (hdb : d ≤ b) :
    heatKernel T b ≤ heatKernel T d := by
  have h4πT : (0:ℝ) < 4 * Real.pi * T := by positivity
  have h4T : (0:ℝ) < 4 * T := by positivity
  unfold heatKernel
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos h4πT _).le
  apply Real.exp_le_exp.mpr
  rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff_of_pos_right h4T]
  exact pow_le_pow_left₀ hd hdb 2

/-- The `errorMT` bracket bound: for `0 ≤ b` the heat kernel
decreases on `[0, b]`, so `b · p_T(b) ≤ ∫_{[0,b]} p_T`, while
`∫_{[0,b]} p_T ≤ ∫_{(0,∞)} p_T = 1/2`; hence the bracket
`b · p_T(b) − ∫_{[0,b]} p_T` lies in `[-1/2, 0]`. -/
theorem errorMT_bracket_abs_le (hT : 0 < T) {b : ℝ} (hb : 0 ≤ b) :
    |b * heatKernel T b - ∫ d in Set.Icc 0 b, heatKernel T d| ≤ 1/2 := by
  have hconst : ∫ _d in Set.Icc 0 b, heatKernel T b = b * heatKernel T b := by
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hb, sub_zero]
  have hmono : b * heatKernel T b ≤ ∫ d in Set.Icc 0 b, heatKernel T d := by
    rw [← hconst]
    exact setIntegral_mono_on (continuous_const.continuousOn.integrableOn_Icc)
      (integrable_heatKernel hT).integrableOn measurableSet_Icc
      (fun d hd => heatKernel_anti_on hT (Set.mem_Icc.mp hd).1 (Set.mem_Icc.mp hd).2)
  have hle : ∫ d in Set.Icc 0 b, heatKernel T d ≤ 1/2 := by
    rw [integral_Icc_heatKernel hT hb]
    linarith [heatKernelTail_nonneg hT b]
  have hnn : (0:ℝ) ≤ b * heatKernel T b := mul_nonneg hb (heatKernel_nonneg hT b)
  rw [abs_le]
  constructor <;> linarith

/-- The tangent-line minorant of the convex function `x ↦ x^{3/2}` at `A > 0`, with
the true slope `(3/2)√A`: `A^{3/2} + (3/2)√A · u ≤ (A + u)^{3/2}` for `0 ≤ u`.
Proved elementarily by squaring: `(A+u)³ − A(A + 3u/2)² = (3/4)Au² + u³ ≥ 0`.  This is
the convexity input for the `e^{-(T + √(2M)) b}` decay in `errorMT_abs_le`; the coarser slope-`√A`
minorant would lose the factor `e^{-√A·b}`
that drives the `M^{-3/4}` prefactor. -/
theorem rpow_three_halves_add_le {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) :
    A^(3/2:ℝ) + (3/2) * A^(1/2:ℝ) * u ≤ (A + u)^(3/2:ℝ) := by
  have hAu : (0:ℝ) < A + u := by linarith
  have key : ∀ x : ℝ, 0 < x → x^(3/2:ℝ) = x * √x := by
    intro x hx
    rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hx, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [← Real.sqrt_eq_rpow, key A hA, key (A + u) hAu]
  apply le_of_pow_le_pow_left₀ (show (2:ℕ) ≠ 0 by norm_num)
    (mul_nonneg hAu.le (Real.sqrt_nonneg _))
  rw [mul_pow, Real.sq_sqrt hAu.le]
  have hL : (A * √A + (3/2) * √A * u)^2 = A * (A + (3/2) * u)^2 := by
    rw [show A * √A + (3/2) * √A * u = √A * (A + (3/2) * u) by ring, mul_pow,
      Real.sq_sqrt hA.le]
  rw [hL]
  nlinarith [sq_nonneg u, hA.le, hu, mul_nonneg hA.le (sq_nonneg u), pow_nonneg hu 3]

/-- The shifted backward-Airy bound behind the error estimate: for
`A = 2M` with `1 ≤ M` and `0 ≤ b`,
`|g_T(A + b)| ≤ C₁ · A^{-1/4} · e^{-TA − (2/3)A^{3/2}} · e^{-(T + √A)·b}` — from
`airyAiReal_le` at `A + b + T²`, antitonicity of `·^{−1/4}`, the convexity minorant
`rpow_three_halves_add_le`, and `e^{-(2/3)T³ − √A·T²} ≤ 1`. -/
theorem backwardAiry_shift_abs_le (hT : 0 < T) {C₁ : ℝ} (hC₁nn : 0 ≤ C₁)
    (hC₁ : ∀ x : ℝ, 1 ≤ x →
      airyAiReal x ≤ C₁ * x^(-1/4:ℝ) * Real.exp (-(2/3 * x^(3/2:ℝ))))
    {M : ℝ} (hM : 1 ≤ M) {b : ℝ} (hb : 0 ≤ b) :
    |backwardAiry T (2*M + b)| ≤ C₁ * (2*M)^(-1/4:ℝ)
      * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ))
      * Real.exp (-(T + (2*M)^(1/2:ℝ)) * b) := by
  have hA : (0:ℝ) < 2*M := by linarith
  have hsa : (0:ℝ) ≤ (2*M)^(1/2:ℝ) := Real.rpow_nonneg hA.le _
  have hX1 : 1 ≤ 2*M + b + T^2 := by linarith [sq_nonneg T]
  have hX0 : (0:ℝ) ≤ 2*M + b + T^2 := by linarith [sq_nonneg T]
  have hAi := hC₁ _ hX1
  have hAipos : (0:ℝ) ≤ airyAiReal (2*M + b + T^2) := (airyAiReal_pos_of_nonneg hX0).le
  have hconv0 : (2*M)^(3/2:ℝ) + (3/2) * (2*M)^(1/2:ℝ) * (b + T^2)
      ≤ (2*M + b + T^2)^(3/2:ℝ) := by
    rw [show 2*M + b + T^2 = 2*M + (b + T^2) by ring]
    exact rpow_three_halves_add_le hA (add_nonneg hb (sq_nonneg T))
  have hconv : -(2/3 * (2*M + b + T^2)^(3/2:ℝ))
      ≤ -(2/3 * ((2*M)^(3/2:ℝ) + (3/2) * (2*M)^(1/2:ℝ) * (b + T^2))) :=
    neg_le_neg_iff.mpr (mul_le_mul_of_nonneg_left hconv0 (by norm_num : (0:ℝ) ≤ 2/3))
  have hrpow : (2*M + b + T^2)^(-1/4:ℝ) ≤ (2*M)^(-1/4:ℝ) :=
    Real.rpow_le_rpow_of_nonpos hA (by linarith [sq_nonneg T]) (by norm_num)
  have hexp : Real.exp (-(2/3)*T^3 - T*(2*M + b))
        * Real.exp (-(2/3 * (2*M + b + T^2)^(3/2:ℝ)))
      ≤ Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ))
        * Real.exp (-(T + (2*M)^(1/2:ℝ)) * b) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hT3 : (0:ℝ) ≤ T^3 := pow_nonneg hT.le 3
    have hsT2 : (0:ℝ) ≤ (2*M)^(1/2:ℝ) * T^2 := mul_nonneg hsa (sq_nonneg T)
    linarith [hconv]
  unfold backwardAiry
  rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg hAipos]
  calc Real.exp (-(2/3)*T^3 - T*(2*M + b)) * airyAiReal (2*M + b + T^2)
      ≤ Real.exp (-(2/3)*T^3 - T*(2*M + b))
        * (C₁ * (2*M)^(-1/4:ℝ) * Real.exp (-(2/3 * (2*M + b + T^2)^(3/2:ℝ)))) :=
        mul_le_mul_of_nonneg_left (hAi.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpow hC₁nn) (Real.exp_pos _).le))
          (Real.exp_pos _).le
    _ = C₁ * (2*M)^(-1/4:ℝ) * (Real.exp (-(2/3)*T^3 - T*(2*M + b))
        * Real.exp (-(2/3 * (2*M + b + T^2)^(3/2:ℝ)))) := by ring
    _ ≤ C₁ * (2*M)^(-1/4:ℝ) * (Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ))
        * Real.exp (-(T + (2*M)^(1/2:ℝ)) * b)) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hC₁nn (Real.rpow_nonneg hA.le _))
    _ = C₁ * (2*M)^(-1/4:ℝ) * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ))
        * Real.exp (-(T + (2*M)^(1/2:ℝ)) * b) := by ring

/-- **The `O_T` remainder bound**: for `0 < T` there is
a constant `C_T > 0` (depending only on `T`) such that for all `1 ≤ M`,

  `|ℰ_{M,T}| ≤ C_T · M^{-3/4} · exp(-T·(2M) − (2/3)(2M)^{3/2})`.

Route: the bracket lies in `[-1/2, 0]` (`errorMT_bracket_abs_le`); with `A = 2M` and
`a = √A`, `backwardAiry_shift_abs_le` gives
`|g_T(A + b)| ≤ C₁ A^{-1/4} e^{-TA − (2/3)A^{3/2}} e^{-(T + a)b}`; and
`∫_0^∞ e^{-(T+a)b} db = (T+a)^{-1} ≤ a^{-1}` — the EXACT value of the integral via
`integral_exp_mul_Ioi` is needed here: bounding it by `1` would lose the decisive
factor `a^{-1}` (since `M^{-1/4} ≰ M^{-3/4}` for large `M`).  The prefactor is then
`(1/2) C₁ A^{-1/4} a^{-1} = (1/2) C₁ (2M)^{-3/4} = 2^{-3/4} C₁ M^{-3/4} / 2`, absorbed
into `C_T := 2^{-3/4} C₁ / 2`.  The exponent `(2/3)(2M)^{3/2} = (4√2/3) M^{3/2}
= κ M^{3/2}` is exactly the one of `ρ(M) = C_* M^{1/4} e^{-κ M^{3/2}}`, so
`errorMT = o(ρ(M)/M)` is a downstream calculation. -/
theorem errorMT_abs_le (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M →
      |errorMT M T| ≤ C * M^(-3/4:ℝ) * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ)) := by
  obtain ⟨C₁, hC₁⟩ := airyAiReal_le
  have hC₁pos : 0 < C₁ := by
    have h1 := hC₁ 1 le_rfl
    rw [Real.one_rpow, Real.one_rpow, mul_one] at h1
    exact pos_of_mul_pos_left ((airyAiReal_pos one_pos).trans_le h1) (Real.exp_pos _).le
  refine ⟨2^(-3/4:ℝ)/2 * C₁, by positivity, fun M hM => ?_⟩
  have hA : (0:ℝ) < 2*M := by linarith
  have hsa : (0:ℝ) < (2*M)^(1/2:ℝ) := Real.rpow_pos_of_pos hA _
  have hTsa : (0:ℝ) < T + (2*M)^(1/2:ℝ) := by positivity
  -- the error integrand is integrable: pointwise it is the difference of the three
  -- pieces already proved integrable for `errorMT_eq`
  have hInt : IntegrableOn (fun b => (b * heatKernel T b
        - ∫ d in Set.Icc 0 b, heatKernel T d) * backwardAiry T (2*M + b))
      (Set.Ioi 0) volume := by
    have hP := (integrableOn_backwardAiry_shift_Ioi hT (2*M)).const_mul (1/2 : ℝ)
    have hI := integrableOn_mul_heatKernel_backwardAiry_shift hT M
    have hR := integrableOn_IccMass_mul_backwardAiry_shift hT M
    apply IntegrableOn.congr_fun ((hP.add hI).sub hR) _ measurableSet_Ioi
    intro b _
    show (1/2) * backwardAiry T (2*M + b) + b * heatKernel T b * backwardAiry T (2*M + b)
        - (1/2 + ∫ d in Set.Icc 0 b, heatKernel T d) * backwardAiry T (2*M + b)
      = (b * heatKernel T b - ∫ d in Set.Icc 0 b, heatKernel T d) * backwardAiry T (2*M + b)
    ring
  have hshift : ∀ b : ℝ, 0 ≤ b → |backwardAiry T (2*M + b)| ≤
      C₁ * (2*M)^(-1/4:ℝ) * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ))
        * Real.exp (-(T + (2*M)^(1/2:ℝ)) * b) :=
    fun b hb => backwardAiry_shift_abs_le hT hC₁pos.le hC₁ hM hb
  have hexpint : ∫ b in Set.Ioi (0:ℝ), Real.exp (-(T + (2*M)^(1/2:ℝ)) * b)
      = (T + (2*M)^(1/2:ℝ))⁻¹ := by
    have h := integral_exp_mul_Ioi (a := -(T + (2*M)^(1/2:ℝ)))
      (neg_neg_iff_pos.mpr hTsa) 0
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq] at h
    rw [h, one_div]
  have hinv : (T + (2*M)^(1/2:ℝ))⁻¹ ≤ ((2*M)^(1/2:ℝ))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hsa (le_add_of_nonneg_left hT.le)
  have hpow : (2*M)^(-1/4:ℝ) * ((2*M)^(1/2:ℝ))⁻¹ = (2*M)^(-3/4:ℝ) := by
    rw [← Real.rpow_neg hA.le, ← Real.rpow_add hA,
      show (-1/4 : ℝ) + -(1/2) = -3/4 by norm_num]
  have hsplit : (2*M)^(-3/4:ℝ) = (2:ℝ)^(-3/4:ℝ) * M^(-3/4:ℝ) :=
    Real.mul_rpow (by norm_num) (by linarith)
  calc |errorMT M T| = |∫ b in Set.Ioi 0, (b * heatKernel T b
          - ∫ d in Set.Icc 0 b, heatKernel T d) * backwardAiry T (2*M + b)| := rfl
    _ ≤ ∫ b in Set.Ioi 0, ‖(b * heatKernel T b - ∫ d in Set.Icc 0 b, heatKernel T d)
          * backwardAiry T (2*M + b)‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ b in Set.Ioi 0, ((1/2) * C₁ * (2*M)^(-1/4:ℝ)
          * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ)))
          * Real.exp (-(T + (2*M)^(1/2:ℝ)) * b) := by
        refine setIntegral_mono_on hInt.norm
          ((exp_neg_integrableOn_Ioi 0 hTsa).const_mul _) measurableSet_Ioi fun b hb => ?_
        have hb0 := (Set.mem_Ioi.mp hb).le
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |b * heatKernel T b - ∫ d in Set.Icc 0 b, heatKernel T d|
              * |backwardAiry T (2*M + b)|
            ≤ (1/2) * (C₁ * (2*M)^(-1/4:ℝ) * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ))
              * Real.exp (-(T + (2*M)^(1/2:ℝ)) * b)) :=
            mul_le_mul (errorMT_bracket_abs_le hT hb0) (hshift b hb0)
              (abs_nonneg _) (by norm_num)
          _ = ((1/2) * C₁ * (2*M)^(-1/4:ℝ) * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ)))
              * Real.exp (-(T + (2*M)^(1/2:ℝ)) * b) := by ring
    _ = ((1/2) * C₁ * (2*M)^(-1/4:ℝ) * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ)))
          * ∫ b in Set.Ioi 0, Real.exp (-(T + (2*M)^(1/2:ℝ)) * b) :=
        integral_const_mul _ _
    _ = ((1/2) * C₁ * (2*M)^(-1/4:ℝ) * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ)))
          * (T + (2*M)^(1/2:ℝ))⁻¹ := by rw [hexpint]
    _ ≤ (2^(-3/4:ℝ)/2 * C₁) * M^(-3/4:ℝ)
          * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ)) := by
        calc ((1/2) * C₁ * (2*M)^(-1/4:ℝ) * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ)))
              * (T + (2*M)^(1/2:ℝ))⁻¹
            ≤ ((1/2) * C₁ * (2*M)^(-1/4:ℝ) * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ)))
              * ((2*M)^(1/2:ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = (1/2) * C₁ * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ))
              * ((2*M)^(-1/4:ℝ) * ((2*M)^(1/2:ℝ))⁻¹) := by ring
          _ = (1/2) * C₁ * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ))
              * (2*M)^(-3/4:ℝ) := by rw [hpow]
          _ = (1/2) * C₁ * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ))
              * ((2:ℝ)^(-3/4:ℝ) * M^(-3/4:ℝ)) := by rw [hsplit]
          _ = (2^(-3/4:ℝ)/2 * C₁) * M^(-3/4:ℝ)
              * Real.exp (-T*(2*M) - (2/3)*(2*M)^(3/2:ℝ)) := by ring

end HeatExact

end AiryConj
