/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.SmallWeight.TwoTimeDefectRev

/-!
# The two-time defect at small weight, explicit in the truncation level

The weight-parametric two-time defect bounds (`airy1FinCdf_twoTime_defect_le`,
`airy1FinCdf_twoTime_defect_rev_le`) specialised to the small-weight frame of the lower-boundedness
argument: for a truncation level `M ≥ 2`, padding `τ = 1/M`, `S = t + τ`, weight `w = 2S`,
lower level `−m₀ = −2M` and gaps `0 < t ≤ 1/(2M)`,
`|G − F| ≤ C_M e^{−(b−a)²/(8t)}` in both orders, with the explicit constant
`C_M = exp(K M^{5/2})` (`smallWeightDefectConst`, `K = smallWeightK`), so
`log C_M = K M^{5/2} = o(M³)` (`log_smallWeightDefectConst`, `isLittleO_log_smallWeightDefectConst`,
`tendsto_log_smallWeightDefectConst_div`).

Ingredients, all at `w = 2S`, `S ∈ (1/M, 3/(2M)]`, so `wM ∈ (2, 3]` and every exponent
`(2t+τ)w², w m₀, t w², S w²` is `O(1)`:
* `‖W_{S,2S}‖₂² ≤ C_W e^{−(10/3)S³}/S ≤ C_W M` (a relaxed form of the paper's
  Hilbert–Schmidt bound for `W`, `hsNorm_wKernel_le_small`; its hypothesis `2S ≤ S + 1`
  holds since `S ≤ 3/4`): `hsNorm_wKernel_smallWeight_le`;
* `C_D ≤ 4 e^{65} M²` (`defectConst_smallWeight_le`; `1 + 2/w² ≤ M²`, `c₀(2t+τ) ≤ c₀(t)`);
* `C₁ ≤ 4 e^{65} M⁴` (`oneTimeConst_smallWeight_le`; `c₀(S) ≤ 1 + 1/(4πS) ≤ 2M`,
  `1/w ≤ M/2`);
* the Simon-type assembly `2PE e^{6P} ≤ e^{8P} E` with `P = √(8 e^{65} C_W M⁵)`.

The bounds hold only for gaps `t ≤ 1/(2M)` (the route needs `w > S ≥ t` at weight `w ≍ 1/M`);
the main library's `FwdDefectBound` / `RevDefectBound` quantify `0 < t ≤ 1`, so the gap-restricted shapes
`FwdDefectBoundOn L δ C` / `RevDefectBoundOn L δ C` are defined here (`…On L 1 C` is
definitionally main's form).
-/

namespace AiryFdd

open MeasureTheory Real Filter Asymptotics
open HilbertSchmidt

/-! ## Gap-restricted defect-bound shapes -/

/-- Forward two-time defect bound at lower level `L`, for gaps `0 < t ≤ δ`, with constant `C`
(main's `FwdDefectBound L C` is `FwdDefectBoundOn L 1 C`). -/
def FwdDefectBoundOn (L δ C : ℝ) : Prop :=
  ∀ (x t a b : ℝ) (y : ({x, x + t} : Finset ℝ) → ℝ), 0 < t → t ≤ δ →
    L ≤ a → a ≤ b → (∀ h, y ⟨x, h⟩ = a) → (∀ h, y ⟨x + t, h⟩ = b) →
    |airy1FinCdf {x} (fun _ => a) - airy1FinCdf {x, x + t} y|
      ≤ C * Real.exp (-(b - a) ^ 2 / (8 * t))

/-- Reverse two-time defect bound at lower level `L`, for gaps `0 < t ≤ δ`, with constant `C`
(main's `RevDefectBound L C` is `RevDefectBoundOn L 1 C`). -/
def RevDefectBoundOn (L δ C : ℝ) : Prop :=
  ∀ (x t a b : ℝ) (y : ({x, x + t} : Finset ℝ) → ℝ), 0 < t → t ≤ δ →
    L ≤ b → b ≤ a → (∀ h, y ⟨x, h⟩ = a) → (∀ h, y ⟨x + t, h⟩ = b) →
    |airy1FinCdf {x + t} (fun _ => b) - airy1FinCdf {x, x + t} y|
      ≤ C * Real.exp (-(a - b) ^ 2 / (8 * t))

theorem FwdDefectBoundOn.mono {L δ C L' δ' C' : ℝ} (H : FwdDefectBoundOn L δ C) (hL : L ≤ L')
    (hδ : δ' ≤ δ) (hC : C ≤ C') : FwdDefectBoundOn L' δ' C' := by
  intro x t a b y ht htδ ha hab hya hyb
  exact (H x t a b y ht (htδ.trans hδ) (hL.trans ha) hab hya hyb).trans
    (mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le)

theorem RevDefectBoundOn.mono {L δ C L' δ' C' : ℝ} (H : RevDefectBoundOn L δ C) (hL : L ≤ L')
    (hδ : δ' ≤ δ) (hC : C ≤ C') : RevDefectBoundOn L' δ' C' := by
  intro x t a b y ht htδ hb hba hya hyb
  exact (H x t a b y ht (htδ.trans hδ) (hL.trans hb) hba hya hyb).trans
    (mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le)

/-! ## Elementary bounds -/

/-- `c₀(S)² = 1/(4πS)`. -/
theorem c0_sq {S : ℝ} (hS : 0 < S) : c0 S ^ 2 = 1 / (4 * Real.pi * S) := by
  have hx : 0 < 4 * Real.pi * S := by positivity
  unfold c0
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num
  rw [Real.rpow_neg_one]
  ring

/-- `c₀(S) ≤ 1 + 1/(4πS)`. -/
theorem c0_le_one_add {S : ℝ} (hS : 0 < S) : c0 S ≤ 1 + 1 / (4 * Real.pi * S) := by
  rw [← c0_sq hS]
  nlinarith [sq_nonneg (c0 S - 1 / 2)]

/-- **Simon-type assembly**: if `X N ≤ P` and `Y N ≤ P` (all nonnegative), then
`2 (X N) E e^{2(XN + 2YN)} ≤ e^{8P} E`. -/
theorem defect_assembly_le {X Y N P E : ℝ} (hX : 0 ≤ X) (hN : 0 ≤ N) (hE : 0 ≤ E)
    (hXP : X * N ≤ P) (hYP : Y * N ≤ P) :
    2 * (X * N) * E * Real.exp (2 * (X * N + 2 * (Y * N))) ≤ Real.exp (8 * P) * E := by
  have hXN : 0 ≤ X * N := mul_nonneg hX hN
  have hP : 0 ≤ P := hXN.trans hXP
  have h1 : Real.exp (2 * (X * N + 2 * (Y * N))) ≤ Real.exp (6 * P) :=
    Real.exp_le_exp.2 (by linarith)
  have h2 : 2 * P ≤ Real.exp (2 * P) := by linarith [Real.add_one_le_exp (2 * P)]
  have h3 : Real.exp (8 * P) = Real.exp (2 * P) * Real.exp (6 * P) := by
    rw [← Real.exp_add]; ring_nf
  have he6 := (Real.exp_pos (6 * P)).le
  calc 2 * (X * N) * E * Real.exp (2 * (X * N + 2 * (Y * N)))
      ≤ 2 * P * E * Real.exp (6 * P) := by gcongr
    _ ≤ Real.exp (2 * P) * E * Real.exp (6 * P) := by gcongr
    _ = Real.exp (8 * P) * E := by rw [h3]; ring

/-! ## The small-weight parameters -/

/-- The elementary facts about the small-weight frame `τ = 1/M`, `S = t + τ`, `w = 2S`, for
`M ≥ 2`, `0 < t ≤ 1/(2M)`. -/
theorem smallWeight_params {M t : ℝ} (hM : 2 ≤ M) (ht : 0 < t) (htM : t ≤ 1 / (2 * M)) :
    1 ≤ (t + 1 / M) * M ∧ (t + 1 / M) * M ≤ 3 / 2 ∧ t + 1 / M ≤ 3 / 4 ∧
      2 * t + 1 / M ≤ 1 ∧ t ≤ 1 / 4 := by
  have hM0 : 0 < M := by linarith
  have h1 : t * (2 * M) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at htM
  have hτ : 1 / M * M = 1 := by field_simp
  have hS : (t + 1 / M) * M = t * M + 1 := by rw [add_mul, hτ]
  have htM' : t * M ≤ 1 / 2 := by nlinarith
  have htM0 : 0 ≤ t * M := by positivity
  refine ⟨by linarith, by linarith, ?_, ?_, ?_⟩
  · nlinarith
  · have : (2 * t + 1 / M) * M ≤ 2 := by rw [add_mul, hτ]; nlinarith
    nlinarith
  · nlinarith

/-- `1 + 2/w² ≤ M²` when `w M ≥ 2`, `M ≥ 2`. -/
theorem one_add_two_div_sq_le {w M : ℝ} (hM : 2 ≤ M) (hw : 0 < w) (hwM : 2 ≤ w * M) :
    1 + 2 / w ^ 2 ≤ M ^ 2 := by
  have h : 2 / w ^ 2 ≤ M ^ 2 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_self_le_mul_self (by norm_num) hwM]
  nlinarith

/-- **The defect constant at small weight**: `C_D(2S, t, 1/M, 2M) ≤ 4 e^{65} M²`. -/
theorem defectConst_smallWeight_le {M t : ℝ} (hM : 2 ≤ M) (ht : 0 < t)
    (htM : t ≤ 1 / (2 * M)) :
    defectConst (2 * (t + 1 / M)) t (1 / M) (2 * M) ≤ 4 * Real.exp 65 * M ^ 2 := by
  obtain ⟨hS1, hS2, hS34, h2t, ht4⟩ := smallWeight_params hM ht htM
  have hM0 : 0 < M := by linarith
  have hτ : 0 < 1 / M := by positivity
  set w := 2 * (t + 1 / M) with hwdef
  have hw0 : 0 < w := by positivity
  have hwM : 2 ≤ w * M := by rw [hwdef]; nlinarith
  have hw32 : w ≤ 3 / 2 := by rw [hwdef]; linarith
  have hwm6 : w * (2 * M) ≤ 6 := by rw [hwdef]; nlinarith
  have hw2 : w ^ 2 ≤ 9 / 4 := by nlinarith
  have hw2' : 0 ≤ w ^ 2 := sq_nonneg w
  have hA : (2 * t + 1 / M) * w ^ 2 ≤ 9 / 4 := by nlinarith
  have hB : t * w ^ 2 ≤ 9 / 16 := by nlinarith
  have hct := c0_pos ht
  have hr : c0 (2 * t + 1 / M) * (1 + 2 / w ^ 2) / c0 t ≤ M ^ 2 := by
    rw [div_le_iff₀ hct]
    have h1 := c0_anti ht (show t ≤ 2 * t + 1 / M by linarith)
    have h2 := one_add_two_div_sq_le hM hw0 hwM
    have h3 := c0_pos (show 0 < 2 * t + 1 / M by positivity)
    calc c0 (2 * t + 1 / M) * (1 + 2 / w ^ 2) ≤ c0 t * M ^ 2 :=
          mul_le_mul h1 h2 (by positivity) hct.le
      _ = M ^ 2 * c0 t := by ring
  have e1 : Real.exp ((2 * t + 1 / M) * w ^ 2 + 3 * w * (2 * M) + 9 * t * w ^ 2)
      ≤ Real.exp 65 := Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (9 * (2 * t + 1 / M) * w ^ 2 + 5 * w * (2 * M) + 25 * t * w ^ 2)
      ≤ Real.exp 65 := Real.exp_le_exp.2 (by nlinarith)
  unfold defectConst
  calc 2 * (c0 (2 * t + 1 / M) * (1 + 2 / w ^ 2) / c0 t) *
        (Real.exp ((2 * t + 1 / M) * w ^ 2 + 3 * w * (2 * M) + 9 * t * w ^ 2)
          + Real.exp (9 * (2 * t + 1 / M) * w ^ 2 + 5 * w * (2 * M) + 25 * t * w ^ 2))
      ≤ 2 * M ^ 2 * (Real.exp 65 + Real.exp 65) := by gcongr
    _ = 4 * Real.exp 65 * M ^ 2 := by ring

/-- `c₀(S) ≤ 2M` for `S ≥ 1/M` (`S M ≥ 1`), `M ≥ 1`. -/
theorem c0_le_two_mul {S M : ℝ} (hM : 1 ≤ M) (hS : 0 < S) (hSM : 1 ≤ S * M) : c0 S ≤ 2 * M := by
  have h := c0_le_one_add hS
  have h2 : 1 / (4 * Real.pi * S) ≤ M := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  linarith

/-- **The one-time constant at small weight**: `C₁(2S, S, 2M) ≤ 4 e^{65} M⁴`. -/
theorem oneTimeConst_smallWeight_le {M t : ℝ} (hM : 2 ≤ M) (ht : 0 < t)
    (htM : t ≤ 1 / (2 * M)) :
    oneTimeConst (2 * (t + 1 / M)) (t + 1 / M) (2 * M) ≤ 4 * Real.exp 65 * M ^ 4 := by
  obtain ⟨hS1, hS2, hS34, h2t, ht4⟩ := smallWeight_params hM ht htM
  have hM0 : 0 < M := by linarith
  set S := t + 1 / M with hSdef
  have hS0 : 0 < S := by positivity
  set w := 2 * S with hwdef
  have hw0 : 0 < w := by positivity
  have hwM : 2 ≤ w * M := by rw [hwdef]; nlinarith
  have hw32 : w ≤ 3 / 2 := by rw [hwdef]; linarith
  have hwm6 : w * (2 * M) ≤ 6 := by rw [hwdef]; nlinarith
  have hw2 : w ^ 2 ≤ 9 / 4 := by nlinarith
  have hw2' : 0 ≤ w ^ 2 := sq_nonneg w
  have hA : S * w ^ 2 ≤ 27 / 16 := by nlinarith
  have hc := c0_le_two_mul (by linarith) hS0 hS1
  have hr := one_add_two_div_sq_le hM hw0 hwM
  have hE65 := Real.exp_pos 65
  have f1 : Real.exp (S * w ^ 2) * Real.exp (3 * w * (2 * M)) / (3 * w) ≤ Real.exp 65 * M := by
    rw [div_le_iff₀ (by positivity), ← Real.exp_add]
    have e : Real.exp (S * w ^ 2 + 3 * w * (2 * M)) ≤ Real.exp 65 :=
      Real.exp_le_exp.2 (by nlinarith)
    have : Real.exp 65 * 1 ≤ Real.exp 65 * (M * (3 * w)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hE65.le
    nlinarith
  have f2 : Real.exp (9 * S * w ^ 2) * Real.exp (5 * w * (2 * M)) / (5 * w)
      ≤ Real.exp 65 * M := by
    rw [div_le_iff₀ (by positivity), ← Real.exp_add]
    have e : Real.exp (9 * S * w ^ 2 + 5 * w * (2 * M)) ≤ Real.exp 65 :=
      Real.exp_le_exp.2 (by nlinarith)
    have : Real.exp 65 * 1 ≤ Real.exp 65 * (M * (5 * w)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hE65.le
    nlinarith
  have hc0 := c0_pos hS0
  unfold oneTimeConst
  calc c0 S * (1 + 2 / w ^ 2) * (Real.exp (S * w ^ 2) * Real.exp (3 * w * (2 * M)) / (3 * w)
        + Real.exp (9 * S * w ^ 2) * Real.exp (5 * w * (2 * M)) / (5 * w))
      ≤ (2 * M) * M ^ 2 * (Real.exp 65 * M + Real.exp 65 * M) := by gcongr
    _ = 4 * Real.exp 65 * M ^ 4 := by ring

/-! ## The `W` norm at weight `2S` -/

/-- The constant `C_W` of the relaxed Hilbert–Schmidt bound for `W` (a fixed choice from `hsNorm_wKernel_le_small`). -/
noncomputable def smallWeightCW : ℝ := hsNorm_wKernel_le_small.choose

theorem smallWeightCW_pos : 0 < smallWeightCW := hsNorm_wKernel_le_small.choose_spec.1

/-- **`‖W_{S,2S}‖₂ ≤ √(C_W M)`** in the small-weight frame. -/
theorem hsNorm_wKernel_smallWeight_le {M t : ℝ} (hM : 2 ≤ M) (ht : 0 < t)
    (htM : t ≤ 1 / (2 * M)) (hw : t + 1 / M < 2 * (t + 1 / M)) :
    hsNorm (kernelOperator (memLp_wKernel_lt hw)) ≤ Real.sqrt (smallWeightCW * M) := by
  obtain ⟨hS1, hS2, hS34, -, -⟩ := smallWeight_params hM ht htM
  have hM0 : 0 < M := by linarith
  refine (hsNorm_wKernel_le_small.choose_spec.2 (t + 1 / M) (2 * (t + 1 / M)) hw
    (by linarith)).trans (Real.sqrt_le_sqrt ?_)
  have hS0 : 0 < t + 1 / M := by positivity
  have hCW := smallWeightCW_pos
  change smallWeightCW * Real.exp ((2 / 3) * (t + 1 / M) ^ 3
      - 2 * (2 * (t + 1 / M)) * (t + 1 / M) ^ 2) / (2 * (t + 1 / M) - (t + 1 / M))
    ≤ smallWeightCW * M
  rw [div_le_iff₀ (by linarith)]
  have he : Real.exp ((2 / 3) * (t + 1 / M) ^ 3 - 2 * (2 * (t + 1 / M)) * (t + 1 / M) ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [pow_pos hS0 3])
  have h1 : smallWeightCW * Real.exp ((2 / 3) * (t + 1 / M) ^ 3
      - 2 * (2 * (t + 1 / M)) * (t + 1 / M) ^ 2) ≤ smallWeightCW * 1 :=
    mul_le_mul_of_nonneg_left he hCW.le
  have h2 : smallWeightCW * 1 ≤ smallWeightCW * ((t + 1 / M) * M) :=
    mul_le_mul_of_nonneg_left hS1 hCW.le
  nlinarith

/-! ## The explicit constant -/

/-- `A = 8 e^{65} C_W`. -/
noncomputable def smallWeightA : ℝ := 8 * Real.exp 65 * smallWeightCW

/-- The growth coefficient `K = 8 √A = 8 √(8 e^{65} C_W)`. -/
noncomputable def smallWeightK : ℝ := 8 * Real.sqrt smallWeightA

/-- **The explicit small-weight defect constant** `C_M = exp(K M^{5/2})`
(written `exp(K · M² √M)`). -/
noncomputable def smallWeightDefectConst (M : ℝ) : ℝ :=
  Real.exp (smallWeightK * (M ^ 2 * Real.sqrt M))

theorem smallWeightA_pos : 0 < smallWeightA := by
  have := smallWeightCW_pos; unfold smallWeightA; positivity

theorem smallWeightK_pos : 0 < smallWeightK := by
  have := smallWeightA_pos; unfold smallWeightK; positivity

theorem smallWeightDefectConst_pos (M : ℝ) : 0 < smallWeightDefectConst M := Real.exp_pos _

/-- `8 √(A M⁵) = K M² √M`. -/
theorem eight_sqrt_smallWeightA_mul (M : ℝ) :
    8 * Real.sqrt (smallWeightA * M ^ 5) = smallWeightK * (M ^ 2 * Real.sqrt M) := by
  have h5 : M ^ 5 = (M ^ 2) ^ 2 * M := by ring
  rw [h5, Real.sqrt_mul smallWeightA_pos.le, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]
  unfold smallWeightK; ring

/-- The three `√C · N` bounds in the small-weight frame, all by `P = √(A M⁵)`. -/
theorem smallWeight_sqrt_bounds {M t : ℝ} (hM : 2 ≤ M) (ht : 0 < t) (htM : t ≤ 1 / (2 * M)) :
    Real.sqrt (defectConst (2 * (t + 1 / M)) t (1 / M) (2 * M)) * Real.sqrt (smallWeightCW * M)
        ≤ Real.sqrt (smallWeightA * M ^ 5) ∧
      Real.sqrt (oneTimeConst (2 * (t + 1 / M)) (t + 1 / M) (2 * M))
          * Real.sqrt (smallWeightCW * M) ≤ Real.sqrt (smallWeightA * M ^ 5) ∧
      Real.sqrt (defectConst (2 * (t + 1 / M)) t (1 / M) (2 * M)
          + oneTimeConst (2 * (t + 1 / M)) (t + 1 / M) (2 * M))
          * Real.sqrt (smallWeightCW * M) ≤ Real.sqrt (smallWeightA * M ^ 5) := by
  have hM0 : 0 < M := by linarith
  have hτ : 0 < 1 / M := by positivity
  have hS0 : 0 < t + 1 / M := by positivity
  have hD0 := defectConst_nonneg (w := 2 * (t + 1 / M)) (m₀ := 2 * M) ht hτ
  have h10 := oneTimeConst_nonneg (S := t + 1 / M) (w := 2 * (t + 1 / M)) (m₀ := 2 * M) hS0
    (by positivity)
  have hD := defectConst_smallWeight_le hM ht htM
  have h1 := oneTimeConst_smallWeight_le hM ht htM
  have hCW := smallWeightCW_pos
  have hE := Real.exp_pos 65
  have hQ : 0 < Real.exp 65 * smallWeightCW := mul_pos hE hCW
  have h24 : M ^ 2 ≤ M ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h35 : M ^ 3 ≤ M ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hM5 : 0 < M ^ 5 := by positivity
  have key : ∀ X : ℝ, 0 ≤ X → X ≤ 8 * Real.exp 65 * M ^ 4 →
      Real.sqrt X * Real.sqrt (smallWeightCW * M) ≤ Real.sqrt (smallWeightA * M ^ 5) := by
    intro X hX0 hX
    rw [← Real.sqrt_mul hX0]
    apply Real.sqrt_le_sqrt
    have : X * (smallWeightCW * M) ≤ (8 * Real.exp 65 * M ^ 4) * (smallWeightCW * M) :=
      mul_le_mul_of_nonneg_right hX (by positivity)
    unfold smallWeightA
    calc X * (smallWeightCW * M) ≤ (8 * Real.exp 65 * M ^ 4) * (smallWeightCW * M) := this
      _ = 8 * Real.exp 65 * smallWeightCW * M ^ 5 := by ring
  refine ⟨key _ hD0 ?_, key _ h10 ?_, key _ (add_nonneg hD0 h10) ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-! ## The small-weight defect bounds -/

/-- **Forward two-time defect at small weight**: for `M ≥ 2`, all `x`, gaps
`0 < t ≤ 1/(2M)` and levels `−2M ≤ a ≤ b`,
`|F_{{x}}(a) − F_{{x,x+t}}(a, b)| ≤ C_M e^{−(b−a)²/(8t)}`, `C_M = exp(K M^{5/2})`
(frame `τ = 1/M`, `w = 2(t + τ)`). -/
theorem smallWeight_fwdDefectBoundOn {M : ℝ} (hM : 2 ≤ M) :
    FwdDefectBoundOn (-(2 * M)) (1 / (2 * M)) (smallWeightDefectConst M) := by
  intro x t a b y ht htM ha hab hya hyb
  have hM0 : 0 < M := by linarith
  have hτ : 0 < 1 / M := by positivity
  have hw : t + 1 / M < 2 * (t + 1 / M) := by linarith
  have hN := hsNorm_wKernel_smallWeight_le hM ht htM hw
  obtain ⟨hD, h1, -⟩ := smallWeight_sqrt_bounds hM ht htM
  refine (airy1FinCdf_twoTime_defect_le ht hτ hw hN ha hab y hya hyb).trans ?_
  refine (defect_assembly_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.exp_pos _).le hD h1).trans (le_of_eq ?_)
  unfold smallWeightDefectConst
  rw [eight_sqrt_smallWeightA_mul M]

/-- **Reverse two-time defect at small weight**: for `M ≥ 2`, all `x`, gaps
`0 < t ≤ 1/(2M)` and levels `−2M ≤ b ≤ a`,
`|F_{{x+t}}(b) − F_{{x,x+t}}(a, b)| ≤ C_M e^{−(a−b)²/(8t)}`, `C_M = exp(K M^{5/2})`. -/
theorem smallWeight_revDefectBoundOn {M : ℝ} (hM : 2 ≤ M) :
    RevDefectBoundOn (-(2 * M)) (1 / (2 * M)) (smallWeightDefectConst M) := by
  intro x t a b y ht htM hb hba hya hyb
  have hM0 : 0 < M := by linarith
  have hτ : 0 < 1 / M := by positivity
  have hw : t + 1 / M < 2 * (t + 1 / M) := by linarith
  have hN := hsNorm_wKernel_smallWeight_le hM ht htM hw
  obtain ⟨hD, -, h2⟩ := smallWeight_sqrt_bounds hM ht htM
  refine (airy1FinCdf_twoTime_defect_rev_le ht hτ hw hN hb hba y hya hyb).trans ?_
  refine (defect_assembly_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.exp_pos _).le hD h2).trans (le_of_eq ?_)
  unfold smallWeightDefectConst
  rw [eight_sqrt_smallWeightA_mul M]

/-! ## Growth of the constant: `log C_M = K M^{5/2} = o(M³)` -/

theorem log_smallWeightDefectConst (M : ℝ) :
    Real.log (smallWeightDefectConst M) = smallWeightK * (M ^ 2 * Real.sqrt M) := by
  unfold smallWeightDefectConst; rw [Real.log_exp]

/-- `log C_M = K M^{5/2}` (real power) for `M ≥ 0`. -/
theorem log_smallWeightDefectConst_eq_rpow {M : ℝ} (hM : 0 ≤ M) :
    Real.log (smallWeightDefectConst M) = smallWeightK * M ^ (5 / 2 : ℝ) := by
  rw [log_smallWeightDefectConst, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_add' hM (by norm_num)]
  norm_num

/-- **`log C_M = o(M³)`**. -/
theorem isLittleO_log_smallWeightDefectConst :
    (fun M : ℝ => Real.log (smallWeightDefectConst M)) =o[atTop] (fun M : ℝ => M ^ 3) := by
  refine IsLittleO.of_bound fun c hc => ?_
  filter_upwards [eventually_ge_atTop (max 0 ((smallWeightK / c) ^ 2))] with M hM
  have hM0 : 0 ≤ M := le_trans (le_max_left _ _) hM
  have hKc : smallWeightK / c ≤ Real.sqrt M := by
    calc smallWeightK / c = Real.sqrt ((smallWeightK / c) ^ 2) :=
          (Real.sqrt_sq (div_pos smallWeightK_pos hc).le).symm
      _ ≤ Real.sqrt M := Real.sqrt_le_sqrt (le_trans (le_max_right _ _) hM)
  have hK : smallWeightK ≤ c * Real.sqrt M := by rwa [div_le_iff₀ hc, mul_comm] at hKc
  have hs := Real.sqrt_nonneg M
  have hss : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM0
  rw [log_smallWeightDefectConst, Real.norm_of_nonneg (by have := smallWeightK_pos; positivity),
    Real.norm_of_nonneg (by positivity)]
  calc smallWeightK * (M ^ 2 * Real.sqrt M) ≤ (c * Real.sqrt M) * (M ^ 2 * Real.sqrt M) :=
        mul_le_mul_of_nonneg_right hK (by positivity)
    _ = c * M ^ 2 * (Real.sqrt M * Real.sqrt M) := by ring
    _ = c * M ^ 3 := by rw [hss]; ring

/-- `log C_M / M³ → 0`. -/
theorem tendsto_log_smallWeightDefectConst_div :
    Tendsto (fun M : ℝ => Real.log (smallWeightDefectConst M) / M ^ 3) atTop (nhds 0) :=
  isLittleO_log_smallWeightDefectConst.tendsto_div_nhds_zero

/-- **Headline**: there is `K > 0` such that for every `M ≥ 2`, with
`C_M = exp(K M^{5/2})`, the forward and reverse two-time defect bounds hold at lower level
`−2M` for all gaps `0 < t ≤ 1/(2M)`; and `log C_M = o(M³)`. -/
theorem smallWeight_defect_headline :
    ∃ K : ℝ, 0 < K ∧
      (∀ M : ℝ, 2 ≤ M →
        FwdDefectBoundOn (-(2 * M)) (1 / (2 * M)) (Real.exp (K * M ^ (5 / 2 : ℝ))) ∧
        RevDefectBoundOn (-(2 * M)) (1 / (2 * M)) (Real.exp (K * M ^ (5 / 2 : ℝ)))) ∧
      (fun M : ℝ => K * M ^ (5 / 2 : ℝ)) =o[atTop] (fun M : ℝ => M ^ 3) := by
  refine ⟨smallWeightK, smallWeightK_pos, fun M hM => ?_, ?_⟩
  · have hM0 : (0 : ℝ) ≤ M := by linarith
    have he : Real.exp (smallWeightK * M ^ (5 / 2 : ℝ)) = smallWeightDefectConst M := by
      rw [← log_smallWeightDefectConst_eq_rpow hM0, Real.exp_log (smallWeightDefectConst_pos M)]
    rw [he]
    exact ⟨smallWeight_fwdDefectBoundOn hM, smallWeight_revDefectBoundOn hM⟩
  · refine isLittleO_log_smallWeightDefectConst.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 0] with M hM
    exact log_smallWeightDefectConst_eq_rpow hM

end AiryFdd
