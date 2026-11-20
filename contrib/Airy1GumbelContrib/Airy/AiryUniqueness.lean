/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Airy.AiryBessel

open MeasureTheory Set Filter
open scoped Topology

/-!
# Abstract uniqueness for the Airy ODE on the half-line

Part of the Airy–Bessel identity route (see `Airy/AiryBessel.lean` for
the overall strategy). A function `W : ℝ → ℝ`, continuous on `[0, ∞)`, differentiable
on `(0, ∞)` with `(W')'(x) = x W x` there, satisfying `W 0 = 0` and
`(W h − W 0)/h → 0` as `h → 0⁺`, vanishes identically on `(0, ∞)`.  This is the
uniqueness half of the ODE bridge for DLMF 9.6.1: applied to `W = y − π Ai` with
`y = airyBesselY` it yields `airyBesselY = π · airyAiReal` on `(0, ∞)`.

Proof: Grönwall (`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`) applied to
the pair `u = (W, W')`.  The work is to show, from the ODE and the slope hypothesis:
`W'(0) = 0`, right-continuity of `W'` at `0` (via `W'(a) → L` and `L = 0` by the mean
value theorem), `W'(h) = ∫₀ʰ t W(t) dt`, and the slope limit of `u` at `0`.
-/

section AiryODEUniqueness

variable {W : ℝ → ℝ} (hW0 : W 0 = 0) (hcont : ContinuousOn W (Set.Ici 0))
  (hdiff : ∀ x ∈ Set.Ioi 0, DifferentiableAt ℝ W x)
  (hW'' : ∀ x ∈ Set.Ioi 0, HasDerivAt (deriv W) (x * W x) x)
  (hslopes : Tendsto (fun h => (W h - W 0) / h) (𝓝[>] (0:ℝ)) (𝓝 0))
  {M : ℝ} (hM : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖W t‖ ≤ M)

include hcont hW'' in
/-- FTC on `[a, b]`, `0 < a ≤ b`: `∫ t in a..b, t W t = W'(b) − W'(a)`. -/
private theorem airyODE_ftc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, t * W t = deriv W b - deriv W a := by
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (deriv W) (x * W x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hW'' x (Set.mem_Ioi.mpr (ha.trans_le hx.1))
  have hint : IntervalIntegrable (fun t => t * W t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_id.mul (hcont.mono (fun x hx => ha.le.trans hx.1))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

include hcont hM in
/-- `∫ t in a..b, t W t → ∫ t in 0..b, t W t` as `a → 0⁺` (for `0 < b ≤ 1`). -/
private theorem airyODE_int_lim {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    Tendsto (fun a => ∫ t in a..b, t * W t) (𝓝[>] (0:ℝ))
      (𝓝 (∫ t in 0..b, t * W t)) := by
  have hint : ∀ {c d : ℝ}, 0 ≤ c → c ≤ d → d ≤ 1 →
      IntervalIntegrable (fun t => t * W t) volume c d := by
    intro c d hc hcd hd
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hcd]
    exact continuousOn_id.mul (hcont.mono (fun x hx => hc.trans hx.1))
  have hsmall : Tendsto (fun a => ∫ t in 0..a, t * W t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun a : ℝ => M * a) (Eventually.of_forall fun a => norm_nonneg _)
    · filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)]
        with a ha ha1
      have hbound : ‖∫ t in 0..a, t * W t‖ ≤ M * |a - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        rw [uIoc_of_le ha.le] at ht
        have htM : ‖W t‖ ≤ M := hM t ⟨ht.1.le, ht.2.trans ha1.le⟩
        calc ‖t * W t‖ = |t| * ‖W t‖ := by
              rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
          _ ≤ 1 * M := mul_le_mul (by rw [abs_of_pos ht.1]; exact ht.2.trans ha1.le) htM
              (norm_nonneg _) zero_le_one
          _ = M := one_mul M
      rw [sub_zero, abs_of_pos ha] at hbound
      exact hbound
    · have hM' : Tendsto (fun a : ℝ => M * a) (𝓝 (0:ℝ)) (𝓝 (M * 0)) :=
        (continuousAt_id.const_mul M).tendsto
      rw [mul_zero] at hM'
      exact hM'.mono_left nhdsWithin_le_nhds
  have hsplit : (fun a => ∫ t in a..b, t * W t) =ᶠ[𝓝[>] (0:ℝ)]
      fun a => (∫ t in 0..b, t * W t) - ∫ t in 0..a, t * W t := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hb)] with a ha hab2
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hint (le_refl 0) ha.le (hab2.le.trans hb1)) (hint ha.le hab2.le hb1)
    rw [eq_sub_iff_add_eq, add_comm]
    exact h
  have hmain : Tendsto (fun a => (∫ t in 0..b, t * W t) - ∫ t in 0..a, t * W t)
      (𝓝[>] (0:ℝ)) (𝓝 ((∫ t in 0..b, t * W t) - 0)) := tendsto_const_nhds.sub hsmall
  rw [sub_zero] at hmain
  exact Tendsto.congr' hsplit.symm hmain

include hcont hW'' hM in
/-- `deriv W a → L := deriv W 1 − ∫₀¹ t W t` along `𝓝[>] 0`. -/
private theorem airyODE_deriv_lim :
    Tendsto (deriv W) (𝓝[>] (0:ℝ)) (𝓝 (deriv W 1 - ∫ t in 0..1, t * W t)) := by
  have heq : deriv W =ᶠ[𝓝[>] (0:ℝ)] fun a => deriv W 1 - ∫ t in a..1, t * W t := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with a ha ha1
    have h := airyODE_ftc hcont hW'' ha ha1.le
    rw [h]; ring
  have hlim := airyODE_int_lim hcont hM one_pos (le_refl 1)
  have hmain : Tendsto (fun a => deriv W 1 - ∫ t in a..1, t * W t) (𝓝[>] (0:ℝ))
      (𝓝 (deriv W 1 - ∫ t in 0..1, t * W t)) := tendsto_const_nhds.sub hlim
  exact Tendsto.congr' heq.symm hmain

include hcont hdiff hW'' hslopes hM in
/-- The limit `L` vanishes: `deriv W a → 0` along `𝓝[>] 0` (mean value theorem on `W`
composed with the deriv-limit). -/
private theorem airyODE_deriv_lim_zero :
    Tendsto (deriv W) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hderWL := airyODE_deriv_lim hcont hW'' hM
  set L := deriv W 1 - ∫ t in 0..1, t * W t with hLdef
  have hMVT : ∀ h : ℝ, ∃ ξ : ℝ, 0 < h →
      (ξ ∈ Set.Ioo 0 h ∧ deriv W ξ = (W h - W 0) / (h - 0)) := by
    intro h
    by_cases hh : 0 < h
    · obtain ⟨ξ, hξmem, hξeq⟩ := exists_deriv_eq_slope W hh
        (hcont.mono Set.Icc_subset_Ici_self)
        (fun x hx => (hdiff x (Set.Ioo_subset_Ioi_self hx)).differentiableWithinAt)
      exact ⟨ξ, fun _ => ⟨hξmem, hξeq⟩⟩
    · exact ⟨0, fun h0 => absurd h0 hh⟩
  choose ξ hξ using hMVT
  have hξT0 : Tendsto ξ (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero' (g := fun h : ℝ => h)
    · filter_upwards [self_mem_nhdsWithin] with h hh using (hξ h hh).1.1.le
    · filter_upwards [self_mem_nhdsWithin] with h hh using (hξ h hh).1.2.le
    · exact tendsto_id.mono_left nhdsWithin_le_nhds
  have hξTI : Tendsto ξ (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hξT0, by filter_upwards [self_mem_nhdsWithin] with h hh using (hξ h hh).1.1⟩
  have hcomp : Tendsto (fun h => deriv W (ξ h)) (𝓝[>] (0:ℝ)) (𝓝 L) := hderWL.comp hξTI
  have heq : (fun h => deriv W (ξ h)) =ᶠ[𝓝[>] (0:ℝ)] fun h => (W h - W 0) / h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [(hξ h hh).2, sub_zero]
  have hcomp' : Tendsto (fun h => (W h - W 0) / h) (𝓝[>] (0:ℝ)) (𝓝 L) :=
    Tendsto.congr' heq hcomp
  have hL : L = 0 := tendsto_nhds_unique hcomp' hslopes
  rwa [hL] at hderWL

include hcont hdiff hW'' hslopes hM in
/-- `W'(0) = 0`. -/
private theorem airyODE_deriv_zero : deriv W 0 = 0 := by
  have hderW0 := airyODE_deriv_lim_zero hcont hdiff hW'' hslopes hM
  by_cases h0d : DifferentiableAt ℝ W 0
  · have hs := h0d.hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hs
    have hs' : Tendsto (slope W 0) (𝓝[>] (0:ℝ)) (𝓝 (deriv W 0)) := by
      apply hs.mono_left
      apply nhdsWithin_mono
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx
    have heq2 : slope W 0 =ᶠ[𝓝[>] (0:ℝ)] fun h => (W h - W 0) / h := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      show (h - 0)⁻¹ • (W h -ᵥ W 0) = (W h - W 0) / h
      rw [sub_zero, vsub_eq_sub, smul_eq_mul, div_eq_inv_mul]
    have hs'' : Tendsto (fun h => (W h - W 0) / h) (𝓝[>] (0:ℝ)) (𝓝 (deriv W 0)) :=
      Tendsto.congr' heq2 hs'
    exact tendsto_nhds_unique hs'' hslopes
  · exact deriv_zero_of_not_differentiableAt h0d

include hW0 hcont hdiff hW'' hslopes in
/-- **Uniqueness for the Airy equation on the half-line** (step 6): a solution `W` of
`W'' = x W` on `(0, ∞)`, continuous on `[0, ∞)`, with `W(0) = 0` and vanishing right
slope at `0`, is identically zero on `(0, ∞)`. -/
theorem airy_ode_uniqueness {x : ℝ} (hx : 0 < x) : W x = 0 := by
  -- the uniform bound of `‖W‖` on `[0, 1]`
  have hWcont01 : ContinuousOn (fun t => ‖W t‖) (Set.Icc 0 1) :=
    (hcont.mono Set.Icc_subset_Ici_self).norm
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) hWcont01
  have hM : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖W t‖ ≤ ‖W x₀‖ := by
    intro t ht
    exact Filter.eventually_principal.mp hmax t ht
  have hderW0lim := airyODE_deriv_lim_zero hcont hdiff hW'' hslopes hM
  have hdW0 : deriv W 0 = 0 := airyODE_deriv_zero hcont hdiff hW'' hslopes hM
  -- value of `deriv W` on `(0, 1]`
  have hD : ∀ h ∈ Set.Ioc (0:ℝ) 1, deriv W h = ∫ t in 0..h, t * W t := by
    intro h hh
    have h1 : Tendsto (fun a => ∫ t in a..h, t * W t) (𝓝[>] (0:ℝ))
        (𝓝 (∫ t in 0..h, t * W t)) := airyODE_int_lim hcont hM hh.1 hh.2
    have heq : (fun a => ∫ t in a..h, t * W t) =ᶠ[𝓝[>] (0:ℝ)]
        fun a => deriv W h - deriv W a := by
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hh.1)] with a ha hah
      exact airyODE_ftc hcont hW'' ha hah.le
    have h2 : Tendsto (fun a => deriv W h - deriv W a) (𝓝[>] (0:ℝ))
        (𝓝 (deriv W h - 0)) := tendsto_const_nhds.sub hderW0lim
    have h1' := Tendsto.congr' heq h1
    have huniq := tendsto_nhds_unique h1' h2
    linarith [huniq]
  -- the quadratic bound on `deriv W`
  have hE : ∀ h ∈ Set.Ioc (0:ℝ) 1, ‖deriv W h‖ ≤ h^2 * ‖W x₀‖ := by
    intro h hh
    rw [hD h hh]
    have hbound : ‖∫ t in 0..h, t * W t‖ ≤ (h * ‖W x₀‖) * |h - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le hh.1.le] at ht
      have htM : ‖W t‖ ≤ ‖W x₀‖ := hM t ⟨ht.1.le, ht.2.trans hh.2⟩
      calc ‖t * W t‖ = |t| * ‖W t‖ := by rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        _ ≤ h * ‖W x₀‖ := mul_le_mul (by rw [abs_of_pos ht.1]; exact ht.2) htM (norm_nonneg _) hh.1.le
    rw [sub_zero, abs_of_pos hh.1] at hbound
    calc ‖∫ t in 0..h, t * W t‖ ≤ h * ‖W x₀‖ * h := hbound
      _ = h^2 * ‖W x₀‖ := by ring
  -- right-continuity of `deriv W` at `0`
  have hderWcont0 : ContinuousWithinAt (deriv W) (Set.Ici 0) 0 := by
    have hIci : Set.Ici (0:ℝ) = insert 0 (Set.Ioi 0) := by
      ext x
      simp only [Set.mem_Ici, Set.mem_insert_iff, Set.mem_Ioi]
      constructor
      · intro h; rcases h.eq_or_lt with rfl | h
        · exact Or.inl rfl
        · exact Or.inr h
      · rintro (rfl | h)
        · exact le_refl 0
        · exact h.le
    have hpure : Tendsto (deriv W) (pure (0:ℝ)) (𝓝 (deriv W 0)) := tendsto_pure_nhds _ _
    have hderW0lim' : Tendsto (deriv W) (𝓝[>] (0:ℝ)) (𝓝 (deriv W 0)) := by
      simpa only [hdW0] using hderW0lim
    show Tendsto (deriv W) (𝓝[Set.Ici 0] 0) (𝓝 (deriv W 0))
    rw [hIci, nhdsWithin_insert, tendsto_sup]
    exact ⟨hpure, hderW0lim'⟩
  -- the pair `u = (W, W')`
  set u : ℝ → ℝ × ℝ := fun x => (W x, deriv W x) with hu
  have hucont : ContinuousOn u (Set.Ici 0) := by
    apply ContinuousOn.prodMk hcont
    intro t ht
    have ht0 : 0 ≤ t := ht
    rcases ht0.eq_or_lt with rfl | htpos
    · exact hderWcont0
    · exact (hW'' t (Set.mem_Ioi.mpr htpos)).continuousAt.continuousWithinAt
  -- the slope limit of `u` at `0`
  have hstep8 : HasDerivWithinAt u (0, 0) (Set.Ici 0) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hset : Set.Ici (0:ℝ) \ {0} = Set.Ioi 0 := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
      constructor
      · rintro ⟨h0, h1⟩
        exact lt_of_le_of_ne h0 (Ne.symm h1)
      · intro h
        exact ⟨h.le, ne_of_gt h⟩
    rw [hset, nhds_prod_eq]
    have hslope : slope u 0 =ᶠ[𝓝[>] (0:ℝ)] fun h => (h⁻¹ * W h, h⁻¹ * deriv W h) := by
      apply Eventually.of_forall
      intro h
      show (h - 0)⁻¹ • (u h -ᵥ u 0) = _
      rw [sub_zero, vsub_eq_sub, hu]
      show h⁻¹ • ((W h, deriv W h) - (W 0, deriv W 0)) = _
      rw [hW0, hdW0, Prod.mk_sub_mk, sub_zero, sub_zero, Prod.smul_def,
        smul_eq_mul, smul_eq_mul]
    have hcoord1 : Tendsto (fun h : ℝ => h⁻¹ * W h) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have heq : (fun h : ℝ => h⁻¹ * W h) = fun h => (W h - W 0) / h := by
        funext h
        rw [hW0, sub_zero, div_eq_inv_mul]
      rw [heq]
      exact hslopes
    have hcoord2 : Tendsto (fun h : ℝ => h⁻¹ * deriv W h) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      apply squeeze_zero' (g := fun h : ℝ => ‖W x₀‖ * h)
        (Eventually.of_forall fun h => norm_nonneg _)
      · filter_upwards [self_mem_nhdsWithin,
          eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)]
          with h hh hh1
        have hb := hE h ⟨hh, hh1.le⟩
        calc ‖h⁻¹ * deriv W h‖ = h⁻¹ * ‖deriv W h‖ := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hh), Real.norm_eq_abs]
          _ ≤ h⁻¹ * (h^2 * ‖W x₀‖) :=
            mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.mpr hh))
          _ = ‖W x₀‖ * h := by
              rw [pow_two, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hh),
                one_mul, mul_comm]
      · have hM' : Tendsto (fun h : ℝ => ‖W x₀‖ * h) (𝓝 (0:ℝ)) (𝓝 (‖W x₀‖ * 0)) :=
          (continuousAt_id.const_mul _).tendsto
        rw [mul_zero] at hM'
        exact hM'.mono_left nhdsWithin_le_nhds
    exact Tendsto.congr' hslope.symm (hcoord1.prodMk hcoord2)
  -- the Grönwall norm bound
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) x,
      ‖(deriv W t, t * W t)‖ ≤ (1 + x) * ‖(W t, deriv W t)‖ := by
    intro t ht
    have hnn : (0:ℝ) ≤ max |W t| |deriv W t| := le_trans (abs_nonneg _) (le_max_left _ _)
    have hx1 : (1:ℝ) ≤ 1 + x := le_add_of_nonneg_right hx.le
    show max ‖deriv W t‖ ‖t * W t‖ ≤ (1 + x) * max ‖W t‖ ‖deriv W t‖
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1]
    apply max_le
    · calc |deriv W t| ≤ max |W t| |deriv W t| := le_max_right _ _
        _ ≤ (1 + x) * max |W t| |deriv W t| := le_mul_of_one_le_left hnn hx1
    · calc t * |W t| ≤ x * |W t| := mul_le_mul_of_nonneg_right ht.2.le (abs_nonneg _)
        _ ≤ (1 + x) * |W t| :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (abs_nonneg _)
        _ ≤ (1 + x) * max |W t| |deriv W t| :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (zero_le_one.trans hx1)
  have hG : ∀ t ∈ Set.Icc (0:ℝ) x, u t = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f' := fun x => (deriv W x, x * W x)) (K := 1 + x)
      (hucont.mono Set.Icc_subset_Ici_self)
    · intro t ht
      have ht0 : 0 ≤ t := ht.1
      rcases ht0.eq_or_lt with rfl | htpos
      · show HasDerivWithinAt u (deriv W 0, 0 * W 0) (Set.Ici 0) 0
        rw [hdW0, zero_mul]
        exact hstep8
      · exact ((hdiff t (Set.mem_Ioi.mpr htpos)).hasDerivAt.prodMk
          (hW'' t (Set.mem_Ioi.mpr htpos))).hasDerivWithinAt
    · show u 0 = 0
      rw [hu]
      show ((W 0, deriv W 0) : ℝ × ℝ) = 0
      rw [hW0, hdW0]
      exact Prod.ext rfl rfl
    · intro t ht
      exact hbound t ht
  have hWx : (u x).1 = ((0, 0) : ℝ × ℝ).1 := congrArg Prod.fst (hG x (Set.right_mem_Icc.mpr hx.le))
  exact hWx

end AiryODEUniqueness
