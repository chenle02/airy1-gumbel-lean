/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FddMeasure.TasepKernel
import Airy1GumbelContrib.Airy.AiryContour
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

open Filter Set MeasureTheory
open scoped Topology BigOperators PowerSeries

namespace AiryFdd

/-- The integer site of the cell containing the spatial coordinate at time u.
The use of the ceiling agrees with the lower orthant of the rescaled position. -/
noncomputable def bfpLatticeSite (N : ℕ) (u s : ℝ) : ℤ :=
  ⌈bfpCenter N u - bfpScale N * s⌉

/-- The BFP07 period-two pole term in rescaled coordinates, with the lattice
spacing removed and the power-of-two conjugation from Section 5. -/
noncomputable def bfpScaledPole (N : ℕ) (u v s₁ s₂ : ℝ) : ℝ :=
  bfpScale N * (2 : ℝ) ^ (bfpLatticeSite N v s₂ - bfpLatticeSite N u s₁) *
    bfpPoleKer N (bfpLabel N u) (bfpLatticeSite N u s₁)
      (bfpLabel N v) (bfpLatticeSite N v s₂)

theorem bfpScale_tendsto_atTop : Tendsto bfpScale atTop atTop := by
  exact ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    tendsto_natCast_atTop_atTop).const_mul_atTop bfpKappa_pos

theorem bfpScale_inv_tendsto_zero : Tendsto (fun N : ℕ => (bfpScale N)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp bfpScale_tendsto_atTop

theorem bfpScale_sq (N : ℕ) : bfpScale N ^ 2 =
    bfpKappa ^ 2 * (N : ℝ) ^ (2 / 3 : ℝ) := by
  unfold bfpScale
  rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ N)]
  norm_num

theorem bfpCenter_eq (N : ℕ) (u : ℝ) : bfpCenter N u = -2 * bfpScale N ^ 2 * u := by
  rw [bfpCenter, bfpScale_sq]
  ring

theorem bfpLabel_eq (N : ℕ) (u : ℝ) :
    bfpLabel N u = ⌊(N : ℝ) / 6 + bfpScale N ^ 2 * u⌋ := by
  rw [bfpLabel, bfpScale_sq]; congr 1; ring

theorem bfpLatticeSite_error (N : ℕ) (u s : ℝ) :
    0 ≤ (bfpLatticeSite N u s : ℝ) - (bfpCenter N u - bfpScale N * s) ∧
    (bfpLatticeSite N u s : ℝ) - (bfpCenter N u - bfpScale N * s) < 1 := by
  unfold bfpLatticeSite
  exact ⟨sub_nonneg.mpr (Int.le_ceil _), sub_lt_iff_lt_add.mpr (by simpa only [add_comm] using Int.ceil_lt_add_one (bfpCenter N u - bfpScale N * s))⟩

theorem bfpLabel_error (N : ℕ) (u : ℝ) :
    -1 < (bfpLabel N u : ℝ) - ((N : ℝ) / 6 + bfpScale N ^ 2 * u) ∧
    (bfpLabel N u : ℝ) - ((N : ℝ) / 6 + bfpScale N ^ 2 * u) ≤ 0 := by
  rw [bfpLabel_eq]
  constructor
  · have h := Int.lt_floor_add_one ((N : ℝ) / 6 + bfpScale N ^ 2 * u)
    linarith
  · exact sub_nonpos.mpr (Int.floor_le _)

/-- The two nearest-integer errors are uniform over the spatial levels. -/
theorem bfpGap_errors (N : ℕ) (u v s t : ℝ) :
    |(bfpLabel N v - bfpLabel N u : ℤ) - bfpScale N ^ 2 * (v-u)| < (1 : ℝ) ∧
    |((bfpLatticeSite N u s - bfpLatticeSite N v t : ℤ) : ℝ) -
      2 * (bfpLabel N v - bfpLabel N u : ℤ) - bfpScale N * (t-s)| < 3 := by
  have h₁ := bfpLabel_error N u
  have h₂ := bfpLabel_error N v
  have h₃ := bfpLatticeSite_error N u s
  have h₄ := bfpLatticeSite_error N v t
  rw [bfpCenter_eq] at h₃ h₄
  push_cast
  simp only [abs_lt]
  constructor <;> constructor <;> nlinarith only [h₁.1,h₁.2,h₂.1,h₂.2,h₃.1,h₃.2,h₄.1,h₄.2]


private def bfpCircleA (r x : ℝ) := 1 + 2*r*x + r^2
private def bfpCircleB (r x : ℝ) := 4 - 4*r*x + r^2
private def bfpCircleD (r x : ℝ) := 1 - 2*r*x + r^2

private noncomputable def bfpCircleLog (r x : ℝ) :=
  (Real.log (bfpCircleA r x) - Real.log (bfpCircleB r x)) / 2 +
    (Real.log (bfpCircleD r x) - Real.log (r^2)) / 6

private theorem bfpCircle_bounds {r x : ℝ} (hr : r ∈ Icc (1/3 : ℝ) (1/2))
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < bfpCircleA r x ∧ bfpCircleA r x ≤ 3 ∧
    0 < bfpCircleB r x ∧ bfpCircleB r x ≤ 7 ∧
    0 < bfpCircleD r x ∧ bfpCircleD r x ≤ 3 := by
  obtain ⟨hr₁,hr₂⟩ := hr
  obtain ⟨hx₁,hx₂⟩ := hx
  have h0 : 0 ≤ r := by linarith
  have h₁ := mul_le_mul_of_nonneg_left hx₁ h0
  have h₂ := mul_le_mul_of_nonneg_left hx₂ h0
  have hsq : r^2 ≤ (1/2 : ℝ)^2 := by gcongr
  have hl : (1/2 : ℝ)^2 ≤ (1-r)^2 := by gcongr; linarith
  unfold bfpCircleA bfpCircleB bfpCircleD
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

private theorem bfpCircle_deriv {r x : ℝ} (hr : r ∈ Icc (1/3 : ℝ) (1/2))
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt (bfpCircleLog r)
      (r * (3 * bfpCircleB r x * bfpCircleD r x + 6 * bfpCircleA r x * bfpCircleD r x -
          bfpCircleA r x * bfpCircleB r x) /
        (3 * bfpCircleA r x * bfpCircleB r x * bfpCircleD r x)) x := by
  obtain ⟨ha,_,hb,_,hd,_⟩ := bfpCircle_bounds hr hx
  have ha' : HasDerivAt (bfpCircleA r) (2*r) x := by
    unfold bfpCircleA
    simpa only [id_eq,mul_one] using
      (((hasDerivAt_id x).const_mul (2*r)).const_add 1).add_const (r^2)
  have hb' : HasDerivAt (bfpCircleB r) (-4*r) x := by
    unfold bfpCircleB
    convert (((hasDerivAt_id x).const_mul (4*r)).const_sub 4).add_const (r^2) using 1 <;> simp [id_eq]
  have hd' : HasDerivAt (bfpCircleD r) (-2*r) x := by
    unfold bfpCircleD
    convert (((hasDerivAt_id x).const_mul (2*r)).const_sub 1).add_const (r^2) using 1 <;> simp [id_eq]
  unfold bfpCircleLog
  convert (((ha'.log ha.ne').sub (hb'.log hb.ne')).div_const 2).add
      (((hd'.log hd.ne').sub_const (Real.log (r^2))).div_const 6) using 1
  field_simp
  ring

private theorem bfpCircle_deriv_lower {r x : ℝ} (hr : r ∈ Icc (1/3 : ℝ) (1/2))
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    (1/2-r)/1000 ≤ deriv (bfpCircleLog r) x := by
  rw [(bfpCircle_deriv hr hx).deriv]
  obtain ⟨ha,ha',hb,hb',hd,hd'⟩ := bfpCircle_bounds hr hx
  let P := 3 * bfpCircleB r x * bfpCircleD r x + 6 * bfpCircleA r x * bfpCircleD r x -
          bfpCircleA r x * bfpCircleB r x
  have hr₁ := hr.1
  have hr₂ := hr.2
  have hy : 0 ≤ 1-x := sub_nonneg.mpr hx.2
  have hP : P = 2*(1-2*r)*(7-6*r+3*r^2-2*r^3) +
      8*r*(2*r^2-2*r+5)*(1-x) + 8*r^2*(1-x)^2 := by
    dsimp [P,bfpCircleA,bfpCircleB,bfpCircleD]; ring
  have h0 : 0 ≤ r := by linarith
  have hterm : 3 ≤ 7-6*r+3*r^2-2*r^3 := by
    have hcube : r^3 ≤ (1/2 : ℝ)^3 := by gcongr
    nlinarith [sq_nonneg r]
  have hterm' : 0 ≤ 2*r^2-2*r+5 := by nlinarith [sq_nonneg r]
  have hPlower : 12*(1/2-r) ≤ P := by
    rw [hP]
    have h₁ := mul_le_mul_of_nonneg_left hterm (show 0 ≤ 2*(1-2*r) by linarith)
    have h₂ := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 8*r) hterm') hy
    have h₃ : 0 ≤ 8*r^2*(1-x)^2 := by positivity
    linarith
  have hprod : 3 * bfpCircleA r x * bfpCircleB r x * bfpCircleD r x ≤ 189 := by
    calc
      _ ≤ (3 : ℝ) * 3 * 7 * 3 := by gcongr
      _ = _ := by norm_num
  have hbase : 0 ≤ 1/2-r := sub_nonneg.mpr hr₂
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ ≤ (1/2-r)/1000 * 189 := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ r * P := by
      have h₁ := mul_le_mul_of_nonneg_left hPlower h0
      have h₂ := mul_le_mul_of_nonneg_right hr₁ (by positivity : 0 ≤ 12*(1/2-r))
      linarith

/-- The circle shifted to the inside of the saddle has a linear loss in
1 minus the cosine of the angle. The slope is proportional to its displacement. -/
private theorem bfpCircleLog_angle {r x : ℝ} (hr : r ∈ Icc (1/3 : ℝ) (1/2))
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    bfpCircleLog r x ≤ bfpCircleLog r 1 - (1/2-r)/1000 * (1-x) := by
  let b : ℝ := (1/2-r)/1000
  let f (x : ℝ) := bfpCircleLog r x - b*x
  have hd (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : HasDerivAt f (deriv (bfpCircleLog r) x - b) x := by
    have h := bfpCircle_deriv hr hx
    rw [h.deriv]
    exact h.sub (by simpa only [id_eq,mul_one] using (hasDerivAt_id x).const_mul b)
  have hmono : MonotoneOn f (Icc (-1 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x (interior_subset hx)).deriv]
      exact sub_nonneg.mpr (bfpCircle_deriv_lower hr (interior_subset hx))
  have h := hmono hx (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) hx.2
  dsimp [f] at h
  change _ ≤ _ - b*(1-x)
  linarith


private theorem bfpPoly_trunc_div {P Q : Polynomial ℂ} {F : ℂ⟦X⟧}
    (hF : (↑Q : ℂ⟦X⟧) * F = ↑P) (k : ℕ) :
    Polynomial.X^(k+1) ∣ P-Q*F.trunc (k+1) := by
  have h : (↑(P-Q*F.trunc (k+1)) : ℂ⟦X⟧) =
      PowerSeries.X^(k+1) * ((↑Q : ℂ⟦X⟧) * PowerSeries.mk (fun i => F.coeff (i+(k+1)))) := by
    simp only [Polynomial.coe_sub, Polynomial.coe_mul, ← hF]
    nth_rw 1 [PowerSeries.eq_X_pow_mul_shift_add_trunc (k+1) F]
    ring
  apply Polynomial.X_pow_dvd_iff.mpr
  intro j hj
  rw [← Polynomial.coeff_coe, h, PowerSeries.coeff_X_pow_mul']
  simp [show ¬k+1 ≤ j by omega]

private theorem bfpCircle_integral_polynomial {r : ℝ} (hr : 0 < r) (P : Polynomial ℂ) (k : ℕ)
    (hP : P.natDegree < k+1) :
    (∮ z in C(0,r), P.eval z * z^(-(k:ℤ)-1)) =
      (2*(Real.pi:ℂ)*Complex.I) * P.coeff k := by
  let S := Finset.range (k+1)
  have he : (∮ z in C(0,r), P.eval z * z^(-(k:ℤ)-1)) =
        ∮ z in C(0,r), ∑ i ∈ S, P.coeff i * z^((i:ℤ)-(k:ℤ)-1) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hz' : z ≠ 0 := by
      intro h
      subst z
      simpa [Metric.mem_sphere, hr.ne] using hz
    have hsum := Polynomial.eval₂_eq_sum_range' (RingHom.id ℂ) hP z
    change P.eval z = _ at hsum
    simp only [RingHom.id_apply] at hsum
    change P.eval z * z^(-(k:ℤ)-1) = ∑ i ∈ S, P.coeff i * z^((i:ℤ)-(k:ℤ)-1)
    rw [hsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc, ← zpow_natCast z i, ← zpow_add₀ hz']
    congr 2
    ring
  rw [he, circleIntegral.integral_fun_sum]
  · have hInt (i : ℕ) :
        (∮ z in C(0,r), P.coeff i * z^((i:ℤ)-(k:ℤ)-1)) =
          if i=k then (2*(Real.pi:ℂ)*Complex.I)*P.coeff k else 0 := by
      rw [circleIntegral.integral_const_mul]
      by_cases hi : i=k
      · subst i
        simp only [sub_self, zero_sub, ite_true,zpow_neg_one]
        have h : (∮ z in C((0:ℂ),r), z⁻¹) = 2*(Real.pi:ℂ)*Complex.I := by
          simpa only [sub_zero] using circleIntegral.integral_sub_center_inv (0:ℂ) hr.ne'
        rw [h,mul_comm]
      · rw [ite_eq_right hi]
        have hw : (i:ℤ)-(k:ℤ)-1 ≠ -1 := by omega
        have h : (∮ z in C((0:ℂ),r), z^((i:ℤ)-(k:ℤ)-1)) = 0 := by
          simpa only [sub_zero] using circleIntegral.integral_sub_zpow_of_ne hw 0 0 r
        rw [h,mul_zero]
    simp_rw [hInt]
    simp [S]
  · intro i hi
    apply ContinuousOn.circleIntegrable hr.le
    apply continuousOn_const.mul
    intro z hz
    refine (continuousAt_zpow₀ _ _ (Or.inl ?_)).continuousWithinAt
    intro h
    subst z
    simpa [Metric.mem_sphere,hr.ne] using hz

/-- Recovery of a formal coefficient on a circle by a finite Taylor division.
Only the nonvanishing of the denominator on the closed disk is needed. -/
private theorem bfpCircle_integral_coeff {r : ℝ} (hr : 0 < r) (P Q : Polynomial ℂ)
    (F : ℂ⟦X⟧) (hF : (↑Q : ℂ⟦X⟧) * F = ↑P) (k : ℕ)
    (hQ : ∀ z ∈ Metric.closedBall (0:ℂ) r, Q.eval z ≠ 0) :
    (∮ z in C(0,r), (P.eval z / Q.eval z) * z^(-(k:ℤ)-1)) =
      (2*(Real.pi:ℂ)*Complex.I) * F.coeff k := by
  let T := F.trunc (k+1)
  obtain ⟨R,hR⟩ := bfpPoly_trunc_div hF k
  have hDiff : DiffContOnCl ℂ (fun z => R.eval z / Q.eval z) (Metric.ball 0 r) := by
    refine ⟨?_,?_⟩
    · intro z hz
      have hne := hQ z (Metric.ball_subset_closedBall hz)
      exact (R.differentiable.differentiableAt.div Q.differentiable.differentiableAt hne).differentiableWithinAt
    · apply R.continuous.continuousOn.div Q.continuous.continuousOn
      intro z hz
      exact hQ z (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hz)
  have hRem : (∮ z in C(0,r), R.eval z / Q.eval z) = 0 :=
    hDiff.circleIntegral_eq_zero hr.le
  have hEq :
      (∮ z in C(0,r), (P.eval z / Q.eval z) * z^(-(k:ℤ)-1)) =
        ∮ z in C(0,r), T.eval z * z^(-(k:ℤ)-1) + R.eval z / Q.eval z := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hz' : z ≠ 0 := by
      intro h
      subst z
      simpa [Metric.mem_sphere,hr.ne] using hz
    have hq := hQ z (Metric.sphere_subset_closedBall hz)
    have he := congrArg (Polynomial.eval z) hR
    simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X] at he
    change _ - Q.eval z * T.eval z = _ at he
    have hE : z^(k+1) * z^(-(k:ℤ)-1) = 1 := by
      rw [← zpow_natCast z (k+1),← zpow_add₀ hz']
      simp
    change P.eval z / Q.eval z * z^(-(k:ℤ)-1) =
      T.eval z * z^(-(k:ℤ)-1) + R.eval z / Q.eval z
    calc
      _ = (Q.eval z * T.eval z + z^(k+1) * R.eval z) / Q.eval z * z^(-(k:ℤ)-1) := by
        rw [sub_eq_iff_eq_add] at he
        rw [he,add_comm (z^(k+1)*R.eval z)]
      _ = _ := by
        field_simp
        linear_combination R.eval z * hE
  have hA : CircleIntegrable (fun z : ℂ => T.eval z * z^(-(k:ℤ)-1)) 0 r := by
    apply ContinuousOn.circleIntegrable hr.le
    apply T.continuous.continuousOn.mul
    intro z hz
    refine (continuousAt_zpow₀ _ _ (Or.inl ?_)).continuousWithinAt
    intro h
    subst z
    simpa [Metric.mem_sphere,hr.ne] using hz
  have hB : CircleIntegrable (fun z : ℂ => R.eval z / Q.eval z) 0 r := by
    apply ContinuousOn.circleIntegrable hr.le
    exact R.continuous.continuousOn.div Q.continuous.continuousOn
      (fun z hz => hQ z (Metric.sphere_subset_closedBall hz))
  have hC : T.natDegree < k+1 := PowerSeries.natDegree_trunc_lt F k
  have hT : T.coeff k = F.coeff k := by
    change (F.trunc (k+1)).coeff k = _
    rw [PowerSeries.coeff_trunc,ite_eq_left (Nat.lt_succ_self k)]
  calc
    _ = _ := hEq
    _ = (∮ z in C(0,r), T.eval z * z^(-(k:ℤ)-1)) +
        (∮ z in C(0,r), R.eval z / Q.eval z) := circleIntegral.integral_add hA hB
    _ = _ := by rw [hRem,add_zero,bfpCircle_integral_polynomial hr T k hC,hT]


private noncomputable def bfpPoleSeries (N : ℕ) (a : ℤ) : ℝ⟦X⟧ :=
  PowerSeries.binomialSeries ℝ a * (1-PowerSeries.X)^N *
    PowerSeries.rescale (1/2:ℝ) (PowerSeries.binomialSeries ℝ (-(N:ℤ)))

private noncomputable def bfpComplexPoleSeries (N : ℕ) (a : ℤ) : ℂ⟦X⟧ :=
  PowerSeries.rescale (-1:ℂ)
    (PowerSeries.map Complex.ofRealHom (bfpPoleSeries N a))

private theorem bfpBinomialSeries_map (a : ℤ) :
    PowerSeries.map Complex.ofRealHom (PowerSeries.binomialSeries ℝ a) =
      PowerSeries.binomialSeries ℂ a := by
  ext n
  simp [PowerSeries.coeff_map]

private theorem bfpRescale_C (a c : ℂ) :
    PowerSeries.rescale a (PowerSeries.C c) = PowerSeries.C c := by
  ext n
  by_cases h : n=0 <;> simp [PowerSeries.coeff_rescale,PowerSeries.coeff_C,h]

private theorem bfpPoleSeries_complex (N : ℕ) (a : ℤ) :
    bfpComplexPoleSeries N a =
      PowerSeries.rescale (-1:ℂ) (PowerSeries.binomialSeries ℂ a * (1-PowerSeries.X)^N *
        PowerSeries.rescale (1/2:ℂ) (PowerSeries.binomialSeries ℂ (-(N:ℤ)))) := by
  have hS := (PowerSeries.rescale_map Complex.ofRealHom (1/2:ℝ)
    (PowerSeries.binomialSeries ℝ (-(N:ℤ)))).symm
  unfold bfpComplexPoleSeries bfpPoleSeries
  congr 1
  simp only [map_mul,map_pow,map_sub,map_one,PowerSeries.map_X,bfpBinomialSeries_map,hS]
  have he : Complex.ofRealHom (1/2:ℝ) = (1/2:ℂ) := by simp
  rw [he]

private theorem bfpPoleSeries_poly (N : ℕ) (a : ℤ) :
    let P : Polynomial ℂ := (1-Polynomial.X)^a.toNat * (1+Polynomial.X)^N
    let Q : Polynomial ℂ := (1-Polynomial.X)^(-a).toNat *
      (1-Polynomial.C (1/2:ℂ)*Polynomial.X)^N
    (↑Q : ℂ⟦X⟧) * bfpComplexPoleSeries N a = ↑P := by
  let B : ℤ → ℂ⟦X⟧ := PowerSeries.binomialSeries ℂ
  let R := PowerSeries.rescale (-1 : ℂ)
  let S := PowerSeries.rescale (1/2 : ℂ)
  have hminus (m : ℕ) : R (B (m:ℤ)) = (1-PowerSeries.X)^m := by
    simp [B,R,PowerSeries.binomialSeries_nat,PowerSeries.rescale_X,sub_eq_add_neg]
  have hplus (m : ℕ) : R ((1-PowerSeries.X)^m) = (1+PowerSeries.X)^m := by
    simp [R,PowerSeries.rescale_X]
  have hfactor : (1-PowerSeries.C (1/2:ℂ)*PowerSeries.X)^N = R (S (B (N:ℤ))) := by
    simp [B,R,S,PowerSeries.binomialSeries_nat,PowerSeries.rescale_X,sub_eq_add_neg,bfpRescale_C]
  have ha : B ((-a).toNat : ℤ) * B a = B (a.toNat : ℤ) := by
    rw [← PowerSeries.binomialSeries_add]
    congr 1
    omega
  have hn : S (B (N:ℤ)) * S (B (-(N:ℤ))) = 1 := by
    rw [← map_mul,← PowerSeries.binomialSeries_add,add_neg_cancel,PowerSeries.binomialSeries_zero,map_one]
  simp only [Polynomial.coe_mul, Polynomial.coe_pow,Polynomial.coe_sub,Polynomial.coe_add,
    Polynomial.coe_one,Polynomial.coe_X,Polynomial.coe_C,bfpPoleSeries_complex,map_mul]
  change ((1-PowerSeries.X)^(-a).toNat*(1-PowerSeries.C (1/2:ℂ)*PowerSeries.X)^N) *
    (R (B a)*R ((1-PowerSeries.X)^N)*R (S (B (-(N:ℤ))))) =
      (1-PowerSeries.X)^a.toNat*(1+PowerSeries.X)^N
  rw [← hminus (-a).toNat,hfactor,← hminus a.toNat,← hplus N]
  calc
    _ = R (B ((-a).toNat:ℤ)*B a) * R ((1-PowerSeries.X)^N) *
        R (S (B (N:ℤ)) * S (B (-(N:ℤ)))) := by simp only [map_mul]; ring
    _ = _ := by rw [ha,hn,map_one,mul_one]

private theorem bfpPoleSeries_circle {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1/2)
    (N : ℕ) (a : ℤ) (k : ℕ) :
    (∮ z in C(0,r), ((1-z)^a * (1+z)^N / (1-z/2)^N) * z^(-(k:ℤ)-1)) =
      (2*(Real.pi:ℂ)*Complex.I) * ((-1:ℂ)^k * (bfpPoleSeries N a).coeff k) := by
  let P : Polynomial ℂ := (1-Polynomial.X)^a.toNat * (1+Polynomial.X)^N
  let Q : Polynomial ℂ := (1-Polynomial.X)^(-a).toNat *
    (1-Polynomial.C (1/2:ℂ)*Polynomial.X)^N
  have hnorm (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) r) : ‖z‖ ≤ (1/2:ℝ) := by
    exact (by simpa [Metric.mem_closedBall,dist_zero_right] using hz : ‖z‖ ≤ r).trans hr'
  have hne (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) r) :
      (1-z ≠ 0) ∧ (1-z/2 ≠ 0) := by
    have h := hnorm z hz
    constructor
    · intro he
      have hi : z = 1 := by linear_combination -he
      norm_num [hi] at h
    · intro he
      have hi : z = 2 := by linear_combination -2*he
      norm_num [hi] at h
  have hQ (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) r) : Q.eval z ≠ 0 := by
    have hh := hne z hz
    simp only [Q,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,
      Polynomial.eval_one,Polynomial.eval_C,Polynomial.eval_X]
    rw [show (1/2:ℂ)*z=z/2 by ring]
    exact mul_ne_zero (pow_ne_zero _ hh.1) (pow_ne_zero _ hh.2)
  have hI := bfpCircle_integral_coeff hr P Q (bfpComplexPoleSeries N a)
    (bfpPoleSeries_poly N a) k hQ
  have hzpow (z : ℂ) (hz : 1-z ≠ 0) :
      (1-z)^a = (1-z)^a.toNat / (1-z)^(-a).toNat := by
    have he : a = (a.toNat:ℤ)-((-a).toNat:ℤ) := by omega
    conv_lhs => rw [he,zpow_sub₀ hz,zpow_natCast,zpow_natCast]
  calc
    _ = (∮ z in C(0,r), (P.eval z/Q.eval z)*z^(-(k:ℤ)-1)) := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      have hh := hne z (Metric.sphere_subset_closedBall hz)
      change _ * z^(-(k:ℤ)-1) = _ * z^(-(k:ℤ)-1)
      congr 1
      simp only [P,Q,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,
        Polynomial.eval_one,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_add]
      rw [hzpow z hh.1,show (1/2:ℂ)*z=z/2 by ring]
      field_simp
    _ = _ := by
      rw [hI,bfpComplexPoleSeries,PowerSeries.coeff_rescale,PowerSeries.coeff_map]
      rfl


private noncomputable def bfpPoleAngular (N : ℕ) (a k : ℤ) (r θ : ℝ) : ℂ :=
  let z := circleMap 0 r θ
  ((1+z)/(2-z))^N * (2*(1-z))^a * (2*z)^(-k)

private theorem bfpPoleAngular_periodic (N : ℕ) (a k : ℤ) (r : ℝ) :
    Function.Periodic (bfpPoleAngular N a k r) (2*Real.pi) := by
  intro θ
  simp only [bfpPoleAngular, periodic_circleMap 0 r θ]

private theorem bfpPoleAngular_coeff {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1/2)
    (N : ℕ) (a : ℤ) (k : ℕ) :
    (∫ θ in -Real.pi..Real.pi, bfpPoleAngular N a k r θ) =
      2*(Real.pi:ℂ) * ((2:ℂ)^(a-k) * (1/2:ℂ)^N *
        ((-1:ℂ)^k * (bfpPoleSeries N a).coeff k)) := by
  let g (z : ℂ) := (1-z)^a * (1+z)^N / (1-z/2)^N * z^(-(k:ℤ)-1)
  have hcircle := bfpPoleSeries_circle hr hr' N a k
  have hperiod := (bfpPoleAngular_periodic N a k r).intervalIntegral_add_eq 0 (-Real.pi)
  have hp : -Real.pi+2*Real.pi = Real.pi := by ring
  rw [zero_add,hp] at hperiod
  rw [← hperiod]
  let c : ℂ := (2:ℂ)^(a-k) * (1/2:ℂ)^N
  have hInt : c * (∮ z in C(0,r), g z) =
      Complex.I * (∫ θ in (0:ℝ)..2*Real.pi, bfpPoleAngular N a k r θ) := by
    rw [circleIntegral,← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    let z := circleMap 0 r θ
    have hz : z ≠ 0 := by
      dsimp [z]
      exact circleMap_ne_center hr.ne'
    have hv : (1-z:ℂ) ≠ 0 := by
      intro h
      have he : z = 1 := by linear_combination -h
      have h' : ‖z‖ = r := by simp [z, norm_circleMap_zero, abs_of_pos hr]
      rw [he,norm_one] at h'
      linarith
    have he : z* z^(-(k:ℤ)-1) = z^(-(k:ℤ)) := by
      calc
        _ = z^(1:ℤ)*z^(-(k:ℤ)-1) := by rw [zpow_one]
        _ = _ := by rw [← zpow_add₀ hz]; congr 1; ring
    have hn : (2-z:ℂ) ≠ 0 := by
      intro h
      have he' : z = 2 := by linear_combination -h
      have h' : ‖z‖ = r := by simp [z, norm_circleMap_zero, abs_of_pos hr]
      norm_num [he'] at h'
      linarith
    change c * (deriv (circleMap 0 r) θ • g z) = _
    rw [deriv_circleMap,smul_eq_mul]
    change c*(z*Complex.I*g z) = _
    have hRatio : ((1+z)/(2-z))^N =
        (1/2:ℂ)^N*((1+z)^N/(1-z/2)^N) := by
      rw [← div_pow, ← mul_pow]
      have ht : (1-z/2:ℂ)=(2-z)/2 := by ring
      rw [ht]
      field_simp
    change _ = Complex.I * (((1+z)/(2-z))^N*(2*(1-z))^a*(2*z)^(-(k:ℤ)))
    rw [hRatio,mul_zpow,mul_zpow]
    have hpow : (2:ℂ)^(a-(k:ℤ)) = (2:ℂ)^a * (2:ℂ)^(-(k:ℤ)) :=
      sub_eq_add_neg a k ▸ (zpow_add₀ (by norm_num : (2:ℂ) ≠ 0) a (-(k:ℤ)))
    unfold c g
    rw [hpow, ← he]
    ring
  have hI : (∮ z in C(0,r), g z) =
      (2*(Real.pi:ℂ)*Complex.I)*((-1:ℂ)^k*(bfpPoleSeries N a).coeff k) := hcircle
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [← hInt,hI]
  dsimp [c]
  ring

private noncomputable def bfpPoleA (N : ℕ) (u v s : ℝ) : ℤ :=
  bfpLatticeSite N v s + bfpLabel N u + bfpLabel N v - 2

private noncomputable def bfpPoleK (N : ℕ) (u v s : ℝ) : ℤ :=
  bfpLatticeSite N u s + bfpLabel N u + bfpLabel N v - 2

private theorem bfpPoleAngular_scaled {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1/2)
    (N : ℕ) (u v s t : ℝ) (hK : 0 ≤ bfpPoleK N u v s) :
    (bfpScaledPole N u v s t : ℂ) = (bfpScale N : ℂ)/(2*(Real.pi:ℂ)) *
      ∫ θ in -Real.pi..Real.pi, bfpPoleAngular N (bfpPoleA N u v t) (bfpPoleK N u v s) r θ := by
  let k := bfpPoleK N u v s
  let a := bfpPoleA N u v t
  have hk : (k.toNat:ℤ)=k := Int.toNat_of_nonneg hK
  have hdiff : a-k = bfpLatticeSite N v t-bfpLatticeSite N u s := by dsimp [a,k,bfpPoleA,bfpPoleK]; ring
  have h := bfpPoleAngular_coeff hr hr' N a k.toNat
  rw [hk,hdiff] at h
  have hb : bfpLatticeSite N u s + bfpLabel N u + bfpLabel N v - 1 = k+1 := by
    dsimp [k,bfpPoleK]; ring
  simp only [bfpScaledPole,bfpPoleKer, hb, ite_eq_left (by omega : 0 < k+1),
    add_sub_cancel_right, Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_pow]
  push_cast
  change (bfpScale N:ℂ)*(2:ℂ)^(bfpLatticeSite N v t-bfpLatticeSite N u s) *
      ((-1:ℂ)^k.toNat*(1/2:ℂ)^N*((bfpPoleSeries N a).coeff k.toNat:ℂ)) =
    _ * ∫ θ in -Real.pi..Real.pi, bfpPoleAngular N a k r θ
  rw [h]
  field_simp [Real.pi_ne_zero]


private theorem bfpScale_cube (N : ℕ) : bfpScale N ^ 3 = (16/27:ℝ) * N := by
  have hk : bfpKappa^3 = (16/27:ℝ) := by
    unfold bfpKappa
    rw [div_pow,← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ 2)]
    norm_num
  unfold bfpScale
  rw [mul_pow,hk,← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ N)]
  norm_num

private theorem bfpTaylor_tendsto_zero {ι : Type*} {l : Filter ι} {d : ι → ℝ} {w : ι → ℂ}
    (hd : Tendsto d l (𝓝 0)) (hd₀ : ∀ᶠ n in l, 0 < d n)
    {q : ℂ} (hw : Tendsto w l (𝓝 q)) (m : ℕ) :
    Tendsto (fun n => ((d n)⁻¹ : ℂ)^m *
      (Complex.log (1 + (d n:ℂ)*w n) - Complex.logTaylor (m+1) ((d n:ℂ)*w n))) l (𝓝 0) := by
  let z (n : ι) := (d n:ℂ)*w n
  have hz : Tendsto z l (𝓝 0) := by
    simpa [z] using (Complex.continuous_ofReal.continuousAt.tendsto.comp hd).mul hw
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp (Complex.log_sub_logTaylor_isBigO m)
  have h := hz.eventually hC
  have hM : ∀ᶠ n in l, ‖w n‖ < ‖q‖+1 :=
    hw.norm.eventually_lt_const (by linarith)
  have hbound : ∀ᶠ n in l,
      ‖((d n)⁻¹ : ℂ)^m * (Complex.log (1+z n) - Complex.logTaylor (m+1) (z n))‖ ≤
        |C| * (‖q‖+1)^(m+1)*d n := by
    filter_upwards [hd₀,h,hM] with n hn he hwn
    have he' : ‖Complex.log (1+z n) - Complex.logTaylor (m+1) (z n)‖
        ≤ |C| * ‖z n‖^(m+1) := by
      refine he.trans ?_
      rw [norm_pow]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    rw [norm_mul,norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg hn.le]
    calc
      _ ≤ ((d n)⁻¹)^m * (|C| * ‖z n‖^(m+1)) := mul_le_mul_of_nonneg_left he' (by positivity)
      _ = |C| * ‖w n‖^(m+1) * d n := by
        have hn' : d n ≠ 0 := hn.ne'
        dsimp [z]
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hn.le,mul_pow,pow_succ,
          inv_pow]
        field_simp
      _ ≤ _ := by gcongr
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    hbound (by simpa using hd.const_mul (|C| * (‖q‖+1)^(m+1)))

private noncomputable def bfpCubicPhase (z : ℂ) : ℂ :=
  Complex.log (1-z/3) - Complex.log (1+z/3) +
    (Complex.log (1+z)-Complex.log (1-z))/3

private noncomputable def bfpQuadPhase (z : ℂ) : ℂ :=
  -Complex.log (1+z)-Complex.log (1-z)

private theorem bfpTaylor_log1 (z : ℂ) : Complex.logTaylor 2 z = z := by
  norm_num [Complex.logTaylor, Finset.sum_range_succ]

private theorem bfpTaylor_log2 (z : ℂ) : Complex.logTaylor 3 z = z-z^2/2 := by
  norm_num [Complex.logTaylor, Finset.sum_range_succ]
  ring

private theorem bfpTaylor_log3 (z : ℂ) : Complex.logTaylor 4 z = z-z^2/2+z^3/3 := by
  norm_num [Complex.logTaylor, Finset.sum_range_succ]
  ring

private theorem bfpScaledPhase_tendsto {ι : Type*} {l : Filter ι} {d : ι → ℝ} {w : ι → ℂ}
    (hd : Tendsto d l (𝓝 0)) (hd₀ : ∀ᶠ n in l, 0 < d n)
    {q : ℂ} (hw : Tendsto w l (𝓝 q)) :
    Tendsto (fun n => ((d n)⁻¹ : ℂ)^3 * bfpCubicPhase ((d n:ℂ)*w n)) l
        (𝓝 ((16/81:ℂ)*q^3)) ∧
      Tendsto (fun n => ((d n)⁻¹ : ℂ)^2 * bfpQuadPhase ((d n:ℂ)*w n)) l (𝓝 (q^2)) ∧
      Tendsto (fun n => ((d n)⁻¹ : ℂ) * Complex.log (1+(d n:ℂ)*w n)) l (𝓝 q) := by
  have h₁ := bfpTaylor_tendsto_zero hd hd₀ hw 3
  have h₂ := bfpTaylor_tendsto_zero hd hd₀ hw.neg 3
  have h₃ := bfpTaylor_tendsto_zero hd hd₀ (hw.div_const 3) 3
  have h₄ := bfpTaylor_tendsto_zero hd hd₀ (hw.neg.div_const 3) 3
  have h₅ := bfpTaylor_tendsto_zero hd hd₀ hw 2
  have h₆ := bfpTaylor_tendsto_zero hd hd₀ hw.neg 2
  have h₇ := bfpTaylor_tendsto_zero hd hd₀ hw 1
  refine ⟨?_,?_,?_⟩
  · have hSum := ((h₄.sub h₃).add ((h₁.sub h₂).div_const 3)).add ((hw.pow 3).const_mul (16/81))
    rw [show (0:ℂ)-0+(0-0)/3+(16/81)*q^3 = (16/81)*q^3 by simp] at hSum
    refine hSum.congr' ?_
    filter_upwards [hd₀] with n hn
    have h : (d n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hn₁ : (1:ℂ)+(d n:ℂ)*(-w n/3) = 1-((d n:ℂ)*w n)/3 := by ring
    have hn₂ : (1:ℂ)+(d n:ℂ)*(w n/3) = 1+((d n:ℂ)*w n)/3 := by ring
    have hn₃ : (1:ℂ)+(d n:ℂ)*(-w n) = 1-(d n:ℂ)*w n := by ring
    simp only [show (3:ℕ)+1=4 by rfl,bfpCubicPhase,bfpTaylor_log3,Complex.ofReal_inv,hn₁,hn₂,hn₃]
    field_simp
    ring
  · have hSum := (h₅.neg.sub h₆).add (hw.pow 2)
    rw [show -(0:ℂ)-0+q^2 = q^2 by simp] at hSum
    refine hSum.congr' ?_
    filter_upwards [hd₀] with n hn
    have h : (d n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hn₃ : (1:ℂ)+(d n:ℂ)*(-w n) = 1-(d n:ℂ)*w n := by ring
    simp only [show (2:ℕ)+1=3 by rfl,bfpQuadPhase,bfpTaylor_log2,Complex.ofReal_inv,hn₃]
    field_simp
    ring
  · have hSum := h₇.add hw
    rw [zero_add] at hSum
    refine hSum.congr' ?_
    filter_upwards [hd₀] with n hn
    have h : (d n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [show (1:ℕ)+1=2 by rfl,bfpTaylor_log1,pow_one,Complex.ofReal_inv]
    field_simp
    ring


private theorem bfpPoleA_error (N : ℕ) (u v t : ℝ) :
    |(bfpPoleA N u v t : ℝ) - ((N:ℝ)/3-bfpScale N^2*(v-u)-bfpScale N*t)| < 4 := by
  have h₁ := bfpLabel_error N u
  have h₂ := bfpLabel_error N v
  have h₃ := bfpLatticeSite_error N v t
  rw [bfpCenter_eq] at h₃
  unfold bfpPoleA
  push_cast
  rw [abs_lt]
  constructor <;> nlinarith only [h₁.1,h₁.2,h₂.1,h₂.2,h₃.1,h₃.2]

private theorem bfpPoleK_error (N : ℕ) (u v s : ℝ) :
    |(bfpPoleK N u v s : ℝ) - ((N:ℝ)/3+bfpScale N^2*(v-u)-bfpScale N*s)| < 4 := by
  have h₁ := bfpPoleA_error N v u s
  unfold bfpPoleA bfpPoleK at *
  push_cast at *
  convert h₁ using 1
  congr 1
  ring

private noncomputable def bfpSaddleRadius (η : ℝ) (N : ℕ) : ℝ :=
  1/2-η/2*(bfpScale N)⁻¹

private theorem bfpSaddleRadius_tendsto (η : ℝ) :
    Tendsto (bfpSaddleRadius η) atTop (𝓝 (1/2)) := by
  unfold bfpSaddleRadius
  have h := (tendsto_const_nhds (x := (1/2:ℝ))).sub (bfpScale_inv_tendsto_zero.const_mul (η/2))
  simpa only [mul_zero,sub_zero] using h

private theorem bfpSaddleRadius_bounds {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, bfpSaddleRadius η N ∈ Icc (1/3:ℝ) (1/2) := by
  filter_upwards [(bfpSaddleRadius_tendsto η).eventually_const_lt (by norm_num : (1/3:ℝ)<1/2),
    eventually_gt_atTop 0] with N hN hN₀
  refine ⟨hN.le,?_⟩
  unfold bfpSaddleRadius
  have hσ := bfpScale_pos hN₀
  linarith [mul_nonneg (show 0 ≤ η/2 by positivity) (inv_nonneg.mpr hσ.le)]

private noncomputable def bfpSaddleCoordinate (η y : ℝ) (N : ℕ) : ℂ :=
  (bfpScale N:ℂ) * (1-2*circleMap 0 (bfpSaddleRadius η N) (y/bfpScale N))

private theorem bfpSaddleCoordinate_tendsto (η y : ℝ) :
    Tendsto (bfpSaddleCoordinate η y) atTop (𝓝 ((η:ℂ)-(y:ℂ)*Complex.I)) := by
  let d (N : ℕ) : ℝ := (bfpScale N)⁻¹
  let h (N : ℕ) : ℂ := (d N:ℂ)*(y:ℂ)*Complex.I
  have hd : Tendsto d atTop (𝓝 0) := bfpScale_inv_tendsto_zero
  have hh : Tendsto h atTop (𝓝 0) := by
    simpa [h] using ((Complex.continuous_ofReal.continuousAt.tendsto.comp hd).mul_const (y:ℂ)).mul_const Complex.I
  have hR : Tendsto (fun N : ℕ => (bfpScale N:ℂ)*(Complex.exp (h N)-1-h N)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hnorm : Tendsto (fun N : ℕ => ‖h N‖) atTop (𝓝 0) := by simpa only [norm_zero] using hh.norm
    have hk : ∀ᶠ N : ℕ in atTop, ‖(bfpScale N:ℂ)*(Complex.exp (h N)-1-h N)‖ ≤ (d N)*y^2 := by
      filter_upwards [hnorm.eventually_lt_const zero_lt_one,eventually_gt_atTop 0] with N hn hN
      have hσ := bfpScale_pos hN
      rw [norm_mul, Complex.norm_real,Real.norm_of_nonneg hσ.le]
      refine (mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_sub_id_le hn.le) hσ.le).trans_eq ?_
      simp only [h,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
      rw [abs_of_nonneg (inv_nonneg.mpr hσ.le),mul_pow,sq_abs]
      dsimp [d]
      field_simp
    exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hk
      (by simpa using hd.mul_const (y^2))
  have hc : Tendsto (fun N : ℕ => (bfpScale N:ℂ)*(Complex.exp (h N)-1)) atTop (𝓝 ((y:ℂ)*Complex.I)) := by
    have hL := hR.add (tendsto_const_nhds (x := (y:ℂ)*Complex.I))
    apply (by simpa only [zero_add] using hL : Tendsto _ _ _).congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hσ : (bfpScale N:ℂ) ≠ 0 := by exact_mod_cast (bfpScale_pos hN).ne'
    simp only [h,d,Complex.ofReal_inv]
    field_simp
    ring
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp (bfpSaddleRadius_tendsto η)
  have hm := (tendsto_const_nhds (x := (η:ℂ))).sub ((hr.const_mul (2:ℂ)).mul hc)
  rw [show (η:ℂ)-(2*(↑(1/2:ℝ):ℂ))*((y:ℂ)*Complex.I) = (η:ℂ)-(y:ℂ)*Complex.I by norm_num] at hm
  refine hm.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hσ : (bfpScale N:ℂ) ≠ 0 := by exact_mod_cast (bfpScale_pos hN).ne'
  have hh' : ((y/bfpScale N:ℝ):ℂ)*Complex.I = h N := by
    rw [Complex.ofReal_div,div_eq_mul_inv]
    unfold h d
    rw [Complex.ofReal_inv]
    ring
  simp only [bfpSaddleCoordinate,Function.comp_apply,circleMap,zero_add,bfpSaddleRadius,
    Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat,Complex.ofReal_inv]
  have harg : (y:ℂ)/(bfpScale N:ℂ)*Complex.I = h N := by
    rw [← Complex.ofReal_div]
    exact hh'
  rw [harg]
  field_simp
  ring


private theorem bfpCircleMap_sq_norms (r θ : ℝ) :
    let z := circleMap 0 r θ
    ‖1+z‖^2 = bfpCircleA r (Real.cos θ) ∧
      ‖2-z‖^2 = bfpCircleB r (Real.cos θ) ∧
      ‖1-z‖^2 = bfpCircleD r (Real.cos θ) := by
  have h := Real.sin_sq_add_cos_sq θ
  dsimp [circleMap,bfpCircleA,bfpCircleB,bfpCircleD]
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.exp_ofReal_mul_I,Complex.add_re,
    Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.one_re,Complex.one_im,Complex.natCast_re,Complex.natCast_im,
    zero_add,zero_mul,mul_zero,sub_zero,mul_one,add_zero]
  norm_num
  constructor
  · linear_combination r^2 * h
  · constructor <;> linear_combination r^2 * h

private theorem bfpCircleLog_norm {r : ℝ} (hr : r ∈ Icc (1/3:ℝ) (1/2)) (θ : ℝ) :
    let z := circleMap 0 r θ
    bfpCircleLog r (Real.cos θ) =
      Real.log (‖1+z‖/‖2-z‖)+(Real.log (2*‖1-z‖)-Real.log (2*r))/3 := by
  let z := circleMap 0 r θ
  obtain ⟨ha,hb,hd⟩ := bfpCircleMap_sq_norms r θ
  change ‖1+z‖^2 = _ at ha
  change ‖2-z‖^2 = _ at hb
  change ‖1-z‖^2 = _ at hd
  have hθ : Real.cos θ ∈ Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩
  obtain ⟨hA,_,hB,_,hD,_⟩ := bfpCircle_bounds hr hθ
  have h₁ : 0 < ‖1+z‖ := by by_contra! h; rw [le_antisymm h (norm_nonneg _),zero_pow] at ha <;> linarith
  have h₂ : 0 < ‖2-z‖ := by by_contra! h; rw [le_antisymm h (norm_nonneg _),zero_pow] at hb <;> linarith
  have h₃ : 0 < ‖1-z‖ := by by_contra! h; rw [le_antisymm h (norm_nonneg _),zero_pow] at hd <;> linarith
  have hr₀ : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
  change bfpCircleLog r (Real.cos θ) =
    Real.log (‖1+z‖/‖2-z‖)+(Real.log (2*‖1-z‖)-Real.log (2*r))/3
  rw [bfpCircleLog,← ha,← hb,← hd,Real.log_div h₁.ne' h₂.ne',
    Real.log_mul (by norm_num) h₃.ne',Real.log_mul (by norm_num) hr₀.ne',
    Real.log_pow,Real.log_pow,Real.log_pow,Real.log_pow]
  norm_num
  ring

private theorem bfpPoleAngular_norm {r : ℝ} (hr : r ∈ Icc (1/3:ℝ) (1/2))
    (N : ℕ) (a k : ℤ) (θ : ℝ) :
    ‖bfpPoleAngular N a k r θ‖ =
      Real.exp ((N:ℝ)*bfpCircleLog r (Real.cos θ) +
        ((a:ℝ)-(N:ℝ)/3)*Real.log (2*‖1-circleMap 0 r θ‖) -
        ((k:ℝ)-(N:ℝ)/3)*Real.log (2*r)) := by
  let z := circleMap 0 r θ
  have hr₀ : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
  have hz : ‖z‖ = r := by simp [z,norm_circleMap_zero,abs_of_pos hr₀]
  obtain ⟨ha,hb,hd⟩ := bfpCircleMap_sq_norms r θ
  change ‖1+z‖^2 = _ at ha
  change ‖2-z‖^2 = _ at hb
  change ‖1-z‖^2 = _ at hd
  obtain ⟨hA,_,hB,_,hD,_⟩ := bfpCircle_bounds hr
    (show Real.cos θ ∈ Icc (-1:ℝ) 1 from ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩)
  have h₁ : 0 < ‖1+z‖ := by by_contra! h; rw [le_antisymm h (norm_nonneg _),zero_pow] at ha <;> linarith
  have h₂ : 0 < ‖2-z‖ := by by_contra! h; rw [le_antisymm h (norm_nonneg _),zero_pow] at hb <;> linarith
  have h₃ : 0 < ‖1-z‖ := by by_contra! h; rw [le_antisymm h (norm_nonneg _),zero_pow] at hd <;> linarith
  have hlog := bfpCircleLog_norm hr θ
  change bfpCircleLog r (Real.cos θ) = _ at hlog
  unfold bfpPoleAngular
  change ‖((1+z)/(2-z))^N*(2*(1-z))^a*(2*z)^(-k)‖ = _
  simp only [norm_mul,norm_div,norm_pow,norm_zpow,Complex.norm_ofNat,hz]
  rw [← Real.exp_log (show 0 < (‖1+z‖/‖2-z‖)^N*(2*‖1-z‖)^a*(2*r)^(-k) by positivity)]
  congr 1
  rw [Real.log_mul (by positivity : (‖1+z‖/‖2-z‖)^N*(2*‖1-z‖)^a ≠ 0) (by positivity),
    Real.log_mul (by positivity : (‖1+z‖/‖2-z‖)^N ≠ 0) (by positivity),
    Real.log_pow,Real.log_zpow,Real.log_zpow,Int.cast_neg,hlog]
  ring

private theorem bfpLogNorm_increment {r : ℝ} (hr : r ∈ Icc (1/3:ℝ) (1/2)) (θ : ℝ) :
    let z := circleMap 0 r θ
    0 ≤ Real.log (2*‖1-z‖)-Real.log (2*(1-r)) ∧
      Real.log (2*‖1-z‖)-Real.log (2*(1-r)) ≤ 2*(1-Real.cos θ) := by
  let z := circleMap 0 r θ
  have hD := (bfpCircleMap_sq_norms r θ).2.2
  change ‖1-z‖^2 = _ at hD
  have hr₁ := hr.1
  have hr₂ := hr.2
  have hc := Real.cos_le_one θ
  have hB : (1-r)^2 ≤ ‖1-z‖^2 := by
    rw [hD,bfpCircleD]
    nlinarith [mul_le_mul_of_nonneg_left hc (show 0 ≤ r by linarith)]
  have hv : 1-r ≤ ‖1-z‖ := by
    have := norm_nonneg (1-z)
    nlinarith
  have hr' : 0 < 1-r := by linarith
  have hv' : 0 < ‖1-z‖ := hr'.trans_le hv
  change 0 ≤ Real.log (2*‖1-z‖)-Real.log (2*(1-r)) ∧ _ ≤ _
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log (by positivity : 0 < 2*(1-r)) (by gcongr))
  · have hD₀ : 0 < (1-r)^2 := by positivity
    have hL := Real.log_le_sub_one_of_pos (show 0 < ‖1-z‖^2/(1-r)^2 by positivity)
    rw [Real.log_div (by positivity) hD₀.ne',Real.log_pow,Real.log_pow] at hL
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_mul (by norm_num) (by positivity)]
    have hmax : ‖1-z‖^2/(1-r)^2-1 ≤ 4*(1-Real.cos θ) := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hD₀).mpr
      have hs : (1/2:ℝ)^2 ≤ (1-r)^2 := by gcongr; linarith
      have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ 4*(1-Real.cos θ) by positivity)
      rw [hD,bfpCircleD]
      nlinarith [mul_le_mul_of_nonneg_right hr₂ (sub_nonneg.mpr hc)]
    linarith


private theorem bfpSaddleRadius_logs {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |(N:ℝ)*bfpCircleLog (bfpSaddleRadius η N) 1| ≤ C ∧
      |bfpScale N^2*(Real.log (2*bfpSaddleRadius η N)+Real.log (2*(1-bfpSaddleRadius η N)))| ≤ C ∧
      |bfpScale N * Real.log (2*bfpSaddleRadius η N)| ≤ C ∧
      |bfpScale N * Real.log (2*(1-bfpSaddleRadius η N))| ≤ C := by
  let d (N : ℕ) := (bfpScale N)⁻¹
  let q (N : ℕ) : ℂ := (d N : ℂ)*(η:ℂ)
  have hd : Tendsto d atTop (𝓝 0) := bfpScale_inv_tendsto_zero
  have hd₀ : ∀ᶠ N : ℕ in atTop, 0 < d N :=
    (eventually_gt_atTop 0).mono (fun _ h => inv_pos.mpr (bfpScale_pos h))
  obtain ⟨hT,hQ,hP⟩ := bfpScaledPhase_tendsto hd hd₀
    (tendsto_const_nhds (x := (η:ℂ)))
  have hM := (bfpScaledPhase_tendsto hd hd₀ (tendsto_const_nhds (x := -(η:ℂ)))).2.2
  have hre : Continuous (Complex.re : ℂ → ℝ) := Complex.continuous_re
  have hT' : Tendsto (fun N : ℕ => ((N:ℂ)*bfpCubicPhase (q N)).re)
      atTop (𝓝 ((27/16:ℂ)*((16/81:ℂ)*(η:ℂ)^3)).re) := by
    refine (hre.continuousAt.tendsto.comp (hT.const_mul (27/16))).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    change ((27/16:ℂ)*(((d N)⁻¹:ℂ)^3*bfpCubicPhase (q N))).re = _
    have hc := congrArg Complex.ofReal (bfpScale_cube N)
    dsimp [d]
    push_cast at hc ⊢
    rw [inv_inv,hc]
    congr 1
    ring
  let r := bfpSaddleRadius η
  have hE : ∀ᶠ N : ℕ in atTop, r N ∈ Icc (1/3:ℝ) (1/2) ∧ 0 < bfpScale N :=
    (bfpSaddleRadius_bounds hη).and ((eventually_gt_atTop 0).mono (fun _ hn => bfpScale_pos hn))
  have hQ' := hre.continuousAt.tendsto.comp hQ
  have hP' := hre.continuousAt.tendsto.comp hP
  have hM' := hre.continuousAt.tendsto.comp hM
  let a := ((27/16:ℂ)*((16/81:ℂ)*(η:ℂ)^3)).re
  let b := ((η:ℂ)^2).re
  let c := ((η:ℂ)).re
  let e := (-(η:ℂ)).re
  let C : ℝ := ‖a‖+‖b‖+‖c‖+‖e‖+1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  have h₁C : ‖a‖ < C := by dsimp only [C]; linarith [norm_nonneg b,norm_nonneg c,norm_nonneg e]
  have h₂C : ‖b‖ < C := by dsimp only [C]; linarith [norm_nonneg a,norm_nonneg c,norm_nonneg e]
  have h₃C : ‖c‖ < C := by dsimp only [C]; linarith [norm_nonneg a,norm_nonneg b,norm_nonneg e]
  have h₄C : ‖e‖ < C := by dsimp only [C]; linarith [norm_nonneg a,norm_nonneg b,norm_nonneg c]
  have hB₁ := hT'.norm.eventually_lt_const h₁C
  have hB₂ := hQ'.norm.eventually_lt_const h₂C
  have hB₃ := hP'.norm.eventually_lt_const h₃C
  have hB₄ := hM'.norm.eventually_lt_const h₄C
  filter_upwards [hE,hB₁,hB₂,hB₃,hB₄] with N hN h₁ h₂ h₃ h₄
  have hr := hN.1
  have hr₁ := hr.1
  have hr₂ := hr.2
  have hσ := hN.2
  have hδ₁ : (1:ℝ)+d N*η = 2*(1-r N) := by dsimp [d,r,bfpSaddleRadius]; ring
  have hδ₂ : (1:ℝ)-d N*η = 2*r N := by dsimp [d,r,bfpSaddleRadius]; ring
  have hδ₃ : (1:ℝ)-(d N*η)/3 = (1+r N)/(3/2) := by dsimp [d,r,bfpSaddleRadius]; ring
  have hδ₄ : (1:ℝ)+(d N*η)/3 = (2-r N)/(3/2) := by dsimp [d,r,bfpSaddleRadius]; ring
  have hn₁ : 0 < 2*(1-r N) := by linarith
  have hn₂ : 0 < 2*r N := by linarith
  have hn₃ : 0 < 1+r N := by linarith
  have hn₄ : 0 < 2-r N := by linarith
  have hc (z : ℝ) (hz : 0 < z) : Complex.log ↑z = ↑(Real.log z) :=
    (Complex.ofReal_log hz.le).symm
  have hPlus : Complex.log (1+q N) = (Real.log (2*(1-r N)):ℂ) := by
    have hh := congrArg Complex.ofReal hδ₁
    push_cast at hh
    change 1+q N = _ at hh
    rw [← hc _ hn₁,hh] <;> push_cast <;> rfl
  have hMinus : Complex.log (1-q N) = (Real.log (2*r N):ℂ) := by
    have hh := congrArg Complex.ofReal hδ₂
    push_cast at hh
    change 1-q N = _ at hh
    rw [← hc _ hn₂,hh] <;> push_cast <;> rfl
  have hpm : Complex.log (1-q N/3) = (Real.log ((1+r N)/(3/2)):ℂ) := by
    have hh := congrArg Complex.ofReal hδ₃
    push_cast at hh
    change 1-q N/3 = _ at hh
    rw [← hc _ (by positivity),hh] <;> push_cast <;> rfl
  have hmp : Complex.log (1+q N/3) = (Real.log ((2-r N)/(3/2)):ℂ) := by
    have hh := congrArg Complex.ofReal hδ₄
    push_cast at hh
    change 1+q N/3 = _ at hh
    rw [← hc _ (by positivity),hh] <;> push_cast <;> rfl
  have hRad : (bfpCubicPhase (q N)).re = bfpCircleLog (r N) 1 := by
    have hA : bfpCircleA (r N) 1 = (1+r N)^2 := by unfold bfpCircleA; ring
    have hB : bfpCircleB (r N) 1 = (2-r N)^2 := by unfold bfpCircleB; ring
    have hD : bfpCircleD (r N) 1 = (1-r N)^2 := by unfold bfpCircleD; ring
    have hr₀ : 0 < r N := by linarith
    have hr₃ : 0 < 1-r N := by linarith
    rw [bfpCubicPhase,hpm,hmp,hPlus,hMinus,bfpCircleLog,hA,hB,hD]
    rw [← Complex.ofReal_sub,← Complex.ofReal_sub,← Complex.ofReal_ofNat,
      ← Complex.ofReal_div,← Complex.ofReal_add,Complex.ofReal_re]
    rw [Real.log_div hn₃.ne' (by norm_num),Real.log_div hn₄.ne' (by norm_num),
      Real.log_mul (by norm_num) hr₃.ne',Real.log_mul (by norm_num) hr₀.ne']
    simp only [Real.log_pow,Nat.cast_ofNat]
    ring
  change |(N:ℝ)*bfpCircleLog (r N) 1| ≤ C ∧ _
  have h₁' : |(N:ℝ)*bfpCircleLog (r N) 1| < C := by
    change ‖((N:ℂ)*bfpCubicPhase (q N)).re‖ < C at h₁
    simpa only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,
      Real.norm_eq_abs,hRad] using h₁
  have h₂' : |bfpScale N^2*(Real.log (2*r N)+Real.log (2*(1-r N)))| < C := by
    change ‖(((d N)⁻¹:ℂ)^2*bfpQuadPhase (q N)).re‖ < C at h₂
    rw [bfpQuadPhase,hPlus,hMinus] at h₂
    have he : (((d N)⁻¹:ℂ)^2*(-(Real.log (2*(1-r N)):ℂ)-(Real.log (2*r N):ℂ))).re =
        -(bfpScale N^2*(Real.log (2*r N)+Real.log (2*(1-r N)))) := by
      simp only [d,Complex.ofReal_inv,inv_inv]
      rw [← Complex.ofReal_neg,← Complex.ofReal_sub,← Complex.ofReal_pow,← Complex.ofReal_mul,
        Complex.ofReal_re]
      ring
    rw [he,Real.norm_eq_abs,abs_neg] at h₂
    exact h₂
  have h₃' : |bfpScale N*Real.log (2*(1-r N))| < C := by
    change ‖(((d N)⁻¹:ℂ)*Complex.log (1+q N)).re‖ < C at h₃
    rw [hPlus] at h₃
    simpa [d,← Complex.ofReal_mul,Real.norm_eq_abs] using h₃
  have h₄' : |bfpScale N*Real.log (2*r N)| < C := by
    change ‖(((d N)⁻¹:ℂ)*Complex.log (1+(d N:ℂ)*(-(η:ℂ)))).re‖ < C at h₄
    rw [show (1:ℂ)+(d N:ℂ)*(-(η:ℂ))=1-q N by dsimp [q]; ring,hMinus] at h₄
    simpa [d,← Complex.ofReal_mul,Real.norm_eq_abs] using h₄
  exact ⟨h₁'.le,h₂'.le,h₄'.le,h₃'.le⟩


private noncomputable def bfpSaddleOffset (u v L : ℝ) : ℝ :=
  10000*(|v-u|+max L 0+5)

private theorem bfpSaddleOffset_pos (u v L : ℝ) : 0 < bfpSaddleOffset u v L := by
  unfold bfpSaddleOffset
  positivity

private theorem bfpSaddle_log_decay {η : ℝ} (hη : 0 < η) {N : ℕ}
    (hσ : 0 < bfpScale N) (hr : bfpSaddleRadius η N ∈ Icc (1/3:ℝ) (1/2)) :
    bfpScale N*Real.log (2*bfpSaddleRadius η N) ≤ -η ∧
      η/2 ≤ bfpScale N*Real.log (2*(1-bfpSaddleRadius η N)) := by
  let σ := bfpScale N
  let t := η/σ
  let r := bfpSaddleRadius η N
  have ht : 0 < t := by dsimp [t,σ]; positivity
  have htr : t = 1-2*r := by dsimp [t,r,bfpSaddleRadius]; ring
  have hσt : σ*t = η := by dsimp [t,σ]; field_simp [hσ.ne']
  have hr₁ := hr.1
  have htm : t ≤ 1 := by rw [htr]; dsimp [r]; linarith
  constructor
  · have h := Real.log_le_sub_one_of_pos (show 0 < 2*r by dsimp [r]; linarith)
    have hh := mul_le_mul_of_nonneg_left h hσ.le
    change σ*Real.log (2*r) ≤ -η
    rw [show 2*r-1 = -t by rw [htr]; ring, mul_neg,hσt] at hh
    exact hh
  · have htpos : 0 < 1+t := by positivity
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr htpos)
    rw [Real.log_inv] at h
    have hhalf : t/2 ≤ 1-(1+t)⁻¹ := by
      rw [inv_eq_one_div, le_sub_comm, div_le_iff₀ htpos]
      nlinarith [mul_le_mul_of_nonneg_left htm ht.le]
    have hh := mul_le_mul_of_nonneg_left (show t/2 ≤ Real.log (1+t) by linarith) hσ.le
    rw [← mul_div_assoc,hσt,htr,show (1:ℝ)+(1-2*r)=2*(1-r) by ring] at hh
    exact hh

private theorem bfpPoleAngular_bound (u v L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s t θ : ℝ,
      -L ≤ s → -L ≤ t → |θ| ≤ Real.pi →
      ‖bfpPoleAngular N (bfpPoleA N u v t) (bfpPoleK N u v s)
        (bfpSaddleRadius (bfpSaddleOffset u v L) N) θ‖ ≤
        C * Real.exp (-(bfpSaddleOffset u v L/2)*(max s 0+max t 0)) *
          Real.exp (-(2/Real.pi^2)*(bfpScale N*θ)^2) := by
  let η := bfpSaddleOffset u v L
  let B := |v-u|+max L 0+4
  have hη : 0 < η := bfpSaddleOffset_pos u v L
  obtain ⟨C,hC,hlogs⟩ := bfpSaddleRadius_logs hη
  refine ⟨Real.exp (C*(9+|v-u|+2*max L 0)),by positivity,?_⟩
  filter_upwards [hlogs,bfpSaddleRadius_bounds hη,bfpScale_tendsto_atTop.eventually_ge_atTop 1] with N hlog hr hσ
  intro s t θ hs ht hθ
  let σ := bfpScale N
  let r := bfpSaddleRadius η N
  let f₁ := Real.log (2*r)
  let f₂ := Real.log (2*(1-r))
  let x := Real.cos θ
  let a : ℝ := bfpPoleA N u v t
  let k : ℝ := bfpPoleK N u v s
  let eA := a-((N:ℝ)/3-σ^2*(v-u)-σ*t)
  let eK := k-((N:ℝ)/3+σ^2*(v-u)-σ*s)
  have ha : |eA| ≤ 4 := (bfpPoleA_error N u v t).le
  have hk : |eK| ≤ 4 := (bfpPoleK_error N u v s).le
  have hσ₀ : 0 < σ := zero_lt_one.trans_le hσ
  have hσ2 : σ ≤ σ^2 := by nlinarith [mul_le_mul_of_nonneg_left hσ hσ₀.le]
  have hσ4 : (4:ℝ) ≤ 4*σ^2 := by nlinarith
  have hA : a-(N:ℝ)/3 ≤ σ^2*B := by
    have ht' : -t ≤ max L 0 := (neg_le.mpr ht).trans (le_max_left _ _)
    have he := (le_abs_self eA).trans ha
    have h₁ := mul_le_mul_of_nonneg_left (neg_le_abs (v-u)) (sq_nonneg σ)
    have h₂ := mul_le_mul_of_nonneg_left ht' hσ₀.le
    have h₃ := mul_le_mul_of_nonneg_right hσ2 (le_max_right L 0)
    dsimp [eA,B] at *
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨h0,h1,h2,h3⟩ := hlog
  change |(N:ℝ)*bfpCircleLog r 1| ≤ C at h0
  change |σ^2*(f₁+f₂)| ≤ C at h1
  change |σ*f₁| ≤ C at h2
  change |σ*f₂| ≤ C at h3
  have hdecay := bfpSaddle_log_decay hη hσ₀ hr
  change σ*f₁ ≤ -η ∧ η/2 ≤ σ*f₂ at hdecay
  have hP : σ*s*f₁ ≤ C*max L 0-η/2*max s 0 := by
    by_cases h : 0 ≤ s
    · rw [max_eq_left h]
      have hle := mul_le_mul_of_nonneg_right (hdecay.1.trans (by linarith : -η ≤ -η/2)) h
      linarith [mul_nonneg hC.le (le_max_right L 0)]
    · rw [max_eq_right (le_of_not_ge h),mul_zero,sub_zero]
      have hL : -s ≤ max L 0 := (neg_le.mpr hs).trans (le_max_left _ _)
      calc
        _ = (-s)*(-(σ*f₁)) := by ring
        _ ≤ max L 0 * C := by
          exact mul_le_mul hL ((neg_le_abs _).trans h2)
            (by linarith [hdecay.1]) (le_max_right _ _)
        _ = _ := mul_comm _ _
  have hQ : -σ*t*f₂ ≤ C*max L 0-η/2*max t 0 := by
    by_cases h : 0 ≤ t
    · rw [max_eq_left h]
      have hle := mul_le_mul_of_nonneg_right hdecay.2 h
      linarith [mul_nonneg hC.le (le_max_right L 0)]
    · rw [max_eq_right (le_of_not_ge h),mul_zero,sub_zero]
      have hL : -t ≤ max L 0 := (neg_le.mpr ht).trans (le_max_left _ _)
      calc
        _ = (-t)*(σ*f₂) := by ring
        _ ≤ max L 0 * C := by
          exact mul_le_mul hL ((le_abs_self _).trans h3) (by linarith [hdecay.2]) (le_max_right _ _)
        _ = _ := mul_comm _ _
  have hA₀ : eA*f₂ ≤ 4*C := by
    have hh := (abs_mul eA f₂).trans_le (mul_le_mul ha
      (by
        calc
          _ ≤ σ*|f₂| := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hσ (abs_nonneg f₂)
          _ = |σ*f₂| := by rw [abs_mul,abs_of_pos hσ₀]
          _ ≤ _ := h3) (abs_nonneg _) (by norm_num))
    exact (le_abs_self _).trans hh
  have hK₀ : -(eK*f₁) ≤ 4*C := by
    have hh := (abs_mul eK f₁).trans_le (mul_le_mul hk
      (by
        calc
          _ ≤ σ*|f₁| := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hσ (abs_nonneg f₁)
          _ = |σ*f₁| := by rw [abs_mul,abs_of_pos hσ₀]
          _ ≤ _ := h2) (abs_nonneg _) (by norm_num))
    exact (neg_le_abs _).trans hh
  have hd : -(v-u)*(σ^2*(f₁+f₂)) ≤ |v-u| * C := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul,abs_neg]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hcent : (N:ℝ)*bfpCircleLog r 1+(a-(N:ℝ)/3)*f₂-(k-(N:ℝ)/3)*f₁ ≤
      C*(9+|v-u|+2*max L 0)-η/2*(max s 0+max t 0) := by
    have hbase := (le_abs_self _).trans h0
    dsimp [eA,eK] at hA₀ hK₀
    linarith only [hbase,hP,hQ,hA₀,hK₀,hd]
  let Δ := Real.log (2*‖1-circleMap 0 r θ‖)-f₂
  have hΔ : 0 ≤ Δ ∧ Δ ≤ 2*(1-x) := bfpLogNorm_increment hr θ
  have hx : x ∈ Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hang := mul_le_mul_of_nonneg_left (bfpCircleLog_angle hr hx) (Nat.cast_nonneg N)
  have hgain : (2*B+1)*σ^2 ≤ (N:ℝ)*(1/2-r)/1000 := by
    have hn : (N:ℝ) = (27/16:ℝ)*σ^3 := by
      have hc := bfpScale_cube N
      dsimp [σ]
      linarith
    rw [hn]
    have he : 1/2-r = η/2*σ⁻¹ := by dsimp [r,bfpSaddleRadius,σ]; ring
    rw [he]
    have he' : (27/16:ℝ)*σ^3*(η/2*σ⁻¹)/1000 = (27*η/32000)*σ^2 := by
      field_simp
      ring
    rw [he']
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg σ)
    dsimp [B,η,bfpSaddleOffset] at *
    linarith [abs_nonneg (v-u),le_max_right L 0]
  have hloss := mul_le_mul_of_nonneg_right hgain (sub_nonneg.mpr hx.2)
  have hagain := (mul_le_mul_of_nonneg_right hA hΔ.1).trans
    (mul_le_mul_of_nonneg_left hΔ.2 (mul_nonneg (sq_nonneg σ) hB))
  have hgauss := mul_le_mul_of_nonneg_left (Real.cos_le_one_sub_mul_cos_sq hθ) (sq_nonneg σ)
  rw [bfpPoleAngular_norm hr,← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change (N:ℝ)*bfpCircleLog r x + (a-(N:ℝ)/3)*Real.log (2*‖1-circleMap 0 r θ‖) -
      (k-(N:ℝ)/3)*f₁ ≤ _
  dsimp only [Δ] at hagain
  nlinarith only [hcent,hang,hloss,hagain,hgauss]


private noncomputable def bfpSaddleIntegrand (u v L : ℝ) (N : ℕ) (s t y : ℝ) : ℂ :=
  (Ioc (-Real.pi*bfpScale N) (Real.pi*bfpScale N)).indicator
    (fun y => bfpPoleAngular N (bfpPoleA N u v t) (bfpPoleK N u v s)
      (bfpSaddleRadius (bfpSaddleOffset u v L) N) (y/bfpScale N)) y

private theorem bfpSaddleIntegrand_measurable (u v L : ℝ) (N : ℕ) (s t : ℝ) :
    Measurable (bfpSaddleIntegrand u v L N s t) := by
  unfold bfpSaddleIntegrand bfpPoleAngular
  exact (by fun_prop : Measurable (fun y : ℝ =>
    let z := circleMap 0 (bfpSaddleRadius (bfpSaddleOffset u v L) N) (y/bfpScale N)
    ((1+z)/(2-z))^N*(2*(1-z))^(bfpPoleA N u v t)*(2*z)^(-bfpPoleK N u v s))).indicator measurableSet_Ioc

private theorem bfpSaddleIntegrand_bound (u v L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s t y : ℝ, -L ≤ s → -L ≤ t →
      ‖bfpSaddleIntegrand u v L N s t y‖ ≤
        C*Real.exp (-(bfpSaddleOffset u v L/2)*(max s 0+max t 0))*
          Real.exp (-(2/Real.pi^2)*y^2) := by
  obtain ⟨C,hC,h⟩ := bfpPoleAngular_bound u v L
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_gt_atTop 0] with N hN hn s t y hs ht
  have hσ := bfpScale_pos hn
  by_cases hy : y ∈ Ioc (-Real.pi*bfpScale N) (Real.pi*bfpScale N)
  · have hθ : |y/bfpScale N| ≤ Real.pi := by
      rw [abs_le,le_div_iff₀ hσ,div_le_iff₀ hσ]
      exact ⟨hy.1.le,hy.2⟩
    have he : bfpScale N*(y/bfpScale N)=y := by field_simp
    rw [bfpSaddleIntegrand,Set.indicator_of_mem hy]
    simpa only [he] using hN s t (y/bfpScale N) hs ht hθ
  · rw [bfpSaddleIntegrand,Set.indicator_of_notMem hy,norm_zero]
    positivity

private theorem bfpSaddleIntegrand_eq {N : ℕ} (hN : 0 < N)
    (u v L s t : ℝ) (hK : 0 ≤ bfpPoleK N u v s)
    (hr : bfpSaddleRadius (bfpSaddleOffset u v L) N ∈ Icc (1/3:ℝ) (1/2)) :
    (bfpScaledPole N u v s t:ℂ) =
      (1/(2*(Real.pi:ℂ))) * ∫ y, bfpSaddleIntegrand u v L N s t y := by
  let σ := bfpScale N
  have hσ := bfpScale_pos hN
  let f := bfpPoleAngular N (bfpPoleA N u v t) (bfpPoleK N u v s)
    (bfpSaddleRadius (bfpSaddleOffset u v L) N)
  have hInt : (∫ y, bfpSaddleIntegrand u v L N s t y) =
      (σ:ℂ) * ∫ θ in -Real.pi..Real.pi, f θ := by
    unfold bfpSaddleIntegrand
    rw [integral_indicator measurableSet_Ioc,← intervalIntegral.integral_of_le
      (by have := Real.pi_pos; nlinarith)]
    rw [intervalIntegral.integral_comp_div f hσ.ne']
    simp only [neg_div, mul_div_cancel_right₀ _ hσ.ne',Complex.real_smul,σ]
  rw [hInt,bfpPoleAngular_scaled (lt_of_lt_of_le (by norm_num) hr.1) hr.2 N u v s t hK]
  change (σ:ℂ)/(2*(Real.pi:ℂ)) * (∫ θ in -Real.pi..Real.pi, f θ) = _
  ring

/-- A single inward-displaced circle gives uniform exponential decay on
the two upper half-lines, including the equal-time block. -/
theorem bfpScaledPole_tail (u v L : ℝ) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ᶠ N : ℕ in atTop,
      ∀ s₁ s₂ : ℝ, -L ≤ s₁ → -L ≤ s₂ →
        |bfpScaledPole N u v s₁ s₂| ≤ C * Real.exp (-(a * (max s₁ 0 + max s₂ 0))) := by
  obtain ⟨C,hC,h⟩ := bfpSaddleIntegrand_bound u v L
  let η := bfpSaddleOffset u v L
  let b : ℝ := 2/Real.pi^2
  have hb : 0 < b := by dsimp [b]; positivity
  have hη : 0 < η := bfpSaddleOffset_pos u v L
  refine ⟨C*Real.sqrt (Real.pi/b)/(2*Real.pi),η/2,by positivity,by positivity,?_⟩
  filter_upwards [h,bfpSaddleRadius_bounds hη,eventually_gt_atTop 0] with N hN hr hn s t hs ht
  by_cases hk : 0 ≤ bfpPoleK N u v s
  · let D := C*Real.exp (-(η/2)*(max s 0+max t 0))
    let G (y : ℝ) := D*Real.exp (-b*y^2)
    have hG : Integrable G := (integrable_exp_neg_mul_sq hb).const_mul D
    have hNorm (y : ℝ) : ‖bfpSaddleIntegrand u v L N s t y‖ ≤ G y := hN s t y hs ht
    have hI : ‖∫ y, bfpSaddleIntegrand u v L N s t y‖ ≤ ∫ y, G y :=
      norm_integral_le_of_norm_le hG (ae_of_all _ hNorm)
    have hE := bfpSaddleIntegrand_eq hn u v L s t hk hr
    have he : |bfpScaledPole N u v s t| = (1/(2*Real.pi)) *
        ‖∫ y, bfpSaddleIntegrand u v L N s t y‖ := by
      have h := congrArg norm hE
      simpa [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le] using h
    rw [he]
    refine (mul_le_mul_of_nonneg_left hI (by positivity)).trans_eq ?_
    unfold G
    rw [integral_const_mul,integral_gaussian]
    dsimp [D]
    ring
  · have hzero : bfpPoleKer N (bfpLabel N u) (bfpLatticeSite N u s)
        (bfpLabel N v) (bfpLatticeSite N v t) = 0 := by
      have htest : ¬ 0 < bfpLatticeSite N u s+bfpLabel N u+bfpLabel N v-1 := by
        unfold bfpPoleK at hk
        omega
      simp only [bfpPoleKer,ite_eq_right htest]
    simp only [bfpScaledPole,hzero,mul_zero,abs_zero]
    positivity


private theorem bfpPoleAngular_exp {r : ℝ} (hr : r ∈ Icc (1/3:ℝ) (1/2))
    (N : ℕ) (a k : ℤ) (θ : ℝ) :
    let q := (1:ℂ)-2*circleMap 0 r θ
    bfpPoleAngular N a k r θ =
      Complex.exp (((N:ℂ)*bfpCubicPhase q) +
        ((a:ℂ)-(N:ℂ)/3)*Complex.log (1+q) -
        ((k:ℂ)-(N:ℂ)/3)*Complex.log (1-q)) := by
  let z := circleMap 0 r θ
  let q := (1:ℂ)-2*z
  have hr₀ : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
  have hz : ‖z‖ = r := by simp [z,norm_circleMap_zero,abs_of_pos hr₀]
  have hz₀ : z ≠ 0 := by intro h; rw [h,norm_zero] at hz; linarith
  have h₁ : 1-z ≠ 0 := by
    intro h
    have he : z=1 := by linear_combination -h
    rw [he,norm_one] at hz
    linarith [hr.2]
  have h₂ : 2-z ≠ 0 := by
    intro h
    have he : z=2 := by linear_combination -h
    norm_num [he] at hz
    linarith [hr.2]
  have h₃ : 1+z ≠ 0 := by
    intro h
    have he : z=-1 := by linear_combination h
    rw [he,norm_neg,norm_one] at hz
    linarith [hr.2]
  have hp : 1+q = 2*(1-z) := by dsimp [q]; ring
  have hm : 1-q = 2*z := by dsimp [q]; ring
  have hp' : 1+q/3 = (2-z)/(3/2) := by dsimp [q]; ring
  have hm' : 1-q/3 = (1+z)/(3/2) := by dsimp [q]; ring
  change bfpPoleAngular N a k r θ = Complex.exp (_)
  have hE : (N:ℂ)*bfpCubicPhase q + ((a:ℂ)-(N:ℂ)/3)*Complex.log (1+q) -
      ((k:ℂ)-(N:ℂ)/3)*Complex.log (1-q) =
        (N:ℂ)*(Complex.log (1-q/3)-Complex.log (1+q/3)) +
          (a:ℂ)*Complex.log (1+q) + ((-k:ℤ):ℂ)*Complex.log (1-q) := by
    unfold bfpCubicPhase
    push_cast
    ring
  change _ = Complex.exp ((N:ℂ)*bfpCubicPhase q + ((a:ℂ)-(N:ℂ)/3)*Complex.log (1+q) -
      ((k:ℂ)-(N:ℂ)/3)*Complex.log (1-q))
  rw [hE,Complex.exp_add,Complex.exp_add,Complex.exp_nat_mul,Complex.exp_int_mul,
    Complex.exp_int_mul,Complex.exp_sub,hp,hm,hp',hm']
  rw [Complex.exp_log (div_ne_zero h₃ (by norm_num)),Complex.exp_log (div_ne_zero h₂ (by norm_num)),
    Complex.exp_log (mul_ne_zero (by norm_num) h₁),Complex.exp_log (mul_ne_zero (by norm_num) hz₀)]
  have hratio : ((1+z)/(3/2))/((2-z)/(3/2)) = (1+z)/(2-z) := by field_simp
  rw [hratio]
  rfl

private theorem bfpPoleRoundings_tendsto {ι : Type*} {l : Filter ι}
    {d : ι → ℂ} (hd : Tendsto d l (𝓝 0)) {e : ι → ℝ}
    (he : ∀ n, |e n| ≤ 4) : Tendsto (fun n => (e n:ℂ)*d n) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hNorm : Tendsto (fun n => ‖d n‖) l (𝓝 0) := by simpa only [norm_zero] using hd.norm
  refine squeeze_zero (fun _ => norm_nonneg _) ?_ (by simpa using hNorm.const_mul (4:ℝ))
  intro n
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (he n) (norm_nonneg (d n))

private theorem bfpSaddleIntegrand_tendsto {ι : Type*} {l : Filter ι}
    {n : ι → ℕ} {s t : ι → ℝ} {s₀ t₀ : ℝ}
    (hn : Tendsto n l atTop) (hs : Tendsto s l (𝓝 s₀)) (ht : Tendsto t l (𝓝 t₀))
    (u v L y : ℝ) :
    let q := (bfpSaddleOffset u v L:ℂ)-(y:ℂ)*Complex.I
    Tendsto (fun j => bfpSaddleIntegrand u v L (n j) (s j) (t j) y) l
      (𝓝 (Complex.exp (q^3/3+(v-u:ℝ)*q^2-(s₀+t₀:ℝ)*q))) := by
  let η := bfpSaddleOffset u v L
  let q := (η:ℂ)-(y:ℂ)*Complex.I
  let σ (j : ι) := bfpScale (n j)
  let δ (j : ι) := (σ j)⁻¹
  let w (j : ι) := bfpSaddleCoordinate η y (n j)
  let z (j : ι) := (δ j:ℂ)*w j
  let eA (j : ι) := (bfpPoleA (n j) u v (t j):ℝ) -
    ((n j:ℝ)/3-σ j^2*(v-u)-σ j*t j)
  let eK (j : ι) := (bfpPoleK (n j) u v (s j):ℝ) -
    ((n j:ℝ)/3+σ j^2*(v-u)-σ j*s j)
  have hη : 0 < η := bfpSaddleOffset_pos u v L
  have hσ := bfpScale_tendsto_atTop.comp hn
  have hδ : Tendsto δ l (𝓝 0) := bfpScale_inv_tendsto_zero.comp hn
  have hz₀ : ∀ᶠ j in l, 0 < σ j :=
    (hn.eventually (eventually_gt_atTop 0)).mono (fun _ h => bfpScale_pos h)
  have hδ₀ : ∀ᶠ j in l, 0 < δ j := hz₀.mono fun j h => inv_pos.mpr h
  have hw : Tendsto w l (𝓝 q) := (bfpSaddleCoordinate_tendsto η y).comp hn
  obtain ⟨hT,hQ,hP⟩ := bfpScaledPhase_tendsto hδ hδ₀ hw
  have hM := (bfpScaledPhase_tendsto hδ hδ₀ hw.neg).2.2
  have hT' : Tendsto (fun j => (σ j:ℂ)^3*bfpCubicPhase (z j)) l (𝓝 ((16/81:ℂ)*q^3)) := by
    simpa [z,δ,Complex.ofReal_inv] using hT
  have hQ' : Tendsto (fun j => (σ j:ℂ)^2*bfpQuadPhase (z j)) l (𝓝 (q^2)) := by
    simpa [z,δ,Complex.ofReal_inv] using hQ
  have hP' : Tendsto (fun j => (σ j:ℂ)*Complex.log (1+z j)) l (𝓝 q) := by
    simpa [z,δ,Complex.ofReal_inv] using hP
  have hM' : Tendsto (fun j => (σ j:ℂ)*Complex.log (1-z j)) l (𝓝 (-q)) := by
    simpa [z,δ,Complex.ofReal_inv,sub_eq_add_neg] using hM
  have hZ : Tendsto z l (𝓝 0) := by
    simpa [z] using (Complex.continuous_ofReal.continuousAt.tendsto.comp hδ).mul hw
  have hlogP : Tendsto (fun j => Complex.log (1+z j)) l (𝓝 0) := by
    have h1 : Tendsto (fun j => 1+z j) l (𝓝 (1:ℂ)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1:ℂ))).add hZ
    simpa [Function.comp_def] using
      (continuousAt_clog (by simp : (1:ℂ) ∈ Complex.slitPlane)).tendsto.comp h1
  have hlogM : Tendsto (fun j => Complex.log (1-z j)) l (𝓝 0) := by
    have h1 : Tendsto (fun j => 1-z j) l (𝓝 (1:ℂ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1:ℂ))).sub hZ
    simpa [Function.comp_def] using
      (continuousAt_clog (by simp : (1:ℂ) ∈ Complex.slitPlane)).tendsto.comp h1
  have hA := bfpPoleRoundings_tendsto hlogP (fun j => (bfpPoleA_error (n j) u v (t j)).le)
  have hK := bfpPoleRoundings_tendsto hlogM (fun j => (bfpPoleK_error (n j) u v (s j)).le)
  have hS := Complex.continuous_ofReal.continuousAt.tendsto.comp hs
  have hU := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  have hPhase := (((((hT'.const_mul (27/16:ℂ)).add (hQ'.const_mul ((v-u:ℝ):ℂ))).add
    (hS.mul hM')).sub (hU.mul hP')).add hA).sub hK
  have hlim : (27 / 16 : ℂ)*(16/81*q^3) + (v-u:ℝ)*q^2 + (s₀:ℂ)*(-q) -
      (t₀:ℂ)*q + 0 - 0 = q^3/3+(v-u:ℝ)*q^2-(s₀+t₀:ℝ)*q := by push_cast; ring
  rw [hlim] at hPhase
  have hExp := Complex.continuous_exp.continuousAt.tendsto.comp hPhase
  refine hExp.congr' ?_
  have hy : ∀ᶠ j in l, y ∈ Ioc (-Real.pi*σ j) (Real.pi*σ j) := by
    filter_upwards [hσ.eventually_gt_atTop ((|y|+1)/Real.pi)] with j hj
    have h := (div_lt_iff₀ Real.pi_pos).mp hj
    change |y|+1 < σ j*Real.pi at h
    rw [mul_comm (σ j)] at h
    exact ⟨by linarith [neg_le_abs y],by linarith [le_abs_self y]⟩
  filter_upwards [hy,hz₀,hn.eventually (bfpSaddleRadius_bounds hη)] with j hj hσj hr
  unfold bfpSaddleIntegrand
  rw [Set.indicator_of_mem hj,bfpPoleAngular_exp hr]
  have hZ' : z j = (1:ℂ)-2*circleMap 0 (bfpSaddleRadius η (n j)) (y/σ j) := by
    dsimp [z,w,δ,σ,bfpSaddleCoordinate]
    rw [Complex.ofReal_inv,← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hσj.ne'),one_mul]
  rw [← hZ']
  have hCube : (n j:ℂ) = (27/16:ℂ)*(σ j:ℂ)^3 := by
    have h := bfpScale_cube (n j)
    have he : (n j:ℝ)=(27/16:ℝ)*(σ j)^3 := by dsimp [σ]; linarith
    have hh := congrArg Complex.ofReal he
    push_cast at hh
    exact hh
  apply congrArg Complex.exp
  dsimp only [Function.comp_apply,eA,eK,σ]
  push_cast
  unfold bfpQuadPhase
  dsimp only [σ] at hCube
  linear_combination -(bfpCubicPhase (z j))*hCube


private noncomputable def bfpSaddleLimit (η d s t y : ℝ) : ℂ :=
  let q := (η:ℂ)-(y:ℂ)*Complex.I
  Complex.exp (q^3/3+(d:ℂ)*q^2-((s+t:ℝ):ℂ)*q)

private theorem bfpSaddleLimit_integral (η d s t : ℝ) (hη : 0 < η+d) :
    ((1/(2*(Real.pi:ℂ))) * ∫ y, bfpSaddleLimit η d s t y).re =
      Real.exp (d*(s+t)+(2/3)*d^3)*airyAiReal (s+t+d^2) := by
  let g (y : ℝ) := Complex.exp ((((η+d:ℝ):ℂ)+(y:ℂ)*Complex.I)^3/3 -
    ((s+t+d^2:ℝ):ℂ)*(((η+d:ℝ):ℂ)+(y:ℂ)*Complex.I))
  let c := Real.exp (d*(s+t)+(2/3)*d^3)
  have h (y : ℝ) : bfpSaddleLimit η d s t y = (c:ℂ)*g (-y) := by
    unfold bfpSaddleLimit c g
    rw [Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_const_mul]
  have hn : (∫ y, g (-y)) = ∫ y, g y :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (MeasurableEquiv.neg ℝ).measurableEmbedding g
  rw [hn,mul_left_comm]
  change ((c:ℂ)*AiryContour.airyContour (η+d) ((s+t+d^2:ℝ):ℂ)).re = _
  rw [AiryContour.airyContour_eq_airyAi (η+d) hη,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  rfl

private theorem bfpSaddle_pole_depth {ι : Type*} {l : Filter ι} {n : ι → ℕ} {s : ι → ℝ} {a : ℝ}
    (hn : Tendsto n l atTop) (hs : Tendsto s l (𝓝 a)) (u v : ℝ) :
    ∀ᶠ j in l, 0 ≤ bfpPoleK (n j) u v (s j) := by
  let M := |v-u|+|a|+6
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hσ := bfpScale_tendsto_atTop.comp hn
  filter_upwards [hσ.eventually_ge_atTop (4*M+1),
    hs.eventually_lt_const (show a < |a|+1 by linarith [le_abs_self a])] with j hj hS
  let σ := bfpScale (n j)
  have hσ₀ : 1 ≤ σ := by dsimp [σ] at *; linarith
  have hσ₂ : σ ≤ σ^2 := by nlinarith [mul_le_mul_of_nonneg_left hσ₀ (show 0 ≤ σ by linarith)]
  have hE := (abs_lt.mp (bfpPoleK_error (n j) u v (s j))).1
  have hC := bfpScale_cube (n j)
  change σ^3=(16/27:ℝ)*(n j:ℝ) at hC
  have h₁ := mul_le_mul_of_nonneg_left hS.le (show 0 ≤ σ by linarith)
  have h₂ := mul_le_mul_of_nonneg_left (neg_le_abs (v-u)) (sq_nonneg σ)
  have h₃ := mul_le_mul_of_nonneg_right hσ₂ (show 0 ≤ |a|+1 by positivity)
  have h₄ : (4:ℝ) ≤ 4*σ^2 := by nlinarith
  have h₅ := mul_le_mul_of_nonneg_right hj (sq_nonneg σ)
  have h0 : 0 ≤ (bfpPoleK (n j) u v (s j):ℝ) := by
    change -4 < (bfpPoleK (n j) u v (s j):ℝ) -
      ((n j:ℝ)/3+σ^2*(v-u)-σ*s j) at hE
    change (4*M+1)*σ^2 ≤ σ*σ^2 at h₅
    dsimp [M] at h₅
    nlinarith only [hE,hC,h₁,h₂,h₃,h₄,h₅,sq_nonneg σ]
  exact_mod_cast h0

private theorem bfpPole_tendsto_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {n : ι → ℕ} {s t : ι → ℝ} {s₀ t₀ : ℝ}
    (hn : Tendsto n l atTop) (hs : Tendsto s l (𝓝 s₀)) (ht : Tendsto t l (𝓝 t₀))
    (u v L : ℝ) (hS : ∀ᶠ j in l, -L ≤ s j ∧ -L ≤ t j) :
    Tendsto (fun j => bfpScaledPole (n j) u v (s j) (t j)) l
      (𝓝 (Real.exp ((v-u)*(s₀+t₀)+(2/3)*(v-u)^3) *
        airyAiReal (s₀+t₀+(v-u)^2))) := by
  let η := bfpSaddleOffset u v L
  let f := bfpSaddleLimit η (v-u) s₀ t₀
  have hη := bfpSaddleOffset_pos u v L
  have hηd : 0 < η+(v-u) := by dsimp [η,bfpSaddleOffset]; linarith [neg_le_abs (v-u),abs_nonneg (v-u),le_max_right L 0]
  obtain ⟨C,hC,hbound⟩ := bfpSaddleIntegrand_bound u v L
  let G (y : ℝ) := C*Real.exp (-(2/Real.pi^2)*y^2)
  have hG : Integrable G := (integrable_exp_neg_mul_sq (by positivity : 0 < 2/Real.pi^2)).const_mul C
  have hHd : ∀ᶠ j in l, ∀ᵐ y : ℝ, ‖bfpSaddleIntegrand u v L (n j) (s j) (t j) y‖ ≤ G y := by
    filter_upwards [hn.eventually hbound,hS] with j hj hj'
    apply ae_of_all _
    intro y
    refine (hj (s j) (t j) y hj'.1 hj'.2).trans ?_
    have he : Real.exp (-(η/2)*(max (s j) 0+max (t j) 0)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by dsimp [η]; positivity))
        (add_nonneg (le_max_right _ _) (le_max_right _ _)))
    dsimp [G]
    calc
      _ ≤ C*1*Real.exp (-(2/Real.pi^2)*y^2) := by gcongr
      _ = _ := by rw [mul_one]
  have hD := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure ℝ)) G
    (Eventually.of_forall (fun j => (bfpSaddleIntegrand_measurable u v L (n j) (s j) (t j)).aestronglyMeasurable))
    hHd hG (f := f) (ae_of_all _ (fun y => bfpSaddleIntegrand_tendsto hn hs ht u v L y))
  have hlim := Complex.continuous_re.continuousAt.tendsto.comp (hD.const_mul (1/(2*(Real.pi:ℂ))))
  rw [bfpSaddleLimit_integral η (v-u) s₀ t₀ hηd] at hlim
  refine hlim.congr' ?_
  filter_upwards [hn.eventually (eventually_gt_atTop 0),bfpSaddle_pole_depth hn hs u v,
    hn.eventually (bfpSaddleRadius_bounds hη)] with j hN hK hr
  have he := congrArg Complex.re (bfpSaddleIntegrand_eq hN u v L (s j) (t j) hK hr)
  exact he.symm

/-- At fixed row and column times the pole converges on compact level squares.
The square may contain the diagonal and the times may coincide. -/
theorem bfpScaledPole_tendstoUniformlyOn (u v : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    TendstoUniformlyOn (fun N : ℕ => fun p : ℝ × ℝ => bfpScaledPole N u v p.1 p.2)
      (fun p => Real.exp ((v - u) * (p.1 + p.2) + (2 / 3) * (v - u) ^ 3) *
        airyAiReal (p.1 + p.2 + (v - u) ^ 2))
      atTop (Set.Icc (-L) L ×ˢ Set.Icc (-L) L) := by
  let S := Set.Icc (-L) L ×ˢ Set.Icc (-L) L
  let F (p : ℝ×ℝ) := Real.exp ((v-u)*(p.1+p.2)+(2/3)*(v-u)^3)*
      airyAiReal (p.1+p.2+(v-u)^2)
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS).mp
  apply tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro p hp
  let l := (atTop : Filter ℕ) ×ˢ 𝓝[S] p
  have hP : Tendsto (Prod.snd : ℕ × (ℝ × ℝ) → ℝ × ℝ) l (𝓝 p) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  have hsp := continuous_fst.continuousAt.tendsto.comp hP
  have htp := continuous_snd.continuousAt.tendsto.comp hP
  have hcut : ∀ᶠ z : ℕ×(ℝ×ℝ) in l, -L ≤ z.2.1 ∧ -L ≤ z.2.2 :=
    ((tendsto_snd : Tendsto Prod.snd l (𝓝[S] p)).eventually self_mem_nhdsWithin).mono
      (fun z hz => ⟨hz.1.1,hz.2.1⟩)
  have ha := bfpPole_tendsto_filter (tendsto_fst : Tendsto Prod.fst l atTop) hsp htp u v L hcut
  have hAi : Continuous airyAiReal := by
    unfold airyAiReal
    exact Complex.continuous_re.comp
      ((continuous_iff_continuousAt.mpr fun z => (Complex.analyticAt_airyAi z).continuousAt).comp
        Complex.continuous_ofReal)
  have hF : Continuous F := by
    unfold F
    apply Continuous.mul
    · fun_prop
    · exact hAi.comp (by fun_prop)
  apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
  simpa [F] using (hF.continuousAt.tendsto.comp hP).dist ha

end AiryFdd
