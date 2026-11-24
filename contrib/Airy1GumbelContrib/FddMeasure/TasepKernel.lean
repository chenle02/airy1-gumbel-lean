/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FddMeasure.TasepSignedArray
import Airy1GumbelContrib.FddMeasure.FredholmSeries
import Airy1GumbelContrib.FredholmDet.Hadamard
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open Filter Function Matrix MeasureTheory Set
open scoped BigOperators ENNReal PowerSeries

/-!
# Period-two kernel of backward sequential TASEP

We specialize the finite gap determinant by coefficient algebra and sum the
principal minors for counting measure. No contour integration or infinite-system
construction is needed at fixed time.
-/

namespace AiryFdd

/-- The coefficient of degree `k` in the power series of `(1+z)^j` at zero.
A negative integer exponent uses its finite binomial coefficient formula. -/
noncomputable def tasepIntBinom (j : ℤ) (k : ℕ) : ℝ :=
  (Ring.choose j k : ℤ)

/-- The nonnegative binomial propagation term of the period-two BFP kernel, to be
subtracted. Its support is strictly forward in the particle label. -/
noncomputable def bfpFreeKer (n₁ z₁ n₂ z₂ : ℤ) : ℝ :=
  if n₁ < n₂ ∧ n₂ - n₁ ≤ z₁ - z₂ then
    (((z₁ - z₂ - 1).toNat).choose (n₂ - n₁ - 1).toNat : ℝ)
  else 0

/-- The pole term in the period-two kernel of Borodin–Ferrari–Prähofer (2007,
Corollary 2.2). At jump probability one half, it is minus the residue at zero of
(1+v)^(z₂+n₁+n₂−2) / (−v)^(z₁+n₁+n₂−1) times ((1−v)/(2+v))^N.
The regular factor is a formal power series, so only one coefficient is extracted. -/
noncomputable def bfpPoleKer (N : ℕ) (n₁ z₁ n₂ z₂ : ℤ) : ℝ :=
  let a := z₂ + n₁ + n₂ - 2
  let b := z₁ + n₁ + n₂ - 1
  if 0 < b then
    (-1 : ℝ) ^ (b - 1).toNat * (1 / 2 : ℝ) ^ N *
      (PowerSeries.binomialSeries ℝ a *
        (1 - PowerSeries.X : ℝ⟦X⟧) ^ N *
        PowerSeries.rescale (1 / 2 : ℝ) (PowerSeries.binomialSeries ℝ (-(N : ℤ)))).coeff
        (b - 1).toNat
  else 0

/-- The extended kernel of the alternating backward sequential model. -/
noncomputable def bfpKer (N : ℕ) (n₁ z₁ n₂ z₂ : ℤ) : ℝ :=
  bfpPoleKer N n₁ z₁ n₂ z₂ - bfpFreeKer n₁ z₁ n₂ z₂

/-- The gap event forbids sites strictly below each cutoff, so the physical particle must
be at or above that cutoff, as in BFP07 Theorem 2.1. -/
noncomputable def bfpCutKernel (N : ℕ) (J : Finset ℤ) (a : J → ℤ) :
    (J × ℤ) → (J × ℤ) → ℝ :=
  fun x y => if x.2 < a x.1 ∧ y.2 < a y.1 then bfpKer N x.1.1 x.2 y.1.1 y.2 else 0

/-- Relabelling by `R` translates the initial positions by `−2R`, leaving the period-two
kernel unchanged. The signs here follow the displayed kernel exponents. -/
theorem bfpKer_shift (N : ℕ) (n₁ z₁ n₂ z₂ R : ℤ) :
    bfpKer N (n₁ + R) (z₁ - 2 * R) (n₂ + R) (z₂ - 2 * R) =
      bfpKer N n₁ z₁ n₂ z₂ := by
  have h₁ : n₂ + R - (n₁ + R) = n₂ - n₁ := by ring
  have h₂ : z₁ - 2 * R - (z₂ - 2 * R) = z₁ - z₂ := by ring
  have ha : z₂ - 2 * R + (n₁ + R) + (n₂ + R) - 2 = z₂ + n₁ + n₂ - 2 := by ring
  have hb : z₁ - 2 * R + (n₁ + R) + (n₂ + R) - 1 = z₁ + n₁ + n₂ - 1 := by ring
  have ht : n₁ + R < n₂ + R ↔ n₁ < n₂ := by omega
  have hz : z₁ - 2 * R - (z₂ - 2 * R) - 1 = z₁ - z₂ - 1 := by omega
  simp only [bfpKer, bfpFreeKer, bfpPoleKer, ha, hb, ht, h₁, h₂, hz]


private noncomputable def tasepPlus (e : ℤ) : ℝ⟦X⟧ :=
  PowerSeries.binomialSeries ℝ e

private noncomputable def tasepMinus (e : ℤ) : ℝ⟦X⟧ :=
  PowerSeries.rescale (-1 : ℝ) (tasepPlus e)

private noncomputable def tasepCoinSeries (N : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.C ((1/2 : ℝ)^N) * tasepPlus N

private theorem tasepPlus_coeff (e : ℤ) (k : ℕ) :
    (tasepPlus e).coeff k = tasepIntBinom e k := by
  simp [tasepPlus, tasepIntBinom, zsmul_eq_mul]

private theorem tasepPlus_add (a b : ℤ) : tasepPlus (a+b) = tasepPlus a * tasepPlus b :=
  PowerSeries.binomialSeries_add _ _

private theorem tasepMinus_add (a b : ℤ) : tasepMinus (a+b) = tasepMinus a * tasepMinus b := by
  rw [tasepMinus, tasepPlus_add, map_mul]
  rfl

private theorem tasepPlus_nat (n : ℕ) : tasepPlus n = (1 + PowerSeries.X)^n :=
  PowerSeries.binomialSeries_nat n

private theorem tasepMinus_nat (n : ℕ) : tasepMinus n = (1 - PowerSeries.X)^n := by
  rw [tasepMinus,tasepPlus_nat,map_pow,map_add,map_one,PowerSeries.rescale_X]
  simp [sub_eq_add_neg]

/-- Multiplication by this series takes a strict prefix sum of coefficients. -/
private noncomputable def tasepStrictSumSeries : ℝ⟦X⟧ :=
  PowerSeries.X * tasepMinus (-1)

private theorem tasepMinus_neg_one_coeff (k : ℕ) :
    (tasepMinus (-1)).coeff k = 1 := by
  have hh : PowerSeries.rescale (-1 : ℝ) (PowerSeries.invOneSubPow ℝ 1) =
        PowerSeries.binomialSeries ℝ (-1 : ℤ) := by
    simpa using PowerSeries.rescale_neg_one_invOneSubPow (A := ℝ) 1
  have h := congrArg (PowerSeries.coeff (R := ℝ) k) hh
  change _ = (tasepPlus (-1)).coeff k at h
  rw [PowerSeries.coeff_rescale] at h
  have hcoef : ((PowerSeries.invOneSubPow ℝ 1 : ℝ⟦X⟧)).coeff k = 1 := by
    simp [PowerSeries.invOneSubPow]
  rw [hcoef, mul_one] at h
  rw [tasepMinus, PowerSeries.coeff_rescale, ← h, ← mul_pow]
  simp

private theorem tasepStrictSumSeries_coeff (k : ℕ) :
    tasepStrictSumSeries.coeff k = if k = 0 then 0 else 1 := by
  cases k with
  | zero => simp [tasepStrictSumSeries]
  | succ k =>
    rw [tasepStrictSumSeries,mul_comm,← pow_one (PowerSeries.X : ℝ⟦X⟧),
      PowerSeries.coeff_mul_X_pow]
    simp [tasepMinus_neg_one_coeff]

private theorem tasepCoeff_mul_strictSum (g : ℝ⟦X⟧) (k : ℕ) :
    (g * tasepStrictSumSeries).coeff k = ∑ l ∈ Finset.range k, g.coeff l := by
  rw [PowerSeries.coeff_mul]
  calc
    _ = ∑ l ∈ Finset.range (k + 1), g.coeff l * tasepStrictSumSeries.coeff (k-l) :=
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => g.coeff i * tasepStrictSumSeries.coeff j) k
    _ = _ := ?_
  rw [Finset.sum_range_succ]
  have hk : k-k = 0 := Nat.sub_self k
  simp only [tasepStrictSumSeries_coeff,hk,ite_true,mul_zero,add_zero]
  apply Finset.sum_congr rfl
  intro l hl
  simp [Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hl)]

private theorem tasepCoinSeries_coeff (N n : ℕ) :
    (tasepCoinSeries N).coeff n = tasepFZero N n := by
  rw [tasepCoinSeries, PowerSeries.coeff_C_mul, tasepPlus_coeff]
  simp [tasepFZero, tasepIntBinom, Ring.choose_natCast]


private theorem tasepCountPi {X : Type*} [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (k : ℕ) : (Measure.pi (fun _ : Fin k => Measure.count : Fin k → Measure X)) =
      Measure.count := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton]
  simp

private theorem tasepIntegralCount_finite {X I : Type*} [Fintype I] [MeasurableSpace X]
    [MeasurableSingletonClass X] (e : I ↪ X) (f : X → ℝ)
    (h : ∀ x ∉ Set.range e, f x = 0) :
    ∫ x, f x ∂Measure.count = ∑ i, f (e i) := by
  classical
  let S := Finset.univ.map e
  have hs : ∀ x ∉ (↑S : Set X), f x = 0 := by
    intro x hx
    exact h x (by simpa [S] using hx)
  have hi : IntegrableOn f (↑S : Set X) Measure.count := by
    rw [← (S : Set X).biUnion_of_singleton]
    exact (integrableOn_finite_biUnion (f := f) (μ := Measure.count)
      (t := fun x : X => ({x} : Set X)) S.finite_toSet).2
      (fun x _ => integrableOn_singleton (x := x) (hx := by simp))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs, setIntegral_finset S hi]
  simp [S, Finset.sum_map]

private theorem tasepCountCoeff_eq_finite {X : Type*} [Countable X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (K : X → X → ℝ) (S : Finset X)
    (h : ∀ (k : ℕ) (x : Fin k → X), (∃ i, x i ∉ S) →
      (Matrix.of (fun i j : Fin k => K (x i) (x j))).det = 0) (k : ℕ) :
    kernelFredholmCoeff Measure.count K k =
      (1 / (k.factorial : ℝ)) *
        ∑ x : Fin k → S, (Matrix.of (fun i j : Fin k => K (x i).1 (x j).1)).det := by
  let e : (Fin k → S) ↪ (Fin k → X) :=
    ⟨fun x i => (x i).1, fun x y h => funext fun i => Subtype.ext (congrFun h i)⟩
  rw [kernelFredholmCoeff, tasepCountPi]
  congr 1
  apply tasepIntegralCount_finite e
  intro x hx
  apply h
  by_contra! hh
  exact hx ⟨fun i => ⟨x i,hh i⟩, rfl⟩

private noncomputable def tasepTupleFibreEquiv {I : Type*} [Fintype I] [DecidableEq I]
    {k : ℕ} (S : Finset I) :
    {x : Fin k → I // Injective x ∧ Finset.univ.image x = S} ≃ (Fin k ≃ S) where
  toFun x := Equiv.ofBijective
    (fun i => ⟨x.1 i, (Finset.ext_iff.mp x.2.2 _).mp (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩)
    ⟨fun _ _ h => x.2.1 (congrArg Subtype.val h), fun s => by
      have hs : s.1 ∈ Finset.univ.image x.1 := x.2.2.symm ▸ s.2
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hs
      exact ⟨i,Subtype.ext hi⟩⟩
  invFun e := ⟨fun i => (e i).1,
    Subtype.val_injective.comp e.injective, by
      ext s
      constructor
      · rintro h
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
        exact (e i).2
      · intro hs
        obtain ⟨i,hi⟩ := e.surjective ⟨s,hs⟩
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,congrArg Subtype.val hi⟩⟩
  left_inv x := Subtype.ext rfl
  right_inv e := Equiv.ext (fun i => Subtype.ext rfl)

/-- Ordered tuples enumerate each principal minor k! times. This identity does not
require a trace-class operator. -/
private theorem tasepCountMinorSum {I : Type*} [Fintype I] [DecidableEq I]
    (K : Matrix I I ℝ) (k : ℕ) :
    (∑ x : Fin k → I, Matrix.det (K.submatrix x x)) =
      (k.factorial : ℝ) * ∑ A ∈ (Finset.univ : Finset I).powersetCard k,
        (K.submatrix (Subtype.val : A → I) Subtype.val).det := by
  classical
  let T : Finset (Fin k → I) := Finset.univ.filter Injective
  let F (x : Fin k → I) := Finset.univ.image x
  have hT : (∑ x : Fin k → I, (K.submatrix x x).det) = ∑ x ∈ T, (K.submatrix x x).det := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : Injective x
    · simp [h]
    · have hh : ∃ i j, x i = x j ∧ i ≠ j := by
        by_contra! hn
        exact h (fun i j hij => hn i j hij)
      obtain ⟨i,j,hij,hne⟩ := hh
      rw [ite_eq_right h]
      exact Matrix.det_zero_of_row_eq hne (funext fun l => by simp [Matrix.submatrix_apply,hij])
  rw [hT, ← Finset.sum_fiberwise_of_maps_to (s := T)
    (t := (Finset.univ : Finset I).powersetCard k) (g := F) (by
      intro x hx
      have hinj := (Finset.mem_filter.mp hx).2
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
        change (Finset.univ.image x).card = k
        rw [Finset.card_image_of_injective _ hinj]
        simp⟩)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hcard := (Finset.mem_powersetCard.mp hA).2
  let e := A.equivFinOfCardEq hcard
  have hty : (↥(T.filter (fun x => F x = A))) ≃ Equiv.Perm (Fin k) :=
    (Equiv.subtypeEquivRight (fun x => by simp [T,F,Finset.mem_filter])).trans
      ((tasepTupleFibreEquiv A).trans
        { toFun := fun f => f.trans e
          invFun := fun f => f.trans e.symm
          left_inv := fun f => by ext i; simp
          right_inv := fun f => by ext i; simp })
  have hconstant (x : Fin k → I) (hx : x ∈ T.filter (fun x => F x = A)) :
      (K.submatrix x x).det = (K.submatrix (Subtype.val : A → I) Subtype.val).det := by
    have hxi : Injective x ∧ F x = A := by simpa [T,Finset.mem_filter] using hx
    exact Matrix.det_submatrix_equiv_self (tasepTupleFibreEquiv A ⟨x,hxi⟩)
      (K.submatrix (Subtype.val : A → I) Subtype.val)
  rw [Finset.sum_congr rfl hconstant, Finset.sum_const, nsmul_eq_mul]
  have hc : (T.filter (fun x => F x = A)).card = k.factorial := by
    rw [← Fintype.card_coe, Fintype.card_congr hty, Fintype.card_perm, Fintype.card_fin]
  rw [hc]


/-- If any tuple leaving the finite site set has zero determinant, the counting-measure
Fredholm series is the ordinary determinant on that set. -/
private theorem tasepCountSeries_eq_det {X : Type*} [Countable X] [DecidableEq X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (K : X → X → ℝ) (S : Finset X)
    (h : ∀ (k : ℕ) (x : Fin k → X), (∃ i, x i ∉ S) →
      (Matrix.of (fun i j : Fin k => K (x i) (x j))).det = 0) :
    kernelFredholmSeries Measure.count K = (1 - (Matrix.of fun i j : S => K i.1 j.1)).det := by
  classical
  let A : Matrix S S ℝ := Matrix.of fun i j => K i.1 j.1
  have hh (k : ℕ) : kernelFredholmCoeff Measure.count K k =
      ∑ U ∈ (Finset.univ : Finset S).powersetCard k,
        (A.submatrix (Subtype.val : U → S) Subtype.val).det := by
    rw [tasepCountCoeff_eq_finite K S h]
    have hl (x : Fin k → S) : (Matrix.of fun i j : Fin k => K (x i).1 (x j).1) =
        A.submatrix x x := rfl
    simp_rw [hl, tasepCountMinorSum]
    have hn : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    rw [← mul_assoc, one_div_mul_cancel hn, one_mul]
  unfold kernelFredholmSeries
  simp_rw [hh]
  rw [tsum_eq_sum (s := Finset.range (S.card+1))]
  · rw [show (1 - A : Matrix S S ℝ) = 1 + (-1 : ℝ) • A by simp [sub_eq_add_neg]]
    rw [HilbertSchmidt.Hadamard.det_one_add_smul_eq_sum_minors A (-1)]
    symm
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset S).powerset) (t := Finset.range (S.card+1))
      (g := Finset.card) (by
        intro U hU
        have hp := Finset.card_le_card (Finset.mem_powerset.mp hU)
        simpa using Nat.lt_succ_of_le hp)]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum, Finset.powersetCard_eq_filter]
    apply Finset.sum_congr rfl
    intro U hU
    have hcard := (Finset.mem_filter.mp hU).2
    rw [hcard,mul_comm]
  · intro k hk
    have hk' : S.card < k := by simpa [Finset.mem_range] using hk
    have he : (Finset.univ : Finset S).powersetCard k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro U hU
      obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp hU
      have hl := Finset.card_le_card hs
      simp only [Finset.card_univ,Fintype.card_coe,hc] at hl
      omega
    rw [he,Finset.sum_empty,mul_zero]


private theorem tasepCoeff_X_one (g : ℝ⟦X⟧) (k : ℕ) :
    (g * PowerSeries.X).coeff (k+1) = g.coeff k := by
  simpa only [pow_one] using PowerSeries.coeff_mul_X_pow g 1 k

private theorem tasepMinus_succ (j : ℤ) :
    tasepMinus (j+1) = tasepMinus j * (1 - PowerSeries.X) := by
  rw [tasepMinus_add]
  have h := tasepMinus_nat 1
  simpa using congrArg (tasepMinus j * ·) h

private theorem tasepNegCoeff (N j : ℕ) (z : ℤ) :
    (tasepDiff^[j]) (tasepFZero N) (z - j) =
      if 0 ≤ z then (-1 : ℝ)^j * (tasepCoinSeries N * tasepMinus j).coeff z.toNat else 0 := by
  induction j generalizing z with
  | zero =>
    by_cases hz : 0 ≤ z
    · have hzero : tasepMinus 0 = 1 := by simpa using tasepMinus_nat 0
      simp only [iterate_zero_apply, Nat.cast_zero, sub_zero, hz, ite_true, hzero,
        pow_zero, mul_one, one_mul, tasepCoinSeries_coeff, Int.toNat_of_nonneg hz]
    · simp [tasepFZero,hz]
  | succ j ih =>
    rw [iterate_succ_apply', tasepDiff,
      show z - (j+1 : ℕ) = (z-1)-(j : ℤ) by push_cast; ring,
      show (z-1)-(j : ℤ)+1 = z-j by ring, ih (z-1), ih z]
    rw [Nat.cast_succ,tasepMinus_succ,← mul_assoc, mul_sub,mul_one,map_sub]
    by_cases hz : 0 ≤ z
    · rw [ite_eq_left hz, ite_eq_left hz]
      cases hzn : z.toNat with
      | zero =>
        have hz0 : z = 0 := by omega
        have hzneg : ¬0 ≤ z-1 := by omega
        simp only [hzneg,ite_false,hzn,map_mul,PowerSeries.constantCoeff_X,mul_zero,pow_succ,
          PowerSeries.coeff_zero_eq_constantCoeff_apply,zero_sub,sub_zero]
        ring
      | succ k =>
        have hzp : 0 ≤ z-1 := by omega
        have hzk : (z-1).toNat = k := by omega
        simp only [hzp,ite_true,hzk,hzn,tasepCoeff_X_one,pow_succ]
        ring
    · have hz' : ¬0 ≤ z-1 := by omega
      simp only [hz,hz',ite_false,sub_zero]

private theorem tasepF_nonpositive_eq_iter (N j : ℕ) (x : ℤ) :
    tasepF (-(j : ℤ)) x N = (tasepDiff^[j]) (tasepFZero N) x := by
  cases j <;> rfl

private theorem tasepCoeff_shift_zero {R : Type*} [Semiring R] (g : R⟦X⟧) (n j : ℕ) :
    (g * PowerSeries.X^j).coeff n = if j ≤ n then g.coeff (n-j) else 0 := by
  rw [PowerSeries.coeff_mul]
  by_cases h : j ≤ n
  · rw [ite_eq_left h, Finset.sum_eq_single (n-j,j)]
    · rw [PowerSeries.coeff_X_pow,ite_eq_left rfl,mul_one]
    · intro i hi hne
      rw [PowerSeries.coeff_X_pow,ite_eq_right,mul_zero]
      intro he
      obtain ⟨a,b⟩ := i
      change b = j at he
      subst b
      have ha : a+j = n := Finset.mem_antidiagonal.mp hi
      exact hne (Prod.ext (by omega) rfl)
    · intro hn
      exact (hn (Finset.mem_antidiagonal.mpr (Nat.sub_add_cancel h))).elim
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro i hi
    have hs := Finset.mem_antidiagonal.mp hi
    rw [PowerSeries.coeff_X_pow,ite_eq_right,mul_zero]
    omega

/-- The terminal functions for an alternating finite window are supported in the crop. -/
private theorem tasepF_flat_coefficient (N j z : ℕ) :
    tasepF (-(j : ℤ)) ((z : ℤ)-2*j) N =
      (-1 : ℝ)^j * (tasepCoinSeries N * tasepMinus j * PowerSeries.X^j).coeff z := by
  rw [tasepF_nonpositive_eq_iter, show (z : ℤ) - 2*j = (z-j : ℤ)-j by ring,
    tasepNegCoeff, tasepCoeff_shift_zero]
  by_cases h : j ≤ z
  · have hi : 0 ≤ (z : ℤ) - j := by omega
    rw [ite_eq_left h,ite_eq_left hi]
    have hh : ((z : ℤ)-j).toNat = z-j := by omega
    rw [hh]
  · have hi : ¬0 ≤ (z : ℤ) - j := by omega
    rw [ite_eq_right h,ite_eq_right hi,mul_zero]


/-- Only finitely many sites contribute to the Fredholm series. A tuple below
the common lower bound has a zero row at a site of minimum position. -/
private theorem tasepBfp_cut_finite {J : Finset ℤ} (N : ℕ) (a : J → ℤ)
    (L U : ℤ) (hL : ∀ i j : J, L + i.1 + j.1 - 2 ≤ 0) (hU : ∀ j : J, a j - 1 ≤ U)
    (S : Finset (J × ℤ))
    (hS : ∀ p : J × ℤ, p ∈ S ↔ L ≤ p.2 ∧ p.2 ≤ U ∧ p.2 < a p.1) :
    kernelFredholmSeries Measure.count (bfpCutKernel N J a) =
      (1 - (Matrix.of fun i j : S => bfpKer N i.1.1.1 i.1.2 j.1.1.1 j.1.2)).det := by
  classical
  have hzero (k : ℕ) (x : Fin k → J × ℤ) (h : ∃ i, x i ∉ S) :
      (Matrix.of (fun i j : Fin k => bfpCutKernel N J a (x i) (x j))).det = 0 := by
    obtain ⟨i,hi⟩ := h
    by_cases hc : ∃ u, ¬(x u).2 < a (x u).1
    · obtain ⟨u,hu⟩ := hc
      apply Matrix.det_eq_zero_of_row_eq_zero u
      intro j
      simp [bfpCutKernel,hu]
    · have hcut (j : Fin k) : (x j).2 < a (x j).1 := by
        by_contra hn
        exact hc ⟨j,hn⟩
      have hlow : (x i).2 < L := by
        by_contra! hl
        exact hi ((hS (x i)).mpr ⟨hl, by have := hU (x i).1; have := hcut i; omega, hcut i⟩)
      obtain ⟨u,_,hu⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin k))
        (fun i => (x i).2) ⟨i,Finset.mem_univ _⟩
      have hlt := (hu i (Finset.mem_univ _)).trans_lt hlow
      apply Matrix.det_eq_zero_of_row_eq_zero u
      intro j
      have hpos := hu j (Finset.mem_univ _)
      have hp := hL (x u).1 (x j).1
      have hpole : ¬ 0 < (x u).2 + (x u).1.1 + (x j).1.1 - 1 := by omega
      have hfree : ¬((x u).1.1 < (x j).1.1 ∧ (x j).1.1 - (x u).1.1 ≤ (x u).2 - (x j).2) := by
        omega
      simp only [Matrix.of_apply,bfpCutKernel,hcut, and_self, ite_true,bfpKer,bfpPoleKer,bfpFreeKer,hpole,hfree,ite_false,sub_zero]
  rw [tasepCountSeries_eq_det _ S hzero]
  have hmat : (Matrix.of (fun i j : S => bfpCutKernel N J a i.1 j.1)) =
      (Matrix.of fun i j : S => bfpKer N i.1.1.1 i.1.2 j.1.1.1 j.1.2) := by
    ext i j
    have hi := ((hS i.1).mp i.2).2.2
    have hj := ((hS j.1).mp j.2).2.2
    simp [bfpCutKernel,hi,hj]
  rw [hmat]


private theorem tasepSum_crop_lt {L U z : ℤ} (hz : z ∈ Finset.Icc L U) (f : ℕ → ℝ) :
    (∑ s : Finset.Icc L U, if s.1 < z then f (s.1-L).toNat else 0) =
      ∑ d ∈ Finset.range (z-L).toNat, f d := by
  classical
  rw [← Finset.sum_filter]
  have hz' := Finset.mem_Icc.mp hz
  refine Finset.sum_bij (fun s _ => (s.1-L).toNat) ?_ ?_ ?_ ?_
  · intro s hs
    have hl := (Finset.mem_Icc.mp s.2).1
    have hu := (Finset.mem_filter.mp hs).2
    exact Finset.mem_range.mpr (by omega)
  · intro i _ j _ he
    apply Subtype.ext
    have hi := (Finset.mem_Icc.mp i.2).1
    have hj := (Finset.mem_Icc.mp j.2).1
    omega
  · intro d hd
    have h := Finset.mem_range.mp hd
    refine ⟨⟨L+d,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by change L+(d:ℤ) < z; omega⟩
    · change (L+(d:ℤ)-L).toNat = d
      omega
  · intro _ _; rfl

private theorem tasepSum_crop_gt {L U z : ℤ} (hz : z ∈ Finset.Icc L U) (f : ℕ → ℝ) :
    (∑ s : Finset.Icc L U, if z < s.1 then f (s.1-z-1).toNat else 0) =
      ∑ d ∈ Finset.range (U-z).toNat, f d := by
  classical
  rw [← Finset.sum_filter]
  have hz' := Finset.mem_Icc.mp hz
  refine Finset.sum_bij (fun s _ => (s.1-z-1).toNat) ?_ ?_ ?_ ?_
  · intro s hs
    have hl := (Finset.mem_filter.mp hs).2
    have hu := (Finset.mem_Icc.mp s.2).2
    exact Finset.mem_range.mpr (by omega)
  · intro i hi j hj he
    apply Subtype.ext
    have h1 := (Finset.mem_filter.mp hi).2
    have h2 := (Finset.mem_filter.mp hj).2
    omega
  · intro d hd
    have h := Finset.mem_range.mp hd
    refine ⟨⟨z+1+d,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by change z < z+1+(d:ℤ); omega⟩
    · change (z+1+(d:ℤ)-z-1).toNat = d
      omega
  · intro _ _; rfl

private theorem tasepPropagation_apply_stage {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (p q : TasepFiniteSite N y) (d : ℕ) (h : p.1.1+d = q.1.1) :
    finiteLevelPropagation N y p q = (finiteLevelTransfer N y ^ d) p q := by
  unfold finiteLevelPropagation
  rw [Matrix.sum_apply, Finset.sum_eq_single d]
  · intro b _ hb
    exact finiteLevelTransfer_pow_zero N y b p q (by omega)
  · intro hd
    have := q.1.2
    exfalso
    exact hd (Finset.mem_range.mpr (by omega))

private theorem tasepPropagation_zero_backward {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (p q : TasepFiniteSite N y) (h : q.1 < p.1) :
    finiteLevelPropagation N y p q = 0 := by
  unfold finiteLevelPropagation
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun d _ => finiteLevelTransfer_pow_zero N y d p q (by
    have hh : q.1.1 < p.1.1 := h
    omega)

private theorem tasepHockeyStick (d k : ℕ) :
    (∑ r ∈ Finset.range d, (Nat.choose r k : ℝ)) = (Nat.choose d (k+1) : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ, Nat.cast_add]
    exact add_comm _ _

private theorem tasepStrictWalk_count {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (k : ℕ) (p q : TasepFiniteSite N y) (h : p.1.1 + (k+1) = q.1.1) :
    (finiteLevelTransfer N y ^ (k+1)) p q =
      if q.2.1 < p.2.1 then (Nat.choose (p.2.1-q.2.1-1).toNat k : ℝ) else 0 := by
  classical
  induction k generalizing p q with
  | zero =>
    rw [pow_one]
    simp only [finiteLevelTransfer,Matrix.of_apply,← h,true_and,Nat.choose_zero_right,Nat.cast_one]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply, Fintype.sum_prod_type]
    let l : Fin m := ⟨p.1.1+(k+1), by have := q.1.2; omega⟩
    rw [Finset.sum_eq_single l]
    · have ihl (s : Finset.Icc (tasepCropLo y) (tasepCropHi N y)) :
          (finiteLevelTransfer N y ^ (k+1)) p (l,s) =
            if s.1 < p.2.1 then (Nat.choose (p.2.1-s.1-1).toNat k : ℝ) else 0 :=
          ih p (l,s) rfl
      simp_rw [ihl]
      have hstep : q.1.1 = l.1+1 := by change q.1.1 = p.1.1+(k+1)+1; omega
      simp only [finiteLevelTransfer,Matrix.of_apply,hstep,true_and]
      by_cases hh : q.2.1 < p.2.1
      · rw [ite_eq_left hh]
        let f (d : ℕ) : ℝ := if (d:ℤ) < p.2.1-q.2.1-1
          then (Nat.choose (p.2.1-q.2.1-2-(d:ℤ)).toNat k : ℝ) else 0
        have he :
            (∑ s : Finset.Icc (tasepCropLo y) (tasepCropHi N y),
              (if s.1 < p.2.1 then (Nat.choose (p.2.1-s.1-1).toNat k : ℝ) else 0) *
              (if q.2.1 < s.1 then 1 else 0)) =
            ∑ s : Finset.Icc (tasepCropLo y) (tasepCropHi N y),
              if q.2.1 < s.1 then f (s.1-q.2.1-1).toNat else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hq : q.2.1 < s.1
          · have hz : (((s.1-q.2.1-1).toNat : ℕ) : ℤ) = s.1-q.2.1-1 := by omega
            simp only [hq,ite_true,mul_one,f,hz]
            have ha : s.1-q.2.1-1 < p.2.1-q.2.1-1 ↔ s.1 < p.2.1 := by omega
            have hb : p.2.1-q.2.1-2-(s.1-q.2.1-1) = p.2.1-s.1-1 := by ring
            simp only [ha,hb]
          · simp [hq]
        rw [he,tasepSum_crop_gt q.2.2]
        let d := (p.2.1-q.2.1-1).toNat
        have hdc : (d : ℤ) = p.2.1-q.2.1-1 := by dsimp [d]; omega
        have hd : d ≤ (tasepCropHi N y-q.2.1).toNat := by
          have hu := (Finset.mem_Icc.mp p.2.2).2
          omega
        rw [← Finset.sum_subset (Finset.range_mono hd)]
        · have hfun (r : ℕ) (hr : r ∈ Finset.range d) :
              f r = (Nat.choose (d-1-r) k : ℝ) := by
            have hr' := Finset.mem_range.mp hr
            have hz : (r : ℤ) < p.2.1-q.2.1-1 := by omega
            have hc : (p.2.1-q.2.1-2-(r:ℤ)).toNat = d-1-r := by omega
            simp only [f,hz,ite_true,hc]
          refine (Finset.sum_congr rfl hfun).trans ?_
          refine (Finset.sum_range_reflect (fun r => (Nat.choose r k : ℝ)) d).trans ?_
          exact tasepHockeyStick d k
        · intro r hr hnr
          have hnr' : ¬(r:ℤ) < p.2.1-q.2.1-1 := by
            rw [Finset.mem_range] at hnr
            omega
          simp [f,hnr']
      · rw [ite_eq_right hh]
        apply Finset.sum_eq_zero
        intro s _
        by_cases hs : q.2.1 < s.1
        · have hn : ¬s.1 < p.2.1 := by omega
          simp [hs,hn]
        · simp [hs]
    · intro i _ hi
      apply Finset.sum_eq_zero
      intro s _
      have hn : p.1.1+(k+1) ≠ i.1 := fun he => hi (Fin.ext he.symm)
      rw [finiteLevelTransfer_pow_zero N y (k+1) p (i,s) hn,zero_mul]
    · intro hl
      exact (hl (Finset.mem_univ l)).elim


private def tasepFlatStart (m : ℕ) (lo : ℤ) (k : Fin m) : ℤ :=
  flatInitial (lo + (k.1 : ℤ))

private theorem tasepFlatStart_strictAnti (m : ℕ) (lo : ℤ) : StrictAnti (tasepFlatStart m lo) := by
  intro i j hij
  have hij' : (i.1 : ℕ) < j.1 := hij
  unfold tasepFlatStart flatInitial
  omega

private theorem tasepFlat_lo {m : ℕ} (hm : 0 < m) (lo : ℤ) :
    tasepCropLo (tasepFlatStart m lo) = flatInitial (lo + (m : ℤ) - 1) := by
  simp only [tasepCropLo,dite_eq_left hm,tasepFlatStart]
  have h : ((m-1 : ℕ) : ℤ) = (m : ℤ)-1 := by omega
  rw [h]
  congr 1
  ring

private theorem tasepFlat_hi {m : ℕ} (hm : 0 < m) (N : ℕ) (lo : ℤ) :
    tasepCropHi N (tasepFlatStart m lo) = flatInitial lo + N := by
  simp [tasepCropHi,hm,tasepFlatStart]

private theorem tasepFlat_terminal_ydiff {m : ℕ} (hm : 0 < m) (lo : ℤ) (j : Fin m) :
    tasepFlatStart m lo j.rev - tasepCropLo (tasepFlatStart m lo) = 2*(j.1:ℤ) := by
  rw [tasepFlat_lo hm]
  unfold tasepFlatStart flatInitial
  have h : (j.rev.1 : ℤ) = (m : ℤ)-1-j.1 := by
    rw [Fin.val_rev]
    have := j.2
    omega
  omega

private theorem tasepProp_terminal_step {m : ℕ} (N : ℕ) (y : Fin m → ℤ) :
    finiteLevelPropagation N y * finiteLevelTerminal N y = finiteLevelTerminal N y +
      finiteLevelTransfer N y * (finiteLevelPropagation N y * finiteLevelTerminal N y) := by
  let Q := 1 - finiteLevelTransfer N y
  let R := finiteLevelPropagation N y
  let C := finiteLevelTerminal N y
  have hQ : IsUnit Q.det := by
    change IsUnit (1-finiteLevelTransfer N y).det
    rw [finiteLevelTransfer_det_one_sub]; exact isUnit_one
  have hI : Q * R = 1 := by
    have hr : R = Q⁻¹ := finiteLevelPropagation_eq_inv N y
    exact hr.symm ▸ Matrix.mul_nonsing_inv Q hQ
  have h := congrArg (fun A => A * C) hI
  rw [Matrix.one_mul, Matrix.mul_assoc] at h
  change (1 - finiteLevelTransfer N y) * (R * C) = C at h
  rw [Matrix.sub_mul,Matrix.one_mul] at h
  change R * C = C + finiteLevelTransfer N y * (R * C)
  exact sub_eq_iff_eq_add.mp h

private theorem tasepStrictSumSeries_pow (d : ℕ) :
    tasepStrictSumSeries^d = PowerSeries.X^d * tasepMinus (-(d:ℤ)) := by
  induction d with
  | zero =>
    have h : tasepMinus 0 = 1 := by simpa using tasepMinus_nat 0
    simp [h]
  | succ d ih =>
    rw [pow_succ,ih,tasepStrictSumSeries,Nat.cast_succ,
      show -((d:ℤ)+1) = -(d:ℤ)+(-1) by ring,tasepMinus_add,pow_succ]
    ring

private theorem tasepFlat_prop_terminal {m : ℕ} (N : ℕ) (lo : ℤ)
    (p : TasepFiniteSite N (tasepFlatStart m lo)) (j : Fin m) :
    (finiteLevelPropagation N (tasepFlatStart m lo) *
      finiteLevelTerminal N (tasepFlatStart m lo)) p j =
      (-1 : ℝ)^j.1 * (tasepCoinSeries N * tasepMinus (j.1:ℤ) * PowerSeries.X^j.1 *
        tasepStrictSumSeries^(m-1-p.1.1)).coeff (p.2.1-tasepCropLo (tasepFlatStart m lo)).toNat := by
  classical
  let y := tasepFlatStart m lo
  let V := finiteLevelPropagation N y * finiteLevelTerminal N y
  let g := tasepCoinSeries N * tasepMinus (j.1:ℤ) * PowerSeries.X^j.1
  have h (d : ℕ) : ∀ p : TasepFiniteSite N y, m-1-p.1.1 = d →
      V p j = (-1 : ℝ)^j.1 * (g*tasepStrictSumSeries^d).coeff (p.2.1-tasepCropLo y).toNat := by
    induction d with
    | zero =>
      intro p hp
      have hpv : p.1.1+1 = m := by have := p.1.2; omega
      have hhm : 0 < m := by have := p.1.2; omega
      have htr : (finiteLevelTransfer N y * V) p j = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro q _
        have hq : ¬q.1.1 = p.1.1+1 := by have := q.1.2; omega
        simp [finiteLevelTransfer,hq]
      have hv := congrArg (fun A : Matrix (TasepFiniteSite N y) (Fin m) ℝ => A p j)
        (tasepProp_terminal_step N y)
      change V p j = finiteLevelTerminal N y p j + (finiteLevelTransfer N y * V) p j at hv
      rw [hv,htr,add_zero,pow_zero,mul_one]
      simp only [finiteLevelTerminal,Matrix.of_apply,hpv,ite_true]
      have hz : ((((p.2.1-tasepCropLo y).toNat) : ℕ) : ℤ) = p.2.1-tasepCropLo y :=
        Int.toNat_of_nonneg (sub_nonneg.mpr (Finset.mem_Icc.mp p.2.2).1)
      have hy : tasepFlatStart m lo j.rev - tasepCropLo y = 2*(j.1:ℤ) :=
        tasepFlat_terminal_ydiff hhm lo j
      have hd : p.2.1-y j.rev = ((p.2.1-tasepCropLo y).toNat : ℤ)-2*j.1 := by
        change p.2.1-tasepFlatStart m lo j.rev = _
        omega
      rw [hd]
      exact tasepF_flat_coefficient N j.1 _
    | succ d ih =>
      intro p hp
      have hpv : p.1.1+1 < m := by omega
      let l : Fin m := ⟨p.1.1+1,hpv⟩
      have hl : m-1-l.1 = d := by change m-1-(p.1.1+1) = d; omega
      have hv := congrArg (fun A : Matrix (TasepFiniteSite N y) (Fin m) ℝ => A p j)
        (tasepProp_terminal_step N y)
      change V p j = finiteLevelTerminal N y p j + (finiteLevelTransfer N y * V) p j at hv
      rw [hv]
      have hterm : finiteLevelTerminal N y p j = 0 := by
        simp [finiteLevelTerminal,show ¬p.1.1+1=m by omega]
      rw [hterm,zero_add,Matrix.mul_apply,Fintype.sum_prod_type,Finset.sum_eq_single l]
      · have he (s : Finset.Icc (tasepCropLo y) (tasepCropHi N y)) :
          finiteLevelTransfer N y p (l,s) * V (l,s) j =
            (-1 : ℝ)^j.1 * (if s.1 < p.2.1 then
              (g*tasepStrictSumSeries^d).coeff (s.1-tasepCropLo y).toNat else 0) := by
          rw [ih (l,s) hl]
          change (if p.1.1+1 = p.1.1+1 ∧ s.1 < p.2.1 then (1:ℝ) else 0) * _ = _
          by_cases hs : s.1 < p.2.1 <;> simp only [hs, true_and, ite_true, ite_false, one_mul, zero_mul, mul_zero]
        simp_rw [he]
        rw [← Finset.mul_sum]
        have hsum := tasepSum_crop_lt p.2.2 (fun k => (g*tasepStrictSumSeries^d).coeff k)
        refine (congrArg ((-1:ℝ)^j.1 * ·) hsum).trans ?_
        rw [pow_succ,← mul_assoc,tasepCoeff_mul_strictSum]
      · intro k _ hk
        apply Finset.sum_eq_zero
        intro s _
        have hv : ¬k.1 = p.1.1+1 := fun he => hk (Fin.ext he)
        simp [finiteLevelTransfer,hv]
      · intro hn
        exact (hn (Finset.mem_univ l)).elim
  exact h _ p rfl


private noncomputable def tasepPhiFactor (N k : ℕ) : ℝ⟦X⟧ :=
  (1 + PowerSeries.C 2 * PowerSeries.X) *
    PowerSeries.rescale (1/2 : ℝ) (tasepPlus (-(N:ℤ))) * tasepPlus (-1-k)

private noncomputable def tasepPhi (N k : ℕ) (z : ℤ) : ℝ :=
  (-1 : ℝ)^k * (tasepPhiFactor N k * tasepPlus z).coeff k

private noncomputable def tasepPsiPoly (N k : ℕ) : Polynomial ℝ :=
  Polynomial.C ((1/2 : ℝ)^N) * (1 + Polynomial.X)^N *
    (1 - Polynomial.X)^k * Polynomial.X^k

private theorem tasepPsiPoly_coe (N k : ℕ) :
    (tasepPsiPoly N k : ℝ⟦X⟧) = tasepCoinSeries N * tasepMinus k * PowerSeries.X^k := by
  simp [tasepPsiPoly,tasepCoinSeries,tasepPlus_nat,tasepMinus_nat]

private theorem tasepPsiPoly_degree (N k : ℕ) : (tasepPsiPoly N k).natDegree ≤ N+2*k := by
  have h₁ : ((1 + Polynomial.X : Polynomial ℝ)^N).natDegree ≤ N := by
    simpa using (Polynomial.natDegree_pow_le (p := (1 + Polynomial.X : Polynomial ℝ)) (n := N))
  have h₂ : ((1 - Polynomial.X : Polynomial ℝ)^k).natDegree ≤ k := by
    have hd : (1 - Polynomial.X : Polynomial ℝ).natDegree ≤ 1 :=
      (Polynomial.natDegree_sub_le _ _).trans (by simp)
    exact (Polynomial.natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left k hd)
  calc
    _ ≤ (Polynomial.C ((1/2 : ℝ)^N) * (1 + Polynomial.X)^N *
        (1 - Polynomial.X)^k : Polynomial ℝ).natDegree + k :=
      (Polynomial.natDegree_mul_le).trans (by simp)
    _ ≤ ((Polynomial.C ((1/2 : ℝ)^N) * (1 + Polynomial.X)^N : Polynomial ℝ).natDegree + k)+k :=
      Nat.add_le_add_right ((Polynomial.natDegree_mul_le).trans (Nat.add_le_add_left h₂ _)) _
    _ ≤ _ := by
      have hh : (Polynomial.C ((1/2 : ℝ)^N) * (1 + Polynomial.X)^N : Polynomial ℝ).natDegree ≤ N :=
        Polynomial.natDegree_mul_le.trans (by simpa using h₁)
      omega

private theorem tasepPsiPhi_eval (N k H : ℕ) (hH : N+2*k < H) :
    (∑ z ∈ Finset.range H, PowerSeries.C ((tasepPsiPoly N k).coeff z) * tasepPlus (z:ℤ)) =
      PowerSeries.rescale (1/2 : ℝ) (tasepPlus N) * tasepPlus k *
        PowerSeries.C ((-1:ℝ)^k) * PowerSeries.X^k := by
  have hf := Polynomial.eval₂_eq_sum_range' (PowerSeries.C : ℝ →+* ℝ⟦X⟧)
    ((tasepPsiPoly_degree N k).trans_lt hH) (1 + PowerSeries.X)
  simp_rw [tasepPlus_nat]
  rw [← hf]
  have hC : PowerSeries.C ((1/2 : ℝ)^N) * (1 + (1 + PowerSeries.X))^N =
      PowerSeries.rescale (1/2 : ℝ) ((1 + PowerSeries.X)^N) := by
    simp only [map_pow,map_add,map_one,PowerSeries.rescale_X,← mul_pow]
    congr 1
    have hhalf : (PowerSeries.C (1/2 : ℝ) : ℝ⟦X⟧) *
        (1 + (1 + PowerSeries.X)) = 1 + PowerSeries.C (1/2 : ℝ) * PowerSeries.X := by
      rw [show (1 : ℝ⟦X⟧) + (1 + PowerSeries.X) = PowerSeries.C 2 + PowerSeries.X by
        rw [show (2:ℝ) = 1+1 by norm_num, map_add,map_one]; ring]
      rw [mul_add,← map_mul]
      norm_num
    exact hhalf
  rw [tasepPsiPoly]
  have hn : -(PowerSeries.X : ℝ⟦X⟧) = (-1 : ℝ⟦X⟧)*PowerSeries.X := (neg_one_mul _).symm
  simp only [Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_add,Polynomial.eval₂_sub,
    Polynomial.eval₂_one,Polynomial.eval₂_C,Polynomial.eval₂_X,
    show (1:ℝ⟦X⟧) - (1+PowerSeries.X) = -PowerSeries.X by abel, hn, mul_pow]
  rw [hC]
  simp only [map_pow,map_neg,map_one]
  ring

private theorem tasepPhi_cancellation (d : ℕ) :
    ((1 + PowerSeries.C 2 * PowerSeries.X) * tasepPlus (-(d:ℤ)-1)).coeff d =
      if d = 0 then 1 else 0 := by
  -- The coefficient vanishes in positive degree by the central binomial identity.
  cases d with
  | zero => simp [tasepPlus,PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ d =>
    have hps : tasepPlus (-((d+2:ℕ):ℤ)) =
        PowerSeries.rescale (-1 : ℝ) (PowerSeries.invOneSubPow ℝ (d+2)) :=
      (PowerSeries.rescale_neg_one_invOneSubPow (d+2)).symm
    rw [show -((d+1:ℕ):ℤ)-1 = -((d+2:ℕ):ℤ) by push_cast; ring,hps]
    simp only [add_mul,one_mul,mul_assoc,map_add,PowerSeries.coeff_C_mul, mul_comm PowerSeries.X,
      tasepCoeff_X_one, PowerSeries.coeff_rescale, PowerSeries.invOneSubPow, PowerSeries.coeff_mk,
      Nat.succ_ne_zero, ite_false]
    have hc : Nat.choose (d+1+(d+1)) (d+1) =
        2 * Nat.choose (d+1+d) (d+1) := by
      have h := Nat.choose_succ_succ (d+1+d) d
      have hs := Nat.choose_symm (n := d+1+d) (k := d) (by omega)
      have h₁ : d+1+(d+1) = (d+1+d)+1 := by omega
      have h₃ : d+1+d-d = d+1 := by omega
      rw [h₃] at hs
      rw [h₁,h,hs]
      omega
    rw [hc,Nat.cast_mul,pow_succ]
    ring

private theorem tasepPsiPhi_ortho (N k j H : ℕ) (hH : N+2*k < H) :
    (∑ z ∈ Finset.range H, (tasepPsiPoly N k).coeff z * tasepPhi N j z) =
      if k = j then 1 else 0 := by
  have hprod (z : ℕ) : (tasepPsiPoly N k).coeff z * tasepPhi N j z =
      (-1:ℝ)^j * (tasepPhiFactor N j *
        (PowerSeries.C ((tasepPsiPoly N k).coeff z) * tasepPlus (z:ℤ))).coeff j := by
    rw [tasepPhi, ← mul_left_comm (PowerSeries.C _) _, PowerSeries.coeff_C_mul]
    ring
  simp_rw [hprod]
  rw [← Finset.mul_sum,← map_sum,← Finset.mul_sum,tasepPsiPhi_eval N k H hH]
  have hreg : tasepPhiFactor N j *
      (PowerSeries.rescale (1/2:ℝ) (tasepPlus N) * tasepPlus k *
        PowerSeries.C ((-1 : ℝ)^k) * PowerSeries.X^k) =
      PowerSeries.C ((-1 : ℝ)^k) * ((1+PowerSeries.C 2*PowerSeries.X)*tasepPlus ((k:ℤ)-j-1)) *
        PowerSeries.X^k := by
    have hcancel : PowerSeries.rescale (1/2:ℝ) (tasepPlus (-(N:ℤ))) *
        PowerSeries.rescale (1/2:ℝ) (tasepPlus N) = 1 := by
      rw [← map_mul,← tasepPlus_add,neg_add_cancel]
      simp [tasepPlus]
    have hadd : tasepPlus (-1-(j:ℤ)) * tasepPlus k = tasepPlus ((k:ℤ)-j-1) := by
      rw [← tasepPlus_add]
      congr 1
      ring
    unfold tasepPhiFactor
    calc
      _ = PowerSeries.C ((-1:ℝ)^k) * (1+PowerSeries.C 2*PowerSeries.X) *
          (PowerSeries.rescale (1/2:ℝ) (tasepPlus (-(N:ℤ))) *
            PowerSeries.rescale (1/2:ℝ) (tasepPlus N)) *
          (tasepPlus (-1-(j:ℤ))*tasepPlus k) * PowerSeries.X^k := by ring
      _ = _ := by rw [hcancel,mul_one,hadd]; ring
  rw [hreg,tasepCoeff_shift_zero]
  by_cases h : k ≤ j
  · rw [ite_eq_left h,PowerSeries.coeff_C_mul]
    have he : (k:ℤ)-(j:ℤ)-1 = -((j-k:ℕ):ℤ)-1 := by omega
    rw [he,tasepPhi_cancellation]
    by_cases heq : k = j
    · subst j
      simp [← mul_pow]
    · have hne : j-k ≠ 0 := by omega
      simp [heq,hne]
  · have hne : k ≠ j := by omega
    simp [h,hne]


private abbrev TasepTwoSeries := (ℝ⟦X⟧)⟦X⟧

private noncomputable def tasepW : TasepTwoSeries := PowerSeries.X
private noncomputable def tasepV : TasepTwoSeries := PowerSeries.C (PowerSeries.X : ℝ⟦X⟧)

private def tasepGeo {R : Type*} [Semiring R] (k : ℕ) (a b : R) : R :=
  ∑ j ∈ Finset.range (k+1), a^j * b^(k-j)

private theorem tasepGeo_mul_sub {R : Type*} [CommRing R] (k : ℕ) (a b : R) :
    (b-a) * tasepGeo k a b = b^(k+1)-a^(k+1) := by
  simpa [tasepGeo] using (Commute.all a b).mul_neg_geom_sum₂ (k+1)

private noncomputable def tasepDiagonalCoeff (k : ℕ) (f : TasepTwoSeries) : ℝ :=
  PowerSeries.coeff k (PowerSeries.coeff k f)

private theorem tasepDiagonalCoeff_drop {k : ℕ} (f g h : TasepTwoSeries) :
    tasepDiagonalCoeff k (f + g * tasepW^(k+1) + h * tasepV^(k+1)) =
      tasepDiagonalCoeff k f := by
  unfold tasepDiagonalCoeff tasepW tasepV
  simp only [map_add, tasepCoeff_shift_zero, not_le_of_gt (Nat.lt_succ_self k), ite_false,
    map_zero, add_zero, ← map_pow, PowerSeries.coeff_mul_C]

private theorem tasepGeo_factor (k : ℕ) :
    (1+tasepV-tasepW) * tasepGeo k (-tasepW*(1-tasepW)) (tasepV*(1+tasepV)) =
      (1+tasepV)^(k+1) * tasepGeo k (-tasepW) tasepV +
        (-tasepW)^(k+1) * tasepGeo k (1-tasepW) (1+tasepV) := by
  let w := tasepW
  let v := tasepV
  have hvw : v+w ≠ 0 := by
    intro h
    have hh := congrArg (PowerSeries.coeff (R := ℝ⟦X⟧) 1) h
    simp [v,w,tasepV,tasepW] at hh
  apply mul_left_cancel₀ hvw
  calc
    _ = (v*(1+v) - (-w*(1-w))) * tasepGeo k (-w*(1-w)) (v*(1+v)) := by
      change (v+w) * ((1+v-w)*_) = _
      ring
    _ = (v*(1+v))^(k+1)-(-w*(1-w))^(k+1) := tasepGeo_mul_sub k _ _
    _ = (1+v)^(k+1) * (v^(k+1)-(-w)^(k+1)) +
        (-w)^(k+1)*((1+v)^(k+1)-(1-w)^(k+1)) := by rw [mul_pow,mul_pow]; ring
    _ = _ := by
      rw [← tasepGeo_mul_sub k (-w) v, ← tasepGeo_mul_sub k (1-w) (1+v)]
      change _ = (v+w) * _
      ring

/-- The terms divisible by either variable to degree k+1 contribute zero
to the coefficient of degree k in both variables. The two remaining factors
encode evaluation at the second root in Borodin–Ferrari–Prähofer (2007), Section 4. -/
private theorem tasepGeo_discard (k : ℕ) :
    ∃ g h : TasepTwoSeries,
    (1+2*tasepV) * tasepGeo k (-tasepW*(1-tasepW)) (tasepV*(1+tasepV)) =
      (1+tasepV)^(k+1) * tasepGeo k (-tasepW) tasepV +
        g*tasepW^(k+1) + h*tasepV^(k+1) := by
  let v := tasepV
  let w := tasepW
  let G := tasepGeo k (-w*(1-w)) (v*(1+v))
  have hunit : IsUnit (1+v-w) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp only [v,w,tasepW,tasepV,map_sub,map_add,map_one,PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, sub_zero]
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp
  obtain ⟨u,hu⟩ := hunit
  have hg : (v+w)*G =
      ((↑(u⁻¹) : TasepTwoSeries) * (1+v)^(k+1)) * v^(k+1) +
      (-((↑(u⁻¹) : TasepTwoSeries) * (-(1-w))^(k+1))) * w^(k+1) := by
    have hn : (↑u : TasepTwoSeries) * ((v+w)*G) =
        (v*(1+v))^(k+1)-(-w*(1-w))^(k+1) := by
      rw [hu, ← mul_assoc, show (1+v-w)*(v+w) = v*(1+v)-(-w*(1-w)) by ring]
      exact tasepGeo_mul_sub k _ _
    have he := congrArg (fun x : TasepTwoSeries => ↑(u⁻¹) * x) hn
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at he
    rw [he, mul_sub, mul_pow, show -w*(1-w) = (-(1-w))*w by ring, mul_pow]
    ring
  refine ⟨(-1)^(k+1)*tasepGeo k (1-w) (1+v) - (↑(u⁻¹) : TasepTwoSeries)* (-(1-w))^(k+1),
    (↑(u⁻¹) : TasepTwoSeries)*(1+v)^(k+1), ?_⟩
  change (1+2*v)*G = _
  rw [show (1+2*v)*G = (1+v-w)*G+(v+w)*G by ring, hg]
  have he := tasepGeo_factor k
  change (1+v-w)*G = _ at he
  rw [he, neg_eq_neg_one_mul, mul_pow]
  ring

private theorem tasepDiagonalCoeff_geo (k : ℕ) (f g : ℝ⟦X⟧) :
    tasepDiagonalCoeff k
      (PowerSeries.map (PowerSeries.C : ℝ →+* ℝ⟦X⟧) f *
        PowerSeries.C g * tasepGeo k (-tasepW) tasepV) =
      (f * PowerSeries.rescale (-1 : ℝ) g).coeff k := by
  unfold tasepGeo
  rw [Finset.mul_sum]
  unfold tasepDiagonalCoeff
  rw [map_sum,map_sum,PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Finset.sum_range_reflect
    (fun j => f.coeff j * (PowerSeries.rescale (-1 : ℝ) g).coeff (k-j)) (k+1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hn : k+1-1-j = k-j := by omega
  have hk : k-(k-j) = j := by omega
  have hneg : -tasepW = (-1 : TasepTwoSeries)*PowerSeries.X := (neg_one_mul _).symm
  simp only [hneg,tasepV,mul_pow,← map_pow, PowerSeries.coeff_rescale, hn,hk]
  rw [show (PowerSeries.map (PowerSeries.C : ℝ →+* ℝ⟦X⟧) f * PowerSeries.C g) *
      (((-1 : TasepTwoSeries)^j * (PowerSeries.X^j)) *
        PowerSeries.C ((PowerSeries.X : ℝ⟦X⟧)^(k-j))) =
      (PowerSeries.map (PowerSeries.C : ℝ →+* ℝ⟦X⟧) f *
        PowerSeries.C (g*((-1:ℝ⟦X⟧)^j)*PowerSeries.X^(k-j))) * PowerSeries.X^j by
      simp only [map_mul,map_pow,map_neg,map_one]; ring]
  rw [tasepCoeff_shift_zero,ite_eq_left hle,PowerSeries.coeff_mul_C,PowerSeries.coeff_map]
  have hme : PowerSeries.C (f.coeff (k-j)) * (g * (-1:ℝ⟦X⟧)^j * PowerSeries.X^(k-j)) =
      (PowerSeries.C (f.coeff (k-j) * (-1:ℝ)^j)*g) * PowerSeries.X^(k-j) := by
    simp only [map_mul,map_pow,map_neg,map_one]
    ring
  refine (congrArg (PowerSeries.coeff (R := ℝ) k) hme).trans ?_
  rw [tasepCoeff_shift_zero,ite_eq_left (Nat.sub_le _ _),hk,PowerSeries.coeff_C_mul]
  ring

private theorem tasepBirth_pow_zero {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (i : Fin m) (q : TasepFiniteSite N y) (d : ℕ) (h : i.1+d ≠ q.1.1) :
    (finiteLevelBirth N y * finiteLevelTransfer N y ^ d) i q = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : i = p.1
  · rw [finiteLevelTransfer_pow_zero N y d p q (by simpa only [← hp] using h),mul_zero]
  · simp [finiteLevelBirth,hp]

private theorem tasepBirth_prop_apply {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (i : Fin m) (q : TasepFiniteSite N y) :
    (finiteLevelBirth N y * finiteLevelPropagation N y) i q =
      if i.1 ≤ q.1.1 then (Nat.choose (tasepCropHi N y-q.2.1).toNat (q.1.1-i.1) : ℝ) else 0 := by
  classical
  rw [Matrix.mul_apply,Fintype.sum_prod_type,Finset.sum_eq_single i]
  · by_cases hi : i.1 ≤ q.1.1
    · rw [ite_eq_left hi]
      let d := q.1.1-i.1
      have hd : i.1 + d = q.1.1 := Nat.add_sub_of_le hi
      have hh (s : Finset.Icc (tasepCropLo y) (tasepCropHi N y)) :
          finiteLevelPropagation N y (i,s) q = (finiteLevelTransfer N y ^ d) (i,s) q :=
        tasepPropagation_apply_stage N y (i,s) q d hd
      simp only [finiteLevelBirth,Matrix.of_apply,ite_true,one_mul,hh]
      change (∑ s : Finset.Icc (tasepCropLo y) (tasepCropHi N y),
        (finiteLevelTransfer N y ^ d) (i,s) q) = (Nat.choose (tasepCropHi N y-q.2.1).toNat d : ℝ)
      cases h : d with
      | zero =>
        have he : i = q.1 := Fin.ext (by omega)
        rw [pow_zero]
        subst i
        simp [Matrix.one_apply,Prod.ext_iff]
      | succ d' =>
        have hw (s : Finset.Icc (tasepCropLo y) (tasepCropHi N y)) :=
          tasepStrictWalk_count N y d' (i,s) q (h ▸ hd)
        simp_rw [hw]
        exact (tasepSum_crop_gt q.2.2 (fun r => (Nat.choose r d' : ℝ))).trans
          (tasepHockeyStick _ _)
    · rw [ite_eq_right hi]
      apply Finset.sum_eq_zero
      intro s _
      rw [tasepPropagation_zero_backward N y (i,s) q (lt_of_not_ge hi),mul_zero]
  · intro i' _ hi'
    apply Finset.sum_eq_zero
    intro s _
    simp [finiteLevelBirth,Ne.symm hi']
  · intro h
    exact (h (Finset.mem_univ i)).elim

private theorem tasepBirth_prop_pow {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (i : Fin m) (q : TasepFiniteSite N y) (d : ℕ) (h : i.1+d = q.1.1) :
    (finiteLevelBirth N y * finiteLevelPropagation N y) i q =
      (finiteLevelBirth N y * finiteLevelTransfer N y ^ d) i q := by
  rw [Matrix.mul_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : i = p.1
  · rw [tasepPropagation_apply_stage N y p q d (by simpa only [← hp] using h)]
  · simp [finiteLevelBirth,hp]

private theorem tasepProp_terminal_pow {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (p : TasepFiniteSite N y) (j : Fin m) (d : ℕ) (h : p.1.1+d+1 = m) :
    (finiteLevelPropagation N y * finiteLevelTerminal N y) p j =
      (finiteLevelTransfer N y ^ d * finiteLevelTerminal N y) p j := by
  rw [Matrix.mul_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q.1.1+1 = m
  · rw [tasepPropagation_apply_stage N y p q d (by omega)]
  · simp [finiteLevelTerminal,hq]

private theorem tasepOverlap_split {m : ℕ} (N : ℕ) (y : Fin m → ℤ)
    (i l j : Fin m) (hil : i ≤ l) :
    (finiteLevelBirth N y * finiteLevelPropagation N y * finiteLevelTerminal N y) i j =
      ∑ s : Finset.Icc (tasepCropLo y) (tasepCropHi N y),
        (finiteLevelBirth N y * finiteLevelPropagation N y) i (l,s) *
          (finiteLevelPropagation N y * finiteLevelTerminal N y) (l,s) j := by
  let B := finiteLevelBirth N y
  let R := finiteLevelPropagation N y
  let C := finiteLevelTerminal N y
  let T := finiteLevelTransfer N y
  let d := l.1-i.1
  let e := m-1-l.1
  have hd : i.1+d = l.1 := Nat.add_sub_of_le hil
  have he : l.1+e+1 = m := by have := l.2; dsimp [e]; omega
  have hv : (B * R * C) i j = (B * T^(d+e) * C) i j := by
    rw [Matrix.mul_apply,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.1.1+1 = m
    · rw [show (B*R) i q = (B*T^(d+e)) i q from
        tasepBirth_prop_pow N y i q (d+e) (by omega)]
    · simp [C,finiteLevelTerminal,hq]
  rw [hv,pow_add,← Matrix.mul_assoc,Matrix.mul_assoc (B*T^d),Matrix.mul_apply,
    Fintype.sum_prod_type,Finset.sum_eq_single l]
  · apply Finset.sum_congr rfl
    intro s _
    rw [← tasepBirth_prop_pow N y i (l,s) d hd, ← tasepProp_terminal_pow N y (l,s) j e he]
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro s _
    have hkn : i.1+d ≠ k.1 := fun hh => hk (Fin.ext (hh.symm.trans hd))
    rw [tasepBirth_pow_zero N y i (k,s) d hkn,zero_mul]
  · intro hl
    exact (hl (Finset.mem_univ l)).elim


private theorem tasepFlat_level_offset {m : ℕ} (_N : ℕ) (lo : ℤ) (l : Fin m) :
    tasepFlatStart m lo l - tasepCropLo (tasepFlatStart m lo) =
      2 * ((m - 1 - l.1 : ℕ) : ℤ) := by
  have hm : 0 < m := by have := l.2; omega
  rw [tasepFlat_lo hm]
  unfold tasepFlatStart flatInitial
  have h := l.2
  omega

private theorem tasepFlat_level_upper {m : ℕ} (N : ℕ) (lo : ℤ) (l : Fin m) :
    tasepCropHi N (tasepFlatStart m lo) - tasepFlatStart m lo l = (N+2*l.1 : ℕ) := by
  rw [tasepFlat_hi (by have := l.2; omega)]
  unfold tasepFlatStart flatInitial
  push_cast
  ring

private noncomputable def tasepPsi (N : ℕ) (q z : ℤ) : ℝ :=
  if 0 ≤ z-q then (tasepCoinSeries N * tasepMinus q).coeff (z-q).toNat else 0

private theorem tasepPsi_ofNat (N j : ℕ) (z : ℤ) :
    tasepPsi N j z = if 0 ≤ z then (tasepPsiPoly N j).coeff z.toNat else 0 := by
  unfold tasepPsi
  by_cases hz : 0 ≤ z
  · rw [ite_eq_left hz, ← Polynomial.coeff_coe, tasepPsiPoly_coe, tasepCoeff_shift_zero]
    by_cases hj : 0 ≤ z-(j:ℤ)
    · rw [ite_eq_left hj, ite_eq_left (by omega : j ≤ z.toNat)]
      rw [show (z-(j:ℤ)).toNat = z.toNat-j by omega]
    · rw [ite_eq_right hj, ite_eq_right (by omega : ¬j ≤ z.toNat)]
  · have h : ¬0 ≤ z-(j:ℤ) := by omega
    rw [ite_eq_right hz,ite_eq_right h]

private theorem tasepFlat_prop_terminal_psi {m : ℕ} (N : ℕ) (lo : ℤ)
    (p : TasepFiniteSite N (tasepFlatStart m lo)) (j : Fin m) :
    (finiteLevelPropagation N (tasepFlatStart m lo) * finiteLevelTerminal N (tasepFlatStart m lo)) p j =
      (-1 : ℝ)^j.1 * tasepPsi N ((j.1 : ℤ) - ((m-1-p.1.1 : ℕ):ℤ))
        (p.2.1-tasepFlatStart m lo p.1) := by
  rw [tasepFlat_prop_terminal,tasepStrictSumSeries_pow]
  let d := m-1-p.1.1
  let z := p.2.1-tasepFlatStart m lo p.1
  let w := p.2.1-tasepCropLo (tasepFlatStart m lo)
  have hw : 0 ≤ w := sub_nonneg.mpr (Finset.mem_Icc.mp p.2.2).1
  have hwz : w = z+2*(d:ℤ) := by
    have he := tasepFlat_level_offset N lo p.1
    dsimp [w,z,d] at *
    omega
  change (-1 : ℝ)^j.1 * (tasepCoinSeries N * tasepMinus j.1 * PowerSeries.X^j.1 *
      (PowerSeries.X^d * tasepMinus (-(d:ℤ)))).coeff w.toNat =
    (-1 : ℝ)^j.1 * tasepPsi N ((j.1:ℤ)-d) z
  congr 1
  rw [show tasepCoinSeries N * tasepMinus j.1 * PowerSeries.X^j.1 *
        (PowerSeries.X^d * tasepMinus (-(d:ℤ))) =
      tasepCoinSeries N * tasepMinus ((j.1:ℤ)-d) * PowerSeries.X^(j.1+d) by
    rw [sub_eq_add_neg,tasepMinus_add,pow_add]; ring, tasepCoeff_shift_zero, tasepPsi]
  have htest : j.1+d ≤ w.toNat ↔ 0 ≤ z-((j.1:ℤ)-d) := by omega
  by_cases ht : j.1+d ≤ w.toNat
  · rw [ite_eq_left ht,ite_eq_left (htest.mp ht)]
    rw [show w.toNat-(j.1+d) = (z-((j.1:ℤ)-d)).toNat by omega]
  · rw [ite_eq_right ht,ite_eq_right (fun he => ht (htest.mpr he))]

private theorem tasepSum_crop_nonnegative {L U b : ℤ} {H : ℕ}
    (hL : L ≤ b) (hU : U-b = (H:ℤ)) (f : ℤ → ℝ) (hf : ∀ z < 0, f z = 0) :
    (∑ s : Finset.Icc L U, f (s.1-b)) = ∑ z ∈ Finset.range (H+1), f (z:ℤ) := by
  classical
  calc
    _ = ∑ s : Finset.Icc L U, if b ≤ s.1 then f (s.1-b) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : b ≤ s.1
      · rw [ite_eq_left hs]
      · rw [ite_eq_right hs, hf _ (by omega)]
    _ = _ := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun s _ => (s.1-b).toNat) ?_ ?_ ?_ ?_
      · intro s hs
        have := (Finset.mem_Icc.mp s.2).2
        exact Finset.mem_range.mpr (by omega)
      · intro s hs t ht he
        have := (Finset.mem_filter.mp hs).2
        have := (Finset.mem_filter.mp ht).2
        exact Subtype.ext (by omega)
      · intro z hz
        have h := Finset.mem_range.mp hz
        refine ⟨⟨b+z,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change b ≤ b+(z:ℤ); omega⟩
        · change (b+(z:ℤ)-b).toNat = z
          omega
      · intro s hs
        have hh := (Finset.mem_filter.mp hs).2
        rw [Int.toNat_of_nonneg (sub_nonneg.mpr hh)]

private theorem tasepFlat_ortho_crop {m : ℕ} (N : ℕ) (lo : ℤ) (l : Fin m) {k j : ℕ}
    (hk : k ≤ l.1) :
    (∑ s : Finset.Icc (tasepCropLo (tasepFlatStart m lo)) (tasepCropHi N (tasepFlatStart m lo)),
      tasepPsi N k (s.1-tasepFlatStart m lo l) * tasepPhi N j (s.1-tasepFlatStart m lo l)) =
      if k = j then 1 else 0 := by
  have hl := tasepFlat_level_offset N lo l
  have hh := tasepFlat_level_upper N lo l
  have hsum := tasepSum_crop_nonnegative (by omega : tasepCropLo (tasepFlatStart m lo) ≤ tasepFlatStart m lo l)
    hh (fun z => tasepPsi N k z * tasepPhi N j z) (fun z hz => by
      rw [tasepPsi_ofNat, ite_eq_right (by omega : ¬0 ≤ z),zero_mul])
  refine hsum.trans ?_
  simp only [tasepPsi_ofNat,Int.natCast_nonneg,ite_true,Int.toNat_natCast]
  exact tasepPsiPhi_ortho N k j _ (by omega)


private noncomputable def tasepLiftW : ℝ⟦X⟧ →+* TasepTwoSeries :=
  PowerSeries.map (PowerSeries.C : ℝ →+* ℝ⟦X⟧)

private theorem tasepDoubleCoeff_product (i j : ℕ) (f g : ℝ⟦X⟧) :
    PowerSeries.coeff j (PowerSeries.coeff i (tasepLiftW f * PowerSeries.C g)) =
      f.coeff i * g.coeff j := by
  rw [PowerSeries.coeff_mul_C,tasepLiftW,PowerSeries.coeff_map,PowerSeries.coeff_C_mul]

private theorem tasepLiftW_X : tasepLiftW (PowerSeries.X : ℝ⟦X⟧) = tasepW := by
  simp [tasepLiftW,tasepW]



private theorem tasepPsiPhi_pole_coeff (N k : ℕ) (r z : ℤ) :
    (∑ j ∈ Finset.range (k+1), tasepPsi N (r+(j:ℤ)) ((k:ℤ)+r) * tasepPhi N j z) =
      (-1:ℝ)^k * (1/2:ℝ)^N *
        (tasepPlus (z+r) * (1-PowerSeries.X)^N *
          PowerSeries.rescale (1/2:ℝ) (tasepPlus (-(N:ℤ)))).coeff k := by
  let f := tasepCoinSeries N * tasepMinus r
  let g := PowerSeries.rescale (1/2:ℝ) (tasepPlus (-(N:ℤ))) * tasepPlus (z-1-(k:ℤ))
  let P := tasepLiftW f * PowerSeries.C g
  let G := tasepGeo k (-tasepW*(1-tasepW)) (tasepV*(1+tasepV))
  have hsum : (∑ j ∈ Finset.range (k+1), tasepPsi N (r+(j:ℤ)) ((k:ℤ)+r) * tasepPhi N j z) =
      tasepDiagonalCoeff k (P * (1+2*tasepV) * G) := by
    unfold G tasepGeo
    rw [Finset.mul_sum]
    unfold tasepDiagonalCoeff
    rw [map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hn : ((k:ℤ)+r)-(r+(j:ℤ)) = ((k-j:ℕ):ℤ) := by omega
    let F := tasepCoinSeries N * tasepMinus (r+(j:ℤ))
    let H := tasepPhiFactor N j * tasepPlus z
    have he : P * (1+2*tasepV) *
        ((-tasepW*(1-tasepW))^j * (tasepV*(1+tasepV))^(k-j)) =
        tasepLiftW (F * PowerSeries.X^j) *
          PowerSeries.C (PowerSeries.C ((-1:ℝ)^j) * H * PowerSeries.X^(k-j)) := by
      have hF : F = f * (1-PowerSeries.X)^j := by
        simp only [F,f,tasepMinus_add,tasepMinus_nat,mul_assoc]
      have hH : H = (1+PowerSeries.C 2*PowerSeries.X)*g*(1+PowerSeries.X)^(k-j) := by
        have hs : tasepPlus (z-1-(k:ℤ)) * tasepPlus ((k-j:ℕ):ℤ) =
            tasepPlus (-1-(j:ℤ)) * tasepPlus z := by
          rw [← tasepPlus_add,← tasepPlus_add]
          congr 1
          omega
        unfold H tasepPhiFactor g
        rw [← tasepPlus_nat]
        calc
          _ = (1+PowerSeries.C 2*PowerSeries.X) *
              PowerSeries.rescale (1/2:ℝ) (tasepPlus (-(N:ℤ))) *
                (tasepPlus (-1-(j:ℤ)) * tasepPlus z) := by ring
          _ = _ := by rw [← hs]; ring
      rw [hF,hH]
      have hsign : -tasepW = PowerSeries.C (PowerSeries.C (-1:ℝ)) * tasepW := by simp
      have hv2 : (2 : TasepTwoSeries) = PowerSeries.C (PowerSeries.C (2:ℝ)) := by
        rw [show (2:ℝ) = 1+1 by norm_num, map_add,map_one,map_add,map_one,one_add_one_eq_two]
      unfold P
      rw [hsign,hv2]
      simp only [map_mul,map_pow,map_sub,map_add,map_one,tasepLiftW_X,tasepV,mul_pow]
      ring
    rw [he,tasepDoubleCoeff_product,tasepCoeff_shift_zero,ite_eq_left hle,
      tasepCoeff_shift_zero,ite_eq_left (Nat.sub_le _ _),PowerSeries.coeff_C_mul]
    rw [tasepPsi,tasepPhi,hn,Int.toNat_natCast,ite_eq_left (Int.natCast_nonneg _),
      show k-(k-j) = j by omega]
  obtain ⟨a,b,hab⟩ := tasepGeo_discard k
  rw [hsum,mul_assoc,hab,mul_add,mul_add,← mul_assoc P a,← mul_assoc P b,
    tasepDiagonalCoeff_drop]
  have he : P * ((1+tasepV)^(k+1) * tasepGeo k (-tasepW) tasepV) =
      tasepLiftW f * PowerSeries.C (g*tasepPlus ((k+1:ℕ):ℤ)) *
        tasepGeo k (-tasepW) tasepV := by
    unfold P
    simp only [tasepPlus_nat,map_mul,map_pow,map_add,map_one,tasepV]
    ring
  rw [he]
  have hdiag := tasepDiagonalCoeff_geo k f (g*tasepPlus ((k+1:ℕ):ℤ))
  change tasepDiagonalCoeff k (tasepLiftW f * _ * _) = _ at hdiag
  rw [hdiag]
  have hflip (p q : ℝ⟦X⟧) :
      (p * PowerSeries.rescale (-1:ℝ) q).coeff k =
        (-1:ℝ)^k * (PowerSeries.rescale (-1:ℝ) p * q).coeff k := by
    have hp : PowerSeries.rescale (-1:ℝ) (PowerSeries.rescale (-1:ℝ) p) = p := by
      ext n
      simp only [PowerSeries.coeff_rescale,← mul_assoc,← mul_pow,neg_mul_neg,one_mul,one_pow]
    have h := PowerSeries.coeff_rescale (a := (-1:ℝ)) (n := k)
      (f := (PowerSeries.rescale (-1:ℝ) p * q))
    rw [map_mul,hp] at h
    exact h
  rw [hflip]
  have hf : PowerSeries.rescale (-1:ℝ) f =
      PowerSeries.C ((1/2:ℝ)^N) * (1-PowerSeries.X)^N * tasepPlus r := by
    have hq : PowerSeries.rescale (-1:ℝ) (tasepMinus r) = tasepPlus r := by
      ext n
      simp only [tasepMinus,PowerSeries.coeff_rescale,← mul_assoc,← mul_pow,neg_mul_neg,one_mul,one_pow]
    unfold f tasepCoinSeries
    rw [map_mul,map_mul,hq]
    have hc : PowerSeries.rescale (-1:ℝ) (PowerSeries.C ((1/2:ℝ)^N)) =
        PowerSeries.C ((1/2:ℝ)^N) := by
      ext n
      by_cases hn : n = 0 <;> simp [PowerSeries.coeff_rescale,PowerSeries.coeff_C,hn]
    rw [hc]
    exact congrArg (fun v => PowerSeries.C ((1/2:ℝ)^N)*v*tasepPlus r) (tasepMinus_nat N)
  rw [hf]
  have hh : (PowerSeries.C ((1/2:ℝ)^N) * (1-PowerSeries.X)^N * tasepPlus r) *
      (g*tasepPlus ((k+1:ℕ):ℤ)) =
      PowerSeries.C ((1/2:ℝ)^N) *
        (tasepPlus (z+r) * (1-PowerSeries.X)^N *
          PowerSeries.rescale (1/2:ℝ) (tasepPlus (-(N:ℤ)))) := by
    have ht : tasepPlus r * tasepPlus (z-1-(k:ℤ)) * tasepPlus ((k+1:ℕ):ℤ) =
        tasepPlus (z+r) := by
      rw [← tasepPlus_add,← tasepPlus_add]
      congr 1
      push_cast
      ring
    unfold g
    calc
      _ = PowerSeries.C ((1/2:ℝ)^N) * (1-PowerSeries.X)^N *
          PowerSeries.rescale (1/2:ℝ) (tasepPlus (-(N:ℤ))) *
          (tasepPlus r * tasepPlus (z-1-(k:ℤ)) * tasepPlus ((k+1:ℕ):ℤ)) := by ring
      _ = _ := by rw [ht]; ring
  rw [hh,PowerSeries.coeff_C_mul,← mul_assoc]

private theorem tasepExtendedPsiPhi_eq_pole (N l₁ l₂ : ℕ) (x₁ x₂ : ℤ)
    (h : x₁+2*(l₁:ℤ) ≤ l₁) :
    (∑ j ∈ Finset.range (l₂+1), tasepPsi N ((l₁:ℤ)-l₂+j) (x₁+2*l₁) *
      tasepPhi N j (x₂+2*l₂)) = bfpPoleKer N ((l₁:ℤ)+1) x₁ ((l₂:ℤ)+1) x₂ := by
  let k := x₁+(l₁:ℤ)+l₂
  have hk : k ≤ l₂ := by dsimp [k]; omega
  have hb : x₁+((l₁:ℤ)+1)+((l₂:ℤ)+1)-1 = k+1 := by dsimp [k]; ring
  have ha : x₂+((l₁:ℤ)+1)+((l₂:ℤ)+1)-2 = (x₂+2*l₂)+((l₁:ℤ)-l₂) := by ring
  unfold bfpPoleKer
  by_cases hn : 0 ≤ k
  · rw [ite_eq_left (by omega : 0 < x₁+((l₁:ℤ)+1)+((l₂:ℤ)+1)-1)]
    rw [hb,ha,add_sub_cancel_right]
    have hl : k.toNat+1 ≤ l₂+1 := by omega
    rw [← Finset.sum_subset (Finset.range_mono hl)]
    · have hh : (k.toNat:ℤ)+((l₁:ℤ)-l₂) = x₁+2*l₁ := by
        rw [Int.toNat_of_nonneg hn]
        dsimp [k]
        ring
      rw [← hh]
      exact tasepPsiPhi_pole_coeff N k.toNat _ _
    · intro j hj hnj
      have hj' : k < (j:ℤ) := by rw [Finset.mem_range] at hnj; omega
      simp only [tasepPsi,ite_eq_right (by dsimp [k] at hj'; omega :
        ¬0 ≤ (x₁+2*(l₁:ℤ))-((l₁:ℤ)-l₂+j)),zero_mul]
  · rw [ite_eq_right (by omega : ¬0 < x₁+((l₁:ℤ)+1)+((l₂:ℤ)+1)-1)]
    apply Finset.sum_eq_zero
    intro j _
    simp only [tasepPsi,ite_eq_right (by dsimp [k] at hn; omega :
      ¬0 ≤ (x₁+2*(l₁:ℤ))-((l₁:ℤ)-l₂+j)),zero_mul]


private theorem tasepBinomial_expand {I : Type*} (z : I → ℤ) (G : ℝ⟦X⟧) (d : ℕ) :
    (fun s => (G*tasepPlus (z s)).coeff d) =
      ∑ i ∈ Finset.range (d+1), (G.coeff (d-i)) • (fun s => (tasepPlus (z s)).coeff i) := by
  funext s
  rw [Finset.sum_apply,mul_comm,PowerSeries.coeff_mul]
  calc
    _ = ∑ i ∈ Finset.range (d+1), (tasepPlus (z s)).coeff i * G.coeff (d-i) :=
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (tasepPlus (z s)).coeff i * G.coeff j) d
    _ = _ := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

private theorem tasepPhiFactor_constant (N k : ℕ) :
    (tasepPhiFactor N k).coeff 0 = 1 := by
  have hh : PowerSeries.constantCoeff (PowerSeries.rescale (1/2:ℝ) (tasepPlus (-(N:ℤ)))) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_rescale,
      pow_zero,one_mul,PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [tasepPlus]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hplus := PowerSeries.binomialSeries_constantCoeff (A := ℝ) (-1-(k:ℤ))
  change PowerSeries.constantCoeff (tasepPlus (-1-(k:ℤ))) = 1 at hplus
  simp only [tasepPhiFactor,map_mul,map_add,map_one,PowerSeries.constantCoeff_X,mul_zero,add_zero,
    hh,hplus,mul_one]

private theorem tasepChoose_reflect (z : ℤ) (d : ℕ) :
    tasepIntBinom (-z) d = (-1:ℝ)^d * tasepIntBinom (z+d-1) d := by
  rw [tasepIntBinom,Ring.choose_neg,tasepIntBinom,Units.smul_def]
  norm_cast

private theorem tasepDual_annihilate {I : Type*} (N l : ℕ) (z : I → ℤ)
    (L : (I → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ d ≤ l, L (fun s => tasepPhi N d (z s)) = 0)
    (c : ℤ) (d : ℕ) (hd : d ≤ l) :
    L (fun s => (tasepPlus (c-z s)).coeff d) = 0 := by
  have he (d : ℕ) : d ≤ l → L (fun s => (tasepPlus (z s)).coeff d) = 0 := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd
      have hh := h d hd
      change L (((-1:ℝ)^d) • (fun s => (tasepPhiFactor N d*tasepPlus (z s)).coeff d)) = 0 at hh
      rw [map_smul,smul_eq_mul] at hh
      have hn : (-1:ℝ)^d ≠ 0 := pow_ne_zero _ (by norm_num)
      have hv := (mul_eq_zero.mp hh).resolve_left hn
      rw [tasepBinomial_expand,Finset.sum_range_succ,map_add,map_sum,Nat.sub_self,tasepPhiFactor_constant,one_smul] at hv
      have hzero : (∑ i ∈ Finset.range d, (PowerSeries.coeff (d-i) (tasepPhiFactor N d)) •
          L (fun s => (tasepPlus (z s)).coeff i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [ih i (Finset.mem_range.mp hi) (by have := Finset.mem_range.mp hi; omega),smul_zero]
      simp only [map_smul] at hv
      rwa [hzero,zero_add] at hv
  have hr :
      (fun s => (tasepPlus (c-z s)).coeff d) =
        ((-1:ℝ)^d) • (fun s => (tasepPlus ((d:ℤ)-1-c)*tasepPlus (z s)).coeff d) := by
    funext s
    rw [show c-z s = -(z s-c) by ring,tasepPlus_coeff,tasepChoose_reflect]
    change _ = (-1:ℝ)^d * (tasepPlus ((d:ℤ)-1-c)*tasepPlus (z s)).coeff d
    rw [← tasepPlus_add,tasepPlus_coeff]
    ring_nf
  rw [hr,map_smul,tasepBinomial_expand,map_sum]
  have hh : (∑ i ∈ Finset.range (d+1),
      L ((PowerSeries.coeff (d-i) (tasepPlus ((d:ℤ)-1-c))) • (fun s => (tasepPlus (z s)).coeff i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_smul,he i (by have := Finset.mem_range.mp hi; omega),smul_zero]
  rw [hh,smul_zero]

private theorem tasepFlat_reproduce {m : ℕ} (N : ℕ) (lo : ℤ) (i l : Fin m)
    (hi : i ≤ l) (t : Finset.Icc (tasepCropLo (tasepFlatStart m lo)) (tasepCropHi N (tasepFlatStart m lo))) :
    let y := tasepFlatStart m lo
    let B := finiteLevelBirth N y * finiteLevelPropagation N y
    (∑ s : Finset.Icc (tasepCropLo y) (tasepCropHi N y), B i (l,s) *
      ∑ k ∈ Finset.range (l.1+1), tasepPsi N k (s.1-y l) * tasepPhi N k (t.1-y l)) = B i (l,t) := by
  classical
  let y := tasepFlatStart m lo
  let U := tasepCropHi N y
  let C := Finset.Icc (tasepCropLo y) U
  let B := finiteLevelBirth N y * finiteLevelPropagation N y
  let z (s : C) := s.1-y l
  let W (s : C) := ∑ k ∈ Finset.range (l.1+1), tasepPsi N k (z s) * tasepPhi N k (z t)
  let L : (C → ℝ) →ₗ[ℝ] ℝ := (∑ s : C, W s • (LinearMap.proj s : (C → ℝ) →ₗ[ℝ] ℝ)) - LinearMap.proj t
  have hL (f : C → ℝ) : L f = (∑ s : C, W s * f s) - f t := by
    simp [L,LinearMap.sum_apply]
  have hPhi (d : ℕ) (hd : d ≤ l.1) : L (fun s => tasepPhi N d (z s)) = 0 := by
    rw [hL,sub_eq_zero]
    unfold W
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    have hsum (k : ℕ) (hk : k ∈ Finset.range (l.1+1)) :
        (∑ s : C, (tasepPsi N k (z s)*tasepPhi N k (z t))*tasepPhi N d (z s)) =
        (if k=d then 1 else 0) * tasepPhi N k (z t) := by
      have he (s : C) :
          (tasepPsi N k (z s)*tasepPhi N k (z t))*tasepPhi N d (z s) =
          (tasepPsi N k (z s)*tasepPhi N d (z s))*tasepPhi N k (z t) := by ring
      simp_rw [he]
      rw [← Finset.sum_mul]
      exact congrArg (· * tasepPhi N k (z t))
        (tasepFlat_ortho_crop N lo l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    rw [Finset.sum_congr rfl hsum]
    simp [Finset.mem_range,hd,ite_mul]
  let d := l.1-i.1
  have hd : d ≤ l.1 := Nat.sub_le _ _
  have hzero := tasepDual_annihilate N l.1 z L hPhi (U-y l) d hd
  have he (s : C) : (tasepPlus ((U-y l)-z s)).coeff d = B i (l,s) := by
    rw [tasepPlus_coeff,show U-y l-z s = U-s.1 by dsimp [z]; ring]
    have hu : 0 ≤ U-s.1 := sub_nonneg.mpr (Finset.mem_Icc.mp s.2).2
    have he := tasepBirth_prop_apply N y i (l,s)
    rw [ite_eq_left (show i.1 ≤ l.1 from hi)] at he
    have hB : B i (l,s) = ((U-s.1).toNat.choose d : ℝ) := he
    exact (by rw [tasepIntBinom,← Int.toNat_of_nonneg hu,Ring.choose_natCast]; norm_cast :
      tasepIntBinom (U-s.1) d = ((U-s.1).toNat.choose d : ℝ)).trans hB.symm
  simp_rw [he] at hzero
  rw [hL,sub_eq_zero] at hzero
  exact (Finset.sum_congr rfl (fun s _ => mul_comm _ _)).trans hzero


private theorem tasepPhi_zero (N : ℕ) (z : ℤ) : tasepPhi N 0 z = 1 := by
  rw [tasepPhi,pow_zero,one_mul,PowerSeries.coeff_zero_eq_constantCoeff_apply,map_mul]
  have h := tasepPhiFactor_constant N 0
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  simp [h,tasepPlus]

private theorem tasepFin_sum_tail (m d : ℕ) (h : d ≤ m) (f : ℕ → ℝ) :
    (∑ j : Fin m, if d ≤ j.1 then f (j.1-d) else 0) =
      ∑ j ∈ Finset.range (m-d), f j := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => j.1-d) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact Finset.mem_range.mpr (by have := j.2; omega)
  · intro i hi j hj hij
    apply Fin.ext
    have h₁ := (Finset.mem_filter.mp hi).2
    have h₂ := (Finset.mem_filter.mp hj).2
    omega
  · intro j hj
    have h' := Finset.mem_range.mp hj
    refine ⟨⟨j+d,by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp⟩, by simp⟩
  · intro _ _; rfl

private noncomputable def tasepFlat_dual {m : ℕ} (N : ℕ) (lo : ℤ) :
    Matrix (Fin m) (TasepFiniteSite N (tasepFlatStart m lo)) ℝ :=
  Matrix.of fun j q =>
    if m-1-q.1.1 ≤ j.1 then
      (-1:ℝ)^j.1 * tasepPhi N (j.1-(m-1-q.1.1)) (q.2.1-tasepFlatStart m lo q.1)
    else 0

private theorem tasepFlatOverlap_zero {m : ℕ} (N : ℕ) (lo : ℤ) (i j : Fin m)
    (h : m-1-i.1 < j.1) :
    let y := tasepFlatStart m lo
    (finiteLevelBirth N y * finiteLevelPropagation N y * finiteLevelTerminal N y) i j = 0 := by
  let y := tasepFlatStart m lo
  change (finiteLevelBirth N y * finiteLevelPropagation N y * finiteLevelTerminal N y) i j = 0
  rw [tasepOverlap_split N y i i j le_rfl]
  let k := j.1-(m-1-i.1)
  have hk : k ≤ i.1 := by have := j.2; have := i.2; dsimp [k]; omega
  have hn : k ≠ 0 := by dsimp [k]; omega
  have hcast : ((k:ℕ):ℤ) = (j.1:ℤ)-((m-1-i.1:ℕ):ℤ) := by dsimp [k]; omega
  have he (s : Finset.Icc (tasepCropLo y) (tasepCropHi N y)) :
      (finiteLevelBirth N y * finiteLevelPropagation N y) i (i,s) *
          (finiteLevelPropagation N y * finiteLevelTerminal N y) (i,s) j =
        (-1:ℝ)^j.1 * (tasepPsi N k (s.1-y i) * tasepPhi N 0 (s.1-y i)) := by
    rw [tasepFlat_prop_terminal_psi, ← hcast, tasepBirth_prop_apply]
    simp [tasepPhi_zero,y]
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hsum := tasepFlat_ortho_crop N lo i (j := 0) hk
  rw [ite_eq_right hn] at hsum
  exact mul_eq_zero_of_right _ hsum

/-- The biorthogonal polynomials solve the finite overlap system.
The birth rows reproduce polynomials of the required degree on each observation level. -/
private theorem tasepFlat_dual_solve {m : ℕ} (N : ℕ) (lo : ℤ) :
    let y := tasepFlatStart m lo
    let B := finiteLevelBirth N y * finiteLevelPropagation N y
    B * finiteLevelTerminal N y * tasepFlat_dual (m := m) N lo = B := by
  classical
  let y := tasepFlatStart m lo
  let B := finiteLevelBirth N y * finiteLevelPropagation N y
  let M := B * finiteLevelTerminal N y
  change M * tasepFlat_dual N lo = B
  ext i q
  let d := m-1-q.1.1
  have hd : m-d = q.1.1+1 := by have := q.1.2; dsimp [d]; omega
  by_cases hi : i ≤ q.1
  · rw [Matrix.mul_apply]
    have hsplit (j : Fin m) := tasepOverlap_split N y i q.1 j hi
    simp_rw [show ∀ j, M i j = _ from hsplit]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc,← Finset.mul_sum]
    have hterm (s : Finset.Icc (tasepCropLo y) (tasepCropHi N y)) :
        (∑ j : Fin m, (finiteLevelPropagation N y * finiteLevelTerminal N y) (q.1,s) j *
          tasepFlat_dual N lo j q) =
          ∑ k ∈ Finset.range (q.1.1+1), tasepPsi N k (s.1-y q.1) * tasepPhi N k (q.2.1-y q.1) := by
      have he (j : Fin m) :
          (finiteLevelPropagation N y * finiteLevelTerminal N y) (q.1,s) j *
          tasepFlat_dual N lo j q =
            if d ≤ j.1 then tasepPsi N (j.1-d : ℕ) (s.1-y q.1) *
                tasepPhi N (j.1-d) (q.2.1-y q.1) else 0 := by
        rw [tasepFlat_prop_terminal_psi,tasepFlat_dual, Matrix.of_apply]
        by_cases hj : d ≤ j.1
        · have he : ((j.1-d:ℕ):ℤ) = (j.1:ℤ)-(d:ℤ) := by omega
          change ((-1:ℝ)^j.1*tasepPsi N ((j.1:ℤ)-d) _) *
            (if d ≤ j.1 then (-1:ℝ)^j.1*tasepPhi N (j.1-d) _ else 0) = _
          rw [ite_eq_left hj,ite_eq_left hj,he]
          have hsgn : (-1:ℝ)^j.1 * (-1:ℝ)^j.1 = 1 := by rw [← mul_pow]; simp
          calc
            _ = ((-1:ℝ)^j.1 * (-1:ℝ)^j.1) *
                (tasepPsi N ((j.1:ℤ)-d) (s.1-y q.1) *
                  tasepPhi N (j.1-d) (q.2.1-y q.1)) := by ring
            _ = _ := by rw [hsgn,one_mul]
        · simp [d,hj]
      simp_rw [he]
      have hh := tasepFin_sum_tail m d (by dsimp [d]; omega)
        (fun k => tasepPsi N k (s.1-y q.1) * tasepPhi N k (q.2.1-y q.1))
      rw [hd] at hh
      exact hh
    simp_rw [hterm]
    exact tasepFlat_reproduce N lo i q.1 hi q.2
  · rw [Matrix.mul_apply,show B i q = 0 from (tasepBirth_prop_apply N y i q).trans (ite_eq_right hi)]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : d ≤ j.1
    · have h : m-1-i.1 < j.1 := by
        have := i.2
        have := q.1.2
        have hi' : q.1.1 < i.1 := lt_of_not_ge hi
        dsimp [d] at hj
        omega
      rw [show M i j = 0 from tasepFlatOverlap_zero N lo i j h,zero_mul]
    · have he : tasepFlat_dual N lo j q = 0 := by
        change (if d ≤ j.1 then _ else 0) = 0
        rw [ite_eq_right hj]
      rw [he,mul_zero]

private theorem tasepFlat_dual_eq_inv {m : ℕ} (N : ℕ) (lo : ℤ) :
    let y := tasepFlatStart m lo
    let B := finiteLevelBirth N y * finiteLevelPropagation N y
    (B * finiteLevelTerminal N y)⁻¹ * B = tasepFlat_dual (m := m) N lo := by
  let y := tasepFlatStart m lo
  let B := finiteLevelBirth N y * finiteLevelPropagation N y
  let M := B * finiteLevelTerminal N y
  have hM : IsUnit M.det := finiteLevelOverlap_isUnit N y (tasepFlatStart_strictAnti m lo)
  have h := congrArg (fun A => M⁻¹*A) (tasepFlat_dual_solve (m := m) N lo)
  change M⁻¹*(M*tasepFlat_dual N lo) = M⁻¹*B at h
  rw [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hM,Matrix.one_mul] at h
  exact h.symm


private theorem tasepFlat_free {m : ℕ} (N : ℕ) (lo : ℤ)
    (p q : TasepFiniteSite N (tasepFlatStart m lo)) :
    (1-finiteLevelPropagation N (tasepFlatStart m lo)) p q =
      -bfpFreeKer (lo+p.1.1) p.2.1 (lo+q.1.1) q.2.1 := by
  let y := tasepFlatStart m lo
  by_cases h : p.1 < q.1
  · let d := q.1.1-p.1.1-1
    have hd : p.1.1+(d+1) = q.1.1 := by
      have h' : p.1.1 < q.1.1 := h
      dsimp [d]
      omega
    have hn : p ≠ q := fun he => (ne_of_lt h) (congrArg Prod.fst he)
    rw [Matrix.sub_apply,Matrix.one_apply_ne hn,tasepPropagation_apply_stage N y p q (d+1) hd,
      tasepStrictWalk_count N y d p q hd,zero_sub]
    congr 1
    have hp : (lo+(p.1.1:ℤ)) < lo+q.1.1 := by
      have h' : p.1.1 < q.1.1 := h
      omega
    have hdiff : lo+(q.1.1:ℤ)-(lo+p.1.1)-1 = d := by
      dsimp [d]
      have h' : p.1.1 < q.1.1 := h
      omega
    unfold bfpFreeKer
    by_cases he : lo+(q.1.1:ℤ)-(lo+p.1.1) ≤ p.2.1-q.2.1
    · have hq : q.2.1 < p.2.1 := by omega
      simp only [hp,he,hq,true_and,ite_true,hdiff,Int.toNat_natCast]
    · have he' : ¬((lo+(p.1.1:ℤ)) < lo+q.1.1 ∧
          lo+(q.1.1:ℤ)-(lo+p.1.1) ≤ p.2.1-q.2.1) := fun h => he h.2
      rw [ite_eq_right he']
      by_cases hq : q.2.1 < p.2.1
      · rw [ite_eq_left hq, Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero]
      · rw [ite_eq_right hq]
  · have h' : ¬lo+(p.1.1:ℤ) < lo+q.1.1 := by
      have hh : ¬p.1.1 < q.1.1 := h
      omega
    rw [bfpFreeKer,ite_eq_right (fun hh => h' hh.1),neg_zero,Matrix.sub_apply]
    by_cases hq : q.1 < p.1
    · rw [tasepPropagation_zero_backward N y p q hq,
        Matrix.one_apply_ne (fun he => (ne_of_lt hq) (congrArg Prod.fst he).symm),sub_zero]
    · have he : p.1.1 = q.1.1 := by
        have h₁ : ¬p.1.1 < q.1.1 := h
        have h₂ : ¬q.1.1 < p.1.1 := hq
        omega
      rw [tasepPropagation_apply_stage N y p q 0 (by omega),pow_zero,sub_self]

private theorem tasepFlat_kernel_entry {m : ℕ} (N : ℕ) (lo : ℤ)
    (p q : TasepFiniteSite N (tasepFlatStart m lo))
    (hp : p.2.1+(lo+(p.1.1:ℤ))+lo-2 ≤ 0) :
    let y := tasepFlatStart m lo
    let R := finiteLevelPropagation N y
    let B := finiteLevelBirth N y
    let C := finiteLevelTerminal N y
    ((1-R+R*C*(B*R*C)⁻¹*B*R) :
      Matrix (TasepFiniteSite N y) (TasepFiniteSite N y) ℝ) p q = bfpKer N (lo+p.1.1) p.2.1 (lo+q.1.1) q.2.1 := by
  let y := tasepFlatStart m lo
  let R := finiteLevelPropagation N y
  let B := finiteLevelBirth N y
  let C := finiteLevelTerminal N y
  let M := B*R*C
  let D := tasepFlat_dual (m := m) N lo
  change ((1-R+R*C*M⁻¹*B*R) :
    Matrix (TasepFiniteSite N y) (TasepFiniteSite N y) ℝ) p q = _
  have hD : M⁻¹*(B*R) = D := tasepFlat_dual_eq_inv (m := m) N lo
  have he : R*C*M⁻¹*B*R = R*C*D := by
    rw [← hD]
    simp only [Matrix.mul_assoc]
  rw [he,Matrix.add_apply,tasepFlat_free N lo p q]
  let d := m-1-q.1.1
  have hd : m-d = q.1.1+1 := by have := q.1.2; dsimp [d]; omega
  rw [Matrix.mul_apply]
  have hx (j : Fin m) :
      (R*C) p j * D j q = if d ≤ j.1 then
        tasepPsi N ((p.1.1:ℤ)-q.1.1+(j.1-d:ℕ)) (p.2.1-y p.1) *
          tasepPhi N (j.1-d) (q.2.1-y q.1) else 0 := by
    have hR : (R*C) p j = _ := tasepFlat_prop_terminal_psi N lo p j
    rw [hR]
    change _ * (if d ≤ j.1 then (-1:ℝ)^j.1*tasepPhi N (j.1-d) _ else 0) = _
    by_cases hj : d ≤ j.1
    · rw [ite_eq_left hj,ite_eq_left hj]
      have hq : (j.1:ℤ)-((m-1-p.1.1 : ℕ):ℤ) = (p.1.1:ℤ)-q.1.1+(j.1-d:ℕ) := by
        have := p.1.2
        have := q.1.2
        dsimp [d]
        omega
      rw [hq]
      have hsgn : (-1:ℝ)^j.1 * (-1:ℝ)^j.1 = 1 := by rw [← mul_pow]; simp
      calc
        _ = ((-1:ℝ)^j.1 * (-1:ℝ)^j.1) *
            (tasepPsi N ((p.1.1:ℤ)-q.1.1+(j.1-d:ℕ)) (p.2.1-y p.1) *
              tasepPhi N (j.1-d) (q.2.1-y q.1)) := by ring
        _ = _ := by rw [hsgn,one_mul]
    · rw [ite_eq_right hj,ite_eq_right hj,mul_zero]
  simp_rw [hx]
  have htail := tasepFin_sum_tail m d (by dsimp [d]; omega)
    (fun k => tasepPsi N ((p.1.1:ℤ)-q.1.1+k) (p.2.1-y p.1) *
      tasepPhi N k (q.2.1-y q.1))
  rw [hd] at htail
  rw [htail]
  let x₁ := p.2.1+2*(lo-1)
  let x₂ := q.2.1+2*(lo-1)
  have h₁ : p.2.1-y p.1 = x₁+2*p.1.1 := by unfold x₁ y tasepFlatStart flatInitial; ring
  have h₂ : q.2.1-y q.1 = x₂+2*q.1.1 := by unfold x₂ y tasepFlatStart flatInitial; ring
  have hS : x₁+2*(p.1.1:ℤ) ≤ p.1.1 := by dsimp [x₁]; omega
  rw [h₁,h₂,tasepExtendedPsiPhi_eq_pole N p.1.1 q.1.1 x₁ x₂ hS]
  have hpole := bfpKer_shift N ((p.1.1:ℤ)+1) x₁ ((q.1.1:ℤ)+1) x₂ (lo-1)
  have hfree : bfpFreeKer (lo+p.1.1) p.2.1 (lo+q.1.1) q.2.1 =
      bfpFreeKer ((p.1.1:ℤ)+1) x₁ ((q.1.1:ℤ)+1) x₂ := by
    unfold bfpFreeKer
    have h₁ : (lo+p.1.1:ℤ) < lo+q.1.1 ↔ (p.1.1:ℤ)+1 < (q.1.1:ℤ)+1 := by omega
    have h₂ : lo+(q.1.1:ℤ)-(lo+p.1.1) = (q.1.1:ℤ)+1-((p.1.1:ℤ)+1) := by ring
    have h₃ : p.2.1-q.2.1 = x₁-x₂ := by dsimp [x₁,x₂]; ring
    apply if_congr
    · exact and_congr h₁ (by rw [h₂,h₃])
    · rw [h₂,h₃]
    · rfl
  have hs₁ : (p.1.1:ℤ)+1+(lo-1) = lo+p.1.1 := by ring
  have hs₂ : (q.1.1:ℤ)+1+(lo-1) = lo+q.1.1 := by ring
  have hs₃ : x₁-2*(lo-1) = p.2.1 := by dsimp [x₁]; ring
  have hs₄ : x₂-2*(lo-1) = q.2.1 := by dsimp [x₂]; ring
  rw [hs₁,hs₂,hs₃,hs₄] at hpole
  rw [hpole,hfree,bfpKer,sub_eq_add_neg,add_comm]


private def tasepObservationEmbedding {J : Finset ℤ} (lo : ℤ) (m : ℕ)
    (hlo : ∀ j : J, lo ≤ j.1) (hhi : ∀ j : J, j.1 < lo+(m:ℤ)) : J ↪ Fin m :=
  ⟨fun j => ⟨(j.1-lo).toNat, by have := hlo j; have := hhi j; omega⟩,
    fun i j h => Subtype.ext (by
      have hh := congrArg (fun k : Fin m => k.1) h
      change (i.1-lo).toNat = (j.1-lo).toNat at hh
      have := hlo i
      have := hlo j
      omega)⟩

private theorem tasepObservation_label {J : Finset ℤ} (lo : ℤ) (m : ℕ)
    (hlo : ∀ j : J, lo ≤ j.1) (hhi : ∀ j : J, j.1 < lo+(m:ℤ)) (j : J) :
    lo+((tasepObservationEmbedding lo m hlo hhi j).1:ℤ) = j.1 := by
  change lo+(((j.1-lo).toNat:ℕ):ℤ) = j.1
  have := hlo j
  omega

private noncomputable def tasepObservationEquiv {J : Finset ℤ} {m : ℕ} (e : J ↪ Fin m) :
    J ≃ (Finset.univ.map e) :=
  Equiv.ofBijective (fun j => ⟨e j, Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun _ _ h => e.injective (congrArg Subtype.val h), fun j => by
      obtain ⟨i,_,he⟩ := Finset.mem_map.mp j.2
      exact ⟨i,Subtype.ext he⟩⟩

private noncomputable def tasepWindowBad {J : Finset ℤ} (a : J → ℤ) (L U : ℤ) :
    Finset (J × ℤ) :=
  (Finset.univ.product (Finset.Icc L U)).filter (fun p => p.2 < a p.1)

private theorem tasepWindowBad_mem {J : Finset ℤ} (a : J → ℤ) (L U : ℤ) (p : J × ℤ) :
    p ∈ tasepWindowBad a L U ↔ L ≤ p.2 ∧ p.2 ≤ U ∧ p.2 < a p.1 := by
  simp [tasepWindowBad, and_assoc]

private theorem tasepBadSite_label_mem {m N : ℕ} {y : Fin m → ℤ}
    {J : Finset (Fin m)} {a : J → ℤ} (p : finiteBadSites N y J a) : p.1.1 ∈ J := by
  by_contra h
  have hp := (Finset.mem_filter.mp p.2).2
  simpa only [dite_eq_right h] using hp

private noncomputable def tasepBadSiteEquiv {J : Finset ℤ} {m : ℕ} (e : J ↪ Fin m)
    (a : J → ℤ) (N : ℕ) (y : Fin m → ℤ) :
    finiteBadSites N y (Finset.univ.map e) (a ∘ (tasepObservationEquiv e).symm) ≃
      tasepWindowBad a (tasepCropLo y) (tasepCropHi N y) where
  toFun p := by
    have hp := tasepBadSite_label_mem p
    have h := (Finset.mem_filter.mp p.2).2
    have hc := Finset.mem_Icc.mp p.1.2.2
    have ha : p.1.2.1 < a ((tasepObservationEquiv e).symm ⟨p.1.1,hp⟩) := by
      simpa only [dite_eq_left hp,Function.comp_apply] using h
    exact ⟨((tasepObservationEquiv e).symm ⟨p.1.1,hp⟩,p.1.2.1),
      (tasepWindowBad_mem _ _ _ _).mpr ⟨hc.1,hc.2,ha⟩⟩
  invFun p := by
    have h := (tasepWindowBad_mem _ _ _ p.1).mp p.2
    let q := tasepObservationEquiv e p.1.1
    refine ⟨(q.1,⟨p.1.2,Finset.mem_Icc.mpr ⟨h.1,h.2.1⟩⟩), ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [dite_eq_left q.2]
    change p.1.2 < a ((tasepObservationEquiv e).symm q)
    rw [show q = tasepObservationEquiv e p.1.1 from rfl,Equiv.symm_apply_apply]
    exact h.2.2
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        ((tasepObservationEquiv e).apply_symm_apply ⟨p.1.1,tasepBadSite_label_mem p⟩)
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (tasepObservationEquiv e).symm_apply_apply p.1.1
    · rfl

/-- The flat TASEP gap law at any finite set of integer labels is the counting-measure
Fredholm series of the period-two BFP kernel. The finite window can be extended
past the observed labels in both directions before evaluating the kernel. -/
theorem flatPosLaw_gap_eq_bfp_series (N : ℕ) (J : Finset ℤ) (a : J → ℤ) :
    (flatPosLaw N J).real {z | ∀ j : J, a j ≤ z j} =
      kernelFredholmSeries Measure.count (bfpCutKernel N J a) := by
  classical
  let f (j : J) := min (j.1-(tasepFrontMargin N:ℤ)) (3-a j-j.1)
  obtain ⟨lo,hlo⟩ := (Set.finite_range f).bddBelow
  obtain ⟨hi,hhi⟩ := (Set.finite_range (Subtype.val : J → ℤ)).bddAbove
  let m := (max lo hi-lo+1).toNat
  have hm : 0 < m := by dsimp [m]; have := le_max_left lo hi; omega
  have hm' : (m:ℤ) = max lo hi-lo+1 := by dsimp [m]; have := le_max_left lo hi; omega
  have hb (j : J) : lo ≤ f j := hlo (Set.mem_range_self j)
  have hfront (j : J) : lo + (tasepFrontMargin N:ℤ) ≤ j.1 := by
    have hh := (hb j).trans (min_le_left _ _)
    omega
  have hlast (j : J) : j.1 < lo+(m:ℤ) := by
    have hh := hhi (Set.mem_range_self j)
    have hm := le_max_right lo hi
    omega
  have hloc (j : J) : lo ≤ j.1 := by have := hfront j; omega
  let e := tasepObservationEmbedding lo m hloc hlast
  let J' := Finset.univ.map e
  let ej : J ≃ J' := tasepObservationEquiv e
  let a' : J' → ℤ := a ∘ ej.symm
  let y := tasepFlatStart m lo
  let L := tasepCropLo y
  let U := tasepCropHi N y
  let S := tasepWindowBad a L U
  have hlabel (j : J) : lo+((e j).1:ℤ) = j.1 := tasepObservation_label lo m hloc hlast j
  have hprobs :
      (flatPosLaw N J).real {z | ∀ j : J, a j ≤ z j} =
        (finiteSeqLaw N y).real {x | ∀ j : J', a' j ≤ x j.1} := by
    rw [flatPosLaw_eq_map_finiteSeqLaw N m J lo hfront hlast]
    simp only [measureReal_def]
    rw [Measure.map_apply]
    · apply congrArg ENNReal.toReal
      apply congrArg (finiteSeqLaw N y)
      ext x
      change (∀ j, a j ≤ x (e j)) ↔ ∀ j : J', a' j ≤ x j.1
      constructor
      · intro h j
        have hh := h (ej.symm j)
        have he : e (ej.symm j) = j.1 := congrArg Subtype.val (ej.apply_symm_apply j)
        rw [he] at hh
        exact hh
      · intro h j
        have hh := h (ej j)
        change a (ej.symm (ej j)) ≤ x (e j) at hh
        rwa [ej.symm_apply_apply] at hh
    · exact Measurable.of_discrete
    · exact MeasurableSet.of_discrete
  have hL (i j : J) : L+i.1+j.1-2 ≤ 0 := by
    have hi := hlast i
    have hj := hlast j
    change tasepCropLo (tasepFlatStart m lo)+i.1+j.1-2 ≤ 0
    rw [tasepFlat_lo hm,flatInitial]
    omega
  have hU (j : J) : a j-1 ≤ U := by
    have h := (hb j).trans (min_le_right _ _)
    have hj := hloc j
    change a j-1 ≤ tasepCropHi N (tasepFlatStart m lo)
    rw [tasepFlat_hi hm,flatInitial]
    omega
  rw [hprobs,finiteSeqLaw_gap_eq_matrix_det N y (tasepFlatStart_strictAnti m lo),
    tasepBfp_cut_finite N a L U hL hU S (tasepWindowBad_mem a L U)]
  let E : finiteBadSites N y J' a' ≃ S := tasepBadSiteEquiv e a N y
  rw [← Matrix.det_submatrix_equiv_self E]
  have hE (p : finiteBadSites N y J' a') :
      ((E p).1.1.1 : ℤ) = lo+p.1.1.1 ∧ (E p).1.2 = p.1.2.1 ∧ p.1.2.1 < a (E p).1.1 := by
    have hp : p.1.1 ∈ J' := tasepBadSite_label_mem p
    have hh := hlabel (ej.symm ⟨p.1.1,hp⟩)
    have he : e (ej.symm ⟨p.1.1,hp⟩) = p.1.1 :=
      congrArg Subtype.val (ej.apply_symm_apply ⟨p.1.1,hp⟩)
    rw [he] at hh
    have hpair : (E p).1 = (ej.symm ⟨p.1.1,hp⟩,p.1.2.1) := rfl
    rw [hpair]
    exact ⟨hh.symm,rfl,by
      have h := (Finset.mem_filter.mp p.2).2
      simpa only [dite_eq_left hp,Function.comp_apply,a'] using h⟩
  apply congrArg Matrix.det
  funext p q
  have ep := hE p
  have eq := hE q
  have hh := (hb (E p).1.1).trans (min_le_right _ _)
  have hp : p.1.2.1+(lo+(p.1.1.1:ℤ))+lo-2 ≤ 0 := by omega
  have hK := tasepFlat_kernel_entry N lo p.1 q.1 hp
  have hdiag : (1 : Matrix S S ℝ) (E p) (E q) =
      (1 : Matrix (finiteBadSites N y J' a') (finiteBadSites N y J' a') ℝ) p q := by
    simp only [Matrix.one_apply]
    exact if_congr E.injective.eq_iff rfl rfl
  change (1 : Matrix (finiteBadSites N y J' a') (finiteBadSites N y J' a') ℝ) p q -
      finiteLevelKernel N y J' a' p q =
    (1 : Matrix S S ℝ) (E p) (E q) -
      bfpKer N (E p).1.1.1 (E p).1.2 (E q).1.1.1 (E q).1.2
  rw [hdiag,ep.1,ep.2.1,eq.1,eq.2.1]
  exact congrArg ((1 : Matrix (finiteBadSites N y J' a') (finiteBadSites N y J' a') ℝ) p q - ·) hK

end AiryFdd
