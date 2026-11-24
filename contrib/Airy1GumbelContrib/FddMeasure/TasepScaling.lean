/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FddMeasure.TasepBinomial
import Airy1GumbelContrib.FddMeasure.AiryExtendedPath
import Mathlib.MeasureTheory.Function.Floor

open Filter MeasureTheory Set Function
open scoped Topology BigOperators ENNReal

namespace AiryFdd

/-- The BFP07 lattice entries are extended as constants on their cells before
applying the polynomial rank gauge. A cell is retained when its integer site
is strictly below the integer cutoff. The gauge follows the extended Airy convention. -/
noncomputable def bfpStepCutKer (N : ℕ) (I : Finset ℝ) (x : I → ℝ) :
    (I × ℝ) → (I × ℝ) → ℝ :=
  fun p q =>
    if bfpLatticeSite N p.1 p.2 < bfpCut N p.1 (x p.1) ∧
      bfpLatticeSite N q.1 q.2 < bfpCut N q.1 (x q.1) then
      airyRankGauge I p.1 p.2 / airyRankGauge I q.1 q.2 *
        (bfpScaledPole N p.1 q.1 p.2 q.2 - bfpScaledFree N p.1 q.1 p.2 q.2)
    else 0

theorem bfpLatticeSite_eq_iff {N : ℕ} (hN : 0 < N) (u s : ℝ) (j : ℤ) :
    bfpLatticeSite N u s = j ↔
      (bfpCenter N u - j) / bfpScale N ≤ s ∧
      s < (bfpCenter N u - j + 1) / bfpScale N := by
  have hσ := bfpScale_pos hN
  rw [bfpLatticeSite, Int.ceil_eq_iff, div_le_iff₀ hσ, lt_div_iff₀ hσ]
  constructor <;> intro h <;> constructor <;> linarith only [h.1,h.2]

theorem bfpLatticeSite_cut_iff {N : ℕ} (hN : 0 < N) (u x s : ℝ) :
    bfpLatticeSite N u s < bfpCut N u x ↔
      (bfpCenter N u - bfpCut N u x + 1) / bfpScale N ≤ s := by
  rw [bfpLatticeSite, ← Int.le_sub_one_iff, Int.ceil_le, div_le_iff₀ (bfpScale_pos hN)]
  push_cast
  constructor <;> intro h <;> linarith

theorem bfpLatticeCut_lower {N : ℕ} (hN : 0 < N) (u x : ℝ) :
    x < (bfpCenter N u - bfpCut N u x + 1) / bfpScale N ∧
    (bfpCenter N u - bfpCut N u x + 1) / bfpScale N ≤ x + (bfpScale N)⁻¹ := by
  have hb := bfpLatticeSite_error N u x
  have he : bfpLatticeSite N u x = bfpCut N u x := rfl
  rw [he] at hb
  have hσ := bfpScale_pos hN
  constructor
  · rw [lt_div_iff₀ hσ]
    linarith only [hb.2]
  · rw [div_le_iff₀ hσ, add_mul, inv_mul_cancel₀ hσ.ne']
    linarith only [hb.1]


private noncomputable def bfpLabelEquiv (N : ℕ) (I : Finset ℝ)
    (h : StrictMono (fun u : I => bfpLabel N u)) : I ≃ I.image (bfpLabel N) :=
  Equiv.ofBijective (fun i => ⟨bfpLabel N i, Finset.mem_image_of_mem _ i.2⟩)
    ⟨fun i j e => h.injective (congrArg Subtype.val e), fun j => by
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp j.2
      exact ⟨⟨u,hu⟩, Subtype.ext he⟩⟩

private noncomputable def bfpCellMap (N : ℕ) (I : Finset ℝ)
    (h : StrictMono (fun u : I => bfpLabel N u)) : I × ℝ → (I.image (bfpLabel N)) × ℤ :=
  fun p => (bfpLabelEquiv N I h p.1, bfpLatticeSite N p.1 p.2)

theorem measurable_bfpLatticeSite (N : ℕ) (u : ℝ) :
    Measurable (bfpLatticeSite N u) := by
  unfold bfpLatticeSite
  exact Int.measurable_ceil.comp (by fun_prop)

private theorem bfpMeasure_of_tagged {I : Finset ℝ} {X : Type*} [MeasurableSpace X]
    (f : I × ℝ → X) (h : ∀ i, Measurable (fun s => f (i,s))) : Measurable f := by
  apply measurable_from_prod_countable_right
  exact h

private theorem measurable_bfpCellMap (N : ℕ) (I : Finset ℝ)
    (h : StrictMono (fun u : I => bfpLabel N u)) : Measurable (bfpCellMap N I h) := by
  apply bfpMeasure_of_tagged
  intro i
  change Measurable (fun s : ℝ => (bfpLabelEquiv N I h i, bfpLatticeSite N i s))
  exact measurable_const.prodMk (measurable_bfpLatticeSite N i)

private theorem bfpMap_cell_measure {N : ℕ} (hN : 0 < N) (I : Finset ℝ)
    (h : StrictMono (fun u : I => bfpLabel N u)) :
    (airySiteMeasure I).map (bfpCellMap N I h) =
      ENNReal.ofReal (bfpScale N)⁻¹ • Measure.count := by
  apply Measure.ext_of_singleton
  rintro ⟨j,z⟩
  rw [Measure.map_apply (measurable_bfpCellMap N I h) (measurableSet_singleton _)]
  have he : (bfpCellMap N I h) ⁻¹' {(j,z)} =
      {(bfpLabelEquiv N I h).symm j} ×ˢ
        Set.Ico ((bfpCenter N ((bfpLabelEquiv N I h).symm j) - z) / bfpScale N)
          ((bfpCenter N ((bfpLabelEquiv N I h).symm j) - z + 1) / bfpScale N) := by
    ext ⟨i,s⟩
    simp only [mem_preimage, mem_singleton_iff, bfpCellMap, Prod.mk.injEq, mem_prod, mem_Ico]
    rw [bfpLatticeSite_eq_iff hN]
    constructor
    · rintro ⟨hi,hs⟩
      have hh := (bfpLabelEquiv N I h).symm_apply_eq.mpr hi.symm
      exact ⟨hh.symm,hh.symm ▸ hs⟩
    · rintro ⟨hi,hs⟩
      subst i
      exact ⟨Equiv.apply_symm_apply _ _,hs⟩
  rw [he, airySiteMeasure, Measure.prod_prod, Real.volume_Ico]
  simp only [Measure.count_singleton, one_mul, Measure.smul_apply, smul_eq_mul, mul_one]
  congr 1
  ring

private theorem bfpPi_cell_measure {N : ℕ} (hN : 0 < N) (I : Finset ℝ)
    (h : StrictMono (fun u : I => bfpLabel N u)) (k : ℕ) :
    (Measure.pi (fun _ : Fin k => airySiteMeasure I)).map
      (fun p : Fin k → I × ℝ => fun i => bfpCellMap N I h (p i)) =
      (ENNReal.ofReal (bfpScale N)⁻¹)^k •
        Measure.pi (fun _ : Fin k => (Measure.count : Measure ((I.image (bfpLabel N)) × ℤ))) := by
  have hσ : SigmaFinite ((ENNReal.ofReal (bfpScale N)⁻¹) •
      (Measure.count : Measure ((I.image (bfpLabel N)) × ℤ))) := by
    apply Measure.sigmaFinite_iff_measure_singleton_lt_top.mpr
    intro p
    simp
  have hm : SigmaFinite ((airySiteMeasure I).map (bfpCellMap N I h)) := by
    rw [bfpMap_cell_measure hN I h]
    exact hσ
  rw [Measure.pi_map_pi (hμ := fun _ => hm)
    (fun _ => (measurable_bfpCellMap N I h).aemeasurable)]
  simp_rw [bfpMap_cell_measure hN I h]
  apply Measure.ext_of_singleton
  intro p
  letI (i : Fin k) := hσ
  simp only [Measure.pi_singleton, Measure.smul_apply, smul_eq_mul, Measure.count_singleton,
    mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_const_one, one_pow]

private theorem bfpRankGauge_pos (I : Finset ℝ) (p : I × ℝ) :
    0 < airyRankGauge I p.1 p.2 := by unfold airyRankGauge; positivity

private noncomputable def bfpCombinedGauge (N : ℕ) (I : Finset ℝ) (p : I × ℝ) : ℝ :=
  airyRankGauge I p.1 p.2 * (2:ℝ)^(-bfpLatticeSite N p.1 p.2)

private theorem bfpStepCutKer_eq_discrete (N : ℕ) (I : Finset ℝ) (x : I → ℝ)
    (h : StrictMono (fun u : I => bfpLabel N u)) (p q : I × ℝ) :
    bfpStepCutKer N I x p q = bfpScale N *
      (bfpCombinedGauge N I p / bfpCombinedGauge N I q) *
      bfpCutKernel N _ (fun j => bfpCut N ((bfpLabelEquiv N I h).symm j)
        (x ((bfpLabelEquiv N I h).symm j))) (bfpCellMap N I h p) (bfpCellMap N I h q) := by
  simp only [bfpStepCutKer,bfpCutKernel,bfpCellMap, Equiv.symm_apply_apply]
  split_ifs
  · have he (i : I) : ((bfpLabelEquiv N I h i : I.image (bfpLabel N)) : ℤ) = bfpLabel N i := rfl
    have hz : (2:ℝ) ^ (bfpLatticeSite N q.1 q.2 - bfpLatticeSite N p.1 p.2) =
        (2:ℝ)^(-bfpLatticeSite N p.1 p.2) * (2:ℝ)^(bfpLatticeSite N q.1 q.2) := by
      rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      congr 1
      ring
    simp only [he,bfpScaledPole,bfpScaledFree,bfpKer,bfpCombinedGauge,div_eq_mul_inv,
      mul_inv_rev,← zpow_neg, hz]
    ring
  · ring

private theorem bfpScaledGauge_det {k : ℕ} (c : ℝ) (f : Fin k → ℝ) (hf : ∀ i, f i ≠ 0)
    (A : Matrix (Fin k) (Fin k) ℝ) :
    (Matrix.of (fun i j => c * (f i / f j) * A i j)).det = c^k * A.det := by
  classical
  have h : Matrix.of (fun i j => c * (f i / f j) * A i j) =
      c • (Matrix.diagonal f * A * Matrix.diagonal (fun i => (f i)⁻¹)) := by
    ext i j
    simp only [Matrix.of_apply,Matrix.smul_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,smul_eq_mul]
    ring
  rw [h, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal,Matrix.det_diagonal]
  rw [mul_right_comm (∏ i, f i),← Finset.prod_mul_distrib]
  simp [hf]

private theorem bfpStepCut_coeff {N : ℕ} (hN : 0 < N) (I : Finset ℝ) (x : I → ℝ)
    (h : StrictMono (fun u : I => bfpLabel N u)) (k : ℕ) :
    kernelFredholmCoeff (airySiteMeasure I) (bfpStepCutKer N I x) k =
      kernelFredholmCoeff Measure.count
        (bfpCutKernel N _ (fun j => bfpCut N ((bfpLabelEquiv N I h).symm j)
          (x ((bfpLabelEquiv N I h).symm j)))) k := by
  classical
  let J := I.image (bfpLabel N)
  let f := bfpCellMap N I h
  let F := bfpCutKernel N J (fun j => bfpCut N ((bfpLabelEquiv N I h).symm j)
    (x ((bfpLabelEquiv N I h).symm j)))
  let D (p : Fin k → J × ℤ) := (Matrix.of (fun i j => F (p i) (p j))).det
  have hDet (p : Fin k → I × ℝ) :
      (Matrix.of (fun i j => bfpStepCutKer N I x (p i) (p j))).det =
        bfpScale N ^ k * D (fun i => f (p i)) := by
    simp_rw [bfpStepCutKer_eq_discrete N I x h]
    exact bfpScaledGauge_det _ _ (fun i => (mul_pos (bfpRankGauge_pos I (p i)) (by positivity)).ne') _
  let μ := Measure.pi (fun _ : Fin k => airySiteMeasure I)
  let ν := Measure.pi (fun _ : Fin k => (Measure.count : Measure (J × ℤ)))
  have hf : Measurable (fun p : Fin k → I × ℝ => fun i => f (p i)) :=
    Measurable.of_eval fun i => (measurable_bfpCellMap N I h).comp (measurable_pi_apply i)
  have hmap := integral_map (μ := μ) hf.aemeasurable (measurable_of_countable D).aestronglyMeasurable
  have hInt : bfpScale N ^ k * (∫ p : Fin k → I × ℝ, D (fun i => f (p i)) ∂μ) =
      ∫ p, D p ∂ν := by
    rw [← hmap]
    dsimp only [μ, f]
    rw [bfpPi_cell_measure hN I h, integral_smul_measure, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (bfpScale_pos hN).le), smul_eq_mul, ← mul_assoc,
      ← mul_pow, mul_inv_cancel₀ (bfpScale_pos hN).ne', one_pow,one_mul]
  unfold kernelFredholmCoeff
  apply congrArg ((1 / (k.factorial : ℝ)) * ·)
  change (∫ p : Fin k → I × ℝ,
    (Matrix.of (fun i j => bfpStepCutKer N I x (p i) (p j))).det ∂μ) =
      ∫ p, D p ∂ν
  have hh : (fun p : Fin k → I × ℝ =>
      (Matrix.of (fun i j => bfpStepCutKer N I x (p i) (p j))).det) =
      (fun p : Fin k → I × ℝ => bfpScale N ^ k * D (fun i => f (p i))) := funext hDet
  rw [hh, integral_const_mul]
  exact hInt

/-- The counting-measure series equals the series of the cell kernel. Each
coordinate contributes a cell length that cancels the inverse lattice spacing. -/
theorem flatTasepCdf_eventually_eq_stepSeries (I : Finset ℝ) (x : I → ℝ) :
    (fun N : ℕ => flatTasepCdf N I x) =ᶠ[atTop]
      (fun N => kernelFredholmSeries (airySiteMeasure I) (bfpStepCutKer N I x)) := by
  filter_upwards [eventually_gt_atTop 0, bfpLabel_eventually_strictMono I] with N hN h
  rw [flatTasepCdf_eq_raw_cut hN]
  let e := bfpLabelEquiv N I h
  have he (i : I) : (e i : ℤ) = bfpLabel N i := rfl
  have he' (i : I) : e i = ⟨bfpLabel N i, Finset.mem_image_of_mem _ i.2⟩ := rfl
  let a (j : I.image (bfpLabel N)) := bfpCut N (e.symm j) (x (e.symm j))
  have hset : {y : I.image (bfpLabel N) → ℤ |
        ∀ u : I, bfpCut N u (x u) ≤ y ⟨bfpLabel N u, Finset.mem_image_of_mem _ u.2⟩} =
      {y | ∀ j : I.image (bfpLabel N), a j ≤ y j} := by
    ext y
    simp only [mem_setOf_eq]
    constructor
    · intro hy j
      have hj := hy (e.symm j)
      rw [← he', e.apply_symm_apply] at hj
      exact hj
    · intro hy i
      have hi := hy (e i)
      simp only [a, e.symm_apply_apply] at hi
      rwa [he'] at hi
  rw [hset, flatPosLaw_gap_eq_bfp_series]
  unfold kernelFredholmSeries
  simp_rw [bfpStepCut_coeff hN I x h]
  rfl


private theorem bfpPower_exp_bound (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, (1+s^2)^m*Real.exp (-a * |s|) ≤ C := by
  let M := 1+(a⁻¹)^2
  refine ⟨M^m*((2*m).factorial:ℝ)*Real.exp 1,by dsimp [M]; positivity,?_⟩
  intro s
  let y := a * |s|
  have hy : 0 ≤ y := mul_nonneg ha.le (abs_nonneg _)
  have h₁ : 1+s^2 ≤ M*(1+y)^2 := by
    have hd : s^2 = (a⁻¹)^2*y^2 := by
      dsimp [y]
      rw [mul_pow,sq_abs,← mul_assoc,← mul_pow,inv_mul_cancel₀ ha.ne',one_pow,one_mul]
    rw [hd]
    dsimp [M]
    nlinarith [mul_nonneg (sq_nonneg a⁻¹) hy,mul_nonneg (sq_nonneg a⁻¹) (sq_nonneg y)]
  calc
    _ ≤ (M*(1+y)^2)^m*Real.exp (-y) := by
      rw [show -a * |s| = -y by dsimp [y]; ring]
      gcongr
    _ = M^m*((1+y)^(2*m)*Real.exp (-y)) := by rw [mul_pow,pow_mul]; ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (add_one_pow_mul_exp_neg_le (2*m) hy)
        (show 0 ≤ M^m by dsimp [M]; positivity)
      convert h using 1 <;> ring

private theorem bfpRank_free_bound (I : Finset ℝ) {i j : I} (hij : (i:ℝ) < j) :
    ∃ C : ℝ, 0 < C ∧ ∀ s t : ℝ,
      airyRankGauge I i s / airyRankGauge I j t * Real.exp (-|s-t|) ≤
        C*(1+s^2)⁻¹ := by
  let m := 2*airyTimeRank I i+1
  let n := 2*airyTimeRank I j
  have hm : m≤n := by have := airyTimeRank_lt_of_lt I hij; dsimp [m,n]; omega
  obtain ⟨C,hC,h⟩ := bfpPower_exp_bound m (by norm_num : (0:ℝ)<1)
  refine ⟨2^m*C,by positivity,?_⟩
  intro s t
  have hbase : 1+s^2 ≤ 2*(1+t^2)*(1+(s-t)^2) := by
    nlinarith [sq_nonneg (s-2*t),mul_nonneg (sq_nonneg t) (sq_nonneg (s-t))]
  have hcomp : (1+s^2)^m ≤ 2^m*(1+t^2)^n*(1+(s-t)^2)^m := calc
    _ ≤ (2*(1+t^2)*(1+(s-t)^2))^m := by gcongr
    _ = 2^m*(1+t^2)^m*(1+(s-t)^2)^m := by rw [mul_pow,mul_pow]
    _ ≤ _ := by
      have hpow : (1+t^2)^m ≤ (1+t^2)^n :=
        pow_le_pow_right₀ (by linarith [sq_nonneg t]) hm
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  rw [← div_eq_mul_inv,le_div_iff₀ (by positivity : 0 < 1+s^2)]
  unfold airyRankGauge
  change ((1+s^2)^(2*airyTimeRank I i)/(1+t^2)^n*Real.exp (-|s-t|))*(1+s^2) ≤ _
  calc
    _ = (1+s^2)^m/(1+t^2)^n*Real.exp (-|s-t|) := by dsimp [m]; rw [pow_succ]; ring
    _ ≤ (2^m*(1+t^2)^n*(1+(s-t)^2)^m)/(1+t^2)^n*Real.exp (-|s-t|) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcomp (by positivity)) (by positivity)
    _ = 2^m*((1+(s-t)^2)^m*Real.exp (-|s-t|)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [neg_one_mul] using h (s-t)) (by positivity)

private theorem bfpRank_pole_bound (I : Finset ℝ) (i j : I) (L : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s t : ℝ, -L ≤ s →
      airyRankGauge I i s / airyRankGauge I j t * Real.exp (-a*(max s 0+max t 0)) ≤
        C*(1+s^2)⁻¹ := by
  let m := 2*airyTimeRank I i+1
  obtain ⟨C,hC,hbound⟩ := bfpPower_exp_bound m ha
  refine ⟨C*Real.exp (a*max L 0),by positivity,?_⟩
  intro s t hs
  have hAbs : |s| ≤ max s 0+max L 0 := by
    by_cases h : 0 ≤ s
    · rw [abs_of_nonneg h,max_eq_left h]
      exact le_add_of_nonneg_right (le_max_right _ _)
    · rw [abs_of_neg (lt_of_not_ge h),max_eq_right (le_of_not_ge h),zero_add]
      exact (neg_le.mpr hs).trans (le_max_left _ _)
  have h₀ : Real.exp (-a*(max s 0+max t 0)) ≤ Real.exp (a*max L 0)*Real.exp (-a * |s|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := mul_le_mul_of_nonneg_left hAbs ha.le
    linarith [mul_nonneg ha.le (le_max_right t 0)]
  have hj : 1 ≤ airyRankGauge I j t := by
    unfold airyRankGauge
    exact one_le_pow₀ (by linarith [sq_nonneg t])
  have hi := (bfpRankGauge_pos I (i,s)).le
  rw [← div_eq_mul_inv,le_div_iff₀ (by positivity : 0 < 1+s^2)]
  calc
    _ ≤ (airyRankGauge I i s*(Real.exp (a*max L 0)*Real.exp (-a * |s|)))*(1+s^2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (div_le_self hi hj) h₀ (Real.exp_pos _).le hi) (by positivity)
    _ = Real.exp (a*max L 0)*((1+s^2)^m*Real.exp (-a * |s|)) := by
      unfold airyRankGauge m
      rw [pow_succ]
      ring
    _ ≤ _ := by calc
      _ ≤ Real.exp (a*max L 0)*C := mul_le_mul_of_nonneg_left (hbound s) (by positivity)
      _ = _ := mul_comm _ _

private theorem bfpStep_block_bound (I : Finset ℝ) (x : I → ℝ) (i j : I) (L : ℝ)
    (hL : ∀ k : I, -L ≤ x k) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s t,
      |bfpStepCutKer N I x (i,s) (j,t)| ≤
        C*(Set.Ici (-L)).indicator (fun r : ℝ => (1+r^2)⁻¹) s := by
  obtain ⟨P,a,hP,ha,hpole⟩ := bfpScaledPole_tail i j L
  obtain ⟨P',hP',hpg⟩ := bfpRank_pole_bound I i j L ha
  obtain ⟨B,hB,hfree⟩ := bfpScaledFree_tail i j
  have hFg : ∃ B' : ℝ, 0 < B' ∧ ∀ᶠ N : ℕ in atTop, ∀ s t,
      airyRankGauge I i s / airyRankGauge I j t * |bfpScaledFree N i j s t| ≤
        B'*(1+s^2)⁻¹ := by
    by_cases hij : (i:ℝ)<j
    · obtain ⟨C,hC,h⟩ := bfpRank_free_bound I hij
      refine ⟨B*C,by positivity,?_⟩
      filter_upwards [hfree] with N hN s t
      have hpos : 0 ≤ airyRankGauge I i s / airyRankGauge I j t :=
        div_nonneg (bfpRankGauge_pos I (i,s)).le (bfpRankGauge_pos I (j,t)).le
      calc
        _ ≤ (airyRankGauge I i s / airyRankGauge I j t)*(B*Real.exp (-|s-t|)) :=
          mul_le_mul_of_nonneg_left (hN s t) hpos
        _ = B*(airyRankGauge I i s / airyRankGauge I j t*Real.exp (-|s-t|)) := by ring
        _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (h s t) hB.le
    · refine ⟨1,by norm_num,Eventually.of_forall ?_⟩
      intro N s t
      rw [bfpScaledFree_eq_zero_of_ge N (le_of_not_gt hij),abs_zero,mul_zero]
      positivity
  obtain ⟨H,hH,hheat⟩ := hFg
  refine ⟨P*P'+H,by positivity,?_⟩
  filter_upwards [hpole,hheat,eventually_gt_atTop 0] with N hp hh hn s t
  unfold bfpStepCutKer
  split_ifs with hc
  · have hs := (bfpLatticeCut_lower hn i (x i)).1.trans_le ((bfpLatticeSite_cut_iff hn i (x i) s).mp hc.1)
    have ht := (bfpLatticeCut_lower hn j (x j)).1.trans_le ((bfpLatticeSite_cut_iff hn j (x j) t).mp hc.2)
    have hs' := (hL i).trans hs.le
    have ht' := (hL j).trans ht.le
    have hg : 0 ≤ airyRankGauge I i s / airyRankGauge I j t :=
      div_nonneg (bfpRankGauge_pos I (i,s)).le (bfpRankGauge_pos I (j,t)).le
    rw [Set.indicator_of_mem (show s ∈ Set.Ici (-L) from hs'),abs_mul,abs_of_nonneg hg]
    have hp' : airyRankGauge I i s / airyRankGauge I j t * |bfpScaledPole N i j s t| ≤ P*P'*(1+s^2)⁻¹ := calc
      _ ≤ (airyRankGauge I i s / airyRankGauge I j t)*(P*Real.exp (-a*(max s 0+max t 0))) :=
        mul_le_mul_of_nonneg_left (by simpa only [neg_mul] using hp s t hs' ht') hg
      _ = P*(airyRankGauge I i s / airyRankGauge I j t*Real.exp (-a*(max s 0+max t 0))) := by ring
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hpg s t hs') hP.le
    exact (mul_le_mul_of_nonneg_left (abs_sub _ _) hg).trans
      (by rw [mul_add,add_mul]; exact add_le_add hp' (hh s t))
  · simp only [abs_zero]
    exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => by positivity) _)

/-- A single integrable row envelope bounds all late lattice kernels on a finite set of times. -/
theorem bfpStepCutKer_bound (I : Finset ℝ) (x : I → ℝ) :
    ∃ L C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ p q : I × ℝ, |bfpStepCutKer N I x p q| ≤
        C * (Set.Ici (-L)).indicator (fun r : ℝ => (1 + r ^ 2)⁻¹) p.2 := by
  classical
  let L := 1+∑ i : I, |x i|
  have hL (i : I) : -L ≤ x i := by
    have hl := Finset.single_le_sum (f := fun j : I => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    change -(1+∑ j : I, |x j|) ≤ x i
    linarith [neg_le_abs (x i)]
  choose C hC hB using fun i j : I => bfpStep_block_bound I x i j L hL
  let C₀ := 1+∑ i : I, ∑ j : I, C i j
  have hsum : 0 ≤ ∑ i : I, ∑ j : I, C i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hC i j).le))
  refine ⟨L,C₀,by change 0 < 1+∑ i : I, ∑ j : I, C i j; linarith,?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hB i))] with N hN p q
  have hsum₁ := Finset.single_le_sum (f := C p.1) (fun j _ => (hC p.1 j).le) (Finset.mem_univ q.1)
  have hsum₂ := Finset.single_le_sum (f := fun i => ∑ j : I, C i j)
    (fun i _ => Finset.sum_nonneg (fun j _ => (hC i j).le)) (Finset.mem_univ p.1)
  have hle : C p.1 q.1 ≤ C₀ := by
    change C p.1 q.1 ≤ 1+∑ i : I, ∑ j : I, C i j
    linarith only [hsum₁,hsum₂]
  exact (hN p.1 q.1 p.2 q.2).trans (mul_le_mul_of_nonneg_right hle
    (Set.indicator_nonneg (fun _ _ => by positivity) _))


private noncomputable def bfpRawCellEntry (N : ℕ) (I : Finset ℝ) (x : I → ℝ)
    (p q : I×ℤ) : ℝ :=
  if p.2 < bfpCut N p.1 (x p.1) ∧ q.2 < bfpCut N q.1 (x q.1) then
    (bfpScale N * (2:ℝ)^(q.2-p.2) *
      bfpPoleKer N (bfpLabel N p.1) p.2 (bfpLabel N q.1) q.2) -
    (bfpScale N * (2:ℝ)^(q.2-p.2) *
      bfpFreeKer (bfpLabel N p.1) p.2 (bfpLabel N q.1) q.2)
  else 0

private theorem bfpMeasurable_sections {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (f : α → ℝ) (S : ι → Set α) (F : ι → α → ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hF : ∀ i, Measurable (F i))
    (hcover : ∀ z, ∃ i, z ∈ S i) (he : ∀ i, Set.EqOn f (F i) (S i)) : Measurable f := by
  intro U hU
  have hpre : f ⁻¹' U = ⋃ i, S i ∩ (F i ⁻¹' U) := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := hcover z
      refine Set.mem_iUnion.mpr ⟨i, hi, ?_⟩
      change F i z ∈ U
      rw [← he i hi]
      exact hz
    · intro hz
      obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion.mp hz
      change f z ∈ U
      rw [he i hi]
      exact hzi
  rw [hpre]
  exact MeasurableSet.iUnion fun i => (hS i).inter (hF i hU)

/-- The site cell is the intersection of a time tag and a ceiling fiber. -/
private noncomputable def bfpSiteCell (N : ℕ) {I : Finset ℝ} (a : I × ℤ) : Set (I × ℝ) :=
  {a.1} ×ˢ ((bfpLatticeSite N a.1) ⁻¹' {a.2})

private theorem bfpSiteCell_measurable (N : ℕ) {I : Finset ℝ} (a : I × ℤ) :
    MeasurableSet (bfpSiteCell N a) :=
  (measurableSet_singleton a.1).prod
    ((measurable_bfpLatticeSite N a.1) (measurableSet_singleton a.2))

private theorem bfpStep_formula (N : ℕ) (I : Finset ℝ) (x : I → ℝ) (p q : I × ℝ) :
    bfpStepCutKer N I x p q =
      if bfpLatticeSite N p.1 p.2 < bfpCut N p.1 (x p.1) ∧
        bfpLatticeSite N q.1 q.2 < bfpCut N q.1 (x q.1) then
        airyRankGauge I p.1 p.2 / airyRankGauge I q.1 q.2 *
          (bfpScaledPole N p.1 q.1 p.2 q.2 - bfpScaledFree N p.1 q.1 p.2 q.2)
      else 0 := rfl

private noncomputable def bfpCellSection (N : ℕ) (I : Finset ℝ) (x : I → ℝ)
    (a b : I × ℤ) (p : (I × ℝ) × (I × ℝ)) : ℝ :=
  airyRankGauge I a.1 p.1.2 / airyRankGauge I b.1 p.2.2 * bfpRawCellEntry N I x a b

private theorem bfpCellSection_measurable (N : ℕ) (I : Finset ℝ) (x : I → ℝ)
    (a b : I × ℤ) : Measurable (bfpCellSection N I x a b) := by
  have h (i : I) : Measurable (airyRankGauge I i) := by
    change Measurable (fun s : ℝ => (1+s^2)^(2*airyTimeRank I i))
    fun_prop
  have h₁ : Measurable (fun p : (I × ℝ) × (I × ℝ) => airyRankGauge I a.1 p.1.2) :=
    (h a.1).comp ((measurable_snd : Measurable (Prod.snd : I × ℝ → ℝ)).comp measurable_fst)
  have h₂ : Measurable (fun p : (I × ℝ) × (I × ℝ) => airyRankGauge I b.1 p.2.2) :=
    (h b.1).comp ((measurable_snd : Measurable (Prod.snd : I × ℝ → ℝ)).comp measurable_snd)
  exact (h₁.div h₂).mul_const _

private theorem bfpStep_eq_cellSection (N : ℕ) (I : Finset ℝ) (x : I → ℝ)
    (a b : I × ℤ) (p : (I × ℝ) × (I × ℝ))
    (hp : p ∈ bfpSiteCell N a ×ˢ bfpSiteCell N b) :
    bfpStepCutKer N I x p.1 p.2 = bfpCellSection N I x a b p := by
  obtain ⟨⟨hi, hs⟩, ⟨hj, ht⟩⟩ := hp
  have hi' : p.1.1 = a.1 := hi
  have hj' : p.2.1 = b.1 := hj
  have hs' : bfpLatticeSite N a.1 p.1.2 = a.2 := hs
  have ht' : bfpLatticeSite N b.1 p.2.2 = b.2 := ht
  rw [bfpStep_formula]
  simp only [bfpCellSection, bfpRawCellEntry, bfpScaledPole, bfpScaledFree, hs', ht', hi', hj']
  split_ifs <;> simp only [mul_zero]

private theorem bfpStepCutKer_measurable (N : ℕ) (I : Finset ℝ) (x : I → ℝ) :
    Measurable (fun p : (I × ℝ) × (I × ℝ) => bfpStepCutKer N I x p.1 p.2) := by
  let S (ab : (I × ℤ) × (I × ℤ)) := bfpSiteCell N ab.1 ×ˢ bfpSiteCell N ab.2
  let F (ab : (I × ℤ) × (I × ℤ)) := bfpCellSection N I x ab.1 ab.2
  have hS (ab : (I × ℤ) × (I × ℤ)) : MeasurableSet (S ab) :=
    (bfpSiteCell_measurable N ab.1).prod (bfpSiteCell_measurable N ab.2)
  have hF (ab : (I × ℤ) × (I × ℤ)) : Measurable (F ab) :=
    bfpCellSection_measurable N I x ab.1 ab.2
  have hcover (p : (I × ℝ) × (I × ℝ)) : ∃ ab, p ∈ S ab :=
    ⟨((p.1.1, bfpLatticeSite N p.1.1 p.1.2), (p.2.1, bfpLatticeSite N p.2.1 p.2.2)),
      ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩
  exact bfpMeasurable_sections _ S F hS hF hcover
    (fun ab p hp => bfpStep_eq_cellSection N I x ab.1 ab.2 p hp)

private theorem bfpLatticeCut_eventually (u x s : ℝ) :
    ∀ᶠ N : ℕ in atTop, (bfpLatticeSite N u s < bfpCut N u x) ↔ x < s := by
  by_cases hs : x<s
  · filter_upwards [eventually_gt_atTop 0,bfpScale_inv_tendsto_zero.eventually_lt_const (sub_pos.mpr hs)]
        with N hn hσ
    have hσ' : (bfpScale N)⁻¹ < s-x := hσ
    have hl : (bfpCenter N u - bfpCut N u x + 1)/bfpScale N ≤ s :=
      (bfpLatticeCut_lower hn u x).2.trans (by linarith only [hσ'])
    exact ⟨fun _ => hs,fun _ => (bfpLatticeSite_cut_iff hn u x s).mpr hl⟩
  · filter_upwards [eventually_gt_atTop 0] with N hn
    have hl := (le_of_not_gt hs).trans_lt (bfpLatticeCut_lower hn u x).1
    exact ⟨fun h => (not_le_of_gt hl ((bfpLatticeSite_cut_iff hn u x s).mp h)).elim,
      fun h => (hs h).elim⟩

private theorem bfpStepCutKer_pointwise (I : Finset ℝ) (x : I → ℝ) (p q : I×ℝ) :
    Tendsto (fun N : ℕ => bfpStepCutKer N I x p q) atTop (𝓝 (airyRankCutKer I x p q)) := by
  have hcut : ∀ᶠ N : ℕ in atTop,
      (bfpLatticeSite N p.1 p.2 < bfpCut N p.1 (x p.1) ∧
       bfpLatticeSite N q.1 q.2 < bfpCut N q.1 (x q.1)) ↔
      (x p.1 < p.2 ∧ x q.1 < q.2) := by
    filter_upwards [bfpLatticeCut_eventually p.1 (x p.1) p.2,
      bfpLatticeCut_eventually q.1 (x q.1) q.2] with N hp hq
    exact and_congr hp hq
  by_cases hpq : x p.1<p.2 ∧ x q.1<q.2
  · let L := max |p.2| |q.2|
    have hL : 0 ≤ L := (abs_nonneg p.2).trans (le_max_left _ _)
    have hm : (p.2,q.2) ∈ Icc (-L) L ×ˢ Icc (-L) L := by
      exact ⟨abs_le.mp (le_max_left _ _),abs_le.mp (le_max_right _ _)⟩
    have hp := (bfpScaledPole_tendstoUniformlyOn p.1 q.1 hL).tendsto_at hm
    have hq := (bfpScaledFree_tendstoUniformlyOn p.1 q.1 hL).tendsto_at hm
    simp only [airyRankCutKer, hpq, ite_true, airyExtendedKer]
    refine ((hp.sub hq).const_mul (airyRankGauge I p.1 p.2 / airyRankGauge I q.1 q.2)).congr' ?_
    exact hcut.mono (fun N h => if_pos (h.mpr hpq) |>.symm)
  · simp only [airyRankCutKer,hpq,ite_false]
    refine tendsto_const_nhds.congr' ?_
    exact hcut.mono (fun N h => (if_neg (fun h' => hpq (h.mp h'))).symm)

/-- The rescaled flat TASEP box law converges to the rank-conjugated extended
Airy series, with the same tagged measure and strict cut as the continuum bridge. -/
theorem tendsto_flatTasepCdf_extendedSeries (I : Finset ℝ) (x : I → ℝ) :
    Tendsto (fun N : ℕ => flatTasepCdf N I x) atTop
      (𝓝 (kernelFredholmSeries (airySiteMeasure I) (airyRankCutKer I x))) := by
  obtain ⟨L,C,hC,h⟩ := bfpStepCutKer_bound I x
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp h
  let K (N : ℕ) (p q : I×ℝ) := if N₀ ≤ N then bfpStepCutKer N I x p q else 0
  let g (p : I×ℝ) := C*(1+p.2^2)⁻¹
  have hg : Integrable g (airySiteMeasure I) := (integrable_airySite_row_weight I).const_mul C
  have hg₀ (p : I×ℝ) : 0 ≤ g p := by dsimp [g]; positivity
  have hk (N : ℕ) : Measurable (fun p : (I×ℝ)×(I×ℝ) => K N p.1 p.2) := by
    by_cases hn : N₀ ≤ N
    · simpa only [K,hn,ite_true] using bfpStepCutKer_measurable N I x
    · simpa only [K,hn,ite_false] using (measurable_const : Measurable (fun _ : (I×ℝ)×(I×ℝ) => (0:ℝ)))
  have hb (N : ℕ) (p q : I×ℝ) : ‖K N p q‖ ≤ g p := by
    by_cases hn : N₀ ≤ N
    · simp only [K,hn,ite_true,Real.norm_eq_abs]
      refine (hN₀ N hn p q).trans ?_
      by_cases he : p.2 ∈ Set.Ici (-L)
      · rw [Set.indicator_of_mem he]
      · rw [Set.indicator_of_notMem he,mul_zero]
        exact hg₀ p
    · simp only [K,hn,ite_false,norm_zero]
      exact hg₀ p
  have hK : ∀ᶠ N : ℕ in atTop, K N = bfpStepCutKer N I x :=
    (eventually_ge_atTop N₀).mono (fun N h => by funext p q; exact if_pos h)
  have hpoint (p q : I×ℝ) : Tendsto (fun N => K N p q) atTop (𝓝 (airyRankCutKer I x p q)) :=
    (bfpStepCutKer_pointwise I x p q).congr'
      (hK.mono (fun N h => congrFun (congrFun h.symm p) q))
  letI : SigmaFinite (airySiteMeasure I) := by unfold airySiteMeasure; infer_instance
  have hlim := tendsto_kernelFredholmSeries_of_row_bound hk hg hg₀ hb
    (fun _ => ae_of_all _ fun p i j => hpoint (p i) (p j))
  apply hlim.congr'
  filter_upwards [hK,flatTasepCdf_eventually_eq_stepSeries I x] with N hn he
  rw [hn]
  exact he.symm

end AiryFdd
