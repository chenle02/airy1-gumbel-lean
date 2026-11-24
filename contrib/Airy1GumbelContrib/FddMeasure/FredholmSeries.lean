/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FredholmDet.DiskAgreement
import Airy1GumbelContrib.FredholmDet.Hadamard
import Airy1GumbelContrib.FredholmDet.TraceNorm
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi

open Filter MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace Topology

namespace AiryFdd

/-- The degree-`k` Fredholm coefficient of a real kernel on a measured space. -/
noncomputable def kernelFredholmCoeff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : X → X → ℝ) (k : ℕ) : ℝ :=
  (1 / (k.factorial : ℝ)) *
    ∫ x : Fin k → X, Matrix.det (fun i j => K (x i) (x j)) ∂(Measure.pi (fun _ => μ))

/-- The Fredholm series with the sign convention for the determinant of the identity minus
the kernel operator. -/
noncomputable def kernelFredholmSeries {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : X → X → ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ k * kernelFredholmCoeff μ K k

/-- A tagged kernel vanishes when either coordinate is outside its open upper half-line. -/
def cutKernelSupported (I : Finset ℝ) (x : I → ℝ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) : Prop :=
  ∀ p q, p.2 ≤ x p.1 ∨ q.2 ≤ x q.1 → K p q = 0

/-- Each active block has a continuous extension to the corresponding closed upper quadrant. -/
def cutKernelContinuous (I : Finset ℝ) (x : I → ℝ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) : Prop :=
  ∀ i j : I, ∃ F : ℝ × ℝ → ℝ,
    ContinuousOn F (Set.Ici (x i) ×ˢ Set.Ici (x j)) ∧
      ∀ s t : ℝ, x i < s → x j < t → F (s, t) = K (i, s) (j, t)

/-- A uniform integrable envelope in the row coordinate on the active half-lines. -/
def cutKernelRowEnvelope (I : Finset ℝ) (x : I → ℝ)
    (K : (I × ℝ) → (I × ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : I × ℝ, x p.1 < p.2 → x q.1 < q.2 →
    |K p q| ≤ C * (1 + p.2 ^ 2)⁻¹

/-- The factorial in the Fredholm coefficients makes the Hadamard bounds summable. -/
theorem summable_hadamard_majorant {D : ℝ} (hD : 0 ≤ D) :
    Summable (fun n : ℕ => D ^ n * (n : ℝ) ^ ((n : ℝ) / 2) / n.factorial) := by
  let B : ℝ := 4 * D ^ 2 * Real.exp 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg : Summable (fun n : ℕ => Real.exp (B / 2) * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_left _
  apply Summable.of_norm_bounded hg
  intro n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hf : 0 < (n.factorial : ℝ) := by positivity
  have hhalf : ((n : ℝ) ^ ((n : ℝ) / 2)) ^ (2 : ℕ) = (n : ℝ) ^ n := by
    rw [← Real.rpow_mul_natCast hn]
    rw [show (n : ℝ) / 2 * ((2 : ℕ) : ℝ) = n by push_cast; ring]
    exact Real.rpow_natCast _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    (D ^ n * (n : ℝ) ^ ((n : ℝ) / 2) / n.factorial) ^ (2 : ℕ)
        = (D ^ 2) ^ n * ((n : ℝ) ^ n / n.factorial) / n.factorial := by
          rw [div_pow, mul_pow, hhalf, ← pow_mul, Nat.mul_comm n 2, pow_mul]
          ring
    _ ≤ (D ^ 2) ^ n * Real.exp (n : ℝ) / n.factorial := by
          gcongr
          exact Real.pow_div_factorial_le_exp _ hn n
    _ = (B ^ n / n.factorial) * (1 / 4 : ℝ) ^ n := by
          rw [show Real.exp (n : ℝ) = Real.exp 1 ^ n by
            rw [← Real.exp_nat_mul, mul_one]]
          dsimp [B]
          rw [mul_pow, mul_pow]
          calc
            (D ^ 2) ^ n * Real.exp 1 ^ n / n.factorial
                = ((4 : ℝ) ^ n * (D ^ 2) ^ n * Real.exp 1 ^ n / n.factorial) *
                    ((4 : ℝ) ^ n)⁻¹ := by
                      field_simp
            _ = _ := by rw [one_div, inv_pow]
    _ ≤ Real.exp B * (1 / 4 : ℝ) ^ n := by
          gcongr
          exact Real.pow_div_factorial_le_exp _ hB n
    _ = (Real.exp (B / 2) * (1 / 2 : ℝ) ^ n) ^ (2 : ℕ) := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul, ← Real.exp_nat_mul]
          congr 1 <;> norm_num <;> ring

/-- The degree-zero coefficient is the determinant of the empty matrix. -/
theorem kernelFredholmCoeff_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (K : X → X → ℝ) :
    kernelFredholmCoeff μ K 0 = 1 := by
  have hdet : (fun p : Fin 0 → X => Matrix.det (fun i j => K (p i) (p j))) =
      (fun _ => (1 : ℝ)) := by
    funext p
    exact Matrix.det_isEmpty
  unfold kernelFredholmCoeff
  rw [hdet, integral_const, measureReal_def, Measure.pi_univ]
  simp

/-- On an empty site space only the degree-zero Fredholm coefficient contributes. -/
theorem kernelFredholmSeries_of_isEmpty {X : Type*} [MeasurableSpace X] [IsEmpty X]
    (μ : Measure X) [SigmaFinite μ] (K : X → X → ℝ) :
    kernelFredholmSeries μ K = 1 := by
  unfold kernelFredholmSeries
  rw [tsum_eq_single 0]
  · simp [kernelFredholmCoeff_zero]
  · intro n hn
    let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have : IsEmpty (Fin n → X) := ⟨fun p => isEmptyElim (p j)⟩
    simp [kernelFredholmCoeff, integral_of_isEmpty]

/-- Hadamard's inequality in the form used for row-dominated kernel matrices. -/
theorem norm_det_le_of_row_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : ∀ i j, ‖A i j‖ ≤ g i) :
    ‖A.det‖ ≤ (n : ℝ) ^ ((n : ℝ) / 2) * ∏ i, g i := by
  let rows (i : Fin n) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (A i)
  let basis := EuclideanSpace.basisFun (Fin n) ℝ
  have hmat : (Matrix.of fun i j : Fin n => inner ℝ (rows i) (basis j)) = A := by
    ext i j
    rw [Matrix.of_apply, EuclideanSpace.inner_basisFun_real]
  have hdet := HilbertSchmidt.Hadamard.crossGram_det_bound_fin (𝕜 := ℝ) rows basis
  rw [hmat] at hdet
  have hbasis (j : Fin n) : ‖basis j‖ = 1 := basis.orthonormal.norm_eq_one j
  simp only [hbasis, Finset.prod_const_one, mul_one] at hdet
  have hrow (i : Fin n) : ‖rows i‖ ≤ Real.sqrt (n : ℝ) * g i := by
    rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (hg i), ← Real.sqrt_mul (Nat.cast_nonneg n)]
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ ∑ _j : Fin n, g i ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ ≤ ∏ i, ‖rows i‖ := hdet
    _ ≤ ∏ i, Real.sqrt (n : ℝ) * g i :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hrow i)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n),
        show 1 / 2 * (n : ℝ) = (n : ℝ) / 2 by ring]

/-- A measurable kernel's finite determinant integrand is measurable on the product space. -/
theorem measurable_kernelFredholmIntegrand {X : Type*} [MeasurableSpace X]
    {K : X → X → ℝ} (hK : Measurable (fun p : X × X => K p.1 p.2)) (n : ℕ) :
    Measurable (fun p : Fin n → X => Matrix.det (fun i j => K (p i) (p j))) := by
  change Measurable (fun p : Fin n → X => (Matrix.of fun i j => K (p i) (p j)).det)
  simp only [Matrix.det_apply]
  apply Finset.measurable_sum _
  intro permutation _
  apply Measurable.const_smul
  apply Finset.measurable_prod _
  intro i _
  change Measurable (fun p : Fin n → X => K (p (permutation i)) (p i))
  have hpair : Measurable (fun p : Fin n → X => (p (permutation i), p i)) :=
    (measurable_pi_apply (permutation i)).prodMk (measurable_pi_apply i)
  exact hK.comp hpair

/-- For each degree, the Hadamard envelope is an integrable product of the row bounds. -/
theorem integrable_kernelFredholmIntegrand {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SigmaFinite μ] {K : X → X → ℝ} {g : X → ℝ}
    (hK : Measurable (fun p : X × X => K p.1 p.2)) (hg : Integrable g μ)
    (hg0 : ∀ p, 0 ≤ g p) (hb : ∀ p q, ‖K p q‖ ≤ g p) (n : ℕ) :
    Integrable (fun p : Fin n → X => Matrix.det (fun i j => K (p i) (p j)))
      (Measure.pi (fun _ => μ)) := by
  have hprod : Integrable (fun p : Fin n → X => ∏ i, g (p i))
      (Measure.pi (fun _ => μ)) :=
    Integrable.fintype_prod (f := fun _ : Fin n => g) (fun _ => hg)
  refine (hprod.const_mul ((n : ℝ) ^ ((n : ℝ) / 2))).mono'
    (measurable_kernelFredholmIntegrand hK n).aestronglyMeasurable ?_
  exact ae_of_all _ fun p =>
    norm_det_le_of_row_bound (fun i j => K (p i) (p j)) (fun i => g (p i))
      (fun i => hg0 (p i)) (fun i j => hb (p i) (p j))

/-- The integral Hadamard envelope bounds the norm of the normalized coefficient. -/
theorem norm_kernelFredholmCoeff_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SigmaFinite μ] {K : X → X → ℝ} {g : X → ℝ}
    (hK : Measurable (fun p : X × X => K p.1 p.2)) (hg : Integrable g μ)
    (hg0 : ∀ p, 0 ≤ g p) (hb : ∀ p q, ‖K p q‖ ≤ g p) (n : ℕ) :
    ‖kernelFredholmCoeff μ K n‖ ≤
      (∫ p, g p ∂μ) ^ n * (n : ℝ) ^ ((n : ℝ) / 2) / n.factorial := by
  let F : (Fin n → X) → ℝ := fun p => Matrix.det (fun i j => K (p i) (p j))
  let G : (Fin n → X) → ℝ := fun p => (n : ℝ) ^ ((n : ℝ) / 2) * ∏ i, g (p i)
  have hprod : Integrable (fun p : Fin n → X => ∏ i, g (p i))
      (Measure.pi (fun _ => μ)) :=
    Integrable.fintype_prod (f := fun _ : Fin n => g) (fun _ => hg)
  have hG : Integrable G (Measure.pi (fun _ => μ)) := hprod.const_mul _
  have hF := integrable_kernelFredholmIntegrand hK hg hg0 hb n
  have hbound : ‖∫ p, F p ∂(Measure.pi (fun _ => μ))‖ ≤
      ∫ p, G p ∂(Measure.pi (fun _ => μ)) :=
    (norm_integral_le_integral_norm _).trans <|
      integral_mono hF.norm hG fun p =>
        norm_det_le_of_row_bound (fun i j => K (p i) (p j)) (fun i => g (p i))
          (fun i => hg0 (p i)) (fun i j => hb (p i) (p j))
  unfold kernelFredholmCoeff
  rw [norm_mul, Real.norm_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq ?_
  dsimp [G]
  rw [integral_const_mul, integral_fintype_prod_eq_pow, Fintype.card_fin]
  ring

/-- The degree-by-degree estimates yield an absolutely summable Fredholm series. -/
theorem summable_norm_kernelFredholmCoeff {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SigmaFinite μ] {K : X → X → ℝ} {g : X → ℝ}
    (hK : Measurable (fun p : X × X => K p.1 p.2)) (hg : Integrable g μ)
    (hg0 : ∀ p, 0 ≤ g p) (hb : ∀ p q, ‖K p q‖ ≤ g p) :
    Summable (fun n => ‖kernelFredholmCoeff μ K n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_kernelFredholmCoeff_le hK hg hg0 hb)
    (summable_hadamard_majorant (integral_nonneg (μ := μ) hg0))

/-- A uniform row envelope permits passage to the limit through the integrals and the
sum over Fredholm degrees. The hypothesis on tuples includes the diagonal entries. -/
theorem tendsto_kernelFredholmSeries_of_row_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [SigmaFinite μ] {K : X → X → ℝ} {Kₙ : ℕ → X → X → ℝ}
    {g : X → ℝ}
    (hKₙ : ∀ m, Measurable (fun p : X × X => Kₙ m p.1 p.2))
    (hg : Integrable g μ) (hg0 : ∀ p, 0 ≤ g p)
    (hb : ∀ m p q, ‖Kₙ m p q‖ ≤ g p)
    (hlim : ∀ n : ℕ, ∀ᵐ p : Fin n → X ∂(Measure.pi (fun _ => μ)),
      ∀ i j, Tendsto (fun m => Kₙ m (p i) (p j)) atTop (𝓝 (K (p i) (p j)))) :
    Tendsto (fun m => kernelFredholmSeries μ (Kₙ m)) atTop (𝓝 (kernelFredholmSeries μ K)) := by
  unfold kernelFredholmSeries
  refine tendsto_tsum_of_dominated_convergence
    (summable_hadamard_majorant (integral_nonneg (μ := μ) hg0)) ?_ ?_
  · intro n
    apply Tendsto.const_mul
    unfold kernelFredholmCoeff
    apply Tendsto.const_mul
    let G : (Fin n → X) → ℝ := fun p => (n : ℝ) ^ ((n : ℝ) / 2) * ∏ i, g (p i)
    have hprod : Integrable (fun p : Fin n → X => ∏ i, g (p i))
        (Measure.pi (fun _ => μ)) :=
      Integrable.fintype_prod (f := fun _ : Fin n => g) (fun _ => hg)
    refine tendsto_integral_of_dominated_convergence G
      (fun m => (measurable_kernelFredholmIntegrand (hKₙ m) n).aestronglyMeasurable)
      (hprod.const_mul _) (fun m => ae_of_all _ fun p => ?_) ?_
    · exact norm_det_le_of_row_bound (fun i j => Kₙ m (p i) (p j)) (fun i => g (p i))
        (fun i => hg0 (p i)) (fun i j => hb m (p i) (p j))
    · filter_upwards [hlim n] with p hp
      change Tendsto (fun m => (Matrix.of fun i j => Kₙ m (p i) (p j)).det) atTop
        (𝓝 ((Matrix.of fun i j => K (p i) (p j)).det))
      simp only [Matrix.det_apply, Matrix.of_apply]
      apply tendsto_finsetSum
      intro σ _
      apply Tendsto.const_smul
      exact tendsto_finsetProd _ fun i _ => hp (σ i) i
  · exact Eventually.of_forall fun m n => by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact norm_kernelFredholmCoeff_le (hKₙ m) hg hg0 (hb m) n

/-- Injective enumerations of a prescribed finite image are equivalences with that image. -/
noncomputable def fredholmEnumerationEquiv {ι : Type*} [DecidableEq ι]
    (n : ℕ) (s : Finset ι) :
    {f : Fin n → ι // Function.Injective f ∧ Finset.univ.image f = s} ≃ (Fin n ≃ s) where
  toFun f :=
    Equiv.ofBijective (fun i => ⟨f.1 i,
      (congrArg (fun t : Finset ι => f.1 i ∈ t) f.2.2).mp
        (Finset.mem_image_of_mem f.1 (Finset.mem_univ i))⟩)
      ⟨fun _ _ h => f.2.1 (congrArg Subtype.val h), fun j => by
        have hj : (j : ι) ∈ Finset.univ.image f.1 := by
          simpa only [f.2.2] using j.property
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
        exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨fun i => (e i : ι), (fun _ _ h => e.injective (Subtype.ext h)), by
    ext j
    constructor
    · intro hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact (e i).property
    · intro hj
      exact Finset.mem_image.mpr ⟨e.symm ⟨j, hj⟩, Finset.mem_univ _,
        congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩)⟩⟩
  left_inv f := Subtype.ext rfl
  right_inv e := Equiv.ext fun _ => Subtype.ext rfl

/-- The determinant sum over ordered tuples is factorial times the sum over
principal minors. Repeated indices contribute zero. -/
theorem sum_det_over_tuples_eq_sum_principal_minors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (n : ℕ) :
    (∑ f : Fin n → ι, (M.submatrix f f).det) =
      (n.factorial : ℝ) * ∑ s ∈ (Finset.univ : Finset ι).powersetCard n,
        (M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det := by
  classical
  let good := (Finset.univ : Finset (Fin n → ι)).filter Function.Injective
  let imageOf (f : Fin n → ι) : Finset ι := Finset.univ.image f
  have hmaps : ∀ f ∈ good, imageOf f ∈ (Finset.univ : Finset ι).powersetCard n := by
    intro f hf
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
      simp [imageOf, Finset.card_image_of_injective,
        (Finset.mem_filter.mp hf).2]⟩
  have hremove : (∑ f : Fin n → ι, (M.submatrix f f).det) = ∑ f ∈ good, (M.submatrix f f).det := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hinj : Function.Injective f
    · simp [hinj]
    · rw [ite_eq_right hinj]
      unfold Function.Injective at hinj
      push Not at hinj
      obtain ⟨i, j, hij, hne⟩ := hinj
      exact Matrix.det_zero_of_row_eq hne (funext fun k => congrArg (fun t => M t (f k)) hij)
  rw [hremove, ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  let fiber := good.filter (fun f => imageOf f = s)
  have hmem (f : Fin n → ι) : f ∈ fiber ↔ Function.Injective f ∧ Finset.univ.image f = s := by
    simp [fiber, good, imageOf]
  have hcount : fiber.card = n.factorial := by
    let e : fiber ≃ (Fin n ≃ s) :=
      (Equiv.subtypeEquivRight fun f => hmem f).trans (fredholmEnumerationEquiv n s)
    let e₀ : Fin n ≃ s := Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, Fintype.card_coe, (Finset.mem_powersetCard.mp hs).2])
    rw [← Fintype.card_coe fiber, Fintype.card_congr e, Fintype.card_equiv e₀,
      Fintype.card_fin]
  change ∑ f ∈ fiber, (M.submatrix f f).det = _
  calc
    _ = ∑ _f ∈ fiber, (M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det := by
      apply Finset.sum_congr rfl
      intro f hf
      let e := fredholmEnumerationEquiv n s ⟨f, (hmem f).mp hf⟩
      let N := M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)
      have heq : M.submatrix f f = N.submatrix e e := by
        ext i j
        rfl
      rw [heq, Matrix.det_submatrix_equiv_self]
    _ = _ := by simp [hcount, nsmul_eq_mul]

/-- Taking the determinant of identity minus a matrix commutes with reindexing. -/
theorem det_one_sub_eq_of_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (M : Matrix κ κ ℝ) (N : Matrix ι ι ℝ)
    (h : M.submatrix e e = N) : (1 - N).det = (1 - M).det := by
  have he : (1 - M).submatrix e e = 1 - N := by
    rw [Matrix.submatrix_sub]
    change (1 : Matrix κ κ ℝ).submatrix e e - M.submatrix e e = _
    rw [Matrix.submatrix_one_equiv, h]
  exact (congrArg Matrix.det he).symm.trans (Matrix.det_submatrix_equiv_self e (1 - M))


/-- Compressing an operator to a finite orthonormal family gives its finite matrix determinant. -/
theorem fredholmDet_eq_det_of_orthonormalCompression
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
    [DecidableEq ι]
    (v : ι → E) (hon : Orthonormal ℝ v)
    (P A : E →L[ℝ] E) (hA : HilbertSchmidt.IsTraceClass A)
    (hP : ∀ f, P f = ∑ i, inner ℝ (v i) f • v i)
    (hfix : ∀ i, P (v i) = v i)
    (hinner : ∀ i f, inner ℝ (v i) (P f) = inner ℝ (v i) f)
    (M : Matrix ι ι ℝ) (hM : ∀ i j, inner ℝ (v i) (A (v j)) = M i j) :
    HilbertSchmidt.fredholmDet (P ∘L A ∘L P) 1 = (1 - M).det := by
  classical
  let X := P ∘L A ∘L P
  have hinj : Function.Injective v := hon.linearIndependent.injective
  obtain ⟨w, b, hsub, hb⟩ :=
    ((orthonormal_subtype_range hinj).2 hon).exists_hilbertBasis_extension
  let g : ι ↪ w :=
    ⟨fun c => ⟨v c, hsub ⟨c, rfl⟩⟩, fun _ _ h => hinj (congrArg Subtype.val h)⟩
  let cells := (Finset.univ : Finset ι).map g
  have hbg (c : ι) : b (g c) = v c := by rw [hb]; rfl
  have hvanish (j : w) (hj : j ∉ cells) : X (b j) = 0 := by
    have hzero : P (b j) = 0 := by
      rw [hP]
      apply Finset.sum_eq_zero
      intro c _
      have hc : g c ≠ j := by
        intro heq
        exact hj (Finset.mem_map.mpr ⟨c, Finset.mem_univ _, heq⟩)
      rw [← hbg, b.orthonormal.2 hc, zero_smul]
    simp only [X, ContinuousLinearMap.comp_apply, hzero, map_zero]
  have hX : HilbertSchmidt.IsTraceClass X := (hA.comp_right P).comp_left P
  let e : ι ≃ cells :=
    Equiv.ofBijective
      (fun c => ⟨g c, Finset.mem_map.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩)
      ⟨fun _ _ h => g.injective (congrArg Subtype.val h), fun j => by
        obtain ⟨c, _, hc⟩ := Finset.mem_map.mp j.property
        exact ⟨c, Subtype.ext hc⟩⟩
  have he (c : ι) : (e c : w) = g c := rfl
  have hmatrix : (HilbertSchmidt.compressMatrix b X cells).submatrix e e = M := by
    ext c d
    change inner ℝ (b (e c : w)) (X (b (e d : w))) = _
    rw [he, he, hbg, hbg]
    change inner ℝ (v c) (P (A (P (v d)))) = _
    rw [hfix, hinner, hM]
  change HilbertSchmidt.fredholmDet X 1 = _
  rw [← HilbertSchmidt.fredholmDetIn_eq_fredholmDet hX b 1,
    HilbertSchmidt.fredholmDetIn_eq_matrix_det_of_support b X cells hvanish, one_smul]
  convert (det_one_sub_eq_of_submatrix_equiv e _ _ hmatrix).symm using 2
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- Left composition of a Hilbert–Schmidt map by a uniformly bounded sequence that
converges strongly to zero tends to zero in Hilbert–Schmidt norm. -/
theorem tendsto_hsNorm_comp_of_strong_zero
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (D : ℕ → F →L[ℝ] F) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ k, ‖D k‖ ≤ C)
    (hD : ∀ v, Tendsto (fun k => D k v) atTop (𝓝 0))
    (B : E →L[ℝ] F) (hB : HilbertSchmidt.IsHilbertSchmidt B) :
    Tendsto (fun k => (HilbertSchmidt.hsENorm (D k ∘L B)).toReal) atTop (𝓝 0) := by
  let b := HilbertSchmidt.canonicalBasis ℝ E
  have hsum : Summable (fun i => C ^ 2 * ‖B (b i)‖ ^ 2) :=
    (HilbertSchmidt.summable_norm_sq_of_hs hB b).mul_left _
  have hpow : Tendsto (fun k => ∑' i, ‖D k (B (b i))‖ ^ 2) atTop (𝓝 0) := by
    have hlim (i : HilbertSchmidt.canonicalIndex ℝ E) :
        Tendsto (fun k => ‖D k (B (b i))‖ ^ 2) atTop (𝓝 0) := by
      simpa using ((hD (B (b i))).norm.pow 2)
    have hle : ∀ k i, ‖‖D k (B (b i))‖ ^ 2‖ ≤ C ^ 2 * ‖B (b i)‖ ^ 2 := by
      intro k i
      rw [Real.norm_of_nonneg (sq_nonneg _), ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (((D k).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _))) 2
    simpa only [tsum_zero] using
      tendsto_tsum_of_dominated_convergence hsum hlim (Eventually.of_forall hle)
  have hsq (k : ℕ) :
      (HilbertSchmidt.hsENorm (D k ∘L B)).toReal ^ 2 = ∑' i, ‖D k (B (b i))‖ ^ 2 := by
    have h : HilbertSchmidt.IsHilbertSchmidt (D k ∘L B) :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top enorm_ne_top hB)
        (HilbertSchmidt.hsENorm_comp_left_le (D k) B)
    rw [← ENNReal.toReal_pow, HilbertSchmidt.hsENorm_sq_eq_ofReal h b,
      ENNReal.toReal_ofReal (tsum_nonneg fun _ => sq_nonneg _)]
    rfl
  have hnorm (k : ℕ) :
      (HilbertSchmidt.hsENorm (D k ∘L B)).toReal = Real.sqrt (∑' i, ‖D k (B (b i))‖ ^ 2) := by
    rw [← hsq, Real.sqrt_sq ENNReal.toReal_nonneg]
  simp_rw [hnorm]
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hpow
  rw [Real.sqrt_zero] at h
  exact h

/-- Uniformly bounded self-adjoint compressions of a trace-class operator converge in
trace norm when the projections converge strongly to a projection supporting the operator. -/
theorem tendsto_traceNorm_compression_of_strong
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : ℕ → E →L[ℝ] E) (S A : E →L[ℝ] E)
    (hPnorm : ∀ k, ‖P k‖ ≤ 1) (hSnorm : ‖S‖ ≤ 1)
    (hPsa : ∀ k, (P k).adjoint = P k) (hSsa : S.adjoint = S)
    (hP : ∀ f, Tendsto (fun k => P k f) atTop (𝓝 (S f)))
    (hA : HilbertSchmidt.IsTraceClass A) (hs : S ∘L A ∘L S = A) :
    Tendsto (fun k => HilbertSchmidt.traceNorm (P k ∘L A ∘L P k - A)) atTop (𝓝 0) := by
  obtain ⟨B, C, hB, hC, rfl⟩ := hA
  let D (k : ℕ) := P k - S
  have hb (k : ℕ) : ‖D k‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by linarith [hPnorm k])
  have hD (f : E) : Tendsto (fun k => D k f) atTop (𝓝 0) := by
    simpa [D] using (hP f).sub (tendsto_const_nhds (x := S f))
  have hleft := tendsto_hsNorm_comp_of_strong_zero D 2 (by norm_num) hb hD B hB
  have hright : Tendsto (fun k => HilbertSchmidt.hsNorm (C ∘L D k)) atTop (𝓝 0) := by
    have heq (k : ℕ) : HilbertSchmidt.hsNorm (C ∘L D k) =
        (HilbertSchmidt.hsENorm (D k ∘L C.adjoint)).toReal := by
      unfold HilbertSchmidt.hsNorm
      rw [← HilbertSchmidt.hsENorm_adjoint_eq (C ∘L D k), ContinuousLinearMap.adjoint_comp,
        show (D k).adjoint = D k by simp [D, hPsa, hSsa]]
    simpa only [heq] using
      tendsto_hsNorm_comp_of_strong_zero D 2 (by norm_num) hb hD C.adjoint hC.adjoint'
  have hsplit (k : ℕ) : P k ∘L (B ∘L C) ∘L P k - B ∘L C =
      ((D k ∘L B) ∘L (C ∘L P k)) + ((S ∘L B) ∘L (C ∘L D k)) := by
    conv_lhs => arg 2; rw [← hs]
    simp only [D, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.comp_assoc]
    abel
  have hbounds (k : ℕ) :
      HilbertSchmidt.traceNorm (P k ∘L (B ∘L C) ∘L P k - B ∘L C) ≤
        HilbertSchmidt.hsNorm (D k ∘L B) * HilbertSchmidt.hsNorm C +
          HilbertSchmidt.hsNorm B * HilbertSchmidt.hsNorm (C ∘L D k) := by
    have hDb := hB.comp_left (D k)
    have hCp := hC.comp_right (P k)
    have hSb := hB.comp_left S
    have hCd := hC.comp_right (D k)
    have hCbound : HilbertSchmidt.hsNorm (C ∘L P k) ≤ HilbertSchmidt.hsNorm C := by
      unfold HilbertSchmidt.hsNorm
      refine (ENNReal.toReal_mono (ENNReal.mul_ne_top hC enorm_ne_top)
        (HilbertSchmidt.hsENorm_comp_right_le C (P k))).trans ?_
      rw [ENNReal.toReal_mul, toReal_enorm]
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hPnorm k)
    have hBbound : HilbertSchmidt.hsNorm (S ∘L B) ≤ HilbertSchmidt.hsNorm B := by
      unfold HilbertSchmidt.hsNorm
      refine (ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top hB)
        (HilbertSchmidt.hsENorm_comp_left_le S B)).trans ?_
      rw [ENNReal.toReal_mul, toReal_enorm]
      exact mul_le_of_le_one_left ENNReal.toReal_nonneg hSnorm
    rw [hsplit]
    refine (HilbertSchmidt.traceNorm_add_le
      (HilbertSchmidt.IsTraceClass.traceENorm_ne_top (hDb.isTraceClass_comp hCp))
      (HilbertSchmidt.IsTraceClass.traceENorm_ne_top (hSb.isTraceClass_comp hCd))).trans ?_
    refine add_le_add ((HilbertSchmidt.traceNorm_comp_le hDb hCp).trans ?_)
      ((HilbertSchmidt.traceNorm_comp_le hSb hCd).trans ?_)
    · exact mul_le_mul_of_nonneg_left hCbound ENNReal.toReal_nonneg
    · exact mul_le_mul_of_nonneg_right hBbound ENNReal.toReal_nonneg
  refine squeeze_zero (fun _ => HilbertSchmidt.traceNorm_nonneg _) hbounds ?_
  simpa only [HilbertSchmidt.hsNorm, zero_mul, mul_zero, zero_add] using
    ((hleft.mul_const (HilbertSchmidt.hsNorm C)).add
      (hright.const_mul (HilbertSchmidt.hsNorm B)))

end AiryFdd
