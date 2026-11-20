/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FredholmDet.EntireDet
import Airy1GumbelContrib.FredholmDet.TraceNorm

/-! # Trace-norm bounds and continuity of the entire determinant

For the entire determinant `fredholmDetIn b A z = det_b(1 − zA)` of `FredholmDet/EntireDet.lean`
and the trace norm `traceNorm A = ‖A‖₁` of `FredholmDet/TraceNorm.lean` we prove, for every
Hilbert basis `b` (arbitrary index type) and every operator of **finite trace norm**
(`traceENorm A ≠ ⊤`; contrib's `IsTraceClass` implies this):

* `norm_fredholmDetIn_le_exp_traceNorm`: `|det(1 − zA)| ≤ exp(|z| ‖A‖₁)` (Simon, *Trace
  Ideals*, 2nd ed., Lemma 3.3 / Thm 3.4(a), sharp constant);
* `norm_fredholmDetIn_add_sub_le` (perturbation form):
  `|det(1 − (A + D)) − det(1 − A)| ≤ 2 ‖D‖₁ exp(2‖A‖₁ + 2‖D‖₁)`;
* `norm_fredholmDetIn_sub_le` (**Lipschitz bound**, symmetric form):
  `|det(1 − Q₁) − det(1 − Q₂)| ≤ 2 ‖Q₁ − Q₂‖₁ exp(2(‖Q₁‖₁ + ‖Q₂‖₁))`, and its coupling
  version `norm_fredholmDetIn_sub_le_coupling`;
* `tendsto_fredholmDet_of_traceNorm`: continuity of `fredholmDet · z` in trace norm;
* `tendsto_fredholmDet_comp`: if `Bₙ → B`, `Cₙ → C` in Hilbert–Schmidt norm then
  `det(1 − z BₙCₙ) → det(1 − z BC)`.

## Constants compared with Simon

Simon's Thm 3.4 has `‖Q₁ − Q₂‖₁ exp(‖Q₁‖₁ + ‖Q₂‖₁ + 1)`.  His proof is complex-analytic
(Cauchy estimate for `z ↦ det(1 + M + zN)`), which is unavailable over a *real* Hilbert space
— and the QR operators of this project live on `Lp ℝ 2` — without complexifying `E`.  The
proof here is real-variable and works for every `RCLike 𝕜`, at the price of the constants
`2, 2` in place of `1, 1` (+1).  The two bounds are incomparable (ours is better for small
norms); either gives Lipschitz continuity on trace-norm balls, which is all that is used here.

## Proof (real-variable)

Factor `A = B₁C₁` through `F₁` and `D = B₂C₂` through `F₂` with AM–GM costs `< a`, `< d`.
In `G = WithLp 2 (F₁ × F₂)` put `uᵢ = (B₁† bᵢ, t⁻¹ B₂† bᵢ)`, `vⱼ = (C₁ bⱼ, 0)`,
`wⱼ = (0, t C₂ bⱼ)` (`t² = d/a`).  Then `⟪bᵢ, A bⱼ⟫ = ⟪uᵢ, vⱼ⟫` and
`⟪bᵢ, (A + D) bⱼ⟫ = ⟪uᵢ, vⱼ + wⱼ⟫`.  Column-multilinearity of the determinant
(`AlternatingMap.map_add_univ`) plus Hadamard's inequality for every mixed cross-Gram matrix
give `|minor_s(A + D) − minor_s(A)| ≤ ∏_s (xᵢ + yᵢ) − ∏_s xᵢ` with `xᵢ = ‖uᵢ‖‖vᵢ‖`,
`yᵢ = ‖uᵢ‖‖wᵢ‖`; summing over finite `s` gives `≤ (∑ y) exp(∑ x + ∑ y)`, and AM–GM with
the choice of `t` gives `∑ x ≤ 2a`, `∑ y ≤ 2d`.  The symmetric form applies this twice
around the midpoint `M = (Q₁ + Q₂)/2`, `N = (Q₁ − Q₂)/2`.
-/

open Filter Topology
open scoped ENNReal NNReal InnerProduct InnerProductSpace
open scoped Classical

universe u

namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]

section Gram

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] {ι : Type*}

/-- Hadamard's bound for a cross-Gram principal block: `|det [⟪uᵢ, vⱼ⟫]_{s}| ≤ ∏_s ‖uᵢ‖‖vᵢ‖`. -/
theorem norm_det_gram_le (u v : ι → G) (s : Finset ι) :
    ‖(Matrix.of fun i j : s => ⟪u i, v j⟫_𝕜).det‖ ≤ ∏ i ∈ s, (‖u i‖ * ‖v i‖) := by
  rw [Finset.prod_mul_distrib, ← Finset.prod_coe_sort s (fun i => ‖u i‖),
    ← Finset.prod_coe_sort s (fun i => ‖v i‖)]
  exact Hadamard.crossGram_det_bound (fun i : s => u i) (fun i : s => v i)

/-- Column-multilinear expansion of a cross-Gram determinant with columns `vⱼ + wⱼ`. -/
theorem det_gram_add_eq_sum (u v w : ι → G) (s : Finset ι) :
    (Matrix.of fun i j : s => ⟪u i, v j + w j⟫_𝕜).det =
      ∑ T : Finset s, (Matrix.of fun i j : s =>
        ⟪u i, T.piecewise (fun j : s => v j) (fun j : s => w j) j⟫_𝕜).det := by
  rw [← Matrix.det_transpose]
  calc (Matrix.transpose (Matrix.of fun i j : s => ⟪u i, v j + w j⟫_𝕜)).det
      = Matrix.detRowAlternating (((fun (j : s) (i : s) => ⟪u i, v j⟫_𝕜) +
          (fun (j : s) (i : s) => ⟪u i, w j⟫_𝕜)) : s → s → 𝕜) := by
        show Matrix.detRowAlternating _ = _
        congr 1
        ext j i
        simp [Matrix.transpose_apply, inner_add_right]
    _ = ∑ T : Finset s, Matrix.detRowAlternating
          (T.piecewise (fun (j : s) (i : s) => ⟪u i, v j⟫_𝕜)
            (fun (j : s) (i : s) => ⟪u i, w j⟫_𝕜)) :=
        AlternatingMap.map_add_univ _ _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun T _ => ?_
        conv_rhs => rw [← Matrix.det_transpose]
        show _ = Matrix.detRowAlternating _
        congr 1
        ext j i
        by_cases hj : j ∈ T <;> simp [hj, Matrix.transpose_apply]

/-- **Difference of two cross-Gram determinants**:
`|det[⟪uᵢ, vⱼ + wⱼ⟫] − det[⟪uᵢ, vⱼ⟫]| ≤ ∏ (xᵢ + yᵢ) − ∏ xᵢ`, `xᵢ = ‖uᵢ‖‖vᵢ‖`,
`yᵢ = ‖uᵢ‖‖wᵢ‖`. -/
theorem norm_det_gram_add_sub_le (u v w : ι → G) (s : Finset ι) :
    ‖(Matrix.of fun i j : s => ⟪u i, v j + w j⟫_𝕜).det -
        (Matrix.of fun i j : s => ⟪u i, v j⟫_𝕜).det‖ ≤
      ∏ i ∈ s, (‖u i‖ * ‖v i‖ + ‖u i‖ * ‖w i‖) - ∏ i ∈ s, (‖u i‖ * ‖v i‖) := by
  set D : Finset s → 𝕜 := fun T => (Matrix.of fun i j : s =>
    ⟪u i, T.piecewise (fun j : s => v j) (fun j : s => w j) j⟫_𝕜).det with hDdef
  set a : s → ℝ := fun j => ‖u j‖ * ‖v j‖ with ha
  set c : s → ℝ := fun j => ‖u j‖ * ‖w j‖ with hc
  have hD : ∀ T, ‖D T‖ ≤ ∏ j, T.piecewise a c j := by
    intro T
    refine (Hadamard.crossGram_det_bound (fun i : s => u i)
      (fun j : s => T.piecewise (fun j : s => v j) (fun j : s => w j) j)).trans (le_of_eq ?_)
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j ∈ T <;> simp [hj, a, c]
  have hDuniv : D Finset.univ = (Matrix.of fun i j : s => ⟪u i, v j⟫_𝕜).det := by
    simp only [hDdef, Finset.piecewise_univ]
  have hsum : ∑ T : Finset s, ∏ j, T.piecewise a c j = ∏ j, (a j + c j) := by
    rw [Finset.prod_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_piecewise, Finset.univ_inter]
  rw [det_gram_add_eq_sum, ← hDuniv, ← Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  calc ‖∑ T ∈ Finset.univ.erase Finset.univ, D T‖
      ≤ ∑ T ∈ Finset.univ.erase Finset.univ, ‖D T‖ := norm_sum_le _ _
    _ ≤ ∑ T ∈ Finset.univ.erase Finset.univ, ∏ j, T.piecewise a c j :=
        Finset.sum_le_sum fun T _ => hD T
    _ = ∑ T : Finset s, ∏ j, T.piecewise a c j - ∏ j, (Finset.univ : Finset s).piecewise a c j :=
        Finset.sum_erase_eq_sub (Finset.mem_univ _)
    _ = ∏ j, (a j + c j) - ∏ j, a j := by rw [hsum, Finset.piecewise_univ]
    _ = _ := by
        rw [Finset.prod_coe_sort s (fun i => ‖u i‖ * ‖v i‖ + ‖u i‖ * ‖w i‖),
          Finset.prod_coe_sort s (fun i => ‖u i‖ * ‖v i‖)]

end Gram

/-- A finite product inequality: `∏ (1 + x + y) − ∏ (1 + x) ≤ (∑ y) ∏ (1 + x + y)`. -/
theorem prod_one_add_add_sub_le {ι : Type*} (t : Finset ι) {x y : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    ∏ i ∈ t, (1 + (x i + y i)) - ∏ i ∈ t, (1 + x i) ≤
      (∑ i ∈ t, y i) * ∏ i ∈ t, (1 + (x i + y i)) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert k t hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.sum_insert hk]
    have hP : 0 ≤ ∏ i ∈ t, (1 + (x i + y i)) :=
      Finset.prod_nonneg fun i _ => by linarith [hx i, hy i]
    have hS : 0 ≤ ∑ i ∈ t, y i := Finset.sum_nonneg fun i _ => hy i
    have hxk := hx k
    have hyk := hy k
    set P := ∏ i ∈ t, (1 + (x i + y i))
    set Q := ∏ i ∈ t, (1 + x i)
    set S := ∑ i ∈ t, y i
    have h1 : (1 + x k) * (P - Q) ≤ (1 + x k) * (S * P) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    nlinarith [mul_nonneg hyk hP, mul_nonneg (mul_nonneg hyk hxk) hP,
      mul_nonneg (mul_nonneg hyk hyk) hP, mul_nonneg (mul_nonneg hS hyk) hP,
      mul_nonneg hS hP]

section Series

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] {ι : Type*}

omit [CompleteSpace E] in
/-- A Gram representation of the matrix elements identifies every principal minor. -/
theorem detMinor_eq_gram (b : HilbertBasis ι 𝕜 E) {A : E →L[𝕜] E} {u v : ι → G}
    (h : ∀ i j, ⟪b i, A (b j)⟫_𝕜 = ⟪u i, v j⟫_𝕜) (s : Finset ι) :
    detMinor b A s = (Matrix.of fun i j : s => ⟪u i, v j⟫_𝕜).det := by
  unfold detMinor
  congr 1
  ext i j
  simp only [Matrix.of_apply, h]

omit [CompleteSpace E] in
/-- **Growth bound from a Gram representation**: `|det_b(1 − zA)| ≤ exp(|z| ∑ᵢ ‖uᵢ‖‖vᵢ‖)`. -/
theorem norm_fredholmDetIn_le_of_gram (b : HilbertBasis ι 𝕜 E) {A : E →L[𝕜] E}
    {u v : ι → G} (h : ∀ i j, ⟪b i, A (b j)⟫_𝕜 = ⟪u i, v j⟫_𝕜)
    (hx : Summable fun i => ‖u i‖ * ‖v i‖) (z : 𝕜) :
    ‖fredholmDetIn b A z‖ ≤ Real.exp (‖z‖ * ∑' i, ‖u i‖ * ‖v i‖) := by
  set w : ι → ℝ := fun i => ‖u i‖ * ‖v i‖
  have hw0 : ∀ i, 0 ≤ w i := fun i => by positivity
  have hw : ∀ s : Finset ι, ‖detMinor b A s‖ ≤ ∏ i ∈ s, w i := fun s => by
    rw [detMinor_eq_gram b h]; exact norm_det_gram_le u v s
  have hmaj := Hadamard.summable_prod_finset (fun i => mul_nonneg (norm_nonneg z) (hw0 i))
    (hx.mul_left ‖z‖)
  have hsum : Summable fun s : Finset ι => ‖(-z) ^ s.card * detMinor b A s‖ :=
    hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_fredholmDetIn_term_le b hw z)
  calc ‖fredholmDetIn b A z‖
      ≤ ∑' s : Finset ι, ‖(-z) ^ s.card * detMinor b A s‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' s : Finset ι, ∏ i ∈ s, (‖z‖ * w i) :=
        Summable.tsum_le_tsum (norm_fredholmDetIn_term_le b hw z) hsum hmaj
    _ ≤ Real.exp (∑' i, ‖z‖ * w i) :=
        Real.tsum_le_of_sum_le (fun s => Finset.prod_nonneg fun i _ =>
          mul_nonneg (norm_nonneg z) (hw0 i))
          (Hadamard.sum_prod_finset_le_exp (fun i => mul_nonneg (norm_nonneg z) (hw0 i))
            (hx.mul_left ‖z‖))
    _ = Real.exp (‖z‖ * ∑' i, w i) := by rw [tsum_mul_left]

omit [CompleteSpace E] in
/-- **Perturbation bound from Gram representations**: if `⟪bᵢ, A bⱼ⟫ = ⟪uᵢ, vⱼ⟫` and
`⟪bᵢ, A' bⱼ⟫ = ⟪uᵢ, vⱼ + wⱼ⟫`, then
`|det_b(1 − A') − det_b(1 − A)| ≤ (∑ y) exp(∑ x + ∑ y)`, `xᵢ = ‖uᵢ‖‖vᵢ‖`, `yᵢ = ‖uᵢ‖‖wᵢ‖`. -/
theorem norm_fredholmDetIn_sub_le_of_gram (b : HilbertBasis ι 𝕜 E) {A A' : E →L[𝕜] E}
    {u v w : ι → G} (hA : ∀ i j, ⟪b i, A (b j)⟫_𝕜 = ⟪u i, v j⟫_𝕜)
    (hA' : ∀ i j, ⟪b i, A' (b j)⟫_𝕜 = ⟪u i, v j + w j⟫_𝕜)
    (hx : Summable fun i => ‖u i‖ * ‖v i‖) (hy : Summable fun i => ‖u i‖ * ‖w i‖) :
    ‖fredholmDetIn b A' 1 - fredholmDetIn b A 1‖ ≤
      (∑' i, ‖u i‖ * ‖w i‖) * Real.exp ((∑' i, ‖u i‖ * ‖v i‖) + ∑' i, ‖u i‖ * ‖w i‖) := by
  set x : ι → ℝ := fun i => ‖u i‖ * ‖v i‖ with hxdef
  set y : ι → ℝ := fun i => ‖u i‖ * ‖w i‖ with hydef
  have hx0 : ∀ i, 0 ≤ x i := fun i => by positivity
  have hy0 : ∀ i, 0 ≤ y i := fun i => by positivity
  have hxy0 : ∀ i, 0 ≤ x i + y i := fun i => add_nonneg (hx0 i) (hy0 i)
  set g : Finset ι → ℝ := fun s => ∏ i ∈ s, (x i + y i) - ∏ i ∈ s, x i with hgdef
  have hg0 : ∀ s, 0 ≤ g s := fun s => sub_nonneg.2
    (Finset.prod_le_prod₀ (fun i _ => hx0 i) (fun i _ => le_add_of_nonneg_right (hy0 i)))
  set f : Finset ι → 𝕜 := fun s => (-1 : 𝕜) ^ s.card * detMinor b A s with hfdef
  set f' : Finset ι → 𝕜 := fun s => (-1 : 𝕜) ^ s.card * detMinor b A' s with hf'def
  have hdiff : ∀ s, ‖f' s - f s‖ ≤ g s := by
    intro s
    simp only [hfdef, hf'def]
    rw [← mul_sub, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      detMinor_eq_gram b hA' s, detMinor_eq_gram b hA s]
    exact norm_det_gram_add_sub_le u v w s
  have hgs : Summable g :=
    (Hadamard.summable_prod_finset hxy0 (hx.add hy)).of_nonneg_of_le hg0
      (fun s => sub_le_self _ (Finset.prod_nonneg fun i _ => hx0 i))
  have hfs : Summable f := by
    refine Summable.of_norm ((Hadamard.summable_prod_finset hx0 hx).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun s => ?_))
    simp only [hfdef]
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, detMinor_eq_gram b hA s]
    exact norm_det_gram_le u v s
  have hds : Summable fun s => f' s - f s :=
    Summable.of_norm (hgs.of_nonneg_of_le (fun _ => norm_nonneg _) hdiff)
  have hf's : Summable f' := (hds.add hfs).congr fun s => sub_add_cancel _ _
  have hdet : fredholmDetIn b A' 1 - fredholmDetIn b A 1 = ∑' s, (f' s - f s) := by
    rw [Summable.tsum_sub hf's hfs]
    rfl
  have hpart : ∀ S : Finset (Finset ι), ∑ s ∈ S, g s ≤
      (∑' i, y i) * Real.exp ((∑' i, x i) + ∑' i, y i) := by
    intro S
    set t : Finset ι := S.sup id
    have hsub : S ⊆ t.powerset := fun s hs =>
      Finset.mem_powerset.2 (Finset.le_sup (f := id) hs)
    have hpow : ∑ s ∈ t.powerset, g s =
        ∏ i ∈ t, (1 + (x i + y i)) - ∏ i ∈ t, (1 + x i) := by
      rw [Finset.prod_one_add, Finset.prod_one_add, ← Finset.sum_sub_distrib]
    have hexp : ∏ i ∈ t, (1 + (x i + y i)) ≤ Real.exp (∑ i ∈ t, (x i + y i)) := by
      rw [Real.exp_sum]
      exact Finset.prod_le_prod₀ (fun i _ => by linarith [hxy0 i])
        (fun i _ => by linarith [Real.add_one_le_exp (x i + y i)])
    have hyt : ∑ i ∈ t, y i ≤ ∑' i, y i := hy.sum_le_tsum t fun i _ => hy0 i
    have hxyt : ∑ i ∈ t, (x i + y i) ≤ (∑' i, x i) + ∑' i, y i := by
      rw [← Summable.tsum_add hx hy]
      exact (hx.add hy).sum_le_tsum t fun i _ => hxy0 i
    have hPpos : 0 ≤ ∏ i ∈ t, (1 + (x i + y i)) :=
      Finset.prod_nonneg fun i _ => by linarith [hxy0 i]
    calc ∑ s ∈ S, g s ≤ ∑ s ∈ t.powerset, g s :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun s _ _ => hg0 s
      _ = ∏ i ∈ t, (1 + (x i + y i)) - ∏ i ∈ t, (1 + x i) := hpow
      _ ≤ (∑ i ∈ t, y i) * ∏ i ∈ t, (1 + (x i + y i)) := prod_one_add_add_sub_le t hx0 hy0
      _ ≤ (∑' i, y i) * Real.exp ((∑' i, x i) + ∑' i, y i) :=
          mul_le_mul hyt (hexp.trans (Real.exp_le_exp.2 hxyt)) hPpos
            (tsum_nonneg fun i => hy0 i)
  rw [hdet]
  calc ‖∑' s, (f' s - f s)‖ ≤ ∑' s, ‖f' s - f s‖ :=
        norm_tsum_le_tsum_norm (hgs.of_nonneg_of_le (fun _ => norm_nonneg _) hdiff)
    _ ≤ ∑' s, g s :=
        Summable.tsum_le_tsum hdiff (hgs.of_nonneg_of_le (fun _ => norm_nonneg _) hdiff) hgs
    _ ≤ _ := Real.tsum_le_of_sum_le hg0 hpart

end Series

/-- Passing to the limit `ε → 0⁺` in a bound valid for every `ε > 0`. -/
theorem le_of_forall_pos_le_of_continuousAt {g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g 0)
    (h : ∀ ε, 0 < ε → c ≤ g ε) : c ≤ g 0 :=
  ge_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall (s := Set.Ioi (0 : ℝ)) fun ε hε => h ε hε)

section Factorized

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {ι : Type*}

/-- A factorization gives a Gram representation whose weight sum is at most its cost. -/
theorem HSFactorization.tsum_weight_le {A : E →L[𝕜] E} (f : HSFactorization A)
    (b : HilbertBasis ι 𝕜 E) :
    Summable (fun i => ‖(f.left†) (b i)‖ * ‖f.right (b i)‖) ∧
      ∑' i, ‖(f.left†) (b i)‖ * ‖f.right (b i)‖ ≤ f.costIn b := by
  have hs := ((f.summable_left b).add (f.summable_right b)).div_const 2
  have hle : ∀ i, ‖(f.left†) (b i)‖ * ‖f.right (b i)‖ ≤
      (‖(f.left†) (b i)‖ ^ 2 + ‖f.right (b i)‖ ^ 2) / 2 := fun i => by
    nlinarith [sq_nonneg (‖(f.left†) (b i)‖ - ‖f.right (b i)‖)]
  have hsum := hs.of_nonneg_of_le (fun i => by positivity) hle
  refine ⟨hsum, (Summable.tsum_le_tsum hle hsum hs).trans (le_of_eq ?_)⟩
  rw [tsum_div_const, Summable.tsum_add (f.summable_left b) (f.summable_right b)]
  rfl

/-- **`|det(1 − zA)| ≤ exp(|z| ‖A‖₁)`** (Simon, *Trace Ideals*, Thm 3.4(a); sharp constant),
in any Hilbert basis, for every operator of finite trace norm. -/
theorem norm_fredholmDetIn_le_exp_traceNorm {A : E →L[𝕜] E} (hA : traceENorm A ≠ ⊤)
    (b : HilbertBasis ι 𝕜 E) (z : 𝕜) :
    ‖fredholmDetIn b A z‖ ≤ Real.exp (‖z‖ * traceNorm A) := by
  have key : ∀ ε, 0 < ε → ‖fredholmDetIn b A z‖ ≤ Real.exp (‖z‖ * (traceNorm A + ε)) := by
    intro ε hε
    obtain ⟨f, hf⟩ := exists_costIn_lt hA b hε
    obtain ⟨hs, hle⟩ := f.tsum_weight_le b
    refine (norm_fredholmDetIn_le_of_gram b (u := fun i => (f.left†) (b i))
      (v := fun i => f.right (b i)) (fun i j => f.inner_apply (b i) (b j)) hs z).trans ?_
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hle.trans hf.le) (norm_nonneg z))
  have hc : ContinuousAt (fun ε : ℝ => Real.exp (‖z‖ * (traceNorm A + ε))) 0 := by fun_prop
  simpa using le_of_forall_pos_le_of_continuousAt hc key

/-- The perturbation bound for two given factorizations (costs `< a`, `< d`):
`|det_b(1 − (A + D)) − det_b(1 − A)| ≤ 2d exp(2a + 2d)`. -/
theorem norm_fredholmDetIn_add_sub_le_of_factor (b : HilbertBasis ι 𝕜 E) {A D : E →L[𝕜] E}
    (f₁ : HSFactorization A) (f₂ : HSFactorization D) {a d : ℝ}
    (ha : f₁.costIn b < a) (hd : f₂.costIn b < d) :
    ‖fredholmDetIn b (A + D) 1 - fredholmDetIn b A 1‖ ≤ 2 * d * Real.exp (2 * a + 2 * d) := by
  have ha0 : 0 < a := lt_of_le_of_lt (f₁.costIn_nonneg b) ha
  have hd0 : 0 < d := lt_of_le_of_lt (f₂.costIn_nonneg b) hd
  set t : ℝ := Real.sqrt (d / a) with htdef
  have ht : 0 < t := Real.sqrt_pos.2 (div_pos hd0 ha0)
  have ht2 : t ^ 2 = d / a := Real.sq_sqrt (div_pos hd0 ha0).le
  have htinv2 : t⁻¹ ^ 2 = a / d := by rw [inv_pow, ht2, inv_div]
  set p : ι → ℝ := fun i => ‖(f₁.left†) (b i)‖ with hpdef
  set q : ι → ℝ := fun i => ‖(f₂.left†) (b i)‖ with hqdef
  set c : ι → ℝ := fun i => ‖f₁.right (b i)‖ with hcdef
  set e : ι → ℝ := fun i => ‖f₂.right (b i)‖ with hedef
  let u : ι → WithLp 2 (f₁.F × f₂.F) := fun i =>
    WithLp.toLp 2 ((f₁.left†) (b i), ((t⁻¹ : ℝ) : 𝕜) • (f₂.left†) (b i))
  let v : ι → WithLp 2 (f₁.F × f₂.F) := fun j => WithLp.toLp 2 (f₁.right (b j), 0)
  let w : ι → WithLp 2 (f₁.F × f₂.F) := fun j =>
    WithLp.toLp 2 (0, ((t : ℝ) : 𝕜) • f₂.right (b j))
  have hct : (starRingEnd 𝕜) ((t⁻¹ : ℝ) : 𝕜) * ((t : ℝ) : 𝕜) = 1 := by
    rw [RCLike.conj_ofReal, ← RCLike.ofReal_mul, inv_mul_cancel₀ ht.ne', RCLike.ofReal_one]
  have hA : ∀ i j, ⟪b i, A (b j)⟫_𝕜 = ⟪u i, v j⟫_𝕜 := by
    intro i j
    rw [f₁.inner_apply]
    show _ = ⟪(f₁.left†) (b i), f₁.right (b j)⟫_𝕜 + ⟪((t⁻¹ : ℝ) : 𝕜) • (f₂.left†) (b i), 0⟫_𝕜
    rw [inner_zero_right, add_zero]
  have hA' : ∀ i j, ⟪b i, (A + D) (b j)⟫_𝕜 = ⟪u i, v j + w j⟫_𝕜 := by
    intro i j
    rw [ContinuousLinearMap.add_apply, inner_add_right, f₁.inner_apply, f₂.inner_apply]
    have hvw : v j + w j =
        WithLp.toLp 2 (f₁.right (b j), ((t : ℝ) : 𝕜) • f₂.right (b j)) := by
      simp only [v, w, ← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add]
    rw [hvw]
    show _ = ⟪(f₁.left†) (b i), f₁.right (b j)⟫_𝕜 +
      ⟪((t⁻¹ : ℝ) : 𝕜) • (f₂.left†) (b i), ((t : ℝ) : 𝕜) • f₂.right (b j)⟫_𝕜
    rw [inner_smul_left, inner_smul_right, ← mul_assoc, hct, one_mul]
  have hu2 : ∀ i, ‖u i‖ ^ 2 = p i ^ 2 + t⁻¹ ^ 2 * q i ^ 2 := by
    intro i
    rw [norm_toLp_sq, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 ht), mul_pow]
  have hv : ∀ j, ‖v j‖ = c j := by
    intro j
    have h : ‖v j‖ ^ 2 = c j ^ 2 := by
      rw [show v j = WithLp.toLp 2 (f₁.right (b j), (0 : f₂.F)) from rfl, norm_toLp_sq,
        norm_zero]
      ring
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
  have hw : ∀ j, ‖w j‖ = t * e j := by
    intro j
    have h : ‖w j‖ ^ 2 = (t * e j) ^ 2 := by
      rw [show w j = WithLp.toLp 2 ((0 : f₁.F), ((t : ℝ) : 𝕜) • f₂.right (b j)) from rfl,
        norm_toLp_sq, norm_zero, norm_smul, RCLike.norm_ofReal, abs_of_pos ht]
      ring
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h
  have hun : ∀ i, 0 ≤ ‖u i‖ := fun i => norm_nonneg _
  have hx_le : ∀ i, ‖u i‖ * ‖v i‖ ≤ (p i ^ 2 + t⁻¹ ^ 2 * q i ^ 2 + c i ^ 2) / 2 := by
    intro i
    rw [hv, ← hu2]
    nlinarith [sq_nonneg (‖u i‖ - c i)]
  have hy_le : ∀ i, ‖u i‖ * ‖w i‖ ≤ (t ^ 2 * p i ^ 2 + q i ^ 2 + e i ^ 2) / 2 := by
    intro i
    rw [hw]
    have h1 : t ^ 2 * ‖u i‖ ^ 2 = t ^ 2 * p i ^ 2 + q i ^ 2 := by
      have htt : t ^ 2 * t⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ ht.ne', one_pow]
      rw [hu2]
      linear_combination (q i ^ 2) * htt
    nlinarith [sq_nonneg (t * ‖u i‖ - e i)]
  have hp := f₁.summable_left b
  have hq := f₂.summable_left b
  have hc := f₁.summable_right b
  have he := f₂.summable_right b
  have hXs : Summable fun i => (p i ^ 2 + t⁻¹ ^ 2 * q i ^ 2 + c i ^ 2) / 2 :=
    ((hp.add (hq.mul_left _)).add hc).div_const 2
  have hYs : Summable fun i => (t ^ 2 * p i ^ 2 + q i ^ 2 + e i ^ 2) / 2 :=
    (((hp.mul_left _).add hq).add he).div_const 2
  have hxs : Summable fun i => ‖u i‖ * ‖v i‖ :=
    hXs.of_nonneg_of_le (fun i => by positivity) hx_le
  have hys : Summable fun i => ‖u i‖ * ‖w i‖ :=
    hYs.of_nonneg_of_le (fun i => by positivity) hy_le
  set P := ∑' i, p i ^ 2
  set Q := ∑' i, q i ^ 2
  set C := ∑' i, c i ^ 2
  set Ee := ∑' i, e i ^ 2
  have hP0 : 0 ≤ P := tsum_nonneg fun i => sq_nonneg _
  have hQ0 : 0 ≤ Q := tsum_nonneg fun i => sq_nonneg _
  have hC0 : 0 ≤ C := tsum_nonneg fun i => sq_nonneg _
  have hE0 : 0 ≤ Ee := tsum_nonneg fun i => sq_nonneg _
  have hcost1 : (P + C) / 2 < a := ha
  have hcost2 : (Q + Ee) / 2 < d := hd
  have hXsum : ∑' i, (p i ^ 2 + t⁻¹ ^ 2 * q i ^ 2 + c i ^ 2) / 2 =
      (P + t⁻¹ ^ 2 * Q + C) / 2 := by
    rw [tsum_div_const, Summable.tsum_add (hp.add (hq.mul_left _)) hc,
      Summable.tsum_add hp (hq.mul_left _), tsum_mul_left]
  have hYsum : ∑' i, (t ^ 2 * p i ^ 2 + q i ^ 2 + e i ^ 2) / 2 =
      (t ^ 2 * P + Q + Ee) / 2 := by
    rw [tsum_div_const, Summable.tsum_add ((hp.mul_left _).add hq) he,
      Summable.tsum_add (hp.mul_left _) hq, tsum_mul_left]
  have hX : ∑' i, ‖u i‖ * ‖v i‖ ≤ 2 * a := by
    refine (Summable.tsum_le_tsum hx_le hxs hXs).trans ?_
    rw [hXsum, htinv2]
    have : a / d * Q ≤ 2 * a := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hd0]
      nlinarith
    linarith
  have hY : ∑' i, ‖u i‖ * ‖w i‖ ≤ 2 * d := by
    refine (Summable.tsum_le_tsum hy_le hys hYs).trans ?_
    rw [hYsum, ht2]
    have : d / a * P ≤ 2 * d := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ha0]
      nlinarith
    linarith
  have hY0 : 0 ≤ ∑' i, ‖u i‖ * ‖w i‖ := tsum_nonneg fun i => by positivity
  refine (norm_fredholmDetIn_sub_le_of_gram b hA hA' hxs hys).trans ?_
  exact mul_le_mul hY (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (by linarith)

/-- **Perturbation bound**: `|det_b(1 − (A + D)) − det_b(1 − A)| ≤ 2‖D‖₁ exp(2‖A‖₁ + 2‖D‖₁)`
for operators of finite trace norm, in any Hilbert basis. -/
theorem norm_fredholmDetIn_add_sub_le (b : HilbertBasis ι 𝕜 E) {A D : E →L[𝕜] E}
    (hA : traceENorm A ≠ ⊤) (hD : traceENorm D ≠ ⊤) :
    ‖fredholmDetIn b (A + D) 1 - fredholmDetIn b A 1‖ ≤
      2 * traceNorm D * Real.exp (2 * traceNorm A + 2 * traceNorm D) := by
  have key : ∀ ε, 0 < ε → ‖fredholmDetIn b (A + D) 1 - fredholmDetIn b A 1‖ ≤
      2 * (traceNorm D + ε) * Real.exp (2 * (traceNorm A + ε) + 2 * (traceNorm D + ε)) := by
    intro ε hε
    obtain ⟨f₁, hf₁⟩ := exists_costIn_lt hA b hε
    obtain ⟨f₂, hf₂⟩ := exists_costIn_lt hD b hε
    exact norm_fredholmDetIn_add_sub_le_of_factor b f₁ f₂ hf₁ hf₂
  have hc : ContinuousAt (fun ε : ℝ => 2 * (traceNorm D + ε) *
      Real.exp (2 * (traceNorm A + ε) + 2 * (traceNorm D + ε))) 0 := by fun_prop
  simpa using le_of_forall_pos_le_of_continuousAt hc key

/-- **Lipschitz bound for the entire determinant** (Simon-type, real-variable constants):
`|det_b(1 − Q₁) − det_b(1 − Q₂)| ≤ 2‖Q₁ − Q₂‖₁ exp(2(‖Q₁‖₁ + ‖Q₂‖₁))`. -/
theorem norm_fredholmDetIn_sub_le (b : HilbertBasis ι 𝕜 E) {Q₁ Q₂ : E →L[𝕜] E}
    (h₁ : traceENorm Q₁ ≠ ⊤) (h₂ : traceENorm Q₂ ≠ ⊤) :
    ‖fredholmDetIn b Q₁ 1 - fredholmDetIn b Q₂ 1‖ ≤
      2 * traceNorm (Q₁ - Q₂) * Real.exp (2 * (traceNorm Q₁ + traceNorm Q₂)) := by
  set M : E →L[𝕜] E := (2⁻¹ : 𝕜) • (Q₁ + Q₂) with hMdef
  set N : E →L[𝕜] E := (2⁻¹ : 𝕜) • (Q₁ - Q₂) with hNdef
  have hM1 : M + N = Q₁ := by
    have h : Q₁ + Q₂ + (Q₁ - Q₂) = (2 : 𝕜) • Q₁ := by rw [two_smul]; abel
    rw [hMdef, hNdef, ← smul_add, h, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hM2 : M + -N = Q₂ := by
    have h : Q₁ + Q₂ + -(Q₁ - Q₂) = (2 : 𝕜) • Q₂ := by rw [two_smul]; abel
    rw [hMdef, hNdef, ← smul_neg, ← smul_add, h, smul_smul, inv_mul_cancel₀ two_ne_zero,
      one_smul]
  have hMf : traceENorm M ≠ ⊤ := traceENorm_smul_ne_top _ (traceENorm_add_ne_top h₁ h₂)
  have hNf : traceENorm N ≠ ⊤ := traceENorm_smul_ne_top _ (traceENorm_sub_ne_top h₁ h₂)
  have hδf : traceENorm (Q₁ - Q₂) ≠ ⊤ := traceENorm_sub_ne_top h₁ h₂
  have e1 := norm_fredholmDetIn_add_sub_le b hMf hNf
  have e2 := norm_fredholmDetIn_add_sub_le b hMf (traceENorm_neg_ne_top hNf)
  rw [hM1] at e1
  rw [hM2, traceNorm_neg] at e2
  have h2 : ‖(2⁻¹ : 𝕜)‖ = 2⁻¹ := by rw [norm_inv, RCLike.norm_ofNat]
  have hm : traceNorm M ≤ 2⁻¹ * (traceNorm Q₁ + traceNorm Q₂) := by
    refine (traceNorm_smul_le _ (traceENorm_add_ne_top h₁ h₂)).trans ?_
    rw [h2]
    exact mul_le_mul_of_nonneg_left (traceNorm_add_le h₁ h₂) (by norm_num)
  have hn : traceNorm N ≤ 2⁻¹ * traceNorm (Q₁ - Q₂) := by
    refine (traceNorm_smul_le _ hδf).trans ?_
    rw [h2]
  have hδ : traceNorm (Q₁ - Q₂) ≤ traceNorm Q₁ + traceNorm Q₂ := traceNorm_sub_le h₁ h₂
  have hn0 := traceNorm_nonneg N
  have hm0 := traceNorm_nonneg M
  set n := traceNorm N
  set m := traceNorm M
  set δ := traceNorm (Q₁ - Q₂)
  have hexp : Real.exp (2 * m + 2 * n) ≤ Real.exp (2 * (traceNorm Q₁ + traceNorm Q₂)) :=
    Real.exp_le_exp.2 (by linarith)
  calc ‖fredholmDetIn b Q₁ 1 - fredholmDetIn b Q₂ 1‖
      ≤ ‖fredholmDetIn b Q₁ 1 - fredholmDetIn b M 1‖ +
          ‖fredholmDetIn b Q₂ 1 - fredholmDetIn b M 1‖ := by
        rw [norm_sub_rev (fredholmDetIn b Q₂ 1)]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * n * Real.exp (2 * m + 2 * n) + 2 * n * Real.exp (2 * m + 2 * n) := add_le_add e1 e2
    _ = (4 * n) * Real.exp (2 * m + 2 * n) := by ring
    _ ≤ (2 * δ) * Real.exp (2 * (traceNorm Q₁ + traceNorm Q₂)) :=
        mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by linarith [traceNorm_nonneg (Q₁ - Q₂)])
    _ = 2 * δ * Real.exp (2 * (traceNorm Q₁ + traceNorm Q₂)) := by ring

omit [CompleteSpace E] in
/-- Moving the coupling into the operator: `det_b(1 − z A) = det_b(1 − 1 · (z A))`. -/
theorem fredholmDetIn_smul_one (b : HilbertBasis ι 𝕜 E) (A : E →L[𝕜] E) (z : 𝕜) :
    fredholmDetIn b (z • A) 1 = fredholmDetIn b A z := by
  unfold fredholmDetIn
  refine tsum_congr fun s => ?_
  have hm : detMinor b (z • A) s = z ^ s.card * detMinor b A s := by
    unfold detMinor
    have : (Matrix.of fun i j : s => ⟪b i, (z • A) (b j)⟫_𝕜) =
        z • Matrix.of fun i j : s => ⟪b i, A (b j)⟫_𝕜 := by
      ext i j
      simp [inner_smul_right]
    rw [this, Matrix.det_smul, Fintype.card_coe]
  rw [hm, neg_pow, neg_pow z]
  ring

/-- **Lipschitz bound at coupling `z`**:
`|det_b(1 − zQ₁) − det_b(1 − zQ₂)| ≤ 2|z| ‖Q₁ − Q₂‖₁ exp(2|z|(‖Q₁‖₁ + ‖Q₂‖₁))`. -/
theorem norm_fredholmDetIn_sub_le_coupling (b : HilbertBasis ι 𝕜 E) {Q₁ Q₂ : E →L[𝕜] E}
    (h₁ : traceENorm Q₁ ≠ ⊤) (h₂ : traceENorm Q₂ ≠ ⊤) (z : 𝕜) :
    ‖fredholmDetIn b Q₁ z - fredholmDetIn b Q₂ z‖ ≤
      2 * ‖z‖ * traceNorm (Q₁ - Q₂) *
        Real.exp (2 * ‖z‖ * (traceNorm Q₁ + traceNorm Q₂)) := by
  rw [← fredholmDetIn_smul_one b Q₁, ← fredholmDetIn_smul_one b Q₂]
  have h := norm_fredholmDetIn_sub_le b (traceENorm_smul_ne_top z h₁)
    (traceENorm_smul_ne_top z h₂)
  have hδ : traceNorm (z • Q₁ - z • Q₂) ≤ ‖z‖ * traceNorm (Q₁ - Q₂) := by
    rw [← smul_sub]
    exact traceNorm_smul_le z (traceENorm_sub_ne_top h₁ h₂)
  have hs1 := traceNorm_smul_le z h₁
  have hs2 := traceNorm_smul_le z h₂
  refine h.trans ?_
  have hexp : Real.exp (2 * (traceNorm (z • Q₁) + traceNorm (z • Q₂))) ≤
      Real.exp (2 * ‖z‖ * (traceNorm Q₁ + traceNorm Q₂)) :=
    Real.exp_le_exp.2 (by nlinarith)
  calc 2 * traceNorm (z • Q₁ - z • Q₂) * Real.exp (2 * (traceNorm (z • Q₁) + traceNorm (z • Q₂)))
      ≤ 2 * (‖z‖ * traceNorm (Q₁ - Q₂)) *
          Real.exp (2 * ‖z‖ * (traceNorm Q₁ + traceNorm Q₂)) :=
        mul_le_mul (by linarith) hexp (Real.exp_pos _).le
          (by have := norm_nonneg z; have := traceNorm_nonneg (Q₁ - Q₂); positivity)
    _ = _ := by ring

/-- `|det(1 − zA)| ≤ exp(|z| ‖A‖₁)` for the canonical-basis determinant. -/
theorem norm_fredholmDet_le_exp_traceNorm {A : E →L[𝕜] E} (hA : traceENorm A ≠ ⊤) (z : 𝕜) :
    ‖fredholmDet A z‖ ≤ Real.exp (‖z‖ * traceNorm A) :=
  norm_fredholmDetIn_le_exp_traceNorm hA _ z

/-- **Lipschitz bound** for the canonical-basis determinant at coupling `z`. -/
theorem norm_fredholmDet_sub_le {Q₁ Q₂ : E →L[𝕜] E} (h₁ : traceENorm Q₁ ≠ ⊤)
    (h₂ : traceENorm Q₂ ≠ ⊤) (z : 𝕜) :
    ‖fredholmDet Q₁ z - fredholmDet Q₂ z‖ ≤
      2 * ‖z‖ * traceNorm (Q₁ - Q₂) *
        Real.exp (2 * ‖z‖ * (traceNorm Q₁ + traceNorm Q₂)) :=
  norm_fredholmDetIn_sub_le_coupling _ h₁ h₂ z

/-- **Continuity of the determinant in trace norm**: if `‖Qₙ − Q‖₁ → 0` then
`det(1 − zQₙ) → det(1 − zQ)`. -/
theorem tendsto_fredholmDet_of_traceNorm {α : Type*} {l : Filter α} {Q : α → E →L[𝕜] E}
    {Q₀ : E →L[𝕜] E} (h₀ : traceENorm Q₀ ≠ ⊤) (hfin : ∀ n, traceENorm (Q n - Q₀) ≠ ⊤)
    (hlim : Tendsto (fun n => traceNorm (Q n - Q₀)) l (𝓝 0)) (z : 𝕜) :
    Tendsto (fun n => fredholmDet (Q n) z) l (𝓝 (fredholmDet Q₀ z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hQn : ∀ n, traceENorm (Q n) ≠ ⊤ := fun n => by
    have h := traceENorm_add_ne_top (hfin n) h₀
    rwa [sub_add_cancel] at h
  set a₀ := traceNorm Q₀
  have hbound : ∀ n, ‖fredholmDet (Q n) z - fredholmDet Q₀ z‖ ≤
      2 * ‖z‖ * traceNorm (Q n - Q₀) *
        Real.exp (2 * ‖z‖ * (2 * a₀ + traceNorm (Q n - Q₀))) := by
    intro n
    refine (norm_fredholmDet_sub_le (hQn n) h₀ z).trans ?_
    have htri : traceNorm (Q n) ≤ traceNorm (Q n - Q₀) + a₀ := by
      have h := traceNorm_add_le (hfin n) h₀
      rwa [sub_add_cancel] at h
    have hz := norm_nonneg z
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (by have := traceNorm_nonneg (Q n - Q₀); positivity)
    nlinarith
  have hc : Continuous fun x : ℝ => 2 * ‖z‖ * x * Real.exp (2 * ‖z‖ * (2 * a₀ + x)) := by
    fun_prop
  have hg := (hc.tendsto 0).comp hlim
  simp only [mul_zero, zero_mul, Function.comp_def] at hg
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hg

/-- **Continuity under Hilbert–Schmidt convergence of the factors**: if `Bₙ → B` and
`Cₙ → C` in Hilbert–Schmidt norm then `det(1 − z BₙCₙ) → det(1 − z BC)` (the form used for
`P̄ₓ → I` arguments; Simon, *Trace Ideals*, Thm 3.4 + Thm 2.7). -/
theorem tendsto_fredholmDet_comp {α : Type*} {l : Filter α} {B C : E →L[𝕜] E}
    {Bn Cn : α → E →L[𝕜] E} (hB : IsHilbertSchmidt B) (hC : IsHilbertSchmidt C)
    (hBn : ∀ n, IsHilbertSchmidt (Bn n)) (hCn : ∀ n, IsHilbertSchmidt (Cn n))
    (hBl : Tendsto (fun n => hsNorm (Bn n - B)) l (𝓝 0))
    (hCl : Tendsto (fun n => hsNorm (Cn n - C)) l (𝓝 0)) (z : 𝕜) :
    Tendsto (fun n => fredholmDet (Bn n ∘L Cn n) z) l (𝓝 (fredholmDet (B ∘L C) z)) := by
  have hdecomp : ∀ n, Bn n ∘L Cn n - B ∘L C =
      ((Bn n - B) ∘L (Cn n - C) + (Bn n - B) ∘L C) + B ∘L (Cn n - C) := by
    intro n
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  have htc : ∀ {S T : E →L[𝕜] E}, IsHilbertSchmidt S → IsHilbertSchmidt T →
      traceENorm (S ∘L T) ≠ ⊤ := fun hS hT =>
    IsTraceClass.traceENorm_ne_top (IsHilbertSchmidt.isTraceClass_comp hS hT)
  have hdB : ∀ n, IsHilbertSchmidt (Bn n - B) := fun n => (hBn n).sub hB
  have hdC : ∀ n, IsHilbertSchmidt (Cn n - C) := fun n => (hCn n).sub hC
  have h1 : ∀ n, traceENorm ((Bn n - B) ∘L (Cn n - C)) ≠ ⊤ := fun n => htc (hdB n) (hdC n)
  have h2 : ∀ n, traceENorm ((Bn n - B) ∘L C) ≠ ⊤ := fun n => htc (hdB n) hC
  have h3 : ∀ n, traceENorm (B ∘L (Cn n - C)) ≠ ⊤ := fun n => htc hB (hdC n)
  have hfin : ∀ n, traceENorm (Bn n ∘L Cn n - B ∘L C) ≠ ⊤ := fun n => by
    rw [hdecomp]
    exact traceENorm_add_ne_top (traceENorm_add_ne_top (h1 n) (h2 n)) (h3 n)
  refine tendsto_fredholmDet_of_traceNorm (htc hB hC) hfin ?_ z
  have hle : ∀ n, traceNorm (Bn n ∘L Cn n - B ∘L C) ≤
      hsNorm (Bn n - B) * hsNorm (Cn n - C) + hsNorm (Bn n - B) * hsNorm C +
        hsNorm B * hsNorm (Cn n - C) := by
    intro n
    rw [hdecomp]
    refine (traceNorm_add_le (traceENorm_add_ne_top (h1 n) (h2 n)) (h3 n)).trans ?_
    refine add_le_add ((traceNorm_add_le (h1 n) (h2 n)).trans
      (add_le_add (traceNorm_comp_le (hdB n) (hdC n)) (traceNorm_comp_le (hdB n) hC)))
      (traceNorm_comp_le hB (hdC n))
  have hlim : Tendsto (fun n => hsNorm (Bn n - B) * hsNorm (Cn n - C) +
      hsNorm (Bn n - B) * hsNorm C + hsNorm B * hsNorm (Cn n - C)) l (𝓝 0) := by
    have := ((hBl.mul hCl).add (hBl.mul_const (hsNorm C))).add (hCl.const_mul (hsNorm B))
    simpa using this
  exact squeeze_zero (fun n => traceNorm_nonneg _) hle hlim

end Factorized

end HilbertSchmidt
