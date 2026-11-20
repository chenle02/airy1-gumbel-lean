/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Mesh.MeshLimit
import Airy1GumbelContrib.TwoInterval.TwoIntervalMembership

/-!
# The two-block dyadic mesh and the two-interval determinant

Two unit blocks `[x, x + 1]` and `[x + 1 + r, x + 2 + r]`
(gap `r > 0`), the same constant level `M` on both.  At mesh level `m ≥ 1`, `g = 2⁻ᵐ`, the
union of the two dyadic meshes `I_m(x) ∪ I_m(x + 1 + r)` has `(level, gap)` entries

  `(M, g)^{×(2ᵐ − 1)}, (M, g + r), (M, g)^{×2ᵐ}`  (`cupList`, head `(M, g)`),

so the total time is `2 + r` (`gapSum_cupList`) and the fdd operator at weight `a` is
admissible exactly when `r + 3 ≤ a` — at `a = √(2M)` this is the guard of contrib's
`K̃∪ = kcupKerT √(2M) M r` (`memLp_kcupKerT`) and of the main record `QRTwoIntervalLaw`.

* **Kernel calculus.** `lamKerN_append`: the kernel of a concatenated entry list is the
  composition of the kernels of the pieces; `lamKerN_bump`: lengthening the last gap by `r`
  composes with `p_r` on the right.  Hence the union mesh kernel is
  `Λ^∪_m = Λ_m ⋆ (P_r ⋆ Λ_m)` (`lamKerN_cupList`), `Λ_m = meshLamKer M 1 m` the one-block
  mesh kernel of `Mesh/MeshLimit.lean`, and the union hitting kernel is
  `H^∪_m = p_{2+r} − Λ_m ⋆ (P_r ⋆ Λ_m)` (`cupHitKer_eq`), while contrib's
  `D_r = P₁P_rP₁ − ΛP_rΛ` is `p_{2+r} − Λ ⋆ (P_r ⋆ Λ)` (`dRKer_eq_heat_sub`).
* **Kernel limit** (from the one-block fact `MeshHittingLimit M 1`, i.e. `Λ ≤ Λ_m` a.e. and
  `Λ_m → Λ` a.e.): `0 ≤ H^∪_m ≤ D_r` a.e. (`ae_cupHitKer_le_dRKer`, monotonicity of the
  composition) and `H^∪_m → D_r` a.e. (`ae_tendsto_cupHitKer`, dominated convergence inside the
  two compositions, dominators `p_1 ⋆ p_r ⋆ p_1`).
* **Determinants.** The fdd operator `cupOp = T_{V^∪_m} ∘ T_W` and
  `K̃∪ = T_{Ṽ_{D,r}} ∘ T_{W_{2+r,a}}` (`kcupKerT_eq_compKernel_vdRKer_wSKer`) share the right
  factor `W = wKernel (2 + r) a`; the left factors converge in `L²` (dominated by `Ṽ_{D,r}²`,
  `memLp_vdRKer`), so `det(I − cupOp) → det(I − K̃∪)` (`tendsto_fredholmDet_cupOp`).
* **Fdd identity** (`airy1FinCdf_cupSet`): `F_{I_m(x) ∪ I_m(x+1+r)}(M, …, M) = det(I − cupOp)`
  at any admissible weight `a ≥ r + 3`.
* **Combined** (`tendsto_airy1FinCdf_cupSet`): under `MeshHittingLimit M 1`, `M > 0`,
  `r > 0`, `r + 3 ≤ a`: `F_{I_{n+1}(x) ∪ I_{n+1}(x+1+r)}(M, …, M) → det(I − kcupKerT a M r)`.
-/

namespace AiryFdd

open MeasureTheory Real Set Filter Topology
open HilbertSchmidt

/-! ## Almost-everywhere bookkeeping on the plane -/

/-- Two almost-everywhere statements in the two coordinates give one on the plane. -/
theorem ae_prod_of_ae_fst_snd {P Q : ℝ → Prop} (hP : ∀ᵐ x, P x) (hQ : ∀ᵐ y, Q y) :
    ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), P p.1 ∧ Q p.2 :=
  ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).tendsto_ae.eventually hP).and
    ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).tendsto_ae.eventually hQ)

/-- An a.e. statement on the plane holds, for a.e. second coordinate, a.e. in the first. -/
theorem ae_ae_swap_of_ae_prod {P : ℝ × ℝ → Prop}
    (h : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), P p) : ∀ᵐ y : ℝ, ∀ᵐ w : ℝ, P (w, y) := by
  have h' : ∀ᵐ q ∂(volume.prod volume : Measure (ℝ × ℝ)), P q.swap :=
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.tendsto_ae.eventually h
  exact Measure.ae_ae_of_ae_prod h'

/-! ## Heat-dominated kernel compositions -/

/-- `|A ⋆ B| ≤ p_{s+t}` when `|A| ≤ p_s` and `|B| ≤ p_t`. -/
theorem abs_compKernel_le_heat {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {A B : ℝ × ℝ → ℝ}
    (hA : Measurable A) (hB : Measurable B) (hAb : ∀ p, |A p| ≤ heatKernel s (p.1 - p.2))
    (hBb : ∀ p, |B p| ≤ heatKernel t (p.1 - p.2)) (p : ℝ × ℝ) :
    |AiryConj.compKernel A B p| ≤ heatKernel (s + t) (p.1 - p.2) := by
  obtain ⟨x, y⟩ := p
  have hint : Integrable fun w : ℝ => A (x, w) * B (w, y) :=
    AiryTwoInt.integrable_pair_mul_of_heatKernel_le hs ht hA hB (fun a b => hAb (a, b))
      (fun a b => hBb (a, b)) x y
  show |∫ w : ℝ, A (x, w) * B (w, y)| ≤ heatKernel (s + t) (x - y)
  rw [← AiryTwoInt.heatKernel_conv hs ht x y]
  refine (abs_integral_le_integral_abs).trans
    (integral_mono hint.abs (integrable_heat_mul_heat hs ht x y) fun w => ?_)
  rw [abs_mul]
  exact mul_le_mul (hAb (x, w)) (hBb (w, y)) (abs_nonneg _) (heatKernel_pos hs _).le

/-- Associativity of heat-dominated kernel compositions (Fubini). -/
theorem compKernel_assoc_heat {s t τ : ℝ} (hs : 0 < s) (ht : 0 < t) (hτ : 0 < τ)
    {A B C : ℝ × ℝ → ℝ} (hA : Measurable A) (hB : Measurable B) (hC : Measurable C)
    (hAb : ∀ p, |A p| ≤ heatKernel s (p.1 - p.2)) (hBb : ∀ p, |B p| ≤ heatKernel t (p.1 - p.2))
    (hCb : ∀ p, |C p| ≤ heatKernel τ (p.1 - p.2)) :
    AiryConj.compKernel (AiryConj.compKernel A B) C
      = AiryConj.compKernel A (AiryConj.compKernel B C) := by
  funext p
  obtain ⟨x, y⟩ := p
  refine AiryTwoInt.compKernel_assoc x y ?_
  refine AiryTwoInt.integrable_uncurry_of_abs_le hs ht le_rfl x hA (fun z => hAb (x, z)) hB
    (fun z₁ z₂ => hBb (z₁, z₂)) (hC.comp (measurable_id.prodMk measurable_const))
    ((4 * Real.pi * τ) ^ (-1 / 2 : ℝ)) (fun z => ?_)
  rw [zero_mul, Real.exp_zero, mul_one]
  exact (hCb (z, y)).trans (AiryTwoInt.heatKernel_le hτ _)

/-- **Dominated convergence inside a composition.** If `A_n → A` and `B_n → B` a.e. on the
plane, with `|A_n| ≤ p_s`, `|B_n| ≤ p_t`, then `A_n ⋆ B_n → A ⋆ B` a.e. on the plane. -/
theorem ae_tendsto_compKernel {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {A B : ℕ → ℝ × ℝ → ℝ} {A₀ B₀ : ℝ × ℝ → ℝ} (hAm : ∀ n, Measurable (A n))
    (hBm : ∀ n, Measurable (B n)) (hAb : ∀ n p, |A n p| ≤ heatKernel s (p.1 - p.2))
    (hBb : ∀ n p, |B n p| ≤ heatKernel t (p.1 - p.2))
    (hAl : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
      Tendsto (fun n => A n p) atTop (𝓝 (A₀ p)))
    (hBl : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
      Tendsto (fun n => B n p) atTop (𝓝 (B₀ p))) :
    ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
      Tendsto (fun n => AiryConj.compKernel (A n) (B n) p) atTop
        (𝓝 (AiryConj.compKernel A₀ B₀ p)) := by
  filter_upwards [ae_prod_of_ae_fst_snd (Measure.ae_ae_of_ae_prod hAl)
    (ae_ae_swap_of_ae_prod hBl)] with p hp
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, hy⟩ := hp
  refine tendsto_integral_of_dominated_convergence
    (fun w => heatKernel s (x - w) * heatKernel t (w - y)) (fun n => ?_)
    (integrable_heat_mul_heat hs ht x y) (fun n => ?_) ?_
  · exact (((hAm n).comp (measurable_const.prodMk measurable_id)).mul
      ((hBm n).comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  · refine Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hAb n (x, w)) (hBb n (w, y)) (abs_nonneg _) (heatKernel_pos hs _).le
  · filter_upwards [hx, hy] with w h1 h2
    exact h1.mul h2

/-- **Monotonicity of the composition** for nonnegative heat-dominated kernels, a.e. -/
theorem ae_compKernel_mono {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {A A' B B' : ℝ × ℝ → ℝ}
    (hA : Measurable A) (hA' : Measurable A') (hB : Measurable B) (hB' : Measurable B')
    (hAb : ∀ p, |A p| ≤ heatKernel s (p.1 - p.2)) (hAb' : ∀ p, |A' p| ≤ heatKernel s (p.1 - p.2))
    (hBb : ∀ p, |B p| ≤ heatKernel t (p.1 - p.2)) (hBb' : ∀ p, |B' p| ≤ heatKernel t (p.1 - p.2))
    (hA0 : ∀ p, 0 ≤ A p) (hB0 : ∀ p, 0 ≤ B p)
    (hAA : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), A p ≤ A' p)
    (hBB : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), B p ≤ B' p) :
    ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
      AiryConj.compKernel A B p ≤ AiryConj.compKernel A' B' p := by
  filter_upwards [ae_prod_of_ae_fst_snd (Measure.ae_ae_of_ae_prod hAA)
    (ae_ae_swap_of_ae_prod hBB)] with p hp
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, hy⟩ := hp
  refine integral_mono_ae
    (AiryTwoInt.integrable_pair_mul_of_heatKernel_le hs ht hA hB (fun a b => hAb (a, b))
      (fun a b => hBb (a, b)) x y)
    (AiryTwoInt.integrable_pair_mul_of_heatKernel_le hs ht hA' hB' (fun a b => hAb' (a, b))
      (fun a b => hBb' (a, b)) x y) ?_
  filter_upwards [hx, hy] with w h1 h2
  exact mul_le_mul h1 h2 (hB0 _) ((hA0 _).trans h1)

/-! ## Kernel calculus for `lamKerN` -/

theorem abs_lamKerN_le {e : ℝ × ℝ} {L : List (ℝ × ℝ)} (he : 0 < e.2) (hL : ∀ y ∈ L, 0 < y.2)
    (p : ℝ × ℝ) : |lamKerN e L p| ≤ heatKernel (gapSum e L) (p.1 - p.2) := by
  obtain ⟨-, h0, h1⟩ := lamKerN_props L e he hL
  rw [abs_of_nonneg (h0 p)]
  exact h1 p

theorem gapSum_append : ∀ (L : List (ℝ × ℝ)) (e y : ℝ × ℝ) (L' : List (ℝ × ℝ)),
    gapSum e (L ++ y :: L') = gapSum e L + gapSum y L'
  | [], e, y, L' => rfl
  | z :: L, e, y, L' => by
    show e.2 + gapSum z (L ++ y :: L') = e.2 + gapSum z L + gapSum y L'
    rw [gapSum_append L z y L']
    ring

/-- **Concatenation**: the kernel of `e :: (L ++ y :: L')` is the composition of the kernels of
`e :: L` and `y :: L'` (the last gap of `e :: L` is the time between the two pieces). -/
theorem lamKerN_append : ∀ (L : List (ℝ × ℝ)) (e y : ℝ × ℝ) (L' : List (ℝ × ℝ)),
    0 < e.2 → (∀ z ∈ L, 0 < z.2) → 0 < y.2 → (∀ z ∈ L', 0 < z.2) →
      lamKerN e (L ++ y :: L') = AiryConj.compKernel (lamKerN e L) (lamKerN y L')
  | [], e, y, L', _, _, _, _ => by
    funext p
    obtain ⟨u, v⟩ := p
    show (Iic e.1).indicator (fun _ => (1 : ℝ)) u
        * (∫ w : ℝ, heatKernel e.2 (u - w) * lamKerN y L' (w, v))
      = ∫ w : ℝ, ((Iic e.1).indicator (fun _ => (1 : ℝ)) u * heatKernel e.2 (u - w))
          * lamKerN y L' (w, v)
    rw [← integral_const_mul]
    congr 1
    funext w
    ring
  | z :: L, e, y, L', he, hL, hy, hL' => by
    have hz : 0 < z.2 := hL z List.mem_cons_self
    have hL0 : ∀ w ∈ L, 0 < w.2 := fun w hw => hL w (List.mem_cons_of_mem _ hw)
    have ih := lamKerN_append L z y L' hz hL0 hy hL'
    obtain ⟨hzm, -, -⟩ := lamKerN_props L z hz hL0
    obtain ⟨hym, -, -⟩ := lamKerN_props L' y hy hL'
    have hassoc := compKernel_assoc_heat he (gapSum_pos L z hz hL0) (gapSum_pos L' y hy hL')
      (AiryTwoInt.measurable_heatKerTwo e.2) hzm hym
      (fun p => AiryTwoInt.heatKerTwo_abs_le_self he p) (abs_lamKerN_le hz hL0)
      (abs_lamKerN_le hy hL')
    funext p
    obtain ⟨u, v⟩ := p
    show (Iic e.1).indicator (fun _ => (1 : ℝ)) u
        * AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (lamKerN z (L ++ y :: L')) (u, v)
      = ∫ w : ℝ, ((Iic e.1).indicator (fun _ => (1 : ℝ)) u
          * AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (lamKerN z L) (u, w))
          * lamKerN y L' (w, v)
    rw [ih, ← hassoc]
    show (Iic e.1).indicator (fun _ => (1 : ℝ)) u
        * (∫ w : ℝ, AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (lamKerN z L) (u, w)
          * lamKerN y L' (w, v)) = _
    rw [← integral_const_mul]
    congr 1
    funext w
    ring

/-- One level: `P̄_x e^{τΔ} ⋆ p_r = P̄_x e^{(τ+r)Δ}`. -/
theorem lamKer1_comp_heat {x τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) :
    AiryConj.compKernel (lamKer1 x τ) (AiryTwoInt.heatKerTwo r) = lamKer1 x (τ + r) := by
  funext p
  obtain ⟨u, v⟩ := p
  show (∫ w : ℝ, ((Iic x).indicator (fun _ => (1 : ℝ)) u * heatKernel τ (u - w))
      * heatKernel r (w - v)) = (Iic x).indicator (fun _ => (1 : ℝ)) u * heatKernel (τ + r) (u - v)
  rw [← AiryTwoInt.heatKernel_conv hτ hr u v, ← integral_const_mul]
  congr 1
  funext w
  ring

/-- **Lengthening the last gap by `r`** composes with `p_r` on the right. -/
theorem lamKerN_bump (L : List (ℝ × ℝ)) (e : ℝ × ℝ) (x : ℝ) {τ r : ℝ} (he : 0 < e.2)
    (hL : ∀ z ∈ L, 0 < z.2) (hτ : 0 < τ) (hr : 0 < r) :
    lamKerN e (L ++ [(x, τ + r)])
      = AiryConj.compKernel (lamKerN e (L ++ [(x, τ)])) (AiryTwoInt.heatKerTwo r) := by
  have hnil : ∀ z ∈ ([] : List (ℝ × ℝ)), 0 < z.2 := fun _ h => absurd h List.not_mem_nil
  rw [lamKerN_append L e (x, τ + r) [] he hL (by simp only; linarith) hnil,
    lamKerN_append L e (x, τ) [] he hL hτ hnil]
  obtain ⟨hm, -, -⟩ := lamKerN_props L e he hL
  show AiryConj.compKernel (lamKerN e L) (lamKer1 x (τ + r))
    = AiryConj.compKernel (AiryConj.compKernel (lamKerN e L) (lamKer1 x τ))
        (AiryTwoInt.heatKerTwo r)
  rw [compKernel_assoc_heat (gapSum_pos L e he hL) hτ hr hm (measurable_lamKer1 x τ)
    (AiryTwoInt.measurable_heatKerTwo r) (abs_lamKerN_le he hL)
    (fun p => (abs_of_nonneg (lamKer1_nonneg hτ x p)).trans_le (lamKer1_le hτ x p))
    (fun p => AiryTwoInt.heatKerTwo_abs_le_self hr p), lamKer1_comp_heat hτ hr]

/-! ## The one-block mesh kernel `Λ_m` -/

/-- The one-block mesh kernel `Λ_m = (P̄_M e^{gΔ})^{2ᵐ}` (`g = T/2ᵐ`). -/
noncomputable def meshLamKer (M T : ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  lamKerN (M, meshGap T n) (meshTail M T n)

theorem meshLamKer_props {M T : ℝ} (hT : 0 < T) (n : ℕ) :
    Measurable (meshLamKer M T n) ∧ (∀ p, 0 ≤ meshLamKer M T n p) ∧
      (∀ p, meshLamKer M T n p ≤ heatKernel T (p.1 - p.2)) := by
  have h := lamKerN_props (meshTail M T n) (M, meshGap T n) (meshGap_pos hT n)
    (meshTail_pos hT n)
  rw [gapSum_meshTail] at h
  exact h

theorem abs_meshLamKer_le {M T : ℝ} (hT : 0 < T) (n : ℕ) (p : ℝ × ℝ) :
    |meshLamKer M T n p| ≤ heatKernel T (p.1 - p.2) := by
  rw [abs_of_nonneg ((meshLamKer_props hT n).2.1 p)]
  exact (meshLamKer_props hT n).2.2 p

theorem meshHitKer_eq_sub (M T : ℝ) (n : ℕ) (p : ℝ × ℝ) :
    meshHitKer M T n p = heatKernel T (p.1 - p.2) - meshLamKer M T n p := by
  unfold meshHitKer hitKerN meshLamKer
  rw [gapSum_meshTail]

/-- (K2) for the mesh kernel: `Λ_m → Λ = lamKerTwo M` a.e. -/
theorem ae_tendsto_meshLamKer {M : ℝ} (hK : MeshHittingLimit M 1) :
    ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
      Tendsto (fun n => meshLamKer M 1 n p) atTop (𝓝 (AiryTwoInt.lamKerTwo M p)) := by
  filter_upwards [hK.tendsto_qMT] with p hp
  have heq : (fun n => meshLamKer M 1 n p)
      = fun n => heatKernel 1 (p.1 - p.2) - meshHitKer M 1 n p := by
    funext n; rw [meshHitKer_eq_sub]; ring
  rw [heq, AiryTwoInt.lamKerTwo_eq_sub]
  exact tendsto_const_nhds.sub hp

/-- (K1) for the mesh kernel: `Λ ≤ Λ_m` a.e. -/
theorem ae_lamKerTwo_le_meshLamKer {M : ℝ} (hK : MeshHittingLimit M 1) (n : ℕ) :
    ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
      AiryTwoInt.lamKerTwo M p ≤ meshLamKer M 1 n p := by
  filter_upwards [hK.le_qMT n] with p hp
  rw [meshHitKer_eq_sub] at hp
  rw [AiryTwoInt.lamKerTwo_eq_sub]
  show heatKernel 1 (p.1 - p.2) - AiryConj.qMT M 1 p.1 p.2 ≤ _
  linarith

/-! ## The two-block entry list -/

/-- The tail of the two-block entry list (head `(M, g)`, `g = 2⁻ᵐ`):
`(M, g)^{×(2ᵐ − 2)}, (M, g + r), (M, g), (M, g)^{×(2ᵐ − 1)}`. -/
noncomputable def cupList (M r : ℝ) (m : ℕ) : List (ℝ × ℝ) :=
  List.replicate (2 ^ m - 2) (M, meshGap 1 m) ++
    (M, meshGap 1 m + r) :: (M, meshGap 1 m) :: meshTail M 1 m

theorem cupList_pos {M r : ℝ} (hr : 0 ≤ r) (m : ℕ) : ∀ y ∈ cupList M r m, 0 < y.2 := by
  have hg := meshGap_pos one_pos m
  intro y hy
  simp only [cupList, List.mem_append, List.mem_replicate, List.mem_cons] at hy
  rcases hy with ⟨-, rfl⟩ | rfl | rfl | hy
  · exact hg
  · show 0 < meshGap 1 m + r; linarith
  · exact hg
  · exact meshTail_pos one_pos m y hy

theorem two_pow_eq_add_two {m : ℕ} (hm : 1 ≤ m) : ∃ k : ℕ, 2 ^ m = k + 2 := by
  have : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact ⟨2 ^ m - 2, by omega⟩

/-- The first block with its last gap at `g`: the one-block mesh tail. -/
theorem replicate_append_meshTail {M : ℝ} {m : ℕ} (hm : 1 ≤ m) :
    List.replicate (2 ^ m - 2) (M, meshGap 1 m) ++ [(M, meshGap 1 m)] = meshTail M 1 m := by
  obtain ⟨k, hk⟩ := two_pow_eq_add_two hm
  rw [meshTail, hk, ← List.replicate_succ']
  congr 1

/-- The two-block entries have total time `2 + r`. -/
theorem gapSum_cupList (M r : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    gapSum (M, meshGap 1 m) (cupList M r m) = 2 + r := by
  have h1 := gapSum_meshTail M 1 m
  rw [← replicate_append_meshTail hm, gapSum_append] at h1
  rw [cupList, show List.replicate (2 ^ m - 2) (M, meshGap 1 m) ++
      (M, meshGap 1 m + r) :: (M, meshGap 1 m) :: meshTail M 1 m
      = (List.replicate (2 ^ m - 2) (M, meshGap 1 m) ++ [(M, meshGap 1 m + r)]) ++
        (M, meshGap 1 m) :: meshTail M 1 m by simp,
    gapSum_append, gapSum_append, gapSum_meshTail]
  simp only [gapSum] at h1 ⊢
  linarith

/-- The two-block hitting kernel `H^∪_m = p_{2+r} − Λ^∪_m`. -/
noncomputable def cupHitKer (M r : ℝ) (m : ℕ) : ℝ × ℝ → ℝ :=
  hitKerN (M, meshGap 1 m) (cupList M r m)

/-- **The two-block mesh kernel factors**: `Λ^∪_m = Λ_m ⋆ (P_r ⋆ Λ_m)`. -/
theorem lamKerN_cupList {M r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 1 ≤ m) :
    lamKerN (M, meshGap 1 m) (cupList M r m)
      = AiryConj.compKernel (meshLamKer M 1 m)
          (AiryConj.compKernel (AiryTwoInt.heatKerTwo r) (meshLamKer M 1 m)) := by
  have hg := meshGap_pos one_pos m
  have hrep : ∀ z ∈ List.replicate (2 ^ m - 2) (M, meshGap 1 m), 0 < z.2 := by
    intro z hz; rw [(List.mem_replicate.1 hz).2]; exact hg
  rw [cupList, show List.replicate (2 ^ m - 2) (M, meshGap 1 m) ++
      (M, meshGap 1 m + r) :: (M, meshGap 1 m) :: meshTail M 1 m
      = (List.replicate (2 ^ m - 2) (M, meshGap 1 m) ++ [(M, meshGap 1 m + r)]) ++
        (M, meshGap 1 m) :: meshTail M 1 m by simp]
  have hpre : ∀ z ∈ List.replicate (2 ^ m - 2) (M, meshGap 1 m) ++ [(M, meshGap 1 m + r)],
      0 < z.2 := by
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact hrep z hz
    · rw [List.mem_singleton.1 hz]; show 0 < meshGap 1 m + r; linarith
  rw [lamKerN_append _ _ _ _ hg hpre hg (meshTail_pos one_pos m),
    lamKerN_bump _ _ M hg hrep hg hr, replicate_append_meshTail hm]
  change AiryConj.compKernel (AiryConj.compKernel (meshLamKer M 1 m) (AiryTwoInt.heatKerTwo r))
      (meshLamKer M 1 m) = _
  exact compKernel_assoc_heat one_pos hr one_pos (meshLamKer_props one_pos m).1
    (AiryTwoInt.measurable_heatKerTwo r) (meshLamKer_props one_pos m).1
    (abs_meshLamKer_le one_pos m) (fun p => AiryTwoInt.heatKerTwo_abs_le_self hr p)
    (abs_meshLamKer_le one_pos m)

theorem cupHitKer_eq {M r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 1 ≤ m) (p : ℝ × ℝ) :
    cupHitKer M r m p = heatKernel (2 + r) (p.1 - p.2)
      - AiryConj.compKernel (meshLamKer M 1 m)
          (AiryConj.compKernel (AiryTwoInt.heatKerTwo r) (meshLamKer M 1 m)) p := by
  unfold cupHitKer hitKerN
  rw [gapSum_cupList M r hm, lamKerN_cupList hr hm]

/-- `D_r = P₁P_rP₁ − ΛP_rΛ = p_{2+r} − Λ ⋆ (P_r ⋆ Λ)`. -/
theorem dRKer_eq_heat_sub {M r : ℝ} (hr : 0 < r) (p : ℝ × ℝ) :
    AiryTwoInt.dRKer M r p = heatKernel (2 + r) (p.1 - p.2)
      - AiryConj.compKernel (AiryTwoInt.lamKerTwo M)
          (AiryConj.compKernel (AiryTwoInt.heatKerTwo r) (AiryTwoInt.lamKerTwo M)) p := by
  unfold AiryTwoInt.dRKer
  rw [AiryTwoInt.heatKerTwo_comp hr one_pos,
    AiryTwoInt.heatKerTwo_comp one_pos (by linarith : (0 : ℝ) < r + 1)]
  show heatKernel (1 + (r + 1)) (p.1 - p.2) - _ = _
  rw [show (1 : ℝ) + (r + 1) = 2 + r by ring]

/-! ## The two-block kernel limit -/

theorem measurable_compKernel_heat_meshLamKer (M r : ℝ) (m : ℕ) :
    Measurable (AiryConj.compKernel (AiryTwoInt.heatKerTwo r) (meshLamKer M 1 m)) :=
  AiryTwoInt.measurable_compKernel (AiryTwoInt.measurable_heatKerTwo r)
    (meshLamKer_props one_pos m).1

theorem abs_compKernel_heat_meshLamKer_le {M r : ℝ} (hr : 0 < r) (m : ℕ) (p : ℝ × ℝ) :
    |AiryConj.compKernel (AiryTwoInt.heatKerTwo r) (meshLamKer M 1 m) p|
      ≤ heatKernel (r + 1) (p.1 - p.2) :=
  abs_compKernel_le_heat hr one_pos (AiryTwoInt.measurable_heatKerTwo r)
    (meshLamKer_props one_pos m).1 (fun q => AiryTwoInt.heatKerTwo_abs_le_self hr q)
    (abs_meshLamKer_le one_pos m) p

theorem abs_compKernel_heat_lamKerTwo_le {M r : ℝ} (hr : 0 < r) (p : ℝ × ℝ) :
    |AiryConj.compKernel (AiryTwoInt.heatKerTwo r) (AiryTwoInt.lamKerTwo M) p|
      ≤ heatKernel (r + 1) (p.1 - p.2) :=
  abs_compKernel_le_heat hr one_pos (AiryTwoInt.measurable_heatKerTwo r)
    (AiryTwoInt.measurable_lamKerTwo M) (fun q => AiryTwoInt.heatKerTwo_abs_le_self hr q)
    (AiryTwoInt.lamKerTwo_abs_le M) p

/-- **Domination**: `H^∪_m ≤ D_r` a.e. (from `Λ ≤ Λ_m` a.e., by monotonicity of the
compositions). -/
theorem ae_cupHitKer_le_dRKer {M r : ℝ} (hr : 0 < r) (hK : MeshHittingLimit M 1) {m : ℕ}
    (hm : 1 ≤ m) :
    ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), cupHitKer M r m p ≤ AiryTwoInt.dRKer M r p := by
  have hinner : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
      AiryConj.compKernel (AiryTwoInt.heatKerTwo r) (AiryTwoInt.lamKerTwo M) p
        ≤ AiryConj.compKernel (AiryTwoInt.heatKerTwo r) (meshLamKer M 1 m) p :=
    ae_compKernel_mono hr one_pos (AiryTwoInt.measurable_heatKerTwo r)
      (AiryTwoInt.measurable_heatKerTwo r) (AiryTwoInt.measurable_lamKerTwo M)
      (meshLamKer_props one_pos m).1 (fun q => AiryTwoInt.heatKerTwo_abs_le_self hr q)
      (fun q => AiryTwoInt.heatKerTwo_abs_le_self hr q) (AiryTwoInt.lamKerTwo_abs_le M)
      (abs_meshLamKer_le one_pos m) (fun q => (heatKernel_pos hr _).le)
      (AiryTwoInt.lamKerTwo_nonneg M) (Eventually.of_forall fun _ => le_rfl)
      (ae_lamKerTwo_le_meshLamKer hK m)
  have houter := ae_compKernel_mono one_pos (by linarith : (0 : ℝ) < r + 1)
    (AiryTwoInt.measurable_lamKerTwo M) (meshLamKer_props one_pos m).1
    (AiryTwoInt.measurable_compKernel (AiryTwoInt.measurable_heatKerTwo r)
      (AiryTwoInt.measurable_lamKerTwo M))
    (measurable_compKernel_heat_meshLamKer M r m) (AiryTwoInt.lamKerTwo_abs_le M)
    (abs_meshLamKer_le one_pos m) (abs_compKernel_heat_lamKerTwo_le hr)
    (abs_compKernel_heat_meshLamKer_le hr m) (AiryTwoInt.lamKerTwo_nonneg M)
    (fun q => AiryTwoInt.compKernel_heatKerTwo_lamKerTwo_nonneg hr M q.1 q.2)
    (ae_lamKerTwo_le_meshLamKer hK m) hinner
  filter_upwards [houter] with p hp
  rw [cupHitKer_eq hr hm, dRKer_eq_heat_sub hr]
  linarith

/-- **Convergence**: `H^∪_{n+1} → D_r` a.e. -/
theorem ae_tendsto_cupHitKer {M r : ℝ} (hr : 0 < r) (hK : MeshHittingLimit M 1) :
    ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
      Tendsto (fun n => cupHitKer M r (n + 1) p) atTop (𝓝 (AiryTwoInt.dRKer M r p)) := by
  have hΛ : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
      Tendsto (fun n => meshLamKer M 1 (n + 1) p) atTop (𝓝 (AiryTwoInt.lamKerTwo M p)) := by
    filter_upwards [ae_tendsto_meshLamKer hK] with p hp
    exact hp.comp (tendsto_add_atTop_nat 1)
  have hinner := ae_tendsto_compKernel hr one_pos
    (A := fun _ => AiryTwoInt.heatKerTwo r) (A₀ := AiryTwoInt.heatKerTwo r)
    (B := fun n => meshLamKer M 1 (n + 1)) (B₀ := AiryTwoInt.lamKerTwo M)
    (fun _ => AiryTwoInt.measurable_heatKerTwo r) (fun n => (meshLamKer_props one_pos _).1)
    (fun _ q => AiryTwoInt.heatKerTwo_abs_le_self hr q) (fun n => abs_meshLamKer_le one_pos _)
    (Eventually.of_forall fun _ => tendsto_const_nhds) hΛ
  have houter := ae_tendsto_compKernel one_pos (by linarith : (0 : ℝ) < r + 1)
    (A := fun n => meshLamKer M 1 (n + 1)) (A₀ := AiryTwoInt.lamKerTwo M)
    (B := fun n => AiryConj.compKernel (AiryTwoInt.heatKerTwo r) (meshLamKer M 1 (n + 1)))
    (B₀ := AiryConj.compKernel (AiryTwoInt.heatKerTwo r) (AiryTwoInt.lamKerTwo M))
    (fun n => (meshLamKer_props one_pos _).1)
    (fun n => measurable_compKernel_heat_meshLamKer M r _)
    (fun n => abs_meshLamKer_le one_pos _) (fun n => abs_compKernel_heat_meshLamKer_le hr _)
    hΛ hinner
  filter_upwards [houter] with p hp
  have heq : (fun n => cupHitKer M r (n + 1) p) = fun n => heatKernel (2 + r) (p.1 - p.2)
      - AiryConj.compKernel (meshLamKer M 1 (n + 1))
          (AiryConj.compKernel (AiryTwoInt.heatKerTwo r) (meshLamKer M 1 (n + 1))) p := by
    funext n; exact cupHitKer_eq hr (by omega) p
  rw [heq, dRKer_eq_heat_sub hr]
  exact tendsto_const_nhds.sub hp

/-! ## The two-block operator and determinant convergence -/

theorem cupAdm {M r a : ℝ} (ha : r + 3 ≤ a) {m : ℕ} (hm : 1 ≤ m) :
    gapSum (M, meshGap 1 m) (cupList M r m) + 1 ≤ a := by
  rw [gapSum_cupList M r hm]; linarith

/-- **The two-block mesh fdd operator** `T_{V^∪_m} ∘ T_W` at weight `a ≥ r + 3`. -/
noncomputable def cupOp (M r : ℝ) (m : ℕ) (hr : 0 < r) (a : ℝ) (ha : r + 3 ≤ a) (hm : 1 ≤ m) :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  fddOpAt (M, meshGap 1 m) (cupList M r m) (meshGap_pos one_pos m) (cupList_pos hr.le m) a
    (cupAdm ha hm)

/-- `cupOp` with its `W` factor written as `wSKer (2 + r) a` — the `W` factor of `K̃∪`. -/
theorem cupOp_eq (M r : ℝ) (m : ℕ) (hr : 0 < r) (a : ℝ) (ha : r + 3 ≤ a) (hm : 1 ≤ m) :
    cupOp M r m hr a ha hm
      = kernelOperator (memLp_fddVKer (M, meshGap 1 m) (cupList M r m) (meshGap_pos one_pos m)
          (cupList_pos hr.le m) (a := a) (by linarith)) ∘L
        kernelOperator (AiryTwoInt.memLp_wSKer hr ha) := by
  unfold cupOp fddOpAt
  congr 1
  exact AiryTwoInt.kernelOperator_congr (by rw [gapSum_cupList M r hm]; rfl) _ _

/-- `K̃∪ = T_{Ṽ_{D,r}} ∘ T_{W_{2+r,a}}` as operators. -/
theorem kernelOperator_kcupKerT_eq {M r a : ℝ} (hr : 0 < r) (hM : 0 < M) (ha : r + 3 ≤ a) :
    kernelOperator (AiryTwoInt.memLp_kcupKerT hr hM ha)
      = kernelOperator (AiryTwoInt.memLp_vdRKer hr hM ha) ∘L
        kernelOperator (AiryTwoInt.memLp_wSKer hr ha) := by
  have hcomp : MemLp (AiryConj.compKernel (AiryTwoInt.vdRKer a M r) (AiryTwoInt.wSKer (2 + r) a))
      2 (volume.prod volume) :=
    (memLp_congr_ae (Eventually.of_forall fun p =>
      congrFun (AiryTwoInt.kcupKerT_eq_compKernel_vdRKer_wSKer a M r) p)).mp
      (AiryTwoInt.memLp_kcupKerT hr hM ha)
  rw [AiryTwoInt.kernelOperator_congr (AiryTwoInt.kcupKerT_eq_compKernel_vdRKer_wSKer a M r)
    (AiryTwoInt.memLp_kcupKerT hr hM ha) hcomp, AiryTwoInt.kernelOperator_compKernel _ _ hcomp]

/-- `Ṽ_{D,r}` is `fddVKer` of `D_r`. -/
theorem vdRKer_eq_fddVKer (a M r : ℝ) : AiryTwoInt.vdRKer a M r = fddVKer (AiryTwoInt.dRKer M r) a :=
  rfl

/-- **Kernel half of the two-block Step O**: `∫∫ (V^∪_{n+1} − Ṽ_{D,r})² → 0`. -/
theorem tendsto_integral_sq_cupVKer {M r a : ℝ} (hr : 0 < r) (hM : 0 < M) (ha : r + 3 ≤ a)
    (hK : MeshHittingLimit M 1) :
    Tendsto (fun n => ∫ p, (fddVKer (cupHitKer M r (n + 1)) a p
        - AiryTwoInt.vdRKer a M r p) ^ 2 ∂(volume.prod volume)) atTop (𝓝 0) := by
  have hV := AiryTwoInt.memLp_vdRKer hr hM ha
  have hint : Integrable (fun p => AiryTwoInt.vdRKer a M r p ^ 2) (volume.prod volume) :=
    hV.integrable_sq
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.prod volume)
    (l := atTop) (f := fun _ => (0 : ℝ)) (fun p => AiryTwoInt.vdRKer a M r p ^ 2)
    (F := fun n p => (fddVKer (cupHitKer M r (n + 1)) a p - AiryTwoInt.vdRKer a M r p) ^ 2)
    (Eventually.of_forall fun n =>
      (((measurable_fddVKer (measurable_hitKerN (meshGap_pos one_pos _)
        (cupList_pos hr.le _)) _).sub
        (AiryTwoInt.measurable_vdRKer a M r)).pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall fun n => by
      filter_upwards [ae_cupHitKer_le_dRKer hr hK (m := n + 1) (by omega)] with p hp
      rw [Real.norm_of_nonneg (sq_nonneg _), vdRKer_eq_fddVKer, fddVKer_eq_mul, fddVKer_eq_mul]
      exact sq_mul_sub_le_sq_mul _ _ _
        (hitKerN_nonneg (meshGap_pos one_pos _) (cupList_pos hr.le _) p) hp)
    hint
    (by
      filter_upwards [ae_tendsto_cupHitKer hr hK] with p hp
      have h1 : Tendsto (fun n => fddVKer (cupHitKer M r (n + 1)) a p) atTop
          (𝓝 (AiryTwoInt.vdRKer a M r p)) := by
        rw [vdRKer_eq_fddVKer, fddVKer_eq_mul]
        simp_rw [fddVKer_eq_mul]
        exact hp.const_mul _
      simpa using (h1.sub_const (AiryTwoInt.vdRKer a M r p)).pow 2)
  simpa using hlim

/-- **Two-block Step O.** Under the one-block kernel fact `MeshHittingLimit M 1`:
`det(I − cupOp_{n+1}) → det(I − K̃∪)` with `K̃∪ = kcupKerT a M r`, `r + 3 ≤ a`. -/
theorem tendsto_fredholmDet_cupOp {M r a : ℝ} (hr : 0 < r) (hM : 0 < M) (ha : r + 3 ≤ a)
    (hK : MeshHittingLimit M 1) :
    Tendsto (fun n => fredholmDet (cupOp M r (n + 1) hr a ha (by omega)) 1) atTop
      (𝓝 (fredholmDet (kernelOperator (AiryTwoInt.memLp_kcupKerT hr hM ha)) 1)) := by
  simp_rw [cupOp_eq M r _ hr a ha]
  rw [kernelOperator_kcupKerT_eq hr hM ha]
  exact tendsto_fredholmDet_kernelOperator_comp _ _ _ (tendsto_integral_sq_cupVKer hr hM ha hK) 1

/-! ## The two-block mesh fdd identity -/

theorem lt_of_mem_meshTimes {g : ℝ} (hg : 0 < g) {k : ℕ} {x t : ℝ}
    (ht : t ∈ meshTimes x g k) : t < x + k * g := by
  obtain ⟨i, hi, rfl⟩ := (mem_meshTimes k x t).1 ht
  have : (i : ℝ) < k := by exact_mod_cast hi
  nlinarith

theorem meshGap_mul_two_pow (m : ℕ) : (2 : ℝ) ^ m * meshGap 1 m = 1 := by
  unfold meshGap; field_simp

/-- The sorted union of the two block meshes is the concatenation of the two progressions. -/
theorem sort_cupSet (x r : ℝ) (hr : 0 < r) (m : ℕ) :
    (meshSet x 1 m ∪ meshSet (x + 1 + r) 1 m).sort (· ≤ ·)
      = meshTimes x (meshGap 1 m) (2 ^ m) ++ meshTimes (x + 1 + r) (meshGap 1 m) (2 ^ m) := by
  have hg := meshGap_pos one_pos m
  have hlt : (meshTimes x (meshGap 1 m) (2 ^ m)
      ++ meshTimes (x + 1 + r) (meshGap 1 m) (2 ^ m)).Pairwise (· < ·) := by
    refine List.pairwise_append.2 ⟨meshTimes_pairwise_lt hg _ _, meshTimes_pairwise_lt hg _ _,
      fun a ha b hb => ?_⟩
    have h1 := lt_of_mem_meshTimes hg ha
    have h2 := le_of_mem_meshTimes hg.le hb
    have h3 := meshGap_mul_two_pow m
    push_cast at h1
    linarith
  have hnd := hlt.imp fun h => h.ne
  have hle := hlt.imp fun h => h.le
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Finset.pairwise_sort _ _) hle ?_
  refine List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _) hnd ?_
  rw [Finset.sort_toFinset, List.toFinset_append]
  rfl

/-- The entries of a progression followed by a later time `y` at gap `g + r`. -/
theorem fddEntries_meshTimes_append {g M r : ℝ} (lev : ℝ → ℝ) (y : ℝ) (rest : List ℝ) :
    ∀ (k : ℕ) (x : ℝ), (∀ t ∈ meshTimes x g (k + 1), lev t = M) →
      y = x + k * g + (g + r) →
      fddEntries lev (meshTimes x g (k + 1) ++ y :: rest)
        = List.replicate k (M, g) ++ (M, g + r) :: fddEntries lev (y :: rest)
  | 0, x, h, hy => by
    have hx : lev x = M := h x List.mem_cons_self
    have hyx : y - x = g + r := by rw [hy]; push_cast; ring
    show (lev x, y - x) :: fddEntries lev (y :: rest) = _
    rw [hx, hyx]
    rfl
  | k + 1, x, h, hy => by
    have hx : lev x = M := h x List.mem_cons_self
    have ih := fddEntries_meshTimes_append (g := g) (M := M) (r := r) lev y rest k (x + g)
      (fun t ht => h t (List.mem_cons_of_mem _ ht)) (by rw [hy]; push_cast; ring)
    show (lev x, x + g - x) :: fddEntries lev (meshTimes (x + g) g (k + 1) ++ y :: rest) = _
    rw [ih, hx, add_sub_cancel_left, List.replicate_succ, List.cons_append]

/-- `SamePad` across a common prefix. -/
theorem samePad_append : ∀ (P : List (ℝ × ℝ)) (e y : ℝ × ℝ) (L : List (ℝ × ℝ)) (y' : ℝ × ℝ)
    (L' : List (ℝ × ℝ)), SamePad y L y' L' → SamePad e (P ++ y :: L) e (P ++ y' :: L')
  | [], _, _, _, _, _, h => ⟨rfl, h⟩
  | z :: P, _, y, L, y', L', h => ⟨rfl, samePad_append P z y L y' L' h⟩

/-- **Two-block mesh fdd identity.** At constant level `M` on the union of the dyadic meshes
`I_m(x)` and `I_m(x + 1 + r)` (`m ≥ 1`, `r > 0`):
`F_{I_m(x) ∪ I_m(x+1+r)}(M, …, M) = det(I − cupOp)` at any weight `a ≥ r + 3`. -/
theorem airy1FinCdf_cupSet (x M r : ℝ) (hr : 0 < r) {m : ℕ} (hm : 1 ≤ m) (a : ℝ)
    (ha : r + 3 ≤ a) :
    airy1FinCdf (meshSet x 1 m ∪ meshSet (x + 1 + r) 1 m) (fun _ => M)
      = fredholmDet (cupOp M r m hr a ha hm) 1 := by
  obtain ⟨k, hk⟩ := two_pow_eq_add_two hm
  set g := meshGap 1 m with hg_def
  have hg := meshGap_pos one_pos m
  set I := meshSet x 1 m ∪ meshSet (x + 1 + r) 1 m with hI
  set lev := levelFn I (fun _ => M) with hlev
  have hlevM : ∀ t ∈ I, lev t = M := fun t ht => by
    simp only [hlev, levelFn, ht, ↓reduceDIte]
  have hmem1 : ∀ t ∈ meshTimes x g (k + 1 + 1), t ∈ I := fun t ht => by
    rw [hI, Finset.mem_union]; left
    unfold meshSet; rw [List.mem_toFinset, hk]; exact ht
  have hmem2 : ∀ t ∈ meshTimes (x + 1 + r) g (k + 1 + 1), t ∈ I := fun t ht => by
    rw [hI, Finset.mem_union]; right
    unfold meshSet; rw [List.mem_toFinset, hk]; exact ht
  have h2g : ((k : ℝ) + 2) * g = 1 := by
    have := meshGap_mul_two_pow m
    have hk' : (2 : ℝ) ^ m = k + 2 := by exact_mod_cast hk
    rw [hk'] at this; linarith
  have happ := fddEntries_meshTimes_append (M := M) (r := r) lev (x + 1 + r)
    (meshTimes (x + 1 + r + g) g (k + 1)) (k + 1) x (fun t ht => hlevM t (hmem1 t ht))
    (by push_cast; linarith)
  obtain ⟨e₂, L₂, hEL, hsp⟩ := fddEntries_meshTimes (M := M) (g := g) lev (k + 1) (x + 1 + r)
    (fun t ht => hlevM t (hmem2 t ht))
  have hfin : finEntries I (fun _ => M)
      = (M, g) :: (List.replicate k (M, g) ++ (M, g + r) :: e₂ :: L₂) := by
    unfold finEntries
    rw [← hlev, sort_cupSet x r hr m, hk]
    show fddEntries lev (meshTimes x g (k + 1 + 1) ++ meshTimes (x + 1 + r) g (k + 1 + 1)) = _
    rw [show meshTimes (x + 1 + r) g (k + 1 + 1)
        = (x + 1 + r) :: meshTimes (x + 1 + r + g) g (k + 1) from rfl, happ,
      show (x + 1 + r) :: meshTimes (x + 1 + r + g) g (k + 1)
        = meshTimes (x + 1 + r) g (k + 1 + 1) from rfl, hEL, List.replicate_succ,
      List.cons_append]
  have hcup : cupList M r m
      = List.replicate k (M, g) ++ (M, g + r) :: (M, g) :: List.replicate (k + 1) (M, g) := by
    rw [cupList, meshTail, hk]
    rfl
  have hsp' : SamePad (M, g) (List.replicate k (M, g) ++ (M, g + r) :: e₂ :: L₂)
      (M, g) (cupList M r m) := by
    rw [hcup]
    exact samePad_append _ _ _ _ _ _ ⟨rfl, hsp⟩
  unfold cupOp
  exact airy1FinCdf_eq_fredholmDet_fddOpAt _ _ hfin hsp' _ _ _

/-- **Combined.** Under the one-block dyadic hitting-kernel limit
`MeshHittingLimit M 1`, `M > 0`, `r > 0`, `r + 3 ≤ a`, for every base point `x`:
`F_{I_{n+1}(x) ∪ I_{n+1}(x+1+r)}(M, …, M) → det(I − K̃∪)`, `K̃∪ = kcupKerT a M r`. -/
theorem tendsto_airy1FinCdf_cupSet (x : ℝ) {M r a : ℝ} (hr : 0 < r) (hM : 0 < M)
    (ha : r + 3 ≤ a) (hK : MeshHittingLimit M 1) :
    Tendsto (fun n => airy1FinCdf (meshSet x 1 (n + 1) ∪ meshSet (x + 1 + r) 1 (n + 1))
        (fun _ => M)) atTop
      (𝓝 (fredholmDet (kernelOperator (AiryTwoInt.memLp_kcupKerT hr hM ha)) 1)) := by
  have heq : (fun n => airy1FinCdf (meshSet x 1 (n + 1) ∪ meshSet (x + 1 + r) 1 (n + 1))
      (fun _ => M)) = fun n => fredholmDet (cupOp M r (n + 1) hr a ha (by omega)) 1 := by
    funext n
    exact airy1FinCdf_cupSet x M r hr (by omega) a ha
  rw [heq]
  exact tendsto_fredholmDet_cupOp hr hM ha hK

end AiryFdd
