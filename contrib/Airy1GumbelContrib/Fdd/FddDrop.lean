/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Fdd.FddCont
import Airy1GumbelContrib.Fdd.FddIndep

/-!
# Dropping a time from the fdd determinant

`Fdd/FddCont.lean` shows that if the levels
converge in `EReal` (limits `≠ ⊥`), the fdd determinant converges to the determinant built
from the extended-level kernel, in which a level `+∞` removes that time's projection
(`P̄_{+∞} = I`).  Here that limit is identified with the determinant of the shorter list.

* Time-list kernels `lamKerT lev τ ts` / `hitKerT` (levels as a function of time, gaps
  `gapsOfP τ ts`, padding `τ`), bridged to FddCont's `lamKerZ` and to FddKernel's `hitKerN`.
* **Interior or last time** (`lamKerT_erase`): a `⊤` level at a non-first time merges the two
  adjacent heat factors (Chapman–Kolmogorov, `compKernel_heat_heat_assoc`); the total time is
  unchanged, the padding changes only when the last time is dropped (then padding and weight
  independence, `Fdd/FddIndep.lean`).
* **First time** (`hitKerT_head_top`, `fredholmDet_swap_heat`): `H_n = p_{g₁} ⋆ H_{n−1}`, and
  `W_S ∘ V_n = W_{S−g₁} ∘ V_{n−1}` at the kernel level (`compKernel_wKernel_fddVKer_heat`:
  `g_S ⋆ p_{g₁} = g_{S−g₁}`); then `fredholmDet_comp_comm` twice and weight independence.
* **All levels** `⊤`: `lamKerT = p_S`, so `H = 0` and the determinant is `1`.

Finset forms: `tendsto_airy1FinCdf_erase` (headline: for any `t ∈ I`, `x_t → +∞` with the other
levels converging gives `F_I → F_{I∖{t}}`), `tendsto_airy1FinCdf_one` (all levels `→ +∞`).
-/

namespace AiryFdd

open MeasureTheory Real Set Filter Topology
open HilbertSchmidt

/-! ## Heat-kernel algebra -/

theorem heatKerTwo_comp_heatKerTwo {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    AiryConj.compKernel (AiryTwoInt.heatKerTwo s) (AiryTwoInt.heatKerTwo t)
      = AiryTwoInt.heatKerTwo (s + t) := by
  funext p
  exact AiryTwoInt.heatKernel_conv hs ht p.1 p.2

/-- Chapman–Kolmogorov against a heat-dominated kernel: `p_s ⋆ (p_t ⋆ R) = p_{s+t} ⋆ R`. -/
theorem compKernel_heat_heat_assoc {s t T : ℝ} (hs : 0 < s) (ht : 0 < t) (hT : 0 < T)
    {R : ℝ × ℝ → ℝ} (hRm : Measurable R) (hR : ∀ p, |R p| ≤ heatKernel T (p.1 - p.2)) :
    AiryConj.compKernel (AiryTwoInt.heatKerTwo s)
        (AiryConj.compKernel (AiryTwoInt.heatKerTwo t) R)
      = AiryConj.compKernel (AiryTwoInt.heatKerTwo (s + t)) R := by
  funext p
  obtain ⟨u, v⟩ := p
  have hInt := AiryTwoInt.integrable_uncurry_of_abs_le hs ht le_rfl u
    (AiryTwoInt.measurable_heatKerTwo s) (fun z => AiryTwoInt.heatKerTwo_abs_le_self hs (u, z))
    (AiryTwoInt.measurable_heatKerTwo t)
    (fun z₁ z₂ => AiryTwoInt.heatKerTwo_abs_le_self ht (z₁, z₂))
    (φ := fun z => R (z, v)) (hRm.comp (measurable_id.prodMk measurable_const)) (c0 T)
    (fun z => by
      rw [zero_mul, Real.exp_zero, mul_one]
      exact (hR (z, v)).trans (AiryTwoInt.heatKernel_le hT _))
  rw [← AiryTwoInt.compKernel_assoc u v hInt, heatKerTwo_comp_heatKerTwo hs ht]

/-- `g_S ⋆ p_g = g_{S−g}` (heat acting on the second slot of the backward Airy kernel). -/
theorem bAiryKer_comp_heatKerTwo {g : ℝ} (hg : 0 < g) (S : ℝ) :
    AiryConj.compKernel (AiryTwoInt.bAiryKer S) (AiryTwoInt.heatKerTwo g)
      = AiryTwoInt.bAiryKer (S - g) := by
  funext p
  obtain ⟨z, w⟩ := p
  have h := congrFun (AiryTwoInt.heatKerTwo_comp_bAiryKer_any hg S) (w, z)
  show ∫ u : ℝ, backwardAiry S (z + u) * heatKernel g (u - w) = backwardAiry (S - g) (z + w)
  have h' : ∫ u : ℝ, heatKernel g (w - u) * backwardAiry S (u + z)
      = backwardAiry (S - g) (w + z) := h
  rw [add_comm z w, ← h']
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [show u - w = -(w - u) by ring, AiryTwoInt.heatKernel_even, add_comm z u, mul_comm]

/-- The weights of `W ⋆ V` factor out: `(W_{S,a} ⋆ V_{K,a})(z, v)
= φ(z)⁻¹ e^{az} e^{−av} φ(v) ∫ g_S(z + u) K(u, v) du`. -/
theorem compKernel_wKernel_fddVKer (S a : ℝ) (K : ℝ × ℝ → ℝ) (z v : ℝ) :
    AiryConj.compKernel (AiryConj.wKernel S a) (fddVKer K a) (z, v)
      = (AiryConj.phiWeight z)⁻¹ * Real.exp (a * z) * Real.exp (-a * v) * AiryConj.phiWeight v
        * AiryConj.compKernel (AiryTwoInt.bAiryKer S) K (z, v) := by
  show ∫ u : ℝ, AiryConj.wKernel S a (z, u) * fddVKer K a (u, v)
    = _ * ∫ u : ℝ, backwardAiry S (z + u) * K (u, v)
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e : Real.exp (a * u) * Real.exp (-a * u) = 1 := by
    rw [← Real.exp_add, show a * u + -a * u = 0 by ring, Real.exp_zero]
  simp only [AiryConj.wKernel, fddVKer]
  calc (AiryConj.phiWeight z)⁻¹ * Real.exp (a * z) * backwardAiry S (z + u) * Real.exp (a * u)
        * (Real.exp (-a * u) * K (u, v) * Real.exp (-a * v) * AiryConj.phiWeight v)
      = (AiryConj.phiWeight z)⁻¹ * Real.exp (a * z) * Real.exp (-a * v)
          * AiryConj.phiWeight v * (backwardAiry S (z + u) * K (u, v))
          * (Real.exp (a * u) * Real.exp (-a * u)) := by ring
    _ = _ := by rw [e, mul_one]

/-- **The first-time kernel identity** (first-time drop): `W_S ⋆ V_{p_g ⋆ H} = W_{S−g} ⋆ V_H`. -/
theorem compKernel_wKernel_fddVKer_heat {S g T a : ℝ} (hg : 0 < g) (hT : 0 < T) (hgS : g ≤ S)
    {H : ℝ × ℝ → ℝ} (hHm : Measurable H) (hH : ∀ p, |H p| ≤ heatKernel T (p.1 - p.2)) :
    AiryConj.compKernel (AiryConj.wKernel S a)
        (fddVKer (AiryConj.compKernel (AiryTwoInt.heatKerTwo g) H) a)
      = AiryConj.compKernel (AiryConj.wKernel (S - g) a) (fddVKer H a) := by
  funext p
  obtain ⟨z, v⟩ := p
  rw [compKernel_wKernel_fddVKer, compKernel_wKernel_fddVKer]
  congr 1
  obtain ⟨C, hC⟩ := AiryTwoInt.bAiryKer_abs_le_exp (by linarith : (0 : ℝ) ≤ S) z
  have hG := AiryTwoInt.integrable_uncurry_of_abs_le hT hg (c := S) (by linarith) v
    (A := fun q => H (q.2, q.1)) (hHm.comp measurable_swap)
    (fun w => by
      show |H (w, v)| ≤ heatKernel T (v - w)
      rw [show v - w = -(w - v) by ring, AiryTwoInt.heatKernel_even]
      exact hH (w, v))
    (B := fun q => AiryTwoInt.heatKerTwo g (q.2, q.1))
    ((AiryTwoInt.measurable_heatKerTwo g).comp measurable_swap)
    (fun z₁ z₂ => by
      show |heatKernel g (z₂ - z₁)| ≤ heatKernel g (z₁ - z₂)
      rw [abs_of_nonneg (heatKernel_pos hg _).le, show z₂ - z₁ = -(z₁ - z₂) by ring,
        AiryTwoInt.heatKernel_even])
    (φ := fun u => AiryTwoInt.bAiryKer S (z, u))
    ((AiryTwoInt.continuous_bAiryKer S).measurable.comp
      (measurable_const.prodMk measurable_id)) C
    (fun u => by
      have := hC u
      simp only [AiryTwoInt.bAiryKer] at this ⊢
      rwa [add_comm z u])
  have hInt : Integrable (Function.uncurry fun z₁ z₂ : ℝ => AiryTwoInt.bAiryKer S (z, z₁)
      * (AiryTwoInt.heatKerTwo g (z₁, z₂) * H (z₂, v))) (volume.prod volume) := by
    refine hG.swap.congr (Eventually.of_forall fun q => ?_)
    obtain ⟨u, w⟩ := q
    simp only [Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]
    ring
  rw [← AiryTwoInt.compKernel_assoc z v hInt, bAiryKer_comp_heatKerTwo hg S]

/-- **First-time determinant identity**: `det(1 − z V_{p_g⋆H} W_S) = det(1 − z V_H W_{S−g})`
(cyclicity twice around the kernel identity). -/
theorem fredholmDet_swap_heat {S g T a : ℝ} (hg : 0 < g) (hT : 0 < T) (hgS : g ≤ S)
    {H : ℝ × ℝ → ℝ} (hHm : Measurable H) (hH : ∀ p, |H p| ≤ heatKernel T (p.1 - p.2))
    (hV : MemLp (fddVKer (AiryConj.compKernel (AiryTwoInt.heatKerTwo g) H) a) 2
      (volume.prod volume))
    (hW : MemLp (AiryConj.wKernel S a) 2 (volume.prod volume))
    (hV' : MemLp (fddVKer H a) 2 (volume.prod volume))
    (hW' : MemLp (AiryConj.wKernel (S - g) a) 2 (volume.prod volume)) (z : ℝ) :
    fredholmDet (kernelOperator hV ∘L kernelOperator hW) z
      = fredholmDet (kernelOperator hV' ∘L kernelOperator hW') z := by
  rw [fredholmDet_comp_comm (isHilbertSchmidt_kernelOperator hV)
      (isHilbertSchmidt_kernelOperator hW),
    fredholmDet_comp_comm (isHilbertSchmidt_kernelOperator hV')
      (isHilbertSchmidt_kernelOperator hW')]
  have hVm : Measurable (fddVKer (AiryConj.compKernel (AiryTwoInt.heatKerTwo g) H) a) :=
    measurable_fddVKer (AiryTwoInt.measurable_compKernel (AiryTwoInt.measurable_heatKerTwo g)
      hHm) a
  have hc := AiryTwoInt.memLp_compKernel (AiryConj.continuous_wKernel S a).measurable hVm hW hV
  have hc' := AiryTwoInt.memLp_compKernel (AiryConj.continuous_wKernel (S - g) a).measurable
    (measurable_fddVKer hHm a) hW' hV'
  rw [← AiryTwoInt.kernelOperator_compKernel hW hV hc,
    ← AiryTwoInt.kernelOperator_compKernel hW' hV' hc']
  congr 1
  exact AiryTwoInt.kernelOperator_congr (compKernel_wKernel_fddVKer_heat hg hT hgS hHm hH) _ _

/-! ## Time-list kernels -/

/-- Gaps of a time list with padding `τ` after the last time. -/
def gapsOfP (τ : ℝ) : List ℝ → List ℝ
  | [] => []
  | [_] => [τ]
  | t :: s :: L => (s - t) :: gapsOfP τ (s :: L)

theorem gapsOf_eq_gapsOfP : ∀ ts : List ℝ, gapsOf ts = gapsOfP 1 ts
  | [] => rfl
  | [_] => rfl
  | t :: s :: L => by rw [gapsOf, gapsOfP, gapsOf_eq_gapsOfP (s :: L)]

theorem gapsOfP_cons (τ a : ℝ) (rest : List ℝ) : ∃ g gs, gapsOfP τ (a :: rest) = g :: gs := by
  cases rest <;> exact ⟨_, _, rfl⟩

theorem gapsOfP_pos {τ : ℝ} (hτ : 0 < τ) : ∀ ts : List ℝ, ts.Pairwise (· < ·) →
    ∀ c ∈ gapsOfP τ ts, 0 < c
  | [], _, c, hc => by simp [gapsOfP] at hc
  | [_], _, c, hc => by
    simp only [gapsOfP, List.mem_singleton] at hc
    rw [hc]; exact hτ
  | t :: s :: L, hp, c, hc => by
    simp only [gapsOfP, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact sub_pos.2 ((List.pairwise_cons.1 hp).1 s List.mem_cons_self)
    · exact gapsOfP_pos hτ (s :: L) (List.pairwise_cons.1 hp).2 c (by simpa [gapsOfP] using hc)

/-- Levels by position from levels by time. -/
def lvE (lev : ℝ → EReal) (ts : List ℝ) (i : ℕ) : EReal := lev (ts.getD i 0)

/-- `Λ e^{τΔ}` over a time list with extended levels `lev` (a function of time). -/
noncomputable def lamKerT (lev : ℝ → EReal) (τ : ℝ) : List ℝ → ℝ × ℝ → ℝ
  | [] => fun _ => 0
  | [a] => fun p => (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1 * heatKernel τ (p.1 - p.2)
  | a :: b :: rest => fun p => (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1
      * AiryConj.compKernel (AiryTwoInt.heatKerTwo (b - a)) (lamKerT lev τ (b :: rest)) p

/-- The hitting kernel over a time list. -/
noncomputable def hitKerT (lev : ℝ → EReal) (τ : ℝ) (ts : List ℝ) (p : ℝ × ℝ) : ℝ :=
  heatKernel (gapsOfP τ ts).sum (p.1 - p.2) - lamKerT lev τ ts p

/-- Bridge to the position-indexed kernel of `FddCont`. -/
theorem lamKerZ_lvE (lev : ℝ → EReal) (τ : ℝ) : ∀ (rest : List ℝ) (a g : ℝ) (gs : List ℝ),
    gapsOfP τ (a :: rest) = g :: gs → lamKerZ (lvE lev (a :: rest)) g gs = lamKerT lev τ (a :: rest)
  | [], a, g, gs, h => by
    simp only [gapsOfP, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | b :: rest, a, g, gs, h => by
    simp only [gapsOfP, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨g', gs', hg'⟩ := gapsOfP_cons τ b rest
    have IH := lamKerZ_lvE lev τ rest b g' gs' hg'
    rw [hg']
    funext p
    show (levSet (lvE lev (a :: b :: rest) 0)).indicator (fun _ => (1 : ℝ)) p.1
        * AiryConj.compKernel (AiryTwoInt.heatKerTwo (b - a))
          (lamKerZ (fun i => lvE lev (a :: b :: rest) (i + 1)) g' gs') p
      = (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1
        * AiryConj.compKernel (AiryTwoInt.heatKerTwo (b - a)) (lamKerT lev τ (b :: rest)) p
    have hx : (fun i => lvE lev (a :: b :: rest) (i + 1)) = lvE lev (b :: rest) :=
      funext fun i => by simp [lvE]
    rw [hx, IH]
    rfl

theorem hitKerZ_lvE (lev : ℝ → EReal) (τ : ℝ) (rest : List ℝ) (a g : ℝ) (gs : List ℝ)
    (h : gapsOfP τ (a :: rest) = g :: gs) :
    hitKerZ (lvE lev (a :: rest)) g gs = hitKerT lev τ (a :: rest) := by
  funext p
  unfold hitKerZ hitKerT
  rw [lamKerZ_lvE lev τ rest a g gs h, h, List.sum_cons]

theorem lamKerT_props (lev : ℝ → EReal) {τ : ℝ} (hτ : 0 < τ) (a : ℝ) (rest : List ℝ)
    (hp : (a :: rest).Pairwise (· < ·)) :
    Measurable (lamKerT lev τ (a :: rest)) ∧ (∀ p, 0 ≤ lamKerT lev τ (a :: rest) p) ∧
      (∀ p, lamKerT lev τ (a :: rest) p
        ≤ heatKernel (gapsOfP τ (a :: rest)).sum (p.1 - p.2)) := by
  obtain ⟨g, gs, h⟩ := gapsOfP_cons τ a rest
  have hpos := gapsOfP_pos hτ (a :: rest) hp
  rw [h] at hpos
  rw [← lamKerZ_lvE lev τ rest a g gs h, h, List.sum_cons]
  exact lamKerZ_props gs g _ (hpos g List.mem_cons_self)
    (fun c hc => hpos c (List.mem_cons_of_mem _ hc))

theorem gapsOfP_sum_pos {τ : ℝ} (hτ : 0 < τ) (a : ℝ) (rest : List ℝ)
    (hp : (a :: rest).Pairwise (· < ·)) : 0 < (gapsOfP τ (a :: rest)).sum := by
  obtain ⟨g, gs, h⟩ := gapsOfP_cons τ a rest
  have hpos := gapsOfP_pos hτ (a :: rest) hp
  rw [h] at hpos ⊢
  have := gapSum_pos (zipLev (fun _ => 0) gs) (0, g) (hpos g List.mem_cons_self)
    (zipLev_pos (fun c hc => hpos c (List.mem_cons_of_mem _ hc)) _)
  rwa [gapSum_zipLev, ← List.sum_cons] at this

theorem abs_lamKerT_le (lev : ℝ → EReal) {τ : ℝ} (hτ : 0 < τ) (a : ℝ) (rest : List ℝ)
    (hp : (a :: rest).Pairwise (· < ·)) (p : ℝ × ℝ) :
    |lamKerT lev τ (a :: rest) p| ≤ heatKernel (gapsOfP τ (a :: rest)).sum (p.1 - p.2) := by
  obtain ⟨-, h0, h1⟩ := lamKerT_props lev hτ a rest hp
  rw [abs_of_nonneg (h0 p)]
  exact h1 p

/-- Only the levels at the listed times matter. -/
theorem lamKerT_congr {lev lev' : ℝ → EReal} (τ : ℝ) : ∀ ts : List ℝ,
    (∀ s ∈ ts, lev s = lev' s) → lamKerT lev τ ts = lamKerT lev' τ ts
  | [], _ => rfl
  | [a], h => by
    funext p
    show (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1 * heatKernel τ (p.1 - p.2)
      = (levSet (lev' a)).indicator (fun _ => (1 : ℝ)) p.1 * heatKernel τ (p.1 - p.2)
    rw [h a List.mem_cons_self]
  | a :: b :: rest, h => by
    funext p
    show (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1
        * AiryConj.compKernel (AiryTwoInt.heatKerTwo (b - a)) (lamKerT lev τ (b :: rest)) p
      = (levSet (lev' a)).indicator (fun _ => (1 : ℝ)) p.1
        * AiryConj.compKernel (AiryTwoInt.heatKerTwo (b - a)) (lamKerT lev' τ (b :: rest)) p
    rw [h a List.mem_cons_self,
      lamKerT_congr τ (b :: rest) fun s hs => h s (List.mem_cons_of_mem _ hs)]

theorem hitKerT_congr {lev lev' : ℝ → EReal} (τ : ℝ) (ts : List ℝ)
    (h : ∀ s ∈ ts, lev s = lev' s) : hitKerT lev τ ts = hitKerT lev' τ ts := by
  funext p
  unfold hitKerT
  rw [lamKerT_congr τ ts h]

/-- Real levels: the time-list hitting kernel is FddKernel's `hitKerN`. -/
theorem hitKerT_coe (lev : ℝ → ℝ) (τ : ℝ) (a : ℝ) (rest : List ℝ) {g : ℝ} {gs : List ℝ}
    (h : gapsOfP τ (a :: rest) = g :: gs) :
    hitKerT (fun s => (lev s : EReal)) τ (a :: rest)
      = hitKerN (lev ((a :: rest).getD 0 0), g)
          (zipLev (fun i => lev ((a :: rest).getD (i + 1) 0)) gs) := by
  rw [← hitKerZ_coe gs g (fun i => lev ((a :: rest).getD i 0)),
    ← hitKerZ_lvE (fun s => (lev s : EReal)) τ rest a g gs h]
  rfl

theorem levSet_top_indicator (u : ℝ) : (levSet ⊤).indicator (fun _ => (1 : ℝ)) u = 1 := by
  rw [levSet_top, Set.indicator_univ]

/-- **All levels `⊤`**: `Λ e^{τΔ} = p_S` (Chapman–Kolmogorov). -/
theorem lamKerT_all_top {lev : ℝ → EReal} {τ : ℝ} (hτ : 0 < τ) : ∀ (rest : List ℝ) (a : ℝ),
    (a :: rest).Pairwise (· < ·) → (∀ s ∈ a :: rest, lev s = ⊤) →
    lamKerT lev τ (a :: rest) = AiryTwoInt.heatKerTwo (gapsOfP τ (a :: rest)).sum
  | [], a, _, h => by
    funext p
    show (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1 * heatKernel τ (p.1 - p.2)
      = heatKernel ([τ] : List ℝ).sum (p.1 - p.2)
    rw [h a List.mem_cons_self, levSet_top_indicator, one_mul, List.sum_singleton]
  | b :: rest, a, hp, h => by
    have hab : 0 < b - a := sub_pos.2 ((List.pairwise_cons.1 hp).1 b List.mem_cons_self)
    have hp' := (List.pairwise_cons.1 hp).2
    have IH := lamKerT_all_top hτ rest b hp' fun s hs => h s (List.mem_cons_of_mem _ hs)
    have hS := gapsOfP_sum_pos hτ b rest hp'
    funext p
    show (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1
        * AiryConj.compKernel (AiryTwoInt.heatKerTwo (b - a)) (lamKerT lev τ (b :: rest)) p
      = AiryTwoInt.heatKerTwo ((b - a) :: gapsOfP τ (b :: rest)).sum p
    rw [h a List.mem_cons_self, levSet_top_indicator, one_mul, IH,
      heatKerTwo_comp_heatKerTwo hab hS, List.sum_cons]

theorem hitKerT_all_top {lev : ℝ → EReal} {τ : ℝ} (hτ : 0 < τ) (rest : List ℝ) (a : ℝ)
    (hp : (a :: rest).Pairwise (· < ·)) (h : ∀ s ∈ a :: rest, lev s = ⊤) :
    hitKerT lev τ (a :: rest) = 0 := by
  funext p
  unfold hitKerT
  rw [lamKerT_all_top hτ rest a hp h]
  exact sub_self _

/-- **Kernel collapse (interior or last time)**: a `⊤` level at a non-first time merges the
adjacent gaps; the
total time is unchanged and the padding changes only if the last time is dropped. -/
theorem lamKerT_erase (lev : ℝ → EReal) {t : ℝ} (ht : lev t = ⊤) : ∀ (rest : List ℝ)
    (a b τ : ℝ), 0 < τ → (a :: b :: rest).Pairwise (· < ·) → t ∈ b :: rest →
    ∃ τ' : ℝ, 0 < τ' ∧
      (gapsOfP τ' (a :: (b :: rest).erase t)).sum = (gapsOfP τ (a :: b :: rest)).sum ∧
      lamKerT lev τ' (a :: (b :: rest).erase t) = lamKerT lev τ (a :: b :: rest) := by
  intro rest
  induction rest with
  | nil =>
    intro a b τ hτ hp hmem
    have htb : t = b := List.mem_singleton.1 hmem
    subst htb
    have hab : 0 < t - a := sub_pos.2 ((List.pairwise_cons.1 hp).1 t List.mem_cons_self)
    rw [List.erase_cons_head]
    refine ⟨t - a + τ, by linarith, by simp [gapsOfP], ?_⟩
    have hl : lamKerT lev τ [t] = AiryTwoInt.heatKerTwo τ := by
      funext q
      show (levSet (lev t)).indicator (fun _ => (1 : ℝ)) q.1 * heatKernel τ (q.1 - q.2) = _
      rw [ht, levSet_top_indicator, one_mul]
      rfl
    funext p
    show (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1 * heatKernel (t - a + τ) (p.1 - p.2)
      = (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1
        * AiryConj.compKernel (AiryTwoInt.heatKerTwo (t - a)) (lamKerT lev τ [t]) p
    rw [hl, heatKerTwo_comp_heatKerTwo hab hτ]
    rfl
  | cons c rest' IH =>
    intro a b τ hτ hp hmem
    have hab : 0 < b - a := sub_pos.2 ((List.pairwise_cons.1 hp).1 b List.mem_cons_self)
    have hp' := (List.pairwise_cons.1 hp).2
    have hbc : 0 < c - b := sub_pos.2 ((List.pairwise_cons.1 hp').1 c List.mem_cons_self)
    have hp'' := (List.pairwise_cons.1 hp').2
    by_cases htb : t = b
    · subst htb
      rw [List.erase_cons_head]
      refine ⟨τ, hτ, by simp [gapsOfP]; ring, ?_⟩
      have hl : lamKerT lev τ (t :: c :: rest')
          = AiryConj.compKernel (AiryTwoInt.heatKerTwo (c - t)) (lamKerT lev τ (c :: rest')) := by
        funext q
        show (levSet (lev t)).indicator (fun _ => (1 : ℝ)) q.1
            * AiryConj.compKernel (AiryTwoInt.heatKerTwo (c - t)) (lamKerT lev τ (c :: rest')) q
          = _
        rw [ht, levSet_top_indicator, one_mul]
      funext p
      show (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1
          * AiryConj.compKernel (AiryTwoInt.heatKerTwo (c - a)) (lamKerT lev τ (c :: rest')) p
        = (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1
          * AiryConj.compKernel (AiryTwoInt.heatKerTwo (t - a)) (lamKerT lev τ (t :: c :: rest')) p
      rw [hl, compKernel_heat_heat_assoc hab hbc (gapsOfP_sum_pos hτ c rest' hp'')
        (lamKerT_props lev hτ c rest' hp'').1 (abs_lamKerT_le lev hτ c rest' hp''),
        show t - a + (c - t) = c - a by ring]
    · have hmem' : t ∈ c :: rest' := by
        rcases List.mem_cons.1 hmem with h | h
        · exact absurd h htb
        · exact h
      obtain ⟨τ', hτ', hsum, hEq⟩ := IH b c τ hτ hp' hmem'
      have he : (b :: c :: rest').erase t = b :: (c :: rest').erase t := by
        rw [List.erase_cons]
        simp [beq_iff_eq, Ne.symm htb]
      refine ⟨τ', hτ', ?_, ?_⟩
      · rw [he]
        show ((b - a) :: gapsOfP τ' (b :: (c :: rest').erase t)).sum
          = ((b - a) :: gapsOfP τ (b :: c :: rest')).sum
        rw [List.sum_cons, List.sum_cons, hsum]
      · rw [he]
        funext p
        show (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1
            * AiryConj.compKernel (AiryTwoInt.heatKerTwo (b - a))
              (lamKerT lev τ' (b :: (c :: rest').erase t)) p
          = (levSet (lev a)).indicator (fun _ => (1 : ℝ)) p.1
            * AiryConj.compKernel (AiryTwoInt.heatKerTwo (b - a))
              (lamKerT lev τ (b :: c :: rest')) p
        rw [hEq]

/-- **Kernel identity (first time)**: a `⊤` level at the first time gives `H_n = p_{g₁} ⋆ H_{n−1}`.
-/
theorem hitKerT_head_top {lev : ℝ → EReal} {τ : ℝ} (hτ : 0 < τ) (a b : ℝ) (rest : List ℝ)
    (hp : (a :: b :: rest).Pairwise (· < ·)) (ha : lev a = ⊤) :
    hitKerT lev τ (a :: b :: rest)
      = AiryConj.compKernel (AiryTwoInt.heatKerTwo (b - a)) (hitKerT lev τ (b :: rest)) := by
  have hab : 0 < b - a := sub_pos.2 ((List.pairwise_cons.1 hp).1 b List.mem_cons_self)
  have hp' := (List.pairwise_cons.1 hp).2
  have hS' := gapsOfP_sum_pos hτ b rest hp'
  obtain ⟨hm, h0, h1⟩ := lamKerT_props lev hτ b rest hp'
  funext p
  obtain ⟨u, v⟩ := p
  have i2 : Integrable fun w : ℝ => heatKernel (b - a) (u - w) * lamKerT lev τ (b :: rest) (w, v) :=
    AiryTwoInt.integrable_pair_mul_of_heatKernel_le hab hS' (AiryTwoInt.measurable_heatKerTwo _)
      hm (fun x z => AiryTwoInt.heatKerTwo_abs_le_self hab (x, z))
      (fun x z => by rw [abs_of_nonneg (h0 _)]; exact h1 (x, z)) u v
  show heatKernel ((b - a) :: gapsOfP τ (b :: rest)).sum (u - v)
      - (levSet (lev a)).indicator (fun _ => (1 : ℝ)) u
        * ∫ w : ℝ, heatKernel (b - a) (u - w) * lamKerT lev τ (b :: rest) (w, v)
    = ∫ w : ℝ, heatKernel (b - a) (u - w)
        * (heatKernel (gapsOfP τ (b :: rest)).sum (w - v) - lamKerT lev τ (b :: rest) (w, v))
  rw [ha, levSet_top_indicator, one_mul, List.sum_cons,
    ← AiryTwoInt.heatKernel_conv hab hS' u v,
    ← integral_sub (integrable_heat_mul_heat hab hS' u v) i2]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  ring

/-! ## Finset bookkeeping -/

theorem sort_lt (I : Finset ℝ) : (I.sort (· ≤ ·)).Pairwise (· < ·) :=
  ((Finset.pairwise_sort I _).and (Finset.sort_nodup I _)).imp fun h => lt_of_le_of_ne h.1 h.2

theorem sort_erase (I : Finset ℝ) (t : ℝ) :
    (I.erase t).sort (· ≤ ·) = (I.sort (· ≤ ·)).erase t := by
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Finset.pairwise_sort _ _)
    (List.Pairwise.sublist (List.erase_sublist) (Finset.pairwise_sort I _)) ?_
  rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ((Finset.sort_nodup I _).erase t)]
  intro s
  rw [Finset.mem_sort, (Finset.sort_nodup I _).mem_erase_iff, Finset.mem_sort, Finset.mem_erase]

/-- `airy1FinCdf` through the position-indexed determinant of `FddCont`. -/
theorem airy1FinCdf_eq_fddDetLev' (I : Finset ℝ) {g : ℝ} {gs : List ℝ}
    (hG : gapsOf (I.sort (· ≤ ·)) = g :: gs) :
    ∃ (hg : 0 < g) (hgs : ∀ c ∈ gs, 0 < c) (h1 : 1 ≤ g + gs.sum), ∀ y : I → ℝ,
      airy1FinCdf I y = fddDetLev g gs hg hgs h1 (fun i => levelFn I y ((I.sort (· ≤ ·)).getD i 0)) := by
  set ts := I.sort (· ≤ ·) with hts
  have hent : ∀ x : I → ℝ, finEntries I x
      = zipLev (fun i => levelFn I x (ts.getD i 0)) (gapsOf ts) := fun x =>
    fddEntries_eq_zipLev _ _
  have hE : ∀ x : I → ℝ, finEntries I x
      = (levelFn I x (ts.getD 0 0), g) :: zipLev (fun i => levelFn I x (ts.getD (i + 1) 0)) gs :=
    fun x => by rw [hent, hG, zipLev_cons]
  have hpos := finEntries_pos I (fun _ => 0)
  rw [hE] at hpos
  have hg : 0 < g := hpos _ List.mem_cons_self
  have hgs : ∀ c ∈ gs, 0 < c := by
    intro c hc
    rw [← map_snd_zipLev gs (fun i => levelFn I (fun _ => 0) (ts.getD (i + 1) 0)),
      List.mem_map] at hc
    obtain ⟨y, hy, rfl⟩ := hc
    exact hpos y (List.mem_cons_of_mem _ hy)
  have h1 : 1 ≤ g + gs.sum := by
    have hl := finEntries_lastGap I (fun _ => 0) _ _ (hE _)
    have := one_le_gapSum hg (zipLev_pos hgs _) hl
    rwa [gapSum_zipLev] at this
  exact ⟨hg, hgs, h1, fun x => cdfOfEntries_cons (hE x) _ _ hg (zipLev_pos hgs _)
    (one_le_gapSum_zipLev h1 (fun i => levelFn I x (ts.getD i 0)))⟩

theorem memLp_fddVKer_hitKerT {lev : ℝ → EReal} (hbot : ∀ s, lev s ≠ ⊥) {τ : ℝ} (hτ : 0 < τ)
    (a0 : ℝ) (rest : List ℝ) (hp : (a0 :: rest).Pairwise (· < ·)) {a : ℝ} (ha : 0 < a) :
    MemLp (fddVKer (hitKerT lev τ (a0 :: rest)) a) 2 (volume.prod volume) := by
  obtain ⟨g, gs, h⟩ := gapsOfP_cons τ a0 rest
  have hpos := gapsOfP_pos hτ (a0 :: rest) hp
  rw [h] at hpos
  rw [← hitKerZ_lvE lev τ rest a0 g gs h]
  exact memLp_fddVKer_hitKerZ (hpos g List.mem_cons_self)
    (fun c hc => hpos c (List.mem_cons_of_mem _ hc)) (fun i => hbot _) ha

/-- **The limit of `F_I` along converging extended levels** (Finset form of
`tendsto_fddDetLev_ereal`, kernel written over the sorted time list). -/
theorem tendsto_airy1FinCdf_lim {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (I : Finset ℝ) {a0 : ℝ} {rest : List ℝ} (hts : I.sort (· ≤ ·) = a0 :: rest)
    {lev : ℝ → EReal} (hbot : ∀ s, lev s ≠ ⊥) (hout : ∀ s, s ∉ I → lev s = ((0 : ℝ) : EReal))
    {xn : α → I → ℝ} (hx : ∀ s : I, Tendsto (fun n => ((xn n s : ℝ) : EReal)) l (𝓝 (lev s)))
    (hV : MemLp (fddVKer (hitKerT lev 1 (a0 :: rest)) (2 * (gapsOfP 1 (a0 :: rest)).sum)) 2
      (volume.prod volume))
    (hW : MemLp (AiryConj.wKernel (gapsOfP 1 (a0 :: rest)).sum
      (2 * (gapsOfP 1 (a0 :: rest)).sum)) 2 (volume.prod volume)) :
    Tendsto (fun n => airy1FinCdf I (xn n)) l
      (𝓝 (fredholmDet (kernelOperator hV ∘L kernelOperator hW) 1)) := by
  obtain ⟨g, gs, hG⟩ := gapsOfP_cons 1 a0 rest
  have hG' : gapsOf (I.sort (· ≤ ·)) = g :: gs := by rw [hts, gapsOf_eq_gapsOfP, hG]
  obtain ⟨hg, hgs, h1, heq⟩ := airy1FinCdf_eq_fddDetLev' I hG'
  simp_rw [heq]
  have hxb : ∀ i, lvE lev (a0 :: rest) i ≠ ⊥ := fun i => hbot _
  have hxi : ∀ i, Tendsto (fun n =>
      ((levelFn I (xn n) ((I.sort (· ≤ ·)).getD i 0) : ℝ) : EReal)) l
      (𝓝 (lvE lev (a0 :: rest) i)) := by
    intro i
    rw [hts]
    unfold lvE
    by_cases hs : (a0 :: rest).getD i 0 ∈ I
    · simp only [levelFn, hs, ↓reduceDIte]
      exact hx ⟨_, hs⟩
    · simp only [levelFn, hs, ↓reduceDIte]
      rw [hout _ hs]
      exact tendsto_const_nhds
  have hT := tendsto_fddDetLev_ereal hg hgs h1 hxb hxi
  have hsum : (gapsOfP 1 (a0 :: rest)).sum = g + gs.sum := by rw [hG, List.sum_cons]
  have hlim : fredholmDet (kernelOperator hV ∘L kernelOperator hW) 1
      = fredholmDet (kernelOperator (memLp_fddVKer_hitKerZ hg hgs hxb
          (a := 2 * (g + gs.sum)) (by linarith)) ∘L
        kernelOperator (AiryConj.memLp_wKernel (T := g + gs.sum) (a := 2 * (g + gs.sum))
          (by linarith) (by linarith))) 1 := by
    congr 2
    · exact AiryTwoInt.kernelOperator_congr
        (by rw [hsum, hitKerZ_lvE lev 1 rest a0 g gs hG]) _ _
    · exact AiryTwoInt.kernelOperator_congr (by rw [hsum]) _ _
  rw [hlim]
  exact hT

/-- Same levels, different paddings: `SamePad`. -/
theorem samePad_zipLev_gapsOfP (τ₁ τ₂ : ℝ) : ∀ (rest : List ℝ) (a : ℝ) (y : ℕ → ℝ)
    {g₁ g₂ : ℝ} {gs₁ gs₂ : List ℝ}, gapsOfP τ₁ (a :: rest) = g₁ :: gs₁ →
    gapsOfP τ₂ (a :: rest) = g₂ :: gs₂ →
    SamePad (y 0, g₁) (zipLev (fun i => y (i + 1)) gs₁) (y 0, g₂)
      (zipLev (fun i => y (i + 1)) gs₂)
  | [], a, y, g₁, g₂, gs₁, gs₂, h₁, h₂ => by
    simp only [gapsOfP, List.cons.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl⟩ := h₂
    simp only [zipLev, SamePad]
  | b :: rest, a, y, g₁, g₂, gs₁, gs₂, h₁, h₂ => by
    simp only [gapsOfP, List.cons.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl⟩ := h₂
    obtain ⟨c₁, cs₁, hc₁⟩ := gapsOfP_cons τ₁ b rest
    obtain ⟨c₂, cs₂, hc₂⟩ := gapsOfP_cons τ₂ b rest
    rw [hc₁, hc₂, zipLev_cons, zipLev_cons]
    exact ⟨rfl, samePad_zipLev_gapsOfP τ₁ τ₂ rest b (fun i => y (i + 1)) hc₁ hc₂⟩

/-- Closing step: a limit operator whose `V` kernel is a real list's `hitKerN` (any padding,
admissible weight) has determinant `F_J(y)` when the list is `SamePad` with `J`'s entries. -/
theorem det_eq_airy1FinCdf_of (J : Finset ℝ) (y : J → ℝ) {e L : _} (hfin : finEntries J y = e :: L)
    {e' : ℝ × ℝ} {L' : List (ℝ × ℝ)} (hsp : SamePad e L e' L') (he' : 0 < e'.2)
    (hL' : ∀ z ∈ L', 0 < z.2) {T a : ℝ} (hTeq : gapSum e' L' = T) (ha : T + 1 ≤ a)
    {K : ℝ × ℝ → ℝ} (hK : K = fddVKer (hitKerN e' L') a) (hV : MemLp K 2 (volume.prod volume))
    (hW : MemLp (AiryConj.wKernel T a) 2 (volume.prod volume)) :
    fredholmDet (kernelOperator hV ∘L kernelOperator hW) 1 = airy1FinCdf J y := by
  have ha' : gapSum e' L' + 1 ≤ a := by rw [hTeq]; exact ha
  rw [airy1FinCdf_eq_fredholmDet_fddOpAt J y hfin hsp he' hL' ha']
  unfold fddOpAt
  congr 2
  · exact AiryTwoInt.kernelOperator_congr hK _ _
  · exact AiryTwoInt.kernelOperator_congr (by rw [hTeq]) _ _

/-- `F_J = 1` when `J` has no times. -/
theorem airy1FinCdf_of_sort_nil (J : Finset ℝ) (h : J.sort (· ≤ ·) = []) (y : J → ℝ) :
    airy1FinCdf J y = 1 := by
  unfold airy1FinCdf
  exact cdfOfEntries_nil (by rw [finEntries, h]; rfl) _ _

/-- The determinant of `T_V ∘ T_W` is `1` when `V = 0`. -/
theorem fredholmDet_kernelOperator_zero {V W : ℝ × ℝ → ℝ} (hV : MemLp V 2 (volume.prod volume))
    (hW : MemLp W 2 (volume.prod volume)) (h0 : V = 0) (z : ℝ) :
    fredholmDet (kernelOperator hV ∘L kernelOperator hW) z = 1 := by
  have h : kernelOperator hV = 0 := by
    rw [AiryTwoInt.kernelOperator_congr (show V = V - V by rw [h0, sub_self]) hV (hV.sub hV),
      AiryTwoInt.kernelOperator_sub hV hV, sub_self]
  rw [h, ContinuousLinearMap.zero_comp, fredholmDet_zero_op]

/-! ## The drop-a-time limits (Finset forms) -/

/-- Extended levels for dropping `t`: `⊤` at `t`, the given levels elsewhere on `I`, `0` off
`I`. -/
noncomputable def dropLev (I : Finset ℝ) (x : I → ℝ) (t s : ℝ) : EReal :=
  if s = t then ⊤ else if h : s ∈ I then ((x ⟨s, h⟩ : ℝ) : EReal) else ((0 : ℝ) : EReal)

theorem dropLev_ne_bot (I : Finset ℝ) (x : I → ℝ) (t s : ℝ) : dropLev I x t s ≠ ⊥ := by
  unfold dropLev
  split_ifs
  · exact top_ne_bot
  · exact EReal.coe_ne_bot _
  · exact EReal.coe_ne_bot _

/-- **Dropping one time**: for any time `t ∈ I`, if `x_t → +∞` and the other levels converge,
then `F_I(x) → F_{I∖{t}}(x|_{I∖{t}})`.  An interior or last time is dropped by the kernel
collapse `lamKerT_erase` (and padding/weight independence); the first time by the cyclicity identity
`fredholmDet_swap_heat` (and weight independence); a single time gives `F_∅ = 1`. -/
theorem tendsto_airy1FinCdf_erase {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (I : Finset ℝ) {t : ℝ} (ht : t ∈ I) (x : I → ℝ) {xn : α → I → ℝ}
    (hx : ∀ s : I, s.1 ≠ t → Tendsto (fun n => xn n s) l (𝓝 (x s)))
    (htop : Tendsto (fun n => xn n ⟨t, ht⟩) l atTop) :
    Tendsto (fun n => airy1FinCdf I (xn n)) l
      (𝓝 (airy1FinCdf (I.erase t) (fun s => x ⟨s.1, Finset.mem_of_mem_erase s.2⟩))) := by
  set x' : (I.erase t) → ℝ := fun s => x ⟨s.1, Finset.mem_of_mem_erase s.2⟩ with hx'def
  set lev := dropLev I x t with hlevdef
  have hbot : ∀ s, lev s ≠ ⊥ := dropLev_ne_bot I x t
  have hout : ∀ s, s ∉ I → lev s = ((0 : ℝ) : EReal) := fun s hs => by
    have hst : s ≠ t := fun h => hs (h ▸ ht)
    simp [hlevdef, dropLev, hst, hs]
  have hlt : lev t = ⊤ := by simp [hlevdef, dropLev]
  have hreal : ∀ s ∈ I.erase t, lev s = ((levelFn (I.erase t) x' s : ℝ) : EReal) := by
    intro s hs
    have hst : s ≠ t := Finset.ne_of_mem_erase hs
    have hsI : s ∈ I := Finset.mem_of_mem_erase hs
    simp [hlevdef, dropLev, hst, hsI, levelFn, hs, hx'def]
  have hxE : ∀ s : I, Tendsto (fun n => ((xn n s : ℝ) : EReal)) l (𝓝 (lev s)) := by
    intro s
    by_cases hst : s.1 = t
    · have hs : s = ⟨t, ht⟩ := Subtype.ext hst
      subst hs
      rw [hlt]
      exact EReal.tendsto_coe_nhds_top_iff.2 htop
    · have hls : lev s = ((x s : ℝ) : EReal) := by simp [hlevdef, dropLev, hst]
      rw [hls]
      exact (continuous_coe_real_ereal.tendsto _).comp (hx s hst)
  have hmem : t ∈ I.sort (· ≤ ·) := (Finset.mem_sort _).2 ht
  obtain ⟨a0, rest, hts⟩ : ∃ a0 rest, I.sort (· ≤ ·) = a0 :: rest := by
    cases h : I.sort (· ≤ ·) with
    | nil => rw [h] at hmem; simp at hmem
    | cons a0 rest => exact ⟨a0, rest, rfl⟩
  rw [hts] at hmem
  have hp : (a0 :: rest).Pairwise (· < ·) := hts ▸ sort_lt I
  have hts' : (I.erase t).sort (· ≤ ·) = (a0 :: rest).erase t := by rw [sort_erase, hts]
  have hpE := sort_lt (I.erase t)
  rw [hts'] at hpE
  have hmemE : ∀ s ∈ (a0 :: rest).erase t, s ∈ I.erase t := fun s hs => by
    rw [← Finset.mem_sort (· ≤ ·), hts']; exact hs
  obtain ⟨g, gs, hG⟩ := gapsOfP_cons 1 a0 rest
  have hS1 : 1 ≤ (gapsOfP 1 (a0 :: rest)).sum := by
    have hG' : gapsOf (I.sort (· ≤ ·)) = g :: gs := by rw [hts, gapsOf_eq_gapsOfP, hG]
    obtain ⟨-, -, h1, -⟩ := airy1FinCdf_eq_fddDetLev' I hG'
    rw [hG, List.sum_cons]; exact h1
  set S := (gapsOfP 1 (a0 :: rest)).sum with hSdef
  have hV := memLp_fddVKer_hitKerT hbot one_pos a0 rest hp (a := 2 * S) (by linarith)
  have hW := AiryTwoInt.memLp_wKernel_any (T := S) (a := 2 * S) (by linarith)
  have hlim := tendsto_airy1FinCdf_lim I hts hbot hout hxE hV hW
  suffices hD : fredholmDet (kernelOperator hV ∘L kernelOperator hW) 1
      = airy1FinCdf (I.erase t) x' by
    rw [← hD]; exact hlim
  by_cases hta : t = a0
  · -- the first time
    have herase : (a0 :: rest).erase t = rest := by rw [hta]; exact List.erase_cons_head ..
    rw [herase] at hpE hmemE
    cases rest with
    | nil =>
      have h0 : fddVKer (hitKerT lev 1 [a0]) (2 * S) = 0 := by
        rw [hitKerT_all_top one_pos [] a0 hp (fun s hs => by
          rw [List.mem_singleton.1 hs, ← hta]; exact hlt)]
        funext p; simp [fddVKer]
      rw [fredholmDet_kernelOperator_zero hV hW h0,
        airy1FinCdf_of_sort_nil _ (by rw [hts', herase]) x']
    | cons b rest' =>
      have hab : 0 < b - a0 := sub_pos.2 ((List.pairwise_cons.1 hp).1 b List.mem_cons_self)
      have hhead := hitKerT_head_top one_pos a0 b rest' hp (hta ▸ hlt)
      have hrl : hitKerT lev 1 (b :: rest')
          = hitKerT (fun s => ((levelFn (I.erase t) x' s : ℝ) : EReal)) 1 (b :: rest') :=
        hitKerT_congr 1 _ fun s hs => hreal s (hmemE s hs)
      obtain ⟨g', gs', hG'⟩ := gapsOfP_cons 1 b rest'
      have hN := hitKerT_coe (levelFn (I.erase t) x') 1 b rest' hG'
      have hpos := gapsOfP_pos one_pos (b :: rest') hpE
      rw [hG'] at hpos
      have he' : 0 < g' := hpos g' List.mem_cons_self
      have hgs' : ∀ c ∈ gs', 0 < c := fun c hc => hpos c (List.mem_cons_of_mem _ hc)
      set y : ℕ → ℝ := fun i => levelFn (I.erase t) x' ((b :: rest').getD i 0) with hy
      have hL' := zipLev_pos hgs' (fun i => y (i + 1))
      have hfin : finEntries (I.erase t) x' = (y 0, g') :: zipLev (fun i => y (i + 1)) gs' := by
        rw [finEntries, fddEntries_eq_zipLev, hts', herase, gapsOf_eq_gapsOfP, hG', zipLev_cons]
      have hT : gapSum (y 0, g') (zipLev (fun i => y (i + 1)) gs')
          = S - (b - a0) := by
        rw [gapSum_zipLev, hSdef]
        show g' + gs'.sum = ((b - a0) :: gapsOfP 1 (b :: rest')).sum - (b - a0)
        rw [List.sum_cons, hG', List.sum_cons]; ring
      have hT0 : 0 < gapSum (y 0, g') (zipLev (fun i => y (i + 1)) gs') :=
        gapSum_pos _ _ he' hL'
      have hK : fddVKer (hitKerT lev 1 (a0 :: b :: rest')) (2 * S)
          = fddVKer (AiryConj.compKernel (AiryTwoInt.heatKerTwo (b - a0))
            (hitKerN (y 0, g') (zipLev (fun i => y (i + 1)) gs'))) (2 * S) := by
        rw [hhead, hrl, hN]
      have hV2 : MemLp (fddVKer (AiryConj.compKernel (AiryTwoInt.heatKerTwo (b - a0))
          (hitKerN (y 0, g') (zipLev (fun i => y (i + 1)) gs'))) (2 * S)) 2
          (volume.prod volume) := hK ▸ hV
      have hV' := memLp_fddVKer (y 0, g') (zipLev (fun i => y (i + 1)) gs') he' hL'
        (a := 2 * S) (by linarith)
      have hW' := AiryTwoInt.memLp_wKernel_any (T := S - (b - a0)) (a := 2 * S)
        (by linarith)
      rw [AiryTwoInt.kernelOperator_congr hK hV hV2,
        fredholmDet_swap_heat hab hT0 (by linarith) (measurable_hitKerN he' hL')
          (abs_hitKerN_le he' hL') hV2 hW hV' hW' 1]
      exact det_eq_airy1FinCdf_of (I.erase t) x' hfin (samePad_refl _ _) he' hL' hT
        (by linarith) rfl hV' hW'
  · -- an interior or the last time
    have htr : t ∈ rest := by
      rcases List.mem_cons.1 hmem with h | h
      · exact absurd h hta
      · exact h
    cases rest with
    | nil => simp at htr
    | cons b rest' =>
      have herase : (a0 :: b :: rest').erase t = a0 :: (b :: rest').erase t := by
        rw [List.erase_cons]
        simp [beq_iff_eq, Ne.symm hta]
      rw [herase] at hpE hmemE
      obtain ⟨τ', hτ', hsum, hEq⟩ := lamKerT_erase lev hlt rest' a0 b 1 one_pos hp htr
      have hcol : hitKerT lev 1 (a0 :: b :: rest') = hitKerT lev τ' (a0 :: (b :: rest').erase t) := by
        funext p
        unfold hitKerT
        rw [hsum, hEq]
      have hrl : hitKerT lev τ' (a0 :: (b :: rest').erase t)
          = hitKerT (fun s => ((levelFn (I.erase t) x' s : ℝ) : EReal)) τ'
            (a0 :: (b :: rest').erase t) :=
        hitKerT_congr τ' _ fun s hs => hreal s (hmemE s hs)
      obtain ⟨g', gs', hG'⟩ := gapsOfP_cons τ' a0 ((b :: rest').erase t)
      obtain ⟨g'', gs'', hG''⟩ := gapsOfP_cons 1 a0 ((b :: rest').erase t)
      have hN := hitKerT_coe (levelFn (I.erase t) x') τ' a0 _ hG'
      have hpos := gapsOfP_pos hτ' _ hpE
      rw [hG'] at hpos
      have he' : 0 < g' := hpos g' List.mem_cons_self
      have hgs' : ∀ c ∈ gs', 0 < c := fun c hc => hpos c (List.mem_cons_of_mem _ hc)
      set y : ℕ → ℝ := fun i =>
        levelFn (I.erase t) x' ((a0 :: (b :: rest').erase t).getD i 0) with hy
      have hL' := zipLev_pos hgs' (fun i => y (i + 1))
      have hfin : finEntries (I.erase t) x'
          = (y 0, g'') :: zipLev (fun i => y (i + 1)) gs'' := by
        rw [finEntries, fddEntries_eq_zipLev, hts', herase, gapsOf_eq_gapsOfP, hG'', zipLev_cons]
      have hsp := samePad_zipLev_gapsOfP 1 τ' _ a0 y hG'' hG'
      have hT : gapSum (y 0, g') (zipLev (fun i => y (i + 1)) gs') = S := by
        rw [gapSum_zipLev, hSdef, ← hsum, hG', List.sum_cons]
      have hK : fddVKer (hitKerT lev 1 (a0 :: b :: rest')) (2 * S)
          = fddVKer (hitKerN (y 0, g') (zipLev (fun i => y (i + 1)) gs')) (2 * S) := by
        rw [hcol, hrl, hN]
      exact det_eq_airy1FinCdf_of (I.erase t) x' hfin hsp he' hL' hT (by linarith) hK hV hW

/-- **Drop-a-time, `update` form**: raising one level to `+∞` with the others fixed. -/
theorem tendsto_airy1FinCdf_update (I : Finset ℝ) {t : ℝ} (ht : t ∈ I) (x : I → ℝ) :
    Tendsto (fun c : ℝ => airy1FinCdf I (Function.update x ⟨t, ht⟩ c)) atTop
      (𝓝 (airy1FinCdf (I.erase t) (fun s => x ⟨s.1, Finset.mem_of_mem_erase s.2⟩))) := by
  refine tendsto_airy1FinCdf_erase I ht x (xn := fun c => Function.update x ⟨t, ht⟩ c)
    (fun s hs => ?_) ?_
  · have hne : s ≠ ⟨t, ht⟩ := fun h => hs (by rw [h])
    simp only [Function.update_of_ne hne]
    exact tendsto_const_nhds
  · simp only [Function.update_self]
    exact tendsto_id

/-- **All levels to `+∞`**: if every level tends to `+∞`, then `F_I → 1` (all projections become
`I`, the
hitting kernel vanishes and the determinant is `det(1) = 1`); `F_∅ = 1` holds already. -/
theorem tendsto_airy1FinCdf_one {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (I : Finset ℝ) {xn : α → I → ℝ} (hx : ∀ s : I, Tendsto (fun n => xn n s) l atTop) :
    Tendsto (fun n => airy1FinCdf I (xn n)) l (𝓝 1) := by
  cases hts : I.sort (· ≤ ·) with
  | nil =>
    simp_rw [airy1FinCdf_of_sort_nil I hts]
    exact tendsto_const_nhds
  | cons a0 rest =>
    set lev : ℝ → EReal := fun s => if s ∈ I then ⊤ else ((0 : ℝ) : EReal) with hlevdef
    have hbot : ∀ s, lev s ≠ ⊥ := fun s => by
      simp only [hlevdef]
      split_ifs
      · exact top_ne_bot
      · exact EReal.coe_ne_bot _
    have hout : ∀ s, s ∉ I → lev s = ((0 : ℝ) : EReal) := fun s hs => by simp [hlevdef, hs]
    have hxE : ∀ s : I, Tendsto (fun n => ((xn n s : ℝ) : EReal)) l (𝓝 (lev s)) := by
      intro s
      have : lev s = ⊤ := by simp [hlevdef]
      rw [this]
      exact EReal.tendsto_coe_nhds_top_iff.2 (hx s)
    have hp : (a0 :: rest).Pairwise (· < ·) := hts ▸ sort_lt I
    obtain ⟨g, gs, hG⟩ := gapsOfP_cons 1 a0 rest
    have hS1 : 1 ≤ (gapsOfP 1 (a0 :: rest)).sum := by
      have hG' : gapsOf (I.sort (· ≤ ·)) = g :: gs := by rw [hts, gapsOf_eq_gapsOfP, hG]
      obtain ⟨-, -, h1, -⟩ := airy1FinCdf_eq_fddDetLev' I hG'
      rw [hG, List.sum_cons]; exact h1
    set S := (gapsOfP 1 (a0 :: rest)).sum with hSdef
    have hV := memLp_fddVKer_hitKerT hbot one_pos a0 rest hp (a := 2 * S) (by linarith)
    have hW := AiryTwoInt.memLp_wKernel_any (T := S) (a := 2 * S) (by linarith)
    have hlim := tendsto_airy1FinCdf_lim I hts hbot hout hxE hV hW
    have h0 : fddVKer (hitKerT lev 1 (a0 :: rest)) (2 * S) = 0 := by
      rw [hitKerT_all_top one_pos rest a0 hp (fun s hs => by
        have : s ∈ I := by rw [← Finset.mem_sort (· ≤ ·), hts]; exact hs
        simp [hlevdef, this])]
      funext p; simp [fddVKer]
    rw [← fredholmDet_kernelOperator_zero hV hW h0 1]
    exact hlim

end AiryFdd
