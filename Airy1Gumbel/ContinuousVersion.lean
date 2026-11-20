/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.TruncatedMoment
import BrownianMotion.Continuity.KolmogorovChentsov
import BrownianMotion.Continuity.KolmogorovChentsovInequality
import BrownianMotion.Continuity.HasBoundedInternalCoveringNumber

open MeasureTheory Set Filter ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace Airy1Gumbel

/-!
# A continuous version of the lower-clamped Airy₁ process

Fix a lower clamp level `L`. On `(ℝ → ℝ, airy1Law h)` we build a process
`airy1ContL h L : ℝ≥0 → (ℝ → ℝ) → ℝ` such that

* every path `t ↦ airy1ContL h L t f` is continuous, takes values in `[L, ∞)`, and is locally
  `β`-Hölder for every `β < 1/2` (`continuous_airy1ContL`, `airy1ContL_ge`,
  `holder_airy1ContL`);
* each `airy1ContL h L t` is measurable (`measurable_airy1ContL`);
* it is a **modification** of `t ↦ max L (f t)`: `airy1ContL h L t =ᵐ max L (f t)` for every
  `t ≥ 0` (`airy1ContL_ae_eq`).

Route (no left tail, no mesh limit):

1. **KC modification for each clamp** (`exists_holder_modification_clamp`): for `U ≥ L`, BM's
   `exists_modification_holder_iSup` with the cover `Ico 0 (n+1)` of `ℝ≥0`
   (`isCoverWithBoundedCoveringNumber_Ico_nnreal`) and the global Kolmogorov condition at the
   moment orders `p = n + 4` (`isKolmogorovProcess_clamp_nnreal`) gives a modification `Y_U` of
   `clamp_{[L,U]}(f t)` which is locally `β`-Hölder for all `β < sup_n (p_n − 3)/(2 p_n) = 1/2`.
2. **Upper boundedness on rationals** (`airy1Law_unbddEvent`): for every `N`, almost surely
   `sup {f s : s ∈ ℚ ∩ [0, N]} < ∞`. Per unit window `[j, j+1)` and level `K` (with fixed lower
   clamp `0`): if `f j ≤ K/2` and `f (j+s) > K` for a rational `s ∈ [0,1)`, the clamped process
   `clamp_{[0,K]}(f (j + ·))` oscillates by `≥ K/2`; the quantitative KC inequality
   (`countable_kolmogorov_chentsov`, order `p = 4`, `β = 1/16`) with the **local** Kolmogorov constant
   (linear in `K`) and Markov give `≤ c K / K⁴`, while `P(f j > K/2) = 1 − F_{0}(K/2) → 0` by
   contrib `tendsto_airy1FinCdf_one` (`window_tail_le`, `measure_unbddEvent_le`).
3. **Glue** (`airy1ContL`): with `U_n = L + n` and modifications `Y_n`, on the full-measure event
   `goodSet` (all `Y_n` agree with the clamps at rational times, and rational sups are finite)
   one has `Y_n = clamp_{[L,L+n]} ∘ Y_m` for `m ≥ n` (continuity + density), the `Y_n` increase
   in `n`, and on each `[0, N)` they are eventually constant. `airy1ContL` is their supremum on
   `goodSet` and the constant `L` off it.

**The lower side, supplied in `LowerBound.lean`.** A real-valued continuous version needs
`P(inf_{ℚ ∩ [0,1]} f < −2M) → 0`. That uses the `GOELeftTail` record
(`F_{0}(−M) ≤ C e^{−cM³}`) and the small-weight moment constant at `w = 2S`, `τ = 1/M`, levels
`≥ −2M` with `log C(M) = o(M³)`, fed into the same grid + KC argument (with a
`δ(M)`-grid instead of a unit grid). Given a lower bound on rational infima on compacts, the gluing
of `airy1ContL h (−m)` over `m` is the mirror image of step 3.
-/

/-! ## Rational times in `ℝ≥0` -/

/-- The rational points of `ℝ≥0` (as the image of `ℚ` under `Real.toNNReal`). -/
def ratNN : Set ℝ≥0 := Set.range (fun q : ℚ => Real.toNNReal q)

theorem ratNN_countable : ratNN.Countable := Set.countable_range _

theorem dense_ratNN : Dense ratNN := by
  have hs : Function.Surjective Real.toNNReal := fun x => ⟨x, Real.toNNReal_coe⟩
  exact hs.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal

theorem zero_mem_ratNN : (0 : ℝ≥0) ∈ ratNN := ⟨0, by simp⟩

/-! ## Clamp algebra -/

theorem clampTo_clampTo {L U U' v : ℝ} (hLU : L ≤ U) (hUU' : U ≤ U') :
    clampTo L U (clampTo L U' v) = clampTo L U v := by
  simp only [clampTo, max_def, min_def]
  split_ifs <;> linarith

theorem clampTo_le_self {L U v : ℝ} (hv : L ≤ v) : clampTo L U v ≤ v :=
  max_le hv (min_le_right _ _)

theorem clampTo_le_max (L U v : ℝ) : clampTo L U v ≤ max L v :=
  max_le_max le_rfl (min_le_right _ _)

theorem clampTo_eq_self_of_lt {L U v : ℝ} (hv : L ≤ v) (h : clampTo L U v < U) :
    clampTo L U v = v := by
  simp only [clampTo, max_def, min_def] at h ⊢
  split_ifs at h ⊢ <;> linarith

theorem clampTo_eq_max_of_le {L U v : ℝ} (hvU : v ≤ U) : clampTo L U v = max L v := by
  simp only [clampTo, min_eq_right hvU]

theorem continuous_clampTo (L U : ℝ) : Continuous (clampTo L U) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- `⨆ n, clamp_{[L, L+n]}(v) = max L v`. -/
theorem iSup_clampTo (L v : ℝ) : ⨆ n : ℕ, clampTo L (L + n) v = max L v := by
  have hbdd : BddAbove (Set.range fun n : ℕ => clampTo L (L + n) v) :=
    ⟨max L v, by rintro _ ⟨n, rfl⟩; exact clampTo_le_max _ _ _⟩
  refine le_antisymm (ciSup_le fun n => clampTo_le_max _ _ _) ?_
  refine le_trans (le_of_eq ?_) (le_ciSup hbdd ⌈v - L⌉₊)
  refine (clampTo_eq_max_of_le ?_).symm
  have := Nat.le_ceil (v - L)
  linarith

/-! ## The unit-window Kolmogorov process -/

/-- The clamped coordinate process on the window `[a, a+1]`, indexed by `ℝ≥0` and frozen after
time `1`: `s ↦ clamp_{[L,U]}(f (a + min s 1))`. -/
noncomputable def windowProc (L U a : ℝ) (s : ℝ≥0) (f : ℝ → ℝ) : ℝ :=
  clampTo L U (f (a + min (s : ℝ) 1))

/-- The window process is a Kolmogorov process on all of `ℝ≥0` with the **local** Kolmogorov constant
`K(C + C', U − L, p)` (linear in the clamp width), since all its time increments are `≤ 1`. -/
theorem isKolmogorovProcess_windowProc (h : Airy1FddPositive) {L U C C' p : ℝ} (hLU : L ≤ U)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hF : FwdDefectBound L C) (hR : RevDefectBound L C')
    (hp : 1 < p) (a : ℝ) :
    IsKolmogorovProcess (windowProc L U a) (airy1Law h) p ((p - 1) / 2)
      (truncMomentConst (C + C') (U - L) p).toNNReal := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun s => (measurable_clampTo L U).comp (measurable_pi_apply _)) (fun s u => ?_)
    (by linarith) (by linarith)
  have hs0 : (0 : ℝ) ≤ min (s : ℝ) 1 := le_min s.2 zero_le_one
  have hu0 : (0 : ℝ) ≤ min (u : ℝ) 1 := le_min u.2 zero_le_one
  have hs1 : min (s : ℝ) 1 ≤ 1 := min_le_right _ _
  have hu1 : min (u : ℝ) 1 ≤ 1 := min_le_right _ _
  have hd : dist (a + min (s : ℝ) 1) (a + min (u : ℝ) 1) ≤ 1 := by
    rw [Real.dist_eq, add_sub_add_left_eq_sub, abs_sub_le_iff]
    constructor <;> linarith
  have H := lintegral_edist_clamp_le h hLU hC hC' hF hR hp hd
  have hed : edist (a + min (s : ℝ) 1) (a + min (u : ℝ) 1) ≤ edist s u := by
    rw [edist_dist, edist_dist, Real.dist_eq, add_sub_add_left_eq_sub, NNReal.dist_eq]
    refine ENNReal.ofReal_le_ofReal ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
    simp
  change ∫⁻ ω, edist (clampTo L U (ω (a + min (s : ℝ) 1)))
      (clampTo L U (ω (a + min (u : ℝ) 1))) ^ p ∂airy1Law h
    ≤ ENNReal.ofReal (truncMomentConst (C + C') (U - L) p) * edist s u ^ ((p - 1) / 2)
  exact H.trans (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hed (by linarith)) zero_le)

/-- The rational points of the window `[0, 1)`. -/
def winPts : Set ℝ≥0 := {s | s < 1 ∧ s ∈ ratNN}

theorem winPts_countable : winPts.Countable := ratNN_countable.mono fun _ hs => hs.2

theorem hasCoveringExponent_Ico_zero_one :
    Metric.HasCoveringExponent (Set.Ico (0 : ℝ≥0) 1) 3 1 := by
  have := isCoverWithBoundedCoveringNumber_Ico_nnreal.hasBoundedCoveringNumber 0
  simpa using this

/-- **Window tail via quantitative KC.** For `K > 0`, `L ≤ K/2` and any window start `a`:
`P(f a ≤ K/2, ∃ rational s ∈ [0,1), f (a + s) > K) ≤ K(C + C', K − L, 4) · L_KC / (K/2)⁴`,
where `L_KC = constL 3 1 4 (3/2) (1/16)` is BM's Kolmogorov–Chentsov constant. -/
theorem window_tail_le (h : Airy1FddPositive) {L K C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hF : FwdDefectBound L C) (hR : RevDefectBound L C') (hK : 0 < K) (hLK : L ≤ K / 2)
    (a : ℝ) :
    airy1Law h {f : ℝ → ℝ | f a ≤ K / 2 ∧ ∃ s ∈ winPts, K < f (a + s)}
      ≤ ENNReal.ofReal (truncMomentConst (C + C') (K - L) 4
          * (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal / (K / 2) ^ (4 : ℝ)) := by
  have hLK' : L ≤ K := by linarith
  set X := windowProc L K a with hXdef
  have hX0 := isKolmogorovProcess_windowProc h hLK' hC hC' hF hR (p := 4) (by norm_num) a
  have e : ((4 : ℝ) - 1) / 2 = 3 / 2 := by norm_num
  rw [e] at hX0
  have hX : IsKolmogorovProcess X (airy1Law h) 4 (3 / 2)
      (truncMomentConst (C + C') (K - L) 4).toNNReal := hX0
  have : Countable winPts := winPts_countable.to_subtype
  have hKC := countable_kolmogorov_chentsov hasCoveringExponent_Ico_zero_one
    hX.IsAEKolmogorovProcess (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2)
    (β := 1 / 16) (by norm_num) winPts (fun s hs => ⟨zero_le, hs.1⟩)
  set Φ : (ℝ → ℝ) → ℝ≥0∞ := fun f => ⨆ (s : winPts) (t : winPts),
    edist (X s f) (X t f) ^ (4 : ℝ) / edist s t ^ (((1 / 16 : ℝ≥0) : ℝ) * 4) with hΦ
  have hΦm : AEMeasurable Φ (airy1Law h) := by
    refine AEMeasurable.iSup (fun s => AEMeasurable.iSup (fun t => ?_))
    exact AEMeasurable.div (hX.measurable_edist.aemeasurable.pow_const _) aemeasurable_const
  have hK2 : 0 < K / 2 := by linarith
  have hε0 : ENNReal.ofReal ((K / 2) ^ (4 : ℝ)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hsub : {f : ℝ → ℝ | f a ≤ K / 2 ∧ ∃ s ∈ winPts, K < f (a + s)}
      ⊆ {f | ENNReal.ofReal ((K / 2) ^ (4 : ℝ)) ≤ Φ f} := by
    rintro f ⟨hfa, s, hs, hfs⟩
    simp only [mem_ofPred_eq]
    have hs1 : (s : ℝ) < 1 := by exact_mod_cast hs.1
    have hXs : X s f = K := by
      simp only [hXdef, windowProc, min_eq_left hs1.le, clampTo]
      rw [min_eq_left hfs.le, max_eq_right hLK']
    have hX0' : X 0 f ≤ K / 2 := by
      simp only [hXdef, windowProc, NNReal.coe_zero, min_eq_left zero_le_one, add_zero, clampTo]
      exact max_le hLK (min_le_right _ _ |>.trans hfa)
    have h0 : (0 : ℝ≥0) ∈ winPts := ⟨one_pos, zero_mem_ratNN⟩
    have hed : ENNReal.ofReal (K / 2) ≤ edist (X s f) (X 0 f) := by
      rw [edist_dist, Real.dist_eq, hXs]
      exact ENNReal.ofReal_le_ofReal (by rw [abs_of_nonneg (by linarith)]; linarith)
    have hst : edist s (0 : ℝ≥0) ^ (((1 / 16 : ℝ≥0) : ℝ) * 4) ≤ 1 := by
      refine ENNReal.rpow_le_one ?_ (by positivity)
      rw [edist_dist, NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg s)]
      exact ENNReal.ofReal_le_one.2 hs1.le
    calc ENNReal.ofReal ((K / 2) ^ (4 : ℝ))
        = ENNReal.ofReal (K / 2) ^ (4 : ℝ) :=
          (ENNReal.ofReal_rpow_of_nonneg hK2.le (by norm_num)).symm
      _ ≤ edist (X s f) (X 0 f) ^ (4 : ℝ) := ENNReal.rpow_le_rpow hed (by norm_num)
      _ = edist (X s f) (X 0 f) ^ (4 : ℝ) / 1 := (div_one _).symm
      _ ≤ edist (X s f) (X 0 f) ^ (4 : ℝ) / edist s (0 : ℝ≥0) ^ (((1 / 16 : ℝ≥0) : ℝ) * 4) :=
          ENNReal.div_le_div_left hst _
      _ ≤ Φ f := by
          simp only [hΦ]
          exact le_iSup₂_of_le (f := fun (s t : winPts) =>
            edist (X s f) (X t f) ^ (4 : ℝ) / edist (s : ℝ≥0) (t : ℝ≥0) ^ (((1 / 16 : ℝ≥0) : ℝ) * 4))
            ⟨s, hs⟩ ⟨0, h0⟩ le_rfl
  have hL : constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ) ≠ ∞ :=
    (constL_lt_top (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by push_cast; norm_num)).ne
  have hM := truncMomentConst_nonneg (add_nonneg hC hC') (by linarith : 0 ≤ K - L)
    (by norm_num : (1 : ℝ) < 4)
  calc airy1Law h {f : ℝ → ℝ | f a ≤ K / 2 ∧ ∃ s ∈ winPts, K < f (a + s)}
      ≤ airy1Law h {f | ENNReal.ofReal ((K / 2) ^ (4 : ℝ)) ≤ Φ f} := measure_mono hsub
    _ ≤ (∫⁻ f, Φ f ∂airy1Law h) / ENNReal.ofReal ((K / 2) ^ (4 : ℝ)) :=
        meas_ge_le_lintegral_div hΦm hε0 ENNReal.ofReal_ne_top
    _ ≤ ((truncMomentConst (C + C') (K - L) 4).toNNReal * constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ))
          / ENNReal.ofReal ((K / 2) ^ (4 : ℝ)) :=
        ENNReal.div_le_div_right hKC _
    _ = ENNReal.ofReal (truncMomentConst (C + C') (K - L) 4
          * (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal / (K / 2) ^ (4 : ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul hM,
          ENNReal.ofReal_toReal hL]
        rfl

/-! ## Upper boundedness on rational times -/

/-- The event that the coordinate path is unbounded above on the rational times of `[0, N]`. -/
def unbddEvent (N : ℕ) : Set (ℝ → ℝ) :=
  {f | ∀ B : ℕ, ∃ q : ℚ, Real.toNNReal q ≤ N ∧ (B : ℝ) < f (Real.toNNReal q)}

/-- One-point upper tail: `P(f j > c) = 1 − F_{0}(c)`. -/
theorem airy1Law_gt_eq (h : Airy1FddPositive) (x c : ℝ) :
    airy1Law h {f : ℝ → ℝ | c < f x}
      = ENNReal.ofReal (1 - AiryFdd.airy1FinCdf {0} (fun _ => c)) := by
  set S : Set (ℝ → ℝ) := {f | ∀ t ∈ ({x} : Finset ℝ), f t ≤ (fun _ => c) t} with hSdef
  have hS : MeasurableSet S := measurableSet_setOf_forall_mem_finset_le {x} (fun _ => c)
  have e1 : {f : ℝ → ℝ | c < f x} = Sᶜ := by
    ext f; simp [hSdef]
  have hF : (airy1Law h).real S = AiryFdd.airy1FinCdf {x} (fun _ => c) := airy1Law_fdd h {x} _
  rw [e1, prob_compl_eq_one_sub hS, ← ofReal_measureReal (measure_ne_top _ _),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ measureReal_nonneg, hF,
    airy1FinCdf_singleton_eq x 0 c]

/-- **Per-level bound** for the unbounded event (fixed lower clamp `L`, level `K`). -/
theorem measure_unbddEvent_le (h : Airy1FddPositive) {L C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hF : FwdDefectBound L C) (hR : RevDefectBound L C') (N : ℕ) {K : ℝ} (hK : 0 < K)
    (hLK : L ≤ K / 2) :
    airy1Law h (unbddEvent N)
      ≤ ENNReal.ofReal (((N : ℝ) + 1) * ((1 - AiryFdd.airy1FinCdf {0} (fun _ => K / 2))
          + truncMomentConst (C + C') (K - L) 4
            * (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal / (K / 2) ^ (4 : ℝ))) := by
  set A : ℝ := 1 - AiryFdd.airy1FinCdf {0} (fun _ => K / 2) with hA
  set T : ℝ := truncMomentConst (C + C') (K - L) 4
    * (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal / (K / 2) ^ (4 : ℝ) with hT
  have hF1 := h.airy1FinCdf_le_one ({0} : Finset ℝ) (fun _ => K / 2)
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hT0 : 0 ≤ T := by
    have := truncMomentConst_nonneg (add_nonneg hC hC') (by linarith : 0 ≤ K - L)
      (by norm_num : (1 : ℝ) < 4)
    rw [hT]
    positivity
  have hsub : unbddEvent N ⊆ ⋃ j ∈ Finset.range (N + 1),
      ({f : ℝ → ℝ | K / 2 < f j} ∪ {f | f j ≤ K / 2 ∧ ∃ s ∈ winPts, K < f (j + s)}) := by
    intro f hf
    obtain ⟨q, hqN, hqf⟩ := hf ⌈K⌉₊
    have hKf : K < f (Real.toNNReal q) := (Nat.le_ceil K).trans_lt hqf
    set x : ℝ := (Real.toNNReal q : ℝ) with hx
    have hx0 : 0 ≤ x := (Real.toNNReal q).2
    have hxN : x ≤ N := by rw [hx]; exact_mod_cast hqN
    set j : ℕ := ⌊x⌋₊ with hj
    have hjx : (j : ℝ) ≤ x := Nat.floor_le hx0
    have hxj : x < j + 1 := Nat.lt_floor_add_one x
    have hjN : j ∈ Finset.range (N + 1) := by
      rw [Finset.mem_range]
      have : x < ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact (Nat.floor_lt hx0).2 this
    simp only [mem_iUnion, mem_union, mem_ofPred_eq]
    refine ⟨j, hjN, ?_⟩
    by_cases hfj : f j ≤ K / 2
    · right
      refine ⟨hfj, Real.toNNReal (x - j), ⟨?_, ?_⟩, ?_⟩
      · rw [← NNReal.coe_lt_coe, NNReal.coe_one, Real.coe_toNNReal _ (by linarith)]
        linarith
      · refine ⟨max q 0 - j, ?_⟩
        rw [hx, Real.coe_toNNReal']
        push_cast
        rfl
      · rwa [Real.coe_toNNReal _ (by linarith), add_sub_cancel]
    · left
      exact lt_of_not_ge hfj
  calc airy1Law h (unbddEvent N)
      ≤ airy1Law h (⋃ j ∈ Finset.range (N + 1),
          ({f : ℝ → ℝ | K / 2 < f j} ∪ {f | f j ≤ K / 2 ∧ ∃ s ∈ winPts, K < f (j + s)})) :=
        measure_mono hsub
    _ ≤ ∑ j ∈ Finset.range (N + 1), airy1Law h
          ({f : ℝ → ℝ | K / 2 < f j} ∪ {f | f j ≤ K / 2 ∧ ∃ s ∈ winPts, K < f (j + s)}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (N + 1), ENNReal.ofReal (A + T) := by
        refine Finset.sum_le_sum fun j _ => (measure_union_le _ _).trans ?_
        rw [airy1Law_gt_eq h (j : ℝ) (K / 2), ENNReal.ofReal_add hA0 hT0]
        exact add_le_add le_rfl (window_tail_le h hC hC' hF hR hK hLK j)
    _ = ENNReal.ofReal (((N : ℝ) + 1) * (A + T)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one]
        simp

/-- The local Kolmogorov constant over `(K/2)⁴` tends to `0` (it is linear in `K`). -/
theorem tendsto_truncMomentConst_div (Cs L : ℝ) :
    Tendsto (fun K : ℝ => truncMomentConst Cs (K - L) 4 / (K / 2) ^ (4 : ℝ)) atTop (𝓝 0) := by
  set A : ℝ := (32 : ℝ) ^ ((4 - 1) / 2 : ℝ) * Real.Gamma ((4 - 1) / 2)
  set B : ℝ := (32 : ℝ) ^ (4 / 2 : ℝ) * Real.Gamma (4 / 2) / 2
  have h1 : Tendsto (fun K : ℝ => (64 * Cs * A) / K ^ 3 + (64 * Cs * (B - L * A)) / K ^ 4)
      atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := 64 * Cs * A)).div_atTop
      (tendsto_pow_atTop (α := ℝ) (n := 3) (by norm_num))
    have := this.add ((tendsto_const_nhds (x := 64 * Cs * (B - L * A))).div_atTop
      (tendsto_pow_atTop (α := ℝ) (n := 4) (by norm_num)))
    simpa using this
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with K hK
  have e4 : (K / 2) ^ (4 : ℝ) = (K / 2) ^ (4 : ℕ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e4]
  unfold truncMomentConst
  field_simp
  ring

/-- **Upper boundedness.** For every `N`, almost surely the coordinate path is bounded
above on the rational times of `[0, N]`: `P(unbddEvent N) = 0`. Fixed lower clamp `0`, unit grid,
quantitative KC and `tendsto_airy1FinCdf_one`; no right-tail rate, mesh limit or left tail. -/
theorem airy1Law_unbddEvent (h : Airy1FddPositive) (N : ℕ) : airy1Law h (unbddEvent N) = 0 := by
  obtain ⟨C, hC, hF⟩ := fwdDefectBound_exists 0
  obtain ⟨C', hC', hR⟩ := revDefectBound_exists 0
  set cL := (constL 3 1 4 (3 / 2) ((1 / 16 : ℝ≥0) : ℝ)).toReal
  have hF1 : Tendsto (fun K : ℝ => AiryFdd.airy1FinCdf {0} (fun _ => K / 2)) atTop (𝓝 1) :=
    AiryFdd.tendsto_airy1FinCdf_one {0} (xn := fun K _ => K / 2)
      (fun _ => tendsto_id.atTop_div_const (by norm_num))
  have hT := (tendsto_truncMomentConst_div (C + C') 0).mul_const cL
  have hr : Tendsto (fun K : ℝ => ((N : ℝ) + 1) * ((1 - AiryFdd.airy1FinCdf {0} (fun _ => K / 2))
      + truncMomentConst (C + C') (K - 0) 4 * cL / (K / 2) ^ (4 : ℝ))) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hF1).add hT
    have := this.const_mul ((N : ℝ) + 1)
    simp only [sub_self, zero_mul, add_zero, mul_zero] at this
    refine this.congr' (Eventually.of_forall fun K => ?_)
    simp only
    ring
  refine le_antisymm ?_ zero_le
  have := ge_of_tendsto (b := airy1Law h (unbddEvent N)) (ENNReal.tendsto_ofReal hr) ?_
  · simpa using this
  filter_upwards [eventually_gt_atTop 0] with K hK
  exact measure_unbddEvent_le h hC.le hC'.le hF hR N hK (by linarith)

/-- Almost surely the coordinate path is bounded above on the rational times of every `[0, N]`. -/
theorem ae_bddAbove_rat (h : Airy1FddPositive) :
    ∀ᵐ f ∂airy1Law h, ∀ N : ℕ, ∃ B : ℕ, ∀ q : ℚ, Real.toNNReal q ≤ N →
      f (Real.toNNReal q) ≤ (B : ℝ) := by
  refine ae_all_iff.2 fun N => ?_
  refine ae_iff.2 (measure_mono_null (fun f hf => ?_) (airy1Law_unbddEvent h N))
  simp only [mem_ofPred_eq, not_exists] at hf
  intro B
  by_contra hcon
  exact hf B fun q hq => le_of_not_gt fun hlt => hcon ⟨q, hq, hlt⟩

/-! ## Continuous modifications of the clamped processes -/

/-- **KC modification for a fixed clamp (step 1).** For `L ≤ U` there is a modification `Y`
of `t ↦ clamp_{[L,U]}(f t)` on `ℝ≥0` under `airy1Law h`, with measurable marginals, whose every
path is locally `β`-Hölder for every `β < 1/2`. BM `exists_modification_holder_iSup`, cover
`Ico 0 (n+1)`, orders `p_n = n + 4`, `q_n = (p_n − 1)/2`. -/
theorem exists_holder_modification_clamp (h : Airy1FddPositive) (L U : ℝ) (hLU : L ≤ U) :
    ∃ Y : ℝ≥0 → (ℝ → ℝ) → ℝ, (∀ t, Measurable (Y t))
      ∧ (∀ t, Y t =ᵐ[airy1Law h] fun f => clampTo L U (f t))
      ∧ ∀ f t (β : ℝ≥0), 0 < β → (β : ℝ) < 1 / 2 →
        ∃ V ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · f) V := by
  obtain ⟨C, _, hK⟩ := isKolmogorovProcess_clamp_nnreal h L
  have hX : ∀ n : ℕ, IsAEKolmogorovProcess (fun (s : ℝ≥0) (f : ℝ → ℝ) => clampTo L U (f s))
      (airy1Law h) ((n : ℝ) + 4) (((n : ℝ) + 4 - 1) / 2)
      (truncMomentConst C (U - L) ((n : ℝ) + 4) + (U - L) ^ ((n : ℝ) + 4)).toNNReal :=
    fun n => (hK U _ hLU (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)).IsAEKolmogorovProcess
  obtain ⟨Y, hYm, hYe, hYh⟩ := exists_modification_holder_iSup
    isCoverWithBoundedCoveringNumber_Ico_nnreal hX (fun n => by finiteness) one_pos
    (fun n => by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
  refine ⟨Y, hYm, hYe, fun f t β hβ hβ2 => hYh f t β hβ ?_⟩
  have hbdd : BddAbove (Set.range fun n : ℕ => (((n : ℝ) + 4 - 1) / 2 - 1) / ((n : ℝ) + 4)) := by
    refine ⟨1 / 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [div_le_iff₀ (by linarith)]
    linarith
  set n : ℕ := ⌈3 / (1 - 2 * (β : ℝ))⌉₊
  have hpos : 0 < 1 - 2 * (β : ℝ) := by linarith
  have hn : 3 ≤ (1 - 2 * (β : ℝ)) * n := by
    have := Nat.le_ceil (3 / (1 - 2 * (β : ℝ)))
    rw [div_le_iff₀ hpos] at this
    linarith
  refine lt_of_lt_of_le ?_ (le_ciSup hbdd n)
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  rw [lt_div_iff₀ (by linarith)]
  nlinarith

/-- The upper clamp levels `U_n = L + n`. -/
theorem le_add_natCast (L : ℝ) (n : ℕ) : L ≤ L + n := le_add_of_nonneg_right n.cast_nonneg

/-- The chosen KC modification of `clamp_{[L, L+n]}`. -/
noncomputable def clampMod (h : Airy1FddPositive) (L : ℝ) (n : ℕ) : ℝ≥0 → (ℝ → ℝ) → ℝ :=
  (exists_holder_modification_clamp h L (L + n) (le_add_natCast L n)).choose

theorem measurable_clampMod (h : Airy1FddPositive) (L : ℝ) (n : ℕ) (t : ℝ≥0) :
    Measurable (clampMod h L n t) :=
  (exists_holder_modification_clamp h L (L + n) (le_add_natCast L n)).choose_spec.1 t

theorem clampMod_ae_eq (h : Airy1FddPositive) (L : ℝ) (n : ℕ) (t : ℝ≥0) :
    clampMod h L n t =ᵐ[airy1Law h] fun f => clampTo L (L + n) (f t) :=
  (exists_holder_modification_clamp h L (L + n) (le_add_natCast L n)).choose_spec.2.1 t

theorem holder_clampMod (h : Airy1FddPositive) (L : ℝ) (n : ℕ) (f : ℝ → ℝ) (t : ℝ≥0)
    (β : ℝ≥0) (hβ : 0 < β) (hβ2 : (β : ℝ) < 1 / 2) :
    ∃ V ∈ 𝓝 t, ∃ C, HolderOnWith C β (clampMod h L n · f) V :=
  (exists_holder_modification_clamp h L (L + n) (le_add_natCast L n)).choose_spec.2.2
    f t β hβ hβ2

theorem continuous_clampMod (h : Airy1FddPositive) (L : ℝ) (n : ℕ) (f : ℝ → ℝ) :
    Continuous (clampMod h L n · f) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  obtain ⟨V, hV, C, hC⟩ := holder_clampMod h L n f t (1 / 4) (by norm_num) (by norm_num)
  exact (hC.continuousOn (by norm_num)).continuousAt hV

/-! ## Gluing -/

/-- The full-measure event on which the modifications glue: all `Y_n` agree with the clamps at
rational times, and the path is bounded above on the rational times of every `[0, N]`. -/
def goodSet (h : Airy1FddPositive) (L : ℝ) : Set (ℝ → ℝ) :=
  {f | (∀ n : ℕ, ∀ q : ℚ, clampMod h L n (Real.toNNReal q) f
      = clampTo L (L + n) (f (Real.toNNReal q)))
    ∧ ∀ N : ℕ, ∃ B : ℕ, ∀ q : ℚ, Real.toNNReal q ≤ N → f (Real.toNNReal q) ≤ (B : ℝ)}

theorem measurableSet_goodSet (h : Airy1FddPositive) (L : ℝ) :
    MeasurableSet (goodSet h L) := by
  have e : goodSet h L = (⋂ n : ℕ, ⋂ q : ℚ, {f : ℝ → ℝ | clampMod h L n (Real.toNNReal q) f
      = clampTo L (L + n) (f (Real.toNNReal q))})
      ∩ ⋂ N : ℕ, ⋃ B : ℕ, ⋂ q : ℚ, {f : ℝ → ℝ | Real.toNNReal q ≤ N →
        f (Real.toNNReal q) ≤ (B : ℝ)} := by
    ext f; simp [goodSet]
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun q => ?_)
    (MeasurableSet.iInter fun N => MeasurableSet.iUnion fun B => MeasurableSet.iInter fun q => ?_)
  · exact measurableSet_eq_fun (measurable_clampMod h L n _)
      ((measurable_clampTo _ _).comp (measurable_pi_apply _))
  · by_cases hq : Real.toNNReal q ≤ N
    · simp only [hq, true_imp_iff]
      exact measurableSet_le (measurable_pi_apply _) measurable_const
    · simp [hq]

theorem ae_mem_goodSet (h : Airy1FddPositive) (L : ℝ) : ∀ᵐ f ∂airy1Law h, f ∈ goodSet h L := by
  have h1 : ∀ᵐ f ∂airy1Law h, ∀ n : ℕ, ∀ q : ℚ, clampMod h L n (Real.toNNReal q) f
      = clampTo L (L + n) (f (Real.toNNReal q)) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun q => clampMod_ae_eq h L n _
  filter_upwards [h1, ae_bddAbove_rat h] with f hf1 hf2 using ⟨hf1, hf2⟩

section Deterministic

variable {h : Airy1FddPositive} {L : ℝ} {f : ℝ → ℝ}

/-- On `goodSet`: `Y_n = clamp_{[L,L+n]} ∘ Y_m` for `n ≤ m` (continuity + density). -/
theorem clampMod_eq_clampTo (hf : f ∈ goodSet h L) {n m : ℕ} (hnm : n ≤ m) (t : ℝ≥0) :
    clampMod h L n t f = clampTo L (L + n) (clampMod h L m t f) := by
  have hc := Continuous.ext_on dense_ratNN (continuous_clampMod h L n f)
    ((continuous_clampTo L (L + n)).comp (continuous_clampMod h L m f)) ?_
  · exact congrFun hc t
  rintro _ ⟨q, rfl⟩
  simp only [Function.comp_apply]
  rw [hf.1 n q, hf.1 m q, clampTo_clampTo (le_add_natCast L n)
    (by have : (n : ℝ) ≤ m := by exact_mod_cast hnm
        linarith)]

theorem clampMod_mem (hf : f ∈ goodSet h L) (n : ℕ) (t : ℝ≥0) :
    clampMod h L n t f ∈ Icc L (L + n) := by
  rw [clampMod_eq_clampTo hf le_rfl t]
  exact clampTo_mem (le_add_natCast L n) _

theorem clampMod_mono (hf : f ∈ goodSet h L) {n m : ℕ} (hnm : n ≤ m) (t : ℝ≥0) :
    clampMod h L n t f ≤ clampMod h L m t f := by
  rw [clampMod_eq_clampTo hf hnm t]
  exact clampTo_le_self (clampMod_mem hf m t).1

/-- On `goodSet`, `Y_n ≤ max L B` on `[0, N)` whenever `B` bounds the rational values on `[0,N]`. -/
theorem clampMod_le_of_bound (hf : f ∈ goodSet h L) {N B : ℕ}
    (hB : ∀ q : ℚ, Real.toNNReal q ≤ N → f (Real.toNNReal q) ≤ (B : ℝ)) (n : ℕ) {t : ℝ≥0}
    (ht : t < N) : clampMod h L n t f ≤ max L B := by
  have hcl : IsClosed {s : ℝ≥0 | clampMod h L n s f ≤ max L B} :=
    isClosed_le (continuous_clampMod h L n f) continuous_const
  have hsub : Iio (N : ℝ≥0) ∩ ratNN ⊆ {s : ℝ≥0 | clampMod h L n s f ≤ max L B} := by
    rintro _ ⟨hs, q, rfl⟩
    simp only [mem_ofPred_eq]
    rw [hf.1 n q]
    exact (clampTo_le_max _ _ _).trans (max_le_max le_rfl (hB q (le_of_lt hs)))
  exact closure_minimal hsub hcl (dense_ratNN.open_subset_closure_inter isOpen_Iio ht)

/-- **Stabilization.** On `goodSet`, for each `N` there is `n₀` with `Y_m = Y_{n₀}` on `[0, N)`
for every `m ≥ n₀`, and `Y_m ≤ Y_{n₀}` there for all `m`. -/
theorem exists_clampMod_stable (hf : f ∈ goodSet h L) (N : ℕ) :
    ∃ n₀ : ℕ, ∀ t : ℝ≥0, t < N → ∀ m : ℕ, clampMod h L m t f ≤ clampMod h L n₀ t f
      ∧ (n₀ ≤ m → clampMod h L m t f = clampMod h L n₀ t f) := by
  obtain ⟨B, hB⟩ := hf.2 N
  refine ⟨⌈(B : ℝ) - L⌉₊ + 1, fun t ht m => ?_⟩
  set n₀ := ⌈(B : ℝ) - L⌉₊ + 1
  have hn₀ : max L (B : ℝ) < L + n₀ := by
    have h1 := Nat.le_ceil ((B : ℝ) - L)
    have h2 : ((n₀ : ℕ) : ℝ) = ⌈(B : ℝ) - L⌉₊ + 1 := by simp [n₀]
    rw [max_lt_iff]
    constructor <;> linarith
  have hstab : ∀ m, n₀ ≤ m → clampMod h L m t f = clampMod h L n₀ t f := by
    intro m hm
    have hlt : clampMod h L n₀ t f < L + n₀ :=
      (clampMod_le_of_bound hf hB n₀ ht).trans_lt hn₀
    have e := clampMod_eq_clampTo hf hm t
    rw [e] at hlt ⊢
    exact (clampTo_eq_self_of_lt (clampMod_mem hf m t).1 hlt).symm
  refine ⟨?_, hstab m⟩
  rcases le_total m n₀ with hm | hm
  · exact clampMod_mono hf hm t
  · exact (hstab m hm).le

end Deterministic

/-! ## The glued continuous version -/

open Classical in
/-- **The lower-clamped continuous Airy₁ process** `Ã_L` on `ℝ≥0`: on `goodSet` the supremum of
the KC modifications of `clamp_{[L, L+n]}`, and the constant `L` off it. -/
noncomputable def airy1ContL (h : Airy1FddPositive) (L : ℝ) (t : ℝ≥0) (f : ℝ → ℝ) : ℝ :=
  if f ∈ goodSet h L then ⨆ n : ℕ, clampMod h L n t f else L

theorem measurable_airy1ContL (h : Airy1FddPositive) (L : ℝ) (t : ℝ≥0) :
    Measurable (airy1ContL h L t) := by
  classical
  unfold airy1ContL
  exact Measurable.ite (measurableSet_goodSet h L)
    (Measurable.iSup fun n => measurable_clampMod h L n t) measurable_const

/-- On `goodSet`, `Ã_L = Y_{n₀}` on `[0, N)`. -/
theorem airy1ContL_eq_clampMod {h : Airy1FddPositive} {L : ℝ} {f : ℝ → ℝ}
    (hf : f ∈ goodSet h L) (N : ℕ) :
    ∃ n₀ : ℕ, ∀ t : ℝ≥0, t < N → airy1ContL h L t f = clampMod h L n₀ t f := by
  obtain ⟨n₀, hn₀⟩ := exists_clampMod_stable hf N
  refine ⟨n₀, fun t ht => ?_⟩
  simp only [airy1ContL, hf, ↓reduceIte]
  have hbdd : BddAbove (Set.range fun n : ℕ => clampMod h L n t f) :=
    ⟨clampMod h L n₀ t f, by rintro _ ⟨m, rfl⟩; exact (hn₀ t ht m).1⟩
  exact le_antisymm (ciSup_le fun m => (hn₀ t ht m).1) (le_ciSup hbdd n₀)

/-- Locally (near any `t`), `Ã_L(·, f)` coincides with a single modification `Y_{n₀}`. -/
theorem airy1ContL_eventuallyEq {h : Airy1FddPositive} {L : ℝ} {f : ℝ → ℝ}
    (hf : f ∈ goodSet h L) (t : ℝ≥0) :
    ∃ n₀ : ℕ, ∃ V ∈ 𝓝 t, ∀ s ∈ V, airy1ContL h L s f = clampMod h L n₀ s f := by
  obtain ⟨n₀, hn₀⟩ := airy1ContL_eq_clampMod hf (⌈t⌉₊ + 1)
  refine ⟨n₀, Iio ((⌈t⌉₊ + 1 : ℕ) : ℝ≥0), Iio_mem_nhds ?_, fun s hs => hn₀ s hs⟩
  have := Nat.le_ceil t
  push_cast
  exact lt_of_le_of_lt this (lt_add_one _)

/-- **Every path of `Ã_L` is continuous.** -/
theorem continuous_airy1ContL (h : Airy1FddPositive) (L : ℝ) (f : ℝ → ℝ) :
    Continuous (airy1ContL h L · f) := by
  classical
  by_cases hf : f ∈ goodSet h L
  · refine continuous_iff_continuousAt.2 fun t => ?_
    obtain ⟨n₀, V, hV, hEq⟩ := airy1ContL_eventuallyEq hf t
    refine ((continuous_clampMod h L n₀ f).continuousAt).congr ?_
    filter_upwards [hV] with s hs using (hEq s hs).symm
  · simp only [airy1ContL, hf, ↓reduceIte]
    exact continuous_const

/-- **Every path of `Ã_L` is locally `β`-Hölder for every `β < 1/2`.** -/
theorem holder_airy1ContL (h : Airy1FddPositive) (L : ℝ) (f : ℝ → ℝ) (t : ℝ≥0) (β : ℝ≥0)
    (hβ : 0 < β) (hβ2 : (β : ℝ) < 1 / 2) :
    ∃ V ∈ 𝓝 t, ∃ C, HolderOnWith C β (airy1ContL h L · f) V := by
  classical
  by_cases hf : f ∈ goodSet h L
  · obtain ⟨n₀, V, hV, hEq⟩ := airy1ContL_eventuallyEq hf t
    obtain ⟨W, hW, C, hC⟩ := holder_clampMod h L n₀ f t β hβ hβ2
    refine ⟨V ∩ W, inter_mem hV hW, C, fun x hx y hy => ?_⟩
    change edist (airy1ContL h L x f) (airy1ContL h L y f) ≤ _
    rw [hEq x hx.1, hEq y hy.1]
    exact hC x hx.2 y hy.2
  · refine ⟨univ, univ_mem, 0, fun x _ y _ => ?_⟩
    simp [airy1ContL, hf]

/-- **`Ã_L` takes values in `[L, ∞)`** (for every path). -/
theorem airy1ContL_ge (h : Airy1FddPositive) (L : ℝ) (t : ℝ≥0) (f : ℝ → ℝ) :
    L ≤ airy1ContL h L t f := by
  classical
  by_cases hf : f ∈ goodSet h L
  · obtain ⟨n₀, hn₀⟩ := airy1ContL_eq_clampMod hf (⌈t⌉₊ + 1)
    have ht : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ≥0) := by
      have := Nat.le_ceil t
      push_cast
      exact lt_of_le_of_lt this (lt_add_one _)
    rw [hn₀ t ht]
    exact (clampMod_mem hf n₀ t).1
  · simp [airy1ContL, hf]

/-- **`Ã_L` is a modification of `max L (f t)`** under `airy1Law h`. -/
theorem airy1ContL_ae_eq (h : Airy1FddPositive) (L : ℝ) (t : ℝ≥0) :
    airy1ContL h L t =ᵐ[airy1Law h] fun f => max L (f t) := by
  have h1 : ∀ᵐ f ∂airy1Law h, ∀ n : ℕ, clampMod h L n t f = clampTo L (L + n) (f t) :=
    ae_all_iff.2 fun n => clampMod_ae_eq h L n t
  filter_upwards [h1, ae_mem_goodSet h L] with f hf1 hf2
  simp only [airy1ContL, hf2, ↓reduceIte, hf1]
  exact iSup_clampTo L (f t)

/-- **Continuous version, main statement.** For every lower level `L` there is a process `Ã : ℝ≥0 → (ℝ → ℝ) → ℝ` with
measurable marginals, every path continuous, locally `β`-Hölder for all `β < 1/2` and `≥ L`,
which is a modification of `t ↦ max L (f t)` under the Airy₁ law `airy1Law h`. -/
theorem exists_continuous_version_max (h : Airy1FddPositive) (L : ℝ) :
    ∃ A : ℝ≥0 → (ℝ → ℝ) → ℝ, (∀ t, Measurable (A t))
      ∧ (∀ t, A t =ᵐ[airy1Law h] fun f => max L (f t))
      ∧ (∀ f, Continuous (A · f))
      ∧ (∀ f t, L ≤ A t f)
      ∧ ∀ f t (β : ℝ≥0), 0 < β → (β : ℝ) < 1 / 2 →
        ∃ V ∈ 𝓝 t, ∃ C, HolderOnWith C β (A · f) V :=
  ⟨airy1ContL h L, measurable_airy1ContL h L, airy1ContL_ae_eq h L,
    continuous_airy1ContL h L, fun f t => airy1ContL_ge h L t f, holder_airy1ContL h L⟩

end Airy1Gumbel
