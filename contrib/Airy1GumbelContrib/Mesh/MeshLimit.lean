/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Fdd.FddIndep
import Airy1GumbelContrib.Fdd.FddCont

/-!
# Dyadic mesh fdd and the conditional mesh limit

Fix a level `M`, a block length `T` and a level
of refinement `n`; put `g = T / 2ⁿ`.

* **Mesh times.** `meshSet x T n = {x, x + g, …, x + (2ⁿ − 1) g}` (`mem_meshSet`), built from
  the explicit list `meshTimes x g (2ⁿ)` (strictly increasing, so it is its own sort).
* **Mesh entries.** At constant level `M` and padding `g`, the entries are `(M, g)` repeated
  `2ⁿ` times: head `(M, g)` and tail `meshTail M T n = replicate (2ⁿ − 1) (M, g)`, total time
  `gapSum = 2ⁿ g = T` exactly (`gapSum_meshTail`).  The mesh hitting kernel is
  `meshHitKer M T n = hitKerN (M, g) (meshTail M T n)` (projections at the `2ⁿ` grid times,
  none at `T`; `= p_T − (P̄_M e^{gΔ})^{2ⁿ}`).
* **Step D** (`airy1FinCdf_meshSet`): `F_{I_n}(M, …, M) = det(I − meshOp M T n)` where
  `meshOp = fddOpAt (M, g) (meshTail M T n) … (2T)`; admissible because `T + 1 ≤ 2T` for
  `T ≥ 1`.  The weight `2T` and the total time `T` are those of `airyTildeOp M T (2T)`, so the
  two `W` factors are the same kernel `wKernel T (2T)` (`meshOp_eq`).
* **Step O** (`tendsto_fredholmDet_meshOp`): under the kernel hypotheses
  `MeshHittingLimit M T` — (K1) `H_n ≤ Q_{M,T}` a.e. for every `n` and (K2) `H_n → Q_{M,T}`
  a.e. (the lower bound `0 ≤ H_n` is `hitKerN_nonneg`, a theorem) — the `V` kernels converge
  in `L²` (dominated by `V²`), hence `det(I − meshOp M T n) → det(I − airyTildeOp M T (2T))`.
* **Combined** (`tendsto_airy1FinCdf_meshSet`): under `MeshHittingLimit M T`, `T ≥ 1`,
  `M > 0`: `F_{I_n}(M, …, M) → det(I − Ã_{M,T})`.
* Orientation checks: at `n = 0` (one time) (K1) holds (`meshHitKer_zero_le_qMT`), while the
  reversed inequality `Q_{M,T} ≤ H_0` fails (`not_qMT_le_meshHitKer_zero`).

The kernel facts (K1)/(K2) themselves — the dyadic Brownian-bridge maximum law — are not proved
here; they are proved from Brownian motion in `Mesh/Skeleton.lean` and `Mesh/Reflection.lean`.
-/

namespace AiryFdd

open MeasureTheory Real Set Filter Topology
open HilbertSchmidt

/-! ## Mesh times -/

/-- The arithmetic progression `x, x + g, …, x + (k − 1) g` as a list. -/
def meshTimes : ℝ → ℝ → ℕ → List ℝ
  | _, _, 0 => []
  | x, g, k + 1 => x :: meshTimes (x + g) g k

theorem mem_meshTimes {g : ℝ} : ∀ (k : ℕ) (x t : ℝ),
    t ∈ meshTimes x g k ↔ ∃ i : ℕ, i < k ∧ t = x + i * g
  | 0, x, t => by simp [meshTimes]
  | k + 1, x, t => by
    simp only [meshTimes, List.mem_cons, mem_meshTimes k (x + g) t]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, Nat.succ_pos k, by simp⟩
      · exact ⟨i + 1, by omega, by push_cast; ring⟩
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | zero => left; simp
      | succ i => right; exact ⟨i, by omega, by push_cast; ring⟩

theorem le_of_mem_meshTimes {g : ℝ} (hg : 0 ≤ g) {k : ℕ} {x t : ℝ}
    (ht : t ∈ meshTimes x g k) : x ≤ t := by
  obtain ⟨i, -, rfl⟩ := (mem_meshTimes k x t).1 ht
  have : 0 ≤ (i : ℝ) * g := mul_nonneg i.cast_nonneg hg
  linarith

theorem meshTimes_pairwise_lt {g : ℝ} (hg : 0 < g) :
    ∀ (k : ℕ) (x : ℝ), (meshTimes x g k).Pairwise (· < ·)
  | 0, _ => List.Pairwise.nil
  | k + 1, x => by
    refine List.pairwise_cons.2 ⟨fun t ht => ?_, meshTimes_pairwise_lt hg k (x + g)⟩
    have := le_of_mem_meshTimes hg.le ht
    linarith

/-- The dyadic mesh step `g = T / 2ⁿ`. -/
noncomputable def meshGap (T : ℝ) (n : ℕ) : ℝ := T / 2 ^ n

theorem meshGap_pos {T : ℝ} (hT : 0 < T) (n : ℕ) : 0 < meshGap T n := by
  unfold meshGap; positivity

/-- **The dyadic time set** `I_n = {x + k T / 2ⁿ : k < 2ⁿ}`. -/
noncomputable def meshSet (x T : ℝ) (n : ℕ) : Finset ℝ :=
  (meshTimes x (meshGap T n) (2 ^ n)).toFinset

theorem mem_meshSet {x T t : ℝ} {n : ℕ} :
    t ∈ meshSet x T n ↔ ∃ k : ℕ, k < 2 ^ n ∧ t = x + k * (T / 2 ^ n) := by
  unfold meshSet
  rw [List.mem_toFinset, mem_meshTimes]
  rfl

/-- The sorted list of the mesh times is the progression itself. -/
theorem sort_meshSet {x T : ℝ} (hT : 0 < T) (n : ℕ) :
    (meshSet x T n).sort (· ≤ ·) = meshTimes x (meshGap T n) (2 ^ n) := by
  have hlt := meshTimes_pairwise_lt (meshGap_pos hT n) (2 ^ n) x
  have hnd : (meshTimes x (meshGap T n) (2 ^ n)).Nodup := hlt.imp fun h => h.ne
  have hle : (meshTimes x (meshGap T n) (2 ^ n)).Pairwise (· ≤ ·) := hlt.imp fun h => h.le
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Finset.pairwise_sort _ _) hle ?_
  refine List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _) hnd ?_
  rw [Finset.sort_toFinset]
  rfl

/-! ## Mesh entries -/

/-- The mesh tail: `(M, g)` repeated `2ⁿ − 1` times (head `(M, g)` gives `2ⁿ` entries). -/
noncomputable def meshTail (M T : ℝ) (n : ℕ) : List (ℝ × ℝ) :=
  List.replicate (2 ^ n - 1) (M, meshGap T n)

theorem gapSum_replicate : ∀ (k : ℕ) (e e' : ℝ × ℝ),
    gapSum e (List.replicate k e') = e.2 + k * e'.2
  | 0, e, _ => by simp [gapSum]
  | k + 1, e, e' => by
    rw [List.replicate_succ]
    show e.2 + gapSum e' (List.replicate k e') = _
    rw [gapSum_replicate k e' e']
    push_cast; ring

/-- The mesh entries have total time exactly `T`. -/
theorem gapSum_meshTail (M T : ℝ) (n : ℕ) : gapSum (M, meshGap T n) (meshTail M T n) = T := by
  unfold meshTail
  rw [gapSum_replicate]
  have h1 : ((2 ^ n - 1 : ℕ) : ℝ) = (2 : ℝ) ^ n - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  simp only
  rw [h1, meshGap]
  field_simp
  ring

theorem meshTail_pos {M T : ℝ} (hT : 0 < T) (n : ℕ) : ∀ y ∈ meshTail M T n, 0 < y.2 := by
  intro y hy
  rw [meshTail, List.mem_replicate] at hy
  rw [hy.2]
  exact meshGap_pos hT n

/-- The mesh hitting kernel `H_n = p_T − (P̄_M e^{gΔ})^{2ⁿ}`, `g = T/2ⁿ`. -/
noncomputable def meshHitKer (M T : ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  hitKerN (M, meshGap T n) (meshTail M T n)

theorem meshHitKer_nonneg {M T : ℝ} (hT : 0 < T) (n : ℕ) (p : ℝ × ℝ) :
    0 ≤ meshHitKer M T n p :=
  hitKerN_nonneg (meshGap_pos hT n) (meshTail_pos hT n) p

theorem measurable_meshHitKer {M T : ℝ} (hT : 0 < T) (n : ℕ) :
    Measurable (meshHitKer M T n) :=
  measurable_hitKerN (meshGap_pos hT n) (meshTail_pos hT n)

theorem meshAdm {M T : ℝ} (hT : 1 ≤ T) (n : ℕ) :
    gapSum (M, meshGap T n) (meshTail M T n) + 1 ≤ 2 * T := by
  rw [gapSum_meshTail]; linarith

/-- **The mesh fdd operator** `T_{V_n} ∘ T_W` at weight `2T` (padding `g`, total time `T`). -/
noncomputable def meshOp (M T : ℝ) (n : ℕ) (hT : 1 ≤ T) :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  fddOpAt (M, meshGap T n) (meshTail M T n) (meshGap_pos (by linarith) n)
    (meshTail_pos (by linarith) n) (2 * T) (meshAdm hT n)

/-- The entries of a progression at constant level have the same levels and interior gaps as
`(M, g)` repeated. -/
theorem fddEntries_meshTimes {g M : ℝ} (lev : ℝ → ℝ) : ∀ (k : ℕ) (x : ℝ),
    (∀ t ∈ meshTimes x g (k + 1), lev t = M) →
      ∃ e L, fddEntries lev (meshTimes x g (k + 1)) = e :: L ∧
        SamePad e L (M, g) (List.replicate k (M, g))
  | 0, x, h => by
    refine ⟨(lev x, 1), [], rfl, ?_⟩
    simp only [List.replicate_zero, SamePad]
    exact h x (by simp [meshTimes])
  | k + 1, x, h => by
    obtain ⟨e, L, hEL, hsp⟩ := fddEntries_meshTimes lev k (x + g)
      (fun t ht => h t (List.mem_cons_of_mem _ ht))
    refine ⟨(lev x, x + g - x), e :: L, ?_, ?_⟩
    · show fddEntries lev (x :: meshTimes (x + g) g (k + 1)) = _
      rw [← hEL]
      rfl
    · rw [List.replicate_succ]
      refine ⟨?_, hsp⟩
      rw [h x List.mem_cons_self, add_sub_cancel_left]

/-- **Step D (mesh fdd identity).** At constant level `M` on the dyadic mesh
`I_n = {x + kT/2ⁿ : k < 2ⁿ}`, `T ≥ 1`: `F_{I_n}(M, …, M) = det(I − meshOp M T n)`
(padding `T/2ⁿ`, so the total time is `T`; weight `2T`). -/
theorem airy1FinCdf_meshSet (x M T : ℝ) (hT : 1 ≤ T) (n : ℕ) :
    airy1FinCdf (meshSet x T n) (fun _ => M) = fredholmDet (meshOp M T n hT) 1 := by
  have hT0 : 0 < T := by linarith
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
  have hlev : ∀ t ∈ meshTimes x (meshGap T n) (k + 1),
      levelFn (meshSet x T n) (fun _ => M) t = M := by
    intro t ht
    have : t ∈ meshSet x T n := by
      unfold meshSet; rw [List.mem_toFinset, hk]; exact ht
    simp only [levelFn, this, ↓reduceDIte]
  obtain ⟨e, L, hEL, hsp⟩ := fddEntries_meshTimes _ k x hlev
  have hfin : finEntries (meshSet x T n) (fun _ => M) = e :: L := by
    unfold finEntries
    rw [sort_meshSet hT0, hk]
    exact hEL
  have htail : meshTail M T n = List.replicate k (M, meshGap T n) := by
    unfold meshTail; rw [hk]; rfl
  unfold meshOp
  rw [airy1FinCdf_eq_fredholmDet_fddOpAt _ _ hfin (htail ▸ hsp) (meshGap_pos hT0 n)
    (meshTail_pos hT0 n) (meshAdm hT n)]

/-! ## The common `W` factor -/

/-- `meshOp` with the `W` factor written as `wKernel T (2T)` — the `W` factor of
`airyTildeOp M T (2T)`. -/
theorem meshOp_eq (M T : ℝ) (n : ℕ) (hT : 1 ≤ T) :
    meshOp M T n hT
      = kernelOperator (memLp_fddVKer (M, meshGap T n) (meshTail M T n)
          (meshGap_pos (by linarith) n) (meshTail_pos (by linarith) n)
          (a := 2 * T) (by linarith)) ∘L
        kernelOperator (AiryConj.memLp_wKernel (T := T) (a := 2 * T) (by linarith)
          (by linarith)) := by
  unfold meshOp fddOpAt
  congr 1
  exact AiryTwoInt.kernelOperator_congr (by rw [gapSum_meshTail]) _ _

/-! ## The kernel hypotheses and Step O -/

/-- **The dyadic hitting-kernel limit** (constant level `M`, block `T`):
(K1) `H_n ≤ Q_{M,T}` a.e. on `ℝ²` for every `n`; (K2) `H_n → Q_{M,T}` a.e.  Here
`H_n = meshHitKer M T n` and `Q_{M,T} = AiryConj.qMT M T` (the reflected heat kernel).  The
lower bound `0 ≤ H_n` is a theorem (`meshHitKer_nonneg`). -/
structure MeshHittingLimit (M T : ℝ) : Prop where
  le_qMT : ∀ n : ℕ, ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
    meshHitKer M T n p ≤ AiryConj.qMT M T p.1 p.2
  tendsto_qMT : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
    Tendsto (fun n => meshHitKer M T n p) atTop (𝓝 (AiryConj.qMT M T p.1 p.2))

theorem qMT_nonneg {M T : ℝ} (hT : 0 < T) (x z : ℝ) : 0 ≤ AiryConj.qMT M T x z := by
  unfold AiryConj.qMT
  split_ifs
  · exact (heatKernel_pos hT _).le
  · exact (heatKernel_pos hT _).le

/-- The positive weight of `fddVKer`: `fddVKer H a p = w(p) H(p)`. -/
theorem fddVKer_eq_mul (H : ℝ × ℝ → ℝ) (a : ℝ) (p : ℝ × ℝ) :
    fddVKer H a p
      = (Real.exp (-a * p.1) * Real.exp (-a * p.2) * AiryConj.phiWeight p.2) * H p := by
  unfold fddVKer; ring

/-- `(wh − wq)² ≤ (wq)²` when `0 ≤ h ≤ q`. -/
theorem sq_mul_sub_le_sq_mul (w h q : ℝ) (h0 : 0 ≤ h) (hq : h ≤ q) :
    (w * h - w * q) ^ 2 ≤ (w * q) ^ 2 := by
  have e1 : (w * h - w * q) ^ 2 = w ^ 2 * (q - h) ^ 2 := by ring
  have e2 : (w * q) ^ 2 = w ^ 2 * q ^ 2 := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sub_nonneg.2 hq) (sub_le_self _ h0) 2) (sq_nonneg w)

/-- **Step O, kernel half.** Under (K1)/(K2), `∫∫ (V_n − V)² → 0` with
`V_n = fddVKer H_n (2T)` and `V = vKernel T (2T) M`. -/
theorem tendsto_integral_sq_meshVKer {M T : ℝ} (hT : 1 ≤ T) (hM : 0 < M)
    (hK : MeshHittingLimit M T) :
    Tendsto (fun n => ∫ p, (fddVKer (meshHitKer M T n) (2 * T) p
        - AiryConj.vKernel T (2 * T) M p) ^ 2 ∂(volume.prod volume)) atTop (𝓝 0) := by
  have hT0 : 0 < T := by linarith
  have hV := AiryConj.vKernel_memLp hT0 hM (a := 2 * T) (by linarith)
  have hint : Integrable (fun p => AiryConj.vKernel T (2 * T) M p ^ 2)
      (volume.prod volume) := hV.integrable_sq
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.prod volume)
    (l := atTop) (f := fun _ => (0 : ℝ)) (fun p => AiryConj.vKernel T (2 * T) M p ^ 2)
    (F := fun n p => (fddVKer (meshHitKer M T n) (2 * T) p
        - AiryConj.vKernel T (2 * T) M p) ^ 2)
    (Eventually.of_forall fun n =>
      (((measurable_fddVKer (measurable_meshHitKer hT0 n) _).sub
        (AiryConj.measurable_vKernel T _ M)).pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall fun n => by
      filter_upwards [hK.le_qMT n] with p hp
      rw [Real.norm_of_nonneg (sq_nonneg _), ← fddVKer_qMT, fddVKer_eq_mul, fddVKer_eq_mul]
      exact sq_mul_sub_le_sq_mul _ _ _ (meshHitKer_nonneg hT0 n p) hp)
    hint
    (by
      filter_upwards [hK.tendsto_qMT] with p hp
      have h1 : Tendsto (fun n => fddVKer (meshHitKer M T n) (2 * T) p) atTop
          (𝓝 (AiryConj.vKernel T (2 * T) M p)) := by
        rw [← fddVKer_qMT, fddVKer_eq_mul]
        simp_rw [fddVKer_eq_mul]
        exact hp.const_mul _
      simpa using (h1.sub_const (AiryConj.vKernel T (2 * T) M p)).pow 2)
  simpa using hlim

/-- **Step O.** Under (K1)/(K2), `det(I − meshOp M T n) → det(I − Ã_{M,T})` at weight `2T`. -/
theorem tendsto_fredholmDet_meshOp {M T : ℝ} (hT : 1 ≤ T) (hM : 0 < M)
    (hK : MeshHittingLimit M T) :
    Tendsto (fun n => fredholmDet (meshOp M T n hT) 1) atTop
      (𝓝 (fredholmDet (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1)) := by
  simp_rw [meshOp_eq M T _ hT]
  exact tendsto_fredholmDet_kernelOperator_comp _ _ _ (tendsto_integral_sq_meshVKer hT hM hK) 1

/-- **Combined.** Under the dyadic hitting-kernel limit (K1)/(K2), `T ≥ 1`, `M > 0`,
for every base point `x`: `F_{I_n}(M, …, M) → det(I − Ã_{M,T})` with `Ã_{M,T}` at weight `2T`,
where `I_n = {x + kT/2ⁿ : k < 2ⁿ}`. -/
theorem tendsto_airy1FinCdf_meshSet (x : ℝ) {M T : ℝ} (hT : 1 ≤ T) (hM : 0 < M)
    (hK : MeshHittingLimit M T) :
    Tendsto (fun n => airy1FinCdf (meshSet x T n) (fun _ => M)) atTop
      (𝓝 (fredholmDet (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1)) := by
  simp_rw [airy1FinCdf_meshSet x M T hT]
  exact tendsto_fredholmDet_meshOp hT hM hK

/-! ## Orientation checks at `n = 0` -/

theorem meshHitKer_zero (M T : ℝ) (p : ℝ × ℝ) :
    meshHitKer M T 0 p = (Ioi M).indicator (fun _ => (1 : ℝ)) p.1 * heatKernel T (p.1 - p.2) := by
  have : meshTail M T 0 = [] := rfl
  rw [meshHitKer, this, hitKerN_one]
  simp [meshGap]

/-- (K1) at `n = 0` (one grid time): `H_0 = 1_{u > M} p_T(u − v) ≤ Q_{M,T}` everywhere. -/
theorem meshHitKer_zero_le_qMT {M T : ℝ} (hT : 0 < T) (p : ℝ × ℝ) :
    meshHitKer M T 0 p ≤ AiryConj.qMT M T p.1 p.2 := by
  rw [meshHitKer_zero]
  by_cases h : p.1 ∈ Ioi M
  · rw [Set.indicator_of_mem h, one_mul,
      AiryConj.qMT_eq_free (fun hh => absurd hh.1 (not_le.2 h))]
  · rw [Set.indicator_of_notMem h, zero_mul]
    exact qMT_nonneg hT _ _

/-- Orientation witness: the reversed (K1) inequality `Q_{M,T} ≤ H_0` fails at `(M, M)`. -/
theorem not_qMT_le_meshHitKer_zero {M T : ℝ} (hT : 0 < T) :
    ¬ AiryConj.qMT M T M M ≤ meshHitKer M T 0 (M, M) := by
  rw [meshHitKer_zero, Set.indicator_of_notMem (show M ∉ Ioi M from lt_irrefl M), zero_mul,
    not_le]
  simp only [AiryConj.qMT, le_refl, and_self, ↓reduceIte]
  exact heatKernel_pos hT _

end AiryFdd
