/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.BlockLaw
import Airy1Gumbel.MeshHitting
import Airy1GumbelContrib.Mesh.TwoBlockMesh

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

/-!
# The two-interval law on `Ã` as a theorem

For the continuous version `Ã = airy1ContR h` under
`airy1Law h`, two unit blocks `[x, x+1]` and `[x+1+r, x+2+r]` (`x ≥ 0`, gap `r > 0`), a level
`M > 0` and a weight `a ≥ r + 3`:

  `ℙ(Ã ≤ M on [x, x+1] ∪ [x+1+r, x+2+r]) = det(I − K̃∪)`, `K̃∪ = AiryTwoInt.kcupKerT a M r`

(`airy1Law_two_blocks_le_eq_fredholmDet`), with no kernel hypothesis left: the one-block fact
`MeshHittingLimit M 1` is the theorem `meshHittingLimit` (`MeshHitting.lean`).

Proof outline (as `BlockLaw.lean`, for two blocks).
* The event is the intersection over `n` of the two-block mesh events at mesh level `n + 1`
  (`setOf_two_blocks_eq_iInter`; continuity of every path on `[0, ∞)`, nested meshes).
* Each two-block mesh event has probability `airy1FinCdf (I_{n+1}(x) ∪ I_{n+1}(x+1+r)) (M, …, M)`
  (`airy1Law_twoMeshEvent`, `airy1Law_fdd`).
* Contrib `AiryFdd.tendsto_airy1FinCdf_cupSet` (the union mesh kernel
  `Λ_m ⋆ (P_r ⋆ Λ_m)`, its a.e. limit `D_r = P₁P_rP₁ − ΛP_rΛ` with domination, and the common
  right factor `W_{2+r,a}`) gives the limit `det(I − K̃∪)`.

Weight and guard. The union entries have total time `2 + r`, so the fdd operator is admissible
at weight `a` iff `r + 3 ≤ a`. At `a = √(2u)`, `r = j − 1`, this is `j + 2 ≤ √(2u)`: exactly the
guard of `QRTwoIntervalLaw` and the admissibility test inside `detKCup u (j − 1)`, whose operator
is `kcupKerT √(2u) u (j − 1)`. No weight change is needed.

Records.
* `qrTwoIntervalLaw_airy1`: `QRTwoIntervalLaw (airy1BlockMax h) (airy1Law h)` is a **theorem**
  under `Airy1FddPositive` and `GOELeftTail` only.
* `gumbel_limit_continuum_real_normalized_airy1_of_QR₁₀`: the concrete headline with all three QR
  block-law records discharged (`qrUnitBlockLaw_airy1`, `qrTwoBlockLaw_airy1` with the
  unconditional `forall_meshHittingLimit`, and `qrTwoIntervalLaw_airy1`). Remaining hypotheses:
  `h`, `hT`, `CubicStrongMixing`, `CubicCovarianceDecay`, `ProcessAssociated`,
  `HighLevelUpcrossingTail`. (Index `₁₀`: the variant `_of_QR₉` in
  `UpcrossingTheorem.lean` discharges `HighLevelUpcrossingTail` instead; both are combined in
  `gumbel_limit_continuum_real_normalized_airy1_final`, `FinalHeadline.lean`.)
-/

namespace Airy1Gumbel

/-- Block `j` of `Ã` is below `u` iff `Ã ≤ u` on `[j, j + 1]`. -/
theorem airy1BlockMax_le_iff (h : Airy1FddPositive) (j : ℕ) (f : ℝ → ℝ) (u : ℝ) :
    airy1BlockMax h j f ≤ u ↔ ∀ t ∈ Icc (j : ℝ) (j + 1), airy1ContR h t f ≤ u := by
  have hc : ContinuousOn (fun t => airy1ContR h t f) (Icc (j : ℝ) (j + 1)) :=
    (continuousOn_airy1ContR h f).mono fun _ ht => (Nat.cast_nonneg j).trans ht.1
  have hbdd := (isCompact_Icc.image_of_continuousOn hc).bddAbove
  have hne : ((fun t => airy1ContR h t f) '' Icc (j : ℝ) (j + 1)).Nonempty :=
    (nonempty_Icc.2 (by linarith)).image _
  unfold airy1BlockMax
  rw [csSup_le_iff hbdd hne, forall_mem_image]

/-- **The two-block event is the intersection of the two-block mesh events** at mesh levels
`n + 1` (every path of `Ã` is continuous on `[0, ∞)`, `x, y ≥ 0`). -/
theorem setOf_two_blocks_eq_iInter (h : Airy1FddPositive) {x y M : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    {f | (∀ t ∈ Icc x (x + 1), airy1ContR h t f ≤ M) ∧
        ∀ t ∈ Icc y (y + 1), airy1ContR h t f ≤ M}
      = ⋂ n, (meshEvent h x 1 M (n + 1) ∩ meshEvent h y 1 M (n + 1)) := by
  ext f
  have hcx := forall_Icc_le_iff_forall_meshSet (g := fun t => airy1ContR h t f) (M := M)
    one_pos ((continuousOn_airy1ContR h f).mono fun t ht => hx.trans ht.1)
  have hcy := forall_Icc_le_iff_forall_meshSet (g := fun t => airy1ContR h t f) (M := M)
    one_pos ((continuousOn_airy1ContR h f).mono fun t ht => hy.trans ht.1)
  change ((∀ t ∈ Icc x (x + 1), airy1ContR h t f ≤ M) ∧
      ∀ t ∈ Icc y (y + 1), airy1ContR h t f ≤ M) ↔
    f ∈ ⋂ n, (meshEvent h x 1 M (n + 1) ∩ meshEvent h y 1 M (n + 1))
  rw [hcx, hcy, mem_iInter]
  constructor
  · rintro ⟨h1, h2⟩ n
    exact ⟨h1 (n + 1), h2 (n + 1)⟩
  · intro hn
    exact ⟨fun n t ht => (hn n).1 t (meshSet_subset_succ x 1 n ht),
      fun n t ht => (hn n).2 t (meshSet_subset_succ y 1 n ht)⟩

/-- Each two-block mesh event has the Airy₁ fdd probability on the union mesh. -/
theorem airy1Law_twoMeshEvent (h : Airy1FddPositive) (hT : GOELeftTail) (x y M : ℝ) (n : ℕ) :
    (airy1Law h).real (meshEvent h x 1 M n ∩ meshEvent h y 1 M n)
      = AiryFdd.airy1FinCdf (AiryFdd.meshSet x 1 n ∪ AiryFdd.meshSet y 1 n) (fun _ => M) := by
  set I := AiryFdd.meshSet x 1 n ∪ AiryFdd.meshSet y 1 n with hI
  have hae : meshEvent h x 1 M n ∩ meshEvent h y 1 M n =ᵐ[airy1Law h]
      {f : ℝ → ℝ | ∀ t ∈ I, f t ≤ (fun _ => M) t} := by
    have hall : ∀ᵐ f ∂airy1Law h, ∀ t ∈ I, airy1ContR h t f = f t :=
      (eventually_all_finset _).2 fun t _ => airy1ContR_ae_eq h hT t
    filter_upwards [hall] with f hf
    refine propext ?_
    change ((∀ t ∈ AiryFdd.meshSet x 1 n, airy1ContR h t f ≤ M) ∧
        ∀ t ∈ AiryFdd.meshSet y 1 n, airy1ContR h t f ≤ M) ↔ ∀ t ∈ I, f t ≤ M
    constructor
    · rintro ⟨h1, h2⟩ t ht
      rw [← hf t ht]
      rcases Finset.mem_union.1 ht with ht | ht
      · exact h1 t ht
      · exact h2 t ht
    · intro h'
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · rw [hf t (Finset.mem_union_left _ ht)]; exact h' t (Finset.mem_union_left _ ht)
      · rw [hf t (Finset.mem_union_right _ ht)]; exact h' t (Finset.mem_union_right _ ht)
  rw [measureReal_def, measure_congr hae, ← measureReal_def, airy1Law_fdd]

/-- **Two-block law.** Under `Airy1FddPositive` and `GOELeftTail`, for `x ≥ 0`,
gap `r > 0`, level `M > 0` and weight `a ≥ r + 3`:
`ℙ(Ã ≤ M on [x, x+1] and on [x+1+r, x+2+r]) = det(I − K̃∪)`, `K̃∪ = kcupKerT a M r`. -/
theorem airy1Law_two_blocks_le_eq_fredholmDet (h : Airy1FddPositive) (hT : GOELeftTail)
    {x M r a : ℝ} (hx : 0 ≤ x) (hr : 0 < r) (hM : 0 < M) (ha : r + 3 ≤ a) :
    (airy1Law h).real {f | (∀ t ∈ Icc x (x + 1), airy1ContR h t f ≤ M) ∧
        ∀ t ∈ Icc (x + 1 + r) (x + 1 + r + 1), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (HilbertSchmidt.kernelOperator (AiryTwoInt.memLp_kcupKerT hr hM ha)) 1 := by
  rw [setOf_two_blocks_eq_iInter h hx (by linarith)]
  have hanti : Antitone fun n =>
      meshEvent h x 1 M (n + 1) ∩ meshEvent h (x + 1 + r) 1 M (n + 1) :=
    fun n m hnm => inter_subset_inter (antitone_meshEvent h x 1 M (Nat.succ_le_succ hnm))
      (antitone_meshEvent h (x + 1 + r) 1 M (Nat.succ_le_succ hnm))
  have hlim := tendsto_measure_iInter_atTop (μ := airy1Law h)
    (fun n => ((measurableSet_meshEvent h x 1 M (n + 1)).inter
      (measurableSet_meshEvent h (x + 1 + r) 1 M (n + 1))).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  have hlimR : Tendsto (fun n => (airy1Law h).real
        (meshEvent h x 1 M (n + 1) ∩ meshEvent h (x + 1 + r) 1 M (n + 1))) atTop
      (𝓝 ((airy1Law h).real
        (⋂ n, (meshEvent h x 1 M (n + 1) ∩ meshEvent h (x + 1 + r) 1 M (n + 1))))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim
  simp_rw [airy1Law_twoMeshEvent h hT] at hlimR
  exact tendsto_nhds_unique hlimR
    (AiryFdd.tendsto_airy1FinCdf_cupSet x hr hM ha (meshHittingLimit M one_pos))

/-- **`QRTwoIntervalLaw` on `Ã` is a theorem** (the paper's two-interval
determinant formula at `T = 1`), under `Airy1FddPositive` and `GOELeftTail` only: for every level `u` and every
block index `j ≥ 2` with `j + 2 ≤ √(2u)`, the two-block law at `x = 0`, gap `r = j − 1`, weight
`a = √(2u)` (admissible: `r + 3 = j + 2 ≤ √(2u)`), which is `detKCup u (j − 1)` on its
admissible branch. -/
theorem qrTwoIntervalLaw_airy1 (h : Airy1FddPositive) (hT : GOELeftTail) :
    QRTwoIntervalLaw (airy1BlockMax h) (airy1Law h) where
  law := by
    refine Eventually.of_forall fun u j hj hju => ?_
    have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
    have hr : 0 < (j : ℝ) - 1 := by linarith
    have hsq : 0 < Real.sqrt (2 * u) := by linarith
    have hu : 0 < u := by
      have := Real.sqrt_pos.1 hsq
      linarith
    have ha : (j : ℝ) - 1 + 3 ≤ Real.sqrt (2 * u) := by linarith
    have hset : {f : ℝ → ℝ | airy1BlockMax h 0 f ≤ u ∧ airy1BlockMax h j f ≤ u}
        = {f | (∀ t ∈ Icc (0 : ℝ) (0 + 1), airy1ContR h t f ≤ u) ∧
            ∀ t ∈ Icc (0 + 1 + ((j : ℝ) - 1)) (0 + 1 + ((j : ℝ) - 1) + 1),
              airy1ContR h t f ≤ u} := by
      ext f
      have hj' : (0 : ℝ) + 1 + ((j : ℝ) - 1) = j := by ring
      change (airy1BlockMax h 0 f ≤ u ∧ airy1BlockMax h j f ≤ u) ↔ _
      rw [airy1BlockMax_le_iff, airy1BlockMax_le_iff, hj', Nat.cast_zero]
      rfl
    rw [hset, airy1Law_two_blocks_le_eq_fredholmDet h hT le_rfl hr hu ha, detKCup,
      dite_eq_left ⟨hr, hu, ha⟩]

/-! ## The main theorem with all three Quastel–Remenik block-law records discharged -/

/-- **Main theorem `_of_QR₁₀` on the Airy₁ law** (Theorem 1.1 of the paper, normalized real-length
form, on `Ã = airy1ContR h`): `gumbel_limit_continuum_real_normalized_airy1_of_QR₆` with
`QRUnitBlockLaw`, `QRTwoBlockLaw` and `QRTwoIntervalLaw` all discharged (`qrUnitBlockLaw_airy1`
and `qrTwoBlockLaw_airy1` with the unconditional `forall_meshHittingLimit`, and
`qrTwoIntervalLaw_airy1`). Remaining hypotheses: `h`, `hT`, `CubicStrongMixing`,
`CubicCovarianceDecay`, `ProcessAssociated` and `HighLevelUpcrossingTail` on `Ã` (`U`; it is
discharged in `gumbel_limit_continuum_real_normalized_airy1_final`). -/
theorem gumbel_limit_continuum_real_normalized_airy1_of_QR₁₀ (h : Airy1FddPositive)
    (hT : GOELeftTail)
    (M : CubicStrongMixing (airy1SRP h hT)) (Cov : CubicCovarianceDecay (airy1SRP h hT))
    (As : ProcessAssociated (airy1SRP h hT)) (U : HighLevelUpcrossingTail (airy1SRP h hT))
    (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law h).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR h x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  gumbel_limit_continuum_real_normalized_airy1_of_QR₆ h hT
    (qrUnitBlockLaw_airy1 h hT (forall_meshHittingLimit one_pos))
    (qrTwoBlockLaw_airy1 h hT (forall_meshHittingLimit two_pos))
    (qrTwoIntervalLaw_airy1 h hT) M Cov As U z

end Airy1Gumbel
