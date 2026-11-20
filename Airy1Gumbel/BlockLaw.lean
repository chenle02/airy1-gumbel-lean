/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.UpcrossingRecord
import Airy1Gumbel.Touching
import Airy1GumbelContrib.Mesh.MeshLimit

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

/-!
# The QR block laws on `Ã` from the dyadic hitting-kernel limit

The law side of the block laws. For the continuous version
`Ã = airy1ContR h` under `airy1Law h`, `T ≥ 1`, `M > 0` and any base point `x ≥ 0`:

  `ℙ(Ã(t) ≤ M ∀ t ∈ [x, x+T]) = det(I − Ã_{M,T})`, `Ã_{M,T} = AiryConj.airyTildeOp M T (2T)`

(`airy1Law_sup_le_eq_fredholmDet`), given contrib's dyadic hitting-kernel limit
`AiryFdd.MeshHittingLimit M T` (the kernel fact K: (K1) domination, (K2) a.e. convergence).

Route.
* The event `{Ã ≤ M on [x, x+T]}` is the intersection over `n` of the mesh events
  `{Ã(t) ≤ M ∀ t ∈ I_n}`, `I_n = AiryFdd.meshSet x T n = {x + kT/2ⁿ : k < 2ⁿ}`
  (`setOf_forall_Icc_le_eq_iInter`): every path of `Ã` is continuous on `[0, ∞)` and every
  `t ∈ [x, x+T]` is the limit of mesh points `s_n ∈ I_n` with `t − T/2ⁿ ≤ s_n ≤ t`
  (`exists_meshSet_near`). The right endpoint `x + T ∉ I_n` is reached from the left.
* The meshes are nested (`meshSet_subset_succ`), so the mesh events decrease, and continuity of
  the measure from above gives convergence of their probabilities.
* At the finitely many mesh times `Ã` agrees a.s. with the coordinates, so each mesh event has
  probability `airy1FinCdf I_n (M, …, M)` (`airy1Law_fdd`), which converges to
  `det(I − Ã_{M,T})` by contrib `AiryFdd.tendsto_airy1FinCdf_meshSet` under K.

Records.
* `qrUnitBlockLaw_airy1`: `QRUnitBlockLaw (airy1BlockMax h) (airy1Law h)` is a **theorem** under
  `GOELeftTail` and `∀ M > 0, MeshHittingLimit M 1` (core law at `x = 0`, `T = 1`, complement).
* `qrTwoBlockLaw_airy1`: `QRTwoBlockLaw (airy1BlockMax h) (airy1Law h)` is a **theorem** under
  `GOELeftTail` and `∀ M > 0, MeshHittingLimit M 2` (core law at `x = 0`, `T = 2`, through
  `QRTwoBlockLaw.of_continuum`).
* `gumbel_limit_continuum_real_normalized_airy1_of_QR₇`: the concrete `_of_QR₆` headline with
  `qr` and `qr₂` discharged; the K-hypotheses at `T = 1, 2` replace them. `QRTwoIntervalLaw`
  remains a hypothesis.
-/

namespace Airy1Gumbel

/-! ## Dyadic meshes -/

/-- The dyadic meshes are nested: `I_n ⊆ I_{n+1}`. -/
theorem meshSet_subset_succ (x T : ℝ) (n : ℕ) :
    AiryFdd.meshSet x T n ⊆ AiryFdd.meshSet x T (n + 1) := by
  intro t ht
  obtain ⟨k, hk, rfl⟩ := AiryFdd.mem_meshSet.1 ht
  refine AiryFdd.mem_meshSet.2 ⟨2 * k, by rw [pow_succ]; omega, ?_⟩
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  push_cast
  rw [pow_succ]
  field_simp

theorem meshSet_mono (x T : ℝ) : Monotone (AiryFdd.meshSet x T) :=
  monotone_nat_of_le_succ (meshSet_subset_succ x T)

/-- The mesh lies in `[x, x+T)`. -/
theorem meshSet_subset_Icc {x T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    ↑(AiryFdd.meshSet x T n) ⊆ Icc x (x + T) := by
  intro t ht
  obtain ⟨k, hk, rfl⟩ := AiryFdd.mem_meshSet.1 ht
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hk' : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk.le
  have hg : 0 ≤ T / 2 ^ n := div_nonneg hT h2.le
  refine ⟨le_add_of_nonneg_right (mul_nonneg k.cast_nonneg hg), ?_⟩
  have : (k : ℝ) * (T / 2 ^ n) ≤ 2 ^ n * (T / 2 ^ n) := mul_le_mul_of_nonneg_right hk' hg
  rw [mul_div_cancel₀ _ h2.ne'] at this
  linarith

/-- Every `t ∈ [x, x+T]` has a mesh point `s ∈ I_n` with `t − T/2ⁿ ≤ s ≤ t`. -/
theorem exists_meshSet_near {x T t : ℝ} (hT : 0 < T) (ht : t ∈ Icc x (x + T)) (n : ℕ) :
    ∃ s ∈ AiryFdd.meshSet x T n, t - T / 2 ^ n ≤ s ∧ s ≤ t := by
  set g : ℝ := T / 2 ^ n with hg_def
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hg : 0 < g := div_pos hT h2
  have hgT : (2 : ℝ) ^ n * g = T := by rw [hg_def]; field_simp
  set k : ℕ := min ⌊(t - x) / g⌋₊ (2 ^ n - 1) with hk_def
  have hk : k < 2 ^ n := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt Nat.one_le_two_pow one_pos)
  have htx : 0 ≤ (t - x) / g := div_nonneg (by linarith [ht.1]) hg.le
  refine ⟨x + k * g, AiryFdd.mem_meshSet.2 ⟨k, hk, rfl⟩, ?_, ?_⟩
  · rcases min_choice ⌊(t - x) / g⌋₊ (2 ^ n - 1) with hmin | hmin
    · have h1 := Nat.lt_floor_add_one ((t - x) / g)
      rw [← hk_def, hmin] at *
      rw [div_lt_iff₀ hg] at h1
      nlinarith
    · rw [← hk_def] at hmin
      rw [hmin, Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      nlinarith [ht.2]
  · have hle : (k : ℝ) ≤ (t - x) / g :=
      (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le htx)
    rw [le_div_iff₀ hg] at hle
    linarith

/-- `T/2ⁿ → 0`. -/
theorem tendsto_div_two_pow (T : ℝ) : Tendsto (fun n : ℕ => T / 2 ^ n) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).const_mul T
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  rw [one_div, inv_pow, div_eq_mul_inv]

/-! ## The closed-interval event as a decreasing limit of mesh events -/

/-- **Mesh reduction (deterministic).** For `g` continuous on `[x, x+T]`, `T > 0`:
`g ≤ M` on `[x, x+T]` iff `g ≤ M` on every dyadic mesh `I_n`. -/
theorem forall_Icc_le_iff_forall_meshSet {g : ℝ → ℝ} {x T M : ℝ} (hT : 0 < T)
    (hg : ContinuousOn g (Icc x (x + T))) :
    (∀ t ∈ Icc x (x + T), g t ≤ M) ↔ ∀ n, ∀ t ∈ AiryFdd.meshSet x T n, g t ≤ M := by
  constructor
  · intro hall n t ht
    exact hall t (meshSet_subset_Icc hT.le n ht)
  · intro hmesh t ht
    choose s hs hlo hhi using fun n => exists_meshSet_near hT ht n
    have hlim : Tendsto s atTop (𝓝 t) := by
      have hl : Tendsto (fun n => t - T / 2 ^ n) atTop (𝓝 t) := by
        simpa using (tendsto_const_nhds (x := t)).sub (tendsto_div_two_pow T)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hhi
    have hlimW : Tendsto s atTop (𝓝[Icc x (x + T)] t) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n =>
        meshSet_subset_Icc hT.le n (hs n)⟩
    exact le_of_tendsto' ((hg t ht).tendsto.comp hlimW) fun n => hmesh n (s n) (hs n)

/-- The mesh event of `Ã` at level `M`. -/
def meshEvent (h : Airy1FddPositive) (x T M : ℝ) (n : ℕ) : Set (ℝ → ℝ) :=
  {f | ∀ t ∈ AiryFdd.meshSet x T n, airy1ContR h t f ≤ M}

theorem measurableSet_meshEvent (h : Airy1FddPositive) (x T M : ℝ) (n : ℕ) :
    MeasurableSet (meshEvent h x T M n) := by
  have : meshEvent h x T M n =
      ⋂ t ∈ AiryFdd.meshSet x T n, {f : ℝ → ℝ | airy1ContR h t f ≤ M} := by
    ext f; simp [meshEvent]
  rw [this]
  exact Finset.measurableSet_biInter _ fun t _ =>
    measurableSet_le (measurable_airy1ContR h t) measurable_const

theorem antitone_meshEvent (h : Airy1FddPositive) (x T M : ℝ) :
    Antitone (meshEvent h x T M) :=
  fun _ _ hnm _ hf t ht => hf t (meshSet_mono x T hnm ht)

/-- **The closed-interval event is the intersection of the mesh events** (every path of `Ã` is
continuous on `[0, ∞)`, `x ≥ 0`). -/
theorem setOf_forall_Icc_le_eq_iInter (h : Airy1FddPositive) {x T M : ℝ} (hx : 0 ≤ x)
    (hT : 0 < T) :
    {f | ∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M} = ⋂ n, meshEvent h x T M n := by
  ext f
  simp only [mem_ofPred_eq, mem_iInter, meshEvent]
  exact forall_Icc_le_iff_forall_meshSet hT
    ((continuousOn_airy1ContR h f).mono fun t ht => hx.trans ht.1)

/-- Each mesh event has the Airy₁ fdd probability `airy1FinCdf I_n (M, …, M)`. -/
theorem airy1Law_meshEvent (h : Airy1FddPositive) (hT : GOELeftTail) (x T M : ℝ) (n : ℕ) :
    (airy1Law h).real (meshEvent h x T M n)
      = AiryFdd.airy1FinCdf (AiryFdd.meshSet x T n) (fun _ => M) := by
  have hae : meshEvent h x T M n =ᵐ[airy1Law h]
      {f : ℝ → ℝ | ∀ t ∈ AiryFdd.meshSet x T n, f t ≤ (fun _ => M) t} := by
    have hall : ∀ᵐ f ∂airy1Law h, ∀ t ∈ AiryFdd.meshSet x T n, airy1ContR h t f = f t :=
      (eventually_all_finset _).2 fun t _ => airy1ContR_ae_eq h hT t
    filter_upwards [hall] with f hf
    refine propext ?_
    change (∀ t ∈ AiryFdd.meshSet x T n, airy1ContR h t f ≤ M) ↔
      ∀ t ∈ AiryFdd.meshSet x T n, f t ≤ M
    exact forall₂_congr fun t ht => by rw [hf t ht]
  rw [measureReal_def, measure_congr hae, ← measureReal_def, airy1Law_fdd]

/-! ## The core law -/

/-- The interval hitting law for any positive length and any fixed admissible weight,
conditional on the dyadic hitting-kernel limit. -/
theorem airy1Law_sup_le_eq_fredholmDet_at_weight (h : Airy1FddPositive) (hT : GOELeftTail)
    {x M T a : ℝ}
    (hx : 0 ≤ x) (hT0 : 0 < T) (hM : 0 < M)
    (ha : T + 1 ≤ a) (hK : AiryFdd.MeshHittingLimit M T) :
    (airy1Law h).real {f | ∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (AiryConj.airyTildeOp M T a hT0 hM ha) 1 := by
  rw [setOf_forall_Icc_le_eq_iInter h hx hT0]
  have hlim := tendsto_measure_iInter_atTop (μ := airy1Law h)
    (fun n => (measurableSet_meshEvent h x T M n).nullMeasurableSet)
    (antitone_meshEvent h x T M) ⟨0, measure_ne_top _ _⟩
  have hlimR : Tendsto (fun n => (airy1Law h).real (meshEvent h x T M n)) atTop
      (𝓝 ((airy1Law h).real (⋂ n, meshEvent h x T M n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim
  simp_rw [airy1Law_meshEvent h hT] at hlimR
  exact tendsto_nhds_unique hlimR (AiryFdd.tendsto_airy1FinCdf_meshSet_at_weight x hT0 hM ha hK)

/-- **Core law.** Under `GOELeftTail` and contrib's dyadic hitting-kernel
limit `MeshHittingLimit M T` (K), for `T ≥ 1`, `M > 0` and any base point `x ≥ 0`:
`ℙ(Ã(t) ≤ M ∀ t ∈ [x, x+T]) = det(I − Ã_{M,T})` with `Ã_{M,T} = airyTildeOp M T (2T)`
(QR 2012 Theorem 4 at block length `T`, QR's weight `a = 2T`). -/
theorem airy1Law_sup_le_eq_fredholmDet (h : Airy1FddPositive) (hT : GOELeftTail) {x M T : ℝ}
    (hx : 0 ≤ x) (hT1 : 1 ≤ T) (hM : 0 < M) (hK : AiryFdd.MeshHittingLimit M T) :
    (airy1Law h).real {f | ∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1 :=
  airy1Law_sup_le_eq_fredholmDet_at_weight h hT hx (by linarith) hM (by linarith) hK

/-- Weight-argument congruence for `airyTildeOp` (the proof arguments are irrelevant). -/
theorem airyTildeOp_congr_weight {M T a b : ℝ} (hab : a = b) (hT : 0 < T) (hM : 0 < M)
    (ha : T + 1 ≤ a) (hb : T + 1 ≤ b) :
    AiryConj.airyTildeOp M T a hT hM ha = AiryConj.airyTildeOp M T b hT hM hb := by
  subst hab; rfl

/-! ## The QR block-law records as theorems -/

/-- Block 0 of `Ã` is below `u` iff `Ã ≤ u` on `[0, 1]`. -/
theorem airy1BlockMax_zero_le_iff (h : Airy1FddPositive) (f : ℝ → ℝ) (u : ℝ) :
    airy1BlockMax h 0 f ≤ u ↔ ∀ t ∈ Icc (0 : ℝ) (0 + 1), airy1ContR h t f ≤ u := by
  have hc : ContinuousOn (fun t => airy1ContR h t f) (Icc (0 : ℝ) (0 + 1)) :=
    (continuousOn_airy1ContR h f).mono fun _ ht => ht.1
  have hbdd := (isCompact_Icc.image_of_continuousOn hc).bddAbove
  have hne : ((fun t => airy1ContR h t f) '' Icc (0 : ℝ) (0 + 1)).Nonempty :=
    (nonempty_Icc.2 (by norm_num)).image _
  unfold airy1BlockMax
  rw [Nat.cast_zero, csSup_le_iff hbdd hne, forall_mem_image]

/-- **`QRUnitBlockLaw` on `Ã` is a theorem** under `GOELeftTail` and the dyadic hitting-kernel
limit at `T = 1` for every level: the core law at `x = 0`, `T = 1`, `a = 2·1 = 2`, plus the
complement. -/
theorem qrUnitBlockLaw_airy1 (h : Airy1FddPositive) (hT : GOELeftTail)
    (hK : ∀ M > 0, AiryFdd.MeshHittingLimit M 1) :
    QRUnitBlockLaw (airy1BlockMax h) (airy1Law h) where
  law := by
    refine Eventually.of_forall fun u hu => ?_
    have hset : {f : ℝ → ℝ | airy1BlockMax h 0 f > u}
        = {f | ∀ t ∈ Icc (0 : ℝ) (0 + 1), airy1ContR h t f ≤ u}ᶜ := by
      ext f
      simp only [mem_ofPred_eq, mem_compl_iff, ← airy1BlockMax_zero_le_iff, not_le, gt_iff_lt]
    have hmeas : MeasurableSet {f : ℝ → ℝ | ∀ t ∈ Icc (0 : ℝ) (0 + 1), airy1ContR h t f ≤ u} := by
      have : {f : ℝ → ℝ | ∀ t ∈ Icc (0 : ℝ) (0 + 1), airy1ContR h t f ≤ u}
          = airy1BlockMax h 0 ⁻¹' Iic u := by
        ext f; simp only [mem_ofPred_eq, mem_preimage, mem_Iic, airy1BlockMax_zero_le_iff]
      rw [this]
      exact measurable_airy1BlockMax h 0 measurableSet_Iic
    rw [hset, probReal_compl_eq_one_sub hmeas,
      airy1Law_sup_le_eq_fredholmDet h hT le_rfl le_rfl hu (hK u hu),
      airyTildeOp_congr_weight (by norm_num : (2 : ℝ) * 1 = 2)]

/-- **`QRTwoBlockLaw` on `Ã` is a theorem** under `GOELeftTail` and the dyadic hitting-kernel
limit at `T = 2` for every level: the core law at `x = 0`, `T = 2`, `a = 2·2 = 4`, through
`QRTwoBlockLaw.of_continuum` on the bundle `airy1CMax h`. -/
theorem qrTwoBlockLaw_airy1 (h : Airy1FddPositive) (hT : GOELeftTail)
    (hK₂ : ∀ M > 0, AiryFdd.MeshHittingLimit M 2) :
    QRTwoBlockLaw (airy1BlockMax h) (airy1Law h) :=
  QRTwoBlockLaw.of_continuum (airy1CMax h) (measurable_airy1BlockMax h) <|
    Eventually.of_forall fun u hu => by
      have hcore := airy1Law_sup_le_eq_fredholmDet h hT le_rfl (by norm_num : (1 : ℝ) ≤ 2) hu
        (hK₂ u hu)
      rw [zero_add, airyTildeOp_congr_weight (by norm_num : (2 : ℝ) * 2 = 4)] at hcore
      exact hcore

/-! ## The headline with `qr` and `qr₂` discharged -/

/-- **Headline `_of_QR₇` on the Airy₁ law** (the paper's main theorem (Theorem 1.1), normalized real-length
form, on `Ã = airy1ContR h`): `gumbel_limit_continuum_real_normalized_airy1_of_QR₆` with
`QRUnitBlockLaw` and `QRTwoBlockLaw` discharged (`qrUnitBlockLaw_airy1`, `qrTwoBlockLaw_airy1`);
they are replaced by the dyadic hitting-kernel limits at `T = 1` and `T = 2` (contrib
`AiryFdd.MeshHittingLimit`). Remaining hypotheses: those two kernel facts, `QRTwoIntervalLaw`,
`CubicStrongMixing`, `CubicCovarianceDecay`, `ProcessAssociated` and
`HighLevelUpcrossingTail` on `Ã`. -/
theorem gumbel_limit_continuum_real_normalized_airy1_of_QR₇ (h : Airy1FddPositive)
    (hT : GOELeftTail)
    (hK : ∀ M > 0, AiryFdd.MeshHittingLimit M 1)
    (hK₂ : ∀ M > 0, AiryFdd.MeshHittingLimit M 2)
    (two : QRTwoIntervalLaw (airy1BlockMax h) (airy1Law h))
    (M : CubicStrongMixing (airy1SRP h hT)) (Cov : CubicCovarianceDecay (airy1SRP h hT))
    (As : ProcessAssociated (airy1SRP h hT)) (U : HighLevelUpcrossingTail (airy1SRP h hT))
    (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law h).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR h x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  gumbel_limit_continuum_real_normalized_airy1_of_QR₆ h hT (qrUnitBlockLaw_airy1 h hT hK)
    (qrTwoBlockLaw_airy1 h hT hK₂) two M Cov As U z

end Airy1Gumbel
