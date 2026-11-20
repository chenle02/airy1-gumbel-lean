/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.Mixing

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Airy1Gumbel

/-!
# `decouple` from the `CubicStrongMixing` record

The record `CubicStrongMixing` (`ExternalInputs.lean`) carries the
σ-algebra strong-mixing statement of [ChenPu2026, Proposition 3.1] at
`s = 1/2` ([ChenPu2026] (arXiv 2607.17113), a preprint): for every cut
point `a`, gap `d ≥ 0`, `E ∈ σ(A y : y ≤ a)` and `F ∈ σ(A y : y ≥ a + d)`,
`|ℙ(E ∩ F) - ℙ(E) ℙ(F)| ≤ C e^{-c d³}`. This file

* audits the record: `cubicStrongMixing_const_nonempty` (a deterministic
  process, which genuinely mixes, is admitted) and
  `not_cubicStrongMixing_of_frozen` (a frozen process `A y = ξ` with
  `0 < ℙ(ξ ≤ 0) < 1` is rejected: the record is false for it);
* proves the transfer from the process to the block maxima of an
  `Airy1ContinuousMax` bundle: the block events `{∀ s ∈ S, Y s ≤ u}` agree
  a.e. with events in `σ(A x : x rational in a block of S)`
  (`Airy1ContinuousMax.blockEvent_ae_eq`), by path continuity and density of
  the rationals (`forall_le_of_forall_rat_le`);
* derives the `decouple` field of `Airy1BlockExtremes`
  (`decouple_of_CubicStrongMixing`; the paper's decoupling telescope
  consumes it) at the explicit envelope
  `CubicStrongMixing.alphaY m = max C 1 · e^{-c (m-1)³}`, the paper's block-maxima
  mixing envelope. The index gap `s + q ≤ t` between unit blocks
  `[s, s+1]` and `[t, t+1]` is a real gap of at least `q - 1`, which is the
  `(m - 1)` of that envelope; `q = 0` and empty index sets are handled by the trivial
  bound `|x - p q| ≤ 1 ≤ alphaY 0`;
* assembles `Airy1BlockExtremes.ofQR₄`, which supplies all ten mixing fields of
  `Airy1BlockExtremes`, and the six `_of_QR₄` corollaries, which carry
  no mixing hypothesis (only the record `CubicStrongMixing X` and the link
  `X.A = C.A`).
-/

/-! ### The past and future σ-algebras -/

section SigmaAlgebras

variable {Ω : Type*}

/-- `σ(A y) ≤ σ(A x : x ≤ a)` for `y ≤ a`. -/
theorem comap_le_pastSigma (A : ℝ → Ω → ℝ) {a y : ℝ} (hy : y ≤ a) :
    MeasurableSpace.comap (A y) Real.measurableSpace ≤ pastSigma A a :=
  le_iSup₂ (f := fun (x : ℝ) (_ : x ≤ a) => MeasurableSpace.comap (A x) Real.measurableSpace)
    y hy

/-- `σ(A y) ≤ σ(A x : x ≥ b)` for `b ≤ y`. -/
theorem comap_le_futureSigma (A : ℝ → Ω → ℝ) {b y : ℝ} (hy : b ≤ y) :
    MeasurableSpace.comap (A y) Real.measurableSpace ≤ futureSigma A b :=
  le_iSup₂ (f := fun (x : ℝ) (_ : b ≤ x) => MeasurableSpace.comap (A x) Real.measurableSpace)
    y hy

/-- `{A y ≤ u}` is a past event for `y ≤ a`. -/
theorem measurableSet_pastSigma_le (A : ℝ → Ω → ℝ) {a y : ℝ} (hy : y ≤ a) (u : ℝ) :
    MeasurableSet[pastSigma A a] {ω | A y ω ≤ u} :=
  comap_le_pastSigma A hy _
    (MeasurableSpace.measurableSet_comap.2 ⟨Set.Iic u, measurableSet_Iic, rfl⟩)

/-- `{A y ≤ u}` is a future event for `b ≤ y`. -/
theorem measurableSet_futureSigma_le (A : ℝ → Ω → ℝ) {b y : ℝ} (hy : b ≤ y) (u : ℝ) :
    MeasurableSet[futureSigma A b] {ω | A y ω ≤ u} :=
  comap_le_futureSigma A hy _
    (MeasurableSpace.measurableSet_comap.2 ⟨Set.Iic u, measurableSet_Iic, rfl⟩)

/-- A countable intersection of level events `{A x ≤ u}`, `x ∈ J`, is measurable for
any σ-algebra containing each of them. -/
theorem measurableSet_setOf_forall_mem_le {m : MeasurableSpace Ω} (A : ℝ → Ω → ℝ) {J : Set ℝ}
    (hJ : J.Countable) {u : ℝ} (h : ∀ x ∈ J, MeasurableSet[m] {ω | A x ω ≤ u}) :
    MeasurableSet[m] {ω | ∀ x ∈ J, A x ω ≤ u} := by
  have hset : {ω | ∀ x ∈ J, A x ω ≤ u} = ⋂ x ∈ J, {ω | A x ω ≤ u} := by
    ext ω; simp
  rw [hset]
  exact MeasurableSet.biInter hJ h

end SigmaAlgebras

/-! ### Rational points of unit blocks, and the a.e. block-event transfer -/

/-- The rational points of the unit blocks `[s, s + 1]`, `s ∈ S`. -/
def ratBlocks (S : Finset ℕ) : Set ℝ :=
  {x | (∃ s ∈ S, x ∈ Set.Icc (s : ℝ) (s + 1)) ∧ x ∈ Set.range ((↑) : ℚ → ℝ)}

/-- `ratBlocks S` is countable. -/
theorem ratBlocks_countable (S : Finset ℕ) : (ratBlocks S).Countable :=
  (Set.countable_range _).mono fun _ hx => hx.2

/-- A function continuous on `[a, b]` (`a < b`) that is `≤ u` at the rational points
of `[a, b]` is `≤ u` on `[a, b]`: the rationals of `(a, b)` are dense in `[a, b]`
and `[a, b] ∩ f⁻¹(-∞, u]` is closed. -/
theorem forall_le_of_forall_rat_le {f : ℝ → ℝ} {a b u : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (h : ∀ x ∈ Set.Icc a b, x ∈ Set.range ((↑) : ℚ → ℝ) → f x ≤ u) :
    ∀ x ∈ Set.Icc a b, f x ≤ u := by
  have hclosed : IsClosed (Set.Icc a b ∩ f ⁻¹' Set.Iic u) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsub : Set.Ioo a b ∩ Set.range ((↑) : ℚ → ℝ) ⊆ Set.Icc a b ∩ f ⁻¹' Set.Iic u :=
    fun x hx => ⟨Set.Ioo_subset_Icc_self hx.1, h x (Set.Ioo_subset_Icc_self hx.1) hx.2⟩
  have hdense : Set.Ioo a b ⊆ closure (Set.Ioo a b ∩ Set.range ((↑) : ℚ → ℝ)) :=
    Dense.open_subset_closure_inter (Rat.denseRange_cast (𝕜 := ℝ)) isOpen_Ioo
  have hIcc : Set.Icc a b ⊆ closure (Set.Ioo a b ∩ Set.range ((↑) : ℚ → ℝ)) := by
    rw [← closure_Ioo hab.ne]
    exact closure_minimal hdense isClosed_closure
  intro x hx
  exact (closure_minimal hsub hclosed (hIcc hx)).2

/-- **Block events are a.e. events of the process at rational points.** On the
full-measure event where the path is continuous and each `Y j` is the supremum of
the path over `[j, j + 1]` (`Airy1ContinuousMax.path_cont`, `Y_eq`),
`(∀ s ∈ S, Y s ≤ u) ↔ (∀ x ∈ ratBlocks S, A x ≤ u)`. The right-hand event is a
countable intersection of level events of `A` (this is the passage from
`α_{A₁}` to `α_Y` in the paper's block-maxima mixing envelope). -/
theorem Airy1ContinuousMax.blockEvent_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (C : Airy1ContinuousMax P) (S : Finset ℕ)
    (u : ℝ) :
    {ω | ∀ s ∈ S, C.Y s ω ≤ u} =ᵐ[P] {ω | ∀ x ∈ ratBlocks S, C.A x ω ≤ u} := by
  filter_upwards [C.path_cont, C.Y_eq] with ω hcont hY
  apply propext
  constructor
  · rintro h x ⟨⟨s, hs, hx⟩, -⟩
    exact (C.le_block_sup hcont hY s hx).trans (h s hs)
  · intro h s hs
    apply C.block_sup_le hY s
    refine forall_le_of_forall_rat_le (f := fun x => C.A x ω) (by linarith) ?_ ?_
    · exact hcont.mono fun x hx => le_trans (Nat.cast_nonneg s) hx.1
    · intro x hx hq
      exact h x ⟨⟨s, hs, hx⟩, hq⟩

/-- The rational block event of `S` is a past event at any cut point `a` to the right
of every block of `S`. -/
theorem measurableSet_pastSigma_ratBlocks {Ω : Type*} (A : ℝ → Ω → ℝ) {S : Finset ℕ}
    {a : ℝ} (hS : ∀ s ∈ S, (s : ℝ) + 1 ≤ a) (u : ℝ) :
    MeasurableSet[pastSigma A a] {ω | ∀ x ∈ ratBlocks S, A x ω ≤ u} :=
  measurableSet_setOf_forall_mem_le A (ratBlocks_countable S) fun _ ⟨⟨s, hs, hx⟩, _⟩ =>
    measurableSet_pastSigma_le A (hx.2.trans (hS s hs)) u

/-- The rational block event of `T` is a future event at any cut point `b` to the
left of every block of `T`. -/
theorem measurableSet_futureSigma_ratBlocks {Ω : Type*} (A : ℝ → Ω → ℝ) {T : Finset ℕ}
    {b : ℝ} (hT : ∀ t ∈ T, b ≤ (t : ℝ)) (u : ℝ) :
    MeasurableSet[futureSigma A b] {ω | ∀ x ∈ ratBlocks T, A x ω ≤ u} :=
  measurableSet_setOf_forall_mem_le A (ratBlocks_countable T) fun _ ⟨⟨t, ht, hx⟩, _⟩ =>
    measurableSet_futureSigma_le A ((hT t ht).trans hx.1) u

/-- The trivial covariance bound `|x - p q| ≤ 1` for `x, p, q ∈ [0, 1]` (the
trivial bound `α ≤ 1` of [ChenPu2026]). -/
theorem abs_sub_mul_le_one_of_unit {x p q : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : |x - p * q| ≤ 1 := by
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hp0 hq0, mul_le_mul hp1 hq1 hq0 zero_le_one]

/-! ### The block-maxima envelope and `decouple` -/

section Envelope

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : StationaryRealProcess P}

/-- The block-maxima mixing envelope of the paper,
`α_Y(m) = max(C, 1) · e^{-c (m - 1)³}`, built from the constants of the
`CubicStrongMixing` record. The amplitude is raised to `max C 1` so that the
trivial bound covers `m = 0` (after increasing `C`, as in [ChenPu2026]). -/
noncomputable def CubicStrongMixing.alphaY (M : CubicStrongMixing X) (m : ℕ) : ℝ :=
  max M.mixC 1 * Real.exp (-M.mixc * ((m : ℝ) - 1) ^ 3)

/-- The raised amplitude `max C 1` is positive. -/
theorem CubicStrongMixing.mixCY_pos (M : CubicStrongMixing X) : 0 < max M.mixC 1 :=
  lt_of_lt_of_le one_pos (le_max_right _ _)

/-- `α_Y(m) ≥ 0`. -/
theorem CubicStrongMixing.alphaY_nonneg (M : CubicStrongMixing X) (m : ℕ) :
    0 ≤ M.alphaY m :=
  mul_nonneg M.mixCY_pos.le (Real.exp_pos _).le

/-- The block-maxima mixing envelope in the `alpha_bound` form of `Airy1BlockExtremes`, by definition. -/
theorem CubicStrongMixing.alphaY_bound (M : CubicStrongMixing X) (m : ℕ) :
    M.alphaY m ≤ max M.mixC 1 * Real.exp (-M.mixc * ((m : ℝ) - 1) ^ 3) :=
  le_rfl

/-- `α_Y(0) = max(C, 1) e^{c} ≥ 1`, which covers the gap-free case `q = 0`. -/
theorem CubicStrongMixing.one_le_alphaY_zero (M : CubicStrongMixing X) :
    1 ≤ M.alphaY 0 := by
  unfold CubicStrongMixing.alphaY
  have he : -M.mixc * (((0 : ℕ) : ℝ) - 1) ^ 3 = M.mixc := by push_cast; ring
  rw [he]
  have h1 : (1 : ℝ) ≤ Real.exp M.mixc := Real.one_le_exp M.mixc_pos.le
  have h2 : (1 : ℝ) ≤ max M.mixC 1 := le_max_right _ _
  nlinarith

/-- **`decouple` from the `CubicStrongMixing` record** (the block-maxima mixing
envelope, as used in the paper's decoupling telescope).
Let `C` be an `Airy1ContinuousMax` bundle whose process is that of `X`
(`X.A = C.A`). For finite index sets `S`, `T` with `s + q ≤ t` for all `s ∈ S`,
`t ∈ T`, the `≤`-events of the block maxima decouple with error `α_Y(q)`,
`α_Y(m) = max(C, 1) e^{-c(m-1)³}`.

Proof: if `S` or `T` is empty, the left side is `0`. If `q = 0`, it is at most
`1 ≤ α_Y(0)`. Otherwise put `s₀ = max S`, `a = s₀ + 1` and `d = q - 1 ≥ 0`;
every block of `S` lies in `(-∞, a]` and every block of `T` in `[a + d, ∞)`,
since `t ≥ s₀ + q = a + d`. By `Airy1ContinuousMax.blockEvent_ae_eq` the block
events are a.e. equal to rational-point events of `A`, which are measurable for
`σ(A y : y ≤ a)` and `σ(A y : y ≥ a + d)`; the record bounds the covariance of the
latter by `C e^{-c d³} ≤ α_Y(q)`, and `P.real` is invariant under a.e. equality. -/
theorem decouple_of_CubicStrongMixing (M : CubicStrongMixing X) (C : Airy1ContinuousMax P)
    (hA : X.A = C.A) :
    ∀ (S T : Finset ℕ) (q : ℕ) (u : ℝ),
      (∀ s ∈ S, ∀ t ∈ T, s + q ≤ t) →
      |P.real ({ω | ∀ s ∈ S, C.Y s ω ≤ u} ∩ {ω | ∀ t ∈ T, C.Y t ω ≤ u}) -
        P.real {ω | ∀ s ∈ S, C.Y s ω ≤ u} * P.real {ω | ∀ t ∈ T, C.Y t ω ≤ u}|
        ≤ M.alphaY q := by
  intro S T q u hsep
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simpa using M.alphaY_nonneg q
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · simpa using M.alphaY_nonneg q
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine le_trans (abs_sub_mul_le_one_of_unit ENNReal.toReal_nonneg measureReal_le_one
      ENNReal.toReal_nonneg measureReal_le_one ENNReal.toReal_nonneg measureReal_le_one) ?_
    exact M.one_le_alphaY_zero
  have hs₀ : ∀ s ∈ S, s ≤ S.max' hSne := fun s hs => S.le_max' s hs
  have hd : (0 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hS' : ∀ s ∈ S, (s : ℝ) + 1 ≤ (S.max' hSne : ℝ) + 1 := fun s hs => by
    have := hs₀ s hs
    have : (s : ℝ) ≤ (S.max' hSne : ℝ) := by exact_mod_cast this
    linarith
  have hT' : ∀ t ∈ T, (S.max' hSne : ℝ) + 1 + ((q : ℝ) - 1) ≤ (t : ℝ) := fun t ht => by
    have h := hsep _ (S.max'_mem hSne) t ht
    have : ((S.max' hSne + q : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  have hE := M.bound _ _ hd _ _ (measurableSet_pastSigma_ratBlocks X.A hS' u)
    (measurableSet_futureSigma_ratBlocks X.A hT' u)
  rw [hA] at hE
  have hES := C.blockEvent_ae_eq S u
  have hET := C.blockEvent_ae_eq T u
  rw [measureReal_congr (hES.inter hET), measureReal_congr hES, measureReal_congr hET]
  refine hE.trans ?_
  unfold CubicStrongMixing.alphaY
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end Envelope

/-! ### Record sanity checks: a mixing witness and a non-mixing rejection -/

section Audit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The deterministic process `A y ω = c` (a trivial-witness test process). -/
def StationaryRealProcess.const (P : Measure Ω) [IsProbabilityMeasure P] (c : ℝ) :
    StationaryRealProcess P where
  A := fun _ _ => c
  A_meas := fun _ => measurable_const
  stat := fun _ _ => rfl

omit [MeasurableSpace Ω] in
/-- A constant process generates the trivial past σ-algebra. -/
theorem pastSigma_const (c a : ℝ) : pastSigma (fun (_ : ℝ) (_ : Ω) => c) a = ⊥ := by
  simp [pastSigma]

/-- **Non-vacuity witness.** A deterministic process genuinely mixes (its
generated σ-algebras are trivial), and the record admits it, with
`C = c = 1`. This is the expected behaviour: the record is satisfiable, and the
witness is a process that does mix. -/
theorem cubicStrongMixing_const_nonempty (P : Measure Ω) [IsProbabilityMeasure P] (c : ℝ) :
    Nonempty (CubicStrongMixing (StationaryRealProcess.const P c)) := by
  refine ⟨{ mixC := 1, mixC_pos := one_pos, mixc := 1, mixc_pos := one_pos, bound := ?_ }⟩
  intro a d _ E F hE hF
  have hE' : MeasurableSet[⊥] E := by
    have h := pastSigma_const (Ω := Ω) c a
    rw [show (StationaryRealProcess.const P c).A = fun (_ : ℝ) (_ : Ω) => c from rfl, h] at hE
    exact hE
  have hF' : MeasurableSet[⊥] F := by
    have h := pastSigma_const (Ω := Ω) c (a + d)
    have hfut : futureSigma (fun (_ : ℝ) (_ : Ω) => c) (a + d) = ⊥ := by
      simp [futureSigma]
    rw [show (StationaryRealProcess.const P c).A = fun (_ : ℝ) (_ : Ω) => c from rfl,
      hfut] at hF
    exact hF
  rcases MeasurableSpace.measurableSet_bot_iff.1 hE' with rfl | rfl <;>
    rcases MeasurableSpace.measurableSet_bot_iff.1 hF' with rfl | rfl <;>
    simp <;> positivity

/-- **Refutation on a non-mixing process.** If the process is frozen,
`A y = ξ` for every `y`, with `0 < ℙ(ξ ≤ 0) < 1`, then the record is
**false**: the event `{ξ ≤ 0}` is both a past and a future event at every gap,
so `p (1 - p) > 0` would be bounded by `C e^{-c d³} → 0`. -/
theorem not_cubicStrongMixing_of_frozen {P : Measure Ω} [IsProbabilityMeasure P]
    {X : StationaryRealProcess P} {ξ : Ω → ℝ} (hX : ∀ y, X.A y = ξ)
    (h0 : 0 < P.real {ω | ξ ω ≤ 0}) (h1 : P.real {ω | ξ ω ≤ 0} < 1) :
    IsEmpty (CubicStrongMixing X) := by
  refine ⟨fun M => ?_⟩
  have hpos : 0 < P.real {ω | ξ ω ≤ 0} * (1 - P.real {ω | ξ ω ≤ 0}) :=
    mul_pos h0 (by linarith)
  have h3 : Tendsto (fun d : ℝ => -M.mixc * d ^ 3) atTop atBot := by
    have h := tendsto_neg_atTop_atBot.comp
      ((tendsto_pow_atTop (α := ℝ) (n := 3) (by norm_num)).const_mul_atTop M.mixc_pos)
    refine h.congr fun d => ?_
    simp [Function.comp, neg_mul]
  have hlim : Tendsto (fun d : ℝ => M.mixC * Real.exp (-M.mixc * d ^ 3)) atTop (𝓝 0) := by
    have h4 := (Real.tendsto_exp_atBot.comp h3).const_mul M.mixC
    rw [mul_zero] at h4
    exact h4
  obtain ⟨d, hdlt, hd0⟩ :=
    ((hlim.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop (0 : ℝ))).exists
  have hE : MeasurableSet[pastSigma X.A 0] {ω | ξ ω ≤ 0} := by
    have h := measurableSet_pastSigma_le X.A (le_refl (0 : ℝ)) 0
    rwa [hX] at h
  have hF : MeasurableSet[futureSigma X.A (0 + d)] {ω | ξ ω ≤ 0} := by
    have h := measurableSet_futureSigma_le X.A (le_refl (0 + d)) 0
    rwa [hX] at h
  have hb := M.bound 0 d hd0 _ _ hE hF
  rw [Set.inter_self] at hb
  have heq : P.real {ω | ξ ω ≤ 0} - P.real {ω | ξ ω ≤ 0} * P.real {ω | ξ ω ≤ 0} =
      P.real {ω | ξ ω ≤ 0} * (1 - P.real {ω | ξ ω ≤ 0}) := by ring
  rw [heq, abs_of_pos hpos] at hb
  linarith

end Audit

/-! ### Smart constructor `ofQR₄` and the `_of_QR₄` corollaries -/

section OfQR₄

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (Y : ℕ → Ω → ℝ) (Y_meas : ∀ j, Measurable (Y j))
  (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
  (stat_pair : ∀ (u : ℝ) (i d : ℕ),
    P {ω | Y i ω > u ∧ Y (i + d) ω > u} = P {ω | Y 0 ω > u ∧ Y d ω > u})
  (qr : QRUnitBlockLaw Y P) (qr₂ : QRTwoBlockLaw Y P) (two : QRTwoIntervalLaw Y P)
  (mesoscopic : ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
    Tendsto (fun N : ℕ =>
      (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
        P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0))
  (C : Airy1ContinuousMax P) (hY : Y = C.Y)
  (X : StationaryRealProcess P) (hA : X.A = C.A) (M : CubicStrongMixing X)

include Y_meas stat_marginal stat_pair qr qr₂ two mesoscopic hY hA M

/-- Smart constructor for `Airy1BlockExtremes`: all ten mixing
fields are supplied from the `CubicStrongMixing` record ([ChenPu2026,
Proposition 3.1] at `s = 1/2`; [ChenPu2026] (arXiv 2607.17113), a preprint)
for a process `X` with `X.A = C.A`, where `C` is the continuum bundle of the block
maxima (`Y = C.Y`). The envelope is `alpha = M.alphaY`,
`α_Y(m) = max(C,1) e^{-c(m-1)³}` (the block-maxima mixing envelope), so
`alpha_bound` holds by `le_rfl`; `decouple` is
`decouple_of_CubicStrongMixing`; `mixing_tail` (summability of the envelope) and
`pair_mix` follow through `ofQR₃'`. `sharp_tail`, `touching`
and `separated` come from `QRUnitBlockLaw`, `QRTwoBlockLaw` and
`QRTwoIntervalLaw` (proved in the paper) as in `ofQR₃`. -/
noncomputable def Airy1BlockExtremes.ofQR₄ : Airy1BlockExtremes P :=
  Airy1BlockExtremes.ofQR₃' Y Y_meas M.alphaY M.alphaY_nonneg (max M.mixC 1) M.mixCY_pos
    M.mixc M.mixc_pos M.alphaY_bound stat_marginal stat_pair qr qr₂ two mesoscopic
    (by subst hY; exact decouple_of_CubicStrongMixing M C hA)

/-- **Conditional Gumbel limit, integer-block form, with every field except
`mesoscopic` discharged** (the paper's main theorem (Theorem 1.1); block form of
`Airy1BlockExtremes.gumbel_limit`). Compared with `gumbel_limit_of_QR₃'`, the
mixing hypotheses `alpha`, `alpha_nonneg`, `mixC*`, `mixc*`, `alpha_bound`
and `decouple` are replaced by
the record `CubicStrongMixing X` ([ChenPu2026, Proposition 3.1]) and the links
`Y = C.Y`, `X.A = C.A`. -/
theorem Airy1BlockExtremes.gumbel_limit_of_QR₄ (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ j ∈ Finset.range N, Y j ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  (Airy1BlockExtremes.ofQR₄ Y Y_meas stat_marginal stat_pair qr qr₂ two mesoscopic C hY X
    hA M).gumbel_limit z

/-- **Conditional Gumbel limit, continuum integer-length form, with no mixing
hypothesis** (Theorem 1.1 of the paper; corollary of
`Airy1ContinuousMax.gumbel_limit_continuum`): `ℙ(M_N ≤ u_N(z)) → e^{-e^{-z}}`.
The ten mixing fields come from `CubicStrongMixing X`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_QR₄ (z : ℝ) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum (Airy1BlockExtremes.ofQR₄ Y Y_meas stat_marginal stat_pair qr
    qr₂ two mesoscopic C hY X hA M) hY z

/-- **Normalized integer-length Gumbel limit, with no mixing hypothesis**
(Theorem 1.1 of the paper; corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_normalized`): `(M_N - a_N)/b_N`
converges in law to the standard Gumbel distribution. The ten mixing fields come
from `CubicStrongMixing X`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_normalized_of_QR₄ (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ),
      (C.A x ω - gumbelA N) / gumbelB N ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_normalized (Airy1BlockExtremes.ofQR₄ Y Y_meas stat_marginal
    stat_pair qr qr₂ two mesoscopic C hY X hA M) hY z

/-- **Perturbed-level integer-length Gumbel limit, with no mixing hypothesis**
(a step of the real-length extension of Theorem 1.1 and
corollary of `Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto`).
The ten mixing fields come from `CubicStrongMixing X`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_of_tendsto_of_QR₄ (z : ℝ) (w : ℕ → ℝ)
    (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun N : ℕ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ), C.A x ω ≤ gumbelU N (w N)})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_of_tendsto (Airy1BlockExtremes.ofQR₄ Y Y_meas stat_marginal
    stat_pair qr qr₂ two mesoscopic C hY X hA M) hY z w hw

/-- **Real-length conditional Gumbel limit, with no mixing hypothesis**
(Theorem 1.1 of the paper, real `T → ∞`; corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_real`): `ℙ(M_T ≤ u_T(z)) → e^{-e^{-z}}`.
The ten mixing fields come from `CubicStrongMixing X`. -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_of_QR₄ (z : ℝ) :
    Tendsto (fun T : ℝ =>
      P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T, C.A x ω ≤ gumbelUR T z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_real (Airy1BlockExtremes.ofQR₄ Y Y_meas stat_marginal stat_pair
    qr qr₂ two mesoscopic C hY X hA M) hY z

/-- **The paper's main theorem with no mixing hypothesis** (Theorem 1.1,
normalized real-length shape; corollary of
`Airy1ContinuousMax.gumbel_limit_continuum_real_normalized`): `(M_T - a_T)/b_T`
converges in law to the standard Gumbel distribution as `T → ∞`. None of the ten
mixing fields of `Airy1BlockExtremes` (`alpha`, `alpha_nonneg`, `mixC*`, `mixc*`,
`alpha_bound`, `mixing_tail`, `decouple`, `pair_mix`) is a hypothesis: they are
derived from the record `CubicStrongMixing X` ([ChenPu2026, Proposition
3.1] at `s = 1/2`; [ChenPu2026] (arXiv 2607.17113), a preprint) for a process
`X` with `X.A = C.A`, via the block-maxima mixing envelope and the decoupling
telescope. The remaining named inputs are the records `QRUnitBlockLaw`,
`QRTwoBlockLaw`, `QRTwoIntervalLaw` (proved in the paper), `CubicStrongMixing`,
stationarity, measurability of `Y`, and `mesoscopic` (the paper's mesoscopic estimate). -/
theorem Airy1ContinuousMax.gumbel_limit_continuum_real_normalized_of_QR₄ (z : ℝ) :
    Tendsto (fun T : ℝ => P.real {ω | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (C.A x ω - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z)))) :=
  C.gumbel_limit_continuum_real_normalized (Airy1BlockExtremes.ofQR₄ Y Y_meas
    stat_marginal stat_pair qr qr₂ two mesoscopic C hY X hA M) hY z

end OfQR₄

end Airy1Gumbel
