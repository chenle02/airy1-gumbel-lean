/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import ChallengeDefs.Airy1Gumbel.Process
import Airy1Gumbel

/-!
# Comparator solution: the Challenge statements, proved from the package

Each theorem of `Challenge.lean` is restated with the same name and type and proved from the
package headlines `Airy1Gumbel.gumbel_limit_continuum_real_normalized_airy1_final₂` and
`Airy1Gumbel.gumbel_limit_continuum_real_normalized_airy1_final₂_coord`.

The bridges (namespace `Airy1GumbelBridge`):

* the analytic definitions of `ChallengeDefs` equal the package's (`rfl`, or induction on the
  entry lists), `kernelOp K` equals the package's `kernelOperator` for a square-integrable `K`
  (both act by integration against `K`, and such an operator is unique), hence
  `Airy1GumbelSpec.airy1FinCdf = AiryFdd.airy1FinCdf`;
* the three inputs: `Airy1FddPositive` and `GOELeftTail` are the package's records, and
  `CubicStrongMixing` (a proposition) is inhabitedness of the package's record structure;
* every Airy₁ law is `airy1Law h` (uniqueness by the finite-dimensional distributions), and any
  two continuous versions agree almost surely on `[0, ∞)` (they agree at the rational times and
  are continuous there), so the probabilities of the Challenge equal those of the headline for
  the package's version `airy1ContR h`.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Airy1GumbelBridge

/-! ## The analytic definitions -/

theorem heatKernel_eq : Airy1GumbelSpec.heatKernel = _root_.heatKernel := rfl

theorem airyAiReal_eq : Airy1GumbelSpec.airyAiReal = _root_.airyAiReal := rfl

theorem backwardAiry_eq : Airy1GumbelSpec.backwardAiry = _root_.backwardAiry := rfl

theorem wKernel_eq : Airy1GumbelSpec.wKernel = AiryConj.wKernel := rfl

theorem compKernel_eq : Airy1GumbelSpec.compKernel = AiryConj.compKernel := rfl

theorem heatKerTwo_eq : Airy1GumbelSpec.heatKerTwo = AiryTwoInt.heatKerTwo := rfl

theorem lamKer1_eq : Airy1GumbelSpec.lamKer1 = AiryFdd.lamKer1 := rfl

theorem fddVKer_eq : Airy1GumbelSpec.fddVKer = AiryFdd.fddVKer := rfl

theorem gapSum_eq : ∀ (e : ℝ × ℝ) (L : List (ℝ × ℝ)),
    Airy1GumbelSpec.gapSum e L = AiryFdd.gapSum e L
  | _, [] => rfl
  | e, y :: L => by
    show e.2 + Airy1GumbelSpec.gapSum y L = e.2 + AiryFdd.gapSum y L
    rw [gapSum_eq y L]

theorem lamKerN_eq : ∀ (e : ℝ × ℝ) (L : List (ℝ × ℝ)),
    Airy1GumbelSpec.lamKerN e L = AiryFdd.lamKerN e L
  | _, [] => rfl
  | e, y :: L => by
    show (fun p => (Iic e.1).indicator (fun _ => (1 : ℝ)) p.1
        * Airy1GumbelSpec.compKernel (Airy1GumbelSpec.heatKerTwo e.2)
          (Airy1GumbelSpec.lamKerN y L) p)
      = fun p => (Iic e.1).indicator (fun _ => (1 : ℝ)) p.1
        * AiryConj.compKernel (AiryTwoInt.heatKerTwo e.2) (AiryFdd.lamKerN y L) p
    rw [lamKerN_eq y L]
    rfl

theorem hitKerN_eq (e : ℝ × ℝ) (L : List (ℝ × ℝ)) :
    Airy1GumbelSpec.hitKerN e L = AiryFdd.hitKerN e L := by
  funext p
  show _root_.heatKernel (Airy1GumbelSpec.gapSum e L) (p.1 - p.2)
      - Airy1GumbelSpec.lamKerN e L p = _
  rw [gapSum_eq, lamKerN_eq]
  rfl

theorem fddEntries_eq (lev : ℝ → ℝ) : ∀ ts : List ℝ,
    Airy1GumbelSpec.fddEntries lev ts = AiryFdd.fddEntries lev ts
  | [] => rfl
  | [_] => rfl
  | t :: s :: L => by
    show (lev t, s - t) :: Airy1GumbelSpec.fddEntries lev (s :: L)
      = (lev t, s - t) :: AiryFdd.fddEntries lev (s :: L)
    rw [fddEntries_eq lev (s :: L)]

theorem finEntries_eq (I : Finset ℝ) (x : I → ℝ) :
    Airy1GumbelSpec.finEntries I x = AiryFdd.finEntries I x :=
  fddEntries_eq _ _

theorem fredholmDet_eq {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (A : E →L[𝕜] E) (z : 𝕜) :
    Airy1GumbelSpec.fredholmDet A z = HilbertSchmidt.fredholmDet A z := rfl

/-- For a square-integrable kernel, the operator characterized by its action is the package's
`kernelOperator`. -/
theorem kernelOp_eq {K : ℝ × ℝ → ℝ} (hK : MemLp K 2 ((volume : Measure ℝ).prod volume)) :
    Airy1GumbelSpec.kernelOp K = HilbertSchmidt.kernelOperator hK := by
  have hspec : ∀ f : Lp ℝ 2 (volume : Measure ℝ),
      ((HilbertSchmidt.kernelOperator hK f : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
        =ᵐ[volume] fun x => ∫ y, K (x, y) * f y :=
    fun f => HilbertSchmidt.kernelOperator_apply_ae hK f
  have hex := Classical.epsilon_spec
    (p := fun T : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) =>
      ∀ f : Lp ℝ 2 (volume : Measure ℝ), (T f : ℝ → ℝ) =ᵐ[volume]
        fun x => ∫ y, K (x, y) * f y) ⟨_, hspec⟩
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  exact (hex f).trans (hspec f).symm

theorem fddOp_eq (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (he : 0 < e.2) (hL : ∀ y ∈ L, 0 < y.2)
    (h1 : 1 ≤ AiryFdd.gapSum e L) :
    Airy1GumbelSpec.fddOp e L = AiryFdd.fddOp e L he hL h1 := by
  unfold Airy1GumbelSpec.fddOp AiryFdd.fddOp
  rw [hitKerN_eq, gapSum_eq, fddVKer_eq, wKernel_eq,
    kernelOp_eq (AiryFdd.memLp_fddVKer_two_mul e L he hL),
    kernelOp_eq (AiryFdd.memLp_wKernel_two_mul e L he hL h1)]

theorem airy1FinCdf_eq (I : Finset ℝ) (x : I → ℝ) :
    Airy1GumbelSpec.airy1FinCdf I x = AiryFdd.airy1FinCdf I x := by
  unfold Airy1GumbelSpec.airy1FinCdf AiryFdd.airy1FinCdf
  rw [finEntries_eq]
  have hpos := AiryFdd.finEntries_pos I x
  have hlast := AiryFdd.finEntries_lastGap I x
  split
  · next hE => exact (AiryFdd.cdfOfEntries_nil hE hpos hlast).symm
  · next e L hE =>
    have he : 0 < e.2 := hpos e (hE ▸ List.mem_cons_self)
    have hL : ∀ y ∈ L, 0 < y.2 := fun y hy => hpos y (hE ▸ List.mem_cons_of_mem _ hy)
    have h1 : 1 ≤ AiryFdd.gapSum e L := AiryFdd.one_le_gapSum he hL (hlast e L hE)
    rw [AiryFdd.cdfOfEntries_cons hE hpos hlast he hL h1, fddOp_eq e L he hL h1,
      fredholmDet_eq]

theorem airy1FinCdf_fun_eq : Airy1GumbelSpec.airy1FinCdf = AiryFdd.airy1FinCdf := by
  funext I x
  exact airy1FinCdf_eq I x

/-! ## The inputs -/

theorem airy1FddPositive_iff :
    Airy1GumbelSpec.Airy1FddPositive ↔ Airy1Gumbel.Airy1FddPositive := by
  unfold Airy1GumbelSpec.Airy1FddPositive
  rw [airy1FinCdf_fun_eq]
  exact ⟨fun h => ⟨h⟩, fun h => h.law⟩

theorem goeLeftTail_iff : Airy1GumbelSpec.GOELeftTail ↔ Airy1Gumbel.GOELeftTail := by
  unfold Airy1GumbelSpec.GOELeftTail
  rw [airy1FinCdf_fun_eq]
  exact ⟨fun h => ⟨h⟩, fun h => h.tail⟩

theorem cubicStrongMixing_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : Airy1Gumbel.StationaryRealProcess P) :
    Airy1GumbelSpec.CubicStrongMixing P X.A ↔ Nonempty (Airy1Gumbel.CubicStrongMixing X) := by
  constructor
  · rintro ⟨C, c, hC, hc, hb⟩
    exact ⟨⟨C, hC, c, hc, hb⟩⟩
  · rintro ⟨M⟩
    exact ⟨M.mixC, M.mixc, M.mixC_pos, M.mixc_pos, M.bound⟩

theorem gumbelAR_eq : Airy1GumbelSpec.gumbelAR = Airy1Gumbel.gumbelAR := rfl

theorem gumbelBR_eq : Airy1GumbelSpec.gumbelBR = Airy1Gumbel.gumbelBR := rfl

/-! ## Laws and versions -/

/-- Every Airy₁ law (in the sense of the Challenge) is the package's `airy1Law h`. -/
theorem eq_airy1Law (h : Airy1Gumbel.Airy1FddPositive) {μ : Measure (ℝ → ℝ)}
    (hμ : Airy1GumbelSpec.IsAiry1Law μ) : μ = Airy1Gumbel.airy1Law h := by
  obtain ⟨hP, hfdd⟩ := hμ
  exact Airy1Gumbel.eq_airy1Law_of_fdd h μ fun I y => by
    rw [← airy1FinCdf_eq]
    exact hfdd I y

theorem isAiry1Law_airy1Law (h : Airy1Gumbel.Airy1FddPositive) :
    Airy1GumbelSpec.IsAiry1Law (Airy1Gumbel.airy1Law h) :=
  ⟨inferInstance, fun I y => by
    rw [airy1FinCdf_eq]
    exact Airy1Gumbel.airy1Law_fdd h I y⟩

theorem isContinuousVersion_airy1ContR (h : Airy1Gumbel.Airy1FddPositive)
    (hT : Airy1Gumbel.GOELeftTail) :
    Airy1GumbelSpec.IsContinuousVersion (Airy1Gumbel.airy1Law h) (Airy1Gumbel.airy1ContR h) :=
  ⟨Airy1Gumbel.measurable_airy1ContR h, Airy1Gumbel.airy1ContR_ae_eq h hT,
    Airy1Gumbel.continuousOn_airy1ContR h⟩

/-- `[0, ∞)` is contained in the closure of its rational points. -/
theorem Ici_subset_closure_rat :
    Ici (0 : ℝ) ⊆ closure (Ici (0 : ℝ) ∩ range ((↑) : ℚ → ℝ)) := by
  have h1 : Ioi (0 : ℝ) ⊆ closure (Ioi (0 : ℝ) ∩ range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioi
  have h2 : closure (Ioi (0 : ℝ) ∩ range ((↑) : ℚ → ℝ))
      ⊆ closure (Ici (0 : ℝ) ∩ range ((↑) : ℚ → ℝ)) :=
    closure_mono (inter_subset_inter_left _ Ioi_subset_Ici_self)
  calc Ici (0 : ℝ) = closure (Ioi 0) := (closure_Ioi 0).symm
    _ ⊆ closure (closure (Ioi (0 : ℝ) ∩ range ((↑) : ℚ → ℝ))) := closure_mono h1
    _ = closure (Ioi (0 : ℝ) ∩ range ((↑) : ℚ → ℝ)) := closure_closure
    _ ⊆ _ := h2

/-- Two continuous versions agree almost surely at every time of `[0, ∞)`. -/
theorem ae_eqOn_of_isContinuousVersion {μ : Measure (ℝ → ℝ)} {Y Y' : ℝ → (ℝ → ℝ) → ℝ}
    (hY : Airy1GumbelSpec.IsContinuousVersion μ Y)
    (hY' : Airy1GumbelSpec.IsContinuousVersion μ Y') :
    ∀ᵐ f ∂μ, EqOn (fun x => Y x f) (fun x => Y' x f) (Ici 0) := by
  have hq : ∀ᵐ f ∂μ, ∀ q : ℚ, Y q f = Y' q f :=
    ae_all_iff.2 fun q => (hY.2.1 q).trans (hY'.2.1 q).symm
  filter_upwards [hq] with f hf
  refine EqOn.of_subset_closure (s := Ici (0 : ℝ) ∩ range ((↑) : ℚ → ℝ)) ?_ (hY.2.2 f)
    (hY'.2.2 f) inter_subset_left Ici_subset_closure_rat
  rintro _ ⟨_, q, rfl⟩
  exact hf q

/-- The Challenge probability does not depend on the continuous version. -/
theorem measureReal_event_congr {μ : Measure (ℝ → ℝ)} {Y Y' : ℝ → (ℝ → ℝ) → ℝ}
    (hY : Airy1GumbelSpec.IsContinuousVersion μ Y)
    (hY' : Airy1GumbelSpec.IsContinuousVersion μ Y') (a b z T : ℝ) :
    μ.real {f | ∀ x ∈ Icc (0 : ℝ) T, (Y x f - a) / b ≤ z}
      = μ.real {f | ∀ x ∈ Icc (0 : ℝ) T, (Y' x f - a) / b ≤ z} := by
  refine measureReal_congr ?_
  filter_upwards [ae_eqOn_of_isContinuousVersion hY hY'] with f hf
  refine propext ⟨fun H x hx => ?_, fun H x hx => ?_⟩
  · have hx' : Y x f = Y' x f := hf (show x ∈ Ici (0 : ℝ) from hx.1)
    rw [← hx']
    exact H x hx
  · have hx' : Y x f = Y' x f := hf (show x ∈ Ici (0 : ℝ) from hx.1)
    rw [hx']
    exact H x hx

/-- A continuous version, as a package `StationaryRealProcess` (one-dimensional stationarity
from the modification property and the stationarity of the coordinate process). -/
noncomputable def versionSRP (h : Airy1Gumbel.Airy1FddPositive) {Y : ℝ → (ℝ → ℝ) → ℝ}
    (hY : Airy1GumbelSpec.IsContinuousVersion (Airy1Gumbel.airy1Law h) Y) :
    Airy1Gumbel.StationaryRealProcess (Airy1Gumbel.airy1Law h) where
  A := Y
  A_meas := hY.1
  stat x s := by
    rw [Measure.map_congr (hY.2.1 (x + s)), Measure.map_congr (hY.2.1 x)]
    exact (Airy1Gumbel.airy1Process h).stat x s

end Airy1GumbelBridge

namespace Airy1GumbelAudit.Airy1Gumbel

open Airy1GumbelSpec

theorem gumbel_limit_continuum_real_normalized_airy1_final₂
    (h : Airy1FddPositive) (hT : GOELeftTail) :
    (∃ μ : Measure (ℝ → ℝ), IsAiry1Law μ) ∧
      ∀ μ : Measure (ℝ → ℝ), IsAiry1Law μ →
        (∃ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y) ∧
          ∀ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y → CubicStrongMixing μ Y →
            ∀ z : ℝ, Tendsto (fun T : ℝ => μ.real {f | ∀ x ∈ Icc (0 : ℝ) T,
              (Y x f - gumbelAR T) / gumbelBR T ≤ z})
              atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  have h' := Airy1GumbelBridge.airy1FddPositive_iff.1 h
  have hT' := Airy1GumbelBridge.goeLeftTail_iff.1 hT
  refine ⟨⟨_, Airy1GumbelBridge.isAiry1Law_airy1Law h'⟩, fun μ hμ => ?_⟩
  obtain rfl := Airy1GumbelBridge.eq_airy1Law h' hμ
  refine ⟨⟨_, Airy1GumbelBridge.isContinuousVersion_airy1ContR h' hT'⟩, fun Y hY M z => ?_⟩
  obtain ⟨MY⟩ := (Airy1GumbelBridge.cubicStrongMixing_iff
    (Airy1GumbelBridge.versionSRP h' hY)).1 M
  have M' : _root_.Airy1Gumbel.CubicStrongMixing (_root_.Airy1Gumbel.airy1SRP h' hT') :=
    MY.ofModification (X := _root_.Airy1Gumbel.airy1SRP h' hT')
      (Y := Airy1GumbelBridge.versionSRP h' hY)
      fun t => (_root_.Airy1Gumbel.airy1ContR_ae_eq h' hT' t).trans (hY.2.1 t).symm
  have key := _root_.Airy1Gumbel.gumbel_limit_continuum_real_normalized_airy1_final₂ h' hT' M' z
  refine key.congr fun T => ?_
  rw [Airy1GumbelBridge.gumbelAR_eq, Airy1GumbelBridge.gumbelBR_eq]
  exact Airy1GumbelBridge.measureReal_event_congr
    (Airy1GumbelBridge.isContinuousVersion_airy1ContR h' hT') hY _ _ _ _

theorem gumbel_limit_continuum_real_normalized_airy1_final₂_coord
    (h : Airy1FddPositive) (hT : GOELeftTail) :
    (∃ μ : Measure (ℝ → ℝ), IsAiry1Law μ) ∧
      ∀ μ : Measure (ℝ → ℝ), IsAiry1Law μ → CubicStrongMixing μ (fun x f => f x) →
        (∃ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y) ∧
          ∀ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y →
            ∀ z : ℝ, Tendsto (fun T : ℝ => μ.real {f | ∀ x ∈ Icc (0 : ℝ) T,
              (Y x f - gumbelAR T) / gumbelBR T ≤ z})
              atTop (𝓝 (Real.exp (-Real.exp (-z)))) := by
  have h' := Airy1GumbelBridge.airy1FddPositive_iff.1 h
  have hT' := Airy1GumbelBridge.goeLeftTail_iff.1 hT
  refine ⟨⟨_, Airy1GumbelBridge.isAiry1Law_airy1Law h'⟩, fun μ hμ M => ?_⟩
  obtain rfl := Airy1GumbelBridge.eq_airy1Law h' hμ
  refine ⟨⟨_, Airy1GumbelBridge.isContinuousVersion_airy1ContR h' hT'⟩, fun Y hY z => ?_⟩
  obtain ⟨M'⟩ := (Airy1GumbelBridge.cubicStrongMixing_iff
    (_root_.Airy1Gumbel.airy1Process h')).1 M
  have key :=
    _root_.Airy1Gumbel.gumbel_limit_continuum_real_normalized_airy1_final₂_coord h' hT' M' z
  refine key.congr fun T => ?_
  rw [Airy1GumbelBridge.gumbelAR_eq, Airy1GumbelBridge.gumbelBR_eq]
  exact Airy1GumbelBridge.measureReal_event_congr
    (Airy1GumbelBridge.isContinuousVersion_airy1ContR h' hT') hY _ _ _ _

end Airy1GumbelAudit.Airy1Gumbel
