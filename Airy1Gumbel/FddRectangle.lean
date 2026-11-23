/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.GOELeftTail
import Airy1GumbelContrib.FddMeasure.BoxCdf

open AiryFdd Filter Set
open scoped Topology

namespace Airy1Gumbel

/-- Dropping the other levels to their upper limits bounds the box CDF by its singleton. -/
theorem airy1FinCdf_le_singleton
    (hmono : ∀ I : Finset ℝ, Monotone (AiryFdd.airy1FinCdf I))
    (I : Finset ℝ) (i : I) (x : I → ℝ) :
    AiryFdd.airy1FinCdf I x ≤ AiryFdd.airy1FinCdf {i.1} (fun _ => x i) := by
  classical
  induction I using Finset.strongInductionOn with
  | _ I ih =>
    by_cases hs : I = {i.1}
    · obtain ⟨t, ht⟩ := i
      dsimp at hs ⊢
      subst I
      suffices x = (fun _ : ({t} : Finset ℝ) => x ⟨t, ht⟩) by rw [this]
      ext j
      congr
      exact Subtype.ext (Finset.mem_singleton.mp j.2)
    · obtain ⟨j, hj, hji⟩ : ∃ j ∈ I, j ≠ i.1 := by
        by_contra! h
        exact hs (Finset.eq_singleton_iff_unique_mem.mpr ⟨i.2, h⟩)
      let i' : I.erase j := ⟨i.1, Finset.mem_erase.mpr ⟨hji.symm, i.2⟩⟩
      have hdrop := AiryFdd.tendsto_airy1FinCdf_update I hj x
      have hle : airy1FinCdf I x ≤
          airy1FinCdf (I.erase j) (fun s => x ⟨s.1, Finset.mem_of_mem_erase s.2⟩) := by
        refine ge_of_tendsto hdrop ?_
        filter_upwards [eventually_ge_atTop (x ⟨j, hj⟩)] with c hc
        apply hmono I
        intro s
        by_cases he : s = ⟨j, hj⟩
        · subst s; simpa
        · simp [Function.update_of_ne he]
      exact hle.trans (ih _ (Finset.erase_ssubset hj) i' _)

/-- The one-point GOE left tail grounds the finite-dimensional CDF at each lower face. -/
theorem airy1FinCdf_tendsto_zero_face (hT : GOELeftTail)
    (hnonneg : ∀ (I : Finset ℝ) (x : I → ℝ), 0 ≤ AiryFdd.airy1FinCdf I x)
    (hmono : ∀ I : Finset ℝ, Monotone (AiryFdd.airy1FinCdf I))
    (I : Finset ℝ) (i : I) (x : I → ℝ) :
    Tendsto (fun r : ℝ => AiryFdd.airy1FinCdf I (Function.update x i r))
      atBot (𝓝 0) := by
  obtain ⟨C, c, _, hc, hb⟩ := hT.tail_at
  have hlim := (tendsto_cubicEnvelope C hc).comp (tendsto_neg_atBot_atTop (G := ℝ))
  refine squeeze_zero' (Eventually.of_forall fun r => hnonneg I _) ?_ hlim
  filter_upwards [eventually_le_atBot (0 : ℝ)] with r hr
  have h : airy1FinCdf I (Function.update x i r) ≤ airy1FinCdf {i.1} (fun _ => r) := by
    simpa only [Function.update_self] using
      airy1FinCdf_le_singleton hmono I i (Function.update x i r)
  exact h.trans (by simpa only [neg_neg, Function.comp_apply] using hb i.1 (-r) (neg_nonneg.mpr hr))

/-- The corner inequalities reduce the existence of the Airy₁ finite-dimensional laws to
positivity, monotonicity and rectangular nonnegativity, with grounding from the GOE left tail. -/
theorem airy1FddPositive_of_rectangle (hT : GOELeftTail)
    (hnonneg : ∀ (I : Finset ℝ) (x : I → ℝ), 0 ≤ AiryFdd.airy1FinCdf I x)
    (hmono : ∀ I : Finset ℝ, Monotone (AiryFdd.airy1FinCdf I))
    (hrect : ∀ (I : Finset ℝ) (a b : I → ℝ), a ≤ b →
      0 ≤ boxCdfIncrement (AiryFdd.airy1FinCdf I) a b) :
    Airy1FddPositive := by
  refine ⟨fun I => ?_⟩
  exact exists_measure_of_box_cdf (airy1FinCdf I) (continuous_airy1FinCdf I)
    (hnonneg I) (hmono I) (hrect I) (airy1FinCdf_tendsto_zero_face hT hnonneg hmono I)
    (tendsto_airy1FinCdf_one I fun _ => tendsto_id)

end Airy1Gumbel
