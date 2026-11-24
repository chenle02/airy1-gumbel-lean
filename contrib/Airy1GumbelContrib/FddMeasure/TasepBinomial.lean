/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.FddMeasure.TasepSaddle
import Airy1GumbelContrib.AiryKernel.BackwardAiry
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

open Filter Set
open scoped Topology BigOperators

namespace AiryFdd

/-- The free BFP07 contribution on increasing time pairs, multiplied by the
inverse lattice spacing and conjugated by the same power of two as the pole. -/
noncomputable def bfpScaledFree (N : ℕ) (u v s₁ s₂ : ℝ) : ℝ :=
  bfpScale N * (2 : ℝ) ^ (bfpLatticeSite N v s₂ - bfpLatticeSite N u s₁) *
    bfpFreeKer (bfpLabel N u) (bfpLatticeSite N u s₁) (bfpLabel N v) (bfpLatticeSite N v s₂)

/-- If the row time does not precede the column time, the free term is zero. -/
theorem bfpScaledFree_eq_zero_of_ge (N : ℕ) {u v : ℝ} (h : v ≤ u) (s₁ s₂ : ℝ) :
    bfpScaledFree N u v s₁ s₂ = 0 := by
  have hn : bfpLabel N v ≤ bfpLabel N u := by
    rw [bfpLabel_eq, bfpLabel_eq]
    apply Int.floor_mono
    gcongr
  simp [bfpScaledFree,bfpFreeKer,not_lt_of_ge hn]


private noncomputable def bfpWaitingMass (p : ℝ) (k l : ℕ) :=
  ((l-1).choose (k-1) : ℝ) * p^k * (1-p)^(l-k)

private theorem bfpWaitingMass_nonneg {p : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1) (k l : ℕ) :
    0 ≤ bfpWaitingMass p k l := by unfold bfpWaitingMass; positivity

private theorem bfpWaitingMass_factor {p : ℝ} {k l : ℕ} (hk : 0 < k) (hl : k ≤ l) :
    bfpWaitingMass p k l = (k:ℝ)/l * (l.choose k : ℝ) * p^k * (1-p)^(l-k) := by
  have hl₀ : 0 < l := hk.trans_le hl
  have h := Nat.add_one_mul_choose_eq (l-1) (k-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ l),Nat.sub_add_cancel (by omega : 1 ≤ k)] at h
  have hcast : (l:ℝ)*((l-1).choose (k-1):ℝ) = (l.choose k:ℝ)*k := by exact_mod_cast h
  unfold bfpWaitingMass
  have hL : (l:ℝ) ≠ 0 := by positivity
  field_simp
  linear_combination (p^k*(1-p)^(l-k))*hcast

private theorem bfpWaitingMass_stirling {p : ℝ} {k l : ℕ} (hp : 0 < p) (hp' : p < 1)
    (hk : 0 < k) (hl : k < l) :
    bfpWaitingMass p k l =
      (k:ℝ)/l * (Real.sqrt (2*l) / (Real.sqrt (2*k)*Real.sqrt (2*(l-k:ℕ)))) *
      (Stirling.stirlingSeq l / (Stirling.stirlingSeq k * Stirling.stirlingSeq (l-k))) *
      Real.exp ((k:ℝ)*Real.log ((l:ℝ)*p/k) +
        ((l-k:ℕ):ℝ)*Real.log ((l:ℝ)*(1-p)/(l-k:ℕ))) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hl.le
  have hd : 0 < d := by omega
  have hl' : 0 < k+d := by omega
  have hchoose : ((k+d).choose k:ℝ) = ((k+d).factorial:ℝ) / ((k.factorial:ℝ)*(d.factorial:ℝ)) := by
    apply (eq_div_iff (by positivity)).mpr
    have h := Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ k+d)
    rw [Nat.add_sub_cancel_left] at h
    exact_mod_cast (show (k+d).choose k * (k.factorial * d.factorial) = (k+d).factorial by rwa [← mul_assoc])
  rw [bfpWaitingMass_factor hk hl.le,Nat.add_sub_cancel_left,hchoose]
  unfold Stirling.stirlingSeq
  have hExp (x : ℝ) (hx : 0 < x) (n : ℕ) : Real.exp ((n:ℝ)*Real.log x) = x^n := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  rw [Real.exp_add,hExp _ (by positivity),hExp _ (by positivity)]
  simp only [pow_add,div_pow,mul_pow]
  field_simp
  <;> ring

private theorem bfpFree_eq_waiting {N : ℕ} (u v s t : ℝ)
    (h : bfpLabel N u < bfpLabel N v)
    (hl : bfpLabel N v-bfpLabel N u ≤ bfpLatticeSite N u s - bfpLatticeSite N v t) :
    bfpScaledFree N u v s t = bfpScale N *
      bfpWaitingMass (1/2) (bfpLabel N v-bfpLabel N u).toNat
        (bfpLatticeSite N u s - bfpLatticeSite N v t).toNat := by
  let k := bfpLabel N v-bfpLabel N u
  let l := bfpLatticeSite N u s-bfpLatticeSite N v t
  have hk : 0 < k := sub_pos.mpr h
  have hkl : k.toNat ≤ l.toNat := by dsimp [k,l]; omega
  have he : bfpLatticeSite N v t-bfpLatticeSite N u s = -(l.toNat:ℤ) := by omega
  simp only [bfpScaledFree,bfpFreeKer,h,hl,true_and,ite_true,bfpWaitingMass,he,
    zpow_neg,zpow_natCast]
  have h₁ : (l-1).toNat = l.toNat-1 := by omega
  have h₂ : (k-1).toNat = k.toNat-1 := by omega
  change bfpScale N * ((2:ℝ)^l.toNat)⁻¹ * ((l-1).toNat.choose (k-1).toNat:ℝ) = _
  have he' : (1/2:ℝ)^k.toNat*(1/2:ℝ)^(l.toNat-k.toNat) = ((2:ℝ)^l.toNat)⁻¹ := by
    rw [← pow_add,Nat.add_sub_of_le hkl,one_div,inv_pow]
  rw [h₁,h₂,show (1:ℝ)-1/2=1/2 by norm_num]
  change _ = bfpScale N * (((l.toNat-1).choose (k.toNat-1):ℝ) *
    (1/2)^k.toNat * (1/2)^(l.toNat-k.toNat))
  rw [mul_assoc ((l.toNat-1).choose (k.toNat-1):ℝ),he']
  ring

private theorem bfpWaitingMass_succ_ratio {p : ℝ} {k l : ℕ} (hk : 0 < k) (hl : k ≤ l) :
    bfpWaitingMass p k (l+1) * ((l+1-k:ℕ):ℝ) =
      bfpWaitingMass p k l * (1-p) * l := by
  have hl' : 0 < l := hk.trans_le hl
  have hs : l+1-k = (l-k)+1 := by omega
  have he : (l+1-1) = l := by omega
  have hchoose := Nat.choose_mul_succ_eq (l-1) (k-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ l),
    show l-(k-1)=l+1-k by omega] at hchoose
  have hc : ((l-1).choose (k-1):ℝ)*l =
      (l.choose (k-1):ℝ)*((l+1-k:ℕ):ℝ) := by exact_mod_cast hchoose
  simp only [bfpWaitingMass,he]
  have hpow : (1-p)^(l+1-k) = (1-p)^(l-k)*(1-p) := by rw [hs,pow_succ]
  rw [hpow]
  linear_combination -p^k * (1-p)^(l-k) * (1-p) * hc


private theorem bfpStirling_positive {k : ℕ} (hk : 0 < k) : 0 < Stirling.stirlingSeq k := by
  unfold Stirling.stirlingSeq
  positivity

private theorem bfpStirling_upper {k : ℕ} (hk : 0 < k) :
    Stirling.stirlingSeq k ≤ Real.exp 1 / Real.sqrt 2 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simpa using Stirling.stirlingSeq'_antitone (Nat.zero_le n)

private theorem bfpWaitingMass_central {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    {k l : ℕ} (hk : 0 < k) (hl : k < l) (hc : (k:ℝ)/6 ≤ (l-k:ℕ)) :
    bfpWaitingMass p k l ≤
      (Real.exp 1 / (Real.sqrt 2 * Real.pi) * Real.sqrt 3) / Real.sqrt k := by
  have hl₀ : 0 < l := by omega
  have hδ : 0 < l-k := by omega
  have h₀ := Real.log_le_sub_one_of_pos (show 0 < (l:ℝ)*p/k by positivity)
  have h₁ := Real.log_le_sub_one_of_pos (show 0 < (l:ℝ)*(1-p)/(l-k:ℕ) by positivity)
  have h₀' := mul_le_mul_of_nonneg_left h₀ (show 0 ≤ (k:ℝ) by positivity)
  have h₁' := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ ((l-k:ℕ):ℝ) by positivity)
  have hsum : (k:ℝ)*Real.log ((l:ℝ)*p/k) +
      ((l-k:ℕ):ℝ)*Real.log ((l:ℝ)*(1-p)/(l-k:ℕ)) ≤ 0 := by
    have hh₀ : (k:ℝ)*((l:ℝ)*p/k-1) = l*p-k := by field_simp <;> ring
    have hh₁ : ((l-k:ℕ):ℝ)*((l:ℝ)*(1-p)/(l-k:ℕ)-1) =
        l*(1-p)-(l-k:ℕ) := by field_simp <;> ring
    rw [hh₀] at h₀'
    rw [hh₁] at h₁'
    have hs : ((l-k:ℕ):ℝ) = (l:ℝ)-k := by exact_mod_cast Nat.cast_sub hl.le
    rw [hs] at h₁' ⊢
    linarith
  have hb : Real.exp ((k:ℝ)*Real.log ((l:ℝ)*p/k) +
      ((l-k:ℕ):ℝ)*Real.log ((l:ℝ)*(1-p)/(l-k:ℕ))) ≤ 1 := Real.exp_le_one_iff.mpr hsum
  have hS : Stirling.stirlingSeq l / (Stirling.stirlingSeq k * Stirling.stirlingSeq (l-k))
      ≤ Real.exp 1 / (Real.sqrt 2 * Real.pi) := by
    have hK := Stirling.sqrt_pi_le_stirlingSeq hk.ne'
    have hD := Stirling.sqrt_pi_le_stirlingSeq hδ.ne'
    have hP : Real.pi ≤ Stirling.stirlingSeq k * Stirling.stirlingSeq (l-k) := by
      rw [← Real.mul_self_sqrt Real.pi_pos.le]
      exact mul_le_mul hK hD (Real.sqrt_nonneg _) (bfpStirling_positive hk).le
    have hdpos := mul_pos (bfpStirling_positive hk) (bfpStirling_positive hδ)
    calc
      _ ≤ (Real.exp 1 / Real.sqrt 2) / (Stirling.stirlingSeq k * Stirling.stirlingSeq (l-k)) :=
        div_le_div_of_nonneg_right (bfpStirling_upper hl₀) hdpos.le
      _ ≤ (Real.exp 1 / Real.sqrt 2) / Real.pi :=
        div_le_div_of_nonneg_left (by positivity) Real.pi_pos hP
      _ = _ := by ring
  have hG : (k:ℝ)/l*(Real.sqrt (2*l)/(Real.sqrt (2*k)*Real.sqrt (2*(l-k:ℕ))))
      ≤ Real.sqrt 3 / Real.sqrt k := by
    have hP (z : ℝ) (hz : 0 ≤ z) : Real.sqrt (2*z) = Real.sqrt 2*Real.sqrt z :=
      Real.sqrt_mul (by positivity) z
    rw [hP _ (by positivity),hP _ (by positivity), hP _ (by positivity)]
    have hs : (k:ℝ)/l*(Real.sqrt 2*Real.sqrt l/
        ((Real.sqrt 2*Real.sqrt k)*(Real.sqrt 2*Real.sqrt (l-k:ℕ)))) =
        (Real.sqrt k/Real.sqrt l) * (Real.sqrt (2*(l-k:ℕ)))⁻¹ := by
      rw [hP _ (by positivity)]
      field_simp
      nlinarith only [Real.sq_sqrt (by positivity : 0 ≤ (k:ℝ)),
        Real.sq_sqrt (by positivity : 0 ≤ (l:ℝ))]
    rw [hs]
    have hA : Real.sqrt k/Real.sqrt l ≤ 1 := (div_le_one (by positivity)).mpr
      (Real.sqrt_le_sqrt (by exact_mod_cast hl.le))
    have hB : (Real.sqrt (2*(l-k:ℕ)))⁻¹ ≤ Real.sqrt 3/Real.sqrt k := by
      have hC : Real.sqrt k ≤ Real.sqrt 3*Real.sqrt (2*(l-k:ℕ)) := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ (3:ℝ))]
        apply Real.sqrt_le_sqrt
        linarith
      apply (inv_le_iff_one_le_mul₀ (by positivity)).mpr
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ (show 0 < Real.sqrt k by positivity)).mpr (by simpa using hC)
    exact (mul_le_mul hA hB (by positivity) zero_le_one).trans_eq (one_mul _)
  rw [bfpWaitingMass_stirling hp hp' hk hl]
  calc
    _ ≤ (Real.sqrt 3/Real.sqrt k) * (Real.exp 1/(Real.sqrt 2*Real.pi)) * 1 := by
      have hs : 0 ≤ Stirling.stirlingSeq l / (Stirling.stirlingSeq k * Stirling.stirlingSeq (l-k)) :=
        div_nonneg (bfpStirling_positive hl₀).le (mul_pos (bfpStirling_positive hk) (bfpStirling_positive hδ)).le
      exact mul_le_mul (mul_le_mul hG hS hs (by positivity)) hb (by positivity) (by positivity)
    _ = _ := by ring

private theorem bfpWaitingMass_mode {p : ℝ} (hp : 0 < p) (hp' : p ≤ 3/4)
    {k l : ℕ} (hk : 8 ≤ k) (hl : k ≤ l) :
    bfpWaitingMass p k l ≤
      (Real.exp 1 / (Real.sqrt 2 * Real.pi) * Real.sqrt 3) / Real.sqrt k := by
  let m := ⌊((k:ℝ)-1)/p⌋₊+1
  have hp₁ : p < 1 := by linarith
  have hM₁ : ((k:ℝ)-1)/p < m := by
    simpa [m] using Nat.lt_floor_add_one (((k:ℝ)-1)/p)
  have hk' : (8:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hM₂ : (m:ℝ)-1 ≤ ((k:ℝ)-1)/p := by
    simpa [m,Nat.cast_add] using Nat.floor_le (div_nonneg (by linarith : 0 ≤ (k:ℝ)-1) hp.le)
  have hc : (k:ℝ)/6 ≤ (m:ℝ)-k := by
    have hmp := (div_lt_iff₀ hp).mp hM₁
    have hpm := mul_le_mul_of_nonneg_right hp' (show 0 ≤ (m:ℝ) by positivity)
    linarith
  have hkM : k < m := by
    have hh : (k:ℝ)<(m:ℝ) := by linarith
    exact_mod_cast hh
  have hk₀ : 0 < k := by omega
  have hmono (j : ℕ) (hj : k ≤ j) (hj' : j < m) :
      bfpWaitingMass p k j ≤ bfpWaitingMass p k (j+1) := by
    have hr := bfpWaitingMass_succ_ratio (p := p) hk₀ hj
    have hd : 0 < ((j+1-k:ℕ):ℝ) := by exact_mod_cast (show 0 < j+1-k by omega)
    have hσ : ((j+1-k:ℕ):ℝ) ≤ (1-p)*j := by
      have hjm : (j:ℝ) ≤ (m:ℝ)-1 := by
        have hh : (j:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj'
        linarith
      have he := (le_div_iff₀ hp).mp (hjm.trans hM₂)
      rw [Nat.cast_sub (by omega : k ≤ j+1),Nat.cast_add,Nat.cast_one]
      linarith
    apply (le_of_mul_le_mul_right · hd)
    rw [hr,mul_assoc]
    exact mul_le_mul_of_nonneg_left hσ (bfpWaitingMass_nonneg hp.le hp₁.le _ _)
  have hanti (j : ℕ) (hj : m ≤ j) :
      bfpWaitingMass p k (j+1) ≤ bfpWaitingMass p k j := by
    have hkj := hkM.le.trans hj
    have hd : 0 < ((j+1-k:ℕ):ℝ) := by exact_mod_cast (show 0 < j+1-k by omega)
    apply (le_of_mul_le_mul_right · hd)
    rw [bfpWaitingMass_succ_ratio (p := p) hk₀ hkj]
    have hσ : (1-p)*(j:ℝ) ≤ ((j+1-k:ℕ):ℝ) := by
      have hmp := (div_lt_iff₀ hp).mp hM₁
      have hpj := mul_le_mul_of_nonneg_right (show (m:ℝ) ≤ j by exact_mod_cast hj) hp.le
      rw [Nat.cast_sub (by omega : k ≤ j+1),Nat.cast_add,Nat.cast_one]
      linarith
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hσ (bfpWaitingMass_nonneg hp.le hp₁.le _ _)
  have hm : bfpWaitingMass p k l ≤ bfpWaitingMass p k m := by
    rcases le_total l m with h | h
    · have hrec (j : ℕ) (hlj : l ≤ j) : j ≤ m →
          bfpWaitingMass p k l ≤ bfpWaitingMass p k j := by
        induction j,hlj using Nat.le_induction with
        | base => exact fun _ => le_rfl
        | succ j hj ih =>
          intro hj'
          exact (ih (by omega)).trans (hmono j (hl.trans hj) (by omega))
      exact hrec m h le_rfl
    · exact (antitoneOn_nat_Ici_of_succ_le (fun j hj => hanti j hj))
        (Set.mem_Ici.mpr le_rfl) (show l ∈ Set.Ici m from h) h
  refine hm.trans (bfpWaitingMass_central hp hp₁ hk₀ hkM ?_)
  rw [Nat.cast_sub hkM.le]
  exact hc


private theorem bfpWaitingMass_tilt {k l : ℕ} (hl : k ≤ l) (z : ℝ)
    (hp : 0 < 1-Real.exp z/2) :
    bfpWaitingMass (1/2) k l =
      bfpWaitingMass (1-Real.exp z/2) k l *
        Real.exp (-z*((l:ℝ)-2*k) + (k:ℝ)*(-z-Real.log (2*(1-Real.exp z/2)))) := by
  let p := 1-Real.exp z/2
  let d := l-k
  have hL : (l:ℝ)=(k:ℝ)+d := by dsimp [d]; rw [Nat.cast_sub hl]; ring
  have hE : -z*((l:ℝ)-2*k) + (k:ℝ)*(-z-Real.log (2*p)) =
      (d:ℝ)*(-z)+(k:ℝ)*(-Real.log (2*p)) := by rw [hL]; ring
  change _ = bfpWaitingMass p k l * Real.exp _
  rw [hE,Real.exp_add,Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_neg,Real.exp_neg,
    Real.exp_log (by positivity : 0 < 2*p)]
  have hq : 1-p = Real.exp z/2 := by dsimp [p]; ring
  unfold bfpWaitingMass
  rw [hq,show (1:ℝ)-1/2=1/2 by norm_num]
  dsimp [d]
  simp only [div_pow,inv_pow,mul_pow]
  have hp0 : p ≠ 0 := hp.ne'
  field_simp [hp0,ne_of_gt (Real.exp_pos z)]
  ring_nf

private theorem bfpWaitingMass_exp_tail {k l : ℕ} (hk : 8 ≤ k) (hl : k ≤ l)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/8) :
    bfpWaitingMass (1/2) k l ≤
      ((Real.exp 1/(Real.sqrt 2*Real.pi)*Real.sqrt 3)/Real.sqrt k) *
        Real.exp (-δ * |(l:ℝ)-2*k| + 8*k*δ^2) := by
  let D := (l:ℝ)-2*k
  let z := if 0 ≤ D then δ else -δ
  let p := 1-Real.exp z/2
  have hz : |z| = δ := by unfold z; split_ifs <;> simp [abs_of_pos hδ]
  have hE := Real.abs_exp_sub_one_le (show |z| ≤ 1 by rw [hz]; linarith)
  rw [hz,abs_le] at hE
  have hp : 0 < p := by dsimp [p]; linarith [hE.2]
  have hp' : p ≤ 3/4 := by dsimp [p]; linarith [hE.1]
  have ht : -z*D = -δ * |D| := by unfold z; split_ifs with h <;> simp [abs_of_nonneg,abs_of_neg,h,lt_of_not_ge] <;> ring
  have hn : -z-Real.log (2*p) ≤ 8*δ^2 := by
    let a := (Real.exp z-1)^2
    have ha : 0 ≤ a := sq_nonneg _
    have ha' : a ≤ 4*δ^2 := by
      dsimp [a]
      nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hE.2),
        mul_nonneg (sub_nonneg.mpr hE.2) (sub_nonneg.mpr (neg_le.mp (by linarith [hE.1] :
           -(Real.exp z-1) ≤ 2*δ)))]
    have ha₁ : a ≤ 1/2 := by nlinarith
    have ha₂ : 0 < 1-a := by linarith
    have he : Real.exp z*(2*p)=1-a := by dsimp [p,a]; ring
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr ha₂)
    rw [Real.log_inv] at hh
    rw [sub_eq_add_neg, ← neg_add, ← Real.log_exp z,← Real.log_mul (Real.exp_pos z).ne' (by positivity), he]
    refine hh.trans ?_
    rw [inv_eq_one_div, sub_le_iff_le_add,div_le_iff₀ ha₂]
    have hA : a ≤ 8*δ^2*(1-a) := by
      refine ha'.trans ?_
      have h := mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ 1-a by linarith)
        (show 0 ≤ 8*δ^2 by positivity)
      nlinarith
    linarith
  rw [bfpWaitingMass_tilt hl z hp]
  have hM := bfpWaitingMass_mode hp hp' hk hl
  have hEx : -z*((l:ℝ)-2*k)+(k:ℝ)*(-z-Real.log (2*p)) ≤ -δ * |(l:ℝ)-2*k| + 8*k*δ^2 := by
    change -z*D+_ ≤ -δ * |D| + _
    rw [ht]
    nlinarith [mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg k)]
  exact mul_le_mul hM (Real.exp_le_exp.mpr hEx) (Real.exp_pos _).le (by positivity)

private theorem bfpRawGap_normalized (u v : ℝ) :
    Tendsto (fun N : ℕ => ((bfpLabel N v-bfpLabel N u:ℤ):ℝ)/(bfpScale N)^2) atTop
      (𝓝 (v-u)) := by
  let err (N : ℕ) := ((bfpLabel N v-bfpLabel N u:ℤ):ℝ)-bfpScale N^2*(v-u)
  have hi := bfpScale_inv_tendsto_zero.pow 2
  have he : Tendsto (fun N => err N*((bfpScale N)⁻¹)^2) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) ?_ (by simpa using hi)
    intro N
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0 ≤ ((bfpScale N)⁻¹)^2)]
    rw [inv_pow]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (sq_nonneg _)) (bfpGap_errors N u v 0 0).1.le
  have h := he.add_const (v-u)
  refine (by simpa only [zero_add] using h : Tendsto _ _ _).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn := (bfpScale_pos hN).ne'
  dsimp [err]
  field_simp
  ring

/-- The free term has uniform exponential decay in the spatial difference. -/
theorem bfpScaledFree_tail (u v : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ s₁ s₂ : ℝ, |bfpScaledFree N u v s₁ s₂| ≤ C * Real.exp (-|s₁ - s₂|) := by
  by_cases hd : u < v
  swap
  · refine ⟨1,by norm_num,Eventually.of_forall ?_⟩
    intro N s t
    rw [bfpScaledFree_eq_zero_of_ge N (le_of_not_gt hd),abs_zero]
    positivity
  let d := v-u
  have hd₀ : 0 < d := sub_pos.mpr hd
  let A := Real.exp 1/(Real.sqrt 2*Real.pi)*Real.sqrt 3
  refine ⟨A*Real.sqrt (2/d)*Real.exp (8*(d+1)+3),by positivity,?_⟩
  have hlim : Tendsto (fun N : ℕ => ((bfpLabel N v-bfpLabel N u:ℤ):ℝ)/(bfpScale N)^2) atTop (𝓝 d) :=
    bfpRawGap_normalized u v
  filter_upwards [hlim.eventually_const_lt (show d/2<d by linarith),
    hlim.eventually_lt_const (show d<d+1 by linarith),
    bfpScale_tendsto_atTop.eventually_ge_atTop (max 8 (Real.sqrt (16/d)))] with N hlo hhi hσ s t
  let σ := bfpScale N
  let k := bfpLabel N v-bfpLabel N u
  let l := bfpLatticeSite N u s-bfpLatticeSite N v t
  let δ := σ⁻¹
  have hσ₈ : 8 ≤ σ := (le_max_left _ _).trans hσ
  have hσ₀ : 0 < σ := by linarith
  have hδ : 0 < δ := inv_pos.mpr hσ₀
  have hδ' : δ ≤ 1/8 := (inv_le_comm₀ hσ₀ (by norm_num)).mpr (by simpa using hσ₈)
  have hK : d/2*σ^2 < (k:ℝ) := (lt_div_iff₀ (by positivity)).mp hlo
  have hK' : (k:ℝ) < (d+1)*σ^2 := (div_lt_iff₀ (by positivity)).mp hhi
  have hk : 0 < k := by
    have hk : 0 < (k:ℝ) := lt_trans (by positivity) hK
    exact_mod_cast hk
  have hk₈ : 8 ≤ k.toNat := by
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) ((le_max_right _ _).trans hσ) 2
    rw [Real.sq_sqrt (by positivity)] at hs
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ d/2 by positivity)
    have hD : d/2*(16/d)=8 := by field_simp; ring
    rw [hD] at hh
    have he : (k.toNat:ℤ)=k := Int.toNat_of_nonneg hk.le
    have h₈ : (8:ℝ) ≤ (k.toNat:ℝ) := by rw [← Int.cast_natCast,he]; exact hh.trans hK.le
    exact_mod_cast h₈
  have htime : bfpLabel N u < bfpLabel N v := sub_pos.mp hk
  by_cases hl : k ≤ l
  swap
  · have htest : ¬(bfpLabel N u < bfpLabel N v ∧
        bfpLabel N v-bfpLabel N u ≤ bfpLatticeSite N u s-bfpLatticeSite N v t) :=
      fun h => hl h.2
    simp only [bfpScaledFree,bfpFreeKer,ite_eq_right htest,mul_zero,abs_zero]
    positivity
  have hle : k.toNat ≤ l.toNat := by omega
  have hKN : (k.toNat:ℝ)=(k:ℝ) := by rw [← Int.cast_natCast,Int.toNat_of_nonneg hk.le]
  have hLN : (l.toNat:ℝ)=(l:ℝ) := by rw [← Int.cast_natCast,Int.toNat_of_nonneg (hk.le.trans hl)]
  have hmass := bfpWaitingMass_exp_tail hk₈ hle hδ hδ'
  rw [hKN,hLN] at hmass
  have he := (bfpGap_errors N u v s t).2
  change |(l:ℝ)-2*(k:ℝ)-σ*(t-s)| < 3 at he
  have hAbs : σ*|s-t| ≤ |(l:ℝ)-2*(k:ℝ)| + 3 := by
    have h := abs_sub_le (σ*(t-s)) ((l:ℝ)-2*(k:ℝ)) 0
    simp only [sub_zero,abs_sub_comm (σ*(t-s)),abs_mul,abs_of_pos hσ₀] at h
    rw [abs_sub_comm s t]
    linarith
  have h1 := mul_le_mul_of_nonneg_left hAbs hδ.le
  have h2 := mul_le_mul_of_nonneg_right hK'.le (show 0 ≤ δ^2 by positivity)
  have hcancel : δ*σ=1 := inv_mul_cancel₀ hσ₀.ne'
  have hcancel2 : σ^2*δ^2=1 := by rw [← mul_pow,mul_comm σ,hcancel,one_pow]
  have ht : -δ * |(l:ℝ)-2*(k:ℝ)| + 8*(k:ℝ)*δ^2 ≤ -|s-t| + 8*(d+1)+3 := by
    have hA : |s-t| ≤ δ*|(l:ℝ)-2*(k:ℝ)| + 3*δ := by
      rw [← mul_assoc,hcancel,one_mul,mul_add,mul_comm δ 3] at h1
      exact h1
    have hB : (k:ℝ)*δ^2 ≤ d+1 := by simpa only [mul_assoc,hcancel2,mul_one] using h2
    linarith [abs_nonneg (s-t)]
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have hS : σ/Real.sqrt (k:ℝ) ≤ Real.sqrt (2/d) := by
    have h := Real.sqrt_le_sqrt hK.le
    rw [Real.sqrt_mul (by positivity),Real.sqrt_sq hσ₀.le] at h
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hkR)).mpr
    have hH : Real.sqrt (2/d)*Real.sqrt (d/2)=1 := by
      rw [← Real.sqrt_mul (by positivity),show 2/d*(d/2)=1 by field_simp,Real.sqrt_one]
    have hh := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg (2/d))
    rwa [← mul_assoc,hH,one_mul] at hh
  rw [bfpFree_eq_waiting u v s t htime hl,abs_of_nonneg
      (mul_nonneg hσ₀.le (bfpWaitingMass_nonneg (by norm_num) (by norm_num) _ _))]
  refine (mul_le_mul_of_nonneg_left hmass hσ₀.le).trans ?_
  change σ*(A/Real.sqrt (k:ℝ) * _) ≤ _
  rw [show σ*(A/Real.sqrt (k:ℝ)*Real.exp (-δ * |(l:ℝ)-2*(k:ℝ)| + 8*(k:ℝ)*δ^2)) =
      A*(σ/Real.sqrt (k:ℝ))*Real.exp (-δ * |(l:ℝ)-2*(k:ℝ)| + 8*(k:ℝ)*δ^2) by ring]
  calc
    _ ≤ A*Real.sqrt (2/d)*Real.exp (-|s-t| + 8*(d+1)+3) := by
      gcongr
    _ = _ := by rw [show -|s-t| + 8*(d+1)+3 = (8*(d+1)+3)+ -|s-t| by ring,Real.exp_add]; ring


private noncomputable def bfpEntropy (x : ℝ) : ℝ :=
  (1+x)*Real.log (1+x)+(1-x)*Real.log (1-x)

private theorem bfpEntropy_approx {x : ℝ} (hx : |x| ≤ 1/2) :
    |bfpEntropy x-x^2| ≤ 4 * |x|^3 := by
  have hp := Real.abs_log_sub_add_sum_range_le (x := -x)
    (by rw [abs_neg]; linarith : |-x| < 1) 2
  have hm := Real.abs_log_sub_add_sum_range_le (x := x) (by linarith : |x|<1) 2
  norm_num [Finset.sum_range_succ,abs_neg] at hp hm
  have h := (abs_le.mp hx)
  have hD : 0 < 1-|x| := by linarith
  have hcmp : |x|^3/(1-|x|) ≤ 2 * |x|^3 := by
    rw [div_le_iff₀ hD]
    have hm := mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ 1-|x| by linarith)
      (show 0 ≤ 2 * |x|^3 by positivity)
    nlinarith
  let a := Real.log (1+x)-(x-x^2/2)
  let b := Real.log (1-x)-(-x-x^2/2)
  have ha : |a| ≤ 2 * |x|^3 := by
    refine le_trans ?_ hcmp
    convert hp using 1 <;> dsimp [a] <;> ring
  have hb : |b| ≤ 2 * |x|^3 := by
    refine le_trans ?_ hcmp
    convert hm using 1 <;> dsimp [b] <;> ring
  have he : bfpEntropy x-x^2 = (1+x)*a+(1-x)*b := by unfold bfpEntropy a b; ring
  rw [he]
  have h₁ : 0 ≤ 1+x := by linarith
  have h₂ : 0 ≤ 1-x := by linarith
  calc
    _ ≤ |(1+x)*a|+|(1-x)*b| := abs_add_le _ _
    _ ≤ (1+x)*(2 * |x|^3)+(1-x)*(2 * |x|^3) := by
      rw [abs_mul,abs_mul,abs_of_nonneg h₁,abs_of_nonneg h₂]
      exact add_le_add (mul_le_mul_of_nonneg_left ha h₁) (mul_le_mul_of_nonneg_left hb h₂)
    _ = _ := by ring

private noncomputable def bfpEntropyRatio (x : ℝ) : ℝ := if x=0 then 1 else bfpEntropy x/x^2

private theorem bfpEntropyRatio_tendsto : Tendsto bfpEntropyRatio (𝓝 0) (𝓝 1) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (g := fun x : ℝ => 4 * |x|) (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · have h : ∀ᶠ x : ℝ in 𝓝 (0:ℝ), |x|<1/2 := by
      simpa only [Real.norm_eq_abs,sub_zero] using eventually_norm_sub_lt (0:ℝ)
        (by norm_num : 0 < (1/2:ℝ))
    filter_upwards [h] with x hx
    by_cases hx₀ : x=0
    · simp [hx₀,bfpEntropyRatio]
    · rw [Real.norm_eq_abs,bfpEntropyRatio,ite_eq_right hx₀,div_sub_one (pow_ne_zero 2 hx₀),
        abs_div,abs_of_nonneg (sq_nonneg x)]
      apply (div_le_iff₀ (sq_pos_of_ne_zero hx₀)).mpr
      refine (bfpEntropy_approx hx.le).trans_eq ?_
      rw [show |x| ^ 3 = |x| * x^2 by
        calc
          _ = |x| * |x| ^ 2 := by ring
          _ = _ := by rw [sq_abs]]
      ring
  · simpa [Real.norm_eq_abs] using (continuous_abs.continuousAt.tendsto
      (x := (0:ℝ))).const_mul (4:ℝ)

private theorem bfpFree_entropy_exact {k l : ℕ} (hk : 0 < k) (hl : k < l) :
    let x := ((l:ℝ)-2*k)/l
    (k:ℝ)*Real.log ((l:ℝ)*(1/2)/k) + ((l-k:ℕ):ℝ)*Real.log ((l:ℝ)*(1-1/2)/(l-k:ℕ)) =
      -((l:ℝ)/2)*bfpEntropy x := by
  let x := ((l:ℝ)-2*k)/l
  have hK : 0 < (k:ℝ) := by exact_mod_cast hk
  have hL : 0 < (l:ℝ) := by exact_mod_cast hk.trans hl
  have hd : 0 < ((l-k:ℕ):ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hl
  change _ = -((l:ℝ)/2)*bfpEntropy x
  have hs : ((l-k:ℕ):ℝ) = (l:ℝ)-k := Nat.cast_sub hl.le
  have h₁ : 1+x = 2*((l-k:ℕ):ℝ)/l := by dsimp [x]; rw [hs]; field_simp; ring
  have h₂ : 1-x = 2*(k:ℝ)/l := by dsimp [x]; field_simp; ring
  have hlog₁ : (l:ℝ)*(1/2)/k=(1-x)⁻¹ := by rw [h₂]; field_simp
  have hlog₂ : (l:ℝ)*(1-1/2)/(l-k:ℕ)=(1+x)⁻¹ := by rw [h₁]; field_simp <;> ring
  rw [hlog₁,hlog₂,Real.log_inv,Real.log_inv,bfpEntropy]
  generalize Real.log (1+x) = p
  generalize Real.log (1-x) = q
  rw [h₁,h₂]
  field_simp
  <;> ring

private theorem bfpSmallError_mul {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (hg : Tendsto g l (𝓝 0)) {C : ℝ} (hf : ∀ i, |f i| ≤ C) :
    Tendsto (fun i => f i*g i) l (𝓝 0) := by
  have hnorm : Tendsto (fun i => |g i|) l (𝓝 0) := by simpa [Real.norm_eq_abs] using hg.norm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) ?_ (by simpa using hnorm.const_mul C)
  intro i
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_right (hf i) (abs_nonneg _)

private theorem bfpFree_scaling_rates {ι : Type*} {l : Filter ι}
    {n : ι → ℕ} {s t : ι → ℝ} {s₀ t₀ : ℝ}
    (hn : Tendsto n l atTop) (hs : Tendsto s l (𝓝 s₀)) (ht : Tendsto t l (𝓝 t₀))
    (u v : ℝ) (hUV : u < v) :
    let σ (i : ι) := bfpScale (n i)
    let k (i : ι) := (bfpLabel (n i) v-bfpLabel (n i) u).toNat
    let a (i : ι) := (bfpLatticeSite (n i) u (s i)-bfpLatticeSite (n i) v (t i)).toNat
    Tendsto (fun i => (k i:ℝ)/(σ i)^2) l (𝓝 (v-u)) ∧
      Tendsto (fun i => (a i:ℝ)/(σ i)^2) l (𝓝 (2*(v-u))) ∧
      Tendsto (fun i => ((a i:ℝ)-2*k i)/σ i) l (𝓝 (t₀-s₀)) ∧
      ∀ᶠ i in l, 0 < bfpLabel (n i) v-bfpLabel (n i) u ∧
        bfpLabel (n i) v-bfpLabel (n i) u <
          bfpLatticeSite (n i) u (s i)-bfpLatticeSite (n i) v (t i) := by
  let σ (i : ι) := bfpScale (n i)
  let κ (i : ι) := bfpLabel (n i) v-bfpLabel (n i) u
  let b (i : ι) := bfpLatticeSite (n i) u (s i)-bfpLatticeSite (n i) v (t i)
  let δ (i : ι) := (σ i)⁻¹
  let e (i : ι) := (b i:ℝ)-2*(κ i:ℝ)-σ i*(t i-s i)
  have hσ := bfpScale_tendsto_atTop.comp hn
  have hδ : Tendsto δ l (𝓝 0) := bfpScale_inv_tendsto_zero.comp hn
  have hσ₀ : ∀ᶠ i in l, 0 < σ i := hσ.eventually_gt_atTop 0
  have hκ := (bfpRawGap_normalized u v).comp hn
  have he := bfpSmallError_mul hδ (fun i => (bfpGap_errors (n i) u v (s i) (t i)).2.le)
  have hgap : Tendsto (fun i => ((b i:ℝ)-2*(κ i:ℝ))/σ i) l (𝓝 (t₀-s₀)) := by
    have h := (ht.sub hs).add he
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [hσ₀] with i hi
    change t i-s i+e i*δ i = _
    dsimp [e,δ]
    field_simp
    ring
  have hbLim : Tendsto (fun i => (b i:ℝ)/(σ i)^2) l (𝓝 (2*(v-u))) := by
    have h := (hgap.mul hδ).add (hκ.const_mul 2)
    rw [mul_zero,zero_add] at h
    refine h.congr' ?_
    filter_upwards [hσ₀] with i hi
    change ((b i:ℝ)-2*(κ i:ℝ))/σ i*δ i+2*((κ i:ℝ)/(σ i)^2) = _
    dsimp [δ]
    ring
  have hkl := (hbLim.sub hκ).eventually_const_lt (show 0 < 2*(v-u)-(v-u) by linarith)
  have hk := hκ.eventually_const_lt (sub_pos.mpr hUV)
  have hSupp : ∀ᶠ i in l, 0 < κ i ∧ κ i < b i := by
    filter_upwards [hk,hkl,hσ₀] with i h₁ h₂ h₃
    change 0 < ((κ i:ℝ)/(σ i)^2) at h₁
    change 0 < ((b i:ℝ)/(σ i)^2)-((κ i:ℝ)/(σ i)^2) at h₂
    have hκ₀ : 0 < (κ i:ℝ) := (div_pos_iff_of_pos_right (by positivity)).mp h₁
    have hkb : (κ i:ℝ) < (b i:ℝ) := (div_lt_div_iff_of_pos_right (by positivity)).mp (sub_pos.mp h₂)
    exact ⟨by exact_mod_cast hκ₀,by exact_mod_cast hkb⟩
  have hInt : ∀ᶠ i in l, ((κ i).toNat:ℤ) = κ i ∧ ((b i).toNat:ℤ) = b i :=
    hSupp.mono (fun i hi => ⟨Int.toNat_of_nonneg hi.1.le,Int.toNat_of_nonneg (hi.1.le.trans hi.2.le)⟩)
  have hR : ∀ᶠ i in l, ((κ i).toNat:ℝ) = (κ i:ℝ) ∧ ((b i).toNat:ℝ) = (b i:ℝ) :=
    hInt.mono (fun i hi => ⟨by exact_mod_cast hi.1,by exact_mod_cast hi.2⟩)
  refine ⟨hκ.congr' ?_,hbLim.congr' ?_,hgap.congr' ?_,hSupp⟩
  · filter_upwards [hR] with i hi
    change (κ i:ℝ)/(σ i)^2 = ((κ i).toNat:ℝ)/(σ i)^2
    rw [hi.1]
  · filter_upwards [hR] with i hi
    change (b i:ℝ)/(σ i)^2 = ((b i).toNat:ℝ)/(σ i)^2
    rw [hi.2]
  · filter_upwards [hR] with i hi
    change ((b i:ℝ)-2*(κ i:ℝ))/σ i = (((b i).toNat:ℝ)-2*((κ i).toNat:ℝ))/σ i
    rw [hi.1,hi.2]


private theorem bfpNat_atTop_of_rate {ι : Type*} {l : Filter ι} {k : ι → ℕ} {σ : ι → ℝ}
    (hσ : Tendsto σ l atTop) {d : ℝ} (hd : 0 < d)
    (hk : Tendsto (fun i => (k i:ℝ)/(σ i)^2) l (𝓝 d)) :
    Tendsto k l atTop := by
  have h := ((tendsto_pow_atTop (α := ℝ) (n := 2) (by decide)).comp hσ).const_mul_atTop
    (show 0 < d/2 by positivity)
  have hle : ∀ᶠ i in l, d/2*(σ i)^2 ≤ (k i:ℝ) := by
    filter_upwards [hk.eventually_const_lt (show d/2<d by linarith),hσ.eventually_gt_atTop 0] with i hi hσ'
    exact ((lt_div_iff₀ (by positivity)).mp hi).le
  exact tendsto_natCast_atTop_iff.mp (tendsto_atTop_mono' _ hle h)

private theorem bfpFree_prefactor {σ : ℝ} (hσ : 0 < σ) {k l : ℕ} (hk : 0 < k) (hl : k < l) :
    σ*((k:ℝ)/l*(Real.sqrt (2*l)/(Real.sqrt (2*k)*Real.sqrt (2*(l-k:ℕ))))) =
      ((k:ℝ)/σ^2)/((l:ℝ)/σ^2) *
        (Real.sqrt (2*((l:ℝ)/σ^2))/
          (Real.sqrt (2*((k:ℝ)/σ^2))*Real.sqrt (2*(((l-k:ℕ):ℝ)/σ^2)))) := by
  have hM : 0 < (l-k:ℕ) := by omega
  have hS (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (2*(x/σ^2)) = Real.sqrt (2*x)/σ := by
    rw [← mul_div_assoc, Real.sqrt_div (by positivity),Real.sqrt_sq hσ.le]
  rw [hS _ (by positivity),hS _ (by positivity),hS _ (by positivity)]
  field_simp [hσ.ne']

private theorem bfpFree_gaussian_limit {ι : Type*} {l : Filter ι}
    {σ : ι → ℝ} {k m : ι → ℕ} {d r : ℝ}
    (hd : 0 < d) (hσ : Tendsto σ l atTop)
    (hk : Tendsto (fun i => (k i:ℝ)/(σ i)^2) l (𝓝 d))
    (hm : Tendsto (fun i => (m i:ℝ)/(σ i)^2) l (𝓝 (2*d)))
    (hgap : Tendsto (fun i => ((m i:ℝ)-2*k i)/σ i) l (𝓝 r))
    (hSupp : ∀ᶠ i in l, 0 < k i ∧ k i < m i) :
    Tendsto (fun i => σ i*bfpWaitingMass (1/2) (k i) (m i)) l (𝓝 (heatKernel d r)) := by
  let K (i : ι) := (k i:ℝ)/(σ i)^2
  let M (i : ι) := (m i:ℝ)/(σ i)^2
  let D (i : ι) := ((m i-k i:ℕ):ℝ)/(σ i)^2
  let τ (i : ι) := ((m i:ℝ)-2*k i)/σ i
  let x (i : ι) := ((m i:ℝ)-2*k i)/(m i:ℝ)
  have hD : Tendsto D l (𝓝 d) := by
    have h := hm.sub hk
    rw [show 2*d-d=d by ring] at h
    refine h.congr' ?_
    filter_upwards [hSupp] with i hi
    dsimp [D]
    rw [Nat.cast_sub hi.2.le,sub_div]
  have hX : Tendsto x l (𝓝 0) := by
    have h := (hgap.div hm (show 2*d ≠ 0 by positivity)).mul (tendsto_inv_atTop_zero.comp hσ)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [hSupp,hσ.eventually_gt_atTop 0] with i hi hσi
    have hmi : (m i:ℝ) ≠ 0 := by exact_mod_cast (hi.1.trans hi.2).ne'
    dsimp [x, Function.comp_def, Pi.div_apply]
    field_simp <;> ring
  have hExp : Tendsto (fun i => -((m i:ℝ)/2)*bfpEntropy (x i)) l (𝓝 (-(r^2/(4*d)))) := by
    have h := ((hgap.pow 2).div hm (show 2*d ≠ 0 by positivity)).mul (bfpEntropyRatio_tendsto.comp hX)
    have h' := h.const_mul (-1/2)
    have he : (-1/2:ℝ)*(r^2/(2*d)*1) = -(r^2/(4*d)) := by field_simp; ring
    rw [he] at h'
    refine h'.congr' ?_
    filter_upwards [hSupp,hσ.eventually_gt_atTop 0] with i hi hσi
    have hm : (m i:ℝ) ≠ 0 := by exact_mod_cast (hi.1.trans hi.2).ne'
    by_cases hx : x i=0
    · have hnum : (m i:ℝ)-2*k i=0 := (div_eq_zero_iff.mp hx).resolve_right hm
      simp [hnum,hx,bfpEntropy]
    · have he : (x i)^2 ≠ 0 := pow_ne_zero _ hx
      change (-1/2:ℝ)*((((m i:ℝ)-2*k i)/σ i)^2 / ((m i:ℝ)/(σ i)^2)*bfpEntropyRatio (x i)) = _
      simp only [bfpEntropyRatio,ite_eq_right hx,x]
      have hnum : (m i:ℝ)-2*k i ≠ 0 := by intro h; exact hx (by simp [x,h])
      field_simp <;> ring
  have hS := (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (bfpNat_atTop_of_rate hσ (by positivity : 0 < 2*d) hm)).div
    ((Stirling.tendsto_stirlingSeq_sqrt_pi.comp (bfpNat_atTop_of_rate hσ hd hk)).mul
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (bfpNat_atTop_of_rate hσ hd hD))) (by positivity)
  have hP := (hk.div hm (by positivity)).mul
    ((Real.continuous_sqrt.continuousAt.tendsto.comp (hm.const_mul 2)).div
      ((Real.continuous_sqrt.continuousAt.tendsto.comp (hk.const_mul 2)).mul
        (Real.continuous_sqrt.continuousAt.tendsto.comp (hD.const_mul 2))) (by positivity))
  have h := (hP.mul hS).mul (Real.continuous_exp.continuousAt.tendsto.comp hExp)
  have hg : (d/(2*d)*(Real.sqrt (2*(2*d))/(Real.sqrt (2*d)*Real.sqrt (2*d)))) *
      (Real.sqrt Real.pi/(Real.sqrt Real.pi*Real.sqrt Real.pi))*Real.exp (-(r^2/(4*d))) =
      heatKernel d r := by
    unfold heatKernel
    rw [show (-1/2:ℝ)=-(1/2) by ring,Real.rpow_neg (by positivity),← Real.sqrt_eq_rpow]
    have h4 : Real.sqrt 4 = 2 := by rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]
    have h₁ : Real.sqrt (2*(2*d))=2*Real.sqrt d := by
      rw [show 2*(2*d)=4*d by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤4),h4]
    have h₂ : Real.sqrt (4*Real.pi*d)=2*Real.sqrt Real.pi*Real.sqrt d := by
      rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by norm_num : (0:ℝ)≤4),h4]
    rw [h₁,h₂, ← pow_two (Real.sqrt (2*d)),Real.sq_sqrt (by positivity)]
    field_simp
    nlinarith [Real.sq_sqrt hd.le]
  rw [hg] at h
  refine h.congr' ?_
  filter_upwards [hSupp,hσ.eventually_gt_atTop 0] with i hi hσi
  change (K i/M i*(Real.sqrt (2*M i)/(Real.sqrt (2*K i)*Real.sqrt (2*D i)))) *
      (Stirling.stirlingSeq (m i)/(Stirling.stirlingSeq (k i)*Stirling.stirlingSeq (m i-k i))) *
      Real.exp (-((m i:ℝ)/2)*bfpEntropy (x i)) = _
  rw [bfpWaitingMass_stirling (by norm_num : (0:ℝ)<1/2) (by norm_num) hi.1 hi.2,
    bfpFree_entropy_exact hi.1 hi.2]
  have hP' : σ i*((k i:ℝ)/m i*(Real.sqrt (2*m i)/
      (Real.sqrt (2*k i)*Real.sqrt (2*(m i-k i:ℕ))))) =
      K i/M i*(Real.sqrt (2*M i)/(Real.sqrt (2*K i)*Real.sqrt (2*D i))) :=
    bfpFree_prefactor hσi hi.1 hi.2
  rw [← hP']
  dsimp [x]
  ring

private theorem bfpFree_tendsto_filter {ι : Type*} {l : Filter ι}
    {n : ι → ℕ} {s t : ι → ℝ} {s₀ t₀ : ℝ}
    (hn : Tendsto n l atTop) (hs : Tendsto s l (𝓝 s₀)) (ht : Tendsto t l (𝓝 t₀))
    (u v : ℝ) :
    Tendsto (fun j => bfpScaledFree (n j) u v (s j) (t j)) l
      (𝓝 (if u<v then heatKernel (v-u) (s₀-t₀) else 0)) := by
  by_cases hUV : u<v
  · rw [ite_eq_left hUV]
    obtain ⟨hk,hm,hgap,hSupp⟩ := bfpFree_scaling_rates hn hs ht u v hUV
    let k (i : ι) := (bfpLabel (n i) v-bfpLabel (n i) u).toNat
    let m (i : ι) := (bfpLatticeSite (n i) u (s i)-bfpLatticeSite (n i) v (t i)).toNat
    have hS : ∀ᶠ i in l, 0 < k i ∧ k i < m i := hSupp.mono (fun i h => by dsimp [k,m]; omega)
    have h := bfpFree_gaussian_limit (sub_pos.mpr hUV) (bfpScale_tendsto_atTop.comp hn) hk hm hgap hS
    have he : heatKernel (v-u) (t₀-s₀)=heatKernel (v-u) (s₀-t₀) := by unfold heatKernel; ring_nf
    rw [he] at h
    exact h.congr' (hSupp.mono (fun i hi =>
      (bfpFree_eq_waiting u v (s i) (t i) (sub_pos.mp hi.1) hi.2.le).symm))
  · rw [ite_eq_right hUV]
    exact tendsto_const_nhds.congr' (Eventually.of_forall (fun i =>
      (bfpScaledFree_eq_zero_of_ge (n i) (le_of_not_gt hUV) (s i) (t i)).symm))

/-- Stirling's formula gives the local Gaussian limit for increasing time pairs. -/
theorem bfpScaledFree_tendstoUniformlyOn (u v : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    TendstoUniformlyOn (fun N : ℕ => fun p : ℝ × ℝ => bfpScaledFree N u v p.1 p.2)
      (fun p => if u < v then heatKernel (v - u) (p.1 - p.2) else 0)
      atTop (Set.Icc (-L) L ×ˢ Set.Icc (-L) L) := by
  let S := Set.Icc (-L) L ×ˢ Set.Icc (-L) L
  let F (p : ℝ×ℝ) := if u<v then heatKernel (v-u) (p.1-p.2) else 0
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS).mp
  apply tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro p hp
  let l := (atTop : Filter ℕ) ×ˢ 𝓝[S] p
  have hP : Tendsto (Prod.snd : ℕ×(ℝ×ℝ) → ℝ×ℝ) l (𝓝 p) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  have hsp := continuous_fst.continuousAt.tendsto.comp hP
  have htp := continuous_snd.continuousAt.tendsto.comp hP
  have h := bfpFree_tendsto_filter (tendsto_fst : Tendsto Prod.fst l atTop) hsp htp u v
  have hc : Continuous F := by
    by_cases hUV : u<v <;> simp only [F,hUV,ite_true,ite_false]
    · unfold heatKernel
      exact continuous_const.mul (by fun_prop)
    · exact continuous_const
  apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
  simpa [F] using (hc.continuousAt.tendsto.comp hP).dist h

end AiryFdd
