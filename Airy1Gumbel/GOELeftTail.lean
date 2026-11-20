/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1Gumbel.TruncatedMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Airy1Gumbel

/-!
# The GOE left tail — external-input record `GOELeftTail`

The lower boundedness of the Airy₁ paths needs a quantitative left tail of the one-point law, `P(A₁(0) ≤ −M) ≤ C e^{−cM³}`. Nothing in
Lean proves it: the one-point function `airy1FinCdf {0}` is Ferrari–Spohn's GOE determinant
`det(I − B_{2x})_{L²(0,∞)}` (contrib `airy1FinCdf_singleton_eq_fsGOE`), and the left tail of
`F_GOE` is a Painlevé II asymptotic (Tracy–Widom; Baik–Buckingham–DiFranco). This module
records it as an **external-input record** (`GOELeftTail`) and proves what follows from it:

* the schema `HasCubicLeftTail F` and `goeLeftTail_iff` (the record is the schema at
  `F = x ↦ airy1FinCdf {0} (fun _ => x)`);
* the bound at every time (`GOELeftTail.tail_at`, stationarity of the one-point function,
  `airy1FinCdf_singleton_eq`), and the law form under `airy1Law h`
  (`GOELeftTail.airy1Law_le`, `GOELeftTail.airy1Law_le_ofReal`), constants uniform in `t`.

Vacuity and falsity checks:

* Schema sanity: a function with a positive limit at `−∞` has no cubic left tail
  (`not_hasCubicLeftTail_of_tendsto`); in particular the constant `1`
  (`not_hasCubicLeftTail_const_one`).
* Falsity witness (a corrupted variant, refuted unconditionally): the reflected function
  `x ↦ airy1FinCdf {0} (fun _ => −x)` has no cubic left tail
  (`not_hasCubicLeftTail_airy1FinCdf_reflect`), since it tends to `1` at `−∞` (contrib
  `tendsto_airy1FinCdf_one`). So the record depends on the orientation of `airy1FinCdf`.
* Consistency with what is proved: under `Airy1FddPositive`, `airy1FinCdf {0} (−M) ∈ [0, 1]`
  and `→ 0` as `M → ∞` (`goeLeftTail_consistent`); and the record is then **equivalent** to its
  eventual (asymptotic) form (`goeLeftTail_iff_eventually`), which is the form BBD state.

It is the hypothesis `hT` of the headlines on the concrete process, including `_final₂`: the
lower-boundedness argument (`LowerBound.lean`) uses it to build the real-valued continuous version.
-/

/-- The schema of a cubic left tail for a function `F : ℝ → ℝ` (a would-be one-dimensional
distribution function): `F(−M) ≤ C e^{−cM³}` for all `M ≥ 0`, with `C, c > 0`.
`GOELeftTail` is this schema at `F = x ↦ airy1FinCdf {0} (fun _ => x)` (`goeLeftTail_iff`);
the schema form is what the falsity witnesses below refute for corrupted `F`. -/
def HasCubicLeftTail (F : ℝ → ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ M : ℝ, 0 ≤ M → F (-M) ≤ C * Real.exp (-c * M ^ 3)

/-- **External-input record: the GOE left tail of the Airy₁ one-point function.**
There are `C, c > 0` with `airy1FinCdf {0} (fun _ => −M) ≤ C e^{−cM³}` for every `M ≥ 0`;
in probabilistic terms `P(A₁(0) ≤ −M) = F_GOE(−2M) ≤ C e^{−cM³}`.

*Provenance (justified by, not literally stated in, the sources).* Two citations are needed.
(1) **Baik–Buckingham–DiFranco 2008** (Comm. Math. Phys. 280 (2008), 463–497, MR2395479,
arXiv:0704.3636), the left-tail asymptotic in their Section 1.2, together with the
corollary computing `τ₁`: as `x → −∞`,
`F₁(x) = τ₁ |x|^{−1/16} e^{−|x|³/24 − |x|^{3/2}/(3√2)} (1 − 1/(24√2 |x|^{3/2}) + O(|x|^{−3}))`,
`τ₁ = 2^{−11/48} e^{ζ'(−1)/2}`, for the Painlevé II form `F₁ = F·E` of Tracy–Widom.
BBD derive this asymptotic from the Tracy–Widom formula and the Hastings–McLeod asymptotic
(Hastings–McLeod 1980, Deift–Zhou 1995); the leading exponent `−|x|³/24` is Tracy–Widom's.
BBD state only the asymptotic, with no explicit threshold: with `F₁ ≤ 1` on `[−s₀, 0]` it gives
`F₁(x) ≤ C e^{−|x|³/24}` for all `x ≤ 0` with an existential `C`; this two-line step is not in
the source, hence "justified by". (2) **Ferrari–Spohn 2005** (J. Phys. A 38, L557;
arXiv:math-ph/0505012): `F₁(s) = det(I − B_s)_{L²(0,∞)}`, `B_s(a,b) = Ai(a + b + s)`; BBD
never state a determinant form for `F₁`. In Lean, `airy1FinCdf {t} x = det(I − B_{2x})` is
proved (contrib `AiryFdd.airy1FinCdf_singleton_eq_fsGOE`); `F₁ = det(I − B_s)` stays cited,
exactly as in `Airy1FddPositive`.

*Convention check.* `airy1FinCdf {0} (fun _ => m)` is `F_GOE(2m)` (QR normalization). At
`x = −2M`, `|x|³/24 = M³/3`, so the source gives `c = 1/3`; this matches Quastel–Remenik
([QuastelRemenik2013], in the proof of their truncation lemma): "`P(A₁(0) < −M) = F_GOE(−2M) ≤
c e^{−M³/3}` … by the results of [BBD]". The record keeps `c` existential (the narrowest form that
the lower-boundedness argument needs; it survives any constant mismatch).

*Scope.* A statement about the defined function `airy1FinCdf` alone: no process, no law, and
not `Airy1FddPositive` is needed to state it. Bound to the concrete `airy1FinCdf` (contrib's
entire `fredholmDet`, no junk branch), with no data field. Vacuity and falsity checks: the refutations
(`not_hasCubicLeftTail_const_one`, `not_hasCubicLeftTail_airy1FinCdf_reflect`) are proved, and
the record is consistent with `Airy1FddPositive` (`goeLeftTail_consistent`, `goeLeftTail_iff_eventually`). -/
structure GOELeftTail : Prop where
  tail : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ M : ℝ, 0 ≤ M →
    AiryFdd.airy1FinCdf {0} (fun _ => -M) ≤ C * Real.exp (-c * M ^ 3)

/-- The record is the cubic-left-tail schema at the one-point function `airy1FinCdf {0}`. -/
theorem goeLeftTail_iff :
    GOELeftTail ↔ HasCubicLeftTail (fun x => AiryFdd.airy1FinCdf {0} (fun _ => x)) :=
  ⟨fun h => h.tail, fun h => ⟨h⟩⟩

/-! ## The cubic envelope and the generic refutation -/

/-- The envelope `C e^{−cM³}` tends to `0` as `M → ∞` (`c > 0`). -/
theorem tendsto_cubicEnvelope (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun M : ℝ => C * Real.exp (-c * M ^ 3)) atTop (𝓝 0) := by
  have h3 : Tendsto (fun M : ℝ => M ^ 3) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h := (Real.tendsto_exp_atBot.comp
    (h3.const_mul_atTop_of_neg (neg_lt_zero.2 hc))).const_mul C
  simpa [Function.comp_def] using h

/-- A function with a positive limit at `−∞` has no cubic left tail. -/
theorem not_hasCubicLeftTail_of_tendsto {F : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hF : Tendsto (fun M => F (-M)) atTop (𝓝 a)) : ¬ HasCubicLeftTail F := by
  rintro ⟨C, c, _, hc, hb⟩
  have hle : a ≤ 0 := le_of_tendsto_of_tendsto hF (tendsto_cubicEnvelope C hc)
    (eventually_atTop.2 ⟨0, fun M hM => hb M hM⟩)
  linarith

/-- Any function with a cubic left tail and nonnegative values tends to `0` at `−∞`. -/
theorem HasCubicLeftTail.tendsto_zero {F : ℝ → ℝ} (hF : HasCubicLeftTail F)
    (h0 : ∀ x, 0 ≤ F x) : Tendsto (fun M => F (-M)) atTop (𝓝 0) := by
  obtain ⟨C, c, _, hc, hb⟩ := hF
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_cubicEnvelope C hc) (Eventually.of_forall fun M => h0 _)
    (eventually_atTop.2 ⟨0, fun M hM => hb M hM⟩)

/-! ## Falsity witnesses -/

/-- **Schema sanity.** The constant `1` (the CDF of "mass at `−∞`") has no cubic left
tail: the schema is not satisfiable by an arbitrary bounded function. -/
theorem not_hasCubicLeftTail_const_one : ¬ HasCubicLeftTail (fun _ => (1 : ℝ)) :=
  not_hasCubicLeftTail_of_tendsto one_pos tendsto_const_nhds

/-- **Falsity witness ( corrupted variant refuted in Lean, unconditionally).** The record
with `airy1FinCdf {0}` replaced by its reflection `x ↦ airy1FinCdf {0} (fun _ => −x)` is
false: the reflection at `−M` is `airy1FinCdf {0} (fun _ => M) → 1` (contrib
`tendsto_airy1FinCdf_one`), while the envelope tends to `0`. So the record's content depends on
the orientation of `airy1FinCdf`; no `Airy1FddPositive` is used. -/
theorem not_hasCubicLeftTail_airy1FinCdf_reflect :
    ¬ HasCubicLeftTail (fun x => AiryFdd.airy1FinCdf {0} (fun _ => -x)) := by
  refine not_hasCubicLeftTail_of_tendsto one_pos ?_
  simp only [neg_neg]
  exact AiryFdd.tendsto_airy1FinCdf_one {0} (xn := fun M _ => M) (fun _ => tendsto_id)

/-! ## Consistency with what is proved (non-vacuity) -/

/-- **Consistency.** Under `Airy1FddPositive`, the record's left-hand side is a probability
that tends to `0` as `M → ∞`; so the record's conclusion is compatible with every proved fact
about `airy1FinCdf {0}` (it asserts only the *rate* of a proved convergence). -/
theorem goeLeftTail_consistent (h : Airy1FddPositive) :
    (∀ M : ℝ, AiryFdd.airy1FinCdf {0} (fun _ => -M) ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun M : ℝ => AiryFdd.airy1FinCdf {0} (fun _ => -M)) atTop (𝓝 0) :=
  ⟨fun _ => ⟨h.airy1FinCdf_nonneg _ _, h.airy1FinCdf_le_one _ _⟩,
    h.tendsto_airy1FinCdf_zero {0} ⟨0, Finset.mem_singleton_self 0⟩ (xn := fun M _ => -M)
      tendsto_neg_atTop_atBot⟩

/-- **Reduction to the source's asymptotic form.** Under `Airy1FddPositive` (so
`airy1FinCdf ≤ 1`), the record is equivalent to the bound holding *eventually* in `M`, which
is the form in which BBD state it; the bounded range is absorbed into `C`. -/
theorem goeLeftTail_iff_eventually (h : Airy1FddPositive) :
    GOELeftTail ↔ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ M in atTop,
      AiryFdd.airy1FinCdf {0} (fun _ => -M) ≤ C * Real.exp (-c * M ^ 3) := by
  constructor
  · rintro ⟨C, c, hC, hc, hb⟩
    exact ⟨C, c, hC, hc, eventually_atTop.2 ⟨0, fun M hM => hb M hM⟩⟩
  · rintro ⟨C, c, hC, hc, hev⟩
    obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 hev
    refine ⟨⟨max C (Real.exp (c * max M₁ 0 ^ 3)), c, lt_max_of_lt_left hC, hc,
      fun M hM => ?_⟩⟩
    have hE : 0 < Real.exp (-c * M ^ 3) := Real.exp_pos _
    rcases le_total (max M₁ 0) M with hMM | hMM
    · calc AiryFdd.airy1FinCdf {0} (fun _ => -M) ≤ C * Real.exp (-c * M ^ 3) :=
            hM₁ M ((le_max_left _ _).trans hMM)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le
    · have hpow : M ^ 3 ≤ max M₁ 0 ^ 3 := pow_le_pow_left₀ hM hMM 3
      have h1 : 1 ≤ Real.exp (c * max M₁ 0 ^ 3) * Real.exp (-c * M ^ 3) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      calc AiryFdd.airy1FinCdf {0} (fun _ => -M) ≤ 1 := h.airy1FinCdf_le_one _ _
        _ ≤ Real.exp (c * max M₁ 0 ^ 3) * Real.exp (-c * M ^ 3) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hE.le

/-! ## Derived forms for the lower-boundedness argument -/

/-- **The bound at every time**, constants uniform in `t` (the one-point function does not
depend on the time, `airy1FinCdf_singleton_eq`). -/
theorem GOELeftTail.tail_at (hT : GOELeftTail) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t M : ℝ, 0 ≤ M →
      AiryFdd.airy1FinCdf {t} (fun _ => -M) ≤ C * Real.exp (-c * M ^ 3) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hT.tail
  exact ⟨C, c, hC, hc, fun t M hM => (airy1FinCdf_singleton_eq t 0 (-M)).le.trans (hb M hM)⟩

/-- One-point lower probability under the Airy₁ law: `P(f t ≤ m) = airy1FinCdf {0} (m)`. -/
theorem airy1Law_le_eq (h : Airy1FddPositive) (t m : ℝ) :
    (airy1Law h).real {f : ℝ → ℝ | f t ≤ m} = AiryFdd.airy1FinCdf {0} (fun _ => m) := by
  have hset : {f : ℝ → ℝ | f t ≤ m}
      = {f : ℝ → ℝ | ∀ s ∈ ({t} : Finset ℝ), f s ≤ (fun _ => m) s} := by
    ext f; simp
  have hF : (airy1Law h).real {f : ℝ → ℝ | ∀ s ∈ ({t} : Finset ℝ), f s ≤ (fun _ => m) s}
      = AiryFdd.airy1FinCdf {t} (fun _ => m) := airy1Law_fdd h {t} _
  rw [hset, hF, airy1FinCdf_singleton_eq t 0 m]

/-- **Law form.** Under `Airy1FddPositive` and the record,
`P(f t ≤ −M) ≤ C e^{−cM³}` for every time `t` and `M ≥ 0`, constants uniform in `t`. -/
theorem GOELeftTail.airy1Law_le (hT : GOELeftTail) (h : Airy1FddPositive) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t M : ℝ, 0 ≤ M →
      (airy1Law h).real {f : ℝ → ℝ | f t ≤ -M} ≤ C * Real.exp (-c * M ^ 3) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hT.tail
  exact ⟨C, c, hC, hc, fun t M hM => (airy1Law_le_eq h t (-M)).le.trans (hb M hM)⟩

/-- **Law form, measure version** (for union bounds in `ℝ≥0∞`). -/
theorem GOELeftTail.airy1Law_le_ofReal (hT : GOELeftTail) (h : Airy1FddPositive) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t M : ℝ, 0 ≤ M →
      airy1Law h {f : ℝ → ℝ | f t ≤ -M} ≤ ENNReal.ofReal (C * Real.exp (-c * M ^ 3)) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hT.airy1Law_le h
  refine ⟨C, c, hC, hc, fun t M hM => ?_⟩
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (hb t M hM)

end Airy1Gumbel
