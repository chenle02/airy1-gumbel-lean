# airy1-gumbel-lean

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24398888.svg)](https://doi.org/10.5281/zenodo.24398888)

Lean 4 companion to Le Chen and Fei Pu, *Gumbel Fluctuations of the Maximum of the
Airy₁ Process* ([arXiv 2611.23658](https://arxiv.org/abs/2611.23658)): a kernel-checked
proof that the maximum of a constructed Airy₁ process over `[0, T]`, centred and scaled
as in the paper, converges to the Gumbel law, under three named inputs.

## What is proved

The Lean companion proves the normalized Gumbel limit in Theorem 1.1 for a constructed
Airy₁ process with continuous paths on the nonnegative time axis. Its headline theorem
uses the paper's centering and scaling for real observation lengths and assumes three
named inputs: finite-dimensional Airy₁ probability laws, a cubic GOE left-tail bound,
and cubic strong mixing. The mesoscopic step uses a direct two-time Fredholm determinant
estimate and a high-level upcrossing bound, replacing the paper's association and
covariance argument. The verification claim covers this conditional theorem and the
listed component results.

The headline is
[`Airy1Gumbel.gumbel_limit_continuum_real_normalized_airy1_final₂`](Airy1Gumbel/FinalHeadlineTP.lean):

```lean
theorem gumbel_limit_continuum_real_normalized_airy1_final₂ (h : Airy1FddPositive)
    (hT : GOELeftTail) (M : CubicStrongMixing (airy1SRP h hT)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law h).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR h x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z))))
```

Here `airy1Law h` is the law on `ℝ → ℝ` built by Kolmogorov extension from the
finite-dimensional Airy₁ laws, `airy1ContR h` is its version with continuous paths on
`[0, ∞)`, and `gumbelAR`, `gumbelBR` are the centering and scaling of the paper's
equations (1.1)–(1.2) for real `T`. The three hypotheses are Lean structures stated in
[`Airy1Gumbel/FddRecord.lean`](Airy1Gumbel/FddRecord.lean),
[`Airy1Gumbel/GOELeftTail.lean`](Airy1Gumbel/GOELeftTail.lean) and
[`Airy1Gumbel/ExternalInputs.lean`](Airy1Gumbel/ExternalInputs.lean):

| Input | What it asserts | Source |
| --- | --- | --- |
| `Airy1FddPositive` | for every finite set of times, a probability measure whose box distribution function is the Airy₁ Fredholm-determinant formula `AiryFdd.airy1FinCdf` | Quastel–Remenik, Theorem 1; Borodin–Ferrari–Prähofer (2007) |
| `GOELeftTail` | a cubic left-tail bound `F(−M) ≤ C e^{−cM³}` (`M ≥ 0`) for the one-point law | Baik–Buckingham–DiFranco (2008), Section 1.2, with the Ferrari–Spohn GOE identity |
| `CubicStrongMixing` | strong mixing of the process between past and future σ-algebras at rate `exp(−c d³)` in the gap `d` | Chen–Pu, Proposition 3.1 ([arXiv 2607.17113](https://arxiv.org/abs/2607.17113)) |

Proved in Lean on the way, among others: the centering and normalization lemmas; the
block-maxima (blocking) assembly; the sharp one-block tail and the touching and separated
pair bounds from the Quastel–Remenik block laws, which are themselves derived for the
constructed process from a dyadic Brownian hitting theorem; the two-time Fredholm determinant bound and the high-level
upcrossing bound used in the mesoscopic step. The nested package
[`contrib/`](contrib/) holds the analytic infrastructure: the Gumbel law, Airy functions
and their asymptotics, the Mills ratio, Hilbert–Schmidt and trace-class operators,
Fredholm determinants, and the Airy₁ finite-dimensional and two-time estimates. Newman's
covariance inequality (`newman_lemma3`) is also proved; only the earlier association-route
headline uses it.

> [!IMPORTANT]
> **Not proved here.**
> - The three inputs above are assumptions of the headline theorem, not theorems.
>   `GOELeftTail` is an extra explicit input relative to the paper, which starts from an
>   existing continuous Airy₁ process.
> - The paper proves its mesoscopic step through association (Pu 2025), Newman's
>   inequality and the Basu–Busani–Ferrari covariance asymptotic. The Lean proof takes a
>   different route for that step (a two-time Fredholm determinant bound), so it does not
>   check the paper's Proposition 4.3 or Lemmas 4.1–4.2 as stated (arbitrary level `M`
>   and cutoff `R(M)`); only the specialisation used in Section 5.2 is proved.
> - Proposition 1.2 is proved for the constructed process for every `T > 0` (since
>   v0.2.0), under `Airy1FddPositive` and `GOELeftTail`; like the headline, it is
>   conditional on those inputs.
> - Lemma 3.1 is proved for the constructed process for two intervals of any equal
>   length `T > 0` (since v0.3.0), under `Airy1FddPositive` and `GOELeftTail`. What is
>   formalized is the trace-class form (3.3) of Remark 3.2, `det(I − K̃∪)` with the
>   conjugated kernel. The determinant displayed in (3.1) has no separate Lean
>   definition: the paper reads it through (3.3), and that reading is the paper's, not
>   a Lean theorem.
> - Remark 5.3 (the Ferrari–Liu derivation) is not covered.
> - This repository does not certify the whole manuscript: it checks the main theorem
>   along the route described above and the component results listed in
>   [`claims.yaml`](claims.yaml) and [`contrib/claims.yaml`](contrib/claims.yaml).

Since v0.3.0, Lemma 3.1 (the two-interval determinant formula) is proved for the
constructed process for every equal length `T > 0`, under `Airy1FddPositive` and
`GOELeftTail`:
[`Airy1Gumbel.airy1Law_two_blocks_le_eq_fredholmDet_of_length`](Airy1Gumbel/TwoIntervalLaw.lean)
states that, for `T > 0`, `r > 0`, `M > 0`, `x ≥ 0` and any weight `a ≥ 2T + r + 1`,
`ℙ{Ã ≤ M on [x, x+T] and on [x+T+r, x+2T+r]} = det(I − K̃∪)`, where `K̃∪ = U_a K∪ U_a⁻¹`
is the conjugated kernel of (3.2)–(3.3) in Remark 3.2. The paper's case is `x = 0`,
`a = √(2M)`. Versions 0.1.0 and 0.2.0 had this law for two unit intervals only; that
statement is unchanged and is now the case `T = 1`.

Since v0.2.0, Proposition 1.2 (the two-term expansion of the tail of the maximum over a
fixed interval) is proved for the constructed process for every length `T > 0`, under
`Airy1FddPositive` and `GOELeftTail`:
[`Airy1Gumbel.airy1Law_interval_tail_sub_traceLead_isLittleO`](Airy1Gumbel/BlockLawUnconditional.lean)
states that `ℙ{∃ t ∈ [0, T], Ã(t) > M} − (T·ρ(M) + ρ(M)/(4M)) = o(ρ(M)/M)` as `M → ∞`,
where `Ã` is the continuous version `airy1ContR h`. Version 0.1.0 had this expansion for
the Fredholm determinant for every `T > 0`, and for the process only for `T ≥ 1`. See
[`CHANGELOG.md`](CHANGELOG.md).

An earlier headline,
`gumbel_limit_continuum_real_normalized_airy1_final`
([`Airy1Gumbel/FinalHeadline.lean`](Airy1Gumbel/FinalHeadline.lean)), follows the paper's
association route and therefore also assumes the covariance-decay and association
records `CubicCovarianceDecay` and `ProcessAssociated`.

## Paper and references

Le Chen and Fei Pu, *Gumbel Fluctuations of the Maximum of the Airy₁ Process*, preprint,
[arXiv 2611.23658](https://arxiv.org/abs/2611.23658) (2026).

```bibtex
@article{chen.pu:26:gumbel,
  title   = {Gumbel Fluctuations of the Maximum of the {Airy}$_1$ Process},
  author  = {Le Chen and Fei Pu},
  year    = {2026},
  journal = {Preprint arXiv:2611.23658},
  url     = {https://arxiv.org/abs/2611.23658}
}
```

## Build and verify

Pinned toolchain `leanprover/lean4:v4.35.0` ([`lean-toolchain`](lean-toolchain)),
Mathlib at `cfc55fc`, [brownian-motion](https://github.com/RemyDegenne/brownian-motion) at
`61de83c`; the nested package `contrib/` is a Lake path dependency.

```sh
git clone https://github.com/chenle02/airy1-gumbel-lean
cd airy1-gumbel-lean
lake exe cache get          # Mathlib build cache
lake build Airy1Gumbel Airy1GumbelContrib
lake env lean AxiomCheck.lean > transcript.txt
python3 scripts/audit.py transcript.txt
```

`scripts/audit.py` checks that `AxiomCheck.lean` prints axioms for exactly the theorems
declared in `Airy1Gumbel/`, that no proof escape (`sorry`, `admit`, `axiom`, …) occurs,
and that every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
[`verify.sh`](verify.sh) (and [`contrib/verify.sh`](contrib/verify.sh)) run the same
check from a fresh build, with two negative controls, and write the log that a
[lean-pkg](https://github.com/lean-pkg/lean-pkg) receipt binds to one commit.

### Comparator check of the headline

[`Challenge.lean`](Challenge.lean) restates Theorem 1.1 in Mathlib vocabulary, in two forms
(mixing assumed on the continuous version, or on the coordinate process); its objects are
defined, without proofs and from Mathlib only, in
[`ChallengeDefs/Airy1Gumbel/`](ChallengeDefs/Airy1Gumbel): the Airy function, the kernels of
the Quastel-Remenik path integral, the entire Fredholm determinant, the distribution functions
`airy1FinCdf`, the three named inputs and the normalization. The law and the continuous version
are not constructed there: each statement asserts that an Airy₁ law exists, and that for such
laws a version continuous on `[0, ∞)` exists and the Gumbel limit holds for every such version
(in the first form for every law and every continuous version satisfying the mixing input; in
the second for every law whose coordinate process satisfies it). The check verifies the
headline under the three inputs, not the inputs.
[`Solution.lean`](Solution.lean) proves both statements from the package headlines, and
[`comparator.json`](comparator.json) is the configuration the comparator checks (each Solution
theorem has exactly its Challenge type and uses only the three standard axioms):

```sh
lake build ChallengeDefs Challenge Solution
```

### Comparator check of the contrib package

Since v0.3.1 the contrib package has its own comparator configuration,
[`contrib/comparator.json`](contrib/comparator.json): all 103 theorem claims of
[`contrib/claims.yaml`](contrib/claims.yaml), one Challenge theorem
`Airy1GumbelLeanContribAudit.<decl>` each. [`contrib/Comparator/Challenge.lean`](contrib/Comparator/Challenge.lean)
states them (76 as the elaborated types Lean prints, 27 as the declarations' own source
statements) over [`contrib/Comparator/Defs`](contrib/Comparator/Defs), a verbatim copy of the
library that imports Mathlib modules only; [`contrib/Comparator/Solution.lean`](contrib/Comparator/Solution.lean)
proves each by the copied library theorem, and neither file imports the library.
[`contrib/scripts/comparator/CheckFidelity.lean`](contrib/scripts/comparator/CheckFidelity.lean)
checks with `Expr` equality that every copied constant equals the library's and every Challenge
statement equals the claimed declaration's type. From `contrib/`:

```sh
lake build Airy1GumbelContrib Comparator.Challenge Comparator.Solution
lake env lean --run scripts/comparator/CheckFidelity.lean
```

To use the library from another Lake project:

```toml
[[require]]
name = "airy1-gumbel-lean"
git = "https://github.com/chenle02/airy1-gumbel-lean"
rev = "v0.3.1"
```

## Trust and axioms

- No `sorry` and no new axioms: every audited theorem depends only on `propext`,
  `Classical.choice` and `Quot.sound`.
- The headline is conditional. Its hypotheses are the three named structures above; read
  their definitions before relying on the theorem.
- The correspondence between the Lean statements and the paper was checked by AI-assisted
  review, not by an independent human referee.

## Built with lean-pkg

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).

## Authors and AI disclosure

The Lean code is by Le Chen (Auburn University); the mathematics is from the paper by
Le Chen and Fei Pu cited above. AI coding assistants, chiefly Anthropic's Claude, helped
write the code and the documentation. Lean's kernel checked the proofs; Le Chen is
responsible for the statements and their correspondence to the paper.

Licensed under the Apache License 2.0 ([`LICENSE`](LICENSE)); see [`NOTICE.md`](NOTICE.md)
and [`CITATION.cff`](CITATION.cff).

<!-- lean-pkg:page:begin -->
<!-- Generated by `lean-pkg page airy1-gumbel-lean` from coverage.yaml, claims.yaml, the claims ledger and the receipts committed under .lean-receipts/. Do not edit between the markers: change the data and run `lean-pkg page airy1-gumbel-lean --write`. -->

## Verification at a glance

**How to read this page.** Lean has checked every step of the proofs listed here. It cannot check that a Lean statement says what the paper says: that comparison is yours. For each result below, read the paper's statement beside the Lean statement, and check that the hypotheses match.

Theorem 1.1 is proved for a constructed Airy\_1 process with continuous paths under three named inputs, with the mesoscopic step proved by a two-time Fredholm determinant bound instead of the paper's association route; Lemmas 4.1-4.2, Proposition 4.3 and Remark 5.3 are outside.

- Paper: *Gumbel Fluctuations of the Maximum of the Airy\_1 Process*, [arXiv:2611.23658v1](https://arxiv.org/abs/2611.23658v1).
- Results listed: 10. In Lean with the paper's own hypotheses: 0; in Lean with extra hypotheses, named below: 6; not formalized: 4.
- Verified: 1 of the 6 result(s) in Lean.

## The paper's results in Lean

### Theorem 1.1: Gumbel limit of the normalized maximum

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1GumbelAudit.Airy1Gumbel.gumbel_limit_continuum_real_normalized_airy1_final₂` in [Challenge.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem gumbel_limit_continuum_real_normalized_airy1_final₂
    (h : Airy1FddPositive) (hT : GOELeftTail) :
    (∃ μ : Measure (ℝ → ℝ), IsAiry1Law μ) ∧
      ∀ μ : Measure (ℝ → ℝ), IsAiry1Law μ →
        (∃ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y) ∧
          ∀ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y → CubicStrongMixing μ Y →
            ∀ z : ℝ, Tendsto (fun T : ℝ => μ.real {f | ∀ x ∈ Icc (0 : ℝ) T,
              (Y x f - gumbelAR T) / gumbelBR T ≤ z})
              atTop (𝓝 (Real.exp (-Real.exp (-z))))
```

**In Lean.** `Airy1GumbelAudit.Airy1Gumbel.gumbel_limit_continuum_real_normalized_airy1_final₂_coord` in [Challenge.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem gumbel_limit_continuum_real_normalized_airy1_final₂_coord
    (h : Airy1FddPositive) (hT : GOELeftTail) :
    (∃ μ : Measure (ℝ → ℝ), IsAiry1Law μ) ∧
      ∀ μ : Measure (ℝ → ℝ), IsAiry1Law μ → CubicStrongMixing μ (fun x f => f x) →
        (∃ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y) ∧
          ∀ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y →
            ∀ z : ℝ, Tendsto (fun T : ℝ => μ.real {f | ∀ x ∈ Icc (0 : ℝ) T,
              (Y x f - gumbelAR T) / gumbelBR T ≤ z})
              atTop (𝓝 (Real.exp (-Real.exp (-z))))
```

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: Airy1FddPositive: for every finite set of times, a probability law whose box distribution function is the Airy\_1 Fredholm-determinant formula (Quastel-Remenik, Theorem 1; Borodin-Ferrari-Prahofer 2007); GOELeftTail: a cubic left-tail bound for the one-point law (Baik-Buckingham-DiFranco 2008 with the Ferrari-Spohn GOE identity); an input the paper does not need, since it starts from an existing continuous process; CubicStrongMixing: strong mixing between past and future sigma-algebras at rate exp(-c d^3) (Chen-Pu, arXiv 2607.17113, Proposition 3.1).

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** The process is the version of the Kolmogorov-extension law with continuous paths on \[0, infinity); centering and scaling are those of (1.1)-(1.2) for real T. The mesoscopic step is proved by the two-time Fredholm determinant bound and a high-level upcrossing bound, not by association and the covariance asymptotic.

### Proposition 1.2: Two-term expansion of the one-block tail

**Built, not compared.** Lean accepts the proof (the build passed), but its statement has not been compared by a second checker, which lean-pkg needs before it counts the result as verified.

**Internal.** `airy1-gumbel-lean/fixed-interval-tail-expansion`, `airy1-gumbel-lean/interval-hitting-law-positive-length`, `airy1-gumbel-lean/block-law-core`, `airy1-gumbel-lean/block-law-unconditional`, `airy1-gumbel-lean/sharp-tail-discharge`: marked internal in `claims.yaml`, a step of the formalization rather than a result offered for reuse. An internal claim counts as verified only when the statement comparison judged its declaration, on the same evidence as any other result.

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1Gumbel.airy1Law_interval_tail_sub_traceLead_isLittleO` in [Airy1Gumbel/BlockLawUnconditional.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/BlockLawUnconditional.lean).

```lean
theorem airy1Law_interval_tail_sub_traceLead_isLittleO
    (h : Airy1FddPositive) (hLeft : GOELeftTail) (T : ℝ) (hT : 0 < T) :
    (fun M : ℝ => (airy1Law h).real {f | ∃ t ∈ Icc (0 : ℝ) T, M < airy1ContR h t f}
      - AiryConj.traceLead M T) =o[atTop] (fun M => AiryConj.rhoM M / M)
```

**In Lean.** `Airy1Gumbel.airy1Law_sup_le_eq_fredholmDet_at_weight'` in [Airy1Gumbel/BlockLawUnconditional.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/BlockLawUnconditional.lean).

```lean
theorem airy1Law_sup_le_eq_fredholmDet_at_weight' (h : Airy1FddPositive) (hLeft : GOELeftTail)
    {x M T a : ℝ} (hx : 0 ≤ x) (hT : 0 < T) (hM : 0 < M) (ha : T + 1 ≤ a) :
    (airy1Law h).real {f | ∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet (AiryConj.airyTildeOp M T a hT hM ha) 1
```

**In Lean.** `Airy1Gumbel.airy1Law_sup_le_eq_fredholmDet` in [Airy1Gumbel/BlockLaw.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/BlockLaw.lean).

```lean
theorem airy1Law_sup_le_eq_fredholmDet (h : Airy1FddPositive) (hT : GOELeftTail) {x M T : ℝ}
    (hx : 0 ≤ x) (hT1 : 1 ≤ T) (hM : 0 < M) (hK : AiryFdd.MeshHittingLimit M T) :
    (airy1Law h).real {f | ∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1
```

**In Lean.** `Airy1Gumbel.airy1Law_sup_le_eq_fredholmDet'` in [Airy1Gumbel/BlockLawUnconditional.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/BlockLawUnconditional.lean).

```lean
theorem airy1Law_sup_le_eq_fredholmDet' (h : Airy1FddPositive) (hT : GOELeftTail) {x M T : ℝ}
    (hx : 0 ≤ x) (hT1 : 1 ≤ T) (hM : 0 < M) :
    (airy1Law h).real {f | ∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1
```

**In Lean.** `Airy1Gumbel.sharp_tail_of_QRUnitBlockLaw` in [Airy1Gumbel/SharpTail.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/SharpTail.lean).

```lean
theorem sharp_tail_of_QRUnitBlockLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ} (h : QRUnitBlockLaw Y P) :
    Tendsto (fun u : ℝ => P.real {ω | Y 0 ω > u} / Real.exp (-airyH u)) atTop (𝓝 1)
```

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: Airy1FddPositive and GOELeftTail, for the process-level interval hitting law.

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Proved for the continuous version of the constructed process on \[0, T\], for every fixed T &gt; 0 (fixed-interval-tail-expansion). The interval hitting law is proved at any weight a &gt;= T + 1 by the dyadic mesh limit and combined with the determinant expansion of contrib. Version 0.1.0 had the process-level statement for T &gt;= 1 only.

### Corollary 1.3: Touching blocks

**Built, not compared.** Lean accepts the proof (the build passed), but its statement has not been compared by a second checker, which lean-pkg needs before it counts the result as verified.

**Internal.** `airy1-gumbel-lean/touching-discharge`, `airy1-gumbel-lean/qr-block-laws-theorems`: marked internal in `claims.yaml`, a step of the formalization rather than a result offered for reuse. An internal claim counts as verified only when the statement comparison judged its declaration, on the same evidence as any other result.

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1Gumbel.touching_of_QR` in [Airy1Gumbel/Touching.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/Touching.lean).

```lean
theorem touching_of_QR {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
    (qr : QRUnitBlockLaw Y P) (qr₂ : QRTwoBlockLaw Y P) (z : ℝ) :
    Tendsto (fun N : ℕ =>
      (N : ℝ) * P.real {ω | Y 0 ω > gumbelU N z ∧ Y 1 ω > gumbelU N z}) atTop (𝓝 0)
```

**In Lean.** `Airy1Gumbel.qrTwoBlockLaw_airy1` in [Airy1Gumbel/BlockLaw.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/BlockLaw.lean).

```lean
theorem qrTwoBlockLaw_airy1 (h : Airy1FddPositive) (hT : GOELeftTail)
    (hK₂ : ∀ M > 0, AiryFdd.MeshHittingLimit M 2) :
    QRTwoBlockLaw (airy1BlockMax h) (airy1Law h)
```

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: Airy1FddPositive and GOELeftTail, for the one- and two-block laws of the constructed process.

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Proposition 1.4: Separated blocks

**Built, not compared.** Lean accepts the proof (the build passed), but its statement has not been compared by a second checker, which lean-pkg needs before it counts the result as verified.

**Internal.** `airy1-gumbel-lean/separated-discharge`, `airy1-gumbel-lean/qr-two-interval-law-theorem`: marked internal in `claims.yaml`, a step of the formalization rather than a result offered for reuse. An internal claim counts as verified only when the statement comparison judged its declaration, on the same evidence as any other result.

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1Gumbel.separated_of_QR` in [Airy1Gumbel/Separated.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/Separated.lean).

```lean
theorem separated_of_QR {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
    (qr : QRUnitBlockLaw Y P) (two : QRTwoIntervalLaw Y P) :
    ∀ (z χ : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 →
      Tendsto (fun N : ℕ =>
        (N : ℝ) * ∑ j ∈ Finset.Icc 2 (mN χ z N),
          P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0)
```

**In Lean.** `Airy1Gumbel.qrTwoIntervalLaw_airy1` in [Airy1Gumbel/TwoIntervalLaw.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/TwoIntervalLaw.lean).

```lean
theorem qrTwoIntervalLaw_airy1 (h : Airy1FddPositive) (hT : GOELeftTail) :
    QRTwoIntervalLaw (airy1BlockMax h) (airy1Law h) where
  law
```

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: Airy1FddPositive and GOELeftTail, for the unit-block and two-interval laws of the constructed process.

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Lemma 3.1: Two-interval determinant formula

**Built, not compared.** Lean accepts the proof (the build passed), but its statement has not been compared by a second checker, which lean-pkg needs before it counts the result as verified.

**Internal.** `airy1-gumbel-lean/two-interval-law-equal-length`, `airy1-gumbel-lean/two-block-law`, `airy1-gumbel-lean/qr-two-interval-law-theorem`: marked internal in `claims.yaml`, a step of the formalization rather than a result offered for reuse. An internal claim counts as verified only when the statement comparison judged its declaration, on the same evidence as any other result.

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1Gumbel.airy1Law_two_blocks_le_eq_fredholmDet_of_length` in [Airy1Gumbel/TwoIntervalLaw.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/TwoIntervalLaw.lean).

```lean
theorem airy1Law_two_blocks_le_eq_fredholmDet_of_length (h : Airy1FddPositive) (hLeft : GOELeftTail)
    {x M T r a : ℝ} (hx : 0 ≤ x) (hT : 0 < T) (hr : 0 < r)
    (hM : 0 < M) (ha : 2 * T + r + 1 ≤ a) :
    (airy1Law h).real {f | (∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M) ∧
        ∀ t ∈ Icc (x + T + r) (x + T + r + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (HilbertSchmidt.kernelOperator (AiryFdd.memLp_kcupKerT_of_length hT hr hM ha)) 1
```

**In Lean.** `Airy1Gumbel.airy1Law_two_blocks_le_eq_fredholmDet` in [Airy1Gumbel/TwoIntervalLaw.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/TwoIntervalLaw.lean).

```lean
theorem airy1Law_two_blocks_le_eq_fredholmDet (h : Airy1FddPositive) (hT : GOELeftTail)
    {x M r a : ℝ} (hx : 0 ≤ x) (hr : 0 < r) (hM : 0 < M) (ha : r + 3 ≤ a) :
    (airy1Law h).real {f | (∀ t ∈ Icc x (x + 1), airy1ContR h t f ≤ M) ∧
        ∀ t ∈ Icc (x + 1 + r) (x + 1 + r + 1), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (HilbertSchmidt.kernelOperator (AiryTwoInt.memLp_kcupKerT hr hM ha)) 1
```

**In Lean.** `Airy1Gumbel.qrTwoIntervalLaw_airy1` in [Airy1Gumbel/TwoIntervalLaw.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/TwoIntervalLaw.lean).

```lean
theorem qrTwoIntervalLaw_airy1 (h : Airy1FddPositive) (hT : GOELeftTail) :
    QRTwoIntervalLaw (airy1BlockMax h) (airy1Law h) where
  law
```

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: Airy1FddPositive and GOELeftTail, for the two-interval hitting law of the constructed process.

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Proved for every T &gt; 0, r &gt; 0, M &gt; 0 at any weight a &gt;= 2T + r + 1 (two-interval-law-equal-length), in the trace-class form (3.3) of Remark 3.2: det(I - K\~), K\~ the conjugated kernel of (3.2). The determinant displayed in (3.1) has no separate Lean definition; the paper reads it through (3.3). Versions 0.1.0 and 0.2.0 had T = 1 only.

### Lemmas 5.1-5.2: Centering, normalization and the blocking assembly of Section 5.2

**Built, not compared.** Lean accepts the proof (the build passed), but its statement has not been compared by a second checker, which lean-pkg needs before it counts the result as verified.

**Internal.** `airy1-gumbel-lean/normalization-centering`, `airy1-gumbel-lean/normalization-scaling`, `airy1-gumbel-lean/decouple-discharge`, `airy1-gumbel-lean/gumbel-limit-conditional`, `airy1-gumbel-lean/mesoscopic-of-bounds-tp`: marked internal in `claims.yaml`, a step of the formalization rather than a result offered for reuse. An internal claim counts as verified only when the statement comparison judged its declaration, on the same evidence as any other result.

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1Gumbel.airyH_gumbelA` in [Airy1Gumbel/Normalization.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/Normalization.lean).

```lean
theorem airyH_gumbelA :
    Tendsto (fun N : ℕ => airyH (gumbelA N) - Real.log N) atTop (𝓝 0)
```

**In Lean.** `Airy1Gumbel.gumbel_normalization` in [Airy1Gumbel/Normalization.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/Normalization.lean).

```lean
theorem gumbel_normalization (z : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-airyH (gumbelU N z)))
      atTop (𝓝 (Real.exp (-z)))
```

**In Lean.** `Airy1Gumbel.decouple_of_CubicStrongMixing` in [Airy1Gumbel/MixingRecord.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/MixingRecord.lean).

```lean
theorem decouple_of_CubicStrongMixing (M : CubicStrongMixing X) (C : Airy1ContinuousMax P)
    (hA : X.A = C.A) :
    ∀ (S T : Finset ℕ) (q : ℕ) (u : ℝ),
      (∀ s ∈ S, ∀ t ∈ T, s + q ≤ t) →
      |P.real ({ω | ∀ s ∈ S, C.Y s ω ≤ u} ∩ {ω | ∀ t ∈ T, C.Y t ω ≤ u}) -
        P.real {ω | ∀ s ∈ S, C.Y s ω ≤ u} * P.real {ω | ∀ t ∈ T, C.Y t ω ≤ u}|
        ≤ M.alphaY q
```

**In Lean.** `Airy1Gumbel.Airy1BlockExtremes.gumbel_limit` in [Airy1Gumbel/GumbelLimit.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/GumbelLimit.lean).

```lean
theorem Airy1BlockExtremes.gumbel_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : Airy1BlockExtremes P) (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ j ∈ Finset.range N, D.Y j ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z))))
```

**In Lean.** `Airy1Gumbel.mesoscopic_of_boundsTP` in [Airy1Gumbel/MesoscopicTP.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/962a984bcc363fd6e9f13dc3303e00be5d668f3d/Airy1Gumbel/MesoscopicTP.lean).

```lean
theorem mesoscopic_of_boundsTP {Y : ℕ → Ω → ℝ} {W : ℝ → Ω → ℝ}
    (b : MesoscopicBoundsTP P Y W) :
    ∀ (z χ : ℝ) (A : ℝ), (1 / 2) ^ ((1 : ℝ) / 3) < χ → χ < 1 → 0 < A →
      Tendsto (fun N : ℕ =>
        (N : ℝ) * ∑ j ∈ Finset.Icc (mN χ z N + 1) (qN A N),
          P.real {ω | Y 0 ω > gumbelU N z ∧ Y j ω > gumbelU N z}) atTop (𝓝 0)
```

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: CubicStrongMixing, for the decoupling of distant blocks.

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

## Not formalized

- Lemma 4.1 (Block modulus): The Lean proof does not use this lemma: its mesoscopic step goes through a high-level upcrossing bound.
- Lemma 4.2 (Pair bound under association): The Lean proof does not use association; it bounds grid pairs by a two-time Fredholm determinant estimate. Newman's covariance inequality itself is proved (newman-lemma3).
- Proposition 4.3 (Mesoscopic sum): The general statement (arbitrary level M and cutoff R(M)) is not formalized; the specialisation used in Section 5.2 is proved along the two-point route (mesoscopic-of-bounds-tp).
- Remark 5.3 (Persistence derivation): The separate Ferrari-Liu derivation is not part of the Lean proof.

## What the checks establish

- **Every proof is checked by Lean.** The package builds; no `sorry` (an unfinished proof) remains; the only axioms used are `Classical.choice`, `Quot.sound`, `propext` (allowed: `propext`, `Quot.sound`, `Classical.choice`).
- **The statements shown are the ones proved.** For 2 statement(s), a second checker (comparator) confirmed that the proof proves exactly the statement shown, with only the permitted axioms, and independent Lean kernels replayed the proof.
- **Not checked by any tool:** that a Lean statement says what the paper says. That is the comparison this page asks you to make. A definition listed under *Definitions checked by a person* is compared by name and type only.

The full account of what each check covers and what it takes on trust is lean-pkg's [trust model](https://github.com/lean-pkg/lean-pkg/blob/main/docs/trust-model.md).

## How this was checked

- lean-pkg's claims ledger: **ready**, every required claim is closed by the recorded receipts; 2 of 2 required claim(s) verified (`sha256:71e1549a7f42d820…`).
- Build check (`lean-pkg gate`) at commit `962a984bcc36`: `sorry` count 0; axioms used: `Classical.choice`, `Quot.sound`, `propext`.
- Axioms of every claim: read from the built environment (Lean's `collectAxioms`) for all 56 claim(s) in `claims.yaml`, not only the theorems the build prints; none uses an axiom beyond `propext`, `Quot.sound` and `Classical.choice`.
- Statement comparison (comparator) at commit `962a984bcc36`: 1 configuration(s), 2 theorem(s) compared (each Challenge statement against its Solution proof); permitted axioms: `Classical.choice`, `Quot.sound`, `propext`; definitions compared by name only: none.

### Receipts

| Receipt | Check | Commit | Date | Job | SHA-256 |
|---|---|---|---|---|---|
| `.lean-receipts/19901ea8b3fe-systemd-user-airy1-gumbel-lean-verify.service-0ebf95d044bb440482efe94120401c18-h-f985343177f7.json` | build | `19901ea8b3fe` | 2026-11-20 | — | `1a6c1ec5f03436f64683563735165e027679053e90a2a5bb3a74822eee8dc9c1` |
| `.lean-receipts/66ac891274b1-comparator.json` | statement comparison | `66ac891274b1` | 2026-11-20 | — | `abbb43a25d904bf50477fa50d267124fef4060f81a8ed0a52dbf57a4fe9da459` |
| `.lean-receipts/66ac891274b1-systemd-user-airy1-v020-main-verify.service-37bfacd30061492d8a7d92f9d1677d7e-h-f985343177f7.json` | build | `66ac891274b1` | 2026-11-20 | — | `423df7f9a678774ad470a0c55c740300cc849185a82f4d38d81e842909c82a35` |
| `.lean-receipts/962a984bcc36-comparator.json` (used here) | statement comparison | `962a984bcc36` | 2026-11-20 | — | `84b03ae346317b204f921def1b546e9fa621b35aae433cc6af96926e82f5d72b` |
| `.lean-receipts/962a984bcc36-systemd-user-airy1-v031-main-verify.service-58730a798b4d4c3988e32f986ef518ae-h-f985343177f7.json` (used here) | build | `962a984bcc36` | 2026-11-20 | — | `8bf0409b4c3da4429ecce5e8fa25ca1b0580a0f1586a7265f2b6ebb62b583cf7` |
| `.lean-receipts/a1bff15de04d-comparator.json` | statement comparison | `a1bff15de04d` | 2026-11-20 | — | `b72c743b1c1c684a7c9c8361e54a124708ac49549d129fa5ba465709543de5d0` |
| `.lean-receipts/a1bff15de04d-systemd-user-airy1-gumbel-lean-verify.service-c2a663d5bb35493f8c24c9e801073dac-h-f985343177f7.json` | build | `a1bff15de04d` | 2026-11-20 | — | `a635d001a22e7a74a45a8cdecf972122d61c938810deb6d0247ef99e740d5497` |
| `.lean-receipts/b098667dfbf3-comparator.json` | statement comparison | `b098667dfbf3` | 2026-11-20 | — | `0f0556b5cac93393f4f9ff7871c52c201e9a79ed1095305c7569e5ca92e7e45b` |
| `.lean-receipts/b098667dfbf3-systemd-user-airy1-v030-main-verify.service-b10c1e8c2d7745c299491cb3d15d6e51-h-f985343177f7.json` | build | `b098667dfbf3` | 2026-11-20 | — | `a313cce2332f72081bb38774cc6229dacddc13ed8e41256ca1a4412715566fd3` |
| `.lean-receipts/e91b7889be06-comparator.json` | statement comparison | `e91b7889be06` | 2026-11-20 | — | `1848f9de577e72defb797ae8e3990e73b084fd9622963621b5e1e3eac235dbcf` |
| `.lean-receipts/e91b7889be06-systemd-user-airy1-gumbel-lean-verify.service-a651ab0e9f964e2bae2aa65c51ee6345-h-f985343177f7.json` | build | `e91b7889be06` | 2026-11-20 | — | `c7b3e3a6feecfecf73d6706dbef25abf7f8ff1cab8474c035776c5d0265fa239` |

*(used here)*: the receipt the lean-pkg registry holds for this package, which the lines above read. SHA-256 is of the file as committed.

### Reproduce

- Lean toolchain: `leanprover/lean4:v4.35.0`.
- Mathlib: `cfc55fc58714a59dc06e6e79edc6d1d95140d3c2` (lake-manifest.json).

```bash
git clone https://github.com/chenle02/airy1-gumbel-lean
cd airy1-gumbel-lean
git checkout 962a984bcc363fd6e9f13dc3303e00be5d668f3d   # the commit the build check binds
lake exe cache get
lake build
```

Expected: `#print axioms` on any declaration above reports a subset of {`Classical.choice`, `Quot.sound`, `propext`} (the union the build check records); `sorryAx` never appears.

## Citation

Le Chen. *airy1-gumbel-lean: Lean companion to Gumbel fluctuations of the maximum of the Airy\_1 process*. Version 0.3.1. [doi:10.5281/zenodo.24398888](https://doi.org/10.5281/zenodo.24398888).

It formalizes results of *Gumbel Fluctuations of the Maximum of the Airy\_1 Process*, [arXiv:2611.23658v1](https://arxiv.org/abs/2611.23658v1). See [CITATION.cff](CITATION.cff).

## License

Released under `Apache-2.0`; see [LICENSE](LICENSE).

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).

<!-- lean-pkg:page:end -->
