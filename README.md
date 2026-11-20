# airy1-gumbel-lean

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
> - Proposition 1.2 is proved for the determinant for every `T > 0`, but at the level of
>   the process only for `T ≥ 1`. Lemma 3.1 is proved for two unit intervals, not for
>   general equal lengths. Remark 5.3 (the Ferrari–Liu derivation) is not covered.
> - This repository does not certify the whole manuscript: it checks the main theorem
>   along the route described above and the component results listed in
>   [`claims.yaml`](claims.yaml) and [`contrib/claims.yaml`](contrib/claims.yaml).

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

To use the library from another Lake project:

```toml
[[require]]
name = "airy1-gumbel-lean"
git = "https://github.com/chenle02/airy1-gumbel-lean"
rev = "v0.1.0"
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
