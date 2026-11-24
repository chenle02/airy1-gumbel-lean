# airy1-gumbel-lean

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24398888.svg)](https://doi.org/10.5281/zenodo.24398888)

Lean 4 companion to Le Chen and Fei Pu, *Gumbel Fluctuations of the Maximum of the
Airy₁ Process* ([arXiv 2611.23658](https://arxiv.org/abs/2611.23658)): a kernel-checked
proof that the maximum of a constructed Airy₁ process over `[0, T]`, centred and scaled
as in the paper, converges to the Gumbel law, under three named inputs. Since v0.9.0 the
first input, `Airy1FddPositive`, is proved under the second, `GOELeftTail`, so the same
limit also holds under two named inputs (`GOELeftTail` and `CubicStrongMixing`).

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
covariance inequality (`newman_lemma3`) is also proved; the headline does not use it, and
the earlier association-route headline, Lemma 4.2 (since v0.5.0) and Proposition 4.3
(since v0.6.0) do.

> [!IMPORTANT]
> **Not proved here.**
> - The three inputs above are assumptions of the headline theorem, not theorems.
>   `GOELeftTail` is an extra explicit input relative to the paper, which starts from an
>   existing continuous Airy₁ process. Since v0.9.0 the first input, `Airy1FddPositive`,
>   is proved under the second (`airy1FddPositive_of_goeLeftTail`), not unconditionally;
>   `_final₂_no_fdd_input` has the headline's conclusion under `GOELeftTail` and
>   `CubicStrongMixing` only, and those two remain assumptions.
> - The paper proves its mesoscopic step through association (Pu 2025), Newman's
>   inequality and the Basu–Busani–Ferrari covariance asymptotic. The headline's Lean
>   proof takes a different route for that step (a two-time Fredholm determinant bound)
>   and uses only the specialisation of Proposition 4.3 needed in Section 5.2, which it
>   proves along that route. Proposition 4.3 as stated (eq. (4.6), every
>   `χ ∈ ((1/2)^{1/3}, 1)` and every cutoff `R(M) = O(√M)`) is proved separately (since
>   v0.6.0), along the paper's route, under the standing inputs `Airy1FddPositive` and
>   `GOELeftTail` and three named inputs, each assumed, not proved, here:
>   `NonnegativeWindowModulusEstimate`, `ProcessAssociated` and `CubicCovarianceDecay`.
>   The headline `_final₂` uses none of these three.
> - Lemma 4.2 (the threshold-sensitive Newman bound, eq. (4.3)) is proved for the
>   constructed process (since v0.5.0) under the standing inputs `Airy1FddPositive` and
>   `GOELeftTail` and the association input `ProcessAssociated`: the association of the
>   Airy₁ process (Pu 2025, Theorem 1.2), which is assumed, not proved, here. The headline
>   `_final₂` still uses exactly its three inputs and does not use `ProcessAssociated`.
> - Lemma 4.1 (the block modulus, eq. (4.1)) is proved for the constructed process
>   (since v0.4.0) under `Airy1FddPositive`, `GOELeftTail` and a fourth named input,
>   `NonnegativeWindowModulusEstimate`: the transferred local oscillation bound (4.2) of
>   arXiv:2611.23658v1 on windows inside `[0, ∞)`, which the paper derives from
>   Basu–Bhattacharjee (2024) and which is assumed, not proved, here. The headline
>   `_final₂` still uses exactly its three inputs and does not use the new one.
> - Proposition 1.2 is proved for the constructed process for every `T > 0` (since
>   v0.2.0), under `Airy1FddPositive` and `GOELeftTail`; like the headline, it is
>   conditional on those inputs.
> - Lemma 3.1 is proved for the constructed process for two intervals of any equal
>   length `T > 0` (since v0.3.0), under `Airy1FddPositive` and `GOELeftTail`. What is
>   formalized is the trace-class form (3.3) of Remark 3.2, `det(I − K̃∪)` with the
>   conjugated kernel. The determinant displayed in (3.1) has no separate Lean
>   definition: the paper reads it through (3.3), and that reading is the paper's, not
>   a Lean theorem.
> - Remark 5.3 (the Gumbel limit derived from the Ferrari–Liu persistence estimates) is
>   proved for the constructed process (since v0.8.0), along integer lengths as the remark
>   states, under the standing inputs `Airy1FddPositive` and `GOELeftTail` and a new named
>   input, `FerrariLiuPersistence`: the finite-length persistence expansion of Ferrari–Liu
>   (2024), which is assumed, not proved, here and is used only by Remark 5.3. The headline
>   `_final₂` does not use it.
> - `Airy1FddPositive` is proved under `GOELeftTail` (since v0.9.0), not
>   unconditionally. The original theorems, the headline `_final₂` and the statements the
>   comparator checks among them, still take it as a hypothesis, unchanged; the
>   `_no_fdd_input` forms do not take it. Since v0.9.0 the comparator also checks
>   `airy1FddPositive_of_goeLeftTail` and `_final₂_no_fdd_input`; the other
>   `_no_fdd_input` forms are built, not compared.
> - Lemmas 3.3–3.8 (the intermediate lemmas of the paper's proof of Proposition 1.4) are
>   proved in the contrib package, 3.6 and 3.7 as stated, 3.3, 3.4 and 3.5 in a different
>   form and 3.8 in a weaker form (Hilbert–Schmidt norms, not trace norms). Lemmas
>   B.1–B.6 of Appendix B are proved in the contrib library as stated (B.4 and B.6 on a
>   larger parameter range), with no named input. All twelve are shown as outside in
>   `coverage.yaml` only because its rows can name main-package claims alone; each row
>   gives the declarations.
> - This repository does not certify the whole manuscript: it checks the main theorem
>   along the route described above and the component results listed in
>   [`claims.yaml`](claims.yaml) and [`contrib/claims.yaml`](contrib/claims.yaml).

Since v0.9.0, `Airy1FddPositive` is proved under `GOELeftTail`, and the headline holds
under two named inputs.
[`Airy1Gumbel.airy1FddPositive_of_goeLeftTail`](Airy1Gumbel/FddFromTasep.lean)
`(hT : GOELeftTail) : Airy1FddPositive` constructs, for every finite set of times, a
probability law whose box distribution function is `AiryFdd.airy1FinCdf`: the nested package
formalizes flat discrete TASEP (sequential update) and its finite-window law, writes its
gap probabilities as Fredholm series of the Borodin–Ferrari–Prähofer kernel, and proves that
the rescaled distribution functions converge to the extended Airy₁ determinants
(`AiryFdd.tendsto_flatTasepCdf_extendedSeries`,
`AiryFdd.airyExtendedSeries_eq_airy1FinCdf`, in
[`contrib/Airy1GumbelContrib/FddMeasure/`](contrib/Airy1GumbelContrib/FddMeasure)). The
limits inherit nonnegativity, monotonicity and nonnegative rectangle increments, and the
v0.8.0 reduction `airy1FddPositive_of_rectangle` turns them into the measures, with
`GOELeftTail` for the behaviour at `−∞`. It is proved under `GOELeftTail`, not
unconditionally. The new headline is
[`Airy1Gumbel.gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_input`](Airy1Gumbel/FddFromTasepCorollaries.lean):

```lean
theorem gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_input (hT : GOELeftTail)
    (M : CubicStrongMixing (airy1SRP (airy1FddPositive_of_goeLeftTail hT) hT)) (z : ℝ) :
    Tendsto (fun T : ℝ => (airy1Law (airy1FddPositive_of_goeLeftTail hT)).real {f | ∀ x ∈ Set.Icc (0 : ℝ) T,
      (airy1ContR (airy1FddPositive_of_goeLeftTail hT) x f - gumbelAR T) / gumbelBR T ≤ z})
      atTop (𝓝 (Real.exp (-Real.exp (-z))))
```

It is `_final₂` at `h := airy1FddPositive_of_goeLeftTail hT`: the same conclusion under
`GOELeftTail` and `CubicStrongMixing` only. No input is added, and `_final₂` and every
earlier statement are unchanged; the originals still take `Airy1FddPositive` as a
hypothesis. [`Airy1Gumbel/FddFromTasepCorollaries.lean`](Airy1Gumbel/FddFromTasepCorollaries.lean)
has 175 such `_no_fdd_input` forms of earlier results, each its original with the
hypothesis `Airy1FddPositive` supplied by `airy1FddPositive_of_goeLeftTail` (taking
`GOELeftTail` where the original did not); every other hypothesis of the original, among
them the named inputs of Lemmas 4.1, 4.2, Proposition 4.3 and Remark 5.3, is kept. Of the
44 new claims of the main package, two are compared (since v0.9.0 the comparator checks
`airy1FddPositive_of_goeLeftTail` and `_final₂_no_fdd_input` against statements of
`Challenge.lean`; see below). The other 42 and the 9 new claims of the contrib package are
`internal`: Lean's kernel checked their proofs, but the comparator does not compare their
statements.

Since v0.8.0, Remark 5.3 (the Gumbel limit derived from the Ferrari–Liu persistence
estimates) is proved for the constructed continuous process, along integer lengths as the
remark states.
[`Airy1Gumbel.gumbel_limit_continuum_airy1_ferrariLiu`](Airy1Gumbel/FerrariLiuRoute.lean)
states that, for every real `z`, `ℙ{Ã(x) ≤ a_N + b_N z for all x ∈ [0, N]} → exp(−e^{−z})`
as `N → ∞` through the integers, with the centering and scaling `a_N`, `b_N` of (1.1)–(1.2)
(`gumbelU N z`). Its hypotheses are the standing inputs `Airy1FddPositive` and
`GOELeftTail` and a new named input,
[`Airy1Gumbel.FerrariLiuPersistence`](Airy1Gumbel/FerrariLiuRoute.lean): the
finite-length persistence expansion of Ferrari–Liu (2024, Theorem 1.1, with the bounds of
their Proposition 2.5 and Section 2.4), which is assumed, not proved, here. For the
continuous version on `[0, ∞)` it says that, for every level `c ≥ 3/2` and length `L ≥ 1`,
`ℙ{Ã(t) ≤ c for all t ∈ [0, L]} = exp(−L κ(c) − S(c) + E(c, L))`, where
`κ(c) = Σ_{n ≥ 1} −2 n^{−5/3} Ai′(2 n^{2/3} c)` is the Ferrari–Liu persistence rate,
`|S(c)| ≤ −6 log(1 − 2β(c))` and
`|E(c, L)| ≤ 2 e^{−4L³/3} + Σ_{n ≥ 2} 7^{n+1} β(c)ⁿ / n · e^{−4L³/(3n²)}`, with the explicit
two-branch parameter `β(c)` of their Section 2.4 (`ferrariLiuBeta`). What is assumed
includes Ferrari–Liu's identity `log det(1 − K) = −Σ_n Tr(Kⁿ)/n`; the input's docstring
also records the sign convention of the rate and the coefficient `2` in the degree-one
error. Proved here: the bound on `β(c)`, the summation of the error series, the vanishing
of the offset `S`, and the asymptotic `κ(c) ~ ρ(c)` that turns the expansion into the
Gumbel limit (`ferrariLiuKappa_div_rhoM_tendsto`). This is the second release that adds
a named input (the first was v0.4.0). `FerrariLiuPersistence` is used only by Remark 5.3
(through its lemma `ferrariLiu_remainders`); the headline `_final₂` does not use it and
still uses exactly its three inputs, and no existing statement changed. The 25 new claims of this route are
`internal`: Lean's kernel checked their proofs, but the comparator does not compare their
statements.

Also since v0.8.0, a first step towards proving `Airy1FddPositive`, which is still an
input. The nested package proves a finite-box measure constructor,
[`AiryFdd.exists_measure_of_box_cdf`](contrib/Airy1GumbelContrib/FddMeasure/BoxCdf.lean):
a continuous function `F` on `ℝ^ι` (`ι` finite) that is nonnegative, monotone, gives every
box `(a, b]` a nonnegative alternating corner sum (`boxCdfIncrement F a b ≥ 0`), tends to
`0` when one coordinate tends to `−∞` and to `1` along the diagonal `x = (r, …, r)`,
`r → +∞`, is the distribution function `x ↦ μ(∏ᵢ (−∞, xᵢ])` of a probability measure `μ`. With it,
[`Airy1Gumbel.airy1FddPositive_of_rectangle`](Airy1Gumbel/FddRectangle.lean) derives
`Airy1FddPositive` from `GOELeftTail` and three properties of the Fredholm-determinant
formulas `AiryFdd.airy1FinCdf I`, for every finite set of times `I`: nonnegativity,
monotonicity and nonnegative rectangle increments. In v0.8.0 those three properties were
hypotheses of the theorem; v0.9.0 proves them (see above). The new claims (one in each package) are
`internal`.

Since v0.6.0, Proposition 4.3 (the mesoscopic sum, eq. (4.6)) is proved as a standalone
result for the constructed continuous process, along the paper's route. Write `Y_j` for
the maximum of `Ã` over `[j, j + 1]` (`airy1BlockMax h j`) and `ρ(M)` for the one-block
tail scale of (1.3) (`AiryConj.rhoM`).
[`Airy1Gumbel.mesoscopic_sum_airy1`](Airy1Gumbel/MesoscopicStandalone.lean) states that,
for every `χ` with `(1/2)^{1/3} < χ < 1` and every cutoff `R : ℝ → ℝ` with
`R(M) = O(√M)`, `Σ_{⌈χ√(2M)⌉ ≤ j ≤ ⌊R(M)⌋} ℙ{Y_0 > M, Y_j > M} = o(ρ(M))` as `M → ∞`
through the reals (an empty range gives the sum `0`). Its five hypotheses are the
standing inputs `Airy1FddPositive` and `GOELeftTail` and three named inputs, each
assumed, not proved, here:

- `NonnegativeWindowModulusEstimate`: the transferred local oscillation bound (4.2) on
  windows inside `[0, ∞)` (Basu–Bhattacharjee 2024); already the input of Lemma 4.1.
- `ProcessAssociated`: the association of the Airy₁ process (Pu 2025, Theorem 1.2);
  already the input of Lemma 4.2.
- [`CubicCovarianceDecay`](Airy1Gumbel/ExternalInputs.lean): the covariance asymptotic of
  the Airy₁ process (Basu–Busani–Ferrari 2023, Theorem 1.1), in the form of its upper
  bound `Cov(Ã(0), Ã(d)) ≤ e^{c d² − (4/3) d³}` for `d > 1`; until this release only the
  earlier association-route headline `_final` (below) and its intermediate forms used it.

The proof uses the first through Lemma 4.1 (the block modulus on `[0, 1]`, carried to
every block `[j, j + 1]` by shift invariance of the law), the second through Lemma 4.2,
and the third only through its proved corollary, the cubic covariance bound
`Cov(Ã(0), Ã(d)) ≤ e^{−θd³}` for every `θ < 4/3` and large `d`
(`CubicCovarianceDecay.theta_bound`). The block-to-grid cover (4.10) and the one-point
bound (4.11) at level `M − 1` are proved (`block_pair_grid_cover_airy1`,
`one_point_tail_minus_one_airy1`). This release adds no new named input. The headline
`_final₂` still uses exactly its three inputs and none of these three, and no existing
statement changed. The five new claims are `internal`: Lean's kernel checked their
proofs, but the comparator does not compare their statements.

Since v0.5.0, Lemma 4.2 (the threshold-sensitive Newman bound, eq. (4.3)) is proved for
the constructed continuous process under the standing inputs `Airy1FddPositive` and
`GOELeftTail` and the association input
[`Airy1Gumbel.ProcessAssociated`](Airy1Gumbel/ExternalInputs.lean): the association of the
Airy₁ process (Pu 2025, Theorem 1.2), in the form that every finite-dimensional marginal
gives nonnegative covariance to bounded, monotone, measurable test functions.
`ProcessAssociated` is an existing named input, assumed, not proved, here; until this
release only the earlier association-route headline `_final` (below) and its intermediate
forms used it. `GOELeftTail` is not a
hypothesis of the paper's Lemma 4.2; it is a standing input of every process-level result
here because the process is constructed. Under these inputs,
[`Airy1Gumbel.tail_sensitive_newman_airy1`](Airy1Gumbel/TailSensitiveNewman.lean) states
that there are `C > 0` and `u₀` such that, for every `u ≥ u₀` and every lag `d ≥ 0`,
`ℙ{Ã(0) > u, Ã(d) > u} ≤ C ℙ{Ã(0) > u}² + C u Cov(Ã(0), Ã(d))`; the constants do not
depend on `d`. The covariance is a genuine one: both marginals are proved
square-integrable (`memLp_two_airy1ContR`), so it is not the value `0` that Lean assigns
off `L²`. The one-point tail ratio `ℙ{Ã(0) > u − u^{−1/2}} ≤ K ℙ{Ã(0) > u}`, which the
paper takes from the density bound (4.4)–(4.5), is proved here from the GOE Fredholm
determinant (`one_point_tail_shift_le_airy1`, through the sharp singleton tail
`goe_singleton_right_tail_sub_profile_isLittleO`), so this release adds no new named
input. The headline `_final₂` still uses exactly its three inputs and does not use
`ProcessAssociated`, and no existing statement changed. The six new claims are
`internal`: Lean's kernel checked their proofs, but the comparator does not compare their
statements.

Since v0.4.0, Lemma 4.1 (the block modulus, eq. (4.1)) is proved for the constructed
process under `Airy1FddPositive`, `GOELeftTail` and a fourth named input,
[`Airy1Gumbel.NonnegativeWindowModulusEstimate`](Airy1Gumbel/BlockModulus.lean): the
transferred local oscillation bound (4.2) of arXiv:2611.23658v1 on windows inside
`[0, ∞)`, which the paper derives from Basu–Bhattacharjee (2024,
[arXiv 2406.11826](https://arxiv.org/abs/2406.11826), Lemma 5.1 with Theorem 1.4) and
which is assumed, not proved, here. The input says that there are `C₀, c₀ > 0` such that,
for all sufficiently large `ℓ`, every radius `0 < s ≤ 1` and every centre `c ≥ s`,
`ℙ{|Ã(t₁) − Ã(t₂)| > C₀ ℓ √s for some t₁, t₂ ∈ [c − s, c + s]} ≤ C₀ e^{−c₀ ℓ}`; it is
not a verbatim Basu–Bhattacharjee statement. Under these inputs,
[`Airy1Gumbel.block_modulus_airy1`](Airy1Gumbel/BlockModulus.lean) states that there are
`C, c, h₀ > 0` such that, for `0 < δ ≤ h₀`,
`ℙ{|Ã(x) − Ã(y)| > 1 for some x, y ∈ [0, 1] with |x − y| ≤ 2δ} ≤ C δ⁻¹ e^{−c δ^{−1/2}}`.
Two audit theorems check that the input is neither vacuous nor trivially true: the zero
process satisfies it (`nonnegativeWindowModulusEstimate_const`) and the process `t²`
violates it (`isEmpty_nonnegativeWindowModulusEstimate_sq`). This is the first release
that adds a named input. The headline `_final₂` still uses exactly its three inputs and
does not use the new one (its mesoscopic step goes through a high-level upcrossing
bound), and no existing statement changed. The new claims are `internal`: Lean's kernel
checked their proofs, but the comparator does not compare their statements.

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

### Video series

Six videos explain the paper, from the question to the proof
([playlist](https://www.youtube.com/playlist?list=PLNddpUb0UMeE); about an hour in total,
narrated by a synthetic voice). The last one also describes this Lean companion.

1. [The highest point of a flat interface](https://www.youtube.com/watch?v=jEq5fAASCd4)
2. [The classical recipe and why clusters matter](https://www.youtube.com/watch?v=gbM2TdlgBLY)
3. [The tail over one interval](https://www.youtube.com/watch?v=S4BQ94UsA4E)
4. [Two separated intervals](https://www.youtube.com/watch?v=zdchJXLYgP4)
5. [The middle range and the blocking argument](https://www.youtube.com/watch?v=15Vr6Y1wSUA)
6. [What is new, what is open, and the Lean check](https://www.youtube.com/watch?v=Tmh-qMmnL04)

A second series of four videos explains the companion paper, Chen and Pu, *Two-time spatial
decorrelation for the flat KPZ fixed point* ([arXiv 2607.17113](https://arxiv.org/abs/2607.17113)),
whose Proposition 3.1 is the hypothesis `CubicStrongMixing` in the table of inputs
([playlist](https://www.youtube.com/playlist?list=PLI4CESkmuyPo); about 36 minutes in total,
narrated by a synthetic voice). Episode 2 explains that mixing bound.

1. [One surface at two times](https://www.youtube.com/watch?v=cXnOSYAVEz4)
2. [The Airy₁ process forgets fast](https://www.youtube.com/watch?v=rLz7QcSSj4I)
3. [Where the optimizer lives](https://www.youtube.com/watch?v=eEzVI7CSdrE)
4. [Spatial averages and the dynamic susceptibility](https://www.youtube.com/watch?v=J1yQqgdr79M)

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
headline under the three inputs, not the inputs. Since v0.9.0 `Challenge.lean` has two more
statements: `airy1FddPositive_of_goeLeftTail` (under `GOELeftTail` alone, the Airy₁
finite-dimensional laws exist) and `gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_input`
(the first form without the hypothesis `Airy1FddPositive`, so under `GOELeftTail` and
`CubicStrongMixing` only); neither proves those two inputs.
[`Solution.lean`](Solution.lean) proves all four statements from the package, and
[`comparator.json`](comparator.json) is the configuration the comparator checks (each Solution
theorem has exactly its Challenge type and uses only the three standard axioms):

```sh
lake build ChallengeDefs Challenge Solution
```

### Comparator check of the contrib package

Since v0.3.1 the contrib package has its own comparator configuration,
[`contrib/comparator.json`](contrib/comparator.json): the 103 theorem claims of
[`contrib/claims.yaml`](contrib/claims.yaml) up to v0.7.0, one Challenge theorem
`Airy1GumbelLeanContribAudit.<decl>` each. The theorem claim added in v0.8.0
(`box-cdf-measure`, the finite-box measure constructor) and the nine added in v0.9.0 (flat
TASEP and the extended Airy₁ determinants) are `internal` and are not compared, and their
modules under `FddMeasure/` are not in the copied library.
[`contrib/Comparator/Challenge.lean`](contrib/Comparator/Challenge.lean)
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
rev = "v0.9.0"
```

## Trust and axioms

- No `sorry` and no new axioms: every audited theorem depends only on `propext`,
  `Classical.choice` and `Quot.sound`.
- The headline is conditional. Its hypotheses are the three named structures above; read
  their definitions before relying on the theorem. Lemma 4.1 (`block_modulus_airy1`)
  assumes, besides the first two, the fourth named input
  `NonnegativeWindowModulusEstimate`, which is not proved here. Lemma 4.2
  (`tail_sensitive_newman_airy1`) assumes, besides the first two, the association input
  `ProcessAssociated` (Pu 2025, Theorem 1.2), which is not proved here. Proposition 4.3
  (`mesoscopic_sum_airy1`) assumes, besides the first two, these three:
  `NonnegativeWindowModulusEstimate`, `ProcessAssociated` and the covariance input
  `CubicCovarianceDecay` (Basu–Busani–Ferrari 2023, Theorem 1.1), none of which is
  proved here. Remark 5.3 (`gumbel_limit_continuum_airy1_ferrariLiu`) assumes, besides
  the first two, the new input `FerrariLiuPersistence` (the finite-length persistence
  expansion of Ferrari–Liu 2024), which is not proved here and which no other result uses.
- `airy1FddPositive_of_goeLeftTail` proves `Airy1FddPositive` under `GOELeftTail`, not
  unconditionally. The `_no_fdd_input` headline therefore assumes `GOELeftTail` and
  `CubicStrongMixing`, neither of which is proved here. The comparator checks the two
  `_final₂` statements under the three inputs and, since v0.9.0,
  `airy1FddPositive_of_goeLeftTail` and `_final₂_no_fdd_input`; the other `_no_fdd_input`
  forms are built, not compared.
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

Theorem 1.1 is proved for a constructed continuous Airy\_1 process under three named inputs, and since v0.9.0 under GOELeftTail and CubicStrongMixing only (Airy1FddPositive proved under GOELeftTail); Lemmas 4.1, 4.2, Proposition 4.3 and Remark 5.3 under further named inputs, each assumed. Lemmas 3.3-3.8 and B.1-B.6 are contrib results, outside this table only because rows name main-package claims.

- Paper: *Gumbel Fluctuations of the Maximum of the Airy\_1 Process*, [arXiv:2611.23658v1](https://arxiv.org/abs/2611.23658v1).
- Results listed: 23. In Lean with the paper's own hypotheses: 0; in Lean with extra hypotheses, named below: 11; not formalized: 12.
- Verified: 2 of the 11 result(s) in Lean.

## The paper's results in Lean

### Theorem 1.1: Gumbel limit of the normalized maximum

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1GumbelAudit.Airy1Gumbel.gumbel_limit_continuum_real_normalized_airy1_final₂` in [Challenge.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

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

**In Lean.** `Airy1GumbelAudit.Airy1Gumbel.gumbel_limit_continuum_real_normalized_airy1_final₂_coord` in [Challenge.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

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

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: Airy1FddPositive: for every finite set of times, a probability law whose box distribution function is the Airy\_1 Fredholm-determinant formula (Quastel-Remenik, Theorem 1; Borodin-Ferrari-Prahofer 2007). A hypothesis of these two theorems; since v0.9.0 it is proved under GOELeftTail (airy1FddPositive\_of\_goeLeftTail), so the next row has the same conclusion without it; GOELeftTail: a cubic left-tail bound for the one-point law (Baik-Buckingham-DiFranco 2008 with the Ferrari-Spohn GOE identity); an input the paper does not need, since it starts from an existing continuous process; CubicStrongMixing: strong mixing between past and future sigma-algebras at rate exp(-c d^3) (Chen-Pu, arXiv 2607.17113, Proposition 3.1).

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** The process is the version of the Kolmogorov-extension law with continuous paths on \[0, infinity); centering and scaling are those of (1.1)-(1.2) for real T. The mesoscopic step is proved by the two-time Fredholm determinant bound and a high-level upcrossing bound, not by association and the covariance asymptotic. The comparator checks these two statements, unchanged in v0.9.0.

### Theorem 1.1, two-input form: Gumbel limit of the normalized maximum without the input Airy1FddPositive

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1GumbelAudit.Airy1Gumbel.gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_input` in [Challenge.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem gumbel_limit_continuum_real_normalized_airy1_final₂_no_fdd_input (hT : GOELeftTail) :
    (∃ μ : Measure (ℝ → ℝ), IsAiry1Law μ) ∧
      ∀ μ : Measure (ℝ → ℝ), IsAiry1Law μ →
        (∃ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y) ∧
          ∀ Y : ℝ → (ℝ → ℝ) → ℝ, IsContinuousVersion μ Y → CubicStrongMixing μ Y →
            ∀ z : ℝ, Tendsto (fun T : ℝ => μ.real {f | ∀ x ∈ Icc (0 : ℝ) T,
              (Y x f - gumbelAR T) / gumbelBR T ≤ z})
              atTop (𝓝 (Real.exp (-Real.exp (-z))))
```

**In Lean.** `Airy1GumbelAudit.Airy1Gumbel.airy1FddPositive_of_goeLeftTail` in [Challenge.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem airy1FddPositive_of_goeLeftTail (hT : GOELeftTail) : Airy1FddPositive
```

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: GOELeftTail: the cubic left-tail bound for the one-point law, as in the row above; it also supplies Airy1FddPositive, through airy1FddPositive\_of\_goeLeftTail; CubicStrongMixing: strong mixing between past and future sigma-algebras at rate exp(-c d^3) (Chen-Pu, arXiv 2607.17113, Proposition 3.1), stated for the process built from airy1FddPositive\_of\_goeLeftTail.

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** New in v0.9.0: the conclusion of the row above under GOELeftTail and CubicStrongMixing only. Airy1FddPositive is proved under GOELeftTail, not unconditionally (airy1FddPositive\_of\_goeLeftTail, via flat discrete TASEP and its scaling limit). No input is added. Both claims are compared. The coordinate form \_final2\_coord\_no\_fdd\_input is built, not compared.

### Proposition 1.2: Two-term expansion of the one-block tail

**Built, not compared.** Lean accepts the proof (the build passed), but its statement has not been compared by a second checker, which lean-pkg needs before it counts the result as verified.

**Internal.** `airy1-gumbel-lean/fixed-interval-tail-expansion`, `airy1-gumbel-lean/interval-hitting-law-positive-length`, `airy1-gumbel-lean/block-law-core`, `airy1-gumbel-lean/block-law-unconditional`, `airy1-gumbel-lean/sharp-tail-discharge`: marked internal in `claims.yaml`, a step of the formalization rather than a result offered for reuse. An internal claim counts as verified only when the statement comparison judged its declaration, on the same evidence as any other result.

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1Gumbel.airy1Law_interval_tail_sub_traceLead_isLittleO` in [Airy1Gumbel/BlockLawUnconditional.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/BlockLawUnconditional.lean).

```lean
theorem airy1Law_interval_tail_sub_traceLead_isLittleO
    (h : Airy1FddPositive) (hLeft : GOELeftTail) (T : ℝ) (hT : 0 < T) :
    (fun M : ℝ => (airy1Law h).real {f | ∃ t ∈ Icc (0 : ℝ) T, M < airy1ContR h t f}
      - AiryConj.traceLead M T) =o[atTop] (fun M => AiryConj.rhoM M / M)
```

**In Lean.** `Airy1Gumbel.airy1Law_sup_le_eq_fredholmDet_at_weight'` in [Airy1Gumbel/BlockLawUnconditional.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/BlockLawUnconditional.lean).

```lean
theorem airy1Law_sup_le_eq_fredholmDet_at_weight' (h : Airy1FddPositive) (hLeft : GOELeftTail)
    {x M T a : ℝ} (hx : 0 ≤ x) (hT : 0 < T) (hM : 0 < M) (ha : T + 1 ≤ a) :
    (airy1Law h).real {f | ∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet (AiryConj.airyTildeOp M T a hT hM ha) 1
```

**In Lean.** `Airy1Gumbel.airy1Law_sup_le_eq_fredholmDet` in [Airy1Gumbel/BlockLaw.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/BlockLaw.lean).

```lean
theorem airy1Law_sup_le_eq_fredholmDet (h : Airy1FddPositive) (hT : GOELeftTail) {x M T : ℝ}
    (hx : 0 ≤ x) (hT1 : 1 ≤ T) (hM : 0 < M) (hK : AiryFdd.MeshHittingLimit M T) :
    (airy1Law h).real {f | ∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1
```

**In Lean.** `Airy1Gumbel.airy1Law_sup_le_eq_fredholmDet'` in [Airy1Gumbel/BlockLawUnconditional.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/BlockLawUnconditional.lean).

```lean
theorem airy1Law_sup_le_eq_fredholmDet' (h : Airy1FddPositive) (hT : GOELeftTail) {x M T : ℝ}
    (hx : 0 ≤ x) (hT1 : 1 ≤ T) (hM : 0 < M) :
    (airy1Law h).real {f | ∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (AiryConj.airyTildeOp M T (2 * T) (by linarith) hM (by linarith)) 1
```

**In Lean.** `Airy1Gumbel.sharp_tail_of_QRUnitBlockLaw` in [Airy1Gumbel/SharpTail.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/SharpTail.lean).

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

**In Lean.** `Airy1Gumbel.touching_of_QR` in [Airy1Gumbel/Touching.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/Touching.lean).

```lean
theorem touching_of_QR {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (Y_meas : ∀ j, Measurable (Y j))
    (stat_marginal : ∀ (u : ℝ) (i : ℕ), P {ω | Y i ω > u} = P {ω | Y 0 ω > u})
    (qr : QRUnitBlockLaw Y P) (qr₂ : QRTwoBlockLaw Y P) (z : ℝ) :
    Tendsto (fun N : ℕ =>
      (N : ℝ) * P.real {ω | Y 0 ω > gumbelU N z ∧ Y 1 ω > gumbelU N z}) atTop (𝓝 0)
```

**In Lean.** `Airy1Gumbel.qrTwoBlockLaw_airy1` in [Airy1Gumbel/BlockLaw.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/BlockLaw.lean).

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

**In Lean.** `Airy1Gumbel.separated_of_QR` in [Airy1Gumbel/Separated.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/Separated.lean).

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

**In Lean.** `Airy1Gumbel.qrTwoIntervalLaw_airy1` in [Airy1Gumbel/TwoIntervalLaw.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/TwoIntervalLaw.lean).

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

**In Lean.** `Airy1Gumbel.airy1Law_two_blocks_le_eq_fredholmDet_of_length` in [Airy1Gumbel/TwoIntervalLaw.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/TwoIntervalLaw.lean).

```lean
theorem airy1Law_two_blocks_le_eq_fredholmDet_of_length (h : Airy1FddPositive) (hLeft : GOELeftTail)
    {x M T r a : ℝ} (hx : 0 ≤ x) (hT : 0 < T) (hr : 0 < r)
    (hM : 0 < M) (ha : 2 * T + r + 1 ≤ a) :
    (airy1Law h).real {f | (∀ t ∈ Icc x (x + T), airy1ContR h t f ≤ M) ∧
        ∀ t ∈ Icc (x + T + r) (x + T + r + T), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (HilbertSchmidt.kernelOperator (AiryFdd.memLp_kcupKerT_of_length hT hr hM ha)) 1
```

**In Lean.** `Airy1Gumbel.airy1Law_two_blocks_le_eq_fredholmDet` in [Airy1Gumbel/TwoIntervalLaw.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/TwoIntervalLaw.lean).

```lean
theorem airy1Law_two_blocks_le_eq_fredholmDet (h : Airy1FddPositive) (hT : GOELeftTail)
    {x M r a : ℝ} (hx : 0 ≤ x) (hr : 0 < r) (hM : 0 < M) (ha : r + 3 ≤ a) :
    (airy1Law h).real {f | (∀ t ∈ Icc x (x + 1), airy1ContR h t f ≤ M) ∧
        ∀ t ∈ Icc (x + 1 + r) (x + 1 + r + 1), airy1ContR h t f ≤ M}
      = HilbertSchmidt.fredholmDet
          (HilbertSchmidt.kernelOperator (AiryTwoInt.memLp_kcupKerT hr hM ha)) 1
```

**In Lean.** `Airy1Gumbel.qrTwoIntervalLaw_airy1` in [Airy1Gumbel/TwoIntervalLaw.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/TwoIntervalLaw.lean).

```lean
theorem qrTwoIntervalLaw_airy1 (h : Airy1FddPositive) (hT : GOELeftTail) :
    QRTwoIntervalLaw (airy1BlockMax h) (airy1Law h) where
  law
```

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: Airy1FddPositive and GOELeftTail, for the two-interval hitting law of the constructed process.

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Proved for every T &gt; 0, r &gt; 0, M &gt; 0 at any weight a &gt;= 2T + r + 1 (two-interval-law-equal-length), in the trace-class form (3.3) of Remark 3.2: det(I - K\~), K\~ the conjugated kernel of (3.2). The determinant displayed in (3.1) has no separate Lean definition; the paper reads it through (3.3). Versions 0.1.0 and 0.2.0 had T = 1 only.

### Lemma 4.1: Block modulus

**Not yet verified.** lean-pkg's record of the checks says: out-of-scope. Until it says verified, read the Lean statement below as work in progress.

**Internal.** `airy1-gumbel-lean/block-modulus-lemma-4-1`, `airy1-gumbel-lean/nonnegative-window-modulus-input`, `airy1-gumbel-lean/nonnegative-window-modulus-constant`, `airy1-gumbel-lean/nonnegative-window-modulus-falsity-witness`: marked internal in `claims.yaml`, a step of the formalization rather than a result offered for reuse. An internal claim counts as verified only when the statement comparison judged its declaration, on the same evidence as any other result.

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1Gumbel.block_modulus_airy1` in [Airy1Gumbel/BlockModulus.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/BlockModulus.lean).

```lean
theorem block_modulus_airy1 (h : Airy1FddPositive) (hT : GOELeftTail)
    (L : NonnegativeWindowModulusEstimate (airy1Law h) (airy1SRP h hT).A) :
    ∃ C c h₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < h₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ h₀ →
        (airy1Law h).real
          {f | ∃ x y : ℝ, x ∈ Icc (0 : ℝ) 1 ∧ y ∈ Icc (0 : ℝ) 1 ∧
            |x - y| ≤ 2 * δ ∧ 1 < |airy1ContR h x f - airy1ContR h y f|}
          ≤ C * δ⁻¹ * Real.exp (-c * δ ^ (-(1 / 2 : ℝ)))
```

**In Lean.** `Airy1Gumbel.NonnegativeWindowModulusEstimate` in [Airy1Gumbel/BlockModulus.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/BlockModulus.lean). Its statement could not be read reliably from the source; open the file to read it.

**In Lean.** `Airy1Gumbel.nonnegativeWindowModulusEstimate_const` in [Airy1Gumbel/BlockModulus.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/BlockModulus.lean).

```lean
theorem nonnegativeWindowModulusEstimate_const {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    Nonempty (NonnegativeWindowModulusEstimate P (fun (_ : ℝ) (_ : Ω) => (0 : ℝ)))
```

**In Lean.** `Airy1Gumbel.isEmpty_nonnegativeWindowModulusEstimate_sq` in [Airy1Gumbel/BlockModulus.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/BlockModulus.lean).

```lean
theorem isEmpty_nonnegativeWindowModulusEstimate_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    IsEmpty (NonnegativeWindowModulusEstimate P (fun (t : ℝ) (_ : Ω) => t ^ 2))
```

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: NonnegativeWindowModulusEstimate, assumed, not proved: the transferred local oscillation bound (4.2) of arXiv:2611.23658v1 on windows inside \[0, infinity): for large l, 0 &lt; s &lt;= 1 and centres c &gt;= s, P(\|A(t1) - A(t2)\| &gt; C0 l sqrt(s) for some t1, t2 in \[c - s, c + s\]) &lt;= C0 exp(-c0 l). The paper derives it from Basu-Bhattacharjee (2024, arXiv 2406.11826); that derivation is not formalized; Airy1FddPositive and GOELeftTail, for the continuous version of the constructed process.

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Proved as eq. (4.1) for the continuous version on \[0, 1\] (block-modulus-lemma-4-1). The input is new in v0.4.0; the zero process satisfies it and the process t^2 violates it (the two audit claims). The headline (Theorem 1.1) does not use this lemma or the new input: its mesoscopic step goes through a high-level upcrossing bound.

### Lemma 4.2: Pair bound under association

**Built, not compared.** Lean accepts the proof (the build passed), but its statement has not been compared by a second checker, which lean-pkg needs before it counts the result as verified.

**Internal.** `airy1-gumbel-lean/threshold-sensitive-newman-lemma-4-2`, `airy1-gumbel-lean/airy1-continuous-point-second-moment`, `airy1-gumbel-lean/airy1-one-point-tail-shift`, `airy1-gumbel-lean/airy1-one-point-tail-profile`, `airy1-gumbel-lean/goe-singleton-right-tail`, `airy1-gumbel-lean/goe-operator-diagonal-trace`: marked internal in `claims.yaml`, a step of the formalization rather than a result offered for reuse. An internal claim counts as verified only when the statement comparison judged its declaration, on the same evidence as any other result.

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1Gumbel.tail_sensitive_newman_airy1` in [Airy1Gumbel/TailSensitiveNewman.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/TailSensitiveNewman.lean).

```lean
theorem tail_sensitive_newman_airy1 (h : Airy1FddPositive) (hT : GOELeftTail)
    (As : ProcessAssociated (airy1SRP h hT)) :
    ∃ C u₀ : ℝ, 0 < C ∧ ∀ u d : ℝ, u₀ ≤ u → 0 ≤ d →
      (airy1Law h).real {f | u < airy1ContR h 0 f ∧ u < airy1ContR h d f}
        ≤ C * ((airy1Law h).real {f | u < airy1ContR h 0 f}) ^ 2 +
          C * u * covariance (airy1ContR h 0) (airy1ContR h d) (airy1Law h)
```

**In Lean.** `Airy1Gumbel.memLp_two_airy1ContR` in [Airy1Gumbel/TailSensitiveNewman.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/TailSensitiveNewman.lean).

```lean
theorem memLp_two_airy1ContR (h : Airy1FddPositive) (hT : GOELeftTail) (t : ℝ) :
    MemLp (airy1ContR h t) 2 (airy1Law h)
```

**In Lean.** `Airy1Gumbel.one_point_tail_shift_le_airy1` in [Airy1Gumbel/TailSensitiveNewman.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/TailSensitiveNewman.lean).

```lean
theorem one_point_tail_shift_le_airy1 (h : Airy1FddPositive) (hT : GOELeftTail) :
    ∃ K u₀ : ℝ, 0 < K ∧ 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      (airy1Law h).real {f | u - (Real.sqrt u)⁻¹ < airy1ContR h 0 f}
        ≤ K * (airy1Law h).real {f | u < airy1ContR h 0 f}
```

**In Lean.** `Airy1Gumbel.one_point_tail_profile_bounds_airy1` in [Airy1Gumbel/TailSensitiveNewman.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/TailSensitiveNewman.lean).

```lean
theorem one_point_tail_profile_bounds_airy1 (h : Airy1FddPositive) (hT : GOELeftTail) :
    ∃ A B u₀ : ℝ, 0 < A ∧ 0 < B ∧ 0 < u₀ ∧
      ∀ u : ℝ, u₀ ≤ u →
        A * (AiryConj.rhoM u / u) ≤
          (airy1Law h).real {f | u < airy1ContR h 0 f} ∧
        (airy1Law h).real {f | u < airy1ContR h 0 f} ≤ B * (AiryConj.rhoM u / u)
```

**In Lean.** `Airy1Gumbel.goe_singleton_right_tail_sub_profile_isLittleO` in [Airy1Gumbel/TailSensitiveNewman.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/TailSensitiveNewman.lean).

```lean
theorem goe_singleton_right_tail_sub_profile_isLittleO :
    (fun u : ℝ => 1 - AiryFdd.airy1FinCdf {0} (fun _ => u) -
      AiryConj.rhoM u / (8 * u)) =o[atTop] (fun u => AiryConj.rhoM u / u)
```

**In Lean.** `Airy1Gumbel.trace_goeOp_eq_half_integral` in [Airy1Gumbel/TailSensitiveNewman.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/TailSensitiveNewman.lean).

```lean
theorem trace_goeOp_eq_half_integral (u : ℝ) :
    HilbertSchmidt.trace (AiryFdd.goeOp u) =
      (1 / 2 : ℝ) * (∫ x in Ioi (2 * u), airyAiReal x)
```

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: ProcessAssociated, assumed, not proved: the association of the Airy\_1 process (Pu 2025, Theorem 1.2), in the form that every finite-dimensional marginal gives nonnegative covariance to bounded, monotone, measurable test functions. An existing named input, until v0.5.0 used only by the earlier association-route headline; Airy1FddPositive and GOELeftTail, standing inputs for the continuous version of the constructed process; GOELeftTail is not a hypothesis of the paper's Lemma 4.2.

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Proved as eq. (4.3) for every u &gt;= u0 and every lag d &gt;= 0, constants independent of d. The covariance is genuine: both marginals are proved square-integrable. The one-point tail ratio, from a density bound in the paper, is proved from the GOE Fredholm determinant: no new named input. The headline (Theorem 1.1) does not use this lemma.

### Proposition 4.3: Mesoscopic sum

**Not yet verified.** lean-pkg's record of the checks says: out-of-scope. Until it says verified, read the Lean statement below as work in progress.

**Internal.** `airy1-gumbel-lean/standalone-mesoscopic-sum-prop-4-3`, `airy1-gumbel-lean/mesoscopic-block-pair-grid-cover`, `airy1-gumbel-lean/one-point-tail-minus-one`, `airy1-gumbel-lean/unit-block-oscillation-shift`, `airy1-gumbel-lean/unit-block-oscillation-event`: marked internal in `claims.yaml`, a step of the formalization rather than a result offered for reuse. An internal claim counts as verified only when the statement comparison judged its declaration, on the same evidence as any other result.

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1Gumbel.mesoscopic_sum_airy1` in [Airy1Gumbel/MesoscopicStandalone.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/MesoscopicStandalone.lean).

```lean
theorem mesoscopic_sum_airy1 (h : Airy1FddPositive) (hT : GOELeftTail)
    (L : NonnegativeWindowModulusEstimate (airy1Law h) (airy1SRP h hT).A)
    (As : ProcessAssociated (airy1SRP h hT))
    (Cov : CubicCovarianceDecay (airy1SRP h hT))
    (χ : ℝ) (hχ : (1 / 2 : ℝ) ^ (1 / 3 : ℝ) < χ) (hχ₁ : χ < 1)
    (R : ℝ → ℝ) (hR : R =O[atTop] fun M => Real.sqrt M) :
    (fun M : ℝ =>
      ∑ j ∈ Finset.Icc ⌈χ * Real.sqrt (2 * M)⌉₊ ⌊R M⌋₊,
        (airy1Law h).real {f | M < airy1BlockMax h 0 f ∧ M < airy1BlockMax h j f})
      =o[atTop] AiryConj.rhoM
```

**In Lean.** `Airy1Gumbel.block_pair_grid_cover_airy1` in [Airy1Gumbel/MesoscopicStandalone.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/MesoscopicStandalone.lean).

```lean
theorem block_pair_grid_cover_airy1 (h : Airy1FddPositive) (j n : ℕ) (hn : 0 < n)
    (δ M : ℝ) (hmesh : 1 / (n : ℝ) ≤ 2 * δ) :
    (airy1Law h).real {f | M < airy1BlockMax h 0 f ∧ M < airy1BlockMax h j f} ≤
      (airy1Law h).real (unit_block_oscillation_event h 0 δ) +
      (airy1Law h).real (unit_block_oscillation_event h j δ) +
      ∑ k ∈ Finset.range (n + 1), ∑ k' ∈ Finset.range (n + 1),
        (airy1Law h).real {f | M - 1 < airy1ContR h (gridPt 0 n k) f ∧
          M - 1 < airy1ContR h (gridPt j n k') f}
```

**In Lean.** `Airy1Gumbel.one_point_tail_minus_one_airy1` in [Airy1Gumbel/MesoscopicStandalone.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/MesoscopicStandalone.lean).

```lean
theorem one_point_tail_minus_one_airy1 (h : Airy1FddPositive) (hT : GOELeftTail) :
    ∃ B E U : ℝ, 0 < B ∧ 0 < E ∧ 0 < U ∧
      ∀ M : ℝ, U ≤ M →
        (airy1Law h).real {f | M - 1 < airy1ContR h 0 f} ≤
          B * M ^ (-3 / 4 : ℝ) *
            Real.exp (-AiryConj.kappaC * M ^ (3 / 2 : ℝ) + E * Real.sqrt M)
```

**In Lean.** `Airy1Gumbel.block_oscillation_probability_shift_airy1` in [Airy1Gumbel/MesoscopicStandalone.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/MesoscopicStandalone.lean).

```lean
theorem block_oscillation_probability_shift_airy1 (h : Airy1FddPositive) (hT : GOELeftTail)
    (j : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    (airy1Law h).real (unit_block_oscillation_event h j δ) =
      (airy1Law h).real (unit_block_oscillation_event h 0 δ)
```

**In Lean.** `Airy1Gumbel.unit_block_oscillation_event` in [Airy1Gumbel/MesoscopicStandalone.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/MesoscopicStandalone.lean). Its statement could not be read reliably from the source; open the file to read it.

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: NonnegativeWindowModulusEstimate, assumed, not proved: the transferred local oscillation bound (4.2) on windows inside \[0, infinity) (Basu-Bhattacharjee 2024); already the input of Lemma 4.1, through which it is used; ProcessAssociated, assumed, not proved: the association of the Airy\_1 process (Pu 2025, Theorem 1.2); already the input of Lemma 4.2, through which it is used; CubicCovarianceDecay, assumed, not proved: the covariance asymptotic of the Airy\_1 process (Basu-Busani-Ferrari 2023, Theorem 1.1), as the upper bound Cov(A(0), A(d)) &lt;= exp(c d^2 - (4/3) d^3) for d &gt; 1; used only through its proved corollary Cov(A(0), A(d)) &lt;= exp(-theta d^3) for theta &lt; 4/3 and large d. Until v0.6.0 used only by the earlier association-route headline and its intermediate forms; Airy1FddPositive and GOELeftTail, standing inputs for the continuous version of the constructed process.

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Proved as eq. (4.6) for the block maxima Y\_j of the continuous version, every chi in ((1/2)^(1/3), 1) and every cutoff R(M) = O(sqrt(M)), M real (mesoscopic\_sum\_airy1), along the paper's route. No new named input. The headline does not use this result or these three inputs; it proves the Section 5.2 specialisation along the two-point route (mesoscopic-of-bounds-tp).

### Lemmas 5.1-5.2: Centering, normalization and the blocking assembly of Section 5.2

**Built, not compared.** Lean accepts the proof (the build passed), but its statement has not been compared by a second checker, which lean-pkg needs before it counts the result as verified.

**Internal.** `airy1-gumbel-lean/normalization-centering`, `airy1-gumbel-lean/normalization-scaling`, `airy1-gumbel-lean/decouple-discharge`, `airy1-gumbel-lean/gumbel-limit-conditional`, `airy1-gumbel-lean/mesoscopic-of-bounds-tp`: marked internal in `claims.yaml`, a step of the formalization rather than a result offered for reuse. An internal claim counts as verified only when the statement comparison judged its declaration, on the same evidence as any other result.

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1Gumbel.airyH_gumbelA` in [Airy1Gumbel/Normalization.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/Normalization.lean).

```lean
theorem airyH_gumbelA :
    Tendsto (fun N : ℕ => airyH (gumbelA N) - Real.log N) atTop (𝓝 0)
```

**In Lean.** `Airy1Gumbel.gumbel_normalization` in [Airy1Gumbel/Normalization.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/Normalization.lean).

```lean
theorem gumbel_normalization (z : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-airyH (gumbelU N z)))
      atTop (𝓝 (Real.exp (-z)))
```

**In Lean.** `Airy1Gumbel.decouple_of_CubicStrongMixing` in [Airy1Gumbel/MixingRecord.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/MixingRecord.lean).

```lean
theorem decouple_of_CubicStrongMixing (M : CubicStrongMixing X) (C : Airy1ContinuousMax P)
    (hA : X.A = C.A) :
    ∀ (S T : Finset ℕ) (q : ℕ) (u : ℝ),
      (∀ s ∈ S, ∀ t ∈ T, s + q ≤ t) →
      |P.real ({ω | ∀ s ∈ S, C.Y s ω ≤ u} ∩ {ω | ∀ t ∈ T, C.Y t ω ≤ u}) -
        P.real {ω | ∀ s ∈ S, C.Y s ω ≤ u} * P.real {ω | ∀ t ∈ T, C.Y t ω ≤ u}|
        ≤ M.alphaY q
```

**In Lean.** `Airy1Gumbel.Airy1BlockExtremes.gumbel_limit` in [Airy1Gumbel/GumbelLimit.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/GumbelLimit.lean).

```lean
theorem Airy1BlockExtremes.gumbel_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : Airy1BlockExtremes P) (z : ℝ) :
    Tendsto (fun N : ℕ => P.real {ω | ∀ j ∈ Finset.range N, D.Y j ω ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z))))
```

**In Lean.** `Airy1Gumbel.mesoscopic_of_boundsTP` in [Airy1Gumbel/MesoscopicTP.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/MesoscopicTP.lean).

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

### Remark 5.3: Persistence derivation

**Not yet verified.** lean-pkg's record of the checks says: out-of-scope. Until it says verified, read the Lean statement below as work in progress.

**Internal.** `airy1-gumbel-lean/ferrari-liu-gumbel-limit-remark-5-3`, `airy1-gumbel-lean/ferrari-liu-persistence-input`, `airy1-gumbel-lean/ferrari-liu-persistence-remainders`, `airy1-gumbel-lean/ferrari-liu-rate-normalization`, `airy1-gumbel-lean/ferrari-liu-kappa-div-rho-limit`: marked internal in `claims.yaml`, a step of the formalization rather than a result offered for reuse. An internal claim counts as verified only when the statement comparison judged its declaration, on the same evidence as any other result.

**In the paper.** The statement is not quoted here; read it in the paper.

**In Lean.** `Airy1Gumbel.gumbel_limit_continuum_airy1_ferrariLiu` in [Airy1Gumbel/FerrariLiuRoute.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/FerrariLiuRoute.lean).

```lean
theorem gumbel_limit_continuum_airy1_ferrariLiu
    (h : Airy1FddPositive) (hT : GOELeftTail)
    (FL : FerrariLiuPersistence (airy1Law h) (airy1SRP h hT).A) (z : ℝ) :
    Tendsto (fun N : ℕ => (airy1Law h).real
        {f | ∀ x ∈ Icc (0 : ℝ) N, airy1ContR h x f ≤ gumbelU N z})
      atTop (𝓝 (Real.exp (-Real.exp (-z))))
```

**In Lean.** `Airy1Gumbel.FerrariLiuPersistence` in [Airy1Gumbel/FerrariLiuRoute.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/FerrariLiuRoute.lean). Its statement could not be read reliably from the source; open the file to read it.

**In Lean.** `Airy1Gumbel.ferrariLiu_remainders` in [Airy1Gumbel/FerrariLiuRoute.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/FerrariLiuRoute.lean).

```lean
theorem ferrariLiu_remainders {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A : ℝ → Ω → ℝ}
    (FL : FerrariLiuPersistence μ A) :
    Tendsto FL.S atTop (𝓝 0) ∧
      ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
        ∀ c L : ℝ, (3 / 2 : ℝ) ≤ c → 1 ≤ L →
          |FL.E c L| ≤ C * Real.exp (-(δ * L))
```

**In Lean.** `Airy1Gumbel.ferrariLiuKappa_gumbel_normalization` in [Airy1Gumbel/FerrariLiuRoute.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/FerrariLiuRoute.lean).

```lean
theorem ferrariLiuKappa_gumbel_normalization (z : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ) * ferrariLiuKappa (gumbelU N z))
      atTop (𝓝 (Real.exp (-z)))
```

**In Lean.** `Airy1Gumbel.ferrariLiuKappa_div_rhoM_tendsto` in [Airy1Gumbel/FerrariLiuRoute.lean](https://github.com/chenle02/airy1-gumbel-lean/blob/8a085b7b234001112fb3a919cf5b6b246233d5fb/Airy1Gumbel/FerrariLiuRoute.lean).

```lean
theorem ferrariLiuKappa_div_rhoM_tendsto :
    Tendsto (fun c : ℝ => ferrariLiuKappa c / AiryConj.rhoM c) atTop (𝓝 1)
```

**Hypotheses.** The paper's, plus these, which the Lean statement assumes and the paper proves or assumes elsewhere: FerrariLiuPersistence, assumed, not proved: the finite-length persistence expansion of Ferrari-Liu (2024, Theorem 1.1, Proposition 2.5, Section 2.4): for c &gt;= 3/2 and L &gt;= 1, P(A &lt;= c on \[0, L\]) = exp(-L kappa(c) - S(c) + E(c, L)), \|S(c)\| &lt;= -6 log(1 - 2 beta(c)), E(c, L) bounded by their trace remainder; it includes their identity log det(1 - K) = -sum Tr(K^n)/n. Used only by Remark 5.3; Airy1FddPositive and GOELeftTail, standing inputs for the continuous version of the constructed process.

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Proved as the remark states: P(A(x) &lt;= a\_N + b\_N z for all x in \[0, N\]) -&gt; exp(-e^(-z)) along integer N, every real z (gumbel\_limit\_continuum\_airy1\_ferrariLiu). The input is new in v0.8.0. The summation of the error series and kappa(c) \~ rho(c) are proved. The headline (Theorem 1.1) does not use this result or FerrariLiuPersistence, and its three inputs are unchanged.

## Not formalized

- Lemma 3.3 (Joint inclusion for separated blocks): Proved in a different form: joint\_exceed\_eq\_detComb (Airy1Gumbel/Separated.lean) holds eventually in u (paper: sqrt(2M) &gt;= r + 3) under the QR records, proved for airy1Law under Airy1FddPositive and GOELeftTail; the decomposition, AiryTwoInt.twoIntKCup\_decomp (contrib TwoInterval/TwoIntervalOps.lean), as stated. Shown as outside only because coverage rows can name main-package claims alone.
- Lemma 3.4 (Interaction trace formula): Proved in contrib in a different form: C\_r trace class (AiryTwoInt.isTraceClass\_crKerT, TwoInterval/TwoIntervalMembership.lean), trace = sum of four sector traces as iterated integrals (AiryTwoInt.trace\_crKerT\_eq\_sectors, TwoInterval/TwoIntervalTrace.lean); no R^4 absolute-convergence statement. Shown as outside only because coverage rows can name main-package claims alone.
- Lemma 3.5 (RR trace): Proved in contrib in a different form: saddle bound as stated (AiryConj.saddleF\_ge, AiryKernel/GaussianSaddle.lean); RR bound (AiryTwoInt.trSectorRR\_abs\_le, TwoInterval/SectorRR.lean) with an extra C2 exp(-c2 M^2), absorbed only in abs\_trace\_crKerT\_le\_discharged. Shown as outside only because coverage rows can name main-package claims alone.
- Lemma 3.6 (Mixed traces): Proved in the contrib library as stated, with no named input: AiryTwoInt.trSectorRF\_eq\_trSectorFR (contrib/Airy1GumbelContrib/TwoInterval/SectorRF.lean) and AiryTwoInt.abs\_trSectorFR\_le\_absorbed (TwoInterval/SectorFR.lean). Shown as outside only because coverage rows can name main-package claims alone.
- Lemma 3.7 (FF trace): Proved in the contrib library as stated, with no named input: AiryTwoInt.trSectorFF\_abs\_le (contrib/Airy1GumbelContrib/TwoInterval/SectorFF.lean). Shown as outside only because coverage rows can name main-package claims alone.
- Lemma 3.8 (Joint trace norms): Proved in contrib in a weaker form: traces and Hilbert-Schmidt norms bounded (AiryTwoInt.twoInt\_stepThree, TwoInterval/TwoIntervalDetRem.lean; hsNorm\_crKerT\_le\_discharged, TwoInterval/TwoIntervalN3.lean; abs\_trace\_crKerT\_le\_discharged), no trace-norm bound; Proposition 1.4 uses this form. Shown as outside only because coverage rows can name main-package claims alone.
- Lemma B.1 (Airy Laplace-type integral): Proved in the contrib library as stated, with no named input: airyAiReal\_laplace (contrib/Airy1GumbelContrib/Airy/AiryLaplaceFull.lean), with the integrability AiryConj.integrable\_exp\_mul\_airyAiReal\_sq (AiryKernel/ConjugateW.lean). Shown as outside only because coverage rows can name main-package claims alone.
- Lemma B.2 (Hilbert-Schmidt bound for W): Proved in the contrib library as stated (absolute C, T &gt; 0, lambda &gt;= T + 1), with no named input: AiryConj.wKernel\_sq\_integral\_le (contrib/Airy1GumbelContrib/AiryKernel/ConjugateW.lean). Shown as outside only because coverage rows can name main-package claims alone.
- Lemma B.3 (Hilbert-Schmidt bound for V): Proved in the contrib library as stated (the bound e^(2T lambda^2 - 4M lambda), the paper's form with a^2 = 2M), with no named input: AiryConj.vKernel\_sq\_integral\_le (contrib/Airy1GumbelContrib/AiryKernel/ConjugateV.lean). Shown as outside only because coverage rows can name main-package claims alone.
- Lemma B.4 (Weighted heat-operator norm): Proved in the contrib library as stated, on a larger parameter range (every real a; the paper has a &gt; 0), with no named input: AiryTwoInt.enorm\_conjHeatCLM\_le (contrib/Airy1GumbelContrib/TwoInterval/TwoIntervalMembership.lean). Shown as outside only because coverage rows can name main-package claims alone.
- Lemma B.5 (Hilbert-Schmidt bound for the U Q P U Phi product): Proved in the contrib library as stated (the Hilbert-Schmidt bound of the paper's own product), with no named input: AiryConj.uphi\_hs\_le (contrib/Airy1GumbelContrib/AiryKernel/ConjugateUPhi.lean). Shown as outside only because coverage rows can name main-package claims alone.
- Lemma B.6 (Truncated Gaussian convolution): Proved in the contrib library as stated, on a larger parameter range (all M, alpha, beta; the paper has x &gt;= M, w &lt;= M), with no named input: AiryConj.heatKernel\_conv\_cdf (contrib/Airy1GumbelContrib/AiryKernel/GaussianSaddle.lean). Shown as outside only because coverage rows can name main-package claims alone.

## What the checks establish

- **Every proof is checked by Lean.** The package builds; no `sorry` (an unfinished proof) remains; the only axioms used are `Classical.choice`, `Quot.sound`, `propext` (allowed: `propext`, `Quot.sound`, `Classical.choice`).
- **The statements shown are the ones proved.** For 4 statement(s), a second checker (comparator) confirmed that the proof proves exactly the statement shown, with only the permitted axioms, and independent Lean kernels replayed the proof.
- **Not checked by any tool:** that a Lean statement says what the paper says. That is the comparison this page asks you to make. A definition listed under *Definitions checked by a person* is compared by name and type only.

The full account of what each check covers and what it takes on trust is lean-pkg's [trust model](https://github.com/lean-pkg/lean-pkg/blob/main/docs/trust-model.md).

## How this was checked

- lean-pkg's claims ledger: **ready**, every required claim is closed by the recorded receipts; 4 of 4 required claim(s) verified (`sha256:4e096335d8dfdade…`).
- Build check (`lean-pkg gate`) at commit `8a085b7b2340`: `sorry` count 0; axioms used: `Classical.choice`, `Quot.sound`, `propext`.
- Axioms of every claim: read from the built environment (Lean's `collectAxioms`) for all 141 claim(s) in `claims.yaml`, not only the theorems the build prints; none uses an axiom beyond `propext`, `Quot.sound` and `Classical.choice`.
- Statement comparison (comparator) at commit `8a085b7b2340`: 1 configuration(s), 4 theorem(s) compared (each Challenge statement against its Solution proof); permitted axioms: `Classical.choice`, `Quot.sound`, `propext`; definitions compared by name only: none.

### Receipts

| Receipt | Check | Commit | Date | Job | SHA-256 |
|---|---|---|---|---|---|
| `.lean-receipts/19901ea8b3fe-systemd-user-airy1-gumbel-lean-verify.service-0ebf95d044bb440482efe94120401c18-h-f985343177f7.json` | build | `19901ea8b3fe` | 2026-11-20 | — | `1a6c1ec5f03436f64683563735165e027679053e90a2a5bb3a74822eee8dc9c1` |
| `.lean-receipts/33d81943f406-comparator.json` | statement comparison | `33d81943f406` | 2026-11-21 | — | `2bea2d74fd5abf27ffc211e56e7497faefab88db9d08d2a38a48b874e45d6b0f` |
| `.lean-receipts/33d81943f406-systemd-user-airy1-v040-main-verify.service-80fdf618b1ee4191a2783cb37149f438-h-f985343177f7.json` | build | `33d81943f406` | 2026-11-21 | — | `5e281770ca82b443ed37f1cb445793a83f97f72ef258aeb18f2f047544d560ad` |
| `.lean-receipts/41052c21e6fc-comparator.json` | statement comparison | `41052c21e6fc` | 2026-11-24 | — | `0e6f48ba28b79ef6c0deaf1bff73872fd4d6905c83b150153e27a5777c54a621` |
| `.lean-receipts/41052c21e6fc-systemd-user-airy1-v090-main-verify.service-48b291d9d44c4842a48547569ce2fda5-h-f985343177f7.json` | build | `41052c21e6fc` | 2026-11-24 | — | `788a1c58b41dea138a03aff364ccbc00253ec84b7dbb06043fd75ac5c9631eca` |
| `.lean-receipts/635255c979a4-comparator.json` | statement comparison | `635255c979a4` | 2026-11-23 | — | `e4cdf78392ae1c0c1e17be16171bee964439f0a66cebebb49a5b6a77f00375ab` |
| `.lean-receipts/635255c979a4-systemd-user-airy1-v080-main-verify.service-57defb604ee64d819a6eb4545c3996a2-h-f985343177f7.json` | build | `635255c979a4` | 2026-11-23 | — | `adf6892644ea54c352e26d2ff69a58b8e82bcec7044a4b5e418e3a9a4acaefbd` |
| `.lean-receipts/66ac891274b1-comparator.json` | statement comparison | `66ac891274b1` | 2026-11-20 | — | `abbb43a25d904bf50477fa50d267124fef4060f81a8ed0a52dbf57a4fe9da459` |
| `.lean-receipts/66ac891274b1-systemd-user-airy1-v020-main-verify.service-37bfacd30061492d8a7d92f9d1677d7e-h-f985343177f7.json` | build | `66ac891274b1` | 2026-11-20 | — | `423df7f9a678774ad470a0c55c740300cc849185a82f4d38d81e842909c82a35` |
| `.lean-receipts/70a76a23b572-comparator.json` | statement comparison | `70a76a23b572` | 2026-11-21 | — | `dbbeff55269eddf9acda3beceaee40da73ef1eba4aa467256cc354e9ee842d6d` |
| `.lean-receipts/70a76a23b572-systemd-user-airy1-v050-main-verify.service-a1a00e13c43a4ad68f1667d7d6c05465-h-f985343177f7.json` | build | `70a76a23b572` | 2026-11-21 | — | `139256c0a3b31b718dc225b0a6f24d9e5c3515624f402c308efc5d25cc11edd3` |
| `.lean-receipts/7f29283339cf-comparator.json` | statement comparison | `7f29283339cf` | 2026-11-22 | — | `fd50502e5c0448b54c937946ddd018151f8c5a85487bf3a7b85142face1fe55c` |
| `.lean-receipts/7f29283339cf-systemd-user-airy1-v070-main-verify.service-0e4600441f8b40dca9e6260da82499f3-h-f985343177f7.json` | build | `7f29283339cf` | 2026-11-22 | — | `c4d4f03701a3f84381328881855bf648e7c4a2c2ebf2968edf2e857d0e6696e6` |
| `.lean-receipts/8a085b7b2340-comparator.json` (used here) | statement comparison | `8a085b7b2340` | 2026-11-24 | — | `e73bf2bb34afc51e023c4f43cc3cb7c19e04f95993d9b7ce67e72ec165a176b8` |
| `.lean-receipts/8a085b7b2340-systemd-user-airy1-v090b-main-verify.service-9e758a227b0b409598e0926d91e1f56b-h-f985343177f7.json` (used here) | build | `8a085b7b2340` | 2026-11-24 | — | `0d324be53d5421377ad7475a99cb6d083d189a124db559ff58b77300c445dc2e` |
| `.lean-receipts/962a984bcc36-comparator.json` | statement comparison | `962a984bcc36` | 2026-11-20 | — | `84b03ae346317b204f921def1b546e9fa621b35aae433cc6af96926e82f5d72b` |
| `.lean-receipts/962a984bcc36-systemd-user-airy1-v031-main-verify.service-58730a798b4d4c3988e32f986ef518ae-h-f985343177f7.json` | build | `962a984bcc36` | 2026-11-20 | — | `8bf0409b4c3da4429ecce5e8fa25ca1b0580a0f1586a7265f2b6ebb62b583cf7` |
| `.lean-receipts/97a2322cf1b6-comparator.json` | statement comparison | `97a2322cf1b6` | 2026-11-21 | — | `d4f1f068b83b33e08acbe248f982749c1b8506f875193f38b958e73d8a088c81` |
| `.lean-receipts/97a2322cf1b6-systemd-user-airy1-v060-main-verify.service-7f44fe5dbd3b4f70b51c7f439a3fedae-h-f985343177f7.json` | build | `97a2322cf1b6` | 2026-11-21 | — | `97ec777ea2ffb67a20cfdbe2a68a0fb1218202e6f594bc0eace78479ffeece44` |
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
git checkout 8a085b7b234001112fb3a919cf5b6b246233d5fb   # the commit the build check binds
lake exe cache get
lake build
```

Expected: `#print axioms` on any declaration above reports a subset of {`Classical.choice`, `Quot.sound`, `propext`} (the union the build check records); `sorryAx` never appears.

## Citation

Le Chen. *airy1-gumbel-lean: Lean companion to Gumbel fluctuations of the maximum of the Airy\_1 process*. Version 0.9.0. [doi:10.5281/zenodo.24398888](https://doi.org/10.5281/zenodo.24398888).

It formalizes results of *Gumbel Fluctuations of the Maximum of the Airy\_1 Process*, [arXiv:2611.23658v1](https://arxiv.org/abs/2611.23658v1). See [CITATION.cff](CITATION.cff).

## License

Released under `Apache-2.0`; see [LICENSE](LICENSE).

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).

<!-- lean-pkg:page:end -->
