# Changelog

Result numbers are those of arXiv:2611.23658v1.

## 0.5.0

- Lemma 4.2 (the threshold-sensitive Newman bound, eq. (4.3)) is now proved for the
  constructed continuous Airy₁ process: `Airy1Gumbel.tail_sensitive_newman_airy1` in
  `Airy1Gumbel/TailSensitiveNewman.lean`. There are `C > 0` and `u₀` such that, for every
  `u ≥ u₀` and every lag `d ≥ 0`,
  `ℙ{Ã(0) > u, Ã(d) > u} ≤ C ℙ{Ã(0) > u}² + C u Cov(Ã(0), Ã(d))`; the constants do not
  depend on `d`.
- Inputs: the standing inputs `Airy1FddPositive` and `GOELeftTail`, and the association
  input `ProcessAssociated`: the association of the Airy₁ process (Pu 2025, Theorem 1.2),
  for bounded, monotone, measurable test functions of finitely many coordinates.
  `ProcessAssociated` is an existing named input, assumed, not proved; until this release
  only the earlier association-route headline `_final` and its intermediate forms used it,
  and it is now also used by Lemma 4.2. `GOELeftTail` is not a hypothesis of the paper's
  Lemma 4.2. No new named input: the one-point tail ratio
  `ℙ{Ã(0) > u − u^{−1/2}} ≤ K ℙ{Ã(0) > u}`, which the paper takes from a density bound,
  is proved here from the GOE Fredholm determinant (`one_point_tail_shift_le_airy1`,
  `one_point_tail_profile_bounds_airy1`, `goe_singleton_right_tail_sub_profile_isLittleO`,
  `trace_goeOp_eq_half_integral`).
- The covariance in (4.3) is a genuine one: every time marginal is proved
  square-integrable (`memLp_two_airy1ContR`).
- No existing statement or proof changed. The headline theorem still uses exactly its
  three inputs and does not use `ProcessAssociated`; the comparator statements are the
  same. Six claims are appended to `claims.yaml`, all `internal` (built, not compared).
  `coverage.yaml`: the Lemma 4.2 row moves from outside to inputs supplied, with
  `ProcessAssociated` named on the row as an assumption.
- The contrib package `airy1-gumbel-lean-contrib` is unchanged; its version stays 0.4.0
  and its v0.4.0 receipts still bind.

## 0.4.0

Zenodo: version DOI [10.5281/zenodo.24410662](https://doi.org/10.5281/zenodo.24410662); concept DOI [10.5281/zenodo.24398888](https://doi.org/10.5281/zenodo.24398888).

- Lemma 4.1 (the block modulus, eq. (4.1)) is now proved for the constructed Airy₁
  process under `Airy1FddPositive`, `GOELeftTail` and a new, fourth named input:
  `Airy1Gumbel.block_modulus_airy1` in `Airy1Gumbel/BlockModulus.lean`. For some
  `C, c, h₀ > 0` and every `0 < δ ≤ h₀`, the probability that `|Ã(x) − Ã(y)| > 1` for
  some `x, y ∈ [0, 1]` with `|x − y| ≤ 2δ` is at most `C δ⁻¹ e^{−c δ^{−1/2}}`.
- This is the first release that adds a named input. The new input,
  `Airy1Gumbel.NonnegativeWindowModulusEstimate`, is the transferred local oscillation
  bound (4.2) of arXiv:2611.23658v1 on windows inside `[0, ∞)`: there are `C₀, c₀ > 0`
  such that, for all sufficiently large `ℓ`, every radius `0 < s ≤ 1` and every centre
  `c ≥ s`, the probability that `|Ã(t₁) − Ã(t₂)| > C₀ ℓ √s` for some
  `t₁, t₂ ∈ [c − s, c + s]` is at most `C₀ e^{−c₀ ℓ}`. The paper derives it from
  Basu–Bhattacharjee (2024, arXiv 2406.11826, Lemma 5.1 with Theorem 1.4); here it is
  assumed, not proved. It is not a verbatim Basu–Bhattacharjee statement. Two audit
  theorems show that it is neither vacuous nor trivially true: the zero process satisfies
  it (`nonnegativeWindowModulusEstimate_const`) and the process `t²` violates it
  (`isEmpty_nonnegativeWindowModulusEstimate_sq`). The earlier record
  `LocalModulusEstimate` is unchanged.
- No existing statement or proof changed. The headline theorem still uses exactly its
  three inputs and does not use the new one; the comparator statements of both packages
  are the same. Four claims are appended to `claims.yaml`, all `internal` (built, not
  compared). `coverage.yaml`: the Lemma 4.1 row moves from outside to inputs supplied,
  with the new input named on the row.

## 0.3.1

Zenodo: version DOI [10.5281/zenodo.24408134](https://doi.org/10.5281/zenodo.24408134); concept DOI [10.5281/zenodo.24398888](https://doi.org/10.5281/zenodo.24398888).

- Comparator tier for the contrib package `airy1-gumbel-lean-contrib`: every one of the 103
  theorem claims of `contrib/claims.yaml` is now compared (`contrib/comparator.json`, 103
  theorem names `Airy1GumbelLeanContribAudit.<decl>`, no definition holes, permitted axioms
  `propext`, `Quot.sound`, `Classical.choice`). The Challenge (`contrib/Comparator/Challenge.lean`)
  states each claimed theorem with proof `sorry`: 76 statements are the elaborated types as Lean
  prints them (exact under lean-pkg's round-trip check) and 27 are the declarations' own source
  statements in the scope context of their files. The definitions the statements use come from
  `contrib/Comparator/Defs`, a verbatim copy of the library (only its imports are redirected to
  the copies); the Solution proves each statement by the copied library theorem, and neither
  imports the library. `contrib/scripts/comparator/CheckFidelity.lean` checks with `Expr`
  equality that the 4238 copied constants equal the library's and that each of the 103
  Challenge statements equals the claimed declaration's type; a planted mutation (a copied
  definition body wrapped in `id`, a Challenge numeral `2` changed to `3`) is reported.
- No statement and no proof changed. The headline theorem, its three inputs, the main
  package's comparator statements and the claims of both packages are the same; the 103
  contrib theorem claims keep the status `internal` (now judged by the comparator).

## 0.3.0

Zenodo: version DOI [10.5281/zenodo.24405700](https://doi.org/10.5281/zenodo.24405700); concept DOI [10.5281/zenodo.24398888](https://doi.org/10.5281/zenodo.24398888).

- Lemma 3.1 (the two-interval determinant formula) is now proved for the constructed
  Airy₁ process for two intervals of any equal length `T > 0`, under `Airy1FddPositive`
  and `GOELeftTail`: `Airy1Gumbel.airy1Law_two_blocks_le_eq_fredholmDet_of_length`, for
  `T > 0`, `r > 0`, `M > 0`, `x ≥ 0` and any weight `a ≥ 2T + r + 1`. The statement is
  the trace-class form (3.3) of Remark 3.2, `det(I − K̃∪)` with the conjugated kernel of
  (3.2); the determinant displayed in (3.1) has no separate Lean definition. Versions
  0.1.0 and 0.2.0 had the law for two unit intervals only.
- New results on the way, in `contrib/Airy1GumbelContrib/Mesh/TwoBlockMesh.lean`: the
  conjugated kernel for equal lengths is square-integrable and its operator is trace
  class (`AiryFdd.memLp_kcupKerT_of_length`, `AiryFdd.isTraceClass_kcupKerT_of_length`),
  it is the unit-interval kernel at `T = 1` (`AiryFdd.kcupKerT_of_length_one`), and the
  dyadic two-interval limit holds at any weight `a ≥ 2T + r + 1`
  (`AiryFdd.tendsto_airy1FinCdf_cupSet_of_length`).
- No statement of version 0.2.0 changed. The unit-interval statements
  (`Airy1Gumbel.airy1Law_two_blocks_le_eq_fredholmDet`,
  `AiryFdd.tendsto_airy1FinCdf_cupSet`) are the same and are now derived from the
  equal-length ones. The headline theorem, its three inputs and the comparator
  statements are the same.
- `coverage.yaml`: the row for Lemma 3.1 is no longer a special case.

## 0.2.0

Zenodo: version DOI [10.5281/zenodo.24403196](https://doi.org/10.5281/zenodo.24403196); concept DOI [10.5281/zenodo.24398888](https://doi.org/10.5281/zenodo.24398888).

- Proposition 1.2 (two-term expansion of the tail of the maximum over a fixed interval)
  is now proved for the constructed Airy₁ process for every length `T > 0`, under
  `Airy1FddPositive` and `GOELeftTail`:
  `Airy1Gumbel.airy1Law_interval_tail_sub_traceLead_isLittleO`. Version 0.1.0 had the
  process-level statement for `T ≥ 1` only.
- New results on the way: the interval hitting law at any weight `a ≥ T + 1` for every
  `T > 0` (`Airy1Gumbel.airy1Law_sup_le_eq_fredholmDet_at_weight`,
  `Airy1Gumbel.airy1Law_sup_le_eq_fredholmDet_at_weight'`) and the dyadic mesh limit at
  any such weight (`AiryFdd.tendsto_airy1FinCdf_meshSet_at_weight`). The statements for
  `T ≥ 1` at weight `2T` are unchanged and are now derived from these.
- No statement of version 0.1.0 changed. The headline theorem, its three inputs and the
  comparator statements are the same.
- Documentation: the overview comment of `Challenge.lean` states the scope of the two
  compared statements more precisely; docstrings in
  `contrib/Airy1GumbelContrib/AiryKernel/TailAsymptotic.lean` cite the arXiv numbering.

## 0.1.0

- First public release: the normalized Gumbel limit of Theorem 1.1 for a constructed
  Airy₁ process with continuous paths, under the three named inputs `Airy1FddPositive`,
  `GOELeftTail` and `CubicStrongMixing`, with the comparator check of the headline.
