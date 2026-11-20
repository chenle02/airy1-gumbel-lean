# Changelog

Result numbers are those of arXiv:2611.23658v1.

## 0.2.0

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
