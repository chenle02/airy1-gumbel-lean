# Notice

Copyright 2026 Le Chen. Licensed under the Apache License, Version 2.0
(see `LICENSE`).

- **Source.** The Lean files were written for this project. Parts of
  `contrib/Airy1GumbelContrib/FredholmDet/Hadamard.lean` and
  `contrib/Airy1GumbelContrib/FredholmDet/EntireDet.lean` closely paraphrase
  [rmt-foundations-lean](https://github.com/chenle02/rmt-foundations-lean)
  (Apache-2.0, by the same author) at revision
  `af3b6edb57330747982dba2e2565d102a56613cb`, as credited in those files;
  nothing is imported from it.
- **Research authorship.** The mathematics is from the paper by Le Chen and
  Fei Pu cited in `README.md`. Results of other authors used by the paper
  and by the Lean proof are credited there and in the Lean docstrings.
- **Dependencies.** Lean 4 and Mathlib (Apache-2.0), and
  [brownian-motion](https://github.com/RemyDegenne/brownian-motion)
  (Apache-2.0), with their transitive dependencies as pinned in
  `lake-manifest.json`, each under its own license.
- **Tools.** AI coding assistants helped write the code and documentation.
  Lean's kernel checked the proofs. Le Chen is responsible for the
  statements and their correspondence to the paper.
