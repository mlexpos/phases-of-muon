# Phases of Muon: statements, proofs and formalization

Companion repository for *Phases of Muon: When Muon Eclipses SignSGD*
(E. Paquette, N. Marshall, L. Benigni, G. Wang, A. Agarwala, C. Paquette; NeurIPS 2026).

**Read the proofs online:** https://mlexpos.github.io/phases-of-muon/

The landing page gives the paper's abstract, direct links to the paper and full proof
supplement, and a description of the site's written proofs and Lean formalization.
The [proof explorer](https://mlexpos.github.io/phases-of-muon/results.html) starts from the results that the paper's main text uses. Each one has a page with
its exact statement, the definitions it needs, what it means, and a sketch of its proof.
From there you can open the full proof, and from the proof any lemma it uses. Each opens over
the page you are on, and closing it returns you to where you were. A graph view shows every
statement of the supplement by section and dependency depth.

The [paper–Lean comparison](https://mlexpos.github.io/phases-of-muon/compare.html) places the
dynamical comparison theorem (SE.1 in the supplement, H.1 in the paper) beside its four Lean
statements and the structures containing their assumptions. Hover, click, or use the keyboard
to highlight corresponding phrases and source lines. These are curated clause-level mappings;
the written theorem is unchanged, and every Lean excerpt is verbatim source at the linked,
immutable public revision. Saved selections can be shared through the page's `#match=…` URL.

## Contents

| Path | What it is |
|---|---|
| `docs/` | The static site, served by GitHub Pages from this folder. |
| `docs/paper.pdf` | The paper, with additional related work, numerics, finite-ridge and momentum experiments, followed by the proof overview and sketches. |
| [`docs/phases_of_muon_expanded_arxiv.tar.gz`](docs/phases_of_muon_expanded_arxiv.tar.gz) | Standalone arXiv sources for the expanded paper, with all supporting files and no separate supplement. Verified with TeX Live 2023 and 2025. |
| `docs/supplement.pdf` | The supplementary material: complete statements and proofs (sections SA–SJ), followed by the Lean formalization table. |
| `lean/` | The Lean 4 formalization and its coverage audit. |

Numbers such as Theorem SE.1 or equation (SE.12) refer to the supplement; unprefixed numbers
refer to the paper.

## Formal verification

The statements and proofs of the supplement were formalized in Lean 4 with Mathlib. The Lean
sources are in `lean/`; the shared probability and random-matrix libraries they use are at
https://github.com/mlexpos/alea-foundations.
The four standard Gaussian inputs are proved there and supplied to the Muon interfaces by
`lean/Muon/External/Discharge.lean`; they are included in the 345 proved formal targets.

To build the formalization after cloning both public repositories:

```sh
cd lean
lake update
lake exe cache get
lake build
```

## Citation

```bibtex
@inproceedings{paquette2026phases,
  title     = {Phases of {Muon}: When {Muon} Eclipses {SignSGD}},
  author    = {Paquette, Elliot and Marshall, Noah and Benigni, Lucas and Wang, Guangyuan and Agarwala, Atish and Paquette, Courtney},
  booktitle = {Advances in Neural Information Processing Systems},
  year      = {2026}
}
```
