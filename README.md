# Phases of Muon: statements, proofs and formalization

Companion repository for *Phases of Muon: When Muon Eclipses SignSGD*
(E. Paquette, N. Marshall, L. Benigni, G. Wang, A. Agarwala, C. Paquette; NeurIPS 2026).

**Read the proofs online:** https://mlexpos.github.io/phases-of-muon/

The site starts from the results that the paper's main text uses. Each one has a page with
its exact statement, the definitions it needs, what it means, and a sketch of its proof.
From there you can open the full proof, and from the proof any lemma it uses. Each opens over
the page you are on, and closing it returns you to where you were. A graph view shows every
statement of the supplement by section and dependency depth.

## Contents

| Path | What it is |
|---|---|
| `docs/` | The static site, served by GitHub Pages from this folder. |
| `docs/paper.pdf` | The paper, with additional related work, numerics, finite-ridge and momentum experiments, followed by the proof overview and sketches. |
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
