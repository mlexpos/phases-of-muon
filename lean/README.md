# Muon Lean package

Lean 4 / Mathlib v4.34.1 (workspace pin; Mathlib at `../../.lake/packages/mathlib`).
Formalizes the appendix of *Phases of Muon* from the frozen camera-ready snapshot
`cr-2026-10-22`. The campaign (protocol, cards, ledger, tooling) lives in
`../phases-of-muon/appendix-nodes/`.

- `Muon.lean` — root; imports every admitted module.
- `coverage.json` — one row per label of the snapshot: declarations, status
  (`planned`, `frozen`, `proved`, `proved-modulo-external`, `out-of-scope`, …),
  certificates, corrections.
- `Audit.lean` + `scripts/verify.py` — full check: snapshot hashes, every module
  reachable from the root, `lake build`, axiom audit of every `Muon` declaration
  (only `propext`, `Classical.choice`, `Quot.sound`; `sorryAx` reported, never in a
  row marked proved), coverage consistency. Run at quiet checkpoints only:

      python3 scripts/verify.py

No axioms are permitted. Cited standard results are explicit hypotheses typed by
`Muon.External` structures (see the campaign's `EXTERNAL-RESULTS.md`).
All four Gaussian interfaces are supplied by the proved terms in
`Muon/External/Discharge.lean`, using the accompanying `gaussian_foundations`
dependency. The campaign's historical `proved-modulo-external` category therefore
records a former integration stage; the paper and website count these results as proved.
