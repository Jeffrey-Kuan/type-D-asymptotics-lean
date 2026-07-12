# Type D ASEP — Lean formalization

Lean 4 formalization accompanying the paper *Correlated and uncorrelated
long-time asymptotics of type D ASEP* (J. Kuan). See §1.5 of the paper for
the precise scope of the formalization and its epistemic conventions
(unconditional results, bundle-conditioned assemblies, citations).

- **Toolchain**: pinned by `lean-toolchain`; Mathlib pinned at `v4.28.0` in `lakefile.toml`.
- **Build**: `lake exe cache get && lake build`.
- **Blueprint**: human-readable map of the formalization with dependency
  graph, built from `blueprint/` by CI and published via GitHub Pages.
- `reports/` — per-task reports from the Aristotle runs (audit trail).
- `briefs/` — the task briefs that specified each formalization campaign.

## Provenance

The Lean proofs were produced by [Aristotle](https://aristotle.harmonic.fun)
(Harmonic AI) from mathematical briefs, and independently audited
(sorry/axiom greps, statement-fidelity review, build verification) as
documented in the paper.

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
