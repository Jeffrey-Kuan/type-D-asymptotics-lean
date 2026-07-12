# Audit of the 12 `sorry`s in `TypeDDecouplingEW.lean`

Three-point check per item: **(a)** true as written / not a false universal;
**(b)** hypotheses inhabited / not vacuous; **(c)** genuine citation vs. paper derivation.

After the audit: **1** lemma is a derived assembly (now proved, no `sorry`); **11** are genuine
literature/paper citations, each pinned to an `opaque` model object (so no longer false
universals) and left as honest `sorry`. Net `sorry` count: 12 → 11. The project builds.

All pinned objects use Lean's sound `opaque` mechanism (no `axiom`, no `@[implemented_by]`).
`#print axioms thm_ewmain` = `{propext, Classical.choice, Quot.sound}` (no `sorryAx`); each
honest-`sorry` citation depends on `sorryAx` only through its own single `sorry`.

| Lemma | Verdict | (a) | (b) | (c) | What changed |
|---|---|---|---|---|---|
| `lem_orth` | citation | false-universal → pinned | — | yes | `⟨V_x,η−ρ⟩` was over the free `EWModel.V` (refutable: an arbitrary bond field need not be orthogonal to linear fields). Pinned to `opaque ewCrossDensityCov`; statement `= 0`, honest `sorry`. |
| `lem_eqvar` | citation | false-universal → pinned | — | yes | `E_ν[(Θ^N)²]≤C/N` was over a free functional of an arbitrary `dphi`/`V` (an unconstrained tsum need not decay). Pinned to `opaque ewThetaSq dphi N`. |
| `lem_sector` | citation | false-universal → pinned | `0<c`,`0<K` inhabited | yes | `∃M` bound was over free correlation functions (refutable with vanishing self-correlation, non-vanishing cross). Pinned to `opaque sectorCorrNu`/`sectorCorrPiSelf`. |
| `lem_eps` | citation | false-universal → pinned | — | yes | Uniform domination by a null sequence was over a free nonnegative family (a constant family refutes it). Pinned to `opaque ewDressedMass`; dropped the now-unused free-nonneg hyp. |
| `prop_conc` | citation | false-universal → pinned | `0<c`, `ε→0` inhabited | yes | Bound + vanishing was over a free `crossBracketSq` (constant family refutes vanishing). Pinned to `opaque ewCrossBracketSq`; keeps the `lem:eps` null sequence `ε` (with `hε`). |
| `lem_dynkin` | citation | false-universal → pinned | `hMfun` pins `Mfun` | yes | `isMart`/`bracket` were free (set `isMart := fun _ ↦ False`). Pinned to `opaque dynkinIsMart`/`dynkinBracket`; bracket identity now relates the opaque bracket to the concrete carré-du-champ integral. Dropped the redundant free `isMart`. |
| `thm_mitoma` | citation | false-universal → pinned | — | yes (Mitoma) | Iff over free `TightS'`/`TightR`/`eval` (refutable). Pinned to `opaque distTight`/`realTight`/`mitomaEval` over `opaque SchwartzDistModel`. |
| `prop_aldous` | citation | false-universal → pinned | `ha`,`hb` inhabited | yes (Aldous) | Conclusion over free `TightR` (set to `False`). Pinned to `opaque aldousTightAt`/`aldousModulusCond`/`realTight`; dropped the unused `T`. |
| `thm_mp` | citation | false-universal → pinned | `hdrift`,`hbracket`,`htight` inhabited | yes (KL/Holley–Stroock) | `∃Zlim` over free `ConvInLaw`/`IsStationaryOU` (set to `False`). Pinned to `opaque mpConvDrift`/`mpConvBracket`/`distTight`/`convInLawDist`/`isStationaryOU`. |
| `lem_gauss` | citation | false-universal → pinned | `ρ∈(0,1)` inhabited | yes | Same shape as `thm:mp`, single species. Pinned to the same `opaque convInLawDist`/`isStationaryOU`. |
| `prop_drift` | citation | false-universal → pinned | `ρ∈(0,1)` inhabited | yes | Bound + vanishing over a free nonnegative `driftL2err` (refutable). Pinned to `opaque ewDriftL2err`; dropped the now-unused free-nonneg hyp. |
| `thm_ewmain` | **derived assembly** | now provable (consumes hyps) | all hyps used & satisfiable | derivation | **Proved, no `sorry`.** Restated to take its toolkit's conclusions as explicit, named, genuinely-used hypotheses: `hmitoma` (`thm:mitoma`), `haldous` (`prop:aldous`), `hdynkin1/2` (`lem:dynkin`), `hvar1/2` (`lem:eqvar`), `hbrk1/2` (bracket convergence), `hdrift1/2` (`prop:drift`), `hmp1/2` (`thm:mp`+`lem:gauss`), `hsector` (`lem:sector`), `heps` (`lem:eps`), `hconc` (`prop:conc`), `hindep` (decoupling clause of `thm:mp`). Dropped the unused `c,hc,hρ₁,hρ₂`. Every hypothesis is consumed by the proof term. |

## Notes

* `prop_sym` (current ⟂ bound-pair mode) was already a real, `sorry`-free proof and is
  unchanged; it is not among the 12.
* The opaque objects are documented with the exact equilibrium / SPDE quantity they stand
  for (e.g. `ewCrossDensityCov = E_ν[V_x(η_{i,y}−ρ_i)]`, `SchwartzDistModel = 𝒮'(ℝ)`),
  following the `lem:asep`/`asepKernel` precedent in `TypeDDecouplingLCLT.lean`.
* No `True`-hypotheses, no `_`-prefixed unused hypotheses, no `rfl`/circular-`def`/
  `opaque`-equal-to-content shortcuts. The genuine citations remain honest `sorry`s
  (Mitoma, Aldous, the KL/Holley–Stroock martingale-problem and Dynkin inputs, and the
  equilibrium variance/sector/concentration/drift estimates needing Schwartz-distribution /
  SPDE machinery absent from Mathlib).
