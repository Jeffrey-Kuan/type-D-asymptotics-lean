import Mathlib
import TypeDDecoupling
import TypeDDecouplingLCLT
import TypeDDecouplingCrossover
import TypeDDecouplingDuality
import TypeDDecouplingEW
import TypeDDecouplingTracyWidom
import TypeDDecouplingDualPairWitness

/-!
# Tiers 3–4 of the type D ASEP formalization: black boxes and the proofs that use them

This module aggregates all tier-3 and tier-4 results of
`typeD_decoupling-draft-rev2.tex` — the random-walk local CLTs and occupation bounds, the
q-Krawtchouk self-duality framework, the two-particle dual kernel bounds, the
two-phase functional CLT and regime-A crossover, the decoupled Edwards–Wilkinson SPDE
limit with its martingale-problem inputs, and the Tracy–Widom marginals and the open
linear-covariance conjecture.

The genuinely *cited / previously-known* results are taken as a **black box**: each is
stated as faithfully as the current Mathlib allows and left as `sorry` (no `axiom`s are
introduced; the `sorry`s mark exactly the literature inputs the paper invokes).

The **paper-level derivations that *use* those black boxes** are, by contrast,
**formalized and proved here** (no `sorry`), taking the cited inputs as hypotheses:

* `thm:dual`, `cor:tri` — global generator self-duality from the bondwise two-site
  interlacing (the computer-algebra input);
* `prop:orth` — two-species orthogonality from the single-species q-Krawtchouk
  orthogonalities (CFG20), by Fubini over the product measure;
* `lem:acr` — the duality-covariance identity from orthogonality and the duality
  expansion (with its `L¹`/Fubini regularity);
* `prop:sym` — current orthogonal to the bound-pair mode, from the product
  (independence) structure of the blocking measure;
* `lem:occ` (occupation half) and `lem:rebind` — the `O(√T)` occupation bound and the
  `O(c/√T)→0` re-binding bound, by integrating the cited on-diagonal heat-kernel bound;
* `thm:marg` — Tracy–Widom marginals of each species' current, from the cited
  single-species step-ASEP Tracy–Widom input (BCS) via the `prop:decouple` reduction.

See the individual files for per-result documentation:

* `TypeDDecouplingLCLT.lean` — `lem:free`, `lem:Rlclt`, `lem:KR`, `lem:Slclt`,
  `thm:karamata`, `lem:tau`, `lem:occ` (occupation half), `lem:rebind`, `lem:asep`,
  `thm:kernel`, `prop:occ`.
* `TypeDDecouplingCrossover.lean` — `prop:twophase`, `lem:crossbridge`, `thm:cross`.
* `TypeDDecouplingDualPairWitness.lean` — satisfiability witness for the dual-pair model
  `IsDualPairRescaling` (so the crossover statements are not vacuous).
* `TypeDDecouplingDuality.lean` — `thm:dual`, `cor:tri`, `lem:acr`, `prop:orth`.
* `TypeDDecouplingEW.lean` — `lem:dynkin`, `thm:mp`, `thm:mitoma`, `prop:aldous`,
  `thm:ewmain`, `lem:gauss`, `lem:orth`, `lem:eqvar`, `lem:sector`, `lem:eps`,
  `prop:conc`, `prop:sym`, `prop:drift`.
* `TypeDDecouplingTracyWidom.lean` — `thm:marg`, `conj:cov`.

The remaining `sorry`s are exactly the cited classical inputs (`lem:free`, `lem:Rlclt`,
`lem:KR`, `lem:Slclt`, `thm:karamata`, `lem:tau`, `lem:asep`, `thm:kernel`, `prop:occ`;
`prop:twophase`, `lem:crossbridge`; `lem:dynkin`, `thm:mp`, `thm:mitoma`,
`prop:aldous`, `thm:ewmain`, `lem:gauss`, `prop:drift`, and the abstractly-rendered
`lem:orth`/`lem:eqvar`/`lem:sector`/`lem:eps`/`prop:conc`) together with the open
conjecture `conj:cov` — i.e. the literature black boxes and the objects (SPDE /
Tracy–Widom / Skorokhod-space) absent from current Mathlib, not the paper's own
derivations.

The elementary / closed-form results of tiers 1–2 are proved (no `sorry`) in
`TypeDDecoupling.lean`.
-/
