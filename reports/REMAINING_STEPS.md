# What remains to be formalized in Lean

This document answers the question "what other steps need to be formalized?" by
laying out the full claim list of `typeD_decoupling-draft-rev2.tex`, marking what is
already done in `RequestProject/TypeDDecoupling.lean`, and grouping everything else by
how realistic it is to formalize with the current Mathlib.

The file currently builds with **no `sorry`** and only the standard axioms.

> **Status update.** Tiers 1 and 2 below are now **complete**: every elementary /
> closed-form claim of the paper that needs no missing probabilistic infrastructure
> has a proven Lean theorem in `TypeDDecoupling.lean`, building with no `sorry` and only
> the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The literal
> `eq:qmom`/`eq:qcov` contact-representation identities of `thm:cov` were the last
> elementary pieces and are now formalized as `qmom_contact` and `qcov_contact`. What
> remains is tiers 3-4 (the heavy probabilistic-analysis and Tracy-Widom/SPDE layers).

---

## 0. Already formalized and fully proved

These are the self-contained closed-form / algebraic / analytic claims:

- **`lem:db`** — local detailed balance for the product blocking measure
  (`siteWeight`, `twoPtWeight`, `twoPtWeight_zero_three/one_two/two_one`).
- **`prop:cross`** — vanishing cross-mobility and cross-compressibility
  (`crossMobility_eq_zero`, `crossCompressibility_eq_zero`).
- **`prop:decouple`(b)** — diagonal hydrodynamic flux Hessian
  (`flux`, `flux_cross_deriv`, `flux_cross_deriv2`).
- **`lem:price`** (both equalities) — Price's theorem + Sheppard's orthant formula
  (`orthantProb_eq`, `positivePartCov_eq`, `positivePartCov_hasDerivAt`,
  `price_sheppard`).
- **`thm:closed`** — crossover correlation `ρ(c) = (1-e^{-4c})/(4c)`, with range,
  monotonicity, `c→0` and `c→∞` limits, `1/(4c)` tail, and the mixing integral
  `∫₀¹ e^{-4ct} dt = ρ(c)` (`rhoCorr_*`, `integral_exp_eq_rhoCorr`).
- **`prop:struve`** (analytic content) — the positive-part correlation in its
  equivalent **integral form** `rhoStruve`, with range `(0,1)`, `c→0` limit `1`, and
  `π/(8(π-1)c)` tail (`rhoStruveNum`, `rhoStruve_*`).
- The algebraic bridge **`corr_sum_diff`** behind `thm:closed`.

---

## 1. The one step you already identified: the literal `I₀`/`L₀` form of `prop:struve`

The proposition is already proved in integral form. To state it *literally* as in the
paper,
`Corr(G₁⁺,G₂⁺) = π/(8(π-1)c)·[1 - 2e^{-4c} + I₀(4c) - L₀(4c)]`,
you need to:

1. **Define `I₀` and `L₀`** as their power series (both entire; `I₀` is just
   `Σ (z/2)^{2m}/(m!)²`, needing only factorials — no Gamma).
2. **Prove the single integral identity (DLMF 11.5.2)**
   `∫₀^{π/2} e^{-4c·sinθ} dθ = (π/2)(I₀(4c) - L₀(4c))`,
   then combine it with an integration-by-parts of the already-formalized
   `rhoStruveNum`. This is exactly the "write an integral and manually check it
   reduces to `I₀`/`L₀`" step.

This is self-contained and Mathlib-mergeable; it needs nothing that is missing from
Mathlib. See `BESSEL_STRUVE_ASSESSMENT.md` for the construction.

**DONE.** `besselI0`/`struveL0` are defined by their power series, DLMF 11.5.2 is proved
as `integral_exp_neg_mul_sin_eq`, and the literal closed form is
`rhoStruveNum_bessel_struve` / `rhoStruve_bessel_struve`.

---

## 2. Tractable now — algebraic / elementary-analytic, no missing infrastructure

These close out the *Regime-A closed-form story* (the `thm:closed`/`prop:struve`
correlations as genuine limits) at the elementary level, and can be done with the
current Mathlib. **All of the items below are now DONE** (lemma names in parentheses):

- **`lem:occ` (symmetry half, `eq:symm`)** — `E[R(t)]=0` and `Cov(S(t),R(t))=0` from the
  species-interchange symmetry `R↦-R`, `S↦S`.
  **DONE** (`occ_symmetry`, with `occ_mean_eq`, `occ_var_eq`).
  *(The companion occupation bound `Λ_T = O(√T)` is in tier 3.)*
- **`lem:split` (limit facts)** — split time `τ ~ Exp(2q²ε)`, `ν_sp·T → 4c`,
  `P(τ>T) → e^{-4c}`, `U = min(τ/T,1) ⇒ min(Exp(4c),1)`.
  **DONE** (`splitRate_mul_tendsto`, `split_survival_tendsto`, `split_cdf_tendsto`,
  and the mixture-mean bridge `expMin_mean_eq_rhoCorr`).
- **`thm:cov` / `eq:qcov` contact representation** — the literal per-sample
  contact-representation identities `eq:qmom`/`eq:qcov`.
  **DONE** at the elementary level (`q_telescope`, `q_telescope_sum`, the literal
  `qmom_contact`/`qcov_contact`, the product expansion `q_cov_product_expansion`, the
  covariance shift `cov_one_sub_one_sub`, and the `[0,1]`-valued bound
  `covariance_abs_le_min_integral`). *(Identifying the contact weights with genuine
  two-particle hitting probabilities `P_{(a,b)}(…)` — the duality identities
  `eq:tri1`/`eq:tri2` and absolute convergence of the infinite sums — is tier 3.)*
- **`lem:tridual`** — triangular (Schütz-type) step-sector duality identities.
  **DONE** (`stepConfig`, `NplusStep`, `step_telescope`, `NplusStep_eq_zero_of_pos`,
  `NplusStep_succ_of_nonpos`, `step_contact_exponent_zero`, `step_qweight_eq_one`,
  `step_dual_weight_collapse`).
- **`prop:decouple`(a)** — the exact current-decoupling identity (companion to the
  already-done flux part (b)).
  **DONE** (`current_decoupling`).

---

## 3. Hard but possibly in reach — needs new probabilistic infrastructure built first

These require building machinery that is currently absent or thin in Mathlib, so each
is a sizable sub-project on its own:

- **`lem:rebind`** — expected merges in `[τ,T]` is `O(c/√T)`. Needs random-walk
  occupation bounds.
- **`lem:occ` (occupation half)** — `E[Λ_T | A_T] = O(√T)` for the adjacent-set
  occupation. Same local-CLT/occupation machinery.
- **`lem:free`, `lem:Rlclt`, `lem:Slclt`, `lem:KR`** — the local CLTs for the dual
  coordinates (§lclt). Local central limit theorems for these walks are not in Mathlib.
- **`thm:karamata` + `lem:tau`** — Karamata Tauberian theorem and the occupation-time
  asymptotics it powers. Some Tauberian theory exists in Mathlib, but not this form.
- **`prop:twophase`** — the two-phase convergence of the dual pair to the bivariate
  normal mixture with `U = min(Exp(4c),1)`. Needs a (multivariate) CLT plus the split
  analysis; this is the analytic heart connecting the model to `thm:closed`.
- **`lem:crossbridge`** — the duality identity tying the species' `q`-Laplace
  observable to a dual hitting probability. Needs the q-Krawtchouk self-duality
  framework (`thm:dual`, `cor:tri`, `prop:orth`, `lem:acr`) formalized first.
- **`thm:cross`** — assembles `prop:twophase` + `thm:closed` + `lem:crossbridge`.

---

## 4. Out of reach without major foundational builds in Mathlib

These rest on theory that does not exist in Mathlib today; formalizing them would be
multi-month foundational efforts:

- **`thm:marg`** — Tracy–Widom (GUE, `F₂`) marginals for each species' current. No
  GUE / `F₂` / Airy / Fredholm-determinant asymptotics in Mathlib.
- **`thm:ewmain`** — the functional CLT: convergence of the density fields to a linear
  stochastic heat / Edwards–Wilkinson SPDE with no cross-coupling. Needs
  distribution-valued (Schwartz) processes and SPDE limit theory.
- **Tightness / martingale toolkit** — `lem:dynkin`, `thm:mp` (martingale problem),
  `thm:mitoma` (Mitoma's criterion), `prop:aldous` (Aldous tightness),
  `thm:kernel` (two-particle dual kernel bound), and the supporting
  `lem:gauss`/`lem:orth`/`lem:eqvar`/`lem:sector`/`lem:eps`/`prop:conc`/`prop:sym`/`prop:drift`.
- **`lem:asep`** — the classical single-species WASEP/KPZ input the EW theorem is stated
  modulo; classical in the literature but not in Mathlib.
- **`conj:cov`** — open conjecture (`Corr(N₁,N₂) ≍ s^{-1/6}`); not a proof target.

---

## Suggested order

1. **`I₀`/`L₀` + DLMF 11.5.2** → upgrade `prop:struve` to its literal closed form
   (the step you flagged; self-contained).
2. **`lem:occ` symmetry identities** and **`lem:split` limits** → elementary, finish the
   closed-form story's easy pieces.
3. **`thm:cov` / `lem:tridual` / `prop:decouple`(a)** → the combinatorial-duality
   identities of Regime B.
4. Only then consider the tier-3 CLT/local-CLT infrastructure, and treat tier 4 as
   long-horizon Mathlib contributions.

---

## Update: tiers 3–4 now stated as black-box (assumed) Lean statements

At the user's request, every tier-3 and tier-4 result is now **stated** in Lean, taking
the truth of the cited / previously-known results as a black box.  Each is a `theorem`
left as an intentional `sorry` (no `axiom`s are introduced), with a docstring marking it as
a cited/assumed result and pointing to the paper label.  Where it is honest to do so, the
*derived* results are phrased as true conditionals on their cited inputs (e.g. `thm:marg`
from the single-species BCS Tracy–Widom input; `thm:dual`/`cor:tri` as bondwise ⟹ global
interlacing; `prop:orth` as the product of single-species orthogonalities), and the
classical inputs are stated with their genuine hypotheses (e.g. `lem:free` via a
`DriftlessReversibleWalk` structure, `lem:KR`, `thm:karamata`).  The SPDE / Tracy–Widom
objects absent from Mathlib are rendered schematically by abstract types and predicates.

Files (all build with `lake build`, only intentional `sorry`s):

- `TypeDDecouplingLCLT.lean` — `lem:free`, `lem:Rlclt`, `lem:KR`, `lem:Slclt`,
  `thm:karamata`, `lem:tau`, `lem:occ` (occupation half), `lem:rebind`, `lem:asep`,
  `thm:kernel`, `prop:occ`.
- `TypeDDecouplingCrossover.lean` — `prop:twophase`, `lem:crossbridge`, `thm:cross`.
- `TypeDDecouplingDuality.lean` — `thm:dual`, `cor:tri`, `lem:acr`, `prop:orth`.
- `TypeDDecouplingEW.lean` — `lem:dynkin`, `thm:mp`, `thm:mitoma`, `prop:aldous`,
  `thm:ewmain`, `lem:gauss`, `lem:orth`, `lem:eqvar`, `lem:sector`, `lem:eps`,
  `prop:conc`, `prop:sym`, `prop:drift`.
- `TypeDDecouplingTracyWidom.lean` — `thm:marg`, `conj:cov` (the latter an open conjecture).
- `TypeDDecouplingTiers34.lean` — aggregator importing all of the above.

Tiers 1–2 remain fully proved (no `sorry`) in `TypeDDecoupling.lean`.
