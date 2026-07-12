# What still needs formalizing — assessment against `typeD_decoupling-draft-rev3.tex`

This note answers the question "does anything in the new draft still need to be
formalized in Lean?" It compares the new draft `typeD_decoupling-draft-rev3.tex`
against the current Lean development. It does **not** modify any proof or statement.

## 1. rev3 vs. the previously-formalized rev2: no new mathematical targets

Diffing `typeD_decoupling-draft-rev2.tex` against `typeD_decoupling-draft-rev3.tex`
shows that **no new theorem, proposition, lemma, corollary, or conjecture was added**.
The numbered-result labels are identical between the two drafts. The rev3 changes are:

- new title / author / date, a rewritten abstract and introduction, an accessibility
  statement, a "Generative AI statement", and acknowledgements;
- a much larger bibliography (many multi-species / KPZ references added);
- cosmetic markup changes (`\emph{...}` → `\underline{...}`, a couple of typo-level
  edits such as "Corollart"/"Corollary");
- **one new display**: the explicit finite-`n` rate matrix `eq:nrates` with the
  parameters `eq:nparams` (`\beta_n`, `\sigma_n`). This is a *definition* of the model
  at finite `n`, reproduced from `[REU, §2.1]`, not a proof target.

So the list of results to formalize is unchanged from the version already worked on.

### Optional: the finite-`n` generator `eq:nrates`
The Lean model is written at `n=∞` (the rates `eq:rates`). The new `eq:nrates`
display is not encoded in Lean. Nothing in the paper's theorems depends on having it in
Lean — `prop:decouple` (current decoupling) is already proved, and the paper's own
statement of it is "valid at every `n`" via a time change. If desired one could add the
finite-`n` generator as a definition and re-derive `prop:decouple` at finite `n`, but
this is optional polish, not a gap in any theorem.

## 2. Current Lean status (verified: the project builds)

The whole project compiles (`lake build` succeeds). Axiom checks (`#print axioms`) were
used to classify each result as **genuinely proved** (only `propext`,
`Classical.choice`, `Quot.sound`) versus **still resting on a `sorry`**.

### 2a. Fully proved, no `sorry` (standard axioms only)
- **Tiers 1–2, all of `TypeDDecoupling.lean`**: local detailed balance (`lem:db`),
  vanishing cross-coefficients (`prop:cross`), flux/current decoupling
  (`prop:decouple`, `current_decoupling`), Price–Sheppard (`lem:price`), the crossover
  correlation closed form `ρ(c)=(1−e^{−4c})/(4c)` with all its limits/monotonicity/tail
  (`thm:closed`), the Bessel–Struve positive-part correlation including the literal
  `I₀`/`L₀` form (`prop:struve`), the `q`-Laplace contact-representation identities
  (`thm:cov`: `qmom_contact`/`qcov_contact`), and the triangular step-sector duality
  identities (`lem:tridual`).
- **Structural / assembly theorems proved conditionally on their cited inputs**
  (they take the cited results as hypotheses and are sorry-free):
  `thm:dual`, `cor:tri`, `lem:acr`, `prop:orth` (q-Krawtchouk self-duality framework);
  `prop:sym`; `thm:kernel` (two-particle dual kernel bound); `lem:occ` (occupation
  half), `lem:rebind`, `prop:occ`; and `thm:marg` (Tracy–Widom marginals of each
  species' current, derived from the cited single-species step-ASEP Tracy–Widom input
  via `prop:decouple`).

### 2b. Stated but still resting on a `sorry` (i.e. these still need formalizing)
These are the remaining `sorry` leaves. Two kinds:

**(i) Classical results the paper cites rather than proves** — legitimately assumable,
but currently unproven in Lean because the needed general theory is absent from Mathlib:
- `lem:KR` — Kolmogorov–Rogozin anti-concentration (Petrov).
- `thm:karamata` — Karamata's Tauberian theorem (BGT / Feller). `lem:tau` is proved
  *from* it, so `lem:tau` also currently inherits this `sorry`.
- `lem:dynkin`, `thm:mp` — Dynkin decomposition / martingale problem (Kipnis–Landim,
  Holley–Stroock).
- `thm:mitoma`, `prop:aldous` — Mitoma's criterion and Aldous tightness.
- the single-species step-ASEP input behind `lem:asep` (steepest-descent decay
  `asepGreen_integral_decay`, following Schütz / Tracy–Widom); `lem:asep` inherits it.
- SPDE / Schwartz-distribution-valued process objects and the GUE/`F₂` Tracy–Widom
  machinery are rendered by `opaque` placeholders because they do not exist in Mathlib.

**(ii) The paper's own proofs not yet formalized** — these are genuine paper content
left as `sorry`:
- Local CLTs for the dual coordinates (§lclt): `lem:free`, `lem:Rlclt`, `lem:Slclt`.
- Edwards–Wilkinson cross-noise toolkit: `lem:orth`, `lem:eqvar`, `lem:sector`,
  `lem:eps`, `prop:conc`, `lem:gauss`, `prop:drift`.
- Two-phase functional CLT and the duality bridge: `prop:twophase`
  (+ `prop:twophase_mixture`) and `lem:crossbridge`.
- The two main assembly theorems `thm:ewmain` (decoupled EW SPDE limit) and `thm:cross`
  (regime-A crossover) have sorry-free proof bodies but transitively depend on the
  leaves above, so they still carry `sorryAx` until those are filled.

**(iii) Open conjecture (not a proof target)**
- `conj:cov` — `Corr(N₁,N₂) ≍ s^{−1/6}`; stated, left as `sorry`, explicitly an open
  conjecture backed only by simulation in the paper.

## 3. Bottom line
- rev3 introduces **no new theorem to formalize** — only exposition, references, and the
  finite-`n` rate display `eq:nrates` (a definition, optional to encode).
- The self-contained algebraic/closed-form core of the paper is **fully proved**, as are
  the duality framework, the kernel-bound assembly, and the Tracy–Widom marginal
  reduction (the last as conditional theorems on cited inputs).
- What remains are the analytic/probabilistic layers listed in 2b: the paper's own local
  CLTs, EW cross-noise toolkit, and two-phase CLT (in reach but needing infrastructure),
  plus the cited classical inputs and out-of-Mathlib objects (Tracy–Widom / SPDE /
  tightness), plus the open conjecture `conj:cov`.
