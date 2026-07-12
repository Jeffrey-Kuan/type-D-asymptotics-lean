# How hard would it be to build Tracy–Widom in Lean / Mathlib?

*An assessment grounded in what Mathlib currently has (checked against the
Mathlib pinned in this project) and what the Tracy–Widom (TW) distribution
actually requires.*

## Short answer

Building the **Tracy–Widom distribution and its main characterizations** in Lean
is a **large, multi-person-year project** — comparable in scope to the largest
analysis projects Mathlib has absorbed (e.g. the prime number theorem, or the
ongoing Fourier/PDE work), and in several places it needs theory that does not
exist anywhere in Mathlib yet. It is *not* a single-PR or single-session task.

The difficulty depends a lot on **which "Tracy–Widom" you mean**, because there
are three standard, provably-equivalent definitions, and they need very
different machinery:

1. **Analytic / Painlevé definition** (TW as a special function):
   `F₂(s) = exp(−∫_s^∞ (x−s) q(x)² dx)` where `q` is the Hastings–McLeod
   solution of Painlevé II `q'' = s·q + 2q³`, `q(s) ~ Ai(s)` as `s→∞`.
   **Most self-contained.** Hard but bounded: weeks–months of focused work.

2. **Fredholm-determinant definition** (TW as an operator determinant):
   `F₂(s) = det(I − K_Ai)|_{L²(s,∞)}`, the Fredholm determinant of the Airy
   kernel. **Needs infrastructure Mathlib does not have at all.** Several
   months just for the prerequisites.

3. **Random-matrix / probabilistic definition** (TW as a limit law):
   `F₂(s) = lim_{N→∞} P( λ_max(GUE_N) ≤ 2√N + s·N^{-1/6} )`. This is the
   "real" theorem, the one your paper (`thm:marg`) ultimately points at.
   **By far the hardest** — it subsumes definitions 1–2 *and* needs a full
   random-matrix-theory and determinantal-point-process layer. Person-years.

Below is the breakdown, with explicit notes on what already exists.

---

## What Mathlib already has (verified)

These are genuine load-bearing prerequisites that are already present, so they
would *not* need to be built:

- **Gamma function** `Complex.Gamma` / `Real.Gamma` and its functional equation.
- **Real/complex analysis substrate**: `deriv`, `fderiv`, `HasDerivAt`,
  interval integrals, improper integrals, dominated convergence, differentiation
  under the integral sign, `Asymptotics.IsBigO`/`IsLittleO`, `Filter.Tendsto`.
- **Linear algebra of Hermitian matrices**: `Matrix.IsHermitian.eigenvalues`,
  the finite-dimensional spectral theorem, `Matrix.det_vandermonde`
  (the Vandermonde determinant — exactly what appears in the GUE joint
  eigenvalue density).
- **Finite-dimensional trace** `LinearMap.trace`.
- **Probability layer**: `ProbabilityTheory.gaussianReal` (1-D Gaussian),
  `ProbabilityTheory.IsGaussian` (Gaussian measures on topological vector
  spaces — recent work), measure-theoretic `variance`/`covariance`
  (this project already uses them), `MeasureTheory.FiniteMeasure` with the
  **portmanteau theorem / weak convergence** infrastructure
  (`FiniteMeasure.tendsto_iff_forall_integral_tendsto`), i.e. the correct notion
  of "convergence in distribution".
- **Infinite products** `tprod` and summability/multipliability API.

## What Mathlib does NOT have (verified absent) — the real work

None of the following exist, and each is a substantial development in its own
right:

- **The Airy function** `Ai`. No special-function entry at all. You would define
  it (e.g. via the contour/oscillatory integral or as the recessive solution of
  `y'' = x·y`) and prove existence, smoothness, the asymptotics
  `Ai(x) ~ exp(−(2/3)x^{3/2})/(2√π x^{1/4})`, the oscillatory `x→−∞` asymptotics,
  and total positivity facts used by the kernel. **Weeks of work by itself.**
- **Bessel and Struve functions** (`I₀`, `L₀`) — relevant to your own paper's
  `prop:struve` closed form, also absent.
- **Painlevé II** and the **Hastings–McLeod solution**: existence/uniqueness of a
  global solution with prescribed asymptotics, connection formulae. This is a
  genuine ODE-theory project (a "connection problem"); the asymptotics are the
  hard part.
- **Schatten / trace-class operators** on Hilbert space, the operator
  **trace** in infinite dimensions, **Hilbert–Schmidt** theory.
- **Fredholm determinants** `det(I − K)` for trace-class `K`, including the
  series expansion `Σ (1/n!) ∫ det[K(x_i,x_j)] dx`, continuity in the operator,
  and the link to traces of powers. **Nothing of this exists.**
- **Determinantal point processes** and the Gaudin–Mehta correlation-kernel
  formalism: the statement that the GUE eigenvalue process is determinantal with
  the Hermite kernel `K_N`, and that `K_N → K_Ai` at the edge.
- **Random matrix theory proper**: the GUE probability measure on Hermitian
  matrices, the **Weyl integration / joint eigenvalue density**
  `∝ Δ(λ)² e^{−Σλ²/2}` (Vandermonde is present, but the change-of-variables to
  eigenvalues is not), **Hermite polynomials as an orthogonal family with their
  asymptotics** (Plancherel–Rotach), and the **edge-scaling limit**.
- A general **central limit theorem** is, at the time of writing, not in Mathlib
  under a usable form either (the Lindeberg/Lévy CLT is still not landed), which
  matters because the probabilistic route leans on CLT-style machinery.

---

## Three routes, ranked by feasibility

### Route 1 — Analytic (Painlevé) definition. *Hardest-but-bounded.*
**Goal:** define `F₂` by the Hastings–McLeod/Tracy–Widom formula and prove it is
a genuine CDF (monotone, `→0` at `−∞`, `→1` at `+∞`, continuous), plus its tail
asymptotics.

Prerequisites to build: Airy function + asymptotics; Painlevé II global solution
with `q(s) ~ Ai(s)`; integrability of `(x−s)q(x)²`; monotonicity/limits of the
resulting `exp(−∫…)`. **Realistic estimate: a few focused months.** This is the
route I would recommend if the aim is "get *a* Tracy–Widom object into Lean with
proved CDF properties," because it avoids operator theory entirely and is the
most modular. It does **not**, by itself, connect to random matrices.

### Route 2 — Fredholm-determinant definition. *Infrastructure-heavy.*
**Goal:** `F₂(s) = det(I − K_Ai|_{L²(s,∞)})`, prove well-definedness and CDF
properties, and (the classical theorem) equivalence with Route 1.

Prerequisites: the entire Schatten/trace-class/Fredholm-determinant tower
(currently absent), plus the Airy kernel and its trace-class bounds. The
Fredholm-determinant layer is genuinely reusable Mathlib infrastructure and
would be valuable independently, but it is **several months of foundational work
before TW even appears**. The equivalence with Painlevé II (the
Tracy–Widom 1994 computation) is itself a hard theorem.

### Route 3 — Random-matrix limit definition. *The full theorem; person-years.*
**Goal:** the actual edge-universality statement
`P(λ_max(GUE_N) ≤ 2√N + sN^{-1/6}) → F₂(s)`, which is what `thm:marg` in the
paper invokes.

This needs **all of Routes 1–2** plus: the GUE measure and Weyl integration
formula; the determinantal structure with the Hermite kernel; Plancherel–Rotach
asymptotics of Hermite polynomials; the edge-scaling kernel convergence
`K_N → K_Ai` with trace-norm control; and continuity of Fredholm determinants to
pass the limit. Each is a major theorem. **Realistic estimate: multiple
person-years**, and it would be a landmark addition to Mathlib (no formal-proof
system has the full GUE edge limit today).

---

## Relation to *this* project

Your paper (`typeD_decoupling-draft-rev2.tex`, `thm:marg`) does **not** reprove
Tracy–Widom — it *reduces* the type-D ASEP currents to single-species ASEP and
then **cites** known TW results for single-species ASEP/last-passage models.
So even a fully formal version of your paper would only need TW as a *black-box
input* (a named hypothesis/`axiom`-free `theorem … := sorry`, or an imported
result), not a from-scratch construction. That is the pragmatic path: state the
TW marginal result as an explicit interface and build the decoupling argument on
top, exactly as the paper does. The closed-form, algebraic, and Gaussian-integral
parts of the paper (already largely formalized in
`RequestProject/TypeDDecoupling.lean`) are the parts that are realistically
within reach without the TW tower.

## Recommended incremental plan (if you want to actually start)

Ordered so that each step is independently useful and Mathlib-mergeable:

1. **Airy function** `Ai`: definition, smoothness, ODE, and `±∞` asymptotics.
   (Self-contained, high value, unblocks everything.)
2. **Fredholm-determinant infrastructure**: Schatten classes → trace-class →
   operator trace → `det(I − K)` with its series and continuity.
   (Reusable far beyond TW.)
3. **Airy kernel** + trace-class bounds on `L²(s,∞)`; **define `F₂` via Route 2**
   and prove CDF properties.
4. **Painlevé II / Hastings–McLeod** and the **Route 1 ↔ Route 2 equivalence**.
5. (Long term) **GUE + Hermite kernel + edge limit** for the full Route 3
   theorem.

Steps 1–3 already constitute a serious but well-defined project that would put a
usable Tracy–Widom `F₂` into Lean; steps 4–5 are research-grade formalization.

---

*Bottom line:* getting a **defined `F₂` with proved CDF properties** is a
realistic multi-month project (best via the Airy/Painlevé or Fredholm route);
getting the **random-matrix limit theorem** that gives TW its meaning is a
multi-person-year, landmark-scale effort, because the entire Fredholm-determinant
and determinantal-point-process layer has to be built first. For the present
ASEP paper, the right move is to treat TW as a cited interface rather than to
rebuild it.
