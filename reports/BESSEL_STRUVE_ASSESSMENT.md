# How hard would it be to build Bessel & Struve functions in Mathlib/Lean?

*Scope note: per your request, this is an assessment only — nothing was built. I checked
the current Mathlib in this project to ground the estimates.*

## TL;DR

It's a **moderate, well-bounded project — far easier than Tracy–Widom** (see
`TRACY_WIDOM_ROADMAP.md`). The objects are elementary special functions defined by
everywhere-convergent power series, and their only nontrivial dependency — the **Gamma
function — is already in Mathlib** (`Real.Gamma`, `Complex.Gamma`, including half-integer
values via `Gamma(1/2) = √π` and the functional equation). There are **no Bessel or Struve
definitions in Mathlib today** (verified: searches for `Bessel` and `Struve` return nothing).

Rough effort, for one person already fluent in Lean/Mathlib:

| Target | Effort | Risk |
|---|---|---|
| Define `I₀`/`J₀` (and general order `Jν`, `Iν`) as power series; prove entire/analytic | ~1–2 weeks | low |
| Add Struve `L₀`/`H₀` (and general order) similarly | ~1 week | low |
| Core algebra: derivative & recurrence relations, the defining ODEs | ~2–4 weeks | low–medium |
| Integral representations (the bridge to the paper's correlation formula) | ~3–6 weeks | medium |
| Large-argument asymptotics, zeros, addition theorems | several months | medium–high |

A genuinely useful, mergeable first contribution (definitions + analyticity + ODE/recurrences)
is realistically a **few weeks to ~1–2 months**. The classical "full theory" is several months.

## Why it's tractable (the dependency picture)

The hard prerequisite for special functions is usually (a) a convergent-series /
analyticity framework and (b) the Gamma function. Mathlib has both:

- **Gamma**: `Real.Gamma`, `Complex.Gamma`, `Gamma_ne_zero`, reflection/duplication, the
  Beta function, and derivatives are all present.
- **Power series / analyticity**: `tsum`, `FormalMultilinearSeries`, `AnalyticAt`,
  ratio/root convergence tests, term-by-term differentiation of power series, and
  `DifferentiableOn`/entire-function machinery are all present.
- **Real-analysis substrate**: derivatives, integrals (`MeasureTheory.integral`),
  dominated convergence, `arcsin`, `exp`, etc.

So Bessel/Struve can be **defined directly as `tsum`s** and their basic theory derived,
without first building any missing infrastructure. This is the key contrast with
Tracy–Widom, Airy-with-asymptotics, or Fredholm determinants, which need large amounts of
*missing* foundational machinery before the target object can even be stated.

## Concrete construction sketch

These are the standard everywhere-convergent series; all coefficients are expressible with
`Real.Gamma`/factorials already in Mathlib.

- **Bessel (first kind):** `Jν z = Σ_{m≥0} (-1)^m / (m! · Γ(m+ν+1)) · (z/2)^(2m+ν)`
- **Modified Bessel:** `Iν z = Σ_{m≥0} 1 / (m! · Γ(m+ν+1)) · (z/2)^(2m+ν)`
  - Order 0 is especially clean: `I₀ z = Σ_{m≥0} (z/2)^(2m) / (m!)²` (no Gamma needed).
- **Struve:** `Hν z = Σ_{m≥0} (-1)^m / (Γ(m+3/2)·Γ(m+ν+3/2)) · (z/2)^(2m+ν+1)`
- **Modified Struve:** `Lν z = Σ_{m≥0} 1 / (Γ(m+3/2)·Γ(m+ν+3/2)) · (z/2)^(2m+ν+1)`
  - Order 0: `L₀ z = Σ_{m≥0} (z/2)^(2m+1) / (Γ(m+3/2))²`, using Mathlib's half-integer Gamma.

A sensible build order:
1. Define `I₀` (cleanest, factorial-only); prove the series is entire and `I₀ 0 = 1`.
2. Generalize to `Iν`/`Jν` with the Gamma coefficients; prove analyticity + radius = ∞.
3. Prove the derivative/recurrence identities and the defining Bessel ODE.
4. Repeat 1–3 for `L₀`/`H₀`/general order (these solve the inhomogeneous Bessel ODE).
5. Integral representations — the part that connects to your paper.

The trickiest routine step is the recurrences/ODEs: differentiating a `tsum` term-by-term
and re-indexing requires care with Mathlib's summability lemmas, but it's standard.

## What this means for your paper specifically

You don't actually need any of this for the type-D ASEP formalization. The Bessel–Struve
positive-part correlation in `prop:struve` is just a **closed-form rewrite** of an integral,
and the equivalent integral form `(1/2π)∫₀¹ (π/2 + arcsin s) e^{−4cs} ds` and all its
analytic content (range `(0,1)`, `c→0` limit `1`, the `π/(8(π−1)c)` tail) are **already
formalized and fully proved** in `RequestProject/TypeDDecoupling.lean` (`rhoStruve`,
`rhoStruve_mem_Ioo`, `rhoStruve_tendsto_one`, `rhoStruve_tail`).

So building Bessel/Struve would only be worthwhile if you wanted the statement *literally*
in terms of `I₀`/`L₀`. To match the paper's literal expression you'd additionally need the
specific integral identity expressing `∫₀¹ (π/2 + arcsin s) e^{−4cs} ds` via `I₀` and `L₀`
(an integral-representation result for Struve functions) — that's the "medium-risk" line in
the table, and it sits on top of the basic build.

## Bottom line

- **Basic Bessel/Struve (definitions, analyticity, ODEs/recurrences):** a clean, mergeable
  Mathlib contribution; **weeks, low risk.** This is genuinely the kind of thing that could
  be PR'd to Mathlib.
- **Integral representations + the exact identity in your paper:** add a few more weeks,
  medium risk.
- **Full classical theory (asymptotics, zeros, addition theorems):** several months.
- **Not needed for your project** — the equivalent integral form is already proved.
