# Status of `lem_free` (Nash/CKS on-diagonal heat-kernel bound)

## What was added / proved

New library-clean file **`TypeDDecouplingNash.lean`** (added to the lake target),
containing the complete *analytic* content of the Nash/CKS method, all proved outright
(verified to use only the standard axioms `propext`, `Classical.choice`, `Quot.sound`):

* **Tier 1 — discrete Nash inequality on `ℤ`** (elementary Agmon route, no Fourier):
  * `agmon_le` : `f(x)² ≤ 2‖f‖₂‖∇f‖₂` for summable `f : ℤ → ℝ`;
  * `nash_ineq` : `‖f‖₂⁶ ≤ 4‖f‖₁⁴‖∇f‖₂²`.
* **Tier 2 (analytic core) — Nash ODE comparison**:
  * `nash_ode_bound` : a nonincreasing `u ≥ 0` on `(0,∞)` with `u' ≤ -κu³` obeys
    `u(t) ≤ 1/√(2κt)`.
* **Tier 3 assembly**:
  * `nash_pointwise_bound` : from the Nash differential inequality for the on-diagonal
    `ℓ²`-energy **plus** a Chapman–Kolmogorov off-diagonal bound `p(2t) r ≤ Cod·u(t)`
    and `p ≤ 1`, deduces the uniform bound `p t r ≤ C/√(1+t)` with an explicit `C`.

In **`TypeDDecouplingLCLT.lean`**, `lem_free` is rewritten to *apply* `nash_pointwise_bound`
(statement and the `DriftlessReversibleWalk` structure unchanged, all other leaves
untouched; a single `import TypeDDecouplingNash` was added).

## The residual (one documented `sorry`)

Applying the assembly reduces `lem_free` to the two genuinely **dynamical** inputs,
bundled in a single `have` inside `lem_free`:

1. the Nash differential inequality `u' ≤ -κu³` for `u t = ∑' x, (W.p t x)²/W.m x`, which
   packages the **Dirichlet-form energy identity** `u'(t) = -2𝓔(p_t)`, the conductance
   lower bound, and `nash_ineq`;
2. the **Chapman–Kolmogorov / off-diagonal bound** `W.p (2t) r ≤ Cod·u(t)` and `W.p ≤ 1`.

These are properties of the **transition semigroup**: they involve the *two-point* kernel
`p_t(y→·)` and mass conservation. The fixed `IsTransitionKernel` interface carries only the
single kernel started at the origin together with its per-site forward ODE — it exposes
neither the two-point kernel, nor Chapman–Kolmogorov, nor any a-priori integrability of
`W.p`. Consequently:

* the off-diagonal `t^{-1/2}` bound provably cannot be obtained from on-diagonal `ℓ²`
  decay alone (that gives only `t^{-1/4}` pointwise); it genuinely needs Chapman–Kolmogorov;
* the energy identity, mass conservation and `p ≤ 1` all require differentiating under the
  infinite sum / a-priori regularity that the bare structure does not force.

Deriving them would require constructing the operator semigroup `exp(tA)δ₀` of the
(finite-range, bounded) generator `A` on `ℓ²(ℤ)` and identifying `W.p` with it (which in
turn needs an a-priori weighted-`ℓ¹` bound from the finite range). Since the task forbids
changing the structure or the statement of `lem_free` (so these facts cannot enter as named
hypotheses), and forbids axioms, this infrastructure would have to be built from scratch;
it is left as the sole residual `sorry`, clearly documented at that point.

## Report on brief remark (5): was the energy identity (d) proved or hypothesised?

Neither, strictly. Under the hard constraints (structure and statement unchanged, no
axioms), the energy identity cannot be introduced as an admissible standalone named
hypothesis, and it cannot be proved in isolation from the bare interface (it needs the
Kolmogorov equation differentiated under the sum, i.e. regularity the structure omits).
It is therefore part of the single bundled residual, together with Chapman–Kolmogorov and
mass conservation, all of which are semigroup/two-point-kernel facts not exposed by
`IsTransitionKernel`.

The whole project builds; every newly added theorem in `TypeDDecouplingNash.lean` is
`sorry`-free and uses only standard axioms.
