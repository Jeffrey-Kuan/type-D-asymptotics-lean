# Semigroup route for `lem_free`'s residual — status, results, and precise obstruction

This note documents work on discharging the single bundled residual `sorry` inside
`lem_free` (`TypeDDecouplingLCLT.lean`) by constructing the transition semigroup of the
bounded forward generator, per `semigroup_brief.tex`. It supplements
`LEM_FREE_STATUS.md` (which is left unchanged).

Everything reported as *proved* below lives in the new, library-clean file
`TypeDDecouplingSemigroup.lean` (added to the Lake build target), is `sorry`-free, and uses
only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. `lem_free`'s
statement, the `DriftlessReversibleWalk` structure, `TypeDDecouplingNash.lean`, and
`nash_pointwise_bound` are all untouched; the residual in `TypeDDecouplingLCLT.lean` is
left intact and honest. The whole project builds.

## What is proved (`TypeDDecouplingSemigroup.lean`, standard axioms, no `sorry`)

- **`exists_forward_generator` (Tier 1 foundation).** For a finite-range
  (`rate x y ≠ 0 → |y−x| ≤ ϱ`), nonnegative, bounded-exit-rate (`∑_y rate x y ≤ Λ`) rate
  matrix on `ℤ`, the forward generator
  `(A μ)(y) = (∑ₓ rate(x,y) μ(x)) − (∑_z rate(y,z)) μ(y)`
  exists as a **continuous linear operator on `ℓ¹(ℤ)`** with `‖A‖ ≤ 2Λ`. This is the
  bounded rate-matrix generator of the brief's Tier 1; from it `Q_t := NormedSpace.exp (t•A)`
  and `q_t := Q_t δ₀` are definable, with `exp_add`/`hasDerivAt_exp_smul_const` supplying the
  semigroup and derivative structure.
- **`weight_ratio`.** Geometric-weight comparison within finite range:
  `|x−y| ≤ ϱ ⟹ θ^{|x|} ≤ (θ⁻¹)^ϱ · θ^{|y|}` for `0 < θ ≤ 1`.
- **`VN_int_ineq` (a-priori-estimate groundwork).** For a nonnegative solution `p` of the
  per-site forward ODE with `c := Λ·(θ⁻¹)^ϱ`, the weighted mass in a finite box is controlled
  by the time-integral of the weighted mass in the slightly larger box:
  `∑_{|x|≤N} θ^{|x|} p_s(x) ≤ 1 + c ∫₀ˢ ∑_{|x|≤N+ϱ} θ^{|x|} p_t(x) dt`.
  This is the differential/integral inequality at the heart of the discrete-Widder
  uniqueness argument.

## The full program to close the residual, and where the gap is

Choosing the bundled existential's `u`, the residual is dischargeable *in principle* via
the classical Nash–Carlen–Kusuoka–Stroock (CKS) argument:

1. **Semigroup** `q^x_t := Q_t δ_x = exp(t•A) δ_x ∈ ℓ¹` — from `exists_forward_generator`
   (**done**) + `NormedSpace.exp`.
2. **Identification `W.p = q^0`** by discrete-Widder uniqueness of the forward equation
   (nonnegative solutions with data `δ₀` are unique).
3. **Mass conservation** `∑_y q^0_t(y) = 1` (pairing with `1 ∈ ℓ∞`, `∑_y (Aμ)(y)=0`),
   hence **`W.p ≤ 1`** with nonnegativity — this supplies the residual's `hp1`.
4. **Chapman–Kolmogorov (two-point)** `q^0_{2t}(r) = ∑_y q^0_t(y) q^y_t(r)` from
   `Q_{2t}=Q_t∘Q_t` and the `ℓ¹` expansion `Q_t δ₀ = ∑_y q^0_t(y) δ_y` — *no positivity
   needed*.
5. **Detailed balance / kernel symmetry** `m(y) q^y_t(r) = m(r) q^r_t(y)` from
   reversibility (`A` self-adjoint in `ℓ²(1/m)`).
6. **Energy identity** `u^x(t) := ∑_y q^x_t(y)²/m(y)` is differentiable with
   `(u^x)'(t) = −2 𝓔(q^x_t)` (norm-differentiability of `Q_t` + reversibility). With the
   conductance lower bound and `TypeDDecouplingNash.nash_ineq`, this gives the **uniform
   Nash ODE** `(u^x)' ≤ −κ (u^x)³` with a single `κ` for *all* start points `x`, hence
   `u^x(t) ≤ 1/√(2κ t)` uniformly (via `TypeDDecouplingNash.nash_ode_bound`).
7. **Cauchy–Schwarz** in `ℓ²(1/m)` on step 4 + steps 5–6:
   `q^0_{2t}(r) ≤ m(r) √(u^0(t) u^r(t)) ≤ c₂/√(2κ t)` — again *no positivity*.
8. **Assembly.** Steps 3 and 7 give the on-diagonal bound
   `W.p τ r ≤ C/√(1+τ)`; one then takes `u(t) := C/√t`, `κ := 1/(2C²)`, `Cod := 1`, which
   satisfies the bundled existential (`u' = −κu³` exactly), and feeds
   `nash_pointwise_bound` unchanged.

Two useful simplifications discovered here: **positivity of the constructed semigroup is
not required** (steps 4–7 are linear/`ℓ²` facts; positivity only enters `p ≤ 1` via mass
conservation), and mass conservation is needed only for `hp1`.

### The remaining obstruction (steps 2 and 6)

The route is not completed. Two genuinely hard pieces remain:

- **Step 2 — discrete-Widder well-posedness (the crux).** Uniqueness of nonnegative
  solutions reduces, via `VN_int_ineq` (**done**), to the *a-priori bound*
  `∑_x θ^{|x|} p_s(x) ≤ e^{c s} < ∞`. The differential/integral inequality is proved, but
  its `N`-uniform closure (equivalently: **finiteness / finite-speed-of-propagation**
  well-posedness of the infinite forward ODE system) is a substantial standalone
  development. The box inequality couples scale `N` to `N+ϱ`; closing it needs either a
  Grönwall *continuation* argument (the set of times where the weighted mass is finite is
  shown open-and-closed) or an explicit finite-speed pointwise bound
  `p_s(x) ≲ (Λ' s)^{⌈|x|/ϱ⌉}/⌈|x|/ϱ⌉!` proved by spatial induction. Nonnegativity — the
  a-priori input the `IsTransitionKernel` interface *does* provide — is mathematically
  sufficient (this is the discrete analogue of Widder's theorem), but neither of the
  brief's routes (f) `g(t)=exp(−tA)p_t` nor (g) weighted-`ℓ∞` Grönwall can be run *directly*
  from the bare interface: both need this growth bound, which must first be derived from
  nonnegativity. Fabricating it (e.g. assuming `p` summable) is not admissible, so it is
  left open.
- **Step 6 — energy identity + uniform Nash ODE.** Differentiating `∑_y q_t(y)²/m(y)`
  under the sum (legitimate by norm-differentiability of `Q_t`) and identifying the result
  with `−2𝓔` via reversibility, then combining with the conductance bound and `nash_ineq`.
  This is standard but sizeable operator-theoretic analysis in `ℓ²(1/m)`.

## Why the fixed reduction does not shortcut the work (circularity note)

Because `u`, `κ`, `Cod` are existentially quantified in the residual, one might hope to pick
a convenient `u`. However, a valid `u` must simultaneously satisfy the Nash ODE
(forcing `u(t) ≤ 1/√(2κt)`, i.e. `t^{-1/2}` decay) **and** dominate the two-point kernel via
`hCK`. Since the walk is *not* translation-invariant, `hCK` needs `u` to control the
energies `u^r` from *all* start points, not just the origin energy `u^0` (which can be much
smaller). Consequently the bundled existential is, up to the mild extra fact `p ≤ 1`,
**logically equivalent to `lem_free`'s own conclusion**: exhibiting a valid `u` is possible
iff the `C/√(1+t)` bound already holds. In particular, merely constructing the semigroup and
taking `u = u^0` does **not** discharge the residual; one genuinely needs the *uniform*
Nash ODE for all start points (step 6) together with Chapman–Kolmogorov + Cauchy–Schwarz
(steps 4–7) and the identification (step 2). This is the honest reason the residual encodes
the full CKS theorem rather than a bookkeeping step.

## Interface fields used / needed

- `IsTransitionKernel` (all three components): initial condition `p 0 = δ₀`, nonnegativity
  `0 ≤ p t r`, and the per-site forward ODE. Nonnegativity is the a-priori input for step 2;
  the ODE + `finite_range` make each inner `∑'` a finite sum (used in `VN_int_ineq`).
- `finite_range`, `exit_le` (→ `Λ`): boundedness of `A` and the finite-box inequality.
- `reversible`, `conductance_lb` (`δ`), `m_lb`/`m_ub` (`c₁,c₂`): needed downstream for
  detailed balance, the energy identity, and the Cauchy–Schwarz constant (steps 5–7).

`nash_pointwise_bound`, `nash_ineq`, `nash_ode_bound` would all be consumed **unchanged**.
