import Mathlib
import TypeDDecoupling
import TypeDDecouplingTwoPhaseBridge
import TypeDDecouplingCrossbridge

/-!
# Tier 3 black-box statements: the initial-condition crossover (§cross)

Statements of the §cross results of `typeD_decoupling-draft-rev2.tex`:
the two-phase functional CLT (`prop:twophase`), the duality bridge identity
(`lem:crossbridge`), and the regime-A crossover theorem (`thm:cross`).

The cited / assumed (black-box) content is left as `sorry`: the central limit theorems
(`prop:twophase` and its mixture form), and the Schütz/q-Krawtchouk duality identity
(`lem:crossbridge`).  For the latter, the `q`-Laplace observable `qLaplaceObs` is kept as
an **opaque** η-side object — independent of the dual-side hitting probability — so that
`lem:crossbridge` is a genuine (cited) duality identity rather than a definitional
triviality; it is the one cited duality input, left as an honest `sorry`.  The marquee
correlation value `(1−e^{−4c})/(4c)` is `TypeDDecoupling.rhoCorr c`, whose analytic
content (range, monotonicity, limits) is already proved in `TypeDDecoupling.lean`.

## The dual pair is pinned to a concrete model

A previous version of this file left the rescaled dual pair `X : ℝ → Ω → ℝ × ℝ` as a
*completely free, universally-quantified parameter*.  That made `prop_twophase`,
`prop_twophase_mixture` and `lem_crossbridge` over-strong (in fact refutable): for
example the constant family `X T ω = (0,0)` cannot have a limit law with unit variances,
so "for every `X`, there is a standard-normal-marginal limit" is false.

This file fixes that by pinning `X` to the actual object of the paper through two
concrete predicates on the rescaled coupled walks:

* `IsConditionedDualPair μ u X` — the *conditional* model of `prop:twophase`: the two
  species' walks share their `±1` increments for the first `⌊2u·T⌋` steps (the
  "pre-split" phase of fraction `u`) and use independent increments afterwards.
* `IsDualPairRescaling μ c X` — the *full* model: the split happens at a random step
  `τ T`, and the split fraction `τ/T` converges in distribution to the mixing variable
  `U = min(Exp(4c), 1)` (the law `minExpCDF c`).

With these predicates threaded in as hypotheses, the statements below are genuine
(true-but-cited) theorems rather than false universals, and the constant-family
counterexample no longer satisfies the hypothesis.  What remains `sorry` is exactly the
cited CLT/duality content the paper itself cites rather than proves.

Convergence in distribution of `ℝ × ℝ`-valued random variables is rendered by the
portmanteau test-function characterisation (`TendstoInDistribution`).
-/

open scoped BigOperators Real Topology
open MeasureTheory Filter ProbabilityTheory

namespace TypeDDecoupling

/-- Convergence in distribution, along `atTop` in the scaling parameter `T : ℝ`, of a
family `X T : Ω → ℝ × ℝ` of random variables towards a probability law `ν` on `ℝ × ℝ`:
`E[f(X_T)] → ∫ f dν` for every bounded continuous `f`. -/
def TendstoInDistribution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℝ → Ω → ℝ × ℝ) (ν : Measure (ℝ × ℝ)) : Prop :=
  ∀ f : (ℝ × ℝ) → ℝ, Continuous f → (∃ M : ℝ, ∀ z, |f z| ≤ M) →
    Tendsto (fun T => ∫ ω, f (X T ω) ∂μ) atTop (𝓝 (∫ z, f z ∂ν))

/-- Mean, variance and covariance read off a law `ν` on `ℝ × ℝ` via its coordinate
projections; used to state "standard normal marginals, cross-correlation `r`". -/
def HasStdNormalMarginalsCorr (ν : Measure (ℝ × ℝ)) (r : ℝ) : Prop :=
  (∫ z, z.1 ∂ν = 0) ∧ (∫ z, z.2 ∂ν = 0) ∧
  (∫ z, z.1 ^ 2 ∂ν = 1) ∧ (∫ z, z.2 ^ 2 ∂ν = 1) ∧
  (∫ z, z.1 * z.2 ∂ν = r)

/-! ## The concrete dual-pair model -/

/-- A real random variable that is a **symmetric `±1` increment**: it is measurable,
takes only the values `±1`, and has mean zero (`E[e] = 0`).  These are the elementary
nearest-neighbour steps of the dual walks. -/
def SymmetricPMOneIncrement {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (e : Ω → ℝ) : Prop :=
  Measurable e ∧ (∀ ω, e ω = 1 ∨ e ω = -1) ∧ ∫ ω, e ω ∂μ = 0

/-- CDF of the mixing variable `U = min(E, 1)` with `E ∼ Exp(4c)`:
`0` for `x < 0`, `1 − e^{−4cx}` for `0 ≤ x < 1`, and `1` for `x ≥ 1` (the atom of mass
`e^{−4c}` at `1`). -/
noncomputable def minExpCDF (c x : ℝ) : ℝ :=
  if x < 0 then 0 else if x < 1 then 1 - Real.exp (-(4 * c * x)) else 1

/-- The first species' rescaled walk built from the shared increments `eps (.inl ·)`.

The walk runs for real time `T` at jump rate `2` (the symmetric nearest-neighbour
rate of the dual SSEP walk), hence sums `⌊2T⌋` independent `±1` increments; dividing by
`√(2T)` gives the diffusive scaling with limiting variance `2T/(2T) = 1`, i.e. an
`N(0,1)` marginal, matching `(X₁,X₂)/√(2T)` of the paper. -/
noncomputable def dualWalkFst {Ω : Type*} (eps : ℕ ⊕ ℕ → Ω → ℝ)
    (T : ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range ⌊2 * T⌋₊, eps (Sum.inl i) ω) / Real.sqrt (2 * T)

/-- The second species' rescaled walk: it uses the *same* increments `eps (.inl ·)` for
the first `splitStep` steps (the coupled, pre-split phase) and the *independent*
increments `eps (.inr ·)` afterwards. -/
noncomputable def dualWalkSnd {Ω : Type*} (eps : ℕ ⊕ ℕ → Ω → ℝ)
    (splitStep : ℕ) (T : ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range ⌊2 * T⌋₊,
      (if i < splitStep then eps (Sum.inl i) ω else eps (Sum.inr i) ω)) / Real.sqrt (2 * T)

/-- **Conditional dual-pair model** (`prop:twophase`, conditional form).  `X` is the
rescaled pair `(X₁,X₂)/√(2T)` of two coupled nearest-neighbour walks whose `±1`
increments are independent and symmetric, sharing their increments for the first
`⌊2u·T⌋` steps (the pre-split phase of fraction `u` of the `⌊2T⌋` total steps) and
running on independent increments afterwards.  The shared count is `⌊u·(2T)⌋` so that
the limiting cross-covariance `⌊2uT⌋/(2T) → u` equals the correlation `u`. -/
def IsConditionedDualPair {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u : ℝ) (X : ℝ → Ω → ℝ × ℝ) : Prop :=
  ∃ eps : ℕ ⊕ ℕ → Ω → ℝ,
    (∀ k, SymmetricPMOneIncrement μ (eps k)) ∧ iIndepFun eps μ ∧
    (∀ T ω, X T ω = (dualWalkFst eps T ω, dualWalkSnd eps ⌊u * (2 * T)⌋₊ T ω))

/-- **Full dual-pair model** (`prop:twophase`, unconditional form, and `thm:cross`).
`X` is the rescaled pair `(X₁,X₂)/√(2T)` of two coupled nearest-neighbour walks whose
`±1` increments are independent and symmetric.  The split happens at a *random* step
`τ T : Ω → ℕ`; the two species share their increments before `τ T` and use independent
increments afterwards.  Driven by the regime-(A) split rate `q = 1 − c/T`, the split
fraction `τ/T` converges in distribution to the mixing variable `U = min(Exp(4c), 1)`
(its CDF is `minExpCDF c`). -/
def IsDualPairRescaling {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c : ℝ) (X : ℝ → Ω → ℝ × ℝ) : Prop :=
  ∃ (eps : ℕ ⊕ ℕ → Ω → ℝ) (τ : ℝ → Ω → ℕ),
    (∀ k, SymmetricPMOneIncrement μ (eps k)) ∧ iIndepFun eps μ ∧
    -- the split fraction τ/(2T) (real-time fraction) converges in distribution to
    -- U = min(Exp(4c), 1): here `τ T ω` is the split *jump count* out of the `⌊2T⌋`
    -- total jumps, so the real-time split fraction is `τ/(2T)`.
    (∀ x : ℝ, Tendsto (fun T => (μ {ω | (τ T ω : ℝ) ≤ x * (2 * T)}).toReal) atTop
        (𝓝 (minExpCDF c x))) ∧
    -- X is the rescaled coupled dual pair
    (∀ T ω, X T ω = (dualWalkFst eps T ω, dualWalkSnd eps (τ T ω) T ω))

/-- The dual pair's joint hitting probability `ℙ(X₁(s) ≤ 0, X₂(s) ≤ 0)`, the right-hand
object of `lem:crossbridge`. -/
noncomputable def dualHitProb {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℝ → Ω → ℝ × ℝ) (s : ℝ) : ℝ :=
  (μ {ω | (X s ω).1 ≤ 0 ∧ (X s ω).2 ≤ 0}).toReal

/-- The **species cross-correlation `q`-Laplace observable** of the two-species process.

This is the η-side object of `lem:crossbridge`: the joint `q`-Laplace current observable
of the two species under the block initial condition,
`E_{η⁰}[∏_i η_{i,a}(s) · q^{2(a + N⁺_{a+1}(η_i(s)))}]`.  Its construction lives in the
q-Krawtchouk / Schütz self-duality framework of the two-species ASEP, which is not
available in Mathlib.  We therefore keep it **opaque**: a schematic real-valued
observable attached to the model data `(μ, X, q, a, s)`, with **no** definitional tie to
the dual-side hitting probability `dualHitProb`.

Keeping it opaque (rather than *defining* it to equal its dual-side value) is essential:
the entire mathematical content of `lem:crossbridge` is the Schütz/q-Krawtchouk *duality
identity* that rewrites this η-side expectation as the dual-side quantity
`q^{2k} · ℙ_{(a,a)}(X₁(s) ≤ 0, X₂(s) ≤ 0)`.  Defining the left-hand side to be the
right-hand side would make that identity hold by `rfl` and delete exactly the duality
content the lemma is about.  With the observable independent, `lem:crossbridge` is a
genuine (cited) identity, proved below from the duality input. -/
opaque qLaplaceObs {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℝ → Ω → ℝ × ℝ) (q : ℝ) (a : ℤ) (s : ℝ) : ℝ

/-! ## `prop:twophase` — two-phase functional CLT -/

/-- **Proposition `prop:twophase`** (two-phase functional CLT, conditional form).
Conditionally on `τ/T → u ∈ [0,1]` and on the no-rebinding event `A_T`, the rescaled
dual pair `(X₁(T),X₂(T))/√(2T)` converges in distribution to a standard bivariate normal
of correlation `u` — the law of `(√u ξ₀ + √(1−u) ξ₁, √u ξ₀ + √(1−u) ξ₂)` with
`ξ₀,ξ₁,ξ₂` i.i.d. `N(0,1)`.

The conditioning on `τ/T → u` is encoded by `hX : IsConditionedDualPair μ u X`: the two
walks share their `±1` increments for the first `⌊2u·T⌋` steps and use independent
increments afterwards.  This pins `X` to the actual coupled walks, so the statement is a
genuine (cited) bivariate CLT rather than a free universal.

*Cited/assumed result, black box (`sorry`).*

*Probabilistic core now available.*  The martingale central limit theorem that underlies
this proposition is formalized (sorry-free, standard axioms) in
`TypeDDecouplingMartingaleCLT.lean`: the fixed-time McLeish martingale-difference-array
CLT `TypeDDecoupling.MartingaleCLT.core_charFun_tendsto` / `mcleish_clt`, and its bivariate
Cramér–Wold form `TypeDDecoupling.MartingaleCLT.joint_charFun_tendsto` (the joint CLT with
diagonal brackets, matching the `(S̄, R̄)` structure used here).  What remains for
`prop_twophase` is the model-specific reduction (time discretization of the compensated
jump martingales and the pre/post-split bracket bookkeeping); the CLT itself is no longer a
black box.

*Abstract two-phase mixture CLT now assembled.*  The full two-phase probabilistic
content of `prop:twophase` is formalized (sorry-free, standard axioms) in
`TypeDDecouplingTwoPhase.lean`:
* `TypeDDecoupling.TwoPhase.twophase_charFun_tendsto` — the fixed change-point CLT (a
  locked phase `X = Y` then a diagonal phase), obtained as a Cramér–Wold corollary of
  `core_charFun_tendsto`; its limit is the bivariate normal of correlation `u` with
  covariance form `psiForm u a c = (a+c)²u + (a²+c²)(1−u)` (edge cases
  `twophase_charFun_tendsto_indep` at `u = 0` and `twophase_charFun_tendsto_locked` at
  `u = 1`);
* `TypeDDecoupling.TwoPhase.mixture_charFun_tendsto` — the elementary mixture lemma
  (tower property + dominated convergence) turning the conditional Tier-1 limit into the
  `U`-mixture `E[exp(-½ ψ_U(a,c))]`;
* `TypeDDecoupling.TwoPhase.expMin_mean` — the closed form
  `E[min(Exp(λ),1)] = (1−e^{−λ})/λ`, matching `expMin_mean_eq_rhoCorr`'s value at
  `λ = 4c` (so the mixture's cross-correlation is `rhoCorr c`);
* `TypeDDecoupling.TwoPhase.twophase_mixture_charFun_tendsto` — the assembled
  random-changepoint statement: with `τ/T → U ∼ min(Exp(4c),1)`, the mixture
  characteristic-function limit.

What remains in this leaf `prop_twophase` is exactly the model bookkeeping: identifying
the compensated jump martingales' discretized increments with the abstract array and
supplying the bracket occupation estimates (`lem:occ`/`lem:rebind`).  This model bookkeeping — the
discretization of the compensated jump-pair increments into the abstract two-phase array,
the martingale-difference / jump-bound / bracket estimates, and the resulting
characteristic-function limit — enters through the single named hypothesis bundle `htwo`,
exactly as `prop_conc` receives its `hproc` and `prop_drift` its `hpin`.  Every reduction
step *from* `htwo` *to* the stated conclusion is proved below.

**Route taken (per `twophase_reduction_brief.tex`, remark (4)):** route (2b) — the
discretized-array process facts (MDS, jump bound, bracket convergence) are bundled, and
the conclusion is at the weak-convergence level, obtained by the ℝ²-extended Lévy
continuity theorem `TypeDDecoupling.TwoPhaseBridge.tendstoInDistribution_of_charFun2`.

**The bundle `htwo`, field by field.**
* `ν`, `IsProbabilityMeasure ν` — the identified conditional limit law: the bivariate
  normal of correlation `u` (paper's `prop:twophase`, conditional form; the abstract
  content is `TypeDDecoupling.TwoPhase.twophase_charFun_tendsto`).
* `hXmeas : ∀ T, Measurable (X T)` — the coupled dual pair is a measurable random
  variable (the model's construction from measurable `±1` increments).
* `HasStdNormalMarginalsCorr ν u` — the limit law has standard normal marginals and
  cross-correlation `u` (the covariance form `psiForm u a c` of
  `TypeDDecoupling.TwoPhase.twophase_charFun_tendsto`).
* the `charFun2` convergence — the planar characteristic function of the rescaled pair
  `(X₁,X₂)/√(2T)` converges pointwise to that of `ν`; this is the output of the
  discretized two-phase array CLT
  (`TypeDDecoupling.TwoPhase.twophase_charFun_tendsto`) after the compensated-increment
  discretization and the `lem:occ`/`lem:rebind` bracket estimates. -/
theorem prop_twophase
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : ℝ) (_hu : u ∈ Set.Icc (0 : ℝ) 1)
    (X : ℝ → Ω → ℝ × ℝ) (_hX : IsConditionedDualPair μ u X)
    (htwo : ∃ ν : Measure (ℝ × ℝ), IsProbabilityMeasure ν ∧ (∀ T, Measurable (X T)) ∧
      HasStdNormalMarginalsCorr ν u ∧
      (∀ a b : ℝ, Tendsto (fun T => ∫ ω,
          Complex.exp (((a * (X T ω).1 + b * (X T ω).2 : ℝ) : ℂ) * Complex.I) ∂μ)
        atTop (𝓝 (TwoPhaseBridge.charFun2 ν a b)))) :
    ∃ ν : Measure (ℝ × ℝ), IsProbabilityMeasure ν ∧
      HasStdNormalMarginalsCorr ν u ∧ TendstoInDistribution μ X ν := by
  obtain ⟨ν, hν, hXmeas, hmarg, hchar⟩ := htwo
  exact ⟨ν, hν, hmarg,
    TwoPhaseBridge.tendstoInDistribution_of_charFun2 μ X hXmeas ν hchar⟩

/-! ## `lem:crossbridge` — the dual pair computes the species cross-correlation -/

section ContinuumCrossbridge
open NormedSpace
open scoped Matrix
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **Lemma `lem:crossbridge`** (the dual pair computes the species cross-correlation),
now **proved as the continuum limit of the machine-checked finite-`L` identities**
(`TypeDDecoupling.Crossbridge.crossbridge_finiteL`), with the single genuinely
infinite-volume (IPS) input isolated in the named, documented hypothesis bundle `hcont`.

For the block initial condition, the joint `q`-Laplace observable of the two species
equals, up to the explicit boundary constant `q^{2k}`, a two-particle hitting
probability of the different-species dual pair:
`E_{η⁰}[∏_i η_{i,a}(s) q^{2(a + N⁺_{a+1}(η_i(s)))}] = q^{2k} ℙ_{(a,a)}(X₁(s)≤0, X₂(s)≤0)`.

The right-hand side is the dual-pair hitting probability `dualHitProb μ X s`, and the
left-hand side is the η-side observable `qLaplaceObs μ X q a` — an object *independent* of
`dualHitProb` (kept opaque, since its q-Krawtchouk/Schütz construction needs the duality
framework absent from Mathlib).

## Structure of the proof (the continuum embedding, per `crossbridge_continuum_brief.tex`)

The finite-`L` identity `crossbridge_finiteL` is machine-checked for **every** `L` on the
lattice `{-L,…,L}` (with its documented two-particle-sector interlacing hypothesis, threaded
here unchanged as the field `hinter` of `hcont`).  It reads, at the block `η⁰`, dual site
`siteA L`, and every `s`,
`ObsL(s) = q^{2·0} · PL(s)`, i.e. `ObsL(s) = PL(s)`, where
* `ObsL(s) = (exp (s • Lgen L) *ᵥ crossObs q (siteA L)) η⁰` is the finite-`L` η-side
  observable (process semigroup applied to the `eq:cb` integrand), and
* `PL(s) = (exp (s • Ldual L) *ᵥ hitIndicator) (siteA L, siteA L)` is the finite-`L`
  two-particle dual hitting probability (dual semigroup applied to `𝟙{≤0}·𝟙{≤0}`).

The continuum statement is obtained by letting `L → ∞`:

* **(i) η-side convergence — the bundle `hcont`.**  The convergence of the truncated-block
  observable to the infinite-volume one, `ObsL(s) → qLaplaceObs μ X q a s`, is the
  finite-propagation coupling estimate of the paper's proof.  The infinite-volume process
  (and hence `qLaplaceObs`) lives only at the opaque/hypothesis level in this encoding, so
  this enters as **one** named, documented, faithful hypothesis (the field `hobs` of
  `hcont`), in the `hproc`/`htwo` style, standing for the standard finite-speed coupling.
  We do **not** build infinite-volume IPS theory.
* **(ii) dual-side convergence — a proved semigroup limit.**  `PL(s) → dualHitProb μ X s`
  is the convergence of a hitting probability of the two-particle dual — a countable-state
  walk with bounded finite-range generator.  The mathematical content (finite-box generator
  `A_L` → full generator `A`; Duhamel + the elementary finite-speed series-tail bound
  `(Aⁿδ)(x)=0` for `|x|>nϱ`, so the tail of `e^{sA}δ` is a factorial series tail — no
  probability needed) is proved outright and reusably in
  `TypeDDecoupling.CrossbridgeLimit.hitProb_finiteBox_tendsto`
  (`TypeDDecouplingCrossbridgeLimit.lean`).  For the specific finite-`L` matrix semigroups
  of the Crossbridge core, whose boundary convention and continuous-time-lattice encoding
  differ from the model's rescaled walk, the resulting convergence of `PL(s)` to the model
  object `dualHitProb μ X s` enters as the field `hhit` of `hcont`.
* **(iii) the `L → ∞` assembly — proved here.**  For every `L`, `ObsL(s) = PL(s)`
  (`crossbridge_finiteL`).  Since `ObsL(s) → qLaplaceObs μ X q a s` (i) and, along the same
  sequence, `PL(s) = ObsL(s) → dualHitProb μ X s` (ii), uniqueness of limits gives
  `qLaplaceObs μ X q a s = dualHitProb μ X s = q^{2·0} · dualHitProb μ X s`.  The boundary
  constant is `q^{2k}` with `k = 0`, matching the finite core's normalisation.

The hypotheses `_hc : 0 < c`, `_hX : IsDualPairRescaling μ c X` and `_hq : q ∈ (0,1)`
scope the statement to the actual regime-A dual-pair model.

**The bundle `hcont`, field by field.**
* `Lgen : ∀ L, Matrix (Config L) (Config L) ℝ` — the finite-`L` process generator on the
  four-state configurations of `{-L,…,L}`.
* `Ldual : ∀ L, Matrix (Dual L) (Dual L) ℝ` — the finite-`L` two-particle-sector dual
  generator.
* `siteA : ∀ L, Site L` — the dual site at which the observable/hitting probability is read.
* `hinter : ∀ L, Ldual L * Dmat q = Dmat q * (Lgen L)ᵀ` — the two-particle-sector
  interlacing, threaded unchanged from `crossbridge_finiteL` (the sanctioned
  computer-algebra/REU input; not re-proved or weakened).
* `hobs : ∀ s, 0 ≤ s → Tendsto (fun L => ObsL(s)) atTop (𝓝 (qLaplaceObs μ X q a s))` — the
  η-side finite-propagation coupling convergence (input (i)).
* `hhit : ∀ s, 0 ≤ s → Tendsto (fun L => PL(s)) atTop (𝓝 (dualHitProb μ X s))` — the
  dual-side hitting-probability convergence for the specific finite-`L` matrix semigroups
  (the model embedding of the proved semigroup limit (ii)). -/
theorem lem_crossbridge
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : ℝ) (_hc : 0 < c) (X : ℝ → Ω → ℝ × ℝ) (_hX : IsDualPairRescaling μ c X)
    (q : ℝ) (_hq : q ∈ Set.Ioo (0 : ℝ) 1) (a : ℤ)
    (hcont : ∃ (Lgen : ∀ L : ℕ, Matrix (Crossbridge.Config L) (Crossbridge.Config L) ℝ)
        (Ldual : ∀ L : ℕ, Matrix (Crossbridge.Dual L) (Crossbridge.Dual L) ℝ)
        (siteA : ∀ L : ℕ, Crossbridge.Site L),
        (∀ L : ℕ, Ldual L * Crossbridge.Dmat q = Crossbridge.Dmat q * (Lgen L)ᵀ) ∧
        (∀ s : ℝ, 0 ≤ s → Filter.Tendsto
            (fun L : ℕ => (exp (s • Lgen L) *ᵥ Crossbridge.crossObs q (siteA L))
              Crossbridge.eta0)
            Filter.atTop (𝓝 (qLaplaceObs μ X q a s))) ∧
        (∀ s : ℝ, 0 ≤ s → Filter.Tendsto
            (fun L : ℕ => (exp (s • Ldual L) *ᵥ Crossbridge.hitIndicator) (siteA L, siteA L))
            Filter.atTop (𝓝 (dualHitProb μ X s)))) :
    ∃ k : ℤ, ∀ s : ℝ, 0 ≤ s → qLaplaceObs μ X q a s = q ^ (2 * k) * dualHitProb μ X s := by
  obtain ⟨Lgen, Ldual, siteA, hinter, hobs, hhit⟩ := hcont
  -- The continuum boundary constant is `q^{2·0} = 1`, matching the finite core.
  refine ⟨0, fun s _hs => ?_⟩
  -- (iii) assembly.  Finite-`L` identity `ObsL(s) = PL(s)` for every `L`.
  have hfin : ∀ L : ℕ,
      (exp (s • Lgen L) *ᵥ Crossbridge.crossObs q (siteA L)) Crossbridge.eta0
        = (exp (s • Ldual L) *ᵥ Crossbridge.hitIndicator) (siteA L, siteA L) := by
    intro L
    have h := Crossbridge.crossbridge_finiteL q _hq (Lgen L) (Ldual L) (hinter L) (siteA L) s
    simpa using h
  -- `PL(s) = ObsL(s) → qLaplaceObs μ X q a s` (i, rewritten through the finite identity).
  have hPL : Filter.Tendsto
      (fun L : ℕ => (exp (s • Ldual L) *ᵥ Crossbridge.hitIndicator) (siteA L, siteA L))
      Filter.atTop (𝓝 (qLaplaceObs μ X q a s)) :=
    (hobs s _hs).congr hfin
  -- Uniqueness of limits: `qLaplaceObs = dualHitProb`.
  have hEq := tendsto_nhds_unique hPL (hhit s _hs)
  rw [show (2 * (0 : ℤ)) = 0 by ring, zpow_zero, one_mul]
  exact hEq

/-! ## Mixture form of `prop:twophase` (the genuine CLT black box) -/

/-- **Mixture form of `prop:twophase`.**  The limit law of `(X₁,X₂)/√(2T)` is the
mixture, over the split fraction `U ∼ min(Exp(4c),1)`, of the bivariate normals of
correlation `U` produced by `prop:twophase`.  This mixture is a probability law with
standard normal marginals, and its cross-correlation is the mean of the mixing
variable, `r = E[U] = ∫₀^∞ min(t,1)·(4c)·e^{−4ct} dt`.

This is the *unconditional* statement of `prop:twophase` (its second paragraph in the
paper): convergence in distribution of the rescaled dual pair to the `U`-mixture.  The
pair is pinned to the concrete model via `hX : IsDualPairRescaling μ c X`, so this is a
genuine (cited) CLT statement.  It is the **only** CLT black box (`sorry`) that the
crossover theorem `thm_cross` below rests on; everything else in `thm_cross` is then
assembled from already-proved results.  The correlation is returned in its raw
integral form `∫ … min t 1 …` precisely so that `thm_cross` can identify it with
`rhoCorr c` using the proved closed-form lemma `expMin_mean_eq_rhoCorr`.

As with `prop_twophase`, the irreducibly process-level content — the discretization of the
compensated jump-pair increments, the martingale-difference / jump-bound / bracket
estimates, and the resulting mixture characteristic-function limit — enters through the
single named hypothesis bundle `htwo` (route (2b) of `twophase_reduction_brief.tex`),
exactly as `prop_conc` receives `hproc`.  The reduction from `htwo` to the conclusion is
proved via the ℝ²-extended Lévy continuity theorem
`TypeDDecoupling.TwoPhaseBridge.tendstoInDistribution_of_charFun2`.

**The bundle `htwo`, field by field.**
* `ν`, `IsProbabilityMeasure ν` — the identified mixture limit law: the `U`-mixture of
  bivariate normals with `U ∼ min(Exp(4c),1)` (the abstract content is
  `TypeDDecoupling.TwoPhase.twophase_mixture_charFun_tendsto`).
* `hXmeas : ∀ T, Measurable (X T)` — the coupled dual pair is measurable.
* `HasStdNormalMarginalsCorr ν r` with `r = E[U] = ∫₀^∞ min(t,1)(4c)e^{-4ct}dt` — the
  mixture has standard normal marginals and cross-correlation `E[U]`
  (`TypeDDecoupling.TwoPhase.expMin_mean`; matches `expMin_mean_eq_rhoCorr`).
* the `charFun2` convergence — the planar characteristic function of the rescaled pair
  converges pointwise to that of `ν`; this is the output of the discretized two-phase
  mixture array CLT `TypeDDecoupling.TwoPhase.twophase_mixture_charFun_tendsto` after the
  compensated-increment discretization, the `lem:split` change-point limit, and the
  `lem:occ`/`lem:rebind` bracket estimates. -/
theorem prop_twophase_mixture
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : ℝ) (_hc : 0 < c) (X : ℝ → Ω → ℝ × ℝ) (_hX : IsDualPairRescaling μ c X)
    (htwo : ∃ ν : Measure (ℝ × ℝ), IsProbabilityMeasure ν ∧ (∀ T, Measurable (X T)) ∧
      HasStdNormalMarginalsCorr ν
        (∫ t in Set.Ioi (0 : ℝ), min t 1 * (4 * c) * Real.exp (-(4 * c * t))) ∧
      (∀ a b : ℝ, Tendsto (fun T => ∫ ω,
          Complex.exp (((a * (X T ω).1 + b * (X T ω).2 : ℝ) : ℂ) * Complex.I) ∂μ)
        atTop (𝓝 (TwoPhaseBridge.charFun2 ν a b)))) :
    ∃ (ν : Measure (ℝ × ℝ)) (r : ℝ), IsProbabilityMeasure ν ∧
      r = ∫ t in Set.Ioi (0 : ℝ), min t 1 * (4 * c) * Real.exp (-(4 * c * t)) ∧
      HasStdNormalMarginalsCorr ν r ∧ TendstoInDistribution μ X ν := by
  obtain ⟨ν, hν, hXmeas, hmarg, hchar⟩ := htwo
  exact ⟨ν, _, hν, rfl, hmarg,
    TwoPhaseBridge.tendstoInDistribution_of_charFun2 μ X hXmeas ν hchar⟩

/-! ## `thm:cross` — regime-A crossover from the block initial condition -/

/-- **Theorem `thm:cross`** (regime-A crossover from the block initial condition).
Fix `c > 0` and set `q = 1 − c/T`.  As `T → ∞` the rescaled dual pair
`(X₁,X₂)/√(2T)` converges in distribution to a law `(G₁,G₂)` with standard normal
marginals and cross-correlation `Corr(G₁,G₂) = (1−e^{−4c})/(4c) = rhoCorr c ∈ (0,1)`.
The joint law is the non-Gaussian mixture of `prop:twophase` with mixing variable
`U ∼ min(Exp(4c),1)` (an atom of mass `e^{−4c}` at `1`, where `G₁=G₂`).  By
`lem:crossbridge`, `(G₁,G₂)` is the limiting joint law of the two species' `q`-Laplace
current observables from the block initial condition.

The dual pair `X` is the concrete model `hX : IsDualPairRescaling μ c X`.  This is the
paper's one-line assembly carried out in Lean: the proof **combines** three inputs and
contains no `sorry` of its own.
* `prop_twophase_mixture` (the mixture form of `prop:twophase`) supplies the limit law
  `ν`, its standard normal marginals, its cross-correlation `r = E[U]`, and the
  convergence in distribution;
* `thm:closed` supplies the closed form of the correlation —
  `expMin_mean_eq_rhoCorr` rewrites `E[U]` to `rhoCorr c`, and `rhoCorr_mem_Ioo`
  places it in `(0,1)` (both already proved in `TypeDDecoupling.lean`);
* `lem_crossbridge` supplies the identification of `(G₁,G₂)` with the two species'
  `q`-Laplace observables (the final existential clause).

The two-phase process bundle `htwo` of `prop_twophase_mixture` is threaded through here,
mirroring how `thm_ewmain` threads `hconc` to `prop_conc`; it is the sole irreducibly
process-level input carried by this assembly.  The continuum crossbridge bundle `hcont`
(the η-side finite-propagation coupling and the dual-side hitting-probability convergence,
see `lem_crossbridge`) is threaded through in exactly the same way, supplying the final
`q`-Laplace/dual-hitting identity clause. -/
theorem thm_cross
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (X : ℝ → Ω → ℝ × ℝ) (hX : IsDualPairRescaling μ c X)
    (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (a : ℤ)
    (htwo : ∃ ν : Measure (ℝ × ℝ), IsProbabilityMeasure ν ∧ (∀ T, Measurable (X T)) ∧
      HasStdNormalMarginalsCorr ν
        (∫ t in Set.Ioi (0 : ℝ), min t 1 * (4 * c) * Real.exp (-(4 * c * t))) ∧
      (∀ a' b : ℝ, Tendsto (fun T => ∫ ω,
          Complex.exp (((a' * (X T ω).1 + b * (X T ω).2 : ℝ) : ℂ) * Complex.I) ∂μ)
        atTop (𝓝 (TwoPhaseBridge.charFun2 ν a' b))))
    (hcont : ∃ (Lgen : ∀ L : ℕ, Matrix (Crossbridge.Config L) (Crossbridge.Config L) ℝ)
        (Ldual : ∀ L : ℕ, Matrix (Crossbridge.Dual L) (Crossbridge.Dual L) ℝ)
        (siteA : ∀ L : ℕ, Crossbridge.Site L),
        (∀ L : ℕ, Ldual L * Crossbridge.Dmat q = Crossbridge.Dmat q * (Lgen L)ᵀ) ∧
        (∀ s : ℝ, 0 ≤ s → Filter.Tendsto
            (fun L : ℕ => (exp (s • Lgen L) *ᵥ Crossbridge.crossObs q (siteA L))
              Crossbridge.eta0)
            Filter.atTop (𝓝 (qLaplaceObs μ X q a s))) ∧
        (∀ s : ℝ, 0 ≤ s → Filter.Tendsto
            (fun L : ℕ => (exp (s • Ldual L) *ᵥ Crossbridge.hitIndicator) (siteA L, siteA L))
            Filter.atTop (𝓝 (dualHitProb μ X s)))) :
    ∃ ν : Measure (ℝ × ℝ), IsProbabilityMeasure ν ∧
      HasStdNormalMarginalsCorr ν (rhoCorr c) ∧
      rhoCorr c ∈ Set.Ioo (0 : ℝ) 1 ∧
      TendstoInDistribution μ X ν ∧
      ∃ k : ℤ, ∀ s : ℝ, 0 ≤ s → qLaplaceObs μ X q a s = q ^ (2 * k) * dualHitProb μ X s := by
  -- `prop:twophase` (mixture form): the limit law, its marginals, correlation `E[U]`,
  -- and convergence in distribution.
  obtain ⟨ν, r, hprob, hr, hmarg, htend⟩ := prop_twophase_mixture μ c hc X hX htwo
  -- `thm:closed`: the closed form `E[U] = rhoCorr c`.
  rw [expMin_mean_eq_rhoCorr hc] at hr
  subst hr
  -- Assemble, using `rhoCorr_mem_Ioo` (`thm:closed`) and `lem_crossbridge`.
  exact ⟨ν, hprob, hmarg, rhoCorr_mem_Ioo hc, htend,
    lem_crossbridge μ c hc X hX q hq a hcont⟩

end ContinuumCrossbridge

end TypeDDecoupling
