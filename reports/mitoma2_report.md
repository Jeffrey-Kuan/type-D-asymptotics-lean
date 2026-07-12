# Mitoma campaign, task 2 — separability of Schwartz space and compact polars in the pointwise dual

## Outcome

**Full delivery.** A new self-contained file `TypeDDecouplingSchwartzDual.lean`
(Mathlib imports only, plus `import TypeDDecouplingSchwartzFrechet` from task M1;
no existing project file touched; whole project builds — 8065 jobs; no
`axiom`/`sorry`) delivers **all** of Part A and Part B. Every deliverable was
checked to depend only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound` (via `#print axioms`). All statements refer to Mathlib's canonical
`SchwartzMap` and `PointwiseConvergenceCLM` topologies; nothing is
re-topologized.

## Part A: separability of `𝓢(ℝ, ℝ)`

Mathlib has **no** separability / second-countability instance for `SchwartzMap`
(verified). Both are now provided.

### (A1) Main results
- `SchwartzMap.instSeparableSpace : SeparableSpace (SchwartzMap ℝ ℝ)`
- `SchwartzMap.instSecondCountableTopology : SecondCountableTopology (SchwartzMap ℝ ℝ)`
  (derived from separability + M1's countably generated uniformity via
  `UniformSpace.secondCountable_of_separable`).

**Route taken — the structural (weighted-derivative) route from the brief.**
The weighted-derivative maps `φ ↦ (x ↦ |x|^k · dⁿφ(x))` are realized as
elements of `C₀(ℝ, ℝ)` and assembled into a single linear map

- `SchwartzMap.weightedDerivC0 (k n : ℕ) (φ) : ZeroAtInftyContinuousMap ℝ ℝ`
  with `toFun x = |x|^k * iteratedDeriv n φ x`;
- `SchwartzMap.weightedDerivLM : 𝓢(ℝ,ℝ) →ₗ[ℝ] Π (kn : ℕ × ℕ), C₀(ℝ, ℝ)`.

Supporting facts:
- `continuous_weightedDerivFun`, `tendsto_weightedDerivFun` — continuity and
  vanishing at infinity (Schwartz decay: `|x|^k·|dⁿφ| ≤ p_{k+1,n}/|x| → 0`,
  via `SchwartzMap.le_seminorm`, `norm_iteratedFDeriv_eq_norm_iteratedDeriv`,
  `tendsto_norm_cocompact_atTop`, `squeeze_zero_norm'`);
- `weightedDerivC0_add`, `weightedDerivC0_smul` — linearity in `φ`;
- `norm_weightedDerivC0 : ‖weightedDerivC0 k n φ‖ = SchwartzMap.seminorm ℝ k n φ`
  — the `C₀` sup-norm of the weighted derivative **equals** the Schwartz
  seminorm `p_{k,n}` (antisymmetry via `SchwartzMap.le_seminorm` /
  `seminorm_le_bound` and the `BoundedContinuousFunction` norm lemmas);
- `isInducing_weightedDerivLM : Topology.IsInducing weightedDerivLM` — the
  embedding is topological. This is the crux: the induced seminorm family
  (`LinearMap.withSeminorms_induced` applied to `withSeminorms_pi` over the
  `C₀` factors, each `norm_withSeminorms`) coincides seminorm-by-seminorm with
  `schwartzSeminormFamily` by `norm_weightedDerivC0`; `WithSeminorms.congr`
  (both `Seminorm.IsBounded` directions being immediate from the value
  equality) then forces the two topologies to agree via
  `SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf`.

Separability then transfers along the embedding:
`Topology.IsInducing.secondCountableTopology` gives second countability of
`𝓢(ℝ,ℝ)` from that of the countable product `Π (kn) C₀(ℝ,ℝ)`, hence separability.

### (A2) Separability of `C₀(ℝ, ℝ)`
- `SchwartzMap.separableSpace_zeroAtInfty : SeparableSpace (ZeroAtInftyContinuousMap ℝ ℝ)`.

Mathlib had no separability for `ZeroAtInftyContinuousMap`. Route via the
**one-point compactification**:
- `SchwartzMap.secondCountableTopology_onePoint_real :
  SecondCountableTopology (OnePoint ℝ)` — an explicit countable topological
  basis (images of a countable basis of `ℝ` under the open embedding `some`,
  together with the neighbourhoods `{∞} ∪ some '' (Icc (-n) n)ᶜ` of `∞`;
  every compact of `ℝ` is bounded). Mathlib only had the *negative* result for
  `OnePoint ℚ`.
- The extension-by-zero map `C₀(ℝ,ℝ) → C(OnePoint ℝ, ℝ)` is an **isometry**
  (`OnePoint.continuousMapMk`; the value at `∞` is `0`, so the sup over
  `OnePoint ℝ` equals the sup over `ℝ`); with `OnePoint ℝ` compact and second
  countable, `C(OnePoint ℝ, ℝ)` is second countable
  (`ContinuousMap.instSeparableSpace`/second-countable instance, compact-open
  = sup norm), so `Topology.IsEmbedding.separableSpace` gives the result.

### (A3) Countable-reduction corollary
- `SchwartzMap.denseSet`, `denseSet_countable`, `denseSet_dense` — a *named*
  countable dense subset of `𝓢(ℝ,ℝ)` (from A1 via `exists_countable_dense`).
- `SchwartzMap.forall_le_of_forall_dense` — for a continuous linear functional
  `F` and a **continuous** seminorm `q`, a bound `|F φ| ≤ q φ` on a dense set of
  `φ` extends to all `φ` (the set `{φ | |F φ| ≤ q φ}` is closed and contains a
  dense set). Stated for an arbitrary dense set, so it does not itself depend on
  A1.

## Part B: compact polars in the pointwise dual

`SchDual := 𝓢(ℝ,ℝ) →Lₚₜ[ℝ] ℝ` (`SchwartzMap.SchDual`, Mathlib's
`PointwiseConvergenceCLM`).

### (B1) Polar balls
- `SchwartzMap.polarBall (q : Seminorm ℝ (𝓢(ℝ,ℝ))) : Set SchDual :=
  {F | ∀ φ, |F φ| ≤ q φ}`, with `mem_polarBall`, `zero_mem_polarBall`,
  `polarBall_mono`.

### (B2) Compactness
- `SchwartzMap.isCompact_polarBall (q) (hq : Continuous q) :
  IsCompact (polarBall q)`.

Route (Tychonoff, **no Ascoli**): push through
`PointwiseConvergenceCLM.isEmbedding_coeFn` into the product `𝓢(ℝ,ℝ) → ℝ`; the
image is exactly the closed set of functions that are additive, homogeneous and
`q`-bounded (a pointwise limit obeying the bound is automatically continuous,
being dominated by the continuous seminorm `q` — reconstructed as a
`ContinuousLinearMap` via `Seminorm.continuous_of_le` +
`continuous_of_continuousAt_zero`), sitting inside the compact box
`∏_φ [-q φ, q φ]` (`isCompact_univ_pi`, `isCompact_Icc`); compactness pulls back
along the embedding.

### (B3) Countable cofinal family of rational polar balls
- `SchwartzMap.ratSeminorm (c : ℝ≥0) (s : Finset (ℕ × ℕ)) :=
  c • Finset.sup s (schwartzSeminormFamily ℝ ℝ ℝ)`, with `continuous_ratSeminorm`
  and `isCompact_polarBall_ratSeminorm`.
- `SchwartzMap.pointwiseBounded_subset_compact_polarBall` — every
  pointwise-bounded family in `SchDual` lies in a **compact** `polarBall` of the
  special rational form. Combines M1's
  `exists_continuous_seminorm_of_pointwise_bounded` (dominating continuous
  seminorm) with `Seminorm.bound_of_continuous` (`WithSeminorms` bound
  characterization: `q ≤ C • s.sup p`, `C : ℝ≥0`).

### (B4) Membership is countably checkable
- `SchwartzMap.mem_polarBall_iff_dense (q) (hq : Continuous q) (hD : Dense D) :
  F ∈ polarBall q ↔ ∀ φ ∈ D, |F φ| ≤ q φ` (direct from A3), and its
  specialisation `mem_polarBall_iff_denseSet` to the named countable dense set.
  This is the measurability hook for task M3: the confinement event is a
  countable intersection of evaluation events.

## Key Mathlib lemmas that carried the proofs
`PointwiseConvergenceCLM.isEmbedding_coeFn`, `Topology.IsEmbedding.isCompact_iff`,
`isCompact_univ_pi`, `isCompact_Icc`, `Seminorm.continuous_of_le`,
`Seminorm.bound_of_continuous`, `WithSeminorms.congr`, `withSeminorms_pi`,
`LinearMap.withSeminorms_induced`,
`SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf`,
`Topology.IsInducing.secondCountableTopology`,
`TopologicalSpace.IsTopologicalBasis.secondCountableTopology`,
`OnePoint.continuousMapMk`, `OnePoint.isOpenEmbedding_coe`,
`Isometry.isEmbedding`, `Topology.IsEmbedding.separableSpace`,
`ZeroAtInftyContinuousMap.norm_toBCF_eq_norm`,
`norm_iteratedFDeriv_eq_norm_iteratedDeriv`, `tendsto_norm_cocompact_atTop`,
`SchwartzMap.le_seminorm`, `SchwartzMap.seminorm_le_bound`, and M1's
`SchwartzMap.exists_continuous_seminorm_of_pointwise_bounded`.

## Obstructions encountered (all resolved)
- No `SeparableSpace`/`SecondCountableTopology` for `SchwartzMap` or
  `ZeroAtInftyContinuousMap` in Mathlib; `SecondCountableTopology (OnePoint ℝ)`
  also absent (only the negative `OnePoint ℚ` result exists). All three were
  proved from scratch here.
- The `C(X,Y)` separability instance in Mathlib is for the compact-open
  topology; it applies to `C₀` only after routing through the (compact)
  one-point compactification, where compact-open coincides with the sup norm.

## Upstream-worthy observations
- `SecondCountableTopology (OnePoint ℝ)`, `SeparableSpace C₀(ℝ,ℝ)`, and the
  separability of `SchwartzMap` are all natural Mathlib additions.
- `norm_weightedDerivC0` (`C₀` sup-norm of the weighted derivative = Schwartz
  seminorm) together with `isInducing_weightedDerivLM` is a reusable
  presentation of the Schwartz topology as an initial topology into `C₀` spaces.
