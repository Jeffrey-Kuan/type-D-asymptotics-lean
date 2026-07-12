# Mitoma campaign, task 1 — the Fréchet package for Schwartz space

## Outcome

**Full package delivered.** A new self-contained file
`TypeDDecouplingSchwartzFrechet.lean` (Mathlib imports only; no existing project
file touched; whole project builds — 8064 jobs; no `axiom`/`sorry`) establishes,
for Mathlib's canonical `SchwartzMap E F`, all five deliverables. Every new
declaration depends only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound` (verified with `#print axioms`).

All instances attach to Mathlib's **canonical** Schwartz uniformity/topology
(`SchwartzMap.instUniformSpace` / `instTopologicalSpace`). No homemade metric or
topology is introduced anywhere; the pseudometrization used for the Baire step is
Mathlib's uniformity-level metrization of countably generated uniformities, so it
induces exactly the canonical uniformity and completeness transfers automatically.

## Generality

Results are stated for general real normed spaces `E`, `F`
(`[NormedAddCommGroup E] [NormedSpace ℝ E]`, likewise `F`). Completeness and
everything downstream additionally assume `[CompleteSpace F]`, which is genuinely
necessary (for `E ≠ 0`, `𝓢(E,F)` is complete iff `F` is). The sanity corollaries
(5a)/(5b) are specialized to `𝓢(ℝ,ℝ)` with real-valued functionals, matching what
campaign task M3 will consume.

The instances fire for concrete complete codomains, e.g.
`CompleteSpace (SchwartzMap ℝ ℝ)`, `BaireSpace (SchwartzMap ℝ ℝ)`,
`BarrelledSpace ℝ (SchwartzMap ℝ ℝ)`,
`CompleteSpace (SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)` — all by `inferInstance`.

## Deliverables and the Mathlib lemmas that carried them

### (1) Countably generated uniformity
`SchwartzMap.instIsCountablyGeneratedUniformity :
(uniformity (SchwartzMap E F)).IsCountablyGenerated`.
Route: `schwartz_withSeminorms` (`ℕ × ℕ`-indexed, hence `Countable`) gives
`WithSeminorms.firstCountableTopology`, so `(nhds 0).IsCountablyGenerated`; then
`IsUniformAddGroup.uniformity_countably_generated` upgrades this to the whole
uniformity.

### (2) Completeness — `SchwartzMap.instCompleteSpace [CompleteSpace F]`
This is the analytic heart. Route:
- `UniformSpace.complete_of_cauchySeq_tendsto` reduces (via (1)) to sequential
  completeness.
- For a Cauchy sequence `f`, each Schwartz seminorm is Cauchy-uniform
  (`cauchySeq_seminorm`, from the `WithSeminorms` uniformity basis), and
  `‖x‖^k · (∂ⁿf_i − ∂ⁿf_j)` is controlled by `SchwartzMap.seminorm ℝ k n (f_i−f_j)`
  (`norm_pow_iteratedFDeriv_sub_le`, via `SchwartzMap.le_seminorm` and additivity of
  `iteratedFDeriv`).
- The pointwise limit exists in the complete `F` (`exists_pointwise_limit`), and each
  iterated derivative converges uniformly (`exists_tendstoUniformly_iteratedFDeriv`,
  via `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto` + `cauchySeq_tendsto_of_complete`
  in the complete `ContinuousMultilinearMap` space).
- **Smoothness of the limit** is the key analytic lemma
  `contDiff_top_of_tendsto_of_tendstoUniformly`: if a sequence of `C^∞` functions
  converges pointwise and every order of iterated derivatives converges uniformly,
  the limit is `C^∞` and its iterated derivatives are those uniform limits. Proved by
  induction on the derivative order using `hasFDerivAt_of_tendstoUniformly`,
  `fderiv_iteratedFDeriv` / `iteratedFDeriv_succ_eq_comp_left`, the isometry
  `continuousMultilinearCurryLeftEquiv` (uniform-convergence transfer isolated as
  `tendstoUniformly_fderiv_iteratedFDeriv` via
  `UniformContinuous.comp_tendstoUniformly`), and finally
  `contDiff_of_differentiable_iteratedFDeriv`.
- Decay bounds pass to the limit: the Cauchy sequence is bounded in every seminorm
  (`bddAbove_seminorm`), and `le_of_tendsto'` transfers `‖x‖^k·‖∂ⁿf_i x‖ ≤ B` to the
  limit, yielding the `SchwartzMap` structure of the limit.
- Convergence in every seminorm (hence in the Schwartz topology) via
  `WithSeminorms.tendsto_nhds` + `SchwartzMap.seminorm_le_bound`, passing the
  per-seminorm Cauchy bound to the limit.

### (3) Baire — `SchwartzMap.instBaireSpace [CompleteSpace F]`
Immediate from (1)+(2): Mathlib's
`TopologicalSpace.IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable`
(a uniform space with countably generated uniformity that is complete is completely
pseudometrizable) then `BaireSpace.of_completelyPseudoMetrizable`. Because these are
instances keyed to the canonical uniformity, completeness transfers with no manual
metric.

### (4) Barrelled — `SchwartzMap.instBarrelledSpace [CompleteSpace F]`
Immediate from (3) via `BaireSpace.instBarrelledSpace` (the required
`IsTopologicalAddGroup` / `ContinuousConstSMul` instances already exist for
`SchwartzMap`).

### (5) Sanity corollaries (for task M3; verify the instances fire)
- (5a) `exists_continuous_seminorm_of_pointwise_bounded`: a pointwise-bounded family
  `𝓕 : ι → 𝓢(ℝ,ℝ) →L[ℝ] ℝ` is dominated by a single continuous seminorm `q`
  (`∀ i φ, |𝓕 i φ| ≤ q φ`). Via `WithSeminorms.banach_steinhaus` (using the barrelled
  instance) to get uniform equicontinuity, then
  `WithSeminorms.uniformEquicontinuous_iff_exists_continuous_seminorm` to extract the
  dominating seminorm.
- (5b) `continuous_iSup_abs`: an everywhere-finite countable pointwise supremum
  `φ ↦ ⨆ i, |𝓕 i φ|` of tempered functionals is continuous, via
  `Seminorm.continuous_iSup` applied to `clmSeminorm (𝓕 i) := (normSeminorm ℝ ℝ).comp (𝓕 i)`.

## Upstream-worthy observations
- The whole `(1) → (3) → (4)` ladder is essentially free from Mathlib once
  completeness is in hand; the only genuine work is (2).
- `contDiff_top_of_tendsto_of_tendstoUniformly` (smooth limit of smooth functions
  with all iterated derivatives converging uniformly) and its companion
  `tendstoUniformly_fderiv_iteratedFDeriv` are general, `SchwartzMap`-independent
  facts that Mathlib currently lacks in this packaged form; they are the natural
  upstream candidates alongside the `CompleteSpace 𝓢(E,F)` instance itself.

## Key declaration names
`SchwartzMap.instIsCountablyGeneratedUniformity`, `SchwartzMap.instCompleteSpace`,
`SchwartzMap.instBaireSpace`, `SchwartzMap.instBarrelledSpace`,
`SchwartzMap.exists_continuous_seminorm_of_pointwise_bounded`,
`SchwartzMap.continuous_iSup_abs`; helpers
`norm_pow_iteratedFDeriv_sub_le`, `cauchySeq_seminorm`, `bddAbove_seminorm`,
`tendstoUniformly_fderiv_iteratedFDeriv`,
`contDiff_top_of_tendsto_of_tendstoUniformly`,
`exists_tendstoUniformly_iteratedFDeriv`, `exists_pointwise_limit`,
`clmSeminorm`.
