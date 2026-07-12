# Mitoma campaign, task 3c — uniform dual-ball confinement

**Status: full delivery.** One new self-contained file
`TypeDDecouplingMitomaCore.lean` (imports `Mathlib`, plus the campaign files
`TypeDDecouplingHermiteSobolev` (M3b) and `TypeDDecouplingSchwartzDual` (M2),
which transitively bring in M3a Hermite and M1 Fréchet). No existing project file
was edited; the new module is registered in `lakefile.toml`. The whole project
builds (8068 jobs). There is no `axiom`/`sorry`; the three headline theorems
`charFunctional_bound` (C1), `gaussian_confinement_bound` (C2) and
`mitoma_confinement` (C3) each depend only on the standard axioms `propext`,
`Classical.choice`, `Quot.sound` (checked with the axiom scanner).

All declarations live in `namespace TypeDDecouplingMitomaCore`. The probabilistic
results are in a `section Probability` with data
```
{ι T : Type*} [Countable T] [Nonempty T]
{Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
(P : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
(Z : (i : ι) → T → Ω i → SchDual)
```
`SchDual = 𝓢(ℝ,ℝ) →Lₚₜ[ℝ] ℝ` is M2's pointwise dual, and `T` is the abstract
countable time set (the brief's `D`).

## (C0) Hypotheses format

Measurability of evaluations is passed as
`hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ)`.

The quantitative hypothesis (H), per-`φ` uniform sup-tightness, is phrased through
the measurable countable-union events (no conditionally-complete `⨆` over a
possibly-unbounded family is taken inside a measure):
```
H : ∀ (φ : 𝓢(ℝ,ℝ)) (ε : ℝ), 0 < ε → ∃ a : ℝ, 0 < a ∧
      ∀ i, (P i) {ω | ∃ t : T, a < |Z i t ω φ|} ≤ ENNReal.ofReal ε
```
This is equivalent to the source's `sup_i P_i(sup_D |⟨Z,φ⟩| > a) ≤ ε`
(`sup_i (·) ≤ ε ↔ ∀ i, (·) ≤ ε`, and `sup_D |·| > a ↔ ∃ t, |·| > a`).
`measurableSet_exists_gt` provides the promised small measurability lemma.

## (C1) The functional `M` and its regularity (JMSJ Lemma 1)

For a fixed real `ε` the score is bounded inside a countable sup, so no `⨆`
finiteness issue arises:
```
bracketFun Z i φ ω = ⨆ t : T, |Z i t ω φ| / (1 + |Z i t ω φ|)
Mi P Z i φ = ∫ ω, bracketFun Z i φ ω ∂(P i)
Mfun P Z φ = ⨆ i, Mi P Z i φ
```
Properties 1)–4) (source p.630):
* `Mfun_nonneg`, `Mfun_le_one`, `Mfun_neg` (property 1);
* `Mfun_subadditive` (property 2), from the pointwise `frac_abs_add_le`
  `|a+b|/(1+|a+b|) ≤ |a|/(1+|a|) + |b|/(1+|b|)`;
* `lowerSemicontinuous_Mfun` (property 3): a `⨆`-of-LSC (`lowerSemicontinuous_ciSup`,
  uniform bound `1`); each `M_i` is LSC via Fatou over the countable sup
  (`lintegral_bracketFun_liminf_le` + `Mi_eq_lintegral_toReal`);
* `Mfun_smul_tendsto_zero` (property 4): **derived from (H)**, not from sample
  continuity, exactly as the brief instructs — given `η`, pick `a` with
  `P_i(bad) ≤ η/2`; for `n ≥ 2a/η` the integrand is `≤ η/2 + 1_bad`, so
  `M(φ/n) ≤ η`.

**Xia's lemma** is proved (`xia_lemma`), a Baire-category argument on the Fréchet
space `𝓢(ℝ,ℝ)` (M1's `BaireSpace` instance): for `M` nonnegative, even,
subadditive, lower-semicontinuous with `M(φ/n) → 0`,
`C_k = ⋂_{m≥k} {φ | M(φ/m) ≤ ε'}` are closed with union `univ`, so
`nonempty_interior_of_iUnion_of_closed` yields an interior point `φ₀`; the
subadditivity/evenness bookkeeping gives `M ≤ 2ε'` on a scaled neighbourhood of
`0`, i.e. `ContinuousAt M 0`. Applied to `M` this is `Mfun_continuousAt_zero`.
`exists_sobolev_ball_of_continuousAt_zero` converts the resulting Schwartz
neighbourhood into a Hermite–Sobolev ball, using M3b's two-sided domination
(`seminorm_le_sobolev`, assembled into `exists_sobolev_dominates_finset_sup`,
plus `sobolevSeminorm_mono`) and the Schwartz nbhd basis
`WithSeminorms.mem_nhds_iff`.

**Conclusion (2.1)** — `charFunctional_bound`:
```
∃ (q : ℕ) (δ : ℝ), 0 < δ ∧ ∀ φ,
  (⨆ i, ∫ ω, (⨆ t, ‖1 - Complex.exp (I * (Z i t ω φ : ℂ))‖) ∂(P i))
      ≤ ε + 2 * (sobolevSeminorm q φ)^2 / δ^2 .
```
The source's proof is transcribed: `δ₂ = min δ₁ ((-1+√(1+ε))/2)` with the
identity `δ₂(1+δ₂) ≤ ε/4`; a Markov step `measure_exists_gt_le_Mi`
(`(a/(1+a))·P_i(∃t,a<|⟨Z,φ⟩|) ≤ M_i`); and the `Ω`-split into
`{sup_D|⟨Z,φ⟩| < δ₂}` and its complement (`charFunctional_bound_per_i`).
For the small term we use `‖1 - e^{is}‖ ≤ |s|` (`norm_one_sub_exp_le`), so the
source's `δ₁` is `ε/2`.

## (C2) Gaussian averaging (JMSJ Lemma 2, (2.4)–(2.9))

With `q, δ` from (C1) and `r = q+1`, `S = Sconst q (q+1) = ∑' j, ‖e^r_j‖_q²`
(finite by M3b's `hermiteSobolev_hs_summable`), the confinement partial sums are
```
Qpart Z r N i t ω = ∑ j ∈ Finset.range N, (Z i t ω (hermiteSobolevVec r j))^2
```
(`Qpart_eq_coeff_form` rewrites this as `∑_{n<N} (n+1)^{-2r} ⟨Z,h_n⟩²`).
The bad set is the countable-sup event `{ω | ∃ t N, C² < Qpart}`.
`gaussian_confinement_bound`:
```
∃ (q : ℕ) (δ : ℝ), 0 < δ ∧ ∀ C, 0 < C → ∀ i,
  ((P i) {ω | ∃ t N, C² < Qpart Z (q+1) N i t ω}).toReal
      ≤ badrikianConst * (ε + (2/δ²) * (Sconst q (q+1) / C²)) ,
```
`badrikianConst = √e / (√e − 1)`. The transcription of (2.5)–(2.9):
* monotone limit in `N` (`Qpart_mono`, `Monotone.measure_iUnion`, `toReal_iSup`);
* Badrikian/Markov (`badrikian_indicator`), using
  `badrikianConst⁻¹ = 1 − e^{−1/2}` and the smoothed functional
  `Wfun = ⨆_t (1 − e^{−Q_N(t)/2C²})`;
* the product-Gaussian identity
  `integral_cos_gaussPi` (`∫ cos(∑ y_j u_j) dγ_n = e^{−∑u_j²/2C²}`, from
  `charFun_gaussianReal` and `integral_fintype_prod_eq_prod`), hence
  `one_sub_exp_le_integral_gaussPi` (`1 − e^{−∑u²/2C²} ≤ ∫ ‖1 − e^{i∑y_ju_j}‖ dγ_n`);
* Fubini (`integral_integral_swap`) and (C1) applied at each `φ_y = ∑_{j<N} y_j e^r_j`
  (`phiY`, `schDual_phiY`), together with the Gaussian second-moment computation
  `integral_sobolevSq_phiY` (`∫ ‖φ_y‖_q² dγ_n = (1/C²) ∑_{j<N} ‖e^r_j‖_q²`), which
  rests on `gaussPi_moment` (`∫ y_j y_k dγ_n = δ_{jk}/C²`) and the Hilbertian
  `q`-inner product realised through M3b's `sobolevLp : 𝓢 → ℓ²`.
The core `∫ W_N ≤ ε + (2/δ²)(S/C²)` is `integral_Wfun_le`.

## (C3) The confinement theorem — `mitoma_confinement`

```
∀ η > 0, ∃ (q : ℕ) (B : ℝ), 0 < B ∧
  IsCompact (polarBall (B.toNNReal • sobolevSeminormB (q+1))) ∧
  ∀ i, ((P i) {ω | ∃ t, Z i t ω ∉ polarBall (B.toNNReal • sobolevSeminormB (q+1))}).toReal ≤ η .
```
`sobolevSeminormB r` is the Hermite–Sobolev seminorm bundled as a genuine
`Seminorm ℝ 𝓢(ℝ,ℝ)` (pulled back from the `ℓ²` norm along the linear map
`sobolevLM`, `sobolevSeminormB_apply : sobolevSeminormB r f = sobolevSeminorm r f`);
it is continuous (`continuous_sobolevSeminormB`), so the polar ball is compact by
M2's `isCompact_polarBall`. The confinement inclusion is purely deterministic:
`schDual_mem_polarBall_of_Qpart_le` shows that if every partial sum
`∑_{n<N} (n+1)^{-2(q+1)} ⟨F,h_n⟩² ≤ C²` then `|F φ| ≤ C ‖φ‖_{q+1}` for all `φ`,
via the seminorm-convergent Hermite expansion in `𝓢` (`hermitePartial_tendsto`,
`schDual_apply_tendsto`) and the weighted Cauchy–Schwarz partial-sum bound
`abs_schDual_partial_le`. Hence the good event of (C2) is contained in the
confinement event; `measure_mono` + `ENNReal.toReal_mono` and the choices
`ε = η/(2·badrikianConst)`, `C` large give `≤ η`. `B = C`, `r = q+1`. The event
is a countable-sup event, so no σ-algebra on `SchDual` is required (`measure_mono`
handles the set inclusion directly).

## Constants and deviations from the sources

* **Constants transcribed verbatim:** `badrikianConst = √e/(√e−1)`, the
  `δ₂ = min(δ₁, (-1+√(1+ε))/2)` bookkeeping (`δ₂(1+δ₂) ≤ ε/4`), and the
  `Ω`-split. `δ₁ = ε/2` because `‖1−e^{is}‖ ≤ |s|` was used directly.
* **Property 4 derivation:** as the brief instructs, `M(φ/n) → 0` is derived from
  (H), replacing the source's use of sample continuity.
* **Formalization-driven, mathematically equivalent choices** (sanctioned by the
  brief's Remark (1), which fixes only the *form* of (C3)):
  - Events use the countable-union form `{∃ t, …}` / `{∃ t N, …}` instead of
    `{sup_D … > a}`, avoiding junk values of `⨆` over possibly-unbounded families
    while denoting the same sets; `M`'s integrand keeps the `⨆` inside `[0,1]`.
  - `Q` is packaged through its increasing partial sums `Qpart`; the good event is
    `∀ t N, Qpart ≤ C²`, equivalent to `sup_D Q ≤ C²`.
  - The Hermite–Sobolev seminorm is bundled as `sobolevSeminormB` via `ℓ²` so that
    `isCompact_polarBall` applies to a genuine `Seminorm`.
  - The seminorm-convergent Hermite expansion `φ = ∑_j ⟨φ,h_j⟩ h_j` in the Schwartz
    topology (needed for (C3)) was proved here (`hermitePartial_tendsto`), since M3b
    supplied only the pointwise expansion; it is obtained from M3b's tail estimate
    `sobolev_tail_tendsto` and two-sided domination.
* No constant needed to be moved beyond these; the architecture matched the primary
  sources without any transcription bug.

## Key declarations for downstream (M3d)

* (C1) `charFunctional_bound`
* (C2) `gaussian_confinement_bound`
* (C3) `mitoma_confinement`

with supporting `Qpart`, `phiY`, `Sconst`, `badrikianConst`, `Wfun`,
`sobolevSeminormB`, `schDual_mem_polarBall_of_Qpart_le`, `xia_lemma`,
`Mfun`/`Mi`/`bracketFun`, and the Gaussian toolkit
`gaussPi`, `gaussPi_moment`, `integral_cos_gaussPi`,
`one_sub_exp_le_integral_gaussPi`, `integral_sobolevSq_phiY`.
