# Skorokhod campaign 6 — progressive measurability + Aldous assembly: delivery report

All new work extends `TypeDDecouplingSkorokhodAldous.lean` in place (Mathlib imports only,
this campaign's live file). The whole project builds; every new declaration is `sorry`-free
and depends only on the standard axioms `propext, Classical.choice, Quot.sound` (verified
with `#print axioms` / the verifier). The frozen modules Basic/Compact/Complete/Tight/
Measurable were not modified, and `prop_aldous` (`TypeDDecouplingEW.lean`) is untouched.

All results live in `namespace SkorokhodBasic`.

## Tier 1 (must-have) — joint measurability of the canonical process — COMPLETE

Statement shape: a **bespoke joint-measurability lemma** on `ℝ × Ω` (not `ProgMeasurable`),
as the brief anticipated. Mathlib's `ProgMeasurable` packaging is geared to
`StronglyAdapted.progMeasurable_of_continuous` (continuous paths); no right-continuous
analogue was found, and Tier 2 consumes the bespoke product-measurability form directly, so
that is what was delivered.

```
def dyadicApprox (X : Ω → Skoro) (n : ℕ) (p : ℝ × Ω) : ℝ :=
  (X p.2).toFun (⌈p.1 * (2 : ℝ) ^ n⌉ / (2 : ℝ) ^ n)

theorem measurable_dyadicApprox {X : Ω → Skoro} (hX : Measurable X) (n : ℕ) :
    Measurable (dyadicApprox X n)

theorem tendsto_dyadicApprox {X : Ω → Skoro} (p : ℝ × Ω) :
    Tendsto (fun n => dyadicApprox X n p) atTop (𝓝 ((X p.2).toFun p.1))

theorem measurable_eval_prod {X : Ω → Skoro} (hX : Measurable X) :
    Measurable (fun p : ℝ × Ω => (X p.2).toFun p.1)

theorem measurable_eval_shift {X : Ω → Skoro} (hX : Measurable X)
    {τ : Ω → ℝ} (hτ : Measurable τ) :
    Measurable (fun p : ℝ × Ω => (X p.2).toFun (min (τ p.2 + p.1) 1))
```

Route (exactly the brief's): the dyadic right-endpoint approximant `X^n(s,ω) =
X(ω)(⌈s·2ⁿ⌉/2ⁿ)`. Each `X^n` is jointly measurable because the integer ceiling `⌈s·2ⁿ⌉ : ℤ`
is measurable (`Int.measurable_ceil`) and takes values in the **countable** space `ℤ`, on
each of which the map is a fixed-time evaluation, measurable by Task 4's `measurable_eval`;
this is packaged via `measurable_from_prod_countable_right`. Pointwise convergence
`X^n(s,ω) → X(ω)(s)` holds for **every** `(s,ω)` (all of `ℝ`, no truncation needed):
`⌈s·2ⁿ⌉/2ⁿ ≥ s` and `→ s`, i.e. the approximants decrease to `s` strictly from the right,
so right-continuity (`Skoro.rightContinuous`, Task 5) gives the limit. `measurable_eval_prod`
is then the pointwise limit of measurable functions. The consumer form
`measurable_eval_shift` is the composition with the measurable time map
`(δ,ω) ↦ (min (τ(ω)+δ) 1, ω)`, which is the integrand Tier 2 consumes.

## Tier 2 — the `v`-term reduction to `α` (Task 5's sole residual) — COMPLETE

```
theorem setLIntegral_Ioc_add_right (φ : ℝ → ℝ≥0∞) (a b c : ℝ) (hφ : Measurable φ) :
    ∫⁻ δ in Set.Ioc a b, φ (δ + c) ∂volume = ∫⁻ s in Set.Ioc (a+c) (b+c), φ s ∂volume

theorem prob_shift_le_aldousQ (P : Measure Ω) (X : Ω → Skoro) (𝓕 : Filtration ℝ m)
    {τ} (hτ : IsStoppingTime …) (hτ1 : ∀ ω, τ ω ≤ 1) {d e s} (hs0 : 0 ≤ s) (hsd : s ≤ d) :
    P {ω | e ≤ |(X ω).toFun (τ ω + s) - (X ω).toFun (τ ω)|}
      ≤ aldousQ P (fun t ω => (X ω).toFun t) 𝓕 d e

theorem vterm_integral_bound (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → Skoro)
    (hX : Measurable X) (𝓕 : Filtration ℝ m) {δ₀ e}
    {τ} (hτ) (hτ1 : ∀ ω, τ ω ≤ 1) (hτmeas : Measurable τ)
    {a} (ha : Measurable a) (ha0 : ∀ ω, -δ₀ ≤ a ω) (ha1 : ∀ ω, a ω ≤ 0) :
    ∫⁻ δ in Set.Ioc δ₀ (2 * δ₀),
        P {ω | e ≤ |(X ω).toFun (τ ω + a ω + δ) - (X ω).toFun (τ ω)|} ∂volume
      ≤ ENNReal.ofReal (2 * δ₀) * aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * δ₀) e
```

This is exactly the reduction identified in the Task-5 report (gap item 1). The `v`-term
event `{e ≤ |X(τ+a+δ) - X(τ)|}` with the **ω-dependent shift** `a = τₖ − τₖ₊₁` (base
`τ = τₖ₊₁`) is averaged over `δ ∈ (δ₀, 2δ₀]`. Proof: rewrite each probability as an
ω-lintegral of an indicator (integrand jointly measurable by Tier 1), Tonelli swap
(`lintegral_lintegral_swap`; `P` finite ⇒ sfinite, `volume.restrict` sfinite), the ω-wise
translation `δ ↦ δ + a(ω)` (`setLIntegral_Ioc_add_right`, Lebesgue translation invariance)
sending the range `(δ₀, 2δ₀]` into `[δ₀+a(ω), 2δ₀+a(ω)] ⊆ (0, 2δ₀]` (using `-δ₀ ≤ a ≤ 0`),
restrict the set to `(0, 2δ₀]`, swap back, and apply `prob_shift_le_aldousQ` at each fixed
shift `s ∈ (0, 2δ₀]`.

### Change-of-variable subtleties (the brief's likely spot)

* **No null-set issue under the shift.** The change of variable is a *pure translation*
  `s = δ + a(ω)`, whose pushforward of Lebesgue measure is Lebesgue measure exactly
  (`measurePreserving_add_right`), so there are no null sets to discard — the translation
  identity is a genuine equality, not merely a.e. The only inequality is the deterministic
  set inclusion `[δ₀+a(ω), 2δ₀+a(ω)] ⊆ (0, 2δ₀]`.
* **Truncation-at-`1` via right flatness.** The Aldous quantity uses the truncated increment
  `X(min(τ+s, 1)) − X(τ)`, whereas the translated integrand carries the untruncated
  `X(τ+s)`. These coincide for **every** `s` because `Skoro` paths are flat on `[1, ∞)`
  (`flatR`): if `τ+s ≥ 1` then `X(τ+s) = X(1) = X(min(τ+s, 1))`; otherwise `min = τ+s`.
  This is exactly `prob_shift_le_aldousQ`, so the `min (τ+δ) 1` convention in `aldousQ`
  integrates cleanly with the boundary and needs no separate edge-case handling here.
* **Global-vs-event shift bound.** `vterm_integral_bound` requires `-δ₀ ≤ a ≤ 0` for *all*
  `ω`. In the assembly this holds only on the good event `A`; it is supplied by applying the
  lemma to `P.restrict A` with the **clamped** shift `a' = max (-δ₀) (min (σ-τ) 0)`, which
  equals the true gap on `A` and satisfies the global bounds everywhere (see
  `consecutive_crossing_bound`).

## Tier 3 — assembly components — DELIVERED (see status below)

```
theorem le_aldousQ_of_stoppingTime …            -- the u-term pointwise bound P(…) ≤ α
theorem uterm_integral_bound …                  -- ∫ P(Uδ) dδ ≤ δ₀ · α(2δ₀, e)
theorem aldousQ_mono_measure (hPQ : P ≤ Q) …    -- monotonicity of α in the measure
theorem consecutive_crossing_bound …            -- δ₀·P(A) ≤ 3δ₀·α(2δ₀, ε/2)
theorem aldousQ_le_of_second_moment …           -- α(d,e) ≤ M / e²   (aldous_of_moment)
```

* `consecutive_crossing_bound` is the heart of Aldous's argument: for stopping times
  `σ ≤ τ ≤ 1` with gap `≤ δ₀` on a measurable event `A`, and the `ε/2`-increment split
  holding for every shift `δ ∈ [δ₀, 2δ₀]`, it proves `δ₀·P(A) ≤ 3δ₀·α(2δ₀, ε/2)`. It is
  assembled from the Task-5 averaging device `averaging_split_bound` (applied to
  `P.restrict A`), the `u`-term bound (`prob_shift_le_aldousQ`), the `v`-term bound
  (`vterm_integral_bound` with the clamped shift `a'`), and `aldousQ_mono_measure`
  (`P.restrict A ≤ P`). The `2ε`/`3δ₀` constant is the sum of the `u`- and `v`-term
  `ε/2`-level contributions, matching the report's resolution (no forced single-cell merge).
* `aldousQ_le_of_second_moment` is the `aldous_of_moment` route: a uniform second-moment
  bound `E|X(min(τ+δ,1)) − X(τ)|² ≤ M` over stopping times `τ ≤ 1` and shifts `δ ≤ d` gives
  `α(d,e) ≤ M/e²`, via `prob_ge_le_second_moment` inside the supremum. If `M = M(d) → 0`
  this delivers Aldous's condition (ii).

## Final status of `aldous_tightness` / `aldous_of_moment`

* The `aldous_of_moment` **mechanism** is complete as `aldousQ_le_of_second_moment` (the
  Chebyshev/Markov control of the Aldous quantity by a second moment).
* The end-to-end `IsTightMeasureSet` theorem `aldous_tightness` is **not** assembled into a
  single named result. All of its analytic inputs are now proved and sorry-free — the
  Tier-3 bridge adapter `isTightMeasureSet_of_bdd_of_modulus_witness` (Task 5), the pathwise
  modulus bound `cadlagModulus_le_of_crossing` (Task 5), and the per-crossing probability
  estimate `consecutive_crossing_bound` (this campaign). What remains is purely combinatorial
  bookkeeping: (i) the induction over the iterated `crossTime` sequence bounding the number
  of `ε`-crossings and their `> δ`-separation, (ii) the boundary/tail term at time `1`
  (controlled by the `min (τ+δ) 1` Aldous increment already encoded in `aldousQ`), and
  (iii) constructing the measurable good event and feeding it to the adapter. This induction
  is the sole remaining residual; it introduces no new analytic content beyond the delivered
  lemmas.

## Fallback-ladder position

Achieved: **Tier 1 (must-have) complete**, **Tier 2 (Task 5's documented residual)
complete**, and the principal **Tier 3 components** (`consecutive_crossing_bound`,
`aldousQ_le_of_second_moment`, plus supporting `aldousQ_mono_measure` / `uterm_integral_bound`)
complete. This strictly exceeds the "Tiers 1–2 with assembly as sole documented residual"
rung. The remaining crossing-count induction for the single packaged `aldous_tightness`
statement is documented above. No incorrect statements and no placeholder `sorry`s were
introduced.
