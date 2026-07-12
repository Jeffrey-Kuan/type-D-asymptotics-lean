# Skorokhod campaign 5 — Aldous's criterion: delivery report

New library-clean module `TypeDDecouplingSkorokhodAldous.lean` (Mathlib imports only,
registered in `lakefile.toml`). The whole project builds; every declaration below is
`sorry`-free and depends only on the standard axioms `propext, Classical.choice,
Quot.sound` (verified with `#print axioms`). The frozen files
Basic/Compact/Complete/Tight/Measurable were not modified, and `prop_aldous`
(`TypeDDecouplingEW.lean`) is untouched — all interaction with the frozen layer is via
adapters/reuse.

All results live in `namespace SkorokhodBasic`.

## Delivered statement shapes

### Tier 3 plumbing — the bridge adapter
```
theorem isTightMeasureSet_of_bdd_of_modulus_witness (S : Set (Measure Skoro))
    (hbdd : ∀ η : ℝ≥0∞, 0 < η → ∃ a : ℝ, ∀ μ ∈ S, μ {f | a ≤ supNorm f} ≤ η)
    (hmod : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ δ, 0 < δ ∧ δ < 1 ∧
        ∀ μ ∈ S, ∃ H : Set Skoro,
          {f | ε ≤ cadlagModulus f.toFun δ} ⊆ H ∧ μ H ≤ η) :
    IsTightMeasureSet S
```
Repackages Task 3's `isTightMeasureSet_of_bdd_of_modulus` so the modulus contribution
is supplied by a **measurable witness superset** `H ⊇ {f | ε ≤ w'(f,δ)}` of small mass —
exactly the shape produced by the `crossTime` construction, whose events are cylinder
measurable even though `w'` itself is not (design constraint 1). The reduction uses only
`measure_mono` (outer-measure monotonicity), so it never touches the measurability of the
`w'` level sets. This is the honest "assembly" endpoint: given the constructed measurable
good events, it yields `IsTightMeasureSet`.

### Tier 2 (path-by-path) — modulus witnesses
```
theorem cadlagModulus_le_of_partition {f : ℝ → ℝ} {δ ε : ℝ} (hε : 0 ≤ ε)
    {n : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0) (htn : t n = 1) (hn : 0 < n)
    (hmono …) (hmesh : ∀ i < n, δ < t (i+1) - t i)
    (hosc : ∀ i < n, ∀ x ∈ Set.Ico (t i) (t (i+1)), |f x - f (t i)| ≤ ε) :
    cadlagModulus f δ ≤ ε
```
A single admissible `δ`-sparse partition with left-endpoint oscillation `≤ ε` bounds `w'`
by `ε` (direct `csInf_le` against `modulusSet`).

```
theorem cadlagModulus_le_of_crossing {f : ℝ → ℝ} {δ ε : ℝ} (hε : 0 ≤ ε) {M : ℕ}
    {s : ℕ → ℝ} (hs0 : s 0 = 0) (hlast : s M < 1)
    (hmono : ∀ i < M, s i < s (i+1)) (hsep : ∀ i < M, δ < s (i+1) - s i)
    (htail : δ < 1 - s M)
    (hosc : ∀ i < M, ∀ x ∈ Set.Ico (s i) (s (i+1)), |f x - f (s i)| ≤ ε)
    (hosctail : ∀ x ∈ Set.Ico (s M) 1, |f x - f (s M)| ≤ ε) :
    cadlagModulus f δ ≤ ε
```
The crossing-times form of Tier 2 (the **tail-long case**): given `ε`-crossing points
`0 = s₀ < ⋯ < s_M < 1`, `> δ`-separated, with the final gap `1 - s_M > δ` too, and
left-endpoint oscillation `≤ ε` on each cell and on the terminal `[s_M, 1)`, the modulus
is `≤ ε`. Proof extends the partition with the node `1`.

### Tier 1 — the ε/2 split and the averaging device
```
theorem abs_ge_split {a b c ε : ℝ} (h : ε ≤ |c - a|) :
    ε / 2 ≤ |b - a| ∨ ε / 2 ≤ |b - c|
```
The Billingsley (16.24) core: if the total increment `|c-a| ≥ ε`, an intermediate value
`b` is `ε/2` from one endpoint (triangle inequality).

```
theorem averaging_split_bound (P : Measure Ω) {A : Set Ω} {δ₀ e : ℝ}
    {u v : ℝ → Ω → ℝ}
    (hsplit : ∀ δ ∈ Set.Icc δ₀ (2*δ₀),
      A ⊆ {ω | e/2 ≤ |u δ ω|} ∪ {ω | e/2 ≤ |v δ ω|}) :
    ENNReal.ofReal δ₀ * P A ≤
      ∫⁻ δ in Set.Ioc δ₀ (2*δ₀),
        (P {ω | e/2 ≤ |u δ ω|} + P {ω | e/2 ≤ |v δ ω|}) ∂volume
```
Billingsley's averaging device (16.24)ff as a **raw interval Lebesgue integral**
(`∫⁻ … ∂volume` over `Set.Ioc`), *not* `uniformOn`. On the consecutive-crossing event `A`,
the `ε/2` split makes `A` sit inside the union of the two increment events for every shift
`δ ∈ [δ₀, 2δ₀]`; averaging over `δ` (length `δ₀`) gives the bound. The proof uses only
`measure_mono`, `measure_union_le`, `setLIntegral_mono'`, `setLIntegral_const`,
`Real.volume_Ioc` — no measurability of `A` or of `u,v` is required for this direction.

### Crossing / process infrastructure
```
theorem crossTime_osc_le (X : ℝ → Ω → ℝ) (s ε : ℝ) (ω : Ω) {t : ℝ}
    (hst : s < t) (ht : (t : WithTop ℝ) < crossTime X s ε ω) :
    |X t ω - X s ω| ≤ ε
```
The fundamental crossing property: before the first `ε`-crossing after `s`, the increment
from `X s` stays `≤ ε`. This is the pathwise fact that supplies the `hosc`/`hosctail`
hypotheses of `cadlagModulus_le_of_crossing` for the `crossTime` iterates.

```
theorem Skoro.rightContinuous (f : Skoro) (t : ℝ) :
    ContinuousWithinAt f.toFun (Set.Ici t) t
```
Every `Skoro` path is right-continuous at **every** real point (càdlàg on `[0,1)`,
flatness elsewhere) — exactly the `hrc` hypothesis of Task 3's `isStoppingTime_crossTime`,
so the crossing times of a `Skoro`-valued random element are stopping times of the
right-continuous filtration.

### The Aldous quantity and the moment corollary
```
def aldousQ (P : Measure Ω) (X : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ m) (d e : ℝ) : ℝ≥0∞ :=
  ⨆ (τ : Ω → ℝ) (_ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ)))
    (_ : ∀ ω, τ ω ≤ 1) (δ : ℝ) (_ : 0 ≤ δ) (_ : δ ≤ d),
    P {ω | e ≤ |X (min (τ ω + δ) 1) ω - X (τ ω) ω|}

theorem aldousQ_mono_shift … {d₁ d₂ e} (h : d₁ ≤ d₂) :
    aldousQ P X 𝓕 d₁ e ≤ aldousQ P X 𝓕 d₂ e
```
Aldous's `α(d,e) = sup_{τ≤1, δ≤d} P(|X(τ+δ) − X(τ)| ≥ e)`, with the shift truncated at `1`
via `min (τ+δ) 1` (the truncation-at-`1` convention). `τ` is real-valued and required to be
a stopping time under the `WithTop ℝ` coercion, matching `IsStoppingTime`. Monotone in the
shift budget `d`.

```
theorem prob_ge_le_second_moment (P : Measure Ω) (Y : Ω → ℝ)
    (hY : AEMeasurable Y P) {e : ℝ} (he : 0 < e) :
    P {ω | e ≤ |Y ω|} ≤ (∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P) / ENNReal.ofReal (e ^ 2)
```
The Chebyshev step for `aldous_of_moment`: a second-moment bound on an increment controls
its large-deviation probability. Applied to `Y = X(τ+δ) − X(τ)` this turns the uniform
`E|·|² ≤ Cδ` hypothesis into the Aldous condition (ii) — i.e. the "by Markov afterwards"
route of the brief.

## Where the every-cell `> δ` convention bit (the terminal-cell obstruction)

The Compact-file `modulusSet` requires **every** cell to have length `> δ` (documented
convention, slightly stronger than Billingsley). Combined with the fact that `cadlagModulus`
measures the **left-endpoint** oscillation, this makes the naive "merge the short terminal
cell into the previous one" step **false in general**, which is why the pathwise Tier-2
lemma is stated in the tail-long case (`htail : δ < 1 - s M`) rather than with an
unconditional `2ε`.

Concrete obstruction (found while formalizing). Take `f` = `0` on `[0, 1−δ/2)` jumping to
`100` at `1−δ/2`, `ε = 1`. The single `ε`-crossing is at `s₁ = 1−δ/2`, with gap
`s₁ − 0 = 1−δ/2 > δ`; there is no crossing afterwards, so the left-endpoint oscillation is
`≤ ε` on `[0, s₁)` and on `[s₁, 1)`. But the terminal gap `1 − s₁ = δ/2 < δ`, so `1` cannot
be added as a node. Merging `[s₁,1)` into `[0,s₁)` gives the cell `[0,1)`, on which
`|f(x) − f(0)| = 100` at `x = s₁`: the crossing at `s₁` is an arbitrarily large **jump**, so
the merged left-endpoint oscillation is `≈ 100`, not `≤ 2ε`. Indeed **no** `δ`-sparse
partition can isolate a jump lying within `δ` of the endpoint `1`, so `w'_f(δ) ≈ 100` for
this `f`. Hence "few `δ`-separated crossings ⇒ `w'(δ) ≤ 2ε`" is genuinely false without an
extra boundary condition.

Resolution (Billingsley's actual argument): the tail jump within `δ` of `1` is not handled
by the modulus partition at all — it is controlled by a **separate application of the Aldous
increment at the boundary**, i.e. `α` with `τ` = last crossing and the shift truncated at `1`
(exactly the `min (τ+δ) 1` in `aldousQ`). So the correct Tier-2 → Tier-3 route uses
`cadlagModulus_le_of_crossing` on the good (tail-long) event and adds one boundary `α`-term
for the tail-short event, rather than forcing a `2ε` merge. The `2ε` in the brief is the
sum of these two `ε`-level contributions, not a merged single-cell bound.

## Remaining Billingsley §16 gaps (as predicted in the brief)

1. **Averaging bookkeeping — the `v`-term reduction to `α`.** `averaging_split_bound`
   delivers `δ₀·P(A) ≤ ∫ (P(Uδ) + P(Vδ)) dδ` soundly. Reducing the right-hand integrals to
   `2δ₀·α(2δ₀, ε/2)` is immediate for the `u`-term (`Uδ = {ε/2 ≤ |X(τₖ+δ) − X(τₖ)|}`, and
   `τₖ` is a stopping time `≤ 1`, `δ ≤ 2δ₀`, so `P(Uδ) ≤ α(2δ₀, ε/2)` for each `δ`). It is
   **not** immediate for the `v`-term `Vδ = {ε/2 ≤ |X(τₖ+δ) − X(τ_{k+1})|}`: writing
   `τₖ+δ = τ_{k+1} + (τₖ+δ − τ_{k+1})` involves an **`ω`-dependent shift**, so `P(Vδ) ≤ α`
   holds only after the Fubini swap (`intervalIntegral_integral_swap` /
   `lintegral_prod`) and an `ω`-dependent change of the integration variable. That change of
   variables needs the **joint (space–time) measurability** of `(δ, ω) ↦ X(τ(ω)+δ, ω)` — the
   evaluation of a càdlàg path at a jointly varying time. Task 4 established measurability of
   evaluation at a *fixed* time (`measurable_eval`); the joint version (progressive
   measurability of the càdlàg coordinate process) is a further, substantial result and is
   the principal residual for the full Tier-1 bound
   `P(τ_{k+1} − τₖ ≤ δ₀, τ_{k+1} ≤ 1) ≤ C·α(2δ₀, ε/2)`.

2. **Truncation-at-`1` edge cases.** The `min (τ+δ) 1` truncation in `aldousQ` interacts
   with the boundary tail-term above; handling it cleanly is part of the same joint-space-time
   evaluation gap.

3. **Full `aldous_tightness` assembly.** With Tiers 1–2 available, the assembly is exactly
   `isTightMeasureSet_of_bdd_of_modulus_witness`: build, for each `ε, η`, the measurable good
   event (few `crossTime` crossings + `> δ` separation, from `crossTime_osc_le` +
   `cadlagModulus_le_of_crossing`) with small complement, then feed it to the adapter. The
   only genuinely missing input is item 1 (the `v`-term reduction and the induction bounding
   the crossing count), so the assembly is one lemma away from the full criterion.

## Fallback-ladder position

Rungs achieved: the Tier-3 **assembly bridge** (adapter) is complete; **Tier 2** is complete
in its correct (tail-long) pathwise form together with the crossing-oscillation and
right-continuity/stopping-time infrastructure; **Tier 1**'s pathwise split and the raw
interval-integral averaging device are complete, with the `aldous_of_moment` Chebyshev step.
The single residual is the joint space–time measurability enabling the Fubini/`ω`-shift
reduction of the averaging integral to `α` (item 1), which is the sole obstacle to the full
`aldous_tightness`. No incorrect statements and no placeholder `sorry`s were delivered.
