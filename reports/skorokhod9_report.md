# Skorokhod campaign 9 — Aldous's tightness criterion fully discharged (two-scale architecture)

All work is in `TypeDDecouplingSkorokhodAldous.lean` (edited in place). The whole project
builds. The frozen modules (Basic / Compact / Complete / Tight / Measurable) and
`TypeDDecouplingEW.lean` were **not** modified (verified by `git diff`). No `axiom` /
`@[implemented_by]` was introduced. Mathlib imports only.

## Result

* `SkorokhodBasic.aldous_tightness`, `SkorokhodBasic.aldous_of_moment`, and
  `TypeDDecoupling.prop_aldous` are now **`sorryAx`-free**, using only the standard axioms
  `propext`, `Classical.choice`, `Quot.sound` (verified with an axiom audit).
* Their **statements are unchanged**.
* The refuted `prob_map_badSet_le` was **deleted**; the unused `measurableSet_badSet` was
  also deleted (consumer audit below).
* **Real project `sorry` count = 1**: only `thm_mitoma` (the Mitoma citation in
  `TypeDDecouplingEW.lean`). (The only other `sorry` token in the sources is inside a
  commented-out reference block in the frozen `TypeDDecouplingSkorokhodMeasurable.lean`.)

## Two refutations that shaped the architecture

1. **Task 8 (interior).** `prob_map_badSet_le` with a `δ`-independent constant is false: the
   "first bad crossing" is future-dependent and the honest union bound costs `⌈1/δ⌉`. This
   is paid by a **two-scale** invocation of the Aldous hypothesis (coarse `δ`, fine `σ`).

2. **New (boundary).** Even the two-scale bound `P(badSet εc σ) ≤ 16η₁ + 8η₂` is FALSE,
   because the `badSet` witness (which lumps the terminal crossing-gap in with the interior
   ones) is too coarse at the right endpoint. Concretely, a path that rises *gradually* to
   the `εc`-crossing level, first exceeding it within `σ` of time `1` (slope `< εc/(4σ)`),
   lies in `badSet εc σ`, yet its càdlàg modulus is small and its `aldousQ(2σ, εc/2) = 0`
   (no stopping-time increment over a `2σ`-window detects a rise spread over a wider window).
   So `P(badSet)` is not controlled by `aldousQ`, and a family concentrating such rises near
   `1` has `sup_i P_i(badSet εc σ) = 1` while being tight — refuting the single-witness bound.

   **Fix.** Split the witness into `interiorBadSet εc σ ∪ boundarySet εc σ`, where
   `boundarySet` is a *first-passage crossing* from the **deterministic** time `1 - 2σ`
   (`boundarySet εc σ = {f | crossTime skoroEval (1-2σ) εc f < 1}`). The point `1-2σ`
   (rather than `1-σ`) is essential: it catches a genuine jump arriving *exactly* at `1-σ`
   (that jump lies in `(1-2σ, 1)` and is measured against `f(1-2σ)`). Its probability IS
   controlled by `aldousQ` via the same window-overlap pigeonhole (using the first-passage
   crossing time as the second point `t₂`), and its complement pins the terminal-cell
   oscillation to `≤ 2εc`.

## The verified architecture (final lemma names / constants)

Fix `εc` (crossing threshold), increment level `εc/2`.

* **Step 2 — shift-average bound.** `prob_fiber_ge_le`: for a stopping time `τ ≤ 1`,
  `P{ω : Leb{s∈(0,2d] : εc/2 ≤ |X(τ+s)-X τ|} ≥ d/2} ≤ 4·aldousQ(2d, εc/2)` (Tonelli via
  `lintegral_lintegral_swap` + Markov via `meas_ge_le_lintegral_div`; no conditional
  expectation).
* **Step 3 — window-overlap pigeonhole.** `window_overlap_pigeonhole` (pure, deterministic;
  now with non-strict gap `t₂ - t₁ ≤ d`).
* **Crossing facts.** `crossSeq_le_one`, `crossSeq_mono`, `crossSeq_crossing_ge`,
  `crossSeq_succ_eq_crossTime`, `crossSeq_osc_le`, `crossTime_value_ge`.
* **Interior pigeonhole.** `prob_badpair_le` (strict gap), `prob_interior_pair_le`
  (`≤`-gap): each `≤ 8·aldousQ(2σ, εc/2)`.
* **Step 4b — crossing count.** `prob_crossSeq_lt_one_le`: with `q·δ > 2`,
  `P(T_q < 1) ≤ 16·η₁` (elementary `E[Y_i·1_B]` telescoping + `enn_count_arith`, a pure
  `ℝ≥0∞` division lemma). No filtration conditioning.
* **Interior assembly.** `prob_map_interiorBadSet_le`:
  `P(interiorBadSet εc σ) ≤ 16·η₁ + 8·η₂` (crossing count + union of `< q` fine gaps, the
  factor `q` paid by the `η₂/q` tolerance).
* **Boundary.** `boundarySet`, `measurableSet_boundarySet`, `measurable_crossTimeStop`,
  `prob_map_boundarySet_le`: `P(boundarySet εc σ) ≤ 8·aldousQ(2·(2σ), εc/2)`
  (first-passage from `1-2σ`, pigeonhole at the pair `(1-2σ, ρ)`, two `prob_fiber_ge_le`).
* **Boundary modulus lemma.** `cadlagModulus_le_of_not_interiorBad_boundarySet`:
  off `interiorBadSet ∪ boundarySet`, `cadlagModulus f σ ≤ 4·εc` (Case A `∉ badSet` reuses
  the kept `cadlagModulus_le_of_not_badSet`; Case B drops the last crossing and bounds the
  terminal cell by `2εc` via `∉ boundarySet`).
* **Assembly.** `aldous_tightness` (statement unchanged): witness
  `interiorBadSet εc σ ∪ boundarySet εc σ`, with `εc = ε/8` (so `4εc = ε/2 < ε`),
  `η₁ = η₂ = (η/2)/16`, coarse `δ`, `q = ⌈2/δ⌉+1`, fine `σ = min(min(d₂/4, δ), 1/4)`,
  giving `P ≤ 16η₁ + 8η₂ + 8η₂ = 16η₁ + 16η₂ = η`. All numeric constants are the honest
  accounting; the theorem's meaning is unchanged.

Every crossing time is itself an `𝓕`-stopping time (`isStoppingTime_crossSeq` from Task 8,
plus the deterministic-start first-passage `ρ`); no future-dependent index selection occurs.

## Consumer audit for the deleted `badSet` items

* `prob_map_badSet_le` — **deleted** (referenced only in explanatory docstrings now).
* `measurableSet_badSet` — **deleted** (no consumer remained).
* `badSet` and `cadlagModulus_le_of_not_badSet` — **kept**: they are now consumed by
  `cadlagModulus_le_of_not_interiorBad_boundarySet` (Case A), so they are not orphaned.

## Axiom / sorry confirmation

* `#print axioms` / axiom audit: `aldous_tightness`, `aldous_of_moment`,
  `TypeDDecoupling.prop_aldous` each depend only on `propext, Classical.choice, Quot.sound`.
* Whole project builds (`lake build`, 8063 jobs). Real `sorry` count = 1 (`thm_mitoma`).
