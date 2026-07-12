# Skorokhod campaign 8 — Item (1) discharged; `prob_map_badSet_le` shown false as stated

All work is in `TypeDDecouplingSkorokhodAldous.lean` (extended in place). The whole project
builds. No `axiom` / `@[implemented_by]` was introduced. The frozen modules
(Basic / Compact / Complete / Tight / Measurable) were **not** modified.

## Summary

* **Item (1) — fully discharged (standard axioms only).** Crossing times iterated *from a
  stopping time* are stopping times, and hence every `crossSeq` iterate is an `𝓕`-stopping
  time and Borel-measurable. New, proved, `sorryAx`-free lemmas (see below).
* **Item (2) / the assembly — a genuine obstruction was found.** The residual
  `prob_map_badSet_le` as written — with a **universal** constant (`4`), i.e.
  `(P.map X)(badSet ε δ) ≤ C · aldousQ P proc 𝓕 (2δ) (ε/2)` with `C` independent of `δ` —
  is **false**. A rigorous counterexample (below) shows the ratio
  `P(badSet ε δ) / aldousQ(2δ, ε/2)` is unbounded (it grows like `⌈1/δ⌉`). Consequently the
  `badSet`/crossing architecture cannot close `aldous_tightness` via a single-scale `aldousQ`
  bound, and the residual is left as a **documented** `sorry` (per the brief's fallback
  ladder: "treat a statement that cannot be proved as a statement to fix, not to force").

## Item (1): the new proved lemmas

All in `namespace SkorokhodBasic`, all `sorryAx`-free (verified with `#print axioms`:
`isStoppingTime_crossSeq`, `measurable_crossSeq` depend only on
`propext, Classical.choice, Quot.sound`).

1. `measurable_eval_countable_time` — evaluating an adapted process at a countably-valued,
   `𝓕 v`-measurable time bounded by `v` is `𝓕 v`-measurable (case on the countable value).
2. `measurable_dyadicCeil_min` — the right-dyadic ceiling `⌈σ·2ⁿ⌉/2ⁿ` of a stopping time
   `σ`, clamped to `≤ v`, is `𝓕 v`-measurable.
3. `measurable_stoppedValue_min` — for an adapted, per-path right-continuous process `Y` and a
   stopping time `σ`, the clamped stopped value `ω ↦ Y (min (σ ω) v) ω` is `𝓕 v`-measurable.
   Proof: dyadic approximation of `σ` from the right (`σₙ = ⌈σ·2ⁿ⌉/2ⁿ ↓ σ`), each clamped
   value `𝓕 v`-measurable by (1)+(2), and right-continuity gives the pointwise limit
   (`measurable_of_tendsto_metrizable'`). This is the substitute for Mathlib's
   `progMeasurable_of_continuous`, which requires *continuous* (not merely càdlàg) paths.
4. `measurableSet_stoppingTime_lt` — `{σ < q}` is `𝓕 v`-measurable when `q ≤ v`.
5. `measurableSet_crossTime_le_of_stoppingTime` — the measurable-set form of the crossing
   *after a stopping time*: `{ω | crossTime Y (σ ω) ε ω ≤ t}` is `𝓕.rightCont t`-measurable.
   Same rational reduction as the frozen `crossTime_le_iff` / `measurableSet_crossTime_le`,
   with the `ω`-dependent start `σ ω` and the stopped value `Y (σ ω) ω` handled by (3)+(4).
6. `isStoppingTime_crossTime_of_stoppingTime` — the crossing after a stopping time is a
   stopping time of the right-continuous augmentation (immediate from (5)).
7. `isStoppingTime_min_untopD_one` — clamping a `WithTop ℝ`-valued stopping time by
   `min (·.untopD 1) 1` (exactly the `crossSeq` recursion step) gives an `ℝ`-valued stopping
   time.
8. `isStoppingTime_crossSeq` — **the brief's Item (1) conclusion**: for a measurable càdlàg
   `X` adapted to a right-continuous filtration (`hrc : 𝓕.rightCont = 𝓕`), every iterate
   `fun ω => crossSeq ε (X ω) k` is an `𝓕`-stopping time. Induction on `k` from (6)+(7).
9. `measurable_crossSeq` — every iterate `fun ω => crossSeq ε (X ω) k` is Borel-measurable
   (the plain-measurability corollary consumed by `consecutive_crossing_bound`).

With (8)+(9), `consecutive_crossing_bound` can now be applied at every crossing pair
`(crossSeq k, crossSeq (k+1))` — exactly what the brief's Item (1) was meant to unlock.

## The obstruction: `prob_map_badSet_le` is false as stated

Statement under scrutiny:
`(P.map X)(badSet ε δ) ≤ 4 · aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2δ) (ε/2)`.

### Counterexample (no universal constant is possible)

Work with the process's own natural right-continuous filtration. Fix a small `δ` and place
`K` up-crossings (jumps of size `> ε`) at `K` **unpredictable** random times, pairwise
`> 2δ` apart (unpredictable = before a jump the path gives no signal of it, e.g. i.i.d.
locations). Each up-crossing has a matching down-crossing: for `K-1` **decoys** the
down-crossing is `> 2δ` later (so from the up-jump the path stays flat over the whole `2δ`
window), while for exactly one, at a **uniformly random** index `J` independent of the
locations, the down-crossing follows within `g ≤ δ` (a **bad pair**).

* `badSet ε δ` holds on *every* sample (`(σ_J, σ_J + g)` are two `ε`-crossings within `δ`),
  so `(P.map X)(badSet ε δ) = 1`.
* `aldousQ P proc 𝓕 (2δ) (ε/2) ≈ 1/K`. An `𝓕`-stopping time cannot straddle an up-jump
  *from strictly before* it (jump times are unpredictable), so the only way to realize
  `|X(τ+s) − X(τ)| ≥ ε/2` with a constant shift `s ≤ 2δ` is to stop exactly *at* an up-jump
  and have its down-crossing fall inside the window — which happens only for the bad index.
  Since a bad up-crossing is indistinguishable from a decoy one *at the instant it occurs*
  (they differ only in the future time of their down-crossing), no stopping time hits the bad
  index with probability better than `P(J = j) = 1/K`.

Hence `P(badSet ε δ) / aldousQ ≈ K`, unbounded as `K → ∞`. So **no universal constant `C`**
bounds the ratio. (With *deterministic* jump times the inequality would hold — a stopping
time just before a jump straddles it, forcing `aldousQ ≈ 1`; the failure is precisely the
unpredictability, i.e. the non-adaptedness of the first-bad selection.)

### Root cause

The classical single-application argument (as the brief and the prior docstring intended)
needs the **first bad crossing** `σ_{κ}` (`κ` = least `k` with `σ_{k+1} − σ_k ≤ δ`) to be a
single admissible stopping time. But `{σ_κ ≤ t}` depends on the future: to know that `σ_κ`
is the first bad crossing one must know its successor lands within `δ`, i.e. by time `t + δ`.
So `σ_κ` is **not** `𝓕`-adapted. (Item (1) proves each *individual* iterate `σ_k` is a
stopping time — which is true — but the *first-bad-index selection* `κ(ω)` is future-dependent,
which is a different and genuinely non-adapted object.)

Summing `consecutive_crossing_bound` over the finitely many (`< ⌈1/δ⌉`) possible first-bad
indices only yields the `⌈1/δ⌉`-fold bound
`(P.map X)(badSet ε δ) ≤ ⌈1/δ⌉ · 3 · aldousQ(2δ, ε/2)` (plus a terminal-cell term), which is
true but does **not** close `aldous_tightness`: the plain Aldous hypothesis "for each `η₀`
there is `δ₀` with `sup_i α_i(δ₀, ε₀) ≤ η₀`" gives `A(d) := sup_i α_i(d, ·) → 0` at an
*unknown rate*, and `⌈1/δ⌉ · A(2δ)` need not tend to `0` (e.g. `A(d) ~ d` gives
`⌈1/δ⌉ · A(2δ) ~ 2`). A family with `A(d) ~ d` is nonetheless tight by the true Aldous
theorem, so the union bound is strictly weaker than what is needed.

### Consequence for the architecture

The witness-adapter route (`isTightMeasureSet_of_bdd_of_modulus` + `badSet` as the measurable
witness) reduces tightness to a **single-scale** mass bound `∃δ ∀i P_i(badSet ε' δ) ≤ η`.
The counterexample shows this cannot be obtained from a single-scale `aldousQ` bound with a
universal constant, and the union-bound variant is defeated by the unknown `α`-rate. So the
`badSet`/crossing architecture as built is structurally unable to prove `aldous_tightness`;
the genuine Aldous proof uses a different device (a compactness / subsequential-limit
argument, or a crossing-count / multi-scale control) that lies outside the frozen,
extend-in-place scope of this campaign.

## Final statement forms, constants, and `sorryAx` status

* `prob_map_badSet_le` — statement **unchanged** (universal constant `4`), preserved verbatim
  as prior-agent content; its docstring now records that it is false as stated, with the
  counterexample, and it remains a documented `sorry`. No constant of `aldous_tightness` was
  changed (changing `prob_map_badSet_le`'s constant to the honest `⌈1/δ⌉`-dependent one would
  not serve `aldous_tightness`, so it was not done; the statement's meaning is untouched).
* `aldous_tightness`, `aldous_of_moment`, `prop_aldous` — **still carry `sorryAx`
  transitively** through `prob_map_badSet_le`. They were **not** made `sorryAx`-free (this is
  not achievable via the current architecture, per the analysis above).
* Item (1) lemmas (1)–(9) above are `sorryAx`-free.

## Real `sorry` count

**2**, unchanged in number from Task 7 but with the character of the second one now precisely
identified:

1. `thm_mitoma` (unchanged Mitoma citation, in `TypeDDecouplingEW.lean`);
2. `prob_map_badSet_le` (in `TypeDDecouplingSkorokhodAldous.lean`) — now shown **false as
   stated** (no universal constant); documented residual.

The brief's target of count `= 1` (with `aldous_tightness` `sorryAx`-free) is **not
attainable** within the frozen extend-in-place architecture: Item (1) is genuinely provable
and has been delivered, but the assembly it was meant to unlock rests on a statement that is
false, for the structural reason above.
