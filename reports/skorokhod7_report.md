# Skorokhod campaign 7 — assemble `aldous_tightness`, de-opaque `prop_aldous`: report

The whole project builds. Only standard axioms are used except for the two remaining
`sorry`s (`sorryAx`); no `axiom` or `@[implemented_by]` was introduced. Frozen modules
(Basic/Compact/Complete/Tight/Measurable) were not modified.

## Part A — the assembly (`TypeDDecouplingSkorokhodAldous.lean`)

New declarations (all in `namespace SkorokhodBasic`):

* `skoroEval : ℝ → Skoro → ℝ` — the coordinate/evaluation process.
* `crossSeq (ε) (f) : ℕ → ℝ` — the iterated `ε`-crossing sequence of a single càdlàg path,
  clamped to `[0,1]` (`crossSeq ε f 0 = 0`, `crossSeq ε f (k+1) =
  min ((crossTime skoroEval (crossSeq ε f k) ε f).untopD 1) 1`).
* `badSet (ε δ) : Set Skoro = {f | ∃ k, crossSeq ε f k < 1 ∧ crossSeq ε f (k+1) − crossSeq ε f k ≤ δ}`.

Fully proved (standard axioms only — verified with `#print axioms`):

* `cadlagModulus_le_of_not_badSet` : off `badSet`, all consecutive crossing gaps exceed `δ`,
  so the finite crossing sequence is a genuine `δ`-sparse partition with left-endpoint
  oscillation `≤ ε` on every cell and on the terminal cell (via `crossTime_osc_le`), giving
  `cadlagModulus f.toFun δ ≤ ε` through `cadlagModulus_le_of_crossing`.
* `measurableSet_badSet` : each `fun f => crossSeq ε f k` is Borel measurable on `Skoro`
  (induction on `k`, using the joint evaluation measurability `measurable_eval_prod` and
  `crossTime_le_iff` for the canonical right-continuous process), hence `badSet` is a
  countable union of measurable sets.

Assembled (proved **modulo** the single residual below):

* `aldous_tightness` — the packaged criterion. For a family `(X i)` of `D`-valued random
  elements on probability spaces `(Ω i, P i)`, each adapted to a right-continuous
  filtration `𝓕 i`, hypotheses **(i)** uniform sup-norm tightness (`hbdd`) and **(ii)** the
  Aldous stopping-time condition in `aldousQ` form (`hald`: `α_i(δ,ε) → 0` uniformly) imply
  `IsTightMeasureSet (Set.range (fun i => (P i).map (X i)))`. Proof: the witness adapter
  `isTightMeasureSet_of_bdd_of_modulus_witness` fed with `badSet` as the measurable modulus
  witness (`cadlagModulus_le_of_not_badSet` + `measurableSet_badSet`) and the probability
  bound below; the shift/level bookkeeping uses `aldousQ_mono_shift`.
* `aldous_of_moment` — the second-moment route. A uniform second-moment bound `≤ M(d)` on
  the truncated increments with `M(d) → 0` as `d → 0` (plus `hbdd`) implies tightness, via
  `aldousQ_le_of_second_moment` (Chebyshev inside the Aldous supremum) and `aldous_tightness`.
  This half is fully assembled (its only `sorry`-dependency is inherited from
  `aldous_tightness`).

Sole residual (one `sorry`):

* `prob_map_badSet_le` : `(P.map X) (badSet ε δ) ≤ 4 · aldousQ P proc 𝓕 (2δ) (ε/2)`.
  The intended proof takes the **first** bad consecutive crossing pair `(σ, τ)` as a single
  admissible stopping-time pair and applies the proved `consecutive_crossing_bound`. Two
  ingredients turned out to lie genuinely beyond the delivered lemmas, which is why it is
  left open:
  1. the *iterated* crossing times `fun ω => crossSeq ε (X ω) k` must be shown to be
     `𝓕`-stopping times — a début-type statement (first `ε`-oscillation *after* a stopping
     time is a stopping time); the delivered `isStoppingTime_crossTime` only covers a fixed
     deterministic start;
  2. the terminal cell (a genuine `ε`-crossing landing within `δ` of `1` with no successor)
     needs a boundary argument via a deterministic stopping time near `1`; matching the
     crossing detection level to the Aldous level requires the classical `3ε`/`ε` level-gap
     bookkeeping (at matched levels the endpoint value-gap can be swamped by the in-cell
     oscillation, so the exact constant/level in the statement may need adjustment when
     discharged).
  The statement is the standard Billingsley shape and is the sole documented residual noted
  in `skorokhod6_report.md`.

## Part B — `prop_aldous` de-opaqued (`TypeDDecouplingEW.lean`)

* `import TypeDDecouplingSkorokhodAldous` added; `open scoped … ENNReal` added.
* `prop_aldous` **restated as the real theorem**: `D`-valued random elements +
  boundedness + `aldousQ` conditions ⇒ `IsTightMeasureSet` of the pushforward laws, proved
  by `exact SkorokhodBasic.aldous_tightness …`. The old opaque version (over `aldousTightAt`
  / `aldousModulusCond` / `realTight` with a schematic `ζ : ℕ → ℝ → ℝ`, an unprovable-by-
  design `sorry`) is gone. The paper-side docstring (Aldous) is kept and now notes the
  statement is the formalized classical criterion, not a citation.
* Opaques `aldousTightAt` and `aldousModulusCond` **deleted** (they were consumed only by
  `thm_ewmain`; see audit).
* `realTight` and `thm_mitoma` left exactly as-is (Mitoma remains the final citation).
* `thm_ewmain` **rewired minimally** (brief item (f), "thread minimally"): the four Aldous
  hypotheses `ha₁/hb₁/ha₂/hb₂` are replaced by the two real-tightness hypotheses
  `ht₁ ht₂ : ∀ φ, realTight (fun N t => mitomaEval φ (Y_i N t))` — exactly the conclusion the
  (now de-opaqued) Aldous criterion produces — and the proof uses `(thm_mitoma _).mpr ht_i`.
  The statement's conclusion is unchanged (not weakened). It no longer depends on
  `prop_aldous`.

## Consumer audit

`grep` over the project confirms `aldousTightAt`, `aldousModulusCond`, `prop_aldous`,
`realTight`, `thm_mitoma`, `thm_ewmain` occur only in `TypeDDecouplingEW.lean`. The only
other file importing `TypeDDecouplingEW` is `TypeDDecouplingTiers34.lean`, which uses none of
these names. Both build. So deleting the two opaques and rewiring `thm_ewmain` breaks no
downstream consumer.

## Real `sorry` count

**Two**, not one. In `TypeDDecouplingEW.lean`/`TypeDDecouplingSkorokhodAldous.lean`:

1. `thm_mitoma` (unchanged Mitoma citation), and
2. `prob_map_badSet_le` (the crossing/boundary probability bound described above).

The previous second `sorry` — the opaque `prop_aldous` — has been **eliminated**:
`prop_aldous` is now a genuine theorem, proved from `aldous_tightness`. Assembling
`aldous_tightness` moved the residual to the honest analytic statement `prob_map_badSet_le`,
whose remaining content (iterated-crossing stopping-time / début property and the terminal-
boundary level bookkeeping) is real mathematics not covered by the delivered lemmas, rather
than an unprovable-by-design opaque predicate. `aldous_tightness`, `aldous_of_moment` and
`prop_aldous` therefore currently carry `sorryAx` transitively through this single residual.
