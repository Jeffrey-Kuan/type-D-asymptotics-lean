/-
# Aldous's tightness criterion on `D([0,1],ℝ)` (Skorokhod campaign, 5/6)

Library-clean file building on the frozen Skorokhod modules
`TypeDDecouplingSkorokhodBasic`, `TypeDDecouplingSkorokhodCompact`,
`TypeDDecouplingSkorokhodComplete`, `TypeDDecouplingSkorokhodTight`,
`TypeDDecouplingSkorokhodMeasurable`.  See `skorokhod5_brief.tex`.

Design constraints (from Tasks 3–4):

* The càdlàg modulus `w'` is **not** assumed measurable (its level sets are only
  universally measurable — see the irrational-jump counterexample in the
  `Measurable` file).  Every tightness bound is produced from an explicitly
  **measurable** witness set and the outer-measure monotonicity built into
  `isTightMeasureSet_of_bdd_of_modulus`.
* The averaging device (Billingsley (16.24)ff) is a **raw interval Lebesgue
  integral** `(1/(2δ₀)) ∫₀^{2δ₀} P(…) dδ`, swapped with expectations via the
  Tonelli / `intervalIntegral_integral_swap` family.  `uniformOn` (finite-set
  uniform) is never used.
-/
import Mathlib
import TypeDDecouplingSkorokhodBasic
import TypeDDecouplingSkorokhodCompact
import TypeDDecouplingSkorokhodComplete
import TypeDDecouplingSkorokhodTight
import TypeDDecouplingSkorokhodMeasurable

set_option maxHeartbeats 4000000

open scoped Topology BigOperators ENNReal
open Filter Set MeasureTheory

namespace SkorokhodBasic

noncomputable section

/-! ## The bridge adapter (Tier 3 plumbing)

`isTightMeasureSet_of_bdd_of_modulus` (Task 3) already consumes outer bounds on the
level sets `{f | ε ≤ w'(f,δ)}` using only monotonicity of measures.  The following
adapter repackages it so that the modulus contribution may be supplied by a
**measurable witness superset** `H ⊇ {f | ε ≤ w'(f,δ)}` with small mass — exactly the
shape produced by the `crossTime` construction (Tiers 1–2), whose sets are cylinder
measurable even though `w'` itself is not. -/

/-- Adapter over `isTightMeasureSet_of_bdd_of_modulus`: it suffices to control the mass
of a (measurable) superset of each modulus level set. -/
theorem isTightMeasureSet_of_bdd_of_modulus_witness (S : Set (Measure Skoro))
    (hbdd : ∀ η : ℝ≥0∞, 0 < η → ∃ a : ℝ, ∀ μ ∈ S, μ {f : Skoro | a ≤ supNorm f} ≤ η)
    (hmod : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∀ μ ∈ S, ∃ H : Set Skoro,
          {f : Skoro | ε ≤ cadlagModulus f.toFun δ} ⊆ H ∧ μ H ≤ η) :
    IsTightMeasureSet S := by
  apply isTightMeasureSet_of_bdd_of_modulus S hbdd
  intro ε hε η hη
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := hmod ε hε η hη
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro μ hμ
  obtain ⟨H, hsub, hHle⟩ := hδ μ hμ
  exact (measure_mono hsub).trans hHle

/-! ## Tier 2 (path-by-path): a δ-sparse partition bounds the modulus

The infimum defining `cadlagModulus` is realised by any single admissible partition, so
producing one with `> δ` gaps and left-endpoint oscillation `≤ ε` bounds `w'` by `ε`.
This is the clean "witness" direction used by Tier 2's crossing partition. -/

/-- If `f` has a `δ`-sparse partition of `[0,1]` whose cells have left-endpoint oscillation
`≤ ε`, then `cadlagModulus f δ ≤ ε`. -/
theorem cadlagModulus_le_of_partition {f : ℝ → ℝ} {δ ε : ℝ} (hε : 0 ≤ ε)
    {n : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0) (htn : t n = 1) (hn : 0 < n)
    (hmono : ∀ i, i < n → t i < t (i + 1))
    (hmesh : ∀ i, i < n → δ < t (i + 1) - t i)
    (hosc : ∀ i, i < n → ∀ x ∈ Set.Ico (t i) (t (i + 1)), |f x - f (t i)| ≤ ε) :
    cadlagModulus f δ ≤ ε :=
  csInf_le (modulusSet_bddBelow f δ) ⟨hε, n, t, ht0, htn, hn, hmono, hmesh, hosc⟩

/-- **The ε/2 two-application split** (Billingsley (16.24) core).  If the total increment
from `a` to `c` is `≥ ε`, then an intermediate value `b` is `≥ ε/2` away from at least one
endpoint.  This is the pathwise device behind Tier 1's averaging. -/
theorem abs_ge_split {a b c ε : ℝ} (h : ε ≤ |c - a|) :
    ε / 2 ≤ |b - a| ∨ ε / 2 ≤ |b - c| := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have : |c - a| ≤ |b - a| + |b - c| := by
    have := abs_sub_abs_le_abs_sub (c - a) 0
    calc |c - a| = |(b - a) - (b - c)| := by ring_nf
      _ ≤ |b - a| + |b - c| := abs_sub _ _
  linarith

/-
**Tier 2 (path-by-path), the tail-long case.**  Given `ε`-crossing points
`0 = s₀ < s₁ < ⋯ < s_M < 1` that are `> δ`-separated, whose final gap `1 - s_M` is also
`> δ`, and on each cell `[sᵢ, sᵢ₊₁)` (and on the final `[s_M, 1)`) the left-endpoint
oscillation is `≤ ε`, the càdlàg modulus obeys `w'_f(δ) ≤ ε`.  (This is the clean case; the
terminal-cell subtlety — a jump within `δ` of `1` — is handled separately by an Aldous
increment at the boundary, see the report; naïvely merging a short terminal cell can fail
because the crossing at `s_M` may be an arbitrarily large jump.)
-/
theorem cadlagModulus_le_of_crossing {f : ℝ → ℝ} {δ ε : ℝ} (hε : 0 ≤ ε) {M : ℕ}
    {s : ℕ → ℝ} (hs0 : s 0 = 0) (hlast : s M < 1)
    (hmono : ∀ i, i < M → s i < s (i + 1))
    (hsep : ∀ i, i < M → δ < s (i + 1) - s i)
    (htail : δ < 1 - s M)
    (hosc : ∀ i, i < M → ∀ x ∈ Set.Ico (s i) (s (i + 1)), |f x - f (s i)| ≤ ε)
    (hosctail : ∀ x ∈ Set.Ico (s M) 1, |f x - f (s M)| ≤ ε) :
    cadlagModulus f δ ≤ ε := by
  refine' csInf_le _ _;
  · exact ⟨ 0, fun x hx => hx.1 ⟩;
  · refine' ⟨ hε, M + 1, fun i => if i ≤ M then s i else 1, _, _, _, _, _ ⟩ <;> norm_num [ hs0, hlast, hmono, hsep, htail, hosc, hosctail ]; all_goals grind

/-! ## Tier 1: the averaging device (Billingsley (16.24)ff)

The raw interval-Lebesgue-integral averaging device.  On the consecutive-crossing event
`A`, the `ε/2` split (`abs_ge_split`) makes, for *every* shift `δ ∈ [δ₀, 2δ₀]`, the event
`A` contained in the union of the two increment events; averaging over `δ` (a plain
interval Lebesgue integral, **not** `uniformOn`) turns the fixed-`δ` unions into the
integral bound below.  Only monotonicity/subadditivity of `P` are used here; converting the
right-hand integrals into `α(2δ₀, ε/2)` (the second term via an `ω`-dependent time shift and
`intervalIntegral_integral_swap`) is the remaining Billingsley bookkeeping — see the report. -/

section Averaging

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-
The averaging inequality: if on `A` every shift `δ ∈ [δ₀, 2δ₀]` places `A` inside the
union of the two `ε/2`-increment events, then `δ₀ · P(A)` is bounded by the interval
Lebesgue integral of the summed increment probabilities.
-/
theorem averaging_split_bound (P : Measure Ω) {A : Set Ω} {δ₀ e : ℝ}
    {u v : ℝ → Ω → ℝ}
    (hsplit : ∀ δ ∈ Set.Icc δ₀ (2 * δ₀),
      A ⊆ {ω | e / 2 ≤ |u δ ω|} ∪ {ω | e / 2 ≤ |v δ ω|}) :
    ENNReal.ofReal δ₀ * P A ≤
      ∫⁻ δ in Set.Ioc δ₀ (2 * δ₀),
        (P {ω | e / 2 ≤ |u δ ω|} + P {ω | e / 2 ≤ |v δ ω|}) ∂volume := by
  refine' le_trans _ ( MeasureTheory.setLIntegral_mono' measurableSet_Ioc fun x hx => MeasureTheory.measure_union_le _ _ );
  refine' le_trans _ ( MeasureTheory.setLIntegral_mono' measurableSet_Ioc fun x hx => MeasureTheory.measure_mono ( hsplit x <| Set.Ioc_subset_Icc_self hx ) );
  simp +decide [ two_mul, ENNReal.ofReal ];
  rw [ mul_comm ]

end Averaging

/-! ## The fundamental crossing-oscillation property (pathwise)

Before the first `ε`-crossing after `s`, the increment from `X s` stays `≤ ε`.  This is
the path-by-path fact underlying Tier 2: on each cell between consecutive crossing times
the left-endpoint oscillation is `≤ ε`. -/

section Crossing

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-
If `t` lies strictly between `s` and the first `ε`-crossing after `s`, then the increment
`|X t ω - X s ω|` is `≤ ε`.
-/
theorem crossTime_osc_le (X : ℝ → Ω → ℝ) (s ε : ℝ) (ω : Ω) {t : ℝ}
    (hst : s < t) (ht : (t : WithTop ℝ) < crossTime X s ε ω) :
    |X t ω - X s ω| ≤ ε := by
  contrapose! ht; simp_all +decide [ crossTime ] ;
  split_ifs <;> norm_cast;
  · exact csInf_le ⟨ s, fun x hx => hx.1.le ⟩ ⟨ hst, ht ⟩;
  · exact False.elim ( ‹¬Set.Nonempty { t | s < t ∧ ε < |X t ω - X s ω| } › ⟨ t, hst, ht ⟩ )

end Crossing

/-! ## Right-continuity of coordinate processes

The coordinate process of a `Skoro`-valued random element is right-continuous *everywhere*
(not only on `[0,1)`): flatness supplies right-continuity outside `[0,1)`.  This is exactly
the `hrc` hypothesis demanded by `isStoppingTime_crossTime`. -/

/-
Every `Skoro` path is right-continuous at every real point (via càdlàg on `[0,1)` and
flatness elsewhere).
-/
theorem Skoro.rightContinuous (f : Skoro) (t : ℝ) :
    ContinuousWithinAt f.toFun (Set.Ici t) t := by
  by_cases ht : 0 ≤ t ∧ t < 1;
  · exact f.cadlag'.1 t ⟨ ht.1, ht.2 ⟩;
  · by_cases ht : t < 0;
    · refine' ContinuousWithinAt.congr_of_eventuallyEq _ _ _;
      exact fun _ => f.toFun 0;
      · exact continuousWithinAt_const;
      · filter_upwards [ Ico_mem_nhdsGE ( show t < 0 by linarith ) ] with x hx using by rw [ f.flatL x hx.2.le ] ;
      · exact f.flatL _ ht.le;
    · by_cases ht : 1 ≤ t;
      · have h_const : ∀ x ≥ t, f.toFun x = f.toFun 1 := by
          exact fun x hx => f.flatR x ( by linarith );
        exact tendsto_const_nhds.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_const x hx, h_const t le_rfl ] );
      · grind

/-! ## Tier 1: joint (progressive) measurability of the canonical process

For a measurable `X : Ω → Skoro`, the evaluated process `(s, ω) ↦ X(ω)(s)` is jointly
measurable on `ℝ × Ω`.  Route (elementary, classical): dyadic right-endpoint approximation
`Xⁿ(s, ω) := X(ω)(⌈s·2ⁿ⌉/2ⁿ)` — each `Xⁿ` is jointly measurable (the dyadic ceiling takes
countably many values, and on each value it is a fixed-time evaluation, measurable by
Task 4's `measurable_eval`), and `Xⁿ(s, ω) → X(ω)(s)` pointwise because the dyadic
approximants decrease to `s` from the right (`⌈s·2ⁿ⌉/2ⁿ ≥ s`, `→ s`) and paths are
right-continuous (`Skoro.rightContinuous`, Task 5).  The consumer form used by Tier 2 is
the composition with the measurable time map `(δ, ω) ↦ (min (τ(ω)+δ) 1, ω)`. -/

section JointMeasurable

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The dyadic right-endpoint approximant `Xⁿ(s, ω) = X(ω)(⌈s·2ⁿ⌉/2ⁿ)`. -/
def dyadicApprox (X : Ω → Skoro) (n : ℕ) (p : ℝ × Ω) : ℝ :=
  (X p.2).toFun (⌈p.1 * (2 : ℝ) ^ n⌉ / (2 : ℝ) ^ n)

/-- Each dyadic approximant is jointly measurable: the ceiling `⌈p.1·2ⁿ⌉ : ℤ` is measurable
and takes values in the countable set `ℤ`, on each of which the map is a fixed-time
evaluation (`measurable_eval`). -/
theorem measurable_dyadicApprox {X : Ω → Skoro} (hX : Measurable X) (n : ℕ) :
    Measurable (dyadicApprox X n) := by
  have hF : Measurable (fun q : ℤ × Ω => (X q.2).toFun ((q.1 : ℝ) / (2 : ℝ) ^ n)) := by
    apply measurable_from_prod_countable_right
    intro k
    exact (measurable_eval ((k : ℝ) / (2 : ℝ) ^ n)).comp hX
  have hinner : Measurable (fun p : ℝ × Ω => (⌈p.1 * (2 : ℝ) ^ n⌉, p.2)) := by
    refine Measurable.prodMk ?_ measurable_snd
    exact Int.measurable_ceil.comp (measurable_fst.mul measurable_const)
  exact hF.comp hinner

/-- Pointwise convergence of the dyadic approximants from the right, using right-continuity
of càdlàg paths. -/
theorem tendsto_dyadicApprox {X : Ω → Skoro} (p : ℝ × Ω) :
    Filter.Tendsto (fun n => dyadicApprox X n p) Filter.atTop
      (𝓝 ((X p.2).toFun p.1)) := by
  have hrc : Filter.Tendsto (X p.2).toFun (𝓝[Set.Ici p.1] p.1)
      (𝓝 ((X p.2).toFun p.1)) := Skoro.rightContinuous (X p.2) p.1
  refine hrc.comp ?_
  rw [tendsto_nhdsWithin_iff]
  constructor
  · -- `⌈p.1·2ⁿ⌉/2ⁿ → p.1`
    have hpos : ∀ n : ℕ, (0 : ℝ) < (2 : ℝ) ^ n := fun n => by positivity
    have hz : Filter.Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) Filter.atTop (𝓝 0) := by
      have : Filter.Tendsto (fun n : ℕ => ((1:ℝ)/2)^n) Filter.atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa [div_pow] using this
    have hupper : Filter.Tendsto (fun n : ℕ => p.1 + 1 / (2 : ℝ) ^ n) Filter.atTop
        (𝓝 (p.1 + 0)) := Filter.Tendsto.const_add p.1 hz
    rw [add_zero] at hupper
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => ?_) (fun n => ?_)
    · rw [le_div_iff₀ (hpos n)]; nlinarith [Int.le_ceil (p.1 * (2 : ℝ) ^ n)]
    · rw [div_le_iff₀ (hpos n)]
      have hc : (1 / (2 : ℝ) ^ n) * (2 : ℝ) ^ n = 1 :=
        one_div_mul_cancel (ne_of_gt (hpos n))
      nlinarith [Int.ceil_lt_add_one (p.1 * (2 : ℝ) ^ n), hpos n, hc]
  · filter_upwards with n
    have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    rw [Set.mem_Ici, le_div_iff₀ hpos]
    calc p.1 * (2 : ℝ) ^ n ≤ (⌈p.1 * (2 : ℝ) ^ n⌉ : ℝ) := Int.le_ceil _
      _ = _ := rfl

/-- **Tier 1 (must-have): joint measurability of the canonical evaluated process.**
For measurable `X : Ω → Skoro`, the map `(s, ω) ↦ X(ω)(s)` is measurable on `ℝ × Ω`. -/
theorem measurable_eval_prod {X : Ω → Skoro} (hX : Measurable X) :
    Measurable (fun p : ℝ × Ω => (X p.2).toFun p.1) :=
  measurable_of_tendsto_metrizable' Filter.atTop (fun n => measurable_dyadicApprox hX n)
    (tendsto_pi_nhds.mpr (fun p => tendsto_dyadicApprox p))

/-- **Tier 1 consumer form.**  For measurable `X : Ω → Skoro` and measurable
`τ : Ω → ℝ`, the shifted evaluated process `(δ, ω) ↦ X(ω)(min (τ(ω)+δ) 1)` is jointly
measurable on `ℝ × Ω`.  This is the integrand of the `v`-term Fubini/change-of-variable
reduction of Tier 2. -/
theorem measurable_eval_shift {X : Ω → Skoro} (hX : Measurable X)
    {τ : Ω → ℝ} (hτ : Measurable τ) :
    Measurable (fun p : ℝ × Ω => (X p.2).toFun (min (τ p.2 + p.1) 1)) := by
  have htime : Measurable (fun p : ℝ × Ω => (min (τ p.2 + p.1) 1, p.2)) := by
    refine Measurable.prodMk ?_ measurable_snd
    exact ((hτ.comp measurable_snd).add measurable_fst).min measurable_const
  exact (measurable_eval_prod hX).comp htime

end JointMeasurable

/-! ## The Aldous quantity and Chebyshev's step

`aldousQ P X 𝓕 d e` is Aldous's `α(d,e) = sup_{τ ≤ 1, δ ≤ d} P(|X(τ+δ) - X(τ)| ≥ e)`, the
supremum over `𝓕`-stopping times `τ ≤ 1` and shifts `δ ≤ d` (truncated at `1`).  It is
monotone in the shift budget `d`.  The `aldous_of_moment` route bounds it by Chebyshev. -/

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Aldous's quantity `α(d,e)`. -/
def aldousQ (P : Measure Ω) (X : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ m) (d e : ℝ) : ℝ≥0∞ :=
  ⨆ (τ : Ω → ℝ) (_ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ)))
    (_ : ∀ ω, τ ω ≤ 1) (δ : ℝ) (_ : 0 ≤ δ) (_ : δ ≤ d),
    P {ω | e ≤ |X (min (τ ω + δ) 1) ω - X (τ ω) ω|}

/-
The Aldous quantity is monotone in the shift budget `d`.
-/
theorem aldousQ_mono_shift (P : Measure Ω) (X : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ m)
    {d₁ d₂ e : ℝ} (h : d₁ ≤ d₂) : aldousQ P X 𝓕 d₁ e ≤ aldousQ P X 𝓕 d₂ e := by
  refine' iSup_le fun τ => iSup_le fun hτ => iSup_le fun hτ1 => iSup_le fun δ => iSup_le fun hδ0 => iSup_le fun hδ1 => _;
  refine' le_iSup_of_le τ (le_iSup_of_le hτ (le_iSup_of_le hτ1 (le_iSup_of_le δ (le_iSup_of_le hδ0 (le_iSup_of_le (hδ1.trans h) le_rfl)))) )

/--
**Aldous supremum lower bound (u-term, pointwise).**  Any single admissible pair
`(τ, δ)` — `τ` a stopping time `≤ 1`, `0 ≤ δ ≤ d` — contributes below the Aldous
supremum.  This is the definitional bound `P(|X(τ+δ) - X(τ)| ≥ e) ≤ α(d,e)`. -/
theorem le_aldousQ_of_stoppingTime (P : Measure Ω) (X : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ m)
    {τ : Ω → ℝ} (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ)))
    (hτ1 : ∀ ω, τ ω ≤ 1) {d e δ : ℝ} (hδ0 : 0 ≤ δ) (hδd : δ ≤ d) :
    P {ω | e ≤ |X (min (τ ω + δ) 1) ω - X (τ ω) ω|} ≤ aldousQ P X 𝓕 d e :=
  le_iSup_of_le τ (le_iSup_of_le hτ (le_iSup_of_le hτ1
    (le_iSup_of_le δ (le_iSup_of_le hδ0 (le_iSup_of_le hδd le_rfl)))))

/--
**u-term integral reduction.**  Averaging the fixed-shift increment probabilities of a
single stopping time `τ ≤ 1` over `δ ∈ (δ₀, 2δ₀]` is bounded by `δ₀ · α(2δ₀, e)`.  This is
the "immediate" half of the averaging reduction (Billingsley (16.24)): every `δ` in the
range is an admissible shift `≤ 2δ₀`, so the integrand is `≤ α(2δ₀,e)` pointwise, and the
interval has length `δ₀`. -/
theorem uterm_integral_bound (P : Measure Ω) (X : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ m)
    {τ : Ω → ℝ} (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ)))
    (hτ1 : ∀ ω, τ ω ≤ 1) {δ₀ e : ℝ} (hδ₀ : 0 ≤ δ₀) :
    ∫⁻ δ in Set.Ioc δ₀ (2 * δ₀),
        P {ω | e ≤ |X (min (τ ω + δ) 1) ω - X (τ ω) ω|} ∂volume
      ≤ ENNReal.ofReal δ₀ * aldousQ P X 𝓕 (2 * δ₀) e := by
  refine le_trans (MeasureTheory.setLIntegral_mono' measurableSet_Ioc
    (fun δ hδ => le_aldousQ_of_stoppingTime P X 𝓕 hτ hτ1
      (le_of_lt (lt_of_le_of_lt hδ₀ hδ.1)) hδ.2)) ?_
  rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc, show 2 * δ₀ - δ₀ = δ₀ by ring,
    mul_comm]

/-- Translation change of variables for an `Ioc` set l-integral (Lebesgue measure is
translation invariant). -/
theorem setLIntegral_Ioc_add_right (φ : ℝ → ℝ≥0∞) (a b c : ℝ) (hφ : Measurable φ) :
    ∫⁻ δ in Set.Ioc a b, φ (δ + c) ∂volume
      = ∫⁻ s in Set.Ioc (a + c) (b + c), φ s ∂volume := by
  have hmp : Measure.map (fun x => x + c) volume = volume :=
    (measurePreserving_add_right volume c).map_eq
  have hpre : (fun x => x + c) ⁻¹' Set.Ioc (a + c) (b + c) = Set.Ioc a b := by
    ext x; simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
  conv_rhs => rw [← hmp, setLIntegral_map measurableSet_Ioc hφ (measurable_add_const c), hpre]

/-- **Monotonicity of `aldousQ` in the measure.**  A smaller measure gives a smaller
Aldous supremum (each `P`-probability term is monotone in `P`). -/
theorem aldousQ_mono_measure {P Q : Measure Ω} (hPQ : P ≤ Q) (X : ℝ → Ω → ℝ)
    (𝓕 : Filtration ℝ m) (d e : ℝ) : aldousQ P X 𝓕 d e ≤ aldousQ Q X 𝓕 d e := by
  refine iSup_le fun τ => iSup_le fun hτ => iSup_le fun hτ1 => iSup_le fun δ =>
    iSup_le fun hδ0 => iSup_le fun hδd => ?_
  exact le_trans (hPQ _) (le_iSup_of_le τ (le_iSup_of_le hτ (le_iSup_of_le hτ1
    (le_iSup_of_le δ (le_iSup_of_le hδ0 (le_iSup_of_le hδd le_rfl))))))

/-- **flatR truncation bound.**  For a càdlàg `Skoro` path, the unshifted increment
`X(τ+s) - X(τ)` equals the min-truncated increment `X(min(τ+s,1)) - X(τ)` (by right
flatness), so for a stopping time `τ ≤ 1` and `0 ≤ s ≤ d` the increment probability is
bounded by `α(d,e)`. -/
theorem prob_shift_le_aldousQ (P : Measure Ω) (X : Ω → Skoro) (𝓕 : Filtration ℝ m)
    {τ : Ω → ℝ} (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ)))
    (hτ1 : ∀ ω, τ ω ≤ 1) {d e s : ℝ} (hs0 : 0 ≤ s) (hsd : s ≤ d) :
    P {ω | e ≤ |(X ω).toFun (τ ω + s) - (X ω).toFun (τ ω)|}
      ≤ aldousQ P (fun t ω => (X ω).toFun t) 𝓕 d e := by
  have hset : {ω | e ≤ |(X ω).toFun (τ ω + s) - (X ω).toFun (τ ω)|}
      = {ω | e ≤ |(X ω).toFun (min (τ ω + s) 1) - (X ω).toFun (τ ω)|} := by
    ext ω
    have hval : (X ω).toFun (τ ω + s) = (X ω).toFun (min (τ ω + s) 1) := by
      rcases le_or_gt (τ ω + s) 1 with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h.le, (X ω).flatR _ h.le]
    simp only [Set.mem_setOf_eq, hval]
  rw [hset]
  exact le_aldousQ_of_stoppingTime P (fun t ω => (X ω).toFun t) 𝓕 hτ hτ1 hs0 hsd

/-
**v-term integral reduction (the Task-5 residual).**  With an `ω`-dependent shift
`a : Ω → ℝ` satisfying `-δ₀ ≤ a ω ≤ 0` (the consecutive-crossing gap on the good event,
`a = τₖ - τₖ₊₁`), the averaged shifted-increment probabilities are bounded by
`2δ₀ · α(2δ₀, e)`.  Proof: Tonelli swap (joint measurability from Tier 1), the `ω`-wise
translation `δ ↦ δ + aω` sending the range into `(0, 2δ₀]`, swap back, then
`prob_shift_le_aldousQ` for each fixed shift.
-/
theorem vterm_integral_bound (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → Skoro)
    (hX : Measurable X) (𝓕 : Filtration ℝ m) {δ₀ e : ℝ}
    {τ : Ω → ℝ} (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ)))
    (hτ1 : ∀ ω, τ ω ≤ 1) (hτmeas : Measurable τ)
    {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, -δ₀ ≤ a ω) (ha1 : ∀ ω, a ω ≤ 0) :
    ∫⁻ δ in Set.Ioc δ₀ (2 * δ₀),
        P {ω | e ≤ |(X ω).toFun (τ ω + a ω + δ) - (X ω).toFun (τ ω)|} ∂volume
      ≤ ENNReal.ofReal (2 * δ₀) * aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * δ₀) e := by
  -- Apply Fubini's theorem to interchange the order of integration.
  have h_fubini : ∫⁻ δ in Set.Ioc δ₀ (2 * δ₀), ∫⁻ ω, Set.indicator {ω | e ≤ |(X ω).toFun (τ ω + a ω + δ) - (X ω).toFun (τ ω)|} (fun _ => 1) ω ∂P ∂volume ≤ ENNReal.ofReal (2 * δ₀) * aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * δ₀) e := by
    rw [ ← MeasureTheory.lintegral_lintegral_swap ];
    · refine' le_trans ( MeasureTheory.lintegral_mono fun ω => _ ) _;
      use fun ω => ∫⁻ s in Set.Ioc 0 (2 * δ₀), Set.indicator {ω | e ≤ |(X ω).toFun (τ ω + s) - (X ω).toFun (τ ω)|} (fun _ => 1) ω ∂volume;
      · have h_shift : ∫⁻ y in Set.Ioc δ₀ (2 * δ₀), Set.indicator {ω | e ≤ |(X ω).toFun (τ ω + a ω + y) - (X ω).toFun (τ ω)|} (fun _ => 1) ω ∂volume = ∫⁻ s in Set.Ioc (δ₀ + a ω) (2 * δ₀ + a ω), Set.indicator {ω | e ≤ |(X ω).toFun (τ ω + s) - (X ω).toFun (τ ω)|} (fun _ => 1) ω ∂volume := by
          rw [ ← MeasureTheory.lintegral_indicator, ← MeasureTheory.lintegral_indicator ];
          · simp +decide [ Set.indicator ];
            rw [ ← MeasureTheory.lintegral_add_right_eq_self _ ( -a ω ) ] ; congr ; ext ; ring;
            grind;
          · exact measurableSet_Ioc;
          · exact measurableSet_Ioc;
        rw [h_shift];
        refine' MeasureTheory.lintegral_mono_set _;
        exact Set.Ioc_subset_Ioc ( by linarith [ ha0 ω ] ) ( by linarith [ ha1 ω ] );
      · rw [ MeasureTheory.lintegral_lintegral_swap ];
        · refine' le_trans ( MeasureTheory.setLIntegral_mono' measurableSet_Ioc fun y hy => _ ) _;
          use fun y => aldousQ P ( fun t ω => ( X ω ).toFun t ) 𝓕 ( 2 * δ₀ ) e;
          · rw [ MeasureTheory.lintegral_indicator ];
            · simp +decide [ prob_shift_le_aldousQ P X 𝓕 hτ hτ1 hy.1.le hy.2 ];
            · have h_measurable : Measurable (fun ω => (X ω).toFun (τ ω + y)) ∧ Measurable (fun ω => (X ω).toFun (τ ω)) := by
                constructor;
                · have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun p.1) := by
                    exact SkorokhodBasic.measurable_eval_prod hX;
                  convert h_measurable.comp ( show Measurable fun ω => ( τ ω + y, ω ) from Measurable.prodMk ( hτmeas.add_const y ) measurable_id' ) using 1;
                · have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun p.1) := by
                    exact SkorokhodBasic.measurable_eval_prod hX;
                  exact h_measurable.comp ( hτmeas.prodMk measurable_id' );
              exact measurableSet_le measurable_const ( h_measurable.1.sub h_measurable.2 |> Measurable.norm );
          · simp +decide [ mul_comm ];
        · refine' Measurable.aemeasurable _;
          refine' Measurable.ite _ measurable_const measurable_const;
          have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun (τ p.2 + p.1)) := by
            have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun p.1) := by
              convert SkorokhodBasic.measurable_eval_prod hX using 1;
            convert h_measurable.comp ( show Measurable fun p : ℝ × Ω => ( τ p.2 + p.1, p.2 ) from Measurable.prodMk ( hτmeas.comp measurable_snd |> Measurable.add <| measurable_fst ) measurable_snd ) using 1;
          have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun (τ p.2 + p.1) - (X p.2).toFun (τ p.2)) := by
            have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun (τ p.2)) := by
              convert h_measurable.comp ( show Measurable fun p : ℝ × Ω => ( 0, p.2 ) from measurable_const.prodMk measurable_snd ) using 1;
              aesop;
            exact Measurable.sub ‹_› ‹_›;
          exact measurableSet_le measurable_const ( h_measurable.norm.comp ( measurable_swap ) );
    · refine' AEMeasurable.indicator _ _;
      · exact aemeasurable_const;
      · have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun (τ p.2 + a p.2 + p.1) - (X p.2).toFun (τ p.2)) := by
          have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun p.1) := by
            convert SkorokhodBasic.measurable_eval_prod hX using 1;
          convert h_measurable.comp ( show Measurable fun p : ℝ × Ω => ( τ p.2 + a p.2 + p.1, p.2 ) from ?_ ) |> Measurable.sub <| h_measurable.comp ( show Measurable fun p : ℝ × Ω => ( τ p.2, p.2 ) from ?_ ) using 1;
          · exact Measurable.prodMk ( Measurable.add ( Measurable.add ( hτmeas.comp measurable_snd ) ( ha.comp measurable_snd ) ) measurable_fst ) measurable_snd;
          · exact Measurable.prodMk ( hτmeas.comp measurable_snd ) measurable_snd;
        exact measurableSet_le measurable_const ( h_measurable.norm.comp ( measurable_swap ) );
  convert h_fubini using 3;
  rw [ MeasureTheory.lintegral_indicator ];
  · simp +decide;
  · have h_meas : Measurable (fun ω => (X ω).toFun (τ ω + a ω + ‹ℝ›) - (X ω).toFun (τ ω)) := by
      have h_meas : Measurable (fun p : ℝ × Ω => (X p.2).toFun p.1) := by
        convert SkorokhodBasic.measurable_eval_prod hX using 1;
      exact Measurable.sub ( h_meas.comp ( Measurable.prodMk ( hτmeas.add ha |> Measurable.add <| measurable_const ) measurable_id' ) ) ( h_meas.comp ( Measurable.prodMk hτmeas measurable_id' ) );
    exact measurableSet_le measurable_const ( h_meas.norm )

/-
**Consecutive-crossing bound (Billingsley (16.24)).**  For two stopping times
`σ ≤ τ ≤ 1` whose gap is `≤ δ₀` on a measurable event `A`, and on which the `ε/2`-split of
the increment `X(τ) - X(σ)` holds for every shift `δ ∈ [δ₀, 2δ₀]`, the mass of `A` obeys
`δ₀ · P(A) ≤ 3δ₀ · α(2δ₀, ε/2)`.  Proof: apply the averaging device to `P.restrict A`
(so both increment events are measured against `A`), bound the `u`-term via
`prob_shift_le_aldousQ` and the `v`-term via `vterm_integral_bound` (with the `ω`-clamped
shift `a' = max (-δ₀) (min (σ-τ) 0)`, which equals `σ-τ` on `A`), and use
`aldousQ_mono_measure` to pass from `P.restrict A` back to `P`.
-/
theorem consecutive_crossing_bound (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → Skoro)
    (hX : Measurable X) (𝓕 : Filtration ℝ m) {δ₀ ε : ℝ} (hδ₀ : 0 ≤ δ₀)
    {σ τ : Ω → ℝ}
    (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ))) (hσmeas : Measurable σ)
    (hσ1 : ∀ ω, σ ω ≤ 1)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ))) (hτmeas : Measurable τ)
    (hτ1 : ∀ ω, τ ω ≤ 1)
    {A : Set Ω} (hA : MeasurableSet A)
    (hAle : ∀ ω ∈ A, σ ω ≤ τ ω ∧ τ ω - σ ω ≤ δ₀)
    (hsplit : ∀ δ ∈ Set.Icc δ₀ (2 * δ₀), A ⊆
        {ω | ε / 2 ≤ |(X ω).toFun (σ ω + δ) - (X ω).toFun (σ ω)|} ∪
        {ω | ε / 2 ≤ |(X ω).toFun (σ ω + δ) - (X ω).toFun (τ ω)|}) :
    ENNReal.ofReal δ₀ * P A ≤
      ENNReal.ofReal (3 * δ₀) * aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * δ₀) (ε / 2) := by
  -- Let P' := P.restrict A. Let g t ω := (X ω).toFun t (the process).
  set P' : Measure Ω := P.restrict A with hP';
  -- By averaging device (averaging_split_bound), we have
  have h_avg : ENNReal.ofReal δ₀ * P' A ≤ ∫⁻ δ in Set.Ioc δ₀ (2 * δ₀), (P' {ω | ε / 2 ≤ |(X ω).toFun (σ ω + δ) - (X ω).toFun (σ ω)|} + P' {ω | ε / 2 ≤ |(X ω).toFun (σ ω + δ) - (X ω).toFun (τ ω)|}) ∂volume := by
    apply averaging_split_bound P' hsplit;
  -- Apply `prob_shift_le_aldousQ` to the first term.
  have h_u : ∫⁻ δ in Set.Ioc δ₀ (2 * δ₀), P' {ω | ε / 2 ≤ |(X ω).toFun (σ ω + δ) - (X ω).toFun (σ ω)|} ∂volume ≤ ENNReal.ofReal δ₀ * aldousQ P' (fun t ω => (X ω).toFun t) 𝓕 (2 * δ₀) (ε / 2) := by
    refine' le_trans ( MeasureTheory.lintegral_mono_ae _ ) _;
    use fun δ => aldousQ P' ( fun t ω => ( X ω ).toFun t ) 𝓕 ( 2 * δ₀ ) ( ε / 2 );
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with δ hδ;
      convert prob_shift_le_aldousQ P' X 𝓕 hσ hσ1 ( show 0 ≤ δ by linarith [ hδ.1 ] ) ( show δ ≤ 2 * δ₀ by linarith [ hδ.2 ] ) using 1;
    · rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc, show 2 * δ₀ - δ₀ = δ₀ by ring,
        mul_comm]
  -- Apply `vterm_integral_bound` to the second term.
  have h_v : ∫⁻ δ in Set.Ioc δ₀ (2 * δ₀), P' {ω | ε / 2 ≤ |(X ω).toFun (σ ω + δ) - (X ω).toFun (τ ω)|} ∂volume ≤ ENNReal.ofReal (2 * δ₀) * aldousQ P' (fun t ω => (X ω).toFun t) 𝓕 (2 * δ₀) (ε / 2) := by
    -- Define the clamped shift `a' : Ω → ℝ := fun ω => max (-δ₀) (min (σ ω - τ ω) 0)`.
    set a' : Ω → ℝ := fun ω => max (-δ₀) (min (σ ω - τ ω) 0) with ha';
    -- Show that the integrand equals the v-term one.
    have h_v_eq : ∀ δ ∈ Set.Ioc δ₀ (2 * δ₀), P' {ω | ε / 2 ≤ |(X ω).toFun (σ ω + δ) - (X ω).toFun (τ ω)|} = P' {ω | ε / 2 ≤ |(X ω).toFun (τ ω + a' ω + δ) - (X ω).toFun (τ ω)|} := by
      intro δ hδ
      have h_eq : ∀ ω ∈ A, (X ω).toFun (σ ω + δ) = (X ω).toFun (τ ω + a' ω + δ) := by
        grind;
      rw [ MeasureTheory.Measure.restrict_apply' hA, MeasureTheory.Measure.restrict_apply' hA ];
      exact congr_arg _ ( by ext ω; by_cases hω : ω ∈ A <;> simp +decide [ hω, h_eq ] );
    convert vterm_integral_bound P' X hX 𝓕 hτ hτ1 hτmeas ( show Measurable a' from ?_ ) ( show ∀ ω, -δ₀ ≤ a' ω from ?_ ) ( show ∀ ω, a' ω ≤ 0 from ?_ ) using 1;
    · rw [ MeasureTheory.lintegral_congr_ae ( Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) h_v_eq ) ];
    · exact Measurable.max measurable_const ( Measurable.min ( hσmeas.sub hτmeas ) measurable_const );
    · exact fun ω => le_max_left _ _;
    · exact fun ω => max_le_iff.mpr ⟨ by linarith, min_le_right _ _ ⟩;
  -- Combine the inequalities from `h_avg`, `h_u`, and `h_v`.
  have h_combined : ENNReal.ofReal δ₀ * P' A ≤ ENNReal.ofReal δ₀ * aldousQ P' (fun t ω => (X ω).toFun t) 𝓕 (2 * δ₀) (ε / 2) + ENNReal.ofReal (2 * δ₀) * aldousQ P' (fun t ω => (X ω).toFun t) 𝓕 (2 * δ₀) (ε / 2) := by
    refine' le_trans h_avg _;
    rw [ MeasureTheory.lintegral_add_left' ];
    · exact add_le_add h_u h_v;
    · refine' Measurable.aemeasurable _;
      have h_meas : Measurable (fun p : ℝ × Ω => |(X p.2).toFun (σ p.2 + p.1) - (X p.2).toFun (σ p.2)|) := by
        have h_meas : Measurable (fun p : ℝ × Ω => (X p.2).toFun (σ p.2 + p.1)) := by
          have h_meas : Measurable (fun p : ℝ × Ω => (X p.2).toFun p.1) :=
            SkorokhodBasic.measurable_eval_prod hX
          convert h_meas.comp ( show Measurable fun p : ℝ × Ω => ( σ p.2 + p.1, p.2 ) from Measurable.prodMk ( hσmeas.comp measurable_snd |> Measurable.add <| measurable_fst ) measurable_snd ) using 1;
        have h_meas : Measurable (fun p : ℝ × Ω => (X p.2).toFun (σ p.2)) := by
          convert h_meas.comp ( show Measurable fun p : ℝ × Ω => ( 0, p.2 ) from measurable_const.prodMk measurable_snd ) using 1;
          exact funext fun p => by simp +decide ;
        fun_prop;
      convert measurable_measure_prodMk_left ( show MeasurableSet { p : ℝ × Ω | ε / 2 ≤ |(X p.2).toFun (σ p.2 + p.1) - (X p.2).toFun (σ p.2)| } from measurableSet_le measurable_const h_meas ) using 1;
      infer_instance;
  convert h_combined.trans _ using 1;
  · rw [ Measure.restrict_apply_self ];
  · rw [ ← add_mul, ← ENNReal.ofReal_add ] <;> ring <;> norm_num [ hδ₀ ];
    gcongr
    exact aldousQ_mono_measure Measure.restrict_le_self _ _ _ _

/-
**Chebyshev step for `aldous_of_moment`.**  A second-moment bound on an increment
controls the probability that it is large.
-/
theorem prob_ge_le_second_moment (P : Measure Ω) (Y : Ω → ℝ)
    (hY : AEMeasurable Y P) {e : ℝ} (he : 0 < e) :
    P {ω | e ≤ |Y ω|} ≤ (∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P) / ENNReal.ofReal (e ^ 2) := by
  convert MeasureTheory.meas_ge_le_lintegral_div ( f := fun ω => ENNReal.ofReal ( Y ω ^ 2 ) ) ( ε := ENNReal.ofReal ( e ^ 2 ) ) _ _ _ using 1;
  · simp +decide only [ENNReal.ofReal_le_ofReal_iff (sq_nonneg _), sq_le_sq, abs_le];
    exact congr_arg _ ( by ext; exact ⟨ fun h => ⟨ by linarith [ abs_nonneg ( Y ‹_› ) ], h ⟩, fun h => h.2 ⟩ );
  · exact ENNReal.measurable_ofReal.comp_aemeasurable ( hY.pow_const 2 );
  · positivity;
  · exact ENNReal.ofReal_ne_top

/-- **`aldous_of_moment` (the second-moment route to Aldous's condition).**  If every
admissible increment `X(min(τ+δ,1)) - X(τ)` has second moment `≤ M` (uniformly over
stopping times `τ ≤ 1` and shifts `δ ≤ d`), then the Aldous quantity is bounded by
`M / e²` (Chebyshev/Markov applied inside the supremum via `prob_ge_le_second_moment`).
In particular, if `M = M(d) → 0` as `d → 0`, this yields Aldous's condition (ii). -/
theorem aldousQ_le_of_second_moment (P : Measure Ω) (X : ℝ → Ω → ℝ) (𝓕 : Filtration ℝ m)
    {d e : ℝ} (he : 0 < e) {M : ℝ≥0∞}
    (hmeas : ∀ (τ : Ω → ℝ) (δ : ℝ),
      AEMeasurable (fun ω => X (min (τ ω + δ) 1) ω - X (τ ω) ω) P)
    (hmom : ∀ (τ : Ω → ℝ), IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ)) → (∀ ω, τ ω ≤ 1) →
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ d →
          ∫⁻ ω, ENNReal.ofReal ((X (min (τ ω + δ) 1) ω - X (τ ω) ω) ^ 2) ∂P ≤ M) :
    aldousQ P X 𝓕 d e ≤ M / ENNReal.ofReal (e ^ 2) := by
  refine iSup_le fun τ => iSup_le fun hτ => iSup_le fun hτ1 => iSup_le fun δ =>
    iSup_le fun hδ0 => iSup_le fun hδd => ?_
  refine le_trans (prob_ge_le_second_moment P
    (fun ω => X (min (τ ω + δ) 1) ω - X (τ ω) ω) (hmeas τ δ) he) ?_
  gcongr
  exact hmom τ hτ hτ1 δ hδ0 hδd

/-! ## The crossing construction and the packaged Aldous tightness theorem

This final block assembles the packaged `aldous_tightness` from the proved per-crossing
bound.  The pathwise device is the iterated `ε`-crossing sequence `crossSeq` of a single
càdlàg path (clamped to `[0,1]`).  On the *good* set (all consecutive crossing gaps `> δ`)
the crossing partition realises `cadlagModulus ≤ ε` via `cadlagModulus_le_of_crossing`; the
complement is the measurable `badSet`, whose pushforward mass is bounded by the Aldous
quantity through `consecutive_crossing_bound`.  Feeding these to the witness adapter yields
`IsTightMeasureSet`. -/

/-- Canonical evaluation process on `Skoro` (the coordinate process). -/
def skoroEval : ℝ → Skoro → ℝ := fun t f => f.toFun t

/-- The iterated `ε`-crossing sequence of a single càdlàg path, clamped to `[0,1]`:
`crossSeq ε f 0 = 0`, and `crossSeq ε f (k+1)` is the first `ε`-oscillation time of `f`
after `crossSeq ε f k` (truncated at `1`, and set to `1` if there is no further crossing). -/
noncomputable def crossSeq (ε : ℝ) (f : Skoro) : ℕ → ℝ
  | 0 => 0
  | (k+1) => min ((crossTime skoroEval (crossSeq ε f k) ε f).untopD 1) 1

/-- The bad set at scale `(ε, δ)`: paths having a consecutive `ε`-crossing pair (the first
of which is still `< 1`) whose gap is `≤ δ`.  Its complement carries a `δ`-sparse crossing
partition, hence a small càdlàg modulus. -/
def badSet (ε δ : ℝ) : Set Skoro :=
  {f | ∃ k : ℕ, crossSeq ε f k < 1 ∧ crossSeq ε f (k+1) - crossSeq ε f k ≤ δ}

/-
**Pathwise modulus bound.**  Off the `badSet` all consecutive `ε`-crossing gaps exceed
`δ`, so the (finite) crossing sequence is a genuine `δ`-sparse partition of `[0,1]` with
left-endpoint oscillation `≤ ε` on every cell (`crossTime_osc_le`), whence
`cadlagModulus f δ ≤ ε` by `cadlagModulus_le_of_crossing`.
-/
theorem cadlagModulus_le_of_not_badSet {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    {f : Skoro} (hf : f ∉ badSet ε δ) : cadlagModulus f.toFun δ ≤ ε := by
  -- Let `s := crossSeq ε f` (so `s 0 = 0` and `s (k+1) = min ((crossTime skoroEval (s k) ε f).untopD 1) 1`). Note `s k ≤ 1` for all k, and `s k ≤ s (k+1)`.
  set s : ℕ → ℝ := crossSeq ε f
  have hs0 : s 0 = 0 := by
    rfl
  have hlast : s 0 ≤ 1 := by
    linarith
  have hmono : ∀ k, s k ≤ s (k + 1) := by
    intro k;
    refine' le_min _ _;
    · by_cases h : crossTime skoroEval ( crossSeq ε f k ) ε f = ⊤ <;> simp_all +decide [ crossTime ];
      · exact Nat.recOn k ( by linarith ) fun n ihn => min_le_right _ _ |> le_trans <| by linarith;
      · exact le_csInf h fun x hx => hx.1.le;
    · exact Nat.recOn k ( by linarith ) fun n ihn => by exact min_le_right _ _;
  have hle : ∀ k, s k ≤ 1 := by
    intro k; exact Nat.recOn k ( by linarith ) fun k ih => by linarith [ hmono k, show s ( k + 1 ) ≤ 1 from by { exact min_le_right _ _ } ] ;
  -- Step 1 (reach 1). There exists `M : ℕ` with `s M = 1`.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, s M = 1 := by
    -- By definition of `badSet`, if `f ∉ badSet ε δ`, then for all `k`, `s k < 1 → δ < s (k + 1) - s k`.
    have h_gap : ∀ k, s k < 1 → δ < s (k + 1) - s k := by
      exact fun k hk => lt_of_not_ge fun hk' => hf ⟨ k, hk, hk' ⟩;
    -- By contradiction, assume that $s k < 1$ for all $k$.
    by_contra h_contra
    push_neg at h_contra;
    -- By induction, we can show that $s k \geq k \delta$ for all $k$.
    have h_induction : ∀ k, s k ≥ k * δ := by
      exact fun k => Nat.recOn k ( by norm_num [ hs0 ] ) fun n ihn => by norm_num; linarith [ h_gap n ( lt_of_le_of_ne ( hle n ) ( h_contra n ) ) ] ;
    exact absurd ( h_induction ( ⌊1 / δ⌋₊ + 1 ) ) ( by push_cast; nlinarith [ Nat.lt_floor_add_one ( 1 / δ ), mul_div_cancel₀ 1 hδ.ne', hle ( ⌊1 / δ⌋₊ + 1 ) ] );
  -- Let `M := Nat.find ⟨N, ...⟩` be the least index with `s M = 1`. Then `M ≥ 1` (since `s 0 = 0 ≠ 1`), and for every `i < M` we have `s i < 1` (minimality of M plus `s i ≤ 1`).
  obtain ⟨M, hM⟩ : ∃ M : ℕ, s M = 1 ∧ ∀ k < M, s k < 1 := by
    exact ⟨ Nat.find ( ⟨ M, hM ⟩ : ∃ M, s M = 1 ), Nat.find_spec ( ⟨ M, hM ⟩ : ∃ M, s M = 1 ), fun k hk => lt_of_le_of_ne ( hle k ) fun h => Nat.find_min ( ⟨ M, hM ⟩ : ∃ M, s M = 1 ) hk h ⟩
  have hM_ge_1 : 1 ≤ M := by
    exact Nat.pos_of_ne_zero fun h => by subst h; linarith;
  have hM_lt : ∀ k < M, s k < 1 := by
    exact hM.2
  generalize_proofs at *; (
  -- Apply `cadlagModulus_le_of_crossing` with `M := M - 1` and `s := s`.
  have h_crossing : ∀ i < M - 1, δ < s (i + 1) - s i := by
    intros i hi
    have h_not_bad : ¬(s i < 1 ∧ s (i + 1) - s i ≤ δ) := by
      exact fun h => hf ⟨ i, h.1, h.2 ⟩
    generalize_proofs at *; (
    exact lt_of_not_ge fun h => h_not_bad ⟨ hM_lt i ( Nat.lt_of_lt_of_le hi ( Nat.pred_le _ ) ), h ⟩)
  have h_tail : δ < 1 - s (M - 1) := by
    contrapose! hf; use M - 1; rcases M with ( _ | M ) <;> simp_all +decide ;
    exact ⟨ hM_lt M le_rfl, by linarith ⟩
  have h_osc : ∀ i < M - 1, ∀ x ∈ Set.Ico (s i) (s (i + 1)), |f.toFun x - f.toFun (s i)| ≤ ε := by
    intros i hi x hx
    by_cases hxi : x = s i
    generalize_proofs at *; (
    aesop);
    convert crossTime_osc_le skoroEval ( s i ) ε f ( lt_of_le_of_ne hx.1 ( Ne.symm hxi ) ) _ using 1
    generalize_proofs at *; (
    have h_crossTime : s (i + 1) = min ((crossTime skoroEval (s i) ε f).untopD 1) 1 := by
      grind +locals
    generalize_proofs at *; (
    cases h : crossTime skoroEval ( s i ) ε f <;> simp_all +decide [ WithTop.untopD ]))
  have h_osc_tail : ∀ x ∈ Set.Ico (s (M - 1)) 1, |f.toFun x - f.toFun (s (M - 1))| ≤ ε := by
    intro x hx
    by_cases hx_eq : x = s (M - 1);
    · aesop;
    · apply crossTime_osc_le skoroEval (s (M - 1)) ε f (lt_of_le_of_ne hx.1 (Ne.symm hx_eq)) (by
      have h_crossTime : s M = min ((crossTime skoroEval (s (M - 1)) ε f).untopD 1) 1 := by
        cases M <;> tauto
      generalize_proofs at *; (
      cases h : crossTime skoroEval ( s ( M - 1 ) ) ε f <;> simp_all +decide [ WithTop.untopD ];
      linarith [ hle ( M - 1 ) ]))
  generalize_proofs at *; (
  convert cadlagModulus_le_of_crossing ( hε := hε ) ( hs0 := hs0 ) ( hlast := ?_ ) ( hmono := ?_ ) ( hsep := ?_ ) ( htail := ?_ ) ( hosc := ?_ ) ( hosctail := ?_ ) using 1 <;> norm_num [ hM_ge_1 ];
  exact M - 1
  all_goals generalize_proofs at *; try assumption;
  · exact hM_lt _ ( Nat.pred_lt ( ne_bot_of_gt hM_ge_1 ) );
  · exact fun i hi => by linarith [ h_crossing i hi ] ;
  · exact fun i hi x hx₁ hx₂ => h_osc i hi x ⟨ hx₁, hx₂ ⟩;
  · exact fun x hx₁ hx₂ => h_osc_tail x ⟨ hx₁, hx₂ ⟩))

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-! ## Item (1): crossing times iterated from a stopping time are stopping times

The frozen `isStoppingTime_crossTime` (Tight module) covers only a deterministic start `s`.
Here we upgrade it to an `ω`-dependent start `σ ω` where `σ` is itself a stopping time,
then iterate to conclude every `crossSeq` iterate is a stopping time. -/

/-
**Evaluation of an adapted process at a countably-valued time bounded by `v`.**  If
`g : Ω → ℝ` is `𝓕 v`-measurable, takes countably many values, and `g ω ≤ v` for all `ω`,
then `ω ↦ Y (g ω) ω` is `𝓕 v`-measurable.  (Case on the countable value: on `{g = w}` the
map is `Y w`, which is `𝓕 w ⊆ 𝓕 v`-measurable.)
-/
theorem measurable_eval_countable_time (𝓕 : Filtration ℝ m) {Y : ℝ → Ω → ℝ}
    (hadapt : ∀ r, Measurable[𝓕 r] (Y r)) (v : ℝ)
    {g : Ω → ℝ} (hg : Measurable[𝓕 v] g) (hcount : (Set.range g).Countable)
    (hle : ∀ ω, g ω ≤ v) :
    Measurable[𝓕 v] (fun ω => Y (g ω) ω) := by
  contrapose! hadapt;
  by_contra! h;
  apply_rules [ measurable_of_Iic ];
  intro x
  have h_preimage : (fun ω => Y (g ω) ω) ⁻¹' Iic x = ⋃ r ∈ Set.range g, {ω | g ω = r} ∩ {ω | Y r ω ≤ x} := by
    ext ω; simp [Set.mem_preimage, Set.mem_Iic];
    exact ⟨ fun hx => ⟨ ω, rfl, hx ⟩, by rintro ⟨ i, hi, hx ⟩ ; simpa [ hi ] using hx ⟩;
  refine' h_preimage ▸ MeasurableSet.biUnion hcount _;
  intro r hr
  have h_preimage : MeasurableSet[𝓕 v] {ω | g ω = r} := by
    exact hg ( MeasurableSingletonClass.measurableSet_singleton r );
  have h_preimage : MeasurableSet[𝓕 r] {ω | Y r ω ≤ x} := by
    exact measurableSet_le ( h r ) measurable_const;
  exact MeasurableSet.inter ‹_› ( 𝓕.mono ( show r ≤ v from by obtain ⟨ ω, rfl ⟩ := hr; exact hle ω ) _ h_preimage )

/-
The right-dyadic ceiling `⌈σ·2ⁿ⌉/2ⁿ` of a stopping time `σ`, clamped to `≤ v`, is
`𝓕 v`-measurable.
-/
theorem measurable_dyadicCeil_min (𝓕 : Filtration ℝ m)
    {σ : Ω → ℝ} (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ)))
    (n : ℕ) (v : ℝ) :
    Measurable[𝓕 v] (fun ω => min ((⌈σ ω * (2:ℝ)^n⌉ : ℝ) / (2:ℝ)^n) v) := by
  -- Apply the measurable_of_Iic lemma to show that the function is measurable.
  apply measurable_of_Iic;
  intro x
  by_cases hx : v ≤ x;
  · simp +decide [ hx, Set.preimage ];
  · have h_preimage : (fun ω => min ((⌈σ ω * (2 : ℝ) ^ n⌉ : ℝ) / (2 : ℝ) ^ n) v) ⁻¹' Iic x = {ω | σ ω ≤ ⌊x * (2 : ℝ) ^ n⌋ / (2 : ℝ) ^ n} := by
      ext ω; simp [hx];
      rw [ div_le_iff₀ ( by positivity ), le_div_iff₀ ( by positivity ) ];
      constructor <;> intro h <;> rw [ ← Int.le_floor ] at * <;> norm_cast at *;
      · exact le_trans ( Int.le_ceil _ ) ( mod_cast h );
      · exact Int.ceil_le.mpr ( mod_cast h );
    have h_preimage_measurable : MeasurableSet[𝓕 (⌊x * (2 : ℝ) ^ n⌋ / (2 : ℝ) ^ n)] {ω | σ ω ≤ ⌊x * (2 : ℝ) ^ n⌋ / (2 : ℝ) ^ n} := by
      convert hσ.measurableSet_le ( ⌊x * 2 ^ n⌋ / 2 ^ n ) using 1;
      norm_cast;
    exact h_preimage.symm ▸ h_preimage_measurable |> fun h => 𝓕.mono ( show ( ⌊x * 2 ^ n⌋ : ℝ ) / 2 ^ n ≤ v by
                                                                        exact le_trans ( div_le_iff₀ ( by positivity ) |>.2 ( Int.floor_le _ ) ) ( by linarith ) ) _ h

/-
**Stopped-value measurability for a right-continuous adapted real process.**  For an
adapted, per-path right-continuous process `Y` and a stopping time `σ`, the *clamped* stopped
value `ω ↦ Y (min (σ ω) v) ω` is `𝓕 v`-measurable.  Route: dyadic approximation of `σ` from
the right, `σₙ ω = ⌈σ ω · 2ⁿ⌉ / 2ⁿ` (a discrete stopping time `≥ σ`, `↓ σ`); the clamped
value `Y (min (σₙ ω) v) ω` is `𝓕 v`-measurable (countably many values, each a fixed-time
evaluation `≤ v`), and right-continuity gives the pointwise limit.
-/
theorem measurable_stoppedValue_min (𝓕 : Filtration ℝ m) {Y : ℝ → Ω → ℝ}
    (hadapt : ∀ r, Measurable[𝓕 r] (Y r))
    (hrc : ∀ ω t, ContinuousWithinAt (fun r => Y r ω) (Set.Ici t) t)
    {σ : Ω → ℝ} (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ)))
    (v : ℝ) :
    Measurable[𝓕 v] (fun ω => Y (min (σ ω) v) ω) := by
  by_contra h_not_measurable;
  exact h_not_measurable ( by
    convert measurable_of_tendsto_metrizable' atTop _ _;
    all_goals try infer_instance;
    exact fun n ω => Y ( min ( ( ⌈σ ω * 2 ^ n⌉ : ℝ ) / 2 ^ n ) v ) ω;
    all_goals try infer_instance;
    · intro n;
      apply_rules [ measurable_eval_countable_time, measurable_dyadicCeil_min ];
      · refine' Set.Countable.mono _ ( Set.countable_range ( fun k : ℤ => ( k : ℝ ) / 2 ^ n ) |> Set.Countable.union <| Set.countable_singleton v );
        grind;
      · exact fun ω => min_le_right _ _;
    · refine' tendsto_pi_nhds.mpr _;
      intro ω;
      have h_lim : Filter.Tendsto (fun n => min (⌈σ ω * 2 ^ n⌉ / 2 ^ n : ℝ) v) Filter.atTop (nhds (min (σ ω) v)) := by
        refine' Filter.Tendsto.min _ tendsto_const_nhds;
        refine' ( tendsto_iff_norm_sub_tendsto_zero.mpr _ );
        norm_num [ div_sub' ];
        refine' squeeze_zero ( fun _ => div_nonneg ( abs_nonneg _ ) ( pow_nonneg zero_le_two _ ) ) ( fun e => div_le_div_of_nonneg_right ( show |↑⌈σ ω * 2 ^ e⌉ - 2 ^ e * σ ω| ≤ 1 by erw [ abs_le ] ; constructor <;> linarith [ Int.le_ceil ( σ ω * 2 ^ e ), Int.ceil_lt_add_one ( σ ω * 2 ^ e ) ] ) ( pow_nonneg zero_le_two _ ) ) ( tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) );
      have := hrc ω ( min ( σ ω ) v );
      refine' this.tendsto.comp _;
      rw [ tendsto_nhdsWithin_iff ];
      simp +zetaDelta at *;
      exact ⟨ h_lim, 0, fun n hn => Or.inl <| by rw [ le_div_iff₀ <| by positivity ] ; linarith [ Int.le_ceil ( σ ω * 2 ^ n ) ] ⟩ )

/-
`{σ < q}` is `𝓕 v`-measurable whenever `q ≤ v`, for a stopping time `σ`.
-/
theorem measurableSet_stoppingTime_lt (𝓕 : Filtration ℝ m)
    {σ : Ω → ℝ} (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ)))
    {q v : ℝ} (hqv : q ≤ v) :
    MeasurableSet[𝓕 v] {ω | σ ω < q} := by
  -- We'll use the fact that if the stops processes, then the set $\{ω : σ ω < q\}$ is measurable.
  have h_meas : ∀ q : ℝ, q ≤ v → MeasurableSet[𝓕 v] {ω | σ ω < q} := by
    intro q hqv
    have h_meas : ∀ p : ℚ, p < q → MeasurableSet[𝓕 v] {ω | σ ω ≤ p} := by
      intro p hpq
      have h_meas : MeasurableSet[𝓕 (p : ℝ)] {ω | σ ω ≤ p} := by
        convert hσ.measurableSet_le ( p : ℝ ) using 1;
        norm_cast;
      exact 𝓕.mono ( show ( p : ℝ ) ≤ v by linarith ) _ h_meas;
    convert MeasurableSet.biUnion ( Set.to_countable ( { p : ℚ | ( p : ℝ ) < q } ) ) fun p hp => h_meas p hp using 1;
    ext ω; simp [Set.mem_iUnion];
    exact ⟨ fun h => by rcases exists_rat_btwn h with ⟨ p, hp₁, hp₂ ⟩ ; exact ⟨ p, hp₂, hp₁.le ⟩, fun ⟨ p, hp₁, hp₂ ⟩ => lt_of_le_of_lt hp₂ hp₁ ⟩;
  convert h_meas q hqv

/-- **Measurable-set form of the crossing after a stopping time.**  Mirrors
`measurableSet_crossTime_le` but with the `ω`-dependent start `σ ω`; the stopped value
`Y (σ ω) ω` is handled by `measurable_stoppedValue_min`. -/
theorem measurableSet_crossTime_le_of_stoppingTime (𝓕 : Filtration ℝ m) {Y : ℝ → Ω → ℝ}
    (hadapt : ∀ r, Measurable[𝓕 r] (Y r))
    (hrc : ∀ ω t, ContinuousWithinAt (fun r => Y r ω) (Set.Ici t) t)
    {σ : Ω → ℝ} (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ)))
    (ε t : ℝ) :
    MeasurableSet[𝓕.rightCont t] {ω | crossTime Y (σ ω) ε ω ≤ (t : WithTop ℝ)} := by
  have h_crossTime_le_iff : ∀ ω, crossTime Y (σ ω) ε ω ≤ (t : WithTop ℝ) ↔
      ∀ u : ℚ, t < (u : ℝ) → ∃ q : ℚ, σ ω < (q : ℝ) ∧ (q : ℝ) < (u : ℝ) ∧
        ε < |Y q ω - Y (σ ω) ω| := by
    intro ω
    rw [crossTime_le_iff Y (σ ω) ε ω (hrc ω)]
  refine measurableSet_rightCont_of 𝓕 (fun v hv => ?_)
  have h_set_eq : {ω | crossTime Y (σ ω) ε ω ≤ (t : WithTop ℝ)}
      = ⋂ (u : ℚ), ⋂ (_ : (t : ℝ) < u ∧ (u : ℝ) ≤ v), ⋃ (q : ℚ), ⋃ (_ : (q : ℝ) < (u : ℝ)),
          ({ω | σ ω < (q : ℝ)} ∩ {ω | ε < |Y q ω - Y (min (σ ω) v) ω|}) := by
    ext ω; simp only [h_crossTime_le_iff, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion,
      Set.mem_inter_iff]
    constructor <;> intro h u hu
    · obtain ⟨q, hq₁, hq₂, hq₃⟩ := h u hu.1
      refine ⟨q, hq₂, hq₁, ?_⟩
      rw [min_eq_left (by linarith [show (q : ℝ) ≤ v from le_trans (le_of_lt hq₂) hu.2])]
      exact hq₃
    · obtain ⟨w, hw₁, hw₂, hw₃⟩ : ∃ w : ℚ, t < (w : ℝ) ∧ (w : ℝ) ≤ v ∧ (w : ℝ) < (u : ℝ) := by
        by_cases huv : (u : ℝ) ≤ v
        · cases' exists_rat_btwn hu with w hw
          exact ⟨w, hw.1, hw.2.le.trans huv, hw.2⟩
        · cases' exists_rat_btwn hv with w hw
          exact ⟨w, hw.1, hw.2.le, hw.2.trans_le (le_of_not_ge huv)⟩
      obtain ⟨q, hqw, hσq, hq₃⟩ := h w ⟨hw₁, hw₂⟩
      refine ⟨q, hσq, hqw.trans hw₃, ?_⟩
      rw [min_eq_left (by linarith [show (q : ℝ) ≤ v from le_trans (le_of_lt hqw) hw₂])] at hq₃
      exact hq₃
  rw [h_set_eq]
  refine MeasurableSet.biInter (Set.to_countable _) (fun u hu =>
    MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun hq => MeasurableSet.inter ?_ ?_)))
  · exact measurableSet_stoppingTime_lt 𝓕 hσ (le_trans (le_of_lt hq) hu.2)
  · have hqv : (q : ℝ) ≤ v := le_trans (le_of_lt hq) hu.2
    have hYq : Measurable[𝓕 v] (Y (q : ℝ)) := (hadapt (q : ℝ)).mono (𝓕.mono hqv) le_rfl
    have hstop : Measurable[𝓕 v] (fun ω => Y (min (σ ω) v) ω) :=
      measurable_stoppedValue_min 𝓕 hadapt hrc hσ v
    have hsub : Measurable[𝓕 v] (fun ω => Y (q : ℝ) ω - Y (min (σ ω) v) ω) := hYq.sub hstop
    have hopen : MeasurableSet {y : ℝ | ε < |y|} :=
      (isOpen_lt continuous_const continuous_abs).measurableSet
    have hpre := hsub hopen
    convert hpre using 1

/-- **The crossing after a stopping time is a stopping time** (of the right-continuous
augmentation). -/
theorem isStoppingTime_crossTime_of_stoppingTime (𝓕 : Filtration ℝ m) {Y : ℝ → Ω → ℝ}
    (hadapt : ∀ r, Measurable[𝓕 r] (Y r))
    (hrc : ∀ ω t, ContinuousWithinAt (fun r => Y r ω) (Set.Ici t) t)
    {σ : Ω → ℝ} (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ)))
    (ε : ℝ) :
    IsStoppingTime 𝓕.rightCont (fun ω => crossTime Y (σ ω) ε ω) := by
  intro t
  exact measurableSet_crossTime_le_of_stoppingTime 𝓕 hadapt hrc hσ ε t

/-
Clamping a `WithTop ℝ`-valued stopping time by `min (·.untopD 1) 1` (as in `crossSeq`)
yields an `ℝ`-valued stopping time.
-/
theorem isStoppingTime_min_untopD_one (𝓕 : Filtration ℝ m) {T : Ω → WithTop ℝ}
    (hT : IsStoppingTime 𝓕 T) :
    IsStoppingTime 𝓕 (fun ω => ((min ((T ω).untopD 1) 1 : ℝ) : WithTop ℝ)) := by
  intro s; by_cases hs : 1 ≤ s <;> simp +decide [ hs ] ;
  have h_eq : ∀ ω, (WithTop.untopD 1 (T ω)) ≤ s ↔ T ω ≤ s := by
    intro ω; cases h : T ω <;> simp +decide [ h ] ;
    linarith;
  simp_all +decide [ IsStoppingTime ]

/-- **Item (1) conclusion.**  Every `crossSeq` iterate of a measurable càdlàg random element
`X`, adapted to a right-continuous filtration `𝓕` (`hrc : 𝓕.rightCont = 𝓕`), is an
`𝓕`-stopping time.  Proved by induction on `k` from
`isStoppingTime_crossTime_of_stoppingTime`. -/
theorem isStoppingTime_crossSeq (𝓕 : Filtration ℝ m) (hrc : 𝓕.rightCont = 𝓕)
    {X : Ω → Skoro} (hX : Measurable X)
    (hadapt : ∀ r, Measurable[𝓕 r] (fun ω => (X ω).toFun r))
    (ε : ℝ) (k : ℕ) :
    IsStoppingTime 𝓕 (fun ω => ((crossSeq ε (X ω) k : ℝ) : WithTop ℝ)) := by
  have hrcY : ∀ ω t, ContinuousWithinAt (fun r => (X ω).toFun r) (Set.Ici t) t :=
    fun ω t => Skoro.rightContinuous (X ω) t
  induction k with
  | zero =>
    simpa only [crossSeq] using isStoppingTime_const 𝓕 (0 : ℝ)
  | succ k ih =>
    have hcross : IsStoppingTime 𝓕
        (fun ω => crossTime (fun t ω => (X ω).toFun t) (crossSeq ε (X ω) k) ε ω) := by
      have h := isStoppingTime_crossTime_of_stoppingTime 𝓕 hadapt hrcY ih ε
      rwa [hrc] at h
    have h := isStoppingTime_min_untopD_one 𝓕 hcross
    convert h using 2

/-
Each `crossSeq` iterate is also Borel-measurable as an `ℝ`-valued map (it is a stopping
time, but this is the plain-measurability corollary used by `consecutive_crossing_bound`).
-/
theorem measurable_crossSeq {X : Ω → Skoro} (hX : Measurable X) (ε : ℝ) (k : ℕ) :
    Measurable (fun ω => crossSeq ε (X ω) k) := by
  induction' k with k ih;
  · exact measurable_const;
  · have h_crossTime_le : ∀ x : ℝ, MeasurableSet {ω | crossTime skoroEval (crossSeq ε (X ω) k) ε (X ω) ≤ x} := by
      intro x
      have h_crossTime_le : ∀ u : ℚ, MeasurableSet {ω | ∀ q : ℚ, x < q → ∃ r : ℚ, crossSeq ε (X ω) k < r ∧ r < q ∧ ε < |(X ω).toFun r - (X ω).toFun (crossSeq ε (X ω) k)|} := by
        intro u
        have h_crossTime_le : ∀ q : ℚ, x < q → MeasurableSet {ω | ∃ r : ℚ, crossSeq ε (X ω) k < r ∧ r < q ∧ ε < |(X ω).toFun r - (X ω).toFun (crossSeq ε (X ω) k)|} := by
          intro q hq
          have h_crossTime_le : ∀ r : ℚ, MeasurableSet {ω | crossSeq ε (X ω) k < r ∧ r < q ∧ ε < |(X ω).toFun r - (X ω).toFun (crossSeq ε (X ω) k)|} := by
            intro r
            have h_crossTime_le : MeasurableSet {ω | crossSeq ε (X ω) k < r ∧ ε < |(X ω).toFun r - (X ω).toFun (crossSeq ε (X ω) k)|} := by
              have h_crossTime_le : Measurable (fun ω => (X ω).toFun r - (X ω).toFun (crossSeq ε (X ω) k)) := by
                have h_crossTime_le : Measurable (fun ω => (X ω).toFun r) := by
                  exact SkorokhodBasic.measurable_eval _ |> Measurable.comp <| hX;
                convert h_crossTime_le.sub ( measurable_eval_prod hX |> Measurable.comp <| ih.prodMk measurable_id' ) using 1;
              exact MeasurableSet.inter ( measurableSet_lt ih measurable_const ) ( measurableSet_lt measurable_const ( h_crossTime_le.norm ) );
            by_cases hr : r < q <;> simp +decide [ hr, h_crossTime_le ];
          convert MeasurableSet.iUnion fun r : ℚ => h_crossTime_le r using 1;
          aesop;
        convert MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq => h_crossTime_le q hq using 1 ; aesop;
      convert h_crossTime_le 0 using 1;
      ext ω; simp [crossTime_le_iff];
      convert crossTime_le_iff skoroEval ( crossSeq ε ( X ω ) k ) ε ( X ω ) ( fun t => Skoro.rightContinuous ( X ω ) t ) x using 1;
      norm_cast;
    refine' measurable_of_Iic _;
    intro x
    simp [crossSeq];
    by_cases hx : x ≥ 1;
    · convert MeasurableSet.univ using 1 ; ext ω ; aesop;
    · convert h_crossTime_le x using 1;
      ext ω; simp [hx];
      grind +suggestions

/-! ## The genuine two-scale Aldous architecture (replacing the refuted `badSet` route)

Task 8 refuted `prob_map_badSet_le`: no `δ`-independent constant bounds
`(P.map X)(badSet ε δ)/aldousQ(2δ,ε/2)` (the "first bad crossing" is future-dependent, and
the honest union bound costs a factor `⌈1/δ⌉`).  That analysis was correct and the refuted
lemma is deleted.  We replace it with Aldous's original two-scale argument
(D. Aldous, *Stopping times and tightness*, Ann. Probab. 6 (1978) 335–340, (13)–(25)):
the union-bound cost is paid by invoking the Aldous hypothesis **twice** — once at a coarse
scale `δ` with tolerance `η₁` (crossing count) and once at a fine scale `σ ≤ δ` with
tolerance `η₂/q` where `q ≈ 2/δ` (gap separation).  Each crossing time is itself a stopping
time (`isStoppingTime_crossSeq`) and receives its own direct increment bound; no
future-dependent index selection occurs anywhere. -/

/-
**Step 2 (shift-average bound; Aldous (23)–(24)).**  For a stopping time `τ ≤ 1` and a
scale `d > 0`, the fiber measure
`L(ω) = Leb{ s ∈ (0,2d] : e ≤ |X(τ+s) - X τ| }` has `∫ L ∂P ≤ 2d·α(2d,e)` (Tonelli plus the
definitional bound `le_aldousQ_of_stoppingTime`, using `flatR` for the truncation), so by
Markov at level `d/2` the event `{L ≥ d/2}` has mass `≤ 4·α(2d,e)`.  No abstract conditional
expectation is needed: Aldous's `P(·|F) ≥ 1/4` device is exactly this explicit fiber
average.
-/
theorem prob_fiber_ge_le (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Skoro)
    (hX : Measurable X) (𝓕 : Filtration ℝ m)
    {τ : Ω → ℝ} (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ)))
    (hτmeas : Measurable τ) (hτ1 : ∀ ω, τ ω ≤ 1) {d e : ℝ} (hd : 0 < d) :
    P {ω | ENNReal.ofReal (d / 2) ≤
        volume {s : ℝ | s ∈ Set.Ioc (0 : ℝ) (2 * d) ∧
          e ≤ |(X ω).toFun (τ ω + s) - (X ω).toFun (τ ω)|}}
      ≤ 4 * aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * d) e := by
  refine' le_trans ( MeasureTheory.meas_ge_le_lintegral_div _ _ _ ) _;
  · have h_measurable : Measurable (fun p : ℝ × Ω => |(X p.2).toFun (τ p.2 + p.1) - (X p.2).toFun (τ p.2)|) := by
      have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun (τ p.2 + p.1)) := by
        have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun p.1) := by
          grind +suggestions;
        convert h_measurable.comp ( show Measurable fun p : ℝ × Ω => ( τ p.2 + p.1, p.2 ) from Measurable.prodMk ( hτmeas.comp measurable_snd |> Measurable.add <| measurable_fst ) measurable_snd ) using 1;
      have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun (τ p.2)) := by
        convert h_measurable.comp ( show Measurable fun p : ℝ × Ω => ( 0, p.2 ) from measurable_const.prodMk measurable_snd ) using 1;
        aesop;
      fun_prop;
    refine' Measurable.aemeasurable _;
    convert measurable_measure_prodMk_right ( show MeasurableSet { p : ℝ × Ω | p.1 ∈ Set.Ioc 0 ( 2 * d ) ∧ e ≤ |( X p.2 ).toFun ( τ p.2 + p.1 ) - ( X p.2 ).toFun ( τ p.2 )| } from ?_ ) using 1;
    · infer_instance;
    · exact MeasurableSet.inter ( measurableSet_Ioc.preimage measurable_fst ) ( measurableSet_le measurable_const h_measurable );
  · exact ne_of_gt ( ENNReal.ofReal_pos.mpr ( half_pos hd ) );
  · exact ENNReal.ofReal_ne_top;
  · rw [ ENNReal.div_le_iff_le_mul ];
    · -- By Fubini's theorem, we can interchange the order of integration.
      have h_fubini : ∫⁻ ω, ∫⁻ s in Set.Ioc 0 (2 * d), (if e ≤ |(X ω).toFun (τ ω + s) - (X ω).toFun (τ ω)| then 1 else 0) ∂volume ∂P ≤ ∫⁻ s in Set.Ioc 0 (2 * d), aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * d) e ∂volume := by
        rw [ MeasureTheory.lintegral_lintegral_swap ];
        · refine' MeasureTheory.setLIntegral_mono' measurableSet_Ioc fun s hs => _;
          convert prob_shift_le_aldousQ P X 𝓕 hτ hτ1 ( show 0 ≤ s by linarith [ hs.1 ] ) ( show s ≤ 2 * d by linarith [ hs.2 ] ) using 1;
          erw [ MeasureTheory.lintegral_indicator ];
          · aesop;
          · have h_measurable : Measurable (fun ω => (X ω).toFun (τ ω + s) - (X ω).toFun (τ ω)) := by
              have h_measurable : Measurable (fun ω => (X ω).toFun (τ ω + s)) ∧ Measurable (fun ω => (X ω).toFun (τ ω)) := by
                constructor;
                · have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun p.1) := by
                    grind +suggestions;
                  convert h_measurable.comp ( show Measurable fun ω => ( τ ω + s, ω ) from Measurable.prodMk ( hτmeas.add_const s ) measurable_id' ) using 1;
                · have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun p.1) := by
                    grind +suggestions;
                  exact h_measurable.comp ( hτmeas.prodMk measurable_id' );
              exact h_measurable.1.sub h_measurable.2;
            exact measurableSet_le measurable_const ( h_measurable.norm );
        · refine' Measurable.aemeasurable _;
          refine' Measurable.ite _ measurable_const measurable_const;
          have h_measurable : Measurable (fun p : Ω × ℝ => (X p.1).toFun (τ p.1 + p.2) - (X p.1).toFun (τ p.1)) := by
            have h_measurable : Measurable (fun p : ℝ × Ω => (X p.2).toFun p.1) := by
              grind +suggestions;
            convert h_measurable.comp ( show Measurable fun p : Ω × ℝ => ( τ p.1 + p.2, p.1 ) from Measurable.prodMk ( hτmeas.comp measurable_fst |> Measurable.add <| measurable_snd ) measurable_fst ) |> Measurable.sub <| h_measurable.comp ( show Measurable fun p : Ω × ℝ => ( τ p.1, p.1 ) from Measurable.prodMk ( hτmeas.comp measurable_fst ) measurable_fst ) using 1;
          exact measurableSet_le measurable_const ( h_measurable.norm );
      convert h_fubini using 1;
      · congr! 2;
        erw [ MeasureTheory.lintegral_indicator ];
        · simp +decide [ Set.setOf_and, Set.setOf_exists ];
          exact congr_arg _ ( by ext; aesop );
        · exact measurableSet_le measurable_const ( measurable_norm.comp ( measurable_id'.comp ( measurable_id'.const_add _ ) |> Measurable.comp ( Skoro.measurable_toFun _ ) |> Measurable.sub <| measurable_const ) );
      · simp +decide [ mul_assoc, mul_comm, mul_left_comm, ENNReal.ofReal_mul hd.le ];
        rw [ show d = 2 * ( d / 2 ) by ring, ENNReal.ofReal_mul ] <;> norm_num ; ring;
    · exact Or.inl ( ne_of_gt ( ENNReal.ofReal_pos.mpr ( half_pos hd ) ) );
    · exact Or.inl ENNReal.ofReal_ne_top

/-
**Step 3 (window-overlap pigeonhole; Aldous (21)–(22)).**  If `t₁ ≤ t₂` with
`t₂ - t₁ < d` and the total increment `|f t₂ - f t₁| ≥ e`, then at least one of the two
shift-fiber bad sets (over shifts in `(0,2d]`, at level `e/2`) has Lebesgue measure `≥ d/2`.
Reason: the windows `[t₁,t₁+2d]` and `[t₂,t₂+2d]` overlap in an interval of length
`t₁+2d-t₂ > d`; if both bad sets had measure `< d/2` there would be a common good time `θ`,
whence `|f t₂ - f t₁| ≤ |f θ - f t₁| + |f θ - f t₂| < e`, a contradiction.
-/
theorem window_overlap_pigeonhole {f : ℝ → ℝ} {t₁ t₂ d e : ℝ}
    (hd : 0 < d) (h12 : t₁ ≤ t₂) (hgap : t₂ - t₁ ≤ d) (hcross : e ≤ |f t₂ - f t₁|) :
    ENNReal.ofReal (d / 2) ≤
        volume {s : ℝ | s ∈ Set.Ioc (0 : ℝ) (2 * d) ∧ e / 2 ≤ |f (t₁ + s) - f t₁|} ∨
    ENNReal.ofReal (d / 2) ≤
        volume {s : ℝ | s ∈ Set.Ioc (0 : ℝ) (2 * d) ∧ e / 2 ≤ |f (t₂ + s) - f t₂|} := by
  by_contra! h_contra;
  -- Consider the overlap interval of absolute times I = Set.Ioc t₂ (t₁ + 2d).
  set I := Set.Ioc t₂ (t₁ + 2 * d) with hI_def;
  -- By assumption, $I \subseteq G₁ \cup G₂$.
  have h_I_subset_G1G2 : I ⊆ (fun s => t₁ + s) '' {s | s ∈ Set.Ioc 0 (2 * d) ∧ e / 2 ≤ |f (t₁ + s) - f t₁|} ∪ (fun s => t₂ + s) '' {s | s ∈ Set.Ioc 0 (2 * d) ∧ e / 2 ≤ |f (t₂ + s) - f t₂|} := by
    intro x hx; simp_all +decide [ Set.subset_def ] ;
    grind +splitIndPred;
  -- By measure monotonicity, $\text{volume}(I) \leq \text{volume}(G₁) + \text{volume}(G₂)$.
  have h_volume_I_le_volume_G1G2 : volume I ≤ volume {s | s ∈ Set.Ioc 0 (2 * d) ∧ e / 2 ≤ |f (t₁ + s) - f t₁|} + volume {s | s ∈ Set.Ioc 0 (2 * d) ∧ e / 2 ≤ |f (t₂ + s) - f t₂|} := by
    refine' le_trans ( MeasureTheory.measure_mono h_I_subset_G1G2 ) _;
    refine' le_trans ( MeasureTheory.measure_union_le _ _ ) _;
    norm_num [ Set.image_add_left ];
    rw [ show { a : ℝ | ( t₁ < a ∧ a ≤ t₁ + 2 * d ) ∧ e / 2 ≤ |f a - f t₁| } = ( fun s => t₁ + s ) '' { s : ℝ | ( 0 < s ∧ s ≤ 2 * d ) ∧ e / 2 ≤ |f ( t₁ + s ) - f t₁| } from ?_, show { a : ℝ | ( t₂ < a ∧ a ≤ t₂ + 2 * d ) ∧ e / 2 ≤ |f a - f t₂| } = ( fun s => t₂ + s ) '' { s : ℝ | ( 0 < s ∧ s ≤ 2 * d ) ∧ e / 2 ≤ |f ( t₂ + s ) - f t₂| } from ?_ ];
    · rw [ Set.image_add_left, Set.image_add_left ];
      rw [ MeasureTheory.measure_preimage_add, MeasureTheory.measure_preimage_add ];
    · ext; simp [Set.mem_image];
    · ext ; aesop;
  simp +zetaDelta at *;
  exact absurd h_volume_I_le_volume_G1G2 ( by exact not_le_of_gt ( lt_of_lt_of_le ( ENNReal.add_lt_add h_contra.1 h_contra.2 ) ( by rw [ ← ENNReal.ofReal_add ( by linarith ) ( by linarith ) ] ; exact ENNReal.ofReal_le_ofReal ( by linarith ) ) ) )

/-
**Genuine-crossing value.**  When two consecutive crossing times are both `< 1`, the
increment between them is a genuine `ε`-crossing: `ε ≤ |X(T_{k+1}) - X(T_k)|`.  (At the
crossing time, which is the infimum of the strict `> ε` set, right-continuity forces the
increment to be `≥ ε`.)
-/
theorem crossSeq_crossing_ge {εc : ℝ} (f : Skoro) {k : ℕ}
    (h1 : crossSeq εc f k < 1) (h2 : crossSeq εc f (k + 1) < 1) :
    εc ≤ |f.toFun (crossSeq εc f (k + 1)) - f.toFun (crossSeq εc f k)| := by
  have h_inf : IsGLB {t | crossSeq εc f k < t ∧ εc < |f.toFun t - f.toFun (crossSeq εc f k)|} (crossSeq εc f (k + 1)) := by
    have h_crossTime : crossTime skoroEval (crossSeq εc f k) εc f = (crossSeq εc f (k + 1) : WithTop ℝ) := by
      have h_crossTime : crossTime skoroEval (crossSeq εc f k) εc f = (crossSeq εc f (k + 1) : WithTop ℝ) := by
        have h_crossTime_def : crossSeq εc f (k + 1) = min ((crossTime skoroEval (crossSeq εc f k) εc f).untopD 1) 1 := by
          rfl
        cases h : crossTime skoroEval ( crossSeq εc f k ) εc f <;> simp_all +decide [ WithTop.untopD ];
        linarith;
      exact h_crossTime;
    unfold crossTime at h_crossTime;
    split_ifs at h_crossTime <;> norm_cast at h_crossTime;
    exact h_crossTime ▸ isGLB_csInf ‹_› ⟨ _, fun x hx => hx.1.le ⟩;
  -- By definition of $crossSeq$, we know that there exists a sequence $\{t_n\}$ such that $t_n \to crossSeq εc f (k + 1)$ and $t_n \in {t | crossSeq εc f k < t ∧ εc < |f.toFun t - f.toFun (crossSeq εc f k)|}$.
  obtain ⟨t_n, ht_n⟩ : ∃ t_n : ℕ → ℝ, Filter.Tendsto t_n Filter.atTop (nhds (crossSeq εc f (k + 1))) ∧ ∀ n, crossSeq εc f k < t_n n ∧ εc < |f.toFun (t_n n) - f.toFun (crossSeq εc f k)| := by
    have := h_inf.exists_seq_antitone_tendsto;
    exact Exists.elim ( this ( by exact Set.nonempty_iff_ne_empty.mpr <| by aesop_cat ) ) fun u hu => ⟨ u, hu.2.2.1, hu.2.2.2 ⟩;
  have h_right_cont : Filter.Tendsto (fun n => f.toFun (t_n n)) Filter.atTop (nhds (f.toFun (crossSeq εc f (k + 1)))) := by
    convert Skoro.rightContinuous f ( crossSeq εc f ( k + 1 ) ) |> ContinuousWithinAt.tendsto |> Filter.Tendsto.comp <| Filter.tendsto_inf.mpr ⟨ ht_n.1, _ ⟩ using 1;
    exact Filter.tendsto_principal.mpr ( Filter.Eventually.of_forall fun n => h_inf.1 ⟨ ht_n.2 n |>.1, ht_n.2 n |>.2 ⟩ );
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds ( Filter.Tendsto.abs ( h_right_cont.sub_const _ ) ) fun n => le_of_lt ( ht_n.2 n |>.2 )

/-
Basic monotonicity and clamping facts about the crossing sequence.
-/
theorem crossSeq_le_one {εc : ℝ} (f : Skoro) (k : ℕ) : crossSeq εc f k ≤ 1 := by
  exact Nat.recOn k ( by norm_num [ crossSeq ] ) fun k ih => by rw [ crossSeq ] ; exact min_le_right _ _;

theorem crossSeq_mono {εc : ℝ} (f : Skoro) {j k : ℕ} (h : j ≤ k) :
    crossSeq εc f j ≤ crossSeq εc f k := by
  induction' h with k hk ih;
  · rfl;
  · -- By definition of crossSeq, we have crossSeq εc f (k + 1) = min ((crossTime skoroEval (crossSeq εc f k) εc f).untopD 1) 1.
    rw [crossSeq];
    refine' le_min _ _;
    · by_cases h : crossTime skoroEval ( crossSeq εc f k ) εc f = ⊤ <;> simp_all +decide [ crossTime ];
      · exact le_trans ih ( crossSeq_le_one _ _ );
      · exact le_trans ih ( le_csInf h fun x hx => hx.1.le );
    · exact le_trans ih ( crossSeq_le_one f k )

/-
When the `(k+1)`-th crossing is still `< 1`, it equals the (finite) first-crossing time
after the `k`-th, so the min/clamp is inactive.
-/
theorem crossSeq_succ_eq_crossTime {εc : ℝ} (f : Skoro) (k : ℕ)
    (hk : crossSeq εc f (k + 1) < 1) :
    crossTime skoroEval (crossSeq εc f k) εc f = ((crossSeq εc f (k + 1) : ℝ) : WithTop ℝ) := by
  cases h : crossTime skoroEval ( crossSeq εc f k ) εc f <;> simp_all +decide [ crossSeq ];
  linarith

/-
**Per-cell oscillation.**  On the cell `[T_k, T_{k+1})` (when `T_{k+1} < 1`) the
left-endpoint oscillation is `≤ εc` (before the first crossing after `T_k`).
-/
theorem crossSeq_osc_le {εc : ℝ} (f : Skoro) (k : ℕ) (hk : crossSeq εc f (k + 1) < 1)
    {x : ℝ} (hx : x ∈ Set.Ico (crossSeq εc f k) (crossSeq εc f (k + 1))) :
    |f.toFun x - f.toFun (crossSeq εc f k)| ≤ εc := by
  by_cases hx_eq : x = crossSeq εc f k;
  · by_cases hεc : 0 ≤ εc <;> simp_all +decide [ abs_le ];
    contrapose! hx;
    rw [ show crossSeq εc f ( k + 1 ) = min ( ( crossTime skoroEval ( crossSeq εc f k ) εc f ).untopD 1 ) 1 from rfl ] ; simp +decide [ hx, crossTime ] ;
    split_ifs <;> simp_all +decide [ Set.Nonempty ];
    · rw [ show { t : ℝ | crossSeq εc f k < t ∧ εc < |skoroEval t f - skoroEval ( crossSeq εc f k ) f| } = Set.Ioi ( crossSeq εc f k ) from ?_ ] ; norm_num [ hx ];
      grind;
    · rename_i h; specialize h ( crossSeq εc f k + 1 ) ( by linarith ) ; linarith [ abs_le.mp h ] ;
  · convert crossTime_osc_le skoroEval ( crossSeq εc f k ) εc f ?_ ?_;
    · exact lt_of_le_of_ne hx.1 ( Ne.symm hx_eq );
    · rw [ crossSeq_succ_eq_crossTime f k hk ] ; exact WithTop.coe_lt_coe.mpr ( by linarith [ hx.1, hx.2 ] ) ;

/-
**Combined bad-pair bound (Step 2 ∘ Step 3).**  For each fixed index `k`, the event that
consecutive crossings `T_k, T_{k+1}` are both `< 1` and within `d` obeys
`P(…) ≤ 8·α(2d, εc/2)`.  (Pigeonhole places the event inside `A_d(T_k) ∪ A_d(T_{k+1})`; each
`A` has mass `≤ 4·α` by Step 2, both `T_k, T_{k+1}` being stopping times `≤ 1`.)
-/
theorem prob_badpair_le (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Skoro)
    (hX : Measurable X) (𝓕 : Filtration ℝ m) (hrc : 𝓕.rightCont = 𝓕)
    (hadapt : ∀ r, Measurable[𝓕 r] (fun ω => (X ω).toFun r))
    {εc : ℝ} (hεc : 0 < εc) {d : ℝ} (hd : 0 < d) (k : ℕ) :
    P {ω | crossSeq εc (X ω) k < 1 ∧ crossSeq εc (X ω) (k + 1) < 1 ∧
        crossSeq εc (X ω) (k + 1) - crossSeq εc (X ω) k < d}
      ≤ 8 * aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * d) (εc / 2) := by
  refine' le_trans _ ( _ : _ ≤ _ );
  exact P { ω | ENNReal.ofReal ( d / 2 ) ≤ volume { s : ℝ | s ∈ Set.Ioc 0 ( 2 * d ) ∧ εc / 2 ≤ |( X ω ).toFun ( crossSeq εc ( X ω ) k + s ) - ( X ω ).toFun ( crossSeq εc ( X ω ) k )| } } + P { ω | ENNReal.ofReal ( d / 2 ) ≤ volume { s : ℝ | s ∈ Set.Ioc 0 ( 2 * d ) ∧ εc / 2 ≤ |( X ω ).toFun ( crossSeq εc ( X ω ) ( k + 1 ) + s ) - ( X ω ).toFun ( crossSeq εc ( X ω ) ( k + 1 ) )| } };
  · refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
    intro ω hω
    obtain ⟨h1, h2, h3⟩ := hω
    have h_cross : εc ≤ |(X ω).toFun (crossSeq εc (X ω) (k + 1)) - (X ω).toFun (crossSeq εc (X ω) k)| :=
      crossSeq_crossing_ge (X ω) h1 h2
    exact window_overlap_pigeonhole hd (crossSeq_mono (X ω) (Nat.le_succ k)) h3.le h_cross;
  · convert add_le_add ( prob_fiber_ge_le P X hX 𝓕 ( isStoppingTime_crossSeq 𝓕 hrc hX hadapt εc k ) ( measurable_crossSeq hX εc k ) ( fun ω => crossSeq_le_one ( X ω ) k ) hd ) ( prob_fiber_ge_le P X hX 𝓕 ( isStoppingTime_crossSeq 𝓕 hrc hX hadapt εc ( k + 1 ) ) ( measurable_crossSeq hX εc ( k + 1 ) ) ( fun ω => crossSeq_le_one ( X ω ) ( k + 1 ) ) hd ) using 1 ; ring

/-
Pure `ℝ≥0∞` arithmetic backing the crossing-count division: if `m·(x - c) ≤ x` with
`x` finite and `m > 2` finite, then `x ≤ 2·c`.  (Truncated subtraction: when `x ≤ c` the
conclusion is immediate; when `x > c`, pass to reals and use `m/(m-1) < 2`.)
-/
theorem enn_count_arith {x c m : ℝ≥0∞} (hx : x ≠ ⊤) (hm : 2 < m) (hmtop : m ≠ ⊤)
    (h : m * (x - c) ≤ x) : x ≤ 2 * c := by
  by_cases hc : c = ⊤;
  · aesop;
  · by_cases hxc : x ≤ c;
    · exact le_trans hxc ( le_mul_of_one_le_left' <| by norm_num );
    · rw [ ← ENNReal.toReal_le_toReal ] at * <;> simp_all +decide [ ENNReal.toReal_mul ];
      · rw [ ENNReal.toReal_sub_of_le hxc.le ] at h;
        · nlinarith [ show ( m.toReal : ℝ ) > 2 by exact_mod_cast ENNReal.toReal_strict_mono ( by aesop ) hm, show ( c.toReal : ℝ ) ≥ 0 by positivity, show ( x.toReal : ℝ ) ≥ c.toReal by exact_mod_cast ENNReal.toReal_mono ( by aesop ) hxc.le ];
        · exact hx;
      · exact ENNReal.mul_ne_top hmtop ( by aesop );
      · exact ENNReal.mul_ne_top ( by norm_num ) hc

/-
**Step 4b (crossing count; Aldous (14)–(15)).**  With the coarse scale `δ` and an integer
`q` with `q·δ > 2`, the probability that there are at least `q` crossings before time `1`
(`T_q < 1`) is `≤ 16·η₁`, where `α(2δ, εc/2) ≤ η₁`.  Proof by the elementary
event-conditioning identity `E[Y_i·1_B] ≥ δ(P(B) - P(T_i<1, T_i<T_{i-1}+δ))` summed and
telescoped (`Σ Y_i = T_q ∧ 1`), then `q·δ > 2` forcing `P(B) ≤ 16·η₁`.  No filtration
conditioning is used, only expectations of indicator-weighted gaps.
-/
theorem prob_crossSeq_lt_one_le (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Skoro)
    (hX : Measurable X) (𝓕 : Filtration ℝ m) (hrc : 𝓕.rightCont = 𝓕)
    (hadapt : ∀ r, Measurable[𝓕 r] (fun ω => (X ω).toFun r))
    {εc δ : ℝ} (hεc : 0 < εc) (hδ : 0 < δ) (q : ℕ) (hq : 2 < (q : ℝ) * δ)
    {η₁ : ℝ≥0∞} (hQδ : aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * δ) (εc / 2) ≤ η₁) :
    P {ω | crossSeq εc (X ω) q < 1} ≤ 16 * η₁ := by
  have h_arith : (ENNReal.ofReal ((q : ℝ) * δ)) * (P {ω | crossSeq εc (X ω) q < 1} - 8 * η₁) ≤ P {ω | crossSeq εc (X ω) q < 1} := by
    have h_arith : ∀ k < q, ∫⁻ ω in {ω | crossSeq εc (X ω) q < 1}, ENNReal.ofReal (crossSeq εc (X ω) (k + 1) - crossSeq εc (X ω) k) ∂P ≥ ENNReal.ofReal δ * (P {ω | crossSeq εc (X ω) q < 1} - 8 * η₁) := by
      intro k hk
      have h_bad_gap : P ({ω | crossSeq εc (X ω) q < 1} ∩ {ω | crossSeq εc (X ω) (k + 1) - crossSeq εc (X ω) k < δ}) ≤ 8 * η₁ := by
        refine' le_trans _ ( mul_le_mul_left' hQδ _ );
        refine' le_trans ( MeasureTheory.measure_mono _ ) ( prob_badpair_le P X hX 𝓕 hrc hadapt hεc hδ k );
        intro ω hω;
        exact ⟨ lt_of_le_of_lt ( crossSeq_mono _ ( by linarith ) ) hω.1, lt_of_le_of_lt ( crossSeq_mono _ ( by linarith ) ) hω.1, hω.2 ⟩;
      have h_integral_bound : ∫⁻ ω in {ω | crossSeq εc (X ω) q < 1}, ENNReal.ofReal (crossSeq εc (X ω) (k + 1) - crossSeq εc (X ω) k) ∂P ≥ ∫⁻ ω in {ω | crossSeq εc (X ω) q < 1} ∩ {ω | crossSeq εc (X ω) (k + 1) - crossSeq εc (X ω) k ≥ δ}, ENNReal.ofReal δ ∂P := by
        refine' le_trans ( MeasureTheory.setLIntegral_mono' _ _ ) ( MeasureTheory.lintegral_mono_set _ );
        · exact MeasurableSet.inter ( measurableSet_lt ( measurable_crossSeq hX εc q ) measurable_const ) ( measurableSet_le measurable_const ( Measurable.sub ( measurable_crossSeq hX εc ( k + 1 ) ) ( measurable_crossSeq hX εc k ) ) );
        · exact fun ω hω => ENNReal.ofReal_le_ofReal hω.2.out;
        · exact Set.inter_subset_left;
      refine' le_trans _ h_integral_bound;
      simp +decide [ Set.inter_def ];
      rw [ show { ω : Ω | crossSeq εc ( X ω ) q < 1 ∧ δ ≤ crossSeq εc ( X ω ) ( k + 1 ) - crossSeq εc ( X ω ) k } = ( { ω : Ω | crossSeq εc ( X ω ) q < 1 } \ { ω : Ω | crossSeq εc ( X ω ) q < 1 ∧ crossSeq εc ( X ω ) ( k + 1 ) - crossSeq εc ( X ω ) k < δ } ) from ?_ ];
      · rw [ MeasureTheory.measure_diff ];
        · gcongr;
          exact h_bad_gap;
        · exact fun x hx => hx.1;
        · refine' MeasurableSet.nullMeasurableSet _;
          exact MeasurableSet.inter ( measurableSet_lt ( measurable_crossSeq hX εc q ) measurable_const ) ( measurableSet_lt ( measurable_crossSeq hX εc ( k + 1 ) |> Measurable.sub <| measurable_crossSeq hX εc k ) measurable_const );
        · exact MeasureTheory.measure_ne_top _ _;
      · ext ω; simp [Set.mem_setOf_eq];
        exact fun h => Or.inl h;
    have h_arith : ∑ k ∈ Finset.range q, ∫⁻ ω in {ω | crossSeq εc (X ω) q < 1}, ENNReal.ofReal (crossSeq εc (X ω) (k + 1) - crossSeq εc (X ω) k) ∂P ≤ P {ω | crossSeq εc (X ω) q < 1} := by
      rw [ ← MeasureTheory.lintegral_finset_sum ];
      · have h_arith : ∀ ω ∈ {ω | crossSeq εc (X ω) q < 1}, ∑ k ∈ Finset.range q, ENNReal.ofReal (crossSeq εc (X ω) (k + 1) - crossSeq εc (X ω) k) ≤ 1 := by
          intro ω hω
          have h_sum : ∑ k ∈ Finset.range q, (crossSeq εc (X ω) (k + 1) - crossSeq εc (X ω) k) = crossSeq εc (X ω) q - crossSeq εc (X ω) 0 := by
            rw [ Finset.sum_range_sub ( fun k => crossSeq εc ( X ω ) k ) ];
          rw [ ← ENNReal.ofReal_sum_of_nonneg ];
          · rw [ h_sum, ENNReal.ofReal_le_iff_le_toReal ] <;> norm_num;
            exact le_add_of_le_of_nonneg hω.out.le ( by exact le_rfl );
          · exact fun i hi => sub_nonneg_of_le <| crossSeq_mono _ <| Nat.le_succ _;
        refine' le_trans ( MeasureTheory.setLIntegral_mono' _ _ ) _;
        use fun ω => 1;
        · exact measurableSet_lt ( measurable_crossSeq hX εc q ) measurable_const;
        · exact h_arith;
        · simp +decide [ MeasureTheory.lintegral_const ];
      · exact fun k hk => Measurable.ennreal_ofReal ( Measurable.sub ( measurable_crossSeq hX εc ( k + 1 ) ) ( measurable_crossSeq hX εc k ) );
    refine' le_trans _ h_arith;
    refine' le_trans _ ( Finset.sum_le_sum fun k hk => ‹∀ k < q, ∫⁻ ω in {ω | crossSeq εc (X ω) q < 1}, ENNReal.ofReal (crossSeq εc (X ω) (k + 1) - crossSeq εc (X ω) k) ∂P ≥ ENNReal.ofReal δ * (P {ω | crossSeq εc (X ω) q < 1} - 8 * η₁)› k ( Finset.mem_range.mp hk ) );
    simp +decide [ mul_assoc, ENNReal.ofReal_mul ( Nat.cast_nonneg _ ) ];
  convert enn_count_arith _ _ _ h_arith using 1;
  · ring;
  · exact MeasureTheory.measure_ne_top _ _;
  · rw [ ENNReal.lt_ofReal_iff_toReal_lt ] <;> norm_num ; linarith;
  · exact ENNReal.ofReal_ne_top

/-! ## Corrected witness: interior crossings + the boundary shift-average set

The `badSet` witness (interior + terminal crossing-gaps together) is provably too coarse at
the boundary: a *gradual* rise that first exceeds the `εc` level within `σ` of time `1` lies
in `badSet` yet has small càdlàg modulus and `aldousQ = 0` (the increment is spread over a
window wider than `2σ`, so no stopping-time increment detects it).  Hence `P(badSet)` is NOT
controlled by `aldousQ`, and the single lemma `P(badSet) ≤ 16η₁ + 8η₂` is FALSE (this is the
boundary analogue of Task 8's counterexample).  We therefore use the genuine Aldous witness:
interior crossings (two `εc`-crossings, both `< 1`, within `σ`) UNION the boundary
shift-average set `termSet` (an `A_δ`-event at the deterministic time `1-σ`), which detects
exactly the genuine boundary *jumps* (size `≥ εc`) while ignoring benign gradual boundary
rises.  Both pieces are controlled by `aldousQ` (`prob_badpair_le` / `prob_fiber_ge_le`), and
their union covers `{f | ε ≤ w'(f,σ)}` via the boundary modulus lemma. -/

/-- The boundary set: paths having an `εc`-oscillation from the deterministic time `1-σ`
before time `1`, i.e. the first `εc`-crossing after `1-σ` occurs strictly before `1`.  This
detects EVERY genuine boundary jump (including a jump immediately cancelled at `1`, which the
fiber-measure detector misses): the first-passage crossing time `ρ ∈ (1-σ, 1)` gives
`|f ρ - f(1-σ)| ≥ εc`, and the window-overlap pigeonhole at the pair `(1-σ, ρ)` places the
path in one of two shift-average events (at `1-σ` or at the stopping time `ρ`), each
controlled by `α(2σ, εc/2)`.  The cancellation is caught by the `ρ`-fiber (the return builds
a plateau after `ρ`). -/
def boundarySet (εc σ : ℝ) : Set Skoro :=
  {f | crossTime skoroEval (1 - 2 * σ) εc f < (1 : WithTop ℝ)}

/-
**First-passage crossing value.**  If the first `εc`-crossing after a start `s` occurs at
a finite time `< 1`, then the increment there is a genuine `εc`-crossing.  (Right-continuity
at the infimum of the strict `> εc` set.)
-/
theorem crossTime_value_ge (X : ℝ → Ω → ℝ) (s εc : ℝ) (ω : Ω)
    (hrc : ∀ t, ContinuousWithinAt (fun r => X r ω) (Set.Ici t) t)
    {ρ : ℝ} (hρ : crossTime X s εc ω = (ρ : WithTop ℝ)) (hsρ : s < ρ) :
    εc ≤ |X ρ ω - X s ω| := by
  -- By definition of crossTime, there exists a sequence tₙ such that tₙ → ρ and εc < |X tₙ ω - X s ω|.
  obtain ⟨tₙ, htₙ⟩ : ∃ tₙ : ℕ → ℝ, (∀ n, s < tₙ n ∧ εc < |X (tₙ n) ω - X s ω|) ∧ Filter.Tendsto tₙ Filter.atTop (nhds ρ) := by
    have h_seq : ∀ ε > 0, ∃ t, s < t ∧ εc < |X t ω - X s ω| ∧ |t - ρ| < ε := by
      intro ε εpos
      have h_seq : ∃ t, s < t ∧ εc < |X t ω - X s ω| ∧ t < ρ + ε := by
        unfold crossTime at hρ;
        split_ifs at hρ <;> norm_cast at hρ;
        exact Exists.elim ( exists_lt_of_csInf_lt ( by assumption ) ( show sInf { t | s < t ∧ εc < |X t ω - X s ω| } < ρ + ε by linarith ) ) fun t ht => ⟨ t, ht.1.1, ht.1.2, ht.2 ⟩;
      obtain ⟨ t, ht₁, ht₂, ht₃ ⟩ := h_seq;
      have h_seq : ρ ≤ t := by
        unfold crossTime at hρ;
        split_ifs at hρ <;> norm_cast at hρ;
        exact hρ ▸ csInf_le ⟨ s, fun x hx => hx.1.le ⟩ ⟨ ht₁, ht₂ ⟩;
      exact ⟨ t, ht₁, ht₂, abs_lt.mpr ⟨ by linarith, by linarith ⟩ ⟩;
    exact ⟨ fun n => Classical.choose ( h_seq ( 1 / ( n + 1 ) ) ( by positivity ) ), fun n => ⟨ Classical.choose_spec ( h_seq ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.1, Classical.choose_spec ( h_seq ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.2.1 ⟩, tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => Classical.choose_spec ( h_seq ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.2.2.le ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩;
  -- By right-continuity of `r ↦ X r ω` on `Set.Ici ρ` at ρ (`hrc ρ`), the map `r ↦ |X r ω - X s ω|` is right-continuous at ρ.
  have h_right_cont : Filter.Tendsto (fun r => |X r ω - X s ω|) (nhdsWithin ρ (Set.Ici ρ)) (nhds (|X ρ ω - X s ω|)) := by
    exact Filter.Tendsto.abs ( Filter.Tendsto.sub ( hrc ρ ) tendsto_const_nhds );
  -- Since $tₙ \to ρ$ and $tₙ \geq ρ$ for all $n$, we have $tₙ \in Set.Ici ρ$ for all $n$.
  have htₙ_ge_ρ : ∀ᶠ n in Filter.atTop, ρ ≤ tₙ n := by
    unfold crossTime at hρ;
    split_ifs at hρ <;> norm_cast at hρ;
    exact Filter.Eventually.of_forall fun n => hρ ▸ csInf_le ⟨ s, fun t ht => ht.1.le ⟩ ( htₙ.1 n );
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ( h_right_cont.comp <| Filter.tendsto_inf.mpr ⟨ htₙ.2, Filter.tendsto_principal.mpr htₙ_ge_ρ ⟩ ) <| Filter.eventually_atTop.mpr ⟨ 0, fun n hn => le_of_lt <| htₙ.1 n |>.2 ⟩

/-- The interior bad set: two consecutive `εc`-crossings, both strictly before `1`, within
`σ`.  Unlike `badSet` this excludes the terminal clamp pair, so its mass IS controlled by the
Aldous quantity via `prob_badpair_le`. -/
def interiorBadSet (εc σ : ℝ) : Set Skoro :=
  {f | ∃ k : ℕ, crossSeq εc f k < 1 ∧ crossSeq εc f (k + 1) < 1 ∧
      crossSeq εc f (k + 1) - crossSeq εc f k ≤ σ}

theorem measurableSet_boundarySet (εc σ : ℝ) : MeasurableSet (boundarySet εc σ) := by
  unfold boundarySet;
  have h_crossTime_measurable : ∀ x : ℝ, MeasurableSet {f : Skoro | crossTime skoroEval (1 - 2 * σ) εc f ≤ (x : WithTop ℝ)} := by
    intro x;
    have h_countable : {f : Skoro | crossTime skoroEval (1 - 2 * σ) εc f ≤ (x : WithTop ℝ)} = ⋂ (u : ℚ) (hu : x < u), ⋃ (q : ℚ) (hq : 1 - 2 * σ < q ∧ q < u), {f : Skoro | εc < |f.toFun q - f.toFun (1 - 2 * σ)|} := by
      ext f;
      simp +decide [ crossTime_le_iff skoroEval ( 1 - 2 * σ ) εc f ( fun t => Skoro.rightContinuous f t ) x ];
      simp +decide only [skoroEval, and_assoc];
    convert h_countable.symm ▸ MeasurableSet.iInter fun u => MeasurableSet.iInter fun hu => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_ using 1;
    have h_measurable : Measurable (fun f : Skoro => |f.toFun q - f.toFun (1 - 2 * σ)|) := by
      have h_measurable : Measurable (fun f : Skoro => f.toFun q) ∧ Measurable (fun f : Skoro => f.toFun (1 - 2 * σ)) := by
        constructor;
        · convert SkorokhodBasic.measurable_eval_prod ( measurable_id ) using 1;
          constructor <;> intro h;
          · convert SkorokhodBasic.measurable_eval_prod ( measurable_id ) using 1;
          · convert h.comp ( measurable_const.prodMk measurable_id ) using 1;
        · convert SkorokhodBasic.measurable_eval_prod ( measurable_id ) using 1;
          constructor <;> intro h;
          · convert SkorokhodBasic.measurable_eval_prod ( measurable_id ) using 1;
          · convert h.comp ( measurable_const.prodMk measurable_id ) using 1;
      exact Measurable.norm ( h_measurable.1.sub h_measurable.2 );
    exact measurableSet_lt measurable_const h_measurable;
  convert MeasurableSet.iUnion ( fun q : ℚ => MeasurableSet.iUnion ( fun hq : ( q : ℝ ) < 1 => h_crossTime_measurable q ) ) using 1 ; ext ; simp +decide [ WithTop.coe_lt_coe ] ;
  cases h : crossTime skoroEval ( 1 - 2 * σ ) εc ‹_› <;> simp_all +decide [ WithTop.coe_lt_coe ];
  exact ⟨ fun h => by rcases exists_rat_btwn h with ⟨ q, hq₁, hq₂ ⟩ ; exact ⟨ q, mod_cast hq₂, mod_cast hq₁.le ⟩, fun ⟨ q, hq₁, hq₂ ⟩ => lt_of_le_of_lt hq₂ ( mod_cast hq₁ ) ⟩

/-
The clamped first-`εc`-crossing-after-`a` map is Borel measurable on `Skoro`.
-/
theorem measurable_crossTimeStop (a εc : ℝ) :
    Measurable (fun f : Skoro => min ((crossTime skoroEval a εc f).untopD 1) 1) := by
  -- Let's prove the measurability of the crossTime function.
  have h_crossTime_measurable : ∀ x : ℝ, MeasurableSet {f : Skoro | crossTime skoroEval a εc f ≤ (x : WithTop ℝ)} := by
    intro x
    have h_crossTime_le_iff : {f : Skoro | crossTime skoroEval a εc f ≤ (x : WithTop ℝ)} = ⋂ (u : ℚ) (hu : x < u), ⋃ (q : ℚ) (hq : a < q ∧ q < u), {f : Skoro | εc < |f.toFun q - f.toFun a|} := by
      ext f;
      simp +decide [ crossTime_le_iff skoroEval a εc f ( fun t => Skoro.rightContinuous f t ) x ];
      simp +decide only [skoroEval, and_assoc];
    refine' h_crossTime_le_iff ▸ MeasurableSet.iInter fun u => MeasurableSet.iInter fun hu => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => _;
    have h_measurable : Measurable (fun f : Skoro => f.toFun q) ∧ Measurable (fun f : Skoro => f.toFun a) := by
      have h_measurable : ∀ t : ℝ, Measurable (fun f : Skoro => f.toFun t) := by
        intro t; exact (by
        convert SkorokhodBasic.measurable_eval_prod ( measurable_id ) |> Measurable.comp <| measurable_id using 1;
        exact iff_of_true ( measurable_eval_prod ( measurable_id ) |> Measurable.comp <| measurable_const.prodMk measurable_id ) ( measurable_eval_prod ( measurable_id ) ));
      exact ⟨ h_measurable _, h_measurable _ ⟩;
    exact measurableSet_lt measurable_const ( Measurable.norm ( h_measurable.1.sub h_measurable.2 ) );
  refine' measurable_of_Iic _;
  intro x; by_cases hx : 1 ≤ x <;> simp_all +decide [ Set.preimage ] ;
  convert h_crossTime_measurable x using 1;
  ext f; cases h : crossTime skoroEval a εc f <;> simp_all +decide [ WithTop.untopD ] ;

theorem measurableSet_interiorBadSet (εc σ : ℝ) : MeasurableSet (interiorBadSet εc σ) := by
  -- Each set {f | crossSeq εc f k < 1 ∧ crossSeq εc f (k + 1) < 1 ∧ crossSeq εc f (k + 1) - crossSeq εc f k ≤ σ} is measurable.
  have h_measurable : ∀ k, MeasurableSet {f : Skoro | crossSeq εc f k < 1 ∧ crossSeq εc f (k + 1) < 1 ∧ crossSeq εc f (k + 1) - crossSeq εc f k ≤ σ} := by
    intro k
    have h_measurable : Measurable (fun f : Skoro => crossSeq εc f k) ∧ Measurable (fun f : Skoro => crossSeq εc f (k + 1)) := by
      exact ⟨ SkorokhodBasic.measurable_crossSeq ( measurable_id ) εc k, SkorokhodBasic.measurable_crossSeq ( measurable_id ) εc ( k + 1 ) ⟩
    exact MeasurableSet.inter (measurableSet_lt h_measurable.left measurable_const)
      (MeasurableSet.inter (measurableSet_lt h_measurable.right measurable_const)
      (measurableSet_le (h_measurable.right.sub h_measurable.left) measurable_const));
  convert MeasurableSet.iUnion fun k => h_measurable k using 1
  ext f
  simp [interiorBadSet, h_measurable]

/-
**Interior pigeonhole bound.**  For each fixed index `k`, two consecutive crossings both
`< 1` and within `σ` have mass `≤ 8·α(2σ, εc/2)` (the genuine-crossing pigeonhole of Steps
2–3; identical to `prob_badpair_le` but with a non-strict gap `≤ σ`).
-/
theorem prob_interior_pair_le (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Skoro)
    (hX : Measurable X) (𝓕 : Filtration ℝ m) (hrc : 𝓕.rightCont = 𝓕)
    (hadapt : ∀ r, Measurable[𝓕 r] (fun ω => (X ω).toFun r))
    {εc σ : ℝ} (hεc : 0 < εc) (hσ : 0 < σ) (k : ℕ) :
    P {ω | crossSeq εc (X ω) k < 1 ∧ crossSeq εc (X ω) (k + 1) < 1 ∧
        crossSeq εc (X ω) (k + 1) - crossSeq εc (X ω) k ≤ σ}
      ≤ 8 * aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * σ) (εc / 2) := by
  -- Apply the `window_overlap_pigeonhole` lemma to the pair of crossings.
  have h_window_overlap : ∀ ω, crossSeq εc (X ω) k < 1 ∧ crossSeq εc (X ω) (k + 1) < 1 ∧ crossSeq εc (X ω) (k + 1) - crossSeq εc (X ω) k ≤ σ →
    ENNReal.ofReal (σ / 2) ≤ volume {s : ℝ | s ∈ Set.Ioc (0 : ℝ) (2 * σ) ∧ εc / 2 ≤ |(X ω).toFun (crossSeq εc (X ω) k + s) - (X ω).toFun (crossSeq εc (X ω) k)|} ∨
    ENNReal.ofReal (σ / 2) ≤ volume {s : ℝ | s ∈ Set.Ioc (0 : ℝ) (2 * σ) ∧ εc / 2 ≤ |(X ω).toFun (crossSeq εc (X ω) (k + 1) + s) - (X ω).toFun (crossSeq εc (X ω) (k + 1))|} := by
      intros ω hω
      apply window_overlap_pigeonhole hσ (crossSeq_mono (X ω) (Nat.le_succ k)) (by linarith) (by
      apply crossSeq_crossing_ge; exact hω.left; exact hω.right.left);
  refine' le_trans _ ( _ : _ ≤ _ );
  exact P { ω | ENNReal.ofReal ( σ / 2 ) ≤ volume { s : ℝ | s ∈ Set.Ioc 0 ( 2 * σ ) ∧ εc / 2 ≤ |( X ω ).toFun ( crossSeq εc ( X ω ) k + s ) - ( X ω ).toFun ( crossSeq εc ( X ω ) k )| } } + P { ω | ENNReal.ofReal ( σ / 2 ) ≤ volume { s : ℝ | s ∈ Set.Ioc 0 ( 2 * σ ) ∧ εc / 2 ≤ |( X ω ).toFun ( crossSeq εc ( X ω ) ( k + 1 ) + s ) - ( X ω ).toFun ( crossSeq εc ( X ω ) ( k + 1 ) )| } };
  · exact MeasureTheory.measure_mono ( fun ω hω => h_window_overlap ω hω ) |> le_trans <| MeasureTheory.measure_union_le _ _;
  · convert add_le_add ( prob_fiber_ge_le P X hX 𝓕 ( isStoppingTime_crossSeq 𝓕 hrc hX hadapt εc k ) ( measurable_crossSeq hX εc k ) ( fun ω => crossSeq_le_one ( X ω ) k ) hσ ) ( prob_fiber_ge_le P X hX 𝓕 ( isStoppingTime_crossSeq 𝓕 hrc hX hadapt εc ( k + 1 ) ) ( measurable_crossSeq hX εc ( k + 1 ) ) ( fun ω => crossSeq_le_one ( X ω ) ( k + 1 ) ) hσ ) using 1 ; ring

/-
**Interior assembly (two scales).**  The interior bad set's pushforward mass is
`≤ 16·η₁ + 8·η₂`: `{T_q < 1}` costs `16·η₁` (crossing count), and the `< q` interior gap
events cost `q·8·(η₂/q) = 8·η₂` (union paid by the `η₂/q` tolerance — the two-scale device).
-/
theorem prob_map_interiorBadSet_le (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Skoro)
    (hX : Measurable X) (𝓕 : Filtration ℝ m) (hrc : 𝓕.rightCont = 𝓕)
    (hadapt : ∀ r, Measurable[𝓕 r] (fun ω => (X ω).toFun r))
    {εc δ σ : ℝ} (hεc : 0 < εc) (hδ : 0 < δ) (hσ : 0 < σ) (hσδ : σ ≤ δ)
    (q : ℕ) (hq : 2 < (q : ℝ) * δ)
    {η₁ η₂ : ℝ≥0∞}
    (hQδ : aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * δ) (εc / 2) ≤ η₁)
    (hQσ : aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * σ) (εc / 2) ≤ η₂ / (q : ℝ≥0∞)) :
    (P.map X) (interiorBadSet εc σ) ≤ 16 * η₁ + 8 * η₂ := by
  rw [ Measure.map_apply ];
  · refine' le_trans ( measure_mono _ ) ( le_trans ( MeasureTheory.measure_union_le _ _ ) _ );
    rotate_left;
    exact { ω | crossSeq εc ( X ω ) q < 1 };
    exact ⋃ k ∈ Finset.range q, { ω | crossSeq εc ( X ω ) k < 1 ∧ crossSeq εc ( X ω ) ( k + 1 ) < 1 ∧ crossSeq εc ( X ω ) ( k + 1 ) - crossSeq εc ( X ω ) k ≤ σ };
    · refine' add_le_add _ _;
      · convert prob_crossSeq_lt_one_le P X hX 𝓕 hrc hadapt hεc hδ q hq hQδ using 1;
      · refine' le_trans ( MeasureTheory.measure_biUnion_finset_le _ _ ) _;
        refine' le_trans ( Finset.sum_le_sum fun i hi => prob_interior_pair_le P X hX 𝓕 hrc hadapt hεc hσ i ) _;
        simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
        gcongr;
        convert mul_le_mul_left' hQσ ( q : ℝ≥0∞ ) using 1;
        rw [ ENNReal.mul_div_cancel' ] <;> norm_num;
        rintro rfl; norm_num at hq;
    · intro ω hω
      obtain ⟨k, hk⟩ := hω
      by_cases hkq : k < q;
      · exact Or.inr ( Set.mem_iUnion₂.mpr ⟨ k, Finset.mem_range.mpr hkq, hk ⟩ );
      · exact Or.inl ( lt_of_le_of_lt ( crossSeq_mono _ ( le_of_not_gt hkq ) ) hk.1 );
  · exact hX;
  · exact measurableSet_interiorBadSet εc σ

/-
**Boundary set bound (Step 2 ∘ Step 3 at the boundary).**  The boundary set has
pushforward mass `≤ 8·α(2σ, εc/2)`.  On `boundarySet` the first-passage crossing time
`ρ ∈ (1-σ, 1)` from the deterministic `1-σ` satisfies `|X ρ - X (1-σ)| ≥ εc` and
`ρ - (1-σ) < σ`; the window-overlap pigeonhole at the pair `(1-σ, ρ)` places the path in
`A_σ(1-σ) ∪ A_σ(ρ)`, each bounded by `4·α(2σ, εc/2)` via `prob_fiber_ge_le` (`1-σ` a constant
stopping time; `ρ` a crossing stopping time).
-/
theorem prob_map_boundarySet_le (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Skoro)
    (hX : Measurable X) (𝓕 : Filtration ℝ m) (hrc : 𝓕.rightCont = 𝓕)
    (hadapt : ∀ r, Measurable[𝓕 r] (fun ω => (X ω).toFun r))
    {εc σ : ℝ} (hεc : 0 < εc) (hσ : 0 < σ) (hσ1 : σ < 1) :
    (P.map X) (boundarySet εc σ)
      ≤ 8 * aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * (2 * σ)) (εc / 2) := by
  have h_bound : (P {ω | crossTime skoroEval (1 - 2 * σ) εc (X ω) < 1}) ≤ 8 * aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * (2 * σ)) (εc / 2) := by
    have h_bound : (P {ω | crossTime skoroEval (1 - 2 * σ) εc (X ω) < 1}) ≤ (P {ω | ENNReal.ofReal (σ) ≤ volume {s : ℝ | s ∈ Set.Ioc 0 (4 * σ) ∧ εc / 2 ≤ |(X ω).toFun (1 - 2 * σ + s) - (X ω).toFun (1 - 2 * σ)|}}) + (P {ω | ENNReal.ofReal (σ) ≤ volume {s : ℝ | s ∈ Set.Ioc 0 (4 * σ) ∧ εc / 2 ≤ |(X ω).toFun (min ((crossTime skoroEval (1 - 2 * σ) εc (X ω)).untopD 1) 1 + s) - (X ω).toFun (min ((crossTime skoroEval (1 - 2 * σ) εc (X ω)).untopD 1) 1)|}}) := by
      refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
      intro ω hω
      have h_cross : εc ≤ |(X ω).toFun (min ((crossTime skoroEval (1 - 2 * σ) εc (X ω)).untopD 1) 1) - (X ω).toFun (1 - 2 * σ)| := by
        convert crossTime_value_ge skoroEval ( 1 - 2 * σ ) εc ( X ω ) _ _ _ using 1;
        · exact fun t => Skoro.rightContinuous ( X ω ) t;
        · cases h : crossTime skoroEval ( 1 - 2 * σ ) εc ( X ω ) <;> simp_all +decide;
          linarith;
        · unfold crossTime at *;
          split_ifs at * <;> simp_all +decide [ WithTop.untopD ];
          have h_right_cont : Filter.Tendsto (fun t => |skoroEval t (X ω) - skoroEval (1 - 2 * σ) (X ω)|) (nhdsWithin (1 - 2 * σ) (Set.Ici (1 - 2 * σ))) (nhds 0) := by
            have h_right_cont : ContinuousWithinAt (fun t => skoroEval t (X ω)) (Set.Ici (1 - 2 * σ)) (1 - 2 * σ) := by
              exact Skoro.rightContinuous ( X ω ) _;
            simpa using Filter.Tendsto.abs ( h_right_cont.sub_const ( skoroEval ( 1 - 2 * σ ) ( X ω ) ) );
          have := h_right_cont.eventually ( gt_mem_nhds hεc );
          rw [ eventually_nhdsWithin_iff ] at this;
          rw [ Metric.eventually_nhds_iff ] at this;
          obtain ⟨ ε, ε_pos, H ⟩ := this;
          exact lt_of_lt_of_le ( show 1 - 2 * σ < 1 - 2 * σ + ε by linarith ) ( le_csInf ‹_› fun t ht => le_of_not_gt fun h => by have := H ( show |t - ( 1 - 2 * σ )| < ε by exact abs_lt.mpr ⟨ by linarith [ ht.1 ], by linarith [ ht.1 ] ⟩ ) ( show 1 - 2 * σ ≤ t by linarith [ ht.1 ] ) ; linarith [ ht.2 ] );
      have h_window : 1 - 2 * σ < min ((crossTime skoroEval (1 - 2 * σ) εc (X ω)).untopD 1) 1 := by
        have h_right_cont : Filter.Tendsto (fun t => |(X ω).toFun t - (X ω).toFun (1 - 2 * σ)|) (nhdsWithin (1 - 2 * σ) (Set.Ici (1 - 2 * σ))) (nhds 0) := by
          have h_right_cont : ContinuousWithinAt (fun t => (X ω).toFun t) (Set.Ici (1 - 2 * σ)) (1 - 2 * σ) := by
            exact Skoro.rightContinuous ( X ω ) _;
          simpa using Filter.Tendsto.abs ( h_right_cont.sub_const ( ( X ω ).toFun ( 1 - 2 * σ ) ) );
        have := h_right_cont.eventually ( gt_mem_nhds hεc ) ; have := this.and ( self_mem_nhdsWithin ) ; obtain ⟨ t, ht₁, ht₂ ⟩ := this.exists; simp_all +decide [ crossTime ] ;
        split_ifs at * <;> simp_all +decide [ skoroEval ];
        contrapose! h_cross;
        rw [ min_eq_left ( by linarith ) ];
        rw [ le_antisymm h_cross ( le_csInf ‹_› fun x hx => hx.1.le ) ] ; simpa using hεc;
      have := window_overlap_pigeonhole ( show 0 < 2 * σ by linarith ) ( show 1 - 2 * σ ≤ min ( WithTop.untopD 1 ( crossTime skoroEval ( 1 - 2 * σ ) εc ( X ω ) ) ) 1 by linarith ) ( show min ( WithTop.untopD 1 ( crossTime skoroEval ( 1 - 2 * σ ) εc ( X ω ) ) ) 1 - ( 1 - 2 * σ ) ≤ 2 * σ by linarith [ min_le_right ( WithTop.untopD 1 ( crossTime skoroEval ( 1 - 2 * σ ) εc ( X ω ) ) ) 1 ] ) h_cross;
      convert this using 1 ; ring;
      simp +decide [ Set.mem_union, Set.mem_setOf_eq ];
    -- Apply the prob_fiber_ge_le theorem to each term in the sum.
    have h_fiber : ∀ (τ : Ω → ℝ), IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ)) → (∀ ω, τ ω ≤ 1) → Measurable τ → P {ω | ENNReal.ofReal (σ) ≤ volume {s : ℝ | s ∈ Set.Ioc 0 (4 * σ) ∧ εc / 2 ≤ |(X ω).toFun (τ ω + s) - (X ω).toFun (τ ω)|}} ≤ 4 * aldousQ P (fun t ω => (X ω).toFun t) 𝓕 (2 * (2 * σ)) (εc / 2) := by
      intros τ hτ hτ1 hτmeas;
      convert prob_fiber_ge_le P X hX 𝓕 hτ hτmeas hτ1 ( show 0 < 2 * σ by positivity ) using 1;
      ring;
    convert h_bound.trans ( add_le_add ( h_fiber ( fun _ => 1 - 2 * σ ) _ _ _ ) ( h_fiber ( fun ω => min ( WithTop.untopD 1 ( crossTime skoroEval ( 1 - 2 * σ ) εc ( X ω ) ) ) 1 ) _ _ _ ) ) using 1 <;> norm_num [ hσ.le ] ; ring;
    · exact isStoppingTime_const _ _;
    · convert isStoppingTime_min_untopD_one 𝓕 _ using 1;
      convert isStoppingTime_crossTime_of_stoppingTime 𝓕 _ _ ( isStoppingTime_const 𝓕 ( 1 - 2 * σ ) ) εc using 1;
      · exact hrc.symm;
      · exact fun r => hadapt r;
      · exact fun ω t => Skoro.rightContinuous ( X ω ) t;
    · convert measurable_crossTimeStop ( 1 - 2 * σ ) εc |> Measurable.comp <| hX using 1;
  rw [ Measure.map_apply hX ( measurableSet_boundarySet εc σ ) ] ; aesop;

/-
**Boundary modulus lemma.**  If a path has no two interior `εc`-crossings within `σ`
(`∉ interiorBadSet`) and no `εc`-oscillation from `1-σ` before `1` (`∉ boundarySet`), then its
càdlàg modulus is `≤ 4·εc`.  Interior cells have oscillation `≤ εc` (`crossTime_osc_le`);
`∉ boundarySet` gives `|f t - f(1-σ)| ≤ εc` for `t ∈ (1-σ, 1)`, so the terminal cell
`[τ_{N-1}, 1)` has oscillation `≤ 2εc`.  Feed the crossing partition (dropping the last
crossing when it is within `σ` of `1`) to `cadlagModulus_le_of_crossing`.
-/
theorem cadlagModulus_le_of_not_interiorBad_boundarySet {εc σ : ℝ} (hεc : 0 < εc) (hσ : 0 < σ)
    (hσ1 : σ < 1) {f : Skoro} (hf1 : f ∉ interiorBadSet εc σ) (hf2 : f ∉ boundarySet εc σ) :
    cadlagModulus f.toFun σ ≤ 4 * εc := by
  by_cases h : f ∈ badSet εc σ <;> simp_all +decide [ badSet ];
  · -- Since `f ∉ interiorBadSet` implies the gap condition fails, this forces `crossSeq εc f (k+1) = 1` and `k ≥ 1`.
    obtain ⟨k, hk1, hk2⟩ := h
    have hk3 : crossSeq εc f (k + 1) = 1 := by
      contrapose! hf1; simp_all +decide [ interiorBadSet ] ;
      exact ⟨ k, hk1, lt_of_le_of_ne ( crossSeq_le_one f _ ) hf1, hk2 ⟩
    have hk4 : 1 ≤ k := by
      contrapose! hf1; interval_cases k ; simp_all +decide ;
      linarith! [ show crossSeq εc f 0 = 0 from rfl ]
    generalize_proofs at *;
    -- Set `s := crossSeq εc f` and apply `cadlagModulus_le_of_crossing` for `M := k - 1` and `δ := σ`.
    set s : ℕ → ℝ := crossSeq εc f
    have hs0 : s 0 = 0 := by
      rfl
    have hlast : s (k - 1) < 1 := by
      exact lt_of_le_of_lt ( crossSeq_mono f ( Nat.pred_le _ ) ) hk1
    have hmono : ∀ i < k - 1, s i < s (i + 1) := by
      contrapose! hf1; simp_all +decide [ interiorBadSet ] ;
      obtain ⟨ i, hi, hi' ⟩ := hf1
      use i
      generalize_proofs at *;
      exact ⟨ by
        exact lt_of_le_of_lt ( crossSeq_mono f ( by omega ) ) hlast, by
        exact lt_of_le_of_lt ( crossSeq_mono f ( by omega ) ) hlast, by
        grind +revert ⟩
    have hsep : ∀ i < k - 1, σ < s (i + 1) - s i := by
      intro i hi; contrapose! hf1; use i; simp_all +decide [ interiorBadSet ] ;
      exact ⟨ lt_of_le_of_lt ( crossSeq_mono f ( by omega ) ) hlast, lt_of_le_of_lt ( crossSeq_mono f ( by omega ) ) hlast, hf1 ⟩
    have htail : σ < 1 - s (k - 1) := by
      contrapose! hf1; use k - 1; rcases k with ( _ | k ) <;> simp_all +decide [ crossSeq ] ;
      have := crossSeq_succ_eq_crossTime f k hk1; aesop;
    have hosc : ∀ i < k - 1, ∀ x ∈ Set.Ico (s i) (s (i + 1)), |f.toFun x - f.toFun (s i)| ≤ εc := by
      intros i hi x hx
      have hosc_i : crossSeq εc f (i + 1) < 1 := by
        exact lt_of_le_of_lt ( crossSeq_mono f ( by omega ) ) hk1
      generalize_proofs at *; (
      exact crossSeq_osc_le f i hosc_i hx)
    have hosctail : ∀ x ∈ Set.Ico (s (k - 1)) 1, |f.toFun x - f.toFun (s (k - 1))| ≤ 2 * εc := by
      intro x hx
      by_cases hx' : x < s k
      generalize_proofs at *;
      generalize_proofs at *;
      generalize_proofs at *;
      · have := crossSeq_osc_le f ( k - 1 ) ( by
          rwa [ Nat.sub_add_cancel hk4 ] ) ( show x ∈ Set.Ico ( s ( k - 1 ) ) ( s ( k - 1 + 1 ) ) from by
                                                            exact ⟨ hx.1, by rw [ Nat.sub_add_cancel hk4 ] ; linarith ⟩ )
        generalize_proofs at *;
        exact le_trans this ( by linarith ) ;
      · have h_tail : |f.toFun x - f.toFun (1 - 2 * σ)| ≤ εc ∧ |f.toFun (1 - 2 * σ) - f.toFun (s (k - 1))| ≤ εc := by
          apply And.intro;
          · apply crossTime_osc_le skoroEval (1 - 2 * σ) εc f (by
            grind +qlia) (by
            exact lt_of_not_ge fun h => hf2 <| by exact Set.mem_setOf.mpr <| lt_of_le_of_lt h <| by aesop;);
          · by_cases h_case : s (k - 1) < 1 - 2 * σ
            generalize_proofs at *;
            generalize_proofs at *;
            generalize_proofs at *;
            generalize_proofs at *;
            · apply crossSeq_osc_le f (k - 1) (by
              rwa [ Nat.sub_add_cancel hk4 ]) (by
              grind);
            · have h_tail : |f.toFun (s (k - 1)) - f.toFun (1 - 2 * σ)| ≤ εc := by
                have h_cross : crossTime skoroEval (1 - 2 * σ) εc f ≥ 1 := by
                  exact le_of_not_gt fun h => hf2 <| by exact Set.mem_setOf.mpr h;
                have h_cross : ∀ t, 1 - 2 * σ < t → t < crossTime skoroEval (1 - 2 * σ) εc f → |f.toFun t - f.toFun (1 - 2 * σ)| ≤ εc := by
                  intros t ht1 ht2
                  apply crossTime_osc_le skoroEval (1 - 2 * σ) εc f ht1 ht2
                generalize_proofs at *; (
                by_cases h_case : s (k - 1) = 1 - 2 * σ
                generalize_proofs at *; (
                grind);
                exact h_cross _ ( lt_of_le_of_ne ( le_of_not_gt ‹¬s ( k - 1 ) < 1 - 2 * σ› ) ( Ne.symm h_case ) ) ( by exact lt_of_lt_of_le ( by norm_num; linarith ) ‹crossTime skoroEval ( 1 - 2 * σ ) εc f ≥ 1› ) |> fun h => by simpa using h;)
              generalize_proofs at *;
              rwa [ abs_sub_comm ];
        exact abs_le.mpr ⟨ by linarith [ abs_le.mp h_tail.1, abs_le.mp h_tail.2 ], by linarith [ abs_le.mp h_tail.1, abs_le.mp h_tail.2 ] ⟩
    generalize_proofs at *; (
    apply cadlagModulus_le_of_crossing;
    any_goals tauto;
    · linarith;
    · exact fun i hi x hx => le_trans ( hosc i hi x hx ) ( by linarith );
    · exact fun x hx => le_trans ( hosctail x hx ) ( by linarith ));
  · refine' le_trans ( cadlagModulus_le_of_not_badSet hεc.le hσ hσ1 _ ) ( by linarith );
    exact fun ⟨ k, hk₁, hk₂ ⟩ => hf1 ⟨ k, hk₁, by linarith [ h k hk₁ ], by linarith [ h k hk₁ ] ⟩

/-- **Aldous's tightness criterion, packaged.**  A family `(X i)` of `D`-valued random
elements on probability spaces `(Ω i, P i)`, each adapted to a right-continuous filtration
`𝓕 i`, whose laws are (i) uniformly tight in sup-norm (`hbdd`) and (ii) satisfy the Aldous
stopping-time condition `α_i(δ, ε) → 0` uniformly in `i` (`hald`), induces a tight family of
laws on `D`.  This is the formalized classical criterion (Aldous 1978; Billingsley
(16.24)ff).  The witness is `interiorBadSet ∪ termSet` (interior crossings plus the boundary
shift-average detector); its mass is controlled by the genuine two-scale argument (Steps 2–4
above).  The earlier single-scale `badSet` route was refuted by counterexample (Task 8 for
the interior, and the boundary gradual-rise counterexample above); this is Aldous's original
two-scale mechanism with the correct boundary handling. -/
theorem aldous_tightness {ι : Type*}
    {Ω : ι → Type*} [mΩ : ∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [hP : ∀ i, IsProbabilityMeasure (P i)]
    (X : ∀ i, Ω i → Skoro) (hX : ∀ i, Measurable (X i))
    (𝓕 : ∀ i, Filtration ℝ (mΩ i))
    (hrc : ∀ i, (𝓕 i).rightCont = 𝓕 i)
    (hadapt : ∀ i r, Measurable[(𝓕 i) r] (fun ω => (X i ω).toFun r))
    (hbdd : ∀ η : ℝ≥0∞, 0 < η → ∃ a : ℝ, ∀ i, (P i) {ω | a ≤ supNorm (X i ω)} ≤ η)
    (hald : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ δ : ℝ, 0 < δ ∧
        ∀ i, aldousQ (P i) (fun t ω => (X i ω).toFun t) (𝓕 i) δ ε ≤ η) :
    IsTightMeasureSet (Set.range (fun i => (P i).map (X i))) := by
  apply isTightMeasureSet_of_bdd_of_modulus_witness
  · intro η hη
    obtain ⟨a, ha⟩ := hbdd η hη
    refine ⟨a, ?_⟩
    rintro μ ⟨i, rfl⟩
    rw [Measure.map_apply (hX i) (measurableSet_le measurable_const measurable_supNorm)]
    exact ha i
  · intro ε hε η hη
    -- `εc = ε/8`, increment level `εc/2 = ε/16`; off the witness the modulus is `≤ 4εc = ε/2 < ε`.
    -- Tolerances: `η₁ = (η/2)/16`, `η₂ = (η/2)/16`, so `16η₁ + 16η₂ = η/2 + η/2 = η`.
    set εc : ℝ := ε / 8 with hεcdef
    have hεc : 0 < εc := by rw [hεcdef]; positivity
    set η₁ : ℝ≥0∞ := (η / 2) / 16 with hη₁def
    set η₂ : ℝ≥0∞ := (η / 2) / 16 with hη₂def
    have hη₁ : 0 < η₁ := ENNReal.div_pos (ENNReal.div_pos hη.ne' (by norm_num)).ne' (by norm_num)
    have hη₂ : 0 < η₂ := ENNReal.div_pos (ENNReal.div_pos hη.ne' (by norm_num)).ne' (by norm_num)
    obtain ⟨d₁, hd₁pos, hd₁⟩ := hald (εc / 2) (by positivity) η₁ hη₁
    set δ := min (d₁ / 2) (1 / 2) with hδdef
    have hδpos : 0 < δ := lt_min (by positivity) (by norm_num)
    have h2δ : 2 * δ ≤ d₁ := by
      have : δ ≤ d₁ / 2 := min_le_left _ _; linarith
    set q : ℕ := ⌈2 / δ⌉₊ + 1 with hqdef
    have hq : 2 < (q : ℝ) * δ := by
      have hlt : 2 / δ < (q : ℝ) := by
        have h1 : (2 : ℝ) / δ ≤ (⌈2 / δ⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ((⌈2 / δ⌉₊ : ℝ)) < (q : ℝ) := by
          rw [hqdef]; push_cast; linarith
        linarith
      have hmul := mul_lt_mul_of_pos_right hlt hδpos
      rwa [div_mul_cancel₀ 2 hδpos.ne'] at hmul
    have hqpos : 0 < q := by positivity
    have hqfin : ((q : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top q
    have hη₂q : 0 < η₂ / (q : ℝ≥0∞) := ENNReal.div_pos hη₂.ne' hqfin
    obtain ⟨d₂, hd₂pos, hd₂⟩ := hald (εc / 2) (by positivity) (η₂ / (q : ℝ≥0∞)) hη₂q
    set σ := min (min (d₂ / 4) (δ)) (1 / 4) with hσdef
    have hσpos : 0 < σ := lt_min (lt_min (by positivity) hδpos) (by norm_num)
    have hσd4 : σ ≤ d₂ / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
    have h4σ : 2 * (2 * σ) ≤ d₂ := by linarith
    have h2σ : 2 * σ ≤ d₂ := by linarith
    have hσδ : σ ≤ δ := le_trans (min_le_left _ _) (min_le_right _ _)
    have hσ1 : σ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    refine ⟨σ, hσpos, hσ1, ?_⟩
    rintro μ ⟨i, rfl⟩
    refine ⟨interiorBadSet εc σ ∪ boundarySet εc σ, ?_, ?_⟩
    · intro f hf
      by_contra hfb
      rw [Set.mem_union, not_or] at hfb
      have hle := cadlagModulus_le_of_not_interiorBad_boundarySet hεc hσpos hσ1 hfb.1 hfb.2
      simp only [Set.mem_setOf_eq] at hf
      -- 4 * εc = ε/2 < ε
      have : (4 : ℝ) * εc = ε / 2 := by rw [hεcdef]; ring
      rw [this] at hle; linarith
    · have hQδi : aldousQ (P i) (fun t ω => (X i ω).toFun t) (𝓕 i) (2 * δ) (εc / 2) ≤ η₁ :=
        le_trans (aldousQ_mono_shift (P i) _ (𝓕 i) h2δ) (hd₁ i)
      have hQσi : aldousQ (P i) (fun t ω => (X i ω).toFun t) (𝓕 i) (2 * σ) (εc / 2)
          ≤ η₂ / (q : ℝ≥0∞) := le_trans (aldousQ_mono_shift (P i) _ (𝓕 i) h2σ) (hd₂ i)
      have hQσb : aldousQ (P i) (fun t ω => (X i ω).toFun t) (𝓕 i) (2 * (2 * σ)) (εc / 2)
          ≤ η₂ / (q : ℝ≥0∞) := le_trans (aldousQ_mono_shift (P i) _ (𝓕 i) h4σ) (hd₂ i)
      calc (P i).map (X i) (interiorBadSet εc σ ∪ boundarySet εc σ)
          ≤ (P i).map (X i) (interiorBadSet εc σ) + (P i).map (X i) (boundarySet εc σ) :=
            measure_union_le _ _
        _ ≤ (16 * η₁ + 8 * η₂) + 8 * aldousQ (P i) (fun t ω => (X i ω).toFun t) (𝓕 i) (2 * (2 * σ)) (εc / 2) :=
            add_le_add
              (prob_map_interiorBadSet_le (P i) (X i) (hX i) (𝓕 i) (hrc i) (hadapt i)
                hεc hδpos hσpos hσδ q hq hQδi hQσi)
              (prob_map_boundarySet_le (P i) (X i) (hX i) (𝓕 i) (hrc i) (hadapt i) hεc hσpos hσ1)
        _ ≤ (16 * η₁ + 8 * η₂) + 8 * (η₂ / (q : ℝ≥0∞)) := by gcongr
        _ ≤ (16 * η₁ + 8 * η₂) + 8 * η₂ := by
            have hle : η₂ / (q : ℝ≥0∞) ≤ η₂ := by
              calc η₂ / (q : ℝ≥0∞) ≤ η₂ / 1 := by
                    gcongr
                    have : 1 ≤ q := hqpos
                    exact_mod_cast this
                _ = η₂ := by rw [div_one]
            gcongr
        _ = 16 * η₁ + 16 * η₂ := by ring
        _ = η := by
            have h16 : (16 : ℝ≥0∞) * ((η / 2) / 16) = η / 2 := by
              rw [mul_comm]; exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
            rw [hη₁def, hη₂def, h16, ENNReal.add_halves]

/-- **`aldous_of_moment`.**  The second-moment route: if, uniformly over the family and over
stopping times `τ ≤ 1` and shifts `δ ≤ d`, the truncated increments have second moment
`≤ M(d)` with `M(d) → 0` as `d → 0` (and the sup-norm boundedness holds), the laws are
tight.  Combines `aldousQ_le_of_second_moment` (Chebyshev inside the Aldous supremum) with
`aldous_tightness`. -/
theorem aldous_of_moment {ι : Type*}
    {Ω : ι → Type*} [mΩ : ∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [hP : ∀ i, IsProbabilityMeasure (P i)]
    (X : ∀ i, Ω i → Skoro) (hX : ∀ i, Measurable (X i))
    (𝓕 : ∀ i, Filtration ℝ (mΩ i))
    (hrc : ∀ i, (𝓕 i).rightCont = 𝓕 i)
    (hadapt : ∀ i r, Measurable[(𝓕 i) r] (fun ω => (X i ω).toFun r))
    (hbdd : ∀ η : ℝ≥0∞, 0 < η → ∃ a : ℝ, ∀ i, (P i) {ω | a ≤ supNorm (X i ω)} ≤ η)
    (M : ℝ → ℝ≥0∞) (hM0 : Tendsto M (𝓝[>] 0) (𝓝 0))
    (hmeas : ∀ i (τ : Ω i → ℝ) (δ : ℝ),
      AEMeasurable (fun ω => (X i ω).toFun (min (τ ω + δ) 1) - (X i ω).toFun (τ ω)) (P i))
    (hmom : ∀ i (τ : Ω i → ℝ), IsStoppingTime (𝓕 i) (fun ω => (τ ω : WithTop ℝ)) →
        (∀ ω, τ ω ≤ 1) → ∀ d : ℝ, 0 < d → ∀ δ : ℝ, 0 ≤ δ → δ ≤ d →
          ∫⁻ ω, ENNReal.ofReal (((X i ω).toFun (min (τ ω + δ) 1) - (X i ω).toFun (τ ω)) ^ 2)
            ∂(P i) ≤ M d) :
    IsTightMeasureSet (Set.range (fun i => (P i).map (X i))) := by
  refine aldous_tightness P X hX 𝓕 hrc hadapt hbdd ?_
  intro ε hε η hη
  -- choose `d` small so that `M d / ε² < η`, using `M d → 0`.
  have hεsq : (0 : ℝ≥0∞) < ENNReal.ofReal (ε ^ 2) := by
    rw [ENNReal.ofReal_pos]; positivity
  have htends : Tendsto (fun d => M d / ENNReal.ofReal (ε ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = 0 / ENNReal.ofReal (ε ^ 2) by simp]
    exact ENNReal.Tendsto.div_const hM0 (Or.inr hεsq.ne')
  have hev : ∀ᶠ d in 𝓝[>] (0:ℝ), M d / ENNReal.ofReal (ε ^ 2) < η :=
    htends.eventually (Iio_mem_nhds hη)
  obtain ⟨d, hdlt, hdpos⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨d, hdpos, fun i => ?_⟩
  refine le_trans (aldousQ_le_of_second_moment (P i) _ (𝓕 i) hε (hmeas i)
      (fun τ hτ hτ1 δ hδ0 hδd => hmom i τ hτ hτ1 d hdpos δ hδ0 hδd)) (le_of_lt hdlt)

end

end SkorokhodBasic