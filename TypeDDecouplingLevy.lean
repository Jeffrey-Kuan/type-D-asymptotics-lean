import Mathlib
import TypeDDecouplingMartingaleCLT

/-!
# Lévy's continuity theorem on `ℝ`

This file proves **Lévy's continuity theorem** on `ℝ` in its *identified-limit* form,
discharging the named hypothesis `TypeDDecoupling.MartingaleCLT.LevyContinuityℝ`
introduced in `TypeDDecouplingMartingaleCLT.lean` (which is **not** modified here).

The statement proved (`levyContinuityℝ`) is:
for probability measures `ξ n, ν` on `ℝ`, if `charFun (ξ n) t → charFun ν t` for
every `t`, then `ξ n → ν` weakly.

## Outcome

Prokhorov's theorem *is* available in the pinned Mathlib
(`MeasureTheory.isCompact_closure_of_isTightMeasureSet`), and the space
`ProbabilityMeasure ℝ` is metrizable
(`MeasureTheory.instMetrizableSpaceProbabilityMeasure`).  Consequently the
sanctioned fallback hypothesis `ProkhorovSeqℝ` is **not** needed: Lévy continuity
is proved outright, and the deliverable `mcleish_clt_unconditional` discharges the
`hLevy` argument of `mcleish_clt` unconditionally.

## Structure

* **Tier 1** — the truncation inequality is reused from Mathlib:
  `MeasureTheory.measureReal_abs_gt_le_integral_charFun`.
* **Tier 2** — tightness from pointwise `charFun` convergence
  (`isTightMeasureSet_of_tendsto_charFun`), via a uniform tail bound
  (`exists_uniform_tail`).
* **Tier 3** — assembly via Prokhorov + `charFun` extensionality
  (`Measure.ext_of_charFun`) + the sub-subsequence principle
  (`tendsto_of_subseq_tendsto`).
-/

open MeasureTheory ProbabilityTheory Complex Filter Finset
open scoped Topology BigOperators ENNReal NNReal Real

namespace TypeDDecoupling.Levy

/-- The quantity controlling the tail of a probability measure through its
characteristic function: `tailBound μ s = s⁻¹ * ‖∫_{-s}^{s} (1 - charFun μ t) dt‖`. -/
noncomputable def tailBound (μ : Measure ℝ) (s : ℝ) : ℝ :=
  s⁻¹ * ‖∫ t in (-s)..s, 1 - charFun μ t‖

/-
**Tier 1 (reused from Mathlib).** The truncation inequality specialised to the
`tailBound` form: for `s > 0`,
`μ {x : |x| > 2/s} ≤ s⁻¹ ‖∫_{-s}^{s} (1 - charFun μ) ‖`.
-/
lemma measureReal_tail_le_tailBound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) :
    μ.real {x | 2 * s⁻¹ < |x|} ≤ tailBound μ s := by
  convert MeasureTheory.measureReal_abs_gt_le_integral_charFun ( show 0 < 2 * s⁻¹ by positivity ) using 1 ; ring_nf;
  · unfold tailBound; norm_num;
  · infer_instance

/-
The characteristic function of a probability measure on `ℝ` is continuous.
-/
lemma continuous_charFun_real (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Continuous (fun t => charFun μ t) := by
  refine' continuous_iff_continuousAt.mpr _;
  intro t₀; apply_rules [ MeasureTheory.tendsto_integral_filter_of_dominated_convergence ];
  any_goals exact fun _ => 1;
  · exact Filter.Eventually.of_forall fun n => Continuous.aestronglyMeasurable ( by continuity );
  · norm_num [ Complex.norm_exp ];
  · norm_num;
  · exact Filter.Eventually.of_forall fun x => Complex.continuous_exp.continuousAt.tendsto.comp <| Continuous.tendsto ( by continuity ) _

/-
For a fixed `s > 0`, `tailBound (ξ n) s → tailBound ν s` when the characteristic
functions converge pointwise (dominated convergence on the compact interval).
-/
lemma tailBound_tendsto (ξ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (h : ∀ t, Tendsto (fun n => charFun (ξ n : Measure ℝ) t) atTop
      (𝓝 (charFun (ν : Measure ℝ) t))) {s : ℝ} :
    Tendsto (fun n => tailBound (ξ n : Measure ℝ) s) atTop
      (𝓝 (tailBound (ν : Measure ℝ) s)) := by
  refine' Filter.Tendsto.mul tendsto_const_nhds _;
  refine' Filter.Tendsto.norm _;
  refine' intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
  refine' fun t => 2;
  · refine' Filter.Eventually.of_forall fun n => _;
    exact Continuous.aestronglyMeasurable ( continuous_const.sub ( continuous_charFun_real _ ) );
  · simp +zetaDelta at *;
    exact ⟨ 0, fun n hn => Filter.Eventually.of_forall fun x hx => by simpa using MeasureTheory.norm_one_sub_charFun_le_two ⟩;
  · norm_num;
  · exact Filter.Eventually.of_forall fun x hx => tendsto_const_nhds.sub ( h x )

/-
Since `charFun ν` is continuous with `charFun ν 0 = 1`, for every `ε > 0` there is
`s > 0` with `tailBound ν s < ε`.
-/
lemma exists_tailBound_lt (ν : Measure ℝ) [IsProbabilityMeasure ν] {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ tailBound ν s < ε := by
  -- By continuity of `charFun ν` at `0` and `charFun ν 0 = 1`, there is `s > 0` such that for all `t` with `|t| ≤ s`, `‖1 - charFun ν t‖ ≤ ε/4`.
  obtain ⟨s, hs_pos, hs⟩ : ∃ s : ℝ, 0 < s ∧ ∀ t, |t| ≤ s → ‖1 - charFun ν t‖ ≤ ε / 4 := by
    obtain ⟨ δ, hδ_pos, hδ ⟩ := Metric.continuous_iff.mp ( show Continuous fun t : ℝ => ‖1 - charFun ν t‖ from Continuous.norm <| continuous_const.sub <| continuous_charFun_real ν ) 0 ( ε / 4 ) ( by linarith );
    simp_all +decide [ charFun_zero ];
    exact ⟨ δ / 2, half_pos hδ_pos, fun t ht => le_of_lt ( hδ t ( by linarith ) ) ⟩;
  refine' ⟨ s, hs_pos, _ ⟩;
  refine' lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( intervalIntegral.norm_integral_le_of_norm_le_const _ ) ( inv_nonneg.2 hs_pos.le ) ) _;
  exacts [ ε / 4, fun x hx => hs x <| by cases Set.mem_uIoc.mp hx <;> exact abs_le.mpr ⟨ by linarith, by linarith ⟩, by rw [ abs_of_nonneg ] <;> nlinarith [ mul_inv_cancel₀ hs_pos.ne' ] ]

/-
A single probability measure on `ℝ` has arbitrarily small tails.
-/
lemma exists_tail_single (μ : Measure ℝ) [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ μ.real {x | R < |x|} ≤ ε := by
  have h_tail : Filter.Tendsto (fun R : ℝ => μ.real {x | R < |x|}) Filter.atTop (nhds 0) := by
    have h_tail : Filter.Tendsto (fun R : ℝ => μ {x | R < |x|}) Filter.atTop (nhds 0) := by
      convert MeasureTheory.tendsto_measure_iInter_atTop _ _ _;
      · rw [ show ( ⋂ n : ℝ, { x : ℝ | n < |x| } ) = ∅ by rw [ Set.eq_empty_iff_forall_notMem ] ; rintro x hx; exact absurd ( Set.mem_iInter.mp hx ( |x| ) ) ( by norm_num ) ] ; norm_num;
      · infer_instance;
      · exact fun i => measurableSet_lt measurable_const measurable_norm |> MeasurableSet.nullMeasurableSet;
      · exact fun x y hxy => Set.setOf_subset_setOf.mpr fun z hz => lt_of_le_of_lt hxy hz;
      · exact ⟨ 0, ne_of_lt ( MeasureTheory.measure_lt_top _ _ ) ⟩;
    convert ENNReal.tendsto_toReal ( show ( 0 : ENNReal ) ≠ ⊤ by norm_num ) |> Filter.Tendsto.comp <| h_tail using 1;
  exact Filter.eventually_atTop.mp ( h_tail.eventually ( ge_mem_nhds hε ) ) |> fun ⟨ R, hR ⟩ => ⟨ Max.max R 1, by positivity, hR _ ( le_max_left _ _ ) ⟩

/-
**Tier 2 (uniform tail bound).** If `charFun (ξ n) → charFun ν` pointwise, then the
family `{ξ n}` has uniformly small tails.
-/
lemma exists_uniform_tail (ξ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (h : ∀ t, Tendsto (fun n => charFun (ξ n : Measure ℝ) t) atTop
      (𝓝 (charFun (ν : Measure ℝ) t))) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ n, (ξ n : Measure ℝ).real {x | R < |x|} ≤ ε := by
  -- By `exists_tailBound_lt (ν : Measure ℝ)` with `ε/2` to get `s > 0` with `tailBound (ν : Measure ℝ) s < ε/2`.
  obtain ⟨s, hs_pos, hs⟩ : ∃ s : ℝ, 0 < s ∧ tailBound (ν : Measure ℝ) s < ε / 2 := by
    exact exists_tailBound_lt _ ( half_pos hε );
  -- By `tailBound_tendsto ξ ν h hs`, `tailBound (ξ n) s → tailBound ν s`; since `tailBound ν s < ε`, `Filter.Tendsto.eventually_lt_const` gives `∀ᶠ n in atTop, tailBound (ξ n) s < ε`, hence there is `N` with `∀ n ≥ N, tailBound (ξ n) s < ε`.
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, tailBound (ξ n : Measure ℝ) s < ε := by
    exact Filter.eventually_atTop.mp ( tailBound_tendsto ξ ν h |> fun h => h.eventually ( gt_mem_nhds <| by linarith ) );
  -- Using `exists_tail_single`, `choose R' hR'pos hR' using fun n => exists_tail_single (ξ n : Measure ℝ) hε`, giving `R' : ℕ → ℝ`, `hR'pos : ∀ n, 0 < R' n`, and `hR' : ∀ n, (ξ n : Measure ℝ).real {x | R' n < |x|} ≤ ε`.
  obtain ⟨R', hR'pos, hR'⟩ : ∃ R' : ℕ → ℝ, (∀ n, 0 < R' n) ∧ (∀ n, (ξ n : Measure ℝ).real {x | R' n < |x|} ≤ ε) := by
    exact ⟨ fun n => Classical.choose ( exists_tail_single ( ξ n : Measure ℝ ) hε ), fun n => Classical.choose_spec ( exists_tail_single ( ξ n : Measure ℝ ) hε ) |>.1, fun n => Classical.choose_spec ( exists_tail_single ( ξ n : Measure ℝ ) hε ) |>.2 ⟩;
  refine' ⟨ Max.max ( 2 * s⁻¹ + 1 ) ( ∑ n ∈ Finset.range N, |R' n| + 1 ), _, _ ⟩;
  · positivity;
  · intro n;
    by_cases hn : n < N;
    · refine' le_trans ( MeasureTheory.measureReal_mono _ _ ) ( hR' n );
      · exact fun x hx => lt_of_le_of_lt ( le_trans ( le_abs_self _ ) ( Finset.single_le_sum ( fun n _ => abs_nonneg ( R' n ) ) ( Finset.mem_range.mpr hn ) ) |> le_trans <| le_add_of_nonneg_right zero_le_one |> le_trans <| le_max_right _ _ ) hx.out;
      · exact MeasureTheory.measure_ne_top _ _;
    · refine' le_trans _ ( le_of_lt ( hN n ( le_of_not_gt hn ) ) );
      refine' le_trans _ ( measureReal_tail_le_tailBound _ hs_pos );
      exact MeasureTheory.measureReal_mono ( fun x hx => by exact Set.mem_setOf.mpr ( lt_of_le_of_lt ( le_max_of_le_left ( by linarith [ inv_pos.mpr hs_pos ] ) ) hx ) ) ( by aesop )

/-
**Tier 2 (tightness).** The family `{ξ n}` is tight.
-/
lemma isTightMeasureSet_of_tendsto_charFun (ξ : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ)
    (h : ∀ t, Tendsto (fun n => charFun (ξ n : Measure ℝ) t) atTop
      (𝓝 (charFun (ν : Measure ℝ) t))) :
    IsTightMeasureSet {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range ξ} := by
  refine' MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun ε hε => _;
  rcases eq_or_ne ε ⊤ with rfl | hε_ne_top;
  · exact ⟨ ∅, isCompact_empty, fun μ hμ => le_top ⟩;
  · obtain ⟨ R, hR_pos, hR ⟩ := exists_uniform_tail ξ ν h ( ENNReal.toReal_pos hε.ne' hε_ne_top );
    refine' ⟨ Metric.closedBall 0 R, ProperSpace.isCompact_closedBall _ _, _ ⟩;
    rintro _ ⟨ μ, ⟨ n, rfl ⟩, rfl ⟩;
    convert ENNReal.ofReal_le_ofReal ( hR n ) using 1;
    · simp +decide [ Set.compl_def, Metric.mem_closedBall ];
    · rw [ ENNReal.ofReal_toReal ( by aesop ) ]

/-
Weak convergence of probability measures on `ℝ` implies pointwise convergence of
characteristic functions.
-/
lemma charFun_tendsto_of_tendsto {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : Tendsto μs atTop (𝓝 μ)) (t : ℝ) :
    Tendsto (fun n => charFun (μs n : Measure ℝ) t) atTop (𝓝 (charFun (μ : Measure ℝ) t)) := by
  have h_integral : Filter.Tendsto (fun n => ∫ ω, Complex.exp (t * ω * Complex.I) ∂(μs n : Measure ℝ)) Filter.atTop (nhds (∫ ω, Complex.exp (t * ω * Complex.I) ∂(μ : Measure ℝ))) := by
    have h_charFun : ∀ f : C(ℝ, ℂ), Continuous f ∧ BddAbove (Set.range (fun x => ‖f x‖)) → Filter.Tendsto (fun n => ∫ ω, f ω ∂(μs n : Measure ℝ)) Filter.atTop (nhds (∫ ω, f ω ∂(μ : Measure ℝ))) := by
      intro f hf;
      convert MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ |>.1 h ( BoundedContinuousFunction.mk ⟨ f, hf.1 ⟩ ?_ ) using 1;
      exact ⟨ hf.2.choose + hf.2.choose, fun x y => le_trans ( dist_le_norm_add_norm _ _ ) ( add_le_add ( hf.2.choose_spec ⟨ x, rfl ⟩ ) ( hf.2.choose_spec ⟨ y, rfl ⟩ ) ) ⟩;
    convert h_charFun ( ContinuousMap.mk ( fun x : ℝ => Complex.exp ( t * x * Complex.I ) ) ( by continuity ) ) ⟨ by continuity, ?_ ⟩ using 1;
    norm_num [ Complex.norm_exp ];
  unfold charFun;
  simpa [ mul_assoc, mul_comm, mul_left_comm ] using h_integral

/-
**Tier 3.** Lévy's continuity theorem on `ℝ` (identified-limit form).
-/
theorem levyContinuityℝ : TypeDDecoupling.MartingaleCLT.LevyContinuityℝ := by
  intro ξ ν h;
  refine' tendsto_of_subseq_tendsto _;
  intro ns hns
  obtain ⟨a, ha, φ, hφmono, hφlim⟩ : ∃ a ∈ closure (Set.range ξ), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (fun k => ξ (ns (φ k))) Filter.atTop (nhds a) := by
    have htight := isTightMeasureSet_of_tendsto_charFun ξ ν h;
    have hcompact : IsCompact (closure (Set.range ξ)) := by
      convert ( isCompact_closure_of_isTightMeasureSet htight ) using 1;
    have := hcompact.isSeqCompact fun k => subset_closure <| Set.mem_range_self <| ns k;
    exact this;
  -- Identify the limit: it suffices to show `(a : Measure ℝ) = (ν : Measure ℝ)`, then `ProbabilityMeasure.toMeasure_injective`.
  have h_eq : (a : Measure ℝ) = (ν : Measure ℝ) := by
    apply Measure.ext_of_charFun;
    ext t;
    exact tendsto_nhds_unique ( charFun_tendsto_of_tendsto hφlim t ) ( h t |> Filter.Tendsto.comp <| hns.comp hφmono.tendsto_atTop );
  cases a ; cases ν ; aesop

/-- **Corollary (deliverable).** McLeish's martingale-difference-array CLT with the
`hLevy` hypothesis discharged: weak convergence of `∑_j X_{n,j}` to `N(0, v)` under the
martingale-difference structure, with **no** Lévy-continuity input required (it is
supplied internally by `levyContinuityℝ`). -/
theorem mcleish_clt_unconditional {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (kn : ℕ → ℕ) (𝓕 : ℕ → ℕ → MeasurableSpace Ω)
    (X : ℕ → ℕ → Ω → ℝ) (v : ℝ≥0) (b : ℕ → ℝ) (C : ℝ)
    (hmono : ∀ n, Monotone (𝓕 n)) (hle : ∀ n k, 𝓕 n k ≤ mΩ)
    (hadapt : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (X n j))
    (hmeas : ∀ n, Measurable (MartingaleCLT.partialSum (X n) (kn n)))
    (hmds : ∀ n j, μ[X n j | 𝓕 n j] =ᵐ[μ] 0)
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n j ω, |X n j ω| ≤ b n)
    (hCbr : ∀ n ω, ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2 ≤ C)
    (hbracket : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2) atTop (𝓝 (v : ℝ))) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n => ⟨μ.map (MartingaleCLT.partialSum (X n) (kn n)),
          Measure.isProbabilityMeasure_map (hmeas n).aemeasurable⟩)
      atTop (𝓝 ⟨gaussianReal 0 v, inferInstance⟩) :=
  MartingaleCLT.mcleish_clt levyContinuityℝ kn 𝓕 X v b C hmono hle hadapt hmeas hmds
    hb0 hblim hbound hCbr hbracket

end TypeDDecoupling.Levy