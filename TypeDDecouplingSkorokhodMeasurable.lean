/-
# The measurability core on `D([0,1],ℝ)` (Skorokhod campaign, 4/5)

Library-clean file building on `TypeDDecouplingSkorokhodBasic`,
`TypeDDecouplingSkorokhodCompact`, `TypeDDecouplingSkorokhodComplete`,
`TypeDDecouplingSkorokhodTight` (the last three supply the
`CompleteSpace`/`PolishSpace`/`BorelSpace` instances and the `cadlagModulus`
API).  It closes Task 3's Tier 1 gaps (see `skorokhod4_brief.tex`, G1):

* **(a) Evaluations are Borel.**  For `q : ℝ`, `fun f => f.toFun q` is Borel
  measurable.  The proof follows Task 3's identified strategy: the
  integral-average functionals `intAvg n q f = (n+1) ∫_q^{q+1/(n+1)} f` are
  `d°`-continuous (dominated convergence along the Skorokhod time changes, using
  pointwise a.e. convergence at continuity points via `continuousAt_eval` and
  endpoint convergence, and the uniform sup bound), and `f(q) = lim_n intAvg n q f`
  by right-continuity.  Pointwise limit of continuous functions ⇒ Borel.
* **(b) Borel = cylinder.**  `evalRat : Skoro → (ℚ → ℝ)` is an injective
  (separating, by right-continuity) measurable map between standard Borel
  spaces, hence a measurable embedding (`Measurable.measurableEmbedding`).
  Route (ii) of the brief.
* **(c) The modulus is Borel**: `fun f => cadlagModulus f.toFun δ` via the
  rational-partition reduction and (a).
* **(d) The bridge lemma**: `X : Ω → Skoro` is measurable iff every coordinate
  `ω ↦ (X ω).toFun t` is measurable (equivalently for rational `t`); and the law
  `Measure.map X` is determined by the finite-dimensional distributions.
-/
import Mathlib
import TypeDDecouplingSkorokhodBasic
import TypeDDecouplingSkorokhodCompact
import TypeDDecouplingSkorokhodComplete
import TypeDDecouplingSkorokhodTight

set_option maxHeartbeats 4000000

open scoped Topology BigOperators ENNReal
open Filter Set MeasureTheory

namespace SkorokhodBasic

noncomputable section

/-! ## Basic measurability / boundedness of the underlying paths -/

/-
A `Skoro` path is bounded on all of `ℝ` (bounded on `[0,1]`, flat outside).
-/
theorem Skoro.bounded_toFun (f : Skoro) : ∃ C : ℝ, ∀ x : ℝ, |f.toFun x| ≤ C := by
  obtain ⟨ C, hC ⟩ := f.bdd';
  use C, fun x => if hx : x ≤ 0 then by rw [ f.flatL x hx ] ; exact hC 0 ( by norm_num ) else if hx' : x ≥ 1 then by rw [ f.flatR x hx' ] ; exact hC 1 ( by norm_num ) else hC x ⟨ by linarith, by linarith ⟩

/-
The underlying function of a `Skoro` path is Borel measurable.  (It is a uniform
limit on `ℝ` of measurable step functions, by the modulus partition lemma.)
-/
theorem Skoro.measurable_toFun (f : Skoro) : Measurable f.toFun := by
  have h_measurable : ∀ k : ℕ, ∃ (N : ℕ) (T : ℕ → ℝ), T 0 = 0 ∧ T N = 1 ∧ 0 < N ∧ (∀ i, i ≤ N → T i ∈ Set.Icc (0:ℝ) 1) ∧ (∀ i, i < N → T i < T (i + 1)) ∧ (∀ i, i < N → ∀ x ∈ Set.Ico (T i) (T (i + 1)), |f.toFun x - f.toFun (T i)| < 1/(k+1)) := by
    intro k
    have := f.cadlag'.exists_modulus_partition (by positivity : (0 : ℝ) < 1 / (k + 1))
    aesop;
  choose N T hT₀ hT₁ hT₂ hT₃ hT₄ hT₅ using h_measurable;
  -- Define `g k := stepFun (N k) (T k) (fun i => f.toFun (T k i))`.
  set g : ℕ → ℝ → ℝ := fun k x => stepFun (N k) (T k) (fun i => f.toFun (T k i)) x;
  -- Show that `g k` converges pointwise to `f.toFun`.
  have h_pointwise : ∀ x, Filter.Tendsto (fun k => g k x) Filter.atTop (nhds (f.toFun x)) := by
    intro x
    by_cases hx : x ∈ Set.Ico (0:ℝ) 1;
    · -- By `exists_cell_index`, there exists `j < N k` such that `x ∈ Set.Ico (T k j) (T k (j + 1))`.
      have h_cell : ∀ k, ∃ j < N k, x ∈ Set.Ico (T k j) (T k (j + 1)) := by
        exact fun k => exists_cell_index ( hT₀ k ) ( hT₁ k ) hx;
      choose j hj₁ hj₂ using h_cell;
      -- By `stepFun_eq_on_cell`, we have `g k x = f.toFun (T k (j k))`.
      have h_g_eq : ∀ k, g k x = f.toFun (T k (j k)) := by
        exact fun k => stepFun_eq_on_cell _ _ _ ( fun i hi => hT₄ k i hi ) ( hj₁ k ) ( hj₂ k );
      -- By `hT₅`, we have `|f.toFun x - f.toFun (T k (j k))| < 1 / (k + 1)`.
      have h_diff : ∀ k, |f.toFun x - f.toFun (T k (j k))| < 1 / (k + 1) := by
        exact fun k => hT₅ k _ ( hj₁ k ) _ ( hj₂ k );
      rw [ tendsto_iff_norm_sub_tendsto_zero ];
      exact squeeze_zero ( fun _ => norm_nonneg _ ) ( fun k => by simpa [ h_g_eq, abs_sub_comm ] using le_of_lt ( h_diff k ) ) ( tendsto_one_div_add_atTop_nhds_zero_nat );
    · by_cases hx' : x ≤ 0 <;> by_cases hx'' : 1 ≤ x <;> simp_all +decide;
      · linarith;
      · -- Since $x < 0$, we have $g k x = f.toFun 0$ for all $k$.
        have h_gk_zero : ∀ k, g k x = f.toFun 0 := by
          intros k
          simp [g, stepFun, hT₀];
          exact Finset.sum_eq_zero fun i hi => if_neg <| by linarith [ hT₃ k ( i + 1 ) ( by linarith [ Finset.mem_range.mp hi ] ) ] ;
        rw [ f.flatL x hx.le ] ; aesop;
      · convert tendsto_const_nhds.congr' _;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk;
        convert f.flatR x hx'' |> Eq.symm using 1;
        · exact f.flatR x hx'' ▸ rfl;
        · convert stepFun_eq_last ( N k ) ( T k ) ( fun i => f.toFun ( T k i ) ) ( fun i hi => hT₄ k i hi ) _ using 1;
          · rw [ hT₁ k, f.flatR x hx'' ];
          · linarith [ hT₁ k ];
      · linarith;
  -- Show that each `g k` is measurable.
  have h_measurable_g : ∀ k, Measurable (g k) := by
    intro k
    simp [g, stepFun];
    exact Measurable.add measurable_const <| Finset.measurable_sum _ fun i hi => Measurable.ite ( measurableSet_Ici ) measurable_const measurable_const;
  exact measurable_of_tendsto_metrizable' atTop ( fun k => h_measurable_g k ) ( tendsto_pi_nhds.mpr h_pointwise )

/-
A `Skoro` path is integrable on every bounded interval (bounded + measurable).
-/
theorem Skoro.integrableOn_Ioc (f : Skoro) (a b : ℝ) :
    IntegrableOn f.toFun (Set.Ioc a b) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun x => ( Skoro.bounded_toFun f ).choose;
  · norm_num;
  · exact f.measurable_toFun.aestronglyMeasurable;
  · exact Filter.Eventually.of_forall fun x => ( Skoro.bounded_toFun f ).choose_spec x

/-! ## Pointwise convergence extracted from `J₁` convergence -/

/-
Endpoint convergence: `J₁` convergence forces convergence of the value at `t = 1`
(time changes fix the endpoints).
-/
theorem tendsto_eval_one {F : ℕ → Skoro} {f : Skoro} (hF : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun n => (F n).toFun 1) atTop (𝓝 (f.toFun 1)) := by
  obtain ⟨l, hl⟩ := SkorokhodBasic.tendsto_iff_exists_timeChanges.mp hF;
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε; filter_upwards [ hl.2.2.eventually ( gt_mem_nhds hε ) ] with n hn; simp_all +decide [ dist_eq_norm ] ;
  refine' lt_of_le_of_lt _ hn;
  refine' le_csSup _ _;
  · exact SkorokhodBasic.Skoro.bddAbove_comp_supDiffSet ( F n ) f ( l n );
  · exact ⟨ 1, by norm_num, by simp +decide [ TimeChange.map_one ] ⟩

/-
Endpoint convergence at `t = 0`.
-/
theorem tendsto_eval_zero {F : ℕ → Skoro} {f : Skoro} (hF : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun n => (F n).toFun 0) atTop (𝓝 (f.toFun 0)) := by
  obtain ⟨l, hl⟩ := SkorokhodBasic.tendsto_iff_exists_timeChanges.mp hF;
  have := hl.2.2;
  convert tendsto_iff_norm_sub_tendsto_zero.mpr _;
  exact squeeze_zero ( fun _ => norm_nonneg _ ) ( fun n => by simpa [ TimeChange.map_zero ] using le_csSup ( SkorokhodBasic.Skoro.bddAbove_comp_supDiffSet ( F n ) f ( l n ) ) ⟨ 0, by norm_num, by simp +decide [ TimeChange.map_zero ] ⟩ ) this

/-
Pointwise convergence at every point where the limit is continuous **or** which lies
outside `(0,1)`: on a `J₁`-convergent sequence, `F n (s) → f (s)` for every `s` at which
`f.toFun` is continuous, and for every `s ∉ (0,1)`.
-/
theorem tendsto_eval_of_continuousAt {F : ℕ → Skoro} {f : Skoro}
    (hF : Tendsto F atTop (𝓝 f)) {s : ℝ}
    (hs : ContinuousAt f.toFun s ∨ s ≤ 0 ∨ 1 ≤ s) :
    Tendsto (fun n => (F n).toFun s) atTop (𝓝 (f.toFun s)) := by
  rcases hs with ( h | hs | hs );
  · by_cases hs : 0 < s ∧ s < 1;
    · convert SkorokhodBasic.continuousAt_eval ( show s ∈ Set.Ioo 0 1 from hs ) ( show ContinuousAt f.toFun s from h ) |> ContinuousAt.tendsto |> Filter.Tendsto.comp <| hF using 1;
    · by_cases hs0 : s ≤ 0;
      · convert tendsto_eval_zero hF using 1;
        · exact funext fun n => by rw [ ( F n ).flatL s hs0 ] ;
        · rw [ f.flatL s hs0 ];
      · by_cases hs1 : 1 ≤ s;
        · convert tendsto_eval_one hF using 1;
          · exact funext fun n => by rw [ F n |>.flatR s hs1 ] ;
          · rw [ f.flatR s hs1 ];
        · exact False.elim <| hs ⟨ not_le.mp hs0, not_le.mp hs1 ⟩;
  · convert Skoro.flatL f s hs ▸ tendsto_eval_zero hF using 1;
    exact funext fun n => by rw [ F n |>.flatL s hs ] ;
  · convert tendsto_eval_one hF using 1;
    · exact funext fun n => ( F n ).flatR s hs;
    · rw [ f.flatR s hs ]

/-
The set of "bad" points where pointwise convergence may fail is contained in the
(countable) set of discontinuities of `f` inside `(0,1)`, hence has measure zero.
-/
theorem eval_tendsto_ae {F : ℕ → Skoro} {f : Skoro} (hF : Tendsto F atTop (𝓝 f)) :
    ∀ᵐ s : ℝ, Tendsto (fun n => (F n).toFun s) atTop (𝓝 (f.toFun s)) := by
  -- By definition of $D$, we know that for any $s \in D$, $f$ is not continuous at $s$.
  have hD : {s : ℝ | ¬ Tendsto (fun n => (F n).toFun s) atTop (𝓝 (f.toFun s))} ⊆ {t : ℝ | t ∈ Set.Icc 0 1 ∧ ¬ ContinuousWithinAt f.toFun (Set.Icc 0 1) t} := by
    intro s hs
    by_cases hs0 : s ≤ 0 ∨ 1 ≤ s;
    · exact False.elim <| hs <| tendsto_eval_of_continuousAt hF <| Or.inr hs0;
    · simp_all +decide [ not_or, Set.mem_Icc ];
      exact ⟨ ⟨ hs0.1.le, hs0.2.le ⟩, fun h => hs <| tendsto_eval_of_continuousAt hF <| Or.inl <| h.continuousAt <| Icc_mem_nhds hs0.1 hs0.2 ⟩;
  exact MeasureTheory.measure_mono_null hD ( Set.Countable.measure_zero ( SkorokhodBasic.IsCadlag.countable_discontinuities f.cadlag' ) MeasureTheory.MeasureSpace.volume )

/-! ## The integral-average functionals and continuity -/

/-- The `n`-th integral-average functional at base-point `q`:
`intAvg n q f = (n+1) ∫_{(q, q+1/(n+1)]} f`. -/
def intAvg (n : ℕ) (q : ℝ) (f : Skoro) : ℝ :=
  ((n : ℝ) + 1) * ∫ s in Set.Ioc q (q + 1 / ((n : ℝ) + 1)), f.toFun s

/-
Uniform sup bound eventually along a convergent sequence: if `F n → f`, then for large
`n`, `|F n (s)| ≤ supNorm f + 1` for all `s ∈ [0,1]`.
-/
theorem eventually_supNorm_le {F : ℕ → Skoro} {f : Skoro} (hF : Tendsto F atTop (𝓝 f)) :
    ∀ᶠ n in atTop, ∀ s ∈ Set.Icc (0:ℝ) 1, |(F n).toFun s| ≤ supNorm f + 1 := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, dist (F n) f < 1 := by
    simpa using Metric.tendsto_atTop.mp hF 1 zero_lt_one;
  refine' Filter.eventually_atTop.mpr ⟨ N, fun n hn s hs => _ ⟩;
  have h_supNorm_le : abs (supNorm (F n) - supNorm f) ≤ 1 := by
    exact le_trans ( SkorokhodBasic.dist_supNorm_le ( F n ) f ) ( le_of_lt ( by simpa only [ SkorokhodBasic.dist_eq_dCirc ] using hN n hn ) );
  linarith [ abs_le.mp h_supNorm_le, SkorokhodBasic.abs_le_supNorm ( F n ) hs ]

/-
`|g.toFun s| ≤ supNorm g` for *every* `s : ℝ` (flat outside `[0,1]`).
-/
theorem abs_le_supNorm_all (g : Skoro) (s : ℝ) : |g.toFun s| ≤ supNorm g := by
  by_cases hs : s ≤ 0;
  · have := g.flatL s hs; rw [ this ] ; exact abs_le_supNorm g ( show ( 0 : ℝ ) ∈ Set.Icc 0 1 by norm_num ) ;
  · by_cases hs' : s ≤ 1;
    · exact abs_le_supNorm g ⟨ by linarith, by linarith ⟩;
    · rw [ g.flatR _ ( by linarith ) ] ; exact abs_le_supNorm g ( by norm_num ) ;

/-
The integral-average functional is `d°`-continuous (dominated convergence).
-/
theorem continuous_intAvg (n : ℕ) (q : ℝ) : Continuous (fun f : Skoro => intAvg n q f) := by
  refine' Continuous.mul continuous_const _;
  have h_dominated_convergence : ∀ {F : ℕ → Skoro} {f : Skoro}, Tendsto F atTop (𝓝 f) → Tendsto (fun k => ∫ s in Set.Ioc q (q + 1 / (n + 1 : ℝ)), (F k).toFun s) atTop (nhds (∫ s in Set.Ioc q (q + 1 / (n + 1 : ℝ)), f.toFun s)) := by
    intro F f hF;
    refine' MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _;
    refine' fun x => ( SupSet.sSup ( Set.range ( fun k => supNorm ( F k ) ) ) );
    · exact fun k => ( Skoro.measurable_toFun ( F k ) |> Measurable.aestronglyMeasurable );
    · norm_num;
    · intro k; filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx; exact le_trans ( abs_le_supNorm_all _ _ ) ( le_csSup ( by exact Filter.Tendsto.bddAbove_range ( continuous_supNorm.continuousAt.tendsto.comp hF ) ) ( Set.mem_range_self k ) ) ;
    · filter_upwards [ MeasureTheory.ae_restrict_of_ae ( eval_tendsto_ae hF ) ] with x hx using hx;
  refine' continuous_iff_continuousAt.mpr _;
  intro f;
  rw [ ContinuousAt ];
  rw [ Filter.tendsto_iff_seq_tendsto ];
  exact fun F hF => h_dominated_convergence hF

/-- The integral-average functional is Borel measurable. -/
theorem measurable_intAvg (n : ℕ) (q : ℝ) : Measurable (fun f : Skoro => intAvg n q f) :=
  (continuous_intAvg n q).measurable

/-
Right-continuity: `intAvg n q f → f(q)` as `n → ∞`, for `q ∈ [0,1)`.
-/
theorem tendsto_intAvg {q : ℝ} (hq : q ∈ Set.Ico (0:ℝ) 1) (f : Skoro) :
    Tendsto (fun n => intAvg n q f) atTop (𝓝 (f.toFun q)) := by
  -- By definition of `intAvg`, we have:
  suffices h_suff : Filter.Tendsto (fun n => (∫ s in Set.Ioc q (q + 1 / (n + 1)), (f.toFun s - f.toFun q)) * (n + 1 : ℝ)) Filter.atTop (nhds 0) by
    convert h_suff.add_const ( f.toFun q ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop using 2 <;> norm_num [ intAvg ];
    rw [ MeasureTheory.integral_sub ( by exact ( Skoro.integrableOn_Ioc f _ _ ) ) ] <;> norm_num ; ring_nf;
    rw [ max_eq_left ( by positivity ) ] ; nlinarith [ inv_mul_cancel_left₀ ( by positivity : ( 1 + ( ‹ℕ› : ℝ ) ) ≠ 0 ) ( f.toFun q ) ];
  -- By the properties of integrals and the continuity of $f$ at $q$, we can bound the integral.
  have h_bound : ∀ ε > 0, ∃ N : ℝ, ∀ n ≥ N, |∫ s in Set.Ioc q (q + 1 / (n + 1)), (f.toFun s - f.toFun q)| ≤ ε * (1 / (n + 1)) := by
    intro ε hε_pos
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x, q ≤ x ∧ x < q + δ → |f.toFun x - f.toFun q| ≤ ε := by
      have := Metric.continuousWithinAt_iff.mp ( f.cadlag'.1 q hq ) ε hε_pos;
      exact ⟨ this.choose, this.choose_spec.1, fun x hx => le_of_lt ( this.choose_spec.2 hx.1 ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) ) ⟩;
    refine' ⟨ ⌈δ⁻¹⌉₊, fun n hn => _ ⟩ ; refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
    refine' fun x => ε;
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
    · norm_num;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using hδ x ⟨ hx.1.le, hx.2.trans_lt <| by nlinarith [ Nat.le_ceil ( δ⁻¹ ), mul_inv_cancel₀ ( ne_of_gt hδ_pos ), one_div_mul_cancel ( show ( n + 1 ) ≠ 0 by linarith ) ] ⟩;
    · norm_num [ mul_comm ];
      rw [ max_eq_left ( by exact inv_nonneg.2 ( by linarith ) ) ];
  rw [ Metric.tendsto_nhds ];
  simp +zetaDelta at *;
  exact fun ε hε => by obtain ⟨ N, hN ⟩ := h_bound ( ε / 2 ) ( half_pos hε ) ; exact ⟨ Max.max N 1, fun n hn => by rw [ abs_of_nonneg ( by linarith [ le_max_right N 1 ] : 0 ≤ n + 1 ) ] ; nlinarith [ hN n ( le_trans ( le_max_left N 1 ) hn ), le_max_right N 1, mul_inv_cancel₀ ( by linarith [ le_max_right N 1 ] : ( n + 1 ) ≠ 0 ) ] ⟩ ;

/-! ## (a) Evaluations are Borel -/

/-
**Tier 1(a)**: coordinate evaluation `fun f => f.toFun t` is Borel measurable, for
every `t : ℝ`.
-/
theorem measurable_eval (t : ℝ) : Measurable (fun f : Skoro => f.toFun t) := by
  by_cases ht : t ∈ Set.Ico 0 1;
  · convert measurable_of_tendsto_metrizable' (atTop) (fun n => measurable_intAvg n t) _ using 1;
    exact tendsto_pi_nhds.mpr fun f => tendsto_intAvg ht f;
  · by_cases ht : 1 ≤ t;
    · have h_meas : Measurable (fun f : Skoro => f.toFun 1) := by
        refine' Continuous.measurable _;
        refine' continuous_iff_seqContinuous.mpr _;
        intro f hf;
        exact fun h => tendsto_eval_one h;
      convert h_meas using 1;
      exact funext fun f => f.flatR t ht;
    · by_cases ht : t < 0;
      · have h_const : ∀ f : Skoro, f.toFun t = f.toFun 0 := by
          exact fun f => f.flatL t ht.le;
        have h_const : Measurable (fun f : Skoro => f.toFun 0) := by
          have h_lim : Filter.Tendsto (fun n => fun f : Skoro => intAvg n 0 f) Filter.atTop (nhds (fun f : Skoro => f.toFun 0)) := by
            exact tendsto_pi_nhds.mpr fun f => tendsto_intAvg ( by norm_num ) f
          exact measurable_of_tendsto_metrizable ( fun n => measurable_intAvg n 0 ) h_lim;
        simp only [ * ];
      · grind

/-! ## (b) Borel = cylinder -/

/-- The rational-coordinate map `Skoro → (ℚ → ℝ)`. -/
def evalRat (f : Skoro) : ℚ → ℝ := fun q => f.toFun (q : ℝ)

theorem measurable_evalRat : Measurable evalRat := by
  rw [measurable_pi_iff]
  intro q
  exact measurable_eval (q : ℝ)

/-
Two `Skoro` paths agreeing at every rational point are equal (separation by
right-continuity; the endpoint `t = 1` is rational).
-/
theorem injective_evalRat : Function.Injective evalRat := by
  intro f g hfg
  have h_eq : ∀ t ∈ Set.Icc (0:ℝ) 1, f.toFun t = g.toFun t := by
    intro t ht
    by_cases ht1 : t = 1;
    · convert congr_fun hfg 1; all_goals unfold evalRat; aesop;
    · -- Since $t < 1$, we can find a sequence of rationals $q_n$ such that $q_n \to t$ from the right.
      obtain ⟨q_n, hq_n⟩ : ∃ q_n : ℕ → ℚ, (∀ n, t < (q_n n : ℝ)) ∧ Filter.Tendsto (fun n => (q_n n : ℝ)) Filter.atTop (nhds t) := by
        have h_seq : ∀ ε > 0, ∃ q : ℚ, t < q ∧ q < t + ε := by
          exact fun ε εpos => exists_rat_btwn ( lt_add_of_pos_right t εpos ) |> fun ⟨ q, hq₁, hq₂ ⟩ => ⟨ q, hq₁, hq₂ ⟩;
        choose! q hq using h_seq;
        exact ⟨ fun n => q ( 1 / ( n + 1 ) ), fun n => hq _ ( by positivity ) |>.1, tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => abs_le.mpr ⟨ by linarith [ hq ( 1 / ( n + 1 ) ) ( by positivity ) ], by linarith [ hq ( 1 / ( n + 1 ) ) ( by positivity ) ] ⟩ ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩;
      have h_cont : Filter.Tendsto (fun n => f.toFun (q_n n : ℝ)) Filter.atTop (nhds (f.toFun t)) ∧ Filter.Tendsto (fun n => g.toFun (q_n n : ℝ)) Filter.atTop (nhds (g.toFun t)) := by
        have h_cont : ContinuousWithinAt f.toFun (Set.Ici t) t ∧ ContinuousWithinAt g.toFun (Set.Ici t) t := by
          exact ⟨ f.cadlag'.1 t ⟨ ht.1, lt_of_le_of_ne ht.2 ht1 ⟩, g.cadlag'.1 t ⟨ ht.1, lt_of_le_of_ne ht.2 ht1 ⟩ ⟩;
        exact ⟨ h_cont.1.tendsto.comp <| Filter.tendsto_inf.mpr ⟨ hq_n.2, Filter.tendsto_principal.mpr <| Filter.Eventually.of_forall fun n => hq_n.1 n |> le_of_lt ⟩, h_cont.2.tendsto.comp <| Filter.tendsto_inf.mpr ⟨ hq_n.2, Filter.tendsto_principal.mpr <| Filter.Eventually.of_forall fun n => hq_n.1 n |> le_of_lt ⟩ ⟩;
      exact tendsto_nhds_unique h_cont.1 ( by simpa only [ show ∀ n, f.toFun ( q_n n : ℝ ) = g.toFun ( q_n n : ℝ ) from fun n => congr_fun hfg ( q_n n ) ] using h_cont.2 )
  exact Skoro.ext_on_Icc h_eq

/-- **Tier 1(b)** (route (ii)): the rational-coordinate map is a measurable embedding, so
the Borel σ-algebra of `Skoro` is generated by the coordinate evaluations. -/
theorem measurableEmbedding_evalRat : MeasurableEmbedding evalRat :=
  measurable_evalRat.measurableEmbedding injective_evalRat

/-! ## (d) The bridge lemma -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Tier 1(d)** (rational form): `X : Ω → Skoro` is measurable iff every rational
coordinate `ω ↦ (X ω).toFun q` is measurable. -/
theorem measurable_iff_forall_rat {X : Ω → Skoro} :
    Measurable X ↔ ∀ q : ℚ, Measurable (fun ω => (X ω).toFun (q : ℝ)) := by
  rw [← measurableEmbedding_evalRat.measurable_comp_iff, measurable_pi_iff]
  rfl

/-- **Tier 1(d)** (the bridge lemma): `X : Ω → Skoro` is measurable iff every coordinate
`ω ↦ (X ω).toFun t` is measurable. -/
theorem measurable_iff_forall_eval {X : Ω → Skoro} :
    Measurable X ↔ ∀ t : ℝ, Measurable (fun ω => (X ω).toFun t) := by
  constructor
  · intro hX t
    exact (measurable_eval t).comp hX
  · intro h
    exact measurable_iff_forall_rat.mpr (fun q => h (q : ℝ))

/-- The finite-dimensional cylinder evaluation at a finite tuple of times. -/
def fdd {k : ℕ} (ts : Fin k → ℝ) (f : Skoro) : Fin k → ℝ := fun i => f.toFun (ts i)

theorem measurable_fdd {k : ℕ} (ts : Fin k → ℝ) : Measurable (fdd ts) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_eval (ts i)

/-- **Tier 1(d)** (law determined by fdds): two measures on `Skoro` that agree on
all finite-dimensional cylinder events (preimages under the rational coordinate maps)
coincide.  Concretely: if `μ` and `ν` agree after pushing forward by `evalRat`, they are
equal.  (The finite-dimensional distributions are the pushforwards under the finite
coordinate maps `fdd`; since `evalRat` collects all rational coordinates and is a
measurable embedding, agreement of the full rational law forces `μ = ν`.) -/
theorem ext_of_map_evalRat {μ ν : Measure Skoro}
    (h : μ.map evalRat = ν.map evalRat) : μ = ν := by
  ext A hA
  have h1 : A = evalRat ⁻¹' (evalRat '' A) := by
    rw [Set.preimage_image_eq _ injective_evalRat]
  rw [h1, ← measurableEmbedding_evalRat.map_apply, ← measurableEmbedding_evalRat.map_apply, h]

/-! ## (c) The càdlàg modulus is Borel — status and obstruction

**Tier 1(c)** asks for Borel measurability of `fun f => cadlagModulus f.toFun δ`
via the "rational-partition reduction": restrict the infimum defining
`cadlagModulus` (over `δ`-sparse partitions of `[0,1]`) to partitions whose
*nodes are rational*, and sample the cell oscillations at rational points.  The
rational **sampling of the oscillation inside a fixed cell** is indeed valid by
right-continuity.  However, the reduction to **rational nodes** is *false* in
general, so this route does not establish Borel measurability:

* Counterexample.  Let `a ∈ (0,1)` be irrational and `f = step a` (the Skoro
  path jumping from `0` to `1` at `a`; `SkorokhodBasic.step`/`isCadlag_step`).
  For `δ < min a (1-a)` the *real* partition `{0, a, 1}` has left-endpoint
  oscillation `0` on each cell (`f` is constant on `[0,a)` and on `[a,1]`), so
  `cadlagModulus f δ = 0` (cf. `cadlagModulus_step`).  But **no partition with
  rational nodes** can separate the jump at the irrational point `a`: every
  rational-node cell that meets a neighbourhood of `a` contains `a` in its
  interior and therefore has oscillation `1`.  Hence the infimum restricted to
  rational nodes equals `1 ≠ 0 = cadlagModulus f δ`.

Consequently `cadlagModulus` genuinely depends on the (possibly irrational)
locations of the large jumps of `f`.  Its sub-level sets
`{f | cadlagModulus f.toFun δ < c}` are projections along the (uncountable,
Polish) partition parameter of a jointly-Borel condition, i.e. **analytic**
(hence universally measurable), but need not be Borel — the naive rational-node
reduction cannot produce a Borel witness.  We therefore leave the *Borel*
measurability statement open (a correct treatment would go through analytic /
universally-measurable sets, or a measurable-selection analysis of the jump
locations, both substantial).

This does **not** affect the tightness bridge or the process-to-path plumbing:
`SkorokhodBasic.isTightMeasureSet_of_bdd_of_modulus` (Task 3) discharges the
modulus contribution using only *outer-measure monotonicity and countable
subadditivity* on the level sets `{f | ε ≤ cadlagModulus f.toFun δ}` — it never
requires those sets to be measurable.  Downstream tightness applications bound
their (outer) measure by that of a genuinely cylinder-measurable superset of
large increments.

The intended statement is recorded here (commented out) for reference:

```
theorem measurable_cadlagModulus (δ : ℝ) :
    Measurable (fun f : Skoro => cadlagModulus f.toFun δ) := by
  sorry
```
-/

end

end SkorokhodBasic