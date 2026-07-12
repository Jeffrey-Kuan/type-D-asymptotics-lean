import Mathlib
import TypeDDecouplingCrossover

/-!
# A satisfiability witness for the dual-pair model (`IsDualPairRescaling`)

The §cross crossover statements (`prop_twophase`, `prop_twophase_mixture`, `thm_cross`)
are stated *conditionally* on the hypothesis `IsDualPairRescaling μ c X`, i.e. they assert
something about the rescaled coupled dual pair only when `X` really is that object.  This
file proves that the predicate is *inhabited*: there is a concrete probability space and a
concrete family `X` satisfying `IsDualPairRescaling μ c X` for every `c > 0`.  This rules
out the degenerate possibility that the hypothesis is unsatisfiable (which would make the
conditional theorems vacuously true).

## The witness

* The increments live on the infinite product space `((ℕ ⊕ ℕ) → Bool)` with the product
  of fair `Bernoulli(1/2)` measures; the increment `eps k ω = if ω.1 k then 1 else -1` is a
  symmetric `±1` variable, and the coordinates are independent by `iIndepFun_infinitePi`.
* The split time uses one extra independent coordinate `ω.2 : ℝ` distributed as
  `Exp(4c)` (`expMeasure (4*c)`); the split jump-count is `τ T ω = ⌊(2T)·min(ω.2, 1)⌋₊`.
  Because `Exp` has no atoms on `(0,1)` and `min(·,1)` puts mass `e^{-4c}` at `1`, the
  rescaled split fraction `τ/(2T)` converges in distribution to `U = min(Exp(4c), 1)`,
  whose CDF is `minExpCDF c`.  This is proved by a squeeze on the exponential CDF.
* The whole space is the product `Ω = ((ℕ ⊕ ℕ) → Bool) × ℝ`.
-/

open scoped BigOperators Real Topology ENNReal
open MeasureTheory Filter ProbabilityTheory

namespace TypeDDecoupling

/-! ## The fair coin measure on `Bool` -/

/-- The fair `Bernoulli(1/2)` law on `Bool`, as an explicit mixture of Dirac masses. -/
noncomputable def bernBool : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance instIsProbabilityMeasure_bernBool : IsProbabilityMeasure bernBool := by
  constructor ; norm_num [ bernBool ];
  rw [ ← two_mul, ENNReal.mul_inv_cancel ] <;> norm_num

/-
The signed increment `b ↦ (if b then 1 else -1)` has mean zero under the fair coin.
-/
lemma bernBool_integral_sign :
    ∫ b, (if b then (1 : ℝ) else -1) ∂bernBool = 0 := by
  unfold bernBool;
  rw [ MeasureTheory.integral_add_measure ] <;> norm_num; all_goals rw [ MeasureTheory.integrable_smul_measure ] <;> norm_num

/-! ## The witness probability space -/

/-- The witness sample space: an infinite stream of `±1` coins (indexed by `ℕ ⊕ ℕ`)
together with one real coordinate driving the random split time. -/
abbrev WitOmega : Type := ((ℕ ⊕ ℕ) → Bool) × ℝ

/-- The witness measure: the product of the fair-coin product measure with `Exp(4c)`. -/
noncomputable def witMeasure (c : ℝ) : Measure WitOmega :=
  (Measure.infinitePi (fun _ : ℕ ⊕ ℕ => bernBool)).prod (expMeasure (4 * c))

lemma isProbabilityMeasure_witMeasure {c : ℝ} (hc : 0 < c) :
    IsProbabilityMeasure (witMeasure c) := by
  haveI : IsProbabilityMeasure (expMeasure (4 * c)) :=
    isProbabilityMeasure_expMeasure (by linarith)
  unfold witMeasure
  infer_instance

/-- The witness increments: the `k`-th coin read off as `±1`. -/
noncomputable def witEps : (ℕ ⊕ ℕ) → WitOmega → ℝ :=
  fun k ω => if ω.1 k then 1 else -1

/-- The witness split jump-count `τ T ω = ⌊(2T)·min(ω.2, 1)⌋₊`. -/
noncomputable def witTau : ℝ → WitOmega → ℕ :=
  fun T ω => ⌊(2 * T) * min ω.2 1⌋₊

/-- The witness rescaled dual pair. -/
noncomputable def witX : ℝ → WitOmega → ℝ × ℝ :=
  fun T ω => (dualWalkFst witEps T ω, dualWalkSnd witEps (witTau T ω) T ω)

/-! ## Independence of an infinite family pulled back along `Prod.fst` -/

/-
If a family of random variables on `Ω₁` is independent, then pulling each one back
along the first projection keeps it independent for the product measure (with a
probability measure on the second factor).
-/
lemma iIndepFun_comp_fst {ι Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ₁ : Measure Ω₁} [IsProbabilityMeasure μ₁]
    {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₂]
    {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)]
    {f : (i : ι) → Ω₁ → 𝓧 i} (h : iIndepFun f μ₁) :
    iIndepFun (fun i (ω : Ω₁ × Ω₂) => f i ω.1) (μ₁.prod μ₂) := by
  unfold iIndepFun at *;
  rw [ Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul ] at *;
  intro S sets hsets; specialize h S hsets; simp_all +decide [ Set.preimage ] ;
  convert congr_arg ( fun x : ENNReal => x * μ₂ Set.univ ) h using 1;
  · convert MeasureTheory.Measure.prod_prod _ _ using 2;
    · ext ⟨x, y⟩; simp [Set.mem_iInter, Set.mem_prod];
    · infer_instance;
  · simp +decide;
    refine' Finset.prod_congr rfl fun i hi => _;
    erw [ show { x : Ω₁ × Ω₂ | f i x.1 ∈ sets i } = ( { x : Ω₁ | f i x ∈ sets i } ×ˢ Set.univ ) by ext ; aesop, MeasureTheory.Measure.prod_prod ] ; aesop

/-
Independence of the witness increments.
-/
lemma iIndepFun_witEps {c : ℝ} (hc : 0 < c) :
    iIndepFun witEps (witMeasure c) := by
  have := @ProbabilityTheory.iIndepFun_infinitePi;
  convert @this ( ℕ ⊕ ℕ ) ( fun _ => ℝ ) ( fun _ => inferInstance ) ( fun _ => Bool ) ( fun _ => inferInstance ) ( fun _ => bernBool ) _ ( fun _ => fun b => if b then ( 1 : ℝ ) else -1 ) _ using 1;
  · constructor;
    · intro h;
      convert @this ( ℕ ⊕ ℕ ) ( fun _ => ℝ ) ( fun _ => inferInstance ) ( fun _ => Bool ) ( fun _ => inferInstance ) ( fun _ => bernBool ) _ ( fun _ => fun b => if b then ( 1 : ℝ ) else -1 ) _ using 1;
      exact fun _ => Measurable.ite ( MeasurableSet.singleton _ ) measurable_const measurable_const;
    · intro h;
      convert iIndepFun_comp_fst h using 1;
      · exact isProbabilityMeasure_expMeasure ( by linarith );
  · exact fun i => Measurable.ite ( MeasurableSet.singleton true ) measurable_const measurable_const

/-
Each witness increment is a symmetric `±1` increment.
-/
lemma symmetricPMOneIncrement_witEps {c : ℝ} (hc : 0 < c) (k : ℕ ⊕ ℕ) :
    SymmetricPMOneIncrement (witMeasure c) (witEps k) := by
  constructor;
  · exact Measurable.ite ( measurableSet_eq_fun ( measurable_pi_apply k |> Measurable.comp <| measurable_fst ) measurable_const ) measurable_const measurable_const;
  · refine' ⟨ fun ω => by unfold witEps; split_ifs <;> norm_num, _ ⟩;
    -- The integral of the increment function over the first component is zero because each increment is symmetric ±1.
    have h_integral_first : ∫ ω₁ : (ℕ ⊕ ℕ) → Bool, (if ω₁ k then (1 : ℝ) else -1) ∂(Measure.infinitePi (fun _ => bernBool)) = 0 := by
      have h_integral_first : ∫ ω₁ : (ℕ ⊕ ℕ) → Bool, (if ω₁ k then (1 : ℝ) else -1) ∂(Measure.infinitePi (fun _ => bernBool)) = ∫ ω₁ : Bool, (if ω₁ then (1 : ℝ) else -1) ∂bernBool := by
        have h_integral_first : ∫ ω₁ : (ℕ ⊕ ℕ) → Bool, (if ω₁ k then (1 : ℝ) else -1) ∂(Measure.infinitePi (fun _ => bernBool)) = ∫ ω₁ : Bool, (if ω₁ then (1 : ℝ) else -1) ∂(Measure.map (fun ω₁ => ω₁ k) (Measure.infinitePi (fun _ => bernBool))) := by
          rw [ MeasureTheory.integral_map ];
          · exact measurable_pi_apply k |> Measurable.aemeasurable;
          · exact Measurable.aestronglyMeasurable ( by exact Measurable.ite ( MeasurableSet.singleton _ ) measurable_const measurable_const );
        rw [ h_integral_first, MeasureTheory.Measure.infinitePi_map_eval ];
      convert bernBool_integral_sign using 1;
    convert congr_arg ( fun x : ℝ => x * ∫ ω₂ : ℝ, 1 ∂expMeasure ( 4 * c ) ) h_integral_first using 1;
    · convert MeasureTheory.integral_prod_mul _ _ using 1;
      · unfold witEps witMeasure; norm_num;
      · have := isProbabilityMeasure_expMeasure ( by linarith : 0 < 4 * c );
        infer_instance;
      · infer_instance;
    · ring

/-! ## Convergence of the split fraction -/

/-
The `Exp(4c)` CDF in closed form (combining `cdf_eq_real` and `cdf_expMeasure_eq`).
-/
lemma expMeasure_Iic_toReal {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ((expMeasure (4 * c)) (Set.Iic y)).toReal
      = if 0 ≤ y then 1 - Real.exp (-(4 * c * y)) else 0 := by
  convert cdf_expMeasure_eq ( show 0 < 4 * c by linarith ) y using 1;
  convert cdf_eq_real ( expMeasure ( 4 * c ) ) y |> Eq.symm using 1;
  exact isProbabilityMeasure_expMeasure ( by linarith )

/-
For `x < 0` and `T > 0` the split-fraction event is empty.
-/
lemma witTau_set_empty {x : ℝ} (hx : x < 0) {T : ℝ} (hT : 0 < T) :
    {e : ℝ | (⌊(2 * T) * min e 1⌋₊ : ℝ) ≤ x * (2 * T)} = ∅ := by
  exact Set.eq_empty_of_forall_notMem fun e he => by nlinarith [ he.out, Nat.lt_floor_add_one ( 2 * T * Min.min e 1 ) ] ;

/-
For `1 ≤ x` and `T > 0` the split-fraction event is everything.
-/
lemma witTau_set_univ {x : ℝ} (hx : 1 ≤ x) {T : ℝ} (hT : 0 < T) :
    {e : ℝ | (⌊(2 * T) * min e 1⌋₊ : ℝ) ≤ x * (2 * T)} = Set.univ := by
  ext e; exact (by
  by_cases h : 0 ≤ 2 * T * min e 1;
  · exact iff_of_true ( by exact le_trans ( Nat.floor_le h ) ( by nlinarith [ min_le_right e 1 ] ) ) trivial;
  · norm_num [ Nat.floor_of_nonpos ( le_of_not_ge h ) ] ; nlinarith)

/-
Lower inclusion for the squeeze: `{e ≤ x} ⊆` the split event (`0 ≤ x < 1`, `T > 0`).
-/
lemma witTau_set_lower {x : ℝ} (hx0 : 0 ≤ x) {T : ℝ} (hT : 0 < T) :
    Set.Iic x ⊆ {e : ℝ | (⌊(2 * T) * min e 1⌋₊ : ℝ) ≤ x * (2 * T)} := by
  intro e he;
  cases le_or_gt 0 ( 2 * T * min e 1 ) <;> simp_all +decide [ mul_comm, mul_left_comm ];
  · exact le_trans ( Nat.floor_le ( by positivity ) ) ( by nlinarith [ min_le_left e 1, min_le_right e 1 ] );
  · rw [ Nat.floor_of_nonpos ( by linarith ) ] ; norm_num ; positivity

/-
Upper inclusion for the squeeze: the split event `⊆ {e ≤ x + 1/(2T)}`
(`0 ≤ x < 1`, and `T` large enough that `x + 1/(2T) < 1`).
-/
lemma witTau_set_upper {x : ℝ} (hx1 : x < 1) {T : ℝ}
    (hT : 1 / (2 * (1 - x)) < T) :
    {e : ℝ | (⌊(2 * T) * min e 1⌋₊ : ℝ) ≤ x * (2 * T)} ⊆ Set.Iic (x + 1 / (2 * T)) := by
  -- Let's take any $e$ in the set and show that $e \leq x + \frac{1}{2T}$.
  intro e he
  by_cases h : e ≤ 1;
  · rw [ Set.mem_Iic, add_div', le_div_iff₀ ] <;> nlinarith [ Nat.lt_floor_add_one ( 2 * T * Min.min e 1 ), show 0 < T from lt_of_le_of_lt ( by exact div_nonneg zero_le_one ( by linarith ) ) hT, min_eq_left h, Set.mem_setOf.mp he ];
  · contrapose! he;
    norm_num [ min_eq_right ( by linarith : 1 ≤ e ) ];
    rw [ div_lt_iff₀ ] at hT <;> nlinarith [ Nat.lt_floor_add_one ( 2 * T ) ]

/-
The CDF of the rescaled split jump-count converges to `minExpCDF c`, expressed
directly on the `Exp(4c)` factor.
-/
lemma witTau_expMeasure_cdf_tendsto {c : ℝ} (hc : 0 < c) (x : ℝ) :
    Tendsto
      (fun T => ((expMeasure (4 * c))
        {e | (⌊(2 * T) * min e 1⌋₊ : ℝ) ≤ x * (2 * T)}).toReal)
      atTop (𝓝 (minExpCDF c x)) := by
  unfold minExpCDF;
  split_ifs;
  · refine' tendsto_const_nhds.congr' _;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT using by rw [ witTau_set_empty ‹_› hT ] ; norm_num;
  · refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' _ _ _ _;
    use fun T => 1 - Real.exp ( - ( 4 * c * x ) );
    use fun T => 1 - Real.exp ( - ( 4 * c * ( x + 1 / ( 2 * T ) ) ) );
    · exact tendsto_const_nhds;
    · exact le_trans ( tendsto_const_nhds.sub <| Real.continuous_exp.continuousAt.tendsto.comp <| Filter.Tendsto.neg <| tendsto_const_nhds.mul <| tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <| Filter.tendsto_id.const_mul_atTop zero_lt_two ) <| by norm_num;
    · refine' Filter.eventually_atTop.mpr ⟨ 1, fun T hT => _ ⟩;
      have h_lower : (expMeasure (4 * c)) (Set.Iic x) ≤ (expMeasure (4 * c)) {e : ℝ | (⌊(2 * T) * min e 1⌋₊ : ℝ) ≤ x * (2 * T)} := by
        refine' MeasureTheory.measure_mono _;
        exact witTau_set_lower ( by linarith ) ( by linarith );
      convert ENNReal.toReal_mono _ h_lower using 1;
      · rw [ expMeasure_Iic_toReal ] <;> aesop;
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide [ isProbabilityMeasure_expMeasure ( show 0 < 4 * c by positivity ) ] ) );
    · filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( 1 / ( 2 * ( 1 - x ) ) ) ] with T hT₁ hT₂;
      refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| witTau_set_upper _ hT₂ ) _;
      · exact ne_of_lt ( isProbabilityMeasure_expMeasure ( by linarith ) |> fun h => h.measure_univ ▸ MeasureTheory.measure_mono ( Set.subset_univ _ ) |> lt_of_le_of_lt <| ENNReal.one_lt_top );
      · linarith;
      · rw [ expMeasure_Iic_toReal ] <;> norm_num;
        · rw [ if_pos ( by linarith [ inv_pos.2 hT₁ ] ) ];
        · linarith;
  · refine' tendsto_const_nhds.congr' _;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT;
    rw [ witTau_set_univ ( by linarith ) hT ] ; norm_num [ isProbabilityMeasure_expMeasure ( by linarith : 0 < 4 * c ) ]

/-
The witness split fraction converges in distribution to `U = min(Exp(4c), 1)`.
-/
lemma witTau_cdf_tendsto {c : ℝ} (hc : 0 < c) (x : ℝ) :
    Tendsto (fun T => ((witMeasure c) {ω | (witTau T ω : ℝ) ≤ x * (2 * T)}).toReal)
      atTop (𝓝 (minExpCDF c x)) := by
  refine' Filter.Tendsto.congr' _ ( witTau_expMeasure_cdf_tendsto hc x );
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT;
  convert rfl using 2;
  convert MeasureTheory.Measure.prod_apply _;
  · unfold witTau; aesop;
  · have := isProbabilityMeasure_expMeasure ( by linarith : 0 < 4 * c );
    infer_instance;
  · refine' measurableSet_le _ _;
    · refine' Measurable.comp ( by measurability ) _;
      exact Measurable.nat_floor ( measurable_const.mul ( measurable_snd.min measurable_const ) );
    · exact measurable_const

/-! ## The main satisfiability statement -/

/-- The concrete witness satisfies `IsDualPairRescaling`. -/
theorem isDualPairRescaling_witMeasure {c : ℝ} (hc : 0 < c) :
    IsDualPairRescaling (witMeasure c) c witX := by
  refine ⟨witEps, witTau, symmetricPMOneIncrement_witEps hc, iIndepFun_witEps hc,
    witTau_cdf_tendsto hc, ?_⟩
  intro T ω
  rfl

/-- **Satisfiability of the dual-pair model.**  For every `c > 0` there is a concrete
probability space `Ω` with measure `μ` and a family `X : ℝ → Ω → ℝ × ℝ` satisfying
`IsDualPairRescaling μ c X`.  Hence the predicate is inhabited and the conditional
crossover theorems are not vacuous. -/
theorem exists_isDualPairRescaling {c : ℝ} (hc : 0 < c) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : ℝ → Ω → ℝ × ℝ),
      IsDualPairRescaling μ c X :=
  ⟨WitOmega, inferInstance, witMeasure c, witX, isDualPairRescaling_witMeasure hc⟩

end TypeDDecoupling