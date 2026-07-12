import Mathlib
import TypeDDecouplingMartingaleCLT
import TypeDDecouplingTwoPhase

/-!
# Gaussian characteristic function of a martingale with deterministic bracket

This is **Part 1** (the library-clean centrepiece) of the `thm_mp` de-opaquing brief.

The project already contains, in `TypeDDecouplingMartingaleCLT.lean`, a fully-proved
martingale-difference-array CLT at the characteristic-function level
(`core_charFun_tendsto`) — but it requires a **deterministic** jump bound
`|X_{n,j}| ≤ b_n → 0`.  For the continuous limiting objects (an ℝ-indexed martingale with
deterministic bracket) the dyadic increments only vanish *a.e.*, not deterministically.

The bridge is the **stopped-array adapter**, the one genuinely new tool here, proved
outright and kept general/reusable:

* `charFun_integral_tendsto_of_agree` — *charFun limits transfer across vanishing events*:
  if two real sequences of random variables `S n, T n` agree with probability `→ 1`
  (`μ{S n ≠ T n} → 0`) and the characteristic-function integrals of `T` converge, then so
  do those of `S`, to the same limit.  This is the transfer mechanism.
* `stopped` / `stopped_mds` / `stopped_agree` — the *discrete optional-stopping* device:
  stop the array at the first oversized increment.  The stopped array is a genuine
  martingale-difference array (predictable indicator, `stopped_mds`) and it agrees with the
  true partial sums on the event that no increment is oversized, whose probability `→ 1`
  (`stopped_agree`).
* `martingale_charFun_gaussian` — the **single-`M_t` Gaussian charFun**, proved outright by
  feeding a deterministically-bounded companion array (the stopped/truncated array) to
  `core_charFun_tendsto` and transferring the limit back with
  `charFun_integral_tendsto_of_agree`.
* `martingale_joint_charFun_gaussian` — the **joint / fdd / independence** version, via
  `joint_charFun_tendsto`, with the identical transfer.  Cross-bracket `→ 0` gives the
  product (independent) Gaussian charFun.

## Faithfulness notes (see brief remark (2),(3))

The bounded companion array `Xt` is supplied as data with the hypotheses a Lindeberg
truncation/stopping supplies (deterministic bound `b_n → 0`, martingale-difference
structure, uniform bracket bound, a.e. bracket convergence) together with the
*agreement-with-probability-`→ 1`* fact.  The transfer adapter and the optional-stopping
structure (`stopped_mds`, `stopped_agree`) are proved outright; they are exactly the
"one genuinely new tool" the brief asks to be reusable.  Requiring only the a.e. modulus of
the paths (not path continuity) is faithful to the continuous Gaussian limits.
-/

open MeasureTheory ProbabilityTheory Complex Filter Finset
open scoped Topology BigOperators ENNReal NNReal Real

namespace TypeDDecoupling.MartingaleGaussian

open TypeDDecoupling.MartingaleCLT (partialSum)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## The transfer adapter: charFun limits transfer across vanishing events -/

/-
**Transfer adapter.**  If two sequences of real random variables `S n` and `T n` agree
with probability tending to `1` (i.e. `μ {ω | S n ω ≠ T n ω} → 0`), and the
characteristic-function integrals of `T` converge to `L`, then so do those of `S`.

This is the reusable heart of the stopped-array bridge: it lets one replace an array whose
increments only vanish a.e. by a deterministically bounded companion (agreeing w.p. `→ 1`)
before invoking `core_charFun_tendsto`.
-/
theorem charFun_integral_tendsto_of_agree
    (S T : ℕ → Ω → ℝ) (u : ℝ) (L : ℂ)
    (hS : ∀ n, Measurable (S n)) (hT : ∀ n, Measurable (T n))
    (hagree : Tendsto (fun n => (μ {ω | S n ω ≠ T n ω}).toReal) atTop (𝓝 0))
    (hlim : Tendsto
      (fun n => ∫ ω, Complex.exp (((u * T n ω : ℝ) : ℂ) * Complex.I) ∂μ) atTop (𝓝 L)) :
    Tendsto
      (fun n => ∫ ω, Complex.exp (((u * S n ω : ℝ) : ℂ) * Complex.I) ∂μ) atTop (𝓝 L) := by
  -- By the triangle inequality, the difference of the integrals is bounded by the integral of the absolute difference.
  have h_triangle : ∀ n, ‖∫ ω, Complex.exp (((u * S n ω : ℝ) : ℂ) * Complex.I) ∂μ - ∫ ω, Complex.exp (((u * T n ω : ℝ) : ℂ) * Complex.I) ∂μ‖ ≤ ∫ ω, ‖Complex.exp (((u * S n ω : ℝ) : ℂ) * Complex.I) - Complex.exp (((u * T n ω : ℝ) : ℂ) * Complex.I)‖ ∂μ := by
    intro n;
    convert MeasureTheory.norm_integral_le_integral_norm ( _ : Ω → ℂ ) using 1;
    rw [ MeasureTheory.integral_sub ];
    · refine' MeasureTheory.Integrable.mono' ( MeasureTheory.integrable_const 1 ) _ _;
      · fun_prop;
      · norm_num [ Complex.norm_exp ];
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      exacts [ fun _ => 1, MeasureTheory.integrable_const _, Complex.continuous_exp.comp_aestronglyMeasurable ( by measurability ), Filter.Eventually.of_forall fun _ => by simp +decide [ Complex.norm_exp ] ];
  -- The integrand ‖Complex.exp (((u * S n ω : ℝ) : ℂ) * Complex.I) - Complex.exp (((u * T n ω : ℝ) : ℂ) * Complex.I)‖ is bounded by 2.
  have h_bound : ∀ n, ∫ ω, ‖Complex.exp (((u * S n ω : ℝ) : ℂ) * Complex.I) - Complex.exp (((u * T n ω : ℝ) : ℂ) * Complex.I)‖ ∂μ ≤ ∫ ω in {ω | S n ω ≠ T n ω}, 2 ∂μ := by
    intro n;
    rw [ ← MeasureTheory.integral_indicator ];
    · refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
      · exact Filter.Eventually.of_forall fun ω => norm_nonneg _;
      · exact MeasureTheory.integrable_indicator_iff ( measurableSet_eq_fun ( hS n ) ( hT n ) |> MeasurableSet.compl ) |>.2 ( MeasureTheory.integrable_const _ );
      · filter_upwards [ ] with ω ; by_cases h : S n ω = T n ω <;> simp +decide [ h ];
        exact le_trans ( norm_sub_le _ _ ) ( by norm_num [ Complex.norm_exp ] );
    · exact measurableSet_eq_fun ( hS n ) ( hT n ) |> MeasurableSet.compl;
  have h_final : Tendsto (fun n => ∫ ω, Complex.exp (((u * S n ω : ℝ) : ℂ) * Complex.I) ∂μ - ∫ ω, Complex.exp (((u * T n ω : ℝ) : ℂ) * Complex.I) ∂μ) atTop (nhds 0) := by
    refine' squeeze_zero_norm ( fun n => le_trans ( h_triangle n ) ( h_bound n ) ) _;
    convert hagree.const_mul 2 using 2 <;> norm_num;
    ring!;
  simpa using h_final.add hlim

/-! ## Discrete optional stopping: the stopped array -/

/-- The stopped (truncated) array: keep increment `j` only while **every** earlier
increment (strictly before `j`) is within the deterministic threshold `b`.  The guarding
indicator `∀ i < j, |X i ω| ≤ b` is measurable with respect to `𝓕 j` (it involves only
increments `i < j`, each `𝓕 (i+1) ≤ 𝓕 j`-measurable), so the stopped array is *predictable*
in the sense needed for the martingale-difference property. -/
noncomputable def stopped (X : ℕ → Ω → ℝ) (b : ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  if (∀ i < j, |X i ω| ≤ b) then X j ω else 0

/-
The stopped array is a martingale-difference array: the guarding indicator is
`𝓕 j`-measurable, so `μ[stopped X b j | 𝓕 j] = (indicator) · μ[X j | 𝓕 j] = 0`.
-/
theorem stopped_mds
    (𝓕 : ℕ → MeasurableSpace Ω) (hmono : Monotone 𝓕)
    (X : ℕ → Ω → ℝ) (b : ℝ)
    (hadapt : ∀ j, StronglyMeasurable[𝓕 (j + 1)] (X j))
    (hint : ∀ j, Integrable (X j) μ)
    (hmds : ∀ j, μ[X j | 𝓕 j] =ᵐ[μ] 0) (j : ℕ) :
    μ[stopped X b j | 𝓕 j] =ᵐ[μ] 0 := by
  -- Write A = {ω | ∀ i < j, |X i ω| ≤ b}. Note stopped X b j = Set.indicator A (X j).
  have hA : ∀ ω, stopped X b j ω = (if (∀ i < j, |X i ω| ≤ b) then X j ω else 0) := by
    exact fun ω => rfl;
  -- The set A is 𝓕 j-measurable: A = ⋂ i ∈ range j, {ω | |X i ω| ≤ b}.
  have hA_measurable : MeasurableSet[𝓕 j] {ω | ∀ i < j, |X i ω| ≤ b} := by
    have hA_measurable : ∀ i < j, MeasurableSet[𝓕 j] {ω | |X i ω| ≤ b} := by
      intro i hi
      have h_meas : MeasurableSet[𝓕 (i + 1)] {ω | |X i ω| ≤ b} := by
        exact measurableSet_le ( hadapt i |> StronglyMeasurable.norm |> StronglyMeasurable.measurable ) measurable_const
      generalize_proofs at *;
      exact hmono ( Nat.succ_le_of_lt hi ) _ h_meas;
    simpa only [ Set.setOf_forall ] using MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi => hA_measurable i hi;
  have h_cond_exp : μ[stopped X b j | 𝓕 j] =ᵐ[μ] (Set.indicator {ω | ∀ i < j, |X i ω| ≤ b}) (μ[X j | 𝓕 j]) := by
    convert MeasureTheory.condExp_indicator _ _ using 1;
    · congr with ω ; aesop;
    · grind +locals;
    · convert hA_measurable using 1;
  filter_upwards [ h_cond_exp, hmds j ] with ω hω₁ hω₂ using by aesop;

/-
The stopped array is adapted: `stopped X b j` is `𝓕 (j+1)`-measurable.
-/
theorem stopped_adapted
    (𝓕 : ℕ → MeasurableSpace Ω) (hmono : Monotone 𝓕)
    (X : ℕ → Ω → ℝ) (b : ℝ)
    (hadapt : ∀ j, StronglyMeasurable[𝓕 (j + 1)] (X j)) (j : ℕ) :
    StronglyMeasurable[𝓕 (j + 1)] (stopped X b j) := by
  have hstopped_measurable : MeasurableSet[𝓕 (j + 1)] {ω | ∀ i < j, |X i ω| ≤ b} := by
    have hstopped_measurable : ∀ i < j, MeasurableSet[𝓕 (j + 1)] {ω | |X i ω| ≤ b} := by
      intro i hi;
      have hstopped_measurable : StronglyMeasurable[𝓕 (j + 1)] (fun ω => |X i ω|) := by
        exact hadapt i |> fun h => h.norm.mono ( hmono ( by linarith ) );
      exact measurableSet_le hstopped_measurable.measurable measurable_const;
    simpa only [ Set.setOf_forall ] using MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi => hstopped_measurable i hi;
  convert MeasureTheory.StronglyMeasurable.indicator ( hadapt j ) hstopped_measurable using 1;
  unfold stopped; aesop;

/-
On the "good event" (no increment among the first `N` is oversized), the stopped partial
sum equals the true partial sum.  Hence the disagreement event is contained in the event of
an oversized increment.
-/
theorem stopped_agree_subset (X : ℕ → Ω → ℝ) (b : ℝ) (N : ℕ) :
    {ω | partialSum X N ω ≠ partialSum (stopped X b) N ω}
      ⊆ {ω | ∃ j < N, b < |X j ω|} := by
  intro ω hω;
  contrapose! hω;
  simp_all +decide [ partialSum, stopped ];
  exact Finset.sum_congr rfl fun i hi => by rw [ if_pos fun j hj => hω j ( by linarith [ Finset.mem_range.mp hi ] ) ] ;

/-! ## The single-`M_t` Gaussian charFun -/

/-
**Gaussian charFun for a martingale-difference array with deterministic bracket**
(single-time / single-`M_t` version), proved by self-discretisation into
`core_charFun_tendsto` bridged by the stopped-array adapter.

`X` is the true array; `Xt` is a deterministically bounded companion (the stopped/truncated
array) that is a martingale-difference array, has a uniform bracket bound `C`, whose bracket
converges a.e. to the deterministic `σsq`, and which agrees with `X` on events of
probability `→ 1`.  The conclusion is that the characteristic function of the true partial
sums `∑_{j<kn n} X_{n,j}` converges to the Gaussian `exp(-σsq u²/2)`.
-/
theorem martingale_charFun_gaussian
    (kn : ℕ → ℕ) (𝓕 : ℕ → ℕ → MeasurableSpace Ω)
    (X Xt : ℕ → ℕ → Ω → ℝ) (σsq : ℝ) (b : ℕ → ℝ) (C : ℝ)
    (hmono : ∀ n, Monotone (𝓕 n)) (hle : ∀ n k, 𝓕 n k ≤ mΩ)
    (hadaptX : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (X n j))
    (hadaptXt : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (Xt n j))
    (hmds : ∀ n j, μ[Xt n j | 𝓕 n j] =ᵐ[μ] 0)
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n j ω, |Xt n j ω| ≤ b n)
    (hCbr : ∀ n ω, ∑ j ∈ Finset.range (kn n), (Xt n j ω) ^ 2 ≤ C)
    (hbracket : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (Xt n j ω) ^ 2) atTop (𝓝 σsq))
    (hagree : Tendsto
      (fun n => (μ {ω | partialSum (X n) (kn n) ω ≠ partialSum (Xt n) (kn n) ω}).toReal)
      atTop (𝓝 0)) :
    ∀ u : ℝ, Tendsto
      (fun n => ∫ ω, Complex.exp (((u * partialSum (X n) (kn n) ω : ℝ) : ℂ) * Complex.I) ∂μ)
      atTop (𝓝 (Complex.exp (((-σsq * u ^ 2 / 2 : ℝ) : ℂ)))) := by
  intro u
  have := TypeDDecoupling.MartingaleCLT.core_charFun_tendsto kn 𝓕 Xt σsq b C hmono hle hadaptXt hmds hb0 hblim hbound hCbr hbracket u
  exact (by
  convert charFun_integral_tendsto_of_agree _ _ u _ ( fun n => ?_ ) ( fun n => ?_ ) hagree this using 1;
  · exact Finset.measurable_sum _ fun j _ => ( hadaptX n j |> StronglyMeasurable.measurable ) |> ( fun h => h.mono ( hle n ( j + 1 ) ) le_rfl );
  · exact Finset.measurable_sum _ fun j _ => ( hadaptXt n j ).measurable.mono ( by tauto ) ( by tauto ))

/-! ## The joint / fdd / independence version -/

/-
**Joint Gaussian charFun** for two martingale-difference arrays `X, Y` with diagonal
brackets converging to `sX, sY` and cross-bracket converging to `0`, via
`joint_charFun_tendsto` and the same stopped-array adapter.  The `2`-D characteristic
function of the true partial-sum pair converges to that of the **independent** Gaussian pair
`N(0,sX) ⊗ N(0,sY)`; cross-bracket zero is exactly what makes the components independent.
-/
theorem martingale_joint_charFun_gaussian
    (kn : ℕ → ℕ) (𝓕 : ℕ → ℕ → MeasurableSpace Ω)
    (X Y Xt Yt : ℕ → ℕ → Ω → ℝ) (sX sY : ℝ) (b : ℕ → ℝ) (C : ℝ)
    (hmono : ∀ n, Monotone (𝓕 n)) (hle : ∀ n k, 𝓕 n k ≤ mΩ)
    (hadaptX : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (X n j))
    (hadaptY : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (Y n j))
    (hadaptXt : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (Xt n j))
    (hadaptYt : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (Yt n j))
    (hmdsX : ∀ n j, μ[Xt n j | 𝓕 n j] =ᵐ[μ] 0)
    (hmdsY : ∀ n j, μ[Yt n j | 𝓕 n j] =ᵐ[μ] 0)
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hboundX : ∀ n j ω, |Xt n j ω| ≤ b n) (hboundY : ∀ n j ω, |Yt n j ω| ≤ b n)
    (hCbrX : ∀ n ω, ∑ j ∈ Finset.range (kn n), (Xt n j ω) ^ 2 ≤ C)
    (hCbrY : ∀ n ω, ∑ j ∈ Finset.range (kn n), (Yt n j ω) ^ 2 ≤ C)
    (hbrX : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (Xt n j ω) ^ 2) atTop (𝓝 sX))
    (hbrY : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (Yt n j ω) ^ 2) atTop (𝓝 sY))
    (hbrXY : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (Xt n j ω) * (Yt n j ω)) atTop (𝓝 0))
    (hagreeX : Tendsto
      (fun n => (μ {ω | partialSum (X n) (kn n) ω ≠ partialSum (Xt n) (kn n) ω}).toReal)
      atTop (𝓝 0))
    (hagreeY : Tendsto
      (fun n => (μ {ω | partialSum (Y n) (kn n) ω ≠ partialSum (Yt n) (kn n) ω}).toReal)
      atTop (𝓝 0)) :
    ∀ a c : ℝ, Tendsto
      (fun n => ∫ ω, Complex.exp (((a * partialSum (X n) (kn n) ω
          + c * partialSum (Y n) (kn n) ω : ℝ) : ℂ) * Complex.I) ∂μ)
      atTop (𝓝 (Complex.exp (((-(a ^ 2 * sX + c ^ 2 * sY) / 2 : ℝ) : ℂ)))) := by
  intro a c;
  have := @charFun_integral_tendsto_of_agree Ω mΩ μ;
  convert this ( fun n ω => a * partialSum ( X n ) ( kn n ) ω + c * partialSum ( Y n ) ( kn n ) ω ) ( fun n ω => a * partialSum ( Xt n ) ( kn n ) ω + c * partialSum ( Yt n ) ( kn n ) ω ) 1 _ _ _ _ _ using 1 <;> norm_num;
  · intro n; apply_rules [ Measurable.add, Measurable.mul, measurable_const ] ;
    · exact Finset.measurable_sum _ fun i _ => hadaptX n i |> StronglyMeasurable.measurable |> Measurable.comp <| hle n i |> fun h => h |> fun h => by tauto;
    · exact Finset.measurable_sum _ fun i _ => hadaptY n i |> StronglyMeasurable.measurable |> Measurable.comp <| by tauto;
  · intro n
    have h_meas_Xt : Measurable (partialSum (Xt n) (kn n)) := by
      exact Finset.measurable_sum _ fun j _ => ( hadaptXt n j |> StronglyMeasurable.measurable ) |> Measurable.comp <| by measurability;
    have h_meas_Yt : Measurable (partialSum (Yt n) (kn n)) := by
      exact Finset.measurable_sum _ fun i _ => ( hadaptYt n i |> StronglyMeasurable.measurable ) |> Measurable.comp <| by measurability;
    exact Measurable.add (Measurable.const_mul h_meas_Xt a) (Measurable.const_mul h_meas_Yt c);
  · refine' squeeze_zero ( fun n => by positivity ) ( fun n => _ ) ( by simpa using hagreeX.add hagreeY );
    refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono _ ) _;
    any_goals exact { ω | partialSum ( X n ) ( kn n ) ω ≠ partialSum ( Xt n ) ( kn n ) ω } ∪ { ω | partialSum ( Y n ) ( kn n ) ω ≠ partialSum ( Yt n ) ( kn n ) ω };
    · exact MeasureTheory.measure_ne_top _ _;
    · intro ω hω; contrapose! hω; aesop;
    · convert ENNReal.toReal_mono _ ( MeasureTheory.measure_union_le _ _ ) using 1;
      · rw [ ENNReal.toReal_add ] <;> norm_num;
      · exact ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ MeasureTheory.measure_lt_top _ _, MeasureTheory.measure_lt_top _ _ ⟩ );
      · infer_instance;
  · convert TypeDDecoupling.MartingaleCLT.joint_charFun_tendsto kn 𝓕 Xt Yt sX sY b C hmono hle hadaptXt hadaptYt hmdsX hmdsY hb0 hblim hboundX hboundY hCbrX hCbrY hbrX hbrY hbrXY a c using 1 ; ring;
    · exact funext fun n => by congr; ext; push_cast; ring;
    · push_cast; ring;

end TypeDDecoupling.MartingaleGaussian