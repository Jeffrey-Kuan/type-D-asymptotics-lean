import Mathlib
import TypeDDecouplingLevy

/-!
# Lévy continuity on `ℝ × ℝ` (bridge for `prop:twophase`)

This file extends the identified-limit form of Lévy's continuity theorem — proved on
`ℝ` in `TypeDDecouplingLevy.lean` — to the plane `ℝ × ℝ`, in the exact shape needed to
turn the characteristic-function limit produced by the abstract two-phase mixture CLT
(`TypeDDecoupling.TwoPhase.twophase_mixture_charFun_tendsto`) into weak convergence of
`ℝ × ℝ`-valued random variables (`TypeDDecoupling.TendstoInDistribution`).

The two-dimensional characteristic function is `charFun2 μ a c = ∫ exp(i(a x + c y)) dμ`.
As the brief notes, tightness (componentwise from the marginal `charFun`s), Prokhorov's
theorem, and `Measure.ext_of_charFun` are dimension-generic in Mathlib; we run the
argument on the inner-product model `E2 = WithLp 2 (ℝ × ℝ)` and transport along the
homeomorphism `WithLp.homeomorphProd`.

Main deliverable: `tendstoInDistribution_of_charFun2` — from pointwise convergence of
`charFun2 (law of X_T) → charFun2 ν`, conclude the portmanteau (bounded-continuous)
convergence `∫ f (X_T) dμ → ∫ f dν`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Complex

namespace TypeDDecoupling.TwoPhaseBridge

/-- The planar characteristic function of a measure on `ℝ × ℝ`:
`charFun2 μ a c = ∫ exp(i (a x + c y)) dμ(x,y)`. -/
noncomputable def charFun2 (μ : Measure (ℝ × ℝ)) (a c : ℝ) : ℂ :=
  ∫ z, Complex.exp (((a * z.1 + c * z.2 : ℝ) : ℂ) * Complex.I) ∂μ

/-- The inner-product model of the plane. -/
abbrev E2 := WithLp 2 (ℝ × ℝ)

/-- The homeomorphism `E2 ≃ₜ ℝ × ℝ`. -/
noncomputable def e2Equiv : E2 ≃ₜ (ℝ × ℝ) := WithLp.homeomorphProd 2 ℝ ℝ

/-- The measurable equivalence `E2 ≃ᵐ ℝ × ℝ`. -/
noncomputable def e2MEquiv : E2 ≃ᵐ (ℝ × ℝ) := e2Equiv.toMeasurableEquiv

/-! ### Relating `charFun2` on `ℝ × ℝ` to Mathlib's `charFun` on `E2` -/

/-
Pulling a measure on `ℝ × ℝ` back to `E2` and taking Mathlib's `charFun` at the point
`e2MEquiv.symm (a, c)` recovers `charFun2`.
-/
lemma charFun_map_symm (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (a c : ℝ) :
    charFun (μ.map e2MEquiv.symm) (e2MEquiv.symm (a, c)) = charFun2 μ a c := by
  rw [ charFun_apply ];
  rw [ MeasureTheory.integral_map ];
  · convert rfl using 3;
  · exact e2MEquiv.symm.measurable.aemeasurable;
  · fun_prop

/-! ### Sequential Lévy continuity on `E2` -/

/-
The characteristic function of a probability measure on `E2` is continuous.
-/
lemma continuous_charFun_E2 (μ : Measure E2) [IsProbabilityMeasure μ] :
    Continuous (fun t => charFun μ t) := by
  refine' continuous_iff_continuousAt.mpr _;
  intro t;
  refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
  refine' fun x => 1;
  · exact Filter.Eventually.of_forall fun n => Continuous.aestronglyMeasurable ( by fun_prop );
  · norm_num [ Complex.norm_exp ];
  · norm_num;
  · exact Filter.Eventually.of_forall fun x => Complex.continuous_exp.continuousAt.tendsto.comp <| Filter.Tendsto.mul ( Complex.continuous_ofReal.continuousAt.tendsto.comp <| Continuous.tendsto ( by exact Continuous.inner continuous_const continuous_id' ) _ ) tendsto_const_nhds

/-- First coordinate direction of `E2`. -/
noncomputable def v1 : E2 := e2Equiv.symm (1, 0)
/-- Second coordinate direction of `E2`. -/
noncomputable def v2 : E2 := e2Equiv.symm (0, 1)

/-
The pushforward of a measure on `E2` under the first coordinate has `charFun` equal to
`charFun` of the original measure along the ray `s • v1`.
-/
lemma charFun_map_proj1 (μ : Measure E2) [IsProbabilityMeasure μ] (s : ℝ) :
    charFun (μ.map (fun x : E2 => (e2Equiv x).1)) s = charFun μ (s • v1) := by
  rw [ charFun, charFun, integral_map ];
  · unfold v1; norm_num [ e2Equiv ] ; ring;
    simp +decide [ mul_assoc, mul_comm, WithLp.homeomorphProd ];
  · exact Continuous.aemeasurable ( by continuity );
  · fun_prop

/-
The pushforward of a measure on `E2` under the second coordinate has `charFun` equal to
`charFun` of the original measure along the ray `s • v2`.
-/
lemma charFun_map_proj2 (μ : Measure E2) [IsProbabilityMeasure μ] (s : ℝ) :
    charFun (μ.map (fun x : E2 => (e2Equiv x).2)) s = charFun μ (s • v2) := by
  simp +decide [ charFun, v2 ];
  convert MeasureTheory.integral_map _ _ using 3;
  · simp +decide [ e2Equiv ];
    simp +decide [ WithLp.homeomorphProd ];
  · fun_prop;
  · exact Continuous.aestronglyMeasurable ( by continuity )

/-
**Tightness on `E2` from pointwise `charFun` convergence.**  Reduces to the 1-D
tightness theorem `TypeDDecoupling.Levy.isTightMeasureSet_of_tendsto_charFun` applied to the
two coordinate marginals, combined into a box.
-/
lemma isTightMeasureSet_of_tendsto_charFun_E2 (ξ : ℕ → ProbabilityMeasure E2)
    (ν : ProbabilityMeasure E2)
    (h : ∀ t, Tendsto (fun n => charFun (ξ n : Measure E2) t) atTop
      (𝓝 (charFun (ν : Measure E2) t))) :
    IsTightMeasureSet {((μ : ProbabilityMeasure E2) : Measure E2) | μ ∈ Set.range ξ} := by
  refine' isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr _;
  intro ε hε
  obtain ⟨K1, hK1⟩ : ∃ K1 : Set ℝ, IsCompact K1 ∧ ∀ n, (ξ n : Measure E2).map (fun x => (e2Equiv x).1) K1ᶜ ≤ ε / 2 := by
    have h_tight1 : ∀ t : ℝ, Tendsto (fun n => charFun (Measure.map (fun x => (e2Equiv x).1) (ξ n : Measure E2)) t) atTop (𝓝 (charFun (Measure.map (fun x => (e2Equiv x).1) (ν : Measure E2)) t)) := by
      intro t
      have := h (t • v1)
      simp_all +decide [ charFun_map_proj1 ];
    have h_tight1 : IsTightMeasureSet {μ | ∃ n, μ = (ξ n : Measure E2).map (fun x => (e2Equiv x).1)} := by
      convert TypeDDecoupling.Levy.isTightMeasureSet_of_tendsto_charFun ( fun n => ⟨ Measure.map ( fun x => ( e2Equiv x ).1 ) ( ξ n : Measure E2 ), ?_ ⟩ ) ⟨ Measure.map ( fun x => ( e2Equiv x ).1 ) ( ν : Measure E2 ), ?_ ⟩ _ using 1;
      all_goals norm_num [ IsProbabilityMeasure ];
      any_goals tauto;
      · simp +decide only [eq_comm];
      · constructor;
        rw [ Measure.map_apply ] <;> norm_num;
        exact measurable_fst.comp e2Equiv.continuous.measurable;
      · constructor;
        rw [ Measure.map_apply ] <;> norm_num;
        exact measurable_fst.comp e2Equiv.continuous.measurable;
    rw [ isTightMeasureSet_iff_exists_isCompact_measure_compl_le ] at h_tight1;
    exact Exists.elim ( h_tight1 ( ε / 2 ) ( ENNReal.half_pos hε.ne' ) ) fun K hK => ⟨ K, hK.1, fun n => hK.2 _ ⟨ n, rfl ⟩ ⟩
  obtain ⟨K2, hK2⟩ : ∃ K2 : Set ℝ, IsCompact K2 ∧ ∀ n, (ξ n : Measure E2).map (fun x => (e2Equiv x).2) K2ᶜ ≤ ε / 2 := by
    have := TypeDDecoupling.Levy.isTightMeasureSet_of_tendsto_charFun (fun n => ⟨(ξ n : Measure E2).map (fun x => (e2Equiv x).2), by
      constructor;
      rw [ Measure.map_apply ] <;> norm_num;
      exact measurable_snd.comp ( e2Equiv.continuous.measurable )⟩) ⟨(ν : Measure E2).map (fun x => (e2Equiv x).2), by
      constructor;
      rw [ Measure.map_apply ] <;> norm_num;
      exact measurable_snd.comp ( e2Equiv.continuous.measurable )⟩ ?_;
    · rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at this;
      exact Exists.elim ( this ( ε / 2 ) ( ENNReal.half_pos hε.ne' ) ) fun K hK => ⟨ K, hK.1, fun n => hK.2 _ ⟨ _, ⟨ n, rfl ⟩, rfl ⟩ ⟩;
    · intro t
      have := h (t • v2)
      simp_all +decide [ charFun_map_proj2 ];
  refine' ⟨ e2Equiv ⁻¹' ( K1 ×ˢ K2 ), _, _ ⟩ <;> simp_all +decide [ Set.preimage ];
  · convert hK1.1.prod hK2.1 |> IsCompact.image <| e2Equiv.symm.continuous using 1 ; aesop;
  · intro n;
    refine' le_trans _ ( le_trans ( add_le_add ( hK1.2 n ) ( hK2.2 n ) ) _ );
    · rw [ Measure.map_apply, Measure.map_apply ] <;> norm_num [ e2Equiv ];
      · exact le_trans ( MeasureTheory.measure_mono ( show { x : E2 | ( ( WithLp.homeomorphProd 2 ℝ ℝ ) x ).1 ∈ K1 ∧ ( ( WithLp.homeomorphProd 2 ℝ ℝ ) x ).2 ∈ K2 } ᶜ ⊆ ( ( fun x => ( ( WithLp.homeomorphProd 2 ℝ ℝ ) x ).1 ) ⁻¹' K1 ) ᶜ ∪ ( ( fun x => ( ( WithLp.homeomorphProd 2 ℝ ℝ ) x ).2 ) ⁻¹' K2 ) ᶜ from fun x hx => by contrapose! hx; aesop ) ) ( MeasureTheory.measure_union_le _ _ );
      · exact measurable_snd.comp ( WithLp.homeomorphProd 2 ℝ ℝ |> Homeomorph.continuous |> Continuous.measurable );
      · exact hK2.1.measurableSet;
      · exact measurable_fst.comp ( WithLp.homeomorphProd 2 ℝ ℝ |> Homeomorph.continuous |> Continuous.measurable );
      · exact hK1.1.measurableSet;
    · rw [ ENNReal.add_halves ]

/-
Weak convergence of probability measures on `E2` implies pointwise convergence of
characteristic functions.
-/
lemma charFun_tendsto_of_tendsto_E2 {μs : ℕ → ProbabilityMeasure E2} {μ : ProbabilityMeasure E2}
    (h : Tendsto μs atTop (𝓝 μ)) (t : E2) :
    Tendsto (fun n => charFun (μs n : Measure E2) t) atTop (𝓝 (charFun (μ : Measure E2) t)) := by
  convert ( ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ ).mp h ( BoundedContinuousFunction.mk ⟨ fun x => Complex.exp ( inner ℝ x t * Complex.I ), ?_ ⟩ ?_ ) using 1;
  fun_prop;
  exact ⟨ 2, fun x y => le_trans ( dist_le_norm_add_norm _ _ ) ( by norm_num [ Complex.norm_exp ] ) ⟩

/-
**Sequential Lévy continuity on `E2` (identified-limit form).**
-/
theorem levyContinuityE2 (ξ : ℕ → ProbabilityMeasure E2) (ν : ProbabilityMeasure E2)
    (h : ∀ t, Tendsto (fun n => charFun (ξ n : Measure E2) t) atTop
      (𝓝 (charFun (ν : Measure E2) t))) :
    Tendsto ξ atTop (𝓝 ν) := by
  -- By the uniqueness of the limit, we have that $a = \nu$.
  have h_unique : ∀ a b : ProbabilityMeasure E2, (∀ t : E2, charFun (a : Measure E2) t = charFun (b : Measure E2) t) → a = b := by
    intro a b h_eq
    have h_char_eq : ∀ t : E2, charFun (a : Measure E2) t = charFun (b : Measure E2) t := by
      assumption;
    have h_char_eq : (a : Measure E2) = (b : Measure E2) := by
      apply Measure.ext_of_charFun;
      exact funext h_char_eq;
    exact Subtype.ext h_char_eq;
  apply_rules [ tendsto_of_subseq_tendsto ];
  intro ns hns
  obtain ⟨a, ha⟩ : ∃ a : ProbabilityMeasure E2, ∃ ms : ℕ → ℕ, StrictMono ms ∧ Tendsto (fun n => ξ (ns (ms n))) atTop (𝓝 a) := by
    have h_compact : IsCompact (closure (Set.range ξ)) := by
      apply_rules [ isCompact_closure_of_isTightMeasureSet, isTightMeasureSet_of_tendsto_charFun_E2 ];
    have := h_compact.isSeqCompact fun n => subset_closure <| Set.mem_range_self <| ns n;
    tauto;
  obtain ⟨ ms, hms₁, hms₂ ⟩ := ha;
  exact ⟨ ms, h_unique a ν ( fun t => by simpa using tendsto_nhds_unique ( charFun_tendsto_of_tendsto_E2 hms₂ t ) ( h t |> Filter.Tendsto.comp <| hns.comp hms₁.tendsto_atTop ) ) ▸ hms₂ ⟩

/-! ### Transport back to `ℝ × ℝ` -/

/-
**Lévy continuity on `ℝ × ℝ`, filtered form.** From pointwise convergence of the
planar characteristic functions (along any countably generated filter) follows weak
convergence of the probability measures.
-/
theorem tendsto_of_charFun2_tendsto {γ : Type*} {F : Filter γ} [F.IsCountablyGenerated]
    (ξ : γ → ProbabilityMeasure (ℝ × ℝ)) (ν : ProbabilityMeasure (ℝ × ℝ))
    (h : ∀ a c : ℝ, Tendsto (fun i => charFun2 (ξ i : Measure (ℝ × ℝ)) a c) F
      (𝓝 (charFun2 (ν : Measure (ℝ × ℝ)) a c))) :
    Tendsto ξ F (𝓝 ν) := by
  have := @tendsto_iff_seq_tendsto;
  convert this.mpr _ using 1;
  · infer_instance;
  · intro x hx_tendsto
    set ξ' : ℕ → ProbabilityMeasure E2 := fun n => (ξ (x n)).map (e2MEquiv.symm.measurable.aemeasurable)
    set ν' : ProbabilityMeasure E2 := ν.map (e2MEquiv.symm.measurable.aemeasurable);
    convert ProbabilityMeasure.continuous_map ( e2Equiv.continuous ) |> Continuous.continuousAt |> fun h => h.tendsto.comp ( levyContinuityE2 ξ' ν' _ ) using 1;
    · ext n; simp +decide [ ξ' ] ;
      rw [ Measure.map_map ];
      · rw [ Measure.map_apply ];
        · congr! 1;
        · exact e2Equiv.continuous.measurable.comp e2MEquiv.symm.measurable;
        · assumption;
      · exact e2Equiv.continuous.measurable;
      · exact e2MEquiv.symm.measurable;
    · rw [ show ν'.map _ = ν from _ ];
      convert ProbabilityMeasure.toMeasure_injective _;
      convert Measure.map_map _ _;
      · erw [ Measure.map_id ];
      · exact e2Equiv.continuous.measurable;
      · exact e2MEquiv.symm.measurable;
    · intro t
      have h_charFun : ∀ n, charFun (ξ' n : Measure E2) t = charFun2 (ξ (x n)) (e2MEquiv t).1 (e2MEquiv t).2 := by
        intro n
        apply charFun_map_symm;
      have h_charFun : charFun (ν' : Measure E2) t = charFun2 ν (e2MEquiv t).1 (e2MEquiv t).2 := by
        convert charFun_map_symm ν ( e2MEquiv t ).1 ( e2MEquiv t ).2 using 1;
      rename_i h₁ h₂;
      simpa only [ h₂, h_charFun ] using h₁ ( e2MEquiv t |>.1 ) ( e2MEquiv t |>.2 ) |> Filter.Tendsto.comp <| hx_tendsto

/-! ### Deliverable used by `TypeDDecouplingCrossover.lean` -/

/-
**Deliverable.** From pointwise convergence of the planar characteristic functions of
the laws of `X_T` to those of `ν`, conclude the portmanteau (bounded-continuous)
convergence that defines `TendstoInDistribution`.
-/
theorem tendstoInDistribution_of_charFun2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → ℝ × ℝ) (hX : ∀ T, Measurable (X T))
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (hchar : ∀ a c : ℝ,
      Tendsto (fun T => ∫ ω, Complex.exp (((a * (X T ω).1 + c * (X T ω).2 : ℝ) : ℂ) * Complex.I) ∂μ)
        atTop (𝓝 (charFun2 ν a c))) :
    ∀ f : (ℝ × ℝ) → ℝ, Continuous f → (∃ M : ℝ, ∀ z, |f z| ≤ M) →
      Tendsto (fun T => ∫ ω, f (X T ω) ∂μ) atTop (𝓝 (∫ z, f z ∂ν)) := by
  intro f hf h_bound
  set ξ : ℝ → (ProbabilityMeasure (ℝ × ℝ)) := fun T => ⟨(μ.map (X T)), Measure.isProbabilityMeasure_map (hX T).aemeasurable⟩
  set ν' : (ProbabilityMeasure (ℝ × ℝ)) := ⟨ν, inferInstance⟩
  have h_tendsto : Filter.Tendsto ξ Filter.atTop (nhds ν') := by
    convert tendsto_of_charFun2_tendsto ( ξ := ξ ) ( ν := ν' ) _;
    · infer_instance;
    · convert hchar using 3;
      ext T; exact (by
      convert MeasureTheory.integral_map _ _ using 3;
      · exact hX T |> Measurable.aemeasurable;
      · fun_prop);
  have h_integral : Filter.Tendsto (fun T => ∫ z, f z ∂(ξ T : Measure (ℝ × ℝ))) Filter.atTop (nhds (∫ z, f z ∂ν')) := by
    have := @ProbabilityMeasure.tendsto_iff_forall_integral_tendsto;
    convert this.mp h_tendsto ( BoundedContinuousFunction.mk ⟨ f, hf ⟩ ?_ ) using 1;
    exact ⟨ h_bound.choose + h_bound.choose, fun x y => le_trans ( dist_le_norm_add_norm _ _ ) ( add_le_add ( h_bound.choose_spec x ) ( h_bound.choose_spec y ) ) ⟩;
  convert h_integral using 1;
  ext T; exact (by
  erw [ MeasureTheory.integral_map ];
  · exact hX T |> Measurable.aemeasurable;
  · exact hf.aestronglyMeasurable)

end TypeDDecoupling.TwoPhaseBridge