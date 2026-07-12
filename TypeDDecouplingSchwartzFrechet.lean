/-
# The Fréchet package for Schwartz space

This file establishes, for Mathlib's canonical `SchwartzMap E F` (Schwartz space of
smooth rapidly decreasing functions), the functional-analytic package needed for
Banach–Steinhaus arguments:

* `SchwartzMap.instIsCountablyGeneratedUniformity` — the uniformity is countably
  generated (from the countable `ℕ × ℕ`-indexed seminorm family
  `schwartzSeminormFamily`);
* `SchwartzMap.instCompleteSpace` — completeness for Mathlib's canonical Schwartz
  uniformity (requires `[CompleteSpace F]`);
* `SchwartzMap.instBaireSpace`, `SchwartzMap.instBarrelledSpace` — the Baire and
  barrelled-space instances, obtained from Mathlib's metrization of countably
  generated uniformities;
* sanity corollaries: the Banach–Steinhaus dominating-seminorm form, and
  continuity of a pointwise supremum of tempered functionals.

Everything attaches to Mathlib's canonical `SchwartzMap.instUniformSpace` /
`instTopologicalSpace`; no new metric or topology is introduced.

The results are stated at the natural generality (`E`, `F` real normed spaces).
Completeness (and everything downstream) additionally requires `[CompleteSpace F]`,
which is genuinely necessary: for `E ≠ 0` the Schwartz space is complete iff `F` is.
-/
import Mathlib

open scoped Topology
open Filter SchwartzMap

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### (1) Countably generated uniformity -/

/-- The uniformity of `SchwartzMap E F` is countably generated: it comes from the
countable `ℕ × ℕ`-indexed seminorm family `schwartzSeminormFamily`. -/
instance instIsCountablyGeneratedUniformity :
    (uniformity (SchwartzMap E F)).IsCountablyGenerated := by
  haveI : FirstCountableTopology (SchwartzMap E F) :=
    (schwartz_withSeminorms ℝ E F).firstCountableTopology
  exact IsUniformAddGroup.uniformity_countably_generated

/-! ### Auxiliary estimates -/

/-
Pointwise bound for the difference of iterated derivatives of two Schwartz maps
in terms of a Schwartz seminorm.
-/
lemma norm_pow_iteratedFDeriv_sub_le (a b : SchwartzMap E F) (k n : ℕ) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (a : E → F) x - iteratedFDeriv ℝ n (b : E → F) x‖
      ≤ (SchwartzMap.seminorm ℝ k n) (a - b) := by
  convert SchwartzMap.le_seminorm ℝ k n ( a - b ) x using 1;
  convert rfl;
  have h_diff : ∀ x : E, ContDiffAt ℝ (⊤ : ℕ∞) (⇑(a - b)) x ∧ ContDiffAt ℝ (⊤ : ℕ∞) (⇑a) x ∧ ContDiffAt ℝ (⊤ : ℕ∞) (⇑b) x := by
    intro x;
    exact ⟨ ( a - b ).smooth'.contDiffAt, a.smooth'.contDiffAt, b.smooth'.contDiffAt ⟩;
  have := h_diff x;
  obtain ⟨ ha, hb, hc ⟩ := this;
  have := iteratedFDeriv_add_apply ( show ContDiffAt ℝ ( ↑n ) ( ⇑a ) x from hb.of_le ( mod_cast le_top ) ) ( show ContDiffAt ℝ ( ↑n ) ( -⇑b ) x from by simpa using hc.neg.of_le ( mod_cast le_top ) );
  convert this using 1;
  · exact congr_arg ( fun f => iteratedFDeriv ℝ n f x ) ( funext fun x => by simp +decide [ sub_eq_add_neg ] );
  · rw [ sub_eq_add_neg, iteratedFDeriv_neg_apply ]

/-
A Cauchy sequence in `SchwartzMap E F` is Cauchy with respect to each Schwartz
seminorm.
-/
lemma cauchySeq_seminorm (f : ℕ → SchwartzMap E F) (hf : CauchySeq f) (k n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ i ≥ N, ∀ j ≥ N, (SchwartzMap.seminorm ℝ k n) (f i - f j) < ε := by
  have h_cauchy : ∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, (SchwartzMap.seminorm ℝ k n) (f i - f j) < ε := by
    intro ε hε
    have h_cauchy_def : ∀ᶠ (ij : ℕ × ℕ) in Filter.atTop ×ˢ atTop, (SchwartzMap.seminorm ℝ k n) (f ij.1 - f ij.2) < ε := by
      have h_cauchy : Filter.Tendsto (fun ij : ℕ × ℕ => (SchwartzMap.seminorm ℝ k n) (f ij.1 - f ij.2)) (atTop ×ˢ atTop) (nhds 0) := by
        have h_cauchy : Filter.Tendsto (fun ij : ℕ × ℕ => (f ij.1 - f ij.2)) (atTop ×ˢ atTop) (𝓝 0) := by
          rw [ cauchySeq_iff ] at hf;
          rw [ tendsto_nhds ];
          intro s hs hs0;
          rcases hf ( { p : 𝓢(E, F) × 𝓢(E, F) | p.1 - p.2 ∈ s } ) ( by
            refine' ⟨ _, _, _ ⟩;
            exact -s;
            · exact IsOpen.mem_nhds ( hs.neg ) ( by simpa );
            · simp +decide [ Set.subset_def, sub_eq_add_neg ] ) with ⟨ N, hN ⟩;
          exact Filter.mem_of_superset ( Filter.prod_mem_prod ( Filter.Ici_mem_atTop N ) ( Filter.Ici_mem_atTop N ) ) fun x hx => hN _ hx.1 _ hx.2;
        convert Filter.Tendsto.comp ( show Filter.Tendsto ( fun x : 𝓢(E, F) => SchwartzMap.seminorm ℝ k n x ) ( 𝓝 0 ) ( 𝓝 0 ) from ?_ ) h_cauchy using 1;
        refine' Continuous.tendsto' _ _ _ _ <;> norm_num;
        convert ( schwartz_withSeminorms ℝ E F ).continuous_seminorm ( k, n ) using 1;
      exact h_cauchy.eventually ( gt_mem_nhds hε )
    rw [ Filter.eventually_prod_iff ] at h_cauchy_def;
    rcases h_cauchy_def with ⟨ pa, hpa, pb, hpb, h ⟩ ; rcases Filter.eventually_atTop.mp hpa with ⟨ N₁, hN₁ ⟩ ; rcases Filter.eventually_atTop.mp hpb with ⟨ N₂, hN₂ ⟩ ; exact ⟨ Max.max N₁ N₂, fun i hi j hj => h ( hN₁ i ( le_trans ( le_max_left _ _ ) hi ) ) ( hN₂ j ( le_trans ( le_max_right _ _ ) hj ) ) ⟩ ;
  exact h_cauchy ε hε

/-! ### The analytic heart: smooth limits of smooth functions -/

/-
If the `(n+1)`-th iterated derivatives converge uniformly to `G`, then the
Fréchet derivatives of the `n`-th iterated derivatives converge uniformly to
`continuousMultilinearCurryLeftEquiv ∘ G`.
-/
lemma tendstoUniformly_fderiv_iteratedFDeriv
    (f : ℕ → E → F) (n : ℕ)
    (G : E → ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) F)
    (h : TendstoUniformly (fun i x => iteratedFDeriv ℝ (n + 1) (f i) x) G atTop) :
    TendstoUniformly (fun i x => fderiv ℝ (iteratedFDeriv ℝ n (f i)) x)
      (fun x => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F (G x))
      atTop := by
  convert UniformContinuous.comp_tendstoUniformly _ h using 1;
  convert ( continuousMultilinearCurryLeftEquiv ℝ ( fun _ : Fin ( n + 1 ) => E ) F ).isometry.uniformContinuous using 1

/-
If a sequence of `C^∞` functions converges pointwise to `g`, and for each order
`n` the `n`-th iterated derivatives converge uniformly (to some function), then the
limit `g` is `C^∞` and its iterated derivatives are the uniform limits of the
iterated derivatives of the sequence. This is the analytic core of completeness.
-/
theorem contDiff_top_of_tendsto_of_tendstoUniformly
    (f : ℕ → E → F) (g : E → F)
    (hf : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f i))
    (hg : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 (g x)))
    (hU : ∀ n : ℕ, ∃ G : E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F,
        TendstoUniformly (fun i x => iteratedFDeriv ℝ n (f i) x) G atTop) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧
      ∀ n : ℕ, TendstoUniformly (fun i x => iteratedFDeriv ℝ n (f i) x)
        (iteratedFDeriv ℝ n g) atTop := by
  have h_key : ∀ n, ∃ G, TendstoUniformly (fun i x => iteratedFDeriv ℝ n (f i) x) G atTop ∧ G = iteratedFDeriv ℝ n g := by
    intro n
    induction' n with n ih
    generalize_proofs at *;
    · obtain ⟨ G, hG ⟩ := hU 0
      generalize_proofs at *;
      use G
      generalize_proofs at *;
      have hG_eq : G = iteratedFDeriv ℝ 0 g := by
        ext x
        generalize_proofs at *;
        have := hG.tendsto_at x;
        convert tendsto_nhds_unique ( this.eval_const ‹_› ) ( hg x |> Filter.Tendsto.comp <| Filter.tendsto_id ) using 1
      generalize_proofs at *;
      exact ⟨ hG, hG_eq ⟩;
    · obtain ⟨ G, hG₁, hG₂ ⟩ := ih
      obtain ⟨ G', hG'₁ ⟩ := hU (n + 1);
      have h_deriv : ∀ x, HasFDerivAt (iteratedFDeriv ℝ n g) (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F (G' x)) x := by
        intro x;
        convert hasFDerivAt_of_tendstoUniformly _ _ _ _ using 1;
        rotate_left;
        exact ℕ;
        exact Filter.atTop;
        exact instIsRCLikeNormedField ℝ;
        use fun i x => iteratedFDeriv ℝ n ( f i ) x;
        use fun i x => fderiv ℝ ( iteratedFDeriv ℝ n ( f i ) ) x;
        use fun x => continuousMultilinearCurryLeftEquiv ℝ ( fun _ : Fin ( n + 1 ) => E ) F ( G' x );
        · exact Filter.atTop_neBot;
        · convert tendstoUniformly_fderiv_iteratedFDeriv f n G' hG'₁ using 1;
        · intro i x;
          have h_diff : DifferentiableAt ℝ (iteratedFDeriv ℝ n (f i)) x := by
            have := hf i;
            convert this.differentiable_iteratedFDeriv _ x using 1;
            exact compareOfLessAndEq_eq_lt.mp rfl;
          exact h_diff.hasFDerivAt;
        · intro x; exact (by
          convert hG₁.tendsto_at x using 1;
          rw [ hG₂ ]);
        · rfl;
      refine' ⟨ G', hG'₁, _ ⟩;
      ext x; simp +decide [ iteratedFDeriv_succ_eq_comp_left, h_deriv x |> HasFDerivAt.fderiv ] ;
  have h_diff : ∀ n, Differentiable ℝ (iteratedFDeriv ℝ n g) := by
    intro n
    obtain ⟨G, hG_unif, hG_eq⟩ := h_key n
    obtain ⟨G', hG'_unif, hG'_eq⟩ := h_key (n + 1);
    have := @hasFDerivAt_of_tendstoUniformly;
    specialize this ( tendstoUniformly_fderiv_iteratedFDeriv f n G' hG'_unif ) ( fun i x => ?_ ) ( fun x => ?_ );
    use fun i x => iteratedFDeriv ℝ n ( f i ) x;
    exact fun x => G x;
    · apply_rules [ DifferentiableAt.hasFDerivAt, hf i |> ContDiff.differentiable_iteratedFDeriv ];
      exact compareOfLessAndEq_eq_lt.mp rfl;
    · exact hG_unif.tendsto_at x;
    · exact fun x => by simpa only [ hG_eq ] using this x |> HasFDerivAt.differentiableAt;
  refine' ⟨ _, fun n => _ ⟩;
  · refine' contDiff_of_differentiable_iteratedFDeriv ( n := ⊤ ) fun n _ => h_diff n;
  · simpa only [ h_key n |> Classical.choose_spec |> And.right ] using h_key n |> Classical.choose_spec |> And.left

/-! ### (2) Completeness -/

/-
For a Cauchy sequence in `SchwartzMap E F`, the pointwise limits of the
iterated derivatives exist and are uniform limits.
-/
lemma exists_tendstoUniformly_iteratedFDeriv [CompleteSpace F]
    (f : ℕ → SchwartzMap E F) (hf : CauchySeq f) (n : ℕ) :
    ∃ G : E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F,
      TendstoUniformly (fun i x => iteratedFDeriv ℝ n (f i : E → F) x) G atTop := by
  have h_uniform_cauchy : UniformCauchySeqOn (fun i x => iteratedFDeriv ℝ n (f i) x) atTop Set.univ := by
    rw [ Metric.uniformCauchySeqOn_iff ];
    intro ε hε
    obtain ⟨N, hN⟩ : ∃ N, ∀ i ≥ N, ∀ j ≥ N, (SchwartzMap.seminorm ℝ 0 n) (f i - f j) < ε := by
      convert cauchySeq_seminorm f hf 0 n hε using 1;
    simp_all +decide [ dist_eq_norm ];
    exact ⟨ N, fun i hi j hj x => lt_of_le_of_lt ( by simpa using norm_pow_iteratedFDeriv_sub_le ( f i ) ( f j ) 0 n x ) ( hN i hi j hj ) ⟩;
  have h_pointwise_limit : ∀ x : E, ∃ Gx : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F, Filter.Tendsto (fun i => iteratedFDeriv ℝ n (f i) x) Filter.atTop (nhds Gx) := by
    intro x
    have h_cauchy : CauchySeq (fun i => iteratedFDeriv ℝ n (f i) x) := by
      rw [ Metric.uniformCauchySeqOn_iff ] at h_uniform_cauchy;
      exact Metric.cauchySeq_iff.2 fun ε hε => by rcases h_uniform_cauchy ε hε with ⟨ N, hN ⟩ ; exact ⟨ N, fun m hm n hn => hN m hm n hn x trivial ⟩ ;
    exact cauchySeq_tendsto_of_complete h_cauchy;
  choose G hG using h_pointwise_limit;
  use G;
  convert h_uniform_cauchy.tendstoUniformlyOn_of_tendsto ( fun x _ => hG x ) using 1;
  simp +decide [ TendstoUniformly, TendstoUniformlyOn ]

/-
For a Cauchy sequence in `SchwartzMap E F`, the pointwise limit function exists.
-/
lemma exists_pointwise_limit [CompleteSpace F]
    (f : ℕ → SchwartzMap E F) (hf : CauchySeq f) :
    ∃ g : E → F, ∀ x, Tendsto (fun i => (f i : E → F) x) atTop (𝓝 (g x)) := by
  have h_pointwise_limit : ∀ x : E, ∃ Gx : F, Filter.Tendsto (fun i => (f i) x) Filter.atTop (nhds Gx) := by
    intro x
    have h_cauchy : ∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, ‖(f i) x - (f j) x‖ < ε := by
      intro ε hε;
      obtain ⟨ N, hN ⟩ := cauchySeq_seminorm f hf 0 0 hε;
      use N; intro i hi j hj; specialize hN i hi j hj; exact (by
      refine' lt_of_le_of_lt _ hN;
      convert SchwartzMap.le_seminorm ℝ 0 0 ( f i - f j ) x using 1;
      simp +decide);
    exact cauchySeq_tendsto_of_complete ( Metric.cauchySeq_iff.2 fun ε hε => by simpa [ dist_eq_norm ] using h_cauchy ε hε );
  exact ⟨ fun x => Classical.choose ( h_pointwise_limit x ), fun x => Classical.choose_spec ( h_pointwise_limit x ) ⟩

/-
A Cauchy sequence in `SchwartzMap E F` is bounded in every Schwartz seminorm.
-/
lemma bddAbove_seminorm (f : ℕ → SchwartzMap E F) (hf : CauchySeq f) (k n : ℕ) :
    ∃ B, ∀ i, (SchwartzMap.seminorm ℝ k n) (f i) ≤ B := by
  obtain ⟨ N, hN ⟩ := cauchySeq_seminorm f hf k n one_pos;
  -- Set `B := (p (f N) + 1) ⊔ (Finset.range (N+1)).sup' (by simp) (fun i => p (f i))`.
  set B := max ((SchwartzMap.seminorm ℝ k n) (f N) + 1) ((Finset.range (N + 1)).sup' (by simp) (fun i => (SchwartzMap.seminorm ℝ k n) (f i))) with hB_def;
  use B;
  intro i
  by_cases hi : i ≤ N;
  · exact le_max_of_le_right ( Finset.le_sup' ( fun i => ( SchwartzMap.seminorm ℝ k n ) ( f i ) ) ( Finset.mem_range_succ_iff.mpr hi ) );
  · refine' le_trans _ ( le_max_left _ _ );
    convert le_trans ( map_add_le_add ( SchwartzMap.seminorm ℝ k n ) ( f i - f N ) ( f N ) ) _ using 1;
    · rw [ sub_add_cancel ];
    · linarith [ hN i ( le_of_not_ge hi ) N le_rfl ]

/-
**Completeness of Schwartz space.** With `F` complete, `SchwartzMap E F` is a
complete space for Mathlib's canonical Schwartz uniformity.
-/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (SchwartzMap E F) := by
  convert @UniformSpace.complete_of_cauchySeq_tendsto _ _ _ _;
  · infer_instance;
  · intro f hf
    obtain ⟨g, hg⟩ := exists_pointwise_limit f hf
    obtain ⟨hg_cont, hg_conv⟩ := contDiff_top_of_tendsto_of_tendstoUniformly
      (fun i => (f i : E → F)) g (fun i => (f i).smooth') hg
      (fun n => exists_tendstoUniformly_iteratedFDeriv f hf n);
    -- Define `g_schwartz : SchwartzMap E F := ⟨g, hg_cont, fun k n => decay k n⟩`.
    obtain ⟨g_schwartz, hg_schwartz⟩ : ∃ g_schwartz : SchwartzMap E F, g_schwartz = g ∧ ∀ k n, ∃ C, ∀ x, ‖x‖^k * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
      have h_decay : ∀ k n, ∃ C, ∀ x, ‖x‖^k * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
        intro k n
        obtain ⟨B, hB⟩ := bddAbove_seminorm f hf k n
        use B
        intro x
        have h_lim : Filter.Tendsto (fun i => ‖x‖^k * ‖iteratedFDeriv ℝ n (f i) x‖) Filter.atTop (nhds (‖x‖^k * ‖iteratedFDeriv ℝ n g x‖)) := by
          exact Filter.Tendsto.mul tendsto_const_nhds ( Filter.Tendsto.norm ( hg_conv n |> TendstoUniformly.tendsto_at |> fun h => h x ) );
        exact le_of_tendsto' h_lim fun i => le_trans ( by simpa using SchwartzMap.le_seminorm ℝ k n ( f i ) x ) ( hB i );
      exact ⟨ ⟨ g, hg_cont, h_decay ⟩, rfl, h_decay ⟩;
    use g_schwartz;
    have h_tendsto : ∀ k n, ∀ ε > 0, ∃ N, ∀ i ≥ N, (SchwartzMap.seminorm ℝ k n) (f i - g_schwartz) < ε := by
      intro k n ε hε
      obtain ⟨N, hN⟩ : ∃ N, ∀ i ≥ N, ∀ j ≥ N, (SchwartzMap.seminorm ℝ k n) (f i - f j) < ε / 2 := by
        exact cauchySeq_seminorm f hf k n ( half_pos hε );
      use N;
      intro i hi
      have h_bound : ∀ x, ‖x‖^k * ‖iteratedFDeriv ℝ n (f i) x - iteratedFDeriv ℝ n g x‖ ≤ ε / 2 := by
        intro x
        have h_bound : Filter.Tendsto (fun j => ‖x‖^k * ‖iteratedFDeriv ℝ n (f i) x - iteratedFDeriv ℝ n (f j) x‖) Filter.atTop (nhds (‖x‖^k * ‖iteratedFDeriv ℝ n (f i) x - iteratedFDeriv ℝ n g x‖)) := by
          exact Filter.Tendsto.mul tendsto_const_nhds ( Filter.Tendsto.norm ( tendsto_const_nhds.sub ( hg_conv n |> fun h => h.tendsto_at x ) ) );
        exact le_of_tendsto h_bound ( Filter.eventually_atTop.mpr ⟨ N, fun j hj => le_of_lt ( lt_of_le_of_lt ( norm_pow_iteratedFDeriv_sub_le ( f i ) ( f j ) k n x ) ( hN i hi j hj ) ) ⟩ );
      refine' lt_of_le_of_lt ( SchwartzMap.seminorm_le_bound ℝ k n ( f i - g_schwartz ) ( half_pos hε |> le_of_lt ) _ ) ( half_lt_self hε );
      convert h_bound using 3;
      rw [ ← hg_schwartz.1 ];
      have h_diff : ∀ x, ContDiffAt ℝ (↑n) (⇑(f i)) x ∧ ContDiffAt ℝ (↑n) (⇑g_schwartz) x := by
        exact fun x => ⟨ ( f i ).smooth'.contDiffAt.of_le ( mod_cast le_top ), g_schwartz.smooth'.contDiffAt.of_le ( mod_cast le_top ) ⟩;
      have := iteratedFDeriv_add_apply ( show ContDiffAt ℝ ( ↑n ) ( ⇑ ( f i ) ) ‹_› from h_diff _ |>.1 ) ( show ContDiffAt ℝ ( ↑n ) ( -⇑g_schwartz ) ‹_› from by simpa using h_diff _ |>.2.neg );
      convert congr_arg Norm.norm this using 1;
      · exact congr_arg Norm.norm ( by congr; ext; simp +decide [ sub_eq_add_neg ] );
      · rw [ iteratedFDeriv_neg_apply ] ; simp +decide [ sub_eq_add_neg ];
    rw [ ( schwartz_withSeminorms ℝ E F ).tendsto_nhds ];
    exact fun i ε hε => by rcases h_tendsto i.1 i.2 ε hε with ⟨ N, hN ⟩ ; exact Filter.eventually_atTop.mpr ⟨ N, fun n hn => hN n hn ⟩ ;

/-! ### (3) Baire space and (4) barrelled space -/

/-- Schwartz space is a Baire space (from countably generated uniformity + completeness,
via Mathlib's metrization of countably generated uniformities). -/
instance instBaireSpace [CompleteSpace F] : BaireSpace (SchwartzMap E F) :=
  inferInstance

/-- Schwartz space is barrelled. -/
instance instBarrelledSpace [CompleteSpace F] :
    BarrelledSpace ℝ (SchwartzMap E F) :=
  inferInstance

/-! ### (5) Sanity corollaries -/

/-- Turn a continuous linear functional on `𝓢(ℝ, ℝ)` into a continuous seminorm. -/
noncomputable def clmSeminorm (T : SchwartzMap ℝ ℝ →L[ℝ] ℝ) : Seminorm ℝ (SchwartzMap ℝ ℝ) :=
  (normSeminorm ℝ ℝ).comp T.toLinearMap

lemma clmSeminorm_apply (T : SchwartzMap ℝ ℝ →L[ℝ] ℝ) (φ : SchwartzMap ℝ ℝ) :
    clmSeminorm T φ = |T φ| := by
  convert Seminorm.comp_apply ( normSeminorm ℝ ℝ ) T.toLinearMap φ using 1

lemma continuous_clmSeminorm (T : SchwartzMap ℝ ℝ →L[ℝ] ℝ) :
    Continuous (clmSeminorm T) := by
  convert T.continuous.abs

/-
**(5a) Banach–Steinhaus, dominating-seminorm form for tempered functionals.**
A pointwise-bounded family of continuous linear functionals on Schwartz space is
dominated by a single continuous seminorm.
-/
theorem exists_continuous_seminorm_of_pointwise_bounded {ι : Type*}
    (𝓕 : ι → SchwartzMap ℝ ℝ →L[ℝ] ℝ)
    (h : ∀ φ : SchwartzMap ℝ ℝ, ∃ C, ∀ i, |𝓕 i φ| ≤ C) :
    ∃ q : Seminorm ℝ (SchwartzMap ℝ ℝ), Continuous q ∧ ∀ i φ, |𝓕 i φ| ≤ q φ := by
  have h_uniform_equicontinuous : UniformEquicontinuous (fun f : ι => DFunLike.coe (𝓕 f)) := by
    apply WithSeminorms.banach_steinhaus;
    convert norm_withSeminorms ℝ ℝ using 1;
    exact fun k x => by rcases h x with ⟨ C, hC ⟩ ; exact ⟨ C, Set.forall_mem_range.2 fun i => hC i ⟩ ;
  have h_banach_steinhaus : ∀ k : Fin 1, ∃ p : Seminorm ℝ (SchwartzMap ℝ ℝ), Continuous p ∧ ∀ i, (normSeminorm ℝ ℝ).comp (𝓕 i |> ContinuousLinearMap.toLinearMap) ≤ p := by
    intro k;
    have := @WithSeminorms.uniformEquicontinuous_iff_exists_continuous_seminorm;
    convert this ( norm_withSeminorms ℝ ℝ ) ( fun i => ( 𝓕 i |> ContinuousLinearMap.toLinearMap ) ) |>.1 h_uniform_equicontinuous 0 using 1;
  exact Exists.elim ( h_banach_steinhaus 0 ) fun p hp => ⟨ p, hp.1, fun i φ => hp.2 i φ ⟩

/-
**(5b) Continuity of a pointwise sup of tempered functionals.**
An everywhere-finite countable pointwise supremum of continuous linear functionals
on Schwartz space is a continuous seminorm.
-/
theorem continuous_iSup_abs {ι : Type*} [Countable ι]
    (𝓕 : ι → SchwartzMap ℝ ℝ →L[ℝ] ℝ)
    (hfin : BddAbove (Set.range (fun i => clmSeminorm (𝓕 i)))) :
    Continuous (fun φ => ⨆ i, |𝓕 i φ|) := by
  convert Seminorm.continuous_iSup ( fun i => clmSeminorm ( 𝓕 i ) ) ( fun i => continuous_clmSeminorm ( 𝓕 i ) ) hfin using 1;
  ext φ; simp +decide [ clmSeminorm_apply ] ;

end SchwartzMap