/-
# Separability of Schwartz space and compact polars in the pointwise dual

This file is the second installment of the "Mitoma campaign".  It builds the
*spatial* infrastructure for Mitoma's tightness criterion on top of the Fréchet
package of `TypeDDecouplingSchwartzFrechet` (task M1):

* **Part A — separability of `𝓢(ℝ, ℝ)`.**
  `SchwartzMap.instSeparableSpace` / `SchwartzMap.instSecondCountableTopology`
  give the (missing in Mathlib) separability of Mathlib's canonical Schwartz
  space, together with a *named* countable dense subset `SchwartzMap.denseSet`
  and the countable-reduction corollary
  `SchwartzMap.forall_le_of_forall_dense`.

* **Part B — compact polars in the pointwise dual.**
  With `SchDual := 𝓢(ℝ, ℝ) →Lₚₜ[ℝ] ℝ` (Mathlib's `PointwiseConvergenceCLM`),
  the polar balls `polarBall q := {F | ∀ φ, |F φ| ≤ q φ}` are compact for
  continuous seminorms `q` (`isCompact_polarBall`, via Tychonoff and the
  pointwise embedding `PointwiseConvergenceCLM.isEmbedding_coeFn`, no Ascoli),
  a countable cofinal family of *rational* polar balls confines every
  pointwise-bounded family (`pointwiseBounded_subset_compact_polarBall`), and
  membership is checkable on the countable dense set (`mem_polarBall_iff_dense`).

Everything attaches to Mathlib's canonical `SchwartzMap` and
`PointwiseConvergenceCLM` topologies; no re-topologization.
-/
import Mathlib
import TypeDDecouplingSchwartzFrechet

open scoped Topology SchwartzMap NNReal
open TopologicalSpace Filter

namespace SchwartzMap

/-! ## Part A: separability of `𝓢(ℝ, ℝ)` -/

/-- The one-point compactification `OnePoint ℝ` is second countable. -/
instance secondCountableTopology_onePoint_real :
    SecondCountableTopology (OnePoint ℝ) := by
  refine' TopologicalSpace.IsTopologicalBasis.secondCountableTopology _ _;
  exact ( Set.image ( fun U : Set ℝ => OnePoint.some '' U ) ( TopologicalSpace.countableBasis ℝ ) ) ∪ ( Set.range fun n : ℕ => { OnePoint.infty } ∪ OnePoint.some '' ( Set.Icc ( -n : ℝ ) n ) ᶜ );
  · refine' isTopologicalBasis_of_isOpen_of_nhds _ _;
    · intro u hu;
      rcases hu with ( ⟨ U, hU, rfl ⟩ | ⟨ n, rfl ⟩ );
      · exact OnePoint.isOpenEmbedding_coe.isOpenMap U ( by rcases TopologicalSpace.isBasis_countableBasis ℝ with h; exact h.isOpen hU );
      · refine' OnePoint.isOpen_iff_of_mem _ |>.2 _;
        · exact Set.mem_union_left _ ( Set.mem_singleton _ );
        · simp +decide [ Set.preimage ];
          rw [ show { x : ℝ | -↑n ≤ x → ↑n < x } = Set.Iio ( -↑n ) ∪ Set.Ioi ( ↑n ) from ?_ ];
          · exact ⟨ isOpen_Iio.union isOpen_Ioi, by rw [ show ( Set.Iio ( -↑n ) ∪ Set.Ioi ( ↑n ) : Set ℝ ) ᶜ = Set.Icc ( -↑n ) ( ↑n ) by ext x; aesop ] ; exact CompactIccSpace.isCompact_Icc ⟩;
          · grind;
    · intro a u ha hu;
      rcases a with ( _ | a );
      · -- Since $u$ is open and contains $\infty$, there exists a compact set $K \subseteq \mathbb{R}$ such that $\{ \infty \} \cup (\mathbb{R} \setminus K) \subseteq u$.
        obtain ⟨K, hK⟩ : ∃ K : Set ℝ, IsCompact K ∧ {OnePoint.infty} ∪ OnePoint.some '' Kᶜ ⊆ u := by
          rcases hu with ⟨ K, hK ⟩;
          exact ⟨ _, K ha, by aesop_cat ⟩;
        -- Since $K$ is compact, there exists $n \in \mathbb{N}$ such that $K \subseteq [-n, n]$.
        obtain ⟨n, hn⟩ : ∃ n : ℕ, K ⊆ Set.Icc (-n : ℝ) n := by
          exact hK.1.isBounded.exists_pos_norm_le.elim fun n hn => ⟨ ⌈n⌉₊, fun x hx => ⟨ neg_le_of_abs_le <| by simpa using hn.2 x hx |> le_trans <| Nat.le_ceil _, le_of_abs_le <| by simpa using hn.2 x hx |> le_trans <| Nat.le_ceil _ ⟩ ⟩;
        refine' ⟨ _, Or.inr ⟨ n, rfl ⟩, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
        · exact Or.inl rfl;
        · exact fun x hx => hK.2.2 x fun hx' => by linarith [ hx ( hn x hx' |>.1 ), hn x hx' |>.2 ] ;
      · have := hu.preimage ( OnePoint.continuous_coe );
        rcases ( TopologicalSpace.isBasis_countableBasis ℝ ).exists_subset_of_mem_open ( Set.mem_preimage.mpr ha ) this with ⟨ v, hv₁, hv₂, hv₃ ⟩ ; use OnePoint.some '' v ; aesop;
  · exact Set.Countable.union ( Set.Countable.image ( TopologicalSpace.countable_countableBasis ℝ ) _ ) ( Set.countable_range _ )

/-- **(A2)** Separability of the space `C₀(ℝ, ℝ)` of continuous real functions
vanishing at infinity, with its sup-norm topology. -/
instance separableSpace_zeroAtInfty :
    SeparableSpace (ZeroAtInftyContinuousMap ℝ ℝ) := by
  -- Define the extension-by-zero map Φ : ZeroAtInftyContinuousMap ℝ ℝ → C(OnePoint ℝ, ℝ).
  set Φ : ZeroAtInftyContinuousMap ℝ ℝ → C(OnePoint ℝ, ℝ) := fun f =>
    { toFun := fun p => p.elim 0 f,
      continuous_toFun := by
        rw [ OnePoint.continuous_iff ];
        convert f.zero_at_infty' using 1;
        norm_num [ Filter.Tendsto ];
        exact fun _ _ => f.continuous }
  generalize_proofs at *;
  -- Show that Φ is an isometry.
  have h_isometry : Isometry Φ := by
    refine' Isometry.of_dist_eq fun f g => _;
    refine' le_antisymm _ _;
    · refine' ContinuousMap.dist_le _ |>.2 fun p => _;
      · exact dist_nonneg;
      · rcases p with ( _ | x ) <;> simp +decide [ Φ ];
        · simp +decide [ OnePoint.elim ];
        · exact le_trans ( by simp +decide [ OnePoint.elim ] ) ( BoundedContinuousFunction.dist_coe_le_dist x );
    · refine' le_csInf _ _ <;> norm_num;
      · refine' ⟨ _, ⟨ _, fun x => _ ⟩ ⟩;
        exact dist f g;
        · exact dist_nonneg;
        · rcases x with ( _ | x ) <;> simp +decide [ Φ ];
          · simp +decide [ OnePoint.elim ];
          · exact le_trans ( by aesop ) ( BoundedContinuousFunction.dist_coe_le_dist x );
      · intro b hb h; exact (by
        refine' le_trans ( BoundedContinuousFunction.dist_le _ |>.2 _ ) _;
        exacts [ b, hb, fun x => by simpa using h ( OnePoint.some x ), le_rfl ])
  generalize_proofs at *;
  convert h_isometry.isEmbedding.separableSpace

/-! ### (A1) Separability of `𝓢(ℝ, ℝ)` via the weighted-derivative embedding

The maps `φ ↦ (x ↦ |x|^k · dⁿφ(x))` land in `C₀(ℝ, ℝ)` (Schwartz decay), realize
the Schwartz seminorms as sup-norms, and jointly embed `𝓢(ℝ, ℝ)` topologically
into the countable product `∏_{k,n} C₀(ℝ, ℝ)`.  Since `C₀(ℝ, ℝ)` is second
countable (separable metric), so is the countable product, and second
countability (hence separability) transfers back along the embedding. -/

/-- Continuity of the weighted derivative `x ↦ |x|^k · dⁿφ(x)`. -/
lemma continuous_weightedDerivFun (k n : ℕ) (φ : SchwartzMap ℝ ℝ) :
    Continuous (fun x => |x| ^ k * iteratedDeriv n φ x) := by
      convert Continuous.mul _ _ using 1;
      · infer_instance;
      · fun_prop;
      · convert φ.smooth'.continuous_iteratedDeriv _ _;
        exact_mod_cast le_top

/-- The weighted derivative `x ↦ |x|^k · dⁿφ(x)` vanishes at infinity. -/
lemma tendsto_weightedDerivFun (k n : ℕ) (φ : SchwartzMap ℝ ℝ) :
    Filter.Tendsto (fun x => |x| ^ k * iteratedDeriv n φ x) (Filter.cocompact ℝ) (𝓝 0) := by
  set C := SchwartzMap.seminorm ℝ (k + 1) n φ;
  -- By definition of $C$, we know that $|x|^{k+1} * |iteratedDeriv n φ x| ≤ C$ for all $x$.
  have h_bound : ∀ x : ℝ, |x|^(k + 1) * |iteratedDeriv n φ x| ≤ C := by
    intro x;
    convert SchwartzMap.le_seminorm ℝ ( k + 1 ) n φ x using 1;
    rw [ iteratedFDeriv_eq_equiv_comp ];
    simp +decide [ ContinuousMultilinearMap.piFieldEquiv ];
  -- Using the bound `h_bound`, we can show that the norm of the function is bounded by `C / |x|`.
  have h_norm_bound : ∀ᶠ x in cocompact ℝ, ‖|x|^k * iteratedDeriv n φ x‖ ≤ C / |x| := by
    simp +zetaDelta at *;
    exact ⟨ ⟨ -1, fun x hx => by rw [ le_div_iff₀ ( abs_pos.mpr <| by linarith ) ] ; convert h_bound x using 1 ; ring ⟩, ⟨ 1, fun x hx => by rw [ le_div_iff₀ ( abs_pos.mpr <| by linarith ) ] ; convert h_bound x using 1 ; ring ⟩ ⟩;
  exact squeeze_zero_norm' h_norm_bound ( tendsto_const_nhds.div_atTop <| tendsto_norm_cocompact_atTop )

/-- The weighted derivative `x ↦ |x|^k · dⁿφ(x)` as an element of `C₀(ℝ, ℝ)`. -/
noncomputable def weightedDerivC0 (k n : ℕ) (φ : SchwartzMap ℝ ℝ) :
    ZeroAtInftyContinuousMap ℝ ℝ where
  toFun x := |x| ^ k * iteratedDeriv n φ x
  continuous_toFun := continuous_weightedDerivFun k n φ
  zero_at_infty' := tendsto_weightedDerivFun k n φ

/-- Additivity of the weighted derivative in the Schwartz argument. -/
lemma weightedDerivC0_add (k n : ℕ) (φ ψ : SchwartzMap ℝ ℝ) :
    weightedDerivC0 k n (φ + ψ) = weightedDerivC0 k n φ + weightedDerivC0 k n ψ := by
      ext x; simp [weightedDerivC0, ZeroAtInftyContinuousMap.add_apply]; ring;
      rw [ ← mul_add, ← iteratedDeriv_add ];
      · rfl;
      · exact φ.smooth'.contDiffAt.of_le ( mod_cast le_top );
      · exact ψ.smooth'.contDiffAt.of_le ( mod_cast le_top )

/-- Homogeneity of the weighted derivative in the Schwartz argument. -/
lemma weightedDerivC0_smul (k n : ℕ) (c : ℝ) (φ : SchwartzMap ℝ ℝ) :
    weightedDerivC0 k n (c • φ) = c • weightedDerivC0 k n φ := by
      convert ZeroAtInftyContinuousMap.ext _ using 1;
      simp +decide [ weightedDerivC0 ];
      intro x; rw [ show ( c • φ : 𝓢(ℝ, ℝ) ) = fun x => c * φ x from rfl ] ; simp only [iteratedDeriv_const_mul_field]; ring;

/-- The joint weighted-derivative map, as a linear map into the countable product
`∏_{k,n} C₀(ℝ, ℝ)`. -/
noncomputable def weightedDerivLM :
    SchwartzMap ℝ ℝ →ₗ[ℝ] (Π _kn : ℕ × ℕ, ZeroAtInftyContinuousMap ℝ ℝ) where
  toFun φ := fun kn => weightedDerivC0 kn.1 kn.2 φ
  map_add' φ ψ := funext fun kn => weightedDerivC0_add kn.1 kn.2 φ ψ
  map_smul' c φ := funext fun kn => weightedDerivC0_smul kn.1 kn.2 c φ

/-
The sup-norm of the weighted derivative equals the Schwartz seminorm `p_{k,n}`.
-/
lemma norm_weightedDerivC0 (k n : ℕ) (φ : SchwartzMap ℝ ℝ) :
    ‖weightedDerivC0 k n φ‖ = SchwartzMap.seminorm ℝ k n φ := by
      refine' le_antisymm _ _;
      · convert BoundedContinuousFunction.norm_le ( apply_nonneg _ _ ) |>.2 _ using 1;
        · infer_instance;
        · convert SchwartzMap.le_seminorm ℝ k n φ using 1;
          simp +decide [ weightedDerivC0, iteratedFDeriv_eq_equiv_comp ];
      · refine' seminorm_le_bound ℝ k n φ ( norm_nonneg _ ) fun x => _;
        convert BoundedContinuousFunction.norm_coe_le_norm ( weightedDerivC0 k n φ |> ZeroAtInftyContinuousMap.toBCF ) x using 1;
        simp +decide [ weightedDerivC0, iteratedFDeriv_eq_equiv_comp ]

/-
The weighted-derivative map is a topological embedding: the Schwartz topology
coincides with the topology induced from the product of `C₀` spaces (the seminorm
families agree by `norm_weightedDerivC0`).
-/
lemma isInducing_weightedDerivLM : Topology.IsInducing (weightedDerivLM) := by
  refine' ⟨ _ ⟩;
  -- By definition of `weightedDerivLM`, we know that it is a linear map.
  set L : SchwartzMap ℝ ℝ →ₗ[ℝ] (Π kn : ℕ × ℕ, ZeroAtInftyContinuousMap ℝ ℝ) := weightedDerivLM;
  -- By definition of `L`, we know that it is a topological embedding.
  have h_embedding : Topology.IsInducing L := by
    have h_withSeminorms : WithSeminorms (topology := instTopologicalSpace ℝ ℝ) (schwartzSeminormFamily ℝ ℝ ℝ) := by
      convert schwartz_withSeminorms ℝ ℝ ℝ using 1
    have h_withSeminorms_L : WithSeminorms (topology := induced L (inferInstance : TopologicalSpace (Π kn : ℕ × ℕ, ZeroAtInftyContinuousMap ℝ ℝ))) (schwartzSeminormFamily ℝ ℝ ℝ) := by
      convert LinearMap.withSeminorms_induced _ L;
      rotate_left;
      exact fun kn => normSeminorm ℝ ( ZeroAtInftyContinuousMap ℝ ℝ ) |> Seminorm.comp <| LinearMap.proj kn;
      · convert withSeminorms_pi ( fun _ => norm_withSeminorms ℝ ( ZeroAtInftyContinuousMap ℝ ℝ ) ) using 1;
        swap;
        exact ℕ × ℕ;
        constructor <;> intro h <;> have := h;
        · convert withSeminorms_pi ( fun _ => norm_withSeminorms ℝ ( ZeroAtInftyContinuousMap ℝ ℝ ) ) using 1;
        · convert this.congr _ _;
          · intro kn; use { ⟨ kn, 0 ⟩ }, 1; simp +decide [ SeminormFamily.sigma ] ;
            exact fun x => by simp +decide [ SeminormFamily.comp ] ;
          · intro kn;
            use {kn.1}, 1;
            simp +decide [ SeminormFamily.sigma, SeminormFamily.comp ];
      · ext kn φ; simp +decide [ L, weightedDerivLM ] ;
        convert norm_weightedDerivC0 kn.1 kn.2 φ |> Eq.symm using 1;
    have := h_withSeminorms_L;
    cases this;
    rename_i h;
    constructor;
    convert h.symm using 1;
  exact h_embedding.eq_induced

/-- Separability of Schwartz space `𝓢(ℝ, ℝ)` on its canonical topology.
Mathlib has no such instance. -/
instance instSeparableSpace : SeparableSpace (SchwartzMap ℝ ℝ) := by
  haveI : SecondCountableTopology (Π _kn : ℕ × ℕ, ZeroAtInftyContinuousMap ℝ ℝ) :=
    inferInstance
  haveI := isInducing_weightedDerivLM.secondCountableTopology
  infer_instance

/-- Second countability of `𝓢(ℝ, ℝ)`: from separability and the countably
generated uniformity (M1). -/
instance instSecondCountableTopology : SecondCountableTopology (SchwartzMap ℝ ℝ) :=
  UniformSpace.secondCountable_of_separable _

/-- A named countable dense subset of `𝓢(ℝ, ℝ)`. -/
def denseSet : Set (SchwartzMap ℝ ℝ) :=
  (exists_countable_dense (SchwartzMap ℝ ℝ)).choose

theorem denseSet_countable : (denseSet).Countable :=
  (exists_countable_dense (SchwartzMap ℝ ℝ)).choose_spec.1

theorem denseSet_dense : Dense (denseSet) :=
  (exists_countable_dense (SchwartzMap ℝ ℝ)).choose_spec.2

/-
**(A3) Countable-reduction corollary.** For a continuous linear functional `F`
and a *continuous* seminorm `q`, the pointwise bound `|F φ| ≤ q φ` on a dense set
of `φ` already implies it for all `φ` (continuity of `F` and `q` plus density).
-/
theorem forall_le_of_forall_dense (F : SchwartzMap ℝ ℝ →L[ℝ] ℝ)
    (q : Seminorm ℝ (SchwartzMap ℝ ℝ)) (hq : Continuous q)
    {D : Set (SchwartzMap ℝ ℝ)} (hD : Dense D)
    (h : ∀ φ ∈ D, |F φ| ≤ q φ) : ∀ φ, |F φ| ≤ q φ := by
  have h_closed : IsClosed {φ : SchwartzMap ℝ ℝ | |F φ| ≤ q φ} := by
    exact isClosed_le ( F.continuous.norm ) hq;
  exact fun φ => h_closed.closure_subset_iff.mpr h ( hD.closure_eq ▸ Set.mem_univ φ )

/-! ## Part B: compact polars in the pointwise dual -/

/-- The pointwise (weak-*) dual of Schwartz space: continuous linear functionals
`𝓢(ℝ, ℝ) → ℝ` carrying Mathlib's pointwise-convergence topology. -/
abbrev SchDual : Type := SchwartzMap ℝ ℝ →Lₚₜ[ℝ] ℝ

/-- **(B1) Polar ball.** For a seminorm `q` on `𝓢(ℝ, ℝ)`, the set of dual
elements dominated by `q`. -/
def polarBall (q : Seminorm ℝ (SchwartzMap ℝ ℝ)) : Set SchDual :=
  {F | ∀ φ, |F φ| ≤ q φ}

theorem mem_polarBall {q : Seminorm ℝ (SchwartzMap ℝ ℝ)} {F : SchDual} :
    F ∈ polarBall q ↔ ∀ φ, |F φ| ≤ q φ := Iff.rfl

theorem zero_mem_polarBall (q : Seminorm ℝ (SchwartzMap ℝ ℝ)) :
    (0 : SchDual) ∈ polarBall q := by
  -- The zero functional satisfies |0(φ)| ≤ q(φ) for all φ because |0| = 0 and q(φ) is non-negative.
  simp [polarBall]

theorem polarBall_mono {q q' : Seminorm ℝ (SchwartzMap ℝ ℝ)} (h : q ≤ q') :
    polarBall q ⊆ polarBall q' := by
  exact fun F hF φ => le_trans ( hF φ ) ( h φ )

/-
**(B2) Compactness of polar balls.** For a *continuous* seminorm `q`, the
polar ball `polarBall q` is compact in the pointwise topology.  The proof pushes
through `PointwiseConvergenceCLM.isEmbedding_coeFn` into the product topology
`𝓢(ℝ, ℝ) → ℝ`: the image is the intersection of the (closed, coordinatewise)
linearity conditions with the pointwise bound, sitting inside the Tychonoff-compact
box `∏_φ [-q φ, q φ]`; a pointwise limit obeying the bound is automatically
continuous (dominated by the continuous seminorm `q`), so the image is closed and
compactness pulls back along the embedding.
-/
theorem isCompact_polarBall (q : Seminorm ℝ (SchwartzMap ℝ ℝ)) (hq : Continuous q) :
    IsCompact (polarBall q) := by
  have h_compact : IsCompact { f : SchwartzMap ℝ ℝ → ℝ | (∀ a b, f (a + b) = f a + f b) ∧ (∀ (c : ℝ) a, f (c • a) = c • f a) ∧ ∀ φ, |f φ| ≤ q φ } := by
    have h_closed : IsClosed { f : SchwartzMap ℝ ℝ → ℝ | (∀ a b, f (a + b) = f a + f b) ∧ (∀ (c : ℝ) a, f (c • a) = c • f a) ∧ ∀ φ, |f φ| ≤ q φ } := by
      simp +decide only [Set.setOf_and, Set.setOf_forall];
      apply_rules [ IsClosed.inter, isClosed_iInter ];
      · exact fun _ => isClosed_iInter fun _ => isClosed_eq ( continuous_apply _ ) ( Continuous.add ( continuous_apply _ ) ( continuous_apply _ ) );
      · exact fun _ => isClosed_iInter fun _ => isClosed_eq ( continuous_apply _ ) ( continuous_const.smul ( continuous_apply _ ) );
      · exact fun i => isClosed_le ( continuous_abs.comp ( continuous_apply i ) ) continuous_const;
    exact CompactIccSpace.isCompact_Icc.of_isClosed_subset h_closed fun f hf => ⟨ fun x => neg_le_of_abs_le <| hf.2.2 x, fun x => le_of_abs_le <| hf.2.2 x ⟩;
  have h_image : Set.image (fun F : SchDual => (F : SchwartzMap ℝ ℝ → ℝ)) (polarBall q) = { f : SchwartzMap ℝ ℝ → ℝ | (∀ a b, f (a + b) = f a + f b) ∧ (∀ (c : ℝ) a, f (c • a) = c • f a) ∧ ∀ φ, |f φ| ≤ q φ } := by
    ext f;
    constructor;
    · rintro ⟨ F, hF, rfl ⟩ ; exact ⟨ F.map_add, F.map_smul, hF ⟩ ;
    · intro hf
      obtain ⟨hf_add, hf_smul, hf_bound⟩ := hf
      have h_cont : Continuous f := by
        have h_cont : ContinuousAt f 0 := by
          have h_cont : Filter.Tendsto (fun φ => q φ) (nhds 0) (nhds 0) := by
            convert hq.tendsto 0 using 1 ; norm_num;
          exact tendsto_iff_norm_sub_tendsto_zero.mpr ( squeeze_zero ( fun _ => by positivity ) ( fun _ => by simpa [ show f 0 = 0 from by simpa using hf_add 0 0 ] using hf_bound _ ) h_cont );
        rw [ continuous_iff_continuousAt ];
        intro x; rw [ show f = fun y => f ( y - x ) + f x by ext y; simpa using hf_add ( y - x ) x ] ; exact ContinuousAt.add ( by exact ContinuousAt.comp ( by continuity ) ( continuousAt_id.sub continuousAt_const ) ) continuousAt_const;
      have h_linear : ∃ L : SchwartzMap ℝ ℝ →ₗ[ℝ] ℝ, f = L := by
        exact ⟨ { toFun := f, map_add' := hf_add, map_smul' := hf_smul }, rfl ⟩
      obtain ⟨L, hL⟩ := h_linear
      have h_clm : ∃ CL : SchwartzMap ℝ ℝ →L[ℝ] ℝ, f = CL := by
        exact ⟨ { toLinearMap := L, cont := by simpa [ hL ] using h_cont }, hL ⟩
      obtain ⟨CL, hCL⟩ := h_clm
      have h_polar : CL ∈ polarBall q := by
        exact fun φ => by simpa [ hCL ] using hf_bound φ;
      use CL
      aesop;
  convert h_compact.of_isClosed_subset _ _;
  convert ( PointwiseConvergenceCLM.isEmbedding_coeFn ( RingHom.id ℝ ) ( SchwartzMap ℝ ℝ ) ℝ ).isCompact_iff;
  · convert h_compact.isClosed using 1;
  · exact h_image.le

/-- The special *rational* seminorms: `c • (sup over a finite set of the canonical
Schwartz seminorm family)`, with `c : ℝ≥0`.  These are continuous. -/
noncomputable def ratSeminorm (c : ℝ≥0) (s : Finset (ℕ × ℕ)) : Seminorm ℝ (SchwartzMap ℝ ℝ) :=
  c • (Finset.sup s (schwartzSeminormFamily ℝ ℝ ℝ))

theorem continuous_ratSeminorm (c : ℝ≥0) (s : Finset (ℕ × ℕ)) :
    Continuous (ratSeminorm c s) := by
  -- The supremum of continuous functions is continuous.
  have h_sup_cont : Continuous (⇑(Finset.sup s (schwartzSeminormFamily ℝ ℝ ℝ))) := by
    induction s using Finset.induction <;> simp_all +decide [ Finset.sup_insert ];
    · fun_prop;
    · rename_i k s hk hs;
      exact Continuous.max ( by exact ( schwartz_withSeminorms ℝ ℝ ℝ ).continuous_seminorm k ) hs;
  convert h_sup_cont.const_smul c using 1

theorem isCompact_polarBall_ratSeminorm (c : ℝ≥0) (s : Finset (ℕ × ℕ)) :
    IsCompact (polarBall (ratSeminorm c s)) :=
  isCompact_polarBall _ (continuous_ratSeminorm c s)

/-
**(B3) Countable cofinal family.**  Every pointwise-bounded family in the
pointwise dual is contained in a compact polar ball of the special rational form
`ratSeminorm c s`.  Combines M1's Banach–Steinhaus dominating-seminorm corollary
with the `WithSeminorms` bound characterization of continuous seminorms.
-/
theorem pointwiseBounded_subset_compact_polarBall {ι : Type*} (𝓕 : ι → SchDual)
    (h : ∀ φ : SchwartzMap ℝ ℝ, ∃ C, ∀ i, |𝓕 i φ| ≤ C) :
    ∃ (c : ℝ≥0) (s : Finset (ℕ × ℕ)),
      IsCompact (polarBall (ratSeminorm c s)) ∧ ∀ i, 𝓕 i ∈ polarBall (ratSeminorm c s) := by
  obtain ⟨q, hq⟩ : ∃ q : Seminorm ℝ (SchwartzMap ℝ ℝ), Continuous q ∧ ∀ i φ, |𝓕 i φ| ≤ q φ := by
    -- Apply the Banach-Steinhaus theorem to obtain the existence of a continuous seminorm q that dominates the family.
    have := exists_continuous_seminorm_of_pointwise_bounded (fun i => (𝓕 i : SchwartzMap ℝ ℝ →L[ℝ] ℝ)) h;
    aesop;
  obtain ⟨s, C, hC0, hqle⟩ : ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ≥0, C ≠ 0 ∧ q ≤ C • (Finset.sup s (schwartzSeminormFamily ℝ ℝ ℝ)) := by
    convert Seminorm.bound_of_continuous ( schwartz_withSeminorms ℝ ℝ ℝ ) q hq.1 using 1;
  refine' ⟨ C, s, isCompact_polarBall_ratSeminorm C s, fun i => fun φ => le_trans ( hq.2 i φ ) ( hqle φ ) ⟩

/-
**(B4) Membership is countably checkable.** For a continuous seminorm `q` and a
dense set `D`, membership in `polarBall q` is decided by the bound on `D`.  Applied
with `D = denseSet` this is the measurability hook for task M3: the confinement
event is a countable intersection of evaluation events.
-/
theorem mem_polarBall_iff_dense (q : Seminorm ℝ (SchwartzMap ℝ ℝ)) (hq : Continuous q)
    {D : Set (SchwartzMap ℝ ℝ)} (hD : Dense D) (F : SchDual) :
    F ∈ polarBall q ↔ ∀ φ ∈ D, |F φ| ≤ q φ := by
  convert forall_le_of_forall_dense ( F : SchwartzMap ℝ ℝ →L[ℝ] ℝ ) q hq hD using 1;
  constructor <;> intro h <;> simp_all +decide [ polarBall ];
  exact ⟨ fun h' φ hφ => h' φ, fun h' => h h' ⟩

/-- Specialisation of `mem_polarBall_iff_dense` to the named countable dense set. -/
theorem mem_polarBall_iff_denseSet (q : Seminorm ℝ (SchwartzMap ℝ ℝ)) (hq : Continuous q)
    (F : SchDual) :
    F ∈ polarBall q ↔ ∀ φ ∈ denseSet, |F φ| ≤ q φ :=
  mem_polarBall_iff_dense q hq denseSet_dense F

end SchwartzMap