/-
# Mitoma campaign, task 3c — uniform dual-ball confinement

This file transcribes Mitoma's Lemmas (Ann. Probab. 11 (1983) Lemmas 3.2–3.3 and
J. Math. Soc. Japan 35 (1983) Lemmas 1–2) into the campaign's setting.

Setting (from M3b `TypeDDecouplingHermiteSobolev` and M2 `TypeDDecouplingSchwartzDual`):
* `sobolevSeminorm q` : the Hermite–Sobolev seminorm on `𝓢(ℝ,ℝ)`;
* `SchDual := 𝓢(ℝ,ℝ) →Lₚₜ[ℝ] ℝ` with `polarBall` and `isCompact_polarBall`.

Deliverables:
* (C1) the functional `M` with properties 1)–4), Xia's lemma (Baire), and the
  characteristic-functional bound (2.1);
* (C2) the Gaussian-averaging bound;
* (C3) `mitoma_confinement`.
-/
import Mathlib
import TypeDDecouplingHermiteSobolev
import TypeDDecouplingSchwartzDual

open MeasureTheory ProbabilityTheory Filter SchwartzMap
open TypeDDecouplingHermite TypeDDecouplingHermiteSobolev
open scoped Real Topology ENNReal NNReal

noncomputable section

namespace TypeDDecouplingMitomaCore

/-! ## Section A: the Hermite–Sobolev seminorm as a bundled `Seminorm`, and the
seminorm-convergent Hermite expansion. -/

/-- The `ℓ²`-sequence of weighted Hermite coefficients of `f`. -/
def sobolevSeq (r : ℕ) (f : 𝓢(ℝ, ℝ)) : ℕ → ℝ :=
  fun n => ((n : ℝ) + 1) ^ r * hermiteCoeffCLM n f

lemma sobolevSeq_memℓp (r : ℕ) (f : 𝓢(ℝ, ℝ)) : Memℓp (sobolevSeq r f) 2 := by
  have h_summable : Summable (fun n => ‖sobolevSeq r f n‖ ^ (2 : ℝ)) := by
    convert TypeDDecouplingHermiteSobolev.sobolev_summable r f using 1
    simp [sobolevSeq];
    ext; rw [ mul_pow, pow_mul' ] ; norm_cast ; ring;
    norm_num [ sq_abs ];
  simp_all +decide [ Memℓp, Real.rpow_two ]

/-- The weighted Hermite coefficients of `f` as an element of `ℓ²`. -/
def sobolevLp (r : ℕ) (f : 𝓢(ℝ, ℝ)) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨sobolevSeq r f, sobolevSeq_memℓp r f⟩

@[simp] lemma sobolevLp_coe (r : ℕ) (f : 𝓢(ℝ, ℝ)) (n : ℕ) :
    (sobolevLp r f : ℕ → ℝ) n = ((n : ℝ) + 1) ^ r * hermiteCoeffCLM n f := rfl

lemma norm_sobolevLp (r : ℕ) (f : 𝓢(ℝ, ℝ)) : ‖sobolevLp r f‖ = sobolevSeminorm r f := by
  convert lp.norm_eq_tsum_rpow ( p := 2 ) ( by norm_num ) ( sobolevLp r f ) using 1;
  -- By definition of `sobolevNormSq`, we have `sobolevNormSq r f = ∑' n, ((n : ℝ) + 1) ^ (2 * r) * (hermiteCoeffCLM n f) ^ 2`.
  simp [sobolevSeminorm, sobolevLp_coe];
  norm_num [ Real.sqrt_eq_rpow, mul_pow, abs_mul, abs_of_nonneg, add_nonneg ];
  norm_num [ ← pow_mul', sobolevNormSq ]

lemma sobolevLp_add (r : ℕ) (f g : 𝓢(ℝ, ℝ)) :
    sobolevLp r (f + g) = sobolevLp r f + sobolevLp r g := by
  ext n;
  simp +decide [ sobolevLp, sobolevSeq ];
  ring

lemma sobolevLp_smul (r : ℕ) (c : ℝ) (f : 𝓢(ℝ, ℝ)) :
    sobolevLp r (c • f) = c • sobolevLp r f := by
  -- By definition of `sobolevLp`, we have:
  ext n
  simp [sobolevLp, sobolevSeq];
  grind +splitImp

/-- The Hermite–Sobolev map `𝓢 → ℓ²` as a linear map. -/
def sobolevLM (r : ℕ) : 𝓢(ℝ, ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2 where
  toFun := sobolevLp r
  map_add' := sobolevLp_add r
  map_smul' := fun c f => sobolevLp_smul r c f

/-- The Hermite–Sobolev seminorm packaged as a `Seminorm`. -/
def sobolevSeminormB (r : ℕ) : Seminorm ℝ (𝓢(ℝ, ℝ)) :=
  (normSeminorm ℝ (lp (fun _ : ℕ => ℝ) 2)).comp (sobolevLM r)

@[simp] lemma sobolevSeminormB_apply (r : ℕ) (f : 𝓢(ℝ, ℝ)) :
    sobolevSeminormB r f = sobolevSeminorm r f := by
  convert norm_sobolevLp r f

lemma continuous_sobolevSeminormB (r : ℕ) : Continuous (sobolevSeminormB r) := by
  obtain ⟨ C, s, hC, hs ⟩ := TypeDDecouplingHermiteSobolev.sobolev_continuous r;
  convert Seminorm.continuous_of_le ( q := SchwartzMap.ratSeminorm C.toNNReal s ) _ _;
  · convert SchwartzMap.continuous_ratSeminorm C.toNNReal s using 1;
  · intro f; specialize hs f; simp_all +decide [ Seminorm.le_def ] ;
    convert hs using 1;
    convert Seminorm.smul_apply ( C.toNNReal ) ( s.sup ( fun i => SchwartzMap.seminorm ℝ i.1 i.2 ) ) f using 1;
    norm_num [ Algebra.smul_def, hC ]

/-
The Hermite–Sobolev seminorms increase with the level.
-/
lemma sobolevSeminorm_mono {r r' : ℕ} (h : r ≤ r') (f : 𝓢(ℝ, ℝ)) :
    sobolevSeminorm r f ≤ sobolevSeminorm r' f := by
  refine' Real.sqrt_le_sqrt _;
  apply_rules [ Summable.tsum_le_tsum ];
  · exact fun i => mul_le_mul_of_nonneg_right ( pow_le_pow_right₀ ( by linarith ) ( by linarith ) ) ( sq_nonneg _ );
  · convert TypeDDecouplingHermiteSobolev.sobolev_summable r f using 1;
  · convert TypeDDecouplingHermiteSobolev.sobolev_summable r' f using 1

/-
A finite sup of Schwartz seminorms is dominated by a single Hermite–Sobolev
seminorm.
-/
lemma exists_sobolev_dominates_finset_sup (s : Finset (ℕ × ℕ)) :
    ∃ (C : ℝ) (q : ℕ), 0 ≤ C ∧ ∀ φ : 𝓢(ℝ, ℝ),
      (s.sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2)) φ ≤ C * sobolevSeminorm q φ := by
  induction' s using Finset.induction with a s' ih;
  · refine' ⟨ 0, 0, _, _ ⟩ <;> norm_num;
  · rename_i h;
    obtain ⟨ C', q', hC', hq' ⟩ := h
    obtain ⟨ Cₐ, rₐ, hCₐ, hqₐ ⟩ := seminorm_le_sobolev a.1 a.2
    use max C' Cₐ, max q' rₐ, by positivity, by
      intro φ; rw [ Finset.sup_insert ] ; simp +decide [ * ] ;
      constructor;
      · exact le_trans ( hqₐ φ ) ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) ( by exact sobolevSeminorm_nonneg _ _ ) ) |> le_trans <| mul_le_mul_of_nonneg_left ( sobolevSeminorm_mono ( le_max_right _ _ ) _ ) ( by positivity );
      · refine' le_trans ( hq' φ ) _;
        exact mul_le_mul ( le_max_left _ _ ) ( sobolevSeminorm_mono ( le_max_left _ _ ) _ ) ( by exact sobolevSeminorm_nonneg _ _ ) ( by positivity )

/-! ### The seminorm-convergent Hermite expansion -/

/-- The `N`-th partial sum of the Hermite expansion of `f`, as a Schwartz map. -/
def hermitePartial (f : 𝓢(ℝ, ℝ)) (N : ℕ) : 𝓢(ℝ, ℝ) :=
  ∑ n ∈ Finset.range N, hermiteCoeffCLM n f • hermiteSchwartz n

lemma hermiteCoeff_hermitePartial (f : 𝓢(ℝ, ℝ)) (N n : ℕ) :
    hermiteCoeffCLM n (hermitePartial f N)
      = if n < N then hermiteCoeffCLM n f else 0 := by
  unfold hermitePartial;
  split_ifs <;> simp_all +decide [ Finset.sum_apply, hermiteCoeffCLM_hermiteSchwartz ]

/-
The Hermite–Sobolev tail seminorm of the partial sum error tends to `0`.
-/
lemma sobolev_tail_tendsto (r : ℕ) (f : 𝓢(ℝ, ℝ)) :
    Tendsto (fun N => sobolevSeminorm r (f - hermitePartial f N)) atTop (nhds 0) := by
  -- The series `n ↦ ((n:ℝ)+1)^(2*r)*(hermiteCoeffCLM n f)^2` is summable.
  have h_summable : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (2 * r) * (hermiteCoeffCLM n f) ^ 2) := by
    convert TypeDDecouplingHermiteSobolev.sobolev_summable r f using 1;
  -- By definition of `sobolevSeminorm`, we have:
  have h_sobolevSeminorm : ∀ N : ℕ, (sobolevSeminorm r (f - hermitePartial f N)) ^ 2 = ∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * r) * (if n < N then 0 else (hermiteCoeffCLM n f) ^ 2) := by
    intro N
    have h_sobolevSeminorm : (sobolevSeminorm r (f - hermitePartial f N)) ^ 2 = ∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * r) * (hermiteCoeffCLM n (f - hermitePartial f N)) ^ 2 := by
      rw [ ← Real.sq_sqrt ( show 0 ≤ ∑' n : ℕ, ( ( n : ℝ ) + 1 ) ^ ( 2 * r ) * ( hermiteCoeffCLM n ( f - hermitePartial f N ) ) ^ 2 from tsum_nonneg fun _ => by positivity ), sobolevSeminorm ];
      rfl;
    convert h_sobolevSeminorm using 3 ; simp +decide [ hermiteCoeff_hermitePartial ];
    split_ifs <;> ring;
  convert Filter.Tendsto.sqrt ( show Filter.Tendsto ( fun N => ∑' n : ℕ, ( ( n : ℝ ) + 1 ) ^ ( 2 * r ) * if n < N then 0 else ( hermiteCoeffCLM n f ) ^ 2 ) Filter.atTop ( nhds 0 ) from ?_ ) using 2;
  · rw [ ← h_sobolevSeminorm, Real.sqrt_sq ( by exact TypeDDecouplingHermiteSobolev.sobolevSeminorm_nonneg _ _ ) ];
  · norm_num;
  · convert tendsto_sum_nat_add fun n => ( n + 1 : ℝ ) ^ ( 2 * r ) * ( hermiteCoeffCLM n f ) ^ 2 using 1;
    ext N; rw [ ← Summable.sum_add_tsum_nat_add N ] ; norm_num [ Finset.sum_range, Nat.lt_succ_iff ] ;
    exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( pow_nonneg ( by positivity ) _ ) ( by split_ifs <;> positivity ) ) ( fun n => mul_le_mul_of_nonneg_left ( by split_ifs <;> nlinarith ) ( by positivity ) ) h_summable

/-
The Hermite partial sums converge to `f` in the Schwartz topology.
-/
lemma hermitePartial_tendsto (f : 𝓢(ℝ, ℝ)) :
    Tendsto (fun N => hermitePartial f N) atTop (nhds f) := by
  -- By definition of_shift_seminorm_bound, we know that the seminorm of the difference is bounded.
  have h_seminorm_diff : ∀ k m : ℕ, ∃ (C : ℝ) (r : ℕ), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℝ)), SchwartzMap.seminorm ℝ k m f ≤ C * sobolevSeminorm r f := by
    exact fun k m => TypeDDecouplingHermiteSobolev.seminorm_le_sobolev k m
  have h_tendsto : ∀ k m : ℕ, Tendsto (fun N => SchwartzMap.seminorm ℝ k m (hermitePartial f N - f)) atTop (nhds 0) := by
    intro k m
    obtain ⟨C, r, hC, h_bound⟩ := h_seminorm_diff k m;
    have h_tendsto : Tendsto (fun N => sobolevSeminorm r (hermitePartial f N - f)) atTop (nhds 0) := by
      convert sobolev_tail_tendsto r f using 1;
      ext N; exact (by
      unfold sobolevSeminorm; norm_num [ sobolevNormSq ] ;
      exact congr_arg Real.sqrt ( tsum_congr fun n => by ring ));
    exact squeeze_zero ( fun _ => by positivity ) ( fun N => h_bound _ ) ( by simpa using h_tendsto.const_mul C );
  rw [ schwartz_withSeminorms ℝ ℝ ℝ |> WithSeminorms.tendsto_nhds ];
  exact fun i ε hε => by simpa using h_tendsto i.1 i.2 |> fun h => h.eventually ( gt_mem_nhds hε ) ;

/-
Any pointwise-dual functional acts on `f` through its Hermite expansion.
-/
lemma schDual_apply_tendsto (F : SchDual) (f : 𝓢(ℝ, ℝ)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, hermiteCoeffCLM n f * F (hermiteSchwartz n))
      atTop (nhds (F f)) := by
  have h_tendsto : Filter.Tendsto (fun N => F (hermitePartial f N)) Filter.atTop (nhds (F f)) := by
    exact F.continuous.continuousAt.tendsto.comp ( hermitePartial_tendsto f );
  convert h_tendsto using 2 ; unfold hermitePartial ; simp +decide

/-
Weighted Cauchy–Schwarz bound for the partial sums of `F f`.
-/
lemma abs_schDual_partial_le (r N : ℕ) (F : SchDual) (f : 𝓢(ℝ, ℝ)) :
    |∑ n ∈ Finset.range N, hermiteCoeffCLM n f * F (hermiteSchwartz n)|
      ≤ sobolevSeminorm r f *
          Real.sqrt (∑ n ∈ Finset.range N,
            ((n : ℝ) + 1) ^ (-2 * (r : ℝ)) * (F (hermiteSchwartz n)) ^ 2) := by
  -- We'll use the fact that the sum of the squares of the coefficients is bounded by the Sobolev norm squared.
  have h_sum_sq : ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (2 * r) * (hermiteCoeffCLM n f) ^ 2 ≤ sobolevNormSq r f := by
    exact Summable.sum_le_tsum ( Finset.range N ) ( fun _ _ => mul_nonneg ( pow_nonneg ( by positivity ) _ ) ( sq_nonneg _ ) ) ( by exact sobolev_summable r f );
  -- Apply the Cauchy-Schwarz inequality to the sums.
  have h_cauchy_schwarz : (∑ n ∈ Finset.range N, (hermiteCoeffCLM n f) * F (hermiteSchwartz n)) ^ 2 ≤ (∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (2 * r) * (hermiteCoeffCLM n f) ^ 2) * (∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-2 * r : ℝ) * (F (hermiteSchwartz n)) ^ 2) := by
    convert Finset.sum_mul_sq_le_sq_mul_sq ( Finset.range N ) ( fun n => ( ( n : ℝ ) + 1 ) ^ r * hermiteCoeffCLM n f ) ( fun n => ( ( n : ℝ ) + 1 ) ^ ( -r : ℝ ) * F ( hermiteSchwartz n ) ) using 1;
    · norm_cast ; norm_num [ mul_assoc, mul_comm, mul_left_comm, pow_add, pow_mul, ne_of_gt ( Nat.cast_add_one_pos _ ) ];
    · norm_cast ; norm_num [ mul_pow, pow_mul' ];
      norm_num [ zpow_mul' ];
  convert Real.abs_le_sqrt h_cauchy_schwarz |> le_trans <| Real.sqrt_le_sqrt <| mul_le_mul_of_nonneg_right h_sum_sq <| Finset.sum_nonneg fun _ _ => ?_ using 1;
  · rw [ Real.sqrt_mul ( by exact tsum_nonneg fun _ => by positivity ), sobolevSeminorm ];
  · positivity

/-
**(C3 core)** If all partial confinement sums of `F` are `≤ C²`, then `F`
lies in the compact polar ball of radius `C` for the level-`r` Sobolev seminorm.
-/
lemma schDual_mem_polarBall_of_Qpart_le (r : ℕ) (C : ℝ) (hC : 0 ≤ C) (F : SchDual)
    (hQ : ∀ N, ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-2 * (r : ℝ)) * (F (hermiteSchwartz n)) ^ 2 ≤ C ^ 2) :
    F ∈ polarBall ((C.toNNReal) • sobolevSeminormB r) := by
  -- Take any `φ : 𝓢(ℝ, ℝ)`. We want to show `|F φ| ≤ C * sobolevSeminorm r φ`.
  intro φ;
  -- Bound the partial sums: for any `N`, `abs (∑ ..) ≤ sobolevSeminorm r φ * Real.sqrt (∑ ..)`.
  have hpart : ∀ N : ℕ,
    |∑ n ∈ Finset.range N, hermiteCoeffCLM n φ * F (hermiteSchwartz n)| ≤
      sobolevSeminorm r φ * Real.sqrt (C ^ 2) := by
        exact fun N => le_trans ( abs_schDual_partial_le r N F φ ) ( mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| hQ N ) <| by exact sobolevSeminorm_nonneg r φ );
  -- Use `schDual_apply_tendsto` to get convergence of partial sums, then take `|·|` and use `le_of_tendsto` using `hpart`.
  have hlim : Filter.Tendsto (fun N => |∑ n ∈ Finset.range N, hermiteCoeffCLM n φ * F (hermiteSchwartz n)|) atTop (nhds (|F φ|)) := by
    exact Filter.Tendsto.abs ( schDual_apply_tendsto F φ );
  convert le_of_tendsto_of_tendsto' hlim tendsto_const_nhds fun N => hpart N using 1 ; norm_num [ Real.sqrt_sq hC, sobolevSeminormB_apply ];
  rw [ mul_comm, Algebra.smul_def ] ; norm_num [ hC ]

/-! ## Section B: (C1) the functional `M`, Xia's lemma, and the characteristic
functional bound. -/

/-
**Xia's lemma** (Baire argument on the Fréchet space `𝓢`): a nonnegative,
subadditive, lower-semicontinuous `M` with `M(φ/n) → 0` for every `φ` is
continuous at `0`.
-/
lemma xia_lemma (M : 𝓢(ℝ, ℝ) → ℝ)
    (h0 : ∀ φ, 0 ≤ M φ)
    (hneg : ∀ φ, M (-φ) = M φ)
    (hsub : ∀ φ ψ, M (φ + ψ) ≤ M φ + M ψ)
    (hlsc : LowerSemicontinuous M)
    (hscale : ∀ φ, Tendsto (fun n : ℕ => M ((n : ℝ)⁻¹ • φ)) atTop (nhds 0)) :
    ContinuousAt M 0 := by
  have h_baire : ∀ ε > 0, ∃ k : ℕ, ∃ W : Set 𝓢(ℝ, ℝ), IsOpen W ∧ 0 ∈ W ∧ ∀ φ ∈ W, M φ ≤ 2 * ε := by
    intro ε hε_pos
    obtain ⟨k, W, hW_open, hW_subset⟩ : ∃ k : ℕ, ∃ W : Set 𝓢(ℝ, ℝ), IsOpen W ∧ W.Nonempty ∧ W ⊆ {φ | ∀ m ≥ k, M ((m : ℝ)⁻¹ • φ) ≤ ε} := by
      have h_baire : ∀ k : ℕ, IsClosed {φ | ∀ m ≥ k, M ((m : ℝ)⁻¹ • φ) ≤ ε} := by
        intro k
        have h_closed : ∀ m ≥ k, IsClosed {φ : 𝓢(ℝ, ℝ) | M ((m : ℝ)⁻¹ • φ) ≤ ε} := by
          intro m hm
          have h_closed : IsClosed {φ : 𝓢(ℝ, ℝ) | M φ ≤ ε} := by
            exact hlsc.isClosed_preimage ε;
          exact h_closed.preimage ( Continuous.smul continuous_const continuous_id' );
        simpa only [ Set.setOf_forall ] using isClosed_iInter fun m => isClosed_iInter fun hm => h_closed m hm;
      have h_baire : ⋃ k : ℕ, {φ | ∀ m ≥ k, M ((m : ℝ)⁻¹ • φ) ≤ ε} = Set.univ := by
        ext φ; simp [hscale];
        exact Filter.eventually_atTop.mp ( hscale φ |> fun h => h.eventually ( ge_mem_nhds hε_pos ) );
      have := @nonempty_interior_of_iUnion_of_closed;
      exact Exists.elim ( this ‹_› h_baire ) fun k hk => ⟨ k, interior { φ : 𝓢(ℝ, ℝ) | ∀ m ≥ k, M ( ( m : ℝ ) ⁻¹ • φ ) ≤ ε }, isOpen_interior, hk, interior_subset ⟩;
    obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ ∈ W, True := by
      exact ⟨ hW_subset.1.some, hW_subset.1.choose_spec, trivial ⟩;
    refine' ⟨ k + 1, ( fun χ => ( k + 1 : ℝ ) • χ + φ₀ ) ⁻¹' W, _, _, _ ⟩ <;> simp_all +decide [ Set.preimage ];
    · exact hW_open.preimage ( Continuous.add ( continuous_const.smul continuous_id' ) continuous_const );
    · intro φ hφ
      have hM_phi : M φ ≤ M ((k + 1 : ℝ)⁻¹ • ((k + 1 : ℝ) • φ + φ₀)) + M ((k + 1 : ℝ)⁻¹ • (-φ₀)) := by
        convert hsub _ _ using 1 ; norm_num [ ← smul_assoc, Nat.cast_add_one_ne_zero ];
      have := hW_subset.2 hφ ( k + 1 ) ( by linarith ) ; have := hW_subset.2 hφ₀ ( k + 1 ) ( by linarith ) ; simp_all +decide [ Nat.cast_add_one_ne_zero ] ; linarith;
  refine' Metric.tendsto_nhds.mpr _;
  -- Since $M(0) = 0$, we have $|M(x) - M(0)| = |M(x)|$.
  have hM0 : M 0 = 0 := by
    simpa using hscale 0;
  intro ε hε; rcases h_baire ( ε / 4 ) ( by positivity ) with ⟨ k, W, hW₁, hW₂, hW₃ ⟩ ; filter_upwards [ hW₁.mem_nhds hW₂ ] with x hx using abs_lt.mpr ⟨ by linarith [ h0 x, hM0 ], by linarith [ hW₃ x hx, h0 x, hM0 ] ⟩ ;

/-
A Schwartz-topology neighborhood of `0` on which `M ≤ c` contains a
Hermite–Sobolev ball.
-/
lemma exists_sobolev_ball_of_continuousAt_zero (M : 𝓢(ℝ, ℝ) → ℝ)
    (hM : ContinuousAt M 0) (hM0 : M 0 = 0) (c : ℝ) (hc : 0 < c) :
    ∃ (q : ℕ) (δ : ℝ), 0 < δ ∧ ∀ φ : 𝓢(ℝ, ℝ), sobolevSeminorm q φ < δ → M φ ≤ c := by
  -- By definition of continuity at a point, there exists a neighborhood $U$ of $0$ such that $M(U) \subseteq (-c, c)$.
  obtain ⟨U, hU⟩ : ∃ U : Set (SchwartzMap ℝ ℝ), U ∈ nhds 0 ∧ ∀ φ ∈ U, M φ < c := by
    exact ⟨ { φ | M φ < c }, hM.eventually ( gt_mem_nhds <| by linarith ), fun φ hφ => hφ ⟩;
  -- By definition of Schwartz topology, there exists a finite set of seminorms $s$ and a radius $r > 0$ such that the ball around $0$ with respect to these seminorms is contained in $U$.
  obtain ⟨s, r, hr_pos, hr⟩ : ∃ s : Finset (ℕ × ℕ), ∃ r : ℝ, 0 < r ∧ {φ : SchwartzMap ℝ ℝ | (s.sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2)) φ < r} ⊆ U := by
    have := ( schwartz_withSeminorms ℝ ℝ ℝ ).mem_nhds_iff 0 U; simp_all +decide [ Set.subset_def ] ;
    convert hU.1 using 1;
  obtain ⟨ C, q, hC, hq ⟩ := exists_sobolev_dominates_finset_sup s;
  refine' ⟨ q, r / ( C + 1 ), div_pos hr_pos ( by linarith ), fun φ hφ => le_of_lt ( hU.2 φ ( hr _ ) ) ⟩;
  exact lt_of_le_of_lt ( hq φ ) ( by rw [ lt_div_iff₀ ] at hφ <;> nlinarith )

/-
`‖1 - e^{i s}‖ ≤ |s|` for real `s`.
-/
lemma norm_one_sub_exp_le (s : ℝ) :
    ‖(1 : ℂ) - Complex.exp (Complex.I * (s : ℂ))‖ ≤ |s| := by
  -- Use the fact that `‖1 - exp(iθ)‖ = 2 * |sin(θ / 2)|` and `|sin(θ / 2)| ≤ |θ / 2|`.
  have h_sin : ‖1 - Complex.exp (Complex.I * s)‖ = 2 * |Real.sin (s / 2)| := by
    norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ];
    rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> norm_num [ Real.sin_sq, Real.cos_sq ] <;> ring_nf at * ; norm_num at *;
    exact Real.cos_le_one _
  have h_sin_le : |Real.sin (s / 2)| ≤ |s / 2| := by
    grind +suggestions
  simp_all +decide [ abs_div ];
  linarith

/-
The score function `x ↦ |x|/(1+|x|)` is subadditive.
-/
lemma frac_abs_add_le (a b : ℝ) :
    |a + b| / (1 + |a + b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := by
  rw [ div_add_div, div_le_div_iff₀ ] <;> try positivity;
  cases abs_cases ( a + b ) <;> cases abs_cases a <;> cases abs_cases b <;> nlinarith [ mul_nonneg ( abs_nonneg a ) ( abs_nonneg b ) ]

section Probability

variable {ι : Type*} {T : Type*} [Countable T] [Nonempty T]
variable {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
variable (P : (i : ι) → Measure (Ω i)) [hP : ∀ i, IsProbabilityMeasure (P i)]
variable (Z : (i : ι) → T → Ω i → SchDual)

/-- Per-`ω` supremum over the (countable) time set of the bounded score
`|⟨Z,φ⟩|/(1+|⟨Z,φ⟩|)`. -/
def bracketFun (i : ι) (φ : 𝓢(ℝ, ℝ)) (ω : Ω i) : ℝ :=
  ⨆ t : T, |Z i t ω φ| / (1 + |Z i t ω φ|)

/-- `M_i(φ) = ∫ bracketFun dP_i`. -/
def Mi (i : ι) (φ : 𝓢(ℝ, ℝ)) : ℝ := ∫ ω, bracketFun Z i φ ω ∂(P i)

/-- `M(φ) = sup_i M_i(φ)`. -/
def Mfun (φ : 𝓢(ℝ, ℝ)) : ℝ := ⨆ i, Mi P Z i φ

lemma bracketFun_nonneg (i : ι) (φ : 𝓢(ℝ, ℝ)) (ω : Ω i) : 0 ≤ bracketFun Z i φ ω := by
  -- The supremum of non-negative numbers is non-negative.
  apply Real.iSup_nonneg; intro t; exact div_nonneg (abs_nonneg _) (by positivity)

lemma bracketFun_le_one (i : ι) (φ : 𝓢(ℝ, ℝ)) (ω : Ω i) : bracketFun Z i φ ω ≤ 1 := by
  exact ciSup_le fun t => div_le_one_of_le₀ ( by linarith [ abs_nonneg ( Z i t ω φ ) ] ) ( by linarith [ abs_nonneg ( Z i t ω φ ) ] )

lemma measurable_bracketFun (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (i : ι) (φ : 𝓢(ℝ, ℝ)) : Measurable (bracketFun Z i φ) := by
  refine' Measurable.iSup _;
  exact fun t => Measurable.mul ( Measurable.norm ( hmeas i t φ ) ) ( Measurable.inv ( measurable_const.add ( Measurable.norm ( hmeas i t φ ) ) ) )

lemma integrable_bracketFun (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (i : ι) (φ : 𝓢(ℝ, ℝ)) : Integrable (bracketFun Z i φ) (P i) := by
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun ω => 1;
  · norm_num;
  · -- The function `bracketFun Z i φ` is measurable because it is the supremum of measurable functions.
    exact (measurable_bracketFun Z hmeas i φ).aestronglyMeasurable;
  · filter_upwards [ ] with ω using by rw [ Real.norm_of_nonneg ( bracketFun_nonneg Z i φ ω ) ] ; exact bracketFun_le_one Z i φ ω;

lemma Mi_nonneg (i : ι) (φ : 𝓢(ℝ, ℝ)) : 0 ≤ Mi P Z i φ := by
  -- Since the bracket function is non-negative, its integral is also non-negative.
  apply MeasureTheory.integral_nonneg_of_ae; exact Filter.Eventually.of_forall (fun ω => bracketFun_nonneg Z i φ ω)

lemma Mi_le_one (i : ι) (φ : 𝓢(ℝ, ℝ)) : Mi P Z i φ ≤ 1 := by
  refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
  refine' fun _ => 1;
  · exact Filter.Eventually.of_forall fun ω => bracketFun_nonneg _ _ _ _;
  · norm_num;
  · exact Filter.Eventually.of_forall fun ω => bracketFun_le_one Z i φ ω;
  · simp +decide [ hP i ]

lemma Mfun_nonneg (φ : 𝓢(ℝ, ℝ)) : 0 ≤ Mfun P Z φ := by
  -- Since each Mi P Z i φ is non-negative, their supremum is also non-negative.
  apply Real.iSup_nonneg; intro i; exact Mi_nonneg P Z i φ

lemma Mfun_le_one (φ : 𝓢(ℝ, ℝ)) : Mfun P Z φ ≤ 1 := by
  by_cases h : Nonempty ι;
  · exact ciSup_le fun i => Mi_le_one P Z i φ;
  · simp_all +decide [ Mfun ]

/-
Property 1): `M(-φ) = M(φ)`.
-/
lemma Mfun_neg (φ : 𝓢(ℝ, ℝ)) : Mfun P Z (-φ) = Mfun P Z φ := by
  grind +locals

/-
Property 2): subadditivity of `M`.
-/
lemma Mfun_subadditive (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (φ ψ : 𝓢(ℝ, ℝ)) : Mfun P Z (φ + ψ) ≤ Mfun P Z φ + Mfun P Z ψ := by
  have h_bracketFun_le_sum : ∀ i ω, bracketFun Z i (φ + ψ) ω ≤ bracketFun Z i φ ω + bracketFun Z i ψ ω := by
    intro i ω;
    refine' ciSup_le fun t => _;
    refine' le_trans _ ( add_le_add ( le_ciSup _ t ) ( le_ciSup _ t ) );
    · convert frac_abs_add_le ( ( Z i t ω ) φ ) ( ( Z i t ω ) ψ ) using 1 ; simp +decide [ map_add ];
    · exact ⟨ 1, Set.forall_mem_range.2 fun t => div_le_one_of_le₀ ( by linarith [ abs_nonneg ( Z i t ω φ ) ] ) ( by linarith [ abs_nonneg ( Z i t ω φ ) ] ) ⟩;
    · exact ⟨ 1, Set.forall_mem_range.2 fun t => div_le_one_of_le₀ ( by linarith [ abs_nonneg ( Z i t ω ψ ) ] ) ( by linarith [ abs_nonneg ( Z i t ω ψ ) ] ) ⟩;
  have h_Mi_le_sum : ∀ i, Mi P Z i (φ + ψ) ≤ Mi P Z i φ + Mi P Z i ψ := by
    intro i;
    refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
    refine' fun ω => bracketFun Z i φ ω + bracketFun Z i ψ ω;
    · exact Filter.Eventually.of_forall fun ω => bracketFun_nonneg _ _ _ _;
    · exact MeasureTheory.Integrable.add ( integrable_bracketFun P Z hmeas i φ ) ( integrable_bracketFun P Z hmeas i ψ );
    · exact Filter.Eventually.of_forall ( h_bracketFun_le_sum i );
    · rw [ MeasureTheory.integral_add ( integrable_bracketFun P Z hmeas i φ ) ( integrable_bracketFun P Z hmeas i ψ ) ];
      rfl;
  rcases isEmpty_or_nonempty ι with h | h;
  · simp +decide [ Mfun ];
  · convert ciSup_le fun i => ?_;
    · exact h;
    · exact le_trans ( h_Mi_le_sum i ) ( add_le_add ( le_ciSup ( show BddAbove ( Set.range ( fun i => Mi P Z i φ ) ) from ⟨ 1, Set.forall_mem_range.2 fun i => Mi_le_one P Z i φ ⟩ ) i ) ( le_ciSup ( show BddAbove ( Set.range ( fun i => Mi P Z i ψ ) ) from ⟨ 1, Set.forall_mem_range.2 fun i => Mi_le_one P Z i ψ ⟩ ) i ) )

/-
`M_i` as a `toReal` of a lower integral.
-/
lemma Mi_eq_lintegral_toReal (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (i : ι) (φ : 𝓢(ℝ, ℝ)) :
    Mi P Z i φ = (∫⁻ ω, ENNReal.ofReal (bracketFun Z i φ ω) ∂(P i)).toReal := by
  rw [ Mi, MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
  · exact Filter.Eventually.of_forall fun ω => bracketFun_nonneg Z i φ ω;
  · exact ( measurable_bracketFun Z hmeas i φ ).aestronglyMeasurable

/-
Fatou for the bracket integrand along a convergent sequence.
-/
lemma lintegral_bracketFun_liminf_le (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (i : ι) (φ₀ : 𝓢(ℝ, ℝ)) (φ : ℕ → 𝓢(ℝ, ℝ)) (hφ : Tendsto φ atTop (nhds φ₀)) :
    ∫⁻ ω, ENNReal.ofReal (bracketFun Z i φ₀ ω) ∂(P i)
      ≤ liminf (fun k => ∫⁻ ω, ENNReal.ofReal (bracketFun Z i (φ k) ω) ∂(P i)) atTop := by
  refine' le_trans ( MeasureTheory.lintegral_mono fun ω => _ ) ( MeasureTheory.lintegral_liminf_le' _ );
  · -- Since $\phi_k \to \phi_0$, we have $|Z_{i,t}(\phi_k)| \to |Z_{i,t}(\phi_0)|$ for each $t$.
    have h_pointwise : ∀ t, Filter.Tendsto (fun k => |(Z i t ω) (φ k)| / (1 + |(Z i t ω) (φ k)|)) Filter.atTop (nhds (|(Z i t ω) φ₀| / (1 + |(Z i t ω) φ₀|))) := by
      intro t;
      exact Filter.Tendsto.div ( Filter.Tendsto.abs ( Filter.Tendsto.comp ( ContinuousLinearMap.continuous _ |> Continuous.continuousAt ) hφ ) ) ( tendsto_const_nhds.add ( Filter.Tendsto.abs ( Filter.Tendsto.comp ( ContinuousLinearMap.continuous _ |> Continuous.continuousAt ) hφ ) ) ) ( by positivity );
    -- Since $\phi_k \to \phi_0$, we have $\sup_{t \in T} |Z_{i,t}(\phi_k)| / (1 + |Z_{i,t}(\phi_k)|) \geq |Z_{i,t}(\phi_0)| / (1 + |Z_{i,t}(\phi_0)|)$ for each $t$.
    have h_sup_ge : ∀ t, Filter.liminf (fun k => ENNReal.ofReal (bracketFun Z i (φ k) ω)) Filter.atTop ≥ ENNReal.ofReal (|(Z i t ω) φ₀| / (1 + |(Z i t ω) φ₀|)) := by
      intro t
      have h_sup_ge : ∀ k, ENNReal.ofReal (bracketFun Z i (φ k) ω) ≥ ENNReal.ofReal (|(Z i t ω) (φ k)| / (1 + |(Z i t ω) (φ k)|)) := by
        intro k;
        exact ENNReal.ofReal_le_ofReal ( le_ciSup ( show BddAbove ( Set.range ( fun t => |( Z i t ω ) ( φ k )| / ( 1 + |( Z i t ω ) ( φ k )| ) ) ) from ⟨ 1, Set.forall_mem_range.2 fun t => div_le_one_of_le₀ ( by linarith [ abs_nonneg ( ( Z i t ω ) ( φ k ) ) ] ) ( by linarith [ abs_nonneg ( ( Z i t ω ) ( φ k ) ) ] ) ⟩ ) t );
      refine' le_trans _ ( Filter.liminf_le_liminf ( Filter.eventually_atTop.mpr ⟨ 0, fun k hk => h_sup_ge k ⟩ ) );
      rw [ Filter.Tendsto.liminf_eq ( ENNReal.tendsto_ofReal ( h_pointwise t ) ) ];
    refine' le_of_forall_lt_imp_le_of_dense fun r hr => _;
    rcases ENNReal.lt_iff_exists_real_btwn.mp hr with ⟨ s, hs ⟩;
    rcases exists_lt_of_lt_ciSup ( show s < ⨆ t : T, |(Z i t ω) φ₀| / (1 + |(Z i t ω) φ₀|) from lt_of_not_ge fun h => hs.2.2.not_ge <| ENNReal.ofReal_le_ofReal h ) with ⟨ t, ht ⟩;
    exact le_trans hs.2.1.le ( le_trans ( ENNReal.ofReal_le_ofReal ht.le ) ( h_sup_ge t ) );
  · exact fun n => ( measurable_bracketFun Z hmeas i ( φ n ) |> Measurable.ennreal_ofReal |> Measurable.aemeasurable )

/-
Each `M_i` is lower semicontinuous.
-/
lemma lowerSemicontinuous_Mi (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (i : ι) : LowerSemicontinuous (Mi P Z i) := by
  intro φ₀ c hc
  by_contra h_contra;
  -- By definition of negation, there exists a sequence $\varphi_k \to \varphi_0$ such that $M_i(\varphi_k) \leq c$ for all $k$.
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → 𝓢(ℝ, ℝ), Filter.Tendsto φ Filter.atTop (nhds φ₀) ∧ ∀ k, Mi P Z i (φ k) ≤ c := by
    rw [ Filter.eventually_iff_exists_mem ] at h_contra;
    push_neg at h_contra;
    rcases ( nhds_basis_opens φ₀ ).exists_antitone_subbasis with ⟨ U, hU ⟩;
    choose f hf using fun n => h_contra ( U n ) ( hU.2.mem n );
    exact ⟨ f, hU.2.tendsto fun n => hf n |>.1, fun n => hf n |>.2 ⟩;
  have h_liminf : ∫⁻ ω, ENNReal.ofReal (bracketFun Z i φ₀ ω) ∂(P i) ≤ liminf (fun k => ∫⁻ ω, ENNReal.ofReal (bracketFun Z i (φ k) ω) ∂(P i)) atTop := by
    apply_rules [ lintegral_bracketFun_liminf_le ];
    exact hφ.1;
  have h_liminf_le : liminf (fun k => ∫⁻ ω, ENNReal.ofReal (bracketFun Z i (φ k) ω) ∂(P i)) atTop ≤ ENNReal.ofReal c := by
    refine' csSup_le _ _ <;> norm_num;
    · exact ⟨ 0, ⟨ 0, fun _ _ => zero_le _ ⟩ ⟩;
    · intro b k hk;
      refine' le_trans ( hk k le_rfl ) _;
      convert ENNReal.ofReal_le_ofReal ( hφ.2 k ) using 1;
      rw [ Mi_eq_lintegral_toReal ];
      · rw [ ENNReal.ofReal_toReal ];
        exact ne_of_lt ( MeasureTheory.Integrable.lintegral_lt_top ( by exact integrable_bracketFun P Z hmeas i ( φ k ) ) );
      · exact hmeas;
  have h_liminf_le : Mi P Z i φ₀ ≤ c := by
    rw [ Mi_eq_lintegral_toReal ];
    · convert ENNReal.toReal_mono _ ( h_liminf.trans h_liminf_le ) using 1;
      · rw [ ENNReal.toReal_ofReal ( le_trans ( by exact le_trans ( by norm_num ) ( Mi_nonneg P Z i ( φ 0 ) ) ) ( hφ.2 0 ) ) ];
      · exact ENNReal.ofReal_ne_top;
    · exact hmeas;
  linarith

/-
Property 3): `M` is lower semicontinuous.
-/
lemma lowerSemicontinuous_Mfun (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ)) :
    LowerSemicontinuous (Mfun P Z) := by
  convert lowerSemicontinuous_ciSup _ _;
  · exact fun φ => ⟨ 1, Set.forall_mem_range.2 fun i => Mi_le_one P Z i φ ⟩;
  · exact fun i => lowerSemicontinuous_Mi P Z hmeas i

/-
Property 4): `M(φ/n) → 0`, derived from the uniform sup-tightness (H).
-/
lemma Mfun_smul_tendsto_zero
    (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (H : ∀ (φ : 𝓢(ℝ, ℝ)) (ε : ℝ), 0 < ε → ∃ a : ℝ, 0 < a ∧
      ∀ i, (P i) {ω | ∃ t : T, a < |Z i t ω φ|} ≤ ENNReal.ofReal ε)
    (φ : 𝓢(ℝ, ℝ)) :
    Tendsto (fun n : ℕ => Mfun P Z ((n : ℝ)⁻¹ • φ)) atTop (nhds 0) := by
  -- Apply the squeeze theorem to conclude the proof.
  have h_squeeze : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Mfun P Z ((n : ℝ)⁻¹ • φ) ≤ ε := by
    intro ε hε
    obtain ⟨a, ha_pos, ha⟩ := H φ (ε / 2) (half_pos hε);
    -- For $n \geq 1$ with $a/n \leq \eta/2$, we have $|Z i t ω ((n:ℝ)⁻¹•φ)| \leq \eta/2 + \mathbf{1}_{\{ω|∃t,a<|Z i t ω φ|\}}(ω)$.
    have h_bound : ∀ n : ℕ, 1 ≤ n → a / (n : ℝ) ≤ ε / 2 → ∀ i, Mi P Z i ((n : ℝ)⁻¹ • φ) ≤ ε / 2 + (ENNReal.ofReal (ε / 2)).toReal := by
      intro n hn hn' i
      have h_bound : ∀ ω, bracketFun Z i ((n : ℝ)⁻¹ • φ) ω ≤ ε / 2 + Set.indicator {ω | ∃ t, a < |(Z i t ω) φ|} 1 ω := by
        intro ω
        simp [bracketFun];
        refine' ciSup_le fun t => _;
        by_cases h : ∃ t, a < |(Z i t ω) φ| <;> simp_all +decide [ div_le_iff₀ ];
        · exact le_add_of_nonneg_of_le ( by positivity ) ( div_le_one_of_le₀ ( by nlinarith [ inv_mul_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ), abs_nonneg ( ( Z i t ω ) φ ) ] ) ( by positivity ) );
        · rw [ div_le_iff₀ ] <;> nlinarith [ inv_pos.mpr ( by positivity : 0 < ( n : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ), h t, show ( n : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ a ( by positivity : ( n : ℝ ) ≠ 0 ), abs_nonneg ( ( Z i t ω ) φ ), mul_nonneg ( inv_nonneg.mpr ( by positivity : 0 ≤ ( n : ℝ ) ) ) ( abs_nonneg ( ( Z i t ω ) φ ) ) ];
      refine' le_trans ( MeasureTheory.integral_mono _ _ h_bound ) _;
      · apply_rules [ integrable_bracketFun ];
      · refine' MeasureTheory.Integrable.add _ _;
        · norm_num;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · exact MeasureTheory.integrable_const _;
          · simp +decide only [Set.setOf_exists];
            exact MeasurableSet.iUnion fun t => measurableSet_lt measurable_const ( hmeas i t φ |> Measurable.norm );
      · rw [ MeasureTheory.integral_add ] <;> norm_num;
        · rw [ MeasureTheory.integral_indicator ];
          · simp +decide [ MeasureTheory.measureReal_def ];
            exact ha i;
          · simp +decide only [Set.setOf_exists];
            exact MeasurableSet.iUnion fun t => measurableSet_lt measurable_const ( hmeas i t φ |> Measurable.norm );
        · refine' MeasureTheory.Integrable.indicator _ _;
          · exact MeasureTheory.integrable_const _;
          · simp +decide only [Set.setOf_exists];
            exact MeasurableSet.iUnion fun t => measurableSet_lt measurable_const ( hmeas i t φ |> Measurable.norm );
    refine' ⟨ ⌈a / ( ε / 2 ) ⌉₊ + 1, fun n hn => _ ⟩ ; specialize h_bound n ( by linarith ) _;
    · rw [ div_le_iff₀ ] <;> nlinarith [ Nat.le_ceil ( a / ( ε / 2 ) ), show ( n : ℝ ) ≥ ⌈a / ( ε / 2 ) ⌉₊ + 1 by exact_mod_cast hn, mul_div_cancel₀ a ( ne_of_gt ( half_pos hε ) ) ];
    · simp_all +decide [ Mfun ];
      cases isEmpty_or_nonempty ι <;> simp_all +decide [ ENNReal.toReal_ofReal ( half_pos hε |> le_of_lt ) ];
      · linarith;
      · exact ciSup_le h_bound;
  exact Metric.tendsto_atTop.mpr fun ε hε => by rcases h_squeeze ( ε / 2 ) ( half_pos hε ) with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => abs_lt.mpr ⟨ by linarith [ show 0 ≤ Mfun P Z ( ( n : ℝ ) ⁻¹ • φ ) from Mfun_nonneg P Z _ ], by linarith [ hN n hn ] ⟩ ⟩ ;

/-
Continuity of `M` at `0` (Xia's lemma applied to `M`).
-/
lemma Mfun_continuousAt_zero
    (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (H : ∀ (φ : 𝓢(ℝ, ℝ)) (ε : ℝ), 0 < ε → ∃ a : ℝ, 0 < a ∧
      ∀ i, (P i) {ω | ∃ t : T, a < |Z i t ω φ|} ≤ ENNReal.ofReal ε) :
    ContinuousAt (Mfun P Z) 0 := by
  exact xia_lemma (Mfun P Z) (Mfun_nonneg P Z) (Mfun_neg P Z)
    (Mfun_subadditive P Z hmeas) (lowerSemicontinuous_Mfun P Z hmeas)
    (Mfun_smul_tendsto_zero P Z hmeas H)

/-
The bad-event `{∃ t, a < |⟨Z,φ⟩|}` is measurable.
-/
lemma measurableSet_exists_gt (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (i : ι) (φ : 𝓢(ℝ, ℝ)) (a : ℝ) :
    MeasurableSet {ω | ∃ t : T, a < |Z i t ω φ|} := by
  simpa only [ Set.setOf_exists ] using MeasurableSet.iUnion fun t => measurableSet_lt measurable_const ( ( hmeas i t φ |> Measurable.norm ) )

/-
Markov-type bound: the mass of the level set is controlled by `M_i`.
-/
lemma measure_exists_gt_le_Mi (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (i : ι) (φ : 𝓢(ℝ, ℝ)) (a : ℝ) (ha : 0 < a) :
    (a / (1 + a)) * (P i {ω | ∃ t : T, a < |Z i t ω φ|}).toReal ≤ Mi P Z i φ := by
  -- By definition of $Mi$, we know that
  have hMi_def : ∫⁻ ω, ENNReal.ofReal (bracketFun Z i φ ω) ∂(P i) ≥ (ENNReal.ofReal (a / (1 + a))) * (P i) {ω | ∃ t, a < |(Z i t ω) φ|} := by
    have h_integral_ge : ∫⁻ ω in {ω | ∃ t, a < |(Z i t ω) φ|}, ENNReal.ofReal (bracketFun Z i φ ω) ∂(P i) ≥ ENNReal.ofReal (a / (1 + a)) * (P i) {ω | ∃ t, a < |(Z i t ω) φ|} := by
      have h_integral_ge : ∀ ω ∈ {ω | ∃ t, a < |(Z i t ω) φ|}, ENNReal.ofReal (bracketFun Z i φ ω) ≥ ENNReal.ofReal (a / (1 + a)) := by
        intro ω hω
        obtain ⟨t, ht⟩ := hω
        have h_le : a / (1 + a) ≤ |(Z i t ω) φ| / (1 + |(Z i t ω) φ|) := by
          rw [ div_le_div_iff₀ ] <;> nlinarith [ abs_nonneg ( ( Z i t ω ) φ ) ];
        exact ENNReal.ofReal_le_ofReal ( le_trans h_le ( le_ciSup ( show BddAbove ( Set.range ( fun t : T => |( Z i t ω ) φ| / ( 1 + |( Z i t ω ) φ| ) ) ) from ⟨ 1, Set.forall_mem_range.2 fun t => div_le_one_of_le₀ ( by linarith [ abs_nonneg ( ( Z i t ω ) φ ) ] ) ( by linarith [ abs_nonneg ( ( Z i t ω ) φ ) ] ) ⟩ ) t ) );
      refine' le_trans _ ( MeasureTheory.setLIntegral_mono_ae _ _ );
      rotate_left;
      use fun ω => ENNReal.ofReal ( a / ( 1 + a ) );
      · exact ENNReal.measurable_ofReal.comp_aemeasurable ( measurable_bracketFun Z hmeas i φ |> Measurable.aemeasurable ) |> fun h => h.mono_measure <| Measure.restrict_le_self;
      · exact Filter.Eventually.of_forall h_integral_ge;
      · simp +decide [ mul_comm ];
    exact h_integral_ge.trans ( MeasureTheory.setLIntegral_le_lintegral _ _ );
  convert ENNReal.toReal_mono _ hMi_def using 1 <;> norm_num [ Mi_eq_lintegral_toReal, hmeas ];
  · exact Or.inl ( by rw [ ENNReal.toReal_ofReal ( by positivity ) ] );
  · refine' ne_of_lt ( MeasureTheory.Integrable.lintegral_lt_top _ );
    convert integrable_bracketFun P Z hmeas i φ using 1

/-
The characteristic-functional integrand is bounded by `2`.
-/
lemma charFunctional_le_two (φ : 𝓢(ℝ, ℝ)) :
    (⨆ i, ∫ ω, (⨆ t : T, ‖(1 : ℂ) - Complex.exp (Complex.I * ((Z i t ω φ : ℝ) : ℂ))‖) ∂(P i)) ≤ 2 := by
  by_cases hIChance : Nonempty ι;
  · refine' ciSup_le fun i => _;
    refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
    refine' fun ω => 2;
    · exact Filter.Eventually.of_forall fun ω => Real.iSup_nonneg fun t => norm_nonneg _;
    · norm_num;
    · filter_upwards [ ] with ω using ciSup_le fun t => le_trans ( norm_sub_le _ _ ) ( by norm_num [ Complex.norm_exp ] );
    · simp +decide [ hP i ];
  · aesop

lemma Mfun_zero : Mfun P Z 0 = 0 := by
  -- By definition of $Mfun$, we know that $Mi P Z i 0 = 0$ for all $i$.
  have hMi_zero : ∀ i, Mi P Z i 0 = 0 := by
    intro i
    simp [Mi, bracketFun];
  cases isEmpty_or_nonempty ι <;> simp_all +decide [ Mfun ]

lemma Mi_le_Mfun (i : ι) (φ : 𝓢(ℝ, ℝ)) : Mi P Z i φ ≤ Mfun P Z φ := by
  -- By definition of supremum, we know that for any $i$, $Mi P Z i φ \leq Mfun P Z φ$.
  apply le_ciSup (show BddAbove (Set.range (fun i => Mi P Z i φ)) from by
                    exact ⟨ 1, Set.forall_mem_range.2 fun i => Mi_le_one P Z i φ ⟩) i

/-
Per-`i` characteristic-functional bound on the small-seminorm regime.
-/
lemma charFunctional_bound_per_i (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (i : ι) (φ : 𝓢(ℝ, ℝ)) (ε : ℝ) (d : ℝ) (hd : 0 < d)
    (hdε : d ≤ ε / 2) (hdsq : d * (1 + d) ≤ ε / 4) (hMi : Mi P Z i φ ≤ d ^ 2) :
    (∫ ω, (⨆ t : T, ‖(1 : ℂ) - Complex.exp (Complex.I * ((Z i t ω φ : ℝ) : ℂ))‖) ∂(P i)) ≤ ε := by
  refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
  refine' fun ω => ε / 2 + 2 * Set.indicator { ω | ∃ t : T, d < |Z i t ω φ| } ( fun _ => 1 ) ω;
  · exact Filter.Eventually.of_forall fun ω => Real.iSup_nonneg fun t => norm_nonneg _;
  · refine' MeasureTheory.Integrable.add _ _ <;> norm_num [ hdε ];
    refine' MeasureTheory.Integrable.const_mul _ _;
    refine' MeasureTheory.Integrable.indicator _ _ <;> norm_num [ hdε ];
    exact Measurable.exists fun t => measurableSet_lt measurable_const ( hmeas i t φ |> Measurable.norm ) |> MeasurableSet.mem;
  · filter_upwards [ ] with ω;
    by_cases h : ∃ t : T, d < |Z i t ω φ| <;> simp_all +decide;
    · refine' ciSup_le fun t => _;
      exact le_trans ( norm_sub_le _ _ ) ( by norm_num [ Complex.norm_exp ] ; linarith );
    · refine' ciSup_le fun t => _;
      exact le_trans ( norm_one_sub_exp_le _ ) ( by simpa [ abs_of_nonneg hd.le ] using h t |> le_trans <| by linarith );
  · rw [ MeasureTheory.integral_add, MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator ] <;> norm_num;
    · have := measure_exists_gt_le_Mi P Z hmeas i φ d hd;
      rw [ div_mul_eq_mul_div, div_le_iff₀ ] at this <;> nlinarith! [ show 0 ≤ ( P i ).real { ω | ∃ t, d < |( Z i t ω ) φ| } from ENNReal.toReal_nonneg ];
    · exact Measurable.exists fun t => measurableSet_lt measurable_const ( hmeas i t φ |> Measurable.norm ) |> MeasurableSet.mem;
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.integrable_indicator_iff _ |>.2 _;
      · exact MeasurableSet.congr ( MeasurableSet.iUnion fun t => measurableSet_lt measurable_const ( hmeas i t φ |> Measurable.norm ) ) ( by aesop );
      · norm_num

/-
**(C1) Characteristic-functional bound (source (2.1)).**
-/
theorem charFunctional_bound
    (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (H : ∀ (φ : 𝓢(ℝ, ℝ)) (ε : ℝ), 0 < ε → ∃ a : ℝ, 0 < a ∧
      ∀ i, (P i) {ω | ∃ t : T, a < |Z i t ω φ|} ≤ ENNReal.ofReal ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (q : ℕ) (δ : ℝ), 0 < δ ∧ ∀ φ : 𝓢(ℝ, ℝ),
      (⨆ i, ∫ ω, (⨆ t : T, ‖(1 : ℂ) - Complex.exp (Complex.I * ((Z i t ω φ : ℝ) : ℂ))‖) ∂(P i))
        ≤ ε + 2 * (sobolevSeminorm q φ) ^ 2 / δ ^ 2 := by
  set d := min (ε / 2) ((-1 + Real.sqrt (1 + ε)) / 2) with hd_def
  have hd_pos : 0 < d := by
    exact lt_min ( half_pos hε ) ( div_pos ( by nlinarith [ Real.sqrt_nonneg ( 1 + ε ), Real.sq_sqrt ( show 0 ≤ 1 + ε by linarith ) ] ) zero_lt_two )
  have hdε : d ≤ ε / 2 := by
    exact min_le_left _ _
  have hdsq : d * (1 + d) ≤ ε / 4 := by
    cases min_cases ( ε / 2 ) ( ( -1 + Real.sqrt ( 1 + ε ) ) / 2 ) <;> nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 1 + ε by linarith ) ];
  obtain ⟨q, δ, hδpos, hball⟩ := exists_sobolev_ball_of_continuousAt_zero (Mfun P Z) (Mfun_continuousAt_zero P Z hmeas H) (Mfun_zero P Z) (d^2) (by positivity);
  refine' ⟨ q, δ, hδpos, fun φ => _ ⟩;
  by_cases hφ : sobolevSeminorm q φ < δ;
  · have h_integral_bound : ∀ i, ∫ ω, (⨆ t : T, ‖(1 : ℂ) - Complex.exp (Complex.I * ((Z i t ω) φ))‖) ∂(P i) ≤ ε := by
      intro i
      apply charFunctional_bound_per_i P Z hmeas i φ ε d hd_pos hdε hdsq (by
      exact le_trans ( Mi_le_Mfun P Z i φ ) ( hball φ hφ ));
    by_cases h : Nonempty ι <;> simp_all +decide [ ciSup_le_iff ];
    · exact le_add_of_le_of_nonneg ( ciSup_le h_integral_bound ) ( by positivity );
    · positivity;
  · refine' le_trans ( charFunctional_le_two P Z φ ) _;
    rw [ add_div', le_div_iff₀ ] <;> nlinarith [ show 0 ≤ sobolevSeminorm q φ from by exact Real.sqrt_nonneg _ ]

/-! ## Section C: (C2) Gaussian averaging. -/

/-- The confinement partial sum `Q_N(t,ω) = ∑_{j<N} ⟨Z,e^r_j⟩²`. -/
def Qpart (r N : ℕ) (i : ι) (t : T) (ω : Ω i) : ℝ :=
  ∑ j ∈ Finset.range N, (Z i t ω (hermiteSobolevVec r j)) ^ 2

/-- The finite Gaussian test function `φ_y = ∑_{j<N} y_j e^r_j`. -/
def phiY (r N : ℕ) (y : Fin N → ℝ) : 𝓢(ℝ, ℝ) :=
  ∑ j : Fin N, y j • hermiteSobolevVec r (j : ℕ)

/-- The Hilbert–Schmidt constant `S = ∑_j ‖e^r_j‖_q²` (finite for `q+1 ≤ r`). -/
def Sconst (q r : ℕ) : ℝ := ∑' j : ℕ, (sobolevSeminorm q (hermiteSobolevVec r j)) ^ 2

/-- The Badrikian constant `√e/(√e−1)`. -/
def badrikianConst : ℝ := Real.sqrt (Real.exp 1) / (Real.sqrt (Real.exp 1) - 1)

lemma Qpart_eq_coeff_form (r N : ℕ) (i : ι) (t : T) (ω : Ω i) :
    Qpart Z r N i t ω
      = ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-2 * (r : ℝ)) * (Z i t ω (hermiteSchwartz n)) ^ 2 := by
  refine' Finset.sum_congr rfl fun j hj => _;
  rw [ show hermiteSobolevVec r j = ( ( j : ℝ ) + 1 ) ^ ( -r : ℝ ) • hermiteSchwartz j from rfl, map_smul ] ; norm_cast ; norm_num ; ring;
  norm_num [ zpow_mul' ] ; ring

lemma schDual_phiY (r N : ℕ) (y : Fin N → ℝ) (i : ι) (t : T) (ω : Ω i) :
    Z i t ω (phiY r N y) = ∑ j : Fin N, y j * Z i t ω (hermiteSobolevVec r (j : ℕ)) := by
  unfold phiY; simp +decide [ mul_comm ] ;

/-- Product Gaussian on `Fin N → ℝ`, each coordinate `N(0, 1/C²)`. -/
def gaussPi (C : ℝ) (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ : Fin N => gaussianReal 0 (Real.toNNReal (C⁻¹ ^ 2)))

instance instIsProbabilityMeasure_gaussPi (C : ℝ) (N : ℕ) :
    IsProbabilityMeasure (gaussPi C N) := by
  unfold gaussPi; infer_instance

/-
Second moments of the product Gaussian: `∫ y_j y_k = δ_{jk}/C²`.
-/
lemma gaussPi_moment (C : ℝ) (hC : 0 < C) (N : ℕ) (j k : Fin N) :
    ∫ y : (Fin N → ℝ), y j * y k ∂(gaussPi C N) = if j = k then (C ^ 2)⁻¹ else 0 := by
  by_cases h : j = k <;> simp_all +decide [ gaussPi ];
  · have h_integral : ∫ y : ℝ, y^2 ∂(gaussianReal 0 (Real.toNNReal (C⁻¹ ^ 2))) = (C ^ 2)⁻¹ := by
      have := @ProbabilityTheory.variance_id_gaussianReal 0 ( Real.toNNReal ( C⁻¹ ^ 2 ) );
      rw [ ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae ] at this;
      · convert this using 1 <;> norm_num [ Real.toNNReal_of_nonneg, sq_nonneg ];
      · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
      · exact Continuous.aestronglyMeasurable ( by continuity );
    have h_integral : ∫ y : Fin N → ℝ, y k ^ 2 ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 (Real.toNNReal (C⁻¹ ^ 2)))) = (∫ y : ℝ, y ^ 2 ∂(gaussianReal 0 (Real.toNNReal (C⁻¹ ^ 2)))) * (∏ i ∈ Finset.univ.erase k, ∫ y : ℝ, 1 ∂(gaussianReal 0 (Real.toNNReal (C⁻¹ ^ 2)))) := by
      have h_integral : ∫ y : Fin N → ℝ, y k ^ 2 ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 (Real.toNNReal (C⁻¹ ^ 2))) ) = ∏ i : Fin N, ∫ y : ℝ, (if i = k then y ^ 2 else 1) ∂(gaussianReal 0 (Real.toNNReal (C⁻¹ ^ 2))) := by
        rw [ ← MeasureTheory.integral_fintype_prod_eq_prod ];
        simp +decide [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
      rw [ h_integral, ← Finset.mul_prod_erase _ _ ( Finset.mem_univ k ) ];
      exact congrArg₂ _ ( by norm_num ) ( Finset.prod_congr rfl fun x hx => by aesop );
    simp_all +decide [ ← sq ];
  · have h_int : ∫ y : Fin N → ℝ, y j * y k ∂Measure.pi (fun _ : Fin N => gaussianReal 0 (C ^ 2)⁻¹.toNNReal) = (∫ y : ℝ, y ∂gaussianReal 0 (C ^ 2)⁻¹.toNNReal) * (∫ y : ℝ, y ∂gaussianReal 0 (C ^ 2)⁻¹.toNNReal) * (∏ l : Fin N, if l = j ∨ l = k then 1 else ∫ y : ℝ, 1 ∂gaussianReal 0 (C ^ 2)⁻¹.toNNReal) := by
      have h_int : ∫ y : Fin N → ℝ, y j * y k ∂Measure.pi (fun _ : Fin N => gaussianReal 0 (C ^ 2)⁻¹.toNNReal) = (∏ l : Fin N, ∫ y : ℝ, (if l = j then y else 1) * (if l = k then y else 1) ∂gaussianReal 0 (C ^ 2)⁻¹.toNNReal) := by
        rw [ ← MeasureTheory.integral_fintype_prod_eq_prod ];
        congr with y ; simp +decide [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne', h ];
        ring;
      rw [ h_int, Finset.prod_eq_mul_prod_diff_singleton <| Finset.mem_univ j ];
      rw [ Finset.prod_eq_mul_prod_diff_singleton <| Finset.mem_sdiff.mpr ⟨ Finset.mem_univ k, by aesop ⟩ ] ; aesop;
    aesop

/-
Product-Gaussian characteristic identity (cosine form).
-/
lemma integral_cos_gaussPi (C : ℝ) (hC : 0 < C) (N : ℕ) (u : Fin N → ℝ) :
    ∫ y : (Fin N → ℝ), Real.cos (∑ j, y j * u j) ∂(gaussPi C N)
      = Real.exp (-(∑ j, (u j) ^ 2) / (2 * C ^ 2)) := by
  convert congr_arg Complex.re ( show ∫ y : Fin N → ℝ, Complex.exp ( Complex.I * ( ∑ j : Fin N, y j * u j ) ) ∂gaussPi C N = Complex.exp ( ( -∑ j : Fin N, u j ^ 2 ) / ( 2 * C ^ 2 ) ) from ?_ ) using 1;
  · convert ( Complex.reCLM.integral_comp_comm _ );
    · norm_num [ Complex.exp_re ];
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun y => 1;
      · exact MeasureTheory.integrable_const _;
      · exact Continuous.aestronglyMeasurable ( by continuity );
      · norm_num [ Complex.norm_exp ];
  · norm_cast;
  · have h_char : ∀ j : Fin N, ∫ y : ℝ, Complex.exp (Complex.I * (y * u j)) ∂(gaussianReal 0 (Real.toNNReal (C⁻¹ ^ 2))) = Complex.exp (- (u j) ^ 2 / (2 * C ^ 2)) := by
      intro j;
      have := @charFun_gaussianReal 0 ( C⁻¹ ^ 2 |> Real.toNNReal ) ( u j ) ; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ;
      convert this using 1 <;> norm_num [ charFun, mul_comm ];
      rw [ max_eq_left ( by positivity ) ] ; norm_cast;
    have h_prod_char : ∫ y : Fin N → ℝ, ∏ j : Fin N, Complex.exp (Complex.I * (y j * u j)) ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 (Real.toNNReal (C⁻¹ ^ 2)))) = ∏ j : Fin N, ∫ y : ℝ, Complex.exp (Complex.I * (y * u j)) ∂(gaussianReal 0 (Real.toNNReal (C⁻¹ ^ 2))) := by
      rw [ ← MeasureTheory.integral_fintype_prod_eq_prod ];
    convert h_prod_char using 1;
    · simp +decide [ ← Complex.exp_sum, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, gaussPi ];
    · simp_all +decide [ Complex.exp_sum, neg_div, Finset.sum_div _ _ _ ];
      rw [ ← Complex.exp_sum, Finset.sum_neg_distrib ]

/-
The Gaussian averaging inequality (product identity + `1 - cos ≤ |1 - e^{i·}|`).
-/
lemma one_sub_exp_le_integral_gaussPi (C : ℝ) (hC : 0 < C) (N : ℕ) (u : Fin N → ℝ) :
    1 - Real.exp (-(∑ j, (u j) ^ 2) / (2 * C ^ 2))
      ≤ ∫ y : (Fin N → ℝ),
          ‖(1 : ℂ) - Complex.exp (Complex.I * ((∑ j, y j * u j : ℝ) : ℂ))‖ ∂(gaussPi C N) := by
  have h_cos : 1 - Real.exp (-(∑ j, (u j) ^ 2) / (2 * C ^ 2)) = ∫ y : Fin N → ℝ, (1 - Real.cos (∑ j, y j * u j)) ∂gaussPi C N := by
    rw [ MeasureTheory.integral_sub ] <;> norm_num [ integral_cos_gaussPi C hC N u ];
    refine' MeasureTheory.Integrable.mono' _ _ _;
    exacts [ fun _ => 1, MeasureTheory.integrable_const _, Continuous.aestronglyMeasurable ( Real.continuous_cos.comp <| continuous_finset_sum _ fun _ _ => continuous_apply _ |> Continuous.mul <| continuous_const ), Filter.Eventually.of_forall fun _ => Real.abs_cos_le_one _ ];
  refine' h_cos ▸ MeasureTheory.integral_mono_of_nonneg _ _ _;
  · exact Filter.Eventually.of_forall fun y => sub_nonneg_of_le ( Real.cos_le_one _ );
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun y => 2;
    · norm_num [ MeasureTheory.integrable_const_iff ];
    · exact Continuous.aestronglyMeasurable ( by continuity );
    · norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ];
      filter_upwards [ ] with x using by rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ) ] ; exact Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith only [ Real.cos_sq' ( ∑ j, x j * u j ) ] ⟩ ;
  · filter_upwards [ ] with y ; norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ];
    nlinarith only [ Real.cos_sq' ( ∑ j, y j * u j ), Real.sqrt_nonneg ( ( 1 - Real.cos ( ∑ j, y j * u j ) ) * ( 1 - Real.cos ( ∑ j, y j * u j ) ) + Real.sin ( ∑ j, y j * u j ) * Real.sin ( ∑ j, y j * u j ) ), Real.mul_self_sqrt ( by nlinarith only [ Real.cos_sq' ( ∑ j, y j * u j ) ] : 0 ≤ ( 1 - Real.cos ( ∑ j, y j * u j ) ) * ( 1 - Real.cos ( ∑ j, y j * u j ) ) + Real.sin ( ∑ j, y j * u j ) * Real.sin ( ∑ j, y j * u j ) ) ]

/-
The Gaussian average of `‖φ_y‖_q²` equals `(1/C²)·∑_{j<N} ‖e^r_j‖_q²`.
-/
lemma integral_sobolevSq_phiY (q r : ℕ) (C : ℝ) (hC : 0 < C) (N : ℕ) :
    ∫ y : (Fin N → ℝ), (sobolevSeminorm q (phiY r N y)) ^ 2 ∂(gaussPi C N)
      = (C ^ 2)⁻¹ * ∑ j : Fin N, (sobolevSeminorm q (hermiteSobolevVec r (j : ℕ))) ^ 2 := by
  trans ∫ y : Fin N → ℝ, ∑ j : Fin N, ∑ k : Fin N, y j * y k * inner ℝ (sobolevLp q (hermiteSobolevVec r j)) (sobolevLp q (hermiteSobolevVec r k)) ∂(gaussPi C N);
  · congr with y;
    have h_inner : sobolevLp q (phiY r N y) = ∑ j : Fin N, y j • sobolevLp q (hermiteSobolevVec r j) := by
      unfold phiY; simp +decide [ sobolevLp, map_sum ] ;
      ext; simp +decide [ sobolevSeq ] ;
      simp +decide only [Finset.mul_sum _ _ _, mul_left_comm];
    rw [ ← norm_sobolevLp, h_inner, norm_eq_sqrt_real_inner ];
    rw [ Real.sq_sqrt ( real_inner_self_nonneg ), sum_inner, Finset.sum_congr rfl fun i hi => inner_sum _ _ _ ] ; simp +decide [ inner_smul_left, inner_smul_right, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  · rw [ MeasureTheory.integral_finset_sum ];
    · rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ MeasureTheory.integral_finset_sum ] ;
      · rw [ Finset.sum_eq_single i ] <;> simp_all +decide [ MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul, gaussPi_moment ];
        · grind +suggestions;
        · aesop;
      · intro j hj; refine' MeasureTheory.Integrable.mul_const _ _; refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun a => a i ^ 2 + a j ^ 2;
        · refine' MeasureTheory.Integrable.add _ _;
          · have := gaussPi_moment C hC N i i; simp_all +decide [ MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ] ;
            contrapose! this;
            rw [ MeasureTheory.integral_undef ( by simpa only [ sq ] using this ) ] ; positivity;
          · have := @gaussPi_moment C hC N j j; simp_all +decide [ MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ] ;
            contrapose! this;
            rw [ MeasureTheory.integral_undef ( by simpa only [ sq ] using this ) ] ; positivity;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_pi_apply i ) ( measurable_pi_apply j ) );
        · filter_upwards [ ] with a using abs_le.mpr ⟨ by nlinarith only, by nlinarith only ⟩;
    · intro i hi;
      refine' MeasureTheory.integrable_finset_sum _ _;
      intro j hj
      have h_integrable : MeasureTheory.Integrable (fun y : Fin N → ℝ => y i * y j) (gaussPi C N) := by
        have := gaussPi_moment C hC N i j;
        contrapose! this;
        rw [ MeasureTheory.integral_undef this ] ; split_ifs <;> norm_num ; positivity;
        refine' this _;
        have h_integrable : ∀ i : Fin N, MeasureTheory.Integrable (fun y : Fin N → ℝ => y i ^ 2) (gaussPi C N) := by
          intro i; exact (by
          have := gaussPi_moment C hC N i i; simp_all +decide [ sq ] ;
          exact ( by by_contra h; rw [ MeasureTheory.integral_undef h ] at this; exact absurd this ( by positivity ) ));
        refine' MeasureTheory.Integrable.mono' ( h_integrable i |> fun hi => hi.add ( h_integrable j ) ) _ _;
        · exact MeasureTheory.AEStronglyMeasurable.mul ( measurable_pi_apply i |> Measurable.aestronglyMeasurable ) ( measurable_pi_apply j |> Measurable.aestronglyMeasurable );
        · filter_upwards [ ] with y using abs_le.mpr ⟨ by norm_num; nlinarith only, by norm_num; nlinarith only ⟩;
      exact h_integrable.mul_const _

/-
Coordinate products are integrable for the product Gaussian.
-/
lemma integrable_gaussPi_coord_mul (C : ℝ) (hC : 0 < C) (N : ℕ) (j k : Fin N) :
    Integrable (fun y : Fin N → ℝ => y j * y k) (gaussPi C N) := by
  have h_integrable : ∀ i : Fin N, MeasureTheory.Integrable (fun y : Fin N → ℝ => y i ^ 2) (gaussPi C N) := by
    intro i; exact (by
      have := gaussPi_moment C hC N i i; simp_all +decide [ sq ] ;
      exact ( by by_contra h; rw [ MeasureTheory.integral_undef h ] at this; exact absurd this ( by positivity ) ));
  refine' MeasureTheory.Integrable.mono' ( h_integrable j |> fun hi => hi.add ( h_integrable k ) ) _ _;
  · exact MeasureTheory.AEStronglyMeasurable.mul ( measurable_pi_apply j |> Measurable.aestronglyMeasurable ) ( measurable_pi_apply k |> Measurable.aestronglyMeasurable );
  · filter_upwards [ ] with y using abs_le.mpr ⟨ by norm_num; nlinarith only, by norm_num; nlinarith only ⟩

/-
The map `y ↦ ‖φ_y‖_q²` is integrable for the product Gaussian.
-/
lemma integrable_sobolevSq_phiY (q r N : ℕ) (C : ℝ) (hC : 0 < C) :
    Integrable (fun y : Fin N → ℝ => (sobolevSeminorm q (phiY r N y)) ^ 2) (gaussPi C N) := by
  by_contra h_not_integrable;
  -- By definition of $phiY$, we have $sobolevSeminorm q (phiY r N y) ^ 2 = int_X (sobolevLp q (phiY r N y) | sobolevLp q (phiY r N y))$.
  have h_eq : ∀ y : Fin N → ℝ, (sobolevSeminorm q (phiY r N y)) ^ 2 = ∑ j : Fin N, ∑ k : Fin N, y j * y k * inner ℝ (sobolevLp q (hermiteSobolevVec r j)) (sobolevLp q (hermiteSobolevVec r k)) := by
    intro y
    have h_inner : sobolevLp q (phiY r N y) = ∑ j : Fin N, y j • sobolevLp q (hermiteSobolevVec r j) := by
      unfold phiY; simp +decide [ sobolevLp, map_sum ] ;
      ext; simp +decide [ sobolevSeq ] ;
      simp +decide only [Finset.mul_sum _ _ _, mul_left_comm]
    rw [← norm_sobolevLp, h_inner, norm_eq_sqrt_real_inner]
    rw [Real.sq_sqrt (real_inner_self_nonneg)]
    rw [sum_inner, Finset.sum_congr rfl fun i hi => inner_sum _ _ _]
    simp +decide [inner_smul_left, inner_smul_right, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _];
  refine' h_not_integrable _;
  simp_rw +decide [ h_eq ];
  refine' MeasureTheory.integrable_finset_sum _ fun i hi => MeasureTheory.integrable_finset_sum _ fun j hj => _;
  exact MeasureTheory.Integrable.mul_const ( integrable_gaussPi_coord_mul C hC N i j ) _

/-- The Badrikian smoothed confinement functional `W_N(ω) = ⨆_t (1 - e^{-Q_N(t,ω)/2C²})`. -/
def Wfun (r N : ℕ) (C : ℝ) (i : ι) (ω : Ω i) : ℝ :=
  ⨆ t : T, (1 - Real.exp (-(Qpart Z r N i t ω) / (2 * C ^ 2)))

lemma Qpart_nonneg (r N : ℕ) (i : ι) (t : T) (ω : Ω i) : 0 ≤ Qpart Z r N i t ω := by
  -- Since each term in the sum is a square, which is always non-negative, the entire sum must be non-negative.
  apply Finset.sum_nonneg; intro j _; exact pow_two_nonneg _

lemma Qpart_mono (r : ℕ) (i : ι) (t : T) (ω : Ω i) {N M : ℕ} (h : N ≤ M) :
    Qpart Z r N i t ω ≤ Qpart Z r M i t ω := by
  -- Apply the fact that the sum of non-negative terms is monotone.
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _ => sq_nonneg _)

lemma Wfun_nonneg (r N : ℕ) (C : ℝ) (i : ι) (ω : Ω i) : 0 ≤ Wfun Z r N C i ω := by
  exact Real.iSup_nonneg fun t => sub_nonneg.2 <| Real.exp_le_one_iff.2 <| by exact div_nonpos_of_nonpos_of_nonneg ( neg_nonpos.2 <| Qpart_nonneg Z r N i t ω ) <| by positivity;

lemma Wfun_le_one (r N : ℕ) (C : ℝ) (i : ι) (ω : Ω i) : Wfun Z r N C i ω ≤ 1 := by
  -- Since each term in the supremum is less than or equal to 1, the supremum itself is less than or equal to 1.
  apply ciSup_le; intro t; exact sub_le_self _ (Real.exp_nonneg _)

lemma measurable_Wfun (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (r N : ℕ) (C : ℝ) (i : ι) : Measurable (Wfun Z r N C i) := by
  convert Measurable.iSup ?_;
  all_goals try infer_instance;
  intro t;
  exact Measurable.sub measurable_const ( Measurable.exp ( Measurable.div_const ( Measurable.neg ( by exact Finset.measurable_sum _ fun j _ => by exact Measurable.pow_const ( hmeas i t _ ) _ ) ) _ ) )

/-
Badrikian/Markov step (source (2.5)).
-/
lemma badrikian_indicator (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (r N : ℕ) (C : ℝ) (hC : 0 < C) (i : ι) :
    badrikianConst⁻¹ * ((P i) {ω | ∃ t : T, C ^ 2 < Qpart Z r N i t ω}).toReal
      ≤ ∫ ω, Wfun Z r N C i ω ∂(P i) := by
  convert MeasureTheory.integral_mono _ _ _ using 1;
  any_goals try infer_instance;
  case convert_11 => exact fun ω => badrikianConst⁻¹ * Set.indicator { ω | ∃ t, C ^ 2 < Qpart Z r N i t ω } ( fun _ => 1 ) ω;
  · rw [ MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator ] <;> norm_num;
    · exact Or.inl rfl;
    · exact Measurable.exists fun t => measurableSet_lt measurable_const ( Finset.measurable_sum _ fun j _ => Measurable.pow_const ( hmeas i t _ ) _ ) |> MeasurableSet.mem;
  · refine' MeasureTheory.Integrable.const_mul _ _;
    refine' MeasureTheory.Integrable.indicator _ _;
    · norm_num;
    · simp +decide only [Set.setOf_exists];
      exact MeasurableSet.iUnion fun t => measurableSet_lt measurable_const ( show Measurable fun ω => Qpart Z r N i t ω from by exact Finset.measurable_sum _ fun j _ => by exact Measurable.pow_const ( hmeas i t _ ) _ );
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun ω => 1;
    · norm_num;
    · exact Measurable.aestronglyMeasurable ( measurable_Wfun Z hmeas r N C i );
    · filter_upwards [ ] with ω using by rw [ Real.norm_of_nonneg ( Wfun_nonneg Z r N C i ω ) ] ; exact Wfun_le_one Z r N C i ω;
  · intro ω; by_cases h : ∃ t, C ^ 2 < Qpart Z r N i t ω <;> simp +decide [ h ] ;
    · obtain ⟨ t, ht ⟩ := h
      have h_exp : 1 - Real.exp (-(Qpart Z r N i t ω) / (2 * C ^ 2)) ≥ badrikianConst⁻¹ := by
        have h_exp : 1 - Real.exp (-1 / 2) = badrikianConst⁻¹ := by
          unfold badrikianConst; norm_num [ Real.exp_neg, Real.exp_half ] ; ring;
          rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr ( Real.exp_pos 1 ) ) ) ];
        exact h_exp ▸ sub_le_sub_left ( Real.exp_le_exp.mpr ( by rw [ div_le_div_iff₀ ] <;> nlinarith ) ) _;
      exact le_trans h_exp ( le_ciSup ( show BddAbove ( Set.range ( fun t : T => 1 - Real.exp ( -Qpart Z r N i t ω / ( 2 * C ^ 2 ) ) ) ) from ⟨ 1, Set.forall_mem_range.2 fun t => sub_le_self _ ( Real.exp_nonneg _ ) ⟩ ) t );
    · exact Wfun_nonneg Z r N C i ω

/-
Gaussian-averaging heart (source (2.6)–(2.9)): bound `∫ W_N` via the char
functional bound at the finite Gaussian test functions.
-/
lemma integral_Wfun_le (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (q : ℕ) (δ ε : ℝ) (hδ : 0 < δ)
    (hchar : ∀ φ : 𝓢(ℝ, ℝ),
      (⨆ i, ∫ ω, (⨆ t : T, ‖(1 : ℂ) - Complex.exp (Complex.I * ((Z i t ω φ : ℝ) : ℂ))‖) ∂(P i))
        ≤ ε + 2 * (sobolevSeminorm q φ) ^ 2 / δ ^ 2)
    (C : ℝ) (hC : 0 < C) (i : ι) (N : ℕ) :
    (∫ ω, Wfun Z (q + 1) N C i ω ∂(P i)) ≤ ε + (2 / δ ^ 2) * (Sconst q (q + 1) / C ^ 2) := by
  refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
  refine' fun ω => ∫ y : Fin N → ℝ, ⨆ t : T, ‖1 - Complex.exp ( Complex.I * ( ∑ j : Fin N, y j * ( Z i t ω ( hermiteSobolevVec ( q + 1 ) j ) ) ) )‖ ∂gaussPi C N;
  · exact Filter.Eventually.of_forall fun ω => Wfun_nonneg _ _ _ _ _ _;
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun ω => 2;
    · norm_num;
    · refine' MeasureTheory.StronglyMeasurable.aestronglyMeasurable _;
      refine' MeasureTheory.StronglyMeasurable.integral_prod_right _;
      fun_prop (disch := solve_by_elim);
    · refine' Filter.Eventually.of_forall fun ω => _;
      refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
      refine' fun _ => 2;
      · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · filter_upwards [ ] with x;
        rw [ Real.norm_of_nonneg ( Real.iSup_nonneg fun _ => norm_nonneg _ ) ];
        refine' ciSup_le fun t => _;
        exact le_trans ( norm_sub_le _ _ ) ( by norm_num [ Complex.norm_exp ] );
      · simp +decide [ gaussPi ];
  · filter_upwards [ ] with ω;
    refine' ciSup_le fun t => _;
    refine' le_trans _ ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
    convert one_sub_exp_le_integral_gaussPi C hC N ( fun j => ( Z i t ω ) ( hermiteSobolevVec ( q + 1 ) j ) ) using 1;
    · simp +decide [ Qpart, Finset.sum_range ];
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun y => 2;
      · fun_prop;
      · refine' Measurable.aestronglyMeasurable _;
        fun_prop;
      · refine' Filter.Eventually.of_forall fun y => _;
        rw [ Real.norm_of_nonneg ( Real.iSup_nonneg fun _ => norm_nonneg _ ) ];
        refine' ciSup_le fun t => _;
        exact le_trans ( norm_sub_le _ _ ) ( by norm_num [ Complex.norm_exp ] );
    · filter_upwards [ ] with y using le_ciSup ( show BddAbove ( Set.range fun t : T => ‖1 - Complex.exp ( Complex.I * ↑ ( ∑ j : Fin N, y j * ( Z i t ω ) ( hermiteSobolevVec ( q + 1 ) j ) ) )‖ ) from ⟨ 2, Set.forall_mem_range.2 fun t => by simpa using norm_sub_le ( 1 : ℂ ) ( Complex.exp _ ) |> le_trans <| by norm_num [ Complex.norm_exp ] ⟩ ) t;
  · rw [ MeasureTheory.integral_integral_swap ];
    · refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
      use fun y => ε + 2 * ( sobolevSeminorm q ( phiY ( q + 1 ) N y ) ) ^ 2 / δ ^ 2;
      · exact Filter.Eventually.of_forall fun y => MeasureTheory.integral_nonneg fun ω => Real.iSup_nonneg fun t => norm_nonneg _;
      · refine' MeasureTheory.Integrable.add _ _;
        · simp +decide [ MeasureTheory.integrable_const_iff ];
        · exact MeasureTheory.Integrable.div_const ( MeasureTheory.Integrable.const_mul ( integrable_sobolevSq_phiY q ( q + 1 ) N C hC ) _ ) _;
      · filter_upwards [ ] with y;
        refine' le_trans _ ( hchar ( phiY ( q + 1 ) N y ) );
        refine' le_trans _ ( le_ciSup _ i );
        · simp +decide [ phiY, schDual_phiY ];
        · refine' ⟨ 2, Set.forall_mem_range.2 fun i => _ ⟩;
          refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
          refine' fun ω => 2;
          · exact Filter.Eventually.of_forall fun ω => Real.iSup_nonneg fun t => norm_nonneg _;
          · norm_num;
          · filter_upwards [ ] with ω using ciSup_le fun t => le_trans ( norm_sub_le _ _ ) ( by norm_num [ Complex.norm_exp ] );
          · norm_num [ hP i ];
      · rw [ MeasureTheory.integral_add, MeasureTheory.integral_div, MeasureTheory.integral_const_mul ] <;> norm_num;
        · rw [ integral_sobolevSq_phiY ];
          · rw [ Sconst ] ; ring_nf ; norm_num;
            rw [ mul_right_comm ];
            exact mul_le_mul_of_nonneg_left ( Summable.sum_le_tsum ( Finset.range N ) ( fun _ _ => sq_nonneg _ ) ( by exact hermiteSobolev_hs_summable q ( 1 + q ) ( by linarith ) ) |> le_trans ( by simp +decide [ Finset.sum_range ] ) ) ( by positivity );
          · exact hC;
        · exact MeasureTheory.Integrable.div_const ( MeasureTheory.Integrable.const_mul ( integrable_sobolevSq_phiY q ( q + 1 ) N C hC ) _ ) _;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => 2;
      · norm_num;
      · refine' Measurable.aestronglyMeasurable _;
        fun_prop;
      · refine' Filter.Eventually.of_forall fun x => _;
        refine' abs_le.mpr ⟨ _, _ ⟩;
        · exact le_trans ( by norm_num ) ( Real.iSup_nonneg fun _ => norm_nonneg _ );
        · refine' ciSup_le fun t => _;
          exact le_trans ( norm_sub_le _ _ ) ( by norm_num [ Complex.norm_exp ] )

/-
**(C2)** Gaussian-averaging bound.
-/
theorem gaussian_confinement_bound
    (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (H : ∀ (φ : 𝓢(ℝ, ℝ)) (ε : ℝ), 0 < ε → ∃ a : ℝ, 0 < a ∧
      ∀ i, (P i) {ω | ∃ t : T, a < |Z i t ω φ|} ≤ ENNReal.ofReal ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (q : ℕ) (δ : ℝ), 0 < δ ∧ ∀ (C : ℝ), 0 < C → ∀ i,
      ((P i) {ω | ∃ (t : T) (N : ℕ), C ^ 2 < Qpart Z (q + 1) N i t ω}).toReal
        ≤ badrikianConst * (ε + (2 / δ ^ 2) * (Sconst q (q + 1) / C ^ 2)) := by
  obtain ⟨ q, δ, hδ, hchar ⟩ := charFunctional_bound P Z hmeas H ε hε;
  refine' ⟨ q, δ, hδ, _ ⟩;
  intro C hC i
  have h_union : (P i) {ω | ∃ t N, C ^ 2 < Qpart Z (q + 1) N i t ω} = ⨆ N : ℕ, (P i) {ω | ∃ t, C ^ 2 < Qpart Z (q + 1) N i t ω} := by
    rw [ show { ω | ∃ t N, C ^ 2 < Qpart Z ( q + 1 ) N i t ω } = ⋃ N, { ω | ∃ t, C ^ 2 < Qpart Z ( q + 1 ) N i t ω } by ext; aesop ];
    have h_monotone : Monotone (fun N => {ω | ∃ t, C ^ 2 < Qpart Z (q + 1) N i t ω}) := by
      exact fun N M hNM ω hω => by obtain ⟨ t, ht ⟩ := hω; exact ⟨ t, lt_of_lt_of_le ht ( Qpart_mono Z ( q + 1 ) i t ω hNM ) ⟩ ;
    exact Monotone.measure_iUnion h_monotone;
  rw [ h_union, ENNReal.toReal_iSup ];
  · refine' ciSup_le fun N => _;
    have := badrikian_indicator P Z hmeas ( q + 1 ) N C hC i;
    have := integral_Wfun_le P Z hmeas q δ ε hδ hchar C hC i N;
    rw [ inv_mul_le_iff₀ ( show 0 < badrikianConst from by exact div_pos ( Real.sqrt_pos.mpr ( Real.exp_pos 1 ) ) ( sub_pos.mpr ( Real.lt_sqrt_of_sq_lt ( by norm_num ) ) ) ) ] at * ; nlinarith [ show 0 < badrikianConst from by exact div_pos ( Real.sqrt_pos.mpr ( Real.exp_pos 1 ) ) ( sub_pos.mpr ( Real.lt_sqrt_of_sq_lt ( by norm_num ) ) ) ];
  · exact fun N => MeasureTheory.measure_ne_top _ _

/-! ## Section D: (C3) the confinement theorem. -/

/-
**(C3)** `mitoma_confinement`: uniform dual-ball confinement with high probability.
-/
theorem mitoma_confinement
    (hmeas : ∀ i t φ, Measurable (fun ω => Z i t ω φ))
    (H : ∀ (φ : 𝓢(ℝ, ℝ)) (ε : ℝ), 0 < ε → ∃ a : ℝ, 0 < a ∧
      ∀ i, (P i) {ω | ∃ t : T, a < |Z i t ω φ|} ≤ ENNReal.ofReal ε)
    (η : ℝ) (hη : 0 < η) :
    ∃ (q : ℕ) (B : ℝ), 0 < B ∧
      IsCompact (polarBall (B.toNNReal • sobolevSeminormB (q + 1))) ∧
      ∀ i, ((P i) {ω | ∃ t : T, Z i t ω ∉ polarBall (B.toNNReal • sobolevSeminormB (q + 1))}).toReal ≤ η := by
  by_contra! h_contra;
  obtain ⟨q, δ, hδ, hC2⟩ := gaussian_confinement_bound P Z hmeas H (η / (2 * badrikianConst)) (by
  exact div_pos hη ( mul_pos zero_lt_two ( div_pos ( Real.sqrt_pos.mpr ( Real.exp_pos 1 ) ) ( sub_pos.mpr ( Real.lt_sqrt_of_sq_lt ( by norm_num ) ) ) ) ));
  obtain ⟨C, hC⟩ : ∃ C : ℝ, 0 < C ∧ badrikianConst * ((2 / δ ^ 2) * (Sconst q (q + 1) / C ^ 2)) ≤ η / 2 := by
    have h_lim : Filter.Tendsto (fun C : ℝ => badrikianConst * ((2 / δ ^ 2) * (Sconst q (q + 1) / C ^ 2))) Filter.atTop (nhds 0) := by
      exact le_trans ( tendsto_const_nhds.mul ( tendsto_const_nhds.mul ( tendsto_const_nhds.div_atTop ( by norm_num ) ) ) ) ( by norm_num );
    exact Filter.eventually_atTop.mp ( h_lim.eventually ( ge_mem_nhds <| half_pos hη ) ) |> fun ⟨ C, hC ⟩ => ⟨ Max.max C 1, by positivity, hC _ <| le_max_left _ _ ⟩;
  obtain ⟨ i, hi ⟩ := h_contra q C hC.1 ( isCompact_polarBall _ ( continuous_sobolevSeminormB ( q + 1 ) |> Continuous.const_smul <| C.toNNReal ) );
  refine' hi.not_ge ( le_trans ( ENNReal.toReal_mono _ _ ) ( le_trans ( hC2 C hC.1 i ) _ ) );
  · exact MeasureTheory.measure_ne_top _ _;
  · refine' MeasureTheory.measure_mono _;
    intro ω hω
    obtain ⟨t, ht⟩ := hω
    use t
    by_contra h_contra
    push_neg at h_contra
    have h_polar : ∀ N, Qpart Z (q + 1) N i t ω ≤ C^2 := by
      exact h_contra
    have h_polar_ball : Z i t ω ∈ polarBall (C.toNNReal • sobolevSeminormB (q + 1)) := by
      apply schDual_mem_polarBall_of_Qpart_le (q + 1) C hC.1.le (Z i t ω);
      exact fun N => by simpa only [ Qpart_eq_coeff_form ] using h_polar N;
    exact ht h_polar_ball;
  · convert add_le_add_left hC.2 ( badrikianConst * ( η / ( 2 * badrikianConst ) ) ) using 1 ; ring;
    rw [ mul_div, add_div', eq_div_iff ] <;> nlinarith [ show 0 < badrikianConst by exact div_pos ( Real.sqrt_pos.mpr ( Real.exp_pos 1 ) ) ( sub_pos.mpr ( Real.lt_sqrt_of_sq_lt ( by norm_num ) ) ) ]

end Probability

end TypeDDecouplingMitomaCore