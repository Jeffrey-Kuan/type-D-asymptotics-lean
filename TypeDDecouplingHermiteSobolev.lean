/-
# Hermite–Sobolev chain generating the Schwartz topology (Mitoma campaign, task 3b)

This file builds the countably-Hilbertian structure on `𝓢(ℝ,ℝ)` from the Hermite
functions delivered in `TypeDDecouplingHermite.lean`.

Main pieces:
* `oscCLM` : the harmonic oscillator `A f = -Δf + (x²/4 + 1/2)·f` as a CLM.
* `oscCLM_self_adjoint` : `∫ (Af)g = ∫ f (Ag)`.
* `oscCLM_hermiteSchwartz` : `A hₙ = (n+1) hₙ` (eigenrelation).
* coefficient decay, seminorm growth, Hermite–Sobolev seminorms and the
  two-sided domination with the canonical Schwartz topology.
* `hermiteSobolev_hs_summable` : the Hilbert–Schmidt summability input for M3c.
-/
import Mathlib
import TypeDDecouplingHermite

open MeasureTheory Real Polynomial SchwartzMap Filter
open scoped Real Nat Topology FourierTransform ContDiff

noncomputable section

namespace TypeDDecouplingHermiteSobolev

open TypeDDecouplingHermite

/-! ## (1) The harmonic oscillator -/

/-- The multiplier `x ↦ x²/4 + 1/2`. -/
def oscMult : ℝ → ℝ := fun x => x ^ 2 / 4 + 1 / 2

lemma oscMult_temperate : Function.HasTemperateGrowth oscMult := by
  refine' ⟨ _, _ ⟩;
  · exact ContDiff.add ( ContDiff.div_const ( contDiff_id.pow 2 ) _ ) contDiff_const;
  · intro n;
    rcases n with ( _ | _ | _ | n ) <;> norm_num [ iteratedFDeriv_eq_equiv_comp ];
    · use 2, 1;
      intro x; rw [ oscMult ] ; rw [ abs_le ] ; constructor <;> cases abs_cases x <;> nlinarith;
    · unfold oscMult; norm_num [ mul_comm ];
      exact ⟨ 1, 1, fun x => by cases abs_cases x <;> cases abs_cases ( x * 2 / 4 ) <;> nlinarith ⟩;
    · unfold oscMult;
      norm_num [ iteratedDeriv_succ' ];
      unfold deriv ; norm_num [ fderiv_apply_one_eq_deriv ];
      exact ⟨ 0, 2, fun x => by rw [ show deriv ( fun x : ℝ => 2 * x ) = fun x : ℝ => 2 by ext; norm_num [ mul_comm ] ] ; norm_num ⟩;
    · unfold oscMult; norm_num [ iteratedDeriv_succ' ] ; ring_nf ;
      norm_num [ show deriv ( fun y : ℝ => y ^ 2 * ( 1 / 4 ) ) = fun y : ℝ => y * ( 1 / 2 ) by ext; norm_num; ring ];
      exact ⟨ 0, 0, fun x => by norm_num ⟩

/-- The harmonic oscillator `A f = -Δf + (x²/4 + 1/2)·f` as a continuous linear map. -/
def oscCLM : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ) :=
  - (LineDeriv.laplacianCLM ℝ ℝ 𝓢(ℝ, ℝ)) + SchwartzMap.smulLeftCLM ℝ oscMult

lemma laplacianCLM_apply_eq (f : 𝓢(ℝ, ℝ)) (x : ℝ) :
    (LineDeriv.laplacianCLM ℝ ℝ 𝓢(ℝ, ℝ) f) x = deriv (deriv (⇑f)) x := by
  rw [SchwartzMap.laplacianCLM_eq, SchwartzMap.laplacian_apply,
    InnerProductSpace.laplacian_eq_iteratedDeriv_real, iteratedDeriv_succ, iteratedDeriv_one]

lemma oscCLM_apply (f : 𝓢(ℝ, ℝ)) (x : ℝ) :
    (oscCLM f) x = - deriv (deriv (⇑f)) x + oscMult x * f x := by
      convert congr_arg₂ ( · + · ) ( congr_arg Neg.neg ( laplacianCLM_apply_eq f x ) ) ( SchwartzMap.smulLeftCLM_apply_apply oscMult_temperate f x ) using 1

/-! ## (3a) Polynomial recurrences for `hpoly` -/

/-
Three-term recurrence `x Hₙ = Hₙ₊₁ + n Hₙ₋₁`.
-/
lemma hpoly_three_term (n : ℕ) (x : ℝ) :
    x * hpoly n x = hpoly (n + 1) x + (n : ℝ) * hpoly (n - 1) x := by
      rw [ TypeDDecouplingHermite.hpoly_add_one, TypeDDecouplingHermite.hpoly_deriv ] ; ring;

/-! ## (3b) Pointwise derivative and ladder identities for `hermiteFun` -/

/-
Pointwise derivative of `hₙ`: `hₙ'(x) = cₙ (n Hₙ₋₁ - (x/2) Hₙ) e^{-x²/4}`.
-/
lemma hasDerivAt_hermiteFun (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFun n)
      (hermiteC n * ((n : ℝ) * hpoly (n - 1) x - (x / 2) * hpoly n x) * Real.exp (-(x ^ 2 / 4)))
      x := by
        convert HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_hpoly n x ) ) ( HasDerivAt.exp ( HasDerivAt.neg ( HasDerivAt.div_const ( hasDerivAt_pow 2 x ) _ ) ) ) using 1 ; ring;
        norm_num ; ring

/-
Constant ratio: `√(n+1) · c_{n+1} = c_n`.
-/
lemma sqrt_succ_mul_hermiteC (n : ℕ) :
    Real.sqrt (n + 1) * hermiteC (n + 1) = hermiteC n := by
      unfold hermiteC;
      norm_num [ Nat.factorial_succ ];
      -- By simplifying, we can see that the left-hand side and right-hand side are equal.
      field_simp [mul_comm, mul_assoc, mul_left_comm]

/-
Constant ratio (predecessor): `c_{n-1} = √n · c_n` for `n ≥ 1`.
-/
lemma hermiteC_pred (n : ℕ) (hn : 1 ≤ n) :
    hermiteC (n - 1) = Real.sqrt n * hermiteC n := by
      convert sqrt_succ_mul_hermiteC ( n - 1 ) |> Eq.symm using 1 ; cases n <;> norm_num at *

/-
Ladder identity for multiplication by `x`:
`x hₙ = √(n+1) hₙ₊₁ + √n hₙ₋₁`.
-/
lemma hermiteFun_x_ladder (n : ℕ) (x : ℝ) :
    x * hermiteFun n x = Real.sqrt (n + 1) * hermiteFun (n + 1) x
      + Real.sqrt n * hermiteFun (n - 1) x := by
        unfold hermiteFun;
        rcases n <;> simp_all +decide [ hpoly_three_term ];
        · unfold hpoly; norm_num [ hermiteC ] ; ring;
        · have := hpoly_three_term ( Nat.succ ‹_› ) x; simp_all +decide [ Nat.succ_eq_add_one, add_assoc ] ; ring;
          rename_i k; have := sqrt_succ_mul_hermiteC ( k + 1 ) ; have := hermiteC_pred ( k + 1 ) ; simp_all +decide [ Nat.succ_eq_add_one, add_assoc ] ; ring;
          grind +revert

/-
Ladder identity for the derivative:
`hₙ' = ½(√n hₙ₋₁ - √(n+1) hₙ₊₁)`.
-/
lemma hermiteFun_deriv_ladder (n : ℕ) (x : ℝ) :
    deriv (hermiteFun n) x
      = (1 / 2) * (Real.sqrt n * hermiteFun (n - 1) x - Real.sqrt (n + 1) * hermiteFun (n + 1) x) :=
  by
    convert HasDerivAt.deriv ( hasDerivAt_hermiteFun n x ) using 1;
    by_cases hn : n = 0;
    · simp +decide [ hn, hermiteFun, hpoly ];
      unfold hermiteC; norm_num ; ring;
    · rw [ show hermiteFun ( n - 1 ) x = hermiteC ( n - 1 ) * hpoly ( n - 1 ) x * Real.exp ( - ( x ^ 2 / 4 ) ) by rfl, show hermiteFun ( n + 1 ) x = hermiteC ( n + 1 ) * hpoly ( n + 1 ) x * Real.exp ( - ( x ^ 2 / 4 ) ) by rfl ];
      rw [ show hermiteC ( n - 1 ) = Real.sqrt n * hermiteC n from ?_, show hermiteC ( n + 1 ) = hermiteC n / Real.sqrt ( n + 1 ) from ?_ ];
      · field_simp;
        rw [ Real.sq_sqrt ( Nat.cast_nonneg _ ) ] ; rw [ hpoly_three_term ] ; ring;
      · have := sqrt_succ_mul_hermiteC n;
        rw [ ← this, mul_div_cancel_left₀ _ ( by positivity ) ];
      · exact hermiteC_pred n ( Nat.pos_of_ne_zero hn )

/-! ## (3c) Second derivative and the eigenrelation -/

/-
The ODE: `hₙ'' = (x²/4 - n - 1/2) hₙ`.
-/
lemma deriv_deriv_hermiteFun (n : ℕ) (x : ℝ) :
    deriv (deriv (hermiteFun n)) x = (x ^ 2 / 4 - n - 1 / 2) * hermiteFun n x := by
      rw [ show deriv ( hermiteFun n ) = _ from funext fun x => HasDerivAt.deriv ( hasDerivAt_hermiteFun n x ) ];
      convert HasDerivAt.deriv ( HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.sub ( HasDerivAt.const_mul _ ( hasDerivAt_hpoly ( n - 1 ) x ) ) ( HasDerivAt.mul ( hasDerivAt_id' x |> HasDerivAt.div_const <| 2 ) ( hasDerivAt_hpoly n x ) ) ) ) ( HasDerivAt.exp ( HasDerivAt.neg ( HasDerivAt.div_const ( hasDerivAt_pow 2 x ) 4 ) ) ) ) using 1 ; norm_num [ hermiteFun ] ; ring;
      rcases n with ( _ | _ | n ) <;> norm_num at *;
      · unfold hpoly; norm_num [ hermite ] ; ring;
      · grind +suggestions

/-
**Eigenrelation:** `A hₙ = (n+1) hₙ`.
-/
lemma oscCLM_hermiteSchwartz (n : ℕ) :
    oscCLM (hermiteSchwartz n) = ((n : ℝ) + 1) • hermiteSchwartz n := by
      ext x;
      convert congr_arg ( fun y => -y + ( x ^ 2 / 4 + 1 / 2 ) * hermiteFun n x ) ( show deriv ( deriv ( hermiteFun n ) ) x = ( x ^ 2 / 4 - n - 1 / 2 ) * hermiteFun n x from deriv_deriv_hermiteFun n x ) using 1 ; ring!;
      · rw [ oscCLM_apply, show hermiteSchwartz n = hermiteFun n from funext ( hermiteSchwartz_apply n ) ] ; ring!;
        unfold oscMult; ring;
      · convert congr_arg ( fun y => ( n + 1 : ℝ ) * y ) ( hermiteSchwartz_apply n x ) using 1 ; ring!

/-! ## (2) Self-adjointness -/

/-
**Self-adjointness of `A` on `𝓢`:** `∫ (Af)g = ∫ f (Ag)`.
-/
lemma oscCLM_self_adjoint (f g : 𝓢(ℝ, ℝ)) :
    (∫ x, (oscCLM f) x * g x) = ∫ x, f x * (oscCLM g) x := by
      have h_integrable : ∀ (f g : 𝓢(ℝ, ℝ)), MeasureTheory.Integrable (fun x => f x * g x) := by
        intro f g;
        refine' MeasureTheory.Integrable.mono' _ _ _;
        exact fun x => |f x| * |g x|;
        · have h_integrable : ∀ (f : 𝓢(ℝ, ℝ)), MeasureTheory.Integrable (fun x => |f x|) := by
            exact fun f => f.integrable.norm;
          have h_integrable : ∀ (f g : 𝓢(ℝ, ℝ)), MeasureTheory.Integrable (fun x => |f x| * |g x|) := by
            intro f g
            have h_bounded : ∃ C, ∀ x, |g x| ≤ C := by
              have := g.decay' 0 0;
              aesop
            refine' MeasureTheory.Integrable.mono' ( h_integrable f |> fun h => h.mul_const h_bounded.choose ) _ _;
            · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable f |> MeasureTheory.Integrable.aestronglyMeasurable ) ( h_integrable g |> MeasureTheory.Integrable.aestronglyMeasurable );
            · filter_upwards [ ] using fun x => by simpa using mul_le_mul_of_nonneg_left ( h_bounded.choose_spec x ) ( abs_nonneg _ ) ;
          exact h_integrable f g;
        · exact MeasureTheory.AEStronglyMeasurable.mul ( f.continuous.aestronglyMeasurable ) ( g.continuous.aestronglyMeasurable );
        · norm_num [ abs_mul ];
      have h_laplacian : ∀ (f g : 𝓢(ℝ, ℝ)), ∫ x, (LineDeriv.laplacianCLM ℝ ℝ 𝓢(ℝ, ℝ) f) x * g x = ∫ x, f x * (LineDeriv.laplacianCLM ℝ ℝ 𝓢(ℝ, ℝ) g) x := by
        convert SchwartzMap.integral_mul_laplacian_right_eq_left using 1;
        any_goals try infer_instance;
        any_goals exact MeasureTheory.MeasureSpace.volume;
        · simp +decide only [eq_comm];
          congr!;
        · infer_instance;
      simp_all +decide [ oscCLM, mul_add, add_mul ];
      rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ];
      · simp_all +decide [ MeasureTheory.integral_neg, smulLeftCLM ];
        split_ifs <;> simp_all +decide [ mul_comm ];
        grind;
      · convert h_integrable f ( LineDeriv.laplacianCLM ℝ ℝ 𝓢(ℝ, ℝ) g ) |> fun h => h.neg using 1;
      · convert h_integrable f ( SchwartzMap.smulLeftCLM ℝ oscMult g ) using 1;
      · refine' MeasureTheory.Integrable.neg _;
        convert h_integrable ( LineDeriv.laplacianCLM ℝ ℝ 𝓢(ℝ, ℝ) f ) g using 1;
      · convert h_integrable ( SchwartzMap.smulLeftCLM ℝ oscMult f ) g using 1

/-! ## Coefficient functional and its behaviour under `A` -/

/-
The Hermite coefficient of `A f`: `⟨A f, hₙ⟩ = (n+1) ⟨f, hₙ⟩`.
-/
lemma hermiteCoeffCLM_oscCLM (n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    hermiteCoeffCLM n (oscCLM f) = ((n : ℝ) + 1) * hermiteCoeffCLM n f := by
      -- By definition of `hermiteCoeffCLM`, we have:
      have h_coeff_def : (hermiteCoeffCLM n) (oscCLM f) = ∫ x, (hermiteSchwartz n) x * (oscCLM f) x := by
        convert TypeDDecouplingHermite.hermiteCoeffCLM_apply n ( oscCLM f ) using 1;
        exact congr_arg _ ( funext fun x => by rw [ TypeDDecouplingHermite.hermiteSchwartz_apply ] );
      rw [ h_coeff_def, ← oscCLM_self_adjoint ];
      rw [ show oscCLM ( hermiteSchwartz n ) = ( ( n : ℝ ) + 1 ) • hermiteSchwartz n from oscCLM_hermiteSchwartz n ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, MeasureTheory.integral_const_mul ];
      exact Or.inl ( by rw [ hermiteCoeffCLM_apply ] )

/-
Iterated version: `⟨Aʳ f, hₙ⟩ = (n+1)ʳ ⟨f, hₙ⟩`.
-/
lemma hermiteCoeffCLM_oscCLM_pow (r n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    hermiteCoeffCLM n ((oscCLM ^ r) f) = ((n : ℝ) + 1) ^ r * hermiteCoeffCLM n f := by
      induction' r with r ih generalizing f;
      · norm_num;
      · simp_all +decide [ pow_succ, mul_assoc, mul_left_comm, ContinuousLinearMap.mul_apply ];
        rw [ hermiteCoeffCLM_oscCLM ] ; ring

/-! ## (4) Coefficient decay -/

/-
Bridge: the coefficient functional equals the `L²` inner product.
-/
lemma hermiteCoeffCLM_eq_inner (n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    hermiteCoeffCLM n f = inner ℝ (hermiteLp n) (f.toLp 2 volume) := by
      convert MeasureTheory.integral_congr_ae _;
      filter_upwards [ ( hermiteSchwartz n ).coeFn_toLp 2 volume, f.coeFn_toLp 2 volume ] with x hx₁ hx₂ ; simp +decide [ hx₁, hx₂, inner ];
      convert congr_arg ( fun y => f x * y ) hx₁ using 1;
      · simp +decide [ hx₁, hx₂, smulLeftCLM ];
        split_ifs <;> simp_all +decide [ mul_comm ];
        exact False.elim <| ‹¬Function.HasTemperateGrowth ( hermiteFun n ) › <| hermiteFun_hasTemperateGrowth n;
      · exact hx₁ ▸ rfl

/-
Bessel: `|⟨f, hₙ⟩| ≤ ‖f‖_{L²}`.
-/
lemma abs_hermiteCoeffCLM_le_L2 (n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    |hermiteCoeffCLM n f| ≤ ‖f.toLp 2 volume‖ := by
      rw [ hermiteCoeffCLM_eq_inner ];
      convert abs_real_inner_le_norm ( hermiteLp n ) ( f.toLp 2 volume ) using 1 ; norm_num [ hermiteLp_orthonormal.norm_eq_one n ]

/-
Any continuous linear map from `𝓢(ℝ,ℝ)` into a normed space is bounded by a
finite sup of Schwartz seminorms of the source.
-/
lemma normCLM_seminorm_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : 𝓢(ℝ, ℝ) →L[ℝ] G) :
    ∃ (C : ℝ) (s : Finset (ℕ × ℕ)), 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℝ),
      ‖T f‖ ≤ C * (s.sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2)) f := by
        convert T.continuous using 1;
        constructor <;> intro h;
        · exact T.continuous;
        · have := @Seminorm.bound_of_continuous;
          specialize this (schwartz_withSeminorms ℝ ℝ ℝ) (Seminorm.comp (normSeminorm ℝ G) T.toLinearMap) (by
          exact continuous_norm.comp h);
          obtain ⟨ s, C, hC, h ⟩ := this; use C; use s; simp_all +decide [ Seminorm.le_def ] ;
          convert h using 1

/-
Any Schwartz CLM: a target seminorm is bounded by a finite sup of source seminorms.
-/
lemma schwartz_clm_seminorm_bound (T : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ)) (k l : ℕ) :
    ∃ (C : ℝ) (s : Finset (ℕ × ℕ)), 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℝ),
      SchwartzMap.seminorm ℝ k l (T f)
        ≤ C * (s.sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2)) f := by
          have := @Seminorm.bound_of_continuous;
          specialize this (schwartz_withSeminorms ℝ ℝ ℝ) ((SchwartzMap.seminorm ℝ k l).comp T.toLinearMap);
          obtain ⟨ s, C, hC₁, hC₂ ⟩ := this ( by
            convert ( schwartz_withSeminorms ℝ ℝ ℝ ).continuous_seminorm ( k, l ) |> Continuous.comp <| T.continuous using 1 );
          exact ⟨ C, s, NNReal.coe_nonneg _, fun f => by simpa using hC₂ f ⟩

/-
**Coefficient decay:** for each `r` there are a constant and a finite seminorm
set with `|⟨f, hₙ⟩| ≤ (n+1)^{-r} · C · (finite sup of Schwartz seminorms of f)`.
-/
lemma hermiteCoeff_decay (r : ℕ) :
    ∃ (C : ℝ) (s : Finset (ℕ × ℕ)), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℝ)) (n : ℕ),
      |hermiteCoeffCLM n f|
        ≤ ((n : ℝ) + 1) ^ (-(r : ℝ)) * C
            * (s.sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2)) f := by
              obtain ⟨C, s, hC_nonneg, h_bound⟩ := normCLM_seminorm_bound ( ( SchwartzMap.toLpCLM ℝ ℝ 2 volume ) |> ContinuousLinearMap.comp <| oscCLM ^ r ) ; use C; use s; simp_all +decide [ Real.rpow_neg, Real.rpow_natCast ] ; (
              intro f n; rw [ mul_assoc ] ; rw [ inv_mul_eq_div ] ; rw [ le_div_iff₀ ( by positivity ) ] ; convert le_trans ( abs_hermiteCoeffCLM_le_L2 n ( ( oscCLM ^ r ) f ) ) ( h_bound f ) using 1 ; ring;
              rw [ hermiteCoeffCLM_oscCLM_pow r n f ] ; ring;
              norm_num [ abs_mul, abs_of_nonneg, add_nonneg ]);

/-! ## (7) Hermite–Sobolev seminorms -/

/-- The (squared) Hermite–Sobolev norm of level `r`:
`‖φ‖_r² = ∑ₙ (n+1)^{2r} ⟨φ, hₙ⟩²`. -/
def sobolevNormSq (r : ℕ) (f : 𝓢(ℝ, ℝ)) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * r) * (hermiteCoeffCLM n f) ^ 2

/-- The Hermite–Sobolev seminorm of level `r`. -/
def sobolevSeminorm (r : ℕ) (f : 𝓢(ℝ, ℝ)) : ℝ := Real.sqrt (sobolevNormSq r f)

/-
Coefficients of a Hermite function: `⟨h_j, h_n⟩ = δ_{nj}`.
-/
lemma hermiteCoeffCLM_hermiteSchwartz (n j : ℕ) :
    hermiteCoeffCLM n (hermiteSchwartz j) = if n = j then 1 else 0 := by
      convert ( TypeDDecouplingHermite.hermiteFun_orthonormal_integral n j ) using 1;
      convert TypeDDecouplingHermite.hermiteCoeffCLM_apply n ( hermiteSchwartz j ) using 1;
      exact congr_arg _ ( funext fun x => by rw [ hermiteSchwartz_apply ] )

/-
The defining series of `sobolevNormSq r` is summable (from coefficient decay).
-/
lemma sobolev_summable (r : ℕ) (f : 𝓢(ℝ, ℝ)) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (2 * r) * (hermiteCoeffCLM n f) ^ 2) := by
      obtain ⟨ C, s, hC, hs ⟩ := hermiteCoeff_decay ( r + 1 );
      -- Apply the bound from `hs` to each term in the sum.
      have h_term_bound : ∀ n : ℕ, ((n : ℝ) + 1) ^ (2 * r) * (hermiteCoeffCLM n f) ^ 2 ≤ C ^ 2 * (s.sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2) f) ^ 2 * ((n : ℝ) + 1) ^ (2 * r - 2 * (r + 1) : ℝ) := by
        intro n
        specialize hs f n
        have h_sq_bound : (hermiteCoeffCLM n f) ^ 2 ≤ ((n + 1 : ℝ) ^ (-2 * (r + 1) : ℝ)) * C ^ 2 * (s.sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2) f) ^ 2 := by
          convert pow_le_pow_left₀ ( abs_nonneg _ ) hs 2 using 1 <;> norm_num [ mul_pow, ← Real.rpow_add ( by positivity : 0 < ( n : ℝ ) + 1 ) ] ; ring;
          exact Or.inl <| Or.inl <| by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring;
        convert mul_le_mul_of_nonneg_left h_sq_bound ( by positivity : 0 ≤ ( n + 1 : ℝ ) ^ ( 2 * r : ℝ ) ) using 1 ; ring;
        · norm_cast;
        · rw [ show ( 2 * r - 2 * ( r + 1 ) : ℝ ) = 2 * r + ( -2 * ( r + 1 ) ) by ring, Real.rpow_add ( by positivity ) ] ; ring;
      refine' Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => h_term_bound n ) _;
      exact Summable.mul_left _ <| by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_nat_rpow.2 <| by linarith;

lemma sobolevNormSq_nonneg (r : ℕ) (f : 𝓢(ℝ, ℝ)) : 0 ≤ sobolevNormSq r f := by
  exact tsum_nonneg fun n => mul_nonneg ( by positivity ) ( sq_nonneg _ )

lemma sobolevSeminorm_nonneg (r : ℕ) (f : 𝓢(ℝ, ℝ)) : 0 ≤ sobolevSeminorm r f :=
  Real.sqrt_nonneg _

/-
Homogeneity: `‖c • φ‖_r = |c| ‖φ‖_r`.
-/
lemma sobolevSeminorm_smul (r : ℕ) (c : ℝ) (f : 𝓢(ℝ, ℝ)) :
    sobolevSeminorm r (c • f) = |c| * sobolevSeminorm r f := by
      unfold sobolevSeminorm sobolevNormSq;
      simp +decide only [ContinuousLinearMap.map_smul, smul_eq_mul, mul_pow];
      rw [ ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul ( by positivity ), ← tsum_mul_left ] ; congr ; ext n ; ring;

/-
**(7a) Continuity:** `‖φ‖_r` is dominated by a finite sup of Schwartz seminorms.
-/
lemma sobolev_continuous (r : ℕ) :
    ∃ (C : ℝ) (s : Finset (ℕ × ℕ)), 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℝ),
      sobolevSeminorm r f ≤ C * (s.sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2)) f := by
        obtain ⟨ C, s, hC, hs ⟩ := hermiteCoeff_decay ( r + 1 );
        refine' ⟨ Real.sqrt ( ∑' n : ℕ, ( ( n + 1 : ℝ ) ^ ( - ( 2 : ℝ ) ) ) ) * C, s, _, _ ⟩;
        · positivity;
        · intro f
          have h_sum : ∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * r) * (hermiteCoeffCLM n f) ^ 2 ≤ (∑' n : ℕ, ((n : ℝ) + 1) ^ (-2 : ℝ)) * C ^ 2 * (s.sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2) f) ^ 2 := by
            rw [ ← tsum_mul_right, ← tsum_mul_right ];
            refine' Summable.tsum_le_tsum _ _ _;
            · intro n; specialize hs f n; rw [ ← Real.sqrt_sq_eq_abs ] at hs; rw [ Real.sqrt_le_left ] at hs <;> norm_cast at * <;> norm_num at *;
              · convert mul_le_mul_of_nonneg_left hs ( pow_nonneg ( by positivity : 0 ≤ ( n : ℝ ) + 1 ) ( 2 * r ) ) using 1 ; ring;
                -- Simplifying the right-hand side:
                field_simp
                ring;
              · exact le_trans ( Real.sqrt_nonneg _ ) hs;
            · convert sobolev_summable r f using 1;
            · exact Summable.mul_right _ <| Summable.mul_right _ <| by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_rpow.2 one_lt_two;
          convert Real.sqrt_le_sqrt h_sum using 1;
          rw [ Real.sqrt_mul', Real.sqrt_mul', Real.sqrt_sq, Real.sqrt_sq ] <;> positivity

/-! ## (8) Hilbert–Schmidt data for M3c -/

/-- The `‖·‖_r`-orthonormal system `e^r_j = (j+1)^{-r} h_j`. -/
def hermiteSobolevVec (r j : ℕ) : 𝓢(ℝ, ℝ) :=
  (((j : ℝ) + 1) ^ (-(r : ℝ))) • hermiteSchwartz j

/-
`‖h_j‖_q = (j+1)^q`.
-/
lemma sobolevSeminorm_hermiteSchwartz (q j : ℕ) :
    sobolevSeminorm q (hermiteSchwartz j) = ((j : ℝ) + 1) ^ q := by
      -- By definition of $ hermiteSobolevVec $, we know that $ hermiteSobolevVec q j = (j + 1)^{-q} * hermiteSchwartz j $.
      simp [sobolevSeminorm, sobolevNormSq];
      rw [ tsum_eq_single j ] <;> norm_num [ hermiteCoeffCLM_hermiteSchwartz ];
      · rw [ pow_mul', Real.sqrt_sq ( by positivity ) ];
      · grind +qlia

/-
`‖e^r_j‖_q = (j+1)^{q-r}`.
-/
lemma sobolevSeminorm_hermiteSobolevVec (q r j : ℕ) :
    sobolevSeminorm q (hermiteSobolevVec r j) = ((j : ℝ) + 1) ^ ((q : ℝ) - r) := by
      convert sobolevSeminorm_smul q ( ( ( j : ℝ ) + 1 ) ^ ( -r : ℝ ) ) ( hermiteSchwartz j ) using 1;
      rw [ abs_of_nonneg ( by positivity ), sobolevSeminorm_hermiteSchwartz ];
      rw [ ← Real.rpow_natCast, ← Real.rpow_add ( by positivity ) ] ; ring

/-
**(8) Hilbert–Schmidt summability** (nuclearity input for Mitoma Lemma 3.2):
`∑_j ‖e^r_j‖_q² < ∞` whenever `r ≥ q + 1`.
-/
lemma hermiteSobolev_hs_summable (q r : ℕ) (h : q + 1 ≤ r) :
    Summable (fun j => (sobolevSeminorm q (hermiteSobolevVec r j)) ^ 2) := by
      convert summable_nat_add_iff 1 |>.1 _ using 2;
      · infer_instance;
      · norm_num [ ← Real.sqrt_eq_rpow, sobolevSeminorm_hermiteSobolevVec ];
        convert Real.summable_nat_rpow.2 ( show ( 2 * ( q - r : ℝ ) ) < -1 by linarith [ show ( r : ℝ ) ≥ q + 1 by norm_cast ] ) |> Summable.comp_injective <| Nat.succ_injective.comp Nat.succ_injective using 1;
        ext; rw [ Function.comp_apply, Function.comp_apply ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring;
        grind

/-! ## (5) Growth of Hermite seminorms -/

/-
`L²` normalization at the level of functions: `∫ (hₙ)² = 1`.
-/
lemma integral_hermiteFun_sq (n : ℕ) : (∫ x, (hermiteFun n x) ^ 2) = 1 := by
  simpa [ sq ] using TypeDDecouplingHermite.hermiteFun_orthonormal_integral n n

/-
`L²` bound on the derivative: `∫ (hₙ')² ≤ n + 1` (in fact `= (2n+1)/4`).
-/
lemma integral_deriv_hermiteFun_sq_le (n : ℕ) :
    (∫ x, (deriv (hermiteFun n) x) ^ 2) ≤ (n : ℝ) + 1 := by
      by_cases hn : n = 0;
      · unfold hermiteFun; norm_num [ hn ];
        norm_num [ mul_pow, hermiteC ] ; ring_nf;
        -- Simplify the integral expression.
        suffices h_simp : ∫ x, x ^ 2 * Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * Real.pi) by
          norm_num [ mul_assoc, ← Real.exp_nat_mul ] at *;
          field_simp;
          rw [ MeasureTheory.integral_div, show ( fun x : ℝ => x ^ 2 * Real.exp ( - ( x ^ 2 * 2 / 4 ) ) ) = fun x : ℝ => x ^ 2 * Real.exp ( -x ^ 2 / 2 ) by ext; ring, h_simp ] ; ring_nf;
          norm_num [ mul_right_comm, ne_of_gt, Real.pi_pos, Real.sqrt_pos ];
        have := @integral_rpow_mul_exp_neg_mul_rpow;
        -- We'll use the fact that $\int_{-\infty}^{\infty} x^2 e^{-x^2/2} \, dx$ can be computed using polar coordinates.
        have h_polar : ∫ x in Set.Ioi 0, x^2 * Real.exp (-x^2 / 2) = Real.sqrt (2 * Real.pi) / 2 := by
          convert @this 2 2 ( 1 / 2 ) ( by norm_num ) ( by norm_num ) ( by norm_num ) using 1 <;> norm_num [ div_eq_inv_mul ];
          rw [ show ( 3 / 2 : ℝ ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one ( by norm_num ), Real.Gamma_one_half_eq ] ; ring ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg, Real.rpow_add ];
          rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add ] <;> norm_num ; ring;
          norm_num [ ← Real.sqrt_eq_rpow, mul_comm ];
        -- Since the integrand is even, we can double the integral over $(0, \infty)$ to get the integral over $(-\infty, \infty)$.
        have h_even : ∫ x in Set.Iic 0, x^2 * Real.exp (-x^2 / 2) = Real.sqrt (2 * Real.pi) / 2 := by
          rw [ ← h_polar, ← neg_zero, ← integral_comp_neg_Iic ] ; norm_num;
        convert congr_arg₂ ( · + · ) h_even h_polar using 1;
        · rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num;
          · exact ( by contrapose! h_even; rw [ MeasureTheory.integral_undef h_even ] ; positivity );
          · exact ( by contrapose! h_polar; rw [ MeasureTheory.integral_undef h_polar ] ; positivity );
        · ring;
      · -- Expand the square of the derivative using the ladder identity.
        have h_expand : ∀ x, (deriv (hermiteFun n) x)^2 = (1/4) * (n * (hermiteFun (n - 1) x)^2 + (n + 1) * (hermiteFun (n + 1) x)^2 - 2 * Real.sqrt n * Real.sqrt (n + 1) * hermiteFun (n - 1) x * hermiteFun (n + 1) x) := by
          intro x; rw [ hermiteFun_deriv_ladder ] ; ring;
          rw [ Real.sq_sqrt ( by positivity ), Real.sq_sqrt ( by positivity ) ] ; ring;
        -- Integrate term by term using the orthonormality of the Hermite functions.
        have h_integral : ∫ x, (hermiteFun (n - 1) x)^2 = 1 ∧ ∫ x, (hermiteFun (n + 1) x)^2 = 1 ∧ ∫ x, hermiteFun (n - 1) x * hermiteFun (n + 1) x = 0 := by
          refine' ⟨ _, _, _ ⟩;
          · convert integral_hermiteFun_sq ( n - 1 ) using 1;
          · convert integral_hermiteFun_sq ( n + 1 ) using 1;
          · convert hermiteFun_orthonormal_integral ( n - 1 ) ( n + 1 ) using 1;
            grind;
        rw [ MeasureTheory.integral_congr_ae ( Filter.Eventually.of_forall h_expand ) ];
        rw [ MeasureTheory.integral_const_mul, MeasureTheory.integral_sub, MeasureTheory.integral_add ];
        · norm_num [ mul_assoc, MeasureTheory.integral_const_mul, h_integral ];
          linarith;
        · exact MeasureTheory.Integrable.const_mul ( by exact ( by contrapose! hn; rw [ MeasureTheory.integral_undef hn ] at h_integral; norm_num at h_integral ) ) _;
        · exact MeasureTheory.Integrable.const_mul ( by exact ( by contrapose! hn; rw [ MeasureTheory.integral_undef hn ] at *; linarith ) ) _;
        · exact MeasureTheory.Integrable.add ( MeasureTheory.Integrable.const_mul ( by exact MeasureTheory.integrable_of_integral_eq_one h_integral.1 ) _ ) ( MeasureTheory.Integrable.const_mul ( by exact MeasureTheory.integrable_of_integral_eq_one h_integral.2.1 ) _ );
        · convert MeasureTheory.Integrable.const_mul ( TypeDDecouplingHermite.integrable_hermiteFun_mul ( n - 1 ) ( n + 1 ) ) ( 2 * Real.sqrt n * Real.sqrt ( n + 1 ) ) using 2 ; ring

/-- The pointwise derivative of a Schwartz map is the Schwartz map `derivCLM f`. -/
lemma schwartz_deriv_eq (f : 𝓢(ℝ, ℝ)) : deriv (⇑f) = ⇑(SchwartzMap.derivCLM ℝ ℝ f) :=
  (funext fun x => (SchwartzMap.derivCLM_apply ℝ f x)).symm

/-
`(f)²` is integrable for Schwartz `f`.
-/
lemma schwartz_sq_integrable (f : 𝓢(ℝ, ℝ)) : Integrable (fun y => (f y) ^ 2) := by
  have h_integrable : MeasureTheory.Integrable (fun y => ‖f y‖ ^ 2) volume := by
    convert MeasureTheory.MemLp.integrable_sq ( f.memLp 2 ) using 1;
    norm_num [ sq ];
  convert h_integrable using 1 ; ext ; norm_num [ sq ]

/-
A product of two Schwartz functions is integrable.
-/
lemma schwartz_mul_integrable (f g : 𝓢(ℝ, ℝ)) : Integrable (fun y => f y * g y) := by
  have h_bounded : ∃ C : ℝ, ∀ y : ℝ, |f y| ≤ C := by
    obtain ⟨ C, hC ⟩ := f.decay' 0 0;
    aesop;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun y => h_bounded.choose * |g y|;
  · exact MeasureTheory.Integrable.const_mul ( g.integrable.norm ) _;
  · exact MeasureTheory.AEStronglyMeasurable.mul ( f.continuous.aestronglyMeasurable ) ( g.continuous.aestronglyMeasurable );
  · filter_upwards [ ] using fun x => by simpa [ abs_mul ] using mul_le_mul_of_nonneg_right ( h_bounded.choose_spec x ) ( abs_nonneg ( g x ) ) ;

/-
`(f)² → 0` at `-∞` for Schwartz `f`.
-/
lemma schwartz_sq_tendsto_atBot (f : 𝓢(ℝ, ℝ)) :
    Filter.Tendsto (fun y => (f y) ^ 2) Filter.atBot (nhds 0) := by
      -- Since $f$ is a Schwartz function, it is continuous and $f(y) \to 0$ as $y \to -\infty$.
      have h_cont : Filter.Tendsto (fun y => f y) (Filter.atBot) (nhds 0) := by
        convert SchwartzMap.tendsto_cocompact f |> Filter.Tendsto.comp <| ?_;
        simp +decide [ Filter.Tendsto ];
      simpa using h_cont.pow 2

/-
**Agmon's 1-D inequality** for Schwartz functions:
`f(x)² ≤ 2 ‖f‖₂ ‖f'‖₂`.
-/
lemma schwartz_sq_le_agmon (f : 𝓢(ℝ, ℝ)) (x : ℝ) :
    (f x) ^ 2 ≤ 2 * Real.sqrt (∫ y, (f y) ^ 2) * Real.sqrt (∫ y, (deriv (⇑f) y) ^ 2) := by
      -- Applying the Cauchy-Schwarz inequality to the integral, we get:
      have h_cauchy_schwarz : (∫ y in Set.Iic x, |(f y)| * |(deriv (⇑f) y)|) ≤ Real.sqrt (∫ y in Set.Iic x, (f y) ^ 2) * Real.sqrt (∫ y in Set.Iic x, (deriv (⇑f) y) ^ 2) := by
        rw [ ← Real.sqrt_mul ( MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ) ];
        refine' Real.le_sqrt_of_sq_le _;
        have h_cauchy_schwarz : ∀ {g h : ℝ → ℝ}, MeasureTheory.IntegrableOn (fun y => g y ^ 2) (Set.Iic x) → MeasureTheory.IntegrableOn (fun y => h y ^ 2) (Set.Iic x) → MeasureTheory.IntegrableOn (fun y => g y * h y) (Set.Iic x) → (∫ y in Set.Iic x, g y * h y) ^ 2 ≤ (∫ y in Set.Iic x, g y ^ 2) * (∫ y in Set.Iic x, h y ^ 2) := by
          intros g h hg hh hgh
          have h_cauchy_schwarz : (∫ y in Set.Iic x, (g y - (∫ y in Set.Iic x, g y * h y) / (∫ y in Set.Iic x, h y ^ 2) * h y) ^ 2) ≥ 0 := by
            exact MeasureTheory.integral_nonneg fun y => sq_nonneg _;
          by_cases h : ∫ y in Set.Iic x, h y ^ 2 = 0 <;> simp_all +decide [ sub_sq, mul_pow ];
          · rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg ( fun _ => sq_nonneg _ ) ] at h;
            · exact MeasureTheory.integral_eq_zero_of_ae ( h.mono fun y hy => by aesop );
            · exact hh;
          · rw [ MeasureTheory.integral_add, MeasureTheory.integral_sub ] at h_cauchy_schwarz;
            · simp_all +decide [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ];
              simp_all +decide [ ← mul_assoc, MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul ];
              nlinarith [ inv_mul_cancel_left₀ h ( ∫ y in Set.Iic x, g y * ‹ℝ → ℝ› y ), inv_mul_cancel₀ h, show 0 ≤ ∫ y in Set.Iic x, g y ^ 2 from MeasureTheory.integral_nonneg fun _ => sq_nonneg _, show 0 ≤ ∫ y in Set.Iic x, ‹ℝ → ℝ› y ^ 2 from MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ];
            · exact hg;
            · convert hgh.mul_const ( 2 * ( ( ∫ y in Set.Iic x, g y * ‹ℝ → ℝ› y ) / ∫ y in Set.Iic x, ‹ℝ → ℝ› y ^ 2 ) ) using 2 ; ring;
            · refine' MeasureTheory.Integrable.sub hg _;
              convert hgh.mul_const ( 2 * ( ( ∫ y in Set.Iic x, g y * ‹ℝ → ℝ› y ) / ∫ y in Set.Iic x, ‹ℝ → ℝ› y ^ 2 ) ) using 2 ; ring;
            · exact MeasureTheory.Integrable.const_mul hh _;
        convert h_cauchy_schwarz _ _ _ using 3 <;> norm_num [ sq_abs ];
        · exact MeasureTheory.Integrable.integrableOn ( by exact schwartz_sq_integrable f );
        · refine' MeasureTheory.Integrable.integrableOn _;
          convert schwartz_sq_integrable ( SchwartzMap.derivCLM ℝ ℝ f ) using 1;
        · refine' MeasureTheory.Integrable.integrableOn _;
          convert schwartz_mul_integrable f ( SchwartzMap.derivCLM ℝ ℝ f ) |> MeasureTheory.Integrable.abs using 1 ; aesop;
      have h_integral : ∫ y in Set.Iic x, (f y) * (deriv (⇑f) y) = (1 / 2) * (f x) ^ 2 - (1 / 2) * (0) ^ 2 := by
        have h_integral : ∀ a b, ∫ y in a..b, (f y) * (deriv (⇑f) y) = (1 / 2) * (f b) ^ 2 - (1 / 2) * (f a) ^ 2 := by
          intro a b; rw [ intervalIntegral.integral_deriv_eq_sub' ] <;> norm_num;
          · ext y; norm_num [ sq, f.differentiableAt ] ; ring;
          · exact fun x hx => DifferentiableAt.mul ( differentiableAt_const _ ) ( DifferentiableAt.pow ( f.differentiableAt ) _ );
          · refine' ContinuousOn.mul ( f.continuous.continuousOn ) _;
            exact Continuous.continuousOn ( by rw [ show deriv f = _ from schwartz_deriv_eq f ] ; exact SchwartzMap.continuous _ );
        have h_integral : Filter.Tendsto (fun a => ∫ y in a..x, (f y) * (deriv (⇑f) y)) Filter.atBot (nhds (∫ y in Set.Iic x, (f y) * (deriv (⇑f) y))) := by
          apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Iic ];
          · refine' MeasureTheory.Integrable.integrableOn _;
            convert schwartz_mul_integrable f ( SchwartzMap.derivCLM ℝ ℝ f ) using 1;
          · exact Filter.tendsto_id;
        have h_lim : Filter.Tendsto (fun a => (f a) ^ 2) Filter.atBot (nhds 0) := by
          convert schwartz_sq_tendsto_atBot f using 1;
        exact tendsto_nhds_unique h_integral ( by simpa [ * ] using Filter.Tendsto.sub ( tendsto_const_nhds.mul ( tendsto_const_nhds ) ) ( tendsto_const_nhds.mul h_lim ) );
      have h_integral_abs : ∫ y in Set.Iic x, |(f y)| * |(deriv (⇑f) y)| ≥ |∫ y in Set.Iic x, (f y) * (deriv (⇑f) y)| := by
        simpa only [ ← abs_mul ] using MeasureTheory.norm_integral_le_integral_norm ( fun y => f y * deriv ( ⇑f ) y );
      have h_integral_abs : Real.sqrt (∫ y in Set.Iic x, (f y) ^ 2) ≤ Real.sqrt (∫ y, (f y) ^ 2) ∧ Real.sqrt (∫ y in Set.Iic x, (deriv (⇑f) y) ^ 2) ≤ Real.sqrt (∫ y, (deriv (⇑f) y) ^ 2) := by
        constructor <;> refine' Real.sqrt_le_sqrt <| MeasureTheory.setIntegral_le_integral _ _;
        · convert schwartz_sq_integrable f using 1;
        · exact Filter.Eventually.of_forall fun y => sq_nonneg _;
        · have h_integrable : ∀ (f : 𝓢(ℝ, ℝ)), Integrable (fun y => (deriv (⇑f) y) ^ 2) := by
            intro f
            have h_integrable : Integrable (fun y => (SchwartzMap.derivCLM ℝ ℝ f y) ^ 2) := by
              convert schwartz_sq_integrable ( SchwartzMap.derivCLM ℝ ℝ f ) using 1;
            convert h_integrable using 1;
          exact h_integrable f;
        · exact Filter.Eventually.of_forall fun y => sq_nonneg _;
      nlinarith [ abs_le.mp ‹_›, Real.sqrt_nonneg ( ∫ y in Set.Iic x, f y ^ 2 ), Real.sqrt_nonneg ( ∫ y in Set.Iic x, deriv ( ⇑f ) y ^ 2 ) ]

/-
**Sup bound for Hermite functions:** `|hₙ(x)| ≤ √2 (n+1)^{1/4}`.
-/
lemma hermiteFun_sup_bound (n : ℕ) (x : ℝ) :
    |hermiteFun n x| ≤ Real.sqrt 2 * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
      -- Apply `schwartz_sq_le_agmon` to `hermiteSchwartz n`.
      have h_sup : (hermiteFun n x) ^ 2 ≤ 2 * Real.sqrt (∫ y, (hermiteFun n y) ^ 2) * Real.sqrt (∫ y, (deriv (hermiteFun n) y) ^ 2) := by
        convert schwartz_sq_le_agmon ( hermiteSchwartz n ) x using 1 ; norm_num [ hermiteSchwartz_apply ];
        congr! 3;
        · exact congr_arg _ ( funext fun x => by rw [ hermiteSchwartz_apply ] );
        · exact funext fun x => by rw [ show hermiteSchwartz n = fun x => hermiteFun n x from funext fun x => hermiteSchwartz_apply n x ] ;
      -- By `integral_hermiteFun_sq n`, we have `∫ (hermiteFun n)^2 = 1`.
      have h_int1 : ∫ y, (hermiteFun n y) ^ 2 = 1 := by
        convert integral_hermiteFun_sq n using 1;
      -- By `integral_deriv_hermiteFun_sq_le n`, we have `∫ (deriv (hermiteFun n))^2 ≤ (n:ℝ)+1`.
      have h_int2 : ∫ y, (deriv (hermiteFun n) y) ^ 2 ≤ (n : ℝ) + 1 := by
        convert integral_deriv_hermiteFun_sq_le n using 1;
      rw [ ← Real.sqrt_sq_eq_abs ];
      refine Real.sqrt_le_iff.mpr ⟨ by positivity, ?_ ⟩;
      convert h_sup.trans _ using 1 ; norm_num [ mul_pow, h_int1, h_int2 ];
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num;
      rw [ ← Real.sqrt_eq_rpow ] ; exact Real.sqrt_le_sqrt h_int2

/-! ## (6) Pointwise Hermite expansion, and (7b) converse domination at `(0,0)` -/

/-
Single-term bound: `|⟨φ, hₙ⟩| ≤ ‖φ‖_r (n+1)^{-r}`.
-/
lemma abs_coeff_le_sobolev (r n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    |hermiteCoeffCLM n f| ≤ sobolevSeminorm r f * ((n : ℝ) + 1) ^ (-(r : ℝ)) := by
      have h_term_bound : ((n : ℝ) + 1) ^ (2 * r) * (hermiteCoeffCLM n f) ^ 2 ≤ sobolevNormSq r f := by
        exact Summable.le_tsum ( sobolev_summable r f ) n ( fun m _ => by positivity );
      unfold sobolevSeminorm;
      rw [ ← div_le_iff₀ ( by positivity ) ];
      refine Real.le_sqrt_of_sq_le ?_;
      convert h_term_bound using 1 ; norm_cast ; norm_num ; ring;
      norm_num

/-
Absolute summability of the Hermite coefficients.
-/
lemma summable_abs_coeff (f : 𝓢(ℝ, ℝ)) :
    Summable (fun n => |hermiteCoeffCLM n f|) := by
      have h_abs_le : ∀ n : ℕ, |hermiteCoeffCLM n f| ≤ sobolevSeminorm 2 f * ((n : ℝ) + 1) ^ (-(2 : ℝ)) := by
        intros n
        apply abs_coeff_le_sobolev 2 n f;
      exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) h_abs_le ( Summable.mul_left _ <| by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_rpow.2 one_lt_two )

/-
Pointwise absolute summability of the Hermite series.
-/
lemma summable_coeff_hermiteFun (f : 𝓢(ℝ, ℝ)) (x : ℝ) :
    Summable (fun n => hermiteCoeffCLM n f * hermiteFun n x) := by
      have := @hermiteFun_sup_bound; ( have := @abs_coeff_le_sobolev; ( norm_num [ Real.sqrt_eq_rpow ] at *; ) );
      have h_summable : Summable (fun n : ℕ => |hermiteCoeffCLM n f| * |hermiteFun n x|) := by
        refine' Summable.of_nonneg_of_le ( fun n => mul_nonneg ( abs_nonneg _ ) ( abs_nonneg _ ) ) ( fun n => mul_le_mul ( this 2 n f ) ( by solve_by_elim ) ( by positivity ) ( by exact le_trans ( by positivity ) ( this 2 n f ) ) ) _;
        -- Factor out the constant $2^{1/2}$ and simplify the expression.
        suffices h_simp : Summable (fun n : ℕ => (sobolevSeminorm 2 f) * (2 ^ (1 / 2 : ℝ)) * ((n + 1 : ℝ) ^ ((1 / 4 : ℝ) - 2))) by
          convert h_simp using 2 ; norm_num [ Real.rpow_sub ( Nat.cast_add_one_pos _ ) ] ; ring;
          rw [ show ( -7 / 4 : ℝ ) = ( 1 / 4 : ℝ ) - 2 by norm_num, Real.rpow_sub ( by positivity ) ] ; norm_num ; ring;
        exact Summable.mul_left _ <| by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_nat_rpow.2 <| by norm_num;
      exact Summable.of_norm <| by simpa using h_summable;

/-- The pointwise Hermite series of `f`. -/
def hermiteSeriesFun (f : 𝓢(ℝ, ℝ)) : ℝ → ℝ :=
  fun x => ∑' n, hermiteCoeffCLM n f * hermiteFun n x

/-
The Hermite series is continuous (Weierstrass M-test).
-/
lemma continuous_hermiteSeriesFun (f : 𝓢(ℝ, ℝ)) : Continuous (hermiteSeriesFun f) := by
  refine' continuous_tsum _ _ _;
  use fun n => |hermiteCoeffCLM n f| * (Real.sqrt 2 * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4));
  · exact fun n => continuous_const.mul ( by exact ( hermiteSchwartz n ).continuous.congr fun x => by rw [ hermiteSchwartz_apply ] );
  · have := @abs_coeff_le_sobolev 2;
    refine' Summable.of_nonneg_of_le ( fun n => mul_nonneg ( abs_nonneg _ ) ( by positivity ) ) ( fun n => mul_le_mul_of_nonneg_right ( this n f ) ( by positivity ) ) _;
    convert Summable.mul_left ( sobolevSeminorm 2 f * Real.sqrt 2 ) ( Real.summable_nat_rpow.2 ( show ( -2 : ℝ ) + 1 / 4 < -1 by norm_num ) |> Summable.comp_injective <| Nat.succ_injective ) using 2 ; norm_num ; ring;
    rw [ show ( -7 / 4 : ℝ ) = ( 1 / 4 : ℝ ) - 2 by norm_num, Real.rpow_sub ( by positivity ) ] ; norm_num ; ring;
    norm_cast ; norm_num ; ring;
  · intro n x; rw [ norm_mul ] ; norm_num [ abs_mul ] ; exact mul_le_mul_of_nonneg_left ( by simpa using hermiteFun_sup_bound n x ) ( by positivity ) ;

/-
The Hermite series equals `f` almost everywhere (via `L²` convergence).
-/
lemma hermiteSeriesFun_ae_eq (f : 𝓢(ℝ, ℝ)) :
    hermiteSeriesFun f =ᵐ[volume] ⇑f := by
      obtain ⟨ns, hns⟩ : ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂volume, Filter.Tendsto (fun k => (∑ n ∈ Finset.range (ns k), hermiteCoeffCLM n f • hermiteSchwartz n) x) Filter.atTop (nhds (f x)) := by
        have h_tendsto_in_measure : MeasureTheory.TendstoInMeasure volume (fun N => (∑ n ∈ Finset.range N, hermiteCoeffCLM n f • hermiteSchwartz n).toLp 2 volume) Filter.atTop (f.toLp 2 volume) := by
          have h_conv : Filter.Tendsto (fun N => (∑ n ∈ Finset.range N, hermiteCoeffCLM n f • hermiteSchwartz n).toLp 2 volume) Filter.atTop (nhds (f.toLp 2 volume)) := by
            convert ( TypeDDecouplingHermite.hermiteBasis_hasSum_repr ( f.toLp 2 volume ) |> HasSum.tendsto_sum_nat ) using 2;
            simp +decide [ hermiteBasis, hermiteLp, hermiteCoeffCLM_eq_inner ];
            simp +decide [ HilbertBasis.repr_apply_apply, hermiteLp_orthonormal ];
            induction ‹ℕ› <;> simp_all +decide [ Finset.sum_range_succ ];
            · ext; simp [toLp];
            · convert congr_arg₂ ( · + · ) ‹_› rfl using 1;
              congr! 1;
          apply_rules [ MeasureTheory.tendstoInMeasure_of_tendsto_Lp ];
        obtain ⟨ ns, hns ⟩ := h_tendsto_in_measure.exists_seq_tendsto_ae;
        refine' ⟨ ns, hns.1, _ ⟩;
        filter_upwards [ hns.2, SchwartzMap.coeFn_toLp f 2 volume, SchwartzMap.coeFn_toLp ( ∑ n ∈ Finset.range ( ns 0 ), ( hermiteCoeffCLM n ) f • hermiteSchwartz n ) 2 volume, MeasureTheory.ae_all_iff.2 fun n => SchwartzMap.coeFn_toLp ( ∑ n_1 ∈ Finset.range ( ns ( n + 1 ) ), ( hermiteCoeffCLM n_1 ) f • hermiteSchwartz n_1 ) 2 volume ] with x hx₁ hx₂ hx₃ hx₄;
        rw [ ← hx₂ ];
        convert hx₁ using 1;
        ext i; induction i <;> aesop;
      filter_upwards [ hns.2 ] with x hx using tendsto_nhds_unique ( by
        convert ( summable_coeff_hermiteFun f x |> Summable.hasSum |> HasSum.tendsto_sum_nat |> Filter.Tendsto.comp <| hns.1.tendsto_atTop ) using 1;
        ext; simp +decide [ hermiteSchwartz_apply ] ; ) hx

/-
**(6) Pointwise expansion:** `φ(x) = ∑ₙ ⟨φ, hₙ⟩ hₙ(x)`.
-/
lemma hermiteExpansion_pointwise (f : 𝓢(ℝ, ℝ)) (x : ℝ) :
    HasSum (fun n => hermiteCoeffCLM n f * hermiteFun n x) (f x) := by
      convert summable_coeff_hermiteFun f x |> Summable.hasSum using 1;
      convert ( Continuous.ae_eq_iff_eq ( volume : Measure ℝ ) ( continuous_hermiteSeriesFun f ) ( f.continuous ) ) |>.1 ( hermiteSeriesFun_ae_eq f ) |> Eq.symm |> fun h => congr_fun h x

/-
**(7b) at `(0,0)`:** the sup-seminorm is dominated by a Hermite–Sobolev seminorm.
-/
lemma seminorm_zero_le_sobolev :
    ∃ (C : ℝ) (r : ℕ), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℝ)),
      SchwartzMap.seminorm ℝ 0 0 f ≤ C * sobolevSeminorm r f := by
        -- Set `r := 2` and `C := Real.sqrt 2 * K` with `K := ∑' n : ℕ, ((n:ℝ)+1)^((1:ℝ)/4 - 2)`.
        set r := 2
        set K := ∑' n : ℕ, ((n : ℝ) + 1) ^ ((1 : ℝ) / 4 - 2)
        use Real.sqrt 2 * K, r;
        refine' ⟨ mul_nonneg ( Real.sqrt_nonneg _ ) ( tsum_nonneg fun _ => by positivity ), _ ⟩;
        intro f
        have h_sup_seminorm : ∀ x, |f x| ≤ Real.sqrt 2 * sobolevSeminorm r f * K := by
          intro x
          have h_sum : |f x| ≤ ∑' n : ℕ, |hermiteCoeffCLM n f * hermiteFun n x| := by
            have h_sum : f x = ∑' n : ℕ, (hermiteCoeffCLM n f) * (hermiteFun n x) := by
              exact Eq.symm ( hermiteExpansion_pointwise f x |> HasSum.tsum_eq );
            convert norm_tsum_le_tsum_norm _ <;> norm_num;
            convert congr_arg Norm.norm h_sum using 1;
            · norm_num [ Norm.norm ];
            · exact Summable.norm ( summable_coeff_hermiteFun f x );
          -- Apply the bound on the Hermite coefficients and the supremum bound on the Hermite functions.
          have h_bound : ∀ n : ℕ, |hermiteCoeffCLM n f * hermiteFun n x| ≤ Real.sqrt 2 * sobolevSeminorm r f * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4 - 2) := by
            intro n
            have h_coeff : |hermiteCoeffCLM n f| ≤ sobolevSeminorm r f * ((n : ℝ) + 1) ^ (-(r : ℝ)) := by
              convert abs_coeff_le_sobolev r n f using 1
            have h_hermite : |hermiteFun n x| ≤ Real.sqrt 2 * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
              convert hermiteFun_sup_bound n x using 1;
            convert mul_le_mul h_coeff h_hermite ( by positivity ) ( by exact mul_nonneg ( by exact sobolevSeminorm_nonneg _ _ ) ( by positivity ) ) using 1 ; ring;
            · rw [ abs_mul ];
            · rw [ show ( 1 / 4 - 2 : ℝ ) = -2 + 1 / 4 by norm_num, Real.rpow_add ] <;> norm_num <;> ring ; positivity;
          refine le_trans h_sum <| le_trans ( Summable.tsum_le_tsum h_bound ?_ ?_ ) ?_;
          · exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) h_bound ( Summable.mul_left _ <| by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_nat_rpow.2 <| by norm_num );
          · exact Summable.mul_left _ <| by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_nat_rpow.2 <| by norm_num;
          · rw [ tsum_mul_left ];
        refine' csInf_le _ _ <;> norm_num;
        · exact ⟨ 0, fun c hc => hc.1 ⟩;
        · exact ⟨ mul_nonneg ( mul_nonneg ( Real.sqrt_nonneg _ ) ( tsum_nonneg fun _ => by positivity ) ) ( sobolevSeminorm_nonneg _ _ ), fun x => by simpa only [ mul_right_comm ] using h_sup_seminorm x ⟩

/-! ## General seminorm growth (5) and converse domination (7b)

The multiplication-by-`x` and differentiation operators shift the Hermite–Sobolev
level by one; iterating reduces every `p_{k,m}` to `p_{0,0}` of a transformed
function, giving the full converse domination and hence polynomial growth of all
Hermite seminorms. -/

/-- Multiplication by `x` as a CLM on `𝓢(ℝ,ℝ)`. -/
def xMulCLM : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ) := SchwartzMap.smulLeftCLM ℝ (fun x => x)

@[simp] lemma xMulCLM_apply (f : 𝓢(ℝ, ℝ)) (x : ℝ) : (xMulCLM f) x = x * f x := by
  simp [xMulCLM, SchwartzMap.smulLeftCLM_apply_apply Function.HasTemperateGrowth.id']

/-
Coefficient recurrence for multiplication by `x`.
-/
lemma coeff_xMulCLM (n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    hermiteCoeffCLM n (xMulCLM f)
      = Real.sqrt (n + 1) * hermiteCoeffCLM (n + 1) f
        + Real.sqrt n * hermiteCoeffCLM (n - 1) f := by
          -- Express the coefficient as an integral: `(hermiteCoeffCLM n) (xMulCLM f) = ∫ x, hermiteFun n x * (x * f x)`.
          have h_coeff_integral : (hermiteCoeffCLM n) (xMulCLM f) = ∫ x, (hermiteFun n x) * (x * f x) := by
            convert hermiteCoeffCLM_apply n ( xMulCLM f ) using 1;
            exact congr_arg _ ( funext fun x => by rw [ xMulCLM_apply ] );
          -- Split the integral into two parts: one involving `hermiteFun (n+1)` and another involving `hermiteFun (n-1)`.
          have h_split_integral : ∫ x, (hermiteFun n x) * (x * f x) = (∫ x, (Real.sqrt (n + 1) * hermiteFun (n + 1) x) * f x) + (∫ x, (Real.sqrt n * hermiteFun (n - 1) x) * f x) := by
            rw [ ← MeasureTheory.integral_add ] ; congr ; ext x ; ring;
            · convert congr_arg ( · * f x ) ( hermiteFun_x_ladder n x ) using 1 <;> ring;
            · convert schwartz_mul_integrable ( hermiteSchwartz ( n + 1 ) ) f |> fun h => h.const_mul ( Real.sqrt ( n + 1 ) ) using 1 ; ext ; simp +decide [ hermiteSchwartz_apply ] ; ring;
            · convert schwartz_mul_integrable ( hermiteSchwartz ( n - 1 ) ) f |> ( fun h => h.const_mul ( Real.sqrt n ) ) using 1 ; ext ; simp +decide [ hermiteSchwartz_apply ] ; ring;
          simp_all +decide [ mul_assoc, MeasureTheory.integral_const_mul ];
          congr! 2;
          · convert hermiteCoeffCLM_apply ( n + 1 ) f |> Eq.symm using 1;
          · convert hermiteCoeffCLM_apply ( n - 1 ) f |> Eq.symm using 1

/-
Coefficient recurrence for differentiation.
-/
lemma coeff_derivCLM (n : ℕ) (f : 𝓢(ℝ, ℝ)) :
    hermiteCoeffCLM n (SchwartzMap.derivCLM ℝ ℝ f)
      = (1 / 2) * (Real.sqrt (n + 1) * hermiteCoeffCLM (n + 1) f
        - Real.sqrt n * hermiteCoeffCLM (n - 1) f) := by
          convert congr_arg ( fun x : ℝ => x ) ( show ∫ x : ℝ, hermiteFun n x * deriv ( fun y => f y ) x = -∫ x : ℝ, deriv ( fun y => hermiteFun n y ) x * f x from ?_ ) using 1;
          · convert TypeDDecouplingHermite.hermiteCoeffCLM_apply n ( SchwartzMap.derivCLM ℝ ℝ f ) using 1;
          · rw [ show deriv ( fun y => hermiteFun n y ) = fun y => ( 1 / 2 ) * ( Real.sqrt n * hermiteFun ( n - 1 ) y - Real.sqrt ( n + 1 ) * hermiteFun ( n + 1 ) y ) from funext fun x => hermiteFun_deriv_ladder n x ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, MeasureTheory.integral_const_mul ] ; ring;
            rw [ MeasureTheory.integral_add, MeasureTheory.integral_neg ];
            · norm_num [ mul_assoc, MeasureTheory.integral_const_mul, hermiteCoeffCLM_apply ] ; ring;
            · refine' MeasureTheory.Integrable.neg _;
              convert schwartz_mul_integrable ( hermiteSchwartz ( 1 + n ) ) f |> fun h => h.const_mul ( Real.sqrt ( 1 + n ) ) using 1 ; ext ; norm_num [ hermiteSchwartz_apply ] ; ring;
            · convert schwartz_mul_integrable ( hermiteSchwartz ( n - 1 ) ) f |> fun h => h.const_mul ( Real.sqrt n ) using 1 ; ext ; norm_num [ hermiteSchwartz_apply ] ; ring;
          · convert SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul ( hermiteSchwartz n ) f using 1;
            · congr!;
              exact funext fun x => hermiteSchwartz_apply n x ▸ rfl;
            · convert rfl;
              exact funext fun x => hermiteSchwartz_apply n x

/-
Reindexing helper: the shifted-up weighted coefficient series is summable.
-/
lemma summable_shift_succ (r : ℕ) (f : 𝓢(ℝ, ℝ)) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (2 * r + 1) * (hermiteCoeffCLM (n + 1) f) ^ 2) := by
      have h_summable : Summable (fun n : ℕ => ((n + 2 : ℝ) ^ (2 * (r + 1)) * (hermiteCoeffCLM (n + 1) f) ^ 2)) := by
        convert summable_nat_add_iff 1 |>.2 ( sobolev_summable ( r + 1 ) f ) using 2 ; push_cast ; ring;
      refine' .of_nonneg_of_le ( fun n => mul_nonneg ( pow_nonneg ( by positivity ) _ ) ( sq_nonneg _ ) ) ( fun n => mul_le_mul_of_nonneg_right ( _ : _ ≤ _ ) ( sq_nonneg _ ) ) h_summable;
      exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( by linarith ) _ ) ( pow_le_pow_right₀ ( by linarith ) ( by linarith ) )

/-
Reindexing helper: the shifted-down weighted coefficient series is summable.
-/
lemma summable_shift_pred (r : ℕ) (f : 𝓢(ℝ, ℝ)) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (2 * r) * (n : ℝ) * (hermiteCoeffCLM (n - 1) f) ^ 2) := by
  rw [ ← summable_nat_add_iff 1 ];
  have h_summable_shift : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ (2 * r) * ((n : ℝ) + 1) * (hermiteCoeffCLM n f) ^ 2) := by
    refine' .of_nonneg_of_le ( fun n => mul_nonneg ( mul_nonneg ( pow_nonneg ( by positivity ) _ ) ( by positivity ) ) ( sq_nonneg _ ) ) ( fun n => _ ) ( show Summable fun n : ℕ => ( 2 : ℝ ) ^ ( 2 * r ) * ( n + 1 ) ^ ( 2 * r + 2 ) * ( hermiteCoeffCLM n f ) ^ 2 from _ );
    · refine' mul_le_mul_of_nonneg_right _ ( sq_nonneg _ );
      refine' le_trans ( mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) ( show ( n : ℝ ) + 2 ≤ 2 * ( n + 1 ) by linarith ) _ ) ( by positivity ) ) _;
      rw [ mul_pow ] ; ring_nf ; norm_num;
      exact le_add_of_le_of_nonneg ( le_mul_of_one_le_right ( by positivity ) ( by norm_num ) ) ( by positivity );
    · convert Summable.mul_left ( 2 ^ ( 2 * r ) ) ( sobolev_summable ( r + 1 ) f ) using 2 ; ring;
  exact_mod_cast h_summable_shift

/-
Reindexing bound (up-shift): `∑ (n+1)^{2r+1} c_{n+1}² ≤ ‖f‖_{r+1}²`.
-/
lemma tsum_shift_succ_le (r : ℕ) (f : 𝓢(ℝ, ℝ)) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * r + 1) * (hermiteCoeffCLM (n + 1) f) ^ 2)
      ≤ sobolevNormSq (r + 1) f := by
        have h_summable : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * r + 1) * (hermiteCoeffCLM n f) ^ 2)) := by
          have h_summable : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (2 * r + 2) * (hermiteCoeffCLM n f) ^ 2) := by
            convert sobolev_summable ( r + 1 ) f using 1;
          refine' .of_nonneg_of_le ( fun n => mul_nonneg ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ( sq_nonneg _ ) ) ( fun n => _ ) h_summable;
          exact mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) ( by linarith ) _ |> le_trans <| pow_le_pow_right₀ ( by linarith ) <| by linarith ) <| sq_nonneg _;
        have h_summable_shift : ∑' n : ℕ, ((n : ℝ) ^ (2 * r + 1) * (hermiteCoeffCLM n f) ^ 2) ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * (r + 1)) * (hermiteCoeffCLM n f) ^ 2 := by
          refine' Summable.tsum_le_tsum _ _ _;
          · exact fun n => mul_le_mul_of_nonneg_right ( by exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( by linarith ) _ ) ( pow_le_pow_right₀ ( by linarith ) ( by linarith ) ) ) ( sq_nonneg _ );
          · convert h_summable using 1;
          · convert sobolev_summable ( r + 1 ) f using 1;
        convert h_summable_shift using 1;
        rw [ eq_comm, Summable.tsum_eq_zero_add h_summable ] ; aesop

/-
Reindexing bound (down-shift): `∑ (n+1)^{2r} n c_{n-1}² ≤ 2^{2r} ‖f‖_{r+1}²`.
-/
lemma tsum_shift_pred_le (r : ℕ) (f : 𝓢(ℝ, ℝ)) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * r) * (n : ℝ) * (hermiteCoeffCLM (n - 1) f) ^ 2)
      ≤ 2 ^ (2 * r) * sobolevNormSq (r + 1) f := by
        rw [ Summable.tsum_eq_zero_add ];
        · simp +zetaDelta at *;
          -- Apply the termwise bound to each term in the sum.
          have h_termwise_bound : ∀ n : ℕ, ((n : ℝ) + 1 + 1) ^ (2 * r) * ((n : ℝ) + 1) * (hermiteCoeffCLM n f) ^ 2 ≤ 2 ^ (2 * r) * ((n : ℝ) + 1) ^ (2 * (r + 1)) * (hermiteCoeffCLM n f) ^ 2 := by
            intro n
            have h_termwise_bound : ((n : ℝ) + 1 + 1) ^ (2 * r) * ((n : ℝ) + 1) ≤ 2 ^ (2 * r) * ((n : ℝ) + 1) ^ (2 * (r + 1)) := by
              rw [ pow_mul, pow_mul ];
              rw [ pow_mul ];
              refine' le_trans ( mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) ( show ( n + 1 + 1 : ℝ ) ^ 2 ≤ 2 ^ 2 * ( n + 1 ) ^ 2 by nlinarith [ sq ( n : ℝ ) ] ) _ ) ( by positivity ) ) _;
              rw [ mul_pow ] ; ring_nf ; norm_num;
              exact le_add_of_le_of_nonneg ( le_mul_of_one_le_right ( by positivity ) ( by norm_num ) ) ( by positivity );
            exact mul_le_mul_of_nonneg_right h_termwise_bound <| sq_nonneg _;
          refine' le_trans ( Summable.tsum_le_tsum h_termwise_bound _ _ ) _;
          · refine' Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => h_termwise_bound n ) _;
            convert Summable.mul_left ( 2 ^ ( 2 * r ) ) ( sobolev_summable ( r + 1 ) f ) using 2 ; ring;
          · convert Summable.mul_left ( 2 ^ ( 2 * r ) ) ( sobolev_summable ( r + 1 ) f ) using 2 ; ring;
          · simp +decide [ mul_assoc, tsum_mul_left, sobolevNormSq ];
        · convert summable_shift_pred r f using 1

/-
Multiplication by `x` raises the Sobolev level by at most one.
-/
lemma exists_sobolev_xMulCLM_bound (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℝ),
      sobolevSeminorm r (xMulCLM f) ≤ C * sobolevSeminorm (r + 1) f := by
        refine' ⟨ Real.sqrt ( 2 + 2 ^ ( 2 * r + 1 ) ), Real.sqrt_nonneg _, fun f => Real.sqrt_le_iff.mpr _ ⟩;
        refine' ⟨ mul_nonneg ( Real.sqrt_nonneg _ ) ( Real.sqrt_nonneg _ ), _ ⟩;
        rw [ mul_pow, Real.sq_sqrt <| by positivity, show sobolevNormSq r ( xMulCLM f ) = ∑' n : ℕ, ( ( n + 1 : ℝ ) ^ ( 2 * r ) ) * ( hermiteCoeffCLM n ( xMulCLM f ) ) ^ 2 from rfl ];
        -- Apply the inequality term by term to the sum.
        have h_term_by_term : ∀ n : ℕ, (n + 1 : ℝ) ^ (2 * r) * (hermiteCoeffCLM n (xMulCLM f)) ^ 2 ≤ 2 * ((n + 1 : ℝ) ^ (2 * r + 1) * (hermiteCoeffCLM (n + 1) f) ^ 2) + 2 * ((n + 1 : ℝ) ^ (2 * r) * (n : ℝ) * (hermiteCoeffCLM (n - 1) f) ^ 2) := by
          intro n
          have h_term_bound : (hermiteCoeffCLM n (xMulCLM f)) ^ 2 ≤ 2 * (n + 1) * (hermiteCoeffCLM (n + 1) f) ^ 2 + 2 * n * (hermiteCoeffCLM (n - 1) f) ^ 2 := by
            rw [ coeff_xMulCLM ];
            nlinarith only [ sq_nonneg ( Real.sqrt ( n + 1 ) * hermiteCoeffCLM ( n + 1 ) f - Real.sqrt n * hermiteCoeffCLM ( n - 1 ) f ), Real.mul_self_sqrt ( show ( n:ℝ ) + 1 ≥ 0 by positivity ), Real.mul_self_sqrt ( show ( n:ℝ ) ≥ 0 by positivity ) ];
          convert mul_le_mul_of_nonneg_left h_term_bound ( pow_nonneg ( by positivity : 0 ≤ ( n : ℝ ) + 1 ) ( 2 * r ) ) using 1 ; ring;
        refine' le_trans ( Summable.tsum_le_tsum h_term_by_term _ _ ) _;
        · convert sobolev_summable r ( xMulCLM f ) using 1;
        · refine' Summable.add _ _;
          · exact Summable.mul_left _ ( summable_shift_succ r f );
          · exact Summable.mul_left _ ( summable_shift_pred r f );
        · rw [ Summable.tsum_add, tsum_mul_left, tsum_mul_left ];
          · rw [ show sobolevSeminorm ( r + 1 ) f ^ 2 = sobolevNormSq ( r + 1 ) f from ?_ ];
            · have := tsum_shift_succ_le r f; have := tsum_shift_pred_le r f; norm_num [ pow_succ', mul_assoc, mul_comm, mul_left_comm, tsum_mul_left ] at *; nlinarith;
            · exact Real.sq_sqrt <| tsum_nonneg fun _ => by positivity;
          · exact Summable.mul_left _ ( summable_shift_succ r f );
          · exact Summable.mul_left _ ( summable_shift_pred r f )

/-
Differentiation raises the Sobolev level by at most one.
-/
lemma exists_sobolev_derivCLM_bound (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℝ),
      sobolevSeminorm r (SchwartzMap.derivCLM ℝ ℝ f) ≤ C * sobolevSeminorm (r + 1) f := by
        refine' ⟨ Real.sqrt ( 1 + 2 ^ ( 2 * r ) ), Real.sqrt_nonneg _, _ ⟩;
        intro f
        have h_sum : (∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * r) * (hermiteCoeffCLM n (SchwartzMap.derivCLM ℝ ℝ f)) ^ 2) ≤ (1 + 2^(2*r)) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * (r + 1)) * (hermiteCoeffCLM n f) ^ 2) := by
          -- By `coeff_derivCLM`, we have:
          have h_coeff_derivCLM : ∀ n : ℕ, (hermiteCoeffCLM n (SchwartzMap.derivCLM ℝ ℝ f)) ^ 2 ≤ (1 / 2) * ((n + 1 : ℝ) * (hermiteCoeffCLM (n + 1) f) ^ 2 + n * (hermiteCoeffCLM (n - 1) f) ^ 2) := by
            intro n
            rw [coeff_derivCLM];
            nlinarith only [ sq_nonneg ( Real.sqrt ( n + 1 ) * hermiteCoeffCLM ( n + 1 ) f + Real.sqrt n * hermiteCoeffCLM ( n - 1 ) f ), Real.mul_self_sqrt ( show ( n:ℝ ) + 1 ≥ 0 by positivity ), Real.mul_self_sqrt ( show ( n:ℝ ) ≥ 0 by positivity ) ];
          -- Apply the inequality term by term to the sum.
          have h_sum_ineq : ∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * r) * (hermiteCoeffCLM n (SchwartzMap.derivCLM ℝ ℝ f)) ^ 2 ≤ (1 / 2) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * r + 1) * (hermiteCoeffCLM (n + 1) f) ^ 2 + ∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * r) * n * (hermiteCoeffCLM (n - 1) f) ^ 2) := by
            rw [ ← Summable.tsum_add ];
            · rw [ ← tsum_mul_left ] ; refine' Summable.tsum_le_tsum _ _ _;
              · intro n; convert mul_le_mul_of_nonneg_left ( h_coeff_derivCLM n ) ( by positivity : 0 ≤ ( n + 1 : ℝ ) ^ ( 2 * r ) ) using 1 ; ring;
              · have := @sobolev_summable r ( SchwartzMap.derivCLM ℝ ℝ f ) ; aesop;
              · refine' Summable.mul_left _ _;
                refine' Summable.add _ _;
                · convert summable_shift_succ r f using 1;
                · convert summable_shift_pred r f using 1;
            · convert summable_shift_succ r f using 1;
            · convert summable_shift_pred r f using 1;
          refine le_trans h_sum_ineq ?_;
          refine le_trans ( mul_le_mul_of_nonneg_left ( add_le_add ( tsum_shift_succ_le r f ) ( tsum_shift_pred_le r f ) ) ( by norm_num ) ) ?_;
          nlinarith! [ show ( 0 : ℝ ) ≤ 2 ^ ( 2 * r ) by positivity, show ( 0 : ℝ ) ≤ ∑' n : ℕ, ( ( n : ℝ ) + 1 ) ^ ( 2 * ( r + 1 ) ) * ( hermiteCoeffCLM n f ) ^ 2 by exact tsum_nonneg fun _ => by positivity ];
        unfold sobolevSeminorm;
        rw [ ← Real.sqrt_mul <| by positivity ] ; exact Real.sqrt_le_sqrt h_sum;

/-
Iterated multiplication by `x`.
-/
lemma exists_sobolev_xMulCLM_pow_bound (k r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℝ),
      sobolevSeminorm r ((xMulCLM ^ k) f) ≤ C * sobolevSeminorm (r + k) f := by
        induction' k with k ih generalizing r;
        · exact ⟨ 1, by norm_num, fun f => by norm_num ⟩;
        · obtain ⟨ C, hC₀, hC ⟩ := ih r;
          obtain ⟨ C', hC'₀, hC' ⟩ := exists_sobolev_xMulCLM_bound ( r + k ) ; use C * C'; simp_all +decide [ pow_succ, mul_assoc];
          exact ⟨ mul_nonneg hC₀ hC'₀, fun f => le_trans ( hC _ ) ( mul_le_mul_of_nonneg_left ( hC' _ ) hC₀ ) ⟩

/-
Iterated differentiation.
-/
lemma exists_sobolev_derivCLM_pow_bound (m r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℝ),
      sobolevSeminorm r (((SchwartzMap.derivCLM ℝ ℝ) ^ m) f) ≤ C * sobolevSeminorm (r + m) f := by
        induction' m with m ih generalizing r;
        · exact ⟨ 1, by norm_num, fun f => by norm_num ⟩;
        · obtain ⟨ C₁, hC₁, hC₁' ⟩ := ih r
          obtain ⟨ C₂, hC₂, hC₂' ⟩ := exists_sobolev_derivCLM_bound (r + m);
          refine' ⟨ C₁ * C₂, mul_nonneg hC₁ hC₂, fun f => _ ⟩;
          convert le_trans ( hC₁' ( SchwartzMap.derivCLM ℝ ℝ f ) ) ( mul_le_mul_of_nonneg_left ( hC₂' f ) hC₁ ) using 1 ; ring!

/-
`p_{k,m}(φ) ≤ p_{0,0}(x^k ∂^m φ)`: the seminorm reduction.
-/
lemma seminorm_le_seminorm_zero_transform (k m : ℕ) (f : 𝓢(ℝ, ℝ)) :
    SchwartzMap.seminorm ℝ k m f
      ≤ SchwartzMap.seminorm ℝ 0 0 ((xMulCLM ^ k) (((SchwartzMap.derivCLM ℝ ℝ) ^ m) f)) := by
        refine' SchwartzMap.seminorm_le_bound ℝ k m f _ _;
        · exact apply_nonneg _ _;
        · intro x
          have h_psi : (xMulCLM ^ k) ((derivCLM ℝ ℝ ^ m) f) x = x ^ k * iteratedDeriv m (⇑f) x := by
            induction' k with k ih generalizing x <;> simp_all +decide [ pow_succ', mul_assoc ];
            induction' m with m ih generalizing x <;> simp_all +decide [ pow_succ', mul_assoc, iteratedDeriv_succ ];
            exact congr_arg ( deriv · x ) ( funext ih );
          convert SchwartzMap.le_seminorm ℝ 0 0 _ x using 1 ; norm_num [ h_psi, norm_iteratedFDeriv_eq_norm_iteratedDeriv ]

/-
**(7b) general converse domination:** each Schwartz seminorm is dominated by a
Hermite–Sobolev seminorm. Together with `sobolev_continuous` this shows the
countable Hilbertian chain generates the Schwartz topology.
-/
lemma seminorm_le_sobolev (k m : ℕ) :
    ∃ (C : ℝ) (r : ℕ), 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℝ),
      SchwartzMap.seminorm ℝ k m f ≤ C * sobolevSeminorm r f := by
        obtain ⟨ C₀, r₀, hC₀, hbound₀ ⟩ := seminorm_zero_le_sobolev;
        obtain ⟨ C₁, hC₁, hb₁ ⟩ := exists_sobolev_xMulCLM_pow_bound k r₀
        obtain ⟨ C₂, hC₂, hb₂ ⟩ := exists_sobolev_derivCLM_pow_bound m ( r₀ + k );
        use C₀ * C₁ * C₂, r₀ + k + m;
        refine' ⟨ by positivity, fun f => _ ⟩;
        convert le_trans ( seminorm_le_seminorm_zero_transform k m f ) ( hbound₀ _ |> le_trans <| mul_le_mul_of_nonneg_left ( hb₁ _ |> le_trans <| mul_le_mul_of_nonneg_left ( hb₂ _ ) hC₁ ) hC₀ ) using 1 ; ring

/-
**(5) Polynomial growth of Hermite seminorms:** `p_{k,m}(hₙ) ≤ C (n+1)^N`.
-/
lemma hermiteSeminorm_growth (k m : ℕ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n : ℕ,
      SchwartzMap.seminorm ℝ k m (hermiteSchwartz n) ≤ C * ((n : ℝ) + 1) ^ N := by
        obtain ⟨ C, r, hC, hbound ⟩ := seminorm_le_sobolev k m;
        exact ⟨ C, r, hC, fun n => le_trans ( hbound _ ) ( by rw [ sobolevSeminorm_hermiteSchwartz ] ) ⟩

end TypeDDecouplingHermiteSobolev