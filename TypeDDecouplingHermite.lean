import Mathlib

/-!
# Hermite functions as a Hilbert basis of `L²(ℝ)`  (Mitoma campaign, task 3a)

This file develops, from Mathlib's Hermite *polynomials* (`Polynomial.hermite`, the
probabilists' convention, monic, orthogonal for the weight `e^{-x²/2}`), the theory of
Hermite *functions* `hₙ(x) = cₙ Hₙ(x) e^{-x²/4}` and shows they form a complete
orthonormal system (Hilbert basis) of `L²(ℝ)` for Lebesgue measure.

Main deliverables:
* `hermiteFun`             : the Hermite functions, `L²`-normalized for Lebesgue measure.
* `hermiteSchwartz`        : their bundling as Schwartz functions.
* `hermite_orthogonality`  : `∫ Hₘ Hₙ e^{-x²/2} = δₘₙ · n! √(2π)`.
* `hermiteFun_orthonormal` : `∫ hₘ hₙ = δₘₙ`.
* `hermite_complete`       : completeness (the analytic heart, via Fourier).
* `hermiteBasis`           : the packaged `HilbertBasis ℕ ℝ (Lp ℝ 2 volume)`.
* `hermiteCoeffCLM`        : the coefficient functional on `𝓢(ℝ,ℝ)` (bridge for M3b).
-/

open MeasureTheory Real Polynomial SchwartzMap Filter
open scoped Real Nat Topology FourierTransform ContDiff

noncomputable section

set_option maxHeartbeats 1000000

namespace TypeDDecouplingHermite

/-! ## Basic definitions -/

/-- Probabilists' Hermite polynomial `Hₙ` evaluated at a real point. -/
def hpoly (n : ℕ) (x : ℝ) : ℝ := aeval x (hermite n)

/-- The Gaussian weight `e^{-x²/2}`. -/
def gwFun (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2))

/-- Normalizing constant `cₙ = (n! √(2π))^{-1/2}`. -/
def hermiteC (n : ℕ) : ℝ := (Real.sqrt ((n ! : ℝ) * Real.sqrt (2 * π)))⁻¹

/-- The Hermite function `hₙ(x) = cₙ Hₙ(x) e^{-x²/4}`. -/
def hermiteFun (n : ℕ) (x : ℝ) : ℝ := hermiteC n * hpoly n x * Real.exp (-(x ^ 2 / 4))

/-! ## Elementary polynomial / Gaussian facts -/

@[simp] lemma hpoly_zero (x : ℝ) : hpoly 0 x = 1 := by
  unfold hpoly; aesop;

lemma hpoly_add_one (n : ℕ) (x : ℝ) :
    hpoly (n + 1) x = x * hpoly n x - deriv (hpoly n) x := by
      unfold hpoly;
      norm_num [ Polynomial.differentiableAt ]

/-
Derivative identity for Hermite polynomials: `Hₙ' = n Hₙ₋₁`.
-/
lemma derivative_hermite (n : ℕ) :
    Polynomial.derivative (hermite n) = (n : ℤ) • hermite (n - 1) := by
      induction' n with n ih;
      · norm_num [ hermite ];
      · rw [ Polynomial.hermite_succ ];
        rcases n <;> simp_all +decide [ Polynomial.smul_eq_C_mul, mul_assoc, mul_comm, mul_left_comm, derivative_mul ];
        ring

lemma hpoly_deriv (n : ℕ) (x : ℝ) : deriv (hpoly n) x = (n : ℝ) * hpoly (n - 1) x := by
  unfold hpoly;
  convert congr_arg ( fun p : ℤ[X] => ( aeval x p : ℝ ) ) ( derivative_hermite n ) using 1;
  · norm_num [ Polynomial.derivative_eval ];
  · norm_num [ Algebra.smul_def ]

lemma hasDerivAt_hpoly (n : ℕ) (x : ℝ) :
    HasDerivAt (hpoly n) ((n : ℝ) * hpoly (n - 1) x) x := by
      convert Polynomial.hasDerivAt_aeval ( hermite n ) x using 1;
      rw [ derivative_hermite, map_zsmul ] ; norm_num [ hpoly ]

lemma hasDerivAt_gwFun (x : ℝ) : HasDerivAt gwFun (-x * gwFun x) x := by
  convert HasDerivAt.exp ( HasDerivAt.neg ( hasDerivAt_pow 2 x |> HasDerivAt.div_const <| 2 ) ) using 1 ; ring!

/-! ## Rodrigues consequence and the differentiated Gaussian-weighted Hermite -/

/-
`Hₙ(x) e^{-x²/2} = (-1)ⁿ (d/dx)ⁿ e^{-x²/2}`.
-/
lemma hpoly_mul_gwFun (n : ℕ) (x : ℝ) :
    hpoly n x * gwFun x = (-1) ^ n * deriv^[n] gwFun x := by
      -- By definition of $gwFun$, we know that $gwFun x = Real.exp (-(x ^ 2 / 2))$.
      have h_gwFun_def : deriv^[n] gwFun x = (-1 : ℝ) ^ n * (aeval x (hermite n)) * gwFun x := by
        convert Polynomial.deriv_gaussian_eq_hermite_mul_gaussian n x using 1;
      by_cases h : Even n <;> simp_all +decide [ hpoly ]

/-
The derivative of `Hₙ e^{-x²/2}` is `-Hₙ₊₁ e^{-x²/2}`.
-/
lemma hasDerivAt_hpoly_mul_gwFun (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => hpoly n y * gwFun y) (-(hpoly (n + 1) x) * gwFun x) x := by
      have h_deriv : HasDerivAt (fun y => hpoly n y * gwFun y) ((n : ℝ) * hpoly (n - 1) x * gwFun x + hpoly n x * (-x * gwFun x)) x := by
        convert HasDerivAt.mul ( hasDerivAt_hpoly n x ) ( hasDerivAt_gwFun x ) using 1;
      convert h_deriv using 1 ; rw [ hpoly_add_one ] ; ring;
      rw [ hpoly_deriv ] ; ring

lemma deriv_hpoly_mul_gwFun (n : ℕ) (x : ℝ) :
    deriv (fun y => hpoly n y * gwFun y) x = -(hpoly (n + 1) x) * gwFun x := by
      convert HasDerivAt.deriv ( hasDerivAt_hpoly_mul_gwFun n x ) using 1

/-! ## Integrability of polynomial × Gaussian -/

lemma integrable_hpoly_mul_gwFun (n : ℕ) :
    Integrable (fun x => hpoly n x * gwFun x) := by
      -- We'll use the fact that $|x^k e^{-x^2/q}|$ is integrable for any $k \ge 0$, $q > 0$.
      have h_integrable : ∀ k : ℕ, ∀ q > 0, (MeasureTheory.Integrable (fun x : ℝ => abs (x^k * Real.exp (-(x^2/q)))) MeasureTheory.volume) := by
        intro k q hq;
        have := @integrable_rpow_mul_exp_neg_mul_sq;
        convert this ( show 0 < ( 1 / q ) by positivity ) ( show -1 < ( k : ℝ ) by linarith ) |> fun h => h.norm using 2 ; norm_num [ div_eq_inv_mul ];
      -- Since $Hₙ(x)$ is a polynomial of degree $n$, we can write it as $Hₙ(x) = \sum_{k=0}^n a_k x^k$ for some coefficients $a_k$.
      obtain ⟨a, ha⟩ : ∃ a : Fin (n + 1) → ℝ, ∀ x : ℝ, hpoly n x = ∑ k ∈ Finset.univ, a k * x ^ (k : ℕ) := by
        unfold hpoly;
        use fun k => ( hermite n |> Polynomial.coeff ) k;
        simp +decide [ Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range ];
        exact fun x => by rw [ Finset.sum_range ] ;
      simp_all +decide [ Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, gwFun ];
      refine' MeasureTheory.integrable_finset_sum _ fun i _ => _;
      refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.mono' ( h_integrable i 2 ( by norm_num ) ) _ _;
      · exact Continuous.aestronglyMeasurable ( by continuity );
      · norm_num [ abs_mul, abs_pow ]

lemma integrable_hpoly_mul_hpoly_mul_gwFun (m n : ℕ) :
    Integrable (fun x => hpoly m x * hpoly n x * gwFun x) := by
      -- Write `hpoly m x * hpoly n x * gwFun x` as `(hpoly m x * hpoly n x * Real.exp (-(x^2/4))) * Real.exp (-(x^2/4))`.
      suffices h_suff : Integrable (fun x => (hpoly m x * hpoly n x) * Real.exp (-(x^2 / 4)) * Real.exp (-(x^2 / 4))) (volume : MeasureTheory.Measure ℝ) by
        convert h_suff using 2 ; norm_num [ gwFun ] ; ring;
        rw [ ← Real.exp_nat_mul ] ; ring;
      -- The function $x \mapsto \exp(-x^2/4)$ is bounded.
      have h_bounded : ∃ C : ℝ, ∀ x : ℝ, abs (Real.exp (-(x^2 / 4))) ≤ C := by
        exact ⟨ 1, fun x => by rw [ abs_of_nonneg ( Real.exp_nonneg _ ) ] ; exact Real.exp_le_one_iff.mpr ( by nlinarith ) ⟩;
      -- The function $x \mapsto (hpoly m x * hpoly n x) * \exp(-x^2/4)$ is integrable.
      have h_integrable : Integrable (fun x => (hpoly m x * hpoly n x) * Real.exp (-(x^2 / 4))) (volume : MeasureTheory.Measure ℝ) := by
        have h_integrable : ∀ p : Polynomial ℝ, Integrable (fun x => p.eval x * Real.exp (-(x^2 / 4))) (volume : MeasureTheory.Measure ℝ) := by
          intro p
          have h_integrable : ∀ k : ℕ, Integrable (fun x => x^k * Real.exp (-(x^2 / 4))) (volume : MeasureTheory.Measure ℝ) := by
            intro k;
            have := @integrable_rpow_mul_exp_neg_mul_sq;
            convert @this ( 1 / 4 ) ( by norm_num ) ( k : ℝ ) ( by linarith ) using 3 ; ring;
            · norm_cast;
            · ring;
          simp_all +decide [ Polynomial.eval_eq_sum_range ];
          simp +decide only [Finset.sum_mul _ _ _, mul_assoc];
          exact MeasureTheory.integrable_finset_sum _ fun i hi => MeasureTheory.Integrable.const_mul ( h_integrable i ) _;
        convert h_integrable ( Polynomial.map ( algebraMap ℤ ℝ ) ( hermite m ) * Polynomial.map ( algebraMap ℤ ℝ ) ( hermite n ) ) using 2 ; norm_num [ hpoly ];
        simp +decide [ Polynomial.aeval_def, Polynomial.eval_map ];
      refine' h_integrable.norm.mul_const _ |> fun h => h.mono' _ _;
      exact h_bounded.choose;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable.aestronglyMeasurable ) ( Real.continuous_exp.comp_aestronglyMeasurable ( by exact Continuous.aestronglyMeasurable ( by continuity ) ) );
      · filter_upwards [ ] with x using by rw [ norm_mul ] ; exact mul_le_mul_of_nonneg_left ( h_bounded.choose_spec x ) ( norm_nonneg _ ) ;

/-! ## The Gaussian integral -/

lemma integral_gwFun : ∫ x, gwFun x = Real.sqrt (2 * π) := by
  convert integral_gaussian ( 1 / 2 ) using 1 <;> norm_num [ div_eq_inv_mul ];
  exact congr_arg _ ( funext fun x => by unfold gwFun; ring )

/-! ## Orthogonality of Hermite polynomials for `e^{-x²/2}` -/

/-
Base case: `∫ Hₘ e^{-x²/2} = δₘ₀ √(2π)`.
-/
lemma integral_hpoly_mul_gwFun (m : ℕ) :
    (∫ x, hpoly m x * gwFun x) = if m = 0 then Real.sqrt (2 * π) else 0 := by
      induction' m with m ih;
      · simp [hpoly_zero, integral_gwFun];
      · -- Apply the recurrence relation for the integral.
        have h_recurrence : ∫ x, hpoly (m + 1) x * gwFun x = -∫ x, deriv (fun x => hpoly m x * gwFun x) x := by
          rw [ ← MeasureTheory.integral_neg ] ; congr ; ext x ; rw [ deriv_hpoly_mul_gwFun ] ; ring;
        -- By the fundamental theorem of calculus, the integral of the derivative of a function over the entire real line is zero.
        have h_ftc : ∀ a b : ℝ, ∫ x in a..b, deriv (fun x => hpoly m x * gwFun x) x = hpoly m b * gwFun b - hpoly m a * gwFun a := by
          intros a b; rw [ intervalIntegral.integral_deriv_eq_sub ];
          · exact fun x hx => DifferentiableAt.mul ( by exact ( hasDerivAt_hpoly m x |> HasDerivAt.differentiableAt ) ) ( by exact ( hasDerivAt_gwFun x |> HasDerivAt.differentiableAt ) );
          · apply_rules [ Continuous.intervalIntegrable ];
            unfold hpoly gwFun;
            norm_num [ Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range ];
            fun_prop;
        -- Apply the fundamental theorem of calculus to the interval $(-\infty, \infty)$.
        have h_ftc_infty : Filter.Tendsto (fun b => ∫ x in (-b)..b, deriv (fun x => hpoly m x * gwFun x) x) Filter.atTop (nhds (∫ x, deriv (fun x => hpoly m x * gwFun x) x)) := by
          apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral ];
          · convert integrable_hpoly_mul_gwFun ( m + 1 ) |> fun h => h.neg using 1;
            exact funext fun x => by simpa using deriv_hpoly_mul_gwFun m x;
          · exact Filter.tendsto_neg_atTop_atBot;
          · exact Filter.tendsto_id;
        -- Since $hpoly m x * gwFun x$ tends to zero as $x$ goes to infinity, the limit of the integral over $(-b, b)$ as $b$ goes to infinity is zero.
        have h_lim_zero : Filter.Tendsto (fun b => hpoly m b * gwFun b) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun b => hpoly m (-b) * gwFun (-b)) Filter.atTop (nhds 0) := by
          have h_lim_zero : ∀ p : Polynomial ℝ, Filter.Tendsto (fun x => p.eval x * Real.exp (-x ^ 2 / 2)) Filter.atTop (nhds 0) := by
            intro p
            have h_lim_zero : Filter.Tendsto (fun x => p.eval x * Real.exp (-x ^ 2 / 2)) Filter.atTop (nhds 0) := by
              have h_poly_exp : ∀ n : ℕ, Filter.Tendsto (fun x => x ^ n * Real.exp (-x ^ 2 / 2)) Filter.atTop (nhds 0) := by
                intro n
                have h_poly_exp : Filter.Tendsto (fun x => x ^ n * Real.exp (-x)) Filter.atTop (nhds 0) := by
                  exact ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n );
                refine' squeeze_zero_norm' _ h_poly_exp;
                filter_upwards [ Filter.eventually_ge_atTop 2 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; nlinarith
              simp_all +decide [ Polynomial.eval_eq_sum_range ];
              simpa [ Finset.sum_mul _ _ _, mul_assoc ] using tendsto_finset_sum _ fun i hi => Filter.Tendsto.const_mul ( p.coeff i ) ( h_poly_exp i )
            exact h_lim_zero;
          have h_lim_zero_neg : ∀ p : Polynomial ℝ, Filter.Tendsto (fun x => p.eval (-x) * Real.exp (-x ^ 2 / 2)) Filter.atTop (nhds 0) := by
            intro p; specialize h_lim_zero ( p.comp ( -Polynomial.X ) ) ; aesop;
          simp_all +decide [ hpoly, gwFun ];
          simp_all +decide [ neg_div, Polynomial.aeval_def ];
          simp_all +decide [ Polynomial.eval₂_eq_eval_map ];
        simp_all +decide [ sub_eq_add_neg ];
        exact tendsto_nhds_unique h_ftc_infty ( by simpa using h_lim_zero.1.add ( h_lim_zero.2.neg ) )

/-
The single-integration-by-parts recurrence:
`∫ Hₘ Hₙ₊₁ e^{-x²/2} = m ∫ Hₘ₋₁ Hₙ e^{-x²/2}`.
-/
lemma orthogonality_recurrence (m n : ℕ) :
    (∫ x, hpoly m x * hpoly (n + 1) x * gwFun x)
      = (m : ℝ) * ∫ x, hpoly (m - 1) x * hpoly n x * gwFun x := by
        have h_int_parts : ∫ x, hpoly m x * (-(hpoly (n + 1) x) * gwFun x) = - ∫ x, (m * hpoly (m - 1) x) * (hpoly n x * gwFun x) := by
          convert integral_mul_deriv_eq_deriv_mul_of_integrable _ _ _ _ _ using 1;
          · exact fun x => hasDerivAt_hpoly m x;
          · exact fun x => hasDerivAt_hpoly_mul_gwFun n x;
          · convert ( integrable_hpoly_mul_hpoly_mul_gwFun m ( n + 1 ) ).neg using 1 ; ext ; norm_num ; ring;
          · convert integrable_hpoly_mul_hpoly_mul_gwFun ( m - 1 ) n |> fun h => h.const_mul ( m : ℝ ) using 1 ; ext ; norm_num ; ring;
          · convert integrable_hpoly_mul_hpoly_mul_gwFun m n using 1 ; ext ; norm_num ; ring;
        simp_all +decide [ mul_assoc, MeasureTheory.integral_neg, MeasureTheory.integral_const_mul ]

/-
**Orthogonality of the Hermite polynomials** for the weight `e^{-x²/2}`.
-/
theorem hermite_orthogonality (m n : ℕ) :
    (∫ x, hpoly m x * hpoly n x * gwFun x)
      = if m = n then (n ! : ℝ) * Real.sqrt (2 * π) else 0 := by
        induction' n with n ih generalizing m;
        · have := integral_hpoly_mul_gwFun m; simp_all +decide [ mul_comm, gwFun ] ;
        · convert orthogonality_recurrence m n using 1;
          cases m <;> simp_all +decide [ Nat.factorial_succ, mul_assoc ]

/-! ## Schwartz bundling -/

/-
Smoothness of the Gaussian `e^{-x²/4}`.
-/
lemma gaussQ_smooth : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (-(x ^ 2 / 4))) := by
  exact ContDiff.exp <| ContDiff.neg <| ContDiff.div_const ( contDiff_id.pow 2 ) _

/-
Every iterated derivative of `e^{-x²/4}` is a polynomial times `e^{-x²/4}`.
-/
lemma iteratedDeriv_gaussQ_eq (n : ℕ) :
    ∃ Q : ℝ[X], ∀ x : ℝ,
      iteratedDeriv n (fun x : ℝ => Real.exp (-(x ^ 2 / 4))) x = aeval x Q * Real.exp (-(x ^ 2 / 4)) := by
  induction' n with n ih <;> simp_all +decide [ iteratedDeriv_succ ];
  · exact ⟨ 1, fun x => by norm_num ⟩;
  · obtain ⟨ Q, hQ ⟩ := ih; use Polynomial.derivative Q - Polynomial.C ( 1 / 2 : ℝ ) * Polynomial.X * Q; intro x; rw [ show iteratedDeriv n ( fun x => Real.exp ( - ( x ^ 2 / 4 ) ) ) = _ from funext hQ ] ; norm_num [ Polynomial.differentiableAt ] ; ring;

/-
A polynomial times the Gaussian `e^{-x²/4}` (with an extra power of `|x|`) is bounded.
-/
lemma poly_mul_gaussQ_bounded (Q : ℝ[X]) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ^ k * (|aeval x Q| * Real.exp (-(x ^ 2 / 4))) ≤ C := by
      -- We'll use the fact that |x|^k * exp(-x^2 / 4) is bounded.
      have h_bound : ∀ k : ℕ, ∃ C, ∀ x : ℝ, |x|^k * Real.exp (-(x ^ 2 / 4)) ≤ C := by
        intro k
        have h_lim : Filter.Tendsto (fun x : ℝ => |x|^k * Real.exp (-(x ^ 2 / 4))) Filter.atTop (nhds 0) := by
          have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k;
          refine' squeeze_zero_norm' _ this;
          filter_upwards [ Filter.eventually_ge_atTop 4 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ abs_of_nonneg ( by positivity ) ] ; gcongr ; nlinarith;
        obtain ⟨ C, hC ⟩ := Metric.tendsto_atTop.mp h_lim 1 zero_lt_one;
        -- Since $|x|^k * \exp(-(x^2 / 4))$ is continuous and tends to $0$ as $|x| \to \infty$, it is bounded on the compact interval $[-C, C]$.
        obtain ⟨ M, hM ⟩ : ∃ M, ∀ x ∈ Set.Icc (-C) C, |x|^k * Real.exp (-(x ^ 2 / 4)) ≤ M := by
          exact ⟨ _, fun x hx => le_csSup ( IsCompact.bddAbove ( isCompact_Icc.image ( show Continuous fun x : ℝ => |x| ^ k * Real.exp ( - ( x ^ 2 / 4 ) ) from by continuity ) ) ) ( Set.mem_image_of_mem _ hx ) ⟩;
        exact ⟨ Max.max M 1, fun x => if hx : |x| ≤ C then le_trans ( hM x ⟨ by linarith [ abs_le.mp hx ], by linarith [ abs_le.mp hx ] ⟩ ) ( le_max_left _ _ ) else le_trans ( le_of_lt ( by simpa using hC ( |x| ) ( by linarith ) ) ) ( le_max_right _ _ ) ⟩;
      -- Since $|Q(x)|$ is a polynomial, it is bounded by some constant $M$.
      obtain ⟨M, hM⟩ : ∃ M, ∀ x : ℝ, |(aeval x) Q| ≤ M * (1 + |x| ^ Q.natDegree) := by
        -- Since $|Q(x)|$ is a polynomial, it is bounded by some constant $M$ for all $x$.
        have h_poly_bound : ∃ M, ∀ x : ℝ, |(aeval x) Q| ≤ M * (1 + |x| ^ Q.natDegree) := by
          have h_poly_bound_aux : ∀ x : ℝ, |(aeval x) Q| ≤ ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i| * |x| ^ i := by
            intro x; rw [ Polynomial.aeval_eq_sum_range ] ; exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun i hi => by simp +decide [ abs_mul ] ) ;
          use ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i|;
          intro x; specialize h_poly_bound_aux x; rw [ Finset.sum_mul _ _ _ ] ; refine le_trans h_poly_bound_aux ?_; gcongr ;
          by_cases hx : |x| ≤ 1;
          · exact le_add_of_le_of_nonneg ( pow_le_one₀ ( abs_nonneg x ) hx ) ( by positivity );
          · exact le_add_of_nonneg_of_le zero_le_one ( pow_le_pow_right₀ ( by linarith ) ( Finset.mem_range_succ_iff.mp ‹_› ) );
        exact h_poly_bound;
      obtain ⟨ C₁, hC₁ ⟩ := h_bound k; obtain ⟨ C₂, hC₂ ⟩ := h_bound ( k + Q.natDegree ) ; use M * ( C₁ + C₂ ) ; intro x; specialize hM x; specialize hC₁ x; specialize hC₂ x; ring_nf at *;
      nlinarith [ show 0 ≤ M by exact le_of_not_gt fun h => by nlinarith [ abs_nonneg ( aeval x Q ), show 0 ≤ |x| ^ Q.natDegree by positivity, show 0 ≤ |x| ^ k * Real.exp ( x ^ 2 * ( -1 / 4 ) ) by positivity ], show 0 ≤ |x| ^ k * Real.exp ( x ^ 2 * ( -1 / 4 ) ) by positivity, show 0 ≤ |x| ^ Q.natDegree * |x| ^ k * Real.exp ( x ^ 2 * ( -1 / 4 ) ) by positivity ]

/-
Rapid decay of all derivatives of the Gaussian `e^{-x²/4}`.
-/
lemma gaussQ_decay : ∀ k n : ℕ, ∃ C : ℝ, ∀ x : ℝ,
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ => Real.exp (-(x ^ 2 / 4))) x‖ ≤ C := by
      intro k n;
      obtain ⟨ Q, hQ ⟩ := iteratedDeriv_gaussQ_eq n;
      obtain ⟨ C, hC ⟩ := poly_mul_gaussQ_bounded Q k; use C; intros x; simp_all +decide [ norm_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv ] ;

/-- The Gaussian `e^{-x²/4}` as a Schwartz function. -/
def gaussQ : 𝓢(ℝ, ℝ) where
  toFun x := Real.exp (-(x ^ 2 / 4))
  smooth' := gaussQ_smooth
  decay' := gaussQ_decay

@[simp] lemma gaussQ_apply (x : ℝ) : gaussQ x = Real.exp (-(x ^ 2 / 4)) := rfl

/-
Hermite polynomials have temperate growth.
-/
lemma hpoly_hasTemperateGrowth (n : ℕ) : Function.HasTemperateGrowth (hpoly n) := by
  unfold hpoly;
  simp +decide [ Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range ];
  refine' Function.HasTemperateGrowth.sum fun i hi => _;
  convert Function.HasTemperateGrowth.const _ |> Function.HasTemperateGrowth.mul <| Function.HasTemperateGrowth.pow ( Function.HasTemperateGrowth.id ) i using 1

lemma hermiteFun_hasTemperateGrowth (n : ℕ) :
    Function.HasTemperateGrowth (hermiteFun n) := by
      refine' Function.HasTemperateGrowth.mul _ _;
      · exact Function.HasTemperateGrowth.const _ |> Function.HasTemperateGrowth.mul <| hpoly_hasTemperateGrowth n;
      · convert SchwartzMap.hasTemperateGrowth gaussQ using 1

/-- The Hermite function bundled as a Schwartz function. -/
def hermiteSchwartz (n : ℕ) : 𝓢(ℝ, ℝ) :=
  hermiteC n • SchwartzMap.smulLeftCLM ℝ (hpoly n) gaussQ

@[simp] lemma hermiteSchwartz_apply (n : ℕ) (x : ℝ) : hermiteSchwartz n x = hermiteFun n x := by
  unfold hermiteSchwartz; norm_num [ smul_eq_mul, mul_comm, mul_assoc, mul_left_comm, hermiteFun, hermiteC ] ;
  erw [ SchwartzMap.smulLeftCLM_apply_apply ( hpoly_hasTemperateGrowth n ) ] ; norm_num ; ring!;

/-- Task M3b consumes this: each Hermite function is a Schwartz function. -/
lemma hermiteFun_mem_schwartz (n : ℕ) :
    ∃ f : 𝓢(ℝ, ℝ), ⇑f = hermiteFun n := ⟨hermiteSchwartz n, funext (hermiteSchwartz_apply n)⟩

/-! ## Orthonormality of the Hermite functions (Lebesgue measure) -/

lemma integrable_hermiteFun_mul (m n : ℕ) :
    Integrable (fun x => hermiteFun m x * hermiteFun n x) := by
      have h_simp : ∀ x : ℝ, hermiteFun m x * hermiteFun n x = (hermiteC m * hermiteC n) * (hpoly m x * hpoly n x * gwFun x) := by
        unfold hermiteFun gwFun; intros; ring;
        rw [ ← Real.exp_nat_mul ] ; ring;
      simpa only [ h_simp ] using ( integrable_hpoly_mul_hpoly_mul_gwFun m n ) |> fun h => h.const_mul _

/-
`∫ hₘ hₙ = δₘₙ`.
-/
theorem hermiteFun_orthonormal_integral (m n : ℕ) :
    (∫ x, hermiteFun m x * hermiteFun n x) = if m = n then 1 else 0 := by
      -- Write `hermiteFun m x * hermiteFun n x` as `(hermiteC m * hermiteC n) * (hpoly m x * hpoly n x * gwFun x)` since `Real.exp(-(x^2/4))^2 = gwFun x`, via `← Real.exp_add`, `ring`.
      have h_simp : ∀ x : ℝ, hermiteFun m x * hermiteFun n x = (hermiteC m * hermiteC n) * (hpoly m x * hpoly n x * gwFun x) := by
        unfold hermiteFun gwFun; intros; ring;
        rw [ ← Real.exp_nat_mul ] ; ring;
      split_ifs <;> simp_all +decide [ MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ];
      · rw [ hermite_orthogonality ] ; norm_num [ hermiteC ];
        ring ; norm_num [ Nat.factorial_ne_zero, Real.pi_pos.le, Real.pi_pos.ne', Real.sqrt_ne_zero'.mpr Real.pi_pos ];
      · exact Or.inr ( by rw [ hermite_orthogonality m n ] ; aesop )

/-- The Hermite functions as elements of `L²(ℝ)`. -/
def hermiteLp (n : ℕ) : Lp ℝ 2 (volume : Measure ℝ) := (hermiteSchwartz n).toLp 2 volume

lemma inner_hermiteLp (m n : ℕ) :
    inner ℝ (hermiteLp m) (hermiteLp n) = ∫ x, hermiteFun m x * hermiteFun n x := by
      convert MeasureTheory.integral_congr_ae _;
      have h_ae_eq : ∀ᵐ x ∂volume, (hermiteLp m) x = hermiteFun m x ∧ (hermiteLp n) x = hermiteFun n x := by
        filter_upwards [ (hermiteSchwartz m).coeFn_toLp 2 volume, (hermiteSchwartz n).coeFn_toLp 2 volume ] with x hx₁ hx₂ using ⟨ hx₁ ▸ hermiteSchwartz_apply m x, hx₂ ▸ hermiteSchwartz_apply n x ⟩;
      filter_upwards [ h_ae_eq ] with x hx using by rw [ hx.1, hx.2 ] ; norm_num [ mul_comm ] ;

theorem hermiteLp_orthonormal : Orthonormal ℝ hermiteLp := by
  rw [ orthonormal_iff_ite ];
  intro i j; rw [ inner_hermiteLp i j ] ; rw [ hermiteFun_orthonormal_integral i j ] ;

/-! ## Completeness (analytic heart) -/

/-
`x^k · e^{-x²/4} · f` is integrable for `f ∈ L²`.
-/
lemma integrable_pow_gaussQuarter_mul_real (f : ℝ → ℝ) (hf : MemLp f 2 volume) (k : ℕ) :
    Integrable (fun x => x ^ k * (Real.exp (-(x ^ 2 / 4)) * f x)) := by
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun x => ‖x ^ k * Real.exp ( - ( x ^ 2 / 4 ) )‖ ^ 2 + ‖f x‖ ^ 2;
      · refine' MeasureTheory.Integrable.add _ _;
        · have h_integrable : MeasureTheory.Integrable (fun x => x^(2 * k) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
            have := @integrable_rpow_mul_exp_neg_mul_sq;
            convert @this ( 1 / 2 ) ( by norm_num ) ( 2 * k ) ( by linarith ) using 3 ; ring;
            · norm_cast;
            · ring;
          convert h_integrable using 2 ; norm_num ; ring;
          rw [ ← Real.exp_nat_mul ] ; ring;
          norm_num [ pow_mul' ];
        · simpa using hf.integrable_norm_pow two_ne_zero;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( Continuous.aestronglyMeasurable ( by continuity ) ) ( MeasureTheory.AEStronglyMeasurable.mul ( Continuous.aestronglyMeasurable ( by continuity ) ) hf.aestronglyMeasurable );
      · simp +zetaDelta at *;
        filter_upwards [ ] with x using by nlinarith only [ sq_nonneg ( |x| ^ k * Real.exp ( - ( x ^ 2 / 4 ) ) - |f x| ), abs_mul_abs_self ( f x ), show 0 ≤ |x| ^ k * Real.exp ( - ( x ^ 2 / 4 ) ) by positivity ] ;

/-
`(aeval x p) · e^{-x²/4} · f` is integrable for `f ∈ L²`.
-/
lemma integrable_aeval_gaussQuarter_mul_real (f : ℝ → ℝ) (hf : MemLp f 2 volume) (p : ℝ[X]) :
    Integrable (fun x => aeval x p * (Real.exp (-(x ^ 2 / 4)) * f x)) := by
      simp_all +decide [ Polynomial.aeval_eq_sum_range ];
      simp +decide only [Finset.sum_mul _ _ _, mul_assoc];
      refine' MeasureTheory.integrable_finset_sum _ fun i hi => _;
      exact MeasureTheory.Integrable.const_mul ( integrable_pow_gaussQuarter_mul_real f hf i ) _

/-
Monomials are integrated to zero: if `f ∈ L²` is orthogonal to every Hermite function,
then `∫ xᵏ e^{-x²/4} f = 0`.
-/
lemma moments_zero_of_orthogonal (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (h : ∀ n, (∫ x, hermiteFun n x * f x) = 0) (k : ℕ) :
    (∫ x, (x ^ k : ℝ) * (Real.exp (-(x ^ 2 / 4)) * f x)) = 0 := by
      induction' k using Nat.strong_induction_on with k ih;
      -- By definition of $hermiteFun$, we can rewrite the integral.
      have h_integral : ∫ x, hermiteFun k x * f x = hermiteC k * ∫ x, ∑ i ∈ Finset.range (k + 1), (hermite k).coeff i * x ^ i * (Real.exp (-(x ^ 2 / 4)) * f x) := by
        rw [ ← MeasureTheory.integral_const_mul ] ; congr ; ext x ; simp +decide [ hermiteFun, hpoly, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range ] ; ring;
        simp +decide only [mul_comm, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm];
      rw [ MeasureTheory.integral_finset_sum ] at h_integral;
      · simp_all +decide [ Finset.sum_range_succ, mul_assoc, MeasureTheory.integral_const_mul ];
        exact eq_neg_of_add_eq_zero_right ( h_integral.resolve_left ( by exact ne_of_gt ( inv_pos.mpr ( Real.sqrt_pos.mpr ( by positivity ) ) ) ) ) ▸ by rw [ Finset.sum_eq_zero fun i hi => by rw [ ih i ( Finset.mem_range.mp hi ) ] ; ring ] ; ring;
      · intro i hi; specialize ih i; by_cases hi' : i < k <;> simp_all +decide [ mul_assoc, MeasureTheory.integral_const_mul ] ;
        · exact MeasureTheory.Integrable.const_mul ( integrable_pow_gaussQuarter_mul_real f hf i ) _;
        · exact MeasureTheory.Integrable.const_mul ( integrable_pow_gaussQuarter_mul_real f hf i ) _

/-
The `L¹` function `g = f · e^{-x²/4}` (complexified).
-/
lemma integrable_gauss_quarter_mul (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    Integrable (fun x => (f x : ℂ) * Real.exp (-(x ^ 2 / 4))) := by
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun x => ‖f x‖ ^ 2 + Real.exp ( - ( x ^ 2 / 4 ) ) ^ 2;
      · refine' MeasureTheory.Integrable.add _ _;
        · simpa using hf.integrable_norm_rpow ( by norm_num );
        · norm_num [ ← Real.exp_nat_mul ];
          simpa [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm ] using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 2 / 4 ) );
      · exact MeasureTheory.AEStronglyMeasurable.mul ( Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1 ) ( Complex.continuous_ofReal.comp_aestronglyMeasurable ( Real.continuous_exp.comp_aestronglyMeasurable ( by exact Continuous.aestronglyMeasurable ( by continuity ) ) ) );
      · filter_upwards [ ] with x using by norm_cast; simpa [ abs_mul, Real.exp_pos ] using by nlinarith [ sq_nonneg ( |f x| - Real.exp ( - ( x ^ 2 / 4 ) ) ), abs_mul_abs_self ( f x ), Real.exp_pos ( - ( x ^ 2 / 4 ) ) ] ;

lemma integrable_pow_gauss_quarter_mul (f : ℝ → ℝ) (hf : MemLp f 2 volume) (k : ℕ) :
    Integrable (fun x : ℝ => ((x : ℂ) ^ k) * ((f x : ℂ) * (Real.exp (-(x ^ 2 / 4)) : ℂ))) := by
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun x => |x ^ k * Real.exp ( - ( x ^ 2 / 4 ) )| * |f x|;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => ( x ^ k * Real.exp ( - ( x ^ 2 / 4 ) ) ) ^ 2 + f x ^ 2;
        · refine' MeasureTheory.Integrable.add _ _;
          · have := @integrable_rpow_mul_exp_neg_mul_sq;
            convert @this ( 1 / 2 ) ( by norm_num ) ( 2 * k ) ( by linarith ) using 1 ; norm_num ; ring;
            norm_num [ ← Real.exp_nat_mul ] ; ext ; ring;
            norm_cast ; ring;
          · exact MeasureTheory.MemLp.integrable_sq hf;
        · exact MeasureTheory.AEStronglyMeasurable.mul ( Continuous.aestronglyMeasurable ( by continuity ) ) ( hf.1.norm );
        · filter_upwards [ ] with x using by rw [ Real.norm_eq_abs, abs_of_nonneg ( by positivity ) ] ; nlinarith [ sq_nonneg ( |x ^ k * Real.exp ( - ( x ^ 2 / 4 ) )| - |f x| ), abs_mul_abs_self ( x ^ k * Real.exp ( - ( x ^ 2 / 4 ) ) ), abs_mul_abs_self ( f x ) ] ;
      · refine' MeasureTheory.AEStronglyMeasurable.mul _ _;
        · exact Continuous.aestronglyMeasurable ( by continuity );
        · exact MeasureTheory.AEStronglyMeasurable.mul ( Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1 ) ( Complex.continuous_ofReal.comp_aestronglyMeasurable ( Real.continuous_exp.comp_aestronglyMeasurable ( by exact Continuous.aestronglyMeasurable ( by continuity ) ) ) );
      · norm_cast ; norm_num [ abs_mul, mul_assoc, mul_comm, mul_left_comm ]

/-
Complex moments vanish: `∫ xⁿ · e^{-x²/4} · f = 0`.
-/
lemma cmoments_zero (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (h : ∀ n, (∫ x, hermiteFun n x * f x) = 0) (n : ℕ) :
    (∫ (x : ℝ), (x : ℂ) ^ n * ((f x : ℂ) * (Real.exp (-(x ^ 2 / 4)) : ℂ))) = 0 := by
      convert congr_arg ( ( ↑ ) : ℝ → ℂ ) ( moments_zero_of_orthogonal f hf h n ) using 1;
      convert integral_ofReal using 3 ; norm_num [ mul_assoc, mul_comm, mul_left_comm ]

/-
The dominating function for the term-by-term Fourier expansion is integrable.
-/
lemma integrable_dominating (f : ℝ → ℝ) (hf : MemLp f 2 volume) (c : ℝ) :
    Integrable (fun x => |f x| * Real.exp (-(x ^ 2 / 4)) * Real.exp (c * |x|)) := by
      have h_integrable : MeasureTheory.Integrable (fun x => |f x| * Real.exp (-(x ^ 2 / 8))) volume := by
        have h_integrable : MemLp (fun x => |f x|) 2 volume ∧ MemLp (fun x => Real.exp (-(x ^ 2 / 8))) 2 volume := by
          refine' ⟨ hf.norm, _ ⟩;
          have h_integrable : MeasureTheory.Integrable (fun x => Real.exp (-(x ^ 2 / 4))) volume := by
            simpa [ div_eq_inv_mul ] using ( integrable_exp_neg_mul_sq ( by norm_num : ( 0 : ℝ ) < 1 / 4 ) );
          rw [ MeasureTheory.memLp_two_iff_integrable_sq ];
          · convert h_integrable using 2 ; rw [ ← Real.exp_nat_mul ] ; ring;
          · exact Continuous.aestronglyMeasurable ( by continuity );
        exact h_integrable.1.integrable_mul h_integrable.2;
      refine' h_integrable.mul_const ( Real.exp ( 2 * c ^ 2 ) ) |> fun h => h.mono' _ _;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( hf.1.norm ) ( Continuous.aestronglyMeasurable ( by continuity ) ) ) ( Continuous.aestronglyMeasurable ( by continuity ) );
      · norm_num [ mul_assoc, ← Real.exp_add ];
        filter_upwards [ ] with x using mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by cases abs_cases x <;> nlinarith [ sq_nonneg ( |x| - 4 * c ) ] ) ( abs_nonneg _ )

/-
The Fourier transform of `g = f · e^{-x²/4}` vanishes identically.
-/
lemma fourier_gauss_quarter_mul_eq_zero (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (h : ∀ n, (∫ x, hermiteFun n x * f x) = 0) (xi : ℝ) :
    𝓕 (fun x : ℝ => (f x : ℂ) * (Real.exp (-(x ^ 2 / 4)) : ℂ)) xi = 0 := by
      -- Let $g(v) = f(v) \cdot e^{-v^2/4}$.
      set g : ℝ → ℂ := fun v => (f v) * (Real.exp (-(v ^ 2 / 4)));
      -- By definition of $g$, we know that $\int g(v) e^{-2\pi i v \xi} dv = \int f(v) e^{-v^2/4} e^{-2\pi i v \xi} dv$.
      have h_fourier : ∫ v, g v * Complex.exp (-2 * Real.pi * Complex.I * v * xi) = 0 := by
        -- By definition of $g$, we know that $\int g(v) e^{-2\pi i v \xi} dv = \lim_{N \to \infty} \int g(v) \sum_{n=0}^{N-1} \frac{(-2\pi i v \xi)^n}{n!} dv$.
        have h_fourier_series : Filter.Tendsto (fun N => ∫ v, g v * (∑ n ∈ Finset.range N, ((-2 * Real.pi * Complex.I * v * xi) ^ n) / (Nat.factorial n))) Filter.atTop (nhds (∫ v, g v * Complex.exp (-2 * Real.pi * Complex.I * v * xi))) := by
          refine' MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _;
          use fun v => ‖g v‖ * Real.exp ( 2 * Real.pi * |xi| * |v| );
          · intro n;
            refine' MeasureTheory.AEStronglyMeasurable.mul _ _;
            · exact MeasureTheory.AEStronglyMeasurable.mul ( Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1 ) ( Complex.continuous_ofReal.comp_aestronglyMeasurable ( Real.continuous_exp.comp_aestronglyMeasurable ( by exact Continuous.aestronglyMeasurable ( by continuity ) ) ) );
            · exact Continuous.aestronglyMeasurable ( by continuity );
          · convert integrable_dominating f hf ( 2 * Real.pi * |xi| ) using 1;
            norm_num +zetaDelta at *;
            norm_num [ Complex.norm_exp, sq ];
          · intro n; filter_upwards [ ] with x; norm_num [ Complex.norm_exp ];
            gcongr;
            refine' le_trans ( norm_sum_le _ _ ) _;
            norm_num [ Complex.norm_exp, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ];
            exact le_trans ( Finset.sum_le_sum fun _ _ => by rw [ abs_of_nonneg Real.pi_pos.le ] ; ring_nf; norm_num ) ( Summable.sum_le_tsum ( Finset.range n ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
          · exact Filter.Eventually.of_forall fun x => tendsto_const_nhds.mul ( by simpa only [ Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div ] using Summable.hasSum ( show Summable _ from by exact Summable.of_norm <| by simpa [ Complex.norm_exp, Complex.norm_exp ] using Real.summable_pow_div_factorial _ ) |> HasSum.tendsto_sum_nat );
        -- By definition of $g$, we know that $\int g(v) \sum_{n=0}^{N-1} \frac{(-2\pi i v \xi)^n}{n!} dv = \sum_{n=0}^{N-1} \frac{(-2\pi i \xi)^n}{n!} \int g(v) v^n dv$.
        have h_fourier_series_sum : ∀ N : ℕ, ∫ v, g v * (∑ n ∈ Finset.range N, ((-2 * Real.pi * Complex.I * v * xi) ^ n) / (Nat.factorial n)) = ∑ n ∈ Finset.range N, ((-2 * Real.pi * Complex.I * xi) ^ n) / (Nat.factorial n) * ∫ v, g v * v ^ n := by
          intro N; simp +decide only [mul_comm, mul_left_comm, Finset.mul_sum _ _ _, ← integral_const_mul] ;
          rw [ MeasureTheory.integral_finset_sum ];
          · exact Finset.sum_congr rfl fun _ _ => by congr; ext; ring;
          · intro i hi; convert integrable_pow_gauss_quarter_mul f hf i |> fun h => h.const_mul ( ( Complex.I * ( xi * ( Real.pi * -2 ) ) ) ^ i / ( i ! : ℂ ) ) using 2 ; ring;
        -- By definition of $g$, we know that $\int g(v) v^n dv = 0$ for all $n$.
        have h_fourier_series_zero : ∀ n : ℕ, ∫ v, g v * v ^ n = 0 := by
          intro n
          have := cmoments_zero f hf h n
          simp_all +decide [ mul_comm, mul_left_comm ];
          convert this using 3 ; ring!;
          norm_num [ Complex.exp_re, Complex.exp_im ];
        aesop;
      convert h_fourier using 1;
      rw [ Real.fourier_eq' ];
      norm_num [ mul_assoc, mul_comm, mul_left_comm, inner ]

/-
**`L¹`-Fourier injectivity.** An integrable function whose Fourier transform vanishes
everywhere is zero almost everywhere.
-/
lemma ae_zero_of_fourier_zero (g : ℝ → ℂ) (hg : Integrable g)
    (hfg : ∀ ξ, 𝓕 g ξ = 0) : g =ᵐ[volume] 0 := by
      have h_fourier_zero : ∀ ψ : SchwartzMap ℝ ℂ, ∫ x, g x * ψ x = 0 := by
        intro ψ;
        -- Let `φs : 𝓢(ℝ, ℂ)` be the inverse Fourier transform of `ψ`.
        set φs : SchwartzMap ℝ ℂ := FourierTransform.fourierInv ψ;
        have h_fourier_zero : ∫ ξ, (𝓕 g ξ) * (φs ξ) = ∫ x, g x * (𝓕 φs x) := by
          convert VectorFourier.integral_fourierIntegral_smul_eq_flip _ _ _ _ using 1;
          all_goals try infer_instance;
          · simp +decide [ VectorFourier.fourierIntegral ];
            congr! 2;
          · exact Real.continuous_fourierChar;
          · fun_prop;
          · exact hg;
          · exact φs.integrable;
        aesop;
      have h_fourier_zero : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∫ x, g x * (ψ x : ℂ) = 0 := by
        intro ψ hψ hψ';
        convert h_fourier_zero ( HasCompactSupport.toSchwartzMap ( show HasCompactSupport ( fun x => ( ψ x : ℂ ) ) from ?_ ) <| by
                                                                    exact Complex.ofRealCLM.contDiff.comp hψ ) using 1
        generalize_proofs at *;
        exact hψ'.mono fun x hx => by simpa using hx;
      have h_ae_zero : ∀ᵐ x ∂volume, g x = 0 := by
        have h_loc_int : LocallyIntegrable g volume := by
          exact hg.locallyIntegrable
        convert ae_eq_zero_of_integral_contDiff_smul_eq_zero h_loc_int _;
        simp_all +decide [ mul_comm, Algebra.smul_def ];
      exact h_ae_zero

/-
**Completeness at the function level.**
-/
theorem hermite_complete_fun (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (h : ∀ n, (∫ x, hermiteFun n x * f x) = 0) :
    f =ᵐ[volume] 0 := by
      convert ae_zero_of_fourier_zero ( fun x => ( f x : ℂ ) * ( Real.exp ( - ( x ^ 2 / 4 ) ) : ℂ ) ) ( integrable_gauss_quarter_mul f hf ) ( fourier_gauss_quarter_mul_eq_zero f hf h ) using 1;
      norm_num [ Filter.EventuallyEq, Complex.exp_ne_zero ]

/-
**Completeness.** Any `L²` function orthogonal to every Hermite function is zero.
-/
theorem hermite_complete (f : Lp ℝ 2 (volume : Measure ℝ))
    (h : ∀ n, inner ℝ (hermiteLp n) f = 0) : f = 0 := by
      -- By definition of $hermiteLp$, we know that $hermiteLp n = (hermiteSchwartz n).toLp 2 volume$.
      have h_hermiteLp : ∀ n, (hermiteLp n : ℝ → ℝ) =ᵐ[volume] (hermiteFun n : ℝ → ℝ) := by
        intro n;
        convert SchwartzMap.coeFn_toLp ( hermiteSchwartz n ) 2 volume;
        exact funext fun x => hermiteSchwartz_apply n x ▸ rfl;
      have h_inner_zero : ∀ n, (∫ x, hermiteFun n x * (f : ℝ → ℝ) x) = 0 := by
        intro n; specialize h n; simp_all +decide [ MeasureTheory.L2.inner_def ] ;
        rw [ ← h, ← MeasureTheory.integral_congr_ae ];
        filter_upwards [ h_hermiteLp n ] with x hx using by rw [ hx, mul_comm ] ;
      convert hermite_complete_fun ( f : ℝ → ℝ ) ( MeasureTheory.Lp.memLp f ) h_inner_zero using 1;
      exact Lp.eq_zero_iff_ae_eq_zero

/-! ## Packaging as a Hilbert basis -/

theorem hermiteLp_span_dense :
    (⊤ : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)))
      ≤ (Submodule.span ℝ (Set.range hermiteLp)).topologicalClosure := by
        -- By definition of completeness, if a function is orthogonal to every element in the span of the Hermite functions, then it must be zero.
        have h_complete : ∀ f : Lp ℝ 2 (volume : Measure ℝ), (∀ n, inner ℝ (hermiteLp n) f = 0) → f = 0 :=
          fun f a => hermite_complete f a
        intro f hf;
        -- By definition of completeness, if a function is orthogonal to every element in the span of the Hermite functions, then it must be zero. Hence, we can apply `h_complete`.
        have h_orthogonal : ∀ f : Lp ℝ 2 (volume : Measure ℝ), f ∈ (Submodule.span ℝ (Set.range hermiteLp))ᗮ → f = 0 := by
          intro f hf;
          exact h_complete f fun n => hf _ <| Submodule.subset_span <| Set.mem_range_self n;
        convert Submodule.eq_top_iff'.mp ( show ( Submodule.span ℝ ( Set.range hermiteLp ) ).topologicalClosure = ⊤ from ?_ ) f using 1;
        rw [ Submodule.topologicalClosure_eq_top_iff ];
        exact eq_bot_iff.mpr h_orthogonal

/-- **The Hermite functions form a Hilbert basis of `L²(ℝ)`.** -/
def hermiteBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  HilbertBasis.mk hermiteLp_orthonormal hermiteLp_span_dense

@[simp] lemma hermiteBasis_apply (n : ℕ) : hermiteBasis n = hermiteLp n :=
  congrFun (HilbertBasis.coe_mk hermiteLp_orthonormal hermiteLp_span_dense) n

/-- The `n`-th Hermite coefficient of `f ∈ L²` is `⟨hₙ, f⟩`. -/
lemma hermiteBasis_repr_apply (f : Lp ℝ 2 (volume : Measure ℝ)) (n : ℕ) :
    hermiteBasis.repr f n = inner ℝ (hermiteLp n) f := by
  simpa [hermiteBasis_apply] using hermiteBasis.repr_apply_apply f n

/-- **Fourier–Hermite expansion:** `f = ∑ₙ ⟨hₙ, f⟩ hₙ` in `L²(ℝ)`. -/
lemma hermiteBasis_hasSum_repr (f : Lp ℝ 2 (volume : Measure ℝ)) :
    HasSum (fun n => hermiteBasis.repr f n • hermiteLp n) f := by
  simpa [hermiteBasis_apply] using hermiteBasis.hasSum_repr f

/-- **Parseval's identity** for the Hermite basis:
`∑ₙ ⟨hₙ, f⟩ · ⟨hₙ, g⟩ = ⟨f, g⟩`. -/
lemma hermiteBasis_hasSum_inner (f g : Lp ℝ 2 (volume : Measure ℝ)) :
    HasSum (fun n => inner ℝ f (hermiteLp n) * inner ℝ (hermiteLp n) g) (inner ℝ f g) := by
  simpa [hermiteBasis_apply] using hermiteBasis.hasSum_inner_mul_inner f g

/-! ## Bridge lemma for M3b : the coefficient functional -/

/-- The `n`-th Hermite coefficient `φ ↦ ∫ φ hₙ` as a continuous linear functional on `𝓢(ℝ,ℝ)`. -/
def hermiteCoeffCLM (n : ℕ) : 𝓢(ℝ, ℝ) →L[ℝ] ℝ :=
  (SchwartzMap.integralCLM ℝ (volume : Measure ℝ)).comp
    (SchwartzMap.smulLeftCLM ℝ (hermiteFun n))

lemma hermiteCoeffCLM_apply (n : ℕ) (phi : 𝓢(ℝ, ℝ)) :
    hermiteCoeffCLM n phi = ∫ x, hermiteFun n x * phi x := by
      -- By definition of `hermiteCoeffCLM`, we have
      simp [hermiteCoeffCLM];
      congr! 2;
      exact SchwartzMap.smulLeftCLM_apply_apply ( hermiteFun_hasTemperateGrowth n ) _ _

end TypeDDecouplingHermite