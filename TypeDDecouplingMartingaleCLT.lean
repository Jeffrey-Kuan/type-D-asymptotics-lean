import Mathlib

/-!
# A martingale central limit theorem (discrete core of Ethier–Kurtz Thm 7.1.4)

This file proves a **martingale central limit theorem** at the fixed-time,
finite-dimensional level (the full Skorokhod path-space statement is out of scope,
as Mathlib has no Skorokhod space).  It is the probabilistic core behind
`TypeDDecoupling.prop_twophase` in `TypeDDecouplingCrossover.lean`
(cross-reference only; that file's `sorry` is *not* touched here).

## Structure

* **Tier 1 — McLeish's martingale difference array CLT.**  The mathematical heart,
  `core_charFun_tendsto`, proves McLeish's product-trick conclusion
  `E[e^{i u Sₙ}] → e^{-σ² u²/2}` (convergence of characteristic functions) with *no*
  extra hypotheses beyond the martingale-difference structure.  Lévy's continuity
  theorem is **not** present in this Mathlib version, so the packaging into weak
  convergence (`mcleish_clt`) takes Lévy continuity as a single named hypothesis
  `hLevy`, exactly as sanctioned by the formalization brief.

* **Tier 2 — the bivariate version with diagonal brackets.**  Via Cramér–Wold
  through Tier 1: `joint_charFun_tendsto` proves that for every `(a,b)` the 2-D
  characteristic function of `(∑X, ∑Y)` converges to that of
  `N(0,σ_X²) ⊗ N(0,σ_Y²)`.  `thm_joint` packages this into joint weak convergence
  using a 2-D Lévy continuity hypothesis.

## Faithfulness / sanctioned simplifications (see brief's final remark)

The paper's arrays are the compensated `±1/√(2T)` jump martingales, so:
* condition (a) is used in its **deterministic** form `|X_{n,j}| ≤ bₙ → 0`
  (brief fallback (2)); this is sufficient for the paper and makes every product
  bounded, removing all integrability side-conditions;
* the bracket `∑_j X_{n,j}²` is not only convergent but **uniformly bounded**
  (`= ⌊2T⌋/(2T) ≤ 1` in the application) and converges **a.e.** (deterministically
  in the application), so bracket convergence is stated as a.e. convergence and the
  truncation/stopping device of the general theorem is unnecessary (brief remark (3),
  "generality is free").
-/

open MeasureTheory ProbabilityTheory Complex Filter Finset
open scoped Topology BigOperators ENNReal NNReal Real

namespace TypeDDecoupling.MartingaleCLT

/-- The elementary McLeish factor `1 + i u x`. -/
def cfac (u x : ℝ) : ℂ := 1 + ((u * x : ℝ) : ℂ) * Complex.I

section Analysis

/-- The real part of `1 + i u x` is `1`. -/
@[simp] lemma cfac_re (u x : ℝ) : (cfac u x).re = 1 := by simp [cfac]

/-- The imaginary part of `1 + i u x` is `u x`. -/
@[simp] lemma cfac_im (u x : ℝ) : (cfac u x).im = u * x := by simp [cfac]

/-- `1 + i u x` has real part `1`, hence is never zero. -/
lemma cfac_ne_zero (u x : ℝ) : cfac u x ≠ 0 := by
  intro h
  have : (cfac u x).re = 0 := by rw [h]; simp
  rw [cfac_re] at this; norm_num at this

/-- `‖1 + i u x‖² = 1 + (u x)²`. -/
lemma norm_cfac_sq (u x : ℝ) : ‖cfac u x‖ ^ 2 = 1 + (u * x) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, cfac_re, cfac_im]; ring

/-- The real part of `Complex.log (1 + i u x)`. -/
lemma log_cfac_re (u x : ℝ) :
    (Complex.log (cfac u x)).re = Real.log (1 + (u * x) ^ 2) / 2 := by
  rw [Complex.log_re]
  have hnn : (0:ℝ) ≤ 1 + (u*x)^2 := by positivity
  have hnorm : ‖cfac u x‖ = Real.sqrt (1 + (u*x)^2) := by
    rw [← norm_cfac_sq]; exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [hnorm, Real.log_sqrt hnn]

/-- `arg (1 + i y) = arctan y` (right half-plane). -/
lemma arg_one_add_mul_I (y : ℝ) :
    Complex.arg (1 + (y : ℂ) * Complex.I) = Real.arctan y := by
  set z : ℂ := 1 + (y:ℂ)*Complex.I with hz
  have hre : z.re = 1 := by simp [hz]
  have him : z.im = y := by simp [hz]
  have hlt : |Complex.arg z| < π/2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]; left; rw [hre]; norm_num
  have htan : Real.tan (Complex.arg z) = y := by rw [Complex.tan_arg, hre, him]; simp
  have h2 : Real.arctan (Real.tan (Complex.arg z)) = Complex.arg z :=
    Real.arctan_tan (abs_lt.mp hlt).1 (abs_lt.mp hlt).2
  rw [htan] at h2; exact h2.symm

/-- The imaginary part of `Complex.log (1 + i u x)` is `arctan (u x)`. -/
lemma log_cfac_im (u x : ℝ) :
    (Complex.log (cfac u x)).im = Real.arctan (u * x) := by
  rw [Complex.log_im]
  show Complex.arg (1 + ((u*x:ℝ):ℂ) * Complex.I) = Real.arctan (u*x)
  exact arg_one_add_mul_I (u*x)

/-
Elementary log bound: for `t ≥ 0`, `0 ≤ t - log (1 + t) ≤ t²/2`.
-/
lemma sub_log_one_add_le {t : ℝ} (ht : 0 ≤ t) :
    |Real.log (1 + t) - t| ≤ t ^ 2 / 2 := by
      refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
      · nlinarith [ Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 + t ) ];
      · -- We'll use the fact that $Real.log (1 + t) \geq t - t^2 / 2$ for $t \geq 0$.
        have h_log_bound : ∀ t : ℝ, 0 ≤ t → Real.log (1 + t) ≥ t - t^2 / 2 := by
          -- Let's choose any $t \geq 0$ and derive the inequality.
          intro t ht
          have h_deriv : ∀ t : ℝ, 0 ≤ t → deriv (fun t => Real.log (1 + t) - t + t^2 / 2) t ≥ 0 := by
            intro t ht; norm_num [ add_comm, show t + 1 ≠ 0 from by linarith ];
            nlinarith [ inv_mul_cancel₀ ( by linarith : ( t + 1 ) ≠ 0 ) ];
          by_contra h_contra;
          have := exists_deriv_eq_slope ( f := fun t => Real.log ( 1 + t ) - t + t ^ 2 / 2 ) ( show t > 0 from ht.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at *;
          exact absurd ( this ( by exact ContinuousOn.add ( ContinuousOn.sub ( ContinuousOn.log ( continuousOn_const.add continuousOn_id ) fun x hx => by linarith [ hx.1 ] ) continuousOn_id ) ( ContinuousOn.div_const ( continuousOn_pow 2 ) _ ) ) ( by exact fun x hx => DifferentiableAt.differentiableWithinAt ( by norm_num [ add_comm, show x + 1 ≠ 0 from by linarith [ hx.1 ] ] ) ) ) ( by rintro ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ ; nlinarith [ h_deriv c ( by linarith ), mul_div_cancel₀ ( Real.log ( 1 + t ) - t + t ^ 2 / 2 ) ( by linarith : t ≠ 0 ) ] );
        linarith [ h_log_bound t ht ]

/-
Elementary arctangent bound: `|arctan y - y| ≤ |y|³ / 3` for all `y`.
-/
lemma abs_arctan_sub_le (y : ℝ) : |Real.arctan y - y| ≤ |y| ^ 3 / 3 := by
  by_cases hy : 0 ≤ y;
  · by_cases hy' : y = 0 <;> simp_all +decide [ abs_of_nonneg ];
    rw [ abs_of_nonpos ];
    · -- Integrate both sides of the inequality $1 - \frac{1}{1+t^2} \leq t^2$ from $0$ to $y$.
      have h_integral : ∫ t in (0 : ℝ)..y, (1 - 1 / (1 + t ^ 2)) ≤ ∫ t in (0 : ℝ)..y, t ^ 2 := by
        refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
        · positivity;
        · exact fun x hx₁ hx₂ => by nlinarith [ inv_mul_cancel₀ ( by positivity : ( 1 + x ^ 2 ) ≠ 0 ) ] ;
      norm_num at h_integral; linarith;
    · simpa using Real.le_tan ( by positivity ) ( Real.arctan_lt_pi_div_two _ );
  · rw [ abs_le ];
    constructor <;> rw [ abs_of_neg ( not_le.mp hy ) ] <;> have := Real.le_tan ( Real.arctan_nonneg.mpr ( neg_nonneg.mpr ( le_of_not_ge hy ) ) ) ( Real.arctan_lt_pi_div_two _ ) <;> simp_all +decide [ Real.tan_arctan ];
    · nlinarith [ sq_nonneg y ];
    · -- Integrate both sides of the inequality $1 / (1 + t^2) \geq 1 - t^2$ from $y$ to $0$.
      have h_integral : ∫ t in y..0, (1 / (1 + t^2)) ≥ ∫ t in y..0, (1 - t^2) := by
        refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
        · linarith;
        · exact fun x hx₁ hx₂ => by nlinarith [ inv_mul_cancel₀ ( by nlinarith : ( 1 + x ^ 2 ) ≠ 0 ) ] ;
      norm_num at h_integral ; linarith

/-
Squeeze to `0`: if `|e n| ≤ g n` and `g → 0` then `e → 0`.
-/
lemma tendsto_zero_of_abs_le (e g : ℕ → ℝ) (hg : Tendsto g atTop (𝓝 0))
    (he : ∀ n, |e n| ≤ g n) :
    Tendsto e atTop (𝓝 0) := by
      exact squeeze_zero_norm' ( Filter.Eventually.of_forall he ) hg

/-
The real part sum of McLeish's correction converges: with jumps bounded by
`b n → 0` and the bracket `∑ Y²` uniformly `≤ C` and converging to `σ²`,
`∑_j ½·log(1 + (u Y_{n,j})²) → u²σ²/2`.
-/
lemma logSum_tendsto (u : ℝ) (kn : ℕ → ℕ) (Y : ℕ → ℕ → ℝ) (σsq C : ℝ) (b : ℕ → ℝ)
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n j, |Y n j| ≤ b n)
    (hCbr : ∀ n, ∑ j ∈ Finset.range (kn n), (Y n j) ^ 2 ≤ C)
    (hω : Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (Y n j) ^ 2) atTop (𝓝 σsq)) :
    Tendsto (fun n => ∑ j ∈ Finset.range (kn n), Real.log (1 + (u * Y n j) ^ 2) / 2) atTop
      (𝓝 (u ^ 2 * σsq / 2)) := by
        -- Let's simplify the goal using the fact that multiplication by a constant out of the limit results in the same limit.
        suffices h_simplified : Filter.Tendsto (fun n => (∑ j ∈ Finset.range (kn n), (u * Y n j)^2 / 2) + (∑ j ∈ Finset.range (kn n), (Real.log (1 + (u * Y n j)^2) - (u * Y n j)^2) / 2)) Filter.atTop (nhds (u^2 * σsq / 2)) by
          exact h_simplified.congr fun n => by rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_congr rfl fun _ _ => by ring;
        -- The first term converges to $u^2 \sigma^2 / 2$ by the properties of the sum of squares.
        have h_first_term : Filter.Tendsto (fun n => (∑ j ∈ Finset.range (kn n), (u * Y n j)^2 / 2)) Filter.atTop (nhds (u^2 * σsq / 2)) := by
          convert hω.const_mul ( u ^ 2 / 2 ) using 2 <;> norm_num [ Finset.mul_sum _ _ _, mul_pow ] ; ring;
          ring;
        -- The second term converges to 0 by the properties of the logarithm and the fact that $|Y_{n,j}| \leq b_n$.
        have h_second_term : Filter.Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (Real.log (1 + (u * Y n j)^2) - (u * Y n j)^2) / 2) Filter.atTop (nhds 0) := by
          -- By the properties of logarithms and the fact that $|Y_{n,j}| \leq b_n$, we have $|\log(1 + (u Y_{n,j})^2) - (u Y_{n,j})^2| \leq \frac{(u Y_{n,j})^4}{2}$.
          have h_log_bound : ∀ n j, |Real.log (1 + (u * Y n j)^2) - (u * Y n j)^2| ≤ (u * Y n j)^4 / 2 := by
            intro n j;
            convert sub_log_one_add_le ( show 0 ≤ ( u * Y n j ) ^ 2 by positivity ) using 1 ; ring;
          -- Using the bound $|\log(1 + (u Y_{n,j})^2) - (u Y_{n,j})^2| \leq \frac{(u Y_{n,j})^4}{2}$, we can show that the sum converges to 0.
          have h_sum_bound : ∀ n, |∑ j ∈ Finset.range (kn n), (Real.log (1 + (u * Y n j)^2) - (u * Y n j)^2) / 2| ≤ (u^4 / 4) * (b n)^2 * (∑ j ∈ Finset.range (kn n), Y n j^2) := by
            intros n
            have h_sum_bound : ∀ j ∈ Finset.range (kn n), |(Real.log (1 + (u * Y n j)^2) - (u * Y n j)^2) / 2| ≤ (u^4 / 4) * (b n)^2 * (Y n j)^2 := by
              intros j hj
              specialize h_log_bound n j
              have h_abs : |(Real.log (1 + (u * Y n j)^2) - (u * Y n j)^2) / 2| ≤ (u^4 / 4) * (Y n j)^4 := by
                exact abs_le.mpr ⟨ by linarith [ abs_le.mp h_log_bound ], by linarith [ abs_le.mp h_log_bound ] ⟩;
              exact h_abs.trans ( by rw [ mul_assoc ] ; exact mul_le_mul_of_nonneg_left ( by nlinarith only [ show Y n j ^ 2 ≤ b n ^ 2 by nlinarith only [ abs_le.mp ( hbound n j ) ] ] ) ( by positivity ) );
            exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum h_sum_bound ) ( by rw [ Finset.mul_sum _ _ _ ] ) );
          exact squeeze_zero_norm h_sum_bound ( by simpa using Filter.Tendsto.mul ( tendsto_const_nhds.mul ( hblim.pow 2 ) ) hω );
        simpa only [ add_zero ] using h_first_term.add h_second_term

/-
The imaginary part sum of McLeish's correction converges to `0`:
`∑_j (arctan (u Y_{n,j}) - u Y_{n,j}) → 0`.
-/
lemma arctanSum_tendsto (u : ℝ) (kn : ℕ → ℕ) (Y : ℕ → ℕ → ℝ) (C : ℝ) (b : ℕ → ℝ)
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n j, |Y n j| ≤ b n)
    (hCbr : ∀ n, ∑ j ∈ Finset.range (kn n), (Y n j) ^ 2 ≤ C) :
    Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (Real.arctan (u * Y n j) - u * Y n j)) atTop
      (𝓝 0) := by
        convert tendsto_zero_of_abs_le ( fun n ↦ ∑ j ∈ Finset.range ( kn n ), ( Real.arctan ( u * Y n j ) - u * Y n j ) ) ( fun n ↦ ( |u|^3 * C ) * b n / 3 ) _ _ using 1;
        · simpa using Filter.Tendsto.div_const ( tendsto_const_nhds.mul hblim ) 3;
        · intro n
          have h_sum_bound : ∑ j ∈ Finset.range (kn n), |Real.arctan (u * Y n j) - u * Y n j| ≤ (|u|^3 * C) * b n / 3 := by
            refine' le_trans ( Finset.sum_le_sum fun i hi => show |Real.arctan ( u * Y n i ) - u * Y n i| ≤ |u| ^ 3 * |Y n i| ^ 3 / 3 from _ ) _;
            · convert abs_arctan_sub_le ( u * Y n i ) using 1 ; norm_num [ abs_mul ] ; ring;
            · refine' le_trans ( Finset.sum_le_sum fun i hi => show |u| ^ 3 * |Y n i| ^ 3 / 3 ≤ |u| ^ 3 * ( Y n i ^ 2 ) * b n / 3 from _ ) _;
              · rw [ show |Y n i| ^ 3 = |Y n i| * |Y n i| ^ 2 by ring, sq_abs ];
                nlinarith only [ show 0 ≤ |u| ^ 3 * Y n i ^ 2 by positivity, show |Y n i| ≤ b n by exact hbound n i ];
              · convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( hCbr n ) ( pow_nonneg ( abs_nonneg u ) 3 ) ) ( hb0 n ) |> ( fun x => div_le_div_of_nonneg_right x zero_le_three ) using 1 ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_div ];
          exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) h_sum_bound

end Analysis

section CondExp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-
Pull-out to zero for the martingale-difference property: if `g` is `m`-strongly
measurable and `X` has vanishing conditional expectation given `m`, then
`∫ g·X = 0`.
-/
lemma integral_mul_of_condExp_zero {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {g X : Ω → ℝ} (hg : StronglyMeasurable[m] g)
    (hgb : ∃ B, ∀ ω, |g ω| ≤ B) (hXb : ∃ B, ∀ ω, |X ω| ≤ B)
    (hX : Integrable X μ) (hcond : μ[X | m] =ᵐ[μ] 0) :
    ∫ ω, g ω * X ω ∂μ = 0 := by
      by_cases h_integrable : MeasureTheory.Integrable (fun ω => g ω * X ω) μ;
      · have h_cond_exp : μ[(fun ω => g ω * X ω) | m] =ᵐ[μ] fun ω => g ω * (μ[X | m]) ω := by
          apply_rules [ MeasureTheory.condExp_mul_of_stronglyMeasurable_left ];
        rw [ ← MeasureTheory.integral_condExp hm ];
        rw [ MeasureTheory.integral_congr_ae h_cond_exp, MeasureTheory.integral_eq_zero_of_ae ] ; filter_upwards [ hcond ] with ω hω ; aesop;
      · rw [ MeasureTheory.integral_undef h_integrable ]

/-
Complex version of the pull-out to zero: if `P` is `m`-strongly measurable and
bounded, and `X` (real) has vanishing conditional expectation given `m`, then
`∫ P·X = 0`.
-/
lemma integral_cmul_of_condExp_zero {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {P : Ω → ℂ} {X : Ω → ℝ} (hP : StronglyMeasurable[m] P)
    (hPb : ∃ B, ∀ ω, ‖P ω‖ ≤ B) (hXb : ∃ B, ∀ ω, |X ω| ≤ B)
    (hX : Integrable X μ) (hcond : μ[X | m] =ᵐ[μ] 0) :
    ∫ ω, P ω * (X ω : ℂ) ∂μ = 0 := by
      convert Complex.ext_iff.mpr ?_;
      have : Integrable (fun ω => P ω * (X ω : ℂ)) μ := by
        refine' MeasureTheory.Integrable.mono' ( hX.norm.const_mul ( hPb.choose : ℝ ) ) _ _;
        · refine' MeasureTheory.AEStronglyMeasurable.mul _ _;
          · exact hP.aestronglyMeasurable.mono hm;
          · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hX.1;
        · filter_upwards [ ] with ω using by simpa using mul_le_mul_of_nonneg_right ( hPb.choose_spec ω ) ( norm_nonneg ( X ω ) ) ;
      -- Apply the pull-out to zero lemma to the real and imaginary parts separately.
      have h_real : ∫ ω, (P ω).re * X ω ∂μ = 0 := by
        apply integral_mul_of_condExp_zero hm;
        · exact Complex.continuous_re.comp_stronglyMeasurable hP;
        · exact ⟨ hPb.choose, fun ω => le_trans ( Complex.abs_re_le_norm _ ) ( hPb.choose_spec ω ) ⟩;
        · exact hXb;
        · exact hX;
        · exact hcond
      have h_imag : ∫ ω, (P ω).im * X ω ∂μ = 0 := by
        apply_rules [ integral_mul_of_condExp_zero ];
        · exact Complex.measurable_im.comp hP.measurable |> fun h => h.stronglyMeasurable;
        · exact ⟨ hPb.choose, fun ω => le_trans ( Complex.abs_im_le_norm _ ) ( hPb.choose_spec ω ) ⟩;
      convert And.intro h_real h_imag using 1;
      · convert Complex.reCLM.integral_comp_comm _;
        any_goals exact this;
        all_goals norm_cast;
        simp +decide [ Complex.ext_iff ];
        grind;
      · convert Complex.imCLM.integral_comp_comm _;
        any_goals exact this;
        simp +decide [ Complex.ext_iff ];
        grind

/-
A bounded a.e.-strongly-measurable `ℂ`-valued function is integrable on the
(finite) probability measure `μ`.
-/
lemma integrable_of_norm_bound {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ) {B : ℝ}
    (hb : ∀ ω, ‖f ω‖ ≤ B) : Integrable f μ := by
      refine' MeasureTheory.Integrable.mono' _ _ _;
      exacts [ fun _ => B, MeasureTheory.integrable_const _, hf, Filter.Eventually.of_forall hb ]

/-- A bounded a.e.-strongly-measurable real function is integrable on the (finite)
probability measure `μ`. -/
lemma integrable_real_of_bound {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f μ := by
  refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const B) hf
    (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hb ω))

/-
The partial product `∏_{j<N} (1 + i u X_j)` is `𝓕 N`-strongly measurable.
-/
lemma cprod_stronglyMeasurable (𝓕 : ℕ → MeasurableSpace Ω) (hmono : Monotone 𝓕)
    (X : ℕ → Ω → ℝ) (u : ℝ) (hadapt : ∀ j, StronglyMeasurable[𝓕 (j + 1)] (X j)) (N : ℕ) :
    StronglyMeasurable[𝓕 N] (fun ω => ∏ j ∈ Finset.range N, cfac u (X j ω)) := by
      induction' N with N ih;
      · exact MeasureTheory.stronglyMeasurable_const;
      · simp +decide only [range_add_one];
        by_cases hN : N ∈ Finset.range N <;> simp_all +decide [ Finset.prod_insert, cfac ];
        apply_rules [ StronglyMeasurable.mul, StronglyMeasurable.add, StronglyMeasurable.mul, stronglyMeasurable_const ];
        · exact Complex.continuous_ofReal.comp_stronglyMeasurable ( hadapt N );
        · exact ih.mono ( hmono ( Nat.le_succ _ ) )

/-
Uniform modulus bound for the partial product.
-/
lemma cprod_norm_le (X : ℕ → Ω → ℝ) (u b : ℝ) (hbound : ∀ j ω, |X j ω| ≤ b)
    (N : ℕ) (ω : Ω) :
    ‖∏ j ∈ Finset.range N, cfac u (X j ω)‖ ≤ (Real.sqrt (1 + (u * b) ^ 2)) ^ N := by
      convert Finset.prod_le_prod ?_ fun i ( hi : i ∈ Finset.range N ) => ( show ‖cfac u ( X i ω )‖ ≤ Real.sqrt ( 1 + ( u * b ) ^ 2 ) from ?_ ) using 1 <;> norm_num [ Real.sqrt_nonneg ];
      refine' Real.sqrt_le_sqrt _;
      unfold cfac; norm_num [ Complex.normSq ] ; nlinarith [ mul_le_mul_of_nonneg_left ( show X i ω ^ 2 ≤ b ^ 2 by nlinarith [ abs_le.mp ( hbound i ω ) ] ) ( sq_nonneg u ) ] ;

/-
**Product martingale identity** (McLeish product trick, step (1)):
`E[∏_{j<N} (1 + i u X_j)] = 1`, for a martingale difference sequence adapted to a
filtration `𝓕`, with deterministically bounded increments.
-/
lemma integral_prod_cfac_eq_one
    (𝓕 : ℕ → MeasurableSpace Ω) (hmono : Monotone 𝓕) (hle : ∀ k, 𝓕 k ≤ mΩ)
    (X : ℕ → Ω → ℝ) (u : ℝ) (b : ℝ)
    (hadapt : ∀ j, StronglyMeasurable[𝓕 (j + 1)] (X j))
    (hbound : ∀ j ω, |X j ω| ≤ b)
    (hmds : ∀ j, μ[X j | 𝓕 j] =ᵐ[μ] 0) (N : ℕ) :
    ∫ ω, ∏ j ∈ Finset.range N, cfac u (X j ω) ∂μ = 1 := by
      induction' N with N ih;
      · simp +decide;
      · -- Now consider the integral of the product up to $N+1$.
        have h_split : ∫ ω, ∏ j ∈ Finset.range (N + 1), cfac u (X j ω) ∂μ = (∫ ω, (∏ j ∈ Finset.range N, cfac u (X j ω)) ∂μ) + (∫ ω, (∏ j ∈ Finset.range N, cfac u (X j ω)) * ((u * X N ω : ℝ) * Complex.I) ∂μ) := by
          rw [ ← MeasureTheory.integral_add ] ; congr ; ext ω ; simp +decide [ Finset.prod_range_succ, cfac ] ; ring;
          · exact ( by contrapose! ih; rw [ MeasureTheory.integral_undef ih ] ; norm_num );
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun ω => ( Real.sqrt ( 1 + ( u * b ) ^ 2 ) ) ^ N * ( |u| * b );
            · exact MeasureTheory.integrable_const _;
            · refine' MeasureTheory.AEStronglyMeasurable.mul _ _;
              · exact MeasureTheory.Integrable.aestronglyMeasurable ( by exact ( by contrapose! ih; rw [ MeasureTheory.integral_undef ih ] ; norm_num ) );
              · exact MeasureTheory.AEStronglyMeasurable.mul ( Complex.continuous_ofReal.comp_aestronglyMeasurable ( MeasureTheory.AEStronglyMeasurable.const_mul ( hadapt N |> StronglyMeasurable.aestronglyMeasurable |> fun h => h.mono ( hle _ ) ) _ ) ) ( MeasureTheory.aestronglyMeasurable_const );
            · simp +decide [ cfac ];
              refine' Filter.Eventually.of_forall fun ω => mul_le_mul _ _ _ _;
              · convert cprod_norm_le X u b hbound N ω using 1;
                simp +decide [ cfac, Complex.norm_def, Complex.normSq ];
              · exact mul_le_mul_of_nonneg_left ( hbound N ω ) ( abs_nonneg u );
              · positivity;
              · positivity;
        -- By the properties of the integral, we can pull the constant factor out of the integral.
        have h_pull : ∫ ω, (∏ j ∈ Finset.range N, cfac u (X j ω)) * ((u * X N ω : ℝ) * Complex.I) ∂μ = (u * Complex.I) * ∫ ω, (∏ j ∈ Finset.range N, cfac u (X j ω)) * (X N ω : ℝ) ∂μ := by
          rw [ ← MeasureTheory.integral_const_mul ] ; congr ; ext ; ring;
          norm_num ; ring;
        have := integral_cmul_of_condExp_zero ( hle N ) ( cprod_stronglyMeasurable 𝓕 hmono X u hadapt N ) ⟨ ( Real.sqrt ( 1 + ( u * b ) ^ 2 ) ) ^ N, fun ω => cprod_norm_le X u b hbound N ω ⟩ ⟨ b, fun ω => hbound N ω ⟩ ( show Integrable ( X N ) μ from ?_ ) ( hmds N ) ; aesop;
        refine' MeasureTheory.Integrable.mono' ( MeasureTheory.integrable_const b ) _ _;
        · exact hadapt N |> StronglyMeasurable.aestronglyMeasurable |> fun h => h.mono ( hle _ );
        · exact Filter.Eventually.of_forall fun ω => hbound N ω

end CondExp

section Core

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The McLeish "difference" product `Dₙ = ∏_j (1 + i u X_j) e^{-i u X_j}`, whose
limit `e^{u²σ²/2}` supplies the Gaussian factor. -/
noncomputable def Dfun (u : ℝ) (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℂ :=
  ∏ j ∈ Finset.range N,
    cfac u (X j ω) * Complex.exp (-(((u * X j ω : ℝ) : ℂ)) * Complex.I)

/-- The partial sum `Sₙ = ∑_{j<N} X_j`. -/
def partialSum (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ := ∑ j ∈ Finset.range N, X j ω

/-
Factorisation `∏_j (1 + i u X_j) = Dₙ · e^{i u Sₙ}`.
-/
lemma prod_cfac_eq (u : ℝ) (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    ∏ j ∈ Finset.range N, cfac u (X j ω)
      = Dfun u X N ω * Complex.exp (((u * partialSum X N ω : ℝ) : ℂ) * Complex.I) := by
        unfold Dfun;
        simp +decide [ Finset.prod_mul_distrib, Complex.exp_sum, Complex.exp_neg, partialSum ];
        simp +decide [ mul_assoc, ← Complex.exp_sum, Finset.mul_sum _ _ _, Finset.sum_mul ]

/-
Uniform modulus bound `‖Dₙ‖ ≤ e^{u²C/2}` whenever the bracket is `≤ C`.
-/
lemma norm_Dfun_le (u : ℝ) (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) (C : ℝ)
    (hbr : ∑ j ∈ Finset.range N, (X j ω) ^ 2 ≤ C) :
    ‖Dfun u X N ω‖ ≤ Real.exp (u ^ 2 * C / 2) := by
      -- Apply the bound on the norm of each term in the product.
      have h_term_bound : ∀ j ∈ Finset.range N, ‖cfac u (X j ω)‖ ≤ Real.exp ((u * X j ω) ^ 2 / 2) := by
        intro j hj
        have h_term : ‖cfac u (X j ω)‖^2 ≤ 1 + (u * X j ω) ^ 2 := by
          rw [ norm_cfac_sq ];
        nlinarith [ Real.add_one_le_exp ( ( u * X j ω ) ^ 2 / 2 ) ];
      refine' le_trans _ ( Real.exp_le_exp.mpr _ );
      convert Finset.prod_le_prod ?_ h_term_bound;
      any_goals exact ∑ j ∈ Finset.range N, ( u * X j ω ) ^ 2 / 2;
      · unfold Dfun; simp +decide [ Complex.norm_exp ] ;
      · rw [ ← Real.exp_sum ];
      · exact fun _ _ => norm_nonneg _;
      · convert mul_le_mul_of_nonneg_left hbr ( show 0 ≤ u ^ 2 / 2 by positivity ) using 1 ; ring;
        · simp +decide only [mul_assoc, Finset.mul_sum _ _ _, sum_mul];
        · ring

/-
`Dₙ` written as a single exponential of its (real) log-modulus plus `i` times its
(real) argument: `Dₙ = exp(∑ ½ log(1+(uX_j)²) + i ∑ (arctan(uX_j) - uX_j))`.
-/
lemma Dfun_eq_exp (u : ℝ) (Y : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    Dfun u Y N ω = Complex.exp
      ((∑ j ∈ Finset.range N, Real.log (1 + (u * Y j ω) ^ 2) / 2 : ℝ)
       + ((∑ j ∈ Finset.range N, (Real.arctan (u * Y j ω) - u * Y j ω) : ℝ) : ℂ) * Complex.I) := by
  have h_step1 : Dfun u Y N ω = Complex.exp (∑ j ∈ Finset.range N, (Complex.log (cfac u (Y j ω)) - ((u * Y j ω : ℝ) : ℂ) * Complex.I)) := by
    -- Apply the exponential property to each term in the product.
    have h_exp : ∀ j, cfac u (Y j ω) * Complex.exp (-(((u * Y j ω : ℝ) : ℂ)) * Complex.I) = Complex.exp (Complex.log (cfac u (Y j ω)) - ((u * Y j ω : ℝ) : ℂ) * Complex.I) := by
      intro j; rw [ sub_eq_add_neg, Complex.exp_add, Complex.exp_log ( cfac_ne_zero _ _ ) ] ; ring;
    convert Finset.prod_congr rfl fun j _ => h_exp j using 1;
    rw [ ← Complex.exp_sum ];
  -- Step 2: Split the sum into real and imaginary parts.
  have h_step2 : ∑ j ∈ Finset.range N, (Complex.log (cfac u (Y j ω)) - ((u * Y j ω : ℝ) : ℂ) * Complex.I) =
    (∑ j ∈ Finset.range N, (Real.log (1 + (u * Y j ω) ^ 2) / 2 : ℝ)) +
    (∑ j ∈ Finset.range N, (Real.arctan (u * Y j ω) - u * Y j ω) : ℝ) * Complex.I := by
      simp +decide [ Complex.ext_iff, log_cfac_re, log_cfac_im ];
      norm_cast ; norm_num;
  rw [ h_step1, h_step2 ]

/-
Pointwise a.e. limit `Dₙ(ω) → e^{u²σ²/2}` when the bracket converges to `σ²` and
the jumps vanish uniformly.
-/
lemma Dfun_tendsto (u : ℝ) (kn : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ) (σsq : ℝ) (b : ℕ → ℝ) (C : ℝ)
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n j ω, |X n j ω| ≤ b n)
    (hCbr : ∀ n ω, ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2 ≤ C)
    (ω : Ω)
    (hω : Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2) atTop (𝓝 σsq)) :
    Tendsto (fun n => Dfun u (X n) (kn n) ω) atTop
      (𝓝 (Complex.exp (((u ^ 2 * σsq / 2 : ℝ) : ℂ)))) := by
        -- Let's rewrite the expression inside the exponential using the results from `logSum_tendsto` and `arctanSum_tendsto`.
        have h_exp : Filter.Tendsto (fun n => (∑ j ∈ Finset.range (kn n), Real.log (1 + (u * X n j ω) ^ 2) / 2) + (∑ j ∈ Finset.range (kn n), (Real.arctan (u * X n j ω) - u * X n j ω)) * Complex.I) Filter.atTop (nhds ((u ^ 2 * σsq / 2) + 0 * Complex.I)) := by
          refine' Filter.Tendsto.add _ _;
          · convert Complex.continuous_ofReal.continuousAt.tendsto.comp ( logSum_tendsto u kn ( fun n j => X n j ω ) σsq C b hb0 hblim ( fun n j => hbound n j ω ) ( fun n => hCbr n ω ) hω ) using 2 ; norm_num;
          · refine' Filter.Tendsto.mul _ tendsto_const_nhds;
            convert Complex.continuous_ofReal.continuousAt.tendsto.comp ( arctanSum_tendsto u kn ( fun n j => X n j ω ) C b hb0 hblim ( fun n j => hbound n j ω ) ( fun n => hCbr n ω ) ) using 2;
        convert Complex.continuous_exp.continuousAt.tendsto.comp h_exp using 2 ; norm_num [ Dfun_eq_exp ];
        norm_num

/-
`Dₙ` is measurable in `ω`.
-/
lemma Dfun_measurable (u : ℝ) (X : ℕ → Ω → ℝ) (N : ℕ)
    (hX : ∀ j, Measurable (X j)) : Measurable (fun ω => Dfun u X N ω) := by
      refine' Finset.measurable_prod _ fun j _ => _;
      exact Measurable.mul ( by exact Measurable.add measurable_const ( by exact Measurable.mul ( Complex.measurable_ofReal.comp ( measurable_const.mul ( hX j ) ) ) measurable_const ) ) ( Complex.continuous_exp.measurable.comp ( by exact Measurable.mul ( by exact Measurable.neg ( by exact Complex.measurable_ofReal.comp ( measurable_const.mul ( hX j ) ) ) ) measurable_const ) )

/-
**Dominated convergence for the difference product.**  `∫ ‖e^{u²σ²/2} - Dₙ‖ → 0`.
-/
lemma integral_norm_Dfun_sub_tendsto
    (u : ℝ) (kn : ℕ → ℕ) (𝓕 : ℕ → ℕ → MeasurableSpace Ω) (X : ℕ → ℕ → Ω → ℝ)
    (σsq : ℝ) (b : ℕ → ℝ) (C : ℝ)
    (hle : ∀ n k, 𝓕 n k ≤ mΩ)
    (hadapt : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (X n j))
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n j ω, |X n j ω| ≤ b n)
    (hCbr : ∀ n ω, ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2 ≤ C)
    (hbracket : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2) atTop (𝓝 σsq)) :
    Tendsto (fun n => ∫ ω, ‖Complex.exp (((u ^ 2 * σsq / 2 : ℝ) : ℂ)) - Dfun u (X n) (kn n) ω‖ ∂μ)
      atTop (𝓝 0) := by
        -- Apply the dominated convergence theorem.
        have h_dominated : ∀ᵐ ω ∂μ, Tendsto (fun n => ‖cexp (u ^ 2 * σsq / 2) - Dfun u (X n) (kn n) ω‖) atTop (𝓝 0) := by
          filter_upwards [ hbracket ] with ω hω;
          convert Filter.Tendsto.norm ( tendsto_const_nhds.sub ( Dfun_tendsto u kn X σsq b C hb0 hblim hbound hCbr ω hω ) ) using 2 ; norm_num;
        convert MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ h_dominated;
        all_goals norm_num;
        refine' fun ω => ‖cexp ( u ^ 2 * σsq / 2 )‖ + Real.exp ( u ^ 2 * C / 2 );
        · intro n
          have h_measurable : Measurable (fun ω => Dfun u (X n) (kn n) ω) := by
            apply Dfun_measurable u (X n) (kn n) (fun j => ((hadapt n j).mono (hle n (j+1))).measurable)
          exact (by
          exact Measurable.aestronglyMeasurable ( by measurability ));
        · norm_num;
        · intro n; filter_upwards [ ] with ω; refine' le_trans ( norm_sub_le _ _ ) _ ; norm_num [ Complex.norm_exp ];
          exact norm_Dfun_le u ( X n ) ( kn n ) ω C ( hCbr n ω )

/-
**McLeish's martingale CLT — characteristic-function core.**
`E[e^{i u Sₙ}] → e^{-σ² u²/2}` for every `u`.  This is the entire probabilistic
content; Lévy's continuity theorem (below) merely repackages it as weak convergence.
-/
theorem core_charFun_tendsto
    (kn : ℕ → ℕ) (𝓕 : ℕ → ℕ → MeasurableSpace Ω)
    (X : ℕ → ℕ → Ω → ℝ) (σsq : ℝ) (b : ℕ → ℝ) (C : ℝ)
    (hmono : ∀ n, Monotone (𝓕 n)) (hle : ∀ n k, 𝓕 n k ≤ mΩ)
    (hadapt : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (X n j))
    (hmds : ∀ n j, μ[X n j | 𝓕 n j] =ᵐ[μ] 0)
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n j ω, |X n j ω| ≤ b n)
    (hCbr : ∀ n ω, ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2 ≤ C)
    (hbracket : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2) atTop (𝓝 σsq)) :
    ∀ u : ℝ, Tendsto
      (fun n => ∫ ω, Complex.exp (((u * partialSum (X n) (kn n) ω : ℝ) : ℂ) * Complex.I) ∂μ)
      atTop (𝓝 (Complex.exp (((-σsq * u ^ 2 / 2 : ℝ) : ℂ)))) := by
        intro u
        set c := Complex.exp ((u ^ 2 * σsq / 2 : ℝ) : ℂ)
        set T := Complex.exp ((-σsq * u ^ 2 / 2 : ℝ) : ℂ)
        have hTc : T * c = 1 := by
          rw [ ← Complex.exp_add ] ; ring ; norm_num;
        have hTnorm : ‖T‖ = Real.exp (-σsq * u ^ 2 / 2) := by
          simp [T, Complex.norm_exp];
          exact Or.inl <| by norm_cast;
        have h_integrable : ∀ n, Integrable (fun ω => (cexp ((u * partialSum (X n) (kn n) ω : ℝ) * Complex.I))) μ := by
          intro n
          have h_measurable : Measurable (fun ω => partialSum (X n) (kn n) ω) := by
            exact Finset.measurable_sum _ fun j _ => ( hadapt n j |> StronglyMeasurable.measurable |> Measurable.comp <| hle n ( j + 1 ) );
          refine' MeasureTheory.Integrable.mono' ( MeasureTheory.integrable_const 1 ) _ _;
          · fun_prop;
          · simp +decide [ Complex.norm_exp ];
        have h_integrable_P : ∀ n, Integrable (fun ω => (∏ j ∈ (Finset.range (kn n)), (1 + (u * (X n j ω : ℝ)) * Complex.I))) μ := by
          intro n
          have h_integrable_P : ∀ ω, ‖(∏ j ∈ (Finset.range (kn n)), (1 + (u * (X n j ω : ℝ)) * Complex.I))‖ ≤ (Real.sqrt (1 + (u * b n) ^ 2)) ^ (kn n) := by
            intro ω; convert cprod_norm_le ( X n ) u ( b n ) ( fun j ω => hbound n j ω ) ( kn n ) ω using 1; simp +decide [ cfac ] ;
          refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun ω => Real.sqrt ( 1 + ( u * b n ) ^ 2 ) ^ kn n;
          · exact MeasureTheory.integrable_const _;
          · refine' Measurable.aestronglyMeasurable _;
            refine' Finset.measurable_prod _ fun j _ => _;
            exact Measurable.add measurable_const ( Measurable.mul ( Measurable.mul measurable_const ( Complex.measurable_ofReal.comp ( hadapt n j |> StronglyMeasurable.measurable |> Measurable.comp <| by tauto ) ) ) measurable_const );
          · exact Filter.Eventually.of_forall h_integrable_P;
        have h_integral : ∀ n, ∫ ω, (∏ j ∈ (Finset.range (kn n)), (1 + (u * (X n j ω : ℝ)) * Complex.I)) ∂μ = 1 := by
          intro n;
          convert integral_prod_cfac_eq_one ( 𝓕 n ) ( hmono n ) ( fun k => hle n k ) ( X n ) u ( b n ) ( hadapt n ) ( hbound n ) ( hmds n ) ( kn n ) using 1;
          unfold cfac; norm_num;
        have h_integral_sub : ∀ n, ∫ ω, (cexp ((u * partialSum (X n) (kn n) ω : ℝ) * Complex.I)) - T * (∏ j ∈ (Finset.range (kn n)), (1 + (u * (X n j ω : ℝ)) * Complex.I)) ∂μ = ∫ ω, (cexp ((u * partialSum (X n) (kn n) ω : ℝ) * Complex.I)) * T * (c - Dfun u (X n) (kn n) ω) ∂μ := by
          intro n
          congr
          funext ω
          simp [Dfun];
          simp +decide [ mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, Finset.prod_mul_distrib, cfac ];
          simp +decide [ ← mul_assoc, ← Complex.exp_sum, ← Finset.sum_mul, hTc ];
          simp +decide [ mul_assoc, ← Complex.exp_add, partialSum ];
          simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        have h_integral_sub : ∀ n, ‖∫ ω, (cexp ((u * partialSum (X n) (kn n) ω : ℝ) * Complex.I)) * T * (c - Dfun u (X n) (kn n) ω) ∂μ‖ ≤ ‖T‖ * ∫ ω, ‖c - Dfun u (X n) (kn n) ω‖ ∂μ := by
          intro n
          have h_integral_sub : ‖∫ ω, (cexp ((u * partialSum (X n) (kn n) ω : ℝ) * Complex.I)) * T * (c - Dfun u (X n) (kn n) ω) ∂μ‖ ≤ ∫ ω, ‖(cexp ((u * partialSum (X n) (kn n) ω : ℝ) * Complex.I)) * T * (c - Dfun u (X n) (kn n) ω)‖ ∂μ := by
            exact MeasureTheory.norm_integral_le_integral_norm _;
          simp_all +decide [ Complex.norm_exp, mul_assoc, MeasureTheory.integral_const_mul ];
        have h_integral_sub : Filter.Tendsto (fun n => ‖T‖ * ∫ ω, ‖c - Dfun u (X n) (kn n) ω‖ ∂μ) Filter.atTop (nhds 0) := by
          convert tendsto_const_nhds.mul ( integral_norm_Dfun_sub_tendsto u kn 𝓕 X σsq b C hle hadapt hb0 hblim hbound hCbr hbracket ) using 2 ; norm_num;
        have h_integral_sub : Filter.Tendsto (fun n => ∫ ω, (cexp ((u * partialSum (X n) (kn n) ω : ℝ) * Complex.I)) - T * (∏ j ∈ (Finset.range (kn n)), (1 + (u * (X n j ω : ℝ)) * Complex.I)) ∂μ) Filter.atTop (nhds 0) := by
          exact squeeze_zero_norm ( fun n => by aesop ) h_integral_sub;
        convert h_integral_sub.add_const T using 2 <;> norm_num [ h_integral ];
        rw [ MeasureTheory.integral_sub ];
        · rw [ MeasureTheory.integral_const_mul, h_integral ] ; ring;
        · aesop;
        · exact MeasureTheory.Integrable.const_mul ( h_integrable_P _ ) _

end Core

section Wrappers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `charFun (μ.map S) t = ∫ e^{i t S}`. -/
lemma charFun_map_real (S : Ω → ℝ) (hS : Measurable S) (t : ℝ) :
    charFun (μ.map S) t = ∫ ω, Complex.exp (((t * S ω : ℝ) : ℂ) * Complex.I) ∂μ := by
  rw [charFun_apply_real,
    MeasureTheory.integral_map hS.aemeasurable
      (Continuous.aestronglyMeasurable (by continuity))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  push_cast; ring_nf

/-- **Lévy's continuity theorem** (named hypothesis; not present in this Mathlib
version, sanctioned by the brief).  Pointwise convergence of characteristic functions
of probability measures on `ℝ` to that of a probability measure implies weak
convergence. -/
def LevyContinuityℝ : Prop :=
  ∀ (ξ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ),
    (∀ t, Tendsto (fun n => charFun (ξ n : Measure ℝ) t) atTop (𝓝 (charFun (ν : Measure ℝ) t))) →
      Tendsto ξ atTop (𝓝 ν)

/-
**Tier 1 — McLeish's martingale difference array CLT (weak convergence form).**
Under the martingale-difference hypotheses (with deterministic jump bound and
uniformly bounded, a.e.-convergent bracket), the law of `Sₙ = ∑_j X_{n,j}` converges
weakly to the centred Gaussian `N(0, σ²)`.  The single named hypothesis `hLevy` is
Lévy's continuity theorem, absent from this Mathlib version.
-/
theorem mcleish_clt (hLevy : LevyContinuityℝ)
    (kn : ℕ → ℕ) (𝓕 : ℕ → ℕ → MeasurableSpace Ω)
    (X : ℕ → ℕ → Ω → ℝ) (v : ℝ≥0) (b : ℕ → ℝ) (C : ℝ)
    (hmono : ∀ n, Monotone (𝓕 n)) (hle : ∀ n k, 𝓕 n k ≤ mΩ)
    (hadapt : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (X n j))
    (hmeas : ∀ n, Measurable (partialSum (X n) (kn n)))
    (hmds : ∀ n j, μ[X n j | 𝓕 n j] =ᵐ[μ] 0)
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n j ω, |X n j ω| ≤ b n)
    (hCbr : ∀ n ω, ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2 ≤ C)
    (hbracket : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2) atTop (𝓝 (v : ℝ))) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n => ⟨μ.map (partialSum (X n) (kn n)),
          Measure.isProbabilityMeasure_map (hmeas n).aemeasurable⟩)
      atTop (𝓝 ⟨gaussianReal 0 v, inferInstance⟩) := by
        convert hLevy _ _ _;
        convert core_charFun_tendsto kn 𝓕 X v b C hmono hle ( fun n j => ?_ ) hmds hb0 hblim hbound hCbr hbracket using 1;
        · simp +decide [ charFun_map_real _ ( hmeas _ ), charFun_gaussianReal ];
          ring;
        · exact hadapt n j

end Wrappers

section Bivariate

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-
Linearity of the martingale-difference property: if `f, g` are integrable with
vanishing conditional expectation given `m`, so is `a·f + c·g`.
-/
omit [IsProbabilityMeasure μ] in
lemma condExp_linear_comb_eq_zero {m : MeasurableSpace Ω} (a c : ℝ)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : μ[f | m] =ᵐ[μ] 0) (hg0 : μ[g | m] =ᵐ[μ] 0) :
    μ[fun ω => a * f ω + c * g ω | m] =ᵐ[μ] 0 := by
      have h_condExp_smul : μ[a • f | m] =ᵐ[μ] a • μ[f | m] := by
        convert MeasureTheory.condExp_smul a f m using 1
      have h_condExp_smul' : μ[c • g | m] =ᵐ[μ] c • μ[g | m] := by
        convert MeasureTheory.condExp_smul c g m using 1;
      have h_condExp_add : μ[a • f + c • g | m] =ᵐ[μ] μ[a • f | m] + μ[c • g | m] := by
        apply_rules [ MeasureTheory.condExp_add ];
        · exact hf.const_mul a;
        · exact hg.const_mul c;
      filter_upwards [ h_condExp_add, h_condExp_smul, h_condExp_smul', hf0, hg0 ] with ω hω₁ hω₂ hω₃ hω₄ hω₅ using by aesop;

/-
**Tier 2 — joint CLT with diagonal brackets, characteristic-function core.**
For martingale difference arrays `X, Y` with a common filtration, each with vanishing
jumps, and diagonal brackets `∑X² → σ_X²`, `∑Y² → σ_Y²`, cross bracket `∑ XY → 0`,
the 2-D characteristic function of `(∑X, ∑Y)` converges to that of the independent
Gaussian pair `N(0,σ_X²) ⊗ N(0,σ_Y²)`.  Proved by Cramér–Wold: the linear combination
`aX + bY` is again a martingale difference array with bracket `a²σ_X² + b²σ_Y²`, to
which `core_charFun_tendsto` applies.
-/
theorem joint_charFun_tendsto
    (kn : ℕ → ℕ) (𝓕 : ℕ → ℕ → MeasurableSpace Ω)
    (X Y : ℕ → ℕ → Ω → ℝ) (sX sY : ℝ) (b : ℕ → ℝ) (C : ℝ)
    (hmono : ∀ n, Monotone (𝓕 n)) (hle : ∀ n k, 𝓕 n k ≤ mΩ)
    (hadaptX : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (X n j))
    (hadaptY : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (Y n j))
    (hmdsX : ∀ n j, μ[X n j | 𝓕 n j] =ᵐ[μ] 0)
    (hmdsY : ∀ n j, μ[Y n j | 𝓕 n j] =ᵐ[μ] 0)
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hboundX : ∀ n j ω, |X n j ω| ≤ b n) (hboundY : ∀ n j ω, |Y n j ω| ≤ b n)
    (hCbrX : ∀ n ω, ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2 ≤ C)
    (hCbrY : ∀ n ω, ∑ j ∈ Finset.range (kn n), (Y n j ω) ^ 2 ≤ C)
    (hbrX : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2) atTop (𝓝 sX))
    (hbrY : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (Y n j ω) ^ 2) atTop (𝓝 sY))
    (hbrXY : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (X n j ω) * (Y n j ω)) atTop (𝓝 0)) :
    ∀ a c : ℝ, Tendsto
      (fun n => ∫ ω, Complex.exp (((a * partialSum (X n) (kn n) ω
          + c * partialSum (Y n) (kn n) ω : ℝ) : ℂ) * Complex.I) ∂μ)
      atTop (𝓝 (Complex.exp (((-(a ^ 2 * sX + c ^ 2 * sY) / 2 : ℝ) : ℂ)))) := by
        intro a c
        set Z : ℕ → ℕ → Ω → ℝ := fun n j ω => a * X n j ω + c * Y n j ω
        set σsq := a^2 * sX + c^2 * sY
        set bb := fun n => (|a| + |c|) * b n
        set CC := 2 * (a^2 + c^2) * C;
        have hZ : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (Z n j) := by
          exact fun n j => StronglyMeasurable.add ( StronglyMeasurable.const_mul ( hadaptX n j ) _ ) ( StronglyMeasurable.const_mul ( hadaptY n j ) _ )
        have hZmds : ∀ n j, μ[Z n j | 𝓕 n j] =ᵐ[μ] 0 := by
          intro n j;
          convert condExp_linear_comb_eq_zero a c _ _ ( hmdsX n j ) ( hmdsY n j ) using 1;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            exact fun ω => b n;
            · norm_num;
            · exact hadaptX n j |> fun h => h.aestronglyMeasurable.mono ( hle n ( j + 1 ) );
            · exact Filter.Eventually.of_forall fun ω => hboundX n j ω;
          · exact integrable_real_of_bound ( ( hadaptY n j |> StronglyMeasurable.aestronglyMeasurable ) |> fun h => h.mono ( hle n ( j + 1 ) ) ) ( fun ω => hboundY n j ω )
        have hZbound : ∀ n j ω, |Z n j ω| ≤ bb n := by
          intro n j ω; specialize hboundX n j ω; specialize hboundY n j ω; simp +zetaDelta at *;
          exact abs_le.mpr ⟨ by cases abs_cases a <;> cases abs_cases c <;> nlinarith [ abs_le.mp hboundX, abs_le.mp hboundY ], by cases abs_cases a <;> cases abs_cases c <;> nlinarith [ abs_le.mp hboundX, abs_le.mp hboundY ] ⟩
        have hZCbr : ∀ n ω, ∑ j ∈ Finset.range (kn n), (Z n j ω) ^ 2 ≤ CC := by
          intro n ω
          have hZsq : ∀ j, (Z n j ω) ^ 2 ≤ 2 * (a ^ 2 * (X n j ω) ^ 2 + c ^ 2 * (Y n j ω) ^ 2) := by
            intro j; nlinarith only [ sq_nonneg ( a * X n j ω - c * Y n j ω ) ] ;
          refine' le_trans ( Finset.sum_le_sum fun j _ => hZsq j ) _;
          simp +decide only [mul_add, sum_add_distrib, ← mul_sum _ _ _];
          nlinarith [ hCbrX n ω, hCbrY n ω ]
        have hZbracket : ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (Z n j ω) ^ 2) atTop (𝓝 σsq) := by
          filter_upwards [ hbrX, hbrY, hbrXY ] with ω hωX hωY hωXY;
          convert Filter.Tendsto.add ( Filter.Tendsto.add ( hωX.const_mul ( a ^ 2 ) ) ( hωY.const_mul ( c ^ 2 ) ) ) ( hωXY.const_mul ( 2 * a * c ) ) using 2 <;> ring;
          simp +decide only [add_sq, mul_pow, mul_comm, mul_assoc, mul_left_comm, sum_add_distrib, Finset.mul_sum _ _ _,
              Z] ; ring;
        have := @core_charFun_tendsto;
        convert this kn 𝓕 Z σsq bb CC hmono hle hZ hZmds ( fun n => mul_nonneg ( add_nonneg ( abs_nonneg a ) ( abs_nonneg c ) ) ( hb0 n ) ) ( by simpa using hblim.const_mul ( |a| + |c| ) ) hZbound hZCbr hZbracket 1 using 2 ; norm_num;
        · simp +decide [ Z, partialSum, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
        · norm_num

end Bivariate

/-!
## Tier 3 (interface only) — continuous-time corollary

The full path-space (Skorokhod) statement is deliberately out of scope (Mathlib has no
Skorokhod space), and is *not* attempted here.  The fixed-time continuous-time corollary
reduces to Tier 1 as follows, recorded here as an interface rather than a theorem because
it depends on a concrete pure-jump martingale encoding that is not part of this file.

Let `M` be a pure-jump square-integrable martingale on `[0,T]` with bounded jumps
`|ΔM| ≤ β` and finitely many jumps a.s., normalized by `√c_T`.  Its dyadic discretization
`X_{n,j} := (M(jT/n) - M((j-1)T/n)) / √c_T` is a martingale difference array for the
filtration `𝓕 n j := σ(M(iT/n) : i ≤ j)`, and:

* the deterministic jump bound (condition (a), in the sanctioned strengthened form of
  `mcleish_clt`/`core_charFun_tendsto`) holds with `b n := β / √c_T → 0` as `c_T → ∞`;
* the bracket convergence (condition (b)) `∑_j X_{n,j}² = ⟨M⟩_T / c_T → σ²` follows from the
  quadratic-variation hypothesis `⟨M⟩_T / c_T → σ²`, with the uniform bracket bound
  supplied by the same quadratic-variation control.

Feeding these into `core_charFun_tendsto` (or `mcleish_clt`, given Lévy continuity) yields
`M(T)/√c_T ⇒ N(0, σ²)`.  A formal statement would take the discretized array and its
two conditions as hypotheses and invoke `core_charFun_tendsto` verbatim; the only missing
ingredient is a Mathlib encoding of the pure-jump martingale and its quadratic variation,
which is why this tier is left as an interface note.
-/

end TypeDDecoupling.MartingaleCLT