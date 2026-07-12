import Mathlib

/-!
# Formalization of closed-form claims from "Fluctuations of the type D ASEP"

This file formalizes several self-contained mathematical claims from the working draft
`typeD_decoupling-draft-rev2.tex` ("Fluctuations of the type D ASEP: decoupling in two
universality classes").

The marquee closed-form result of the paper is **Theorem `thm:closed`**: in the
critically weak-asymmetry (Edwards–Wilkinson) regime `q = 1 - c/T`, the limiting
cross-correlation of the two species' fluctuations is the explicit function

  `ρ(c) = (1 - e^{-4c}) / (4c)`,

decreasing from `1` as `c → 0` to a `1/c` tail as `c → ∞`.

We formalize:

* the analytic content of `thm:closed`: `ρ` takes values in `(0,1)`, is strictly
  decreasing on `(0,∞)`, tends to `1` at `0⁺`, tends to `0` at `∞`, with the precise
  `c·ρ(c) → 1/4` (i.e. the `1/(4c)` tail);
* the mean of the mixing variable `U = min(Exp(4c), 1)` driving the limiting mixture
  (Proposition `prop:twophase` / Lemma `lem:split`), namely
  `E[min(Exp(4c),1)] = ∫₀¹ e^{-4ct} dt = ρ(c)`, which is exactly the limiting
  bound-state occupation `E[τ₀]/T` appearing in the proof of `thm:closed`;
* the key algebraic identity in the proof of `thm:closed`: passing to sum/difference
  coordinates `S = X₁+X₂`, `R = X₂-X₁`, with `Cov(S,R)=0`, gives
  `Corr(X₁,X₂) = (Var S - Var R)/(Var S + Var R)`;
* the diagonal hydrodynamic flux Hessian of the exact current decoupling
  (Proposition `prop:decouple`(b)): the macroscopic species flux is a function of its
  own density alone, so all cross-derivatives vanish.
-/

open scoped BigOperators Real
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ProbabilityTheory

namespace TypeDDecoupling

/-- The crossover correlation `ρ(c) = (1 - e^{-4c})/(4c)` of Theorem `thm:closed`. -/
noncomputable def rhoCorr (c : ℝ) : ℝ := (1 - Real.exp (-(4 * c))) / (4 * c)

/--
For `c > 0` the crossover correlation is positive.
-/
lemma rhoCorr_pos {c : ℝ} (hc : 0 < c) : 0 < rhoCorr c := by
  exact div_pos ( by norm_num; positivity ) ( by positivity )

/--
For `c > 0` the crossover correlation is `< 1`.
-/
lemma rhoCorr_lt_one {c : ℝ} (hc : 0 < c) : rhoCorr c < 1 := by
  rw [ rhoCorr, div_lt_iff₀ ];
  · linarith [ Real.add_one_lt_exp ( show - ( 4 * c ) ≠ 0 by linarith ) ];
  · positivity

/-- The crossover correlation lies in `(0,1)` for every `c > 0` (Theorem `thm:closed`). -/
lemma rhoCorr_mem_Ioo {c : ℝ} (hc : 0 < c) : rhoCorr c ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨rhoCorr_pos hc, rhoCorr_lt_one hc⟩

/--
The crossover correlation is strictly decreasing on `(0,∞)` (Theorem `thm:closed`).
-/
lemma rhoCorr_strictAntiOn : StrictAntiOn rhoCorr (Set.Ioi (0 : ℝ)) := by
  -- Let's compute the derivative of `rhoCorr` using the quotient rule.
  have h_deriv : ∀ c > 0, deriv rhoCorr c = (Real.exp (-(4 * c)) * (4 * c + 1) - 1) / (4 * c ^ 2) := by
    intro c hc;
    convert HasDerivAt.deriv ( HasDerivAt.div ( HasDerivAt.sub ( hasDerivAt_const _ _ ) ( HasDerivAt.exp ( HasDerivAt.neg ( HasDerivAt.const_mul 4 ( hasDerivAt_id' c ) ) ) ) ) ( HasDerivAt.const_mul 4 ( hasDerivAt_id' c ) ) _ ) using 1 <;> norm_num [ hc.ne' ] ; ring_nf!;
  -- We need to show that the derivative of `rhoCorr` is negative on `(0, ∞)`.
  have h_deriv_neg : ∀ c > 0, deriv rhoCorr c < 0 := by
    intro c hc; rw [ h_deriv c hc ] ; exact div_neg_of_neg_of_pos ( by nlinarith [ Real.exp_pos ( - ( 4 * c ) ), Real.exp_neg ( 4 * c ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( 4 * c ) ) ), Real.add_one_lt_exp ( show ( 4 * c ) ≠ 0 by positivity ) ] ) ( by positivity ) ;
  -- Apply the fact that if the derivative of a function is negative on an interval, then the function is strictly decreasing on that interval.
  apply strictAntiOn_of_deriv_neg;
  · exact convex_Ioi 0;
  · exact continuousOn_of_forall_continuousAt fun x hx => by exact DifferentiableAt.continuousAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_lt ( h_deriv_neg x hx ) ) ) ;
  · aesop

/--
As `c → 0⁺`, the crossover correlation tends to `1` (Theorem `thm:closed`).
-/
lemma rhoCorr_tendsto_one :
    Tendsto rhoCorr (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  -- We'll use the fact that $e^{-4c} - 1 \sim -4c$ as $c \to 0$.
  have h_exp : Filter.Tendsto (fun c => (Real.exp (-4 * c) - 1) / c) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-4)) := by
    simpa [ div_eq_inv_mul ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.exp ( HasDerivAt.const_mul ( -4 : ℝ ) ( hasDerivAt_id 0 ) ) );
  convert h_exp.neg.const_mul ( 1 / 4 ) using 2 <;> norm_num
  unfold rhoCorr; ring

/--
As `c → ∞`, the crossover correlation tends to `0` (Theorem `thm:closed`).
-/
lemma rhoCorr_tendsto_zero : Tendsto rhoCorr atTop (nhds 0) := by
  exact le_trans ( Filter.Tendsto.div_atTop ( tendsto_const_nhds.sub ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| Filter.tendsto_id.const_mul_atTop zero_lt_four ) ) <| Filter.tendsto_id.const_mul_atTop zero_lt_four ) ( by norm_num )

/--
The precise `1/(4c)` tail of the crossover correlation: `c·ρ(c) → 1/4`
(Theorem `thm:closed`).
-/
lemma rhoCorr_tail : Tendsto (fun c => c * rhoCorr c) atTop (nhds (1 / 4)) := by
  -- For $c \neq 0$, we can rewrite $c \cdot \rho(c)$ as $(1 - e^{-4c}) / 4$.
  have h_eq : ∀ c > 0, c * rhoCorr c = (1 - Real.exp (-(4 * c))) / 4 := by
    exact fun c hc => by rw [ rhoCorr, mul_div, mul_comm ] ; rw [ div_eq_iff ( by positivity ) ] ; ring;
  rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with c hc using h_eq c hc ) ] ; convert Filter.Tendsto.div_const ( tendsto_const_nhds.sub ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| Filter.tendsto_id.const_mul_atTop zero_lt_four ) ) _ using 2 ; norm_num;

/--
The mean of the mixing variable `U = min(Exp(4c), 1)` of the limiting mixture
(Proposition `prop:twophase`, Lemma `lem:split`) equals the crossover correlation:
`E[min(Exp(4c),1)] = ∫₀¹ e^{-4ct} dt = ρ(c)`. This integral is exactly the limiting
bound-state occupation `E[τ₀]/T` used in the proof of Theorem `thm:closed`.
-/
lemma integral_exp_eq_rhoCorr {c : ℝ} (hc : 0 < c) :
    (∫ t in (0:ℝ)..1, Real.exp (-(4 * c) * t)) = rhoCorr c := by
  rw [ intervalIntegral.integral_comp_mul_left ] <;> norm_num [ rhoCorr, hc.ne' ] ; ring

/--
**Key algebraic step in the proof of Theorem `thm:closed`.**
Passing to the sum and difference coordinates `S = X₁ + X₂`, `R = X₂ - X₁`, so that
`X₁ = (S - R)/2`, `X₂ = (S + R)/2`, and using the exact symmetry identity `Cov(S,R) = 0`,
the cross-correlation of the two species is

  `Corr(X₁, X₂) = (Var S - Var R) / (Var S + Var R)`.

Here `Corr` is the covariance divided by the product of standard deviations.
-/
lemma corr_sum_diff {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {S R : Ω → ℝ}
    (hS : MemLp S 2 μ) (hR : MemLp R 2 μ) (hcov : cov[S, R; μ] = 0)
    (hpos : 0 < Var[S; μ] + Var[R; μ]) :
    cov[fun ω => (S ω - R ω) / 2, fun ω => (S ω + R ω) / 2; μ]
        / (Real.sqrt (Var[fun ω => (S ω - R ω) / 2; μ])
            * Real.sqrt (Var[fun ω => (S ω + R ω) / 2; μ]))
      = (Var[S; μ] - Var[R; μ]) / (Var[S; μ] + Var[R; μ]) := by
  -- Using the linearity and symmetry properties of the covariance, we can expand the left-hand side.
  have cov_expand : cov[(fun ω => (S ω - R ω) / 2), (fun ω => (S ω + R ω) / 2); μ] = (1 / 4) * (Var[S; μ] - Var[R; μ]) := by
    have h_cov : cov[(fun ω => (S ω - R ω) / 2), (fun ω => (S ω + R ω) / 2); μ] = (1 / 4) * (cov[S, S; μ] + cov[S, R; μ] - cov[R, S; μ] - cov[R, R; μ]) := by
      norm_num [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm, ProbabilityTheory.covariance ];
      rw [ ← MeasureTheory.integral_sub ];
      · rw [ ← MeasureTheory.integral_const_mul ] ; congr ; ext ω ; norm_num [ MeasureTheory.integral_add, MeasureTheory.integral_sub, MeasureTheory.integral_mul_const, hS.integrable one_le_two, hR.integrable one_le_two ] ; ring;
      · simpa only [ ← sq ] using hS.sub ( MeasureTheory.memLp_const _ ) |> fun h => h.integrable_sq;
      · simpa only [ ← sq ] using hR.sub ( memLp_const _ ) |> fun h => h.integrable_sq;
    simp_all +decide [ covariance_comm ];
    rw [ covariance_self, covariance_self ];
    · exact hR.1.aemeasurable;
    · exact hS.1.aemeasurable;
  -- Using the linearity and symmetry properties of the variance, we can expand the left-hand side.
  have var_expand : Var[(fun ω => (S ω - R ω) / 2); μ] = (1 / 4) * (Var[S; μ] + Var[R; μ]) ∧ Var[(fun ω => (S ω + R ω) / 2); μ] = (1 / 4) * (Var[S; μ] + Var[R; μ]) := by
    constructor <;> norm_num [ div_eq_inv_mul, ProbabilityTheory.variance_const_mul, hcov ];
    · have := ProbabilityTheory.variance_sub ( hS ) ( hR );
      aesop;
    · convert ProbabilityTheory.variance_add hS hR using 1;
      linarith;
  grind

/-- The macroscopic hydrodynamic flux of a species (Proposition `prop:decouple`(b)):
`E_{ν_ρ}[j_i] = (r_R - r_L) · ρ_i (1 - ρ_i)`, a function of the species' own density alone. -/
def flux (rR rL ρ : ℝ) : ℝ := (rR - rL) * ρ * (1 - ρ)

/--
**Exact current decoupling, Proposition `prop:decouple`(b).** The species-`2` flux
does not depend on the species-`1` density `ρ₁`; hence its `ρ₁`-derivative vanishes, the
two-species hydrodynamic flux Hessian is diagonal.
-/
lemma flux_cross_deriv (rR rL ρ₁ ρ₂ : ℝ) :
    deriv (fun _ρ => flux rR rL ρ₂) ρ₁ = 0 := by
  convert deriv_const _ _ using 1

/--
The second `ρ₁`-derivative of the species-`2` flux vanishes too (Prop. `prop:decouple`(b)).
-/
lemma flux_cross_deriv2 (rR rL ρ₁ ρ₂ : ℝ) :
    deriv (deriv (fun _ρ => flux rR rL ρ₂)) ρ₁ = 0 := by
  unfold flux; norm_num;

/-!
## Bessel–Struve positive-part correlation (Proposition `prop:struve`)

For the limiting mixture `(G₁,G₂)` of Theorem `thm:cross`, each `Gᵢ ~ N(0,1)`, and with
`Gᵢ⁺ = max(Gᵢ,0)` the proof of Proposition `prop:struve` shows

  `Corr(G₁⁺,G₂⁺) = (E[g(U)] - 1/(2π)) / (1/2 - 1/(2π))`,

where `g(u) = E[Z₁⁺Z₂⁺]` is the positive-part covariance of a correlation-`u` bivariate
normal and `U ~ min(Exp(4c),1)`. By Price's theorem (`lem:price`) `g'(u) = 1/4 + arcsin u/(2π)`,
`g(0) = 1/(2π)`, so

  `E[g(U)] - 1/(2π) = ∫₀¹ g'(s) P(U > s) ds = (1/(2π)) ∫₀¹ (π/2 + arcsin s) e^{-4cs} ds`.

The paper then rewrites the resulting integral in closed form via the modified Bessel
`I₀` and Struve `L₀` functions:

  `Corr(G₁⁺,G₂⁺) = π/(8(π-1)c) [1 - 2e^{-4c} + I₀(4c) - L₀(4c)]`.

Since `I₀`/`L₀` are not available in Mathlib, we formalize the equivalent **integral form**
that the proof establishes, `rhoStruve`, and prove its analytic content: it lies in `(0,1)`,
tends to `1` as `c → 0⁺`, and has the precise `1/c` tail `c·Corr → π/(8(π-1))`.
-/

/-- The numerator integral `∫₀¹ (π/2 + arcsin s) e^{-4cs} ds` of Proposition `prop:struve`. -/
noncomputable def rhoStruveNum (c : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..1, (Real.pi / 2 + Real.arcsin s) * Real.exp (-(4 * c) * s)

/-- The positive-part correlation `Corr(G₁⁺,G₂⁺)` of Proposition `prop:struve`, in the
integral form derived in its proof:
`(E[g(U)] - 1/(2π)) / (1/2 - 1/(2π))` with
`E[g(U)] - 1/(2π) = (1/(2π)) ∫₀¹ (π/2 + arcsin s) e^{-4cs} ds`. -/
noncomputable def rhoStruve (c : ℝ) : ℝ :=
  (1 / (2 * Real.pi) * rhoStruveNum c) / (1 / 2 - 1 / (2 * Real.pi))

/-
The Jordan-type bound `arcsin s ≤ (π/2) s` for `s ∈ [0,1]`.
-/
lemma arcsin_le_pi_div_two_mul {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    Real.arcsin s ≤ Real.pi / 2 * s := by
  rw [ Real.arcsin_le_iff_le_sin ];
  · convert Real.mul_le_sin _ _ using 1 <;> ring <;> norm_num [ h0, h1 ];
    · positivity;
    · nlinarith [ Real.pi_pos ];
  · constructor <;> linarith;
  · constructor <;> nlinarith [ Real.pi_pos ]

/-
The denominator `1/2 - 1/(2π)` of `rhoStruve` is positive.
-/
lemma rhoStruve_denom_pos : (0 : ℝ) < 1 / 2 - 1 / (2 * Real.pi) := by
  rw [ sub_pos, div_lt_div_iff₀ ] <;> linarith [ Real.pi_gt_three ]

/-
The base integral `∫₀¹ (π/2 + arcsin s) ds = π - 1`.
-/
lemma integral_pi_half_add_arcsin :
    (∫ s in (0:ℝ)..1, (Real.pi / 2 + Real.arcsin s)) = Real.pi - 1 := by
  rw [ intervalIntegral.integral_add, intervalIntegral.integral_const ] <;> norm_num;
  · rw [ intervalIntegral.integral_eq_sub_of_hasDeriv_right ];
    rotate_right;
    use fun x => x * Real.arcsin x + Real.sqrt ( 1 - x ^ 2 );
    · simpa using by ring;
    · fun_prop;
    · intro x hx; convert HasDerivAt.hasDerivWithinAt <| HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_id x ) <| Real.hasDerivAt_arcsin .. ) <| HasDerivAt.sqrt ( HasDerivAt.const_sub 1 <| hasDerivAt_pow 2 x ) .. using 1 <;> norm_num at * <;> ring;
      · linarith;
      · linarith;
      · nlinarith;
    · exact Continuous.intervalIntegrable ( Real.continuous_arcsin ) _ _;
  · exact Continuous.intervalIntegrable ( Real.continuous_arcsin ) _ _

/-
The numerator integral is positive for every `c`.
-/
lemma rhoStruveNum_pos (c : ℝ) : 0 < rhoStruveNum c := by
  refine' ( lt_of_lt_of_le _ ( intervalIntegral.integral_mono_on _ _ _ fun x hx => mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( show - ( 4 * c ) * x ≥ - ( 4 * |c| ) by cases abs_cases c <;> nlinarith [ hx.1, hx.2 ] ) ) ( by linarith [ Real.pi_pos, Real.arcsin_nonneg.mpr hx.1 ] ) ) ) <;> norm_num;
  · exact mul_pos ( by rw [ integral_pi_half_add_arcsin ] ; linarith [ Real.pi_gt_three ] ) ( Real.exp_pos _ );
  · exact Continuous.intervalIntegrable ( by continuity ) _ _;
  · exact Continuous.intervalIntegrable ( by continuity ) _ _

/-
For `c > 0` the numerator integral is strictly below its `c = 0` value `π - 1`.
-/
lemma rhoStruveNum_lt_base {c : ℝ} (hc : 0 < c) : rhoStruveNum c < Real.pi - 1 := by
  -- Apply the strict interval-integral monotonicity lemma.
  have h_int_mono : ∫ s in (0:ℝ)..1, (Real.pi / 2 + Real.arcsin s) * (1 - Real.exp (-(4 * c) * s)) > 0 := by
    rw [ intervalIntegral.integral_of_le ] <;> norm_num;
    rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
    · simp +decide [ Function.support ];
      exact lt_of_lt_of_le ( by norm_num ) ( MeasureTheory.measure_mono <| show Set.Ioo 0 1 ⊆ { x : ℝ | ¬ Real.pi / 2 + Real.arcsin x = 0 ∧ ¬ 1 - Real.exp ( - ( 4 * c * x ) ) = 0 } ∩ Set.Ioc 0 1 from fun x hx => ⟨ ⟨ by linarith [ Real.pi_pos, Real.arcsin_nonneg.2 hx.1.le ], by exact ne_of_gt <| sub_pos.2 <| Real.exp_lt_one_iff.2 <| by nlinarith [ hx.1, hx.2 ] ⟩, ⟨ hx.1, hx.2.le ⟩ ⟩ );
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using mul_nonneg ( add_nonneg ( by positivity ) ( Real.arcsin_nonneg.2 hx.1.le ) ) ( sub_nonneg.2 ( Real.exp_le_one_iff.2 ( by nlinarith [ hx.1, hx.2 ] ) ) );
    · exact Continuous.integrableOn_Ioc ( by continuity );
  simp_all +decide [ mul_sub ];
  rw [ intervalIntegral.integral_sub ] at h_int_mono <;> norm_num at *;
  · convert h_int_mono using 1;
    · unfold rhoStruveNum; congr; ext; ring;
    · convert integral_pi_half_add_arcsin.symm using 1;
  · exact Continuous.intervalIntegrable ( by continuity ) _ _;
  · exact Continuous.intervalIntegrable ( by continuity ) _ _

/-
The positive-part correlation lies in `(0,1)` for every `c > 0` (Proposition `prop:struve`).
-/
lemma rhoStruve_mem_Ioo {c : ℝ} (hc : 0 < c) : rhoStruve c ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold rhoStruve;
  field_simp;
  exact ⟨ div_pos ( rhoStruveNum_pos c ) ( by linarith [ Real.pi_gt_three ] ), by rw [ div_lt_one ( by linarith [ Real.pi_gt_three ] ) ] ; exact rhoStruveNum_lt_base hc ⟩

/-
As `c → 0⁺`, the numerator integral tends to its base value `π - 1`.
-/
lemma rhoStruveNum_tendsto_base :
    Tendsto rhoStruveNum (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi - 1)) := by
  -- We'll use the fact that the integral of a continuous function over a compact interval is continuous.
  have h_continuous : Continuous (fun c => ∫ s in (0)..1, (Real.pi / 2 + Real.arcsin s) * Real.exp (-(4 * c) * s)) := by
    fun_prop;
  convert h_continuous.tendsto 0 |> Filter.Tendsto.mono_left <| nhdsWithin_le_nhds using 2 ; norm_num [ integral_pi_half_add_arcsin ]

/-
Helper for the tail: `c·∫₀¹ s·e^{-4cs} ds → 0` as `c → ∞`.
-/
lemma c_mul_integral_id_exp_tendsto_zero :
    Tendsto (fun c => c * ∫ s in (0:ℝ)..1, s * Real.exp (-(4 * c) * s)) atTop (nhds 0) := by
  -- Let's simplify the expression inside the integral.
  suffices h_simp : Filter.Tendsto (fun c : ℝ => c * (1 - (1 + 4 * c) * Real.exp (-4 * c)) / (16 * c ^ 2)) Filter.atTop (nhds 0) by
    refine h_simp.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with c hc;
    rw [ intervalIntegral.integral_deriv_eq_sub' ];
    rotate_left;
    use fun s => - ( s / ( 4 * c ) + 1 / ( 4 * c ) ^ 2 ) * Real.exp ( - ( 4 * c ) * s );
    · ext; norm_num [ mul_comm, hc.ne' ] ; ring;
      norm_num [ sq, mul_assoc, hc.ne' ];
    · fun_prop;
    · fun_prop;
    · -- Let's simplify the expression.
      field_simp
      ring;
      norm_num ; ring;
  -- We can cancel out $c$ in the numerator and denominator.
  suffices h_cancel : Filter.Tendsto (fun c : ℝ => (1 - (1 + 4 * c) * Real.exp (-4 * c)) / (16 * c)) Filter.atTop (nhds 0) by
    refine h_cancel.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with c hc using by rw [ ← mul_div_mul_left _ _ hc.ne' ] ; ring );
  -- We'll use the fact that $e^{-4c}$ goes to $0$ faster than any polynomial grows.
  have h_exp : Filter.Tendsto (fun c : ℝ => (1 + 4 * c) * Real.exp (-4 * c)) Filter.atTop (nhds 0) := by
    -- Let $y = 4c$, therefore the limit becomes $\lim_{y \to \infty} (1 + y) e^{-y}$.
    suffices h_y : Filter.Tendsto (fun y : ℝ => (1 + y) * Real.exp (-y)) Filter.atTop (nhds 0) by
      convert h_y.comp ( Filter.tendsto_id.const_mul_atTop zero_lt_four ) using 2 ; norm_num;
    ring_nf;
    simpa using Filter.Tendsto.add ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 ) ( Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot );
  simpa using Filter.Tendsto.div_atTop ( h_exp.const_sub 1 ) ( Filter.tendsto_id.const_mul_atTop ( by norm_num ) )

/-
The precise `1/c` tail of the numerator integral: `c·rhoStruveNum c → π/8`.
-/
lemma rhoStruveNum_tail :
    Tendsto (fun c => c * rhoStruveNum c) atTop (nhds (Real.pi / 8)) := by
  -- Split rhoStruveNum c (for each c) by linearity of the interval integral over the sum of integrands (π/2)·exp(-(4c)s) and arcsin s · exp(-(4c)s):
  have h_split : ∀ c > 0, rhoStruveNum c = (Real.pi / 2) * rhoCorr c + ∫ s in (0:ℝ)..1, Real.arcsin s * Real.exp (-(4 * c) * s) := by
    intro c hc; rw [ ← integral_exp_eq_rhoCorr hc ] ; rw [ rhoStruveNum ] ; rw [ ← intervalIntegral.integral_const_mul ] ; rw [ ← intervalIntegral.integral_add ] ; congr ; ext ; ring;
    · exact Continuous.intervalIntegrable ( by continuity ) _ _;
    · exact Continuous.intervalIntegrable ( by continuity ) _ _;
  -- We have, for c > 0 and s ∈ [0,1]: 0 ≤ arcsin s · exp(-(4c)s) ≤ (π/2 · s)·exp(-(4c)s) (using arcsin s ≥ 0 from Real.arcsin_nonneg for s ≥ 0, exp > 0, and arcsin_le_pi_div_two_mul). Integrating (monotonicity of interval integral, both integrands nonneg and integrable): 0 ≤ ∫₀¹ arcsin s · exp(-(4c)s) ds ≤ (π/2)·∫₀¹ s·exp(-(4c)s) ds.
  have h_bound : ∀ c > 0, 0 ≤ c * ∫ s in (0:ℝ)..1, Real.arcsin s * Real.exp (-(4 * c) * s) ∧ c * ∫ s in (0:ℝ)..1, Real.arcsin s * Real.exp (-(4 * c) * s) ≤ (Real.pi / 2) * c * ∫ s in (0:ℝ)..1, s * Real.exp (-(4 * c) * s) := by
    intro c hc; refine' ⟨ _, _ ⟩;
    · exact mul_nonneg hc.le ( intervalIntegral.integral_nonneg ( by norm_num ) fun x hx => mul_nonneg ( Real.arcsin_nonneg.2 hx.1 ) ( Real.exp_nonneg _ ) );
    · -- Applying the bound $0 \leq \arcsin s \leq \frac{\pi}{2} s$ to the integral.
      have h_integral_bound : ∫ s in (0:ℝ)..1, Real.arcsin s * Real.exp (-(4 * c) * s) ≤ ∫ s in (0:ℝ)..1, (Real.pi / 2) * s * Real.exp (-(4 * c) * s) := by
        refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
        · exact Continuous.intervalIntegrable ( by continuity ) _ _;
        · exact Continuous.intervalIntegrable ( by continuity ) _ _;
        · exact fun x hx₁ hx₂ => mul_le_mul_of_nonneg_right ( by simpa using arcsin_le_pi_div_two_mul hx₁ hx₂ ) ( Real.exp_nonneg _ );
      convert mul_le_mul_of_nonneg_left h_integral_bound hc.le using 1 ; norm_num [ mul_assoc, mul_comm, mul_left_comm, ← intervalIntegral.integral_const_mul ];
  -- Using the bound, we can show that the second term tends to 0 as $c \to \infty$.
  have h_second_term_zero : Filter.Tendsto (fun c => c * ∫ s in (0:ℝ)..1, Real.arcsin s * Real.exp (-(4 * c) * s)) Filter.atTop (nhds 0) := by
    have h_second_term_zero : Filter.Tendsto (fun c => (Real.pi / 2) * c * ∫ s in (0:ℝ)..1, s * Real.exp (-(4 * c) * s)) Filter.atTop (nhds 0) := by
      simpa [ mul_assoc ] using Filter.Tendsto.const_mul ( Real.pi / 2 ) ( c_mul_integral_id_exp_tendsto_zero );
    exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun c hc => by rw [ Real.norm_of_nonneg ( h_bound c ( by positivity ) |>.1 ) ] ; exact h_bound c ( by positivity ) |>.2 ⟩ ) h_second_term_zero;
  -- Using the split form and the fact that the second term tends to 0, we can conclude the proof.
  have h_final : Filter.Tendsto (fun c => c * ((Real.pi / 2) * rhoCorr c)) Filter.atTop (nhds (Real.pi / 8)) := by
    convert Filter.Tendsto.const_mul ( Real.pi / 2 ) ( rhoCorr_tail ) using 2 <;> ring;
  simpa using Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with c hc; rw [ h_split c hc ] ; ring ) ( h_final.add h_second_term_zero )

/-
As `c → 0⁺`, the positive-part correlation tends to `1` (Proposition `prop:struve`).
-/
lemma rhoStruve_tendsto_one :
    Tendsto rhoStruve (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  convert Filter.Tendsto.div_const ( Filter.Tendsto.mul tendsto_const_nhds ( rhoStruveNum_tendsto_base ) ) _ using 1;
  field_simp;
  rw [ div_self ( sub_ne_zero_of_ne ( by linarith [ Real.pi_gt_three ] ) ) ]

/-
The precise `1/c` tail of the positive-part correlation:
`c·Corr(G₁⁺,G₂⁺) → π/(8(π-1))` (Proposition `prop:struve`).
-/
lemma rhoStruve_tail :
    Tendsto (fun c => c * rhoStruve c) atTop (nhds (Real.pi / (8 * (Real.pi - 1)))) := by
  convert Tendsto.div_const ( Tendsto.const_mul ( 1 / ( 2 * Real.pi ) ) ( rhoStruveNum_tail ) ) ( 1 / 2 - 1 / ( 2 * Real.pi ) ) using 2;
  · unfold rhoStruve; ring;
  · field_simp

/-!
## Local detailed balance and vanishing cross coefficients (§3, `sec:decouple`)

The type D ASEP is reversible with respect to the product blocking measure `ν`
(Proposition `prop:measure`, eq. `eq:nu`)

  `ν(η) = ∏ₓ α₁^{η₁,ₓ} α₂^{η₂,ₓ} q^{-2x(η₁,ₓ + η₂,ₓ)}`,

a product over both sites `x ∈ ℤ` and the two species, with each species--`i` particle
at site `x` contributing the fugacity factor `αᵢ q^{-2x}`. We encode the local
two--point structure that the model-specific computations of §3 actually use: the
unnormalised weight of an adjacent pair `(x, x+1)` in local states `(a,b)`, where the
four local states `a ∈ {0,1,2,3}` are *empty*, *species 1*, *species 2*, *bound pair*.

From this we prove:

* **Local detailed balance, Lemma `lem:db`**: `ν(0,3) = q^{-4} ν(3,0)` and
  `ν(1,2) = ν(2,1) = q^{-2} ν(3,0)`;
* **Vanishing cross--mobility, Proposition `prop:cross`**: the equilibrium expectation
  of the carré du champ bond function
  `V_x = 𝟙_{(3,0)} + q⁴ 𝟙_{(0,3)} - q² 𝟙_{(1,2)} - q² 𝟙_{(2,1)}` vanishes, via the
  cancellation `ν(3,0)·(1 + 1 - 1 - 1) = 0` (`σ₁₂ = 0`);
* **Vanishing static cross--compressibility, Proposition `prop:cross`**: the two
  species are independent under `ν`, so the cross--compressibility
  `C₁₂ = Cov(N₁, N₂)/L` vanishes — here the model-independent fact that the
  covariance of two independent (square--integrable) random variables is zero.
-/

/-- Single-site unnormalised weight of the product blocking measure `ν` (eq. `eq:nu`)
in local state `a ∈ {0,1,2,3}` at site `x`: the empty state contributes `1`, a
species--`1` particle contributes `α₁ q^{-2x}`, a species--`2` particle contributes
`α₂ q^{-2x}`, and a bound pair (both species) contributes `α₁ α₂ q^{-4x}`. -/
noncomputable def siteWeight (a1 a2 q : ℝ) (x : ℤ) : ℕ → ℝ
  | 0 => 1
  | 1 => a1 * q ^ (-2 * x)
  | 2 => a2 * q ^ (-2 * x)
  | _ => a1 * a2 * q ^ (-4 * x)

/-- Unnormalised two--point weight of `ν` on the adjacent bond `(x, x+1)` in local
states `(a, b)`, the product of the two single-site weights. -/
noncomputable def twoPtWeight (a1 a2 q : ℝ) (a b : ℕ) (x : ℤ) : ℝ :=
  siteWeight a1 a2 q x a * siteWeight a1 a2 q (x + 1) b

/-- **Local detailed balance (Lemma `lem:db`), bound-pair relation.**
Moving the bound pair from `x` to `x+1` multiplies the weight by `q^{-4}`. -/
lemma twoPtWeight_zero_three (a1 a2 q : ℝ) (hq : q ≠ 0) (x : ℤ) :
    twoPtWeight a1 a2 q 0 3 x = q ^ (-4 : ℤ) * twoPtWeight a1 a2 q 3 0 x := by
  simp only [twoPtWeight, siteWeight, one_mul, mul_one]
  rw [show (-4 * (x + 1) : ℤ) = -4 + -4 * x by ring, zpow_add₀ hq]
  ring

/-- **Local detailed balance (Lemma `lem:db`), species-swap relation.**
Moving one species--`1` particle from `x` to `x+1` and one species--`2` particle from
`x+1` to `x` leaves a single `q^{-2}` deficit. -/
lemma twoPtWeight_one_two (a1 a2 q : ℝ) (hq : q ≠ 0) (x : ℤ) :
    twoPtWeight a1 a2 q 1 2 x = q ^ (-2 : ℤ) * twoPtWeight a1 a2 q 3 0 x := by
  simp only [twoPtWeight, siteWeight, mul_one]
  rw [show (-2 * (x + 1) : ℤ) = -2 * x + -2 by ring, zpow_add₀ hq,
    show (-4 * x : ℤ) = -2 * x + -2 * x by ring, zpow_add₀ hq]
  ring

/-- The two off-diagonal mixed states carry equal weight (Lemma `lem:db`). -/
lemma twoPtWeight_two_one (a1 a2 q : ℝ) (hq : q ≠ 0) (x : ℤ) :
    twoPtWeight a1 a2 q 2 1 x = q ^ (-2 : ℤ) * twoPtWeight a1 a2 q 3 0 x := by
  simp only [twoPtWeight, siteWeight, mul_one]
  rw [show (-2 * (x + 1) : ℤ) = -2 * x + -2 by ring, zpow_add₀ hq,
    show (-4 * x : ℤ) = -2 * x + -2 * x by ring, zpow_add₀ hq]
  ring

/-- **Vanishing cross--mobility (Proposition `prop:cross`).** The equilibrium
expectation of the carré du champ bond function
`V_x = 𝟙_{(3,0)} + q⁴ 𝟙_{(0,3)} - q² 𝟙_{(1,2)} - q² 𝟙_{(2,1)}` vanishes:
`ν(3,0) + q⁴ν(0,3) - q²ν(1,2) - q²ν(2,1) = ν(3,0)·(1 + 1 - 1 - 1) = 0`,
i.e. the equilibrium cross--mobility `σ₁₂ = 0`. -/
lemma crossMobility_eq_zero (a1 a2 q : ℝ) (hq : q ≠ 0) (x : ℤ) :
    twoPtWeight a1 a2 q 3 0 x + q ^ 4 * twoPtWeight a1 a2 q 0 3 x
        - q ^ 2 * twoPtWeight a1 a2 q 1 2 x - q ^ 2 * twoPtWeight a1 a2 q 2 1 x = 0 := by
  rw [twoPtWeight_zero_three a1 a2 q hq, twoPtWeight_one_two a1 a2 q hq,
    twoPtWeight_two_one a1 a2 q hq]
  have h4 : (q ^ 4 : ℝ) * q ^ (-4 : ℤ) = 1 := by
    rw [← zpow_natCast q 4, ← zpow_add₀ hq]; norm_num
  have h2 : (q ^ 2 : ℝ) * q ^ (-2 : ℤ) = 1 := by
    rw [← zpow_natCast q 2, ← zpow_add₀ hq]; norm_num
  linear_combination (twoPtWeight a1 a2 q 3 0 x) * h4
    - 2 * (twoPtWeight a1 a2 q 3 0 x) * h2

/-- **Vanishing static cross--compressibility (Proposition `prop:cross`).** The two
species are independent under the product blocking measure `ν`; consequently the static
cross--compressibility `C₁₂ = Cov(N₁, N₂)/L` vanishes, since the covariance of two
independent square--integrable random variables is zero. -/
lemma crossCompressibility_eq_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N1 N2 : Ω → ℝ}
    (h : IndepFun N1 N2 μ) (h1 : MemLp N1 2 μ) (h2 : MemLp N2 2 μ) :
    cov[N1, N2; μ] = 0 :=
  h.covariance_eq_zero h1 h2

/-!
## Sheppard's orthant formula (Lemma `lem:price`)

The paper's Lemma `lem:price` records two classical facts about the standard bivariate
normal `(Z₁, Z₂)` of correlation `u`:

* **Price's theorem**: `d/du E[Z₁⁺ Z₂⁺] = P(Z₁ > 0, Z₂ > 0)`;
* **Sheppard's orthant formula**: `P(Z₁ > 0, Z₂ > 0) = 1/4 + arcsin(u) / (2π)`.

We formalize the substantive closed form, **Sheppard's orthant formula**, which is the
quantity actually used (as `g'(u) = 1/4 + arcsin(u)/(2π)`) in the Bessel–Struve
correlation `prop:struve` already formalized above.

We model the standard bivariate normal of correlation `u` by the rotation
representation `(Z₁, Z₂) = (X, u·X + √(1-u²)·Y)` with `X, Y` independent standard
normals, so that the orthant probability is the integral of the standard planar Gaussian
density `g₂(x,y) = (1/2π) exp(-(x²+y²)/2)` over the wedge
`{x > 0, u·x + √(1-u²)·y > 0}`. -/

/-- The standard planar Gaussian density `g₂(x,y) = (1/2π) exp(-(x²+y²)/2)`. -/
noncomputable def gaussian2 (p : ℝ × ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2)

/-- The orthant probability `P(Z₁ > 0, Z₂ > 0)` of the standard bivariate normal of
correlation `u`, modelled via the rotation representation
`(Z₁, Z₂) = (X, u·X + √(1-u²)·Y)`: the integral of the planar Gaussian density over the
wedge `{x > 0, u·x + √(1-u²)·y > 0}`. -/
noncomputable def orthantProb (u : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ,
    Set.indicator {q : ℝ × ℝ | 0 < q.1 ∧ 0 < u * q.1 + Real.sqrt (1 - u ^ 2) * q.2}
      gaussian2 p

/-
The radial Gaussian integral `∫₀^∞ r e^{-r²/2} dr = 1`.
-/
lemma radial_gaussian_integral :
    ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-(r ^ 2) / 2) = 1 := by
  have := @integral_rpow_mul_exp_neg_mul_rpow;
  convert @this 2 1 ( 1 / 2 ) ( by norm_num ) ( by norm_num ) ( by norm_num ) using 1 <;> norm_num [ div_eq_inv_mul ]

/-
**Angular characterization of the wedge.** For `u ∈ (-1, 1)`, the set of angles
`θ ∈ (-π, π)` for which `(cos θ, sin θ)` lies in the wedge
`{0 < cos θ, 0 < u cos θ + √(1-u²) sin θ}` is exactly the interval
`(-arcsin u, π/2)`. The key identity is
`u cos θ + √(1-u²) sin θ = sin(θ + arcsin u)`.
-/
lemma wedge_angle_set (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    {θ : ℝ | θ ∈ Set.Ioo (-Real.pi) Real.pi ∧ 0 < Real.cos θ ∧
        0 < u * Real.cos θ + Real.sqrt (1 - u ^ 2) * Real.sin θ}
      = Set.Ioo (-Real.arcsin u) (Real.pi / 2) := by
  -- Prove the set equality by showing mutual inclusion.
  apply Set.ext
  intro θ
  constructor
  intro hθ
  obtain ⟨hθ_range, hθ_cos, hθ_sin⟩ := hθ;
  · -- From $0 < \cos \theta$, we get $-\frac{\pi}{2} < \theta < \frac{\pi}{2}$.
    have hθ_range' : -Real.pi / 2 < θ ∧ θ < Real.pi / 2 := by
      constructor <;> contrapose! hθ_cos;
      · rw [ ← Real.cos_neg ] ; exact Real.cos_nonpos_of_pi_div_two_le_of_le ( by linarith [ Set.mem_Ioo.mp hθ_range ] ) ( by linarith [ Set.mem_Ioo.mp hθ_range ] );
      · exact Real.cos_nonpos_of_pi_div_two_le_of_le hθ_cos ( by linarith [ Real.pi_pos, hθ_range.2 ] );
    -- From $0 < u \cos \theta + \sqrt{1 - u^2} \sin \theta$, we get $\sin(\theta + \arcsin u) > 0$.
    have h_sin_pos : Real.sin (θ + Real.arcsin u) > 0 := by
      rw [ Real.sin_add, Real.sin_arcsin, Real.cos_arcsin ] <;> linarith [ hu.1, hu.2 ];
    constructor <;> contrapose! h_sin_pos;
    · exact Real.sin_nonpos_of_nonpos_of_neg_pi_le ( by linarith ) ( by linarith [ Real.neg_pi_div_two_le_arcsin u, Real.arcsin_le_pi_div_two u ] );
    · linarith;
  · intro hθ
    have hθ_range : θ ∈ Set.Ioo (-Real.pi) Real.pi := by
      constructor <;> linarith [ hθ.1, hθ.2, Real.neg_pi_div_two_le_arcsin u, Real.arcsin_le_pi_div_two u, Real.pi_pos ]
    have hθ_cos : 0 < Real.cos θ := by
      exact Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos, hθ.1, Real.arcsin_le_pi_div_two u, Real.neg_pi_div_two_le_arcsin u ], by linarith [ Real.pi_pos, hθ.2, Real.arcsin_le_pi_div_two u, Real.neg_pi_div_two_le_arcsin u ] ⟩
    have hθ_sin : 0 < u * Real.cos θ + Real.sqrt (1 - u ^ 2) * Real.sin θ := by
      have hθ_sin : Real.sin (θ + Real.arcsin u) > 0 := by
        exact Real.sin_pos_of_pos_of_lt_pi ( by linarith [ hθ.1, hθ.2, Real.arcsin_le_pi_div_two u, Real.neg_pi_div_two_le_arcsin u ] ) ( by linarith [ hθ.1, hθ.2, Real.arcsin_le_pi_div_two u, Real.neg_pi_div_two_le_arcsin u ] );
      rw [ Real.sin_add, Real.sin_arcsin, Real.cos_arcsin ] at hθ_sin <;> linarith [ hu.1, hu.2 ]
    exact ⟨hθ_range, hθ_cos, hθ_sin⟩

/-
**Sheppard's orthant formula (Lemma `lem:price`).** For `u ∈ (-1, 1)`,
`P(Z₁ > 0, Z₂ > 0) = 1/4 + arcsin(u) / (2π)`.
-/
theorem orthantProb_eq (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    orthantProb u = 1 / 4 + Real.arcsin u / (2 * Real.pi) := by
  -- Use the integral_comp_polarCoord_symm lemma to rewrite the integral.
  have h_polar : ∫ p : ℝ × ℝ, Set.indicator {q : ℝ × ℝ | 0 < q.1 ∧ 0 < u * q.1 + Real.sqrt (1 - u ^ 2) * q.2} (gaussian2) p = ∫ p in polarCoord.target, p.1 * Set.indicator {q : ℝ × ℝ | 0 < q.1 ∧ 0 < u * q.1 + Real.sqrt (1 - u ^ 2) * q.2} (gaussian2) (polarCoord.symm p) := by
    convert ( integral_comp_polarCoord_symm _ ) |> Eq.symm using 1;
  -- Simplify the integrand using the properties of the Gaussian density and the indicator function.
  have h_simplify : ∫ p in polarCoord.target, p.1 * Set.indicator {q : ℝ × ℝ | 0 < q.1 ∧ 0 < u * q.1 + Real.sqrt (1 - u ^ 2) * q.2} (gaussian2) (polarCoord.symm p) = ∫ p in polarCoord.target, p.1 * (if p.2 ∈ Set.Ioo (-Real.arcsin u) (Real.pi / 2) then (1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2) / 2) else 0) := by
    refine' MeasureTheory.setIntegral_congr_fun _ _;
    · exact measurableSet_Ioi.prod measurableSet_Ioo;
    · intro p hp; simp +decide [ Set.indicator, gaussian2 ] ;
      congr! 1;
      · convert Set.ext_iff.mp ( wedge_angle_set u hu ) p.2 using 1;
        constructor <;> intro h <;> simp_all +decide [ mul_assoc, mul_comm ]; all_goals nlinarith;
      · rw [ show ( - ( p.1 * Real.sin p.2 ) ^ 2 + - ( p.1 * Real.cos p.2 ) ^ 2 ) / 2 = -p.1 ^ 2 / 2 by nlinarith only [ Real.sin_sq_add_cos_sq p.2 ] ];
  -- Evaluate the integral over the target set.
  have h_target : ∫ p in polarCoord.target, p.1 * (if p.2 ∈ Set.Ioo (-Real.arcsin u) (Real.pi / 2) then (1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2) / 2) else 0) = (∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-(r ^ 2) / 2)) * (∫ θ in Set.Ioo (-Real.arcsin u) (Real.pi / 2), (1 / (2 * Real.pi))) := by
    erw [ ← MeasureTheory.setIntegral_prod_mul ];
    rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    · congr with x ; split_ifs <;> ring;
      · aesop;
      · tauto;
      · exact False.elim <| ‹¬ ( 0 < x.1 ∧ -Real.pi < x.2 ∧ x.2 < Real.pi ) › ⟨ by linarith, by linarith [ Real.neg_pi_div_two_le_arcsin u, Real.arcsin_le_pi_div_two u ], by linarith [ Real.neg_pi_div_two_le_arcsin u, Real.arcsin_le_pi_div_two u ] ⟩;
    · exact measurableSet_Ioi.prod measurableSet_Ioo;
    · exact measurableSet_Ioi.prod measurableSet_Ioo;
  convert h_polar.trans ( h_simplify.trans h_target ) using 1 ; norm_num [ radial_gaussian_integral ] ; ring;
  rw [ max_eq_left ( by linarith [ Real.neg_pi_div_two_le_arcsin u, Real.arcsin_le_pi_div_two u ] ) ] ; ring;
  norm_num [ Real.pi_ne_zero ] ; ring

/-!
## Price's theorem (Lemma `lem:price`, first equality)

The positive-part covariance `g(u) = E[Z₁⁺ Z₂⁺]` of the standard bivariate normal of
correlation `u`, in the same rotation representation `(Z₁, Z₂) = (X, u·X + √(1-u²)·Y)`
used for `orthantProb`, is

  `positivePartCov u = ∫ (x⁺)·(u·x + √(1-u²)·y)⁺ · g₂(x,y) dx dy`.

Price's theorem states `g'(u) = P(Z₁ > 0, Z₂ > 0) = orthantProb u`. We prove it by
evaluating `g` in closed form via polar coordinates (exactly as for `orthantProb_eq`),
`g(u) = (√(1-u²) + (π/2 + arcsin u)·u)/(2π)`, and differentiating that closed form.
-/

/-- The positive-part covariance `g(u) = E[Z₁⁺ Z₂⁺]` of the standard bivariate normal of
correlation `u`, in the rotation representation `(Z₁, Z₂) = (X, u·X + √(1-u²)·Y)`. -/
noncomputable def positivePartCov (u : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ,
    max p.1 0 * max (u * p.1 + Real.sqrt (1 - u ^ 2) * p.2) 0 * gaussian2 p

/-
The radial integral `∫₀^∞ r³ e^{-r²/2} dr = 2`.
-/
lemma radial_gaussian_integral_cube :
    ∫ r in Set.Ioi (0 : ℝ), r ^ 3 * Real.exp (-(r ^ 2) / 2) = 2 := by
  have := @integral_rpow_mul_exp_neg_mul_rpow;
  convert @this 2 3 ( 1 / 2 ) ( by norm_num ) ( by norm_num ) ( by norm_num ) using 1 <;> norm_num [ div_eq_inv_mul ]

/-
The angular integral over the wedge for the positive-part covariance:
`∫_{-arcsin u}^{π/2} cos θ · sin(θ + arcsin u) dθ = (√(1-u²) + (π/2 + arcsin u)·u)/2`.
-/
lemma angular_pos_integral (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    ∫ θ in Set.Ioo (-Real.arcsin u) (Real.pi / 2),
        Real.cos θ * Real.sin (θ + Real.arcsin u)
      = (Real.sqrt (1 - u ^ 2) + (Real.pi / 2 + Real.arcsin u) * u) / 2 := by
  rw [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ];
  · norm_num [ Real.sin_add, Real.cos_add ];
    ring_nf;
    rw [ intervalIntegral.integral_add ] <;> norm_num [ mul_div ];
    · norm_num [ mul_comm ( Real.cos _ ) ] ; rw [ Real.sin_arcsin, Real.cos_arcsin ] <;> linarith [ hu.1, hu.2 ] ;
    · exact Continuous.intervalIntegrable ( by continuity ) _ _;
    · exact Continuous.intervalIntegrable ( by continuity ) _ _;
  · linarith [ Real.neg_pi_div_two_le_arcsin u, Real.arcsin_le_pi_div_two u ]

/-
Closed form of the positive-part covariance, obtained by passing to polar
coordinates (as for `orthantProb_eq`):
`g(u) = (√(1-u²) + (π/2 + arcsin u)·u)/(2π)`.
-/
theorem positivePartCov_eq (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    positivePartCov u
      = (Real.sqrt (1 - u ^ 2) + (Real.pi / 2 + Real.arcsin u) * u) / (2 * Real.pi) := by
  unfold positivePartCov;
  -- Apply `integral_comp_polarCoord_symm` to rewrite the integral in polar coordinates.
  have h_polar : ∫ p : ℝ × ℝ, max p.1 0 * max (u * p.1 + Real.sqrt (1 - u ^ 2) * p.2) 0 * gaussian2 p = ∫ p in Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi, p.1 * (max (p.1 * Real.cos p.2) 0 * max (u * p.1 * Real.cos p.2 + Real.sqrt (1 - u ^ 2) * p.1 * Real.sin p.2) 0 * (1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2) / 2)) := by
    have := @integral_comp_polarCoord_symm;
    convert this _ |> Eq.symm using 1;
    unfold gaussian2; norm_num [ mul_assoc, mul_comm, mul_left_comm ] ;
    norm_num [ mul_pow, Real.sin_sq, Real.cos_sq ] ; congr ; ext ; ring;
  -- Simplify the integrand on the target.
  have h_integrand : ∀ p : ℝ × ℝ, p ∈ Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi → max (p.1 * Real.cos p.2) 0 * max (u * p.1 * Real.cos p.2 + Real.sqrt (1 - u ^ 2) * p.1 * Real.sin p.2) 0 = if p.2 ∈ Set.Ioo (-Real.arcsin u) (Real.pi / 2) then p.1 ^ 2 * Real.cos p.2 * Real.sin (p.2 + Real.arcsin u) else 0 := by
    intro p hp
    have h_cos : max (p.1 * Real.cos p.2) 0 = if Real.cos p.2 > 0 then p.1 * Real.cos p.2 else 0 := by
      split_ifs <;> cases max_cases ( p.1 * Real.cos p.2 ) 0 <;> nlinarith [ hp.1.out ]
    have h_sin : max (u * p.1 * Real.cos p.2 + Real.sqrt (1 - u ^ 2) * p.1 * Real.sin p.2) 0 = if Real.sin (p.2 + Real.arcsin u) > 0 then p.1 * Real.sin (p.2 + Real.arcsin u) else 0 := by
      rw [ Real.sin_add, Real.sin_arcsin, Real.cos_arcsin ] <;> try linarith [ hu.1, hu.2 ];
      split_ifs <;> cases max_cases ( u * p.1 * Real.cos p.2 + Real.sqrt ( 1 - u ^ 2 ) * p.1 * Real.sin p.2 ) 0 <;> nlinarith [ hp.1.out ];
    have h_wedge : {θ : ℝ | θ ∈ Set.Ioo (-Real.pi) Real.pi ∧ 0 < Real.cos θ ∧ 0 < Real.sin (θ + Real.arcsin u)} = Set.Ioo (-Real.arcsin u) (Real.pi / 2) := by
      convert wedge_angle_set u hu using 1;
      ext θ; simp [Real.sin_add, Real.cos_arcsin];
      intro _ _ _; rw [ Real.sin_arcsin ] <;> try linarith [ hu.1, hu.2 ] ; ; ring;
    grind;
  -- Substitute the simplified integrand back into the integral.
  have h_integral : ∫ p in Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi, p.1 * (max (p.1 * Real.cos p.2) 0 * max (u * p.1 * Real.cos p.2 + Real.sqrt (1 - u ^ 2) * p.1 * Real.sin p.2) 0 * (1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2) / 2)) = ∫ p in Set.Ioi 0 ×ˢ Set.Ioo (-Real.arcsin u) (Real.pi / 2), p.1 ^ 3 * Real.cos p.2 * Real.sin (p.2 + Real.arcsin u) * (1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2) / 2) := by
    rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    · congr with x ; by_cases hx : 0 < x.1 <;> by_cases hx' : -Real.pi < x.2 ∧ x.2 < Real.pi <;> simp +decide [ hx, hx' ];
      · grind;
      · exact fun h₁ h₂ => False.elim <| hx' ⟨ by linarith [ Real.neg_pi_div_two_le_arcsin u, Real.arcsin_le_pi_div_two u ], by linarith [ Real.neg_pi_div_two_le_arcsin u, Real.arcsin_le_pi_div_two u ] ⟩;
    · exact measurableSet_Ioi.prod measurableSet_Ioo;
    · exact measurableSet_Ioi.prod measurableSet_Ioo;
  -- Split the integral into the product of two separate integrals.
  have h_split : ∫ p in Set.Ioi 0 ×ˢ Set.Ioo (-Real.arcsin u) (Real.pi / 2), p.1 ^ 3 * Real.cos p.2 * Real.sin (p.2 + Real.arcsin u) * (1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2) / 2) = (∫ r in Set.Ioi 0, r ^ 3 * Real.exp (-(r ^ 2) / 2)) * (∫ θ in Set.Ioo (-Real.arcsin u) (Real.pi / 2), Real.cos θ * Real.sin (θ + Real.arcsin u) * (1 / (2 * Real.pi))) := by
    erw [ ← MeasureTheory.setIntegral_prod_mul ];
    ac_rfl;
  rw [ h_polar, h_integral, h_split ];
  rw [ MeasureTheory.integral_mul_const, angular_pos_integral u hu ] ; norm_num [ radial_gaussian_integral_cube ] ; ring

/-
**Price's theorem (Lemma `lem:price`, first equality).** The derivative of the
positive-part covariance `g(u) = E[Z₁⁺ Z₂⁺]` equals the orthant probability value
`1/4 + arcsin(u)/(2π)`.
-/
theorem positivePartCov_hasDerivAt (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt positivePartCov (1 / 4 + Real.arcsin u / (2 * Real.pi)) u := by
  convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
  exact fun v => ( Real.sqrt ( 1 - v ^ 2 ) + ( Real.pi / 2 + Real.arcsin v ) * v ) / ( 2 * Real.pi );
  · convert HasDerivAt.div_const ( HasDerivAt.add ( HasDerivAt.sqrt ( HasDerivAt.const_sub _ <| hasDerivAt_pow 2 u ) _ ) <| HasDerivAt.mul ( HasDerivAt.add ( hasDerivAt_const _ _ ) <| Real.hasDerivAt_arcsin hu.1.ne' hu.2.ne ) <| hasDerivAt_id u ) _ using 1 <;> norm_num ; ring_nf;
    · norm_num [ Real.pi_ne_zero ] ; ring;
    · nlinarith [ hu.1, hu.2 ];
  · filter_upwards [ Ioo_mem_nhds hu.1 hu.2 ] with v hv using positivePartCov_eq v hv

/-- **Lemma `lem:price` (full statement, eq. `eq:price`).** Combining Price's theorem
and Sheppard's orthant formula: the derivative of the positive-part covariance
`g(u) = E[Z₁⁺ Z₂⁺]` equals the orthant probability `P(Z₁ > 0, Z₂ > 0) = orthantProb u`,
which in turn equals `1/4 + arcsin(u)/(2π)`. -/
theorem price_sheppard (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt positivePartCov (orthantProb u) u ∧
      orthantProb u = 1 / 4 + Real.arcsin u / (2 * Real.pi) := by
  refine ⟨?_, orthantProb_eq u hu⟩
  rw [orthantProb_eq u hu]
  exact positivePartCov_hasDerivAt u hu

/-!
## Literal Bessel–Struve closed form of `prop:struve` (DLMF 11.5.2)

The positive-part correlation `rhoStruve` is already proved in its integral form
`rhoStruveNum c = ∫₀¹ (π/2 + arcsin s) e^{-4cs} ds`.  Here we upgrade it to the
*literal* closed form of the paper,

  `Corr(G₁⁺,G₂⁺) = π/(8(π-1)c)·[1 - 2e^{-4c} + I₀(4c) - L₀(4c)]`,

with `I₀` the modified Bessel function and `L₀` the modified Struve function, both
defined here by their everywhere-convergent power series.  The analytic heart is the
DLMF 11.5.2 identity
  `∫₀^{π/2} e^{-a sinθ} dθ = (π/2)(I₀(a) - L₀(a))`.
-/

/-- The **modified Bessel function** of order `0`, `I₀(z) = ∑_{m≥0} (z/2)^{2m}/(m!)²`. -/
noncomputable def besselI0 (z : ℝ) : ℝ :=
  ∑' m : ℕ, (z / 2) ^ (2 * m) / (Nat.factorial m : ℝ) ^ 2

/-- The **modified Struve function** of order `0`,
`L₀(z) = ∑_{m≥0} (z/2)^{2m+1}/Γ(m+3/2)²`. -/
noncomputable def struveL0 (z : ℝ) : ℝ :=
  ∑' m : ℕ, (z / 2) ^ (2 * m + 1) / (Real.Gamma (m + 3 / 2)) ^ 2

/-
The half-range sine-power integral is half of the full-range one (symmetry about
`π/2`).
-/
lemma integral_sin_pow_half (k : ℕ) :
    (∫ θ in (0:ℝ)..(Real.pi / 2), Real.sin θ ^ k)
      = (1 / 2) * ∫ θ in (0:ℝ)..Real.pi, Real.sin θ ^ k := by
  have h_split : ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ k = (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ ^ k) + (∫ θ in (Real.pi / 2)..Real.pi, Real.sin θ ^ k) := by
    rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> exact Continuous.intervalIntegrable ( by continuity ) _ _;
  rw [ h_split ] ; rw [ show ( ∫ θ in ( Real.pi / 2 )..Real.pi, Real.sin θ ^ k ) = ( ∫ θ in ( 0 : ℝ ).. ( Real.pi / 2 ), Real.sin θ ^ k ) by convert intervalIntegral.integral_comp_sub_left _ π using 2 <;> norm_num ; ring ] ; ring;

/-
Wallis integral, even case (on `[0,π/2]`):
`∫₀^{π/2} sin^{2m}θ dθ = (π/2)·(2m)!/(4^m (m!)²)`.
-/
lemma integral_sin_pow_half_even (m : ℕ) :
    (∫ θ in (0:ℝ)..(Real.pi / 2), Real.sin θ ^ (2 * m))
      = Real.pi / 2 * (Nat.factorial (2 * m) : ℝ) / (4 ^ m * (Nat.factorial m : ℝ) ^ 2) := by
  induction m <;> simp_all +decide [ Nat.mul_succ, integral_sin_pow ];
  field_simp;
  simpa [ Nat.factorial, pow_succ' ] using by ring;

/-
Wallis integral, odd case (on `[0,π/2]`):
`∫₀^{π/2} sin^{2m+1}θ dθ = 4^m (m!)²/(2m+1)!`.
-/
lemma integral_sin_pow_half_odd (m : ℕ) :
    (∫ θ in (0:ℝ)..(Real.pi / 2), Real.sin θ ^ (2 * m + 1))
      = (4 ^ m * (Nat.factorial m : ℝ) ^ 2) / (Nat.factorial (2 * m + 1) : ℝ) := by
  induction' m with m ih;
  · norm_num;
  · simp_all +decide [ Nat.mul_succ, integral_sin_pow ];
    rw [ div_mul_div_comm, div_eq_div_iff ] <;> first | positivity | push_cast [ Nat.factorial_succ, pow_succ' ] ; ring;

/-
Closed form of the squared half-integer Gamma value:
`Γ(m+3/2)² = π·((2m+1)!)²/(4^{2m+1}(m!)²)`.
-/
lemma gamma_add_three_half_sq (m : ℕ) :
    (Real.Gamma (m + 3 / 2)) ^ 2
      = Real.pi * (Nat.factorial (2 * m + 1) : ℝ) ^ 2 / (4 ^ (2 * m + 1) * (Nat.factorial m : ℝ) ^ 2) := by
  -- By definition of the Gamma function, we know that $\Gamma(m + 3/2) = \frac{(2m+1)!}{2^{2m+1} m!} \sqrt{\pi}$.
  have h_gamma_def : Real.Gamma (m + 3 / 2) = (Nat.factorial (2 * m + 1) : ℝ) / (2 ^ (2 * m + 1) * (Nat.factorial m : ℝ)) * Real.sqrt Real.pi := by
    induction' m with m ih;
    · convert congr_arg ( ( ↑ ) : ℝ → ℂ ) ( Real.Gamma_one_half_eq ) using 1 ; norm_num;
      rw [ show ( 3 / 2 : ℝ ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one ( by norm_num ), mul_comm ] ; norm_num;
      grind +qlia;
    · convert congr_arg ( fun x : ℝ => x * ( m + 1 + 3 / 2 - 1 ) ) ih using 1 <;> push_cast [ Nat.factorial_succ, pow_succ' ] <;> ring;
      · rw [ show ( 5 / 2 + m : ℝ ) = ( 3 / 2 + m ) + 1 by ring, Real.Gamma_add_one ( by positivity ) ] ; ring;
      · field_simp;
        norm_num [ Nat.add_comm 2, Nat.factorial_succ, pow_mul' ] ; ring;
        norm_num [ mul_assoc, ← mul_pow ];
  rw [ h_gamma_def, mul_pow, Real.sq_sqrt <| by positivity ] ; ring ; norm_num [ pow_mul', ← mul_pow ] ; ring;

/-
The even summand of `∫₀^{π/2} e^{-a sinθ}dθ` is the `m`-th term of `(π/2)·I₀(a)`.
-/
lemma besselI0_summand (a : ℝ) (m : ℕ) :
    (-a) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)
        * (∫ θ in (0:ℝ)..(Real.pi / 2), Real.sin θ ^ (2 * m))
      = Real.pi / 2 * ((a / 2) ^ (2 * m) / (Nat.factorial m : ℝ) ^ 2) := by
  rw [ integral_sin_pow_half_even m ];
  field_simp;
  norm_num [ pow_mul, ← mul_pow ] ; ring

/-
The odd summand of `∫₀^{π/2} e^{-a sinθ}dθ` is the `m`-th term of `-(π/2)·L₀(a)`.
-/
lemma struveL0_summand (a : ℝ) (m : ℕ) :
    (-a) ^ (2 * m + 1) / (Nat.factorial (2 * m + 1) : ℝ)
        * (∫ θ in (0:ℝ)..(Real.pi / 2), Real.sin θ ^ (2 * m + 1))
      = -(Real.pi / 2) * ((a / 2) ^ (2 * m + 1) / (Real.Gamma (m + 3 / 2)) ^ 2) := by
  rw [ integral_sin_pow_half_odd ];
  rw [ gamma_add_three_half_sq ] ; ring;
  norm_num [ pow_mul', Real.pi_ne_zero ] ; ring;
  norm_num only [ mul_assoc, ← mul_pow ]

/-
The Bessel `I₀` series is summable.
-/
lemma besselI0_summable (a : ℝ) :
    Summable (fun m : ℕ => (a / 2) ^ (2 * m) / (Nat.factorial m : ℝ) ^ 2) := by
  norm_num [ pow_mul ];
  exact Summable.of_nonneg_of_le ( fun m => by positivity ) ( fun m => by gcongr ; norm_cast ; nlinarith [ Nat.factorial_pos m ] ) ( Real.summable_pow_div_factorial _ )

/-
The Struve `L₀` series is summable.
-/
lemma struveL0_summable (a : ℝ) :
    Summable (fun m : ℕ => (a / 2) ^ (2 * m + 1) / (Real.Gamma (m + 3 / 2)) ^ 2) := by
  refine' summable_of_ratio_norm_eventually_le _ _;
  exact 1 / 2;
  · norm_num;
  · -- We'll use the fact that |a/2|²·16·(m+1)²/((2m+2)(2m+3))² → 0 as m→∞.
    have h_ratio : Filter.Tendsto (fun m : ℕ => |a / 2| ^ 2 * 16 * (m + 1) ^ 2 / ((2 * m + 2) * (2 * m + 3)) ^ 2) Filter.atTop (nhds 0) := by
      refine' squeeze_zero_norm' _ _;
      use fun n => |a / 2| ^ 2 * 16 / ( n + 1 );
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ div_le_div_iff₀ ] <;> first | positivity | exact le_of_sub_nonneg ( by ring_nf; positivity ) ;
      · exact tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
    filter_upwards [ h_ratio.eventually ( gt_mem_nhds <| show 0 < 1 / 2 by norm_num ) ] with m hm ; norm_num [ abs_div, abs_mul, abs_of_nonneg, Real.Gamma_pos_of_pos, add_nonneg ] at hm ⊢;
    convert mul_le_mul_of_nonneg_right hm.le ( show 0 ≤ ( |a| / 2 ) ^ ( 2 * m + 1 ) / Real.Gamma ( m + 3 / 2 ) ^ 2 by positivity ) using 1 ; ring;
    rw [ show ( 5 / 2 + m : ℝ ) = ( 3 / 2 + m ) + 1 by ring, Real.Gamma_add_one ( by positivity ) ] ; ring;
    -- Combine and simplify the terms on the right-hand side.
    field_simp
    ring

/-
Term-by-term integration of the exponential series against the sine powers.
-/
lemma integral_exp_neg_mul_sin_tsum (a : ℝ) :
    (∫ θ in (0:ℝ)..(Real.pi / 2), Real.exp (-a * Real.sin θ))
      = ∑' n : ℕ, (-a) ^ n / (Nat.factorial n : ℝ)
          * (∫ θ in (0:ℝ)..(Real.pi / 2), Real.sin θ ^ n) := by
  -- By Fubini's theorem, we can interchange the sum and the integral.
  have h_fubini : ∫ θ in (0:ℝ)..(Real.pi / 2), ∑' n, ((-a) ^ n / (Nat.factorial n)) * (Real.sin θ) ^ n = ∑' n, ((-a) ^ n / (Nat.factorial n)) * ∫ θ in (0:ℝ)..(Real.pi / 2), (Real.sin θ) ^ n := by
    rw [ intervalIntegral.integral_of_le Real.pi_div_two_pos.le, MeasureTheory.integral_tsum ];
    · norm_num [ ← intervalIntegral.integral_of_le Real.pi_div_two_pos.le ];
    · exact fun i => Continuous.aestronglyMeasurable ( by continuity );
    · refine' ne_of_lt ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum fun n => _ ) _ );
      use fun n => ENNReal.ofReal ( |a|^n / ( n.factorial : ℝ ) * ( Real.pi / 2 ) );
      · refine' le_trans ( MeasureTheory.lintegral_mono fun x => _ ) _;
        use fun x => ENNReal.ofReal ( |a|^n / ( n.factorial : ℝ ) );
        · rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num;
          · exact mul_le_of_le_one_right ( by positivity ) ( pow_le_one₀ ( abs_nonneg _ ) ( Real.abs_sin_le_one _ ) );
          · finiteness;
          · positivity;
        · simp +decide [ mul_comm, Real.pi_div_two_pos.le ];
          rw [ ← ENNReal.ofReal_mul ( by positivity ) ];
      · rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num;
        · exact fun n => by positivity;
        · exact Summable.mul_right _ <| Real.summable_pow_div_factorial _;
  convert h_fubini using 3 ; rw [ Real.exp_eq_exp_ℝ ] ; rw [ NormedSpace.exp_eq_tsum_div ] ; ring;

/-
**DLMF 11.5.2.** `∫₀^{π/2} e^{-a sinθ} dθ = (π/2)(I₀(a) - L₀(a))`.
-/
lemma integral_exp_neg_mul_sin_eq (a : ℝ) :
    (∫ θ in (0:ℝ)..(Real.pi / 2), Real.exp (-a * Real.sin θ))
      = Real.pi / 2 * (besselI0 a - struveL0 a) := by
  have h_tsum_even_add_odd : ∑' k : ℕ, (-a) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) * (∫ θ in (0:ℝ)..(Real.pi / 2), Real.sin θ ^ (2 * k)) + ∑' k : ℕ, (-a) ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ) * (∫ θ in (0:ℝ)..(Real.pi / 2), Real.sin θ ^ (2 * k + 1)) = ∑' k : ℕ, (-a) ^ k / (Nat.factorial k : ℝ) * (∫ θ in (0:ℝ)..(Real.pi / 2), Real.sin θ ^ k) := by
    rw [ eq_comm, ← tsum_even_add_odd ];
    · convert besselI0_summable a |> Summable.mul_left ( Real.pi / 2 ) using 1;
      exact funext fun n => besselI0_summand a n ▸ by ring;
    · have := struveL0_summable a;
      convert this.mul_left ( - ( Real.pi / 2 ) ) using 2 ; norm_num [ struveL0_summand ];
  rw [ integral_exp_neg_mul_sin_tsum, ← h_tsum_even_add_odd ];
  rw [ tsum_congr fun k => besselI0_summand a k, tsum_congr fun k => struveL0_summand a k ];
  norm_num [ tsum_neg, tsum_mul_left, besselI0, struveL0 ] ; ring

/-
Substituting `s = sin θ` turns `rhoStruveNum` into a smooth `θ`-integral.
-/
lemma rhoStruveNum_eq_sin_integral (c : ℝ) :
    rhoStruveNum c
      = ∫ θ in (0:ℝ)..(Real.pi / 2),
          (Real.pi / 2 + θ) * Real.cos θ * Real.exp (-(4 * c) * Real.sin θ) := by
  rw [ intervalIntegral.integral_eq_sub_of_hasDeriv_right ];
  rotate_right;
  use fun x => ∫ s in ( 0 : ℝ )..Real.sin x, ( Real.pi / 2 + Real.arcsin s ) * Real.exp ( - ( 4 * c ) * s );
  · norm_num [ rhoStruveNum ];
  · fun_prop;
  · intro x hx
    have h_deriv : HasDerivAt (fun x => ∫ s in (0:ℝ)..x, (Real.pi / 2 + Real.arcsin s) * Real.exp (-(4 * c) * s)) ((Real.pi / 2 + Real.arcsin (Real.sin x)) * Real.exp (-(4 * c) * Real.sin x)) (Real.sin x) := by
      apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
      · exact Continuous.intervalIntegrable ( by continuity ) _ _;
      · exact Continuous.stronglyMeasurable ( by continuity ) |> fun h => h.stronglyMeasurableAtFilter;
      · exact ContinuousAt.mul ( ContinuousAt.add continuousAt_const ( Real.continuous_arcsin.continuousAt ) ) ( ContinuousAt.rexp ( ContinuousAt.mul continuousAt_const continuousAt_id ) );
    convert HasDerivAt.hasDerivWithinAt ( h_deriv.comp x ( Real.hasDerivAt_sin x ) ) using 1 ; ring;
    rw [ Real.arcsin_sin ] <;> cases max_cases ( 0 : ℝ ) ( Real.pi / 2 ) <;> cases min_cases ( 0 : ℝ ) ( Real.pi / 2 ) <;> linarith [ hx.1, hx.2, Real.pi_pos ];
  · exact Continuous.intervalIntegrable ( by continuity ) _ _

/-
After substitution and integration by parts, `rhoStruveNum` is expressed through the
bridge integral `K(4c) = ∫₀^{π/2} e^{-4c sinθ}dθ`.
-/
lemma rhoStruveNum_eq_K (c : ℝ) (hc : 0 < c) :
    rhoStruveNum c
      = (1 / (4 * c)) * (Real.pi / 2 - Real.pi * Real.exp (-(4 * c))
          + ∫ θ in (0:ℝ)..(Real.pi / 2), Real.exp (-(4 * c) * Real.sin θ)) := by
  -- Apply integration by parts with $u = \frac{\pi}{2} + \theta$ and $dv = \cos \theta \cdot \exp(-(4c) \sin \theta) \, d\theta$.
  have h_parts : ∀ a b : ℝ, ∫ x in a..b, (Real.pi / 2 + x) * Real.cos x * Real.exp (-(4 * c) * Real.sin x) =
    (Real.pi / 2 + b) * (-1 / (4 * c)) * Real.exp (-(4 * c) * Real.sin b) -
    (Real.pi / 2 + a) * (-1 / (4 * c)) * Real.exp (-(4 * c) * Real.sin a) -
    ∫ x in a..b, (-1 / (4 * c)) * Real.exp (-(4 * c) * Real.sin x) := by
      intro a b; rw [ eq_sub_iff_add_eq ] ; rw [ ← intervalIntegral.integral_add ] ; rw [ intervalIntegral.integral_deriv_eq_sub' ];
      · ext; norm_num [ Real.differentiableAt_sin, Real.differentiableAt_exp, add_mul, mul_assoc, mul_comm, mul_left_comm, hc.ne' ] ; ring;
        simpa [ mul_assoc, mul_comm c, hc.ne' ] using by ring;
      · fun_prop;
      · fun_prop;
      · exact Continuous.intervalIntegrable ( by continuity ) _ _;
      · exact Continuous.intervalIntegrable ( by continuity ) _ _;
  rw [ rhoStruveNum_eq_sin_integral, h_parts ] ; norm_num ; ring

/-- **Literal Bessel–Struve form of the numerator integral.** -/
theorem rhoStruveNum_bessel_struve (c : ℝ) (hc : 0 < c) :
    rhoStruveNum c
      = Real.pi / (8 * c) * (1 - 2 * Real.exp (-(4 * c)) + besselI0 (4 * c) - struveL0 (4 * c)) := by
  rw [rhoStruveNum_eq_K c hc, integral_exp_neg_mul_sin_eq (4 * c)]
  have hc' : (4 * c) ≠ 0 := by positivity
  field_simp
  ring

/-- **Proposition `prop:struve` (literal closed form).** The positive-part correlation
of the limiting mixture equals
`π/(8(π-1)c)·[1 - 2e^{-4c} + I₀(4c) - L₀(4c)]`, with `I₀` the modified Bessel and `L₀`
the modified Struve function. -/
theorem rhoStruve_bessel_struve (c : ℝ) (hc : 0 < c) :
    rhoStruve c
      = Real.pi / (8 * (Real.pi - 1) * c)
          * (1 - 2 * Real.exp (-(4 * c)) + besselI0 (4 * c) - struveL0 (4 * c)) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rw [rhoStruve, rhoStruveNum_bessel_struve c hc]
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  have hc' : c ≠ 0 := ne_of_gt hc
  have hpi1 : Real.pi - 1 ≠ 0 := by nlinarith [Real.pi_gt_three]
  field_simp

/-!
## Exact symmetry identities (Lemma `lem:occ`, eq. `eq:symm`)

Species-interchange symmetry maps `R ↦ -R`, `S ↦ S` and fixes the law of the process.
We abstract this as the invariance of the *joint law* of `(X₁,X₂)` under swapping the
two coordinates, and derive the two exact identities used in the proof of
`thm:closed`: the difference `R = X₂ - X₁` has mean zero, and the sum and difference are
uncorrelated, `Cov(S,R) = 0`.
-/

/-
Under species-interchange symmetry (invariance of the joint law of `(X₁,X₂)` under
swapping coordinates), the two species have equal means.
-/
lemma occ_mean_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X1 X2 : Ω → ℝ}
    (h1 : MemLp X1 2 μ) (h2 : MemLp X2 2 μ)
    (hsymm : Measure.map (fun ω => (X1 ω, X2 ω)) μ
      = Measure.map (fun ω => (X2 ω, X1 ω)) μ) :
    ∫ ω, X1 ω ∂μ = ∫ ω, X2 ω ∂μ := by
  convert congr_arg ( fun m => ∫ p : ℝ × ℝ, p.1 ∂m ) hsymm using 1;
  · rw [ MeasureTheory.integral_map ];
    · exact h1.1.aemeasurable.prodMk h2.1.aemeasurable;
    · exact measurable_fst.aestronglyMeasurable;
  · rw [ MeasureTheory.integral_map ];
    · exact h2.aestronglyMeasurable.aemeasurable.prodMk h1.aestronglyMeasurable.aemeasurable;
    · exact measurable_fst.aestronglyMeasurable

/-
Under species-interchange symmetry, the two species have equal variances.
-/
lemma occ_var_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X1 X2 : Ω → ℝ}
    (h1 : MemLp X1 2 μ) (h2 : MemLp X2 2 μ)
    (hsymm : Measure.map (fun ω => (X1 ω, X2 ω)) μ
      = Measure.map (fun ω => (X2 ω, X1 ω)) μ) :
    Var[X1; μ] = Var[X2; μ] := by
  have h_var : Var[fun ω => ω.1; Measure.map (fun ω => (X1 ω, X2 ω)) μ] = Var[fun ω => ω.1; Measure.map (fun ω => (X2 ω, X1 ω)) μ] := by
    rw [hsymm];
  convert h_var using 1;
  · rw [ ProbabilityTheory.variance_map ];
    · rfl;
    · exact measurable_fst.aemeasurable;
    · exact h1.1.aemeasurable.prodMk h2.1.aemeasurable;
  · rw [ ProbabilityTheory.variance_map ];
    · rfl;
    · exact measurable_fst.aemeasurable;
    · exact h2.1.aemeasurable.prodMk h1.1.aemeasurable

/-
**Lemma `lem:occ`, eq. `eq:symm`.** Species-interchange symmetry gives the exact
identities `E[R] = 0` and `Cov(S,R) = 0` for the sum `S = X₁+X₂` and difference
`R = X₂-X₁`.
-/
lemma occ_symmetry {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X1 X2 : Ω → ℝ}
    (h1 : MemLp X1 2 μ) (h2 : MemLp X2 2 μ)
    (hsymm : Measure.map (fun ω => (X1 ω, X2 ω)) μ
      = Measure.map (fun ω => (X2 ω, X1 ω)) μ) :
    (∫ ω, (X2 ω - X1 ω) ∂μ = 0) ∧
      cov[fun ω => X1 ω + X2 ω, fun ω => X2 ω - X1 ω; μ] = 0 := by
  constructor;
  · rw [ MeasureTheory.integral_sub ( h2.integrable one_le_two ) ( h1.integrable one_le_two ) ];
    rw [ sub_eq_zero, occ_mean_eq h1 h2 hsymm ];
  · have h_var_eq : ProbabilityTheory.variance X1 μ = ProbabilityTheory.variance X2 μ := by
      convert occ_var_eq h1 h2 hsymm using 1;
    have h_cov_eq : ProbabilityTheory.covariance X1 X2 μ = ProbabilityTheory.covariance X2 X1 μ := by
      rw [ ProbabilityTheory.covariance_comm ];
    have h_cov_expand : ProbabilityTheory.covariance (fun ω => X1 ω + X2 ω) (fun ω => X2 ω - X1 ω) μ = ProbabilityTheory.covariance X1 X2 μ - ProbabilityTheory.covariance X1 X1 μ + ProbabilityTheory.covariance X2 X2 μ - ProbabilityTheory.covariance X2 X1 μ := by
      have h_cov_expand : ProbabilityTheory.covariance (fun ω => X1 ω + X2 ω) (fun ω => X2 ω - X1 ω) μ = ProbabilityTheory.covariance X1 (fun ω => X2 ω - X1 ω) μ + ProbabilityTheory.covariance X2 (fun ω => X2 ω - X1 ω) μ := by
        apply_rules [ ProbabilityTheory.covariance_add_left ];
        exact h2.sub h1;
      have h_cov_expand : ProbabilityTheory.covariance X1 (fun ω => X2 ω - X1 ω) μ = ProbabilityTheory.covariance X1 X2 μ - ProbabilityTheory.covariance X1 X1 μ := by
        apply_rules [ ProbabilityTheory.covariance_sub_right ];
      have h_cov_expand : ProbabilityTheory.covariance X2 (fun ω => X2 ω - X1 ω) μ = ProbabilityTheory.covariance X2 X2 μ - ProbabilityTheory.covariance X2 X1 μ := by
        apply_rules [ ProbabilityTheory.covariance_sub_right ];
      linarith;
    simp_all +decide;
    rw [ ProbabilityTheory.covariance_self, ProbabilityTheory.covariance_self ] ; linarith!;
    · exact h2.1.aemeasurable;
    · exact h1.1.aemeasurable

/-!
## Split-time limits (Lemma `lem:split`)

While bound, the pair leaves the bound phase only through a split, whose holding time is
`τ ∼ Exp(ν_sp)` with split rate `ν_sp = 2q²ε`, `ε = 1-q²` and `q = 1 - c/T`.  The
exponential-time facts of `lem:split` reduce to the real-analytic limits below.
-/

/-- The split rate `ν_sp = 2q²ε` with `ε = 1-q²` and `q = 1 - c/T`. -/
noncomputable def splitRate (c T : ℝ) : ℝ :=
  2 * (1 - c / T) ^ 2 * (1 - (1 - c / T) ^ 2)

/-
**Lemma `lem:split`.** The scaled split rate converges: `ν_sp·T → 4c`.
-/
lemma splitRate_mul_tendsto (c : ℝ) :
    Filter.Tendsto (fun T => splitRate c T * T) Filter.atTop (nhds (4 * c)) := by
  -- First, simplify the expression inside the limit:
  suffices h_simp : Filter.Tendsto (fun T : ℝ => 2 * (1 - c / T)^2 * (2 * c - c^2 / T)) Filter.atTop (nhds (4 * c)) by
    refine h_simp.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT;
    unfold splitRate
    field_simp
    ring;
  exact le_trans ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( Filter.Tendsto.pow ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) _ ) ) ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ) ( by ring_nf; norm_num )

/-
**Lemma `lem:split`.** The survival probability `P(τ > T) = e^{-ν_sp·T} → e^{-4c}`.
-/
lemma split_survival_tendsto (c : ℝ) :
    Filter.Tendsto (fun T => Real.exp (-(splitRate c T * T))) Filter.atTop
      (nhds (Real.exp (-(4 * c)))) := by
  exact Real.continuous_exp.continuousAt.tendsto.comp ( Filter.Tendsto.neg ( splitRate_mul_tendsto c ) )

/-
**Lemma `lem:split`.** Convergence in distribution of `τ/T` to `Exp(4c)` at the
level of CDFs: for each `x`, `P(τ/T ≤ x) = 1 - e^{-ν_sp·T·x} → 1 - e^{-4cx}`, the CDF of
`Exp(4c)`.
-/
lemma split_cdf_tendsto (c x : ℝ) :
    Filter.Tendsto (fun T => 1 - Real.exp (-(splitRate c T * T * x))) Filter.atTop
      (nhds (1 - Real.exp (-(4 * c * x)))) := by
  -- Using the fact that `splitRate c T * T` tends to `4 * c`, we can show that `splitRate c T * T * x` tends to `4 * c * x`.
  have h_mul : Filter.Tendsto (fun T => splitRate c T * T * x) Filter.atTop (nhds (4 * c * x)) := by
    exact Filter.Tendsto.mul ( splitRate_mul_tendsto c ) tendsto_const_nhds;
  exact tendsto_const_nhds.sub ( Real.continuous_exp.continuousAt.tendsto.comp <| h_mul.neg )

/-
**Mixture-mean identity (bridging `lem:split` and `thm:closed`).**  The mean of the
limiting split fraction `U = min(Exp(4c), 1)` equals the crossover correlation `ρ(c)`.
With the `Exp(4c)` density `(4c)·e^{-4ct}` on `(0,∞)`,
`E[min(Exp(4c),1)] = ∫₀^∞ min(t,1)·(4c)·e^{-4ct} dt = (1-e^{-4c})/(4c) = ρ(c)`.
Together with the bivariate-normal mixture of `prop:twophase` (whose unconditional
correlation is `E[U]`), this is the probabilistic origin of `thm:closed`.
-/
lemma expMin_mean_eq_rhoCorr {c : ℝ} (hc : 0 < c) :
    ∫ t in Set.Ioi (0 : ℝ), min t 1 * (4 * c) * Real.exp (-(4 * c * t)) = rhoCorr c := by
  -- Split the integral into two parts: from 0 to 1 and from 1 to ∞.
  have h_split : ∫ t in Set.Ioi 0, min t 1 * (4 * c) * Real.exp (-(4 * c * t)) = (∫ t in Set.Ioc 0 1, t * (4 * c) * Real.exp (-(4 * c * t))) + (∫ t in Set.Ioi 1, (4 * c) * Real.exp (-(4 * c * t))) := by
    have h_split : (∫ t in Set.Ioi 0, min t 1 * (4 * c) * Real.exp (-(4 * c * t))) = (∫ t in Set.Ioc 0 1, min t 1 * (4 * c) * Real.exp (-(4 * c * t))) + (∫ t in Set.Ioi 1, min t 1 * (4 * c) * Real.exp (-(4 * c * t))) := by
      rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num;
      · exact Continuous.integrableOn_Ioc ( by apply_rules [ Continuous.mul, Continuous.min ] <;> continuity );
      · -- The integral of $e^{-4ct}$ over $(1, \infty)$ is convergent.
        have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-(4 * c * t))) (Set.Ioi 1) := by
          have := ( exp_neg_integrableOn_Ioi 0 ( by positivity : 0 < 4 * c ) );
          simpa only [ neg_mul ] using this.mono_set ( Set.Ioi_subset_Ioi zero_le_one );
        refine' h_integrable.const_mul ( 4 * c ) |> fun h => h.congr _;
        filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by rw [ min_eq_right ( by linarith [ hx.out ] ) ] ; ring;
    exact h_split.trans ( congrArg₂ ( · + · ) ( MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ min_eq_left hx.2 ] ) ( MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [ min_eq_right hx.out.le ] ; ring ) );
  -- Evaluate the first integral: $\int_{0}^{1} t \cdot 4c \cdot e^{-4ct} \, dt$.
  have h_first : ∫ t in Set.Ioc 0 1, t * (4 * c) * Real.exp (-(4 * c * t)) = (1 - (4 * c + 1) * Real.exp (-(4 * c))) / (4 * c) := by
    rw [ ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_deriv_eq_sub' ];
    case f => exact fun x => - ( x + 1 / ( 4 * c ) ) * Real.exp ( - ( 4 * c * x ) );
    · -- Simplify the expression for the first integral.
      field_simp
      ring;
      norm_num ; ring;
    · ext; norm_num [ mul_comm ] ; ring;
      norm_num [ mul_assoc, mul_comm c ] ; ring;
      grind +qlia;
    · fun_prop;
    · fun_prop;
  -- Evaluate the second integral: $\int_{1}^{\infty} 4c \cdot e^{-4ct} \, dt$.
  have h_second : ∫ t in Set.Ioi 1, (4 * c) * Real.exp (-(4 * c * t)) = Real.exp (-(4 * c)) := by
    have := integral_exp_neg_mul_rpow zero_lt_one ( show 0 < 4 * c by positivity );
    -- Use the fact that the integral of $e^{-4ct}$ over $(1, \infty)$ is the same as the integral over $(0, \infty)$ shifted by 1.
    have h_shift : ∫ t in Set.Ioi 1, Real.exp (-(4 * c * t)) = ∫ t in Set.Ioi 0, Real.exp (-(4 * c * (t + 1))) := by
      rw [ ← MeasureTheory.integral_indicator ( measurableSet_Ioi ), ← MeasureTheory.integral_indicator ( measurableSet_Ioi ) ];
      rw [ ← MeasureTheory.integral_add_right_eq_self _ 1 ] ; congr ; ext ; rw [ Set.indicator_apply, Set.indicator_apply ] ; aesop;
    simp_all +decide [ mul_add, Real.exp_add, MeasureTheory.integral_const_mul ];
    norm_num [ Real.rpow_neg_one, mul_assoc, mul_comm, mul_left_comm, hc.ne' ];
    ring;
  unfold rhoCorr; rw [ h_split, h_first, h_second ] ; ring; norm_num [ hc.ne' ] ;
  norm_num [ mul_comm c, hc.ne' ]

/-!
## Exact current decoupling: the rate tally (Proposition `prop:decouple`(a))

The macroscopic flux part (b) is `flux_cross_deriv`/`flux_cross_deriv2` above.  Here we
formalize the microscopic computation behind eq. `eq:jdecouple`: the species-1 transfer
rate across a bond is the *same in every species-2 background*, so the species-1 current
`j₁ = r_R η₁(1-η₁') - r_L (1-η₁)η₁'` does not depend on the species-2 occupancy, with
`r_R = q^{-1}β_n`, `r_L = q β_n`, `β_n = q^{1-2n}+q^{2n-1}`.  This is the finite-`n` rate
tally of the `16×16` generator (verified by computer algebra in the paper), here reduced
to Laurent-polynomial identities in `q` (with `q ≠ 0`).
-/

/-- `β_n = q^{1-2n} + q^{2n-1}` (the symmetric jump factor of eq. `eq:jdecouple`). -/
noncomputable def betaN (q : ℝ) (n : ℕ) : ℝ := q ^ (1 - 2 * (n : ℤ)) + q ^ (2 * (n : ℤ) - 1)

/-- `σ_n = (q^{n-1} - q^{1-n})²`. -/
noncomputable def sigmaN (q : ℝ) (n : ℕ) : ℝ := (q ^ ((n : ℤ) - 1) - q ^ (1 - (n : ℤ))) ^ 2

/-- Species-1 rightward transfer rate, species-2 background `(1,0)`. -/
noncomputable def rate1R_10 (q : ℝ) (n : ℕ) : ℝ := q ^ (-1 : ℤ) * betaN q n

/-- Species-1 rightward transfer rate, species-2 background `(3,0)`:
`q^{-2}σ_n + (q^{2n-2} - q^{2n-4} + 2q^{-2})`. -/
noncomputable def rate1R_30 (q : ℝ) (n : ℕ) : ℝ :=
  q ^ (-2 : ℤ) * sigmaN q n + (q ^ (2 * (n : ℤ) - 2) - q ^ (2 * (n : ℤ) - 4) + 2 * q ^ (-2 : ℤ))

/-- Species-1 rightward transfer rate, species-2 background `(1,2)`:
`(2 + q^{-2n}(1-q²)) + σ_n`. -/
noncomputable def rate1R_12 (q : ℝ) (n : ℕ) : ℝ :=
  (2 + q ^ (-2 * (n : ℤ)) * (1 - q ^ 2)) + sigmaN q n

/-- Species-1 rightward transfer rate, species-2 background `(3,2)`. -/
noncomputable def rate1R_32 (q : ℝ) (n : ℕ) : ℝ := q ^ (-1 : ℤ) * betaN q n

/-- Species-1 leftward transfer rate, species-2 background `(0,3)`:
`q²σ_n + (2q² + q^{2-2n} - q^{4-2n})`. -/
noncomputable def rate1L_03 (q : ℝ) (n : ℕ) : ℝ :=
  q ^ 2 * sigmaN q n + (2 * q ^ 2 + q ^ (2 - 2 * (n : ℤ)) - q ^ (4 - 2 * (n : ℤ)))

/-- Species-1 leftward transfer rate, species-2 background `(2,1)`:
`σ_n + (2 - q^{2n-2}(1-q²))`. -/
noncomputable def rate1L_21 (q : ℝ) (n : ℕ) : ℝ :=
  sigmaN q n + (2 - q ^ (2 * (n : ℤ) - 2) * (1 - q ^ 2))

/-
The rightward rate in background `(3,0)` equals `q^{-1}β_n`.
-/
lemma rate1R_30_eq (q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    rate1R_30 q n = q ^ (-1 : ℤ) * betaN q n := by
  -- Unfold the definitions of `rate1R_30`, `betaN`, and `sigmaN`.
  unfold rate1R_30 betaN sigmaN;
  norm_num [ zpow_sub₀ hq, zpow_add₀ hq ] ; ring;
  norm_cast ; simp +decide [ hq, pow_mul', mul_assoc, mul_comm, mul_left_comm ] ; ring

/-
The rightward rate in background `(1,2)` equals `q^{-1}β_n`.
-/
lemma rate1R_12_eq (q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    rate1R_12 q n = q ^ (-1 : ℤ) * betaN q n := by
  unfold rate1R_12 betaN sigmaN;
  norm_num [ zpow_sub₀ hq, zpow_add₀ hq ] ; ring;
  norm_cast ; simp +decide [ hq, pow_mul', mul_assoc, mul_comm q ] ; ring

/-
The leftward rate in background `(0,3)` equals `qβ_n`.
-/
lemma rate1L_03_eq (q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    rate1L_03 q n = q * betaN q n := by
  unfold rate1L_03 betaN sigmaN;
  norm_num [ zpow_sub₀ hq, zpow_add₀ hq ] ; ring;
  norm_cast ; simp +decide [ hq, pow_mul', mul_assoc, mul_comm, mul_left_comm ] ; ring;
  grind

/-
The leftward rate in background `(2,1)` equals `qβ_n`.
-/
lemma rate1L_21_eq (q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    rate1L_21 q n = q * betaN q n := by
  unfold rate1L_21 betaN sigmaN;
  norm_num [ zpow_sub₀ hq, zpow_add₀ hq ] ; ring;
  norm_cast ; simpa [ *, sq, mul_assoc, mul_comm q ] using by ring;

/-- **Proposition `prop:decouple`(a) (rate decoupling).** The microscopic species-1
rightward transfer rate is the same value `q^{-1}β_n` in *every* species-2 background
`(1,0),(3,0),(1,2),(3,2)`, and the leftward rate is the same value `qβ_n` in every
background `(0,3),(2,1)`.  Hence the species-1 current `j₁` is independent of the
species-2 occupancy: it is an autonomous single-species ASEP current with rates
`r_R = q^{-1}β_n`, `r_L = qβ_n`.

**Every-`n` coverage.**  This encodes the four rightward and two of the leftward
background identities for a fixed `n : ℕ`.  The file `TypeDDecouplingFiniteN.lean` gives the
complete every-`n` (indeed real `q^n`) form: the two real parameters `q, r` with `r` playing
the role of `q^n` turn every rate into a Laurent polynomial in `(q, r)`, all eight
per-background tallies become `ring`-provable identities
(`TypeDDecouplingFiniteN.current_decoupling_finiteN`), and the specialization `r = q^n`
reproduces the definitions here (`TypeDDecouplingFiniteN.betaR_eq_betaN`,
`TypeDDecouplingFiniteN.rate1R_10_specialize`).  That file also machine-checks the exact
`q^{2n}=r²`-rescaled decompositions with their `n → ∞` limits (`eq:rates`), rate
nonnegativity for `n ≥ 1`, and the `rem:range` continuation threshold — discharging the
paper's computer-algebra verification on the `16×16` generator (§1.1, §3). -/
theorem current_decoupling (q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    (rate1R_10 q n = q ^ (-1 : ℤ) * betaN q n ∧ rate1R_30 q n = q ^ (-1 : ℤ) * betaN q n ∧
        rate1R_12 q n = q ^ (-1 : ℤ) * betaN q n ∧ rate1R_32 q n = q ^ (-1 : ℤ) * betaN q n) ∧
      (rate1L_03 q n = q * betaN q n ∧ rate1L_21 q n = q * betaN q n) := by
  refine ⟨⟨rfl, rate1R_30_eq q hq n, rate1R_12_eq q hq n, rfl⟩,
    rate1L_03_eq q hq n, rate1L_21_eq q hq n⟩

/-- **The `q`-telescope identity (eq. `eq:telescope`), underlying Theorem `thm:cov`.**
With `N⁺_{a+1} = m` and the single-site occupation `e ∈ {0,1}`, so that
`N⁺_a = N⁺_{a+1} + e` and the `q`-deformed right-counts are `q^{2N⁺_{a+1}} = q^{2m}` and
`q^{2N⁺_a} = q^{2(m+e)}`, the increment telescopes as
`q^{2N⁺_{a+1}} - q^{2N⁺_a} = (1-q²)·e·q^{2N⁺_{a+1}}`. -/
lemma q_telescope (q : ℝ) (m e : ℕ) (he : e = 0 ∨ e = 1) :
    q ^ (2 * m) - q ^ (2 * (m + e)) = (1 - q ^ 2) * (e : ℝ) * q ^ (2 * m) := by
  rcases he with h | h <;> subst h <;> push_cast <;> ring

end TypeDDecoupling

/-
**Half-line telescoping sum (algebraic core of `eq:qmom`/`eq:qcov`).**
Given the `q`-deformed right-counts `q^{2N⁺_a}` of a right-finite configuration, where
`N⁺ : ℕ → ℕ` decrements by `0` or `1` at each step (`N⁺_a - N⁺_{a+1} = η_a ∈ {0,1}`) and
vanishes beyond `K`, summing the local telescope `eq:telescope` over the half-line `a ≥ m`
collapses to `1 - q^{2N⁺_m}`.  This is the identity used (with the duality identities
`eq:tri1`/`eq:tri2`) to pass from `q_telescope` to the exact contact representation of
Theorem `thm:cov`.
-/
lemma q_telescope_sum (q : ℝ) (Np : ℕ → ℕ) (K : ℕ)
    (hmono : ∀ a, Np (a + 1) ≤ Np a ∧ Np a ≤ Np (a + 1) + 1)
    (hzero : ∀ a, K ≤ a → Np a = 0) (m : ℕ) (hm : m ≤ K) :
    ∑ a ∈ Finset.Ico m K,
        (1 - q ^ 2) * ((Np a - Np (a + 1) : ℕ) : ℝ) * q ^ (2 * Np (a + 1))
      = 1 - q ^ (2 * Np m) := by
  -- Apply the telescoping sum lemma to simplify the expression.
  have h_telescope : ∑ a ∈ Finset.Ico m K, (1 - q ^ 2) * ((Np a - Np (a + 1) : ℤ) : ℝ) * q ^ (2 * Np (a + 1)) = ∑ a ∈ Finset.Ico m K, (q ^ (2 * Np (a + 1)) - q ^ (2 * Np a)) := by
    apply Finset.sum_congr rfl;
    intro a ha; specialize hmono a; rcases hmono with ⟨ h₁, h₂ ⟩ ; rcases h₂.eq_or_lt with h₂ | h₂ <;> simp_all +decide ; ring;
    grind +splitImp;
  have h_telescope_sum : ∑ a ∈ Finset.Ico m K, (q ^ (2 * (Np (a + 1))) - q ^ (2 * (Np a))) = q ^ (2 * (Np K)) - q ^ (2 * (Np m)) := by
    erw [ Finset.sum_Ico_eq_sum_range ];
    convert Finset.sum_range_sub ( fun x => q ^ ( 2 * Np ( m + x ) ) ) ( K - m ) using 1 ; simp +decide [ hm ];
  simp_all +decide [ Nat.cast_sub ( hmono _ |>.1 ) ]
namespace TypeDDecoupling

/-!
## `thm:cov` contact representation: the product expansion and covariance bound

This section completes the remaining elementary algebra of the `q`-Laplace contact
representation Theorem `thm:cov` (`eq:qcov`).  Two ingredients are needed beyond the
half-line telescope already established (`q_telescope`, `q_telescope_sum`):

* the **product expansion** that turns the double `q`-telescope
  `E[(1-q^{2N₁})(1-q^{2N₂})]` and the two marginal identities `eq:qmom` into the
  *connected* pair kernel `C_s(a,b) = P_{(a,b)}(…) - P_a(…)·P_b(…)` of `eq:qcov`
  (`cov_one_sub_one_sub` for the covariance shift, `q_cov_product_expansion` for the
  algebra), and
* the final **`[0,1]`-valued covariance bound** `|Cov(U,V)| ≤ min(E U, E V)`
  (`covariance_abs_le_min_integral`), which is the step giving
  `|Cov(q^{2N₁}, q^{2N₂})| ≤ E[q^{2N₁}] → 0`.
-/

/-- **Product expansion (algebraic core of `eq:qcov`).**  Expanding the double
`q`-telescope and subtracting the two marginal identities `eq:qmom` collapses the joint
pair kernel `Pj` minus the product of marginals `Pm` into the *connected* pair kernel.
With weights `w a = q^{-2a}` and `Pj a b = P_{(a,b)}(X₁≤0,X₂≤0)`, `Pm a = P_a(X≤0)`,
the left-hand side is exactly `Cov(q^{2N₁}, q^{2N₂})` and the right-hand side is
`(1-q²)² ∑_{a,b} q^{-2(a+b)} C_s(a,b)` of `eq:qcov`. -/
lemma q_cov_product_expansion (q : ℝ) (s t : Finset ℕ) (w : ℕ → ℝ)
    (Pm : ℕ → ℝ) (Pj : ℕ → ℕ → ℝ) :
    (1 - q ^ 2) ^ 2 * (∑ a ∈ s, ∑ b ∈ t, w a * w b * Pj a b)
      - ((1 - q ^ 2) * ∑ a ∈ s, w a * Pm a)
          * ((1 - q ^ 2) * ∑ b ∈ t, w b * Pm b)
      = (1 - q ^ 2) ^ 2
          * ∑ a ∈ s, ∑ b ∈ t, w a * w b * (Pj a b - Pm a * Pm b) := by
  have hprod : (∑ a ∈ s, w a * Pm a) * (∑ b ∈ t, w b * Pm b)
      = ∑ a ∈ s, ∑ b ∈ t, w a * w b * (Pm a * Pm b) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
  rw [show ((1 - q ^ 2) * ∑ a ∈ s, w a * Pm a) * ((1 - q ^ 2) * ∑ b ∈ t, w b * Pm b)
      = (1 - q ^ 2) ^ 2 * ((∑ a ∈ s, w a * Pm a) * (∑ b ∈ t, w b * Pm b)) by ring,
      hprod, ← mul_sub, ← Finset.sum_sub_distrib]
  apply congrArg; apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro b _; ring

/-- Covariance is invariant under reflecting both arguments through `1`:
`Cov(1 - X, 1 - Y) = Cov(X, Y)`.  This is the step in the proof of `thm:cov` that turns
the double `q`-telescope `E[(1-q^{2N₁})(1-q^{2N₂})]` into the covariance
`Cov(q^{2N₁}, q^{2N₂})`. -/
lemma cov_one_sub_one_sub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    cov[fun ω => 1 - X ω, fun ω => 1 - Y ω; μ] = cov[X, Y; μ] := by
  rw [covariance_const_sub_left hX 1, covariance_const_sub_right hY 1, neg_neg]

/-- **The `[0,1]`-valued covariance bound (final step of `thm:cov`).**  For random
variables `U, V` taking values in `[0,1]` on a probability space,
`|Cov(U,V)| ≤ min(E U, E V)`.  Applied to `U = q^{2N₁}`, `V = q^{2N₂}` (both in `[0,1]`)
this yields `|Cov(q^{2N₁}, q^{2N₂})| ≤ E[q^{2N₁}]`, which tends to `0`. -/
lemma covariance_abs_le_min_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {U V : Ω → ℝ}
    (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (hU0 : 0 ≤ᵐ[μ] U) (hU1 : U ≤ᵐ[μ] 1) (hV0 : 0 ≤ᵐ[μ] V) (hV1 : V ≤ᵐ[μ] 1) :
    |cov[U, V; μ]| ≤ min (∫ ω, U ω ∂μ) (∫ ω, V ω ∂μ) := by
  have hUi : Integrable U μ := hU.integrable one_le_two
  have hVi : Integrable V μ := hV.integrable one_le_two
  have hUVsm : AEStronglyMeasurable (U * V) μ :=
    hU.aestronglyMeasurable.mul hV.aestronglyMeasurable
  have hUVleU : (fun ω => ‖(U * V) ω‖) ≤ᵐ[μ] U := by
    filter_upwards [hU0, hU1, hV0, hV1] with ω hu0 hu1 hv0 hv1
    simp only [Pi.mul_apply, Pi.one_apply, Pi.zero_apply] at *
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu0 hv0)]
    nlinarith
  have hUVi : Integrable (U * V) μ := Integrable.mono' hUi hUVsm hUVleU
  rw [covariance_eq_sub hU hV]
  set IU := ∫ ω, U ω ∂μ
  set IV := ∫ ω, V ω ∂μ
  set IUV := ∫ ω, (U * V) ω ∂μ
  have hIU0 : 0 ≤ IU := integral_nonneg_of_ae hU0
  have hIV0 : 0 ≤ IV := integral_nonneg_of_ae hV0
  have hIUV0 : 0 ≤ IUV := integral_nonneg_of_ae (by
    filter_upwards [hU0, hV0] with ω hu hv
    simp only [Pi.mul_apply, Pi.zero_apply] at *; exact mul_nonneg hu hv)
  have hIUVleU : IUV ≤ IU := by
    apply integral_mono_ae hUVi hUi
    filter_upwards [hU0, hV1] with ω hu hv
    simp only [Pi.mul_apply, Pi.one_apply, Pi.zero_apply] at *
    nlinarith
  have hIUVleV : IUV ≤ IV := by
    apply integral_mono_ae hUVi hVi
    filter_upwards [hV0, hU1] with ω hv hu
    simp only [Pi.mul_apply, Pi.one_apply, Pi.zero_apply] at *
    nlinarith
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h1 : IU * IV ≤ min IU IV := by
      rw [le_min_iff]
      refine ⟨?_, ?_⟩
      · nlinarith [integral_mono_ae hVi (integrable_const (1 : ℝ)) hV1,
          (by simp : ∫ _ω : Ω, (1 : ℝ) ∂μ = 1)]
      · nlinarith [integral_mono_ae hUi (integrable_const (1 : ℝ)) hU1,
          (by simp : ∫ _ω : Ω, (1 : ℝ) ∂μ = 1)]
    nlinarith [hIUV0]
  · have : IUV ≤ min IU IV := le_min hIUVleU hIUVleV
    nlinarith [mul_nonneg hIU0 hIV0]

/-!
## `lem:tridual`: step-sector duality identities (combinatorial core)

Lemma `lem:tridual` evaluates the triangular duality functional `D^{tri}(ξ_s, η⁰)` on the
**step** initial condition `η⁰` (state `3`, encoded as occupation `1`, on every site
`x ≤ 0`; empty on `x > 0`).  Its combinatorial heart is that on the step every `q`-weight
`q^{2(a + N⁺_{a+1}(η⁰))}` collapses to `1`, because `N⁺_{a+1}(η⁰) = -a` for the occupied
sites `a ≤ 0`; the dual functional then reduces to the bare indicator
`𝟙{Xᵢ(s) ≤ 0 ∀ i}`.  We set up the step configuration and its right-count and prove these
identities.  (The marginal-consistency claim `P_{(a,b)}(X₁≤0) = P_a(X≤0)` is the
probabilistic content carried by `prop:decouple`(a) and is not part of this algebraic core.)
-/

/-- The step configuration `η⁰` of `lem:tridual`: a particle (occupation `1`) at every
site `x ≤ 0`, empty (`0`) at every site `x > 0`. -/
def stepConfig (x : ℤ) : ℤ := if x ≤ 0 then 1 else 0

/-- The right-count `N⁺_a(η⁰) = #{x ≥ a : η⁰_x = 1}` of the step configuration:
`N⁺_a = max 0 (1 - a)` — there are `1 - a` occupied sites in `[a, 0]` when `a ≤ 0`, and
none when `a ≥ 1`. -/
def NplusStep (a : ℤ) : ℤ := max 0 (1 - a)

lemma NplusStep_nonneg (a : ℤ) : 0 ≤ NplusStep a := le_max_left _ _

/-- The defining right-count recurrence `N⁺_a = N⁺_{a+1} + η⁰_a` (the per-site identity
underlying `eq:telescope`): adjoining site `a` to the half-line `[a+1, ∞)` increases the
count by the occupation `η⁰_a`.  This identifies `NplusStep` as the genuine right-count of
`stepConfig`. -/
lemma step_telescope (a : ℤ) : NplusStep a = NplusStep (a + 1) + stepConfig a := by
  unfold NplusStep stepConfig
  rcases le_or_gt a 0 with h | h <;> simp [h] <;> omega

/-- The step right-count vanishes on the empty half-line `a ≥ 1` (`η⁰` is right-finite). -/
lemma NplusStep_eq_zero_of_pos {a : ℤ} (ha : 1 ≤ a) : NplusStep a = 0 := by
  unfold NplusStep; omega

/-- On the step, for an occupied site `a ≤ 0` the right-count is `N⁺_{a+1} = -a`. -/
lemma NplusStep_succ_of_nonpos {a : ℤ} (ha : a ≤ 0) : NplusStep (a + 1) = -a := by
  unfold NplusStep; omega

/-- **Step-sector exponent collapse (core of `lem:tridual`).**  On the step configuration,
for every occupied site `a ≤ 0` the contact exponent `a + N⁺_{a+1}(η⁰)` vanishes. -/
lemma step_contact_exponent_zero {a : ℤ} (ha : a ≤ 0) :
    a + NplusStep (a + 1) = 0 := by
  unfold NplusStep; omega

/-- Consequently every `q`-weight `q^{2(a + N⁺_{a+1}(η⁰))}` in `D^{tri}(ξ_s, η⁰)` equals
`1` (the paper's `q^{2(Xᵢ - Xᵢ)} = 1`), for any base `q`. -/
lemma step_qweight_eq_one (q : ℝ) {a : ℤ} (ha : a ≤ 0) :
    q ^ (2 * (a + NplusStep (a + 1))) = 1 := by
  rw [step_contact_exponent_zero ha]; simp

/-- The dual contribution therefore reduces to a pure indicator: any weighted dual term
`q^{2(a + N⁺_{a+1}(η⁰))} · P` collapses to `P`, so on the step
`D^{tri}(ξ_s, η⁰) = 𝟙{Xᵢ(s) ≤ 0 ∀ i}`, as in `lem:tridual`. -/
lemma step_dual_weight_collapse (q P : ℝ) {a : ℤ} (ha : a ≤ 0) :
    q ^ (2 * (a + NplusStep (a + 1))) * P = P := by
  rw [step_qweight_eq_one q ha, one_mul]

/-!
## `thm:cov` contact representation: the literal `eq:qmom`/`eq:qcov` identities

The two preceding sections supplied every algebraic ingredient of the `q`-Laplace
contact representation Theorem `thm:cov`: the per-site telescope `q_telescope`
(eq. `eq:telescope`), its half-line sum `q_telescope_sum`, the product expansion
`q_cov_product_expansion`, the covariance shift `cov_one_sub_one_sub`, and the
`[0,1]`-valued covariance bound `covariance_abs_le_min_integral`.  Here we assemble the
first of those into the paper's literal contact-representation identities, written
*verbatim* with the contact weights `q^{2(a + N⁺_{a+1})}` of the duality identities
`eq:tri1`/`eq:tri2` and the prefactor weights `q^{-2a}`.

Given a right-finite single-species configuration with `q`-deformed right-counts
`q^{2N⁺_a}` — encoded by `Np : ℕ → ℕ` with site occupation `η_a = N⁺_a - N⁺_{a+1} ∈
{0,1}` and `N⁺_a = 0` for `a ≥ K`, so that `N := N⁺_1` is the right-count at the origin
— the marginal `q`-Laplace observable has the exact per-sample contact representation
`eq:qmom`.  Taking expectations and identifying
`P_a = E[η_a q^{2(a + N⁺_{a+1})}]` recovers the probabilistic statement of the paper.
-/

/-- **Literal `eq:qmom` (per-sample contact representation of `thm:cov`).**
For a right-finite configuration with `q`-deformed right-counts `q^{2N⁺_a}` (encoded by
`Np`, with `η_a = N⁺_a - N⁺_{a+1} ∈ {0,1}` and `N⁺_a = 0` for `a ≥ K`), the marginal
`q`-Laplace observable at the origin satisfies the exact contact representation
`q^{2N⁺_1} = 1 - (1-q²) ∑_{a=1}^{K-1} q^{-2a}·η_a·q^{2(a + N⁺_{a+1})}`.
Taking expectations with `P_a := E[η_a q^{2(a + N⁺_{a+1})}]` gives the paper's `eq:qmom`
`E[q^{2N_i}] = 1 - (1-q²) ∑_{a≥1} q^{-2a} P_a`. -/
lemma qmom_contact (q : ℝ) (hq : q ≠ 0) (Np : ℕ → ℕ) (K : ℕ)
    (hmono : ∀ a, Np (a + 1) ≤ Np a ∧ Np a ≤ Np (a + 1) + 1)
    (hzero : ∀ a, K ≤ a → Np a = 0) (hK : 1 ≤ K) :
    q ^ (2 * Np 1)
      = 1 - (1 - q ^ 2) * ∑ a ∈ Finset.Ico 1 K,
          q ^ (-(2 * (a : ℤ))) * ((Np a - Np (a + 1) : ℕ) : ℝ)
            * q ^ (2 * ((a : ℤ) + (Np (a + 1) : ℤ))) := by
  have hsum : (1 - q ^ 2) * ∑ a ∈ Finset.Ico 1 K,
        q ^ (-(2 * (a : ℤ))) * ((Np a - Np (a + 1) : ℕ) : ℝ)
          * q ^ (2 * ((a : ℤ) + (Np (a + 1) : ℤ)))
      = ∑ a ∈ Finset.Ico 1 K,
        (1 - q ^ 2) * ((Np a - Np (a + 1) : ℕ) : ℝ) * q ^ (2 * Np (a + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    have hz : q ^ (-(2 * (a : ℤ))) * q ^ (2 * ((a : ℤ) + (Np (a + 1) : ℤ)))
        = q ^ (2 * Np (a + 1)) := by
      rw [← zpow_add₀ hq,
        show (-(2 * (a : ℤ)) + 2 * ((a : ℤ) + (Np (a + 1) : ℤ))) = (2 * Np (a + 1) : ℕ) by
          push_cast; ring,
        zpow_natCast]
    rw [show (1 - q ^ 2) * (q ^ (-(2 * (a : ℤ))) * ((Np a - Np (a + 1) : ℕ) : ℝ)
            * q ^ (2 * ((a : ℤ) + (Np (a + 1) : ℤ))))
        = (1 - q ^ 2) * ((Np a - Np (a + 1) : ℕ) : ℝ)
            * (q ^ (-(2 * (a : ℤ))) * q ^ (2 * ((a : ℤ) + (Np (a + 1) : ℤ)))) by ring,
      hz]
  rw [hsum, q_telescope_sum q Np K hmono hzero 1 hK]
  ring

/-- **Literal `eq:qcov` (per-sample contact representation of `thm:cov`).**
Multiplying the two marginal identities `qmom_contact` for the two species gives the
exact double-contact representation
`(1 - q^{2N₁})(1 - q^{2N₂}) = (1-q²)² ∑_{a,b} q^{-2(a+b)}·
  (η₁_a q^{2(a+N⁺₁_{a+1})})·(η₂_b q^{2(b+N⁺₂_{b+1})})`.
Taking expectations, applying the product expansion `q_cov_product_expansion` and the
covariance shift `cov_one_sub_one_sub`, and inserting the duality identities
`eq:tri1`/`eq:tri2` yields the paper's `eq:qcov` with the connected pair kernel
`C_s(a,b)`. -/
lemma qcov_contact (q : ℝ) (hq : q ≠ 0) (Np1 Np2 : ℕ → ℕ) (K : ℕ)
    (hmono1 : ∀ a, Np1 (a + 1) ≤ Np1 a ∧ Np1 a ≤ Np1 (a + 1) + 1)
    (hzero1 : ∀ a, K ≤ a → Np1 a = 0)
    (hmono2 : ∀ a, Np2 (a + 1) ≤ Np2 a ∧ Np2 a ≤ Np2 (a + 1) + 1)
    (hzero2 : ∀ a, K ≤ a → Np2 a = 0) (hK : 1 ≤ K) :
    (1 - q ^ (2 * Np1 1)) * (1 - q ^ (2 * Np2 1))
      = (1 - q ^ 2) ^ 2 * ∑ a ∈ Finset.Ico 1 K, ∑ b ∈ Finset.Ico 1 K,
          q ^ (-(2 * ((a : ℤ) + (b : ℤ))))
            * (((Np1 a - Np1 (a + 1) : ℕ) : ℝ) * q ^ (2 * ((a : ℤ) + (Np1 (a + 1) : ℤ))))
            * (((Np2 b - Np2 (b + 1) : ℕ) : ℝ) * q ^ (2 * ((b : ℤ) + (Np2 (b + 1) : ℤ)))) := by
  have h1 := qmom_contact q hq Np1 K hmono1 hzero1 hK
  have h2 := qmom_contact q hq Np2 K hmono2 hzero2 hK
  set S1 := ∑ a ∈ Finset.Ico 1 K,
      q ^ (-(2 * (a : ℤ))) * ((Np1 a - Np1 (a + 1) : ℕ) : ℝ)
        * q ^ (2 * ((a : ℤ) + (Np1 (a + 1) : ℤ))) with hS1
  set S2 := ∑ b ∈ Finset.Ico 1 K,
      q ^ (-(2 * (b : ℤ))) * ((Np2 b - Np2 (b + 1) : ℕ) : ℝ)
        * q ^ (2 * ((b : ℤ) + (Np2 (b + 1) : ℤ))) with hS2
  have e1 : 1 - q ^ (2 * Np1 1) = (1 - q ^ 2) * S1 := by rw [h1]; ring
  have e2 : 1 - q ^ (2 * Np2 1) = (1 - q ^ 2) * S2 := by rw [h2]; ring
  rw [e1, e2, show (1 - q ^ 2) * S1 * ((1 - q ^ 2) * S2) = (1 - q ^ 2) ^ 2 * (S1 * S2) by ring]
  congr 1
  rw [hS1, hS2, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  have hz : q ^ (-(2 * (a : ℤ))) * q ^ (-(2 * (b : ℤ))) = q ^ (-(2 * ((a : ℤ) + (b : ℤ)))) := by
    rw [← zpow_add₀ hq]; congr 1; ring
  rw [← hz]; ring

end TypeDDecoupling