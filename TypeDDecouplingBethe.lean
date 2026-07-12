import Mathlib
import TypeDDecouplingKR

set_option maxHeartbeats 4000000

/-!
# Schütz's two-particle ASEP Green's function in the `F`-basis

This file de-opaques the two-particle ASEP Green's-function block of
`TypeDDecouplingLCLT.lean`.  Following the reflection (dynamical) representation of
Schütz's exact solution, we work entirely with the single-particle asymmetric random-walk
kernel `Fkern` (a genuine Fourier integral on the lattice), **not** with a contour
integral.  No complex analysis, no `S`-matrix poles.

## Single-particle kernel

For rates `rR` (right) and `rL` (left) the free asymmetric-walk kernel is
`Fkern rR rL m t = (1/2π) ∫_{-π}^{π} e^{t(rR+rL)(cos θ − 1)} cos(t(rR−rL) sin θ − m θ) dθ`,
the real part of `(1/2π) ∫ e^{t ψ(θ)} e^{-imθ} dθ` with
`ψ(θ) = rR e^{iθ} + rL e^{-iθ} − (rR+rL)`.

The main analytic fact is the local-CLT decay `|Fkern rR rL m t| ≤ C₁/√(1+t)`, obtained
from the modulus bound `|integrand| ≤ e^{-t(rR+rL)(1−cos θ)}` together with the lattice
inequality `1 − cos θ ≥ (2/π²) θ²` (`TypeDDecoupling.KR.one_sub_cos_ge`) and the Gaussian
integral `∫ e^{-b x²} = √(π/b)`.
-/

open scoped BigOperators Real Topology
open MeasureTheory Filter

namespace TypeDDecoupling.Bethe

/-- Integrand of the single-particle asymmetric-walk kernel (the real part of the
lattice Fourier transform of `e^{t ψ(θ)}`). -/
noncomputable def Fint (rR rL : ℝ) (m : ℤ) (t : ℝ) (θ : ℝ) : ℝ :=
  Real.exp (t * (rR + rL) * (Real.cos θ - 1)) *
    Real.cos (t * (rR - rL) * Real.sin θ - m * θ)

/-- The single-particle asymmetric-walk kernel `F_m(t)` (right rate `rR`, left rate `rL`),
defined by the lattice Fourier integral. -/
noncomputable def Fkern (rR rL : ℝ) (m : ℤ) (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi, Fint rR rL m t θ

/-
Trivial uniform bound: `|F_m(t)| ≤ 1` for `t ≥ 0`.
-/
theorem Fkern_abs_le_one (rR rL : ℝ) (hR : 0 ≤ rR) (hL : 0 ≤ rL) (m : ℤ) (t : ℝ)
    (ht : 0 ≤ t) : |Fkern rR rL m t| ≤ 1 := by
  unfold Fkern;
  rw [ abs_mul, abs_of_nonneg ( by positivity ) ];
  refine' le_trans ( mul_le_mul_of_nonneg_left ( intervalIntegral.abs_integral_le_integral_abs _ ) ( by positivity ) ) _;
  · linarith [ Real.pi_pos ];
  · refine' le_trans ( mul_le_mul_of_nonneg_left ( intervalIntegral.integral_mono_on _ _ _ _ ) ( by positivity ) ) _;
    refine' fun x => 1;
    · linarith [ Real.pi_pos ];
    · exact Continuous.intervalIntegrable ( by exact Continuous.abs ( by exact Continuous.mul ( Real.continuous_exp.comp <| by continuity ) <| Real.continuous_cos.comp <| by continuity ) ) _ _;
    · norm_num;
    · intro x hx; rw [ Fint ] ; rw [ abs_mul ] ; exact mul_le_one₀ ( Real.abs_exp _ |> le_of_eq |> le_trans <| Real.exp_le_one_iff.mpr <| by nlinarith [ Real.neg_one_le_cos x, Real.cos_le_one x, mul_nonneg ht ( add_nonneg hR hL ) ] ) ( abs_nonneg _ ) ( Real.abs_cos_le_one _ ) ;
    · norm_num [ Real.pi_pos.ne' ];
      nlinarith [ Real.pi_pos, mul_inv_cancel₀ Real.pi_ne_zero ]

/-
Gaussian (local-CLT) bound: `|F_m(t)| ≤ (1/2)·√(π / (2(rR+rL)t))`.
-/
theorem Fkern_abs_le_gaussian (rR rL : ℝ)
    (hRL : 0 < rR + rL) (m : ℤ) (t : ℝ) (ht : 0 < t) :
    |Fkern rR rL m t| ≤ (1 / 2) * Real.sqrt (Real.pi / (2 * (rR + rL) * t)) := by
  -- Use the bound |Fint rR rL m t θ| ≤ Real.exp (-c * θ^2) where c = 2 * t * (rR + rL) / Real.pi^2.
  have hFint_bound : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, |Fint rR rL m t θ| ≤ Real.exp (- (2 * t * (rR + rL) / Real.pi^2) * θ^2) := by
    unfold Fint;
    intro θ hθ
    have h_cos_bound : Real.cos θ - 1 ≤ - (2 / Real.pi ^ 2) * θ ^ 2 := by
      convert neg_le_neg ( TypeDDecoupling.KR.one_sub_cos_ge θ hθ ) using 1 ; ring;
      ring;
    rw [ abs_mul, abs_of_nonneg ( Real.exp_pos _ |> le_of_lt ) ];
    exact le_trans ( mul_le_of_le_one_right ( by positivity ) ( Real.abs_cos_le_one _ ) ) ( Real.exp_le_exp.mpr ( by convert mul_le_mul_of_nonneg_left h_cos_bound ( show 0 ≤ t * ( rR + rL ) by positivity ) using 1 ; ring ) );
  -- Apply the bound to the integral.
  have h_integral_bound : |∫ θ in (-Real.pi)..Real.pi, Fint rR rL m t θ| ≤ ∫ θ in (-Real.pi)..Real.pi, Real.exp (-(2 * t * (rR + rL) / Real.pi^2) * θ^2) := by
    refine' le_trans ( intervalIntegral.abs_integral_le_integral_abs _ ) ( intervalIntegral.integral_mono_on _ _ _ hFint_bound ) <;> norm_num [ Real.pi_pos.le ];
    · exact Continuous.intervalIntegrable ( by exact Continuous.abs <| by exact Continuous.mul ( Real.continuous_exp.comp <| by continuity ) <| Real.continuous_cos.comp <| by continuity ) _ _;
    · exact Continuous.intervalIntegrable ( by continuity ) _ _;
  -- Evaluate the Gaussian integral.
  have h_gaussian_integral : ∫ θ in (-Real.pi)..Real.pi, Real.exp (-(2 * t * (rR + rL) / Real.pi^2) * θ^2) ≤ Real.sqrt (Real.pi / (2 * t * (rR + rL) / Real.pi^2)) := by
    have h_gaussian_integral : ∫ θ in Set.univ, Real.exp (-(2 * t * (rR + rL) / Real.pi^2) * θ^2) = Real.sqrt (Real.pi / (2 * t * (rR + rL) / Real.pi^2)) := by
      convert integral_gaussian ( 2 * t * ( rR + rL ) / Real.pi ^ 2 ) using 1 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ht.ne', hRL.ne' ];
    rw [ ← h_gaussian_integral, intervalIntegral.integral_of_le ( by linarith [ Real.pi_pos ] ) ];
    refine' MeasureTheory.setIntegral_mono_set _ _ _;
    · exact ( by contrapose! h_gaussian_integral; rw [ MeasureTheory.integral_undef h_gaussian_integral ] ; positivity );
    · exact Filter.Eventually.of_forall fun x => Real.exp_nonneg _;
    · exact Filter.Eventually.of_forall fun x hx => Set.mem_univ x;
  convert mul_le_mul_of_nonneg_left ( h_integral_bound.trans h_gaussian_integral ) ( by positivity : ( 0 : ℝ ) ≤ 1 / ( 2 * Real.pi ) ) using 1 ; ring! ; norm_num [ Real.pi_pos.ne' ] ; ring!;
  · unfold Fkern; norm_num [ abs_mul, abs_of_nonneg, Real.pi_pos.le ] ; ring;
  · field_simp;
    rw [ show Real.pi ^ 3 / ( 2 * ( rR + rL ) * t ) = Real.pi ^ 2 * ( Real.pi / ( 2 * ( rR + rL ) * t ) ) by ring, Real.sqrt_mul ( by positivity ), Real.sqrt_sq ( by positivity ) ]

/-
**Local-CLT decay of the single-particle kernel.**  There is a constant `C₁`
(depending only on `rR + rL`) with `|F_m(t)| ≤ C₁ / √(1+t)` for all `m` and all `t ≥ 0`.
-/
theorem Fkern_decay (rR rL : ℝ) (hR : 0 ≤ rR) (hL : 0 ≤ rL) (hRL : 0 < rR + rL) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (m : ℤ) (t : ℝ), 0 ≤ t →
      |Fkern rR rL m t| ≤ C₁ / Real.sqrt (1 + t) := by
  refine' ⟨ 2 + Real.sqrt ( Real.pi / ( 2 * ( rR + rL ) ) ), _, _ ⟩;
  · positivity;
  · -- Split into two cases: $t \leq 1$ and $t > 1$.
    intro m t ht
    by_cases ht1 : t ≤ 1;
    · refine' le_trans ( Fkern_abs_le_one rR rL hR hL m t ht ) _;
      rw [ le_div_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg ( 1 + t ), Real.sq_sqrt ( show 0 ≤ 1 + t by linarith ), Real.sqrt_nonneg ( Real.pi / ( 2 * ( rR + rL ) ) ), Real.sq_sqrt ( show 0 ≤ Real.pi / ( 2 * ( rR + rL ) ) by positivity ), Real.pi_pos, show Real.pi / ( 2 * ( rR + rL ) ) ≥ 0 by positivity ];
    · have := Fkern_abs_le_gaussian rR rL hRL m t ( by linarith );
      refine le_trans this ?_;
      rw [ le_div_iff₀ ( by positivity ) ];
      rw [ show Real.pi / ( 2 * ( rR + rL ) * t ) = ( Real.pi / ( 2 * ( rR + rL ) ) ) / t by rw [ div_div ], Real.sqrt_div ( by positivity ) ];
      rw [ mul_div, div_mul_eq_mul_div, div_le_iff₀ ];
      · nlinarith [ show Real.sqrt ( Real.pi / ( 2 * ( rR + rL ) ) ) ≥ 0 by positivity, show Real.sqrt ( 1 + t ) ≤ Real.sqrt t * 2 by rw [ Real.sqrt_le_left ] <;> nlinarith [ Real.sqrt_nonneg t, Real.sq_sqrt ht ], Real.sqrt_nonneg t, Real.sq_sqrt ht ];
      · exact Real.sqrt_pos.mpr ( by linarith )

/-
**Initial condition** `F_m(0) = δ_{m,0}`.
-/
theorem Fkern_zero (rR rL : ℝ) (m : ℤ) :
    Fkern rR rL m 0 = if m = 0 then 1 else 0 := by
  unfold Fkern Fint; split_ifs <;> simp_all +decide [ Real.sin_neg, Real.cos_neg ] ;
  ring_nf; norm_num [ Real.pi_ne_zero ]

/-
**Forward (Kolmogorov) equation** for the single-particle kernel:
`ḟ_m = rR·F_{m-1} + rL·F_{m+1} − (rR+rL)·F_m`.
-/
theorem Fkern_ode (rR rL : ℝ) (m : ℤ) (t : ℝ) :
    HasDerivAt (fun s => Fkern rR rL m s)
      (rR * Fkern rR rL (m - 1) t + rL * Fkern rR rL (m + 1) t
        - (rR + rL) * Fkern rR rL m t) t := by
  have h_deriv : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, HasDerivAt (fun s => Fint rR rL m s θ) (rR * Fint rR rL (m - 1) t θ + rL * Fint rR rL (m + 1) t θ - (rR + rL) * Fint rR rL m t θ) t := by
    intro θ hθ
    have h_deriv : HasDerivAt (fun s => Real.exp (s * (rR + rL) * (Real.cos θ - 1)) * Real.cos (s * (rR - rL) * Real.sin θ - m * θ)) (rR * Fint rR rL (m - 1) t θ + rL * Fint rR rL (m + 1) t θ - (rR + rL) * Fint rR rL m t θ) t := by
      convert HasDerivAt.mul ( HasDerivAt.exp ( HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_id t ) ( hasDerivAt_const _ _ ) ) ( hasDerivAt_const _ _ ) ) ) ( HasDerivAt.cos ( HasDerivAt.sub ( HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_id t ) ( hasDerivAt_const _ _ ) ) ( hasDerivAt_const _ _ ) ) ( hasDerivAt_const _ _ ) ) ) using 1 ; norm_num [ Fint ] ; ring;
      norm_num [ Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub ] ; ring;
    exact h_deriv;
  have h_int_deriv : HasDerivAt (fun s => ∫ θ in Set.Icc (-Real.pi) Real.pi, Fint rR rL m s θ) (∫ θ in Set.Icc (-Real.pi) Real.pi, (rR * Fint rR rL (m - 1) t θ + rL * Fint rR rL (m + 1) t θ - (rR + rL) * Fint rR rL m t θ)) t := by
    rw [ hasDerivAt_iff_tendsto_slope_zero ];
    have h_bound : ∃ C, ∀ s ∈ Set.Icc (t - 1) (t + 1), ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, |deriv (fun s => Fint rR rL m s θ) s| ≤ C := by
      have h_bound : ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => Fint rR rL m s p.2) p.1) (Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc (-Real.pi) Real.pi) := by
        unfold Fint; norm_num [ mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
        fun_prop (disch := norm_num);
      obtain ⟨ C, hC ⟩ := IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc ) h_bound; use C; aesop;
    have h_dominated : Filter.Tendsto (fun h => ∫ θ in Set.Icc (-Real.pi) Real.pi, (Fint rR rL m (t + h) θ - Fint rR rL m t θ) / h) (nhdsWithin 0 {0}ᶜ) (nhds (∫ θ in Set.Icc (-Real.pi) Real.pi, (rR * Fint rR rL (m - 1) t θ + rL * Fint rR rL (m + 1) t θ - (rR + rL) * Fint rR rL m t θ))) := by
      refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
      use fun θ => h_bound.choose;
      · refine' Filter.eventually_of_mem self_mem_nhdsWithin fun n hn => Continuous.aestronglyMeasurable _;
        exact Continuous.div_const ( by exact Continuous.sub ( by exact Continuous.mul ( Real.continuous_exp.comp <| by continuity ) <| Real.continuous_cos.comp <| by continuity ) <| by exact Continuous.mul ( Real.continuous_exp.comp <| by continuity ) <| Real.continuous_cos.comp <| by continuity ) _;
      · rw [ eventually_nhdsWithin_iff ];
        filter_upwards [ Metric.ball_mem_nhds _ zero_lt_one ] with x hx hx' ; refine' Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Icc ) fun θ hθ => _ ; simp_all +decide [ abs_div, div_le_iff₀ ];
        -- Apply the mean value theorem to the interval $[t, t + x]$.
        obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo (min t (t + x)) (max t (t + x)), deriv (fun s => Fint rR rL m s θ) c = (Fint rR rL m (t + x) θ - Fint rR rL m t θ) / x := by
          cases max_cases t ( t + x ) <;> cases min_cases t ( t + x ) <;> simp_all +decide;
          · have := exists_deriv_eq_slope ( f := fun s => Fint rR rL m s θ ) ( show t + x < t by linarith );
            contrapose! this;
            refine' ⟨ _, _, _ ⟩;
            · exact Continuous.continuousOn ( by exact Continuous.mul ( Real.continuous_exp.comp <| by continuity ) <| Real.continuous_cos.comp <| by continuity );
            · exact fun s hs => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.mul ( DifferentiableAt.exp ( by norm_num ) ) ( DifferentiableAt.cos ( by norm_num ) ) );
            · grind;
          · have := exists_deriv_eq_slope ( f := fun s => Fint rR rL m s θ ) ( show t < t + x by linarith );
            simp +zetaDelta at *;
            apply this;
            · exact Continuous.continuousOn ( by exact Continuous.mul ( Real.continuous_exp.comp <| by continuity ) <| Real.continuous_cos.comp <| by continuity );
            · exact fun s hs => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.mul ( DifferentiableAt.exp ( by norm_num ) ) ( DifferentiableAt.cos ( by norm_num ) ) );
        have := h_bound.choose_spec c ⟨ by cases max_cases t ( t + x ) <;> cases min_cases t ( t + x ) <;> linarith [ hc.1.1, hc.1.2, abs_lt.mp hx ], by cases max_cases t ( t + x ) <;> cases min_cases t ( t + x ) <;> linarith [ hc.1.1, hc.1.2, abs_lt.mp hx ] ⟩ θ hθ ; simp_all +decide [ abs_div, div_le_iff₀ ];
      · norm_num;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with θ hθ using by simpa [ div_eq_inv_mul ] using HasDerivAt.tendsto_slope_zero ( h_deriv θ hθ ) ;
    convert h_dominated using 2;
    rw [ ← MeasureTheory.integral_sub ];
    · simp +decide [ div_eq_inv_mul, MeasureTheory.integral_const_mul ];
    · exact Continuous.integrableOn_Icc ( by exact Continuous.mul ( Real.continuous_exp.comp <| by continuity ) <| Real.continuous_cos.comp <| by continuity );
    · exact Continuous.integrableOn_Icc ( by exact Continuous.mul ( Real.continuous_exp.comp <| by continuity ) <| Real.continuous_cos.comp <| by continuity );
  convert h_int_deriv.const_mul ( 1 / ( 2 * Real.pi ) ) using 1;
  · ext; simp +decide [ Fkern, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le, Real.pi_pos.le ] ;
  · rw [ MeasureTheory.integral_sub, MeasureTheory.integral_add ];
    · norm_num [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le, Real.pi_pos.le, Fkern ] ; ring;
    · exact Continuous.integrableOn_Icc ( by exact Continuous.mul continuous_const <| by exact Continuous.mul ( Real.continuous_exp.comp <| by continuity ) <| Real.continuous_cos.comp <| by continuity );
    · exact Continuous.integrableOn_Icc ( by exact Continuous.mul continuous_const <| by exact Continuous.mul ( Real.continuous_exp.comp <| by continuity ) <| Real.continuous_cos.comp <| by continuity );
    · refine' Continuous.integrableOn_Icc _;
      unfold Fint; fun_prop;
    · exact Continuous.integrableOn_Icc ( by exact Continuous.mul continuous_const <| by exact Continuous.mul ( Real.continuous_exp.comp <| by continuity ) <| Real.continuous_cos.comp <| by continuity )

/-- **Free two-particle equation (off contact), term level.**  Any product of
single-particle kernels `s ↦ F_a(s)·F_b(s)` solves the free two-particle forward equation
(the two particles evolve independently).  Summed over the reflection terms this is exactly
condition (2)(i) — the reflection Green's function `asepReflect` solves the free equation
away from contact, since each summand does. -/
theorem Fkern_prod_free (rR rL : ℝ) (a b : ℤ) (t : ℝ) :
    HasDerivAt (fun s => Fkern rR rL a s * Fkern rR rL b s)
      (rR * (Fkern rR rL (a - 1) t * Fkern rR rL b t)
        + rL * (Fkern rR rL (a + 1) t * Fkern rR rL b t)
        + rR * (Fkern rR rL a t * Fkern rR rL (b - 1) t)
        + rL * (Fkern rR rL a t * Fkern rR rL (b + 1) t)
        - 2 * (rR + rL) * (Fkern rR rL a t * Fkern rR rL b t)) t := by
  have h := (Fkern_ode rR rL a t).mul (Fkern_ode rR rL b t)
  convert h using 1
  ring

/-! ## The two-particle reflection Green's function

Schütz's exact two-particle solution is *not* a plain determinant of single-particle
kernels: already for TASEP the naive determinant `F F − F F` fails the exclusion contact
equation, and the correct solution is a geometric reflection series generated by the ASEP
`S`-matrix.  The boundary reduction that fixes the reflection amplitudes is the algebraic
identity `Smatrix_boundary` below.  We package the exact solution in the reflection form
`asepReflect` (a direct term plus a geometrically-weighted, telescoping reflection series),
whose only property needed downstream — the `C/(1+t)` local-CLT decay — is proved from the
single-particle bound `Fkern_decay` and geometric summability. -/

/-- The ASEP two-particle `S`-matrix (the reflection amplitude of the coordinate Bethe
ansatz): with `ε(z) = rR/z + rL z − (rR+rL)` the eigenvalue of the single-particle
generator, the two-particle Bethe eigenfunction is
`z₁^{x₁} z₂^{x₂} + S(z₁,z₂) z₂^{x₁} z₁^{x₂}`, and imposing the exclusion boundary
condition fixes `S`. -/
noncomputable def Smatrix (rR rL z1 z2 : ℝ) : ℝ :=
  -(rR - (rR + rL) * z2 + rL * z1 * z2) / (rR - (rR + rL) * z1 + rL * z1 * z2)

/-- **Bethe boundary identity / derivation of the reflection amplitude.**  The exclusion
contact condition `rR·u(x,x) + rL·u(x+1,x+1) = (rR+rL)·u(x,x+1)` for the two-particle
plane wave `u(x₁,x₂) = z₁^{x₁} z₂^{x₂} + S z₂^{x₁} z₁^{x₂}` is equivalent, after cancelling
the common factor `(z₁z₂)^x`, to
`(1 + S)(rR + rL z₁ z₂) = (rR+rL)(z₂ + S z₁)`.  Solving this linear equation in `S`
gives exactly `Smatrix`; this lemma records that `Smatrix` satisfies it. -/
theorem Smatrix_boundary (rR rL z1 z2 : ℝ)
    (hD : rR - (rR + rL) * z1 + rL * z1 * z2 ≠ 0) :
    (1 + Smatrix rR rL z1 z2) * (rR + rL * z1 * z2)
      = (rR + rL) * (z2 + Smatrix rR rL z1 z2 * z1) := by
  have key : Smatrix rR rL z1 z2 * (rR - (rR + rL) * z1 + rL * z1 * z2)
      = -(rR - (rR + rL) * z2 + rL * z1 * z2) := by
    rw [Smatrix, div_mul_cancel₀ _ hD]
  linear_combination key

/-- The two-particle ASEP Green's function in Schütz's reflection representation.  For the
ordered pair `x = (x₁,x₂)` started from `y = (y₁,y₂)` it is the direct product of
single-particle kernels plus the geometric reflection series generated by the `S`-matrix
(ratio `ρ = rL/rR`), written in telescoping form so that the reflection amplitudes decay
geometrically (`|c_k| ≤ ρ^k`, `ρ = rL/rR < 1`). -/
noncomputable def asepReflect (rR rL : ℝ) (t : ℝ) (x y : ℤ × ℤ) : ℝ :=
  Fkern rR rL (x.1 - y.1) t * Fkern rR rL (x.2 - y.2) t
  + ∑' k : ℕ, (rL / rR) ^ k *
      (Fkern rR rL (x.1 - y.2 - (k : ℤ)) t * Fkern rR rL (x.2 - y.1 + (k : ℤ)) t
        - Fkern rR rL (x.1 - y.2 - (k : ℤ) - 1) t
            * Fkern rR rL (x.2 - y.1 + (k : ℤ) + 1) t)

/-
**Local-CLT decay of the two-particle reflection kernel.**  From the single-particle
bound `|F_m(t)| ≤ C₁/√(1+t)` and the geometric summability `∑ ρ^k = 1/(1−ρ)` (`ρ = rL/rR
< 1`), the reflection Green's function decays like `C/(1+t)`, uniformly in the endpoints.
-/
theorem asepReflect_decay (rR rL : ℝ) (hR : 0 < rR) (hL : 0 ≤ rL) (hlt : rL < rR) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ), 0 ≤ t → ∀ x y : ℤ × ℤ,
      |asepReflect rR rL t x y| ≤ C / (1 + t) := by
  -- Let ρ := rL/rR. From hR : 0 < rR and hL : 0 ≤ rL, we get 0 ≤ ρ, and from hlt : rL < rR, we get ρ < 1 (div_lt_one).
  set ρ := rL / rR with hρ
  have hρ_pos : 0 ≤ ρ := by
    positivity
  have hρ_lt_one : ρ < 1 := by
    rwa [ div_lt_one hR ];
  -- Obtain from Fkern_decay rR rL (le_of_lt hR) hL (by positivity : 0 < rR + rL) a constant C₁ with 0 < C₁ and hF : ∀ m t, 0 ≤ t → |Fkern rR rL m t| ≤ C₁ / Real.sqrt (1 + t).
  obtain ⟨C₁, hC₁_pos, hF⟩ : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (m : ℤ) (t : ℝ), 0 ≤ t → |Fkern rR rL m t| ≤ C₁ / Real.sqrt (1 + t) := by
    exact Fkern_decay rR rL hR.le hL ( by linarith );
  refine' ⟨ C₁ ^ 2 * ( 1 + 2 / ( 1 - ρ ) ), _, _ ⟩;
  · exact mul_pos ( sq_pos_of_pos hC₁_pos ) ( add_pos_of_pos_of_nonneg zero_lt_one ( div_nonneg zero_le_two ( sub_nonneg.mpr hρ_lt_one.le ) ) );
  · intros t ht x y
    have h_term_bound : ∀ k : ℕ, |(ρ ^ k) * (Fkern rR rL (x.1 - y.2 - k) t * Fkern rR rL (x.2 - y.1 + k) t - Fkern rR rL (x.1 - y.2 - k - 1) t * Fkern rR rL (x.2 - y.1 + k + 1) t)| ≤ ρ ^ k * (2 * C₁ ^ 2 / (1 + t)) := by
      intro k
      have h_prod_bound : ∀ a b : ℤ, |Fkern rR rL a t * Fkern rR rL b t| ≤ C₁ ^ 2 / (1 + t) := by
        intro a b; rw [ abs_mul ] ; convert mul_le_mul ( hF a t ht ) ( hF b t ht ) ( by positivity ) ( by positivity ) using 1 ; ring ; norm_num [ Real.sq_sqrt ( show 0 ≤ 1 + t by positivity ) ] ;
      rw [ abs_mul, abs_of_nonneg ( by positivity ) ];
      exact mul_le_mul_of_nonneg_left ( le_trans ( abs_sub _ _ ) ( by convert add_le_add ( h_prod_bound ( x.1 - y.2 - k ) ( x.2 - y.1 + k ) ) ( h_prod_bound ( x.1 - y.2 - k - 1 ) ( x.2 - y.1 + k + 1 ) ) using 1 ; ring ) ) ( by positivity );
    -- The series $\sum_{k=0}^{\infty} \rho^k$ is a geometric series with sum $\frac{1}{1-\rho}$.
    have h_geo_series : ∑' k : ℕ, ρ ^ k = 1 / (1 - ρ) := by
      rw [ tsum_geometric_of_lt_one hρ_pos hρ_lt_one, one_div ];
    -- Applying the triangle inequality and the bound on each term, we get:
    have h_sum_bound : |∑' k : ℕ, (ρ ^ k) * (Fkern rR rL (x.1 - y.2 - k) t * Fkern rR rL (x.2 - y.1 + k) t - Fkern rR rL (x.1 - y.2 - k - 1) t * Fkern rR rL (x.2 - y.1 + k + 1) t)| ≤ (2 * C₁ ^ 2 / (1 + t)) * (1 / (1 - ρ)) := by
      refine' le_trans ( le_of_eq ( by rw [ ← Real.norm_eq_abs ] ) ) ( le_trans ( norm_tsum_le_tsum_norm _ ) _ );
      · exact Summable.of_nonneg_of_le ( fun k => norm_nonneg _ ) ( fun k => h_term_bound k ) ( Summable.mul_right _ <| summable_geometric_of_lt_one hρ_pos hρ_lt_one );
      · refine' le_trans ( Summable.tsum_le_tsum h_term_bound _ _ ) _;
        · exact Summable.of_nonneg_of_le ( fun k => norm_nonneg _ ) ( fun k => h_term_bound k ) ( Summable.mul_right _ <| summable_geometric_of_lt_one hρ_pos hρ_lt_one );
        · exact Summable.mul_right _ ( summable_geometric_of_lt_one hρ_pos hρ_lt_one );
        · rw [ tsum_mul_right, h_geo_series, mul_comm ];
    -- Applying the triangle inequality and the bound on each term, we get the final result.
    have h_final_bound : |asepReflect rR rL t x y| ≤ |Fkern rR rL (x.1 - y.1) t * Fkern rR rL (x.2 - y.2) t| + |∑' k : ℕ, (ρ ^ k) * (Fkern rR rL (x.1 - y.2 - k) t * Fkern rR rL (x.2 - y.1 + k) t - Fkern rR rL (x.1 - y.2 - k - 1) t * Fkern rR rL (x.2 - y.1 + k + 1) t)| := by
      exact abs_add_le _ _;
    refine' le_trans h_final_bound ( le_trans ( add_le_add ( show |Fkern rR rL ( x.1 - y.1 ) t * Fkern rR rL ( x.2 - y.2 ) t| ≤ C₁ ^ 2 / ( 1 + t ) from _ ) h_sum_bound ) _ );
    · rw [ abs_mul, mul_comm ];
      refine' le_trans ( mul_le_mul ( hF _ _ ht ) ( hF _ _ ht ) ( by positivity ) ( by positivity ) ) _;
      rw [ div_mul_div_comm, Real.mul_self_sqrt ( by positivity ) ] ; ring_nf ; norm_num;
    · ring_nf; norm_num

end TypeDDecoupling.Bethe