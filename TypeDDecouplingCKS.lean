import Mathlib
import TypeDDecouplingSemigroup
import TypeDDecouplingNash

/-!
# CKS heat-kernel program on the exponential semigroup

This file discharges the two dynamical inputs of `lem_free`
(`TypeDDecouplingLCLT.lean`) by running the Nash / Carlen–Kusuoka–Stroock (CKS)
argument on the **exponential semigroup** `Q_t := exp (t • A)` of the bounded
forward generator `A` (from `TypeDDecouplingSemigroup.exists_forward_generator`).

The strategy is *inverted*: every property (positivity, mass, `q ≤ 1`,
Chapman–Kolmogorov, reversibility, energy identity, the `y`-uniform Nash ODE,
off-diagonal decay) is proved for the semigroup kernel `q^y_t(x)`, for **all**
start points `y`, and the abstract kernel `W.p` is touched exactly once through
the identification `W.p = q^0` (weighted Grönwall, using the a-priori bound
`W.p ≤ 1`).
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open NormedSpace
open scoped BigOperators Topology

namespace TypeDDecouplingCKS

/-- The `ℓ¹` space of signed measures on `ℤ`. -/
abbrev L1 := lp (fun _ : ℤ => ℝ) 1

/-- Coordinate evaluation `f ↦ f x` as a linear map on `ℓ¹`. -/
noncomputable def evalL (x : ℤ) : L1 →ₗ[ℝ] ℝ where
  toFun f := (f : ∀ _ : ℤ, ℝ) x
  map_add' f g := by simp
  map_smul' c f := by simp

/-- Coordinate evaluation `f ↦ f x` as a continuous linear map on `ℓ¹`
(operator norm `≤ 1`). -/
noncomputable def evalC (x : ℤ) : L1 →L[ℝ] ℝ :=
  (evalL x).mkContinuous 1 (by
    intro f
    simpa [evalL] using lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0) f x)

@[simp] lemma evalC_apply (x : ℤ) (f : L1) : evalC x f = (f : ∀ _ : ℤ, ℝ) x := rfl

/-- The exponential of a scalar multiple of the identity operator is the scalar
exponential times the identity. -/
lemma exp_smul_one (s : ℝ) :
    (exp (s • (1 : L1 →L[ℝ] L1))) = (Real.exp s) • (1 : L1 →L[ℝ] L1) := by
  have h1 : s • (1 : L1 →L[ℝ] L1) = algebraMap ℝ (L1 →L[ℝ] L1) s :=
    (Algebra.algebraMap_eq_smul_one s).symm
  rw [h1, ← NormedSpace.algebraMap_exp_comm s, Algebra.algebraMap_eq_smul_one]
  congr 1
  rw [Real.exp_eq_exp_ℝ]

/-
**Positivity of the operator exponential.**  If a bounded operator `T`
preserves coordinatewise nonnegativity, so does `exp T`.
-/
lemma exp_coord_nonneg (T : L1 →L[ℝ] L1)
    (hT : ∀ g : L1, (∀ w : ℤ, 0 ≤ (g : ∀ _ : ℤ, ℝ) w) → ∀ x : ℤ, 0 ≤ (T g : ∀ _ : ℤ, ℝ) x)
    (f : L1) (hf : ∀ w : ℤ, 0 ≤ (f : ∀ _ : ℤ, ℝ) w) (x : ℤ) :
    0 ≤ ((exp T) f : ∀ _ : ℤ, ℝ) x := by
  -- By definition of exponentiation, we know that $(\exp T) f = \sum_{n=0}^{\infty} \frac{T^n f}{n!}$.
  have h_exp : (exp T) f = ∑' n : ℕ, (1 / (Nat.factorial n) : ℝ) • (T^[n] f) := by
    have h_exp : (exp T) = ∑' n, (1 / (n.factorial : ℝ)) • (T^n) := by
      simp +decide [ NormedSpace.exp_eq_tsum ];
      convert exp_eq_tsum using 1;
      constructor <;> intro h;
      convert exp_eq_tsum;
      convert h ℝ;
      any_goals exact L1 →L[ℝ] L1;
      any_goals try infer_instance;
      constructor <;> intro h <;> simp_all +decide [ funext_iff ];
      rename_i h';
      convert h' ℝ using 1;
    rw [ h_exp, ← ContinuousLinearMap.apply_apply ];
    rw [ ContinuousLinearMap.map_tsum ];
    · ext; simp +decide [ ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_pow ];
    · refine' Summable.of_norm _;
      simp +decide [ norm_smul ];
      -- Since $T$ is a bounded linear operator, we have $\|T^n\| \leq \|T\|^n$.
      have h_norm : ∀ n : ℕ, ‖T^n‖ ≤ ‖T‖^n := by
        intro n; induction n <;> simp_all +decide [ pow_succ' ] ;
        · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp +decide ;
        · exact le_trans ( ContinuousLinearMap.opNorm_comp_le _ _ ) ( mul_le_mul_of_nonneg_left ‹_› ( norm_nonneg _ ) );
      exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ( norm_nonneg _ ) ) ( fun n => mul_le_mul_of_nonneg_left ( h_norm n ) ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ) ( by simpa [ inv_mul_eq_div ] using Real.summable_pow_div_factorial ‖T‖ );
  have h_nonneg : ∀ n : ℕ, 0 ≤ (T^[n] f) x := by
    intro n; induction' n with n ih generalizing x <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
  by_cases h : Summable ( fun n : ℕ => ( 1 / ( n.factorial : ℝ ) ) • ( T^[n] f ) ) <;> simp_all +decide [ tsum_eq_zero_of_not_summable ];
  have h_nonneg : ∀ {g : ℕ → L1}, Summable g → (∀ n, 0 ≤ (g n) x) → 0 ≤ (∑' n, g n) x := by
    intros g hg hg_nonneg
    have h_nonneg : 0 ≤ (evalC x (∑' n, g n)) := by
      rw [ ContinuousLinearMap.map_tsum ];
      · exact tsum_nonneg fun n => hg_nonneg n;
      · exact hg;
    exact h_nonneg;
  exact h_nonneg h fun n => by simpa using mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ( by solve_by_elim ) ;

/-- The semigroup vector `q^y_t := exp (t • A) δ_y ∈ ℓ¹`. -/
noncomputable def qvec (A : L1 →L[ℝ] L1) (y : ℤ) (t : ℝ) : L1 :=
  (exp (t • A)) (lp.single 1 y 1)

/-- The kernel `q^y_t(x)`: the `x`-coordinate of `q^y_t`. -/
noncomputable def qq (A : L1 →L[ℝ] L1) (y : ℤ) (t : ℝ) (x : ℤ) : ℝ :=
  (qvec A y t : ∀ _ : ℤ, ℝ) x

/-- The on-diagonal `ℓ²(1/m)` energy `u^y(t) := ∑ₓ q^y_t(x)² / m x`. -/
noncomputable def energy (A : L1 →L[ℝ] L1) (m : ℤ → ℝ) (y : ℤ) (t : ℝ) : ℝ :=
  ∑' x : ℤ, (qq A y t x) ^ 2 / m x

/-- The pointwise time-derivative of the energy, in "`2 ∑ q q'/m`" form
(with `q'` the forward-ODE right-hand side). -/
noncomputable def energyDeriv (A : L1 →L[ℝ] L1) (rate : ℤ → ℤ → ℝ) (m : ℤ → ℝ)
    (y : ℤ) (t : ℝ) : ℝ :=
  ∑' x : ℤ,
    2 * qq A y t x *
      ((∑' z, rate z x * qq A y t z) - (∑' z, rate x z) * qq A y t x) / m x

/-- The uniform Nash-ODE rate constant `κ := δ c₁⁴ / (2 c₂³)`. -/
noncomputable def kap (δ c₁ c₂ : ℝ) : ℝ := δ * c₁ ^ 4 / (2 * c₂ ^ 3)

/-
Cauchy–Schwarz inequality for `tsum` over `ℤ`.
-/
lemma tsum_cauchy_schwarz (f g : ℤ → ℝ)
    (hfg : Summable (fun z => f z * g z))
    (hf : Summable (fun z => (f z) ^ 2)) (hg : Summable (fun z => (g z) ^ 2)) :
    ∑' z, f z * g z ≤ Real.sqrt (∑' z, (f z) ^ 2) * Real.sqrt (∑' z, (g z) ^ 2) := by
  convert Summable.tsum_le_of_sum_le ( hfg ) _ using 1;
  intro s;
  convert Real.sum_mul_le_sqrt_mul_sqrt ( s := s ) ( f := f ) ( g := g ) |> le_trans <| ?_ using 1;
  exact mul_le_mul ( Real.sqrt_le_sqrt <| Summable.sum_le_tsum ( s ) ( fun _ _ => sq_nonneg _ ) hf ) ( Real.sqrt_le_sqrt <| Summable.sum_le_tsum ( s ) ( fun _ _ => sq_nonneg _ ) hg ) ( Real.sqrt_nonneg _ ) ( Real.sqrt_nonneg _ )

section Semigroup

variable (A : L1 →L[ℝ] L1) (rate : ℤ → ℤ → ℝ) (m : ℤ → ℝ)
variable (Λ δ c₁ c₂ : ℝ) (ϱ : ℕ)
variable (hA : ∀ (f : L1) (y : ℤ), (A f : ∀ _ : ℤ, ℝ) y
    = (∑' x, rate x y * (f : ∀ _ : ℤ, ℝ) x) - (∑' z, rate y z) * (f : ∀ _ : ℤ, ℝ) y)
variable (hnn : ∀ x y, 0 ≤ rate x y)
variable (hfr : ∀ x y, rate x y ≠ 0 → (y - x).natAbs ≤ ϱ)
variable (hexit : ∀ x, ∑' y, rate x y ≤ Λ)
variable (hrev : ∀ x y, m x * rate x y = m y * rate y x)
variable (hc1 : 0 < c₁) (hmlb : ∀ x, c₁ ≤ m x) (hmub : ∀ x, m x ≤ c₂)
variable (hδ : 0 < δ) (hcond : ∀ x, δ ≤ m x * rate x (x + 1))

include A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond

/-- Initial condition: `q^y_0 = δ_y`. -/
lemma qq_zero (y x : ℤ) : qq A y 0 x = if x = y then 1 else 0 := by
  simp only [qq, qvec, zero_smul, exp_zero]
  rw [ContinuousLinearMap.one_apply, lp.single_apply]
  simp [Pi.single_apply]

/-- The per-site forward (Kolmogorov) ODE satisfied by the semigroup kernel. -/
lemma qq_hasDerivAt (y x : ℤ) (t : ℝ) :
    HasDerivAt (fun s => qq A y s x)
      ((∑' z, rate z x * qq A y t z) - (∑' z, rate x z) * qq A y t x) t := by
  have h1 : HasDerivAt (fun s => exp (s • A)) (exp (t • A) * A) t :=
    hasDerivAt_exp_smul_const A t
  have h2 : HasDerivAt (fun s => (exp (s • A)) (lp.single 1 y 1))
      ((exp (t • A) * A) (lp.single 1 y 1)) t := by
    simpa using h1.clm_apply (hasDerivAt_const t (lp.single 1 y 1))
  have h3 : HasDerivAt (fun s => qq A y s x)
      (((exp (t • A) * A) (lp.single 1 y 1) : ∀ _ : ℤ, ℝ) x) t :=
    (evalC x).hasFDerivAt.comp_hasDerivAt t h2
  have hcomm : (exp (t • A)) * A = A * (exp (t • A)) := by
    have hc : Commute (t • A) A := (Commute.refl A).smul_left t
    simpa [Commute, SemiconjBy] using hc.exp_left.eq
  have hval : ((exp (t • A) * A) (lp.single 1 y 1) : ∀ _ : ℤ, ℝ) x
      = (∑' z, rate z x * qq A y t z) - (∑' z, rate x z) * qq A y t x := by
    rw [hcomm]
    show (A ((exp (t • A)) (lp.single 1 y 1)) : ∀ _ : ℤ, ℝ) x = _
    rw [hA]
    rfl
  rwa [hval] at h3

/-- Each `q^y_t` is coordinate-summable (it lives in `ℓ¹`). -/
lemma qq_summable (y : ℤ) (t : ℝ) : Summable (fun x => qq A y t x) := by
  have h := lp.hasSum_norm (by norm_num : (0:ℝ) < (1:ENNReal).toReal) (qvec A y t)
  simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] at h
  exact (h.summable).of_abs

/-
The total mass is annihilated by the generator: `∑ₓ (A f)(x) = 0`.
-/
lemma A_mass_zero (f : L1) : ∑' x : ℤ, (A f : ∀ _ : ℤ, ℝ) x = 0 := by
  -- The sum of the exit rates is equal to the sum of the entry rates.
  have h_sum_eq : ∑' x, (∑' z, rate x z) * (f : ℤ → ℝ) x = ∑' x, (∑' z, rate z x * (f : ℤ → ℝ) z) := by
    rw [ ← Summable.tsum_comm ];
    · simp +decide only [tsum_mul_right];
    · have h_summable : Summable (fun p : ℤ × ℤ => rate p.1 p.2 * |f p.1|) := by
        have h_summable : Summable (fun (p : ℤ × ℤ) => rate p.1 p.2 * |f p.1|) := by
          have h_summable : ∀ x, Summable (fun (y : ℤ) => rate x y * |f x|) := by
            intro x
            have h_summable : Summable (fun (y : ℤ) => rate x y) := by
              refine' summable_of_ne_finset_zero _;
              exacts [ Finset.Icc ( x - ϱ ) ( x + ϱ ), fun y hy => Classical.not_not.1 fun h => hy <| Finset.mem_Icc.2 ⟨ by cases abs_cases ( y - x ) <;> linarith [ hfr x y h ], by cases abs_cases ( y - x ) <;> linarith [ hfr x y h ] ⟩ ];
            exact h_summable.mul_right _
          have h_summable : Summable (fun (x : ℤ) => ∑' (y : ℤ), rate x y * |f x|) := by
            have h_summable : Summable (fun (x : ℤ) => (∑' (y : ℤ), rate x y) * |f x|) := by
              have h_summable : Summable (fun (x : ℤ) => Λ * |f x|) := by
                exact Summable.mul_left _ ( by simpa using f.2.summable );
              exact Summable.of_nonneg_of_le ( fun x => mul_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ( abs_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_right ( hexit x ) ( abs_nonneg _ ) ) h_summable;
            simpa only [ tsum_mul_right ] using h_summable;
          rw [ summable_prod_of_nonneg ];
          · grobner;
          · exact fun _ => mul_nonneg ( hnn _ _ ) ( abs_nonneg _ );
        convert h_summable using 1;
      rw [ ← summable_norm_iff ] at *;
      convert h_summable.comp_injective ( show Function.Injective ( fun x : ℤ × ℤ => ( x.2, x.1 ) ) from fun x y h => by aesop ) using 1;
      ext; simp [Function.uncurry];
  by_cases h : Summable ( fun x => ( ∑' z, rate x z ) * f x ) <;> simp_all +decide [ tsum_mul_left, tsum_mul_right ];
  · by_cases h' : Summable ( fun x => ∑' z, rate z x * f z ) <;> simp_all +decide [ tsum_mul_left, tsum_mul_right ];
    · rw [ Summable.tsum_sub h' h, h_sum_eq, sub_self ];
    · rw [ tsum_eq_zero_of_not_summable ];
      exact fun H => h' <| by simpa using H.add h;
  · contrapose! h;
    refine' .of_norm _;
    refine' Summable.of_nonneg_of_le ( fun x => norm_nonneg _ ) ( fun x => _ ) ( Summable.mul_left ( Λ ) ( show Summable fun x : ℤ => ‖f x‖ from _ ) );
    · simpa only [ norm_mul, Real.norm_eq_abs, abs_of_nonneg ( show 0 ≤ ∑' z : ℤ, rate x z from tsum_nonneg fun _ => hnn _ _ ) ] using mul_le_mul_of_nonneg_right ( hexit x ) ( abs_nonneg _ );
    · simpa using f.2.summable

/-
Mass conservation: `∑ₓ q^y_t(x) = 1` for `t ≥ 0`.
-/
lemma qq_mass (y : ℤ) (t : ℝ) (ht : 0 ≤ t) : ∑' x : ℤ, qq A y t x = 1 := by
  -- Let `S t := ∑' x, qq A y t x`. Note `qq A y t x = (qvec A y t) x` (the `x`-coordinate), so `S t = ∑' x, (qvec A y t) x`.
  set S : ℝ → ℝ := fun t => ∑' x : ℤ, qq A y t x;
  -- Step 1 (mass functional as a CLM). Build `massC : L1 →L[ℝ] ℝ` with `massC g = ∑' x, (g : ℤ→ℝ) x`.
  have h_massC : ∃ massC : L1 →L[ℝ] ℝ, ∀ g : L1, massC g = ∑' x : ℤ, (g : ℤ → ℝ) x := by
    have h_massC : ∀ g : L1, ‖∑' x : ℤ, (g : ℤ → ℝ) x‖ ≤ ‖g‖ := by
      intro g;
      have := lp.hasSum_norm ( by norm_num : ( 0 : ℝ ) < ( 1 : ENNReal ).toReal ) g;
      exact le_trans ( norm_tsum_le_tsum_norm ( by simpa using g.2.summable ) ) ( by simpa using this.tsum_eq.le );
    refine' ⟨ _, _ ⟩;
    exact ( LinearMap.mkContinuous ( show L1 →ₗ[ℝ] ℝ from { toFun := fun g => ∑' x : ℤ, ( g : ℤ → ℝ ) x, map_add' := fun g h => by
                                                              rw [ ← Summable.tsum_add ];
                                                              · rfl;
                                                              · have := g.2.summable;
                                                                exact Summable.of_norm <| by simpa using this zero_lt_one;
                                                              · have := h.2.summable;
                                                                exact .of_norm <| by simpa using this zero_lt_one;, map_smul' := fun c g => by
                                                              simp +decide [ tsum_mul_left ] } ) 1 fun g => by simpa using h_massC g );
    aesop;
  -- Step 2 (derivative of qvec). Show `HasDerivAt (fun s => qvec A y s) (A (qvec A y t)) t`.
  have h_qvec_deriv : ∀ t : ℝ, HasDerivAt (fun s => qvec A y s) (A (qvec A y t)) t := by
    intro t;
    convert ( hasDerivAt_exp_smul_const A t ).clm_apply ( hasDerivAt_const t ( lp.single 1 y 1 ) ) using 1;
    have h_comm : Commute (t • A) A := by
      simp +decide [ Commute, mul_comm ];
      simp +decide [ SemiconjBy, mul_comm ];
    simp +decide [ qvec, h_comm.exp_left ];
    have := h_comm.exp_left;
    exact congr_arg ( fun f => f ( lp.single 1 y 1 ) ) this.symm;
  -- Step 3 (S has zero derivative everywhere). `S = massC ∘ (qvec A y ·)`, so `HasDerivAt S (massC (A (qvec A y t))) t`.
  obtain ⟨massC, hmassC⟩ := h_massC;
  have h_S_deriv : ∀ t : ℝ, HasDerivAt S (massC (A (qvec A y t))) t := by
    intro t; convert ( massC.hasFDerivAt.comp_hasDerivAt t ( h_qvec_deriv t ) ) using 1; aesop;
  -- Step 4 (S is constant, value at 0). A function with derivative `0` everywhere on `ℝ` is constant: use `is_const_of_deriv_eq_zero` (with `Differentiable` from the `HasDerivAt`s) or the MVT.
  have h_S_const : ∀ t : ℝ, S t = S 0 := by
    have h_S_const : ∀ t : ℝ, massC (A (qvec A y t)) = 0 := by
      exact fun t => hmassC _ ▸ A_mass_zero A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond _;
    intro t; exact is_const_of_deriv_eq_zero (fun t => (h_S_deriv t).differentiableAt) (fun t => by simpa [h_S_const] using (h_S_deriv t).deriv) t 0;
  convert h_S_const t using 1;
  simp +zetaDelta at *;
  unfold qq; simp +decide [ qvec ] ;

/-- Semigroup split: `exp (t • A) = e^{-Λ t} · exp (t • (A + Λ·1))`. -/
lemma exp_shift (t : ℝ) :
    exp (t • A)
      = (Real.exp (-(Λ * t))) • exp (t • (A + Λ • (1 : L1 →L[ℝ] L1))) := by
  have hB : t • (A + Λ • (1 : L1 →L[ℝ] L1)) = t • A + (t * Λ) • (1 : L1 →L[ℝ] L1) := by
    rw [smul_add, smul_smul]
  have hcomm : Commute (t • A) ((t * Λ) • (1 : L1 →L[ℝ] L1)) :=
    (Commute.one_right (t • A)).smul_right (t * Λ)
  have hadd : exp (t • A + (t * Λ) • (1 : L1 →L[ℝ] L1))
      = exp (t • A) * exp ((t * Λ) • (1 : L1 →L[ℝ] L1)) := by
    apply exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hcomm <;>
      · rw [NormedSpace.expSeries_radius_eq_top]; simp
  rw [hB, hadd, exp_smul_one]
  rw [mul_smul_comm, mul_one, smul_smul, ← Real.exp_add]
  rw [show -(Λ * t) + t * Λ = 0 by ring, Real.exp_zero, one_smul]

/-- Positivity of the semigroup kernel for `t ≥ 0`. -/
lemma qq_nonneg (y x : ℤ) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ qq A y t x := by
  set B : L1 →L[ℝ] L1 := A + Λ • (1 : L1 →L[ℝ] L1) with hBdef
  -- `B` preserves coordinatewise nonnegativity
  have hBnn : ∀ g : L1, (∀ w : ℤ, 0 ≤ (g : ∀ _ : ℤ, ℝ) w) → ∀ z : ℤ, 0 ≤ (B g : ∀ _ : ℤ, ℝ) z := by
    intro g hg z
    have hval : (B g : ∀ _ : ℤ, ℝ) z
        = (∑' w, rate w z * (g : ∀ _ : ℤ, ℝ) w) + (Λ - ∑' w, rate z w) * (g : ∀ _ : ℤ, ℝ) z := by
      simp only [hBdef, ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, lp.coeFn_smul,
        Pi.smul_apply, smul_eq_mul, hA]
      ring
    rw [hval]
    exact add_nonneg (tsum_nonneg fun _ => mul_nonneg (hnn _ _) (hg _))
      (mul_nonneg (sub_nonneg.mpr (hexit _)) (hg _))
  -- hence `t • B` preserves it (for `t ≥ 0`)
  have hTnn : ∀ g : L1, (∀ w : ℤ, 0 ≤ (g : ∀ _ : ℤ, ℝ) w) → ∀ z : ℤ, 0 ≤ ((t • B) g : ∀ _ : ℤ, ℝ) z := by
    intro g hg z
    have : ((t • B) g : ∀ _ : ℤ, ℝ) z = t * ((B g : ∀ _ : ℤ, ℝ) z) := by
      simp [ContinuousLinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply]
    rw [this]; exact mul_nonneg ht (hBnn g hg z)
  have hsingle : ∀ w : ℤ, 0 ≤ (lp.single 1 y (1 : ℝ) : ∀ _ : ℤ, ℝ) w := by
    intro w; rw [lp.single_apply]; by_cases h : w = y <;> simp [Pi.single_apply, h]
  have hpos := exp_coord_nonneg (t • B) hTnn (lp.single 1 y 1) hsingle x
  have hsplit : qq A y t x = Real.exp (-(Λ * t)) * ((exp (t • B) (lp.single 1 y 1) : ∀ _ : ℤ, ℝ) x) := by
    simp only [qq, qvec, exp_shift A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond t,
      ← hBdef, ContinuousLinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [hsplit]
  exact mul_nonneg (Real.exp_nonneg _) hpos

/-- The semigroup kernel is a sub-probability: `q^y_t(x) ≤ 1` for `t ≥ 0`. -/
lemma qq_le_one (y x : ℤ) (t : ℝ) (ht : 0 ≤ t) : qq A y t x ≤ 1 := by
  have hs := qq_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t
  have hle : qq A y t x ≤ ∑' w, qq A y t w :=
    hs.le_tsum x (fun j _ => qq_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y j t ht)
  rwa [qq_mass A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht] at hle

/-
Series representation of the kernel in terms of matrix powers of the
generator.
-/
lemma qq_series (a b : ℤ) (t : ℝ) :
    qq A a t b
      = ∑' n : ℕ, (n.factorial : ℝ)⁻¹ * t ^ n * (((A ^ n) (lp.single 1 a 1) : ∀ _ : ℤ, ℝ) b) := by
  have h_exp : exp (t • A) = ∑' n, (n.factorial : ℝ)⁻¹ • (t • A)^n := by
    convert exp_eq_tsum using 1;
    constructor;
    intro h;
    convert exp_eq_tsum using 1;
    intro h; exact h ℝ ( 𝔸 := L1 →L[ℝ] L1 ) ▸ rfl;
  have h_eval : ∀ n : ℕ, (((t • A)^n) (lp.single 1 a 1)) = t^n • ((A^n) (lp.single 1 a 1)) := by
    intro n; induction n <;> simp_all +decide [ pow_succ', mul_assoc, smul_smul ] ;
  have h_summable : Summable (fun n : ℕ => (n.factorial : ℝ)⁻¹ • (t • A)^n) := by
    convert NormedSpace.expSeries_summable' ( t • A ) using 1;
    all_goals infer_instance;
  convert congr_arg ( fun f => ( evalC b ) ( f ( lp.single 1 a 1 ) ) ) h_exp using 1;
  have h_eval_sum : ∀ {f : ℕ → L1 →L[ℝ] L1}, Summable f → (evalC b) ((∑' n, f n) (lp.single 1 a 1)) = ∑' n, (evalC b) (f n (lp.single 1 a 1)) := by
    intro f hf; exact (by
    convert ( ContinuousLinearMap.map_tsum ( evalC b ) ( hf.map ( ContinuousLinearMap.apply ℝ L1 ( lp.single 1 a 1 ) ) ?_ ) ) using 1;
    · congr! 1;
      exact ( ContinuousLinearMap.apply ℝ L1 ( lp.single 1 a 1 ) ).map_tsum hf;
    · fun_prop);
  rw [ h_eval_sum h_summable ];
  simp +decide [ h_eval, mul_assoc, mul_left_comm, mul_comm ]

/-
Right recurrence for matrix powers (apply `A` last).
-/
lemma Apow_apply_right (n : ℕ) (a b : ℤ) :
    (((A ^ (n + 1)) (lp.single 1 a 1) : ∀ _ : ℤ, ℝ) b)
      = (∑' z, rate z b * (((A ^ n) (lp.single 1 a 1) : ∀ _ : ℤ, ℝ) z))
          - (∑' z, rate b z) * (((A ^ n) (lp.single 1 a 1) : ∀ _ : ℤ, ℝ) b) := by
  convert hA _ _ using 1;
  rw [ pow_succ', ContinuousLinearMap.mul_apply ]

/-
Left recurrence for matrix powers (apply `A` first).
-/
lemma Apow_apply_left (n : ℕ) (a b : ℤ) :
    (((A ^ (n + 1)) (lp.single 1 a 1) : ∀ _ : ℤ, ℝ) b)
      = (∑' z, rate a z * (((A ^ n) (lp.single 1 z 1) : ∀ _ : ℤ, ℝ) b))
          - (∑' z, rate a z) * (((A ^ n) (lp.single 1 a 1) : ∀ _ : ℤ, ℝ) b) := by
  -- By definition of $g$, we have $g = \sum_{z} \text{lp.single } 1 z (g z)$.
  have hg : (A (lp.single 1 a 1)) = ∑' z, (lp.single 1 z (rate a z - (if z = a then (∑' w, rate a w) else 0))) := by
    have hg : ∀ z, (A (lp.single 1 a 1) : ∀ _ : ℤ, ℝ) z = rate a z - (if z = a then (∑' w, rate a w) else 0) := by
      intro z; rw [ hA ] ; simp +decide [ tsum_mul_left, tsum_mul_right, lp.single_apply ] ;
      rw [ tsum_eq_single a ] <;> aesop;
    have hg_sum : Summable (fun z => lp.single 1 z (rate a z - (if z = a then (∑' w, rate a w) else 0))) := by
      refine' summable_of_ne_finset_zero _;
      exact Finset.Icc ( a - ϱ ) ( a + ϱ );
      intro z hz; specialize hfr a z; contrapose! hz; simp_all +decide [ sub_eq_iff_eq_add ] ;
      grind +splitImp;
    refine' lp.hasSum_single ( by norm_num ) _ |> fun h => h.unique _;
    convert hg_sum.hasSum using 1 ; aesop;
  -- By definition of $g$, we have $g = \sum_{z} \text{lp.single } 1 z (g z)$, so we can apply $A^n$ to both sides.
  have hA_g : (A ^ n) (A (lp.single 1 a 1)) = ∑' z, (rate a z - (if z = a then (∑' w, rate a w) else 0)) • (A ^ n) (lp.single 1 z 1) := by
    rw [ hg ];
    have h_sum : Summable (fun z => (rate a z - (if z = a then (∑' w, rate a w) else 0)) • (lp.single 1 z 1 : L1)) := by
      refine' summable_of_ne_finset_zero _;
      exact Finset.Icc ( a - ϱ ) ( a + ϱ );
      intro z hz; split_ifs <;> simp_all +decide [ sub_eq_iff_eq_add ] ;
      exact Or.inl <| Classical.not_not.1 fun h => by have := hfr a z h; cases abs_cases ( z - a ) <;> linarith [ hz <| by linarith ] ;
    convert ( ContinuousLinearMap.map_tsum ( A ^ n ) h_sum ) using 1;
    · congr! 2;
      ext z; simp +decide [ lp.single_apply, Pi.smul_apply ] ;
      by_cases h : z = ‹_› <;> simp +decide [ h, Pi.single_apply ];
    · exact tsum_congr fun _ => by rw [ ContinuousLinearMap.map_smul ] ;
  convert congr_arg ( fun f => f b ) hA_g using 1;
  rw [ tsum_eq_sum, tsum_eq_sum ];
  any_goals exact Finset.Icc ( a - ϱ ) ( a + ϱ );
  · rw [ tsum_eq_sum ];
    any_goals exact Finset.Icc ( a - ϱ ) ( a + ϱ );
    · simp +decide [ sub_mul, Finset.sum_mul _ _ _ ];
    · intro z hz; split_ifs <;> simp_all +decide [ sub_eq_iff_eq_add ] ;
      exact Or.inl <| Classical.not_not.1 fun h => by have := hfr a z h; cases abs_cases ( z - a ) <;> linarith [ hz <| by linarith ] ;
  · exact fun x hx => Classical.not_not.1 fun hx' => hx <| Finset.mem_Icc.2 ⟨ by cases abs_cases ( x - a ) <;> linarith [ hfr a x hx' ], by cases abs_cases ( x - a ) <;> linarith [ hfr a x hx' ] ⟩;
  · grind

/-- **Matrix symmetry (detailed balance for powers of the generator).**
`m a · (A^n δ_a)(b) = m b · (A^n δ_b)(a)` for all `n`. -/
lemma matrix_symm (n : ℕ) (a b : ℤ) :
    m a * (((A ^ n) (lp.single 1 a 1) : ∀ _ : ℤ, ℝ) b)
      = m b * (((A ^ n) (lp.single 1 b 1) : ∀ _ : ℤ, ℝ) a) := by
  induction n generalizing a b with
  | zero =>
    simp only [pow_zero, ContinuousLinearMap.one_apply, lp.single_apply, Pi.single_apply]
    by_cases h : b = a
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]; ring
  | succ n ih =>
    rw [Apow_apply_right A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond n a b,
        Apow_apply_left A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond n b a,
        mul_sub, mul_sub, ← tsum_mul_left, ← tsum_mul_left]
    congr 1
    · refine tsum_congr (fun z => ?_)
      have hIH := ih a z
      have hr := hrev z b
      linear_combination (rate z b) * hIH + (((A ^ n) (lp.single 1 z 1) : ∀ _ : ℤ, ℝ) a) * hr
    · rw [← mul_assoc, ← mul_assoc, mul_comm (m a), mul_comm (m b), mul_assoc, mul_assoc,
          ih a b]

/-- Detailed balance / reversibility of the semigroup kernel:
`m y · q^y_t(x) = m x · q^x_t(y)`. -/
lemma qq_reversible (y x : ℤ) (t : ℝ) : m y * qq A y t x = m x * qq A x t y := by
  rw [qq_series A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y x t,
      qq_series A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond x y t,
      ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  have hs := matrix_symm A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond n y x
  linear_combination ((n.factorial : ℝ)⁻¹ * t ^ n) * hs

/-
Chapman–Kolmogorov for the semigroup kernel.
-/
lemma qq_CK (y x : ℤ) (s t : ℝ) :
    qq A y (s + t) x = ∑' z : ℤ, qq A y s z * qq A z t x := by
  -- Apply the Chapman-Kolmogorov equation for the semigroup.
  have h_semigroup : ∀ s t : ℝ, exp ((s + t) • A) = exp (t • A) * exp (s • A) := by
    intro s t;
    convert ( exp_add_of_commute_of_mem_ball ( 𝕂 := ℝ ) ( show Commute ( t • A ) ( s • A ) from ?_ ) ?_ ?_ ) using 1 <;> norm_num [ Commute, SemiconjBy ];
    · rw [ add_smul, add_comm ];
    · rw [ SMulCommClass.smul_comm ];
    · rw [ NormedSpace.expSeries_radius_eq_top ] ; norm_num;
    · rw [ NormedSpace.expSeries_radius_eq_top ] ; norm_num;
  have h_summable : Summable (fun z => (qq A y s z) • (lp.single 1 z 1 : L1)) := by
    have := qq_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y s;
    refine' .of_norm _;
    convert this.norm using 2 ; norm_num [ norm_smul ];
  have h_eval : (evalC x) (exp (t • A) (qvec A y s)) = ∑' z, (evalC x) (exp (t • A) ((qq A y s z) • (lp.single 1 z 1 : L1))) := by
    rw [ show qvec A y s = ∑' z, qq A y s z • lp.single 1 z 1 from ?_ ];
    · rw [ ContinuousLinearMap.map_tsum ];
      · rw [ ContinuousLinearMap.map_tsum ];
        exact ContinuousLinearMap.summable _ h_summable;
      · convert h_summable using 1;
    · convert lp.hasSum_single _ ( qvec A y s ) |> HasSum.tsum_eq |> Eq.symm;
      · ext; simp [qq, qvec];
        grind +splitImp;
      · norm_num;
  unfold qq qvec; aesop;

/-- The energy is nonnegative. -/
lemma energy_nonneg (y : ℤ) (t : ℝ) : 0 ≤ energy A m y t := by
  refine tsum_nonneg (fun x => ?_)
  exact div_nonneg (sq_nonneg _) (le_of_lt (lt_of_lt_of_le hc1 (hmlb x)))

/-
The energy summand is summable (for `t ≥ 0`).
-/
lemma energy_summable (y : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun x => (qq A y t x) ^ 2 / m x) := by
  refine' .of_nonneg_of_le ( fun x => div_nonneg ( sq_nonneg _ ) ( by linarith [ hmlb x ] ) ) ( fun x => _ ) ( show Summable fun x => qq A y t x / c₁ from _ );
  · gcongr;
    · exact qq_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y x t ht;
    · exact pow_le_of_le_one ( qq_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y x t ht ) ( qq_le_one A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y x t ht ) ( by norm_num );
    · exact hmlb x;
  · exact Summable.mul_right _ ( qq_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t )

/-
**Energy identity (differentiation under the sum).**  The energy is
differentiable with derivative `2 ∑ q q'/m` for `t ≥ 0`.  (Fallback candidate
(d) of the brief.)
-/
lemma energy_hasDerivAt (y : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => energy A m y s) (energyDeriv A rate m y t) t := by
  have hB : ∃ B : L1 →L[ℝ] L1 →L[ℝ] ℝ, ∀ f g : L1, B f g = ∑' x : ℤ, (f : ∀ _ : ℤ, ℝ) x * (g : ∀ _ : ℤ, ℝ) x / m x := by
    have hB : ∀ f g : L1, Summable (fun x => (f : ∀ _ : ℤ, ℝ) x * (g : ∀ _ : ℤ, ℝ) x / m x) := by
      intro f g
      have h_summable : Summable (fun x => |f x| * |g x| / c₁) := by
        refine' Summable.mul_right _ _;
        have h_summable : Summable (fun x => |(f : ℤ → ℝ) x| * ‖g‖) := by
          exact Summable.mul_right _ ( by simpa using f.2.summable );
        exact Summable.of_nonneg_of_le ( fun x => mul_nonneg ( abs_nonneg _ ) ( abs_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_left ( show |g x| ≤ ‖g‖ from by simpa using lp.norm_apply_le_norm one_ne_zero g x ) ( abs_nonneg _ ) ) h_summable
      generalize_proofs at *;
      refine' .of_norm <| _;
      refine' .of_nonneg_of_le ( fun x => norm_nonneg _ ) ( fun x => _ ) h_summable.norm ; norm_num [ abs_div, abs_mul ];
      gcongr ; cases abs_cases ( m x ) <;> cases abs_cases c₁ <;> linarith [ hmlb x, hmub x ]
    generalize_proofs at *;
    have hB : ∃ B : L1 →ₗ[ℝ] L1 →ₗ[ℝ] ℝ, ∀ f g : L1, B f g = ∑' x : ℤ, (f : ∀ _ : ℤ, ℝ) x * (g : ∀ _ : ℤ, ℝ) x / m x := by
      use (LinearMap.mk₂ ℝ (fun f g : L1 => ∑' x : ℤ, (f : ∀ _ : ℤ, ℝ) x * (g : ∀ _ : ℤ, ℝ) x / m x) (by
      intro f g h; simp +decide [ add_mul, div_eq_mul_inv, tsum_mul_left, tsum_mul_right ] ; ring;
      rw [ ← Summable.tsum_add ] ; congr ; ext x ; ring;
      · simpa only [ div_eq_mul_inv ] using hB f h;
      · simpa only [ div_eq_mul_inv ] using hB g h) (by
      simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left ]) (by
      intro f g h; simp +decide [ mul_add, add_div, Summable.tsum_add, hB ] ;) (by
      simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left, tsum_mul_right ]));
      aesop
    generalize_proofs at *;
    obtain ⟨ B, hB ⟩ := hB
    generalize_proofs at *;
    have hB_cont : ∃ C : ℝ, ∀ f g : L1, |B f g| ≤ C * ‖f‖ * ‖g‖ := by
      use 1 / c₁;
      intros f g
      have hB_bound : ∀ x, |(f : ∀ _ : ℤ, ℝ) x * (g : ∀ _ : ℤ, ℝ) x / m x| ≤ (1 / c₁) * |(f : ∀ _ : ℤ, ℝ) x| * ‖g‖ := by
        intro x
        have h_abs : |(f : ∀ _ : ℤ, ℝ) x * (g : ∀ _ : ℤ, ℝ) x / m x| ≤ |(f : ∀ _ : ℤ, ℝ) x| * |(g : ∀ _ : ℤ, ℝ) x| / c₁ := by
          rw [ abs_div, abs_mul ];
          gcongr ; cases abs_cases ( m x ) <;> linarith [ hmlb x ]
        generalize_proofs at *;
        have h_abs_g : |(g : ∀ _ : ℤ, ℝ) x| ≤ ‖g‖ := by
          exact lp.norm_apply_le_norm ( by norm_num ) g x
        generalize_proofs at *;
        exact h_abs.trans ( by rw [ div_mul_eq_mul_div, div_mul_eq_mul_div ] ; rw [ div_le_div_iff_of_pos_right hc1 ] ; nlinarith [ abs_nonneg ( f x : ℝ ) ] )
      generalize_proofs at *;
      rw [ hB, ← Real.norm_eq_abs ];
      refine' le_trans ( norm_tsum_le_tsum_norm _ ) _;
      · exact Summable.of_nonneg_of_le ( fun x => norm_nonneg _ ) ( fun x => hB_bound x ) ( Summable.mul_right _ <| Summable.mul_left _ <| by simpa using f.2.summable );
      · refine' le_trans ( Summable.tsum_le_tsum hB_bound _ _ ) _;
        · exact Summable.of_nonneg_of_le ( fun x => norm_nonneg _ ) ( fun x => hB_bound x ) ( Summable.mul_right _ <| Summable.mul_left _ <| by simpa using f.2.summable );
        · exact Summable.mul_right _ <| Summable.mul_left _ <| by simpa using f.2.summable;
        · simp +decide [ tsum_mul_left, tsum_mul_right, mul_assoc, mul_comm, mul_left_comm, lp.norm_eq_tsum_rpow ]
    generalize_proofs at *;
    obtain ⟨ C, hC ⟩ := hB_cont
    generalize_proofs at *;
    have hB_cont : Continuous (fun p : L1 × L1 => B p.1 p.2) := by
      refine' continuous_iff_continuousAt.mpr _;
      intro p
      generalize_proofs at *;
      refine' tendsto_iff_norm_sub_tendsto_zero.mpr _;
      have hB_cont : Filter.Tendsto (fun e : L1 × L1 => ‖B (e.1 - p.1) e.2‖ + ‖B p.1 (e.2 - p.2)‖) (𝓝 p) (𝓝 0) := by
        refine' squeeze_zero ( fun _ => by positivity ) ( fun e => add_le_add ( hC _ _ ) ( hC _ _ ) ) _;
        refine' Continuous.tendsto' _ _ _ _ <;> norm_num;
        fun_prop (disch := norm_num)
      generalize_proofs at *;
      refine' squeeze_zero ( fun e => norm_nonneg _ ) ( fun e => _ ) hB_cont
      generalize_proofs at *;
      convert norm_add_le ( ( B ( e.1 - p.1 ) ) e.2 ) ( ( B p.1 ) ( e.2 - p.2 ) ) using 2 ; simp +decide [ sub_eq_add_neg, add_assoc ]
    generalize_proofs at *;
    exact ⟨ B.mkContinuous₂ C fun f g => by simpa [ mul_assoc ] using hC f g, hB ⟩;
  obtain ⟨B, hB⟩ := hB
  have hB_cont : Continuous B := by
    exact B.continuous;
  convert HasDerivAt.clm_apply ( B.hasFDerivAt.comp_hasDerivAt t ( show HasDerivAt ( fun s => qvec A y s ) ( A ( qvec A y t ) ) t from ?_ ) ) ( show HasDerivAt ( fun s => qvec A y s ) ( A ( qvec A y t ) ) t from ?_ ) using 1;
  · ext; simp +decide [ hB, energy, qq ] ; ring;
  · simp +decide [ hB, energyDeriv ];
    rw [ ← Summable.tsum_add ] ; congr ; ext x ; rw [ hA ] ; ring!;
    · refine' .of_norm _;
      refine' .of_nonneg_of_le ( fun x => norm_nonneg _ ) ( fun x => _ ) ( show Summable fun x => ‖( A ( qvec A y t ) : ∀ _ : ℤ, ℝ ) x‖ * ‖( qvec A y t : ∀ _ : ℤ, ℝ ) x‖ / c₁ from _ );
      · rw [ norm_div, norm_mul ];
        gcongr ; rw [ Real.norm_of_nonneg ] <;> linarith [ hmlb x, hmub x ];
      · refine' Summable.mul_right _ _;
        refine' Summable.of_nonneg_of_le ( fun x => mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_left ( lp.norm_apply_le_norm ( by norm_num ) ( qvec A y t ) x ) ( norm_nonneg _ ) ) _;
        exact Summable.mul_right _ ( by simpa using ( A ( qvec A y t ) ) |>.2.summable );
    · have h_summable : Summable (fun x => (qvec A y t : ∀ _ : ℤ, ℝ) x * (A (qvec A y t) : ∀ _ : ℤ, ℝ) x) := by
        have h_summable : Summable (fun x => |(qvec A y t : ∀ _ : ℤ, ℝ) x| * |(A (qvec A y t) : ∀ _ : ℤ, ℝ) x|) := by
          have h_summable : Summable (fun x => |(qvec A y t : ∀ _ : ℤ, ℝ) x|) := by
            exact Summable.abs ( qq_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t )
          have h_summable' : Summable (fun x => |(A (qvec A y t) : ∀ _ : ℤ, ℝ) x|) := by
            have := A ( qvec A y t ) |>.2.summable;
            simpa using this zero_lt_one
          exact Summable.of_nonneg_of_le ( fun x => mul_nonneg ( abs_nonneg _ ) ( abs_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_left ( Summable.le_tsum h_summable' x ( fun _ _ => abs_nonneg _ ) ) ( abs_nonneg _ ) ) ( h_summable.mul_right _ );
        exact Summable.of_norm <| by simpa using h_summable;
      have h_summable : Summable (fun x => |(qvec A y t : ∀ _ : ℤ, ℝ) x * (A (qvec A y t) : ∀ _ : ℤ, ℝ) x| / m x) := by
        exact Summable.of_nonneg_of_le ( fun x => div_nonneg ( abs_nonneg _ ) ( by linarith [ hmlb x ] ) ) ( fun x => div_le_div_of_nonneg_left ( abs_nonneg _ ) ( by linarith [ hmlb x ] ) ( hmlb x ) ) ( h_summable.abs.mul_right _ );
      exact Summable.of_norm <| by simpa using h_summable.norm;
  · convert ( hasDerivAt_exp_smul_const A t ).clm_apply ( hasDerivAt_const t ( lp.single 1 y 1 ) ) using 1;
    have h_comm : Commute (t • A) A := by
      simp +decide [ Commute, mul_comm ];
      simp +decide [ SemiconjBy, mul_comm ];
    simp +decide [ qvec, h_comm.exp_left ];
    exact congr_arg ( fun f => f ( lp.single 1 y 1 ) ) ( h_comm.exp_left.symm );
  · convert ( hasDerivAt_exp_smul_const A t ).clm_apply ( hasDerivAt_const t ( lp.single 1 y 1 ) ) using 1;
    have h_comm : Commute (t • A) A := by
      simp +decide [ Commute, mul_comm ];
      simp +decide [ SemiconjBy, mul_comm ];
    simp +decide [ qvec, h_comm.exp_left ];
    exact congr_arg ( fun f => f ( lp.single 1 y 1 ) ) ( h_comm.exp_left.symm )

/-
`|φ| = q/m` is summable (`φ x := qq A y t x / m x`).
-/
lemma phi_summable_abs (y : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun x => |qq A y t x / m x|) := by
  have h_summable : Summable (fun x => |qq A y t x| / c₁) := by
    exact Summable.mul_right _ ( qq_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t |> Summable.abs );
  exact Summable.of_nonneg_of_le ( fun x => abs_nonneg _ ) ( fun x => by rw [ abs_div, abs_of_nonneg ( show 0 ≤ m x from le_trans hc1.le ( hmlb x ) ) ] ; exact div_le_div_of_nonneg_left ( abs_nonneg _ ) ( by positivity ) ( hmlb x ) ) h_summable

/-
`φ² = (q/m)²` is summable.
-/
lemma phi_summable_sq (y : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun x => (qq A y t x / m x) ^ 2) := by
  have := energy_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht;
  refine' .of_nonneg_of_le ( fun x => sq_nonneg _ ) ( fun x => _ ) ( this.mul_right ( 1 / c₁ ) );
  field_simp;
  rw [ div_le_div_iff₀ ] <;> nlinarith [ hmlb x, hmub x, show 0 ≤ qq A y t x ^ 2 * m x from mul_nonneg ( sq_nonneg _ ) ( by linarith [ hmlb x ] ), show 0 ≤ qq A y t x ^ 2 * c₁ from mul_nonneg ( sq_nonneg _ ) hc1.le ]

/-
The discrete gradient of `φ` is square-summable.
-/
lemma phi_summable_grad (y : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun x => (qq A y t (x + 1) / m (x + 1) - qq A y t x / m x) ^ 2) := by
  refine' .of_nonneg_of_le ( fun x => sq_nonneg _ ) ( fun x => _ ) ( Summable.mul_left 2 ( Summable.add ( ( phi_summable_sq A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht ) |> Summable.comp_injective <| add_left_injective 1 ) ( phi_summable_sq A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht ) ) );
  norm_num ; nlinarith [ sq_nonneg ( qq A y t ( x + 1 ) / m ( x + 1 ) + qq A y t x / m x ) ]

/-
**Energy identity (Dirichlet form).**  `energyDeriv = -∑_{x,z} a(x,z)(φx-φz)²`
with `a x z = m x · rate x z` and `φ x = q x / m x`.
-/
lemma energyDeriv_eq (y : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    energyDeriv A rate m y t
      = - ∑' p : ℤ × ℤ,
          (m p.1 * rate p.1 p.2)
            * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2) ^ 2 := by
  -- Let's simplify the expression inside the sum.
  have h_simplify : ∀ x, 2 * qq A y t x * ((∑' z, rate z x * qq A y t z) - (∑' z, rate x z) * qq A y t x) / m x = -2 * (∑' z, m x * rate x z * (qq A y t x / m x - qq A y t z / m z) * (qq A y t x / m x)) := by
    intro x; rw [ show ( ∑' z : ℤ, rate z x * qq A y t z ) = ∑' z : ℤ, m x * rate x z * qq A y t z / m z from ?_ ] ; ring;
    · rw [ Summable.tsum_add ] <;> norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < m x from lt_of_lt_of_le hc1 ( hmlb x ) ) ] ; ring;
      · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, tsum_neg, tsum_mul_left, tsum_mul_right ] ; ring;
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, ← tsum_mul_left ];
        simp +decide [ mul_assoc, mul_left_comm ( m x ), ne_of_gt ( show 0 < m x from lt_of_lt_of_le hc1 ( hmlb x ) ) ];
      · refine' summable_of_ne_finset_zero _;
        exact Finset.Icc ( x - ϱ ) ( x + ϱ );
        grind +splitImp;
      · refine' summable_of_ne_finset_zero _;
        exact Finset.Icc ( x - ϱ ) ( x + ϱ );
        grind;
    · grind;
  rw [ show energyDeriv A rate m y t = ∑' x, -2 * ∑' z, m x * rate x z * ( qq A y t x / m x - qq A y t z / m z ) * ( qq A y t x / m x ) from tsum_congr h_simplify ];
  have h_summable : Summable (fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1) * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2)) := by
    have h_summable : Summable (fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1) ^ 2) := by
      have h_summable : Summable (fun x => (∑' z, m x * rate x z) * (qq A y t x / m x) ^ 2) := by
        have h_summable : Summable (fun x => (c₂ * Λ) * (qq A y t x / m x) ^ 2) := by
          exact Summable.mul_left _ ( phi_summable_sq A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht );
        refine' h_summable.of_nonneg_of_le ( fun x => mul_nonneg ( tsum_nonneg fun _ => mul_nonneg ( by linarith [ hmlb x ] ) ( hnn _ _ ) ) ( sq_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_right _ ( sq_nonneg _ ) );
        rw [ tsum_mul_left ] ; nlinarith [ hmlb x, hmub x, hexit x, show 0 ≤ ∑' z : ℤ, rate x z from tsum_nonneg fun _ => hnn _ _ ];
      have h_summable : ∀ x, Summable (fun z => m x * rate x z * (qq A y t x / m x) ^ 2) := by
        intro x
        have h_summable : Summable (fun z => rate x z) := by
          refine' summable_of_ne_finset_zero _;
          exact Finset.Icc ( x - ϱ ) ( x + ϱ );
          exact fun z hz => Classical.not_not.1 fun h => hz <| Finset.mem_Icc.2 ⟨ by cases abs_cases ( z - x ) <;> linarith [ hfr x z h ], by cases abs_cases ( z - x ) <;> linarith [ hfr x z h ] ⟩;
        exact Summable.mul_right _ ( h_summable.mul_left _ );
      rw [ summable_prod_of_nonneg ];
      · simp_all +decide [ tsum_mul_right ];
      · exact fun p => mul_nonneg ( mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn p.1 p.2 ) ) ( sq_nonneg _ );
    have h_summable : Summable (fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * (qq A y t p.2 / m p.2) ^ 2) := by
      convert h_summable.comp_injective ( show Function.Injective ( fun p : ℤ × ℤ => ( p.2, p.1 ) ) from fun p q h => by aesop ) using 1 ; aesop;
    have h_summable : Summable (fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1) * (qq A y t p.2 / m p.2)) := by
      have h_summable : Summable (fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * ((qq A y t p.1 / m p.1) ^ 2 + (qq A y t p.2 / m p.2) ^ 2) / 2) := by
        convert Summable.div_const ( Summable.add ‹Summable fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * ( qq A y t p.1 / m p.1 ) ^ 2› ‹Summable fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * ( qq A y t p.2 / m p.2 ) ^ 2› ) 2 using 2 ; ring;
      refine' .of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) h_summable;
      · exact mul_nonneg ( mul_nonneg ( mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn _ _ ) ) ( div_nonneg ( qq_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y p.1 t ht ) ( by linarith [ hmlb p.1 ] ) ) ) ( div_nonneg ( qq_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y p.2 t ht ) ( by linarith [ hmlb p.2 ] ) );
      · nlinarith only [ sq_nonneg ( qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2 ), show 0 ≤ m p.1 * rate p.1 p.2 by exact mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn p.1 p.2 ) ];
    convert ‹Summable fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * ( qq A y t p.1 / m p.1 ) ^ 2›.sub h_summable using 2 ; ring;
  have h_summable : ∑' p : ℤ × ℤ, m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2) * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2) = 2 * ∑' p : ℤ × ℤ, m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1) * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2) := by
    have h_summable : ∑' p : ℤ × ℤ, m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2) * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2) = ∑' p : ℤ × ℤ, m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1) * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2) + ∑' p : ℤ × ℤ, m p.1 * rate p.1 p.2 * (qq A y t p.2 / m p.2) * (qq A y t p.2 / m p.2 - qq A y t p.1 / m p.1) := by
      rw [ ← Summable.tsum_add ] ; congr ; ext p ; ring;
      · convert h_summable using 1;
      · convert h_summable.comp_injective ( show Function.Injective ( fun p : ℤ × ℤ => ( p.2, p.1 ) ) from fun p q h => by aesop ) using 1;
        ext ⟨x, z⟩; simp [hrev];
    rw [ h_summable, two_mul ];
    rw [ ← Equiv.tsum_eq ( Equiv.prodComm ℤ ℤ ) ] ; norm_num [ hrev ];
  simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm, tsum_neg, tsum_mul_left ];
  erw [ Summable.tsum_prod ];
  assumption

/-
Dropping to nearest-neighbour edges and using the conductance lower bound.
-/
lemma energyDeriv_le_grad (y : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    energyDeriv A rate m y t
      ≤ -(2 * δ) * (∑' x : ℤ, (qq A y t (x + 1) / m (x + 1) - qq A y t x / m x) ^ 2) := by
  rw [energyDeriv_eq A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht];
  have h_summable : Summable (fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2) ^ 2) := by
    have h_summable : Summable (fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1) ^ 2) := by
      have h_summable : Summable (fun x => (∑' z, m x * rate x z) * (qq A y t x / m x) ^ 2) := by
        have h_summable : Summable (fun x => (c₂ * Λ) * (qq A y t x / m x) ^ 2) := by
          exact Summable.mul_left _ ( phi_summable_sq A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht );
        refine' h_summable.of_nonneg_of_le ( fun x => mul_nonneg ( tsum_nonneg fun _ => mul_nonneg ( by linarith [ hmlb x ] ) ( hnn _ _ ) ) ( sq_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_right _ ( sq_nonneg _ ) );
        rw [ tsum_mul_left ] ; nlinarith [ hmlb x, hmub x, hexit x, show 0 ≤ ∑' z : ℤ, rate x z from tsum_nonneg fun _ => hnn _ _ ];
      rw [ summable_prod_of_nonneg ];
      · simp_all +decide [ tsum_mul_right, tsum_mul_left ];
        intro x;
        refine' summable_of_ne_finset_zero _;
        exact Finset.Icc ( x - ϱ ) ( x + ϱ );
        grind;
      · exact fun p => mul_nonneg ( mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn p.1 p.2 ) ) ( sq_nonneg _ );
    have h_summable : Summable (fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * (qq A y t p.2 / m p.2) ^ 2) := by
      convert h_summable.comp_injective ( show Function.Injective ( fun p : ℤ × ℤ => ( p.2, p.1 ) ) from fun p q h => by aesop ) using 1 ; aesop;
    refine' .of_nonneg_of_le ( fun p => mul_nonneg ( mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn p.1 p.2 ) ) ( sq_nonneg _ ) ) ( fun p => _ ) ( Summable.add ‹Summable fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * ( qq A y t p.1 / m p.1 ) ^ 2› ‹Summable fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * ( qq A y t p.2 / m p.2 ) ^ 2› |> Summable.mul_left 2 );
    nlinarith only [ sq_nonneg ( qq A y t p.1 / m p.1 + qq A y t p.2 / m p.2 ), show 0 ≤ m p.1 * rate p.1 p.2 by exact mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn p.1 p.2 ) ];
  have h_summable : ∑' p : ℤ × ℤ, m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2) ^ 2 ≥ ∑' x : ℤ, m x * rate x (x + 1) * (qq A y t x / m x - qq A y t (x + 1) / m (x + 1)) ^ 2 + ∑' x : ℤ, m (x + 1) * rate (x + 1) x * (qq A y t (x + 1) / m (x + 1) - qq A y t x / m x) ^ 2 := by
    have h_summable : ∑' p : ℤ × ℤ, m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2) ^ 2 ≥ ∑' p : ℤ × ℤ, (if p.2 = p.1 + 1 then m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2) ^ 2 else 0) + ∑' p : ℤ × ℤ, (if p.2 = p.1 - 1 then m p.1 * rate p.1 p.2 * (qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2) ^ 2 else 0) := by
      rw [ ← Summable.tsum_add ];
      · refine' Summable.tsum_le_tsum _ _ h_summable;
        · intro p; split_ifs <;> norm_num;
          · linarith;
          · exact mul_nonneg ( mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn _ _ ) ) ( sq_nonneg _ );
        · exact Summable.of_nonneg_of_le ( fun p => by split_ifs <;> nlinarith [ hnn p.1 p.2, show 0 ≤ m p.1 * rate p.1 p.2 by exact mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn p.1 p.2 ) ] ) ( fun p => by split_ifs <;> nlinarith [ hnn p.1 p.2, show 0 ≤ m p.1 * rate p.1 p.2 by exact mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn p.1 p.2 ) ] ) h_summable;
      · exact Summable.of_nonneg_of_le ( fun p => by split_ifs <;> nlinarith [ show 0 ≤ m p.1 * rate p.1 p.2 by exact mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn p.1 p.2 ) ] ) ( fun p => by split_ifs <;> nlinarith [ show 0 ≤ m p.1 * rate p.1 p.2 by exact mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn p.1 p.2 ) ] ) h_summable;
      · exact Summable.of_nonneg_of_le ( fun p => by split_ifs <;> nlinarith [ show 0 ≤ m p.1 * rate p.1 p.2 by exact mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn p.1 p.2 ) ] ) ( fun p => by split_ifs <;> nlinarith [ show 0 ≤ m p.1 * rate p.1 p.2 by exact mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn p.1 p.2 ) ] ) h_summable;
    convert h_summable using 2;
    · erw [ Summable.tsum_prod ];
      · exact tsum_congr fun x => by rw [ tsum_eq_single ( x + 1 ) ] <;> aesop;
      · refine' Summable.of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) ‹_›;
        · split_ifs <;> first | positivity | exact mul_nonneg ( mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn _ _ ) ) ( sq_nonneg _ ) ;
        · split_ifs <;> [ exact le_rfl; exact mul_nonneg ( mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn p.1 p.2 ) ) ( sq_nonneg _ ) ];
    · erw [ Summable.tsum_prod ];
      · rw [ ← Equiv.tsum_eq ( Equiv.addRight ( -1 ) ) ] ; norm_num;
        rfl;
      · refine' Summable.of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) ‹_›;
        · split_ifs <;> first | positivity | exact mul_nonneg ( mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn _ _ ) ) ( sq_nonneg _ ) ;
        · split_ifs <;> norm_num;
          exact mul_nonneg ( mul_nonneg ( by linarith [ hmlb p.1 ] ) ( hnn _ _ ) ) ( sq_nonneg _ );
  have h_summable : ∑' x : ℤ, m x * rate x (x + 1) * (qq A y t x / m x - qq A y t (x + 1) / m (x + 1)) ^ 2 ≥ δ * ∑' x : ℤ, (qq A y t (x + 1) / m (x + 1) - qq A y t x / m x) ^ 2 := by
    rw [ ← tsum_mul_left ] ; exact Summable.tsum_le_tsum ( fun x => by nlinarith only [ hcond x, sq_nonneg ( qq A y t x / m x - qq A y t ( x + 1 ) / m ( x + 1 ) ) ] ) ( by
      exact Summable.mul_left _ ( phi_summable_grad A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht ) ) ( by
      convert ‹Summable fun p : ℤ × ℤ => m p.1 * rate p.1 p.2 * ( qq A y t p.1 / m p.1 - qq A y t p.2 / m p.2 ) ^ 2›.comp_injective ( show Function.Injective ( fun x : ℤ => ( x, x + 1 ) ) from fun x y hxy => by simpa using hxy ) using 1 ) ;
  grind

/-
The Nash step: convert the gradient energy to a bound in terms of `energy`.
-/
lemma grad_nash (y : ℤ) (t : ℝ) (ht : 0 < t) :
    -(2 * δ) * (∑' x : ℤ, (qq A y t (x + 1) / m (x + 1) - qq A y t x / m x) ^ 2)
      ≤ -(kap δ c₁ c₂) * (energy A m y t) ^ 3 := by
  -- Let's set up some local notation for clarity.
  set G := ∑' x, (qq A y t (x + 1) / m (x + 1) - qq A y t x / m x) ^ 2
  set φ := fun x => qq A y t x / m x
  set S1 := ∑' x, abs (φ x)
  set S2 := ∑' x, (φ x) ^ 2
  set E := energy A m y t
  set kap := kap δ c₁ c₂;
  -- We need to show that $E^3 \leq c₂^3 S2^3$.
  suffices h_E_le : E ^ 3 ≤ c₂ ^ 3 * S2 ^ 3 by
    -- From `phi_summable_abs`, `phi_summable_sq`, `phi_summable_grad`, and by `qq_nonneg`, `qq_mass`, `hmlb`, `hmub`, `hc1`, `hδ`,
    have h_S1_bound : S1 ≤ 1 / c₁ := by
      have h_S1_bound : S1 ≤ ∑' x, (qq A y t x) / c₁ := by
        refine' Summable.tsum_le_tsum _ _ _;
        · intro x; rw [ abs_of_nonneg ( div_nonneg ( qq_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y x t ht.le ) ( by linarith [ hmlb x ] ) ) ] ; exact div_le_div_of_nonneg_left ( qq_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y x t ht.le ) ( by linarith [ hmlb x ] ) ( hmlb x ) ;
        · exact phi_summable_abs A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht.le;
        · exact Summable.mul_right _ ( qq_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t );
      rw [ tsum_div_const, qq_mass A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht.le ] at h_S1_bound ; aesop
    have h_S2_bound : S2 ^ 3 ≤ 4 * S1 ^ 4 * G := by
      apply TypeDDecouplingNash.nash_ineq;
      · exact phi_summable_abs A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht.le;
      · exact phi_summable_sq A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht.le;
      · exact phi_summable_grad A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht.le
    have h_E_bound : E ≤ c₂ * S2 := by
      convert Summable.tsum_le_tsum ( fun x => show ( qq A y t x ) ^ 2 / m x ≤ c₂ * ( qq A y t x / m x ) ^ 2 from ?_ ) ( show Summable fun x => ( qq A y t x ) ^ 2 / m x from ?_ ) ( show Summable fun x => c₂ * ( qq A y t x / m x ) ^ 2 from ?_ ) using 1;
      · rw [ tsum_mul_left ];
      · rw [ div_pow, mul_div, div_le_div_iff₀ ] <;> nlinarith only [ hmlb x, hmub x, show 0 < m x from lt_of_lt_of_le hc1 ( hmlb x ), show 0 ≤ qq A y t x ^ 2 from sq_nonneg _, show 0 ≤ m x * qq A y t x ^ 2 from mul_nonneg ( le_of_lt ( lt_of_lt_of_le hc1 ( hmlb x ) ) ) ( sq_nonneg _ ) ];
      · exact energy_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht.le;
      · exact Summable.mul_left _ ( phi_summable_sq A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht.le )
    have h_nonneg : 0 ≤ E ∧ 0 ≤ G ∧ 0 ≤ S2 := by
      exact ⟨ energy_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t, tsum_nonneg fun _ => sq_nonneg _, tsum_nonneg fun _ => sq_nonneg _ ⟩;
    -- From `h_S1_bound`, we have `4 * S1^4 ≤ 4 / c₁^4`.
    have h_S1_bound_pow : 4 * S1 ^ 4 ≤ 4 / c₁ ^ 4 := by
      convert mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( show 0 ≤ S1 from tsum_nonneg fun _ => abs_nonneg _ ) h_S1_bound 4 ) zero_le_four using 1 ; ring;
    -- From `h_S1_bound_pow`, we have `c₁^4 * S2^3 ≤ 4 * G`.
    have h_S2_bound_pow : c₁ ^ 4 * S2 ^ 3 ≤ 4 * G := by
      rw [ le_div_iff₀ ( by positivity ) ] at h_S1_bound_pow ; nlinarith [ pow_pos hc1 4 ] ;
    unfold kap;
    unfold TypeDDecouplingCKS.kap;
    field_simp;
    rw [ neg_le_neg_iff, div_le_iff₀ ] <;> nlinarith [ pow_pos hc1 4, pow_pos ( show 0 < c₂ by linarith [ hmlb 0, hmub 0 ] ) 3 ];
  -- By definition of $E$, we know that $E \leq c₂ S2$.
  have h_E_le : E ≤ c₂ * S2 := by
    convert Summable.tsum_le_tsum _ _ _ using 1;
    any_goals try infer_instance;
    rw [ ← tsum_mul_left ];
    · intro x; rw [ div_pow, mul_div ] ; rw [ div_le_div_iff₀ ] <;> try nlinarith [ hmlb x, hmub x ];
      nlinarith only [ show 0 ≤ qq A y t x ^ 2 * m x by exact mul_nonneg ( sq_nonneg _ ) ( by linarith [ hmlb x ] ), hmub x, hmlb x ];
    · exact energy_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht.le;
    · exact Summable.mul_left _ ( phi_summable_sq A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht.le );
  simpa only [ ← mul_pow ] using pow_le_pow_left₀ ( by exact energy_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ) h_E_le 3

/-- **Nash differential inequality (uniform in the start point).**  The energy
derivative satisfies `2 ∑ q q'/m ≤ -κ u³` with `κ = δ c₁⁴/(2 c₂³)`. -/
lemma energyDeriv_le (y : ℤ) (t : ℝ) (ht : 0 < t) :
    energyDeriv A rate m y t ≤ -(kap δ c₁ c₂) * (energy A m y t) ^ 3 :=
  le_trans
    (energyDeriv_le_grad A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht.le)
    (grad_nash A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y t ht)

/-- **Uniform on-diagonal energy decay.**  For all start points `y`,
`u^y(t) ≤ 1/√(2κ t)`. -/
lemma energy_decay (y : ℤ) (t : ℝ) (ht : 0 < t) :
    energy A m y t ≤ 1 / Real.sqrt (2 * kap δ c₁ c₂ * t) := by
  have hκ : 0 < kap δ c₁ c₂ := by
    have hc2 : 0 < c₂ := lt_of_lt_of_le hc1 (le_trans (hmlb 0) (hmub 0))
    unfold kap; positivity
  exact TypeDDecouplingNash.nash_ode_bound
    (fun s => energy A m y s) (fun s => energyDeriv A rate m y s) (kap δ c₁ c₂) hκ
    (fun s _ => energy_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y s)
    (fun s hs => energy_hasDerivAt A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y s hs.le)
    (fun s hs => energyDeriv_le A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond y s hs)
    t ht

/-
**Off-diagonal bound** via Chapman–Kolmogorov + reversibility +
Cauchy–Schwarz + the uniform decay: `q^0_{2t}(r) ≤ c₂/√(2κ t)`.
-/
lemma offdiag (r : ℤ) (t : ℝ) (ht : 0 < t) :
    qq A 0 (2 * t) r ≤ c₂ / Real.sqrt (2 * kap δ c₁ c₂ * t) := by
  -- Step 1: Use Chapman-Kolmogorov to express $q_{2t}(0, r)$.
  have h1 : qq A 0 (2 * t) r = ∑' z, qq A 0 t z * qq A z t r := by
    convert qq_CK A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond 0 r t t using 1 ; ring;
  -- Step 2: Use reversibility to rewrite the sum.
  have h2 : ∑' z, qq A 0 t z * qq A z t r = m r * ∑' z, (qq A 0 t z * qq A r t z) / m z := by
    rw [ ← tsum_mul_left ];
    refine' tsum_congr fun z => _;
    have := qq_reversible A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond z r t;
    grind +splitImp;
  -- Step 3: Apply Cauchy-Schwarz inequality to the sum.
  have h3 : ∑' z, (qq A 0 t z * qq A r t z) / m z ≤ Real.sqrt (∑' z, (qq A 0 t z)^2 / m z) * Real.sqrt (∑' z, (qq A r t z)^2 / m z) := by
    convert tsum_cauchy_schwarz ( fun z => qq A 0 t z / Real.sqrt ( m z ) ) ( fun z => qq A r t z / Real.sqrt ( m z ) ) _ _ _ using 1;
    · exact tsum_congr fun x => by rw [ div_mul_div_comm, Real.mul_self_sqrt ( by linarith [ hmlb x ] ) ] ;
    · simp +decide only [div_pow, Real.sq_sqrt (le_trans hc1.le (hmlb _))];
    · refine' Summable.of_nonneg_of_le ( fun z => _ ) ( fun z => _ ) ( Summable.add ( energy_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond 0 t ht.le ) ( energy_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond r t ht.le ) );
      · exact mul_nonneg ( div_nonneg ( qq_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond 0 z t ht.le ) ( Real.sqrt_nonneg _ ) ) ( div_nonneg ( qq_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond r z t ht.le ) ( Real.sqrt_nonneg _ ) );
      · ring_nf;
        rw [ inv_pow, Real.sq_sqrt ( by linarith [ hmlb z ] ) ] ; nlinarith only [ sq_nonneg ( qq A 0 t z - qq A r t z ), inv_nonneg.2 ( show 0 ≤ m z by linarith [ hmlb z ] ) ] ;
    · convert energy_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond 0 t ht.le using 1 ; ring;
      exact funext fun x => by rw [ inv_pow, Real.sq_sqrt ( by linarith [ hmlb x ] ) ] ;
    · convert energy_summable A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond r t ht.le using 1;
      exact funext fun x => by rw [ div_pow, Real.sq_sqrt ( by linarith [ hmlb x ] ) ] ;
  -- Step 4: Apply the energy decay bound to each term in the product.
  have h4 : Real.sqrt (∑' z, (qq A 0 t z)^2 / m z) ≤ 1 / Real.sqrt (Real.sqrt (2 * kap δ c₁ c₂ * t)) := by
    convert Real.sqrt_le_sqrt ( energy_decay A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond 0 t ht ) using 1 ; norm_num [ Real.sqrt_div_self ]
  have h5 : Real.sqrt (∑' z, (qq A r t z)^2 / m z) ≤ 1 / Real.sqrt (Real.sqrt (2 * kap δ c₁ c₂ * t)) := by
    convert Real.sqrt_le_sqrt ( energy_decay A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond r t ht ) using 1;
    norm_num;
  refine le_trans ( h1.le.trans ( h2.le.trans ( mul_le_mul_of_nonneg_left h3 <| by linarith [ hmlb r ] ) ) ) ?_;
  refine le_trans ( mul_le_mul_of_nonneg_left ( mul_le_mul h4 h5 ( by positivity ) ( by positivity ) ) ( by linarith [ hmlb r ] ) ) ?_ ; ring_nf ; norm_num [ ht.le ];
  norm_num [ mul_pow, Real.sqrt_nonneg ];
  exact mul_le_mul_of_nonneg_right ( hmub r ) ( by positivity )

end Semigroup

/-
Scalar Grönwall: a nonnegative bounded function on `[0,∞)` satisfying
`ρ s ≤ c ∫₀ˢ ρ` is identically zero.
-/
lemma gronwall_zero (ρ : ℝ → ℝ) (c M : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hcont : ContinuousOn ρ (Set.Ici 0))
    (hnn : ∀ s, 0 ≤ s → 0 ≤ ρ s)
    (hbd : ∀ s, 0 ≤ s → ρ s ≤ M)
    (hint : ∀ s, 0 ≤ s → ρ s ≤ c * ∫ u in (0:ℝ)..s, ρ u) :
    ∀ s, 0 ≤ s → ρ s = 0 := by
  intro s hs;
  -- Prove by induction on `n : ℕ` the bound `claim n : ρ s ≤ M * (c * s) ^ n / n.factorial`.
  have h_induction : ∀ n : ℕ, ∀ s ≥ 0, ρ s ≤ M * (c * s) ^ n / n.factorial := by
    intro n
    induction' n with n ih;
    · aesop;
    · intro s hs
      have h_integral : ∫ u in (0 : ℝ)..s, ρ u ≤ ∫ u in (0 : ℝ)..s, M * (c * u) ^ n / n.factorial := by
        apply_rules [ intervalIntegral.integral_mono_on ];
        · apply_rules [ ContinuousOn.intervalIntegrable, hcont ];
          simpa only [ Set.uIcc_of_le hs ] using hcont.mono ( Set.Icc_subset_Ici_self );
        · exact Continuous.intervalIntegrable ( by continuity ) _ _;
        · exact fun x hx => ih x hx.1;
      convert le_trans ( ‹∀ s ≥ 0, ρ s ≤ c * ∫ u in ( 0 : ℝ )..s, ρ u› s hs ) ( mul_le_mul_of_nonneg_left h_integral hc ) using 1 ; ring;
      norm_num [ Nat.add_comm 1 n, Nat.factorial_succ ] ; ring;
  -- Since $M * (c * s) ^ n / n.factorial$ tends to $0$ as $n$ tends to infinity, we have $\rho(s) \leq 0$.
  have h_lim : Filter.Tendsto (fun n : ℕ => M * (c * s) ^ n / Nat.factorial n) Filter.atTop (nhds 0) := by
    simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul M ( Real.summable_pow_div_factorial _ |> Summable.tendsto_atTop_zero );
  exact le_antisymm ( le_of_tendsto_of_tendsto' tendsto_const_nhds h_lim fun n => h_induction n s hs ) ( hnn s hs )

/-- Geometric weight `w x = (1/2)^{|x|}`. -/
noncomputable def gw (x : ℤ) : ℝ := (2:ℝ)⁻¹ ^ x.natAbs

lemma gw_pos (x : ℤ) : 0 < gw x := by unfold gw; positivity

lemma gw_summable : Summable gw := by
  unfold gw
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩ <;>
  · simp only [Int.natAbs_neg, Int.natAbs_natCast]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- Summability of the weighted absolute values of a bounded function. -/
lemma gu_summ (f : ℤ → ℝ) (M : ℝ) (hf : ∀ x, |f x| ≤ M) :
    Summable (fun x => gw x * |f x|) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hf 0)
  refine Summable.of_nonneg_of_le (fun x => mul_nonneg (gw_pos x).le (abs_nonneg _))
    (fun x => mul_le_mul_of_nonneg_left (hf x) (gw_pos x).le) ?_
  simpa [mul_comm] using gw_summable.mul_left M

/-
**Spatial weighted-ℓ¹ estimate for the generator** (drift/finite-range).
-/
lemma gu_spatial (rate : ℤ → ℤ → ℝ) (Λ : ℝ) (ϱ : ℕ)
    (hnn : ∀ x y, 0 ≤ rate x y)
    (hfr : ∀ x y, rate x y ≠ 0 → (y - x).natAbs ≤ ϱ)
    (hexit : ∀ x, ∑' y, rate x y ≤ Λ)
    (f : ℤ → ℝ) (hf : Summable (fun x => gw x * |f x|)) :
    (∑' x, gw x * |(∑' z, rate z x * f z) - (∑' z, rate x z) * f x|)
      ≤ (2 * Λ * (2:ℝ) ^ ϱ) * ∑' x, gw x * |f x| := by
  -- Apply the triangle inequality to the absolute value inside the sum.
  have h_triangle : ∀ x, abs ((∑' z, rate z x * f z) - (∑' z, rate x z) * f x) ≤ (∑' z, rate z x * abs (f z)) + (∑' z, rate x z) * abs (f x) := by
    intro x;
    refine' le_trans ( abs_sub _ _ ) ( add_le_add _ _ );
    · by_cases h : Summable ( fun z => rate z x * f z );
      · convert norm_tsum_le_tsum_norm _ <;> norm_num [ abs_mul, hnn ];
        any_goals tauto;
        · norm_num [ abs_mul, abs_of_nonneg ( hnn _ _ ) ];
        · exact h.norm;
      · rw [ tsum_eq_zero_of_not_summable h ] ; norm_num ; exact tsum_nonneg fun _ => mul_nonneg ( hnn _ _ ) ( abs_nonneg _ ) ;
    · rw [ abs_mul, abs_of_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ];
  -- Apply the triangle inequality to each term in the sum.
  have h_sum_triangle : ∑' x, gw x * abs ((∑' z, rate z x * f z) - (∑' z, rate x z) * f x) ≤ ∑' x, gw x * (∑' z, rate z x * abs (f z)) + ∑' x, gw x * (∑' z, rate x z) * abs (f x) := by
    rw [ ← Summable.tsum_add ];
    · refine' Summable.tsum_le_tsum _ _ _;
      · exact fun x => by nlinarith [ h_triangle x, show 0 ≤ gw x from by exact le_of_lt ( gw_pos x ) ] ;
      · refine' Summable.of_nonneg_of_le ( fun x => mul_nonneg ( gw_pos x |> le_of_lt ) ( abs_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_left ( h_triangle x ) ( gw_pos x |> le_of_lt ) ) _;
        have h_summable : Summable (fun x => gw x * (∑' z, rate z x * |f z|)) := by
          have h_summable : Summable (fun p : ℤ × ℤ => gw p.1 * rate p.2 p.1 * |f p.2|) := by
            have h_summable : Summable (fun p : ℤ × ℤ => rate p.2 p.1 * gw p.2 * |f p.2| * 2 ^ ϱ) := by
              have h_summable : Summable (fun p : ℤ × ℤ => rate p.2 p.1 * gw p.2 * |f p.2|) := by
                have h_summable : ∀ z, Summable (fun x => rate z x * gw z * |f z|) := by
                  intro z
                  have h_summable : Summable (fun x => rate z x) := by
                    refine' summable_of_ne_finset_zero _;
                    exacts [ Finset.Icc ( z - ϱ ) ( z + ϱ ), fun x hx => Classical.not_not.1 fun hx' => hx <| Finset.mem_Icc.2 ⟨ by cases abs_cases ( x - z ) <;> linarith [ hfr z x hx' ], by cases abs_cases ( x - z ) <;> linarith [ hfr z x hx' ] ⟩ ]
                  exact Summable.mul_right _ ( Summable.mul_right _ h_summable )
                have h_summable : Summable (fun p : ℤ × ℤ => rate p.1 p.2 * gw p.1 * |f p.1|) := by
                  have h_summable : Summable (fun z => ∑' x, rate z x * gw z * |f z|) := by
                    simp_all +decide [ tsum_mul_right, tsum_mul_left ];
                    refine' .of_nonneg_of_le ( fun z => mul_nonneg ( mul_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ( by exact le_of_lt ( gw_pos z ) ) ) ( abs_nonneg _ ) ) ( fun z => mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( hexit z ) ( by exact le_of_lt ( gw_pos z ) ) ) ( abs_nonneg _ ) ) _;
                    simpa only [ mul_assoc ] using hf.mul_left Λ
                  rw [ summable_prod_of_nonneg ];
                  · aesop;
                  · exact fun p => mul_nonneg ( mul_nonneg ( hnn _ _ ) ( by exact le_of_lt ( gw_pos _ ) ) ) ( abs_nonneg _ );
                convert h_summable.comp_injective ( show Function.Injective ( fun p : ℤ × ℤ => ( p.2, p.1 ) ) from fun p q h => by aesop ) using 1;
              exact h_summable.mul_right _;
            refine' .of_nonneg_of_le ( fun p => mul_nonneg ( mul_nonneg ( gw_pos p.1 |> le_of_lt ) ( hnn _ _ ) ) ( abs_nonneg _ ) ) ( fun p => _ ) h_summable;
            by_cases h : rate p.2 p.1 = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
            have := TypeDDecouplingSemigroup.weight_ratio ( 2⁻¹ : ℝ ) ( by norm_num ) ( by norm_num ) ϱ p.1 p.2 ; simp_all +decide [ gw ];
            exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left this ( abs_nonneg _ ) ) ( hnn _ _ );
          have h_summable : ∀ x, gw x * ∑' z, rate z x * |f z| = ∑' z, gw x * rate z x * |f z| := by
            exact fun x => by rw [ ← tsum_mul_left ] ; exact tsum_congr fun z => by ring;
          rw [ summable_prod_of_nonneg ] at *;
          · aesop;
          · exact fun p => mul_nonneg ( mul_nonneg ( gw_pos _ |> le_of_lt ) ( hnn _ _ ) ) ( abs_nonneg _ );
        convert h_summable.add ( show Summable fun x => gw x * ( ∑' z, rate x z ) * |f x| from ?_ ) using 2 ; ring;
        refine' .of_nonneg_of_le ( fun x => mul_nonneg ( mul_nonneg ( by exact_mod_cast pow_nonneg ( by norm_num : ( 0 : ℝ ) ≤ 2⁻¹ ) _ ) ( tsum_nonneg fun _ => hnn _ _ ) ) ( abs_nonneg _ ) ) ( fun x => _ ) ( hf.mul_left Λ );
        nlinarith [ hexit x, show 0 ≤ gw x * |f x| by exact mul_nonneg ( by exact_mod_cast pow_nonneg ( by norm_num : ( 0 : ℝ ) ≤ 2⁻¹ ) _ ) ( abs_nonneg _ ) ];
      · refine' Summable.add _ _;
        · have h_summable : Summable (fun p : ℤ × ℤ => gw p.1 * rate p.2 p.1 * abs (f p.2)) := by
            have h_summable : Summable (fun p : ℤ × ℤ => rate p.2 p.1 * gw p.2 * |f p.2| * 2 ^ ϱ) := by
              have h_summable : Summable (fun p : ℤ × ℤ => rate p.2 p.1 * gw p.2 * |f p.2|) := by
                have h_summable : ∀ z, Summable (fun x => rate z x * gw z * |f z|) := by
                  intro z
                  have h_summable : Summable (fun x => rate z x) := by
                    refine' summable_of_ne_finset_zero _;
                    exacts [ Finset.Icc ( z - ϱ ) ( z + ϱ ), fun x hx => Classical.not_not.1 fun hx' => hx <| Finset.mem_Icc.2 ⟨ by cases abs_cases ( x - z ) <;> linarith [ hfr z x hx' ], by cases abs_cases ( x - z ) <;> linarith [ hfr z x hx' ] ⟩ ]
                  exact Summable.mul_right _ ( Summable.mul_right _ h_summable )
                have h_summable : Summable (fun p : ℤ × ℤ => rate p.1 p.2 * gw p.1 * |f p.1|) := by
                  have h_summable : Summable (fun z => ∑' x, rate z x * gw z * |f z|) := by
                    simp_all +decide [ tsum_mul_right, tsum_mul_left ];
                    refine' .of_nonneg_of_le ( fun z => mul_nonneg ( mul_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ( by exact le_of_lt ( gw_pos z ) ) ) ( abs_nonneg _ ) ) ( fun z => mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( hexit z ) ( by exact le_of_lt ( gw_pos z ) ) ) ( abs_nonneg _ ) ) _;
                    simpa only [ mul_assoc ] using hf.mul_left Λ
                  rw [ summable_prod_of_nonneg ];
                  · aesop;
                  · exact fun p => mul_nonneg ( mul_nonneg ( hnn _ _ ) ( by exact le_of_lt ( gw_pos _ ) ) ) ( abs_nonneg _ );
                convert h_summable.comp_injective ( show Function.Injective ( fun p : ℤ × ℤ => ( p.2, p.1 ) ) from fun p q h => by aesop ) using 1;
              exact h_summable.mul_right _;
            refine' .of_nonneg_of_le ( fun p => mul_nonneg ( mul_nonneg ( gw_pos p.1 |> le_of_lt ) ( hnn _ _ ) ) ( abs_nonneg _ ) ) ( fun p => _ ) h_summable;
            by_cases h : rate p.2 p.1 = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
            have := TypeDDecouplingSemigroup.weight_ratio ( 2⁻¹ : ℝ ) ( by norm_num ) ( by norm_num ) ϱ p.1 p.2 ; simp_all +decide [ gw ];
            exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left this ( abs_nonneg _ ) ) ( hnn _ _ );
          convert h_summable using 1;
          constructor <;> intro h <;> rw [ summable_prod_of_nonneg ] at * <;> norm_num at *;
          any_goals exact fun p => mul_nonneg ( mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( hnn _ _ ) ) ( abs_nonneg _ );
          · exact h_summable;
          · convert h.2 using 1;
            exact funext fun x => by rw [ ← tsum_mul_left ] ; exact tsum_congr fun y => by ring;
        · refine' Summable.of_nonneg_of_le ( fun x => mul_nonneg ( mul_nonneg ( by exact le_of_lt ( gw_pos x ) ) ( tsum_nonneg fun _ => hnn _ _ ) ) ( abs_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( hexit x ) ( by exact le_of_lt ( gw_pos x ) ) ) ( abs_nonneg _ ) ) _;
          convert hf.mul_left Λ using 2 ; ring;
    · have h_summable : Summable (fun p : ℤ × ℤ => gw p.1 * rate p.2 p.1 * |f p.2|) := by
        have h_summable : Summable (fun p : ℤ × ℤ => rate p.2 p.1 * gw p.2 * |f p.2| * 2 ^ ϱ) := by
          have h_summable : Summable (fun p : ℤ × ℤ => rate p.2 p.1 * gw p.2 * |f p.2|) := by
            have h_summable : ∀ z, Summable (fun x => rate z x * gw z * |f z|) := by
              intro z
              have h_summable : Summable (fun x => rate z x) := by
                refine' summable_of_ne_finset_zero _;
                exacts [ Finset.Icc ( z - ϱ ) ( z + ϱ ), fun x hx => Classical.not_not.1 fun hx' => hx <| Finset.mem_Icc.2 ⟨ by cases abs_cases ( x - z ) <;> linarith [ hfr z x hx' ], by cases abs_cases ( x - z ) <;> linarith [ hfr z x hx' ] ⟩ ]
              exact Summable.mul_right _ ( Summable.mul_right _ h_summable )
            have h_summable : Summable (fun p : ℤ × ℤ => rate p.1 p.2 * gw p.1 * |f p.1|) := by
              have h_summable : Summable (fun z => ∑' x, rate z x * gw z * |f z|) := by
                simp_all +decide [ tsum_mul_right, tsum_mul_left ];
                refine' .of_nonneg_of_le ( fun z => mul_nonneg ( mul_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ( by exact le_of_lt ( gw_pos z ) ) ) ( abs_nonneg _ ) ) ( fun z => mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( hexit z ) ( by exact le_of_lt ( gw_pos z ) ) ) ( abs_nonneg _ ) ) _;
                simpa only [ mul_assoc ] using hf.mul_left Λ
              rw [ summable_prod_of_nonneg ];
              · aesop;
              · exact fun p => mul_nonneg ( mul_nonneg ( hnn _ _ ) ( by exact le_of_lt ( gw_pos _ ) ) ) ( abs_nonneg _ );
            convert h_summable.comp_injective ( show Function.Injective ( fun p : ℤ × ℤ => ( p.2, p.1 ) ) from fun p q h => by aesop ) using 1;
          exact h_summable.mul_right _;
        refine' .of_nonneg_of_le ( fun p => mul_nonneg ( mul_nonneg ( gw_pos p.1 |> le_of_lt ) ( hnn _ _ ) ) ( abs_nonneg _ ) ) ( fun p => _ ) h_summable;
        by_cases h : rate p.2 p.1 = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        have := TypeDDecouplingSemigroup.weight_ratio ( 2⁻¹ : ℝ ) ( by norm_num ) ( by norm_num ) ϱ p.1 p.2 ; simp_all +decide [ gw ];
        exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left this ( abs_nonneg _ ) ) ( hnn _ _ );
      have h_summable : ∀ x, gw x * ∑' z, rate z x * |f z| = ∑' z, gw x * rate z x * |f z| := by
        exact fun x => by rw [ ← tsum_mul_left ] ; exact tsum_congr fun z => by ring;
      rw [ summable_prod_of_nonneg ] at *;
      · aesop;
      · exact fun p => mul_nonneg ( mul_nonneg ( gw_pos _ |> le_of_lt ) ( hnn _ _ ) ) ( abs_nonneg _ );
    · refine' .of_nonneg_of_le ( fun x => mul_nonneg ( mul_nonneg ( gw_pos x |> le_of_lt ) ( tsum_nonneg fun _ => hnn _ _ ) ) ( abs_nonneg _ ) ) ( fun x => _ ) ( hf.mul_left Λ );
      nlinarith [ hexit x, show 0 ≤ gw x * |f x| by exact mul_nonneg ( gw_pos x |> le_of_lt ) ( abs_nonneg _ ) ];
  -- Apply the weight ratio inequality to the first sum.
  have h_first_sum : ∑' x, gw x * (∑' z, rate z x * abs (f z)) ≤ 2 ^ ϱ * Λ * ∑' x, gw x * abs (f x) := by
    have h_first_sum : ∀ z, ∑' x, gw x * rate z x ≤ 2 ^ ϱ * gw z * Λ := by
      intro z
      have h_weight_ratio_step : ∀ x, rate z x ≠ 0 → gw x ≤ 2 ^ ϱ * gw z := by
        intro x hx; specialize hfr z x hx; unfold gw; norm_num;
        have := TypeDDecouplingSemigroup.weight_ratio ( 1 / 2 ) ( by norm_num ) ( by norm_num ) ϱ x z hfr; norm_num at * ; linarith;
      have h_weight_ratio_step : ∑' x, gw x * rate z x ≤ ∑' x, (2 ^ ϱ * gw z) * rate z x := by
        refine' Summable.tsum_le_tsum _ _ _;
        · exact fun x => if hx : rate z x = 0 then by norm_num [ hx ] else mul_le_mul_of_nonneg_right ( h_weight_ratio_step x hx ) ( hnn _ _ );
        · refine' summable_of_ne_finset_zero _;
          exact Finset.Icc ( z - ϱ ) ( z + ϱ );
          grind;
        · refine' summable_of_ne_finset_zero _;
          exact Finset.Icc ( z - ϱ ) ( z + ϱ );
          grind;
      simp_all +decide [ tsum_mul_left ];
      exact h_weight_ratio_step.trans ( mul_le_mul_of_nonneg_left ( hexit z ) ( mul_nonneg ( pow_nonneg zero_le_two _ ) ( by unfold gw; positivity ) ) );
    have h_first_sum : ∑' x, gw x * (∑' z, rate z x * abs (f z)) = ∑' z, abs (f z) * (∑' x, gw x * rate z x) := by
      simp +decide only [← tsum_mul_left, mul_comm, mul_left_comm];
      rw [ ← Summable.tsum_comm ] ; congr ; ext ; congr ; ext ; ring;
      have h_summable : Summable (fun p : ℤ × ℤ => rate p.2 p.1 * abs (f p.2) * gw p.1) := by
        have h_summable : ∀ z, Summable (fun x => rate z x * abs (f z) * gw x) := by
          intro z
          have h_summable : Summable (fun x => rate z x * gw x) := by
            refine' summable_of_ne_finset_zero _;
            exact Finset.Icc ( z - ϱ ) ( z + ϱ );
            grind;
          convert h_summable.mul_left |f z| using 2 ; ring
        have h_summable : Summable (fun p : ℤ × ℤ => rate p.1 p.2 * abs (f p.1) * gw p.2) := by
          have h_summable : ∀ z, Summable (fun x => rate z x * abs (f z) * gw x) := h_summable
          have h_summable : Summable (fun z => ∑' x, rate z x * abs (f z) * gw x) := by
            have h_summable : ∀ z, ∑' x, rate z x * abs (f z) * gw x ≤ 2 ^ ϱ * gw z * Λ * abs (f z) := by
              intro z; specialize h_first_sum z; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, tsum_mul_left ] ;
              convert mul_le_mul_of_nonneg_left h_first_sum ( abs_nonneg ( f z ) ) using 1 <;> ring;
              rw [ ← tsum_mul_left ] ; exact tsum_congr fun x => by ring;
            refine' Summable.of_nonneg_of_le ( fun z => tsum_nonneg fun x => mul_nonneg ( mul_nonneg ( hnn _ _ ) ( abs_nonneg _ ) ) ( by exact le_of_lt ( gw_pos _ ) ) ) ( fun z => h_summable z ) _;
            convert hf.mul_left ( 2 ^ ϱ * Λ ) using 2 ; ring
          rw [ summable_prod_of_nonneg ];
          · aesop;
          · exact fun p => mul_nonneg ( mul_nonneg ( hnn _ _ ) ( abs_nonneg _ ) ) ( gw_pos _ |> le_of_lt );
        convert h_summable.comp_injective ( show Function.Injective ( fun p : ℤ × ℤ => ( p.2, p.1 ) ) from fun p q h => by aesop ) using 1;
      exact h_summable;
    rw [ h_first_sum, ← tsum_mul_left ];
    refine' Summable.tsum_le_tsum _ _ _;
    · intro z; convert mul_le_mul_of_nonneg_left ( ‹∀ z, ∑' x, gw x * rate z x ≤ 2 ^ ϱ * gw z * Λ› z ) ( abs_nonneg ( f z ) ) using 1 ; ring;
    · refine' Summable.of_nonneg_of_le ( fun z => mul_nonneg ( abs_nonneg _ ) ( tsum_nonneg fun x => mul_nonneg ( by exact ( show 0 ≤ gw x from by unfold gw; positivity ) ) ( hnn _ _ ) ) ) ( fun z => mul_le_mul_of_nonneg_left ( ‹∀ z, ∑' x, gw x * rate z x ≤ 2 ^ ϱ * gw z * Λ› z ) ( abs_nonneg _ ) ) _;
      convert hf.mul_left ( 2 ^ ϱ * Λ ) using 2 ; ring;
    · exact Summable.mul_left _ hf;
  -- Apply the weight ratio inequality to the second sum.
  have h_second_sum : ∑' x, gw x * (∑' z, rate x z) * abs (f x) ≤ Λ * ∑' x, gw x * abs (f x) := by
    rw [ ← tsum_mul_left ] ; exact Summable.tsum_le_tsum ( fun x => by nlinarith only [ hexit x, show 0 ≤ gw x * |f x| by exact mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( abs_nonneg _ ), show 0 ≤ gw x by exact pow_nonneg ( by norm_num ) _ ] ) ( by
                                                                                                                                                                                                        refine' .of_nonneg_of_le ( fun x => mul_nonneg ( mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( tsum_nonneg fun _ => hnn _ _ ) ) ( abs_nonneg _ ) ) ( fun x => _ ) ( hf.mul_left Λ );
                                                                                                                                                                                                        nlinarith only [ hexit x, show 0 ≤ gw x * |f x| by exact mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( abs_nonneg _ ), show 0 ≤ gw x by exact pow_nonneg ( by norm_num ) _ ] ) ( by
                                                                                                                                                                                                        exact hf.mul_left _ ) ;
  refine le_trans h_sum_triangle <| le_trans ( add_le_add h_first_sum h_second_sum ) ?_;
  nlinarith [ show 0 ≤ Λ * ∑' x : ℤ, gw x * |f x| by exact mul_nonneg ( show 0 ≤ Λ by exact le_trans ( tsum_nonneg fun _ => hnn 0 _ ) ( hexit 0 ) ) ( tsum_nonneg fun _ => mul_nonneg ( by exact le_of_lt ( gw_pos _ ) ) ( abs_nonneg _ ) ), show ( 2 : ℝ ) ^ ϱ ≥ 1 by exact one_le_pow₀ ( by norm_num ) ]

/-
Continuity of the weighted mass.
-/
lemma gu_cont (r : ℝ → ℤ → ℝ) (M : ℝ)
    (hrc : ∀ x, Continuous (fun s => r s x))
    (hrbd : ∀ s, 0 ≤ s → ∀ x, |r s x| ≤ M) :
    ContinuousOn (fun s => ∑' x, gw x * |r s x|) (Set.Ici 0) := by
  refine' continuousOn_tsum _ _ _;
  refine' fun x => gw x * M;
  · exact fun x => ContinuousOn.mul continuousOn_const ( ContinuousOn.abs ( hrc x |> Continuous.continuousOn ) );
  · exact Summable.mul_right _ ( by simpa [ gw ] using gw_summable );
  · exact fun n x hx => by rw [ Real.norm_of_nonneg ( mul_nonneg ( by exact le_of_lt ( by exact pow_pos ( by norm_num ) _ ) ) ( abs_nonneg _ ) ) ] ; exact mul_le_mul_of_nonneg_left ( hrbd x hx n ) ( by exact le_of_lt ( by exact pow_pos ( by norm_num ) _ ) ) ;

end TypeDDecouplingCKS
