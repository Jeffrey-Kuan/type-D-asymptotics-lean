import Mathlib

/-!
# Abstract analysis for `lem_free`: the discrete Nash inequality on `ℤ` and Nash's ODE

This file collects the *library-clean, self-contained* analytic inputs of the Nash/CKS
proof of the on-diagonal heat-kernel bound (`lem_free` in `TypeDDecouplingLCLT.lean`):

* **Tier 1 — the one-dimensional discrete Nash inequality.**  For summable `f : ℤ → ℝ`,
  with `‖∇f‖₂² = ∑ₓ (f(x+1) − f(x))²`,
  - `agmon_le` : `f(x)² ≤ 2 ‖f‖₂ ‖∇f‖₂`  (the elementary 1-D Agmon/Sobolev bound), and
  - `nash_ineq` : `‖f‖₂⁶ ≤ 4 ‖f‖₁⁴ ‖∇f‖₂²`.

* **Tier 2 (analytic core) — the Nash ODE comparison.**  A nonincreasing `u ≥ 0` on
  `(0,∞)` with `u' ≤ −κ u³` obeys `u(t) ≤ 1/√(2κ t)`.

Nothing here refers to the probabilistic structure; these are pure inequalities, proved
outright (no `sorry`, standard axioms only).
-/

open scoped BigOperators Topology

namespace TypeDDecouplingNash

/-! ## Tier 1: the discrete Agmon and Nash inequalities on `ℤ` -/

/-
**1-D discrete Agmon bound.** For summable-square `f : ℤ → ℝ` with summable gradient,
`f(x)² ≤ 2 √(∑ f²) √(∑ (Δf)²)` for every `x`, where `Δf(y) = f(y+1) − f(y)`.

*Proof.* Telescoping, `f(x)² = ∑_{y ≤ x} (f(y)² − f(y−1)²)
= ∑_{y ≤ x} (f(y) + f(y−1))(f(y) − f(y−1))`, using `f → 0` at `−∞`
(from square-summability).  Bound the partial sum by the full sum of absolute values and
apply Cauchy–Schwarz together with `(a+b)² ≤ 2a² + 2b²`.
-/
lemma agmon_le (f : ℤ → ℝ)
    (hf2 : Summable (fun x : ℤ => (f x) ^ 2))
    (hg2 : Summable (fun x : ℤ => (f (x + 1) - f x) ^ 2)) (x : ℤ) :
    (f x) ^ 2 ≤ 2 * Real.sqrt (∑' y : ℤ, (f y) ^ 2)
        * Real.sqrt (∑' y : ℤ, (f (y + 1) - f y) ^ 2) := by
  have h_sum_ineq : (f x)^2 ≤ (∑' y : ℤ, |f y - f (y - 1)| * |f y + f (y - 1)|) := by
    have h_sum_ineq : (f x)^2 = ∑' n : ℕ, ((f (x - n))^2 - (f (x - n - 1))^2) := by
      have h_sum_ineq : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, ((f (x - k))^2 - (f (x - k - 1))^2)) Filter.atTop (nhds ((f x)^2)) := by
        have h_sum_ineq : Filter.Tendsto (fun n : ℕ => f (x - n)^2) Filter.atTop (nhds 0) := by
          convert hf2.comp_injective ( show Function.Injective ( fun n : ℕ => x - n ) from fun a b h => by simpa using h ) |> Summable.tendsto_atTop_zero using 1;
        convert h_sum_ineq.const_sub ( f x ^ 2 ) using 2 <;> norm_num [ sub_sub ];
        induction ‹_› <;> norm_num [ Finset.sum_range_succ ] at * ; linarith;
      refine' tendsto_nhds_unique h_sum_ineq ( Summable.hasSum _ |> HasSum.tendsto_sum_nat );
      exact Summable.sub ( hf2.comp_injective fun a b h => by simpa using h ) ( hf2.comp_injective fun a b h => by simpa using h );
    have h_sum_ineq : ∑' n : ℕ, |(f (x - n))^2 - (f (x - n - 1))^2| ≤ ∑' y : ℤ, |f y - f (y - 1)| * |f y + f (y - 1)| := by
      have h_sum_ineq : ∑' n : ℕ, |(f (x - n))^2 - (f (x - n - 1))^2| ≤ ∑' y : ℤ, |(f y)^2 - (f (y - 1))^2| := by
        have h_sum_ineq : Summable (fun y : ℤ => |(f y)^2 - (f (y - 1))^2|) := by
          exact Summable.abs ( hf2.sub ( hf2.comp_injective ( sub_left_injective ) ) );
        have h_sum_ineq : ∑' n : ℕ, |(f (x - n))^2 - (f (x - n - 1))^2| ≤ ∑' y : ℤ, |(f y)^2 - (f (y - 1))^2| := by
          have h_sum_ineq : ∀ N : ℕ, ∑ n ∈ Finset.range N, |(f (x - n))^2 - (f (x - n - 1))^2| ≤ ∑' y : ℤ, |(f y)^2 - (f (y - 1))^2| := by
            intro N
            have h_sum_ineq : ∑ n ∈ Finset.range N, |(f (x - n))^2 - (f (x - n - 1))^2| ≤ ∑ y ∈ Finset.image (fun n : ℕ => x - n) (Finset.range N), |(f y)^2 - (f (y - 1))^2| := by
              rw [ Finset.sum_image ] ; aesop;
            exact h_sum_ineq.trans ( Summable.sum_le_tsum _ ( fun _ _ => abs_nonneg _ ) ‹_› )
          contrapose! h_sum_ineq;
          exact ( Summable.hasSum ( show Summable _ from by exact ( by { by_contra h; rw [ tsum_eq_zero_of_not_summable h ] at h_sum_ineq; linarith [ show 0 ≤ ∑' y : ℤ, |f y ^ 2 - f ( y - 1 ) ^ 2| from tsum_nonneg fun _ => abs_nonneg _ ] } ) ) ) |> fun h => h.tendsto_sum_nat.eventually ( lt_mem_nhds h_sum_ineq ) |> fun h => h.exists;
        convert h_sum_ineq using 1;
      exact h_sum_ineq.trans_eq ( tsum_congr fun y => by rw [ ← abs_mul ] ; ring );
    refine' le_trans _ h_sum_ineq;
    rw [ ‹f x ^ 2 = ∑' n : ℕ, ( f ( x - n ) ^ 2 - f ( x - n - 1 ) ^ 2 ) › ];
    refine' le_of_abs_le _;
    by_cases h : Summable ( fun n : ℕ => f ( x - n ) ^ 2 - f ( x - n - 1 ) ^ 2 );
    · convert norm_tsum_le_tsum_norm _ <;> norm_num;
      any_goals tauto;
      exact h.norm;
    · rw [ tsum_eq_zero_of_not_summable h ] ; norm_num;
      exact tsum_nonneg fun _ => abs_nonneg _;
  have h_cauchy_schwarz : (∑' y : ℤ, |f y - f (y - 1)| * |f y + f (y - 1)|) ≤ Real.sqrt (∑' y : ℤ, (f y - f (y - 1))^2) * Real.sqrt (∑' y : ℤ, (f y + f (y - 1))^2) := by
    have h_cauchy_schwarz : ∀ (u v : ℤ → ℝ), Summable (fun y => u y ^ 2) → Summable (fun y => v y ^ 2) → (∑' y : ℤ, u y * v y) ^ 2 ≤ (∑' y : ℤ, u y ^ 2) * (∑' y : ℤ, v y ^ 2) := by
      intros u v hu hv;
      have h_cauchy_schwarz : ∀ (u v : ℤ → ℝ), Summable (fun y => u y ^ 2) → Summable (fun y => v y ^ 2) → ∀ (s : Finset ℤ), (∑ y ∈ s, u y * v y) ^ 2 ≤ (∑ y ∈ s, u y ^ 2) * (∑ y ∈ s, v y ^ 2) := by
        exact fun u v _ _ s => Finset.sum_mul_sq_le_sq_mul_sq s u v
      have h_cauchy_schwarz : Filter.Tendsto (fun s : Finset ℤ => (∑ y ∈ s, u y * v y) ^ 2) Filter.atTop (nhds ((∑' y : ℤ, u y * v y) ^ 2)) := by
        refine' Filter.Tendsto.pow _ _;
        refine' Summable.hasSum _;
        have h_cauchy_schwarz : Summable (fun y => |u y * v y|) := by
          exact Summable.of_nonneg_of_le ( fun y => abs_nonneg _ ) ( fun y => by rw [ abs_mul ] ; exact by nlinarith only [ sq_nonneg ( |u y| - |v y| ), abs_mul_abs_self ( u y ), abs_mul_abs_self ( v y ) ] ) ( hu.add hv );
        exact h_cauchy_schwarz.of_abs;
      exact le_of_tendsto_of_tendsto' h_cauchy_schwarz ( Filter.Tendsto.mul ( hu.hasSum ) ( hv.hasSum ) ) fun s => by aesop;
    convert Real.le_sqrt_of_sq_le ( h_cauchy_schwarz ( fun y => |f y - f ( y - 1 )| ) ( fun y => |f y + f ( y - 1 )| ) ?_ ?_ ) using 1 <;> norm_num [ abs_mul ];
    · rw [ Real.sqrt_mul <| tsum_nonneg fun _ => sq_nonneg _ ];
    · convert hg2.comp_injective ( sub_left_injective : Function.Injective ( fun y : ℤ => y - 1 ) ) using 1;
      exact funext fun x => by rw [ Function.comp_apply ] ; ring;
    · have h_summable : Summable (fun y => (f y)^2 + (f (y - 1))^2) := by
        exact Summable.add hf2 ( hf2.comp_injective ( sub_left_injective ) );
      refine' .of_nonneg_of_le ( fun y => sq_nonneg _ ) ( fun y => _ ) ( h_summable.mul_left 2 );
      linarith [ sq_nonneg ( f y - f ( y - 1 ) ) ];
  have h_sum_bound : (∑' y : ℤ, (f y + f (y - 1))^2) ≤ 4 * (∑' y : ℤ, (f y)^2) := by
    have h_sum_bound : (∑' y : ℤ, (f y + f (y - 1))^2) ≤ (∑' y : ℤ, 2 * (f y)^2 + ∑' y : ℤ, 2 * (f (y - 1))^2) := by
      rw [ ← Summable.tsum_add ];
      · refine' Summable.tsum_le_tsum _ _ _;
        · exact fun i => by linarith [ sq_nonneg ( f i - f ( i - 1 ) ) ] ;
        · have h_sum_bound : Summable (fun y : ℤ => (f y)^2 + (f (y - 1))^2) := by
            exact Summable.add hf2 ( hf2.comp_injective ( sub_left_injective ) );
          refine' .of_nonneg_of_le ( fun y => sq_nonneg _ ) ( fun y => _ ) ( h_sum_bound.mul_left 2 );
          exact add_sq_le
        · exact Summable.add ( hf2.mul_left _ ) ( hf2.mul_left _ |> Summable.comp_injective <| sub_left_injective );
      · exact hf2.mul_left 2;
      · exact Summable.mul_left _ ( hf2.comp_injective ( sub_left_injective ) );
    convert h_sum_bound using 1 ; norm_num [ tsum_mul_left, tsum_mul_right ] ; ring;
    rw [ show ( ∑' x : ℤ, f ( -1 + x ) ^ 2 ) = ∑' x : ℤ, f x ^ 2 from Equiv.tsum_eq ( Equiv.addLeft ( -1 ) ) fun x => f x ^ 2 ] ; ring;
  convert h_sum_ineq.trans ( h_cauchy_schwarz.trans _ ) using 1;
  convert mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt h_sum_bound ) ( Real.sqrt_nonneg ( ∑' y : ℤ, ( f y - f ( y - 1 ) ) ^ 2 ) ) using 1 ; ring;
  rw [ show ( ∑' y : ℤ, ( - ( f ( 1 + y ) * f y * 2 ) + f ( 1 + y ) ^ 2 + f y ^ 2 ) ) = ( ∑' y : ℤ, ( - ( f y * f ( -1 + y ) * 2 ) + f y ^ 2 + f ( -1 + y ) ^ 2 ) ) by rw [ ← Equiv.tsum_eq ( Equiv.addRight ( -1 ) ) ] ; norm_num [ add_comm, add_left_comm, add_assoc ] ] ; norm_num ; ring;

/-
**1-D discrete Nash inequality.** For `f : ℤ → ℝ` in `ℓ¹ ∩ ℓ²` with summable gradient,
`(∑ f²)³ ≤ 4 (∑ |f|)⁴ (∑ (Δf)²)`.

*Proof.* From `agmon_le`, `|f(x)| ≤ M := √(2√U√G)` for all `x`, hence
`U = ∑ f² = ∑ |f|·|f| ≤ M ∑ |f| = M·L`; squaring gives `U² ≤ 2√U√G·L²`, i.e.
`U⁴ ≤ 4 U G L⁴`, and therefore `U³ ≤ 4 L⁴ G`.
-/
lemma nash_ineq (f : ℤ → ℝ)
    (hf1 : Summable (fun x : ℤ => |f x|))
    (hf2 : Summable (fun x : ℤ => (f x) ^ 2))
    (hg2 : Summable (fun x : ℤ => (f (x + 1) - f x) ^ 2)) :
    (∑' x : ℤ, (f x) ^ 2) ^ 3
      ≤ 4 * (∑' x : ℤ, |f x|) ^ 4 * (∑' x : ℤ, (f (x + 1) - f x) ^ 2) := by
  -- Let $U = \sum' x, f x^2$, $L = \sum' x, |f x|$, and $G = \sum' x, (f (x + 1) - f x)^2$.
  set U := ∑' x, f x ^ 2
  set L := ∑' x, |f x|
  set G := ∑' x, (f (x + 1) - f x) ^ 2;
  -- From `agmon_le`, `|f(x)| ≤ M := √(2√U√G)` for all `x`, hence `U = ∑ f² = ∑ |f|·|f| ≤ M ∑ |f| = M·L`; squaring gives `U² ≤ 2√U√G·L²`, i.e. `U⁴ ≤ 4 U G L⁴`, and therefore `U³ ≤ 4 L⁴ G`.
  have h_ineq : U ≤ Real.sqrt (2 * Real.sqrt U * Real.sqrt G) * L := by
    have h_ineq : ∀ x, (f x) ^ 2 ≤ Real.sqrt (2 * Real.sqrt U * Real.sqrt G) * |f x| := by
      intro x
      have h_abs : |f x| ≤ Real.sqrt (2 * Real.sqrt U * Real.sqrt G) := by
        convert Real.abs_le_sqrt ( agmon_le f hf2 hg2 x ) using 1;
      cases abs_cases ( f x ) <;> nlinarith [ Real.sqrt_nonneg ( 2 * Real.sqrt U * Real.sqrt G ) ];
    convert Summable.tsum_le_tsum h_ineq hf2 ( Summable.mul_left _ hf1 ) using 1 ; rw [ tsum_mul_left ];
  -- Squaring both sides of the inequality $U \leq \sqrt{2 \sqrt{U} \sqrt{G}} L$, we get $U^2 \leq 2 \sqrt{U} \sqrt{G} L^2$.
  have h_sq : U ^ 2 ≤ 2 * Real.sqrt U * Real.sqrt G * L ^ 2 := by
    convert pow_le_pow_left₀ ( show 0 ≤ U by exact tsum_nonneg fun _ => sq_nonneg _ ) h_ineq 2 using 1 ; rw [ mul_pow, Real.sq_sqrt <| by positivity ];
  -- Squaring both sides of the inequality $U^2 \leq 2 \sqrt{U} \sqrt{G} L^2$, we get $U^4 \leq 4 U G L^4$.
  have h_sq_sq : U ^ 4 ≤ 4 * U * G * L ^ 4 := by
    convert pow_le_pow_left₀ ( by positivity ) h_sq 2 using 1 <;> ring;
    rw [ Real.sq_sqrt ( tsum_nonneg fun _ => sq_nonneg _ ), Real.sq_sqrt ( tsum_nonneg fun _ => sq_nonneg _ ) ] ; ring;
  by_cases hU : U = 0;
  · simp [hU];
    exact mul_nonneg ( mul_nonneg zero_le_four ( by positivity ) ) ( tsum_nonneg fun _ => sq_nonneg _ );
  · nlinarith [ show 0 < U from lt_of_le_of_ne ( tsum_nonneg fun _ => sq_nonneg _ ) ( Ne.symm hU ) ]

/-! ## Tier 2 analytic core: Nash's ODE comparison `u' ≤ −κ u³ ⟹ u ≤ 1/√(2κt)` -/

/-
**Nash ODE comparison.** Let `u : ℝ → ℝ` be nonnegative, differentiable on `(0, ∞)`
with derivative `u'` there, satisfying `u'(t) ≤ −κ u(t)³` for all `t > 0` (with `κ > 0`).
Then `u(t) ≤ 1/√(2κ t)` for every `t > 0`.

*Proof.* Where `u > 0`, `g := u^{-2}` satisfies `g' = −2 u^{-3} u' ≥ 2κ`, so `g` grows at
rate `≥ 2κ`; integrating from `0⁺` (where `g ≥ 0`) gives `g(t) ≥ 2κ t`, i.e.
`u(t)² ≤ 1/(2κ t)`.  Where `u` hits `0` it stays `0` (as `u' ≤ 0`), so the bound is
trivial.
-/
lemma nash_ode_bound (u u' : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hu_nonneg : ∀ t : ℝ, 0 < t → 0 ≤ u t)
    (hu_deriv : ∀ t : ℝ, 0 < t → HasDerivAt u (u' t) t)
    (hu_ode : ∀ t : ℝ, 0 < t → u' t ≤ -κ * (u t) ^ 3) :
    ∀ t : ℝ, 0 < t → u t ≤ 1 / Real.sqrt (2 * κ * t) := by
  intro t ht
  by_cases hu_t_zero : u t = 0;
  · exact hu_t_zero.symm ▸ by positivity;
  · -- Consider $g(s) := (u(s))^{-2}$ on the interval $(0, t]$.
    set g : ℝ → ℝ := fun s => (u s)⁻¹ ^ 2
    have hg_deriv : ∀ s, 0 < s → s ≤ t → HasDerivAt g (-2 * (u s)⁻¹ ^ 3 * u' s) s := by
      intro s hs hst; convert HasDerivAt.comp s ( hasDerivAt_pow 2 _ ) ( HasDerivAt.inv ( hu_deriv s hs ) _ ) using 1 ; ring;
      · ring!;
      · contrapose! hu_t_zero;
        have h_u_zero : ∀ x, s < x → x ≤ t → u x = 0 := by
          intros x hx₁ hx₂; exact (by
          have := exists_deriv_eq_slope u hx₁;
          exact this ( continuousOn_of_forall_continuousAt fun y hy => HasDerivAt.continuousAt ( hu_deriv y ( by linarith [ hy.1 ] ) ) ) ( fun y hy => DifferentiableAt.differentiableWithinAt ( hu_deriv y ( by linarith [ hy.1 ] ) |> HasDerivAt.differentiableAt ) ) |> fun ⟨ c, hc₁, hc₂ ⟩ => by have := hu_ode c ( by linarith [ hc₁.1 ] ) ; rw [ eq_div_iff ] at hc₂ <;> nlinarith [ hu_nonneg c ( by linarith [ hc₁.1 ] ), hu_nonneg x ( by linarith [ hc₁.1 ] ), pow_nonneg ( hu_nonneg c ( by linarith [ hc₁.1 ] ) ) 3, pow_nonneg ( hu_nonneg x ( by linarith [ hc₁.1 ] ) ) 3, mul_pos hκ ( sub_pos.mpr hx₁ ), mul_pos hκ ( sub_pos.mpr hc₁.1 ), mul_pos hκ ( sub_pos.mpr hc₁.2 ), hu_deriv c ( by linarith [ hc₁.1 ] ) |> HasDerivAt.deriv ] ;);
        grind;
    -- Since $g'(s) \geq 2\kappa$ for all $s \in (0, t]$, we can apply the mean value theorem to $g$ on this interval.
    have h_mvt : ∀ s, 0 < s → s < t → g t - g s ≥ 2 * κ * (t - s) := by
      intros s hs hs_lt_t
      have h_mvt_step : ∀ x ∈ Set.Ioo s t, deriv g x ≥ 2 * κ := by
        intros x hx
        have h_u_pos : 0 < u x := by
          by_contra h_u_neg;
          have h_u_zero : ∀ y ∈ Set.Icc x t, u y = 0 := by
            intros y hy
            have h_u_le : ∀ z ∈ Set.Icc x y, u z ≤ u x := by
              intros z hz
              have h_u_le : ∀ w ∈ Set.Icc x z, u' w ≤ 0 := by
                exact fun w hw => le_trans ( hu_ode w ( by linarith [ hw.1, hx.1 ] ) ) ( mul_nonpos_of_nonpos_of_nonneg ( neg_nonpos.mpr hκ.le ) ( pow_nonneg ( hu_nonneg w ( by linarith [ hw.1, hx.1 ] ) ) 3 ) );
              by_cases hz_eq_x : z = x;
              · rw [hz_eq_x];
              · have := exists_deriv_eq_slope u ( lt_of_le_of_ne hz.1 ( Ne.symm hz_eq_x ) );
                simp +zetaDelta at *;
                exact this ( continuousOn_of_forall_continuousAt fun w hw => HasDerivAt.continuousAt ( hu_deriv w ( by linarith [ hw.1 ] ) ) ) ( fun w hw => DifferentiableAt.differentiableWithinAt ( hu_deriv w ( by linarith [ hw.1 ] ) |> HasDerivAt.differentiableAt ) ) |> fun ⟨ c, hc₁, hc₂ ⟩ => by have := h_u_le c ( by linarith ) ( by linarith ) ; rw [ eq_div_iff ] at hc₂ <;> nlinarith [ hu_deriv c ( by linarith ) |> HasDerivAt.deriv ] ;
            exact le_antisymm ( le_trans ( h_u_le y ⟨ by linarith [ hx.1, hy.1 ], by linarith [ hx.2, hy.2 ] ⟩ ) ( le_of_not_gt h_u_neg ) ) ( hu_nonneg y ( by linarith [ hx.1, hy.1 ] ) );
          exact hu_t_zero <| h_u_zero t ⟨ by linarith [ hx.1, hx.2 ], by linarith [ hx.1, hx.2 ] ⟩;
        have := hg_deriv x ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) ; have := this.deriv; simp_all +decide;
        nlinarith [ hu_ode x ( by linarith ), inv_pos.mpr ( pow_pos h_u_pos 3 ), mul_inv_cancel₀ ( ne_of_gt ( pow_pos h_u_pos 3 ) ), pow_pos h_u_pos 3 ];
      have := exists_deriv_eq_slope g hs_lt_t;
      contrapose! this;
      exact ⟨ continuousOn_of_forall_continuousAt fun x hx => HasDerivAt.continuousAt ( hg_deriv x ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) ), fun x hx => DifferentiableAt.differentiableWithinAt ( hg_deriv x ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) |> HasDerivAt.differentiableAt ), fun x hx => by rw [ ne_eq, eq_div_iff ] <;> nlinarith [ h_mvt_step x hx ] ⟩;
    -- Taking the limit as $s \to 0^+$ in $g(t) - g(s) \geq 2\kappa(t - s)$, we get $g(t) \geq 2\kappa t$.
    have h_lim : g t ≥ 2 * κ * t := by
      -- Since $g(s) \geq 0$ for all $s \in (0, t]$, we have $g(t) \geq 2\kappa(t - s)$ for all $s \in (0, t]$.
      have h_g_nonneg : ∀ s, 0 < s → s < t → g t ≥ 2 * κ * (t - s) := by
        exact fun s hs hs' => le_trans ( h_mvt s hs hs' ) ( sub_le_self _ ( sq_nonneg _ ) );
      -- Taking the limit as $s \to 0^+$ in $g(t) \geq 2\kappa(t - s)$, we get $g(t) \geq 2\kappa t$.
      have h_lim : Filter.Tendsto (fun s => 2 * κ * (t - s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * κ * t)) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
      exact le_of_tendsto h_lim ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT ht ) fun s hs => h_g_nonneg s hs.1 hs.2 );
    rw [ le_div_iff₀ ] <;> norm_num at *;
    · nlinarith [ show 0 < u t from lt_of_le_of_ne ( hu_nonneg t ht ) ( Ne.symm hu_t_zero ), Real.mul_self_sqrt ( show 0 ≤ 2 * κ * t by positivity ), inv_mul_cancel₀ hu_t_zero, inv_pow ( u t ) 2 ];
    · positivity

/-! ## Tier 3 assembly: from the Nash differential inequality to the pointwise bound -/

/-
**Nash/CKS pointwise assembly.**  Suppose `p : ℝ → ℤ → ℝ` is a kernel with
`p t r ≤ 1` (probabilities), and let `u : ℝ → ℝ` be the on-diagonal `ℓ²`-energy.  Assume
the two genuinely dynamical inputs of the Nash method:

* the **Nash differential inequality** `u' ≤ -κ u³` on `(0,∞)` with `u ≥ 0` there
  (this packages the energy identity `u' = -2 𝓔(p_t)`, the conductance lower bound
  `𝓔 ≥ (δ/2)‖∇·‖²`, and the discrete Nash inequality `nash_ineq`), and
* the **Chapman–Kolmogorov / off-diagonal bound** `p (2t) r ≤ Cod · u t`
  (semigroup property + Cauchy–Schwarz + reversibility).

Then `p` obeys the on-diagonal heat-kernel bound `p t r ≤ C/√(1+t)` uniformly, with an
explicit `C = max (√2) (Cod·√(2/κ))`.

This is the pure Tier-3 assembly of `lem_free`; it is proved outright and is reusable for
any reversible kernel supplying the two dynamical inputs.
-/
theorem nash_pointwise_bound
    (p : ℝ → ℤ → ℝ) (u u' : ℝ → ℝ) (κ Cod : ℝ)
    (hκ : 0 < κ) (hCod : 0 < Cod)
    (hp1 : ∀ t : ℝ, 0 ≤ t → ∀ r : ℤ, p t r ≤ 1)
    (hu_nonneg : ∀ t : ℝ, 0 < t → 0 ≤ u t)
    (hu_deriv : ∀ t : ℝ, 0 < t → HasDerivAt u (u' t) t)
    (hu_ode : ∀ t : ℝ, 0 < t → u' t ≤ -κ * (u t) ^ 3)
    (hCK : ∀ t : ℝ, 0 < t → ∀ r : ℤ, p (2 * t) r ≤ Cod * u t) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ r : ℤ, p t r ≤ C / Real.sqrt (1 + t) := by
  use max (Real.sqrt 2) (Cod * Real.sqrt (2 / κ));
  refine' ⟨ by positivity, fun t ht r => _ ⟩;
  by_cases ht_pos : 0 < t;
  · have h_bound : p t r ≤ Cod / Real.sqrt (κ * t) := by
      have h_bound : p t r ≤ Cod * u (t / 2) := by
        simpa [ two_mul ] using hCK ( t / 2 ) ( half_pos ht_pos ) r;
      have h_bound : u (t / 2) ≤ 1 / Real.sqrt (2 * κ * (t / 2)) := by
        apply nash_ode_bound u u' κ hκ hu_nonneg hu_deriv hu_ode (t / 2) (by linarith);
      convert le_trans ‹p t r ≤ Cod * u ( t / 2 ) › ( mul_le_mul_of_nonneg_left h_bound hCod.le ) using 1 ; ring;
    by_cases ht_ge_1 : t ≥ 1;
    · refine le_trans h_bound ?_;
      field_simp;
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( le_max_right _ _ ) ( Real.sqrt_nonneg _ ) );
      rw [ mul_left_comm, ← Real.sqrt_mul ( by positivity ) ];
      exact mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| by nlinarith [ mul_div_cancel₀ ( 2 : ℝ ) hκ.ne' ] ) hCod.le;
    · refine le_trans ( hp1 t ht r ) ?_;
      rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( by linarith ) ) ];
      exact le_max_of_le_left ( by rw [ one_mul ] ; exact Real.sqrt_le_sqrt <| by linarith );
  · norm_num [ show t = 0 by linarith ] at *;
    exact Or.inl ( le_trans ( hp1 0 le_rfl r ) ( Real.le_sqrt_of_sq_le ( by norm_num ) ) )

end TypeDDecouplingNash