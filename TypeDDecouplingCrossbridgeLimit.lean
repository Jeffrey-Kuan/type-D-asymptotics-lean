import Mathlib

/-!
# The dual-side convergence of `lem:crossbridge`: a finite-box → full semigroup limit

This file isolates and **proves outright** the dual-side ingredient (ii) of the continuum
crossbridge (`TypeDDecouplingCrossover.lean`, `lem_crossbridge`), per
`crossbridge_continuum_brief.tex`.

The dual side of `lem:crossbridge` is a hitting probability of the two-particle dual — a
countable-state walk with a bounded, finite-range generator, i.e. genuine *semigroup*
territory.  Write `A` for the full generator and `A_L` for the finite-box generator, both
bounded continuous-linear operators on a Banach space `E` (in the concrete model
`E = ℓ¹`), and `δ` for the initial mass at the origin.  We must show the finite-box
hitting probabilities converge to the full one, `ℙ_L → ℙ_∞`.

## The elementary finite-speed / series-tail argument (no probability)

The paper's brief describes the mechanism via Duhamel plus the elementary finite-speed
bound.  The clean, probability-free realisation used here is the following.  Because the
generator has finite range `ϱ`, the two semigroups **agree to high order on `δ`**: with
`n₀(L) → ∞` the truncation order,
`(A_L)^n δ = A^n δ` for all `n ≤ n₀(L)`
(the finite-speed bound `(A^n δ)(x) = 0` for `|x| > n ϱ` is exactly what makes the boxed
and full generators indistinguishable on `δ` up to order `n₀(L)`).  Consequently the
difference of the exponentials, expanded as power series, is a *factorial series tail*:
`e^{tA_L}δ − e^{tA}δ = ∑_{n} (t^n/n!)((A_L)^n − A^n)δ = ∑_{n > n₀(L)} (t^n/n!)((A_L)^n − A^n)δ`,
whose norm is bounded by `2‖δ‖ ∑_{n > n₀(L)} (|t|·M)^n / n!` (with `M` a common operator
bound), a tail of the convergent series for `e^{|t|M}`.  As `L → ∞`, `n₀(L) → ∞` and the
tail → 0.  Pairing with any bounded functional (the hitting-set indicator) gives the
hitting-probability convergence.

The main results are:
* `semigroup_apply_tendsto` — `e^{tA_L}δ → e^{tA}δ` in norm (the vector statement);
* `hitProb_finiteBox_tendsto` — for any bounded functional `ℓ` (the hitting-set indicator
  paired against the evolved mass), `ℓ(e^{tA_L}δ) → ℓ(e^{tA}δ)`.

Both are proved with standard axioms and **no `sorry`**, purely from the two structural
hypotheses (a uniform operator bound and the finite-order agreement on `δ`), which is the
faithful abstraction of the finite-range dual generator.  No infinite-volume IPS theory is
built.
-/

open scoped BigOperators Topology
open NormedSpace Filter

namespace TypeDDecoupling.CrossbridgeLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The exponential of a continuous-linear operator, applied to a vector, is the
termwise-applied power series. -/
theorem exp_apply_eq_tsum (c : E →L[ℝ] E) (v : E) :
    (exp c) v = ∑' n : ℕ, (n.factorial : ℝ)⁻¹ • ((c ^ n) v) := by
  have h : exp c = ∑' n : ℕ, (n.factorial : ℝ)⁻¹ • c ^ n :=
    congrFun (exp_eq_tsum (𝕂 := ℝ) (𝔸 := E →L[ℝ] E)) c
  have hsum := expSeries_summable' (𝕂 := ℝ) c
  calc (exp c) v = (ContinuousLinearMap.apply ℝ E v) (exp c) := rfl
    _ = (ContinuousLinearMap.apply ℝ E v) (∑' n, (n.factorial : ℝ)⁻¹ • c ^ n) := by rw [h]
    _ = ∑' n, (ContinuousLinearMap.apply ℝ E v) ((n.factorial : ℝ)⁻¹ • c ^ n) :=
        (ContinuousLinearMap.apply ℝ E v).map_tsum hsum
    _ = ∑' n, (n.factorial : ℝ)⁻¹ • ((c ^ n) v) := by simp

omit [CompleteSpace E] in
/-- Norm bound for the `n`-th power of `t • c` applied to `v`:
`‖((t•c)^n) v‖ ≤ (|t|·‖c‖)^n · ‖v‖`. -/
theorem norm_smul_pow_apply_le (t : ℝ) (c : E →L[ℝ] E) (v : E) (n : ℕ) :
    ‖((t • c) ^ n) v‖ ≤ (|t| * ‖c‖) ^ n * ‖v‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · calc ‖((t • c) ^ n) v‖ ≤ ‖(t • c) ^ n‖ * ‖v‖ := ((t • c) ^ n).le_opNorm v
      _ ≤ ‖t • c‖ ^ n * ‖v‖ := by gcongr; exact norm_pow_le' _ hn
      _ = (|t| * ‖c‖) ^ n * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]

/-
**The dual-side convergence (ii), vector form.**  Let `a` be a bounded operator (the
full generator), `aL L` the finite-box generators, all bounded by a common `M`, and suppose
that on the fixed vector `v` (the initial mass `δ`) the powers agree up to order `n₀ L`,
with `n₀ L → ∞` (the finite-speed / finite-range input).  Then `e^{t·aL L} v → e^{t·a} v`
in norm as `L → ∞`.

This is exactly the finite-speed + factorial-series-tail argument; no probability and no
Duhamel operator integral is needed.
-/
theorem semigroup_apply_tendsto
    (t : ℝ) (a : E →L[ℝ] E) (v : E) (aL : ℕ → E →L[ℝ] E) (M : ℝ)
    (hAM : ‖a‖ ≤ M) (hALM : ∀ L, ‖aL L‖ ≤ M)
    (n₀ : ℕ → ℕ) (hn₀ : Tendsto n₀ atTop atTop)
    (hagree : ∀ L n, n ≤ n₀ L → ((aL L) ^ n) v = (a ^ n) v) :
    Tendsto (fun L => (exp (t • aL L)) v) atTop (𝓝 ((exp (t • a)) v)) := by
  -- Define the dominating series $g$.
  set g : ℕ → ℝ := fun n => (n.factorial : ℝ)⁻¹ * (2 * ‖v‖ * (|t| * M)^n);
  -- By the properties of the exponential function and the definition of $g$, we have:
  have h_exp : ∀ L, ‖(exp (t • aL L)) v - (exp (t • a)) v‖ ≤ ∑' n, ‖(n.factorial : ℝ)⁻¹ • (((t • aL L) ^ n) v - ((t • a) ^ n) v)‖ := by
    intro L
    have h_sum : (exp (t • aL L)) v - (exp (t • a)) v = ∑' n : ℕ, (n.factorial : ℝ)⁻¹ • (((t • aL L) ^ n) v - ((t • a) ^ n) v) := by
      rw [ exp_apply_eq_tsum, exp_apply_eq_tsum, ← Summable.tsum_sub ];
      · simp +decide only [smul_sub];
      · refine' Summable.of_norm ?_;
        simp +decide [ norm_smul ];
        refine' Summable.of_nonneg_of_le ( fun n => mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ( norm_nonneg _ ) ) ( fun n => mul_le_mul_of_nonneg_left ( norm_smul_pow_apply_le t ( aL L ) v n ) ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ) _;
        convert Real.summable_pow_div_factorial ( |t| * ‖aL L‖ ) |> Summable.mul_right ‖v‖ using 2 ; ring;
      · have h_summable : Summable (fun n : ℕ => (n.factorial : ℝ)⁻¹ * (|t| * ‖a‖)^n * ‖v‖) := by
          exact Summable.mul_right _ ( by simpa [ inv_mul_eq_div ] using Real.summable_pow_div_factorial ( |t| * ‖a‖ ) );
        refine' .of_norm <| h_summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => _ );
        simp +decide [ norm_smul, mul_assoc ];
        exact mul_le_mul_of_nonneg_left ( norm_smul_pow_apply_le t a v n ) ( by positivity );
    convert norm_tsum_le_tsum_norm _;
    -- By the properties of the exponential function and the definition of $g$, we have that the series $\sum_{n=0}^{\infty} \frac{1}{n!} \|((t • aL L)^n) v - ((t • a)^n) v\|$ is dominated by the convergent series $\sum_{n=0}^{\infty} \frac{1}{n!} (|t| M)^n \|v\|$.
    have h_dominate : ∀ n, ‖(n.factorial : ℝ)⁻¹ • (((t • aL L) ^ n) v - ((t • a) ^ n) v)‖ ≤ g n := by
      intro n
      have h_bound : ‖((t • aL L) ^ n) v‖ ≤ (|t| * M) ^ n * ‖v‖ ∧ ‖((t • a) ^ n) v‖ ≤ (|t| * M) ^ n * ‖v‖ := by
        exact ⟨ norm_smul_pow_apply_le t ( aL L ) v n |> le_trans <| mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) ( mul_le_mul_of_nonneg_left ( hALM L ) ( by positivity ) ) _ ) ( by positivity ), norm_smul_pow_apply_le t a v n |> le_trans <| mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) ( mul_le_mul_of_nonneg_left ( hAM ) ( by positivity ) ) _ ) ( by positivity ) ⟩;
      rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ];
      exact le_trans ( mul_le_mul_of_nonneg_left ( norm_sub_le _ _ ) ( by positivity ) ) ( by rw [ show g n = ( n.factorial : ℝ ) ⁻¹ * ( 2 * ‖v‖ * ( |t| * M ) ^ n ) by rfl ] ; nlinarith [ inv_nonneg.2 ( by positivity : 0 ≤ ( n.factorial : ℝ ) ) ] );
    refine' Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => h_dominate n ) _;
    convert Summable.mul_left ( 2 * ‖v‖ ) ( Real.summable_pow_div_factorial ( |t| * M ) ) using 2 ; ring;
  -- By the properties of the exponential function and the definition of $g$, we have that $\sum' n, ‖(n.factorial : ℝ)⁻¹ • (((t • aL L) ^ n) v - ((t • a) ^ n) v)‖ \leq \sum' n, g (n + n₀ L)$.
  have h_sum_bound : ∀ L, ∑' n, ‖(n.factorial : ℝ)⁻¹ • (((t • aL L) ^ n) v - ((t • a) ^ n) v)‖ ≤ ∑' n, g (n + n₀ L) := by
    intro L
    have h_sum_bound : ∀ n, n ≥ n₀ L → ‖(n.factorial : ℝ)⁻¹ • (((t • aL L) ^ n) v - ((t • a) ^ n) v)‖ ≤ g n := by
      intro n hn
      have h_norm : ‖((t • aL L) ^ n) v - ((t • a) ^ n) v‖ ≤ 2 * ‖v‖ * (|t| * M) ^ n := by
        have h_norm : ‖((t • aL L) ^ n) v‖ ≤ (|t| * M) ^ n * ‖v‖ ∧ ‖((t • a) ^ n) v‖ ≤ (|t| * M) ^ n * ‖v‖ := by
          exact ⟨ norm_smul_pow_apply_le t ( aL L ) v n |> le_trans <| mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) ( mul_le_mul_of_nonneg_left ( hALM L ) ( by positivity ) ) _ ) ( by positivity ), norm_smul_pow_apply_le t a v n |> le_trans <| mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) ( mul_le_mul_of_nonneg_left hAM ( by positivity ) ) _ ) ( by positivity ) ⟩;
        exact le_trans ( norm_sub_le _ _ ) ( by linarith );
      rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ] ; exact mul_le_mul_of_nonneg_left h_norm ( by positivity );
    rw [ ← Summable.sum_add_tsum_nat_add ( n₀ L ) ];
    · rw [ Finset.sum_eq_zero ] <;> simp_all +decide [ sub_eq_iff_eq_add ];
      · refine' Summable.tsum_le_tsum ( fun n => h_sum_bound _ ( by linarith ) ) _ _;
        · refine' Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => h_sum_bound _ ( by linarith ) ) _;
          have h_summable : Summable g := by
            convert Summable.mul_left ( 2 * ‖v‖ ) ( Real.summable_pow_div_factorial ( |t| * M ) ) using 2 ; ring;
          exact h_summable.comp_injective ( add_left_injective _ );
        · have h_summable : Summable g := by
            convert Summable.mul_left ( 2 * ‖v‖ ) ( Real.summable_pow_div_factorial ( |t| * M ) ) using 2 ; ring;
          exact h_summable.comp_injective ( add_left_injective _ );
      · intro n hn; specialize hagree L n hn.le; simp_all +decide [ smul_pow ] ;
    · refine' Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => _ ) ( show Summable g from _ );
      · by_cases hn : n < n₀ L;
        · simp +decide [ hagree L n hn.le, smul_pow ];
          exact mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ( mul_nonneg ( mul_nonneg zero_le_two ( norm_nonneg _ ) ) ( pow_nonneg ( mul_nonneg ( abs_nonneg _ ) ( le_trans ( norm_nonneg _ ) hAM ) ) _ ) );
        · exact h_sum_bound n ( le_of_not_gt hn );
      · have := Real.summable_pow_div_factorial ( |t| * M );
        convert this.mul_left ( 2 * ‖v‖ ) using 2 ; ring;
  -- By the properties of the exponential function and the definition of $g$, we have that $\sum' n, g (n + n₀ L) \to 0$ as $L \to \infty$.
  have h_sum_zero : Filter.Tendsto (fun L => ∑' n, g (n + n₀ L)) Filter.atTop (nhds 0) := by
    convert tendsto_sum_nat_add ( fun n => g n ) |> Filter.Tendsto.comp <| hn₀ using 1;
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ( squeeze_zero ( fun _ => norm_nonneg _ ) ( fun L => le_trans ( h_exp L ) ( h_sum_bound L ) ) h_sum_zero )

/-- **The dual-side convergence (ii), hitting-probability form.**  Under the hypotheses of
`semigroup_apply_tendsto`, for any bounded functional `ℓ` (the hitting-set indicator paired
against the evolved mass), the finite-box hitting probabilities converge to the full one:
`ℓ(e^{t·aL L} v) → ℓ(e^{t·a} v)`. -/
theorem hitProb_finiteBox_tendsto
    (t : ℝ) (a : E →L[ℝ] E) (v : E) (aL : ℕ → E →L[ℝ] E) (M : ℝ)
    (hAM : ‖a‖ ≤ M) (hALM : ∀ L, ‖aL L‖ ≤ M)
    (n₀ : ℕ → ℕ) (hn₀ : Tendsto n₀ atTop atTop)
    (hagree : ∀ L n, n ≤ n₀ L → ((aL L) ^ n) v = (a ^ n) v)
    (ℓ : E →L[ℝ] ℝ) :
    Tendsto (fun L => ℓ ((exp (t • aL L)) v)) atTop (𝓝 (ℓ ((exp (t • a)) v))) :=
  (ℓ.continuous.tendsto _).comp
    (semigroup_apply_tendsto t a v aL M hAM hALM n₀ hn₀ hagree)

end TypeDDecoupling.CrossbridgeLimit