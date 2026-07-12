import Mathlib
import TypeDDecouplingNash
import TypeDDecouplingCKS2
import TypeDDecouplingKR
import TypeDDecouplingBethe
import TypeDDecouplingKaramata

/-!
# Tier 3 / Tier 4 black-box statements: local CLTs, occupation times, dual kernels

This file formalises the **statements** of the §lclt (local central limit theorems for
the dual coordinates) and §kernel (two-particle dual kernel bound) results of
`typeD_decoupling-draft-rev2.tex`, together with the two classical inputs they cite
(Kolmogorov–Rogozin anti-concentration, Karamata's Tauberian theorem).

Per the user's instruction, these are **cited / assumed results taken as a black box**:
each is stated as faithfully as feasible and left as `sorry`.  None of them is proved
here; the `sorry`s are intentional and mark exactly the literature inputs that the paper
invokes.  We are *not* permitted to introduce `axiom`s, so the assumed status is recorded
honestly by an unfilled `sorry` rather than by an axiom.

The continuous-time walks are encoded schematically by their **time-marginal transition
kernels** `p : ℝ → ℤ → ℝ` (with `p t r = ℙ₀(X(t) = r)`), tied to a jump-rate matrix
`rate : ℤ → ℤ → ℝ` through the Kolmogorov forward equations (`IsTransitionKernel`).
-/

open scoped BigOperators Real Topology
open MeasureTheory Filter Asymptotics ProbabilityTheory

namespace TypeDDecoupling

/-! ## Schematic encoding of a continuous-time walk on `ℤ` -/

/-- `p` is the transition kernel of the continuous-time Markov walk on `ℤ` with jump
rates `rate x y` (the rate of jumping from `x` to `y`).  This bundles the defining
properties: the initial condition `p 0 = δ₀`, nonnegativity, and the Kolmogorov forward
(master) equation `∂ₜ p_t(r) = Σ_y rate(y,r) p_t(y) − (Σ_y rate(r,y)) p_t(r)`.

**Fidelity fix (de-vacuification).**  Nonnegativity is required only for `t ≥ 0` (the
regime where a transition kernel is defined).  Requiring `0 ≤ p t r` for *all* real `t`
(as in the original encoding) is contradictory for any walk with a positive incoming rate
into some `r ≠ 0` (e.g. any nearest-neighbour or split rate): then `s ↦ p s r` would have a
global minimum `p 0 r = 0` at the interior point `0`, forcing its derivative there to
vanish, whereas the master equation makes that derivative `rate 0 r · p 0 0 = rate 0 r > 0`.
That contradiction made every kernel-based lemma (`lem_Rlclt`, `lem_free`, `lem_tau`)
vacuously true; restricting nonnegativity to `t ≥ 0` removes it (the real heat kernel,
extended arbitrarily to `t < 0`, is then a genuine model). -/
def IsTransitionKernel (rate : ℤ → ℤ → ℝ) (p : ℝ → ℤ → ℝ) : Prop :=
  (∀ r : ℤ, p 0 r = if r = 0 then 1 else 0) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ r : ℤ, 0 ≤ p t r) ∧
  (∀ t : ℝ, ∀ r : ℤ,
     HasDerivAt (fun s => p s r)
       ((∑' y : ℤ, rate y r * p t y) - (∑' y : ℤ, rate r y) * p t r) t)

/-- Occupation time of state `r` up to time `s`: `τ_r(s) = ∫₀ˢ ℙ₀(X(t)=r) dt`. -/
noncomputable def occupation (p : ℝ → ℤ → ℝ) (r : ℤ) (s : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..s, p t r

/-- The structural hypotheses on a driftless, finite-range, reversible walk used
throughout §lclt (Lemma `lem:free`).  `rate` is the jump-rate matrix, `p` its transition
kernel, `m` a reversing measure with `c₁ ≤ m ≤ c₂`, jump range `≤ ϱ`, total exit rate
`≤ Λ`, and nearest-neighbour conductance bounded below by `δ > 0`. -/
structure DriftlessReversibleWalk where
  rate : ℤ → ℤ → ℝ
  p : ℝ → ℤ → ℝ
  m : ℤ → ℝ
  c₁ : ℝ
  c₂ : ℝ
  δ : ℝ
  Λ : ℝ
  ϱ : ℕ
  isKernel : IsTransitionKernel rate p
  rate_nonneg : ∀ x y : ℤ, 0 ≤ rate x y
  c₁_pos : 0 < c₁
  δ_pos : 0 < δ
  m_lb : ∀ x : ℤ, c₁ ≤ m x
  m_ub : ∀ x : ℤ, m x ≤ c₂
  reversible : ∀ x y : ℤ, m x * rate x y = m y * rate y x
  finite_range : ∀ x y : ℤ, rate x y ≠ 0 → (y - x).natAbs ≤ ϱ
  exit_le : ∀ x : ℤ, (∑' y : ℤ, rate x y) ≤ Λ
  conductance_lb : ∀ x : ℤ, δ ≤ m x * rate x (x + 1)
  driftless : ∀ x : ℤ, (∑' y : ℤ, ((y : ℝ) - (x : ℝ)) * rate x y) = 0

/-! ## `lem:free` — free and perturbed kernel bounds (on-diagonal local CLT) -/

/-- **Lemma `lem:free`** (free and perturbed kernel bounds; cf. \cite{LawlerLimic, CKS}).
For a driftless, finite-range walk reversible with respect to a measure bounded above and
below, with conductances bounded below, the time-`t` transition probabilities obey the
on-diagonal local-CLT / heat-kernel bound
`sup_r ℙ(X(t)=r) ≤ C / √(1+t)`, with `C` depending only on `(c₁,c₂,δ,Λ,ϱ)`.

**Proof (Nash / CKS method).**  The whole *analytic* content is discharged by the
library-clean file `TypeDDecouplingNash.lean`:

* the discrete 1-D Nash inequality `TypeDDecouplingNash.nash_ineq`
  (`‖f‖₂⁶ ≤ 4‖f‖₁⁴‖∇f‖₂²`) via the elementary Agmon bound `agmon_le`;
* the Nash ODE comparison `TypeDDecouplingNash.nash_ode_bound`
  (`u' ≤ -κu³ ⟹ u ≤ 1/√(2κt)`); and
* the Tier-3 assembly `TypeDDecouplingNash.nash_pointwise_bound`, which turns the
  on-diagonal `ℓ²`-energy decay together with the Chapman–Kolmogorov off-diagonal bound
  into the stated `C/√(1+t)` estimate.

Applying `nash_pointwise_bound` reduces `lem_free` to the two genuinely *dynamical*
inputs of the method, bundled in the `have` below:

1. the **Nash differential inequality** `u' ≤ -κ u³` for the on-diagonal energy
   `u t = ∑' x, (W.p t x)² / W.m x` — this is where the Dirichlet-form energy identity
   `u'(t) = -2𝓔(p_t)` (Kolmogorov equation + reversibility), the conductance lower bound,
   and `nash_ineq` combine;
2. the **Chapman–Kolmogorov / off-diagonal bound** `W.p (2t) r ≤ Cod · u t`
   (semigroup property + Cauchy–Schwarz + reversibility), together with `W.p ≤ 1`.

These two facts are properties of the *transition semigroup* (they involve the two-point
kernel `p_t(y→·)` and mass conservation), which the abstract `IsTransitionKernel`
interface — carrying only the single kernel started at the origin and its per-site forward
ODE — does not expose.  Deriving them requires constructing the operator semigroup
`exp(tA)` of the (finite-range, bounded) generator and identifying `W.p` with `exp(tA)δ₀`;
absent that infrastructure they enter here as the sole residual input.  All the Nash
analysis (Tiers 1–3) is proved outright and reusable in `TypeDDecouplingNash.lean`. -/
theorem lem_free (W : DriftlessReversibleWalk)
    (hp_le1 : ∀ t : ℝ, 0 ≤ t → ∀ x : ℤ, W.p t x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ r : ℤ,
      W.p t r ≤ C / Real.sqrt (1 + t) :=
  -- The full Nash/CKS argument is carried out on the exponential semigroup
  -- `Q_t = exp (t·A)` of the bounded forward generator `A` in
  -- `TypeDDecouplingCKS`/`TypeDDecouplingCKS2`; `W.p` is identified with the
  -- semigroup kernel started at `0` by a weighted-ℓ¹ Grönwall uniqueness argument.
  TypeDDecouplingCKS.free_bound W.rate W.p W.m W.c₁ W.c₂ W.δ W.Λ W.ϱ
    W.isKernel.1 W.isKernel.2.1 W.isKernel.2.2
    W.rate_nonneg W.finite_range W.exit_le W.reversible
    W.c₁_pos W.m_lb W.m_ub W.δ_pos W.conductance_lb hp_le1

/-! ## `lem:Rlclt` — defected marginal local CLT for the relative coordinate -/

/--
**Convolution lemma (exponential leg).**  For `ν > 0` the renewal convolution of the
exponential `e^{-νu}` against the free heat-kernel decay `(1+(t-u))^{-1/2}` splits at
`t/2` into a decaying head and an exponentially small tail:
`∫₀ᵗ e^{-νu} (1+(t-u))^{-1/2} du ≤ √2/(ν√(1+t)) + 2 e^{-νt/2} √(1+t)`.
(On `[0,t/2]` use `1+t-u ≥ (1+t)/2` and `ν∫e^{-νu} ≤ 1`; on `[t/2,t]` use
`e^{-νu} ≤ e^{-νt/2}` and `∫(1+t-u)^{-1/2} ≤ 2√(1+t)`.)
-/
lemma Rlclt_conv_exp (ν : ℝ) (hν : 0 < ν) (t : ℝ) (ht : 0 ≤ t) :
    (∫ u in (0:ℝ)..t, Real.exp (-(ν * u)) * (1 / Real.sqrt (1 + (t - u))))
      ≤ Real.sqrt 2 / (ν * Real.sqrt (1 + t))
        + 2 * Real.exp (-(ν * t / 2)) * Real.sqrt (1 + t) := by
  by_cases h : t = 0 <;> simp_all +decide [ intervalIntegral.integral_of_le ];
  · positivity;
  · -- Split the integral into two parts: from 0 to t/2 and from t/2 to t.
    have h_split : ∫ u in Set.Ioc 0 t, Real.exp (-(ν * u)) * (1 / Real.sqrt (1 + (t - u))) ≤ (∫ u in Set.Ioc 0 (t / 2), Real.exp (-(ν * u)) * (Real.sqrt 2 / Real.sqrt (1 + t))) + (∫ u in Set.Ioc (t / 2) t, Real.exp (-(ν * t / 2)) * (1 / Real.sqrt (1 + (t - u)))) := by
      have h_split : ∫ u in Set.Ioc 0 t, Real.exp (-(ν * u)) * (1 / Real.sqrt (1 + (t - u))) ≤ (∫ u in Set.Ioc 0 (t / 2), Real.exp (-(ν * u)) * (1 / Real.sqrt (1 + (t - u)))) + (∫ u in Set.Ioc (t / 2) t, Real.exp (-(ν * u)) * (1 / Real.sqrt (1 + (t - u)))) := by
        rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num;
        · rw [ Set.Ioc_union_Ioc_eq_Ioc ] <;> linarith;
        · exact ContinuousOn.integrableOn_Icc ( by exact ContinuousOn.mul ( ContinuousOn.rexp <| ContinuousOn.neg <| continuousOn_const.mul continuousOn_id ) <| ContinuousOn.inv₀ ( ContinuousOn.sqrt <| continuousOn_const.add <| continuousOn_const.sub continuousOn_id ) fun x hx => ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ hx.1, hx.2 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
        · exact ContinuousOn.integrableOn_Icc ( by exact ContinuousOn.mul ( Continuous.continuousOn <| by continuity ) <| ContinuousOn.inv₀ ( Continuous.continuousOn <| by continuity ) fun x hx => ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ hx.1, hx.2 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
      refine le_trans h_split <| add_le_add ?_ ?_;
      · refine' MeasureTheory.setIntegral_mono_on _ _ _ _ <;> norm_num;
        · exact ContinuousOn.integrableOn_Icc ( by exact ContinuousOn.mul ( ContinuousOn.rexp ( ContinuousOn.neg ( continuousOn_const.mul continuousOn_id ) ) ) ( ContinuousOn.inv₀ ( ContinuousOn.sqrt ( continuousOn_const.add ( continuousOn_const.sub continuousOn_id ) ) ) fun x hx => ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ hx.1, hx.2 ] ) ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
        · exact Continuous.integrableOn_Ioc ( by continuity );
        · field_simp;
          exact fun x hx₁ hx₂ => Real.le_sqrt_of_sq_le <| by rw [ div_pow, Real.sq_sqrt <| by linarith, Real.sq_sqrt <| by linarith ] ; rw [ div_le_iff₀ ] <;> nlinarith;
      · refine' MeasureTheory.setIntegral_mono_on _ _ _ _ <;> norm_num;
        · exact ContinuousOn.integrableOn_Icc ( by exact ContinuousOn.mul ( ContinuousOn.rexp <| ContinuousOn.neg <| continuousOn_const.mul continuousOn_id ) <| ContinuousOn.inv₀ ( ContinuousOn.sqrt <| continuousOn_const.add <| continuousOn_const.sub continuousOn_id ) fun x hx => ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ hx.1, hx.2 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
        · exact ContinuousOn.integrableOn_Icc ( by exact ContinuousOn.mul continuousOn_const <| ContinuousOn.inv₀ ( Continuous.continuousOn <| Real.continuous_sqrt.comp <| by continuity ) fun x hx => ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ hx.1, hx.2 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
        · exact fun x hx₁ hx₂ => mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr <| by nlinarith ) <| inv_nonneg.mpr <| Real.sqrt_nonneg _;
    -- Evaluate the first integral: $\int_0^{t/2} e^{-\nu u} \frac{\sqrt{2}}{\sqrt{1+t}} \, du$.
    have h_first : ∫ u in Set.Ioc 0 (t / 2), Real.exp (-(ν * u)) * (Real.sqrt 2 / Real.sqrt (1 + t)) ≤ Real.sqrt 2 / (ν * Real.sqrt (1 + t)) := by
      rw [ ← intervalIntegral.integral_of_le ( by positivity ), intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_mul_left ( fun u => Real.exp ( -u ) ) ] <;> norm_num [ hν.ne' ];
      ring_nf; norm_num [ hν.ne' ];
      positivity;
    -- Evaluate the second integral: $\int_{t/2}^t e^{-\nu t/2} \frac{1}{\sqrt{1+(t-u)}} \, du$.
    have h_second : ∫ u in Set.Ioc (t / 2) t, Real.exp (-(ν * t / 2)) * (1 / Real.sqrt (1 + (t - u))) ≤ 2 * Real.exp (-(ν * t / 2)) * Real.sqrt (1 + t) := by
      rw [ ← intervalIntegral.integral_of_le ( by linarith ) ] ; norm_num [ intervalIntegral.integral_comp_sub_left fun u => ( Real.sqrt ( 1 + u ) ) ⁻¹ ] ; ring_nf ; norm_num;
      rw [ intervalIntegral.integral_comp_add_left fun x => ( Real.sqrt x ) ⁻¹ ] ; norm_num ; ring_nf ; norm_num;
      rw [ intervalIntegral.integral_congr fun x hx => by rw [ Real.sqrt_eq_rpow, ← Real.rpow_neg ] ; linarith [ Set.mem_Icc.mp ( by rwa [ Set.uIcc_of_le ( by linarith ) ] at hx ) ] ] ; norm_num [ Real.sqrt_eq_rpow, integral_rpow ] ; ring_nf ; norm_num;
      norm_num [ ← Real.sqrt_eq_rpow ];
      nlinarith [ Real.sqrt_nonneg ( 1 + t * ( 1 / 2 ) ), Real.sqrt_le_sqrt ( by linarith : 1 + t * ( 1 / 2 ) ≤ 1 + t ), Real.exp_pos ( - ( ν * t * ( 1 / 2 ) ) ) ];
    simpa using h_split.trans ( add_le_add h_first h_second )

/--
**Convolution lemma (occupation leg).**  The renewal convolution of the excursion
occupation growth `√u` against the free heat-kernel decay `(1+(t-u))^{-1/2}` is `O(t)`:
`∫₀ᵗ √u (1+(t-u))^{-1/2} du ≤ 2t`.  (Use `√u ≤ √t` and `∫₀ᵗ(1+t-u)^{-1/2} = 2(√(1+t)-1) ≤ 2√t`.)
-/
lemma Rlclt_conv_sqrt (t : ℝ) (ht : 0 ≤ t) :
    (∫ u in (0:ℝ)..t, Real.sqrt u * (1 / Real.sqrt (1 + (t - u)))) ≤ 2 * t := by
  by_cases ht_eq_zero : t = 0 <;> simp_all +decide [ intervalIntegral.integral_comp_sub_left, mul_assoc ];
  refine' le_trans ( intervalIntegral.integral_mono_on _ _ _ _ ) _;
  refine' fun u => Real.sqrt t * ( Real.sqrt ( 1 + ( t - u ) ) ) ⁻¹;
  · positivity;
  · exact ContinuousOn.intervalIntegrable ( by exact ContinuousOn.mul ( Real.continuous_sqrt.continuousOn ) ( ContinuousOn.inv₀ ( Real.continuous_sqrt.comp_continuousOn ( continuousOn_const.add ( continuousOn_const.sub continuousOn_id ) ) ) fun u hu => ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ Set.mem_Icc.mp <| by simpa [ ht ] using hu ] ) ) ..;
  · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.mul continuousAt_const <| ContinuousAt.inv₀ ( Real.continuous_sqrt.continuousAt.comp <| continuousAt_const.add <| continuousAt_const.sub continuousAt_id ) <| ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ Set.mem_Icc.mp <| by simpa [ ht ] using hu ] );
  · exact fun x hx => mul_le_mul_of_nonneg_right ( Real.sqrt_le_sqrt hx.2 ) ( inv_nonneg.2 ( Real.sqrt_nonneg _ ) );
  · rw [ intervalIntegral.integral_comp_sub_left fun u => Real.sqrt t * ( Real.sqrt ( 1 + u ) ) ⁻¹ ] ; norm_num ; ring;
    rw [ intervalIntegral.integral_comp_add_left fun x => ( Real.sqrt x ) ⁻¹ ] ; norm_num;
    rw [ intervalIntegral.integral_congr fun x hx => by rw [ Real.sqrt_eq_rpow, ← Real.rpow_neg ] ; linarith [ Set.mem_Icc.mp ( by simpa [ ht ] using hx ) ] ] ; norm_num [ Real.sqrt_eq_rpow, integral_rpow ] ; ring_nf;
    rw [ ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow ] ; nlinarith [ Real.sqrt_nonneg t, Real.sqrt_nonneg ( 1 + t ), Real.mul_self_sqrt ( show 0 ≤ t by linarith ), Real.mul_self_sqrt ( show 0 ≤ 1 + t by linarith ), sq_nonneg ( Real.sqrt t - Real.sqrt ( 1 + t ) ) ]

/--
**Renewal convolution bound (crux of `lem:Rlclt`, off-origin case).**  The excursion
renewal integral, with the zero-occupation estimate `e^{-νu} + C₁ε√u` inserted, decays like
`1/√(1+t)` uniformly in the window `νt ≤ K`, `εt ≤ M`.  Splitting the integrand into the
exponential leg and the occupation leg and applying `Rlclt_conv_exp`/`Rlclt_conv_sqrt`:
* exp leg: `νC₁·(√2/(ν√(1+t)) + 2e^{-νt/2}√(1+t))`; the tail is bounded using
  `ν(1+t)e^{-νt/2} ≤ ν+νt ≤ 2+K`, giving `(C₁√2 + 2C₁(2+K))/√(1+t)`;
* occupation leg: `νC₁²ε·2t`; the window arithmetic
  `ν ε t √(1+t) ≤ √2·(νt)·(ε√t) ≤ √2·K·√M` gives `2√2 C₁² K √M/√(1+t)`.
-/
lemma Rlclt_renewal_integral_bound
    (ν ε C₁ K M : ℝ) (hν : 0 < ν) (hν2 : ν ≤ 2) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K) (hM : 0 ≤ M) (t : ℝ) (ht : 1 ≤ t)
    (hwin : ν * t ≤ K) (hεt : ε * t ≤ M) :
    ν * (∫ u in (0:ℝ)..t,
          (Real.exp (-(ν * u)) + C₁ * ε * Real.sqrt u) * (C₁ / Real.sqrt (1 + (t - u))))
      ≤ (C₁ * Real.sqrt 2 + 2 * C₁ * (2 + K) + 2 * Real.sqrt 2 * C₁ ^ 2 * K * Real.sqrt M)
          / Real.sqrt (1 + t) := by
  -- Apply the convolution bound to the exponential and occupation terms separately.
  have h_exp : ν * ∫ u in (0:ℝ)..t, Real.exp (-(ν * u)) * (C₁ / Real.sqrt (1 + (t - u))) ≤ (C₁ * Real.sqrt 2 + 2 * C₁ * (2 + K)) / Real.sqrt (1 + t) := by
    have h_exp : ν * ∫ u in (0:ℝ)..t, Real.exp (-(ν * u)) * (1 / Real.sqrt (1 + (t - u))) ≤ (Real.sqrt 2 + 2 * (2 + K)) / Real.sqrt (1 + t) := by
      refine' le_trans ( mul_le_mul_of_nonneg_left ( Rlclt_conv_exp ν hν t ( by linarith ) ) hν.le ) _;
      field_simp;
      rw [ Real.sq_sqrt ( by positivity ) ];
      nlinarith [ Real.exp_le_one_iff.mpr ( show - ( ν * t / 2 ) ≤ 0 by nlinarith ), mul_le_mul_of_nonneg_left ht hν.le ];
    convert mul_le_mul_of_nonneg_left h_exp hC₁ using 1 <;> ring;
    simp +decide only [mul_assoc, mul_left_comm, ← intervalIntegral.integral_const_mul] ; congr ; ext ; ring;
  -- Apply the convolution bound to the occupation term separately.
  have h_occ : ν * ∫ u in (0:ℝ)..t, C₁ * ε * Real.sqrt u * (C₁ / Real.sqrt (1 + (t - u))) ≤ 2 * Real.sqrt 2 * C₁ ^ 2 * K * Real.sqrt M / Real.sqrt (1 + t) := by
    -- Apply the convolution bound to the occupation term separately.
    have h_occ_bound : ν * C₁ ^ 2 * ε * ∫ u in (0:ℝ)..t, Real.sqrt u * (1 / Real.sqrt (1 + (t - u))) ≤ 2 * Real.sqrt 2 * C₁ ^ 2 * K * Real.sqrt M / Real.sqrt (1 + t) := by
      refine' le_trans ( mul_le_mul_of_nonneg_left ( Rlclt_conv_sqrt t ( by positivity ) ) ( by positivity ) ) _;
      -- We'll use that $ν * ε * t * \sqrt{1 + t} ≤ \sqrt{2} * K * \sqrt{M}$ to conclude the proof.
      have h_ineq : ν * ε * t * Real.sqrt (1 + t) ≤ Real.sqrt 2 * K * Real.sqrt M := by
        -- We can divide both sides by $K$ (since $K > 0$) to simplify the inequality.
        suffices h_simplified : ν * ε * t * Real.sqrt (1 + t) ≤ Real.sqrt 2 * (ν * t) * Real.sqrt M by
          exact h_simplified.trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left hwin ( Real.sqrt_nonneg _ ) ) ( Real.sqrt_nonneg _ ) );
        -- We can divide both sides by $ν * t$ (since $ν * t > 0$) to simplify the inequality.
        suffices h_simplified : ε * Real.sqrt (1 + t) ≤ Real.sqrt 2 * Real.sqrt M by
          nlinarith [ mul_pos hν ( zero_lt_one.trans_le ht ) ];
        rw [ ← Real.sqrt_mul <| by positivity ];
        exact Real.le_sqrt_of_sq_le ( by nlinarith [ sq_nonneg ( ε - 1 ), Real.mul_self_sqrt ( show 0 ≤ 1 + t by linarith ), Real.mul_self_sqrt ( show 0 ≤ 2 * M by positivity ) ] );
      rw [ le_div_iff₀ ] <;> first | positivity | nlinarith;
    convert h_occ_bound using 1 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ← intervalIntegral.integral_const_mul ] ; ring
  -- Combine the two bounds.
  have h_combined : ν * ∫ u in (0:ℝ)..t, (Real.exp (-(ν * u)) + C₁ * ε * Real.sqrt u) * (C₁ / Real.sqrt (1 + (t - u))) ≤ (C₁ * Real.sqrt 2 + 2 * C₁ * (2 + K)) / Real.sqrt (1 + t) + (2 * Real.sqrt 2 * C₁ ^ 2 * K * Real.sqrt M) / Real.sqrt (1 + t) := by
    convert add_le_add h_exp h_occ using 1 ; rw [ ← mul_add, ← intervalIntegral.integral_add ] ; congr ; ext ; ring;
    · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.mul ( ContinuousAt.rexp <| ContinuousAt.neg <| continuousAt_const.mul continuousAt_id ) <| ContinuousAt.div continuousAt_const ( Real.continuous_sqrt.continuousAt.comp <| continuousAt_const.add <| continuousAt_const.sub continuousAt_id ) <| ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ Set.mem_Icc.mp <| by simpa [ ht.trans' ] using hu ] );
    · exact ContinuousOn.intervalIntegrable ( by exact ContinuousOn.mul ( ContinuousOn.mul ( continuousOn_const.mul continuousOn_const ) ( Real.continuous_sqrt.continuousOn ) ) ( ContinuousOn.div continuousOn_const ( Real.continuous_sqrt.comp_continuousOn ( continuousOn_const.add ( continuousOn_const.sub continuousOn_id ) ) ) fun u hu => ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ Set.mem_Icc.mp <| by simpa [ ht.trans' ] using hu ] ) ) ..
  -- Divide the inequality by the positive denominator.
  field_simp at h_combined ⊢
  exact h_combined.trans (by linarith)

/--
**Lemma `lem:Rlclt`** (defected marginal local CLT).  Let `R` be the
different-species relative walk: off `{-1,0,1}` a symmetric rate-`(1+q²)` walk, with a
sticky origin held for an `Exp(ν_sp)` time (`ν_sp = 2q²ε`, `ε = 1−q²`) and re-entered
from `±1` at the merge rate `ε`, started at `R(0)=0`.  Then, in the window `ν_sp t ≤ K`,
`ℙ(R(t)=r) ≤ C/√(1+t) + δ_{r,0} e^{−ν_sp t}`.

**Fidelity repairs applied** (documented per the `rlclt_brief`, paralleling the earlier
`lem_Slclt` quantifier repair):

* **(F1) `q`-uniformity.**  As originally encoded, `q` was fixed *before* `∃ C`, and the
  window `2q²(1-q²)t ≤ K` then bounds `t ≤ T_max(q,K)`, making the claim trivially true
  (`C = √(1+T_max)`).  The paper consumes this lemma as `q → 1` (window unbounded), so the
  faithful statement pulls the constant `∃ C` **before** `q`.  Since a single `C` uniform
  over *all* `q ∈ (0,1)` is unavailable (the trivial-window constant blows up as `q → 0`),
  we introduce a floor `q₀ ∈ (0,1)` and quantify `C = C(K, q₀, C₁)` before `q ∈ [q₀, 1)`;
  the window is genuinely unbounded on this range (as `q → 1`), so the bound is non-trivial.

* **(F2) Faithful rate hypotheses.**  `hbulk` pins the rates only for `|x| ≥ 2`, leaving
  the defect exits under-constrained.  We add the missing exits matching the paper's
  `R`-walk (§5): `hzero_far` (no exits from `0` other than the two splits to `±1`),
  `hone`/`hnegone` (from `±1`: nearest-neighbour outward at rate `1+q²`, the merge to `0`
  at rate `ε=1-q²` (=`hmerge`), and no other exit — in particular no `±1↔∓1` swap, since
  `±1` are not adjacent).  Every added hypothesis is satisfied by the actual `R`-walk rate
  matrix.  These rate hypotheses pin the concrete model that *justifies* the renewal input
  `hrenew` below; they are kept for fidelity even though the proof routes through `hrenew`.

* **(F3) A-priori kernel bound.**  `IsTransitionKernel` does not force `pR ≤ 1`; we add
  `hle1 : pR t r ≤ 1` (the known interface gap from the `lem_free` campaign), used for the
  degenerate short-time range `t ≤ 1`.

**Route taken (sanctioned fallback).**  Tiers 1–2 (semigroup identification and the
Fourier free-kernel `C₀/√(1+t)` bound) and the excursion/renewal representation enter as a
*single documented faithful hypothesis bundle* `hrenew`, with an absolute free-kernel
constant `C₁` (Tier-2, uniform in `q → 1`) quantified before `q`.  `hrenew` bundles the
paper's three intermediate estimates, each provable for the concrete `R`-walk and none of
which is the conclusion:
* **(occupation)** `∫₀ᵗ (pR u 1 + pR u (-1)) du ≤ (1+K) C₁ √t` — the window-consuming
  occupation-of-the-adjacent-set bound (this is where `ν_sp t ≤ K` enters);
* **(zero-decomposition)** `pR t 0 ≤ e^{-νt} + ε ∫₀ᵗ (pR u 1 + pR u (-1)) du` — decomposing
  `{R(t)=0}` on the last merge before `t` (or none);
* **(renewal)** for `t ≥ 1`, `r ≠ 0`,
  `pR t r ≤ ν ∫₀ᵗ (e^{-νu} + C₁ ε √u)(C₁/√(1+(t-u))) du` — the excursion renewal integral
  with the standard zero-occupation estimate `pR u 0 ≤ e^{-νu} + C₁ ε √u` inserted.
What is **proved here** from `hrenew`: the `t ≤ 1` degenerate case, the `r = 0` assembly
(from occupation + zero-decomposition), and the `r ≠ 0` convolution-splitting/window
assembly (from the renewal integral, `Rlclt_conv_exp`, `Rlclt_conv_sqrt` and the window
arithmetic `ε t = ν t/(2q²) ≤ K/(2q₀²)`), combined into the single `q`-uniform `C`.
-/
theorem lem_Rlclt
    (K : ℝ) (hK : 0 < K)
    (q₀ : ℝ) (hq₀ : q₀ ∈ Set.Ioo (0 : ℝ) 1)
    (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ), q ∈ Set.Ico q₀ 1 →
      ∀ (rate : ℤ → ℤ → ℝ) (pR : ℝ → ℤ → ℝ),
        IsTransitionKernel rate pR →
        (∀ (t : ℝ) (r : ℤ), 0 ≤ t → pR t r ≤ 1) →
        (∀ x : ℤ, 2 ≤ |x| → ∀ y, rate x y =
           (if y = x + 1 ∨ y = x - 1 then 1 + q ^ 2 else 0)) →
        (rate 0 1 = q ^ 2 * (1 - q ^ 2) ∧ rate 0 (-1) = q ^ 2 * (1 - q ^ 2)) →
        (rate 1 0 = 1 - q ^ 2 ∧ rate (-1) 0 = 1 - q ^ 2) →
        (∀ y : ℤ, 2 ≤ |y| → rate 0 y = 0) →
        (∀ y : ℤ, y ≠ 0 → rate 1 y = if y = 2 then 1 + q ^ 2 else 0) →
        (∀ y : ℤ, y ≠ 0 → rate (-1) y = if y = -2 then 1 + q ^ 2 else 0) →
        ( (∀ t : ℝ, 0 ≤ t →
              (∫ u in (0:ℝ)..t, (pR u 1 + pR u (-1))) ≤ (1 + K) * C₁ * Real.sqrt t)
          ∧ (∀ t : ℝ, 0 ≤ t →
              pR t 0 ≤ Real.exp (-(2 * q ^ 2 * (1 - q ^ 2) * t))
                + (1 - q ^ 2) * (∫ u in (0:ℝ)..t, (pR u 1 + pR u (-1))))
          ∧ (∀ t : ℝ, 1 ≤ t → ∀ r : ℤ, r ≠ 0 →
              pR t r ≤ (2 * q ^ 2 * (1 - q ^ 2))
                * ∫ u in (0:ℝ)..t,
                    (Real.exp (-(2 * q ^ 2 * (1 - q ^ 2) * u)) + C₁ * (1 - q ^ 2) * Real.sqrt u)
                      * (C₁ / Real.sqrt (1 + (t - u)))) ) →
        ∀ t : ℝ, 0 ≤ t → 2 * q ^ 2 * (1 - q ^ 2) * t ≤ K → ∀ r : ℤ,
          pR t r ≤ C / Real.sqrt (1 + t)
            + (if r = 0 then Real.exp (-(2 * q ^ 2 * (1 - q ^ 2) * t)) else 0) := by
  refine' ⟨ ( 1 + K ) * C₁ * ( 1 + K / ( 2 * q₀ ^ 2 ) ) + ( C₁ * Real.sqrt 2 + 2 * C₁ * ( 2 + K ) + 2 * Real.sqrt 2 * C₁ ^ 2 * K * Real.sqrt ( K / ( 2 * q₀ ^ 2 ) ) ) + Real.sqrt 2 + 1, _, _ ⟩;
  · positivity;
  · intro q hq rate pR hker hle1 hbulk hsplit hmerge hzero_far hone hnegone hrenew t ht hwin r;
    by_cases hr : r = 0;
    · by_cases ht1 : t ≤ 1;
      · rw [ if_pos hr ];
        refine' le_add_of_le_of_nonneg ( le_trans ( hle1 t r ht ) _ ) ( Real.exp_nonneg _ );
        rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( by linarith ) ) ];
        nlinarith [ show 0 ≤ ( 1 + K ) * C₁ * ( 1 + K / ( 2 * q₀ ^ 2 ) ) by exact mul_nonneg ( mul_nonneg ( by linarith ) ( by linarith ) ) ( by exact add_nonneg zero_le_one ( div_nonneg ( by linarith ) ( by nlinarith [ hq₀.1, hq₀.2 ] ) ) ), show 0 ≤ C₁ * Real.sqrt 2 by positivity, show 0 ≤ 2 * C₁ * ( 2 + K ) by positivity, show 0 ≤ 2 * Real.sqrt 2 * C₁ ^ 2 * K * Real.sqrt ( K / ( 2 * q₀ ^ 2 ) ) by positivity, Real.sqrt_nonneg 2, Real.sqrt_nonneg ( 1 + t ), Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ 1 + t by linarith ) ];
      · have hz := hrenew.2.1 t ht
        have ho := hrenew.1 t ht
        have hεt : (1 - q ^ 2) * t ≤ K / (2 * q₀ ^ 2) := by
          rw [ le_div_iff₀ ] <;> nlinarith [ show 0 < q₀ ^ 2 by exact sq_pos_of_pos hq₀.1, show q₀ ^ 2 ≤ q ^ 2 by nlinarith [ hq₀.1, hq₀.2, hq.1, hq.2 ] ];
        have hkey : (1 - q ^ 2) * ∫ u in (0:ℝ)..t, (pR u 1 + pR u (-1)) ≤ ((1 + K) * C₁ * (1 + K / (2 * q₀ ^ 2))) / Real.sqrt (1 + t) := by
          refine le_trans ( mul_le_mul_of_nonneg_left ho <| sub_nonneg.mpr <| by nlinarith [ hq.1, hq.2, hq₀.1, hq₀.2 ] ) ?_;
          rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( by linarith ) ) ];
          rw [ mul_assoc ];
          refine' le_trans ( mul_le_mul_of_nonneg_left ( show ( 1 + K ) * C₁ * Real.sqrt t * Real.sqrt ( 1 + t ) ≤ ( 1 + K ) * C₁ * ( 1 + t ) by nlinarith [ show 0 ≤ ( 1 + K ) * C₁ by positivity, show Real.sqrt t * Real.sqrt ( 1 + t ) ≤ 1 + t by rw [ ← Real.sqrt_mul <| by positivity ] ; exact Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith ⟩ ] ) <| sub_nonneg.mpr <| by nlinarith [ hq.1, hq.2, hq₀.1, hq₀.2 ] ) _;
          nlinarith [ show 0 < ( 1 + K ) * C₁ by positivity ];
        rw [ hr, if_pos rfl ];
        refine le_trans hz ?_;
        rw [ add_comm ];
        refine' add_le_add ( le_trans hkey _ ) le_rfl;
        gcongr;
        exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( le_add_of_nonneg_right <| by positivity ) <| by positivity ) <| by positivity;
    · by_cases ht1 : t ≤ 1;
      · refine' le_add_of_le_of_nonneg _ _;
        · refine' le_trans ( hle1 t r ht ) _;
          rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( by linarith ) ) ];
          nlinarith [ show 0 ≤ ( 1 + K ) * C₁ * ( 1 + K / ( 2 * q₀ ^ 2 ) ) by exact mul_nonneg ( mul_nonneg ( by linarith ) ( by linarith ) ) ( by exact add_nonneg zero_le_one ( div_nonneg ( by linarith ) ( by nlinarith [ hq₀.1, hq₀.2 ] ) ) ), show 0 ≤ C₁ * Real.sqrt 2 by positivity, show 0 ≤ 2 * C₁ * ( 2 + K ) by positivity, show 0 ≤ 2 * Real.sqrt 2 * C₁ ^ 2 * K * Real.sqrt ( K / ( 2 * q₀ ^ 2 ) ) by positivity, Real.sqrt_nonneg 2, Real.sqrt_nonneg ( 1 + t ), Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ 1 + t by linarith ) ];
        · split_ifs ; positivity;
      · have hbound := Rlclt_renewal_integral_bound (2 * q ^ 2 * (1 - q ^ 2)) (1 - q ^ 2) C₁ K (K / (2 * q₀ ^ 2)) (by
        exact mul_pos ( mul_pos two_pos ( sq_pos_of_pos ( by linarith [ hq₀.1, hq.1 ] ) ) ) ( by nlinarith [ hq₀.1, hq₀.2, hq.1, hq.2 ] )) (by
        nlinarith [ sq_nonneg ( q ^ 2 - 1 ), hq.1, hq.2 ]) (by
        nlinarith [ hq.1, hq.2, hq₀.1, hq₀.2 ]) (by
        nlinarith [ hq.1, hq.2 ]) (by
        positivity) (by
        linarith) (by
        exact div_nonneg hK.le ( mul_nonneg zero_le_two ( sq_nonneg _ ) )) t (by linarith) (by
        linarith) (by
        rw [ le_div_iff₀ ] <;> nlinarith [ show 0 < q₀ ^ 2 by exact sq_pos_of_pos hq₀.1, show q₀ ^ 2 ≤ q ^ 2 by exact pow_le_pow_left₀ hq₀.1.le hq.1 2 ]);
        refine le_trans ( hrenew.2.2 t ( by linarith ) r hr ) ?_;
        simp [hr];
        exact hbound.trans ( div_le_div_of_nonneg_right ( by nlinarith [ show 0 ≤ ( 1 + K ) * C₁ * ( 1 + K / ( 2 * q₀ ^ 2 ) ) by exact mul_nonneg ( mul_nonneg ( by linarith ) ( by linarith ) ) ( by exact add_nonneg zero_le_one ( div_nonneg ( by linarith ) ( by nlinarith [ hq₀.1, hq₀.2 ] ) ) ), Real.sqrt_nonneg 2 ] ) ( Real.sqrt_nonneg _ ) )

/-! ## `lem:KR` — Kolmogorov–Rogozin anti-concentration -/

/-- Largest atom (concentration function) of an integer-valued random variable `Y`:
`Q(Y) = sup_x ℙ(Y = x)`. -/
noncomputable def concentration {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℤ) : ℝ :=
  ⨆ x : ℤ, (μ (Y ⁻¹' {x})).toReal

/-- **Lemma `lem:KR`** (Kolmogorov–Rogozin anti-concentration; \cite[Ch.~III]{Petrov}).
There is a universal constant `C` such that for independent integer-valued
`Y₁,…,Yₙ`, the largest atom of the sum obeys
`Q(Y₁+⋯+Yₙ) ≤ C · (Σⱼ (1 − Q(Yⱼ)))^{−1/2}`.

*Classical cited result, black box (`sorry`).* -/
theorem kolmogorov_rogozin :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (n : ℕ) (Y : Fin n → Ω → ℤ),
      (∀ j, Measurable (Y j)) → iIndepFun Y μ →
      0 < (∑ j, (1 - concentration μ (Y j))) →
      concentration μ (fun ω => ∑ j, Y j ω)
        ≤ C / Real.sqrt (∑ j, (1 - concentration μ (Y j))) := by
  obtain ⟨C, hC, hb⟩ := KR.KR_abstract
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ n Y hmeas hindep hW
  have hsummeas : Measurable (fun ω => ∑ j, Y j ω) := by fun_prop
  exact hb n (fun j x => (μ (Y j ⁻¹' {x})).toReal)
      (fun x => (μ ((fun ω => ∑ j, Y j ω) ⁻¹' {x})).toReal)
      (fun j x => KR.pmf_nonneg μ (Y j) x)
      (fun j => KR.pmf_hasSum μ (Y j) (hmeas j))
      (fun x => KR.pmf_nonneg μ _ x)
      (KR.pmf_hasSum μ (fun ω => ∑ j, Y j ω) hsummeas)
      (fun t => KR.cf_pmf_sum_eq_prod μ n Y hmeas hindep t)
      hW

/-! ## `lem:Slclt` — conditional concentration for the sum coordinate -/

/-
**Lemma `lem:Slclt`** (conditional concentration for the sum coordinate).
Given the *unsigned skeleton* `𝔖` (the `R`-path together with the pair-hop times),
the sum coordinate is `S(t) = m(𝔖) + Σ_{j≤M} η_j` with the `η_j` conditionally
independent two-valued increments, each value of probability in `[δ,1−δ]`; hence by
Kolmogorov–Rogozin `ℙ(S(t)=s' ∣ 𝔖) ≤ C/√(1+M)`, and the number `M` of ambiguous
jumps stochastically dominates a rate-`1` Poisson count, so `ℙ(M < t/2) ≤ e^{−ct}`.

*Cited/assumed result.*  The two genuinely mathematical pieces are
stated concretely: (a) the conditional law of `S(t)` is that of
`shift + Σ_{j<M} η_j` with the `η_j` independent two-valued increments each value of
probability `≥ δ`, whose largest atom is `≤ C₀/√(δ(1+M))`; and (b) the ambiguous-jump count
`Mrv` stochastically dominates a rate-`1` Poisson variable, giving `ℙ(Mrv<t/2) ≤ e^{−ct}`.

**Fidelity fix (statement strengthening).**  As originally encoded, part (a) read
`∃ C, … ≤ C / √(1+M)` with the constant `C` existentially quantified *after* `M`, `δ`
were fixed; that makes it vacuously satisfiable (take `C = √(1+M)`) and does not express
the paper's claim.  We restore fidelity exactly as in the earlier `log₊` correction: the
existential over the universal constant is pulled to the *front*, before `M`, `η`, `shift`,
`δ`, so a single `C` must work for **all** admissible data, and the `δ`-dependence is made
explicit inside the bound as `C / √(δ·(1+M))` (equivalently `(C/√δ)/√(1+M)`, i.e. the
effective constant `C₀ = C/√δ` depends only on `δ`).  The mild, faithful hypothesis
`δ ≤ 1` (the two-valued atom probabilities force `δ ≤ 1/2` whenever `M ≥ 1`) is recorded so
the universal-in-`δ` bound is also correct in the degenerate empty case `M = 0`, where the
sum is deterministic and the largest atom equals `1`.  Part (b) is likewise stated with its
constant `c` quantified before `t`, so the exponential bound holds uniformly for all `t ≥ 0`.
Both parts are now genuinely proved (no `sorry`), from the Kolmogorov–Rogozin bound
`kolmogorov_rogozin` and the Poisson lower-tail Chernoff bound `KR.poisson_lower_tail`.
-/
theorem lem_Slclt (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (M : ℕ) (η : Fin M → Ω → ℤ) (shift : ℤ) (δ : ℝ), 0 < δ → δ ≤ 1 →
        (∀ j, Measurable (η j)) → iIndepFun η μ →
        (∀ j, ∃ u v : ℤ, u ≠ v ∧ δ ≤ (μ (η j ⁻¹' {u})).toReal ∧ δ ≤ (μ (η j ⁻¹' {v})).toReal) →
        concentration μ (fun ω => shift + ∑ j, η j ω) ≤ C / Real.sqrt (δ * (1 + (M : ℝ))))
    ∧ (∃ c : ℝ, 0 < c ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Mrv : Ω → ℕ) (t : ℝ), 0 ≤ t →
        (∀ k : ℕ, (μ {ω | Mrv ω < k}).toReal
            ≤ Real.exp (-t) * ∑ i ∈ Finset.range k, t ^ i / i.factorial) →
        (μ {ω | (Mrv ω : ℝ) < t / 2}).toReal ≤ Real.exp (-(c * t))) := by
  constructor;
  · obtain ⟨ CKR, hCKR_pos, hKR ⟩ := TypeDDecoupling.kolmogorov_rogozin;
    refine' ⟨ Max.max ( CKR * Real.sqrt 2 ) 1, _, _ ⟩ <;> norm_num;
    intro Ω _ μ _ M η shift δ hδ_pos hδ_le_one hmeas hindep htwo
    have h_concentration : concentration μ (fun ω => shift + ∑ j, η j ω) = concentration μ (fun ω => ∑ j, η j ω) := by
      convert TypeDDecoupling.KR.atomSup_add_const μ ( fun ω => ∑ j, η j ω ) shift using 1;
    by_cases hM_pos : 0 < M;
    · have h_sum_bound : ∑ j, (1 - concentration μ (η j)) ≥ M * δ := by
        have h_sum_bound : ∀ j, 1 - concentration μ (η j) ≥ δ := by
          intro j
          obtain ⟨u, v, huv, hu, hv⟩ := htwo j
          have h_concentration_le : concentration μ (η j) ≤ 1 - δ := by
            convert TypeDDecoupling.KR.atomSup_two_valued_le μ ( η j ) ( hmeas j ) δ u v huv hu hv using 1
          linarith;
        exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => h_sum_bound _ );
      have h_final_bound : CKR / Real.sqrt (∑ j, (1 - concentration μ (η j))) ≤ CKR * Real.sqrt 2 / Real.sqrt (δ * (1 + M)) := by
        rw [ div_le_div_iff₀ ] <;> try positivity;
        · rw [ mul_assoc, ← Real.sqrt_mul ( by positivity ) ];
          exact mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| by nlinarith [ show ( M : ℝ ) ≥ 1 by norm_cast ] ) hCKR_pos.le;
        · exact Real.sqrt_pos.mpr ( lt_of_lt_of_le ( by positivity ) h_sum_bound );
      exact h_concentration.symm ▸ le_trans ( hKR μ M η hmeas hindep ( by nlinarith [ show ( M : ℝ ) ≥ 1 by norm_cast ] ) ) ( h_final_bound.trans ( by gcongr ; norm_num ) );
    · interval_cases M ; norm_num at *;
      rw [ h_concentration, show concentration μ ( fun _ => 0 ) = 1 from ?_ ];
      · rw [ le_div_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg δ, Real.sq_sqrt hδ_pos.le, le_max_right ( CKR * Real.sqrt 2 ) 1 ];
      · convert TypeDDecoupling.KR.atomSup_const μ 0 using 1;
  · obtain ⟨ c, hc₀, hc ⟩ := TypeDDecoupling.KR.poisson_lower_tail;
    exact ⟨ c, hc₀, fun { Ω } _ μ _ Mrv t ht h => hc μ Mrv t ht h ⟩

/-! ## `thm:karamata` — Karamata's Tauberian theorem -/

/-
If `u ∼ v` and `v` is eventually nonzero, then `u` is eventually nonzero.
-/
lemma isEquivalent_eventually_ne {u v : ℝ → ℝ} {l : Filter ℝ}
    (h : IsEquivalent l u v) (hv : ∀ᶠ x in l, v x ≠ 0) : ∀ᶠ x in l, u x ≠ 0 := by
  have hv_nonzero := hv;
  rw [ Asymptotics.isEquivalent_iff_exists_eq_mul ] at h;
  obtain ⟨ φ, hφ, huv ⟩ := h; filter_upwards [ huv, hv_nonzero, hφ.eventually_ne one_ne_zero ] with x hx₁ hx₂ hx₃; aesop;

/-
**Theorem `thm:karamata`** (Karamata's Tauberian theorem, constant-`L` case).

*Citations.*  The general **measurable**-`L` statement
(`ω(λ) ∼ λ^{−ρ} L(1/λ) ⇔ ∫₀ˢ p ∼ s^ρ L(s)/Γ(ρ+1)` for `L` slowly varying)
is the cited literature: \cite[Thm.~1.7.1′]{BGT}, \cite[§XIII.5]{Feller2}.

*Fidelity note (the project's sixth catch).*  The statement previously encoded here
quantified over **all** pointwise slowly varying `L` with **no measurability** hypothesis.
But the cited theorems require `L` measurable, and the slowly-varying theory (the
uniform-convergence theorem for regularly varying functions) genuinely fails for
non-measurable `L`; the encoded statement therefore *exceeded* the cited literature and was
not a faithful citation.  The sole consumer `lem_tau` only ever instantiates `L` at a
**constant** (`L ≡ m(r)/(2√a)`, `ρ = 1/2`), so we restate and **prove** the theorem at
constant `L`, i.e. with a constant `c > 0`.  The proof (finite-measure Karamata method) is in
`TypeDDecouplingKaramata`.

For `p ≥ 0` (on `t ≥ 0`), with `e^{−λt}p` integrable for every `λ > 0`, `ρ > 0`, `c > 0`, and
`ω(λ) = ∫₀^∞ e^{−λt}p(t)dt`, the **Tauberian** implication — the one `lem_tau` consumes —
holds: `ω(λ) ∼ c·λ^{−ρ}  (λ↓0)  ⟹  ∫₀ˢ p ∼ c·s^ρ/Γ(ρ+1)  (s→∞)`.
-/
theorem karamata_tauberian
    (p : ℝ → ℝ) (ρ c : ℝ)
    (hp : ∀ t, 0 ≤ t → 0 ≤ p t)
    (hint : ∀ lam, 0 < lam → IntegrableOn (fun t => Real.exp (-(lam * t)) * p t) (Set.Ioi 0))
    (hρ : 0 < ρ) (hc : 0 < c)
    (ω : ℝ → ℝ) (hω : ∀ lam, 0 < lam → ω lam = ∫ t in Set.Ioi (0:ℝ), Real.exp (-(lam * t)) * p t)
    (hLaplace : IsEquivalent (𝓝[>] (0:ℝ)) ω (fun lam => c * lam ^ (-ρ))) :
    IsEquivalent atTop (fun s => ∫ t in (0:ℝ)..s, p t)
      (fun s => c * s ^ ρ / Real.Gamma (ρ + 1)) := by
  have hlim : Tendsto (fun lam => lam ^ ρ * TypeDDecouplingKaramata.lap p lam)
      (𝓝[>] (0:ℝ)) (𝓝 c) := by
    have := hLaplace.isLittleO.tendsto_div_nhds_zero;
    convert this.mul_const c |> Filter.Tendsto.const_add c |> Filter.Tendsto.congr' _ |> Filter.Tendsto.mono_left <| nhdsWithin_mono _ _ using 2 <;> norm_num;
    filter_upwards [ self_mem_nhdsWithin ] with x hx ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hx.out.ne', ne_of_gt ( Real.rpow_pos_of_pos hx.out _ ), ne_of_gt hc, hω x hx.out, TypeDDecouplingKaramata.lap ] ; ring;
    simp +decide [ Real.rpow_neg hx.out.le, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( Real.rpow_pos_of_pos hx.out _ ) ]
  exact TypeDDecouplingKaramata.tauberian_isEquivalent
    { p := p, ρ := ρ, c := c, hp := hp, hint := hint, hρ := hρ, hc := hc, hlim := hlim }

/-! ## `lem:tau` — occupation-time asymptotics -/

/-- The structural hypotheses of Lemma `lem:tau`: an irreducible, recurrent walk on `ℤ`,
reversible with respect to a measure `m` with `c₁ ≤ m ≤ c₂` and `m ≡ 1` off a finite set,
agreeing off a finite set with the symmetric nearest-neighbour walk of rate `a` per
direction. -/
structure OccupationWalk where
  rate : ℤ → ℤ → ℝ
  p : ℝ → ℤ → ℝ
  m : ℤ → ℝ
  a : ℝ
  c₁ : ℝ
  c₂ : ℝ
  F : Finset ℤ
  a_pos : 0 < a
  c₁_pos : 0 < c₁
  isKernel : IsTransitionKernel rate p
  m_lb : ∀ x, c₁ ≤ m x
  m_ub : ∀ x, m x ≤ c₂
  m_one_off : ∀ x, x ∉ F → m x = 1
  reversible : ∀ x y, m x * rate x y = m y * rate y x
  free_off : ∀ x, x ∉ F → ∀ y, rate x y = (if y = x + 1 ∨ y = x - 1 then a else 0)
  recurrent : ∀ r : ℤ, ¬ Summable (fun (n : ℕ) => p (n : ℝ) r)

/-
**Lemma `lem:tau`** (occupation-time asymptotics).  For such a walk and every fixed
`r`, `τ_r(s) := ∫₀ˢ ℙ₀(X(t)=r) dt ∼ m(r) √(s/(π a))` as `s → ∞`.

*Derived here* (the paper's derivation "from detailed balance, the first-passage
decomposition, and Karamata").  The detailed-balance / first-passage step is taken as the
explicit hypothesis `hLaplace`: the Laplace transform `ω(λ) = ∫₀^∞ e^{−λt} ℙ₀(X(t)=r) dt`
has the small-`λ` asymptotics `ω(λ) ∼ λ^{−1/2}·m(r)/(2√a)`.  The transfer from this Laplace
behaviour to the occupation-time asymptotics is then performed by genuinely invoking
Karamata's Tauberian theorem `karamata_tauberian` (with `ρ = 1/2` and the constant slowly
varying function `L ≡ m(r)/(2√a)`), using `Γ(3/2) = √π/2` to match constants.

Constant-matching for `lem_tau`: `m(r)·√(s/(πa)) = (m(r)/(2√a))·s^{1/2}/Γ(3/2)`
(using `Γ(3/2) = √π/2`).
-/
lemma lem_tau_const_match (W : OccupationWalk) (r : ℤ) :
    (fun s => W.m r * Real.sqrt (s / (Real.pi * W.a)))
      = (fun s => (W.m r / (2 * Real.sqrt W.a)) * s ^ (1/2 : ℝ) / Real.Gamma (1/2 + 1)) := by
  ext s; norm_num [ Real.sqrt_eq_rpow, Real.Gamma_add_one, Real.pi_pos.le, W.a_pos.le ] ; ring;
  by_cases hs : 0 ≤ s;
  · rw [ show ( 3 / 2 : ℝ ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one ( by norm_num ), Real.Gamma_one_half_eq ] ; ring;
    norm_num [ ← Real.sqrt_eq_rpow, mul_assoc, mul_comm, mul_left_comm, hs, Real.pi_pos.le, W.a_pos.le ];
  · norm_num [ ← Real.sqrt_eq_rpow, Real.sqrt_eq_zero_of_nonpos ( show s * Real.pi⁻¹ * W.a⁻¹ ≤ 0 by exact mul_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonpos_of_nonneg ( le_of_not_ge hs ) ( inv_nonneg.2 Real.pi_pos.le ) ) ( inv_nonneg.2 W.a_pos.le ) ), Real.sqrt_eq_zero_of_nonpos ( show s ≤ 0 by linarith ) ]

theorem lem_tau (W : OccupationWalk) (r : ℤ)
    (ω : ℝ → ℝ)
    (hω : ∀ lam, 0 < lam → ω lam
            = ∫ t in Set.Ioi (0:ℝ), Real.exp (-(lam * t)) * W.p t r)
    (hLaplace : IsEquivalent (𝓝[>] (0:ℝ)) ω
            (fun lam => lam ^ (-(1/2 : ℝ)) * (W.m r / (2 * Real.sqrt W.a)))) :
    IsEquivalent atTop (fun s => occupation W.p r s)
      (fun s => W.m r * Real.sqrt (s / (Real.pi * W.a))) := by
  have hmpos : 0 < W.m r := lt_of_lt_of_le W.c₁_pos (W.m_lb r)
  have hspos : 0 < Real.sqrt W.a := Real.sqrt_pos.mpr W.a_pos
  have hcpos : 0 < W.m r / (2 * Real.sqrt W.a) := div_pos hmpos (by positivity)
  have hp : ∀ t, 0 ≤ t → 0 ≤ W.p t r := fun t ht => W.isKernel.2.1 t ht r
  -- Put `hLaplace` in the `c · λ^{-ρ}` shape consumed by `karamata_tauberian`.
  have hLaplace' : IsEquivalent (𝓝[>] (0:ℝ)) ω
      (fun lam => (W.m r / (2 * Real.sqrt W.a)) * lam ^ (-(1/2 : ℝ))) := by
    have hEq : (fun lam : ℝ => lam ^ (-(1/2 : ℝ)) * (W.m r / (2 * Real.sqrt W.a)))
        = (fun lam => (W.m r / (2 * Real.sqrt W.a)) * lam ^ (-(1/2 : ℝ))) := by
      funext lam; ring
    rwa [hEq] at hLaplace
  -- Integrability of `e^{-λt} ℙ₀(X(t)=r)`: the Laplace transform is (eventually) nonzero.
  have hne : ∀ᶠ lam in 𝓝[>] (0:ℝ), ω lam ≠ 0 :=
    isEquivalent_eventually_ne hLaplace' <| by
      filter_upwards [self_mem_nhdsWithin] with lam hlam
      exact ne_of_gt (mul_pos hcpos (Real.rpow_pos_of_pos hlam _))
  have hint : ∀ lam, 0 < lam →
      IntegrableOn (fun t => Real.exp (-(lam * t)) * W.p t r) (Set.Ioi 0) :=
    TypeDDecouplingKaramata.integrableOn_exp_mul_of_eventually_ne (fun t => W.p t r) ω hω hne
  have key := karamata_tauberian (fun t => W.p t r) (1/2) (W.m r / (2 * Real.sqrt W.a))
    hp hint (by norm_num) hcpos ω hω hLaplace'
  -- Match the constants: `c·s^{1/2}/Γ(3/2) = m(r)·√(s/(πa))`, using `Γ(3/2) = √π/2`.
  rw [lem_tau_const_match W r]
  simpa only [occupation] using key

/-! ## `lem:occ` — adjacent-set occupation bound (occupation half) -/

/-
**Lemma `lem:occ` (occupation half)**.  After the split, with no re-binding, the
relative walk `R` performs the no-merge walk; its adjacent-set occupation
`Λ_T = ∫_τ^T 𝟙{|R(t)|=1} dt` has expectation `O(√T)`.  Schematically: the expected
occupation of `{±1}` under the no-merge kernel `pR` up to time `T` is `≤ C √T`.

*Formalized and proved here* from the cited on-diagonal bound `hfree` (the output of
`lem:free` for the no-merge walk): integrating `Cf/√(1+t)` over `[0,T]` gives the
`O(√T)` occupation.
-/
theorem lem_occ_occupation
    (pR : ℝ → ℤ → ℝ) (hnn : ∀ t r, 0 ≤ pR t r)
    (hfree : ∃ Cf : ℝ, 0 < Cf ∧ ∀ t : ℝ, 0 ≤ t → ∀ r : ℤ, pR t r ≤ Cf / Real.sqrt (1 + t)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T →
      occupation pR 1 T + occupation pR (-1) T ≤ C * Real.sqrt (1 + T) := by
  obtain ⟨Cf, hCf_pos, hCf⟩ := hfree
  use 4 * Cf + 1; (
  refine' ⟨ by positivity, fun T hT => _ ⟩
  have h_integrable : ∀ r : ℤ, occupation pR r T ≤ ∫ t in (0:ℝ)..T, Cf / Real.sqrt (1 + t) := by
    intro r
    unfold occupation
    generalize_proofs at *; (
    rw [ intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT ];
    refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
    · exact Filter.Eventually.of_forall fun x => hnn x r;
    · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( Real.continuous_sqrt.continuousAt.comp <| continuousAt_const.add continuousAt_id ) <| ne_of_gt <| Real.sqrt_pos.mpr <| by linarith [ hx.1 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using hCf x hx.1.le r)
  generalize_proofs at *; (
  refine' le_trans ( add_le_add ( h_integrable 1 ) ( h_integrable ( -1 ) ) ) _ ; norm_num [ div_eq_mul_inv ] ; ring_nf ; (
  rw [ intervalIntegral.integral_comp_add_left fun x => ( Real.sqrt x ) ⁻¹ ] ; norm_num [ Real.sqrt_eq_rpow, integral_rpow ] ; ring_nf ; norm_num [ hT ] ; (
  rw [ intervalIntegral.integral_congr fun x hx => by rw [ ← Real.rpow_neg ( by linarith [ Set.mem_Icc.mp ( by simpa [ hT ] using hx ) ] ) ] ] ; norm_num [ integral_rpow ] ; ring_nf ; norm_num [ hT ] ; nlinarith [ Real.rpow_nonneg ( by linarith : 0 ≤ 1 + T ) ( 1 / 2 : ℝ ) ] ;));))

/-! ## `lem:rebind` — no re-binding -/

/-
**Lemma `lem:rebind`** (no re-binding).  In the crossover scaling `q = 1 − c/T`, the
expected number of merges in `[τ,T]` is `O(c/√T) → 0`.  Schematically: there is `C` with
expected merge count `≤ C c / √T → 0` as `T → ∞`.

*Formalized and proved here* via the paper's identity
`merges = ε · occupation` (taking the `O(√T)` occupation bound `hoccbound` from
`lem:free`/`lem:occ` as the cited input): with merge rate `ε = 1−q² = 1−(1−c/T)²` and the `O(√T)`
occupation `occ` of `{±1}` (from `lem:free`/`lem:occ`), the expected merge count is
`ε·occ = O(c/√T) → 0`.
-/
theorem lem_rebind (c : ℝ) (hc : 0 < c)
    (occ : ℝ → ℝ) (hocc : ∀ T, 0 ≤ occ T)
    (hoccbound : ∃ Cocc : ℝ, 0 < Cocc ∧ ∀ T : ℝ, 0 ≤ T → occ T ≤ Cocc * Real.sqrt (1 + T))
    (mergeCount : ℝ → ℝ)
    (hmerge : ∀ T : ℝ, mergeCount T = (1 - (1 - c / T) ^ 2) * occ T) :
    (∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → mergeCount T ≤ C * c / Real.sqrt T)
    ∧ Tendsto (fun T => mergeCount T) atTop (𝓝 0) := by
  constructor;
  · obtain ⟨ Cocc, hCocc₁, hCocc₂ ⟩ := hoccbound;
    refine' ⟨ 2 * Cocc * Real.sqrt 2, by positivity, fun T hT => _ ⟩;
    refine le_trans ( hmerge T ▸ mul_le_mul_of_nonneg_right ( show 1 - ( 1 - c / T ) ^ 2 ≤ 2 * c / T by
                                                                ring_nf; nlinarith [ inv_mul_cancel₀ ( by linarith : T ≠ 0 ) ] ; ) ( hocc T ) ) ?_;
    refine le_trans ( mul_le_mul_of_nonneg_left ( hCocc₂ T ( by positivity ) ) ( by positivity ) ) ?_;
    field_simp;
    rw [ ← Real.sqrt_mul <| by positivity ] ; exact Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ sq_nonneg ( T - 1 ), Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ) ] ⟩;
  · -- We'll use the fact that $occ(T) \leq Cocc \sqrt{1+T}$ to bound $mergeCount(T)$.
    obtain ⟨Cocc, hCocc_pos, hCocc_bound⟩ := hoccbound;
    have h_merge_bound : ∀ T, 1 ≤ T → mergeCount T ≤ (2 * c / T) * Cocc * Real.sqrt (1 + T) := by
      intros T hT
      rw [hmerge]
      have h_bound : (1 - (1 - c / T) ^ 2) * occ T ≤ (2 * c / T) * occ T := by
        exact mul_le_mul_of_nonneg_right ( by ring_nf; nlinarith [ inv_mul_cancel₀ ( by linarith : T ≠ 0 ), inv_pos.2 ( by linarith : 0 < T ) ] ) ( hocc T );
      simpa only [ mul_assoc ] using h_bound.trans ( mul_le_mul_of_nonneg_left ( hCocc_bound T ( by positivity ) ) ( by positivity ) );
    -- We'll use the fact that $2 * c / T * Cocc * \sqrt{1 + T}$ tends to $0$ as $T$ tends to infinity.
    have h_lim : Filter.Tendsto (fun T : ℝ => 2 * c / T * Cocc * Real.sqrt (1 + T)) Filter.atTop (nhds 0) := by
      -- We can simplify the expression inside the limit further by dividing the numerator and the denominator by $T$.
      suffices h_simplify'' : Filter.Tendsto (fun T : ℝ => 2 * c * Cocc * Real.sqrt (1 / T + 1 / T^2)) Filter.atTop (nhds 0) by
        refine h_simplify''.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT using by rw [ show 1 / T + 1 / T ^ 2 = ( 1 + T ) / T ^ 2 by ring_nf; norm_num [ sq, mul_assoc, hT.ne' ] ] ; rw [ Real.sqrt_div' _ ( by positivity ), Real.sqrt_sq hT.le ] ; ring );
      exact le_trans ( Filter.Tendsto.mul tendsto_const_nhds <| Filter.Tendsto.sqrt <| Filter.Tendsto.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) <| tendsto_const_nhds.div_atTop <| by norm_num ) <| by norm_num;
    refine' squeeze_zero_norm' _ h_lim;
    filter_upwards [ Filter.eventually_ge_atTop 1, Filter.eventually_gt_atTop ( c : ℝ ) ] with T hT₁ hT₂ using by rw [ Real.norm_of_nonneg ( hmerge T ▸ mul_nonneg ( sub_nonneg.2 ( pow_le_one₀ ( sub_nonneg.2 ( div_le_one_of_le₀ ( by linarith ) ( by linarith ) ) ) ( sub_le_self _ ( by exact div_nonneg hc.le ( by linarith ) ) ) ) ) ( hocc T ) ) ] ; exact h_merge_bound T hT₁;

/-! ## `lem:asep` — same-species channel kernel bound -/

/-- The same-species two-particle dual kernel `p_t(ξ,ξ')` (a two-particle ASEP), as a
function of the asymmetry parameter `q`.

**Fidelity repair (de-opaquing).**  This kernel was previously an `opaque` object whose
Green's-function content was carried by an unprovable `sorry` (`asepGreen_integral_decay`)
and an `opaque asepGreenIntegrand` (a schematic contour integrand).  It is now
*synthesised* concretely as Schütz's two-particle Green's function in the reflection
(`F`-basis) representation `TypeDDecoupling.Bethe.asepReflect`, built from the
single-particle asymmetric-walk kernel `TypeDDecoupling.Bethe.Fkern`.  The same-species
dual rates are read off the reversible measure `m(0)=q^{-2}` of the relative walk
(`RelativeWalkTW`): detailed balance gives the ratio `rL/rR = q²`, so we take right rate
`rR = 1` and left rate `rL = q²` (asymmetry `ρ = q² ∈ (0,1)`).  See
`TypeDDecouplingBethe.lean` for the construction, the derivation of the reflection
amplitude from the exclusion boundary condition (`Bethe.Smatrix_boundary`), and the decay
`Bethe.asepReflect_decay`.

The two `opaque` declarations and the `sorry`-ed `asepGreen_integral_decay` of the earlier
contour-integral encoding are **retired** and superseded by this `F`-basis representation
(the paper's §1.5 Green's-function mapping is now traceable through `Bethe.asepReflect`). -/
noncomputable def asepKernel (q : ℝ) : ℝ → (ℤ × ℤ) → (ℤ × ℤ) → ℝ :=
  fun t ξ ξ' => TypeDDecoupling.Bethe.asepReflect 1 (q ^ 2) t ξ ξ'

/-- **Lemma `lem:asep`** (same-species channel; \cite{Schutz, TW08}).  The same-species
two-particle dual kernel (the two-particle ASEP `asepKernel q`) obeys
`p_t(ξ,ξ') ≤ C/(1+t)`.

**Now unconditional.**  The earlier version carried a hypothesis `hGreen` (the kernel as a
contour integral of the `opaque asepGreenIntegrand`) and its proof rested on the
`sorry`-ed `asepGreen_integral_decay`.  With `asepKernel q` synthesised as the reflection
representation `Bethe.asepReflect 1 q²`, the bound is a theorem with **no** extra
hypothesis: it follows from the single-particle local-CLT decay `|F_m(t)| ≤ C₁/√(1+t)`
(`Bethe.Fkern_decay`) and geometric summability of the reflection amplitudes
(`Bethe.asepReflect_decay`), taking `C = C₁²(1 + 2/(1−q²))`.

The reflection amplitudes themselves are fixed by the exclusion boundary condition, proved
separately at the Bethe-eigenfunction level as `Bethe.Smatrix_boundary`.  Duality for the
dual kernel is Schütz's \cite{Schutz} ("Duality relations for asymmetric exclusion
processes", J. Stat. Phys. 86, 1997); the explicit two-particle Green's function is from
Schütz's companion paper (J. Stat. Phys. 88, 1997; cond-mat/9701019), also in \cite{TW08}.
The hypothesis `q ∈ (0,1)` is inhabited (e.g. `q = 1/2`). -/
theorem lem_asep
    (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ ξ ξ' : ℤ × ℤ,
      asepKernel q t ξ ξ' ≤ C / (1 + t) := by
  obtain ⟨hq0, hq1⟩ := hq
  have hq2 : q ^ 2 < 1 := by nlinarith
  obtain ⟨C, hC, hbound⟩ :=
    TypeDDecoupling.Bethe.asepReflect_decay 1 (q ^ 2) one_pos (by positivity) hq2
  refine ⟨C, hC, fun t ht ξ ξ' => ?_⟩
  calc asepKernel q t ξ ξ'
      = TypeDDecoupling.Bethe.asepReflect 1 (q ^ 2) t ξ ξ' := rfl
    _ ≤ |TypeDDecoupling.Bethe.asepReflect 1 (q ^ 2) t ξ ξ'| := le_abs_self _
    _ ≤ C / (1 + t) := hbound t ht ξ ξ'

/-! ## `thm:kernel` — type D two-particle dual kernel bound -/

/-
**Theorem `thm:kernel`** (type D two-particle kernel bound).  For the
different-species dual started from a bound pair, in the window `ν_sp t ≤ K`,
`p_t(ξ,ξ') ≤ C/(1+t) + e^{−ν_sp t} · C/√(1+t)`, with `ν_sp = 2q²ε`.

*Assembled here from the cited local-CLT lemmas.* The different-species kernel is rendered
schematically as `p2 : ℝ → (ℤ × ℤ) → (ℤ × ℤ) → ℝ`, and the assembly is made explicit by
factoring it (hypothesis `hfact`) through a sum-coordinate factor `Smarg` and a
relative-coordinate factor `Rmarg`.  The two cited inputs enter as the marginal bounds:
`hS` is the sum-coordinate local CLT (`lem:Slclt`/`lem:KR`), `Smarg t ≤ C_S/√(1+t)`, and
`hR` is the defected relative-coordinate local CLT (`lem:Rlclt`),
`Rmarg t ≤ C_R/√(1+t) + e^{−ν_sp t}`.  Multiplying the two and using
`√(1+t)·√(1+t) = 1+t` produces the claimed `C/(1+t) + e^{−ν_sp t}·C/√(1+t)` bound.
-/
theorem thm_kernel
    (q : ℝ)
    (p2 : ℝ → (ℤ × ℤ) → (ℤ × ℤ) → ℝ) (K : ℝ)
    (Smarg Rmarg : ℝ → (ℤ × ℤ) → (ℤ × ℤ) → ℝ)
    (hSnn : ∀ t ξ ξ', 0 ≤ Smarg t ξ ξ')
    (hfact : ∀ t ξ ξ', p2 t ξ ξ' ≤ Smarg t ξ ξ' * Rmarg t ξ ξ')
    (hS : ∃ CS : ℝ, 0 < CS ∧ ∀ t : ℝ, 0 ≤ t → ∀ ξ ξ' : ℤ × ℤ,
        Smarg t ξ ξ' ≤ CS / Real.sqrt (1 + t))
    (hR : ∃ CR : ℝ, 0 < CR ∧ ∀ t : ℝ, 0 ≤ t → 2 * q ^ 2 * (1 - q ^ 2) * t ≤ K →
        ∀ ξ ξ' : ℤ × ℤ,
        Rmarg t ξ ξ' ≤ CR / Real.sqrt (1 + t)
          + Real.exp (-(2 * q ^ 2 * (1 - q ^ 2) * t))) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → 2 * q ^ 2 * (1 - q ^ 2) * t ≤ K →
      ∀ ξ ξ' : ℤ × ℤ,
      p2 t ξ ξ' ≤ C / (1 + t)
        + Real.exp (-(2 * q ^ 2 * (1 - q ^ 2) * t)) * (C / Real.sqrt (1 + t)) := by
  obtain ⟨ CS, hCS_pos, hCS ⟩ := hS; obtain ⟨ CR, hCR_pos, hCR ⟩ := hR; use CS * CR + CS; refine' ⟨ by positivity, fun t ht ht' ξ ξ' ↦ le_trans ( hfact t ξ ξ' ) _ ⟩ ; refine' le_trans ( mul_le_mul_of_nonneg_left ( hCR t ht ht' ξ ξ' ) ( hSnn t ξ ξ' ) ) _ ; ring_nf;
  refine' le_trans ( add_le_add ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( hCS t ht ξ ξ' ) hCR_pos.le ) ( by positivity ) ) ( mul_le_mul_of_nonneg_right ( hCS t ht ξ ξ' ) ( by positivity ) ) ) _;
  field_simp;
  nlinarith [ show 0 ≤ CR * Real.sqrt ( 1 + t ) * Real.exp ( t * q ^ 2 * 2 * ( -1 + q ^ 2 ) ) by positivity, show 0 ≤ CR * Real.sqrt ( 1 + t ) by positivity, show 0 ≤ Real.sqrt ( 1 + t ) * Real.exp ( t * q ^ 2 * 2 * ( -1 + q ^ 2 ) ) by positivity, Real.sqrt_nonneg ( 1 + t ), Real.mul_self_sqrt ( show 0 ≤ 1 + t by positivity ) ]

/-! ## `prop:occ` — contact occupations of the relative walk (Tracy–Widom regime) -/

/-- The relative walk `𝔯` of the Tracy–Widom regime, reversible with respect to the
measure `m(0)=q^{-2}`, `m(r)=1` (`r≠0`), agreeing off a finite set with the symmetric
nearest-neighbour walk of rate `1+q²` per direction. -/
structure RelativeWalkTW (q : ℝ) where
  rate : ℤ → ℤ → ℝ
  p : ℝ → ℤ → ℝ
  F : Finset ℤ
  isKernel : IsTransitionKernel rate p
  m0 : ∀ x : ℤ, x ∉ F → ∀ y, rate x y =
       (if y = x + 1 ∨ y = x - 1 then 1 + q ^ 2 else 0)
  reversible : (q ^ (-2 : ℤ)) * rate 0 1 = rate 1 0
            ∧ (q ^ (-2 : ℤ)) * rate 0 (-1) = rate (-1) 0
  recurrent : ∀ r : ℤ, ¬ Summable (fun (n : ℕ) => p (n : ℝ) r)

/-
**Proposition `prop:occ`** (contact occupations of the relative walk).  With the
stickiness measure `m(0)=q^{-2}`, `m(±1)=1`, the occupation-time ratio satisfies
`τ₀(s)/τ_{±1}(s) → q^{-2}` and the contact combination satisfies
`(1+q⁴)τ₀ − q²(τ_{+1}+τ_{−1}) ∼ (1−q⁴)/q² · √(s/(π(1+q²)))`.

*Derived here as an application of `lem:tau`.* The three cited inputs `htau0`, `htau1`,
`htaum1` are exactly the conclusions of `lem:tau` for `r = 0, 1, −1`, instantiated with the
stickiness measure `m(0) = q^{-2}`, `m(±1) = 1` and rate `a = 1+q²`.  The ratio limit
follows by dividing the two equivalences (`IsEquivalent.div`), and the contact-combination
asymptotics follows because the leading coefficient `(1+q⁴)q^{-2} − 2q² = (1−q⁴)/q²` does
not vanish, so the lower-order remainders combine into a genuine `o(√s)`.
-/
theorem prop_occ (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (W : RelativeWalkTW q)
    (htau0 : IsEquivalent atTop (fun s => occupation W.p 0 s)
        (fun s => q ^ (-2 : ℤ) * Real.sqrt (s / (Real.pi * (1 + q ^ 2)))))
    (htau1 : IsEquivalent atTop (fun s => occupation W.p 1 s)
        (fun s => Real.sqrt (s / (Real.pi * (1 + q ^ 2)))))
    (htaum1 : IsEquivalent atTop (fun s => occupation W.p (-1) s)
        (fun s => Real.sqrt (s / (Real.pi * (1 + q ^ 2))))) :
    Tendsto (fun s => occupation W.p 0 s / occupation W.p 1 s) atTop (𝓝 (q ^ (-2 : ℤ)))
    ∧ IsEquivalent atTop
        (fun s => (1 + q ^ 4) * occupation W.p 0 s
                    - q ^ 2 * (occupation W.p 1 s + occupation W.p (-1) s))
        (fun s => (1 - q ^ 4) / q ^ 2 * Real.sqrt (s / (Real.pi * (1 + q ^ 2)))) := by
  constructor;
  · have h_div : (fun s => occupation W.p 0 s / occupation W.p 1 s) ~[atTop] (fun s => q ^ (-2 : ℤ) * Real.sqrt (s / (Real.pi * (1 + q ^ 2))) / Real.sqrt (s / (Real.pi * (1 + q ^ 2)))) := by
      apply_rules [ Asymptotics.IsEquivalent.div ];
    have h_simplify : (fun s => q ^ (-2 : ℤ) * Real.sqrt (s / (Real.pi * (1 + q ^ 2))) / Real.sqrt (s / (Real.pi * (1 + q ^ 2)))) =ᶠ[atTop] (fun _ => q ^ (-2 : ℤ)) := by
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with s hs using mul_div_cancel_right₀ _ <| ne_of_gt <| Real.sqrt_pos.mpr <| by positivity;
    exact h_div.congr_right h_simplify |> fun h => h.tendsto_const;
  · -- Now use the fact that the difference of equivalent functions is little-o of the equivalent function.
    have h_diff : (fun s => (1 + q ^ 4) * occupation W.p 0 s - q ^ 2 * (occupation W.p 1 s + occupation W.p (-1) s) - ((1 - q ^ 4) / q ^ 2) * Real.sqrt (s / (Real.pi * (1 + q ^ 2)))) =o[atTop] (fun s => Real.sqrt (s / (Real.pi * (1 + q ^ 2)))) := by
      have h_diff : (fun s => occupation W.p 0 s - q ^ (-2 : ℤ) * Real.sqrt (s / (Real.pi * (1 + q ^ 2))) ) =o[atTop] (fun s => Real.sqrt (s / (Real.pi * (1 + q ^ 2)))) ∧ (fun s => occupation W.p 1 s - Real.sqrt (s / (Real.pi * (1 + q ^ 2))) ) =o[atTop] (fun s => Real.sqrt (s / (Real.pi * (1 + q ^ 2)))) ∧ (fun s => occupation W.p (-1) s - Real.sqrt (s / (Real.pi * (1 + q ^ 2))) ) =o[atTop] (fun s => Real.sqrt (s / (Real.pi * (1 + q ^ 2)))) := by
        simp_all +decide [ Asymptotics.IsEquivalent ];
        exact ⟨ by simpa using htau0.trans_isBigO ( Asymptotics.isBigO_const_mul_self _ _ _ ), htau1, htaum1 ⟩;
      convert h_diff.1.const_mul_left ( 1 + q ^ 4 ) |> Asymptotics.IsLittleO.sub <| h_diff.2.1.const_mul_left ( q ^ 2 ) |> Asymptotics.IsLittleO.add <| h_diff.2.2.const_mul_left ( q ^ 2 ) using 2 ; ring;
      norm_cast ; norm_num [ hq.1.ne', hq.2.ne', pow_succ, mul_assoc, mul_comm, mul_left_comm ] ; ring;
      grind;
    refine' h_diff.trans_isBigO _;
    norm_num [ Asymptotics.isBigO_iff ];
    refine' ⟨ 1 / ( |1 - q ^ 4| / q ^ 2 ), 1, fun s hs => _ ⟩ ; rw [ abs_of_nonneg ( Real.sqrt_nonneg _ ) ] ; ring_nf;
    norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < 1 - q ^ 4 by nlinarith [ hq.1, hq.2, pow_pos hq.1 2, pow_pos hq.1 3 ] ), ne_of_gt hq.1 ]

end TypeDDecoupling