import Mathlib
import TypeDDecouplingDrift

/-!
# `lem:gauss` (condition (N)) — the finite-`N` WASEP bracket computation

This is **Part 2** of the `lem_gauss` de-opaquing brief (`gauss_brief.tex`): the genuinely new,
standalone, library-clean finite-`N` facts that make the bracket hypothesis `mpConvBracket`
(consumed by the fidelity-repaired `lem_gauss` in `TypeDDecouplingEW.lean`) *faithful* for the
actual stationary single-species WASEP.

The single-species exclusion process with jump rates `(1, q²)` (right at rate `1`, left at rate
`q²`) is run under the Bernoulli(`ρ`) product weight `pber` on the window `Λ`.  Writing
`η_x ∈ {0,1}` for the occupation (`socc` of `TypeDDecouplingDrift.lean`), the two two-site jump
occupancies across the bond `(x, x+1)` are

* `gfwd x = η_x(1 − η_{x+1})` — a right jump is possible (rate `1`);
* `gval x = η_{x+1}(1 − η_x)` — a left  jump is possible (rate `q²`), the observable of
  `TypeDDecouplingDrift.lean`.

The instantaneous **bracket** (quadratic variation) of the martingale part of the field pairing
`⟨Y^N, φ⟩` is the normalized sum `bracketField`, whose per-bond weight is
`φ'(x/N)² · (gfwd x + q² · gval x)` (each jump moves the pairing by `φ'(x/N)/√N`, and squared
increments are `1`).

## Contents

* **(a) Mean** (`Ep_gval_bernoulli`, `Ep_gfwd_bernoulli`, `Ep_bracketField`,
  `bracketField_mean_tendsto`): the exact equilibrium per-bond factor is
  `E_ρ[gfwd x] = E_ρ[gval x] = ρ(1−ρ) = χ`, so `E_ρ[c_x] = (1+q²)χ`, and the normalized bracket
  mean is the Riemann sum `(1/N)∑ φ'(x/N)² · (1+q²)χ`, converging to `2χD‖φ'‖²` under the
  convention `D = (1+q²)/2` (so that `2χD = (1+q²)χ`, consistent with `prop_drift`'s `D`; see
  `bracket_two_chi_D`).
* **(b) Variance** (`bracketVar_le`): the fluctuation of the normalized bracket functional has
  second moment `O(1/N)` under the product weight, via the `corr_second_moment` pattern of
  `TypeDDecouplingDrift.lean` (finite-range covariances, `(1/N²)·O(N)` bookkeeping).
* **(c) Time integration** (`sq_intervalIntegral_le`, `timeIntegral_sq_integral_le`,
  `timeIntegral_L2_concentration`): from (a)+(b), the time-integrated bracket over `[0,t]`
  concentrates at `2χDt‖φ'‖²` in `L²` under stationarity, by equal-time Cauchy–Schwarz in time
  (no mixing needed).

These are [P]-class results consumed by `lem_gauss`'s documentation as the finite-`N` ground
truth; only the Dynkin-bracket identification and the process-level pairing construction remain
as the documented Dittrich–Gärtner citation content.

The existing files `TypeDDecouplingDrift.lean`, `TypeDDecouplingMartingaleGaussian.lean` and the
CLT files are **not** modified.
-/

open scoped BigOperators
open Finset MeasureTheory
open Filter Topology

namespace TypeDDecoupling.BracketN

open TypeDDecoupling.Drift

/-! ## The Bernoulli(ρ) product weight -/

/-- The Bernoulli(`ρ`) single-site probability vector, giving the product weight `pber Λ ρ`
(each site independently occupied with probability `ρ`). -/
noncomputable def pber (Λ : Finset ℤ) (ρ : ℝ) : {x : ℤ // x ∈ Λ} → Bool → ℝ :=
  fun _ b => if b then ρ else 1 - ρ

lemma pber_nonneg (Λ : Finset ℤ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∀ s b, 0 ≤ pber Λ ρ s b := by
  intro s b; cases b <;> simp only [pber, Bool.false_eq_true, if_true, if_false] <;> linarith

lemma pber_sum_one (Λ : Finset ℤ) (ρ : ℝ) : ∀ s, ∑ b, pber Λ ρ s b = 1 := by
  intro s; simp only [pber, Fintype.sum_bool, Bool.false_eq_true, if_true, if_false]; ring

/-! ## The forward jump occupancy `gfwd x = η_x(1 − η_{x+1})` -/

/-- The forward-jump two-site occupancy `gfwd x = η_x(1 − η_{x+1})` (a right jump across the bond
`(x,x+1)` requires `η_x = 1`, `η_{x+1} = 0`).  This is the mirror of `gval` of
`TypeDDecouplingDrift.lean`. -/
noncomputable def gfwd (Λ : Finset ℤ) (x : ℤ) (c : SConfig Λ) : ℝ :=
  socc Λ x c * (1 - socc Λ (x + 1) c)

/-- Per-site multiplier realizing `gfwd x` as a product of single-site functions (mirror of
`uloc`, with the roles of `x` and `x+1` swapped). -/
noncomputable def ufwd (Λ : Finset ℤ) (x : ℤ) (s : {x : ℤ // x ∈ Λ}) (b : Bool) : ℝ :=
  if (s : ℤ) = x then (if b then (1 : ℝ) else 0)
  else if (s : ℤ) = x + 1 then (1 - (if b then (1 : ℝ) else 0))
  else 1

/-- `|gfwd x| ≤ 1` pointwise. -/
lemma gfwd_abs_le_one (Λ : Finset ℤ) (x : ℤ) (c : SConfig Λ) : |gfwd Λ x c| ≤ 1 := by
  unfold gfwd socc; split_ifs <;> norm_num

/-
`gfwd x` as a product of single-site functions (mirror of `gval_eq_prod`).
-/
lemma gfwd_eq_prod (Λ : Finset ℤ) (x : ℤ) (hx : x ∈ Λ) (hx1 : x + 1 ∈ Λ) (c : SConfig Λ) :
    gfwd Λ x c = ∏ s, ufwd Λ x s (c s) := by
  unfold gfwd; simp +decide [ *, Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ ( ⟨ x, hx ⟩ : Λ ) ) ] ; (
  rw [ Finset.prod_eq_mul_prod_diff_singleton ( show ⟨ x, hx ⟩ ∈ Λ.attach from Finset.mem_attach _ _ ), Finset.prod_eq_single ⟨ x + 1, hx1 ⟩ ] <;> simp +decide [ *, socc ];
  · unfold ufwd; aesop;
  · unfold ufwd; aesop;)

/-! ## (a) Equilibrium means -/

/-
**(a) equilibrium mean of the backward occupancy**: `E_ρ[gval x] = ρ(1−ρ) = χ`, for a bond
`(x,x+1)` inside the window, under the Bernoulli(`ρ`) product weight.
-/
lemma Ep_gval_bernoulli (Λ : Finset ℤ) (ρ : ℝ) (x : ℤ) (hx : x ∈ Λ) (hx1 : x + 1 ∈ Λ) :
    Ep Λ (pber Λ ρ) (gval Λ x) = ρ * (1 - ρ) := by
  convert Ep_prod_local Λ ( pber Λ ρ ) ( fun s => uloc Λ x s ) using 1;
  · exact congr_arg _ ( funext fun c => gval_eq_prod Λ x hx hx1 c );
  · rw [ Finset.prod_eq_mul_prod_diff_singleton <| Finset.mem_univ ⟨ x + 1, hx1 ⟩ ] ; norm_num [ pber, uloc ] ; ring;
    rw [ Finset.prod_eq_single ⟨ x, hx ⟩ ] <;> norm_num ; ring;
    aesop

/-
**(a) equilibrium mean of the forward occupancy**: `E_ρ[gfwd x] = ρ(1−ρ) = χ`.
-/
lemma Ep_gfwd_bernoulli (Λ : Finset ℤ) (ρ : ℝ) (x : ℤ) (hx : x ∈ Λ) (hx1 : x + 1 ∈ Λ) :
    Ep Λ (pber Λ ρ) (gfwd Λ x) = ρ * (1 - ρ) := by
  convert Ep_prod_local Λ ( pber Λ ρ ) ( fun s => ufwd Λ x s ) using 1;
  · exact congr_arg _ ( funext fun c => gfwd_eq_prod Λ x hx hx1 c );
  · rw [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ ⟨ x, hx ⟩ ) ];
    rw [ Finset.prod_eq_single ⟨ x + 1, hx1 ⟩ ] <;> simp +decide [ pber, ufwd ];
    aesop

/-! ## The instantaneous bracket field and its mean -/

/-- The per-bond instantaneous bracket occupancy with rates `(1, q²)`:
`c_x = gfwd x + q² · gval x` (right jump rate `1`, left jump rate `q²`). -/
noncomputable def brBond (Λ : Finset ℤ) (q : ℝ) (x : ℤ) (c : SConfig Λ) : ℝ :=
  gfwd Λ x c + q ^ 2 * gval Λ x c

/-- The normalized instantaneous **bracket field** of the pairing `⟨Y^N,φ⟩`:
`(1/N) ∑_{x∈B} φ'(x/N)² · c_x`. -/
noncomputable def bracketField (Λ : Finset ℤ) (q : ℝ) (dphi : ℝ → ℝ) (N : ℕ) (B : Finset ℤ)
    (c : SConfig Λ) : ℝ :=
  (1 / (N : ℝ)) * ∑ x ∈ B, dphi ((x : ℝ) / N) ^ 2 * brBond Λ q x c

/-
**(a) exact equilibrium mean of the normalized bracket field** equals the explicit Riemann
sum with the per-bond factor `(1+q²)χ`, `χ = ρ(1−ρ)`.
-/
lemma Ep_bracketField (Λ : Finset ℤ) (q ρ : ℝ) (dphi : ℝ → ℝ) (N : ℕ) (B : Finset ℤ)
    (hB : ∀ x ∈ B, x ∈ Λ ∧ x + 1 ∈ Λ) :
    Ep Λ (pber Λ ρ) (bracketField Λ q dphi N B)
      = (1 / (N : ℝ)) * ∑ x ∈ B, dphi ((x : ℝ) / N) ^ 2 * ((1 + q ^ 2) * (ρ * (1 - ρ))) := by
  unfold bracketField;
  convert congr_arg _ ( Finset.sum_congr rfl fun x hx => ?_ ) using 1;
  rw [ Ep_smul, Ep_sum ];
  rw [ Ep_smul, show brBond Λ q x = fun c => gfwd Λ x c + q ^ 2 * gval Λ x c from rfl, Ep_add, Ep_smul, Ep_gfwd_bernoulli Λ ρ x ( hB x hx |>.1 ) ( hB x hx |>.2 ), Ep_gval_bernoulli Λ ρ x ( hB x hx |>.1 ) ( hB x hx |>.2 ) ] ; ring

/-- The `2χD`-normalization: with `D = (1+q²)/2`, the per-bond factor `(1+q²)χ` is exactly
`2χD`, consistent with `prop_drift`'s diffusivity `D` and the paper's `2χD` convention. -/
lemma bracket_two_chi_D (q ρ : ℝ) :
    (1 + q ^ 2) * (ρ * (1 - ρ)) = 2 * (ρ * (1 - ρ)) * ((1 + q ^ 2) / 2) := by ring

/-
**(a) convergence of the equilibrium bracket mean**: with `D = (1+q²)/2`, if the Riemann sum
`(1/N)∑_{x∈B N} φ'(x/N)²` converges to `sig` (`= ‖φ'‖_{L²}²`), then the equilibrium bracket mean
converges to `2χD·sig`, `χ = ρ(1−ρ)`.
-/
lemma bracketField_mean_tendsto (Λ : ℕ → Finset ℤ) (q ρ D sig : ℝ) (hD : D = (1 + q ^ 2) / 2)
    (dphi : ℝ → ℝ) (B : ℕ → Finset ℤ)
    (hB : ∀ N, ∀ x ∈ B N, x ∈ Λ N ∧ x + 1 ∈ Λ N)
    (hRiem : Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∑ x ∈ B N, dphi ((x : ℝ) / N) ^ 2)
      atTop (𝓝 sig)) :
    Tendsto (fun N => Ep (Λ N) (pber (Λ N) ρ) (bracketField (Λ N) q dphi N (B N)))
      atTop (𝓝 (2 * (ρ * (1 - ρ)) * D * sig)) := by
  convert hRiem.const_mul ( ( 1 + q ^ 2 ) * ( ρ * ( 1 - ρ ) ) ) using 2 ; norm_num [ bracketField ] ; ring;
  · rw [ Ep_bracketField ] ; ring;
    · simp +decide only [mul_comm, mul_left_comm, sum_add_distrib, sum_sub_distrib, Finset.mul_sum _ _ _, mul_assoc] ; ring;
      simp +decide only [mul_assoc, Finset.mul_sum _ _ _];
    · exact hB _;
  · rw [ hD ] ; ring;

/-! ## (b) Variance `O(1/N)` under the product weight -/

/-
**(b) `O(1/N)` variance** of the normalized bracket functional under any product probability
weight — the `corr_second_moment` pattern of `TypeDDecouplingDrift.lean`.  For a weight `ψ`
bounded by `Mψ` (in the bracket application `ψ = (1+q²)(φ')²`), the centered normalized
functional `(1/N)·F0` has second moment `≤ 3((2K+1)N+2)Mψ²/N² = O(1/N)` when the bond count is
`≤ (2K+1)N+2`.
-/
lemma bracketVar_le (Λ : Finset ℤ) (p : {x : ℤ // x ∈ Λ} → Bool → ℝ)
    (hp_nonneg : ∀ s b, 0 ≤ p s b) (hp : ∀ s, ∑ b, p s b = 1)
    (ψ : ℝ → ℝ) (Mψ : ℝ) (hψ : ∀ u, |ψ u| ≤ Mψ)
    (N K : ℕ) (B : Finset ℤ) (hB : ∀ x ∈ B, x ∈ Λ ∧ x + 1 ∈ Λ)
    (hBcard : (B.card : ℝ) ≤ (2 * (K : ℝ) + 1) * N + 2) :
    Ep Λ p (fun c => ((1 / (N : ℝ)) * F0 Λ p ψ N B c) ^ 2)
      ≤ (3 * ((2 * (K : ℝ) + 1) * N + 2) * Mψ ^ 2) / (N : ℝ) ^ 2 := by
  convert mul_le_mul_of_nonneg_left ( Ep_F0_sq_le Λ p hp_nonneg hp ψ Mψ hψ N B hB ) ( by positivity : 0 ≤ ( 1 / ( N : ℝ ) ) ^ 2 ) |> le_trans <| ?_ using 1;
  · convert Ep_smul Λ p _ _ using 3 ; ring;
  · convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left hBcard <| show ( 0 : ℝ ) ≤ 3 * Mψ ^ 2 by positivity ) <| show ( 0 : ℝ ) ≤ ( N : ℝ ) ⁻¹ ^ 2 by positivity using 1 ; ring;
    ring

/-! ## (c) `L²` concentration of the time-integrated bracket -/

/-
**(c) equal-time Cauchy–Schwarz in time** (deterministic): for `f` on `[0,t]`,
`(∫₀ᵗ f)² ≤ t · ∫₀ᵗ f²`.
-/
lemma sq_intervalIntegral_le (t : ℝ) (ht : 0 ≤ t) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 t)
    (hf2 : IntervalIntegrable (fun s => f s ^ 2) volume 0 t) :
    (∫ s in (0 : ℝ)..t, f s) ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, f s ^ 2 := by
  have h_cauchy_schwarz : (∫ s in Set.Ioc 0 t, (f s - (∫ u in Set.Ioc 0 t, f u) / t) ^ 2) ≥ 0 := by
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _;
  by_cases h : t = 0 <;> simp_all +decide [ sub_sq, mul_assoc, mul_comm, ← intervalIntegral.integral_of_le ht ];
  rw [ intervalIntegral.integral_add, intervalIntegral.integral_sub ] at h_cauchy_schwarz <;> norm_num at *;
  · nlinarith [ mul_div_cancel₀ ( ∫ u in ( 0 : ℝ )..t, f u ) h ];
  · exact hf2;
  · exact hf.mul_const _;
  · exact hf2.sub ( hf.mul_const _ )

/-
**(c) `L²` of the time integral**: integrating the equal-time Cauchy–Schwarz bound over the
probability space, `E[(∫₀ᵗ dev·)²] ≤ t · E[∫₀ᵗ (dev·)²]`.
-/
lemma timeIntegral_sq_integral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : ℝ) (dev : ℝ → Ω → ℝ)
    (hCS : ∀ ω, (∫ s in (0 : ℝ)..t, dev s ω) ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, (dev s ω) ^ 2)
    (hint1 : Integrable (fun ω => (∫ s in (0 : ℝ)..t, dev s ω) ^ 2) μ)
    (hint2 : Integrable (fun ω => ∫ s in (0 : ℝ)..t, (dev s ω) ^ 2) μ) :
    ∫ ω, (∫ s in (0 : ℝ)..t, dev s ω) ^ 2 ∂μ
      ≤ t * ∫ ω, (∫ s in (0 : ℝ)..t, (dev s ω) ^ 2) ∂μ := by
  simpa only [ ← MeasureTheory.integral_const_mul ] using MeasureTheory.integral_mono hint1 ( hint2.const_mul t ) hCS

/-
**(c) `L²` concentration of the time-integrated bracket**: combining the equal-time
Cauchy–Schwarz bound with the equal-time second-moment control `hstat` (the Tonelli swap of the
`O(1/N)` variance (b) under stationarity, `E[∫₀ᵗ (dev·)²] ≤ t·C`), the `L²` error of the
time-integrated bracket is `≤ t²·C`.  With `C = O(1/N)` this vanishes, giving the concentration
of the time-integrated bracket at `2χDt‖φ'‖²`.
-/
lemma timeIntegral_L2_concentration {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : ℝ) (ht : 0 ≤ t) (dev : ℝ → Ω → ℝ) (C : ℝ)
    (hCS : ∀ ω, (∫ s in (0 : ℝ)..t, dev s ω) ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, (dev s ω) ^ 2)
    (hint1 : Integrable (fun ω => (∫ s in (0 : ℝ)..t, dev s ω) ^ 2) μ)
    (hint2 : Integrable (fun ω => ∫ s in (0 : ℝ)..t, (dev s ω) ^ 2) μ)
    (hstat : ∫ ω, (∫ s in (0 : ℝ)..t, (dev s ω) ^ 2) ∂μ ≤ t * C) :
    ∫ ω, (∫ s in (0 : ℝ)..t, dev s ω) ^ 2 ∂μ ≤ t ^ 2 * C := by
  have h := timeIntegral_sq_integral_le μ t dev hCS hint1 hint2;
  convert h.trans ( mul_le_mul_of_nonneg_left hstat ht ) using 1 ; ring

end TypeDDecoupling.BracketN