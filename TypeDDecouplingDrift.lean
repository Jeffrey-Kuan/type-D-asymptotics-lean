import Mathlib

/-!
# `prop:drift` — the finite-`N` quantitative core

This file formalises, `sorry`-free, the two finite-algebra estimates behind `prop:drift`
of the type-D ASEP decoupling paper (brief `tierB_drift_orthcomplete.tex`):

* `drift_sbp_bound` (Lemma `sbp`): a **deterministic** summation-by-parts + Taylor estimate,
  valid for *every* configuration `η` and any centering `ρ`, showing that the rescaled
  gradient current `N^{1/2} ∑ φ'(x/N)(η_x − η_{x+1})` agrees with the discrete Laplacian
  `N^{-1/2} ∑ φ''(x/N)(η_x − ρ)` up to `O(N^{-1/2})`;

* `corr_second_moment` (Lemma `corr`): under *any* product probability weight the
  second moment of the correction functional
  `F = γ N^{1/2} ∑ φ'(x/N)(g_x − E[g_x])`, `g_x = η_{x+1}(1−η_x)`, is `O(γ² N²) = O(c²/N²)`.
  The mechanism is that centred two-site functions have vanishing covariance at distance
  `≥ 2` under product weights (`gval_indep_of_disjoint`), the same disjoint-support
  independence as `expect_V_mul_V_eq_zero` in `TypeDDecouplingEqvarOrth.lean`.

The passage from these two estimates to the `𝒮'(ℝ)`-valued `L²`-convergence
`Γ^N → D·Y(Δφ)` involves the limiting distribution-valued field and the time integral
under stationarity, and stays hypothesis-level (see `TypeDDecouplingEW.lean`, `prop_drift`).
-/

open scoped BigOperators
open Finset

namespace TypeDDecoupling.Drift

/-! ## Part A.1 — Deterministic summation by parts + Taylor (`lem:sbp`) -/

/-
**Summation by parts (Abel) with vanishing boundary.**  If `f (a−1) = 0` and `f b = 0`
then the discrete gradient current equals the discrete divergence:
`∑_{a≤x≤b} f x (η x − η (x+1)) = ∑_{a≤x≤b} (f x − f (x−1)) η x`.  No boundary terms appear.
-/
lemma sbp_identity (f η : ℤ → ℝ) (a b : ℤ) (hab : a ≤ b)
    (hfa : f (a - 1) = 0) (hfb : f b = 0) :
    ∑ x ∈ Finset.Icc a b, f x * (η x - η (x + 1))
      = ∑ x ∈ Finset.Icc a b, (f x - f (x - 1)) * η x := by
  simp_all +decide [ mul_sub ];
  have h_shift : ∑ x ∈ Finset.Icc a b, f x * η (x + 1) = ∑ x ∈ Finset.Icc (a + 1) (b + 1), f (x - 1) * η x := by
    apply Finset.sum_bij (fun x hx => x + 1);
    · exact fun x hx => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], by linarith [ Finset.mem_Icc.mp hx ] ⟩;
    · aesop;
    · exact fun x hx => ⟨ x - 1, Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], by linarith [ Finset.mem_Icc.mp hx ] ⟩, by ring ⟩;
    · grind;
  have h_split : ∑ x ∈ Finset.Icc (a + 1) (b + 1), f (x - 1) * η x = ∑ x ∈ Finset.Icc a b, f (x - 1) * η x := by
    rw [ show ( Finset.Icc ( a + 1 ) ( b + 1 ) ) = Finset.Icc a b \ { a } ∪ { b + 1 } from ?_, Finset.sum_union ] <;> norm_num [ Finset.sum_singleton, Finset.sum_sdiff, * ];
    grind;
  simp_all +decide [ sub_mul ]

/-
**Lemma `sbp`.**  Deterministic summation-by-parts + Taylor estimate.  For every
configuration `η` (bounded by `1`) and every centering `ρ ∈ [0,1]`, the rescaled gradient
current `N^{1/2} ∑ φ'(x/N)(η_x − η_{x+1})` agrees with the discrete Laplacian
`N^{-1/2} ∑ φ''(x/N)(η_x − ρ)` up to `O(N^{-1/2})`, with an explicit constant in
`K, ‖φ'''‖ (= M3)` and the Riemann-sum bound `CK` on `∑ φ''`.
-/
lemma drift_sbp_bound
    (N : ℕ) (hN : 1 ≤ N) (K : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (dphi ddphi : ℝ → ℝ) (M3 CK : ℝ) (hM3 : 0 ≤ M3)
    (η : ℤ → ℝ) (hη : ∀ x, |η x| ≤ 1)
    (hsupp : ∀ x : ℤ, (K : ℝ) * N < |(x : ℝ)| → dphi ((x : ℝ) / N) = 0)
    (hTaylor : ∀ x : ℤ,
        |(dphi ((x : ℝ) / N) - dphi (((x : ℝ) - 1) / N)) - ddphi ((x : ℝ) / N) / N|
          ≤ M3 / (2 * (N : ℝ) ^ 2))
    (hRiemann :
        |∑ x ∈ Finset.Icc (-(K : ℤ) * N - 1) ((K : ℤ) * N + 1), ddphi ((x : ℝ) / N)| ≤ CK) :
    |Real.sqrt N * (∑ x ∈ Finset.Icc (-(K : ℤ) * N - 1) ((K : ℤ) * N + 1),
          dphi ((x : ℝ) / N) * (η x - η (x + 1)))
        - (Real.sqrt N)⁻¹ * (∑ x ∈ Finset.Icc (-(K : ℤ) * N - 1) ((K : ℤ) * N + 1),
          ddphi ((x : ℝ) / N) * (η x - ρ))|
      ≤ (M3 * (2 * (K : ℝ) + 3) / 2 + CK) / Real.sqrt N := by
  -- Apply `sbp_identity` to rewrite the sum.
  have sbp_identity_applied : ∑ x ∈ Finset.Icc (-(K:ℤ)*N-1) ((K:ℤ)*N+1), dphi ((x:ℝ)/N) * (η x - η (x + 1)) = ∑ x ∈ Finset.Icc (-(K:ℤ)*N-1) ((K:ℤ)*N+1), (dphi ((x:ℝ)/N) - dphi (((x:ℝ)-1)/N)) * η x := by
    convert sbp_identity _ _ _ _ _ _ _ using 1;
    · norm_num;
    · nlinarith;
    · convert hsupp ( -K * N - 1 - 1 ) _ using 1 ; norm_num;
      grind;
    · convert hsupp ( K * N + 1 ) _ using 1 ; norm_num [ abs_of_nonneg, add_nonneg, mul_nonneg, hN ];
  -- Apply the Taylor expansion to each term in the sum.
  have taylor_expansion : ∑ x ∈ Finset.Icc (-(K:ℤ)*N-1) ((K:ℤ)*N+1), (dphi ((x:ℝ)/N) - dphi (((x:ℝ)-1)/N)) * η x = ∑ x ∈ Finset.Icc (-(K:ℤ)*N-1) ((K:ℤ)*N+1), (ddphi ((x:ℝ)/N) / N) * η x + ∑ x ∈ Finset.Icc (-(K:ℤ)*N-1) ((K:ℤ)*N+1), (dphi ((x:ℝ)/N) - dphi (((x:ℝ)-1)/N) - ddphi ((x:ℝ)/N) / N) * η x := by
    simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun _ _ => by ring;
  -- Apply the triangle inequality to the sum.
  have triangle_inequality : |∑ x ∈ Finset.Icc (-(K:ℤ)*N-1) ((K:ℤ)*N+1), (dphi ((x:ℝ)/N) - dphi (((x:ℝ)-1)/N) - ddphi ((x:ℝ)/N) / N) * η x| ≤ (2 * K * N + 3) * M3 / (2 * N^2) := by
    refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => _ ) _;
    use fun x => M3 / ( 2 * N ^ 2 );
    · simpa only [ abs_mul ] using mul_le_of_le_one_right ( abs_nonneg _ ) ( hη x ) |> le_trans <| hTaylor x;
    · norm_num [ mul_div_assoc ];
      exact mul_le_mul_of_nonneg_right ( mod_cast by linarith [ Int.toNat_of_nonneg ( by nlinarith : 0 ≤ ( K : ℤ ) * N + 1 + 1 - ( - ( K * N ) - 1 ) ) ] ) ( by positivity );
  -- Apply the triangle inequality to the sum and simplify.
  have triangle_inequality_simplified : |Real.sqrt N * (∑ x ∈ Finset.Icc (-(K:ℤ)*N-1) ((K:ℤ)*N+1), (ddphi ((x:ℝ)/N) / N) * η x) - (Real.sqrt N)⁻¹ * (∑ x ∈ Finset.Icc (-(K:ℤ)*N-1) ((K:ℤ)*N+1), ddphi ((x:ℝ)/N) * (η x - ρ))| ≤ CK / Real.sqrt N := by
    field_simp [mul_comm, mul_assoc, mul_left_comm] at *;
    norm_num [ ← Finset.sum_div _ _ _, mul_sub ] at *;
    norm_num [ mul_div_cancel₀, ne_of_gt ( zero_lt_one.trans_le hN ) ] at *;
    norm_num [ ← Finset.sum_mul _ _ _, abs_div, abs_mul, abs_of_nonneg ( Real.sqrt_nonneg _ ) ] at *;
    rw [ mul_div_cancel₀ _ ( by positivity ) ] ; exact le_trans ( mul_le_of_le_one_right ( by positivity ) ( abs_le.mpr ⟨ by linarith, by linarith ⟩ ) ) hRiemann;
  rw [ abs_le ] at *;
  field_simp at *;
  norm_num [ ← Finset.sum_div _ _ _ ] at *;
  constructor <;> nlinarith [ show ( N : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( ∑ i ∈ Finset.Icc ( - ( K * N : ℤ ) - 1 ) ( K * N + 1 ), ddphi ( i / N ) * η i ) ( by positivity : ( N : ℝ ) ≠ 0 ), mul_div_cancel₀ ( ∑ i ∈ Finset.Icc ( - ( K * N : ℤ ) - 1 ) ( K * N + 1 ), ( N * ( dphi ( i / N ) - dphi ( ( i - 1 ) / N ) ) - ddphi ( i / N ) ) * η i ) ( by positivity : ( N : ℝ ) ≠ 0 ) ]

/-! ## Part A.2 — Correction second moment under product weights (`lem:corr`)

A single-species product probability weight over the finite window `Λ`.  A configuration
`c : SConfig Λ` assigns a `{0,1}` occupation to each site; the weight `W(c) = ∏_s p_s(c_s)`
is an arbitrary product of per-site probability vectors `p_s`.  The correction observable is
`g_x = η_{x+1}(1 − η_x)`, a two-site function.  Centred, such functions have vanishing
covariance at distance `≥ 2` (`gval_cov_zero`), the disjoint-support independence used to
bound the correction second moment. -/

/-- Single-species configuration on the window `Λ`. -/
abbrev SConfig (Λ : Finset ℤ) : Type := {x : ℤ // x ∈ Λ} → Bool

variable (Λ : Finset ℤ)

/-- Real occupation (`0`/`1`; `0` off the window). -/
noncomputable def socc (x : ℤ) (c : SConfig Λ) : ℝ :=
  if h : x ∈ Λ then (if c ⟨x, h⟩ then (1 : ℝ) else 0) else 0

/-- The two-site correction observable `g_x = η_{x+1}(1 − η_x)`. -/
noncomputable def gval (x : ℤ) (c : SConfig Λ) : ℝ := socc Λ (x + 1) c * (1 - socc Λ x c)

/-- Product probability weight `W(c) = ∏_s p_s(c_s)`. -/
noncomputable def Wp (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (c : SConfig Λ) : ℝ := ∏ s, p s (c s)

/-- Expectation `E_p[f] = ∑_c W(c) f(c)`. -/
noncomputable def Ep (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (f : SConfig Λ → ℝ) : ℝ :=
  ∑ c, Wp Λ p c * f c

/-- Per-site multiplier realising `g_x` as a product of single-site functions. -/
noncomputable def uloc (x : ℤ) (s : {x : ℤ // x ∈ Λ}) (b : Bool) : ℝ :=
  if (s : ℤ) = x + 1 then (if b then (1 : ℝ) else 0)
  else if (s : ℤ) = x then (1 - (if b then (1 : ℝ) else 0))
  else 1

/-
**Master factorization.**  The expectation of a product of per-site functions factorizes
into a product of per-site expectations (Fubini for the product measure).
-/
lemma Ep_prod_local (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (u : {x : ℤ // x ∈ Λ} → Bool → ℝ) :
    Ep Λ p (fun c => ∏ s, u s (c s)) = ∏ s, ∑ b, p s b * u s b := by
  simp +decide only [Ep, Wp];
  simp +decide only [← prod_mul_distrib, Fintype.prod_sum]

/-
Normalisation: `E_p[1] = 1` for a product probability weight.
-/
lemma Ep_one (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (hp : ∀ s, ∑ b, p s b = 1) :
    Ep Λ p (fun _ => 1) = 1 := by
  convert Ep_prod_local Λ p ( fun _ _ => 1 ) using 1;
  · norm_num;
  · aesop

/-
Additivity of the expectation.
-/
lemma Ep_add (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (f g : SConfig Λ → ℝ) :
    Ep Λ p (fun c => f c + g c) = Ep Λ p f + Ep Λ p g := by
  convert Finset.sum_add_distrib using 1;
  exact Finset.sum_congr rfl fun _ _ => by ring;

/-- Homogeneity of the expectation in a scalar factor. -/
lemma Ep_smul (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (k : ℝ) (f : SConfig Λ → ℝ) :
    Ep Λ p (fun c => k * f c) = k * Ep Λ p f := by
  unfold Ep
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-
The expectation commutes with a finite sum.
-/
lemma Ep_sum (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (B : Finset ℤ) (g : ℤ → SConfig Λ → ℝ) :
    Ep Λ p (fun c => ∑ x ∈ B, g x c) = ∑ x ∈ B, Ep Λ p (g x) := by
  convert Finset.sum_comm using 1;
  exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum _ _ _ ] ;

/-
Positivity of the expectation for a nonnegative weight.
-/
lemma Ep_nonneg (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (hp_nonneg : ∀ s b, 0 ≤ p s b)
    (f : SConfig Λ → ℝ) (hf : ∀ c, 0 ≤ f c) : 0 ≤ Ep Λ p f := by
  exact Finset.sum_nonneg fun c _ => mul_nonneg ( Finset.prod_nonneg fun s _ => hp_nonneg s _ ) ( hf c )

/-
Monotone bound: `|E_p[f]| ≤ M` if `|f| ≤ M` pointwise, for a product probability weight.
-/
lemma Ep_abs_le (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (hp_nonneg : ∀ s b, 0 ≤ p s b)
    (hp : ∀ s, ∑ b, p s b = 1) (f : SConfig Λ → ℝ) (M : ℝ) (hf : ∀ c, |f c| ≤ M) :
    |Ep Λ p f| ≤ M := by
  refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) _;
  refine' le_trans ( Finset.sum_le_sum fun c _ => _ ) _;
  use fun c => Wp Λ p c * M;
  · rw [ abs_mul, abs_of_nonneg ( show 0 ≤ Wp Λ p c from Finset.prod_nonneg fun _ _ => hp_nonneg _ _ ) ] ; exact mul_le_mul_of_nonneg_left ( hf c ) ( Finset.prod_nonneg fun _ _ => hp_nonneg _ _ );
  · convert mul_le_mul_of_nonneg_right ( show ∑ i : SConfig Λ, Wp Λ p i ≤ 1 from ?_ ) ( show 0 ≤ M by linarith [ abs_le.mp ( hf ( fun _ => Bool.true ) ) ] ) using 1;
    · rw [ Finset.sum_mul _ _ _ ];
    · ring;
    · convert Ep_one Λ p hp |> le_of_eq using 1;
      exact Finset.sum_congr rfl fun _ _ => by unfold Wp; aesop;

/-
`|g_x| ≤ 1` pointwise.
-/
lemma gval_abs_le_one (x : ℤ) (c : SConfig Λ) : |gval Λ x c| ≤ 1 := by
  unfold gval socc;
  split_ifs <;> norm_num

/-
`g_x` as a product of single-site functions.
-/
lemma gval_eq_prod (x : ℤ) (hx : x ∈ Λ) (hx1 : x + 1 ∈ Λ) (c : SConfig Λ) :
    gval Λ x c = ∏ s, uloc Λ x s (c s) := by
  unfold gval uloc socc;
  rw [ Finset.prod_eq_mul_prod_diff_singleton ( show ⟨ x + 1, hx1 ⟩ ∈ Finset.univ from Finset.mem_univ _ ) ];
  rw [ Finset.prod_eq_single ⟨ x, hx ⟩ ] <;> aesop

/-
**Disjoint-support independence.**  For bonds at distance `≥ 2`, `E_p[g_x g_y] =
E_p[g_x]·E_p[g_y]` (same mechanism as `expect_V_mul_V_eq_zero`).
-/
lemma gval_indep (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (hp : ∀ s, ∑ b, p s b = 1)
    (x y : ℤ) (hx : x ∈ Λ) (hx1 : x + 1 ∈ Λ) (hy : y ∈ Λ) (hy1 : y + 1 ∈ Λ)
    (hdisj : x + 1 < y ∨ y + 1 < x) :
    Ep Λ p (fun c => gval Λ x c * gval Λ y c) = Ep Λ p (gval Λ x) * Ep Λ p (gval Λ y) := by
  obtain h | h := hdisj <;> simp +decide [ *, gval_eq_prod ] at *;
  · rw [ show gval Λ x = fun c => ∏ s ∈ Λ.attach, uloc Λ x s ( c s ) from funext fun c => gval_eq_prod Λ x hx hx1 c, show gval Λ y = fun c => ∏ s ∈ Λ.attach, uloc Λ y s ( c s ) from funext fun c => gval_eq_prod Λ y hy hy1 c ];
    convert Ep_prod_local Λ p ( fun s b => uloc Λ x s b * uloc Λ y s b ) using 1;
    · simp +decide only [prod_mul_distrib];
      rfl;
    · convert congr_arg₂ ( · * · ) ( Ep_prod_local Λ p ( fun s b => uloc Λ x s b ) ) ( Ep_prod_local Λ p ( fun s b => uloc Λ y s b ) ) using 1;
      rw [ ← Finset.prod_mul_distrib ] ; congr ; ext s ; simp +decide [ mul_assoc, Finset.sum_mul _ _ _ ] ; ring;
      grind +locals;
  · convert Ep_prod_local Λ p ( fun s b => uloc Λ x s b * uloc Λ y s b ) using 1;
    · simp +decide [ Finset.prod_mul_distrib ];
    · rw [ show gval Λ x = fun c => ∏ s, uloc Λ x s ( c s ) from funext fun c => gval_eq_prod Λ x hx hx1 c, show gval Λ y = fun c => ∏ s, uloc Λ y s ( c s ) from funext fun c => gval_eq_prod Λ y hy hy1 c, Ep_prod_local, Ep_prod_local ];
      rw [ ← Finset.prod_mul_distrib ] ; congr ; ext s ; simp +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _ ] ; ring;
      unfold uloc;
      grind

/-- The centred covariance `E_p[(g_x − ḡ_x)(g_y − ḡ_y)]`. -/
noncomputable def gcov (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (x y : ℤ) : ℝ :=
  Ep Λ p (fun c => (gval Λ x c - Ep Λ p (gval Λ x)) * (gval Λ y c - Ep Λ p (gval Λ y)))

/-
**Vanishing covariance at distance `≥ 2`.**
-/
lemma gcov_zero (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (hp_nonneg : ∀ s b, 0 ≤ p s b)
    (hp : ∀ s, ∑ b, p s b = 1)
    (x y : ℤ) (hx : x ∈ Λ) (hx1 : x + 1 ∈ Λ) (hy : y ∈ Λ) (hy1 : y + 1 ∈ Λ)
    (hdisj : x + 1 < y ∨ y + 1 < x) : gcov Λ p x y = 0 := by
  unfold gcov;
  unfold Ep; simp +decide [ Finset.prod_mul_distrib, sub_mul, mul_sub ] ; ring;
  simp +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hp ];
  rw [ show ∑ i : SConfig Λ, Wp Λ p i = 1 from ?_ ] ; ring;
  · simp +decide [ mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hp ];
    convert sub_eq_zero.mpr ( gval_indep Λ p hp x y hx hx1 hy hy1 hdisj ) using 1;
  · convert Ep_one Λ p hp using 1;
    exact Finset.sum_congr rfl fun _ _ => by unfold Wp; aesop;

/-
`|gcov x y| ≤ 1` always (Cauchy–Schwarz / `|g − ḡ| ≤ 1`).
-/
lemma gcov_abs_le_one (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (hp_nonneg : ∀ s b, 0 ≤ p s b)
    (hp : ∀ s, ∑ b, p s b = 1) (x y : ℤ) : |gcov Λ p x y| ≤ 1 := by
  apply_rules [ Ep_abs_le ];
  -- By definition of $gval$, we know that $0 \leq gval \Lambda x c \leq 1$ for all $c$.
  have h_gval_bounds : ∀ x c, 0 ≤ gval Λ x c ∧ gval Λ x c ≤ 1 := by
    unfold gval socc; aesop;
  -- By definition of $Ep$, we know that $0 \leq Ep \Lambda p (gval \Lambda x) \leq 1$ for all $x$.
  have h_Ep_bounds : ∀ x, 0 ≤ Ep Λ p (gval Λ x) ∧ Ep Λ p (gval Λ x) ≤ 1 := by
    intro x;
    refine' ⟨ _, _ ⟩;
    · exact Ep_nonneg Λ p hp_nonneg _ fun c => h_gval_bounds x c |>.1;
    · convert Ep_abs_le Λ p hp_nonneg hp ( gval Λ x ) 1 ( fun c => abs_le.mpr ⟨ by linarith [ h_gval_bounds x c ], by linarith [ h_gval_bounds x c ] ⟩ ) using 1;
      rw [ abs_of_nonneg ( Ep_nonneg Λ p hp_nonneg _ fun c => h_gval_bounds x c |>.1 ) ];
  exact fun c => abs_le.mpr ⟨ by nlinarith [ h_gval_bounds x c, h_gval_bounds y c, h_Ep_bounds x, h_Ep_bounds y ], by nlinarith [ h_gval_bounds x c, h_gval_bounds y c, h_Ep_bounds x, h_Ep_bounds y ] ⟩

/-- The (un-normalised) correction functional `F₀ = ∑_{x∈B} φ'(x/N)(g_x − ḡ_x)`. -/
noncomputable def F0 (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (dphi : ℝ → ℝ) (N : ℕ) (B : Finset ℤ)
    (c : SConfig Λ) : ℝ :=
  ∑ x ∈ B, dphi ((x : ℝ) / N) * (gval Λ x c - Ep Λ p (gval Λ x))

/-
The second moment of `F₀` is the covariance quadratic form.
-/
lemma Ep_F0_sq_expand (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (dphi : ℝ → ℝ) (N : ℕ) (B : Finset ℤ) :
    Ep Λ p (fun c => (F0 Λ p dphi N B c) ^ 2)
      = ∑ x ∈ B, ∑ y ∈ B, dphi ((x : ℝ) / N) * dphi ((y : ℝ) / N) * gcov Λ p x y := by
  unfold F0 gcov;
  simp +decide only [pow_two, Finset.mul_sum _ _ _, mul_comm, mul_left_comm, mul_assoc];
  simp +decide [ Ep_sum, Ep_smul ]

/-
**Core second-moment bound.**  `E_p[F₀²] ≤ 3·|B|·‖φ'‖²`, using that only the `≤ 3`
near-diagonal covariance terms per bond survive.
-/
lemma Ep_F0_sq_le (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (hp_nonneg : ∀ s b, 0 ≤ p s b)
    (hp : ∀ s, ∑ b, p s b = 1) (dphi : ℝ → ℝ) (M : ℝ) (hM : ∀ u, |dphi u| ≤ M)
    (N : ℕ) (B : Finset ℤ) (hB : ∀ x ∈ B, x ∈ Λ ∧ x + 1 ∈ Λ) :
    Ep Λ p (fun c => (F0 Λ p dphi N B c) ^ 2) ≤ 3 * (B.card : ℝ) * M ^ 2 := by
  -- Apply the Ep_F0_sq_expand lemma to rewrite the left-hand side.
  have h_lhs : Ep Λ p (fun c => (F0 Λ p dphi N B c) ^ 2) = ∑ x ∈ B, ∑ y ∈ B, dphi ((x : ℝ) / N) * dphi ((y : ℝ) / N) * gcov Λ p x y := by
    exact Ep_F0_sq_expand Λ p dphi N B
  -- Apply the termwise bound to each term in the double sum.
  have h_termwise_bound : ∀ x ∈ B, ∑ y ∈ B, |dphi ((x : ℝ) / N) * dphi ((y : ℝ) / N) * gcov Λ p x y| ≤ 3 * M^2 := by
    intro x hx
    have h_term_bound : ∀ y ∈ B, |dphi ((x : ℝ) / N) * dphi ((y : ℝ) / N) * gcov Λ p x y| ≤ M^2 * (if (x - 1 ≤ y ∧ y ≤ x + 1) then 1 else 0) := by
      intro y hy
      by_cases hxy : x - 1 ≤ y ∧ y ≤ x + 1;
      · rw [ if_pos hxy ];
        rw [ abs_mul, abs_mul ];
        exact le_trans ( mul_le_mul ( mul_le_mul ( hM _ ) ( hM _ ) ( by positivity ) ( by linarith [ abs_nonneg ( dphi ( x / N ) ), abs_nonneg ( dphi ( y / N ) ), hM ( x / N ), hM ( y / N ) ] ) ) ( gcov_abs_le_one Λ p hp_nonneg hp x y ) ( by positivity ) ( by nlinarith [ abs_nonneg ( dphi ( x / N ) ), abs_nonneg ( dphi ( y / N ) ), hM ( x / N ), hM ( y / N ) ] ) ) ( by nlinarith );
      · rw [ if_neg hxy, MulZeroClass.mul_zero ];
        rw [ gcov_zero Λ p hp_nonneg hp x y ( hB x hx |>.1 ) ( hB x hx |>.2 ) ( hB y hy |>.1 ) ( hB y hy |>.2 ) ( by contrapose! hxy; omega ) ] ; norm_num;
    refine' le_trans ( Finset.sum_le_sum h_term_bound ) _;
    norm_num [ Finset.sum_ite ];
    exact mul_le_mul_of_nonneg_right ( mod_cast le_trans ( Finset.card_le_card <| show _ ⊆ Finset.Icc ( x - 1 ) ( x + 1 ) from fun y hy => Finset.mem_Icc.mpr <| by aesop ) <| by simp +arith +decide ) <| sq_nonneg _;
  exact h_lhs.symm ▸ le_trans ( Finset.sum_le_sum fun x hx => le_trans ( Finset.sum_le_sum fun y hy => le_abs_self _ ) ( h_termwise_bound x hx ) ) ( by simp +decide [ mul_assoc, mul_comm, mul_left_comm ] )

/-
**Lemma `corr`.**  Under any product probability weight, the correction functional
`F = γ N^{1/2} ∑_{x∈B} φ'(x/N)(g_x − ḡ_x)` has second moment `≤ γ² N · 3((2K+1)N+2)‖φ'‖²`
(when the bond count `|B| ≤ (2K+1)N+2`).  With `γ ≤ 3c/N²` this is `O(c²/N²)`.
-/
theorem corr_second_moment (p : {x : ℤ // x ∈ Λ} → Bool → ℝ) (hp_nonneg : ∀ s b, 0 ≤ p s b)
    (hp : ∀ s, ∑ b, p s b = 1) (dphi : ℝ → ℝ) (M : ℝ) (hM : ∀ u, |dphi u| ≤ M)
    (N : ℕ) (K : ℕ) (B : Finset ℤ) (hB : ∀ x ∈ B, x ∈ Λ ∧ x + 1 ∈ Λ)
    (hBcard : (B.card : ℝ) ≤ (2 * (K : ℝ) + 1) * N + 2) (γ : ℝ) :
    Ep Λ p (fun c => (γ * Real.sqrt N * F0 Λ p dphi N B c) ^ 2)
      ≤ γ ^ 2 * N * (3 * ((2 * (K : ℝ) + 1) * N + 2) * M ^ 2) := by
  have h1 : (Ep Λ p (fun c => (γ * Real.sqrt N * F0 Λ p dphi N B c)^2)) = (γ^2 * N) * (Ep Λ p (fun c => (F0 Λ p dphi N B c)^2)) := by
    convert Ep_smul Λ p ( γ ^ 2 * N ) ( fun c => F0 Λ p dphi N B c ^ 2 ) using 2 ; ring;
    norm_num;
  exact h1.symm ▸ mul_le_mul_of_nonneg_left ( le_trans ( Ep_F0_sq_le Λ p hp_nonneg hp dphi M hM N B hB ) ( by gcongr ) ) ( by positivity )

end TypeDDecoupling.Drift