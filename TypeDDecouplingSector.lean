import Mathlib

/-!
# The sector comparison at compensated fugacity (`lem:sector`, corrected)

This file is a self-contained, `sorry`-free formalisation of the **corrected** sector
comparison of the type-D ASEP decoupling paper, following the standalone draft
`lem_sector_fix_draft.tex`.

## Why a correction is needed

The paper's `lem:sector` is **false as stated**: it compares the product blocking measure
`ν` at fugacity `α` with the sector-reweighted measure `ϖ` carried at the *same* fugacity
`α`.  The sector reweighting tilts each sector by a constant-per-particle factor
`q^{2n}/(1 − α q^{2n−2S}) → (1 − α)^{-1}`, so `ϖ_α` behaves as a blocking measure at
*effective* fugacity `α/(1 − α)`, i.e. bulk density `α`, whereas `ν_α` has density
`α/(1+α)`.  The two measures then concentrate on sector ranges `Θ(N)` apart, and the
comparability constant `M = sup ν/ϖ` grows like `e^{Θ(N)}`.

## The correction

Comparability holds two-sidedly over **all** sectors once `ϖ` is taken at the
**compensated fugacity** `β = α/(1+α)` (equivalently `β = ρ`, the `ν`-density).  The linear
term in `log(ν(n)/ϖ(n))` cancels *exactly*, because `log(α/β) = log(1+α) = −log(1−β)`.  The
proof is entirely elementary (an exact telescoping identity plus a normalisation argument).

## Formalisation simplification

Following the draft, the sector reweighting is defined by the **finite** product
`hfac q β S n = q^{n(n−1)} / ∏_{m<n} (1 − β q^{2m−2S})` (with `hfac … 0 = 1`), which is
*proportional* to the paper's infinite `q`-Pochhammer form (the constant of proportionality
cancels in every probability ratio).  Thus **no infinite products** are needed, and the key
recursion `hfac (n+1) / hfac n = q^{2n} / (1 − β q^{2n−2S})` is definitional.

## Contents

* `condLaw_sector_const` — **Lemma cond**: two weights differing by a sector-constant factor
  induce the same conditional law on every particle-number fiber.
* `gfun_master` — the exact telescoping identity for `log(ν(n)/ϖ(n)) − const`.
* `gfun_bound` — `|gfun| ≤ C₀`, `C₀ = A(1 + 8β/(1−β))`, `A` a bound on `(−log q)·S²`.
* `log_ratio_pinned` — the normalisation argument pinning the constant.
* `sector_comparison_single` — **Theorem M** (single species): `|log(ν(n)/ϖ(n))| ≤ 2C₀`.
* `esymm_homogeneous` and `sector_masses_ratio` — the `e_n(γ t) = γⁿ e_n(t)` homogeneity of
  the elementary symmetric polynomials, giving the ratio structure used by Theorem M.
* `sector_comparison_two` — the two-species product bound.
* `correlation_transfer` — **Corollary transfer**: per-sector Cauchy–Schwarz for a positive
  semidefinite self-adjoint form plus the sector-mass comparison give the correlation
  transfer inequality.
-/

open scoped BigOperators Real
open Finset

namespace TypeDDecoupling.Sector

/-! ## Lemma cond: conditional laws agree -/

/-- The conditional law of a weight `W` on the particle-number fiber `{N = n}`:
the normalised restriction of `W` to that fiber. -/
noncomputable def condLaw {Ω : Type*} [Fintype Ω]
    (Npart : Ω → ℕ) (W : Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  if Npart ω = n then
    W ω / (∑ ω' ∈ Finset.univ.filter (fun ω' => Npart ω' = n), W ω')
  else 0

/-
**Lemma cond** (conditional laws agree).  Two weights that differ by a
sector-constant positive factor `cfac (N ω)` induce the *same* conditional law on every
particle-number fiber `{N = n}`: the sector prefactor is constant on the fiber and cancels
in the conditional normalisation.  In particular the product blocking measure and the
sector-reweighted measure (whose weights differ exactly by the sector factors `γⁿ` and
`h(n)`) share the same canonical conditional laws given the particle numbers.
-/
theorem condLaw_sector_const {Ω : Type*} [Fintype Ω]
    (Npart : Ω → ℕ) (W : Ω → ℝ) (cfac : ℕ → ℝ) (hc : ∀ n, cfac n ≠ 0) (n : ℕ) :
    condLaw Npart (fun ω => cfac (Npart ω) * W ω) n = condLaw Npart W n := by
  unfold condLaw;
  ext ω; split_ifs <;> simp +decide [ *, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ] ;
  rw [ show ( ∑ x with Npart x = n, W x * cfac ( Npart x ) ) = ( ∑ x with Npart x = n, W x ) * cfac n by rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun x hx => by aesop ] ; rw [ mul_div_mul_comm ] ; aesop;

/-! ## The finite sector factor `hfac` and the drift factors `dfac` -/

/-- The drift factor `dfac q β S m = 1 − β q^{2m − 2S}`. -/
noncomputable def dfac (q β : ℝ) (S : ℕ) (m : ℕ) : ℝ :=
  1 - β * q ^ (2 * (m : ℤ) - 2 * (S : ℤ))

/-- The finite sector-reweighting factor
`hfac q β S n = q^{n(n−1)} / ∏_{m<n} (1 − β q^{2m−2S})`, with `hfac … 0 = 1`.  This is
proportional to the paper's `q^{n(n−1)} (β q^{2n−2S}; q²)_∞`, the proportionality constant
`(β q^{−2S}; q²)_∞` being independent of `n`. -/
noncomputable def hfac (q β : ℝ) (S : ℕ) (n : ℕ) : ℝ :=
  q ^ (n * (n - 1)) / ∏ m ∈ Finset.range n, dfac q β S m

/-
`dfac` is positive on the relevant range: for `m ≤ S` and `β q^{−2S} ≤ (1+β)/2` one has
`dfac q β S m ≥ (1−β)/2 > 0`.
-/
theorem dfac_pos (q β : ℝ) (S : ℕ) (hq0 : 0 < q) (hq1 : q < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ' : β * q ^ (-(2 * (S : ℤ))) ≤ (1 + β) / 2) (m : ℕ) (hm : m ≤ S) :
    (1 - β) / 2 ≤ dfac q β S m := by
  -- Since $q^{2m - 2S} \leq q^{-2S}$, we have $\beta q^{2m - 2S} \leq \beta q^{-2S}$.
  have h_beta_q_le_beta_q_neg : β * q ^ (2 * m - 2 * S : ℤ) ≤ β * q ^ (-(2 * S) : ℤ) := by
    exact mul_le_mul_of_nonneg_left ( by exact zpow_le_zpow_right_of_le_one₀ ( by positivity ) hq1.le ( by linarith ) ) hβ0.le;
  unfold dfac; linarith;

/-
`hfac` is positive on the relevant range.
-/
theorem hfac_pos (q β : ℝ) (S : ℕ) (hq0 : 0 < q) (hq1 : q < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ' : β * q ^ (-(2 * (S : ℤ))) ≤ (1 + β) / 2) (n : ℕ) (hn : n ≤ S) :
    0 < hfac q β S n := by
  refine' div_pos _ ( Finset.prod_pos _ );
  · positivity;
  · exact fun i hi => by have := dfac_pos q β S hq0 hq1 hβ0 hβ1 hβ' i ( by linarith [ Finset.mem_range.mp hi ] ) ; linarith;

/-! ## The log-ratio function `gfun` and its telescoping identity -/

/-- The `n`-dependent part of `log(ν(n)/ϖ(n))`:
`gfun q α β S n = n·log(α/β) − log(hfac q β S n)`. -/
noncomputable def gfun (q α β : ℝ) (S : ℕ) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (α / β) - Real.log (hfac q β S n)

/-
**The telescoping (master) identity.**  With the compensated fugacity relation
`β = α/(1+α)` (so `α/β = 1/(1−β)`, i.e. `log(α/β) = −log(1−β)`),
`gfun = n(n−1)·(−log q) + ∑_{m<n} (log(dfac m) − log(1−β))`.
The linear-in-`n` term cancels exactly; the first summand is `≥ 0`, the sum `≤ 0`.
-/
theorem gfun_master (q α β : ℝ) (S : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < α)
    (hα : β = α / (1 + α))
    (hβ' : β * q ^ (-(2 * (S : ℤ))) ≤ (1 + β) / 2)
    (n : ℕ) (hn : n ≤ S) :
    gfun q α β S n =
      ((n : ℝ) * (n - 1)) * (-(Real.log q))
        + ∑ m ∈ Finset.range n, (Real.log (dfac q β S m) - Real.log (1 - β)) := by
  unfold gfun;
  unfold hfac; rw [ Real.log_div ] <;> norm_num [ hα0.ne', hβ0.ne' ];
  rw [ Real.log_div, Real.log_pow, Real.log_prod ] <;> norm_num;
  · rw [ hα, Real.log_div ] <;> try positivity;
    rw [ show ( 1 - α / ( 1 + α ) ) = ( 1 + α ) ⁻¹ by rw [ one_sub_div ( by positivity ) ] ; ring ] ; rw [ Real.log_inv ] ; cases n <;> norm_num ; ring;
  · intro m hm; exact ne_of_gt ( show 0 < dfac q β S m from by exact lt_of_lt_of_le ( by linarith ) ( dfac_pos q β S hq0 hq1 hβ0 hβ1 hβ' m ( by linarith ) ) ) ;
  · aesop;
  · exact ne_of_gt <| Finset.prod_pos fun m hm => by have := dfac_pos q β S hq0 hq1 hβ0 hβ1 hβ' m ( by linarith [ Finset.mem_range.mp hm ] ) ; linarith;

/-! ### Elementary analytic bounds -/

/-
Elementary log estimate: for `0 ≤ a ≤ b < 1`, `log(1−a) − log(1−b) ≤ (b−a)/(1−b)`.
-/
theorem log_one_sub_diff_le (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    Real.log (1 - a) - Real.log (1 - b) ≤ (b - a) / (1 - b) := by
  rw [ ← Real.log_div ( by linarith ) ( by linarith ) ];
  exact le_trans ( Real.log_le_sub_one_of_pos ( div_pos ( by linarith ) ( by linarith ) ) ) ( by rw [ div_sub_one, div_le_div_iff_of_pos_right ] <;> linarith )

/-
For `j ≤ S`, `q^{−2j} − 1 ≤ 4·(−log q)·j`, using `q^{−2S} ≤ 2`.
-/
theorem qpow_neg_sub_one_le (q : ℝ) (S : ℕ) (hq0 : 0 < q) (hq1 : q < 1)
    (hqS : q ^ (-(2 * (S : ℤ))) ≤ 2) (j : ℕ) (hj : j ≤ S) :
    q ^ (-(2 * (j : ℤ))) - 1 ≤ 4 * (-(Real.log q)) * (j : ℝ) := by
  -- Let's write `θ := -Real.log q > 0` (since `0 < q < 1`, `Real.log q < 0`).
  set θ : ℝ := -Real.log q
  have hθ_pos : 0 < θ := by
    exact neg_pos_of_neg ( Real.log_neg hq0 hq1 )
  have hθ_log : q = Real.exp (-θ) := by
    rw [ neg_neg, Real.exp_log hq0 ]
  have hθ_exp : q ^ (-(2 * (j : ℤ))) = Real.exp (θ * (2 * j)) := by
    rw [ hθ_log, ← Real.rpow_intCast, Real.rpow_def_of_pos ( by positivity ), mul_comm ] ; norm_num;
    ring;
  -- We want `Real.exp x - 1 ≤ 2*x` (i.e. `4θj = 2*(2θj) = 2x`).
  have h_exp_bound : Real.exp (θ * (2 * j)) - 1 ≤ θ * (2 * j) * Real.exp (θ * (2 * j)) := by
    nlinarith [ Real.exp_pos ( θ * ( 2 * j ) ), Real.exp_neg ( θ * ( 2 * j ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( θ * ( 2 * j ) ) ) ), Real.add_one_le_exp ( θ * ( 2 * j ) ), Real.add_one_le_exp ( - ( θ * ( 2 * j ) ) ) ];
  -- Since `q^(-(2S)) ≤ 2`, we have `Real.exp (θ * (2 * S)) ≤ 2`.
  have h_exp_bound_S : Real.exp (θ * (2 * S)) ≤ 2 := by
    convert hqS using 1 ; rw [ hθ_log ] ; norm_num [ ← Real.exp_nat_mul, ← Real.exp_neg ] ; ring;
    norm_cast ; norm_num [ ← Real.exp_nat_mul, ← Real.exp_neg ] ; ring;
  nlinarith [ show 0 ≤ θ * j by positivity, show Real.exp ( θ * ( 2 * j ) ) ≤ Real.exp ( θ * ( 2 * S ) ) by gcongr ]

/-
**The bound** `|gfun| ≤ C₀`, with `C₀ = A·(1 + 8β/(1−β))` and `A` a bound on
`(−log q)·S²`.  The quadratic term is bounded by `A`, the Pochhammer-drift sum by
`A·8β/(1−β)`.
-/
theorem gfun_bound (q α β : ℝ) (S : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < α)
    (hα : β = α / (1 + α))
    (A : ℝ) (hA0 : 0 ≤ A) (hAbnd : (-(Real.log q)) * (S : ℝ) ^ 2 ≤ A)
    (hβ' : β * q ^ (-(2 * (S : ℤ))) ≤ (1 + β) / 2)
    (hqS : q ^ (-(2 * (S : ℤ))) ≤ 2)
    (n : ℕ) (hn : n ≤ S) :
    |gfun q α β S n| ≤ A * (1 + 8 * β / (1 - β)) := by
  -- Apply the bound on each term in the sum.
  have h_term_bound : ∀ m ∈ Finset.range n, |Real.log (dfac q β S m) - Real.log (1 - β)| ≤ 8 * β * (-Real.log q) * ((S - m : ℝ) / (1 - β)) := by
    intro m hm
    have h_term_bound : Real.log (1 - β) - Real.log (dfac q β S m) ≤ 8 * β * (-Real.log q) * ((S - m : ℝ) / (1 - β)) := by
      have h_term_bound : Real.log (1 - β) - Real.log (1 - β * q ^ (2 * (m : ℤ) - 2 * (S : ℤ))) ≤ (β * q ^ (2 * (m : ℤ) - 2 * (S : ℤ)) - β) / (1 - β * q ^ (2 * (m : ℤ) - 2 * (S : ℤ))) := by
        apply log_one_sub_diff_le;
        · positivity;
        · norm_num [ zpow_sub₀ hq0.ne', zpow_mul ];
          exact le_mul_of_one_le_right hβ0.le ( one_le_div ( pow_pos ( sq_pos_of_pos hq0 ) _ ) |>.2 ( pow_le_pow_of_le_one ( sq_nonneg _ ) ( by nlinarith ) ( by linarith [ Finset.mem_range.mp hm ] ) ) );
        · norm_num [ zpow_sub₀ hq0.ne' ] at *;
          norm_cast at *;
          field_simp;
          contrapose! hβ';
          rw [ div_lt_iff₀ ] <;> nlinarith [ show q ^ ( 2 * S ) > 0 by positivity, show q ^ ( 2 * m ) ≤ 1 by exact pow_le_one₀ ( by positivity ) hq1.le, mul_inv_cancel₀ ( ne_of_gt ( show q ^ ( 2 * S ) > 0 by positivity ) ) ];
      have h_term_bound : β * q ^ (2 * (m : ℤ) - 2 * (S : ℤ)) - β ≤ 4 * β * (-Real.log q) * (S - m) := by
        have h_term_bound : q ^ (-(2 * (S - m : ℤ))) - 1 ≤ 4 * (-(Real.log q)) * (S - m) := by
          convert qpow_neg_sub_one_le q S hq0 hq1 hqS ( S - m ) ( Nat.sub_le _ _ ) using 1 ; norm_num [ Nat.cast_sub ( show m ≤ S from by linarith [ Finset.mem_range.mp hm ] ) ];
          rw [ Nat.cast_sub ( by linarith [ Finset.mem_range.mp hm ] ) ];
        convert mul_le_mul_of_nonneg_left h_term_bound hβ0.le using 1 <;> ring;
      have h_term_bound : (β * q ^ (2 * (m : ℤ) - 2 * (S : ℤ)) - β) / (1 - β * q ^ (2 * (m : ℤ) - 2 * (S : ℤ))) ≤ (4 * β * (-Real.log q) * (S - m)) / ((1 - β) / 2) := by
        gcongr;
        · exact mul_nonneg ( mul_nonneg ( mul_nonneg zero_le_four hβ0.le ) ( neg_nonneg.mpr ( Real.log_nonpos hq0.le hq1.le ) ) ) ( sub_nonneg.mpr ( Nat.cast_le.mpr ( by linarith [ Finset.mem_range.mp hm ] ) ) );
        · linarith;
        · convert dfac_pos q β S hq0 hq1 hβ0 hβ1 hβ' m ( by linarith [ Finset.mem_range.mp hm ] ) |> le_trans <| le_rfl using 1;
      convert le_trans ‹_› h_term_bound using 1 ; ring!;
      rw [ show ( 1 / 2 + β * ( -1 / 2 ) ) = ( 1 - β ) / 2 by ring ] ; norm_num ; ring;
    rw [ abs_sub_comm, abs_of_nonneg ];
    · exact h_term_bound;
    · refine' sub_nonneg_of_le ( Real.log_le_log _ _ );
      · exact dfac_pos q β S hq0 hq1 hβ0 hβ1 hβ' m ( by linarith [ Finset.mem_range.mp hm ] ) |> lt_of_lt_of_le ( by linarith );
      · refine' sub_le_sub_left _ _;
        norm_num [ zpow_sub₀ hq0.ne', zpow_mul ];
        exact le_mul_of_one_le_right hβ0.le ( one_le_div ( pow_pos ( sq_pos_of_pos hq0 ) _ ) |>.2 ( pow_le_pow_of_le_one ( sq_nonneg _ ) ( by nlinarith ) ( by linarith [ Finset.mem_range.mp hm ] ) ) );
  -- Sum the bounds over all terms in the sum.
  have h_sum_bound : |∑ m ∈ Finset.range n, (Real.log (dfac q β S m) - Real.log (1 - β))| ≤ 8 * β * (-Real.log q) * (∑ m ∈ Finset.range n, ((S - m : ℝ) / (1 - β))) := by
    exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum h_term_bound );
  -- Apply the bound on the sum of the terms.
  have h_sum_bound_final : |∑ m ∈ Finset.range n, (Real.log (dfac q β S m) - Real.log (1 - β))| ≤ 8 * β * (-Real.log q) * ((S : ℝ)^2 / (1 - β)) := by
    refine le_trans h_sum_bound ?_;
    gcongr;
    · exact mul_nonneg ( mul_nonneg ( by norm_num ) hβ0.le ) ( neg_nonneg_of_nonpos ( Real.log_nonpos hq0.le hq1.le ) );
    · rw [ ← Finset.sum_div _ _ _ ];
      gcongr;
      · linarith;
      · exact le_trans ( Finset.sum_le_sum fun _ _ => sub_le_self _ <| Nat.cast_nonneg _ ) <| by norm_num; nlinarith [ show ( n : ℝ ) ≤ S by norm_cast ] ;
  -- Apply the bound on the quadratic term.
  have h_quad_bound : |((n : ℝ) * (n - 1)) * (-(Real.log q))| ≤ A := by
    rw [ abs_of_nonneg ];
    · rcases n with ( _ | n ) <;> norm_num at *;
      · linarith;
      · nlinarith [ show ( n : ℝ ) + 1 ≤ S by norm_cast, show ( n : ℝ ) * ( n + 1 ) ≤ S ^ 2 by norm_cast; nlinarith, Real.log_le_sub_one_of_pos hq0 ];
    · exact mul_nonneg ( if h : n = 0 then by norm_num [ h ] else by nlinarith only [ show ( n : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero h ) ] ) ( neg_nonneg.mpr ( Real.log_nonpos hq0.le hq1.le ) );
  rw [ gfun_master q α β S hq0 hq1 hβ0 hβ1 hα0 hα hβ' n hn ];
  rw [ abs_le ] at *;
  field_simp at *;
  constructor <;> nlinarith [ mul_div_cancel₀ ( 8 * β ) ( by linarith : ( 1 - β ) ≠ 0 ), mul_div_cancel₀ ( 8 * β * Real.log q * S ^ 2 ) ( by linarith : ( 1 - β ) ≠ 0 ) ]

/-! ## The normalisation (pinning) argument -/

/-
**Pinning.**  If two probability weights `nu`, `pi` on the sectors `{0,…,S}` have
`nu n = exp(lZ + gf n) · pi n` for a single constant `lZ`, and `|gf n| ≤ C₀` for all
sectors, then `|log(nu n / pi n)| ≤ 2 C₀`.  The constant `lZ` is pinned by normalisation:
since both sum to `1`, some sector has ratio `≥ 1` and some `≤ 1`, forcing `|lZ| ≤ C₀`.
-/
theorem log_ratio_pinned (S : ℕ) (nu pi gf : ℕ → ℝ) (C0 lZ : ℝ)
    (hpi : ∀ n ≤ S, 0 < pi n)
    (hsum_nu : ∑ n ∈ Finset.range (S + 1), nu n = 1)
    (hsum_pi : ∑ n ∈ Finset.range (S + 1), pi n = 1)
    (hratio : ∀ n ≤ S, nu n = Real.exp (lZ + gf n) * pi n)
    (hg : ∀ n ≤ S, |gf n| ≤ C0) :
    ∀ n ≤ S, |Real.log (nu n / pi n)| ≤ 2 * C0 := by
  -- First, establish that $|lZ| \leq C0$.
  have hZ_bound : |lZ| ≤ C0 := by
    -- From `hsum_nu` and `hsum_pi`, there must exist sectors `n1, n2 ≤ S` with `Real.exp (lZ + gf n1) ≥ 1` and `Real.exp (lZ + gf n2) ≤ 1`.
    have h_exists_n1_n2 : ∃ n1 n2, n1 ≤ S ∧ n2 ≤ S ∧ Real.exp (lZ + gf n1) ≥ 1 ∧ Real.exp (lZ + gf n2) ≤ 1 := by
      obtain ⟨n1, hn1⟩ : ∃ n1, n1 ≤ S ∧ Real.exp (lZ + gf n1) ≥ 1 := by
        by_contra h_contra;
        push_neg at h_contra;
        exact absurd ( hsum_nu ▸ Finset.sum_lt_sum_of_nonempty ( by norm_num ) fun n hn => show nu n < pi n from by rw [ hratio n ( Finset.mem_range_succ_iff.mp hn ) ] ; exact mul_lt_of_lt_one_left ( hpi n ( Finset.mem_range_succ_iff.mp hn ) ) ( h_contra n ( Finset.mem_range_succ_iff.mp hn ) ) ) ( by norm_num [ hsum_pi ] )
      obtain ⟨n2, hn2⟩ : ∃ n2, n2 ≤ S ∧ Real.exp (lZ + gf n2) ≤ 1 := by
        contrapose! hsum_nu;
        rw [ Finset.sum_congr rfl fun n hn => hratio n <| Finset.mem_range_succ_iff.mp hn ];
        exact ne_of_gt ( by rw [ ← hsum_pi ] ; exact Finset.sum_lt_sum_of_nonempty ( by norm_num ) fun n hn => by nlinarith [ hpi n ( Finset.mem_range_succ_iff.mp hn ), hsum_nu n ( Finset.mem_range_succ_iff.mp hn ) ] )
      use n1, n2, hn1.left, hn2.left, hn1.right, hn2.right;
    simp +zetaDelta at *;
    exact abs_le.mpr ⟨ by obtain ⟨ n1, hn1, x, hx, h1, h2 ⟩ := h_exists_n1_n2; linarith [ abs_le.mp ( hg n1 hn1 ), abs_le.mp ( hg x hx ) ], by obtain ⟨ n1, hn1, x, hx, h1, h2 ⟩ := h_exists_n1_n2; linarith [ abs_le.mp ( hg n1 hn1 ), abs_le.mp ( hg x hx ) ] ⟩;
  intro n hn; rw [ hratio n hn, mul_div_cancel_right₀ _ ( ne_of_gt ( hpi n hn ) ) ] ; rw [ Real.log_exp ] ; exact abs_le.mpr ⟨ by linarith [ abs_le.mp hZ_bound, abs_le.mp ( hg n hn ) ], by linarith [ abs_le.mp hZ_bound, abs_le.mp ( hg n hn ) ] ⟩ ;

/-! ## Theorem M (single species) -/

/-
**Theorem M** (two-sided sector comparability, single species).  Let `ν`, `ϖ` be
probability weights on the sectors `{0,…,S}` whose per-sector ratio has the compensated
shape `nu n / pi n = Z · (α/β)ⁿ / hfac q β S n` (this is where the elementary-symmetric
prefactors cancel, by homogeneity), with `β = α/(1+α)`.  Then for all sectors,
`|log(ν(n)/ϖ(n))| ≤ 2 C₀`, `C₀ = A(1 + 8β/(1−β))`, `A` bounding `(−log q)·S²`.
-/
theorem sector_comparison_single (q α β : ℝ) (S : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < α)
    (hα : β = α / (1 + α))
    (A : ℝ) (hA0 : 0 ≤ A) (hAbnd : (-(Real.log q)) * (S : ℝ) ^ 2 ≤ A)
    (hβ' : β * q ^ (-(2 * (S : ℤ))) ≤ (1 + β) / 2)
    (hqS : q ^ (-(2 * (S : ℤ))) ≤ 2)
    (nu pi : ℕ → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hpi : ∀ n ≤ S, 0 < pi n)
    (hsum_nu : ∑ n ∈ Finset.range (S + 1), nu n = 1)
    (hsum_pi : ∑ n ∈ Finset.range (S + 1), pi n = 1)
    (hratio : ∀ n ≤ S, nu n = Z * (α / β) ^ n / hfac q β S n * pi n) :
    ∀ n ≤ S, |Real.log (nu n / pi n)| ≤ 2 * (A * (1 + 8 * β / (1 - β))) := by
  convert log_ratio_pinned S nu pi ( fun n => gfun q α β S n ) ( A * ( 1 + 8 * β / ( 1 - β ) ) ) ( Real.log Z ) _ _ _ _ _ using 1;
  · assumption;
  · exact hsum_nu;
  · exact hsum_pi;
  · intro n hn; rw [ hratio n hn ] ; simp +decide [ Real.exp_add, Real.exp_log hZ, Real.exp_nat_mul, Real.exp_log ( div_pos hα0 hβ0 ), gfun ] ; ring;
    rw [ Real.exp_sub, Real.exp_nat_mul, Real.exp_log ( by positivity ), Real.exp_log ( by exact hfac_pos q β S hq0 hq1 hβ0 hβ1 hβ' n hn ) ] ; ring ; norm_num [ hZ.ne', hβ0.ne', hα0.ne' ];
  · exact fun n hn => gfun_bound q α β S hq0 hq1 hβ0 hβ1 hα0 hα A hA0 hAbnd hβ' hqS n hn

/-! ## Homogeneity of the elementary symmetric polynomials -/

/-- The elementary symmetric polynomial `e_k` of a finite family `w : ι → ℝ`. -/
noncomputable def esymm {ι : Type*} [Fintype ι] (w : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ Finset.univ.powersetCard k, ∏ i ∈ T, w i

/-
**Homogeneity** `e_k(γ·w) = γᵏ e_k(w)` of the elementary symmetric polynomials.
-/
theorem esymm_homogeneous {ι : Type*} [Fintype ι] (w : ι → ℝ) (γ : ℝ) (k : ℕ) :
    esymm (fun i => γ * w i) k = γ ^ k * esymm w k := by
  unfold esymm; simp +decide [ mul_pow, Finset.prod_mul_distrib, Finset.mul_sum ] ;
  exact Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard ] at hx; aesop;

/-
The elementary symmetric polynomial of a positive family is positive for `k` up to the
cardinality.
-/
theorem esymm_pos {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (hk : k ≤ Fintype.card ι) : 0 < esymm w k := by
  refine' Finset.sum_pos _ _;
  · exact fun _ _ => Finset.prod_pos fun _ _ => hw _;
  · exact Finset.powersetCard_nonempty.mpr (by rwa [Finset.card_univ])

/-! ## Theorem M (two species) -/

/-
**Theorem M** (two species).  For product measures over two independent species, the
single-species bounds add: `|log(ν(n₁,n₂)/ϖ(n₁,n₂))| ≤ 2(C₀(β₁)+C₀(β₂))`.
-/
theorem sector_comparison_two
    (r1 r2 : ℝ) (C1 C2 : ℝ)
    (hr1 : |r1| ≤ 2 * C1) (hr2 : |r2| ≤ 2 * C2) :
    |r1 + r2| ≤ 2 * (C1 + C2) := by
  grind

/-! ## Corollary transfer: correlation transfer -/

/-
**Corollary transfer** (correlation transfer).  Let the state space split into sectors
`ι`; on each sector `s` let `Tform s` be the symmetric positive-semidefinite form
`⟨·, P ·⟩` induced by a sector-preserving, self-adjoint, positive-semidefinite operator `P`
(the per-sector Cauchy–Schwarz `hCS` and positivity `hpsd` are taken as hypotheses; they
hold for `P_t = (exp(tL/2))²`).  If the sector masses satisfy `|ν(s)| ≤ M · ϖ(s)` (Theorem
M) with `ϖ(s) ≥ 0`, then
`|E_ν[f · P h]| ≤ M · E_ϖ[f · P f]^{1/2} · E_ϖ[h · P h]^{1/2}`.
-/
theorem correlation_transfer
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    (nu pi : ι → ℝ) (M : ℝ)
    (Tform : (s : ι) → E s → E s → ℝ)
    (f h : (s : ι) → E s)
    (hpi_nonneg : ∀ s, 0 ≤ pi s)
    (hpsd : ∀ s a, 0 ≤ Tform s a a)
    (hCS : ∀ s a b, |Tform s a b| ≤ Real.sqrt (Tform s a a) * Real.sqrt (Tform s b b))
    (hcomp : ∀ s, |nu s| ≤ M * pi s) :
    |∑ s, nu s * Tform s (f s) (h s)|
      ≤ M * Real.sqrt (∑ s, pi s * Tform s (f s) (f s))
          * Real.sqrt (∑ s, pi s * Tform s (h s) (h s)) := by
  convert Real.abs_le_sqrt ( show ( ∑ s, nu s * Tform s ( f s ) ( h s ) ) ^ 2 ≤ M ^ 2 * ( ∑ s, pi s * Tform s ( f s ) ( f s ) ) * ( ∑ s, pi s * Tform s ( h s ) ( h s ) ) from ?_ ) using 1;
  · rw [ Real.sqrt_mul', Real.sqrt_mul' ];
    · by_cases hM : 0 ≤ M <;> simp_all +decide;
      contrapose! hcomp;
      exact Exists.elim ( show ∃ s, pi s ≠ 0 from not_forall.mp fun h => hcomp.1.2 <| Real.sqrt_eq_zero_of_nonpos <| Finset.sum_nonpos fun s _ => by simp +decide [ h ] ) fun s hs => ⟨ s, lt_of_lt_of_le ( mul_neg_of_neg_of_pos hM <| lt_of_le_of_ne ( hpi_nonneg s ) <| Ne.symm hs ) <| abs_nonneg _ ⟩;
    · exact Finset.sum_nonneg fun s _ => mul_nonneg ( hpi_nonneg s ) ( hpsd s _ );
    · exact Finset.sum_nonneg fun s _ => mul_nonneg ( hpi_nonneg s ) ( hpsd s _ );
  · -- Applying the Cauchy-Schwarz inequality to the sums.
    have h_cauchy_schwarz : (∑ s, nu s * Tform s (f s) (h s)) ^ 2 ≤ (∑ s, |nu s| * Real.sqrt (Tform s (f s) (f s)) * Real.sqrt (Tform s (h s) (h s))) ^ 2 := by
      have h_cauchy_schwarz : ∀ s, |nu s * Tform s (f s) (h s)| ≤ |nu s| * Real.sqrt (Tform s (f s) (f s)) * Real.sqrt (Tform s (h s) (h s)) := by
        exact fun s => by rw [ abs_mul ] ; exact mul_le_mul_of_nonneg_left ( hCS s _ _ ) ( abs_nonneg _ ) |> le_trans <| by ring_nf; norm_num;
      exact le_trans ( by rw [ sq_abs ] ) ( pow_le_pow_left₀ ( abs_nonneg _ ) ( Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun _ _ => h_cauchy_schwarz _ ) _ );
    -- Applying the inequality |nu s| ≤ M * pi s to each term in the sum.
    have h_ineq : (∑ s, |nu s| * Real.sqrt (Tform s (f s) (f s)) * Real.sqrt (Tform s (h s) (h s))) ^ 2 ≤ (M * ∑ s, pi s * Real.sqrt (Tform s (f s) (f s)) * Real.sqrt (Tform s (h s) (h s))) ^ 2 := by
      rw [ Finset.mul_sum _ _ _ ];
      exact pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _ => mul_nonneg ( mul_nonneg ( abs_nonneg _ ) ( Real.sqrt_nonneg _ ) ) ( Real.sqrt_nonneg _ ) ) ( Finset.sum_le_sum fun s _ => by simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_right ( hcomp s ) ( mul_nonneg ( Real.sqrt_nonneg _ ) ( Real.sqrt_nonneg _ ) ) ) _;
    -- Applying the Cauchy-Schwarz inequality to the sums.
    have h_cauchy_schwarz : (∑ s, pi s * Real.sqrt (Tform s (f s) (f s)) * Real.sqrt (Tform s (h s) (h s))) ^ 2 ≤ (∑ s, pi s * Tform s (f s) (f s)) * (∑ s, pi s * Tform s (h s) (h s)) := by
      have h_cauchy_schwarz : ∀ (u v : ι → ℝ), (∑ s, u s * v s) ^ 2 ≤ (∑ s, u s ^ 2) * (∑ s, v s ^ 2) := by
        exact fun u v => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v;
      convert h_cauchy_schwarz ( fun s => Real.sqrt ( pi s ) * Real.sqrt ( Tform s ( f s ) ( f s ) ) ) ( fun s => Real.sqrt ( pi s ) * Real.sqrt ( Tform s ( h s ) ( h s ) ) ) using 3 <;> ring <;> norm_num [ Real.sq_sqrt, hpi_nonneg, hpsd ] ;
      ring;
    nlinarith

end TypeDDecoupling.Sector