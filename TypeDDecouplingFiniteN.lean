import Mathlib
import TypeDDecoupling

/-!
# Finite-`n` (and general real `q^n`) type D ASEP rates and the every-`n` current decoupling

This file formalizes the finite-`n` content of *Fluctuations of the type D ASEP*
(`typeD_decoupling-draft-rev4.tex`, §1.1 and §3, briefed in `finiteN_brief.tex`).

The existing file `TypeDDecoupling.lean` already encodes the microscopic rate tally of
`prop:decouple`(a) using integer `zpow`s in `q` for a fixed `n : ℕ` (see
`TypeDDecoupling.current_decoupling`).  Here we adopt the **key design choice** of the
brief: work with two real parameters `q ∈ (0,1)` and `r > 0`, where `r` plays the role of
`q^n`.  Every rate is then a Laurent polynomial in `(q, r)`, so all identities are
`field_simp`/`ring`-provable, the paper's analytic continuation in `q^n` (`rem:range`) is
automatic, and the natural-number case is the specialization `r = q^n`
(`betaR_eq_betaN`, `sigmaR_eq_sigmaN`, `rate1R_10_specialize`, …).

We prove, sorry-free:

* **(a)** the eight per-background tally identities behind the *every-`n`* statement of
  `prop:decouple`: the species-1 rightward transfer rate equals `r⁻² + r²q⁻² = q⁻¹βₙ` in
  every species-2 background, and the leftward rate equals `q²r⁻² + r² = qβₙ` in every
  background — hence the finite-`n` current decoupling (`current_decoupling_finiteN`);
* **(b)** the exact `q^{2n}=r²`-rescaled decompositions "rescaled rate = `n=∞` limit value
  `+ r²·`explicit correction" for all ten microscopic bond rates (hop/pair/swap/merge/split),
  the trivial `r → 0` limits recovering the `n=∞` table `eq:rates`, and a consistency lemma
  tying the constant terms to those `n=∞` rate values;
* **(c)** nonnegativity of all rates for `0 < r ≤ q < 1` (i.e. `n ≥ 1`) and the continuation
  threshold of `rem:range` at which the left merge/split rates vanish.

These results upgrade the Lean coverage of `prop:decouple` from `n=∞` to **every `n`** (and
real `q^n`), machine-checking the paper's "verified by computer algebra on the `16×16`
generator" claims (§1.1, §3).
-/

namespace TypeDDecouplingFiniteN

open scoped Topology
open Filter

/-! ## Parametrization: `βₙ` and `σₙ` as Laurent polynomials in `(q, r)` -/

/-- `βₙ = q^{1-2n} + q^{2n-1} = q/r² + r²/q` with `r = q^n` (symmetric jump factor). -/
noncomputable def betaR (q r : ℝ) : ℝ := q / r ^ 2 + r ^ 2 / q

/-- `σₙ = (q^{n-1} - q^{1-n})² = (r/q - q/r)²` with `r = q^n`. -/
noncomputable def sigmaR (q r : ℝ) : ℝ := (r / q - q / r) ^ 2

/-! ### Specialization to `r = q^n`: agreement with `TypeDDecoupling.betaN`/`sigmaN` -/

/-- With `r = q^n`, `betaR` agrees with the `zpow` definition `TypeDDecoupling.betaN`. -/
lemma betaR_eq_betaN (q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    betaR q (q ^ n) = TypeDDecoupling.betaN q n := by
  unfold betaR TypeDDecoupling.betaN
  have key : ((q : ℝ) ^ n) ^ 2 = q ^ (2 * (n : ℤ)) := by
    rw [← zpow_natCast (q ^ n) 2, ← zpow_natCast q n, ← zpow_mul]; norm_num [mul_comm]
  rw [key, zpow_sub₀ hq, zpow_sub₀ hq]
  have hqz : q ^ (2 * (n : ℤ)) ≠ 0 := zpow_ne_zero _ hq
  field_simp

/-- With `r = q^n`, `sigmaR` agrees with the `zpow` definition `TypeDDecoupling.sigmaN`. -/
lemma sigmaR_eq_sigmaN (q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    sigmaR q (q ^ n) = TypeDDecoupling.sigmaN q n := by
  unfold sigmaR TypeDDecoupling.sigmaN
  have key : ((q : ℝ) ^ n) = q ^ ((n : ℤ)) := (zpow_natCast q n).symm
  rw [key, zpow_sub₀ hq, zpow_sub₀ hq]
  field_simp

/-! ## (a) The eight per-background tally rates

Species-1 rightward rate across a bond, case by case in the species-2 background; each
sums to `q⁻¹βₙ = r⁻² + r²q⁻²`.  Species-1 leftward; each sums to `qβₙ = q²r⁻² + r²`.
(Species 2 is symmetric under swapping the two species, the rates being species-symmetric.)
-/

/-- Species-1 rightward rate, species-2 background `(1,0)`: `q⁻¹βₙ`. -/
noncomputable def rate1R_10 (q r : ℝ) : ℝ := betaR q r / q

/-- Species-1 rightward rate, species-2 background `(3,0)`:
`q⁻²σₙ + (q^{2n-2} - q^{2n-4} + 2q⁻²)`. -/
noncomputable def rate1R_30 (q r : ℝ) : ℝ :=
  sigmaR q r / q ^ 2 + (r ^ 2 / q ^ 2 - r ^ 2 / q ^ 4 + 2 / q ^ 2)

/-- Species-1 rightward rate, species-2 background `(1,2)`: `(2 + q^{-2n}(1-q²)) + σₙ`. -/
noncomputable def rate1R_12 (q r : ℝ) : ℝ :=
  (2 + (1 - q ^ 2) / r ^ 2) + sigmaR q r

/-- Species-1 rightward rate, species-2 background `(3,2)`: `q⁻¹βₙ`. -/
noncomputable def rate1R_32 (q r : ℝ) : ℝ := betaR q r / q

/-- Species-1 leftward rate, species-2 background `(0,1)`: `qβₙ`. -/
noncomputable def rate1L_01 (q r : ℝ) : ℝ := q * betaR q r

/-- Species-1 leftward rate, species-2 background `(0,3)`:
`q²σₙ + (2q² + q^{2-2n} - q^{4-2n})`. -/
noncomputable def rate1L_03 (q r : ℝ) : ℝ :=
  q ^ 2 * sigmaR q r + (2 * q ^ 2 + q ^ 2 / r ^ 2 - q ^ 4 / r ^ 2)

/-- Species-1 leftward rate, species-2 background `(2,1)`: `σₙ + (2 - q^{2n-2}(1-q²))`. -/
noncomputable def rate1L_21 (q r : ℝ) : ℝ :=
  sigmaR q r + (2 - r ^ 2 * (1 - q ^ 2) / q ^ 2)

/-- Species-1 leftward rate, species-2 background `(2,3)`: `qβₙ`. -/
noncomputable def rate1L_23 (q r : ℝ) : ℝ := q * betaR q r

/-! ### The eight tally identities (each `ring`-provable in `(q, r)`) -/

/-- `(1,0)` rightward tally: `q⁻¹βₙ = r⁻² + r²q⁻²`. -/
lemma rate1R_10_tally (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    rate1R_10 q r = 1 / r ^ 2 + r ^ 2 / q ^ 2 := by
  unfold rate1R_10 betaR; field_simp

/-- `(3,0)` rightward tally: `q⁻²σₙ + (q^{2n-2}-q^{2n-4}+2q⁻²) = r⁻² + r²q⁻²`. -/
lemma rate1R_30_tally (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    rate1R_30 q r = 1 / r ^ 2 + r ^ 2 / q ^ 2 := by
  unfold rate1R_30 sigmaR; field_simp; ring

/-- `(1,2)` rightward tally: `(2 + q^{-2n}(1-q²)) + σₙ = r⁻² + r²q⁻²`. -/
lemma rate1R_12_tally (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    rate1R_12 q r = 1 / r ^ 2 + r ^ 2 / q ^ 2 := by
  unfold rate1R_12 sigmaR; field_simp; ring

/-- `(3,2)` rightward tally: `q⁻¹βₙ = r⁻² + r²q⁻²`. -/
lemma rate1R_32_tally (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    rate1R_32 q r = 1 / r ^ 2 + r ^ 2 / q ^ 2 := by
  unfold rate1R_32 betaR; field_simp

/-- `(0,1)` leftward tally: `qβₙ = q²r⁻² + r²`. -/
lemma rate1L_01_tally (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    rate1L_01 q r = q ^ 2 / r ^ 2 + r ^ 2 := by
  unfold rate1L_01 betaR; field_simp

/-- `(0,3)` leftward tally: `q²σₙ + (2q²+q^{2-2n}-q^{4-2n}) = q²r⁻² + r²`. -/
lemma rate1L_03_tally (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    rate1L_03 q r = q ^ 2 / r ^ 2 + r ^ 2 := by
  unfold rate1L_03 sigmaR; field_simp; ring

/-- `(2,1)` leftward tally: `σₙ + (2 - q^{2n-2}(1-q²)) = q²r⁻² + r²`. -/
lemma rate1L_21_tally (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    rate1L_21 q r = q ^ 2 / r ^ 2 + r ^ 2 := by
  unfold rate1L_21 sigmaR; field_simp; ring

/-- `(2,3)` leftward tally: `qβₙ = q²r⁻² + r²`. -/
lemma rate1L_23_tally (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    rate1L_23 q r = q ^ 2 / r ^ 2 + r ^ 2 := by
  unfold rate1L_23 betaR; field_simp

/-- **Every-`n` current decoupling, `prop:decouple`(a) (real `q^n` form).**  For every
`q ≠ 0` and `r ≠ 0` (in particular `r = q^n` for any `n`, and any analytic continuation of
`q^n`), the species-1 rightward transfer rate is the single value `q⁻¹βₙ = r⁻² + r²q⁻²` in
*every* species-2 background `(1,0),(3,0),(1,2),(3,2)`, and the leftward rate is the single
value `qβₙ = q²r⁻² + r²` in every background `(0,1),(0,3),(2,1),(2,3)`.  Hence the species-1
current is the autonomous single-species ASEP current with `r_R = q⁻¹βₙ`, `r_L = qβₙ`,
independent of the species-2 occupancy. -/
theorem current_decoupling_finiteN (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    (rate1R_10 q r = 1 / r ^ 2 + r ^ 2 / q ^ 2 ∧ rate1R_30 q r = 1 / r ^ 2 + r ^ 2 / q ^ 2 ∧
        rate1R_12 q r = 1 / r ^ 2 + r ^ 2 / q ^ 2 ∧
        rate1R_32 q r = 1 / r ^ 2 + r ^ 2 / q ^ 2) ∧
      (rate1L_01 q r = q ^ 2 / r ^ 2 + r ^ 2 ∧ rate1L_03 q r = q ^ 2 / r ^ 2 + r ^ 2 ∧
        rate1L_21 q r = q ^ 2 / r ^ 2 + r ^ 2 ∧ rate1L_23 q r = q ^ 2 / r ^ 2 + r ^ 2) :=
  ⟨⟨rate1R_10_tally q r hq hr, rate1R_30_tally q r hq hr, rate1R_12_tally q r hq hr,
      rate1R_32_tally q r hq hr⟩,
    rate1L_01_tally q r hq hr, rate1L_03_tally q r hq hr, rate1L_21_tally q r hq hr,
      rate1L_23_tally q r hq hr⟩

/-- All four rightward background rates agree (single autonomous rightward rate). -/
theorem rate1R_decoupled (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    rate1R_10 q r = rate1R_30 q r ∧ rate1R_30 q r = rate1R_12 q r ∧
      rate1R_12 q r = rate1R_32 q r := by
  rw [rate1R_10_tally q r hq hr, rate1R_30_tally q r hq hr, rate1R_12_tally q r hq hr,
    rate1R_32_tally q r hq hr]
  exact ⟨rfl, rfl, rfl⟩

/-- All four leftward background rates agree (single autonomous leftward rate). -/
theorem rate1L_decoupled (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    rate1L_01 q r = rate1L_03 q r ∧ rate1L_03 q r = rate1L_21 q r ∧
      rate1L_21 q r = rate1L_23 q r := by
  rw [rate1L_01_tally q r hq hr, rate1L_03_tally q r hq hr, rate1L_21_tally q r hq hr,
    rate1L_23_tally q r hq hr]
  exact ⟨rfl, rfl, rfl⟩

/-- **`thm:marg` input: the `n`-free rate ratio.**  The rightward/leftward rate ratio is
`q⁻²`, independent of `n` (and `r`).  This is the only rate datum the every-`n`
marginal statement `thm:marg` consumes beyond the time change `βₙ`. -/
theorem rate_ratio_nfree (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    rate1R_10 q r / rate1L_01 q r = q ^ (-2 : ℤ) := by
  rw [rate1R_10_tally q r hq hr, rate1L_01_tally q r hq hr, zpow_neg, zpow_two,
    div_eq_iff (by positivity)]
  field_simp

/-! ## (b) The `q^{2n}=r²`-rescaled microscopic bond rates and the `n → ∞` limit

Multiplying each of the ten microscopic bond rates by `q^{2n}=r²` gives polynomials in `r²`
whose constant terms are the `n=∞` rates of `eq:rates` (with `ε = 1-q²`).  We first record
the `n=∞` limit values, then the unscaled finite-`n` rates, then the exact decompositions
"`r²·`rate = limit value `+ r²·`explicit correction", then the trivial `r → 0` limits, and
finally a consistency lemma.
-/

/-- The `n=∞` limiting rates of `eq:rates` (with `ε = 1-q²`), as encoded implicitly in
`TypeDDecoupling.lean`: hop right/left `1, q²`; pair right/left `1, q⁴`; swap `q²`;
right merge/split `ε, q²ε`; left merge/split `0, 0`. -/
noncomputable def hopRInf (_q : ℝ) : ℝ := 1
noncomputable def hopLInf (q : ℝ) : ℝ := q ^ 2
noncomputable def pairRInf (_q : ℝ) : ℝ := 1
noncomputable def pairLInf (q : ℝ) : ℝ := q ^ 4
noncomputable def swapInf (q : ℝ) : ℝ := q ^ 2
noncomputable def mergeRInf (q : ℝ) : ℝ := 1 - q ^ 2
noncomputable def splitRInf (q : ℝ) : ℝ := q ^ 2 * (1 - q ^ 2)
noncomputable def mergeLInf (_q : ℝ) : ℝ := 0
noncomputable def splitLInf (_q : ℝ) : ℝ := 0

/-- Unscaled finite-`n` hop-right rate `q⁻¹βₙ`. -/
noncomputable def hopR (q r : ℝ) : ℝ := betaR q r / q
/-- Unscaled finite-`n` hop-left rate `qβₙ`. -/
noncomputable def hopL (q r : ℝ) : ℝ := q * betaR q r
/-- Unscaled finite-`n` pair-right rate `q⁻²σₙ`. -/
noncomputable def pairR (q r : ℝ) : ℝ := sigmaR q r / q ^ 2
/-- Unscaled finite-`n` pair-left rate `q²σₙ`. -/
noncomputable def pairL (q r : ℝ) : ℝ := q ^ 2 * sigmaR q r
/-- Unscaled finite-`n` swap rate `σₙ`. -/
noncomputable def swapRate (q r : ℝ) : ℝ := sigmaR q r
/-- Unscaled finite-`n` right-merge rate `2 + q^{-2n}(1-q²)`. -/
noncomputable def mergeR (q r : ℝ) : ℝ := 2 + (1 - q ^ 2) / r ^ 2
/-- Unscaled finite-`n` right-split rate `q²(1-q²)q^{-2n} + 2q²`. -/
noncomputable def splitR (q r : ℝ) : ℝ := q ^ 2 * (1 - q ^ 2) / r ^ 2 + 2 * q ^ 2
/-- Unscaled finite-`n` left-merge rate `2 - q^{2n-2}(1-q²)`. -/
noncomputable def mergeL (q r : ℝ) : ℝ := 2 - r ^ 2 * (1 - q ^ 2) / q ^ 2
/-- Unscaled finite-`n` left-split rate `2q⁻² - q^{2n-4}(1-q²)`. -/
noncomputable def splitL (q r : ℝ) : ℝ := 2 / q ^ 2 - r ^ 2 * (1 - q ^ 2) / q ^ 4

/-- Rescaled hop right: `r²·q⁻¹βₙ = 1 + r²·(r²q⁻²)`. -/
lemma hopR_rescaled (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    r ^ 2 * hopR q r = hopRInf q + r ^ 2 * (r ^ 2 / q ^ 2) := by
  unfold hopR betaR hopRInf; field_simp

/-- Rescaled hop left: `r²·qβₙ = q² + r²·(r²)`. -/
lemma hopL_rescaled (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    r ^ 2 * hopL q r = hopLInf q + r ^ 2 * r ^ 2 := by
  unfold hopL betaR hopLInf; field_simp

/-- Rescaled pair right: `r²·q⁻²σₙ = 1 + r²·(-2q⁻² + r²q⁻⁴)`. -/
lemma pairR_rescaled (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    r ^ 2 * pairR q r = pairRInf q + r ^ 2 * (-2 / q ^ 2 + r ^ 2 / q ^ 4) := by
  unfold pairR sigmaR pairRInf; field_simp; ring

/-- Rescaled pair left: `r²·q²σₙ = q⁴ + r²·(-2q² + r²)`. -/
lemma pairL_rescaled (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    r ^ 2 * pairL q r = pairLInf q + r ^ 2 * (-2 * q ^ 2 + r ^ 2) := by
  unfold pairL sigmaR pairLInf; field_simp; ring

/-- Rescaled swap: `r²·σₙ = q² + r²·(-2 + r²q⁻²)`. -/
lemma swap_rescaled (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    r ^ 2 * swapRate q r = swapInf q + r ^ 2 * (-2 + r ^ 2 / q ^ 2) := by
  unfold swapRate sigmaR swapInf; field_simp; ring

/-- Rescaled right merge: `r²·(2 + q^{-2n}(1-q²)) = ε + r²·2`. -/
lemma mergeR_rescaled (q r : ℝ) (hr : r ≠ 0) :
    r ^ 2 * mergeR q r = mergeRInf q + r ^ 2 * 2 := by
  unfold mergeR mergeRInf; field_simp; ring

/-- Rescaled right split: `r²·splitR = q²ε + r²·(2q²)`. -/
lemma splitR_rescaled (q r : ℝ) (hq : q ≠ 0) (hr : r ≠ 0) :
    r ^ 2 * splitR q r = splitRInf q + r ^ 2 * (2 * q ^ 2) := by
  unfold splitR splitRInf; field_simp

/-- Rescaled left merge: `r²·(2 - q^{2n-2}(1-q²)) = 0 + r²·(2 - r²q⁻²ε)`. -/
lemma mergeL_rescaled (q r : ℝ) (hq : q ≠ 0) :
    r ^ 2 * mergeL q r = mergeLInf q + r ^ 2 * (2 - r ^ 2 * (1 - q ^ 2) / q ^ 2) := by
  unfold mergeL mergeLInf; field_simp; ring

/-- Rescaled left split: `r²·splitL = 0 + r²·(2q⁻² - r²q⁻⁴ε)`. -/
lemma splitL_rescaled (q r : ℝ) (hq : q ≠ 0) :
    r ^ 2 * splitL q r = splitLInf q + r ^ 2 * (2 / q ^ 2 - r ^ 2 * (1 - q ^ 2) / q ^ 4) := by
  unfold splitL splitLInf; field_simp; ring

/-! ### The trivial `r → 0` limits: each rescaled rate tends to its `n=∞` value -/

/-- `r → 0` limit of the rescaled hop-right rate is the `n=∞` value `1`. -/
lemma hopR_rescaled_tendsto (q : ℝ) (hq : q ≠ 0) :
    Tendsto (fun r => r ^ 2 * hopR q r) (𝓝[≠] 0) (𝓝 (hopRInf q)) := by
  have h : Set.EqOn (fun r => r ^ 2 * hopR q r)
      (fun r => hopRInf q + r ^ 2 * (r ^ 2 / q ^ 2)) ({0}ᶜ : Set ℝ) :=
    fun r hr => hopR_rescaled q r hq hr
  refine Tendsto.congr' (eventuallyEq_nhdsWithin_of_eqOn h).symm ?_
  have hc : Continuous (fun r : ℝ => hopRInf q + r ^ 2 * (r ^ 2 / q ^ 2)) := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- `r → 0` limit of the rescaled left-merge rate is the `n=∞` value `0`. -/
lemma mergeL_rescaled_tendsto (q : ℝ) (hq : q ≠ 0) :
    Tendsto (fun r => r ^ 2 * mergeL q r) (𝓝[≠] 0) (𝓝 (mergeLInf q)) := by
  have h : Set.EqOn (fun r => r ^ 2 * mergeL q r)
      (fun r => mergeLInf q + r ^ 2 * (2 - r ^ 2 * (1 - q ^ 2) / q ^ 2)) ({0}ᶜ : Set ℝ) :=
    fun r _ => mergeL_rescaled q r hq
  refine Tendsto.congr' (eventuallyEq_nhdsWithin_of_eqOn h).symm ?_
  have hc : Continuous
      (fun r : ℝ => mergeLInf q + r ^ 2 * (2 - r ^ 2 * (1 - q ^ 2) / q ^ 2)) := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-! ### Consistency: the constant terms are the `n=∞` rate values

Each decomposition above has the shape `r²·rate = (n=∞ value) + r²·correction`; the constant
(`r`-free) term is exactly the `n=∞` limit value.  We record the explicit values, and tie the
right-split constant to the split rate `TypeDDecoupling.splitRate` used in the
Edwards–Wilkinson analysis (`prop:twophase`/`lem:split`). -/

/-- The `n=∞` rate values (constant terms of the rescaled decompositions) collected. -/
lemma nInf_values (q : ℝ) :
    hopRInf q = 1 ∧ hopLInf q = q ^ 2 ∧ pairRInf q = 1 ∧ pairLInf q = q ^ 4 ∧
      swapInf q = q ^ 2 ∧ mergeRInf q = 1 - q ^ 2 ∧ splitRInf q = q ^ 2 * (1 - q ^ 2) ∧
      mergeLInf q = 0 ∧ splitLInf q = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Consistency with `TypeDDecoupling.splitRate`: the `n=∞` right-split rate `q²ε` is exactly
half the Edwards–Wilkinson split rate `ν_sp = 2q²ε` of `lem:split`, under `q = 1 - c/T`. -/
lemma splitRInf_eq_half_splitRate (c T : ℝ) :
    splitRInf (1 - c / T) = TypeDDecoupling.splitRate c T / 2 := by
  unfold splitRInf TypeDDecoupling.splitRate; ring

/-! ## (c) Nonnegativity of all rates for `0 < r ≤ q < 1` (i.e. `n ≥ 1`) -/

section Nonneg

variable {q r : ℝ}

lemma hopR_nonneg (hq0 : 0 < q) (hr0 : 0 < r) : 0 ≤ hopR q r := by
  unfold hopR betaR; positivity

lemma hopL_nonneg (hq0 : 0 < q) (hr0 : 0 < r) : 0 ≤ hopL q r := by
  unfold hopL betaR; positivity

lemma pairR_nonneg (hq0 : 0 < q) : 0 ≤ pairR q r := by
  unfold pairR sigmaR; positivity

lemma pairL_nonneg (hq0 : 0 < q) : 0 ≤ pairL q r := by
  unfold pairL sigmaR; positivity

lemma swap_nonneg : 0 ≤ swapRate q r := by
  unfold swapRate sigmaR; positivity

lemma mergeR_nonneg (hq0 : 0 < q) (hq1 : q < 1) (hr0 : 0 < r) : 0 ≤ mergeR q r := by
  unfold mergeR
  have h1 : (0:ℝ) < 1 - q ^ 2 := by nlinarith
  positivity

lemma splitR_nonneg (hq0 : 0 < q) (hq1 : q < 1) (hr0 : 0 < r) : 0 ≤ splitR q r := by
  unfold splitR
  have h1 : (0:ℝ) < 1 - q ^ 2 := by nlinarith
  positivity

/-- The only nontrivial nonnegativity: the left-merge rate `2 - r²q⁻²(1-q²) ≥ 0` for
`0 < r ≤ q < 1` (here `r ≤ q` gives `r²q⁻² ≤ 1` and `1-q² < 2`). -/
lemma mergeL_nonneg (hq0 : 0 < q) (hq1 : q < 1) (hr0 : 0 < r) (hrq : r ≤ q) :
    0 ≤ mergeL q r := by
  unfold mergeL
  have hq2 : (0:ℝ) < q ^ 2 := by positivity
  rw [sub_nonneg, div_le_iff₀ hq2]
  nlinarith [sq_nonneg (q - r), sq_nonneg q, mul_pos hr0 hr0]

/-- Nonnegativity of the left-split rate for `0 < r ≤ q < 1`. -/
lemma splitL_nonneg (hq0 : 0 < q) (hq1 : q < 1) (hr0 : 0 < r) (hrq : r ≤ q) :
    0 ≤ splitL q r := by
  unfold splitL
  have hq2 : (0:ℝ) < q ^ 2 := by positivity
  have hq4 : (0:ℝ) < q ^ 4 := by positivity
  have hr2 : r ^ 2 ≤ q ^ 2 := by nlinarith
  have h1 : (0:ℝ) ≤ 1 - q ^ 2 := by nlinarith
  rw [sub_nonneg, div_le_div_iff₀ hq4 hq2]
  nlinarith [mul_nonneg h1 hq2.le,
    mul_le_mul_of_nonneg_right hr2 (mul_nonneg h1 hq2.le)]

end Nonneg

/-! ### The continuation threshold of `rem:range`

The left merge and left split rates vanish simultaneously, precisely when
`r²q⁻²(1-q²) = 2` — the boundary of the analytic-continuation range in `q^n` of `rem:range`.
-/

/-- The left-merge rate vanishes iff `r²q⁻²(1-q²) = 2`. -/
lemma mergeL_eq_zero_iff (q r : ℝ) :
    mergeL q r = 0 ↔ r ^ 2 * (1 - q ^ 2) / q ^ 2 = 2 := by
  unfold mergeL; constructor <;> intro h <;> linarith

/-- The left-split rate vanishes iff `r²q⁻²(1-q²) = 2` — the same threshold as the
left-merge rate. -/
lemma splitL_eq_zero_iff (q r : ℝ) (hq : q ≠ 0) :
    splitL q r = 0 ↔ r ^ 2 * (1 - q ^ 2) / q ^ 2 = 2 := by
  unfold splitL
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero _ hq
  have hq4 : q ^ 4 ≠ 0 := pow_ne_zero _ hq
  rw [sub_eq_zero]
  constructor <;> intro h
  · field_simp at h ⊢; nlinarith [h]
  · field_simp at h ⊢; nlinarith [h]

/-- The left-merge and left-split rates vanish together (same continuation threshold). -/
lemma mergeL_zero_iff_splitL_zero (q r : ℝ) (hq : q ≠ 0) :
    mergeL q r = 0 ↔ splitL q r = 0 := by
  rw [mergeL_eq_zero_iff q r, splitL_eq_zero_iff q r hq]

/-! ### Specialization of the tallies to `r = q^n` (agreement with `TypeDDecoupling`) -/

/-- With `r = q^n`, the `(1,0)` rate agrees with `TypeDDecoupling.rate1R_10`. -/
lemma rate1R_10_specialize (q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    rate1R_10 q (q ^ n) = TypeDDecoupling.rate1R_10 q n := by
  unfold rate1R_10 TypeDDecoupling.rate1R_10
  rw [betaR_eq_betaN q hq n, zpow_neg, zpow_one]
  field_simp

end TypeDDecouplingFiniteN
