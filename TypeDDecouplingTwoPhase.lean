import Mathlib
import TypeDDecouplingMartingaleCLT

/-!
# The abstract two-phase mixture CLT (the array core of `prop:twophase`)

This file proves the **abstract two-phase central limit theorem** whose model
instantiation is `TypeDDecoupling.prop_twophase` in `TypeDDecouplingCrossover.lean`.
It builds on `TypeDDecouplingMartingaleCLT.lean`, reusing
`TypeDDecoupling.MartingaleCLT.core_charFun_tendsto` (the McLeish martingale
difference array characteristic-function core); their proofs are **not** duplicated.

## Setting

For each `n`: a filtration `(𝓕 n j)_j`, a pair of square-integrable arrays
`(X n j, Y n j)` adapted with the martingale difference property
`E[X n j | 𝓕 n j] = E[Y n j | 𝓕 n j] = 0`, jumps deterministically bounded by
`b n → 0`, and a change point `m n ∈ {0,…,k n}`.

* **Phase 1 (locked):** for `j < m n`, `X n j = Y n j` (the two components receive
  identical increments — the bound pair moving as one particle before the split).
* **Phase 2 (decoupled):** for `j ≥ m n`, the brackets are diagonal in the limit.

## Results

* `psiForm` — the limiting quadratic form `ψ_u(a,c) = (a+c)² u + (a²+c²)(1-u)`.
* `twophase_charFun_tendsto` (**Tier 1**) — for a fixed change-point fraction
  `m n / k n → u` (via the four bracket limits), the joint characteristic function
  of `(∑ X, ∑ Y)` converges to `exp(-½ ψ_u(a,c))`, the characteristic function of the
  standard bivariate normal of correlation `u`.  Proved by Cramér–Wold through
  `core_charFun_tendsto`.
* `twophase_charFun_tendsto_indep` (`u = 0`) and `twophase_charFun_tendsto_locked`
  (`u = 1`) — the two edge cases.
* `mixture_charFun_tendsto` (**Tier 2**) — the elementary mixture lemma (tower
  property + dominated convergence): if the conditional characteristic function
  matches `exp(-½ ψ_{U n}(a,c))` a.e. and `U n → U` a.e., then the unconditional
  characteristic function converges to the `U`-mixture `E[exp(-½ ψ_U(a,c))]`.
* `expMin_mean` (**Tier 2**) — the closed form
  `E[min(Exp(λ),1)] = (1 - e^{-λ})/λ`, i.e.
  `∫₀^∞ min(t,1)·λ·e^{-λt} dt = (1 - e^{-λ})/λ`.  Specialized at `λ = 4c` this is
  `TypeDDecoupling.expMin_mean_eq_rhoCorr`, the mixture correlation of `thm:closed`.
* `twophase_mixture_charFun_tendsto` (**Tier 3**) — the assembled random-changepoint
  statement, packaging the conditional Tier-1 applicability as one named hypothesis
  and concluding the mixture characteristic-function limit via Tier 2.

The whole development uses only the standard axioms.
-/

open MeasureTheory ProbabilityTheory Complex Filter Finset
open scoped Topology BigOperators ENNReal NNReal Real

namespace TypeDDecoupling.TwoPhase

open TypeDDecoupling.MartingaleCLT

/-- The limiting quadratic form of the two-phase CLT:
`ψ_u(a,c) = (a+c)² u + (a²+c²)(1-u)`.  It is the covariance form of the standard
bivariate normal of correlation `u`, i.e. of
`(√u ξ₀ + √(1-u) ξ₁, √u ξ₀ + √(1-u) ξ₂)` with `ξ₀,ξ₁,ξ₂` i.i.d. `N(0,1)`. -/
noncomputable def psiForm (u a c : ℝ) : ℝ := (a + c) ^ 2 * u + (a ^ 2 + c ^ 2) * (1 - u)

@[simp] lemma psiForm_zero (a c : ℝ) : psiForm 0 a c = a ^ 2 + c ^ 2 := by
  simp [psiForm]

@[simp] lemma psiForm_one (a c : ℝ) : psiForm 1 a c = (a + c) ^ 2 := by
  simp [psiForm]

/-- `ψ_u(a,c) ≥ 0` for `u ∈ [0,1]`: it is a convex combination of the nonnegative
numbers `(a+c)²` and `a²+c²`. -/
lemma psiForm_nonneg {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (a c : ℝ) :
    0 ≤ psiForm u a c := by
  obtain ⟨h0, h1⟩ := hu
  have : 0 ≤ 1 - u := by linarith
  have h1 : 0 ≤ (a + c) ^ 2 * u := mul_nonneg (sq_nonneg _) h0
  have h2 : 0 ≤ (a ^ 2 + c ^ 2) * (1 - u) := mul_nonneg (by positivity) this
  simpa [psiForm] using add_nonneg h1 h2

/-- `u ↦ ψ_u(a,c)` is continuous. -/
lemma continuous_psiForm (a c : ℝ) : Continuous (fun u => psiForm u a c) := by
  unfold psiForm; fun_prop

section Tier1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Tier 1 — the two-phase CLT at a deterministic change-point fraction.**

Fix `u` and a change point `m n ≤ k n`.  Assume the martingale-difference-array
structure for both `X` and `Y` (adapted, mean zero given the past, jumps bounded by
`b n → 0`, uniformly bounded brackets), the **locking** `X n j = Y n j` for `j < m n`,
and the four bracket limits (a.e.):
`∑_{j<m n} (X n j)² → u`, `∑_{m n ≤ j < k n} (X n j)² → 1-u`,
`∑_{m n ≤ j < k n} (Y n j)² → 1-u`, `∑_{m n ≤ j < k n} (X n j)(Y n j) → 0`.

Then for all `a, c`, with `S n = ∑ X n`, `R n = ∑ Y n`,
`E[exp(i(a S n + c R n))] → exp(-½ ψ_u(a,c))`,
the characteristic function of the standard bivariate normal of correlation `u`.

**Route.**  Cramér–Wold: for fixed `(a,c)` the array `Z n j := a·X n j + c·Y n j`
is a martingale difference array with jumps `≤ (|a|+|c|) b n → 0` and bracket
`(a+c)² ∑_{j<m n}(X n j)² + a² ∑_{≥}(X n j)² + 2ac ∑_{≥}(X n j)(Y n j) + c² ∑_{≥}(Y n j)²
→ ψ_u(a,c)` (using `X = Y` on phase 1); then `core_charFun_tendsto` at `σ² = ψ_u(a,c)`,
evaluated at frequency `1`.

The hypothesis `hu : u ∈ [0,1]` is included per the brief; the characteristic-function
limit itself does not require it. -/
theorem twophase_charFun_tendsto
    (kn : ℕ → ℕ) (mn : ℕ → ℕ) (𝓕 : ℕ → ℕ → MeasurableSpace Ω)
    (X Y : ℕ → ℕ → Ω → ℝ) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (b : ℕ → ℝ) (C : ℝ)
    (hmn : ∀ n, mn n ≤ kn n)
    (hmono : ∀ n, Monotone (𝓕 n)) (hle : ∀ n k, 𝓕 n k ≤ mΩ)
    (hadaptX : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (X n j))
    (hadaptY : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (Y n j))
    (hmdsX : ∀ n j, μ[X n j | 𝓕 n j] =ᵐ[μ] 0)
    (hmdsY : ∀ n j, μ[Y n j | 𝓕 n j] =ᵐ[μ] 0)
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hboundX : ∀ n j ω, |X n j ω| ≤ b n) (hboundY : ∀ n j ω, |Y n j ω| ≤ b n)
    (hCbrX : ∀ n ω, ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2 ≤ C)
    (hCbrY : ∀ n ω, ∑ j ∈ Finset.range (kn n), (Y n j ω) ^ 2 ≤ C)
    (hlock : ∀ n j ω, j < mn n → X n j ω = Y n j ω)
    (hbr1 : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (mn n), (X n j ω) ^ 2) atTop (𝓝 u))
    (hbr2X : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.Ico (mn n) (kn n), (X n j ω) ^ 2) atTop (𝓝 (1 - u)))
    (hbr2Y : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.Ico (mn n) (kn n), (Y n j ω) ^ 2) atTop (𝓝 (1 - u)))
    (hbr2XY : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.Ico (mn n) (kn n), (X n j ω) * (Y n j ω)) atTop (𝓝 0)) :
    ∀ a c : ℝ, Tendsto
      (fun n => ∫ ω, Complex.exp (((a * partialSum (X n) (kn n) ω
          + c * partialSum (Y n) (kn n) ω : ℝ) : ℂ) * Complex.I) ∂μ)
      atTop (𝓝 (Complex.exp (((-psiForm u a c / 2 : ℝ) : ℂ)))) := by
  intro a c
  set Z : ℕ → ℕ → Ω → ℝ := fun n j ω => a * X n j ω + c * Y n j ω
  have hZ : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (Z n j) :=
    fun n j => StronglyMeasurable.add (StronglyMeasurable.const_mul (hadaptX n j) _)
      (StronglyMeasurable.const_mul (hadaptY n j) _)
  have hZmds : ∀ n j, μ[Z n j | 𝓕 n j] =ᵐ[μ] 0 := by
    intro n j
    convert condExp_linear_comb_eq_zero a c _ _ (hmdsX n j) (hmdsY n j) using 1
    · refine MeasureTheory.Integrable.mono' (g := fun _ => b n) ?_ ?_ ?_
      · exact MeasureTheory.integrable_const _
      · exact hadaptX n j |> fun h => h.aestronglyMeasurable.mono (hle n (j + 1))
      · exact Filter.Eventually.of_forall fun ω => hboundX n j ω
    · exact integrable_real_of_bound
        ((hadaptY n j |> StronglyMeasurable.aestronglyMeasurable) |> fun h =>
          h.mono (hle n (j + 1))) (fun ω => hboundY n j ω)
  have hZbound : ∀ n j ω, |Z n j ω| ≤ (|a| + |c|) * b n := by
    intro n j ω
    show |a * X n j ω + c * Y n j ω| ≤ (|a| + |c|) * b n
    have hx := abs_le.mp (hboundX n j ω)
    have hy := abs_le.mp (hboundY n j ω)
    rw [abs_le]
    refine ⟨?_, ?_⟩ <;>
      (cases abs_cases a <;> cases abs_cases c <;> nlinarith [hx, hy])
  have hZCbr : ∀ n ω, ∑ j ∈ Finset.range (kn n), (Z n j ω) ^ 2 ≤ 2 * (a ^ 2 + c ^ 2) * C := by
    intro n ω
    refine le_trans (Finset.sum_le_sum fun i _ =>
      show (a * X n i ω + c * Y n i ω) ^ 2 ≤ (a ^ 2 + c ^ 2) * (X n i ω ^ 2 + Y n i ω ^ 2) by
        nlinarith only [sq_nonneg (a * Y n i ω - c * X n i ω)]) ?_
    rw [← Finset.mul_sum _ _ _, Finset.sum_add_distrib]
    nlinarith [hCbrX n ω, hCbrY n ω]
  have hZbracket : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (kn n), (Z n j ω) ^ 2) atTop (𝓝 (psiForm u a c)) := by
    filter_upwards [hbr1, hbr2X, hbr2Y, hbr2XY] with ω hω1 hω2 hω3 hω4
    have h_split : ∀ n, ∑ j ∈ Finset.range (kn n), (Z n j ω) ^ 2
        = (∑ j ∈ Finset.range (mn n), (Z n j ω) ^ 2)
          + (∑ j ∈ Finset.Ico (mn n) (kn n), (Z n j ω) ^ 2) :=
      fun n => by rw [Finset.sum_range_add_sum_Ico _ (hmn n)]
    have h_range : ∀ n, ∑ j ∈ Finset.range (mn n), (Z n j ω) ^ 2
        = (a + c) ^ 2 * ∑ j ∈ Finset.range (mn n), (X n j ω) ^ 2 := by
      intro n
      rw [Finset.mul_sum _ _ _]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [show Z n j ω = (a + c) * X n j ω by
        rw [show Z n j ω = a * X n j ω + c * Y n j ω from rfl,
          hlock n j ω (Finset.mem_range.mp hj)]; ring]
      ring
    have h_range2 : ∀ n, ∑ j ∈ Finset.Ico (mn n) (kn n), (Z n j ω) ^ 2
        = a ^ 2 * ∑ j ∈ Finset.Ico (mn n) (kn n), (X n j ω) ^ 2
          + 2 * a * c * ∑ j ∈ Finset.Ico (mn n) (kn n), (X n j ω) * (Y n j ω)
          + c ^ 2 * ∑ j ∈ Finset.Ico (mn n) (kn n), (Y n j ω) ^ 2 := by
      intro n
      rw [Finset.mul_sum _ _ _, Finset.mul_sum _ _ _, Finset.mul_sum _ _ _,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      congr; ext; ring
    convert Filter.Tendsto.add (Filter.Tendsto.const_mul ((a + c) ^ 2) hω1)
      (Filter.Tendsto.add (Filter.Tendsto.add (Filter.Tendsto.const_mul (a ^ 2) hω2)
        (Filter.Tendsto.const_mul (2 * a * c) hω4)) (Filter.Tendsto.const_mul (c ^ 2) hω3))
      using 2
    · rw [h_split, h_range, h_range2]
    · unfold psiForm; ring
  have hPS : ∀ n ω, (partialSum (Z n) (kn n) ω : ℝ)
      = a * partialSum (X n) (kn n) ω + c * partialSum (Y n) (kn n) ω := by
    intro n ω
    simp only [partialSum, Z, Finset.sum_add_distrib, Finset.mul_sum]
  have hfun : (fun n => ∫ ω, Complex.exp (((a * partialSum (X n) (kn n) ω
        + c * partialSum (Y n) (kn n) ω : ℝ) : ℂ) * Complex.I) ∂μ)
      = (fun n => ∫ ω, Complex.exp (((1 * partialSum (Z n) (kn n) ω : ℝ) : ℂ) * Complex.I) ∂μ) := by
    funext n
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hPS, one_mul]
  rw [hfun]
  have hcore := TypeDDecoupling.MartingaleCLT.core_charFun_tendsto kn 𝓕 Z (psiForm u a c)
    (fun n => (|a| + |c|) * b n) (2 * (a ^ 2 + c ^ 2) * C) hmono hle hZ hZmds
    (fun n => mul_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg c)) (hb0 n))
    (by simpa using hblim.const_mul (|a| + |c|)) (fun n j ω => hZbound n j ω)
    (fun n ω => hZCbr n ω) hZbracket 1
  convert hcore using 3
  norm_num

/-- **Edge case `u = 0` (independent pair).**  With `m n / k n → 0`, no locked phase in
the limit and diagonal brackets `∑ X² → 1`, `∑ Y² → 1`, `∑ XY → 0`, the limit is
`exp(-½ (a²+c²))`, the characteristic function of the independent standard normal
pair. -/
theorem twophase_charFun_tendsto_indep
    (kn : ℕ → ℕ) (mn : ℕ → ℕ) (𝓕 : ℕ → ℕ → MeasurableSpace Ω)
    (X Y : ℕ → ℕ → Ω → ℝ) (b : ℕ → ℝ) (C : ℝ)
    (hmn : ∀ n, mn n ≤ kn n)
    (hmono : ∀ n, Monotone (𝓕 n)) (hle : ∀ n k, 𝓕 n k ≤ mΩ)
    (hadaptX : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (X n j))
    (hadaptY : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (Y n j))
    (hmdsX : ∀ n j, μ[X n j | 𝓕 n j] =ᵐ[μ] 0)
    (hmdsY : ∀ n j, μ[Y n j | 𝓕 n j] =ᵐ[μ] 0)
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hboundX : ∀ n j ω, |X n j ω| ≤ b n) (hboundY : ∀ n j ω, |Y n j ω| ≤ b n)
    (hCbrX : ∀ n ω, ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2 ≤ C)
    (hCbrY : ∀ n ω, ∑ j ∈ Finset.range (kn n), (Y n j ω) ^ 2 ≤ C)
    (hlock : ∀ n j ω, j < mn n → X n j ω = Y n j ω)
    (hbr1 : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (mn n), (X n j ω) ^ 2) atTop (𝓝 0))
    (hbr2X : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.Ico (mn n) (kn n), (X n j ω) ^ 2) atTop (𝓝 1))
    (hbr2Y : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.Ico (mn n) (kn n), (Y n j ω) ^ 2) atTop (𝓝 1))
    (hbr2XY : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.Ico (mn n) (kn n), (X n j ω) * (Y n j ω)) atTop (𝓝 0)) :
    ∀ a c : ℝ, Tendsto
      (fun n => ∫ ω, Complex.exp (((a * partialSum (X n) (kn n) ω
          + c * partialSum (Y n) (kn n) ω : ℝ) : ℂ) * Complex.I) ∂μ)
      atTop (𝓝 (Complex.exp (((-(a ^ 2 + c ^ 2) / 2 : ℝ) : ℂ)))) := by
  intro a c
  have h := twophase_charFun_tendsto kn mn 𝓕 X Y 0 (by norm_num) b C hmn hmono hle
    hadaptX hadaptY hmdsX hmdsY hb0 hblim hboundX hboundY hCbrX hCbrY hlock hbr1
    (by simpa using hbr2X) (by simpa using hbr2Y) hbr2XY a c
  simpa [psiForm_zero] using h

/-- **Edge case `u = 1` (identical/locked pair).**  With `m n / k n → 1`, the two
components are locked throughout in the limit, `∑_{j<m n} X² → 1`, and the post-split
brackets vanish; the limit is `exp(-½ (a+c)²)`, the characteristic function of the
degenerate pair `(ξ, ξ)` with `ξ ∼ N(0,1)`. -/
theorem twophase_charFun_tendsto_locked
    (kn : ℕ → ℕ) (mn : ℕ → ℕ) (𝓕 : ℕ → ℕ → MeasurableSpace Ω)
    (X Y : ℕ → ℕ → Ω → ℝ) (b : ℕ → ℝ) (C : ℝ)
    (hmn : ∀ n, mn n ≤ kn n)
    (hmono : ∀ n, Monotone (𝓕 n)) (hle : ∀ n k, 𝓕 n k ≤ mΩ)
    (hadaptX : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (X n j))
    (hadaptY : ∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (Y n j))
    (hmdsX : ∀ n j, μ[X n j | 𝓕 n j] =ᵐ[μ] 0)
    (hmdsY : ∀ n j, μ[Y n j | 𝓕 n j] =ᵐ[μ] 0)
    (hb0 : ∀ n, 0 ≤ b n) (hblim : Tendsto b atTop (𝓝 0))
    (hboundX : ∀ n j ω, |X n j ω| ≤ b n) (hboundY : ∀ n j ω, |Y n j ω| ≤ b n)
    (hCbrX : ∀ n ω, ∑ j ∈ Finset.range (kn n), (X n j ω) ^ 2 ≤ C)
    (hCbrY : ∀ n ω, ∑ j ∈ Finset.range (kn n), (Y n j ω) ^ 2 ≤ C)
    (hlock : ∀ n j ω, j < mn n → X n j ω = Y n j ω)
    (hbr1 : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.range (mn n), (X n j ω) ^ 2) atTop (𝓝 1))
    (hbr2X : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.Ico (mn n) (kn n), (X n j ω) ^ 2) atTop (𝓝 0))
    (hbr2Y : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.Ico (mn n) (kn n), (Y n j ω) ^ 2) atTop (𝓝 0))
    (hbr2XY : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ∑ j ∈ Finset.Ico (mn n) (kn n), (X n j ω) * (Y n j ω)) atTop (𝓝 0)) :
    ∀ a c : ℝ, Tendsto
      (fun n => ∫ ω, Complex.exp (((a * partialSum (X n) (kn n) ω
          + c * partialSum (Y n) (kn n) ω : ℝ) : ℂ) * Complex.I) ∂μ)
      atTop (𝓝 (Complex.exp (((-(a + c) ^ 2 / 2 : ℝ) : ℂ)))) := by
  intro a c
  have h := twophase_charFun_tendsto kn mn 𝓕 X Y 1 (by norm_num) b C hmn hmono hle
    hadaptX hadaptY hmdsX hmdsY hb0 hblim hboundX hboundY hCbrX hCbrY hlock
    (by simpa using hbr1) (by simpa using hbr2X) (by simpa using hbr2Y) hbr2XY a c
  simpa [psiForm_one] using h

end Tier1

section Tier2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Tier 2 — the mixture lemma (tower property + dominated convergence).**

Let `Z1 n, Z2 n` be real random variables, `G n` sub-σ-algebras, `U n` measurable with
`U n → Ulim` a.e. and values in `[0,1]`.  If for fixed `(a,c)` the conditional
characteristic function matches the correlation-`U n` bivariate normal in `L¹` (the
sanctioned `L¹` form of the hypothesis, brief remark (2)),
`E[ ‖ E[exp(i(a Z1 n + c Z2 n)) | G n] - exp(-½ ψ_{U n}(a,c)) ‖ ] → 0`, then the
unconditional characteristic function converges to the `Ulim`-mixture,
`E[exp(i(a Z1 n + c Z2 n))] → E[exp(-½ ψ_{Ulim}(a,c))]`.

**Route.**  Tower property `∫ f_n = ∫ E[f_n | G n]`; then
`‖∫ E[f_n|G n] - ∫ exp(-½ ψ_{U n})‖ = ‖∫ (E[f_n|G n] - exp(-½ ψ_{U n}))‖
  ≤ ∫ ‖E[f_n|G n] - exp(-½ ψ_{U n})‖ → 0` by the `L¹` hypothesis, while
`∫ exp(-½ ψ_{U n}) → ∫ exp(-½ ψ_{Ulim})` by dominated convergence (`U n → Ulim` a.e.,
`u ↦ exp(-½ ψ_u)` continuous, bounded by `1` on `[0,1]`). -/
theorem mixture_charFun_tendsto
    (G : ℕ → MeasurableSpace Ω) (hG : ∀ n, G n ≤ mΩ)
    (Z1 Z2 : ℕ → Ω → ℝ)
    (hZ1 : ∀ n, Measurable (Z1 n)) (hZ2 : ∀ n, Measurable (Z2 n))
    (U : ℕ → Ω → ℝ) (Ulim : Ω → ℝ)
    (hUmeas : ∀ n, Measurable (U n))
    (hUconv : ∀ᵐ ω ∂μ, Tendsto (fun n => U n ω) atTop (𝓝 (Ulim ω)))
    (hUrange : ∀ n ω, U n ω ∈ Set.Icc (0 : ℝ) 1)
    (a c : ℝ)
    (hcond : Tendsto
      (fun n => ∫ ω, ‖(μ[fun ω' => Complex.exp (((a * Z1 n ω' + c * Z2 n ω' : ℝ) : ℂ)
            * Complex.I) | G n]) ω
          - Complex.exp (((-psiForm (U n ω) a c / 2 : ℝ) : ℂ))‖ ∂μ) atTop (𝓝 0)) :
    Tendsto
      (fun n => ∫ ω, Complex.exp (((a * Z1 n ω + c * Z2 n ω : ℝ) : ℂ) * Complex.I) ∂μ)
      atTop (𝓝 (∫ ω, Complex.exp (((-psiForm (Ulim ω) a c / 2 : ℝ) : ℂ)) ∂μ)) := by
  -- The unconditional characteristic-function integrand and the two Gaussian integrands.
  set f : ℕ → Ω → ℂ :=
    fun n ω => Complex.exp (((a * Z1 n ω + c * Z2 n ω : ℝ) : ℂ) * Complex.I) with hf
  set g : ℕ → Ω → ℂ :=
    fun n ω => Complex.exp (((-psiForm (U n ω) a c / 2 : ℝ) : ℂ)) with hg
  set gU : Ω → ℂ := fun ω => Complex.exp (((-psiForm (Ulim ω) a c / 2 : ℝ) : ℂ)) with hgU
  -- `‖f n ω‖ = 1`.
  have hf_norm : ∀ n ω, ‖f n ω‖ = 1 := by
    intro n ω; simp [hf, Complex.norm_exp]
  -- `‖g n ω‖ ≤ 1` (since `ψ ≥ 0` on `[0,1]`), and likewise a pointwise value for `gU`.
  have hg_norm : ∀ n ω, ‖g n ω‖ ≤ 1 := by
    intro n ω
    rw [hg]
    simp only [Complex.norm_exp, Complex.ofReal_re, neg_div]
    exact Real.exp_le_one_iff.2 (by
      have := psiForm_nonneg (hUrange n ω) a c; linarith)
  -- Measurability of `f n` and `g n`.
  have hf_meas : ∀ n, Measurable (f n) := by
    intro n
    exact Complex.measurable_exp.comp (((Complex.measurable_ofReal.comp
      (((hZ1 n).const_mul a).add ((hZ2 n).const_mul c))).mul measurable_const))
  have hg_meas : ∀ n, Measurable (g n) := by
    intro n
    refine Complex.measurable_exp.comp (Complex.measurable_ofReal.comp ?_)
    exact (((continuous_psiForm a c).measurable.comp (hUmeas n)).neg).div_const _
  -- Integrability of `f n` and `g n` (bounded by `1` on a probability measure).
  have hf_int : ∀ n, Integrable (f n) μ :=
    fun n => (MeasureTheory.integrable_const (1 : ℝ)).mono' (hf_meas n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [hf_norm n ω])
  have hg_int : ∀ n, Integrable (g n) μ :=
    fun n => (MeasureTheory.integrable_const (1 : ℝ)).mono' (hg_meas n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => hg_norm n ω)
  -- Step A (tower): `∫ f n = ∫ E[f n | G n]`.
  have hstepA : ∀ n, ∫ ω, f n ω ∂μ = ∫ ω, (μ[f n | G n]) ω ∂μ :=
    fun n => (MeasureTheory.integral_condExp (hG n)).symm
  -- Step B: `∫ E[f n | G n] - ∫ g n → 0`.
  have hstepB : Tendsto (fun n => (∫ ω, (μ[f n | G n]) ω ∂μ) - ∫ ω, g n ω ∂μ)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hcond
    rw [← MeasureTheory.integral_sub MeasureTheory.integrable_condExp (hg_int n)]
    exact MeasureTheory.norm_integral_le_integral_norm _
  -- Continuity of `u ↦ exp(-½ ψ_u)`.
  have hcont : Continuous fun u : ℝ => Complex.exp (((-psiForm u a c / 2 : ℝ) : ℂ)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
      (((continuous_psiForm a c).neg).div_const _))
  -- Step C: `∫ g n → ∫ gU` by dominated convergence.
  have hstepC : Tendsto (fun n => ∫ ω, g n ω ∂μ) atTop (𝓝 (∫ ω, gU ω ∂μ)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun n => (hg_meas n).aestronglyMeasurable) (MeasureTheory.integrable_const 1)
      (fun n => Filter.Eventually.of_forall fun ω => hg_norm n ω) ?_
    filter_upwards [hUconv] with ω hω
    exact (hcont.tendsto (Ulim ω)).comp hω
  -- Combine.
  show Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, gU ω ∂μ))
  have e1 : (fun n => ∫ ω, f n ω ∂μ)
      = fun n => ((∫ ω, (μ[f n | G n]) ω ∂μ) - ∫ ω, g n ω ∂μ) + ∫ ω, g n ω ∂μ := by
    funext n; rw [hstepA n]; ring
  rw [e1]
  simpa using hstepB.add hstepC

/-
**Tier 2 — closed form of the mixture correlation.**
`E[min(Exp(λ),1)] = (1 - e^{-λ})/λ`, i.e. with the `Exp(λ)` density `λ e^{-λ t}` on
`(0,∞)`, `∫₀^∞ min(t,1)·λ·e^{-λ t} dt = (1 - e^{-λ})/λ`.  Specialized at `λ = 4c` this
is `TypeDDecoupling.expMin_mean_eq_rhoCorr` (whose value is `rhoCorr c`, the correlation
of `thm:closed`).
-/
lemma expMin_mean {lam : ℝ} (hlam : 0 < lam) :
    ∫ t in Set.Ioi (0 : ℝ), min t 1 * lam * Real.exp (-(lam * t))
      = (1 - Real.exp (-lam)) / lam := by
  -- Split the integral into two parts: from 0 to 1 and from 1 to ∞.
  have h_split : ∫ t in Set.Ioi 0, min t 1 * lam * Real.exp (-(lam * t)) = (∫ t in Set.Ioc 0 1, t * lam * Real.exp (-(lam * t))) + (∫ t in Set.Ioi 1, 1 * lam * Real.exp (-(lam * t))) := by
    have h_split : ∫ t in Set.Ioi 0, min t 1 * lam * Real.exp (-(lam * t)) = (∫ t in Set.Ioc 0 1, min t 1 * lam * Real.exp (-(lam * t))) + (∫ t in Set.Ioi 1, min t 1 * lam * Real.exp (-(lam * t))) := by
      rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num;
      · exact Continuous.integrableOn_Ioc ( by apply_rules [ Continuous.mul, Continuous.min ] <;> continuity );
      · -- The integral of the exponential function is convergent.
        have h_exp_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-(lam * t))) (Set.Ioi 1) := by
          have := ( exp_neg_integrableOn_Ioi 0 hlam );
          simpa only [ neg_mul ] using this.mono_set ( Set.Ioi_subset_Ioi zero_le_one );
        refine' h_exp_integrable.const_mul lam |> fun h => h.congr _;
        filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by rw [ min_eq_right ( by linarith [ hx.out ] ) ] ; ring;
    exact h_split.trans ( congrArg₂ _ ( MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ min_eq_left hx.2 ] ) ( MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [ min_eq_right hx.out.le ] ) );
  -- Evaluate the first integral: $\int_{0}^{1} t \lambda e^{-\lambda t} \, dt$.
  have h_first : ∫ t in Set.Ioc 0 1, t * lam * Real.exp (-(lam * t)) = (1 - (lam + 1) * Real.exp (-lam)) / lam := by
    rw [ ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_deriv_eq_sub' ];
    rotate_left;
    use fun x => - ( x + 1 / lam ) * Real.exp ( - ( lam * x ) );
    · ext; norm_num [ mul_comm lam, hlam.ne' ] ; ring;
      norm_num [ mul_comm lam ] ; ring;
      norm_num [ hlam.ne' ];
    · fun_prop;
    · fun_prop;
    · grind +suggestions;
  -- Evaluate the second integral: $\int_{1}^{\infty} \lambda e^{-\lambda t} \, dt$.
  have h_second : ∫ t in Set.Ioi 1, lam * Real.exp (-(lam * t)) = Real.exp (-lam) := by
    have := integral_exp_neg_mul_rpow zero_lt_one hlam;
    -- Use the fact that the integral of $e^{-\lambda t}$ over $(1, \infty)$ is the same as the integral over $(0, \infty)$ shifted by 1.
    have h_shift : ∫ t in Set.Ioi 1, Real.exp (-(lam * t)) = ∫ t in Set.Ioi 0, Real.exp (-(lam * (t + 1))) := by
      rw [ ← MeasureTheory.integral_indicator ( measurableSet_Ioi ), ← MeasureTheory.integral_indicator ( measurableSet_Ioi ) ];
      rw [ ← MeasureTheory.integral_add_right_eq_self _ 1 ] ; congr ; ext ; rw [ Set.indicator_apply, Set.indicator_apply ] ; aesop;
    simp_all +decide [ Real.rpow_neg_one, mul_add, Real.exp_add, MeasureTheory.integral_const_mul ];
    norm_num [ mul_assoc, mul_comm lam, hlam.ne' ];
  grind

end Tier2

section Tier3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Tier 3 (stretch) — the assembled random-changepoint statement.**

A two-phase array with a `G n`-measurable random change point `M n`, split fraction
`M n / k n → U` a.e., whose conditional brackets satisfy the Tier-1 hypotheses
conditionally on `G n`.  As sanctioned by the brief, the conditional Tier-1
applicability is packaged as the single named hypothesis `hcond` (the conditional
characteristic-function convergence, which the fixed-changepoint `twophase_charFun_tendsto`
supplies pointwise in the split fraction); we do not re-prove `core_charFun_tendsto`
conditionally.  The conclusion, via the Tier-2 `mixture_charFun_tendsto`, is the mixture
characteristic-function limit `E[exp(i(a S n + c R n))] → E[exp(-½ ψ_U(a,c))]`. -/
theorem twophase_mixture_charFun_tendsto
    (kn : ℕ → ℕ) (G : ℕ → MeasurableSpace Ω) (hG : ∀ n, G n ≤ mΩ)
    (S R : ℕ → Ω → ℝ)
    (hS : ∀ n, Measurable (S n)) (hR : ∀ n, Measurable (R n))
    (M : ℕ → Ω → ℕ) (Ulim : Ω → ℝ)
    (hMmeas : ∀ n, Measurable (fun ω => (M n ω : ℝ)))
    (hMconv : ∀ᵐ ω ∂μ, Tendsto (fun n => (M n ω : ℝ) / (kn n : ℝ)) atTop (𝓝 (Ulim ω)))
    (hMrange : ∀ n ω, (M n ω : ℝ) / (kn n : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (a c : ℝ)
    (hcond : Tendsto
      (fun n => ∫ ω, ‖(μ[fun ω' => Complex.exp (((a * S n ω' + c * R n ω' : ℝ) : ℂ)
            * Complex.I) | G n]) ω
          - Complex.exp (((-psiForm ((M n ω : ℝ) / (kn n : ℝ)) a c / 2 : ℝ) : ℂ))‖ ∂μ)
        atTop (𝓝 0)) :
    Tendsto
      (fun n => ∫ ω, Complex.exp (((a * S n ω + c * R n ω : ℝ) : ℂ) * Complex.I) ∂μ)
      atTop (𝓝 (∫ ω, Complex.exp (((-psiForm (Ulim ω) a c / 2 : ℝ) : ℂ)) ∂μ)) := by
  exact mixture_charFun_tendsto G hG S R hS hR
    (fun n ω => (M n ω : ℝ) / (kn n : ℝ)) Ulim
    (fun n => (hMmeas n).div_const _) hMconv hMrange a c hcond

end Tier3

end TypeDDecoupling.TwoPhase