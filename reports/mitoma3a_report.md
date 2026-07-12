# Mitoma campaign, task 3a — report

**The Hermite functions as a Hilbert basis of `L²(ℝ)`.**

Full delivery. New self-contained file `TypeDDecouplingHermite.lean` (Mathlib imports
only; no existing project file edited). The whole project builds (8066 jobs). No
`axiom`/`sorry`; every headline result depends only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms`).

Convention: probabilists' Hermite polynomials `Polynomial.hermite` (monic, weight
`e^{-x²/2}`), as fixed by the brief.

## Final normalizations (derived, not assumed)

* Gaussian integral: `∫ e^{-x²/2} dx = √(2π)`  (`integral_gwFun`).
* Polynomial orthogonality:
  `∫ Hₘ(x) Hₙ(x) e^{-x²/2} dx = δₘₙ · n! √(2π)`  (`hermite_orthogonality`).
* Normalizing constant `cₙ = (n!·√(2π))^{-1/2}`  (`hermiteC`), i.e.
  `hₙ(x) = cₙ Hₙ(x) e^{-x²/4}`  (`hermiteFun`).
* The constant is **derived**: `hermiteFun_orthonormal_integral` proves
  `∫ hₘ hₙ dx = δₘₙ` (Lebesgue measure), which forces `cₙ² · n!√(2π) = 1`. This
  confirms the brief's classical value `cₙ = (n!√(2π))^{-1/2}` (catch-#2 style
  convention check passed).

## Deliverables and key declarations

1. **Hermite functions and Schwartz bundling.**
   `hermiteFun`, `hermiteSchwartz : ℕ → 𝓢(ℝ,ℝ)` with
   `hermiteSchwartz_apply : hermiteSchwartz n x = hermiteFun n x`, and
   `hermiteFun_mem_schwartz` (consumed by M3b).
   The Gaussian `e^{-x²/4}` is bundled as `gaussQ : 𝓢(ℝ,ℝ)`; its smoothness and
   rapid decay are proved from scratch (`gaussQ_smooth`, `iteratedDeriv_gaussQ_eq`
   — every iterate is a polynomial times the Gaussian — `poly_mul_gaussQ_bounded`,
   `gaussQ_decay`). Hermite functions are then `cₙ • smulLeftCLM (Hₙ) gaussQ`.

2. **Orthogonality of the Hermite polynomials** (`hermite_orthogonality`).
   Route: a single-integration-by-parts recurrence
   `∫ Hₘ Hₙ₊₁ e^{-x²/2} = m ∫ Hₘ₋₁ Hₙ e^{-x²/2}` (`orthogonality_recurrence`),
   obtained from `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`
   (the integrability-only IBP on ℝ, no boundary terms needed) together with the
   pointwise derivative `d/dx (Hₙ e^{-x²/2}) = -Hₙ₊₁ e^{-x²/2}`
   (`hasDerivAt_hpoly_mul_gwFun`, from Mathlib's Rodrigues formula
   `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`) and `Hₙ' = n Hₙ₋₁`
   (`derivative_hermite`). Base case `∫ Hₘ e^{-x²/2} = δₘ₀√(2π)`
   (`integral_hpoly_mul_gwFun`); induction closes the general case using
   `natDegree_hermite`/`coeff_hermite_self` for the top coefficient.
   Integrability of polynomial×Gaussian: `integrable_hpoly_mul_hpoly_mul_gwFun`.

3. **Completeness** (the analytic heart, `hermite_complete` /
   `hermite_complete_fun`). If `f ∈ L²` is orthogonal to every `hₙ`, then `f = 0`.
   Route (Fourier, no complex-analysis library):
   * `moments_zero_of_orthogonal`: all moments `∫ xᵏ e^{-x²/4} f = 0`
     (strong induction using monicity of `Hₖ`; `cmoments_zero` is the ℂ version).
   * `g := f·e^{-x²/4} ∈ L¹` (`integrable_gauss_quarter_mul`, Cauchy–Schwarz via
     `MemLp.integrable_mul`).
   * `fourier_gauss_quarter_mul_eq_zero`: `𝓕 g ≡ 0`, by term-by-term integration
     of the power series of `e^{-2πixξ}`, justified by dominated convergence with
     the single dominating function `|f|·e^{-x²/4}·e^{2π|ξ||x|}`
     (`integrable_dominating`, using the pointwise bound
     `-x²/4 + c|x| ≤ 2c² - x²/8`); the partial-sum integrals vanish by the moments.
   * `ae_zero_of_fourier_zero`: **L¹-Fourier injectivity** — `Integrable g` and
     `𝓕 g ≡ 0` imply `g = 0` a.e. Proved via the multiplication/flip formula
     `VectorFourier.integral_fourierIntegral_smul_eq_flip` paired with Schwartz
     test functions (`HasCompactSupport.toSchwartzMap`, Schwartz Fourier
     inversion) and `MeasureTheory.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.
   Then `g = 0` a.e. gives `f = 0` a.e. (Gaussian factor never vanishes).

4. **Hilbert basis packaging.**
   `hermiteLp n := (hermiteSchwartz n).toLp 2 volume`; orthonormality
   `hermiteLp_orthonormal`; dense span `hermiteLp_span_dense` (from completeness
   via `Submodule.topologicalClosure_eq_top_iff`); and
   `hermiteBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 volume) := HilbertBasis.mk …`
   with `hermiteBasis_apply : hermiteBasis n = hermiteLp n`.
   Parseval consequences confirmed to elaborate: `hermiteBasis_repr_apply`
   (`repr f n = ⟨hₙ,f⟩`), `hermiteBasis_hasSum_repr` (`f = ∑ ⟨hₙ,f⟩ hₙ`),
   `hermiteBasis_hasSum_inner` (Parseval `∑ ⟨hₙ,f⟩⟨hₙ,g⟩ = ⟨f,g⟩`).

5. **Bridge lemma for M3b.**
   `hermiteCoeffCLM n : 𝓢(ℝ,ℝ) →L[ℝ] ℝ`, the coefficient functional
   `φ ↦ ∫ φ hₙ`, built as `integralCLM ∘ smulLeftCLM (hermiteFun n)`, with
   `hermiteCoeffCLM_apply : hermiteCoeffCLM n φ = ∫ x, hermiteFun n x * φ x`.

## Mathlib lemmas that carried the two hard parts

* Orthogonality (2): `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`,
  `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`,
  `Polynomial.hasDerivAt_aeval`, `integral_gaussian`,
  `integrable_rpow_mul_exp_neg_mul_sq`.
* Completeness (3): `MeasureTheory.tendsto_integral_of_dominated_convergence`,
  `NormedSpace.expSeries_div_summable` (exp power series),
  `VectorFourier.integral_fourierIntegral_smul_eq_flip`,
  `MeasureTheory.ae_eq_zero_of_integral_contDiff_smul_eq_zero`,
  `HasCompactSupport.toSchwartzMap`, Schwartz Fourier inversion (`FourierPair`),
  `MeasureTheory.MemLp.integrable_mul`.

Mathlib provided the Hermite *polynomials* and Rodrigues formula but **no**
orthogonality, completeness, or Hermite *functions*; all of these are new here.
