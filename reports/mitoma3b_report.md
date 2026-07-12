# Mitoma campaign, task 3b — report

**The Hermite–Sobolev chain generates the Schwartz topology.**

Full delivery. New self-contained file `TypeDDecouplingHermiteSobolev.lean`
(imports `Mathlib` and the M3a file `TypeDDecouplingHermite`; no existing project
file edited). The whole project builds (8067 jobs). No `axiom`/`sorry`; every
headline result depends only on the standard axioms `propext`,
`Classical.choice`, `Quot.sound` (checked with `#print axioms`).

Throughout, `⟨φ, hₙ⟩ := hermiteCoeffCLM n φ = ∫ x, hermiteFun n x * φ x`
(M3a's coefficient functional), and `hₙ = hermiteFun n = cₙ Hₙ e^{-x²/4}` with
probabilists' `Hₙ` and `cₙ = (n!·√(2π))^{-1/2}` (M3a's convention).

## Derived identities and constants (all checked, not assumed)

* **Three-term recurrence** `x Hₙ = Hₙ₊₁ + n Hₙ₋₁` (`hpoly_three_term`), from
  M3a's `hpoly_add_one`/`hpoly_deriv` (i.e. `Hₙ' = n Hₙ₋₁`).
* **Pointwise derivative** `hₙ'(x) = cₙ (n Hₙ₋₁ − (x/2) Hₙ) e^{-x²/4}`
  (`hasDerivAt_hermiteFun`).
* **Constant ratios** `√(n+1)·c_{n+1} = cₙ` (`sqrt_succ_mul_hermiteC`) and
  `c_{n-1} = √n·cₙ` for `n ≥ 1` (`hermiteC_pred`).
* **Normalized ladder identities** (`O(√(n+1))` coefficients, exactly as
  predicted):
  * `x hₙ = √(n+1) hₙ₊₁ + √n hₙ₋₁`  (`hermiteFun_x_ladder`);
  * `hₙ' = ½(√n hₙ₋₁ − √(n+1) hₙ₊₁)`  (`hermiteFun_deriv_ladder`).
* **Second derivative / ODE** `hₙ'' = (x²/4 − n − ½) hₙ`
  (`deriv_deriv_hermiteFun`).
* **Eigenvalue** `A hₙ = (n+1) hₙ` (`oscCLM_hermiteSchwartz`), confirming the
  predicted `−hₙ'' + (x²/4) hₙ = (n+½) hₙ`, hence eigenvalue `n+1` for
  `A = −Δ + (x²/4 + ½)`.
* **Coefficient recurrences under the ladder operators:**
  * `⟨x·φ, hₙ⟩ = √(n+1) ⟨φ, hₙ₊₁⟩ + √n ⟨φ, hₙ₋₁⟩`  (`coeff_xMulCLM`);
  * `⟨φ', hₙ⟩ = ½(√(n+1) ⟨φ, hₙ₊₁⟩ − √n ⟨φ, hₙ₋₁⟩)`  (`coeff_derivCLM`).
* **Agmon sup-bound** `|hₙ(x)| ≤ √2 (n+1)^{1/4}` (`hermiteFun_sup_bound`),
  confirming the predicted `1/4` exponent, from the inline 1-D Agmon inequality
  `f(x)² ≤ 2‖f‖₂‖f'‖₂` (`schwartz_sq_le_agmon`), `‖hₙ‖₂ = 1`
  (`integral_hermiteFun_sq`) and `‖hₙ'‖₂² = (2n+1)/4 ≤ n+1`
  (`integral_deriv_hermiteFun_sq_le`).

## Deliverables and key declarations

1. **The oscillator** `oscCLM : 𝓢(ℝ,ℝ) →L[ℝ] 𝓢(ℝ,ℝ)`,
   `A φ = −Δφ + (x²/4 + ½)·φ`, from Mathlib's Laplacian CLM and
   `smulLeftCLM`; iterates are `oscCLM ^ r`. `oscCLM_apply`,
   `laplacianCLM_apply_eq` (`Δ = ∂²` on ℝ).
2. **Self-adjointness** `∫ (Aφ)ψ = ∫ φ (Aψ)` (`oscCLM_self_adjoint`), via
   `SchwartzMap.integral_mul_laplacian_right_eq_left` and pointwise symmetry.
3. **Eigenrelation** `oscCLM_hermiteSchwartz` and the ladder identities above.
4. **Coefficient decay** `hermiteCoeff_decay r`: for every `r` there are `C ≥ 0`
   and a finite `s ⊆ ℕ×ℕ` with
   `|⟨φ,hₙ⟩| ≤ (n+1)^{−r}·C·(s.sup pₖₗ) φ`. Route: self-adjointness `r` times
   (`hermiteCoeffCLM_oscCLM_pow`), Bessel `|⟨φ,hₙ⟩| ≤ ‖φ‖_{L²}`
   (`abs_hermiteCoeffCLM_le_L2`, from `hermiteCoeffCLM_eq_inner`), and continuity
   of `𝓢 →L Lp` (`normCLM_seminorm_bound`).
5. **Polynomial growth of Hermite seminorms** `hermiteSeminorm_growth (k m)`:
   `p_{k,m}(hₙ) ≤ C (n+1)^N` (honest exponent `N = r₀+k+m` from the reduction,
   any polynomial exponent suffices downstream).
6. **Pointwise expansion** `hermiteExpansion_pointwise`:
   `φ(x) = ∑ₙ ⟨φ,hₙ⟩ hₙ(x)` (`HasSum`). The series function is continuous
   (`continuous_hermiteSeriesFun`, Weierstrass M-test from (4)+Agmon) and equals
   `φ` a.e. via `L²` convergence and an a.e.-subsequence
   (`hermiteSeriesFun_ae_eq`, using M3a's `hermiteBasis_hasSum_repr`), hence
   everywhere by continuity.
7. **Hermite–Sobolev seminorms and the two-sided equivalence.**
   `sobolevNormSq r φ = ∑ₙ (n+1)^{2r} ⟨φ,hₙ⟩²` (`sobolev_summable`),
   `sobolevSeminorm r φ = √(sobolevNormSq r φ)` (homogeneous:
   `sobolevSeminorm_smul`).
   * **(7a)** `sobolev_continuous r`: `‖φ‖_r ≤ C·(s.sup pₖₗ) φ` (continuous
     w.r.t. the canonical topology).
   * **(7b)** `seminorm_le_sobolev (k m)`: `p_{k,m}(φ) ≤ C·‖φ‖_r` for a suitable
     `r` (full, all `k,m`). Route: `p_{k,m}(φ) = p_{0,0}(x^k ∂^m φ)`
     (`seminorm_le_seminorm_zero_transform`), `p_{0,0} ≤ C‖·‖₂`
     (`seminorm_zero_le_sobolev`, from (6)+Agmon+Cauchy–Schwarz), and the
     level-shift bounds `‖x·φ‖_r ≤ C‖φ‖_{r+1}`,
     `‖φ'‖_r ≤ C‖φ‖_{r+1}` (`exists_sobolev_xMulCLM_bound`,
     `exists_sobolev_derivCLM_bound`) iterated
     (`exists_sobolev_xMulCLM_pow_bound`, `exists_sobolev_derivCLM_pow_bound`).
   Together: the countable Hilbertian family `{‖·‖_r}_{r∈ℕ}` generates the
   Schwartz topology (two-sided domination, `sobolev_continuous` +
   `seminorm_le_sobolev`).
8. **Hilbert–Schmidt data for M3c.** `hermiteSobolevVec r j = (j+1)^{−r} hₙ`,
   with `‖hⱼ‖_q = (j+1)^q` (`sobolevSeminorm_hermiteSchwartz`) and
   `‖e^r_j‖_q = (j+1)^{q−r}` (`sobolevSeminorm_hermiteSobolevVec`). The named
   lemma **`hermiteSobolev_hs_summable (q r) (h : q + 1 ≤ r)`** :
   `Summable (fun j => (sobolevSeminorm q (hermiteSobolevVec r j))^2)`
   is the nuclearity input Mitoma's Lemma 3.2 (M3c) consumes.

## Shapes M3c should import

* Two-sided domination generating the topology:
  `sobolev_continuous : ∀ r, ∃ C s, 0 ≤ C ∧ ∀ φ, sobolevSeminorm r φ ≤ C·(s.sup 𝓢-seminorm) φ`
  and `seminorm_le_sobolev : ∀ k m, ∃ C r, 0 ≤ C ∧ ∀ φ, 𝓢.seminorm k m φ ≤ C·sobolevSeminorm r φ`.
* Nuclearity/HS input:
  `hermiteSobolev_hs_summable : ∀ q r, q + 1 ≤ r → Summable (fun j => (sobolevSeminorm q (hermiteSobolevVec r j))^2)`
  (sharp line `r > q + ½`; any integer gap `r ≥ q+1` is proved).

## Notes

* All constants are the honest values produced by the derivation; only the
  polynomial character matters downstream, and the predicted eigenvalue `n+1`,
  `O(√(n+1))` ladder coefficients, and Agmon exponent `1/4` were all confirmed.
* Mathlib supplied the Laplacian/`smulLeftCLM`/Schwartz integration-by-parts and
  the `L²`/`WithSeminorms` infrastructure; the oscillator theory, ladder and
  coefficient recurrences, Agmon bound, expansion, Sobolev chain, and the
  two-sided equivalence are new here.
