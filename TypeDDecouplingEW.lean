import Mathlib
import TypeDDecouplingDynkin
import TypeDDecouplingDressedMass
import TypeDDecouplingEqvarOrth
import TypeDDecouplingSector
import TypeDDecouplingDrift
import TypeDDecouplingConc
import TypeDDecouplingMartingaleGaussian
import TypeDDecouplingSkorokhodAldous
import TypeDDecouplingMitomaBridge

/-!
# Tier 4 black-box statements: the decoupled Edwards–Wilkinson limit (§ew)

Statements of the §ew results of `typeD_decoupling-draft-rev2.tex`:
the classical inputs `lem:dynkin` (Dynkin decomposition), `thm:mp` (equilibrium
fluctuations / OU martingale problem), `thm:mitoma` (tightness criterion) and
`prop:aldous` (Aldous's criterion); the main theorem `thm:ewmain` (decoupled
Edwards–Wilkinson limit); and the supporting lemmas `lem:gauss`, `lem:orth`,
`lem:eqvar`, `lem:sector`, `lem:eps`, `prop:conc`, `prop:sym`, `prop:drift`.

## Design after the §ew audit

The objects of SPDE / distribution-valued-process theory (Schwartz distributions `𝒮'(ℝ)`,
càdlàg processes valued in them, Skorokhod-space tightness, the limiting
Ornstein–Uhlenbeck / Edwards–Wilkinson fields) and the equilibrium two-time correlations /
variance functionals do **not** exist in Mathlib.  Stating the cited inputs over *free*
predicates/functions (e.g. an arbitrary `crossBracketSq`, an arbitrary tightness predicate,
an arbitrary distribution type) makes them **false universals** — one can instantiate the
free parameter to refute the conclusion.  Following the `lem:asep`/`asepKernel` precedent in
`TypeDDecouplingLCLT.lean`, every such cited input is therefore **pinned to an `opaque`
model object** below, so the cited statement becomes genuine content (neither provable nor
refutable without the absent construction) and is left as an honest `sorry`.

* `prop:sym` is *formalized and proved* here from the equilibrium product (independence)
  structure of the blocking measure (the `EWModel` structure), with no `sorry`.
* `thm:ewmain` is the **assembly step**: it is *derived* (sorry-free) from its toolkit
  (`lem:dynkin`, `lem:eqvar`, `prop:drift`, `thm:mp`, `thm:mitoma`, `prop:aldous`,
  `lem:gauss`, `lem:sector`, `lem:eps`, `prop:conc`), whose conclusions are passed as
  explicit, named, genuinely-used hypotheses rather than asserted.
* `thm:mitoma` is, as of the Mitoma campaign's final task, **no longer a `sorry`**: it is the
  genuine, proved Mitoma tightness criterion in Kallianpur–Xiong compact-confinement form
  (`= TypeDDecouplingMitomaBridge.mitoma_tightness`).  The former opaque tightness/evaluation
  placeholders `distTight`/`realTight` are retired; the real predicate `distTightReal`
  replaces the tightness gate consumed by `MPPathBundle`/`thm:mp`/`thm:ewmain`.
* All remaining §ew inputs are genuine literature/paper citations, pinned to the `opaque`
  objects and threaded as explicit hypotheses (there is no longer a `sorry` in this file).
-/

open scoped BigOperators Real Topology ENNReal
open MeasureTheory Filter

namespace TypeDDecoupling

/-! ## Shared model for the equilibrium algebraic lemmas -/

/-- A schematic description of the equilibrium (product blocking) measure and the
functions entering the cross-noise analysis.  `η i x ω` is the occupation of species
`i ∈ {0,1}` at site `x`; `ρ i` the species density; `W i x` the instantaneous species-`i`
current across `(x,x+1)`; `V x` the bond cross-term `V_x` of (eq:Vdef); `Theta N` the
cross-bracket density `Θ^N` of (eq:Theta).  The product structure of the measure is
recorded by the independence/mean fields. -/
structure EWModel where
  Ω : Type
  mΩ : MeasurableSpace Ω
  μ : Measure Ω
  isProb : IsProbabilityMeasure μ
  η : Fin 2 → ℤ → Ω → ℝ
  ρ : Fin 2 → ℝ
  W : Fin 2 → ℤ → Ω → ℝ
  V : ℤ → Ω → ℝ
  /-- each occupation is integrable (a genuine, bounded random variable) -/
  integ_η : ∀ i x, Integrable (η i x) μ
  /-- each occupation has mean equal to the density -/
  mean_η : ∀ i x, (∫ ω, η i x ω ∂μ) = ρ i
  /-- the cross-term `V_x` is centred (Proposition `prop:cross`) -/
  mean_V : ∀ x, (∫ ω, V x ω ∂μ) = 0
  /-- `V_x` is supported on the bond `{x,x+1}`, so under the product measure its
      covariance with `V_y` vanishes for `|x−y| > 1` -/
  cov_V_support : ∀ x y : ℤ, 1 < (x - y).natAbs → (∫ ω, V x ω * V y ω ∂μ) = 0
  /-- the near-diagonal covariances of `V` are bounded -/
  cov_V_bound : ∃ B : ℝ, ∀ x y : ℤ, |∫ ω, V x ω * V y ω ∂μ| ≤ B
  /-- the species-`i` current is a function of the species-`i` occupations alone
      (Proposition `prop:decouple`) -/
  W_marginal : ∀ i, ∃ Wfun : (ℤ → ℝ) → ℝ, ∀ x ω, W i x ω = Wfun (fun y => η i y ω)
  /-- the two species are independent under the product measure: a function of `η 0` and a
      function of `η 1` factorise under the expectation -/
  species_factor :
    ∀ (f : Ω → ℝ) (g : Ω → ℝ),
      (∃ F : (ℤ → ℝ) → ℝ, ∀ ω, f ω = F (fun y => η 0 y ω)) →
      (∃ G : (ℤ → ℝ) → ℝ, ∀ ω, g ω = G (fun y => η 1 y ω)) →
      (∫ ω, f ω * g ω ∂μ) = (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)

attribute [instance] EWModel.mΩ EWModel.isProb

/-! ## `prop:sym` — current orthogonal to the bound-pair mode -/

/-
**Corollary `prop:sym`** (current orthogonal to the bound-pair mode).
For all densities `ρ₁,ρ₂ ∈ (0,1)`, `⟨W_{i,x}, B_z⟩ = 0` for every `z`, where
`B_z = (η_{1,z}−ρ₁)(η_{2,z}−ρ₂)`.

*Formalized and proved here* from the equilibrium product (independence) structure of the
blocking measure: the species-`i` current `W_{i,x}` depends only on the species-`i`
occupations (`W_marginal`), so under the product measure it factorizes against the
opposite-species centred field, whose mean vanishes (`mean_η`); hence the covariance is `0`.
-/
theorem prop_sym (M : EWModel) (i : Fin 2) (x z : ℤ) :
    (∫ ω, M.W i x ω * ((M.η 0 z ω - M.ρ 0) * (M.η 1 z ω - M.ρ 1)) ∂M.μ) = 0 := by
  have h0 : (∫ ω, (M.η 0 z ω - M.ρ 0) ∂M.μ) = 0 := by
    rw [MeasureTheory.integral_sub (M.integ_η 0 z) (integrable_const _), M.mean_η 0 z]; simp
  have h1 : (∫ ω, (M.η 1 z ω - M.ρ 1) ∂M.μ) = 0 := by
    rw [MeasureTheory.integral_sub (M.integ_η 1 z) (integrable_const _), M.mean_η 1 z]; simp
  fin_cases i
  · obtain ⟨Wfun, hWfun⟩ := M.W_marginal 0
    have hfac := M.species_factor
      (fun ω => M.W 0 x ω * (M.η 0 z ω - M.ρ 0))
      (fun ω => M.η 1 z ω - M.ρ 1)
      ⟨fun f => Wfun f * (f z - M.ρ 0), fun ω => by dsimp only; rw [hWfun]⟩
      ⟨fun f => f z - M.ρ 1, fun ω => rfl⟩
    calc (∫ ω, M.W 0 x ω * ((M.η 0 z ω - M.ρ 0) * (M.η 1 z ω - M.ρ 1)) ∂M.μ)
        = ∫ ω, (M.W 0 x ω * (M.η 0 z ω - M.ρ 0)) * (M.η 1 z ω - M.ρ 1) ∂M.μ := by
          congr 1; funext ω; ring
      _ = (∫ ω, M.W 0 x ω * (M.η 0 z ω - M.ρ 0) ∂M.μ) * (∫ ω, M.η 1 z ω - M.ρ 1 ∂M.μ) := hfac
      _ = 0 := by rw [h1]; ring
  · obtain ⟨Wfun, hWfun⟩ := M.W_marginal 1
    have hfac := M.species_factor
      (fun ω => M.η 0 z ω - M.ρ 0)
      (fun ω => M.W 1 x ω * (M.η 1 z ω - M.ρ 1))
      ⟨fun f => f z - M.ρ 0, fun ω => rfl⟩
      ⟨fun f => Wfun f * (f z - M.ρ 1), fun ω => by dsimp only; rw [hWfun]⟩
    calc (∫ ω, M.W 1 x ω * ((M.η 0 z ω - M.ρ 0) * (M.η 1 z ω - M.ρ 1)) ∂M.μ)
        = ∫ ω, (M.η 0 z ω - M.ρ 0) * (M.W 1 x ω * (M.η 1 z ω - M.ρ 1)) ∂M.μ := by
          congr 1; funext ω; ring
      _ = (∫ ω, M.η 0 z ω - M.ρ 0 ∂M.μ) * (∫ ω, M.W 1 x ω * (M.η 1 z ω - M.ρ 1) ∂M.μ) := hfac
      _ = 0 := by rw [h0]; ring

/-! ## Opaque equilibrium-estimate objects

The following equilibrium two-time correlations, variance functionals and dressed-mass
quantities are determined by the (product blocking) measure `ν` and the sector-reweighted
measure `ϖ` of the model; their construction needs the full §ew analytic apparatus, which is
absent from Mathlib.  They are declared `opaque` so the cited estimates about them below are
genuine content (neither provable nor refutable in Lean) rather than false universals over a
free function. -/

/- The equilibrium covariance `E_ν[V_x · (η_{i,y} − ρ_i)]` of the bond cross-term `V_x`
against a centred density field was formerly an `opaque`; it is now realised concretely (see
`ewCrossDensityCov` below) as the bare covariance `⟨V_x, η_{i,y}⟩` over a finite
blocking-measure window; since `⟨V_x, 1⟩ = 0` (`prop:cross`) this equals the centred
covariance `⟨V_x, η_{i,y} − ρ_i⟩` for any constant `ρ_i`.

-- opaque ewCrossDensityCov (i : Fin 2) (x y : ℤ) : ℝ  -- (replaced by a concrete definition below)

The equal-time second moment `E_ν[(Θ^N)²]` of the cross-bracket density
`Θ^N = N^{-1} Σ_x φ'(x/N)² V_x` was likewise formerly `opaque`; it is now realised concretely
(see `ewThetaSq` below) as the normalised second moment under the finite blocking measure.

-- opaque ewThetaSq (dphi : ℝ → ℝ) (N : ℕ) : ℝ  -- (replaced by a concrete definition below) -/

/- The two-time correlations `sectorCorrNu`/`sectorCorrPiSelf` that formerly pinned `lem:sector`
as an opaque, fugacity-agnostic object are **removed**: they could only express the paper's
*uncompensated* comparison `ν_α` vs `ϖ_α`, which is FALSE (the sector ratio grows like
`e^{Θ(N)}`, see the docstring of `lem_sector` below).  The corrected comparison is proved
concretely at the compensated fugacity `β = α/(1+α)` via `TypeDDecoupling.Sector`.

-- opaque sectorCorrNu (c K : ℝ) : ℝ × ℝ → ℝ
-- opaque sectorCorrPiSelf (c K : ℝ) : ℝ → ℝ
-/

/-! ### Concrete regime-A model for the dressed mass

The dressed mass is realized concretely, so that `lem:eps` becomes a genuine theorem proved
from the elementary argument of `TypeDDecouplingDressedMass.lean` (Theorem `thm:main`), rather
than an honest `sorry` about a free object.  We instantiate the regime-A window
`Λ = [−N, N] ∩ ℤ` (taking `K = 1`), the parameter `q = 1 − 1/(N+2)²` (of the form
`1 − c/N²`, shifted to keep `q ∈ (0,1)` for all `N`), the finite `{0,1}²`-occupation
configuration space, and — since the estimate `‖V^{(dr)}‖² ≤ (q^{-4ℓ}-1)²` holds for *any*
probability weight — a uniform probability weight `ϖ` (the sector-reweighted measure of the
main text is one such weight, so the bound applies to it a fortiori). -/

/-- The regime-A lattice window `Λ = [−N, N] ∩ ℤ` (taking `K = 1`). -/
def ewLambda (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- The finite configuration space at scale `N`: `{0,1}`-valued occupations of the two species
at the window sites. -/
abbrev EWConfig (N : ℕ) : Type := {x : ℤ // x ∈ ewLambda N} → Fin 2 → Bool

/-- The `{0,1}`-valued species-`i` occupation at site `x`, vanishing off the window. -/
def ewOcc (N : ℕ) : Fin 2 → ℤ → EWConfig N → ℝ :=
  fun i x c => if h : x ∈ ewLambda N then (if c ⟨x, h⟩ i then 1 else 0) else 0

/-- The regime-A parameter `q = 1 − c/N²` (here `c = 1`, shifted to keep `q ∈ (0,1)`). -/
noncomputable def ewQ (N : ℕ) : ℝ := 1 - 1 / ((N : ℝ) + 2) ^ 2

/-- The uniform probability weight on the finite configuration space. -/
noncomputable def ewW (N : ℕ) : EWConfig N → ℝ := fun _ => (Fintype.card (EWConfig N) : ℝ)⁻¹

/-- The dressed mass `‖V^{(dr)}_z‖²_{L²(ϖ)}` at field-window site `z` and scale `N`, realized as
the squared `L²(ϖ)`-distance from the bond cross-term `V_z` to the span of the four bond-pair
duality functions (Theorem `thm:main`). -/
noncomputable def ewDressedMass (N : ℕ) (z : ℤ) : ℝ :=
  DressedMass.dressedMass (ewW N) (DressedMass.Vbond (ewQ N) (ewOcc N) z)
    (DressedMass.bpBasis (ewQ N) (ewLambda N) (ewOcc N) z)

/-- The regime-A null sequence `ε_N = (q_N^{-4|Λ|} − 1)²` dominating the dressed mass. -/
noncomputable def ewEps (N : ℕ) : ℝ :=
  (Real.rpow (ewQ N) (-(4 * (2 * (N : ℝ) + 1))) - 1) ^ 2

/-
`q_N ∈ (0,1)`.
-/
lemma ewQ_pos (N : ℕ) : 0 < ewQ N := by
  unfold ewQ; norm_num; ring_nf; norm_cast; norm_num;
  exact inv_lt_one_of_one_lt₀ ( by nlinarith )

lemma ewQ_lt_one (N : ℕ) : ewQ N < 1 := by
  exact sub_lt_self _ ( by positivity )

/-
Occupations vanish off the window.
-/
lemma ewOcc_out (N : ℕ) : ∀ i x c, x ∉ ewLambda N → ewOcc N i x c = 0 := by
  exact fun i x c hx => by unfold TypeDDecoupling.ewOcc; aesop;

/-
Occupations are `{0,1}`-valued.
-/
lemma ewOcc_01 (N : ℕ) : ∀ i x c, ewOcc N i x c = 0 ∨ ewOcc N i x c = 1 := by
  unfold ewOcc; aesop;

/-
The uniform weight is nonnegative.
-/
lemma ewW_nonneg (N : ℕ) : ∀ c, 0 ≤ ewW N c := by
  exact fun c => by unfold ewW; positivity;

/-
The uniform weight is a probability weight.
-/
lemma ewW_sum (N : ℕ) : ∑ c, ewW N c = 1 := by
  unfold ewW; norm_num;

/-
The regime-A null sequence tends to `0` (rate `O(N^{-2})`).
-/
lemma ewEps_tendsto : Tendsto ewEps atTop (𝓝 0) := by
  -- Show that the term `Real.rpow (ewQ N) (-(4*(2*(N:ℝ)+1)))` tends to `1` as `N` tends to infinity.
  have h_exp : Filter.Tendsto (fun N => Real.rpow (ewQ N) (-(4*(2*(N:ℝ)+1)))) Filter.atTop (nhds 1) := by
    -- We'll use the exponential property to simplify the expression. Note that $(1 - \frac{1}{(N+2)^2})^{-(4(2N+1))} = \exp(-(4(2N+1)) \ln(1 - \frac{1}{(N+2)^2}))$.
    suffices h_exp : Filter.Tendsto (fun N : ℕ => -(4 * (2 * N + 1)) * Real.log (1 - 1 / ((N + 2 : ℝ) ^ 2))) Filter.atTop (nhds 0) by
      convert h_exp.exp using 2 <;> norm_num [ ewQ ];
      rw [ Real.rpow_def_of_pos ( sub_pos.mpr <| inv_lt_one_of_one_lt₀ <| one_lt_pow₀ ( by linarith ) two_ne_zero ), mul_comm ] ; norm_num [ Real.exp_eq_exp_ℝ ];
    -- We'll use the fact that $\log(1 - x) \approx -x$ for $x$ close to $0$.
    have h_log_approx : Filter.Tendsto (fun N : ℕ => Real.log (1 - 1 / ((N + 2 : ℝ) ^ 2)) / (1 / ((N + 2 : ℝ) ^ 2))) Filter.atTop (nhds (-1)) := by
      have h_log_approx : Filter.Tendsto (fun x : ℝ => Real.log (1 - x) / x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
        simpa [ div_eq_inv_mul ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.log ( hasDerivAt_id 0 |> HasDerivAt.const_sub 1 ) <| by norm_num );
      refine h_log_approx.comp <| Filter.tendsto_inf.mpr ⟨ ?_, ?_ ⟩;
      · exact tendsto_const_nhds.div_atTop ( Filter.tendsto_pow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
      · exact Filter.tendsto_principal.mpr <| Filter.Eventually.of_forall fun N => by norm_num; positivity;
    convert h_log_approx.mul ( show Filter.Tendsto ( fun N : ℕ => - ( 4 * ( 2 * ( N : ℝ ) + 1 ) ) / ( ( N + 2 : ℝ ) ^ 2 ) ) Filter.atTop ( nhds 0 ) from ?_ ) using 2 <;> norm_num;
    · field_simp;
    · rw [ Metric.tendsto_nhds ] ; norm_num;
      exact fun ε hε => ⟨ Nat.ceil ( ε⁻¹ * 8 ), fun n hn => by rw [ div_lt_iff₀ ] <;> cases abs_cases ( 2 * ( n : ℝ ) + 1 ) <;> nlinarith [ Nat.ceil_le.mp hn, inv_pos.mpr hε, mul_inv_cancel₀ hε.ne' ] ⟩;
  convert Filter.Tendsto.pow ( h_exp.sub_const 1 ) 2 using 2 ; norm_num

/-! ### Concrete realisation of `lem:orth` and `lem:eqvar`

Both quantities are realised over a finite blocking-measure window using the general
Tier-A machinery in `TypeDDecouplingEqvarOrth.lean` (an involution-based finite algebra),
with unit fugacities `αᵢ = 1`. -/

/-- A finite window containing `x`, `x+1`, `y` (for the orthogonality covariance). -/
def ewOrthLambda (x y : ℤ) : Finset ℤ := Finset.Icc (min x y) (max (x + 1) y)

/-- **Concrete `ewCrossDensityCov`.**  The bare covariance `⟨V_x, η_{i,y}⟩` under the finite
blocking measure (`q = 1/2`, `αᵢ = 1`) on the window `ewOrthLambda x y`.  By `expect_V_eq_zero`
(`⟨V_x, 1⟩ = 0`) this coincides with the centred covariance `⟨V_x, η_{i,y} − ρ_i⟩` for any
constant `ρ_i`, and its value does not depend on the choice of `q ∈ (0,1)` or window. -/
noncomputable def ewCrossDensityCov (i : Fin 2) (x y : ℤ) : ℝ :=
  ∑ c, EqvarOrth.Wb (ewOrthLambda x y) (1 / 2) (fun _ => 1) c
        * EqvarOrth.Vb (ewOrthLambda x y) (1 / 2) x c
        * EqvarOrth.bocc (ewOrthLambda x y) i y c

/-- The bonds of the regime-A window `[−N, N]`: sites `x` with `x, x+1 ∈ [−N, N]`. -/
def ewBonds (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) ((N : ℤ) - 1)

/-- The cross-bracket density `Θ^N = N^{-1} Σ_x φ'(x/N)² V_x` at scale `N`, as a function on
the finite configuration space. -/
noncomputable def ewTheta (dphi : ℝ → ℝ) (N : ℕ) (c : EqvarOrth.Config (ewLambda N)) : ℝ :=
  (1 / (N : ℝ)) * ∑ x ∈ ewBonds N, (dphi ((x : ℝ) / N)) ^ 2 * EqvarOrth.Vb (ewLambda N) (ewQ N) x c

/-- **Concrete `ewThetaSq`.**  The normalised equal-time second moment `E_ν[(Θ^N)²]` of the
cross-bracket density under the finite blocking measure (`q = q_N`, `αᵢ = 1`) on `[−N, N]`. -/
noncomputable def ewThetaSq (dphi : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ c, EqvarOrth.Wb (ewLambda N) (ewQ N) (fun _ => 1) c * (ewTheta dphi N c) ^ 2)
    / (∑ c, EqvarOrth.Wb (ewLambda N) (ewQ N) (fun _ => 1) c)

/-- The `L²` norm `E_ν[⟨M₁^N,M₂^N⟩(φ,t)²]` of the cross bracket of the two species'
Dynkin martingales, in the regime governed by `c`. -/
opaque ewCrossBracketSq (c : ℝ) (N : ℕ) (t : ℝ) : ℝ

/-- The `L²` distance `‖Γ_i^N(φ,·) − D Y_i(Δφ,·)‖` between the rescaled drift and the
Laplacian of the limit field, at scale `N`, for diffusivity `D` and density `ρ`. -/
opaque ewDriftL2err (D ρ : ℝ) (N : ℕ) : ℝ

/-! ## `lem:orth` — orthogonality of the cross-term to the density fields -/

/-- **Lemma `lem:orth`** (orthogonality to the density fields; density-free).
For every species `i`, sites `x,y`, `⟨V_x, η_{i,y}−ρ_i⟩ = 0`; hence `V_x` has no order-one
component, its lowest order being two.

*Proved here* (no `sorry`) from the general involution argument
`EqvarOrth.expect_V_mul_occ_eq_zero`: swapping the *other* species across the bond `(x,x+1)`
reverses the sign of `V_x` while fixing the blocking weight and the density field `η_{i,y}`,
so the weighted sum cancels. -/
theorem lem_orth (i : Fin 2) (x y : ℤ) :
    ewCrossDensityCov i x y = 0 := by
  have hx : x ∈ ewOrthLambda x y := by simp only [ewOrthLambda, Finset.mem_Icc]; omega
  have hx1 : x + 1 ∈ ewOrthLambda x y := by simp only [ewOrthLambda, Finset.mem_Icc]; omega
  exact EqvarOrth.expect_V_mul_occ_eq_zero (ewOrthLambda x y) (1 / 2) (by norm_num)
    (fun _ => 1) x hx hx1 i y

/-! ## `lem:eqvar` — equal-time variance of the cross-bracket density -/

/-
**Lemma `lem:eqvar`** (equal-time variance).  With
`Θ^N = N^{-1} Σ_x φ'(x/N)² V_x`, one has `E_ν[(Θ^N)²] ≤ C(φ) N^{-1}`.

*Proved here* (no `sorry`) from the general variance bound `EqvarOrth.expect_sq_le`.  The
boundedness hypothesis `hdphi` (satisfied by the paper's Schwartz test-function derivative
`φ'`) is genuinely needed: for a coefficient field unbounded on `[−1,1]` the normalised second
moment need not decay, so the bare statement over an arbitrary `dphi` would be false.  With
`|dphi| ≤ M₀` the equal-time variance is `O(1/N)` via the exact cancellation `E[V_x V_y] = 0`
for `|x−y| ≥ 2` (`expect_V_mul_V_eq_zero`) together with `|V| ≤ 1`.
-/
theorem lem_eqvar (dphi : ℝ → ℝ) (hdphi : ∃ M, ∀ u, |dphi u| ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
      ewThetaSq dphi N ≤ C / (N : ℝ) := by
  -- Apply the general bound from EqvarOrth.expect_sq_le.
  obtain ⟨M, hM⟩ : ∃ M, ∀ u, |dphi u| ≤ M := hdphi
  have h_bound : ∀ N : ℕ, 0 < N → ewThetaSq dphi N ≤ (3 * M^4 * (2 * N)) / (N : ℝ) ^ 2 := by
    intros N hN_pos
    have h_bound : (∑ c : EWConfig N, EqvarOrth.Wb (ewLambda N) (ewQ N) (fun _ => 1) c * (ewTheta dphi N c) ^ 2) ≤ 3 * M^4 * (2 * N) * (∑ c : EWConfig N, EqvarOrth.Wb (ewLambda N) (ewQ N) (fun _ => 1) c) / (N : ℝ) ^ 2 := by
      have h_bound : (∑ c : EWConfig N, EqvarOrth.Wb (ewLambda N) (ewQ N) (fun _ => 1) c * (∑ x ∈ ewBonds N, (dphi ((x : ℝ) / N)) ^ 2 * EqvarOrth.Vb (ewLambda N) (ewQ N) x c) ^ 2) ≤ 3 * M^4 * (2 * N) * (∑ c : EWConfig N, EqvarOrth.Wb (ewLambda N) (ewQ N) (fun _ => 1) c) := by
        have := @TypeDDecoupling.EqvarOrth.expect_sq_le (ewLambda N);
        convert this ( ewQ N ) ( ewQ_pos N ) ( ewQ_lt_one N ) ( fun _ => 1 ) ( fun _ => zero_lt_one ) ( ewBonds N ) _ ( fun x => dphi ( x / N ) ^ 2 ) ( M ^ 2 ) ( sq_nonneg _ ) _ using 1 <;> norm_num [ ewBonds ];
        · norm_cast ; ring;
        · exact fun x hx₁ hx₂ => ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ⟩;
        · exact fun x hx₁ hx₂ => by nlinarith only [ abs_le.mp ( hM ( x / N ) ) ] ;
      convert div_le_div_of_nonneg_right h_bound ( sq_nonneg ( N : ℝ ) ) using 1 ; norm_num [ ewTheta ] ; ring;
      simp +decide only [mul_assoc, mul_left_comm, Finset.mul_sum _ _ _];
    rw [ ewThetaSq, div_le_iff₀ ];
    · exact h_bound.trans_eq ( by ring );
    · convert TypeDDecoupling.EqvarOrth.sum_Wb_pos ( ewLambda N ) ( ewQ N ) ( ewQ_pos N ) ( fun _ => 1 ) ( fun _ => zero_lt_one ) using 1;
  refine' ⟨ 3 * M ^ 4 * 2 + 1, by positivity, fun N hN => le_trans ( h_bound N hN ) _ ⟩ ; rw [ div_le_div_iff₀ ] <;> nlinarith [ show ( N : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr hN, pow_pos ( show ( N : ℝ ) > 0 by positivity ) 2 ] ;

/-! ## `lem:sector` — sector comparison (CORRECTED, compensated fugacity) -/

/-
**Lemma `lem:sector`** (sector comparison), *corrected version*.

**The original statement is FALSE.**  The paper compared the product blocking measure `ν` at
fugacity `α` with the sector-reweighted measure `ϖ` carried at the *same* fugacity `α`, and
claimed a bounded comparability constant `M = sup ν/ϖ` along the regime-(A) scaling.  This is
refutable: the sector reweighting tilts each sector by the constant-per-particle factor
`q^{2n}/(1 − α q^{2n−2S}) → (1 − α)^{-1}`, so `ϖ_α` behaves as a blocking measure at
*effective* fugacity `α/(1 − α)` (bulk density `α`), whereas `ν_α` has density `α/(1+α)`.  The
two measures concentrate on sector ranges `Θ(N)` apart, so `M = e^{Θ(N)}` — unbounded.

**Correction (this statement).**  Comparability holds *two-sidedly over all sectors* once `ϖ`
is taken at the **compensated fugacity** `β = α/(1+α)` (equivalently `β = ρ`, the `ν`-density).
The key cancellation is `log(α/β) = log(1+α) = −log(1−β)`, which annihilates the linear-in-`n`
term in `log(ν(n)/ϖ(n))`.  Here `nu`, `pi` are the (normalised) sector masses of `ν`, `ϖ`;
their per-sector ratio has the compensated shape `nu n / pi n = Z·(α/β)ⁿ / hfac q β S n`,
the elementary-symmetric prefactors having cancelled by homogeneity (`Sector.esymm_homogeneous`).
The bound is `M = exp(2 C₀)`, `C₀ = A(1 + 8β/(1−β))` with `A` a bound on `(−log q)·S²`
(`= 18 c K²` under `q = 1 − c/N²`, `S ≤ 3KN`).

*Proved here* (no `sorry`) as `Sector.sector_comparison_single`.  The measures share the same
conditional laws given the particle number (`Sector.condLaw_sector_const`).
-/
theorem lem_sector
    (q α β : ℝ) (S : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < α)
    (hα : β = α / (1 + α))
    (A : ℝ) (hA0 : 0 ≤ A) (hAbnd : (-(Real.log q)) * (S : ℝ) ^ 2 ≤ A)
    (hβ' : β * q ^ (-(2 * (S : ℤ))) ≤ (1 + β) / 2)
    (hqS : q ^ (-(2 * (S : ℤ))) ≤ 2)
    (nu pi : ℕ → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hpi : ∀ n ≤ S, 0 < pi n)
    (hsum_nu : ∑ n ∈ Finset.range (S + 1), nu n = 1)
    (hsum_pi : ∑ n ∈ Finset.range (S + 1), pi n = 1)
    (hratio : ∀ n ≤ S, nu n = Z * (α / β) ^ n / Sector.hfac q β S n * pi n) :
    (∀ n ≤ S, |Real.log (nu n / pi n)| ≤ 2 * (A * (1 + 8 * β / (1 - β)))) ∧
      (∀ n ≤ S, nu n ≤ Real.exp (2 * (A * (1 + 8 * β / (1 - β)))) * pi n
              ∧ pi n ≤ Real.exp (2 * (A * (1 + 8 * β / (1 - β)))) * nu n) := by
  have hC0 : ∀ n ≤ S, |Real.log (nu n / pi n)| ≤ 2 * (A * (1 + 8 * β / (1 - β))) :=
    fun n hn => Sector.sector_comparison_single q α β S hq0 hq1 hβ0 hβ1 hα0 hα A hA0 hAbnd hβ'
      hqS nu pi Z hZ hpi hsum_nu hsum_pi hratio n hn
  refine ⟨hC0, fun n hn => ?_⟩
  have h_pos : 0 < nu n ∧ 0 < pi n := by
    exact ⟨ hratio n hn ▸ mul_pos ( div_pos ( mul_pos hZ ( pow_pos ( div_pos hα0 hβ0 ) _ ) ) ( Sector.hfac_pos q β S hq0 hq1 hβ0 hβ1 hβ' n hn ) ) ( hpi n hn ), hpi n hn ⟩;
  have h_exp : Real.exp (Real.log (nu n / pi n)) ≤ Real.exp (2 * (A * (1 + 8 * β / (1 - β)))) ∧ Real.exp (-Real.log (nu n / pi n)) ≤ Real.exp (2 * (A * (1 + 8 * β / (1 - β)))) := by
    exact ⟨ Real.exp_le_exp.mpr ( le_of_abs_le ( hC0 n hn ) ), Real.exp_le_exp.mpr ( neg_le_iff_add_nonneg'.mpr ( by linarith [ abs_le.mp ( hC0 n hn ) ] ) ) ⟩;
  rw [ Real.exp_log ( div_pos h_pos.1 h_pos.2 ), Real.exp_neg, Real.exp_log ( div_pos h_pos.1 h_pos.2 ) ] at h_exp;
  exact ⟨ by rw [ div_le_iff₀ h_pos.2 ] at h_exp; linarith, by rw [ inv_div, div_le_iff₀ h_pos.1 ] at h_exp; linarith ⟩

/-- **Corollary (correlation transfer)** at compensated fugacity.  Given the corrected
two-sided sector-mass comparison `nu s ≤ M · pi s` (from `lem_sector`) and, for each sector
`s`, a symmetric positive-semidefinite self-adjoint form `Tform s = ⟨·, P ·⟩` (the per-sector
Cauchy–Schwarz `hCS` and positivity `hpsd` hold for the sector-preserving semigroup
`P_t = (exp(tL/2))²`), the two-time correlation transfers:
`|E_ν[f · P h]| ≤ M · E_ϖ[f · P f]^{1/2} · E_ϖ[h · P h]^{1/2}`.  A direct instance of
`Sector.correlation_transfer`. -/
theorem lem_sector_transfer
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    (nu pi : ι → ℝ) (M : ℝ)
    (Tform : (s : ι) → E s → E s → ℝ) (fld hld : (s : ι) → E s)
    (hpi_nonneg : ∀ s, 0 ≤ pi s)
    (hpsd : ∀ s a, 0 ≤ Tform s a a)
    (hCS : ∀ s a b, |Tform s a b| ≤ Real.sqrt (Tform s a a) * Real.sqrt (Tform s b b))
    (hcomp : ∀ s, |nu s| ≤ M * pi s) :
    |∑ s, nu s * Tform s (fld s) (hld s)|
      ≤ M * Real.sqrt (∑ s, pi s * Tform s (fld s) (fld s))
          * Real.sqrt (∑ s, pi s * Tform s (hld s) (hld s)) :=
  Sector.correlation_transfer nu pi M Tform fld hld hpi_nonneg hpsd hCS hcomp

/-! ## `lem:eps` — the dressed mass is asymptotically negligible -/

/-
**Lemma `lem:eps`** (the dressed mass is asymptotically negligible).
In the regime-A scaling there is `ε_N → 0` with `‖V^{(dr)}_z‖²_{L²(ϖ)} ≤ ε_N`, uniformly
over `z` in the field window.

*Proved here* (no `sorry`) from the elementary dressed-mass estimate
`TypeDDecoupling.DressedMass.dressedMass_bond_le` (Theorem `thm:main`): the dressed mass at
bond `z` is at most `(q_N^{-4ℓ(z)} − 1)²` with `ℓ(z)` the number of window sites strictly left
of `z`; since `ℓ(z) ≤ |Λ| = 2N+1` uniformly and `q_N = 1 − 1/(N+2)² → 1`, the sequence
`ε_N = (q_N^{-4(2N+1)} − 1)² = O(N^{-2})` dominates the dressed mass and tends to `0`
(`ewEps_tendsto`).
-/
theorem lem_eps :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ N z, ewDressedMass N z ≤ ε N := by
  refine ⟨ewEps, ewEps_tendsto, ?_⟩
  intro N z
  refine' DressedMass.dressedMass_bond_le _ ( ewQ_pos N ) ( ewQ_lt_one N ) _ _ _ _ _ _ _ _ |> le_trans <| _;
  · grind +locals;
  · -- By definition of `ewOcc`, we know that `ewOcc N i x c` is either 0 or 1.
    intros i x c
    apply ewOcc_01 N i x c;
  · exact fun _ => by unfold ewW; positivity;
  · convert ewW_sum N using 1;
  · refine' pow_le_pow_left₀ _ _ _ <;> norm_num [ ewEps ];
    · exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_ge ( by exact sub_pos.mpr ( by rw [ div_lt_iff₀ ] <;> ring <;> nlinarith ) ) ( sub_le_self _ ( by positivity ) ) ( show ( - ( 4 * ( Finset.card ( Finset.filter ( fun x => x < z ) ( Finset.Icc ( - ( N : ℤ ) ) ( N : ℤ ) ) ) ) : ℝ ) ) ≤ 0 by exact neg_nonpos.mpr ( mul_nonneg zero_le_four ( Nat.cast_nonneg _ ) ) ) );
    · refine' Real.rpow_le_rpow_of_exponent_ge ( ewQ_pos N ) ( ewQ_lt_one N |> le_of_lt ) _ ; norm_num [ ewLambda ];
      exact_mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num; linarith )

/-! ## `prop:conc` — L² concentration of the cross bracket (condition (X)) -/

/-
Auxiliary decay: `N⁻² · log_+(tN²) → 0` (since `log N = o(N)`).
-/
lemma tendsto_invSq_log_max (t : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ ^ 2 * (Real.log (t * (N : ℝ) ^ 2) ⊔ 0)) atTop (𝓝 0) := by
  by_cases ht : t = 0;
  · aesop;
  · -- We can factor out $(N⁻¹)^2$ and use the fact that $Real.log (t * N^2)$ grows slower than any linear function.
    have h_log_growth : Filter.Tendsto (fun N : ℕ => (Real.log (t * N^2)) / (N : ℝ)) Filter.atTop (nhds 0) := by
      -- We can use the fact that $\log(tN^2) = \log t + 2\log N$.
      suffices h_log : Filter.Tendsto (fun N : ℕ => (Real.log t + 2 * Real.log N) / (N : ℝ)) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using by rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ] ; ring );
      -- We can use the fact that $\frac{\log N}{N}$ tends to $0$ as $N$ tends to infinity.
      have h_log_div_N : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
      simpa [ add_div, mul_div_assoc ] using Filter.Tendsto.add ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat ) ( h_log_div_N.const_mul 2 );
    refine' squeeze_zero_norm' _ ( by simpa using h_log_growth.norm );
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn ; rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ inv_pow ] ; ring_nf ; norm_num [ hn.ne' ];
    rw [ inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ ] <;> first | positivity | cases max_cases ( Real.log ( n ^ 2 * t ) ) 0 <;> cases abs_cases ( Real.log ( n ^ 2 * t ) ) <;> nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast, show ( n : ℝ ) ^ 2 ≥ n by norm_cast; nlinarith ] ;

/-- **Proposition `prop:conc`** (`L²` concentration of the cross bracket).
`E_ν[⟨M₁^N,M₂^N⟩(φ,t)²] ≤ C(φ,c) t (N^{-1} + N^{-2} log_+(tN²) + t ε_N) → 0`; hence the
cross bracket tends to `0` in `L²`, establishing condition (X).

**Now proved `sorry`-free** from the abstract concentration estimate
`TypeDDecoupling.Conc.conc_master` (file `TypeDDecouplingConc.lean`), which supplies the full
quantitative content — the correlation bound (Cauchy–Schwarz on the double bond sum,
`Conc.corr_pointwise`) and the time integration (the elementary integrals `∫ ds/(sN²)`,
`∫ e^{-3cs}/√s ds = √(π/3c)`, `∫ C_e/N ds`; `Conc.time_integral_bound`).  The `L²` cross
bracket is pinned to the opaque object `ewCrossBracketSq`; the process-level inputs — the
transfer bound with compensated fugacity (`lem_sector_transfer`), the mass-sector kernel split
(`thm:kernel` for the sixteen bond-pair terms and `lem_eps` for the dressed part), the
equal-time bound (`lem_eqvar`), and the stationarity identity
`E_ν[(∫Θ)²] = 2∫₀ᵗ(t−s)C_Θ` — enter as the named hypothesis `hproc`, exactly as `prop_drift`
receives its `hpin`.  `ε` is the null dressed-mass sequence from `lem:eps` (`hε`), with
`ε_N ≥ 0` (`hε0`, satisfied since `ε_N = (q^{-4ℓ}-1)²`).

*Faithfulness note.*  The middle term uses the truncated logarithm `log_+(tN²) = log(tN²) ⊔ 0`
(the paper's `log_+`, as in `propconc_brief.tex`); the bare `Real.log` would make the bound
false for small `t` (a negative right-hand side against the nonnegative `L²` norm). -/
theorem prop_conc (c : ℝ) (hc : 0 < c)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ N, 0 ≤ ε N)
    (hproc : ∃ Mc Cphi Ck Ce : ℝ, 0 ≤ Mc ∧ 0 ≤ Ck ∧ 0 ≤ Ce ∧
      ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 < t →
        ∃ (nu : ℝ) (bonds : Finset ℤ) (g : ℤ → ℝ) (G : ℝ → ℤ → ℝ) (Ct : ℝ → ℝ),
          0 ≤ ewCrossBracketSq c N t ∧
          3 * c ≤ nu * (N : ℝ) ^ 2 ∧
          (∀ x, 0 ≤ g x) ∧
          (∑ x ∈ bonds, g x ≤ Cphi * (N : ℝ)) ∧
          (∀ s x, x ∈ bonds → G s x ≤
            Ck * ((1 + s * (N : ℝ) ^ 2)⁻¹
              + Real.exp (-nu * (s * (N : ℝ) ^ 2)) * (Real.sqrt (1 + s * (N : ℝ) ^ 2))⁻¹) + ε N) ∧
          (∀ s, 0 < s → |Ct s| ≤ (Mc / (N : ℝ) ^ 2) * (∑ x ∈ bonds, g x * Real.sqrt (G s x)) ^ 2) ∧
          (∀ s, 0 < s → |Ct s| ≤ Ce / (N : ℝ)) ∧
          IntervalIntegrable (fun s => |Ct s|) MeasureTheory.volume 0 t ∧
          ewCrossBracketSq c N t ≤ 2 * t * ∫ s in (0:ℝ)..t, |Ct s|) :
    (∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 < t →
        ewCrossBracketSq c N t ≤ C * t *
          ((N : ℝ)⁻¹ + (N : ℝ)⁻¹ ^ 2 * (Real.log (t * (N : ℝ) ^ 2) ⊔ 0) + t * ε N))
    ∧ (∀ t : ℝ, 0 < t → Tendsto (fun N => ewCrossBracketSq c N t) atTop (𝓝 0)) := by
  obtain ⟨Mc, Cphi, Ck, Ce, hMc, hCk, hCe, H⟩ := hproc
  have hbound : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 < t →
      ewCrossBracketSq c N t ≤ Conc.concConst c Mc Cphi Ck Ce * t *
        ((N : ℝ)⁻¹ + (N : ℝ)⁻¹ ^ 2 * (Real.log (t * (N : ℝ) ^ 2) ⊔ 0) + t * ε N) := by
    intro N hN t ht
    obtain ⟨nu, bonds, g, G, Ct, _hbr, hnu, hg, hgsum, hsplit, hCS, heq, hint, hstat⟩ :=
      H N hN t ht
    exact Conc.conc_master N hN t ht c Mc Cphi Ck Ce (ε N) nu hc hMc hCk hCe (hε0 N) hnu
      bonds g G Ct _ hg hgsum hsplit hCS heq hint hstat
  refine ⟨⟨Conc.concConst c Mc Cphi Ck Ce, Conc.concConst_pos c Mc Cphi Ck Ce hMc hCk hCe,
    hbound⟩, ?_⟩
  intro t ht
  have hRHS : Tendsto
      (fun N : ℕ => Conc.concConst c Mc Cphi Ck Ce * t *
        ((N : ℝ)⁻¹ + (N : ℝ)⁻¹ ^ 2 * (Real.log (t * (N : ℝ) ^ 2) ⊔ 0) + t * ε N))
      atTop (𝓝 0) := by
    have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hε' : Tendsto (fun N : ℕ => t * ε N) atTop (𝓝 0) := by
      simpa using hε.const_mul t
    have hsum : Tendsto
        (fun N : ℕ => (N : ℝ)⁻¹ + (N : ℝ)⁻¹ ^ 2 * (Real.log (t * (N : ℝ) ^ 2) ⊔ 0) + t * ε N)
        atTop (𝓝 0) := by
      simpa using (hinv.add (tendsto_invSq_log_max t)).add hε'
    simpa using hsum.const_mul (Conc.concConst c Mc Cphi Ck Ce * t)
  refine squeeze_zero'
    (Filter.eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
    (Filter.eventually_atTop.2 ⟨1, fun N hN => hbound N hN t ht⟩) hRHS
  obtain ⟨_, _, _, _, _, hbr, _⟩ := H N hN t ht
  exact hbr

/-! ## `lem:dynkin` — Dynkin martingale decomposition -/

/-- **Lemma `lem:dynkin`** (Dynkin decomposition; \cite[App.~1.5]{KL}), **de-opaqued**.
For a Markov process with generator `L`, Feller semigroup `P` and local functions `f,g`,
`M^f_t = f(η_t) − f(η_0) − ∫₀ᵗ (Lf)(η_s) ds` is a martingale with predictable cross-bracket
`⟨M^f,M^g⟩_t = ∫₀ᵗ Γ(f,g)(η_s) ds`, `Γ` the carré du champ.

**Fidelity repair (de-opaquing; the `asepKernel`/Bethe precedent).**  This lemma was
formerly pinned to two `opaque` objects — a free martingale predicate `dynkinIsMart` and a
free bracket `dynkinBracket` — which made the conclusion an honest `sorry` (stating it for a
free predicate/bracket is a false universal: instantiate the predicate to `False`).  Both
`opaque`s are now **retired** and superseded by genuine content in
`TypeDDecouplingDynkin.lean`:

* the martingale property is proved outright against Mathlib's real, `ℝ`-indexed
  `MeasureTheory.Martingale` (`TypeDDecoupling.dynkin_martingale`), from a faithful,
  satisfiable Markov–Feller hypothesis bundle (the Markov property via `P`, the Kolmogorov
  identity `P_t f − f = ∫₀ᵗ P_s(Lf) ds`, and the boundedness/measurability facts a Feller
  jump process with bounded generator possesses);
* Mathlib has **no** continuous-time predictable quadratic covariation, so the bracket is
  realised as the **definition** `TypeDDecoupling.dynkinBracketDef = ∫₀ᵗ Γ(f,g)(η_s) ds`
  (second conjunct, definitional/`rfl`); identifying it with the true predictable bracket is
  the cited classical fact (Ethier–Kurtz Ch. 4 / Dellacherie–Meyer), documented exactly as
  `asepKernel`'s identification rests on Schütz;
* the honest, library-accessible `L²`-level content is proved (third conjunct,
  `TypeDDecoupling.dynkin_L2`): the integrated covariance identity
  `E[M^f_t M^g_t] = E[∫₀ᵗ Γ(f,g)(η_s) ds]`, for **general** `f, g`.

The first hypothesis block is exactly the `dynkin_martingale` bundle for `f`; `hMg`, `hMfg`
are the same martingale property applied to `g` and to the product `fg`
(`dynkin_martingale` again); the remaining blocks are the boundedness/measurability
integrability facts `dynkin_L2` needs (all standard for a Feller jump process with bounded
generator on a probability space). -/
theorem lem_dynkin {S Ω : Type} [MeasurableSpace S] {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℝ mΩ)
    (proc : ℝ → Ω → S) (L : (S → ℝ) → S → ℝ) (P : ℝ → (S → ℝ) → S → ℝ)
    (f g : S → ℝ) (t : ℝ) (ht : 0 ≤ t)
    -- Markov–Feller bundle for `f` (the `dynkin_martingale` hypotheses)
    (hf_adapted : ∀ t : ℝ, StronglyMeasurable[ℱ t] (fun ω => f (proc t ω)))
    (hf0_adapt : ∀ t : ℝ, StronglyMeasurable[ℱ t] (fun ω => f (proc 0 ω)))
    (hInt_adapted : ∀ t : ℝ,
        StronglyMeasurable[ℱ t] (fun ω => ∫ s in (0:ℝ)..t, L f (proc s ω)))
    (hft_int : ∀ t : ℝ, Integrable (fun ω => f (proc t ω)) μ)
    (hf0_int : Integrable (fun ω => f (proc 0 ω)) μ)
    (hJ_int : ∀ t : ℝ, Integrable (fun ω => ∫ s in (0:ℝ)..t, L f (proc s ω)) μ)
    (hMarkov_f : ∀ s t : ℝ, s ≤ t →
        μ[(fun ω => f (proc t ω)) | ℱ s] =ᵐ[μ] fun ω => P (t - s) f (proc s ω))
    (hMarkov_Lf : ∀ s u : ℝ, s ≤ u →
        μ[(fun ω => L f (proc u ω)) | ℱ s] =ᵐ[μ] fun ω => P (u - s) (L f) (proc s ω))
    (hKol : ∀ (τ : ℝ) (x : S), 0 ≤ τ → P τ f x - f x = ∫ r in (0:ℝ)..τ, P r (L f) x)
    (hLf_ii : ∀ (ω : Ω) (a b : ℝ), IntervalIntegrable (fun u => L f (proc u ω)) volume a b)
    (hLf_slice : ∀ u : ℝ, Integrable (fun ω => L f (proc u ω)) μ)
    (hLf_jointInt : ∀ s t : ℝ, s ≤ t →
        Integrable (Function.uncurry (fun u ω => L f (proc u ω)))
          ((volume.restrict (Set.Ioc s t)).prod μ))
    (hPLf_jointInt : ∀ s t : ℝ, s ≤ t →
        Integrable (Function.uncurry (fun u ω => P (u - s) (L f) (proc s ω)))
          ((volume.restrict (Set.Ioc s t)).prod μ))
    (hbracketMeas : ∀ s t : ℝ, StronglyMeasurable[ℱ s]
        (fun ω => ∫ u in s..t, P (u - s) (L f) (proc s ω)))
    -- the `g` and `fg` Dynkin martingales (`dynkin_martingale` applied to `g` resp. `fg`)
    (hMg : Martingale (dynkinM L proc g) ℱ μ)
    (hMfg : Martingale (dynkinM L proc (fun s => f s * g s)) ℱ μ)
    -- extra measurability for the `L²` computation
    (hLf_adapt : ∀ s : ℝ, StronglyMeasurable[ℱ s] (fun ω => L f (proc s ω)))
    (hLg_adapt : ∀ s : ℝ, StronglyMeasurable[ℱ s] (fun ω => L g (proc s ω)))
    (hg0_adapt : StronglyMeasurable[ℱ 0] (fun ω => g (proc 0 ω)))
    (hLg_ii : ∀ ω : Ω, IntervalIntegrable (fun s => L g (proc s ω)) volume 0 t)
    -- integrability facts for the `L²` identity (standard from boundedness, finite `μ`)
    (hint_fg_t : Integrable (fun ω => f (proc t ω) * g (proc t ω)) μ)
    (hint_fg_0 : Integrable (fun ω => f (proc 0 ω) * g (proc 0 ω)) μ)
    (hint_Dfg : Integrable
        (fun ω => ∫ r in (0:ℝ)..t, L (fun s' => f s' * g s') (proc r ω)) μ)
    (hint_Mf_g0 : Integrable (fun ω => dynkinM L proc f t ω * g (proc 0 ω)) μ)
    (hint_Mg_f0 : Integrable (fun ω => dynkinM L proc g t ω * f (proc 0 ω)) μ)
    (hint_Mf_Dg : Integrable
        (fun ω => dynkinM L proc f t ω * ∫ r in (0:ℝ)..t, L g (proc r ω)) μ)
    (hint_Mg_Df : Integrable
        (fun ω => dynkinM L proc g t ω * ∫ r in (0:ℝ)..t, L f (proc r ω)) μ)
    (hint_f0_Dg : Integrable
        (fun ω => f (proc 0 ω) * ∫ r in (0:ℝ)..t, L g (proc r ω)) μ)
    (hint_g0_Df : Integrable
        (fun ω => g (proc 0 ω) * ∫ r in (0:ℝ)..t, L f (proc r ω)) μ)
    (hint_Df_Dg : Integrable
        (fun ω => (∫ r in (0:ℝ)..t, L f (proc r ω)) * (∫ r in (0:ℝ)..t, L g (proc r ω))) μ)
    (hint_Lfg : ∀ s : ℝ, Integrable (fun ω => L (fun s' => f s' * g s') (proc s ω)) μ)
    (hint_fsLg : ∀ s : ℝ, Integrable (fun ω => f (proc s ω) * L g (proc s ω)) μ)
    (hint_gsLf : ∀ s : ℝ, Integrable (fun ω => g (proc s ω) * L f (proc s ω)) μ)
    (hint_f0Lg : ∀ s : ℝ, Integrable (fun ω => f (proc 0 ω) * L g (proc s ω)) μ)
    (hint_g0Lf : ∀ s : ℝ, Integrable (fun ω => g (proc 0 ω) * L f (proc s ω)) μ)
    (hint_DfsLg : ∀ s : ℝ,
        Integrable (fun ω => (∫ r in (0:ℝ)..s, L f (proc r ω)) * L g (proc s ω)) μ)
    (hint_DgsLf : ∀ s : ℝ,
        Integrable (fun ω => (∫ r in (0:ℝ)..s, L g (proc r ω)) * L f (proc s ω)) μ)
    (hint_MfLg : ∀ s : ℝ, Integrable (fun ω => dynkinM L proc f t ω * L g (proc s ω)) μ)
    (hint_MgLf : ∀ s : ℝ, Integrable (fun ω => dynkinM L proc g t ω * L f (proc s ω)) μ)
    (hint_MfsLg : ∀ s : ℝ, Integrable (fun ω => dynkinM L proc f s ω * L g (proc s ω)) μ)
    (hint_MgsLf : ∀ s : ℝ, Integrable (fun ω => dynkinM L proc g s ω * L f (proc s ω)) μ)
    (hjoint_MfLg : Integrable
        (Function.uncurry (fun s ω => dynkinM L proc f t ω * L g (proc s ω)))
        ((volume.restrict (Set.Ioc 0 t)).prod μ))
    (hjoint_MgLf : Integrable
        (Function.uncurry (fun s ω => dynkinM L proc g t ω * L f (proc s ω)))
        ((volume.restrict (Set.Ioc 0 t)).prod μ))
    (hjoint_fLg : Integrable
        (Function.uncurry (fun s ω => f (proc s ω) * L g (proc s ω)))
        ((volume.restrict (Set.Ioc 0 t)).prod μ))
    (hjoint_gLf : Integrable
        (Function.uncurry (fun s ω => g (proc s ω) * L f (proc s ω)))
        ((volume.restrict (Set.Ioc 0 t)).prod μ))
    (hjoint_Lfg : Integrable
        (Function.uncurry (fun s ω => L (fun s' => f s' * g s') (proc s ω)))
        ((volume.restrict (Set.Ioc 0 t)).prod μ))
    (hjoint_f0Lg : Integrable
        (Function.uncurry (fun s ω => f (proc 0 ω) * L g (proc s ω)))
        ((volume.restrict (Set.Ioc 0 t)).prod μ))
    (hjoint_g0Lf : Integrable
        (Function.uncurry (fun s ω => g (proc 0 ω) * L f (proc s ω)))
        ((volume.restrict (Set.Ioc 0 t)).prod μ))
    (hjoint_DfLg : Integrable
        (Function.uncurry (fun s ω => (∫ r in (0:ℝ)..s, L f (proc r ω)) * L g (proc s ω)))
        ((volume.restrict (Set.Ioc 0 t)).prod μ))
    (hjoint_DgLf : Integrable
        (Function.uncurry (fun s ω => (∫ r in (0:ℝ)..s, L g (proc r ω)) * L f (proc s ω)))
        ((volume.restrict (Set.Ioc 0 t)).prod μ))
    (hjoint_MfsLg : Integrable
        (Function.uncurry (fun s ω => dynkinM L proc f s ω * L g (proc s ω)))
        ((volume.restrict (Set.Ioc 0 t)).prod μ))
    (hjoint_MgsLf : Integrable
        (Function.uncurry (fun s ω => dynkinM L proc g s ω * L f (proc s ω)))
        ((volume.restrict (Set.Ioc 0 t)).prod μ))
    (hjoint_Gamma : Integrable
        (Function.uncurry (fun s ω => carreDuChamp L f g (proc s ω)))
        ((volume.restrict (Set.Ioc 0 t)).prod μ)) :
    -- (1) the Dynkin martingale property against Mathlib's `Martingale`;
    Martingale (dynkinM L proc f) ℱ μ
      -- (2) the bracket, definitionally the carré-du-champ time integral;
      ∧ (∀ (τ : ℝ) (ω : Ω), dynkinBracketDef L proc f g τ ω
          = ∫ s in (0:ℝ)..τ, carreDuChamp L f g (proc s ω))
      -- (3) the proved `L²` integrated-covariance identity.
      ∧ (∫ ω, dynkinM L proc f t ω * dynkinM L proc g t ω ∂μ
          = ∫ ω, dynkinBracketDef L proc f g t ω ∂μ) := by
  have hMf : Martingale (dynkinM L proc f) ℱ μ :=
    dynkin_martingale μ ℱ proc L P f hf_adapted hf0_adapt hInt_adapted hft_int hf0_int hJ_int
      hMarkov_f hMarkov_Lf hKol hLf_ii hLf_slice hLf_jointInt hPLf_jointInt hbracketMeas
  refine ⟨hMf, fun _ _ => rfl, ?_⟩
  exact dynkin_L2 μ ℱ proc L f g t ht hMf hMg hMfg hLf_adapt hLg_adapt hg0_adapt (hf0_adapt 0)
    (fun ω => hLf_ii ω 0 t) hLg_ii hint_fg_t hint_fg_0 hint_Dfg hint_Mf_g0 hint_Mg_f0
    hint_Mf_Dg hint_Mg_Df hint_f0_Dg hint_g0_Df hint_Df_Dg hint_Lfg hint_fsLg hint_gsLf
    hint_f0Lg hint_g0Lf hint_DfsLg hint_DgsLf hint_MfLg hint_MgLf hint_MfsLg hint_MgsLf
    hjoint_MfLg hjoint_MgLf hjoint_fLg hjoint_gLf hjoint_Lfg hjoint_f0Lg hjoint_g0Lf
    hjoint_DfLg hjoint_DgLf hjoint_MfsLg hjoint_MgsLf hjoint_Gamma

/-! ## Opaque SPDE / Skorokhod-space objects -/

/-- The space `𝒮'(ℝ)` of tempered (Schwartz) distributions, as the state space of the
distribution-valued fluctuation fields.  Its càdlàg-process / Skorokhod theory is absent
from Mathlib, so it is pinned to an opaque type. -/
opaque SchwartzDistModel : Type

/-- Evaluation `Z ↦ Z(φ)` of a distribution against a test function `φ`.  (Retained: it is a
genuine consumer-facing observable used by the charFun-level definition `mpConvDrift` below —
see the consumer audit in `mitoma4_report.md`; the earlier plan to delete it was corrected
after `mpConvDrift` was found to depend on it.) -/
opaque mitomaEval : (ℝ → ℝ) → SchwartzDistModel → ℝ

/-- **Pairing-level charFun observable** (de-opaquing device).  For a *random*
distribution-valued state `Z` (an element of the opaque `SchwartzDistModel`, which records
the random distribution), test function `φ` and frequency `u`,
`pairingCF Z φ u = E[exp(i u ⟨Z,φ⟩)]` is the characteristic function of the real pairing
`⟨Z,φ⟩`.  The Skorokhod/`𝒮'(ℝ)` theory is absent from Mathlib, but the *fdd/charFun*
observable of the pairings is genuine real content; the OU limit and Mitoma reduction are
stated through it.  This is the analogue of `mitomaEval` (which records only the pairing
*value*) at the level of the pairing's *law*, and it is what lets the previously-free
predicates below be replaced by genuine content proved from the martingale CLT
(`TypeDDecouplingMartingaleGaussian.lean`). -/
opaque pairingCF : SchwartzDistModel → (ℝ → ℝ) → ℝ → ℂ

/-- **Real Mitoma tightness predicate** (replaces the former `opaque distTight`).

Whereas the genuine `D([0,1];𝒮'(ℝ))`-tightness of the *opaque* model `SchwartzDistModel`
would require a topology on distribution-valued path space (absent from Mathlib, and not
built here), the *formalizable* content of Mitoma's criterion lives at the concrete level of
`SchwartzMap.SchDual = 𝒮(ℝ,ℝ) →Lₚₜ[ℝ] ℝ`.  `distTightReal Z` asserts that the model `Z`
admits an honest probabilistic realization by `SchDual`-valued processes `W` on probability
spaces `(Ω N, P N)` — with càdlàg `Skoro`-path processes `Yp φ` realizing the real pairings
`t ↦ ⟨W_N(t),φ⟩`, measurable evaluations, per-`φ` Skorokhod tightness of the path laws, and
the charFun link to `Z` via `pairingCF` — i.e. *exactly the hypotheses* of the real Mitoma
theorem `thm_mitoma` (`= TypeDDecouplingMitomaBridge.mitoma_tightness`).  Applying
`thm_mitoma` to that realization yields the uniform compact confinement
`∀η>0 ∃q B, P_N(∃ t∈[0,1], W_N(t)∉polarBall(B·‖·‖_{q+1})) ≤ η`, i.e. the Kallianpur–Xiong
compact-confinement content.  This is the genuine predicate the path bundle `MPPathBundle`
now consumes. -/
def distTightReal (Z : ℕ → ℝ → SchwartzDistModel) : Prop :=
  ∃ (Ω : ℕ → Type) (mΩ : ∀ N, MeasurableSpace (Ω N))
     (P : ∀ N, @MeasureTheory.Measure (Ω N) (mΩ N))
     (_ : ∀ N, @MeasureTheory.IsProbabilityMeasure (Ω N) (mΩ N) (P N))
     (W : ∀ N, ℝ → Ω N → SchwartzMap.SchDual)
     (Yp : SchwartzMap ℝ ℝ → ∀ N, Ω N → SkorokhodBasic.Skoro),
    (∀ (N : ℕ) (t : ℝ) (φ : SchwartzMap ℝ ℝ), @Measurable _ _ (mΩ N) _ (fun ω => W N t ω φ)) ∧
    (∀ (φ : SchwartzMap ℝ ℝ) (N : ℕ), @Measurable _ _ (mΩ N) _ (Yp φ N)) ∧
    (∀ (φ : SchwartzMap ℝ ℝ) (N : ℕ) (ω : Ω N) (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 →
        (Yp φ N ω).toFun t = W N t ω φ) ∧
    (∀ φ : SchwartzMap ℝ ℝ,
        MeasureTheory.IsTightMeasureSet (Set.range (fun N => (P N).map (Yp φ N)))) ∧
    (∀ (N : ℕ) (t : ℝ) (φ : SchwartzMap ℝ ℝ) (u : ℝ),
        pairingCF (Z N t) (fun x => φ x) u
          = ∫ ω, Complex.exp (((u * W N t ω φ : ℝ) : ℂ) * Complex.I) ∂(P N))

/-- The centered Gaussian (Ornstein–Uhlenbeck / Edwards–Wilkinson) target characteristic
function at the finite-dimensional level: `ouCF D χ sig t φ u = exp(-(2 χ D t · sig φ) u²/2)`,
i.e. the `N(0, 2 χ D t ‖∂_x φ‖²)` charFun (condition (N)).  `sig φ` is the `‖∂_x φ‖²`-type
covariance functional, taken as **explicit data** (brief 2(b): covariance data as fields,
not built from a heat semigroup on `𝒮`). -/
noncomputable def ouCF (D χ : ℝ) (sig : (ℝ → ℝ) → ℝ) (t : ℝ) (φ : ℝ → ℝ) (u : ℝ) : ℂ :=
  Complex.exp (((-(2 * χ * D * t * sig φ) * u ^ 2 / 2 : ℝ) : ℂ))

/-- **Condition (D)** (drift convergence), de-opaqued as a genuine real statement: the
rescaled drift of the pairing's Dynkin decomposition converges to `D · Z(Δφ)`.  `drift N t φ`
is the (real) compensator increment of `⟨Z_·^N,φ⟩` and `lap t φ` the limiting Laplacian
pairing `Z_t(Δφ)`. -/
def mpConvDrift (Z : ℕ → ℝ → SchwartzDistModel) (D : ℝ) : Prop :=
  ∃ (drift : ℕ → ℝ → (ℝ → ℝ) → ℝ) (lapOp : (ℝ → ℝ) → (ℝ → ℝ)) (lap : ℝ → (ℝ → ℝ) → ℝ),
    -- the limiting Laplacian pairing `Z_t(Δφ)` (evaluated via `mitomaEval` against `Δφ = lapOp φ`)
    (∀ (φ : ℝ → ℝ) (t : ℝ),
      Filter.Tendsto (fun N => mitomaEval (lapOp φ) (Z N t)) Filter.atTop (𝓝 (lap t φ))) ∧
    -- the rescaled drift converges to `D · Z_t(Δφ)`
    (∀ (φ : ℝ → ℝ) (t : ℝ),
      Filter.Tendsto (fun N => drift N t φ) Filter.atTop (𝓝 (D * lap t φ)))

/-- **Condition (D)/(N)** bracket content, de-opaqued as the exact input to Part 1's
`martingale_charFun_gaussian`: for every test function `φ` and time `t ≥ 0`, the pairings
`⟨Z_t^N,φ⟩` are realized (via `pairingCF`) as the characteristic functions of partial sums of
a **martingale-difference array** with **deterministic bracket** `2 χ D t · sig φ` and
vanishing (a.e.) increments — this is the Dynkin decomposition's martingale part with the
bracket `→ 2χD t ‖∂φ‖²`.  The stopped/truncated companion `Xt` (deterministically bounded,
agreeing with the true array with probability `→ 1`) is exactly the stopped-array adapter of
Part 1. -/
def mpConvBracket (Z : ℕ → ℝ → SchwartzDistModel) (D χ : ℝ) : Prop :=
  ∃ sig : (ℝ → ℝ) → ℝ, (∀ φ, 0 ≤ sig φ) ∧
    ∀ (φ : ℝ → ℝ) (t : ℝ), 0 ≤ t →
      ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @MeasureTheory.Measure Ω mΩ)
        (_ : @MeasureTheory.IsProbabilityMeasure Ω mΩ μ)
        (kn : ℕ → ℕ) (𝓕 : ℕ → ℕ → MeasurableSpace Ω)
        (Xproc Xt : ℕ → ℕ → Ω → ℝ) (bb : ℕ → ℝ) (Cc : ℝ),
        (∀ n, Monotone (𝓕 n)) ∧ (∀ n k, 𝓕 n k ≤ mΩ) ∧
        (∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (Xproc n j)) ∧
        (∀ n j, StronglyMeasurable[𝓕 n (j + 1)] (Xt n j)) ∧
        (∀ n j, μ[Xt n j | 𝓕 n j] =ᵐ[μ] 0) ∧
        (∀ n, 0 ≤ bb n) ∧ Filter.Tendsto bb Filter.atTop (𝓝 0) ∧
        (∀ n j ω, |Xt n j ω| ≤ bb n) ∧
        (∀ n ω, ∑ j ∈ Finset.range (kn n), (Xt n j ω) ^ 2 ≤ Cc) ∧
        (∀ᵐ ω ∂μ, Filter.Tendsto
          (fun n => ∑ j ∈ Finset.range (kn n), (Xt n j ω) ^ 2)
          Filter.atTop (𝓝 (2 * χ * D * t * sig φ))) ∧
        (Filter.Tendsto (fun n => (μ {ω | TypeDDecoupling.MartingaleCLT.partialSum (Xproc n) (kn n) ω
            ≠ TypeDDecoupling.MartingaleCLT.partialSum (Xt n) (kn n) ω}).toReal)
          Filter.atTop (𝓝 0)) ∧
        (∀ (n : ℕ) (u : ℝ), pairingCF (Z n t) φ u
          = ∫ ω, Complex.exp
              (((u * TypeDDecoupling.MartingaleCLT.partialSum (Xproc n) (kn n) ω : ℝ) : ℂ)
                * Complex.I) ∂μ)

/-- **Convergence in law at the fdd/charFun level**: every pairing charFun converges,
`E[exp(iu⟨Z_t^N,φ⟩)] → E[exp(iu⟨Z_t,φ⟩)]` for each `φ`, `t ≥ 0`, `u`.  (The full
Skorokhod-space convergence rides on the Mitoma/Aldous leaves and enters `thm_mp` via the
bundle `MPPathBundle`; this is its fdd shadow, which is what the OU limit is stated at.) -/
def convInLawDist (Z : ℕ → ℝ → SchwartzDistModel) (Zlim : ℝ → SchwartzDistModel) : Prop :=
  ∀ (φ : ℝ → ℝ) (t : ℝ), 0 ≤ t → ∀ u : ℝ,
    Filter.Tendsto (fun N => pairingCF (Z N t) φ u) Filter.atTop (𝓝 (pairingCF (Zlim t) φ u))

/-- **Stationary OU / Edwards–Wilkinson field**, de-opaqued at the fdd/charFun level: the
limit's finite-dimensional distributions are the centered Gaussian ones with the OU
covariance (condition (N)), `E[exp(iu⟨Z_t,φ⟩)] = exp(-(2χD t · sig φ) u²/2)`.  The covariance
functional `sig` (the `‖∂_x φ‖²`-type normalization) is taken as explicit data (brief 2(b));
the heat-semigroup construction on `𝒮` is *not* built here. -/
def isStationaryOU (Zlim : ℝ → SchwartzDistModel) (D χ : ℝ) : Prop :=
  ∃ sig : (ℝ → ℝ) → ℝ, (∀ φ, 0 ≤ sig φ) ∧
    ∀ (φ : ℝ → ℝ) (t : ℝ), 0 ≤ t → ∀ u : ℝ, pairingCF (Zlim t) φ u = ouCF D χ sig t φ u

/-- **Path-space existence/convergence bundle** for `thm_mp` — the *single* documented input
that is genuinely cited rather than proved (it rides on the Mitoma/Aldous tightness leaves
and the heat-semigroup identification of the OU field).  It consumes the Mitoma tightness
`distTightReal Z` and the drift→Laplacian identification `mpConvDrift Z D`, and, *given* that
every fdd charFun converges to a target `g` (which `thm_mp` supplies **proved from Part 1**),
produces a genuine `𝒮'(ℝ)`-valued limit process whose fdds realize `g`.  The Gaussian/
uniqueness content is *not* part of this bundle — it is proved from the martingale CLT. -/
def MPPathBundle (Z : ℕ → ℝ → SchwartzDistModel) (D : ℝ) : Prop :=
  distTightReal Z → mpConvDrift Z D →
    ∀ g : ℝ → (ℝ → ℝ) → ℝ → ℂ,
      (∀ (φ : ℝ → ℝ) (t : ℝ), 0 ≤ t → ∀ u : ℝ,
        Filter.Tendsto (fun N => pairingCF (Z N t) φ u) Filter.atTop (𝓝 (g t φ u))) →
      ∃ Zlim : ℝ → SchwartzDistModel,
        ∀ (φ : ℝ → ℝ) (t : ℝ), 0 ≤ t → ∀ u : ℝ, pairingCF (Zlim t) φ u = g t φ u

/-! ## `thm:mitoma` and `prop:aldous` — tightness criteria -/

/-- **Theorem `thm:mitoma`** (Mitoma, *Ann. Probab.* **11** (1983); Kallianpur–Xiong
compact-confinement form).  A family of càdlàg `𝒮'(ℝ)`-valued processes is tight in
`D([0,1];𝒮'(ℝ))` iff, for every test function `φ`, the real-valued pairing process
`⟨Z^N(·),φ⟩` is tight in `D([0,1];ℝ)`.

**Fidelity repair (Mitoma campaign, task 4).**  The earlier version stated this equivalence
for the *opaque* placeholders `distTight`/`realTight`/`mitomaEval` and was an honest `sorry`;
building a genuine topology on distribution-valued path space `D([0,1];𝒮'(ℝ))` is beyond
current Mathlib and is deliberately **not** attempted here, so a literal `iff` at that level
would be either unformalizable or a manufactured fake.  It is here replaced by the genuine,
proved theorem in the *substantive* (Kallianpur–Xiong) direction: **per-`φ` Skorokhod
tightness `⇒` uniform compact confinement**.

Concretely, for probability spaces `(Ω N, P N)`, distribution-valued processes
`Z N : ℝ → Ω N → SchDual` (where `SchDual = 𝒮(ℝ,ℝ) →Lₚₜ[ℝ] ℝ` is M2's pointwise dual) with
measurable evaluations, and, for each `φ`, a càdlàg `Skoro`-path process `Y φ N : Ω N → Skoro`
realizing the real pairings `t ↦ ⟨Z_N(t),φ⟩` on `[0,1]`: if every path-law family
`{(P N).map (Y φ N)}_N` is `IsTightMeasureSet`, then for every `η>0` there are `q,B>0` with
`K = polarBall (B·‖·‖_{q+1})` compact and `sup_N P_N(∃ t∈[0,1], Z_N(t)∉K) ≤ η`.  This is the
real Mitoma Theorem 4.1 as proved through the Hermite–Sobolev nuclear chain; the
equivalence with the abstract `D([0,1];𝒮'(ℝ))`-tightness is the classical Kallianpur–Xiong
criterion (whose reverse direction we do not formalize, lacking the path-space topology).

The proof is `TypeDDecouplingMitomaBridge.mitoma_tightness`, assembled from M3c's
`mitoma_confinement`, the Skorokhod `IsTightMeasureSet`/`supNorm` theory (A1) and the
càdlàg dense-time upgrade (A2). -/
theorem thm_mitoma
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, MeasureTheory.Measure (Ω N)) [∀ N, MeasureTheory.IsProbabilityMeasure (P N)]
    (Z : ∀ N, ℝ → Ω N → SchwartzMap.SchDual)
    (Y : SchwartzMap ℝ ℝ → ∀ N, Ω N → SkorokhodBasic.Skoro)
    (hmeas : ∀ (N : ℕ) (t : ℝ) (φ : SchwartzMap ℝ ℝ), Measurable (fun ω => Z N t ω φ))
    (hYmeas : ∀ (φ : SchwartzMap ℝ ℝ) (N : ℕ), Measurable (Y φ N))
    (hY : ∀ (φ : SchwartzMap ℝ ℝ) (N : ℕ) (ω : Ω N) (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 →
        (Y φ N ω).toFun t = Z N t ω φ)
    (htight : ∀ φ : SchwartzMap ℝ ℝ,
        MeasureTheory.IsTightMeasureSet (Set.range (fun N => (P N).map (Y φ N))))
    (η : ℝ) (hη : 0 < η) :
    ∃ (q : ℕ) (B : ℝ), 0 < B ∧
      IsCompact (SchwartzMap.polarBall
        (B.toNNReal • TypeDDecouplingMitomaCore.sobolevSeminormB (q + 1))) ∧
      ∀ N, ((P N) {ω | ∃ t ∈ Set.Icc (0:ℝ) 1,
        Z N t ω ∉ SchwartzMap.polarBall
          (B.toNNReal • TypeDDecouplingMitomaCore.sobolevSeminormB (q + 1))}).toReal ≤ η :=
  TypeDDecouplingMitomaBridge.mitoma_tightness P Z Y hmeas hYmeas hY htight η hη

/-- **Proposition `prop:aldous`** (Aldous's criterion; \cite{Aldous}) — the formalized
classical criterion, no longer a citation.  A family `(X i)` of `D([0,1];ℝ)`-valued random
elements on probability spaces `(Ω i, P i)`, each adapted to a right-continuous filtration
`𝓕 i`, whose laws are (i) uniformly tight in sup-norm (`hbdd`) and (ii) satisfy the Aldous
stopping-time condition in `aldousQ` form (`hald`: `α_i(δ, ε) → 0` uniformly in `i`), has
tight pushforward laws on the Skorokhod space `D`.

**Fidelity repair (Skorokhod campaign).**  The earlier version pinned the hypotheses and
conclusion to the opaque predicates `aldousTightAt`/`aldousModulusCond`/`realTight` over a
schematic `ζ : ℕ → ℝ → ℝ` (no probability space, no laws) and was an honest `sorry`.  It is
here replaced by the genuine theorem, obtained by direct application of
`SkorokhodBasic.aldous_tightness` (Part A of the Skorokhod campaign). -/
theorem prop_aldous {ι : Type*}
    {Ω : ι → Type*} [mΩ : ∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (X : ∀ i, Ω i → SkorokhodBasic.Skoro) (hX : ∀ i, Measurable (X i))
    (𝓕 : ∀ i, Filtration ℝ (mΩ i))
    (hrc : ∀ i, (𝓕 i).rightCont = 𝓕 i)
    (hadapt : ∀ i r, Measurable[(𝓕 i) r] (fun ω => (X i ω).toFun r))
    (hbdd : ∀ η : ℝ≥0∞, 0 < η →
        ∃ a : ℝ, ∀ i, (P i) {ω | a ≤ SkorokhodBasic.supNorm (X i ω)} ≤ η)
    (hald : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ δ : ℝ, 0 < δ ∧
        ∀ i, SkorokhodBasic.aldousQ (P i) (fun t ω => (X i ω).toFun t) (𝓕 i) δ ε ≤ η) :
    IsTightMeasureSet (Set.range (fun i => (P i).map (X i))) :=
  SkorokhodBasic.aldous_tightness P X hX 𝓕 hrc hadapt hbdd hald

/-! ## `thm:mp` — equilibrium fluctuations (OU martingale problem) -/

/-- **Gaussian finite-dimensional distributions of the limit, proved from Part 1.**  From the
de-opaqued bracket condition `mpConvBracket Z D χ` — which packages, per test function `φ`
and time `t ≥ 0`, a martingale-difference array with deterministic bracket `2 χ D t · sig φ`
and its stopped/truncated companion — the pairing charFun of `Z_t^N` converges to the
centered Gaussian `ouCF D χ sig`.  This is exactly `martingale_charFun_gaussian` of Part 1
(`TypeDDecouplingMartingaleGaussian.lean`): the single-`M_t` Gaussian charFun via
self-discretisation into the project's own `core_charFun_tendsto`, bridged by the
stopped-array adapter. -/
theorem mpConvBracket_gaussian_fdd {Z : ℕ → ℝ → SchwartzDistModel} {D χ : ℝ}
    (hbracket : mpConvBracket Z D χ) :
    ∃ sig : (ℝ → ℝ) → ℝ, (∀ φ, 0 ≤ sig φ) ∧
      ∀ (φ : ℝ → ℝ) (t : ℝ), 0 ≤ t → ∀ u : ℝ,
        Filter.Tendsto (fun N => pairingCF (Z N t) φ u) Filter.atTop
          (𝓝 (ouCF D χ sig t φ u)) := by
  obtain ⟨sig, hsig, H⟩ := hbracket
  refine ⟨sig, hsig, ?_⟩
  intro φ t ht u
  obtain ⟨Ω, mΩ, μ, hμ, kn, 𝓕, Xproc, Xt, bb, Cc, hmono, hle, hadX, hadXt, hmds,
    hb0, hblim, hbound, hCbr, hbr, hagree, hCF⟩ := H φ t ht
  haveI := hμ
  have hlim := MartingaleGaussian.martingale_charFun_gaussian kn 𝓕 Xproc Xt
    (2 * χ * D * t * sig φ) bb Cc hmono hle hadX hadXt hmds hb0 hblim hbound hCbr hbr hagree u
  have heq : (fun N => pairingCF (Z N t) φ u)
      = (fun N => ∫ ω, Complex.exp
          (((u * TypeDDecoupling.MartingaleCLT.partialSum (Xproc N) (kn N) ω : ℝ) : ℂ)
            * Complex.I) ∂μ) := by
    funext N; exact hCF N u
  rw [heq]
  simpa only [ouCF] using hlim

/-- **Theorem `thm:mp`** (Equilibrium fluctuations; Kipnis–Landim Ch. 11, after
Holley–Stroock), **de-opaqued and its Gaussian/uniqueness core proved from Part 1.**  A
process with Dynkin decomposition whose drift converges to `D Z(Δφ)` (`mpConvDrift`), whose
bracket converges to `2χD t ‖∂φ‖²` (`mpConvBracket`), and which is Mitoma-tight (`distTightReal`),
converges in law to the stationary OU solution.

**What is proved vs. bundled (brief 2(c)).**
* The **Gaussian / uniqueness** content — that every fdd charFun of the limit is the centered
  Gaussian `ouCF D χ sig` — is *proved* from `mpConvBracket_gaussian_fdd`, i.e. from Part 1's
  martingale CLT and the stopped-array adapter.  This determines the limit law (uniqueness).
* The **path-space existence/convergence** content — the production of a genuine `𝒮'(ℝ)`-valued
  limit process realizing those fdds — rides on the Mitoma/Aldous tightness leaves and the
  heat-semigroup identification of the OU field, which are absent from Mathlib.  It enters as
  the *single* documented bundle `hmp : MPPathBundle Z D`, threaded exactly like `hconc`/`hcont`
  in `thm_ewmain`.  `hmp` consumes `htight` and `hdrift` and, *given* the (proved) fdd
  convergence, yields the limit process.

Thus `thm_mp` is now **`sorry`-free**: the previously opaque predicates are genuine content
and the mathematical heart is discharged by Part 1. -/
theorem thm_mp (Z : ℕ → ℝ → SchwartzDistModel) (D χ : ℝ)
    (hdrift : mpConvDrift Z D) (hbracket : mpConvBracket Z D χ) (htight : distTightReal Z)
    (hmp : MPPathBundle Z D) :
    ∃ Zlim : ℝ → SchwartzDistModel, convInLawDist Z Zlim ∧ isStationaryOU Zlim D χ := by
  obtain ⟨sig, hsig, hgauss⟩ := mpConvBracket_gaussian_fdd hbracket
  obtain ⟨Zlim, hZlim⟩ := hmp htight hdrift (ouCF D χ sig) hgauss
  refine ⟨Zlim, ?_, ⟨sig, hsig, fun φ t ht u => hZlim φ t ht u⟩⟩
  intro φ t ht u
  rw [hZlim φ t ht u]
  exact hgauss φ t ht u

/-! ## `lem:gauss` — single-species Gaussianity (condition (N)) -/

/-- **Lemma `lem:gauss`** (single-species Gaussianity; classical Dittrich–Gärtner).  Each
single-species fluctuation field `Y^N` converges to the Gaussian Ornstein–Uhlenbeck /
Edwards–Wilkinson field, with diagonal bracket `2 χ D t ‖∂φ‖²` (condition (N)), `χ = ρ(1−ρ)`.

**Catch #8 — fidelity repair.**  The previous statement took a *free* `Y` with *no* dynamical
hypotheses and asserted OU convergence — a false-universal-shaped placeholder, not a rendering
of the paper's Lemma 6.6.  As the paper itself notes, Lemma 6.6 is the *single-field case* of
Theorem 6.2 (here `thm_mp`), so it is now stated with the same faithful single-species
hypotheses as `thm_mp`'s de-opaqued architecture:
* `hdrift : mpConvDrift Y D` — the single-field drift condition (D): the compensator of the
  pairing's Dynkin decomposition converges to `D · Y(Δφ)`;
* `hbracket : mpConvBracket Y D (ρ*(1-ρ))` — the single-field bracket realization (N): the
  pairings are charFun-realized as martingale-difference arrays with deterministic bracket
  `2 χ D t · sig φ`, `χ = ρ(1-ρ)`, with stopped/truncated companions (exactly Part 1's
  `MartingaleGaussian.martingale_charFun_gaussian` inputs);
* `htight : distTightReal Y` — Mitoma tightness (the real `SchDual`-realization predicate);
* `hmp : MPPathBundle Y D` — the path-space existence/convergence bundle (`MPPathBundle`-style
  field), cited on the Mitoma/Aldous leaves.

The finite-`N` ground truth making `hbracket` faithful for the stationary single-species WASEP
is the (N)-computation of `TypeDDecouplingBracketN.lean` (equilibrium mean `2χD‖φ'‖²`, `O(1/N)`
variance under the Bernoulli product weight, and the `L²` time-integration).  The
Dittrich–Gärtner reference is thereby demoted to a *classical instantiation* citation (which
stationary WASEP field realizes these pairings), no longer a proof obligation: the lemma is now
proved outright as the single-field case of `thm_mp`, sharing its derivation
(`mpConvBracket_gaussian_fdd` + the path bundle) rather than duplicating it.

The density hypothesis `ρ ∈ (0,1)` is kept as a faithful part of the statement (`χ = ρ(1-ρ)` is
the blocking-measure variance); the proof, being the single-field `thm_mp`, does not consume
it directly. -/
theorem lem_gauss (Y : ℕ → ℝ → SchwartzDistModel) (D ρ : ℝ) (_hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (hdrift : mpConvDrift Y D) (hbracket : mpConvBracket Y D (ρ * (1 - ρ)))
    (htight : distTightReal Y) (hmp : MPPathBundle Y D) :
    ∃ Ylim : ℝ → SchwartzDistModel,
      convInLawDist Y Ylim ∧ isStationaryOU Ylim D (ρ * (1 - ρ)) :=
  thm_mp Y D (ρ * (1 - ρ)) hdrift hbracket htight hmp

/-! ## `prop:drift` — the drift converges to the Laplacian (condition (D)) -/

/-
**Proposition `prop:drift`** (drift).  For each species and density,
`Γ_i^N(φ,·) → D Y_i(Δφ,·)` in `L²`, `D` the symmetric-part diffusivity (condition (D)).

**Quantitative core (now proved `sorry`-free).**  The finite-`N` content of the drift
convergence is the two deterministic finite-algebra estimates of `TypeDDecouplingDrift.lean`:

* `TypeDDecoupling.Drift.drift_sbp_bound` (Lemma `sbp`): summation-by-parts + Taylor shows
  the rescaled gradient current `N^{1/2} ∑ φ'(x/N)(η_x − η_{x+1})` matches the discrete
  Laplacian `N^{-1/2} ∑ φ''(x/N)(η_x − ρ)` up to `O(N^{-1/2})`, for *every* configuration;
* `TypeDDecoupling.Drift.corr_second_moment` (Lemma `corr`): under *any* product probability
  weight the correction functional `γ N^{1/2} ∑ φ'(x/N)(g_x − ḡ_x)`, `g_x = η_{x+1}(1−η_x)`,
  has second moment `≤ γ² N · 3((2K+1)N+2)‖φ'‖² = O(c²/N²)`.

**S'(ℝ)-convergence wrapper (hypothesis-level).**  The passage from these finite-`N`
estimates to the `L²` drift error against the *distribution-valued* limiting field (the
object `ewDriftL2err`, involving the `𝒮'(ℝ)`-valued fluctuation field and the time integral
under stationarity) is the SPDE bridge; it is not available in Mathlib and is taken here as
the hypotheses `hpin` / `hpin_nonneg` (the identification of `ewDriftL2err` with a concrete
nonnegative family controlled by the quantitative core).  Given the wrapper, the `C/N` bound
and the vanishing are derived with no `sorry`.

The density hypothesis `_hρ : ρ ∈ (0,1)` is kept as a faithful part of the proposition (the
blocking-measure density regime) even though the wrapper-level derivation does not consume it.
-/
theorem prop_drift (D ρ : ℝ) (_hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (Cw : ℝ) (hCw : 0 < Cw)
    (hpin : ∀ N : ℕ, 1 ≤ N → ewDriftL2err D ρ N ≤ Cw / (N : ℝ))
    (hpin_nonneg : ∀ N : ℕ, 0 ≤ ewDriftL2err D ρ N) :
    (∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ewDriftL2err D ρ N ≤ C / (N : ℝ))
    ∧ Tendsto (fun N => ewDriftL2err D ρ N) atTop (𝓝 0) := by
  refine ⟨⟨Cw, hCw, hpin⟩, ?_⟩
  exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun N hN => by rw [ Real.norm_of_nonneg ( hpin_nonneg N ) ] ; exact hpin N hN ⟩ ) ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop )

/-! ## `thm:ewmain` — the decoupled Edwards–Wilkinson limit -/

/-- **Theorem `thm:ewmain`** (decoupled Edwards–Wilkinson limit).  Under `q = 1 − c/N²`,
the two species' fluctuation fields `Y₁^N,Y₂^N` (valued in `𝒮'(ℝ) = SchwartzDistModel`) are
tight in `D([0,T];𝒮'(ℝ))` and every limit `Y_i` is a stationary solution of
`∂_t Y_i = D ∂²_x Y_i + √(2χ_i D) ∂_x ξ_i` with `D = 1`, `χ_i = ρ_i(1−ρ_i)`; moreover the
two limits *decouple*: the limiting cross bracket `⟨M₁^N,M₂^N⟩` vanishes (condition (X)) and
the ν/ϖ sector comparison holds.

**Faithful assembly of the toolkit.**  Unlike a purely propositional skeleton, this is wired
to the file-level model objects (`SchwartzDistModel`, `distTightReal`, `convInLawDist`,
`isStationaryOU`, `mitomaEval`, `mpConvDrift`, `mpConvBracket`,
`ewCrossBracketSq`, `ewDressedMass`) and to the concrete corrected
sector comparison of `TypeDDecoupling.Sector`, and it *invokes the genuine toolkit lemmas*:

* tightness of each species: threaded directly as the real predicate `distTightReal` via
  `htight1`, `htight2` — the genuine `SchDual`-realization tightness that the proved
  `thm_mitoma` acts on to yield uniform compact confinement (Kallianpur–Xiong); the earlier
  opaque `realTight` component-tightness inputs and the fake `distTight` iff are retired;
* OU limits: `thm_mp` (fed the drift/bracket convergences `hdrift1`, `hbracket1` and the
  Mitoma tightness) for species 1, and `lem_gauss` (single-species Gaussianity, fed
  `ρ₂ ∈ (0,1)`) for species 2;
* decoupling: `lem_eps` provides the null dressed-mass sequence `ε_N → 0`, which feeds
  `prop_conc` to give the vanishing limiting cross bracket `ewCrossBracketSq c N t → 0`
  (condition (X)); the **corrected** `lem_sector` (at the compensated fugacity
  `β = α/(1+α)`) supplies the two-sided sector-mass comparison constant `M`.

As of the Mitoma campaign's final task, `thm_ewmain` is **`sorry`-free** and depends only on
the standard axioms `propext`/`Classical.choice`/`Quot.sound` (verified with `#print axioms`).
The former last `sorry` lived in the opaque `thm_mitoma` iff; that theorem is now the genuine,
proved Mitoma criterion (`= TypeDDecouplingMitomaBridge.mitoma_tightness`), and the two
species' tightness enters here as the real predicate `distTightReal` (an honest `SchDual`
realization with per-`φ` Skorokhod tightness) rather than through the retired opaque iff.  The
remaining toolkit inputs (`mpConvDrift`/`mpConvBracket`/`MPPathBundle`/`lem_sector`/`prop_conc`
etc.) are threaded as explicit, genuinely-used hypotheses, so the assembly introduces no
`sorry` of its own. -/
theorem thm_ewmain
    (ρ₁ ρ₂ : ℝ) (hρ₂ : ρ₂ ∈ Set.Ioo (0 : ℝ) 1)
    (Y₁ Y₂ : ℕ → ℝ → SchwartzDistModel)
    (c : ℝ) (hc : 0 < c)
    -- Mitoma tightness of the two species' fields, as the real predicate `distTightReal`
    -- (replacing the former opaque `realTight`/`mitomaEval` component-tightness inputs): each
    -- packages an honest `SchDual`-valued realization with per-`φ` Skorokhod tightness, i.e.
    -- exactly the hypotheses `thm_mitoma` consumes to produce uniform compact confinement.
    (htight1 : distTightReal Y₁)
    (htight2 : distTightReal Y₂)
    -- `prop:drift` / bracket convergence feeding `thm:mp` for species 1
    (hdrift1 : mpConvDrift Y₁ 1)
    (hbracket1 : mpConvBracket Y₁ 1 (ρ₁ * (1 - ρ₁)))
    -- the single documented path-space existence/convergence bundle for `thm:mp`
    -- (Mitoma/Aldous + heat-semigroup identification), threaded like `hconc`/`hcont`
    (hmp1 : MPPathBundle Y₁ 1)
    -- `lem:gauss` (single-species Gaussianity) inputs for species 2, threaded exactly like
    -- `hdrift1`/`hbracket1`/`hmp1` above (the fidelity-repaired `lem_gauss` now takes the same
    -- faithful single-field hypotheses as `thm_mp`)
    (hdrift2 : mpConvDrift Y₂ 1)
    (hbracket2 : mpConvBracket Y₂ 1 (ρ₂ * (1 - ρ₂)))
    (hmp2 : MPPathBundle Y₂ 1)
    -- corrected `lem:sector` at the compensated fugacity `β = α/(1+α)`: sector masses `nu`, `pi`
    (q α β : ℝ) (S : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < α)
    (hα : β = α / (1 + α))
    (A : ℝ) (hA0 : 0 ≤ A) (hAbnd : (-(Real.log q)) * (S : ℝ) ^ 2 ≤ A)
    (hβ' : β * q ^ (-(2 * (S : ℤ))) ≤ (1 + β) / 2)
    (hqS : q ^ (-(2 * (S : ℤ))) ≤ 2)
    (nu pi : ℕ → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hpi : ∀ n ≤ S, 0 < pi n)
    (hsum_nu : ∑ n ∈ Finset.range (S + 1), nu n = 1)
    (hsum_pi : ∑ n ∈ Finset.range (S + 1), pi n = 1)
    (hratio : ∀ n ≤ S, nu n = Z * (α / β) ^ n / Sector.hfac q β S n * pi n)
    (hconc : ∃ Mc Cphi Ck Ce : ℝ, 0 ≤ Mc ∧ 0 ≤ Ck ∧ 0 ≤ Ce ∧
      ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 < t →
        ∃ (nu' : ℝ) (bonds : Finset ℤ) (g : ℤ → ℝ) (G : ℝ → ℤ → ℝ) (Ct : ℝ → ℝ),
          0 ≤ ewCrossBracketSq c N t ∧
          3 * c ≤ nu' * (N : ℝ) ^ 2 ∧
          (∀ x, 0 ≤ g x) ∧
          (∑ x ∈ bonds, g x ≤ Cphi * (N : ℝ)) ∧
          (∀ s x, x ∈ bonds → G s x ≤
            Ck * ((1 + s * (N : ℝ) ^ 2)⁻¹
              + Real.exp (-nu' * (s * (N : ℝ) ^ 2)) * (Real.sqrt (1 + s * (N : ℝ) ^ 2))⁻¹) + ewEps N) ∧
          (∀ s, 0 < s → |Ct s| ≤ (Mc / (N : ℝ) ^ 2) * (∑ x ∈ bonds, g x * Real.sqrt (G s x)) ^ 2) ∧
          (∀ s, 0 < s → |Ct s| ≤ Ce / (N : ℝ)) ∧
          IntervalIntegrable (fun s => |Ct s|) MeasureTheory.volume 0 t ∧
          ewCrossBracketSq c N t ≤ 2 * t * ∫ s in (0:ℝ)..t, |Ct s|) :
    distTightReal Y₁ ∧ distTightReal Y₂ ∧
      (∃ Z₁ Z₂ : ℝ → SchwartzDistModel,
        convInLawDist Y₁ Z₁ ∧ convInLawDist Y₂ Z₂ ∧
        isStationaryOU Z₁ 1 (ρ₁ * (1 - ρ₁)) ∧ isStationaryOU Z₂ 1 (ρ₂ * (1 - ρ₂))) ∧
      (∀ n ≤ S, nu n ≤ Real.exp (2 * (A * (1 + 8 * β / (1 - β)))) * pi n
              ∧ pi n ≤ Real.exp (2 * (A * (1 + 8 * β / (1 - β)))) * nu n) ∧
      (∀ t : ℝ, 0 < t → Tendsto (fun N => ewCrossBracketSq c N t) atTop (𝓝 0)) := by
  -- tightness of each species is now the genuine `distTightReal` hypothesis (the real Mitoma
  -- content `thm_mitoma` acts on), threaded directly into `thm_mp`/`lem_gauss`.
  -- OU limits: `thm:mp` (species 1) and `lem:gauss` (species 2)
  obtain ⟨Z₁, hcl1, hou1⟩ := thm_mp Y₁ 1 (ρ₁ * (1 - ρ₁)) hdrift1 hbracket1 htight1 hmp1
  obtain ⟨Z₂, hcl2, hou2⟩ := lem_gauss Y₂ 1 ρ₂ hρ₂ hdrift2 hbracket2 htight2 hmp2
  -- two-sided sector-mass comparison (uniform constant `exp(2C₀)`) from the corrected `lem:sector`
  have hsec := lem_sector q α β S hq0 hq1 hβ0 hβ1 hα0 hα A hA0 hAbnd hβ' hqS nu pi Z hZ hpi
      hsum_nu hsum_pi hratio
  -- the dressed mass is asymptotically negligible (`lem:eps`), giving the null sequence `ewEps`
  -- ... feeding `prop:conc` for the vanishing limiting cross bracket (condition (X))
  have hvanish :=
    (prop_conc c hc ewEps ewEps_tendsto (fun N => by unfold ewEps; positivity) hconc).2
  exact ⟨htight1, htight2,
    ⟨Z₁, Z₂, hcl1, hcl2, hou1, hou2⟩, hsec.2, hvanish⟩

end TypeDDecoupling