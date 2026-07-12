import Mathlib

/-!
# Karamata's Tauberian theorem at constant `L` (the case the project uses)

This file develops, library-clean, the **constant-`L` Karamata Tauberian theorem** used by
`TypeDDecouplingLCLT.lem_tau`.

**Fidelity note (the project's sixth catch).**  The statement previously encoded in
`TypeDDecouplingLCLT.lean` (theorem `karamata_tauberian`, now removed) quantified over *all*
pointwise slowly varying `L` with **no measurability** hypothesis.  The cited theorem
(BGT Thm 1.7.1′, Feller §XIII.5) requires `L` measurable, and the slowly-varying theory
(the uniform-convergence theorem for regularly varying functions) genuinely fails for
non-measurable `L`; the encoded statement therefore *exceeded* the cited literature and was
not a faithful citation.  The consumer `lem_tau` only ever instantiates `L` at a **constant**
(`L ≡ m(r)/(2√a)`, `ρ = 1/2`), so we restate and *prove* the theorem at constant `L`, i.e.
with a constant `c > 0`:
`ω(λ) ∼ c·λ^{-ρ}  (λ↓0)  ⇔  ∫₀ˢ p ∼ c·s^ρ/Γ(ρ+1)  (s→∞)`,
for `p ≥ 0` locally integrable and `ρ > 0`.

The **Tauberian** direction (`ω ⇒ ∫p`, the one `lem_tau` consumes) is proved here in full via
Karamata's method in its finite-measure ("moments carry the `e^{-u}` weight") formulation:
the rescaled functionals `Ifn` test `p` against `φ(e^{-λt})·e^{-λt}`; their limits `Jfn` are
integration against the finite measure `(c/Γρ)·e^{-x}x^{ρ-1}dx`.  Monomials give the moments
(Laplace values), Stone–Weierstrass extends to continuous test functions, and a one-sided
continuous sandwich of the indicator (whose jump point carries no mass) yields the result.
-/

open MeasureTheory Filter Set Topology Asymptotics
open scoped BigOperators Real Topology

namespace TypeDDecouplingKaramata

/-- The Laplace transform `ω(λ) = ∫₀^∞ e^{−λt} p(t) dt`. -/
noncomputable def lap (p : ℝ → ℝ) (lam : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ), Real.exp (-(lam * t)) * p t

/-- Rescaled test functional: `Ifn p ρ λ φ = λ^ρ ∫₀^∞ φ(e^{−λt})·e^{−λt}·p(t) dt`.
The extra `e^{−λt}` weight is what makes the limit measure finite. -/
noncomputable def Ifn (p : ℝ → ℝ) (ρ lam : ℝ) (φ : ℝ → ℝ) : ℝ :=
  lam ^ ρ * ∫ t in Ioi (0:ℝ), φ (Real.exp (-(lam * t))) * Real.exp (-(lam * t)) * p t

/-- Limit functional: `Jfn ρ c φ = (c/Γρ) ∫₀^∞ φ(e^{−x})·e^{−x}·x^{ρ−1} dx`, i.e. integration
of `φ(e^{−x})` against the finite measure `(c/Γρ) e^{−x} x^{ρ−1} dx` of total mass `c`. -/
noncomputable def Jfn (ρ c : ℝ) (φ : ℝ → ℝ) : ℝ :=
  (c / Real.Gamma ρ) * ∫ x in Ioi (0:ℝ), φ (Real.exp (-x)) * Real.exp (-x) * x ^ (ρ - 1)

/-- The one-sided target test function `φ₀(y) = (1/y)·𝟙_{[e^{-1},1]}(y)` (bounded, with a single
jump at `y = e^{-1}`), chosen so that `Ifn` of it is `λ^ρ ∫₀^{1/λ} p` and `Jfn` of it is
`c/Γ(ρ+1)`. -/
noncomputable def phi0 : ℝ → ℝ := fun y => if Real.exp (-1) ≤ y then 1 / y else 0

/-- Bundled hypotheses of the constant-`L` Tauberian theorem. -/
structure KData where
  p : ℝ → ℝ
  ρ : ℝ
  c : ℝ
  hp : ∀ t : ℝ, 0 ≤ t → 0 ≤ p t
  hint : ∀ lam : ℝ, 0 < lam → IntegrableOn (fun t => Real.exp (-(lam * t)) * p t) (Ioi 0)
  hρ : 0 < ρ
  hc : 0 < c
  hlim : Tendsto (fun lam => lam ^ ρ * lap p lam) (𝓝[>] (0:ℝ)) (𝓝 c)

/-! ## Moments: `Ifn` of a monomial is a Laplace value -/

/-
`Ifn p ρ λ (y ↦ y^k) = λ^ρ · lap p ((k+1)λ)` (pointwise identity of integrands).
-/
lemma Ifn_monomial_eq (p : ℝ → ℝ) (ρ : ℝ) {lam : ℝ} (hlam : 0 < lam) (k : ℕ) :
    Ifn p ρ lam (fun y => y ^ k) = lam ^ ρ * lap p ((k + 1) * lam) := by
  exact congrArg _ ( MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [ show ( Real.exp ( - ( lam * x ) ) ) ^ k * Real.exp ( - ( lam * x ) ) = Real.exp ( - ( ( k + 1 ) * lam * x ) ) by rw [ ← Real.exp_nat_mul, ← Real.exp_add ] ; ring ] )

/-
Scaling the Laplace argument: `λ^ρ · lap p (m·λ) → c·m^{-ρ}` as `λ ↓ 0`, for `m ≥ 1`.
-/
lemma lap_scale_tendsto (D : KData) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun lam => lam ^ D.ρ * lap D.p (m * lam)) (𝓝[>] (0:ℝ))
      (𝓝 (D.c * (m : ℝ) ^ (-D.ρ))) := by
  have h_aux : Filter.Tendsto (fun lam => (m * lam) ^ D.ρ * lap D.p (m * lam)) (nhdsWithin 0 (Set.Ioi 0)) (nhds D.c) := by
    convert D.hlim.comp ( show Filter.Tendsto ( fun lam : ℝ => ( m : ℝ ) * lam ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) from ?_ ) using 2;
    refine' Filter.Tendsto.inf _ _ <;> norm_num;
    · exact Continuous.tendsto' ( by continuity ) _ _ ( by norm_num );
    · exact fun x hx => mul_pos ( Nat.cast_pos.mpr hm ) hx;
  have h_rewrite : ∀ lam : ℝ, 0 < lam → (m * lam) ^ D.ρ * lap D.p (m * lam) = m ^ D.ρ * (lam ^ D.ρ * lap D.p (m * lam)) := by
    intro lam hl; rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring;
  have := h_aux.div_const ( m ^ D.ρ : ℝ );
  exact this.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_rewrite x hx, mul_div_cancel_left₀ _ ( by positivity ) ] ) |> fun h => h.trans ( by rw [ Real.rpow_neg ( by positivity ) ] ; ring_nf; norm_num )

/-
Monomial moment convergence: `Ifn (y ↦ y^k) → c·(k+1)^{-ρ} = Jfn (y ↦ y^k)`.
-/
lemma Ifn_monomial_tendsto (D : KData) (k : ℕ) :
    Tendsto (fun lam => Ifn D.p D.ρ lam (fun y => y ^ k)) (𝓝[>] (0:ℝ))
      (𝓝 (D.c * (k + 1 : ℝ) ^ (-D.ρ))) := by
  convert lap_scale_tendsto D ( k + 1 ) ( by linarith ) using 1;
  · ext lam
    simp [Ifn, lap];
    exact Or.inl ( by congr; ext t; rw [ ← Real.exp_nat_mul ] ; rw [ ← Real.exp_add ] ; ring );
  · norm_cast

/-
`Jfn` of a monomial equals `c·(k+1)^{-ρ}` (Gamma integral).
-/
lemma Jfn_monomial (D : KData) (k : ℕ) :
    Jfn D.ρ D.c (fun y => y ^ k) = D.c * (k + 1 : ℝ) ^ (-D.ρ) := by
  convert congr_arg ( fun x : ℝ => ( D.c / Real.Gamma D.ρ ) * x ) ( Real.integral_rpow_mul_exp_neg_mul_Ioi ( show 0 < D.ρ by linarith [ D.hρ ] ) ( show 0 < ( k : ℝ ) + 1 by linarith ) ) using 1;
  · unfold Jfn; congr; ext; ring;
    rw [ ← Real.exp_nat_mul ] ; rw [ ← Real.exp_add ] ; ring;
  · rw [ Real.rpow_neg ( by positivity ), Real.div_rpow ] <;> ring <;> norm_num [ ne_of_gt ( Real.Gamma_pos_of_pos D.hρ ) ];
    positivity

/-! ## Integrability and boundedness of the functionals -/

/-
For a function `g` bounded by `M` on `(0,1]`, the `Ifn`-integrand is integrable.
-/
lemma integrableOn_weighted (D : KData) {lam : ℝ} (hlam : 0 < lam) (g : ℝ → ℝ)
    (hg : Continuous g) :
    IntegrableOn
      (fun t => g (Real.exp (-(lam * t))) * Real.exp (-(lam * t)) * D.p t) (Ioi 0) := by
  obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc ( show ContinuousOn g ( Set.Icc 0 1 ) from hg.continuousOn );
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun t => M * Real.exp ( - ( lam * t ) ) * |D.p t|;
  · have h_integrable : IntegrableOn (fun t => Real.exp (-(lam * t)) * D.p t) (Ioi 0) :=
      D.hint lam hlam
    convert h_integrable.norm.const_mul M using 2 ; norm_num [ mul_assoc, abs_mul ];
  · have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-(lam * t)) * D.p t) (Set.Ioi 0) :=
      D.hint lam hlam
    have := h_integrable.aestronglyMeasurable;
    simpa only [ mul_assoc ] using Continuous.aestronglyMeasurable ( show Continuous fun t => g ( Real.exp ( - ( lam * t ) ) ) from hg.comp <| Real.continuous_exp.comp <| Continuous.neg <| continuous_const.mul continuous_id' ) |> fun h => h.mul this;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by simpa [ abs_mul, abs_of_nonneg ( Real.exp_pos _ |> LT.lt.le ) ] using mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( hM _ ⟨ by positivity, Real.exp_le_one_iff.mpr <| neg_nonpos.mpr <| mul_nonneg hlam.le ht.out.le ⟩ ) <| Real.exp_pos _ |> LT.lt.le ) <| abs_nonneg _;

/-
`Ifn` is additive in the test function (over integrable integrands).
-/
lemma Ifn_add (D : KData) {lam : ℝ} (hlam : 0 < lam) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    Ifn D.p D.ρ lam (fun y => f y + g y)
      = Ifn D.p D.ρ lam f + Ifn D.p D.ρ lam g := by
  unfold Ifn; ring;
  convert congr_arg _ ( MeasureTheory.integral_add ( integrableOn_weighted D hlam f hf ) ( integrableOn_weighted D hlam g hg ) ) using 1 ; ring!

/-
`Ifn` respects scalar multiples.
-/
lemma Ifn_smul (D : KData) {lam : ℝ} (hlam : 0 < lam) (a : ℝ) (f : ℝ → ℝ) :
    Ifn D.p D.ρ lam (fun y => a * f y) = a * Ifn D.p D.ρ lam f := by
  unfold Ifn;
  simp +decide only [mul_assoc, mul_left_comm, ← integral_const_mul]

/-
`Ifn` is monotone: `f ≤ g` on `(0,1]` implies `Ifn f ≤ Ifn g`, using `p ≥ 0`.
-/
lemma Ifn_mono (D : KData) {lam : ℝ} (hlam : 0 < lam) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ y : ℝ, 0 < y → y ≤ 1 → f y ≤ g y) :
    Ifn D.p D.ρ lam f ≤ Ifn D.p D.ρ lam g := by
  refine' mul_le_mul_of_nonneg_left ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioi fun t ht => _ ) ( Real.rpow_nonneg hlam.le _ );
  · convert integrableOn_weighted D hlam f hf using 1;
  · convert integrableOn_weighted D hlam g hg using 1;
  · exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( hfg _ ( Real.exp_pos _ ) ( Real.exp_le_one_iff.mpr ( by nlinarith [ ht.out ] ) ) ) ( Real.exp_nonneg _ ) ) ( D.hp _ ( le_of_lt ht.out ) )

/-
`Ifn` of the constant `1` is `λ^ρ · lap p λ`.
-/
lemma Ifn_one_eq (p : ℝ → ℝ) (ρ : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Ifn p ρ lam (fun _ => 1) = lam ^ ρ * lap p lam := by
  unfold lap Ifn; aesop;

/-
`Ifn (·↦1) → c`.
-/
lemma Ifn_one_tendsto (D : KData) :
    Tendsto (fun lam => Ifn D.p D.ρ lam (fun _ => 1)) (𝓝[>] (0:ℝ)) (𝓝 D.c) := by
  refine' Filter.Tendsto.congr' _ D.hlim;
  filter_upwards [ self_mem_nhdsWithin ] with lam hl using by rw [ Ifn_one_eq _ _ hl ] ;

/-
`|Jfn φ| ≤ M·c` when `|φ| ≤ M` on `(0,1]`.
-/
lemma Jfn_bound (D : KData) (φ : ℝ → ℝ) (M : ℝ)
    (hφ : ∀ y : ℝ, 0 < y → y ≤ 1 → |φ y| ≤ M) :
    |Jfn D.ρ D.c φ| ≤ M * D.c := by
  -- Let's simplify the expression for $|Jfn|$.
  have h_simp : abs (∫ x in Set.Ioi 0, φ (Real.exp (-x)) * Real.exp (-x) * x ^ (D.ρ - 1)) ≤ M * ∫ x in Set.Ioi 0, Real.exp (-x) * x ^ (D.ρ - 1) := by
    rw [ ←MeasureTheory.integral_const_mul ];
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
    · have := @integral_rpow_mul_exp_neg_rpow 1;
      specialize @this ( D.ρ - 1 ) ; simp_all +decide [ mul_comm ];
      exact MeasureTheory.Integrable.const_mul ( by exact ( by by_contra h; exact absurd ( this D.hρ ) ( by rw [ MeasureTheory.integral_undef h ] ; linarith [ Real.Gamma_pos_of_pos D.hρ ] ) ) ) _;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx;
      norm_num [ abs_mul, abs_of_nonneg ( Real.exp_pos _ |> le_of_lt ), abs_of_nonneg ( Real.rpow_nonneg hx.out.le _ ) ];
      simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_right ( hφ _ ( Real.exp_pos _ ) ( Real.exp_le_one_iff.mpr ( neg_nonpos.mpr hx.out.le ) ) ) ( mul_nonneg ( Real.exp_nonneg _ ) ( Real.rpow_nonneg hx.out.le _ ) );
  convert mul_le_mul_of_nonneg_left h_simp ( div_nonneg D.hc.le ( Real.Gamma_nonneg_of_nonneg D.hρ.le ) ) using 1;
  · unfold Jfn; rw [ abs_mul, abs_of_nonneg ( div_nonneg D.hc.le ( Real.Gamma_nonneg_of_nonneg D.hρ.le ) ) ] ;
  · rw [ Real.Gamma_eq_integral D.hρ ] ; ring;
    rw [ mul_assoc, mul_inv_cancel₀ ( ne_of_gt <| by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by rw [ show ( ∫ x : ℝ in Set.Ioi 0, Real.exp ( -x ) * x ^ ( -1 + D.ρ ) ) = Real.Gamma ( D.ρ ) by rw [ Real.Gamma_eq_integral ( by linarith [ D.hρ ] ) ] ; congr; ext; ring ] ; exact Real.Gamma_pos_of_pos ( by linarith [ D.hρ ] ) ) ) ) ) ) ) ), mul_one ]

/-
`Jfn` of the constant `1` is `c`.
-/
lemma Jfn_one (D : KData) : Jfn D.ρ D.c (fun _ => 1) = D.c := by
  convert congr_arg ( fun x : ℝ => ( D.c / Real.Gamma D.ρ ) * x ) ( Real.Gamma_eq_integral D.hρ ) using 1;
  · unfold Jfn;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, Real.Gamma_eq_integral D.hρ ];
  · rw [ div_mul_eq_mul_div, eq_div_iff ];
    · rw [ Real.Gamma_eq_integral D.hρ ];
    · exact ne_of_gt <| Real.Gamma_pos_of_pos D.hρ

/-- `|Ifn ψ| ≤ M · (λ^ρ · lap p λ)` when `|ψ| ≤ M` on `(0,1]`. -/
lemma Ifn_abs_le (D : KData) {lam : ℝ} (hlam : 0 < lam) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (M : ℝ) (hM : ∀ y : ℝ, 0 < y → y ≤ 1 → |ψ y| ≤ M) :
    |Ifn D.p D.ρ lam ψ| ≤ M * (lam ^ D.ρ * lap D.p lam) := by
  have hsimp : |∫ t in Ioi 0, ψ (Real.exp (-(lam * t))) * Real.exp (-(lam * t)) * D.p t|
      ≤ M * ∫ t in Ioi 0, Real.exp (-(lam * t)) * D.p t := by
    rw [← MeasureTheory.integral_const_mul, ← Real.norm_eq_abs]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _)
      (MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_)
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _
    · exact (D.hint lam hlam).const_mul M
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
      have he1 : Real.exp (-(lam * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.out])
      have hpt : 0 ≤ D.p t := D.hp t ht.out.le
      have hψM : |ψ (Real.exp (-(lam * t)))| ≤ M := hM _ he he1
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg he.le, abs_of_nonneg hpt]
      calc |ψ (Real.exp (-(lam * t)))| * Real.exp (-(lam * t)) * D.p t
          = |ψ (Real.exp (-(lam * t)))| * (Real.exp (-(lam * t)) * D.p t) := by ring
        _ ≤ M * (Real.exp (-(lam * t)) * D.p t) :=
            mul_le_mul_of_nonneg_right hψM (mul_nonneg he.le hpt)
  unfold Ifn lap
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hlam.le _)]
  calc lam ^ D.ρ * |∫ t in Ioi 0, ψ (Real.exp (-(lam * t))) * Real.exp (-(lam * t)) * D.p t|
      ≤ lam ^ D.ρ * (M * ∫ t in Ioi 0, Real.exp (-(lam * t)) * D.p t) :=
        mul_le_mul_of_nonneg_left hsimp (Real.rpow_nonneg hlam.le _)
    _ = M * (lam ^ D.ρ * ∫ t in Ioi 0, Real.exp (-(lam * t)) * D.p t) := by ring

/-
`Jfn` is additive.
-/
lemma Jfn_add (D : KData) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Jfn D.ρ D.c (fun y => f y + g y) = Jfn D.ρ D.c f + Jfn D.ρ D.c g := by
  unfold Jfn; ring;
  rw [ ← mul_add, ← MeasureTheory.integral_add ];
  · -- The product of a continuous function and an integrable function is integrable.
    have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * x ^ (-1 + D.ρ)) (Set.Ioi 0) := by
      have h_integrable : ∫ x in Set.Ioi 0, Real.exp (-x) * x ^ (-1 + D.ρ) = Real.Gamma (D.ρ) := by
        rw [ Real.Gamma_eq_integral D.hρ ] ; congr ; ext ; ring;
      exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; linarith [ Real.Gamma_pos_of_pos D.hρ ] );
    -- Since $f$ is continuous, $f(\exp(-x))$ is bounded on $(0, \infty)$.
    obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Set.Ioi 0, |f (Real.exp (-x))| ≤ M := by
      have h_bounded : ∃ M, ∀ x ∈ Set.Icc 0 1, |f x| ≤ M := by
        exact IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) hf.continuousOn;
      exact ⟨ h_bounded.choose, fun x hx => h_bounded.choose_spec _ ⟨ Real.exp_nonneg _, Real.exp_le_one_iff.mpr <| neg_nonpos.mpr hx.out.le ⟩ ⟩;
    refine' MeasureTheory.Integrable.mono' ( h_integrable.norm.const_mul M ) _ _;
    · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( hf.comp ( Real.continuous_exp.comp ( ContinuousNeg.continuous_neg ) ) |> Continuous.aestronglyMeasurable ) ( Real.continuous_exp.comp ( ContinuousNeg.continuous_neg ) |> Continuous.aestronglyMeasurable ) ) ( measurable_id.pow_const _ |> Measurable.aestronglyMeasurable );
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by simpa [ mul_assoc, abs_mul ] using mul_le_mul_of_nonneg_right ( hM x hx ) ( by positivity ) ;
  · -- The function $g(e^{-x}) e^{-x} x^{\rho-1}$ is integrable on $(0, \infty)$ because $g$ is continuous and bounded, and $e^{-x} x^{\rho-1}$ is integrable.
    have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * x ^ (-1 + D.ρ)) (Set.Ioi 0) := by
      have h_integrable : ∫ x in Set.Ioi 0, Real.exp (-x) * x ^ (-1 + D.ρ) = Real.Gamma (D.ρ) := by
        rw [ Real.Gamma_eq_integral D.hρ ] ; congr ; ext ; ring;
      exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; linarith [ Real.Gamma_pos_of_pos D.hρ ] );
    -- Since $g$ is continuous, $g(e^{-x})$ is bounded on $(0, \infty)$.
    obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Set.Ioi 0, |g (Real.exp (-x))| ≤ M := by
      have h_bounded : ContinuousOn g (Set.Icc 0 1) := by
        exact hg.continuousOn;
      obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) h_bounded; use M; intro x hx; exact hM _ ⟨ by positivity, Real.exp_le_one_iff.mpr <| neg_nonpos.mpr hx.out.le ⟩ ;
    refine' MeasureTheory.Integrable.mono' ( h_integrable.const_mul M ) _ _;
    · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( hg.comp ( Real.continuous_exp.comp ( ContinuousNeg.continuous_neg ) ) |> Continuous.aestronglyMeasurable ) ( Real.continuous_exp.comp ( ContinuousNeg.continuous_neg ) |> Continuous.aestronglyMeasurable ) ) ( measurable_id.pow_const _ |> Measurable.aestronglyMeasurable );
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by simpa only [ mul_assoc, Real.norm_eq_abs, abs_mul, abs_of_nonneg ( Real.exp_pos _ |> LT.lt.le ), abs_of_nonneg ( Real.rpow_nonneg ( le_of_lt hx ) _ ) ] using mul_le_mul_of_nonneg_right ( hM x hx ) ( mul_nonneg ( Real.exp_pos _ |> LT.lt.le ) ( Real.rpow_nonneg ( le_of_lt hx ) _ ) ) ;

/-
`Jfn` respects scalar multiples.
-/
lemma Jfn_smul (D : KData) (a : ℝ) (f : ℝ → ℝ) :
    Jfn D.ρ D.c (fun y => a * f y) = a * Jfn D.ρ D.c f := by
  unfold Jfn;
  simp +decide only [mul_assoc, mul_left_comm, ← integral_const_mul]

/-! ## From monomials to polynomials to continuous test functions -/

/-
Polynomial moment convergence: `Ifn (eval P) → Jfn (eval P)` for every real polynomial.
-/
lemma Ifn_poly_tendsto (D : KData) (P : Polynomial ℝ) :
    Tendsto (fun lam => Ifn D.p D.ρ lam (fun y => P.eval y)) (𝓝[>] (0:ℝ))
      (𝓝 (Jfn D.ρ D.c (fun y => P.eval y))) := by
  induction' P using Polynomial.induction_on' with p q hp hq;
  · simp_all +decide [ Polynomial.eval_add ];
    refine' Filter.Tendsto.congr' _ ( hp.add hq ) |> fun h => h.trans _;
    · filter_upwards [ self_mem_nhdsWithin ] with lam hl using by rw [ ← Ifn_add D hl _ _ ( Polynomial.continuous _ ) ( Polynomial.continuous _ ) ] ;
    · rw [ ← Jfn_add ];
      · exact p.continuous;
      · exact q.continuous;
  · convert Tendsto.const_mul ‹ℝ› ( Ifn_monomial_tendsto D ‹ℕ› ) using 2 <;> ring;
    · unfold Ifn; norm_num [ mul_assoc, mul_comm, mul_left_comm, ← MeasureTheory.integral_const_mul ] ;
    · convert Jfn_smul D ‹ℝ› ( fun y => y ^ ‹ℕ› ) using 1 ; norm_num ; ring;
      rw [ Jfn_monomial ] ; ring

/-- Weierstrass: a continuous function on `[0,1]` is uniformly approximable by polynomials. -/
lemma exists_poly_approx (φ : ℝ → ℝ) (hφ : Continuous φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℝ, ∀ y ∈ Icc (0:ℝ) 1, |φ y - P.eval y| < ε := by
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn 0 1 φ hφ.continuousOn ε hε
  exact ⟨P, fun y hy => by rw [abs_sub_comm]; exact hP y hy⟩

/-
Continuous test-function convergence: `Ifn φ → Jfn φ` for every continuous `φ`.
-/
lemma Ifn_tendsto_cont (D : KData) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    Tendsto (fun lam => Ifn D.p D.ρ lam φ) (𝓝[>] (0:ℝ)) (𝓝 (Jfn D.ρ D.c φ)) := by
  -- Set `c := D.c` (so `c > 0`). Let `ε' := ε / (2*c + 3)`, so `ε' > 0`.
  have h_eps_prime : ∀ ε > 0, ∃ ε' > 0, ε' * (2 * D.c + 3) = ε := by
    exact fun ε hε => ⟨ ε / ( 2 * D.c + 3 ), div_pos hε ( by linarith [ D.hc ] ), div_mul_cancel₀ _ ( by linarith [ D.hc ] ) ⟩;
  refine' Metric.tendsto_nhds.mpr _;
  intro ε hε_pos
  obtain ⟨ε', hε'_pos, hε'_eq⟩ := h_eps_prime ε hε_pos
  obtain ⟨P, hP⟩ := exists_poly_approx φ hφ hε'_pos
  set ψ : ℝ → ℝ := fun y => φ y - P.eval y
  have hψ_cont : Continuous ψ := by
    exact hφ.sub ( P.continuous )
  have hψ_bound : ∀ y ∈ Set.Icc 0 1, |ψ y| ≤ ε' := by
    exact fun y hy => le_of_lt ( hP y hy );
  filter_upwards [ self_mem_nhdsWithin, Ifn_poly_tendsto D P |> fun h => h.eventually ( Metric.ball_mem_nhds _ hε'_pos ), D.hlim.eventually ( gt_mem_nhds <| show D.c < D.c + 1 by linarith ) ] with lam hlam hlam' hlam'' ; simp_all +decide [ dist_eq_norm ];
  -- By the properties of `Ifn` and `Jfn`, we have:
  have h_ifn_jfn : Ifn D.p D.ρ lam φ = Ifn D.p D.ρ lam (fun y => P.eval y) + Ifn D.p D.ρ lam ψ ∧ Jfn D.ρ D.c φ = Jfn D.ρ D.c (fun y => P.eval y) + Jfn D.ρ D.c ψ := by
    apply And.intro;
    · convert Ifn_add D hlam ( fun y => P.eval y ) ψ P.continuous hψ_cont using 1;
      aesop;
    · convert Jfn_add D ( fun y => P.eval y ) ψ P.continuous hψ_cont using 1 ; aesop;
  -- By the properties of `Ifn` and `Jfn`, we have `|Ifn ψ| ≤ ε' * (lam^D.ρ * lap D.p lam)` and `|Jfn ψ| ≤ ε' * D.c`.
  have h_ifn_jfn_bound : |Ifn D.p D.ρ lam ψ| ≤ ε' * (lam ^ D.ρ * lap D.p lam) ∧ |Jfn D.ρ D.c ψ| ≤ ε' * D.c := by
    exact ⟨ Ifn_abs_le D hlam ψ hψ_cont ε' fun y hy₁ hy₂ => hψ_bound y hy₁.le hy₂, Jfn_bound D ψ ε' fun y hy₁ hy₂ => hψ_bound y hy₁.le hy₂ ⟩;
  exact abs_lt.mpr ⟨ by nlinarith [ abs_lt.mp hlam', abs_le.mp h_ifn_jfn_bound.1, abs_le.mp h_ifn_jfn_bound.2 ], by nlinarith [ abs_lt.mp hlam', abs_le.mp h_ifn_jfn_bound.1, abs_le.mp h_ifn_jfn_bound.2 ] ⟩

/-! ## The one-sided sandwich of the indicator -/

/-- Upper continuous majorant of `phi0` at scale `δ`. -/
noncomputable def phiUpper (δ : ℝ) : ℝ → ℝ := fun y =>
  if Real.exp (-1) ≤ y then 1 / max y (Real.exp (-1))
  else if Real.exp (-1) - δ ≤ y then (Real.exp 1) * (y - (Real.exp (-1) - δ)) / δ
  else 0

/-- Lower continuous minorant of `phi0` at scale `δ`. -/
noncomputable def phiLower (δ : ℝ) : ℝ → ℝ := fun y =>
  if Real.exp (-1) + δ ≤ y then 1 / max y (Real.exp (-1) + δ)
  else if Real.exp (-1) ≤ y then (1 / (Real.exp (-1) + δ)) * (y - Real.exp (-1)) / δ
  else 0

lemma phiUpper_continuous {δ : ℝ} (hδ : 0 < δ) : Continuous (phiUpper δ) := by
  refine' Continuous.if_le _ _ _ _ _;
  · exact Continuous.div continuous_const ( continuous_id.max continuous_const ) fun x => by positivity;
  · apply_rules [ Continuous.if_le ] <;> continuity;
  · exact continuous_const;
  · exact continuous_id;
  · norm_num [ ← Real.exp_neg, hδ.ne' ];
    positivity

lemma phiLower_continuous {δ : ℝ} (hδ : 0 < δ) : Continuous (phiLower δ) := by
  refine' Continuous.if _ _ _;
  · erw [ frontier_Ici ] ; norm_num;
    rw [ if_pos hδ.le, mul_div_cancel_right₀ _ hδ.ne' ];
  · exact continuous_const.div ( continuous_id.max continuous_const ) fun x => by positivity;
  · apply_rules [ Continuous.if_le ] <;> continuity

/-
`phi0 ≤ phiUpper δ` on `(0,1]`.
-/
lemma phi0_le_phiUpper {δ : ℝ} (hδ : 0 < δ) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    phi0 y ≤ phiUpper δ y := by
  unfold phi0 phiUpper;
  split_ifs <;> norm_num;
  · rw [ max_eq_left ‹_› ];
  · exact div_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( by linarith ) ) hδ.le

/-
`phiLower δ ≤ phi0` on `(0,1]`.
-/
lemma phiLower_le_phi0 {δ : ℝ} (hδ : 0 < δ) (y : ℝ) (hy : 0 < y) :
    phiLower δ y ≤ phi0 y := by
  unfold phiLower phi0;
  split_ifs <;> try linarith [ Real.exp_pos ( -1 ) ];
  · rw [ max_eq_left ( by linarith ) ];
  · rw [ div_mul_eq_mul_div, div_div, div_le_div_iff₀ ] <;> nlinarith [ Real.exp_pos ( -1 ), mul_pos hδ hy ]

/-
Uniform (in `δ`) bound `|phiUpper δ y| ≤ e` on `(0,1]`.
-/
lemma phiUpper_le_exp1 {δ : ℝ} (hδ : 0 < δ) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    |phiUpper δ y| ≤ Real.exp 1 := by
  unfold phiUpper; split_ifs <;> norm_num [ abs_of_nonneg, Real.exp_nonneg ];
  · rw [ max_eq_left ‹_›, inv_eq_one_div, div_le_iff₀ ] <;> nlinarith [ Real.exp_pos 1, Real.exp_pos ( -1 ), Real.exp_neg 1, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos 1 ) ) ];
  · rw [ abs_of_nonneg ( div_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( by linarith ) ) hδ.le ) ] ; exact div_le_of_le_mul₀ ( by positivity ) ( by positivity ) ( by nlinarith [ Real.exp_pos 1, Real.exp_pos ( -1 ) ] )

/-
Uniform (in `δ`) bound `|phiLower δ y| ≤ e` on `(0,1]`.
-/
lemma phiLower_le_exp1 {δ : ℝ} (hδ : 0 < δ) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    |phiLower δ y| ≤ Real.exp 1 := by
  unfold phiLower; split_ifs <;> norm_num [ abs_le ];
  · rw [ abs_of_nonneg ( by positivity ), inv_le_comm₀ ] <;> norm_num [ Real.exp_pos ];
    · exact Or.inl ( by rw [ ← Real.exp_neg ] ; linarith [ Real.exp_pos ( -1 ) ] );
    · exact Or.inl hy;
  · field_simp;
    constructor <;> nlinarith [ Real.exp_pos 1, Real.exp_pos ( -1 ), mul_pos ( Real.exp_pos 1 ) hδ, mul_pos ( Real.exp_pos ( -1 ) ) hδ, Real.exp_neg 1, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos 1 ) ) ];
  · positivity

/-
As `δ ↓ 0`, `Jfn (phiUpper δ) → Jfn phi0` (dominated convergence; the jump point is null).
-/
lemma Jfn_phiUpper_tendsto (D : KData) :
    Tendsto (fun δ => Jfn D.ρ D.c (phiUpper δ)) (𝓝[>] (0:ℝ)) (𝓝 (Jfn D.ρ D.c phi0)) := by
  refine' Filter.Tendsto.mul tendsto_const_nhds ( MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _ );
  refine' fun x => Real.exp 1 * Real.exp ( -x ) * x ^ ( D.ρ - 1 );
  · refine' Filter.eventually_of_mem self_mem_nhdsWithin fun δ hδ => Measurable.aestronglyMeasurable _;
    refine' Measurable.mul ( Measurable.mul _ _ ) _;
    · exact Measurable.ite ( measurableSet_Ici.preimage ( Real.continuous_exp.measurable.comp ( measurable_neg ) ) ) ( Measurable.div ( measurable_const ) ( Measurable.max ( Real.continuous_exp.measurable.comp ( measurable_neg ) ) measurable_const ) ) ( Measurable.ite ( measurableSet_Ici.preimage ( Real.continuous_exp.measurable.comp ( measurable_neg ) ) ) ( Measurable.div ( measurable_const.mul ( Real.continuous_exp.measurable.comp ( measurable_neg ) |> Measurable.sub <| measurable_const ) ) measurable_const ) measurable_const );
    · exact Measurable.exp ( measurable_id.neg );
    · exact measurable_id.pow_const _;
  · filter_upwards [ self_mem_nhdsWithin ] with δ hδ ; filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx ; simp_all +decide [ abs_mul, abs_of_nonneg, Real.exp_nonneg ];
    gcongr;
    · exact phiUpper_le_exp1 hδ _ ( Real.exp_pos _ ) ( Real.exp_le_one_iff.mpr ( by linarith ) );
    · rw [ abs_of_nonneg ( Real.rpow_nonneg hx.le _ ) ];
  · have h_gamma : ∫ x in Set.Ioi 0, Real.exp (-x) * x ^ (D.ρ - 1) = Real.Gamma D.ρ := by
      rw [ Real.Gamma_eq_integral D.hρ ];
    simp_all +decide [ mul_assoc, MeasureTheory.integral_const_mul ];
    exact MeasureTheory.Integrable.const_mul ( by exact ( by contrapose! h_gamma; rw [ MeasureTheory.integral_undef h_gamma ] ; linarith [ Real.Gamma_pos_of_pos D.hρ ] ) ) _;
  · refine' MeasureTheory.ae_restrict_mem measurableSet_Ioi |> fun h => h.mono fun x hx => _;
    by_cases h : Real.exp ( -1 ) ≤ Real.exp ( -x ) <;> simp_all +decide [ phiUpper, phi0 ];
    rw [ if_neg ( by linarith ) ];
    rw [ Filter.tendsto_congr' ( by filter_upwards [ Ioo_mem_nhdsGT ( show 0 < Real.exp ( -1 ) - Real.exp ( -x ) by exact sub_pos.mpr <| Real.exp_lt_exp.mpr <| by linarith ) ] with n hn; rw [ if_neg <| by linarith, if_neg <| by linarith [ hn.1, hn.2 ] ] ) ] ; norm_num

/-
As `δ ↓ 0`, `Jfn (phiLower δ) → Jfn phi0` (dominated convergence; the jump point is null).
-/
lemma Jfn_phiLower_tendsto (D : KData) :
    Tendsto (fun δ => Jfn D.ρ D.c (phiLower δ)) (𝓝[>] (0:ℝ)) (𝓝 (Jfn D.ρ D.c phi0)) := by
  refine' ( tendsto_const_nhds.mul _ );
  refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
  refine' fun x => Real.exp 1 * ( Real.exp ( -x ) * x ^ ( D.ρ - 1 ) );
  · filter_upwards [ self_mem_nhdsWithin ] with δ hδ;
    refine' Measurable.aestronglyMeasurable _;
    apply_rules [ Measurable.mul, Measurable.ite, measurable_const ];
    exacts [ measurableSet_le measurable_const ( Real.continuous_exp.measurable.comp measurable_neg ), Measurable.inv ( Measurable.max ( Real.continuous_exp.measurable.comp measurable_neg ) measurable_const ), measurableSet_le measurable_const ( Real.continuous_exp.measurable.comp measurable_neg ), Measurable.sub ( Real.continuous_exp.measurable.comp measurable_neg ) measurable_const, Real.continuous_exp.measurable.comp measurable_neg, measurable_id.pow_const _ ];
  · refine' Filter.eventually_of_mem self_mem_nhdsWithin fun δ hδ => Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioi ) fun x hx => _;
    convert mul_le_mul_of_nonneg_right ( phiLower_le_exp1 hδ ( Real.exp ( -x ) ) ( Real.exp_pos _ ) ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr hx.out.le ) ) ( mul_nonneg ( Real.exp_nonneg ( -x ) ) ( Real.rpow_nonneg hx.out.le ( D.ρ - 1 ) ) ) using 1;
    rw [ Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg ( Real.exp_pos _ |> le_of_lt ), abs_of_nonneg ( Real.rpow_nonneg ( le_of_lt hx ) _ ) ] ; ring;
  · have h_gamma : ∫ x in Set.Ioi 0, Real.exp (-x) * x ^ (D.ρ - 1) = Real.Gamma D.ρ := by
      rw [ Real.Gamma_eq_integral D.hρ ];
    exact MeasureTheory.Integrable.const_mul ( by exact ( by contrapose! h_gamma; rw [ MeasureTheory.integral_undef h_gamma ] ; linarith [ Real.Gamma_pos_of_pos D.hρ ] ) ) _;
  · refine' MeasureTheory.measure_mono_null _ ( MeasureTheory.measure_singleton 1 );
    intro x hx; contrapose! hx; simp_all +decide [ phiLower, phi0 ] ;
    cases lt_or_gt_of_ne hx;
    · rw [ if_pos ( by linarith ) ];
      refine' Filter.Tendsto.congr' _ tendsto_const_nhds;
      filter_upwards [ Ioo_mem_nhdsGT ( show 0 < Real.exp ( -x ) - Real.exp ( -1 ) by exact sub_pos.mpr ( Real.exp_lt_exp.mpr ( by linarith ) ) ) ] with n hn using by rw [ if_pos ( by linarith [ hn.1, hn.2 ] ) ] ;
    · rw [ if_neg ( by linarith ) ];
      refine' tendsto_const_nhds.congr' _;
      filter_upwards [ self_mem_nhdsWithin ] with n hn using by rw [ if_neg ( by linarith [ Real.exp_lt_exp.2 ( show -x < -1 by linarith ), hn.out ] ), if_neg ( by linarith ) ] ;

/-
The `phi0` weighted integrand is integrable on `(0,∞)`.
-/
lemma integrableOn_phi0 (D : KData) {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn
      (fun t => phi0 (Real.exp (-(lam * t))) * Real.exp (-(lam * t)) * D.p t) (Ioi 0) := by
  refine' MeasureTheory.Integrable.mono' ( integrableOn_weighted _ hlam ( phiUpper ( Real.exp ( -1 ) / 2 ) ) ( phiUpper_continuous ( by positivity ) ) ) _ _;
  exact D;
  · refine' MeasureTheory.AEStronglyMeasurable.mul _ _;
    · refine' Measurable.aestronglyMeasurable _;
      exact Measurable.mul ( Measurable.ite ( measurableSet_Ici.preimage ( Real.continuous_exp.measurable.comp ( measurable_neg.comp ( measurable_const.mul measurable_id' ) ) ) ) ( measurable_const.div ( Real.continuous_exp.measurable.comp ( measurable_neg.comp ( measurable_const.mul measurable_id' ) ) ) ) measurable_const ) ( Real.continuous_exp.measurable.comp ( measurable_neg.comp ( measurable_const.mul measurable_id' ) ) );
    · have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-(lam * t)) * D.p t) (Set.Ioi (0:ℝ)) :=
        D.hint lam hlam
      have := h_integrable.aestronglyMeasurable;
      convert this.mul ( Continuous.aestronglyMeasurable ( show Continuous fun t => Real.exp ( lam * t ) from Real.continuous_exp.comp <| continuous_const.mul continuous_id' ) ) using 1 ; ext1 t ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Real.exp_neg ];
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht;
    convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( phi0_le_phiUpper ( by positivity : ( 0 : ℝ ) < Real.exp ( -1 ) / 2 ) ( Real.exp ( - ( lam * t ) ) ) ( by positivity ) ( Real.exp_le_one_iff.mpr ( by nlinarith [ ht.out ] ) ) ) ( Real.exp_nonneg ( - ( lam * t ) ) ) ) ( D.hp t ht.out.le ) using 1 ; norm_num [ abs_of_nonneg, Real.exp_nonneg, mul_assoc ];
    rw [ abs_of_nonneg ( show 0 ≤ phi0 ( Real.exp ( - ( lam * t ) ) ) from by unfold phi0; split_ifs <;> positivity ), abs_of_nonneg ( show 0 ≤ D.p t from D.hp t ht.out.le ) ]

/-
`Ifn phi0 ≤ Ifn g` for continuous `g ≥ phi0` on `(0,1]`.
-/
lemma Ifn_phi0_le_cont (D : KData) {lam : ℝ} (hlam : 0 < lam) (g : ℝ → ℝ) (hg : Continuous g)
    (h : ∀ y : ℝ, 0 < y → y ≤ 1 → phi0 y ≤ g y) :
    Ifn D.p D.ρ lam phi0 ≤ Ifn D.p D.ρ lam g := by
  refine' mul_le_mul_of_nonneg_left _ ( Real.rpow_nonneg hlam.le _ );
  refine' MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioi fun t ht => mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( h _ ( Real.exp_pos _ ) ( Real.exp_le_one_iff.mpr <| by nlinarith [ ht.out ] ) ) <| Real.exp_nonneg _ ) <| D.hp _ ht.out.le;
  · convert integrableOn_phi0 D hlam using 1;
  · convert integrableOn_weighted D hlam g hg using 1

/-
`Ifn g ≤ Ifn phi0` for continuous `g ≤ phi0` on `(0,1]`.
-/
lemma Ifn_cont_le_phi0 (D : KData) {lam : ℝ} (hlam : 0 < lam) (g : ℝ → ℝ) (hg : Continuous g)
    (h : ∀ y : ℝ, 0 < y → y ≤ 1 → g y ≤ phi0 y) :
    Ifn D.p D.ρ lam g ≤ Ifn D.p D.ρ lam phi0 := by
  refine' mul_le_mul_of_nonneg_left ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioi fun t ht => _ ) ( Real.rpow_nonneg hlam.le _ );
  · exact integrableOn_weighted D hlam g hg;
  · convert integrableOn_phi0 D hlam using 1;
  · exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( h _ ( Real.exp_pos _ ) ( Real.exp_le_one_iff.mpr ( by nlinarith [ ht.out ] ) ) ) ( Real.exp_nonneg _ ) ) ( D.hp _ ht.out.le )

/-! ## `Ifn` / `Jfn` of `phi0`, and the squeeze -/

/-
`Ifn p ρ λ phi0 = λ^ρ · ∫₀^{1/λ} p`.
-/
lemma Ifn_phi0_eq (D : KData) {lam : ℝ} (hlam : 0 < lam) :
    Ifn D.p D.ρ lam phi0 = lam ^ D.ρ * ∫ t in (0:ℝ)..(1 / lam), D.p t := by
  rw [ intervalIntegral.integral_of_le ( by positivity ), ← MeasureTheory.integral_indicator ];
  · have h_indicator : ∀ t ∈ Set.Ioi 0, phi0 (Real.exp (-(lam * t))) * Real.exp (-(lam * t)) * D.p t = (Set.Ioc 0 (1 / lam)).indicator D.p t := by
      intro t ht;
      by_cases h : t ≤ 1 / lam <;> simp_all +decide [ phi0 ];
      · exact fun h' => False.elim <| h'.not_ge <| by nlinarith [ mul_inv_cancel₀ hlam.ne' ] ;
      · exact fun h' => False.elim <| h.not_ge <| by nlinarith [ mul_inv_cancel₀ hlam.ne' ] ;
    convert congr_arg ( fun x => lam ^ D.ρ * x ) ( MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_indicator ) using 1;
    rw [ MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ] ; aesop;
  · norm_num

/-
`Jfn ρ c phi0 = c/Γ(ρ+1)`.
-/
lemma Jfn_phi0_eq (D : KData) :
    Jfn D.ρ D.c phi0 = D.c / Real.Gamma (D.ρ + 1) := by
  unfold Jfn phi0;
  rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ];
  change D.c / Real.Gamma D.ρ * ∫ x in Set.Ioc 0 1, x ^ ( D.ρ - 1 ) ∂volume.restrict ( Ioi 0 ) = D.c / Real.Gamma ( D.ρ + 1 );
  · rw [ MeasureTheory.Measure.restrict_restrict_of_subset ( Set.Ioc_subset_Ioi_self ), ← intervalIntegral.integral_of_le zero_le_one, integral_rpow ] <;> norm_num;
    · rw [ Real.zero_rpow ( ne_of_gt D.hρ ), sub_zero, Real.Gamma_add_one ( ne_of_gt D.hρ ) ] ; ring;
    · exact D.hρ;
  · norm_num;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx;
    split_ifs <;> simp_all +decide [ Real.exp_pos, ne_of_gt, Real.exp_le_exp ]

/-
The squeeze: `Ifn phi0 → Jfn phi0`.
-/
lemma Ifn_phi0_tendsto (D : KData) :
    Tendsto (fun lam => Ifn D.p D.ρ lam phi0) (𝓝[>] (0:ℝ)) (𝓝 (Jfn D.ρ D.c phi0)) := by
  refine' Metric.tendsto_nhds.mpr _;
  intro ε hε;
  -- Choose δ₁ and δ₂ such that |Jfn D.ρ D.c (phiUpper δ₁) - Jfn D.ρ D.c phi0| < ε / 2 and |Jfn D.ρ D.c (phiLower δ₂) - Jfn D.ρ D.c phi0| < ε / 2.
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, |Jfn D.ρ D.c (phiUpper δ₁) - Jfn D.ρ D.c phi0| < ε / 2 := by
    have := Metric.tendsto_nhdsWithin_nhds.mp ( Jfn_phiUpper_tendsto D ) ( ε / 2 ) ( half_pos hε );
    exact ⟨ this.choose / 2, half_pos this.choose_spec.1, this.choose_spec.2 ( show 0 < this.choose / 2 by linarith [ this.choose_spec.1 ] ) ( by rw [ dist_eq_norm ] ; exact abs_lt.mpr ⟨ by linarith [ this.choose_spec.1 ], by linarith [ this.choose_spec.1 ] ⟩ ) ⟩
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, |Jfn D.ρ D.c (phiLower δ₂) - Jfn D.ρ D.c phi0| < ε / 2 := by
    have := Jfn_phiLower_tendsto D;
    have := this.eventually ( Metric.ball_mem_nhds _ <| half_pos hε ) ; have := this.and self_mem_nhdsWithin; obtain ⟨ δ₂, hδ₂₁, hδ₂₂ ⟩ := this.exists; exact ⟨ δ₂, hδ₂₂, hδ₂₁ ⟩ ;
  -- By the properties of the integrals and the definitions of `phiUpper` and `phiLower`, we have:
  have h_bounds : ∀ᶠ lam in 𝓝[>] 0, Ifn D.p D.ρ lam (phiLower δ₂) ≤ Ifn D.p D.ρ lam phi0 ∧ Ifn D.p D.ρ lam phi0 ≤ Ifn D.p D.ρ lam (phiUpper δ₁) := by
    filter_upwards [ self_mem_nhdsWithin ] with lam hlam;
    exact ⟨ Ifn_cont_le_phi0 D hlam _ ( phiLower_continuous hδ₂_pos ) fun y hy _ => phiLower_le_phi0 hδ₂_pos y hy, Ifn_phi0_le_cont D hlam _ ( phiUpper_continuous hδ₁_pos ) fun y hy hy1 => phi0_le_phiUpper hδ₁_pos y hy hy1 ⟩;
  filter_upwards [ h_bounds, ( Ifn_tendsto_cont D ( phiUpper δ₁ ) ( phiUpper_continuous hδ₁_pos ) ) |> fun h => h.eventually ( Metric.ball_mem_nhds _ <| half_pos hε ), ( Ifn_tendsto_cont D ( phiLower δ₂ ) ( phiLower_continuous hδ₂_pos ) ) |> fun h => h.eventually ( Metric.ball_mem_nhds _ <| half_pos hε ) ] with lam hl₁ hl₂ hl₃;
  exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp hδ₁, abs_lt.mp hδ₂, abs_lt.mp hl₂, abs_lt.mp hl₃ ], by linarith [ abs_lt.mp hδ₁, abs_lt.mp hδ₂, abs_lt.mp hl₂, abs_lt.mp hl₃ ] ⟩

/-! ## Main theorem (constant-`L` Tauberian direction) -/

/-
The occupation-integral asymptotics, in `Tendsto` form:
`s^{-ρ} · ∫₀ˢ p → c/Γ(ρ+1)` as `s → ∞`.
-/
lemma tauberian_tendsto (D : KData) :
    Tendsto (fun s => s ^ (-D.ρ) * ∫ t in (0:ℝ)..s, D.p t) atTop
      (𝓝 (D.c / Real.Gamma (D.ρ + 1))) := by
  -- By definition of $Jfn$, we know that $Jfn D.ρ D.c phi0 = D.c / Real.Gamma (D.ρ + 1)$.
  have hJfn : Filter.Tendsto (fun s : ℝ => Ifn D.p D.ρ (1 / s) phi0) Filter.atTop (nhds (D.c / Real.Gamma (D.ρ + 1))) := by
    convert Filter.Tendsto.comp ( Ifn_phi0_tendsto D ) _ using 2;
    · exact Jfn_phi0_eq D ▸ rfl;
    · exact tendsto_nhdsWithin_iff.mpr ⟨ tendsto_const_nhds.div_atTop Filter.tendsto_id, Filter.eventually_atTop.mpr ⟨ 1, fun x hx => by norm_num; linarith ⟩ ⟩;
  refine' hJfn.congr' _;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with s hs;
  convert Ifn_phi0_eq D ( one_div_pos.mpr hs ) using 1 ; norm_num [ Real.rpow_neg hs.le ];
  exact Or.inl ( by rw [ Real.inv_rpow hs.le ] )

/-
The occupation-integral asymptotics, in `IsEquivalent` form.
-/
theorem tauberian_isEquivalent (D : KData) :
    IsEquivalent atTop (fun s => ∫ t in (0:ℝ)..s, D.p t)
      (fun s => D.c * s ^ D.ρ / Real.Gamma (D.ρ + 1)) := by
  rw [ Asymptotics.isEquivalent_iff_tendsto_one ];
  · convert Filter.Tendsto.congr' _ ( ( tauberian_tendsto D ) |> Filter.Tendsto.const_mul ( Real.Gamma ( D.ρ + 1 ) / D.c ) ) using 1;
    · rw [ div_mul_div_cancel₀ ( ne_of_gt D.hc ), div_self ( ne_of_gt ( Real.Gamma_pos_of_pos ( add_pos D.hρ zero_lt_one ) ) ) ];
    · filter_upwards [ Filter.eventually_gt_atTop 0 ] with s hs;
      simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Real.rpow_neg hs.le, ne_of_gt D.hc, ne_of_gt ( Real.Gamma_pos_of_pos ( add_pos D.hρ zero_lt_one ) ) ];
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using div_ne_zero ( mul_ne_zero D.hc.ne' ( ne_of_gt ( Real.rpow_pos_of_pos hx _ ) ) ) ( ne_of_gt ( Real.Gamma_pos_of_pos ( add_pos D.hρ zero_lt_one ) ) )

/-! ## Deriving the integrability hypothesis from a nonvanishing Laplace transform -/

/-
If the Laplace transform `ω` is eventually nonzero near `0`, then `e^{−λt}p(t)` is integrable
for every `λ > 0`.  (If it were not integrable for some `λ`, the Bochner integral defining `ω`
would vanish there, so nonvanishing forces integrability; domination `e^{−λt} ≤ e^{−λ₀t}` for
`λ ≥ λ₀` propagates it to all `λ > 0`.)
-/
lemma integrableOn_exp_mul_of_eventually_ne (p ω : ℝ → ℝ)
    (hω : ∀ lam, 0 < lam → ω lam = ∫ t in Ioi (0:ℝ), Real.exp (-(lam * t)) * p t)
    (hne : ∀ᶠ lam in 𝓝[>] (0:ℝ), ω lam ≠ 0) :
    ∀ lam : ℝ, 0 < lam → IntegrableOn (fun t => Real.exp (-(lam * t)) * p t) (Ioi 0) := by
  intro lam hl;
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, 0 < l₀ ∧ l₀ < lam ∧ ω l₀ ≠ 0 := by
    rcases ( hne.and ( Ioo_mem_nhdsGT hl ) ) with h ; obtain ⟨ l₀, hl₀₁, hl₀₂ ⟩ := h.exists ; exact ⟨ l₀, hl₀₂.1, hl₀₂.2, hl₀₁ ⟩ ;
  have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.exp (-(l₀ * t)) * p t) (Set.Ioi 0) := by
    exact ( by by_contra h; rw [ hω l₀ hl₀.1, MeasureTheory.integral_undef h ] at hl₀; aesop );
  refine' h_integrable.norm.mono' _ _;
  · have := h_integrable.aestronglyMeasurable;
    convert this.mul ( Continuous.aestronglyMeasurable ( show Continuous fun t => Real.exp ( - ( lam * t ) ) / Real.exp ( - ( l₀ * t ) ) from by exact Continuous.div ( Real.continuous_exp.comp <| by continuity ) ( Real.continuous_exp.comp <| by continuity ) fun t => by positivity ) ) using 1 ; ext t ; by_cases h : t = 0 <;> simp +decide [ h, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by simpa [ abs_mul ] using mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr <| by nlinarith [ ht.out ] ) <| abs_nonneg <| p t;

end TypeDDecouplingKaramata