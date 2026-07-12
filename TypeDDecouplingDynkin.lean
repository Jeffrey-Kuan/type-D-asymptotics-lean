import Mathlib

/-!
# `lem:dynkin` — the Dynkin martingale, de-opaqued

This file replaces the former `opaque` encoding of the Dynkin decomposition
(`dynkinIsMart`, `dynkinBracket` in `TypeDDecouplingEW.lean`) by genuine content, following
the `asepKernel`/Bethe fidelity-repair precedent.

For a Markov process `η_t = proc t` with (bounded) generator `L` and Feller semigroup `P`,
and a real-indexed filtration `ℱ`, the **Dynkin martingale** of a local function `f` is
`M^f_t = f(η_t) − f(η_0) − ∫₀ᵗ (Lf)(η_s) ds`.

* **Part 1 (`dynkin_martingale`), PROVED.**  `M^f` is a genuine `MeasureTheory.Martingale`
  for `ℱ` and `μ`.  The proof is the classical tower-property + conditional-Fubini
  computation, run against the faithful Markov–Feller hypothesis bundle (Markov property via
  the semigroup `P`, the Kolmogorov identity `P_t f − f = ∫₀ᵗ P_s(Lf) ds`, and the
  boundedness/measurability facts a Feller jump process with bounded generator possesses).

* **Part 2 (bracket), definitional + `L²` content.**  Mathlib has no continuous-time
  predictable quadratic covariation, so the identity `⟨M^f,M^g⟩_t = ∫₀ᵗ Γ(f,g)(η_s) ds`
  cannot be *stated* against a library object.  We therefore **define** `dynkinBracketDef`
  to be that integral; identifying it with the true predictable bracket is the cited
  classical fact (Ethier–Kurtz Ch. 4 / Dellacherie–Meyer), exactly as `asepKernel`'s
  identification rests on Schütz.  In addition we prove the honest, library-accessible
  `L²`-level content, the integrated covariance identity
  `E[M^f_t M^g_t] = E[∫₀ᵗ Γ(f,g)(η_s) ds]` (`dynkin_L2`).

All hypotheses of the bundle are standard facts for a Feller jump process with bounded
generator on a probability space; they are documented field by field and are simultaneously
satisfiable.
-/

open scoped BigOperators Real Topology
open MeasureTheory Filter

namespace TypeDDecoupling

/-- The carré du champ of a Markov generator `L`: `Γ(f,g) = L(fg) − f·Lg − g·Lf`. -/
def carreDuChamp {S : Type*} (L : (S → ℝ) → S → ℝ) (f g : S → ℝ) : S → ℝ :=
  fun s => L (fun s' => f s' * g s') s - f s * L g s - g s * L f s

/-- The Dynkin martingale of a local function `f`:
`M^f_t = f(η_t) − f(η_0) − ∫₀ᵗ (Lf)(η_s) ds`. -/
noncomputable def dynkinM {S Ω : Type*} (L : (S → ℝ) → S → ℝ) (proc : ℝ → Ω → S) (f : S → ℝ) :
    ℝ → Ω → ℝ :=
  fun t ω => f (proc t ω) - f (proc 0 ω) - ∫ s in (0:ℝ)..t, L f (proc s ω)

/-- The predictable cross-bracket `⟨M^f,M^g⟩`, **defined** (there is no Mathlib object to
pin it to) as `∫₀ᵗ Γ(f,g)(η_s) ds`.  Identifying this with the true predictable quadratic
covariation is the cited classical fact (Ethier–Kurtz Ch. 4). -/
noncomputable def dynkinBracketDef {S Ω : Type*} (L : (S → ℝ) → S → ℝ) (proc : ℝ → Ω → S)
    (f g : S → ℝ) : ℝ → Ω → ℝ :=
  fun t ω => ∫ s in (0:ℝ)..t, carreDuChamp L f g (proc s ω)

/-! ## Conditional Fubini over a time interval

The one genuinely non-trivial analytic input to Part 1: the time integral can be pulled
through a conditional expectation.  This is the standard consequence of joint integrability
(Tonelli/Fubini) plus the defining set-integral property of conditional expectation. -/

/-
**Conditional Fubini.**  For `a ≤ b`, if `g` and `k` are jointly integrable on
`Ioc a b × Ω`, the parameter-conditional expectations agree `μ[g u | m] =ᵐ k u`, and the
integrated `k` is `m`-measurable, then
`μ[fun ω => ∫ u in a..b, g u ω | m] =ᵐ fun ω => ∫ u in a..b, k u ω`.
-/
theorem condExp_intervalIntegral_ae_eq
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ) (μ : Measure Ω)
    [IsFiniteMeasure μ] {a b : ℝ} (hab : a ≤ b) (g k : ℝ → Ω → ℝ)
    (hg : Integrable (Function.uncurry g) ((volume.restrict (Set.Ioc a b)).prod μ))
    (hk : Integrable (Function.uncurry k) ((volume.restrict (Set.Ioc a b)).prod μ))
    (hg_slice : ∀ u ∈ Set.Ioc a b, Integrable (g u) μ)
    (hk_meas : StronglyMeasurable[m] (fun ω => ∫ u in a..b, k u ω))
    (hcond : ∀ u ∈ Set.Ioc a b, μ[g u | m] =ᵐ[μ] k u) :
    μ[fun ω => ∫ u in a..b, g u ω | m] =ᵐ[μ] fun ω => ∫ u in a..b, k u ω := by
  refine' ( ae_eq_condExp_of_forall_setIntegral_eq _ _ _ _ hk_meas.aestronglyMeasurable ).symm;
  · assumption;
  · convert hg.integral_prod_right using 1;
    simp +decide [ intervalIntegral.integral_of_le hab ];
  · intro s hs _;
    have h_integrable : MeasureTheory.Integrable (fun ω => ∫ u in Set.Ioc a b, k u ω) μ := by
      convert hk.integral_prod_right using 1;
    simpa only [ intervalIntegral.integral_of_le hab ] using h_integrable.integrableOn;
  · intro s hs hμs
    have h_fubini_k : ∫ ω in s, ∫ u in a..b, k u ω ∂MeasureTheory.volume ∂μ = ∫ u in a..b, ∫ ω in s, k u ω ∂μ := by
      rw [ intervalIntegral.integral_of_le hab, MeasureTheory.integral_integral_swap ];
      · simp +decide only [intervalIntegral.integral_of_le hab];
      · refine' hk.mono_measure _;
        rw [ MeasureTheory.Measure.le_iff ];
        intro t ht; rw [ MeasureTheory.Measure.prod_apply ht, MeasureTheory.Measure.prod_apply ht ] ;
        exact MeasureTheory.lintegral_mono fun x => MeasureTheory.Measure.restrict_apply_le _ _
    have h_fubini_g : ∫ ω in s, ∫ u in a..b, g u ω ∂MeasureTheory.volume ∂μ = ∫ u in a..b, ∫ ω in s, g u ω ∂μ := by
      rw [ intervalIntegral.integral_of_le hab, MeasureTheory.integral_integral_swap ];
      · simp +decide only [intervalIntegral.integral_of_le hab];
      · refine' hg.mono_measure _;
        simp +decide [ MeasureTheory.Measure.le_iff ];
        intro t ht; rw [ MeasureTheory.Measure.prod_apply ht, MeasureTheory.Measure.prod_apply ht ] ;
        exact MeasureTheory.lintegral_mono fun x => MeasureTheory.Measure.restrict_apply_le _ _
    simp_all +decide [ intervalIntegral.integral_of_le hab ];
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun u hu => _;
    rw [ ← MeasureTheory.integral_congr_ae ( MeasureTheory.ae_restrict_of_ae ( hcond u hu.1 hu.2 ) ) ];
    apply_rules [ MeasureTheory.setIntegral_condExp ];
    · exact hu.1;
    · linarith [ hu.2 ]

/-! ## Part 1: the martingale property -/

/-
**Part 1 of `lem:dynkin` (PROVED).**  The Dynkin martingale `M^f` is a genuine
`MeasureTheory.Martingale` for the filtration `ℱ` and measure `μ`.

Hypothesis bundle (each a standard fact for a Feller jump process with bounded generator):
* `hf_adapted`, `hInt_adapted` : `f(η_t)` and `∫₀ᵗ Lf(η_s) ds` are `ℱ_t`-measurable
  (adaptedness of the process and joint measurability of `(s,ω) ↦ Lf(η_s)`);
* `hft_int`, `hf0_int`, `hJ_int` : integrability of `f(η_t)`, `f(η_0)` and the drift term
  (boundedness of `f`, `Lf`);
* `hMarkov_f`, `hMarkov_Lf` : the Markov property `μ[h(η_t) | ℱ_s] = (P_{t-s} h)(η_s)` for
  `h ∈ {f, Lf}`;
* `hKol` : the Kolmogorov identity `P_τ f − f = ∫₀^τ P_r(Lf) dr`;
* `hLf_jointInt`, `hPLf_jointInt`, `hbracketMeas` : the joint integrability and
  `ℱ_s`-measurability needed for the conditional Fubini step.
-/
theorem dynkin_martingale
    {S Ω : Type*} [MeasurableSpace S] {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ mΩ)
    (proc : ℝ → Ω → S) (L : (S → ℝ) → S → ℝ) (P : ℝ → (S → ℝ) → S → ℝ)
    (f : S → ℝ)
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
        (fun ω => ∫ u in s..t, P (u - s) (L f) (proc s ω))) :
    Martingale (dynkinM L proc f) ℱ μ := by
  constructor ; intro t ; simp_all +decide [ dynkinM ] ; (
  exact MeasureTheory.StronglyMeasurable.sub ( MeasureTheory.StronglyMeasurable.sub ( hf_adapted t ) ( hf0_adapt t ) ) ( hInt_adapted t ));
  intro s t hst
  have h_condExp : μ[fun ω => ∫ u in (0:ℝ)..t, L f (proc u ω) | ℱ s] =ᵐ[μ] fun ω => (∫ u in (0:ℝ)..s, L f (proc u ω)) + (∫ u in (s:ℝ)..t, P (u - s) (L f) (proc s ω)) := by
    have h_condExp : μ[fun ω => ∫ u in (s:ℝ)..t, L f (proc u ω) | ℱ s] =ᵐ[μ] fun ω => ∫ u in (s:ℝ)..t, P (u - s) (L f) (proc s ω) := by
      convert condExp_intervalIntegral_ae_eq ( ℱ.le s ) μ hst ( fun u ω => L f ( proc u ω ) ) ( fun u ω => P ( u - s ) ( L f ) ( proc s ω ) ) ( hLf_jointInt s t hst ) ( hPLf_jointInt s t hst ) ( fun u hu => hLf_slice u ) ( hbracketMeas s t ) ( fun u hu => hMarkov_Lf s u hu.1.le ) using 1;
    have h_condExp : μ[fun ω => (∫ u in (0:ℝ)..s, L f (proc u ω)) + (∫ u in s..t, L f (proc u ω)) | ℱ s] =ᵐ[μ] fun ω => (∫ u in (0:ℝ)..s, L f (proc u ω)) + (∫ u in s..t, P (u - s) (L f) (proc s ω)) := by
      have h_condExp : μ[fun ω => (∫ u in (0:ℝ)..s, L f (proc u ω)) + (∫ u in s..t, L f (proc u ω)) | ℱ s] =ᵐ[μ] fun ω => (∫ u in (0:ℝ)..s, L f (proc u ω)) + μ[fun ω => ∫ u in s..t, L f (proc u ω) | ℱ s] ω := by
        convert MeasureTheory.condExp_add _ _ _ using 1;
        · ext ω; simp +decide [ MeasureTheory.condExp_of_stronglyMeasurable ( ℱ.le s ) ( hInt_adapted s ) ( hJ_int s ) ] ;
        · exact hJ_int s;
        · convert hJ_int t |> fun h => h.sub ( hJ_int s ) using 1 ; ext ω ; simp +decide [ intervalIntegral.integral_of_le hst ];
          rw [ ← intervalIntegral.integral_of_le hst, intervalIntegral.integral_interval_sub_left ];
          · exact hLf_ii ω 0 t;
          · exact hLf_ii ω 0 s;
      filter_upwards [ h_condExp, ‹μ[fun ω => ∫ u in s..t, L f (proc u ω) | ℱ s] =ᶠ[ae μ] fun ω => ∫ u in s..t, P (u - s) (L f) (proc s ω)› ] with ω hω₁ hω₂ using by simpa only [ hω₂ ] using hω₁;
    convert h_condExp using 1;
    exact congr_arg _ ( funext fun ω => by rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ hLf_ii ] )
  generalize_proofs at *; (
  have h_condExp_split : μ[fun ω => f (proc t ω) - f (proc 0 ω) - ∫ u in (0:ℝ)..t, L f (proc u ω) | ℱ s] =ᵐ[μ] fun ω => (P (t - s) f (proc s ω)) - f (proc 0 ω) - ((∫ u in (0:ℝ)..s, L f (proc u ω)) + (∫ u in (s:ℝ)..t, P (u - s) (L f) (proc s ω))) := by
    have h_condExp_split : μ[fun ω => f (proc t ω) - f (proc 0 ω) - ∫ u in (0:ℝ)..t, L f (proc u ω) | ℱ s] =ᵐ[μ] μ[fun ω => f (proc t ω) | ℱ s] - μ[fun ω => f (proc 0 ω) | ℱ s] - μ[fun ω => ∫ u in (0:ℝ)..t, L f (proc u ω) | ℱ s] := by
      have h_condExp_split : ∀ {g h k : Ω → ℝ}, MeasureTheory.Integrable g μ → MeasureTheory.Integrable h μ → MeasureTheory.Integrable k μ → μ[g - h - k | ℱ s] =ᵐ[μ] μ[g | ℱ s] - μ[h | ℱ s] - μ[k | ℱ s] := by
        intro g h k hg hh hk; simp +decide only [sub_eq_add_neg] ; (
        have := MeasureTheory.condExp_add ( hg ) ( hh.neg ) ; have := MeasureTheory.condExp_add ( hg.add hh.neg ) ( hk.neg ) ; simp_all +decide [ MeasureTheory.condExp_neg ] ;
        filter_upwards [ this ( ℱ s ), ‹∀ m : MeasurableSpace Ω, μ[g + -h | m] =ᶠ[ae μ] μ[g | m] + μ[-h | m]› ( ℱ s ), MeasureTheory.condExp_neg h ( ℱ s ), MeasureTheory.condExp_neg k ( ℱ s ) ] with ω hω₁ hω₂ hω₃ hω₄ using by aesop;)
      generalize_proofs at *; (
      exact h_condExp_split ( hft_int t ) ( hf0_int ) ( hJ_int t ))
    generalize_proofs at *; (
    filter_upwards [ h_condExp_split, hMarkov_f s t hst, h_condExp, show μ[fun ω => f (proc 0 ω) | ℱ s] =ᵐ[μ] fun ω => f (proc 0 ω) from by
                                                                      rw [ MeasureTheory.condExp_of_stronglyMeasurable ] <;> aesop ( simp_config := { singlePass := true } ) ; ] with ω hω₁ hω₂ hω₃ hω₄
    generalize_proofs at *; (
    aesop))
  generalize_proofs at *; (
  convert h_condExp_split using 1
  generalize_proofs at *; (
  ext ω; simp +decide [ dynkinM ] ; ring;
  rw [ show ∫ u in s..t, P ( -s + u ) ( L f ) ( proc s ω ) = ∫ u in ( 0 : ℝ )..t - s, P u ( L f ) ( proc s ω ) by convert intervalIntegral.integral_comp_sub_right _ s using 3 <;> ring ] ; linarith [ hKol ( t - s ) ( proc s ω ) ( sub_nonneg.mpr hst ) ] ;)))

/-! ## Part 2: the `L²` integrated-covariance identity -/

/-
**Auxiliary (integration by parts).**  For interval-integrable `φ ψ` the product of the
two running integrals is the symmetric integral of `(∫₀ˢφ)·ψ(s) + (∫₀ˢψ)·φ(s)`.  This is the
`ω`-pointwise identity behind the drift–drift term of the `L²` computation.
-/
theorem intervalIntegral_mul_eq_ibp (φ ψ : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hφ : IntervalIntegrable φ volume 0 t) (hψ : IntervalIntegrable ψ volume 0 t) :
    (∫ s in (0:ℝ)..t, φ s) * (∫ s in (0:ℝ)..t, ψ s)
      = ∫ s in (0:ℝ)..t,
          ((∫ r in (0:ℝ)..s, φ r) * ψ s + (∫ r in (0:ℝ)..s, ψ r) * φ s) := by
  rw [ intervalIntegral.integral_add ];
  · -- By Fubini's theorem, we can interchange the order of integration.
    have h_fubini : ∫ x in (0:ℝ)..t, (∫ r in (0:ℝ)..x, φ r) * ψ x = ∫ r in (0:ℝ)..t, φ r * (∫ x in (r:ℝ)..t, ψ x) := by
      have h_fubini : ∫ x in Set.Ioc 0 t, (∫ r in (0:ℝ)..x, φ r) * ψ x = ∫ r in Set.Ioc 0 t, ∫ x in Set.Ioc r t, φ r * ψ x := by
        have h_fubini : ∫ x in Set.Ioc 0 t, (∫ r in (0:ℝ)..x, φ r) * ψ x = ∫ x in Set.Ioc 0 t, ∫ r in Set.Ioc 0 t, (if r ≤ x then φ r * ψ x else 0) := by
          refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => _;
          rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
          rw [ intervalIntegral.integral_of_le hx.1.le, ← MeasureTheory.integral_mul_const ];
          rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
          grind;
        rw [ h_fubini, ← MeasureTheory.integral_integral_swap ];
        · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => _;
          rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
          rw [ ← MeasureTheory.integral_congr_ae ];
          filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton x ) ] with y hy;
          grind;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · exact MeasureTheory.Integrable.mul_prod ( by simpa only [ intervalIntegrable_iff_integrableOn_Ioc_of_le ht ] using hφ ) ( by simpa only [ intervalIntegrable_iff_integrableOn_Ioc_of_le ht ] using hψ );
          · exact measurableSet_le measurable_fst measurable_snd;
      simp_all +decide [ intervalIntegral.integral_of_le ht, MeasureTheory.integral_const_mul ];
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ intervalIntegral.integral_of_le hx.2 ] ;
    simp_all +decide [ mul_comm ];
    rw [ ← intervalIntegral.integral_add ];
    · rw [ ← intervalIntegral.integral_mul_const ];
      refine' intervalIntegral.integral_congr fun x hx => _;
      rw [ ← mul_add, add_comm, intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ hψ.mono_set, Set.Icc_subset_Icc ] <;> aesop;
    · apply_rules [ IntervalIntegrable.mul_continuousOn, hφ ];
      have h_cont : ContinuousOn (fun x => ∫ r in t..x, ψ r) (Set.uIcc 0 t) := by
        intro x hx; apply_rules [ intervalIntegral.continuousWithinAt_primitive, hψ ] ; aesop;
        cases max_cases t 0 <;> cases min_cases t 0 <;> aesop;
      exact ContinuousOn.congr ( h_cont.neg ) fun x hx => by rw [ ← intervalIntegral.integral_symm ] ;
    · apply_rules [ hφ.mul_continuousOn, hψ.mul_continuousOn ];
      intro x hx;
      refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> aesop;
  · have h_cont : ContinuousOn (fun s => ∫ r in (0:ℝ)..s, φ r) (Set.Icc 0 t) := by
      intro s hs; apply_rules [ intervalIntegral.continuousWithinAt_primitive, hφ ] ; aesop;
      simpa [ ht ] using hφ;
    rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le ht ] at *;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun s => ( SupSet.sSup ( Set.image ( fun s => |∫ r in ( 0 : ℝ )..s, φ r| ) ( Set.Icc 0 t ) ) ) * |ψ s|;
    · exact MeasureTheory.Integrable.const_mul ( hψ.norm ) _;
    · exact MeasureTheory.AEStronglyMeasurable.mul ( h_cont.aestronglyMeasurable ( measurableSet_Icc ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self ) hψ.aestronglyMeasurable;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ norm_mul ] ; exact mul_le_mul_of_nonneg_right ( le_csSup ( IsCompact.bddAbove ( isCompact_Icc.image_of_continuousOn ( h_cont.abs ) ) ) ( Set.mem_image_of_mem _ <| Set.Ioc_subset_Icc_self hx ) ) ( abs_nonneg _ ) ;
  · apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
    have h_integrable : ContinuousOn (fun s => ∫ r in (0:ℝ)..s, ψ r) (Set.Icc 0 t) := by
      intro s hs; apply_rules [ intervalIntegral.continuousWithinAt_primitive, hψ ] ; aesop;
      simpa [ ht ] using hψ;
    rw [ intervalIntegrable_iff_integrableOn_Icc_of_le ht ] at *;
    rw [ Set.uIcc_of_le ht ];
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun s => ( SupSet.sSup ( Set.image ( fun s => |∫ r in ( 0 : ℝ )..s, ψ r| ) ( Set.Icc 0 t ) ) ) * |φ s|;
    · exact MeasureTheory.Integrable.const_mul ( hφ.norm ) _;
    · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable.aestronglyMeasurable measurableSet_Icc ) hφ.aestronglyMeasurable;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx using by rw [ norm_mul ] ; exact mul_le_mul_of_nonneg_right ( le_csSup ( IsCompact.bddAbove ( isCompact_Icc.image_of_continuousOn ( h_integrable.abs ) ) ) ( Set.mem_image_of_mem _ hx ) ) ( abs_nonneg _ ) ;

/-
**Mean-zero of a Dynkin martingale.**  `E[M^h_t] = 0` for `0 ≤ t`, since `M^h_0 = 0`
and `M^h` is a martingale.
-/
theorem dynkin_mean_zero
    {S Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ mΩ)
    (proc : ℝ → Ω → S) (L : (S → ℝ) → S → ℝ) (h : S → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hM : Martingale (dynkinM L proc h) ℱ μ) :
    ∫ ω, dynkinM L proc h t ω ∂μ = 0 := by
  have h_zero : ∫ ω, dynkinM L proc h t ω ∂μ = ∫ ω, dynkinM L proc h 0 ω ∂μ := by
    have := hM.2 0 t ht;
    rw [ ← MeasureTheory.integral_congr_ae this, MeasureTheory.integral_condExp ];
  simp_all +decide [ dynkinM ]

/-
**Tower / orthogonality identity.**  For a martingale `M`, an `ℱ_s`-measurable `Z` and
`s ≤ t`, `E[Z·M_t] = E[Z·M_s]`.
-/
theorem dynkin_tower_mul
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ mΩ)
    (M : ℝ → Ω → ℝ) (hM : Martingale M ℱ μ)
    (s t : ℝ) (hst : s ≤ t) (Z : Ω → ℝ)
    (hZ : StronglyMeasurable[ℱ s] Z)
    (h1 : Integrable (fun ω => Z ω * M t ω) μ) :
    ∫ ω, Z ω * M t ω ∂μ = ∫ ω, Z ω * M s ω ∂μ := by
  have h_condExp : μ[(fun ω => Z ω * M t ω) | ℱ s] =ᵐ[μ] fun ω => Z ω * M s ω := by
    have := hM.condExp_ae_eq hst;
    convert MeasureTheory.condExp_mul_of_stronglyMeasurable_left hZ h1 ( hM.integrable t ) |> ( fun h => h.trans ( Filter.EventuallyEq.mul ( Filter.EventuallyEq.refl _ _ ) this ) ) using 1;
  rw [ ← MeasureTheory.integral_congr_ae h_condExp, MeasureTheory.integral_condExp ]

/-
**Fubini over a time interval.**  Swap the `ω`-integral and the time-integral.
-/
theorem dynkin_interval_integral_swap
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [SFinite μ]
    (hfun : ℝ → Ω → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hjoint : Integrable (Function.uncurry hfun) ((volume.restrict (Set.Ioc 0 t)).prod μ)) :
    ∫ ω, (∫ s in (0:ℝ)..t, hfun s ω) ∂μ = ∫ s in (0:ℝ)..t, ∫ ω, hfun s ω ∂μ := by
  simp +decide only [intervalIntegral.integral_of_le ht];
  exact Eq.symm (integral_integral_swap hjoint)

/-
**Martingale-drift Fubini + tower.**  `E[M_t · ∫₀ᵗφ_s ds] = ∫₀ᵗ E[M_s · φ_s] ds` when
`M` is a martingale and each `φ_s` is `ℱ_s`-measurable.
-/
theorem dynkin_mart_drift_fubini
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ mΩ)
    (M : ℝ → Ω → ℝ) (hM : Martingale M ℱ μ) (φ : ℝ → Ω → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hφ_adapt : ∀ s : ℝ, StronglyMeasurable[ℱ s] (φ s))
    (hjoint : Integrable (Function.uncurry (fun s ω => M t ω * φ s ω))
        ((volume.restrict (Set.Ioc 0 t)).prod μ))
    (hint_Mt : ∀ s : ℝ, Integrable (fun ω => M t ω * φ s ω) μ) :
    ∫ ω, M t ω * (∫ s in (0:ℝ)..t, φ s ω) ∂μ
      = ∫ s in (0:ℝ)..t, ∫ ω, M s ω * φ s ω ∂μ := by
  have h_fubini : ∫ ω, (∫ s in (0:ℝ)..t, M t ω * φ s ω) ∂μ = ∫ s in (0:ℝ)..t, ∫ ω, M t ω * φ s ω ∂μ := by
    convert dynkin_interval_integral_swap μ ( fun s ω => M t ω * φ s ω ) t ht hjoint using 1;
  convert h_fubini using 1;
  · simp +decide only [intervalIntegral.integral_const_mul];
  · rw [ intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht ];
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs => _;
    have := @dynkin_tower_mul;
    specialize this μ ℱ M hM s t hs.2 ( φ s ) ( hφ_adapt s ) ( by simpa only [ mul_comm ] using ‹∀ s, Integrable ( fun ω => M t ω * φ s ω ) μ› s ) ; simp_all +decide [ mul_comm ] ;

/-
Interval-integrability of a parameter integral from joint integrability.
-/
theorem dynkin_ii_of_joint
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [SFinite μ]
    (h : ℝ → Ω → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hjoint : Integrable (Function.uncurry h) ((volume.restrict (Set.Ioc 0 t)).prod μ)) :
    IntervalIntegrable (fun s => ∫ ω, h s ω ∂μ) volume 0 t := by
  rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le ht ];
  exact hjoint.integral_prod_left

/-
Split identity: `∫ f(η_s)·φ = ∫ M^f_s·φ + ∫ f(η_0)·φ + ∫ (∫₀ˢLf)·φ`, since
`f(η_s) = M^f_s + f(η_0) + ∫₀ˢ Lf(η_r) dr` pointwise.
-/
theorem dynkin_split_mul
    {S Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (proc : ℝ → Ω → S) (L : (S → ℝ) → S → ℝ) (f : S → ℝ) (φ : Ω → ℝ) (s : ℝ)
    (h1 : Integrable (fun ω => dynkinM L proc f s ω * φ ω) μ)
    (h2 : Integrable (fun ω => f (proc 0 ω) * φ ω) μ)
    (h3 : Integrable (fun ω => (∫ r in (0:ℝ)..s, L f (proc r ω)) * φ ω) μ) :
    ∫ ω, f (proc s ω) * φ ω ∂μ
      = (∫ ω, dynkinM L proc f s ω * φ ω ∂μ) + (∫ ω, f (proc 0 ω) * φ ω ∂μ)
          + (∫ ω, (∫ r in (0:ℝ)..s, L f (proc r ω)) * φ ω ∂μ) := by
  convert MeasureTheory.integral_add ( h1.add h2 ) h3 using 1;
  · congr with ω ; simp +decide [ dynkinM ] ; ring;
  · convert ( MeasureTheory.integral_add h1 h2 ) |> Eq.symm |> congr_arg ( · + ∫ ω, ( ∫ r in ( 0 : ℝ )..s, L f ( proc r ω ) ) * φ ω ∂μ ) using 1

/-
Final combinatorial step of the `L²` identity: assemble the seven interval integrals
into the carré-du-champ integrand using the two split identities `hf`, `hg`.
-/
theorem dynkin_L2_combine (t : ℝ)
    (I1 I2 I3 J2 J3 I4 I5 I6 I7 : ℝ → ℝ)
    (hI1 : IntervalIntegrable I1 volume 0 t)
    (hI2 : IntervalIntegrable I2 volume 0 t)
    (hI3 : IntervalIntegrable I3 volume 0 t)
    (hJ2 : IntervalIntegrable J2 volume 0 t)
    (hJ3 : IntervalIntegrable J3 volume 0 t)
    (hI4 : IntervalIntegrable I4 volume 0 t)
    (hI5 : IntervalIntegrable I5 volume 0 t)
    (hI6 : IntervalIntegrable I6 volume 0 t)
    (hI7 : IntervalIntegrable I7 volume 0 t)
    (hf : ∀ s ∈ Set.uIcc 0 t, I2 s = J2 s + I4 s + I6 s)
    (hg : ∀ s ∈ Set.uIcc 0 t, I3 s = J3 s + I5 s + I7 s) :
    (∫ s in (0:ℝ)..t, I1 s) - (∫ s in (0:ℝ)..t, J2 s) - (∫ s in (0:ℝ)..t, J3 s)
        - (∫ s in (0:ℝ)..t, I4 s) - (∫ s in (0:ℝ)..t, I5 s)
        - (∫ s in (0:ℝ)..t, (I6 s + I7 s))
      = ∫ s in (0:ℝ)..t, (I1 s - I2 s - I3 s) := by
  rw [ intervalIntegral.integral_sub, intervalIntegral.integral_sub ] <;> norm_num [ hI1, hI2, hI3, hJ2, hJ3, hI4, hI5, hI6, hI7 ];
  rw [ intervalIntegral.integral_congr fun x hx => hf x ?_, intervalIntegral.integral_congr fun x hx => hg x ?_ ];
  · rw [ intervalIntegral.integral_add, intervalIntegral.integral_add ];
    · rw [ intervalIntegral.integral_add, intervalIntegral.integral_add ] <;> ring <;> norm_num [ hJ2, hJ3, hI4, hI5, hI6, hI7 ];
    · assumption;
    · assumption;
    · exact hJ2.add hI4;
    · assumption;
  · exact hx;
  · exact hx

/-- **Part 2 of `lem:dynkin` (`L²` content, PROVED).**  The honest, library-accessible
part of the bracket statement: the integrated covariance identity
`E[M^f_t M^g_t] = E[∫₀ᵗ Γ(f,g)(η_s) ds]`, `Γ = L(fg) − fLg − gLf`.

The full predictable-bracket identity is `dynkinBracketDef`'s cited classical fact; this is
the `L²`-level content that consumers morally use.  The key observation is that this
identity needs **only** the martingale property (Part 1) applied to `f`, `g` and the product
`fg`, together with Fubini/integration-by-parts — no further semigroup input.  Concretely:
expand `M^f_t M^g_t` against `M^{fg}_t`, use mean-zero of the three martingales and the
tower property `E[Z·M^f_t] = E[Z·M^f_s]` for `ℱ_s`-measurable `Z`, and the drift–drift
integration-by-parts identity.  All integrability facts below are standard from boundedness
of `f, g, Lf, Lg, L(fg)` and finiteness of `μ`. -/
theorem dynkin_L2
    {S Ω : Type*} [MeasurableSpace S] {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ mΩ)
    (proc : ℝ → Ω → S) (L : (S → ℝ) → S → ℝ)
    (f g : S → ℝ) (t : ℝ) (ht : 0 ≤ t)
    -- the three Dynkin martingales (Part 1 applied to `f`, `g` and `fg`)
    (hMf : Martingale (dynkinM L proc f) ℱ μ)
    (hMg : Martingale (dynkinM L proc g) ℱ μ)
    (hMfg : Martingale (dynkinM L proc (fun s => f s * g s)) ℱ μ)
    -- `ℱ_s`-measurability of the drift integrands and the initial values
    (hLf_adapt : ∀ s : ℝ, StronglyMeasurable[ℱ s] (fun ω => L f (proc s ω)))
    (hLg_adapt : ∀ s : ℝ, StronglyMeasurable[ℱ s] (fun ω => L g (proc s ω)))
    (hg0_adapt : StronglyMeasurable[ℱ 0] (fun ω => g (proc 0 ω)))
    (hf0_adapt : StronglyMeasurable[ℱ 0] (fun ω => f (proc 0 ω)))
    -- interval-integrability of the drift integrands (for the interval integrals / IBP)
    (hLf_ii : ∀ ω : Ω, IntervalIntegrable (fun s => L f (proc s ω)) volume 0 t)
    (hLg_ii : ∀ ω : Ω, IntervalIntegrable (fun s => L g (proc s ω)) volume 0 t)
    -- single-time integrability (standard from boundedness and finiteness of `μ`)
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
    -- per-time-`s` integrability (standard from boundedness and finiteness of `μ`)
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
    -- joint integrability for the Fubini swaps over `Ioc 0 t × Ω`
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
    ∫ ω, dynkinM L proc f t ω * dynkinM L proc g t ω ∂μ
      = ∫ ω, dynkinBracketDef L proc f g t ω ∂μ := by
  -- LHS: expand the product pointwise, then split the integral into nine pieces.
  have h_simp : ∫ ω, dynkinM L proc f t ω * dynkinM L proc g t ω ∂μ
      = (∫ ω, f (proc t ω) * g (proc t ω) ∂μ) - (∫ ω, f (proc 0 ω) * g (proc 0 ω) ∂μ)
        - (∫ ω, dynkinM L proc f t ω * g (proc 0 ω) ∂μ)
        - (∫ ω, dynkinM L proc f t ω * (∫ r in (0:ℝ)..t, L g (proc r ω)) ∂μ)
        - (∫ ω, dynkinM L proc g t ω * f (proc 0 ω) ∂μ)
        - (∫ ω, dynkinM L proc g t ω * (∫ r in (0:ℝ)..t, L f (proc r ω)) ∂μ)
        - (∫ ω, f (proc 0 ω) * (∫ r in (0:ℝ)..t, L g (proc r ω)) ∂μ)
        - (∫ ω, g (proc 0 ω) * (∫ r in (0:ℝ)..t, L f (proc r ω)) ∂μ)
        - (∫ ω, (∫ r in (0:ℝ)..t, L f (proc r ω)) * (∫ r in (0:ℝ)..t, L g (proc r ω)) ∂μ) := by
    have hpt : ∀ ω, dynkinM L proc f t ω * dynkinM L proc g t ω
        = f (proc t ω) * g (proc t ω) - f (proc 0 ω) * g (proc 0 ω)
          - dynkinM L proc f t ω * g (proc 0 ω)
          - dynkinM L proc f t ω * (∫ r in (0:ℝ)..t, L g (proc r ω))
          - dynkinM L proc g t ω * f (proc 0 ω)
          - dynkinM L proc g t ω * (∫ r in (0:ℝ)..t, L f (proc r ω))
          - f (proc 0 ω) * (∫ r in (0:ℝ)..t, L g (proc r ω))
          - g (proc 0 ω) * (∫ r in (0:ℝ)..t, L f (proc r ω))
          - (∫ r in (0:ℝ)..t, L f (proc r ω)) * (∫ r in (0:ℝ)..t, L g (proc r ω)) :=
      fun ω => by simp only [dynkinM]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_sub _ hint_Df_Dg, integral_sub _ hint_g0_Df, integral_sub _ hint_f0_Dg,
        integral_sub _ hint_Mg_Df, integral_sub _ hint_Mg_f0, integral_sub _ hint_Mf_Dg,
        integral_sub _ hint_Mf_g0, integral_sub hint_fg_t hint_fg_0]
    all_goals first
      | exact (((((((hint_fg_t.sub hint_fg_0).sub hint_Mf_g0).sub hint_Mf_Dg).sub hint_Mg_f0).sub
            hint_Mg_Df).sub hint_f0_Dg).sub hint_g0_Df)
      | exact ((((((hint_fg_t.sub hint_fg_0).sub hint_Mf_g0).sub hint_Mf_Dg).sub hint_Mg_f0).sub
            hint_Mg_Df).sub hint_f0_Dg)
      | exact (((((hint_fg_t.sub hint_fg_0).sub hint_Mf_g0).sub hint_Mf_Dg).sub hint_Mg_f0).sub
            hint_Mg_Df)
      | exact ((((hint_fg_t.sub hint_fg_0).sub hint_Mf_g0).sub hint_Mf_Dg).sub hint_Mg_f0)
      | exact (((hint_fg_t.sub hint_fg_0).sub hint_Mf_g0).sub hint_Mf_Dg)
      | exact ((hint_fg_t.sub hint_fg_0).sub hint_Mf_g0)
      | exact (hint_fg_t.sub hint_fg_0)
  -- Tower / orthogonality: the two initial-value cross terms vanish.
  have h_towerf : ∫ ω, dynkinM L proc f t ω * g (proc 0 ω) ∂μ = 0 := by
    have h := dynkin_tower_mul μ ℱ (dynkinM L proc f) hMf 0 t ht (fun ω => g (proc 0 ω))
      hg0_adapt (by simpa [mul_comm] using hint_Mf_g0)
    have hz : (fun ω => g (proc 0 ω) * dynkinM L proc f 0 ω) = fun _ : Ω => (0:ℝ) := by
      funext ω; simp [dynkinM]
    rw [show (∫ ω, dynkinM L proc f t ω * g (proc 0 ω) ∂μ)
          = ∫ ω, g (proc 0 ω) * dynkinM L proc f t ω ∂μ from
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => mul_comm _ _)), h, hz,
        integral_zero]
  have h_towerg : ∫ ω, dynkinM L proc g t ω * f (proc 0 ω) ∂μ = 0 := by
    have h := dynkin_tower_mul μ ℱ (dynkinM L proc g) hMg 0 t ht (fun ω => f (proc 0 ω))
      hf0_adapt (by simpa [mul_comm] using hint_Mg_f0)
    have hz : (fun ω => f (proc 0 ω) * dynkinM L proc g 0 ω) = fun _ : Ω => (0:ℝ) := by
      funext ω; simp [dynkinM]
    rw [show (∫ ω, dynkinM L proc g t ω * f (proc 0 ω) ∂μ)
          = ∫ ω, f (proc 0 ω) * dynkinM L proc g t ω ∂μ from
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => mul_comm _ _)), h, hz,
        integral_zero]
  -- Mean-zero of the product martingale `M^{fg}`.
  have h_mzero : (∫ ω, f (proc t ω) * g (proc t ω) ∂μ) - (∫ ω, f (proc 0 ω) * g (proc 0 ω) ∂μ)
      = ∫ s in (0:ℝ)..t, ∫ ω, L (fun s' => f s' * g s') (proc s ω) ∂μ := by
    have hmz := dynkin_mean_zero μ ℱ proc L (fun s' => f s' * g s') t ht hMfg
    have hsplit : ∫ ω, dynkinM L proc (fun s' => f s' * g s') t ω ∂μ
        = (∫ ω, f (proc t ω) * g (proc t ω) ∂μ) - (∫ ω, f (proc 0 ω) * g (proc 0 ω) ∂μ)
          - ∫ ω, (∫ r in (0:ℝ)..t, L (fun s' => f s' * g s') (proc r ω)) ∂μ := by
      rw [show (fun ω => dynkinM L proc (fun s' => f s' * g s') t ω)
            = fun ω => f (proc t ω) * g (proc t ω) - f (proc 0 ω) * g (proc 0 ω)
                - (∫ r in (0:ℝ)..t, L (fun s' => f s' * g s') (proc r ω)) from by
          funext ω; simp only [dynkinM],
        integral_sub _ hint_Dfg, integral_sub hint_fg_t hint_fg_0]
      exact hint_fg_t.sub hint_fg_0
    rw [hsplit] at hmz
    have hswap := dynkin_interval_integral_swap μ
      (fun s ω => L (fun s' => f s' * g s') (proc s ω)) t ht hjoint_Lfg
    linarith [hswap, hmz]
  -- The two martingale-drift terms (Fubini + tower).
  have h_MfDg : ∫ ω, dynkinM L proc f t ω * (∫ r in (0:ℝ)..t, L g (proc r ω)) ∂μ
      = ∫ s in (0:ℝ)..t, ∫ ω, dynkinM L proc f s ω * L g (proc s ω) ∂μ :=
    dynkin_mart_drift_fubini μ ℱ (dynkinM L proc f) hMf (fun s ω => L g (proc s ω)) t ht
      hLg_adapt hjoint_MfLg hint_MfLg
  have h_MgDf : ∫ ω, dynkinM L proc g t ω * (∫ r in (0:ℝ)..t, L f (proc r ω)) ∂μ
      = ∫ s in (0:ℝ)..t, ∫ ω, dynkinM L proc g s ω * L f (proc s ω) ∂μ :=
    dynkin_mart_drift_fubini μ ℱ (dynkinM L proc g) hMg (fun s ω => L f (proc s ω)) t ht
      hLf_adapt hjoint_MgLf hint_MgLf
  -- The two constant-drift terms (Fubini).
  have h_f0Dg : ∫ ω, f (proc 0 ω) * (∫ r in (0:ℝ)..t, L g (proc r ω)) ∂μ
      = ∫ s in (0:ℝ)..t, ∫ ω, f (proc 0 ω) * L g (proc s ω) ∂μ := by
    rw [← dynkin_interval_integral_swap μ (fun s ω => f (proc 0 ω) * L g (proc s ω)) t ht
        hjoint_f0Lg]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun ω =>
      (intervalIntegral.integral_const_mul (f (proc 0 ω)) (fun s => L g (proc s ω))).symm))
  have h_g0Df : ∫ ω, g (proc 0 ω) * (∫ r in (0:ℝ)..t, L f (proc r ω)) ∂μ
      = ∫ s in (0:ℝ)..t, ∫ ω, g (proc 0 ω) * L f (proc s ω) ∂μ := by
    rw [← dynkin_interval_integral_swap μ (fun s ω => g (proc 0 ω) * L f (proc s ω)) t ht
        hjoint_g0Lf]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun ω =>
      (intervalIntegral.integral_const_mul (g (proc 0 ω)) (fun s => L f (proc s ω))).symm))
  -- The drift–drift term (integration by parts + Fubini).
  have h_DfDg : ∫ ω, (∫ r in (0:ℝ)..t, L f (proc r ω)) * (∫ r in (0:ℝ)..t, L g (proc r ω)) ∂μ
      = ∫ s in (0:ℝ)..t, (∫ ω, (∫ r in (0:ℝ)..s, L f (proc r ω)) * L g (proc s ω) ∂μ
            + ∫ ω, (∫ r in (0:ℝ)..s, L g (proc r ω)) * L f (proc s ω) ∂μ) := by
    rw [show (fun ω => (∫ r in (0:ℝ)..t, L f (proc r ω)) * (∫ r in (0:ℝ)..t, L g (proc r ω)))
          = fun ω => ∫ s in (0:ℝ)..t, ((∫ r in (0:ℝ)..s, L f (proc r ω)) * L g (proc s ω)
                + (∫ r in (0:ℝ)..s, L g (proc r ω)) * L f (proc s ω)) from by
        funext ω
        exact intervalIntegral_mul_eq_ibp (fun r => L f (proc r ω)) (fun r => L g (proc r ω))
          t ht (hLf_ii ω) (hLg_ii ω)]
    rw [dynkin_interval_integral_swap μ
      (fun s ω => (∫ r in (0:ℝ)..s, L f (proc r ω)) * L g (proc s ω)
                + (∫ r in (0:ℝ)..s, L g (proc r ω)) * L f (proc s ω)) t ht
      (hjoint_DfLg.add hjoint_DgLf)]
    exact intervalIntegral.integral_congr
      (fun s _ => integral_add (hint_DfsLg s) (hint_DgsLf s))
  -- RHS: the bracket definition, swapped and split by the carré du champ.
  have h_rhs : ∫ ω, dynkinBracketDef L proc f g t ω ∂μ
      = ∫ s in (0:ℝ)..t, ((∫ ω, L (fun s' => f s' * g s') (proc s ω) ∂μ)
          - (∫ ω, f (proc s ω) * L g (proc s ω) ∂μ)
          - (∫ ω, g (proc s ω) * L f (proc s ω) ∂μ)) := by
    rw [show ∫ ω, dynkinBracketDef L proc f g t ω ∂μ
          = ∫ ω, (∫ s in (0:ℝ)..t, carreDuChamp L f g (proc s ω)) ∂μ from rfl,
        dynkin_interval_integral_swap μ (fun s ω => carreDuChamp L f g (proc s ω)) t ht
          hjoint_Gamma]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [carreDuChamp]
    rw [integral_sub _ (hint_gsLf s), integral_sub (hint_Lfg s) (hint_fsLg s)]
    exact (hint_Lfg s).sub (hint_fsLg s)
  -- The two split identities `f(η_s) = M^f_s + f(η_0) + ∫₀ˢ Lf`.
  have hf : ∀ s ∈ Set.uIcc (0:ℝ) t, (∫ ω, f (proc s ω) * L g (proc s ω) ∂μ)
      = (∫ ω, dynkinM L proc f s ω * L g (proc s ω) ∂μ)
        + (∫ ω, f (proc 0 ω) * L g (proc s ω) ∂μ)
        + (∫ ω, (∫ r in (0:ℝ)..s, L f (proc r ω)) * L g (proc s ω) ∂μ) :=
    fun s _ => dynkin_split_mul μ proc L f (fun ω => L g (proc s ω)) s
      (hint_MfsLg s) (hint_f0Lg s) (hint_DfsLg s)
  have hg' : ∀ s ∈ Set.uIcc (0:ℝ) t, (∫ ω, g (proc s ω) * L f (proc s ω) ∂μ)
      = (∫ ω, dynkinM L proc g s ω * L f (proc s ω) ∂μ)
        + (∫ ω, g (proc 0 ω) * L f (proc s ω) ∂μ)
        + (∫ ω, (∫ r in (0:ℝ)..s, L g (proc r ω)) * L f (proc s ω) ∂μ) :=
    fun s _ => dynkin_split_mul μ proc L g (fun ω => L f (proc s ω)) s
      (hint_MgsLf s) (hint_g0Lf s) (hint_DgsLf s)
  -- Assemble.
  rw [h_rhs, h_simp, h_towerf, h_towerg, h_mzero, h_MfDg, h_MgDf, h_f0Dg, h_g0Df, h_DfDg]
  simp only [sub_zero]
  exact dynkin_L2_combine t
    (fun s => ∫ ω, L (fun s' => f s' * g s') (proc s ω) ∂μ)
    (fun s => ∫ ω, f (proc s ω) * L g (proc s ω) ∂μ)
    (fun s => ∫ ω, g (proc s ω) * L f (proc s ω) ∂μ)
    (fun s => ∫ ω, dynkinM L proc f s ω * L g (proc s ω) ∂μ)
    (fun s => ∫ ω, dynkinM L proc g s ω * L f (proc s ω) ∂μ)
    (fun s => ∫ ω, f (proc 0 ω) * L g (proc s ω) ∂μ)
    (fun s => ∫ ω, g (proc 0 ω) * L f (proc s ω) ∂μ)
    (fun s => ∫ ω, (∫ r in (0:ℝ)..s, L f (proc r ω)) * L g (proc s ω) ∂μ)
    (fun s => ∫ ω, (∫ r in (0:ℝ)..s, L g (proc r ω)) * L f (proc s ω) ∂μ)
    (dynkin_ii_of_joint μ _ t ht hjoint_Lfg)
    (dynkin_ii_of_joint μ _ t ht hjoint_fLg)
    (dynkin_ii_of_joint μ _ t ht hjoint_gLf)
    (dynkin_ii_of_joint μ _ t ht hjoint_MfsLg)
    (dynkin_ii_of_joint μ _ t ht hjoint_MgsLf)
    (dynkin_ii_of_joint μ _ t ht hjoint_f0Lg)
    (dynkin_ii_of_joint μ _ t ht hjoint_g0Lf)
    (dynkin_ii_of_joint μ _ t ht hjoint_DfLg)
    (dynkin_ii_of_joint μ _ t ht hjoint_DgLf)
    hf hg'

end TypeDDecoupling