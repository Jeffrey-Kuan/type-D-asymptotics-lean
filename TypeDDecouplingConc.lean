import Mathlib

/-!
# Abstract `L²` concentration estimate for the cross bracket (`prop:conc`)

This file isolates the quantitative content of `prop:conc` (the `L²` concentration of the
cross bracket, condition (X)) as a self-contained real-analysis theorem, following the brief
`propconc_brief.tex`.  The process-level facts (transfer bound, kernel split, equal-time
bound, stationarity identity) enter as hypotheses; the inequality chain (Cauchy–Schwarz on
the double bond sum) and the time integration (elementary integrals) are proved here.

Main results (namespace `TypeDDecoupling.Conc`):

* `corr_pointwise` (Lemma "correlation bound"): from the transfer+Cauchy–Schwarz bound
  `|C_Θ(s)| ≤ (M/N²)(∑_x g_x √G(x))²`, the kernel split
  `G(x) ≤ C_k[(1+u)⁻¹ + e^{-ν u}(1+u)^{-1/2}] + ε_*` (`u = sN²`), and the Riemann-sum bound
  `∑_x g_x ≤ C_φ N`, one gets the pointwise bound
  `|C_Θ(s)| ≤ 3 M C_φ² [C_k/(sN²) + C_k e^{-3cs}/(√s N) + ε_*]`.

* `gaussian_half_integral_bound`: `∫_a^t e^{-3cs}/√s ds ≤ √(π/(3c))` for `0 < a ≤ t`.

* `time_integral_bound` (Lemma "time integration"): combining the correlation bound for
  `s ≥ N⁻²` with the equal-time bound for `s ≤ N⁻²`,
  `∫_0^t |C_Θ| ds ≤ C_e/N³ + (D_c/N²) log₊(tN²) + D_c √(π/3c)/N + D_e t`.

* `conc_master`: assembling the above with the stationarity identity
  `E_ν[(∫Θ)²] ≤ 2t ∫_0^t |C_Θ|` yields the paper's three-term bound
  `E_ν[(∫Θ)²] ≤ C · t · (N⁻¹ + N⁻² log₊(tN²) + t ε_*)`.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral Filter Topology

namespace TypeDDecoupling.Conc

/-
Subadditivity of the square root over three nonnegative summands.
-/
lemma sqrt_add3_le (a b d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    Real.sqrt (a + b + d) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt d := by
  rw [ Real.sqrt_le_iff ];
  exact ⟨ by positivity, by rw [ add_sq, add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hd ] ; nlinarith [ Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg d ] ⟩

/-
**Correlation bound (Lemma `lem:corrbound`).**  The transfer+Cauchy–Schwarz bound on the
correlation, together with the kernel split and the Riemann-sum bound on the coefficients,
gives the pointwise decay bound at time `u = s N²`.
-/
lemma corr_pointwise
    (N : ℕ) (hN : 1 ≤ N)
    (Mc Cphi Ck epsStar cc nu : ℝ)
    (hMc : 0 ≤ Mc) (hCk : 0 ≤ Ck) (hepsStar : 0 ≤ epsStar)
    (s : ℝ) (hs : 0 < s)
    (hnu : 3 * cc ≤ nu * (N : ℝ) ^ 2)
    (bonds : Finset ℤ) (g G : ℤ → ℝ) (CtV : ℝ)
    (hg : ∀ x, 0 ≤ g x)
    (hgsum : ∑ x ∈ bonds, g x ≤ Cphi * (N : ℝ))
    (hsplit : ∀ x ∈ bonds, G x ≤
      Ck * ((1 + s * (N : ℝ) ^ 2)⁻¹
        + Real.exp (-nu * (s * (N : ℝ) ^ 2)) * (Real.sqrt (1 + s * (N : ℝ) ^ 2))⁻¹) + epsStar)
    (hCS : |CtV| ≤ (Mc / (N : ℝ) ^ 2) * (∑ x ∈ bonds, g x * Real.sqrt (G x)) ^ 2) :
    |CtV| ≤ 3 * Mc * Cphi ^ 2 * Ck / (s * (N : ℝ) ^ 2)
      + 3 * Mc * Cphi ^ 2 * Ck * Real.exp (-3 * cc * s) / (Real.sqrt s * (N : ℝ))
      + 3 * Mc * Cphi ^ 2 * epsStar := by
  -- Applying the bound from hsplit to each term in the sum.
  have hsum_bound : (∑ x ∈ bonds, g x * Real.sqrt (G x)) ^ 2 ≤ (Cphi * (N : ℝ)) ^ 2 * (3 * (Ck * ((1 + s * (N : ℝ) ^ 2)⁻¹ + Real.exp (-nu * (s * (N : ℝ) ^ 2)) * (Real.sqrt (1 + s * (N : ℝ) ^ 2))⁻¹) + epsStar)) := by
    refine' le_trans ( pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _ => mul_nonneg ( hg _ ) ( Real.sqrt_nonneg _ ) ) ( show ∑ x ∈ bonds, g x * Real.sqrt ( G x ) ≤ Cphi * N * Real.sqrt ( Ck * ( ( 1 + s * N ^ 2 ) ⁻¹ + Real.exp ( -nu * ( s * N ^ 2 ) ) * ( Real.sqrt ( 1 + s * N ^ 2 ) ) ⁻¹ ) + epsStar ) from _ ) 2 ) _;
    · exact le_trans ( Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| hsplit x hx ) <| hg x ) <| by simpa only [ Finset.sum_mul _ _ _ ] using mul_le_mul_of_nonneg_right hgsum <| Real.sqrt_nonneg _;
    · rw [ mul_pow, Real.sq_sqrt <| by positivity ] ; nlinarith only [ show 0 ≤ Ck * ( ( 1 + s * N ^ 2 ) ⁻¹ + Real.exp ( -nu * ( s * N ^ 2 ) ) * ( Real.sqrt ( 1 + s * N ^ 2 ) ) ⁻¹ ) + epsStar by positivity ] ;
  -- Applying the bounds on the exponential terms and simplifying.
  have h_exp_bound : Real.exp (-nu * (s * (N : ℝ) ^ 2)) ≤ Real.exp (-3 * cc * s) := by
    exact Real.exp_le_exp.mpr ( by nlinarith )
  have h_sqrt_bound : (Real.sqrt (1 + s * (N : ℝ) ^ 2))⁻¹ ≤ (Real.sqrt s * (N : ℝ))⁻¹ := by
    exact inv_anti₀ ( by positivity ) ( Real.le_sqrt_of_sq_le ( by nlinarith [ show ( N : ℝ ) ^ 2 ≥ 1 by norm_cast; nlinarith, Real.mul_self_sqrt hs.le ] ) );
  refine le_trans hCS <| le_trans ( mul_le_mul_of_nonneg_left hsum_bound <| by positivity ) ?_;
  refine' le_trans ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( add_le_add ( mul_le_mul_of_nonneg_left ( add_le_add ( inv_anti₀ ( by positivity ) <| show ( 1 + s * N ^ 2 : ℝ ) ≥ s * N ^ 2 by nlinarith ) <| mul_le_mul h_exp_bound h_sqrt_bound ( by positivity ) <| by positivity ) <| by positivity ) le_rfl ) <| by positivity ) <| by positivity ) <| by positivity ) _ ; ring_nf ; norm_num;
  norm_num [ show N ≠ 0 by linarith, pow_three, pow_two, mul_assoc ] ; ring_nf ; norm_num;
  norm_num [ show ( N : ℝ ) ^ 4 = N ^ 2 * N ^ 2 by ring, mul_assoc, ne_of_gt ( zero_lt_one.trans_le hN ) ] ; ring_nf ; norm_num

/-
The half-integer Gaussian moment on a finite interval is bounded, uniformly in the
endpoints, by the value of the improper integral `∫_0^∞ e^{-3cs}/√s ds = √(π/(3c))`.
-/
lemma gaussian_half_integral_bound (cc : ℝ) (hcc : 0 < cc) (a t : ℝ) (ha : 0 < a) (hat : a ≤ t) :
    ∫ s in a..t, Real.exp (-3 * cc * s) / Real.sqrt s ≤ Real.sqrt (Real.pi / (3 * cc)) := by
  -- Apply the Gaussian integral bound to the integrand.
  have h_gauss_bound : ∫ s in a..t, Real.exp (-3 * cc * s) / Real.sqrt s = ∫ s in Set.Ioc a t, Real.exp (-3 * cc * s) * s ^ (-1 / 2 : ℝ) := by
    rw [ intervalIntegral.integral_of_le hat ] ; refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => _ ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg ( by linarith [ hx.1 ] : 0 ≤ x ) ] ; ring;
  -- Apply the Gaussian integral bound to the integrand and use the fact that the integral over $(0, \infty)$ is $\sqrt{\pi / (3cc)}$.
  have h_gauss_bound : ∫ s in Set.Ioi 0, Real.exp (-3 * cc * s) * s ^ (-1 / 2 : ℝ) = Real.sqrt (Real.pi / (3 * cc)) := by
    have := @integral_rpow_mul_exp_neg_mul_rpow 1;
    convert @this ( -1 / 2 ) ( 3 * cc ) ( by norm_num ) ( by norm_num ) ( by positivity ) using 1 <;> norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg, mul_comm, Real.Gamma_one_half_eq ];
    rw [ Real.div_rpow ( by positivity ) ( by positivity ), Real.rpow_neg ( by positivity ) ] ; ring;
  refine' h_gauss_bound ▸ ‹∫ s in a..t, Real.exp ( -3 * cc * s ) / Real.sqrt s = ∫ s in Set.Ioc a t, Real.exp ( -3 * cc * s ) * s ^ ( -1 / 2 : ℝ ) › ▸ MeasureTheory.setIntegral_mono_set _ _ _;
  · exact ( by contrapose! h_gauss_bound; rw [ MeasureTheory.integral_undef h_gauss_bound ] ; positivity );
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with s hs using mul_nonneg ( Real.exp_nonneg _ ) ( Real.rpow_nonneg hs.out.le _ );
  · exact MeasureTheory.ae_of_all _ fun x hx => lt_of_lt_of_le ha hx.1.le

/-
**Time integration (Lemma `lem:timeint`).**  Splitting `[0,t]` at `s = N⁻²` and using the
equal-time bound below the cut and the correlation bound above it, the elementary integrals
`∫ ds/(sN²)`, `∫ e^{-3cs}/√s ds` and `∫ C_e/N ds` give the three-term bound.
-/
lemma time_integral_bound
    (N : ℕ) (hN : 1 ≤ N)
    (Dc De Ce cc : ℝ) (hDc : 0 ≤ Dc) (hDe : 0 ≤ De) (hCe : 0 ≤ Ce) (hcc : 0 < cc)
    (t : ℝ) (ht : 0 < t)
    (Ct : ℝ → ℝ)
    (hint : IntervalIntegrable (fun s => |Ct s|) volume 0 t)
    (heq : ∀ s, 0 < s → |Ct s| ≤ Ce / (N : ℝ))
    (hcorr : ∀ s, 0 < s → |Ct s| ≤
      Dc / (s * (N : ℝ) ^ 2) + Dc * Real.exp (-3 * cc * s) / (Real.sqrt s * (N : ℝ)) + De) :
    ∫ s in (0:ℝ)..t, |Ct s| ≤
      Ce / (N : ℝ) ^ 3 + Dc / (N : ℝ) ^ 2 * (Real.log (t * (N : ℝ) ^ 2) ⊔ 0)
        + Dc * Real.sqrt (Real.pi / (3 * cc)) / (N : ℝ) + De * t := by
  by_cases hs : t ≤ (N : ℝ)⁻¹ ^ 2;
  · -- Since $t \leq (N : ℝ)⁻¹ ^ 2$, we have $\int_0^t |Ct(s)| \, ds \leq \int_0^t \frac{Ce}{N} \, ds = \frac{Ce}{N} t$.
    have h_integral_bound : ∫ s in (0)..t, |Ct s| ≤ (Ce / N) * t := by
      rw [ intervalIntegral.integral_of_le ht.le ];
      exact le_trans ( MeasureTheory.setIntegral_mono_on ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by simpa only [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc ] using ‹IntervalIntegrable ( fun s => |Ct s| ) volume 0 t›.1 ) ) ) ) ) ) ( by exact ( by norm_num ) ) measurableSet_Ioc fun x hx => heq x hx.1 ) ( by norm_num [ mul_comm, ht.le ] );
    refine le_trans h_integral_bound ?_;
    refine le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ?_ ?_ ) ?_ ) ?_;
    · convert mul_le_mul_of_nonneg_left hs ( show 0 ≤ Ce / N by positivity ) using 1 ; ring;
    · positivity;
    · positivity;
    · positivity;
  · -- We'll use the fact that $|Ct(s)| \leq Dc / (s * N^2) + Dc * \exp(-3 * cc * s) / (\sqrt{s} * N) + De$ for $s > (N : ℝ)⁻¹ ^ 2$ to bound the integral.
    have h_bound : ∫ s in (N : ℝ)⁻¹ ^ 2..t, |Ct s| ≤ (Dc / (N : ℝ) ^ 2) * Real.log (t * N ^ 2) + Dc * Real.sqrt (Real.pi / (3 * cc)) / N + De * t := by
      refine' le_trans ( intervalIntegral.integral_mono_on _ _ _ _ ) _;
      refine' fun s => Dc / ( s * N ^ 2 ) + Dc * Real.exp ( -3 * cc * s ) / ( Real.sqrt s * N ) + De;
      · linarith;
      · apply_rules [ IntervalIntegrable.mono_set, Set.Icc_subset_Icc ] <;> norm_num;
        exact Or.inr ( by simpa using le_of_not_ge hs );
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.add ( ContinuousAt.add ( ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| continuousAt_const.pow 2 ) <| ne_of_gt <| mul_pos ( show 0 < x from by cases Set.mem_uIcc.mp hx <;> nlinarith [ inv_pos.mpr ( by positivity : 0 < ( N : ℝ ) ) ] ) <| by positivity ) <| ContinuousAt.div ( ContinuousAt.mul continuousAt_const <| Real.continuous_exp.continuousAt.comp <| ContinuousAt.mul continuousAt_const continuousAt_id ) ( ContinuousAt.mul ( Real.continuous_sqrt.continuousAt ) <| continuousAt_const ) <| ne_of_gt <| mul_pos ( Real.sqrt_pos.mpr <| show 0 < x from by cases Set.mem_uIcc.mp hx <;> nlinarith [ inv_pos.mpr ( by positivity : 0 < ( N : ℝ ) ) ] ) <| by positivity ) continuousAt_const;
      · exact fun x hx => hcorr x <| lt_of_lt_of_le ( by positivity ) hx.1;
      · rw [ intervalIntegral.integral_add, intervalIntegral.integral_add ] <;> norm_num;
        · refine' add_le_add_three _ _ _;
          · norm_num [ div_eq_mul_inv ];
            rw [ integral_inv_of_pos ] <;> norm_num <;> try positivity;
            linarith;
          · convert mul_le_mul_of_nonneg_left ( TypeDDecoupling.Conc.gaussian_half_integral_bound cc hcc ( ( N : ℝ ) ⁻¹ ^ 2 ) t ( by positivity ) ( by linarith ) ) ( show 0 ≤ Dc / N by positivity ) using 1 <;> ring;
            simp +decide only [mul_assoc, mul_comm, mul_left_comm, ← intervalIntegral.integral_const_mul];
          · nlinarith [ inv_pos.mpr ( by positivity : 0 < ( N : ℝ ) ^ 2 ) ];
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| continuousAt_const ) <| ne_of_gt <| mul_pos ( lt_of_lt_of_le ( by positivity ) hx.1 ) <| by positivity;
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( ContinuousAt.mul continuousAt_const <| ContinuousAt.rexp <| ContinuousAt.neg <| ContinuousAt.mul continuousAt_const continuousAt_id ) ( ContinuousAt.mul ( Real.continuous_sqrt.continuousAt ) continuousAt_const ) <| ne_of_gt <| mul_pos ( Real.sqrt_pos.mpr <| by cases Set.mem_uIcc.mp hx <;> nlinarith [ inv_pos.mpr ( by positivity : 0 < ( N : ℝ ) ^ 2 ) ] ) <| by positivity;
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.add ( ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| continuousAt_const ) <| ne_of_gt <| mul_pos ( lt_of_lt_of_le ( by positivity ) hu.1 ) <| by positivity ) <| ContinuousAt.div ( ContinuousAt.mul continuousAt_const <| Real.continuous_exp.continuousAt.comp <| ContinuousAt.neg <| ContinuousAt.mul continuousAt_const continuousAt_id ) ( ContinuousAt.mul ( Real.continuous_sqrt.continuousAt ) <| continuousAt_const ) <| ne_of_gt <| mul_pos ( Real.sqrt_pos.mpr <| lt_of_lt_of_le ( by positivity ) hu.1 ) <| by positivity;
    -- We'll use the fact that $|Ct(s)| \leq Ce / N$ for $s \leq (N : ℝ)⁻¹ ^ 2$ to bound the integral.
    have h_bound_lower : ∫ s in (0 : ℝ)..(N : ℝ)⁻¹ ^ 2, |Ct s| ≤ Ce / (N : ℝ) ^ 3 := by
      rw [ intervalIntegral.integral_of_le ( by positivity ) ];
      refine' le_trans ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioc fun x hx => heq x hx.1 ) _ <;> norm_num;
      · exact MeasureTheory.IntegrableOn.mono_set ( by simpa using ‹IntervalIntegrable ( fun s => |Ct s| ) volume 0 t›.1 ) ( Set.Ioc_subset_Ioc_right ( by simpa using le_of_not_ge hs ) );
      · ring_nf; norm_num;
    convert add_le_add h_bound_lower h_bound using 1;
    · rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ IntervalIntegrable.mono_set, Set.Icc_subset_Icc ] <;> norm_num; all_goals exact Or.inr ( by simpa using le_of_not_ge hs );
    · rw [ max_eq_left ( Real.log_nonneg <| by nlinarith [ show ( N : ℝ ) ≥ 1 by norm_cast, inv_mul_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ), inv_pow ( N : ℝ ) 2 ] ) ] ; ring

/-- The explicit concentration constant. -/
noncomputable def concConst (cc Mc Cphi Ck Ce : ℝ) : ℝ :=
  2 * (Ce + 3 * Mc * Cphi ^ 2 * Ck
        + 3 * Mc * Cphi ^ 2 * Ck * Real.sqrt (Real.pi / (3 * cc))
        + 3 * Mc * Cphi ^ 2) + 1

lemma concConst_pos (cc Mc Cphi Ck Ce : ℝ)
    (hMc : 0 ≤ Mc) (hCk : 0 ≤ Ck) (hCe : 0 ≤ Ce) :
    0 < concConst cc Mc Cphi Ck Ce := by
  unfold concConst
  have : 0 ≤ Real.sqrt (Real.pi / (3 * cc)) := Real.sqrt_nonneg _
  positivity

/-
**Master concentration estimate (`prop:conc`, quantitative content).**  From the transfer
bound, kernel split, Riemann-sum bound, equal-time bound and the stationarity identity (in the
form `bracketSq ≤ 2t ∫_0^t |C_Θ|`), the cross-bracket second moment obeys the paper's
three-term bound.
-/
theorem conc_master
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t)
    (cc Mc Cphi Ck Ce epsStar nu : ℝ)
    (hcc : 0 < cc) (hMc : 0 ≤ Mc) (hCk : 0 ≤ Ck) (hCe : 0 ≤ Ce)
    (hepsStar : 0 ≤ epsStar)
    (hnu : 3 * cc ≤ nu * (N : ℝ) ^ 2)
    (bonds : Finset ℤ) (g : ℤ → ℝ) (G : ℝ → ℤ → ℝ) (Ct : ℝ → ℝ) (bracketSq : ℝ)
    (hg : ∀ x, 0 ≤ g x)
    (hgsum : ∑ x ∈ bonds, g x ≤ Cphi * (N : ℝ))
    (hsplit : ∀ s x, x ∈ bonds → G s x ≤
      Ck * ((1 + s * (N : ℝ) ^ 2)⁻¹
        + Real.exp (-nu * (s * (N : ℝ) ^ 2)) * (Real.sqrt (1 + s * (N : ℝ) ^ 2))⁻¹) + epsStar)
    (hCS : ∀ s, 0 < s → |Ct s| ≤ (Mc / (N : ℝ) ^ 2) * (∑ x ∈ bonds, g x * Real.sqrt (G s x)) ^ 2)
    (heq : ∀ s, 0 < s → |Ct s| ≤ Ce / (N : ℝ))
    (hint : IntervalIntegrable (fun s => |Ct s|) volume 0 t)
    (hstat : bracketSq ≤ 2 * t * ∫ s in (0:ℝ)..t, |Ct s|) :
    bracketSq ≤ concConst cc Mc Cphi Ck Ce * t *
      ((N : ℝ)⁻¹ + (N : ℝ)⁻¹ ^ 2 * (Real.log (t * (N : ℝ) ^ 2) ⊔ 0) + t * epsStar) := by
  -- Apply the time_integral_bound lemma to get an upper bound for the integral of |Ct s|.
  have htime_integral_bound : ∫ s in (0:ℝ)..t, |Ct s| ≤ Ce / (N : ℝ) ^ 3 + 3 * Mc * Cphi ^ 2 * Ck / (N : ℝ) ^ 2 * (Real.log (t * (N : ℝ) ^ 2) ⊔ 0) + 3 * Mc * Cphi ^ 2 * Ck * Real.sqrt (Real.pi / (3 * cc)) / (N : ℝ) + 3 * Mc * Cphi ^ 2 * epsStar * t := by
    convert time_integral_bound N hN ( 3 * Mc * Cphi ^ 2 * Ck ) ( 3 * Mc * Cphi ^ 2 * epsStar ) Ce cc ( by positivity ) ( by positivity ) ( by positivity ) hcc t ht Ct ‹_› ‹_› _ using 1;
    intro s hs;
    apply corr_pointwise N hN Mc Cphi Ck epsStar cc nu hMc hCk hepsStar s hs hnu bonds g (G s) (Ct s) hg hgsum (fun x hx => hsplit s x hx) (hCS s hs);
  refine le_trans hstat <| le_trans ( mul_le_mul_of_nonneg_left htime_integral_bound <| by positivity ) ?_ ; ring_nf at *; simp_all +decide [ concConst ] ;
  refine' add_le_add_three _ _ _;
  · field_simp at *; ring_nf at *; norm_num at *; (
    refine' add_le_add _ _;
    · exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( mul_le_mul_of_nonneg_right ( le_mul_of_one_le_right ( by positivity ) ( mod_cast Nat.one_le_pow _ _ hN ) ) ( by positivity ) ) ( by positivity ) ) ( by positivity ) ) ( by positivity );
    · norm_num [ mul_assoc, mul_comm, mul_left_comm ]);
  · field_simp;
    nlinarith [ show 0 ≤ Mc * Cphi ^ 2 * Ck by positivity, show 0 ≤ Mc * Cphi ^ 2 * Ck * Real.sqrt ( Real.pi / ( 3 * cc ) ) by positivity, show 0 ≤ Mc * Cphi ^ 2 by positivity, show 0 ≤ Ce by positivity, show 0 ≤ max ( Real.log ( t * N ^ 2 ) ) 0 by positivity ];
  · exact le_of_sub_nonneg ( by ring_nf; positivity )

end TypeDDecoupling.Conc