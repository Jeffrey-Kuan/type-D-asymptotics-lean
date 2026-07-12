import Mathlib

/-!
# Kolmogorov–Rogozin anti-concentration via Esseen's method

This library-clean file develops, from scratch, the analytic machinery behind the
Kolmogorov–Rogozin anti-concentration inequality for integer-valued random variables,
following the lattice-Esseen route.

The pure-analysis core works with a probability mass function `a : ℤ → ℝ` on the integer
lattice (`a ≥ 0`, `HasSum a 1`), its characteristic function
`cf a t = ∑' x, a x · e^{i t x}`, and its largest atom `atomSup a = ⨆ x, a x`.

* **Tier 1** (`atomSup_le_integral`): the lattice Esseen inversion bound
  `atomSup a ≤ (1/2π) ∫_{-π}^{π} ‖cf a t‖ dt`.
* **Tier 2** (`KR_abstract`): the Kolmogorov–Rogozin bound
  `atomSup aS ≤ C/√(∑_j (1 - atomSup (a j)))` for the "sum" pmf `aS` whose characteristic
  function factorises as `cf aS t = ∏_j cf (a j) t`.  The argument uses the algebraic
  symmetrization weights `sw a y = ∑_x a x · a (x+y)`, the single-gap Gaussian integral
  bound, and a Jensen (convexity of `exp`) collapse of the product-over-gaps.
* **Interface** (`cf_pmf_sum_eq_prod`): the characteristic function of the pmf of a sum of
  independent integer random variables is the product of the characteristic functions, via
  Mathlib's `IndepFun.charFun_map_add_eq_mul`.
* **Poisson lower tail** (`poisson_lower_tail`): a Chernoff bound for a variable dominating
  a rate-`1` Poisson count.
-/

open scoped BigOperators Real Topology
open MeasureTheory Filter ProbabilityTheory

namespace TypeDDecoupling.KR

noncomputable section

/-- The lattice character `t ↦ e^{i t n}`. -/
def ch (t : ℝ) (n : ℤ) : ℂ := Complex.exp (t * n * Complex.I)

/-- Characteristic function of a pmf `a` on `ℤ`: `cf a t = ∑' x, a x · e^{i t x}`. -/
def cf (a : ℤ → ℝ) (t : ℝ) : ℂ := ∑' x : ℤ, (a x : ℂ) * ch t x

/-- Largest atom (concentration function) of a pmf `a` on `ℤ`. -/
def atomSup (a : ℤ → ℝ) : ℝ := ⨆ x : ℤ, a x

/-- Algebraic symmetrization weight: `sw a y = ∑_x a x · a (x+y) = ℙ(Y - Y' = y)`. -/
def sw (a : ℤ → ℝ) (y : ℤ) : ℝ := ∑' x : ℤ, a x * a (x + y)

/-! ## Elementary facts on `ch` and `atomSup` -/

lemma ch_norm (t : ℝ) (n : ℤ) : ‖ch t n‖ = 1 := by
  simp [ch, Complex.norm_exp]

lemma ch_add (t : ℝ) (m n : ℤ) : ch t m * ch t n = ch t (m + n) := by
  rw [ch, ch, ch, ← Complex.exp_add]; congr 1; push_cast; ring

/-
`∫_{-π}^{π} e^{i t n} dt = 2π` if `n = 0`, else `0` (orthogonality of characters).
-/
lemma integral_ch (n : ℤ) :
    (∫ t in (-Real.pi)..Real.pi, ch t n) = if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  split_ifs with hn;
  · simp +decide [ hn, ch ] ; ring;
  · unfold ch;
    have := @integral_exp_mul_complex ( -Real.pi ) Real.pi;
    convert @this ( n * Complex.I ) ( mul_ne_zero ( Int.cast_ne_zero.mpr hn ) Complex.I_ne_zero ) using 3 <;> ring;
    norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]

lemma atom_le_one {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) (x : ℤ) :
    a x ≤ 1 := by
  simpa using le_hasSum hsum x (fun i _ => hnn i)

lemma bddAbove_atom {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) :
    BddAbove (Set.range a) := by
  refine ⟨1, ?_⟩; rintro _ ⟨x, rfl⟩; exact le_hasSum hsum x (fun i _ => hnn i)

lemma atom_le_atomSup {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) (x : ℤ) :
    a x ≤ atomSup a := le_ciSup (bddAbove_atom hnn hsum) x

lemma atomSup_nonneg {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) :
    0 ≤ atomSup a :=
  le_ciSup_of_le (bddAbove_atom hnn hsum) 0 (hnn 0)

lemma atomSup_le_one {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) :
    atomSup a ≤ 1 :=
  ciSup_le (fun x => le_hasSum hsum x (fun i _ => hnn i))

/-! ## Tier 1: lattice Esseen inversion bound -/

lemma cf_norm_le_one {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) (t : ℝ) :
    ‖cf a t‖ ≤ 1 := by
  have hsummable : Summable (fun x : ℤ => ‖(a x : ℂ) * ch t x‖) := by
    have h : (fun x : ℤ => ‖(a x : ℂ) * ch t x‖) = a := by
      funext x
      rw [norm_mul, ch_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (hnn x)]
    rw [h]; exact hsum.summable
  calc ‖cf a t‖ ≤ ∑' x, ‖(a x : ℂ) * ch t x‖ := norm_tsum_le_tsum_norm hsummable
    _ = ∑' x, a x := by
        congr 1; funext x
        rw [norm_mul, ch_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (hnn x)]
    _ = 1 := hsum.tsum_eq

/-
Fourier inversion on `ℤ`: each atom is recovered from the characteristic function.
-/
lemma atom_inversion {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) (k : ℤ) :
    (a k : ℂ) = (1 / (2 * Real.pi)) *
      ∫ t in (-Real.pi)..Real.pi, ch t (-k) * cf a t := by
  -- By Fubini's theorem, we can interchange the order of summation and integration.
  have h_fubini : ∫ t in (-Real.pi)..Real.pi, ∑' x : ℤ, (a x : ℂ) * ch t (x - k) = ∑' x : ℤ, (a x : ℂ) * ∫ t in (-Real.pi)..Real.pi, ch t (x - k) := by
    rw [ intervalIntegral.integral_of_le, MeasureTheory.integral_tsum ] <;> norm_num [ Real.pi_pos.le ];
    · norm_num [ intervalIntegral.integral_of_le ( neg_le_self Real.pi_pos.le ), MeasureTheory.integral_const_mul ];
    · exact fun x => Continuous.aestronglyMeasurable ( by exact Continuous.mul ( continuous_const ) ( Complex.continuous_exp.comp ( by continuity ) ) );
    · refine' ne_of_lt ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum fun i => _ ) _ );
      use fun i => ENNReal.ofReal ( a i * ( 2 * Real.pi ) );
      · refine' le_trans ( MeasureTheory.lintegral_mono fun x => _ ) _;
        use fun x => ENNReal.ofReal ( a i );
        · simp +decide [ ch, Complex.norm_exp, ENorm.enorm ];
          norm_num [ ← ENNReal.ofReal_coe_nnreal, Complex.norm_exp ];
          rw [ abs_of_nonneg ( hnn i ) ];
        · simp +decide [ Real.pi_pos.le ];
          rw [ ← ENNReal.ofReal_mul ( hnn i ) ] ; ring_nf; norm_num;
      · rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num [ hnn, Real.pi_pos.le ];
        · exact fun n => mul_nonneg ( hnn n ) ( by positivity );
        · exact Summable.mul_right _ hsum.summable;
  convert congr_arg ( fun x : ℂ => ( 1 / ( 2 * Real.pi ) ) * x ) h_fubini.symm using 1;
  · rw [ tsum_eq_single k ] <;> norm_num [ integral_ch ];
    · ring_nf; norm_num [ Real.pi_ne_zero ];
    · exact fun x hx hx' => False.elim <| hx <| sub_eq_zero.mp hx';
  · congr! 2;
    ext t; simp +decide [ cf, ch_add ] ; ring;
    rw [ ← tsum_mul_left ] ; congr ; ext x ; rw [ ← mul_assoc, ← ch_add ] ; ring

/-- Consequence of inversion: each atom is bounded by the mean modulus of `cf`. -/
lemma atom_le_integral {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) (k : ℤ) :
    a k ≤ (1 / (2 * Real.pi)) * ∫ t in (-Real.pi)..Real.pi, ‖cf a t‖ := by
  have hak : a k = ‖(a k : ℂ)‖ := by rw [Complex.norm_real]; exact (abs_of_nonneg (hnn k)).symm
  rw [hak, atom_inversion hnn hsum k, norm_mul]
  have hc : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div]; norm_num [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hc]; gcongr
  calc ‖∫ t in (-Real.pi)..Real.pi, ch t (-k) * cf a t‖
      ≤ ∫ t in (-Real.pi)..Real.pi, ‖ch t (-k) * cf a t‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith [Real.pi_pos])
    _ = ∫ t in (-Real.pi)..Real.pi, ‖cf a t‖ := by
        congr 1; funext t; rw [norm_mul, ch_norm, one_mul]

/-- **Tier 1** (lattice Esseen inversion bound). -/
lemma atomSup_le_integral {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) :
    atomSup a ≤ (1 / (2 * Real.pi)) * ∫ t in (-Real.pi)..Real.pi, ‖cf a t‖ :=
  ciSup_le (fun k => atom_le_integral hnn hsum k)

/-! ## Tier 2: symmetrization identities -/

lemma sw_nonneg {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (y : ℤ) : 0 ≤ sw a y :=
  tsum_nonneg (fun x => mul_nonneg (hnn x) (hnn _))

/-- `∑_x a x ^ 2 ≤ atomSup a`: the diagonal symmetrization mass is small. -/
lemma sum_sq_le_atomSup {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) :
    (∑' x : ℤ, (a x) ^ 2) ≤ atomSup a := by
  have hbdd : BddAbove (Set.range a) := bddAbove_atom hnn hsum
  have hle : ∀ x, a x ≤ atomSup a := fun x => le_ciSup hbdd x
  have hsummable_sq : Summable (fun x : ℤ => (a x) ^ 2) := by
    apply hsum.summable.of_nonneg_of_le (fun x => by positivity)
    intro x; nlinarith [hnn x, le_hasSum hsum x (fun i _ => hnn i)]
  calc (∑' x, (a x) ^ 2) ≤ ∑' x, atomSup a * a x :=
        Summable.tsum_le_tsum (fun x => by nlinarith [hle x, hnn x]) hsummable_sq
          (hsum.summable.mul_left _)
    _ = atomSup a * 1 := by rw [tsum_mul_left, hsum.tsum_eq]
    _ = atomSup a := mul_one _

/-
Symmetrization identity: `‖cf a t‖² = ∑_y sw a y · cos (t y)`.
-/
lemma normSq_cf {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) (t : ℝ) :
    ‖cf a t‖ ^ 2 = ∑' y : ℤ, sw a y * Real.cos (t * y) := by
  -- Using the fact that $‖cf a t‖^2 = Complex.normSq (cf a t)$ and $Complex.normSq (cf a t) = (cf a t * conj (cf a t)).re$, we can rewrite the goal.
  suffices h_norm_sq : ‖cf a t‖^2 = (∑' y : ℤ, sw a y * (ch t y)).re by
    convert h_norm_sq using 1;
    rw_mod_cast [ Complex.re_tsum ];
    · unfold ch; norm_num [ Complex.exp_re ] ;
    · have h_summable : Summable (fun y : ℤ => sw a y) := by
        have h_summable : Summable (fun y : ℤ => ∑' x : ℤ, a x * a (x + y)) := by
          have h_summable : Summable (fun p : ℤ × ℤ => a p.1 * a p.2) := by
            exact .of_norm <| by simpa using Summable.mul_norm ( hsum.summable.norm ) ( hsum.summable.norm ) ;
          have h_summable : Summable (fun p : ℤ × ℤ => a p.1 * a (p.1 + p.2)) := by
            convert h_summable.comp_injective ( show Function.Injective ( fun p : ℤ × ℤ => ( p.1, p.1 + p.2 ) ) from fun p q h => by aesop ) using 1;
          refine' summable_of_sum_le _ _;
          exact ∑' p : ℤ × ℤ, a p.1 * a ( p.1 + p.2 );
          · exact fun y => tsum_nonneg fun x => mul_nonneg ( hnn x ) ( hnn ( x + y ) );
          · intro u;
            have h_summable : ∑ x ∈ u, ∑' (x_1 : ℤ), a x_1 * a (x_1 + x) ≤ ∑' (p : ℤ × ℤ), a p.1 * a (p.1 + p.2) := by
              have h_summable : ∑ x ∈ u, ∑' (x_1 : ℤ), a x_1 * a (x_1 + x) = ∑' (p : ℤ × ℤ), a p.1 * a (p.1 + p.2) * (if p.2 ∈ u then 1 else 0) := by
                erw [ Summable.tsum_prod ];
                · rw [ Summable.tsum_comm ];
                  · rw [ tsum_eq_sum ];
                    congr! 1; all_goals aesop;
                  · refine' Summable.of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) ( h_summable.comp_injective ( Prod.swap_injective ) );
                    · exact mul_nonneg ( mul_nonneg ( hnn _ ) ( hnn _ ) ) ( by positivity );
                    · exact if h : p.1 ∈ u then by rw [ Function.uncurry_apply_pair ] ; exact le_of_eq ( by aesop ) else by rw [ Function.uncurry_apply_pair ] ; exact le_trans ( by aesop ) ( mul_nonneg ( hnn _ ) ( hnn _ ) ) ;
                · exact Summable.of_nonneg_of_le ( fun p => mul_nonneg ( mul_nonneg ( hnn _ ) ( hnn _ ) ) ( by positivity ) ) ( fun p => mul_le_of_le_one_right ( mul_nonneg ( hnn _ ) ( hnn _ ) ) ( by aesop ) ) h_summable
              rw [h_summable];
              refine' Summable.tsum_le_tsum _ _ _;
              · exact fun p => mul_le_of_le_one_right ( mul_nonneg ( hnn _ ) ( hnn _ ) ) ( by split_ifs <;> norm_num );
              · exact Summable.of_nonneg_of_le ( fun p => mul_nonneg ( mul_nonneg ( hnn _ ) ( hnn _ ) ) ( by split_ifs <;> norm_num ) ) ( fun p => mul_le_of_le_one_right ( mul_nonneg ( hnn _ ) ( hnn _ ) ) ( by split_ifs <;> norm_num ) ) ‹_›;
              · assumption;
            convert h_summable using 1;
        convert h_summable using 1;
      exact .of_norm <| by simpa [ ch_norm ] using h_summable.norm;
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑' (x : ℤ), ∑' (x' : ℤ), (a x) * (a x') * (ch t (x - x')) = ∑' (y : ℤ), ∑' (x : ℤ), (a x) * (a (x - y)) * (ch t y) := by
    have h_fubini : ∀ {f : ℤ × ℤ → ℂ}, Summable f → ∑' (x : ℤ), ∑' (x' : ℤ), f (x, x') = ∑' (y : ℤ), ∑' (x : ℤ), f (x, x - y) := by
      intro f hf
      have h_fubini : ∑' (p : ℤ × ℤ), f p = ∑' (p : ℤ × ℤ), f (p.1, p.1 - p.2) := by
        rw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun p : ℤ × ℤ => ( p.1, p.1 - p.2 ) ) ⟨ fun p => _, fun p => _ ⟩ ) ];
        exacts [ rfl, fun p q h => by cases p; cases q; norm_num at h; exact Prod.ext ( by linarith ) ( by linarith ), fun p => ⟨ ( p.1, p.1 - p.2 ), by norm_num ⟩ ];
      convert h_fubini using 1;
      · erw [ Summable.tsum_prod ];
        exact hf;
      · erw [ Summable.tsum_prod ];
        · rw [ ← Summable.tsum_comm ];
          convert hf.comp_injective ( show Function.Injective ( fun p : ℤ × ℤ => ( p.2, p.2 - p.1 ) ) from fun p q h => by aesop ) using 1;
        · convert hf.comp_injective ( show Function.Injective ( fun p : ℤ × ℤ => ( p.1, p.1 - p.2 ) ) from fun p q h => by aesop ) using 1;
    convert h_fubini _ using 3;
    rotate_left;
    rotate_left;
    use fun p => ( a p.1 : ℂ ) * ( a p.2 : ℂ ) * ch t ( p.1 - p.2 );
    · have h_summable : Summable (fun p : ℤ × ℤ => (a p.1) * (a p.2)) := by
        exact .of_norm <| by simpa using Summable.mul_norm ( hsum.summable.norm ) ( hsum.summable.norm ) ;
      rw [ ← summable_norm_iff ] at *;
      simp_all +decide [ ch, Complex.norm_exp ];
    · rfl;
    · norm_num;
  convert congr_arg Complex.re h_fubini using 1;
  · have h_fubini : ∑' (x : ℤ), ∑' (x' : ℤ), (a x) * (a x') * (ch t (x - x')) = (∑' (x : ℤ), (a x) * (ch t x)) * (∑' (x' : ℤ), (a x') * (ch t (-x'))) := by
      rw [ ← tsum_mul_right ] ; congr ; ext x ; rw [ ← tsum_mul_left ] ; congr ; ext x' ; ring;
      grind +suggestions;
    rw [ h_fubini, show ( ∑' x' : ℤ, ( a x' : ℂ ) * ch t ( -x' ) ) = ( starRingEnd ℂ ) ( ∑' x : ℤ, ( a x : ℂ ) * ch t x ) from ?_ ];
    · norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
      norm_cast;
    · rw [ Complex.conj_tsum ] ; congr ; ext x ; simp +decide [ ch ] ; ring;
      norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
  · simp +decide [ ← mul_assoc, tsum_mul_right, tsum_mul_left, sw ];
    congr! 2;
    ext y; norm_cast; rw [ ← Equiv.tsum_eq ( Equiv.subRight y ) ] ; norm_num;
    exact Or.inl ( tsum_congr fun x => mul_comm _ _ )

/-
`∑_y sw a y = 1`.
-/
lemma sw_hasSum_one {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) :
    HasSum (sw a) 1 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑' y : ℤ, ∑' x : ℤ, a x * a (x + y) = ∑' x : ℤ, ∑' y : ℤ, a x * a (x + y) := by
    have h_fubini : Summable (fun p : ℤ × ℤ => a p.1 * a p.2) := by
      exact .of_norm <| by simpa using Summable.mul_norm ( hsum.summable.norm ) ( hsum.summable.norm ) ;
    convert ( Summable.tsum_comm _ ) using 1;
    · infer_instance;
    · infer_instance;
    · infer_instance;
    · convert h_fubini.comp_injective ( show Function.Injective ( fun p : ℤ × ℤ => ( p.1, p.1 + p.2 ) ) from fun p q h => by aesop ) using 1;
  -- By Fubini's theorem, we can interchange the order of summation and simplify the expression.
  have h_fubini_simplified : ∑' x : ℤ, ∑' y : ℤ, a x * a (x + y) = ∑' x : ℤ, a x * ∑' y : ℤ, a y := by
    simp +decide only [tsum_mul_left];
    exact tsum_congr fun x => by rw [ eq_comm, ← Equiv.tsum_eq ( Equiv.addLeft x ) ] ; simp +decide ;
  convert h_fubini_simplified ▸ h_fubini ▸ Summable.hasSum _ using 1;
  · rw [ tsum_mul_right, hsum.tsum_eq ] ; norm_num;
  · contrapose! h_fubini_simplified;
    rw [ ← h_fubini, tsum_eq_zero_of_not_summable h_fubini_simplified ] ; norm_num [ hsum.tsum_eq ]

/-- Consequence: `1 - ‖cf a t‖² = ∑_y sw a y · (1 - cos (t y))`. -/
lemma one_sub_normSq_cf {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) (t : ℝ) :
    1 - ‖cf a t‖ ^ 2 = ∑' y : ℤ, sw a y * (1 - Real.cos (t * y)) := by
  have hswsum : HasSum (sw a) 1 := sw_hasSum_one hnn hsum
  have hsum_cos : Summable (fun y : ℤ => sw a y * Real.cos (t * y)) := by
    apply Summable.of_norm_bounded (g := sw a) hswsum.summable
    intro y
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sw_nonneg hnn y)]
    calc sw a y * |Real.cos (t * y)| ≤ sw a y * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sw_nonneg hnn y)
      _ = sw a y := mul_one _
  have hexp : (∑' y : ℤ, sw a y * (1 - Real.cos (t * y)))
      = (∑' y, sw a y) - ∑' y, sw a y * Real.cos (t * y) := by
    rw [← Summable.tsum_sub hswsum.summable hsum_cos]; congr 1; funext y; ring
  rw [normSq_cf hnn hsum t, hexp, hswsum.tsum_eq]

/-- The total off-diagonal symmetrization mass `∑_{y≠0} sw a y = 1 - ∑_x a x²`. -/
lemma gapMass_ge {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) :
    1 - atomSup a ≤ 1 - (∑' x : ℤ, (a x) ^ 2) := by
  have := sum_sq_le_atomSup hnn hsum; linarith

/-! ## Tier 2: the elementary bound `x ≤ exp(-(1-x²)/2)` and single-gap integral -/

lemma norm_cf_le_exp {a : ℤ → ℝ} (hnn : ∀ x, 0 ≤ a x) (hsum : HasSum a 1) (t : ℝ) :
    ‖cf a t‖ ≤ Real.exp (-(1 / 2) * (1 - ‖cf a t‖ ^ 2)) := by
  have hx0 : 0 ≤ ‖cf a t‖ := norm_nonneg _
  have hx1 : ‖cf a t‖ ≤ 1 := cf_norm_le_one hnn hsum t
  have h1 := Real.add_one_le_exp (-(1 / 2) * (1 - ‖cf a t‖ ^ 2))
  nlinarith [h1, hx0, hx1]

/-- `1 - cos v ≥ (2/π²) v²` on `[-π, π]`. -/
lemma one_sub_cos_ge (v : ℝ) (hv : v ∈ Set.Icc (-Real.pi) Real.pi) :
    2 / Real.pi ^ 2 * v ^ 2 ≤ 1 - Real.cos v := by
  obtain ⟨hv1, hv2⟩ := hv
  have hpi : 0 < Real.pi := Real.pi_pos
  have habs : |v| ≤ Real.pi := abs_le.2 ⟨by linarith, hv2⟩
  have hcos : Real.cos v = 1 - 2 * Real.sin (v / 2) ^ 2 := by
    have h2 : Real.cos v = 2 * Real.cos (v / 2) ^ 2 - 1 := by
      have := Real.cos_two_mul (v / 2); rw [show 2 * (v / 2) = v by ring] at this; linarith
    nlinarith [Real.sin_sq_add_cos_sq (v / 2), h2]
  have hjord : |v| / Real.pi ≤ Real.sin (|v| / 2) := by
    have h := Real.mul_le_sin (x := |v| / 2) (by positivity) (by nlinarith [abs_nonneg v])
    calc |v| / Real.pi = 2 / Real.pi * (|v| / 2) := by ring
      _ ≤ Real.sin (|v| / 2) := h
  have hsin_nonneg : 0 ≤ Real.sin (|v| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [abs_nonneg v])
  have hsq : Real.sin (v / 2) ^ 2 = Real.sin (|v| / 2) ^ 2 := by
    rcases abs_cases v with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show -v / 2 = -(v / 2) by ring, Real.sin_neg]; ring
  have hkey : (|v| / Real.pi) ^ 2 ≤ Real.sin (|v| / 2) ^ 2 :=
    sq_le_sq' ((neg_nonpos.2 hsin_nonneg).trans (by positivity)) hjord
  have hkey' : |v| ^ 2 / Real.pi ^ 2 ≤ Real.sin (|v| / 2) ^ 2 := by rw [← div_pow]; exact hkey
  rw [hcos, hsq, (sq_abs v).symm]
  have hpisq : (0 : ℝ) < Real.pi ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_sub_iff_add_le, div_add' _ _ _ (ne_of_gt hpisq),
     div_le_iff₀ hpisq] at *
  nlinarith [hkey', hpisq]

/-- Periodicity reduction: for `y ≠ 0` and a `2π`-periodic continuous `g`,
`∫_{-π}^{π} g(t·y) dt = ∫_{-π}^{π} g`. -/
lemma periodic_scale_integral (g : ℝ → ℝ) (hg : Function.Periodic g (2 * Real.pi))
    (hgc : Continuous g) (y : ℤ) (hy : y ≠ 0) :
    (∫ t in (-Real.pi)..Real.pi, g (t * y)) = ∫ u in (-Real.pi)..Real.pi, g u := by
  have hy' : (↑y : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hy
  have hint : ∀ t₁ t₂, IntervalIntegrable g volume t₁ t₂ := fun t₁ t₂ => hgc.intervalIntegrable _ _
  have hcomm : (∫ t in (-Real.pi)..Real.pi, g (t * ↑y)) = ∫ t in (-Real.pi)..Real.pi, g (↑y * t) := by
    congr 1; ext t; rw [mul_comm]
  rw [hcomm, intervalIntegral.integral_comp_mul_left g hy']
  have he : (↑y : ℝ) * Real.pi = ↑y * (-Real.pi) + (y : ℤ) • (2 * Real.pi) := by
    rw [zsmul_eq_mul]; ring
  have hstep : (∫ u in (↑y * (-Real.pi))..(↑y * Real.pi), g u)
      = (y : ℤ) • ∫ u in (-Real.pi)..Real.pi, g u := by
    rw [he, hg.intervalIntegral_add_zsmul_eq y (↑y * (-Real.pi)) hint]
    congr 1
    have hae := hg.intervalIntegral_add_eq (↑y * (-Real.pi)) (-Real.pi)
    rw [hae]; congr 1; ring
  rw [hstep, zsmul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hy', one_mul]

/-- Single-gap integral bound (with periodicity reduction), `y ≠ 0`, `α > 0`. -/
lemma gap_integral_le (y : ℤ) (hy : y ≠ 0) (α : ℝ) (hα : 0 < α) :
    (∫ t in (-Real.pi)..Real.pi, Real.exp (-(α * (1 - Real.cos (t * y)))))
      ≤ 4 * Real.pi / Real.sqrt (1 + α) := by
  have hgc : Continuous (fun u => Real.exp (-(α * (1 - Real.cos u)))) := by fun_prop
  have hcg : Continuous (fun u => Real.exp (-(2 * α / Real.pi ^ 2) * u ^ 2)) := by fun_prop
  have hg : Function.Periodic (fun u => Real.exp (-(α * (1 - Real.cos u)))) (2 * Real.pi) :=
    fun u => by simp [Real.cos_add_two_pi]
  have hper := periodic_scale_integral (fun u => Real.exp (-(α * (1 - Real.cos u)))) hg hgc y hy
  calc (∫ t in (-Real.pi)..Real.pi, Real.exp (-(α * (1 - Real.cos (t * ↑y)))))
      = ∫ u in (-Real.pi)..Real.pi, Real.exp (-(α * (1 - Real.cos u))) := hper
    _ ≤ 4 * Real.pi / Real.sqrt (1 + α) := by
        have h_bound : ∀ u ∈ Set.Icc (-Real.pi) Real.pi,
            Real.exp (-(α * (1 - Real.cos u))) ≤ Real.exp (-(2 * α / Real.pi ^ 2) * u ^ 2) := by
          intro u hu
          refine Real.exp_le_exp.mpr ?_
          have h := mul_le_mul_of_nonneg_left (one_sub_cos_ge u hu) hα.le
          have he : (2 * α / Real.pi ^ 2) * u ^ 2 = α * (2 / Real.pi ^ 2 * u ^ 2) := by ring
          linarith [h, he]
        have hIP : MeasureTheory.IntegrableOn (fun u => Real.exp (-(α * (1 - Real.cos u))))
            (Set.Ioc (-Real.pi) Real.pi) MeasureTheory.volume :=
          (hgc.intervalIntegrable (-Real.pi) Real.pi).1
        have hIG : MeasureTheory.IntegrableOn (fun u => Real.exp (-(2 * α / Real.pi ^ 2) * u ^ 2))
            (Set.Ioc (-Real.pi) Real.pi) MeasureTheory.volume :=
          (hcg.intervalIntegrable (-Real.pi) Real.pi).1
        have hgauss : ∫ u in (-Real.pi)..Real.pi, Real.exp (-(α * (1 - Real.cos u)))
            ≤ Real.sqrt (Real.pi ^ 3 / (2 * α)) := by
          have h1 : ∫ u in (-Real.pi)..Real.pi, Real.exp (-(α * (1 - Real.cos u)))
              ≤ ∫ u, Real.exp (-(2 * α / Real.pi ^ 2) * u ^ 2) := by
            rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
            refine le_trans (MeasureTheory.setIntegral_mono_on hIP hIG measurableSet_Ioc
              (fun u hu => h_bound u (Set.Ioc_subset_Icc_self hu))) ?_
            refine MeasureTheory.setIntegral_le_integral ?_
              (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)
            simpa using integrable_exp_neg_mul_sq (show (0:ℝ) < 2 * α / Real.pi ^ 2 by positivity)
          have hg2 := integral_gaussian (2 * α / Real.pi ^ 2)
          have heq : Real.sqrt (Real.pi / (2 * α / Real.pi ^ 2))
              = Real.sqrt (Real.pi ^ 3 / (2 * α)) := by congr 1; field_simp
          rw [heq] at hg2; linarith [h1, hg2.le, hg2.ge]
        have htriv : ∫ u in (-Real.pi)..Real.pi, Real.exp (-(α * (1 - Real.cos u))) ≤ 2 * Real.pi := by
          have hmono : (∫ u in (-Real.pi)..Real.pi, Real.exp (-(α * (1 - Real.cos u))))
              ≤ ∫ _u in (-Real.pi)..Real.pi, (1:ℝ) := intervalIntegral.integral_mono_on
            (by linarith [Real.pi_pos]) (hgc.intervalIntegrable _ _)
            (intervalIntegral.intervalIntegrable_const)
            (fun u _ => Real.exp_le_one_iff.mpr (by nlinarith [Real.cos_le_one u, hα.le]))
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hmono
          linarith [hmono]
        by_cases hc : α ≤ 3
        · refine htriv.trans ?_
          rw [le_div_iff₀ (by positivity)]
          nlinarith [Real.pi_pos, Real.sq_sqrt (show (0:ℝ) ≤ 1 + α by positivity),
            Real.sqrt_nonneg (1 + α)]
        · refine hgauss.trans ?_
          have h16 : Real.sqrt (16 * Real.pi ^ 2) = 4 * Real.pi := by
            rw [show (16 * Real.pi ^ 2) = (4 * Real.pi) ^ 2 by ring, Real.sqrt_sq (by positivity)]
          have hrhs : (4 * Real.pi) / Real.sqrt (1 + α) = Real.sqrt (16 * Real.pi ^ 2 / (1 + α)) := by
            rw [Real.sqrt_div (by positivity), h16]
          rw [hrhs]
          apply Real.sqrt_le_sqrt
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hα3 : (3:ℝ) < α := not_le.mp hc
          have hkey : Real.pi * (1 + α) ≤ 32 * α := by nlinarith [Real.pi_le_four, hα3]
          nlinarith [mul_le_mul_of_nonneg_left hkey (sq_nonneg Real.pi), Real.pi_pos]

/-- Finite Jensen collapse: the product-over-gaps integral bound.  For a finite family of
nonnegative weights `β i` attached to nonzero gaps `yy i`, convexity of `exp` collapses the
product so the single-gap bound applies with the total mass. -/
lemma finite_gap_bound {ι : Type} (F : Finset ι) (β : ι → ℝ) (yy : ι → ℤ)
    (hβ : ∀ i ∈ F, 0 ≤ β i) (hy : ∀ i ∈ F, yy i ≠ 0) (hW : 0 < ∑ i ∈ F, β i) :
    (∫ t in (-Real.pi)..Real.pi, Real.exp (-(1/2) * ∑ i ∈ F, β i * (1 - Real.cos (t * yy i))))
      ≤ 4 * Real.pi / Real.sqrt (1 + (∑ i ∈ F, β i) / 2) := by
  set W := ∑ i ∈ F, β i with hWdef
  have hsumw : ∑ i ∈ F, β i / W = 1 := by rw [← Finset.sum_div, ← hWdef, div_self (ne_of_gt hW)]
  have hjensen : ∀ t : ℝ, Real.exp (-(1/2) * ∑ i ∈ F, β i * (1 - Real.cos (t * yy i)))
      ≤ ∑ i ∈ F, (β i / W) * Real.exp (-((W/2) * (1 - Real.cos (t * yy i)))) := by
    intro t
    have h := ConvexOn.map_sum_le convexOn_exp (w := fun i => β i / W)
      (p := fun i => -((W/2) * (1 - Real.cos (t * yy i)))) (t := F)
      (fun i hi => div_nonneg (hβ i hi) hW.le) hsumw (fun i hi => Set.mem_univ _)
    have hexp : ∑ i ∈ F, (β i / W) • (-((W/2) * (1 - Real.cos (t * yy i))))
        = -(1/2) * ∑ i ∈ F, β i * (1 - Real.cos (t * yy i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [smul_eq_mul]; field_simp
    rw [hexp] at h
    simpa only [smul_eq_mul] using h
  have hcontR : Continuous (fun t : ℝ =>
      ∑ i ∈ F, (β i / W) * Real.exp (-((W/2) * (1 - Real.cos (t * yy i))))) := by fun_prop
  have hcontL : Continuous (fun t : ℝ =>
      Real.exp (-(1/2) * ∑ i ∈ F, β i * (1 - Real.cos (t * yy i)))) := by fun_prop
  calc (∫ t in (-Real.pi)..Real.pi, Real.exp (-(1/2) * ∑ i ∈ F, β i * (1 - Real.cos (t * yy i))))
      ≤ ∫ t in (-Real.pi)..Real.pi,
          ∑ i ∈ F, (β i / W) * Real.exp (-((W/2) * (1 - Real.cos (t * yy i)))) :=
        intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) (hcontL.intervalIntegrable _ _)
          (hcontR.intervalIntegrable _ _) (fun t _ => hjensen t)
    _ = ∑ i ∈ F, (β i / W) * ∫ t in (-Real.pi)..Real.pi,
          Real.exp (-((W/2) * (1 - Real.cos (t * yy i)))) := by
        rw [intervalIntegral.integral_finset_sum]
        · exact Finset.sum_congr rfl (fun i hi => intervalIntegral.integral_const_mul _ _)
        · exact fun i hi => ((by fun_prop : Continuous fun t : ℝ =>
            (β i / W) * Real.exp (-((W/2) * (1 - Real.cos (t * yy i))))).intervalIntegrable _ _)
    _ ≤ ∑ i ∈ F, (β i / W) * (4 * Real.pi / Real.sqrt (1 + W/2)) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        exact mul_le_mul_of_nonneg_left (gap_integral_le (yy i) (hy i hi) (W/2) (by linarith))
          (div_nonneg (hβ i hi) hW.le)
    _ = 4 * Real.pi / Real.sqrt (1 + W/2) := by rw [← Finset.sum_mul, hsumw, one_mul]

/-- Product/exponential bound for the sum characteristic function. -/
lemma norm_cf_aS_le_exp (n : ℕ) (a : Fin n → ℤ → ℝ) (aS : ℤ → ℝ)
    (hnn : ∀ j x, 0 ≤ a j x) (hsum : ∀ j, HasSum (a j) 1)
    (hprod : ∀ t, cf aS t = ∏ j, cf (a j) t) (t : ℝ) :
    ‖cf aS t‖ ≤ Real.exp (-(1/2) * ∑ j, (1 - ‖cf (a j) t‖ ^ 2)) := by
  rw [hprod, norm_prod]
  calc ∏ j, ‖cf (a j) t‖
      ≤ ∏ j, Real.exp (-(1/2) * (1 - ‖cf (a j) t‖ ^ 2)) :=
        Finset.prod_le_prod (fun j _ => norm_nonneg _)
          (fun j _ => norm_cf_le_exp (hnn j) (hsum j) t)
    _ = Real.exp (∑ j, -(1/2) * (1 - ‖cf (a j) t‖ ^ 2)) := (Real.exp_sum _ _).symm
    _ = Real.exp (-(1/2) * ∑ j, (1 - ‖cf (a j) t‖ ^ 2)) := by rw [Finset.mul_sum]

/-! ## Tier 2: assembly -/

/-
**Kolmogorov–Rogozin anti-concentration (abstract, pmf form).**
For pmfs `a j` on `ℤ` and a pmf `aS` whose characteristic function factorises as
`cf aS t = ∏_j cf (a j) t`, the largest atom of `aS` obeys the bound
`atomSup aS ≤ C · (∑_j (1 - atomSup (a j)))^{-1/2}` for a universal constant `C`.
-/
set_option maxHeartbeats 2000000 in
theorem KR_abstract :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (a : Fin n → ℤ → ℝ) (aS : ℤ → ℝ),
      (∀ j x, 0 ≤ a j x) → (∀ j, HasSum (a j) 1) →
      (∀ x, 0 ≤ aS x) → HasSum aS 1 →
      (∀ t : ℝ, cf aS t = ∏ j, cf (a j) t) →
      0 < (∑ j, (1 - atomSup (a j))) →
      atomSup aS ≤ C / Real.sqrt (∑ j, (1 - atomSup (a j))) := by
  refine' ⟨ 2 * Real.sqrt 2, by positivity, _ ⟩;
  intro n a aS hnn hsum hnn' hsum' hprod hW_pos
  set S := ∑ j, (1 - atomSup (a j))
  have hS_pos : 0 < S := hW_pos
  have hW'' : S ≤ ∑ j, (1 - ∑' x, (a j x)^2) := by
    exact Finset.sum_le_sum fun j _ => sub_le_sub_left ( sum_sq_le_atomSup ( hnn j ) ( hsum j ) ) _
  generalize_proofs at *; (
  -- Step 1: Choose a finite gap set with mass close to `S`.
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin n × ℤ), (∀ p ∈ F, p.2 ≠ 0) ∧ (∑ p ∈ F, sw (a p.1) p.2) > max (S - 2) 0 ∧ (∑ p ∈ F, sw (a p.1) p.2) > 0 := by
    have h_summable : Summable (fun p : Fin n × ℤ => if p.2 = 0 then 0 else sw (a p.1) p.2) := by
      have h_summable : ∀ j, Summable (fun y => if y = 0 then 0 else sw (a j) y) := by
        intro j
        have h_summable : Summable (fun y => sw (a j) y) := by
          exact HasSum.summable ( sw_hasSum_one ( hnn j ) ( hsum j ) )
        generalize_proofs at *; (
        convert h_summable.sub ( show Summable fun y => if y = 0 then sw ( a j ) 0 else 0 from ⟨ _, hasSum_single 0 <| by aesop ⟩ ) using 2 ; aesop)
      generalize_proofs at *; (
      rw [ summable_prod_of_nonneg ];
      · exact ⟨ h_summable, ⟨ _, hasSum_fintype _ ⟩ ⟩;
      · exact fun p => by split_ifs <;> [ exact le_rfl; exact sw_nonneg ( hnn _ ) _ ] ;)
    generalize_proofs at *; (
    have h_summable : ∑' p : Fin n × ℤ, (if p.2 = 0 then 0 else sw (a p.1) p.2) ≥ S := by
      have h_summable : ∑' p : Fin n × ℤ, (if p.2 = 0 then 0 else sw (a p.1) p.2) = ∑ j, (∑' y : ℤ, sw (a j) y - sw (a j) 0) := by
        have h_summable : ∀ j, ∑' y : ℤ, (if y = 0 then 0 else sw (a j) y) = ∑' y : ℤ, sw (a j) y - sw (a j) 0 := by
          intro j; rw [ eq_comm, Summable.tsum_eq_add_tsum_ite ] ; ring;
          exact sw_hasSum_one ( hnn j ) ( hsum j ) |> HasSum.summable
        generalize_proofs at *; (
        erw [ Summable.tsum_prod ] ; aesop;
        assumption)
      generalize_proofs at *; (
      have h_summable : ∀ j, ∑' y : ℤ, sw (a j) y = 1 := by
        exact fun j => HasSum.tsum_eq ( sw_hasSum_one ( hnn j ) ( hsum j ) )
      generalize_proofs at *; (
      simp_all +decide [ sw ];
      simpa only [ sq ] using hW''))
    generalize_proofs at *; (
    have h_summable : ∃ F : Finset (Fin n × ℤ), (∑ p ∈ F, (if p.2 = 0 then 0 else sw (a p.1) p.2)) > max (S - 2) 0 := by
      have h_summable : Filter.Tendsto (fun F : Finset (Fin n × ℤ) => ∑ p ∈ F, (if p.2 = 0 then 0 else sw (a p.1) p.2)) Filter.atTop (nhds (∑' p : Fin n × ℤ, (if p.2 = 0 then 0 else sw (a p.1) p.2))) := by
        exact Summable.hasSum ‹_› |> fun h => h.comp <| Filter.tendsto_id;
      generalize_proofs at *; (
      exact ( h_summable.eventually ( lt_mem_nhds <| by cases max_cases ( S - 2 ) 0 <;> linarith ) ) |> fun h => h.exists)
    generalize_proofs at *; (
    obtain ⟨ F, hF ⟩ := h_summable; use F.filter ( fun p => p.2 ≠ 0 ) ; simp_all +decide [ Finset.sum_filter ] ;)))
  generalize_proofs at *; (
  -- Step 2: Pointwise gap-partial bound.
  have h_pointwise : ∀ t : ℝ, ∑ p ∈ F, sw (a p.1) p.2 * (1 - Real.cos (t * p.2)) ≤ ∑ j, (1 - ‖cf (a j) t‖ ^ 2) := by
    intro t
    have h_pointwise_step : ∀ j, ∑ p ∈ F.filter (fun p => p.1 = j), sw (a j) p.2 * (1 - Real.cos (t * p.2)) ≤ ∑' y, sw (a j) y * (1 - Real.cos (t * y)) := by
      intro j
      have h_pointwise_step : ∑ p ∈ F.filter (fun p => p.1 = j), sw (a j) p.2 * (1 - Real.cos (t * p.2)) ≤ ∑ y ∈ Finset.image (fun p => p.2) (F.filter (fun p => p.1 = j)), sw (a j) y * (1 - Real.cos (t * y)) := by
        rw [ Finset.sum_image ];
        intro p hp q hq; aesop;
      generalize_proofs at *; (
      refine le_trans h_pointwise_step <| Summable.sum_le_tsum _ ?_ ?_ <;> norm_num +zetaDelta at *; (
      exact fun _ _ => mul_nonneg ( sw_nonneg ( hnn j ) _ ) ( sub_nonneg.2 ( Real.cos_le_one _ ) ));
      have h_summable : Summable (fun y => sw (a j) y) := by
        exact HasSum.summable ( sw_hasSum_one ( hnn j ) ( hsum j ) )
      generalize_proofs at *; (
      refine' .of_nonneg_of_le ( fun y => mul_nonneg ( show 0 ≤ sw ( a j ) y from _ ) ( sub_nonneg.mpr ( Real.cos_le_one _ ) ) ) ( fun y => mul_le_mul_of_nonneg_left ( sub_le_sub_left ( Real.neg_one_le_cos _ ) _ ) ( show 0 ≤ sw ( a j ) y from _ ) ) ( h_summable.mul_right _ ); all_goals exact sw_nonneg ( hnn j ) y))
    generalize_proofs at *; (
    convert Finset.sum_le_sum fun j _ => h_pointwise_step j using 1;
    any_goals exact Finset.univ;
    · rw [ Finset.sum_sigma' ];
      refine' Finset.sum_bij ( fun p hp => ⟨ p.1, p ⟩ ) _ _ _ _ <;> aesop;
    · exact Finset.sum_congr rfl fun _ _ => one_sub_normSq_cf ( hnn _ ) ( hsum _ ) _ ▸ rfl)
  generalize_proofs at *; (
  -- Step 3: Assemble the bounds.
  have h_assemble : atomSup aS ≤ (1 / (2 * Real.pi)) * (4 * Real.pi / Real.sqrt (1 + (∑ p ∈ F, sw (a p.1) p.2) / 2)) := by
    refine' le_trans ( atomSup_le_integral hnn' hsum' ) _;
    refine' mul_le_mul_of_nonneg_left _ ( by positivity );
    refine' le_trans ( intervalIntegral.integral_mono_on _ _ _ _ ) _;
    use fun t => Real.exp ( - ( 1 / 2 ) * ∑ p ∈ F, sw ( a p.1 ) p.2 * ( 1 - Real.cos ( t * p.2 ) ) );
    · linarith [ Real.pi_pos ];
    · apply_rules [ Continuous.intervalIntegrable ];
      refine' continuous_norm.comp _;
      refine' continuous_tsum _ _ _;
      use fun n => |aS n|;
      · exact fun _ => continuous_const.mul ( Complex.continuous_exp.comp <| by continuity );
      · exact hsum'.summable.abs;
      · norm_num [ ch, Complex.norm_exp ];
    · exact Continuous.intervalIntegrable ( by exact Real.continuous_exp.comp <| by exact Continuous.mul continuous_const <| by exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const ) <| by exact Continuous.sub continuous_const <| Real.continuous_cos.comp <| by continuity ) _ _;
    · intro t ht; specialize h_pointwise t; simp_all +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _ ] ;
      have := norm_cf_aS_le_exp n a aS hnn hsum hprod t; simp_all +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _ ] ;
      exact this.trans ( Real.exp_le_exp.mpr <| by linarith );
    · convert finite_gap_bound F ( fun p => sw ( a p.1 ) p.2 ) ( fun p => p.2 ) _ _ _ using 1 <;> norm_num [ hF ];
      · exact fun j y hy => sw_nonneg ( hnn j ) y;
      · exact fun j x hx => hF.1 _ hx
  generalize_proofs at *; (
  refine le_trans h_assemble ?_;
  field_simp;
  rw [ div_le_iff₀ ] <;> norm_num;
  · rw [ mul_assoc, mul_div_cancel₀ _ ( by positivity ) ] ; exact mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| by linarith [ le_max_left ( S - 2 ) 0, le_max_right ( S - 2 ) 0 ] ) zero_le_four;
  · linarith [ hF.2.2 ]))))

/-! ## Measure-theoretic interface -/

/-
Bridge: the pmf-characteristic function `cf` of an integer random variable coincides with
Mathlib's `charFun` of the real pushforward.
-/
lemma cf_pmf_eq_charFun {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω → ℤ) (hY : Measurable Y) (t : ℝ) :
    cf (fun x => (μ (Y ⁻¹' {x})).toReal) t
      = charFun (μ.map (fun ω => ((Y ω : ℤ) : ℝ))) t := by
  rw [ charFun ];
  convert ( MeasureTheory.integral_map ( f := fun x => Complex.exp ( x * t * Complex.I ) ) ?_ ( ?_ ) ) using 1;
  rotate_left;
  convert MeasureTheory.integral_map _ _;
  rotate_left;
  fun_prop;
  fun_prop;
  use fun ω => Y ω;
  · fun_prop;
  · exact Continuous.aestronglyMeasurable ( by continuity );
  · rw [ MeasureTheory.integral_map ];
    · have h_integral : ∫ ω, Complex.exp (↑(Y ω) * ↑t * Complex.I) ∂μ = ∑' x : ℤ, ∫ ω in Y ⁻¹' {x}, Complex.exp (↑x * ↑t * Complex.I) ∂μ := by
        have h_integral : ∫ ω, Complex.exp (↑(Y ω) * ↑t * Complex.I) ∂μ = ∑' x : ℤ, ∫ ω in Y ⁻¹' {x}, Complex.exp (↑(Y ω) * ↑t * Complex.I) ∂μ := by
          rw [ ← MeasureTheory.integral_iUnion ];
          · rw [ MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ] ; aesop;
          · exact fun i => hY ( MeasurableSingletonClass.measurableSet_singleton i );
          · exact fun x y hxy => Set.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun ω => 1;
            · norm_num;
            · fun_prop;
            · norm_num [ Complex.norm_exp ];
        convert h_integral using 3;
        exact MeasureTheory.setIntegral_congr_fun ( hY ( MeasurableSingletonClass.measurableSet_singleton _ ) ) fun ω hω => by aesop;
      simp_all +decide [ cf, ch ];
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, MeasureTheory.measureReal_def ];
    · exact Measurable.aemeasurable ( by measurability );
    · exact Continuous.aestronglyMeasurable ( by continuity );
  · simp +decide [ inner, mul_comm ]

/-- The pmf of an integer random variable is a genuine pmf: nonnegative and summing to `1`. -/
lemma pmf_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℤ) (x : ℤ) : 0 ≤ (μ (Y ⁻¹' {x})).toReal := ENNReal.toReal_nonneg

lemma pmf_hasSum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω → ℤ) (hY : Measurable Y) :
    HasSum (fun x => (μ (Y ⁻¹' {x})).toReal) 1 := by
  have hsingle : ∀ x : ℤ, μ (Y ⁻¹' {x}) = (μ.map Y) {x} := by
    intro x; rw [Measure.map_apply hY (measurableSet_singleton x)]
  have hmap : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have htsum : ∑' x : ℤ, (μ.map Y) {x} = 1 := by
    have := Measure.tsum_indicator_apply_singleton (μ.map Y) Set.univ MeasurableSet.univ
    simpa using this
  have hsum := ENNReal.hasSum_toReal (f := fun x => (μ.map Y) {x}) (by rw [htsum]; simp)
  have heq : (∑' x : ℤ, ((μ.map Y) {x}).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun x => measure_ne_top _ _), htsum]; simp
  rw [heq] at hsum
  simp_rw [hsingle]; exact hsum

/-
Product formula for the characteristic function of a sum of independent integer
random variables.
-/
lemma cf_pmf_sum_eq_prod {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) (Y : Fin n → Ω → ℤ)
    (hmeas : ∀ j, Measurable (Y j)) (hindep : iIndepFun Y μ) (t : ℝ) :
    cf (fun x => (μ ((fun ω => ∑ j, Y j ω) ⁻¹' {x})).toReal) t
      = ∏ j, cf (fun x => (μ (Y j ⁻¹' {x})).toReal) t := by
  simp +decide [cf];
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∫ ω, Complex.exp (t * (∑ j, Y j ω) * Complex.I) ∂μ = ∏ j, ∫ ω, Complex.exp (t * Y j ω * Complex.I) ∂μ := by
    have h_fubini : ∀ (f : Fin n → Ω → ℂ), (∀ j, Measurable (f j)) → (∀ j, MeasureTheory.Integrable (f j) μ) → (iIndepFun (fun j ω => f j ω) μ) → ∫ ω, ∏ j, f j ω ∂μ = ∏ j, ∫ ω, f j ω ∂μ := by
      intro f hf_meas hf_int hf_indep
      have h_fubini : ∫ ω, ∏ j, f j ω ∂μ = ∏ j, ∫ ω, f j ω ∂μ := by
        have h_indep : ProbabilityTheory.iIndepFun (fun j ω => f j ω) μ := hf_indep
        convert h_indep.integral_prod_eq_prod_integral _;
        · simp +decide [ Finset.prod_apply ];
        · exact fun j => ( hf_int j ).1;
      exact h_fubini;
    convert h_fubini _ _ _ _ using 3;
    · simp +decide [ ← Complex.exp_sum, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul ];
    · fun_prop;
    · intro j;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      exacts [ fun _ => 1, MeasureTheory.integrable_const _, Measurable.aestronglyMeasurable ( by measurability ), Filter.Eventually.of_forall fun _ => by simp +decide [ Complex.norm_exp ] ];
    · convert hindep.comp ( fun j => fun x : ℤ => Complex.exp ( t * x * Complex.I ) ) using 1;
      exact Iff.symm (imp_iff_right fun i ⦃t⦄ a => trivial);
  convert h_fubini using 1;
  · convert cf_pmf_eq_charFun μ ( fun ω => ∑ j, Y j ω ) ( by measurability ) t |> Eq.symm using 1;
    · convert cf_pmf_eq_charFun μ ( fun ω => ∑ j, Y j ω ) ( by measurability ) t using 1;
    · convert cf_pmf_eq_charFun μ ( fun ω => ∑ j, Y j ω ) ( by measurability ) t |> Eq.symm using 1;
      rw [ charFun ];
      rw [ MeasureTheory.integral_map ];
      · simp +decide [ mul_assoc, mul_comm, mul_left_comm, inner ];
      · fun_prop;
      · fun_prop;
  · refine' Finset.prod_congr rfl fun j _ => _;
    convert cf_pmf_eq_charFun μ ( Y j ) ( hmeas j ) t |> Eq.symm using 1;
    · convert cf_pmf_eq_charFun μ ( Y j ) ( hmeas j ) t using 1;
    · convert cf_pmf_eq_charFun μ ( Y j ) ( hmeas j ) t |> Eq.symm using 1;
      rw [ charFun, MeasureTheory.integral_map ];
      · simp +decide [ mul_assoc, mul_comm, mul_left_comm, inner ];
      · exact Measurable.aemeasurable ( by measurability );
      · exact Continuous.aestronglyMeasurable ( by continuity )

/-! ## Concentration helpers for the two-valued corollary -/

/-- Concentration is shift-invariant: adding a constant permutes the atoms. -/
lemma atomSup_add_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℤ) (c : ℤ) :
    atomSup (fun x => (μ ((fun ω => c + Y ω) ⁻¹' {x})).toReal)
      = atomSup (fun x => (μ (Y ⁻¹' {x})).toReal) := by
  have hpre : ∀ x : ℤ, (fun ω => c + Y ω) ⁻¹' {x} = Y ⁻¹' {x - c} := by
    intro x; ext ω; simp [eq_sub_iff_add_eq, add_comm]
  simp only [hpre, atomSup]
  exact (Equiv.subRight c).iSup_comp (g := fun x => (μ (Y ⁻¹' {x})).toReal)

/-- A two-valued increment with both atoms `≥ δ` has largest atom `≤ 1 - δ`. -/
lemma atomSup_two_valued_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω → ℤ) (hY : Measurable Y) (δ : ℝ) (u v : ℤ) (huv : u ≠ v)
    (hu : δ ≤ (μ (Y ⁻¹' {u})).toReal) (hv : δ ≤ (μ (Y ⁻¹' {v})).toReal) :
    atomSup (fun x => (μ (Y ⁻¹' {x})).toReal) ≤ 1 - δ := by
  have hbound : ∀ w x : ℤ, w ≠ x → δ ≤ (μ (Y ⁻¹' {w})).toReal →
      (μ (Y ⁻¹' {x})).toReal ≤ 1 - δ := by
    intro w x hwx hw
    have hdisj : Disjoint (Y ⁻¹' {x}) (Y ⁻¹' {w}) :=
      (Set.disjoint_singleton.2 (Ne.symm hwx)).preimage Y
    have hadd : μ (Y ⁻¹' {x}) + μ (Y ⁻¹' {w}) ≤ 1 := by
      rw [← measure_union hdisj (hY (measurableSet_singleton w))]
      calc μ (Y ⁻¹' {x} ∪ Y ⁻¹' {w}) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have h1 : (μ (Y ⁻¹' {x})).toReal + (μ (Y ⁻¹' {w})).toReal ≤ 1 := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      calc (μ (Y ⁻¹' {x}) + μ (Y ⁻¹' {w})).toReal ≤ (1 : ENNReal).toReal :=
            ENNReal.toReal_mono (by simp) hadd
        _ = 1 := by simp
    linarith [hw, h1]
  refine ciSup_le (fun x => ?_)
  by_cases hxu : x = u
  · exact hbound v x (by rw [hxu]; exact huv.symm) hv
  · exact hbound u x (Ne.symm hxu) hu

/-- The largest atom of a (deterministic) constant integer variable is `1`. -/
lemma atomSup_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℤ) :
    atomSup (fun x => (μ ((fun _ : Ω => c) ⁻¹' {x})).toReal) = 1 := by
  have hf : (fun x => (μ ((fun _ : Ω => c) ⁻¹' {x})).toReal)
      = fun x => if x = c then (1 : ℝ) else 0 := by
    funext x
    rw [Set.preimage_const]
    by_cases hx : c ∈ ({x} : Set ℤ)
    · rw [if_pos hx]; simp only [Set.mem_singleton_iff] at hx; simp [hx.symm]
    · rw [if_neg hx]; simp only [Set.mem_singleton_iff] at hx; simp [Ne.symm hx]
  rw [hf, atomSup]
  apply le_antisymm
  · exact ciSup_le (fun x => by by_cases h : x = c <;> simp [h])
  · exact le_ciSup_of_le ⟨1, by rintro _ ⟨x, rfl⟩; by_cases h : x = c <;> simp [h]⟩ c (by simp)

/-! ## Poisson lower-tail Chernoff bound -/

/-- **Poisson lower tail.**  If a random variable `Mrv` dominates a rate-`t` Poisson count in
the sense of the CDF bound `ℙ(Mrv < k) ≤ e^{-t} ∑_{i<k} t^i/i!`, then
`ℙ(Mrv < t/2) ≤ e^{-c t}` with `c = (1 - log 2)/2 > 0`. -/
theorem poisson_lower_tail :
    ∃ c : ℝ, 0 < c ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      (Mrv : Ω → ℕ) (t : ℝ), 0 ≤ t →
      (∀ k : ℕ, (μ {ω | Mrv ω < k}).toReal
          ≤ Real.exp (-t) * ∑ i ∈ Finset.range k, t ^ i / i.factorial) →
      (μ {ω | (Mrv ω : ℝ) < t / 2}).toReal ≤ Real.exp (-(c * t)) := by
  refine ⟨(1 - Real.log 2) / 2, ?_, ?_⟩
  · have h : Real.log 2 < 1 := by
      have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num); linarith
    linarith
  · intro Ω _ μ Mrv t ht hdom
    set θ := Real.log 2 with hθ
    have hθpos : 0 < θ := Real.log_pos (by norm_num)
    have hehalf : Real.exp (-θ) = 1 / 2 := by
      rw [hθ, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    set K := ⌈t / 2⌉₊ with hK
    have hset : {ω | (Mrv ω : ℝ) < t / 2} = {ω | Mrv ω < K} := by
      ext ω; simp only [Set.mem_setOf_eq, hK, Nat.lt_ceil]
    rw [hset]
    refine (hdom K).trans ?_
    have hsum_le : ∑ i ∈ Finset.range K, t ^ i / i.factorial
        ≤ Real.exp (θ * t / 2) * Real.exp (t / 2) := by
      calc ∑ i ∈ Finset.range K, t ^ i / i.factorial
          ≤ ∑ i ∈ Finset.range K, Real.exp (θ * t / 2) * ((t / 2) ^ i / i.factorial) := by
            apply Finset.sum_le_sum
            intro i hi
            have hile : (i : ℝ) ≤ t / 2 := le_of_lt (Nat.lt_ceil.1 (Finset.mem_range.1 hi))
            have hhalf_pow : (t / 2) ^ i = t ^ i * Real.exp (-θ * i) := by
              rw [show (t / 2 : ℝ) = t * Real.exp (-θ) from by rw [hehalf]; ring, mul_pow,
                ← Real.exp_nat_mul, mul_comm (i : ℝ) (-θ)]
            have key : t ^ i ≤ Real.exp (θ * t / 2) * (t / 2) ^ i := by
              rw [hhalf_pow]
              have heq : Real.exp (θ * t / 2) * (t ^ i * Real.exp (-θ * i))
                  = t ^ i * Real.exp (θ * (t / 2 - i)) := by
                rw [← mul_assoc, mul_comm (Real.exp (θ * t / 2)) (t ^ i), mul_assoc,
                  ← Real.exp_add]
                congr 2; ring
              rw [heq]
              nlinarith [pow_nonneg ht i,
                Real.one_le_exp_iff.2 (mul_nonneg hθpos.le (by linarith : (0:ℝ) ≤ t / 2 - i))]
            rw [mul_div_assoc']
            exact div_le_div_of_nonneg_right key (by positivity)
        _ ≤ Real.exp (θ * t / 2) * Real.exp (t / 2) := by
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left
              (Real.sum_le_exp_of_nonneg (by positivity) K) (Real.exp_nonneg _)
    calc Real.exp (-t) * ∑ i ∈ Finset.range K, t ^ i / i.factorial
        ≤ Real.exp (-t) * (Real.exp (θ * t / 2) * Real.exp (t / 2)) :=
          mul_le_mul_of_nonneg_left hsum_le (Real.exp_nonneg _)
      _ = Real.exp (-((1 - Real.log 2) / 2 * t)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hθ]; ring

end

end TypeDDecoupling.KR