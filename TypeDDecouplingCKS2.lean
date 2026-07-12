import Mathlib
import TypeDDecouplingCKS

/-!
# CKS program, part 2: Grönwall uniqueness, identification, and `lem_free`

Continuation of `TypeDDecouplingCKS.lean` (split out to keep individual files
light).  Contains the integral inequality `gu_int`, the weighted-ℓ¹ Grönwall
uniqueness `gronwall_uniqueness`, the identification `identify`, and the final
`free_bound` (the semigroup form of `lem_free`).
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open NormedSpace
open scoped BigOperators Topology

namespace TypeDDecouplingCKS

/-
Continuity of the ODE right-hand side in time (finite range in space).
-/
lemma gu_Dcont (rate : ℤ → ℤ → ℝ) (ϱ : ℕ)
    (hfr : ∀ x y, rate x y ≠ 0 → (y - x).natAbs ≤ ϱ)
    (r : ℝ → ℤ → ℝ)
    (hrode : ∀ s x, HasDerivAt (fun u => r u x)
      ((∑' z, rate z x * r s z) - (∑' z, rate x z) * r s x) s)
    (x : ℤ) :
    Continuous (fun u => (∑' z, rate z x * r u z) - (∑' z, rate x z) * r u x) := by
  refine' Continuous.sub _ _;
  · -- The sum is finite since `rate z x ≠ 0` implies `z ∈ Finset.Icc (x - ϱ) (x + ϱ)`.
    have h_finite : ∀ u, ∑' z, rate z x * r u z = ∑ z ∈ Finset.Icc (x - ϱ) (x + ϱ), rate z x * r u z := by
      intro u; rw [ tsum_eq_sum ] ; (
      grind);
    simpa only [ h_finite ] using continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const ) ( by exact continuous_iff_continuousAt.mpr fun u => ( hrode u _ |> HasDerivAt.continuousAt ) );
  · exact continuous_const.mul ( continuous_iff_continuousAt.mpr fun u => ( hrode u x |> HasDerivAt.continuousAt ) )

/-- Per-site fundamental theorem of calculus bound. -/
lemma gu_ftc (rate : ℤ → ℤ → ℝ) (ϱ : ℕ)
    (hfr : ∀ x y, rate x y ≠ 0 → (y - x).natAbs ≤ ϱ)
    (r : ℝ → ℤ → ℝ)
    (hr0 : ∀ x, r 0 x = 0)
    (hrode : ∀ s x, HasDerivAt (fun u => r u x)
      ((∑' z, rate z x * r s z) - (∑' z, rate x z) * r s x) s)
    (s : ℝ) (hs : 0 ≤ s) (x : ℤ) :
    |r s x| ≤ ∫ u in (0:ℝ)..s, |(∑' z, rate z x * r u z) - (∑' z, rate x z) * r u x| := by
  have hDc := gu_Dcont rate ϱ hfr r hrode x
  have hFTC : ∫ u in (0:ℝ)..s, ((∑' z, rate z x * r u z) - (∑' z, rate x z) * r u x) = r s x - r 0 x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hrode u x)
      (hDc.intervalIntegrable _ _)]
  have h2 : |r s x| = |∫ u in (0:ℝ)..s, ((∑' z, rate z x * r u z) - (∑' z, rate x z) * r u x)| := by
    rw [hFTC, hr0]; simp
  rw [h2]
  exact intervalIntegral.abs_integral_le_integral_abs hs

/-
Weighted summability of the inflow rates (finite range + geometric weight).
-/
lemma gu_weight_inflow_summable (rate : ℤ → ℤ → ℝ) (Λ : ℝ) (ϱ : ℕ)
    (hnn : ∀ x y, 0 ≤ rate x y)
    (hfr : ∀ x y, rate x y ≠ 0 → (y - x).natAbs ≤ ϱ)
    (hexit : ∀ x, ∑' y, rate x y ≤ Λ) :
    Summable (fun x => gw x * ∑' z, rate z x) := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : Summable (fun p : ℤ × ℤ => gw p.1 * rate p.2 p.1) := by
    have h_summable : Summable (fun p : ℤ × ℤ => gw p.2 * rate p.2 p.1) := by
      have h_summable : Summable (fun p : ℤ × ℤ => gw p.1 * rate p.1 p.2) := by
        have h_summable : ∀ x, Summable (fun z => gw x * rate x z) := by
          intro x
          have h_summable : Summable (fun z => rate x z) := by
            refine' summable_of_ne_finset_zero _;
            exacts [ Finset.Icc ( x - ϱ ) ( x + ϱ ), fun y hy => Classical.not_not.1 fun h => hy <| Finset.mem_Icc.2 ⟨ by cases abs_cases ( y - x ) <;> linarith [ hfr x y h ], by cases abs_cases ( y - x ) <;> linarith [ hfr x y h ] ⟩ ]
          exact Summable.mul_left _ h_summable
        have h_summable : Summable (fun x => ∑' z, gw x * rate x z) := by
          have h_summable : ∀ x, ∑' z, gw x * rate x z ≤ 2 ^ ϱ * gw x * Λ := by
            intro x; rw [ tsum_mul_left ] ; refine' le_trans _ ( mul_le_mul_of_nonneg_left ( hexit x ) ( by exact mul_nonneg ( pow_nonneg zero_le_two _ ) ( by exact ( show 0 ≤ gw x from by exact pow_nonneg ( by norm_num ) _ ) ) ) ) ; ring_nf;
            exact le_mul_of_one_le_right ( mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( tsum_nonneg fun _ => hnn _ _ ) ) ( one_le_pow₀ ( by norm_num ) );
          refine' Summable.of_nonneg_of_le ( fun x => tsum_nonneg fun z => mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( hnn _ _ ) ) ( fun x => h_summable x ) _;
          exact Summable.mul_right _ ( Summable.mul_left _ ( TypeDDecouplingCKS.gw_summable ) );
        rw [ summable_prod_of_nonneg ];
        · aesop;
        · exact fun p => mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( hnn _ _ );
      convert h_summable.comp_injective ( Prod.swap_injective ) using 1;
    have h_swap : ∀ p : ℤ × ℤ, gw p.1 * rate p.2 p.1 ≤ (2 : ℝ) ^ ϱ * gw p.2 * rate p.2 p.1 := by
      intro p
      by_cases h_rate : rate p.2 p.1 = 0;
      · simp [h_rate];
      · have := TypeDDecouplingSemigroup.weight_ratio ( 2⁻¹ : ℝ ) ( by norm_num ) ( by norm_num ) ϱ p.1 p.2 ( hfr _ _ h_rate ) ; simp_all +decide [ gw ];
        exact mul_le_mul_of_nonneg_right this ( hnn _ _ );
    refine' Summable.of_nonneg_of_le ( fun p => mul_nonneg ( gw_pos _ |> le_of_lt ) ( hnn _ _ ) ) ( fun p => h_swap p ) _;
    simpa only [ mul_assoc ] using h_summable.mul_left _;
  convert h_fubini using 1;
  constructor <;> intro h <;> rw [ summable_prod_of_nonneg ] at *;
  any_goals intro p; exact mul_nonneg ( gw_pos _ |> le_of_lt ) ( hnn _ _ );
  · exact h_fubini;
  · simpa only [ tsum_mul_left ] using h.2

/-
The integral inequality feeding Grönwall.
-/
lemma gu_int (rate : ℤ → ℤ → ℝ) (Λ : ℝ) (ϱ : ℕ)
    (hnn : ∀ x y, 0 ≤ rate x y)
    (hfr : ∀ x y, rate x y ≠ 0 → (y - x).natAbs ≤ ϱ)
    (hexit : ∀ x, ∑' y, rate x y ≤ Λ)
    (r : ℝ → ℤ → ℝ) (M : ℝ)
    (hr0 : ∀ x, r 0 x = 0)
    (hrode : ∀ s x, HasDerivAt (fun u => r u x)
      ((∑' z, rate z x * r s z) - (∑' z, rate x z) * r s x) s)
    (hrbd : ∀ s, 0 ≤ s → ∀ x, |r s x| ≤ M) :
    ∀ s, 0 ≤ s → (∑' x, gw x * |r s x|)
      ≤ (2 * Λ * (2:ℝ) ^ ϱ) * ∫ u in (0:ℝ)..s, ∑' x, gw x * |r u x| := by
  intro s hs; by_cases hs' : 0 < s <;> simp_all +decide [ intervalIntegral.integral_of_le ] ;
  · refine' le_trans ( Summable.tsum_le_tsum ( fun x => mul_le_mul_of_nonneg_left ( gu_ftc rate ϱ hfr r hr0 hrode s hs x ) ( by exact ( show 0 ≤ gw x from by exact pow_nonneg ( by norm_num ) _ ) ) ) _ _ ) _;
    · exact gu_summ ( r s ) M ( hrbd s hs );
    · have h_integrable : Summable (fun x => gw x * (∫ u in Set.Ioc 0 s, |(∑' z, rate z x * r u z) - (∑' z, rate x z) * r u x|)) := by
        have h_bound : ∀ x, ∫ u in Set.Ioc 0 s, |(∑' z, rate z x * r u z) - (∑' z, rate x z) * r u x| ≤ s * ((∑' z, rate z x) + Λ) * M := by
          intro x
          have h_bound : ∀ u ∈ Set.Ioc 0 s, |(∑' z, rate z x * r u z) - (∑' z, rate x z) * r u x| ≤ (∑' z, rate z x) * M + Λ * M := by
            intro u hu
            have h_bound : |∑' z, rate z x * r u z| ≤ (∑' z, rate z x) * M := by
              have h_summable : Summable (fun z => rate z x * |r u z|) := by
                have h_summable : Set.Finite {z : ℤ | rate z x ≠ 0} := by
                  exact Set.Finite.subset ( Set.finite_Icc ( x - ϱ : ℤ ) ( x + ϱ : ℤ ) ) fun y hy => ⟨ by cases abs_cases ( x - y ) <;> linarith [ hfr y x hy ], by cases abs_cases ( x - y ) <;> linarith [ hfr y x hy ] ⟩;
                refine' summable_of_ne_finset_zero _;
                exacts [ h_summable.toFinset, fun z hz => mul_eq_zero_of_left ( by simpa using hz ) _ ];
              have h_bound : |∑' z, rate z x * r u z| ≤ ∑' z, rate z x * |r u z| := by
                have h_bound : ∀ {f : ℤ → ℝ}, Summable (fun z => |f z|) → |∑' z, f z| ≤ ∑' z, |f z| := by
                  intro f hf; exact (by
                  convert norm_tsum_le_tsum_norm _ <;> tauto);
                convert h_bound _ using 1;
                · simp +decide [ abs_mul, abs_of_nonneg ( hnn _ _ ) ];
                · simpa [ abs_mul, abs_of_nonneg ( hnn _ _ ) ] using h_summable.abs;
              refine' le_trans h_bound ( le_trans ( Summable.tsum_le_tsum ( fun z => mul_le_mul_of_nonneg_left ( hrbd u hu.1.le z ) ( hnn z x ) ) _ _ ) _ );
              · exact h_summable;
              · have h_summable : Summable (fun z => rate z x) := by
                  refine' summable_of_ne_finset_zero _;
                  exact Finset.Icc ( x - ϱ ) ( x + ϱ );
                  exact fun y hy => Classical.not_not.1 fun h => hy <| Finset.mem_Icc.2 ⟨ by cases abs_cases ( x - y ) <;> linarith [ hfr y x h ], by cases abs_cases ( x - y ) <;> linarith [ hfr y x h ] ⟩;
                exact h_summable.mul_right _;
              · rw [ tsum_mul_right ]
            have h_bound' : |(∑' z, rate x z) * r u x| ≤ Λ * M := by
              rw [ abs_mul, abs_of_nonneg ( show 0 ≤ ∑' z, rate x z from tsum_nonneg fun _ => hnn _ _ ) ] ; exact mul_le_mul ( hexit _ ) ( hrbd _ hu.1.le _ ) ( by exact abs_nonneg _ ) ( by linarith [ show 0 ≤ Λ by exact le_trans ( tsum_nonneg fun _ => hnn _ _ ) ( hexit 0 ) ] ) ;
            have h_bound'' : |∑' z, rate z x * r u z - (∑' z, rate x z) * r u x| ≤ (∑' z, rate z x) * M + Λ * M := by
              exact le_trans ( abs_sub _ _ ) ( add_le_add h_bound h_bound' )
            exact h_bound'';
          convert MeasureTheory.setIntegral_mono_on _ _ _ h_bound <;> norm_num [ hs ];
          · ring;
          · refine' Continuous.integrableOn_Ioc _;
            exact Continuous.abs ( gu_Dcont rate ϱ hfr r hrode x )
        refine' Summable.of_nonneg_of_le ( fun x => mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( MeasureTheory.integral_nonneg fun u => abs_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_left ( h_bound x ) ( pow_nonneg ( by norm_num ) _ ) ) _;
        convert Summable.mul_left ( s * M ) ( gu_weight_inflow_summable rate Λ ϱ hnn hfr hexit |> Summable.add <| Summable.mul_left Λ <| gw_summable ) using 2 ; ring!;
      simpa only [ intervalIntegral.integral_of_le hs ] using h_integrable;
    · have h_summable : Summable (fun x => gw x * ∫ u in Set.Ioc 0 s, |(∑' z, rate z x * r u z) - (∑' z, rate x z) * r u x|) := by
        have h_integrable : ∀ x, ∫ u in Set.Ioc 0 s, |(∑' z, rate z x * r u z) - (∑' z, rate x z) * r u x| ≤ s * ((∑' z, rate z x) + Λ) * M := by
          intro x
          have h_bound : ∀ u ∈ Set.Ioc 0 s, |(∑' z, rate z x * r u z) - (∑' z, rate x z) * r u x| ≤ (∑' z, rate z x) * M + Λ * M := by
            intro u hu
            have h_bound : |∑' z, rate z x * r u z| ≤ (∑' z, rate z x) * M := by
              have h_summable : Summable (fun z => rate z x * |r u z|) := by
                have h_summable : Set.Finite {z : ℤ | rate z x ≠ 0} := by
                  exact Set.Finite.subset ( Set.finite_Icc ( x - ϱ : ℤ ) ( x + ϱ : ℤ ) ) fun y hy => ⟨ by cases abs_cases ( x - y ) <;> linarith [ hfr y x hy ], by cases abs_cases ( x - y ) <;> linarith [ hfr y x hy ] ⟩;
                refine' summable_of_ne_finset_zero _;
                exacts [ h_summable.toFinset, fun z hz => mul_eq_zero_of_left ( by simpa using hz ) _ ];
              have h_bound : |∑' z, rate z x * r u z| ≤ ∑' z, rate z x * |r u z| := by
                have h_bound : ∀ {f : ℤ → ℝ}, Summable (fun z => |f z|) → |∑' z, f z| ≤ ∑' z, |f z| := by
                  intro f hf; exact (by
                  convert norm_tsum_le_tsum_norm _ <;> tauto);
                convert h_bound _ using 1;
                · simp +decide [ abs_mul, abs_of_nonneg ( hnn _ _ ) ];
                · simpa [ abs_mul, abs_of_nonneg ( hnn _ _ ) ] using h_summable.abs;
              refine' le_trans h_bound ( le_trans ( Summable.tsum_le_tsum ( fun z => mul_le_mul_of_nonneg_left ( hrbd u hu.1.le z ) ( hnn z x ) ) _ _ ) _ );
              · exact h_summable;
              · have h_summable : Summable (fun z => rate z x) := by
                  refine' summable_of_ne_finset_zero _;
                  exact Finset.Icc ( x - ϱ ) ( x + ϱ );
                  exact fun y hy => Classical.not_not.1 fun h => hy <| Finset.mem_Icc.2 ⟨ by cases abs_cases ( x - y ) <;> linarith [ hfr y x h ], by cases abs_cases ( x - y ) <;> linarith [ hfr y x h ] ⟩;
                exact h_summable.mul_right _;
              · rw [ tsum_mul_right ]
            have h_bound' : |(∑' z, rate x z) * r u x| ≤ Λ * M := by
              rw [ abs_mul, abs_of_nonneg ( show 0 ≤ ∑' z, rate x z from tsum_nonneg fun _ => hnn _ _ ) ] ; exact mul_le_mul ( hexit _ ) ( hrbd _ hu.1.le _ ) ( by exact abs_nonneg _ ) ( by linarith [ show 0 ≤ Λ by exact le_trans ( tsum_nonneg fun _ => hnn _ _ ) ( hexit 0 ) ] ) ;
            have h_bound'' : |∑' z, rate z x * r u z - (∑' z, rate x z) * r u x| ≤ (∑' z, rate z x) * M + Λ * M := by
              exact le_trans ( abs_sub _ _ ) ( add_le_add h_bound h_bound' )
            exact h_bound'';
          convert MeasureTheory.setIntegral_mono_on _ _ _ h_bound <;> norm_num [ hs ];
          · ring;
          · refine' Continuous.integrableOn_Ioc _;
            exact Continuous.abs ( gu_Dcont rate ϱ hfr r hrode x );
        refine' Summable.of_nonneg_of_le ( fun x => mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( MeasureTheory.integral_nonneg fun _ => abs_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_left ( h_integrable x ) ( pow_nonneg ( by norm_num ) _ ) ) _;
        convert Summable.mul_left ( s * M ) ( gu_weight_inflow_summable rate Λ ϱ hnn hfr hexit |> Summable.add <| Summable.mul_left Λ <| gw_summable ) using 2 ; ring!;
      have h_integral_tsum : ∑' x, gw x * ∫ u in Set.Ioc 0 s, |(∑' z, rate z x * r u z) - (∑' z, rate x z) * r u x| = ∫ u in Set.Ioc 0 s, ∑' x, gw x * |(∑' z, rate z x * r u z) - (∑' z, rate x z) * r u x| := by
        rw [ MeasureTheory.integral_tsum ];
        · simp +decide only [MeasureTheory.integral_const_mul];
        · intro x; exact Continuous.aestronglyMeasurable ( by exact Continuous.mul continuous_const <| Continuous.abs <| by exact gu_Dcont rate ϱ hfr r hrode x ) ;
        · refine' ne_of_lt ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum _ ) _ );
          use fun x => ENNReal.ofReal ( gw x * ∫ u in Set.Ioc 0 s, |∑' z, rate z x * r u z - (∑' z, rate x z) * r u x| );
          · intro x; rw [ ← MeasureTheory.integral_const_mul ] ; rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ] ;
            · refine' MeasureTheory.lintegral_mono fun u => _;
              rw [ Real.enorm_eq_ofReal ( mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( abs_nonneg _ ) ) ];
            · refine' Continuous.integrableOn_Ioc _;
              refine' Continuous.mul continuous_const _;
              exact Continuous.abs ( gu_Dcont rate ϱ hfr r hrode x );
            · exact Filter.Eventually.of_forall fun _ => mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( abs_nonneg _ );
          · rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num [ h_summable ];
            exact fun x => mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( MeasureTheory.integral_nonneg fun _ => abs_nonneg _ );
      convert h_integral_tsum.le.trans _ using 1;
      · simp +decide only [intervalIntegral.integral_of_le hs];
      · rw [ ← MeasureTheory.integral_const_mul ];
        refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
        · exact Filter.Eventually.of_forall fun u => tsum_nonneg fun x => mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( abs_nonneg _ );
        · refine' ContinuousOn.integrableOn_Icc _ |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
          refine' ContinuousOn.mul continuousOn_const _;
          convert gu_cont r M ( fun x => continuous_iff_continuousAt.mpr fun s => HasDerivAt.continuousAt ( hrode s x ) ) ( fun s hs x => hrbd s hs x ) |> ContinuousOn.mono <| Set.Icc_subset_Ici_self using 1;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu;
          convert gu_spatial rate Λ ϱ hnn hfr hexit ( r u ) ( gu_summ ( r u ) M ( hrbd u hu.1.le ) ) using 1;
  · norm_num [ show s = 0 by linarith, hr0 ]

/-- **Weighted ℓ¹ Grönwall uniqueness.**  A bounded solution `r` of the linear
forward ODE with zero initial data vanishes for `t ≥ 0`. -/
lemma gronwall_uniqueness
    (rate : ℤ → ℤ → ℝ) (Λ : ℝ) (ϱ : ℕ)
    (hnn : ∀ x y, 0 ≤ rate x y)
    (hfr : ∀ x y, rate x y ≠ 0 → (y - x).natAbs ≤ ϱ)
    (hexit : ∀ x, ∑' y, rate x y ≤ Λ)
    (hΛ : 0 ≤ Λ)
    (r : ℝ → ℤ → ℝ) (M : ℝ)
    (hr0 : ∀ x, r 0 x = 0)
    (hrode : ∀ s x, HasDerivAt (fun u => r u x)
      ((∑' z, rate z x * r s z) - (∑' z, rate x z) * r s x) s)
    (hrbd : ∀ s, 0 ≤ s → ∀ x, |r s x| ≤ M) :
    ∀ s, 0 ≤ s → ∀ x, r s x = 0 := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hrbd 0 le_rfl 0)
  have hrc : ∀ x, Continuous (fun s => r s x) := fun x =>
    continuous_iff_continuousAt.2 (fun s => (hrode s x).continuousAt)
  set ρ : ℝ → ℝ := fun s => ∑' x, gw x * |r s x| with hρ
  have hnnρ : ∀ s, 0 ≤ s → 0 ≤ ρ s := fun s _ => tsum_nonneg (fun x => mul_nonneg (gw_pos x).le (abs_nonneg _))
  have hbdρ : ∀ s, 0 ≤ s → ρ s ≤ M * ∑' x, gw x := by
    intro s hs
    have hsm := gu_summ (r s) M (hrbd s hs)
    calc ρ s ≤ ∑' x, gw x * M :=
          Summable.tsum_le_tsum (fun x => mul_le_mul_of_nonneg_left (hrbd s hs x) (gw_pos x).le)
            hsm (gw_summable.mul_right M)
      _ = M * ∑' x, gw x := by rw [tsum_mul_right, mul_comm]
  have hcont := gu_cont r M hrc hrbd
  have hint := gu_int rate Λ ϱ hnn hfr hexit r M hr0 hrode hrbd
  have hgwnn : 0 ≤ ∑' x, gw x := tsum_nonneg (fun x => (gw_pos x).le)
  have hzero := gronwall_zero ρ (2 * Λ * (2:ℝ) ^ ϱ) (M * ∑' x, gw x)
    (mul_nonneg (mul_nonneg (by norm_num) hΛ) (by positivity)) (mul_nonneg hM hgwnn)
    hcont hnnρ hbdρ hint
  intro s hs x
  have hsum0 : ρ s = 0 := hzero s hs
  have hterm : gw x * |r s x| ≤ ρ s :=
    Summable.le_tsum (gu_summ (r s) M (hrbd s hs)) x
      (fun j _ => mul_nonneg (gw_pos j).le (abs_nonneg _))
  have : gw x * |r s x| ≤ 0 := by rw [← hsum0]; exact hterm
  have habs : |r s x| = 0 := by
    by_contra hne
    have : 0 < gw x * |r s x| := mul_pos (gw_pos x) (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne))
    linarith
  exact abs_eq_zero.1 habs

/-- **Identification of the abstract kernel with the semigroup kernel.**
Any nonnegative bounded solution of the forward ODE with data `δ_0` coincides
with `q^0` on `t ≥ 0` (weighted Grönwall uniqueness). -/
lemma identify
    (A : L1 →L[ℝ] L1) (rate : ℤ → ℤ → ℝ) (m : ℤ → ℝ)
    (c₁ c₂ δ Λ : ℝ) (ϱ : ℕ)
    (hA : ∀ (f : L1) (y : ℤ), (A f : ∀ _ : ℤ, ℝ) y
      = (∑' x, rate x y * (f : ∀ _ : ℤ, ℝ) x) - (∑' z, rate y z) * (f : ∀ _ : ℤ, ℝ) y)
    (hnn : ∀ x y, 0 ≤ rate x y)
    (hfr : ∀ x y, rate x y ≠ 0 → (y - x).natAbs ≤ ϱ)
    (hexit : ∀ x, ∑' y, rate x y ≤ Λ)
    (hrev : ∀ x y, m x * rate x y = m y * rate y x)
    (hc1 : 0 < c₁) (hmlb : ∀ x, c₁ ≤ m x) (hmub : ∀ x, m x ≤ c₂)
    (hδ : 0 < δ) (hcond : ∀ x, δ ≤ m x * rate x (x + 1))
    (hΛ : 0 ≤ Λ)
    (p : ℝ → ℤ → ℝ)
    (hp0 : ∀ r, p 0 r = if r = 0 then 1 else 0)
    (hpnn : ∀ t, 0 ≤ t → ∀ r, 0 ≤ p t r)
    (hpode : ∀ t r, HasDerivAt (fun s => p s r)
      ((∑' y, rate y r * p t y) - (∑' y, rate r y) * p t r) t)
    (hp_le1 : ∀ t, 0 ≤ t → ∀ x, p t x ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) (x : ℤ) :
    p t x = qq A 0 t x := by
  set r : ℝ → ℤ → ℝ := fun s x => p s x - qq A 0 s x with hr
  -- summability of the (finite-range) inflow sums against any function
  have hsum : ∀ (g : ℤ → ℝ) (x : ℤ), Summable (fun z => rate z x * g z) := by
    intro g x
    apply summable_of_ne_finset_zero (s := Finset.Icc (x - ϱ) (x + ϱ))
    intro z hz
    have hz0 : rate z x = 0 := by
      by_contra h
      exact hz (Finset.mem_Icc.2 (by have := hfr z x h; omega))
    rw [hz0, zero_mul]
  have hr0 : ∀ x, r 0 x = 0 := by
    intro x
    simp only [hr, hp0 x,
      qq_zero A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond 0 x, sub_self]
  have hrode : ∀ s x, HasDerivAt (fun u => r u x)
      ((∑' z, rate z x * r s z) - (∑' z, rate x z) * r s x) s := by
    intro s x
    have e1 : ∑' z, rate z x * r s z
        = (∑' z, rate z x * p s z) - ∑' z, rate z x * qq A 0 s z := by
      rw [← Summable.tsum_sub (hsum (fun z => p s z) x) (hsum (fun z => qq A 0 s z) x)]
      exact tsum_congr (fun z => by simp only [hr]; ring)
    have hq := qq_hasDerivAt A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond 0 x s
    have hstep := (hpode s x).sub hq
    convert hstep using 1
    rw [e1]; simp only [hr]; ring
  have hrbd : ∀ s, 0 ≤ s → ∀ x, |r s x| ≤ 2 := by
    intro s hs x
    have h1 := hpnn s hs x
    have h2 := hp_le1 s hs x
    have h3 := qq_nonneg A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond 0 x s hs
    have h4 := qq_le_one A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond 0 x s hs
    rw [hr, abs_le]; constructor <;> simp only [] <;> linarith
  have hzero := gronwall_uniqueness rate Λ ϱ hnn hfr hexit hΛ r 2 hr0 hrode hrbd t ht x
  have hfin : p t x - qq A 0 t x = 0 := hzero
  linarith

/-- **`lem_free`, semigroup form.**  The on-diagonal local-CLT bound for any
finite-range, driftless, reversible walk kernel `p` with the a-priori bound
`p ≤ 1`. -/
theorem free_bound
    (rate : ℤ → ℤ → ℝ) (p : ℝ → ℤ → ℝ) (m : ℤ → ℝ)
    (c₁ c₂ δ Λ : ℝ) (ϱ : ℕ)
    (hp0 : ∀ r, p 0 r = if r = 0 then 1 else 0)
    (hpnn : ∀ t, 0 ≤ t → ∀ r, 0 ≤ p t r)
    (hpode : ∀ t r, HasDerivAt (fun s => p s r)
      ((∑' y, rate y r * p t y) - (∑' y, rate r y) * p t r) t)
    (hnn : ∀ x y, 0 ≤ rate x y)
    (hfr : ∀ x y, rate x y ≠ 0 → (y - x).natAbs ≤ ϱ)
    (hexit : ∀ x, ∑' y, rate x y ≤ Λ)
    (hrev : ∀ x y, m x * rate x y = m y * rate y x)
    (hc1 : 0 < c₁) (hmlb : ∀ x, c₁ ≤ m x) (hmub : ∀ x, m x ≤ c₂)
    (hδ : 0 < δ) (hcond : ∀ x, δ ≤ m x * rate x (x + 1))
    (hp_le1 : ∀ t, 0 ≤ t → ∀ x, p t x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ r : ℤ, p t r ≤ C / Real.sqrt (1 + t) := by
  obtain ⟨A, hA, _hAnorm⟩ :=
    TypeDDecouplingSemigroup.exists_forward_generator rate ϱ Λ hnn hfr hexit
  have hΛ : 0 ≤ Λ := le_trans (tsum_nonneg (fun y => hnn 0 y)) (hexit 0)
  have hc2 : 0 < c₂ := lt_of_lt_of_le hc1 (le_trans (hmlb 0) (hmub 0))
  have hκ : 0 < kap δ c₁ c₂ := by unfold kap; positivity
  set K : ℝ := c₂ / Real.sqrt (2 * kap δ c₁ c₂) with hKdef
  have hsqrt2κ : 0 < Real.sqrt (2 * kap δ c₁ c₂) := Real.sqrt_pos.mpr (by positivity)
  have hKpos : 0 < K := by rw [hKdef]; positivity
  refine TypeDDecouplingNash.nash_pointwise_bound p
    (fun s => K * (Real.sqrt s)⁻¹) (fun s => -(K / 2) * (Real.sqrt s)⁻¹ ^ 3)
    (1 / (2 * K ^ 2)) 1 (by positivity) (by norm_num) hp_le1 ?_ ?_ ?_ ?_
  · intro s hs; positivity
  · intro s hs
    have h1 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt (ne_of_gt hs)
    have h2 : HasDerivAt (fun s => (Real.sqrt s)⁻¹)
        (-(1 / (2 * Real.sqrt s)) / (Real.sqrt s) ^ 2) s := h1.inv (by positivity)
    have h3 := h2.const_mul K
    have hs' : Real.sqrt s > 0 := Real.sqrt_pos.mpr hs
    have heq : -(K / 2) * (Real.sqrt s)⁻¹ ^ 3
        = K * (-(1 / (2 * Real.sqrt s)) / (Real.sqrt s) ^ 2) := by field_simp
    show HasDerivAt (fun s => K * (Real.sqrt s)⁻¹) (-(K / 2) * (Real.sqrt s)⁻¹ ^ 3) s
    rw [heq]; exact h3
  · intro s hs
    have hs' : Real.sqrt s > 0 := Real.sqrt_pos.mpr hs
    have : (K * (Real.sqrt s)⁻¹) ^ 3 = K ^ 3 * (Real.sqrt s)⁻¹ ^ 3 := by ring
    rw [this]
    rw [show -(1 / (2 * K ^ 2)) * (K ^ 3 * (Real.sqrt s)⁻¹ ^ 3)
        = -(K / 2) * (Real.sqrt s)⁻¹ ^ 3 by field_simp]
  · intro s hs r
    rw [one_mul]
    have hid := identify A rate m c₁ c₂ δ Λ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond hΛ
      p hp0 hpnn hpode hp_le1 (2 * s) (by linarith) r
    have hs' : Real.sqrt s > 0 := Real.sqrt_pos.mpr hs
    have heq : c₂ / Real.sqrt (2 * kap δ c₁ c₂ * s) = K * (Real.sqrt s)⁻¹ := by
      rw [hKdef, Real.sqrt_mul (by positivity) s]; field_simp
    show p (2 * s) r ≤ K * (Real.sqrt s)⁻¹
    rw [hid, ← heq]
    exact offdiag A rate m Λ δ c₁ c₂ ϱ hA hnn hfr hexit hrev hc1 hmlb hmub hδ hcond r s hs


end TypeDDecouplingCKS