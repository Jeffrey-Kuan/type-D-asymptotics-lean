import Mathlib

set_option maxHeartbeats 4000000

open scoped BigOperators
open NormedSpace

namespace TypeDDecouplingSemigroup

/-- The `ℓ¹` space of signed measures on `ℤ`. -/
abbrev L1 := lp (fun _ : ℤ => ℝ) 1

/-
Existence of the bounded forward generator of a finite-range, bounded, nonnegative
rate matrix on `ℤ`, as a continuous linear operator on `ℓ¹(ℤ)`.  Its action on a density
`μ` is `(Aμ)(y) = (∑ₓ rate(x,y) μ(x)) − (∑_z rate(y,z)) μ(y)` (inflow minus outflow).
-/
theorem exists_forward_generator
    (rate : ℤ → ℤ → ℝ) (ϱ : ℕ) (Λ : ℝ)
    (hnn : ∀ x y, 0 ≤ rate x y)
    (hfr : ∀ x y, rate x y ≠ 0 → (y - x).natAbs ≤ ϱ)
    (hexit : ∀ x, ∑' y, rate x y ≤ Λ) :
    ∃ A : L1 →L[ℝ] L1,
      (∀ (f : L1) (y : ℤ),
        (A f : ℤ → ℝ) y
          = (∑' x : ℤ, rate x y * (f : ℤ → ℝ) x)
              - (∑' z : ℤ, rate y z) * (f : ℤ → ℝ) y)
      ∧ ‖A‖ ≤ 2 * Λ := by
  -- Define the operator $A$.
  obtain ⟨A, hA⟩ : ∃ A : L1 →ₗ[ℝ] L1, (∀ f : L1, ∀ y : ℤ, (A f) y = ∑' x, rate x y * f x - (∑' z, rate y z) * f y) := by
    have hA_def : ∀ f : L1, (∀ y : ℤ, Summable (fun x => rate x y * f x)) ∧ (Summable (fun y => |(∑' x, rate x y * f x - (∑' z, rate y z) * f y)|)) := by
      intro f
      have h_summable : Summable (fun y => |∑' x, rate x y * f x|) ∧ Summable (fun y => |(∑' z, rate y z) * f y|) := by
        constructor;
        · -- By Fubini's theorem, we can interchange the order of summation.
          have h_fubini : Summable (fun p : ℤ × ℤ => rate p.1 p.2 * |f p.1|) := by
            have h_summable : Summable (fun x => |f x| * ∑' y, rate x y) := by
              refine' .of_nonneg_of_le ( fun x => mul_nonneg ( abs_nonneg _ ) ( tsum_nonneg fun _ => hnn _ _ ) ) ( fun x => mul_le_mul_of_nonneg_left ( hexit x ) ( abs_nonneg _ ) ) _;
              exact Summable.mul_right _ ( by simpa using f.2.summable );
            rw [ summable_prod_of_nonneg ];
            · simp_all +decide [ mul_comm, tsum_mul_left, tsum_mul_right ];
              intro x;
              refine' summable_of_ne_finset_zero _;
              exacts [ Finset.Icc ( x - ϱ ) ( x + ϱ ), fun y hy => mul_eq_zero_of_left ( Classical.not_not.1 fun h => hy <| Finset.mem_Icc.2 ⟨ by cases abs_cases ( y - x ) <;> linarith [ hfr x y h ], by cases abs_cases ( y - x ) <;> linarith [ hfr x y h ] ⟩ ) _ ];
            · exact fun _ => mul_nonneg ( hnn _ _ ) ( abs_nonneg _ );
          have h_fubini : Summable (fun y => ∑' x, rate x y * |f x|) := by
            refine' summable_of_sum_le _ _;
            exact ∑' p : ℤ × ℤ, rate p.1 p.2 * |f p.1|;
            · exact fun y => tsum_nonneg fun x => mul_nonneg ( hnn x y ) ( abs_nonneg _ );
            · intro u
              have h_fubini : ∑ x ∈ u, ∑' x_1, rate x_1 x * |f x_1| = ∑' p : ℤ × ℤ, rate p.1 p.2 * |f p.1| * (if p.2 ∈ u then 1 else 0) := by
                erw [ Summable.tsum_prod ];
                · rw [ Summable.tsum_comm ];
                  · rw [ tsum_eq_sum ];
                    congr! 1; all_goals aesop;
                  · refine' Summable.of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) ( h_fubini.comp_injective ( Prod.swap_injective ) );
                    · exact mul_nonneg ( mul_nonneg ( hnn _ _ ) ( abs_nonneg _ ) ) ( by positivity );
                    · exact mul_le_of_le_one_right ( mul_nonneg ( hnn _ _ ) ( abs_nonneg _ ) ) ( by aesop );
                · exact Summable.of_nonneg_of_le ( fun p => mul_nonneg ( mul_nonneg ( hnn _ _ ) ( abs_nonneg _ ) ) ( by positivity ) ) ( fun p => mul_le_of_le_one_right ( mul_nonneg ( hnn _ _ ) ( abs_nonneg _ ) ) ( by aesop ) ) h_fubini;
              rw [h_fubini];
              refine' Summable.tsum_le_tsum _ _ _;
              · exact fun p => mul_le_of_le_one_right ( mul_nonneg ( hnn _ _ ) ( abs_nonneg _ ) ) ( by split_ifs <;> norm_num );
              · exact Summable.of_nonneg_of_le ( fun p => mul_nonneg ( mul_nonneg ( hnn _ _ ) ( abs_nonneg _ ) ) ( by split_ifs <;> norm_num ) ) ( fun p => mul_le_of_le_one_right ( mul_nonneg ( hnn _ _ ) ( abs_nonneg _ ) ) ( by split_ifs <;> norm_num ) ) ‹_›;
              · assumption;
          refine' .of_nonneg_of_le ( fun y => abs_nonneg _ ) ( fun y => _ ) h_fubini;
          by_cases h : Summable ( fun x => rate x y * f x ) <;> simp_all +decide [ tsum_eq_zero_of_not_summable ];
          · convert norm_tsum_le_tsum_norm _ <;> norm_num [ abs_mul, hnn ];
            any_goals tauto;
            · norm_num [ abs_mul, abs_of_nonneg ( hnn _ _ ) ];
            · exact h.norm;
          · exact tsum_nonneg fun x => mul_nonneg ( hnn x y ) ( abs_nonneg _ );
        · have h_summable : Summable (fun y => (∑' z, rate y z) * |f y|) := by
            refine' .of_nonneg_of_le ( fun y => mul_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ( abs_nonneg _ ) ) ( fun y => mul_le_mul_of_nonneg_right ( hexit y ) ( abs_nonneg _ ) ) _;
            exact Summable.mul_left _ <| by simpa using f.2.summable;
          simpa [ abs_mul ] using h_summable.abs;
      refine' ⟨ _, Summable.of_nonneg_of_le ( fun y => abs_nonneg _ ) ( fun y => abs_sub _ _ ) ( h_summable.1.add h_summable.2 ) ⟩;
      intro y
      have h_finite_support : Set.Finite {x : ℤ | rate x y ≠ 0} := by
        exact Set.Finite.subset ( Set.finite_Icc ( y - ϱ : ℤ ) ( y + ϱ : ℤ ) ) fun x hx => ⟨ by cases abs_cases ( y - x ) <;> linarith [ hfr x y hx ], by cases abs_cases ( y - x ) <;> linarith [ hfr x y hx ] ⟩;
      refine' summable_of_ne_finset_zero _;
      exacts [ h_finite_support.toFinset, fun x hx => mul_eq_zero_of_left ( Classical.not_not.1 fun hx' => hx <| h_finite_support.mem_toFinset.2 hx' ) _ ];
    have hA_def : ∀ f : L1, ∃ g : L1, ∀ y : ℤ, g y = ∑' x, rate x y * f x - (∑' z, rate y z) * f y := by
      intro f
      obtain ⟨g, hg⟩ : ∃ g : ℤ → ℝ, (∀ y : ℤ, g y = ∑' x, rate x y * f x - (∑' z, rate y z) * f y) ∧ Summable (fun y => |g y|) := by
        exact ⟨ _, fun y => rfl, hA_def f |>.2 ⟩;
      refine' ⟨ ⟨ g, _ ⟩, hg.1 ⟩;
      simp_all +decide [ L1, lp ];
      simp_all +decide [ Memℓp ];
      simpa only [ ← hg.1 ] using hg.2;
    choose g hg using hA_def;
    have hA_linear : ∀ f₁ f₂ : L1, g (f₁ + f₂) = g f₁ + g f₂ := by
      intro f₁ f₂; ext y; simp +decide [ hg, mul_add, add_mul, Summable.tsum_add ] ; ring;
      rw [ Summable.tsum_add ( hA_def f₁ |>.1 y ) ( hA_def f₂ |>.1 y ) ] ; ring;
    have hA_smul : ∀ (c : ℝ) (f : L1), g (c • f) = c • g f := by
      intro c f; ext y; simp +decide [ hg, mul_assoc, mul_left_comm, tsum_mul_left ] ;
      ring;
    exact ⟨ { toFun := g, map_add' := hA_linear, map_smul' := hA_smul }, hg ⟩;
  -- Show that $A$ is bounded.
  have h_bounded : ∀ f : L1, ‖A f‖ ≤ 2 * Λ * ‖f‖ := by
    intro f
    have h_norm : ∑' y, ‖(A f) y‖ ≤ 2 * Λ * ∑' x, ‖f x‖ := by
      -- Apply the triangle inequality to the sum.
      have h_triangle : ∑' y, ‖(A f) y‖ ≤ ∑' y, (∑' x, rate x y * ‖f x‖) + ∑' y, (∑' z, rate y z) * ‖f y‖ := by
        rw [ ← Summable.tsum_add ];
        · refine' Summable.tsum_le_tsum _ _ _;
          · intro y; rw [ hA ] ; refine' le_trans ( abs_sub _ _ ) _ ; norm_num [ abs_of_nonneg, hnn ] ;
            gcongr;
            · by_cases h : Summable ( fun x => rate x y * f x ) <;> simp_all +decide [ tsum_eq_zero_of_not_summable ];
              · convert norm_tsum_le_tsum_norm _ <;> norm_num [ abs_mul, hnn ];
                any_goals tauto;
                · norm_num [ abs_mul, abs_of_nonneg ( hnn _ _ ) ];
                · exact h.norm;
              · exact tsum_nonneg fun _ => mul_nonneg ( hnn _ _ ) ( abs_nonneg _ );
            · rw [ abs_of_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ];
          · have := f.2;
            convert this.summable using 1;
            exact iff_of_true ( by simpa using ( A f ) |>.2.summable ) ( by simpa using f.2.summable );
          · refine' Summable.add _ _;
            · -- By Fubini's theorem, we can interchange the order of summation.
              have h_fubini : Summable (fun p : ℤ × ℤ => rate p.1 p.2 * ‖f p.1‖) := by
                have h_summable : Summable (fun x => ∑' y, rate x y * ‖f x‖) := by
                  simp_all +decide [ tsum_mul_right ];
                  refine' .of_nonneg_of_le ( fun x => mul_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ( abs_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_right ( hexit x ) ( abs_nonneg _ ) ) _;
                  exact Summable.mul_left _ <| by simpa using f.2.summable;
                rw [ summable_prod_of_nonneg ];
                · refine' ⟨ _, h_summable ⟩;
                  intro x;
                  refine' summable_of_ne_finset_zero _;
                  exact Finset.Icc ( x - ϱ ) ( x + ϱ );
                  grind;
                · exact fun _ => mul_nonneg ( hnn _ _ ) ( norm_nonneg _ );
              refine' summable_of_sum_le _ _;
              exact ∑' p : ℤ × ℤ, rate p.1 p.2 * ‖f p.1‖;
              · exact fun _ => tsum_nonneg fun _ => mul_nonneg ( hnn _ _ ) ( norm_nonneg _ );
              · intro u;
                have h_fubini : ∑ x ∈ u, ∑' (x_1 : ℤ), rate x_1 x * ‖f x_1‖ = ∑' (p : ℤ × ℤ), rate p.1 p.2 * ‖f p.1‖ * (if p.2 ∈ u then 1 else 0) := by
                  erw [ Summable.tsum_prod ];
                  · rw [ Summable.tsum_comm ];
                    · rw [ tsum_eq_sum ];
                      congr! 1; all_goals aesop;
                    · refine' Summable.of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) ( h_fubini.comp_injective ( Prod.swap_injective ) );
                      · exact mul_nonneg ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by positivity );
                      · exact mul_le_of_le_one_right ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by aesop );
                  · exact Summable.of_nonneg_of_le ( fun p => mul_nonneg ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by positivity ) ) ( fun p => mul_le_of_le_one_right ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by aesop ) ) h_fubini;
                rw [h_fubini];
                refine' Summable.tsum_le_tsum _ _ _;
                · exact fun p => mul_le_of_le_one_right ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by split_ifs <;> norm_num );
                · exact Summable.of_nonneg_of_le ( fun p => mul_nonneg ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by split_ifs <;> norm_num ) ) ( fun p => mul_le_of_le_one_right ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by split_ifs <;> norm_num ) ) ‹_›;
                · assumption;
            · refine' Summable.of_nonneg_of_le ( fun x => mul_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ( norm_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_right ( hexit x ) ( norm_nonneg _ ) ) _;
              exact Summable.mul_left _ <| by simpa using f.2.summable;
        · -- By Fubini's theorem, we can interchange the order of summation.
          have h_fubini : Summable (fun p : ℤ × ℤ => rate p.1 p.2 * ‖f p.1‖) := by
            have h_summable : Summable (fun x => ∑' y, rate x y * ‖f x‖) := by
              simp_all +decide [ tsum_mul_right ];
              refine' .of_nonneg_of_le ( fun x => mul_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ( abs_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_right ( hexit x ) ( abs_nonneg _ ) ) _;
              exact Summable.mul_left _ <| by simpa using f.2.summable;
            rw [ summable_prod_of_nonneg ];
            · refine' ⟨ _, h_summable ⟩;
              intro x;
              refine' summable_of_ne_finset_zero _;
              exact Finset.Icc ( x - ϱ ) ( x + ϱ );
              grind;
            · exact fun _ => mul_nonneg ( hnn _ _ ) ( norm_nonneg _ );
          refine' summable_of_sum_le _ _;
          exact ∑' p : ℤ × ℤ, rate p.1 p.2 * ‖f p.1‖;
          · exact fun y => tsum_nonneg fun x => mul_nonneg ( hnn x y ) ( norm_nonneg _ );
          · intro u;
            have h_fubini : ∑ x ∈ u, ∑' (x_1 : ℤ), rate x_1 x * ‖f x_1‖ = ∑' (p : ℤ × ℤ), rate p.1 p.2 * ‖f p.1‖ * (if p.2 ∈ u then 1 else 0) := by
              erw [ Summable.tsum_prod ];
              · rw [ Summable.tsum_comm ];
                · rw [ tsum_eq_sum ];
                  congr! 1; all_goals aesop;
                · refine' Summable.of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) ( h_fubini.comp_injective ( Prod.swap_injective ) );
                  · exact mul_nonneg ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by positivity );
                  · exact mul_le_of_le_one_right ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by aesop );
              · exact Summable.of_nonneg_of_le ( fun p => mul_nonneg ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by positivity ) ) ( fun p => mul_le_of_le_one_right ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by aesop ) ) h_fubini;
            rw [h_fubini];
            refine' Summable.tsum_le_tsum _ _ _;
            · exact fun p => mul_le_of_le_one_right ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by split_ifs <;> norm_num );
            · exact Summable.of_nonneg_of_le ( fun p => mul_nonneg ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by split_ifs <;> norm_num ) ) ( fun p => mul_le_of_le_one_right ( mul_nonneg ( hnn _ _ ) ( norm_nonneg _ ) ) ( by split_ifs <;> norm_num ) ) ‹_›;
            · assumption;
        · have h_summable : Summable (fun y => Λ * ‖f y‖) := by
            exact Summable.mul_left _ <| by simpa using f.2.summable;
          exact Summable.of_nonneg_of_le ( fun y => mul_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ( norm_nonneg _ ) ) ( fun y => mul_le_mul_of_nonneg_right ( hexit y ) ( norm_nonneg _ ) ) h_summable;
      -- Interchange the order of summation in the first term.
      have h_interchange : ∑' y, ∑' x, rate x y * ‖f x‖ = ∑' x, ∑' y, rate x y * ‖f x‖ := by
        rw [ Summable.tsum_comm ];
        have h_summable : Summable (fun x => ∑' y, rate x y * ‖f x‖) := by
          have h_summable : Summable (fun x => (∑' y, rate x y) * ‖f x‖) := by
            refine' .of_nonneg_of_le ( fun x => mul_nonneg ( tsum_nonneg fun y => hnn x y ) ( norm_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_right ( hexit x ) ( norm_nonneg _ ) ) _;
            exact Summable.mul_left _ <| by simpa using f.2.summable;
          simpa only [ tsum_mul_right ] using h_summable;
        rw [ summable_prod_of_nonneg ];
        · refine' ⟨ _, h_summable ⟩;
          intro x;
          refine' summable_of_ne_finset_zero _;
          exact Finset.Icc ( x - ϱ ) ( x + ϱ );
          grind;
        · exact fun x => mul_nonneg ( hnn _ _ ) ( norm_nonneg _ );
      -- Apply the bounds on the sums of rates.
      have h_bounds : ∑' x, ∑' y, rate x y * ‖f x‖ ≤ Λ * ∑' x, ‖f x‖ ∧ ∑' y, (∑' z, rate y z) * ‖f y‖ ≤ Λ * ∑' y, ‖f y‖ := by
        constructor <;> rw [ ← tsum_mul_left ];
        · refine' Summable.tsum_le_tsum _ _ _;
          · exact fun x => by rw [ tsum_mul_right ] ; exact mul_le_mul_of_nonneg_right ( hexit x ) ( norm_nonneg _ ) ;
          · simp_all +decide [ tsum_mul_right ];
            refine' Summable.of_nonneg_of_le ( fun x => mul_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ( abs_nonneg _ ) ) ( fun x => mul_le_mul_of_nonneg_right ( hexit x ) ( abs_nonneg _ ) ) _;
            exact Summable.mul_left _ <| by simpa using f.2.summable;
          · exact Summable.mul_left _ <| by simpa using f.2.summable;
        · refine' Summable.tsum_le_tsum _ _ _;
          · exact fun x => mul_le_mul_of_nonneg_right ( hexit x ) ( norm_nonneg _ );
          · refine' Summable.of_nonneg_of_le ( fun y => mul_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ( norm_nonneg _ ) ) ( fun y => mul_le_mul_of_nonneg_right ( hexit y ) ( norm_nonneg _ ) ) _;
            exact Summable.mul_left _ <| by simpa using f.2.summable;
          · exact Summable.mul_left _ <| by simpa using f.2.summable;
      linarith;
    simp_all +decide [ lp.norm_eq_tsum_rpow ];
  refine' ⟨ A.mkContinuous _ h_bounded, hA, _ ⟩;
  convert ContinuousLinearMap.opNorm_le_bound _ _ _ <;> norm_num [ h_bounded ];
  exact le_trans ( tsum_nonneg fun _ => hnn 0 _ ) ( hexit 0 )


/-! ## Finite-box mass control for the forward equation (a-priori estimate groundwork) -/

/-
Geometric-weight ratio bound: within finite range the weight changes by at most
`(θ⁻¹)^ϱ`.
-/
theorem weight_ratio (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ϱ : ℕ) :
    ∀ x y : ℤ, (x - y).natAbs ≤ ϱ →
      θ ^ x.natAbs ≤ (θ⁻¹) ^ ϱ * θ ^ y.natAbs := by
  intro x y hxy
  have h_mul : θ ^ (x.natAbs + ϱ) ≤ θ ^ y.natAbs := by
    exact pow_le_pow_of_le_one hθ0.le hθ1 ( by omega );
  convert mul_le_mul_of_nonneg_left h_mul ( pow_nonneg ( inv_nonneg.mpr hθ0.le ) ϱ ) using 1 ; ring_nf ; norm_num [ hθ0.ne' ]

/-
Finite-box integral inequality for the weighted mass of a nonnegative solution of the
forward equation.  With `c := Λ·(θ⁻¹)^ϱ`, the mass in the box `Icc (−N) N` is controlled by
its initial value plus `c` times the time-integral of the mass in the slightly larger box
`Icc (−(N+ϱ)) (N+ϱ)`.
-/
theorem VN_int_ineq
    (rate : ℤ → ℤ → ℝ) (ϱ : ℕ) (Λ : ℝ)
    (hnn : ∀ x y, 0 ≤ rate x y)
    (hfr : ∀ x y, rate x y ≠ 0 → (y - x).natAbs ≤ ϱ)
    (hexit : ∀ x, ∑' y, rate x y ≤ Λ)
    (p : ℝ → ℤ → ℝ)
    (hp0 : ∀ r, p 0 r = if r = 0 then 1 else 0)
    (hpnn : ∀ t r, 0 ≤ p t r)
    (hpode : ∀ t r, HasDerivAt (fun s => p s r)
      ((∑' y, rate y r * p t y) - (∑' y, rate r y) * p t r) t)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (N : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (∑ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), θ ^ x.natAbs * p s x)
      ≤ 1 + (Λ * (θ⁻¹) ^ ϱ)
          * ∫ t in (0 : ℝ)..s,
              ∑ x ∈ Finset.Icc (-((N : ℤ) + ϱ)) ((N : ℤ) + ϱ), θ ^ x.natAbs * p t x := by
  have h_bound : ∀ t ∈ Set.Icc 0 s, ∑ x ∈ Finset.Icc (-(N : ℤ)) N, θ ^ x.natAbs * ((∑' y, rate y x * p t y) - (∑' y, rate x y) * p t x) ≤ Λ * θ⁻¹ ^ ϱ * ∑ x ∈ Finset.Icc (-(N + ϱ : ℤ)) (N + ϱ : ℤ), θ ^ x.natAbs * p t x := by
    intro t ht
    have h_bound : ∑ x ∈ Finset.Icc (-(N : ℤ)) N, θ ^ x.natAbs * (∑' y, rate y x * p t y) ≤ Λ * θ⁻¹ ^ ϱ * ∑ x ∈ Finset.Icc (-(N + ϱ : ℤ)) (N + ϱ : ℤ), θ ^ x.natAbs * p t x := by
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ x ∈ Finset.Icc (-(N : ℤ)) N, θ ^ x.natAbs * ∑' y, rate y x * p t y = ∑ y ∈ Finset.Icc (-(N + ϱ : ℤ)) (N + ϱ : ℤ), ∑ x ∈ Finset.Icc (-(N : ℤ)) N, θ ^ x.natAbs * rate y x * p t y := by
        rw [ Finset.sum_comm, Finset.sum_congr rfl ];
        intro x hx; rw [ tsum_eq_sum ] ; simp +decide [ mul_assoc, Finset.mul_sum _ _ _ ] ;
        congr! 1;
        grind;
      -- Apply the bound on the weight ratio to each term in the sum.
      have h_weight_ratio : ∀ y ∈ Finset.Icc (-(N + ϱ : ℤ)) (N + ϱ : ℤ), ∑ x ∈ Finset.Icc (-(N : ℤ)) N, θ ^ x.natAbs * rate y x * p t y ≤ θ⁻¹ ^ ϱ * θ ^ y.natAbs * p t y * ∑ x ∈ Finset.Icc (-(N : ℤ)) N, rate y x := by
        intros y hy
        have h_weight_ratio : ∀ x ∈ Finset.Icc (-(N : ℤ)) N, rate y x ≠ 0 → θ ^ x.natAbs ≤ θ⁻¹ ^ ϱ * θ ^ y.natAbs := by
          intros x hx hxy
          have h_abs : (x - y).natAbs ≤ ϱ := by
            simpa only [ Int.natAbs_neg, neg_sub ] using hfr y x hxy;
          convert weight_ratio θ hθ0 hθ1.le ϱ x y h_abs using 1;
        rw [ Finset.mul_sum _ _ _ ];
        exact Finset.sum_le_sum fun x hx => by by_cases h : rate y x = 0 <;> simpa [ *, mul_assoc, mul_comm, mul_left_comm ] using mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( h_weight_ratio x hx h ) ( hpnn t y ) ) ( hnn y x ) ;
      -- Apply the bound on the exit rate to each term in the sum.
      have h_exit_rate : ∀ y ∈ Finset.Icc (-(N + ϱ : ℤ)) (N + ϱ : ℤ), ∑ x ∈ Finset.Icc (-(N : ℤ)) N, rate y x ≤ Λ := by
        intro y hy;
        refine' le_trans _ ( hexit y );
        refine' Summable.sum_le_tsum _ _ _;
        · exact fun _ _ => hnn _ _;
        · refine' summable_of_ne_finset_zero _;
          exact Finset.Icc ( y - ϱ ) ( y + ϱ );
          exact fun x hx => Classical.not_not.1 fun hx' => hx <| Finset.mem_Icc.2 ⟨ by cases abs_cases ( x - y ) <;> linarith [ hfr y x hx' ], by cases abs_cases ( x - y ) <;> linarith [ hfr y x hx' ] ⟩;
      rw [ h_fubini, Finset.mul_sum _ _ _ ];
      exact Finset.sum_le_sum fun y hy => le_trans ( h_weight_ratio y hy ) ( by nlinarith only [ h_exit_rate y hy, show 0 ≤ θ⁻¹ ^ ϱ * θ ^ y.natAbs * p t y by exact mul_nonneg ( mul_nonneg ( pow_nonneg ( inv_nonneg.2 hθ0.le ) _ ) ( pow_nonneg hθ0.le _ ) ) ( hpnn t y ) ] );
    simp_all +decide [ mul_sub ];
    exact le_add_of_le_of_nonneg h_bound ( Finset.sum_nonneg fun _ _ => mul_nonneg ( pow_nonneg hθ0.le _ ) ( mul_nonneg ( tsum_nonneg fun _ => hnn _ _ ) ( hpnn _ _ ) ) );
  have h_integral : ∫ t in (0 : ℝ)..s, ∑ x ∈ Finset.Icc (-(N : ℤ)) N, θ ^ x.natAbs * ((∑' y, rate y x * p t y) - (∑' y, rate x y) * p t x) = ∑ x ∈ Finset.Icc (-(N : ℤ)) N, θ ^ x.natAbs * p s x - ∑ x ∈ Finset.Icc (-(N : ℤ)) N, θ ^ x.natAbs * p 0 x := by
    rw [ intervalIntegral.integral_deriv_eq_sub' ];
    · ext t; norm_num [ hpode _ _ |> HasDerivAt.differentiableAt ] ;
      exact Finset.sum_congr rfl fun _ _ => by rw [ hpode _ _ |> HasDerivAt.deriv ] ;
    · -- Since each term in the sum is differentiable, the sum is differentiable.
      have h_diff : ∀ x ∈ Set.uIcc 0 s, ∀ r ∈ Finset.Icc (-N : ℤ) N, DifferentiableAt ℝ (fun s => p s r) x := by
        exact fun x hx r hr => HasDerivAt.differentiableAt ( hpode x r );
      fun_prop (disch := solve_by_elim);
    · refine' continuousOn_finset_sum _ fun x hx => ContinuousOn.mul _ _;
      · exact continuousOn_const;
      · refine' ContinuousOn.sub _ _;
        · refine' ContinuousOn.congr _ _;
          use fun t => ∑ y ∈ Finset.Icc ( x - ϱ : ℤ ) ( x + ϱ : ℤ ), rate y x * p t y;
          · exact continuousOn_finset_sum _ fun y hy => ContinuousOn.mul ( continuousOn_const ) ( continuousOn_of_forall_continuousAt fun t ht => HasDerivAt.continuousAt ( hpode t y ) );
          · intro t ht; simp +decide [ tsum_eq_sum, Finset.sum_ite ] ;
            rw [ tsum_eq_sum ];
            grind;
        · exact ContinuousOn.mul continuousOn_const ( continuousOn_of_forall_continuousAt fun t ht => HasDerivAt.continuousAt ( hpode t x ) );
  have h_integral_le : ∫ t in (0 : ℝ)..s, ∑ x ∈ Finset.Icc (-(N : ℤ)) N, θ ^ x.natAbs * ((∑' y, rate y x * p t y) - (∑' y, rate x y) * p t x) ≤ ∫ t in (0 : ℝ)..s, Λ * θ⁻¹ ^ ϱ * ∑ x ∈ Finset.Icc (-(N + ϱ : ℤ)) (N + ϱ : ℤ), θ ^ x.natAbs * p t x := by
    apply_rules [ intervalIntegral.integral_mono_on ];
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      refine' continuousOn_finset_sum _ fun x hx => ContinuousOn.mul _ _;
      · exact continuousOn_const;
      · refine' ContinuousOn.sub _ _;
        · refine' ContinuousOn.congr _ _;
          use fun u => ∑ y ∈ Finset.Icc ( x - ϱ : ℤ ) ( x + ϱ : ℤ ), rate y x * p u y;
          · exact continuousOn_finset_sum _ fun y hy => ContinuousOn.mul ( continuousOn_const ) ( continuousOn_of_forall_continuousAt fun u hu => HasDerivAt.continuousAt ( hpode u y ) );
          · intro u hu; simp +decide [ tsum_eq_sum, Finset.sum_ite ] ;
            rw [ tsum_eq_sum ];
            grind;
        · exact ContinuousOn.mul continuousOn_const ( continuousOn_of_forall_continuousAt fun u hu => HasDerivAt.continuousAt ( hpode u x ) );
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      exact ContinuousOn.mul continuousOn_const <| continuousOn_finset_sum _ fun _ _ => ContinuousOn.mul continuousOn_const <| continuousOn_of_forall_continuousAt fun u hu => HasDerivAt.continuousAt <| hpode u _;
  simp_all +decide [ intervalIntegral.integral_comp_mul_left ];
  linarith

end TypeDDecouplingSemigroup
