/-
# Tightness on `D([0,1],ℝ)` and Aldous's criterion (Skorokhod campaign, 3/5)

Library-clean file building on `TypeDDecouplingSkorokhodBasic`,
`TypeDDecouplingSkorokhodCompact`, `TypeDDecouplingSkorokhodComplete` (the latter
supplies the `CompleteSpace`/`SecondCountableTopology`/`PolishSpace` instances).

Contents (see `skorokhod3_brief.tex`).  This file reaches the following rung of the
brief's fallback ladder: **Tiers 0, 1(a)–sup-norm, 1(b), and 2 are complete and
`sorry`-free**; the deliverable tightness criterion is the sufficiency bridge
`isTightMeasureSet_of_bdd_of_modulus` (Tier 1(b)).

* **Tier 0** — Billingsley Thm 12.3 (compactness), *sufficiency*: a set that is
  uniformly bounded and has uniformly decaying càdlàg modulus is totally
  bounded, hence relatively compact (`totallyBounded_of_bdd_of_modulus`,
  `isCompact_closure_of_bdd_of_modulus`).
* **Tier 1** — the sup-norm `f ↦ supNorm f` is `1`-Lipschitz, hence Borel
  measurable (`measurable_supNorm`); and the tightness bridge, sufficiency
  direction (`isTightMeasureSet_of_bdd_of_modulus`), proved without any
  measurability of the level sets (only monotonicity/subadditivity of measures).
* **Tier 2** — càdlàg oscillation hitting times are stopping times of the
  right-continuous filtration (`isStoppingTime_crossTime`, and the supporting
  `crossTime_le_iff` / `measurableSet_crossTime_le`).

**Identified gaps (Billingsley 16 fights), not reached here:**

* Borel measurability of the càdlàg modulus `f ↦ cadlagModulus f.toFun δ`
  (Tier 1(a), `w'`).  Its rational-partition reduction is elementary, but it
  ultimately requires measurability of the coordinate evaluations
  `f ↦ f.toFun q` on `D` (equivalently, that the Borel σ-algebra of `D` is the
  projection σ-algebra).  Evaluation is *continuous only at continuity points*
  (`SkorokhodBasic.continuousAt_eval`), so its measurability needs the
  integral-average approximation `f(q) = lim_n n∫_q^{q+1/n} f`, whose functionals
  are `d°`-continuous by dominated convergence along the Skorokhod time changes
  (`tendsto_iff_exists_timeChanges`).  This is a self-contained sub-project.
* Aldous's criterion itself (Tier 3, `aldous_tightness` / `aldous_of_moment`):
  the averaging argument (Billingsley (16.24)ff) turning the two-time stopping
  condition into a modulus bound, on top of the `w'` measurability above.
-/
import Mathlib
import TypeDDecouplingSkorokhodBasic
import TypeDDecouplingSkorokhodCompact
import TypeDDecouplingSkorokhodComplete

set_option maxHeartbeats 4000000

open scoped Topology BigOperators
open Filter Set

namespace SkorokhodBasic

noncomputable section

/-! ## Borel measurable-space structure on `Skoro` -/

instance : MeasurableSpace Skoro := borel Skoro
instance : BorelSpace Skoro := ⟨rfl⟩

/-! ## Tier 0: compactness sufficiency (Billingsley Thm 12.3, ⇐) -/

/-- The sup-norm on `[0,1]` of a path. -/
def supNorm (f : Skoro) : ℝ := supDiff f.toFun (fun _ => 0)

/-
If `f` is bounded on `[0,1]` by `M` and `δ < 1`, the admissible modulus set is
nonempty (witnessed by the trivial one-cell partition).
-/
theorem modulusSet_nonempty {f : ℝ → ℝ} {M : ℝ}
    (hb : ∀ t ∈ Set.Icc (0:ℝ) 1, |f t| ≤ M) {δ : ℝ} (hδ : δ < 1) :
    (modulusSet f δ).Nonempty := by
  refine' ⟨ 2 * M, _, 1, fun i => if i = 0 then 0 else 1, _, _, _, _, _ ⟩ <;> norm_num;
  · exact le_trans ( abs_nonneg _ ) ( hb 0 ( by norm_num ) );
  · exact ⟨ hδ, fun x hx₁ hx₂ => by linarith [ abs_sub ( f x ) ( f 0 ), hb x ⟨ hx₁, hx₂.le ⟩, hb 0 ⟨ by norm_num, by norm_num ⟩ ] ⟩

/-
If the càdlàg modulus is below `ε`, there is a genuine `δ`-sparse partition whose
left-endpoint oscillation is below `ε`.
-/
theorem exists_partition_of_cadlagModulus_lt {f : ℝ → ℝ} {δ ε : ℝ}
    (hne : (modulusSet f δ).Nonempty) (h : cadlagModulus f δ < ε) :
    ∃ (n : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t n = 1 ∧ 0 < n ∧
      (∀ i, i < n → t i < t (i + 1)) ∧
      (∀ i, i < n → δ < t (i + 1) - t i) ∧
      (∀ i, i < n → ∀ x ∈ Set.Ico (t i) (t (i + 1)), |f x - f (t i)| < ε) := by
  rcases exists_lt_of_csInf_lt hne h with ⟨ x, hx₁, hx₂ ⟩;
  rcases hx₁ with ⟨ hx₀, n, t, ht₀, ht₁, hn, ht₂, ht₃, ht₄ ⟩ ; exact ⟨ n, t, ht₀, ht₁, hn, ht₂, ht₃, fun i hi x hx => lt_of_le_of_lt ( ht₄ i hi x hx ) hx₂ ⟩ ;

/-
Cells longer than `δ` cannot be too many: `n·δ < 1`.
-/
theorem card_cells_lt {n : ℕ} {t : ℕ → ℝ} {δ : ℝ}
    (ht0 : t 0 = 0) (htn : t n = 1) (hmesh : ∀ i, i < n → δ < t (i + 1) - t i) :
    (n : ℝ) * δ < 1 := by
  by_cases hn : n = 0;
  · aesop;
  · convert Finset.sum_lt_sum_of_nonempty ( Finset.nonempty_range_iff.mpr hn ) fun i hi => hmesh i ( Finset.mem_range.mp hi ) using 1;
    · norm_num;
    · rw [ Finset.sum_range_sub, htn, ht0, sub_zero ]

/-- The finite index set of the `ε`-net: step functions with at most `N` cells, cut
points on the `K`-grid, and values on the `1/D`-lattice bounded by `C/D`. -/
def netIdx (N K C D : ℕ) : Finset SepIndex :=
  (Finset.range (N + 1)).sigma (fun n =>
    (Fintype.piFinset (fun _ : Fin (n + 1) =>
        (Finset.Icc (0 : ℤ) K).image (fun k : ℤ => (k : ℚ) / K)))
      ×ˢ
    (Fintype.piFinset (fun _ : Fin (n + 1) =>
        (Finset.Icc (-(C : ℤ)) C).image (fun k : ℤ => (k : ℚ) / D))))

/-
Grid-rounded nodes: rounding an increasing `δ`-sparse partition to the `K`-grid
(with `K` large) yields a valid rational grid whose gaps are within `exp(±η)` of the
original gaps, with numerators in `Icc 0 K`.
-/
theorem exists_gridNodes {n : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0) (htn : t n = 1)
    (htmono : ∀ i, i < n → t i < t (i + 1)) (htIcc : ∀ i, i ≤ n → t i ∈ Set.Icc (0:ℝ) 1)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hmesh : ∀ i, i < n → δ < t (i + 1) - t i)
    {K : ℕ} (hKpos : 0 < K)
    (hK1 : (1:ℝ) / K ≤ δ * (1 - Real.exp (-η)))
    (hK2 : Real.exp η / K ≤ δ * (Real.exp η - 1)) :
    ∃ r : ℕ → ℤ,
      (r 0 = 0) ∧ (r n = K) ∧
      (∀ i, i ≤ n → r i ∈ Finset.Icc (0:ℤ) K) ∧
      (∀ i, i < n → ((r i : ℝ) / K) < ((r (i + 1) : ℝ) / K)) ∧
      (∀ i, i ≤ n → ((r i : ℝ) / K) ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ i, i < n → Real.exp (-η) * ((r (i + 1) : ℝ) / K - (r i : ℝ) / K) ≤ t (i + 1) - t i) ∧
      (∀ i, i < n → t (i + 1) - t i ≤ Real.exp η * ((r (i + 1) : ℝ) / K - (r i : ℝ) / K)) := by
  refine' ⟨ fun i => ⌊t i * K + 1 / 2⌋, _, _, _, _, _, _ ⟩ <;> norm_num;
  all_goals norm_num [ ht0, htn ];
  · exact fun i hi => ⟨ Int.floor_nonneg.2 <| by nlinarith [ Set.mem_Icc.1 <| htIcc i hi, show ( K : ℝ ) ≥ 1 by norm_cast ], Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; nlinarith [ Set.mem_Icc.1 <| htIcc i hi, show ( K : ℝ ) ≥ 1 by norm_cast ] ⟩;
  · intro i hi; rw [ div_lt_div_iff_of_pos_right ( by positivity ) ] ; norm_num [ Int.floor_lt ] ;
    nlinarith [ Real.add_one_le_exp η, Real.exp_pos η, Real.exp_neg η, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos η ) ), mul_pos hδ ( Real.exp_pos η ), mul_pos hδ ( Real.exp_pos ( -η ) ), Int.floor_le ( t ( i + 1 ) * K + 1 / 2 ), Int.lt_floor_add_one ( t ( i + 1 ) * K + 1 / 2 ), hmesh i hi, htmono i hi, show ( K : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( 1 : ℝ ) ( by positivity : ( K : ℝ ) ≠ 0 ) ];
  · intro i hi; rw [ le_div_iff₀ ( by positivity ), div_le_iff₀ ( by positivity ) ] ; norm_num;
    exact ⟨ Int.floor_nonneg.2 ( by nlinarith [ Set.mem_Icc.mp ( htIcc i hi ), show ( K : ℝ ) ≥ 1 by norm_cast ] ), by exact_mod_cast Int.le_of_lt_add_one ( Int.floor_lt.2 ( by norm_num; nlinarith [ Set.mem_Icc.mp ( htIcc i hi ), show ( K : ℝ ) ≥ 1 by norm_cast ] ) ) ⟩;
  · constructor <;> intro i hi;
    · field_simp;
      have := Int.floor_le ( ( t ( i + 1 ) * K * 2 + 1 ) / 2 );
      have := Int.lt_floor_add_one ( ( K * 2 * t i + 1 ) / 2 );
      rw [ div_le_iff₀ ( by positivity ) ] at hK1;
      nlinarith [ hmesh i hi, Real.exp_pos ( -η ), Real.exp_le_one_iff.mpr ( show -η ≤ 0 by linarith ), mul_le_mul_of_nonneg_left ( Real.exp_le_one_iff.mpr ( show -η ≤ 0 by linarith ) ) ( show ( 0 : ℝ ) ≤ K by positivity ) ];
    · have h_floor : (⌊t (i + 1) * K + 1 / 2⌋ : ℝ) - (⌊t i * K + 1 / 2⌋ : ℝ) ≥ (t (i + 1) - t i) * K - 1 := by
        linarith [ Int.lt_floor_add_one ( t ( i + 1 ) * K + 1 / 2 ), Int.floor_le ( t i * K + 1 / 2 ) ];
      field_simp at *;
      nlinarith [ hmesh i hi, Real.add_one_le_exp η, Real.exp_pos η, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos η ) ), Real.exp_neg η, mul_pos hδ ( Real.exp_pos η ), mul_pos hδ ( Real.exp_pos ( -η ) ) ]

/-
**Net approximation** (the crux of Tier 0): under the size conditions relating
`N,K,C,D` to `ε,δ,η,M`, every bounded path with small càdlàg modulus is within `ε` of
a member of the finite net `sepFun '' netIdx N K C D`.
-/
theorem net_approx {A : Set Skoro} {M : ℝ}
    (hbdd : ∀ f ∈ A, ∀ t ∈ Set.Icc (0:ℝ) 1, |f.toFun t| ≤ M)
    {ε δ η : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η) (hηε : η ≤ ε / 4)
    {N K C D : ℕ} (hKpos : 0 < K) (hDpos : 0 < D)
    (hN : (1:ℝ) / δ ≤ N)
    (hK1 : (1:ℝ) / K ≤ δ * (1 - Real.exp (-η)))
    (hK2 : Real.exp η / K ≤ δ * (Real.exp η - 1))
    (hDε : (1:ℝ) / D ≤ ε / 4)
    (hC : (M : ℝ) * D + 1 ≤ C)
    {f : Skoro} (hf : f ∈ A) (hcm : cadlagModulus f.toFun δ < ε / 4) :
    ∃ p ∈ netIdx N K C D, dCirc f (sepFun p) < ε := by
  -- By partitioning f with gaps greater than δ, we obtain n, t with desired properties.
  obtain ⟨ n, t, ht0, htn, hmn, htmono, hmesh, hosc ⟩ := exists_partition_of_cadlagModulus_lt (by
  exact modulusSet_nonempty ( hbdd f hf ) hδ1) hcm;
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℤ, (∀ i, i ≤ n → v i ∈ Finset.Icc (-(C : ℤ)) C) ∧ (∀ i, i ≤ n → |f.toFun (t i) - ((v i : ℝ) / D)| ≤ 1 / (2 * D)) := by
    refine' ⟨ fun i => ⌊f.toFun ( t i ) * D + 1 / 2⌋, _, _ ⟩ <;> norm_num;
    · intro i hi
      have h_bound : |f.toFun (t i)| ≤ M := by
        apply hbdd f hf;
        induction' i with i ih;
        · norm_num [ ht0 ];
        · have h_monotone : ∀ i j, i ≤ j → j ≤ n → t i ≤ t j := by
            intro i j hij hjn; induction hij <;> simp_all +decide [ Nat.succ_le_iff ] ;
            exact le_trans ( by solve_by_elim [ le_of_lt ] ) ( le_of_lt ( htmono _ hjn ) );
          exact ⟨ by linarith [ ih ( Nat.le_of_succ_le hi ), h_monotone 0 ( i + 1 ) ( by linarith ) ( by linarith ) ], by linarith [ h_monotone ( i + 1 ) n ( by linarith ) ( by linarith ) ] ⟩;
      exact ⟨ Int.le_floor.2 <| by norm_num; nlinarith [ abs_le.mp h_bound, show ( D : ℝ ) ≥ 1 by norm_cast ], Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; nlinarith [ abs_le.mp h_bound, show ( D : ℝ ) ≥ 1 by norm_cast ] ⟩;
    · intro i hi; rw [ abs_le ] ; constructor <;> nlinarith [ Int.floor_le ( f.toFun ( t i ) * D + 1 / 2 ), Int.lt_floor_add_one ( f.toFun ( t i ) * D + 1 / 2 ), show ( D : ℝ ) > 0 by positivity, mul_div_cancel₀ ( ⌊f.toFun ( t i ) * D + 1 / 2⌋ : ℝ ) ( by positivity : ( D : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( D : ℝ ) ≠ 0 ) ] ;
  obtain ⟨r, hr⟩ := exists_gridNodes ht0 htn htmono (fun i hi => by
    have h_monotone : ∀ i j, i ≤ j → j ≤ n → t i ≤ t j := by
      intro i j hij hjn; induction hij <;> norm_num at *;
      exact le_trans ( by solve_by_elim [ Nat.le_of_lt ] ) ( le_of_lt ( htmono _ hjn ) );
    exact ⟨ by linarith [ h_monotone 0 i ( by norm_num ) hi ], by linarith [ h_monotone i n hi ( by linarith ) ] ⟩) hδ hη hmesh hKpos hK1 hK2;
  refine' ⟨ ⟨ n, fun i => ( r i : ℚ ) / K, fun i => ( v i : ℚ ) / D ⟩, _, _ ⟩ <;> simp_all +decide [ netIdx ];
  · refine' ⟨ _, _, _ ⟩;
    · have := card_cells_lt ht0 htn hmesh;
      exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ mul_inv_cancel₀ ( ne_of_gt hδ ) ] );
    · exact fun i => ⟨ r i, hr.2.2.1 i ( Fin.is_le i ), rfl ⟩;
    · exact fun i => ⟨ v i, hv.1 i ( Fin.is_le i ), rfl ⟩;
  · -- By definition of `sepFun`, we know that `sepFun ⟨n, (fun i => ↑(r ↑i) / ↑K, fun i => ↑(v ↑i) / ↑D)⟩` is equal to `stepSkoro n (fun i => ((r i : ℝ) / K)) (fun i => ((v i : ℝ) / D))`.
    have h_sepFun_eq : sepFun ⟨n, (fun i => (r i : ℚ) / K, fun i => (v i : ℚ) / D)⟩ = stepSkoro n (fun i => ((r i : ℝ) / K)) (fun i => ((v i : ℝ) / D)) (by
    aesop) (by
    simp +decide [ hr.2.1, hKpos.ne' ]) (by
    exact hr.2.2.2.1) := by
      unfold sepFun stepSkoro; simp +decide [ hr ] ;
      split_ifs <;> simp_all +decide [ ne_of_gt ];
      · unfold stepFun; simp +decide [ Finset.sum_range, Nat.lt_succ_iff ] ;
      · grind
    generalize_proofs at *;
    -- By definition of `stepSkoro`, we know that `stepSkoro n t (fun i => f.toFun (t i))` is equal to `f`.
    have h_stepSkoro_eq : dCirc f (stepSkoro n t (fun i => f.toFun (t i)) ht0 htn htmono) ≤ ε / 4 := by
      refine' le_trans ( dCirc_le_supDiff _ _ ) _;
      refine' csSup_le _ _ <;> norm_num;
      · exact supDiffSet_nonempty _ _;
      · rintro _ ⟨ x, hx, rfl ⟩;
        by_cases hx1 : x = 1;
        · rw [ hx1, stepFun_eq_last ] <;> norm_num [ htn ];
          · linarith;
          · exact htmono;
        · obtain ⟨ j, hj ⟩ := exists_cell_index ( show t 0 = 0 from ht0 ) ( show t n = 1 from htn ) ( show x ∈ Set.Ico 0 1 from ⟨ hx.1, lt_of_le_of_ne hx.2 hx1 ⟩ );
          rw [ stepFun_eq_on_cell n t ( fun i => f.toFun ( t i ) ) htmono hj.1 hj.2 ] ; exact le_of_lt ( hosc j hj.1 x hj.2.1 hj.2.2 );
    -- By definition of `stepSkoro`, we know that `stepSkoro n t (fun i => ((v i : ℝ) / D))` is equal to `stepSkoro n t (fun i => f.toFun (t i))`.
    have h_stepSkoro_eq' : dCirc (stepSkoro n t (fun i => f.toFun (t i)) ht0 htn htmono) (stepSkoro n t (fun i => ((v i : ℝ) / D)) ht0 htn htmono) ≤ 1 / (2 * D) := by
      refine' le_trans ( dCirc_le_supDiff _ _ ) _;
      refine' csSup_le _ _ <;> norm_num;
      · exact supDiffSet_nonempty _ _;
      · rintro _ ⟨ x, hx, rfl ⟩;
        by_cases hx' : x = 1;
        · simp_all +decide [ stepFun_eq_last ];
          simpa [ htn ] using hv.2 n le_rfl;
        · obtain ⟨ j, hj₁, hj₂ ⟩ := exists_cell_index ht0 htn ( show x ∈ Set.Ico 0 1 from ⟨ hx.1, lt_of_le_of_ne hx.2 hx' ⟩ );
          rw [ stepFun_eq_on_cell n t ( fun i => f.toFun ( t i ) ) htmono hj₁ hj₂, stepFun_eq_on_cell n t ( fun i => ( v i : ℝ ) / D ) htmono hj₁ hj₂ ];
          simpa using hv.2 j ( by linarith );
    -- By definition of `stepSkoro`, we know that `stepSkoro n (fun i => ((r i : ℝ) / K)) (fun i => ((v i : ℝ) / D))` is equal to `stepSkoro n t (fun i => ((v i : ℝ) / D))`.
    have h_stepSkoro_eq'' : dCirc (stepSkoro n t (fun i => ((v i : ℝ) / D)) ht0 htn htmono) (stepSkoro n (fun i => ((r i : ℝ) / K)) (fun i => ((v i : ℝ) / D)) (by
    lia) (by
    grind) (by
    grind +qlia)) ≤ η := by
      apply dCirc_stepSkoro_le n t (fun i => ((r i : ℝ) / K)) (fun i => ((v i : ℝ) / D)) η (le_of_lt hη) htmono ht0 htn (fun i hi => by
        have h_monotone : ∀ i j, i ≤ j → j ≤ n → t i ≤ t j := by
          intro i j hij hjn; induction hij <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
          exact le_trans ( by solve_by_elim [ Nat.le_of_lt ] ) ( le_of_lt ( htmono _ hjn ) )
        generalize_proofs at *;
        exact ⟨ by linarith [ h_monotone 0 i ( by norm_num ) hi ], by linarith [ h_monotone i n hi ( by norm_num ) ] ⟩) (fun i hi => by
        exact hr.2.2.2.1 i hi) (by
      lia) (by
      grind) (by
      exact fun i hi => hr.2.2.2.2.1 i hi) (by
      exact hr.2.2.2.2.2.1) (by
      exact fun i hi => by linarith [ hr.2.2.2.2.2.2 i hi ] ;)
    generalize_proofs at *;
    have h_triangle : dCirc f (stepSkoro n (fun i => ((r i : ℝ) / K)) (fun i => ((v i : ℝ) / D)) (by
    grind +splitImp) (by
    grind) (by
    grind)) ≤ dCirc f (stepSkoro n t (fun i => f.toFun (t i)) ht0 htn htmono) + dCirc (stepSkoro n t (fun i => f.toFun (t i)) ht0 htn htmono) (stepSkoro n t (fun i => ((v i : ℝ) / D)) ht0 htn htmono) + dCirc (stepSkoro n t (fun i => ((v i : ℝ) / D)) ht0 htn htmono) (stepSkoro n (fun i => ((r i : ℝ) / K)) (fun i => ((v i : ℝ) / D)) (by
    grind +splitImp) (by
    grind) (by
    grind)) := by
      exact le_trans ( dCirc_triangle _ _ _ ) ( add_le_add ( dCirc_triangle _ _ _ ) le_rfl )
    generalize_proofs at *;
    rw [ h_sepFun_eq ] ; linarith [ show ( 1 : ℝ ) / ( 2 * D ) ≤ ε / 4 by ring_nf at *; linarith ] ;

/-
**Tier 0** (Billingsley 12.3, ⇐): a uniformly bounded family with uniformly
decaying càdlàg modulus is totally bounded.
-/
theorem totallyBounded_of_bdd_of_modulus (A : Set Skoro) {M : ℝ}
    (hbdd : ∀ f ∈ A, ∀ t ∈ Set.Icc (0:ℝ) 1, |f.toFun t| ≤ M)
    (hmod : ∀ ε > 0, ∃ δ > 0, δ < 1 ∧ ∀ f ∈ A, cadlagModulus f.toFun δ < ε) :
    TotallyBounded A := by
  refine' Metric.totallyBounded_iff.mpr _;
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_lt_1, hcm⟩ := hmod (ε / 4) (by linarith)
  set η := ε / 4 with hη_def
  obtain ⟨N, K, C, D, hKpos, hDpos, hN, hK1, hK2, hDε, hC⟩ : ∃ N K C D : ℕ, 0 < K ∧ 0 < D ∧ (1:ℝ)/δ ≤ N ∧ (1:ℝ)/K ≤ δ*(1-Real.exp (-η)) ∧ Real.exp η/K ≤ δ*(Real.exp η - 1) ∧ (1:ℝ)/D ≤ ε/4 ∧ (M : ℝ)*D + 1 ≤ C := by
    refine' ⟨ ⌈1 / δ⌉₊, ⌈1 / ( δ * ( 1 - Real.exp ( -η ) ) ) ⌉₊ + ⌈Real.exp η / ( δ * ( Real.exp η - 1 ) ) ⌉₊ + 1, ⌈M * ( ⌈4 / ε⌉₊ + 1 ) + 1⌉₊, ⌈4 / ε⌉₊ + 1, _, _, _, _, _ ⟩ <;> norm_num;
    · exact Nat.le_ceil _;
    · rw [ inv_le_comm₀ ] <;> norm_num;
      · linarith [ Nat.le_ceil ( ( 1 - Real.exp ( -η ) ) ⁻¹ * δ⁻¹ ), Nat.le_ceil ( Real.exp η / ( δ * ( Real.exp η - 1 ) ) ) ];
      · positivity;
      · exact mul_pos hδ_pos ( sub_pos_of_lt ( Real.exp_lt_one_iff.mpr ( by linarith ) ) );
    · refine' ⟨ _, _, _ ⟩;
      · rw [ div_le_iff₀ ];
        · have := Nat.le_ceil ( Real.exp η / ( δ * ( Real.exp η - 1 ) ) );
          rw [ div_le_iff₀ ] at this <;> nlinarith [ Real.add_one_le_exp η, Real.exp_pos η, mul_pos hδ_pos ( Real.exp_pos η ), mul_pos hδ_pos ( sub_pos.mpr ( show 1 < Real.exp η from by norm_num; positivity ) ) ];
        · positivity;
      · rw [ inv_eq_one_div, div_le_iff₀ ] <;> nlinarith [ Nat.le_ceil ( 4 / ε ), mul_div_cancel₀ 4 hε.ne' ];
      · exact Nat.le_ceil _;
  refine' ⟨ _, _, _ ⟩;
  exact Set.image ( fun p : SepIndex => sepFun p ) ( netIdx N K C D |> Finset.toSet );
  · exact Set.Finite.image _ ( Finset.finite_toSet _ );
  · intro f hf
    obtain ⟨p, hp⟩ := net_approx hbdd hε hδ_pos hδ_lt_1 (by linarith) (by linarith) hKpos hDpos hN hK1 hK2 hDε hC hf (hcm f hf);
    exact Set.mem_iUnion₂.mpr ⟨ _, Set.mem_image_of_mem _ ( Finset.mem_coe.mpr hp.1 ), by simpa [ dist_eq_dCirc ] using hp.2 ⟩

/-- **Tier 0** (relative compactness): the closure is compact. -/
theorem isCompact_closure_of_bdd_of_modulus (A : Set Skoro) {M : ℝ}
    (hbdd : ∀ f ∈ A, ∀ t ∈ Set.Icc (0:ℝ) 1, |f.toFun t| ≤ M)
    (hmod : ∀ ε > 0, ∃ δ > 0, δ < 1 ∧ ∀ f ∈ A, cadlagModulus f.toFun δ < ε) :
    IsCompact (closure A) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨(totallyBounded_of_bdd_of_modulus A hbdd hmod).closure,
    isClosed_closure.isComplete⟩

/-! ## Tier 1: measurability primitives and the tightness bridge -/

open MeasureTheory
open scoped ENNReal

/-
Every value of a path is bounded by its sup-norm.
-/
theorem abs_le_supNorm (f : Skoro) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |f.toFun t| ≤ supNorm f := by
  convert SkorokhodBasic.le_supDiff _ ht using 1 ; norm_num [ SkorokhodBasic.supDiffSet ];
  convert SkorokhodBasic.bddAbove_supDiffSet _ _;
  exacts [ f.bdd'.choose, 0, fun t ht => f.bdd'.choose_spec t ht, fun t ht => by norm_num ]

/-
General triangle inequality for `supDiff` (both arguments bounded on `[0,1]`).
-/
theorem supDiff_triangle (f g h : Skoro) :
    supDiff f.toFun h.toFun ≤ supDiff f.toFun g.toFun + supDiff g.toFun h.toFun := by
  refine' csSup_le _ _ <;> norm_num [ supDiffSet_nonempty ];
  rintro _ ⟨ t, ht, rfl ⟩;
  refine' le_trans _ ( add_le_add ( le_supDiff _ _ ) ( le_supDiff _ _ ) );
  exact abs_sub_le _ _ _;
  · exact SkorokhodBasic.bddAbove_supDiffSet ( fun t ht => f.bdd' |> Classical.choose_spec |> fun h => h t ht ) ( fun t ht => g.bdd' |> Classical.choose_spec |> fun h => h t ht );
  · exact ht;
  · obtain ⟨ C₁, hC₁ ⟩ := g.bdd'
    obtain ⟨ C₂, hC₂ ⟩ := h.bdd'
    use C₁ + C₂
    intro r hr
    obtain ⟨ t, ht, rfl ⟩ := hr
    exact abs_le.mpr ⟨ by linarith [ abs_le.mp ( hC₁ t ht ), abs_le.mp ( hC₂ t ht ) ], by linarith [ abs_le.mp ( hC₁ t ht ), abs_le.mp ( hC₂ t ht ) ] ⟩;
  · exact ht

/-
A time change does not affect the sup-norm (it is a surjection of `[0,1]`).
-/
theorem supDiff_comp_eq (f : Skoro) (l : TimeChange) :
    supDiff (fun t => f.toFun (l.toFun t)) (fun _ => 0) = supNorm f := by
  convert ( congr_arg ( fun x : Set ℝ => sSup x ) ?_ ) using 1;
  ext; constructor <;> rintro ⟨ t, ht, rfl ⟩;
  · exact ⟨ l.toFun t, l.mapsTo' ht, rfl ⟩;
  · obtain ⟨ u, hu, hu' ⟩ := l.surjOn ( show t ∈ Set.Icc 0 1 from ht ) ; use u; aesop;

/-
`supNorm` is `1`-Lipschitz for the Skorokhod metric, hence continuous.
-/
theorem dist_supNorm_le (f g : Skoro) : |supNorm f - supNorm g| ≤ dCirc f g := by
  refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
  · have h_le : ∀ r ∈ dCircSet f g, supNorm f - supNorm g ≤ r := by
      rintro r ⟨ l, hl, rfl ⟩;
      have h_supDiff_triangle : supDiff (fun t => f.toFun (l.toFun t)) g.toFun ≥ supNorm f - supNorm g := by
        have h_supDiff_triangle : supDiff (fun t => f.toFun (l.toFun t)) (fun _ => 0) ≤ supDiff (fun t => f.toFun (l.toFun t)) g.toFun + supDiff g.toFun (fun _ => 0) := by
          convert supDiff_triangle ( Skoro.compTimeChange f l ) g zeroPath using 1;
        linarith! [ supDiff_comp_eq f l ];
      exact le_trans h_supDiff_triangle ( le_max_right _ _ );
    exact le_csInf ( dCircSet_nonempty f g ) h_le;
  · refine' le_of_forall_pos_le_add fun ε εpos => _;
    -- By definition of $dCirc$, there exists a time change $l$ such that $logSlopeNorm l \leq dCirc f g + \epsilon / 2$ and $supDiff (fun t => f.toFun (l.toFun t)) g.toFun \leq dCirc f g + \epsilon / 2$.
    obtain ⟨l, hl⟩ : ∃ l : TimeChange, FiniteNorm l ∧ logSlopeNorm l ≤ dCirc f g + ε / 2 ∧ supDiff (fun t => f.toFun (l.toFun t)) g.toFun ≤ dCirc f g + ε / 2 := by
      obtain ⟨r, hr⟩ : ∃ r ∈ dCircSet f g, r ≤ dCirc f g + ε / 2 := by
        exact exists_lt_of_csInf_lt ( dCircSet_nonempty f g ) ( lt_add_of_pos_right _ ( half_pos εpos ) ) |> fun ⟨ r, hr₁, hr₂ ⟩ => ⟨ r, hr₁, le_of_lt hr₂ ⟩;
      rcases hr with ⟨ ⟨ l, hl₁, rfl ⟩, hr ⟩ ; exact ⟨ l, hl₁, by linarith [ le_max_left ( logSlopeNorm l ) ( supDiff ( fun t => f.toFun ( l.toFun t ) ) g.toFun ) ], by linarith [ le_max_right ( logSlopeNorm l ) ( supDiff ( fun t => f.toFun ( l.toFun t ) ) g.toFun ) ] ⟩ ;
    -- By definition of $supNorm$, we have $supNorm g \leq supDiff g.toFun F.toFun + supNorm F$.
    have h_supNorm_g : supNorm g ≤ supDiff g.toFun (fun t => f.toFun (l.toFun t)) + supNorm f := by
      convert supDiff_triangle g ( Skoro.compTimeChange f l ) zeroPath using 1;
      exact congr_arg₂ _ rfl ( supDiff_comp_eq f l ▸ rfl );
    linarith [ show supDiff g.toFun ( fun t => f.toFun ( l.toFun t ) ) ≤ dCirc f g + ε / 2 by simpa only [ supDiff_comm ] using hl.2.2 ]

theorem continuous_supNorm : Continuous supNorm := by
  rw [Metric.continuous_iff]
  intro g ε hε
  refine ⟨ε, hε, fun a ha => ?_⟩
  have := dist_supNorm_le a g
  rw [Real.dist_eq]
  rw [dist_eq_dCirc] at ha
  linarith [dist_supNorm_le a g]

/-- **Tier 1(a)**: the sup-norm is Borel measurable on `D`. -/
theorem measurable_supNorm : Measurable supNorm :=
  continuous_supNorm.measurable

/-
**Tier 1(b)** (Billingsley 13.2/16.3, sufficiency): a family of measures that is
uniformly tight in sup-norm and has uniformly (in probability) decaying càdlàg modulus
is tight on `D`.

Working setting: `S` is any set of measures; the two hypotheses bound, uniformly over
`μ ∈ S`, the mass of the "large sup-norm" sets and of the "large modulus" sets.  No
measurability of these sets is needed — only monotonicity and countable subadditivity of
measures.
-/
theorem isTightMeasureSet_of_bdd_of_modulus (S : Set (Measure Skoro))
    (hbdd : ∀ η : ℝ≥0∞, 0 < η → ∃ a : ℝ, ∀ μ ∈ S, μ {f : Skoro | a ≤ supNorm f} ≤ η)
    (hmod : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∀ μ ∈ S, μ {f : Skoro | ε ≤ cadlagModulus f.toFun δ} ≤ η) :
    IsTightMeasureSet S := by
  refine' isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr _;
  intro ε hε
  obtain ⟨a, ha⟩ := hbdd (ε / 2) (ENNReal.half_pos hε.ne');
  choose! δ hδ_pos hδ_lt_one hδ using fun k : ℕ => hmod ( 1 / ( k + 1 ) ) ( by positivity ) ( ε * ( 1 / 2 ) ^ ( k + 2 ) ) ( by exact ENNReal.mul_pos ( by aesop ) ( by aesop ) );
  refine' ⟨ closure { f : Skoro | supNorm f ≤ a ∧ ∀ k : ℕ, cadlagModulus f.toFun ( δ k ) < 1 / ( k + 1 ) }, _, _ ⟩;
  · refine' isCompact_closure_of_bdd_of_modulus _ _ _;
    exact a;
    · exact fun f hf t ht => le_trans ( abs_le_supNorm f ht ) hf.1;
    · intro ε hε_pos
      obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 / (k + 1 : ℝ) < ε := by
        exact ⟨ ⌊ε⁻¹⌋₊, by simpa using inv_lt_of_inv_lt₀ hε_pos <| Nat.lt_floor_add_one _ ⟩;
      exact ⟨ δ k, hδ_pos k, hδ_lt_one k, fun f hf => lt_of_lt_of_le ( hf.2 k ) hk.le ⟩;
  · intro μ hμ
    have h_compl : μ (closure {f : Skoro | supNorm f ≤ a ∧ ∀ k : ℕ, cadlagModulus f.toFun (δ k) < 1 / (k + 1)})ᶜ ≤ μ {f : Skoro | a < supNorm f} + μ (⋃ k : ℕ, {f : Skoro | 1 / (k + 1) ≤ cadlagModulus f.toFun (δ k)}) := by
      refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
      intro f hf; contrapose! hf; simp_all +decide [ Set.subset_def ] ;
      exact subset_closure hf;
    refine' le_trans h_compl ( le_trans ( add_le_add ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_iUnion_le _ ) ) _ );
    exact { f : Skoro | a ≤ supNorm f };
    · exact fun x hx => hx.out.le;
    · refine' le_trans ( add_le_add ( ha μ hμ ) ( ENNReal.tsum_le_tsum fun k => hδ k μ hμ ) ) _;
      norm_num [ pow_add, ENNReal.tsum_mul_left ];
      rw [ ENNReal.tsum_mul_right, ENNReal.tsum_geometric ] ; norm_num;
      rw [ show ( 2 : ENNReal ) * 2⁻¹ ^ 2 = 2⁻¹ by
            rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num;
            norm_num [ ENNReal.mul_eq_top ] ] ; ring_nf;
      rw [ ENNReal.div_eq_inv_mul ] ; ring_nf;
      rw [ mul_right_comm, ENNReal.inv_mul_cancel ] <;> norm_num

/-! ## Tier 2: càdlàg oscillation hitting times are stopping times -/

section Tier2

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Membership in the right-continuous filtration reduces to membership in `𝓕 v` for all
`v > t`. -/
theorem measurableSet_rightCont_of (𝓕 : Filtration ℝ m) {t : ℝ} {s : Set Ω}
    (h : ∀ v : ℝ, t < v → MeasurableSet[𝓕 v] s) : MeasurableSet[𝓕.rightCont t] s := by
  rw [Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf]
  intro v
  rw [MeasurableSpace.measurableSet_iInf]
  intro hv
  exact h v hv

/-- The first time after `s` at which the process `X` deviates from `X s` by more than `ε`
(as `WithTop ℝ`; `⊤` if that never happens). -/
noncomputable def crossTime (X : ℝ → Ω → ℝ) (s ε : ℝ) (ω : Ω) : WithTop ℝ :=
  haveI := Classical.dec
  if _h : {t : ℝ | s < t ∧ ε < |X t ω - X s ω|}.Nonempty
    then (↑(sInf {t : ℝ | s < t ∧ ε < |X t ω - X s ω|}) : WithTop ℝ) else ⊤

/-
Right-continuous characterization of `{crossTime ≤ t}` by a countable (rational)
condition.
-/
theorem crossTime_le_iff (X : ℝ → Ω → ℝ) (s ε : ℝ) (ω : Ω)
    (hrc : ∀ t, ContinuousWithinAt (fun r => X r ω) (Set.Ici t) t) (t : ℝ) :
    crossTime X s ε ω ≤ (t : WithTop ℝ) ↔
      ∀ u : ℚ, t < (u:ℝ) → ∃ q : ℚ, s < (q:ℝ) ∧ (q:ℝ) < (u:ℝ) ∧ ε < |X q ω - X s ω| := by
  constructor <;> intro h;
  · intro u hu; by_cases h_nonempty : {t : ℝ | s < t ∧ ε < |X t ω - X s ω|}.Nonempty <;> simp_all +decide [ crossTime ] ;
    obtain ⟨q, hq⟩ : ∃ q : ℝ, s < q ∧ q < u ∧ ε < |X q ω - X s ω| := by
      exact Exists.elim ( exists_lt_of_csInf_lt h_nonempty ( lt_of_le_of_lt h hu ) ) fun q hq => ⟨ q, hq.1.1, hq.2, hq.1.2 ⟩;
    -- By the right-continuity of $X$ at $q$, there exists a $\delta > 0$ such that for all $r \in [q, q + \delta)$, $\epsilon < |X r \omega - X s \omega|$.
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ r, q ≤ r ∧ r < q + δ → ε < |X r ω - X s ω| := by
      have := Metric.continuousWithinAt_iff.mp ( show ContinuousWithinAt ( fun r => |X r ω - X s ω| ) ( Set.Ici q ) q from ContinuousWithinAt.abs ( ContinuousWithinAt.sub ( hrc q ) continuousWithinAt_const ) );
      exact Exists.elim ( this ( |X q ω - X s ω| - ε ) ( sub_pos.mpr hq.2.2 ) ) fun δ hδ => ⟨ δ, hδ.1, fun r hr => by linarith [ abs_lt.mp ( hδ.2 hr.1 ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) ) ] ⟩;
    rcases exists_rat_btwn ( show q < Min.min ( q + δ ) u by exact lt_min ( by linarith ) ( by linarith ) ) with ⟨ r, hr₁, hr₂ ⟩ ; exact ⟨ r, by exact_mod_cast hr₁.trans_le' hq.1.le, by exact_mod_cast hr₂.trans_le ( min_le_right _ _ ), hδ _ ⟨ by exact_mod_cast hr₁.le, by exact_mod_cast hr₂.trans_le ( min_le_left _ _ ) ⟩ ⟩ ;
  · by_cases h_nonempty : {t : ℝ | s < t ∧ ε < |X t ω - X s ω|}.Nonempty;
    · have h_inf_le_t : sInf {t : ℝ | s < t ∧ ε < |X t ω - X s ω|} ≤ t := by
        refine' le_of_not_gt fun h' => _;
        obtain ⟨ u, hu ⟩ := exists_rat_btwn h';
        obtain ⟨ q, hq₁, hq₂, hq₃ ⟩ := h u hu.1;
        linarith [ show ( q : ℝ ) ≥ sInf { t : ℝ | s < t ∧ ε < |X t ω - X s ω| } by exact csInf_le ⟨ s, fun x hx => hx.1.le ⟩ ⟨ hq₁, hq₃ ⟩ ];
      unfold crossTime; aesop;
    · contrapose! h_nonempty;
      rcases exists_rat_gt t with ⟨ u, hu ⟩ ; rcases h u ( mod_cast hu ) with ⟨ q, hq₁, hq₂, hq₃ ⟩ ; exact ⟨ q, mod_cast hq₁, mod_cast hq₃ ⟩

/-- The set `{crossTime ≤ t}` is measurable with respect to the right-continuous
filtration. -/
theorem measurableSet_crossTime_le (𝓕 : Filtration ℝ m) {X : ℝ → Ω → ℝ}
    (hadapt : ∀ r, Measurable[𝓕 r] (X r))
    (hrc : ∀ ω t, ContinuousWithinAt (fun r => X r ω) (Set.Ici t) t)
    (s ε t : ℝ) :
    MeasurableSet[𝓕.rightCont t] {ω | crossTime X s ε ω ≤ (t : WithTop ℝ)} := by
  apply measurableSet_rightCont_of
  intro v hv
  have h_eq : {ω | crossTime X s ε ω ≤ (t : WithTop ℝ)}
      = ⋂ (u : ℚ), ⋂ (_ : (t:ℝ) < u ∧ (u:ℝ) ≤ v),
          ⋃ (q : ℚ), ⋃ (_ : s < (q:ℝ) ∧ (q:ℝ) < (u:ℝ)),
            {ω | ε < |X q ω - X s ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    rw [crossTime_le_iff X s ε ω (hrc ω) t]
    constructor
    · intro h u hu
      obtain ⟨q, hq₁, hq₂, hq₃⟩ := h u hu.1
      exact ⟨q, ⟨hq₁, hq₂⟩, hq₃⟩
    · intro h u hu
      obtain ⟨w, hw₁, hw₂, hw₃⟩ : ∃ w : ℚ, (t:ℝ) < w ∧ (w:ℝ) < u ∧ (w:ℝ) ≤ v := by
        by_cases huv : (u:ℝ) ≤ v
        · obtain ⟨w, hw⟩ := exists_rat_btwn hu
          exact ⟨w, hw.1, hw.2, hw.2.le.trans huv⟩
        · obtain ⟨w, hw⟩ := exists_rat_btwn hv
          exact ⟨w, hw.1, hw.2.trans_le (le_of_not_ge huv), hw.2.le⟩
      obtain ⟨q, hq, hq₃⟩ := h w ⟨hw₁, hw₃⟩
      exact ⟨q, hq.1, hq.2.trans hw₂, hq₃⟩
  rw [h_eq]
  refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun hu =>
    MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  have hqv : (q:ℝ) ≤ v := le_of_lt (hq.2.trans_le hu.2)
  have hsv : s ≤ v := le_of_lt (hq.1.trans (hq.2.trans_le hu.2))
  have h_meas_q : Measurable[𝓕 v] (X q) := (hadapt q).mono (𝓕.mono hqv) le_rfl
  have h_meas_s : Measurable[𝓕 v] (X s) := (hadapt s).mono (𝓕.mono hsv) le_rfl
  have hsub : Measurable[𝓕 v] (fun ω => X q ω - X s ω) := h_meas_q.sub h_meas_s
  have hopen : MeasurableSet {y : ℝ | ε < |y|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hpre := hsub hopen
  convert hpre using 1

/-- **Tier 2**: the càdlàg oscillation (first-crossing) time after `s` is a stopping time
of the right-continuous augmentation of an adapted, right-continuous process. -/
theorem isStoppingTime_crossTime (𝓕 : Filtration ℝ m) {X : ℝ → Ω → ℝ}
    (hadapt : ∀ r, Measurable[𝓕 r] (X r))
    (hrc : ∀ ω t, ContinuousWithinAt (fun r => X r ω) (Set.Ici t) t)
    (s ε : ℝ) :
    IsStoppingTime 𝓕.rightCont (crossTime X s ε) := by
  intro t
  exact measurableSet_crossTime_le 𝓕 hadapt hrc s ε t

end Tier2

end

end SkorokhodBasic