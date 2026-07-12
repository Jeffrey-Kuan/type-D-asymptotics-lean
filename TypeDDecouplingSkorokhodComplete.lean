/-
# Completeness and Polishness of the Skorokhod space (Skorokhod campaign, 2/5)

This small companion file to `TypeDDecouplingSkorokhodBasic` assembles the `σ∞`
infinite-composition argument (Billingsley Thm 12.2) into the `CompleteSpace` instance and
derives `PolishSpace`.  It is kept separate from `Basic` only so that the (large) final
assembly elaborates against a lighter import surface; all supporting lemmas
(`exists_muSeq`, `exists_rhoSeq`, `exists_skoroUnifLimit`, `TimeChange.exists_limit`,
`logSlopeNorm_comp_tail`, `logSlopeNorm_rhoInf_tail`, `TimeChange.slope_bounds`) live in
`Basic`.
-/
import Mathlib
import TypeDDecouplingSkorokhodBasic

set_option maxHeartbeats 2000000

open scoped Topology BigOperators
open Filter Set

namespace SkorokhodBasic

noncomputable section

/-
Elementary: `exp t - 1 ≤ 2 t` on `[0,1]` (convexity chord bound; `exp 1 - 1 < 2`).
-/
theorem exp_sub_one_le_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t - 1 ≤ 2 * t := by
  -- Use the convexity of exp on [0,1]: write t = (1-t)•0 + t•1. By convexOn_exp (ConvexOn ℝ univ exp), exp t = exp ((1-t)•0 + t•1) ≤ (1-t)•exp 0 + t•exp 1 = (1-t)*1 + t*exp 1 = 1 + t*(exp 1 - 1).
  have convex_bound : Real.exp t ≤ 1 + t * (Real.exp 1 - 1) := by
    have h_convex : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := by
      exact convexOn_exp;
    convert h_convex.2 ( Set.mem_univ 0 ) ( Set.mem_univ 1 ) ( by linarith : 0 ≤ 1 - t ) ( by linarith : 0 ≤ t ) ( by linarith ) using 1 <;> norm_num ; ring;
  have := Real.exp_one_lt_d9 ; norm_num at this ; nlinarith

/-
**Completeness** of the Skorokhod space (Billingsley Thm 12.2): every rapidly-Cauchy
sequence converges.  This is the `σ∞` infinite-composition argument.
-/
theorem exists_limit_of_rapid (u : ℕ → Skoro)
    (hu : ∀ k, dist (u k) (u (k + 1)) < (1/2:ℝ)^k) :
    ∃ f : Skoro, Tendsto u atTop (𝓝 f) := by
  -- Let's obtain the sequences of time changes and apply them to our rapidly-Cauchy sequence.
  obtain ⟨μ, hμ⟩ := exists_muSeq u (fun k => by simpa only [dist_eq_dCirc] using hu k)
  obtain ⟨ρ, hρ⟩ := exists_rhoSeq μ (fun k => (hμ k).1) (fun k => (hμ k).2.1);
  obtain ⟨rhoInf, hrhoInf⟩ : ∃ rhoInf : TimeChange, FiniteNorm rhoInf ∧ (∀ x, x ∈ Set.Icc (0:ℝ) 1 → Tendsto (fun k => (ρ k).toFun x) atTop (𝓝 (rhoInf.toFun x))) ∧ ∀ k, logSlopeNorm (rhoInf.comp (ρ k).symm) ≤ 2 * (1/2:ℝ)^k := by
    have h_cauchy : ∀ x, x ∈ Set.Icc (0:ℝ) 1 → CauchySeq (fun k => (ρ k).toFun x) := by
      intro x hx
      have h_dist : ∀ k, |(ρ k).toFun x - (ρ (k + 1)).toFun x| ≤ Real.exp ((1 / 2 : ℝ) ^ k) - 1 := by
        intro k
        have h_dist : |(ρ k).toFun x - (μ k).symm.toFun ((ρ k).toFun x)| ≤ Real.exp (logSlopeNorm (μ k)) - 1 := by
          convert timeChange_dist_id_le ( μ k |> TimeChange.symm ) ( finiteNorm_symm _ ( hμ k |>.1 ) ) ( ρ k |> TimeChange.mapsTo' <| hx ) using 1;
          · rw [ abs_sub_comm ];
          · rw [ logSlopeNorm_symm _ ( hμ k |>.1 ) ];
        exact hρ.2.2.1 k x ▸ h_dist.trans ( sub_le_sub_right ( Real.exp_le_exp.mpr ( le_of_lt ( hμ k |>.2.1 ) ) ) _ );
      have h_dist : ∀ k, |(ρ k).toFun x - (ρ (k + 1)).toFun x| ≤ 2 * (1 / 2 : ℝ) ^ k := by
        exact fun k => le_trans ( h_dist k ) ( by have := exp_sub_one_le_two_mul ( show 0 ≤ ( 1 / 2 : ℝ ) ^ k by positivity ) ( show ( 1 / 2 : ℝ ) ^ k ≤ 1 by exact pow_le_one₀ ( by positivity ) ( by norm_num ) ) ; linarith );
      exact cauchySeq_of_le_geometric _ _ ( by norm_num ) h_dist;
    have := TimeChange.exists_limit ρ 2 ( by norm_num ) hρ.1 ( fun k => hρ.2.2.2 k ) ( fun x hx => by
      exact cauchySeq_tendsto_of_complete ( h_cauchy x hx ) )
    generalize_proofs at *;
    obtain ⟨ rlim, hrlim₁, hrlim₂, hrlim₃ ⟩ := this; use rlim; exact ⟨ hrlim₁, hrlim₃, fun k => by simpa using logSlopeNorm_rhoInf_tail μ ρ rlim ( fun j => ( hμ j |>.1 ) ) ( fun j => ( hμ j |>.2.1 ) ) ( fun k => ( hρ.1 k ) ) ( fun k x => ( hρ.2.2.1 k x ) ) ( fun x hx => hrlim₃ x hx ) k ⟩ ;
  obtain ⟨h, hHcauchy⟩ : ∃ h : ℕ → Skoro, (∀ k, supDiff (h (k + 1)).toFun (h k).toFun ≤ (1/2:ℝ)^k) ∧ (∀ k, h k = (u k).compTimeChange (ρ k)) := by
    refine' ⟨ _, _, fun k => rfl ⟩;
    intro k
    have h_supDiff : ∀ x ∈ Set.Icc (0:ℝ) 1, |((u (k + 1)).toFun ((ρ (k + 1)).toFun x)) - ((u k).toFun ((ρ k).toFun x))| ≤ supDiff (fun t => (u k).toFun ((μ k).toFun t)) (u (k + 1)).toFun := by
      intro x hx
      have h_supDiff : |((u (k + 1)).toFun ((μ k).symm.toFun ((ρ k).toFun x))) - ((u k).toFun ((μ k).toFun ((μ k).symm.toFun ((ρ k).toFun x))))| ≤ supDiff (fun t => (u k).toFun ((μ k).toFun t)) (u (k + 1)).toFun := by
        apply le_csSup;
        · apply Skoro.bddAbove_comp_supDiffSet;
        · use (μ k).symm.toFun ((ρ k).toFun x);
          exact ⟨ by exact (μ k).symmFun_mem_Icc ( (ρ k).mapsTo' hx ), by rw [ abs_sub_comm ] ⟩;
      grind +suggestions;
    refine' csSup_le _ _;
    · exact ⟨ _, ⟨ 0, by norm_num, rfl ⟩ ⟩;
    · rintro _ ⟨ x, hx, rfl ⟩ ; exact le_trans ( h_supDiff x hx ) ( le_of_lt ( hμ k |>.2.2 ) ) ;
  obtain ⟨hinf, hHconv⟩ := exists_skoroUnifLimit h hHcauchy.1
  use hinf.compTimeChange rhoInf.symm
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h_dist : ∀ k, dist (u k) (hinf.compTimeChange rhoInf.symm) ≤ max (2 * (1 / 2 : ℝ) ^ k) (supDiff (h k).toFun hinf.toFun) := by
    intro k
    have h_dist_k : dist (u k) (hinf.compTimeChange rhoInf.symm) ≤ max (logSlopeNorm (rhoInf.comp (ρ k).symm)) (supDiff (fun x => (hinf.compTimeChange rhoInf.symm).toFun ((rhoInf.comp (ρ k).symm).toFun x)) (u k).toFun) := by
      convert csInf_le _ _ using 1;
      · exact dCircSet_bddBelow _ _;
      · use (rhoInf.comp (ρ k).symm).symm;
        constructor;
        · exact finiteNorm_symm _ ( finiteNorm_comp _ _ hrhoInf.1 ( finiteNorm_symm _ ( hρ.1 k ) ) );
        · rw [ logSlopeNorm_symm ];
          · rw [ supDiff_comp_symm ];
          · exact finiteNorm_comp _ _ hrhoInf.1 ( finiteNorm_symm _ ( hρ.1 k ) );
    refine le_trans h_dist_k <| max_le_max ?_ ?_;
    · exact hrhoInf.2.2 k;
    · refine' csSup_le _ _ <;> norm_num [ hHcauchy.2 ];
      · exact ⟨ _, ⟨ 0, by norm_num, rfl ⟩ ⟩;
      · rintro _ ⟨ x, hx, rfl ⟩ ; simp +decide [ Skoro.compTimeChange ] ;
        convert le_csSup _ _ using 1;
        · convert Skoro.bddAbove_comp_supDiffSet ( u k ) hinf ( ρ k ) using 1;
        · use (ρ k).symmFun x;
          simp +decide [ abs_sub_comm ];
          grind +suggestions
  have hB0 : Filter.Tendsto (fun k => max (2 * (1 / 2 : ℝ) ^ k) (supDiff (h k).toFun hinf.toFun)) atTop (𝓝 0) := by
    exact le_trans ( Filter.Tendsto.max ( tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by norm_num ) ( by norm_num ) ) ) hHconv ) ( by norm_num )
  exact squeeze_zero (fun _ => dist_nonneg) h_dist hB0

/-- **Completeness** of the Skorokhod space (Billingsley Thm 12.2). -/
instance : CompleteSpace Skoro :=
  Metric.complete_of_convergent_controlled_sequences (fun n => (1/2:ℝ)^n)
    (fun n => by positivity)
    (fun u hu => exists_limit_of_rapid u (fun k => hu k k (k + 1) le_rfl (Nat.le_succ k)))

/-- Second countability follows from separability of the metric space. -/
instance : SecondCountableTopology Skoro := UniformSpace.secondCountable_of_separable Skoro

/-- The `PolishSpace` instance: complete + separable (second countable) metric. -/
instance : PolishSpace Skoro := inferInstance

end

end SkorokhodBasic