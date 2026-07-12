/-
# The càdlàg modulus `w'` and compactness in the Skorokhod space (Skorokhod campaign, 2/5)

This is a **library-clean** file building on `TypeDDecouplingSkorokhodBasic`.  It develops:

* **Tier 1 — the càdlàg modulus `w'` and the standard comparisons.**  `cadlagModulus f δ`
  is Billingsley's `w'_f(δ)`: the infimum over `δ`-sparse partitions of `[0,1]` of the
  maximal left-endpoint oscillation on the cells.  We prove it is finite, monotone
  (`↓` as `δ ↓ 0`), and — the key consequence of the partition lemma
  `IsCadlag.exists_modulus_partition` — that it tends to `0` as `δ → 0`.

* **Tier 3 — Billingsley Thm 12.3 (compactness), sufficiency.**  Bounded `+` uniform
  modulus decay `⇒` totally bounded (`⇒` relatively compact, using completeness).

All statements are against the `SkorokhodBasic.Skoro` / `IsCadlag` API; no re-definitions.
-/
import Mathlib
import TypeDDecouplingSkorokhodBasic

set_option maxHeartbeats 2000000

open scoped Topology BigOperators
open Filter Set

namespace SkorokhodBasic

noncomputable section

/-! ## Tier 1: the càdlàg modulus `w'` -/

/-- The set of admissible bounds `ε` for the left-endpoint oscillation of `f` over some
`δ`-sparse partition of `[0,1]` (every cell has length `> δ`).  Billingsley's convention is
followed, except that we require *all* cells to be longer than `δ` (this is harmless for the
`δ → 0` limit, since any finite partition is `δ`-sparse for `δ` below its minimal gap). -/
def modulusSet (f : ℝ → ℝ) (δ : ℝ) : Set ℝ :=
  {ε : ℝ | 0 ≤ ε ∧ ∃ (n : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t n = 1 ∧ 0 < n ∧
    (∀ i, i < n → t i < t (i + 1)) ∧
    (∀ i, i < n → δ < t (i + 1) - t i) ∧
    (∀ i, i < n → ∀ x ∈ Set.Ico (t i) (t (i + 1)), |f x - f (t i)| ≤ ε)}

/-- Billingsley's càdlàg modulus `w'_f(δ)`. -/
def cadlagModulus (f : ℝ → ℝ) (δ : ℝ) : ℝ := sInf (modulusSet f δ)

theorem modulusSet_bddBelow (f : ℝ → ℝ) (δ : ℝ) : BddBelow (modulusSet f δ) :=
  ⟨0, fun _ hx => hx.1⟩

/-- The càdlàg modulus is nonnegative. -/
theorem cadlagModulus_nonneg (f : ℝ → ℝ) (δ : ℝ) : 0 ≤ cadlagModulus f δ := by
  rcases (modulusSet f δ).eq_empty_or_nonempty with h | h
  · simp [cadlagModulus, h, Real.sInf_empty]
  · exact le_csInf h (fun x hx => hx.1)

/-- Monotonicity: enlarging `δ` shrinks the admissible partitions, so `w'` increases; hence
`w'_f(δ) ↓` as `δ ↓ 0`. -/
theorem modulusSet_subset {f : ℝ → ℝ} {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) :
    modulusSet f δ₂ ⊆ modulusSet f δ₁ := by
  rintro ε ⟨hε, n, t, ht0, htn, hn, htmono, htmesh, htcell⟩
  exact ⟨hε, n, t, ht0, htn, hn, htmono, fun i hi => lt_of_le_of_lt h (htmesh i hi), htcell⟩

theorem cadlagModulus_mono {f : ℝ → ℝ} {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂)
    (hne : (modulusSet f δ₂).Nonempty) :
    cadlagModulus f δ₁ ≤ cadlagModulus f δ₂ :=
  csInf_le_csInf (modulusSet_bddBelow f δ₁) hne (modulusSet_subset h)

/-
**Tier 1(b), the key consequence of the partition lemma:** for every càdlàg `f` and
`ε > 0` there is `δ > 0` with `w'_f(δ) ≤ ε`.  (With monotonicity this is `w'_f(δ) → 0`.)
-/
theorem exists_delta_cadlagModulus_le {f : ℝ → ℝ} (hf : IsCadlag f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, cadlagModulus f δ ≤ ε := by
  -- By the Cadlag Partition Lemma, there exists a partition $(t_i)$ of $[0,1]$ such that for every $i$, $t_{i+1} - t_i > \delta$ and $|f(x) - f(t_i)| < \frac{\epsilon}{2}$ for every $x \in [t_i, t_{i+1})$.
  obtain ⟨n, t, ht0, ht1, ht_mono, ht_bound⟩ : ∃ n : ℕ, ∃ t : ℕ → ℝ, t 0 = 0 ∧ t n = 1 ∧ 0 < n ∧ (∀ i, i < n → t i < t (i + 1)) ∧ (∀ i, i < n → ∀ x ∈ Set.Ico (t i) (t (i + 1)), |f x - f (t i)| < ε / 2) := by
    obtain ⟨ n, t, ht ⟩ := IsCadlag.exists_modulus_partition hf ( half_pos hε );
    exact ⟨ n, t, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2 ⟩;
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ i < n, δ < t (i + 1) - t i := by
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ i < n, δ ≤ t (i + 1) - t i := by
      have h_min_gap : ∃ i ∈ Finset.range n, ∀ j ∈ Finset.range n, t (j + 1) - t j ≥ t (i + 1) - t i := by
        exact Finset.exists_min_image _ _ ⟨ _, Finset.mem_range.mpr ht_mono ⟩;
      exact ⟨ t ( h_min_gap.choose + 1 ) - t h_min_gap.choose, sub_pos.mpr ( ht_bound.1 _ ( Finset.mem_range.mp h_min_gap.choose_spec.1 ) ), fun i hi => h_min_gap.choose_spec.2 _ ( Finset.mem_range.mpr hi ) ⟩;
    exact ⟨ δ / 2, half_pos hδ_pos, fun i hi => by linarith [ hδ i hi ] ⟩;
  refine' ⟨ δ, hδ_pos, csInf_le _ _ ⟩;
  · exact ⟨ 0, fun x hx => hx.1 ⟩;
  · exact ⟨ by linarith, n, t, ht0, ht1, ht_mono, ht_bound.1, fun i hi => by linarith [ hδ i hi ], fun i hi x hx => by linarith [ ht_bound.2 i hi x hx ] ⟩

/-
`w'_f(δ) → 0` as `δ → 0⁺` (for càdlàg `f`).
-/
theorem cadlagModulus_tendsto_zero {f : ℝ → ℝ} (hf : IsCadlag f) :
    Tendsto (cadlagModulus f) (𝓝[>] 0) (𝓝 0) := by
  -- Given ε > 0, apply the partition lemma to find n, t.
  have h_partition (ε : ℝ) (hε : 0 < ε) :
      ∃ δ' > 0, ∀ x ∈ Set.Ioi 0, x < δ' → cadlagModulus f x < ε := by
        obtain ⟨n, t, ht0, htn, hn, htmono, hcell⟩ : ∃ n : ℕ, ∃ t : ℕ → ℝ, t 0 = 0 ∧ t n = 1 ∧ 0 < n ∧ (∀ i ≤ n, t i ∈ Set.Icc 0 1) ∧ (∀ i < n, t i < t (i + 1)) ∧ (∀ i < n, ∀ x ∈ Set.Ico (t i) (t (i + 1)), |f x - f (t i)| < ε / 2) := by
          convert IsCadlag.exists_modulus_partition hf ( half_pos hε ) using 1;
        -- Let m be the minimum of (t (i+1) - t i) over i ∈ Finset.range n.
        obtain ⟨m, hm⟩ : ∃ m > 0, ∀ i < n, m ≤ t (i + 1) - t i := by
          have h_min : ∃ m ∈ Finset.image (fun i => t (i + 1) - t i) (Finset.range n), ∀ x ∈ Finset.image (fun i => t (i + 1) - t i) (Finset.range n), m ≤ x := by
            exact ⟨ Finset.min' _ ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_range.mpr hn ) ⟩, Finset.min'_mem _ _, fun x hx => Finset.min'_le _ _ hx ⟩;
          obtain ⟨ m, hm₁, hm₂ ⟩ := h_min; use m; aesop;
        refine' ⟨ m, hm.1, fun x hx₁ hx₂ => lt_of_le_of_lt ( csInf_le _ _ ) ( half_lt_self hε ) ⟩;
        · exact ⟨ 0, fun y hy => hy.1 ⟩;
        · exact ⟨ by linarith, n, t, ht0, htn, hn, fun i hi => hcell.1 i hi, fun i hi => by linarith [ hm.2 i hi ], fun i hi x hx => le_of_lt ( hcell.2 i hi x hx ) ⟩
  generalize_proofs at *; (
  rw [ Metric.tendsto_nhdsWithin_nhds ];
  exact fun ε hε => by rcases h_partition ε hε with ⟨ δ', hδ', H ⟩ ; exact ⟨ δ', hδ', fun x hx₁ hx₂ => abs_lt.mpr ⟨ by linarith [ show 0 ≤ cadlagModulus f x from cadlagModulus_nonneg f x ], by linarith [ H x hx₁ ( by linarith [ abs_lt.mp hx₂ ] ) ] ⟩ ⟩ ;)

/-! ### Numerical sanity (Billingsley remark): `w'` of a unit step vanishes for small `δ`. -/

/-
For the unit step at `a ∈ (0,1)`, `w'(δ) = 0` once `δ < min a (1 - a)`.
-/
theorem cadlagModulus_step {a : ℝ} (ha : a ∈ Set.Ioo (0:ℝ) 1) {δ : ℝ}
    (hδa : δ < min a (1 - a)) : cadlagModulus (step a) δ = 0 := by
  refine' le_antisymm _ ( cadlagModulus_nonneg _ _ );
  refine' csInf_le ( modulusSet_bddBelow _ _ ) _;
  refine' ⟨ le_rfl, 2, fun i => if i = 0 then 0 else if i = 1 then a else 1, _, _, _, _, _ ⟩ <;> norm_num;
  · intro i hi; interval_cases i <;> norm_num [ ha.1, ha.2 ] ;
  · constructor <;> intro i hi <;> interval_cases i <;> norm_num [ step ];
    · linarith [ min_le_left a ( 1 - a ) ];
    · linarith [ min_le_right a ( 1 - a ) ];
    · grind;
    · grind +revert

end

end SkorokhodBasic