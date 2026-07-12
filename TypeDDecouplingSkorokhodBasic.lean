/-
# The Skorokhod space `D([0,1], ℝ)` with the `J₁` topology (Skorokhod campaign, 1/5)

This is a **library-clean** file: it imports only Mathlib and no project files, and
is meant to become load-bearing API for the later Skorokhod campaign tasks
(compactness, tightness/Aldous, Polish targets, Mitoma).

## Design decisions (documented per the brief)

* **`T = 1`.**  We fix the time horizon to `[0,1]` (sanctioned fallback (i) of the
  brief).  This removes the need to thread a parameter `T` through every
  definition while `[0,1]` fights the various Mathlib interval lemmas; a general
  `T` version is a mechanical rescaling of everything here.

* **Domain encoding: `ℝ → ℝ` with flat extension.**  A càdlàg path is modelled as
  an honest function `ℝ → ℝ` (`toFun`) that is càdlàg on `[0,1]` and *flat* outside:
  constant `= toFun 0` on `(-∞,0]` and constant `= toFun 1` on `[1,∞)`.  This keeps
  the ambient topology on the *source* the usual topology of `ℝ` (so
  `ContinuousWithinAt`/`Tendsto` lemmas apply directly, avoiding subtype-order-topology
  friction) while still giving genuine **equality on the nose** from `d° = 0`: two
  càdlàg paths agreeing on `[0,1]` agree everywhere by flatness, hence are equal.
  Thus the metric space is a genuine `MetricSpace` (no quotient), as the brief asks.

* **Boundedness as a field.**  `Skoro` additionally carries a boundedness witness
  `bdd'`.  Every càdlàg function on the compact `[0,1]` is automatically bounded, so
  this does not shrink the class; carrying it makes the sup in the metric a genuine
  real number *without* first formalizing the compactness–boundedness theorem.

* **Time changes: `ℝ → ℝ` structure `TimeChange`.**  A time change is a structure
  bundling `toFun : ℝ → ℝ` that on `[0,1]` is a strictly monotone continuous
  bijection fixing the endpoints, and is flat outside `[0,1]`.  The **log-slope
  norm** `logSlopeNorm` is the `sSup` of `|log ((λ t - λ s)/(t - s))|` over
  `0 ≤ s < t ≤ 1`; `FiniteNorm λ` records that this set is bounded above.  We do
  not install a literal `Group` instance (equality of time changes is not needed
  for the metric); instead we provide composition `TimeChange.comp` and the inverse
  `TimeChange.symm`, and prove the two norm facts the brief requests
  (`logSlopeNorm_symm`, `logSlopeNorm_comp_le`).

* **The metric `d°` (`dCirc`).**  `dCirc f g = sInf` over finite-norm time changes
  `λ` of `max (logSlopeNorm λ) (supDiff (f ∘ λ) g)`, where `supDiff` is the sup over
  `t ∈ [0,1]` of `|·|`.

## Tier coverage (this file)

* **Tier 0 — COMPLETE.**  `IsCadlag`, the space `Skoro`, `TimeChange` with `id`, `comp`,
  `symm` (inverse via `Function.invFunOn`, proved strictly monotone, continuous, a genuine
  two-sided inverse on `[0,1]`), `slopeLog`/`logSlopeNorm`/`FiniteNorm`, and the group facts
  `logSlopeNorm_symm` (`‖λ⁻¹‖° = ‖λ‖°`) and `logSlopeNorm_comp_le`
  (`‖λ∘μ‖° ≤ ‖λ‖° + ‖μ‖°`), plus `finiteNorm_*` and `timeChange_dist_id_le`
  (`|λ t - t| ≤ exp ‖λ‖° - 1`).
* **Tier 1 — COMPLETE.**  `IsCadlag.countable_discontinuities` (standalone), `supDiff`/`dCirc`,
  and a genuine `MetricSpace Skoro` instance: `dCirc_self`, `dCirc_comm`, `dCirc_triangle`,
  and the identity of indiscernibles `dCirc_eq_zero` (via the sequence extraction,
  agreement at continuity points/endpoints, and density of continuity points).
* **Tier 2 — RESIDUAL.**  `isCadlag_of_tendstoUniformly` (uniform limits of càdlàg are
  càdlàg) and `isCadlag_comp_timeChange`/`Skoro.compTimeChange` are proved; `CompleteSpace`
  is a documented residual (see its docstring — the `σ∞` infinite-composition limit).
* **Tier 3 — (a,b) RESIDUAL, (c) COMPLETE.**  Convergence API is complete:
  `tendsto_iff_exists_timeChanges` (both directions of the `λ`-characterization),
  `tendsto_of_tendstoUniformly` (uniform ⇒ `J₁`), `continuousAt_eval` (evaluation continuity
  at continuity points), `dCirc_le_supDiff`, `const`, `dCirc_const`, and the sanity lemma
  `isCadlag_step`.  `SecondCountableTopology` and `PolishSpace` are wired to be **derived**
  from `SeparableSpace` + `CompleteSpace`.  The modulus/partition lemma, the
  partition-approximation, and `SeparableSpace` are documented residuals.

## Design decisions found while formalizing (Billingsley-gap notes)

* The identity-of-indiscernibles argument needs `f = g` at *all* points of `[0,1]`, not only
  continuity points: the endpoints are handled directly (time changes fix `0` and `1`), and
  interior points by right-density of continuity points plus right-continuity of both `f`
  and `g` — the countability of the discontinuity set is genuinely required here.
* Boundedness of càdlàg paths on `[0,1]` is carried as a field of `Skoro` rather than derived,
  so the sup in the metric is a real number without first formalizing compactness–boundedness.
-/
import Mathlib

set_option maxHeartbeats 2000000

open scoped Topology BigOperators
open Filter Set

namespace SkorokhodBasic

noncomputable section

/-! ## Tier 0: càdlàg predicate, the space `Skoro`, time changes, log-slope norm -/

/-- A function `f : ℝ → ℝ` is càdlàg on `[0,1]`: right-continuous on `[0,1)` and with
left limits on `(0,1]`. -/
def IsCadlag (f : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Ico (0:ℝ) 1, ContinuousWithinAt f (Set.Ici t) t) ∧
  (∀ t ∈ Set.Ioc (0:ℝ) 1, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L))

/-- The Skorokhod space `D([0,1], ℝ)`: càdlàg paths, bounded on `[0,1]`, flat outside. -/
structure Skoro where
  /-- The underlying function on all of `ℝ`. -/
  toFun : ℝ → ℝ
  /-- `toFun` is càdlàg on `[0,1]`. -/
  cadlag' : IsCadlag toFun
  /-- `toFun` is bounded on `[0,1]` (automatic for càdlàg; carried for convenience). -/
  bdd' : ∃ C : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 1, |toFun t| ≤ C
  /-- Flat on `(-∞, 0]`. -/
  flatL : ∀ t : ℝ, t ≤ 0 → toFun t = toFun 0
  /-- Flat on `[1, ∞)`. -/
  flatR : ∀ t : ℝ, 1 ≤ t → toFun t = toFun 1

namespace Skoro

instance : CoeFun Skoro (fun _ => ℝ → ℝ) := ⟨Skoro.toFun⟩

@[simp] theorem coe_mk (f h1 h2 h3 h4) : ((⟨f, h1, h2, h3, h4⟩ : Skoro) : ℝ → ℝ) = f := rfl

theorem coe_injective : Function.Injective (Skoro.toFun) := by
  intro f g h; cases f; cases g; simp only [Skoro.mk.injEq]; simpa using h

/-- Two càdlàg paths agreeing on `[0,1]` are equal (uses flatness). -/
theorem ext_on_Icc {f g : Skoro} (h : ∀ t ∈ Set.Icc (0:ℝ) 1, f t = g t) : f = g := by
  apply coe_injective
  funext t
  rcases le_or_gt t 0 with h0 | h0
  · rw [f.flatL t h0, g.flatL t h0]; exact h 0 ⟨le_refl 0, by norm_num⟩
  · rcases le_or_gt t 1 with h1 | h1
    · exact h t ⟨le_of_lt h0, h1⟩
    · rw [f.flatR t (le_of_lt h1), g.flatR t (le_of_lt h1)]
      exact h 1 ⟨by norm_num, le_refl 1⟩

end Skoro

/-! ### Time changes and the log-slope norm -/

/-- A time change of `[0,1]`: strictly increasing continuous bijection fixing the
endpoints, flat outside `[0,1]`. -/
structure TimeChange where
  /-- The underlying function on all of `ℝ`. -/
  toFun : ℝ → ℝ
  map_zero' : toFun 0 = 0
  map_one' : toFun 1 = 1
  strictMonoOn' : StrictMonoOn toFun (Set.Icc 0 1)
  continuousOn' : ContinuousOn toFun (Set.Icc 0 1)
  mapsTo' : Set.MapsTo toFun (Set.Icc 0 1) (Set.Icc 0 1)
  flatL : ∀ t : ℝ, t ≤ 0 → toFun t = 0
  flatR : ∀ t : ℝ, 1 ≤ t → toFun t = 1

namespace TimeChange

instance : CoeFun TimeChange (fun _ => ℝ → ℝ) := ⟨TimeChange.toFun⟩

@[simp] theorem map_zero (l : TimeChange) : l 0 = 0 := l.map_zero'
@[simp] theorem map_one (l : TimeChange) : l 1 = 1 := l.map_one'

/-- Every time change maps `[0,1]` into `[0,1]`. -/
theorem mapsTo (l : TimeChange) : Set.MapsTo l (Set.Icc 0 1) (Set.Icc 0 1) := l.mapsTo'

/-
Time changes are surjective from `[0,1]` onto `[0,1]` (intermediate value).
-/
theorem surjOn (l : TimeChange) : Set.SurjOn l (Set.Icc 0 1) (Set.Icc 0 1) := by
  intro y hy; have := intermediate_value_Icc ( by norm_num : ( 0 : ℝ ) ≤ 1 ) l.continuousOn'; simp_all +decide [ Set.subset_def ] ;

/-- Time changes are injective on `[0,1]`. -/
theorem injOn (l : TimeChange) : Set.InjOn l (Set.Icc 0 1) :=
  l.strictMonoOn'.injOn

/-- The identity time change (clamped to be flat outside `[0,1]`). -/
def id : TimeChange where
  toFun := fun t => max 0 (min 1 t)
  map_zero' := by norm_num
  map_one' := by norm_num
  strictMonoOn' := by
    intro a ha b hb hab
    simp only [Set.mem_Icc] at ha hb
    have : min 1 a = a := min_eq_right ha.2
    have : min 1 b = b := min_eq_right hb.2
    simp only [min_eq_right ha.2, min_eq_right hb.2, max_eq_right ha.1, max_eq_right hb.1]
    exact hab
  continuousOn' := (continuous_const.max (continuous_const.min continuous_id)).continuousOn
  mapsTo' := by
    intro t ht
    simp only [Set.mem_Icc] at ht ⊢
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  flatL := by
    intro t ht
    have : min 1 t = t := min_eq_right (le_trans ht (by norm_num))
    simp [this, max_eq_left ht]
  flatR := by
    intro t ht
    simp [min_eq_left ht]

/-- Composition of time changes: `(l.comp m) t = l (m t)`. -/
def comp (l m : TimeChange) : TimeChange where
  toFun := fun t => l (m t)
  map_zero' := by simp
  map_one' := by simp
  strictMonoOn' := by
    intro a ha b hb hab
    exact l.strictMonoOn' (m.mapsTo' ha) (m.mapsTo' hb) (m.strictMonoOn' ha hb hab)
  continuousOn' := l.continuousOn'.comp m.continuousOn' m.mapsTo'
  mapsTo' := l.mapsTo'.comp m.mapsTo'
  flatL := by intro t ht; rw [m.flatL t ht, l.map_zero']
  flatR := by intro t ht; rw [m.flatR t ht, l.map_one']

/-- The underlying function of the inverse time change: `Set.invFunOn` on `[0,1]`,
clamped to be flat outside. -/
def symmFun (l : TimeChange) : ℝ → ℝ :=
  fun x => if x ≤ 0 then 0 else if 1 ≤ x then 1 else Function.invFunOn l.toFun (Set.Icc 0 1) x

@[simp] theorem symmFun_zero (l : TimeChange) : symmFun l 0 = 0 := by simp [symmFun]
@[simp] theorem symmFun_one (l : TimeChange) : symmFun l 1 = 1 := by
  simp only [symmFun]; norm_num

theorem symmFun_flatL (l : TimeChange) {t : ℝ} (ht : t ≤ 0) : symmFun l t = 0 := by
  simp [symmFun, ht]
theorem symmFun_flatR (l : TimeChange) {t : ℝ} (ht : 1 ≤ t) : symmFun l t = 1 := by
  have h0 : ¬ t ≤ 0 := by linarith
  simp [symmFun, h0, ht]

/-
`symmFun l` maps `[0,1]` into `[0,1]`.
-/
theorem symmFun_mem_Icc (l : TimeChange) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    symmFun l x ∈ Set.Icc (0:ℝ) 1 := by
  by_cases h0 : x ≤ 0 <;> by_cases h1 : 1 ≤ x <;> simp_all +decide [ TimeChange.symmFun ];
  · split_ifs <;> norm_num;
  · split_ifs <;> norm_num;
    have := l.surjOn; simp_all +decide [ Set.SurjOn ];
    exact Function.invFunOn_mem ( this ⟨ hx.1, hx.2 ⟩ )

/-
Right inverse: `l (symmFun l x) = x` for `x ∈ [0,1]`.
-/
theorem apply_symmFun (l : TimeChange) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    l.toFun (symmFun l x) = x := by
  by_cases h0 : x ≤ 0 <;> by_cases h1 : 1 ≤ x <;> simp_all +decide [ TimeChange.symmFun ];
  · linarith;
  · linarith;
  · norm_num [ show x = 1 by linarith, l.map_one' ];
  · have := l.surjOn; simp_all +decide [ Set.SurjOn ];
    convert Function.invFunOn_eq ( this ⟨ h0.le, h1.le ⟩ ) using 1;
    grobner

/-
Left inverse: `symmFun l (l t) = t` for `t ∈ [0,1]`.
-/
theorem symmFun_apply (l : TimeChange) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    symmFun l (l.toFun t) = t := by
  unfold TimeChange.symmFun;
  split_ifs <;> simp_all +decide [ Set.InjOn ];
  · by_contra h_contra;
    exact absurd ( l.strictMonoOn' ( show 0 ∈ Set.Icc 0 1 by norm_num ) ( show t ∈ Set.Icc 0 1 by constructor <;> linarith ) ( lt_of_le_of_ne ht.1 ( Ne.symm ( by aesop ) ) ) ) ( by linarith [ l.map_zero' ] );
  · by_contra h_contra;
    have := l.strictMonoOn' ( show t ∈ Set.Icc 0 1 from ht ) ( show 1 ∈ Set.Icc 0 1 from by norm_num ) ( lt_of_le_of_ne ht.2 ( Ne.symm h_contra ) ) ; norm_num at this ; linarith [ l.map_one' ] ;
  · rw [ Function.invFunOn ];
    split_ifs with h
    all_goals generalize_proofs at *;
    · have := Classical.choose_spec h;
      exact l.injOn this.1 ht this.2;
    · exact False.elim <| h ⟨ t, ht, rfl ⟩

theorem symmFun_strictMonoOn (l : TimeChange) : StrictMonoOn (symmFun l) (Set.Icc 0 1) := by
  intros a ha b hb hab; have := l.apply_symmFun ha; have := l.apply_symmFun hb; have := l.surjOn; simp_all +decide [ StrictMonoOn ] ;
  by_contra h_contra;
  by_cases h_eq : l.symmFun a = l.symmFun b;
  · grobner;
  · linarith [ l.strictMonoOn' ( show l.symmFun b ∈ Set.Icc 0 1 from l.symmFun_mem_Icc hb ) ( show l.symmFun a ∈ Set.Icc 0 1 from l.symmFun_mem_Icc ha ) ( lt_of_le_of_ne ( le_of_not_gt h_contra ) ( Ne.symm h_eq ) ) ]

theorem symmFun_continuousOn (l : TimeChange) : ContinuousOn (symmFun l) (Set.Icc 0 1) := by
  rw [ Metric.continuousOn_iff ];
  intro b hb ε hε;
  -- Choose δ such that if |a - b| < δ, then |l.symmFun a - l.symmFun b| < ε.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ a ∈ Set.Icc 0 1, |a - b| < δ → l.symmFun a ∈ Set.Ioo (l.symmFun b - ε / 2) (l.symmFun b + ε / 2) := by
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ a ∈ Set.Icc 0 1, |a - b| < δ → l.symmFun a < l.symmFun b + ε / 2 ∧ l.symmFun a > l.symmFun b - ε / 2 := by
      have h_left : ∃ δ₁ > 0, ∀ a ∈ Set.Icc 0 1, |a - b| < δ₁ → l.symmFun a < l.symmFun b + ε / 2 := by
        by_cases h₂ : l.symmFun b + ε / 2 > 1;
        · exact ⟨ 1, by norm_num, fun a ha ha' => by linarith [ show l.symmFun a ≤ 1 from l.symmFun_mem_Icc ha |>.2 ] ⟩;
        · obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ a ∈ Set.Icc 0 1, |a - b| < δ₁ → l.toFun (l.symmFun b + ε / 2) > a := by
            have h_cont : l.toFun (l.symmFun b + ε / 2) > b := by
              have h₃ : l.toFun (l.symmFun b + ε / 2) > l.toFun (l.symmFun b) := by
                apply l.strictMonoOn';
                · exact symmFun_mem_Icc l hb;
                · exact ⟨ add_nonneg ( l.symmFun_mem_Icc hb |>.1 ) ( half_pos hε |> le_of_lt ), le_of_not_gt h₂ ⟩;
                · linarith;
              have := l.apply_symmFun hb; aesop;
            exact ⟨ l.toFun ( l.symmFun b + ε / 2 ) - b, sub_pos.mpr h_cont, fun a ha ha' => by linarith [ abs_lt.mp ha' ] ⟩;
          use δ₁, hδ₁_pos;
          intros a ha hδ₁a
          have h_lt : l.toFun (l.symmFun a) < l.toFun (l.symmFun b + ε / 2) := by
            linarith [ hδ₁ a ha hδ₁a, l.apply_symmFun ha ];
          contrapose! h_lt;
          have h_monotone : StrictMonoOn l.toFun (Set.Icc 0 1) := by
            exact l.strictMonoOn';
          exact h_monotone.le_iff_le ( by constructor <;> linarith [ Set.mem_Icc.mp ( l.symmFun_mem_Icc hb ), Set.mem_Icc.mp ( l.symmFun_mem_Icc ha ) ] ) ( by constructor <;> linarith [ Set.mem_Icc.mp ( l.symmFun_mem_Icc hb ), Set.mem_Icc.mp ( l.symmFun_mem_Icc ha ) ] ) |>.2 h_lt
      have h_right : ∃ δ₂ > 0, ∀ a ∈ Set.Icc 0 1, |a - b| < δ₂ → l.symmFun a > l.symmFun b - ε / 2 := by
        by_cases h₂ : l.symmFun b - ε / 2 < 0;
        · exact ⟨ 1, by norm_num, fun a ha ha' => by linarith [ show 0 ≤ l.symmFun a from by exact le_of_not_gt fun h => by have := l.symmFun_mem_Icc ha; linarith [ this.1 ] ] ⟩;
        · obtain ⟨a, ha⟩ : ∃ a ∈ Set.Icc 0 1, l.symmFun a = l.symmFun b - ε / 2 := by
            have h_surj : Set.SurjOn l.symmFun (Set.Icc 0 1) (Set.Icc 0 1) := by
              intro x hx; use l.toFun x; simp_all +decide [ Set.SurjOn ] ;
              exact ⟨ ⟨ l.mapsTo' hx |>.1, l.mapsTo' hx |>.2 ⟩, l.symmFun_apply hx ⟩;
            exact h_surj ⟨ by linarith, by linarith [ show l.symmFun b ≤ 1 from by
                                                        exact l.symmFun_mem_Icc hb |>.2 ] ⟩;
          by_cases h₂ : a < b;
          · use b - a;
            simp +zetaDelta at *;
            exact ⟨ by linarith, fun x hx₁ hx₂ hx₃ => by linarith [ l.symmFun_strictMonoOn ( show a ∈ Set.Icc 0 1 from ⟨ by linarith, by linarith ⟩ ) ( show x ∈ Set.Icc 0 1 from ⟨ by linarith, by linarith ⟩ ) ( by linarith [ abs_lt.mp hx₃ ] ) ] ⟩;
          · linarith [ l.symmFun_strictMonoOn ( show b ∈ Set.Icc 0 1 from hb ) ( show a ∈ Set.Icc 0 1 from ha.1 ) ( lt_of_le_of_ne ( le_of_not_gt h₂ ) ( Ne.symm <| by rintro rfl; linarith ) ) ]
      exact ⟨ Min.min h_left.choose h_right.choose, lt_min h_left.choose_spec.1 h_right.choose_spec.1, fun a ha ha' => ⟨ h_left.choose_spec.2 a ha ( lt_of_lt_of_le ha' ( min_le_left _ _ ) ), h_right.choose_spec.2 a ha ( lt_of_lt_of_le ha' ( min_le_right _ _ ) ) ⟩ ⟩;
    exact ⟨ δ, hδ_pos, fun a ha ha' => ⟨ hδ a ha ha' |>.2, hδ a ha ha' |>.1 ⟩ ⟩;
  exact ⟨ δ, hδ_pos, fun a ha ha' => abs_lt.mpr ⟨ by linarith [ Set.mem_Ioo.mp ( hδ a ha ha' ) ], by linarith [ Set.mem_Ioo.mp ( hδ a ha ha' ) ] ⟩ ⟩

/-- The inverse time change. -/
def symm (l : TimeChange) : TimeChange where
  toFun := symmFun l
  map_zero' := symmFun_zero l
  map_one' := symmFun_one l
  strictMonoOn' := symmFun_strictMonoOn l
  continuousOn' := symmFun_continuousOn l
  mapsTo' := fun _ hx => symmFun_mem_Icc l hx
  flatL := fun _ ht => symmFun_flatL l ht
  flatR := fun _ ht => symmFun_flatR l ht

@[simp] theorem symm_toFun (l : TimeChange) : (l.symm).toFun = symmFun l := rfl

@[simp] theorem comp_apply (l m : TimeChange) (t : ℝ) : (l.comp m) t = l (m t) := rfl

/-- Left inverse property of `symm` on `[0,1]`. -/
theorem symm_apply_apply (l : TimeChange) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    l.symm (l t) = t := symmFun_apply l ht

/-- Right inverse property of `symm` on `[0,1]`. -/
theorem apply_symm_apply (l : TimeChange) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    l (l.symm t) = t := apply_symmFun l ht

end TimeChange

/-- The (absolute) log-slope of `f` over `[s,t]`. -/
def slopeLog (f : ℝ → ℝ) (s t : ℝ) : ℝ := |Real.log ((f t - f s) / (t - s))|

/-- The set of log-slopes of `f` over subintervals `[s,t] ⊆ [0,1]` with `s < t`. -/
def logSlopeSet (f : ℝ → ℝ) : Set ℝ :=
  {r : ℝ | ∃ s t, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧ r = slopeLog f s t}

/-- The log-slope norm `‖λ‖°` of a time change. -/
def logSlopeNorm (l : TimeChange) : ℝ := sSup (logSlopeSet l.toFun)

/-- `λ` has finite log-slope norm (the defining condition of `Λ°`). -/
def FiniteNorm (l : TimeChange) : Prop := BddAbove (logSlopeSet l.toFun)

theorem logSlopeSet_nonempty (l : TimeChange) : (logSlopeSet l.toFun).Nonempty :=
  ⟨slopeLog l.toFun 0 1, 0, 1, le_refl 0, by norm_num, le_refl 1, rfl⟩

/-- The increment of a time change over a nondegenerate subinterval of `[0,1]` is positive. -/
theorem timeChange_sub_pos (l : TimeChange) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    0 < l.toFun t - l.toFun s := by
  have hs1 : s ≤ 1 := le_of_lt (lt_of_lt_of_le hst ht)
  have hlt : l.toFun s < l.toFun t :=
    l.strictMonoOn' ⟨hs, hs1⟩ ⟨le_of_lt (lt_of_le_of_lt hs hst), ht⟩ hst
  linarith

/-- Every log-slope is nonnegative (it is an absolute value). -/
theorem slopeLog_nonneg (f : ℝ → ℝ) (s t : ℝ) : 0 ≤ slopeLog f s t := abs_nonneg _

/-
The inverse time change has the same log-slope set (hence the same norm).
-/
theorem logSlopeSet_symm (l : TimeChange) : logSlopeSet (l.symm).toFun = logSlopeSet l.toFun := by
  ext; simp [logSlopeSet];
  constructor <;> rintro ⟨ s, hs, t, ht, hst, rfl ⟩;
  · refine' ⟨ l.symmFun s, _, l.symmFun t, _, _, _ ⟩;
    · exact l.symmFun_mem_Icc ⟨ hs, by linarith ⟩ |>.1;
    · exact l.symmFun_strictMonoOn ⟨ hs, by linarith ⟩ ⟨ by linarith, hst ⟩ ht;
    · exact l.symmFun_mem_Icc ⟨ by linarith, by linarith ⟩ |>.2;
    · -- By definition of `slopeLog`, we have:
      simp [slopeLog];
      rw [ TimeChange.apply_symmFun l ( by constructor <;> linarith ), TimeChange.apply_symmFun l ( by constructor <;> linarith ) ];
      rw [ ← abs_neg, ← Real.log_inv, inv_div ];
  · refine' ⟨ l.toFun s, _, l.toFun t, _, _, _ ⟩;
    · have := l.mapsTo' ( show s ∈ Set.Icc 0 1 from ⟨ hs, by linarith ⟩ ) ; aesop;
    · exact l.strictMonoOn' ⟨ hs, by linarith ⟩ ⟨ by linarith, hst ⟩ ht;
    · exact l.mapsTo' ⟨ by linarith, by linarith ⟩ |>.2;
    · unfold slopeLog;
      rw [ TimeChange.symmFun_apply l ( show t ∈ Set.Icc 0 1 from ⟨ by linarith, by linarith ⟩ ), TimeChange.symmFun_apply l ( show s ∈ Set.Icc 0 1 from ⟨ by linarith, by linarith ⟩ ) ];
      rw [ ← abs_neg, ← Real.log_inv, inv_div ]

theorem logSlopeNorm_nonneg (l : TimeChange) (h : FiniteNorm l) : 0 ≤ logSlopeNorm l := by
  apply_rules [ Real.sSup_nonneg ];
  exact fun x hx => hx.choose_spec.choose_spec.2.2.2.symm ▸ slopeLog_nonneg _ _ _

/-
The identity time change has zero log-slope norm.
-/
theorem logSlopeNorm_id : logSlopeNorm TimeChange.id = 0 := by
  unfold logSlopeNorm;
  rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ];
  · exact ⟨ _, 0, 1, by norm_num, by norm_num, by norm_num, rfl ⟩;
  · rintro _ ⟨ s, t, hs, ht, hst, rfl ⟩;
    unfold slopeLog; norm_num [ TimeChange.id ];
    grind;
  · exact fun w hw => ⟨ _, ⟨ 0, 1, by norm_num, by norm_num, by norm_num, rfl ⟩, hw.trans_le <| abs_nonneg _ ⟩

theorem finiteNorm_id : FiniteNorm TimeChange.id := by
  use 0; rintro x ⟨ s, t, hs, ht, hst, rfl ⟩ ; unfold slopeLog; norm_num [ TimeChange.id ] ;
  grind

/-- `‖λ⁻¹‖° = ‖λ‖°` (the brief's inverse-symmetry of the log-slope norm). -/
theorem logSlopeNorm_symm (l : TimeChange) (h : FiniteNorm l) :
    logSlopeNorm l.symm = logSlopeNorm l := by
  unfold logSlopeNorm; rw [logSlopeSet_symm]

theorem finiteNorm_symm (l : TimeChange) (h : FiniteNorm l) : FiniteNorm l.symm := by
  unfold FiniteNorm at *; rwa [logSlopeSet_symm]

/-
`‖λ∘μ‖° ≤ ‖λ‖° + ‖μ‖°` (the brief's subadditivity of the log-slope norm).
-/
theorem logSlopeNorm_comp_le (l m : TimeChange) (hl : FiniteNorm l) (hm : FiniteNorm m) :
    logSlopeNorm (l.comp m) ≤ logSlopeNorm l + logSlopeNorm m := by
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ 0, 1, by norm_num, by norm_num, by norm_num, rfl ⟩ ⟩;
  · rintro _ ⟨ s, t, hs, ht, hst, rfl ⟩;
    -- By definition of $l.comp m$, we have $(l.comp m).toFun x = l.toFun (m.toFun x)$.
    have h_comp : slopeLog (l.comp m).toFun s t ≤ slopeLog l.toFun (m.toFun s) (m.toFun t) + slopeLog m.toFun s t := by
      unfold slopeLog;
      rw [ show ( l.comp m |> TimeChange.toFun ) t = l.toFun ( m.toFun t ) by rfl, show ( l.comp m |> TimeChange.toFun ) s = l.toFun ( m.toFun s ) by rfl, show ( l.toFun ( m.toFun t ) - l.toFun ( m.toFun s ) ) / ( t - s ) = ( ( l.toFun ( m.toFun t ) - l.toFun ( m.toFun s ) ) / ( m.toFun t - m.toFun s ) ) * ( ( m.toFun t - m.toFun s ) / ( t - s ) ) by rw [ div_mul_div_cancel₀ ] ; linarith [ timeChange_sub_pos m hs ht hst ] ];
      rw [ Real.log_mul ];
      · exact abs_add_le (Real.log ((l.toFun (m.toFun t) - l.toFun (m.toFun s)) / (m.toFun t - m.toFun s))) (Real.log ((m.toFun t - m.toFun s) / (t - s)));
      · exact div_ne_zero ( sub_ne_zero_of_ne <| by exact fun h => by have := l.strictMonoOn' ( show m.toFun s ∈ Set.Icc 0 1 from m.mapsTo' ⟨ by linarith, by linarith ⟩ ) ( show m.toFun t ∈ Set.Icc 0 1 from m.mapsTo' ⟨ by linarith, by linarith ⟩ ) ( by linarith [ timeChange_sub_pos m hs ht hst ] ) ; aesop ) ( sub_ne_zero_of_ne <| by exact fun h => by have := timeChange_sub_pos m hs ht hst; aesop );
      · exact div_ne_zero ( sub_ne_zero_of_ne <| ne_of_gt <| m.strictMonoOn' ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ ht ) ( sub_ne_zero_of_ne <| ne_of_gt ht );
    refine' le_trans h_comp ( add_le_add _ _ );
    · refine' le_csSup _ _;
      · exact hl;
      · exact ⟨ m.toFun s, m.toFun t, by linarith [ m.mapsTo' ( show s ∈ Set.Icc 0 1 from ⟨ hs, by linarith ⟩ ) |>.1 ], by linarith [ timeChange_sub_pos m hs ht hst ], by linarith [ m.mapsTo' ( show t ∈ Set.Icc 0 1 from ⟨ by linarith, by linarith ⟩ ) |>.2 ], rfl ⟩;
    · exact le_csSup hm ⟨ s, t, hs, ht, hst, rfl ⟩

theorem finiteNorm_comp (l m : TimeChange) (hl : FiniteNorm l) (hm : FiniteNorm m) :
    FiniteNorm (l.comp m) := by
  obtain ⟨ C₁, hC₁ ⟩ := hl;
  obtain ⟨ C₂, hC₂ ⟩ := hm;
  use C₁ + C₂;
  rintro x ⟨ s, t, hs, ht, hst, rfl ⟩;
  refine' le_trans _ ( add_le_add ( hC₁ ⟨ m.toFun s, m.toFun t, _, _, _, rfl ⟩ ) ( hC₂ ⟨ s, t, hs, ht, hst, rfl ⟩ ) );
  · unfold slopeLog;
    rw [ show ( l.comp m |> TimeChange.toFun ) t = l.toFun ( m.toFun t ) by rfl, show ( l.comp m |> TimeChange.toFun ) s = l.toFun ( m.toFun s ) by rfl, show ( l.toFun ( m.toFun t ) - l.toFun ( m.toFun s ) ) / ( t - s ) = ( ( l.toFun ( m.toFun t ) - l.toFun ( m.toFun s ) ) / ( m.toFun t - m.toFun s ) ) * ( ( m.toFun t - m.toFun s ) / ( t - s ) ) by rw [ div_mul_div_cancel₀ ] ; linarith [ timeChange_sub_pos m hs ht hst ] ];
    rw [ Real.log_mul ];
    · exact abs_add_le (Real.log ((l.toFun (m.toFun t) - l.toFun (m.toFun s)) / (m.toFun t - m.toFun s))) (Real.log ((m.toFun t - m.toFun s) / (t - s)));
    · exact div_ne_zero ( sub_ne_zero_of_ne <| by exact fun h => by have := l.strictMonoOn' ( show m.toFun s ∈ Set.Icc 0 1 from m.mapsTo' ⟨ by linarith, by linarith ⟩ ) ( show m.toFun t ∈ Set.Icc 0 1 from m.mapsTo' ⟨ by linarith, by linarith ⟩ ) ( by linarith [ timeChange_sub_pos m hs ht hst ] ) ; aesop ) ( sub_ne_zero_of_ne <| ne_of_gt <| m.strictMonoOn' ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ ht );
    · exact div_ne_zero ( sub_ne_zero_of_ne <| by exact fun h => by have := m.strictMonoOn' ( show s ∈ Set.Icc 0 1 from ⟨ hs, by linarith ⟩ ) ( show t ∈ Set.Icc 0 1 from ⟨ by linarith, by linarith ⟩ ) ht; aesop ) ( sub_ne_zero_of_ne <| by linarith );
  · have := m.mapsTo' ( show s ∈ Set.Icc 0 1 from ⟨ hs, by linarith ⟩ ) ; aesop;
  · exact m.strictMonoOn' ⟨ hs, by linarith ⟩ ⟨ by linarith, by linarith ⟩ ht;
  · exact m.mapsTo' ⟨ by linarith, by linarith ⟩ |>.2

/-
The log-slope norm controls uniform closeness to the identity:
`|λ t - t| ≤ exp ‖λ‖° - 1` for `t ∈ [0,1]`.  (Recurs; needed for the convergence API
and completeness.)
-/
theorem timeChange_dist_id_le (l : TimeChange) (h : FiniteNorm l) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : |l.toFun t - t| ≤ Real.exp (logSlopeNorm l) - 1 := by
  by_cases h_cases : t = 0 ∨ t = 1;
  · cases h_cases <;> simp +decide [ * ]; all_goals exact logSlopeNorm_nonneg l h;
  · -- Let $r := l.toFun t / t$. Since $t \neq 0$ and $t \neq 1$, we have $0 < r$.
    set r : ℝ := l.toFun t / t
    have hr_pos : 0 < r := by
      exact div_pos ( by linarith [ l.map_zero', l.map_one', timeChange_sub_pos l ( show 0 ≤ 0 by norm_num ) ( show 0 < t by exact lt_of_le_of_ne ht.1 ( Ne.symm <| by tauto ) ) ( show t ≤ 1 by linarith [ ht.2 ] ) ] ) ( lt_of_le_of_ne ht.1 ( Ne.symm <| by tauto ) );
    -- From $|Real.log r| ≤ N$ and $r > 0$, we get $Real.exp (-N) ≤ r ≤ Real.exp N$.
    have hr_bounds : Real.exp (-logSlopeNorm l) ≤ r ∧ r ≤ Real.exp (logSlopeNorm l) := by
      have hr_bounds : |Real.log r| ≤ logSlopeNorm l := by
        refine' le_csSup h _;
        use 0, t;
        simp +zetaDelta at *;
        exact ⟨ lt_of_le_of_ne ht.1 ( Ne.symm h_cases.1 ), ht.2, by unfold slopeLog; norm_num [ l.map_zero' ] ⟩;
      exact ⟨ by rw [ ← Real.exp_log hr_pos ] ; exact Real.exp_le_exp.mpr ( by linarith [ abs_le.mp hr_bounds ] ), by rw [ ← Real.exp_log hr_pos ] ; exact Real.exp_le_exp.mpr ( by linarith [ abs_le.mp hr_bounds ] ) ⟩;
    rw [ abs_le ] ; constructor <;> cases lt_or_gt_of_ne ( mt Or.inl h_cases ) <;> cases lt_or_gt_of_ne ( mt Or.inr h_cases ) <;> nlinarith [ ht.1, ht.2, mul_div_cancel₀ ( l.toFun t ) ( by linarith : t ≠ 0 ), Real.exp_pos ( -logSlopeNorm l ), Real.exp_pos ( logSlopeNorm l ), Real.exp_neg ( logSlopeNorm l ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( logSlopeNorm l ) ) ), Real.add_one_le_exp ( logSlopeNorm l ), Real.add_one_le_exp ( -logSlopeNorm l ) ] ;

/-! ## Tier 1: `d°` is a metric -/

/-
Countability of the discontinuity set of a càdlàg function (standalone; recurs).
-/
theorem IsCadlag.countable_discontinuities {f : ℝ → ℝ} (hf : IsCadlag f) :
    {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ ¬ ContinuousWithinAt f (Set.Icc 0 1) t}.Countable := by
  revert hf;
  intro hf
  have h_finite : ∀ n : ℕ, Set.Finite {t ∈ Set.Icc 0 1 | ∀ δ > 0, ∃ s ∈ Set.Icc 0 1, |s - t| < δ ∧ 1 / (n + 1 : ℝ) ≤ |f s - f t|} := by
    intro n
    by_contra h_inf
    obtain ⟨t_star, ht_star⟩ : ∃ t_star ∈ Set.Icc 0 1, ∀ ε > 0, Set.Infinite {t ∈ Set.Icc 0 1 | |t - t_star| < ε ∧ ∀ δ > 0, ∃ s ∈ Set.Icc 0 1, |s - t| < δ ∧ 1 / (n + 1 : ℝ) ≤ |f s - f t|} := by
      contrapose! h_inf;
      choose! ε hε using h_inf;
      -- Since $[0,1]$ is compact, we can find a finite subcover of the open cover $\{ (t - \epsilon(t), t + \epsilon(t)) \mid t \in [0,1] \}$.
      obtain ⟨t_fin, ht_fin⟩ : ∃ t_fin : Finset ℝ, (∀ t ∈ t_fin, t ∈ Set.Icc 0 1) ∧ (∀ t ∈ Set.Icc 0 1, ∃ t' ∈ t_fin, |t - t'| < ε t') := by
        have h_compact : IsCompact (Set.Icc (0 : ℝ) 1) := by
          exact CompactIccSpace.isCompact_Icc;
        have := h_compact.elim_nhds_subcover;
        exact Exists.elim ( this ( fun x => Metric.ball x ( ε x ) ) fun x hx => Metric.ball_mem_nhds x ( hε x hx |>.1 ) ) fun t ht => ⟨ t, ht.1, fun x hx => by simpa using ht.2 hx ⟩;
      exact Set.Finite.subset ( Set.Finite.biUnion ( Finset.finite_toSet t_fin ) fun t ht => hε t ( ht_fin.1 t ht ) |>.2 ) fun x hx => by rcases ht_fin.2 x hx.1 with ⟨ t', ht', ht'' ⟩ ; aesop;
    -- Since $f$ is càdlàg, it has a right limit $f(t^*)$ at $t^*$ (right continuity, if $t^* < 1$) and a left limit $L$ at $t^*$ (if $t^* > 0).
    obtain ⟨L, hL⟩ : ∃ L, Tendsto f (𝓝[<] t_star) (𝓝 L) ∨ t_star = 0 := by
      by_cases h : t_star = 0 <;> simp_all +decide [ IsCadlag ];
      exact hf.2 t_star ( lt_of_le_of_ne ht_star.1.1 ( Ne.symm h ) ) ht_star.1.2
    obtain ⟨R, hR⟩ : ∃ R, Tendsto f (𝓝[>] t_star) (𝓝 R) ∨ t_star = 1 := by
      by_cases h : t_star = 1 <;> simp_all +decide [ IsCadlag ];
      exact ⟨ _, hf.1 t_star ht_star.1.1 ( lt_of_le_of_ne ht_star.1.2 h ) |> ContinuousWithinAt.tendsto |> Filter.Tendsto.mono_left <| nhdsWithin_mono _ <| Set.Ioi_subset_Ici_self ⟩;
    -- Choose $\eta = \frac{1}{3(n+1)}$ and a two-sided punctured neighborhood of $t^*$ on which $f$ is within $\eta$ of $f(t^*)$ on the right and within $\eta$ of $L$ on the left.
    obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ t ∈ Set.Icc 0 1, t ≠ t_star → |t - t_star| < ε → |f t - if t < t_star then L else R| < 1 / (3 * (n + 1) : ℝ) := by
      have h_eps : ∃ ε > 0, ∀ t ∈ Set.Icc 0 1, t < t_star → |t - t_star| < ε → |f t - L| < 1 / (3 * (n + 1) : ℝ) := by
        by_cases hL_zero : t_star = 0;
        · exact ⟨ 1, by norm_num, by intros; linarith [ Set.mem_Icc.mp ‹_› ] ⟩;
        · have := Metric.tendsto_nhdsWithin_nhds.mp ( hL.resolve_right hL_zero ) ( 1 / ( 3 * ( n + 1 ) ) ) ( by positivity );
          exact ⟨ this.choose, this.choose_spec.1, fun t ht ht' ht'' => this.choose_spec.2 ht' ht'' ⟩;
      have h_eps_right : ∃ ε > 0, ∀ t ∈ Set.Icc 0 1, t > t_star → |t - t_star| < ε → |f t - R| < 1 / (3 * (n + 1) : ℝ) := by
        by_cases h : t_star = 1 <;> simp_all +decide [ Metric.tendsto_nhdsWithin_nhds ];
        · exact ⟨ 1, by norm_num ⟩;
        · exact Exists.elim ( hR ( ( n + 1 : ℝ ) ⁻¹ * 3⁻¹ ) ( by positivity ) ) fun δ hδ => ⟨ δ, hδ.1, fun t ht₁ ht₂ ht₃ ht₄ => hδ.2 ht₃ ht₄ ⟩;
      grind;
    obtain ⟨t₁, ht₁⟩ : ∃ t₁ ∈ Set.Icc 0 1, t₁ ≠ t_star ∧ |t₁ - t_star| < ε ∧ ∀ δ > 0, ∃ s ∈ Set.Icc 0 1, |s - t₁| < δ ∧ 1 / (n + 1 : ℝ) ≤ |f s - f t₁| := by
      obtain ⟨ t₁, ht₁ ⟩ := Set.Infinite.nonempty ( ht_star.2 ε hε_pos |> Set.Infinite.diff <| Set.finite_singleton t_star ) ; use t₁; aesop;
    obtain ⟨s, hs⟩ : ∃ s ∈ Set.Icc 0 1, |s - t₁| < min (ε - |t₁ - t_star|) (|t₁ - t_star|) ∧ 1 / (n + 1 : ℝ) ≤ |f s - f t₁| := by
      exact ht₁.2.2.2 _ ( lt_min ( sub_pos.mpr ht₁.2.2.1 ) ( abs_pos.mpr ( sub_ne_zero.mpr ht₁.2.1 ) ) );
    have h_contra : |f s - f t₁| < 2 / (3 * (n + 1) : ℝ) := by
      grind;
    ring_nf at *;
    nlinarith [ inv_mul_cancel₀ ( by linarith : ( 1 + n : ℝ ) ≠ 0 ), inv_mul_cancel₀ ( by linarith : ( 3 + n * 3 : ℝ ) ≠ 0 ), abs_nonneg ( f s - f t₁ ) ];
  refine' Set.Countable.mono _ ( Set.countable_iUnion fun n => Set.Finite.countable <| h_finite n );
  intro t ht; simp_all +decide [ Metric.continuousWithinAt_iff ] ;
  obtain ⟨ x, hx₁, hx₂ ⟩ := ht.2; use ⌊x⁻¹⌋₊; intro δ hδ; obtain ⟨ s, hs₁, hs₂, hs₃, hs₄ ⟩ := hx₂ δ hδ; exact ⟨ s, ⟨ hs₁, hs₂ ⟩, hs₃, by simpa using hs₄.trans' <| inv_le_of_inv_le₀ hx₁ <| Nat.lt_floor_add_one _ |> le_of_lt ⟩ ;

/-- The underlying set of `supDiff`. -/
def supDiffSet (f g : ℝ → ℝ) : Set ℝ := {r : ℝ | ∃ t ∈ Set.Icc (0:ℝ) 1, r = |f t - g t|}

/-- The sup over `[0,1]` of `|f - g|`. -/
def supDiff (f g : ℝ → ℝ) : ℝ := sSup (supDiffSet f g)

theorem supDiffSet_nonempty (f g : ℝ → ℝ) : (supDiffSet f g).Nonempty :=
  ⟨_, 0, ⟨le_refl 0, by norm_num⟩, rfl⟩

theorem supDiff_nonneg (f g : ℝ → ℝ) : 0 ≤ supDiff f g := by
  apply Real.sSup_nonneg;
  rintro x ⟨ t, ht, rfl ⟩ ; exact abs_nonneg _

/-
If both functions are bounded on `[0,1]`, the sup-difference set is bounded above.
-/
theorem bddAbove_supDiffSet {f g : ℝ → ℝ} {Cf Cg : ℝ}
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, |f t| ≤ Cf) (hg : ∀ t ∈ Set.Icc (0:ℝ) 1, |g t| ≤ Cg) :
    BddAbove (supDiffSet f g) := by
  exact ⟨ Cf + Cg, by rintro x ⟨ t, ht, rfl ⟩ ; exact abs_sub _ _ |> le_trans <| add_le_add ( hf t ht ) ( hg t ht ) ⟩

/-- Bound a single value by `supDiff` (needs boundedness above). -/
theorem le_supDiff {f g : ℝ → ℝ} (hb : BddAbove (supDiffSet f g)) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : |f t - g t| ≤ supDiff f g :=
  le_csSup hb ⟨t, ht, rfl⟩

theorem supDiff_comm (f g : ℝ → ℝ) : supDiff f g = supDiff g f := by
  apply csSup_eq_csSup_of_forall_exists_le;
  · exact fun x hx => by rcases hx with ⟨ t, ht, rfl ⟩ ; exact ⟨ _, ⟨ t, ht, rfl ⟩, by rw [ abs_sub_comm ] ⟩ ;
  · exact fun y hy => by rcases hy with ⟨ t, ht, rfl ⟩ ; exact ⟨ _, ⟨ t, ht, rfl ⟩, by rw [ abs_sub_comm ] ⟩ ;

/-
Boundedness of the sup-difference set for a time-changed `Skoro` path against another.
-/
theorem Skoro.bddAbove_comp_supDiffSet (f g : Skoro) (l : TimeChange) :
    BddAbove (supDiffSet (fun t => f (l t)) g) := by
  obtain ⟨ C, hC ⟩ := f.bdd';
  exact bddAbove_supDiffSet ( fun t ht => hC ( l.toFun t ) ( l.mapsTo' ht ) ) g.bdd'.choose_spec

/-
Change of variables `u = l t` in the sup-difference of a time-changed path.
-/
theorem supDiff_comp_symm (f g : Skoro) (l : TimeChange) :
    supDiff (fun t => f (l t)) g = supDiff (fun u => g (l.symm u)) f := by
  apply csSup_eq_csSup_of_forall_exists_le;
  · simp +decide [ supDiffSet ];
    intro x y hy₁ hy₂ hx; use l.toFun y; simp_all +decide [ TimeChange.apply_symmFun, TimeChange.symm_apply_apply ] ;
    exact ⟨ l.mapsTo' ⟨ hy₁, hy₂ ⟩, by rw [ TimeChange.symmFun_apply l ⟨ hy₁, hy₂ ⟩ ] ; rw [ abs_sub_comm ] ⟩;
  · rintro _ ⟨ u, hu, rfl ⟩;
    refine' ⟨ _, ⟨ l.symm u, _, rfl ⟩, _ ⟩ <;> norm_num;
    · exact l.symmFun_mem_Icc hu;
    · rw [ TimeChange.apply_symmFun l hu, abs_sub_comm ]

/-- The set whose infimum defines Billingsley's metric. -/
def dCircSet (f g : Skoro) : Set ℝ :=
  {r : ℝ | ∃ l : TimeChange, FiniteNorm l ∧
      r = max (logSlopeNorm l) (supDiff (fun t => f (l t)) g)}

/-- Billingsley's metric `d°(f, g)`. -/
def dCirc (f g : Skoro) : ℝ := sInf (dCircSet f g)

theorem dCircSet_nonempty (f g : Skoro) : (dCircSet f g).Nonempty :=
  ⟨_, TimeChange.id, finiteNorm_id, rfl⟩

theorem dCircSet_bddBelow (f g : Skoro) : BddBelow (dCircSet f g) := by
  use 0; rintro x ⟨ l, hl, rfl ⟩ ; exact le_max_of_le_left ( logSlopeNorm_nonneg l hl ) ;

theorem dCirc_nonneg (f g : Skoro) : 0 ≤ dCirc f g := by
  exact le_csInf ( dCircSet_nonempty f g ) fun x hx => by rcases hx with ⟨ l, hl, rfl ⟩ ; exact le_max_of_le_left ( logSlopeNorm_nonneg l hl ) ;

theorem dCirc_self (f : Skoro) : dCirc f f = 0 := by
  refine' le_antisymm _ _;
  · refine' csInf_le ( dCircSet_bddBelow f f ) ⟨ TimeChange.id, finiteNorm_id, _ ⟩ ; norm_num [ logSlopeNorm_id, supDiff ];
    refine' csSup_le _ _ <;> norm_num [ supDiffSet ];
    · exact ⟨ _, ⟨ 0, ⟨ by norm_num, by norm_num ⟩, rfl ⟩ ⟩;
    · unfold TimeChange.id; aesop;
  · exact dCirc_nonneg f f

theorem dCirc_comm (f g : Skoro) : dCirc f g = dCirc g f := by
  refine' le_antisymm ( le_csInf _ _ ) ( le_csInf _ _ );
  · exact dCircSet_nonempty g f;
  · intro b hb; obtain ⟨ l, hl, rfl ⟩ := hb; refine' csInf_le _ _ <;> norm_num [ dCircSet ] at *;
    · exact ⟨ 0, by rintro x ⟨ l, hl, rfl ⟩ ; exact le_max_of_le_left ( logSlopeNorm_nonneg l hl ) ⟩;
    · refine' ⟨ l.symm, finiteNorm_symm l hl, _ ⟩;
      rw [ logSlopeNorm_symm l hl, supDiff_comp_symm g f l ];
  · exact ⟨ _, ⟨ TimeChange.id, finiteNorm_id, rfl ⟩ ⟩;
  · rintro _ ⟨ l, hl, rfl ⟩;
    refine' csInf_le _ _ <;> norm_num [ dCircSet ];
    · exact ⟨ 0, by rintro x ⟨ l, hl, rfl ⟩ ; exact le_max_of_le_left ( logSlopeNorm_nonneg l hl ) ⟩;
    · refine' ⟨ l.symm, finiteNorm_symm l hl, _ ⟩;
      rw [ logSlopeNorm_symm l hl, supDiff_comp_symm f g l ]

theorem dCirc_triangle (f g h : Skoro) : dCirc f h ≤ dCirc f g + dCirc g h := by
  refine' le_of_forall_pos_le_add fun ε ε_pos => _;
  obtain ⟨l₁, hl₁⟩ : ∃ l₁ : TimeChange, FiniteNorm l₁ ∧ max (logSlopeNorm l₁) (supDiff (fun t => f (l₁ t)) g) < dCirc f g + ε / 2 := by
    have := exists_lt_of_csInf_lt ( show ( dCircSet f g ).Nonempty from dCircSet_nonempty f g ) ( show dCirc f g < dCirc f g + ε / 2 from lt_add_of_pos_right _ <| half_pos ε_pos );
    unfold dCircSet at this; aesop;
  obtain ⟨l₂, hl₂⟩ : ∃ l₂ : TimeChange, FiniteNorm l₂ ∧ max (logSlopeNorm l₂) (supDiff (fun t => g (l₂ t)) h) < dCirc g h + ε / 2 := by
    exact exists_lt_of_csInf_lt ( dCircSet_nonempty g h ) ( lt_add_of_pos_right _ ( half_pos ε_pos ) ) |> fun ⟨ x, hx₁, hx₂ ⟩ => by rcases hx₁ with ⟨ l₂, hl₂₁, rfl ⟩ ; exact ⟨ l₂, hl₂₁, hx₂ ⟩ ;
  refine' le_trans ( csInf_le _ ⟨ l₁.comp l₂, finiteNorm_comp l₁ l₂ hl₁.1 hl₂.1, rfl ⟩ ) _;
  · exact ⟨ 0, fun x hx => by rcases hx with ⟨ l, hl, rfl ⟩ ; exact le_max_of_le_left ( logSlopeNorm_nonneg l hl ) ⟩;
  · refine' max_le _ _;
    · linarith [ logSlopeNorm_comp_le l₁ l₂ hl₁.1 hl₂.1, le_max_left ( logSlopeNorm l₁ ) ( supDiff ( fun t => f.toFun ( l₁.toFun t ) ) g.toFun ), le_max_right ( logSlopeNorm l₁ ) ( supDiff ( fun t => f.toFun ( l₁.toFun t ) ) g.toFun ), le_max_left ( logSlopeNorm l₂ ) ( supDiff ( fun t => g.toFun ( l₂.toFun t ) ) h.toFun ), le_max_right ( logSlopeNorm l₂ ) ( supDiff ( fun t => g.toFun ( l₂.toFun t ) ) h.toFun ) ];
    · refine' le_trans ( csSup_le _ _ ) _;
      exact supDiff ( fun t => f.toFun ( l₁.toFun t ) ) g.toFun + supDiff ( fun t => g.toFun ( l₂.toFun t ) ) h.toFun;
      · exact ⟨ _, ⟨ 0, ⟨ by norm_num, by norm_num ⟩, rfl ⟩ ⟩;
      · rintro _ ⟨ t, ht, rfl ⟩;
        refine' le_trans _ ( add_le_add ( le_csSup _ ⟨ l₂.toFun t, _, rfl ⟩ ) ( le_csSup _ ⟨ t, _, rfl ⟩ ) );
        · exact abs_sub_le _ _ _;
        · exact Skoro.bddAbove_comp_supDiffSet f g l₁;
        · exact l₂.mapsTo' ht;
        · exact Skoro.bddAbove_comp_supDiffSet g h l₂;
        · exact ht;
      · linarith [ le_max_right ( logSlopeNorm l₁ ) ( supDiff ( fun t => f.toFun ( l₁.toFun t ) ) g.toFun ), le_max_right ( logSlopeNorm l₂ ) ( supDiff ( fun t => g.toFun ( l₂.toFun t ) ) h.toFun ) ]

/-
`d°` is dominated by the uniform (sup) distance (take `λ = id`).
-/
theorem dCirc_le_supDiff (f g : Skoro) : dCirc f g ≤ supDiff f.toFun g.toFun := by
  refine' csInf_le _ _;
  · exact ⟨ 0, fun x hx => by rcases hx with ⟨ l, hl, rfl ⟩ ; exact le_max_of_le_left ( logSlopeNorm_nonneg l hl ) ⟩;
  · use TimeChange.id; simp [logSlopeNorm_id, supDiff];
    refine' ⟨ finiteNorm_id, _ ⟩;
    unfold TimeChange.id; simp +decide [ supDiffSet ] ;
    rw [ max_eq_right ];
    · exact congr_arg _ ( by ext; exact ⟨ fun ⟨ t, ht, ht' ⟩ => ⟨ t, ht, by simpa [ ht.1, ht.2 ] using ht' ⟩, fun ⟨ t, ht, ht' ⟩ => ⟨ t, ht, by simpa [ ht.1, ht.2 ] using ht' ⟩ ⟩ );
    · apply_rules [ Real.sSup_nonneg ] ; aesop

/-
From `d° = 0`, extract a sequence of time changes with vanishing log-slope norm and
vanishing sup-difference.
-/
theorem exists_seq_tendsto_of_dCirc_eq_zero {f g : Skoro} (h : dCirc f g = 0) :
    ∃ l : ℕ → TimeChange, (∀ k, FiniteNorm (l k)) ∧
      Tendsto (fun k => logSlopeNorm (l k)) atTop (𝓝 0) ∧
      Tendsto (fun k => supDiff (fun t => f (l k t)) g.toFun) atTop (𝓝 0) := by
  -- By definition of $dCirc$, we know that for any $\epsilon > 0$, there exists a time change $l$ such that $\max(\logSlopeNorm l, \supDiff(f(l), g)) < \epsilon$.
  have h_eps : ∀ ε > 0, ∃ l : TimeChange, FiniteNorm l ∧ max (logSlopeNorm l) (supDiff (fun t => f.toFun (l.toFun t)) g.toFun) < ε := by
    intro ε hε_pos
    have h_inf : sInf (dCircSet f g) < ε := by
      linarith!
    generalize_proofs at *; (
    exact Exists.elim ( exists_lt_of_csInf_lt ( dCircSet_nonempty f g ) h_inf ) fun x hx => by rcases hx.1 with ⟨ l, hl₁, rfl ⟩ ; exact ⟨ l, hl₁, hx.2 ⟩ ;);
  choose l hl using fun k : ℕ => h_eps ( 1 / ( k + 1 ) ) ( by positivity );
  exact ⟨ l, fun k => hl k |>.1, squeeze_zero ( fun k => logSlopeNorm_nonneg _ ( hl k |>.1 ) ) ( fun k => le_max_left _ _ |> le_trans <| le_of_lt <| hl k |>.2 ) <| tendsto_one_div_add_atTop_nhds_zero_nat, squeeze_zero ( fun k => supDiff_nonneg _ _ ) ( fun k => le_max_right _ _ |> le_trans <| le_of_lt <| hl k |>.2 ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩

/-
From `d° = 0`, `f` and `g` agree at every point where `f` is continuous within `[0,1]`.
-/
theorem eqAt_contPoint_of_dCirc_eq_zero {f g : Skoro} (h : dCirc f g = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hc : ContinuousWithinAt f.toFun (Set.Icc 0 1) t) :
    f.toFun t = g.toFun t := by
  -- Step 1: `Tendsto (fun k => (l k).toFun t) atTop (𝓝 t)`.
  obtain ⟨l, hl_fin, hl_log, hl_sup⟩ := exists_seq_tendsto_of_dCirc_eq_zero h;
  have h_l_tendsto : Filter.Tendsto (fun k => (l k).toFun t) Filter.atTop (nhds t) := by
    have h_l_tendsto : ∀ k, |(l k).toFun t - t| ≤ Real.exp (logSlopeNorm (l k)) - 1 := by
      exact fun k => timeChange_dist_id_le ( l k ) ( hl_fin k ) ht;
    exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => abs_nonneg _ ) h_l_tendsto <| by simpa using Filter.Tendsto.sub_const ( Filter.Tendsto.comp ( Real.continuous_exp.tendsto _ ) hl_log ) 1;
  -- Step 2: `Tendsto (fun k => f.toFun ((l k).toFun t)) atTop (𝓝 (g.toFun t))`.
  have h_f_tendsto : Filter.Tendsto (fun k => f.toFun ((l k).toFun t)) Filter.atTop (nhds (g.toFun t)) := by
    have h_f_tendsto : ∀ k, |f.toFun ((l k).toFun t) - g.toFun t| ≤ supDiff (fun s => f.toFun ((l k).toFun s)) g.toFun := by
      intro k; exact le_supDiff (Skoro.bddAbove_comp_supDiffSet f g (l k)) ht;
    exact tendsto_iff_norm_sub_tendsto_zero.mpr ( squeeze_zero ( fun _ => norm_nonneg _ ) h_f_tendsto hl_sup );
  refine' tendsto_nhds_unique _ h_f_tendsto;
  refine' hc.tendsto.comp _;
  exact tendsto_nhdsWithin_iff.mpr ⟨ h_l_tendsto, Filter.Eventually.of_forall fun k => ( l k ).mapsTo' ht ⟩

/-
From `d° = 0`, `f` and `g` agree at the endpoints (time changes fix `0` and `1`).
-/
theorem eqAt_endpoints_of_dCirc_eq_zero {f g : Skoro} (h : dCirc f g = 0)
    {t : ℝ} (ht : t = 0 ∨ t = 1) : f.toFun t = g.toFun t := by
  obtain ⟨l, hl⟩ := exists_seq_tendsto_of_dCirc_eq_zero h;
  have h_f_tendsto : Filter.Tendsto (fun k => f.toFun ((l k).toFun t)) Filter.atTop (nhds (g.toFun t)) := by
    have h_f_tendsto : ∀ k, |f.toFun ((l k).toFun t) - g.toFun t| ≤ supDiff (fun s => f.toFun ((l k).toFun s)) g.toFun := by
      exact fun k => le_csSup ( Skoro.bddAbove_comp_supDiffSet f g ( l k ) ) ⟨ t, by cases ht <;> aesop, rfl ⟩;
    exact tendsto_iff_norm_sub_tendsto_zero.mpr ( squeeze_zero ( fun _ => norm_nonneg _ ) h_f_tendsto hl.2.2 );
  cases ht <;> aesop

/-
Continuity points of a càdlàg function are dense: every open subinterval of `[0,1]`
contains a point where `f` is continuous within `[0,1]` (its discontinuities are countable).
-/
theorem exists_contPoint_Ioo {f : ℝ → ℝ} (hf : IsCadlag f) {a b : ℝ}
    (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    ∃ s, s ∈ Set.Ioo a b ∧ ContinuousWithinAt f (Set.Icc 0 1) s := by
  -- Let `D` be the set of points in `[0,1]` where `f` is discontinuous within `[0,1]`.
  set D := {t | t ∈ Set.Icc 0 1 ∧ ¬ ContinuousWithinAt f (Set.Icc 0 1) t} with hD_def;
  contrapose! hD_def;
  -- Since `D` is countable, the interval `(a, b)` cannot be contained in `D`.
  have h_not_subset : ¬Set.Ioo a b ⊆ D := by
    exact fun h => absurd ( Set.Countable.mono h <| hf.countable_discontinuities ) ( by exact fun h' => absurd ( h'.measure_zero <| MeasureTheory.MeasureSpace.volume ) ( by simp +decide [ hab, ha, hb ] ) );
  exact False.elim <| h_not_subset <| fun x hx => ⟨ ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩, hD_def x hx ⟩

/-
Identity of indiscernibles: `d°(f,g) = 0 → f = g` (Tier 1 heart).
-/
theorem dCirc_eq_zero {f g : Skoro} (h : dCirc f g = 0) : f = g := by
  apply Skoro.ext_on_Icc;
  intro t ht; by_cases ht1 : t = 1; simp_all +decide [ eqAt_endpoints_of_dCirc_eq_zero ] ;
  · exact eqAt_endpoints_of_dCirc_eq_zero h ( Or.inr rfl );
  · -- By `exists_contPoint_Ioo`, there exists a sequence `s_j` in `(t, 1)` such that `f` is continuous at `s_j`.
    obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, (∀ j, t < s j ∧ s j < 1) ∧ Filter.Tendsto s Filter.atTop (nhds t) ∧ ∀ j, ContinuousWithinAt f.toFun (Set.Icc 0 1) (s j) := by
      have h_seq : ∀ j : ℕ, ∃ s_j ∈ Set.Ioo t 1, ContinuousWithinAt f.toFun (Set.Icc 0 1) s_j ∧ |s_j - t| < 1 / (j + 1) := by
        intro j
        obtain ⟨s_j, hs_j⟩ : ∃ s_j ∈ Set.Ioo t (min 1 (t + 1 / (j + 1))), ContinuousWithinAt f.toFun (Set.Icc 0 1) s_j := by
          apply exists_contPoint_Ioo f.cadlag' (by
          exact lt_min ( lt_of_le_of_ne ht.2 ht1 ) ( lt_add_of_pos_right _ ( by positivity ) )) (by
          linarith [ ht.1 ]) (by
          exact min_le_left _ _);
        exact ⟨ s_j, ⟨ hs_j.1.1, hs_j.1.2.trans_le <| min_le_left _ _ ⟩, hs_j.2, abs_lt.mpr ⟨ by linarith [ hs_j.1.1, hs_j.1.2, min_le_right 1 ( t + 1 / ( j + 1 ) ) ], by linarith [ hs_j.1.1, hs_j.1.2, min_le_right 1 ( t + 1 / ( j + 1 ) ) ] ⟩ ⟩;
      choose s hs using h_seq; exact ⟨ s, fun j => ⟨ hs j |>.1.1, hs j |>.1.2 ⟩, tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun j => le_of_lt <| hs j |>.2.2 ) <| tendsto_one_div_add_atTop_nhds_zero_nat, fun j => hs j |>.2.1 ⟩ ;
    -- By `eqAt_contPoint_of_dCirc_eq_zero`, we have `f.toFun (s j) = g.toFun (s j)` for all `j`.
    have h_eq_s : ∀ j, f.toFun (s j) = g.toFun (s j) := by
      exact fun j => eqAt_contPoint_of_dCirc_eq_zero h ⟨ by linarith [ hs.1 j, ht.1 ], by linarith [ hs.1 j, ht.2 ] ⟩ ( hs.2.2 j );
    -- By ` Cadlag`, we have `ContinuousWithinAt f.toFun (Set.Ici t) t` and `ContinuousWithinAt g.toFun (Set.Ici t) t`.
    have h_cont_f : ContinuousWithinAt f.toFun (Set.Ici t) t := by
      exact f.cadlag'.1 t ⟨ ht.1, lt_of_le_of_ne ht.2 ht1 ⟩
    have h_cont_g : ContinuousWithinAt g.toFun (Set.Ici t) t := by
      exact g.cadlag'.1 t ⟨ ht.1, lt_of_le_of_ne ht.2 ht1 ⟩;
    have h_lim_f : Filter.Tendsto (fun j => f.toFun (s j)) Filter.atTop (nhds (f.toFun t)) := by
      exact h_cont_f.tendsto.comp <| Filter.tendsto_inf.mpr ⟨ hs.2.1, Filter.tendsto_principal.mpr <| Filter.Eventually.of_forall fun j => hs.1 j |>.1.le ⟩
    have h_lim_g : Filter.Tendsto (fun j => g.toFun (s j)) Filter.atTop (nhds (g.toFun t)) := by
      exact h_cont_g.tendsto.comp ( Filter.tendsto_inf.mpr ⟨ hs.2.1, Filter.tendsto_principal.mpr <| Filter.Eventually.of_forall fun j => hs.1 j |>.1.le ⟩ );
    exact tendsto_nhds_unique h_lim_f ( by simpa only [ h_eq_s ] using h_lim_g )

/-- The `MetricSpace` instance on `Skoro` via Billingsley's `d°`. -/
instance : MetricSpace Skoro where
  dist := dCirc
  dist_self := dCirc_self
  dist_comm := dCirc_comm
  dist_triangle := dCirc_triangle
  eq_of_dist_eq_zero := dCirc_eq_zero

theorem dist_eq_dCirc (f g : Skoro) : dist f g = dCirc f g := rfl

/-! ## Tier 2: completeness (Billingsley Thm 12.2) -/

/-
Uniform limits of càdlàg functions are càdlàg (standalone lemma).
-/
theorem isCadlag_of_tendstoUniformly {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, IsCadlag (F n)) (hunif : TendstoUniformly F f atTop) : IsCadlag f := by
  have H := hunif;
  constructor;
  · intro t ht;
    rw [ Metric.tendstoUniformly_iff ] at H;
    rw [ Metric.continuousWithinAt_iff ];
    intro ε hε
    obtain ⟨n, hn⟩ : ∃ n, ∀ x, dist (f x) (F n x) < ε / 3 := by
      exact Filter.Eventually.exists ( H ( ε / 3 ) ( div_pos hε zero_lt_three ) );
    obtain ⟨ δ, hδ, H ⟩ := Metric.continuousWithinAt_iff.mp ( hF n |>.1 t ht ) ( ε / 3 ) ( by linarith );
    exact ⟨ δ, hδ, fun x hx₁ hx₂ => abs_lt.mpr ⟨ by linarith [ abs_lt.mp ( hn x ), abs_lt.mp ( hn t ), abs_lt.mp ( H hx₁ hx₂ ) ], by linarith [ abs_lt.mp ( hn x ), abs_lt.mp ( hn t ), abs_lt.mp ( H hx₁ hx₂ ) ] ⟩ ⟩;
  · intro t ht;
    -- By definition of $IsCadlag$, we know that for each $n$, $F n$ has a left limit at $t$.
    have h_left_limit : ∀ n, ∃ L, Filter.Tendsto (F n) (nhdsWithin t (Set.Iio t)) (nhds L) := by
      intro n; specialize hF n; exact hF.2 t ht;
    choose L hL using h_left_limit;
    -- Since $F_n$ converges uniformly to $f$, the sequence $L_n$ is Cauchy.
    have hL_cauchy : CauchySeq L := by
      rw [ Metric.cauchySeq_iff ];
      rw [ Metric.tendstoUniformly_iff ] at H;
      intro ε hε; obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp ( H ( ε / 3 ) ( by positivity ) ) ; use N; intros m hm n hn; have := hN m hm; have := hN n hn; simp_all +decide [ dist_eq_norm ] ;
      have hLm : Filter.Tendsto (fun x => F m x - F n x) (nhdsWithin t (Set.Iio t)) (nhds (L m - L n)) := by
        exact Filter.Tendsto.sub ( hL m ) ( hL n );
      have := hLm.eventually ( Metric.ball_mem_nhds _ <| show 0 < ε / 3 by linarith ) ; have := this.and ( Ioo_mem_nhdsLT ht.1 ) ; obtain ⟨ x, hx₁, hx₂ ⟩ := this.exists; exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp hx₁, abs_lt.mp ( hN m hm x ), abs_lt.mp ( hN n hn x ) ], by linarith [ abs_lt.mp hx₁, abs_lt.mp ( hN m hm x ), abs_lt.mp ( hN n hn x ) ] ⟩ ;
    obtain ⟨ L', hL' ⟩ := cauchySeq_tendsto_of_complete hL_cauchy;
    use L';
    rw [ Metric.tendstoUniformly_iff ] at H;
    rw [ Metric.tendsto_nhds ] at *;
    intro ε hε; rcases H ( ε / 3 ) ( by positivity ) with h; rcases hL' ( ε / 3 ) ( by positivity ) with h'; rcases Filter.eventually_atTop.mp ( h.and h' ) with ⟨ N, hN ⟩ ; filter_upwards [ hL N |> fun h => h.eventually ( Metric.ball_mem_nhds _ <| show 0 < ε / 3 by positivity ), self_mem_nhdsWithin ] with x hx₁ hx₂; exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp ( hN N le_rfl |>.1 x ), abs_lt.mp ( hN N le_rfl |>.2 ), abs_lt.mp hx₁ ], by linarith [ abs_lt.mp ( hN N le_rfl |>.1 x ), abs_lt.mp ( hN N le_rfl |>.2 ), abs_lt.mp hx₁ ] ⟩ ;

/-
Composition of a càdlàg function with a time change is càdlàg (reusable API).
-/
theorem isCadlag_comp_timeChange {f : ℝ → ℝ} (hf : IsCadlag f) (σ : TimeChange) :
    IsCadlag (fun t => f (σ.toFun t)) := by
  refine' ⟨ fun t ht => _, fun t ht => _ ⟩;
  · refine' hf.1 ( σ.toFun t ) ⟨ _, _ ⟩ |> fun h => h.comp _ _;
    · exact σ.mapsTo' ⟨ ht.1, ht.2.le ⟩ |>.1;
    · exact lt_of_lt_of_le ( σ.strictMonoOn' ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ht.2 ) ( by linarith [ σ.map_one' ] );
    · have := σ.continuousOn';
      refine' this t ⟨ ht.1, ht.2.le ⟩ |> fun h => h.mono_of_mem_nhdsWithin _;
      exact mem_nhdsGE_iff_exists_Ico_subset.mpr ⟨ 1, by aesop, fun x hx => ⟨ by linarith [ hx.1, ht.1 ], by linarith [ hx.2, ht.2 ] ⟩ ⟩;
    · intro x hx; exact (by
      by_cases h_cases : x ∈ Set.Icc 0 1;
      · exact σ.strictMonoOn'.monotoneOn ⟨ by linarith [ ht.1, hx.out ], by linarith [ ht.2, hx.out, h_cases.2 ] ⟩ ⟨ by linarith [ ht.1, hx.out, h_cases.1 ], by linarith [ ht.2, hx.out, h_cases.2 ] ⟩ hx.out;
      · simp_all +decide [ TimeChange.flatR ];
        rw [ σ.flatR x ( by linarith [ h_cases ( by linarith ) ] ) ];
        exact σ.mapsTo' ⟨ by linarith, by linarith ⟩ |>.2);
  · -- By definition of $f$ being cadlag, there exists a left limit $L$ at $\sigma(t)$.
    obtain ⟨L, hL⟩ : ∃ L, Filter.Tendsto f (𝓝[<] (σ.toFun t)) (𝓝 L) := by
      apply hf.2;
      constructor;
      · linarith [ σ.map_zero', σ.strictMonoOn' ( show 0 ∈ Set.Icc 0 1 by norm_num ) ( show t ∈ Set.Icc 0 1 by exact Set.Ioc_subset_Icc_self ht ) ht.1 ];
      · exact σ.mapsTo' ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ |>.2;
    use L;
    refine' hL.comp _;
    refine' tendsto_nhdsWithin_iff.mpr ⟨ _, _ ⟩;
    · have h_cont : ContinuousWithinAt σ.toFun (Set.Icc 0 1) t := by
        exact σ.continuousOn' t ( by constructor <;> linarith [ ht.1, ht.2 ] );
      refine' h_cont.mono_left _;
      rw [ nhdsWithin_le_iff ];
      exact mem_nhdsLT_iff_exists_Ioo_subset.mpr ⟨ 0, ht.1, fun x hx => ⟨ hx.1.le, hx.2.le.trans ht.2 ⟩ ⟩;
    · filter_upwards [ Ioo_mem_nhdsLT ht.1 ] with x hx using σ.strictMonoOn' ⟨ by linarith [ hx.1, ht.1 ], by linarith [ hx.2, ht.2 ] ⟩ ⟨ by linarith [ hx.1, ht.1 ], by linarith [ hx.2, ht.2 ] ⟩ hx.2

/-- Precompose a `Skoro` path with a time change (reusable API). -/
def Skoro.compTimeChange (f : Skoro) (σ : TimeChange) : Skoro where
  toFun := fun t => f.toFun (σ.toFun t)
  cadlag' := isCadlag_comp_timeChange f.cadlag' σ
  bdd' := by
    obtain ⟨C, hC⟩ := f.bdd'
    exact ⟨C, fun t ht => hC (σ.toFun t) (σ.mapsTo' ht)⟩
  flatL := by intro t ht; rw [σ.flatL t ht, σ.map_zero']
  flatR := by intro t ht; rw [σ.flatR t ht, σ.map_one']

/-! ## Tier 3: separability, Polishness, convergence API -/

/-- Auxiliary predicate: the initial segment `[0,b]` admits a finite partition
`0 = t 0 < … < t n = b` on whose half-open cells `f` deviates by `< ε` from the left
endpoint value.  (`n = 0` with `b = 0` is the degenerate empty partition.) -/
def HasGoodPartition (f : ℝ → ℝ) (ε b : ℝ) : Prop :=
  ∃ (n : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t n = b ∧
    (∀ i, i < n → t i < t (i + 1)) ∧
    (∀ i, i ≤ n → t i ∈ Set.Icc (0:ℝ) b) ∧
    (∀ i, i < n → ∀ x ∈ Set.Ico (t i) (t (i + 1)), |f x - f (t i)| < ε)

/-- The empty partition witnesses `HasGoodPartition f ε 0`. -/
theorem hasGoodPartition_zero (f : ℝ → ℝ) (ε : ℝ) : HasGoodPartition f ε 0 := by
  refine ⟨0, fun _ => 0, rfl, rfl, ?_, ?_, ?_⟩
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · intro i hi; simp
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)

/-
Extend a good partition of `[0,b]` by one cell `[b,c)` on which `f` deviates by `< ε`
from `f b`.  This is the reusable single-step (snoc) extension.
-/
theorem hasGoodPartition_snoc {f : ℝ → ℝ} {ε b c : ℝ} (hb : HasGoodPartition f ε b)
    (hbc : b < c) (hcell : ∀ x ∈ Set.Ico b c, |f x - f b| < ε) :
    HasGoodPartition f ε c := by
  obtain ⟨ n, t, ht ⟩ := hb;
  refine' ⟨ n + 1, fun i => if i ≤ n then t i else c, _, _, _, _, _ ⟩ <;> simp_all +decide; all_goals grind

/-
The full segment `[0,1]` admits a good partition (Billingsley's `sup`/left-limit/
right-continuity argument).
-/
theorem hasGoodPartition_one {f : ℝ → ℝ} (hf : IsCadlag f) {ε : ℝ} (hε : 0 < ε) :
    HasGoodPartition f ε 1 := by
  -- Let S := {b : ℝ | 0 ≤ b ∧ b ≤ 1 ∧ HasGoodPartition f ε b}.
  set S := {b : ℝ | 0 ≤ b ∧ b ≤ 1 ∧ HasGoodPartition f ε b} with hS_def
  have hS_nonempty : 0 ∈ S := by
    exact ⟨ by norm_num, by norm_num, hasGoodPartition_zero f ε ⟩
  have hS_bddAbove : BddAbove S := by
    exact ⟨ 1, fun x hx => hx.2.1 ⟩
  have hS_sup : sSup S ∈ Set.Icc 0 1 := by
    exact ⟨ le_trans hS_nonempty.1 ( le_csSup hS_bddAbove hS_nonempty ), csSup_le ⟨ 0, hS_nonempty ⟩ fun x hx => hx.2.1 ⟩
  have hS_beta_in_S : HasGoodPartition f ε (sSup S) := by
    by_cases hβ_pos : 0 < sSup S;
    · -- Since $sSup S > 0$, we can apply the left limit property to find a $\delta > 0$ such that for all $x \in (sSup S - \delta, sSup S)$, $|f x - L| < \epsilon / 2$.
      obtain ⟨L, hL⟩ : ∃ L, Filter.Tendsto f (nhdsWithin (sSup S) (Set.Iio (sSup S))) (nhds L) := by
        exact hf.2 _ ⟨ hβ_pos, hS_sup.2 ⟩
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ Set.Ioo (sSup S - δ) (sSup S), |f x - L| < ε / 2 := by
        have := Metric.tendsto_nhdsWithin_nhds.mp hL ( ε / 2 ) ( half_pos hε );
        exact ⟨ this.choose, this.choose_spec.1, fun x hx => this.choose_spec.2 hx.2 ( abs_lt.mpr ⟨ by linarith [ hx.1, hx.2 ], by linarith [ hx.1, hx.2 ] ⟩ ) ⟩;
      -- Choose $b \in S$ such that $sSup S - δ < b ≤ sSup S$.
      obtain ⟨b, hbS, hbδ⟩ : ∃ b ∈ S, sSup S - δ < b ∧ b ≤ sSup S := by
        exact exists_lt_of_lt_csSup ( show S.Nonempty from ⟨ 0, hS_nonempty ⟩ ) ( by linarith ) |> fun ⟨ b, hb₁, hb₂ ⟩ => ⟨ b, hb₁, hb₂, le_csSup hS_bddAbove hb₁ ⟩;
      by_cases hb_eq : b = sSup S;
      · aesop;
      · have hcell : ∀ x ∈ Set.Ico b (sSup S), |f x - f b| < ε := by
          grind;
        exact hasGoodPartition_snoc hbS.2.2 ( lt_of_le_of_ne hbδ.2 hb_eq ) hcell;
    · rw [ show sSup S = 0 by linarith [ hS_sup.1 ] ] ; exact hasGoodPartition_zero f ε;
  have hS_beta_eq_one : sSup S = 1 := by
    by_contra h_contra; push_neg at h_contra; (
    obtain ⟨c, hc⟩ : ∃ c, sSup S < c ∧ c ≤ 1 ∧ ∀ x ∈ Set.Ico (sSup S) c, |f x - f (sSup S)| < ε := by
      obtain ⟨ δ, hδ_pos, hδ ⟩ := Metric.continuousWithinAt_iff.mp ( hf.1 ( sSup S ) ⟨ hS_sup.1, lt_of_le_of_ne hS_sup.2 h_contra ⟩ ) ε hε;
      exact ⟨ Min.min ( sSup S + δ ) 1, lt_min ( lt_add_of_pos_right _ hδ_pos ) ( lt_of_le_of_ne hS_sup.2 h_contra ), min_le_right _ _, fun x hx => hδ hx.1 <| abs_lt.mpr ⟨ by linarith [ hx.1, min_le_left ( sSup S + δ ) 1 ], by linarith [ hx.2, min_le_left ( sSup S + δ ) 1 ] ⟩ ⟩;
    exact absurd ( le_csSup hS_bddAbove ⟨ by linarith [ hS_sup.1 ], by linarith [ hS_sup.2 ], hasGoodPartition_snoc hS_beta_in_S ( by linarith ) ( by aesop ) ⟩ ) ( by linarith ));
  aesop

/-- **Càdlàg modulus / partition lemma** (reusable for Task 2): for a càdlàg `f` and
`ε > 0` there is a finite partition of `[0,1]` (given by a strictly monotone list of
cut points `t 0 = 0 < t 1 < … < t n = 1`) such that on each half-open cell `[t i, t (i+1))`
the function oscillates from its left value by less than `ε`.

**Documented residual.**  This is the càdlàg modulus, the technical primitive underlying
both the partition-approximation (Tier 3a) and the compactness criterion of Task 2.  Its
proof is a greedy left-to-right construction: right-continuity extends each cell, and the
existence of left limits forces termination after finitely many cells (the same
compactness/accumulation pattern proved in `IsCadlag.countable_discontinuities`).  The
single-step extension is routine; the finite-termination packaging into `t : ℕ → ℝ` is the
remaining work. -/
theorem IsCadlag.exists_modulus_partition {f : ℝ → ℝ} (hf : IsCadlag f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t n = 1 ∧ 0 < n ∧
      (∀ i, i ≤ n → t i ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ i, i < n → t i < t (i + 1)) ∧
      (∀ i, i < n → ∀ x ∈ Set.Ico (t i) (t (i + 1)), |f x - f (t i)| < ε) := by
  obtain ⟨n, t, ht0, htn, htmono, htIcc, htcell⟩ := hasGoodPartition_one hf hε
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso; rw [h] at htn; rw [ht0] at htn; norm_num at htn
    · exact h
  exact ⟨n, t, ht0, htn, hn, htIcc, htmono, htcell⟩

/-! ### Step-function infrastructure (for separability and compactness) -/

/-- Constant functions are càdlàg. -/
theorem isCadlag_const (c : ℝ) : IsCadlag (fun _ : ℝ => c) :=
  ⟨fun _ _ => continuousWithinAt_const, fun _ _ => ⟨c, tendsto_const_nhds⟩⟩

/-- Sums of càdlàg functions are càdlàg. -/
theorem IsCadlag.add {f g : ℝ → ℝ} (hf : IsCadlag f) (hg : IsCadlag g) :
    IsCadlag (fun x => f x + g x) := by
  refine ⟨fun t ht => (hf.1 t ht).add (hg.1 t ht), fun t ht => ?_⟩
  obtain ⟨Lf, hLf⟩ := hf.2 t ht
  obtain ⟨Lg, hLg⟩ := hg.2 t ht
  exact ⟨Lf + Lg, hLf.add hLg⟩

/-
The scaled right-continuous indicator `x ↦ if a ≤ x then c else 0` is càdlàg.
-/
theorem isCadlag_indicator (a c : ℝ) : IsCadlag (fun x => if a ≤ x then c else 0) := by
  constructor;
  · intro t ht; by_cases h : a ≤ t <;> simp_all +decide [ ContinuousWithinAt ] ;
    · exact tendsto_const_nhds.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ if_pos ( by linarith [ hx.out ] ) ] );
    · rw [ Metric.tendsto_nhdsWithin_nhds ];
      exact fun ε ε_pos => ⟨ a - t, by linarith, fun x hx₁ hx₂ => by rw [ if_neg ( by linarith [ abs_lt.mp hx₂ ] ), if_neg ( by linarith [ abs_lt.mp hx₂ ] ) ] ; simpa ⟩;
  · intro t ht;
    by_cases h : a < t;
    · exact ⟨ c, tendsto_const_nhds.congr' <| Filter.eventuallyEq_of_mem ( Ioo_mem_nhdsLT h ) fun x hx => by rw [ if_pos hx.1.le ] ⟩;
    · exact ⟨ 0, tendsto_const_nhds.congr' <| Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ if_neg <| by linarith [ hx.out ] ] ⟩

/-- Finite sums of càdlàg functions are càdlàg. -/
theorem IsCadlag.sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ)
    (hF : ∀ i ∈ s, IsCadlag (F i)) : IsCadlag (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isCadlag_const 0
  | insert a s ha ih =>
      have heq : (fun x => ∑ i ∈ insert a s, F i x) = (fun x => F a x + ∑ i ∈ s, F i x) := by
        funext x; rw [Finset.sum_insert ha]
      rw [heq]
      exact (hF a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

/-- A right-continuous step function with cut points `t 0 < … < t n` and value `v i` on
`[t i, t (i+1))`, represented as `v 0` plus the running sum of indicator jumps. -/
noncomputable def stepFun (n : ℕ) (t v : ℕ → ℝ) : ℝ → ℝ :=
  fun x => v 0 + ∑ i ∈ Finset.range n, (if t (i + 1) ≤ x then v (i + 1) - v i else 0)

/-- `stepFun` is càdlàg. -/
theorem isCadlag_stepFun (n : ℕ) (t v : ℕ → ℝ) : IsCadlag (stepFun n t v) := by
  apply (isCadlag_const (v 0)).add
  exact IsCadlag.sum (Finset.range n) _ (fun i _ => isCadlag_indicator (t (i + 1)) (v (i + 1) - v i))

/-
On a cell `[t j, t (j+1))`, `stepFun` equals the left value `v j`.
-/
theorem stepFun_eq_on_cell (n : ℕ) (t v : ℕ → ℝ)
    (htmono : ∀ i, i < n → t i < t (i + 1)) {j : ℕ} (hj : j < n)
    {x : ℝ} (hx : x ∈ Set.Ico (t j) (t (j + 1))) : stepFun n t v x = v j := by
  have h_chain : ∀ a b, a ≤ b → b ≤ n → t a ≤ t b := by
    intro a b hab hbn; induction hab <;> norm_num at *;
    grind +splitImp;
  have h_split : ∑ i ∈ Finset.range n, (if t (i + 1) ≤ x then v (i + 1) - v i else 0) = ∑ i ∈ Finset.range j, (v (i + 1) - v i) := by
    rw [ ← Finset.sum_range_add_sum_Ico _ hj.le ];
    rw [ Finset.sum_congr rfl fun i hi => if_pos <| by linarith [ hx.1, h_chain _ _ ( by linarith [ Finset.mem_range.mp hi ] : i + 1 ≤ j ) ( by linarith [ Finset.mem_range.mp hi ] ) ], Finset.sum_congr rfl fun i hi => if_neg <| by linarith [ hx.2, h_chain _ _ ( by linarith [ Finset.mem_Ico.mp hi ] : j + 1 ≤ i + 1 ) ( by linarith [ Finset.mem_Ico.mp hi ] ) ] ] ; norm_num;
  convert congr_arg₂ ( · + · ) rfl h_split using 1;
  rw [ Finset.sum_range_sub ( fun i => v i ) ] ; ring

/-
At (or past) the right endpoint `t n`, `stepFun` equals the last value `v n`.
-/
theorem stepFun_eq_last (n : ℕ) (t v : ℕ → ℝ)
    (htmono : ∀ i, i < n → t i < t (i + 1)) {x : ℝ} (hx : t n ≤ x) :
    stepFun n t v x = v n := by
  have h_chain : ∀ a b, a ≤ b → b ≤ n → t a ≤ t b := by
    intro a b hab hbn; induction hab <;> norm_num at *;
    grind +splitImp;
  exact Eq.symm ( by rw [ show stepFun n t v x = v 0 + ∑ i ∈ Finset.range n, ( if t ( i + 1 ) ≤ x then v ( i + 1 ) - v i else 0 ) by rfl ] ; rw [ Finset.sum_congr rfl fun i hi => if_pos ( by linarith [ h_chain ( i + 1 ) n ( by linarith [ Finset.mem_range.mp hi ] ) ( by linarith [ Finset.mem_range.mp hi ] ) ] ) ] ; rw [ Finset.sum_range_sub ( fun i => v i ) ] ; ring )

/-
`stepFun` is flat on `(-∞, 0]`.
-/
theorem stepFun_flatL (n : ℕ) (t v : ℕ → ℝ) (ht0 : t 0 = 0)
    (htmono : ∀ i, i < n → t i < t (i + 1)) {x : ℝ} (hx : x ≤ 0) :
    stepFun n t v x = stepFun n t v 0 := by
  unfold stepFun;
  refine' congr rfl ( Finset.sum_congr rfl fun i hi => _ );
  -- Since $t$ is strictly increasing, $t (i + 1) > 0$ for all $i$.
  have h_pos : ∀ i < n, 0 < t (i + 1) := by
    intro i hi; induction' i with i ih <;> simp_all +decide ;
    · linarith [ htmono 0 hi ];
    · linarith [ ih ( Nat.lt_of_succ_lt hi ), htmono ( i + 1 ) hi ];
  grind

/-
`stepFun` is flat on `[1, ∞)`.
-/
theorem stepFun_flatR (n : ℕ) (t v : ℕ → ℝ) (htn : t n = 1)
    (htmono : ∀ i, i < n → t i < t (i + 1)) {x : ℝ} (hx : 1 ≤ x) :
    stepFun n t v x = stepFun n t v 1 := by
  unfold stepFun;
  refine' congr rfl ( Finset.sum_congr rfl fun i hi => _ );
  have h_chain : ∀ a b, a ≤ b → b ≤ n → t a ≤ t b := by
    intro a b hab hbn; induction hab <;> norm_num at *;
    grind;
  grind

/-- Uniform bound for `stepFun` on all of `ℝ`. -/
theorem stepFun_bdd (n : ℕ) (t v : ℕ → ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, |stepFun n t v x| ≤ C := by
  refine ⟨|v 0| + ∑ i ∈ Finset.range n, |v (i + 1) - v i|, fun x => ?_⟩
  have hsum : |∑ i ∈ Finset.range n, (if t (i + 1) ≤ x then v (i + 1) - v i else 0)|
      ≤ ∑ i ∈ Finset.range n, |v (i + 1) - v i| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => by split_ifs with h <;> simp [abs_nonneg]))
  have := abs_add_le (v 0) (∑ i ∈ Finset.range n, (if t (i + 1) ≤ x then v (i + 1) - v i else 0))
  simp only [stepFun]; linarith

/-- Package `stepFun` as a `Skoro` path, given an increasing partition of `[0,1]`. -/
noncomputable def stepSkoro (n : ℕ) (t v : ℕ → ℝ) (ht0 : t 0 = 0) (htn : t n = 1)
    (htmono : ∀ i, i < n → t i < t (i + 1)) : Skoro where
  toFun := stepFun n t v
  cadlag' := isCadlag_stepFun n t v
  bdd' := by obtain ⟨C, hC⟩ := stepFun_bdd n t v; exact ⟨C, fun x _ => hC x⟩
  flatL := fun x hx => stepFun_flatL n t v ht0 htmono hx
  flatR := fun x hx => stepFun_flatR n t v htn htmono hx

@[simp] theorem stepSkoro_toFun (n : ℕ) (t v : ℕ → ℝ) (ht0 htn htmono) :
    (stepSkoro n t v ht0 htn htmono).toFun = stepFun n t v := rfl

/-
Partition-approximation: a càdlàg `f` is `d°`-approximated by functions that are
piecewise-constant on a fine partition with rational values (via the modulus partition
`IsCadlag.exists_modulus_partition`: the approximant is the step function `g` equal to a
rational near `f (t i)` on each cell `[t i, t (i+1))`; then `|f - g| < ε` uniformly on
`[0,1]`, so `dCirc f g ≤ supDiff f g < ε` by `dCirc_le_supDiff`).

Every point of `[0,1)` lies in a unique partition cell.
-/
theorem exists_cell_index {n : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0) (htn : t n = 1)
    {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) :
    ∃ j, j < n ∧ x ∈ Set.Ico (t j) (t (j + 1)) := by
  -- Let `S := (Finset.range (n+1)).filter (fun i => t i ≤ x)`. `S` is non-empty since `0 ∈ S` (because `t 0 = 0 ≤ x`), and `x < 1 = t n`, so `n` is not in `S`.
  set S := Finset.filter (fun i => (t i) ≤ x) (Finset.range (n + 1)) with hS_def
  have hS_nonempty : S.Nonempty := by
    exact ⟨ 0, Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.succ_pos _ ), by linarith [ hx.1 ] ⟩ ⟩
  have hS_not_n : n ∉ S := by
    grind;
  -- Let `j := S.max' (nonempty)`. Then `j ∈ S`, so `j ≤ n` and `t j ≤ x`. Also `j ≠ n`, so `j < n`.
  obtain ⟨j, hj⟩ : ∃ j ∈ S, ∀ i ∈ S, i ≤ j := by
    exact ⟨ Finset.max' _ hS_nonempty, Finset.max'_mem _ hS_nonempty, fun i hi => Finset.le_max' _ _ hi ⟩
  have hj_lt_n : j < n := by
    exact lt_of_le_of_ne ( Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hj.1 |>.1 ) ) fun h => hS_not_n <| h ▸ hj.1
  have hj_le_x : t j ≤ x := by
    aesop
  have hj1_gt_x : x < t (j + 1) := by
    exact lt_of_not_ge fun h => not_lt_of_ge ( hj.2 ( j + 1 ) <| Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| by linarith, h ⟩ ) <| Nat.lt_succ_self _
  use j, hj_lt_n, hj_le_x, hj1_gt_x

/-
A step function with rational values is rational-valued everywhere.
-/
theorem stepFun_rat (n : ℕ) (t : ℕ → ℝ) (q : ℕ → ℚ) (x : ℝ) :
    ∃ r : ℚ, stepFun n t (fun i => (q i : ℝ)) x = (r : ℝ) := by
  -- The value of the step function at x is the sum of rational numbers, hence it is rational.
  use q 0 + ∑ i ∈ Finset.range n, (if t (i + 1) ≤ x then q (i + 1) - q i else 0);
  simp +decide [ stepFun ];
  exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> norm_num;

theorem exists_piecewiseConst_approx (f : Skoro) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Skoro, (∀ t ∈ Set.Icc (0:ℝ) 1, ∃ q : ℚ, g t = (q : ℝ)) ∧ dCirc f g < ε := by
  set δ : ℝ := ε / 3 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨n, t, ht0, htn, hn, htIcc, htmono, htcell⟩ :=
    IsCadlag.exists_modulus_partition f.cadlag' hδ
  choose qs hqs using fun i => exists_rat_near (f.toFun (t i)) hδ
  set v : ℕ → ℝ := fun i => (qs i : ℝ) with hvdef
  refine ⟨stepSkoro n t v ht0 htn htmono, ?_, ?_⟩
  · intro x _
    obtain ⟨r, hr⟩ := stepFun_rat n t qs x
    exact ⟨r, hr⟩
  · have key : ∀ x ∈ Set.Icc (0:ℝ) 1,
        |f.toFun x - (stepSkoro n t v ht0 htn htmono).toFun x| ≤ 2 * δ := by
      intro x hx
      rw [stepSkoro_toFun]
      by_cases hx1 : x < 1
      · obtain ⟨j, hj, hxcell⟩ := exists_cell_index ht0 htn (x := x) ⟨hx.1, hx1⟩
        rw [stepFun_eq_on_cell n t v htmono hj hxcell, hvdef]; simp only
        have h1 := htcell j hj x hxcell
        have h2 := hqs j
        calc |f.toFun x - (qs j : ℝ)|
            ≤ |f.toFun x - f.toFun (t j)| + |f.toFun (t j) - (qs j : ℝ)| := abs_sub_le _ _ _
          _ ≤ 2 * δ := by linarith
      · have hx1' : x = 1 := le_antisymm hx.2 (not_lt.mp hx1)
        have hlast : t n ≤ x := by rw [htn, hx1']
        rw [stepFun_eq_last n t v htmono hlast, hvdef]; simp only
        have h2 := hqs n
        have hfeq : f.toFun x = f.toFun (t n) := by rw [htn, hx1']
        rw [hfeq]
        linarith [abs_nonneg (f.toFun (t n) - (qs n : ℝ))]
    have hsup : supDiff f.toFun (stepSkoro n t v ht0 htn htmono).toFun ≤ 2 * δ := by
      apply csSup_le (supDiffSet_nonempty _ _)
      rintro y ⟨x, hx, rfl⟩
      exact key x hx
    calc dCirc f (stepSkoro n t v ht0 htn htmono)
        ≤ supDiff f.toFun (stepSkoro n t v ht0 htn htmono).toFun := dCirc_le_supDiff _ _
      _ ≤ 2 * δ := hsup
      _ < ε := by rw [hδdef]; linarith

/-! ### Piecewise-linear time changes (for separability and compactness) -/

/-- Piecewise-linear interpolation through the nodes `(s i, r i)`, `i = 0,…,n`, written in
the telescoping `min` form so that it is automatically flat outside `[0,1]` (when
`s 0 = 0`, `s n = 1`, `s i ∈ [0,1]`). -/
noncomputable def plFun (n : ℕ) (s r : ℕ → ℝ) : ℝ → ℝ :=
  fun x => r 0 + ∑ i ∈ Finset.range n,
    ((r (i + 1) - r i) / (s (i + 1) - s i)) * (min x (s (i + 1)) - min x (s i))

/-
The key weighted-average slope bounds: if every piece slope lies in
`[exp (-η), exp η]` then `plFun` stretches every subinterval of `[0,1]` by a factor in
`[exp (-η), exp η]`.
-/
theorem plFun_slope_bounds (n : ℕ) (s r : ℕ → ℝ) (η : ℝ)
    (hsmono : ∀ i, i < n → s i < s (i + 1))
    (hslope_lo : ∀ i, i < n → Real.exp (-η) * (s (i + 1) - s i) ≤ r (i + 1) - r i)
    (hslope_hi : ∀ i, i < n → r (i + 1) - r i ≤ Real.exp η * (s (i + 1) - s i))
    (hs0 : s 0 = 0) (hsn : s n = 1) (hsIcc : ∀ i, i ≤ n → s i ∈ Set.Icc (0:ℝ) 1)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Real.exp (-η) * (b - a) ≤ plFun n s r b - plFun n s r a ∧
      plFun n s r b - plFun n s r a ≤ Real.exp η * (b - a) := by
  -- Let's compute the difference $plFun(n,s,r,b) - plFun(n,s,r,a)$.
  have h_diff : plFun n s r b - plFun n s r a = ∑ i ∈ Finset.range n, ((r (i + 1) - r i) / (s (i + 1) - s i)) * ((min b (s (i + 1)) - min b (s i)) - (min a (s (i + 1)) - min a (s i))) := by
    unfold plFun; simp +decide [ mul_sub ] ;
  -- Apply the bounds on the slopes to each term in the sum.
  have h_bounds : ∀ i < n, (Real.exp (-η)) * ((min b (s (i + 1)) - min b (s i)) - (min a (s (i + 1)) - min a (s i))) ≤ ((r (i + 1) - r i) / (s (i + 1) - s i)) * ((min b (s (i + 1)) - min b (s i)) - (min a (s (i + 1)) - min a (s i))) ∧ ((r (i + 1) - r i) / (s (i + 1) - s i)) * ((min b (s (i + 1)) - min b (s i)) - (min a (s (i + 1)) - min a (s i))) ≤ (Real.exp η) * ((min b (s (i + 1)) - min b (s i)) - (min a (s (i + 1)) - min a (s i))) := by
    intro i hi
    have h_nonneg : 0 ≤ (min b (s (i + 1)) - min b (s i)) - (min a (s (i + 1)) - min a (s i)) := by
      grind +splitIndPred;
    exact ⟨ mul_le_mul_of_nonneg_right ( by rw [ le_div_iff₀ ] <;> linarith [ hsmono i hi, hslope_lo i hi ] ) h_nonneg, mul_le_mul_of_nonneg_right ( by rw [ div_le_iff₀ ] <;> linarith [ hsmono i hi, hslope_hi i hi ] ) h_nonneg ⟩;
  -- Apply the bounds on the slopes to the sum.
  have h_sum_bounds : ∑ i ∈ Finset.range n, ((min b (s (i + 1)) - min b (s i)) - (min a (s (i + 1)) - min a (s i))) = b - a := by
    convert Finset.sum_range_sub ( fun i => min b ( s i ) - min a ( s i ) ) n using 1 ; norm_num [ hs0, hsn ];
    · ring;
    · grind +revert;
  rw [ ← h_sum_bounds, Finset.mul_sum _ _ _, Finset.mul_sum _ _ _ ];
  exact ⟨ h_diff.symm ▸ Finset.sum_le_sum fun i hi => h_bounds i ( Finset.mem_range.mp hi ) |>.1, h_diff.symm ▸ Finset.sum_le_sum fun i hi => h_bounds i ( Finset.mem_range.mp hi ) |>.2 ⟩

/-
Value of `plFun` at the nodes.
-/
theorem plFun_node (n : ℕ) (s r : ℕ → ℝ) (hsmono : ∀ i, i < n → s i < s (i + 1))
    {j : ℕ} (hj : j ≤ n) : plFun n s r (s j) = r j := by
  have h_chain : ∀ a b, a ≤ b → b ≤ n → s a ≤ s b := by
    intro a b hab hbn; induction hab <;> norm_num at *;
    grind;
  convert congr_arg₂ ( · + · ) rfl ( Finset.sum_range_add_sum_Ico ( fun i => if s ( i + 1 ) ≤ s j then r ( i + 1 ) - r i else 0 ) hj ) using 1
  simp_all +decide [ Finset.sum_range_succ ];
  any_goals exact r 0;
  · unfold plFun;
    rw [ Finset.sum_Ico_eq_sub _ hj ] ; norm_num [ Finset.sum_range_add ] ; ring;
    refine Finset.sum_congr rfl fun i hi => ?_;
    grind;
  · rw [ ← Finset.sum_range_add_sum_Ico _ hj ];
    rw [ Finset.sum_congr rfl fun i hi => if_pos <| h_chain _ _ ( by linarith [ Finset.mem_range.mp hi ] ) ( by linarith [ Finset.mem_range.mp hi ] ), Finset.sum_congr rfl fun i hi => if_neg <| by linarith [ hsmono i ( by linarith [ Finset.mem_Ico.mp hi ] ), h_chain _ _ ( by linarith [ Finset.mem_Ico.mp hi ] : j ≤ i ) ( by linarith [ Finset.mem_Ico.mp hi ] ) ] ] ; norm_num [ Finset.sum_range_sub ( fun i => r i ) ]

/-- `plFun` is continuous. -/
theorem plFun_continuous (n : ℕ) (s r : ℕ → ℝ) : Continuous (plFun n s r) := by
  unfold plFun
  refine continuous_const.add (continuous_finset_sum _ (fun i _ => ?_))
  exact continuous_const.mul (((continuous_id.min continuous_const).sub
    (continuous_id.min continuous_const)))

/-- `plFun` maps `0` to `r 0`; with `r 0 = 0` and `s 0 = 0` this is `0`. -/
theorem plFun_zero (n : ℕ) (s r : ℕ → ℝ) (hsmono : ∀ i, i < n → s i < s (i + 1))
    (hs0 : s 0 = 0) (hr0 : r 0 = 0) : plFun n s r 0 = 0 := by
  have h := plFun_node n s r hsmono (Nat.zero_le n)
  rw [hs0, hr0] at h; exact h

/-- `plFun` maps `1` to `r n`; with `r n = 1` and `s n = 1` this is `1`. -/
theorem plFun_one (n : ℕ) (s r : ℕ → ℝ) (hsmono : ∀ i, i < n → s i < s (i + 1))
    (hsn : s n = 1) (hrn : r n = 1) : plFun n s r 1 = 1 := by
  have h := plFun_node n s r hsmono (le_refl n)
  rw [hsn, hrn] at h; exact h

/-- `plFun` is flat (`= 0`) on `(-∞, 0]`. -/
theorem plFun_flatL (n : ℕ) (s r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hsIcc : ∀ i, i ≤ n → s i ∈ Set.Icc (0:ℝ) 1) {x : ℝ} (hx : x ≤ 0) :
    plFun n s r x = 0 := by
  unfold plFun
  rw [hr0, zero_add]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have hi' : i < n := Finset.mem_range.mp hi
  have hsi : (0:ℝ) ≤ s i := (hsIcc i (by omega)).1
  have hsi1 : (0:ℝ) ≤ s (i + 1) := (hsIcc (i + 1) (by omega)).1
  rw [min_eq_left (le_trans hx hsi1), min_eq_left (le_trans hx hsi)]; ring

/-- `plFun` is flat (`= 1`) on `[1, ∞)`. -/
theorem plFun_flatR (n : ℕ) (s r : ℕ → ℝ) (hsmono : ∀ i, i < n → s i < s (i + 1))
    (hr0 : r 0 = 0) (hrn : r n = 1) (hsIcc : ∀ i, i ≤ n → s i ∈ Set.Icc (0:ℝ) 1)
    {x : ℝ} (hx : 1 ≤ x) : plFun n s r x = 1 := by
  unfold plFun
  have hterm : ∀ i ∈ Finset.range n,
      ((r (i + 1) - r i) / (s (i + 1) - s i)) * (min x (s (i + 1)) - min x (s i))
        = r (i + 1) - r i := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hsi : s i ≤ 1 := (hsIcc i (by omega)).2
    have hsi1 : s (i + 1) ≤ 1 := (hsIcc (i + 1) (by omega)).2
    have hpos : s (i + 1) - s i ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hsmono i hi'))
    rw [min_eq_right (le_trans hsi1 hx), min_eq_right (le_trans hsi hx)]
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun i => r i), hr0, hrn]; ring

/-- `plFun` is strictly monotone on `[0,1]`. -/
theorem plFun_strictMonoOn (n : ℕ) (s r : ℕ → ℝ) (η : ℝ)
    (hsmono : ∀ i, i < n → s i < s (i + 1))
    (hslope_lo : ∀ i, i < n → Real.exp (-η) * (s (i + 1) - s i) ≤ r (i + 1) - r i)
    (hslope_hi : ∀ i, i < n → r (i + 1) - r i ≤ Real.exp η * (s (i + 1) - s i))
    (hs0 : s 0 = 0) (hsn : s n = 1) (hsIcc : ∀ i, i ≤ n → s i ∈ Set.Icc (0:ℝ) 1) :
    StrictMonoOn (plFun n s r) (Set.Icc 0 1) := by
  intro a ha b hb hab
  have := (plFun_slope_bounds n s r η hsmono hslope_lo hslope_hi hs0 hsn hsIcc
    ha.1 hab.le hb.2).1
  nlinarith [Real.exp_pos (-η), this]

/-- Assemble `plFun` into a `TimeChange`, given strictly increasing nodes on `[0,1]` and a
uniform log-slope bound `η ≥ 0`. -/
noncomputable def plLambda (n : ℕ) (s r : ℕ → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hsmono : ∀ i, i < n → s i < s (i + 1))
    (hslope_lo : ∀ i, i < n → Real.exp (-η) * (s (i + 1) - s i) ≤ r (i + 1) - r i)
    (hslope_hi : ∀ i, i < n → r (i + 1) - r i ≤ Real.exp η * (s (i + 1) - s i))
    (hs0 : s 0 = 0) (hsn : s n = 1) (hsIcc : ∀ i, i ≤ n → s i ∈ Set.Icc (0:ℝ) 1)
    (hr0 : r 0 = 0) (hrn : r n = 1) : TimeChange where
  toFun := plFun n s r
  map_zero' := plFun_zero n s r hsmono hs0 hr0
  map_one' := plFun_one n s r hsmono hsn hrn
  strictMonoOn' := plFun_strictMonoOn n s r η hsmono hslope_lo hslope_hi hs0 hsn hsIcc
  continuousOn' := (plFun_continuous n s r).continuousOn
  mapsTo' := by
    intro x hx
    have hlo := (plFun_slope_bounds n s r η hsmono hslope_lo hslope_hi hs0 hsn hsIcc
      (le_refl (0:ℝ)) hx.1 hx.2).1
    have hlo2 := (plFun_slope_bounds n s r η hsmono hslope_lo hslope_hi hs0 hsn hsIcc
      hx.1 hx.2 (le_refl (1:ℝ))).1
    rw [plFun_zero n s r hsmono hs0 hr0] at hlo
    rw [plFun_one n s r hsmono hsn hrn] at hlo2
    exact ⟨by nlinarith [Real.exp_pos (-η), hx.1, hlo], by nlinarith [Real.exp_pos (-η), hx.2, hlo2]⟩
  flatL := fun x hx => plFun_flatL n s r hr0 hsIcc hx
  flatR := fun x hx => plFun_flatR n s r hsmono hr0 hrn hsIcc hx

@[simp] theorem plLambda_toFun (n s r η hη hsmono hslo hshi hs0 hsn hsIcc hr0 hrn) :
    (plLambda n s r η hη hsmono hslo hshi hs0 hsn hsIcc hr0 hrn).toFun = plFun n s r := rfl

/-
The log-slope norm of `plLambda` is at most `η`.
-/
theorem logSlopeNorm_plLambda_le (n s r η) (hη : 0 ≤ η)
    (hsmono hslo hshi hs0 hsn hsIcc hr0 hrn) :
    logSlopeNorm (plLambda n s r η hη hsmono hslo hshi hs0 hsn hsIcc hr0 hrn) ≤ η := by
  refine' csSup_le _ _;
  · exact logSlopeSet_nonempty _;
  · rintro x ⟨ a, b, ha, hab, hb, rfl ⟩;
    have := plFun_slope_bounds n s r η hsmono hslo hshi hs0 hsn hsIcc ha hab.le hb;
    unfold slopeLog; simp +decide [ *, ne_of_gt ( sub_pos.mpr hab ) ] ;
    rw [ abs_le ];
    exact ⟨ by rw [ Real.le_log_iff_exp_le ( div_pos ( by nlinarith [ Real.exp_pos ( -η ) ] ) ( by linarith ) ) ] ; rw [ le_div_iff₀ ( by linarith ) ] ; linarith, by rw [ Real.log_le_iff_le_exp ( div_pos ( by nlinarith [ Real.exp_pos ( -η ) ] ) ( by linarith ) ) ] ; rw [ div_le_iff₀ ( by linarith ) ] ; linarith ⟩

theorem finiteNorm_plLambda (n s r η) (hη : 0 ≤ η)
    (hsmono hslo hshi hs0 hsn hsIcc hr0 hrn) :
    FiniteNorm (plLambda n s r η hη hsmono hslo hshi hs0 hsn hsIcc hr0 hrn) := by
  refine' ⟨ η, fun r hr => _ ⟩;
  obtain ⟨ a, b, ha, hab, hb, rfl ⟩ := hr; simp +decide [ slopeLog ] ;
  rw [ abs_le ];
  have := plFun_slope_bounds n s r η hsmono hslo hshi hs0 hsn hsIcc ha hab.le hb;
  exact ⟨ by rw [ Real.le_log_iff_exp_le ( div_pos ( by nlinarith [ Real.exp_pos ( -η ) ] ) ( by linarith ) ) ] ; rw [ le_div_iff₀ ( by linarith ) ] ; linarith, by rw [ Real.log_le_iff_le_exp ( div_pos ( by nlinarith [ Real.exp_pos ( -η ) ] ) ( by linarith ) ) ] ; rw [ div_le_iff₀ ( by linarith ) ] ; linarith ⟩

/-! ### Separability: rational step functions are dense -/

/-
Cell-matching: composing the target step function with the piecewise-linear map
`plFun n r t` (sending the `r`-grid to the `t`-grid) reproduces the step function on the
`r`-grid.
-/
theorem stepFun_comp_plFun (n : ℕ) (t r q : ℕ → ℝ)
    (htmono : ∀ i, i < n → t i < t (i + 1)) (ht0 : t 0 = 0) (htn : t n = 1)
    (hrmono : ∀ i, i < n → r i < r (i + 1)) (hr0 : r 0 = 0) (hrn : r n = 1)
    (hrIcc : ∀ i, i ≤ n → r i ∈ Set.Icc (0:ℝ) 1)
    (η : ℝ)
    (hslo : ∀ i, i < n → Real.exp (-η) * (r (i + 1) - r i) ≤ t (i + 1) - t i)
    (hshi : ∀ i, i < n → t (i + 1) - t i ≤ Real.exp η * (r (i + 1) - r i))
    (htIcc : ∀ i, i ≤ n → t i ∈ Set.Icc (0:ℝ) 1)
    {y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1) :
    stepFun n t q (plFun n r t y) = stepFun n r q y := by
  by_cases hy1 : y < 1;
  · obtain ⟨ j, hj, hyj ⟩ := exists_cell_index hr0 hrn ( x := y ) ⟨ hy.1, hy1 ⟩;
    have h_plFun_bounds : t j ≤ plFun n r t y ∧ plFun n r t y < t (j + 1) := by
      have h_plFun_mono : StrictMonoOn (plFun n r t) (Set.Icc 0 1) := by
        apply plFun_strictMonoOn n r t η hrmono hslo hshi hr0 hrn hrIcc;
      exact ⟨ by rw [ ← plFun_node n r t hrmono ( by linarith ) ] ; exact h_plFun_mono.le_iff_le ( by constructor <;> linarith [ Set.mem_Icc.mp ( hrIcc j ( by linarith ) ), Set.mem_Icc.mp hy ] ) ( by constructor <;> linarith [ Set.mem_Icc.mp ( hrIcc j ( by linarith ) ), Set.mem_Icc.mp hy ] ) |>.2 hyj.1, by rw [ ← plFun_node n r t hrmono ( by linarith ) ] ; exact h_plFun_mono.lt_iff_lt ( by constructor <;> linarith [ Set.mem_Icc.mp ( hrIcc j ( by linarith ) ), Set.mem_Icc.mp hy ] ) ( by constructor <;> linarith [ Set.mem_Icc.mp ( hrIcc ( j + 1 ) ( by linarith ) ), Set.mem_Icc.mp hy ] ) |>.2 hyj.2 ⟩;
    rw [ stepFun_eq_on_cell n t q htmono hj ⟨ h_plFun_bounds.1, h_plFun_bounds.2 ⟩, stepFun_eq_on_cell n r q hrmono hj hyj ];
  · norm_num [ show y = 1 by linarith [ hy.2 ], plFun_one, stepFun_eq_last, * ];
    rw [ show plFun n r t 1 = 1 by exact plFun_one n r t ( by assumption ) ( by assumption ) ( by assumption ) ] ; rw [ stepFun_eq_last, stepFun_eq_last ] <;> aesop;

/-
The approximation lemma with the step structure exposed (variant of
`exists_piecewiseConst_approx`).
-/
theorem exists_stepSkoro_approx (f : Skoro) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (t : ℕ → ℝ) (qs : ℕ → ℚ) (ht0 : t 0 = 0) (htn : t n = 1)
      (htmono : ∀ i, i < n → t i < t (i + 1)),
      (∀ i, i ≤ n → t i ∈ Set.Icc (0:ℝ) 1) ∧
      dCirc f (stepSkoro n t (fun i => (qs i : ℝ)) ht0 htn htmono) < ε := by
  -- Set δ = ε / 3.
  set δ := ε / 3 with hδ;
  obtain ⟨ n, t, ht0, htn, hn, htIcc, htmono, htcell ⟩ := IsCadlag.exists_modulus_partition f.cadlag' ( by positivity : 0 < δ );
  -- Choose rationals `qs` via `choose qs hqs using fun i => exists_rat_near (f.toFun (t i)) hδ` giving `|f.toFun (t i) - (qs i : ℝ)| < δ`.
  obtain ⟨qs, hqs⟩ : ∃ qs : ℕ → ℚ, ∀ i ≤ n, |f.toFun (t i) - (qs i : ℝ)| < δ := by
    exact ⟨ fun i => Classical.choose ( exists_rat_near ( f.toFun ( t i ) ) ( by positivity ) ), fun i hi => Classical.choose_spec ( exists_rat_near ( f.toFun ( t i ) ) ( by positivity ) ) ⟩;
  refine' ⟨ n, t, qs, ht0, htn, htmono, htIcc, _ ⟩;
  have key : ∀ x ∈ Set.Icc (0:ℝ) 1,
      |f.toFun x - (stepSkoro n t (fun i => (qs i : ℝ)) ht0 htn htmono).toFun x| ≤ 2 * δ := by
        intro x hx
        by_cases hx1 : x < 1
        · obtain ⟨j, hj, hxcell⟩ := exists_cell_index ht0 htn (x := x) ⟨hx.1, hx1⟩
          rw [stepSkoro_toFun, stepFun_eq_on_cell n t (fun i => (qs i : ℝ)) htmono hj hxcell]
          have h1 := htcell j hj x hxcell
          have h2 := hqs j (by omega)
          calc |f.toFun x - (qs j : ℝ)|
              ≤ |f.toFun x - f.toFun (t j)| + |f.toFun (t j) - (qs j : ℝ)| := abs_sub_le _ _ _
            _ ≤ 2 * δ := by linarith
        · have hx1' : x = 1 := le_antisymm hx.2 (not_lt.mp hx1)
          have hlast : t n ≤ x := by rw [htn, hx1']
          rw [stepSkoro_toFun, stepFun_eq_last n t (fun i => (qs i : ℝ)) htmono hlast]
          have h2 := hqs n (by omega)
          have hfeq : f.toFun x = f.toFun (t n) := by rw [htn, hx1']
          rw [hfeq]
          linarith [abs_nonneg (f.toFun (t n) - (qs n : ℝ))];
  have hsup : supDiff f.toFun (stepSkoro n t (fun i => (qs i : ℝ)) ht0 htn htmono).toFun ≤ 2 * δ := by
    apply csSup_le (supDiffSet_nonempty _ _);
    rintro _ ⟨ x, hx, rfl ⟩ ; exact key x hx;
  exact lt_of_le_of_lt ( dCirc_le_supDiff _ _ ) ( by linarith )

/-
Choose rational nodes `r` whose gaps are within a factor `exp (±η)` of the `t`-gaps.
-/
theorem exists_rational_nodes {n : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0) (htn : t n = 1)
    (htmono : ∀ i, i < n → t i < t (i + 1)) (htIcc : ∀ i, i ≤ n → t i ∈ Set.Icc (0:ℝ) 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ r : ℕ → ℚ, ((r 0 : ℝ) = 0) ∧ ((r n : ℝ) = 1) ∧
      (∀ i, i ≤ n → ((r i : ℝ)) ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ i, i < n → (r i : ℝ) < (r (i + 1) : ℝ)) ∧
      (∀ i, i < n → Real.exp (-η) * ((r (i + 1) : ℝ) - (r i : ℝ)) ≤ t (i + 1) - t i) ∧
      (∀ i, i < n → t (i + 1) - t i ≤ Real.exp η * ((r (i + 1) : ℝ) - (r i : ℝ))) := by
  by_cases hn : n = 0;
  · aesop;
  · -- Set m to be the minimum of the gaps t(i+1)-t i over i ∈ Finset.range n (nonempty when n>0).
    obtain ⟨m, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ i < n, m ≤ t (i + 1) - t i := by
      obtain ⟨m, hm⟩ : ∃ m ∈ Finset.image (fun i => t (i + 1) - t i) (Finset.range n), ∀ j ∈ Finset.image (fun i => t (i + 1) - t i) (Finset.range n), m ≤ j := by
        exact ⟨ Finset.min' _ ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_range.mpr ( Nat.pos_of_ne_zero hn ) ) ⟩, Finset.min'_mem _ _, fun j hj => Finset.min'_le _ _ hj ⟩;
      exact ⟨ m, by obtain ⟨ i, hi, rfl ⟩ := Finset.mem_image.mp hm.1; linarith [ htmono i ( Finset.mem_range.mp hi ) ], fun i hi => hm.2 _ ( Finset.mem_image.mpr ⟨ i, Finset.mem_range.mpr hi, rfl ⟩ ) ⟩;
    -- Set c := min (1 - Real.exp (-η)) (Real.exp η - 1); c > 0 (η > 0 gives exp(-η) < 1 and exp η > 1).
    set c := min (1 - Real.exp (-η)) (Real.exp η - 1) with hc
    have hc_pos : 0 < c := by
      exact lt_min ( sub_pos.mpr ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr hη ) ) ) ( sub_pos.mpr ( by norm_num; positivity ) )
    -- Set δ := m * c / 2; δ > 0, and δ ≤ m/2 (since c ≤ 1... note 1 - exp(-η) < 1, so c < 1, hence δ < m/2).
    set δ := m * c / 2 with hδ
    have hδ_pos : 0 < δ := by
      exact div_pos ( mul_pos hm.1 hc_pos ) zero_lt_two
    have hδ_le_m_div_2 : δ ≤ m / 2 := by
      nlinarith [ show c ≤ 1 by exact min_le_of_left_le ( sub_le_self _ ( Real.exp_nonneg _ ) ) ];
    -- For each i, choose r i : ℚ with t i - δ < (r i : ℝ) < t i + δ via exists_rat_btwn (t i - δ < t i + δ).
    obtain ⟨r, hr⟩ : ∃ r : ℕ → ℚ, (∀ i ≤ n, t i - δ < (r i : ℝ) ∧ (r i : ℝ) < t i + δ) ∧ (r 0 : ℝ) = 0 ∧ (r n : ℝ) = 1 := by
      choose! r hr using fun i => exists_rat_btwn ( show t i - δ < t i + δ by linarith );
      use fun i => if i = 0 then 0 else if i = n then 1 else r i;
      aesop;
    refine' ⟨ r, hr.2.1, hr.2.2, _, _, _, _ ⟩;
    · intro i hi
      have hri_bounds : t i - δ < (r i : ℝ) ∧ (r i : ℝ) < t i + δ := hr.1 i hi
      have hri_nonneg : 0 ≤ (r i : ℝ) := by
        by_cases hi0 : i = 0;
        · aesop;
        · have hri_nonneg : t i ≥ m := by
            induction' i with i ih <;> norm_num [ * ] at *;
            linarith [ hm.2 i hi, htIcc i ( by linarith ) ];
          linarith [ htIcc i hi |>.1 ]
      have hri_le_one : (r i : ℝ) ≤ 1 := by
        grind
      exact ⟨hri_nonneg, hri_le_one⟩;
    · grind;
    · intro i hi; nlinarith [ hr.1 i ( by linarith ), hr.1 ( i + 1 ) ( by linarith ), hm.2 i hi, Real.exp_pos ( -η ), Real.exp_pos η, mul_div_cancel₀ ( m * c ) two_ne_zero, min_le_left ( 1 - Real.exp ( -η ) ) ( Real.exp η - 1 ), min_le_right ( 1 - Real.exp ( -η ) ) ( Real.exp η - 1 ), Real.exp_neg η, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos η ) ) ] ;
    · intro i hi; nlinarith [ hr.1 i ( by linarith ), hr.1 ( i + 1 ) ( by linarith ), hm.2 i hi, Real.add_one_le_exp η, Real.exp_pos ( -η ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos η ) ), Real.exp_neg η, min_le_left ( 1 - Real.exp ( -η ) ) ( Real.exp η - 1 ), min_le_right ( 1 - Real.exp ( -η ) ) ( Real.exp η - 1 ) ] ;

/-
Alignment: two step functions on the grids `t` and `r` with the *same* values are
`d°`-close, with the distance controlled by the log-slope of the grid map.
-/
theorem dCirc_stepSkoro_le (n : ℕ) (t r q : ℕ → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (htmono : ∀ i, i < n → t i < t (i + 1)) (ht0 : t 0 = 0) (htn : t n = 1)
    (htIcc : ∀ i, i ≤ n → t i ∈ Set.Icc (0:ℝ) 1)
    (hrmono : ∀ i, i < n → r i < r (i + 1)) (hr0 : r 0 = 0) (hrn : r n = 1)
    (hrIcc : ∀ i, i ≤ n → r i ∈ Set.Icc (0:ℝ) 1)
    (hslo : ∀ i, i < n → Real.exp (-η) * (r (i + 1) - r i) ≤ t (i + 1) - t i)
    (hshi : ∀ i, i < n → t (i + 1) - t i ≤ Real.exp η * (r (i + 1) - r i)) :
    dCirc (stepSkoro n t q ht0 htn htmono) (stepSkoro n r q hr0 hrn hrmono) ≤ η := by
  refine' le_trans ( csInf_le _ _ ) _;
  exact max ( logSlopeNorm ( plLambda n r t η hη hrmono hslo hshi hr0 hrn hrIcc ht0 htn ) ) ( supDiff ( fun y => ( stepSkoro n t q ht0 htn htmono ).toFun ( plLambda n r t η hη hrmono hslo hshi hr0 hrn hrIcc ht0 htn y ) ) ( stepSkoro n r q hr0 hrn hrmono ).toFun );
  · exact ⟨ 0, fun x hx => by rcases hx with ⟨ l, hl, rfl ⟩ ; exact le_max_of_le_left ( by apply Real.sSup_nonneg; rintro x ⟨ a, b, ha, hab, hb, rfl ⟩ ; exact abs_nonneg _ ) ⟩;
  · exact ⟨ _, finiteNorm_plLambda n r t η hη hrmono hslo hshi hr0 hrn hrIcc ht0 htn, rfl ⟩;
  · refine' max_le ( logSlopeNorm_plLambda_le _ _ _ _ _ _ _ _ _ _ _ _ _ ) _;
    refine' csSup_le _ _;
    · exact ⟨ _, ⟨ 0, by norm_num, rfl ⟩ ⟩;
    · rintro x ⟨ y, hy, rfl ⟩ ; simp +decide [ stepSkoro_toFun, plLambda_toFun ] ;
      rw [ stepFun_comp_plFun n t r q htmono ht0 htn hrmono hr0 hrn hrIcc η hslo hshi htIcc hy ] ; norm_num [ hη ]

/-- Index type for the countable family of rational step functions. -/
abbrev SepIndex : Type := Σ n : ℕ, (Fin (n + 1) → ℚ) × (Fin (n + 1) → ℚ)

instance : Countable SepIndex := by unfold SepIndex; infer_instance

/-- The zero path (used as the fallback for invalid rational data). -/
def zeroPath : Skoro where
  toFun := fun _ => 0
  cadlag' := ⟨fun _ _ => continuousWithinAt_const, fun _ _ => ⟨0, tendsto_const_nhds⟩⟩
  bdd' := ⟨0, fun _ _ => by simp⟩
  flatL := fun _ _ => rfl
  flatR := fun _ _ => rfl

open Classical in
/-- The countable family of rational step functions (invalid data maps to the zero path). -/
noncomputable def sepFun : SepIndex → Skoro := fun p =>
  let n := p.1
  let r : ℕ → ℝ := fun i => if h : i < n + 1 then ((p.2.1 ⟨i, h⟩ : ℚ) : ℝ) else 1
  let q : ℕ → ℝ := fun i => if h : i < n + 1 then ((p.2.2 ⟨i, h⟩ : ℚ) : ℝ) else 0
  if H : r 0 = 0 ∧ r n = 1 ∧ ∀ i, i < n → r i < r (i + 1) then
    stepSkoro n r q H.1 H.2.1 H.2.2
  else zeroPath

/-
Density: every path is `d°`-approximable by a member of the rational step family.
-/
theorem exists_sepFun_close (f : Skoro) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : SepIndex, dCirc f (sepFun p) < ε := by
  obtain ⟨ n, t, qs, ht0, htn, htmono, htIcc, hfg ⟩ := exists_stepSkoro_approx f ( show 0 < ε / 2 by linarith );
  obtain ⟨ r, hr0, hrn, hrIcc, hrmono, hslo, hshi ⟩ := exists_rational_nodes ht0 htn htmono htIcc ( show 0 < ε / 2 by linarith );
  -- Let $g'$ be the stepSkoro function with rational nodes $r$ and values $qs$.
  set g' : Skoro := stepSkoro n (fun i => (r i : ℝ)) (fun i => (qs i : ℝ)) hr0 hrn hrmono;
  have hg' : dCirc (stepSkoro n t (fun i => (qs i : ℝ)) ht0 htn htmono) g' ≤ ε / 2 := by
    convert dCirc_stepSkoro_le n t ( fun i => ( r i : ℝ ) ) ( fun i => ( qs i : ℝ ) ) ( ε / 2 ) ( by linarith ) htmono ht0 htn htIcc hrmono hr0 hrn hrIcc hslo hshi using 1;
  -- By definition of `sepFun`, we have `sepFun ⟨n, fun i => r i, fun i => qs i⟩ = g'`.
  have h_sepFun : sepFun ⟨n, fun i => r i, fun i => qs i⟩ = g' := by
    convert Skoro.coe_injective <| funext fun x => ?_;
    unfold sepFun; simp +decide [ g', stepSkoro_toFun ] ;
    split_ifs <;> simp_all +decide [ stepSkoro_toFun ];
    · unfold stepFun; simp +decide [ Finset.sum_range, Nat.lt_succ_iff ] ;
    · rename_i h; specialize h ( by simpa using hr0 ) ; obtain ⟨ i, hi, hi' ⟩ := h; split_ifs at hi' <;> linarith [ hrmono i hi ] ;
  exact ⟨ _, by rw [ h_sepFun ] ; exact lt_of_le_of_lt ( dCirc_triangle _ _ _ ) ( by linarith ) ⟩

/-- Separability of the Skorokhod space.

A countable dense set is the set of step functions with rational cut points and rational
values.  Density combines the partition-approximation (`exists_piecewiseConst_approx`) with
a `J₁` alignment by a piecewise-linear time change (`plLambda`); countability is by encoding
the finite rational data.  `SecondCountableTopology` and `PolishSpace` are derived
automatically from this instance together with `CompleteSpace`. -/
instance : TopologicalSpace.SeparableSpace Skoro :=
  TopologicalSpace.SeparableSpace.of_denseRange sepFun <| by
    rw [Metric.denseRange_iff]
    intro f ε hε
    obtain ⟨p, hp⟩ := exists_sepFun_close f hε
    exact ⟨p, by rw [dist_eq_dCirc]; exact hp⟩

/-! ### Completeness (Billingsley Thm 12.2): the `σ∞` infinite-composition -/

/-
Two-sided slope control from the log-slope norm: a finite-norm time change stretches
every subinterval of `[0,1]` by a factor in `[exp (-‖l‖), exp ‖l‖]`.
-/
theorem TimeChange.slope_bounds (l : TimeChange) (h : FiniteNorm l) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    Real.exp (-logSlopeNorm l) * (y - x) ≤ l.toFun y - l.toFun x ∧
      l.toFun y - l.toFun x ≤ Real.exp (logSlopeNorm l) * (y - x) := by
  by_cases hxy' : x < y <;> by_cases hyx' : y - x > 0 <;> simp_all +decide [ Real.exp_pos ];
  · -- By definition of `logSlopeNorm`, we know that for any $0 \leq s < t \leq 1$, $|\log((l(t) - l(s)) / (t - s))| \leq \logSlopeNorm l$.
    have h_log_slope : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → abs (Real.log ((l.toFun t - l.toFun s) / (t - s))) ≤ logSlopeNorm l := by
      exact fun s t hs ht ht' => le_csSup ( h ) ⟨ s, t, hs, ht, ht', rfl ⟩;
    have := h_log_slope x y hx hxy' hy; rw [ abs_le ] at this; rw [ Real.le_log_iff_exp_le, Real.log_le_iff_le_exp ] at * <;> norm_num at *;
    · exact ⟨ by rw [ le_div_iff₀ ( sub_pos.mpr hxy' ) ] at this; linarith, by rw [ div_le_iff₀ ( sub_pos.mpr hxy' ) ] at this; linarith ⟩;
    · exact lt_of_lt_of_le ( Real.exp_pos _ ) this.1;
    · exact div_pos ( sub_pos.mpr ( l.strictMonoOn' ( by constructor <;> linarith ) ( by constructor <;> linarith ) hxy' ) ) ( sub_pos.mpr hxy' );
  · linarith;
  · norm_num [ show x = y by linarith ]

/-
Construct the limit time change from a pointwise-convergent sequence of time changes
with a uniform log-slope bound.  The limit inherits the same log-slope bound, so it is a
genuine (strictly monotone, bi-Lipschitz) time change.
-/
theorem TimeChange.exists_limit (ρ : ℕ → TimeChange) (N : ℝ) (hN : 0 ≤ N)
    (hfin : ∀ k, FiniteNorm (ρ k)) (hnorm : ∀ k, logSlopeNorm (ρ k) ≤ N)
    (hconv : ∀ x, x ∈ Set.Icc (0:ℝ) 1 → ∃ L, Tendsto (fun k => (ρ k).toFun x) atTop (𝓝 L)) :
    ∃ rlim : TimeChange, FiniteNorm rlim ∧ logSlopeNorm rlim ≤ N ∧
      ∀ x, x ∈ Set.Icc (0:ℝ) 1 →
        Tendsto (fun k => (ρ k).toFun x) atTop (𝓝 (rlim.toFun x)) := by
  choose! L hL using hconv;
  -- Define the limit function $G : ℝ → ℝ$ by $G(x) = L(x)$ for $x ∈ [0,1]$ and $G(x) = 0$ for $x ≤ 0$ and $G(x) = 1$ for $x ≥ 1$.
  set G : ℝ → ℝ := fun x => if hx : x ∈ Set.Icc (0:ℝ) 1 then L x else if x ≤ 0 then 0 else 1;
  -- Show that $G$ is a time change.
  have hG_time_change : ∃ rlim : TimeChange, rlim.toFun = G := by
    have hG_mapsTo : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ G x ∧ G x ≤ 1 := by
      intro x hx; specialize hL x hx; simp_all +decide [ G ] ;
      exact ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds hL fun k => ( ρ k ).mapsTo' hx |>.1, le_of_tendsto_of_tendsto' hL tendsto_const_nhds fun k => ( ρ k ).mapsTo' hx |>.2 ⟩
    have hG_cont : ContinuousOn G (Set.Icc (0:ℝ) 1) := by
      have hG_lip : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ 1 → |G y - G x| ≤ Real.exp N * (y - x) := by
        intros x y hx hy hxy
        have hG_lip : ∀ k, |(ρ k).toFun y - (ρ k).toFun x| ≤ Real.exp N * (y - x) := by
          intros k
          have hG_lip : Real.exp (-logSlopeNorm (ρ k)) * (y - x) ≤ (ρ k).toFun y - (ρ k).toFun x ∧ (ρ k).toFun y - (ρ k).toFun x ≤ Real.exp (logSlopeNorm (ρ k)) * (y - x) := by
            apply TimeChange.slope_bounds (ρ k) (hfin k) hx hy hxy;
          rw [ abs_le ];
          constructor <;> nlinarith [ Real.exp_pos ( -logSlopeNorm ( ρ k ) ), Real.exp_pos N, Real.exp_le_exp.mpr ( show -logSlopeNorm ( ρ k ) ≤ N by linarith [ hnorm k, show 0 ≤ logSlopeNorm ( ρ k ) from by apply Real.sSup_nonneg; rintro x ⟨ a, b, ha, hab, hb, rfl ⟩ ; exact abs_nonneg _ ] ), Real.exp_le_exp.mpr ( show logSlopeNorm ( ρ k ) ≤ N by linarith [ hnorm k ] ) ];
        simp +zetaDelta at *;
        rw [ if_pos ⟨ by linarith, by linarith ⟩, if_pos ⟨ by linarith, by linarith ⟩ ];
        exact le_of_tendsto' ( Filter.Tendsto.abs ( Filter.Tendsto.sub ( hL y ( by linarith ) ( by linarith ) ) ( hL x ( by linarith ) ( by linarith ) ) ) ) fun k => hG_lip k;
      refine' Metric.continuousOn_iff.mpr _;
      intro b hb ε hε; use ε / Real.exp N; refine' ⟨ div_pos hε ( Real.exp_pos _ ), fun a ha hab => _ ⟩ ; simp_all +decide [ dist_eq_norm ] ;
      cases le_total a b <;> simp_all +decide [ abs_lt, mul_div_cancel₀, Real.exp_ne_zero ];
      · constructor <;> nlinarith [ abs_le.mp ( hG_lip a b ha.1 ‹_› hb.2 ), Real.exp_pos N, mul_div_cancel₀ ε ( ne_of_gt ( Real.exp_pos N ) ) ];
      · constructor <;> nlinarith [ abs_le.mp ( hG_lip b a hb.1 ‹_› ha.2 ), Real.exp_pos N, mul_div_cancel₀ ε ( ne_of_gt ( Real.exp_pos N ) ) ]
    have hG_mono : StrictMonoOn G (Set.Icc (0:ℝ) 1) := by
      intros x hx y hy hxy;
      have hG_slope : ∀ k, Real.exp (-N) * (y - x) ≤ (ρ k).toFun y - (ρ k).toFun x ∧ (ρ k).toFun y - (ρ k).toFun x ≤ Real.exp N * (y - x) := by
        intros k
        have hG_slope_k : Real.exp (-logSlopeNorm (ρ k)) * (y - x) ≤ (ρ k).toFun y - (ρ k).toFun x ∧ (ρ k).toFun y - (ρ k).toFun x ≤ Real.exp (logSlopeNorm (ρ k)) * (y - x) := by
          apply TimeChange.slope_bounds (ρ k) (hfin k) hx.1 hxy.le hy.2;
        exact ⟨ le_trans ( mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr ( neg_le_neg ( hnorm k ) ) ) ( sub_nonneg.mpr hxy.le ) ) hG_slope_k.1, le_trans hG_slope_k.2 ( mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr ( hnorm k ) ) ( sub_nonneg.mpr hxy.le ) ) ⟩;
      have hG_slope_lim : Real.exp (-N) * (y - x) ≤ L y - L x ∧ L y - L x ≤ Real.exp N * (y - x) := by
        exact ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds ( Filter.Tendsto.sub ( hL y hy ) ( hL x hx ) ) fun k => hG_slope k |>.1, le_of_tendsto_of_tendsto' ( Filter.Tendsto.sub ( hL y hy ) ( hL x hx ) ) tendsto_const_nhds fun k => hG_slope k |>.2 ⟩;
      simp +zetaDelta at *;
      rw [ if_pos ⟨ hx.1, hx.2 ⟩, if_pos ⟨ hy.1, hy.2 ⟩ ] ; nlinarith [ Real.exp_pos ( -N ), Real.exp_pos N ]
    have hG_zero : G 0 = 0 := by
      have hG_zero : L 0 = 0 := by
        exact tendsto_nhds_unique ( hL 0 <| by norm_num ) <| tendsto_const_nhds.congr' <| by filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk; simp +decide [ ( ρ k ).map_zero' ] ;
      simp [G, hG_zero]
    have hG_one : G 1 = 1 := by
      have hG_one : L 1 = 1 := by
        exact tendsto_nhds_unique ( hL 1 <| by norm_num ) <| tendsto_const_nhds.congr' <| by filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk; simp +decide [ ( ρ k ).map_one' ] ;
      simp [G, hG_one]
    have hG_flatL : ∀ x ≤ 0, G x = 0 := by
      grind
    have hG_flatR : ∀ x ≥ 1, G x = 1 := by
      grind +qlia;
    use ⟨G, hG_zero, hG_one, hG_mono, hG_cont, hG_mapsTo, hG_flatL, hG_flatR⟩;
  obtain ⟨ rlim, hrlim ⟩ := hG_time_change; use rlim; simp_all +decide [ funext_iff ] ;
  refine' ⟨ _, _, _ ⟩;
  · refine' ⟨ N, fun r hr => _ ⟩;
    obtain ⟨ a, b, ha, hab, hb, rfl ⟩ := hr;
    -- By the properties of the limit function $G$, we have $G(b) - G(a) \geq \exp(-N) (b - a)$ and $G(b) - G(a) \leq \exp(N) (b - a)$.
    have hG_bounds : Real.exp (-N) * (b - a) ≤ G b - G a ∧ G b - G a ≤ Real.exp N * (b - a) := by
      have hG_bounds : ∀ k, Real.exp (-N) * (b - a) ≤ (ρ k).toFun b - (ρ k).toFun a ∧ (ρ k).toFun b - (ρ k).toFun a ≤ Real.exp N * (b - a) := by
        intro k; exact TimeChange.slope_bounds (ρ k) (hfin k) ha hab.le hb |> fun h => ⟨ by nlinarith [ Real.exp_pos ( -N ), Real.exp_le_exp.mpr ( neg_le_neg ( hnorm k ) ) ], by nlinarith [ Real.exp_pos N, Real.exp_le_exp.mpr ( hnorm k ) ] ⟩ ;
      simp +zetaDelta at *;
      exact ⟨ by rw [ if_pos ⟨ by linarith, by linarith ⟩, if_pos ⟨ by linarith, by linarith ⟩ ] ; exact le_of_tendsto_of_tendsto' tendsto_const_nhds ( Filter.Tendsto.sub ( hL b ( by linarith ) ( by linarith ) ) ( hL a ( by linarith ) ( by linarith ) ) ) fun k => hG_bounds k |>.1, by rw [ if_pos ⟨ by linarith, by linarith ⟩, if_pos ⟨ by linarith, by linarith ⟩ ] ; exact le_of_tendsto_of_tendsto' ( hL b ( by linarith ) ( by linarith ) ) ( Filter.Tendsto.add tendsto_const_nhds ( hL a ( by linarith ) ( by linarith ) ) ) fun k => hG_bounds k |>.2 ⟩;
    unfold slopeLog; simp +decide [ *, ne_of_gt ( sub_pos.mpr hab ) ] ;
    rw [ abs_le ];
    exact ⟨ by rw [ Real.le_log_iff_exp_le ( div_pos ( by nlinarith [ Real.exp_pos ( -N ), Real.exp_pos N ] ) ( sub_pos.mpr hab ) ) ] ; rw [ le_div_iff₀ ( sub_pos.mpr hab ) ] ; linarith, by rw [ Real.log_le_iff_le_exp ( div_pos ( by nlinarith [ Real.exp_pos ( -N ), Real.exp_pos N ] ) ( sub_pos.mpr hab ) ) ] ; rw [ div_le_iff₀ ( sub_pos.mpr hab ) ] ; linarith ⟩;
  · refine' csSup_le _ _ <;> norm_num [ logSlopeSet ];
    · exact ⟨ _, ⟨ 0, by norm_num, 1, by norm_num, by norm_num, rfl ⟩ ⟩;
    · intro b x hx y hy hxy hb; subst hb; unfold slopeLog; simp +decide [ *, abs_le ] ;
      -- By the properties of the logarithm and the definition of $G$, we have:
      have h_log_bounds : Real.exp (-N) * (y - x) ≤ L y - L x ∧ L y - L x ≤ Real.exp N * (y - x) := by
        have h_log_bounds : ∀ k, Real.exp (-N) * (y - x) ≤ (ρ k).toFun y - (ρ k).toFun x ∧ (ρ k).toFun y - (ρ k).toFun x ≤ Real.exp N * (y - x) := by
          intro k; exact TimeChange.slope_bounds (ρ k) (hfin k) hx hy.le hxy |> fun h => ⟨ by nlinarith [ Real.exp_pos (-N), Real.exp_le_exp.mpr ( show -N ≤ -logSlopeNorm ( ρ k ) by linarith [ hnorm k ] ) ], by nlinarith [ Real.exp_pos N, Real.exp_le_exp.mpr ( show logSlopeNorm ( ρ k ) ≤ N by linarith [ hnorm k ] ) ] ⟩ ;
        exact ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds ( Filter.Tendsto.sub ( hL y ( by linarith ) ( by linarith ) ) ( hL x ( by linarith ) ( by linarith ) ) ) fun k => h_log_bounds k |>.1, le_of_tendsto_of_tendsto' ( Filter.Tendsto.sub ( hL y ( by linarith ) ( by linarith ) ) ( hL x ( by linarith ) ( by linarith ) ) ) tendsto_const_nhds fun k => h_log_bounds k |>.2 ⟩;
      simp +zetaDelta at *;
      rw [ if_pos ⟨ by linarith, by linarith ⟩, if_pos ⟨ by linarith, by linarith ⟩ ];
      exact ⟨ by rw [ Real.le_log_iff_exp_le ( div_pos ( by nlinarith [ Real.exp_pos ( -N ), Real.exp_pos N ] ) ( by linarith ) ) ] ; rw [ le_div_iff₀ ( by linarith ) ] ; linarith, by rw [ Real.log_le_iff_le_exp ( div_pos ( by nlinarith [ Real.exp_pos ( -N ), Real.exp_pos N ] ) ( by linarith ) ) ] ; rw [ div_le_iff₀ ( by linarith ) ] ; linarith ⟩;
  · aesop

/-- `logSlopeNorm` depends only on the underlying function. -/
theorem logSlopeNorm_congr {l l' : TimeChange} (h : l.toFun = l'.toFun) :
    logSlopeNorm l = logSlopeNorm l' := by
  unfold logSlopeNorm; rw [h]

/-
Extract the aligning time changes from a rapidly-Cauchy sequence.
-/
theorem exists_muSeq (u : ℕ → Skoro) (hu : ∀ k, dCirc (u k) (u (k + 1)) < (1/2:ℝ)^k) :
    ∃ μ : ℕ → TimeChange, ∀ k, FiniteNorm (μ k) ∧ logSlopeNorm (μ k) < (1/2:ℝ)^k ∧
      supDiff (fun t => (u k).toFun ((μ k).toFun t)) (u (k + 1)).toFun < (1/2:ℝ)^k := by
  have h_seq : ∀ k, ∃ l : TimeChange, FiniteNorm l ∧ logSlopeNorm l < (1 / 2) ^ k ∧ supDiff (fun t => (u k).toFun (l.toFun t)) (u (k + 1)).toFun < (1 / 2) ^ k := by
    intro k
    obtain ⟨l, hl⟩ : ∃ l : TimeChange, FiniteNorm l ∧ max (logSlopeNorm l) (supDiff (fun t => (u k).toFun (l.toFun t)) (u (k + 1)).toFun) < (1 / 2) ^ k := by
      have := hu k;
      contrapose! this;
      exact le_csInf ( dCircSet_nonempty _ _ ) fun x hx => hx.choose_spec.2.symm ▸ this _ hx.choose_spec.1;
    exact ⟨ l, hl.1, lt_of_le_of_lt ( le_max_left _ _ ) hl.2, lt_of_le_of_lt ( le_max_right _ _ ) hl.2 ⟩;
  exact ⟨ fun k => Classical.choose ( h_seq k ), fun k => Classical.choose_spec ( h_seq k ) ⟩

/-
Telescoping bound for the log-slope norm of the composition `ρ m ∘ (ρ k)⁻¹`, where the
`ρ` are the running inverse-compositions of the `μ`.
-/
theorem logSlopeNorm_comp_tail (μ ρ : ℕ → TimeChange)
    (hμfin : ∀ j, FiniteNorm (μ j)) (hρfin : ∀ k, FiniteNorm (ρ k))
    (hρrec : ∀ k x, (ρ (k + 1)).toFun x = (μ k).symm.toFun ((ρ k).toFun x)) :
    ∀ k m, k ≤ m →
      logSlopeNorm ((ρ m).comp (ρ k).symm) ≤ ∑ j ∈ Finset.Ico k m, logSlopeNorm (μ j) := by
  intro k m hkm
  induction' hkm with m ih;
  · refine' csSup_le _ _ <;> norm_num [ logSlopeSet ];
    · exact ⟨ _, ⟨ 0, by norm_num, 1, by norm_num, by norm_num, rfl ⟩ ⟩;
    · intros b x hx y hy hxy hb
      have h_eq : (ρ k).toFun ((ρ k).symm.toFun x) = x ∧ (ρ k).toFun ((ρ k).symm.toFun y) = y := by
        exact ⟨ TimeChange.apply_symm_apply _ ⟨ hx, by linarith ⟩, TimeChange.apply_symm_apply _ ⟨ by linarith, by linarith ⟩ ⟩;
      unfold slopeLog at hb; simp_all +decide [ ne_of_gt ( sub_pos.mpr hy ) ] ;
  · -- By definition of composition, we have:
    have h_comp : (ρ (m + 1)).comp (ρ k).symm = (μ m).symm.comp ((ρ m).comp (ρ k).symm) := by
      unfold TimeChange.comp; aesop;
    -- By the properties of the log-slope norm, we have:
    have h_log_slope_norm_comp : logSlopeNorm ((μ m).symm.comp ((ρ m).comp (ρ k).symm)) ≤ logSlopeNorm (μ m).symm + logSlopeNorm ((ρ m).comp (ρ k).symm) := by
      apply logSlopeNorm_comp_le;
      · exact finiteNorm_symm _ ( hμfin m );
      · exact finiteNorm_comp _ _ ( hρfin m ) ( finiteNorm_symm _ ( hρfin k ) );
    rw [ Finset.sum_Ico_succ_top ih ];
    rw [ h_comp, logSlopeNorm_symm ] at * ; linarith;
    exact hμfin m

/-
A sup-rapidly-Cauchy sequence of paths has a càdlàg uniform limit in `Skoro`, with the
sup-distances to the limit tending to `0`.
-/
theorem exists_skoroUnifLimit (h : ℕ → Skoro)
    (hcauchy : ∀ k, supDiff (h (k + 1)).toFun (h k).toFun ≤ (1/2:ℝ)^k) :
    ∃ hinf : Skoro, Tendsto (fun k => supDiff (h k).toFun hinf.toFun) atTop (𝓝 0) := by
  -- Since the sequence `(h k).toFun` is Cauchy in the uniform norm, it converges to some limit `g`.
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, TendstoUniformly (fun k => (h k).toFun) g atTop := by
    -- By definition of `hcauchy`, we know that the sequence of functions `(h k).toFun` is uniformly Cauchy.
    have h_uniform_cauchy : UniformCauchySeqOn (fun k => (h k).toFun) Filter.atTop (Set.Icc 0 1) := by
      -- By definition of $hcauchy$, we know that for all $k$, $\sup_{t \in [0,1]} |h_{k+1}(t) - h_k(t)| \leq (1/2)^k$.
      have h_sup_diff : ∀ k, ∀ t ∈ Set.Icc 0 1, |(h (k + 1)).toFun t - (h k).toFun t| ≤ (1 / 2 : ℝ)^k := by
        intros k t ht
        have h_diff : |(h (k + 1)).toFun t - (h k).toFun t| ≤ supDiff (h (k + 1)).toFun (h k).toFun := by
          apply le_csSup;
          · obtain ⟨ C₁, hC₁ ⟩ := ( h ( k + 1 ) ).bdd'
            obtain ⟨ C₂, hC₂ ⟩ := ( h k ).bdd'
            use C₁ + C₂
            intro x hx
            obtain ⟨ t, ht, rfl ⟩ := hx
            exact abs_le.mpr ⟨ by linarith [ abs_le.mp ( hC₁ t ht ), abs_le.mp ( hC₂ t ht ) ], by linarith [ abs_le.mp ( hC₁ t ht ), abs_le.mp ( hC₂ t ht ) ] ⟩;
          · exact ⟨ t, ht, rfl ⟩
        exact le_trans h_diff (hcauchy k);
      -- By definition of $h_sup_diff$, we know that for all $k$, $\sup_{t \in [0,1]} |h_{k+1}(t) - h_k(t)| \leq (1/2)^k$.
      have h_sup_diff_sum : ∀ m n, m ≤ n → ∀ t ∈ Set.Icc 0 1, |(h n).toFun t - (h m).toFun t| ≤ ∑ k ∈ Finset.Ico m n, (1 / 2 : ℝ)^k := by
        intro m n hmn t ht; induction hmn <;> simp_all +decide [ Finset.sum_Ico_succ_top ] ;
        exact abs_le.mpr ⟨ by linarith [ abs_le.mp ‹_›, abs_le.mp ( h_sup_diff ‹_› t ht.1 ht.2 ) ], by linarith [ abs_le.mp ‹_›, abs_le.mp ( h_sup_diff ‹_› t ht.1 ht.2 ) ] ⟩;
      rw [ Metric.uniformCauchySeqOn_iff ];
      intro ε hε
      obtain ⟨N, hN⟩ : ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∑ k ∈ Finset.Ico m n, (1 / 2 : ℝ)^k < ε := by
        have h_sum_conv : Summable (fun k : ℕ => (1 / 2 : ℝ)^k) := by
          exact summable_geometric_two;
        have := Metric.tendsto_atTop.mp h_sum_conv.hasSum.tendsto_sum_nat;
        obtain ⟨ N, HN ⟩ := this ( ε / 2 ) ( half_pos hε ) ; use N; intros m hm n hn; cases le_total m n <;> simp_all +decide [ dist_eq_norm, Finset.sum_Ico_eq_sub _ ] ;
        linarith [ abs_lt.mp ( HN m hm ), abs_lt.mp ( HN n hn ) ];
      use N; intros m hm n hn x hx; cases le_total m n <;> simp_all +decide [ dist_eq_norm ] ;
      · simpa only [ abs_sub_comm ] using lt_of_le_of_lt ( h_sup_diff_sum m n ‹_› x hx.1 hx.2 ) ( hN m hm n hn );
      · exact lt_of_le_of_lt ( h_sup_diff_sum _ _ ‹_› _ hx.1 hx.2 ) ( hN _ hn _ hm );
    have h_uniform_converge : ∃ g : ℝ → ℝ, TendstoUniformlyOn (fun k => (h k).toFun) g Filter.atTop (Set.Icc 0 1) := by
      have h_uniform_converge : ∀ x ∈ Set.Icc 0 1, ∃ L, Filter.Tendsto (fun k => (h k).toFun x) Filter.atTop (nhds L) := by
        intro x hx; exact cauchySeq_tendsto_of_complete ( show CauchySeq ( fun k => ( h k |> Skoro.toFun ) x ) from by
                                                            grind +suggestions ) ;
      choose! g hg using h_uniform_converge;
      use g;
      rw [ Metric.uniformCauchySeqOn_iff ] at h_uniform_cauchy;
      rw [ Metric.tendstoUniformlyOn_iff ];
      intro ε hε; rcases h_uniform_cauchy ( ε / 2 ) ( half_pos hε ) with ⟨ N, HN ⟩ ; filter_upwards [ Filter.Ici_mem_atTop N ] with n hn; intro x hx; have := hg x hx; have := this.eventually ( Metric.ball_mem_nhds _ ( half_pos hε ) ) ; have := this.and ( Filter.eventually_ge_atTop N ) ; obtain ⟨ m, hm₁, hm₂ ⟩ := this.exists; exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp ( HN m hm₂ n hn x hx ), abs_lt.mp hm₁ ], by linarith [ abs_lt.mp ( HN m hm₂ n hn x hx ), abs_lt.mp hm₁ ] ⟩ ;
    obtain ⟨ g, hg ⟩ := h_uniform_converge;
    use fun x => if hx : x ∈ Set.Icc 0 1 then g x else if x ≤ 0 then g 0 else g 1;
    intro ε hε; filter_upwards [ hg ε hε, Filter.eventually_gt_atTop 0 ] with k hk hk'; intro x; by_cases hx : x ∈ Set.Icc 0 1 <;> simp_all +decide [ Metric.tendstoUniformlyOn_iff ] ;
    split_ifs <;> simp_all +decide [ Skoro.flatL, Skoro.flatR ];
    convert hk 1 ( by norm_num ) ( by norm_num ) using 1;
    exact congr_arg _ ( by rw [ Skoro.flatR ] ; linarith [ hx ( by linarith ) ] );
  -- By definition of `g`, we know that `g` is a Skorokhod path.
  obtain ⟨hinf, hhinf⟩ : ∃ hinf : Skoro, hinf.toFun = g := by
    have h_cadlag : IsCadlag g := by
      apply isCadlag_of_tendstoUniformly (fun k => (h k).cadlag') hg
    have h_bdd : ∃ C, ∀ t ∈ Set.Icc (0:ℝ) 1, |g t| ≤ C := by
      have := hg;
      rw [ Metric.tendstoUniformly_iff ] at this;
      obtain ⟨ n, hn ⟩ := this 1 zero_lt_one |> fun h => h.exists;
      exact ⟨ ( h n |> Skoro.bdd' |> Classical.choose ) + 1, fun t ht => abs_le.mpr ⟨ by linarith [ abs_lt.mp ( hn t ), abs_le.mp ( ( h n |> Skoro.bdd' |> Classical.choose_spec ) t ht ) ], by linarith [ abs_lt.mp ( hn t ), abs_le.mp ( ( h n |> Skoro.bdd' |> Classical.choose_spec ) t ht ) ] ⟩ ⟩
    have h_flatL : ∀ x ≤ 0, g x = g 0 := by
      intro x hx
      have h_eq : ∀ k, (h k).toFun x = (h k).toFun 0 := by
        exact fun k => ( h k ).flatL x hx;
      have h_eq : Filter.Tendsto (fun k => (h k).toFun x) Filter.atTop (nhds (g x)) ∧ Filter.Tendsto (fun k => (h k).toFun 0) Filter.atTop (nhds (g 0)) := by
        exact ⟨ hg.tendsto_at x, hg.tendsto_at 0 ⟩;
      exact tendsto_nhds_unique h_eq.1 ( by simp only [*] )
    have h_flatR : ∀ x ≥ 1, g x = g 1 := by
      intro x hx
      have h_eq : ∀ k, (h k).toFun x = (h k).toFun 1 := by
        exact fun k => ( h k ).flatR x hx;
      have h_eq : Filter.Tendsto (fun k => (h k).toFun x) Filter.atTop (nhds (g x)) ∧ Filter.Tendsto (fun k => (h k).toFun 1) Filter.atTop (nhds (g 1)) := by
        exact ⟨ hg.tendsto_at x, hg.tendsto_at 1 ⟩;
      exact tendsto_nhds_unique h_eq.1 ( by simp only [*] )
    use ⟨g, h_cadlag, h_bdd, h_flatL, h_flatR⟩;
  use hinf;
  rw [ Metric.tendstoUniformly_iff ] at hg;
  rw [ Metric.tendsto_nhds ];
  simp_all +decide [ dist_eq_norm ];
  intro ε hε; obtain ⟨ a, ha ⟩ := hg ( ε / 2 ) ( half_pos hε ) ; use a; intros b hb; rw [ abs_of_nonneg ( show 0 ≤ supDiff ( h b |> Skoro.toFun ) g from by apply Real.sSup_nonneg; rintro x ⟨ y, hy, rfl ⟩ ; exact abs_nonneg _ ) ] ; refine' lt_of_le_of_lt ( csSup_le _ _ ) ( half_lt_self hε );
  · exact ⟨ _, ⟨ 0, by norm_num, rfl ⟩ ⟩;
  · rintro x ⟨ y, hy, rfl ⟩ ; exact le_of_lt ( by simpa [ abs_sub_comm ] using ha b hb y ) ;

/-
The running inverse-compositions `ρ 0 = id`, `ρ (k+1) = (μ k).symm ∘ ρ k`, with uniform
log-slope bound `≤ 2`.
-/
theorem exists_rhoSeq (μ : ℕ → TimeChange) (hμfin : ∀ k, FiniteNorm (μ k))
    (hμnorm : ∀ k, logSlopeNorm (μ k) < (1/2:ℝ)^k) :
    ∃ ρ : ℕ → TimeChange, (∀ k, FiniteNorm (ρ k)) ∧
      (∀ x, (ρ 0).toFun x = TimeChange.id.toFun x) ∧
      (∀ k x, (ρ (k + 1)).toFun x = (μ k).symm.toFun ((ρ k).toFun x)) ∧
      (∀ k, logSlopeNorm (ρ k) ≤ 2) := by
  refine' ⟨ fun k => Nat.recOn k TimeChange.id fun k ih => ( μ k ).symm.comp ih, _, _, _, _ ⟩ <;> norm_num;
  · intro k; induction k <;> simp_all +decide [ finiteNorm_id, finiteNorm_comp, finiteNorm_symm ] ;
  · intro k
    have h_sum : logSlopeNorm (Nat.rec TimeChange.id (fun k ih => (μ k).symm.comp ih) k) ≤ ∑ j ∈ Finset.range k, logSlopeNorm (μ j) := by
      induction' k with k ih
      generalize_proofs at *;
      · convert logSlopeNorm_id.le;
      · rw [ Finset.sum_range_succ ];
        convert le_trans ( logSlopeNorm_comp_le _ _ _ _ ) _ using 1;
        · exact finiteNorm_symm _ ( hμfin k );
        · refine' Nat.recOn k _ _ <;> simp_all +decide [ finiteNorm_comp, finiteNorm_symm ];
          exact finiteNorm_id;
        · rw [ add_comm, logSlopeNorm_symm _ ( hμfin k ) ] ; linarith
    generalize_proofs at *;
    exact h_sum.trans ( le_trans ( Finset.sum_le_sum fun _ _ => le_of_lt ( hμnorm _ ) ) ( by simpa using sum_geometric_two_le k ) )

/-
The tail log-slope bound: the residual time change `ρ∞ ∘ (ρ k)⁻¹` has log-slope norm
`≤ 2·(1/2)^k → 0`.
-/
theorem logSlopeNorm_rhoInf_tail (μ ρ : ℕ → TimeChange) (rhoInf : TimeChange)
    (hμfin : ∀ j, FiniteNorm (μ j)) (hμnorm : ∀ j, logSlopeNorm (μ j) < (1/2:ℝ)^j)
    (hρfin : ∀ k, FiniteNorm (ρ k))
    (hρrec : ∀ k x, (ρ (k + 1)).toFun x = (μ k).symm.toFun ((ρ k).toFun x))
    (hρlim : ∀ x, x ∈ Set.Icc (0:ℝ) 1 →
      Tendsto (fun m => (ρ m).toFun x) atTop (𝓝 (rhoInf.toFun x))) :
    ∀ k, logSlopeNorm (rhoInf.comp (ρ k).symm) ≤ 2 * (1/2:ℝ)^k := by
  intro k
  set c := 2 * (1 / 2 : ℝ) ^ k
  have hN : 0 ≤ c := by
    positivity
  have hσfin : ∀ m, FiniteNorm ((ρ (k + m)).comp (ρ k).symm) := by
    exact fun m => finiteNorm_comp _ _ ( hρfin _ ) ( finiteNorm_symm _ ( hρfin _ ) )
  have hσnorm : ∀ m, logSlopeNorm ((ρ (k + m)).comp (ρ k).symm) ≤ c := by
    intro m
    have hsum : logSlopeNorm ((ρ (k + m)).comp (ρ k).symm) ≤ ∑ j ∈ Finset.Ico k (k + m), logSlopeNorm (μ j) := by
      apply logSlopeNorm_comp_tail μ ρ hμfin hρfin hρrec k (k + m) (by linarith)
    exact hsum.trans (by
    refine' le_trans ( Finset.sum_le_sum fun _ _ => le_of_lt ( hμnorm _ ) ) _;
    rw [ geom_sum_Ico ] <;> ring <;> norm_num;
    exact le_add_of_le_of_nonneg ( by linarith ) ( by positivity ))
  have hσconv : ∀ x ∈ Set.Icc 0 1, ∃ L, Filter.Tendsto (fun m => ((ρ (k + m)).comp (ρ k).symm).toFun x) Filter.atTop (nhds L) := by
    intro x hx
    use rhoInf.toFun ((ρ k).symm.toFun x);
    convert hρlim ( ( ρ k |> TimeChange.symm |> TimeChange.toFun ) x ) _ |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun m => Nat.le_add_left _ _ ) Filter.tendsto_id using 1;
    exact TimeChange.symmFun_mem_Icc ( ρ k ) hx
  have hrlim : ∃ rlim, FiniteNorm rlim ∧ logSlopeNorm rlim ≤ c ∧ ∀ x ∈ Set.Icc 0 1, Filter.Tendsto (fun m => ((ρ (k + m)).comp (ρ k).symm).toFun x) Filter.atTop (nhds (rlim.toFun x)) := by
    convert TimeChange.exists_limit ( fun m => ( ρ ( k + m ) ).comp ( ρ k ).symm ) c hN hσfin hσnorm hσconv using 1
  obtain ⟨rlim, hrlimfin, hrlimnorm, hrlimconv⟩ := hrlim
  have hrlimeq : rlim.toFun = (rhoInf.comp (ρ k).symm).toFun := by
    ext x; by_cases hx : x ≤ 0 <;> by_cases hx' : x ≥ 1 <;> simp_all +decide [ TimeChange.comp_apply ] ;
    · linarith;
    · have := rlim.flatL x hx; have := rhoInf.flatL ( ( ρ k ).symmFun x ) ( by
        grind +locals ) ; aesop;
    · convert rlim.flatR x hx' using 1;
      convert rhoInf.map_one' using 1;
      exact congr_arg _ ( TimeChange.symmFun_flatR _ ( by linarith ) );
    · convert tendsto_nhds_unique ( hrlimconv x hx.le hx'.le ) _ using 1;
      convert hρlim ( ( ρ k ).symmFun x ) _ _ |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun m => Nat.le_add_left _ _ ) Filter.tendsto_id using 1;
      · exact ( ρ k ).symmFun_mem_Icc ⟨ by linarith, by linarith ⟩ |>.1;
      · exact TimeChange.symmFun_mem_Icc _ ( by simp +decide [ hx.le, hx'.le ] ) |>.2
  have hlogSlopeNorm : logSlopeNorm (rhoInf.comp (ρ k).symm) = logSlopeNorm rlim := by
    exact logSlopeNorm_congr hrlimeq.symm
  exact hlogSlopeNorm.symm ▸ hrlimnorm



/-! ### Convergence API -/

/-
`λ`-characterization of `d°`-convergence (the brief's Tier 3(c)).
-/
theorem tendsto_iff_exists_timeChanges {F : ℕ → Skoro} {f : Skoro} :
    Tendsto F atTop (𝓝 f) ↔
      ∃ l : ℕ → TimeChange, (∀ n, FiniteNorm (l n)) ∧
        Tendsto (fun n => logSlopeNorm (l n)) atTop (𝓝 0) ∧
        Tendsto (fun n => supDiff (fun t => (F n) (l n t)) f) atTop (𝓝 0) := by
  constructor;
  · intro hF;
    have h_eps : ∀ k : ℕ, ∃ l : TimeChange, FiniteNorm l ∧ max (logSlopeNorm l) (supDiff (fun t => (F k).toFun (l.toFun t)) f.toFun) < dist (F k) f + 1 / (k + 1) := by
      intro k
      have h_inf : sInf (dCircSet (F k) f) < dist (F k) f + 1 / (k + 1) := by
        exact lt_add_of_le_of_pos ( by rfl ) ( by positivity )
      generalize_proofs at *; (
      exact Exists.elim ( exists_lt_of_csInf_lt ( dCircSet_nonempty ( F k ) f ) h_inf ) fun x hx => by rcases hx.1 with ⟨ l, hl₁, rfl ⟩ ; exact ⟨ l, hl₁, hx.2 ⟩ ;);
    choose l hl using h_eps;
    refine' ⟨ l, fun n => hl n |>.1, squeeze_zero ( fun n => logSlopeNorm_nonneg _ ( hl n |>.1 ) ) ( fun n => le_max_left _ _ |> le_trans <| le_of_lt <| hl n |>.2 ) _, squeeze_zero ( fun n => supDiff_nonneg _ _ ) ( fun n => le_max_right _ _ |> le_trans <| le_of_lt <| hl n |>.2 ) _ ⟩; all_goals simpa using Filter.Tendsto.add ( tendsto_iff_dist_tendsto_zero.mp hF ) ( tendsto_one_div_add_atTop_nhds_zero_nat );
  · intro h
    obtain ⟨l, hl_fin, hl_log, hl_sup⟩ := h
    have h_dCirc : ∀ n, dCirc (F n) f ≤ max (logSlopeNorm (l n)) (supDiff (fun t => (F n).toFun ((l n).toFun t)) f.toFun) := by
      exact fun n => csInf_le ( dCircSet_bddBelow _ _ ) ⟨ l n, hl_fin n, rfl ⟩
    generalize_proofs at *; (
    exact tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => dCirc_nonneg _ _ ) ( fun n => dist_eq_dCirc _ _ ▸ h_dCirc n ) ( by simpa using Filter.Tendsto.max hl_log hl_sup ))

/-
Uniform convergence (sup over `[0,1]`) implies `J₁` (`d°`) convergence.
-/
theorem tendsto_of_tendstoUniformly {F : ℕ → Skoro} {f : Skoro}
    (h : Tendsto (fun n => supDiff (fun t => (F n) t) f) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 f) := by
  convert tendsto_iff_dist_tendsto_zero.mpr _;
  refine' squeeze_zero ( fun n => _ ) ( fun n => _ ) h;
  · exact dist_nonneg;
  · convert dCirc_le_supDiff ( F n ) f using 1

/-
Evaluation `f ↦ f t` is continuous at every `f` that is continuous at `t ∈ (0,1)`.
-/
theorem continuousAt_eval {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1) {f : Skoro}
    (hf : ContinuousAt f.toFun t) :
    ContinuousAt (fun g : Skoro => g.toFun t) f := by
  rw [ Metric.continuousAt_iff ] at *;
  intro ε hε
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ : ∃ δ₀ > 0, ∀ ⦃x : ℝ⦄, dist x t < δ₀ → dist (f.toFun x) (f.toFun t) < ε / 2 := hf (ε / 2) (half_pos hε)
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, δ < ε / 2 ∧ Real.exp δ - 1 < δ₀ := by
    have := Metric.continuousAt_iff.mp ( show ContinuousAt ( fun x => Real.exp x - 1 ) 0 by exact ContinuousAt.sub ( Real.continuous_exp.continuousAt ) continuousAt_const ) δ₀ hδ₀_pos; norm_num at *;
    obtain ⟨ δ, hδ₁, hδ₂ ⟩ := this; exact ⟨ Min.min δ ( ε / 4 ) / 2, by positivity, by linarith [ min_le_left δ ( ε / 4 ), min_le_right δ ( ε / 4 ) ], by linarith [ abs_lt.mp ( hδ₂ ( show |Min.min δ ( ε / 4 ) / 2| < δ by rw [ abs_of_nonneg ( by positivity ) ] ; linarith [ min_le_left δ ( ε / 4 ), min_le_right δ ( ε / 4 ) ] ) ) ] ⟩ ;
  refine' ⟨ δ, hδ_pos, fun g hg => _ ⟩;
  -- By definition of $dCirc$, there exists a time change $l$ such that $FiniteNorm l$ and $max (logSlopeNorm l) (supDiff (fun s => g (l s)) f) < δ$.
  obtain ⟨ l, hl₁, hl₂ ⟩ : ∃ l : TimeChange, FiniteNorm l ∧ max (logSlopeNorm l) (supDiff (fun s => g (l s)) f) < δ := by
    exact exists_lt_of_csInf_lt ( dCircSet_nonempty g f ) hg |> fun ⟨ x, hx₁, hx₂ ⟩ => by rcases hx₁ with ⟨ l, hl₁, rfl ⟩ ; exact ⟨ l, hl₁, hx₂ ⟩ ;
  -- Set $s₀ = l.symm t ∈ Icc 0 1$.
  set s₀ := l.symm t with hs₀_def;
  have hs₀_mem : s₀ ∈ Set.Icc (0:ℝ) 1 := by
    exact l.symmFun_mem_Icc ⟨ ht.1.le, ht.2.le ⟩;
  have hs₀_t : l.toFun s₀ = t := by
    exact TimeChange.apply_symmFun l ⟨ ht.1.le, ht.2.le ⟩;
  have hs₀_dist : |s₀ - t| ≤ Real.exp (logSlopeNorm l) - 1 := by
    convert timeChange_dist_id_le l.symm ( finiteNorm_symm l hl₁ ) _ using 1;
    · rw [ logSlopeNorm_symm l hl₁ ];
    · exact ⟨ ht.1.le, ht.2.le ⟩;
  have hs₀_dist_lt : |s₀ - t| < δ₀ := by
    exact lt_of_le_of_lt hs₀_dist ( by linarith [ Real.exp_le_exp.mpr ( show logSlopeNorm l ≤ δ by linarith [ le_max_left ( logSlopeNorm l ) ( supDiff ( fun s => g.toFun ( l.toFun s ) ) f.toFun ) ] ) ] );
  have hs₀_f_dist : |f.toFun s₀ - f.toFun t| < ε / 2 := by
    exact hδ₀ hs₀_dist_lt;
  have hs₀_g_dist : |g.toFun t - f.toFun s₀| ≤ supDiff (fun s => g.toFun (l.toFun s)) f := by
    exact le_csSup ( Skoro.bddAbove_comp_supDiffSet g f l ) ⟨ s₀, hs₀_mem, by aesop ⟩;
  have hs₀_g_dist_lt : |g.toFun t - f.toFun s₀| < δ := by
    exact lt_of_le_of_lt hs₀_g_dist ( lt_of_le_of_lt ( le_max_right _ _ ) hl₂ );
  have hs₀_g_dist_lt_final : |g.toFun t - f.toFun t| < ε := by
    exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp hs₀_g_dist_lt, abs_lt.mp hs₀_f_dist ], by linarith [ abs_lt.mp hs₀_g_dist_lt, abs_lt.mp hs₀_f_dist ] ⟩;
  exact hs₀_g_dist_lt_final;

/-- Constant paths embed isometrically. -/
def const (c : ℝ) : Skoro where
  toFun := fun _ => c
  cadlag' := ⟨fun _ _ => continuousWithinAt_const, fun _ _ => ⟨c, tendsto_const_nhds⟩⟩
  bdd' := ⟨|c|, fun _ _ => le_refl _⟩
  flatL := fun _ _ => rfl
  flatR := fun _ _ => rfl

theorem dCirc_const (c d : ℝ) : dCirc (const c) (const d) = |c - d| := by
  refine' le_antisymm _ _;
  · refine' csInf_le _ _;
    · exact ⟨ 0, fun x hx => by rcases hx with ⟨ l, hl, rfl ⟩ ; exact le_max_of_le_left ( logSlopeNorm_nonneg l hl ) ⟩;
    · refine' ⟨ TimeChange.id, finiteNorm_id, _ ⟩ ; norm_num [ logSlopeNorm_id, supDiff ];
      unfold supDiffSet; norm_num [ const ] ;
      rw [ show { r : ℝ | ( ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ) ∧ r = |c - d| } = { |c - d| } by rw [ Set.eq_singleton_iff_unique_mem ] ; exact ⟨ ⟨ ⟨ 0, by norm_num, by norm_num ⟩, rfl ⟩, by rintro x ⟨ ⟨ y, hy₀, hy₁ ⟩, rfl ⟩ ; rfl ⟩ ] ; norm_num;
  · refine' le_csInf _ _;
    · exact ⟨ _, ⟨ TimeChange.id, finiteNorm_id, rfl ⟩ ⟩;
    · rintro _ ⟨ l, hl, rfl ⟩ ; exact le_max_of_le_right <| le_csSup ( show BddAbove ( supDiffSet ( fun t => ( const c ) ( l t ) ) ( const d ) ) from by
                                                                        exact ⟨ |c - d|, by rintro x ⟨ t, ht, rfl ⟩ ; exact le_of_eq ( by unfold const; aesop ) ⟩ ) ⟨ 0, by norm_num, rfl ⟩

/-! ### Numerical sanity (catch definition errors early) -/

/-- A unit step function jumping at `a ∈ (0,1)`. -/
def step (a : ℝ) : ℝ → ℝ := fun t => if a ≤ t then 1 else 0

theorem isCadlag_step {a : ℝ} (ha : a ∈ Set.Ioo (0:ℝ) 1) : IsCadlag (step a) := by
  constructor;
  · simp +zetaDelta at *;
    intro t ht₁ ht₂; by_cases h : a ≤ t <;> simp_all +decide [ ContinuousWithinAt ] ;
    · exact tendsto_const_nhds.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ step, step ] ; split_ifs <;> linarith [ hx.out ] );
    · rw [ Metric.tendsto_nhdsWithin_nhds ];
      intro ε hε; use a - t; exact ⟨ by linarith, fun x hx₁ hx₂ => by rw [ show step a x = 0 by exact if_neg <| by linarith [ abs_lt.mp hx₂, hx₁.out ] ] ; rw [ show step a t = 0 by exact if_neg <| by linarith [ abs_lt.mp hx₂, hx₁.out ] ] ; simpa ⟩ ;
  · intro t ht; by_cases h : t ≤ a <;> simp_all +decide ;
    · exact ⟨ 0, tendsto_const_nhds.congr' <| Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ step ] ; split_ifs <;> linarith [ hx.out ] ⟩;
    · exact ⟨ 1, tendsto_const_nhds.congr' <| Filter.eventuallyEq_of_mem ( Ioo_mem_nhdsLT h ) fun x hx => by rw [ step, if_pos hx.1.le ] ⟩

end

end SkorokhodBasic