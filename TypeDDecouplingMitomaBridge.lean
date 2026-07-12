/-
# Mitoma campaign, task 4 — bridges (Part A)

This file assembles the real Mitoma Theorem 4.1 (Kallianpur–Xiong compact-confinement
form) `mitoma_tightness` out of:

* the Skorokhod campaign's `Skoro`/`supNorm`/`IsTightMeasureSet` theory
  (`TypeDDecouplingSkorokhodTight`, `TypeDDecouplingSkorokhodBasic`);
* M3c's uniform dual-ball confinement `mitoma_confinement`
  (`TypeDDecouplingMitomaCore`), together with M2's `polarBall`/`isCompact_polarBall`.

The three ingredients of the brief:

* (A1) `tight_supNorm_tail` — `IsTightMeasureSet` on `Skoro` gives uniform sup-norm tail
  bounds (compact ⇒ `supNorm`-bounded via continuity of `supNorm`);
* (A2) `mem_polarBall_of_denseTimes` — dense-time upgrade: confinement on the rationals
  of `[0,1]` upgrades to all of `[0,1]` by right-approximation, using càdlàg paths and the
  pointwise description of `polarBall`;
* (A3) `mitoma_tightness` — the assembly: per-`φ` Skorokhod tightness of the pairing
  path processes `Y^φ_N` ⇒ uniform compact confinement of `Z_N` on `[0,1]`.
-/
import Mathlib
import TypeDDecouplingMitomaCore
import TypeDDecouplingSkorokhodTight

open MeasureTheory Filter SchwartzMap SkorokhodBasic TypeDDecouplingMitomaCore
open scoped Real Topology ENNReal NNReal

noncomputable section

namespace TypeDDecouplingMitomaBridge

/-! ## (A1) Tightness ⇒ uniform sup-norm tail bounds -/

/-- `supNorm` is bounded above on any compact subset of `Skoro`
(continuity of `supNorm` + compactness). -/
lemma exists_supNorm_bound_of_isCompact {K : Set Skoro} (hK : IsCompact K) :
    ∃ a : ℝ, ∀ f ∈ K, supNorm f ≤ a := by
  rcases (hK.image continuous_supNorm).bddAbove with ⟨a, ha⟩
  exact ⟨a, fun f hf => ha ⟨f, hf, rfl⟩⟩

/-- **(A1)** For a tight family of measures on `Skoro`, the sup-norm tails are uniformly
small: for each `ε > 0` there is a threshold `a` with `μ {f | a ≤ supNorm f} ≤ ε` for every
`μ` in the family. -/
lemma tight_supNorm_tail {S : Set (Measure Skoro)}
    (hS : IsTightMeasureSet S) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ a : ℝ, ∀ μ ∈ S, μ {f : Skoro | a ≤ supNorm f} ≤ ε := by
  obtain ⟨K, hKc, hKmass⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hS) ε hε
  obtain ⟨a0, ha0⟩ := exists_supNorm_bound_of_isCompact hKc
  refine ⟨a0 + 1, fun μ hμ => le_trans (measure_mono ?_) (hKmass μ hμ)⟩
  intro f hf
  simp only [Set.mem_setOf_eq] at hf
  simp only [Set.mem_compl_iff]
  intro hfK
  have := ha0 f hfK
  linarith

/-! ## (A2) Dense-time upgrade -/

/-
A rational sequence approaching `t ∈ [0,1)` strictly from the right, staying in `[0,1]`.
-/
lemma exists_rat_seq_right {t : ℝ} (ht : t ∈ Set.Ico (0:ℝ) 1) :
    ∃ s : ℕ → ℚ, (∀ n, ((s n : ℝ)) ∈ Set.Icc (0:ℝ) 1) ∧ (∀ n, t ≤ (s n : ℝ)) ∧
      Tendsto (fun n => ((s n : ℝ))) atTop (𝓝 t) := by
  -- By the density of rationals in reals, for each n, there exists a rational number s_n such that t < s_n < t + 1/(n+1).
  have h_dense : ∀ n : ℕ, ∃ s_n : ℚ, t < s_n ∧ s_n < t + 1 / (n + 1) ∧ s_n ∈ Set.Icc 0 1 := by
    intro n
    obtain ⟨s_n, hs_n⟩ : ∃ s_n : ℚ, t < s_n ∧ s_n < min 1 (t + 1 / (n + 1)) := by
      exact exists_rat_btwn ( lt_min ht.2 ( lt_add_of_pos_right _ ( by positivity ) ) );
    exact ⟨ s_n, hs_n.1, hs_n.2.trans_le ( min_le_right _ _ ), ⟨ by exact_mod_cast hs_n.1.le.trans' ht.1, by exact_mod_cast hs_n.2.le.trans ( min_le_left _ _ ) ⟩ ⟩;
  choose s hs using h_dense;
  exact ⟨ s, fun n => hs n |>.2.2 |> fun h => ⟨ mod_cast h.1, mod_cast h.2 ⟩, fun n => le_of_lt ( hs n |>.1 ), tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => abs_le.mpr ⟨ by linarith [ hs n |>.1, hs n |>.2.1 ], by linarith [ hs n |>.1, hs n |>.2.1 ] ⟩ ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩

/-
**(A2)** Dense-time upgrade. Let `g : ℝ → SchDual` be a distribution-valued path whose
pairings `t ↦ g t φ` agree, on `[0,1]`, with the càdlàg `Skoro` path `path φ`. If `g` is
confined to the (pointwise) polar ball `polarBall q'` at every rational time in `[0,1]`, then
it is confined at every `t ∈ [0,1]`.
-/
lemma mem_polarBall_of_denseTimes
    {q' : Seminorm ℝ (𝓢(ℝ, ℝ))}
    {g : ℝ → SchDual}
    (path : (𝓢(ℝ, ℝ)) → Skoro)
    (hpath : ∀ (φ : 𝓢(ℝ, ℝ)) t, t ∈ Set.Icc (0:ℝ) 1 → (path φ).toFun t = g t φ)
    (hconf : ∀ r : ℚ, (r:ℝ) ∈ Set.Icc (0:ℝ) 1 → g (r:ℝ) ∈ polarBall q')
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    g t ∈ polarBall q' := by
  by_cases h : t = 1;
  · simpa [ h ] using hconf 1 ⟨ by norm_num, by norm_num ⟩;
  · -- By `exists_rat_seq_right`, there exists a sequence `s : ℕ → ℚ` such that `s n ∈ (0,1]`, `t ≤ s n`, and `s n → t`.
    obtain ⟨s, hs_mem, hs_ge, hs_lim⟩ : ∃ s : ℕ → ℚ, (∀ n, ((s n : ℝ)) ∈ Set.Icc (0:ℝ) 1) ∧ (∀ n, t ≤ (s n : ℝ)) ∧ Tendsto (fun n => ((s n : ℝ))) atTop (𝓝 t) := exists_rat_seq_right ⟨ht.left, lt_of_le_of_ne ht.right h⟩;
    -- Since `path φ` is right-continuous at `t`, we have `Tendsto (fun n => (path φ).toFun (s n:ℝ)) atTop (𝓝 ((path φ).toFun t))`.
    have h_right_cont : ∀ φ : 𝓢(ℝ, ℝ), Tendsto (fun n => (path φ).toFun (s n : ℝ)) atTop (𝓝 ((path φ).toFun t)) := by
      intro φ
      have h_right_cont : ContinuousWithinAt (fun r => (path φ).toFun r) (Set.Ici t) t := by
        exact ( path φ ).cadlag'.1 t ⟨ ht.1, lt_of_le_of_ne ht.2 h ⟩;
      exact h_right_cont.tendsto.comp ( Filter.tendsto_inf.mpr ⟨ hs_lim, Filter.tendsto_principal.mpr <| Filter.Eventually.of_forall hs_ge ⟩ );
    simp_all +decide [ SchwartzMap.mem_polarBall ];
    exact fun φ => le_of_tendsto' ( Filter.Tendsto.abs ( h_right_cont φ ) ) fun n => hconf _ ( mod_cast hs_mem n |>.1 ) ( mod_cast hs_mem n |>.2 ) _

/-! ## (A3) The real Mitoma Theorem 4.1 (Kallianpur–Xiong form) -/

/-- **(A3) `mitoma_tightness`.** The real Mitoma tightness criterion in
compact-confinement (Kallianpur–Xiong) form. Data: probability spaces `(Ω N, P N)`,
distribution-valued processes `Z N : ℝ → Ω N → SchDual` with measurable evaluations, and for
each test function `φ` a *path process* `Y φ N : Ω N → Skoro` (an honest càdlàg `D([0,1],ℝ)`
element) whose values realize the real pairings `t ↦ ⟨Z_N(t), φ⟩` on `[0,1]` (`hY`).

If, for every `φ`, the family of laws `{(P N).map (Y φ N)}_N` is `IsTightMeasureSet` on
`Skoro`, then for every `η > 0` there are `q, B > 0` with `K = polarBall (B • ‖·‖_{q+1})`
compact and, uniformly in `N`, `P_N(∃ t ∈ [0,1], Z_N(t) ∉ K) ≤ η`.

Proof: (A1) converts per-`φ` tightness into M3c's hypothesis (H) over the rationals of
`[0,1]`; `mitoma_confinement` gives confinement over that countable dense set; (A2) upgrades
the confinement to all of `[0,1]` via right-continuity of the càdlàg paths. -/
theorem mitoma_tightness
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    (Z : ∀ N, ℝ → Ω N → SchDual)
    (Y : (𝓢(ℝ, ℝ)) → ∀ N, Ω N → Skoro)
    (hmeas : ∀ (N : ℕ) (t : ℝ) (φ : 𝓢(ℝ, ℝ)), Measurable (fun ω => Z N t ω φ))
    (hYmeas : ∀ (φ : 𝓢(ℝ, ℝ)) (N : ℕ), Measurable (Y φ N))
    (hY : ∀ (φ : 𝓢(ℝ, ℝ)) (N : ℕ) (ω : Ω N) (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 →
        (Y φ N ω).toFun t = Z N t ω φ)
    (htight : ∀ φ : 𝓢(ℝ, ℝ),
        IsTightMeasureSet (Set.range (fun N => (P N).map (Y φ N))))
    (η : ℝ) (hη : 0 < η) :
    ∃ (q : ℕ) (B : ℝ), 0 < B ∧
      IsCompact (polarBall (B.toNNReal • sobolevSeminormB (q + 1))) ∧
      ∀ N, ((P N) {ω | ∃ t ∈ Set.Icc (0:ℝ) 1,
        Z N t ω ∉ polarBall (B.toNNReal • sobolevSeminormB (q + 1))}).toReal ≤ η := by
  classical
  haveI : Nonempty {r : ℚ // (r:ℝ) ∈ Set.Icc (0:ℝ) 1} := ⟨⟨1, by norm_num⟩⟩
  set Zt : ∀ N, {r : ℚ // (r:ℝ) ∈ Set.Icc (0:ℝ) 1} → Ω N → SchDual :=
    fun N s ω => Z N (s.1 : ℝ) ω with hZt
  have hmeas' : ∀ N s φ, Measurable (fun ω => Zt N s ω φ) := fun N s φ => hmeas N (s.1 : ℝ) φ
  -- hypothesis (H): per-φ uniform sup-tightness over the countable dense time set
  have H : ∀ (φ : 𝓢(ℝ, ℝ)) (ε : ℝ), 0 < ε → ∃ a : ℝ, 0 < a ∧
      ∀ N, (P N) {ω | ∃ s : {r : ℚ // (r:ℝ) ∈ Set.Icc (0:ℝ) 1}, a < |Zt N s ω φ|}
        ≤ ENNReal.ofReal ε := by
    intro φ ε hε
    obtain ⟨a0, ha0⟩ := tight_supNorm_tail (htight φ) (ε := ENNReal.ofReal ε)
      (ENNReal.ofReal_pos.mpr hε)
    refine ⟨max a0 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun N => ?_⟩
    have hmap : (P N).map (Y φ N) ∈ Set.range (fun N => (P N).map (Y φ N)) := ⟨N, rfl⟩
    have hms : MeasurableSet {f : Skoro | a0 ≤ supNorm f} :=
      measurable_supNorm measurableSet_Ici
    have hkey := ha0 _ hmap
    rw [Measure.map_apply (hYmeas φ N) hms] at hkey
    refine le_trans (measure_mono ?_) hkey
    intro ω hω
    obtain ⟨s, hs⟩ := hω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have hval : Zt N s ω φ = (Y φ N ω).toFun (s.1 : ℝ) := (hY φ N ω (s.1 : ℝ) s.2).symm
    have hle : |Zt N s ω φ| ≤ supNorm (Y φ N ω) := by
      rw [hval]; exact abs_le_supNorm _ s.2
    have hlt : max a0 1 < supNorm (Y φ N ω) := lt_of_lt_of_le hs hle
    linarith [le_max_left a0 1]
  -- M3c confinement over the countable dense time set
  obtain ⟨q, B, hB0, hcompact, hconf⟩ :=
    TypeDDecouplingMitomaCore.mitoma_confinement P Zt hmeas' H η hη
  refine ⟨q, B, hB0, hcompact, fun N => ?_⟩
  refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)) (hconf N)
  -- (A2) upgrade to all of [0,1]
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  obtain ⟨t, ht, htK⟩ := hω
  by_contra hcon
  push_neg at hcon
  exact htK (mem_polarBall_of_denseTimes (fun φ => Y φ N ω)
    (fun φ t ht => hY φ N ω t ht) (fun r hr => hcon ⟨r, hr⟩) ht)

end TypeDDecouplingMitomaBridge