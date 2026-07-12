import Mathlib

/-!
# Tier A finite-algebra lemmas: equal-time variance (`lem:eqvar`) and orthogonality (`lem:orth`)

This file gives a self-contained, `sorry`-free formalisation of the two Tier-A finite-algebra
lemmas of the type-D ASEP decoupling paper, following `tierA_eqvar_orth.tex` and the
conventions of `TypeDDecouplingDressedMass.lean`.

## Set-up

A finite lattice `Λ ⊆ ℤ`, two species of `{0,1}`-valued occupations, and a parameter `q`.
A configuration `c : Config Λ = {x // x ∈ Λ} → Fin 2 → Bool` records, for each lattice site
and species, whether that site is occupied.  The real occupation variable is `bocc i x c`
(`= 1` if species `i` occupies site `x`, else `0`; `0` off the window).  The single-species
bond factor `φⁱ_z`, the bond cross term `V_z = φ⁰_z φ¹_z` and the block-product (blocking)
weight `W(c) = ∏ₓ ∏ᵢ (αᵢ q^{-2x})^{ζ_{i,x}}` are `phi`, `Vb` and `Wb`.

## Key idea: a sign-reversing involution

For a species `s` and a bond `(z, z+1)`, the involution `swapC s z z+1` swaps the species-`s`
occupations at the two bond sites.  The central fact (`pointwise_antisym`) is the *pointwise*
identity
`W(σ c) · V_z(σ c) = − W(c) · V_z(c)`,
which holds because the blocking weight changes by exactly `q^{±2}` under the swap while the
bond factor changes sign.  Summing over the (finite) configuration space and re-indexing by the
involution gives, for any `σ`-invariant `f`,
`∑_c W(c) · V_z(c) · f(c) = 0`   (`expect_Vf_zero`).

From this single mechanism we obtain, with no analysis:

* `expect_V_eq_zero`      : `E[V_z] = 0`                    (Lemma `lem:eqvar` (i));
* `expect_V_mul_occ_eq_zero` : `E[V_z · η_{i,y}] = 0`      (the mass-1 case of `lem:orth`);
* `expect_V_mul_V_eq_zero`  : `E[V_x V_y] = 0` for `|x−y| ≥ 2`  (Lemma `lem:eqvar` (ii)).

Combined with `Vb_abs_le_one` (`|V_z| ≤ 1`, Lemma `lem:eqvar` (iii)) these give the
equal-time variance bound `eqvar_bound`.

The fugacities `αᵢ` are kept as a general positive vector; the identities in fact hold for any
`αᵢ`, since the detailed-balance ratios are `α`-independent.
-/

open scoped BigOperators

namespace TypeDDecoupling.EqvarOrth

/-- The finite configuration space: for each site of `Λ` and each species, a `{0,1}` occupation. -/
abbrev Config (Λ : Finset ℤ) : Type := {x : ℤ // x ∈ Λ} → Fin 2 → Bool

variable (Λ : Finset ℤ)

/-- The real-valued species-`i` occupation at site `x` (`0` off the window). -/
noncomputable def bocc (i : Fin 2) (x : ℤ) (c : Config Λ) : ℝ :=
  if h : x ∈ Λ then (if c ⟨x, h⟩ i then (1 : ℝ) else 0) else 0

/-- Single-site blocking factor `∏ᵢ (αᵢ q^{-2x})^{ζᵢ}`. -/
noncomputable def siteFac (q : ℝ) (alpha : Fin 2 → ℝ) (x : ℤ) (b : Fin 2 → Bool) : ℝ :=
  ∏ i, (if b i then alpha i * q ^ (-2 * x) else 1)

/-- The blocking (block-product) weight `W(c) = ∏ₛ siteFac`. -/
noncomputable def Wb (q : ℝ) (alpha : Fin 2 → ℝ) (c : Config Λ) : ℝ :=
  ∏ s : {x // x ∈ Λ}, siteFac q alpha (s : ℤ) (c s)

/-- Single-species bond factor `φⁱ_z = η_{i,z} − q² η_{i,z+1} − (1−q²) η_{i,z} η_{i,z+1}`. -/
noncomputable def phi (q : ℝ) (i : Fin 2) (z : ℤ) (c : Config Λ) : ℝ :=
  bocc Λ i z c - q ^ 2 * bocc Λ i (z + 1) c - (1 - q ^ 2) * (bocc Λ i z c * bocc Λ i (z + 1) c)

/-- The bond cross term `V_z = φ⁰_z φ¹_z`. -/
noncomputable def Vb (q : ℝ) (z : ℤ) (c : Config Λ) : ℝ := phi Λ q 0 z c * phi Λ q 1 z c

/-- The involution swapping species-`s0` occupations at sites `a` and `b`. -/
noncomputable def swapC (s0 : Fin 2) (a b : {x // x ∈ Λ}) (c : Config Λ) : Config Λ :=
  fun t => if t = a then Function.update (c a) s0 (c b s0)
           else if t = b then Function.update (c b) s0 (c a s0) else c t

/-- Bond-only cross-term value as a function of the two bond occupations. -/
noncomputable def VbBexpr (q : ℝ) (bz bz1 : Fin 2 → Bool) : ℝ :=
  ((if bz 0 then (1 : ℝ) else 0) - q ^ 2 * (if bz1 0 then 1 else 0)
      - (1 - q ^ 2) * ((if bz 0 then 1 else 0) * (if bz1 0 then 1 else 0)))
    * ((if bz 1 then (1 : ℝ) else 0) - q ^ 2 * (if bz1 1 then 1 else 0)
      - (1 - q ^ 2) * ((if bz 1 then 1 else 0) * (if bz1 1 then 1 else 0)))

/-! ## The bond-only antisymmetry (finite algebra) -/

set_option maxHeartbeats 4000000 in
/-- The bond-only sign-reversal identity: multiplying the two swapped bond weights by the swapped
bond cross-term gives minus the unswapped product.  This is the exact detailed-balance
cancellation `(1, q^{-4}, q^{-2}, q^{-2}) · (1, q⁴, −q², −q²) → (+,+,−,−)`. -/
theorem bondcore (q : ℝ) (hq : q ≠ 0) (alpha : Fin 2 → ℝ) (s0 : Fin 2) (z : ℤ)
    (ca cb : Fin 2 → Bool) :
    siteFac q alpha z (Function.update ca s0 (cb s0))
        * siteFac q alpha (z + 1) (Function.update cb s0 (ca s0))
        * VbBexpr q (Function.update ca s0 (cb s0)) (Function.update cb s0 (ca s0))
      = - (siteFac q alpha z ca * siteFac q alpha (z + 1) cb * VbBexpr q ca cb) := by
  have hz : q ^ (-2 * z) = q ^ 2 * q ^ (-2 * (z + 1)) := by
    rw [show (-2 * z) = 2 + (-2 * (z + 1)) by ring, zpow_add₀ hq]; norm_cast
  unfold siteFac VbBexpr
  fin_cases s0 <;>
  · simp only [Fin.mk_zero, Fin.mk_one, Fin.prod_univ_two, Fin.isValue, Function.update_self,
      Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide),
      Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
    cases ca 0 <;> cases ca 1 <;> cases cb 0 <;> cases cb 1 <;>
      simp only [if_true, if_false, Bool.false_eq_true, hz] <;> ring

/-! ## Basic evaluation lemmas for `swapC` -/

lemma swapC_at_a (s0 : Fin 2) (a b : {x // x ∈ Λ}) (c : Config Λ) :
    swapC Λ s0 a b c a = Function.update (c a) s0 (c b s0) := by simp [swapC]

lemma swapC_at_b (s0 : Fin 2) (a b : {x // x ∈ Λ}) (hab : a ≠ b) (c : Config Λ) :
    swapC Λ s0 a b c b = Function.update (c b) s0 (c a s0) := by simp [swapC, Ne.symm hab]

lemma swapC_at_other (s0 : Fin 2) (a b : {x // x ∈ Λ}) (c : Config Λ) (t : {x // x ∈ Λ})
    (hta : t ≠ a) (htb : t ≠ b) : swapC Λ s0 a b c t = c t := by simp [swapC, hta, htb]

/-- `swapC` is an involution. -/
lemma swapC_invol (s0 : Fin 2) (a b : {x // x ∈ Λ}) (hab : a ≠ b) :
    Function.Involutive (swapC Λ s0 a b) := by
  intro c
  funext t
  by_cases hta : t = a
  · subst hta
    rw [swapC_at_a, swapC_at_a, swapC_at_b _ _ _ _ hab, Function.update_self,
      Function.update_idem, Function.update_eq_self]
  · by_cases htb : t = b
    · subst htb
      rw [swapC_at_b _ _ _ _ hab, swapC_at_b _ _ _ _ hab, swapC_at_a, Function.update_self,
        Function.update_idem, Function.update_eq_self]
    · rw [swapC_at_other _ _ _ _ _ _ hta htb, swapC_at_other _ _ _ _ _ _ hta htb]

/-! ## The pointwise sign-reversal identity -/

/-- **Pointwise antisymmetry.**  `W(σ c) · V_z(σ c) = − W(c) · V_z(c)`, where `σ = swapC s0 z z+1`.
Here `⟨z, hz⟩` and `⟨z+1, hz1⟩` are the two bond sites. -/
theorem pointwise_antisym (q : ℝ) (hq : q ≠ 0) (alpha : Fin 2 → ℝ) (s0 : Fin 2) (z : ℤ)
    (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (c : Config Λ) :
    Wb Λ q alpha (swapC Λ s0 ⟨z, hz⟩ ⟨z + 1, hz1⟩ c) * Vb Λ q z (swapC Λ s0 ⟨z, hz⟩ ⟨z + 1, hz1⟩ c)
      = - (Wb Λ q alpha c * Vb Λ q z c) := by
  set a : {x // x ∈ Λ} := ⟨z, hz⟩ with ha
  set b : {x // x ∈ Λ} := ⟨z + 1, hz1⟩ with hb
  have hab : a ≠ b := by simp only [ha, hb, ne_eq, Subtype.mk.injEq]; omega
  have hoff : ∀ t ∈ (Finset.univ \ {a, b}), swapC Λ s0 a b c t = c t := by
    intro t ht
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at ht
    push_neg at ht
    simp [swapC, ht.2.1, ht.2.2]
  have σa : swapC Λ s0 a b c a = Function.update (c a) s0 (c b s0) := by simp [swapC]
  have σb : swapC Λ s0 a b c b = Function.update (c b) s0 (c a s0) := by simp [swapC, Ne.symm hab]
  have hP : (∏ s ∈ (Finset.univ \ {a, b}), siteFac q alpha (s : ℤ) (swapC Λ s0 a b c s))
      = ∏ s ∈ (Finset.univ \ {a, b}), siteFac q alpha (s : ℤ) (c s) :=
    Finset.prod_congr rfl (fun t ht => by rw [hoff t ht])
  have hWc : Wb Λ q alpha c = siteFac q alpha (a : ℤ) (c a) * siteFac q alpha (b : ℤ) (c b)
      * ∏ s ∈ (Finset.univ \ {a, b}), siteFac q alpha (s : ℤ) (c s) := by
    unfold Wb; rw [← Finset.prod_sdiff (Finset.subset_univ {a, b}), Finset.prod_pair hab]; ring
  have hWs : Wb Λ q alpha (swapC Λ s0 a b c)
      = siteFac q alpha (a : ℤ) (Function.update (c a) s0 (c b s0))
        * siteFac q alpha (b : ℤ) (Function.update (c b) s0 (c a s0))
        * ∏ s ∈ (Finset.univ \ {a, b}), siteFac q alpha (s : ℤ) (c s) := by
    unfold Wb
    rw [← Finset.prod_sdiff (Finset.subset_univ {a, b}), Finset.prod_pair hab, hP, σa, σb]; ring
  have bocc_a : ∀ (i : Fin 2) (c' : Config Λ), bocc Λ i z c' = if c' a i then (1 : ℝ) else 0 := by
    intro i c'; rw [ha]; simp [bocc, hz]
  have bocc_b : ∀ (i : Fin 2) (c' : Config Λ),
      bocc Λ i (z + 1) c' = if c' b i then (1 : ℝ) else 0 := by
    intro i c'; rw [hb]; simp [bocc, hz1]
  have hVc : Vb Λ q z c = VbBexpr q (c a) (c b) := by
    simp only [Vb, phi, bocc_a, bocc_b, VbBexpr]
  have hVs : Vb Λ q z (swapC Λ s0 a b c)
      = VbBexpr q (Function.update (c a) s0 (c b s0)) (Function.update (c b) s0 (c a s0)) := by
    simp only [Vb, phi, bocc_a, bocc_b, σa, σb, VbBexpr]
  have hca : (a : ℤ) = z := rfl
  have hcb : (b : ℤ) = z + 1 := rfl
  rw [hWs, hWc, hVs, hVc, hca, hcb]
  have BC := bondcore q hq alpha s0 z (c a) (c b)
  linear_combination (∏ s ∈ (Finset.univ \ {a, b}), siteFac q alpha (s : ℤ) (c s)) * BC

/-! ## The master vanishing lemma -/

/-- **Master vanishing lemma.**  For any function `f` invariant under the species-`s0`
bond swap, `∑_c W(c) · V_z(c) · f(c) = 0`. -/
theorem expect_Vf_zero [Fintype {x // x ∈ Λ}] (q : ℝ) (hq : q ≠ 0) (alpha : Fin 2 → ℝ)
    (s0 : Fin 2) (z : ℤ) (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (f : Config Λ → ℝ)
    (hfinv : ∀ c, f (swapC Λ s0 ⟨z, hz⟩ ⟨z + 1, hz1⟩ c) = f c) :
    ∑ c, Wb Λ q alpha c * Vb Λ q z c * f c = 0 := by
  set a : {x // x ∈ Λ} := ⟨z, hz⟩ with ha
  set b : {x // x ∈ Λ} := ⟨z + 1, hz1⟩ with hb
  have hab : a ≠ b := by simp only [ha, hb, ne_eq, Subtype.mk.injEq]; omega
  set g : Config Λ → ℝ := fun c => Wb Λ q alpha c * Vb Λ q z c * f c with hg
  have key : ∀ c, g (swapC Λ s0 a b c) = - g c := by
    intro c
    have PA := pointwise_antisym Λ q hq alpha s0 z hz hz1 c
    simp only [hg]; rw [hfinv c, PA]; ring
  have reindex : (∑ c, g c) = ∑ c, g (swapC Λ s0 a b c) :=
    (Equiv.sum_comp (swapC_invol Λ s0 a b hab).toPerm g).symm
  have hEq : (∑ c, g c) = - ∑ c, g c := by
    conv_lhs => rw [reindex]
    simp_rw [key, Finset.sum_neg_distrib]
  have hzero : ∑ c, g c = 0 := by linarith
  simpa [hg] using hzero

/-! ## Invariance helper lemmas -/

/-- The other species (`≠ i`). -/
def other : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0

lemma other_ne (i : Fin 2) : other i ≠ i := by fin_cases i <;> decide

/-- Swapping species `s0` does not change species-`i` occupations when `i ≠ s0`. -/
lemma swapC_species (s0 : Fin 2) (a b : {x // x ∈ Λ}) (c : Config Λ) (i : Fin 2) (hi : i ≠ s0)
    (t : {x // x ∈ Λ}) : swapC Λ s0 a b c t i = c t i := by
  unfold swapC
  split_ifs with h1 h2
  · rw [h1]; exact Function.update_of_ne hi _ _
  · rw [h2]; exact Function.update_of_ne hi _ _
  · rfl

/-- The occupation `bocc i w` is invariant under a swap of the other species. -/
lemma bocc_swapC_species (s0 : Fin 2) (a b : {x // x ∈ Λ}) (c : Config Λ) (i : Fin 2)
    (hi : i ≠ s0) (w : ℤ) : bocc Λ i w (swapC Λ s0 a b c) = bocc Λ i w c := by
  unfold bocc
  by_cases h : w ∈ Λ <;> simp only [h, dif_pos, dif_neg, not_false_iff]
  · rw [swapC_species Λ s0 a b c i hi ⟨w, h⟩]

/-- The occupation `bocc i w` is invariant under a bond swap at sites disjoint from `w`. -/
lemma bocc_swapC_offsite (s0 : Fin 2) (x : ℤ) (hx : x ∈ Λ) (hx1 : x + 1 ∈ Λ) (c : Config Λ)
    (i : Fin 2) (w : ℤ) (hwx : w ≠ x) (hwx1 : w ≠ x + 1) :
    bocc Λ i w (swapC Λ s0 ⟨x, hx⟩ ⟨x + 1, hx1⟩ c) = bocc Λ i w c := by
  unfold bocc
  by_cases h : w ∈ Λ <;> simp only [h, dif_pos, dif_neg, not_false_iff]
  · rw [swapC_at_other]
    · exact fun he => hwx (congrArg Subtype.val he)
    · exact fun he => hwx1 (congrArg Subtype.val he)

/-- `V_y` is invariant under a bond swap at a disjoint bond `(x, x+1)`. -/
lemma Vb_swapC_offbond (q : ℝ) (s0 : Fin 2) (x : ℤ) (hx : x ∈ Λ) (hx1 : x + 1 ∈ Λ) (c : Config Λ)
    (y : ℤ) (hyx : y ≠ x) (hyx1 : y ≠ x + 1) (hy1x : y + 1 ≠ x) (hy1x1 : y + 1 ≠ x + 1) :
    Vb Λ q y (swapC Λ s0 ⟨x, hx⟩ ⟨x + 1, hx1⟩ c) = Vb Λ q y c := by
  simp only [Vb, phi,
    bocc_swapC_offsite Λ s0 x hx hx1 c _ y hyx hyx1,
    bocc_swapC_offsite Λ s0 x hx hx1 c _ (y + 1) hy1x hy1x1]

/-! ## The three consequences -/

variable [Fintype {x // x ∈ Λ}]

/-- **Lemma `lem:eqvar` (i) / `lem:orth` (constant part).**  `E[V_z] = 0`. -/
theorem expect_V_eq_zero (q : ℝ) (hq : q ≠ 0) (alpha : Fin 2 → ℝ) (z : ℤ)
    (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) :
    ∑ c, Wb Λ q alpha c * Vb Λ q z c = 0 := by
  have := expect_Vf_zero Λ q hq alpha 0 z hz hz1 (fun _ => 1) (fun c => rfl)
  simpa using this

/-- **Lemma `lem:orth` (mass-1 case).**  `E[V_z · η_{i,y}] = 0` for every species `i` and site `y`. -/
theorem expect_V_mul_occ_eq_zero (q : ℝ) (hq : q ≠ 0) (alpha : Fin 2 → ℝ) (z : ℤ)
    (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (i : Fin 2) (y : ℤ) :
    ∑ c, Wb Λ q alpha c * Vb Λ q z c * bocc Λ i y c = 0 := by
  refine expect_Vf_zero Λ q hq alpha (other i) z hz hz1 (fun c => bocc Λ i y c) ?_
  intro c
  exact bocc_swapC_species Λ (other i) _ _ c i (other_ne i).symm y

/-- **Lemma `lem:eqvar` (ii).**  `E[V_x · V_y] = 0` whenever the bonds are disjoint. -/
theorem expect_V_mul_V_eq_zero (q : ℝ) (hq : q ≠ 0) (alpha : Fin 2 → ℝ) (x y : ℤ)
    (hx : x ∈ Λ) (hx1 : x + 1 ∈ Λ)
    (hyx : y ≠ x) (hyx1 : y ≠ x + 1) (hy1x : y + 1 ≠ x) (hy1x1 : y + 1 ≠ x + 1) :
    ∑ c, Wb Λ q alpha c * Vb Λ q x c * Vb Λ q y c = 0 := by
  refine expect_Vf_zero Λ q hq alpha 0 x hx hx1 (fun c => Vb Λ q y c) ?_
  intro c
  exact Vb_swapC_offbond Λ q 0 x hx hx1 c y hyx hyx1 hy1x hy1x1

/-! ## Pointwise bounds -/

omit [Fintype {x // x ∈ Λ}] in
lemma bocc_mem (i : Fin 2) (x : ℤ) (c : Config Λ) : bocc Λ i x c = 0 ∨ bocc Λ i x c = 1 := by
  unfold bocc; split <;> [split; skip] <;> simp_all

omit [Fintype {x // x ∈ Λ}] in
/-- `|V_z| ≤ 1` pointwise for `q ∈ (0,1)` (Lemma `lem:eqvar` (iii)). -/
lemma Vb_abs_le_one (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (z : ℤ) (c : Config Λ) :
    |Vb Λ q z c| ≤ 1 := by
  have hq2 : q ^ 2 ≤ 1 := pow_le_one₀ hq0.le hq1.le
  have hq2' : (0 : ℝ) ≤ q ^ 2 := sq_nonneg q
  have hphi : ∀ i, |phi Λ q i z c| ≤ 1 := by
    intro i
    unfold phi
    rcases bocc_mem Λ i z c with h0 | h0 <;> rcases bocc_mem Λ i (z + 1) c with h1 | h1 <;>
      rw [h0, h1] <;> rw [abs_le] <;> constructor <;> nlinarith
  calc |Vb Λ q z c| = |phi Λ q 0 z c| * |phi Λ q 1 z c| := by rw [Vb, abs_mul]
    _ ≤ 1 * 1 := by apply mul_le_mul (hphi 0) (hphi 1) (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

omit [Fintype {x // x ∈ Λ}] in
/-- Each single-site blocking factor is positive when `q > 0` and `αᵢ > 0`. -/
lemma siteFac_pos (q : ℝ) (hq0 : 0 < q) (alpha : Fin 2 → ℝ) (halpha : ∀ i, 0 < alpha i)
    (x : ℤ) (b : Fin 2 → Bool) : 0 < siteFac q alpha x b := by
  unfold siteFac
  apply Finset.prod_pos
  intro i _
  split
  · exact mul_pos (halpha i) (zpow_pos hq0 _)
  · norm_num

omit [Fintype {x // x ∈ Λ}] in
/-- The blocking weight is positive. -/
lemma Wb_pos (q : ℝ) (hq0 : 0 < q) (alpha : Fin 2 → ℝ) (halpha : ∀ i, 0 < alpha i) (c : Config Λ) :
    0 < Wb Λ q alpha c := by
  unfold Wb
  exact Finset.prod_pos (fun s _ => siteFac_pos q hq0 alpha halpha _ _)

/-- The partition function is positive. -/
lemma sum_Wb_pos (q : ℝ) (hq0 : 0 < q) (alpha : Fin 2 → ℝ) (halpha : ∀ i, 0 < alpha i)
    [Nonempty (Config Λ)] : 0 < ∑ c, Wb Λ q alpha c :=
  Finset.sum_pos (fun c _ => Wb_pos Λ q hq0 alpha halpha c) ⟨Classical.arbitrary _, Finset.mem_univ _⟩

/-! ## The equal-time variance bound (Lemma `lem:eqvar` (iii)) -/

/-
**Per-pair covariance bound.**  `|E[V_x V_y]| ≤ Z` (unnormalised): the weighted sum of
`V_x V_y` is bounded in absolute value by the partition function, since `|V_x V_y| ≤ 1` and the
blocking weight is nonnegative.
-/
lemma abs_expect_VV_le (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (alpha : Fin 2 → ℝ)
    (halpha : ∀ i, 0 < alpha i) (x y : ℤ) :
    |∑ c, Wb Λ q alpha c * Vb Λ q x c * Vb Λ q y c| ≤ ∑ c, Wb Λ q alpha c := by
  refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun c _ => _ );
  rw [ abs_mul, abs_mul, abs_of_nonneg ( show 0 ≤ Wb Λ q alpha c from le_of_lt ( Wb_pos Λ q hq0 alpha halpha c ) ) ];
  exact mul_le_of_le_one_right ( mul_nonneg ( le_of_lt ( Wb_pos Λ q hq0 alpha halpha c ) ) ( abs_nonneg _ ) ) ( Vb_abs_le_one Λ q hq0 hq1 y c ) |> le_trans <| mul_le_of_le_one_right ( le_of_lt ( Wb_pos Λ q hq0 alpha halpha c ) ) ( Vb_abs_le_one Λ q hq0 hq1 x c )

/-
**Expansion of the squared linear combination** as a weighted double sum of pair
covariances.
-/
lemma sq_sum_expand (q : ℝ) (alpha : Fin 2 → ℝ) (bonds : Finset ℤ) (g : ℤ → ℝ) :
    (∑ c, Wb Λ q alpha c * (∑ x ∈ bonds, g x * Vb Λ q x c) ^ 2)
      = ∑ x ∈ bonds, ∑ y ∈ bonds,
          g x * g y * (∑ c, Wb Λ q alpha c * Vb Λ q x c * Vb Λ q y c) := by
  simp +decide only [sq, Finset.mul_sum, Finset.sum_mul, mul_assoc];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) )

/-
**The general equal-time variance bound.**  For a bounded coefficient field `g` and bonds
inside the window, the weighted mean square of `Σ_x g x V_x` is at most `Z · 3 M² |bonds|`.
The off-diagonal terms vanish by disjoint-support independence (`expect_V_mul_V_eq_zero`); the
at most `3|bonds|` near-diagonal terms are each bounded by `Z M²` (`abs_expect_VV_le`).
-/
theorem expect_sq_le (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (alpha : Fin 2 → ℝ)
    (halpha : ∀ i, 0 < alpha i) (bonds : Finset ℤ) (hb : ∀ x ∈ bonds, x ∈ Λ ∧ x + 1 ∈ Λ)
    (g : ℤ → ℝ) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x ∈ bonds, |g x| ≤ M) :
    (∑ c, Wb Λ q alpha c * (∑ x ∈ bonds, g x * Vb Λ q x c) ^ 2)
      ≤ (∑ c, Wb Λ q alpha c) * (3 * M ^ 2 * bonds.card) := by
  have h_sq_sum_expand : (∑ c, Wb Λ q alpha c * (∑ x ∈ bonds, g x * Vb Λ q x c) ^ 2) = ∑ x ∈ bonds, ∑ y ∈ bonds, g x * g y * (∑ c, Wb Λ q alpha c * Vb Λ q x c * Vb Λ q y c) := by
    convert sq_sum_expand Λ q alpha bonds g using 1;
  -- Apply the bound on the absolute value of the sum.
  have h_abs_sum : |∑ x ∈ bonds, ∑ y ∈ bonds, g x * g y * (∑ c, Wb Λ q alpha c * Vb Λ q x c * Vb Λ q y c)| ≤ ∑ x ∈ bonds, ∑ y ∈ bonds, |g x| * |g y| * (∑ c, Wb Λ q alpha c) * (if y ∈ ({x - 1, x, x + 1} : Finset ℤ) then 1 else 0) := by
    refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun x hx => Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun y hy => _ );
    split_ifs <;> simp_all +decide [ abs_mul ];
    · gcongr;
      exact abs_expect_VV_le Λ q hq0 hq1 alpha ( fun i => by fin_cases i <;> tauto ) x y;
    · rw [ expect_V_mul_V_eq_zero Λ q ( ne_of_gt hq0 ) alpha x y ( hb x hx |>.1 ) ( hb x hx |>.2 ) ( by omega ) ( by omega ) ( by omega ) ( by omega ) ] ; norm_num;
  -- Apply the bound on the absolute value of the sum to each term in the double sum.
  have h_abs_sum_bound : ∑ x ∈ bonds, ∑ y ∈ bonds, |g x| * |g y| * (∑ c, Wb Λ q alpha c) * (if y ∈ ({x - 1, x, x + 1} : Finset ℤ) then 1 else 0) ≤ ∑ x ∈ bonds, ∑ y ∈ ({x - 1, x, x + 1} : Finset ℤ), M * M * (∑ c, Wb Λ q alpha c) := by
    refine' Finset.sum_le_sum fun x hx => _;
    refine' le_trans ( Finset.sum_le_sum fun y hy => _ ) _;
    use fun y => if y ∈ ({x - 1, x, x + 1} : Finset ℤ) then M * M * (∑ c, Wb Λ q alpha c) else 0;
    · split_ifs <;> norm_num;
      exact mul_le_mul_of_nonneg_right ( mul_le_mul ( hM x hx ) ( hM y hy ) ( by positivity ) ( by positivity ) ) ( Finset.sum_nonneg fun _ _ => le_of_lt ( Wb_pos Λ q hq0 alpha halpha _ ) );
    · simp +decide [ Finset.sum_ite ];
      exact mul_le_mul_of_nonneg_right ( mod_cast Finset.card_le_card fun y hy => by aesop ) ( mul_nonneg ( mul_nonneg hM0 hM0 ) ( Finset.sum_nonneg fun _ _ => le_of_lt ( Wb_pos Λ q hq0 alpha halpha _ ) ) );
  refine le_trans ( h_sq_sum_expand.le.trans ( le_of_abs_le h_abs_sum ) ) ( h_abs_sum_bound.trans ?_ );
  norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ] ; ring_nf;
  norm_num [ Finset.card_insert_of_notMem, Finset.card_singleton, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]

/-! ## The duality coefficient `D-bar(xi, .)` and the support of the inner product

This is the general orthogonality lemma `lem:orth` of the brief.  For a dual configuration `ξ`
(a second `{0,1}` two-species occupation) the (finite-product) duality function is
`D̄(ξ, η) = ∏ᵢ ∏_v (1 − (q^{2(v − N⁻_{v-1}(ηᵢ) + N⁺_{v+1}(ξᵢ))}/αᵢ) · ξ_{i,v} · η_{i,v})`,
where `N⁻_{v-1}(ηᵢ) = Σ_{u<v} η_{i,u}` and `N⁺_{v+1}(ξᵢ) = Σ_{u>v} ξ_{i,u}` (sums over `Λ`).
The factor at `(i,v)` is trivial unless both the dual and primal configurations occupy `(i,v)`.

We prove: for a sector-reweighted weight `W(η)·h(N(η))` (blocking weight times an arbitrary
function `h` of the total particle number `N`), the inner product `⟨V_z, D̄(ξ, ·)⟩` vanishes
whenever some species has no dual particle on the bond `{z, z+1}`.  Since a dual configuration of
total mass `≤ 1` necessarily leaves one species empty on the bond, this covers the mass `≤ 1`
statement of `lem:orth` (and the density-field case).  The mechanism is the species-swap
involution: with that species empty on the bond, `D̄(ξ, ·)` is invariant under the swap, `N` is
preserved, and `V_z` changes sign. -/

/-- The total particle number (summed over sites and species). -/
noncomputable def Ntot (c : Config Λ) : ℝ := ∑ s : {x // x ∈ Λ}, ∑ i, (if c s i then (1 : ℝ) else 0)

/-- `N⁻_{v-1}(cᵢ) = Σ_{u < v} c_{i,u}`. -/
noncomputable def Nminus (i : Fin 2) (v : ℤ) (c : Config Λ) : ℝ :=
  ∑ u ∈ Λ.filter (· < v), bocc Λ i u c

/-- `N⁺_{v+1}(ξᵢ) = Σ_{u > v} ξ_{i,u}`. -/
noncomputable def Nplus (i : Fin 2) (v : ℤ) (ξ : Config Λ) : ℝ :=
  ∑ u ∈ Λ.filter (v < ·), bocc Λ i u ξ

/-- A single factor of `D̄(ξ, ·)` at species `i`, site `v`. -/
noncomputable def barDfac (q : ℝ) (alpha : Fin 2 → ℝ) (ξ : Config Λ) (i : Fin 2) (v : ℤ)
    (c : Config Λ) : ℝ :=
  1 - (Real.rpow q (2 * ((v : ℝ) - Nminus Λ i v c + Nplus Λ i v ξ)) / alpha i)
        * bocc Λ i v ξ * bocc Λ i v c

/-- The duality function `D̄(ξ, ·)` as a finite product over species and sites. -/
noncomputable def barD (q : ℝ) (alpha : Fin 2 → ℝ) (ξ : Config Λ) (c : Config Λ) : ℝ :=
  ∏ i, ∏ s : {x // x ∈ Λ}, barDfac Λ q alpha ξ i (s : ℤ) c

/-
The total particle number is invariant under a species swap.
-/
lemma Ntot_swapC (s0 : Fin 2) (a b : {x // x ∈ Λ}) (c : Config Λ) :
    Ntot Λ (swapC Λ s0 a b c) = Ntot Λ c := by
  unfold Ntot;
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  rotate_right;
  use fun i => ∑ s : { x // x ∈ Λ }, if c s i then 1 else 0;
  · exact Finset.sum_comm;
  · intro i hi;
    by_cases hi' : i = s0;
    · convert Equiv.sum_comp ( Equiv.swap a b ) ( fun s => if c s s0 then ( 1 : ℝ ) else 0 ) using 1;
      · congr! 2;
        unfold swapC; aesop;
      · rw [ hi' ];
    · exact Finset.sum_congr rfl fun x hx => by rw [ swapC_species Λ s0 a b c i hi' x ] ;

omit [Fintype {x // x ∈ Λ}] in
/-- `N⁻` is invariant under a swap of a different species. -/
lemma Nminus_swapC_species (s0 : Fin 2) (a b : {x // x ∈ Λ}) (c : Config Λ) (i : Fin 2)
    (hi : i ≠ s0) (v : ℤ) : Nminus Λ i v (swapC Λ s0 a b c) = Nminus Λ i v c := by
  unfold Nminus
  exact Finset.sum_congr rfl (fun u _ => bocc_swapC_species Λ s0 a b c i hi u)

omit [Fintype {x // x ∈ Λ}] in
/-- `N⁻` at a site off the bond is invariant under the bond swap (the two swapped occupations
lie on the same side of `v`, so their contributions cancel). -/
lemma Nminus_swapC_offbond (i0 : Fin 2) (z : ℤ) (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (c : Config Λ)
    (v : ℤ) (hvz : v ≠ z) (hvz1 : v ≠ z + 1) :
    Nminus Λ i0 v (swapC Λ i0 ⟨z, hz⟩ ⟨z + 1, hz1⟩ c) = Nminus Λ i0 v c := by
  by_cases hlt : z < v;
  · -- Since $z < v$ and $v \neq z + 1$, we have $z + 1 < v$.
    have hlt1 : z + 1 < v := by
      exact lt_of_le_of_ne hlt ( Ne.symm hvz1 );
    unfold Nminus; simp +decide [ *, Finset.sum_filter ] ;
    apply Finset.sum_bij (fun a _ => if a = z then z + 1 else if a = z + 1 then z else a);
    · grind;
    · grind;
    · grind;
    · intro a ha; split_ifs <;> simp_all +decide [ bocc_swapC_offsite ] ;
      · unfold bocc; simp +decide [ *, swapC ] ;
      · unfold bocc swapC; aesop;
  · refine' Finset.sum_congr rfl _;
    grind +suggestions

/-- If species `i0` has no dual particle on the bond `{z, z+1}`, then `D̄(ξ, ·)` is invariant
under the species-`i0` swap of the two bond occupations. -/
lemma barD_swapC_zero (q : ℝ) (alpha : Fin 2 → ℝ) (ξ : Config Λ) (i0 : Fin 2) (z : ℤ)
    (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (c : Config Λ)
    (hξ0 : bocc Λ i0 z ξ = 0) (hξ1 : bocc Λ i0 (z + 1) ξ = 0) :
    barD Λ q alpha ξ (swapC Λ i0 ⟨z, hz⟩ ⟨z + 1, hz1⟩ c) = barD Λ q alpha ξ c := by
  refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun s _ => ?_))
  by_cases hi0 : i = i0
  · subst hi0
    by_cases hsz : (s : ℤ) = z
    · simp only [barDfac, hsz, hξ0, mul_zero, zero_mul, sub_zero]
    · by_cases hsz1 : (s : ℤ) = z + 1
      · simp only [barDfac, hsz1, hξ1, mul_zero, zero_mul, sub_zero]
      · unfold barDfac
        rw [bocc_swapC_offsite Λ i z hz hz1 c i (s : ℤ) hsz hsz1,
          Nminus_swapC_offbond Λ i z hz hz1 c (s : ℤ) hsz hsz1]
  · unfold barDfac
    rw [bocc_swapC_species Λ i0 _ _ c i hi0 (s : ℤ),
      Nminus_swapC_species Λ i0 _ _ c i hi0 (s : ℤ)]

/-- **General `lem:orth` (empty-species case, covering mass `≤ 1`).**  For the sector-reweighted
weight `W(η)·h(N(η))` with `h` arbitrary, `⟨V_z, D̄(ξ, ·)⟩` vanishes whenever some species `i0`
has no dual particle on the bond `{z, z+1}`. -/
theorem expect_V_mul_barD_eq_zero (q : ℝ) (hq0 : 0 < q) (alpha : Fin 2 → ℝ)
    (ξ : Config Λ) (z : ℤ) (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (h : ℝ → ℝ) (i0 : Fin 2)
    (hξ0 : bocc Λ i0 z ξ = 0) (hξ1 : bocc Λ i0 (z + 1) ξ = 0) :
    ∑ c, Wb Λ q alpha c * Vb Λ q z c * (h (Ntot Λ c) * barD Λ q alpha ξ c) = 0 := by
  refine expect_Vf_zero Λ q (ne_of_gt hq0) alpha i0 z hz hz1
    (fun c => h (Ntot Λ c) * barD Λ q alpha ξ c) ?_
  intro c
  dsimp only
  rw [Ntot_swapC, barD_swapC_zero Λ q alpha ξ i0 z hz hz1 c hξ0 hξ1]

/-! ## `lem:orth` completion: same-species duals on **both** bond sites -/

omit [Fintype {x // x ∈ Λ}] in
/-- Bond-site occupation swap: `bocc i0 z (σ c) = bocc i0 (z+1) c`. -/
lemma bocc_swapC_bond_left (i0 : Fin 2) (z : ℤ) (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (c : Config Λ) :
    bocc Λ i0 z (swapC Λ i0 ⟨z, hz⟩ ⟨z + 1, hz1⟩ c) = bocc Λ i0 (z + 1) c := by
  unfold bocc; simp +decide [ *, swapC ] ;

omit [Fintype {x // x ∈ Λ}] in
/-- Bond-site occupation swap: `bocc i0 (z+1) (σ c) = bocc i0 z c`. -/
lemma bocc_swapC_bond_right (i0 : Fin 2) (z : ℤ) (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (c : Config Λ) :
    bocc Λ i0 (z + 1) (swapC Λ i0 ⟨z, hz⟩ ⟨z + 1, hz1⟩ c) = bocc Λ i0 z c := by
  unfold bocc;
  unfold swapC; aesop;

omit [Fintype {x // x ∈ Λ}] in
/-- Splitting `N⁻` at `z+1` into `N⁻` at `z` plus the site-`z` occupation. -/
lemma Nminus_succ (i0 : Fin 2) (z : ℤ) (hz : z ∈ Λ) (c : Config Λ) :
    Nminus Λ i0 (z + 1) c = Nminus Λ i0 z c + bocc Λ i0 z c := by
  unfold Nminus;
  rw [ show ( Λ.filter fun u => u < z + 1 ) = ( Λ.filter fun u => u < z ) ∪ { z } from ?_, Finset.sum_union ] <;> norm_num [ hz ];
  grind

omit [Fintype {x // x ∈ Λ}] in
/-- Splitting `N⁺` at `z` into the site-`z+1` occupation plus `N⁺` at `z+1`. -/
lemma Nplus_pred (i0 : Fin 2) (z : ℤ) (hz1 : z + 1 ∈ Λ) (ξ : Config Λ) :
    Nplus Λ i0 z ξ = bocc Λ i0 (z + 1) ξ + Nplus Λ i0 (z + 1) ξ := by
  unfold Nplus;
  rw [ show ( Finset.filter ( fun u => z < u ) Λ ) = { z + 1 } ∪ Finset.filter ( fun u => z + 1 < u ) Λ from ?_, Finset.sum_union ] <;> norm_num;
  grind

omit [Fintype {x // x ∈ Λ}] in
/-- `N⁻` at the left bond site is invariant under the bond swap (no site `< z` is moved). -/
lemma Nminus_swapC_at_z (i0 : Fin 2) (z : ℤ) (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (c : Config Λ) :
    Nminus Λ i0 z (swapC Λ i0 ⟨z, hz⟩ ⟨z + 1, hz1⟩ c) = Nminus Λ i0 z c := by
  refine' Finset.sum_congr rfl fun u hu => _;
  grind +suggestions

omit [Fintype {x // x ∈ Λ}] in
/-- **Lemma `equalc`.**  When species `i0` has dual particles on both bond sites
(`ξ_{i0,z} = ξ_{i0,z+1} = 1`), the product of the two species-`i0` bond factors of `D̄` is
invariant under the bond swap `σ_{i0}`.  The active exponents at `z` and `z+1` coincide because
the dual at `z+1` contributes `+1` to `N⁺` at `z`, while the count `N⁻` at `z+1` gains the
site-`z` occupation. -/
lemma barDfac_bond_product_swap (q : ℝ) (alpha : Fin 2 → ℝ) (ξ : Config Λ) (i0 : Fin 2)
    (z : ℤ) (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (c : Config Λ)
    (hξ0 : bocc Λ i0 z ξ = 1) (hξ1 : bocc Λ i0 (z + 1) ξ = 1) :
    barDfac Λ q alpha ξ i0 z (swapC Λ i0 ⟨z, hz⟩ ⟨z + 1, hz1⟩ c)
        * barDfac Λ q alpha ξ i0 (z + 1) (swapC Λ i0 ⟨z, hz⟩ ⟨z + 1, hz1⟩ c)
      = barDfac Λ q alpha ξ i0 z c * barDfac Λ q alpha ξ i0 (z + 1) c := by
  unfold barDfac;
  grind +suggestions

/-
If species `i0` has dual particles on **both** bond sites, `D̄(ξ,·)` is invariant under the
species-`i0` bond swap.  Off-bond factors are invariant factorwise (as in `barD_swapC_zero`);
the two bond factors are invariant as a product by `barDfac_bond_product_swap`.
-/
lemma barD_swapC_two (q : ℝ) (alpha : Fin 2 → ℝ) (ξ : Config Λ) (i0 : Fin 2) (z : ℤ)
    (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (c : Config Λ)
    (hξ0 : bocc Λ i0 z ξ = 1) (hξ1 : bocc Λ i0 (z + 1) ξ = 1) :
    barD Λ q alpha ξ (swapC Λ i0 ⟨z, hz⟩ ⟨z + 1, hz1⟩ c) = barD Λ q alpha ξ c := by
  refine' Finset.prod_congr rfl fun i hi => _;
  by_cases hi0 : i = i0;
  · -- Set za := (⟨z,hz⟩ : {x//x∈Λ}), zb := (⟨z+1,hz1⟩ : {x//x∈Λ}).
    set za : {x // x ∈ Λ} := ⟨z, hz⟩
    set zb : {x // x ∈ Λ} := ⟨z + 1, hz1⟩;
    -- The remaining product over rest = (univ.erase za).erase zb is invariant factorwise.
    have h_rest_inv : ∏ s ∈ (Finset.univ.erase za).erase zb, barDfac Λ q alpha ξ i0 (s : ℤ) (swapC Λ i0 za zb c) = ∏ s ∈ (Finset.univ.erase za).erase zb, barDfac Λ q alpha ξ i0 (s : ℤ) c := by
      refine' Finset.prod_congr rfl fun s hs => _;
      unfold barDfac;
      rw [ Nminus_swapC_offbond, bocc_swapC_offsite ] <;> aesop;
    have h_bond_inv : barDfac Λ q alpha ξ i0 z (swapC Λ i0 za zb c) * barDfac Λ q alpha ξ i0 (z + 1) (swapC Λ i0 za zb c) = barDfac Λ q alpha ξ i0 z c * barDfac Λ q alpha ξ i0 (z + 1) c := by
      exact barDfac_bond_product_swap Λ q alpha ξ i0 z hz hz1 c hξ0 hξ1
    convert congr_arg₂ ( · * · ) h_bond_inv h_rest_inv using 1;
    · rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ za ), ← Finset.mul_prod_erase _ _ ( Finset.mem_erase_of_ne_of_mem ( by aesop ) ( Finset.mem_univ zb ) ) ];
      grind;
    · rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ za ), ← Finset.mul_prod_erase _ _ ( Finset.mem_erase_of_ne_of_mem ( by aesop ) ( Finset.mem_univ zb ) ) ];
      rw [ hi0, mul_assoc ];
  · refine' Finset.prod_congr rfl fun s hs => _;
    unfold barDfac;
    rw [ bocc_swapC_species Λ i0 ⟨ z, hz ⟩ ⟨ z + 1, hz1 ⟩ c i hi0 s, Nminus_swapC_species Λ i0 ⟨ z, hz ⟩ ⟨ z + 1, hz1 ⟩ c i hi0 s ]

/-- **`lem:orth` (two-duals case).**  `⟨V_z, D̄(ξ,·)⟩` vanishes when species `i0` has dual
particles on *both* bond sites. -/
theorem expect_V_mul_barD_eq_zero_two (q : ℝ) (hq0 : 0 < q) (alpha : Fin 2 → ℝ)
    (ξ : Config Λ) (z : ℤ) (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (h : ℝ → ℝ) (i0 : Fin 2)
    (hξ0 : bocc Λ i0 z ξ = 1) (hξ1 : bocc Λ i0 (z + 1) ξ = 1) :
    ∑ c, Wb Λ q alpha c * Vb Λ q z c * (h (Ntot Λ c) * barD Λ q alpha ξ c) = 0 := by
  refine expect_Vf_zero Λ q (ne_of_gt hq0) alpha i0 z hz hz1
    (fun c => h (Ntot Λ c) * barD Λ q alpha ξ c) ?_
  intro c
  dsimp only
  rw [Ntot_swapC, barD_swapC_two Λ q alpha ξ i0 z hz hz1 c hξ0 hξ1]

/-- **`lem:orth` support classification (combined).**  For the sector-reweighted weight
`W(η)·h(N(η))`, the inner product `⟨V_z, D̄(ξ,·)⟩` vanishes whenever some species `i0` has `0`
or `2` dual particles on the bond `{z, z+1}` (equivalently `ξ_{i0,z} = ξ_{i0,z+1}`).  Hence a
nonvanishing coefficient requires **exactly one** dual of each species on the bond. -/
theorem expect_V_mul_barD_eq_zero_of_eq (q : ℝ) (hq0 : 0 < q) (alpha : Fin 2 → ℝ)
    (ξ : Config Λ) (z : ℤ) (hz : z ∈ Λ) (hz1 : z + 1 ∈ Λ) (h : ℝ → ℝ) (i0 : Fin 2)
    (hξ : bocc Λ i0 z ξ = bocc Λ i0 (z + 1) ξ) :
    ∑ c, Wb Λ q alpha c * Vb Λ q z c * (h (Ntot Λ c) * barD Λ q alpha ξ c) = 0 := by
  rcases bocc_mem Λ i0 z ξ with h0 | h1
  · exact expect_V_mul_barD_eq_zero Λ q hq0 alpha ξ z hz hz1 h i0 h0 (by rw [← hξ]; exact h0)
  · exact expect_V_mul_barD_eq_zero_two Λ q hq0 alpha ξ z hz hz1 h i0 h1 (by rw [← hξ]; exact h1)

end TypeDDecoupling.EqvarOrth