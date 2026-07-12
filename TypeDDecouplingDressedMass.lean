import Mathlib

/-!
# The dressed-mass estimate (`lem:eps`): the elementary proof

This file formalises the elementary, self-contained proof of the dressed-mass estimate
(Theorem `thm:main` / Lemma `lem:eps` of the type-D ASEP decoupling paper), following
`lem_eps_proof_draft.tex`.

The set-up is a *finite* configuration space `Config` with two species of `{0,1}`-valued
occupation variables `occ i x c` (`i ∈ Fin 2` the species, `x ∈ ℤ` the site, `c` the
configuration), a bond `(z, z+1)`, a parameter `q ∈ (0,1)`, a finite lattice `Λ ⊆ ℤ`
outside of which occupations vanish, and a probability weight `w` giving the `L²(ϖ)`
inner product `ip w f g = ∑_c w c · f c · g c`.

The proof rests on two exact algebraic identities, both proved here with no `sorry`:

* **`Vbond_eq_product`** (Lemma `lem:prod`): the bond cross-term `V_z` equals the product
  `φ¹_z · φ²_z` of the two single-species bond factors
  `φⁱ_z = η_{i,z} − q² η_{i,z+1} − (1−q²) η_{i,z} η_{i,z+1}` (here `Vbond` is *defined* as
  this product, and `Vbond_support_values` records the values on the four support
  configurations, i.e. the content of `lem:prod`).
* **`Fdual_diff`** (Lemma `lem:dress`): the exact dressing identity
  `F^i_z − F^i_{z+1} = − q^{2(z − L_i)} φⁱ_z`, with `L_i = N⁻_{z-1}(η_i)` the number of
  species-`i` particles strictly left of `z`, and `F^i_w = D̄(ξ^{i,w}, ·)` the single-dual
  duality function (here with fugacities `α_i = 1`).

From these, `A_z := q^{-4z}(F¹_z − F¹_{z+1})(F²_z − F²_{z+1})` lies in the span `U_z` of the
four bond-pair duality functions and satisfies `V_z − A_z = (1 − q^{-2(L₁+L₂)}) V_z`
exactly (`Vbond_sub_Az`). Since `0 ≤ L₁+L₂ ≤ 2ℓ(z)` this gives the pointwise bound
`|V_z − A_z| ≤ (q^{-4ℓ(z)} − 1)|V_z|` (`Vbond_sub_Az_abs_le`). Finally, the dressed mass —
the squared `L²(ϖ)`-distance from `V_z` to `U_z` — is at most `‖V_z − A_z‖²`, which is at
most `(q^{-4ℓ(z)} − 1)²` (`dressedMass_bond_le`). This is Theorem `thm:main`.

Everything is stated for an *arbitrary* probability weight `w`; in particular it applies to
the sector-reweighted measure `ϖ` of the main text.
-/

open scoped BigOperators

namespace TypeDDecoupling.DressedMass

variable {Config : Type*}

/-! ## The weighted `L²` inner product -/

/-- The `L²(ϖ)` inner product `⟨f,g⟩_ϖ = ∑_c w c · f c · g c` for a weight `w`. -/
def ip [Fintype Config] (w f g : Config → ℝ) : ℝ := ∑ c, w c * (f c * g c)

/-! ## The single-species bond factors, the cross-term, and the duality functions -/

/-- The single-species bond factor `φⁱ_z(η) = η_{i,z} − q² η_{i,z+1} − (1−q²) η_{i,z} η_{i,z+1}`. -/
def phi (q : ℝ) (occ : Fin 2 → ℤ → Config → ℝ) (i : Fin 2) (z : ℤ) (c : Config) : ℝ :=
  occ i z c - q ^ 2 * occ i (z + 1) c - (1 - q ^ 2) * (occ i z c * occ i (z + 1) c)

/-- The bond cross-term `V_z = φ¹_z · φ²_z` (Lemma `lem:prod`: this product equals the
indicator form `1_{(3,0)} + q⁴ 1_{(0,3)} − q² 1_{(1,2)} − q² 1_{(2,1)}`). -/
def Vbond (q : ℝ) (occ : Fin 2 → ℤ → Config → ℝ) (z : ℤ) (c : Config) : ℝ :=
  phi q occ 0 z c * phi q occ 1 z c

/-- The number `N⁻_{w-1}(η_i)` of species-`i` particles strictly to the left of `w`. -/
def Nleft (Λ : Finset ℤ) (occ : Fin 2 → ℤ → Config → ℝ) (i : Fin 2) (w : ℤ) (c : Config) : ℝ :=
  ∑ v ∈ Λ.filter (· < w), occ i v c

/-- The single-dual duality function `F^i_w = D̄(ξ^{i,w}, ·) = 1 − q^{2(w − N⁻_{w-1}(η_i))} η_{i,w}`
(with fugacity `α_i = 1`). -/
noncomputable def Fdual (q : ℝ) (Λ : Finset ℤ) (occ : Fin 2 → ℤ → Config → ℝ)
    (i : Fin 2) (w : ℤ) (c : Config) : ℝ :=
  1 - Real.rpow q (2 * ((w : ℝ) - Nleft Λ occ i w c)) * occ i w c

/-- The four bond-pair duality functions `F¹_{w₁} F²_{w₂}`, `w₁,w₂ ∈ {z,z+1}`, indexed by
`Fin 4` as `(z,z), (z,z+1), (z+1,z), (z+1,z+1)`. -/
noncomputable def bpBasis (q : ℝ) (Λ : Finset ℤ) (occ : Fin 2 → ℤ → Config → ℝ) (z : ℤ) :
    Fin 4 → Config → ℝ
  | 0 => fun c => Fdual q Λ occ 0 z c * Fdual q Λ occ 1 z c
  | 1 => fun c => Fdual q Λ occ 0 z c * Fdual q Λ occ 1 (z + 1) c
  | 2 => fun c => Fdual q Λ occ 0 (z + 1) c * Fdual q Λ occ 1 z c
  | 3 => fun c => Fdual q Λ occ 0 (z + 1) c * Fdual q Λ occ 1 (z + 1) c

/-- The coefficients expressing `A_z = q^{-4z}(F¹_z − F¹_{z+1})(F²_z − F²_{z+1})` in the
bond-pair basis: `(q^{-4z}, −q^{-4z}, −q^{-4z}, q^{-4z})`. -/
noncomputable def AzCoef (q : ℝ) (z : ℤ) : Fin 4 → ℝ
  | 0 => Real.rpow q (-(4 * (z : ℝ)))
  | 1 => -Real.rpow q (-(4 * (z : ℝ)))
  | 2 => -Real.rpow q (-(4 * (z : ℝ)))
  | 3 => Real.rpow q (-(4 * (z : ℝ)))

/-- The dressed mass `‖V^{(dr)}‖²_{L²(ϖ)}`: the squared `L²(ϖ)`-distance from `V` to the span
`U` of the four bond-pair duality functions, i.e. the minimum of `‖V − A‖²` over `A ∈ U`. -/
noncomputable def dressedMass [Fintype Config] (w V : Config → ℝ) (basis : Fin 4 → Config → ℝ) : ℝ :=
  ⨅ coef : Fin 4 → ℝ,
    ip w (fun c => V c - ∑ j, coef j * basis j c) (fun c => V c - ∑ j, coef j * basis j c)

/-! ## Step (1): the product form of `V_z` -/

/-
The single-species bond factor takes the value `0` if species `i` occupies neither or
both bond sites, `1` if only `z`, and `−q²` if only `z+1`.
-/
lemma phi_values (q : ℝ) (occ : Fin 2 → ℤ → Config → ℝ) (i : Fin 2) (z : ℤ) (c : Config)
    (h0 : occ i z c = 0 ∨ occ i z c = 1) (h1 : occ i (z + 1) c = 0 ∨ occ i (z + 1) c = 1) :
    phi q occ i z c = 0 ∨ phi q occ i z c = 1 ∨ phi q occ i z c = -q ^ 2 := by
  cases h0 <;> cases h1 <;> simp +decide [ *, phi ]

/-
**Lemma `lem:prod`** (support values of `V_z`).  On the four support configurations the
cross-term `V_z = φ¹_z φ²_z` takes the values `1, q⁴, −q², −q²`, matching the indicator form
`1_{(3,0)} + q⁴ 1_{(0,3)} − q² 1_{(1,2)} − q² 1_{(2,1)}`; off the support it vanishes.
-/
lemma Vbond_support_values (q : ℝ) (occ : Fin 2 → ℤ → Config → ℝ) (z : ℤ) (c : Config)
    (h00 : occ 0 z c = 0 ∨ occ 0 z c = 1) (h01 : occ 0 (z + 1) c = 0 ∨ occ 0 (z + 1) c = 1)
    (h10 : occ 1 z c = 0 ∨ occ 1 z c = 1) (h11 : occ 1 (z + 1) c = 0 ∨ occ 1 (z + 1) c = 1) :
    Vbond q occ z c = 0 ∨ Vbond q occ z c = 1 ∨ Vbond q occ z c = q ^ 4 ∨
      Vbond q occ z c = -q ^ 2 := by
  unfold Vbond;
  unfold phi; rcases h00 with ( h00 | h00 ) <;> rcases h01 with ( h01 | h01 ) <;> rcases h10 with ( h10 | h10 ) <;> rcases h11 with ( h11 | h11 ) <;> simp +decide [ * ] ; ring_nf ; norm_num;

/-
`|V_z| ≤ 1` pointwise (since `|q| ≤ 1`): each factor `φⁱ_z ∈ {0, 1, −q²}` has absolute
value `≤ 1`.
-/
lemma Vbond_abs_le_one (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (occ : Fin 2 → ℤ → Config → ℝ)
    (z : ℤ) (c : Config)
    (h00 : occ 0 z c = 0 ∨ occ 0 z c = 1) (h01 : occ 0 (z + 1) c = 0 ∨ occ 0 (z + 1) c = 1)
    (h10 : occ 1 z c = 0 ∨ occ 1 z c = 1) (h11 : occ 1 (z + 1) c = 0 ∨ occ 1 (z + 1) c = 1) :
    |Vbond q occ z c| ≤ 1 := by
  rcases Vbond_support_values q occ z c h00 h01 h10 h11 with h|h|h|h <;> rw [ h ] <;> norm_num [ abs_of_nonneg, hq0.le, hq1.le ];
  exact pow_le_one₀ hq0.le hq1.le

/-! ## Step (2): the dressing identity -/

/-
Counting particles strictly left of `z+1` adds the occupation at `z` to the count
strictly left of `z` (using that occupations vanish off `Λ`).
-/
lemma Nleft_succ (Λ : Finset ℤ) (occ : Fin 2 → ℤ → Config → ℝ)
    (hoccOut : ∀ i x c, x ∉ Λ → occ i x c = 0) (i : Fin 2) (z : ℤ) (c : Config) :
    Nleft Λ occ i (z + 1) c = Nleft Λ occ i z c + occ i z c := by
  by_cases h : z ∈ Λ <;> simp_all +decide [ Nleft ];
  · rw [ show ( Λ.filter fun x => x ≤ z ) = ( Λ.filter fun x => x < z ) ∪ { z } from ?_, Finset.sum_union ] <;> norm_num [ h ];
    grind;
  · rw [ show ( Finset.filter ( fun x => x ≤ z ) Λ ) = Finset.filter ( fun x => x < z ) Λ from ?_ ];
    · fin_cases i <;> aesop;
    · grind

/-
**Lemma `lem:dress`** (exact dressing identity).  With `α_i = 1`,
`F^i_z − F^i_{z+1} = − q^{2(z − L_i)} φⁱ_z`, where `L_i = N⁻_{z-1}(η_i) = Nleft Λ occ i z c`.
-/
lemma Fdual_diff (q : ℝ) (hq0 : 0 < q) (Λ : Finset ℤ) (occ : Fin 2 → ℤ → Config → ℝ)
    (hoccOut : ∀ i x c, x ∉ Λ → occ i x c = 0)
    (hocc01 : ∀ i x c, occ i x c = 0 ∨ occ i x c = 1)
    (i : Fin 2) (z : ℤ) (c : Config) :
    Fdual q Λ occ i z c - Fdual q Λ occ i (z + 1) c
      = -Real.rpow q (2 * ((z : ℝ) - Nleft Λ occ i z c)) * phi q occ i z c := by
  unfold Fdual phi;
  rw [ Nleft_succ ];
  · cases hocc01 i z c <;> cases hocc01 i ( z + 1 ) c <;> simp_all +decide ; ring;
    rw [ ← Real.rpow_natCast, ← Real.rpow_add hq0 ] ; ring;
  · exact hoccOut

/-! ## Step (3): `A_z = q^{-2(L₁+L₂)} V_z`, hence `V_z − A_z = (1 − q^{-2(L₁+L₂)}) V_z` -/

/-
`∑ⱼ AzCoef j · bpBasis j = q^{-4z}(F¹_z − F¹_{z+1})(F²_z − F²_{z+1})`.
-/
lemma Az_expand (q : ℝ) (Λ : Finset ℤ) (occ : Fin 2 → ℤ → Config → ℝ) (z : ℤ) (c : Config) :
    (∑ j, AzCoef q z j * bpBasis q Λ occ z j c)
      = Real.rpow q (-(4 * (z : ℝ)))
        * ((Fdual q Λ occ 0 z c - Fdual q Λ occ 0 (z + 1) c)
          * (Fdual q Λ occ 1 z c - Fdual q Λ occ 1 (z + 1) c)) := by
  rw [ Fin.sum_univ_four ] ; unfold AzCoef bpBasis ; ring;

/-
**Step (3)** (exact identity).  `V_z − A_z = (1 − q^{-2(L₁+L₂)}) V_z`, with
`L_i = Nleft Λ occ i z c`.
-/
lemma Vbond_sub_Az (q : ℝ) (hq0 : 0 < q) (Λ : Finset ℤ) (occ : Fin 2 → ℤ → Config → ℝ)
    (hoccOut : ∀ i x c, x ∉ Λ → occ i x c = 0)
    (hocc01 : ∀ i x c, occ i x c = 0 ∨ occ i x c = 1)
    (z : ℤ) (c : Config) :
    Vbond q occ z c - (∑ j, AzCoef q z j * bpBasis q Λ occ z j c)
      = (1 - Real.rpow q (-(2 * (Nleft Λ occ 0 z c + Nleft Λ occ 1 z c))))
        * Vbond q occ z c := by
  rw [ Az_expand ];
  rw [ Fdual_diff q hq0 Λ occ hoccOut hocc01, Fdual_diff q hq0 Λ occ hoccOut hocc01 ] ; ring;
  norm_num [ ← Real.rpow_add hq0 ] ; ring;
  rw [ show ( - ( z * 2 ) - Nleft Λ occ 0 z c * 2 : ℝ ) = - ( Nleft Λ occ 0 z c * 2 ) - Nleft Λ occ 1 z c * 2 - ( z * 2 - Nleft Λ occ 1 z c * 2 ) by ring ] ; rw [ Real.rpow_sub hq0 ] ; ring;
  simp +decide [ mul_assoc, ne_of_gt ( Real.rpow_pos_of_pos hq0 _ ) ];
  rfl

/-
`0 ≤ Nleft ≤ ℓ(z)`, the number of lattice sites strictly left of `z`.
-/
lemma Nleft_bounds (Λ : Finset ℤ) (occ : Fin 2 → ℤ → Config → ℝ)
    (hocc01 : ∀ i x c, occ i x c = 0 ∨ occ i x c = 1) (i : Fin 2) (z : ℤ) (c : Config) :
    0 ≤ Nleft Λ occ i z c ∧ Nleft Λ occ i z c ≤ ((Λ.filter (· < z)).card : ℝ) := by
  exact ⟨ Finset.sum_nonneg fun _ _ => by cases hocc01 i _ c <;> linarith, le_trans ( Finset.sum_le_sum fun _ _ => show occ i _ _ ≤ 1 from by cases hocc01 i _ c <;> linarith ) ( by simp +decide ) ⟩

/-
**Pointwise bound.**  `|V_z − A_z| ≤ (q^{-4ℓ(z)} − 1) |V_z|`.
-/
lemma Vbond_sub_Az_abs_le (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (Λ : Finset ℤ)
    (occ : Fin 2 → ℤ → Config → ℝ)
    (hoccOut : ∀ i x c, x ∉ Λ → occ i x c = 0)
    (hocc01 : ∀ i x c, occ i x c = 0 ∨ occ i x c = 1)
    (z : ℤ) (c : Config) :
    |Vbond q occ z c - (∑ j, AzCoef q z j * bpBasis q Λ occ z j c)|
      ≤ (Real.rpow q (-(4 * ((Λ.filter (· < z)).card : ℝ))) - 1) * |Vbond q occ z c| := by
  rw [ Vbond_sub_Az q hq0 Λ occ hoccOut hocc01 ];
  rw [ abs_mul ];
  gcongr;
  rw [ abs_of_nonpos ] <;> norm_num;
  · refine' Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le _;
    linarith [ Nleft_bounds Λ occ hocc01 0 z c, Nleft_bounds Λ occ hocc01 1 z c ];
  · exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le ( show ( - ( 2 * ( Nleft Λ occ 0 z c + Nleft Λ occ 1 z c ) ) ) ≤ 0 by linarith [ show 0 ≤ Nleft Λ occ 0 z c from by exact ( Nleft_bounds Λ occ hocc01 0 z c ).1, show 0 ≤ Nleft Λ occ 1 z c from by exact ( Nleft_bounds Λ occ hocc01 1 z c ).1 ] ) )

/-! ## Step (4): the Hilbert-space bound -/

/-
**Abstract dressed-mass bound.**  In `L²(ϖ)` with probability weight `w`, if `A` is any
element of the span `U` (a linear combination of the basis functions) and `|V − A| ≤ bound·|V|`
pointwise with `|V| ≤ 1`, then the dressed mass `‖V^{(dr)}‖² = min_{A'∈U} ‖V − A'‖²` is at
most `bound²`.
-/
lemma dressedMass_le [Fintype Config] (w V : Config → ℝ) (basis : Fin 4 → Config → ℝ) (coefA : Fin 4 → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    (hVle1 : ∀ c, |V c| ≤ 1)
    (hbnd : ∀ c, |V c - ∑ j, coefA j * basis j c| ≤ bound * |V c|) :
    dressedMass w V basis ≤ bound ^ 2 := by
  refine' ciInf_le_of_le _ coefA _;
  · exact ⟨ 0, Set.forall_mem_range.2 fun coef => Finset.sum_nonneg fun c _ => mul_nonneg ( hw c ) ( mul_self_nonneg _ ) ⟩;
  · refine' le_trans ( Finset.sum_le_sum fun c _ => _ ) _;
    use fun c => w c * bound ^ 2;
    · exact mul_le_mul_of_nonneg_left ( by nlinarith only [ abs_le.mp ( hbnd c ), abs_mul_abs_self ( V c - ∑ j, coefA j * basis j c ), abs_mul_abs_self ( V c ), show bound * |V c| ≤ bound by exact mul_le_of_le_one_right hb ( hVle1 c ) ] ) ( hw c );
    · rw [ ← Finset.sum_mul _ _ _, hw1, one_mul ]

/-
**Theorem `thm:main`** (dressed-mass estimate).  For an arbitrary probability weight `w`,
the dressed mass of the bond cross-term `V_z` satisfies
`‖V^{(dr)}_z‖²_{L²(ϖ)} ≤ (q^{-4ℓ(z)} − 1)²`, with `ℓ(z)` the number of lattice sites strictly
to the left of the bond.
-/
theorem dressedMass_bond_le [Fintype Config] (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (Λ : Finset ℤ)
    (occ : Fin 2 → ℤ → Config → ℝ)
    (hoccOut : ∀ i x c, x ∉ Λ → occ i x c = 0)
    (hocc01 : ∀ i x c, occ i x c = 0 ∨ occ i x c = 1)
    (w : Config → ℝ) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1) (z : ℤ) :
    dressedMass w (Vbond q occ z) (bpBasis q Λ occ z)
      ≤ (Real.rpow q (-(4 * ((Λ.filter (· < z)).card : ℝ))) - 1) ^ 2 := by
  apply_rules [ dressedMass_le ];
  any_goals exact AzCoef q z;
  · norm_num +zetaDelta at *;
    exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le ( show ( - ( 4 * ( Finset.card ( Finset.filter ( fun x => x < z ) Λ ) : ℝ ) ) ) ≤ 0 by linarith ) );
  · exact fun c => Vbond_abs_le_one q hq0 hq1 occ z c ( hocc01 0 z c ) ( hocc01 0 ( z + 1 ) c ) ( hocc01 1 z c ) ( hocc01 1 ( z + 1 ) c );
  · convert Vbond_sub_Az_abs_le q hq0 hq1 Λ occ hoccOut hocc01 z using 1

end TypeDDecoupling.DressedMass