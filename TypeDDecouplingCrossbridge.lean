import Mathlib

/-!
# `lem:crossbridge` on a finite lattice — the algebraic core, machine-checked

This file formalizes, for a **finite** lattice `Λ = {-L, …, L}`, the algebraic core of
`lem:crossbridge` from the type D ASEP paper (the continuum statement lives in
`TypeDDecouplingCrossover.lean` as `lem_crossbridge`, whose `sorry` covers only the
scaling embedding — see the docstring cross-reference there).

The three steps of `crossbridge_finiteL_brief.tex` are carried out here:

* **Step 1 (interlacing ⇒ semigroup duality).**  The general linear-algebra fact that an
  intertwining `A D = D B` of finite matrices lifts to the matrix exponentials,
  `exp A · D = D · exp B`, is proved from scratch (`exp_intertwine_gen` for a Banach
  algebra, `matrix_exp_intertwine` for rectangular matrices via a block embedding, using
  `matrix_exp_fromBlocks_diag`).  This is the exact content of
  `e^{sL} D = D e^{sL_{dual}^{T}}`.

  The two-particle-sector interlacing `L_{dual} D = D L^{T}` itself is taken as a named
  hypothesis of the main theorem (the *sanctioned fallback* of the brief: this matches the
  paper's own epistemic status — `thm:dual`(ii)/`cor:tri` rest on computer-algebra
  verification plus the REU induction).  Everything downstream is proved `sorry`-free from
  it, for **all** `L`.

* **Step 2 (block evaluation).**  With the block `η⁰` = bound pairs (state `3`) on
  `{-L,…,0}` and empty on `{1,…,L}`, the triangular duality function of a two-particle
  dual at positions `(x₁,x₂)` evaluates to `𝟙{x₁≤0}·𝟙{x₂≤0}` — the boundary constant is
  `q^{2k}` with `k = 0` in this normalisation (`Dtri_block_eval`).

* **Step 3 (the crossbridge identity `eq:cb`).**  Combining Steps 1–2 gives, for every `s`,
  `E_{η⁰}[η_{1,a}(s) η_{2,a}(s) q^{2(a+N⁺_{a+1}(η₁(s)))+2(a+N⁺_{a+1}(η₂(s)))}]
     = q^{2k} · ℙ_{(a,a)}(X₁(s)≤0, X₂(s)≤0)`
  with both sides defined directly from the finite semigroups (`crossbridge_finiteL`).
  This is the identity the paper verified numerically for `L ≤ 6`; here it is a theorem for
  all `L`.
-/

open NormedSpace
open scoped Matrix BigOperators

namespace TypeDDecoupling.Crossbridge

/-! ## Step 1 (general): the exponential intertwining -/

section Step1
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **Intertwining of exponentials in a Banach algebra.**  If `a * d = d * b` then
`exp a * d = d * exp b`.  Proved by the power-series induction `a^k d = d b^k` and moving
the (continuous, linear) maps `· * d` and `d * ·` through the exponential `tsum`. -/
theorem exp_intertwine_gen {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    {a b d : 𝔸} (h : a * d = d * b) : exp a * d = d * exp b := by
  have hpow : ∀ k : ℕ, a ^ k * d = d * b ^ k := by
    intro k; induction k with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc]
  set φ : 𝔸 →L[ℝ] 𝔸 := (ContinuousLinearMap.mul ℝ 𝔸).flip d
  set ψ : 𝔸 →L[ℝ] 𝔸 := ContinuousLinearMap.mul ℝ 𝔸 d
  have e1 : exp a * d = φ (exp a) := rfl
  have e2 : d * exp b = ψ (exp b) := rfl
  rw [e1, e2, exp_eq_tsum ℝ, φ.map_tsum (expSeries_summable' a),
    ψ.map_tsum (expSeries_summable' b)]
  congr 1; ext n
  simp only [φ, ψ, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']
  rw [smul_mul_assoc, mul_smul_comm, hpow n]

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The exponential of a block-diagonal matrix is block diagonal, with the exponentials of
the diagonal blocks.  Proved via the four block projections as continuous linear maps and
`(fromBlocks A 0 0 B)^n = fromBlocks (A^n) 0 0 (B^n)`. -/
theorem matrix_exp_fromBlocks_diag (A : Matrix I I ℝ) (B : Matrix J J ℝ) :
    exp (Matrix.fromBlocks A 0 0 B) = Matrix.fromBlocks (exp A) 0 0 (exp B) := by
  have hpow : ∀ n : ℕ, (Matrix.fromBlocks A 0 0 B) ^ n = Matrix.fromBlocks (A ^ n) 0 0 (B ^ n) := by
    intro n; induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, Matrix.fromBlocks_multiply]; simp [pow_succ]
  let P11 : Matrix (I ⊕ J) (I ⊕ J) ℝ →L[ℝ] Matrix I I ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := Matrix.toBlocks₁₁, map_add' := fun x y => rfl, map_smul' := fun c x => rfl }
  let P22 : Matrix (I ⊕ J) (I ⊕ J) ℝ →L[ℝ] Matrix J J ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := Matrix.toBlocks₂₂, map_add' := fun x y => rfl, map_smul' := fun c x => rfl }
  let P12 : Matrix (I ⊕ J) (I ⊕ J) ℝ →L[ℝ] Matrix I J ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := Matrix.toBlocks₁₂, map_add' := fun x y => rfl, map_smul' := fun c x => rfl }
  let P21 : Matrix (I ⊕ J) (I ⊕ J) ℝ →L[ℝ] Matrix J I ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := Matrix.toBlocks₂₁, map_add' := fun x y => rfl, map_smul' := fun c x => rfl }
  have hs := expSeries_summable' (𝕂 := ℝ) (Matrix.fromBlocks A 0 0 B)
  rw [← Matrix.fromBlocks_toBlocks (exp (Matrix.fromBlocks A 0 0 B))]
  have E11 : (exp (Matrix.fromBlocks A 0 0 B)).toBlocks₁₁ = exp A := by
    show P11 (exp (Matrix.fromBlocks A 0 0 B)) = exp A
    rw [exp_eq_tsum ℝ, P11.map_tsum hs, exp_eq_tsum ℝ]
    apply tsum_congr; intro n; rw [map_smul]; congr 1
    show (Matrix.fromBlocks A 0 0 B ^ n).toBlocks₁₁ = A ^ n
    rw [hpow]; rfl
  have E22 : (exp (Matrix.fromBlocks A 0 0 B)).toBlocks₂₂ = exp B := by
    show P22 (exp (Matrix.fromBlocks A 0 0 B)) = exp B
    rw [exp_eq_tsum ℝ, P22.map_tsum hs, exp_eq_tsum ℝ]
    apply tsum_congr; intro n; rw [map_smul]; congr 1
    show (Matrix.fromBlocks A 0 0 B ^ n).toBlocks₂₂ = B ^ n
    rw [hpow]; rfl
  have E12 : (exp (Matrix.fromBlocks A 0 0 B)).toBlocks₁₂ = 0 := by
    have hz : ∀ n : ℕ, P12 ((n.factorial : ℝ)⁻¹ • Matrix.fromBlocks A 0 0 B ^ n) = 0 := by
      intro n; rw [map_smul]
      show (n.factorial : ℝ)⁻¹ • (Matrix.fromBlocks A 0 0 B ^ n).toBlocks₁₂ = 0
      rw [hpow]; ext i j; simp [Matrix.toBlocks₁₂]
    show P12 (exp (Matrix.fromBlocks A 0 0 B)) = 0
    rw [exp_eq_tsum ℝ, P12.map_tsum hs]; simp only [hz, tsum_zero]
  have E21 : (exp (Matrix.fromBlocks A 0 0 B)).toBlocks₂₁ = 0 := by
    have hz : ∀ n : ℕ, P21 ((n.factorial : ℝ)⁻¹ • Matrix.fromBlocks A 0 0 B ^ n) = 0 := by
      intro n; rw [map_smul]
      show (n.factorial : ℝ)⁻¹ • (Matrix.fromBlocks A 0 0 B ^ n).toBlocks₂₁ = 0
      rw [hpow]; ext i j; simp [Matrix.toBlocks₂₁]
    show P21 (exp (Matrix.fromBlocks A 0 0 B)) = 0
    rw [exp_eq_tsum ℝ, P21.map_tsum hs]; simp only [hz, tsum_zero]
  rw [E11, E22, E12, E21]

/-- **Rectangular exponential intertwining.**  For finite matrices `A : I×I`, `B : J×J`,
`D : I×J` with `A D = D B`, one has `exp A · D = D · exp B`.  Proved by embedding into the
square algebra over `I ⊕ J`, where `exp_intertwine_gen` applies. -/
theorem matrix_exp_intertwine (A : Matrix I I ℝ) (B : Matrix J J ℝ) (D : Matrix I J ℝ)
    (h : A * D = D * B) : exp A * D = D * exp B := by
  have hcomm : Matrix.fromBlocks A 0 0 B * Matrix.fromBlocks 0 D 0 0
             = Matrix.fromBlocks 0 D 0 0 * Matrix.fromBlocks A 0 0 B := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]; simp [h]
  have hexp := exp_intertwine_gen hcomm
  rw [matrix_exp_fromBlocks_diag, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hexp
  simp only [mul_zero, zero_mul, add_zero, zero_add] at hexp
  have h12 := congrArg Matrix.toBlocks₁₂ hexp
  simpa [Matrix.toBlocks₁₂] using h12

end Step1

/-! ## The finite lattice and the triangular duality function -/

/-- The finite lattice `{-L,…,L}` as `Fin (2L+1)`. -/
abbrev Site (L : ℕ) := Fin (2 * L + 1)

/-- The integer position of a site: site `i` sits at `i - L ∈ {-L,…,L}`. -/
def sitePos {L : ℕ} (i : Site L) : ℤ := (i : ℤ) - (L : ℤ)

/-- A process configuration: each site carries one of four states
`0` empty, `1` species 1, `2` species 2, `3` bound pair. -/
abbrev Config (L : ℕ) := Site L → Fin 4

/-- A two-particle dual state: one species-1 particle and one species-2 particle, given by
their positions. -/
abbrev Dual (L : ℕ) := Site L × Site L

/-- Species-1 occupation of a configuration at a site (`1` if species 1 is present, i.e.
state `1` or the bound pair `3`). -/
def occ1 {L : ℕ} (η : Config L) (i : Site L) : ℝ := if η i = 1 ∨ η i = 3 then 1 else 0

/-- Species-2 occupation of a configuration at a site (`1` if species 2 is present, i.e.
state `2` or the bound pair `3`). -/
def occ2 {L : ℕ} (η : Config L) (i : Site L) : ℝ := if η i = 2 ∨ η i = 3 then 1 else 0

/-- `N⁺_{x+1}(η₁)`: the number of species-1 particles strictly to the right of `x`. -/
def Nplus1 {L : ℕ} (η : Config L) (x : Site L) : ℤ :=
  ((Finset.univ.filter (fun y : Site L => x < y ∧ (η y = 1 ∨ η y = 3))).card : ℤ)

/-- `N⁺_{x+1}(η₂)`: the number of species-2 particles strictly to the right of `x`. -/
def Nplus2 {L : ℕ} (η : Config L) (x : Site L) : ℤ :=
  ((Finset.univ.filter (fun y : Site L => x < y ∧ (η y = 2 ∨ η y = 3))).card : ℤ)

/-- The **triangular duality function** on the two-particle sector: for a dual state
`ξ = (x₁,x₂)` and a configuration `η`,
`D^{tri}(ξ,η) = 𝟙{sp1 at x₁}·𝟙{sp2 at x₂}·q^{2(x₁+N⁺(η₁,x₁))}·q^{2(x₂+N⁺(η₂,x₂))}`.
(The `N⁻` term of the general definition vanishes since there is one particle per species.) -/
noncomputable def Dtri {L : ℕ} (q : ℝ) (ξ : Dual L) (η : Config L) : ℝ :=
  occ1 η ξ.1 * occ2 η ξ.2
    * q ^ (2 * (sitePos ξ.1 + Nplus1 η ξ.1))
    * q ^ (2 * (sitePos ξ.2 + Nplus2 η ξ.2))

/-- The duality matrix `D[ξ,η] = D^{tri}(ξ,η)`. -/
noncomputable def Dmat {L : ℕ} (q : ℝ) : Matrix (Dual L) (Config L) ℝ := fun ξ η => Dtri q ξ η

/-- The block initial configuration `η⁰`: bound pairs (state `3`) on `{-L,…,0}`, empty on
`{1,…,L}`. -/
def eta0 {L : ℕ} : Config L := fun i => if sitePos i ≤ 0 then 3 else 0

/-! ## Step 2: block evaluation of the triangular duality function -/

/-- Counting lemma for the block: for a site `x` with `sitePos x ≤ 0`, the number of sites
strictly to its right with `sitePos ≤ 0` is `-(sitePos x)`. -/
theorem block_count {L : ℕ} (x : Site L) (hx : sitePos x ≤ 0) :
    ((Finset.univ.filter (fun y : Site L => x < y ∧ sitePos y ≤ 0)).card : ℤ) = -(sitePos x) := by
  simp +decide [sitePos] at hx ⊢;
  rw [ show ( Finset.filter ( fun y : Fin ( 2 * L + 1 ) => x < y ∧ ( y : ℕ ) ≤ L ) Finset.univ ) = Finset.Ioc x ⟨ L, by linarith ⟩ from ?_ ] ; aesop;
  ext; aesop

/-- **Step 2 (block evaluation).**  At the block `η⁰`, the triangular duality function of a
two-particle dual `ξ = (x₁,x₂)` equals `𝟙{x₁≤0}·𝟙{x₂≤0}`; i.e. the boundary constant is
`q^{2k}` with `k = 0` in this normalisation. -/
theorem Dtri_block_eval {L : ℕ} (q : ℝ) (ξ : Dual L) :
    Dtri q ξ eta0
      = (if sitePos ξ.1 ≤ 0 then 1 else 0) * (if sitePos ξ.2 ≤ 0 then 1 else 0) := by
  unfold Dtri occ1 occ2;
  simp [eta0];
  split_ifs <;> simp_all +decide [ Nplus1, Nplus2 ];
  · rw [ show ( Finset.filter ( fun y => ξ.1 < y ∧ ( eta0 y = 1 ∨ eta0 y = 3 ) ) Finset.univ ) = Finset.filter ( fun y => ξ.1 < y ∧ sitePos y ≤ 0 ) Finset.univ from ?_, show ( Finset.filter ( fun y => ξ.2 < y ∧ ( eta0 y = 2 ∨ eta0 y = 3 ) ) Finset.univ ) = Finset.filter ( fun y => ξ.2 < y ∧ sitePos y ≤ 0 ) Finset.univ from ?_ ];
    · have := block_count ξ.1 ‹_›; have := block_count ξ.2 ‹_›; aesop;
    · unfold eta0; aesop;
    · unfold eta0; aesop;
  · lia;
  · grind;
  · linarith

/-! ## Step 3: the crossbridge identity `eq:cb` -/

/-- The η-side crossbridge observable, exactly `eq:cb`'s integrand with `a = sitePos siteA`:
`η_{1,a}·η_{2,a}·q^{2(a+N⁺_{a+1}(η₁))+2(a+N⁺_{a+1}(η₂))}`.  Definitionally
`crossObs q siteA η = D^{tri}((siteA,siteA), η)`. -/
noncomputable def crossObs {L : ℕ} (q : ℝ) (siteA : Site L) : Config L → ℝ := fun η =>
  occ1 η siteA * occ2 η siteA
    * q ^ (2 * (sitePos siteA + Nplus1 η siteA))
    * q ^ (2 * (sitePos siteA + Nplus2 η siteA))

/-- The dual-side hitting indicator `𝟙{x₁≤0}·𝟙{x₂≤0}` on dual states. -/
noncomputable def hitIndicator {L : ℕ} : Dual L → ℝ := fun ξ =>
  (if sitePos ξ.1 ≤ 0 then 1 else 0) * (if sitePos ξ.2 ≤ 0 then 1 else 0)

/-- `crossObs` is the triangular duality function at the two-particle dual `(siteA,siteA)`. -/
theorem crossObs_eq_Dtri {L : ℕ} (q : ℝ) (siteA : Site L) :
    crossObs q siteA = fun η => Dtri q (siteA, siteA) η := rfl

section Step3
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **`lem:crossbridge` on a finite lattice (`eq:cb`).**  Fix `q ∈ (0,1)`, a process
generator `Lgen` and a two-particle-sector dual generator `Ldual` satisfying the
interlacing `Ldual · D = D · Lgenᵀ` (Step 1's input; see the module docstring).  Then for
every time `s` and every dual site `siteA`,
`E_{η⁰}[crossObs(s)] = q^{2·0} · ℙ_{(siteA,siteA)}(X₁(s)≤0, X₂(s)≤0)`,
where the left side is the process semigroup `exp(s·Lgen)` applied to the η-side observable
`crossObs` (the `eq:cb` integrand), and the right side is the dual semigroup
`exp(s·Ldual)` applied to the hitting indicator, times the explicit block constant `q^{2k}`
with `k = 0`.

The `s ≥ 0` restriction of the paper is unnecessary here (the matrix exponential is entire),
so the identity is stated for all real `s`. -/
theorem crossbridge_finiteL {L : ℕ} (q : ℝ) (_hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (Lgen : Matrix (Config L) (Config L) ℝ) (Ldual : Matrix (Dual L) (Dual L) ℝ)
    (hinter : Ldual * Dmat q = Dmat q * (Lgen)ᵀ)
    (siteA : Site L) (s : ℝ) :
    (exp (s • Lgen) *ᵥ crossObs q siteA) eta0
      = q ^ (2 * (0 : ℤ)) * (exp (s • Ldual) *ᵥ hitIndicator) (siteA, siteA) := by
  -- Step 1: scale the interlacing and lift it to the exponentials.
  have hscale : (s • Ldual) * Dmat q = Dmat q * ((s • Lgen)ᵀ) := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hinter]
  have hB : exp (s • Ldual) * Dmat q = Dmat q * exp ((s • Lgen)ᵀ) :=
    matrix_exp_intertwine (s • Ldual) ((s • Lgen)ᵀ) (Dmat q) hscale
  rw [Matrix.exp_transpose] at hB
  -- hB : exp (s • Ldual) * Dmat q = Dmat q * (exp (s • Lgen))ᵀ
  -- The block constant q^{2·0} = 1.
  rw [show (2 * (0 : ℤ)) = 0 by ring, zpow_zero, one_mul]
  -- LHS is the (ξ₀, η⁰) entry of `Dmat q * (exp (s•Lgen))ᵀ`.
  have hgoalL : (exp (s • Lgen) *ᵥ crossObs q siteA) eta0
      = (Dmat q * (exp (s • Lgen))ᵀ : Matrix (Dual L) (Config L) ℝ) (siteA, siteA) eta0 := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun x _ => by
      rw [show Dmat q (siteA, siteA) x = crossObs q siteA x from rfl]; ring)
  -- RHS is (by Step 2) the (ξ₀, η⁰) entry of `exp (s•Ldual) * Dmat q`.
  have hgoalR : (exp (s • Ldual) *ᵥ hitIndicator) (siteA, siteA)
      = (exp (s • Ldual) * Dmat q : Matrix (Dual L) (Config L) ℝ) (siteA, siteA) eta0 := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl (fun ξ' _ => by
      rw [show Dmat q ξ' eta0 = Dtri q ξ' eta0 from rfl, Dtri_block_eval]; rfl)
  rw [hgoalL, hgoalR, hB]

end Step3

end TypeDDecoupling.Crossbridge