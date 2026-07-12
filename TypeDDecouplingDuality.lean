import Mathlib

/-!
# Tier 3 black-box statements: the q-Krawtchouk self-duality framework (§model)

Statements of the orthogonal/triangular self-duality results of
`typeD_decoupling-draft-rev2.tex` that underlie `lem:crossbridge` and the cross-noise
reduction: `thm:dual` (orthogonal q-Krawtchouk self-duality), `cor:tri` (triangular form
at `n=∞`), `lem:acr` (duality covariance, after ACR), and `prop:orth` (orthogonality of
the duality functions).

Each is a **paper-level derivation that uses cited (black-box) inputs**, here formalized
and **proved** (no `sorry`): the cited inputs (the bondwise two-site interlacing verified
by computer algebra, the single-species q-Krawtchouk orthogonalities of CFG20, and the
`L¹`/Fubini regularity of the duality expansion) enter as hypotheses, and the paper's
reduction is carried out from them.  They are phrased as the genuine logical reductions
the paper uses:

* `thm:dual` / `cor:tri` — the generator self-duality `L D = D Lᵀ` follows from the
  bondwise (two-site) interlacing, verified by computer algebra in the paper, by linearity
  over the bond decomposition `L = Σ_b L_b`.  This is stated as the implication
  "bondwise interlacing ⟹ global self-duality".
* `prop:orth` — the two-species orthogonality is the product, under the product measure,
  of the single-species q-Krawtchouk orthogonalities (CFG20); stated as that product fact.
* `lem:acr` — the duality-covariance identity, derived from orthogonality and the duality
  relation.
-/

open scoped BigOperators
open MeasureTheory

namespace TypeDDecoupling

/-- Generator (intertwining) self-duality: `L` acting on the `η`-variable of `D` equals
the dual generator `Ld` acting on the `ξ`-variable, i.e. the interlacing `L D = D Lᵀ`. -/
def GeneratorDual {S Sd : Type*} (L : (S → ℝ) → S → ℝ) (Ld : (Sd → ℝ) → Sd → ℝ)
    (D : Sd → S → ℝ) : Prop :=
  ∀ (ξ : Sd) (η : S), L (fun η' => D ξ η') η = Ld (fun ξ' => D ξ' η) ξ

/-! ## `thm:dual` — orthogonal q-Krawtchouk self-duality -/

/-
**Theorem `thm:dual`** (orthogonal q-Krawtchouk self-duality; \cite[Thm.~3.1]{REU}).
For the type D ASEP at `n=∞` (and `n=2,3`), the process is self-dual with respect to the
two-point q-Krawtchouk product `D_{α₁,α₂}` of (eq:Dreu): the interlacing `L D = D Lᵀ`.

*The paper's reduction, formalized and proved here* (taking the bondwise two-site
interlacing `hbond`, verified by computer algebra in the paper, as the cited input):
writing the generator as a sum of bond-local terms `L = Σ_b L_b` (and `Lᵀ = Σ_b L_bᵀ`), the global
interlacing follows from the bondwise interlacing `hbond` (the two-site identity the paper
verifies by computer algebra).  `D` is the function (eq:Dreu).
-/
theorem thm_dual {S Sd : Type*}
    (L : (S → ℝ) → S → ℝ) (Ld : (Sd → ℝ) → Sd → ℝ) (D : Sd → S → ℝ)
    (Lbond : ℤ → (S → ℝ) → S → ℝ) (Ldbond : ℤ → (Sd → ℝ) → Sd → ℝ)
    (hLdecomp : ∀ (f : S → ℝ) (s : S), L f s = ∑' b : ℤ, Lbond b f s)
    (hLddecomp : ∀ (g : Sd → ℝ) (d : Sd), Ld g d = ∑' b : ℤ, Ldbond b g d)
    (hbond : ∀ (b : ℤ) (ξ : Sd) (η : S),
        Lbond b (fun η' => D ξ η') η = Ldbond b (fun ξ' => D ξ' η) ξ) :
    GeneratorDual L Ld D := by
  intro ξ η; rw [ hLdecomp, hLddecomp ] ; congr; ext b; aesop;

/-! ## `cor:tri` — triangular form at `n=∞` -/

/-
**Corollary `cor:tri`** (triangular self-duality at `n=∞`; \cite{KLLPZ}).
At `n=∞` the type D ASEP is self-dual with respect to the triangular function
`D^{tri}(ξ,η) = 𝟙{ξ⊆η} ∏_i ∏_{x:ξ_{i,x}=1} q^{2(x − N⁻_{x−1}(ξ_i) + N⁺_{x+1}(η_i))}`
(eq:Dtri), obtained from (eq:Dreu) by extracting the leading `α_i → 0` coefficients.

*The paper's reduction, formalized and proved here.*  As in `thm_dual`, the bondwise ⟹
global reduction for `Dtri` (eq:Dtri), with `hbond` the cited two-site input.
-/
theorem cor_tri {S Sd : Type*}
    (L : (S → ℝ) → S → ℝ) (Ld : (Sd → ℝ) → Sd → ℝ) (Dtri : Sd → S → ℝ)
    (Lbond : ℤ → (S → ℝ) → S → ℝ) (Ldbond : ℤ → (Sd → ℝ) → Sd → ℝ)
    (hLdecomp : ∀ (f : S → ℝ) (s : S), L f s = ∑' b : ℤ, Lbond b f s)
    (hLddecomp : ∀ (g : Sd → ℝ) (d : Sd), Ld g d = ∑' b : ℤ, Ldbond b g d)
    (hbond : ∀ (b : ℤ) (ξ : Sd) (η : S),
        Lbond b (fun η' => Dtri ξ η') η = Ldbond b (fun ξ' => Dtri ξ' η) ξ) :
    GeneratorDual L Ld Dtri := by
  intro ξ η; rw [ hLdecomp, hLddecomp ] ; exact tsum_congr ( fun b => hbond b ξ η ) ;

/-! ## `lem:acr` — duality covariance (after ACR) -/

/-
**Lemma `lem:acr`** (duality covariance; after \cite[Lem.~2.1]{ACR}).
Let `{D(ξ,·)}` be a family of duality functions orthogonal in `L²(ϖ)`,
`∫ D(ξ,·)D(ξ',·) dϖ = δ_{ξ,ξ'} a(ξ)`.  Then for all `ξ,ξ'` and `t ≥ 0`,
`∫ E_η[D(ξ,η_t)] D(ξ',η) dϖ(η) = p_t(ξ,ξ') a(ξ')`.

*The paper's derivation, formalized and proved here* from the orthogonality `horth` and
the duality relation `hdual` (after \cite[Lem.~2.1]{ACR}).  `Et ξ t η = E_η[D(ξ,η_t)]` is
the time-evolved duality function, `pdual` the dual transition kernel, `a` the squared
norms, with the duality relation `Et ξ t η = Σ_{ξ''} p_t(ξ,ξ'') D(ξ'',η)` recorded in
`hdual`.  The cited input is supplied as the genuine `L¹`/Fubini regularity of the
duality expansion (`hint`: each term is integrable; `hsumm`: the integrated norms are
summable), under which the integral and the duality series may be interchanged.
-/
theorem lem_acr {S Sd : Type*} [MeasurableSpace S] [DecidableEq Sd] [Countable Sd]
    (ϖ : Measure S)
    (D : Sd → S → ℝ) (a : Sd → ℝ)
    (Et : Sd → ℝ → S → ℝ) (pdual : ℝ → Sd → Sd → ℝ)
    (horth : ∀ ξ ξ' : Sd, (∫ η, D ξ η * D ξ' η ∂ϖ) = if ξ = ξ' then a ξ else 0)
    (hdual : ∀ (ξ : Sd) (t : ℝ) (η : S), Et ξ t η = ∑' ξ'' : Sd, pdual t ξ ξ'' * D ξ'' η)
    (hint : ∀ (ξ ξ' : Sd) (t : ℝ) (ξ'' : Sd),
        Integrable (fun η => pdual t ξ ξ'' * (D ξ'' η * D ξ' η)) ϖ)
    (hsumm : ∀ (ξ ξ' : Sd) (t : ℝ),
        Summable (fun ξ'' => ∫ η, ‖pdual t ξ ξ'' * (D ξ'' η * D ξ' η)‖ ∂ϖ)) :
    ∀ (ξ ξ' : Sd) (t : ℝ), 0 ≤ t →
      (∫ η, Et ξ t η * D ξ' η ∂ϖ) = pdual t ξ ξ' * a ξ' := by
  intro ξ ξ' t ht;
  -- Apply the linearity of the integral and the orthogonality relation.
  have h_integral : ∫ η, ∑' ξ'', pdual t ξ ξ'' * D ξ'' η * D ξ' η ∂ϖ = ∑' ξ'', pdual t ξ ξ'' * ∫ η, D ξ'' η * D ξ' η ∂ϖ := by
    convert MeasureTheory.integral_tsum _ _ using 1;
    · simp +decide only [mul_assoc, integral_const_mul];
    · infer_instance;
    · exact fun ξ'' => by simpa only [ mul_assoc ] using ( ‹∀ ξ ξ' : Sd, ∀ t : ℝ, ∀ ξ'' : Sd, Integrable ( fun η => pdual t ξ ξ'' * ( D ξ'' η * D ξ' η ) ) ϖ› ξ ξ' t ξ'' |> MeasureTheory.Integrable.aestronglyMeasurable ) ;
    · refine' ne_of_lt ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum fun i => _ ) _ );
      use fun i => ENNReal.ofReal ( ∫ η, ‖pdual t ξ i * ( D i η * D ξ' η )‖ ∂ϖ );
      · rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
        · simp +decide [ mul_assoc, ENorm.enorm ];
          norm_num [ ← ENNReal.ofReal_coe_nnreal ];
        · exact MeasureTheory.Integrable.norm ( ‹∀ ξ ξ' : Sd, ∀ t : ℝ, ∀ ξ'' : Sd, Integrable ( fun η => pdual t ξ ξ'' * ( D ξ'' η * D ξ' η ) ) ϖ› ξ ξ' t i );
        · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
      · rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num [ hsumm ];
        · exact fun _ => MeasureTheory.integral_nonneg fun _ => by positivity;
        · simpa [ abs_mul ] using hsumm ξ ξ' t;
  simp_all +decide [ ← mul_assoc, tsum_mul_right ]

/-! ## `prop:orth` — orthogonality of the duality functions -/

/-
**Proposition `prop:orth`** (orthogonality; \cite[Thm.~3.2]{CFG20}, \cite[§3.1]{REU}).
For the sector-reweighted blocking measure `ϖ = ϖ_{α₁} ⊗ ϖ_{α₂}`, the duality functions
`D̄` are orthogonal in `L²(ϖ)`: `∫ D̄(ξ,·) D̄(ξ',·) dϖ = δ_{ξ,ξ'} a(ξ)`.

*Formalized and proved here* (from the single-species q-Krawtchouk orthogonalities `h1`,
`h2`, the cited CFG20 inputs, by Fubini over the product measure): the
two-species family `D̄(ξ,η) = D₁(ξ₁,η₁)·D₂(ξ₂,η₂)` is orthogonal in `L²(ϖ₁ ⊗ ϖ₂)`
because it is the product of the single-species q-Krawtchouk orthogonalities `h1`, `h2`
(CFG20).
-/
theorem prop_orth {S₁ S₂ Sd₁ Sd₂ : Type*}
    [MeasurableSpace S₁] [MeasurableSpace S₂] [DecidableEq Sd₁] [DecidableEq Sd₂]
    (ϖ₁ : Measure S₁) (ϖ₂ : Measure S₂) [SigmaFinite ϖ₁] [SigmaFinite ϖ₂]
    (D₁ : Sd₁ → S₁ → ℝ) (D₂ : Sd₂ → S₂ → ℝ) (a₁ : Sd₁ → ℝ) (a₂ : Sd₂ → ℝ)
    (h1 : ∀ ξ ξ' : Sd₁, (∫ η, D₁ ξ η * D₁ ξ' η ∂ϖ₁) = if ξ = ξ' then a₁ ξ else 0)
    (h2 : ∀ ξ ξ' : Sd₂, (∫ η, D₂ ξ η * D₂ ξ' η ∂ϖ₂) = if ξ = ξ' then a₂ ξ else 0) :
    ∀ ξ ξ' : Sd₁ × Sd₂,
      (∫ η, (D₁ ξ.1 η.1 * D₂ ξ.2 η.2) * (D₁ ξ'.1 η.1 * D₂ ξ'.2 η.2) ∂(ϖ₁.prod ϖ₂))
        = if ξ = ξ' then a₁ ξ.1 * a₂ ξ.2 else 0 := by
  intro ξ ξ';
  convert congr_arg₂ ( · * · ) ( h1 ξ.1 ξ'.1 ) ( h2 ξ.2 ξ'.2 ) using 1;
  · rw [ ← MeasureTheory.integral_prod_mul ] ; congr ; ext ; ring;
  · grind

end TypeDDecoupling