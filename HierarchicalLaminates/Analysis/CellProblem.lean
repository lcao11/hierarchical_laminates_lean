module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The abstract periodic cell problem

In a real Hilbert space, a complete submodule specifies the admissible gradient
corrections. Lax--Milgram gives the unique equilibrated field at each loading
for a bounded coercive operator. When the operator is symmetric, this field
minimizes its quadratic energy over the affine space of admissible fields.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Coercivity of a material operator, with an explicit lower bound. -/
def CoerciveLaw (A : H →L[ℝ] H) (μ : ℝ) : Prop :=
  ∀ v : H, μ * ‖v‖ * ‖v‖ ≤ inner ℝ (A v) v

/-- Symmetry in the real Hilbert-space formulation. -/
def SymmetricLaw (A : H →L[ℝ] H) : Prop :=
  ∀ v w : H, inner ℝ (A v) w = inner ℝ v (A w)

/-- A field has the prescribed affine gradient and an equilibrated flux. -/
def IsCellField (G : Submodule ℝ H) (A : H →L[ℝ] H) (F e : H) : Prop :=
  e - F ∈ G ∧ ∀ g ∈ G, inner ℝ (A e) g = 0

/-- An equilibrium flux pairs with an affine field through its loading alone. -/
theorem cell_pairing_eq {G : Submodule ℝ H} {A : H →L[ℝ] H}
    {F e F' v : H} (he : IsCellField G A F e) (hv : v - F' ∈ G) :
    inner ℝ (A e) v = inner ℝ (A e) F' := by
  have hz := he.2 (v - F') hv
  rw [inner_sub_right] at hz
  exact sub_eq_zero.mp hz

/-- Two equilibrated fields at the same loading agree under coercivity. -/
theorem cellField_unique {G : Submodule ℝ H} {A : H →L[ℝ] H}
    {μ : ℝ} (hμ : 0 < μ) (hA : CoerciveLaw A μ) {F e₁ e₂ : H}
    (h₁ : IsCellField G A F e₁) (h₂ : IsCellField G A F e₂) : e₁ = e₂ := by
  have hd : e₁ - e₂ ∈ G := by
    simpa only [sub_sub_sub_cancel_right] using G.sub_mem h₁.1 h₂.1
  have hz : inner ℝ (A (e₁ - e₂)) (e₁ - e₂) = 0 := by
    rw [map_sub, inner_sub_left, h₁.2 _ hd, h₂.2 _ hd, sub_self]
  have hc := hA (e₁ - e₂)
  rw [hz] at hc
  have hn : ‖e₁ - e₂‖ = 0 := by
    by_contra hn
    have hpos : 0 < ‖e₁ - e₂‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    exact (not_lt_of_ge hc) (mul_pos (mul_pos hμ hpos) hpos)
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Orthogonality gives the exact quadratic energy increment. -/
theorem cell_energy_increment {G : Submodule ℝ H} {A : H →L[ℝ] H}
    (hA : SymmetricLaw A) {F e v : H} (he : IsCellField G A F e)
    (hv : v - F ∈ G) :
    inner ℝ (A v) v = inner ℝ (A e) e + inner ℝ (A (v - e)) (v - e) := by
  have hd : v - e ∈ G := by
    simpa only [sub_sub_sub_cancel_right] using G.sub_mem hv he.1
  have hcross : inner ℝ (A e) (v - e) = 0 := he.2 _ hd
  have hcross' : inner ℝ (A (v - e)) e = 0 := by
    rw [hA, real_inner_comm, hcross]
  have hv' : v = e + (v - e) := by abel
  conv_lhs => rw [hv']
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hcross, hcross']
  ring

/-- An equilibrated field minimizes energy over its affine gradient space. -/
theorem cell_energy_minimal {G : Submodule ℝ H} {A : H →L[ℝ] H}
    (hAs : SymmetricLaw A) {μ : ℝ} (hμ : 0 ≤ μ) (hA : CoerciveLaw A μ)
    {F e v : H} (he : IsCellField G A F e) (hv : v - F ∈ G) :
    inner ℝ (A e) e ≤ inner ℝ (A v) v := by
  rw [cell_energy_increment hAs he hv]
  have hc := hA (v - e)
  have hn : 0 ≤ μ * ‖v - e‖ * ‖v - e‖ := by positivity
  linarith

section Existence

variable (G : Submodule ℝ H) [CompleteSpace G]

/-- Orthogonal projection preserves the pairing against a member of the subspace. -/
theorem inner_projection (x : H) (g : G) :
    inner ℝ (G.orthogonalProjectionOnto x) g = inner ℝ x (g : H) := by
  exact G.inner_orthogonalProjectionOnto_eq_of_mem_right g x

/-- The material operator restricted to the gradient subspace. -/
def restrictedOperator (A : H →L[ℝ] H) : G →L[ℝ] G :=
  G.orthogonalProjectionOnto.comp (A.comp G.subtypeL)

/-- The bounded bilinear form to which Lax--Milgram is applied. -/
def restrictedForm (A : H →L[ℝ] H) : G →L[ℝ] G →L[ℝ] ℝ :=
  (innerSL ℝ).comp (restrictedOperator G A)

@[simp]
theorem restrictedForm_apply (A : H →L[ℝ] H) (g h : G) :
    restrictedForm G A g h = inner ℝ (A (g : H)) (h : H) := by
  exact inner_projection G (A (g : H)) h

theorem restrictedForm_coercive {A : H →L[ℝ] H} {μ : ℝ}
    (hμ : 0 < μ) (hA : CoerciveLaw A μ) : IsCoercive (restrictedForm G A) := by
  refine ⟨μ, hμ, ?_⟩
  intro g
  simpa only [restrictedForm_apply, Submodule.norm_coe] using hA (g : H)

/-- The gradient correction, as a bounded linear function of the loading. -/
def correction (A : H →L[ℝ] H) (μ : ℝ) (hμ : 0 < μ)
    (hA : CoerciveLaw A μ) : H →L[ℝ] G :=
  (restrictedForm_coercive G hμ hA).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (G.orthogonalProjectionOnto.comp (-A))

/-- The full minimizing field, before choosing a space of constant loadings. -/
def cellField (A : H →L[ℝ] H) (μ : ℝ) (hμ : 0 < μ)
    (hA : CoerciveLaw A μ) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H + G.subtypeL.comp (correction G A μ hμ hA)

theorem correction_equation (A : H →L[ℝ] H) (μ : ℝ) (hμ : 0 < μ)
    (hA : CoerciveLaw A μ) (F : H) (g : G) :
    inner ℝ (A (correction G A μ hμ hA F : H)) (g : H) =
      -inner ℝ (A F) (g : H) := by
  let c := restrictedForm_coercive G hμ hA
  have h := c.continuousLinearEquivOfBilin_apply (correction G A μ hμ hA F) g
  have hinv : c.continuousLinearEquivOfBilin (correction G A μ hμ hA F) =
      G.orthogonalProjectionOnto (-(A F)) := by
    exact c.continuousLinearEquivOfBilin.apply_symm_apply _
  rw [hinv, restrictedForm_apply, inner_projection] at h
  simpa only [inner_neg_left] using h.symm

theorem cellField_isCellField (A : H →L[ℝ] H) (μ : ℝ) (hμ : 0 < μ)
    (hA : CoerciveLaw A μ) (F : H) :
    IsCellField G A F (cellField G A μ hμ hA F) := by
  constructor
  · change F + (correction G A μ hμ hA F : H) - F ∈ G
    simpa only [add_sub_cancel_left] using (correction G A μ hμ hA F).property
  · intro g hg
    change inner ℝ (A (F + (correction G A μ hμ hA F : H))) g = 0
    rw [map_add, inner_add_left, correction_equation G A μ hμ hA F ⟨g, hg⟩]
    ring

/-- Existence and uniqueness of the abstract cell field. -/
theorem existsUnique_cellField (A : H →L[ℝ] H) (μ : ℝ) (hμ : 0 < μ)
    (hA : CoerciveLaw A μ) (F : H) : ∃! e : H, IsCellField G A F e := by
  refine ⟨cellField G A μ hμ hA F, cellField_isCellField G A μ hμ hA F, ?_⟩
  intro e he
  exact cellField_unique hμ hA he (cellField_isCellField G A μ hμ hA F)

end Existence

end HierarchicalLaminates.Analysis
