module

public import HierarchicalLaminates.GClosure.ObliqueFields

/-! Localized microscopic potentials in arbitrary periodic layer coordinates. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open HierarchicalLaminates.Periodic HierarchicalLaminates.Composition

def obliqueLocalizedPotential (R : TorusCoordinates) {a δ : ℝ}
    (ha₀ : 0 < a) (ha : a ≤ 1) (hδ : 0 < δ) {r : ℕ} (hr : 0 < r)
    (k : ℕ) (u : RegularPotential) : RegularPotential :=
  transformPotential R.matrix
    (localizedPotential ha₀ ha hδ hr k (transformPotential R.inverse u))

def obliqueSlabField (R : TorusCoordinates) (a : ℝ) (r k : ℕ)
    (u : RegularPotential) : PhysicalField :=
  R.gradientPullback ((transformPotential R.inverse u).slabField a r k)

theorem obliqueLocalization_error_bound (R : TorusCoordinates) {a δ : ℝ}
    (ha₀ : 0 < a) (ha : a ≤ 1) (hδ : 0 < δ) {r : ℕ} (hr : 0 < r)
    (k : ℕ) (u : RegularPotential) :
    ‖(obliqueLocalizedPotential R ha₀ ha hδ hr k u).field - obliqueSlabField R a r k u‖ ≤
      ‖spatialGradientMap R.matrix‖ *
        ‖(localizedPotential ha₀ ha hδ hr k (transformPotential R.inverse u)).field -
          (transformPotential R.inverse u).slabField a r k‖ := by
  unfold obliqueLocalizedPotential obliqueSlabField
  rw [← R.gradientPullback_regular, ← map_sub]
  exact R.gradientPullback_norm_le _

theorem exists_common_oblique_localization {I : Type*} [Fintype I]
    (R : TorusCoordinates) (a : ℝ) (ha₀ : 0 < a) (ha : a ≤ 1)
    (u ψ : I → RegularPotential) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ r : ℕ, ∃ hr : 0 < r, ∃ k : ℕ, 0 < k ∧
      ∀ j : I,
        ‖(obliqueLocalizedPotential R ha₀ ha hδ hr k (u j)).field -
          obliqueSlabField R a r k (u j)‖ +
        ‖(obliqueLocalizedPotential R ha₀ ha hδ hr k (ψ j)).field -
          obliqueSlabField R a r k (ψ j)‖ < ε := by
  let M := ‖spatialGradientMap R.matrix‖
  have hM : 0 ≤ M := norm_nonneg _
  obtain ⟨δ,hδ,r,hr,k,hk,hlocal⟩ := exists_common_localization a ha₀ ha
    (fun j => transformPotential R.inverse (u j))
    (fun j => transformPotential R.inverse (ψ j)) (ε / (M+1)) (by positivity)
  refine ⟨δ,hδ,r,hr,k,hk,?_⟩
  intro j
  have h₁ := obliqueLocalization_error_bound R ha₀ ha hδ hr k (u j)
  have h₂ := obliqueLocalization_error_bound R ha₀ ha hδ hr k (ψ j)
  have he := hlocal j
  have hsum : 0 ≤
      ‖(localizedPotential ha₀ ha hδ hr k (transformPotential R.inverse (u j))).field -
        (transformPotential R.inverse (u j)).slabField a r k‖ +
      ‖(localizedPotential ha₀ ha hδ hr k (transformPotential R.inverse (ψ j))).field -
        (transformPotential R.inverse (ψ j)).slabField a r k‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hscaled := mul_lt_mul_of_pos_left he (by positivity : 0 < M+1)
  have hcancel : (M+1) * (ε/(M+1)) = ε := by field_simp
  rw [hcancel] at hscaled
  dsimp [M] at *
  nlinarith

end HierarchicalLaminates.GClosure
