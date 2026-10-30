module

public import HierarchicalLaminates.GClosure.TwoChildGeometry
public import HierarchicalLaminates.GClosure.ObliqueSlabNorm

/-!
# Localized fields and residual transport in the complementary oblique slab
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open MeasureTheory Set HierarchicalLaminates.Periodic HierarchicalLaminates.Binary HierarchicalLaminates.Composition

def complementaryLocalizedPotential (R : TorusCoordinates) (a : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) {δ : ℝ} (hδ : 0 < δ) {r : ℕ} (hr : 0 < r)
    (k : ℕ) (u : RegularPotential) : RegularPotential :=
  transformPotential R.matrix (translatePotential a
    (localizedPotential (by linarith : 0 < 1-a) (by linarith : 1-a ≤ 1)
      hδ hr k (transformPotential R.inverse u)))

def complementarySlabField (R : TorusCoordinates) (a : ℝ) (r k : ℕ)
    (u : RegularPotential) : PhysicalField :=
  R.gradientPullback (translateField a ((transformPotential R.inverse u).slabField (1-a) r k))

theorem translateField_sub_eq (a : ℝ) (f g : PhysicalField) :
    translateField a (f-g) = translateField a f - translateField a g :=
  map_sub (Lp.compMeasurePreserving (shiftVertical a) (shiftVertical_measurePreserving a)) f g

theorem complementaryLocalization_error_bound (R : TorusCoordinates) (a : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) {δ : ℝ} (hδ : 0 < δ) {r : ℕ} (hr : 0 < r)
    (k : ℕ) (u : RegularPotential) :
    ‖(complementaryLocalizedPotential R a ha₀ ha₁ hδ hr k u).field -
        complementarySlabField R a r k u‖ ≤
      ‖spatialGradientMap R.matrix‖ *
        ‖(localizedPotential (by linarith : 0 < 1-a) (by linarith : 1-a ≤ 1)
          hδ hr k (transformPotential R.inverse u)).field -
          (transformPotential R.inverse u).slabField (1-a) r k‖ := by
  unfold complementaryLocalizedPotential complementarySlabField
  rw [← R.gradientPullback_regular,translatePotential_field,← map_sub,← translateField_sub_eq]
  exact (R.gradientPullback_norm_le _).trans_eq (by rw [translateField_norm])

theorem complementarySlabField_coe (R : TorusCoordinates) (a : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) (r k : ℕ) (u : RegularPotential) :
    complementarySlabField R a r k u =ᵐ[domainMeasure] fun q =>
      if a ≤ coordinateRepresentative 1 (R.equiv q) then
        u.gradient (obliqueComplementCoordinates R a r k q) else 0 := by
  filter_upwards [R.gradientPullback_coe
      (translateField a ((transformPotential R.inverse u).slabField (1-a) r k)),
    R.measurePreserving.quasiMeasurePreserving.ae
      (translateField_coe a ((transformPotential R.inverse u).slabField (1-a) r k)),
    R.measurePreserving.quasiMeasurePreserving.ae
      ((shiftVertical_measurePreserving a).quasiMeasurePreserving.ae
        ((transformPotential R.inverse u).slabField_coe (1-a) r k))] with q hp ht hs
  change R.gradientPullback (translateField a
    ((transformPotential R.inverse u).slabField (1-a) r k)) q = _
  rw [hp,ht,hs]
  unfold slabPhysicalValue
  simp only [shiftVertical_slab_iff ha₀ ha₁]
  split_ifs
  · rw [transformPotential_gradient,spatialGradientMap_inverse]
    rfl
  · exact map_zero _

def complementarySlabPhysicalField (R : TorusCoordinates) (a : ℝ) (r k : ℕ)
    (f : Domain → PhysicalGradient) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q, ‖f q‖ ≤ C) : PhysicalField :=
  R.pullbackField (translateField a (slabPhysicalField (1-a) r k (fun q => f (R.symm.equiv q))
    (hf.comp R.symm.continuous.measurable) C hC (fun q => hb (R.symm.equiv q))))

theorem complementarySlabPhysicalField_coe (R : TorusCoordinates) (a : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) (r k : ℕ)
    (f : Domain → PhysicalGradient) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q, ‖f q‖ ≤ C) :
    complementarySlabPhysicalField R a r k f hf C hC hb =ᵐ[domainMeasure] fun q =>
      if a ≤ coordinateRepresentative 1 (R.equiv q) then
        f (obliqueComplementCoordinates R a r k q) else 0 := by
  let S := slabPhysicalField (1-a) r k (fun q => f (R.symm.equiv q))
    (hf.comp R.symm.continuous.measurable) C hC (fun q => hb (R.symm.equiv q))
  filter_upwards [R.pullbackField_coe (translateField a S),
    R.measurePreserving.quasiMeasurePreserving.ae (translateField_coe a S),
    R.measurePreserving.quasiMeasurePreserving.ae
      ((shiftVertical_measurePreserving a).quasiMeasurePreserving.ae
        (slabPhysicalField_coe (1-a) r k (fun q => f (R.symm.equiv q))
          (hf.comp R.symm.continuous.measurable) C hC (fun q => hb (R.symm.equiv q))))]
      with q hp ht hs
  change R.pullbackField (translateField a S) q = _
  rw [hp,ht,hs]
  unfold slabPhysicalValue
  simp only [shiftVertical_slab_iff ha₀ ha₁]
  split_ifs <;> rfl

theorem complementarySlabPhysicalField_norm_le (R : TorusCoordinates) (a : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (f : Domain → PhysicalGradient) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q, ‖f q‖ ≤ C) :
    ‖complementarySlabPhysicalField R a r k f hf C hC hb‖ ≤ ‖boundedPhysicalField f hf C hb‖ := by
  unfold complementarySlabPhysicalField
  rw [R.pullbackField_norm,translateField_norm]
  have h := slabPhysicalField_norm_le (a := 1-a) ⟨by linarith,by linarith⟩ hr hk
    (fun q => f (R.symm.equiv q)) (hf.comp R.symm.continuous.measurable) C hC
      (fun q => hb (R.symm.equiv q))
  rw [← R.symm.pullback_boundedPhysicalField,R.symm.pullbackField_norm] at h
  exact h

theorem exists_common_complementary_localization {I : Type*} [Fintype I]
    (R : TorusCoordinates) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (u ψ : I → RegularPotential) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ r : ℕ, ∃ hr : 0 < r, ∃ k : ℕ, 0 < k ∧
      ∀ j : I,
        ‖(complementaryLocalizedPotential R a ha₀ ha₁ hδ hr k (u j)).field -
          complementarySlabField R a r k (u j)‖ +
        ‖(complementaryLocalizedPotential R a ha₀ ha₁ hδ hr k (ψ j)).field -
          complementarySlabField R a r k (ψ j)‖ < ε := by
  let M := ‖spatialGradientMap R.matrix‖
  have hM : 0 ≤ M := norm_nonneg _
  obtain ⟨δ,hδ,r,hr,k,hk,hlocal⟩ := exists_common_localization (1-a)
    (by linarith : 0 < 1-a) (by linarith : 1-a ≤ 1)
    (fun j => transformPotential R.inverse (u j))
    (fun j => transformPotential R.inverse (ψ j)) (ε / (M+1)) (by positivity)
  refine ⟨δ,hδ,r,hr,k,hk,?_⟩
  intro j
  have h₁ := complementaryLocalization_error_bound R a ha₀ ha₁ hδ hr k (u j)
  have h₂ := complementaryLocalization_error_bound R a ha₀ ha₁ hδ hr k (ψ j)
  have he := hlocal j
  have hsum : 0 ≤
      ‖(localizedPotential (by linarith : 0 < 1-a) (by linarith : 1-a ≤ 1)
        hδ hr k (transformPotential R.inverse (u j))).field -
        (transformPotential R.inverse (u j)).slabField (1-a) r k‖ +
      ‖(localizedPotential (by linarith : 0 < 1-a) (by linarith : 1-a ≤ 1)
        hδ hr k (transformPotential R.inverse (ψ j))).field -
        (transformPotential R.inverse (ψ j)).slabField (1-a) r k‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hscaled := mul_lt_mul_of_pos_left he (by positivity : 0 < M+1)
  have hcancel : (M+1) * (ε/(M+1)) = ε := by field_simp
  rw [hcancel] at hscaled
  dsimp [M] at *
  nlinarith

end HierarchicalLaminates.GClosure
