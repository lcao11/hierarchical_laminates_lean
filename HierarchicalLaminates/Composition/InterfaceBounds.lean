module

public import HierarchicalLaminates.Composition.MacroPrimitive

/-!
# L² bounds from the measure of the two interface bands
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open MeasureTheory Set HierarchicalLaminates.Homogenization HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Binary

theorem slabIndicator_abs_le (a : ℝ) (q : Domain) : |slabIndicator a q| ≤ 1 := by
  unfold slabIndicator
  split_ifs <;> norm_num

theorem slabIndicator_integrable (a : ℝ) : Integrable (slabIndicator a) domainMeasure :=
  Integrable.of_bound (slabIndicator_measurable a).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun q => by
      simpa only [Real.norm_eq_abs] using slabIndicator_abs_le a q)

theorem slabIndicator_integral {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    (∫ q, slabIndicator a q ∂domainMeasure) = a := by
  have h := slabValue_integral ha (by norm_num : 0 < (1 : ℕ))
    (by norm_num : 0 < (1 : ℕ)) (fun _ => (1 : ℝ)) measurable_const
    (by norm_num : (0 : ℝ) ≤ 1) (fun _ => by norm_num)
  simpa only [slabValue,slabIndicator,integral_const,Measure.real,measure_univ,
    ENNReal.toReal_one,smul_eq_mul,mul_one] using h

def bandDensity (a w : ℝ) (q : Domain) : ℝ :=
  slabIndicator w q + slabIndicator a q - slabIndicator (a-w) q

theorem bandDensity_integrable (a w : ℝ) : Integrable (bandDensity a w) domainMeasure :=
  ((slabIndicator_integrable w).add (slabIndicator_integrable a)).sub
    (slabIndicator_integrable (a-w))

theorem bandDensity_integral {a w : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1)
    (hw : 0 < w) (hwa : w < a / 2) :
    (∫ q, bandDensity a w q ∂domainMeasure) = 2*w := by
  calc
    _ = ∫ q, (slabIndicator w q + slabIndicator a q) - slabIndicator (a-w) q
        ∂domainMeasure := rfl
    _ = (∫ q, slabIndicator w q + slabIndicator a q ∂domainMeasure) -
        ∫ q, slabIndicator (a-w) q ∂domainMeasure :=
      integral_sub ((slabIndicator_integrable w).add (slabIndicator_integrable a))
        (slabIndicator_integrable (a-w))
    _ = 2*w := by
      rw [integral_add (slabIndicator_integrable w) (slabIndicator_integrable a),
        slabIndicator_integral ⟨hw,by linarith [ha.2]⟩,
        slabIndicator_integral ha,slabIndicator_integral ⟨by linarith,by linarith [ha.2]⟩]
      ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem field_norm_sq_integral (v : Periodic.Field E) :
    ‖v‖ ^ 2 = ∫ q, ‖v q‖ ^ 2 ∂domainMeasure := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- An L² field with a uniform bound and support in two bands of width `w` has small norm. -/
theorem interface_norm_sq_le {a w C : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1)
    (hw : 0 < w) (hwa : w < a / 2) (_hC : 0 ≤ C) (v : Periodic.Field E)
    (hv : ∀ᵐ q ∂domainMeasure, ‖v q‖ ≤ C)
    (hcenter : ∀ᵐ q ∂domainMeasure,
      w ≤ coordinateRepresentative 1 q → coordinateRepresentative 1 q < a-w → v q = 0)
    (houtside : ∀ᵐ q ∂domainMeasure, a ≤ coordinateRepresentative 1 q → v q = 0) :
    ‖v‖ ^ 2 ≤ 2*w*C^2 := by
  have hvint : Integrable (fun q => ‖v q‖ ^ 2) domainMeasure := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) v v
  have hle : (∫ q, ‖v q‖ ^ 2 ∂domainMeasure) ≤
      ∫ q, C^2 * bandDensity a w q ∂domainMeasure := by
    apply integral_mono_ae hvint ((bandDensity_integrable a w).const_mul (C^2))
    filter_upwards [hv,hcenter,houtside] with q hvq hc ho
    have hbound : ‖v q‖ ^ 2 ≤ C^2 := pow_le_pow_left₀ (norm_nonneg _) hvq 2
    by_cases hlow : coordinateRepresentative 1 q < w
    · have hm : coordinateRepresentative 1 q < a-w := by linarith
      have ha' : coordinateRepresentative 1 q < a := by linarith
      simpa only [bandDensity,slabIndicator,ite_eq_left hlow,ite_eq_left hm,ite_eq_left ha',
        add_sub_cancel_right,mul_one] using hbound
    · by_cases hmid : coordinateRepresentative 1 q < a-w
      · have ha' : coordinateRepresentative 1 q < a := by linarith
        rw [hc (le_of_not_gt hlow) hmid]
        simp only [norm_zero,zero_pow (by norm_num : 2 ≠ 0),bandDensity,slabIndicator,
          ite_eq_right hlow,ite_eq_left hmid,ite_eq_left ha']
        norm_num
      · by_cases hupp : coordinateRepresentative 1 q < a
        · simpa only [bandDensity,slabIndicator,ite_eq_right hlow,ite_eq_right hmid,
            ite_eq_left hupp,zero_add,sub_zero,mul_one] using hbound
        · rw [ho (le_of_not_gt hupp)]
          simp only [norm_zero,zero_pow (by norm_num : 2 ≠ 0),bandDensity,slabIndicator,
            ite_eq_right hlow,ite_eq_right hmid,ite_eq_right hupp]
          norm_num
  rw [field_norm_sq_integral]
  calc
    _ ≤ ∫ q, C^2 * bandDensity a w q ∂domainMeasure := hle
    _ = 2*w*C^2 := by rw [integral_const_mul,bandDensity_integral ha hw hwa]; ring

theorem interface_norm_le {a w C : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1)
    (hw : 0 < w) (hwa : w < a / 2) (hC : 0 ≤ C) (v : Periodic.Field E)
    (hv : ∀ᵐ q ∂domainMeasure, ‖v q‖ ≤ C)
    (hcenter : ∀ᵐ q ∂domainMeasure,
      w ≤ coordinateRepresentative 1 q → coordinateRepresentative 1 q < a-w → v q = 0)
    (houtside : ∀ᵐ q ∂domainMeasure, a ≤ coordinateRepresentative 1 q → v q = 0) :
    ‖v‖ ≤ C * Real.sqrt (2*w) := by
  have hs := interface_norm_sq_le ha hw hwa hC v hv hcenter houtside
  have ht : (C * Real.sqrt (2*w))^2 = 2*w*C^2 := by
    rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*w)]
    ring
  nlinarith [norm_nonneg v,mul_nonneg hC (Real.sqrt_nonneg (2*w))]

end HierarchicalLaminates.Composition
