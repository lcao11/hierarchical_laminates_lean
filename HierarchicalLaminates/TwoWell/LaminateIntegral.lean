module

public import HierarchicalLaminates.Composition.InterfaceBounds

/-!
# Integral estimates for laminate transition regions

Exact slab averages give the two bulk contributions. The remaining transition
bands have small measure and need only an upper bound on the integrand. The
estimate uses absolute endpoint values to accommodate signed minorants.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory Set Periodic Binary HierarchicalLaminates.Composition

private theorem integral_add_scalar (f g : Domain → ℝ)
    (hf : Integrable f domainMeasure) (hg : Integrable g domainMeasure) :
    (∫ q,f q+g q ∂domainMeasure) = (∫ q,f q ∂domainMeasure)+(∫ q,g q ∂domainMeasure) := by
  simpa only [Pi.add_apply] using integral_add hf hg

private theorem integral_sub_scalar (f g : Domain → ℝ)
    (hf : Integrable f domainMeasure) (hg : Integrable g domainMeasure) :
    (∫ q,f q-g q ∂domainMeasure) = (∫ q,f q ∂domainMeasure)-(∫ q,g q ∂domainMeasure) := by
  simpa only [Pi.sub_apply] using integral_sub hf hg

theorem slabIndicator_nonneg (a : ℝ) (q : Domain) : 0 ≤ slabIndicator a q := by
  unfold slabIndicator
  split_ifs <;> norm_num

theorem slabIndicator_le_one (a : ℝ) (q : Domain) : slabIndicator a q ≤ 1 := by
  unfold slabIndicator
  split_ifs <;> norm_num

theorem slabIndicator_mono {a b : ℝ} (hab : a ≤ b) (q : Domain) :
    slabIndicator a q ≤ slabIndicator b q := by
  unfold slabIndicator
  split_ifs <;> norm_num at *; linarith

theorem slabIndicator_integral_Icc {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    (∫ q,slabIndicator a q ∂domainMeasure) = a := by
  rcases eq_or_lt_of_le ha.1 with rfl | hpos
  · have he : slabIndicator 0 = fun _ : Domain => (0 : ℝ) := by
      funext q
      exact ite_eq_right (not_lt.mpr (coordinateRepresentative_mem 1 q).1)
    rw [he]
    simp
  · exact slabIndicator_integral ⟨hpos,ha.2⟩

def laminateBandDensity (a δ : ℝ) (q : Domain) : ℝ :=
  slabIndicator (2*δ) q + (slabIndicator (a+δ) q-slabIndicator (a-δ) q) +
    (1-slabIndicator (1-2*δ) q)

theorem laminateBandDensity_integrable (a δ : ℝ) :
    Integrable (laminateBandDensity a δ) domainMeasure :=
  ((slabIndicator_integrable (2*δ)).add
    ((slabIndicator_integrable (a+δ)).sub (slabIndicator_integrable (a-δ)))).add
      ((integrable_const 1).sub (slabIndicator_integrable (1-2*δ)))

theorem laminateBandDensity_nonneg {a δ : ℝ} (hδ : 0 ≤ δ) (q : Domain) :
    0 ≤ laminateBandDensity a δ q := by
  have hm := slabIndicator_mono (show a-δ ≤ a+δ by linarith) q
  have hn := slabIndicator_nonneg (2*δ) q
  have ho := slabIndicator_le_one (1-2*δ) q
  unfold laminateBandDensity
  linarith

theorem laminateBandDensity_integral {a δ : ℝ} (hδ : 0 < δ)
    (ha : 3*δ ≤ a) (ha1 : a+3*δ ≤ 1) :
    (∫ q,laminateBandDensity a δ q ∂domainMeasure) = 6*δ := by
  have hsum := integral_add ((slabIndicator_integrable (2*δ)).add
      ((slabIndicator_integrable (a+δ)).sub (slabIndicator_integrable (a-δ))))
      ((integrable_const 1).sub (slabIndicator_integrable (1-2*δ)))
  have hsum2 := integral_add (slabIndicator_integrable (2*δ))
      ((slabIndicator_integrable (a+δ)).sub (slabIndicator_integrable (a-δ)))
  have hsub := integral_sub (slabIndicator_integrable (a+δ)) (slabIndicator_integrable (a-δ))
  have hsub1 := integral_sub (integrable_const 1) (slabIndicator_integrable (1-2*δ))
  simp only [Pi.add_apply,Pi.sub_apply] at hsum hsum2 hsub hsub1
  unfold laminateBandDensity
  rw [hsum,hsum2,hsub,hsub1,
    slabIndicator_integral_Icc ⟨by linarith,by linarith⟩,
    slabIndicator_integral_Icc ⟨by linarith,by linarith⟩,
    slabIndicator_integral_Icc ⟨by linarith,by linarith⟩,
    slabIndicator_integral_Icc ⟨by linarith,by linarith⟩]
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul]
  ring

def laminateStep (a A B : ℝ) (q : Domain) : ℝ :=
  slabIndicator a q*A + (1-slabIndicator a q)*B

theorem laminateStep_integrable (a A B : ℝ) : Integrable (laminateStep a A B) domainMeasure :=
  ((slabIndicator_integrable a).mul_const A).add
    (((integrable_const 1).sub (slabIndicator_integrable a)).mul_const B)

theorem laminateStep_integral {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (A B : ℝ) :
    (∫ q,laminateStep a A B q ∂domainMeasure) = a*A+(1-a)*B := by
  have hadd := integral_add ((slabIndicator_integrable a).mul_const A)
      (((integrable_const 1).sub (slabIndicator_integrable a)).mul_const B)
  have hsub := integral_sub (integrable_const 1) (slabIndicator_integrable a)
  simp only [Pi.sub_apply] at hadd hsub
  unfold laminateStep
  rw [hadd,integral_mul_const,integral_mul_const,hsub,slabIndicator_integral_Icc ha]
  simp

theorem laminateStep_lower (a A B : ℝ) (q : Domain) :
    -(|A|+|B|) ≤ laminateStep a A B q := by
  unfold laminateStep slabIndicator
  split_ifs <;> simp only [one_mul,zero_mul,sub_self,sub_zero,add_zero,zero_add]
  · linarith [neg_abs_le A,abs_nonneg B]
  · linarith [neg_abs_le B,abs_nonneg A]

theorem laminateBandDensity_large_of_outside {a δ : ℝ} (hδ : 0 < δ)
    (ha : 3*δ ≤ a) (ha1 : a+3*δ ≤ 1) (q : Domain)
    (hA : ¬(2*δ ≤ coordinateRepresentative 1 q ∧ coordinateRepresentative 1 q ≤ a-δ))
    (hB : ¬(a+δ ≤ coordinateRepresentative 1 q ∧ coordinateRepresentative 1 q ≤ 1-2*δ)) :
    1 ≤ laminateBandDensity a δ q := by
  unfold laminateBandDensity slabIndicator
  push Not at hA hB
  split_ifs <;> simp_all <;> linarith

/-- Only upper control of the tested energy is used on transition bands. -/
theorem laminate_pointwise_upper {a δ M A B : ℝ} (hδ : 0 < δ)
    (ha : 3*δ ≤ a) (ha1 : a+3*δ ≤ 1) (hM : 0 ≤ M)
    (g : Domain → ℝ) (hg : ∀ q,g q ≤ M)
    (hA : ∀ q,2*δ ≤ coordinateRepresentative 1 q → coordinateRepresentative 1 q ≤ a-δ → g q = A)
    (hB : ∀ q,a+δ ≤ coordinateRepresentative 1 q → coordinateRepresentative 1 q ≤ 1-2*δ → g q = B)
    (q : Domain) :
    g q ≤ laminateStep a A B q + (M+|A|+|B|)*laminateBandDensity a δ q := by
  have hC : 0 ≤ M+|A|+|B| := by positivity
  have hE := laminateBandDensity_nonneg (a := a) hδ.le q
  by_cases hgoodA : 2*δ ≤ coordinateRepresentative 1 q ∧ coordinateRepresentative 1 q ≤ a-δ
  · rw [hA q hgoodA.1 hgoodA.2]
    have hy : coordinateRepresentative 1 q < a := by linarith [hgoodA.2]
    simp only [laminateStep,slabIndicator,ite_eq_left hy,one_mul,sub_self,zero_mul,add_zero]
    exact le_add_of_nonneg_right (mul_nonneg hC hE)
  · by_cases hgoodB : a+δ ≤ coordinateRepresentative 1 q ∧ coordinateRepresentative 1 q ≤ 1-2*δ
    · rw [hB q hgoodB.1 hgoodB.2]
      have hy : ¬coordinateRepresentative 1 q < a := by linarith [hgoodB.1]
      simp only [laminateStep,slabIndicator,ite_eq_right hy,zero_mul,sub_zero,one_mul,zero_add]
      exact le_add_of_nonneg_right (mul_nonneg hC hE)
    · have he := laminateBandDensity_large_of_outside hδ ha ha1 q hgoodA hgoodB
      have hs := laminateStep_lower a A B q
      have hm := mul_le_mul_of_nonneg_left he hC
      have hq := hg q
      nlinarith

theorem laminate_integral_upper {a δ M A B : ℝ} (hδ : 0 < δ)
    (ha : 3*δ ≤ a) (ha1 : a+3*δ ≤ 1) (hM : 0 ≤ M)
    (g : Domain → ℝ) (hgi : Integrable g domainMeasure) (hg : ∀ q,g q ≤ M)
    (hA : ∀ q,2*δ ≤ coordinateRepresentative 1 q → coordinateRepresentative 1 q ≤ a-δ → g q = A)
    (hB : ∀ q,a+δ ≤ coordinateRepresentative 1 q → coordinateRepresentative 1 q ≤ 1-2*δ → g q = B) :
    (∫ q,g q ∂domainMeasure) ≤ a*A+(1-a)*B+6*δ*(M+|A|+|B|) := by
  have hi := integral_mono_ae hgi
    ((laminateStep_integrable a A B).add
      ((laminateBandDensity_integrable a δ).const_mul (M+|A|+|B|)))
    (Filter.Eventually.of_forall (laminate_pointwise_upper hδ ha ha1 hM g hg hA hB))
  simp only [Pi.add_apply] at hi
  rw [integral_add_scalar _ _ (laminateStep_integrable a A B)
      ((laminateBandDensity_integrable a δ).const_mul (M+|A|+|B|)),
    laminateStep_integral ⟨by linarith,by linarith⟩ A B,integral_const_mul,
    laminateBandDensity_integral hδ ha ha1] at hi
  nlinarith

end HierarchicalLaminates.TwoWell
