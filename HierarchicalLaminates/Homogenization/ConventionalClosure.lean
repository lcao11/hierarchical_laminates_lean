module

public import HierarchicalLaminates.PaperCounterexample

/-!
# G-closure at an exact constituent fraction

Each fraction slice contains effective tensors of periodic two-phase
coefficients with that exact fraction, and its tensor closure defines the
corresponding G-closure.
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Homogenization

open MeasureTheory HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination

def IsBinary (b : PhaseFraction) : Prop := ∀ q, b.value q = 0 ∨ b.value q = 1

def phaseMean (b : PhaseFraction) : ℝ := ∫ q, b.value q ∂domainMeasure

def periodicBinaryTensors (θ : ℝ) : Set (Tensor (Fin 16)) :=
  {B | ∃ b : PhaseFraction, IsBinary b ∧ phaseMean b = θ ∧ effectiveMatrix b = B}

def GClosure (θ : ℝ) : Set (Tensor (Fin 16)) := closure (periodicBinaryTensors θ)

theorem effectiveMatrix_mem_GClosure {b : PhaseFraction} (hb : IsBinary b) :
    effectiveMatrix b ∈ GClosure (phaseMean b) := by
  exact subset_closure ⟨b, hb, rfl, rfl⟩

theorem positive_binary_of_mem_GClosure {θ : ℝ} {B : Tensor (Fin 16)}
    (hB : B ∈ GClosure θ) (hpositive : 0 < loadingDifference xiFlat etaFlat B) :
    ∃ b : PhaseFraction, IsBinary b ∧ phaseMean b = θ ∧
      0 < physicalLoadingDifference b ∧
      effectiveMatrix b ∉ closure (allFiniteLaminates phaseZero (phaseOne rho)) := by
  have hcont := loadingDifference_continuous xiFlat etaFlat
  have hopen : IsOpen {C : Tensor (Fin 16) | 0 < loadingDifference xiFlat etaFlat C} :=
    isOpen_lt continuous_const hcont
  obtain ⟨C, hCpos, hC⟩ := mem_closure_iff_nhds.mp hB
    {C : Tensor (Fin 16) | 0 < loadingDifference xiFlat etaFlat C}
    (hopen.mem_nhds hpositive)
  rcases hC with ⟨b, hb, hmean, rfl⟩
  exact ⟨b, hb, hmean, hCpos,
    positive_loading_difference_not_in_laminateClosure rho_pos.le rho_lt_two_thirds hCpos⟩

/-- The G-closure composition property with weighted phase fractions. -/
def ExactFractionComposition : Prop :=
  ∀ (θ₁ θ₂ : ℝ), θ₁ ∈ Set.Icc (0 : ℝ) 1 → θ₂ ∈ Set.Icc (0 : ℝ) 1 →
    ∀ (B₁ B₂ : Tensor (Fin 16)), B₁ ∈ GClosure θ₁ → B₂ ∈ GClosure θ₂ →
      ∀ (n : LayerNormal) (weight : LayerProportion) (C : Tensor (Fin 16)),
        IsLayerTensor B₁ B₂ n weight C →
          C ∈ GClosure ((weight : ℝ) * θ₁ + (1 - (weight : ℝ)) * θ₂)

end HierarchicalLaminates.Homogenization
