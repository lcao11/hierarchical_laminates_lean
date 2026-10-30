module

public import HierarchicalLaminates.Corrector.Source
public import HierarchicalLaminates.Corrector.WeakProduct
public import HierarchicalLaminates.Binary.SampledProfileEstimate

/-!
# Constitutive difference for the binary residual estimate
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open Matrix MeasureTheory HierarchicalLaminates.Fourier HierarchicalLaminates.Periodic
  HierarchicalLaminates.Lamination HierarchicalLaminates.Material

theorem constitutive_difference_pointwise (b : PhaseFraction) (z : PotentialVector)
    (q : PeriodicDomain) (i : Fin 2) (a : Fin 16) :
    (coefficientOperator smoothFraction q (totalContinuous z q) -
      coefficientOperator b q (totalContinuous z q)) (i, a) =
      if i = 0 then HierarchicalLaminates.rho * (b.value q - cosineProfile q) * sourceComponent z a q
      else 0 := by
  rw [coefficientOperator_eq_matrix, coefficientOperator_eq_matrix,
    mixtureTensor_material, mixtureTensor_material]
  change (materialTensor ((HierarchicalLaminates.rho * cosineProfile q) • (1 : HierarchicalLaminates.RMatrix8)) *ᵥ
      (totalContinuous z q : PhysicalIndex → ℝ)) (i, a) -
    (materialTensor ((HierarchicalLaminates.rho * b.value q) • (1 : HierarchicalLaminates.RMatrix8)) *ᵥ
      (totalContinuous z q : PhysicalIndex → ℝ)) (i, a) = _
  rw [materialTensor_mulVec_rows, materialTensor_mulVec_rows]
  fin_cases i
  · norm_num
    simp only [horizontalR, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [sourceComponent_physical]
    ring
  · norm_num

theorem constitutive_difference_component_ae (b : PhaseFraction) (z : PotentialVector)
    (i : Fin 2) (a : Fin 16) :
    componentField i a
      (coefficientLaw smoothFraction (continuousField (totalContinuous z)) -
        coefficientLaw b (continuousField (totalContinuous z))) =ᵐ[domainMeasure]
      fun q => if i = 0 then
        HierarchicalLaminates.rho * (b.value q - cosineProfile q) * sourceComponent z a q else 0 := by
  filter_upwards
    [(EuclideanSpace.proj (𝕜 := ℝ) (i, a)).coeFn_compLpL
      (coefficientLaw smoothFraction (continuousField (totalContinuous z)) -
        coefficientLaw b (continuousField (totalContinuous z))),
      Lp.coeFn_sub (coefficientLaw smoothFraction (continuousField (totalContinuous z)))
        (coefficientLaw b (continuousField (totalContinuous z))),
      coefficientLaw_coe smoothFraction (continuousField (totalContinuous z)),
      coefficientLaw_coe b (continuousField (totalContinuous z)),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) domainMeasure (totalContinuous z)]
      with q hcomp hsub hs hb htotal
  change componentField i a _ q = _ at hcomp
  change continuousField (totalContinuous z) q = totalContinuous z q at htotal
  rw [hcomp, hsub]
  simp only [Pi.sub_apply]
  rw [hs, hb, htotal]
  exact constitutive_difference_pointwise b z q i a

theorem constitutive_binary_horizontal (N : ℕ) (hN : 0 < N)
    (z : PotentialVector) (a : Fin 16) :
    componentField 0 a
      (coefficientLaw smoothFraction (continuousField (totalContinuous z)) -
        coefficientLaw (binaryFraction N) (continuousField (totalContinuous z))) =
      HierarchicalLaminates.rho • continuousProduct (sourceComponent z a)
        (Binary.binaryVerticalDerivativeField N + Binary.sampledProfileErrorField N hN) := by
  apply Lp.ext
  filter_upwards
    [constitutive_difference_component_ae (binaryFraction N) z 0 a,
      Lp.coeFn_smul HierarchicalLaminates.rho (continuousProduct (sourceComponent z a)
        (Binary.binaryVerticalDerivativeField N + Binary.sampledProfileErrorField N hN)),
      continuousProduct_coe (sourceComponent z a)
        (Binary.binaryVerticalDerivativeField N + Binary.sampledProfileErrorField N hN),
      Lp.coeFn_add (Binary.binaryVerticalDerivativeField N) (Binary.sampledProfileErrorField N hN),
      MemLp.coeFn_toLp (Binary.binaryVerticalDerivative_memLp N),
      MemLp.coeFn_toLp (Binary.sampledProfileError_memLp hN)]
      with q hleft hsmul hprod hadd hvertical herror
  rw [hleft, hsmul]
  simp only [↓reduceIte, Pi.smul_apply, smul_eq_mul]
  rw [hprod, hadd]
  simp only [Pi.add_apply]
  change Binary.binaryVerticalDerivativeField N q = Binary.binaryVerticalDerivative N q at hvertical
  change Binary.sampledProfileErrorField N hN q = Binary.sampledProfileError N q at herror
  rw [hvertical, herror]
  simp only [binaryFraction, Binary.binaryVerticalDerivative, Binary.sampledProfileError]
  ring

theorem constitutive_binary_vertical (N : ℕ) (z : PotentialVector) (a : Fin 16) :
    componentField 1 a
      (coefficientLaw smoothFraction (continuousField (totalContinuous z)) -
        coefficientLaw (binaryFraction N) (continuousField (totalContinuous z))) = 0 := by
  apply Lp.ext
  filter_upwards [constitutive_difference_component_ae (binaryFraction N) z 1 a,
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := domainMeasure)] with q hleft hzero
  rw [hleft, hzero]
  norm_num

theorem binary_constitutive_difference_zero (N : ℕ) (hN : 0 < N)
    (z : PotentialVector) (a : Fin 16) :
    componentField 0 a
      (coefficientLaw smoothFraction (continuousField (totalContinuous z)) -
        coefficientLaw (binaryFraction N) (continuousField (totalContinuous z))) =
      HierarchicalLaminates.rho • continuousProduct (sourceComponent z a)
        (Binary.binaryVerticalDerivativeField N + Binary.sampledProfileErrorField N hN) :=
  constitutive_binary_horizontal N hN z a

theorem binary_constitutive_difference_one (N : ℕ) (_hN : 0 < N)
    (z : PotentialVector) (a : Fin 16) :
    componentField 1 a
      (coefficientLaw smoothFraction (continuousField (totalContinuous z)) -
        coefficientLaw (binaryFraction N) (continuousField (totalContinuous z))) = 0 :=
  constitutive_binary_vertical N z a

end HierarchicalLaminates.Corrector
