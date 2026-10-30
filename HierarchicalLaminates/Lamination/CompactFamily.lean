module

public import HierarchicalLaminates.Lamination.PhysicalLamination
public import HierarchicalLaminates.Lamination.MaterialEmbedding
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-!
# Compact parameter families and the full laminate closure

The order interval `0 ≤ H ≤ r I` in the finite-dimensional parameter space is
closed and bounded, hence compact, for every real `r`. Its image under the
affine material map is the compact family `materialFamily r`.

For `0 ≤ r < 2/3`, the family contains both constituents and is stable under
lamination. Consequently it contains every finite laminate and the closure of
all finite laminates, with arbitrary directions, weights and finite depths.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Lamination

open Matrix

/-- The parameter-space order interval `0 ≤ H ≤ r I`. -/
def parameterIntervalAt (r : ℝ) : Set RMatrix8 :=
  {H | H ∈ parameterSpace ∧ H.PosSemidef ∧ (r • (1 : RMatrix8) - H).PosSemidef}

theorem parameterIntervalAt_isClosed (r : ℝ) : IsClosed (parameterIntervalAt r) := by
  change IsClosed ((parameterSpace : Set RMatrix8) ∩
    ({H : RMatrix8 | H.PosSemidef} ∩
    {H : RMatrix8 | (r • (1 : RMatrix8) - H).PosSemidef}))
  exact parameterSpace.closed_of_finiteDimensional.inter
    (Matrix.posSemidef_is_closed.inter
      (Matrix.posSemidef_is_closed.preimage (by fun_prop)))

/-- The semidefinite bounds control every matrix entry by `r`. -/
theorem parameterIntervalAt_entry_bound {r : ℝ} {H : RMatrix8}
    (hH : H ∈ parameterIntervalAt r) (i j : Fin 8) : |H i j| ≤ r := by
  have hdiag (k : Fin 8) : H k k ≤ r := by
    have h := hH.2.2.diag_nonneg (i := k)
    simpa using h
  have hnon (k : Fin 8) : 0 ≤ H k k := hH.2.1.diag_nonneg
  by_cases hij : i = j
  · subst j
    rw [abs_of_nonneg (hnon i)]
    exact hdiag i
  · have hsym : H j i = H i j := hH.2.1.isHermitian.apply i j
    have hp := hH.2.1.dotProduct_mulVec_nonneg
      (Pi.single i (1 : ℝ) + Pi.single j 1)
    have hm := hH.2.1.dotProduct_mulVec_nonneg
      (Pi.single i (1 : ℝ) - Pi.single j 1)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_sub,
      dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct] at hp hm
    simp [hsym] at hp hm
    exact abs_le.mpr ⟨by linarith [hdiag i, hdiag j], by linarith [hdiag i, hdiag j]⟩

/-- The parameter interval is compact for every real upper-bound parameter. -/
theorem parameterIntervalAt_isCompact (r : ℝ) : IsCompact (parameterIntervalAt r) := by
  apply (isCompact_Icc (a := -r) (b := r)).matrix.of_isClosed_subset
    (parameterIntervalAt_isClosed r)
  intro H hH i j
  exact abs_le.mp (parameterIntervalAt_entry_bound hH i j)

/-- The material tensor depends affinely, and therefore continuously, on its parameter. -/
theorem materialTensor_continuous : Continuous materialTensor := by
  have heq : materialTensor = fun H : RMatrix8 =>
      phaseZero - reducedLiftMatrix * H * reducedLiftMatrixᵀ := by
    funext H
    exact materialTensor_affine H
  rw [heq]
  fun_prop

theorem materialFamily_eq_parameterInterval_image (r : ℝ) :
    materialFamily r = materialTensor '' parameterIntervalAt r := by
  ext A
  constructor
  · rintro ⟨H, hp, hl, hu, rfl⟩
    exact ⟨H, ⟨hp, hl, hu⟩, rfl⟩
  · rintro ⟨H, ⟨hp, hl, hu⟩, rfl⟩
    exact ⟨H, hp, hl, hu, rfl⟩

/-- The material family is the compact image of the parameter interval. -/
theorem materialFamily_isCompact_at (r : ℝ) : IsCompact (materialFamily r) := by
  rw [materialFamily_eq_parameterInterval_image]
  exact (parameterIntervalAt_isCompact r).image materialTensor_continuous

/-- In the coercive contrast range, the material family contains the closure
of all finite laminates, allowing arbitrary overall phase fractions. -/
theorem laminateClosure_mem_materialFamily {r : ℝ} (hr : 0 ≤ r) (hrlt : r < 2 / 3)
    {C : Tensor (Fin 16)} (hC : C ∈ closure (allFiniteLaminates phaseZero (phaseOne r))) :
    C ∈ materialFamily r := by
  have hsubset : allFiniteLaminates phaseZero (phaseOne r) ⊆ materialFamily r := by
    intro A hA
    exact finiteLaminate_mem_of_stable (phaseZero_mem_materialFamily hr)
      (phaseOne_mem_materialFamily hr)
      (fun n weight h₁ h₂ hlayer => materialFamily_stable hr hrlt h₁ h₂ n weight hlayer) hA
  exact closure_minimal hsubset (materialFamily_isCompact_at r).isClosed hC

end HierarchicalLaminates.Lamination
