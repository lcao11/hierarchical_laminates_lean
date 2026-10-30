module

public import HierarchicalLaminates.Algebra.MaterialData
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The loading functional on four-factor products

For four elements of the five-dimensional parameter space, the loading
functional is a scalar polynomial. This formula simplifies the fifth-order
coefficient calculation.
-/

@[expose] public section

namespace HierarchicalLaminates

def cliffordBasisQ : Fin 5 → QMatrix 8 8 :=
  ![1, gammaQ 0, gammaQ 1, gammaQ 2, gammaQ 3]

def spinCombinationQ (a : Fin 5 → ℚ) : QMatrix 8 8 :=
  ∑ i : Fin 5, a i • cliffordBasisQ i

/-- Expansion of the four-by-four determinant along its first row. -/
def quarticDetQ (a b c d : Fin 4 → ℚ) : ℚ :=
  a 0 * (b 1 * (c 2 * d 3 - c 3 * d 2) - b 2 * (c 1 * d 3 - c 3 * d 1) +
    b 3 * (c 1 * d 2 - c 2 * d 1)) -
  a 1 * (b 0 * (c 2 * d 3 - c 3 * d 2) - b 2 * (c 0 * d 3 - c 3 * d 0) +
    b 3 * (c 0 * d 2 - c 2 * d 0)) +
  a 2 * (b 0 * (c 1 * d 3 - c 3 * d 1) - b 1 * (c 0 * d 3 - c 3 * d 0) +
    b 3 * (c 0 * d 1 - c 1 * d 0)) -
  a 3 * (b 0 * (c 1 * d 2 - c 2 * d 1) - b 1 * (c 0 * d 2 - c 2 * d 0) +
    b 2 * (c 0 * d 1 - c 1 * d 0))

def generatorRowQ (i : Fin 5) : Fin 4 → ℚ :=
  fun j => if i.val = j.val + 1 then 1 else 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem difference_basis_four : ∀ i j k l : Fin 5,
    reducedDifferenceQ (cliffordBasisQ i * cliffordBasisQ j *
      cliffordBasisQ k * cliffordBasisQ l) =
      2 * quarticDetQ (generatorRowQ i) (generatorRowQ j)
        (generatorRowQ k) (generatorRowQ l) := by
  decide +kernel

theorem reducedDifferenceQ_sum {ι : Type*} (s : Finset ι) (f : ι → QMatrix 8 8) :
    reducedDifferenceQ (∑ i ∈ s, f i) = ∑ i ∈ s, reducedDifferenceQ (f i) := by
  simp [reducedDifferenceQ, Matrix.sum_apply, Finset.sum_sub_distrib]

theorem reducedDifferenceQ_smul (r : ℚ) (M : QMatrix 8 8) :
    reducedDifferenceQ (r • M) = r * reducedDifferenceQ M := by
  simp only [reducedDifferenceQ, Matrix.smul_apply, smul_eq_mul]
  ring

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem difference_spin_four (a b c d : Fin 5 → ℚ) :
    reducedDifferenceQ (spinCombinationQ a * spinCombinationQ b *
      spinCombinationQ c * spinCombinationQ d) =
      2 * quarticDetQ (fun j => a j.succ) (fun j => b j.succ)
        (fun j => c j.succ) (fun j => d j.succ) := by
  simp only [spinCombinationQ, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, reducedDifferenceQ_sum,
    reducedDifferenceQ_smul]
  simp_rw [difference_basis_four]
  norm_num [Fin.sum_univ_succ, generatorRowQ, quarticDetQ]
  ring

end HierarchicalLaminates
