module

public import HierarchicalLaminates.Finite.FastExpansion

/-!
# Exact finite Neumann coefficients for the loading difference

The first four coefficients vanish by the short-product identities. Expanding
the fifth coefficient into a rational finite sum and reducing it in the kernel
gives its exact positive value.
-/

@[expose] public section

namespace HierarchicalLaminates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem loading_coefficient_one : finiteLoadingCoefficient 0 = 0 := by
  exact coefficient_one_zero

theorem loading_coefficient_two : finiteLoadingCoefficient 1 = 0 := by
  exact coefficient_two_zero

theorem loading_coefficient_three : finiteLoadingCoefficient 2 = 0 := by
  exact coefficient_three_zero

theorem loading_coefficient_four : finiteLoadingCoefficient 3 = 0 := by
  exact coefficient_four_zero

theorem fast_fifth_coefficient_value : fastFifthCoefficientQ = 2 * kappaQ := by
  decide +kernel

theorem loading_coefficient_five : finiteLoadingCoefficient 4 = 2 * kappaQ := by
  rw [fifth_coefficient_eq_fast, fast_fifth_coefficient_value]

end HierarchicalLaminates
