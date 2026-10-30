module

public import HierarchicalLaminates.Algebra.MaterialData
public import HierarchicalLaminates.Algebra.Parameters

/-!
# Fourier coefficients of the cosine profile

The profile has seven nonzero Fourier coefficients. Its matrix recurrence
gives each Neumann coefficient as a finite sum.
-/

@[expose] public section

namespace HierarchicalLaminates

abbrev Frequency := ℤ × ℤ

def profileStep : Fin 7 → Frequency :=
  ![(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1), (1, 3), (-1, -3)]

def profileWeight (i : Fin 7) : ℚ := if i = 0 then 1 / 2 else 1 / 12

def profileCoeffQ (k : Frequency) : ℚ :=
  if k = (0, 0) then 1 / 2
  else if k = (1, 0) ∨ k = (-1, 0) ∨ k = (0, 1) ∨ k = (0, -1) ∨
      k = (1, 3) ∨ k = (-1, -3) then 1 / 12 else 0

def directionalWeightQ (k : Frequency) (j : Fin 4) : ℚ :=
  if k = (0, 0) then 0 else
    ((j.val + 1 : ℕ) : ℚ) * (k.1 : ℚ) ^ 2 /
      (4 * (((j.val + 1 : ℕ) : ℚ) * (k.1 : ℚ) ^ 2 + (k.2 : ℚ) ^ 2))

/-- The rational symbol, including its zero-frequency convention. -/
def directionalSymbolQ (k : Frequency) : QMatrix 8 8 :=
  ∑ j : Fin 4, directionalWeightQ k j • ((1 : QMatrix 8 8) + gammaQ j)

/-- Index `n` gives the Neumann coefficient `X_(n+1)`. -/
def neumannCoeffQ : ℕ → Frequency → QMatrix 8 8
  | 0, k => profileCoeffQ k • (1 : QMatrix 8 8)
  | n + 1, k => ∑ s : Fin 7,
      profileWeight s • (directionalSymbolQ (k - profileStep s) *
        neumannCoeffQ n (k - profileStep s))

def finiteLoadingCoefficient (n : ℕ) : ℚ :=
  reducedDifferenceQ (neumannCoeffQ n (0, 0))

theorem profile_weight_sum : (∑ i : Fin 7, profileWeight i) = 1 := by
  decide +kernel

theorem profile_steps_distinct : Function.Injective profileStep := by
  decide +kernel

theorem profile_coeff_at_step : ∀ i : Fin 7,
    profileCoeffQ (profileStep i) = profileWeight i := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem directional_zero : directionalSymbolQ (0, 0) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem directional_vertical : directionalSymbolQ (0, 1) = 0 := by
  decide +kernel

end HierarchicalLaminates
