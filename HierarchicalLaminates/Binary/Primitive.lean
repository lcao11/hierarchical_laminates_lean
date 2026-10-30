module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Pointwise estimates for the bounded stripe primitive. -/

@[expose] public section

namespace HierarchicalLaminates.Binary

def stripePrimitive (h tau t : ℝ) : ℝ := h * (min tau t - tau * t)

theorem primitive_at_zero {h t : ℝ} (ht : 0 ≤ t) :
    stripePrimitive h 0 t = 0 := by
  simp [stripePrimitive, min_eq_left ht]

theorem primitive_at_one {h t : ℝ} (ht : t ≤ 1) :
    stripePrimitive h 1 t = 0 := by
  simp [stripePrimitive, min_eq_right ht]

theorem primitive_unit_bounds {tau t : ℝ} (htau : tau ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ min tau t - tau * t ∧ min tau t - tau * t ≤ 1 / 4 := by
  by_cases hle : tau ≤ t
  · rw [min_eq_left hle]
    have hnonneg := mul_nonneg htau.1 (sub_nonneg.mpr ht.2)
    have hcompare := mul_nonneg htau.1 (sub_nonneg.mpr hle)
    constructor
    · nlinarith
    · nlinarith [sq_nonneg (tau - 1 / 2)]
  · have hrev : t ≤ tau := le_of_not_ge hle
    rw [min_eq_right hrev]
    have hnonneg := mul_nonneg ht.1 (sub_nonneg.mpr htau.2)
    have hcompare := mul_nonneg ht.1 (sub_nonneg.mpr hrev)
    constructor
    · nlinarith
    · nlinarith [sq_nonneg (t - 1 / 2)]

theorem primitive_bounds {h tau t : ℝ} (hh : 0 ≤ h)
    (htau : tau ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ stripePrimitive h tau t ∧ stripePrimitive h tau t ≤ h / 4 := by
  obtain ⟨hlo, hhi⟩ := primitive_unit_bounds htau ht
  constructor
  · exact mul_nonneg hh hlo
  · have hm := mul_le_mul_of_nonneg_left hhi hh
    dsimp [stripePrimitive]
    nlinarith

theorem primitive_abs_bound {h tau t : ℝ} (hh : 0 ≤ h)
    (htau : tau ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |stripePrimitive h tau t| ≤ h / 4 := by
  obtain ⟨hlo, hhi⟩ := primitive_bounds hh htau ht
  simpa only [abs_of_nonneg hlo] using hhi

end HierarchicalLaminates.Binary
