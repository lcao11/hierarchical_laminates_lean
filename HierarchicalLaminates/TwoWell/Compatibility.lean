module

public import HierarchicalLaminates.TwoWell.Envelopes

/-! Unit-normal compatibility covers every conventional outer-product jump. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open HierarchicalLaminates.Lamination

def horizontalNormal : LayerNormal := ⟨![1,0], by norm_num⟩

theorem normalize_spatial_vector (n : Fin 2 → ℝ) :
    ∃ (N : LayerNormal) (r : ℝ), ∀ i, n i = r*N.coordinates i := by
  by_cases hz : n 0 = 0 ∧ n 1 = 0
  · refine ⟨horizontalNormal,0,?_⟩
    intro i
    fin_cases i <;> simp [hz.1,hz.2]
  · have hs : 0 < n 0 ^ 2+n 1 ^ 2 := by
      rcases not_and_or.mp hz with h | h
      · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (n 1)]
      · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (n 0)]
    let r := Real.sqrt (n 0 ^ 2+n 1 ^ 2)
    have hr : 0 < r := Real.sqrt_pos.2 hs
    have hrsq : r^2 = n 0 ^ 2+n 1 ^ 2 := Real.sq_sqrt hs.le
    let N : LayerNormal := ⟨fun i => n i/r, by
      rw [div_pow,div_pow,← add_div,← hrsq,div_self (pow_ne_zero 2 hr.ne')]
      ⟩
    refine ⟨N,r,?_⟩
    intro i
    change n i = r*(n i/r)
    field_simp [hr.ne']

/-- An unrestricted real outer-product direction in each block, with one spatial vector. -/
def OuterCompatible (F₁ F₂ : PairedGradient) : Prop :=
  ∃ (n : Fin 2 → ℝ) (z₁ z₂ : Fin 16 → ℝ),
    (∀ i a, F₁.1 (i,a)-F₂.1 (i,a) = n i*z₁ a) ∧
    (∀ i a, F₁.2 (i,a)-F₂.2 (i,a) = n i*z₂ a)

theorem compatible_iff_outerCompatible (F₁ F₂ : PairedGradient) :
    Compatible F₁ F₂ ↔ OuterCompatible F₁ F₂ := by
  constructor
  · rintro ⟨n,z₁,z₂,h₁,h₂⟩
    refine ⟨n.coordinates,z₁,z₂,?_,?_⟩
    · intro i a
      exact congrFun h₁ (i,a)
    · intro i a
      exact congrFun h₂ (i,a)
  · rintro ⟨n,z₁,z₂,h₁,h₂⟩
    obtain ⟨N,r,hr⟩ := normalize_spatial_vector n
    refine ⟨N,r • z₁,r • z₂,?_,?_⟩
    · ext ⟨i,a⟩
      change F₁.1 (i,a)-F₂.1 (i,a) = N.coordinates i*(r*z₁ a)
      rw [h₁,hr]
      ring
    · ext ⟨i,a⟩
      change F₁.2 (i,a)-F₂.2 (i,a) = N.coordinates i*(r*z₂ a)
      rw [h₂,hr]
      ring

end HierarchicalLaminates.TwoWell
