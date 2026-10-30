module

public import HierarchicalLaminates.GClosure.TorusMatrix

/-! Completing a primitive integer normal to periodic coordinates. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open Matrix

def coordinatesOfBezout (p q a b : ℤ) (h : p * a + q * b = 1) : TorusCoordinates where
  matrix := !![b, -a; p, q]
  inverse := !![q, a; -p, b]
  inverse_mul := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith
  mul_inverse := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

def coordinatesOfCoprime (p q : ℤ) (h : Int.gcd p q = 1) : TorusCoordinates :=
  coordinatesOfBezout p q (Int.gcdA p q) (Int.gcdB p q) (by
    have hg := Int.gcd_eq_gcd_ab p q
    rw [h] at hg
    simpa using hg.symm)

@[simp] theorem coordinatesOfCoprime_second_row (p q : ℤ) (h : Int.gcd p q = 1) :
    (coordinatesOfCoprime p q h).matrix 1 = ![p,q] := rfl

theorem TorusCoordinates.second_row_nonzero (R : TorusCoordinates) :
    R.matrix 1 0 ≠ 0 ∨ R.matrix 1 1 ≠ 0 := by
  by_contra h
  push Not at h
  have hi := congrArg (fun A : IntegerSpatialMatrix => A 1 1) R.mul_inverse
  simp [Matrix.mul_apply, Fin.sum_univ_two, h.1, h.2] at hi

end HierarchicalLaminates.GClosure
