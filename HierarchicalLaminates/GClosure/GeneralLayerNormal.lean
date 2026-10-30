module

public import HierarchicalLaminates.GClosure.LayerContinuity
public import HierarchicalLaminates.GClosure.TorusMatrixBezout

/-! Unit normals associated with periodic coordinates and tangential flux amplitudes. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open Matrix HierarchicalLaminates HierarchicalLaminates.Lamination

def coordinateScale (R : TorusCoordinates) : ℝ :=
  Real.sqrt ((R.matrix 1 0 : ℝ)^2 + (R.matrix 1 1 : ℝ)^2)

theorem coordinateScale_sq_pos (R : TorusCoordinates) :
    0 < (R.matrix 1 0 : ℝ)^2 + (R.matrix 1 1 : ℝ)^2 := by
  rcases R.second_row_nonzero with h | h
  · have hn : (R.matrix 1 0 : ℝ) ≠ 0 := by exact_mod_cast h
    nlinarith [sq_pos_of_ne_zero hn, sq_nonneg (R.matrix 1 1 : ℝ)]
  · have hn : (R.matrix 1 1 : ℝ) ≠ 0 := by exact_mod_cast h
    nlinarith [sq_pos_of_ne_zero hn, sq_nonneg (R.matrix 1 0 : ℝ)]

theorem coordinateScale_pos (R : TorusCoordinates) : 0 < coordinateScale R :=
  Real.sqrt_pos.2 (coordinateScale_sq_pos R)

theorem coordinateScale_sq (R : TorusCoordinates) :
    coordinateScale R ^ 2 = (R.matrix 1 0 : ℝ)^2 + (R.matrix 1 1 : ℝ)^2 :=
  Real.sq_sqrt (coordinateScale_sq_pos R).le

def coordinateNormal (R : TorusCoordinates) : LayerNormal where
  coordinates i := (R.matrix 1 i : ℝ) / coordinateScale R
  unit_length := by
    have hs := coordinateScale_sq R
    have hn := (coordinateScale_pos R).ne'
    field_simp
    nlinarith

@[simp] theorem coordinateNormal_apply (R : TorusCoordinates) (i : Fin 2) :
    (coordinateNormal R).coordinates i = (R.matrix 1 i : ℝ) / coordinateScale R := rfl

theorem coordinateNormal_mul_scale (R : TorusCoordinates) (i : Fin 2) :
    (coordinateNormal R).coordinates i * coordinateScale R = (R.matrix 1 i : ℝ) := by
  simp [coordinateNormal, (coordinateScale_pos R).ne']

theorem normal_component {m : Type*} [Fintype m] [DecidableEq m]
    (n : LayerNormal) (J : Gradient m) (c : m) :
    ((normalMatrix n)ᵀ *ᵥ J) c =
      n.coordinates 0 * J (0,c) + n.coordinates 1 * J (1,c) := by
  simp [Matrix.mulVec, dotProduct, normalMatrix, Fintype.sum_prod_type,
    Fin.sum_univ_two, Pi.single_apply]

def tangentAmplitude {m : Type*} (n : LayerNormal) (J : Gradient m) : m → ℝ :=
  fun c => -n.coordinates 1 * J (0,c) + n.coordinates 0 * J (1,c)

def tangentField {m : Type*} (n : LayerNormal) (z : m → ℝ) : Gradient m :=
  fun c => if c.1 = 0 then -n.coordinates 1 * z c.2 else n.coordinates 0 * z c.2

theorem tangentField_eq_of_normal_zero {m : Type*} [Fintype m] [DecidableEq m]
    (n : LayerNormal) (J : Gradient m) (hJ : (normalMatrix n)ᵀ *ᵥ J = 0) :
    tangentField n (tangentAmplitude n J) = J := by
  ext ⟨i,c⟩
  have hn : n.coordinates 0 * J (0,c) + n.coordinates 1 * J (1,c) = 0 := by
    simpa only [normal_component, Pi.zero_apply] using congrFun hJ c
  have hu := n.unit_length
  fin_cases i
  · change -n.coordinates 1 * (-n.coordinates 1 * J (0,c) +
      n.coordinates 0 * J (1,c)) = J (0,c)
    linear_combination J (0,c) * hu - n.coordinates 0 * hn
  · change n.coordinates 0 * (-n.coordinates 1 * J (0,c) +
      n.coordinates 0 * J (1,c)) = J (1,c)
    linear_combination J (1,c) * hu - n.coordinates 1 * hn

end HierarchicalLaminates.GClosure
