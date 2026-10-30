module

public import HierarchicalLaminates.TwoWell.Components32
public import HierarchicalLaminates.Algebra.RealData
public import HierarchicalLaminates.GClosure.DimensionAll

/-!
# Rational branch matrices and constituent order

A real matrix has rational entries when it is the entrywise image of a
rational matrix. This property is preserved by inversion,
multiplication, transpose, spatial duality, component extension and reindexing.
It therefore holds for both thirty-two-component complementary branch matrices
and for the constructed constituents in every component count `m ≥ 16`.

The final results record the quadratic-form order of the two constituents and
show that adding passive components preserves it.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates

open Matrix Lamination TwoWell GClosure

/-- A real matrix has rational entries if it is the entrywise cast of a rational matrix. -/
def HasRationalEntries {ι κ : Type*} (A : Matrix ι κ ℝ) : Prop :=
  ∃ Q : Matrix ι κ ℚ, A = Q.map (algebraMap ℚ ℝ)

/-- Rational-to-real casting commutes with matrix inversion. The identity also
holds for singular matrices under the totalized matrix-inverse convention. -/
theorem rationalMatrix_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℚ) :
    (Q.map (algebraMap ℚ ℝ))⁻¹ = (Q⁻¹).map (algebraMap ℚ ℝ) := by
  rw [Matrix.inv_def, Matrix.inv_def]
  have hd : (Q.map (algebraMap ℚ ℝ)).det = (Q.det : ℝ) :=
    ((algebraMap ℚ ℝ).map_det Q).symm
  have ha : (Q.map (algebraMap ℚ ℝ)).adjugate = Q.adjugate.map (algebraMap ℚ ℝ) :=
    ((algebraMap ℚ ℝ).map_adjugate Q).symm
  rw [hd, ha]
  ext i j
  simp [Ring.inverse_eq_inv', Matrix.map_apply]

/-- Inversion preserves rational entries. -/
theorem HasRationalEntries.inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (h : HasRationalEntries A) : HasRationalEntries A⁻¹ := by
  obtain ⟨Q, rfl⟩ := h
  exact ⟨Q⁻¹, rationalMatrix_inv Q⟩

theorem HasRationalEntries.mul {ι κ ν : Type*} [Fintype κ]
    {A : Matrix ι κ ℝ} {B : Matrix κ ν ℝ}
    (hA : HasRationalEntries A) (hB : HasRationalEntries B) : HasRationalEntries (A * B) := by
  obtain ⟨P, rfl⟩ := hA
  obtain ⟨Q, rfl⟩ := hB
  refine ⟨P * Q, ?_⟩
  ext i j
  simp [Matrix.mul_apply, Matrix.map_apply]

theorem HasRationalEntries.transpose {ι κ : Type*} {A : Matrix ι κ ℝ}
    (h : HasRationalEntries A) : HasRationalEntries Aᵀ := by
  obtain ⟨Q, rfl⟩ := h
  exact ⟨Qᵀ, rfl⟩

/-- Spatial rotation uses only the rational entries `0`, `1` and `-1`. -/
theorem rotationMatrix_rational : HasRationalEntries rotationMatrix := by
  refine ⟨fun p q => if p.2 = q.2 then
    if p.1 = 0 then (if q.1 = 1 then 1 else 0)
    else (if q.1 = 0 then -1 else 0) else 0, ?_⟩
  ext p q
  change rotationMatrix p q = algebraMap ℚ ℝ _
  unfold rotationMatrix
  split_ifs <;> norm_num [*]

/-- The complementary tensor obtained by inverse and spatial rotation has rational entries. -/
theorem HasRationalEntries.dual {A : Tensor16} (h : HasRationalEntries A) :
    HasRationalEntries (dual A) :=
  (rotationMatrix_rational.mul h.inv).mul rotationMatrix_rational.transpose

/-- The material map preserves rational entries of the reduced parameter. -/
theorem materialTensor_rational {H : RMatrix8} (h : HasRationalEntries H) :
    HasRationalEntries (materialTensor H) := by
  obtain ⟨Q, rfl⟩ := h
  let T : Matrix (Fin 2 × Fin 16) (Fin 2 × Fin 16) ℚ := fun i j =>
    if i.1 = j.1 then
      (if i.1 = 0 then 1 - factorQ * Q * factorQᵀ else verticalQ) i.2 j.2 else 0
  refine ⟨T, ?_⟩
  have hhorizontal : horizontalR (Q.map (algebraMap ℚ ℝ)) =
      realMatrix (1 - factorQ * Q * factorQᵀ) := by
    change horizontalR (realMatrix Q) = realMatrix (1 - factorQ * Q * factorQᵀ)
    rw [realMatrix_sub, realMatrix_one, realMatrix_mul, realMatrix_mul, realMatrix_transpose]
    rfl
  ext i j
  change materialTensor (Q.map (algebraMap ℚ ℝ)) i j = algebraMap ℚ ℝ (T i j)
  simp only [materialTensor, Matrix.of_apply, hhorizontal, T, apply_ite, map_zero]
  split_ifs <;> rfl

theorem phaseZero_rational : HasRationalEntries phaseZero := by
  apply materialTensor_rational
  exact ⟨0, by ext i j; simp⟩

theorem phaseOne_rational : HasRationalEntries (phaseOne rho) := by
  apply materialTensor_rational
  refine ⟨rhoQ • (1 : Matrix (Fin 8) (Fin 8) ℚ), ?_⟩
  ext i j
  change (rho • (1 : Matrix (Fin 8) (Fin 8) ℝ)) i j =
    algebraMap ℚ ℝ ((rhoQ • (1 : Matrix (Fin 8) (Fin 8) ℚ)) i j)
  by_cases hij : i = j <;> simp [rho, hij]

/-- Pairing a rational tensor with its complementary dual gives a rational
thirty-two-component quadratic branch matrix. -/
theorem HasRationalEntries.branchTensor32 {A : Tensor16} (h : HasRationalEntries A) :
    HasRationalEntries (branchTensor32 A) := by
  obtain ⟨P, hP⟩ := h
  obtain ⟨Q, hQ⟩ := HasRationalEntries.dual ⟨P, hP⟩
  let B : Matrix (Fin 2 × (Fin 16 ⊕ Fin 16)) (Fin 2 × (Fin 16 ⊕ Fin 16)) ℚ :=
    fun p q => match p.2, q.2 with
    | .inl a, .inl b => P (p.1, a) (q.1, b)
    | .inr a, .inr b => Q (p.1, a) (q.1, b)
    | _, _ => 0
  refine ⟨fun p q => B (p.1, componentSumEquiv.symm p.2)
    (q.1, componentSumEquiv.symm q.2), ?_⟩
  ext ⟨i, a⟩ ⟨j, b⟩
  change pairedTensor A (i, componentSumEquiv.symm a) (j, componentSumEquiv.symm b) =
    algebraMap ℚ ℝ (B (i, componentSumEquiv.symm a) (j, componentSumEquiv.symm b))
  have hQ' : TwoWell.dual (P.map (algebraMap ℚ ℝ)) = Q.map (algebraMap ℚ ℝ) := by
    simpa only [hP] using hQ
  cases ha : componentSumEquiv.symm a <;> cases hb : componentSumEquiv.symm b <;>
    simp [pairedTensor, B, hQ', hP, Matrix.map_apply]

/-- Both matrices defining the two-well quadratic branches have rational entries. -/
theorem quadratic_branches_rational :
    HasRationalEntries (branchTensor32 phaseZero) ∧
      HasRationalEntries (branchTensor32 (phaseOne rho)) :=
  ⟨phaseZero_rational.branchTensor32, phaseOne_rational.branchTensor32⟩

/-- Adding an identity tensor in passive components preserves rational entries. -/
theorem HasRationalEntries.extendTensor {α β : Type*} {A : Tensor α}
    (h : HasRationalEntries A) : HasRationalEntries (GClosure.extendTensor (β := β) A) := by
  classical
  obtain ⟨P, hP⟩ := h
  let Q : Matrix (Fin 2 × (α ⊕ β)) (Fin 2 × (α ⊕ β)) ℚ := fun p q =>
    match p.2, q.2 with
    | .inl a, .inl b => P (p.1, a) (q.1, b)
    | .inr a, .inr b => if p.1 = q.1 ∧ a = b then 1 else 0
    | _, _ => 0
  refine ⟨Q, ?_⟩
  ext ⟨i, a⟩ ⟨j, b⟩
  change GClosure.extendTensor A (i, a) (j, b) = algebraMap ℚ ℝ (Q (i, a) (j, b))
  cases a <;> cases b <;> simp [GClosure.extendTensor, Q, hP, Matrix.map_apply]

/-- A change of component indices preserves rational entries. -/
theorem HasRationalEntries.reindexTensor {α β : Type*} (e : α ≃ β) {A : Tensor α}
    (h : HasRationalEntries A) : HasRationalEntries (GClosure.reindexTensor e A) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun c d => P ((componentEquiv e).symm c) ((componentEquiv e).symm d), ?_⟩
  rw [hP]
  rfl

/-- Both constructed constituents have rational entries in every component count `m ≥ 16`. -/
theorem dimension_constituents_rational (m : ℕ) (hm : 16 ≤ m) :
    HasRationalEntries (dimensionPhaseZero m hm) ∧
      HasRationalEntries (dimensionPhaseOne m hm) :=
  ⟨phaseZero_rational.extendTensor.reindexTensor (dimensionEquiv m hm),
    phaseOne_rational.extendTensor.reindexTensor (dimensionEquiv m hm)⟩

/-- The phase-one quadratic energy is at most the phase-zero energy at every loading. -/
theorem constituent_energy_order (F : Gradient (Fin 16)) :
    quadraticEnergy (phaseOne rho) F ≤ quadraticEnergy phaseZero F := by
  rw [phaseOne, phaseZero, materialTensor_energy, materialTensor_energy]
  simp only [quadraticFormValue, horizontalR_quadratic, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, Matrix.zero_mulVec, dotProduct_zero, smul_eq_mul]
  have hn := real_dot_self_nonneg (factorRᵀ *ᵥ (fun a => F (0, a)))
  nlinarith [mul_nonneg rho_pos.le hn]

/-- The same constituent energy order holds after adding passive components
and reindexing to any `m ≥ 16`. -/
theorem dimension_constituent_energy_order (m : ℕ) (hm : 16 ≤ m)
    (F : Gradient (Fin m)) :
    quadraticEnergy (dimensionPhaseOne m hm) F ≤
      quadraticEnergy (dimensionPhaseZero m hm) F := by
  unfold dimensionPhaseOne dimensionPhaseZero
  rw [← reindexGradient_symm (dimensionEquiv m hm) F,
    quadraticEnergy_reindex, quadraticEnergy_reindex,
    quadraticEnergy_extendTensor, quadraticEnergy_extendTensor]
  exact add_le_add (constituent_energy_order _) le_rfl

end HierarchicalLaminates
