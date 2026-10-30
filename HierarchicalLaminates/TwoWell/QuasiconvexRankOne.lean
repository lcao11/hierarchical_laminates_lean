module

public import HierarchicalLaminates.TwoWell.LaminateJensen
public import HierarchicalLaminates.TwoWell.Components32
public import HierarchicalLaminates.Analysis.CoordinateConvex
public import HierarchicalLaminates.TwoWell.RankOneDirectionClosure

/-!
# From periodic Jensen tests to real rank-one directions

Integer-normal laminate tests first give convexity in each scalar coordinate.
For nonnegative minorants below a continuous obstacle, local bounds then give
joint continuity. Density of integer normals then extends the inequalities to
every real direction. `EnvelopeCharacterization` treats signed minorants by
lower truncation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory Set Filter HierarchicalLaminates HierarchicalLaminates.Periodic
  HierarchicalLaminates.Composition HierarchicalLaminates.GClosure
  HierarchicalLaminates.Lamination HierarchicalLaminates.Analysis

def IntegerNormalJensen (h : PairedGradient → ℝ) : Prop :=
  ∀ (R : TorusCoordinates) (F : PairedGradient) (z₁ z₂ : Fin 16 → ℝ)
    (a : LayerProportion),
    h F ≤ (a : ℝ)*h (F+(1-(a : ℝ)) • pairedNormalJump (coordinateNormal R) z₁ z₂)+
      (1-(a : ℝ))*h (F-(a : ℝ) • pairedNormalJump (coordinateNormal R) z₁ z₂)

theorem IntegerNormalJensen.compatible {h : PairedGradient → ℝ}
    (hh : IntegerNormalJensen h) (R : TorusCoordinates) (F₁ F₂ : PairedGradient)
    (z₁ z₂ : Fin 16 → ℝ)
    (h₁ : F₁.1-F₂.1 = normalJump (coordinateNormal R) z₁)
    (h₂ : F₁.2-F₂.2 = normalJump (coordinateNormal R) z₂)
    (a : LayerProportion) :
    h ((a : ℝ) • F₁+(1-(a : ℝ)) • F₂) ≤
      (a : ℝ)*h F₁+(1-(a : ℝ))*h F₂ := by
  have hJ : pairedNormalJump (coordinateNormal R) z₁ z₂ = F₁-F₂ :=
    Prod.ext h₁.symm h₂.symm
  have hp : ((a : ℝ) • F₁+(1-(a : ℝ)) • F₂)+
      (1-(a : ℝ)) • pairedNormalJump (coordinateNormal R) z₁ z₂ = F₁ := by
    rw [hJ]
    module
  have hm : ((a : ℝ) • F₁+(1-(a : ℝ)) • F₂)-
      (a : ℝ) • pairedNormalJump (coordinateNormal R) z₁ z₂ = F₂ := by
    rw [hJ]
    module
  simpa only [hp,hm] using hh R ((a : ℝ) • F₁+(1-(a : ℝ)) • F₂) z₁ z₂ a

def axisTorusCoordinates (i : Fin 2) : TorusCoordinates :=
  if i = 0 then coordinatesOfCoprime 1 0 (by norm_num)
    else coordinatesOfCoprime 0 1 (by norm_num)

theorem axisNormal_apply (i j : Fin 2) :
    (coordinateNormal (axisTorusCoordinates i)).coordinates j = if j = i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [axisTorusCoordinates,coordinateNormal,coordinateScale,
      coordinatesOfCoprime,coordinatesOfBezout]

theorem IntegerNormalJensen.coordinateConvex {h : PairedGradient → ℝ}
    (hh : IntegerNormalJensen h) (x : Gradient32) (c : Fin 2 × Fin 32) :
    ConvexOn ℝ univ (fun t : ℝ => h (split32 (Function.update x c t))) := by
  refine ⟨convex_univ,?_⟩
  intro t _ s _ a b ha hb hab
  have hb' : b = 1-a := by linarith
  subst b
  let R := axisTorusCoordinates c.1
  let z₁ : Fin 16 → ℝ := fun α => if componentSumEquiv (.inl α) = c.2 then t-s else 0
  let z₂ : Fin 16 → ℝ := fun α => if componentSumEquiv (.inr α) = c.2 then t-s else 0
  have h₁ : (split32 (Function.update x c t)).1-(split32 (Function.update x c s)).1 =
      normalJump (coordinateNormal R) z₁ := by
    funext p
    rcases p with ⟨j,α⟩
    change Function.update x c t (j,componentSumEquiv (.inl α))-
      Function.update x c s (j,componentSumEquiv (.inl α)) =
        (coordinateNormal (axisTorusCoordinates c.1)).coordinates j*z₁ α
    rw [axisNormal_apply]
    by_cases hj : j = c.1 <;> by_cases hα : componentSumEquiv (.inl α) = c.2
    all_goals simp [Function.update,Prod.ext_iff,hj,hα,z₁]
  have h₂ : (split32 (Function.update x c t)).2-(split32 (Function.update x c s)).2 =
      normalJump (coordinateNormal R) z₂ := by
    funext p
    rcases p with ⟨j,α⟩
    change Function.update x c t (j,componentSumEquiv (.inr α))-
      Function.update x c s (j,componentSumEquiv (.inr α)) =
        (coordinateNormal (axisTorusCoordinates c.1)).coordinates j*z₂ α
    rw [axisNormal_apply]
    by_cases hj : j = c.1 <;> by_cases hα : componentSumEquiv (.inr α) = c.2
    all_goals simp [Function.update,Prod.ext_iff,hj,hα,z₂]
  have heq : a • Function.update x c t+(1-a) • Function.update x c s =
      Function.update x c (a*t+(1-a)*s) := by
    funext d
    by_cases hd : d = c
    · subst d
      simp
    · simp only [Pi.add_apply,Pi.smul_apply,Function.update_of_ne hd,smul_eq_mul]
      ring
  have h := hh.compatible R (split32 (Function.update x c t))
    (split32 (Function.update x c s)) z₁ z₂ h₁ h₂ ⟨a,ha,by linarith⟩
  simpa only [← split32_smul,← split32_add,heq,smul_eq_mul] using h

theorem IntegerNormalJensen.continuous_of_nonneg_le {h W : PairedGradient → ℝ}
    (hh : IntegerNormalJensen h) (hzero : ∀ F, 0 ≤ h F)
    (hW : Continuous W) (hle : ∀ F, h F ≤ W F) : Continuous h := by
  have hs : Continuous split32 := paired32Equiv.symm.toLinearMap.continuous_of_finiteDimensional
  have hj : Continuous join32 := paired32Equiv.toLinearMap.continuous_of_finiteDimensional
  have hc : Continuous (fun F : Gradient32 => h (split32 F)) :=
    continuous_of_coordinateConvex_of_nonneg_le hh.coordinateConvex
      (fun F => hzero (split32 F)) (hW.comp hs) (fun F => hle (split32 F))
  simpa only [Function.comp_def,split32_join32] using hc.comp hj

theorem PeriodicQuasiconvex.integerNormalJensen {h W : PairedGradient → ℝ}
    (hh : PeriodicQuasiconvex h) (hW : Continuous W) (hle : ∀ F, h F ≤ W F) :
    IntegerNormalJensen h :=
  hh.coordinateNormal_jensen hW hle

theorem PeriodicQuasiconvex.continuous_of_nonneg_le {h W : PairedGradient → ℝ}
    (hh : PeriodicQuasiconvex h) (hzero : ∀ F, 0 ≤ h F)
    (hW : Continuous W) (hle : ∀ F, h F ≤ W F) : Continuous h :=
  (hh.integerNormalJensen hW hle).continuous_of_nonneg_le hzero hW hle

theorem PeriodicQuasiconvex.rankOneConvex_of_nonneg_le {h W : PairedGradient → ℝ}
    (hh : PeriodicQuasiconvex h) (hzero : ∀ F, 0 ≤ h F)
    (hW : Continuous W) (hle : ∀ F, h F ≤ W F) : RankOneConvex h :=
  rankOneConvex_of_continuous_coordinateNormal_jensen
    (hh.continuous_of_nonneg_le hzero hW hle) (hh.integerNormalJensen hW hle)

end HierarchicalLaminates.TwoWell
