module

public import HierarchicalLaminates.GClosure.TorusMatrix
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Directional derivatives from continuous periodic coordinate partials
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Composition Filter
open scoped Topology

def pairFlow (q : Domain) (z : ℝ × ℝ) : Domain :=
  q + ![(z.1 : UnitAddCircle), (z.2 : UnitAddCircle)]

theorem pairFlow_continuous (q : Domain) : Continuous (pairFlow q) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const.add ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst)
  · exact continuous_const.add ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)

theorem pairFlow_horizontal (q : Domain) (x y : ℝ) :
    pairFlow q (x,y) = coordinateFlow 0 (pairFlow q (0,y)) x := by
  ext i
  fin_cases i <;> simp [pairFlow, coordinateFlow, Matrix.vecHead, Matrix.vecTail]

theorem pairFlow_vertical (q : Domain) (x y : ℝ) :
    pairFlow q (x,y) = coordinateFlow 1 (pairFlow q (x,0)) y := by
  ext i
  fin_cases i <;> simp [pairFlow, coordinateFlow, Matrix.vecHead, Matrix.vecTail]

theorem RegularPotential.hasFDerivAt_pairFlow (u : RegularPotential) (c : Fin 16)
    (q : Domain) (z : ℝ × ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => u.potential c (pairFlow q p))
      ((ContinuousLinearMap.toSpanSingleton ℝ (u.gradient (pairFlow q z) (0,c))).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (u.gradient (pairFlow q z) (1,c)))) z := by
  let f : ℝ → ℝ → ℝ := fun x y => u.potential c (pairFlow q (x,y))
  let f₁ : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun x y =>
    ContinuousLinearMap.toSpanSingleton ℝ (u.gradient (pairFlow q (x,y)) (0,c))
  let f₂ : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun x y =>
    ContinuousLinearMap.toSpanSingleton ℝ (u.gradient (pairFlow q (x,y)) (1,c))
  have hf₁ (p : ℝ × ℝ) : HasFDerivAt (fun x => f x p.2) (f₁ p.1 p.2) p.1 := by
    have h := u.hasPartial 0 c (pairFlow q (0,p.2)) p.1
    convert h.hasFDerivAt using 1
    · ext x
      exact congrArg (u.potential c) (pairFlow_horizontal q x p.2)
    · rw [← pairFlow_horizontal]
  have hf₂ (p : ℝ × ℝ) : HasFDerivAt (fun y => f p.1 y) (f₂ p.1 p.2) p.2 := by
    have h := u.hasPartial 1 c (pairFlow q (p.1,0)) p.2
    convert h.hasFDerivAt using 1
    · ext y
      exact congrArg (u.potential c) (pairFlow_vertical q p.1 y)
    · rw [← pairFlow_vertical]
  have hcont (i : Fin 2) : Continuous (fun p : ℝ × ℝ =>
      ContinuousLinearMap.toSpanSingleton ℝ (u.gradient (pairFlow q p) (i,c))) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp
      (((EuclideanSpace.proj (𝕜 := ℝ) (i,c)).continuous.comp u.gradient.continuous).comp
        (pairFlow_continuous q))
  exact (hasStrictFDerivAt_uncurry_coprod
    (𝕜 := ℝ) (E₁ := ℝ) (E₂ := ℝ) (F := ℝ)
    (f := f) (f₁ := f₁) (f₂ := f₂)
    (Eventually.of_forall hf₁) (Eventually.of_forall hf₂)
    (hcont 0).continuousAt (hcont 1).continuousAt).hasFDerivAt

def linearFlow (q : Domain) (v : Fin 2 → ℝ) (s : ℝ) : Domain :=
  pairFlow q (v 0 * s, v 1 * s)

theorem RegularPotential.hasDerivAt_linearFlow (u : RegularPotential) (c : Fin 16)
    (q : Domain) (v : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => u.potential c (linearFlow q v s))
      (v 0 * u.gradient (linearFlow q v t) (0,c) +
        v 1 * u.gradient (linearFlow q v t) (1,c)) t := by
  have hpath : HasDerivAt (fun s : ℝ => (v 0 * s,v 1 * s)) (v 0,v 1) t :=
    by simpa only [mul_one, id_eq] using
      ((hasDerivAt_id t).const_mul (v 0)).prodMk ((hasDerivAt_id t).const_mul (v 1))
  have h := (RegularPotential.hasFDerivAt_pairFlow u c q (v 0 * t,v 1 * t)).comp_hasDerivAt t hpath
  convert h using 1 <;>
    simp [linearFlow, ContinuousLinearMap.coprod_apply, mul_comm]
  rfl

end HierarchicalLaminates.GClosure
