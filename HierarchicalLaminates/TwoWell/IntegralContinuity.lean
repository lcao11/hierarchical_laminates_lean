module

public import HierarchicalLaminates.TwoWell.PeriodicEnergy
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpOrder

/-! Strong-L² continuity of the integral of the minimum of two quadratics.

Each quadratic is represented by its L¹ density via Hölder's continuous
bilinear map. Taking the pointwise minimum is continuous in L¹, and integration
is continuous.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory Matrix HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material
  HierarchicalLaminates.Lamination

abbrev EnergyDensity := Lp ℝ 1 domainMeasure

def quadraticDensity (A : Tensor16) (e : PhysicalField) : EnergyDensity :=
  (innerSL ℝ).holderL domainMeasure 2 2 1
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) A).compLpL 2 domainMeasure e) e

theorem quadraticDensity_continuous (A : Tensor16) : Continuous (quadraticDensity A) := by
  exact ((innerSL ℝ).holderL domainMeasure 2 2 1).continuous₂.comp
    (((Matrix.toEuclideanCLM (𝕜 := ℝ) A).compLpL 2 domainMeasure).continuous.prodMk
      continuous_id)

theorem quadraticDensity_coe (A : Tensor16) (e : PhysicalField) :
    quadraticDensity A e =ᵐ[domainMeasure] fun q => quadraticEnergy A (e q : Gradient16) := by
  let a := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  have hh := (innerSL ℝ).coeFn_holder (r := 1) (a.compLpL 2 domainMeasure e) e
  filter_upwards [hh,a.coeFn_compLpL e] with q hq ha
  change quadraticDensity A e q = inner ℝ (a.compLpL 2 domainMeasure e q) (e q) at hq
  rw [hq,ha,real_inner_comm,Matrix.inner_toEuclideanCLM]
  rfl

def pairedDensity (A : Tensor16) (z : PhysicalField × PhysicalField) : EnergyDensity :=
  quadraticDensity A z.1+quadraticDensity (dual A) z.2

theorem pairedDensity_continuous (A : Tensor16) : Continuous (pairedDensity A) :=
  ((quadraticDensity_continuous A).comp continuous_fst).add
    ((quadraticDensity_continuous (dual A)).comp continuous_snd)

theorem pairedDensity_coe (A : Tensor16) (e g : PhysicalField) :
    pairedDensity A (e,g) =ᵐ[domainMeasure]
      fun q => pairedEnergy A ((e q : Gradient16),(g q : Gradient16)) := by
  filter_upwards [Lp.coeFn_add (quadraticDensity A e) (quadraticDensity (dual A) g),
    quadraticDensity_coe A e,quadraticDensity_coe (dual A) g] with q hadd he hg
  change pairedDensity A (e,g) q = _ at hadd
  rw [hadd]
  simp only [Pi.add_apply]
  rw [he,hg]
  rfl

def twoWellDensity (z : PhysicalField × PhysicalField) : EnergyDensity :=
  pairedDensity phaseZero z ⊓ pairedDensity (phaseOne rho) z

theorem twoWellDensity_continuous : Continuous twoWellDensity :=
  (pairedDensity_continuous phaseZero).inf (pairedDensity_continuous (phaseOne rho))

theorem twoWellDensity_coe (e g : PhysicalField) :
    twoWellDensity (e,g) =ᵐ[domainMeasure]
      fun q => twoWellEnergy ((e q : Gradient16),(g q : Gradient16)) := by
  filter_upwards [Lp.coeFn_inf (pairedDensity phaseZero (e,g))
      (pairedDensity (phaseOne rho) (e,g)),
    pairedDensity_coe phaseZero e g,pairedDensity_coe (phaseOne rho) e g]
    with q hinf h₀ h₁
  change twoWellDensity (e,g) q = _ at hinf
  rw [hinf]
  simp only [Pi.inf_apply,h₀,h₁]
  rfl

def twoWellIntegral (z : PhysicalField × PhysicalField) : ℝ :=
  ∫ q, twoWellEnergy ((z.1 q : Gradient16),(z.2 q : Gradient16)) ∂domainMeasure

theorem twoWellIntegral_eq (e g : PhysicalField) :
    twoWellIntegral (e,g) = ∫ q, twoWellDensity (e,g) q ∂domainMeasure :=
  (integral_congr_ae (twoWellDensity_coe e g)).symm

/-- The nonlinear integral is continuous under strong L² convergence of both blocks. -/
theorem twoWellIntegral_continuous : Continuous twoWellIntegral := by
  have h := (continuous_integral : Continuous
    (fun f : EnergyDensity => ∫ q, f q ∂domainMeasure)).comp twoWellDensity_continuous
  exact h.congr (fun z => (twoWellIntegral_eq z.1 z.2).symm)

end HierarchicalLaminates.TwoWell
