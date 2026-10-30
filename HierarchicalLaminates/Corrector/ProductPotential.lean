module

public import HierarchicalLaminates.Corrector.FieldAssembly
public import HierarchicalLaminates.Corrector.SourceRegularity
public import HierarchicalLaminates.Corrector.WeakProduct
public import HierarchicalLaminates.WeakCalculus.Curl

/-!
# The H¹ product potential for the binary flux correction
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Corrector

open HierarchicalLaminates.Periodic HierarchicalLaminates.Fourier HierarchicalLaminates.WeakCalculus

def productPotentialComponents (p : ScalarField) (z : PotentialVector) : Fin 16 → ScalarField :=
  fun a => continuousProduct (sourceComponent z a) p

def productGradientComponents (p : ScalarField) (dp : Fin 2 → ScalarField)
    (z : PotentialVector) (i : Fin 2) (a : Fin 16) : ScalarField :=
  continuousProduct (sourceComponent z a) (dp i) +
    continuousProduct (sourceDerivative z a i) p

def productGradient (p : ScalarField) (dp : Fin 2 → ScalarField)
    (z : PotentialVector) : PhysicalField :=
  assembleField fun j => productGradientComponents p dp z j.1 j.2

lemma product_hasWeakGradient (p : ScalarField) (dp : Fin 2 → ScalarField)
    (hp : ∀ i, ScalarWeakPartial p (dp i) i) (z : PotentialVector) :
    HasWeakGradient (productPotentialComponents p z) (productGradient p dp z) := by
  intro i a test
  rw [productGradient, component_assembleField]
  have h := weakProduct_cosineSynthesis (hp i) (sourceCoefficients z a)
    (sourceDerivativeCoefficients z a i)
    (fun k => by simpa only [smul_eq_mul] using sourceDerivativeCoefficients_apply z a i k)
  rw [← sourceComponent_eq_synthesis] at h
  exact h test

lemma product_curl_orthogonal (p : ScalarField) (dp : Fin 2 → ScalarField)
    (hp : ∀ i, ScalarWeakPartial p (dp i) i) (z : PotentialVector)
    (g : PhysicalField) (hg : g ∈ gradientSpace) :
    inner ℝ (curlField (productGradient p dp z)) g = 0 :=
  weakCurl_gradient_zero (product_hasWeakGradient p dp hp z) g hg

lemma product_curl_mean_zero (p : ScalarField) (dp : Fin 2 → ScalarField)
    (hp : ∀ i, ScalarWeakPartial p (dp i) i) (z : PotentialVector) :
    meanField (curlField (productGradient p dp z)) = 0 :=
  weakCurl_mean_zero (product_hasWeakGradient p dp hp z)

end HierarchicalLaminates.Corrector
