module

public import HierarchicalLaminates.Composition.PaperCounterexample
public import HierarchicalLaminates.Composition.MicroscopicApproximation
public import HierarchicalLaminates.Composition.FiniteLocalization
public import HierarchicalLaminates.Composition.TrialFields
public import HierarchicalLaminates.Homogenization.Homogeneous

/-! Shared interfaces for arbitrary laminate directions and additional potential components. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.GClosure

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Material HierarchicalLaminates.Lamination
  HierarchicalLaminates.Homogenization HierarchicalLaminates.Composition

end HierarchicalLaminates.GClosure
