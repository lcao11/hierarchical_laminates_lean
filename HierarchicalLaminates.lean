module

-- Principal existential statements.
public import HierarchicalLaminates.Statements.Composite
public import HierarchicalLaminates.Statements.TwoWell
public import HierarchicalLaminates.Statements.TwoWellPeriod

-- Exact periodic minimizers and nonlinear trial interfaces.
public import HierarchicalLaminates.Periodic.Attainment
public import HierarchicalLaminates.GClosure.Attainment
public import HierarchicalLaminates.TwoWell.H1Trial32
public import HierarchicalLaminates.TwoWell.PeriodicWitness
public import HierarchicalLaminates.TwoWell.ExactTrials
public import HierarchicalLaminates.TwoWell.SmoothTrials

-- Envelope characterizations on the paired and full gradient spaces.
public import HierarchicalLaminates.TwoWell.EnvelopeCharacterization
public import HierarchicalLaminates.TwoWell.EnvelopeCharacterization32

-- Constitutive algebra, exact fractions and closure topology.
public import HierarchicalLaminates.Algebra.InverseClosure
public import HierarchicalLaminates.Binary.MeanAll
public import HierarchicalLaminates.Lamination.CompactFamily
public import HierarchicalLaminates.Lamination.ClosureTopology
public import HierarchicalLaminates.Corrector.FullTensor
public import HierarchicalLaminates.TwoWell.RationalBranches

-- Parameter-dependent physical response and joint smoothness.
public import HierarchicalLaminates.Contrast.Asymptotic
public import HierarchicalLaminates.Contrast.FullTensor
public import HierarchicalLaminates.Contrast.Regularity
public import HierarchicalLaminates.Fourier.SmoothSynthesis
public import HierarchicalLaminates.Corrector.Smoothness
public import HierarchicalLaminates.Contrast.Smoothness
public import HierarchicalLaminates.Contrast.ReducedSymmetry

/-!
# Library entry point

* HierarchicalLaminates.composite_counterexample
* HierarchicalLaminates.two_well_energy_gap

Import this module for the two principal declarations and the public supporting
interfaces listed above. `docs/Statements.md` specifies their mathematical
conventions; `docs/ProofGuide.md` gives a reading order through the proofs.
-/
