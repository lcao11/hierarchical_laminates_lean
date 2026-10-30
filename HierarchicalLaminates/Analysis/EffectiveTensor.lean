module

public import HierarchicalLaminates.Analysis.CellProblem

/-!
# Effective response on a space of loadings

A pairing identity relates the constant-field embedding to the mean map.
The effective response is the mean constitutive flux of the cell field;
for a symmetric coercive law, its quadratic form equals the minimum cell energy.
-/

@[expose] public section

noncomputable section

namespace HierarchicalLaminates.Analysis

variable {H E : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (G : Submodule ℝ H) [CompleteSpace G]

/-- Effective tensor defined by mean constitutive flux. -/
def effectiveOperator (constant : E →L[ℝ] H) (mean : H →L[ℝ] E)
    (A : H →L[ℝ] H) (μ : ℝ) (hμ : 0 < μ) (hA : CoerciveLaw A μ) : E →L[ℝ] E :=
  mean.comp (A.comp ((cellField G A μ hμ hA).comp constant))

/-- The effective quadratic form equals the energy of the cell field. -/
theorem effectiveOperator_energy (constant : E →L[ℝ] H) (mean : H →L[ℝ] E)
    (hpair : ∀ F : E, ∀ v : H, inner ℝ (constant F) v = inner ℝ F (mean v))
    (A : H →L[ℝ] H) (μ : ℝ) (hμ : 0 < μ) (hA : CoerciveLaw A μ) (F : E) :
    inner ℝ (effectiveOperator G constant mean A μ hμ hA F) F =
      inner ℝ (A (cellField G A μ hμ hA (constant F)))
        (cellField G A μ hμ hA (constant F)) := by
  let e := cellField G A μ hμ hA (constant F)
  have he : IsCellField G A (constant F) e := cellField_isCellField G A μ hμ hA _
  change inner ℝ (mean (A e)) F = inner ℝ (A e) e
  calc
    inner ℝ (mean (A e)) F = inner ℝ F (mean (A e)) := real_inner_comm _ _
    _ = inner ℝ (constant F) (A e) := (hpair F (A e)).symm
    _ = inner ℝ (A e) (constant F) := real_inner_comm _ _
    _ = inner ℝ (A e) e := (cell_pairing_eq he he.1).symm

/-- The effective tensor is self-adjoint whenever the material operator is. -/
theorem effectiveOperator_symmetric (constant : E →L[ℝ] H) (mean : H →L[ℝ] E)
    (hpair : ∀ F : E, ∀ v : H, inner ℝ (constant F) v = inner ℝ F (mean v))
    (A : H →L[ℝ] H) (hAs : SymmetricLaw A) (μ : ℝ) (hμ : 0 < μ)
    (hA : CoerciveLaw A μ) :
    SymmetricLaw (effectiveOperator G constant mean A μ hμ hA) := by
  intro F Q
  let eF := cellField G A μ hμ hA (constant F)
  let eQ := cellField G A μ hμ hA (constant Q)
  have heF : IsCellField G A (constant F) eF := cellField_isCellField G A μ hμ hA _
  have heQ : IsCellField G A (constant Q) eQ := cellField_isCellField G A μ hμ hA _
  change inner ℝ (mean (A eF)) Q = inner ℝ F (mean (A eQ))
  calc
    inner ℝ (mean (A eF)) Q = inner ℝ Q (mean (A eF)) := real_inner_comm _ _
    _ = inner ℝ (constant Q) (A eF) := (hpair Q (A eF)).symm
    _ = inner ℝ (A eF) (constant Q) := real_inner_comm _ _
    _ = inner ℝ (A eF) eQ := (cell_pairing_eq heF heQ.1).symm
    _ = inner ℝ eF (A eQ) := hAs eF eQ
    _ = inner ℝ (A eQ) eF := real_inner_comm _ _
    _ = inner ℝ (A eQ) (constant F) := cell_pairing_eq heQ heF.1
    _ = inner ℝ (constant F) (A eQ) := real_inner_comm _ _
    _ = inner ℝ F (mean (A eQ)) := hpair F (A eQ)

end HierarchicalLaminates.Analysis
