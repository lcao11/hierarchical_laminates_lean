module

public import HierarchicalLaminates.TwoWell.Envelopes32
public import HierarchicalLaminates.Periodic.Rescaling

/-!
# Nonlinear periodic Jensen inequalities at every positive period

For `L > 0`, the period-`L` tests are defined using continuous potentials and
their continuous coordinate derivatives on `(ℝ / Lℤ)²`. The scaling
`u_L(y) = L * u(y / L)` preserves the gradient after the change of coordinates.

Normalized measure transport preserves test integrability in both directions
and identifies the Jensen predicates and their minorant suprema for every
real-valued integrand. The normalized integral also equals `L⁻²` times the
Lebesgue integral over the open square `(0, L)²` for integrable trial energies.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory HierarchicalLaminates.Periodic HierarchicalLaminates.Composition

variable (L : ℝ) [hL : Fact (0 < L)]

/-- C¹ periodic potentials on a period-L torus. -/
structure PeriodRegularPotential where
  potential : Fin 16 → C(PeriodDomain L, ℝ)
  gradient : C(PeriodDomain L, PhysicalGradient)
  hasPartial : ∀ i a q t, HasDerivAt
    (fun s : ℝ => potential a (periodCoordinateFlow L i q s))
    (gradient (periodCoordinateFlow L i q t) (i, a)) t

/-- Pull back the gradient and divide the potential by the period. -/
def PeriodRegularPotential.pull (u : PeriodRegularPotential L) : RegularPotential where
  potential a := L⁻¹ • pullContinuous L (u.potential a)
  gradient := pullContinuous L u.gradient
  hasPartial i a q t := by
    have hd := ((u.hasPartial i a (scaleTorus L q) (L * t)).comp t
      ((hasDerivAt_id t).const_mul L)).const_mul L⁻¹
    convert hd using 1
    · ext s
      change L⁻¹ * u.potential a (scaleTorus L (coordinateFlow i q s)) =
        L⁻¹ * u.potential a (periodCoordinateFlow L i (scaleTorus L q) (L * s))
      rw [scaleTorus_coordinateFlow]
    · change u.gradient (scaleTorus L (coordinateFlow i q t)) (i,a) =
        L⁻¹ * (u.gradient (periodCoordinateFlow L i (scaleTorus L q) (L*t)) (i,a) * (L * 1))
      rw [scaleTorus_coordinateFlow]
      field_simp [hL.out.ne']

/-- Scale the potential by `u_L(y) = L * u(y / L)`, preserving the pulled-back gradient. -/
def pushRegularPotential (u : RegularPotential) : PeriodRegularPotential L where
  potential a := L • pushContinuous L (u.potential a)
  gradient := pushContinuous L u.gradient
  hasPartial i a q t := by
    have hd := ((u.hasPartial i a ((scaleTorus L).symm q) (t / L)).comp t
      ((hasDerivAt_id t).div_const L)).const_mul L
    convert hd using 1
    · ext s
      change L * u.potential a ((scaleTorus L).symm (periodCoordinateFlow L i q s)) =
        L * u.potential a (coordinateFlow i ((scaleTorus L).symm q) (s / L))
      rw [scaleTorus_symm_coordinateFlow]
    · change u.gradient ((scaleTorus L).symm (periodCoordinateFlow L i q t)) (i,a) =
        L * (u.gradient (coordinateFlow i ((scaleTorus L).symm q) (t/L)) (i,a) * (1/L))
      rw [scaleTorus_symm_coordinateFlow]
      field_simp [hL.out.ne']

@[simp] theorem pull_pushPeriod_gradient (u : RegularPotential) :
    ((pushRegularPotential L u).pull L).gradient = u.gradient :=
  pullContinuous_pushContinuous L u.gradient

@[simp] theorem pushPeriod_pull_gradient (u : PeriodRegularPotential L) :
    (pushRegularPotential L (u.pull L)).gradient = u.gradient :=
  pushContinuous_pullContinuous L u.gradient

@[simp] theorem pull_pushPeriod_potential (u : RegularPotential) (a : Fin 16) :
    ((pushRegularPotential L u).pull L).potential a = u.potential a := by
  ext q
  change L⁻¹ * (L * u.potential a ((scaleTorus L).symm (scaleTorus L q))) =
    u.potential a q
  rw [(scaleTorus L).symm_apply_apply]
  field_simp [hL.out.ne']

@[simp] theorem pushPeriod_pull_potential (u : PeriodRegularPotential L) (a : Fin 16) :
    (pushRegularPotential L (u.pull L)).potential a = u.potential a := by
  ext q
  change L * (L⁻¹ * u.potential a (scaleTorus L ((scaleTorus L).symm q))) =
    u.potential a q
  rw [(scaleTorus L).apply_symm_apply]
  field_simp [hL.out.ne']

/-- A full `2 × 32` trial formed from two independent sixteen-component potentials. -/
def periodRegularTrial32 (F : Gradient32) (u v : PeriodRegularPotential L)
    (q : PeriodDomain L) : Gradient32 :=
  join32 ((split32 F).1 + (fun c => u.gradient q c),
    (split32 F).2 + (fun c => v.gradient q c))

theorem periodRegularTrial32_pull (F : Gradient32) (u v : PeriodRegularPotential L)
    (q : Domain) :
    regularTrial32 F (u.pull L) (v.pull L) q =
      periodRegularTrial32 L F u v (scaleTorus L q) := rfl

theorem periodRegularTrial32_push (F : Gradient32) (u v : RegularPotential)
    (q : PeriodDomain L) :
    periodRegularTrial32 L F (pushRegularPotential L u) (pushRegularPotential L v) q =
      regularTrial32 F u v ((scaleTorus L).symm q) := rfl

/-- Period-`L` Jensen quasiconvexity, including integrability of every C¹ trial energy. -/
def PeriodQuasiconvex32 (h : Gradient32 → ℝ) : Prop :=
  ∀ (F : Gradient32) (u v : PeriodRegularPotential L),
    Integrable (fun q => h (periodRegularTrial32 L F u v q)) (periodMeasure L) ∧
      h F ≤ ∫ q, h (periodRegularTrial32 L F u v q) ∂periodMeasure L

/-- The pointwise supremum of all period-L Jensen minorants. -/
def periodQuasiconvexEnvelope32 (W : Gradient32 → ℝ) (F : Gradient32) : ℝ :=
  sSup ((fun h => h F) '' {h | PeriodQuasiconvex32 L h ∧ ∀ G, h G ≤ W G})

theorem periodTrial_integrable_iff (h : Gradient32 → ℝ) (F : Gradient32)
    (u v : PeriodRegularPotential L) :
    Integrable (fun q => h (regularTrial32 F (u.pull L) (v.pull L) q)) domainMeasure ↔
      Integrable (fun q => h (periodRegularTrial32 L F u v q)) (periodMeasure L) := by
  exact (scaleTorus_measurePreserving L).integrable_comp_emb
    (g := fun q : PeriodDomain L => h (periodRegularTrial32 L F u v q))
    (scaleTorus L).toMeasurableEquiv.measurableEmbedding

theorem pushedTrial_integrable_iff (h : Gradient32 → ℝ) (F : Gradient32)
    (u v : RegularPotential) :
    Integrable (fun q => h (periodRegularTrial32 L F (pushRegularPotential L u) (pushRegularPotential L v) q))
      (periodMeasure L) ↔
      Integrable (fun q => h (regularTrial32 F u v q)) domainMeasure := by
  exact (scaleTorus_symm_measurePreserving L).integrable_comp_emb
    (g := fun q : Domain => h (regularTrial32 F u v q))
    (scaleTorus L).toMeasurableEquiv.symm.measurableEmbedding

theorem periodTrial_integral (h : Gradient32 → ℝ) (F : Gradient32)
    (u v : PeriodRegularPotential L) :
    (∫ q, h (regularTrial32 F (u.pull L) (v.pull L) q) ∂domainMeasure) =
      ∫ q, h (periodRegularTrial32 L F u v q) ∂periodMeasure L :=
  integral_rescaling L (fun q => h (periodRegularTrial32 L F u v q))

theorem pushedTrial_integral (h : Gradient32 → ℝ) (F : Gradient32)
    (u v : RegularPotential) :
    (∫ q, h (periodRegularTrial32 L F (pushRegularPotential L u) (pushRegularPotential L v) q)
      ∂periodMeasure L) =
      ∫ q, h (regularTrial32 F u v q) ∂domainMeasure :=
  integral_unscaling L (fun q => h (regularTrial32 F u v q))

/-- For an integrable trial energy, the normalized torus integral equals
`L⁻²` times its Lebesgue integral over `(0, L)²`. -/
theorem periodTrial_integral_openCube (h : Gradient32 → ℝ) (F : Gradient32)
    (u v : PeriodRegularPotential L)
    (hi : Integrable (fun q => h (periodRegularTrial32 L F u v q)) (periodMeasure L)) :
    (∫ q, h (periodRegularTrial32 L F u v q) ∂periodMeasure L) =
      (L ^ 2)⁻¹ * ∫ x in periodOpenCube L,
        h (periodRegularTrial32 L F u v (periodQuotient L x)) := by
  have hiv : Integrable (fun q => h (periodRegularTrial32 L F u v q))
      (volume : Measure (PeriodDomain L)) := by
    rw [periodVolume_eq_smul_normalized L]
    exact hi.smul_measure (by finiteness)
  exact normalized_period_integral_eq_openCube L _ hiv

theorem PeriodQuasiconvex32.openCube_trial {h : Gradient32 → ℝ}
    (hh : PeriodQuasiconvex32 L h) (F : Gradient32) (u v : PeriodRegularPotential L) :
    h F ≤ (L ^ 2)⁻¹ * ∫ x in periodOpenCube L,
      h (periodRegularTrial32 L F u v (periodQuotient L x)) := by
  rw [← periodTrial_integral_openCube L h F u v (hh F u v).1]
  exact (hh F u v).2

/-- The period-`L` and unit-period Jensen predicates agree for every real-valued `h`. -/
theorem periodQuasiconvex32_iff (h : Gradient32 → ℝ) :
    PeriodQuasiconvex32 L h ↔ PeriodicQuasiconvex32 h := by
  constructor
  · intro hh F u v
    have htrial := hh F (pushRegularPotential L u) (pushRegularPotential L v)
    exact ⟨(pushedTrial_integrable_iff L h F u v).mp htrial.1,
      (pushedTrial_integral L h F u v) ▸ htrial.2⟩
  · intro hh F u v
    have htrial := hh F (u.pull L) (v.pull L)
    exact ⟨(periodTrial_integrable_iff L h F u v).mp htrial.1,
      (periodTrial_integral L h F u v) ▸ htrial.2⟩

/-- Period rescaling preserves the pointwise supremum of all admissible minorants. -/
theorem periodQuasiconvexEnvelope32_eq (W : Gradient32 → ℝ) (F : Gradient32) :
    periodQuasiconvexEnvelope32 L W F = quasiconvexEnvelope32 W F := by
  unfold periodQuasiconvexEnvelope32 quasiconvexEnvelope32
  simp only [periodQuasiconvex32_iff]

end HierarchicalLaminates.TwoWell
