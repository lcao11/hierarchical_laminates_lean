module

public import HierarchicalLaminates.WeakCalculus.Parseval
public import HierarchicalLaminates.Periodic.CellEnergy

/-!
# Exact weak Sobolev potentials and attained cell energies

On the unit two-dimensional torus, the Fourier Poincaré estimate controls a
zero-mean L² potential by its two weak derivatives. It follows that the range
of periodic weak gradients is closed and that each field in `gradientSpace`
has a unique zero-mean weak H¹ potential.

The construction applies componentwise to sixteen potentials. Applied to the
Hilbert-space cell solver, it gives a minimizing potential. Coercivity
is sufficient to recover the solver's potential; the energy-minimization and
uniqueness statements also assume symmetry of the coefficient law.
-/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Periodic

open MeasureTheory Filter
open HierarchicalLaminates HierarchicalLaminates.Fourier HierarchicalLaminates.WeakCalculus
open HierarchicalLaminates.Analysis
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem complexField_norm (u : ScalarField) : ‖complexField u‖ = ‖u‖ := by
  have h := complexField_inner u u
  rw [inner_self_eq_norm_sq_to_K, real_inner_self_eq_norm_sq] at h
  rw [Complex.ofReal_pow] at h
  have hs : ‖complexField u‖ ^ 2 = ‖u‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    exact h
  nlinarith [norm_nonneg (complexField u), norm_nonneg u]

private def scalarCoefficient (u : ScalarField) (k : Fin 2 → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (complexField u) k

private theorem hasSum_scalarCoefficient (u : ScalarField) :
    HasSum (fun k => ‖scalarCoefficient u k‖ ^ 2) (‖u‖ ^ 2) := by
  have h := lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    (UnitAddTorus.mFourierBasis.repr (complexField u))
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  change HasSum (fun k => ‖UnitAddTorus.mFourierBasis.repr (complexField u) k‖ ^ 2)
    (‖UnitAddTorus.mFourierBasis.repr (complexField u)‖ ^ 2) at h
  erw [UnitAddTorus.mFourierBasis.repr.norm_map, complexField_norm] at h
  apply h.congr_fun
  intro k
  erw [UnitAddTorus.mFourierBasis_repr]
  rfl

private theorem scalarCoefficient_zero (u : ScalarField) (hm : meanField u = 0) :
    scalarCoefficient u 0 = 0 := by
  have h := constant_mean_pairing (1 : ℝ) u
  rw [hm] at h
  have hk : frequencyVector (0, 0) = (0 : Fin 2 → ℤ) := by ext i; fin_cases i <;> rfl
  rw [scalarCoefficient, ← hk, coefficient_complexField, cosineKernel_zero, sineKernel_zero]
  simp only [map_zero, inner_zero_right, Complex.ofReal_zero, mul_zero, sub_zero]
  have hc : continuousField (1 : C(Domain, ℝ)) = constantField (1 : ℝ) :=
    continuousField_const 1
  rw [hc, real_inner_comm]
  simpa using h

private theorem weakPartial_coefficient_norm {u du : ScalarField} {i : Fin 2}
    (hu : HasWeakPartial u du i) (k : Fin 2 → ℤ) :
    ‖scalarCoefficient du k‖ = |2 * Real.pi * (k i : ℝ)| * ‖scalarCoefficient u k‖ := by
  have hk : frequencyVector (k 0, k 1) = k := by ext j; fin_cases j <;> rfl
  have h := hu.coefficient (k 0, k 1)
  rw [hk] at h
  unfold scalarCoefficient
  rw [h, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  congr 2
  fin_cases i <;> rfl

private theorem angularFrequency_abs_lower (k : Fin 2 → ℤ) (i : Fin 2)
    (hk : k i ≠ 0) : 2 * Real.pi ≤ |2 * Real.pi * (k i : ℝ)| := by
  have hi : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  rw [abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  nlinarith [Real.pi_pos]

/-- On the unit torus, a zero-mean weak H¹ function satisfies
`2π ‖u‖₂ ≤ ‖∂₁u‖₂ + ‖∂₂u‖₂`. -/
theorem weak_poincare {u ux uy : ScalarField}
    (hx : HasWeakPartial u ux 0) (hy : HasWeakPartial u uy 1)
    (hm : meanField u = 0) : 2 * Real.pi * ‖u‖ ≤ ‖ux‖ + ‖uy‖ := by
  have hterm (k : Fin 2 → ℤ) :
      (2 * Real.pi) ^ 2 * ‖scalarCoefficient u k‖ ^ 2 ≤
        ‖scalarCoefficient ux k‖ ^ 2 + ‖scalarCoefficient uy k‖ ^ 2 := by
    by_cases hk : k = 0
    · subst k
      rw [scalarCoefficient_zero u hm]
      norm_num only [norm_zero, zero_pow, mul_zero]
      exact add_nonneg (sq_nonneg ‖scalarCoefficient ux 0‖) (sq_nonneg ‖scalarCoefficient uy 0‖)
    · have hn : k 0 ≠ 0 ∨ k 1 ≠ 0 := by
        by_contra h
        push Not at h
        apply hk
        ext i
        fin_cases i <;> simp [h.1, h.2]
      rcases hn with hn | hn
      · have hnorm := weakPartial_coefficient_norm hx k
        have hfreq := angularFrequency_abs_lower k 0 hn
        have hmul := mul_le_mul_of_nonneg_right hfreq (norm_nonneg (scalarCoefficient u k))
        have hle : 2 * Real.pi * ‖scalarCoefficient u k‖ ≤ ‖scalarCoefficient ux k‖ := by nlinarith
        have hsq := sq_le_sq₀ (by positivity : 0 ≤ 2 * Real.pi * ‖scalarCoefficient u k‖)
          (norm_nonneg (scalarCoefficient ux k))
        nlinarith [hsq.mpr hle, sq_nonneg ‖scalarCoefficient uy k‖]
      · have hnorm := weakPartial_coefficient_norm hy k
        have hfreq := angularFrequency_abs_lower k 1 hn
        have hmul := mul_le_mul_of_nonneg_right hfreq (norm_nonneg (scalarCoefficient u k))
        have hle : 2 * Real.pi * ‖scalarCoefficient u k‖ ≤ ‖scalarCoefficient uy k‖ := by nlinarith
        have hsq := sq_le_sq₀ (by positivity : 0 ≤ 2 * Real.pi * ‖scalarCoefficient u k‖)
          (norm_nonneg (scalarCoefficient uy k))
        nlinarith [hsq.mpr hle, sq_nonneg ‖scalarCoefficient ux k‖]
  have hsq := hasSum_le hterm ((hasSum_scalarCoefficient u).mul_left ((2 * Real.pi) ^ 2))
    ((hasSum_scalarCoefficient ux).add (hasSum_scalarCoefficient uy))
  have hp : 0 ≤ 2 * Real.pi * ‖u‖ := by positivity
  nlinarith [norm_nonneg u, norm_nonneg ux, norm_nonneg uy]

/-- Subtraction preserves the weak integration-by-parts identity. -/
theorem HasWeakGradient.sub {u v : Fin 16 → ScalarField} {g h : PhysicalField}
    (hu : HasWeakGradient u g) (hv : HasWeakGradient v h) :
    HasWeakGradient (fun a => u a - v a) (g - h) := by
  intro i a test
  simp only [map_sub, inner_sub_left]
  rw [hu, hv]
  ring

/-- Componentwise constant potentials have zero weak gradient. -/
theorem weakGradient_constant (c : Fin 16 → ℝ) :
    HasWeakGradient (fun a => constantField (c a)) 0 := by
  intro i a test
  have hm : meanField (continuousField (test.derivative i)) = 0 := by
    change meanContinuous (test.derivative i) = 0
    rw [meanContinuous_eq_integral]
    exact integral_coordinateDerivative_zero test.value (test.derivative i) i
      (smoothTest_hasDerivAt_flow test i)
  simp only [map_zero, inner_zero_left]
  rw [constant_mean_pairing, hm, inner_zero_right, neg_zero]

/-- Subtract each component's mean to fix the additive-constant ambiguity. -/
def centeredPotential (u : Fin 16 → ScalarField) : Fin 16 → ScalarField :=
  fun a => u a - constantField (meanField (u a))

theorem centeredPotential_mean_zero (u : Fin 16 → ScalarField) (a : Fin 16) :
    meanField (centeredPotential u a) = 0 := by
  change meanField (u a - constantField (meanField (u a))) = 0
  rw [map_sub, mean_constantField, sub_self]

theorem HasWeakGradient.center {u : Fin 16 → ScalarField} {g : PhysicalField}
    (hu : HasWeakGradient u g) : HasWeakGradient (centeredPotential u) g := by
  change HasWeakGradient (fun a => u a - constantField (meanField (u a))) g
  simpa only [sub_zero] using hu.sub (weakGradient_constant (fun a => meanField (u a)))

/-- The weak derivative identity is stable under L² convergence of both the
potential components and their assembled gradients. -/
theorem HasWeakGradient.limit {us : ℕ → Fin 16 → ScalarField} {gs : ℕ → PhysicalField}
    {u : Fin 16 → ScalarField} {g : PhysicalField}
    (hw : ∀ n, HasWeakGradient (us n) (gs n))
    (hu : ∀ a, Tendsto (fun n => us n a) atTop (nhds (u a)))
    (hg : Tendsto gs atTop (nhds g)) : HasWeakGradient u g := by
  intro i a test
  have hL := (((componentField i a).continuous.tendsto g).comp hg).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := continuousField test.value))
  have hR := ((hu a).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := continuousField (test.derivative i)))).neg
  exact tendsto_nhds_unique hL (hR.congr' (Eventually.of_forall (fun n => (hw n i a test).symm)))

/-- Every field in the closure of weak gradients has a zero-mean
weak H¹ potential. Poincaré makes centered approximating potentials Cauchy. -/
theorem gradientSpace_exact_potential (g : PhysicalField) (hg : g ∈ gradientSpace) :
    ∃ u : Fin 16 → ScalarField, HasWeakGradient u g ∧ ∀ a, meanField (u a) = 0 := by
  have hclosure : g ∈ closure (weakGradientSpace : Set PhysicalField) := hg
  obtain ⟨gs, hgs, hlim⟩ := mem_closure_iff_seq_limit.mp hclosure
  have hrep : ∀ n, ∃ u : Fin 16 → ScalarField, HasWeakGradient u (gs n) :=
    fun n => hgs n
  choose vs hvs using hrep
  let us : ℕ → Fin 16 → ScalarField := fun n => centeredPotential (vs n)
  have hw (n : ℕ) : HasWeakGradient (us n) (gs n) := (hvs n).center
  have hm (n : ℕ) (a : Fin 16) : meanField (us n a) = 0 :=
    centeredPotential_mean_zero (vs n) a
  have hc (a : Fin 16) : CauchySeq (fun n => us n a) := by
    have hc0 := (((componentField 0 a).continuous.tendsto g).comp hlim).cauchySeq
    have hc1 := (((componentField 1 a).continuous.tendsto g).comp hlim).cauchySeq
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have he : 0 < ε * Real.pi := mul_pos hε Real.pi_pos
    obtain ⟨N₀, hN₀⟩ := Metric.cauchySeq_iff.mp hc0 (ε * Real.pi) he
    obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.mp hc1 (ε * Real.pi) he
    refine ⟨max N₀ N₁, ?_⟩
    intro m hm' n hn'
    have h0 := hN₀ m (le_trans (le_max_left _ _) hm') n (le_trans (le_max_left _ _) hn')
    have h1 := hN₁ m (le_trans (le_max_right _ _) hm') n (le_trans (le_max_right _ _) hn')
    have hdiff := (hw m).sub (hw n)
    have hmean : meanField (us m a-us n a) = 0 := by rw [map_sub, hm, hm, sub_self]
    have hp := weak_poincare (hdiff 0 a) (hdiff 1 a) hmean
    simp only [map_sub] at hp
    rw [dist_eq_norm] at h0 h1 ⊢
    simp only [Function.comp_apply] at h0 h1
    nlinarith [Real.pi_pos]
  choose u hu using fun a => cauchySeq_tendsto_of_complete (hc a)
  refine ⟨u, HasWeakGradient.limit hw hu hlim, ?_⟩
  intro a
  have hmean := (meanField.continuous.tendsto (u a)).comp (hu a)
  have hzero : Tendsto (fun n => meanField (us n a)) atTop (nhds 0) := by
    simpa only [hm] using (tendsto_const_nhds (x := (0 : ℝ)))
  exact tendsto_nhds_unique hmean hzero

/-- The range of periodic weak gradients is closed. -/
theorem weakGradientSpace_eq_gradientSpace : weakGradientSpace = gradientSpace := by
  apply le_antisymm weakGradientSpace.le_topologicalClosure
  intro g hg
  obtain ⟨u, hu, _⟩ := gradientSpace_exact_potential g hg
  exact ⟨u, hu⟩

theorem weakGradientSpace_isClosed : IsClosed (weakGradientSpace : Set PhysicalField) := by
  rw [weakGradientSpace_eq_gradientSpace]
  exact weakGradientSpace.isClosed_topologicalClosure

/-- A zero-mean potential is uniquely determined by its weak gradient. -/
theorem zeroMean_potential_unique {u v : Fin 16 → ScalarField} {g : PhysicalField}
    (hu : HasWeakGradient u g) (hv : HasWeakGradient v g)
    (hmu : ∀ a, meanField (u a) = 0) (hmv : ∀ a, meanField (v a) = 0) : u = v := by
  funext a
  have hw := hu.sub hv
  have hm : meanField (u a-v a) = 0 := by rw [map_sub, hmu, hmv, sub_self]
  have hp := weak_poincare (hw 0 a) (hw 1 a) hm
  simp only [sub_self, map_zero, norm_zero, add_zero] at hp
  have hn : ‖u a-v a‖ = 0 := by nlinarith [norm_nonneg (u a-v a), Real.pi_pos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Each field in `gradientSpace` has exactly one zero-mean weak potential. -/
theorem gradientSpace_existsUnique_potential (g : PhysicalField) (hg : g ∈ gradientSpace) :
    ∃! u : Fin 16 → ScalarField, HasWeakGradient u g ∧ ∀ a, meanField (u a) = 0 := by
  obtain ⟨u, hu, hm⟩ := gradientSpace_exact_potential g hg
  exact ⟨u, ⟨hu, hm⟩, fun v hv => zeroMean_potential_unique hv.1 hu hv.2 hm⟩

/-- The zero-mean periodic weak potential associated with a closed weak gradient. -/
def exactPotential (g : PhysicalField) (hg : g ∈ gradientSpace) : SobolevPotential where
  potential := Classical.choose (gradientSpace_exact_potential g hg)
  gradient := g
  weakGradient := (Classical.choose_spec (gradientSpace_exact_potential g hg)).1

@[simp] theorem exactPotential_gradient (g : PhysicalField) (hg : g ∈ gradientSpace) :
    (exactPotential g hg).gradient = g := rfl

theorem exactPotential_mean_zero (g : PhysicalField) (hg : g ∈ gradientSpace) (a : Fin 16) :
    meanField ((exactPotential g hg).potential a) = 0 :=
  (Classical.choose_spec (gradientSpace_exact_potential g hg)).2 a

/-- The recovered potential satisfies the componentwise Poincaré bound. -/
theorem exactPotential_norm_bound (g : PhysicalField) (hg : g ∈ gradientSpace) (a : Fin 16) :
    2 * Real.pi * ‖(exactPotential g hg).potential a‖ ≤
      ‖componentField 0 a g‖ + ‖componentField 1 a g‖ :=
  weak_poincare ((exactPotential g hg).weakGradient 0 a)
    ((exactPotential g hg).weakGradient 1 a) (exactPotential_mean_zero g hg a)

/-- The zero-mean periodic weak H¹ potential of the coercive cell solver's
correction at the prescribed constant loading `F`. -/
def cellPotential (A : PhysicalField →L[ℝ] PhysicalField) (mu : ℝ)
    (hmu : 0 < mu) (hA : CoerciveLaw A mu) (F : PhysicalGradient) : SobolevPotential :=
  exactPotential (correction gradientSpace A mu hmu hA (constantField F))
    (correction gradientSpace A mu hmu hA (constantField F)).property

theorem cellPotential_mean_zero (A : PhysicalField →L[ℝ] PhysicalField) (mu : ℝ)
    (hmu : 0 < mu) (hA : CoerciveLaw A mu) (F : PhysicalGradient) (a : Fin 16) :
    meanField ((cellPotential A mu hmu hA F).potential a) = 0 :=
  exactPotential_mean_zero _ _ a

/-- Adding the recovered gradient to the loading gives the cell field. -/
theorem cellPotential_field (A : PhysicalField →L[ℝ] PhysicalField) (mu : ℝ)
    (hmu : 0 < mu) (hA : CoerciveLaw A mu) (F : PhysicalGradient) :
    constantField F + (cellPotential A mu hmu hA F).gradient =
      cellField gradientSpace A mu hmu hA (constantField F) := rfl

/-- The recovered field has the prescribed mean loading and satisfies weak equilibrium. -/
theorem cellPotential_isCell (A : PhysicalField →L[ℝ] PhysicalField) (mu : ℝ)
    (hmu : 0 < mu) (hA : CoerciveLaw A mu) (F : PhysicalGradient) :
    IsCellField gradientSpace A (constantField F)
      (constantField F+(cellPotential A mu hmu hA F).gradient) := by
  rw [cellPotential_field]
  exact cellField_isCellField _ _ _ _ _ _

/-- The Sobolev infimum is the energy of a minimizing weak H¹ potential. -/
theorem cellPotential_energy (A : PhysicalField →L[ℝ] PhysicalField)
    (hAs : SymmetricLaw A) (mu : ℝ) (hmu : 0 < mu) (hA : CoerciveLaw A mu)
    (F : PhysicalGradient) :
    fieldEnergy A F (cellPotential A mu hmu hA F).gradient = sobolevCellEnergy A F := by
  rw [sobolevCellEnergy_eq_weakCellEnergy,
    weakCellEnergy_eq_closedMinimum A hAs mu hmu hA F]
  rfl

/-- For a symmetric coercive law, the recovered potential minimizes energy
among all periodic weak H¹ competitors. Competitors need not be centered. -/
theorem cellPotential_minimizes (A : PhysicalField →L[ℝ] PhysicalField)
    (hAs : SymmetricLaw A) (mu : ℝ) (hmu : 0 < mu) (hA : CoerciveLaw A mu)
    (F : PhysicalGradient) (v : SobolevPotential) :
    fieldEnergy A F (cellPotential A mu hmu hA F).gradient ≤ fieldEnergy A F v.gradient := by
  apply cell_energy_minimal hAs hmu.le hA (cellPotential_isCell A mu hmu hA F)
  simpa only [add_sub_cancel_left] using weakGradient_mem_gradientSpace v

/-- The periodic weak-Sobolev cell energy is an attained minimum. -/
theorem sobolevCellEnergy_isLeast (A : PhysicalField →L[ℝ] PhysicalField)
    (hAs : SymmetricLaw A) (mu : ℝ) (hmu : 0 < mu) (hA : CoerciveLaw A mu)
    (F : PhysicalGradient) :
    IsLeast (Set.range fun v : SobolevPotential => fieldEnergy A F v.gradient)
      (sobolevCellEnergy A F) := by
  refine ⟨⟨cellPotential A mu hmu hA F, cellPotential_energy A hAs mu hmu hA F⟩, ?_⟩
  rintro E ⟨v, rfl⟩
  rw [← cellPotential_energy A hAs mu hmu hA F]
  exact cellPotential_minimizes A hAs mu hmu hA F v

/-- The mean flux of the recovered cell field is the effective operator applied to `F`. -/
theorem cellPotential_mean_flux (A : PhysicalField →L[ℝ] PhysicalField) (mu : ℝ)
    (hmu : 0 < mu) (hA : CoerciveLaw A mu) (F : PhysicalGradient) :
    meanField (A (constantField F+(cellPotential A mu hmu hA F).gradient)) =
      periodicEffective A mu hmu hA F := rfl

/-- Every zero-mean weak H¹ energy minimizer equals the cell potential. -/
theorem cellPotential_unique (A : PhysicalField →L[ℝ] PhysicalField)
    (hAs : SymmetricLaw A) (mu : ℝ) (hmu : 0 < mu) (hA : CoerciveLaw A mu)
    (F : PhysicalGradient) (v : SobolevPotential)
    (hm : ∀ a, meanField (v.potential a) = 0)
    (hmin : fieldEnergy A F v.gradient = sobolevCellEnergy A F) :
    v.potential = (cellPotential A mu hmu hA F).potential := by
  let u := cellPotential A mu hmu hA F
  let e := constantField F+u.gradient
  let ev := constantField F+v.gradient
  have he : IsCellField gradientSpace A (constantField F) e := cellPotential_isCell A mu hmu hA F
  have hv : ev-constantField F ∈ gradientSpace := by
    simpa only [ev, add_sub_cancel_left] using weakGradient_mem_gradientSpace v
  have hinc := cell_energy_increment hAs he hv
  have henergy : inner ℝ (A ev) ev = inner ℝ (A e) e := by
    change fieldEnergy A F v.gradient = fieldEnergy A F u.gradient
    rw [hmin, cellPotential_energy A hAs mu hmu hA F]
  have hz : inner ℝ (A (ev-e)) (ev-e) = 0 := by linarith
  have hco := hA (ev-e)
  rw [hz] at hco
  have hn : ‖ev-e‖ = 0 := by
    by_contra hn
    have hp := lt_of_le_of_ne (norm_nonneg (ev-e)) (Ne.symm hn)
    exact (not_lt_of_ge hco) (mul_pos (mul_pos hmu hp) hp)
  have hgrad : v.gradient = u.gradient := by
    have hh := norm_eq_zero.mp hn
    have hh' : constantField F+v.gradient = constantField F+u.gradient := sub_eq_zero.mp hh
    exact add_left_cancel hh'
  exact zeroMean_potential_unique (hgrad ▸ v.weakGradient) u.weakGradient hm
    (cellPotential_mean_zero A mu hmu hA F)

end HierarchicalLaminates.Periodic
