module

public import HierarchicalLaminates.TwoWell.RegularLaminateProfile
public import HierarchicalLaminates.TwoWell.Envelopes
public import HierarchicalLaminates.GClosure.ObliquePullback
public import HierarchicalLaminates.GClosure.DirectionApproximation
public import HierarchicalLaminates.TwoWell.LaminateIntegral

/-!
# Jensen inequalities along integer torus normals

The regular profiles are transported through integer torus coordinates to
produce periodic potential variations. Their bulk gradients and a
vanishing transition error give the two-state Jensen inequality. A continuous
upper obstacle bounds transition values, and the periodic Jensen predicate
supplies integrability of each trial energy.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.TwoWell

open MeasureTheory Set Filter HierarchicalLaminates HierarchicalLaminates.Periodic
  HierarchicalLaminates.Composition HierarchicalLaminates.GClosure
  HierarchicalLaminates.Lamination HierarchicalLaminates.Homogenization

def pairedNormalJump (n : LayerNormal) (z₁ z₂ : Fin 16 → ℝ) : PairedGradient :=
  (normalJump n z₁,normalJump n z₂)

def normalLaminatePotential (R : TorusCoordinates) (a δ : ℝ)
    (hδ : 0 < δ) (hδ₁ : δ < 1) (z : Fin 16 → ℝ) : RegularPotential :=
  transformPotential R.matrix
    (laminatePotential a δ hδ hδ₁ ((coordinateScale R)⁻¹ • z))

theorem normalLaminatePotential_gradient (R : TorusCoordinates) (a δ : ℝ)
    (hδ : 0 < δ) (hδ₁ : δ < 1) (z : Fin 16 → ℝ)
    (q : Domain) (i : Fin 2) (c : Fin 16) :
    (normalLaminatePotential R a δ hδ hδ₁ z).gradient q (i,c) =
      scalarProfileSlope a δ hδ hδ₁ (matrixTorus R.matrix q)*
        normalJump (coordinateNormal R) z (i,c) := by
  rw [normalLaminatePotential,transformPotential_gradient,spatialGradientMap_apply]
  simp only [laminatePotential_gradient,Pi.smul_apply,smul_eq_mul,normalJump,
    coordinateNormal_apply]
  norm_num only [Fin.zero_eta,Fin.isValue,Fin.reduceEq,ite_true,ite_false]
  ring

theorem normalLaminateTrial (R : TorusCoordinates) (F : PairedGradient)
    (a δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ < 1) (z₁ z₂ : Fin 16 → ℝ) (q : Domain) :
    regularTrial F (normalLaminatePotential R a δ hδ hδ₁ z₁)
      (normalLaminatePotential R a δ hδ hδ₁ z₂) q =
        F+scalarProfileSlope a δ hδ hδ₁ (matrixTorus R.matrix q) •
          pairedNormalJump (coordinateNormal R) z₁ z₂ := by
  apply Prod.ext
  · funext c
    exact congrArg (fun r => F.1 c+r) (normalLaminatePotential_gradient R a δ hδ hδ₁ z₁ q c.1 c.2)
  · funext c
    exact congrArg (fun r => F.2 c+r) (normalLaminatePotential_gradient R a δ hδ hδ₁ z₂ q c.1 c.2)

theorem normalLaminateTrial_first (R : TorusCoordinates) (F : PairedGradient)
    {a δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) (ha : a+δ ≤ 1)
    (z₁ z₂ : Fin 16 → ℝ) {q : Domain}
    (hq : circleRepresentative ((matrixTorus R.matrix q) 1) ∈ Icc (2*δ) (a-δ)) :
    regularTrial F (normalLaminatePotential R a δ hδ hδ₁ z₁)
      (normalLaminatePotential R a δ hδ hδ₁ z₂) q =
        F+(1-a) • pairedNormalJump (coordinateNormal R) z₁ z₂ := by
  rw [normalLaminateTrial]
  have hs : scalarProfileSlope a δ hδ hδ₁ (matrixTorus R.matrix q) = 1-a :=
    laminateProfileSlope_first hδ ha hq
  rw [hs]

theorem normalLaminateTrial_second (R : TorusCoordinates) (F : PairedGradient)
    {a δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) (ha : δ ≤ a)
    (z₁ z₂ : Fin 16 → ℝ) {q : Domain}
    (hq : circleRepresentative ((matrixTorus R.matrix q) 1) ∈ Icc (a+δ) (1-2*δ)) :
    regularTrial F (normalLaminatePotential R a δ hδ hδ₁ z₁)
      (normalLaminatePotential R a δ hδ hδ₁ z₂) q =
        F-a • pairedNormalJump (coordinateNormal R) z₁ z₂ := by
  rw [normalLaminateTrial]
  have hs : scalarProfileSlope a δ hδ hδ₁ (matrixTorus R.matrix q) = -a :=
    laminateProfileSlope_second hδ ha hq
  rw [hs,neg_smul]
  rfl

theorem continuous_line_energy_bounded {W : PairedGradient → ℝ} (hW : Continuous W)
    (F J : PairedGradient) (K : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc (-K) K, W (F+s • J) ≤ M := by
  let f : C(Icc (-K) K,ℝ) := ⟨fun s => W (F+(s : ℝ) • J),
    hW.comp (continuous_const.add (continuous_subtype_val.smul continuous_const))⟩
  refine ⟨‖f‖,norm_nonneg _,?_⟩
  intro s hs
  exact (le_abs_self _).trans (f.norm_coe_le_norm ⟨s,hs⟩)

def torusCoordinateHomeomorph (R : TorusCoordinates) : Domain ≃ₜ Domain where
  toEquiv := R.equiv.toEquiv
  continuous_toFun := R.continuous
  continuous_invFun := R.continuous_symm

theorem torusCoordinate_integrable_iff (R : TorusCoordinates) (g : Domain → ℝ) :
    Integrable (fun q => g (matrixTorus R.matrix q)) domainMeasure ↔
      Integrable g domainMeasure :=
  R.measurePreserving.integrable_comp_emb (torusCoordinateHomeomorph R).measurableEmbedding

theorem torusCoordinate_integral (R : TorusCoordinates) (g : Domain → ℝ) :
    (∫ q, g (matrixTorus R.matrix q) ∂domainMeasure) = ∫ q, g q ∂domainMeasure :=
  R.measurePreserving.integral_comp (torusCoordinateHomeomorph R).measurableEmbedding g

theorem PeriodicQuasiconvex.coordinateNormal_estimate
    {h W : PairedGradient → ℝ} (hh : PeriodicQuasiconvex h)
    (hle : ∀ F, h F ≤ W F) (R : TorusCoordinates) (F : PairedGradient)
    (z₁ z₂ : Fin 16 → ℝ) {a δ C M : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hδ : 0 < δ) (hδa : 3*δ ≤ a) (hδb : a+3*δ ≤ 1)
    (hC : 0 ≤ C) (hbound : ∀ y, |deriv Real.smoothTransition y| ≤ C)
    (hM : 0 ≤ M)
    (hMb : ∀ s ∈ Icc (-(4*C+1)) (4*C+1),
      W (F+s • pairedNormalJump (coordinateNormal R) z₁ z₂) ≤ M) :
    h F ≤ a*h (F+(1-a) • pairedNormalJump (coordinateNormal R) z₁ z₂)+
      (1-a)*h (F-a • pairedNormalJump (coordinateNormal R) z₁ z₂)+
      6*δ*(M+|h (F+(1-a) • pairedNormalJump (coordinateNormal R) z₁ z₂)|+
        |h (F-a • pairedNormalJump (coordinateNormal R) z₁ z₂)|) := by
  have hδ₁ : δ < 1 := by linarith [ha.2]
  let J := pairedNormalJump (coordinateNormal R) z₁ z₂
  let g : Domain → ℝ := fun q => h (F+scalarProfileSlope a δ hδ hδ₁ q • J)
  have hq := hh F (normalLaminatePotential R a δ hδ hδ₁ z₁)
    (normalLaminatePotential R a δ hδ hδ₁ z₂)
  have heq : (fun q => h (regularTrial F (normalLaminatePotential R a δ hδ hδ₁ z₁)
      (normalLaminatePotential R a δ hδ hδ₁ z₂) q)) = fun q => g (matrixTorus R.matrix q) := by
    funext q
    rw [normalLaminateTrial]
  rw [heq] at hq
  have hgi := (torusCoordinate_integrable_iff R g).1 hq.1
  rw [torusCoordinate_integral] at hq
  apply hq.2.trans
  apply laminate_integral_upper hδ hδa hδb hM g hgi
  · intro q
    exact (hle _).trans (hMb _ (abs_le.mp
      (scalarProfileSlope_uniform_bound ha hδ hδ₁ hδa hδb hC hbound q)))
  · intro q hq₀ hq₁
    have hs : scalarProfileSlope a δ hδ hδ₁ q = 1-a :=
      laminateProfileSlope_first hδ (by linarith) ⟨hq₀,hq₁⟩
    simp only [g,J,hs]
  · intro q hq₀ hq₁
    have hs : scalarProfileSlope a δ hδ hδ₁ q = -a :=
      laminateProfileSlope_second hδ (by linarith) ⟨hq₀,hq₁⟩
    simp only [g,J,hs,neg_smul,sub_eq_add_neg]

theorem PeriodicQuasiconvex.coordinateNormal_jensen
    {h W : PairedGradient → ℝ} (hh : PeriodicQuasiconvex h)
    (hW : Continuous W) (hle : ∀ F, h F ≤ W F)
    (R : TorusCoordinates) (F : PairedGradient) (z₁ z₂ : Fin 16 → ℝ)
    (a : LayerProportion) :
    h F ≤ (a : ℝ)*h (F+(1-(a : ℝ)) • pairedNormalJump (coordinateNormal R) z₁ z₂)+
      (1-(a : ℝ))*h (F-(a : ℝ) • pairedNormalJump (coordinateNormal R) z₁ z₂) := by
  by_cases ha₀ : (a : ℝ) = 0
  · simp [ha₀]
  by_cases ha₁ : (a : ℝ) = 1
  · simp [ha₁]
  have ha₀' : 0 < (a : ℝ) := lt_of_le_of_ne a.property.1 (Ne.symm ha₀)
  have ha₁' : (a : ℝ) < 1 := lt_of_le_of_ne a.property.2 ha₁
  obtain ⟨C,hC,hCb⟩ := smoothTransition_derivative_bounded
  obtain ⟨M,hM,hMb⟩ := continuous_line_energy_bounded hW F
    (pairedNormalJump (coordinateNormal R) z₁ z₂) (4*C+1)
  let d : ℝ := min (a : ℝ) (1-(a : ℝ))/6
  have hd : 0 < d := div_pos (lt_min ha₀' (sub_pos.mpr ha₁')) (by norm_num)
  have hd₁ : 6*d ≤ (a : ℝ) := by
    dsimp [d]
    linarith [min_le_left (a : ℝ) (1-(a : ℝ))]
  have hd₂ : (a : ℝ)+6*d ≤ 1 := by
    dsimp [d]
    linarith [min_le_right (a : ℝ) (1-(a : ℝ))]
  let A := h (F+(1-(a : ℝ)) • pairedNormalJump (coordinateNormal R) z₁ z₂)
  let B := h (F-(a : ℝ) • pairedNormalJump (coordinateNormal R) z₁ z₂)
  have hn (n : ℕ) : 0 < (n : ℝ)+1 := by positivity
  have hi (n : ℕ) :
      h F ≤ (a : ℝ)*A+(1-(a : ℝ))*B+6*(d/((n : ℝ)+1))*(M+|A|+|B|) := by
    have hdn : d/((n : ℝ)+1) ≤ d := div_le_self hd.le (by
      have hn₀ := Nat.cast_nonneg (α := ℝ) n
      linarith)
    exact hh.coordinateNormal_estimate hle R F z₁ z₂ a.property
      (div_pos hd (hn n)) (by linarith) (by linarith) hC hCb hM hMb
  have hseq : Tendsto (fun n : ℕ => d/((n : ℝ)+1)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,one_div,mul_zero,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul d
  have hlim : Tendsto (fun n : ℕ => (a : ℝ)*A+(1-(a : ℝ))*B+
      6*(d/((n : ℝ)+1))*(M+|A|+|B|)) atTop
      (nhds ((a : ℝ)*A+(1-(a : ℝ))*B)) := by
    simpa only [mul_zero,zero_mul,add_zero] using
      tendsto_const_nhds.add ((hseq.const_mul 6).mul_const (M+|A|+|B|))
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hi)

end HierarchicalLaminates.TwoWell
