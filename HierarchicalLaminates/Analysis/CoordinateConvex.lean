module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Continuity from convexity in each coordinate and a local bound

For a real-valued function on a finite product of copies of `ℝ`, a uniform
absolute bound and convexity in each coordinate give a Lipschitz estimate on
a smaller box. The proof telescopes scalar convexity estimates through the
finitely many coordinates.

Local absolute boundedness therefore gives joint continuity. In particular,
a nonnegative coordinate-convex function below a continuous function is
jointly continuous. The balls below use the finite product's supremum metric.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace HierarchicalLaminates.Analysis

open Set Metric Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def coordinateMix (s : Finset ι) (x y : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ s then y i else x i

/-- An absolute bound on the radius-`R` box gives a Lipschitz bound on the
concentric radius-`R / 2` box, for `R > 0`. -/
theorem coordinateConvex_lipschitzOn_ball {f : (ι → ℝ) → ℝ}
    (hcoord : ∀ x i,ConvexOn ℝ univ (fun t : ℝ => f (Function.update x i t)))
    (c : ι → ℝ) {R M : ℝ} (hR : 0 < R)
    (hbound : ∀ x ∈ ball c R,|f x| ≤ M) :
    ∃ K : NNReal,LipschitzOnWith K f (ball c (R/2)) := by
  classical
  let K : NNReal := (2*M/(R/2)).toNNReal
  have hhalf : 0 < R/2 := half_pos hR
  have hslice (z : ι → ℝ) (hz : z ∈ ball c (R/2)) (i : ι) :
      LipschitzOnWith K (fun t : ℝ => f (Function.update z i t)) (ball (c i) (R/2)) := by
    have hup (t : ℝ) (ht : t ∈ ball (c i) R) : Function.update z i t ∈ ball c R := by
      apply (dist_pi_lt_iff hR).2
      intro j
      by_cases hji : j = i
      · subst j
        simpa using ht
      · rw [Function.update_of_ne hji]
        exact ((dist_pi_lt_iff hhalf).1 hz j).trans (by linarith)
    have hc := (hcoord z i).subset (subset_univ (ball (c i) R)) (convex_ball (c i) R)
    have hl := hc.lipschitzOnWith_of_abs_le hhalf (fun t ht => hbound _ (hup t ht))
    simpa only [show R-R/2 = R/2 by ring] using hl
  refine ⟨_,LipschitzOnWith.of_dist_le' (K := (Fintype.card ι : ℝ)*(K : ℝ)) ?_⟩
  intro x hx y hy
  have hmix (s : Finset ι) : coordinateMix s x y ∈ ball c (R/2) := by
    apply (dist_pi_lt_iff hhalf).2
    intro i
    by_cases hi : i ∈ s
    · simpa [coordinateMix,hi] using (dist_pi_lt_iff hhalf).1 hy i
    · simpa [coordinateMix,hi] using (dist_pi_lt_iff hhalf).1 hx i
  have htel (s : Finset ι) :
      dist (f (coordinateMix s x y)) (f x) ≤ ∑ i ∈ s,(K : ℝ)*dist (y i) (x i) := by
    induction s using Finset.induction_on with
    | empty =>
      have he : coordinateMix ∅ x y = x := by
        funext i
        change (if i ∈ (∅ : Finset ι) then y i else x i) = x i
        simp
      rw [he]
      simp
    | @insert i s hi ih =>
      have hnew : coordinateMix (insert i s) x y = Function.update (coordinateMix s x y) i (y i) := by
        ext j
        by_cases hji : j = i
        · subst j; simp [coordinateMix]
        · simp [coordinateMix,hji]
      have hold : Function.update (coordinateMix s x y) i (x i) = coordinateMix s x y := by
        have hxi : coordinateMix s x y i = x i := by simp [coordinateMix,hi]
        rw [← hxi]
        exact Function.update_eq_self i _
      have hs := (hslice (coordinateMix s x y) (hmix s) i).dist_le_mul
        (y i) ((dist_pi_lt_iff hhalf).1 hy i) (x i) ((dist_pi_lt_iff hhalf).1 hx i)
      rw [hold,← hnew] at hs
      calc
        dist (f (coordinateMix (insert i s) x y)) (f x) ≤
            dist (f (coordinateMix (insert i s) x y)) (f (coordinateMix s x y)) +
              dist (f (coordinateMix s x y)) (f x) := dist_triangle _ _ _
        _ ≤ (K : ℝ)*dist (y i) (x i)+∑ j ∈ s,(K : ℝ)*dist (y j) (x j) := add_le_add hs ih
        _ = _ := by rw [Finset.sum_insert hi]
  rw [dist_comm (f x) (f y),dist_comm x y]
  calc
    dist (f y) (f x) ≤ ∑ i : ι,(K : ℝ)*dist (y i) (x i) := by
      have he : coordinateMix Finset.univ x y = y := by
        funext i
        change (if i ∈ (Finset.univ : Finset ι) then y i else x i) = y i
        simp
      simpa only [he] using htel Finset.univ
    _ ≤ ∑ _i : ι,(K : ℝ)*dist y x := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (dist_le_pi_dist y x i) K.coe_nonneg)
    _ = (Fintype.card ι : ℝ)*(K : ℝ)*dist y x := by simp [Finset.sum_const,nsmul_eq_mul,mul_assoc]

/-- Joint continuity for coordinate-convex functions with locally bounded absolute value. -/
theorem continuous_of_coordinateConvex_of_locally_abs_bounded {f : (ι → ℝ) → ℝ}
    (hcoord : ∀ x i,ConvexOn ℝ univ (fun t : ℝ => f (Function.update x i t)))
    (hbound : ∀ c,∃ R : ℝ,0 < R ∧ ∃ M : ℝ,∀ x ∈ ball c R,|f x| ≤ M) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro c
  obtain ⟨R,hR,M,hM⟩ := hbound c
  obtain ⟨K,hK⟩ := coordinateConvex_lipschitzOn_ball hcoord c hR hM
  exact hK.continuousOn.continuousAt (ball_mem_nhds c (half_pos hR))

/-- A nonnegative coordinate-convex function below a continuous upper bound
is jointly continuous. -/
theorem continuous_of_coordinateConvex_of_nonneg_le {f W : (ι → ℝ) → ℝ}
    (hcoord : ∀ x i,ConvexOn ℝ univ (fun t : ℝ => f (Function.update x i t)))
    (hzero : ∀ x,0 ≤ f x) (hW : Continuous W) (hle : ∀ x,f x ≤ W x) :
    Continuous f := by
  apply continuous_of_coordinateConvex_of_locally_abs_bounded hcoord
  intro c
  have he : ∀ᶠ x in 𝓝 c,W x < W c+1 :=
    hW.continuousAt.eventually (eventually_lt_nhds (by linarith : W c < W c+1))
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨R,hR,|W c|+1,?_⟩
  intro x hx
  rw [abs_of_nonneg (hzero x)]
  exact (hle x).trans ((hball hx).le.trans (by linarith [le_abs_self (W c)]))

end HierarchicalLaminates.Analysis
