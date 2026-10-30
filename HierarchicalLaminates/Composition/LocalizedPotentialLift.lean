module

public import HierarchicalLaminates.Composition.SlabCutoff

/-! Continuous gluing of families that vanish near the circle seam. -/

@[expose] public section
noncomputable section

namespace HierarchicalLaminates.Composition

open HierarchicalLaminates HierarchicalLaminates.Periodic HierarchicalLaminates.Binary HierarchicalLaminates.Homogenization
open Set Filter
open scoped Topology

theorem circleRepresentative_mem (y : UnitAddCircle) :
    circleRepresentative y ∈ Ico (0 : ℝ) 1 := by
  simpa [circleRepresentative] using (AddCircle.equivIco 1 0 y).2

theorem circleRepresentative_quotient (y : UnitAddCircle) :
    (circleRepresentative y : UnitAddCircle) = y :=
  AddCircle.coe_equivIco

theorem circleRepresentative_zero : circleRepresentative (0 : UnitAddCircle) = 0 := by
  simpa using circleRepresentative_coe (by norm_num : (0 : ℝ) ∈ Ico (0 : ℝ) 1)

theorem continuousAt_circleRepresentative {y : UnitAddCircle} (hy : y ≠ 0) :
    ContinuousAt circleRepresentative y := by
  exact continuousAt_subtype_val.comp (by
    simpa using AddCircle.continuousAt_equivIco (1 : ℝ) (0 : ℝ) hy)

theorem circleRepresentative_pos {y : UnitAddCircle} (hy : y ≠ 0) :
    0 < circleRepresentative y := by
  apply lt_of_le_of_ne (circleRepresentative_mem y).1
  intro h
  apply hy
  rw [← circleRepresentative_quotient y, ← h]
  rfl

theorem eventually_circleRepresentative_outside {l u : ℝ} (hl : 0 < l) (hu : u < 1) :
    ∀ᶠ y : UnitAddCircle in 𝓝 0, circleRepresentative y ∉ Icc l u := by
  let S : Set UnitAddCircle := (fun x : ℝ => (x : UnitAddCircle)) '' Icc l u
  have hclosed : IsClosed S :=
    (isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed
  have hzero : (0 : UnitAddCircle) ∉ S := by
    rintro ⟨x, hx, hxeq⟩
    have hxmem : x ∈ Ico (0 : ℝ) (0 + 1) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h0mem : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have heq : x = 0 := (AddCircle.coe_eq_coe_iff_of_mem_Ico hxmem h0mem).mp hxeq
    linarith [hx.1]
  filter_upwards [hclosed.isOpen_compl.mem_nhds hzero] with y hy
  intro hrep
  exact hy ⟨circleRepresentative y, hrep, circleRepresentative_quotient y⟩

def liftSlabFamily {E : Type*} (f : UnitAddCircle → ℝ → E) (q : Domain) : E :=
  f (q 0) (circleRepresentative (q 1))

theorem liftSlabFamily_eventually_zero {E : Type*} [Zero E]
    {f : UnitAddCircle → ℝ → E} {l u : ℝ} (hl : 0 < l) (hu : u < 1)
    (hfzero : ∀ x y, y ∉ Icc l u → f x y = 0)
    {q : Domain} (hq : q 1 = 0) :
    liftSlabFamily f =ᶠ[𝓝 q] fun _ => 0 := by
  have ht : Tendsto (fun p : Domain => p 1) (𝓝 q) (𝓝 (0 : UnitAddCircle)) := by
    rw [← hq]
    exact (continuous_apply 1 : Continuous (fun p : Domain => p 1)).continuousAt
  filter_upwards [ht.eventually (eventually_circleRepresentative_outside hl hu)] with p hp
  exact hfzero _ _ hp

theorem liftSlabFamily_continuous {E : Type*} [TopologicalSpace E] [Zero E]
    {f : UnitAddCircle → ℝ → E} {l u : ℝ} (hl : 0 < l) (hu : u < 1)
    (hf : Continuous (Function.uncurry f))
    (hfzero : ∀ x y, y ∉ Icc l u → f x y = 0) :
    Continuous (liftSlabFamily f) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hq : q 1 = 0
  · exact continuousAt_const.congr_of_eventuallyEq
      (liftSlabFamily_eventually_zero hl hu hfzero hq)
  · have hx : ContinuousAt (fun p : Domain => p 0) q := (continuous_apply 0).continuousAt
    have hy : ContinuousAt (fun p : Domain => circleRepresentative (p 1)) q :=
      (continuousAt_circleRepresentative hq).comp (f := fun p : Domain => p 1) (x := q)
        (show ContinuousAt (fun p : Domain => p 1) q from (continuous_apply 1).continuousAt)
    exact hf.continuousAt.comp (hx.prodMk hy)

theorem coordinateRepresentative_eq_circleRepresentative (i : Fin 2) (q : Domain) :
    coordinateRepresentative i q = circleRepresentative (q i) := rfl

theorem coordinateFlow_eval (i j : Fin 2) (q : Domain) (s : ℝ) :
    coordinateFlow i q s j = q j + if j = i then (s : UnitAddCircle) else 0 := by
  simp [coordinateFlow, Pi.single_apply]

theorem circleRepresentative_flow_eventually {q : Domain} (hq : q 1 ≠ 0) :
    (fun s : ℝ => circleRepresentative (coordinateFlow 1 q s 1)) =ᶠ[𝓝 0]
      (fun s => circleRepresentative (q 1) + s) := by
  have hz₀ := circleRepresentative_pos hq
  have hz₁ := (circleRepresentative_mem (q 1)).2
  have hcont : Continuous (fun s : ℝ => circleRepresentative (q 1) + s) := by fun_prop
  have hev : ∀ᶠ s : ℝ in 𝓝 0,
      circleRepresentative (q 1) + s ∈ Ioo (0 : ℝ) 1 :=
    hcont.continuousAt (isOpen_Ioo.mem_nhds (by simpa using And.intro hz₀ hz₁))
  filter_upwards [hev] with s hs
  have heq : coordinateFlow 1 q s 1 =
      ((circleRepresentative (q 1) + s : ℝ) : UnitAddCircle) := by
    rw [coordinateFlow_eval]
    simp only [ite_true, AddCircle.coe_add, circleRepresentative_quotient]
  rw [heq]
  exact circleRepresentative_coe (Ioo_subset_Ico_self hs)

end HierarchicalLaminates.Composition
