import TakhtajanTeo.Ch1.TCurveBaseContinuity

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Descend a class-invariant continuous coefficient family using actual local
Linf sections. There is no continuity hypothesis on the quotient choice. -/
theorem tcg_class_family_continuous {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : LinfStar × Y → Z) {V : Set Y} (hV : IsOpen V)
    (hF : ContinuousOn F (LinfStarBall ×ˢ V))
    (hclass : ∀ (μ ν : LinfStarBall), teichSetoid μ ν →
      ∀ y ∈ V, F ((μ : LinfStar), y) = F ((ν : LinfStar), y))
    (p : X → T1) (y : X → Y)
    (hp : @Continuous X T1 inferInstance hilbertTopology p)
    (hy : Continuous y) (hyV : ∀ x, y x ∈ V) :
    Continuous (fun x => F (((Quotient.out (p x) : LinfStarBall) : LinfStar), y x)) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨s, hs, hs0, hev⟩ := tcg_local_section (p x₀)
  have hsB : s (p x₀) ∈ LinfStarBall := by rw [hs0]; exact (Quotient.out (p x₀) : LinfStarBall).2
  have hFca : ContinuousAt F (s (p x₀), y x₀) :=
    hF.continuousAt ((isOpen_ball.prod hV).mem_nhds ⟨hsB, hyV x₀⟩)
  have hpair : ContinuousAt (fun x : X => (s (p x), y x)) x₀ :=
    (hs.comp (f := p) hp.continuousAt).prodMk hy.continuousAt
  have hc : ContinuousAt (fun x => F (s (p x), y x)) x₀ :=
    hFca.comp (f := fun x : X => (s (p x), y x)) hpair
  have heq : (fun x => F (s (p x), y x)) =ᶠ[𝓝 x₀]
      (fun x => F (((Quotient.out (p x) : LinfStarBall) : LinfStar), y x)) := by
    filter_upwards [hp.continuousAt.tendsto.eventually hev] with x hx
    obtain ⟨hxB, hxp⟩ := hx
    have hrel : teichSetoid (⟨s (p x), hxB⟩ : LinfStarBall) (Quotient.out (p x) : LinfStarBall) :=
      Quotient.exact (hxp.trans (Quotient.out_eq (p x)).symm)
    exact hclass _ _ hrel _ (hyV x)
  exact hc.congr_of_eventuallyEq heq.symm

theorem tcg_exterior_open : IsOpen extDiscExterior := by
  rw [fi_extDiscExterior_eq_compl]
  exact ((isCompact_closedBall (0 : ℂ) 1).image OnePoint.continuous_coe).isClosed.isOpen_compl

theorem tcg_welding_coeff_continuous :
    ContinuousOn (fun x : LinfStar × ExtPlane => normalizedWeldingSphere x.1 x.2)
      (LinfStarBall ×ˢ univ) := by
  exact AppA.acc_wB_cont.comp (f := fun x : LinfStar × ExtPlane =>
    (x.1, Function.invFun (wAS x.1) x.2))
    (continuousOn_fst.prodMk AppA.acc_wAS_inv_cont) (fun x hx => ⟨hx.1, mem_univ _⟩)

/-- Joint continuity of the actual class-based exterior welding evaluation. -/
theorem tcg_welding_class_continuous_family {X : Type*} [TopologicalSpace X]
    (p : X → T1) (y : X → ExtPlane)
    (hp : @Continuous X T1 inferInstance hilbertTopology p)
    (hy : Continuous y) (hyE : ∀ x, y x ∈ extDiscExterior) :
    Continuous (fun x => normalizedWeldingSphere (Quotient.out (p x) : LinfStarBall) (y x)) := by
  apply tcg_class_family_continuous (fun x => normalizedWeldingSphere x.1 x.2)
    tcg_exterior_open (tcg_welding_coeff_continuous.mono (prod_mono Subset.rfl (subset_univ _)))
    _ p y hp hy hyE
  intro μ ν h y hy
  exact tcg_welding_congr h hy

theorem tcg_fB_coeff_continuous :
    ContinuousOn (fun x : LinfStar × ℂ => fB x.1 x.2) (LinfStarBall ×ˢ unitDisc) := by
  intro x hx
  have hw₀ : ContinuousAt (fun y : LinfStar × ExtPlane => wB y.1 y.2) (x.1, (x.2 : ExtPlane)) :=
    AppA.acc_wB_cont.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hx.1, mem_univ _⟩)
  have hw : ContinuousAt (fun x : LinfStar × ℂ => wB x.1 (x.2 : ExtPlane)) x :=
    hw₀.comp
      (f := fun x : LinfStar × ℂ => (x.1, (x.2 : ExtPlane)))
      (continuous_fst.prodMk (OnePoint.continuous_coe.comp continuous_snd)).continuousAt
  have hf : ContinuousAt finPart (wB x.1 (x.2 : ExtPlane)) := by
    rw [wB_disc_eq_fB hx.1 hx.2]
    exact OnePoint.isOpenEmbedding_coe.continuousAt_iff.mp
      (continuousAt_id : ContinuousAt (fun z : ℂ => z) (fB x.1 x.2))
  exact (hf.comp (f := fun x : LinfStar × ℂ => wB x.1 (x.2 : ExtPlane)) hw).continuousWithinAt

/-- The normalized interior map depends continuously on its class and its
interior argument in the Hilbert topology. -/
theorem tcg_fB_class_continuous_family {X : Type*} [TopologicalSpace X]
    (p : X → T1) (z : X → ℂ)
    (hp : @Continuous X T1 inferInstance hilbertTopology p)
    (hz : Continuous z) (hzD : ∀ x, z x ∈ unitDisc) :
    Continuous (fun x => fB (Quotient.out (p x) : LinfStarBall) (z x)) := by
  apply tcg_class_family_continuous (fun x => fB x.1 x.2) (V := unitDisc)
    isOpen_ball tcg_fB_coeff_continuous _ p z hp hz hzD
  intro μ ν h z hz
  exact (modelA_iff_modelB μ ν).mp h z hz

#print axioms tcg_class_family_continuous
#print axioms tcg_welding_class_continuous_family
#print axioms tcg_fB_class_continuous_family
end TakhtajanTeo
