import TakhtajanTeo.Ch1.TCurveTopGroup
import TakhtajanTeo.Appendix.AppACor2

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- On the exterior, normalized sphere welding depends only on the class. -/
theorem tcg_welding_congr {μ ν : LinfStarBall} (h : teichSetoid μ ν) :
    EqOn (normalizedWeldingSphere μ) (normalizedWeldingSphere ν) extDiscExterior := by
  have hw := weldingPrime_congr_h (fun z hz => h z hz) (normalizedWeldingPrime_actual μ.2)
  have he := (conformal_welding_prime_unique (tmi_wA_oneFixed ν.2)
    hw (normalizedWeldingPrime_actual ν.2)).2
  intro p hp
  induction p using OnePoint.rec with
  | infty => rw [normalizedWeldingSphere_infty μ.2, normalizedWeldingSphere_infty ν.2]
  | coe z =>
    have hz : z ∈ unitDiscExterior := by simpa [extDiscExterior, toExt] using hp
    rw [← normalizedWeldingExterior_coe μ.2, ← normalizedWeldingExterior_coe ν.2]
    exact congrArg (fun x : ℂ => (x : ExtPlane)) (he hz)

/-- Changing the representative leaves the genuine fibre parameter unchanged. -/
theorem tcg_parameter_congr {μ ν : LinfStarBall} (h : teichSetoid μ ν) {z : ExtPlane}
    (hz : z ∈ wB μ '' extDiscExterior) :
    Function.invFun (normalizedWeldingSphere μ) z =
      Function.invFun (normalizedWeldingSphere ν) z := by
  have hu := tcg_parameter_mem μ.2 hz
  apply (normalizedWeldingSphere_bijective ν).1
  rw [← tcg_welding_congr h hu,
    Function.invFun_eq ((normalizedWeldingSphere_bijective μ).2 z),
    Function.invFun_eq ((normalizedWeldingSphere_bijective ν).2 z)]

/-- The boundary datum for the chosen extension is independent of the base representative. -/
theorem tcg_boundary_congr {μ ν : LinfStarBall} (h : teichSetoid μ ν) {w : ExtPlane}
    (hw : w ∈ wB μ '' extDiscExterior) :
    EqOn (fun z : ℂ => finPart
      (sigmaSphere (Function.invFun (normalizedWeldingSphere μ) w) (gammaMu μ z)))
      (fun z : ℂ => finPart
      (sigmaSphere (Function.invFun (normalizedWeldingSphere ν) w) (gammaMu ν z))) unitCircle := by
  intro z hz
  dsimp only
  rw [tcg_parameter_congr h hw, (tce_gamma_circle μ.2 hz).1,
    (tce_gamma_circle ν.2 hz).1, h z hz]

/-- Forgetting the Hilbert refinement, the Bers coordinate is still continuous. -/
theorem tcg_bers_continuous :
    @Continuous T1 (AInf unitDisc) hilbertTopology inferInstance bers := by
  have hi : @Continuous (AInf unitDisc) (AInf unitDisc)
      hilbertTopologyA inferInstance id := continuous_id_iff_le.mpr hilbertTopologyA_spec.1
  exact @Continuous.comp T1 (AInf unitDisc) (AInf unitDisc)
    hilbertTopology hilbertTopologyA inferInstance bers id hi ctb_bers_continuous_hilbert

/-- A continuous local choice of representatives through a prescribed class.
Only the value at the centre is `out p`; no continuity of `Quotient.out` is used. -/
theorem tcg_local_section (p : T1) :
    ∃ s : T1 → LinfStar,
      @ContinuousAt T1 LinfStar hilbertTopology inferInstance s p ∧
      s p = ((Quotient.out p : LinfStarBall) : LinfStar) ∧
      ∀ᶠ q in @nhds T1 hilbertTopology p,
        ∃ h : s q ∈ LinfStarBall, Phi ⟨s q, h⟩ = q := by
  obtain ⟨s, hsc, hs0, hev⟩ := AppA.ac2g_section p
  let _ : TopologicalSpace T1 := hilbertTopology
  refine ⟨s ∘ bers, hsc.comp tcg_bers_continuous.continuousAt, hs0, ?_⟩
  filter_upwards [tcg_bers_continuous.continuousAt.tendsto.eventually hev] with q hq
  obtain ⟨h, he⟩ := hq
  exact ⟨h, bers_injective he⟩

/-- Evaluate inverse sphere welding using any representative of the class. -/
theorem tcg_parameter_eq_rep {p : T1} {μ : LinfStarBall} (hμ : Phi μ = p)
    {w : ExtPlane} (hw : (p, w) ∈ TCurve) :
    Function.invFun (normalizedWeldingSphere (Quotient.out p : LinfStarBall)) w =
      Function.invFun (normalizedWeldingSphere μ) w := by
  have hc : teichSetoid (Quotient.out p : LinfStarBall) μ :=
    Quotient.exact ((Quotient.out_eq p).trans hμ.symm)
  exact tcg_parameter_congr hc hw

/-- The inverse welding family is jointly continuous on the coefficient ball. -/
theorem tcg_parameter_continuous :
    ContinuousOn (fun x : LinfStar × ExtPlane =>
      Function.invFun (normalizedWeldingSphere x.1) x.2) (LinfStarBall ×ˢ univ) := by
  have he : (fun x : LinfStar × ExtPlane =>
      Function.invFun (normalizedWeldingSphere x.1) x.2) =
      (fun x : LinfStar × ExtPlane => wAS x.1 (Function.invFun (wB x.1) x.2)) := by
    funext x
    apply (normalizedWeldingSphere_bijective x.1).1
    rw [Function.invFun_eq ((normalizedWeldingSphere_bijective x.1).2 x.2), AppA.ac2g_right_inv]
  rw [he]
  exact AppA.ac2g_inv_cont

/-- The true exterior parameter is continuous in the Hilbert-product topology. -/
theorem tcg_fibre_parameter_continuous :
    @ContinuousOn (T1 × ExtPlane) ExtPlane
      (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance) inferInstance
      (fun q => Function.invFun (normalizedWeldingSphere (Quotient.out q.1 : LinfStarBall)) q.2)
      TCurve := by
  let _ : TopologicalSpace T1 := hilbertTopology
  intro q hq
  obtain ⟨s, hsc, hs0, hev⟩ := tcg_local_section q.1
  have hc : ContinuousAt (fun x : T1 × ExtPlane => (s x.1, x.2)) q :=
    (hsc.comp continuousAt_fst).prodMk continuousAt_snd
  have hs : s q.1 ∈ LinfStarBall := by rw [hs0]; exact (Quotient.out q.1 : LinfStarBall).2
  have hpar : ContinuousAt (fun x : LinfStar × ExtPlane =>
      Function.invFun (normalizedWeldingSphere x.1) x.2) (s q.1, q.2) :=
    tcg_parameter_continuous.continuousAt
    ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hs, mem_univ q.2⟩)
  have hcomp : ContinuousAt (fun x : T1 × ExtPlane =>
      Function.invFun (normalizedWeldingSphere (s x.1)) x.2) q :=
    hpar.comp (f := fun x : T1 × ExtPlane => (s x.1, x.2)) hc
  have hev' : ∀ᶠ x : T1 × ExtPlane in 𝓝[TCurve] q,
      ∃ h : s x.1 ∈ LinfStarBall, Phi ⟨s x.1, h⟩ = x.1 :=
    (continuousAt_fst.tendsto.eventually hev).filter_mono nhdsWithin_le_nhds
  have heq : (fun x : T1 × ExtPlane =>
      Function.invFun (normalizedWeldingSphere (s x.1)) x.2) =ᶠ[𝓝[TCurve] q]
      (fun x => Function.invFun (normalizedWeldingSphere (Quotient.out x.1 : LinfStarBall)) x.2) := by
    filter_upwards [hev', self_mem_nhdsWithin] with x hx hxT
    obtain ⟨hx, hrep⟩ := hx
    exact (tcg_parameter_eq_rep hrep hxT).symm
  have h0 : Function.invFun (normalizedWeldingSphere (s q.1)) q.2 =
      Function.invFun (normalizedWeldingSphere (Quotient.out q.1 : LinfStarBall)) q.2 := by rw [hs0]
  exact hcomp.continuousWithinAt.congr_of_eventuallyEq heq.symm h0.symm

#print axioms tcg_welding_congr
#print axioms tcg_local_section
#print axioms tcg_fibre_parameter_continuous
end TakhtajanTeo
