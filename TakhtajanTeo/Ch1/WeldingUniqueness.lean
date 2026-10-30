import TakhtajanTeo.Ch1.ActualWelding
import LiZhongQC.ClusterSets
/-! # Exterior boundary uniqueness and the choice-based welding function

Schwarz reflection and the identity theorem give exterior uniqueness from
circle values. Consequently `gMu` equals the constructed exterior map, with
the exact sphere-valued inverse factorization.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem exterior_zero_of_circle_zero {h : ℂ → ℂ} (hc : Continuous h)
    (hd : DifferentiableOn ℂ h unitDiscExterior)
    (hb : ∀ z ∈ sphere (0 : ℂ) 1, h z = 0) : EqOn h 0 unitDiscExterior := by
  let U : Set ℂ := {0}ᶜ
  let v : ℂ → ℂ := fun z => h z⁻¹
  have hU : IsOpen U := isOpen_compl_singleton
  have hSU : sphere (0 : ℂ) 1 ⊆ U := by
    intro z hz
    exact norm_ne_zero_iff.mp (by rw [mem_sphere_zero_iff_norm.mp hz]; exact one_ne_zero)
  have hUA : IsCircleSymmetricNbhd U (sphere (0 : ℂ) 1) := by
    refine ⟨hU, inter_eq_right.mpr hSU, ?_⟩
    intro z hz
    change circleReflect z ≠ 0
    rw [circleReflect]
    have hz0 : z ≠ 0 := hz
    exact one_div_ne_zero (by simpa using hz0)
  have hvc : ContinuousOn v U := by
    intro z hz
    exact (hc.continuousAt.comp (continuousAt_inv₀ (show z ≠ 0 from hz))).continuousWithinAt
  have hvd : DifferentiableOn ℂ v (U ∩ unitDisc) := by
    intro z hz
    have hz0 : z ≠ 0 := hz.1
    have hext : z⁻¹ ∈ unitDiscExterior := by
      change 1 < ‖z⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr (mem_ball_zero_iff.mp hz.2)
    exact ((hd.differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hext)).comp z
      (differentiableAt_id.inv hz0)).differentiableWithinAt
  have hvzero : ∀ z ∈ sphere (0 : ℂ) 1, v z = 0 := by
    intro z hz
    apply hb
    rw [mem_sphere_zero_iff_norm, norm_inv, mem_sphere_zero_iff_norm.mp hz, inv_one]
  obtain ⟨F, hFd, he⟩ := schwarz_reflection_arc_real hUA hvd
    (hvc.mono (union_subset inter_subset_left hSU))
    (fun z hz => by rw [hvzero z hz]; simp)
  have hdense : Dense ({0}ᶜ : Set ℂ) := Set.Countable.dense_compl ℂ (countable_singleton 0)
  have hsub : unitDisc ⊆ closure (U ∩ unitDisc) := by
    simpa only [U, inter_comm] using hdense.open_subset_closure_inter (show IsOpen unitDisc from isOpen_ball)
  have hcl : closedBall (0 : ℂ) 1 ⊆ closure (U ∩ unitDisc) := by
    rw [← closure_ball (0 : ℂ) one_ne_zero]
    exact closure_minimal hsub isClosed_closure
  have hecl : EqOn F v (U ∩ closedBall (0 : ℂ) 1) :=
    he.of_subset_closure (hFd.continuousOn.mono inter_subset_left) (hvc.mono inter_subset_left)
      (fun z hz => ⟨hz.1, ball_subset_closedBall hz.2⟩) (fun z hz => hcl hz.2)
  have hFzeroCircle : ∀ z ∈ sphere (0 : ℂ) 1, F z = 0 := by
    intro z hz
    exact (hecl ⟨hSU hz, mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp hz).le⟩).trans
      (hvzero z hz)
  obtain ⟨ξ, hξi, hξn⟩ := exists_boundaryPole_family
  have hInf : (sphere (0 : ℂ) 1).Infinite :=
    (Set.infinite_range_of_injective hξi).mono (by
      rintro _ ⟨t, rfl⟩
      exact mem_sphere_zero_iff_norm.mpr (hξn t))
  obtain ⟨p, hp, hacc⟩ := hInf.exists_accPt_of_subset_isCompact (isCompact_sphere (0 : ℂ) 1) Subset.rfl
  have hpcl : p ∈ closure (sphere (0 : ℂ) 1 \ {p}) :=
    mem_closure_iff_clusterPt.mpr (accPt_principal_iff_clusterPt.mp hacc)
  have hconn : IsPreconnected U :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp [rank_real_complex]) (0 : ℂ)).isPreconnected
  have hzsub : sphere (0 : ℂ) 1 \ {p} ⊆ {z : ℂ | F z = 0} \ {p} :=
    fun z hz => ⟨hFzeroCircle z hz.1, hz.2⟩
  have hFzero : EqOn F 0 U := (hFd.analyticOnNhd hU).eqOn_zero_of_preconnected_of_mem_closure
    hconn (hSU hp) (closure_mono hzsub hpcl)
  intro z hz
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hu : z⁻¹ ∈ U ∩ unitDisc := ⟨inv_ne_zero hz0,
    mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1)⟩
  have hzero := hFzero hu.1
  rw [he hu] at hzero
  simpa only [v, inv_inv, Pi.zero_apply] using hzero

theorem exterior_eq_of_circle_eq {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfd : DifferentiableOn ℂ f unitDiscExterior) (hgd : DifferentiableOn ℂ g unitDiscExterior)
    (he : EqOn f g (sphere (0 : ℂ) 1)) : EqOn f g unitDiscExterior := by
  have h := exterior_zero_of_circle_zero (hf.sub hg) (hfd.sub hgd)
    (fun z hz => sub_eq_zero.mpr (he hz))
  intro z hz
  exact sub_eq_zero.mp (h hz)

theorem gMu_eq_normalizedWeldingExterior {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    EqOn (gMu μ) (normalizedWeldingExterior μ) unitDiscExterior := by
  obtain ⟨hα, ⟨F, G, ⟨KF, hKF⟩, hFs, hFf, ⟨KG, hKG⟩, hGs, hGg, hboundary⟩,
    hfd, hfi, hf0, hf1, hgi⟩ := gMu_isWelding hμ
  obtain ⟨F0, ⟨K0, hK0⟩, hF0s, hF0f⟩ := fB_hasQCExtension_closed hμ
  have hFc : Continuous F := continuousOn_univ.mp hKF.2.2.1.1
  have hGc : Continuous G := continuousOn_univ.mp hKG.2.2.1.1
  have hF0c : Continuous F0 := continuousOn_univ.mp hK0.2.2.1.1
  have heF : EqOn F F0 unitDisc := fun z hz => (hFf hz).trans (hF0f (ball_subset_closedBall hz)).symm
  have hFbound : ∀ z ∈ unitCircle, F z = fB μ z := by
    intro z hz
    have hzcl : z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr (show ‖z‖ = 1 from hz).le
    have hcl := heF.closure hFc hF0c
    rw [unitDisc, closure_ball _ one_ne_zero] at hcl
    exact (hcl hzcl).trans (hF0f hzcl)
  have hGbound : EqOn G (normalizedWeldingExterior μ) (sphere (0 : ℂ) 1) := by
    intro u hu
    have huC : u ∈ unitCircle := mem_sphere_zero_iff_norm.mp hu
    have hu' : (u : ExtPlane) ∈ wAS μ '' toExt unitCircle := by
      rw [(wA_mapsTo hμ).2.2]
      exact ⟨u, huC, rfl⟩
    obtain ⟨_, ⟨z, hz, rfl⟩, hzu⟩ := hu'
    have hAz : wA μ z = u := by unfold wA; rw [hzu]; rfl
    have hb := hboundary z hz
    rw [alphaMu_eq_id] at hb
    change (G (wA μ z) : ExtPlane) = (F z : ExtPlane) at hb
    have hb' := OnePoint.coe_injective hb
    rw [hAz] at hb'
    calc G u = F z := hb'
      _ = fB μ z := hFbound z hz
      _ = normalizedWeldingExterior μ (wA μ z) := (normalizedWeldingExterior_boundary hμ hz).symm
      _ = normalizedWeldingExterior μ u := by rw [hAz]
  have heG := exterior_eq_of_circle_eq hGc (normalizedWeldingExterior_continuous_proper hμ).1
    (hgi.1.congr hGg) (normalizedWeldingExterior_differentiableOn hμ) hGbound
  intro z hz
  exact (hGg hz).symm.trans (heG hz)

theorem gMu_sphere_factorization {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    (gMu μ z : ExtPlane) = wB μ (Function.invFun (wAS μ) (z : ExtPlane)) := by
  rw [gMu_eq_normalizedWeldingExterior hμ hz, normalizedWeldingExterior_coe hμ]
  rfl

end TakhtajanTeo
