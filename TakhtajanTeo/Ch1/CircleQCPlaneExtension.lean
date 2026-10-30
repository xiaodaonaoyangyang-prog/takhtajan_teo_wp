import TakhtajanTeo.Ch1.PeriodicDiskOrigin
import TakhtajanTeo.Ch1.WeldingPairRigidity

/-! Genuine global QC extensions of sense-preserving QS circle maps. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem disk_map_closed_extension {G h : ℂ → ℂ}
    (hc : Continuous G) (hi : InjOn G unitDisc) (hs : G '' unitDisc = unitDisc)
    (hb : EqOn G h unitCircle) (hhi : InjOn h unitCircle)
    (hhs : h '' unitCircle = unitCircle) :
    IsHomeoExtension G unitDisc unitDisc (OnePoint.map G) := by
  have hD : ∀ z ∈ unitDisc, ‖G z‖ < 1 := by
    intro z hz
    have hh : G z ∈ unitDisc := hs ▸ mem_image_of_mem G hz
    exact mem_ball_zero_iff.mp hh
  have hS : ∀ z ∈ unitCircle, ‖G z‖ = 1 := by
    intro z hz
    rw [hb hz]
    have hm : h z ∈ unitCircle := by
      rw [← hhs]
      exact mem_image_of_mem h hz
    exact hm
  have hcl : MapsTo G (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    intro z hz
    apply mem_closedBall_zero_iff.mpr
    rcases (mem_closedBall_zero_iff.mp hz).lt_or_eq with hd | hbd
    · exact (hD z (mem_ball_zero_iff.mpr hd)).le
    · exact (hS z hbd).le
  have hicl : InjOn G (closedBall (0 : ℂ) 1) := by
    intro z hz w hw he
    rcases (mem_closedBall_zero_iff.mp hz).lt_or_eq with hzD | hzS <;>
      rcases (mem_closedBall_zero_iff.mp hw).lt_or_eq with hwD | hwS
    · exact hi (mem_ball_zero_iff.mpr hzD) (mem_ball_zero_iff.mpr hwD) he
    · have hh := hD z (mem_ball_zero_iff.mpr hzD)
      rw [he, hS w hwS] at hh
      exact (lt_irrefl _ hh).elim
    · have hh := hD w (mem_ball_zero_iff.mpr hwD)
      rw [← he, hS z hzS] at hh
      exact (lt_irrefl _ hh).elim
    · exact hhi hzS hwS (by rwa [hb hzS, hb hwS] at he)
  have hscl : G '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1 := by
    apply Subset.antisymm hcl.image_subset
    intro w hw
    rcases (mem_closedBall_zero_iff.mp hw).lt_or_eq with hwD | hwS
    · have hw' : w ∈ G '' unitDisc := by rw [hs]; exact mem_ball_zero_iff.mpr hwD
      obtain ⟨z, hz, he⟩ := hw'
      exact ⟨z, ball_subset_closedBall hz, he⟩
    · have hw' : w ∈ h '' unitCircle := by rw [hhs]; exact hwS
      obtain ⟨z, hz, he⟩ := hw'
      exact ⟨z, mem_closedBall_zero_iff.mpr (show ‖z‖ = 1 from hz).le, (hb hz).trans he⟩
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_⟩
  · rw [abR_t_closure]
    rintro _ ⟨z, hz, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [OnePoint.continuousAt_coe]
    exact OnePoint.continuous_coe.continuousAt.comp hc.continuousAt
  · rw [abR_t_closure]
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ he
    exact congrArg (fun z : ℂ => (z : ExtPlane)) (hicl hz hw (OnePoint.coe_injective he))
  · rw [abR_t_closure]
    ext p
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨G z, hcl hz, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      rw [← hscl] at hw
      obtain ⟨z, hz, he⟩ := hw
      exact ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, congrArg (fun z : ℂ => (z : ExtPlane)) he⟩

theorem circle_quasisymmetric_plane_extension {h : ℂ → ℂ} (hh : IsQSCircleHomeo h) :
    ∃ H : ℂ → ℂ, IsQuasiconformal H univ ∧ H '' univ = univ ∧
      H '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 ∧ EqOn H h unitCircle := by
  obtain ⟨u, ρ, hu, hρ, -, hBA⟩ := circle_real_quasisymmetric_lift hh
  have hLift := hu
  obtain ⟨hc, hm, -, -, hp, -⟩ := hu
  let f := beurlingAhlfors u 1
  let G := periodicDiskMap f
  have hper : ∀ z : ℂ, ∀ n : ℤ, f (z + n) = f z + n := beurlingAhlfors_add_int hc hp 1
  have hGcont : Continuous G := beurlingAhlfors_disk_continuous hc hm hp
  have hG0 : G 0 = 0 := periodicDiskMap_zero _
  have hGp := periodicDiskMap_isKQC hBA.1 hper
  have hGpi := periodicDiskMap_injOn hper hBA.1.2.2.1.2.1
  have hGps := periodicDiskMap_image hper hBA.2.1
  have hGi : InjOn G unitDisc := by
    intro z hz w hw he
    by_cases hz0 : z = 0
    · subst z
      by_contra hw0
      exact periodicDiskMap_ne_zero (Ne.symm hw0) (he.symm.trans hG0)
    · by_cases hw0 : w = 0
      · subst w
        exact (periodicDiskMap_ne_zero hz0 (he.trans hG0)).elim
      · exact hGpi ⟨hz, hz0⟩ ⟨hw, hw0⟩ he
  have hGs : G '' unitDisc = unitDisc := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      by_cases hz0 : z = 0
      · simp [hz0, hG0, unitDisc]
      · have hh' : G z ∈ unitDisc \ {0} := hGps ▸ mem_image_of_mem _ ⟨hz, hz0⟩
        exact hh'.1
    · intro hw
      by_cases hw0 : w = 0
      · subst w
        exact ⟨0, by simp [unitDisc], hG0⟩
      · have hw' : w ∈ G '' (unitDisc \ {0}) := by rw [hGps]; exact ⟨hw, hw0⟩
        obtain ⟨z, hz, he⟩ := hw'
        exact ⟨z, hz.1, he⟩
  have hhome := qcl_f_isHomeomorphOnto_of_injOn isOpen_ball hGcont.continuousOn hGi
  have hGK : IsKQC G unitDisc (8 * ρ * (ρ + 1)) := by
    apply iskqc_of_subsingleton_exceptional (P := fun z => z ∈ unitDisc ∧ z ≠ 0)
      isOpen_ball hhome hGp.2.1 (fun z hz => hz.1) ?_ hGp
    intro z hz w hw
    have hz0 : z = 0 := by by_contra hn; exact hz.2 ⟨hz.1, hn⟩
    have hw0 : w = 0 := by by_contra hn; exact hw.2 ⟨hw.1, hn⟩
    exact hz0.trans hw0.symm
  have hGb : EqOn G h unitCircle := beurlingAhlfors_disk_boundary hLift
  have hunit : unitCircle = sphere (0 : ℂ) 1 := by ext z; simp [unitCircle]
  have hhi : InjOn h unitCircle := by rw [hunit]; exact hh.2.choose_spec.1
  have hhs := sense_circle_image hh.1
  have hExt := disk_map_closed_extension hGcont hGi hGs hGb hhi hhs
  obtain ⟨H, hHK, hHs, -, hHb, -⟩ := ab_reflect hGK hGs hG0 hExt
  have hHh : EqOn H h unitCircle := by
    intro z hz
    have he := hHb z hz
    change (H z : ExtPlane) = (G z : ExtPlane) at he
    exact (OnePoint.coe_injective he).trans (hGb hz)
  refine ⟨H, ⟨_, hHK⟩, hHs, ?_, hHh⟩
  rw [← hunit, image_congr hHh, hhs]

end TakhtajanTeo

#print axioms TakhtajanTeo.circle_quasisymmetric_plane_extension
