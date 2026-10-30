import TakhtajanTeo.Ch1.TCurveNormalizedTransport
import TakhtajanTeo.Ch1.ComponentRelativeCoefficient

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Each class has a plane extension retaining its actual coefficient and
the three normalization points. No regularity of a choice function is asserted. -/
theorem tcg_normalized_extension {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ (e : ℂ ≃ₜ ℂ) (K : ℝ) (ξ : LinfStarBall), IsKQC (⇑e) univ K ∧
      e '' unitDiscExterior = unitDiscExterior ∧
      e '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 ∧
      EqOn (⇑e) (wA μ) unitCircle ∧ e (-1) = -1 ∧ e (-I) = -I ∧ e 1 = 1 ∧
      (ξ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] complexDilatation (⇑e) ∧
      Phi ξ = Phi ⟨μ, hμ⟩ := by
  have hu : extInf ∈ extDiscExterior := Or.inr rfl
  obtain ⟨G, hG⟩ := tcg_extension_exists hμ hu
  obtain ⟨K, e, hK, he, hE, hCl, hC⟩ := tmi_G_data hμ hu hG
  have hKe : IsKQC (⇑e) univ K := he ▸ hK
  have hb : EqOn (⇑e) (wA μ) unitCircle := by
    intro z hz
    rw [he, hG.2.2 hz]
    dsimp only
    rw [(tce_gamma_circle hμ hz).1]
    rfl
  obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, h1⟩ := wA_spec hμ
  have hm1' : wA μ (-1) = -1 := congrArg finPart hm1
  have hmI' : wA μ (-I) = -I := congrArg finPart hmI
  have h1' : wA μ 1 = 1 := congrArg finPart h1
  obtain ⟨ξ, hξ⟩ := crc_coefficient e hKe
  refine ⟨e, K, ξ, hKe, he ▸ hE, he ▸ hC, hb,
    (hb (by simp [unitCircle])).trans hm1',
    (hb (by simp [unitCircle])).trans hmI',
    (hb (by simp [unitCircle])).trans h1', hξ, ?_⟩
  apply Quotient.sound
  exact crc_normalized_boundary ξ.2 hKe (he ▸ hC) hb hm1' hmI' h1' hξ

/-- Inverting a homeomorphism conformal on the disk gives the genuine
inverse disk automorphism, with no use of a total inverse off its domain. -/
theorem tcg_inverse_disk_conformal (e : ℂ ≃ₜ ℂ)
    (he : IsConformalOnto (⇑e) unitDisc unitDisc) :
    IsConformalOnto (⇑e.symm) unitDisc unitDisc := by
  have hi := he.symm isOpen_ball
  have heq : EqOn (⇑e.symm) (Function.invFunOn (⇑e) unitDisc) unitDisc := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := he.2.2.symm ▸ hz
    rw [e.symm_apply_apply, e.injective.injOn.leftInvOn_invFunOn hw]
  exact ⟨hi.1.congr heq, e.symm.injective.injOn, heq.image_eq.trans hi.2.2⟩

/-- Every exterior sphere parameter has a genuine plane extension of sigma,
conformal on the disk, including the identity extension at infinity. -/
theorem tcg_sigma_extension {u : ExtPlane} (hu : u ∈ extDiscExterior) :
    ∃ (e : ℂ ≃ₜ ℂ) (K : ℝ), IsKQC (⇑e) univ K ∧
      e '' unitDiscExterior = unitDiscExterior ∧
      IsConformalOnto (⇑e.symm) unitDisc unitDisc ∧
      EqOn (⇑e) (fun z : ℂ => finPart (sigmaSphere u (z : ExtPlane))) unitCircle := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  induction u using OnePoint.rec with
  | infty =>
    refine ⟨Homeomorph.refl ℂ, 1, ?_, ?_, ?_, ?_⟩
    · exact isKQC_one_of_conformal isOpen_univ (isConformalOnto_id univ)
    · exact image_id _
    · exact isConformalOnto_id unitDisc
    · intro z hz; rfl
  | coe u =>
    have huE : u ∈ unitDiscExterior := by simpa [extDiscExterior, toExt] using hu
    obtain ⟨R, hRq, hRs, hRa⟩ := sigmaW_closed_extension huE
    have hG : IsQuasiconformal R univ ∧ R '' univ = univ ∧
        EqOn R (fun z : ℂ => finPart (sigmaSphere (u : ExtPlane) (gammaMu 0 z))) unitCircle := by
      refine ⟨hRq, hRs, ?_⟩
      intro z hz
      dsimp only
      have hz1 : ‖z‖ = 1 := hz
      have hzu : z ≠ u := by intro h; rw [h] at hz1; exact (ne_of_gt huE) hz1
      have hg : gammaMu 0 z = (z : ExtPlane) := by
        simp only [gammaMu, alphaMu_eq_id, grp_wAS_zero, id_eq]
      rw [hRa (mem_closedBall_zero_iff.mpr hz1.le), hg, sigmaSphere_coe_eq huE hzu]
      rfl
    obtain ⟨K, e, hKe, he, hE, hC, hS⟩ := tmi_G_data h0 hu hG
    obtain ⟨c, a, hc, ha, heA⟩ := sigmaW_blaschke_closed huE
    have heq : EqOn (⇑e) (fun z => c * blaschke a z) unitDisc := by
      intro z hz
      rw [he, hRa (ball_subset_closedBall hz), heA (ball_subset_closedBall hz)]
    have hconf := (isConformalOnto_rot hc).comp (isConformalOnto_blaschke ha)
    have heD : IsConformalOnto (⇑e) unitDisc unitDisc :=
      ⟨hconf.1.congr heq, e.injective.injOn, heq.image_eq.trans hconf.2.2⟩
    refine ⟨e, K, he ▸ hKe, he ▸ hE, tcg_inverse_disk_conformal e heD, ?_⟩
    intro z hz
    have hg := hG.2.2 hz
    have hg0 : gammaMu 0 z = (z : ExtPlane) := by
      simp only [gammaMu, alphaMu_eq_id, grp_wAS_zero, id_eq]
    change e z = finPart (sigmaSphere (u : ExtPlane) (z : ExtPlane))
    rw [he]
    simpa only [hg0] using hg

#print axioms tcg_normalized_extension
#print axioms tcg_sigma_extension
end TakhtajanTeo
