import TakhtajanTeo.Ch1.ComponentRelativeAmbient
import TakhtajanTeo.Ch1.ComponentRelativeNormalization
import TakhtajanTeo.Ch1.TCurveIndependent
import TakhtajanTeo.Ch1.GroupAlgebra

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem crc_exterior_chart {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ (e : ℂ ≃ₜ ℂ) (K : ℝ), IsKQC e univ K ∧
      EqOn e (gsans μ) unitDiscExterior ∧
      ∀ w ∈ closedBall (0 : ℂ) 1, e (wA μ w) = fsans μ w := by
  obtain ⟨K, hK⟩ := normalizedWeldingExterior_quasiconformal hμ
  obtain ⟨e, he⟩ := t203_pack_homeo hK (normalizedWeldingExterior_homeomorph hμ).2.2.1
  refine ⟨e, K, by rwa [he], ?_, ?_⟩
  · intro w hw
    rw [he, S2C.s2c_gsans_eq hμ]
    exact (gMu_eq_normalizedWeldingExterior hμ hw).symm
  · intro w hw
    rw [he, S2C.s2c_fsans_eq hμ]
    exact normalizedWeldingExterior_closedDisk hμ hw

theorem crc_wA_continuous_closed {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ContinuousOn (wA μ) (closedBall (0 : ℂ) 1) := by
  apply (wA_continuousOn_finite hμ).mono
  intro w hw
  obtain ⟨y, hy, he⟩ := (wAS_closed_iff hμ (w : ExtPlane)).mp ⟨w, hw, rfl⟩
  exact fun hi => OnePoint.coe_ne_infty y (he.trans hi)

theorem crc_qmp (e : ℂ ≃ₜ ℂ) {K : ℝ} (hK : IsKQC e univ K) :
    Measure.QuasiMeasurePreserving e volume volume := by
  have hi : Function.invFunOn (e.symm : ℂ → ℂ) univ = e := by
    funext z
    obtain ⟨w, rfl⟩ := e.symm.surjective z
    rw [e.symm.injective.injOn.leftInvOn_invFunOn (mem_univ w), e.apply_symm_apply]
  have h := ahT_qmp_inv ⟨K, homeomorph_inverse_isKQC e hK⟩
    (image_univ_of_surjective e.symm.surjective)
  rwa [hi] at h

/-- A genuine normalized circle map with exactly the required exterior
coefficient. The phase is from right conformal composition. -/
theorem crc_circle_map {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (F : ℂ ≃ₜ ℂ) {KF : ℝ} (hF : IsKQC F univ KF)
    (hmatch : ∀ w ∈ unitDisc, F (fsans μ w) = fsans ν w) :
    ∃ (T : ℂ ≃ₜ ℂ) (K : ℝ), IsKQC T univ K ∧
      T '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 ∧
      (∀ z : ℂ, ‖z‖ = 1 → T (wA μ z) = wA ν z) ∧
      T (-1) = -1 ∧ T (-I) = -I ∧ T 1 = 1 ∧
      (complexDilatation T =ᵐ[volume.restrict unitDiscExterior]
        hbPre_pullback (complexDilatation F) (gsans μ)) := by
  obtain ⟨eμ, Kμ, hKμ, heμ, hwμ⟩ := crc_exterior_chart hμ
  obtain ⟨eν, Kν, hKν, heν, hwν⟩ := crc_exterior_chart hν
  let T := (eμ.trans F).trans eν.symm
  have hFG : IsKQC ((F : ℂ → ℂ) ∘ eμ) univ (Kμ*KF) :=
    thm7_1_comp hKμ hF (subset_univ _)
  have hTK : IsKQC T univ ((Kμ*KF)*Kν) := by
    change IsKQC ((eν.symm : ℂ → ℂ) ∘ ((F : ℂ → ℂ) ∘ eμ)) univ _
    exact thm7_1_comp hFG (homeomorph_inverse_isKQC eν hKν) (subset_univ _)
  have hinside : ∀ w ∈ unitDisc, T (wA μ w) = wA ν w := by
    intro w hw
    change eν.symm (F (eμ (wA μ w))) = wA ν w
    rw [hwμ w (ball_subset_closedBall hw), hmatch w hw, ← hwν w (ball_subset_closedBall hw),
      eν.symm_apply_apply]
  have hclosed : IsClosed {w ∈ closedBall (0 : ℂ) 1 | T (wA μ w) = wA ν w} :=
    isClosed_closedBall.isClosed_eq
      (T.continuous.comp_continuousOn (crc_wA_continuous_closed hμ)) (crc_wA_continuous_closed hν)
  have heclosed := closure_minimal
    (show unitDisc ⊆ {w ∈ closedBall (0 : ℂ) 1 | T (wA μ w) = wA ν w} from
      fun w hw => ⟨ball_subset_closedBall hw, hinside w hw⟩) hclosed
  have hb : ∀ z : ℂ, ‖z‖ = 1 → T (wA μ z) = wA ν z := by
    intro z hz
    apply (heclosed ?_).2
    rw [unitDisc, closure_ball (0 : ℂ) one_ne_zero, mem_closedBall, dist_zero_right, hz]
  have hTc : T '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := tmi_circle_surj (wA_circle_sensePreserving hμ)
        (mem_sphere_zero_iff_norm.mp hy)
      rw [hb z hz]
      exact mem_sphere_zero_iff_norm.mpr (bg_circle_val hν hz).1
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := tmi_circle_surj (wA_circle_sensePreserving hν)
        (mem_sphere_zero_iff_norm.mp hy)
      exact ⟨wA μ z, mem_sphere_zero_iff_norm.mpr (bg_circle_val hμ hz).1, hb z hz⟩
  have hfix : ∀ {a : LinfStar}, a ∈ LinfStarBall →
      wA a (-1) = -1 ∧ wA a (-I) = -I ∧ wA a 1 = 1 := by
    intro a ha
    obtain ⟨_, _, _, _, _, _, hm1, hmI, hm2⟩ := wA_spec ha
    exact ⟨congrArg finPart hm1, congrArg finPart hmI, congrArg finPart hm2⟩
  have hfm := hfix hμ
  have hfn := hfix hν
  refine ⟨T, (Kμ*KF)*Kν, hTK, hTc, hb, ?_, ?_, ?_, ?_⟩
  · simpa only [hfm.1, hfn.1] using hb (-1) (by simp)
  · simpa only [hfm.2.1, hfn.2.1] using hb (-I) (by simp)
  · simpa only [hfm.2.2, hfn.2.2] using hb 1 (by simp)
  have hEo := resolvent_exterior_isOpen
  have hcm : IsConformalOnto eμ unitDiscExterior (gsans μ '' unitDiscExterior) :=
    ⟨(S2C.s2c_conf_g hμ).1.congr heμ, eμ.injective.injOn, heμ.image_eq⟩
  have hcn : IsConformalOnto eν unitDiscExterior (gsans ν '' unitDiscExterior) :=
    ⟨(S2C.s2c_conf_g hν).1.congr heν, eν.injective.injOn, heν.image_eq⟩
  have hni := hcn.symm hEo
  have hnieq : EqOn (Function.invFunOn (eν : ℂ → ℂ) unitDiscExterior) eν.symm
      (gsans ν '' unitDiscExterior) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← heν hw, eν.injective.injOn.leftInvOn_invFunOn hw, eν.symm_apply_apply]
  have hnconf : IsConformalOnto eν.symm (gsans ν '' unitDiscExterior) unitDiscExterior :=
    ⟨hni.1.congr hnieq.symm, eν.symm.injective.injOn, hnieq.image_eq.symm.trans hni.2.2⟩
  have hFimg := (cra_ambient_images hμ hν hmatch).2.2.2
  have hFGimg : ((F : ℂ → ℂ) ∘ eμ) '' unitDiscExterior = gsans ν '' unitDiscExterior := by
    rw [image_comp, hcm.2.2, hFimg]
  have hleft := (bg_comp_conformal
    (ac_t_isKQC_restrict hFG hEo (subset_univ _)) (hcn.isOpen hEo) hnconf hFGimg.le).2
  have hFa : ∀ᵐ u : ℂ, DifferentiableAt ℝ F u := by
    simpa only [Measure.restrict_univ] using thm9_3_differentiable_ae hF
  have hFpull := (crc_qmp eμ hKμ).ae hFa
  filter_upwards [hleft, ae_restrict_of_ae hFpull, ae_restrict_mem hEo.measurableSet]
    with w hw hd hwE
  change complexDilatation ((eν.symm : ℂ → ℂ) ∘ ((F : ℂ → ℂ) ∘ eμ)) w = _
  rw [hw, complexDilatation_comp_conformal_right
    (hcm.1.differentiableAt (hEo.mem_nhds hwE))
    (deriv_ne_zero_of_injOn hEo hcm.1 hcm.2.1 hwE) hd]
  have hev : (eμ : ℂ → ℂ) =ᶠ[𝓝 w] gsans μ :=
    Filter.eventually_of_mem (hEo.mem_nhds hwE) heμ
  have hdg : deriv (eμ : ℂ → ℂ) w = deriv (gsans μ) w := hev.deriv_eq
  rw [heμ hwE, hdg]
  rfl

/-- Extract the actual admissible coefficient, retaining its a.e. formula. -/
theorem crc_coefficient (T : ℂ ≃ₜ ℂ) {K : ℝ} (hK : IsKQC T univ K) :
    ∃ ω : LinfStarBall, (ω : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] complexDilatation T := by
  have hK1 : 1 ≤ K := hK.2.1
  have hk0 : 0 ≤ (K-1)/(K+1) := div_nonneg (by linarith) (by linarith)
  have hk1 : (K-1)/(K+1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hb : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖complexDilatation T z‖ ≤ (K-1)/(K+1) :=
    ae_restrict_of_ae_restrict_of_subset (subset_univ _) (isKQC_maxDilatation_le hK).2
  have hm := (thm10_2_genHomeoSolution_of_isKQC hK).1.1.mono_measure
    (Measure.restrict_mono (subset_univ unitDiscExterior) le_rfl)
  have hmem := memLp_top_of_bound hm ((K-1)/(K+1)) hb
  have hball : toLinf (complexDilatation T) ∈ LinfStarBall := by
    rw [LinfStarBall, mem_ball_zero_iff]
    exact (norm_toLinf_le_of_ae_bound hk0 hb).trans_lt hk1
  exact ⟨⟨toLinf (complexDilatation T), hball⟩, bc_toLinf_ae hmem⟩

/-- A physical nonlinear extension with finite pulled-back energy gives a
finite-L2 relative coefficient and the exact RIGHT multiplication class. -/
theorem crc_relative_coefficient {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (F : ℂ ≃ₜ ℂ) {KF : ℝ} (hF : IsKQC F univ KF)
    (hmatch : ∀ w ∈ unitDisc, F (fsans μ w) = fsans ν w)
    (hL2 : normL2 unitDiscExterior (hbPre_pullback (complexDilatation F) (gsans μ)) < ∞) :
    ∃ ω : LinfStarBall, normL2 unitDiscExterior (ω : LinfStar) < ∞ ∧
      Phi ⟨beltramiMul (ω : LinfStar) μ, grp_mul_mem ω.2 hμ⟩ = Phi ⟨ν, hν⟩ := by
  obtain ⟨T, K, hTK, hTc, hb, hm1, hmI, h1, hraw⟩ := crc_circle_map hμ hν F hF hmatch
  obtain ⟨ω, hωae⟩ := crc_coefficient T hTK
  have he := hωae.trans hraw
  have hn : normL2 unitDiscExterior (ω : LinfStar) =
      normL2 unitDiscExterior (hbPre_pullback (complexDilatation F) (gsans μ)) := by
    unfold normL2
    congr 1
    apply lintegral_congr_ae
    filter_upwards [he] with z hz
    rw [hz]
  refine ⟨ω, hn ▸ hL2, ?_⟩
  have hωT := crc_normalized_boundary ω.2 hTK hTc (fun _ _ => rfl) hm1 hmI h1 hωae
  apply Quotient.sound
  intro z hz
  have hzm := bg_circle_val hμ hz
  have hprod := congrFun (bc_wA_mul hμ ω.2).2.1 (z : ExtPlane)
  change finPart (wAS (beltramiMul (ω : LinfStar) μ) (z : ExtPlane)) = wA ν z
  rw [hprod, Function.comp_apply, hzm.2]
  change wA ω (wA μ z) = wA ν z
  rw [hωT _ hzm.1, hb z hz]

/-- Function-form interface matching the nonlinear extension contract: the
global homeomorphism is constructed from QC and onto, not assumed separately. -/
theorem crc_relative_coefficient_of_qc {μ ν : LinfStar}
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    {F : ℂ → ℂ} {K : ℝ} (hF : IsKQC F univ K) (hFs : F '' univ = univ)
    (hmatch : ∀ w ∈ unitDisc, F (fsans μ w) = fsans ν w)
    (hL2 : normL2 unitDiscExterior (hbPre_pullback (complexDilatation F) (gsans μ)) < ∞) :
    ∃ ω : LinfStarBall, normL2 unitDiscExterior (ω : LinfStar) < ∞ ∧
      Phi ⟨beltramiMul (ω : LinfStar) μ, grp_mul_mem ω.2 hμ⟩ = Phi ⟨ν, hν⟩ := by
  obtain ⟨e, he⟩ := t203_pack_homeo hF hFs
  have heK : IsKQC e univ K := by rwa [he]
  exact crc_relative_coefficient hμ hν e heK
    (by simpa only [he] using hmatch) (by simpa only [he] using hL2)

#print axioms crc_exterior_chart
#print axioms crc_wA_continuous_closed
#print axioms crc_qmp
#print axioms crc_circle_map
#print axioms crc_coefficient
#print axioms crc_relative_coefficient
#print axioms crc_relative_coefficient_of_qc
end TakhtajanTeo
