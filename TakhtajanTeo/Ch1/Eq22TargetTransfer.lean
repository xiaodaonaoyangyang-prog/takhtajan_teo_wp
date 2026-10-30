import TakhtajanTeo.Ch1.Eq22WeakTransfer

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem eq22v_null_image {D : Set ℂ} {h : ℂ → ℂ}
    (hh : IsQuasiconformal (fun u => conj (h u)) D)
    {S : Set ℂ} (hSD : S⊆D) (hS : volume S=0) : volume (h '' S)=0 := by
  obtain ⟨K,hK⟩ := hh
  have hn := ac_n_volume_image_null_of_isKQC hK hSD hS
  have he : h '' S = conj ⁻¹' ((fun u => conj (h u)) '' S) := by
    ext v
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u,hu,rfl⟩
    · rintro ⟨u,hu,he⟩
      exact ⟨u,hu,by simpa using congrArg conj he⟩
  rw [he]
  exact gzE_conj_measurePreserving.quasiMeasurePreserving.preimage_null hn

theorem eq22v_jacobian_nonpos {D : Set ℂ} {h : ℂ → ℂ}
    (hh : IsQuasiconformal (fun u => conj (h u)) D) {u : ℂ} (hu : u∈D)
    (hd : DifferentiableAt ℝ h u) : jacobian h u≤0 := by
  obtain ⟨K,hK⟩ := hh
  have hg : DifferentiableAt ℝ (fun u => conj (h u)) u :=
    Complex.conjCLE.differentiableAt.comp u hd
  have hn := ac_j_jacobian_nonneg hK hu hg
  simp only [jacobian,dz_conj hd,dzbar_conj hd,norm_conj] at hn
  dsimp only [jacobian]
  linarith

set_option maxHeartbeats 800000 in
/-- Signed anti-QC area change of variables, including integrability in both directions. -/
theorem eq22v_anti_cov {D : Set ℂ} {h : ℂ → ℂ}
    (hh : IsQuasiconformal (fun u => conj (h u)) D) (G : ℂ → ℂ) :
    (IntegrableOn G (h '' D) ↔
      IntegrableOn (fun u => (jacobian h u : ℂ)*G (h u)) D) ∧
    (∫ v in h '' D, G v) = -(∫ u in D, (jacobian h u : ℂ)*G (h u)) := by
  obtain ⟨K,hK⟩ := hh
  have hD := hK.1.measurableSet
  let A := D ∩ {u | DifferentiableAt ℝ h u}
  have hAm : MeasurableSet A := hD.inter (measurableSet_of_differentiableAt ℝ h)
  have hAD : A⊆D := inter_subset_left
  have hn : volume (D \ A)=0 := by
    have hd := eq22w_antiQC_diff (show IsQuasiconformal (fun u => conj (h u)) D from ⟨K,hK⟩)
    rw [ae_restrict_iff' hD,ae_iff] at hd
    refine measure_mono_null (t := {u : ℂ | ¬(u∈D → DifferentiableAt ℝ h u)}) ?_ hd
    intro u hu hd'
    exact hu.2 ⟨hu.1,hd' hu.1⟩
  have himgn : volume (h '' (D \ A))=0 := eq22v_null_image ⟨K,hK⟩ sdiff_subset hn
  have hset : A =ᵐ[volume] D := ae_eq_set.mpr ⟨by
    rw [sdiff_eq_empty.mpr hAD,measure_empty],hn⟩
  have himg : h '' D =ᵐ[volume] h '' A := by
    apply ae_eq_set.mpr
    refine ⟨measure_mono_null ?_ himgn,?_⟩
    · rintro v ⟨⟨u,hu,rfl⟩,hv⟩
      exact ⟨u,⟨hu,fun ha => hv ⟨u,ha,rfl⟩⟩,rfl⟩
    · rw [sdiff_eq_empty.mpr (image_mono hAD),measure_empty]
  have hi : InjOn h A := by
    intro u hu v hv he
    exact hK.2.2.1.2.1 (hAD hu) (hAD hv) (congrArg conj he)
  have hdiff : ∀ u∈A, HasFDerivWithinAt h (fderiv ℝ h u) A u :=
    fun u hu => hu.2.hasFDerivAt.hasFDerivWithinAt
  have hfun : (fun u => |(fderiv ℝ h u).det| • G (h u)) =ᵐ[volume.restrict A]
      (fun u => -((jacobian h u : ℂ)*G (h u))) := by
    filter_upwards [ae_restrict_mem hAm] with u hu
    have he : (fderiv ℝ h u).det = jacobian h u := det_fderiv_eq_jacobian hu.2
    rw [he,abs_of_nonpos (eq22v_jacobian_nonpos ⟨K,hK⟩ hu.1 hu.2)]
    simp [Complex.real_smul]
  constructor
  · calc IntegrableOn G (h '' D) ↔ IntegrableOn G (h '' A) := integrableOn_congr_set_ae himg
      _ ↔ IntegrableOn (fun u => |(fderiv ℝ h u).det| • G (h u)) A :=
        integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hAm hdiff hi G
      _ ↔ IntegrableOn (fun u => -((jacobian h u : ℂ)*G (h u))) A :=
        integrableOn_congr_fun_ae hfun
      _ ↔ IntegrableOn (fun u => (jacobian h u : ℂ)*G (h u)) A := by simp
      _ ↔ IntegrableOn (fun u => (jacobian h u : ℂ)*G (h u)) D := integrableOn_congr_set_ae hset
  · calc (∫ v in h '' D, G v) = ∫ v in h '' A, G v := setIntegral_congr_set himg
      _ = ∫ u in A, |(fderiv ℝ h u).det| • G (h u) :=
        integral_image_eq_integral_abs_det_fderiv_smul volume hAm hdiff hi G
      _ = ∫ u in A, -((jacobian h u : ℂ)*G (h u)) := integral_congr_ae hfun
      _ = -(∫ u in D, (jacobian h u : ℂ)*G (h u)) := by
        rw [integral_neg,setIntegral_congr_set hset]

def eq22v_targetKernel (H q : ℂ → ℂ) (z v : ℂ) : ℂ :=
  q v*(1/(H v-z)+(H v-v)/(H v-z)^2+(H v-v)^2/(H v-z)^3)

/-- Actual target-domain transfer under the original reflection hypothesis. The inverse H,
the omitted point, both integrability statements and the positive sign are constructed. -/
theorem eq22v_reflection_transfer {μ : LinfStar} (hμ : μ∈LinfStarBall)
    {h q : ℂ → ℂ} {z : ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hq : DifferentiableOn ℂ q (fsans μ '' unitDisc)) (hz : z∈fsans μ '' unitDisc) :
    ∃ a∈fsans μ '' unitDisc, Tendsto h (cocompact ℂ) (𝓝 a) ∧
      ∃ H : ℂ → ℂ, ContinuousOn H ((fsans μ '' unitDisc) \ {a}) ∧
        MapsTo H ((fsans μ '' unitDisc) \ {a}) (gsans μ '' unitDiscExterior) ∧
        (∀ u∈gsans μ '' unitDiscExterior, H (h u)=u) ∧
        (∀ v∈(fsans μ '' unitDisc) \ {a}, h (H v)=v) ∧
        ∀ t : ℂ → ℂ, ContDiff ℝ 1 t → HasCompactSupport t →
          tsupport t⊆(fsans μ '' unitDisc) \ {a} →
          Integrable (fun u => (gsans μ '' unitDiscExterior).indicator (t ∘ h) u *
            (q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) ∧
          IntegrableOn (fun v => eq22v_targetKernel H q z v*dzbar t v)
            ((fsans μ '' unitDisc) \ {a}) ∧
          (∫ u, (gsans μ '' unitDiscExterior).indicator (t ∘ h) u *
            (q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)) =
            (1/3 : ℂ)*(∫ v in (fsans μ '' unitDisc) \ {a}, eq22v_targetKernel H q z v*dzbar t v) := by
  obtain ⟨a,ha,hinf,H,hH,hmap,hleft,hright⟩ := eq22_reflection_inverse hμ hh
  obtain ⟨b,_,hbinf,htransfer⟩ := eq22t_reflection_transfer hμ hh hq hz
  have hba : b=a := tendsto_nhds_unique hbinf hinf
  subst b
  obtain ⟨c,_,hcinf,himg⟩ := eq22_reflection_image hμ hh
  have hca : c=a := tendsto_nhds_unique hcinf hinf
  subst c
  refine ⟨a,ha,hinf,H,hH,hmap,hleft,hright,?_⟩
  intro t ht htc hts
  obtain ⟨hI,hJ,he⟩ := htransfer t ht htc hts
  let G : ℂ → ℂ := fun v => eq22v_targetKernel H q z v*dzbar t v
  have hcov := eq22v_anti_cov hh.1 G
  rw [himg] at hcov
  have hEm : MeasurableSet (gsans μ '' unitDiscExterior) := (Classical.choose_spec hh.1).1.measurableSet
  have hsource : (fun u => (jacobian h u : ℂ)*G (h u)) =ᵐ[volume.restrict (gsans μ '' unitDiscExterior)]
      (fun u => eq22t_kernel h q z u*dzbar t (h u)*(jacobian h u : ℂ)) := by
    filter_upwards [ae_restrict_mem hEm] with u hu
    simp only [G,eq22v_targetKernel,eq22t_kernel,hleft u hu]
    ring
  refine ⟨hI,hcov.1.mpr (hJ.congr hsource.symm),?_⟩
  rw [he]
  change -(1/3 : ℂ)*(∫ u in gsans μ '' unitDiscExterior,
    eq22t_kernel h q z u*dzbar t (h u)*(jacobian h u : ℂ)) =
      (1/3 : ℂ)*(∫ v in (fsans μ '' unitDisc) \ {a}, G v)
  rw [hcov.2,integral_congr_ae hsource]
  ring

end TakhtajanTeo

