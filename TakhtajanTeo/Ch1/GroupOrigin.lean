import TakhtajanTeo.Ch1.GroupChain2
import TakhtajanTeo.Ch1.SphereWeldingTransport

/-! S1: regularity at the origin for harmonic coefficients. Approved stop:
600 new proof lines. Work uses explicit AW charts, not a W-REG assumption. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem grp25z_transition_chart (eF eW : ℂ ≃ₜ ℂ) {ψ : ℂ → ℂ}
    (hψ : IsConformalOnto ψ (eF '' unitDiscExterior) (eW '' unitDiscExterior))
    (hrel : ∀ x ∈ unitDiscExterior, eW x = ψ (eF x)) :
    ∃ ξ : ℂ → ℂ, AnalyticAt ℂ ξ 0 ∧ ξ 0 = 0 ∧ deriv ξ 0 ≠ 0 ∧
      ∀ t : ℂ, t ≠ 0 → ξ t = (eW (eF.symm t⁻¹))⁻¹ := by
  let T : ℂ ≃ₜ ℂ := eF.symm.trans eW
  let ξ : ℂ → ℂ := fun t => if t = 0 then 0 else (T t⁻¹)⁻¹
  have hξ0 : ξ 0 = 0 := by simp [ξ]
  have hInv : Tendsto (fun t : ℂ => t⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_nhdsNE_zero
  have hOut : Tendsto (fun t : ℂ => t⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded
  have hT := (isProperMap_iff_tendsto_cocompact.mp T.isProperMap).2
  have hF := (isProperMap_iff_tendsto_cocompact.mp eF.symm.isProperMap).2
  have hEmem : unitDiscExterior ∈ cocompact ℂ := by
    have he : unitDiscExterior = (closedBall (0 : ℂ) 1)ᶜ := by
      ext z
      simp [unitDiscExterior]
    rw [he]
    exact (isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact
  have hneMem : {z : ℂ | z ≠ 0} ∈ cocompact ℂ :=
    (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have hEv : ∀ᶠ t in 𝓝[≠] (0 : ℂ), eF.symm t⁻¹ ∈ unitDiscExterior ∧ T t⁻¹ ≠ 0 :=
    ((hF.comp hInv).eventually hEmem).and ((hT.comp hInv).eventually hneMem)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hEv)
  have hP : ∀ t ∈ ball (0 : ℂ) r, t ≠ 0 → eF.symm t⁻¹ ∈ unitDiscExterior ∧ T t⁻¹ ≠ 0 :=
    fun t ht h0 => hball ht h0
  have hUo : IsOpen (eF '' unitDiscExterior) :=
    eF.isOpenMap _ (isOpen_lt continuous_const continuous_norm)
  have hval : ∀ t ∈ ball (0 : ℂ) r, t ≠ 0 → T t⁻¹ = ψ t⁻¹ := by
    intro t ht h0
    simpa [T] using hrel (eF.symm t⁻¹) (hP t ht h0).1
  have hg : DifferentiableOn ℂ (fun t => (ψ t⁻¹)⁻¹) (ball (0 : ℂ) r \ {0}) := by
    intro t ht
    have htU : t⁻¹ ∈ eF '' unitDiscExterior :=
      ⟨eF.symm t⁻¹, (hP t ht.1 ht.2).1, eF.apply_symm_apply _⟩
    have hψd := hψ.1.differentiableAt (hUo.mem_nhds htU)
    have hn : ψ t⁻¹ ≠ 0 := (hval t ht.1 ht.2) ▸ (hP t ht.1 ht.2).2
    exact ((hψd.comp t (differentiableAt_inv ht.2)).inv hn).differentiableWithinAt
  have hξd : DifferentiableOn ℂ ξ (ball (0 : ℂ) r \ {0}) := hg.congr (by
    intro t ht
    simp only [ξ, if_neg (show t ≠ 0 from ht.2), hval t ht.1 ht.2])
  have hξc : ContinuousAt ξ 0 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hξ0]
    apply (hOut.comp (hT.comp hInv)).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (if_neg (show t ≠ 0 from ht)).symm
  have hd : DifferentiableOn ℂ ξ (ball (0 : ℂ) r) :=
    (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (ball_mem_nhds 0 hr)).mp ⟨hξd, hξc⟩
  have hξne : ∀ t ∈ ball (0 : ℂ) r, t ≠ 0 → ξ t ≠ 0 := by
    intro t ht h0
    change (if t = 0 then 0 else (T t⁻¹)⁻¹) ≠ 0
    rw [if_neg h0]
    exact inv_ne_zero (hP t ht h0).2
  have hinj : InjOn ξ (ball (0 : ℂ) r) := by
    intro t ht s hs he
    by_cases ht0 : t = 0
    · subst t
      by_contra hn
      exact hξne s hs (Ne.symm hn) (he.symm.trans hξ0)
    · by_cases hs0 : s = 0
      · subst s
        exact (hξne t ht ht0 (he.trans hξ0)).elim
      · have he' : (T t⁻¹)⁻¹ = (T s⁻¹)⁻¹ := by simpa [ξ, ht0, hs0] using he
        exact inv_injective (T.injective (inv_injective he'))
  refine ⟨ξ, hd.analyticOnNhd isOpen_ball 0 (mem_ball_self hr), hξ0,
    deriv_ne_zero_of_injOn isOpen_ball hd hinj (mem_ball_self hr), ?_⟩
  intro t ht
  simp only [ξ, if_neg ht]
  rfl

theorem grp25z_aw_chart {φ : AInf unitDisc} (hφ : ‖φ‖ < 2) :
    ∃ F τ : ℂ → ℂ, IsQuasiconformal F univ ∧ F '' univ = univ ∧
      (∀ᵐ z ∂(volume.restrict unitDiscExterior), complexDilatation F z = Lambda φ z) ∧
      ContDiffAt ℝ 1 τ 0 ∧ τ 0 = 0 ∧ dz τ 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℂ), τ t = (F t⁻¹)⁻¹ := by
  obtain ⟨H, K, hH, hHs, -, -, hHd, -, hHμ, hHreg⟩ :=
    grp_l333_core_reg (s := ‖φ‖ / 4) (by positivity) (by linarith) (aw_phi_diff φ)
      (fun z hz => aw_phi_bound φ hz)
  obtain ⟨e, rfl⟩ := t1_homeomorph hH hHs
  let R : ExtPlane → ExtPlane := mobiusExt 0 1 1 (-e I)
  have hR : IsMobius R := ⟨0, 1, 1, -e I, by norm_num, rfl⟩
  let Φ : ExtPlane → ExtPlane := R ∘ e.onePointCongr ∘ mobiusExt I I 1 (-1)
  have hRi : Φ extInf = extInf := by
    change R (e.onePointCongr (mobiusExt I I 1 (-1) extInf)) = extInf
    rw [mobiusExt_infty_of_ne (by norm_num : (1 : ℂ) ≠ 0)]
    simp only [div_one]
    change mobiusExt 0 1 1 (-e I) (e I : ExtPlane) = extInf
    apply mobiusExt_coe_of_eq_zero
    simp
  have hRc := mobius_sphere_continuous_bijective hR
  have hAc := mobius_sphere_continuous_bijective aw_gS_mobius
  have hΦb : Function.Bijective Φ := hRc.2.comp (e.onePointCongr.bijective.comp hAc.2)
  have hΦc : Continuous Φ := hRc.1.comp (e.onePointCongr.continuous.comp hAc.1)
  let F : ℂ → ℂ := fun z => finPart (Φ (z : ExtPlane))
  have hFK : IsKQC F univ K := sphereTransport_isKQC e.onePointCongr.bijective
    e.onePointCongr.continuous (fun z => rfl) hH aw_gS_mobius hR hRi
  have hFs := (sphereFinite_homeomorph hΦb hΦc hRi).2.2.1
  have hFcoe : ∀ z : ℂ, (F z : ExtPlane) = Φ (z : ExtPlane) := sphereFinite_coe hΦb hRi
  have hRel : ∀ z : ℂ, z ≠ 1 → Φ (z : ExtPlane) = R (e (awG z) : ExtPlane) := by
    intro z hz
    change R (e.onePointCongr (mobiusExt I I 1 (-1) (z : ExtPlane))) = _
    rw [aw_gS_coe (sub_ne_zero.mpr hz)]
    rfl
  have hRf : ∀ z : ℂ, z ≠ 1 → R (e (awG z) : ExtPlane) ≠ extInf := by
    intro z hz
    rw [← hRel z hz, ← hFcoe z]
    exact OnePoint.coe_ne_infty _
  have hform : ∀ v : ℂ, finPart (R (v : ExtPlane)) = (v - e I)⁻¹ := by
    intro v
    change finPart (mobiusExt 0 1 1 (-e I) (v : ExtPlane)) = _
    by_cases hv : v - e I = 0
    · rw [mobiusExt_coe_of_eq_zero (by simpa [sub_eq_add_neg] using hv), hv]
      simp [finPart]
    · rw [mobiusExt_coe (by simpa [sub_eq_add_neg] using hv)]
      simp [finPart, mobiusFn, sub_eq_add_neg]
  have hFform : ∀ z : ℂ, z ≠ 1 → F z = (e (awG z) - e I)⁻¹ := by
    intro z hz
    change finPart (Φ (z : ExtPlane)) = _
    rw [hRel z hz, hform]
  have hPoint : ∀ z ∈ unitDiscExterior,
      complexDilatation F z = complexDilatation (fun u => e (awG u)) z := by
    intro z hz
    have hz1 : z ≠ 1 := by rintro rfl; norm_num [unitDiscExterior] at hz
    let P : ℂ → ℂ := fun u => finPart (R (u : ExtPlane))
    have he : EqOn F (P ∘ (fun u => e (awG u))) {u : ℂ | u ≠ 1} := by
      intro u hu
      change finPart (Φ (u : ExtPlane)) = finPart (R (e (awG u) : ExtPlane))
      rw [hRel u hu]
    have hdf : DifferentiableAt ℝ (fun u => e (awG u)) z :=
      ((hHreg _ (aw_G_im_pos hz)).1.differentiableAt one_ne_zero).comp z
        ((aw_hasDerivAt_G (sub_ne_zero.mpr hz1)).differentiableAt.restrictScalars ℝ)
    have hPo := mobius_finite_open hR
    have hPc := mobius_finite_conformal hR
    exact (abR_t_complexDilatation_congr isOpen_ne he hz1).trans
      (complexDilatation_comp_conformal_left hdf
        (hPc.1.differentiableAt (hPo.mem_nhds (hRf z hz1)))
        (deriv_ne_zero_of_injOn hPo hPc.1 hPc.2.1 (hRf z hz1)))
  have hdil : ∀ᵐ z ∂(volume.restrict unitDiscExterior), complexDilatation F z = Lambda φ z := by
    filter_upwards [ae_restrict_of_ae (aw_dil_comp hH hHd hHμ),
      ae_restrict_mem (isOpen_lt continuous_const continuous_norm).measurableSet] with z hz hzE
    have hz1 : z - 1 ≠ 0 := by
      intro hh
      have he : z = 1 := sub_eq_zero.mp hh
      rw [he] at hzE
      norm_num [unitDiscExterior] at hzE
    rw [hPoint z hzE, hz hz1, extB, indicator_of_mem hzE]
  let τ : ℂ → ℂ := fun t => e (cayleyInv t) - e I
  have hc0 : cayleyInv 0 = I := by simp [cayleyInv]
  have hca : AnalyticAt ℂ cayleyInv 0 := by
    unfold cayleyInv
    exact (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
      (analyticAt_const.sub analyticAt_id) (by norm_num)
  have hcd : HasDerivAt cayleyInv (2 * I) 0 := by
    convert (((hasDerivAt_id (0 : ℂ)).const_add 1).const_mul I).div
      ((hasDerivAt_id (0 : ℂ)).const_sub 1) (by norm_num) using 1
    · funext z
      simp [cayleyInv, mul_add]
    · norm_num
      ring
  have hHI := hHreg I (by simp [upperHalf])
  have hHi : ContDiffAt ℝ 1 (e : ℂ → ℂ) (cayleyInv 0) := by rw [hc0]; exact hHI.1
  have hcomp : ContDiffAt ℝ 1 (fun t => e (cayleyInv t)) 0 :=
    hHi.comp 0 (hca.contDiffAt.restrict_scalars ℝ)
  have hτcd : ContDiffAt ℝ 1 τ 0 := hcomp.sub contDiffAt_const
  have hτdz : dz τ 0 = dz (e : ℂ → ℂ) I * (2 * I) := by
    change dz (fun t => e (cayleyInv t) - e I) 0 = _
    rw [dz_sub_pointwise (hcomp.differentiableAt one_ne_zero) (differentiableAt_const _)]
    have hconst : dz (fun _ : ℂ => e I) 0 = 0 := by simp [dz]
    rw [hconst, sub_zero]
    have he := (eq6_4 hcd.differentiableAt (hHi.differentiableAt one_ne_zero)).1
    simpa only [Function.comp_def, hc0, hcd.deriv] using he
  refine ⟨F, τ, ⟨K, hFK⟩, hFs, hdil, hτcd, ?_, ?_, ?_⟩
  · simp [τ, hc0]
  · rw [hτdz]
    exact mul_ne_zero hHI.2 (by norm_num)
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds (by norm_num : (0 : ℂ) ≠ 1))] with t ht0 ht1
    have hti1 : t⁻¹ ≠ 1 := by intro hh; apply ht1; simpa using congrArg Inv.inv hh
    have hc : awG t⁻¹ = cayleyInv t := by
      unfold awG cayleyInv
      have hden : 1 - t ≠ 0 := sub_ne_zero.mpr ht1.symm
      have ht0' : t ≠ 0 := ht0
      have hden' : t⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr hti1
      field_simp [ht0', hden, hden']
      <;> ring
    rw [hFform t⁻¹ hti1, hc, inv_inv]

theorem grp25z_conj_chart {F : ℂ → ℂ} (hF : ContDiffAt ℝ 1 F 0) :
    ContDiffAt ℝ 1 (fun z => conj (F (conj z))) 0 ∧
      dz (fun z => conj (F (conj z))) 0 = conj (dz F 0) := by
  have hconj : ContDiff ℝ 1 (conj : ℂ → ℂ) := Complex.conjCLE.contDiff
  have hFi : ContDiffAt ℝ 1 F (conj 0) := by simpa using hF
  have hin := hFi.comp 0 hconj.contDiffAt
  refine ⟨hconj.contDiffAt.comp 0 hin, ?_⟩
  obtain ⟨hcd, hdz, hdzbar⟩ := l333_mux_dz_conj (0 : ℂ)
  have hh := eq6_2_dzbar_comp hcd (hFi.differentiableAt one_ne_zero)
  have hid : dzbar (fun z : ℂ => conj (conj z)) 0 = 0 := by simp [dzbar]
  have hinner : dzbar (F ∘ conj) 0 = dz F 0 := by
    simpa only [map_zero, hdzbar, mul_one, hid, mul_zero, add_zero] using hh
  simpa only [Function.comp_def] using
    (eq6_3 (hin.differentiableAt one_ne_zero)).2.symm.trans (congrArg conj hinner)

theorem grp25_regular_zero {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hμ1 : ‖μ‖ < 1) :
    ContDiffAt ℝ 1 (wA μ) 0 ∧ dz (wA μ) 0 ≠ 0 := by
  have hμb : μ ∈ LinfStarBall := by simpa [LinfStarBall] using hμ1
  obtain ⟨φ, hφμ⟩ := Lambda_surjective_harmonic hμ
  have hφ2 : ‖φ‖ < 2 := by
    have hh := Lambda_norm_eq φ
    rw [hφμ] at hh
    linarith
  obtain ⟨F, τ, ⟨KF, hKF⟩, hFs, hdil, hτcd, hτ0, hτdz, hτrel⟩ := grp25z_aw_chart hφ2
  rw [hφμ] at hdil
  obtain ⟨eF, rfl⟩ := t1_homeomorph hKF hFs
  obtain ⟨M, hM, W, hW, hwf, -, -, -, -⟩ := wA_spec hμb
  obtain ⟨KW, hKW⟩ := hW.1
  obtain ⟨eW, rfl⟩ := t1_homeomorph hKW hW.2.1
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  obtain ⟨ψ, hψ, hWψ⟩ := grp_stoilow hE
    ⟨KF, nx_isKQC_restrict hKF hE (subset_univ _)⟩
    ⟨KW, nx_isKQC_restrict hKW hE (subset_univ _)⟩ (by
      filter_upwards [hdil, ae_restrict_of_ae hW.2.2.2.2, ae_restrict_mem hE.measurableSet] with z hz₁ hz₂ hzE
      rw [hz₁, hz₂]
      exact (extA_eq_on_exterior _ hzE).symm)
  obtain ⟨ξ, hξa, hξ0, hξder, hξrel⟩ := grp25z_transition_chart eF eW hψ hWψ
  have hξat : DifferentiableAt ℂ ξ (τ 0) := by rw [hτ0]; exact hξa.differentiableAt
  have hξcd : ContDiffAt ℝ 1 ξ (τ 0) := by rw [hτ0]; exact hξa.contDiffAt.restrict_scalars ℝ
  have hcomp : ContDiffAt ℝ 1 (fun t => ξ (τ t)) 0 := hξcd.comp 0 hτcd
  have hcompdz : dz (fun t => ξ (τ t)) 0 ≠ 0 := by
    rw [(grp_dz_comp_holo (hτcd.differentiableAt one_ne_zero) hξat).2, hτ0]
    exact mul_ne_zero hξder hτdz
  let Q : ℂ → ℂ := fun z => conj (ξ (τ (conj z)))
  obtain ⟨hQcd, hQdz⟩ := grp25z_conj_chart hcomp
  have hQ0 : Q 0 = 0 := by simp [Q, hτ0, hξ0]
  have hQdzne : dz Q 0 ≠ 0 := by
    rw [hQdz]
    simpa using hcompdz
  have hInv : Tendsto (fun t : ℂ => t⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_nhdsNE_zero
  have hFproper := (isProperMap_iff_tendsto_cocompact.mp eF.isProperMap).2
  have hFne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), eF t⁻¹ ≠ 0 :=
    (hFproper.comp hInv).eventually (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have hconjT : Tendsto (conj : ℂ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [map_zero] using (Complex.continuous_conj.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have hev : (eW : ℂ → ℂ) =ᶠ[𝓝[≠] 0] Q := by
    filter_upwards [hconjT.eventually hτrel, hconjT.eventually hFne] with z hzτ hzF
    have hτne : τ (conj z) ≠ 0 := by rw [hzτ]; exact inv_ne_zero hzF
    have hξval : ξ (τ (conj z)) = (eW (conj z)⁻¹)⁻¹ := by
      rw [hξrel _ hτne, hzτ, inv_inv, eF.symm_apply_apply]
    change eW z = conj (ξ (τ (conj z)))
    rw [hξval]
    have href := normalized_solution_refl_comm hW z
    change eW (conj z)⁻¹ = (conj (eW z))⁻¹ at href
    rw [href, inv_inv, Complex.conj_conj]
  have hev0 : (eW : ℂ → ℂ) =ᶠ[𝓝 0] Q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hev] with z hz
    by_cases hz0 : z = 0
    · subst z
      rw [hW.2.2.1, hQ0]
    · exact hz hz0
  have hWcd : ContDiffAt ℝ 1 (eW : ℂ → ℂ) 0 := hQcd.congr_of_eventuallyEq hev0
  have hWdz : dz (eW : ℂ → ℂ) 0 ≠ 0 := by
    rw [(t203_c1_dz_congr hev0).1]
    exact hQdzne
  have hMfin : M (eW 0 : ExtPlane) ≠ extInf := by
    rw [← hwf 0]
    intro hzero
    apply wAS_pole_notin_disc hμb (show ‖(0 : ℂ)‖ < 1 by norm_num)
    rw [← hzero]
    exact Function.leftInverse_invFun (wAS_bijective μ).1 _
  have hMo := mobius_finite_open hM
  have hMc := mobius_finite_conformal hM
  let P : ℂ → ℂ := fun z => finPart (M (z : ExtPlane))
  have hPd : DifferentiableAt ℂ P (eW 0) := hMc.1.differentiableAt (hMo.mem_nhds hMfin)
  have hPcd : ContDiffAt ℝ 1 P (eW 0) := grp_holo_cd hMo hMc.1 hMfin
  have hPder : deriv P (eW 0) ≠ 0 := deriv_ne_zero_of_injOn hMo hMc.1 hMc.2.1 hMfin
  have heq : wA μ = fun z => P (eW z) := by
    funext z
    unfold wA
    rw [hwf z]
  rw [heq]
  refine ⟨hPcd.comp 0 hWcd, ?_⟩
  rw [(grp_dz_comp_holo (hWcd.differentiableAt one_ne_zero) hPd).2]
  exact mul_ne_zero hPder hWdz

end TakhtajanTeo

#print axioms TakhtajanTeo.grp25z_transition_chart
#print axioms TakhtajanTeo.grp25z_aw_chart
#print axioms TakhtajanTeo.grp25z_conj_chart
#print axioms TakhtajanTeo.grp25_regular_zero
