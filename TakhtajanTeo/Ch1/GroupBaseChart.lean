import TakhtajanTeo.Ch1.GroupBase

/-! Normalized infinity charts for S3. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem grp25b_cayley_deriv : HasDerivAt cayleyInv (2 * I) 0 := by
  convert (((hasDerivAt_id (0 : ℂ)).const_add 1).const_mul I).div
    ((hasDerivAt_id (0 : ℂ)).const_sub 1) (by norm_num) using 1
  · funext z
    simp [cayleyInv, mul_add]
  · norm_num
    ring

theorem grp25b_chart {φ : AInf unitDisc} (e : ℂ ≃ₜ ℂ) {K : ℝ}
    (hK : IsKQC (e : ℂ → ℂ) univ K)
    (hhol : DifferentiableOn ℂ (e : ℂ → ℂ) lowerHalf)
    (hμ : ∀ z ∈ upperHalf, complexDilatation (e : ℂ → ℂ) z =
      -2 * (z.im : ℂ) ^ 2 * awPhi φ (conj z))
    (hreg : ∀ z ∈ upperHalf, ContDiffAt ℝ 1 (e : ℂ → ℂ) z ∧ dz (e : ℂ → ℂ) z ≠ 0) :
    ∃ F : ℂ ≃ₜ ℂ, ∃ τ : ℂ → ℂ,
      IsKQC (F : ℂ → ℂ) univ K ∧ F 0 = 0 ∧ F 1 = 1 ∧
      (∀ᵐ z ∂(volume.restrict unitDiscExterior), complexDilatation (F : ℂ → ℂ) z = Lambda φ z) ∧
      ContDiffAt ℝ 1 τ 0 ∧ τ 0 = 0 ∧
      dz τ 0 = dz (e : ℂ → ℂ) I * (2 * I) / (e I - e (-I)) ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℂ), τ t = (F t⁻¹)⁻¹ := by
  have he : e I ≠ e (-I) := by
    intro hh
    have hi := congrArg Complex.im (e.injective hh)
    norm_num at hi
  let N : ExtPlane → ExtPlane := mobiusExt 1 (-e (-I)) 1 (-e I)
  have hN : IsMobius N := ⟨1, -e (-I), 1, -e I, by
    simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr he.symm, rfl⟩
  let Φ : ExtPlane → ExtPlane := N ∘ e.onePointCongr ∘ mobiusExt I I 1 (-1)
  have hΦi : Φ extInf = extInf := by
    change N (e.onePointCongr (mobiusExt I I 1 (-1) extInf)) = extInf
    rw [mobiusExt_infty_of_ne (by norm_num : (1 : ℂ) ≠ 0)]
    simp only [div_one]
    change mobiusExt 1 (-e (-I)) 1 (-e I) (e I : ExtPlane) = extInf
    exact mobiusExt_coe_of_eq_zero (by simp)
  have hNc := mobius_sphere_continuous_bijective hN
  have hAc := mobius_sphere_continuous_bijective aw_gS_mobius
  have hΦb : Function.Bijective Φ := hNc.2.comp (e.onePointCongr.bijective.comp hAc.2)
  have hΦc : Continuous Φ := hNc.1.comp (e.onePointCongr.continuous.comp hAc.1)
  let f : ℂ → ℂ := fun z => finPart (Φ (z : ExtPlane))
  have hfK : IsKQC f univ K := sphereTransport_isKQC e.onePointCongr.bijective
    e.onePointCongr.continuous (fun z => rfl) hK aw_gS_mobius hN hΦi
  have hfs := (sphereFinite_homeomorph hΦb hΦc hΦi).2.2.1
  obtain ⟨F, hF⟩ := t1_homeomorph hfK hfs
  have hfcoe : ∀ z : ℂ, (f z : ExtPlane) = Φ (z : ExtPlane) := sphereFinite_coe hΦb hΦi
  have hRel : ∀ z : ℂ, z ≠ 1 → Φ (z : ExtPlane) = N (e (awG z) : ExtPlane) := by
    intro z hz
    change N (e.onePointCongr (mobiusExt I I 1 (-1) (z : ExtPlane))) = _
    rw [aw_gS_coe (sub_ne_zero.mpr hz)]
    rfl
  have hNf : ∀ z : ℂ, z ≠ 1 → N (e (awG z) : ExtPlane) ≠ extInf := by
    intro z hz
    rw [← hRel z hz, ← hfcoe z]
    exact OnePoint.coe_ne_infty _
  have hform : ∀ v : ℂ, finPart (N (v : ExtPlane)) = (v - e (-I)) / (v - e I) := by
    intro v
    change finPart (mobiusExt 1 (-e (-I)) 1 (-e I) (v : ExtPlane)) = _
    by_cases hv : v - e I = 0
    · rw [mobiusExt_coe_of_eq_zero (by simpa [sub_eq_add_neg] using hv), hv]
      simp [finPart]
    · rw [mobiusExt_coe (by simpa [sub_eq_add_neg] using hv)]
      simp [finPart, mobiusFn, sub_eq_add_neg]
  have hfForm : ∀ z : ℂ, z ≠ 1 → f z = (e (awG z) - e (-I)) / (e (awG z) - e I) := by
    intro z hz
    change finPart (Φ (z : ExtPlane)) = _
    rw [hRel z hz, hform]
  have hf0 : f 0 = 0 := by
    rw [hfForm 0 (by norm_num)]
    have hg0 : awG 0 = -I := by simp [awG, div_neg]
    rw [hg0]
    simp
  have hf1 : f 1 = 1 := by
    change finPart (N (e.onePointCongr (mobiusExt I I 1 (-1) ((1 : ℂ) : ExtPlane)))) = 1
    rw [mobiusExt_coe_of_eq_zero (by norm_num : (1 : ℂ) * 1 + -1 = 0)]
    change finPart (mobiusExt 1 (-e (-I)) 1 (-e I) extInf) = 1
    rw [mobiusExt_infty_of_ne (by norm_num : (1 : ℂ) ≠ 0)]
    simp [finPart]
  have hPoint : ∀ z ∈ unitDiscExterior,
      complexDilatation f z = complexDilatation (fun u => e (awG u)) z := by
    intro z hz
    have hz1 : z ≠ 1 := by rintro rfl; norm_num [unitDiscExterior] at hz
    let P : ℂ → ℂ := fun u => finPart (N (u : ExtPlane))
    have hh : EqOn f (P ∘ (fun u => e (awG u))) {u : ℂ | u ≠ 1} := by
      intro u hu
      change finPart (Φ (u : ExtPlane)) = finPart (N (e (awG u) : ExtPlane))
      rw [hRel u hu]
    have hdf : DifferentiableAt ℝ (fun u => e (awG u)) z :=
      ((hreg _ (aw_G_im_pos hz)).1.differentiableAt one_ne_zero).comp z
        ((aw_hasDerivAt_G (sub_ne_zero.mpr hz1)).differentiableAt.restrictScalars ℝ)
    have hPo := mobius_finite_open hN
    have hPc := mobius_finite_conformal hN
    exact (abR_t_complexDilatation_congr isOpen_ne hh hz1).trans
      (complexDilatation_comp_conformal_left hdf
        (hPc.1.differentiableAt (hPo.mem_nhds (hNf z hz1)))
        (deriv_ne_zero_of_injOn hPo hPc.1 hPc.2.1 (hNf z hz1)))
  have hdil : ∀ᵐ z ∂(volume.restrict unitDiscExterior), complexDilatation f z = Lambda φ z := by
    filter_upwards [ae_restrict_of_ae (aw_dil_comp hK hhol hμ),
      ae_restrict_mem (isOpen_lt continuous_const continuous_norm).measurableSet] with z hz hzE
    have hz1 : z - 1 ≠ 0 := by
      intro hh
      rw [sub_eq_zero.mp hh] at hzE
      norm_num [unitDiscExterior] at hzE
    rw [hPoint z hzE, hz hz1, extB, indicator_of_mem hzE]
  let P : ℂ → ℂ := fun v => (v - e I) / (v - e (-I))
  let τ : ℂ → ℂ := fun t => P (e (cayleyInv t))
  have hc0 : cayleyInv 0 = I := by simp [cayleyInv]
  have hca : AnalyticAt ℂ cayleyInv 0 := by
    unfold cayleyInv
    exact (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
      (analyticAt_const.sub analyticAt_id) (by norm_num)
  have hPa : AnalyticAt ℂ P (e I) := (analyticAt_id.sub analyticAt_const).div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr he)
  have hPd : deriv P (e I) = 1 / (e I - e (-I)) := by
    have hh := ((hasDerivAt_id (e I)).sub_const (e I)).div
      ((hasDerivAt_id (e I)).sub_const (e (-I))) (sub_ne_zero.mpr he)
    change deriv ((fun v : ℂ => id v - e I) / (fun v : ℂ => id v - e (-I))) (e I) = _
    rw [hh.deriv]
    simp only [id_eq, sub_self, zero_mul, sub_zero, one_mul]
    field_simp
  have hHI := hreg I (by simp [upperHalf])
  have hcd : ContDiffAt ℝ 1 (fun t => e (cayleyInv t)) 0 := by
    apply ContDiffAt.comp 0 _ (hca.contDiffAt.restrict_scalars ℝ)
    simpa [hc0] using hHI.1
  have hτcd : ContDiffAt ℝ 1 τ 0 := by
    change ContDiffAt ℝ 1 (P ∘ (fun t => e (cayleyInv t))) 0
    apply ContDiffAt.comp 0 _ hcd
    simpa [hc0] using hPa.contDiffAt.restrict_scalars ℝ
  refine ⟨F, τ, hF ▸ hfK, ?_, ?_, hF ▸ hdil, hτcd, ?_, ?_, ?_⟩
  · simpa [hF] using hf0
  · simpa [hF] using hf1
  · simp [τ, P, hc0]
  · have hinner := (eq6_4 grp25b_cayley_deriv.differentiableAt
      (show DifferentiableAt ℝ (e : ℂ → ℂ) (cayleyInv 0) by simpa [hc0] using hHI.1.differentiableAt one_ne_zero)).1
    have hout := (grp_dz_comp_holo (hcd.differentiableAt one_ne_zero)
      (show DifferentiableAt ℂ P (e (cayleyInv 0)) by simpa [hc0] using hPa.differentiableAt)).2
    dsimp only [τ]
    rw [hout, hc0, hPd]
    have hi : dz (fun t => e (cayleyInv t)) 0 = dz (e : ℂ → ℂ) I * (2 * I) := by
      simpa only [Function.comp_def, hc0, grp25b_cayley_deriv.deriv] using hinner
    rw [hi]
    ring
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds (by norm_num : (0 : ℂ) ≠ 1))] with t ht0 ht1
    have hti1 : t⁻¹ ≠ 1 := by intro hh; apply ht1; simpa using congrArg Inv.inv hh
    have hc : awG t⁻¹ = cayleyInv t := by
      unfold awG cayleyInv
      have ht0' : t ≠ 0 := ht0
      have hd1 : 1 - t ≠ 0 := sub_ne_zero.mpr ht1.symm
      have hd2 : t⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr hti1
      field_simp [ht0', hd1, hd2]
    rw [show F t⁻¹ = f t⁻¹ from congrFun hF _, hfForm _ hti1, hc, inv_div]

end TakhtajanTeo

#print axioms TakhtajanTeo.grp25b_chart
