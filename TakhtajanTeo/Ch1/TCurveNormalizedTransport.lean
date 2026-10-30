import TakhtajanTeo.Ch1.TCurveTopGroup

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- A normalized plane extension with the prescribed exterior coefficient
agrees with the actual Model A solution on the entire exterior sphere. -/
theorem tcg_modelA_exterior {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {K : ℝ} (e : ℂ ≃ₜ ℂ) (he : IsKQC (⇑e) univ K)
    (heC : e '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1)
    (hm1 : e (-1) = -1) (hmI : e (-I) = -I) (h1 : e 1 = 1)
    (hae : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] complexDilatation (⇑e)) :
    EqOn (wAS μ) (OnePoint.map e) extDiscExterior := by
  obtain ⟨M, hM, W, hW, hwf, hwi, hwm1, hwmI, hw1⟩ := wA_spec hμ
  obtain ⟨KW, hKW⟩ := hW.1
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  obtain ⟨heCl, heD, heE⟩ := planeHomeomorph_circle_regions e heC
  have hdi : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      complexDilatation W z = complexDilatation (⇑e) z := by
    filter_upwards [ae_restrict_of_ae hW.2.2.2.2, hae, ae_restrict_mem hEo.measurableSet]
      with z hz hμz hzE
    rw [hz, extA_eq_on_exterior μ hzE]
    exact hμz
  have hconf := bg_conformal_of_dilatation_eq
    (ac_t_isKQC_restrict he hEo (subset_univ _))
    (ac_t_isKQC_restrict hKW hEo (subset_univ _)) hdi
  rw [heE] at hconf
  have hinv : ∀ z ∈ unitDiscExterior, Function.invFunOn (⇑e) unitDiscExterior z = e.symm z := by
    intro z hz
    have hz' : z ∈ e '' unitDiscExterior := heE.symm ▸ hz
    obtain ⟨y, hy, rfl⟩ := hz'
    rw [e.injective.injOn.leftInvOn_invFunOn hy, e.symm_apply_apply]
  have hR : DifferentiableOn ℂ (W ∘ e.symm) unitDiscExterior :=
    hconf.1.congr (fun z hz => by simp only [Function.comp_apply, hinv z hz])
  let C : ExtPlane → ExtPlane := fun p => wAS μ (e.onePointCongr.symm p)
  have hcc : Continuous C := (wAS_continuous hμ).comp e.onePointCongr.symm.continuous
  have hcb : Function.Bijective C := (wAS_bijective μ).comp e.onePointCongr.symm.bijective
  have hCe : ∀ p, C (OnePoint.map e p) = wAS μ p := by
    intro p
    change wAS μ (e.onePointCongr.symm (e.onePointCongr p)) = wAS μ p
    rw [e.onePointCongr.symm_apply_apply]
  have hCl : ∀ p, p ∈ toExt (closedBall (0 : ℂ) 1) ↔ C p ∈ toExt (closedBall (0 : ℂ) 1) := by
    intro p
    obtain ⟨x, rfl⟩ := e.onePointCongr.surjective p
    change OnePoint.map e x ∈ toExt (closedBall (0 : ℂ) 1) ↔
      C (OnePoint.map e x) ∈ toExt (closedBall (0 : ℂ) 1)
    rw [hCe, ← tmi_map_iff (tmi_cb_iff heCl) x, ← wAS_closed_iff hμ]
  have hnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), C p ∉ toExt (closedBall (0 : ℂ) 1) :=
    fun p hp h => hp ((hCl p).mpr h)
  have hsurj : ∀ p ∉ toExt (closedBall (0 : ℂ) 1),
      ∃ q ∉ toExt (closedBall (0 : ℂ) 1), C q = p := by
    intro p hp
    obtain ⟨q, rfl⟩ := hcb.2 p
    exact ⟨q, fun h => hp ((hCl q).mp h), rfl⟩
  have hidMob : IsMobius (id : ExtPlane → ExtPlane) :=
    tce_sigma_isMobius (w := extInf) (Or.inr rfl)
  have hform : ∀ p, C p = M (OnePoint.map (W ∘ e.symm) (id p)) := by
    intro p
    induction p using OnePoint.rec with
    | infty => exact hwi
    | coe z => exact hwf (e.symm z)
  have hmaps : ∀ p ∉ toExt (closedBall (0 : ℂ) 1),
      id p = extInf ∨ ∃ z ∈ unitDiscExterior, id p = (z : ExtPlane) := by
    intro p hp
    induction p using OnePoint.rec with
    | infty => exact Or.inl rfl
    | coe z =>
      right
      refine ⟨z, ?_, rfl⟩
      rw [coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le] at hp
      exact hp
  have hd := tmi_hdiff hidMob hM hEo hR hform hmaps hcc hcb.1 hnot
  have hfix : ∀ z : ℂ, e z = z → wAS μ (z : ExtPlane) = (z : ExtPlane) →
      C (z : ExtPlane) = (z : ExtPlane) := by
    intro z hez hwz
    have h := hCe (z : ExtPlane)
    change C ((e z : ℂ) : ExtPlane) = wAS μ (z : ExtPlane) at h
    rwa [hez, hwz] at h
  have hid := (tmi_tail hcc hcb.1 hnot hsurj hd
    (hfix (-1) hm1 hwm1) (hfix (-I) hmI hwmI) (hfix 1 h1 hw1)).2
  intro p hp
  have hep : OnePoint.map e p ∉ toExt (closedBall (0 : ℂ) 1) := by
    rw [fi_extDiscExterior_eq_compl] at hp
    exact fun h => hp ((tmi_map_iff (tmi_cb_iff heCl) p).mpr h)
  have h := hid _ hep
  rwa [hCe] at h

/-- When an extension is the genuine Model A map on the exterior, the
coefficient formula is the actual group quotient, not just an equal class. -/
theorem tcg_lambda_eq_group_of_exterior {μ ν : LinfStar}
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    {K : ℝ} (e : ℂ ≃ₜ ℂ) (he : IsKQC (⇑e) univ K)
    (heE : e '' unitDiscExterior = unitDiscExterior)
    (hmodel : EqOn (wA μ) e unitDiscExterior)
    (hae : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] complexDilatation (⇑e)) :
    tcurveLambda ν e = beltramiMul ν (beltramiInv μ) := by
  have hes : e '' univ = univ := image_univ.trans e.surjective.range_eq
  have hinvE : ∀ z ∈ unitDiscExterior, Function.invFun (⇑e) z ∈ unitDiscExterior := by
    intro z hz
    obtain ⟨x, hx, hxe⟩ := heE.symm ▸ hz
    rw [← hxe, Function.leftInverse_invFun e.injective x]
    exact hx
  have hinv : ∀ z ∈ unitDiscExterior,
      Function.invFun (wA μ) z = Function.invFun (⇑e) z := by
    intro z hz
    have hx := hinvE z hz
    have hv : wA μ (Function.invFun (⇑e) z) = z :=
      (hmodel hx).trans (Function.invFun_eq (e.surjective z))
    have hz0 : z ≠ 0 := by
      intro hez
      have hz1 : 1 < ‖z‖ := hz
      rw [hez, norm_zero] at hz1
      norm_num at hz1
    rw [← hv, bc_invFun_wA (hv.symm ▸ hz0), hv]
  have hphase : ∀ z ∈ unitDiscExterior, dz (wA μ) z = dz (⇑e) z := by
    intro z hz
    have hg : wA μ =ᶠ[𝓝 z] (⇑e) :=
      Filter.eventuallyEq_of_mem (bc_hEo.mem_nhds hz) (fun w hw => hmodel hw)
    exact (t203_c1_dz_congr hg).1
  have hpull := tmi_ae_pull_inv he hes heE hae
  apply Lp.ext
  filter_upwards [(tmi_lambda_props hν he hes heE).2,
    bc_beltramiMul_inv_formula hμ hν, hpull, ae_restrict_mem bc_hEo.measurableSet]
    with z hl hg hμz hz
  rw [hl, hg]
  rw [hinv z hz, hμz, hphase _ (hinvE z hz)]

/-- The normalized extension hypotheses discharge the preceding exterior premise. -/
theorem tcg_lambda_eq_group {μ ν : LinfStar}
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    {K : ℝ} (e : ℂ ≃ₜ ℂ) (he : IsKQC (⇑e) univ K)
    (heC : e '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1)
    (hm1 : e (-1) = -1) (hmI : e (-I) = -I) (h1 : e 1 = 1)
    (hae : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] complexDilatation (⇑e)) :
    tcurveLambda ν e = beltramiMul ν (beltramiInv μ) := by
  apply tcg_lambda_eq_group_of_exterior hμ hν e he
    (planeHomeomorph_circle_regions e heC).2.2 _ hae
  intro z hz
  exact congrArg finPart (tcg_modelA_exterior hμ e he heC hm1 hmI h1 hae (Or.inl ⟨z, hz, rfl⟩))

#print axioms tcg_modelA_exterior
#print axioms tcg_lambda_eq_group
end TakhtajanTeo
