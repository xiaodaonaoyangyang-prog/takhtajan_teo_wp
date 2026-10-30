import TakhtajanTeo.Ch1.Eq19Completed

/-! Coefficient-retaining normalization of a genuine plane QC circle map.
The sphere-conformal boundary argument is the Eq19 argument, with the
admissible coefficient and its a.e. identity retained as explicit data. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem crc_normalized_boundary {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {h : ℂ → ℂ} {K : ℝ} {e : ℂ ≃ₜ ℂ} (hH : IsKQC (⇑e) univ K)
    (hHc : e '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1)
    (hHh : EqOn (⇑e) h unitCircle)
    (hm1 : h (-1) = -1) (hmI : h (-I) = -I) (h1 : h 1 = 1)
    (hμae : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] complexDilatation (⇑e)) :
    ∀ z : ℂ, ‖z‖ = 1 → wA μ z = h z := by
  have hDo : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨Mμ, hMμ, Wμ, hWμ, hwfμ, hwiμ, hm1', hmI', hm2'⟩ := wA_spec hμ
  obtain ⟨KW, hKW⟩ := hWμ.1
  have hKWD := ac_t_isKQC_restrict hKW hDo (subset_univ _)
  have hKeD := ac_t_isKQC_restrict hH hDo (subset_univ _)
  have hdil : ∀ᵐ z ∂(volume.restrict {w : ℂ | 1 < ‖w‖}),
      complexDilatation Wμ z = complexDilatation (⇑e) z := by
    filter_upwards [ae_restrict_of_ae hWμ.2.2.2.2, hμae, ae_restrict_mem hDo.measurableSet]
      with z h1 h2 hz
    rw [h1, extA_eq_on_exterior μ hz]
    exact h2
  have hψ := bg_conformal_of_dilatation_eq hKeD hKWD hdil
  obtain ⟨hreg1, hreg2, hreg3⟩ := planeHomeomorph_circle_regions e hHc
  have hD : (⇑e) '' {w : ℂ | 1 < ‖w‖} = {w : ℂ | 1 < ‖w‖} := hreg3
  rw [hD] at hψ
  -- the sphere map
  have hE : ∀ u : ℂ, e.onePointCongr (u : ExtPlane) = ((e u : ℂ) : ExtPlane) := fun u => rfl
  have hEs : ∀ u : ℂ, e.onePointCongr.symm (u : ExtPlane) = ((e.symm u : ℂ) : ExtPlane) := by
    intro u
    exact e.onePointCongr.symm_apply_eq.2 (by rw [hE, e.apply_symm_apply])
  have hEinf : e.onePointCongr.symm extInf = extInf :=
    e.onePointCongr.symm_apply_eq.2 rfl
  have hEcl : ∀ q ∈ toExt (closedBall (0 : ℂ) 1), e.onePointCongr q ∈ toExt (closedBall (0 : ℂ) 1) := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨e v, hreg1 ▸ mem_image_of_mem e hv, rfl⟩
  have hEscl : ∀ p ∈ toExt (closedBall (0 : ℂ) 1),
      e.onePointCongr.symm p ∈ toExt (closedBall (0 : ℂ) 1) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hEs]
    rw [← hreg1] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨v, hv, ?_⟩
    rw [e.symm_apply_apply]
  obtain ⟨Csph, hCdef⟩ : ∃ Csph : ExtPlane → ExtPlane,
      Csph = fun p => wAS μ (e.onePointCongr.symm p) := ⟨_, rfl⟩
  have hCcont : Continuous Csph := by
    rw [hCdef]
    exact (wAS_continuous hμ).comp e.onePointCongr.symm.continuous
  have hCinj : Function.Injective Csph := by
    intro p q hpq
    rw [hCdef] at hpq
    exact e.onePointCongr.symm.injective ((wAS_bijective μ).1 hpq)
  have hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p ∉ toExt (closedBall (0 : ℂ) 1) := by
    intro p hp hC
    rw [hCdef] at hC
    have h2 := hEcl _ ((wAS_closed_iff hμ _).2 hC)
    rw [e.onePointCongr.apply_symm_apply] at h2
    exact hp h2
  have hCsurj : ∀ p' ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1),
      Csph p = p' := by
    intro p' hp'
    obtain ⟨q, hq⟩ := (wAS_bijective μ).2 p'
    have hqn : q ∉ toExt (closedBall (0 : ℂ) 1) := by
      intro hqc
      apply hp'
      rw [← hq]
      exact (wAS_closed_iff hμ q).1 hqc
    refine ⟨e.onePointCongr q, ?_, ?_⟩
    · intro hc
      have h5 := hEscl _ hc
      rw [e.onePointCongr.symm_apply_apply] at h5
      exact hqn h5
    · rw [hCdef]
      show wAS μ (e.onePointCongr.symm (e.onePointCongr q)) = p'
      rw [e.onePointCongr.symm_apply_apply, hq]
  have hcirc : ∀ z : ℂ, ‖z‖ = 1 → e z = h z := fun z hz => hHh (show z ∈ unitCircle from hz)
  have hsymm : ∀ z : ℂ, ‖z‖ = 1 → e.symm (h z) = z := by
    intro z hz
    rw [← hcirc z hz, e.symm_apply_apply]
  have hfix1 : Csph ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) := by
    rw [hCdef]
    show wAS μ (e.onePointCongr.symm ((-1 : ℂ) : ExtPlane)) = _
    rw [hEs, ← hm1, hsymm (-1) (by simp), hm1]
    exact hm1'
  have hfixI : Csph ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane) := by
    rw [hCdef]
    show wAS μ (e.onePointCongr.symm ((-I : ℂ) : ExtPlane)) = _
    rw [hEs, ← hmI, hsymm (-I) (by simp), hmI]
    exact hmI'
  have hfix2 : Csph ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
    rw [hCdef]
    show wAS μ (e.onePointCongr.symm ((1 : ℂ) : ExtPlane)) = _
    rw [hEs, ← h1, hsymm 1 (by simp), h1]
    exact hm2'
  -- conformality of `c`
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  have hσ : IsMobius (mobiusExt 0 1 1 0) := ⟨0, 1, 1, 0, by norm_num, rfl⟩
  have hP : IsMobius (fun p => mobiusExt 0 1 1 0 (Mμ p)) := isMobius_comp hMμ hσ
  have hPc := mobius_finite_conformal hP
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ → ℂ, c = fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) := ⟨_, rfl⟩
  have hinvon : ∀ u ∈ {w : ℂ | 1 < ‖w‖}, Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖} u = e.symm u := by
    intro u hu
    rw [← hD] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [e.symm_apply_apply]
    exact (e.injective.injOn).leftInvOn_invFunOn hv
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Set ℂ, Ω = {w | w ∈ unitDisc ∧ w ≠ 0 ∧
      Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf} := ⟨_, rfl⟩
  have hcw : ∀ w ∈ Ω, w⁻¹ ∈ {w : ℂ | 1 < ‖w‖} ∧
      c w = finPart (mobiusExt 0 1 1 0 (Mμ (((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) w⁻¹ : ℂ) :
        ExtPlane))) ∧
      mobiusExt 0 1 1 0 (Mμ (((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) w⁻¹ : ℂ) : ExtPlane)) ≠
        extInf := by
    intro w hw
    rw [hΩ] at hw
    obtain ⟨hwD, hw0, hwne⟩ := hw
    have hwin : w⁻¹ ∈ {w : ℂ | 1 < ‖w‖} := by
      show 1 < ‖w⁻¹‖
      rw [norm_inv]
      have : ‖w‖ < 1 := mem_ball_zero_iff.1 hwD
      exact one_lt_inv₀ (norm_pos_iff.2 hw0) |>.2 this
    have hCw : Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) =
        Mμ (((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) w⁻¹ : ℂ) : ExtPlane) := by
      rw [hCdef]
      show wAS μ (e.onePointCongr.symm (mobiusExt 0 1 1 0 (w : ExtPlane))) = _
      rw [sigma_coe hw0, hEs, Function.comp_apply, hinvon _ hwin]
      exact hwfμ _
    refine ⟨hwin, ?_, ?_⟩
    · rw [hcdef]
      show finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) = _
      rw [hCw]
    · rw [← hCw]
      obtain ⟨y, hy, -⟩ := sigma_of_not_closed (hCnot _ (sigma_not_closed hwD))
      rw [hy]
      exact OnePoint.coe_ne_infty y
  have hdiffΩ : DifferentiableOn ℂ c Ω := by
    have h1 : DifferentiableOn ℂ (fun w : ℂ => w⁻¹) Ω := fun w hw =>
      ((differentiableAt_id.inv (by
        rw [hΩ] at hw
        exact hw.2.1))).differentiableWithinAt
    have h2 : DifferentiableOn ℂ ((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) ∘ fun w : ℂ => w⁻¹) Ω :=
      hψ.1.comp h1 (fun w hw => (hcw w hw).1)
    have h3 := hPc.1.comp h2 (fun w hw => (hcw w hw).2.2)
    refine h3.congr (fun w hw => ?_)
    exact (hcw w hw).2.1
  have hE1 : {w : ℂ | w ∈ unitDisc ∧ Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) = extInf}.Subsingleton := by
    intro w1 h1 w2 h2
    have := hCinj (h1.2.trans h2.2.symm)
    exact OnePoint.coe_injective (hσi this)
  have hEfin : (unitDisc \ Ω).Finite := by
    refine ((Set.finite_singleton (0 : ℂ)).union hE1.finite).subset ?_
    intro w hw
    by_cases h0 : w = 0
    · exact Or.inl h0
    · refine Or.inr ⟨hw.1, ?_⟩
      by_contra hb
      apply hw.2
      rw [hΩ]
      exact ⟨hw.1, h0, hb⟩
  have hdiffc : DifferentiableOn ℂ c unitDisc := by
    refine differentiableOn_of_finite_exceptional (show IsOpen unitDisc from isOpen_ball) hEfin ?_ ?_
    · rw [hcdef]
      exact sphere_c_continuousOn hCcont hCnot
    · refine hdiffΩ.mono ?_
      intro w hw
      by_contra h
      exact hw.2 ⟨hw.1, h⟩
  have hid := sphere_circle_id hCcont hCinj hCnot hCsurj (by rw [← hcdef]; exact hdiffc)
    hfix1 hfixI hfix2
  intro z hz
  have hez : ‖e z‖ = 1 := mem_sphere_zero_iff_norm.1 (hHc ▸ mem_image_of_mem e (mem_sphere_zero_iff_norm.2 hz))
  have h3 := hid (e z) hez
  rw [hCdef] at h3
  have h4 : wAS μ (z : ExtPlane) = ((e z : ℂ) : ExtPlane) := by
    have := h3
    simp only [hEs, e.symm_apply_apply] at this
    exact this
  show finPart (wAS μ (z : ExtPlane)) = h z
  rw [h4, ← hcirc z hz]
  rfl

#print axioms crc_normalized_boundary
end TakhtajanTeo

