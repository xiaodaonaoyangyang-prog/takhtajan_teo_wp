import TakhtajanTeo.Ch1.HomogeneousCompleted
import TakhtajanTeo.Ch1.BeltramiCompose

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Abstract tail of `wAS_eq_of_wB_eq`: a continuous sphere bijection preserving the complement of the closed disc,
conformal there (in the chart `1/z`), and fixing `-1, -i, 1`, is the identity on the circle. -/
theorem sphere_circle_id {Csph : ExtPlane → ExtPlane} (hCcont : Continuous Csph)
    (hCinj : Function.Injective Csph)
    (hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p ∉ toExt (closedBall (0 : ℂ) 1))
    (hCsurj : ∀ p' ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p = p')
    (hdiff' : DifferentiableOn ℂ (fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))))) unitDisc)
    (hfix1 : Csph ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane))
    (hfixI : Csph ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane))
    (hfix2 : Csph ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)) :
    ∀ ζ : ℂ, ‖ζ‖ = 1 → Csph (ζ : ExtPlane) = (ζ : ExtPlane) := by
  have hσc : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ → ℂ, c = fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) := ⟨_, rfl⟩
  rw [← hcdef] at hdiff'
  have hc1 : ∀ w ∈ unitDisc, mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))) =
      ((c w : ℂ) : ExtPlane) ∧ c w ∈ unitDisc := by
    intro w hw
    obtain ⟨y, hy, hyD⟩ := sigma_of_not_closed (hCnot _ (sigma_not_closed hw))
    have hcy : c w = y := by
      rw [hcdef]
      show finPart (mobiusExt 0 1 1 0 (Csph _)) = y
      rw [hy]
      rfl
    exact ⟨by rw [hcy]; exact hy, hcy ▸ hyD⟩
  have hcinj : InjOn c unitDisc := by
    intro w1 hw1 w2 hw2 h
    have e1 := (hc1 w1 hw1).1
    have e2 := (hc1 w2 hw2).1
    rw [h] at e1
    have := hCinj (hσi (e1.trans e2.symm))
    exact OnePoint.coe_injective (hσi this)
  have hcsurj : c '' unitDisc = unitDisc := by
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact (hc1 w hw).2
    · intro y hy
      obtain ⟨p, hpn, hp⟩ := hCsurj _ (sigma_not_closed hy)
      obtain ⟨w, hwp, hwD⟩ := sigma_of_not_closed hpn
      refine ⟨w, hwD, ?_⟩
      have e := (hc1 w hwD).1
      rw [← hwp, sigma_invol, hp, sigma_invol] at e
      exact (OnePoint.coe_injective e).symm
  obtain ⟨A, B, C, D, hdet, heq⟩ :=
    exists_mobius_of_isConformalOnto_unitDisc ⟨hdiff', hcinj, hcsurj⟩
  have hmc : Continuous (mobiusExt A B C D) := continuous_mobiusExt hdet
  have hZ : {x : ℂ | C * x + D = 0}.Subsingleton := by
    intro x hx y hy
    have hx' : C * x + D = 0 := hx
    have hy' : C * y + D = 0 := hy
    by_cases hC : C = 0
    · exfalso
      rw [hC, zero_mul, zero_add] at hx'
      apply hdet
      rw [hC, hx']
      ring
    · have : C * (x - y) = 0 := by linear_combination hx' - hy'
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hC)
  have hZd : Dense ({x : ℂ | C * x + D = 0}ᶜ) := Set.Countable.dense_compl ℂ hZ.finite.countable
  have hagree : EqOn (fun p => mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 p))) (mobiusExt A B C D)
      (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ)) := by
    rintro _ ⟨w, ⟨hw, hwZ⟩, rfl⟩
    have hwD : w ∈ unitDisc := hw
    show mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))) = _
    rw [(hc1 w hwD).1, mobiusExt_coe hwZ, heq hwD]
  have hcl : EqOn (fun p => mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 p))) (mobiusExt A B C D)
      (closure (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ))) :=
    EqOn.closure hagree (hσc.comp (hCcont.comp hσc)) hmc
  have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 → mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (ζ : ExtPlane))) =
      mobiusExt A B C D (ζ : ExtPlane) := by
    intro ζ hζ
    apply hcl
    have h1 : ζ ∈ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) := by
      have hsub : ball (0 : ℂ) 1 ⊆ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) :=
        hZd.open_subset_closure_inter isOpen_ball
      have : closure (ball (0 : ℂ) 1) ⊆ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) :=
        closure_minimal hsub isClosed_closure
      apply this
      rw [closure_ball _ one_ne_zero]
      exact mem_closedBall_zero_iff.2 hζ.le
    exact (image_closure_subset_closure_image OnePoint.continuous_coe) ⟨ζ, h1, rfl⟩
  have hid : ∀ p, mobiusExt 1 0 0 1 p = p := by
    intro p
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z =>
      rw [mobiusExt_coe (by simp)]
      congr 1
      simp [mobiusFn]
  have hI0 : (-I : ℂ) ≠ 0 := neg_ne_zero.2 Complex.I_ne_zero
  have hMid : mobiusExt A B C D = mobiusExt 1 0 0 1 := by
    refine mobius_eq_of_three_points (p₁ := -1) (p₂ := I) (p₃ := 1) ⟨A, B, C, D, hdet, rfl⟩
      ⟨1, 0, 0, 1, by norm_num, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h
      have := congrArg Complex.re h
      norm_num at this
    · norm_num
    · intro h
      have := congrArg Complex.re h
      norm_num at this
    · rw [← hcirc (-1) (by simp), sigma_coe (by norm_num), hid]
      have : ((-1 : ℂ)⁻¹) = -1 := by norm_num
      rw [this, hfix1, sigma_coe (by norm_num), this]
    · rw [← hcirc I (by simp), sigma_coe Complex.I_ne_zero, hid]
      have : (I : ℂ)⁻¹ = -I := by simp
      rw [this, hfixI, sigma_coe hI0]
      simp
    · rw [← hcirc 1 (by simp), sigma_coe one_ne_zero, hid]
      rw [inv_one, hfix2, sigma_coe one_ne_zero, inv_one]
  intro ζ hζ
  have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.1 (by rw [hζ]; exact one_ne_zero)
  have h1 := hcirc ζ⁻¹ (by rw [norm_inv, hζ]; simp)
  rw [hMid, hid, sigma_coe (inv_ne_zero hζ0), inv_inv] at h1
  have h2 := congrArg (mobiusExt 0 1 1 0) h1
  rw [sigma_invol, sigma_coe (inv_ne_zero hζ0), inv_inv] at h2
  exact h2

theorem sphere_c_continuousOn {Csph : ExtPlane → ExtPlane} (hCcont : Continuous Csph)
    (hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p ∉ toExt (closedBall (0 : ℂ) 1)) :
    ContinuousOn (fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))))) unitDisc := by
  have hσc : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
  have hcoe : ∀ w ∈ unitDisc, ((finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) : ℂ) :
      ExtPlane) = mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))) := by
    intro w hw
    obtain ⟨y, hy, -⟩ := sigma_of_not_closed (hCnot _ (sigma_not_closed hw))
    rw [hy]
    rfl
  have hct : Continuous (fun p : ExtPlane => mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 p))) :=
    hσc.comp (hCcont.comp hσc)
  rw [OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.continuousOn_iff]
  refine (hct.comp OnePoint.continuous_coe).continuousOn.congr ?_
  intro w hw
  exact hcoe w hw

theorem eq19_exists_mu {h : ℂ → ℂ} {K : ℝ} {e : ℂ ≃ₜ ℂ} (hH : IsKQC (⇑e) univ K)
    (hHc : e '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1) (hHh : EqOn (⇑e) h unitCircle)
    (hm1 : h (-1) = -1) (hmI : h (-I) = -I) (h1 : h 1 = 1) :
    ∃ μ : LinfStar, μ ∈ LinfStarBall ∧ ∀ z : ℂ, ‖z‖ = 1 → wA μ z = h z := by
  have hK1 : (1 : ℝ) ≤ K := hH.2.1
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk1 : (K - 1) / (K + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hDo : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hbd0 := (isKQC_maxDilatation_le hH).2
  have hbd : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖complexDilatation (⇑e) z‖ ≤ (K - 1) / (K + 1) :=
    ae_restrict_of_ae_restrict_of_subset (subset_univ _) hbd0
  have hmeas : AEStronglyMeasurable (complexDilatation (⇑e)) (volume.restrict unitDiscExterior) :=
    (thm10_2_genHomeoSolution_of_isKQC hH).1.1.mono_measure
      (Measure.restrict_mono (subset_univ _) le_rfl)
  have hmem : MemLp (complexDilatation (⇑e)) ∞ (volume.restrict unitDiscExterior) :=
    memLp_top_of_bound hmeas _ hbd
  obtain ⟨μ, hμdef⟩ : ∃ μ : LinfStar, μ = toLinf (complexDilatation (⇑e)) := ⟨_, rfl⟩
  have hμae : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] complexDilatation (⇑e) := by
    rw [hμdef]
    exact bc_toLinf_ae hmem
  have hμ : μ ∈ LinfStarBall := by
    change μ ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, hμdef]
    exact lt_of_le_of_lt (norm_toLinf_le_of_ae_bound hk0 hbd) hk1
  refine ⟨μ, hμ, ?_⟩
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

theorem weldingPrime_congr_h {h h' f g : ℂ → ℂ} (hh : EqOn h h' unitCircle) (hw : IsWeldingPrime h f g) :
    IsWeldingPrime h' f g := by
  obtain ⟨⟨F, G, hF, hFs, hFf, hG, hGs, hGg, hb⟩, hrest⟩ := hw
  exact ⟨⟨F, G, hF, hFs, hFf, hG, hGs, hGg, fun z hz => by rw [← hh hz]; exact hb z hz⟩, hrest⟩

theorem eq_1_9_surj_core {h : ℂ → ℂ} (hh : IsNormalizedQS h) :
    ∃ p : T1, EqOn (wA (Quotient.out p : LinfStarBall)) h unitCircle := by
  obtain ⟨H, ⟨K, hK⟩, hHs, hHc, hHh⟩ := circle_quasisymmetric_plane_extension hh.1
  obtain ⟨e, rfl⟩ := t1_homeomorph hK hHs
  obtain ⟨μ, hμ, hwA⟩ := eq19_exists_mu hK hHc hHh hh.2.1 hh.2.2.1 hh.2.2.2
  refine ⟨Phi ⟨μ, hμ⟩, fun z hz => ?_⟩
  have h2 : teichSetoid.r (Phi ⟨μ, hμ⟩).out ⟨μ, hμ⟩ := Quotient.mk_out (s := teichSetoid) ⟨μ, hμ⟩
  exact (h2 z hz).trans (hwA z hz)

theorem eq_1_9_homeo_cand :
    (∀ p : T1, IsNormalizedQS (wA (Quotient.out p : LinfStarBall))) ∧
      (∀ p q : T1, EqOn (wA (Quotient.out p : LinfStarBall)) (wA (Quotient.out q : LinfStarBall)) unitCircle →
        p = q) ∧
      ∀ h, IsNormalizedQS h → ∃ p : T1, EqOn (wA (Quotient.out p : LinfStarBall)) h unitCircle := by
  refine ⟨fun p => ?_, fun p q hpq => ?_, fun h hh => eq_1_9_surj_core hh⟩
  · have hμ := (Quotient.out p : LinfStarBall).property
    obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hμ
    refine ⟨⟨wA_circle_sensePreserving hμ, wA_circle_quasisymmetric hμ⟩, ?_, ?_, ?_⟩
    · show finPart (wAS _ ((-1 : ℂ) : ExtPlane)) = -1
      rw [hm1]; rfl
    · show finPart (wAS _ ((-I : ℂ) : ExtPlane)) = -I
      rw [hmI]; rfl
    · show finPart (wAS _ ((1 : ℂ) : ExtPlane)) = 1
      rw [hm2]; rfl
  · have h2 : teichSetoid.r (Quotient.out p : LinfStarBall) (Quotient.out q : LinfStarBall) := hpq
    rw [← Quotient.out_eq p, ← Quotient.out_eq q]
    exact Quotient.sound h2

theorem eq_1_9_classD_cand :
    (∀ p : T1, fB (Quotient.out p : LinfStarBall) ∈ ClassDtilde) ∧
      (∀ p q : T1, EqOn (fB (Quotient.out p : LinfStarBall)) (fB (Quotient.out q : LinfStarBall)) unitDisc →
        p = q) ∧
      ∀ h, IsNormalizedQS h → ∀ f g, IsWeldingPrime h f g →
        ∃ p : T1, EqOn (fB (Quotient.out p : LinfStarBall)) f unitDisc := by
  refine ⟨fun p => ?_, fun p q hpq => ?_, fun h hh f g hw => ?_⟩
  · have hμ := (Quotient.out p : LinfStarBall).property
    obtain ⟨hd, hi⟩ := fB_holomorphic_injective hμ
    obtain ⟨H, hH1, hH2, hH3⟩ := fB_hasQCExtension_closed hμ
    exact ⟨hd, hi, (fB_normalization _).1, (fB_normalization _).2.1,
      ⟨H, hH1, hH2, fun z hz => hH3 (ball_subset_closedBall hz)⟩⟩
  · have h2 := modelB_to_modelA (Quotient.out p : LinfStarBall) (Quotient.out q : LinfStarBall) hpq
    have h3 : teichSetoid.r (Quotient.out p : LinfStarBall) (Quotient.out q : LinfStarBall) := h2
    rw [← Quotient.out_eq p, ← Quotient.out_eq q]
    exact Quotient.sound h3
  · obtain ⟨p, hp⟩ := eq_1_9_surj_core hh
    refine ⟨p, ?_⟩
    have hμ := (Quotient.out p : LinfStarBall).property
    have hw0 := weldingPrime_congr_h hp (normalizedWeldingPrime_actual hμ)
    exact (conformal_welding_prime_unique ⟨hh.1, hh.2.2.2⟩ hw0 hw).1

/-! ### Originals relocated from `S1_2` (2026-10-25) -/

/-- **(1.9)** (TT:602–617), left map. `[μ] ↦ w^μ|𝔻` embeds `T(1)` in `𝒟̃`; its image is the set of the functions `f`
of the weldings of the normalized `h ∈ Möb(S¹)\Homeo_qs(S¹)`.
- **[CORRECTION 2026-10-25]** TT's bijection `T(1) ≅ 𝒟` fails: the normalization `f''(0) = 0` is not always
  attainable by a finite-valued holomorphic `f` (see `IsNormalizedB`). With the normalization `w^μ(∞) = ∞`, the
  functions `f^μ = w^μ|𝔻` lie in `𝒟̃`, the map `[μ] ↦ f^μ` is injective, and its image consists of the functions `f`
  of the weldings `(f, g)` of normalized `h`. -/
theorem eq_1_9_classD :
    (∀ p : T1, fB (Quotient.out p : LinfStarBall) ∈ ClassDtilde) ∧
      (∀ p q : T1, EqOn (fB (Quotient.out p : LinfStarBall)) (fB (Quotient.out q : LinfStarBall)) unitDisc → p = q) ∧
      ∀ h, IsNormalizedQS h → ∀ f g, IsWeldingPrime h f g →
        ∃ p : T1, EqOn (fB (Quotient.out p : LinfStarBall)) f unitDisc :=
  eq_1_9_classD_cand

/-- **(1.9)** (TT:602–620), right map. `[μ] ↦ w_μ|S¹` is a bijection of `T(1)` onto `Möb(S¹)\Homeo_qs(S¹)` (maps
compared on `S¹`). It is a group isomorphism (`wA_mul`). -/
theorem eq_1_9_homeo :
    (∀ p : T1, IsNormalizedQS (wA (Quotient.out p : LinfStarBall))) ∧
      (∀ p q : T1, EqOn (wA (Quotient.out p : LinfStarBall)) (wA (Quotient.out q : LinfStarBall)) unitCircle → p = q) ∧
      ∀ h, IsNormalizedQS h → ∃ p : T1, EqOn (wA (Quotient.out p : LinfStarBall)) h unitCircle :=
  eq_1_9_homeo_cand

end TakhtajanTeo
