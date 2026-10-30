import TakhtajanTeo.Ch2.S4PullbackVariation
import TakhtajanTeo.Ch1.S2Core

/-! # Smooth representatives of the actual moving-base coefficient (`s4pv_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- P5
theorem s4pv_actual_chart {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    ∃ (U : Set ℂ) (J : ℂ → ℂ), IsOpen U ∧ AnalyticOnNhd ℂ J U ∧
      MapsTo J U unitDiscExterior ∧ (∀ y ∈ U, deriv J y ≠ 0) ∧
      ∀ x ∈ unitDiscExterior, wAS κ (x : ExtPlane) ≠ extInf →
        qcv_planeSolution κ x ∈ U ∧ J (qcv_planeSolution κ x) = wA κ x := by
  obtain ⟨a, b, c, d, hdet, -, hfac⟩ := S2C.s2c_mobius hκ
  let M := mobiusFn a b c d
  let G := gsans κ '' unitDiscExterior
  let V : Set ℂ := {y | c * y + d ≠ 0}
  let U : Set ℂ := V ∩ M ⁻¹' G
  let J := Function.invFunOn (gsans κ) unitDiscExterior ∘ M
  have hg := S2C.s2c_conf_g hκ
  have hG : IsOpen G := hg.isOpen wp_exterior_isOpen
  have hi := hg.symm wp_exterior_isOpen
  have hV : IsOpen V := isOpen_ne_fun (continuous_const.mul continuous_id |>.add continuous_const)
    continuous_const
  have hMd : DifferentiableOn ℂ M V := fun y hy =>
    (bc_mobiusFn_hasDerivAt hy).differentiableAt.differentiableWithinAt
  have hU : IsOpen U := hMd.continuousOn.isOpen_inter_preimage hV hG
  have hmap : MapsTo M U G := fun y hy => hy.2
  have hJd : DifferentiableOn ℂ J U := hi.1.comp (hMd.mono inter_subset_left) hmap
  refine ⟨U, J, hU, hJd.analyticOnNhd hU, ?_, ?_, ?_⟩
  · intro y hy
    exact Function.invFunOn_mem hy.2
  · intro y hy
    have hdM := bc_mobiusFn_hasDerivAt (a := a) (b := b) hy.1
    have hdI := hi.1.differentiableAt (hG.mem_nhds hy.2)
    have hnI := deriv_ne_zero_of_injOn hG hi.1 hi.2.1 hy.2
    have he : deriv J y = deriv (Function.invFunOn (gsans κ) unitDiscExterior) (M y) *
        ((a * d - b * c) / (c * y + d) ^ 2) := by
      exact (hdI.hasDerivAt.comp y hdM).deriv
    rw [he]
    exact mul_ne_zero hnI (div_ne_zero hdet (pow_ne_zero _ hy.1))
  · intro x hx hp
    obtain ⟨hden, hvalue⟩ := hfac x hx hp
    have hw : wA κ x ∈ unitDiscExterior := by
      rcases wAS_maps_ext hκ hx with h | ⟨u, hu, hxu⟩
      · exact (hp h).elim
      · change 1 < ‖finPart (wAS κ (x : ExtPlane))‖
        rw [hxu, finPart_coe]
        exact hu
    have hv : M (qcv_planeSolution κ x) = gsans κ (wA κ x) := hvalue.symm
    refine ⟨⟨hden, ?_⟩, ?_⟩
    · exact ⟨wA κ x, hw, hv.symm⟩
    · change Function.invFunOn (gsans κ) unitDiscExterior (M (qcv_planeSolution κ x)) = _
      rw [hv]
      exact hg.2.1.leftInvOn_invFunOn hw

-- P6
theorem s4pv_dot_chart_ae {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (ν : LinfStar)
    {U : Set ℂ} {J : ℂ → ℂ} (hJ : AnalyticOnNhd ℂ J U)
    (hchart : ∀ x ∈ unitDiscExterior, wAS κ (x : ExtPlane) ≠ extInf →
      qcv_planeSolution κ x ∈ U ∧ J (qcv_planeSolution κ x) = wA κ x) :
    ∀ᵐ x : ℂ ∂(volume.restrict unitDiscExterior), wAS κ (x : ExtPlane) ≠ extInf →
      ahT_dot (extB (qcv_rightDerivative κ ν)) (extB κ) (qcv_planeSolution κ)
        (qcv_planeSolution κ x) =
      ν (wA κ x) * conj (deriv J (qcv_planeSolution κ x)) / deriv J (qcv_planeSolution κ x) := by
  obtain ⟨K, hK⟩ := (qcv_W_props (bc_norm_lt_one hκ)).1.1
  have hN := s23_c2_ae_good hK
  rw [Measure.restrict_univ] at hN
  filter_upwards [ae_restrict_of_ae hN, ae_restrict_of_ae (bc_wA_ae hκ),
    qcv_rightDerivative_ae hκ ν, LinfStar_ae_norm_le κ,
    ae_restrict_mem wp_exterior_isOpen.measurableSet] with x hn hw hD hk hx
  intro hp
  have hNz : dz (qcv_planeSolution κ) x ≠ 0 := by
    intro hzero
    have hlt := hn.2.1
    change ‖dzbar (qcv_planeSolution κ) x‖ < ‖dz (qcv_planeSolution κ) x‖ at hlt
    rw [hzero, norm_zero] at hlt
    exact (not_lt_of_ge (norm_nonneg _)) hlt
  have heq : (J ∘ qcv_planeSolution κ) =ᶠ[𝓝 x] wA κ := by
    filter_upwards [(wp_exterior_isOpen.inter (S2C.s2c_pole_open κ)).mem_nhds
      (show x ∈ unitDiscExterior ∩ {y : ℂ | wAS κ (y : ExtPlane) ≠ extInf} from ⟨hx, hp⟩)] with y hy
    exact (hchart y hy.1 hy.2).2
  have hchain : deriv J (qcv_planeSolution κ x) * dz (qcv_planeSolution κ) x = dz (wA κ) x :=
    ((eq6_5 hn.1 (hJ _ (hchart x hx hp).1).differentiableAt).1).symm.trans
      ((t203_c1_dz_congr heq).1)
  have hJz : deriv J (qcv_planeSolution κ x) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hchain
    exact hw.2.1 hchain.symm
  have hδ : 1 - conj (κ x) * κ x ≠ 0 := by
    intro hzero
    have hn' := congrArg norm (sub_eq_zero.mp hzero)
    rw [norm_one, norm_mul, norm_conj] at hn'
    have hsmall := hk.trans_lt (bc_norm_lt_one hκ)
    nlinarith [norm_nonneg (κ x)]
  have hρ : (1 - (‖κ x‖ : ℂ) ^ 2) = 1 - conj (κ x) * κ x := by
    rw [mul_comm (conj (κ x)) (κ x), Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hinv := (qcv_planeSolution_bijective hκ).1.injOn.leftInvOn_invFunOn (mem_univ x)
  simp only [ahT_dot, hinv, extB, indicator_of_mem hx]
  rw [hD, hρ, ← hchain, map_mul]
  field_simp [hδ, hNz, hJz]

-- P7
theorem s4pv_plane_exterior_isOpen {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    IsOpen (qcv_planeSolution κ ''
      {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}) := by
  obtain ⟨K, hK⟩ := (qcv_W_props (bc_norm_lt_one hκ)).1.1
  exact isOpen_image_of_continuousOn_injOn
    (wp_exterior_isOpen.inter (S2C.s2c_pole_open κ))
    (hK.2.2.1.1.mono (subset_univ _)) (qcv_planeSolution_bijective hκ).1.injOn

-- P8
theorem s4pv_dot_smooth_rep {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    ∃ m : ℂ → ℂ,
      ahT_dot (extB (qcv_rightDerivative κ ν)) (extB κ) (qcv_planeSolution κ) =ᵐ[volume] m ∧
      IsBeltramiCoeff m univ (‖qcv_rightDerivative κ ν‖ / (1 - ‖κ‖ ^ 2)) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m
        (qcv_planeSolution κ ''
          {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}) := by
  obtain ⟨U, J, hU, hJ, hmap, hJzero, hchart⟩ := s4pv_actual_chart hκ
  obtain ⟨r, hr, hνr⟩ := wr_harm_rep hν
  let V := qcv_planeSolution κ ''
    {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}
  let R : ℂ → ℂ := fun y => r (J y) * conj (deriv J y) / deriv J y
  let m₀ := ahT_dot (extB (qcv_rightDerivative κ ν)) (extB κ) (qcv_planeSolution κ)
  let m : ℂ → ℂ := fun y => if y ∈ V then R y else m₀ y
  have hVU : V ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hchart x hx.1 hx.2).1
  have hJs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J U :=
    (hJ.contDiffOn hU.uniqueDiffOn).restrict_scalars ℝ
  have hDs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) U :=
    (hJ.deriv.contDiffOn hU.uniqueDiffOn).restrict_scalars ℝ
  have hCs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => conj (deriv J y)) U :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hDs
  have hIs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (deriv J y)⁻¹) U :=
    ((hJ.deriv.inv hJzero).contDiffOn hU.uniqueDiffOn).restrict_scalars ℝ
  have hRs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R U := by
    dsimp only [R]
    simp only [div_eq_mul_inv]
    exact ((hr.comp hJs hmap).mul hCs).mul hIs
  have hsrc : ∀ᵐ x : ℂ ∂(volume.restrict unitDiscExterior),
      wAS κ (x : ExtPlane) ≠ extInf → m₀ (qcv_planeSolution κ x) = R (qcv_planeSolution κ x) := by
    filter_upwards [s4pv_dot_chart_ae hκ ν hJ hchart, bc_pullback_ae hκ hνr,
      ae_restrict_mem wp_exterior_isOpen.measurableSet] with x hx hrx hxE
    intro hp
    dsimp only [m₀]
    rw [hx hp, hrx]
    simp only [R, (hchart x hxE hp).2]
  have hN := (qcv_W_props (bc_norm_lt_one hκ)).1
  have hloc : ∀ᵐ y : ℂ, y ∈ V → m₀ y = R y := by
    filter_upwards [(ahT_qmp_inv hN.1 hN.2.1).ae
      ((ae_restrict_iff' wp_exterior_isOpen.measurableSet).mp hsrc)] with y hy
    rintro ⟨x, hx, rfl⟩
    have hinv := (qcv_planeSolution_bijective hκ).1.injOn.leftInvOn_invFunOn (mem_univ x)
    simp only [qcv_planeSolution] at hinv hy
    rw [hinv] at hy
    exact hy hx.1 hx.2
  have he : m₀ =ᵐ[volume] m := by
    filter_upwards [hloc] with y hy
    by_cases hv : y ∈ V
    · exact (hy hv).trans (ite_eq_left hv).symm
    · exact (ite_eq_right hv).symm
  refine ⟨m, he, wr_isBC_congr (qcv_base_dot_isBeltramiCoeff hκ _) he, ?_⟩
  exact (hRs.mono hVU).congr (fun y hy => ite_eq_left hy)

end Ch2
end TakhtajanTeo
