import TakhtajanTeo.Ch1.HilbertPreimageMetric
import TakhtajanTeo.Ch1.HilbertChosenReflection
import TakhtajanTeo.Ch1.HilbertBersPreimageAssembly
import TakhtajanTeo.Ch1.Eq22ReproducingFinal

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Push a disk quadratic differential to the actual interior welding domain. -/
theorem hbSurj_target {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {P : ℂ → ℂ} (hP : P ∈ A2fun unitDisc) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q (fsans μ '' unitDisc) ∧
      (∀ w ∈ unitDisc, q (fsans μ w) * deriv (fsans μ) w ^ 2 = P w) ∧
      (∫⁻ v in fsans μ '' unitDisc,
        ENNReal.ofReal (‖q v‖ ^ 2 / poincareDensity (fsans μ '' unitDisc) v ^ 2)) < ∞ := by
  let f := fsans μ
  let Ω := f '' unitDisc
  have hf := S2C.s2c_conf_f hμ
  have hΩ : IsOpen Ω := hf.isOpen isOpen_ball
  let F := Function.invFunOn f unitDisc
  have hF : IsConformalOnto F Ω unitDisc := hf.symm isOpen_ball
  let q : ℂ → ℂ := fun v => P (F v) * deriv F v ^ 2
  have hq : DifferentiableOn ℂ q Ω :=
    (hP.1.comp hF.1 hF.mapsTo).mul ((hF.1.deriv hΩ).pow 2)
  have he : ∀ w ∈ unitDisc, q (f w) * deriv f w ^ 2 = P w := by
    intro w hw
    have hi := t1_deriv_invFunOn_mul isOpen_ball hf hw
    change deriv (Function.invFunOn f unitDisc) (f w) * deriv f w = 1 at hi
    dsimp only [q, F]
    rw [hf.2.1.leftInvOn_invFunOn hw]
    calc P w * deriv (Function.invFunOn f unitDisc) (f w) ^ 2 * deriv f w ^ 2 =
        P w * (deriv (Function.invFunOn f unitDisc) (f w) * deriv f w) ^ 2 := by ring
      _ = P w := by rw [hi]; ring
  refine ⟨q, hq, he, ?_⟩
  rw [eq22_pullback_mass hf]
  have hm : (∫⁻ w in unitDisc, (‖P w‖₊ : ℝ≥0∞)^2 * ENNReal.ofReal (rho w)⁻¹) < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1/2)).mp hP.2
  convert hm using 1
  apply setLIntegral_congr_fun isOpen_ball.measurableSet
  intro w hw
  change (‖q (f w) * deriv f w ^ 2‖₊ : ℝ≥0∞)^2 * ENNReal.ofReal (rho w)⁻¹ = _
  rw [he w hw]

/-- The SAME chosen reflection supplies an essentially bounded and finite-L2
coefficient after the exterior conformal pullback. -/
theorem hbSurj_raw {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (fsans μ '' unitDisc))
    (hq2 : (∫⁻ v in fsans μ '' unitDisc,
      ENNReal.ofReal (‖q v‖ ^ 2 / poincareDensity (fsans μ '' unitDisc) v ^ 2)) < ∞) :
    ∃ h : ℂ → ℂ,
      IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h ∧
      MemLp (hbPre_pullback (hbPre_reflected q h) (gsans μ)) ∞ (volume.restrict unitDiscExterior) ∧
      normL2 unitDiscExterior (hbPre_pullback (hbPre_reflected q h) (gsans μ)) < ∞ := by
  have hf := S2C.s2c_conf_f hμ
  have hg := S2C.s2c_conf_g hμ
  have hΩ := hf.isOpen isOpen_ball
  have hE := hg.isOpen resolvent_exterior_isOpen
  obtain ⟨h, C0, hC0, hh, hC1, hbounded⟩ := hc6_chosen_raw_coefficient hμ
  obtain ⟨M, hM, hqbound⟩ := eq22_A2_weighted_sup hf hq hq2
  obtain ⟨hbmem, hbnd⟩ := hbounded q M hM hq hqbound
  have hbc : ContinuousOn (hbPre_reflected q h) (gsans μ '' unitDiscExterior) := by
    unfold hbPre_reflected
    exact ((continuousOn_const.mul (hq.continuousOn.comp hC1.continuousOn hh.2.1)).mul
      ((continuousOn_id.sub hC1.continuousOn).pow 2)).mul
      (continuousOn_dz_dzbar hC1 hE).2
  have hdne : ∀ w ∈ unitDiscExterior, deriv (gsans μ) w ≠ 0 :=
    fun w hw => deriv_ne_zero_of_injOn resolvent_exterior_isOpen hg.1 hg.2.1 hw
  have hdc := (hg.1.deriv resolvent_exterior_isOpen).continuousOn
  have hac : ContinuousOn (hbPre_pullback (hbPre_reflected q h) (gsans μ)) unitDiscExterior :=
    (hbc.comp hg.1.continuousOn hg.mapsTo).mul
      ((continuous_conj.comp_continuousOn hdc).div hdc hdne)
  have hamem : MemLp (hbPre_pullback (hbPre_reflected q h) (gsans μ)) ∞
      (volume.restrict unitDiscExterior) := by
    apply memLp_top_of_bound (hac.aestronglyMeasurable resolvent_exterior_isOpen.measurableSet)
      (M*C0/2)
    filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with w hw
    rw [hbPre_pullback_norm (hdne w hw)]
    exact hbnd _ (hg.mapsTo hw)
  obtain ⟨C, hC, hprod⟩ := hr6_reflection_density_product hμ hh
  obtain ⟨K, hK⟩ := hh.1
  have hρ : ∀ v ∈ fsans μ '' unitDisc, 0 < poincareDensity (fsans μ '' unitDisc) v ^ 2 := by
    intro v hv
    exact sq_pos_of_pos (s20l_a2_density_pos hΩ (hf.symm isOpen_ball) hv)
  have hmass := hbPre_reflected_mass (q := q) hK hh.2.1 hρ hC.le
    (fun u hu => (hprod u hu).2)
  have hfinite : (∫⁻ u in gsans μ '' unitDiscExterior,
      ENNReal.ofReal (‖hbPre_reflected q h u‖ ^ 2 *
        poincareDensityNearInfty (gsans μ '' unitDiscExterior) u ^ 2)) < ∞ :=
    hmass.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hq2)
  have he : (∫⁻ w in unitDiscExterior,
      (‖hbPre_pullback (hbPre_reflected q h) (gsans μ) w‖₊ : ℝ≥0∞)^2 *
        ENNReal.ofReal (rho w)) =
      ∫⁻ u in gsans μ '' unitDiscExterior, ENNReal.ofReal (‖hbPre_reflected q h u‖ ^ 2 *
        poincareDensityNearInfty (gsans μ '' unitDiscExterior) u ^ 2) := by
    calc _ = ∫⁻ w in unitDiscExterior,
        ENNReal.ofReal (‖hbPre_pullback (hbPre_reflected q h) (gsans μ) w‖ ^ 2) *
          ENNReal.ofReal (rho w) := by
            simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
      _ = _ := (hbPre_pullback_mass resolvent_exterior_isOpen hg).trans (by
        apply setLIntegral_congr_fun hE.measurableSet
        intro u hu
        dsimp only
        rw [← hbSurj_exterior_density hμ hu, ENNReal.ofReal_mul (sq_nonneg _)])
  refine ⟨h, hh, hamem, ?_⟩
  unfold normL2
  rw [he]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfinite.ne

/-- Every actual target A2 differential has a harmonic L2 preimage. -/
theorem hbSurj_harmonic_preimage {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {P : ℂ → ℂ} (hP : P ∈ A2fun unitDisc) :
    ∃ ν ∈ harmonicL2 unitDiscExterior,
      EqOn (AInf.toFun (D0BersR μ (toLinf ν))) P unitDisc := by
  obtain ⟨q, hq, hqp, hq2⟩ := hbSurj_target hμ hP
  obtain ⟨h, hh, hraw, hL2⟩ := hbSurj_raw hμ hq hq2
  have hmass : (∫⁻ v in fsans μ '' unitDisc, (‖q v‖₊ : ℝ≥0∞)^2 *
      ENNReal.ofReal (poincareDensity (fsans μ '' unitDisc) v ^ 2)⁻¹) < ∞ := by
    convert hq2 using 1
    apply setLIntegral_congr_fun ((S2C.s2c_conf_f hμ).isOpen isOpen_ball).measurableSet
    intro v hv
    dsimp only
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg ‖q v‖),
      ENNReal.ofReal_pow (norm_nonneg (q v)), ofReal_norm, enorm_eq_nnnorm]
  obtain ⟨ν, hν, he, -⟩ := hbPre_reflection_preimage hμ q h
    (fun z hz => eq22_reproducing hμ hh hq hmass hz) hraw hL2
  exact ⟨ν, hν, fun w hw => (he w hw).trans (hqp w hw)⟩

/-- Surjectivity holds for every coefficient in the unit ball, without a groupO premise. -/
theorem hbSurj_bersOperator (μ : LinfStarBall) : Function.Surjective (hbL2_bersOperator μ) := by
  intro φ
  have hφ : AInf.toFun (A2toAInf φ) ∈ A2fun unitDisc := by
    refine ⟨(A2toAInf φ).property, ?_⟩
    rw [← l29b_nnnorm_eq]
    exact ENNReal.coe_lt_top
  obtain ⟨ν, hν, he⟩ := hbSurj_harmonic_preimage μ.2 hφ
  obtain ⟨ψ, hψ, -⟩ := hbL2_harmonic_coordinate hν
  refine ⟨ψ, A2toAInf_injective ?_⟩
  rw [hbL2_bersOperator_spec, hψ]
  exact AInf.ext_of_toFun_eqOn (fun z hz => (mem_ball_zero_iff.mp hz).ne) he

#print axioms hbSurj_target
#print axioms hbSurj_raw
#print axioms hbSurj_harmonic_preimage
#print axioms hbSurj_bersOperator
end TakhtajanTeo
