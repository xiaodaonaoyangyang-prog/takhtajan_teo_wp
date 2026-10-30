import TakhtajanTeo.Ch2.S3S1Tilde
import TakhtajanTeo.Ch2.WReg3
import TakhtajanTeo.Ch1.S5RightTranslationHol
import TakhtajanTeo.Appendix.AppACont
import TakhtajanTeo.Appendix.BergmanPeriodModel
import TakhtajanTeo.Ch1.WeldingUniqueness
import TakhtajanTeo.Ch1.S5Thm53Curve
import TakhtajanTeo.Ch1.S5ExteriorChartRegularity
import TakhtajanTeo.Ch1.S5WeldingRegularity

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- Along the off-centre line, `a + t m` and `ν_t = (a + t m) * κ` stay in the ball for small `t`. -/
theorem s35wn_mem {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : ‖a‖ < 1) (μ : LinfStar) :
    ∀ᶠ t in 𝓝 (0 : ℂ), a + t • μ ∈ LinfStarBall ∧ beltramiMul (a + t • μ) κ ∈ LinfStarBall := by
  have hc : Continuous fun t : ℂ => ‖a + t • μ‖ := by fun_prop
  have h0 : ‖a + (0 : ℂ) • μ‖ < 1 := by simpa using ha
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds h0)] with t ht
  have hb : a + t • μ ∈ LinfStarBall := by simpa [LinfStarBall] using ht
  exact ⟨hb, bg_mul_mem_ball hκ hb⟩

/-- `t ↦ (a + t m) * κ` is complex differentiable at `0` (`bd_differentiableOn`). -/
theorem s35wn_nu_diff {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (μ : LinfStar) :
    DifferentiableAt ℂ (fun t : ℂ => beltramiMul (a + t • μ) κ) 0 := by
  have hd : DifferentiableAt ℂ (fun l => beltramiMul l κ) a :=
    (bd_differentiableOn hκ a ha).differentiableAt (isOpen_ball.mem_nhds ha)
  have hl : DifferentiableAt ℂ (fun t : ℂ => a + t • μ) 0 := by fun_prop
  have h0 : a + (0 : ℂ) • μ = a := by simp
  have hd' : DifferentiableAt ℂ (fun l => beltramiMul l κ) (a + (0 : ℂ) • μ) := by rw [h0]; exact hd
  exact DifferentiableAt.comp (g := fun l => beltramiMul l κ) (f := fun t : ℂ => a + t • μ) 0 hd' hl

/-- **The pre-Schwarzian at `0` through the plane solution.** With `W = W_{extB μ}` and the welding pole
`p = (w_μ)⁻¹(∞)`, `𝒜(𝖿)(0) = 2 W'(0)/W(p) + W''(0)/W'(0)` (`s5rh_memoir` at `v = p`). -/
theorem s35wn_fsans {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    preSchwarzian (fsans μ) 0 = 2 * deriv (normalizedSolution (extB μ)) 0 *
        finPart (inversion (OnePoint.map (normalizedSolution (extB μ)) (Function.invFun (wAS μ) extInf))) +
      deriv (deriv (normalizedSolution (extB μ))) 0 / deriv (normalizedSolution (extB μ)) 0 := by
  have hf : fsans μ = fB μ := by
    funext z
    simp [fsans, lambdaW, AppB.b8_weldConst_zero hμ]
  obtain ⟨-, hd1, hp⟩ := fB_normalization μ
  have hpole := hp ⟨_, (wB_spec hμ).1⟩
  have hv := (AppA.acc_wB_rep hμ).2.1
  have hm := s5rh_memoir hμ hv
  have hinf0 : inversion extInf = ((0 : ℂ) : ExtPlane) := by
    rw [← (tcc_inversion_eq_inf_iff ((0 : ℂ) : ExtPlane)).mpr rfl, tcc_inversion_invol]
  rw [hpole, hinf0] at hm
  change (0 : ℂ) + _ = _ at hm
  have hd := s5cf_planeB_deriv_ne_zero hμ
  rw [hf, preSchwarzian, hd1, div_one]
  linear_combination 2 * hm

/-- `𝗀 = g_μ` (welding normalization `c = 0`, `α_μ = id`). -/
theorem s35wn_gsans_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ζ : ℂ) : gsans μ ζ = gMu μ ζ := by
  have hid : Function.invFun (id : ExtPlane → ExtPlane) = id :=
    funext fun z => Function.leftInverse_invFun Function.injective_id z
  show lambdaW (weldConst μ) (gMu μ (finPart (Function.invFun (alphaMu μ) (ζ : ExtPlane)))) = gMu μ ζ
  rw [AppB.b8_weldConst_zero hμ, alphaMu_eq_id, hid]
  simp only [lambdaW, zero_mul, zero_add, div_one]
  rfl

/-- The pole term `1/W_μ(p_μ)`, `p_μ = (w_μ)⁻¹(∞)`, is the reciprocal normalization coordinate at `0`
(`s5cf_planeB_inverse_wAS_reciprocal`), which is real-analytic in `μ` (`s5t53_P_analytic`). -/
theorem s35wn_pole {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    finPart (inversion (OnePoint.map (normalizedSolution (extB μ)) (Function.invFun (wAS μ) extInf))) =
      s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) := by
  have h := s5cf_planeB_inverse_wAS_reciprocal hμ (t := 0) (by simp [unitDisc])
  rw [mobiusExt_coe_of_eq_zero (by norm_num)] at h
  change finPart (mobiusExt 0 1 1 0 _) = _
  rw [h]
  rfl

/-- `𝗀_μ'(∞) = 1/(g^♯_μ)'(0)` with `g^♯_μ(u) = 1/g_μ(1/u)` written through the exterior reciprocal chart
(`s5cf_gchart_eq`). -/
theorem s35wn_derivAtInfty {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    derivAtInfty (gsans μ) = (deriv (fun w => s5cf_exterior_reciprocal (μ, star μ) w) 0)⁻¹ := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hev : s5cf_gchart μ =ᶠ[𝓝 0] fun w => s5cf_exterior_reciprocal (μ, star μ) w := by
    filter_upwards [isOpen_ball.mem_nhds h0] with s hs
    exact s5cf_gchart_eq hμ hs
  rw [← hev.deriv_eq]
  have hHa : HasDerivAt (s5cf_gchart μ) (deriv (s5cf_gchart μ) 0) 0 :=
    (s5cf_gchart_analytic hμ h0).differentiableAt.hasDerivAt
  have hH0 : s5cf_gchart μ 0 = 0 := by
    show (if (0 : ℂ) = 0 then 0 else (gMu μ (0 : ℂ)⁻¹)⁻¹) = 0
    simp
  refine s5wr_derivAtInfty_of_reciprocal hHa hH0 (s5cf_gchart_deriv_ne_zero hμ h0) ?_
  filter_upwards [s5t53_ev_exterior] with z hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num [unitDiscExterior] at hz
  show (if z⁻¹ = 0 then 0 else (gMu μ z⁻¹⁻¹)⁻¹) = (gsans μ z)⁻¹
  rw [ite_eq_right_of_eq_false _ _ (eq_false (inv_ne_zero hz0)), inv_inv, s35wn_gsans_eq hμ z]

/-- `ν ↦ (g^♯_ν)'(0)` is real-analytic on the ball (the exterior reciprocal chart is jointly holomorphic in
`(ν, ν̄, u)`, `s5cf_exterior_reciprocal_analytic`). -/
theorem s35wn_gchart_deriv_analytic {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    AnalyticAt ℝ (fun ν : LinfStar => deriv (fun w => s5cf_exterior_reciprocal (ν, star ν) w) 0) μ := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hc : AnalyticAt ℂ (fun p : LinfStar × LinfStar => deriv (s5cf_exterior_reciprocal p) 0) (μ, star μ) :=
    s5cf_partial_deriv_analytic (F := s5cf_exterior_reciprocal) (s5cf_exterior_reciprocal_analytic hμ h0)
  have hm : AnalyticAt ℝ (fun ν : LinfStar => (ν, star ν)) μ := analyticAt_id.prod (s5cf_star_analytic μ)
  exact hc.restrictScalars.comp_of_eq hm rfl

/-- A function real differentiable at `ν₀ = a * κ` is real differentiable along the off-centre line `t ↦ ν_t`. -/
theorem s35wn_line_diff {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (μ : LinfStar)
    {F : LinfStar → ℂ} (hF : DifferentiableAt ℝ F (beltramiMul a κ)) :
    DifferentiableAt ℝ (fun t : ℂ => F (beltramiMul (a + t • μ) κ)) 0 := by
  have hν : DifferentiableAt ℝ (fun t : ℂ => beltramiMul (a + t • μ) κ) 0 :=
    (s35wn_nu_diff hκ ha μ).restrictScalars ℝ
  have h0 : a + (0 : ℂ) • μ = a := by simp
  have hF' : DifferentiableAt ℝ F (beltramiMul (a + (0 : ℂ) • μ) κ) := by rw [h0]; exact hF
  exact DifferentiableAt.comp (g := F) (f := fun t : ℂ => beltramiMul (a + t • μ) κ) 0 hF' hν

/-- **(W-NORM)** The normalization data of the welding pair are real differentiable along the off-centre line:
`t ↦ 𝒜(𝖿_t)(0) = 𝖿_t''(0)` and `t ↦ 𝗀_t'(∞)`. Here `𝖿_t = M_t ∘ W_t` with `W_t = normalizedSolution (extB ν_t)`
holomorphic in `t` and `M_t` the Möbius map sending the image `q_t = W_t(p_t)` of the Model A pole
`p_t = (w^A_{ν_t})⁻¹(∞)` to `∞`. Route: `q_t = Ŵ_t(h₀(γ_t⁻¹(∞)))` with `γ_t = w^A_{λ_t}`, `λ_t = (a + t m) * a⁻¹`,
`Ŵ_t` holomorphic in `t` with `Ŵ₀ = id` (first-order expansion uniform near `q₀`), and `h₀ = W₀ ∘ (w^A_{ν₀})⁻¹`
conformal on `𝔻*`; `𝗀_t'(∞)` from the Laurent data at `∞` of the same welded maps. -/
theorem s35_wnorm {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {a : LinfStar}
    (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior) :
    DifferentiableAt ℝ (fun t : ℂ => preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) 0) 0 ∧
      DifferentiableAt ℝ (fun t : ℂ => derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ))) 0 := by
  -- the frozen hypotheses `hκ`, `ha`, `haL`, `hm` are not needed: both normalization data are real-analytic
  -- on the whole ball (`s5t53_P_analytic`, `s5cf_planeB_deriv_analytic`, `s5rh_jet2_holo`,
  -- `s35wn_gchart_deriv_analytic`) and `t ↦ ν_t` is holomorphic (`bd_differentiableOn`)
  have _h := And.intro hκ (And.intro ha (And.intro haL hm))
  have ha1 : ‖a‖ < 1 := has.trans delta0_bounds.2
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.mpr ha1
  have hν0 : beltramiMul a κ ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), beltramiMul (a + t • toLinf m) κ ∈ LinfStarBall :=
    (s35wn_mem κ.2 ha1 (toLinf m)).mono fun t ht => ht.2
  have hd0 := s5cf_planeB_deriv_ne_zero hν0
  refine ⟨?_, ?_⟩
  · have hd : DifferentiableAt ℝ (fun ν : LinfStar => deriv (normalizedSolution (extB ν)) 0) (beltramiMul a κ) :=
      (s5cf_planeB_deriv_analytic hν0).differentiableAt.restrictScalars ℝ
    have hP : DifferentiableAt ℝ (fun ν : LinfStar => s5cf_reciprocal (ν, star ν) (s5cf_alpha (ν, star ν) 0))
        (beltramiMul a κ) := (s5t53_P_analytic hν0).differentiableAt
    have hj : DifferentiableAt ℝ (fun ν : LinfStar => deriv (deriv (normalizedSolution (extB ν))) 0)
        (beltramiMul a κ) :=
      ((s5rh_jet2_holo _ hν0).differentiableAt (isOpen_ball.mem_nhds hν0)).restrictScalars ℝ
    have hF := ((hd.const_mul (2 : ℂ)).mul hP).add (hj.mul (hd.inv hd0))
    refine (s35wn_line_diff κ.2 haB (toLinf m) hF).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    simp only [s35wn_fsans ht, s35wn_pole ht, div_eq_mul_inv, Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
  · have hG := (s35wn_gchart_deriv_analytic hν0).differentiableAt.inv
      (s5cf_exterior_reciprocal_deriv_ne_zero hν0 (by simp [unitDisc]))
    refine (s35wn_line_diff κ.2 haB (toLinf m) hG).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    exact s35wn_derivAtInfty ht

end TakhtajanTeo.Ch2
