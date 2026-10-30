import TakhtajanTeo.Ch1.TcChart
import TakhtajanTeo.Ch1.QCVariation
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Analytic parameter bridges for the characteristic forms of the universal curve. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem s5wr_inverse_bers (p : T1) : Function.invFunOn bers univ (bers p) = p :=
  bers_isOpenEmbedding.injective.injOn.leftInvOn_invFunOn (mem_univ p)

theorem s5wr_inverse_translation (ν : LinfStarBall)
    (hi : beltramiInv (ν : LinfStar) ∈ LinfStarBall)
    (hcomp : rightTrans ⟨beltramiInv (ν : LinfStar), hi⟩ ∘ rightTrans ν = id)
    {χ : AInf unitDisc} (hχ : χ ∈ ball 0 2) :
    bers (rightTrans ⟨beltramiInv (ν : LinfStar), hi⟩
      (Function.invFunOn bers univ (bersPhi (beltramiMul (Lambda χ) ν)))) = χ := by
  obtain ⟨hΛ, hAW⟩ := QCV.qs_AW (mem_ball_zero_iff.mp hχ)
  have hp : bersPhi (beltramiMul (Lambda χ) ν) = bers (rightTrans ν (Phi ⟨Lambda χ, hΛ⟩)) := by
    rw [bt_rightTrans_phi, bers_Phi]
  rw [hp, s5wr_inverse_bers]
  have he := congrFun hcomp (Phi ⟨Lambda χ, hΛ⟩)
  change rightTrans ⟨beltramiInv (ν : LinfStar), hi⟩ (rightTrans ν (Phi ⟨Lambda χ, hΛ⟩)) = Phi ⟨Lambda χ, hΛ⟩ at he
  rw [he, bers_Phi, hAW]

theorem s5wr_G_local_inverse {ν : LinfStar} (hν : ν ∈ LinfStarBall) :
    ∃ L : AInf unitDisc → AInf unitDisc,
      DifferentiableOn ℂ L (range bers) ∧ L (bersPhi ν) = 0 ∧
      ∀ᶠ χ in 𝓝 (bersPhi ν), L χ ∈ ball (0 : AInf unitDisc) 2 ∧
        bersPhi (beltramiMul (Lambda (L χ)) ν) = χ := by
  let hi : beltramiInv ν ∈ LinfStarBall := bc_beltramiInv_mem_ball hν
  have hId := bsub_rightTrans_differentiableOn ⟨beltramiInv ν, hi⟩
  have hcomp : rightTrans ⟨beltramiInv ν, hi⟩ ∘ rightTrans ⟨ν, hν⟩ = id :=
    funext (bt_rightTrans_inv_left ⟨ν, hν⟩ hi)
  let L : AInf unitDisc → AInf unitDisc :=
    bers ∘ rightTrans ⟨beltramiInv ν, hi⟩ ∘ Function.invFunOn bers univ
  obtain ⟨L0, _, hL0, hev⟩ := bsub_G_local_inverse hν
  have he : L =ᶠ[𝓝 (bersPhi ν)] L0 := by
    filter_upwards [hev] with χ hχ
    have hh := s5wr_inverse_translation ⟨ν, hν⟩ hi hcomp hχ.1
    change L (bersPhi (beltramiMul (Lambda (L0 χ)) ν)) = L0 χ at hh
    rwa [hχ.2] at hh
  refine ⟨L, hId, (he.self_of_nhds).trans hL0, ?_⟩
  filter_upwards [hev, he] with χ hχ heχ
  rw [heχ]
  exact hχ

theorem s5wr_section (p : T1) :
    ∃ s : AInf unitDisc → LinfStar, ∃ U : Set (AInf unitDisc),
      IsOpen U ∧ bers p ∈ U ∧ DifferentiableOn ℂ s U ∧
      s (bers p) = ((Quotient.out p : LinfStarBall) : LinfStar) ∧
      ∀ χ ∈ U, ∃ h : s χ ∈ LinfStarBall, bers (Phi ⟨s χ, h⟩) = χ := by
  let ν : LinfStar := (Quotient.out p : LinfStarBall)
  have hν : ν ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hbp : bers p = bersPhi ν := rfl
  obtain ⟨L, hLd, hL0, hev⟩ := s5wr_G_local_inverse hν
  have hO : IsOpen (range bers) := bers_isOpenEmbedding.isOpen_range
  have hm : bersPhi ν ∈ range bers := ⟨p, hbp⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hev.and (hO.mem_nhds hm))
  let s : AInf unitDisc → LinfStar := fun χ => beltramiMul (Lambda (L χ)) ν
  refine ⟨s, ball (bersPhi ν) r, isOpen_ball, by rw [hbp]; exact mem_ball_self hr, ?_, ?_, ?_⟩
  · intro χ hχ
    obtain ⟨hχL, hχr⟩ := hball χ hχ
    have hΛ : Lambda (L χ) ∈ LinfStarBall := Lambda_mem_ball (mem_ball_zero_iff.mp hχL.1)
    exact (((bd_differentiableOn hν).differentiableAt (isOpen_ball.mem_nhds hΛ)).comp χ
      ((Lambda_differentiable (L χ)).comp χ (hLd.differentiableAt (hO.mem_nhds hχr)))).differentiableWithinAt
  · change beltramiMul (Lambda (L (bers p))) ν = ν
    rw [hbp, hL0, glr_lambda_zero, hb_zero_mul hν]
  · intro χ hχ
    obtain ⟨hχL, _⟩ := hball χ hχ
    have hΛ : Lambda (L χ) ∈ LinfStarBall := Lambda_mem_ball (mem_ball_zero_iff.mp hχL.1)
    refine ⟨bg_mul_mem_ball hν hΛ, ?_⟩
    rw [bers_Phi]
    exact hχL.2

theorem s5wr_planeB_curve_analytic {s : ℂ → LinfStar} {U : Set ℂ}
    (hU : IsOpen U) (hs : DifferentiableOn ℂ s U) (hm : MapsTo s U LinfStarBall) (z : ℂ) :
    AnalyticOnNhd ℂ (fun t => normalizedSolution (extB (s t)) z) U := by
  exact ((QCV.qcv_planeB_differentiableOn z).comp hs hm).analyticOnNhd hU

theorem s5wr_section_curve (p : T1) (X : AInf unitDisc) :
    ∃ r > 0, ∃ s : ℂ → LinfStar, AnalyticOnNhd ℂ s (ball 0 r) ∧
      s 0 = ((Quotient.out p : LinfStarBall) : LinfStar) ∧
      ∀ t ∈ ball 0 r, s t ∈ LinfStarBall ∧ bersPhi (s t) = bers p + t • X := by
  obtain ⟨s, U, hU, hp, hd, hs0, he⟩ := s5wr_section p
  have hc : ContinuousAt (fun t : ℂ => bers p + t • X) 0 := by fun_prop
  have hev : ∀ᶠ t : ℂ in 𝓝 0, bers p + t • X ∈ U := by
    exact hc (by simpa using hU.mem_nhds hp)
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨r, hr, fun t => s (bers p + t • X), ?_, by simpa using hs0, ?_⟩
  · exact (hd.comp ((differentiable_const _).add (differentiable_id.smul_const X)).differentiableOn
      (fun t ht => hb t ht)).analyticOnNhd isOpen_ball
  · intro t ht
    obtain ⟨h, hh⟩ := he _ (hb t ht)
    exact ⟨h, by simpa [bers_Phi] using hh⟩

theorem s5wr_uniformizer_jet {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w : ℂ} (hw : w ∈ unitDiscExterior) :
    fiberUniformizer μ (gMu μ w)⁻¹ = w⁻¹ ∧
      HasDerivAt (fiberUniformizer μ) ((gMu μ w) ^ 2 / (w ^ 2 * deriv (gMu μ) w)) (gMu μ w)⁻¹ := by
  have hgi : IsUnivalentAtInfty (gMu μ) := (gMu_isWelding hμ).2.2.2.2.2.2
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hgw := gMu_exterior_ne_zero hμ hw
  have hw0 : w ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hw
  have hd0 : deriv (gMu μ) w ≠ 0 := RMT.deriv_ne_zero_of_injOn hO hgi.1 hgi.2.1 hw
  have hi : Function.invFunOn (gMu μ) unitDiscExterior (gMu μ w) = w :=
    hgi.2.1.leftInvOn_invFunOn hw
  have hs := (hgi.1.analyticAt (hO.mem_nhds hw)).hasStrictDerivAt
  have hleft : ∀ᶠ z in 𝓝 w, Function.invFunOn (gMu μ) unitDiscExterior (gMu μ z) = z := by
    filter_upwards [hO.mem_nhds hw] with z hz
    exact hgi.2.1.leftInvOn_invFunOn hz
  have hinv := (hs.to_local_left_inverse hd0 hleft).hasDerivAt
  have hinv' : HasDerivAt (Function.invFunOn (gMu μ) unitDiscExterior) (deriv (gMu μ) w)⁻¹
      (gMu μ w)⁻¹⁻¹ := by simpa only [inv_inv] using hinv
  have hd := (hinv'.comp (gMu μ w)⁻¹ (hasDerivAt_inv (inv_ne_zero hgw))).inv
    (by simpa only [Function.comp_apply, inv_inv, hi] using hw0)
  have he : (fun z => (Function.invFunOn (gMu μ) unitDiscExterior z⁻¹)⁻¹) =ᶠ[𝓝 (gMu μ w)⁻¹]
      fiberUniformizer μ := by
    filter_upwards [eventually_ne_nhds (inv_ne_zero hgw)] with z hz
    simp [fiberUniformizer, hz]
  refine ⟨by simp [fiberUniformizer, inv_ne_zero hgw, hi], ?_⟩
  convert! hd.congr_of_eventuallyEq he.symm using 1
  simp only [Function.comp_apply, inv_inv, hi]
  field_simp

theorem s5wr_uniformizer_potential {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w : ℂ} (hw : w ∈ unitDiscExterior) :
    Real.log (4 * ‖deriv (fiberUniformizer μ) (gMu μ w)⁻¹‖ ^ 2 /
      (1 - ‖fiberUniformizer μ (gMu μ w)⁻¹‖ ^ 2) ^ 2) / 2 - Real.log 2 =
      Real.log (‖gMu μ w‖ ^ 2 / (‖deriv (gMu μ) w‖ * (‖w‖ ^ 2 - 1))) := by
  obtain ⟨hval, hder⟩ := s5wr_uniformizer_jet hμ hw
  have hgi : IsUnivalentAtInfty (gMu μ) := (gMu_isWelding hμ).2.2.2.2.2.2
  have hgw := gMu_exterior_ne_zero hμ hw
  have hd := RMT.deriv_ne_zero_of_injOn (isOpen_lt continuous_const continuous_norm) hgi.1 hgi.2.1 hw
  have hn : 1 < ‖w‖ := hw
  have hw0 : ‖w‖ ≠ 0 := by linarith
  have hd0 : ‖deriv (gMu μ) w‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have hw2 : 0 < ‖w‖ ^ 2 - 1 := by nlinarith [norm_nonneg w]
  have hR : 0 < ‖gMu μ w‖ ^ 2 / (‖deriv (gMu μ) w‖ * (‖w‖ ^ 2 - 1)) :=
    div_pos (pow_pos (norm_pos_iff.mpr hgw) _) (mul_pos (norm_pos_iff.mpr hd) hw2)
  rw [hval, hder.deriv]
  have he : 4 * ‖(gMu μ w) ^ 2 / (w ^ 2 * deriv (gMu μ) w)‖ ^ 2 / (1 - ‖w⁻¹‖ ^ 2) ^ 2 =
      4 * (‖gMu μ w‖ ^ 2 / (‖deriv (gMu μ) w‖ * (‖w‖ ^ 2 - 1))) ^ 2 := by
    simp only [norm_div, norm_pow, norm_mul, norm_inv]
    field_simp [hw0, hd0, hw2.ne']
  rw [he, Real.log_mul (by norm_num) (pow_ne_zero 2 hR.ne'), Real.log_pow]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    convert Real.log_pow 2 2 using 1 <;> norm_num
  rw [h4]
  ring

theorem s5wr_potential_at_fiber (p : T1) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    potentialK (p, (gMu (Quotient.out p : LinfStarBall) w : ExtPlane)) =
      Real.log (‖gMu (Quotient.out p : LinfStarBall) w‖ ^ 2 /
        (‖deriv (gMu (Quotient.out p : LinfStarBall)) w‖ * (‖w‖ ^ 2 - 1))) := by
  have hμ := (Quotient.out p : LinfStarBall).2
  have hgw := gMu_exterior_ne_zero hμ hw
  simpa [potentialK, logNormSq, inversion, mobiusExt, hgw, finPart] using s5wr_uniformizer_potential hμ hw

theorem s5wr_sigma_inverse_germ {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∀ᶠ z in cocompact ℂ, Function.invFun (sigmaW w) z =
      (w + ((1 - w) / (1 - conj w)) * z⁻¹) /
        (1 + ((1 - w) / (1 - conj w)) * conj w * z⁻¹) := by
  let k : ℂ := (1 - w) / (1 - conj w)
  filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact,
    (isCompact_singleton (x := -(k * conj w))).compl_mem_cocompact] with z hz hd
  have hz' : z ∈ unitDiscExterior := by simpa [unitDiscExterior] using hz
  have hz0 : z ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hz'
  have hden : z + k * conj w ≠ 0 := by simpa [eq_neg_iff_add_eq_zero] using hd
  have hs := sigmaW_invFun_of_finite_inverse hw hz' (sigmaInvSphere_coe_eq hw hden)
  rw [hs]
  have hd' : 1 + k * conj w * z⁻¹ = (z + k * conj w) / z := by field_simp
  change sigmaInv w z = (w + k * z⁻¹) / (1 + k * conj w * z⁻¹)
  rw [hd']
  dsimp [sigmaInv]
  change (k + z * w) / (z + k * conj w) = (w + k * z⁻¹) / ((z + k * conj w) / z)
  field_simp
  ring

theorem s5wr_derivAtInfty_of_reciprocal {g H : ℂ → ℂ} {d : ℂ}
    (hH : HasDerivAt H d 0) (h0 : H 0 = 0) (hd : d ≠ 0)
    (he : ∀ᶠ z in cocompact ℂ, H z⁻¹ = (g z)⁻¹) : derivAtInfty g = d⁻¹ := by
  have ht : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    · filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
      exact inv_ne_zero (by simpa using hz)
  have hh := (hH.tendsto_slope.comp ht).inv₀ hd
  apply Tendsto.limUnder_eq
  apply hh.congr'
  filter_upwards [he] with z hz
  simp [slope_def_field, h0, hz, div_eq_mul_inv, mul_comm]

theorem s5wr_recenter_capacity_norm {g : ℂ → ℂ} {w : ℂ} (hw : w ∈ unitDiscExterior)
    (hg : DifferentiableAt ℂ g w) (hg0 : g w ≠ 0) (hgd : deriv g w ≠ 0) :
    ‖derivAtInfty (fun z => lambdaW (-1 / g w) (g (Function.invFun (sigmaW w) z)))‖ =
      ‖g w‖ ^ 2 / (‖deriv g w‖ * (‖w‖ ^ 2 - 1)) := by
  let k : ℂ := (1 - w) / (1 - conj w)
  let R : ℂ → ℂ := fun t => (w + k * t) / (1 + k * conj w * t)
  let H : ℂ → ℂ := fun t => (g (R t))⁻¹ - (g w)⁻¹
  let d : ℂ := -(deriv g w * (k * (1 - w * conj w))) / (g w) ^ 2
  have hR0 : R 0 = w := by simp [R]
  have hR : HasDerivAt R (k * (1 - w * conj w)) 0 := by
    convert! (((hasDerivAt_id (0 : ℂ)).const_mul k).const_add w).div
      (((hasDerivAt_id (0 : ℂ)).const_mul (k * conj w)).const_add 1) (by norm_num) using 1
    simp
    ring
  have hgR : HasDerivAt g (deriv g w) (R 0) := by rw [hR0]; exact hg.hasDerivAt
  have hH : HasDerivAt H d 0 := by
    convert! ((hgR.comp 0 hR).inv (by simpa only [Function.comp_apply, hR0] using hg0)).sub_const (g w)⁻¹ using 1
    simp [d, hR0]
  have hH0 : H 0 = 0 := by simp [H, hR0]
  have hn : 1 < ‖w‖ := hw
  have hw2 : 0 < ‖w‖ ^ 2 - 1 := by nlinarith [norm_nonneg w]
  have hnorm : ‖(1 : ℂ) - w * conj w‖ = ‖w‖ ^ 2 - 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have he : (1 : ℂ) - ((‖w‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  have hdNorm : ‖d‖ = ‖deriv g w‖ * (‖w‖ ^ 2 - 1) / ‖g w‖ ^ 2 := by
    simp only [d, norm_div, norm_neg, norm_mul, norm_pow, hnorm,
      show ‖k‖ = 1 from wp_sigma_normalizing_norm hw, one_mul]
  have hd : d ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hdNorm]
    exact (div_pos (mul_pos (norm_pos_iff.mpr hgd) hw2) (pow_pos (norm_pos_iff.mpr hg0) _)).ne'
  have ht : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hgn : ∀ᶠ z in cocompact ℂ, g (R z⁻¹) ≠ 0 := by
    have hc := (hgR.comp 0 hR).continuousAt
    have hlim : Tendsto (fun z : ℂ => g (R z⁻¹)) (cocompact ℂ) (𝓝 (g w)) := by
      convert! hc.tendsto.comp ht using 1
      simp [hR0]
    exact hlim.eventually_ne hg0
  have he : ∀ᶠ z in cocompact ℂ, H z⁻¹ =
      (lambdaW (-1 / g w) (g (Function.invFun (sigmaW w) z)))⁻¹ := by
    filter_upwards [s5wr_sigma_inverse_germ hw, hgn] with z hz hgz
    change Function.invFun (sigmaW w) z = R z⁻¹ at hz
    rw [hz]
    change (g (R z⁻¹))⁻¹ - (g w)⁻¹ = (lambdaW (-1 / g w) (g (R z⁻¹)))⁻¹
    rw [lambdaW, inv_div]
    field_simp [hgz, hg0]
    ring
  rw [s5wr_derivAtInfty_of_reciprocal hH hH0 hd he, norm_inv, hdNorm, inv_div]

theorem s5wr_lemma_5_1_formula (p : T1) (w : ℂ) (hw : w ∈ unitDiscExterior) :
    potentialK (p, (gMu (Quotient.out p : LinfStarBall) w : ExtPlane)) =
      Real.log ‖derivAtInfty (fun z => lambdaW (-1 / gMu (Quotient.out p : LinfStarBall) w)
        (gMu (Quotient.out p : LinfStarBall) (Function.invFun (sigmaW w) z)))‖ := by
  have hμ := (Quotient.out p : LinfStarBall).2
  have hg : IsUnivalentAtInfty (gMu (Quotient.out p : LinfStarBall)) := (gMu_isWelding hμ).2.2.2.2.2.2
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  rw [s5wr_potential_at_fiber p hw, s5wr_recenter_capacity_norm hw
    (hg.1.differentiableAt (hO.mem_nhds hw)) (gMu_exterior_ne_zero hμ hw)
    (RMT.deriv_ne_zero_of_injOn hO hg.1 hg.2.1 hw)]

end TakhtajanTeo
