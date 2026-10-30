import TakhtajanTeo.Ch1.HilbertBersInverse

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1
/-- The actual Cui increment estimate at every Beltrami base point in the unit ball. -/
theorem hcr_increment_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {k : ℝ} (hk : k < 2) :
    ∃ C > 0, ∀ φ : A2 unitDisc, ‖A2toAInf φ‖ ≤ k →
      normA2 unitDisc (AInf.toFun (bersPhi (beltramiMul (Lambda (A2toAInf φ)) μ) - bersPhi μ)) ≤
        ENNReal.ofReal C * (‖φ‖₊ : ℝ≥0∞) := by
  obtain ⟨k', hk'⟩ : ∃ k' : ℝ, k' = max (k / 2) 0 := ⟨_, rfl⟩
  have hk'0 : 0 ≤ k' := by rw [hk']; exact le_max_right _ _
  have hk'1 : k' < 1 := by rw [hk']; exact max_lt (by linarith) one_pos
  have hk'q : 0 < 1 - k' ^ 2 := by nlinarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 144 * (4 * π) / (π * (1 - k' ^ 2)) := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hc]; have : 0 < 1 - k' ^ 2 := by nlinarith
    positivity
  refine ⟨2 * Real.sqrt c, by positivity, fun φ hφ => ?_⟩
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = Lambda (A2toAInf φ) := ⟨_, rfl⟩
  rw [← hωdef]
  have hωn : ‖ω‖ ≤ k' := by
    rw [hωdef, Lambda_norm_eq, hk']
    exact le_max_of_le_left (by linarith)
  have hωb : ω ∈ LinfStarBall := mem_ball_zero_iff.mpr (hωn.trans_lt hk'1)
  let W := QCV.qcv_planeSolution μ
  let F := QCV.qcv_planeSolution (beltramiMul ω μ) ∘ Function.invFunOn W univ
  let ν := complexDilatation F
  let ρs : ℂ → ℝ := fun u =>
    (∫⁻ y in W '' unitDisc, ENNReal.ofReal (1 / ‖u - y‖ ^ 4)).toReal
  obtain ⟨K, hF, hFs⟩ := l29b_F_qc hμ hωb
  obtain ⟨hFΩ, hS⟩ := l29b_plane_schwarzian hμ hωb
  have hfd := QCV.qcv_planeSolution_conformal hμ
  have hI : ∀ u ∈ interior ((W '' unitDisc)ᶜ),
      ∫⁻ y in W '' unitDisc, ENNReal.ofReal (1 / ‖u - y‖ ^ 4) ≤
        ENNReal.ofReal (1 * ρs u) := by
    intro u hu
    simpa only [one_mul] using (ENNReal.ofReal_toReal (l29b_kernel_finite hμ hu)).ge
  have hcui := CUI.cui_disc_bound hk'0 hk'1 (by norm_num : (0 : ℝ) ≤ 1)
    hfd.1 hfd.2.1 hF hFs hFΩ (l29b_qc_equation hF)
    ((l29b_F_bound hμ hωb).mono fun u hu => hu.trans hωn)
    (l29b_plane_frontier_null hμ) ρs hI
  have hL2 : ∫⁻ u in unitDiscExterior, (‖ω u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u) =
      (2 * (‖φ‖₊ : ℝ≥0∞)) ^ 2 := by
    have h := l29b_Lambda_L2 φ
    rw [← hωdef] at h
    unfold normL2 at h
    rw [← h, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hR : (∫⁻ u in (W '' unitDisc)ᶜ, (‖ν u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (ρs u)) ≤
      ENNReal.ofReal (4 * π) * (2 * (‖φ‖₊ : ℝ≥0∞)) ^ 2 := by
    rw [← hL2]
    refine le_trans (lintegral_mono fun u => mul_le_mul' le_rfl ENNReal.ofReal_toReal_le)
      (l29b_plane_energy hμ hωb)
  have hLHS : normA2 unitDisc (AInf.toFun (bersPhi (beltramiMul ω μ) - bersPhi μ)) =
      (∫⁻ z in unitDisc, (‖schwarzianHol (F ∘ W) z - schwarzianHol W z‖₊ : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (rho z)⁻¹) ^ (1 / 2 : ℝ) := by
    unfold normA2
    congr 1
    apply setLIntegral_congr_fun measurableSet_ball
    intro z hz
    beta_reduce
    rw [hS z hz]
  rw [hLHS]
  have hest : (∫⁻ z in unitDisc,
      (‖schwarzianHol (F ∘ W) z - schwarzianHol W z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹) ≤
      ENNReal.ofReal c * (2 * (‖φ‖₊ : ℝ≥0∞)) ^ 2 := by
    refine (hcui.trans (mul_le_mul' le_rfl hR)).trans_eq ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [hc]
    ring
  calc _ ≤ (ENNReal.ofReal c * (2 * (‖φ‖₊ : ℝ≥0∞)) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hest (by norm_num)
    _ = ENNReal.ofReal (2 * Real.sqrt c) * (‖φ‖₊ : ℝ≥0∞) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ENNReal.ofReal_rpow_of_nonneg hc0.le (by norm_num), ← Real.sqrt_eq_rpow,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
      ring

-- L2
/-- The concrete Hilbert Bers chart is A2-valued and holomorphic for every base point. -/
theorem hcr_chart_regular (μ : LinfStarBall) :
    (∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
      AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ) ∈ A2fun unitDisc) ∧
    DifferentiableOn ℂ (hib_chart μ) (ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) := by
  obtain ⟨F, hFdef⟩ : ∃ F : A2 unitDisc → AInf unitDisc, ∀ φ, F φ =
      bersPhi (beltramiMul (Lambda (A2toAInf φ)) (μ : LinfStar)) - bersPhi μ := ⟨_, fun _ => rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (π / 3) := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 < r := by rw [hr]; positivity
  have hFeq : ∀ φ ∈ ball (0 : A2 unitDisc) r,
      bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ = F φ := fun φ hφ => by
    rw [hFdef, ctb_bers_chartInv μ (ct_A2toAInf_norm_lt (hr ▸ hφ))]
  have hGd : DifferentiableOn ℂ (fun φ => bersPhi (beltramiMul (Lambda (A2toAInf φ)) (μ : LinfStar)))
      (ball (0 : A2 unitDisc) r) :=
    (ctb_G_diff μ).comp A2toAInfCLM.differentiableOn
      (fun φ hφ => mem_ball_zero_iff.mpr (ct_A2toAInf_norm_lt (hr ▸ hφ)))
  have hF : DifferentiableOn ℂ F (ball (0 : A2 unitDisc) r) := by
    have := hGd.sub (differentiableOn_const (bersPhi (μ : LinfStar)))
    exact this.congr (fun φ _ => hFdef φ)
  have hbd : ∀ x ∈ ball (0 : A2 unitDisc) r, ∃ ρ > 0, ∃ M : ℝ, ∀ y ∈ ball x ρ,
      y ∈ ball (0 : A2 unitDisc) r ∧ normA2 unitDisc (AInf.toFun (F y)) ≤ ENNReal.ofReal M := by
    intro x hx
    have hnx : ‖A2toAInf x‖ < 2 := ct_A2toAInf_norm_lt (hr ▸ hx)
    obtain ⟨C, hC, hCb⟩ := hcr_increment_bound μ.2 (k := (‖A2toAInf x‖ + 2) / 2) (by linarith)
    have hk : ‖A2toAInf x‖ < (‖A2toAInf x‖ + 2) / 2 := by linarith
    have hxr : ‖x‖ < r := mem_ball_zero_iff.mp hx
    obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ‖A2toAInfCLM‖ := ⟨_, rfl⟩
    have hL0 : 0 ≤ L := by rw [hL]; exact norm_nonneg A2toAInfCLM
    refine ⟨min (r - ‖x‖) (((‖A2toAInf x‖ + 2) / 2 - ‖A2toAInf x‖) / (L + 1)), ?_, C * r, ?_⟩
    · apply lt_min (by linarith)
      apply div_pos (by linarith) (by linarith)
    · intro y hy
      have hd : dist y x < min (r - ‖x‖) (((‖A2toAInf x‖ + 2) / 2 - ‖A2toAInf x‖) / (L + 1)) :=
        mem_ball.mp hy
      have hd1 : dist y x < r - ‖x‖ := lt_of_lt_of_le hd (min_le_left _ _)
      have hd2 : dist y x < ((‖A2toAInf x‖ + 2) / 2 - ‖A2toAInf x‖) / (L + 1) :=
        lt_of_lt_of_le hd (min_le_right _ _)
      have hyx : ‖y - x‖ = dist y x := (dist_eq_norm y x).symm
      have hyU : y ∈ ball (0 : A2 unitDisc) r := by
        rw [mem_ball_zero_iff]
        have := norm_le_norm_add_norm_sub' y x
        linarith
      refine ⟨hyU, ?_⟩
      have hyk : ‖A2toAInf y‖ ≤ (‖A2toAInf x‖ + 2) / 2 := by
        have e1 : A2toAInf y = A2toAInf x + A2toAInfCLM (y - x) := by
          rw [map_sub]; simp
        have e2 : ‖A2toAInfCLM (y - x)‖ ≤ L * ‖y - x‖ := by
          rw [hL]; exact A2toAInfCLM.le_opNorm _
        have e3 : L * ‖y - x‖ ≤ (L + 1) * ‖y - x‖ := by
          apply mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        have e4 : (L + 1) * ‖y - x‖ ≤ (‖A2toAInf x‖ + 2) / 2 - ‖A2toAInf x‖ := by
          rw [hyx]
          have := (lt_div_iff₀ (by linarith : (0:ℝ) < L + 1)).mp hd2
          linarith
        have e5 := norm_add_le (A2toAInf x) (A2toAInfCLM (y - x))
        rw [e1]
        linarith
      have h1 := hCb y hyk
      have h2 : normA2 unitDisc (AInf.toFun (F y)) ≤ ENNReal.ofReal C * (‖y‖₊ : ℝ≥0∞) := by
        rw [hFdef]; exact h1
      refine h2.trans ?_
      have hyr : ‖y‖ ≤ r := (mem_ball_zero_iff.mp hyU).le
      have : (‖y‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖y‖ := by
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
      rw [this, ← ENNReal.ofReal_mul hC.le]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hyr hC.le)
  have hmem : ∀ x ∈ ball (0 : A2 unitDisc) r, AInf.toFun (F x) ∈ A2fun unitDisc := by
    intro x hx
    obtain ⟨ρ, hρ, M, hM⟩ := hbd x hx
    refine ⟨(F x).2, ?_⟩
    exact lt_of_le_of_lt (hM x (mem_ball_self hρ)).2 ENNReal.ofReal_lt_top
  have hH := ctb_holo_of_bounded isOpen_ball hF hmem hbd
  refine ⟨fun φ hφ => ?_, hH.congr (fun φ hφ => ?_)⟩
  · rw [hFeq φ hφ]; exact hmem φ hφ
  · rw [hib_chart, hFeq φ hφ]

-- L3
/-- Strict differentiability throughout the actual Hilbert chart, without a groupO premise. -/
theorem hcr_chart_strict (μ : LinfStarBall) {x : A2 unitDisc}
    (hx : x ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :
    HasStrictFDerivAt (hib_chart μ) (fderiv ℂ (hib_chart μ) x) x := by
  exact bh_hasStrictFDerivAt isOpen_ball (hcr_chart_regular μ).2 hx

-- L4
/-- The derivative at the center is the actual bounded Hilbert Bers operator. -/
theorem hcr_chart_fderiv_zero (μ : LinfStarBall) :
    fderiv ℂ (hib_chart μ) 0 = hbL2_bersOperator μ := by
  let G : A2 unitDisc → A2 unitDisc := fun φ =>
    toA2 unitDisc (AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ))
  let J : A2 unitDisc →L[ℂ] LinfStar :=
    ((Submodule.subtypeL harmonicBeltrami).comp LambdaEquiv.toContinuousLinearMap).comp A2toAInfCLM
  have hJ : ∀ φ, J φ = Lambda (A2toAInf φ) := fun _ => rfl
  have h0 : (0 : A2 unitDisc) ∈ ball 0 (Real.sqrt (π / 3)) := mem_ball_self (by positivity)
  obtain ⟨hmem, hdiff⟩ := hcr_chart_regular μ
  have hG : DifferentiableAt ℂ G 0 := hdiff.differentiableAt (isOpen_ball.mem_nhds h0)
  have hdirect : HasFDerivAt
      (fun φ => bersPhi (beltramiMul (J φ) (μ : LinfStar)) - bersPhi μ)
      (hbL2_ambient μ) 0 := by
    have hb : HasFDerivAt (fun l => bersPhi (beltramiMul l (μ : LinfStar))) (D0BersR μ) (J 0) := by
      simpa using hb_D0BersR_hasFDerivAt μ.2
    exact (hb.comp 0 J.hasFDerivAt).sub_const _
  have hev : (fun φ => bersPhi (beltramiMul (J φ) (μ : LinfStar)) - bersPhi μ) =ᶠ[𝓝 0]
      (A2toAInfCLM ∘ G) := by
    filter_upwards [isOpen_ball.mem_nhds h0] with φ hφ
    change _ = A2toAInf (toA2 unitDisc (AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ)))
    rw [ctb_A2toAInf_toA2 (hmem φ hφ), ctb_bers_chartInv μ (ct_A2toAInf_norm_lt hφ), hJ]
  have hcomp : A2toAInfCLM.comp (fderiv ℂ G 0) = hbL2_ambient μ :=
    (A2toAInfCLM.hasFDerivAt.comp 0 hG.hasFDerivAt).unique (hdirect.congr_of_eventuallyEq hev.symm)
  apply ContinuousLinearMap.ext
  intro φ
  apply A2toAInf_injective
  have hh := congrArg (fun L : A2 unitDisc →L[ℂ] AInf unitDisc => L φ) hcomp
  exact hh.trans (hbL2_bersOperator_spec μ φ).symm

-- L5
/-- The strict derivative at the center, valid for every Beltrami coefficient in the ball. -/
theorem hcr_chart_strict_zero (μ : LinfStarBall) :
    HasStrictFDerivAt (hib_chart μ) (hbL2_bersOperator μ) 0 := by
  have h := hcr_chart_strict μ (x := 0) (mem_ball_self (by positivity))
  rw [hcr_chart_fderiv_zero μ] at h
  exact h

end TakhtajanTeo
