import TakhtajanTeo.Ch1.S5AnalyticImplicit

/-! Joint real analyticity of the original uniformizer and its hyperbolic metric. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem s5cf_joint_vertical_deriv_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E × ℂ → ℂ} {p : E} {z : ℂ} (ha : AnalyticAt ℂ F (p, z)) :
    AnalyticAt ℂ (fun q : E × ℂ => deriv (fun w => F (q.1, w)) q.2) (p, z) := by
  have hEval : AnalyticAt ℂ (fun q : E × ℂ => fderiv ℂ F q (0, 1)) (p, z) :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0 : E), (1 : ℂ))).analyticAt _).comp_of_eq ha.fderiv rfl
  apply hEval.congr
  filter_upwards [ha.eventually_analyticAt] with q hq
  exact (s5cf_vertical_fderiv hq.differentiableAt).symm

-- L2
theorem s5cf_diagonal_analytic (μ : LinfStar) (ζ : ℂ) :
    AnalyticAt ℝ (fun q : LinfStar × ℂ => ((q.1, star q.1), q.2)) (μ, ζ) := by
  have hs : AnalyticAt ℝ (fun q : LinfStar × ℂ => star q.1) (μ, ζ) :=
    (s5cf_star_analytic μ).comp_of_eq analyticAt_fst rfl
  exact (analyticAt_fst.prod hs).prod analyticAt_snd

-- L3
theorem s5cf_eventuallyEq_vertical_deriv {X : Type*} [TopologicalSpace X]
    {F G : X × ℂ → ℂ} {q₀ : X × ℂ} (he : F =ᶠ[𝓝 q₀] G) :
    (fun q : X × ℂ => deriv (fun w => F (q.1, w)) q.2) =ᶠ[𝓝 q₀]
      (fun q : X × ℂ => deriv (fun w => G (q.1, w)) q.2) := by
  filter_upwards [he.eventually_nhds] with q hq
  change F =ᶠ[𝓝 q] G at hq
  have hs : ContinuousAt (fun w : ℂ => (q.1, w)) q.2 := by fun_prop
  have hslice : (fun w => F (q.1, w)) =ᶠ[𝓝 q.2] fun w => G (q.1, w) := hq.comp_tendsto hs
  exact hslice.deriv_eq

-- L4
theorem s5cf_uniformizer_parameter_analytic {μ : LinfStar} {ζ : ℂ} (hμ : μ ∈ LinfStarBall)
    (hζ : ζ = 0 ∨ ∃ w ∈ unitDiscExterior, ζ = (gMu μ w)⁻¹) :
    AnalyticAt ℝ (fun q : LinfStar × ℂ => fiberUniformizer q.1 q.2) (μ, ζ) ∧
      AnalyticAt ℝ (fun q : LinfStar × ℂ => deriv (fiberUniformizer q.1) q.2) (μ, ζ) := by
  obtain ⟨ht, hval⟩ := s5cf_uniformizer_inverse_data hμ hζ
  have hH0 : s5cf_exterior_reciprocal (μ, star μ) (fiberUniformizer μ ζ) = ζ :=
    (s5cf_gchart_eq hμ ht).symm.trans hval
  obtain ⟨G, hGa, hG0, hGr, _⟩ := s5cf_analytic_implicit
    (s5cf_exterior_reciprocal_analytic hμ ht) (s5cf_exterior_reciprocal_deriv_ne_zero hμ ht)
  change AnalyticAt ℂ G ((μ, star μ), s5cf_exterior_reciprocal (μ, star μ) (fiberUniformizer μ ζ)) at hGa
  change G ((μ, star μ), s5cf_exterior_reciprocal (μ, star μ) (fiberUniformizer μ ζ)) = fiberUniformizer μ ζ at hG0
  change ∀ᶠ q in 𝓝 ((μ, star μ), s5cf_exterior_reciprocal (μ, star μ) (fiberUniformizer μ ζ)),
    s5cf_exterior_reciprocal q.1 (G q) = q.2 at hGr
  rw [hH0] at hGa hG0 hGr
  have hJ := s5cf_diagonal_analytic μ ζ
  have hGc : AnalyticAt ℝ (fun q : LinfStar × ℂ => G ((q.1, star q.1), q.2)) (μ, ζ) :=
    hGa.restrictScalars.comp_of_eq hJ rfl
  have hGs : ∀ᶠ q : LinfStar × ℂ in 𝓝 (μ, ζ), G ((q.1, star q.1), q.2) ∈ unitDisc :=
    hGc.continuousAt.eventually (isOpen_ball.mem_nhds (by
      change G ((μ, star μ), ζ) ∈ unitDisc
      rw [hG0]
      exact ht))
  have hright : ∀ᶠ q : LinfStar × ℂ in 𝓝 (μ, ζ),
      s5cf_exterior_reciprocal (q.1, star q.1) (G ((q.1, star q.1), q.2)) = q.2 :=
    hJ.continuousAt.eventually hGr
  have he : (fun q : LinfStar × ℂ => G ((q.1, star q.1), q.2)) =ᶠ[𝓝 (μ, ζ)]
      (fun q : LinfStar × ℂ => fiberUniformizer q.1 q.2) := by
    filter_upwards [(continuous_fst.tendsto (μ, ζ)).eventually (isOpen_ball.mem_nhds hμ), hGs, hright]
      with q hqμ hqt hqr
    have hi := s5cf_uniformizer_left hqμ hqt
    rw [s5cf_gchart_eq hqμ hqt, hqr] at hi
    exact hi.symm
  refine ⟨hGc.congr he, ?_⟩
  have hDa : AnalyticAt ℝ (fun q : LinfStar × ℂ =>
      deriv (fun w => G ((q.1, star q.1), w)) q.2) (μ, ζ) :=
    (s5cf_joint_vertical_deriv_analytic hGa).restrictScalars.comp_of_eq hJ rfl
  exact hDa.congr (s5cf_eventuallyEq_vertical_deriv he)

-- L5
theorem s5cf_norm_sq_real_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun q => ‖f q‖ ^ 2) x := by
  have hre := (Complex.reCLM.analyticAt (f x)).comp_of_eq hf rfl
  have him := (Complex.imCLM.analyticAt (f x)).comp_of_eq hf rfl
  convert! (hre.mul hre).add (him.mul him) using 1
  funext q
  exact Complex.sq_norm (f q)

-- L6
theorem s5cf_metric_parameter_analytic {μ : LinfStar} {ζ : ℂ} (hμ : μ ∈ LinfStarBall)
    (hζ : ζ = 0 ∨ ∃ w ∈ unitDiscExterior, ζ = (gMu μ w)⁻¹) :
    AnalyticAt ℝ (fun q : LinfStar × ℂ => Real.log (4 * ‖deriv (fiberUniformizer q.1) q.2‖ ^ 2 /
      (1 - ‖fiberUniformizer q.1 q.2‖ ^ 2) ^ 2)) (μ, ζ) := by
  obtain ⟨hG, hD⟩ := s5cf_uniformizer_parameter_analytic hμ hζ
  obtain ⟨_, hv, hd⟩ := s5fg_uniformizer_regular hμ hζ
  have hsq : 0 < 1 - ‖fiberUniformizer μ ζ‖ ^ 2 := by nlinarith [norm_nonneg (fiberUniformizer μ ζ)]
  have hn := s5cf_norm_sq_real_analytic hD
  have hb := s5cf_norm_sq_real_analytic hG
  have hnum : AnalyticAt ℝ (fun q : LinfStar × ℂ => 4 * ‖deriv (fiberUniformizer q.1) q.2‖ ^ 2) (μ, ζ) :=
    analyticAt_const.mul hn
  have hden : AnalyticAt ℝ (fun q : LinfStar × ℂ => (1 - ‖fiberUniformizer q.1 q.2‖ ^ 2) ^ 2) (μ, ζ) :=
    (analyticAt_const.sub hb).pow 2
  have hrat := hnum.div hden (pow_ne_zero 2 hsq.ne')
  have hp : 0 < 4 * ‖deriv (fiberUniformizer μ) ζ‖ ^ 2 / (1 - ‖fiberUniformizer μ ζ‖ ^ 2) ^ 2 :=
    div_pos (mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hd) _)) (pow_pos hsq _)
  convert! (analyticAt_log hp).comp_of_eq hrat rfl using 1

end TakhtajanTeo

