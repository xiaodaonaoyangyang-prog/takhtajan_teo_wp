import TakhtajanTeo.Ch1.S2_HilbertManifold
import TakhtajanTeo.Ch1.HarmonicL2Bers
import TakhtajanTeo.Ch2.S2_Remark22
import TakhtajanTeo.Ch1.CuiBound
import TakhtajanTeo.Ch1.BeltramiGroup
import TakhtajanTeo.Ch1.QuasidiskKernel
import TakhtajanTeo.Ch1.S2Core

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## `l29r_restricted`, part (b): base transfer (`l29b_` prefix) -/

/-- The `A₂` norm of an element of `A₂(𝔻)` through its `A∞` image. -/
theorem l29b_nnnorm_eq (ψ : A2 unitDisc) :
    (‖ψ‖₊ : ℝ≥0∞) = normA2 unitDisc (AInf.toFun (A2toAInf ψ)) := by
  rw [← A2.norm_toFun]
  exact normA2_congr measurableSet_ball (fun z hz => ((A2toAInf_bounded.2 ψ).2 z hz).symm)

/-- `Λ` doubles the norm from `A₂(𝔻)` to `L²(𝔻*, ρ)` (from `d2_lambda_mass`). -/
theorem l29b_Lambda_L2 (φ : A2 unitDisc) :
    normL2 unitDiscExterior ⇑(Lambda (A2toAInf φ)) = 2 * (‖φ‖₊ : ℝ≥0∞) := by
  have hX : ∫⁻ z in unitDiscExterior, (‖Lambda (A2toAInf φ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) =
      4 * ∫⁻ w in unitDisc, (‖AInf.toFun (A2toAInf φ) w‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹ := by
    rw [← d2_lambda_mass]
    apply lintegral_congr_ae
    filter_upwards [Lambda_coe_ae (A2toAInf φ)] with z hz
    rw [hz]
  unfold normL2
  rw [hX, l29b_nnnorm_eq]
  unfold normA2
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [show (4 : ℝ≥0∞) = 2 ^ (2 : ℝ) by rw [ENNReal.rpow_two]; norm_num, ← ENNReal.rpow_mul]
  norm_num

/-- `Ω = f^μ(𝔻)` and `Ω* = 𝗀(𝔻*)` are open and disjoint. -/
theorem l29b_open_disjoint {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsOpen (fB μ '' unitDisc) ∧ IsOpen (gsans μ '' unitDiscExterior) ∧
      Disjoint (fB μ '' unitDisc) (gsans μ '' unitDiscExterior) := by
  have h := AppB.b8_welding_normalized_pair hμ
  rw [(Ch2.r22_fsans_gsans hμ).1] at h
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  exact ⟨(RMT.differentiableOn_invFunOn_of_injOn isOpen_ball h.1 h.2.1).1,
    (RMT.differentiableOn_invFunOn_of_injOn hEo h.2.2.2.2.1.1 h.2.2.2.2.1.2.1).1, h.2.2.2.2.2⟩

/-- The quasicircle `∂(f^μ(𝔻))` is null (from `r22_complement_null`). -/
theorem l29b_frontier_null {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    volume (frontier (fB μ '' unitDisc)) = 0 := by
  obtain ⟨hfo, hgo, hd⟩ := l29b_open_disjoint hμ
  have hnull := Ch2.r22_complement_null hμ
  rw [(Ch2.r22_fsans_gsans hμ).1] at hnull
  apply measure_mono_null _ hnull
  intro x hx
  rw [frontier, hfo.interior_eq] at hx
  rintro (h1 | h2)
  · exact hx.2 h1
  · exact Set.disjoint_left.mp (hd.closure_left hgo) hx.1 h2

/-- `AInf.toFun` is additive on differences. -/
theorem l29b_toFun_sub (a b : AInf unitDisc) : AInf.toFun (a - b) = AInf.toFun a - AInf.toFun b := by
  funext z
  by_cases hz : z ∈ unitDisc
  · simp [AInf.toFun, unweight, hz, sub_div]
  · simp [AInf.toFun, unweight, hz]

/-- `interior Ωᶜ ⊆ Ω* = 𝗀(𝔻*)`. -/
theorem l29b_interior_compl {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    interior ((fB μ '' unitDisc)ᶜ) ⊆ gsans μ '' unitDiscExterior := by
  intro u hu
  by_contra hug
  have huf : u ∉ fB μ '' unitDisc := interior_subset hu
  have hgs : gsans μ = gMu μ := (Ch2.r22_fsans_gsans hμ).2
  rw [hgs] at hug
  obtain ⟨z, hz1, hzu⟩ := Ch2.r22_complement_circle hμ (by
    rintro (h1 | h2)
    · exact huf h1
    · exact hug h2)
  -- `u` is a limit of points of `Ω`
  have hdisc : ∀ w ∈ unitDisc, wB μ (w : ExtPlane) = ((fB μ w : ℂ) : ExtPlane) := by
    intro w hw
    obtain ⟨⟨M, -, W, -, -, -, f, hf, -⟩, -⟩ := wB_spec hμ
    have h := hf w hw
    rw [show fB μ w = f w by unfold fB; rw [h, finPart_coe]]
    exact h
  have hcl : u ∈ closure (fB μ '' unitDisc) := by
    have ht : Tendsto (fun r : ℝ => ((r : ℂ) * z)) (𝓝[<] 1) (𝓝 z) := by
      have : Tendsto (fun r : ℝ => ((r : ℂ) * z)) (𝓝 1) (𝓝 ((1 : ℝ) * z)) :=
        ((Complex.continuous_ofReal.mul continuous_const).tendsto 1)
      simpa using this.mono_left nhdsWithin_le_nhds
    have hT : Tendsto (fun r : ℝ => wB μ (((r : ℂ) * z : ℂ) : ExtPlane)) (𝓝[<] 1) (𝓝 (wB μ (z : ExtPlane))) :=
      ((wB_continuous hμ).tendsto _).comp (OnePoint.continuous_coe.continuousAt.tendsto.comp ht)
    rw [hzu] at hT
    have hmem : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r → ((r : ℂ) * z) ∈ unitDisc := by
      filter_upwards [self_mem_nhdsWithin] with r hr hr0
      rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hz1,
        mul_one]
      exact hr
    have hpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r := by
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
      exact hr.1
    have hT' : Tendsto (fun r : ℝ => fB μ ((r : ℂ) * z)) (𝓝[<] 1) (𝓝 u) := by
      refine (OnePoint.isOpenEmbedding_coe.isEmbedding.tendsto_nhds_iff).mpr ?_
      refine hT.congr' ?_
      filter_upwards [hmem, hpos] with r hr hr0
      exact hdisc _ (hr hr0)
    apply mem_closure_of_tendsto hT'
    filter_upwards [hmem, hpos] with r hr hr0
    exact ⟨_, hr hr0, rfl⟩
  rw [interior_compl] at hu
  exact hu hcl

/-- The exterior hyperbolic density of `Ω* = 𝗀(𝔻*)` in the form of `r24_exterior_kernel_bound`. -/
theorem l29b_rhos_cov {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (h : ℂ → ℝ≥0∞) :
    ∫⁻ u in (fB μ '' unitDisc)ᶜ, h u * ENNReal.ofReal
        (rho (Function.invFunOn (gsans μ) unitDiscExterior u) *
          ‖deriv (Function.invFunOn (gsans μ) unitDiscExterior) u‖ ^ 2) =
      ∫⁻ u in unitDiscExterior, h (gsans μ u) * ENNReal.ofReal (rho u) := by
  obtain ⟨hfo, hgo, hd⟩ := l29b_open_disjoint hμ
  have hp := AppB.b8_welding_normalized_pair hμ
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hgd : DifferentiableOn ℂ (gsans μ) unitDiscExterior := hp.2.2.2.2.1.1
  have hgi : InjOn (gsans μ) unitDiscExterior := hp.2.2.2.2.1.2.1
  have hnull := Ch2.r22_complement_null hμ
  rw [(Ch2.r22_fsans_gsans hμ).1] at hnull
  have hset : ((fB μ '' unitDisc)ᶜ : Set ℂ) =ᵐ[volume] (gsans μ '' unitDiscExterior : Set ℂ) := by
    rw [ae_eq_set]
    constructor
    · apply measure_mono_null _ hnull
      intro x hx
      rintro (h1 | h2)
      · exact hx.1 h1
      · exact hx.2 h2
    · have : (gsans μ '' unitDiscExterior) \ (fB μ '' unitDisc)ᶜ = ∅ := by
        ext x
        simp only [Set.mem_sdiff, mem_compl_iff, not_not, mem_empty_iff_false, iff_false, not_and]
        intro hx hxf
        exact Set.disjoint_left.mp hd hxf hx
      rw [this, measure_empty]
  rw [setLIntegral_congr hset, d2_lintegral_image hEo hgd hgi]
  apply setLIntegral_congr_fun hEo.measurableSet
  intro z hz
  have hinv : Function.invFunOn (gsans μ) unitDiscExterior (gsans μ z) = z := hgi.leftInvOn_invFunOn hz
  have hInvD := (RMT.differentiableOn_invFunOn_of_injOn hEo hgd hgi).2
  have hGz : HasDerivAt (gsans μ) (deriv (gsans μ) z) z :=
    (hgd.differentiableAt (hEo.mem_nhds hz)).hasDerivAt
  have hIz : HasDerivAt (Function.invFunOn (gsans μ) unitDiscExterior)
      (deriv (Function.invFunOn (gsans μ) unitDiscExterior) (gsans μ z)) (gsans μ z) :=
    (hInvD.differentiableAt (hgo.mem_nhds ⟨z, hz, rfl⟩)).hasDerivAt
  have hcomp := hIz.comp z hGz
  have hid : HasDerivAt (Function.invFunOn (gsans μ) unitDiscExterior ∘ gsans μ) 1 z := by
    apply (hasDerivAt_id z).congr_of_eventuallyEq
    filter_upwards [hEo.mem_nhds hz] with w hw
    exact hgi.leftInvOn_invFunOn hw
  have h1 := hcomp.unique hid
  beta_reduce
  rw [hinv]
  have halg : ‖deriv (gsans μ) z‖ ^ 2 * (rho z *
      ‖deriv (Function.invFunOn (gsans μ) unitDiscExterior) (gsans μ z)‖ ^ 2) = rho z := by
    have : ‖deriv (Function.invFunOn (gsans μ) unitDiscExterior) (gsans μ z)‖ * ‖deriv (gsans μ) z‖ = 1 := by
      rw [← norm_mul, h1, norm_one]
    calc _ = rho z * (‖deriv (Function.invFunOn (gsans μ) unitDiscExterior) (gsans μ z)‖ *
          ‖deriv (gsans μ) z‖) ^ 2 := by ring
      _ = rho z := by rw [this]; ring
  have hρ : 0 ≤ rho z := by unfold rho; positivity
  rw [mul_left_comm, ← ENNReal.ofReal_mul (sq_nonneg _), halg]

/-! ### The plane transition `F = W_{ω*μ} ∘ W_μ⁻¹` -/

/-- Properties of the normalized plane solution `W_μ`. -/
theorem l29b_W {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ K, IsKQC (QCV.qcv_planeSolution μ) univ K ∧ QCV.qcv_planeSolution μ '' univ = univ ∧
      ∀ᵐ z, complexDilatation (QCV.qcv_planeSolution μ) z = extB μ z := by
  obtain ⟨hN, -, -, -⟩ := QCV.qcv_W_props (bc_norm_lt_one hμ)
  obtain ⟨⟨K, hK⟩, himg, -, -, hdil⟩ := hN
  exact ⟨K, hK, himg, hdil⟩

/-- The plane transition is a global q.c. homeomorphism. -/
theorem l29b_F_qc {μ ω : LinfStar} (hμ : μ ∈ LinfStarBall) (hω : ω ∈ LinfStarBall) :
    ∃ K, IsKQC (QCV.qcv_planeSolution (beltramiMul ω μ) ∘
        Function.invFunOn (QCV.qcv_planeSolution μ) univ) univ K ∧
      (QCV.qcv_planeSolution (beltramiMul ω μ) ∘ Function.invFunOn (QCV.qcv_planeSolution μ) univ) '' univ =
        univ := by
  obtain ⟨K0, hK0, himg0, -⟩ := l29b_W hμ
  obtain ⟨K1, hK1, himg1, -⟩ := l29b_W (bg_mul_mem_ball hμ hω)
  have hinv := thm7_2_inv hK0
  rw [himg0] at hinv
  refine ⟨K0 * K1, thm7_1_comp hinv hK1 (subset_univ _), ?_⟩
  have hinvimg : Function.invFunOn (QCV.qcv_planeSolution μ) univ '' univ = univ := by
    apply eq_univ_of_forall
    intro x
    refine ⟨QCV.qcv_planeSolution μ x, mem_univ _, ?_⟩
    exact hK0.2.2.1.2.1.leftInvOn_invFunOn (mem_univ x)
  rw [image_comp, hinvimg, himg1]

/-- Algebra of the group law: if `c = (a + b)/(1 + ā b)` then `(c - a)/(1 - ā c) = b`. -/
theorem l29b_alg {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ((a + b) / (1 + conj a * b) - a) / (1 - conj a * ((a + b) / (1 + conj a * b))) = b := by
  have hden : 1 + conj a * b ≠ 0 := by
    intro h
    have : ‖conj a * b‖ = 1 := by
      rw [show conj a * b = -1 by linear_combination h, norm_neg, norm_one]
    rw [norm_mul, Complex.norm_conj] at this
    nlinarith [norm_nonneg a, norm_nonneg b]
  have haa : conj a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 : (1 : ℂ) - conj a * a ≠ 0 := by
    rw [haa]
    intro h
    have : (‖a‖ ^ 2 : ℝ) = 1 := by exact_mod_cast (sub_eq_zero.mp h).symm
    nlinarith [norm_nonneg a]
  have hden' : 1 + b * conj a ≠ 0 := by rwa [mul_comm]
  have h1' : (1 : ℂ) - a * conj a ≠ 0 := by rwa [mul_comm]
  have e1 : (a + b) / (1 + conj a * b) - a = b * (1 - conj a * a) / (1 + conj a * b) := by
    field_simp; ring
  have e2 : 1 - conj a * ((a + b) / (1 + conj a * b)) = (1 - conj a * a) / (1 + conj a * b) := by
    field_simp; ring
  rw [e1, e2]
  field_simp

/-- The Beltrami coefficient of the plane transition: `|ν_F(W_μ z)| = |ω(w_μ z)|` on `𝔻*`, `0` on `𝔻`. -/
theorem l29b_F_dil {μ ω : LinfStar} (hμ : μ ∈ LinfStarBall) (hω : ω ∈ LinfStarBall) :
    (∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖complexDilatation (QCV.qcv_planeSolution (beltramiMul ω μ) ∘
        Function.invFunOn (QCV.qcv_planeSolution μ) univ) (QCV.qcv_planeSolution μ z)‖ = ‖ω (wA μ z)‖) ∧
      ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation (QCV.qcv_planeSolution (beltramiMul ω μ) ∘
        Function.invFunOn (QCV.qcv_planeSolution μ) univ) (QCV.qcv_planeSolution μ z) = 0 := by
  have hωμ := bg_mul_mem_ball hμ hω
  obtain ⟨K0, hK0, -, hd0⟩ := l29b_W hμ
  obtain ⟨K1, hK1, -, hd1⟩ := l29b_W hωμ
  have hA := ahQ_comp_inv_dilatation hK1 hK0
  rw [Measure.restrict_univ] at hA
  have hJ := thm9_6_cor2_jacobian_pos hK0
  rw [Measure.restrict_univ] at hJ
  have hdz : ∀ᵐ z, dz (QCV.qcv_planeSolution μ) z ≠ 0 := by
    filter_upwards [hJ] with z hz h0
    unfold jacobian at hz
    rw [h0, norm_zero] at hz
    nlinarith [norm_nonneg (dzbar (QCV.qcv_planeSolution μ) z)]
  have hτ : ∀ᵐ z, ‖dz (QCV.qcv_planeSolution μ) z / conj (dz (QCV.qcv_planeSolution μ) z)‖ = 1 := by
    filter_upwards [hdz] with z hz
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hz)]
  constructor
  · have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
    filter_upwards [ae_restrict_of_ae hA, ae_restrict_of_ae hd0, ae_restrict_of_ae hd1, ae_restrict_of_ae hτ,
      bg_mul_ae hμ hω, bc_comp_dilatation_ae hω hμ, ae_restrict_of_ae (bc_wA_ae hμ),
      LinfStar_ae_norm_le μ, bc_pullback_ae hμ (LinfStar_ae_norm_le ω), ae_restrict_mem hEm]
      with z hAz h0z h1z hτz hgz hcz hwz hμz hωz hzE
    obtain ⟨-, hdzw, -, -⟩ := hwz
    rw [hAz, h0z, h1z]
    simp only [extB, indicator_of_mem hzE]
    rw [hgz, hcz]
    have hτw : ‖conj (dz (wA μ) z) / dz (wA μ) z‖ = 1 := by
      rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hdzw)]
    have ha : ‖μ z‖ < 1 := hμz.trans_lt (bc_norm_lt_one hμ)
    have hb : ‖ω (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)‖ < 1 := by
      rw [norm_mul, hτw, mul_one]; exact hωz.trans_lt (bc_norm_lt_one hω)
    have e : (μ z + ω (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) /
        (1 + conj (μ z) * ω (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) =
        (μ z + ω (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) /
        (1 + conj (μ z) * (ω (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))) := by ring
    rw [e, l29b_alg ha hb, norm_mul, norm_mul, hτw, hτz, mul_one, mul_one]
  · filter_upwards [ae_restrict_of_ae hA, ae_restrict_of_ae hd0, ae_restrict_of_ae hd1,
      ae_restrict_mem (isOpen_ball.measurableSet : MeasurableSet unitDisc)] with z hAz h0z h1z hzD
    have hzE : z ∉ unitDiscExterior := by
      intro h
      have h1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hzD
      have h2 : 1 < ‖z‖ := h
      linarith
    rw [hAz, h0z, h1z]
    simp [extB, indicator_of_notMem hzE]

/-! ### Möbius transport of the kernel `|u - y|⁻⁴` -/

/-- Möbius distortion of the kernel: `|N u - N y|⁻⁴ |N'(u)|² |N'(y)|² = |u - y|⁻⁴`. -/
theorem l29b_mob_kernel {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) {u y : ℂ} (hu : c * u + d ≠ 0)
    (hy : c * y + d ≠ 0) :
    ‖(a * u + b) / (c * u + d) - (a * y + b) / (c * y + d)‖ ^ 4 =
      ‖u - y‖ ^ 4 * (‖a * d - b * c‖ / (‖c * u + d‖ * ‖c * y + d‖)) ^ 4 := by
  have e : (a * u + b) / (c * u + d) - (a * y + b) / (c * y + d) =
      (u - y) * ((a * d - b * c) / ((c * u + d) * (c * y + d))) := by
    rw [div_sub_div _ _ hu hy]
    ring
  rw [e, norm_mul, mul_pow, norm_div, norm_mul]

/-- The derivative of a Möbius map. -/
theorem l29b_mob_deriv {a b c d : ℂ} {y : ℂ} (hy : c * y + d ≠ 0) :
    HasDerivAt (fun w => (a * w + b) / (c * w + d)) ((a * d - b * c) / (c * y + d) ^ 2) y := by
  have h1 : HasDerivAt (fun w => a * w + b) a y := by
    simpa using ((hasDerivAt_id y).const_mul a).add_const b
  have h2 : HasDerivAt (fun w => c * w + d) c y := by
    simpa using ((hasDerivAt_id y).const_mul c).add_const d
  convert h1.div h2 hy using 1
  field_simp
  ring

/-- Kernel finiteness off the closure: for `u` in the interior of `(W_μ 𝔻)ᶜ`, `∫_{W_μ 𝔻} |u - y|⁻⁴ < ∞`. -/
theorem l29b_kernel_finite {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ℂ}
    (hu : u ∈ interior ((QCV.qcv_planeSolution μ '' unitDisc)ᶜ)) :
    ∫⁻ y in QCV.qcv_planeSolution μ '' unitDisc, ENNReal.ofReal (1 / ‖u - y‖ ^ 4) ≠ ⊤ := by
  obtain ⟨K, hK, -, -⟩ := l29b_W hμ
  have hcont : Continuous (QCV.qcv_planeSolution μ) := continuousOn_univ.mp hK.2.2.1.1
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hu)
  have hbd : ∀ y ∈ QCV.qcv_planeSolution μ '' unitDisc, ENNReal.ofReal (1 / ‖u - y‖ ^ 4) ≤
      ENNReal.ofReal (1 / r ^ 4) := by
    intro y hy
    apply ENNReal.ofReal_le_ofReal
    have hyr : r ≤ ‖u - y‖ := by
      by_contra h
      push_neg at h
      exact hball (by rw [mem_ball, dist_eq_norm]; simpa only [norm_sub_rev] using h) hy
    gcongr
  have hfin : volume (QCV.qcv_planeSolution μ '' unitDisc) < ⊤ := by
    have hc : IsCompact (QCV.qcv_planeSolution μ '' closedBall (0 : ℂ) 1) :=
      (isCompact_closedBall 0 1).image hcont
    exact lt_of_le_of_lt (measure_mono (image_mono ball_subset_closedBall)) hc.measure_lt_top
  have hO : IsOpen (QCV.qcv_planeSolution μ '' unitDisc) := QCV.qcv_planeDisk_isOpen hμ
  apply ne_of_lt
  calc ∫⁻ y in QCV.qcv_planeSolution μ '' unitDisc, ENNReal.ofReal (1 / ‖u - y‖ ^ 4)
      ≤ ∫⁻ y in QCV.qcv_planeSolution μ '' unitDisc, ENNReal.ofReal (1 / r ^ 4) :=
        setLIntegral_mono' hO.measurableSet hbd
    _ = ENNReal.ofReal (1 / r ^ 4) * volume (QCV.qcv_planeSolution μ '' unitDisc) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem l29b_mob_kernel_weight {a b c d u y : ℂ} (hdet : a * d - b * c ≠ 0)
    (hu : c * u + d ≠ 0) (hy : c * y + d ≠ 0) :
    ‖(a * d - b * c) / (c * u + d) ^ 2‖ ^ 2 *
      ‖(a * d - b * c) / (c * y + d) ^ 2‖ ^ 2 *
        (1 / ‖(a * u + b) / (c * u + d) - (a * y + b) / (c * y + d)‖ ^ 4) =
      1 / ‖u - y‖ ^ 4 := by
  by_cases huy : u = y
  · subst y; simp
  rw [l29b_mob_kernel hdet hu hy]
  simp only [norm_div, norm_pow]
  field_simp [norm_ne_zero_iff.mpr hdet, norm_ne_zero_iff.mpr hu,
    norm_ne_zero_iff.mpr hy, norm_ne_zero_iff.mpr (sub_ne_zero.mpr huy)] <;> ring

theorem l29b_mob_kernel_weight_en {a b c d u y : ℂ} (hdet : a * d - b * c ≠ 0)
    (hu : c * u + d ≠ 0) (hy : c * y + d ≠ 0) :
    ENNReal.ofReal (‖(a * d - b * c) / (c * u + d) ^ 2‖ ^ 2) *
      ENNReal.ofReal (‖(a * d - b * c) / (c * y + d) ^ 2‖ ^ 2) *
        ENNReal.ofReal (1 / ‖(a * u + b) / (c * u + d) - (a * y + b) / (c * y + d)‖ ^ 4) =
      ENNReal.ofReal (1 / ‖u - y‖ ^ 4) := by
  rw [← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)), l29b_mob_kernel_weight hdet hu hy]

/-- Exact transport of the positive kernel from the plane disk to the normalized disk. -/
theorem l29b_kernel_mob_cov {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {a b c d : ℂ}
    (hdet : a * d - b * c ≠ 0)
    (hf : ∀ ζ ∈ unitDisc, c * QCV.qcv_planeSolution μ ζ + d ≠ 0 ∧
      fsans μ ζ = (a * QCV.qcv_planeSolution μ ζ + b) / (c * QCV.qcv_planeSolution μ ζ + d))
    {u : ℂ} (hu : c * u + d ≠ 0) :
    ENNReal.ofReal (‖(a * d - b * c) / (c * u + d) ^ 2‖ ^ 2) *
      (∫⁻ y in fsans μ '' unitDisc,
        ENNReal.ofReal (1 / ‖(a * u + b) / (c * u + d) - y‖ ^ 4)) =
      ∫⁻ y in QCV.qcv_planeSolution μ '' unitDisc, ENNReal.ofReal (1 / ‖u - y‖ ^ 4) := by
  rw [r24_conformal_lintegral (U := unitDisc) isOpen_ball (S2C.s2c_conf_f hμ).1 (S2C.s2c_conf_f hμ).2.1,
    r24_conformal_lintegral (U := unitDisc) isOpen_ball (QCV.qcv_planeSolution_conformal hμ).1
      (QCV.qcv_planeSolution_conformal hμ).2.1,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_ball
  intro y hy
  dsimp only
  rw [(hf y hy).2, S2C.s2c_deriv_mobius hμ hf hy, norm_mul, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _)]
  calc _ = ENNReal.ofReal (‖deriv (QCV.qcv_planeSolution μ) y‖ ^ 2) *
      (ENNReal.ofReal (‖(a * d - b * c) / (c * u + d) ^ 2‖ ^ 2) *
        ENNReal.ofReal (‖(a * d - b * c) / (c * QCV.qcv_planeSolution μ y + d) ^ 2‖ ^ 2) *
          ENNReal.ofReal (1 / ‖(a * u + b) / (c * u + d) -
            (a * QCV.qcv_planeSolution μ y + b) / (c * QCV.qcv_planeSolution μ y + d)‖ ^ 4)) := by ring
    _ = _ := by rw [l29b_mob_kernel_weight_en hdet hu (hf y hy).1]

theorem l29b_g_kernel_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {x : ℂ} (hx : x ∈ unitDiscExterior) :
    ENNReal.ofReal (‖deriv (gsans μ) x‖ ^ 2) *
      (∫⁻ y in fsans μ '' unitDisc, ENNReal.ofReal (1 / ‖gsans μ x - y‖ ^ 4)) ≤
      ENNReal.ofReal (4 * π * rho x) := by
  have h := r24_exterior_kernel_bound hμ (mem_image_of_mem (gsans μ) hx)
  have hi : (∫⁻ y in fsans μ '' unitDisc, ENNReal.ofReal (1 / ‖gsans μ x - y‖ ^ 4)) ≤
      ∫⁻ y in fsans μ '' unitDisc, (‖gsans μ x - y‖₊ : ℝ≥0∞)⁻¹ ^ 4 := by
    apply lintegral_mono
    intro y
    dsimp only
    by_cases hy : gsans μ x - y = 0
    · simp [hy]
    · rw [one_div, ← inv_pow, ENNReal.ofReal_pow (inv_nonneg.mpr (norm_nonneg _)),
        ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr hy), ofReal_norm, enorm_eq_nnnorm]
  have hg := S2C.s2c_conf_g hμ
  have hInv := hg.2.1.leftInvOn_invFunOn hx
  have hprod := t1_deriv_invFunOn_mul bc_hEo hg hx
  have hn : ‖deriv (Function.invFunOn (gsans μ) unitDiscExterior) (gsans μ x)‖ * ‖deriv (gsans μ) x‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  have halg : ‖deriv (gsans μ) x‖ ^ 2 *
      (4 * π * (rho x * ‖deriv (Function.invFunOn (gsans μ) unitDiscExterior) (gsans μ x)‖ ^ 2)) =
      4 * π * rho x := by
    calc _ = (4 * π * rho x) *
        (‖deriv (Function.invFunOn (gsans μ) unitDiscExterior) (gsans μ x)‖ * ‖deriv (gsans μ) x‖) ^ 2 := by ring
      _ = _ := by rw [hn]; ring
  have hh := mul_le_mul' (le_refl (ENNReal.ofReal (‖deriv (gsans μ) x‖ ^ 2))) (hi.trans h)
  simpa only [hInv, ← ENNReal.ofReal_mul (sq_nonneg _), halg] using hh

/-! ### The actual plane domains and transition coefficient -/

theorem l29b_plane_domains {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsOpen (QCV.qcv_planeSolution μ '' unitDisc) ∧
    IsOpen (QCV.qcv_planeSolution μ '' unitDiscExterior) ∧
    Disjoint (QCV.qcv_planeSolution μ '' unitDisc) (QCV.qcv_planeSolution μ '' unitDiscExterior) ∧
    volume ((QCV.qcv_planeSolution μ '' unitDisc) ∪
      (QCV.qcv_planeSolution μ '' unitDiscExterior))ᶜ = 0 := by
  obtain ⟨K, hK, himg, -⟩ := l29b_W hμ
  have hi := (QCV.qcv_planeSolution_bijective hμ).1
  have hEo := isOpen_image_of_isKQC (nx_isKQC_restrict hK bc_hEo (subset_univ _))
  have hd : Disjoint (QCV.qcv_planeSolution μ '' unitDisc)
      (QCV.qcv_planeSolution μ '' unitDiscExterior) := by
    apply Set.disjoint_left.mpr
    rintro u ⟨x, hx, hxu⟩ ⟨y, hy, hyu⟩
    have hxy := hi (hxu.trans hyu.symm)
    subst y
    have h1 := mem_ball_zero_iff.mp hx
    exact (not_lt_of_gt (show 1 < ‖x‖ from hy)) h1
  refine ⟨QCV.qcv_planeDisk_isOpen hμ, hEo, hd, ?_⟩
  apply measure_mono_null _ (thm9_6_cor1_null hK (subset_univ (sphere (0 : ℂ) 1))
    (Measure.addHaar_sphere volume (0 : ℂ) 1))
  intro u hu
  obtain ⟨x, rfl⟩ := (QCV.qcv_planeSolution_bijective hμ).2 u
  have hnD : ¬ ‖x‖ < 1 := fun h => hu (Or.inl ⟨x, mem_ball_zero_iff.mpr h, rfl⟩)
  have hnE : ¬ 1 < ‖x‖ := fun h => hu (Or.inr ⟨x, h, rfl⟩)
  exact ⟨x, by simp [mem_sphere, dist_zero_right, le_antisymm (le_of_not_gt hnE) (le_of_not_gt hnD)], rfl⟩

theorem l29b_plane_frontier_null {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    volume (frontier (QCV.qcv_planeSolution μ '' unitDisc)) = 0 := by
  obtain ⟨hDo, hEo, hd, hn⟩ := l29b_plane_domains hμ
  apply measure_mono_null _ hn
  intro u hu
  rw [frontier, hDo.interior_eq] at hu
  rintro (hD | hE)
  · exact hu.2 hD
  · exact Set.disjoint_left.mp (hd.closure_left hEo) hu.1 hE

theorem l29b_plane_compl_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ((QCV.qcv_planeSolution μ '' unitDisc)ᶜ : Set ℂ) =ᵐ[volume]
      (QCV.qcv_planeSolution μ '' unitDiscExterior : Set ℂ) := by
  obtain ⟨-, -, hd, hn⟩ := l29b_plane_domains hμ
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null _ hn
    intro u hu
    exact fun h => h.elim hu.1 hu.2
  · have he : (QCV.qcv_planeSolution μ '' unitDiscExterior) \
        (QCV.qcv_planeSolution μ '' unitDisc)ᶜ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact Set.disjoint_left.mp hd (not_not.mp hu.2) hu.1
    rw [he, measure_empty]

theorem l29b_F_bound {μ ω : LinfStar} (hμ : μ ∈ LinfStarBall) (hω : ω ∈ LinfStarBall) :
    ∀ᵐ u : ℂ, ‖complexDilatation (QCV.qcv_planeSolution (beltramiMul ω μ) ∘
      Function.invFunOn (QCV.qcv_planeSolution μ) univ) u‖ ≤ ‖ω‖ := by
  let F := QCV.qcv_planeSolution (beltramiMul ω μ) ∘ Function.invFunOn (QCV.qcv_planeSolution μ) univ
  obtain ⟨K, hK, himg, -⟩ := l29b_W hμ
  obtain ⟨hE, hD⟩ := l29b_F_dil hμ hω
  have hE' := (ae_restrict_iff' bc_hEo.measurableSet).mp hE
  have hD' := (ae_restrict_iff' measurableSet_ball).mp hD
  have hω' := (ae_restrict_iff' bc_hEo.measurableSet).mp (bc_pullback_ae hμ (LinfStar_ae_norm_le ω))
  have hcircle := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0 : ℂ) 1)
  have hpre : ∀ᵐ z : ℂ, ‖complexDilatation F (QCV.qcv_planeSolution μ z)‖ ≤ ‖ω‖ := by
    filter_upwards [hE', hD', hω', hcircle] with z hzE hzD hzω hzS
    by_cases hz : ‖z‖ < 1
    · rw [hzD (mem_ball_zero_iff.mpr hz), norm_zero]
      exact norm_nonneg _
    · have hne : ‖z‖ ≠ 1 := by simpa [mem_sphere, dist_zero_right] using hzS
      have he : z ∈ unitDiscExterior := lt_of_le_of_ne (le_of_not_gt hz) hne.symm
      rw [hzE he]
      exact hzω he
  filter_upwards [(ahT_qmp_inv ⟨K, hK⟩ himg).ae hpre] with u hu
  have hi : QCV.qcv_planeSolution μ (Function.invFunOn (QCV.qcv_planeSolution μ) univ u) = u :=
    Function.invFunOn_eq (by change u ∈ QCV.qcv_planeSolution μ '' univ; rw [himg]; exact mem_univ _)
  simpa only [hi] using hu

theorem l29b_qc_equation {F : ℂ → ℂ} {K : ℝ} (hF : IsKQC F univ K) :
    ∀ᵐ u : ℂ, dzbar F u = complexDilatation F u * dz F u := by
  have hJ := thm9_6_cor2_jacobian_pos hF
  rw [Measure.restrict_univ] at hJ
  filter_upwards [hJ] with u hu
  have hn : dz F u ≠ 0 := by
    intro hn
    unfold jacobian at hu
    rw [hn, norm_zero] at hu
    nlinarith [sq_nonneg ‖dzbar F u‖]
  simp only [complexDilatation, div_mul_cancel₀ _ hn]

theorem l29b_plane_schwarzian {μ ω : LinfStar} (hμ : μ ∈ LinfStarBall) (hω : ω ∈ LinfStarBall) :
    let F := QCV.qcv_planeSolution (beltramiMul ω μ) ∘ Function.invFunOn (QCV.qcv_planeSolution μ) univ
    DifferentiableOn ℂ F (QCV.qcv_planeSolution μ '' unitDisc) ∧
    ∀ z ∈ unitDisc, schwarzianHol (F ∘ QCV.qcv_planeSolution μ) z - schwarzianHol (QCV.qcv_planeSolution μ) z =
      AInf.toFun (bersPhi (beltramiMul ω μ) - bersPhi μ) z := by
  intro F
  have hωμ := bg_mul_mem_ball hμ hω
  have he : Function.invFunOn (QCV.qcv_planeSolution μ) univ = Function.invFun (QCV.qcv_planeSolution μ) := by
    funext u
    obtain ⟨z, rfl⟩ := (QCV.qcv_planeSolution_bijective hμ).2 u
    rw [(QCV.qcv_planeSolution_bijective hμ).1.injOn.leftInvOn_invFunOn (mem_univ z),
      Function.leftInverse_invFun (QCV.qcv_planeSolution_bijective hμ).1]
  have hcomp : F ∘ QCV.qcv_planeSolution μ = QCV.qcv_planeSolution (beltramiMul ω μ) := by
    dsimp [F]
    rw [he]
    exact QCV.qcv_planeTransition_comp hμ _
  constructor
  · change DifferentiableOn ℂ (QCV.qcv_planeSolution (beltramiMul ω μ) ∘ _)
      (QCV.qcv_planeSolution μ '' unitDisc)
    rw [he]
    exact (QCV.qcv_planeTransition_conformal hμ hωμ).1
  · intro z hz
    rw [hcomp, l29b_toFun_sub, Pi.sub_apply, (bersPhi_spec hωμ).1 z hz,
      (bersPhi_spec hμ).1 z hz, QCV.qcv_schwarzian_fB_eq hωμ hz, QCV.qcv_schwarzian_fB_eq hμ hz]
    rfl

theorem l29b_jac_hol_comp {f g : ℂ → ℂ} {x : ℂ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℂ g (f x)) :
    jacobian (fun y => g (f y)) x = ‖deriv g (f x)‖ ^ 2 * jacobian f x := by
  obtain ⟨hd, hb⟩ := eq6_5 hf hg
  change jacobian (g ∘ f) x = _
  unfold jacobian
  rw [hd, hb, norm_mul, norm_mul]
  ring

/-- Kernel covariance with the true plane Jacobian; normalized poles are removed only a.e. -/
theorem l29b_plane_kernel_bound_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ x ∂(volume.restrict unitDiscExterior),
      ENNReal.ofReal (jacobian (QCV.qcv_planeSolution μ) x) *
        (∫⁻ y in QCV.qcv_planeSolution μ '' unitDisc,
          ENNReal.ofReal (1 / ‖QCV.qcv_planeSolution μ x - y‖ ^ 4)) ≤
        ENNReal.ofReal (4 * π) *
          (ENNReal.ofReal (jacobian (wA μ) x) * ENNReal.ofReal (rho (wA μ x))) := by
  obtain ⟨a, b, c, d, hdet, hf, hg⟩ := S2C.s2c_mobius hμ
  obtain ⟨K, hK, -, -⟩ := l29b_W hμ
  have hdiff := thm9_3_differentiable_ae hK
  rw [Measure.restrict_univ] at hdiff
  have hpole : ∀ᵐ x : ℂ, wAS μ (x : ExtPlane) ≠ extInf :=
    measure_eq_zero_iff_ae_notMem.mp ((S2C.s2c_pole_subsingleton μ).measure_zero volume)
  filter_upwards [ae_restrict_of_ae hdiff, ae_restrict_of_ae hpole,
    ae_restrict_of_ae (bc_wA_ae hμ),
    bc_pullback_ae hμ (ae_restrict_mem bc_hEo.measurableSet), ae_restrict_mem bc_hEo.measurableSet]
    with x hWx hpx hAx hxA hx
  obtain ⟨hdenx, hMx⟩ := hg x hx hpx
  let M : ℂ → ℂ := fun u => (a * u + b) / (c * u + d)
  have hM := l29b_mob_deriv hdenx (a := a) (b := b)
  have hgd := (S2C.s2c_conf_g hμ).1.differentiableAt (bc_hEo.mem_nhds hxA)
  have hZ : (fun y => gsans μ (wA μ y)) =ᶠ[𝓝 x] fun y => M (QCV.qcv_planeSolution μ y) := by
    filter_upwards [bc_hEo.mem_nhds hx, (S2C.s2c_pole_open μ).mem_nhds hpx] with y hy hpy
    exact (hg y hy hpy).2
  have hJ : jacobian (fun y => gsans μ (wA μ y)) x =
      jacobian (fun y => M (QCV.qcv_planeSolution μ y)) x := by
    simp only [jacobian, dz, dzbar, hZ.fderiv_eq (𝕜 := ℝ)]
  rw [l29b_jac_hol_comp hAx.1 hgd, l29b_jac_hol_comp hWx hM.differentiableAt, hM.deriv] at hJ
  have hJE := congrArg ENNReal.ofReal hJ
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _)] at hJE
  have hc := l29b_kernel_mob_cov hμ hdet hf hdenx
  rw [← hMx] at hc
  calc _ = ENNReal.ofReal (jacobian (QCV.qcv_planeSolution μ) x) *
        (ENNReal.ofReal (‖(a * d - b * c) / (c * QCV.qcv_planeSolution μ x + d) ^ 2‖ ^ 2) *
          ∫⁻ y in fsans μ '' unitDisc, ENNReal.ofReal (1 / ‖gsans μ (wA μ x) - y‖ ^ 4)) := by rw [hc]
    _ = ENNReal.ofReal (jacobian (wA μ) x) *
        (ENNReal.ofReal (‖deriv (gsans μ) (wA μ x)‖ ^ 2) *
          ∫⁻ y in fsans μ '' unitDisc, ENNReal.ofReal (1 / ‖gsans μ (wA μ x) - y‖ ^ 4)) := by
          rw [← mul_assoc, mul_comm (ENNReal.ofReal (jacobian (QCV.qcv_planeSolution μ) x)), ← hJE]
          ring
    _ ≤ ENNReal.ofReal (jacobian (wA μ) x) * ENNReal.ofReal (4 * π * rho (wA μ x)) :=
      mul_le_mul' le_rfl (l29b_g_kernel_bound hμ hxA)
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * π)]; ring

theorem l29b_wA_lintegral {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (G : ℂ → ℝ≥0∞) :
    (∫⁻ x in unitDiscExterior, ENNReal.ofReal (jacobian (wA μ) x) * G (wA μ x)) =
      ∫⁻ x in unitDiscExterior, G x := by
  obtain ⟨U, K, hUo, hUE, hfin, hK, hmaps⟩ := bc_wA_kqc hμ
  have hi := bc_wA_image_compl_finite hμ hfin.finite
  rw [← setLIntegral_congr (S2C.s2c_ae_eq_ext hUE hfin.finite),
    ← QCV.qcv_lintegral_image_eq hK G, setLIntegral_congr (S2C.s2c_ae_eq_ext hmaps hi)]

/-- True plane-coordinate kernel energy bound for the transition dilatation. -/
theorem l29b_plane_energy {μ ω : LinfStar} (hμ : μ ∈ LinfStarBall) (hω : ω ∈ LinfStarBall) :
    let ν := complexDilatation (QCV.qcv_planeSolution (beltramiMul ω μ) ∘
      Function.invFunOn (QCV.qcv_planeSolution μ) univ)
    (∫⁻ u in (QCV.qcv_planeSolution μ '' unitDisc)ᶜ, (‖ν u‖₊ : ℝ≥0∞) ^ 2 *
      (∫⁻ y in QCV.qcv_planeSolution μ '' unitDisc, ENNReal.ofReal (1 / ‖u - y‖ ^ 4))) ≤
      ENNReal.ofReal (4 * π) * ∫⁻ x in unitDiscExterior, (‖ω x‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho x) := by
  intro ν
  obtain ⟨K, hK, -, -⟩ := l29b_W hμ
  rw [setLIntegral_congr (l29b_plane_compl_ae hμ),
    QCV.qcv_lintegral_image_eq (nx_isKQC_restrict hK bc_hEo (subset_univ _))]
  have hbound : (∫⁻ x in unitDiscExterior,
      ENNReal.ofReal (jacobian (QCV.qcv_planeSolution μ) x) *
        ((‖ν (QCV.qcv_planeSolution μ x)‖₊ : ℝ≥0∞) ^ 2 *
          ∫⁻ y in QCV.qcv_planeSolution μ '' unitDisc, ENNReal.ofReal (1 / ‖QCV.qcv_planeSolution μ x - y‖ ^ 4))) ≤
      ∫⁻ x in unitDiscExterior, ENNReal.ofReal (4 * π) *
        (ENNReal.ofReal (jacobian (wA μ) x) * ((‖ω (wA μ x)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho (wA μ x)))) := by
    apply lintegral_mono_ae
    filter_upwards [l29b_plane_kernel_bound_ae hμ, (l29b_F_dil hμ hω).1] with x hx hνx
    have he : ‖ν (QCV.qcv_planeSolution μ x)‖₊ = ‖ω (wA μ x)‖₊ := NNReal.eq hνx
    rw [he, mul_left_comm]
    have hh := mul_le_mul' (le_refl ((‖ω (wA μ x)‖₊ : ℝ≥0∞) ^ 2)) hx
    convert hh using 1 <;> ring
  refine hbound.trans_eq ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact congrArg (ENNReal.ofReal (4 * π) * ·)
    (l29b_wA_lintegral hμ (fun x => (‖ω x‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho x)))

/-- `𝒪(𝔻*)₁ ⊆ L∞(𝔻*)₁`. -/
theorem l29b_groupO_ball {μ : LinfStar} (hμ : μ ∈ groupO) : μ ∈ LinfStarBall :=
  hμ LinfStarBall subset_rfl
    (fun ν _ hν => mem_ball_zero_iff.mpr (hν.trans delta0_bounds.2))
    (fun a ha b hb => bg_mul_mem_ball hb ha) (fun a ha => bc_beltramiInv_mem_ball ha)

/-- Assembly: the frozen statement of `l29r_restricted`. -/
theorem l29b_l29r {μ : LinfStar} (hμ : μ ∈ groupO) {k : ℝ} (hk : k < 2) :
    ∃ C > 0, ∀ φ : A2 unitDisc, ‖A2toAInf φ‖ ≤ k →
      normA2 unitDisc (AInf.toFun (bersPhi (beltramiMul (Lambda (A2toAInf φ)) μ) - bersPhi μ)) ≤
        ENNReal.ofReal C * (‖φ‖₊ : ℝ≥0∞) := by
  have hμb := l29b_groupO_ball hμ
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
  obtain ⟨K, hF, hFs⟩ := l29b_F_qc hμb hωb
  obtain ⟨hFΩ, hS⟩ := l29b_plane_schwarzian hμb hωb
  have hfd := QCV.qcv_planeSolution_conformal hμb
  have hI : ∀ u ∈ interior ((W '' unitDisc)ᶜ),
      ∫⁻ y in W '' unitDisc, ENNReal.ofReal (1 / ‖u - y‖ ^ 4) ≤
        ENNReal.ofReal (1 * ρs u) := by
    intro u hu
    simpa only [one_mul] using (ENNReal.ofReal_toReal (l29b_kernel_finite hμb hu)).ge
  have hcui := CUI.cui_disc_bound hk'0 hk'1 (by norm_num : (0 : ℝ) ≤ 1)
    hfd.1 hfd.2.1 hF hFs hFΩ (l29b_qc_equation hF)
    ((l29b_F_bound hμb hωb).mono fun u hu => hu.trans hωn)
    (l29b_plane_frontier_null hμb) ρs hI
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
      (l29b_plane_energy hμb hωb)
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

end TakhtajanTeo

