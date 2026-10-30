import TakhtajanTeo.Ch2.S1_BP16Completed
import TakhtajanTeo.Ch1.Cor32Completed
import TakhtajanTeo.Ch1.FiberCircleOrientation
import TakhtajanTeo.Ch1.HilbertChosenReflection
import TakhtajanTeo.Ch1.S2Core
import TakhtajanTeo.Ch1.ComponentRelativeCoefficient
import TakhtajanTeo.Ch1.ComponentTC

/-!
# Corollary 1.8: `T₀(1) ⊆ S`

One direction of Gardiner–Sullivan, through Theorem 1.6. For `p = [μ] ∈ T₀(1)`:
- `β(p) ∈ A₂(𝔻)` (`ctd_componentT_spec_one_subset` at `[0]`), so `(1-|z|²)² 𝒮(f^μ) → 0` (`c18_A2_decay`).
- (ii) ⇒ (i) of Theorem 1.6 (`thm_1_6`) for `f^μ` (a quasidisc, `hc6_welding_quasidisc`) gives an extension `F̃`
  with `μ_F̃ → 0`. With the welding map `G` (`G ∘ w_μ = f^μ` on `𝔻̄`), `Ψ = G⁻¹ ∘ F̃` extends `h = w_μ|S¹` outside
  `S¹` with `μ_Ψ → 0` (`c18_outer`).
- The reflection plus removability of `S¹` (`s13x_removable`) gives a two-sided extension (`c18_two_sided`).
- The splitting `Φ = H ∘ W` on `S¹` (`c18_split`) has `W` a plane `K`-q.c. map with `K → 1` and `H` conformal near
  `W(S¹)`.
- Symmetric triples on `S¹` lie on circles about the middle point, so `thm15_4_circle_distortion` bounds the
  `W`-ratio by `λ(K) → 1` (`c18_ratio_W`, `c18_lambdaInv_near_one`).
- The `H`-ratio tends to `1` (`c18_ratio_H`).
- Chords to arcs (`c18_symmetric_of_chord`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-- `λ(K) → 1` as `K → 1⁺`. -/
theorem c18_lambdaInv_near_one {η : ℝ} (hη : 0 < η) :
    ∃ K > 1, ∀ K' : ℝ, 1 ≤ K' → K' ≤ K → lambdaInv K' ≤ 1 + η := by
  obtain ⟨hmono, -, -⟩ := quadLambda_strictMono
  have h1 : (1 : ℝ) ∈ Ioi (0 : ℝ) := by norm_num
  have h2 : (1 + η) ∈ Ioi (0 : ℝ) := by show (0 : ℝ) < 1 + η; linarith
  refine ⟨quadLambda (1 + η), ?_, fun K' hK' hKK => ?_⟩
  · calc (1 : ℝ) = quadLambda 1 := b4_quadLambda_one.symm
      _ < quadLambda (1 + η) := hmono h1 h2 (by linarith)
  · obtain ⟨hpos, hq⟩ := td_quadLambda_lambdaInv (show 0 < K' by linarith)
    exact (hmono.le_iff_le hpos h2).mp (by rw [hq]; exact hKK)

/-- Elements of `A₂(𝔻)` vanish at the boundary in the weighted sup sense: `(1 - |z|²)² φ(z) → 0`. -/
theorem c18_A2_decay {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDisc) :
    Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * φ z) (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  obtain ⟨hφd, hφ2⟩ := hφ
  have hfin : ∫⁻ z in unitDisc, (‖φ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ ≠ ⊤ :=
    ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp hφ2).ne
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmass⟩ := exists_pos_setLIntegral_lt_of_measure_lt hfin
    (show ENNReal.ofReal (π * ε ^ 2 / 2048) ≠ 0 by positivity)
  have hvolcont : Continuous (fun t : ℝ => ENNReal.ofReal (π * (|t - 1| / 2) ^ 2)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have hvolsmall : ∀ᶠ t : ℝ in 𝓝 1, ENNReal.ofReal (π * (|t - 1| / 2) ^ 2) < δ := by
    have h := (hvolcont.tendsto 1).eventually
      (gt_mem_nhds (show ENNReal.ofReal (π * (|(1 : ℝ) - 1| / 2) ^ 2) < δ by simpa using hδ))
    simpa using h
  have hn : Tendsto (fun z : ℂ => ‖z‖) (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝[<] 1) := tendsto_comap
  filter_upwards [hn.eventually (hvolsmall.filter_mono nhdsWithin_le_nhds), hn.eventually self_mem_nhdsWithin]
    with z hzvol hz1
  have hz1' : ‖z‖ < 1 := hz1
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (1 - ‖z‖) / 2 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; linarith
  have hrabs : |‖z‖ - 1| / 2 = r := by rw [hrdef, abs_of_neg (by linarith)]; ring
  rw [hrabs] at hzvol
  have hclosed : closedBall z r ⊆ unitDisc := by
    intro w hw
    have hd : ‖w - z‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hw
    have := norm_le_norm_add_norm_sub' w z
    show w ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]
    linarith
  have hsub : ball z r ⊆ unitDisc := ball_subset_closedBall.trans hclosed
  have hvol : volume (ball z r) = ENNReal.ofReal (π * r ^ 2) := by
    rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow (le_of_lt hr),
      ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    exact mul_comm _ _
  have hsmall : (volume.restrict unitDisc) (ball z r) < δ := by
    rw [Measure.restrict_apply measurableSet_ball, inter_eq_self_of_subset_left hsub, hvol]
    exact hzvol
  have hm := hmass (ball z r) hsmall
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_self_of_subset_left hsub] at hm
  have hmean := a21_submean_sq hφd hr hclosed
  -- the weight is `≥ r²/4` on the ball
  have hweight : ENNReal.ofReal (r ^ 2 / 4) * ∫⁻ w in ball z r, (‖φ w‖₊ : ℝ≥0∞) ^ 2 ≤
      ∫⁻ w in ball z r, (‖φ w‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_ball
    intro w hw
    rw [mul_comm]
    gcongr
    have hd : ‖w - z‖ < r := by simpa [mem_ball, dist_eq_norm] using hw
    have hw1 := norm_le_norm_add_norm_sub' w z
    have h1 : r ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    unfold rho
    rw [inv_div]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    nlinarith
  have hfinal := (mul_le_mul' le_rfl hmean).trans (hweight.trans hm.le)
  rw [← ENNReal.ofReal_mul (by positivity)] at hfinal
  have hreal : r ^ 2 / 4 * (π * r ^ 2 * ‖φ z‖ ^ 2) ≤ π * ε ^ 2 / 2048 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfinal
  have hpi : π * (r ^ 2 * ‖φ z‖) ^ 2 ≤ π * (ε ^ 2 / 512) := by linarith
  have hb0 : (r ^ 2 * ‖φ z‖) ^ 2 ≤ ε ^ 2 / 512 := le_of_mul_le_mul_left hpi Real.pi_pos
  have hb : (16 * r ^ 2 * ‖φ z‖) ^ 2 < ε ^ 2 := by nlinarith [sq_pos_of_pos hε]
  have hb' : 16 * r ^ 2 * ‖φ z‖ < ε := by
    nlinarith [sq_nonneg (16 * r ^ 2 * ‖φ z‖ + ε), norm_nonneg (φ z)]
  have hnorm : ‖((1 - ‖z‖ ^ 2) ^ 2 : ℂ)‖ = (1 - ‖z‖ ^ 2) ^ 2 := by
    have : ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) = (((1 - ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [dist_zero_right, norm_mul, hnorm]
  have h4 : 1 - ‖z‖ ^ 2 ≤ 4 * r := by rw [hrdef]; nlinarith [norm_nonneg z]
  have h0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  calc (1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖ ≤ (4 * r) ^ 2 * ‖φ z‖ := by gcongr
    _ = 16 * r ^ 2 * ‖φ z‖ := by ring
    _ < ε := hb'

/-- The outer asymptotically conformal extension of `h = w_μ|S¹`, from condition (ii) for `f^μ`. -/
theorem c18_outer {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hS : Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (fB μ) z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)) :
    ∃ r > 1, ∃ Ψ : ℂ → ℂ, IsQuasiconformal Ψ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < r} ∧
      ContinuousOn Ψ {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ < r} ∧ InjOn Ψ {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ < r} ∧
      (∀ z : ℂ, ‖z‖ = 1 → Ψ z = wA μ z) ∧ (∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < r → 1 < ‖Ψ z‖) ∧
      Tendsto (complexDilatation Ψ) (comap (fun z : ℂ => ‖z‖) (𝓝[>] 1)) (𝓝 0) := by
  -- Theorem 1.6 (ii) ⇒ (i) for `f^μ`
  obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective hμ
  obtain ⟨Kq, -, hqd, hbd, -⟩ := hc6_welding_quasidisc hμ
  rw [S2C.s2c_fsans_eq hμ] at hqd hbd
  obtain ⟨R, hR, F, ⟨K, hK⟩, hFf, hμF⟩ := ((thm_1_6 hfd hfi hqd.1 hbd).out 2 1).mp hS
  have hFc : ContinuousOn F (ball 0 R) := hK.2.2.1.1
  have hFi : InjOn F (ball 0 R) := hK.2.2.1.2.1
  -- the welding map `G` (`G ∘ w_μ = f^μ` on `𝔻̄`), as a homeomorphism `e`
  obtain ⟨KG, hKG⟩ := normalizedWeldingExterior_quasiconformal hμ
  obtain ⟨e, he⟩ := t203_pack_homeo hKG (normalizedWeldingExterior_homeomorph hμ).2.2.1
  have hGw : ∀ z ∈ closedBall (0 : ℂ) 1, e (wA μ z) = fB μ z := by
    intro z hz
    rw [he]
    exact normalizedWeldingExterior_closedDisk hμ hz
  have hGd : DifferentiableOn ℂ e unitDiscExterior := by
    rw [he]
    exact normalizedWeldingExterior_differentiableOn hμ
  have hEo : IsOpen unitDiscExterior := resolvent_exterior_isOpen
  have hball : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∈ ball (0 : ℂ) R := fun z hz => mem_ball_zero_iff.mpr (by linarith)
  -- `F = G ∘ w_μ` on `𝔻̄`
  have hFw : ∀ z ∈ closedBall (0 : ℂ) 1, F z = e (wA μ z) := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have hcl : z ∈ closure unitDisc := by
      show z ∈ closure (ball (0 : ℂ) 1)
      rw [closure_ball (0 : ℂ) one_ne_zero]
      exact hz
    have : (𝓝[unitDisc] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have h1 : Tendsto F (𝓝[unitDisc] z) (𝓝 (F z)) :=
      ((hFc z (hball z hz1)).continuousAt (isOpen_ball.mem_nhds (hball z hz1))).tendsto.mono_left
        nhdsWithin_le_nhds
    have hgc : ContinuousWithinAt (fun w => e (wA μ w)) (closedBall (0 : ℂ) 1) z :=
      e.continuous.continuousAt.comp_continuousWithinAt (crc_wA_continuous_closed hμ z hz)
    have h2 : Tendsto (fun w => e (wA μ w)) (𝓝[unitDisc] z) (𝓝 (e (wA μ z))) :=
      hgc.tendsto.mono_left (nhdsWithin_mono _ ball_subset_closedBall)
    have h3 : Tendsto F (𝓝[unitDisc] z) (𝓝 (e (wA μ z))) := by
      apply h2.congr'
      filter_upwards [self_mem_nhdsWithin] with w hw
      rw [hFf hw, hGw w (ball_subset_closedBall hw)]
    exact tendsto_nhds_unique h1 h3
  -- outside `𝔻̄`, `e⁻¹ ∘ F` lands in `𝔻*`
  have hout : ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < R → 1 < ‖e.symm (F z)‖ := by
    intro z hz1 hzR
    by_contra hcon
    have hu : e.symm (F z) ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr (not_lt.mp hcon)
    have hu' : ((e.symm (F z) : ℂ) : ExtPlane) ∈ wAS μ '' toExt (closedBall (0 : ℂ) 1) := by
      rw [wAS_closed_image hμ]
      exact ⟨_, hu, rfl⟩
    obtain ⟨_, ⟨v, hv, rfl⟩, hvu⟩ := hu'
    have hwv : wA μ v = e.symm (F z) := by
      show finPart (wAS μ (v : ExtPlane)) = _
      rw [hvu, finPart_coe]
    have hFv : F v = F z := by rw [hFw v hv, hwv, e.apply_symm_apply]
    have hvz := hFi (hball v (mem_closedBall_zero_iff.mp hv)) (mem_ball_zero_iff.mpr hzR) hFv
    rw [hvz] at hv
    linarith [mem_closedBall_zero_iff.mp hv]
  -- the open annulus
  have hAo : IsOpen {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAsub : {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R} ⊆ ball (0 : ℂ) R := fun z hz => mem_ball_zero_iff.mpr hz.2
  -- `e⁻¹` is conformal on `E = e(𝔻*)`
  obtain ⟨E, hEd⟩ : ∃ E : Set ℂ, E = ⇑e.symm ⁻¹' unitDiscExterior := ⟨_, rfl⟩
  have hEo' : IsOpen E := by rw [hEd]; exact hEo.preimage e.symm.continuous
  have hinvd : ∀ w ∈ E, DifferentiableAt ℂ e.symm w := by
    intro w hw
    rw [hEd] at hw
    have hev : ∀ᶠ v in 𝓝 (e (e.symm w)), e.symm v ∈ unitDiscExterior ∧ e (e.symm v) = v := by
      rw [e.apply_symm_apply]
      have hwE : w ∈ E := by rw [hEd]; exact hw
      filter_upwards [hEo'.mem_nhds hwE] with v hv
      rw [hEd] at hv
      exact ⟨hv, e.apply_symm_apply v⟩
    have h := s82td_inverse_differentiableAt hEo hGd (e.injective.injOn) (z := e.symm w) hw hev
    rwa [e.apply_symm_apply] at h
  have hconf : IsConformalOnto e.symm E unitDiscExterior := by
    refine ⟨fun w hw => (hinvd w hw).differentiableWithinAt, e.symm.injective.injOn, ?_⟩
    rw [hEd]
    exact image_preimage_eq _ e.symm.surjective
  have hFE : F '' {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R} ⊆ E := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hEd]
    exact hout z hz.1 hz.2
  have hQC : IsKQC (⇑e.symm ∘ F) {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R} (K * 1) :=
    thm7_1_comp (t3b_isKQC_restrict hK hAo hAsub) (isKQC_one_of_conformal hEo' hconf) hFE
  have hcsub : {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ < R} ⊆ ball (0 : ℂ) R := fun z hz => mem_ball_zero_iff.mpr hz.2
  refine ⟨R, hR, ⇑e.symm ∘ F, ⟨K * 1, hQC⟩, e.symm.continuous.comp_continuousOn (hFc.mono hcsub),
    e.symm.injective.comp_injOn (hFi.mono hcsub), ?_, fun z h1 h2 => hout z h1 h2, ?_⟩
  · intro z hz
    rw [Function.comp_apply, hFw z (mem_closedBall_zero_iff.mpr hz.le), e.symm_apply_apply]
  · -- `μ_{e⁻¹ ∘ F} = μ_F` on the annulus
    apply hμF.congr'
    have hann : ∀ᶠ z in comap (fun z : ℂ => ‖z‖) (𝓝[>] 1), ‖z‖ ∈ Ioo 1 R :=
      tendsto_comap.eventually (Ioo_mem_nhdsGT hR)
    filter_upwards [hann] with z hz
    have hzA : z ∈ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R} := hz
    have hzB : z ∈ ball (0 : ℂ) R := hAsub hzA
    have hFzE : F z ∈ E := hFE ⟨z, hzA, rfl⟩
    have hu : e.symm (F z) ∈ unitDiscExterior := by rw [hEd] at hFzE; exact hFzE
    have hk : DifferentiableAt ℂ e (e.symm (F z)) := hGd.differentiableAt (hEo.mem_nhds hu)
    exact (s23_dilatation_comp_left ((hFc z hzB).continuousAt (isOpen_ball.mem_nhds hzB))
      (hinvd (F z) hFzE) hk (Filter.Eventually.of_forall e.apply_symm_apply)).symm

/-- Reflection in `S¹` and removability of `S¹`: a two-sided asymptotically conformal extension. -/
theorem c18_two_sided {h Ψ : ℂ → ℂ} {r : ℝ} (hr : 1 < r) (hh : ∀ z : ℂ, ‖z‖ = 1 → ‖h z‖ = 1)
    (hq : IsQuasiconformal Ψ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < r})
    (hc : ContinuousOn Ψ {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ < r}) (hi : InjOn Ψ {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ < r})
    (hb : ∀ z : ℂ, ‖z‖ = 1 → Ψ z = h z) (hout : ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < r → 1 < ‖Ψ z‖)
    (hμ : Tendsto (complexDilatation Ψ) (comap (fun z : ℂ => ‖z‖) (𝓝[>] 1)) (𝓝 0)) :
    ∃ r' > 1, ∃ Φ : ℂ → ℂ, IsQuasiconformal Φ {z : ℂ | 1 / r' < ‖z‖ ∧ ‖z‖ < r'} ∧
      (∀ z : ℂ, ‖z‖ = 1 → Φ z = h z) ∧
      Tendsto (complexDilatation Φ) (comap (fun z : ℂ => ‖z‖) (𝓝[≠] 1)) (𝓝 0) := by
  obtain ⟨K, hK⟩ := hq
  have hr0 : 0 < r := by linarith
  have hr1 : 1 / r < 1 := (div_lt_one hr0).mpr hr
  have hrpos : 0 < 1 / r := one_div_pos.mpr hr0
  set A : Set ℂ := {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < r} with hAdef
  set A' : Set ℂ := {z : ℂ | 1 / r < ‖z‖ ∧ ‖z‖ < 1} with hA'def
  set S : Set ℂ := {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ < r} with hSdef
  set T : Set ℂ := {z : ℂ | 1 / r < ‖z‖ ∧ ‖z‖ ≤ 1} with hTdef
  set Ω : Set ℂ := {z : ℂ | 1 / r < ‖z‖ ∧ ‖z‖ < r} with hΩdef
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hA'o : IsOpen A' :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hΩo : IsOpen Ω :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  -- the reflection `σ z = 1/z̄` exchanges the two sides
  have hinvlt : ∀ z : ℂ, 1 / r < ‖z‖ → 0 < ‖z‖ ∧ ‖z‖⁻¹ < r := by
    intro z hz
    have h0 : 0 < ‖z‖ := lt_trans hrpos hz
    exact ⟨h0, (inv_lt_comm₀ h0 hr0).mpr (by rwa [one_div] at hz)⟩
  have hσA : ∀ z ∈ A', (conj z)⁻¹ ∈ A := by
    intro z hz
    obtain ⟨h0, h1⟩ := hinvlt z hz.1
    show 1 < ‖(conj z)⁻¹‖ ∧ ‖(conj z)⁻¹‖ < r
    rw [abR_t_norm_inv_conj]
    exact ⟨(one_lt_inv₀ h0).mpr hz.2, h1⟩
  have hTS : MapsTo (fun z : ℂ => (conj z)⁻¹) T S := by
    intro z hz
    obtain ⟨h0, h1⟩ := hinvlt z hz.1
    show 1 ≤ ‖(conj z)⁻¹‖ ∧ ‖(conj z)⁻¹‖ < r
    rw [abR_t_norm_inv_conj]
    exact ⟨(one_le_inv₀ h0).mpr hz.2, h1⟩
  have hT0 : ∀ z ∈ T, z ≠ 0 := fun z hz => norm_pos_iff.mp (hinvlt z hz.1).1
  have hA'0 : A' ⊆ {0}ᶜ := fun z hz => mem_compl_singleton_iff.mpr (norm_pos_iff.mp (hinvlt z hz.1).1)
  have hΨS : ∀ w ∈ S, 1 ≤ ‖Ψ w‖ := by
    intro w hw
    rcases hw.1.lt_or_eq with h1 | h1
    · exact (hout w h1 hw.2).le
    · rw [hb w h1.symm, hh w h1.symm]
  have hΨ0 : ∀ w ∈ S, Ψ w ≠ 0 := fun w hw h0 => by
    have := hΨS w hw
    rw [h0, norm_zero] at this
    linarith
  -- the inner map `Φ_in = σ ∘ Ψ ∘ σ`
  obtain ⟨Φin, hΦin⟩ : ∃ f : ℂ → ℂ,
      f = (fun w : ℂ => w⁻¹) ∘ ((fun z => conj (Ψ (conj z))) ∘ fun w : ℂ => w⁻¹) := ⟨_, rfl⟩
  have hΦin_apply : ∀ z, Φin z = (conj (Ψ (conj z)⁻¹))⁻¹ := by
    intro z
    rw [hΦin]
    simp only [Function.comp_apply, map_inv₀]
  have hΦin_cont : ContinuousOn Φin T := by
    have hσc : ContinuousOn (fun z : ℂ => (conj z)⁻¹) T :=
      Complex.continuous_conj.continuousOn.inv₀ (fun z hz => (map_ne_zero _).2 (hT0 z hz))
    have h2 : ContinuousOn (fun z => Ψ (conj z)⁻¹) T := hc.comp hσc hTS
    have h3 : ContinuousOn (fun z => (conj (Ψ (conj z)⁻¹))⁻¹) T :=
      (Complex.continuous_conj.comp_continuousOn h2).inv₀
        (fun z hz => (map_ne_zero _).2 (hΨ0 _ (hTS hz)))
    exact h3.congr (fun z _ => hΦin_apply z)
  have hglue : ∀ z : ℂ, ‖z‖ = 1 → Φin z = Ψ z := by
    intro z hz
    rw [hΦin_apply, abR_t_inv_conj_of_norm_one hz, hb z hz, abR_t_inv_conj_of_norm_one (hh z hz)]
  have hΦin_lt : ∀ z ∈ A', ‖Φin z‖ < 1 := by
    intro z hz
    have hσ := hσA z hz
    rw [hΦin_apply, norm_inv, Complex.norm_conj]
    exact inv_lt_one_of_one_lt₀ (hout _ hσ.1 hσ.2)
  -- the glued map `Φ`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ → ℂ, Φ = fun z => if 1 ≤ ‖z‖ then Ψ z else Φin z := ⟨_, rfl⟩
  have hΦo : ∀ z : ℂ, 1 ≤ ‖z‖ → Φ z = Ψ z := by
    intro z hz
    rw [hΦ]
    simp only [hz, ↓reduceIte]
  have hΦi : ∀ z : ℂ, ‖z‖ < 1 → Φ z = Φin z := by
    intro z hz
    have hz' : ¬ 1 ≤ ‖z‖ := not_le.mpr hz
    rw [hΦ]
    simp only [hz', ↓reduceIte]
  have hΦT : ∀ z : ℂ, ‖z‖ ≤ 1 → Φ z = Φin z := by
    intro z hz
    rcases hz.lt_or_eq with h1 | h1
    · exact hΦi z h1
    · rw [hΦo z h1.ge, hglue z h1]
  -- continuity and injectivity on the annulus `Ω`
  have hΦc : ContinuousOn Φ Ω := by
    intro x hx
    have hsub : Ω ⊆ S ∪ T := fun z hz => by
      rcases le_or_gt 1 ‖z‖ with h1 | h1
      · exact Or.inl ⟨h1, hz.2⟩
      · exact Or.inr ⟨hz.1, h1.le⟩
    apply ContinuousWithinAt.mono _ hsub
    rw [continuousWithinAt_union]
    constructor
    · by_cases hxS : x ∈ S
      · exact (hc x hxS).congr (fun y hy => hΦo y hy.1) (hΦo x hxS.1)
      · apply continuousWithinAt_of_notMem_closure
        intro hcl
        have h1 : x ∈ {y : ℂ | 1 ≤ ‖y‖} :=
          closure_minimal (fun y hy => hy.1) (isClosed_le continuous_const continuous_norm) hcl
        exact hxS ⟨h1, hx.2⟩
    · by_cases hxT : x ∈ T
      · exact (hΦin_cont x hxT).congr (fun y hy => hΦT y hy.2) (hΦT x hxT.2)
      · apply continuousWithinAt_of_notMem_closure
        intro hcl
        have h1 : x ∈ {y : ℂ | ‖y‖ ≤ 1} :=
          closure_minimal (fun y hy => hy.2) (isClosed_le continuous_norm continuous_const) hcl
        exact hxT ⟨hx.1, h1⟩
  have hΦinj : InjOn Φ Ω := by
    intro a ha b hb' hab
    rcases le_or_gt 1 ‖a‖ with h1 | h1 <;> rcases le_or_gt 1 ‖b‖ with h2 | h2
    · rw [hΦo a h1, hΦo b h2] at hab
      exact hi ⟨h1, ha.2⟩ ⟨h2, hb'.2⟩ hab
    · exfalso
      rw [hΦo a h1, hΦi b h2] at hab
      have h3 := hΦin_lt b ⟨hb'.1, h2⟩
      rw [← hab] at h3
      linarith [hΨS a ⟨h1, ha.2⟩]
    · exfalso
      rw [hΦi a h1, hΦo b h2] at hab
      have h3 := hΦin_lt a ⟨ha.1, h1⟩
      rw [hab] at h3
      linarith [hΨS b ⟨h2, hb'.2⟩]
    · rw [hΦi a h1, hΦi b h2, hΦin_apply, hΦin_apply] at hab
      have h3 : Ψ (conj a)⁻¹ = Ψ (conj b)⁻¹ := by
        have h4 := congrArg (fun w => conj w⁻¹) hab
        simpa using h4
      have hσa := hσA a ⟨ha.1, h1⟩
      have hσb := hσA b ⟨hb'.1, h2⟩
      have h5 := hi ⟨hσa.1.le, hσa.2⟩ ⟨hσb.1.le, hσb.2⟩ h3
      rw [← abR_t_conj_inv_inv a, ← abR_t_conj_inv_inv b, h5]
  -- `Φ_in` is `K`-q.c. on `A'`
  have hpre : conj ⁻¹' A = A := by
    ext z
    simp only [mem_preimage, hAdef, mem_ofPred_eq, Complex.norm_conj]
  have hgA : IsKQC (fun z => conj (Ψ (conj z))) A K := by
    have := abR_x_isKQC_conj hK
    rwa [hpre] at this
  have hinvA' : IsKQC (fun w : ℂ => w⁻¹) A' 1 :=
    isKQC_one_of_conformal hA'o (D' := (fun w : ℂ => w⁻¹) '' A')
      ⟨nx_inv_isConformalOnto.1.mono hA'0, nx_inv_isConformalOnto.2.1.mono hA'0, rfl⟩
  have hinv0 : IsKQC (fun w : ℂ => w⁻¹) {0}ᶜ 1 :=
    isKQC_one_of_conformal isOpen_compl_singleton nx_inv_isConformalOnto
  have hsub1 : (fun w : ℂ => w⁻¹) '' A' ⊆ A := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨h0, h1⟩ := hinvlt z hz.1
    show 1 < ‖z⁻¹‖ ∧ ‖z⁻¹‖ < r
    rw [norm_inv]
    exact ⟨(one_lt_inv₀ h0).mpr hz.2, h1⟩
  have hsub2 : ((fun z => conj (Ψ (conj z))) ∘ fun w : ℂ => w⁻¹) '' A' ⊆ {0}ᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    have hzA := hsub1 ⟨z, hz, rfl⟩
    have hcA : conj z⁻¹ ∈ A := by rw [← hpre] at hzA; exact hzA
    exact mem_compl_singleton_iff.mpr ((map_ne_zero _).2 (hΨ0 _ ⟨hcA.1.le, hcA.2⟩))
  have h1 := thm7_1_comp hinvA' hgA hsub1
  have h2 := thm7_1_comp h1 hinv0 hsub2
  rw [one_mul, mul_one] at h2
  have hΦinK : IsKQC Φin A' K := by rw [hΦin]; exact h2
  -- removability of `S¹`
  have hΦK : IsKQC Φ Ω K := by
    refine s13x_removable (L := sphere (0 : ℂ) 1) hΩo hK.2.1
      (qcl_f_isHomeomorphOnto_of_injOn hΩo hΦc hΦinj) (Measure.addHaar_sphere volume 0 1)
      (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun y => ?_) ?_
    · refine Set.Countable.mono (fun s hs => ?_) (abR_c_countable_circle x)
      have := abR_c_norm_eq_one (mem_sphere_zero_iff_norm.mp hs)
      show s ^ 2 + x ^ 2 = 1
      linarith
    · refine Set.Countable.mono (fun s hs => ?_) (abR_c_countable_circle y)
      exact abR_c_norm_eq_one (mem_sphere_zero_iff_norm.mp hs)
    · intro z hz
      have hz1 : ‖z‖ ≠ 1 := fun h => hz.2 (mem_sphere_zero_iff_norm.mpr h)
      rcases lt_or_gt_of_ne hz1 with h1 | h1
      · exact ⟨A', hA'o, ⟨hz.1.1, h1⟩, fun w hw => ⟨hw.1, by linarith [hw.2]⟩,
          ad_isKQC_congr hΦinK (fun w hw => hΦi w hw.2)⟩
      · exact ⟨A, hAo, ⟨h1, hz.1.2⟩, fun w hw => ⟨by linarith [hw.1], hw.2⟩,
          ad_isKQC_congr hK (fun w hw => hΦo w hw.1.le)⟩
  -- the dilatation: equal to `μ_Ψ` outside, bounded by `|μ_Ψ ∘ σ|` inside
  have hdil_out : ∀ z ∈ A, complexDilatation Φ z = complexDilatation Ψ z := fun z hz =>
    abR_t_complexDilatation_congr hAo (fun w hw => hΦo w hw.1.le) hz
  have hdil_in : ∀ z ∈ A', ‖complexDilatation Φ z‖ ≤ ‖complexDilatation Ψ (conj z)⁻¹‖ := by
    intro z hz
    have hz0 : z ≠ 0 := mem_compl_singleton_iff.mp (hA'0 hz)
    rw [abR_t_complexDilatation_congr hA'o (fun w hw => hΦi w hw.2) hz]
    have hσz := hσA z hz
    have hcz : conj z⁻¹ = (conj z)⁻¹ := map_inv₀ _ _
    have hgz : (fun z => conj (Ψ (conj z))) z⁻¹ ≠ 0 := by
      show conj (Ψ (conj z⁻¹)) ≠ 0
      rw [hcz]
      exact (map_ne_zero _).2 (hΨ0 _ ⟨hσz.1.le, hσz.2⟩)
    have hN : Φin = nxInvConj (fun z => conj (Ψ (conj z))) := by rw [hΦin]; rfl
    by_cases hd : DifferentiableAt ℝ Ψ (conj z)⁻¹
    · refine le_of_eq ?_
      have hd' : DifferentiableAt ℝ Ψ (conj z⁻¹) := by rw [hcz]; exact hd
      obtain ⟨hgd, hdz, hdzbar⟩ := abR_x_dz_dzbar_conj hd'
      rw [hN, nxI2_dilatation_invConj_at hz0 hgz hgd, norm_mul]
      have hn1 : ‖z ^ 2 / conj z ^ 2‖ = 1 := by
        rw [norm_div, norm_pow, norm_pow, Complex.norm_conj]
        exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.2 hz0))
      rw [hn1, mul_one, complexDilatation, complexDilatation, hdz, hdzbar, norm_div, norm_div,
        Complex.norm_conj, Complex.norm_conj, hcz]
    · -- `Φ_in` is not differentiable at `z` either, so both sides are junk-free: `μ_{Φ_in}(z) = 0`
      have hnd : ¬ DifferentiableAt ℝ Φin z := by
        intro hdΦ
        apply hd
        have hconjd : ∀ w : ℂ, DifferentiableAt ℝ (fun w : ℂ => conj w) w := fun w =>
          ((conjCLE : ℂ →L[ℝ] ℂ).differentiableAt : DifferentiableAt ℝ (conjCLE : ℂ →L[ℝ] ℂ) w)
        have hinvd : ∀ w : ℂ, w ≠ 0 → DifferentiableAt ℝ (fun w : ℂ => w⁻¹) w := fun w hw =>
          (differentiableAt_inv (𝕜 := ℂ) hw).restrictScalars ℝ
        have hw0 : (conj z)⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero _).2 hz0)
        have e1 : DifferentiableAt ℝ (fun w : ℂ => (conj w)⁻¹) (conj z)⁻¹ :=
          (hinvd _ ((map_ne_zero _).2 hw0)).comp _ (hconjd _)
        have e2 : DifferentiableAt ℝ Φin (conj (conj z)⁻¹)⁻¹ := by rw [abR_t_conj_inv_inv]; exact hdΦ
        have e3' : DifferentiableAt ℝ (fun w : ℂ => Φin (conj w)⁻¹) (conj z)⁻¹ :=
          DifferentiableAt.comp (f := fun w : ℂ => (conj w)⁻¹) _ e2 e1
        have e3 : DifferentiableAt ℝ (fun w : ℂ => conj (Φin (conj w)⁻¹)) (conj z)⁻¹ :=
          DifferentiableAt.comp (f := fun w : ℂ => Φin (conj w)⁻¹) _ (hconjd _) e3'
        have hne : conj (Φin (conj (conj z)⁻¹)⁻¹) ≠ 0 := by
          rw [abR_t_conj_inv_inv, hΦin_apply]
          exact (map_ne_zero _).2 (inv_ne_zero ((map_ne_zero _).2 (hΨ0 _ ⟨hσz.1.le, hσz.2⟩)))
        have e4 : DifferentiableAt ℝ (fun w : ℂ => (conj (Φin (conj w)⁻¹))⁻¹) (conj z)⁻¹ :=
          DifferentiableAt.comp (f := fun w : ℂ => conj (Φin (conj w)⁻¹)) _ (hinvd _ hne) e3
        apply e4.congr_of_eventuallyEq
        exact Eventually.of_forall (fun w => by
          show Ψ w = (conj (Φin (conj w)⁻¹))⁻¹
          rw [hΦin_apply]
          simp [map_inv₀])
      have h0 : complexDilatation Φin z = 0 := by
        simp [complexDilatation, dz, dzbar, fderiv_zero_of_not_differentiableAt hnd]
      rw [h0, norm_zero]
      exact norm_nonneg _
  -- the limit
  refine ⟨r, hr, Φ, ⟨K, hΦK⟩, fun z hz => by rw [hΦo z hz.ge, hb z hz], ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := (Metric.tendsto_nhds.mp hμ) ε hε
  rw [Filter.eventually_comap] at hev
  obtain ⟨u, hu1, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min u r := ⟨_, rfl⟩
  have hδ1 : 1 < δ := by rw [hδ]; exact lt_min hu1 hr
  have hδu : δ ≤ u := by rw [hδ]; exact min_le_left _ _
  have hδr : δ ≤ r := by rw [hδ]; exact min_le_right _ _
  have hδ0 : 0 < δ := by linarith
  have hsmall : ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < δ → ‖complexDilatation Ψ w‖ < ε := by
    intro w hw1 hw2
    have h := hu ⟨hw1, lt_of_lt_of_le hw2 hδu⟩ w rfl
    rwa [dist_zero_right] at h
  have hset : {(1 : ℝ)}ᶜ ∩ Ioo (1 / δ) δ ∈ 𝓝[≠] (1 : ℝ) :=
    inter_mem_nhdsWithin _ (Ioo_mem_nhds ((div_lt_one hδ0).mpr hδ1) hδ1)
  filter_upwards [tendsto_comap.eventually hset] with z hz
  rw [dist_zero_right]
  have hne : ‖z‖ ≠ 1 := hz.1
  obtain ⟨hz1, hz2⟩ := hz.2
  rcases lt_or_gt_of_ne hne with h | h
  · have hrδ : 1 / r ≤ 1 / δ := one_div_le_one_div_of_le hδ0 hδr
    have hzA' : z ∈ A' := ⟨lt_of_le_of_lt hrδ hz1, h⟩
    have h0 : 0 < ‖z‖ := lt_trans (one_div_pos.mpr hδ0) hz1
    refine lt_of_le_of_lt (hdil_in z hzA') (hsmall _ ?_ ?_)
    · rw [abR_t_norm_inv_conj]
      exact (one_lt_inv₀ h0).mpr h
    · rw [abR_t_norm_inv_conj, inv_lt_comm₀ h0 hδ0]
      rwa [one_div] at hz1
  · rw [hdil_out z ⟨h, lt_of_lt_of_le hz2 hδr⟩]
    exact hsmall z h hz2

/-- The splitting near `S¹`: for every `K > 1`, `Φ = H ∘ W` on `S¹` with `W` a plane `K`-q.c. map and `H` conformal on
a neighbourhood of `W(S¹)`. -/
theorem c18_split {Φ : ℂ → ℂ} {r : ℝ} (hr : 1 < r)
    (hq : IsQuasiconformal Φ {z : ℂ | 1 / r < ‖z‖ ∧ ‖z‖ < r})
    (hμ : Tendsto (complexDilatation Φ) (comap (fun z : ℂ => ‖z‖) (𝓝[≠] 1)) (𝓝 0)) {K : ℝ} (hK : 1 < K) :
    ∃ W H : ℂ → ℂ, ∃ U : Set ℂ, IsKQC W univ K ∧ W '' univ = univ ∧ IsOpen U ∧
      W '' sphere (0 : ℂ) 1 ⊆ U ∧ DifferentiableOn ℂ H U ∧ InjOn H U ∧
      ∀ z : ℂ, ‖z‖ = 1 → Φ z = H (W z) := by
  obtain ⟨KΦ, hKΦ⟩ := hq
  have hr0 : 0 < r := by linarith
  -- the bound `k` with `(1 + k)/(1 - k) = K`
  obtain ⟨k, hkd⟩ : ∃ k : ℝ, k = (K - 1) / (K + 1) := ⟨_, rfl⟩
  have hk0 : 0 ≤ k := by rw [hkd]; exact div_nonneg (by linarith) (by linarith)
  have hk1 : k < 1 := by rw [hkd, div_lt_one (by linarith)]; linarith
  have hkpos : 0 < k := by rw [hkd]; exact div_pos (by linarith) (by linarith)
  have hKk : (1 + k) / (1 - k) = K := by
    rw [hkd]
    have h1 : K + 1 ≠ 0 := by linarith
    field_simp
    ring
  -- a thin two-sided annulus `A` on which `|μ_Φ| < k` off `S¹`
  have hev := (Metric.tendsto_nhds.mp hμ) k hkpos
  rw [Filter.eventually_comap] at hev
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.mp hev
  obtain ⟨ρ, hρd⟩ : ∃ ρ : ℝ, ρ = min r (1 + ε / 2) := ⟨_, rfl⟩
  have hρ1 : 1 < ρ := by rw [hρd]; exact lt_min hr (by linarith)
  have hρr : ρ ≤ r := by rw [hρd]; exact min_le_left _ _
  have hρε : ρ ≤ 1 + ε / 2 := by rw [hρd]; exact min_le_right _ _
  have hρ0 : 0 < ρ := by linarith
  have hsmall : ∀ z : ℂ, 1 / ρ < ‖z‖ → ‖z‖ < ρ → ‖z‖ ≠ 1 → ‖complexDilatation Φ z‖ < k := by
    intro z h1 h2 h3
    have hlow : 1 - ε / 2 < ‖z‖ := by
      have : 1 - ε / 2 ≤ 1 / ρ := by
        rw [le_div_iff₀ hρ0]
        nlinarith
      linarith
    have hmem : ‖z‖ ∈ ball (1 : ℝ) ε ∩ {(1 : ℝ)}ᶜ := by
      refine ⟨?_, h3⟩
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have h := hεs hmem z rfl
    rwa [dist_zero_right] at h
  set A : Set ℂ := {z : ℂ | 1 / ρ < ‖z‖ ∧ ‖z‖ < ρ} with hAdef
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAm : MeasurableSet A := hAo.measurableSet
  have hAsub : A ⊆ {z : ℂ | 1 / r < ‖z‖ ∧ ‖z‖ < r} := fun z hz =>
    ⟨lt_of_le_of_lt (one_div_le_one_div_of_le hρ0 hρr) hz.1, lt_of_lt_of_le hz.2 hρr⟩
  have hsphA : sphere (0 : ℂ) 1 ⊆ A := by
    intro z hz
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    exact ⟨by rw [hz1, div_lt_one hρ0]; exact hρ1, by rw [hz1]; exact hρ1⟩
  -- the coefficient `m = μ_Φ · 1_A` and the plane solution `W`
  have hμm : Measurable (complexDilatation Φ) := (measurable_dzbar Φ).div (measurable_dz Φ)
  have h3 : ∀ᵐ z : ℂ, z ∉ sphere (0 : ℂ) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume 0 1)
  have hm : IsBeltramiCoeff (A.indicator (complexDilatation Φ)) univ k := by
    refine ⟨by simpa only [Measure.restrict_univ] using (hμm.indicator hAm).aestronglyMeasurable, ?_⟩
    rw [Measure.restrict_univ]
    filter_upwards [h3] with z hz
    by_cases hzA : z ∈ A
    · rw [indicator_of_mem hzA]
      exact (hsmall z hzA.1 hzA.2 (fun h => hz (mem_sphere_zero_iff_norm.mpr h))).le
    · rw [indicator_of_notMem hzA, norm_zero]
      exact hk0
  obtain ⟨W, hWn, hWK, -⟩ := thm13_7_normalized_existence hk0 hk1 hm
  rw [hKk] at hWK
  -- equal dilatations on `A`
  have hdil : ∀ᵐ z ∂(volume.restrict A), complexDilatation W z = complexDilatation Φ z := by
    rw [ae_restrict_iff' hAm]
    filter_upwards [hWn.2.2.2.2] with z hz hzA
    rw [hz, indicator_of_mem hzA]
  have hWA : IsKQC W A K := t3b_isKQC_restrict hWK hAo (subset_univ _)
  have hΦA : IsKQC Φ A KΦ := t3b_isKQC_restrict hKΦ hAo hAsub
  obtain ⟨hβW, hsolW⟩ := thm10_2_genHomeoSolution_of_isKQC hWA
  obtain ⟨-, hsolΦ⟩ := thm10_2_genHomeoSolution_of_isKQC hΦA
  have hsolΦ' : IsGenHomeoSolution Φ (complexDilatation W) A 2 := by
    obtain ⟨hghom, gx, gy, hgp, hgae⟩ := hsolΦ
    refine ⟨hghom, gx, gy, hgp, ?_⟩
    filter_upwards [hgae, hdil] with z h1 h2
    rw [h2]
    exact h1
  have hk' : (K - 1) / (K + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨φ, hφ, hΦφ⟩ := same_dilatation_conformal hAo hk' hβW hsolW hsolΦ'
  exact ⟨W, φ, W '' A, hWK, hWn.2.1, t3b_isOpenMap hWK (subset_univ _) hAo, image_mono hsphA,
    hφ.1, hφ.2.1, fun z hz => hΦφ z (hsphA (mem_sphere_zero_iff_norm.mpr hz))⟩

/-- Circle distortion for symmetric triples: `|W c - W b| ≤ λ(K) |W a - W b|` when `|a - b| = |c - b|`. -/
theorem c18_ratio_W {W : ℂ → ℂ} {K : ℝ} (hW : IsKQC W univ K) (hs : W '' univ = univ) {a b c : ℂ}
    (habc : ‖a - b‖ = ‖c - b‖) (hab : a ≠ b) :
    ‖W c - W b‖ ≤ lambdaInv K * ‖W a - W b‖ := by
  have hr : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hd := thm15_4_circle_distortion hW hs b hr
  have hcont : Continuous W := continuousOn_univ.mp hW.2.2.1.1
  have hpt : ∀ x : ℂ, x - b ≠ 0 → x = b + (‖x - b‖ : ℂ) * exp ((arg (x - b) : ℂ) * I) := by
    intro x hx
    have := Complex.norm_mul_exp_arg_mul_I (x - b)
    rw [this]
    ring
  obtain ⟨C, hC⟩ := (isCompact_sphere b ‖a - b‖).exists_bound_of_continuousOn hcont.continuousOn
  have hbdd : BddAbove (range fun θ : ℝ => ‖W (b + ‖a - b‖ * exp (θ * I)) - W b‖) := by
    refine ⟨C + ‖W b‖, ?_⟩
    rintro _ ⟨θ, rfl⟩
    have hm : b + (‖a - b‖ : ℂ) * exp (θ * I) ∈ sphere b ‖a - b‖ := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hr.le, norm_exp_ofReal_mul_I, mul_one]
    exact (norm_sub_le _ _).trans (by linarith [hC _ hm])
  have hbddb : BddBelow (range fun θ : ℝ => ‖W (b + ‖a - b‖ * exp (θ * I)) - W b‖) :=
    ⟨0, by rintro _ ⟨θ, rfl⟩; exact norm_nonneg _⟩
  have hc0 : c - b ≠ 0 := by
    intro h
    rw [h, norm_zero] at habc
    linarith
  have hcm : ‖W c - W b‖ ≤ sSup (range fun θ : ℝ => ‖W (b + ‖a - b‖ * exp (θ * I)) - W b‖) := by
    refine le_csSup hbdd ⟨arg (c - b), ?_⟩
    dsimp only
    rw [habc, ← hpt c hc0]
  have ham : sInf (range fun θ : ℝ => ‖W (b + ‖a - b‖ * exp (θ * I)) - W b‖) ≤ ‖W a - W b‖ := by
    refine csInf_le hbddb ⟨arg (a - b), ?_⟩
    dsimp only
    rw [← hpt a (sub_ne_zero.mpr hab)]
  have hl : 0 ≤ lambdaInv K := by linarith [td_one_le_lambdaInv hW.2.1]
  exact hcm.trans (hd.trans (mul_le_mul_of_nonneg_left ham hl))

/-- A conformal map distorts small-scale ratios on a compact set by a factor close to `1`. -/
theorem c18_ratio_H {H : ℂ → ℂ} {U C : Set ℂ} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (hH : DifferentiableOn ℂ H U) (hinj : InjOn H U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ C, ∀ q ∈ C, ∀ s ∈ C, ‖p - q‖ < δ → ‖s - q‖ < δ →
      ‖H s - H q‖ * ‖p - q‖ ≤ (1 + ε) * ‖H p - H q‖ * ‖s - q‖ := by
  obtain ⟨δ0, hδ0, hthick⟩ := hC.exists_cthickening_subset_open hU hCU
  have hK' : IsCompact (cthickening δ0 C) := hC.cthickening
  have hHd : DifferentiableOn ℂ (deriv H) U := hH.deriv hU
  have hcont' : ContinuousOn (deriv H) (cthickening δ0 C) := hHd.continuousOn.mono hthick
  have hne : ∀ y ∈ U, deriv H y ≠ 0 := fun y hy => deriv_ne_zero_of_injOn hU hH hinj hy
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ q ∈ C, m ≤ ‖deriv H q‖ := by
    by_cases hCe : C.Nonempty
    · obtain ⟨q0, hq0, hmin⟩ := hC.exists_isMinOn hCe
        (continuous_norm.comp_continuousOn (hcont'.mono (self_subset_cthickening C)))
      exact ⟨‖deriv H q0‖, norm_pos_iff.mpr (hne q0 (hCU hq0)), fun q hq => hmin hq⟩
    · exact ⟨1, one_pos, fun q hq => absurd ⟨q, hq⟩ hCe⟩
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε * m / (2 + ε) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  obtain ⟨δ1, hδ1, hu⟩ := Metric.uniformContinuousOn_iff.mp
    (hK'.uniformContinuousOn_of_continuous hcont') ε' hε'0
  refine ⟨min δ0 δ1, lt_min hδ0 hδ1, fun p hp q hq s hs hpq hsq => ?_⟩
  -- the linear approximation at `q`
  have hlin : ∀ x : ℂ, ‖x - q‖ < min δ0 δ1 → ‖H x - H q - deriv H q * (x - q)‖ ≤ ε' * ‖x - q‖ := by
    intro x hx
    have hball : ball q (min δ0 δ1) ⊆ cthickening δ0 C := fun y hy =>
      mem_cthickening_of_dist_le y q δ0 C hq ((le_of_lt (lt_of_lt_of_le hy (min_le_left _ _))))
    have hdiff : ∀ y ∈ ball q (min δ0 δ1), DifferentiableAt ℂ (fun w => H w - deriv H q * w) y := by
      intro y hy
      exact ((hH.differentiableAt (hU.mem_nhds (hthick (hball hy)))).sub
        ((differentiableAt_id.const_mul (deriv H q))))
    have hbound : ∀ y ∈ ball q (min δ0 δ1), ‖deriv (fun w => H w - deriv H q * w) y‖ ≤ ε' := by
      intro y hy
      have hd : deriv (fun w => H w - deriv H q * w) y = deriv H y - deriv H q := by
        have h1 := (hH.differentiableAt (hU.mem_nhds (hthick (hball hy)))).hasDerivAt
        have h3 : HasDerivAt (fun w => H w - deriv H q * w) (deriv H y - deriv H q * 1) y :=
          h1.sub ((hasDerivAt_id' y).const_mul _)
        rw [h3.deriv, mul_one]
      rw [hd, ← dist_eq_norm]
      exact (hu _ (hball hy) _ (self_subset_cthickening C hq)
        (lt_of_lt_of_le (mem_ball.mp hy) (min_le_right _ _))).le
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_ball q _)
      (mem_ball_self (lt_min hδ0 hδ1)) (mem_ball.mpr (by rwa [dist_eq_norm]))
    have he : (H x - deriv H q * x) - (H q - deriv H q * q) = H x - H q - deriv H q * (x - q) := by ring
    rwa [he] at h
  have hA : m ≤ ‖deriv H q‖ := hm q hq
  have hup : ‖H s - H q‖ ≤ (‖deriv H q‖ + ε') * ‖s - q‖ := by
    have h1 := hlin s hsq
    calc ‖H s - H q‖ ≤ ‖deriv H q * (s - q)‖ + ‖H s - H q - deriv H q * (s - q)‖ := by
          have := norm_add_le (deriv H q * (s - q)) (H s - H q - deriv H q * (s - q))
          rwa [add_sub_cancel] at this
      _ ≤ ‖deriv H q‖ * ‖s - q‖ + ε' * ‖s - q‖ := by rw [norm_mul]; gcongr
      _ = (‖deriv H q‖ + ε') * ‖s - q‖ := by ring
  have hlo : (‖deriv H q‖ - ε') * ‖p - q‖ ≤ ‖H p - H q‖ := by
    have h1 := hlin p hpq
    have h2 := norm_sub_norm_le (deriv H q * (p - q)) (deriv H q * (p - q) - (H p - H q))
    have he : deriv H q * (p - q) - (deriv H q * (p - q) - (H p - H q)) = H p - H q := by ring
    rw [he, norm_mul] at h2
    have h3 : ‖deriv H q * (p - q) - (H p - H q)‖ = ‖H p - H q - deriv H q * (p - q)‖ := norm_sub_rev _ _
    rw [h3] at h2
    nlinarith
  have hkey : ‖deriv H q‖ + ε' ≤ (1 + ε) * (‖deriv H q‖ - ε') := by
    have : (2 + ε) * ε' = ε * m := by rw [hε']; field_simp
    nlinarith
  have hpq0 := norm_nonneg (p - q)
  have hsq0 := norm_nonneg (s - q)
  calc ‖H s - H q‖ * ‖p - q‖ ≤ (‖deriv H q‖ + ε') * ‖s - q‖ * ‖p - q‖ := by gcongr
    _ ≤ (1 + ε) * (‖deriv H q‖ - ε') * ‖s - q‖ * ‖p - q‖ := by gcongr
    _ = (1 + ε) * ((‖deriv H q‖ - ε') * ‖p - q‖) * ‖s - q‖ := by ring
    _ ≤ (1 + ε) * ‖H p - H q‖ * ‖s - q‖ := by gcongr

/-- Chord ratios close to `1` at small scales make a sense-preserving circle homeomorphism symmetric. -/
theorem c18_symmetric_of_chord {h : ℂ → ℂ} (hsp : Pommerenke1992.IsSensePreservingCircleHomeo h)
    (hc : ∀ ε > 0, ∃ δ > 0, ∀ x t : ℝ, 0 < t → t < δ →
      ‖h (exp ((x + t) * I)) - h (exp (x * I))‖ ≤ (1 + ε) * ‖h (exp (x * I)) - h (exp ((x - t) * I))‖ ∧
      ‖h (exp (x * I)) - h (exp ((x - t) * I))‖ ≤ (1 + ε) * ‖h (exp ((x + t) * I)) - h (exp (x * I))‖) :
    IsSymmetricHomeo h := by
  obtain ⟨u, hu, hmono, hper, hh⟩ := hsp
  refine ⟨u, hu, hmono, hper, hh, ?_⟩
  -- integer periods
  have hperZ : ∀ k : ℤ, ∀ y : ℝ, u (y + 2 * π * k) = u y + 2 * π * k := by
    intro k
    induction k using Int.induction_on with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      have h1 := hper (y + 2 * π * (n : ℝ))
      have h2 := ih y
      push_cast at h2 ⊢
      rw [show y + 2 * π * ((n : ℝ) + 1) = y + 2 * π * (n : ℝ) + 2 * π by ring, h1, h2]
      ring
    | pred n ih =>
      intro y
      have h1 := hper (y + 2 * π * (-(n : ℝ) - 1))
      have h2 := ih y
      push_cast at h2 ⊢
      rw [show y + 2 * π * (-(n : ℝ) - 1) + 2 * π = y + 2 * π * (-(n : ℝ)) by ring, h2] at h1
      linarith
  -- uniformly small increments
  have hsmall : ∀ σ > 0, ∃ τ > 0, ∀ x t : ℝ, 0 ≤ t → t < τ → u (x + t) - u x < σ ∧ u x - u (x - t) < σ := by
    intro σ hσ
    obtain ⟨τ0, hτ0, hτ⟩ := Metric.uniformContinuousOn_iff.mp
      ((isCompact_Icc (a := -2 * π) (b := 4 * π)).uniformContinuousOn_of_continuous hu.continuousOn) σ hσ
    refine ⟨min τ0 (2 * π), lt_min hτ0 (by positivity), fun x t ht0 ht => ?_⟩
    have ht1 : t < τ0 := lt_of_lt_of_le ht (min_le_left _ _)
    have ht2 : t < 2 * π := lt_of_lt_of_le ht (min_le_right _ _)
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊x / (2 * π)⌋ := ⟨_, rfl⟩
    have hpi : 0 < 2 * π := by positivity
    set x0 := x - 2 * π * k with hx0
    have hk1 : (k : ℝ) ≤ x / (2 * π) := by rw [hk]; exact Int.floor_le _
    have hk2 : x / (2 * π) < k + 1 := by rw [hk]; exact Int.lt_floor_add_one _
    have hx00 : 0 ≤ x0 := by
      rw [hx0]
      have := (le_div_iff₀ hpi).mp hk1
      linarith
    have hx01 : x0 < 2 * π := by
      rw [hx0]
      have := (div_lt_iff₀ hpi).mp hk2
      linarith
    have hshift : ∀ y : ℝ, u (y + 2 * π * k) - u (x0 + 2 * π * k) = u y - u x0 := by
      intro y
      rw [hperZ, hperZ]
      ring
    have hxe : x = x0 + 2 * π * k := by rw [hx0]; ring
    have m1 : x0 ∈ Icc (-2 * π) (4 * π) := ⟨by linarith, by linarith⟩
    have m2 : x0 + t ∈ Icc (-2 * π) (4 * π) := ⟨by linarith, by linarith⟩
    have m3 : x0 - t ∈ Icc (-2 * π) (4 * π) := ⟨by linarith, by linarith⟩
    have d1 := hτ _ m2 _ m1 (by rw [Real.dist_eq]; rw [abs_of_nonneg (by linarith)]; linarith)
    have d2 := hτ _ m1 _ m3 (by rw [Real.dist_eq]; rw [abs_of_nonneg (by linarith)]; linarith)
    rw [Real.dist_eq] at d1 d2
    have e1 : u (x + t) - u x = u (x0 + t) - u x0 := by
      rw [hxe, show x0 + 2 * π * k + t = (x0 + t) + 2 * π * k by ring, hshift]
    have e2 : u x - u (x - t) = u x0 - u (x0 - t) := by
      rw [hxe, show x0 + 2 * π * k - t = (x0 - t) + 2 * π * k by ring]
      have := hshift (x0 - t)
      linarith
    rw [e1, e2]
    exact ⟨lt_of_le_of_lt (le_abs_self _) d1, lt_of_le_of_lt (le_abs_self _) d2⟩
  -- chords in terms of increments
  have hchord : ∀ a b : ℝ, 0 < b - a → b - a ≤ 1 →
      (b - a) * (1 - (b - a) ^ 2 / 24) ≤ ‖exp (b * I) - exp (a * I)‖ ∧
        ‖exp (b * I) - exp (a * I)‖ ≤ b - a := by
    intro a b hd hd1
    have he : exp (b * I) - exp (a * I) = exp (a * I) * (exp (I * ((b - a : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, ← Complex.exp_add, mul_one]
      congr 2
      push_cast
      ring
    rw [he, norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_exp_I_mul_ofReal_sub_one, norm_mul,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hs0 : 0 ≤ Real.sin ((b - a) / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith [Real.pi_gt_three])
    rw [Real.norm_of_nonneg hs0]
    have h1 := Real.sin_le (show 0 ≤ (b - a) / 2 by linarith)
    have h2 := Real.sin_ge_sub_cube (show 0 ≤ (b - a) / 2 by linarith)
    constructor <;> nlinarith
  intro ε hε
  obtain ⟨ε0, hε0⟩ : ∃ ε0 : ℝ, ε0 = min ε 1 := ⟨_, rfl⟩
  have hε00 : 0 < ε0 := by rw [hε0]; exact lt_min hε one_pos
  have hε01 : ε0 ≤ 1 := by rw [hε0]; exact min_le_right _ _
  have hε0ε : ε0 ≤ ε := by rw [hε0]; exact min_le_left _ _
  obtain ⟨δc, hδc, hcδ⟩ := hc (ε0 / 4) (by positivity)
  obtain ⟨τ, hτ, hτb⟩ := hsmall ε0 hε00
  refine ⟨min δc τ, lt_min hδc hτ, fun x t ht ht' => ?_⟩
  obtain ⟨c1, c2⟩ := hcδ x t ht (lt_of_lt_of_le ht' (min_le_left _ _))
  obtain ⟨s1, s2⟩ := hτb x t ht.le (lt_of_lt_of_le ht' (min_le_right _ _))
  have p1 : 0 < u (x + t) - u x := sub_pos.mpr (hmono (by linarith))
  have p2 : 0 < u x - u (x - t) := sub_pos.mpr (hmono (by linarith))
  rw [show ((x : ℂ) + t) = ((x + t : ℝ) : ℂ) by push_cast; ring,
    show ((x : ℂ) - t) = ((x - t : ℝ) : ℂ) by push_cast; ring] at c1 c2
  simp only [hh] at c1 c2
  obtain ⟨l1, -⟩ := hchord (u x) (u (x + t)) p1 (by linarith)
  obtain ⟨-, r1⟩ := hchord (u x) (u (x + t)) p1 (by linarith)
  obtain ⟨l2, -⟩ := hchord (u (x - t)) (u x) p2 (by linarith)
  obtain ⟨-, r2⟩ := hchord (u (x - t)) (u x) p2 (by linarith)
  set d1 := u (x + t) - u x
  set d2 := u x - u (x - t)
  have hk1 : 1 - ε0 / 4 ≤ 1 - d1 ^ 2 / 24 := by nlinarith
  have hk2 : 1 - ε0 / 4 ≤ 1 - d2 ^ 2 / 24 := by nlinarith
  have hA : (1 - ε0 / 4) * d1 ≤ (1 + ε0 / 4) * d2 := by nlinarith
  have hB : (1 - ε0 / 4) * d2 ≤ (1 + ε0 / 4) * d1 := by nlinarith
  rw [abs_sub_lt_iff]
  constructor
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ p2]
    nlinarith
  · rw [sub_lt_comm, lt_div_iff₀ p2]
    nlinarith

/-- **Corollary 1.8** (TT:3652), byte-identical copy of `cor_1_8`. -/
theorem c18_cor_1_8 : T01 ⊆ symmetricT := by
  intro p hp
  -- `β(p) ∈ β(T₀(1)) ⊆ β([0]) + A₂(𝔻) = A₂(𝔻)` (the proved inclusion of `componentT_spec`, conjunct 1)
  have hmem := ctd_componentT_spec_one_subset (Phi ⟨0, mem_ball_self one_pos⟩)
    (show bers p ∈ bers '' componentT (Phi ⟨0, mem_ball_self one_pos⟩) from ⟨p, hp, rfl⟩)
  obtain ⟨⟨ψ, hψ⟩, -⟩ := hmem
  rw [c32_bers_origin, zero_add] at hψ
  have hp : bers p ∈ range A2toAInf := ⟨ψ, hψ.symm⟩
  rw [A2toAInf_range] at hp
  obtain ⟨μ, hμd⟩ : ∃ μ : LinfStar, μ = ((Quotient.out p : LinfStarBall) : LinfStar) := ⟨_, rfl⟩
  have hμ : μ ∈ LinfStarBall := by rw [hμd]; exact (Quotient.out p).2
  show IsSymmetricHomeo (wA ((Quotient.out p : LinfStarBall) : LinfStar))
  rw [← hμd]
  have hp' : AInf.toFun (bersPhi μ) ∈ A2fun unitDisc := by rw [hμd]; exact hp
  -- condition (ii) for `f^μ`
  have hS : Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (fB μ) z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
    apply (c18_A2_decay hp').congr'
    have hin : ∀ᶠ z in comap (fun z : ℂ => ‖z‖) (𝓝[<] 1), ‖z‖ < 1 :=
      tendsto_comap.eventually self_mem_nhdsWithin
    filter_upwards [hin] with z hz
    rw [(bersPhi_spec hμ).1 z (mem_ball_zero_iff.mpr hz)]
  -- the two-sided asymptotically conformal extension of `w_μ|S¹`
  obtain ⟨r, hr, Ψ, hq, hc, hi, hb, hout, hμΨ⟩ := c18_outer hμ hS
  have hh : ∀ z : ℂ, ‖z‖ = 1 → ‖wA μ z‖ = 1 := by
    intro z hz
    obtain ⟨u, hu, he⟩ := wAS_maps_circle hμ hz
    have ha : wA μ z = u := congrArg finPart he
    rwa [ha]
  obtain ⟨r', hr', Φ, hqΦ, hbΦ, hμΦ⟩ := c18_two_sided hr hh hq hc hi hb hout hμΨ
  apply c18_symmetric_of_chord (wA_circle_sensePreserving hμ)
  intro ε hε
  obtain ⟨ε0, hε0⟩ : ∃ ε0 : ℝ, ε0 = min ε 1 := ⟨_, rfl⟩
  have hε00 : 0 < ε0 := by rw [hε0]; exact lt_min hε one_pos
  have hε01 : ε0 ≤ 1 := by rw [hε0]; exact min_le_right _ _
  have hε0ε : ε0 ≤ ε := by rw [hε0]; exact min_le_left _ _
  -- `K` with `λ(K) ≤ 1 + ε0/3`, the splitting, and the conformal ratio bound
  obtain ⟨K, hK1, hKlam⟩ := c18_lambdaInv_near_one (η := ε0 / 3) (by positivity)
  have hlam : lambdaInv K ≤ 1 + ε0 / 3 := hKlam K hK1.le le_rfl
  obtain ⟨W, H, U, hWK, hWs, hUo, hWU, hHd, hHi, hfac⟩ := c18_split hr' hqΦ hμΦ hK1
  have hWc : Continuous W := continuousOn_univ.mp hWK.2.2.1.1
  have hWi : InjOn W univ := hWK.2.2.1.2.1
  have hCc : IsCompact (W '' sphere (0 : ℂ) 1) := (isCompact_sphere 0 1).image hWc
  obtain ⟨δH, hδH, hHr⟩ := c18_ratio_H hUo hCc hWU hHd hHi (ε := ε0 / 3) (by positivity)
  obtain ⟨δW, hδW, hWuc⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hWc.continuousOn) δH hδH
  have hboth : ∀ z : ℂ, ‖z‖ = 1 → wA μ z = H (W z) := fun z hz => by rw [← hbΦ z hz, hfac z hz]
  -- the ratio estimate for a symmetric pair of points about `b`
  have key : ∀ b p s : ℂ, ‖b‖ = 1 → ‖p‖ = 1 → ‖s‖ = 1 → ‖p - b‖ = ‖s - b‖ → p ≠ b →
      ‖p - b‖ < δW → ‖s - b‖ < δW → ‖wA μ s - wA μ b‖ ≤ (1 + ε) * ‖wA μ p - wA μ b‖ := by
    intro b p s hb1 hp1 hs1 heq hpb hpδ hsδ
    have hsb : s ≠ b := fun h => hpb (norm_sub_eq_zero_iff.mp (by rw [heq, h, sub_self, norm_zero]))
    have hmemC : ∀ z : ℂ, ‖z‖ = 1 → W z ∈ W '' sphere (0 : ℂ) 1 := fun z hz =>
      ⟨z, mem_sphere_zero_iff_norm.mpr hz, rfl⟩
    have hball : ∀ z : ℂ, ‖z‖ = 1 → z ∈ closedBall (0 : ℂ) 1 := fun z hz =>
      mem_closedBall_zero_iff.mpr hz.le
    have hWp : ‖W p - W b‖ < δH := by
      have h := hWuc p (hball p hp1) b (hball b hb1) (by rwa [dist_eq_norm])
      rwa [dist_eq_norm] at h
    have hWs' : ‖W s - W b‖ < δH := by
      have h := hWuc s (hball s hs1) b (hball b hb1) (by rwa [dist_eq_norm])
      rwa [dist_eq_norm] at h
    have hr1 := hHr (W p) (hmemC p hp1) (W b) (hmemC b hb1) (W s) (hmemC s hs1) hWp hWs'
    have hr2 := c18_ratio_W hWK hWs heq hpb
    have hwp : 0 < ‖W p - W b‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hpb (hWi (mem_univ _) (mem_univ _) h)))
    rw [hboth s hs1, hboth b hb1, hboth p hp1]
    have hA := norm_nonneg (H (W p) - H (W b))
    have k1 : ‖H (W s) - H (W b)‖ * ‖W p - W b‖ ≤
        ((1 + ε0 / 3) * lambdaInv K * ‖H (W p) - H (W b)‖) * ‖W p - W b‖ := by
      calc ‖H (W s) - H (W b)‖ * ‖W p - W b‖
          ≤ (1 + ε0 / 3) * ‖H (W p) - H (W b)‖ * ‖W s - W b‖ := hr1
        _ ≤ (1 + ε0 / 3) * ‖H (W p) - H (W b)‖ * (lambdaInv K * ‖W p - W b‖) :=
            mul_le_mul_of_nonneg_left hr2 (by positivity)
        _ = ((1 + ε0 / 3) * lambdaInv K * ‖H (W p) - H (W b)‖) * ‖W p - W b‖ := by ring
    have k2 := le_of_mul_le_mul_right k1 hwp
    have k3 : (1 + ε0 / 3) * lambdaInv K ≤ 1 + ε := by
      have h1 : (1 + ε0 / 3) * lambdaInv K ≤ (1 + ε0 / 3) * (1 + ε0 / 3) :=
        mul_le_mul_of_nonneg_left hlam (by positivity)
      nlinarith
    calc ‖H (W s) - H (W b)‖ ≤ (1 + ε0 / 3) * lambdaInv K * ‖H (W p) - H (W b)‖ := k2
      _ ≤ (1 + ε) * ‖H (W p) - H (W b)‖ := mul_le_mul_of_nonneg_right k3 hA
  -- chords of `S¹`
  have hnorm1 : ∀ y : ℝ, ‖exp ((y : ℂ) * I)‖ = 1 := fun y => norm_exp_ofReal_mul_I y
  have hdiff : ∀ y s : ℝ, exp (((y : ℂ) + (s : ℂ)) * I) - exp ((y : ℂ) * I) =
      exp ((y : ℂ) * I) * (exp (I * (s : ℂ)) - 1) := by
    intro y s
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    ring
  have hchn : ∀ y s : ℝ, ‖exp (((y : ℂ) + (s : ℂ)) * I) - exp ((y : ℂ) * I)‖ = ‖exp (I * (s : ℂ)) - 1‖ := by
    intro y s
    rw [hdiff, norm_mul, hnorm1, one_mul]
  have hpt : ∀ y s : ℝ, ‖exp (((y : ℂ) + (s : ℂ)) * I)‖ = 1 := by
    intro y s
    rw [show ((y : ℂ) + (s : ℂ)) = ((y + s : ℝ) : ℂ) by push_cast; ring]
    exact hnorm1 _
  refine ⟨min δW π, lt_min hδW Real.pi_pos, fun x t ht htδ => ?_⟩
  have htW : t < δW := lt_of_lt_of_le htδ (min_le_left _ _)
  have htπ : t < π := lt_of_lt_of_le htδ (min_le_right _ _)
  have hm : ((x : ℂ) - (t : ℂ)) = (x : ℂ) + ((-t : ℝ) : ℂ) := by push_cast; ring
  rw [hm]
  have hsym : ‖exp (I * (t : ℂ)) - 1‖ = ‖exp (I * ((-t : ℝ) : ℂ)) - 1‖ := by
    rw [norm_exp_I_mul_ofReal_sub_one, norm_exp_I_mul_ofReal_sub_one, neg_div, Real.sin_neg, mul_neg,
      norm_neg]
  have hpos : 0 < ‖exp (I * (t : ℂ)) - 1‖ := by
    rw [norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      Real.norm_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
    exact mul_pos two_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hlt : ∀ s : ℝ, |s| = t → ‖exp (I * (s : ℂ)) - 1‖ < δW := by
    intro s hs
    refine lt_of_le_of_lt Real.norm_exp_I_mul_ofReal_sub_one_le ?_
    rw [Real.norm_eq_abs, hs]
    exact htW
  have hlt1 := hlt t (abs_of_pos ht)
  have hlt2 := hlt (-t) (by rw [abs_neg, abs_of_pos ht])
  have hne : ∀ s : ℝ, 0 < ‖exp (I * (s : ℂ)) - 1‖ →
      exp (((x : ℂ) + (s : ℂ)) * I) ≠ exp ((x : ℂ) * I) := by
    intro s hs h
    rw [← hchn x s, h, sub_self, norm_zero] at hs
    exact lt_irrefl _ hs
  constructor
  · rw [norm_sub_rev (wA μ (exp ((x : ℂ) * I)))]
    exact key _ _ _ (hnorm1 x) (hpt x (-t)) (hpt x t) (by rw [hchn, hchn, hsym])
      (hne (-t) (hsym ▸ hpos)) (by rw [hchn]; exact hlt2) (by rw [hchn]; exact hlt1)
  · rw [norm_sub_rev (wA μ (exp ((x : ℂ) * I)))]
    exact key _ _ _ (hnorm1 x) (hpt x t) (hpt x (-t)) (by rw [hchn, hchn, hsym])
      (hne t hpos) (by rw [hchn]; exact hlt1) (by rw [hchn]; exact hlt2)

/-- **Corollary 1.8** (TT:3652). `T₀(1)` is a subgroup of `S`. -/
theorem cor_1_8 : T01 ⊆ symmetricT :=
  c18_cor_1_8

end Ch2

end TakhtajanTeo
