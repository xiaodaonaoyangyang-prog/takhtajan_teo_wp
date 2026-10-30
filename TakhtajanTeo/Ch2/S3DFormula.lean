import TakhtajanTeo.Ch2.S3DBase
import TakhtajanTeo.Ch2.S3DD0
import TakhtajanTeo.Ch2.S3DD1
import TakhtajanTeo.Ch2.S3DD2
import TakhtajanTeo.Ch2.S3DD3
import TakhtajanTeo.Ch2.S3Remark310
import TakhtajanTeo.Ch2.S3S1Tilde
import TakhtajanTeo.Ch2.S3Lemma36

/-! # Density route: the formula `s3d_formula` (Program G)

F-H, F-POLE, F-I2, F-I4, F-FUB (FB-D, FB-C, FB-E/DD, H-vanishing, FB-E, glue) and the assembly. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- [F-H helper] `s36l_sp_I1` for an arbitrary derivative `φ = P'`. Green on `𝔻` for the `K₁`-term: `∬_𝔻 K₁ \overline{𝒜(f)} = (1/2i) ∮_{S¹} K₁ \overline{P}`. -/
theorem s3fh_I1g {f P φ : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R))
    (hP : ∀ w ∈ ball (0 : ℂ) R, HasDerivAt P (φ w) w) {z : ℂ} (hz : z ∈ unitDisc) :
    (∫ w in unitDisc, kerK1 f z w * conj (φ w)) =
      1 / (2 * I) * ∮ w in C(0, 1), kerK1 f z w * conj (P w) := by
  have hzR : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hz) hR)
  obtain ⟨K, hK, hKe⟩ := s36l_sp_K1_holo hf hfi hzR
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 R := fun w hw =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hR)
  have hPd : DifferentiableOn ℂ P (ball 0 R) := fun w hw => (hP w hw).differentiableAt.differentiableWithinAt
  have hKr : ContDiffOn ℝ 1 K (ball 0 R) := (hK.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hPr : ContDiffOn ℝ 1 P (ball 0 R) := (hPd.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hcP : ContDiffOn ℝ 1 (fun w => conj (P w)) (ball 0 R) :=
    Complex.conjCLE.contDiff.comp_contDiffOn hPr
  have hF : ContDiffOn ℝ 1 (fun w => K w * conj (P w)) (closedBall 0 1) := (hKr.mul hcP).mono hcb
  have hG := eq11_9_green_dz zero_lt_one hF
  have hsph : EqOn (fun w => K w * conj (P w)) (fun w => kerK1 f z w * conj (P w)) (sphere 0 1) := by
    intro w hw
    have hw1 : ‖w‖ = 1 := by simpa using hw
    have hwz : w ≠ z := fun h => by
      rw [h] at hw1; have := mem_ball_zero_iff.mp hz; linarith
    simp only [hKe w (hcb (sphere_subset_closedBall hw)) hwz]
  rw [circleIntegral.integral_congr zero_le_one hsph] at hG
  rw [hG]
  have hI : (2 * I : ℂ) ≠ 0 := by simp [I_ne_zero]
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hI, one_mul]
  refine setIntegral_congr_ae measurableSet_ball ?_
  filter_upwards [(volume : Measure ℂ).ae_ne z] with w hwz hw
  have hwB : w ∈ ball (0 : ℂ) R := hcb (ball_subset_closedBall hw)
  have hKw : DifferentiableAt ℂ K w := (hK w hwB).differentiableAt (isOpen_ball.mem_nhds hwB)
  have hPw : DifferentiableAt ℂ P w := (hP w hwB).differentiableAt
  have hcPw : DifferentiableAt ℝ (fun w => conj (P w)) w :=
    Complex.conjCLE.differentiableAt.comp w (hPw.restrictScalars ℝ)
  rw [dzbar_mul (hKw.restrictScalars ℝ) hcPw, dzbar_conj (hPw.restrictScalars ℝ), dz_eq_deriv hPw,
    (cauchyRiemann_iff.1 hKw).2, (hP w hwB).deriv, hKe w hwB hwz, mul_zero, add_zero]

/-- [F-H helper] `s36l_sp_I2` for an arbitrary derivative `φ = P'`. Green on `𝔻*` for the `K₂`-term (with the outer circle pushed to `∞`). -/
theorem s3fh_I2g {f g P φ : ℂ → ℂ} {R r' : ℝ} (hR : 1 < R) (hr0 : 0 < r') (hr' : r' < 1)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g {w | r' < ‖w‖})
    (hgi : InjOn g {w | r' < ‖w‖}) (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hg0 : ∀ w : ℂ, r' < ‖w‖ → g w ≠ 0) {z : ℂ} (hz : z ∈ unitDisc)
    (hgz : ∀ w : ℂ, r' < ‖w‖ → g w ≠ f z)
    (hP : ∀ w : ℂ, r' < ‖w‖ → HasDerivAt P (φ w) w) {C : ℝ}
    (hC : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖P w‖ ≤ C) :
    (∫ w in unitDiscExterior, kerK2 f g z w * conj (-φ w)) =
      1 / (2 * I) * ∮ w in C(0, 1), kerK2 f g z w * conj (P w) := by
  obtain ⟨G, hGd, hGi, hG0, hGe⟩ := s36l_sp_inv hr0 hg hgi hginf hg0
  obtain ⟨ρ, hρ1, hρ2, P', hP'd, hP'e⟩ := s36l_sp_remove hr0 hr'
    (fun w hw => (hP w hw).differentiableAt.differentiableWithinAt) hC
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 ρ := fun w hw =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hρ1)
  have hbb : ball (0 : ℂ) ρ ⊆ ball 0 r'⁻¹ := ball_subset_ball hρ2.le
  have hmem : ∀ u : ℂ, u ≠ 0 → ‖u‖ < r'⁻¹ → r' < ‖u⁻¹‖ := by
    intro u hu hus
    rw [norm_inv, lt_inv_comm₀ hr0 (norm_pos_iff.mpr hu)]; exact hus
  have hG1 : ∀ u ∈ ball (0 : ℂ) ρ, f z * G u - 1 ≠ 0 := by
    intro u hu
    have hus : ‖u‖ < r'⁻¹ := mem_ball_zero_iff.mp (hbb hu)
    by_cases hu0 : u = 0
    · rw [hu0, hG0]; simp
    · have ha := hg0 _ (hmem u hu0 hus)
      have hz := hgz _ (hmem u hu0 hus)
      rw [hGe u hu0 hus]
      intro h
      apply hz
      have h' : f z * (g u⁻¹)⁻¹ = 1 := by linear_combination h
      rw [mul_inv_eq_one₀ ha] at h'
      exact h'.symm
  have hG' : DifferentiableOn ℂ (deriv G) (ball 0 r'⁻¹) := (hGd.analyticOnNhd isOpen_ball).deriv.differentiableOn
  set H : ℂ → ℂ := fun u => 1 / π * (deriv f z * deriv G u / (f z * G u - 1) ^ 2) with hH_def
  have hH : DifferentiableOn ℂ H (ball 0 ρ) :=
    (differentiableOn_const _).mul (((differentiableOn_const _).mul (hG'.mono hbb)).div
      ((((differentiableOn_const _).mul (hGd.mono hbb)).sub (differentiableOn_const _)).pow 2)
        fun u hu => pow_ne_zero 2 (hG1 u hu))
  have hHe : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ρ → H u = kerK2 f g z u⁻¹ * (u⁻¹) ^ 2 := by
    intro u hu0 huρ
    have hus : ‖u‖ < r'⁻¹ := lt_trans huρ hρ2
    have hd := s36l_sp_inv_deriv hr0 hg hg0 hGe hu0 hus
    have ha := hg0 _ (hmem u hu0 hus)
    have hz := hgz _ (hmem u hu0 hus)
    have e1 : kerK2 f g z u⁻¹ * (u⁻¹) ^ 2 =
        1 / π * (deriv f z * (deriv g u⁻¹ * (u⁻¹) ^ 2) / (f z - g u⁻¹) ^ 2) := by
      unfold kerK2; ring
    rw [e1, hd, hH_def]
    simp only
    rw [hGe u hu0 hus]
    have hzs : f z - g u⁻¹ ≠ 0 := sub_ne_zero.mpr hz.symm
    generalize g u⁻¹ = a at ha hzs ⊢
    generalize deriv G u = d
    have h3 : f z * a⁻¹ - 1 ≠ 0 := by
      rw [show f z * a⁻¹ - 1 = (f z - a) / a by field_simp]
      exact div_ne_zero hzs ha
    field_simp
  -- derivative of `P' = P ∘ inv`
  have hP'deriv : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ρ → deriv P' u = φ u⁻¹ * -(u ^ 2)⁻¹ := by
    intro u hu0 huρ
    have hw := hmem u hu0 (lt_trans huρ hρ2)
    have hc : HasDerivAt (fun u => P u⁻¹) (φ u⁻¹ * -(u ^ 2)⁻¹) u := by
      have := (hP _ hw).comp u (hasDerivAt_inv hu0)
      simpa [Function.comp_def] using this
    have hB : IsOpen (ball (0 : ℂ) ρ \ {0}) := isOpen_ball.sdiff isClosed_singleton
    have hev : P' =ᶠ[𝓝 u] fun u => P u⁻¹ := by
      filter_upwards [hB.mem_nhds ⟨mem_ball_zero_iff.mpr huρ, hu0⟩] with v hv
      exact hP'e v hv.2 (mem_ball_zero_iff.mp hv.1)
    rw [hev.deriv_eq, hc.deriv]
  -- Green on the unit disc for `H · conj P'`
  have hHr : ContDiffOn ℝ 1 H (ball 0 ρ) := (hH.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hPr : ContDiffOn ℝ 1 P' (ball 0 ρ) := (hP'd.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hcP : ContDiffOn ℝ 1 (fun u => conj (P' u)) (ball 0 ρ) := Complex.conjCLE.contDiff.comp_contDiffOn hPr
  have hF : ContDiffOn ℝ 1 (fun u => H u * conj (P' u)) (closedBall 0 1) := (hHr.mul hcP).mono hcb
  have hGr := eq11_9_green_dz zero_lt_one hF
  -- the circle integral is the original one, by inversion
  have hcirc : (∮ u in C(0, 1), H u * conj (P' u)) = ∮ w in C(0, 1), kerK2 f g z w * conj (P w) := by
    rw [s36l_sp_circ_inv (fun w => kerK2 f g z w * conj (P w))]
    refine circleIntegral.integral_congr zero_le_one fun u hu => ?_
    have hu1 : ‖u‖ = 1 := by simpa using hu
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; norm_num at hu1
    rw [hHe u hu0 (by rw [hu1]; exact hρ1), hP'e u hu0 (by rw [hu1]; exact hρ1)]
    ring
  rw [hcirc] at hGr
  rw [hGr]
  have hI : (2 * I : ℂ) ≠ 0 := by simp [I_ne_zero]
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hI, one_mul]
  -- change of variables `w = 1/u`
  rw [integral_image_conformal_complex (isOpen_ball.sdiff isClosed_singleton) isConformalOnto_inv_puncturedDisc]
  have hnull : (ball (0 : ℂ) 1 \ {0} : Set ℂ) =ᵐ[volume] ball (0 : ℂ) 1 :=
    sdiff_null_ae_eq_self (measure_singleton 0)
  rw [setIntegral_congr_set hnull]
  refine setIntegral_congr_ae measurableSet_ball ?_
  filter_upwards [(volume : Measure ℂ).ae_ne 0] with u hu0 hu
  have huρ : ‖u‖ < ρ := lt_trans (mem_ball_zero_iff.mp hu) hρ1
  have hHu : DifferentiableAt ℂ H u := (hH u (mem_ball_zero_iff.mpr huρ)).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr huρ))
  have hPu : DifferentiableAt ℂ P' u := (hP'd u (mem_ball_zero_iff.mpr huρ)).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr huρ))
  have hcPu : DifferentiableAt ℝ (fun u => conj (P' u)) u :=
    Complex.conjCLE.differentiableAt.comp u (hPu.restrictScalars ℝ)
  rw [dzbar_mul (hHu.restrictScalars ℝ) hcPu, dzbar_conj (hPu.restrictScalars ℝ), dz_eq_deriv hPu,
    (cauchyRiemann_iff.1 hHu).2, mul_zero, add_zero, hP'deriv u hu0 huρ, hHe u hu0 huρ, deriv_inv]
  have hn : ((‖-(u ^ 2)⁻¹‖ ^ 2 : ℝ) : ℂ) = (u⁻¹) ^ 2 * conj (-(u ^ 2)⁻¹) * (-1) := by
    rw [norm_neg, norm_inv, norm_pow, map_neg, map_inv₀, map_pow]
    have hc : (u⁻¹) ^ 2 * -((conj u ^ 2)⁻¹) * (-1) = ((u * conj u) ^ 2)⁻¹ := by ring
    rw [hc, Complex.mul_conj']
    push_cast
    ring
  push_cast at hn ⊢
  rw [hn]
  simp only [map_mul, map_neg]
  ring

/-- [F-H helper] **Q-version of `s36l_smooth_pair`**: the same identity with `v = (𝒜(f) - 2L_f, -(𝒜(g) - 2L_g))`,
`L = h'/h - 1/w`, and right side `-𝒜(f)(z)` (the roles of the primitives `P` of `𝒜` and `Q` of `𝒜 - 2L` swap; the
jump relation is the complex conjugate of `s36l_sp_jump`). -/
theorem s3fh_smoothQ {f g : ℂ → ℂ} {R r : ℝ} (hR : 1 < R) (hr : r < 1)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R)) (hf0 : f 0 = 0)
    (hg : DifferentiableOn ℂ g {w | r < ‖w‖}) (hgi : InjOn g {w | r < ‖w‖})
    (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hc : g '' unitDiscExterior = (f '' closedBall 0 1)ᶜ)
    {z : ℂ} (hz : z ∈ unitDisc) :
    (∫ w in unitDisc, kerK1 f z w * conj (preSchwarzian f w - 2 * deriv f w / f w + 2 / w)) +
        (∫ w in unitDiscExterior, kerK2 f g z w * conj (-(preSchwarzian g w - 2 * deriv g w / g w + 2 / w))) =
      -preSchwarzian f z := by
  obtain ⟨PD, QD, hPDd, hQDd, hPD, hQD⟩ := s36l_sp_primD hR hf hfi hf0
  obtain ⟨r', hrr', hr0, hr'1, hgne, PE, QE, hPEd, hQEd, hPE, hQE, C, hC⟩ :=
    s36l_sp_primE hR hr hf hfi hf0 hg hgi hginf hc hz
  have hsub : {w : ℂ | r' < ‖w‖} ⊆ {w | r < ‖w‖} := fun w hw => lt_of_le_of_lt hrr' hw
  have hg' := hg.mono hsub
  have hgi' := hgi.mono hsub
  obtain ⟨γ, a, b, ha, hb, hbR, hγ, hγg, hS⟩ := s36l_sp_weld hR hrr' hr'1 hf hfi hg hgi hginf hc
  obtain ⟨k, hk⟩ := s36l_sp_subst ha hb hγ hS
  obtain ⟨c0, hjump0⟩ := s36l_sp_jump hR hr'1 hf hfi hf0 hg' hgi' (fun w hw => (hgne w hw).1) hPD hQD hPE hQE
    ha hb hbR hγ hγg hS
  obtain ⟨c, hjump⟩ : ∃ c : ℂ, ∀ w : ℂ, ‖w‖ = 1 → -conj (QD w) + PD w = -conj (QE (γ w)) + PE (γ w) + c := by
    refine ⟨-conj c0, fun w hw => ?_⟩
    have h := congrArg conj (hjump0 w hw)
    simp only [map_add, map_neg, Complex.conj_conj] at h
    linear_combination -h
  have hzR0 : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hz) hR)
  have hI1 : (∫ w in unitDisc, kerK1 f z w * conj (preSchwarzian f w - 2 * deriv f w / f w + 2 / w)) =
      ∫ w in unitDisc, kerK1 f z w * conj (deriv QD w) := by
    refine setIntegral_congr_ae isOpen_ball.measurableSet ?_
    filter_upwards [(volume : Measure ℂ).ae_ne 0] with w hw0 hw
    have hwR : w ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hw) hR)
    rw [(hQD w hwR hw0).deriv]
  rw [hI1, s3fh_I1g hR hf hfi (fun w hw => (hQDd.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt) hz,
    s3fh_I2g hR hr0 hr'1 hf hg' hgi' hginf (fun w hw => (hgne w hw).1) hz (fun w hw => (hgne w hw).2) hQE
      (fun w hw => (hC w hw).2)]
  -- basic facts
  have hzR : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hz) hR)
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hU : IsOpen {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hE : IsOpen {w : ℂ | r' < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hS1 : ∀ w : ℂ, w ∈ sphere (0 : ℂ) 1 → ‖w‖ = 1 := fun w hw => by simpa using hw
  have hUw : ∀ w : ℂ, ‖w‖ = 1 → w ∈ {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b} := fun w hw => ⟨by rw [hw]; exact ha, by rw [hw]; exact hb⟩
  have hEw : ∀ w : ℂ, ‖w‖ = 1 → r' < ‖w‖ := fun w hw => by rw [hw]; exact hr'1
  have hwz : ∀ w : ℂ, ‖w‖ = 1 → w - z ≠ 0 := fun w hw h => by
    rw [sub_eq_zero] at h; rw [h] at hw; linarith
  have hchain : ∀ w : ℂ, ‖w‖ = 1 → deriv g (γ w) * deriv γ w = deriv f w := by
    intro w hw
    have hwU := hUw w hw
    have hγw : DifferentiableAt ℂ γ w := (hγ w hwU).differentiableAt (hU.mem_nhds hwU)
    have hgw : DifferentiableAt ℂ g (γ w) :=
      (hg' (γ w) (hγg w hwU.1 hwU.2).1).differentiableAt (hE.mem_nhds (hγg w hwU.1 hwU.2).1)
    have heq : (g ∘ γ) =ᶠ[𝓝 w] f := by
      filter_upwards [hU.mem_nhds hwU] with u hu
      exact (hγg u hu.1 hu.2).2
    rw [← heq.deriv_eq, deriv_comp w hgw hγw]
  -- continuity on the sphere
  have hgc : ContinuousOn g {w : ℂ | r' < ‖w‖} := hg'.continuousOn
  have hg'c : ContinuousOn (deriv g) {w : ℂ | r' < ‖w‖} := (hg'.analyticOnNhd hE).deriv.continuousOn
  have hγc : ContinuousOn γ (sphere 0 1) := hγ.continuousOn.mono fun w hw => hUw w (hS1 w hw)
  have hγ'c : ContinuousOn (deriv γ) (sphere 0 1) :=
    (hγ.analyticOnNhd hU).deriv.continuousOn.mono fun w hw => hUw w (hS1 w hw)
  have hγE : MapsTo γ (sphere (0 : ℂ) 1) {w : ℂ | r' < ‖w‖} := fun w hw => by
    show r' < ‖γ w‖; rw [hS w (hS1 w hw)]; exact hr'1
  have hsE : sphere (0 : ℂ) 1 ⊆ {w : ℂ | r' < ‖w‖} := fun w hw => hEw w (hS1 w hw)
  have hsB : sphere (0 : ℂ) 1 ⊆ ball 0 R := fun w hw => mem_ball_zero_iff.mpr (by rw [hS1 w hw]; exact hR)
  have hHc : ContinuousOn (kerK2 f g z) {w : ℂ | r' < ‖w‖} := by
    intro w hw
    unfold kerK2
    refine (continuousWithinAt_const.mul ((continuousWithinAt_const.mul (hg'c w hw)).div
      ((continuousWithinAt_const.sub (hgc w hw)).pow 2) ?_))
    exact pow_ne_zero 2 (sub_ne_zero.mpr (hgne w hw).2.symm)
  obtain ⟨K, hK1, hKe⟩ := s36l_sp_K1_holo hf hfi hzR
  have hKs : EqOn K (kerK1 f z) (sphere 0 1) := fun w hw => hKe w (hsB hw) (fun h => hwz w (hS1 w hw) (by rw [h, sub_self]))
  have hK1c : ContinuousOn (kerK1 f z) (sphere 0 1) := (hK1.continuousOn.mono hsB).congr hKs.symm
  have hQDc : ContinuousOn (fun w => conj (QD w)) (sphere 0 1) :=
    (continuous_conj.comp_continuousOn hQDd.continuousOn).mono hsB
  have hPDc : ContinuousOn PD (sphere 0 1) := hPDd.continuousOn.mono hsB
  have hQEc : ContinuousOn (fun w => conj (QE w)) {w : ℂ | r' < ‖w‖} :=
    continuous_conj.comp_continuousOn hQEd.continuousOn
  have hinvc : ContinuousOn (fun w : ℂ => ((w - z) ^ 2)⁻¹) (sphere 0 1) := fun w hw =>
    (((continuous_id.sub continuous_const).pow 2).continuousAt.inv₀
      (pow_ne_zero 2 (hwz w (hS1 w hw)))).continuousWithinAt
  -- k = 1
  have hk1 : (k : ℂ) = 1 := by
    have hΨ : ContinuousOn (fun ξ => deriv g ξ / (g ξ - f z)) (sphere 0 1) := fun w hw =>
      ((hg'c w (hsE hw)).div (hgc.sub continuousOn_const w (hsE hw))
        (sub_ne_zero.mpr (hgne w (hsE hw)).2)).mono hsE
    have h := hk _ hΨ
    rw [s36l_sp_windE hr0 hr'1 hg' hgi' hginf (fun w hw => (hgne w hw).1) (fun w hw => (hgne w hw).2)] at h
    have hl : (∮ w in C(0, 1), deriv g (γ w) / (g (γ w) - f z) * deriv γ w) =
        ∮ w in C(0, 1), deriv f w / (f w - f z) := by
      refine circleIntegral.integral_congr zero_le_one fun w hw => ?_
      have hw1 := hS1 w hw
      have hwU := hUw w hw1
      rw [(hγg w hwU.1 hwU.2).2, ← hchain w hw1]
      ring
    rw [hl, s36l_sp_windD hR hf hfi hz] at h
    have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    exact (mul_right_cancel₀ hpi (by rw [one_mul]; exact h : (1 : ℂ) * (2 * π * I) = (k : ℂ) * (2 * π * I))).symm
  -- the substituted K₂ boundary terms
  have hA2 : (∮ w in C(0, 1), kerK2 f g z w * conj (QE w)) =
      ∮ w in C(0, 1), kerK2 f g z (γ w) * conj (QE (γ w)) * deriv γ w := by
    have h := hk (fun ξ => kerK2 f g z ξ * conj (QE ξ)) ((hHc.mul hQEc).mono hsE)
    simp only [hk1, one_mul] at h
    exact h.symm
  have hB2 : (∮ w in C(0, 1), kerK2 f g z (γ w) * PE (γ w) * deriv γ w) = 0 := by
    have h := hk (fun ξ => kerK2 f g z ξ * PE ξ) ((hHc.mul hPEd.continuousOn).mono hsE)
    simp only [hk1, one_mul] at h
    rw [h, s36l_sp_ext_zero hr0 hr'1 hg' hgi' hginf (fun w hw => (hgne w hw).1) (fun w hw => (hgne w hw).2) hPEd (fun w hw => (hC w hw).1)]
  -- pointwise identity on S¹
  set m : ℂ → ℂ := fun w => 1 / π * (deriv f z * deriv f w / (f z - f w) ^ 2) with hm
  have hHm : ∀ w : ℂ, ‖w‖ = 1 → kerK2 f g z (γ w) * deriv γ w = m w := by
    intro w hw
    have hwU := hUw w hw
    simp only [kerK2, hm, (hγg w hwU.1 hwU.2).2, ← hchain w hw]
    ring
  have hKm : ∀ w : ℂ, ‖w‖ = 1 → kerK1 f z w + m w = 1 / π * ((w - z) ^ 2)⁻¹ := by
    intro w hw
    have hzw : z ≠ w := fun h => hwz w hw (by rw [h, sub_self])
    rw [kerK1_of_ne f hzw, hm]
    have : (z - w) ^ 2 = (w - z) ^ 2 := by ring
    rw [this]
    ring
  have hpt : EqOn (fun w => kerK1 f z w * conj (QD w) + kerK2 f g z (γ w) * conj (QE (γ w)) * deriv γ w)
      (fun w => 1 / π * (((w - z) ^ 2)⁻¹ * conj (QD w)) - 1 / π * (((w - z) ^ 2)⁻¹ * PD w) +
        kerK1 f z w * PD w + kerK2 f g z (γ w) * PE (γ w) * deriv γ w +
          c * (1 / π * ((w - z) ^ 2)⁻¹ - kerK1 f z w)) (sphere 0 1) := by
    intro w hw
    have hw1 := hS1 w hw
    have h1 := hjump w hw1
    have h2 := hHm w hw1
    have h3 := hKm w hw1
    have hQE' : conj (QE (γ w)) = conj (QD w) - PD w + PE (γ w) + c := by linear_combination h1
    have e1 : kerK2 f g z (γ w) * conj (QE (γ w)) * deriv γ w = m w * conj (QE (γ w)) := by
      rw [← h2]; ring
    have e2 : kerK2 f g z (γ w) * PE (γ w) * deriv γ w = m w * PE (γ w) := by rw [← h2]; ring
    have e3 : m w = 1 / π * ((w - z) ^ 2)⁻¹ - kerK1 f z w := by linear_combination h3
    simp only
    rw [e1, e2, hQE', e3]
    ring
  -- integrate
  have ci : ∀ {F : ℂ → ℂ}, ContinuousOn F (sphere 0 1) → CircleIntegrable F 0 1 :=
    fun h => h.circleIntegrable zero_le_one
  have hT1 : ContinuousOn (fun w => 1 / π * (((w - z) ^ 2)⁻¹ * conj (QD w))) (sphere 0 1) :=
    continuousOn_const.mul (hinvc.mul hQDc)
  have hT2 : ContinuousOn (fun w => 1 / π * (((w - z) ^ 2)⁻¹ * PD w)) (sphere 0 1) :=
    continuousOn_const.mul (hinvc.mul hPDc)
  have hT3 : ContinuousOn (fun w => kerK1 f z w * PD w) (sphere 0 1) := hK1c.mul hPDc
  have hT4 : ContinuousOn (fun w => kerK2 f g z (γ w) * PE (γ w) * deriv γ w) (sphere 0 1) :=
    ((hHc.comp hγc hγE).mul (hPEd.continuousOn.comp hγc hγE)).mul hγ'c
  have hT5 : ContinuousOn (fun w => c * (1 / π * ((w - z) ^ 2)⁻¹ - kerK1 f z w)) (sphere 0 1) :=
    continuousOn_const.mul ((continuousOn_const.mul hinvc).sub hK1c)
  have hL1 : ContinuousOn (fun w => kerK1 f z w * conj (QD w)) (sphere 0 1) := hK1c.mul hQDc
  have hL2 : ContinuousOn (fun w => kerK2 f g z (γ w) * conj (QE (γ w)) * deriv γ w) (sphere 0 1) :=
    ((hHc.comp hγc hγE).mul (hQEc.comp hγc hγE)).mul hγ'c
  have hsum := circleIntegral.integral_congr zero_le_one hpt
  have e0 := circleIntegral.integral_add (c := 0) (R := 1)
    (f := fun w => kerK1 f z w * conj (QD w)) (g := fun w => kerK2 f g z (γ w) * conj (QE (γ w)) * deriv γ w)
    (ci hL1) (ci hL2)
  have e5 := circleIntegral.integral_add (c := 0) (R := 1)
    (f := fun w => 1 / π * (((w - z) ^ 2)⁻¹ * conj (QD w)) - 1 / π * (((w - z) ^ 2)⁻¹ * PD w) + kerK1 f z w * PD w + kerK2 f g z (γ w) * PE (γ w) * deriv γ w) (g := fun w => c * (1 / π * ((w - z) ^ 2)⁻¹ - kerK1 f z w))
    (ci (((hT1.sub hT2).add hT3).add hT4)) (ci hT5)
  have e4 := circleIntegral.integral_add (c := 0) (R := 1)
    (f := fun w => 1 / π * (((w - z) ^ 2)⁻¹ * conj (QD w)) - 1 / π * (((w - z) ^ 2)⁻¹ * PD w) + kerK1 f z w * PD w) (g := fun w => kerK2 f g z (γ w) * PE (γ w) * deriv γ w) (ci ((hT1.sub hT2).add hT3)) (ci hT4)
  have e3 := circleIntegral.integral_add (c := 0) (R := 1)
    (f := fun w => 1 / π * (((w - z) ^ 2)⁻¹ * conj (QD w)) - 1 / π * (((w - z) ^ 2)⁻¹ * PD w)) (g := fun w => kerK1 f z w * PD w) (ci (hT1.sub hT2)) (ci hT3)
  have e2 := circleIntegral.integral_sub (c := 0) (R := 1)
    (f := fun w => 1 / π * (((w - z) ^ 2)⁻¹ * conj (QD w))) (g := fun w => 1 / π * (((w - z) ^ 2)⁻¹ * PD w)) (ci hT1) (ci hT2)
  beta_reduce at e0 e5 e4 e3 e2
  rw [e0, e5, e4, e3, e2] at hsum
  -- the five boundary integrals
  have hz2 : (∮ w in C(0, 1), ((w - z) ^ 2)⁻¹) = 0 := by
    simpa using! circleIntegral.integral_sub_zpow_of_ne (by decide : (-2 : ℤ) ≠ -1) 0 z 1
  have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 R := fun w hw =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hR)
  have hcauchy : ∀ {F : ℂ → ℂ}, DifferentiableOn ℂ F (ball 0 R) → (∮ w in C(0, 1), F w) = 0 := by
    intro F hF
    exact circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one countable_empty
      (hF.continuousOn.mono hcb) fun w hw => (hF w (hcb (ball_subset_closedBall hw.1))).differentiableAt
        (isOpen_ball.mem_nhds (hcb (ball_subset_closedBall hw.1)))
  have i1 : (∮ w in C(0, 1), 1 / π * (((w - z) ^ 2)⁻¹ * conj (QD w))) = 0 := by
    rw [circleIntegral.integral_const_mul]
    have := s36l_sp_conj_zero hR hQDd hz
    simp only [div_eq_mul_inv] at this
    rw [show (∮ w in C(0, 1), ((w - z) ^ 2)⁻¹ * conj (QD w)) = ∮ w in C(0, 1), conj (QD w) * ((w - z) ^ 2)⁻¹ by
      simp only [mul_comm], this, mul_zero]
  have i2 : (∮ w in C(0, 1), 1 / π * (((w - z) ^ 2)⁻¹ * PD w)) = 1 / π * (2 * π * I * deriv PD z) := by
    rw [circleIntegral.integral_const_mul]
    have h := two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable isOpen_ball hcb hPDd
      (mem_ball_zero_iff.mpr hz1 : z ∈ ball (0 : ℂ) 1)
    simp only [smul_eq_mul] at h
    have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    rw [← h, mul_inv_cancel_left₀ hpi]
  have i3 : (∮ w in C(0, 1), kerK1 f z w * PD w) = 0 := by
    have e : (∮ w in C(0, 1), kerK1 f z w * PD w) = ∮ w in C(0, 1), K w * PD w :=
      circleIntegral.integral_congr zero_le_one fun w hw => by simp only [hKs hw]
    rw [e]
    exact hcauchy (hK1.mul hPDd)
  have i5 : (∮ w in C(0, 1), c * (1 / π * ((w - z) ^ 2)⁻¹ - kerK1 f z w)) = 0 := by
    have e := circleIntegral.integral_sub (c := 0) (R := 1) (f := fun w => 1 / π * ((w - z) ^ 2)⁻¹)
      (g := fun w => kerK1 f z w) (ci (continuousOn_const.mul hinvc)) (ci hK1c)
    beta_reduce at e
    rw [circleIntegral.integral_const_mul, e, circleIntegral.integral_const_mul, hz2,
      (circleIntegral.integral_congr zero_le_one hKs).symm.trans (hcauchy hK1)]
    ring
  rw [i1, i2, i3, hB2, i5, ← hA2] at hsum
  have hdQ : deriv PD z = preSchwarzian f z := (hPD z hzR).deriv
  rw [← hdQ, ← mul_add, hsum]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-- [F-H helper] Area change of variables `w ↦ 1/w` from `𝔻` to `𝔻*` (`s4v_integral_reflection` and conjugation). -/
theorem s3fh_area_D (F : ℂ → ℂ) :
    (∫ u in unitDisc, F u) = ∫ w in unitDiscExterior, (((‖w‖ ^ 4)⁻¹ : ℝ) : ℂ) * F w⁻¹ := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [s4v_integral_reflection F, ← s36l_conj_integral hEm (fun _ => s3pk_conj_exterior)
    (fun w => (((‖w‖ ^ 4)⁻¹ : ℝ) : ℂ) * F w⁻¹)]
  refine setIntegral_congr_fun hEm fun w _ => ?_
  simp only [refl, RCLike.norm_conj]

/-- [F-H helper] Area change of variables `w ↦ 1/w` from `𝔻*` to `𝔻`. -/
theorem s3fh_area_E (F : ℂ → ℂ) :
    (∫ u in unitDiscExterior, F u) = ∫ w in unitDisc, (((‖w‖ ^ 4)⁻¹ : ℝ) : ℂ) * F w⁻¹ := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [s3fh_area_D (fun w => (((‖w‖ ^ 4)⁻¹ : ℝ) : ℂ) * F w⁻¹)]
  refine setIntegral_congr_fun hEm fun w hw => ?_
  have hw0 : ‖w‖ ≠ 0 := by
    have : (1 : ℝ) < ‖w‖ := hw
    linarith
  have hw0' : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw0
  simp only [inv_inv, norm_inv]
  push_cast
  field_simp

/-- [F-H helper] The conjugation `H = ι ∘ h ∘ ι` (`ι(z) = 1/z`) at `x ≠ 0`: values, first derivative, and
`𝒜(H) - 2H'/H + 2/x = -x⁻² 𝒜(h)(1/x)`. -/
theorem s3fh_inv_pre {h H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hh0 : ∀ y ∈ U, h y ≠ 0) {x : ℂ} (hx : x ≠ 0) (hxU : x⁻¹ ∈ U) (hd : deriv h x⁻¹ ≠ 0)
    (hev : H =ᶠ[𝓝 x] fun y => (h y⁻¹)⁻¹) :
    H x = (h x⁻¹)⁻¹ ∧ deriv H x = deriv h x⁻¹ * (x⁻¹) ^ 2 / h x⁻¹ ^ 2 ∧
      preSchwarzian H x - 2 * deriv H x / H x + 2 / x = -(x⁻¹) ^ 2 * preSchwarzian h x⁻¹ := by
  have hinv : Tendsto (fun y : ℂ => y⁻¹) (𝓝 x) (𝓝 x⁻¹) := tendsto_inv₀ hx
  have hV : ∀ᶠ y in 𝓝 x, y ≠ 0 ∧ y⁻¹ ∈ U := (eventually_ne_nhds hx).and (hinv (hU.mem_nhds hxU))
  have hD1 : ∀ y : ℂ, y ≠ 0 → y⁻¹ ∈ U →
      HasDerivAt (fun y => (h y⁻¹)⁻¹) (deriv h y⁻¹ * (y⁻¹) ^ 2 / h y⁻¹ ^ 2) y := by
    intro y hy hyU
    have h1 := ((hh.differentiableAt (hU.mem_nhds hyU)).hasDerivAt).comp y (hasDerivAt_inv hy)
    have h2 := h1.inv (hh0 _ hyU)
    have := hh0 _ hyU
    refine h2.congr_deriv ?_
    simp only [Function.comp_apply]
    field_simp
  have hdH : deriv H =ᶠ[𝓝 x] fun y => deriv h y⁻¹ * (y⁻¹) ^ 2 / h y⁻¹ ^ 2 := by
    filter_upwards [hev.eventuallyEq_nhds, hV] with y hy hyV
    rw [hy.deriv_eq, (hD1 y hyV.1 hyV.2).deriv]
  have a1 := (((hh.deriv hU).differentiableAt (hU.mem_nhds hxU)).hasDerivAt).comp x (hasDerivAt_inv hx)
  have a2 := (hasDerivAt_inv hx).pow 2
  have a3 := ((((hh.differentiableAt (hU.mem_nhds hxU)).hasDerivAt).comp x (hasDerivAt_inv hx)).pow 2)
  have hd2 := ((a1.mul a2).div a3 (pow_ne_zero 2 (hh0 _ hxU))).congr_of_eventuallyEq hdH
  have hHx : H x = (h x⁻¹)⁻¹ := hev.eq_of_nhds
  have hH'x : deriv H x = deriv h x⁻¹ * (x⁻¹) ^ 2 / h x⁻¹ ^ 2 := hdH.eq_of_nhds
  refine ⟨hHx, hH'x, ?_⟩
  show deriv (deriv H) x / deriv H x - 2 * deriv H x / H x + 2 / x =
    -(x⁻¹) ^ 2 * (deriv (deriv h) x⁻¹ / deriv h x⁻¹)
  rw [hd2.deriv, hH'x, hHx]
  simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
  have hB := hh0 _ hxU
  generalize deriv (deriv h) x⁻¹ = C
  generalize deriv h x⁻¹ = A at hd ⊢
  generalize h x⁻¹ = B at hB ⊢
  field_simp
  linear_combination (-2 * x * A * B ^ 2) * mul_inv_cancel₀ hx

/-- [F-H helper] For a welding pair as in `s36l_smooth_pair`, `g(ω) ≠ f(v)` for `‖ω‖ ≥ 1` and `v ∈ 𝔻` (for
`‖ω‖ = 1`: `f(𝔻)` is a neighbourhood of `f(v)` by the open mapping theorem, while `g(ζ) ∉ f(𝔻̄)` for `‖ζ‖ > 1`). -/
theorem s3fh_key1 {f g : ℂ → ℂ} {R r : ℝ} (hR : 1 < R) (hr : r < 1)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R))
    (hg : DifferentiableOn ℂ g {w | r < ‖w‖})
    (hc : g '' unitDiscExterior = (f '' closedBall 0 1)ᶜ) {ω v : ℂ} (hω : 1 ≤ ‖ω‖) (hv : v ∈ unitDisc) :
    g ω ≠ f v := by
  have hvR : v ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hv) hR)
  have hout : ∀ ζ : ℂ, 1 < ‖ζ‖ → g ζ ∉ f '' unitDisc := by
    intro ζ hζ hmem
    have h1 : g ζ ∈ g '' unitDiscExterior := mem_image_of_mem g hζ
    rw [hc] at h1
    exact h1 (image_mono ball_subset_closedBall hmem)
  intro heq
  rcases hω.lt_or_eq with hω1 | hω1
  · exact hout ω hω1 (heq ▸ mem_image_of_mem f hv)
  have han : AnalyticAt ℂ f v := hf.analyticAt (isOpen_ball.mem_nhds hvR)
  have hnhds : 𝓝 (f v) ≤ map f (𝓝 v) := by
    refine han.eventually_constant_or_nhds_le_map_nhds.resolve_left fun hev => ?_
    have h2 : ∀ᶠ z in 𝓝[≠] v, f z = f v ∧ z ∈ ball (0 : ℂ) R ∧ z ∈ ({v} : Set ℂ)ᶜ :=
      Filter.Eventually.and (mem_nhdsWithin_of_mem_nhds hev)
        (Filter.Eventually.and (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hvR)) self_mem_nhdsWithin)
    obtain ⟨z, hz1, hz2, hz3⟩ := h2.exists
    exact hz3 (hfi hz2 hvR hz1)
  have hU : f '' unitDisc ∈ 𝓝 (g ω) := heq ▸ hnhds (image_mem_map (isOpen_ball.mem_nhds hv))
  have hrω : r < ‖ω‖ := by rw [← hω1]; exact hr
  have hgc : ContinuousAt g ω :=
    (hg.differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hrω)).continuousAt
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hgc.preimage_mem_nhds hU)
  have hζ1 : 1 < ‖ω * ((1 + ε / 2 : ℝ) : ℂ)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← hω1]
    linarith
  have hζb : ω * ((1 + ε / 2 : ℝ) : ℂ) ∈ ball ω ε := by
    have h : ω * ((1 + ε / 2 : ℝ) : ℂ) - ω = ω * ((ε / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [mem_ball, dist_eq_norm, h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← hω1]
    linarith
  exact hout _ hζ1 (hsub hζb)

/-- [F-H helper] The `ι`-conjugated welding pair `(F̂, ĝ) = (ι ∘ g ∘ ι, ι ∘ f ∘ ι)` is again complementary:
`ĝ(𝔻*) = (F̂(𝔻̄))ᶜ` (`s3fh_key1` and `s36l_sp_weld`). -/
theorem s3fh_cmpl {f g Fh : ℂ → ℂ} {R r r' : ℝ} (hR : 1 < R) (hr : r < 1)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R)) (hf0 : f 0 = 0)
    (hg : DifferentiableOn ℂ g {w | r < ‖w‖}) (hgi : InjOn g {w | r < ‖w‖})
    (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hc : g '' unitDiscExterior = (f '' closedBall 0 1)ᶜ) (hr0 : 0 < r') (hr'1 : r' < 1)
    (hF0 : Fh 0 = 0) (hFeq : ∀ u : ℂ, u ≠ 0 → ‖u‖ < r'⁻¹ → Fh u = (g u⁻¹)⁻¹) :
    (fun w => (f w⁻¹)⁻¹) '' unitDiscExterior = (Fh '' closedBall 0 1)ᶜ := by
  have h1r : (1 : ℝ) < r'⁻¹ := (one_lt_inv₀ hr0).mpr hr'1
  have hfne : ∀ v ∈ ball (0 : ℂ) R, v ≠ 0 → f v ≠ 0 := fun v hv hv0 h =>
    hv0 (hfi hv (mem_ball_self (lt_trans one_pos hR)) (h.trans hf0.symm))
  obtain ⟨γ, a, b, ha, hb, -, -, hγ, hγ1⟩ := s36l_sp_weld hR le_rfl hr hf hfi hg hgi hginf hc
  ext y
  simp only [mem_image, mem_compl_iff, not_exists, not_and]
  constructor
  · rintro ⟨w, hw, rfl⟩ z hz hFz
    have hw1 : (1 : ℝ) < ‖w‖ := hw
    have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans one_pos hw1)
    have hv : w⁻¹ ∈ unitDisc := by
      show w⁻¹ ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, norm_inv]; exact inv_lt_one_of_one_lt₀ hw1
    have hvR : w⁻¹ ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hv) hR)
    have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    by_cases hz0 : z = 0
    · rw [hz0, hF0] at hFz
      exact hfne _ hvR (inv_ne_zero hw0) (inv_eq_zero.mp hFz.symm)
    · rw [hFeq z hz0 (lt_of_le_of_lt hz1 h1r)] at hFz
      have hz' : 1 ≤ ‖z⁻¹‖ := by rw [norm_inv]; exact (one_le_inv₀ (norm_pos_iff.mpr hz0)).mpr hz1
      exact s3fh_key1 hR hr hf hfi hg hc hz' hv (inv_inj.mp hFz)
  · intro hy
    have hy0 : y ≠ 0 := fun h => hy 0 (mem_closedBall_self zero_le_one) (hF0.trans h.symm)
    have hgy : ∀ ω : ℂ, 1 ≤ ‖ω‖ → g ω ≠ y⁻¹ := by
      intro ω hω h
      have hω0 : ω ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le one_pos hω)
      have hωi : ‖ω⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hω
      refine hy ω⁻¹ (mem_closedBall_zero_iff.mpr hωi) ?_
      rw [hFeq _ (inv_ne_zero hω0) (lt_of_le_of_lt hωi h1r), inv_inv, h, inv_inv]
    have hin : y⁻¹ ∈ f '' closedBall 0 1 := by
      by_contra hn
      rw [← mem_compl_iff, ← hc] at hn
      obtain ⟨ω, hω, h⟩ := hn
      exact hgy ω (le_of_lt hω) h
    obtain ⟨v, hv, hfv⟩ := hin
    have hv1 : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp hv
    rcases hv1.lt_or_eq with hv1 | hv1
    · have hv0 : v ≠ 0 := by
        rintro rfl
        rw [hf0] at hfv
        exact hy0 (inv_eq_zero.mp hfv.symm)
      refine ⟨v⁻¹, ?_, ?_⟩
      · show (1 : ℝ) < ‖v⁻¹‖
        rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.mpr hv0)).mpr hv1
      · simp only [inv_inv, hfv]
    · obtain ⟨-, hγ2⟩ := hγ v (by rw [hv1]; exact ha) (by rw [hv1]; exact hb)
      exact (hgy (γ v) (le_of_eq (hγ1 v hv1).symm) (hγ2.trans hfv)).elim

/-- [F-H helper] **The `g`-side identity** for an abstract welding pair: Lemma 3.6 (`s3fh_smoothQ`, the
`Q`-version) applied to the `ι`-conjugated pair `(ι ∘ g ∘ ι, ι ∘ f ∘ ι)` at `1/u`, transported back by `w ↦ 1/w`
(`s3fh_area_D`, `s3fh_area_E`, `s3fh_inv_pre`) and divided by `u²`. -/
theorem s3fh_gside {f g : ℂ → ℂ} {R r : ℝ} (hR : 1 < R) (hr : r < 1)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R)) (hf0 : f 0 = 0)
    (hfd : ∀ z ∈ ball (0 : ℂ) R, deriv f z ≠ 0)
    (hg : DifferentiableOn ℂ g {w | r < ‖w‖}) (hgi : InjOn g {w | r < ‖w‖})
    (hgd : ∀ z : ℂ, r < ‖z‖ → deriv g z ≠ 0)
    (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hc : g '' unitDiscExterior = (f '' closedBall 0 1)ᶜ) {u : ℂ} (hu : u ∈ unitDiscExterior) :
    ((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian f w) * (deriv g u * deriv f w / (g u - f w) ^ 2)) +
        (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian g ω) *
          (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2) =
      preSchwarzian g u - 2 * deriv g u / g u + 2 / u := by
  have hu1 : (1 : ℝ) < ‖u‖ := hu
  have hu0 : u ≠ 0 := norm_pos_iff.mp (lt_trans one_pos hu1)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hDm : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  obtain ⟨r', hrr', hr'2, hr'1, hgne⟩ :=
    s36l_sp_annulus hR hr hf hfi hf0 hg hgi hginf hc (mem_ball_self one_pos)
  have hr0 : 0 < r' := by linarith
  have h1r : (1 : ℝ) < r'⁻¹ := (one_lt_inv₀ hr0).mpr hr'1
  have hU : IsOpen {w : ℂ | r' < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hg' : DifferentiableOn ℂ g {w | r' < ‖w‖} :=
    hg.mono fun w (hw : r' < ‖w‖) => (show r < ‖w‖ by linarith)
  have hgi' : InjOn g {w | r' < ‖w‖} := hgi.mono fun w (hw : r' < ‖w‖) => (show r < ‖w‖ by linarith)
  obtain ⟨Fh, hFd, hFi, hF0, hFeq⟩ := s36l_sp_inv hr0 hg' hgi' hginf fun w hw => (hgne w hw).1
  have hfne : ∀ v ∈ ball (0 : ℂ) R, v ≠ 0 → f v ≠ 0 := fun v hv hv0 h =>
    hv0 (hfi hv (mem_ball_self (lt_trans one_pos hR)) (h.trans hf0.symm))
  -- the reflected exterior map `ĝ = ι ∘ f ∘ ι`
  obtain ⟨gh, hgh⟩ : ∃ gh : ℂ → ℂ, gh = fun w => (f w⁻¹)⁻¹ := ⟨_, rfl⟩
  have hR0 : 0 < R := lt_trans one_pos hR
  have hRi : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hVo : IsOpen (ball (0 : ℂ) R \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hfV : DifferentiableOn ℂ f (ball (0 : ℂ) R \ {0}) := hf.mono sdiff_subset
  have hfV0 : ∀ y ∈ ball (0 : ℂ) R \ {0}, f y ≠ 0 := fun y hy => hfne y hy.1 hy.2
  have hinvV : ∀ w : ℂ, R⁻¹ < ‖w‖ → w ≠ 0 ∧ w⁻¹ ∈ ball (0 : ℂ) R \ {0} := by
    intro w hw
    have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans (inv_pos.mpr hR0) hw)
    refine ⟨hw0, mem_ball_zero_iff.mpr ?_, fun h => inv_ne_zero hw0 h⟩
    rw [norm_inv]; exact (inv_lt_comm₀ (norm_pos_iff.mpr hw0) hR0).mpr hw
  have hghd : DifferentiableOn ℂ gh {w | R⁻¹ < ‖w‖} := by
    rw [hgh]
    intro w hw
    obtain ⟨hw0, hwV⟩ := hinvV w hw
    exact (((hf.differentiableAt (isOpen_ball.mem_nhds hwV.1)).comp w (differentiableAt_inv hw0)).inv
      (hfV0 _ hwV)).differentiableWithinAt
  have hghi : InjOn gh {w | R⁻¹ < ‖w‖} := by
    rw [hgh]
    intro w1 hw1 w2 hw2 h
    have h' : f w1⁻¹ = f w2⁻¹ := inv_inj.mp h
    exact inv_inj.mp (hfi (hinvV w1 hw1).2.1 (hinvV w2 hw2).2.1 h')
  have hghinf : Tendsto gh (cocompact ℂ) (cocompact ℂ) := by
    rw [hgh, ← Metric.cobounded_eq_cocompact]
    have h0 : Tendsto f (𝓝 0) (𝓝 0) := by
      have := (hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR0))).continuousAt.tendsto
      rwa [hf0] at this
    have h1 : Tendsto (fun w : ℂ => f w⁻¹) (Bornology.cobounded ℂ) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨h0.comp tendsto_inv₀_cobounded, ?_⟩
      filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R⁻¹)] with w hw
      exact hfV0 _ (hinvV w hw).2
    exact tendsto_inv₀_nhdsNE_zero.comp h1
  have hcc : gh '' unitDiscExterior = (Fh '' closedBall 0 1)ᶜ := by
    rw [hgh]; exact s3fh_cmpl hR hr hf hfi hf0 hg hgi hginf hc hr0 hr'1 hF0 hFeq
  have hx : u⁻¹ ∈ unitDisc := by
    show u⁻¹ ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_inv]; exact inv_lt_one_of_one_lt₀ hu1
  have hS := s3fh_smoothQ h1r hRi hFd hFi hF0 hghd hghi hghinf hcc hx
  -- `F̂` and `ĝ` near `1/y`
  have hFinv : ∀ y : ℂ, 1 < ‖y‖ → Fh y⁻¹ = (g y)⁻¹ ∧ deriv Fh y⁻¹ = deriv g y * y ^ 2 / g y ^ 2 ∧
      preSchwarzian Fh y⁻¹ - 2 * deriv Fh y⁻¹ / Fh y⁻¹ + 2 / y⁻¹ = -y ^ 2 * preSchwarzian g y := by
    intro y hy
    have hy0 : y ≠ 0 := norm_pos_iff.mp (lt_trans one_pos hy)
    have ho : IsOpen {z : ℂ | z ≠ 0 ∧ ‖z‖ < r'⁻¹} := isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
    have hev : Fh =ᶠ[𝓝 y⁻¹] fun z => (g z⁻¹)⁻¹ := by
      have hm : y⁻¹ ∈ {z : ℂ | z ≠ 0 ∧ ‖z‖ < r'⁻¹} :=
        ⟨inv_ne_zero hy0, by rw [norm_inv]; exact lt_trans (inv_lt_one_of_one_lt₀ hy) h1r⟩
      filter_upwards [ho.mem_nhds hm] with z hz
      exact hFeq z hz.1 hz.2
    have hyU : y⁻¹⁻¹ ∈ {w : ℂ | r' < ‖w‖} := by rw [inv_inv]; show r' < ‖y‖; linarith
    have h := s3fh_inv_pre hU hg' (fun w hw => (hgne w hw).1) (inv_ne_zero hy0) hyU
      (by rw [inv_inv]; exact hgd y (by linarith)) hev
    simp only [inv_inv] at h
    exact h
  have hginv : ∀ v ∈ unitDisc, v ≠ 0 → gh v⁻¹ = (f v)⁻¹ ∧ deriv gh v⁻¹ = deriv f v * v ^ 2 / f v ^ 2 ∧
      preSchwarzian gh v⁻¹ - 2 * deriv gh v⁻¹ / gh v⁻¹ + 2 / v⁻¹ = -v ^ 2 * preSchwarzian f v := by
    intro v hv hv0
    have hvR : v ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hv) hR)
    have hev : gh =ᶠ[𝓝 v⁻¹] fun y => (f y⁻¹)⁻¹ := Filter.Eventually.of_forall fun y => by rw [hgh]
    have hvV : v⁻¹⁻¹ ∈ ball (0 : ℂ) R \ {0} := by rw [inv_inv]; exact ⟨hvR, hv0⟩
    have h := s3fh_inv_pre hVo hfV hfV0 (inv_ne_zero hv0) hvV (by rw [inv_inv]; exact hfd v hvR) hev
    simp only [inv_inv] at h
    exact h
  have hgu0 : g u ≠ 0 := (hgne u (by linarith)).1
  -- the `𝔻`-integral of `F̂` becomes the `g`-side integral
  have hI1 : (∫ w in unitDisc, kerK1 Fh u⁻¹ w * conj (preSchwarzian Fh w - 2 * deriv Fh w / Fh w + 2 / w)) =
      (u ^ 2 * (1 / π : ℂ)) * ∫ ω in unitDiscExterior, conj (preSchwarzian g ω) *
        (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2) := by
    rw [s3fh_area_D, ← integral_const_mul]
    refine setIntegral_congr_ae hEm ?_
    filter_upwards [(volume : Measure ℂ).ae_ne u] with ω hωu hω
    have hω1 : (1 : ℝ) < ‖ω‖ := hω
    have hω0 : ω ≠ 0 := norm_pos_iff.mp (lt_trans one_pos hω1)
    obtain ⟨a1, a2, a3⟩ := hFinv ω hω1
    obtain ⟨b1, b2, -⟩ := hFinv u hu1
    have hne : u⁻¹ ≠ ω⁻¹ := fun h => hωu (inv_inj.mp h).symm
    have hgω0 : g ω ≠ 0 := (hgne ω (by linarith)).1
    have hguω : g u - g ω ≠ 0 :=
      sub_ne_zero.mpr fun h => hωu (hgi' (show r' < ‖u‖ by linarith) (show r' < ‖ω‖ by linarith) h).symm
    have hgωu : g ω - g u ≠ 0 := fun h => hguω (by linear_combination -h)
    have huω : u - ω ≠ 0 := sub_ne_zero.mpr fun h => hωu h.symm
    have hωu' : ω - u ≠ 0 := sub_ne_zero.mpr hωu
    have hc0 : conj ω ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hω0
    have hn : (((‖ω‖ ^ 4)⁻¹ : ℝ) : ℂ) = ((ω * conj ω) ^ 2)⁻¹ := by
      rw [Complex.mul_conj']; push_cast; ring
    rw [a3, kerK1, if_neg hne, a1, a2, b1, b2, inv_sub_inv hu0 hω0, inv_sub_inv hgu0 hgω0, hn]
    simp only [map_neg, map_mul, map_pow]
    field_simp
    ring
  -- the `𝔻*`-integral of `(F̂, ĝ)` becomes the `f`-side integral
  have hI2 : (∫ w in unitDiscExterior, kerK2 Fh gh u⁻¹ w *
        conj (-(preSchwarzian gh w - 2 * deriv gh w / gh w + 2 / w))) =
      (u ^ 2 * (1 / π : ℂ)) * ∫ w in unitDisc, conj (preSchwarzian f w) *
        (deriv g u * deriv f w / (g u - f w) ^ 2) := by
    rw [s3fh_area_E, ← integral_const_mul]
    refine setIntegral_congr_ae hDm ?_
    filter_upwards [(volume : Measure ℂ).ae_ne 0] with v hv0 hv
    have hvR : v ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hv) hR)
    obtain ⟨c1, c2, c3⟩ := hginv v hv hv0
    obtain ⟨b1, b2, -⟩ := hFinv u hu1
    have hfv0 : f v ≠ 0 := hfne v hvR hv0
    have hguv : g u - f v ≠ 0 := sub_ne_zero.mpr (s3fh_key1 hR hr hf hfi hg hc (le_of_lt hu1) hv)
    have hgvu : f v - g u ≠ 0 := fun h => hguv (by linear_combination -h)
    have hc0 : conj v ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hv0
    have hn : (((‖v‖ ^ 4)⁻¹ : ℝ) : ℂ) = ((v * conj v) ^ 2)⁻¹ := by
      rw [Complex.mul_conj']; push_cast; ring
    rw [c3, kerK2, b1, b2, c1, c2, inv_sub_inv hgu0 hfv0, hn]
    simp only [map_neg, map_mul, map_pow]
    field_simp
    ring
  have hR' : -preSchwarzian Fh u⁻¹ = u ^ 2 * (preSchwarzian g u - 2 * deriv g u / g u + 2 / u) := by
    obtain ⟨b1, b2, b3⟩ := hFinv u hu1
    rw [b1, b2] at b3
    have hA : preSchwarzian Fh u⁻¹ =
        -u ^ 2 * preSchwarzian g u + 2 * (deriv g u * u ^ 2 / g u ^ 2) / (g u)⁻¹ - 2 / u⁻¹ := by
      linear_combination b3
    rw [hA]
    field_simp
    ring
  rw [hI1, hI2, hR'] at hS
  apply mul_left_cancel₀ (pow_ne_zero 2 hu0)
  linear_combination hS

/-- **(F-H)** `h = 𝒜(g) - 2g'/g + 2/u` on `𝔻*` (installed `lemma_3_6` transported by `ι`, plus
`E = 1/u - g'/g` by Stokes to `𝕊¹` and residues). -/
theorem s3f_h {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ)) :
    ∀ u ∈ unitDiscExterior, (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) u * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) u * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (u - ω) ^ 2)) = preSchwarzian (gsans (beltramiMul a κ)) u - 2 * deriv (gsans (beltramiMul a κ)) u / gsans (beltramiMul a κ) u + 2 / u := by
  intro u hu
  obtain ⟨⟨ρ, hρ, G, hGd, hGi, hGd', hGg⟩, R, hR, F, hFd, hFi, hFd', hFg⟩ := d2l_ext hκ hκD ha has haL haD
  have haB : a ∈ LinfStarBall := by
    show a ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff]
    exact has.trans delta0_bounds.2
  set ν := beltramiMul a (κ : LinfStar) with hν_def
  have hν : ν ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  obtain ⟨hcomp, hinf⟩ := s36l_complement hν
  have hDm : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  -- `F = 𝖿` on `𝔻̄` (both continuous there), hence the complement relation for `(F, G)`
  have hfc : ContinuousOn (fsans ν) (closedBall 0 1) := by
    intro z hz
    rw [S2C.s2c_fsans_eq hν]
    exact (s5e_fB_continuousAt hν (mem_closedBall_zero_iff.mp hz)).continuousWithinAt
  have hFcB : EqOn F (fsans ν) (closedBall 0 1) := by
    refine hFg.of_subset_closure (hFd.continuousOn.mono (closedBall_subset_ball hR)) hfc ball_subset_closedBall ?_
    show closedBall (0 : ℂ) 1 ⊆ closure (ball 0 1)
    rw [closure_ball 0 one_ne_zero]
  have hF0 : F 0 = 0 := (hFg (mem_ball_self one_pos)).trans (s2c_facts hν).2.2.1
  have hc : G '' unitDiscExterior = (F '' closedBall 0 1)ᶜ := by
    rw [hGg.image_eq, hFcB.image_eq]; exact hcomp
  have hGinf : Tendsto G (cocompact ℂ) (cocompact ℂ) := by
    refine hinf.congr' ?_
    filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with w hw
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hw
    exact (hGg hw).symm
  have key := s3fh_gside hR hρ hFd hFi hF0 hFd' hGd hGi hGd' hGinf hc hu
  -- back to `(𝖿, 𝗀)` on the open sets `𝔻`, `𝔻*`
  have hpre : ∀ (A B : ℂ → ℂ) (z : ℂ), A =ᶠ[𝓝 z] B →
      preSchwarzian A z = preSchwarzian B z ∧ deriv A z = deriv B z := by
    intro A B z h
    refine ⟨?_, h.deriv_eq⟩
    unfold preSchwarzian
    rw [h.deriv.deriv_eq, h.deriv_eq]
  have hFev : ∀ z ∈ unitDisc, F =ᶠ[𝓝 z] fsans ν := fun z hz => by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hFg hw
  have hGev : ∀ z ∈ unitDiscExterior, G =ᶠ[𝓝 z] gsans ν := fun z hz => by
    filter_upwards [hEo.mem_nhds hz] with w hw
    exact hGg hw
  obtain ⟨hGu1, hGu2⟩ := hpre _ _ _ (hGev u hu)
  have e1 : (∫ w in unitDisc, conj (preSchwarzian F w) * (deriv G u * deriv F w / (G u - F w) ^ 2)) =
      ∫ w in unitDisc, conj (preSchwarzian (fsans ν) w) *
        (deriv (gsans ν) u * deriv (fsans ν) w / (gsans ν u - fsans ν w) ^ 2) := by
    refine setIntegral_congr_fun hDm fun w hw => ?_
    obtain ⟨h1, h2⟩ := hpre _ _ _ (hFev w hw)
    rw [h1, h2, hGu2, hGg hu, hFg hw]
  have e2 : (∫ ω in unitDiscExterior, conj (preSchwarzian G ω) *
        (deriv G u * deriv G ω / (G u - G ω) ^ 2 - 1 / (u - ω) ^ 2)) =
      ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans ν) ω) *
        (deriv (gsans ν) u * deriv (gsans ν) ω / (gsans ν u - gsans ν ω) ^ 2 - 1 / (u - ω) ^ 2) := by
    refine setIntegral_congr_fun hEo.measurableSet fun ω hω => ?_
    obtain ⟨h1, h2⟩ := hpre _ _ _ (hGev ω hω)
    rw [h1, h2, hGu2, hGg hu, hGg hω]
  rw [e1, e2, hGu1, hGu2, hGg hu] at key
  exact key

/-- [F-POLE helper] The `u = ∞` case of `s3fh_gside`: `s3fh_smoothQ` for the `ι`-pair (`F̂ = ι ∘ g ∘ ι`,
`ĝ = ι ∘ f ∘ ι`) at `z = 0`. With `c = F̂'(0)` (`= 1/b`):
`(1/π)∫_𝔻 conj 𝒜(f)·c f' + (1/π)∫_{𝔻*} conj 𝒜(g)(c g' - 1) = -𝒜(F̂)(0)`, the `𝔻*`-integrand being integrable. -/
theorem s3fp_gside0 {f g : ℂ → ℂ} {R r : ℝ} (hR : 1 < R) (hr : r < 1)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hfi : InjOn f (ball 0 R)) (hf0 : f 0 = 0)
    (hfd : ∀ z ∈ ball (0 : ℂ) R, deriv f z ≠ 0)
    (hg : DifferentiableOn ℂ g {w | r < ‖w‖}) (hgi : InjOn g {w | r < ‖w‖})
    (hgd : ∀ z : ℂ, r < ‖z‖ → deriv g z ≠ 0)
    (hginf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hc : g '' unitDiscExterior = (f '' closedBall 0 1)ᶜ) :
    ∃ s : ℝ, 1 < s ∧ ∃ Fh : ℂ → ℂ, DifferentiableOn ℂ Fh (ball 0 s) ∧ InjOn Fh (ball 0 s) ∧ Fh 0 = 0 ∧
      (∀ u : ℂ, u ≠ 0 → ‖u‖ < s → Fh u = (g u⁻¹)⁻¹) ∧
      IntegrableOn (fun ω => conj (preSchwarzian g ω) * (deriv Fh 0 * deriv g ω - 1)) unitDiscExterior ∧
      ((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian f w) * (deriv Fh 0 * deriv f w)) +
        (1 / π : ℂ) * (∫ ω in unitDiscExterior, conj (preSchwarzian g ω) * (deriv Fh 0 * deriv g ω - 1)) =
      -preSchwarzian Fh 0 := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hDm : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  obtain ⟨r', hrr', hr'2, hr'1, hgne⟩ :=
    s36l_sp_annulus hR hr hf hfi hf0 hg hgi hginf hc (mem_ball_self one_pos)
  have hr0 : 0 < r' := by linarith
  have h1r : (1 : ℝ) < r'⁻¹ := (one_lt_inv₀ hr0).mpr hr'1
  have hU : IsOpen {w : ℂ | r' < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hg' : DifferentiableOn ℂ g {w | r' < ‖w‖} :=
    hg.mono fun w (hw : r' < ‖w‖) => (show r < ‖w‖ by linarith)
  have hgi' : InjOn g {w | r' < ‖w‖} := hgi.mono fun w (hw : r' < ‖w‖) => (show r < ‖w‖ by linarith)
  obtain ⟨Fh, hFd, hFi, hF0, hFeq⟩ := s36l_sp_inv hr0 hg' hgi' hginf fun w hw => (hgne w hw).1
  have hfne : ∀ v ∈ ball (0 : ℂ) R, v ≠ 0 → f v ≠ 0 := fun v hv hv0 h =>
    hv0 (hfi hv (mem_ball_self (lt_trans one_pos hR)) (h.trans hf0.symm))
  -- the reflected exterior map `ĝ = ι ∘ f ∘ ι`
  obtain ⟨gh, hgh⟩ : ∃ gh : ℂ → ℂ, gh = fun w => (f w⁻¹)⁻¹ := ⟨_, rfl⟩
  have hR0 : 0 < R := lt_trans one_pos hR
  have hRi : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hVo : IsOpen (ball (0 : ℂ) R \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hfV : DifferentiableOn ℂ f (ball (0 : ℂ) R \ {0}) := hf.mono sdiff_subset
  have hfV0 : ∀ y ∈ ball (0 : ℂ) R \ {0}, f y ≠ 0 := fun y hy => hfne y hy.1 hy.2
  have hinvV : ∀ w : ℂ, R⁻¹ < ‖w‖ → w ≠ 0 ∧ w⁻¹ ∈ ball (0 : ℂ) R \ {0} := by
    intro w hw
    have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans (inv_pos.mpr hR0) hw)
    refine ⟨hw0, mem_ball_zero_iff.mpr ?_, fun h => inv_ne_zero hw0 h⟩
    rw [norm_inv]; exact (inv_lt_comm₀ (norm_pos_iff.mpr hw0) hR0).mpr hw
  have hghd : DifferentiableOn ℂ gh {w | R⁻¹ < ‖w‖} := by
    rw [hgh]
    intro w hw
    obtain ⟨hw0, hwV⟩ := hinvV w hw
    exact (((hf.differentiableAt (isOpen_ball.mem_nhds hwV.1)).comp w (differentiableAt_inv hw0)).inv
      (hfV0 _ hwV)).differentiableWithinAt
  have hghi : InjOn gh {w | R⁻¹ < ‖w‖} := by
    rw [hgh]
    intro w1 hw1 w2 hw2 h
    have h' : f w1⁻¹ = f w2⁻¹ := inv_inj.mp h
    exact inv_inj.mp (hfi (hinvV w1 hw1).2.1 (hinvV w2 hw2).2.1 h')
  have hghinf : Tendsto gh (cocompact ℂ) (cocompact ℂ) := by
    rw [hgh, ← Metric.cobounded_eq_cocompact]
    have h0 : Tendsto f (𝓝 0) (𝓝 0) := by
      have := (hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR0))).continuousAt.tendsto
      rwa [hf0] at this
    have h1 : Tendsto (fun w : ℂ => f w⁻¹) (Bornology.cobounded ℂ) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨h0.comp tendsto_inv₀_cobounded, ?_⟩
      filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R⁻¹)] with w hw
      exact hfV0 _ (hinvV w hw).2
    exact tendsto_inv₀_nhdsNE_zero.comp h1
  have hcc : gh '' unitDiscExterior = (Fh '' closedBall 0 1)ᶜ := by
    rw [hgh]; exact s3fh_cmpl hR hr hf hfi hf0 hg hgi hginf hc hr0 hr'1 hF0 hFeq
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hx : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hS := s3fh_smoothQ h1r hRi hFd hFi hF0 hghd hghi hghinf hcc hx
  have hFinv : ∀ y : ℂ, 1 < ‖y‖ → Fh y⁻¹ = (g y)⁻¹ ∧ deriv Fh y⁻¹ = deriv g y * y ^ 2 / g y ^ 2 ∧
      preSchwarzian Fh y⁻¹ - 2 * deriv Fh y⁻¹ / Fh y⁻¹ + 2 / y⁻¹ = -y ^ 2 * preSchwarzian g y := by
    intro y hy
    have hy0 : y ≠ 0 := norm_pos_iff.mp (lt_trans one_pos hy)
    have ho : IsOpen {z : ℂ | z ≠ 0 ∧ ‖z‖ < r'⁻¹} := isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
    have hev : Fh =ᶠ[𝓝 y⁻¹] fun z => (g z⁻¹)⁻¹ := by
      have hm : y⁻¹ ∈ {z : ℂ | z ≠ 0 ∧ ‖z‖ < r'⁻¹} :=
        ⟨inv_ne_zero hy0, by rw [norm_inv]; exact lt_trans (inv_lt_one_of_one_lt₀ hy) h1r⟩
      filter_upwards [ho.mem_nhds hm] with z hz
      exact hFeq z hz.1 hz.2
    have hyU : y⁻¹⁻¹ ∈ {w : ℂ | r' < ‖w‖} := by rw [inv_inv]; show r' < ‖y‖; linarith
    have h := s3fh_inv_pre hU hg' (fun w hw => (hgne w hw).1) (inv_ne_zero hy0) hyU
      (by rw [inv_inv]; exact hgd y (by linarith)) hev
    simp only [inv_inv] at h
    exact h
  have hginv : ∀ v ∈ unitDisc, v ≠ 0 → gh v⁻¹ = (f v)⁻¹ ∧ deriv gh v⁻¹ = deriv f v * v ^ 2 / f v ^ 2 ∧
      preSchwarzian gh v⁻¹ - 2 * deriv gh v⁻¹ / gh v⁻¹ + 2 / v⁻¹ = -v ^ 2 * preSchwarzian f v := by
    intro v hv hv0
    have hvR : v ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hv) hR)
    have hev : gh =ᶠ[𝓝 v⁻¹] fun y => (f y⁻¹)⁻¹ := Filter.Eventually.of_forall fun y => by rw [hgh]
    have hvV : v⁻¹⁻¹ ∈ ball (0 : ℂ) R \ {0} := by rw [inv_inv]; exact ⟨hvR, hv0⟩
    have h := s3fh_inv_pre hVo hfV hfV0 (inv_ne_zero hv0) hvV (by rw [inv_inv]; exact hfd v hvR) hev
    simp only [inv_inv] at h
    exact h
  -- the pointwise transport of the `𝔻`-integrand of `F̂` (at `z = 0`) to `𝔻*`
  have hpt : ∀ ω ∈ unitDiscExterior, (((‖ω‖ ^ 4)⁻¹ : ℝ) : ℂ) *
      (kerK1 Fh 0 ω⁻¹ * conj (preSchwarzian Fh ω⁻¹ - 2 * deriv Fh ω⁻¹ / Fh ω⁻¹ + 2 / ω⁻¹)) =
      (1 / π : ℂ) * (conj (preSchwarzian g ω) * (deriv Fh 0 * deriv g ω - 1)) := by
    intro ω hω
    have hω1 : (1 : ℝ) < ‖ω‖ := hω
    have hω0 : ω ≠ 0 := norm_pos_iff.mp (lt_trans one_pos hω1)
    obtain ⟨a1, a2, a3⟩ := hFinv ω hω1
    have hne : (0 : ℂ) ≠ ω⁻¹ := (inv_ne_zero hω0).symm
    have hgω0 : g ω ≠ 0 := (hgne ω (by linarith)).1
    have hc0 : conj ω ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hω0
    have hn : (((‖ω‖ ^ 4)⁻¹ : ℝ) : ℂ) = ((ω * conj ω) ^ 2)⁻¹ := by
      rw [Complex.mul_conj']; push_cast; ring
    rw [a3, kerK1, if_neg hne, a1, a2, hF0, hn]
    simp only [map_neg, map_mul, map_pow]
    field_simp
    ring
  have hI1 : (∫ w in unitDisc, kerK1 Fh 0 w * conj (preSchwarzian Fh w - 2 * deriv Fh w / Fh w + 2 / w)) =
      (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian g ω) * (deriv Fh 0 * deriv g ω - 1) := by
    rw [s3fh_area_D, ← integral_const_mul]
    exact setIntegral_congr_fun hEm hpt
  have hI2 : (∫ w in unitDiscExterior, kerK2 Fh gh 0 w *
        conj (-(preSchwarzian gh w - 2 * deriv gh w / gh w + 2 / w))) =
      (1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian f w) * (deriv Fh 0 * deriv f w) := by
    rw [s3fh_area_E, ← integral_const_mul]
    refine setIntegral_congr_ae hDm ?_
    filter_upwards [(volume : Measure ℂ).ae_ne 0] with v hv0 hv
    have hvR : v ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hv) hR)
    obtain ⟨c1, c2, c3⟩ := hginv v hv hv0
    have hfv0 : f v ≠ 0 := hfne v hvR hv0
    have hc0 : conj v ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hv0
    have hn : (((‖v‖ ^ 4)⁻¹ : ℝ) : ℂ) = ((v * conj v) ^ 2)⁻¹ := by
      rw [Complex.mul_conj']; push_cast; ring
    rw [c3, kerK2, c1, c2, hF0, hn]
    simp only [map_neg, map_mul, map_pow]
    field_simp
    ring
  -- integrability of the `𝔻*`-integrand: transport of a bounded continuous function on `𝔻̄`
  have hint : IntegrableOn (fun ω => conj (preSchwarzian g ω) * (deriv Fh 0 * deriv g ω - 1)) unitDiscExterior := by
    have hs0 : (0 : ℂ) ∈ ball (0 : ℂ) r'⁻¹ := mem_ball_self (by linarith)
    obtain ⟨K, hKd, hKe⟩ := s36l_sp_K1_holo hFd hFi hs0
    obtain ⟨-, Q, -, hQd, -, hQ⟩ := s36l_sp_primD h1r hFd hFi hF0
    have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 r'⁻¹ := closedBall_subset_ball h1r
    have hQ' : ContinuousOn (deriv Q) (ball 0 r'⁻¹) :=
      (hQd.analyticOnNhd isOpen_ball).deriv.differentiableOn.continuousOn
    have hcont : ContinuousOn (fun w => K w * conj (deriv Q w)) (closedBall 0 1) :=
      ((hKd.continuousOn.mono hcb).mul ((Complex.continuous_conj.comp_continuousOn (hQ'.mono hcb))))
    have hD : IntegrableOn (fun w => kerK1 Fh 0 w * conj (preSchwarzian Fh w - 2 * deriv Fh w / Fh w + 2 / w))
        (unitDisc \ {0}) := by
      refine ((hcont.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
        (diff_subset.trans ball_subset_closedBall)).congr_fun (fun w hw => ?_)
        ((isOpen_ball.sdiff isClosed_singleton).measurableSet)
      have hw0 : w ≠ 0 := hw.2
      have hwR : w ∈ ball (0 : ℂ) r'⁻¹ := hcb (ball_subset_closedBall hw.1)
      show K w * conj (deriv Q w) = _
      rw [hKe w hwR hw0, (hQ w hwR hw0).deriv]
    have hc := resolvent_inv_exterior_conformal
    have hT := (ahP_integrableOn_image hEo hc.1 hc.2.1
      (fun w => kerK1 Fh 0 w * conj (preSchwarzian Fh w - 2 * deriv Fh w / Fh w + 2 / w))).mp
      (by rw [hc.2.2]; exact hD)
    refine IntegrableOn.congr_fun (hT.const_mul (π : ℂ)) (fun ω hω => ?_) hEm
    have hω0 : ω ≠ 0 := norm_pos_iff.mp (lt_trans one_pos (show (1 : ℝ) < ‖ω‖ from hω))
    have hdi : ‖deriv (fun z : ℂ => z⁻¹) ω‖ ^ 2 = (‖ω‖ ^ 4)⁻¹ := by
      rw [deriv_inv, norm_neg, norm_inv, norm_pow]; ring
    have h := hpt ω hω
    simp only [hdi, Complex.real_smul]
    rw [h]
    field_simp
  refine ⟨r'⁻¹, h1r, Fh, hFd, hFi, hF0, hFeq, hint, ?_⟩
  rw [hI1, hI2] at hS
  linear_combination hS

/-- [F-POLE helper] `g` at `∞` from `F̂ = ι ∘ g ∘ ι` at `0`: with `c = F̂'(0)`, `g(z)/z → 1/c` and
`g(z) - z/c → -𝒜(F̂)(0)/(2c)` (`F̂ = s q(s)`, `q = c + s p(s)`: `g - z/c = -p(1/z)/(c q(1/z))`, `𝒜(F̂)(0) = 2p(0)/c`). -/
theorem s3fp_inf {Fh g : ℂ → ℂ} {s : ℝ} (hs : 0 < s) (hFd : DifferentiableOn ℂ Fh (ball 0 s)) (hF0 : Fh 0 = 0)
    (hc : deriv Fh 0 ≠ 0) (hFg : ∀ u : ℂ, u ≠ 0 → ‖u‖ < s → Fh u = (g u⁻¹)⁻¹) :
    Tendsto (fun z => g z / z) (cocompact ℂ) (𝓝 (1 / deriv Fh 0)) ∧
      Tendsto (fun z => g z - 1 / deriv Fh 0 * z) (cocompact ℂ)
        (𝓝 (-preSchwarzian Fh 0 / (2 * deriv Fh 0))) := by
  have hn : ball (0 : ℂ) s ∈ 𝓝 0 := isOpen_ball.mem_nhds (mem_ball_self hs)
  set c := deriv Fh 0 with hcdef
  set q : ℂ → ℂ := dslope Fh 0 with hq_def
  have hq : DifferentiableOn ℂ q (ball 0 s) := (differentiableOn_dslope hn).mpr hFd
  have hq0 : q 0 = c := dslope_same Fh 0
  have hFq : ∀ u, Fh u = u * q u := fun u => by
    have h := sub_smul_dslope Fh 0 u
    rw [hF0, sub_zero, sub_zero, smul_eq_mul] at h
    exact h.symm
  set p : ℂ → ℂ := dslope q 0 with hp_def
  have hp : DifferentiableOn ℂ p (ball 0 s) := (differentiableOn_dslope hn).mpr hq
  have hp0 : p 0 = deriv q 0 := dslope_same q 0
  have hqp : ∀ u, q u = c + u * p u := fun u => by
    have h := sub_smul_dslope q 0 u
    rw [sub_zero, smul_eq_mul, hq0] at h
    linear_combination -h
  -- `𝒜(F̂)(0) = 2 p(0)/c`
  have hqd : DifferentiableOn ℂ (deriv q) (ball 0 s) := (hq.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hdF : ∀ u ∈ ball (0 : ℂ) s, deriv Fh u = q u + u * deriv q u := by
    intro u hu
    have hqa := (hq.differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
    have h := (hasDerivAt_id' u).mul hqa
    have he : (fun x => x * q x) = Fh := funext fun x => (hFq x).symm
    rw [← he]
    exact h.deriv.trans (by ring)
  have hddF : deriv (deriv Fh) 0 = 2 * deriv q 0 := by
    have hev : deriv Fh =ᶠ[𝓝 0] fun u => q u + u * deriv q u := by
      filter_upwards [hn] with u hu using hdF u hu
    rw [hev.deriv_eq]
    have hqa := (hq.differentiableAt hn).hasDerivAt
    have hqda := (hqd.differentiableAt hn).hasDerivAt
    have h := hqa.add ((hasDerivAt_id' 0).mul hqda)
    exact h.deriv.trans (by ring)
  have hA : preSchwarzian Fh 0 = 2 * p 0 / c := by
    unfold preSchwarzian
    rw [hddF, hp0]
  -- the limits at `∞`
  have hqc : ContinuousAt q 0 := (hq.differentiableAt hn).continuousAt
  have hpc : ContinuousAt p 0 := (hp.differentiableAt hn).continuousAt
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]; exact tendsto_inv₀_cobounded
  have hq0' : q 0 ≠ 0 := by rw [hq0]; exact hc
  have hev : ∀ᶠ z in cocompact ℂ, z ≠ 0 ∧ ‖z⁻¹‖ < s ∧ q z⁻¹ ≠ 0 := by
    have h1 := hinv.eventually (hqc.eventually_ne hq0')
    have h2 := hinv.eventually hn
    have h3 : ∀ᶠ z in cocompact ℂ, z ≠ 0 := by
      rw [← Metric.cobounded_eq_cocompact]
      filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with z hz
      exact norm_pos_iff.mp hz
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    exact ⟨hz3, mem_ball_zero_iff.mp hz2, hz1⟩
  have hgz : ∀ z : ℂ, z ≠ 0 → ‖z⁻¹‖ < s → q z⁻¹ ≠ 0 → g z = z / q z⁻¹ := by
    intro z hz hzs hqz
    have h := hFg z⁻¹ (inv_ne_zero hz) hzs
    rw [inv_inv, hFq] at h
    have h' : g z = (z⁻¹ * q z⁻¹)⁻¹ := by rw [h, inv_inv]
    rw [h']
    field_simp
  constructor
  · have hlim := (hqc.tendsto.comp hinv).inv₀ hq0'
    rw [hq0, ← one_div] at hlim
    refine hlim.congr' ?_
    filter_upwards [hev] with z hz
    obtain ⟨hz0, hzs, hqz⟩ := hz
    simp only [Function.comp]
    rw [hgz z hz0 hzs hqz]
    field_simp
  · have hlim := ((hpc.tendsto.comp hinv).neg.div ((hqc.tendsto.comp hinv).const_mul c) (mul_ne_zero hc hq0'))
    have hval : -p 0 / (c * q 0) = -preSchwarzian Fh 0 / (2 * c) := by
      rw [hA, hq0]
      field_simp
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [hev] with z hz
    obtain ⟨hz0, hzs, hqz⟩ := hz
    simp only [Function.comp, Pi.div_apply]
    rw [hgz z hz0 hzs hqz]
    have hne : c + z⁻¹ * p z⁻¹ ≠ 0 := by rw [← hqp]; exact hqz
    have hne2 : z * c + p z⁻¹ ≠ 0 := by
      have h : z * c + p z⁻¹ = z * (c + z⁻¹ * p z⁻¹) := by field_simp
      rw [h]; exact mul_ne_zero hz0 hne
    rw [hqp z⁻¹]
    generalize p z⁻¹ = P' at hne hne2 ⊢
    have hne3 : P' + c * z ≠ 0 := by rw [add_comm, mul_comm]; exact hne2
    field_simp
    linear_combination (-1 : ℂ) * inv_mul_cancel₀ hne3

/-- **(F-POLE)** The I-pole identity (Dirichlet pairing / Stokes on `Γ = f(𝕊¹) = g(𝕊¹)`, `λ₁ = 0`):
`∫_𝔻 conj 𝒜(f) f' + ∫_{𝔻*} conj 𝒜(g) (g' - b) = 2π b₀`, both integrands integrable. -/
theorem s3f_pole {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ)) :
    IntegrableOn (fun z => conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z) unitDisc ∧
      IntegrableOn (fun z => conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ)))) unitDiscExterior ∧
      (∫ z in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z) +
          (∫ z in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ)))) = 2 * π * limUnder (cocompact ℂ) (fun z => gsans (beltramiMul a κ) z - derivAtInfty (gsans (beltramiMul a κ)) * z) := by
  obtain ⟨⟨ρ, hρ, G, hGd, hGi, hGd', hGg⟩, R, hR, F, hFd, hFi, hFd', hFg⟩ := d2l_ext hκ hκD ha has haL haD
  have haB : a ∈ LinfStarBall := by
    show a ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff]
    exact has.trans delta0_bounds.2
  set ν := beltramiMul a (κ : LinfStar) with hν_def
  have hν : ν ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  obtain ⟨hcomp, hinf⟩ := s36l_complement hν
  have hDm : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  -- `F = 𝖿` on `𝔻̄` (both continuous there), hence the complement relation for `(F, G)`
  have hfc : ContinuousOn (fsans ν) (closedBall 0 1) := by
    intro z hz
    rw [S2C.s2c_fsans_eq hν]
    exact (s5e_fB_continuousAt hν (mem_closedBall_zero_iff.mp hz)).continuousWithinAt
  have hFcB : EqOn F (fsans ν) (closedBall 0 1) := by
    refine hFg.of_subset_closure (hFd.continuousOn.mono (closedBall_subset_ball hR)) hfc ball_subset_closedBall ?_
    show closedBall (0 : ℂ) 1 ⊆ closure (ball 0 1)
    rw [closure_ball 0 one_ne_zero]
  have hF0 : F 0 = 0 := (hFg (mem_ball_self one_pos)).trans (s2c_facts hν).2.2.1
  have hc : G '' unitDiscExterior = (F '' closedBall 0 1)ᶜ := by
    rw [hGg.image_eq, hFcB.image_eq]; exact hcomp
  have hGinf : Tendsto G (cocompact ℂ) (cocompact ℂ) := by
    refine hinf.congr' ?_
    filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with w hw
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hw
    exact (hGg hw).symm
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨s, hs, Fh, hFhd, hFhi, hFh0, hFhg, hint, key⟩ :=
    s3fp_gside0 hR hρ hFd hFi hF0 hFd' hGd hGi hGd' hGinf hc
  have hcF : deriv Fh 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hFhd hFhi (mem_ball_self (by linarith))
  obtain ⟨hb, hb0⟩ := s3fp_inf (by linarith) hFhd hFh0 hcF hFhg
  set c := deriv Fh 0 with hcdef
  -- `b = 1/c`, `b₀ = -𝒜(F̂)(0)/(2c)` for `𝗀`
  have hGev' : G =ᶠ[cocompact ℂ] gsans ν := by
    filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with w hw
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hw
    exact hGg hw
  have hbg : derivAtInfty (gsans ν) = 1 / c := by
    show limUnder (cocompact ℂ) (fun z => gsans ν z / z) = 1 / c
    exact (hb.congr' (hGev'.mono fun z hz => by simp only [hz])).limUnder_eq
  have hb0g : limUnder (cocompact ℂ) (fun z => gsans ν z - derivAtInfty (gsans ν) * z) =
      -preSchwarzian Fh 0 / (2 * c) := by
    rw [hbg]
    exact (hb0.congr' (hGev'.mono fun z hz => by simp only [hz])).limUnder_eq
  -- back to `(𝖿, 𝗀)` on `𝔻`, `𝔻*`
  have hpre : ∀ (A B : ℂ → ℂ) (z : ℂ), A =ᶠ[𝓝 z] B →
      preSchwarzian A z = preSchwarzian B z ∧ deriv A z = deriv B z := by
    intro A B z h
    refine ⟨?_, h.deriv_eq⟩
    unfold preSchwarzian
    rw [h.deriv.deriv_eq, h.deriv_eq]
  have hFev : ∀ z ∈ unitDisc, F =ᶠ[𝓝 z] fsans ν := fun z hz => by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hFg hw
  have hGev : ∀ z ∈ unitDiscExterior, G =ᶠ[𝓝 z] gsans ν := fun z hz => by
    filter_upwards [hEo.mem_nhds hz] with w hw
    exact hGg hw
  have e1 : (∫ w in unitDisc, conj (preSchwarzian F w) * (c * deriv F w)) =
      c * ∫ w in unitDisc, conj (preSchwarzian (fsans ν) w) * deriv (fsans ν) w := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hDm fun w hw => ?_
    obtain ⟨h1, h2⟩ := hpre _ _ _ (hFev w hw)
    rw [h1, h2]
    ring
  have e2 : (∫ ω in unitDiscExterior, conj (preSchwarzian G ω) * (c * deriv G ω - 1)) =
      c * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans ν) ω) *
        (deriv (gsans ν) ω - derivAtInfty (gsans ν)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hEo.measurableSet fun ω hω => ?_
    obtain ⟨h1, h2⟩ := hpre _ _ _ (hGev ω hω)
    rw [h1, h2, hbg]
    field_simp
  -- integrability
  have hiF : IntegrableOn (fun z => conj (preSchwarzian (fsans ν) z) * deriv (fsans ν) z) unitDisc := by
    have hcb : closedBall (0 : ℂ) 1 ⊆ ball 0 R := closedBall_subset_ball hR
    have hF1 : DifferentiableOn ℂ (deriv F) (ball 0 R) := (hFd.analyticOnNhd isOpen_ball).deriv.differentiableOn
    have hF2 : DifferentiableOn ℂ (deriv (deriv F)) (ball 0 R) :=
      (hF1.analyticOnNhd isOpen_ball).deriv.differentiableOn
    have hcA : ContinuousOn (preSchwarzian F) (ball 0 R) :=
      hF2.continuousOn.div hF1.continuousOn fun z hz => hFd' z hz
    have hcont : ContinuousOn (fun z => conj (preSchwarzian F z) * deriv F z) (closedBall 0 1) :=
      ((Complex.continuous_conj.comp_continuousOn (hcA.mono hcb)).mul (hF1.continuousOn.mono hcb))
    refine ((hcont.integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall).congr_fun
      (fun z hz => ?_) hDm
    obtain ⟨h1, h2⟩ := hpre _ _ _ (hFev z hz)
    simp only [h1, h2]
  have hiG : IntegrableOn (fun z => conj (preSchwarzian (gsans ν) z) *
      (deriv (gsans ν) z - derivAtInfty (gsans ν))) unitDiscExterior := by
    refine IntegrableOn.congr_fun (hint.const_mul (1 / c)) (fun ω hω => ?_) hEo.measurableSet
    obtain ⟨h1, h2⟩ := hpre _ _ _ (hGev ω hω)
    simp only [h1, h2, hbg]
    field_simp
  refine ⟨hiF, hiG, ?_⟩
  rw [e1, e2] at key
  rw [hb0g]
  field_simp
  field_simp at key
  linear_combination key

/-- (F-I2 helper) Local 2D integrability of `|w - z|⁻¹` (copy of `s4g_int_inv_norm_ball`, which is outside this
file's import closure). -/
theorem s3f_i2_invball (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun w : ℂ => ‖w - z‖⁻¹) (ball z r) := by
  refine ⟨((measurable_id.sub_const z).norm.inv).aestronglyMeasurable, ?_⟩
  show (∫⁻ w in ball z r, ‖‖w - z‖⁻¹‖ₑ) < ∞
  have h := lintegral_ball_sub_enorm_rpow_neg (a := 1) (by norm_num) hr z
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_) (h ▸ ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ENNReal.ofReal_lt_top)
  by_cases hw : w = z
  · subst hw
    simp
  · have hne : ‖w - z‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hw)
    rw [ENNReal.rpow_neg_one, enorm_inv hne, Real.enorm_eq_ofReal (norm_nonneg _), ofReal_norm]

/-- (F-I2 helper) The rational kernel `1/(u²(u²-1))` is integrable on `𝔻*`: `|u ∓ 1|⁻¹` near `±1` (local 2D
integrability, `s3f_i2_invball`) and `(1+|u|)⁻⁴` away from `±1`. -/
theorem s3f_i2_kint : IntegrableOn (fun u : ℂ => 1 / (u ^ 2 * (u ^ 2 - 1))) unitDiscExterior := by
  have hm : Measurable (fun u : ℂ => 1 / (u ^ 2 * (u ^ 2 - 1))) := by fun_prop
  have hnorm : ∀ u : ℂ, ‖1 / (u ^ 2 * (u ^ 2 - 1))‖ = (‖u‖ ^ 2 * ‖u + 1‖)⁻¹ * ‖u - 1‖⁻¹ := fun u => by
    rw [show u ^ 2 - 1 = (u - 1) * (u + 1) by ring]
    simp only [one_div, norm_inv, norm_mul, norm_pow, mul_inv]
    ring
  have hnorm' : ∀ u : ℂ, ‖1 / (u ^ 2 * (u ^ 2 - 1))‖ = (‖u‖ ^ 2 * ‖u - 1‖)⁻¹ * ‖u - -1‖⁻¹ := fun u => by
    rw [hnorm, sub_neg_eq_add]
    simp only [mul_inv]
    ring
  have hcov : unitDiscExterior ⊆ (ball (1 : ℂ) (1 / 2) ∪ ball (-1 : ℂ) (1 / 2)) ∪
      (unitDiscExterior \ (ball (1 : ℂ) (1 / 2) ∪ ball (-1 : ℂ) (1 / 2))) := fun u hu => by
    by_cases h : u ∈ ball (1 : ℂ) (1 / 2) ∪ ball (-1 : ℂ) (1 / 2)
    · exact Or.inl h
    · exact Or.inr ⟨hu, h⟩
  refine IntegrableOn.mono_set ?_ hcov
  refine (IntegrableOn.union ?_ ?_).union ?_
  · refine Integrable.mono' ((s3f_i2_invball (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (8 / 3))
      hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
    have h1 : ‖u - 1‖ < 1 / 2 := by rw [← dist_eq_norm]; exact hu
    have h2 : 1 / 2 ≤ ‖u‖ := by
      have := norm_sub_norm_le (1 : ℂ) u
      rw [norm_one, norm_sub_rev] at this
      linarith
    have h3 : 3 / 2 ≤ ‖u + 1‖ := by
      have := norm_sub_norm_le (2 : ℂ) (-(u - 1))
      rw [norm_neg, show (2 : ℂ) - -(u - 1) = u + 1 by ring, show ‖(2 : ℂ)‖ = 2 by norm_num] at this
      linarith
    rw [hnorm]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  · refine Integrable.mono' ((s3f_i2_invball (-1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (8 / 3))
      hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
    have h1 : ‖u + 1‖ < 1 / 2 := by rw [← sub_neg_eq_add, ← dist_eq_norm]; exact hu
    have h2 : 1 / 2 ≤ ‖u‖ := by
      have := norm_sub_norm_le (-1 : ℂ) (-(u + 1))
      rw [norm_neg, norm_neg, norm_one, show (-1 : ℂ) - -(u + 1) = u by ring] at this
      linarith
    have h3 : 3 / 2 ≤ ‖u - 1‖ := by
      have := norm_sub_norm_le (2 : ℂ) (u + 1)
      rw [show (2 : ℂ) - (u + 1) = -(u - 1) by ring, norm_neg, show ‖(2 : ℂ)‖ = 2 by norm_num] at this
      linarith
    rw [hnorm']
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  · have hfin : (Module.finrank ℝ ℂ : ℝ) < 4 := by rw [Complex.finrank_real_complex]; norm_num
    refine Integrable.mono' (((integrable_one_add_norm (μ := volume) hfin).const_mul 144).integrableOn)
      hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (isOpen_lt continuous_const continuous_norm |>.measurableSet.diff
      (measurableSet_ball.union measurableSet_ball))] with u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hu1' : 1 < ‖u‖ := hu1
    have hb1 : 1 / 2 ≤ ‖u - 1‖ := by
      by_contra h
      exact hu2 (Or.inl (by rw [mem_ball, dist_eq_norm]; linarith))
    have hb2 : 1 / 2 ≤ ‖u + 1‖ := by
      by_contra h
      exact hu2 (Or.inr (by rw [mem_ball, dist_eq_norm, sub_neg_eq_add]; linarith))
    have hd1 : ‖u‖ - 1 ≤ ‖u - 1‖ := by
      have := norm_sub_norm_le u 1
      rwa [norm_one] at this
    have hd2 : ‖u‖ - 1 ≤ ‖u + 1‖ := by
      have := norm_sub_norm_le u (-1)
      rwa [norm_neg, norm_one, sub_neg_eq_add] at this
    have hc1 : (1 + ‖u‖) / 6 ≤ ‖u - 1‖ := by rcases le_or_gt ‖u‖ 2 with h | h <;> linarith
    have hc2 : (1 + ‖u‖) / 6 ≤ ‖u + 1‖ := by rcases le_or_gt ‖u‖ 2 with h | h <;> linarith
    have hc0 : (1 + ‖u‖) / 2 ≤ ‖u‖ := by linarith
    have hP : (1 + ‖u‖) ^ 4 / 144 ≤ ‖u‖ ^ 2 * ‖u - 1‖ * ‖u + 1‖ := by
      calc (1 + ‖u‖) ^ 4 / 144 = ((1 + ‖u‖) / 2) ^ 2 * ((1 + ‖u‖) / 6) * ((1 + ‖u‖) / 6) := by ring
        _ ≤ ‖u‖ ^ 2 * ‖u - 1‖ * ‖u + 1‖ := by gcongr
    have e : ‖1 / (u ^ 2 * (u ^ 2 - 1))‖ = (‖u‖ ^ 2 * ‖u - 1‖ * ‖u + 1‖)⁻¹ := by
      rw [hnorm]
      simp only [mul_inv]
      ring
    rw [e, Real.rpow_neg (by positivity), show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (‖u‖ ^ 2 * ‖u - 1‖ * ‖u + 1‖)⁻¹ ≤ ((1 + ‖u‖) ^ 4 / 144)⁻¹ := inv_anti₀ (by positivity) hP
      _ = 144 * ((1 + ‖u‖) ^ 4)⁻¹ := by field_simp

/-- (F-I2 helper) A series in the Bergman basis `basisF` of `𝔻*` with square-summable coefficients is `O(|u|⁻²)`
on `|u| ≥ 2`. -/
theorem s3f_i2_decay {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    ∃ K : ℝ, ∀ u : ℂ, 2 ≤ ‖u‖ → ‖∑' n, x n * basisF n u‖ ≤ K / ‖u‖ ^ 2 := by
  set S := ∑' n, ‖x n‖ ^ 2 with hS
  have hxn : ∀ n, ‖x n‖ ≤ 1 + S := fun n => by
    have h1 : ‖x n‖ ^ 2 ≤ S := hx.le_tsum n (fun _ _ => sq_nonneg _)
    nlinarith [sq_nonneg (‖x n‖ - 1)]
  have ha : Summable (fun n : ℕ => ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
    refine (h1.add summable_geometric_two).congr fun n => ?_
    simp only [pow_one]
    ring
  refine ⟨(1 + S) * ∑' n : ℕ, ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n, fun u hu => ?_⟩
  have hu0 : 0 < ‖u‖ := by linarith
  have hterm : ∀ n : ℕ, ‖x n * basisF n u‖ ≤ (1 + S) / ‖u‖ ^ 2 * (((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) := by
    intro n
    have hsq : Real.sqrt (((n : ℝ) + 1) / π) ≤ (n : ℝ) + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      have : ((n : ℝ) + 1) / π ≤ (n : ℝ) + 1 := div_le_self (by positivity) (by linarith [Real.pi_gt_three])
      nlinarith
    have hz : ‖u ^ (-(n : ℤ) - 2)‖ ≤ (1 / 2 : ℝ) ^ n / ‖u‖ ^ 2 := by
      rw [norm_zpow, show (-(n : ℤ) - 2) = -((n + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, pow_add]
      have h2n : (2 : ℝ) ^ n ≤ ‖u‖ ^ n := pow_le_pow_left₀ (by norm_num) hu n
      rw [div_eq_mul_inv, one_div, inv_pow, ← mul_inv]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right h2n (by positivity))
    unfold basisF
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    calc ‖x n‖ * (Real.sqrt (((n : ℝ) + 1) / π) * ‖u ^ (-(n : ℤ) - 2)‖)
        ≤ (1 + S) * (((n : ℝ) + 1) * ((1 / 2 : ℝ) ^ n / ‖u‖ ^ 2)) := by
          gcongr
          exact hxn n
      _ = (1 + S) / ‖u‖ ^ 2 * (((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) := by ring
  have hs : Summable (fun n => ‖x n * basisF n u‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (ha.mul_left _)
  calc ‖∑' n, x n * basisF n u‖ ≤ ∑' n, ‖x n * basisF n u‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, (1 + S) / ‖u‖ ^ 2 * (((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) :=
        Summable.tsum_le_tsum hterm hs (ha.mul_left _)
    _ = (1 + S) * (∑' n : ℕ, ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) / ‖u‖ ^ 2 := by
        rw [tsum_mul_left]
        ring

/-- (F-I2 helper) If `V ∈ L²(𝔻*)` and `|V| ≤ K|u|⁻²` on `|u| ≥ 2`, then `V/u` is integrable on `𝔻*`. -/
theorem s3f_i2_vu {V : ℂ → ℂ} (hV : MemLp V 2 (volume.restrict unitDiscExterior)) {K : ℝ}
    (hK : ∀ u : ℂ, 2 ≤ ‖u‖ → ‖V u‖ ≤ K / ‖u‖ ^ 2) :
    IntegrableOn (fun u => V u / u) unitDiscExterior := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have haes : AEStronglyMeasurable (fun u => V u / u) (volume.restrict unitDiscExterior) :=
    hV.aestronglyMeasurable.mul (measurable_inv.aestronglyMeasurable) |>.congr (Eventually.of_forall fun u => by simp [div_eq_mul_inv])
  have hcov : unitDiscExterior ⊆ (unitDiscExterior ∩ ball (0 : ℂ) 2) ∪ (unitDiscExterior \ ball (0 : ℂ) 2) :=
    fun u hu => by
      by_cases h : u ∈ ball (0 : ℂ) 2
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hu, h⟩
  refine IntegrableOn.mono_set (IntegrableOn.union ?_ ?_) hcov
  · haveI : IsFiniteMeasure (volume.restrict (unitDiscExterior ∩ ball (0 : ℂ) 2)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono inter_subset_right).trans_lt measure_ball_lt_top⟩
    have h2 : MemLp V 2 (volume.restrict (unitDiscExterior ∩ ball (0 : ℂ) 2)) := hV.mono_measure
      (Measure.restrict_mono inter_subset_left le_rfl)
    refine Integrable.mono' (h2.integrable one_le_two).norm
      (haes.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)) ?_
    filter_upwards [ae_restrict_mem (hEm.inter measurableSet_ball)] with u hu
    have h1 : 1 < ‖u‖ := hu.1
    rw [norm_div]
    exact div_le_self (norm_nonneg _) h1.le
  · have hfin : (Module.finrank ℝ ℂ : ℝ) < 3 := by rw [Complex.finrank_real_complex]; norm_num
    refine Integrable.mono' (((integrable_one_add_norm (μ := volume) hfin).const_mul (27 / 8 * max K 0)).integrableOn)
      (haes.mono_measure (Measure.restrict_mono diff_subset le_rfl)) ?_
    filter_upwards [ae_restrict_mem (hEm.diff measurableSet_ball)] with u hu
    have h2 : 2 ≤ ‖u‖ := by
      have := hu.2
      rw [mem_ball_zero_iff, not_lt] at this
      exact this
    have hu0 : 0 < ‖u‖ := by linarith
    have hV' : ‖V u‖ ≤ max K 0 / ‖u‖ ^ 2 :=
      (hK u h2).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    rw [norm_div, Real.rpow_neg (by positivity), show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h3 : 8 / 27 * (1 + ‖u‖) ^ 3 ≤ ‖u‖ ^ 3 := by
      calc 8 / 27 * (1 + ‖u‖) ^ 3 ≤ 8 / 27 * (3 / 2 * ‖u‖) ^ 3 := by gcongr; linarith
        _ = ‖u‖ ^ 3 := by ring
    calc ‖V u‖ / ‖u‖ ≤ max K 0 / ‖u‖ ^ 2 / ‖u‖ := div_le_div_of_nonneg_right hV' hu0.le
      _ = max K 0 * (‖u‖ ^ 3)⁻¹ := by field_simp
      _ ≤ max K 0 * (27 / 8 * ((1 + ‖u‖) ^ 3)⁻¹) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
          calc (‖u‖ ^ 3)⁻¹ ≤ (8 / 27 * (1 + ‖u‖) ^ 3)⁻¹ := inv_anti₀ (by positivity) h3
            _ = 27 / 8 * ((1 + ‖u‖) ^ 3)⁻¹ := by rw [mul_inv]; norm_num
      _ = 27 / 8 * max K 0 * ((1 + ‖u‖) ^ 3)⁻¹ := by ring
/-- **(F-I2)** The non-pole `β` part (TT's `I₂`): substituting `ζ = 1/ū` in the `t̄` integral,
`(1/π)∫ R (g'²/g² - (ζ+i)/Dn) - conj((1/π)∫_𝔻 R̃ (ζ+i)/Dn) = (1/π)∫ R (g'²/g² - 1/ζ²)`. -/
theorem s3f_I2 {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    IntegrableOn (fun u => RnmFun (toLinf m) a u * (deriv (gsans (beltramiMul a κ)) u ^ 2 / gsans (beltramiMul a κ) u ^ 2 - 1 / u ^ 2)) unitDiscExterior ∧
      (1 / π : ℂ) * (∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / gsans (beltramiMul a κ) ζ ^ 2 - (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) -
          conj ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1))) =
        (1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * (deriv (gsans (beltramiMul a κ)) u ^ 2 / gsans (beltramiMul a κ) u ^ 2 - 1 / u ^ 2) := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hd := delta0_bounds
  have ha1 : a ∈ LinfStarBall := mem_ball_zero_iff.mpr (has.trans hd.2)
  have hν' : beltramiMul a (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 ha1
  set g := gsans (beltramiMul a κ) with hgdef
  set f := fsans (beltramiMul a κ) with hfdef
  set R := RnmFun (toLinf m) a with hRdef
  obtain ⟨hpair, hnull, -, -⟩ := mg_remark_2_2 hν'
  have hs2 := (r22_sum hpair hnull).2.1
  -- the Grunsky series of `v = g'/g - 1/u`
  set x : ℕ → ℂ := fun n => -(Real.sqrt (π * ((n : ℝ) + 1)) : ℂ) * grunsky f g ((n : ℤ) + 1) 0 with hxdef
  have hx : Summable (fun n => ‖x n‖ ^ 2) := by
    refine (hs2.mul_left π).congr fun n => ?_
    simp only [hxdef, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ π * ((n : ℝ) + 1))]
    push_cast
    ring
  have hser : ∀ w ∈ unitDiscExterior, HasSum (fun n => x n * basisF n w) (-(deriv g w / g w - 1 / w)) :=
    fun w hw => s310_w2_series hpair hw
  obtain ⟨hVA, hVae⟩ := s310_ae_seriesF hx (E := ∅) measure_empty (fun u hu _ => hser u hu)
  have hVL2 := ((mem_A21fun_iff_memLp hEm).1 hVA).2
  have hv2 : MemLp (fun u => deriv g u / g u - 1 / u) 2 (volume.restrict unitDiscExterior) := by
    refine hVL2.neg.ae_eq ?_
    filter_upwards [hVae] with u hu
    simp only [Pi.neg_apply]
    rw [← hu, neg_neg]
  obtain ⟨K, hK⟩ := s3f_i2_decay hx
  have hK' : ∀ u : ℂ, 2 ≤ ‖u‖ → ‖deriv g u / g u - 1 / u‖ ≤ K / ‖u‖ ^ 2 := by
    intro u hu
    have hu' : u ∈ unitDiscExterior := show 1 < ‖u‖ by linarith
    rw [← norm_neg, ← (hser u hu').tsum_eq]
    exact hK u hu
  have hvu := s3f_i2_vu hv2 hK'
  have hvsq : IntegrableOn (fun u => (deriv g u / g u - 1 / u) ^ 2) unitDiscExterior := by
    refine Integrable.mono' ((memLp_two_iff_integrable_sq_norm hv2.aestronglyMeasurable).1 hv2)
      (hv2.aestronglyMeasurable.pow 2) (Eventually.of_forall fun u => ?_)
    rw [norm_pow]
  have hG : IntegrableOn (fun u => deriv g u ^ 2 / g u ^ 2 - 1 / u ^ 2) unitDiscExterior := by
    refine (hvsq.add (hvu.const_mul 2)).congr ?_
    filter_upwards [ae_restrict_mem hEm] with u hu
    have hu0 : u ≠ 0 := by
      intro h
      have : (1 : ℝ) < ‖u‖ := hu
      rw [h, norm_zero] at this
      linarith
    simp only [Pi.add_apply]
    rw [← div_pow]
    field_simp
    ring
  -- `R` is essentially bounded and measurable on `𝔻*`
  have hRae : (⇑(Rnm (toLinf m) a) : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] R := bc_Rnm_ae ha1 (toLinf m)
  have hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior) :=
    (Lp.aestronglyMeasurable (Rnm (toLinf m) a)).congr hRae
  have hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ ‖Rnm (toLinf m) a‖ := by
    filter_upwards [hRae, LinfStar_ae_norm_le (Rnm (toLinf m) a)] with u h1 h2
    rw [← h1]
    exact h2
  have hI1 : IntegrableOn (fun u => R u * (deriv g u ^ 2 / g u ^ 2 - 1 / u ^ 2)) unitDiscExterior :=
    Integrable.bdd_mul hG hRm hRb
  have hI2 : IntegrableOn (fun u => R u * (1 / (u ^ 2 * (u ^ 2 - 1)))) unitDiscExterior :=
    Integrable.bdd_mul s3f_i2_kint hRm hRb
  refine ⟨hI1, ?_⟩
  -- the first integral
  have hne : ∀ u ∈ unitDiscExterior, u ≠ 0 ∧ u - 1 ≠ 0 ∧ u + 1 ≠ 0 ∧ u + I ≠ 0 := by
    intro u hu
    have h1 : (1 : ℝ) < ‖u‖ := hu
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [h, norm_zero] at h1; linarith
    · rw [sub_eq_zero.1 h, norm_one] at h1; linarith
    · rw [eq_neg_of_add_eq_zero_left h, norm_neg, norm_one] at h1; linarith
    · rw [eq_neg_of_add_eq_zero_left h, norm_neg, Complex.norm_I] at h1; linarith
  have e1 : (∫ ζ in unitDiscExterior, R ζ * (deriv g ζ ^ 2 / g ζ ^ 2 - (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) =
      (∫ u in unitDiscExterior, R u * (deriv g u ^ 2 / g u ^ 2 - 1 / u ^ 2)) -
        ∫ u in unitDiscExterior, R u * (1 / (u ^ 2 * (u ^ 2 - 1))) := by
    rw [← integral_sub hI1 hI2]
    refine setIntegral_congr_fun hEm fun u hu => ?_
    obtain ⟨h0, h1, h2, h3⟩ := hne u hu
    have h4 : u ^ 2 - 1 ≠ 0 := by
      rw [show u ^ 2 - 1 = (u - 1) * (u + 1) by ring]
      exact mul_ne_zero h1 h2
    field_simp
    ring
  -- the second integral, by `ζ = 1/ū`
  have e2 : conj (∫ ζ in unitDisc, conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (ζ + I) /
      ((ζ + 1) * (ζ + I) * (ζ - 1))) = -∫ u in unitDiscExterior, R u * (1 / (u ^ 2 * (u ^ 2 - 1))) := by
    rw [s310_disc_punct]
    have hrefl := s2c_refl_integral (fun v => (‖v‖ ^ 4)⁻¹ • (conj (R (1 / conj (refl v))) * refl v ^ 2 /
      conj (refl v) ^ 2 * (refl v + I) / ((refl v + 1) * (refl v + I) * (refl v - 1))))
    beta_reduce at hrefl
    have hpt : ∀ u ∈ unitDisc \ {0}, (‖u‖ ^ 4)⁻¹ • ((‖refl u‖ ^ 4)⁻¹ • (conj (R (1 / conj (refl (refl u)))) *
        refl (refl u) ^ 2 / conj (refl (refl u)) ^ 2 * (refl (refl u) + I) /
          ((refl (refl u) + 1) * (refl (refl u) + I) * (refl (refl u) - 1)))) =
        conj (R (1 / conj u)) * u ^ 2 / conj u ^ 2 * (u + I) / ((u + 1) * (u + I) * (u - 1)) := by
      intro u hu
      have hu0 : u ≠ 0 := hu.2
      have hrr : refl (refl u) = u := by simp [refl]
      have hnr : ‖refl u‖ = ‖u‖⁻¹ := by simp [refl]
      rw [hrr, hnr, smul_smul, inv_pow, inv_inv, inv_mul_cancel₀ (by positivity), one_smul]
    rw [show (∫ u in unitDisc \ {0}, conj (R (1 / conj u)) * u ^ 2 / conj u ^ 2 * (u + I) /
        ((u + 1) * (u + I) * (u - 1))) = ∫ u in unitDisc \ {0}, (‖u‖ ^ 4)⁻¹ • ((‖refl u‖ ^ 4)⁻¹ •
          (conj (R (1 / conj (refl (refl u)))) * refl (refl u) ^ 2 / conj (refl (refl u)) ^ 2 *
            (refl (refl u) + I) / ((refl (refl u) + 1) * (refl (refl u) + I) * (refl (refl u) - 1)))) from
      (setIntegral_congr_fun (measurableSet_ball.diff (measurableSet_singleton 0)) hpt).symm,
      ← hrefl, ← integral_conj, ← integral_neg]
    refine setIntegral_congr_fun hEm fun v hv => ?_
    obtain ⟨h0, h1, h2, -⟩ := hne v hv
    have hv1 : (1 : ℝ) < ‖v‖ := hv
    have hrv : refl v = (conj v)⁻¹ := rfl
    have hcv : conj v ≠ 0 := (map_ne_zero _).2 h0
    have hz1 : (conj v)⁻¹ + I ≠ 0 := by
      intro h
      have := congrArg norm (eq_neg_of_add_eq_zero_left h)
      rw [norm_neg, Complex.norm_I, norm_inv, Complex.norm_conj] at this
      have : ‖v‖ = 1 := by rw [← inv_inv ‖v‖, this, inv_one]
      linarith
    have hz2 : (conj v)⁻¹ + 1 ≠ 0 := by
      intro h
      have := congrArg norm (eq_neg_of_add_eq_zero_left h)
      rw [norm_neg, norm_one, norm_inv, Complex.norm_conj] at this
      have : ‖v‖ = 1 := by rw [← inv_inv ‖v‖, this, inv_one]
      linarith
    have hz3 : (conj v)⁻¹ - 1 ≠ 0 := by
      intro h
      have := congrArg norm (sub_eq_zero.1 h)
      rw [norm_one, norm_inv, Complex.norm_conj] at this
      have : ‖v‖ = 1 := by rw [← inv_inv ‖v‖, this, inv_one]
      linarith
    have hw1 : v⁻¹ - I ≠ 0 := by simpa [sub_eq_add_neg] using (map_ne_zero (starRingEnd ℂ)).2 hz1
    have hw2 : v⁻¹ + 1 ≠ 0 := by simpa using (map_ne_zero (starRingEnd ℂ)).2 hz2
    have hw3 : v⁻¹ - 1 ≠ 0 := by simpa using (map_ne_zero (starRingEnd ℂ)).2 hz3
    have h4 : v ^ 2 - 1 ≠ 0 := by
      rw [show v ^ 2 - 1 = (v - 1) * (v + 1) by ring]
      exact mul_ne_zero h1 h2
    have h5 : (1 : ℂ) - v ^ 2 ≠ 0 := by
      rw [← neg_sub]
      exact neg_ne_zero.2 h4
    have hRv : 1 / conj ((conj v)⁻¹) = v := by rw [map_inv₀, Complex.conj_conj, one_div, inv_inv]
    rw [hrv, hRv, Complex.real_smul]
    have hn4 : (((‖v‖ ^ 4)⁻¹ : ℝ) : ℂ) = (v ^ 2 * conj v ^ 2)⁻¹ := by
      push_cast
      rw [s310_norm4]
    have hvI : 1 - v * I ≠ 0 := by
      intro h
      have h' : ‖v * I‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
      rw [norm_mul, Complex.norm_I, mul_one] at h'
      linarith
    have hX : 1 - v * I - v ^ 2 + v ^ 3 * I ≠ 0 := by
      rw [show 1 - v * I - v ^ 2 + v ^ 3 * I = (1 - v ^ 2) * (1 - v * I) by ring]
      exact mul_ne_zero h5 hvI
    rw [hn4]
    simp only [map_mul, map_div₀, map_inv₀, map_pow, map_add, map_sub, map_one, Complex.conj_conj, Complex.conj_I]
    field_simp
    linear_combination (-(R v)) * mul_inv_cancel₀ hX
  rw [e1, map_mul, e2]
  simp only [map_div₀, map_one, Complex.conj_ofReal]
  ring

/-- (F-I4 helper) The kernel `(ζ - r w)⁻³` (`|ζ| < 1 ≤ r`) in the Bergman basis of `𝔻*`:
`(ζ - r w)⁻³ = Σ_j y_j basisF_j(w)`, `y_j = -C(j+1,2) ζ^{j-1} r^{-j-2}/√((j+1)/π)` (`y₀ = 0` as `C(1,2) = 0`). -/
theorem s3f_i4_kexp {ζ : ℂ} (hζ : ζ ∈ unitDisc) {r : ℝ} (hr : 1 ≤ r) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    HasSum (fun j : ℕ => -(((j + 1).choose 2 : ℂ) * ζ ^ (j - 1) * (r : ℂ) ^ (-(j : ℤ) - 2) /
        (Real.sqrt (((j : ℝ) + 1) / π) : ℂ)) * basisF j w) (1 / (ζ - r * w) ^ 3) := by
  have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
  have hw1 : 1 < ‖w‖ := hw
  have hr0 : (0 : ℝ) < r := by linarith
  have hrw : 1 < ‖(r : ℂ) * w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    nlinarith
  have hrw0 : (r : ℂ) * w ≠ 0 := fun h => by rw [h, norm_zero] at hrw; linarith
  have hq : ‖ζ / ((r : ℂ) * w)‖ < 1 := by
    rw [norm_div, div_lt_one (by linarith)]
    linarith
  have hsub : (r : ℂ) * w - ζ ≠ 0 := by
    intro h
    have := congrArg norm (sub_eq_zero.1 h)
    linarith
  have hg := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) 2 hq).mul_left (-(((r : ℂ) * w) ^ 3)⁻¹)
  have hY : (r : ℂ) * w - ζ ≠ 0 := hsub
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw1; linarith
  have hr0' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have hval : -(((r : ℂ) * w) ^ 3)⁻¹ * (1 / (1 - ζ / ((r : ℂ) * w)) ^ (2 + 1)) = 1 / (ζ - r * w) ^ 3 := by
    have h1 : (1 : ℂ) - ζ / ((r : ℂ) * w) = ((r : ℂ) * w - ζ) / ((r : ℂ) * w) := by
      rw [eq_div_iff hrw0, sub_mul, div_mul_cancel₀ _ hrw0, one_mul]
    rw [h1, show (2 : ℕ) + 1 = 3 from rfl, div_pow, one_div_div,
      show ζ - (r : ℂ) * w = -((r : ℂ) * w - ζ) by ring, neg_pow]
    field_simp
  rw [hval] at hg
  rw [← hasSum_nat_add_iff' 1, Finset.sum_range_one]
  simp only [show (0 + 1).choose 2 = 0 from rfl, Nat.cast_zero, zero_mul, neg_zero, zero_div, sub_zero]
  refine hg.congr_fun fun k => ?_
  have hc : ((Real.sqrt ((((k + 1 : ℕ) : ℝ) + 1) / π) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.2 (by positivity)).ne'
  simp only [Nat.add_sub_cancel, basisF]
  rw [show (-((k + 1 : ℕ) : ℤ) - 2) = -((k + 3 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_neg, zpow_natCast,
    zpow_natCast, show k + 1 + 1 = k + 2 by ring]
  push_cast at hc ⊢
  simp only [div_pow, mul_pow]
  field_simp
  ring

/-- (F-I4 helper) Scaling `z = r w` maps `𝔻*` onto `{|z| > r}`: `∫_{|z|>r} f = r² ∫_{𝔻*} f(r w)`. -/
theorem s3f_i4_scale (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ z in {z : ℂ | r < ‖z‖}, f z = (r : ℂ) ^ 2 * ∫ w in unitDiscExterior, f ((r : ℂ) * w) := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hEr : MeasurableSet {z : ℂ | r < ‖z‖} := (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [← integral_indicator hEr, ← integral_indicator hE]
  have h := Measure.integral_comp_smul (μ := (volume : Measure ℂ)) ({z : ℂ | r < ‖z‖}.indicator f) r
  rw [Complex.finrank_real_complex] at h
  have hind : (fun w : ℂ => {z : ℂ | r < ‖z‖}.indicator f (r • w)) = unitDiscExterior.indicator (fun w => f ((r : ℂ) * w)) := by
    funext w
    have hiff : r • w ∈ {z : ℂ | r < ‖z‖} ↔ w ∈ unitDiscExterior := by
      show r < ‖r • w‖ ↔ 1 < ‖w‖
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      constructor
      · intro h; nlinarith
      · intro h; nlinarith
    by_cases hw : w ∈ unitDiscExterior
    · rw [indicator_of_mem (hiff.2 hw), indicator_of_mem hw, Complex.real_smul]
    · rw [indicator_of_notMem (fun h => hw (hiff.1 h)), indicator_of_notMem hw]
  rw [hind] at h
  have hr0' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  rw [h, Complex.real_smul]
  simp only [abs_inv, abs_pow, abs_of_pos hr]
  push_cast
  field_simp

/-- (F-I4 helper) `|w|⁻³ ∈ L²(𝔻*)`. -/
theorem s3f_i4_inv3 : MemLp (fun w : ℂ => (((‖w‖ ^ 3)⁻¹ : ℝ) : ℂ)) 2 (volume.restrict unitDiscExterior) := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hm : AEStronglyMeasurable (fun w : ℂ => (((‖w‖ ^ 3)⁻¹ : ℝ) : ℂ)) (volume.restrict unitDiscExterior) :=
    (Complex.continuous_ofReal.comp_continuousOn ((continuous_norm.pow 3).continuousOn.inv₀
      (fun y hy => pow_ne_zero 3 (lt_trans one_pos hy).ne'))).aestronglyMeasurable hO.measurableSet
  refine (memLp_two_iff_integrable_sq_norm hm).2 ((d2l_powint (k := 6) (by norm_num)).congr ?_)
  filter_upwards with w
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, ← pow_mul]

/-- (F-I4 helper) Membership in `A₂¹(𝔻*)` from holomorphy and an `O(|w|⁻³)` bound. -/
theorem s3f_i4_A21 {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDiscExterior) {C : ℝ}
    (hC : ∀ w ∈ unitDiscExterior, ‖F w‖ ≤ C * (‖w‖ ^ 3)⁻¹) : F ∈ A21fun unitDiscExterior := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  refine (mem_A21fun_iff_memLp hO.measurableSet).2 ⟨hF, ?_⟩
  refine (s3f_i4_inv3.const_mul ((max C 0 : ℝ) : ℂ)).of_le (hF.continuousOn.aestronglyMeasurable hO.measurableSet) ?_
  filter_upwards [ae_restrict_mem hO.measurableSet] with w hw
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (le_max_right _ _),
    Real.norm_of_nonneg (by positivity)]
  exact (hC w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-- (F-I4 helper) Termwise derivative of a `basisF`-series with `ℓ²` coefficients at a point of `𝔻*`. -/
theorem s3f_i4_dser {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) {F : ℂ → ℂ}
    (hF : ∀ w ∈ unitDiscExterior, HasSum (fun n => x n * basisF n w) (F w)) {w₀ : ℂ}
    (hw₀ : w₀ ∈ unitDiscExterior) :
    HasDerivAt F (∑' n, x n * ((Real.sqrt (((n : ℝ) + 1) / π) : ℂ) * (-((n : ℂ) + 2)) * w₀ ^ (-(n : ℤ) - 3))) w₀ := by
  have hw1 : 1 < ‖w₀‖ := hw₀
  set ρ := (1 + ‖w₀‖) / 2 with hρ
  have hρ1 : 1 < ρ := by rw [hρ]; linarith
  set t := ball w₀ (‖w₀‖ - ρ) with ht
  have htE : ∀ w ∈ t, ρ < ‖w‖ := fun w hw => by
    have := norm_sub_norm_le w₀ w
    rw [mem_ball, dist_eq_norm, norm_sub_rev] at hw
    linarith
  set S := ∑' n, ‖x n‖ ^ 2 with hS
  have hxn : ∀ n, ‖x n‖ ≤ 1 + S := fun n => by
    have h1 : ‖x n‖ ^ 2 ≤ S := hx.le_tsum n (fun _ _ => sq_nonneg _)
    nlinarith [sq_nonneg (‖x n‖ - 1)]
  -- the derivative bound `|x_n| √((n+1)/π) (n+2) ρ^{-n-3} ≤ (1+S) (n+2)² ρ⁻ⁿ`
  have hu : Summable (fun n : ℕ => (1 + S) * (((n : ℝ) + 2) ^ 2 * (ρ⁻¹) ^ n)) := by
    have hq : ‖ρ⁻¹‖ < 1 := by
      rw [Real.norm_of_nonneg (by positivity), inv_lt_one₀ (by linarith)]
      exact hρ1
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hq
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
    have h0 := summable_geometric_of_lt_one (by positivity) (show ρ⁻¹ < 1 by rwa [Real.norm_of_nonneg (by positivity)] at hq)
    refine (((h2.add (h1.mul_left 4)).add (h0.mul_left 4)).mul_left (1 + S)).congr fun n => ?_
    simp only [pow_one]
    ring
  have hderiv : ∀ n w, w ∈ t → HasDerivAt (fun w => x n * basisF n w)
      (x n * ((Real.sqrt (((n : ℝ) + 1) / π) : ℂ) * (-((n : ℂ) + 2)) * w ^ (-(n : ℤ) - 3))) w := by
    intro n w hw
    have hw0 : w ≠ 0 := fun h => by have := htE w hw; rw [h, norm_zero] at this; linarith
    have h := (hasDerivAt_zpow (-(n : ℤ) - 2) w (Or.inl hw0)).const_mul
      ((Real.sqrt (((n : ℝ) + 1) / π) : ℂ))
    have h' := h.const_mul (x n)
    have e : (fun w => x n * basisF n w) =
        fun y => x n * ((Real.sqrt (((n : ℝ) + 1) / π) : ℂ) * y ^ (-(n : ℤ) - 2)) := by
      funext y
      simp only [basisF]
    rw [e]
    convert h' using 1
    rw [show (-(n : ℤ) - 2 - 1) = -(n : ℤ) - 3 by ring]
    push_cast
    ring
  have hbound : ∀ n w, w ∈ t → ‖x n * ((Real.sqrt (((n : ℝ) + 1) / π) : ℂ) * (-((n : ℂ) + 2)) *
      w ^ (-(n : ℤ) - 3))‖ ≤ (1 + S) * (((n : ℝ) + 2) ^ 2 * (ρ⁻¹) ^ n) := by
    intro n w hw
    have hwρ := htE w hw
    have hρ0 : 0 < ρ := by linarith
    have hsq : Real.sqrt (((n : ℝ) + 1) / π) ≤ (n : ℝ) + 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      have : ((n : ℝ) + 1) / π ≤ (n : ℝ) + 1 := div_le_self (by positivity) (by linarith [Real.pi_gt_three])
      nlinarith
    have hz : ‖w ^ (-(n : ℤ) - 3)‖ ≤ (ρ⁻¹) ^ n := by
      rw [norm_zpow, show (-(n : ℤ) - 3) = -((n + 3 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]
      refine inv_anti₀ (by positivity) ?_
      calc ρ ^ n ≤ ‖w‖ ^ n := pow_le_pow_left₀ hρ0.le hwρ.le n
        _ ≤ ‖w‖ ^ (n + 3) := pow_le_pow_right₀ (by linarith) (by omega)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_neg,
      show ‖(n : ℂ) + 2‖ = (n : ℝ) + 2 by norm_cast]
    calc ‖x n‖ * (Real.sqrt (((n : ℝ) + 1) / π) * ((n : ℝ) + 2) * ‖w ^ (-(n : ℤ) - 3)‖)
        ≤ (1 + S) * (((n : ℝ) + 2) * ((n : ℝ) + 2) * (ρ⁻¹) ^ n) := by
          gcongr
          exact hxn n
      _ = (1 + S) * (((n : ℝ) + 2) ^ 2 * (ρ⁻¹) ^ n) := by ring
  have hw₀t : w₀ ∈ t := mem_ball_self (by linarith)
  have hsum := hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball _ _).isPreconnected hderiv hbound hw₀t
    (hF w₀ hw₀).summable hw₀t
  have heq : (fun w => ∑' n, x n * basisF n w) =ᶠ[𝓝 w₀] F := by
    filter_upwards [isOpen_ball.mem_nhds hw₀t] with w hw
    exact (hF w (show 1 < ‖w‖ by linarith [htE w hw])).tsum_eq
  exact hsum.congr_of_eventuallyEq heq.symm

/-- (F-I4 helper) The `𝔻*`-mode computation: for `A = Σ x_n basisF_n` on `𝔻*` with `|A| ≤ C|w|⁻³`, `0 < |ζ| < 1 ≤ r`,
`(2/π)∫_{|z|>r} A(z) conj((ζ - z)⁻³) = r⁴ ζ̄⁻⁴ (A' + 2A/u)(r²/ζ̄)` (scaling, the kernel modes, Parseval in `A₂¹(𝔻*)`). -/
theorem s3f_i4_core {A : ℂ → ℂ} {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2))
    (hA : ∀ w ∈ unitDiscExterior, HasSum (fun n => x n * basisF n w) (A w))
    (hAd : DifferentiableOn ℂ A unitDiscExterior) {C : ℝ}
    (hC : ∀ w ∈ unitDiscExterior, ‖A w‖ ≤ C * (‖w‖ ^ 3)⁻¹)
    {ζ : ℂ} (hζ : ζ ∈ unitDisc) (hζ0 : ζ ≠ 0) {r : ℝ} (hr : 1 ≤ r) :
    (2 / π : ℂ) * (∫ z in {z : ℂ | r < ‖z‖}, A z * conj (1 / (ζ - z) ^ 3)) =
      (r : ℂ) ^ 4 * ((conj ζ)⁻¹) ^ 4 * (deriv A ((r : ℂ) ^ 2 / conj ζ) +
        2 * A ((r : ℂ) ^ 2 / conj ζ) / ((r : ℂ) ^ 2 / conj ζ)) := by
  have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
  have hr0 : (0 : ℝ) < r := by linarith
  have hr0' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have hcz : conj ζ ≠ 0 := (map_ne_zero _).2 hζ0
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hrw : ∀ w ∈ unitDiscExterior, (r : ℂ) * w ∈ unitDiscExterior := fun w hw => by
    show 1 < ‖(r : ℂ) * w‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    have : 1 < ‖w‖ := hw
    nlinarith
  -- `A(r ·)` and the kernel `(ζ - r ·)⁻³` lie in `A₂¹(𝔻*)`, with explicit modes
  have hF : (fun w => A ((r : ℂ) * w)) ∈ A21fun unitDiscExterior := by
    refine s3f_i4_A21 (F := fun w => A ((r : ℂ) * w)) (C := max C 0)
      (hAd.comp ((differentiable_const (r : ℂ)).mul differentiable_id).differentiableOn hrw) ?_
    intro w hw
    have hw1 : 1 < ‖w‖ := hw
    refine (hC _ (hrw w hw)).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    calc C * ((r * ‖w‖) ^ 3)⁻¹ ≤ max C 0 * ((r * ‖w‖) ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * (‖w‖ ^ 3)⁻¹ := by
        refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) (le_max_right _ _)
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) 3
  have hFx : ∀ w ∈ unitDiscExterior,
      HasSum (fun n => x n * (r : ℂ) ^ (-(n : ℤ) - 2) * basisF n w) (A ((r : ℂ) * w)) := by
    intro w hw
    convert hA _ (hrw w hw) using 1
    funext n
    simp only [basisF]
    rw [mul_zpow]
    ring
  have hne : ∀ w ∈ unitDiscExterior, ζ - (r : ℂ) * w ≠ 0 := fun w hw h => by
    have h1 : 1 < ‖(r : ℂ) * w‖ := hrw w hw
    rw [← sub_eq_zero.1 h] at h1
    linarith
  have hG : (fun w : ℂ => 1 / (ζ - r * w) ^ 3) ∈ A21fun unitDiscExterior := by
    refine s3f_i4_A21 (C := ((1 - ‖ζ‖) ^ 3)⁻¹)
      ((differentiableOn_const (1 : ℂ)).div (((differentiableOn_const ζ).sub
        ((differentiableOn_const (r : ℂ)).mul differentiableOn_id)).pow 3) fun w hw => pow_ne_zero 3 (hne w hw)) ?_
    intro w hw
    have hw1 : 1 < ‖w‖ := hw
    have hlow : (1 - ‖ζ‖) * ‖w‖ ≤ ‖ζ - (r : ℂ) * w‖ := by
      have := norm_sub_norm_le ((r : ℂ) * w) ζ
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_sub_rev] at this
      nlinarith [mul_nonneg (sub_nonneg.2 hr) (norm_nonneg w), mul_nonneg (norm_nonneg ζ) (sub_nonneg.2 hw1.le)]
    have hpos : 0 < (1 - ‖ζ‖) * ‖w‖ := by
      have : 0 < 1 - ‖ζ‖ := by linarith
      positivity
    rw [norm_div, norm_one, norm_pow, one_div, ← mul_inv, ← mul_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hlow 3)
  have hP := A21_basisF_pairing hF hG hFx (fun w hw => s3f_i4_kexp hζ hr hw)
  have hs := s3f_i4_scale (fun z => A z * conj (1 / (ζ - z) ^ 3)) hr0
  rw [hs]
  -- the evaluation point `u₀ = r²/ζ̄ ∈ 𝔻*`
  set u₀ := (r : ℂ) ^ 2 / conj ζ with hu₀
  have hu₀E : u₀ ∈ unitDiscExterior := by
    show 1 < ‖u₀‖
    rw [hu₀, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le, Complex.norm_conj,
      lt_div_iff₀ (norm_pos_iff.2 hζ0)]
    nlinarith
  have hu₀0 : u₀ ≠ 0 := div_ne_zero (pow_ne_zero 2 hr0') hcz
  rw [(s3f_i4_dser hx hA hu₀E).deriv]
  set k : ℂ := (r : ℂ) ^ 4 * ((conj ζ)⁻¹) ^ 4 with hk
  have hQ := hP.mul_left ((2 / π : ℂ) * (r : ℂ) ^ 2)
  have hB := (hA u₀ hu₀E).mul_left (k * 2 / u₀)
  -- termwise: `(2/π) r² x_n r^{-n-2} conj y_n = k (x_n basisF_n'(u₀) + 2 x_n basisF_n(u₀)/u₀)`
  have hD : HasSum (fun n => k * (x n * ((Real.sqrt (((n : ℝ) + 1) / π) : ℂ) * (-((n : ℂ) + 2)) *
      u₀ ^ (-(n : ℤ) - 3))))
      ((2 / π : ℂ) * (r : ℂ) ^ 2 * (∫ w in unitDiscExterior, A ((r : ℂ) * w) * conj (1 / (ζ - (r : ℂ) * w) ^ 3)) -
        k * 2 / u₀ * A u₀) := by
    refine (hQ.sub hB).congr_fun fun n => ?_
    beta_reduce
    rcases n with _ | j
    · simp only [show ((0 : ℕ) + 1).choose 2 = 0 from rfl, basisF, Nat.cast_zero, zero_mul, zero_div, neg_zero, map_zero, mul_zero, zero_sub, zero_add,
        zpow_neg, zpow_ofNat]
      field_simp
    · simp only [basisF]
      rw [show (-((j + 1 : ℕ) : ℤ) - 2) = -((j + 3 : ℕ) : ℤ) by push_cast; ring,
        show (-((j + 1 : ℕ) : ℤ) - 3) = -((j + 4 : ℕ) : ℤ) by push_cast; ring]
      set s : ℂ := ((Real.sqrt ((((j + 1 : ℕ) : ℝ) + 1) / π) : ℝ) : ℂ) with hs
      have hs0 : s ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne'
      have hj : ((j : ℂ) + 2) ≠ 0 := by norm_cast
      have hcs : s ^ 2 * (π : ℂ) = (j : ℂ) + 2 := by
        rw [hs, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
        push_cast
        field_simp
        ring
      have hinv : s⁻¹ = s * ((π : ℂ) / ((j : ℂ) + 2)) := by
        rw [← hcs]
        field_simp
      simp only [map_neg, map_mul, map_pow, map_inv₀, Complex.conj_ofReal, map_natCast, zpow_neg,
        zpow_natCast, Nat.add_sub_cancel, div_eq_mul_inv]
      have hsc : conj s = s := by rw [hs, Complex.conj_ofReal]
      rw [hsc, hinv, hu₀, hk, Nat.cast_choose_two]
      push_cast
      generalize (starRingEnd ℂ) ζ = c at hcz ⊢
      simp only [div_pow, inv_div, pow_add, mul_pow, inv_pow]
      have hcj : c ^ j ≠ 0 := pow_ne_zero _ hcz
      have hrj : (r : ℂ) ^ j ≠ 0 := pow_ne_zero _ hr0'
      generalize c ^ j = P at hcj ⊢
      rw [show ((r : ℂ) ^ 2) ^ j = (r : ℂ) ^ j * (r : ℂ) ^ j by ring]
      generalize (r : ℂ) ^ j = Q at hrj ⊢
      field_simp
      ring
  have h1 := hD.tsum_eq
  rw [tsum_mul_left] at h1
  rw [mul_add, h1]
  ring

/-- (F-I4 helper) The reflection `u = 1/ζ̄` turns the `𝔻`-side representation into an `𝔻*` integral against `R`. -/
theorem s3f_i4_refl (R K : ℂ → ℂ) (r : ℝ) :
    ∫ ζ in unitDisc, conj (conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2) *
        ((r : ℂ) ^ 4 * ((conj ζ)⁻¹) ^ 4 * K ((r : ℂ) ^ 2 / conj ζ)) =
      ∫ u in unitDiscExterior, R u * ((r : ℂ) ^ 4 * K ((r : ℂ) ^ 2 * u)) := by
  rw [s310_disc_punct, s2c_refl_integral]
  beta_reduce
  refine setIntegral_congr_fun (measurableSet_ball.diff (measurableSet_singleton 0)) fun u hu => ?_
  have hu0 : u ≠ 0 := hu.2
  have hcu : conj u ≠ 0 := (map_ne_zero _).2 hu0
  have hrefl : refl u = (conj u)⁻¹ := rfl
  have hn4 : (((‖u‖ ^ 4)⁻¹ : ℝ) : ℂ) = (u ^ 2 * conj u ^ 2)⁻¹ := by
    push_cast
    rw [s310_norm4]
  rw [hrefl, Complex.real_smul, hn4, one_div, div_eq_mul_inv ((r : ℂ) ^ 2) (conj u)]
  generalize K ((r : ℂ) ^ 2 * (conj u)⁻¹) = κ
  generalize R (conj u)⁻¹ = ρ
  simp only [map_div₀, map_mul, map_pow, Complex.conj_conj]
  field_simp

/-- (F-I4 helper) Integrability on `{|z| > r} × 𝔻` of the Fubini integrand (`r > 1`). -/
theorem s3f_i4_fub_int {A S : ℂ → ℂ} (hAc : ContinuousOn A unitDiscExterior) {CA : ℝ} (hCA : 0 ≤ CA)
    (hAb : ∀ w ∈ unitDiscExterior, ‖A w‖ ≤ CA * (‖w‖ ^ 3)⁻¹) {Sb : ℝ}
    (hSm : AEStronglyMeasurable S (volume.restrict unitDisc))
    (hSb : ∀ᵐ ζ ∂(volume.restrict unitDisc), ‖S ζ‖ ≤ Sb) {r : ℝ} (hr : 1 < r) :
    Integrable (fun p : ℂ × ℂ => conj (S p.2) * ((2 / π : ℂ) * (A p.1 * conj (1 / (p.2 - p.1) ^ 3))))
      ((volume.restrict {z : ℂ | r < ‖z‖}).prod (volume.restrict unitDisc)) := by
  have hEr : MeasurableSet {z : ℂ | r < ‖z‖} := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hsub : {z : ℂ | r < ‖z‖} ⊆ unitDiscExterior := fun z hz => by
    show 1 < ‖z‖
    exact hr.trans hz
  have hAm : AEStronglyMeasurable A (volume.restrict {z : ℂ | r < ‖z‖}) :=
    (hAc.mono hsub).aestronglyMeasurable hEr
  have hkm : Measurable (fun p : ℂ × ℂ => conj (1 / (p.2 - p.1) ^ 3)) :=
    Complex.continuous_conj.measurable.comp (measurable_const.div ((measurable_snd.sub measurable_fst).pow_const 3))
  have m1 : AEStronglyMeasurable (fun p : ℂ × ℂ => conj (S p.2))
      ((volume.restrict {z : ℂ | r < ‖z‖}).prod (volume.restrict unitDisc)) :=
    Complex.continuous_conj.comp_aestronglyMeasurable (hSm.comp_snd (μ := volume.restrict {z : ℂ | r < ‖z‖}))
  have m2 : AEStronglyMeasurable (fun p : ℂ × ℂ => A p.1)
      ((volume.restrict {z : ℂ | r < ‖z‖}).prod (volume.restrict unitDisc)) :=
    hAm.comp_fst (ν := volume.restrict unitDisc)
  have hmeas := m1.mul ((m2.mul hkm.aestronglyMeasurable).const_mul (2 / π : ℂ))
  have hg : Integrable (fun p : ℂ × ℂ => (2 / π * CA * ((1 - r⁻¹) ^ 3)⁻¹ * (‖p.1‖ ^ 6)⁻¹) * Sb)
      ((volume.restrict {z : ℂ | r < ‖z‖}).prod (volume.restrict unitDisc)) := by
    have h6 : Integrable (fun z : ℂ => 2 / π * CA * ((1 - r⁻¹) ^ 3)⁻¹ * (‖z‖ ^ 6)⁻¹)
        (volume.restrict {z : ℂ | r < ‖z‖}) :=
      ((d2l_powint (k := 6) (by norm_num)).mono_set hsub).const_mul _
    haveI : IsFiniteMeasure (volume.restrict unitDisc) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    exact h6.mul_prod (integrable_const Sb)
  refine hg.mono' hmeas ?_
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict {z : ℂ | r < ‖z‖})
    (ν := volume.restrict unitDisc)).ae (ae_restrict_mem hEr)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := volume.restrict {z : ℂ | r < ‖z‖})
    (ν := volume.restrict unitDisc)).ae (hSb.and (ae_restrict_mem hDm))
  filter_upwards [h1, h2] with p hp1 hp2
  obtain ⟨hSp, hp2⟩ := hp2
  have hz : r < ‖p.1‖ := hp1
  have hζ : ‖p.2‖ < 1 := mem_ball_zero_iff.1 hp2
  have hr0 : 0 < r := by linarith
  have hδ : 0 < 1 - r⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ hr)
  have hlow : (1 - r⁻¹) * ‖p.1‖ ≤ ‖p.2 - p.1‖ := by
    have h1 := norm_sub_norm_le p.1 p.2
    rw [norm_sub_rev] at h1
    have h2 : 1 ≤ r⁻¹ * ‖p.1‖ := by
      rw [inv_mul_eq_div, le_div_iff₀ hr0]
      linarith
    nlinarith
  have hk : ‖conj (1 / (p.2 - p.1) ^ 3)‖ ≤ ((1 - r⁻¹) ^ 3)⁻¹ * (‖p.1‖ ^ 3)⁻¹ := by
    rw [Complex.norm_conj, norm_div, norm_one, norm_pow, one_div, ← mul_inv, ← mul_pow]
    have hpos : 0 < (1 - r⁻¹) * ‖p.1‖ := mul_pos hδ (by linarith)
    exact inv_anti₀ (pow_pos hpos 3) (pow_le_pow_left₀ hpos.le hlow 3)
  have hA1 := hAb p.1 (hsub hp1)
  have hSb0 : 0 ≤ Sb := (norm_nonneg _).trans hSp
  have h2π : ‖(2 / π : ℂ)‖ = 2 / π := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, h2π]
  have hb1 : ‖A p.1‖ * ‖conj (1 / (p.2 - p.1) ^ 3)‖ ≤
      (CA * (‖p.1‖ ^ 3)⁻¹) * (((1 - r⁻¹) ^ 3)⁻¹ * (‖p.1‖ ^ 3)⁻¹) :=
    mul_le_mul hA1 hk (norm_nonneg _) (mul_nonneg hCA (by positivity))
  have hb2 := mul_le_mul hSp (mul_le_mul_of_nonneg_left hb1 (by positivity : (0 : ℝ) ≤ 2 / π))
    (by positivity) hSb0
  refine hb2.trans (le_of_eq ?_)
  rw [show ‖p.1‖ ^ 6 = ‖p.1‖ ^ 3 * ‖p.1‖ ^ 3 by ring, mul_inv]
  ring

/-- (F-I4 helper) Fubini on `{|z| > r} × 𝔻` (`r > 1`, absolutely convergent as `|ζ - z| ≥ (1 - 1/r)|z|`). -/
theorem s3f_i4_fub {A S : ℂ → ℂ} (hAc : ContinuousOn A unitDiscExterior) {CA : ℝ} (hCA : 0 ≤ CA)
    (hAb : ∀ w ∈ unitDiscExterior, ‖A w‖ ≤ CA * (‖w‖ ^ 3)⁻¹) {Sb : ℝ}
    (hSm : AEStronglyMeasurable S (volume.restrict unitDisc))
    (hSb : ∀ᵐ ζ ∂(volume.restrict unitDisc), ‖S ζ‖ ≤ Sb) {r : ℝ} (hr : 1 < r) :
    ∫ z in {z : ℂ | r < ‖z‖}, A z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc, S ζ / (ζ - z) ^ 3) =
      ∫ ζ in unitDisc, conj (S ζ) * ((2 / π : ℂ) * ∫ z in {z : ℂ | r < ‖z‖}, A z * conj (1 / (ζ - z) ^ 3)) := by
  have hEr : MeasurableSet {z : ℂ | r < ‖z‖} := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hsub : {z : ℂ | r < ‖z‖} ⊆ unitDiscExterior := fun z hz => by
    show 1 < ‖z‖
    exact hr.trans hz
  have hc : conj (2 / π : ℂ) = 2 / π := by rw [map_div₀, Complex.conj_ofReal, map_ofNat]
  have hpt : ∀ z, A z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc, S ζ / (ζ - z) ^ 3) =
      ∫ ζ in unitDisc, conj (S ζ) * ((2 / π : ℂ) * (A z * conj (1 / (ζ - z) ^ 3))) := by
    intro z
    rw [map_mul, hc, ← integral_conj, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    simp only [map_div₀, map_one, map_pow]
    ring
  rw [setIntegral_congr_fun hEr (fun z _ => hpt z)]
  have hint : Integrable (Function.uncurry fun (z ζ : ℂ) => conj (S ζ) * ((2 / π : ℂ) * (A z * conj (1 / (ζ - z) ^ 3))))
      ((volume.restrict {z : ℂ | r < ‖z‖}).prod (volume.restrict unitDisc)) :=
    s3f_i4_fub_int hAc hCA hAb hSm hSb hr
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  beta_reduce
  rw [integral_const_mul, integral_const_mul]

/-- (F-I4 helper) The `r > 1` representation: `∫_{|z|>r} 𝒜 conj I = ∫_{𝔻*} R(u) r⁴ K(r² u)`, `K = A' + 2A/u`. -/
theorem s3f_i4_rep {A R : ℂ → ℂ} {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2))
    (hA : ∀ w ∈ unitDiscExterior, HasSum (fun n => x n * basisF n w) (A w))
    (hAd : DifferentiableOn ℂ A unitDiscExterior) {CA : ℝ} (hCA : 0 ≤ CA)
    (hAb : ∀ w ∈ unitDiscExterior, ‖A w‖ ≤ CA * (‖w‖ ^ 3)⁻¹) {Sb : ℝ}
    (hSm : AEStronglyMeasurable (fun ζ => conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2) (volume.restrict unitDisc))
    (hSb : ∀ᵐ ζ ∂(volume.restrict unitDisc), ‖conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2‖ ≤ Sb)
    {r : ℝ} (hr : 1 < r) :
    ∫ z in {z : ℂ | r < ‖z‖}, A z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc,
        conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) =
      ∫ u in unitDiscExterior, R u * ((r : ℂ) ^ 4 * (deriv A ((r : ℂ) ^ 2 * u) +
        2 * A ((r : ℂ) ^ 2 * u) / ((r : ℂ) ^ 2 * u))) := by
  have hfub := s3f_i4_fub (S := fun ζ => conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2) hAd.continuousOn hCA hAb
    hSm hSb hr
  beta_reduce at hfub
  rw [hfub, s310_disc_punct]
  have hcore : ∀ ζ ∈ unitDisc \ {0}, conj (conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2) *
      ((2 / π : ℂ) * ∫ z in {z : ℂ | r < ‖z‖}, A z * conj (1 / (ζ - z) ^ 3)) =
      conj (conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2) * ((r : ℂ) ^ 4 * ((conj ζ)⁻¹) ^ 4 *
        (deriv A ((r : ℂ) ^ 2 / conj ζ) + 2 * A ((r : ℂ) ^ 2 / conj ζ) / ((r : ℂ) ^ 2 / conj ζ))) := by
    intro ζ hζ
    rw [s3f_i4_core hx hA hAd hAb hζ.1 hζ.2 hr.le]
  have hD0 : MeasurableSet (unitDisc \ {0}) := measurableSet_ball.diff (measurableSet_singleton 0)
  rw [setIntegral_congr_fun hD0 hcore, ← s310_disc_punct]
  have hrefl := s3f_i4_refl R (fun v => deriv A v + 2 * A v / v) r
  beta_reduce at hrefl
  exact hrefl

/-- (F-I4 helper) `∫_{|z|>r} F → ∫_{𝔻*} F` as `r → 1⁺` (dominated convergence). -/
theorem s3f_i4_lim_ext {F : ℂ → ℂ} (hF : IntegrableOn F unitDiscExterior) :
    Tendsto (fun r : ℝ => ∫ z in {z : ℂ | r < ‖z‖}, F z) (𝓝[>] 1) (𝓝 (∫ z in unitDiscExterior, F z)) := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEr : ∀ r : ℝ, MeasurableSet {z : ℂ | r < ‖z‖} :=
    fun r => (isOpen_lt continuous_const continuous_norm).measurableSet
  have hlim : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      Tendsto (fun r : ℝ => {z : ℂ | r < ‖z‖}.indicator F z) (𝓝[>] 1) (𝓝 (F z)) := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    have hz1 : (1 : ℝ) < ‖z‖ := hz
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hz1)] with r hr
    exact (indicator_of_mem (show z ∈ {z : ℂ | r < ‖z‖} from hr) F).symm
  refine (tendsto_integral_filter_of_dominated_convergence (fun z => ‖F z‖)
    (Eventually.of_forall fun r => hF.aestronglyMeasurable.indicator (hEr r))
    (Eventually.of_forall fun r => Eventually.of_forall fun z => norm_indicator_le_norm_self _ _)
    hF.norm hlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr1 : (1 : ℝ) < r := hr
  have hsub : {z : ℂ | r < ‖z‖} ⊆ unitDiscExterior := fun z hz => by
    show 1 < ‖z‖
    exact lt_trans hr1 hz
  rw [setIntegral_indicator (hEr r), inter_eq_right.2 hsub]

/-- (F-I4 helper) `∫_{𝔻*} R(u) r⁴ K(r² u) → ∫_{𝔻*} R K` as `r → 1⁺` for `K` continuous with `|K| ≤ C|w|⁻⁴`. -/
theorem s3f_i4_lim_int {R K : ℂ → ℂ} {Rb CK : ℝ} (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb) (hK : ContinuousOn K unitDiscExterior)
    (hCK : 0 ≤ CK) (hKb : ∀ w ∈ unitDiscExterior, ‖K w‖ ≤ CK * (‖w‖ ^ 4)⁻¹) :
    Tendsto (fun r : ℝ => ∫ u in unitDiscExterior, R u * ((r : ℂ) ^ 4 * K ((r : ℂ) ^ 2 * u))) (𝓝[>] 1)
      (𝓝 (∫ u in unitDiscExterior, R u * K u)) := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hmap : ∀ r : ℝ, 1 ≤ r → ∀ u ∈ unitDiscExterior, (r : ℂ) ^ 2 * u ∈ unitDiscExterior := fun r hr u hu => by
    show 1 < ‖(r : ℂ) ^ 2 * u‖
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have : 1 < ‖u‖ := hu
    have h1 : 1 ≤ r ^ 2 := one_le_pow₀ hr
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (le_of_lt (lt_trans one_pos this))]
  have hev : ∀ᶠ r in 𝓝[>] (1 : ℝ), 1 < r := self_mem_nhdsWithin
  refine tendsto_integral_filter_of_dominated_convergence (fun u => Rb * (CK * (‖u‖ ^ 4)⁻¹)) ?_ ?_ ?_ ?_
  · filter_upwards [hev] with r hr
    refine hRm.mul (ContinuousOn.aestronglyMeasurable ?_ hO.measurableSet)
    exact continuousOn_const.mul (hK.comp (continuousOn_const.mul continuousOn_id) (hmap r hr.le))
  · filter_upwards [hev] with r hr
    filter_upwards [hRb, ae_restrict_mem hO.measurableSet] with u hRu hu
    have hu1 : 1 < ‖u‖ := hu
    have hu0 : ‖u‖ ≠ 0 := by positivity
    have hr0 : r ≠ 0 := by positivity
    have hw := hKb _ (hmap r hr.le u hu)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ r)] at hw
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ r)]
    have hRb0 : 0 ≤ Rb := (norm_nonneg _).trans hRu
    have hr4 : (1 : ℝ) ≤ r ^ 4 := one_le_pow₀ hr.le
    have hk : r ^ 4 * ‖K ((r : ℂ) ^ 2 * u)‖ ≤ CK * (‖u‖ ^ 4)⁻¹ := by
      calc r ^ 4 * ‖K ((r : ℂ) ^ 2 * u)‖ ≤ r ^ 4 * (CK * ((r ^ 2 * ‖u‖) ^ 4)⁻¹) :=
            mul_le_mul_of_nonneg_left hw (by positivity)
        _ = CK * (r ^ 4 * ‖u‖ ^ 4)⁻¹ := by
            field_simp
        _ ≤ CK * (‖u‖ ^ 4)⁻¹ := by
            refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) hCK
            nlinarith [pow_pos (show 0 < ‖u‖ by linarith) 4]
    exact mul_le_mul hRu hk (by positivity) hRb0
  · exact ((d2l_powint (k := 4) (by norm_num)).const_mul CK).const_mul Rb
  · filter_upwards [ae_restrict_mem hO.measurableSet] with u hu
    have hK1 : ContinuousAt K (((1 : ℝ) : ℂ) ^ 2 * u) := by
      simpa using hK.continuousAt (hO.mem_nhds hu)
    have hc1 : Continuous (fun r : ℝ => (r : ℂ) ^ 4) := Complex.continuous_ofReal.pow 4
    have hc2 : Continuous (fun r : ℝ => (r : ℂ) ^ 2 * u) := (Complex.continuous_ofReal.pow 2).mul continuous_const
    have hc : ContinuousAt (fun r : ℝ => R u * ((r : ℂ) ^ 4 * K ((r : ℂ) ^ 2 * u))) 1 :=
      continuousAt_const.mul (hc1.continuousAt.mul (ContinuousAt.comp (f := fun r : ℝ => (r : ℂ) ^ 2 * u) (x := 1) hK1 hc2.continuousAt))
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using this

/-- (F-I4 helper) The identity of `s3f_I4` for abstract data: `A = Σ x_n basisF_n` with `|A| ≲ |w|⁻³`, `|A'| ≲ |w|⁻⁴`,
`R` bounded, and the left integrand integrable. -/
theorem s3f_i4_ident {A R : ℂ → ℂ} {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2))
    (hA : ∀ w ∈ unitDiscExterior, HasSum (fun n => x n * basisF n w) (A w))
    (hAd : DifferentiableOn ℂ A unitDiscExterior) {CA CA' : ℝ} (hCA : 0 ≤ CA) (hCA' : 0 ≤ CA')
    (hAb : ∀ w ∈ unitDiscExterior, ‖A w‖ ≤ CA * (‖w‖ ^ 3)⁻¹)
    (hAb' : ∀ w ∈ unitDiscExterior, ‖deriv A w‖ ≤ CA' * (‖w‖ ^ 4)⁻¹) {Rb : ℝ}
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hint : IntegrableOn (fun z => A z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc,
      conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3)) unitDiscExterior) :
    IntegrableOn (fun u => R u * (deriv A u + 2 * A u / u)) unitDiscExterior ∧
      ∫ z in unitDiscExterior, A z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc,
        conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) =
      ∫ u in unitDiscExterior, R u * (deriv A u + 2 * A u / u) := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hne : ∀ w ∈ unitDiscExterior, w ≠ 0 := fun w hw h => by
    have : (1 : ℝ) < ‖w‖ := hw
    rw [h, norm_zero] at this
    linarith
  have hKc : ContinuousOn (fun w => deriv A w + 2 * A w / w) unitDiscExterior :=
    (hAd.deriv hO).continuousOn.add ((continuousOn_const.mul hAd.continuousOn).div continuousOn_id hne)
  have hKb : ∀ w ∈ unitDiscExterior, ‖deriv A w + 2 * A w / w‖ ≤ (CA' + 2 * CA) * (‖w‖ ^ 4)⁻¹ := by
    intro w hw
    have hw1 : 1 < ‖w‖ := hw
    have hw0 : 0 < ‖w‖ := by linarith
    have hw0' : ‖w‖ ≠ 0 := hw0.ne'
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have h2 : 2 * ‖A w‖ / ‖w‖ ≤ 2 * CA * (‖w‖ ^ 4)⁻¹ := by
      rw [div_le_iff₀ hw0]
      have := hAb w hw
      calc 2 * ‖A w‖ ≤ 2 * (CA * (‖w‖ ^ 3)⁻¹) := by linarith
        _ = 2 * CA * (‖w‖ ^ 4)⁻¹ * ‖w‖ := by
            field_simp
    linarith [hAb' w hw]
  have hint2 : IntegrableOn (fun u => R u * (deriv A u + 2 * A u / u)) unitDiscExterior := by
    refine Integrable.mono' (((d2l_powint (k := 4) (by norm_num)).const_mul (CA' + 2 * CA)).const_mul Rb)
      (hRm.mul (hKc.aestronglyMeasurable hO.measurableSet)) ?_
    filter_upwards [hRb, ae_restrict_mem hO.measurableSet] with u hRu hu
    rw [norm_mul]
    exact mul_le_mul hRu (hKb u hu) (norm_nonneg _) ((norm_nonneg _).trans hRu)
  refine ⟨hint2, ?_⟩
  have h1 := s3f_i4_lim_ext hint
  have h2 := s3f_i4_lim_int hRm hRb hKc (by linarith) hKb
  obtain ⟨hSm, hSb⟩ := d2e_S_ae hRm hRb
  have h3 : ∀ᶠ r in 𝓝[>] (1 : ℝ), ∫ z in {z : ℂ | r < ‖z‖}, A z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc,
      conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) =
      ∫ u in unitDiscExterior, R u * ((r : ℂ) ^ 4 * (deriv A ((r : ℂ) ^ 2 * u) +
        2 * A ((r : ℂ) ^ 2 * u) / ((r : ℂ) ^ 2 * u))) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact s3f_i4_rep hx hA hAd hCA hAb hSm hSb (show (1 : ℝ) < r from hr)
  exact tendsto_nhds_unique (h1.congr' h3) h2

/-- (F-I4 helper) `∂_z` of the zero function vanishes. -/
theorem s3f_i4_dz0 (z : ℂ) : dz (fun _ : ℂ => (0 : ℂ)) z = 0 := by
  show (fderiv ℝ (fun _ : ℂ => (0 : ℂ)) z 1 - I * fderiv ℝ (fun _ : ℂ => (0 : ℂ)) z I) / 2 = 0
  simp

/-- (F-I4 helper) Integrability of the `I₄` integrand: by the unwelded `t̄`-identity and `d2p_tbar`,
`I = ∂̄_t 𝒜(g_t)|₀ + ∂_z(𝒜 γ̇₂) - 2c₂'(g'/b - 1)` on `𝔻*`; the first is `L²` (G-DOM), the second is the Lie term of
`d2l_main` (with `R = 0`), the third is `O(|z|⁻³)` against bounded `g'`. -/
theorem s3f_i4_conj1 {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    IntegrableOn (fun z => preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc,
      conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3)) unitDiscExterior := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hO.measurableSet
  have hd := delta0_bounds
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.2 (has.trans hd.2)
  have hμ : beltramiMul a (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨⟨ρ, hρ, G, hGd, hGi, hGd', hGg⟩, -⟩ := d2l_ext hκ hκD ha has haL haD
  obtain ⟨hRm, hRb⟩ := d2l_R_data has m
  obtain ⟨hSm, hSb⟩ := d2e_S_ae hRm hRb
  obtain ⟨hgd, hg'd, hgi, hdd, hg'⟩ := d2e_basic hρ hGd hGi hGd' hGg
  obtain ⟨hAd, CA, CA', hCA, hCA', hA, hA'⟩ := d2l_A_bounds hκ hκD ha has haL haD
  -- `‖g'‖` is bounded on `𝔻*` (as in `s3d_D2_pointwise`)
  obtain ⟨c, -, C, hC⟩ := d2e_growth hpair
  have hOρ : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨M1, hM1⟩ := ((isCompact_closedBall (0 : ℂ) 4).inter_right
    (isClosed_le continuous_const continuous_norm)).exists_bound_of_continuousOn
    ((hGd.deriv hOρ).continuousOn.mono fun z hz => show ρ < ‖z‖ from lt_of_lt_of_le hρ hz.2)
  have hM : ∀ u ∈ unitDiscExterior, ‖deriv (gsans (beltramiMul a κ)) u‖ ≤ max M1 C := by
    intro u hu
    have hu1 : 1 < ‖u‖ := hu
    by_cases h4 : 4 ≤ ‖u‖
    · exact (hC u h4).2.trans (le_max_right _ _)
    · rw [hdd u hu]
      exact (hM1 u ⟨mem_closedBall_zero_iff.2 (by linarith), hu1.le⟩).trans (le_max_left _ _)
  -- (1) `𝒜 · conj ∂̄_t 𝒜(g_t)|₀`: product of two `L²` functions
  have hAL : MemLp (preSchwarzian (gsans (beltramiMul a κ))) 2 (volume.restrict unitDiscExterior) :=
    ((mem_A21fun_iff_memLp hEm).1 (s3f_i4_A21 hAd hA)).2
  have hD := (s3x_dom_data hEm (s3d_g_dom_proof hκ hκD ha has haL haD hm hmD)).2.2
  have hf1 : Integrable (fun z => preSchwarzian (gsans (beltramiMul a κ)) z *
      conj (dzbar (fun t : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) 0))
      (volume.restrict unitDiscExterior) := by
    have h1 := (memLp_two_iff_integrable_sq_norm hAL.aestronglyMeasurable).1 hAL
    have h2 := (memLp_two_iff_integrable_sq_norm hD.aestronglyMeasurable).1 hD
    refine Integrable.mono' ((h1.add h2).div_const 2)
      (hAL.aestronglyMeasurable.mul (Complex.continuous_conj.comp_aestronglyMeasurable hD.aestronglyMeasurable)) ?_
    filter_upwards with z
    try simp only [Pi.add_apply]
    rw [norm_mul, Complex.norm_conj]
    nlinarith [sq_nonneg (‖preSchwarzian (gsans (beltramiMul a κ)) z‖ -
      ‖dzbar (fun t : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) 0‖)]
  -- (2) the Lie term: `d2l_main` with `R = 0`
  have hγ2 : DifferentiableOn ℂ (fun y : ℂ => -(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) *
      ζ ^ 2 / conj ζ ^ 2 * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) unitDiscExterior := by
    have hη2 := (s3d_D2_eta hκ hκD ha has haL haD hm hmD).2
    refine ((((differentiableOn_const (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) *
      ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)))).mul
      (hgd.pow 2)).div hg'd hg').sub hη2).congr fun y hy => ?_
    have h3 := hg' y hy
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    beta_reduce
    generalize (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
      (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) = J
    generalize (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) *
      ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) = C
    field_simp
    ring
  have hf2 := d2l_main (R := fun _ => (0 : ℂ)) (Rb := 0)
    (S := fun ζ => conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2) hCA hCA' hAd hA hA'
    aestronglyMeasurable_const (Eventually.of_forall fun _ => by simp) hSm hSb
    (by simp only [zero_mul, integral_zero, mul_zero]; exact contDiffOn_const) hγ2
  simp only [zero_mul, integral_zero, mul_zero, s3f_i4_dz0, zero_add] at hf2
  -- the pointwise identity on `𝔻*`
  have hunw := s3d_D2_unwelded hκ hκD ha has haL haD hm hmD
  have hpw := s3d_D2_pointwise hκ hκD ha has haL haD hm hmD
  -- (3) the `g'` term
  have hf3 : Integrable (fun z => preSchwarzian (gsans (beltramiMul a κ)) z *
      conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 /
        ((ζ + 1) * (ζ + I) * (ζ - 1))) * (deriv (gsans (beltramiMul a κ)) z / derivAtInfty (gsans (beltramiMul a κ)) - 1)))
      (volume.restrict unitDiscExterior) := by
    generalize hc2 : (1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 /
        ((ζ + 1) * (ζ + I) * (ζ - 1)) = c2
    generalize hb : derivAtInfty (gsans (beltramiMul a κ)) = b
    have hcont : ContinuousOn (fun z => 2 * c2 * (deriv (gsans (beltramiMul a κ)) z / b - 1)) unitDiscExterior :=
      continuousOn_const.mul ((hg'd.continuousOn.div_const b).sub continuousOn_const)
    refine Integrable.mono' (((d2l_powint (k := 3) (by norm_num)).const_mul CA).const_mul
      (2 * ‖c2‖ * (max M1 C * ‖b‖⁻¹ + 1)))
      ((hAd.continuousOn.aestronglyMeasurable hEm).mul
        (Complex.continuous_conj.comp_aestronglyMeasurable (hcont.aestronglyMeasurable hEm))) ?_
    filter_upwards [ae_restrict_mem hEm] with z hz
    have h1 : ‖deriv (gsans (beltramiMul a κ)) z / b - 1‖ ≤ max M1 C * ‖b‖⁻¹ + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_div, norm_one, div_eq_mul_inv]
      gcongr
      exact hM z hz
    have h2 : ‖(2 : ℂ) * c2‖ = 2 * ‖c2‖ := by
      rw [norm_mul]
      norm_num
    show ‖preSchwarzian (gsans (beltramiMul a κ)) z * conj (2 * c2 * (deriv (gsans (beltramiMul a κ)) z / b - 1))‖ ≤ _
    rw [norm_mul, Complex.norm_conj, norm_mul, h2]
    refine (mul_le_mul (hA z hz) (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
      (mul_nonneg hCA (by positivity))).trans (le_of_eq ?_)
    ring
  have hpt : ∀ z ∈ unitDiscExterior, preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc,
      conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) =
      preSchwarzian (gsans (beltramiMul a κ)) z *
          conj (dzbar (fun t : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) 0) +
        preSchwarzian (gsans (beltramiMul a κ)) z * conj (dz (fun y : ℂ => preSchwarzian (gsans (beltramiMul a κ)) y *
          (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
            (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z) -
        preSchwarzian (gsans (beltramiMul a κ)) z *
          conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 /
            ((ζ + 1) * (ζ + I) * (ζ - 1))) * (deriv (gsans (beltramiMul a κ)) z / derivAtInfty (gsans (beltramiMul a κ)) - 1)) := by
    intro z hz
    have e1 := (hunw z hz).2.2
    have e2 := (hpw z hz).2.2
    rw [← mul_add, ← mul_sub, ← map_add, ← map_sub, e1]
    congr 2
    linear_combination (-1 : ℂ) * e2
  exact IntegrableOn.congr_fun ((hf1.add hf2).sub hf3) (fun z hz => (hpt z hz).symm) hEm

/-- **(F-I4)** The `t̄`-part of `D2` (TT's `I₄`): `ζ = 1/ū` and Laurent modes of `𝒜(g)` on `𝔻*` give
`∫_{𝔻*} 𝒜(g) conj((2/π)∫_𝔻 R̃/(ζ - z)³) = ∫_{𝔻*} R (𝒜(g)' + 2𝒜(g)/u)`, both integrands integrable. -/
theorem s3f_I4 {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    IntegrableOn (fun z => preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3)) unitDiscExterior ∧
      IntegrableOn (fun u => RnmFun (toLinf m) a u * (deriv (preSchwarzian (gsans (beltramiMul a κ))) u + 2 * preSchwarzian (gsans (beltramiMul a κ)) u / u)) unitDiscExterior ∧
      (∫ z in unitDiscExterior, preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3)) =
        ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * (deriv (preSchwarzian (gsans (beltramiMul a κ))) u + 2 * preSchwarzian (gsans (beltramiMul a κ)) u / u) := by
  obtain ⟨hAd, CA, CA', hCA, hCA', hAb, hAb'⟩ := d2l_A_bounds hκ hκD ha has haL haD
  obtain ⟨hRm, hRb⟩ := d2l_R_data has m
  obtain ⟨x, hx, hAx, -⟩ := s35_ext_expansion (s3f_i4_A21 hAd hAb)
  have hint := s3f_i4_conj1 hκ hκD ha has haL haD hm hmD
  obtain ⟨h2, h3⟩ := s3f_i4_ident hx hAx hAd hCA hCA' hAb hAb' hRm hRb hint
  exact ⟨hint, h2, h3⟩

/-- Exterior Koebe separation: `|g'(x)|(|x| - 1)/4 ≤ |g(x) - f(z)|` for `x ∈ 𝔻*`, `z ∈ 𝔻`. -/
theorem s3fb_gkoebe {f g G : ℂ → ℂ} {ρ : ℝ} (hpair : IsNormalizedDisjointPair f g) (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGg : EqOn G g unitDiscExterior) {x : ℂ} (hx : x ∈ unitDiscExterior) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖deriv g x‖ * (‖x‖ - 1) / 4 ≤ ‖g x - f z‖ := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hx1 : (1 : ℝ) < ‖x‖ := hx
  set δ : ℝ := ‖x‖ - 1 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hball : ∀ ζ ∈ ball (0 : ℂ) 1, x + (δ : ℂ) * ζ ∈ unitDiscExterior := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
    show (1 : ℝ) < ‖x + (δ : ℂ) * ζ‖
    have h1 : ‖(δ : ℂ) * ζ‖ < δ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
      exact mul_lt_of_lt_one_right hδ0 hζ1
    have h2 := norm_sub_norm_le x (-((δ : ℂ) * ζ))
    rw [sub_neg_eq_add, norm_neg] at h2
    linarith
  have hEρ : ∀ y ∈ unitDiscExterior, y ∈ {z : ℂ | ρ < ‖z‖} := fun y hy => by
    have : (1 : ℝ) < ‖y‖ := hy
    show ρ < ‖y‖
    linarith
  set ψ : ℂ → ℂ := fun ζ => G (x + (δ : ℂ) * ζ) - G x with hψ
  have hψd : DifferentiableOn ℂ ψ (ball (0 : ℂ) 1) := by
    intro ζ hζ
    have hG' : DifferentiableAt ℂ G (x + (δ : ℂ) * ζ) :=
      hGd.differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds (hEρ _ (hball ζ hζ)))
    exact ((hG'.comp ζ ((differentiableAt_id.const_mul (δ : ℂ)).const_add x)).sub_const _).differentiableWithinAt
  have hψi : InjOn ψ (ball (0 : ℂ) 1) := by
    intro ζ₁ h₁ ζ₂ h₂ h
    have h' : G (x + (δ : ℂ) * ζ₁) = G (x + (δ : ℂ) * ζ₂) := sub_left_inj.1 h
    have := hGi (hEρ _ (hball ζ₁ h₁)) (hEρ _ (hball ζ₂ h₂)) h'
    have hδc : (δ : ℂ) ≠ 0 := ofReal_ne_zero.2 hδ0.ne'
    exact mul_left_cancel₀ hδc (add_left_cancel this)
  have hψ0 : ψ 0 = 0 := by simp [hψ]
  have hGx : DifferentiableAt ℂ G x := hGd.differentiableAt
    ((isOpen_lt continuous_const continuous_norm).mem_nhds (hEρ x hx))
  have hdψ : deriv ψ 0 = deriv G x * (δ : ℂ) := by
    have h1 : HasDerivAt (fun ζ : ℂ => x + (δ : ℂ) * ζ) (δ : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (δ : ℂ)).const_add x
    have h2 : HasDerivAt (fun ζ : ℂ => G (x + (δ : ℂ) * ζ)) (deriv G x * (δ : ℂ)) 0 := by
      exact hGx.hasDerivAt.comp_of_eq 0 h1 (by ring)
    exact (h2.sub_const (G x)).deriv
  have hw : f z - G x ∉ ψ '' ball (0 : ℂ) 1 := by
    rintro ⟨ζ, hζ, h⟩
    have h' : G (x + (δ : ℂ) * ζ) = f z := by
      simp only [hψ] at h
      linear_combination h
    have hm := hball ζ hζ
    rw [hGg hm] at h'
    exact Set.disjoint_left.1 hpair.2.2.2.2.2 ⟨z, hz, rfl⟩ ⟨_, hm, h'⟩
  have hK := koebe_quarter_of_not_mem hψd hψi hψ0 hw
  rw [hdψ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0] at hK
  have hgG : deriv g x = deriv G x := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hE.mem_nhds hx] with y hy using (hGg hy).symm
  rw [hgG, ← hGg hx]
  rw [norm_sub_rev] at hK
  linarith

/-- Change of variables `x = f(z)`: `∫_𝔻 |f'|²|f - p|⁻³ ≤ 2π · 2/d` when `f(𝔻)` stays `d` away from `p`. -/
theorem s3fb_inner {f g : ℂ → ℂ} (hpair : IsNormalizedDisjointPair f g) {p : ℂ} {d : ℝ} (hd : 0 < d)
    (hp : ∀ z ∈ unitDisc, d ≤ ‖f z - p‖) :
    ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv f z‖ ^ 2) * ‖f z - p‖ₑ ^ (-3 : ℝ) ≤
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (-(d / 2) ^ (2 - 3 : ℝ) / (2 - 3)) := by
  have hDo : IsOpen unitDisc := isOpen_ball
  rw [← r24_conformal_lintegral hDo hpair.1 hpair.2.1 (fun y => ‖y - p‖ₑ ^ (-3 : ℝ))]
  rw [← lintegral_compl_ball_sub_enorm_rpow_neg (by norm_num : (2 : ℝ) < 3) (half_pos hd) p]
  refine lintegral_mono_set ?_
  rintro _ ⟨z, hz, rfl⟩
  show d / 2 < ‖f z - p‖
  linarith [hp z hz]

/-- Bounds for the interior map on `𝔻` from a holomorphic extension past `𝕊¹`. -/
theorem s3fb_fbd {f F : ℂ → ℂ} {Rf : ℝ} (hRf : 1 < Rf) (hFd : DifferentiableOn ℂ F (ball 0 Rf))
    (hFd' : ∀ z ∈ ball (0 : ℂ) Rf, deriv F z ≠ 0) (hFf : EqOn F f unitDisc) :
    ∃ K M Mf c0 : ℝ, 0 < c0 ∧ ∀ z ∈ unitDisc, ‖f z‖ ≤ K ∧ ‖deriv (deriv f) z‖ ≤ M ∧ ‖deriv f z‖ ≤ Mf ∧
      c0 ≤ ‖deriv f z‖ := by
  have hO : IsOpen (ball (0 : ℂ) Rf) := isOpen_ball
  have hDo : IsOpen unitDisc := isOpen_ball
  have hK : IsCompact (closedBall (0 : ℂ) 1) := isCompact_closedBall 0 1
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 Rf := closedBall_subset_ball hRf
  have hF1 : DifferentiableOn ℂ (deriv F) (ball 0 Rf) := hFd.deriv hO
  have hF2 : DifferentiableOn ℂ (deriv (deriv F)) (ball 0 Rf) := hF1.deriv hO
  obtain ⟨K, hKb⟩ := hK.exists_bound_of_continuousOn (hFd.continuousOn.mono hsub)
  obtain ⟨M, hMb⟩ := hK.exists_bound_of_continuousOn (hF2.continuousOn.mono hsub)
  obtain ⟨Mf, hMfb⟩ := hK.exists_bound_of_continuousOn (hF1.continuousOn.mono hsub)
  obtain ⟨z0, hz0, hmin⟩ := hK.exists_isMinOn (nonempty_closedBall.2 zero_le_one)
    ((hF1.continuousOn.mono hsub).norm)
  have hc0 : 0 < ‖deriv F z0‖ := norm_pos_iff.2 (hFd' z0 (hsub hz0))
  have hev : ∀ z ∈ unitDisc, F =ᶠ[𝓝 z] f := fun z hz => by
    filter_upwards [hDo.mem_nhds hz] with y hy using hFf hy
  have hev1 : ∀ z ∈ unitDisc, deriv F =ᶠ[𝓝 z] deriv f := fun z hz => by
    filter_upwards [hDo.mem_nhds hz] with y hy using (hev y hy).deriv_eq
  refine ⟨K, M, Mf, ‖deriv F z0‖, hc0, fun z hz => ?_⟩
  have hzc : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hFf hz]; exact hKb z hzc
  · rw [← (hev1 z hz).deriv_eq]; exact hMb z hzc
  · rw [← (hev z hz).deriv_eq]; exact hMfb z hzc
  · rw [← (hev z hz).deriv_eq]; exact hmin hzc

/-- Real form of `s3fb_inner`. -/
theorem s3fb_inner_real {f g : ℂ → ℂ} (hpair : IsNormalizedDisjointPair f g) {Mf : ℝ}
    (hMf : ∀ z ∈ unitDisc, ‖deriv f z‖ ≤ Mf) {p : ℂ} {d : ℝ} (hd : 0 < d)
    (hp : ∀ z ∈ unitDisc, d ≤ ‖f z - p‖) :
    IntegrableOn (fun z => ‖deriv f z‖ ^ 2 / ‖f z - p‖ ^ 3) unitDisc ∧
      ∫ z in unitDisc, ‖deriv f z‖ ^ 2 / ‖f z - p‖ ^ 3 ≤ 4 * π / d := by
  have hDo : IsOpen unitDisc := isOpen_ball
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hfc : ContinuousOn f unitDisc := hpair.1.continuousOn
  have hf'c : ContinuousOn (deriv f) unitDisc := (hpair.1.deriv hDo).continuousOn
  have hne : ∀ z ∈ unitDisc, 0 < ‖f z - p‖ := fun z hz => lt_of_lt_of_le hd (hp z hz)
  have hcont : ContinuousOn (fun z => ‖deriv f z‖ ^ 2 / ‖f z - p‖ ^ 3) unitDisc :=
    (hf'c.norm.pow 2).div ((hfc.sub continuousOn_const).norm.pow 3) fun z hz => (pow_pos (hne z hz) 3).ne'
  have hbd : ∀ z ∈ unitDisc, ‖‖deriv f z‖ ^ 2 / ‖f z - p‖ ^ 3‖ ≤ Mf ^ 2 / d ^ 3 := by
    intro z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖deriv f z‖ ^ 2 ≤ Mf ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hMf z hz) 2
    have h2 : d ^ 3 ≤ ‖f z - p‖ ^ 3 := pow_le_pow_left₀ hd.le (hp z hz) 3
    calc ‖deriv f z‖ ^ 2 / ‖f z - p‖ ^ 3 ≤ Mf ^ 2 / ‖f z - p‖ ^ 3 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ Mf ^ 2 / d ^ 3 := div_le_div_of_nonneg_left (by positivity) (by positivity) h2
  have hint : IntegrableOn (fun z => ‖deriv f z‖ ^ 2 / ‖f z - p‖ ^ 3) unitDisc :=
    (integrableOn_const (C := Mf ^ 2 / d ^ 3) measure_ball_lt_top.ne).mono'
      (hcont.aestronglyMeasurable hDm) ((ae_restrict_iff' hDm).2 (Filter.Eventually.of_forall hbd))
  refine ⟨hint, ?_⟩
  have hL := s3fb_inner hpair hd hp
  have hconst : ENNReal.ofReal (2 * π) * ENNReal.ofReal (-(d / 2) ^ (2 - 3 : ℝ) / (2 - 3)) =
      ENNReal.ofReal (4 * π / d) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : (2 - 3 : ℝ) = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
    field_simp
    ring
  rw [hconst] at hL
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => by positivity)
    hint.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_trans (le_of_eq ?_) hL)
  refine setLIntegral_congr_fun hDm fun z hz => ?_
  have hz0 := hne z hz
  rw [ENNReal.ofReal_div_of_pos (pow_pos hz0 3), div_eq_mul_inv, ← ofReal_norm_eq_enorm,
    ENNReal.ofReal_rpow_of_pos hz0, Real.rpow_neg hz0.le]
  congr 1
  rw [ENNReal.ofReal_inv_of_pos (by positivity)]
  norm_cast


/-- `|R|/(|x| - 1) ≤ (|R|² ρ + (|x| + 1)²/4)/2` on `𝔻*` (AM-GM against the hyperbolic weight). -/
theorem s3fb_amgm {r t : ℝ} (ht : 1 < t) (hr : 0 ≤ r) :
    r / (t - 1) ≤ (r ^ 2 * (4 / (1 - t ^ 2) ^ 2) + (t + 1) ^ 2 / 4) / 2 := by
  have ht1 : 0 < t - 1 := by linarith
  have ht2 : 0 < t ^ 2 - 1 := by nlinarith
  set a : ℝ := 2 * r / (t ^ 2 - 1) with ha
  set b : ℝ := (t + 1) / 2 with hb
  have hab : r / (t - 1) = a * b := by
    rw [ha, hb]
    field_simp
    ring
  have ha2 : r ^ 2 * (4 / (1 - t ^ 2) ^ 2) = a ^ 2 := by
    rw [ha, div_pow, show (1 - t ^ 2) ^ 2 = (t ^ 2 - 1) ^ 2 by ring]
    ring
  have hb2 : (t + 1) ^ 2 / 4 = b ^ 2 := by rw [hb]; ring
  rw [hab, ha2, hb2]
  nlinarith [sq_nonneg (a - b)]

/-- Joint integrability of the `V̈` kernel on `𝔻* × 𝔻`. -/
theorem s3fb_joint {f g G F R : ℂ → ℂ} {ρ Rf Rb : ℝ} (hpair : IsNormalizedDisjointPair f g) (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGd' : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0) (hGg : EqOn G g unitDiscExterior)
    (hRf : 1 < Rf) (hFd : DifferentiableOn ℂ F (ball 0 Rf)) (hFd' : ∀ z ∈ ball (0 : ℂ) Rf, deriv F z ≠ 0)
    (hFf : EqOn F f unitDisc)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hRL : ∫⁻ u in unitDiscExterior, ‖R u‖ₑ ^ 2 * ENNReal.ofReal (rho u) < ∞) :
    Integrable (fun q : ℂ × ℂ => conj (preSchwarzian f q.2) * (deriv f q.2 * (-(2 / π : ℂ) *
      (R q.1 * deriv g q.1 ^ 2 / (g q.1 - f q.2) ^ 3))))
      ((volume.restrict unitDiscExterior).prod (volume.restrict unitDisc)) := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have hDo : IsOpen unitDisc := isOpen_ball
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hGo : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨hgd, hg'd, -, hgG, hg'⟩ := d2e_basic hρ hGd hGi hGd' hGg
  obtain ⟨K, M, Mf, c0, hc0, hfb⟩ := s3fb_fbd hRf hFd hFd' hFf
  obtain ⟨c, hc, C, hgrow⟩ := d2e_growth hpair
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hfb 0 h0D).2.1
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hfb 0 h0D).1
  have hf'd : DifferentiableOn ℂ (deriv f) unitDisc := hpair.1.deriv hDo
  have hf'ne : ∀ z ∈ unitDisc, deriv f z ≠ 0 := fun z hz =>
    norm_pos_iff.1 (lt_of_lt_of_le hc0 (hfb z hz).2.2.2)
  have hAfc : ContinuousOn (preSchwarzian f) unitDisc :=
    (hf'd.deriv hDo).continuousOn.div hf'd.continuousOn hf'ne
  have hne : ∀ x ∈ unitDiscExterior, ∀ z ∈ unitDisc, g x - f z ≠ 0 := fun x hx z hz h =>
    Set.disjoint_left.1 hpair.2.2.2.2.2 ⟨z, hz, rfl⟩ ⟨x, hx, sub_eq_zero.1 h⟩
  have hπ : 0 < π := Real.pi_pos
  have h2π : ‖(-(2 / π : ℂ))‖ = 2 / π := by
    rw [norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg hπ.le]
    norm_num
  set Φ : ℂ × ℂ → ℂ := fun q => conj (preSchwarzian f q.2) * (deriv f q.2 * (-(2 / π : ℂ) *
    (R q.1 * deriv g q.1 ^ 2 / (g q.1 - f q.2) ^ 3))) with hΦ
  have hnorm : ∀ x : ℂ, ∀ z ∈ unitDisc, ‖Φ (x, z)‖ =
      2 / π * ‖R x‖ * ‖deriv g x‖ ^ 2 * ‖deriv (deriv f) z‖ / ‖g x - f z‖ ^ 3 := by
    intro x z hz
    have hf' : ‖deriv f z‖ ≠ 0 := norm_ne_zero_iff.2 (hf'ne z hz)
    simp only [hΦ, norm_mul, norm_div, norm_pow, Complex.norm_conj, h2π]
    rw [show preSchwarzian f z = deriv (deriv f) z / deriv f z from rfl, norm_div]
    field_simp
  -- measurability on the product
  have h1m : MapsTo Prod.fst (unitDiscExterior ×ˢ unitDisc) unitDiscExterior := fun q hq => hq.1
  have h2m : MapsTo Prod.snd (unitDiscExterior ×ˢ unitDisc) unitDisc := fun q hq => hq.2
  have hΨc : ContinuousOn (fun q : ℂ × ℂ => conj (preSchwarzian f q.2) * (deriv f q.2 * (-(2 / π : ℂ) *
      (deriv g q.1 ^ 2 / (g q.1 - f q.2) ^ 3)))) (unitDiscExterior ×ˢ unitDisc) :=
    (Complex.continuous_conj.comp_continuousOn (hAfc.comp continuousOn_snd h2m)).mul
      ((hf'd.continuousOn.comp continuousOn_snd h2m).mul (continuousOn_const.mul
      (((hg'd.continuousOn.comp continuousOn_fst h1m).pow 2).div
      (((hgd.continuousOn.comp continuousOn_fst h1m).sub (hpair.1.continuousOn.comp continuousOn_snd h2m)).pow 3)
      fun q hq => pow_ne_zero 3 (hne q.1 hq.1 q.2 hq.2))))
  have hΦm : AEStronglyMeasurable Φ ((volume.restrict unitDiscExterior).prod (volume.restrict unitDisc)) := by
    have hRm' := hRm.comp_fst (ν := volume.restrict unitDisc)
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hRm' ⊢
    have hΨm := hΨc.aestronglyMeasurable (μ := volume) (hEm.prod hDm)
    refine (hRm'.mul hΨm).congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [hΦ, Pi.mul_apply]
    ring
  -- per-point separation and integrability in `z`
  have hsep : ∀ x ∈ unitDiscExterior, 0 < ‖deriv g x‖ * (‖x‖ - 1) / 4 ∧
      ∀ z ∈ unitDisc, ‖deriv g x‖ * (‖x‖ - 1) / 4 ≤ ‖f z - g x‖ := fun x hx => by
    have hx1 : (1 : ℝ) < ‖x‖ := hx
    refine ⟨by have := norm_pos_iff.2 (hg' x hx); nlinarith, fun z hz => ?_⟩
    rw [norm_sub_rev]
    exact s3fb_gkoebe hpair hρ hGd hGi hGg hx hz
  have hxint : ∀ x ∈ unitDiscExterior, Integrable (fun z => Φ (x, z)) (volume.restrict unitDisc) := by
    intro x hx
    obtain ⟨hd0, hd⟩ := hsep x hx
    refine (integrableOn_const (C := 2 / π * ‖R x‖ * ‖deriv g x‖ ^ 2 * M /
      (‖deriv g x‖ * (‖x‖ - 1) / 4) ^ 3) measure_ball_lt_top.ne).mono' ?_
      ((ae_restrict_iff' hDm).2 (Filter.Eventually.of_forall fun z hz => ?_))
    · have h2 : MapsTo (fun z : ℂ => (x, z)) unitDisc (unitDiscExterior ×ˢ unitDisc) := fun z hz => ⟨hx, hz⟩
      have := (hΨc.comp (continuousOn_const.prodMk continuousOn_id) h2).aestronglyMeasurable (μ := volume) hDm
      refine (this.const_mul (R x)).congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [hΦ, Function.comp, id]
      ring
    · rw [hnorm x z hz]
      have h1 := (hfb z hz).2.1
      have h2 : (‖deriv g x‖ * (‖x‖ - 1) / 4) ^ 3 ≤ ‖g x - f z‖ ^ 3 :=
        pow_le_pow_left₀ hd0.le (by rw [norm_sub_rev]; exact hd z hz) 3
      have hpos : 0 ≤ 2 / π * ‖R x‖ * ‖deriv g x‖ ^ 2 := by positivity
      calc 2 / π * ‖R x‖ * ‖deriv g x‖ ^ 2 * ‖deriv (deriv f) z‖ / ‖g x - f z‖ ^ 3
          ≤ 2 / π * ‖R x‖ * ‖deriv g x‖ ^ 2 * M / ‖g x - f z‖ ^ 3 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hpos) (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) h2
  -- the annulus bound for `g'`
  set T : ℝ := max 4 (2 * K / c) with hT
  have hT4 : 4 ≤ T := le_max_left _ _
  have hTK : 2 * K / c ≤ T := le_max_right _ _
  have hAnn : IsCompact (closedBall (0 : ℂ) T ∩ {z : ℂ | 1 ≤ ‖z‖}) :=
    (isCompact_closedBall 0 T).inter_right (isClosed_le continuous_const continuous_norm)
  have hAnnsub : closedBall (0 : ℂ) T ∩ {z : ℂ | 1 ≤ ‖z‖} ⊆ {z : ℂ | ρ < ‖z‖} := fun z hz => by
    have : (1 : ℝ) ≤ ‖z‖ := hz.2
    show ρ < ‖z‖
    linarith
  obtain ⟨CT, hCT⟩ := hAnn.exists_bound_of_continuousOn ((hGd.deriv hGo).continuousOn.mono hAnnsub)
  have hg'T : ∀ x ∈ unitDiscExterior, ‖x‖ ≤ T → ‖deriv g x‖ ≤ CT := fun x hx hxT => by
    rw [hgG x hx]
    exact hCT x ⟨mem_closedBall_zero_iff.2 hxT, (show (1 : ℝ) < ‖x‖ from hx).le⟩
  -- the dominating function
  have hRρ : Integrable (fun x => ‖R x‖ ^ 2 * rho x) (volume.restrict unitDiscExterior) := by
    have hρm : Measurable rho := by
      unfold rho
      exact measurable_const.div ((measurable_const.sub (continuous_norm.measurable.pow_const 2)).pow_const 2)
    refine ⟨(hRm.norm.pow 2).mul hρm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => by unfold rho; positivity)]
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) hRL
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  set V : ℝ := (volume unitDisc).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set A1 : ℝ := 16 * (M / c0 ^ 2) * |CT| with hA1
  set A2 : ℝ := 2 / π * Rb * C ^ 2 * M / (c / 2) ^ 3 * V with hA2
  have hA10 : 0 ≤ A1 := by positivity
  have hDmi : Integrable (fun x => A1 * (‖R x‖ ^ 2 * rho x + (T + 1) ^ 2 / 4 *
      (ball (0 : ℂ) (T + 1)).indicator (fun _ => (1 : ℝ)) x) + |A2| * (‖x‖ ^ 3)⁻¹)
      (volume.restrict unitDiscExterior) := by
    refine ((hRρ.add ?_).const_mul A1).add ((d2l_powint (le_refl 3)).const_mul |A2|)
    refine Integrable.const_mul ?_ _
    refine (integrable_indicator_iff measurableSet_ball).2 ?_
    exact (integrableOn_const measure_ball_lt_top.ne).mono_measure Measure.restrict_le_self
  rw [integrable_prod_iff hΦm]
  refine ⟨(ae_restrict_iff' hEm).2 (Filter.Eventually.of_forall hxint), ?_⟩
  refine hDmi.mono' (hΦm.norm.integral_prod_right') ?_
  filter_upwards [ae_restrict_mem hEm, hRb] with x hx hRx
  have hx1 : (1 : ℝ) < ‖x‖ := hx
  obtain ⟨hd0, hd⟩ := hsep x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z => norm_nonneg _)]
  have hind0 : 0 ≤ (ball (0 : ℂ) (T + 1)).indicator (fun _ => (1 : ℝ)) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hρx : 0 ≤ rho x := by unfold rho; positivity
  have hDm0 : 0 ≤ A1 * (‖R x‖ ^ 2 * rho x + (T + 1) ^ 2 / 4 *
      (ball (0 : ℂ) (T + 1)).indicator (fun _ => (1 : ℝ)) x) := by positivity
  have hDm1 : 0 ≤ |A2| * (‖x‖ ^ 3)⁻¹ := by positivity
  by_cases hxT : ‖x‖ ≤ T
  · -- near `𝕊¹`: change of variables + AM-GM
    have hin := s3fb_inner_real hpair (fun z hz => (hfb z hz).2.2.1) hd0 hd
    have hb : ∀ z ∈ unitDisc, ‖Φ (x, z)‖ ≤ 2 / π * (M / c0 ^ 2) * ‖R x‖ * ‖deriv g x‖ ^ 2 *
        (‖deriv f z‖ ^ 2 / ‖f z - g x‖ ^ 3) := by
      intro z hz
      rw [hnorm x z hz, norm_sub_rev (g x)]
      have hc0f := (hfb z hz).2.2.2
      have hMf : ‖deriv (deriv f) z‖ ≤ M / c0 ^ 2 * ‖deriv f z‖ ^ 2 := by
        calc ‖deriv (deriv f) z‖ ≤ M := (hfb z hz).2.1
          _ = M / c0 ^ 2 * c0 ^ 2 := by field_simp
          _ ≤ M / c0 ^ 2 * ‖deriv f z‖ ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0.le hc0f 2) (by positivity)
      have hpos : 0 < ‖f z - g x‖ := lt_of_lt_of_le hd0 (hd z hz)
      calc 2 / π * ‖R x‖ * ‖deriv g x‖ ^ 2 * ‖deriv (deriv f) z‖ / ‖f z - g x‖ ^ 3
          ≤ 2 / π * ‖R x‖ * ‖deriv g x‖ ^ 2 * (M / c0 ^ 2 * ‖deriv f z‖ ^ 2) / ‖f z - g x‖ ^ 3 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hMf (by positivity)) (by positivity)
        _ = _ := by ring
    have hI : ∫ z in unitDisc, ‖Φ (x, z)‖ ≤ 2 / π * (M / c0 ^ 2) * ‖R x‖ * ‖deriv g x‖ ^ 2 *
        (4 * π / (‖deriv g x‖ * (‖x‖ - 1) / 4)) := by
      refine (setIntegral_mono_on (hxint x hx).norm (hin.1.const_mul _) hDm hb).trans ?_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hin.2 (by positivity)
    have hg0 : 0 < ‖deriv g x‖ := norm_pos_iff.2 (hg' x hx)
    have hgT := hg'T x hx hxT
    have hx1' : 0 < ‖x‖ - 1 := by linarith
    have heq : 2 / π * (M / c0 ^ 2) * ‖R x‖ * ‖deriv g x‖ ^ 2 * (4 * π / (‖deriv g x‖ * (‖x‖ - 1) / 4)) =
        32 * (M / c0 ^ 2) * ‖deriv g x‖ * (‖R x‖ / (‖x‖ - 1)) := by
      field_simp
      ring
    have hAM := s3fb_amgm hx1 (norm_nonneg (R x))
    have hind : (ball (0 : ℂ) (T + 1)).indicator (fun _ => (1 : ℝ)) x = 1 :=
      Set.indicator_of_mem (mem_ball_zero_iff.2 (by linarith)) _
    have hxT2 : (‖x‖ + 1) ^ 2 / 4 ≤ (T + 1) ^ 2 / 4 := by
      have : ‖x‖ + 1 ≤ T + 1 := by linarith
      nlinarith
    rw [heq] at hI
    refine hI.trans ?_
    rw [hind, mul_one]
    have hρe : rho x = 4 / (1 - ‖x‖ ^ 2) ^ 2 := rfl
    rw [hρe] at hDm0 ⊢
    calc 32 * (M / c0 ^ 2) * ‖deriv g x‖ * (‖R x‖ / (‖x‖ - 1))
        ≤ 32 * (M / c0 ^ 2) * |CT| * ((‖R x‖ ^ 2 * (4 / (1 - ‖x‖ ^ 2) ^ 2) + (‖x‖ + 1) ^ 2 / 4) / 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hgT.trans (le_abs_self _)) (by positivity)) hAM
            (by positivity) (by positivity)
      _ = A1 * (‖R x‖ ^ 2 * (4 / (1 - ‖x‖ ^ 2) ^ 2) + (‖x‖ + 1) ^ 2 / 4) := by rw [hA1]; ring
      _ ≤ A1 * (‖R x‖ ^ 2 * (4 / (1 - ‖x‖ ^ 2) ^ 2) + (T + 1) ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left (by linarith) hA10
      _ ≤ _ := le_add_of_nonneg_right hDm1
  · -- near `∞`: `|g(x) - f(z)| ≥ c|x|/2`
    rw [not_le] at hxT
    have hx4 : 4 ≤ ‖x‖ := by linarith
    obtain ⟨hgx, hg'x⟩ := hgrow x hx4
    have hcx : 2 * K ≤ c * ‖x‖ := by
      have := (div_le_iff₀ hc).1 (hTK.trans hxT.le)
      linarith
    have hsepx : ∀ z ∈ unitDisc, c * ‖x‖ / 2 ≤ ‖g x - f z‖ := fun z hz => by
      have h1 := (hfb z hz).1
      have h2 := norm_sub_norm_le (g x) (f z)
      linarith
    have hcx0 : 0 < c * ‖x‖ / 2 := by positivity
    set B' : ℝ := 2 / π * Rb * C ^ 2 * M / (c / 2) ^ 3 with hB'
    have hR0 : 0 ≤ Rb := (norm_nonneg _).trans hRx
    have hb : ∀ z ∈ unitDisc, ‖Φ (x, z)‖ ≤ B' * (‖x‖ ^ 3)⁻¹ := by
      intro z hz
      rw [hnorm x z hz]
      have h3 : (c * ‖x‖ / 2) ^ 3 ≤ ‖g x - f z‖ ^ 3 := pow_le_pow_left₀ hcx0.le (hsepx z hz) 3
      have hgx2 : ‖deriv g x‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg'x 2
      have hnum : 2 / π * ‖R x‖ * ‖deriv g x‖ ^ 2 * ‖deriv (deriv f) z‖ ≤ 2 / π * Rb * C ^ 2 * M :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hRx (by positivity)) hgx2 (by positivity)
          (by positivity)) (hfb z hz).2.1 (norm_nonneg _) (by positivity)
      calc 2 / π * ‖R x‖ * ‖deriv g x‖ ^ 2 * ‖deriv (deriv f) z‖ / ‖g x - f z‖ ^ 3
          ≤ 2 / π * Rb * C ^ 2 * M / (c * ‖x‖ / 2) ^ 3 :=
            div_le_div₀ (by positivity) hnum (by positivity) h3
        _ = B' * (‖x‖ ^ 3)⁻¹ := by rw [hB']; field_simp
    have hI : ∫ z in unitDisc, ‖Φ (x, z)‖ ≤ ∫ _ in unitDisc, B' * (‖x‖ ^ 3)⁻¹ :=
      setIntegral_mono_on (hxint x hx).norm (integrableOn_const measure_ball_lt_top.ne) hDm hb
    rw [setIntegral_const, smul_eq_mul] at hI
    refine hI.trans ?_
    have : V * (B' * (‖x‖ ^ 3)⁻¹) ≤ |A2| * (‖x‖ ^ 3)⁻¹ := by
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [mul_comm]
      exact le_abs_self _
    exact this.trans (le_add_of_nonneg_left hDm0)

/-- **(FB-D)** The disc part of F-FUB: Fubini for the `V̈` kernel and `h₁' - 𝒜 h₁ = K_d`. -/
theorem s3fb_disc {f g G F R : ℂ → ℂ} {ρ Rf Rb : ℝ} (hpair : IsNormalizedDisjointPair f g) (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGd' : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0) (hGg : EqOn G g unitDiscExterior)
    (hRf : 1 < Rf) (hFd : DifferentiableOn ℂ F (ball 0 Rf)) (hFd' : ∀ z ∈ ball (0 : ℂ) Rf, deriv F z ≠ 0)
    (hFf : EqOn F f unitDisc)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hRL : ∫⁻ u in unitDiscExterior, ‖R u‖ₑ ^ 2 * ENNReal.ofReal (rho u) < ∞) :
    IntegrableOn (fun z => conj (preSchwarzian f z) * (deriv f z *
        (-(2 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * deriv g ζ ^ 2 / (g ζ - f z) ^ 3))) unitDisc ∧
      IntegrableOn (fun u => R u * (-(2 / π : ℂ) * deriv g u ^ 2 *
        ∫ w in unitDisc, conj (preSchwarzian f w) * deriv f w / (g u - f w) ^ 3)) unitDiscExterior ∧
      (∫ z in unitDisc, conj (preSchwarzian f z) * (deriv f z *
        (-(2 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * deriv g ζ ^ 2 / (g ζ - f z) ^ 3))) =
        (∫ u in unitDiscExterior, R u * (-(2 / π : ℂ) * deriv g u ^ 2 *
          ∫ w in unitDisc, conj (preSchwarzian f w) * deriv f w / (g u - f w) ^ 3)) ∧
      ∀ u ∈ unitDiscExterior,
        DifferentiableAt ℂ (fun x : ℂ => (1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian f w) *
          (deriv g x * deriv f w / (g x - f w) ^ 2)) u ∧
        deriv (fun x : ℂ => (1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian f w) *
          (deriv g x * deriv f w / (g x - f w) ^ 2)) u -
          preSchwarzian g u * ((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian f w) *
            (deriv g u * deriv f w / (g u - f w) ^ 2)) =
          -(2 / π : ℂ) * deriv g u ^ 2 * ∫ w in unitDisc, conj (preSchwarzian f w) * deriv f w / (g u - f w) ^ 3 := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have hDo : IsOpen unitDisc := isOpen_ball
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hGo : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨hgd, hg'd, -, hgG, hg'⟩ := d2e_basic hρ hGd hGi hGd' hGg
  obtain ⟨K, M, Mf, c0, hc0, hfb⟩ := s3fb_fbd hRf hFd hFd' hFf
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hfb 0 h0D).2.1
  have hf'd : DifferentiableOn ℂ (deriv f) unitDisc := hpair.1.deriv hDo
  have hf'ne : ∀ z ∈ unitDisc, deriv f z ≠ 0 := fun z hz =>
    norm_pos_iff.1 (lt_of_lt_of_le hc0 (hfb z hz).2.2.2)
  have hAfc : ContinuousOn (preSchwarzian f) unitDisc :=
    (hf'd.deriv hDo).continuousOn.div hf'd.continuousOn hf'ne
  have hne : ∀ x ∈ unitDiscExterior, ∀ z ∈ unitDisc, g x - f z ≠ 0 := fun x hx z hz h =>
    Set.disjoint_left.1 hpair.2.2.2.2.2 ⟨z, hz, rfl⟩ ⟨x, hx, sub_eq_zero.1 h⟩
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hJ := s3fb_joint hpair hρ hGd hGi hGd' hGg hRf hFd hFd' hFf hRm hRb hRL
  set Φ : ℂ × ℂ → ℂ := fun q => conj (preSchwarzian f q.2) * (deriv f q.2 * (-(2 / π : ℂ) *
    (R q.1 * deriv g q.1 ^ 2 / (g q.1 - f q.2) ^ 3))) with hΦ
  have hN1 : ∀ z, conj (preSchwarzian f z) * (deriv f z *
      (-(2 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * deriv g ζ ^ 2 / (g ζ - f z) ^ 3)) =
      ∫ x in unitDiscExterior, Φ (x, z) := by
    intro z
    simp only [hΦ]
    rw [integral_const_mul, integral_const_mul, integral_const_mul]
  have hRK : ∀ u, R u * (-(2 / π : ℂ) * deriv g u ^ 2 *
      ∫ w in unitDisc, conj (preSchwarzian f w) * deriv f w / (g u - f w) ^ 3) =
      ∫ z in unitDisc, Φ (u, z) := by
    intro u
    have : (fun z => Φ (u, z)) = fun z => (R u * (-(2 / π : ℂ) * deriv g u ^ 2)) *
        (conj (preSchwarzian f z) * deriv f z / (g u - f z) ^ 3) := by
      funext z
      simp only [hΦ]
      ring
    rw [this, integral_const_mul]
    ring
  have hint1 : IntegrableOn (fun z => conj (preSchwarzian f z) * (deriv f z *
      (-(2 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * deriv g ζ ^ 2 / (g ζ - f z) ^ 3))) unitDisc := by
    simp only [hN1]
    exact hJ.integral_prod_right
  have hint2 : IntegrableOn (fun u => R u * (-(2 / π : ℂ) * deriv g u ^ 2 *
      ∫ w in unitDisc, conj (preSchwarzian f w) * deriv f w / (g u - f w) ^ 3)) unitDiscExterior := by
    simp only [hRK]
    exact hJ.integral_prod_left
  refine ⟨hint1, hint2, ?_, ?_⟩
  · simp only [hN1, hRK]
    exact (integral_integral_swap (f := fun x z => Φ (x, z)) hJ).symm
  -- the derivative of `h₁`
  intro u0 hu0
  have hu1 : (1 : ℝ) < ‖u0‖ := hu0
  set r : ℝ := (‖u0‖ - 1) / 4 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hyr : ∀ y ∈ closedBall u0 (2 * r), (‖u0‖ - 1) / 2 ≤ ‖y‖ - 1 := fun y hy => by
    have h1 : ‖y - u0‖ ≤ 2 * r := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy
    have h2 := norm_sub_norm_le u0 y
    rw [norm_sub_rev] at h2
    rw [hr] at h1
    linarith
  have hball : closedBall u0 (2 * r) ⊆ unitDiscExterior := fun y hy => by
    have := hyr y hy
    show (1 : ℝ) < ‖y‖
    linarith
  have hballρ : closedBall u0 (2 * r) ⊆ {z : ℂ | ρ < ‖z‖} := fun y hy => by
    have : (1 : ℝ) < ‖y‖ := hball hy
    show ρ < ‖y‖
    linarith
  have hKb : IsCompact (closedBall u0 (2 * r)) := isCompact_closedBall u0 (2 * r)
  have hG'd : DifferentiableOn ℂ (deriv G) {z : ℂ | ρ < ‖z‖} := hGd.deriv hGo
  obtain ⟨CG, hCG⟩ := hKb.exists_bound_of_continuousOn (hG'd.continuousOn.mono hballρ)
  obtain ⟨y0, hy0, hmin⟩ := hKb.exists_isMinOn (nonempty_closedBall.2 (by linarith))
    ((hG'd.continuousOn.mono hballρ).norm)
  have hcG : 0 < ‖deriv G y0‖ := norm_pos_iff.2 (hGd' y0 (hballρ hy0))
  set δ : ℝ := ‖deriv G y0‖ * ((‖u0‖ - 1) / 2) / 4 with hδ
  have hδ0 : 0 < δ := by
    have : 0 < (‖u0‖ - 1) / 2 := by linarith
    rw [hδ]
    positivity
  have hsepy : ∀ y ∈ closedBall u0 (2 * r), ∀ w ∈ unitDisc, δ ≤ ‖G y - f w‖ := by
    intro y hy w hw
    have hyE := hball hy
    have hk := s3fb_gkoebe hpair hρ hGd hGi hGg hyE hw
    rw [← hGg hyE, hgG y hyE] at hk
    refine le_trans ?_ hk
    rw [hδ]
    have h1 : ‖deriv G y0‖ ≤ ‖deriv G y‖ := hmin hy
    have h2 := hyr y hy
    have : 0 < (‖u0‖ - 1) / 2 := by linarith
    have : 0 ≤ ‖deriv G y0‖ := norm_nonneg _
    gcongr
  set k : ℂ → ℂ → ℂ := fun w y => conj (preSchwarzian f w) * (deriv G y * deriv f w / (G y - f w) ^ 2) with hk
  have hkd : ∀ᵐ w ∂(volume.restrict unitDisc), DifferentiableOn ℂ (k w) unitDiscExterior := by
    filter_upwards [ae_restrict_mem hDm] with w hw
    intro y hy
    have hyρ : y ∈ {z : ℂ | ρ < ‖z‖} := by
      have : (1 : ℝ) < ‖y‖ := hy
      show ρ < ‖y‖
      linarith
    have hGy : DifferentiableAt ℂ G y := hGd.differentiableAt (hGo.mem_nhds hyρ)
    have hG'y : DifferentiableAt ℂ (deriv G) y := hG'd.differentiableAt (hGo.mem_nhds hyρ)
    have hne' : G y - f w ≠ 0 := by rw [hGg hy]; exact hne y hy w hw
    exact (((hG'y.mul_const _).div ((hGy.sub_const _).pow 2) (pow_ne_zero 2 hne')).const_mul _).differentiableWithinAt
  have hkm : ∀ y ∈ unitDiscExterior, AEStronglyMeasurable (fun w => k w y) (volume.restrict unitDisc) := by
    intro y hy
    have hne' : ∀ w ∈ unitDisc, G y - f w ≠ 0 := fun w hw => by rw [hGg hy]; exact hne y hy w hw
    exact ((Complex.continuous_conj.comp_continuousOn hAfc).mul (continuousOn_const.mul
      (hf'd.continuousOn) |>.div ((continuousOn_const.sub hpair.1.continuousOn).pow 2)
      fun w hw => pow_ne_zero 2 (hne' w hw))).aestronglyMeasurable hDm
  have hkb : ∀ᵐ w ∂(volume.restrict unitDisc), ∀ y ∈ closedBall u0 (2 * r), ‖k w y‖ ≤ M * CG / δ ^ 2 := by
    filter_upwards [ae_restrict_mem hDm] with w hw y hy
    have hn : ‖k w y‖ = ‖deriv (deriv f) w‖ * ‖deriv G y‖ / ‖G y - f w‖ ^ 2 := by
      have hf' : ‖deriv f w‖ ≠ 0 := norm_ne_zero_iff.2 (hf'ne w hw)
      simp only [hk, norm_mul, norm_div, norm_pow, Complex.norm_conj]
      rw [show preSchwarzian f w = deriv (deriv f) w / deriv f w from rfl, norm_div]
      field_simp
    rw [hn]
    have h1 := (hfb w hw).2.1
    have h2 := hCG y hy
    have h3 : δ ^ 2 ≤ ‖G y - f w‖ ^ 2 := pow_le_pow_left₀ hδ0.le (hsepy y hy w hw) 2
    exact div_le_div₀ (mul_nonneg hM0 ((norm_nonneg _).trans h2)) (mul_le_mul h1 h2 (norm_nonneg _) hM0) (by positivity) h3
  obtain ⟨hki, hdki, hdk⟩ := d2p_param hE hr0 hball hkd hkm (integrableOn_const (C := M * CG / δ ^ 2) measure_ball_lt_top.ne) hkb
  -- `h₁ = (1/π) ∫ k(·, y)` near `u0`
  have hev : (fun x : ℂ => (1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian f w) *
      (deriv g x * deriv f w / (g x - f w) ^ 2)) =ᶠ[𝓝 u0]
      fun y => (1 / π : ℂ) * ∫ w in unitDisc, k w y := by
    filter_upwards [hE.mem_nhds hu0] with y hy
    simp only [hk, hGg hy, hgG y hy]
  have hD := (hdk.const_mul (1 / π : ℂ)).congr_of_eventuallyEq hev
  refine ⟨hD.differentiableAt, ?_⟩
  rw [hD.deriv]
  -- pointwise derivative of the kernel
  have hu0ρ : u0 ∈ {z : ℂ | ρ < ‖z‖} := hballρ (mem_closedBall_self (by linarith))
  have hGu : HasDerivAt G (deriv G u0) u0 := (hGd.differentiableAt (hGo.mem_nhds hu0ρ)).hasDerivAt
  have hG'u : HasDerivAt (deriv G) (deriv (deriv G) u0) u0 :=
    (hG'd.differentiableAt (hGo.mem_nhds hu0ρ)).hasDerivAt
  have hG'0 : deriv G u0 ≠ 0 := hGd' u0 hu0ρ
  have hdkw : ∀ w ∈ unitDisc, deriv (k w) u0 = conj (preSchwarzian f w) * deriv f w *
      (deriv (deriv G) u0 / (G u0 - f w) ^ 2 - 2 * deriv G u0 ^ 2 / (G u0 - f w) ^ 3) := by
    intro w hw
    have hne' : G u0 - f w ≠ 0 := by rw [hGg hu0]; exact hne u0 hu0 w hw
    have h := (((hG'u.mul_const (deriv f w)).div ((hGu.sub_const (f w)).pow 2) (pow_ne_zero 2 hne')).const_mul
      (conj (preSchwarzian f w)))
    change HasDerivAt (k w) _ u0 at h
    rw [h.deriv]
    simp only [Pi.pow_apply, Pi.div_apply, Nat.cast_ofNat]
    field_simp
    ring
  have hA : preSchwarzian g u0 = deriv (deriv G) u0 / deriv G u0 := by
    have h1 : deriv g =ᶠ[𝓝 u0] deriv G := by
      filter_upwards [hE.mem_nhds hu0] with y hy using hgG y hy
    show deriv (deriv g) u0 / deriv g u0 = _
    rw [h1.deriv_eq, hgG u0 hu0]
  rw [← hGg hu0, hgG u0 hu0, hA]
  have e1 : (∫ w in unitDisc, conj (preSchwarzian f w) * (deriv G u0 * deriv f w / (G u0 - f w) ^ 2)) =
      ∫ w in unitDisc, k w u0 := rfl
  rw [e1]
  set c : ℂ := deriv (deriv G) u0 / deriv G u0 with hc
  have e2 : (∫ w in unitDisc, (deriv (k w) u0 - c * k w u0)) =
      (∫ w in unitDisc, deriv (k w) u0) - c * ∫ w in unitDisc, k w u0 := by
    rw [integral_sub hdki (hki.const_mul c), integral_const_mul]
  have e3 : (∫ w in unitDisc, -(2 : ℂ) * deriv G u0 ^ 2 * (conj (preSchwarzian f w) * deriv f w / (G u0 - f w) ^ 3)) =
      -(2 : ℂ) * deriv G u0 ^ 2 * ∫ w in unitDisc, conj (preSchwarzian f w) * deriv f w / (G u0 - f w) ^ 3 :=
    integral_const_mul _ _
  have e4 : (∫ w in unitDisc, (deriv (k w) u0 - c * k w u0)) =
      ∫ w in unitDisc, -(2 : ℂ) * deriv G u0 ^ 2 * (conj (preSchwarzian f w) * deriv f w / (G u0 - f w) ^ 3) := by
    refine setIntegral_congr_fun hDm fun w hw => ?_
    have hne' : G u0 - f w ≠ 0 := by rw [hGg hu0]; exact hne u0 hu0 w hw
    simp only [hk, hc]
    rw [hdkw w hw]
    field_simp
    ring
  have hcomb : (∫ w in unitDisc, deriv (k w) u0) - c * ∫ w in unitDisc, k w u0 =
      -(2 : ℂ) * deriv G u0 ^ 2 * ∫ w in unitDisc, conj (preSchwarzian f w) * deriv f w / (G u0 - f w) ^ 3 := by
    rw [← e2, e4, e3]
  calc (1 / π : ℂ) * (∫ w in unitDisc, deriv (k w) u0) - c * ((1 / π : ℂ) * ∫ w in unitDisc, k w u0)
      = (1 / π : ℂ) * ((∫ w in unitDisc, deriv (k w) u0) - c * ∫ w in unitDisc, k w u0) := by ring
    _ = _ := by rw [hcomb]; ring

/-- [FB-C helper] Uniform bound for the divided difference `dslope A ζ y` (`ζ ∈ 𝔻*`, `y` near `z0`), from bounds of
`A` and `A'` on `𝔻*` and the mean value inequality on `ball z0 (3r) ⊆ 𝔻*`. -/
theorem s3fc_dslope_bd {A : ℂ → ℂ} {CA CA' : ℝ} (hAd : DifferentiableOn ℂ A unitDiscExterior)
    (hA : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ CA) (hA' : ∀ z ∈ unitDiscExterior, ‖deriv A z‖ ≤ CA')
    {z0 : ℂ} {r : ℝ} (hr : 0 < r) (hball : closedBall z0 (4 * r) ⊆ unitDiscExterior)
    {ζ y : ℂ} (hζ : ζ ∈ unitDiscExterior) (hy : y ∈ closedBall z0 (2 * r)) :
    ‖dslope A ζ y‖ ≤ 2 * CA / r + CA' := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hCA : 0 ≤ CA := (norm_nonneg _).trans (hA ζ hζ)
  have hc : 0 ≤ 2 * CA / r := by positivity
  by_cases hyζ : y = ζ
  · rw [hyζ, dslope_same]
    linarith [hA' ζ hζ]
  rw [dslope_of_ne _ hyζ, slope_def_field]
  have hyE : y ∈ unitDiscExterior := hball (closedBall_subset_closedBall (by linarith) hy)
  have hne : 0 < ‖y - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyζ)
  rw [norm_div]
  by_cases hfar : r ≤ ‖y - ζ‖
  · have h1 : ‖A y - A ζ‖ ≤ 2 * CA := (norm_sub_le _ _).trans (by linarith [hA y hyE, hA ζ hζ])
    have h2 : ‖A y - A ζ‖ / ‖y - ζ‖ ≤ 2 * CA / r := by
      rw [div_le_div_iff₀ hne hr]
      nlinarith [norm_nonneg (A y - A ζ)]
    linarith [(norm_nonneg _).trans (hA' ζ hζ)]
  · push_neg at hfar
    have hsub : ball z0 (3 * r) ⊆ unitDiscExterior :=
      ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hball)
    have hyd : dist y z0 ≤ 2 * r := mem_closedBall.mp hy
    have hyB : y ∈ ball z0 (3 * r) := mem_ball.mpr (by linarith)
    have hζB : ζ ∈ ball z0 (3 * r) := by
      refine mem_ball.mpr (lt_of_le_of_lt (dist_triangle ζ y z0) ?_)
      rw [dist_comm, dist_eq_norm]
      linarith
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := A)
      (fun x hx => hAd.differentiableAt (hO.mem_nhds (hsub hx))) (fun x hx => hA' x (hsub hx))
      (convex_ball z0 (3 * r)) hζB hyB
    have h2 : ‖A y - A ζ‖ / ‖y - ζ‖ ≤ CA' := by rw [div_le_iff₀ hne]; exact hmv
    linarith

/-- [FB-C helper] The kernel `R(ζ)/Dn(ζ) · Dn(y) · dslope A ζ y` is integrable on `𝔻*` and its integral is holomorphic
in `y ∈ 𝔻*` (`d2e_param` with the bound of `s3fc_dslope_bd`). -/
theorem s3fc_holo {A R : ℂ → ℂ} {CA CA' Rb : ℝ} (hAd : DifferentiableOn ℂ A unitDiscExterior)
    (hA : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ CA) (hA' : ∀ z ∈ unitDiscExterior, ‖deriv A z‖ ≤ CA')
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb) {z0 : ℂ} (hz0 : z0 ∈ unitDiscExterior) :
    IntegrableOn (fun ζ => R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) *
      (((z0 + 1) * (z0 + I) * (z0 - 1)) * dslope A ζ z0)) unitDiscExterior ∧
    DifferentiableAt ℂ (fun y => ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) *
      (((y + 1) * (y + I) * (y - 1)) * dslope A ζ y)) z0 := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hOm := hO.measurableSet
  have hz1 : (1 : ℝ) < ‖z0‖ := hz0
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = (‖z0‖ - 1) / 5 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrd]; linarith
  have hball : closedBall z0 (4 * r) ⊆ unitDiscExterior := by
    intro y hy
    show 1 < ‖y‖
    have h := mem_closedBall.mp hy
    have h2 : ‖z0‖ - ‖y‖ ≤ dist y z0 := by
      rw [dist_eq_norm, norm_sub_rev]; exact norm_sub_norm_le z0 y
    linarith
  have hball2 : closedBall z0 (2 * r) ⊆ unitDiscExterior :=
    (closedBall_subset_closedBall (by linarith)).trans hball
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = (‖z0‖ + 2 * r + 1) ^ 3 := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L : ℝ, L = 2 * CA / r + CA' := ⟨_, rfl⟩
  have hDc : Continuous fun u : ℂ => (u + 1) * (u + I) * (u - 1) := by fun_prop
  have hkd : ∀ᵐ ζ ∂(volume.restrict unitDiscExterior), DifferentiableOn ℂ (fun y => R ζ /
      ((ζ + 1) * (ζ + I) * (ζ - 1)) * (((y + 1) * (y + I) * (y - 1)) * dslope A ζ y)) unitDiscExterior := by
    filter_upwards [ae_restrict_mem hOm] with ζ hζ
    exact (differentiableOn_const _).mul ((by fun_prop : Differentiable ℂ fun u : ℂ =>
      (u + 1) * (u + I) * (u - 1)).differentiableOn.mul ((differentiableOn_dslope (hO.mem_nhds hζ)).mpr hAd))
  have hkm : ∀ y ∈ unitDiscExterior, AEStronglyMeasurable (fun ζ => R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) *
      (((y + 1) * (y + I) * (y - 1)) * dslope A ζ y)) (volume.restrict unitDiscExterior) := by
    intro y hy
    have h1 : AEStronglyMeasurable (fun ζ => (A y - A ζ) / (y - ζ)) (volume.restrict unitDiscExterior) :=
      ((continuousOn_const.sub hAd.continuousOn).aestronglyMeasurable hOm).div₀
        (continuous_const.sub continuous_id).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun ζ => dslope A ζ y) (volume.restrict unitDiscExterior) := by
      refine h1.congr ?_
      filter_upwards [ae_restrict_of_ae ((volume : Measure ℂ).ae_ne y)] with ζ hζ
      rw [dslope_of_ne _ (Ne.symm hζ), slope_def_field]
    exact (hRm.div₀ hDc.aestronglyMeasurable).mul (aestronglyMeasurable_const.mul h2)
  have hBi : Integrable (fun u : ℂ => max Rb 0 * M * L * ‖(u + 1) * (u + I) * (u - 1)‖⁻¹)
      (volume.restrict unitDiscExterior) := (d2e_dn_int.const_mul (max Rb 0 * M * L)).integrableOn
  have hB : ∀ᵐ ζ ∂(volume.restrict unitDiscExterior), ∀ y ∈ closedBall z0 (2 * r),
      ‖R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) * (((y + 1) * (y + I) * (y - 1)) * dslope A ζ y)‖ ≤
        max Rb 0 * M * L * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ := by
    filter_upwards [hRb, ae_restrict_mem hOm] with ζ hRζ hζ
    intro y hy
    have hdl : ‖dslope A ζ y‖ ≤ L := hLd ▸ s3fc_dslope_bd hAd hA hA' hr hball hζ hy
    have hyn : ‖y‖ ≤ ‖z0‖ + 2 * r := by
      have h := mem_closedBall.mp hy
      rw [dist_eq_norm] at h
      linarith [norm_le_insert' y z0]
    have hM : ‖(y + 1) * (y + I) * (y - 1)‖ ≤ M := by
      have e1 : ‖y + 1‖ ≤ ‖z0‖ + 2 * r + 1 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
      have e2 : ‖y + I‖ ≤ ‖z0‖ + 2 * r + 1 := (norm_add_le _ _).trans (by rw [Complex.norm_I]; linarith)
      have e3 : ‖y - 1‖ ≤ ‖z0‖ + 2 * r + 1 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
      rw [norm_mul, norm_mul, hMd, pow_three, ← mul_assoc]
      gcongr
    have hRζ' : ‖R ζ‖ ≤ max Rb 0 := hRζ.trans (le_max_left _ _)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
    rw [norm_mul, norm_mul, norm_div, div_eq_mul_inv]
    calc ‖R ζ‖ * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * (‖(y + 1) * (y + I) * (y - 1)‖ * ‖dslope A ζ y‖) ≤
        max Rb 0 * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * (M * L) := by gcongr
      _ = max Rb 0 * M * L * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ := by ring
  exact d2e_param hO hr hball2 hkd hkm hBi hB

/-- [FB-C helper] `C¹` of `Γ_W` for `W = R A`: `Γ_W = A γ̇ - (1/π) ∫ R/Dn · Dn(y) · dslope A ζ y` on `𝔻*`, a product of
`C¹` functions plus a holomorphic one. -/
theorem s3fc_C1 {A R : ℂ → ℂ} {CA CA' Rb : ℝ} (hAd : DifferentiableOn ℂ A unitDiscExterior)
    (hA : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ CA) (hA' : ∀ z ∈ unitDiscExterior, ‖deriv A z‖ ≤ CA')
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hγ : ContDiffOn ℝ 1 (fun y : ℂ => -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ *
      (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) unitDiscExterior) :
    ContDiffOn ℝ 1 (fun y : ℂ => -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * A ζ *
      (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) unitDiscExterior := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hOm := hO.measurableSet
  have hH : DifferentiableOn ℂ (fun y => ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) *
      (((y + 1) * (y + I) * (y - 1)) * dslope A ζ y)) unitDiscExterior := fun y hy =>
    (s3fc_holo hAd hA hA' hRm hRb hy).2.differentiableWithinAt
  have hHC := (hH.contDiffOn hO : ContDiffOn ℂ 1 _ _).restrict_scalars ℝ
  have hAC := (hAd.contDiffOn hO : ContDiffOn ℂ 1 A _).restrict_scalars ℝ
  have hP := (hAC.mul hγ).sub ((contDiffOn_const (c := (1 / π : ℂ))).mul hHC)
  refine hP.congr fun y hy => ?_
  have hsplit : (∫ ζ in unitDiscExterior, R ζ * A ζ *
      (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) =
      A y * (∫ ζ in unitDiscExterior, R ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) +
        ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) *
          (((y + 1) * (y + I) * (y - 1)) * dslope A ζ y) := by
    rw [← integral_const_mul, ← integral_add ((d2e_N_int hRm hRb hy).const_mul (A y)) (s3fc_holo hAd hA hA' hRm hRb hy).1]
    refine setIntegral_congr_ae hOm ?_
    filter_upwards [(volume : Measure ℂ).ae_ne y] with ζ hζy hζ
    have hD := d2e_dn_ne (show (1 : ℝ) < ‖ζ‖ from hζ)
    have h1 : ζ - y ≠ 0 := sub_ne_zero.mpr hζy
    have h2 : y - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζy)
    rw [dslope_of_ne _ (Ne.symm hζy), slope_def_field]
    generalize hDd : (ζ + 1) * (ζ + I) * (ζ - 1) = D at hD ⊢
    field_simp
    ring
  rw [hsplit]
  ring

/-- [FB-C helper] **Abstract FB-C**: for `A` holomorphic on `𝔻*` with `A = O(|ζ|⁻³)`, `A' = O(|ζ|⁻⁴)` and `R` bounded
with `γ̇ = -(1/π)∫ R Dn(y)/(Dn(ζ)(ζ - y))` of class `C¹`, the Cauchy transform `C(y) = ∫_{𝔻*} R A/(ζ - y)` is `C¹` with
`∂_y C = -π H(1_{𝔻*} R A)` a.e. (`C = -π Γ_W + P`, `P` a quadratic polynomial; `d2l_weak` for `Γ_W`). -/
theorem s3fc_abs {A R : ℂ → ℂ} {CA CA' Rb : ℝ} (hCA : 0 ≤ CA) (hCA' : 0 ≤ CA')
    (hAd : DifferentiableOn ℂ A unitDiscExterior)
    (hA : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ CA * (‖z‖ ^ 3)⁻¹)
    (hA' : ∀ z ∈ unitDiscExterior, ‖deriv A z‖ ≤ CA' * (‖z‖ ^ 4)⁻¹)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hγ : ContDiffOn ℝ 1 (fun y : ℂ => -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ *
      (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) unitDiscExterior) :
    ContDiffOn ℝ 1 (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * A ζ / (ζ - y)) unitDiscExterior ∧
    ∀ᵐ y ∂(volume.restrict unitDiscExterior),
      dz (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * A ζ / (ζ - y)) y =
        -(π : ℂ) * hilbertH (unitDiscExterior.indicator (fun ζ => R ζ * A ζ)) y := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hOm := hO.measurableSet
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hA1 : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ CA := fun z hz =>
    (hA z hz).trans (mul_le_of_le_one_right hCA (inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt hz))))
  have hA'1 : ∀ z ∈ unitDiscExterior, ‖deriv A z‖ ≤ CA' := fun z hz =>
    (hA' z hz).trans (mul_le_of_le_one_right hCA' (inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt hz))))
  have hc0 : 0 ≤ max Rb 0 * CA := mul_nonneg (le_max_right _ _) hCA
  -- `W = R A`
  have hWm : AEStronglyMeasurable (fun ζ => R ζ * A ζ) (volume.restrict unitDiscExterior) :=
    hRm.mul (hAd.continuousOn.aestronglyMeasurable hOm)
  have hWb3 : ∀ᵐ ζ ∂(volume.restrict unitDiscExterior), ‖R ζ * A ζ‖ ≤ max Rb 0 * CA * (‖ζ‖ ^ 3)⁻¹ := by
    filter_upwards [hRb, ae_restrict_mem hOm] with ζ h hζ
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (h.trans (le_max_left _ _)) (hA ζ hζ) (norm_nonneg _) (le_max_right _ _)
  have hWb : ∀ᵐ ζ ∂(volume.restrict unitDiscExterior), ‖R ζ * A ζ‖ ≤ max Rb 0 * CA := by
    filter_upwards [hWb3, ae_restrict_mem hOm] with ζ h hζ
    exact h.trans (mul_le_of_le_one_right hc0 (inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt hζ))))
  have hWj : ∀ᵐ ζ ∂(volume.restrict unitDiscExterior),
      ‖R ζ * A ζ * ζ‖ ≤ max Rb 0 * CA ∧ ‖R ζ * A ζ * ζ ^ 2‖ ≤ max Rb 0 * CA := by
    filter_upwards [hWb3, ae_restrict_mem hOm] with ζ h hζ
    have hζ1 : (1 : ℝ) < ‖ζ‖ := hζ
    have hp : 0 < ‖ζ‖ ^ 3 := by positivity
    constructor
    · rw [norm_mul]
      calc ‖R ζ * A ζ‖ * ‖ζ‖ ≤ max Rb 0 * CA * (‖ζ‖ ^ 3)⁻¹ * ‖ζ‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ ≤ max Rb 0 * CA := by
          rw [mul_assoc]
          refine mul_le_of_le_one_right hc0 ?_
          rw [inv_mul_le_iff₀ hp, mul_one]
          calc ‖ζ‖ = ‖ζ‖ ^ 1 := (pow_one _).symm
            _ ≤ ‖ζ‖ ^ 3 := pow_le_pow_right₀ hζ1.le (by norm_num)
    · rw [norm_mul, norm_pow]
      calc ‖R ζ * A ζ‖ * ‖ζ‖ ^ 2 ≤ max Rb 0 * CA * (‖ζ‖ ^ 3)⁻¹ * ‖ζ‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h (by positivity)
        _ ≤ max Rb 0 * CA := by
          rw [mul_assoc]
          refine mul_le_of_le_one_right hc0 ?_
          rw [inv_mul_le_iff₀ hp, mul_one]
          exact pow_le_pow_right₀ hζ1.le (by norm_num)
  have hW2 : MemLp (unitDiscExterior.indicator (fun ζ => R ζ * A ζ)) 2 := by
    have h6 := d2l_powint (k := 6) (by norm_num)
    refine (memLp_indicator_iff_restrict hOm).2 ?_
    refine MemLp.of_le (g := fun ζ => max Rb 0 * CA * (‖ζ‖ ^ 3)⁻¹) ?_ hWm ?_
    swap
    · filter_upwards [hWb3] with ζ h
      rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc0 (by positivity))]
    refine (memLp_two_iff_integrable_sq ((continuous_norm.pow 3).continuousOn.inv₀ (fun y hy =>
      pow_ne_zero 3 (lt_trans one_pos hy).ne') |>.aestronglyMeasurable hOm |>.const_mul _)).2 ?_
    refine (h6.const_mul ((max Rb 0 * CA) ^ 2)).congr ?_
    filter_upwards [ae_restrict_mem hOm] with ζ hζ
    show (max Rb 0 * CA) ^ 2 * (‖ζ‖ ^ 6)⁻¹ = (max Rb 0 * CA * (‖ζ‖ ^ 3)⁻¹) ^ 2
    ring
  have hDi : ∀ {V : ℂ → ℂ} {b : ℝ}, AEStronglyMeasurable V (volume.restrict unitDiscExterior) →
      (∀ᵐ ζ ∂(volume.restrict unitDiscExterior), ‖V ζ‖ ≤ b) →
      IntegrableOn (fun ζ => V ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) unitDiscExterior := fun {V b} hm hb => by
    refine (d2e_dn_int.const_mul b).integrableOn.mono'
      (hm.div₀ (by fun_prop : Continuous fun u : ℂ => ((u + 1) * (u + I) * (u - 1))).aestronglyMeasurable) ?_
    filter_upwards [hb] with u hu
    rw [norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hu (inv_nonneg.2 (norm_nonneg _))
  have hK0 := hDi hWm hWb
  have hK1 : IntegrableOn (fun ζ => R ζ * A ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) unitDiscExterior :=
    hDi (hWm.mul continuous_id.aestronglyMeasurable) (by filter_upwards [hWj] with ζ h using h.1)
  have hK2 : IntegrableOn (fun ζ => R ζ * A ζ * ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) unitDiscExterior :=
    hDi (hWm.mul (continuous_id.pow 2).aestronglyMeasurable) (by filter_upwards [hWj] with ζ h using h.2)
  obtain ⟨K0, hK0d⟩ : ∃ K, K = ∫ ζ in unitDiscExterior, R ζ * A ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) := ⟨_, rfl⟩
  obtain ⟨K1, hK1d⟩ : ∃ K, K = ∫ ζ in unitDiscExterior, R ζ * A ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) := ⟨_, rfl⟩
  obtain ⟨K2, hK2d⟩ : ∃ K, K = ∫ ζ in unitDiscExterior, R ζ * A ζ * ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1)) :=
    ⟨_, rfl⟩
  -- `Γ_W`, `P` and the decomposition `C = -π Γ_W + P`
  obtain ⟨Γ, hΓe⟩ : ∃ Γ : ℂ → ℂ, Γ = fun y => -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * A ζ *
      (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) := ⟨_, rfl⟩
  have hΓC : ContDiffOn ℝ 1 Γ unitDiscExterior := hΓe ▸ s3fc_C1 hAd hA1 hA'1 hRm hRb hγ
  have hweak := d2l_weak (W := fun ζ => R ζ * A ζ) hOm hWm hWb hW2 hK0 hK1
    (fun y _ => by rw [hΓe]) hΓC
  obtain ⟨P, hPe⟩ : ∃ P : ℂ → ℂ, P = fun w => w ^ 2 * K0 + w * (K1 + I * K0) + (K2 + I * K1 - K0) := ⟨_, rfl⟩
  generalize hCe : (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * A ζ / (ζ - y)) = C
  have hdec : ∀ y ∈ unitDiscExterior, C y = -(π : ℂ) * Γ y + P y := by
    intro y hy
    rw [← hCe, hΓe, hPe]
    simp only
    have hN := d2e_N_int hWm hWb hy
    have e : (∫ ζ in unitDiscExterior, R ζ * A ζ / (ζ - y)) =
        ∫ ζ in unitDiscExterior, (R ζ * A ζ * (((y + 1) * (y + I) * (y - 1)) /
          (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) + y ^ 2 * (R ζ * A ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) +
          y * (R ζ * A ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) + I * (R ζ * A ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) +
          (R ζ * A ζ * ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1)) + I * (R ζ * A ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) -
            R ζ * A ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) := by
      refine setIntegral_congr_ae hOm ?_
      filter_upwards [(volume : Measure ℂ).ae_ne y] with ζ hζy hζ
      have hD := d2e_dn_ne (show (1 : ℝ) < ‖ζ‖ from hζ)
      have h1 : ζ - y ≠ 0 := sub_ne_zero.mpr hζy
      generalize hDd : (ζ + 1) * (ζ + I) * (ζ - 1) = D at hD ⊢
      field_simp
      rw [← hDd]
      ring
    have j0 : IntegrableOn (fun ζ => I * (R ζ * A ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) unitDiscExterior :=
      hK0.const_mul I
    have j1 : IntegrableOn (fun ζ => I * (R ζ * A ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) unitDiscExterior :=
      hK1.const_mul I
    have j21 : IntegrableOn (fun ζ => R ζ * A ζ * ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1)) +
        I * (R ζ * A ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) unitDiscExterior := hK2.add j1
    have j3 : IntegrableOn (fun ζ => R ζ * A ζ * ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1)) +
        I * (R ζ * A ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) - R ζ * A ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))
        unitDiscExterior := j21.sub hK0
    have j2 : IntegrableOn (fun ζ => R ζ * A ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) +
        I * (R ζ * A ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) unitDiscExterior := hK1.add j0
    have i1 : IntegrableOn (fun ζ => y ^ 2 * (R ζ * A ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) unitDiscExterior :=
      hK0.const_mul _
    have i2 : IntegrableOn (fun ζ => y * (R ζ * A ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) +
        I * (R ζ * A ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))))) unitDiscExterior := j2.const_mul _
    have i01 : IntegrableOn (fun ζ => R ζ * A ζ * (((y + 1) * (y + I) * (y - 1)) /
        (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) + y ^ 2 * (R ζ * A ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))))
        unitDiscExterior := hN.add i1
    have i012 : IntegrableOn (fun ζ => R ζ * A ζ * (((y + 1) * (y + I) * (y - 1)) /
        (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) + y ^ 2 * (R ζ * A ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) +
        y * (R ζ * A ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) + I * (R ζ * A ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))))
        unitDiscExterior := i01.add i2
    rw [e, integral_add i012 j3, integral_add i01 i2, integral_add hN i1]
    simp only [integral_const_mul]
    rw [integral_add hK1 j0, integral_sub j21 hK0, integral_add hK2 j1]
    simp only [integral_const_mul]
    rw [← hK0d, ← hK1d, ← hK2d]
    generalize (∫ ζ in unitDiscExterior, R ζ * A ζ * (((y + 1) * (y + I) * (y - 1)) /
      (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) = J
    field_simp
    ring
  have hPC : ContDiff ℝ 1 P := by rw [hPe]; fun_prop
  refine ⟨((contDiffOn_const.mul hΓC).add hPC.contDiffOn).congr hdec, ?_⟩
  filter_upwards [hweak, ae_restrict_mem hOm] with y hy hyE
  rw [← hK0d, ← hK1d] at hy
  have hev : C =ᶠ[𝓝 y] fun w => -(π : ℂ) * Γ w + P w := Filter.eventuallyEq_of_mem (hO.mem_nhds hyE) hdec
  have hΓd := (hΓC.differentiableOn one_ne_zero y hyE).differentiableAt (hO.mem_nhds hyE)
  have hPd : HasDerivAt P (2 * y * K0 + (K1 + I * K0)) y := by
    rw [hPe]
    refine ((((hasDerivAt_pow 2 y).mul_const K0).add ((hasDerivAt_id y).mul_const (K1 + I * K0))).add_const
      (K2 + I * K1 - K0)).congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, one_mul]
  have e : dz C y = -(π : ℂ) * dz Γ y + dz P y := by
    show (fderiv ℝ C y 1 - I * fderiv ℝ C y I) / 2 =
      -(π : ℂ) * ((fderiv ℝ Γ y 1 - I * fderiv ℝ Γ y I) / 2) + (fderiv ℝ P y 1 - I * fderiv ℝ P y I) / 2
    rw [hev.fderiv_eq, fderiv_fun_add (hΓd.const_mul _) (hPd.differentiableAt.restrictScalars ℝ),
      fderiv_const_mul hΓd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [e, hy, dz_eq_deriv hPd.differentiableAt, hPd.deriv]
  field_simp
  ring

/-- **(FB-C)** The Cauchy transform of `R 𝒜(g)` over `𝔻*` is `C¹` on `𝔻*`, with `∂_y = -π · hilbertH(1_{𝔻*} R 𝒜(g))` a.e. -/
theorem s3fc_cauchy_dz {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    ContDiffOn ℝ 1 (fun y : ℂ => ∫ ζ in unitDiscExterior,
      RnmFun (toLinf m) a ζ * preSchwarzian (gsans (beltramiMul a κ)) ζ / (ζ - y)) unitDiscExterior ∧
    ∀ᵐ y ∂(volume.restrict unitDiscExterior),
      dz (fun y : ℂ => ∫ ζ in unitDiscExterior,
          RnmFun (toLinf m) a ζ * preSchwarzian (gsans (beltramiMul a κ)) ζ / (ζ - y)) y =
        -(π : ℂ) * hilbertH (unitDiscExterior.indicator
          (fun ζ => RnmFun (toLinf m) a ζ * preSchwarzian (gsans (beltramiMul a κ)) ζ)) y := by
  obtain ⟨hRm, hRb⟩ := d2l_R_data has m
  obtain ⟨hAd, CA, CA', hCA, hCA', hA, hA'⟩ := d2l_A_bounds hκ hκD ha has haL haD
  exact s3fc_abs hCA hCA' hAd hA hA' hRm hRb (s3d_D2_gd1_C1 hκ hκD ha has haL haD hm hmD)

/-- [FB-E/DD helper] Local linearization: near a point `p` of an open set where `G` is holomorphic,
`‖G u - G z - G'(p)(u - z)‖ ≤ ‖G'(p)‖/2 · ‖u - z‖` (continuity of `G'` and the mean value inequality). -/
theorem s3fe_loc {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hGd : DifferentiableOn ℂ G U) {p : ℂ} (hp : p ∈ U)
    (hp' : deriv G p ≠ 0) :
    ∃ δ > 0, ball p δ ⊆ U ∧ ∀ u ∈ ball p δ, ∀ z ∈ ball p δ,
      ‖G u - G z - deriv G p * (u - z)‖ ≤ ‖deriv G p‖ / 2 * ‖u - z‖ := by
  have hc : ContinuousAt (deriv G) p := ((hGd.deriv hU).differentiableAt (hU.mem_nhds hp)).continuousAt
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.mp hc (‖deriv G p‖ / 2) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.isOpen_iff.mp hU p hp
  have hB : ball p (min δ1 δ2) ⊆ U := (ball_subset_ball (min_le_right _ _)).trans h2
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, hB, fun u hu z hz => ?_⟩
  have hψ : ∀ w ∈ ball p (min δ1 δ2), HasDerivAt (fun w => G w - deriv G p * w) (deriv G w - deriv G p * 1) w :=
    fun w hw => ((hGd.differentiableAt (hU.mem_nhds (hB hw))).hasDerivAt).sub ((hasDerivAt_id' w).const_mul _)
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun w => G w - deriv G p * w)
    (C := ‖deriv G p‖ / 2) (fun w hw => (hψ w hw).differentiableAt) (fun w hw => by
      rw [(hψ w hw).deriv, mul_one, ← dist_eq_norm]
      exact (h1 (lt_of_lt_of_le (mem_ball.mp hw) (min_le_left _ _))).le) (convex_ball _ _) hz hu
  calc ‖G u - G z - deriv G p * (u - z)‖ = ‖(G u - deriv G p * u) - (G z - deriv G p * z)‖ := by
        congr 1; ring
    _ ≤ ‖deriv G p‖ / 2 * ‖u - z‖ := hmv

/-- [FB-E/DD helper] Uniform bi-Lipschitz lower bound on a compact subset of the domain of an injective holomorphic
`G` with `G' ≠ 0` (Lebesgue number for `s3fe_loc` near the diagonal, compactness away from it). -/
theorem s3fe_cpt {G : ℂ → ℂ} {U K : Set ℂ} (hU : IsOpen U) (hGd : DifferentiableOn ℂ G U) (hGi : InjOn G U)
    (hGd' : ∀ z ∈ U, deriv G z ≠ 0) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ m > 0, ∀ u ∈ K, ∀ z ∈ K, m * ‖u - z‖ ≤ ‖G u - G z‖ := by
  have hloc : ∀ p : K, ∃ δ > 0, ball (p : ℂ) δ ⊆ U ∧ ∀ u ∈ ball (p : ℂ) δ, ∀ z ∈ ball (p : ℂ) δ,
      ‖G u - G z - deriv G p * (u - z)‖ ≤ ‖deriv G p‖ / 2 * ‖u - z‖ := fun p =>
    s3fe_loc hU hGd (hKU p.2) (hGd' _ (hKU p.2))
  choose δ hδ hδU hδl using hloc
  obtain ⟨δL, hδL, hL⟩ := lebesgue_number_lemma_of_metric (c := fun p : K => ball (p : ℂ) (δ p)) hK
    (fun p => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hδ _)⟩)
  have hGc : ContinuousOn G K := hGd.continuousOn.mono hKU
  obtain ⟨m1, hm1, hm1K⟩ : ∃ m1 > 0, ∀ x ∈ K, m1 ≤ ‖deriv G x‖ := by
    by_cases hKn : K.Nonempty
    · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hKn ((hGd.deriv hU).continuousOn.mono hKU).norm
      exact ⟨‖deriv G x0‖, norm_pos_iff.mpr (hGd' x0 (hKU hx0)), fun x hx => isMinOn_iff.mp hmin x hx⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hKn⟩
  obtain ⟨S, hSd⟩ : ∃ S : Set (ℂ × ℂ), S = (K ×ˢ K) ∩ {q | δL ≤ ‖q.1 - q.2‖} := ⟨_, rfl⟩
  have hS : IsCompact S := by
    rw [hSd]
    exact (hK.prod hK).inter_right (isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm)
  obtain ⟨m2, hm2, hm2S⟩ : ∃ m2 > 0, ∀ q ∈ S, m2 ≤ ‖G q.1 - G q.2‖ := by
    by_cases hSn : S.Nonempty
    · have hcont : ContinuousOn (fun q : ℂ × ℂ => ‖G q.1 - G q.2‖) S := by
        refine ((hGc.comp continuousOn_fst fun q hq => ?_).sub (hGc.comp continuousOn_snd fun q hq => ?_)).norm
        · rw [hSd] at hq; exact hq.1.1
        · rw [hSd] at hq; exact hq.1.2
      obtain ⟨q0, hq0, hmin⟩ := hS.exists_isMinOn hSn hcont
      have hq0' := hq0
      rw [hSd] at hq0'
      have hne : q0.1 ≠ q0.2 := by
        intro h
        have := hq0'.2
        simp only [mem_setOf_eq, h, sub_self, norm_zero] at this
        linarith
      refine ⟨‖G q0.1 - G q0.2‖, norm_pos_iff.mpr (sub_ne_zero.mpr fun h =>
        hne (hGi (hKU hq0'.1.1) (hKU hq0'.1.2) h)), fun q hq => isMinOn_iff.mp hmin q hq⟩
    · exact ⟨1, one_pos, fun q hq => absurd ⟨q, hq⟩ hSn⟩
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine ⟨min (m1 / 2) (m2 / (2 * max R 0 + 1)), lt_min (by positivity) (by positivity), fun u hu z hz => ?_⟩
  by_cases hd : ‖u - z‖ < δL
  · obtain ⟨i, hi⟩ := hL u hu
    have hzb : z ∈ ball u δL := by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hd
    have h := hδl i u (hi (mem_ball_self hδL)) z (hi hzb)
    have h2 := norm_sub_norm_le (deriv G i * (u - z)) (G u - G z)
    rw [norm_mul] at h2
    have h3 : ‖deriv G i * (u - z) - (G u - G z)‖ = ‖G u - G z - deriv G i * (u - z)‖ := norm_sub_rev _ _
    have hmi := hm1K i i.2
    calc min (m1 / 2) (m2 / (2 * max R 0 + 1)) * ‖u - z‖ ≤ m1 / 2 * ‖u - z‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
      _ ≤ ‖deriv G i‖ / 2 * ‖u - z‖ := by gcongr
      _ ≤ ‖G u - G z‖ := by linarith
  · push_neg at hd
    have hq : (u, z) ∈ S := by rw [hSd]; exact ⟨⟨hu, hz⟩, hd⟩
    have hm := hm2S _ hq
    have huz : ‖u - z‖ ≤ 2 * max R 0 + 1 := by
      have := norm_sub_le u z
      linarith [hR u hu, hR z hz, le_max_left R 0]
    have hpos : 0 < 2 * max R 0 + 1 := by positivity
    calc min (m1 / 2) (m2 / (2 * max R 0 + 1)) * ‖u - z‖ ≤ m2 / (2 * max R 0 + 1) * ‖u - z‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ ≤ m2 / (2 * max R 0 + 1) * (2 * max R 0 + 1) := by gcongr
      _ = m2 := by field_simp
      _ ≤ ‖G u - G z‖ := hm

/-- **(FB-E/DD)** `∃ c > 0, ∀ u z ∈ 𝔻*, c |u - z| ≤ |g u - g z|`. -/
theorem s3fe_dd_lower {f g G : ℂ → ℂ} {ρ : ℝ} (hpair : IsNormalizedDisjointPair f g) (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGd' : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0) (hGg : EqOn G g unitDiscExterior) :
    ∃ c > 0, ∀ u ∈ unitDiscExterior, ∀ z ∈ unitDiscExterior, c * ‖u - z‖ ≤ ‖g u - g z‖ := by
  have hU : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  -- near `∞`: `g(1/s) = b/φ(s)` with `φ(s) ≈ s`
  obtain ⟨φ, b, hφd, -, hφ0, hφ1, hb, -, hgφ⟩ := g1_inverted_exterior hpair
  obtain ⟨δφ, hδφ, hφB, hφl⟩ := s3fe_loc isOpen_ball hφd (mem_ball_self one_pos) (by rw [hφ1]; exact one_ne_zero)
  rw [hφ1, norm_one] at hφl
  have hlow : ∀ s ∈ ball (0 : ℂ) δφ, ∀ t ∈ ball (0 : ℂ) δφ, 1 / 2 * ‖s - t‖ ≤ ‖φ s - φ t‖ := by
    intro s hs t ht
    have h := hφl s hs t ht
    have h2 := norm_sub_le (φ s - φ t) (φ s - φ t - 1 * (s - t))
    rw [show φ s - φ t - (φ s - φ t - 1 * (s - t)) = s - t by ring] at h2
    linarith
  have hup : ∀ s ∈ ball (0 : ℂ) δφ, ‖φ s‖ ≤ 3 / 2 * ‖s‖ := by
    intro s hs
    have h := hφl s hs 0 (mem_ball_self hδφ)
    simp only [hφ0, sub_zero] at h
    have h2 := norm_sub_norm_le (φ s) (1 * s)
    rw [one_mul] at h h2
    linarith
  obtain ⟨r1, hr1d⟩ : ∃ r1 : ℝ, r1 = min (δφ / 2) (1 / 2) := ⟨_, rfl⟩
  have hr1 : 0 < r1 := by rw [hr1d]; exact lt_min (by linarith) (by norm_num)
  have hr1δ : r1 < δφ := by rw [hr1d]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr1h : r1 ≤ 1 / 2 := by rw [hr1d]; exact min_le_right _ _
  obtain ⟨T, hTd⟩ : ∃ T : ℝ, T = r1⁻¹ := ⟨_, rfl⟩
  have hT2 : 2 ≤ T := by
    rw [hTd, show (2 : ℝ) = (1 / 2)⁻¹ by norm_num]
    exact inv_anti₀ hr1 hr1h
  have hA : ∀ u z : ℂ, T ≤ ‖u‖ → T ≤ ‖z‖ → 2 / 9 * ‖b‖ * ‖u - z‖ ≤ ‖g u - g z‖ := by
    intro u z hu hz
    have hu0 : u ≠ 0 := norm_pos_iff.mp (by linarith)
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
    have hsr : ∀ w : ℂ, T ≤ ‖w‖ → w ≠ 0 → w⁻¹ ∈ ball (0 : ℂ) δφ := fun w hw hw0 => by
      rw [mem_ball_zero_iff, norm_inv]
      exact lt_of_le_of_lt (inv_le_of_inv_le₀ hr1 (by rw [← hTd]; exact hw)) hr1δ
    have hs := hsr u hu hu0
    have ht := hsr z hz hz0
    have hg : ∀ w : ℂ, T ≤ ‖w‖ → w ≠ 0 → g w = b / φ w⁻¹ := fun w hw hw0 => by
      have := hgφ w⁻¹ (hφB (hsr w hw hw0)) (inv_ne_zero hw0)
      rwa [one_div, inv_inv] at this
    have hφne : ∀ w : ℂ, T ≤ ‖w‖ → w ≠ 0 → φ w⁻¹ ≠ 0 := fun w hw hw0 h => by
      have := hlow w⁻¹ (hsr w hw hw0) 0 (mem_ball_self hδφ)
      rw [h, hφ0, sub_zero, sub_zero, norm_zero] at this
      have : 0 < ‖w⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hw0)
      linarith
    have hφu : ‖φ u⁻¹‖ * ‖u‖ ≤ 3 / 2 := by
      have h := hup _ hs
      rw [norm_inv] at h
      calc ‖φ u⁻¹‖ * ‖u‖ ≤ 3 / 2 * ‖u‖⁻¹ * ‖u‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ = 3 / 2 := by field_simp [norm_ne_zero_iff.mpr hu0]
    have hφz : ‖φ z⁻¹‖ * ‖z‖ ≤ 3 / 2 := by
      have h := hup _ ht
      rw [norm_inv] at h
      calc ‖φ z⁻¹‖ * ‖z‖ ≤ 3 / 2 * ‖z‖⁻¹ * ‖z‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
        _ = 3 / 2 := by field_simp [norm_ne_zero_iff.mpr hz0]
    have hpu := hφne u hu hu0
    have hpz := hφne z hz hz0
    have key : g u - g z = b * (φ z⁻¹ - φ u⁻¹) / (φ u⁻¹ * φ z⁻¹) := by
      rw [hg u hu hu0, hg z hz hz0, div_sub_div _ _ hpu hpz]; ring
    have key2 : u - z = (z⁻¹ - u⁻¹) * (u * z) := by
      rw [sub_mul, mul_comm u z, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul, mul_comm z u, ← mul_assoc,
        inv_mul_cancel₀ hu0, one_mul]
    have hpos : 0 < ‖φ u⁻¹‖ * ‖φ z⁻¹‖ := mul_pos (norm_pos_iff.mpr hpu) (norm_pos_iff.mpr hpz)
    rw [key, key2, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, le_div_iff₀ hpos]
    calc 2 / 9 * ‖b‖ * (‖z⁻¹ - u⁻¹‖ * (‖u‖ * ‖z‖)) * (‖φ u⁻¹‖ * ‖φ z⁻¹‖) =
        2 / 9 * ‖b‖ * ‖z⁻¹ - u⁻¹‖ * ((‖φ u⁻¹‖ * ‖u‖) * (‖φ z⁻¹‖ * ‖z‖)) := by ring
      _ ≤ 2 / 9 * ‖b‖ * ‖z⁻¹ - u⁻¹‖ * (3 / 2 * (3 / 2)) := by gcongr
      _ = ‖b‖ * (1 / 2 * ‖z⁻¹ - u⁻¹‖) := by ring
      _ ≤ ‖b‖ * ‖φ z⁻¹ - φ u⁻¹‖ := by gcongr; exact hlow _ ht _ hs
  -- the compact annulus `1 ≤ |w| ≤ T`: `G` is bounded
  have hKc : ∀ T0 : ℝ, IsCompact {w : ℂ | 1 ≤ ‖w‖ ∧ ‖w‖ ≤ T0} := fun T0 =>
    (isCompact_closedBall (0 : ℂ) T0).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
      fun w hw => mem_closedBall_zero_iff.mpr hw.2
  have hKU : ∀ T0 : ℝ, {w : ℂ | 1 ≤ ‖w‖ ∧ ‖w‖ ≤ T0} ⊆ {z : ℂ | ρ < ‖z‖} := fun T0 w hw => by
    show ρ < ‖w‖
    linarith [hw.1]
  obtain ⟨M, hM⟩ := (hKc T).exists_bound_of_continuousOn (hGd.continuousOn.mono (hKU T))
  obtain ⟨c0, hc0, Cg, hgr⟩ := d2e_growth hpair
  obtain ⟨T', hT'd⟩ : ∃ T' : ℝ, T' = max (max T 4) (2 * M / c0) := ⟨_, rfl⟩
  have hTT' : T ≤ T' := by rw [hT'd]; exact (le_max_left _ _).trans (le_max_left _ _)
  -- the mixed case
  have hC : ∀ u ∈ unitDiscExterior, ∀ z ∈ unitDiscExterior, ‖z‖ < T → T' < ‖u‖ →
      c0 / 4 * ‖u - z‖ ≤ ‖g u - g z‖ := by
    intro u hu z hz hzT huT
    have h4 : 4 ≤ ‖u‖ := by
      have : 4 ≤ T' := by rw [hT'd]; exact (le_max_right _ _).trans (le_max_left _ _)
      linarith
    have hMu : 2 * M ≤ ‖u‖ * c0 := by
      have : 2 * M / c0 ≤ ‖u‖ := by have : 2 * M / c0 ≤ T' := by rw [hT'd]; exact le_max_right _ _
                                    linarith
      exact (div_le_iff₀ hc0).mp this
    have hgz : ‖g z‖ ≤ M := by
      rw [← hGg hz]
      exact hM z ⟨le_of_lt (show (1 : ℝ) < ‖z‖ from hz), le_of_lt hzT⟩
    have hgu := (hgr u h4).1
    have h1 := norm_sub_norm_le (g u) (g z)
    have h2 := norm_sub_le u z
    nlinarith
  -- the compact part
  obtain ⟨mB, hmB, hB⟩ := s3fe_cpt hU hGd hGi hGd' (hKc T') (hKU T')
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  refine ⟨min (min (2 / 9 * ‖b‖) mB) (c0 / 4), lt_min (lt_min (by positivity) hmB) (by positivity), ?_⟩
  intro u hu z hz
  have hu1 : (1 : ℝ) < ‖u‖ := hu
  have hz1 : (1 : ℝ) < ‖z‖ := hz
  obtain ⟨cc, hcc⟩ : ∃ cc, cc = min (min (2 / 9 * ‖b‖) mB) (c0 / 4) := ⟨_, rfl⟩
  rw [← hcc]
  have hcA : cc ≤ 2 / 9 * ‖b‖ := hcc ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hcB : cc ≤ mB := hcc ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hcC : cc ≤ c0 / 4 := hcc ▸ min_le_right _ _
  have hBg : ‖u‖ ≤ T' → ‖z‖ ≤ T' → cc * ‖u - z‖ ≤ ‖g u - g z‖ := fun h1 h2 => by
    rw [← hGg hu, ← hGg hz]
    exact (mul_le_mul_of_nonneg_right hcB (norm_nonneg _)).trans
      (hB u ⟨hu1.le, h1⟩ z ⟨hz1.le, h2⟩)
  by_cases hu' : T ≤ ‖u‖
  · by_cases hz' : T ≤ ‖z‖
    · exact (mul_le_mul_of_nonneg_right hcA (norm_nonneg _)).trans (hA u z hu' hz')
    · push_neg at hz'
      by_cases huT : ‖u‖ ≤ T'
      · exact hBg huT (by linarith)
      · push_neg at huT
        exact (mul_le_mul_of_nonneg_right hcC (norm_nonneg _)).trans (hC u hu z hz hz' huT)
  · push_neg at hu'
    by_cases hzT : ‖z‖ ≤ T'
    · exact hBg (by linarith) hzT
    · push_neg at hzT
      rw [norm_sub_rev u z, norm_sub_rev (g u) (g z)]
      exact (mul_le_mul_of_nonneg_right hcC (norm_nonneg _)).trans (hC z hz u hu hu' hzT)

/-- The reflected integrand `g_r(w) = conj A(r²/w̄)/w` is holomorphic at every `w ≠ 0` with `|w| ≤ r` (`r > 1`). -/
theorem s3h_g_diff {A : ℂ → ℂ} {ρ r : ℝ} (hρ : ρ < 1) (hAd : DifferentiableOn ℂ A {z : ℂ | ρ < ‖z‖})
    (hr : 1 < r) {w : ℂ} (hw0 : w ≠ 0) (hwr : ‖w‖ ≤ r) :
    DifferentiableAt ℂ (fun w : ℂ => conj (A ((r : ℂ) ^ 2 / conj w)) / w) w := by
  have hcw : conj w ≠ 0 := (map_ne_zero _).2 hw0
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hmem : ρ < ‖(r : ℂ) ^ 2 / conj w‖ := by
    rw [norm_div, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [lt_div_iff₀ hwpos]
    nlinarith
  have hU : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hA' : DifferentiableAt ℂ (fun u : ℂ => A ((r : ℂ) ^ 2 / u)) (conj w) :=
    (hAd.differentiableAt (hU.mem_nhds hmem)).comp (conj w) (differentiableAt_const _ |>.div differentiableAt_id hcw)
  have hN : DifferentiableAt ℂ (conj ∘ (fun u : ℂ => A ((r : ℂ) ^ 2 / u)) ∘ conj) w := by
    rw [differentiableAt_conj_conj_iff]
    exact hA'
  exact hN.div differentiableAt_id hw0

/-- `g_r` is continuous at `0` (removable zero: `|g_r(w)| ≤ C |w|² / r⁶`). -/
theorem s3h_g_cont0 {A : ℂ → ℂ} {C r : ℝ} (hA : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ C * (‖z‖ ^ 3)⁻¹) (hr : 1 < r) :
    ContinuousAt (fun w : ℂ => conj (A ((r : ℂ) ^ 2 / conj w)) / w) 0 := by
  have hr0 : 0 < r := by linarith
  show Tendsto _ (𝓝 0) (𝓝 (conj (A ((r : ℂ) ^ 2 / conj 0)) / 0))
  rw [div_zero]
  have hb : ∀ᶠ w in 𝓝 (0 : ℂ), ‖conj (A ((r : ℂ) ^ 2 / conj w)) / w‖ ≤ C / r ^ 6 * ‖w‖ ^ 2 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < r ^ 2 by positivity)] with w hw
    rw [mem_ball_zero_iff] at hw
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have hn : ‖(r : ℂ) ^ 2 / conj w‖ = r ^ 2 / ‖w‖ := by
      rw [norm_div, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    have hmem : (r : ℂ) ^ 2 / conj w ∈ unitDiscExterior := by
      show 1 < ‖(r : ℂ) ^ 2 / conj w‖
      rw [hn, one_lt_div hwpos]
      exact hw
    have h1 := hA _ hmem
    rw [hn] at h1
    rw [norm_div, Complex.norm_conj, div_le_iff₀ hwpos]
    refine h1.trans (le_of_eq ?_)
    field_simp
  refine squeeze_zero_norm' hb ?_
  have hc : Continuous fun w : ℂ => C / r ^ 6 * ‖w‖ ^ 2 := continuous_const.mul (continuous_norm.pow 2)
  simpa using hc.tendsto (0 : ℂ)

/-- **Angular integral.** For `r > 1` and `|y| ≠ r`, `∫₀^{2π} conj A(re^{iθ}) / (re^{iθ} - y) dθ` equals
`2π conj A(r²/ȳ)/y` if `|y| < r` and `0` if `|y| > r` (Cauchy's formula for `g_r`). -/
theorem s3h_circle {A : ℂ → ℂ} {ρ C r : ℝ} (hρ : ρ < 1) (hAd : DifferentiableOn ℂ A {z : ℂ | ρ < ‖z‖})
    (hA : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ C * (‖z‖ ^ 3)⁻¹) (hr : 1 < r) {y : ℂ} (hy : ‖y‖ ≠ r) :
    (∫ θ in (0 : ℝ)..2 * π, conj (A ((r : ℂ) * exp ((θ : ℂ) * I))) / ((r : ℂ) * exp ((θ : ℂ) * I) - y)) =
      if ‖y‖ < r then 2 * π * (conj (A ((r : ℂ) ^ 2 / conj y)) / y) else 0 := by
  have hr0 : 0 < r := by linarith
  set g : ℂ → ℂ := fun w : ℂ => conj (A ((r : ℂ) ^ 2 / conj w)) / w with hg
  have hgd : ∀ w ∈ closedBall (0 : ℂ) r, w ≠ 0 → DifferentiableAt ℂ g w := fun w hw hw0 =>
    s3h_g_diff hρ hAd hr hw0 (mem_closedBall_zero_iff.1 hw)
  have hgc : ContinuousOn g (closedBall (0 : ℂ) r) := fun w hw => by
    rcases eq_or_ne w 0 with rfl | hw0
    · exact (s3h_g_cont0 hA hr).continuousWithinAt
    · exact (hgd w hw hw0).continuousAt.continuousWithinAt
  have hcirc : (∮ z in C(0, r), (z - y)⁻¹ • g z) =
      I * ∫ θ in (0 : ℝ)..2 * π, conj (A ((r : ℂ) * exp ((θ : ℂ) * I))) / ((r : ℂ) * exp ((θ : ℂ) * I) - y) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, circleMap_zero, smul_eq_mul, hg]
    set w : ℂ := (r : ℂ) * exp ((θ : ℂ) * I) with hw
    have hw0 : w ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hr0.ne') (Complex.exp_ne_zero _)
    have hwc : (r : ℂ) ^ 2 / conj w = w := by
      have hcw : conj w ≠ 0 := (map_ne_zero _).2 hw0
      rw [div_eq_iff hcw, Complex.mul_conj, Complex.normSq_eq_norm_sq, hw, norm_mul, Complex.norm_exp_ofReal_mul_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      push_cast
      ring
    rw [hwc]
    field_simp
  by_cases hyr : ‖y‖ < r
  · rw [ite_eq_left hyr]
    have hyb : y ∈ ball (0 : ℂ) r := mem_ball_zero_iff.2 hyr
    have h := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable (s := {0}) (Set.countable_singleton 0)
      hyb hgc (fun x hx => hgd x (ball_subset_closedBall hx.1) hx.2)
    rw [hcirc, smul_eq_mul] at h
    have hI : I ≠ 0 := I_ne_zero
    have h2 : ∫ θ in (0 : ℝ)..2 * π, conj (A ((r : ℂ) * exp ((θ : ℂ) * I))) / ((r : ℂ) * exp ((θ : ℂ) * I) - y) =
        2 * π * g y := by
      apply mul_left_cancel₀ hI
      rw [h]
      ring
    rw [h2]
  · rw [ite_eq_right hyr]
    have hyr' : r < ‖y‖ := lt_of_le_of_ne (not_lt.1 hyr) (Ne.symm hy)
    have hne : ∀ z ∈ closedBall (0 : ℂ) r, z - y ≠ 0 := fun z hz h => by
      rw [sub_eq_zero] at h
      rw [mem_closedBall_zero_iff, h] at hz
      linarith
    have h := circleIntegral_eq_zero_of_differentiable_on_off_countable (s := {0}) (f := fun z => (z - y)⁻¹ • g z) hr0.le (Set.countable_singleton 0)
      (((continuousOn_id.sub continuousOn_const).inv₀ hne).smul hgc)
      (fun x hx => ((differentiableAt_id.sub_const y).inv
        (hne x (ball_subset_closedBall hx.1))).smul (hgd x (ball_subset_closedBall hx.1) hx.2))
    rw [hcirc] at h
    exact (mul_eq_zero.1 h).resolve_left I_ne_zero

/-- `(r²/|y|²) y = r²/ȳ`. -/
theorem s3h_refl_pt {y : ℂ} (hy0 : y ≠ 0) (r : ℝ) : (((r ^ 2 / ‖y‖ ^ 2 : ℝ)) : ℂ) * y = (r : ℂ) ^ 2 / conj y := by
  have hcy : conj y ≠ 0 := (map_ne_zero _).2 hy0
  have hn : (‖y‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hy0)
  have hyy : y * conj y = (‖y‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [eq_div_iff hcy, mul_assoc, hyy]
  push_cast
  field_simp

/-- **Ray formula.** For `|y| > 1`, `∫_{𝔻*} conj A(ζ)/(ζ - y) = π · conj (∫₁^∞ y A(s y) ds)` (polar coordinates,
`s3h_circle`, and `s = r²/|y|²`). -/
theorem s3h_C {A : ℂ → ℂ} {ρ C : ℝ} (hρ : ρ < 1) (hAd : DifferentiableOn ℂ A {z : ℂ | ρ < ‖z‖})
    (hA : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ C * (‖z‖ ^ 3)⁻¹) {y : ℂ} (hy : 1 < ‖y‖)
    (hint : IntegrableOn (fun ζ => conj (A ζ) / (ζ - y)) unitDiscExterior) :
    (∫ ζ in unitDiscExterior, conj (A ζ) / (ζ - y)) = (π : ℂ) * conj (∫ s in Ioi (1 : ℝ), y * A ((s : ℂ) * y)) := by
  have hy0 : y ≠ 0 := norm_pos_iff.1 (by linarith)
  have hyp : 0 < ‖y‖ := by linarith
  set E := unitDiscExterior with hE
  have hEm : MeasurableSet E := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hAc : ContinuousOn (fun ζ => conj (A ζ)) E :=
    Complex.continuous_conj.comp_continuousOn (hAd.continuousOn.mono fun z hz => lt_trans hρ hz)
  set G : ℂ → ℂ := E.indicator (fun ζ => conj (A ζ) / (ζ - y)) with hGdef
  have hG1 : Measurable (E.indicator fun ζ => conj (A ζ)) := by
    rw [← piecewise_eq_indicator]
    exact hAc.measurable_piecewise continuousOn_const hEm
  have hGe : G = fun ζ => (E.indicator fun ζ => conj (A ζ)) ζ * (ζ - y)⁻¹ := by
    funext ζ
    by_cases hζ : ζ ∈ E
    · rw [hGdef, indicator_of_mem hζ, indicator_of_mem hζ, div_eq_mul_inv]
    · rw [hGdef, indicator_of_notMem hζ, indicator_of_notMem hζ, zero_mul]
  have hGm : Measurable G := by
    rw [hGe]
    exact hG1.mul (measurable_id.sub_const y).inv
  have hGi : Integrable G := (integrable_indicator_iff hEm).mpr hint
  have hpt : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = (p.1 : ℂ) * exp ((p.2 : ℂ) * I) := fun p => by
    rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  set H : ℝ × ℝ → ℂ := fun p => p.1 • G ((p.1 : ℂ) * exp ((p.2 : ℂ) * I)) with hHdef
  have hpolar : (∫ ζ in E, conj (A ζ) / (ζ - y)) = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, H p := by
    rw [← integral_indicator hEm, ← Complex.integral_comp_polarCoord_symm]
    simp only [hpt]
    rfl
  have hHm : Measurable H := by
    rw [hHdef]
    exact measurable_fst.smul (hGm.comp (by fun_prop))
  have hHi : IntegrableOn H (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
    refine ⟨hHm.aestronglyMeasurable, ?_⟩
    have hl := Complex.lintegral_comp_polarCoord_symm (fun v => ‖G v‖ₑ)
    simp only [hpt] at hl
    show ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ‖H p‖ₑ < ⊤
    have he : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ‖H p‖ₑ =
        ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • ‖G ((p.1 : ℂ) * exp ((p.2 : ℂ) * I))‖ₑ := by
      refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
      rw [hHdef, enorm_smul, Real.enorm_eq_ofReal (le_of_lt hp.1), smul_eq_mul]
    rw [he, hl]
    exact hGi.2
  rw [hpolar, Measure.volume_eq_prod, setIntegral_prod H hHi]
  set K : ℝ → ℂ := fun r => r • (2 * π * (conj (A ((r : ℂ) ^ 2 / conj y)) / y)) with hKdef
  have hae : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ ‖y‖ :=
    ae_iff.2 (by simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton])
  have hinner : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioi (0 : ℝ) →
      (∫ θ in Ioo (-π) π, H (r, θ)) = (Ioi ‖y‖).indicator K r := by
    filter_upwards [hae] with r hry hr0
    have hr0' : 0 < r := hr0
    have hnorm : ∀ θ : ℝ, ‖(r : ℂ) * exp ((θ : ℂ) * I)‖ = r := fun θ => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0']
    by_cases hr1 : 1 < r
    · have hmemE : ∀ θ : ℝ, (r : ℂ) * exp ((θ : ℂ) * I) ∈ E := fun θ => by
        show 1 < ‖(r : ℂ) * exp ((θ : ℂ) * I)‖
        rw [hnorm]
        exact hr1
      set F0 : ℝ → ℂ := fun θ => conj (A ((r : ℂ) * exp ((θ : ℂ) * I))) / ((r : ℂ) * exp ((θ : ℂ) * I) - y)
        with hF0
      have hHpt : ∀ θ : ℝ, H (r, θ) = r • F0 θ := fun θ => by
        simp only [hHdef, hGdef, hF0]
        rw [indicator_of_mem (hmemE θ)]
      have hper : Function.Periodic F0 (2 * π) := by
        intro θ
        simp only [hF0]
        rw [show ((θ + 2 * π : ℝ) : ℂ) * I = (θ : ℂ) * I + 2 * π * I by push_cast; ring, Complex.exp_add,
          Complex.exp_two_pi_mul_I, mul_one]
      have hshift : (∫ θ in Ioo (-π) π, F0 θ) = ∫ θ in (0 : ℝ)..2 * π, F0 θ := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
        have := hper.intervalIntegral_add_eq (-π) 0
        rw [show -π + 2 * π = π by ring, zero_add] at this
        exact this
      simp only [hHpt]
      rw [integral_smul, hshift, hF0, s3h_circle hρ hAd hA hr1 (Ne.symm hry)]
      by_cases hyr : ‖y‖ < r
      · rw [ite_eq_left hyr, indicator_of_mem (show r ∈ Ioi ‖y‖ from hyr)]
      · rw [ite_eq_right hyr, indicator_of_notMem (show r ∉ Ioi ‖y‖ from hyr), smul_zero]
    · have hHpt : ∀ θ : ℝ, H (r, θ) = 0 := fun θ => by
        simp only [hHdef, hGdef]
        rw [indicator_of_notMem (fun h => hr1 (by have h' : 1 < ‖(r : ℂ) * exp ((θ : ℂ) * I)‖ := h; rwa [hnorm] at h')),
          smul_zero]
      have hrn : r ∉ Ioi ‖y‖ := fun h => hr1 (lt_trans hy h)
      simp only [hHpt, integral_zero]
      rw [indicator_of_notMem hrn]
  rw [setIntegral_congr_ae measurableSet_Ioi hinner, setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi ‖y‖ = Ioi ‖y‖ from inter_eq_right.mpr fun r hr => lt_trans hyp hr]
  -- the substitution `u = r²/|y|²`
  have himg : (fun r : ℝ => r ^ 2 / ‖y‖ ^ 2) '' Ioi ‖y‖ = Ioi 1 := by
    ext u
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : ‖y‖ < r := hr
      show 1 < r ^ 2 / ‖y‖ ^ 2
      rw [one_lt_div (by positivity)]
      exact pow_lt_pow_left₀ hr' hyp.le two_ne_zero
    · intro hu
      have hu' : 1 < u := hu
      refine ⟨‖y‖ * Real.sqrt u, ?_, ?_⟩
      · show ‖y‖ < ‖y‖ * Real.sqrt u
        have : 1 < Real.sqrt u := by rw [Real.lt_sqrt zero_le_one]; simpa using hu'
        nlinarith
      · show (‖y‖ * Real.sqrt u) ^ 2 / ‖y‖ ^ 2 = u
        rw [mul_pow, Real.sq_sqrt (by linarith)]
        field_simp
  have hinj : InjOn (fun r : ℝ => r ^ 2 / ‖y‖ ^ 2) (Ioi ‖y‖) := by
    intro a ha b hb hab
    have ha' : 0 < a := lt_trans hyp ha
    have hb' : 0 < b := lt_trans hyp hb
    have h2 : a ^ 2 = b ^ 2 := by
      have hn : ‖y‖ ^ 2 ≠ 0 := by positivity
      have := hab
      simp only at this
      field_simp at this
      linarith
    exact (pow_left_inj₀ ha'.le hb'.le two_ne_zero).1 h2
  have hsub := integral_image_eq_integral_abs_deriv_smul (f := fun r : ℝ => r ^ 2 / ‖y‖ ^ 2)
    (f' := fun r : ℝ => 2 * r / ‖y‖ ^ 2) (measurableSet_Ioi : MeasurableSet (Ioi ‖y‖))
    (fun r _ => HasDerivAt.hasDerivWithinAt (by
      convert (hasDerivAt_pow 2 r).div_const (‖y‖ ^ 2) using 1
      norm_num)) hinj (fun u : ℝ => ((π * ‖y‖ ^ 2 : ℝ) : ℂ) * (conj (A ((u : ℂ) * y)) / y))
  rw [himg] at hsub
  have hK : ∀ r ∈ Ioi ‖y‖, K r = |2 * r / ‖y‖ ^ 2| • (((π * ‖y‖ ^ 2 : ℝ) : ℂ) *
      (conj (A (((r ^ 2 / ‖y‖ ^ 2 : ℝ) : ℂ) * y)) / y)) := fun r hr => by
    have hr' : 0 < r := lt_trans hyp hr
    have hn : (‖y‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hyp.ne'
    rw [hKdef, s3h_refl_pt hy0, abs_of_pos (by positivity)]
    simp only [Complex.real_smul]
    push_cast
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hK, ← hsub]
  have hyy : ((‖y‖ ^ 2 : ℝ) : ℂ) / y = conj y := by
    rw [div_eq_iff hy0, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hpt2 : ∀ u : ℝ, ((π * ‖y‖ ^ 2 : ℝ) : ℂ) * (conj (A ((u : ℂ) * y)) / y) =
      (π : ℂ) * conj (y * A ((u : ℂ) * y)) := fun u => by
    rw [map_mul, ← hyy]
    push_cast
    ring
  simp only [hpt2]
  rw [integral_const_mul, integral_conj]

/-- Cauchy estimate: `|A'(z)| ≤ 2C/(δ s⁴)` when `|z| ≥ s(1 + δ)`, `s ≥ 1`. -/
theorem s3h_dA {A : ℂ → ℂ} {ρ C δ : ℝ} (hρ : ρ < 1) (hAd : DifferentiableOn ℂ A {z : ℂ | ρ < ‖z‖})
    (hA : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ C * (‖z‖ ^ 3)⁻¹) (hC : 0 ≤ C) (hδ : 0 < δ) {s : ℝ} (hs : 1 ≤ s)
    {z : ℂ} (hz : s * (1 + δ) ≤ ‖z‖) : ‖deriv A z‖ ≤ 2 * C / (δ * s ^ 4) := by
  have hs0 : 0 < s := by linarith
  set R : ℝ := s * δ / 2 with hR
  have hR0 : 0 < R := by positivity
  have hfar : ∀ w ∈ closedBall z R, s * (1 + δ / 2) ≤ ‖w‖ := fun w hw => by
    have h1 : ‖z‖ - ‖w‖ ≤ ‖z - w‖ := norm_sub_norm_le z w
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at hw
    nlinarith
  have hd : DiffContOnCl ℂ A (ball z R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z hR0.ne']
    refine hAd.mono fun w hw => ?_
    have := hfar w hw
    show ρ < ‖w‖
    nlinarith
  have hb : ∀ w ∈ sphere z R, ‖A w‖ ≤ C * (s ^ 3)⁻¹ := fun w hw => by
    have h1 := hfar w (sphere_subset_closedBall hw)
    have hws : s ≤ ‖w‖ := by nlinarith
    have hw1 : w ∈ unitDiscExterior := by
      show 1 < ‖w‖
      nlinarith
    refine (hA w hw1).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hs0.le hws 3)
  refine (norm_deriv_le_of_forall_mem_sphere_norm_le hR0 hd hb).trans (le_of_eq ?_)
  rw [hR]
  field_simp

/-- **Holomorphy of the ray integral** `F(y) = ∫₁^∞ y A(s y) ds` on `|y| > 1` (dominated differentiation). -/
theorem s3h_F_diff {A : ℂ → ℂ} {ρ C : ℝ} (hρ : ρ < 1) (hAd : DifferentiableOn ℂ A {z : ℂ | ρ < ‖z‖})
    (hA : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ C * (‖z‖ ^ 3)⁻¹) (hC : 0 ≤ C) {y₀ : ℂ} (hy₀ : 1 < ‖y₀‖) :
    DifferentiableAt ℂ (fun y : ℂ => ∫ s in Ioi (1 : ℝ), y * A ((s : ℂ) * y)) y₀ := by
  set δ : ℝ := (‖y₀‖ - 1) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hU : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hball : ∀ y ∈ ball y₀ δ, 1 + δ ≤ ‖y‖ ∧ ‖y‖ ≤ ‖y₀‖ + δ := fun y hy => by
    rw [mem_ball, dist_eq_norm] at hy
    have h1 : ‖y₀‖ - ‖y‖ ≤ ‖y - y₀‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le y₀ y
    have h2 : ‖y‖ - ‖y₀‖ ≤ ‖y - y₀‖ := norm_sub_norm_le y y₀
    constructor <;> linarith
  have hsy : ∀ (s : ℝ) (y : ℂ), 0 < s → ‖(s : ℂ) * y‖ = s * ‖y‖ := fun s y hs => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hmemU : ∀ (s : ℝ) (y : ℂ), 1 < s → 1 < ‖y‖ → (s : ℂ) * y ∈ {z : ℂ | ρ < ‖z‖} := fun s y hs hy => by
    show ρ < ‖(s : ℂ) * y‖
    rw [hsy s y (by linarith)]
    nlinarith
  have hmemE : ∀ (s : ℝ) (y : ℂ), 1 < s → 1 < ‖y‖ → (s : ℂ) * y ∈ unitDiscExterior := fun s y hs hy => by
    show 1 < ‖(s : ℂ) * y‖
    rw [hsy s y (by linarith)]
    nlinarith
  have hcont : ∀ y : ℂ, 1 < ‖y‖ → ContinuousOn (fun s : ℝ => y * A ((s : ℂ) * y)) (Ioi 1) := fun y hy =>
    continuousOn_const.mul (hAd.continuousOn.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
      fun s hs => hmemU s y hs hy)
  have hdA : DifferentiableOn ℂ (deriv A) {z : ℂ | ρ < ‖z‖} := hAd.deriv hU
  set F' : ℂ → ℝ → ℂ := fun y s => A ((s : ℂ) * y) + y * ((s : ℂ) * deriv A ((s : ℂ) * y)) with hF'
  set K : ℝ := C + (‖y₀‖ + δ) * (2 * C / δ) with hK
  have hpow : ∀ s : ℝ, 0 < s → (s ^ 3)⁻¹ = s ^ (-3 : ℝ) := fun s hs => by
    rw [Real.rpow_neg hs.le]
    norm_cast
  have hbi : IntegrableOn (fun s : ℝ => K * s ^ (-3 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) zero_lt_one).const_mul K
  have hAb : ∀ (s : ℝ) (y : ℂ), 1 < s → 1 ≤ ‖y‖ → 1 < ‖y‖ → ‖A ((s : ℂ) * y)‖ ≤ C * (s ^ 3)⁻¹ :=
    fun s y hs hy1 hy => by
      refine (hA _ (hmemE s y hs hy)).trans (mul_le_mul_of_nonneg_left ?_ hC)
      rw [hsy s y (by linarith)]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by nlinarith) 3)
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun y s => y * A ((s : ℂ) * y)) (F' := F') (bound := fun s => K * s ^ (-3 : ℝ))
    (x₀ := y₀) (ball_mem_nhds y₀ hδ)
    (by
      filter_upwards [ball_mem_nhds y₀ hδ] with y hy
      exact (hcont y (by linarith [(hball y hy).1])).aestronglyMeasurable measurableSet_Ioi)
    (by
      refine Integrable.mono' (hbi.const_mul ‖y₀‖) ((hcont y₀ hy₀).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs' : 1 < s := hs
      rw [norm_mul, ← hpow s (by linarith)]
      have := hAb s y₀ hs' hy₀.le hy₀
      have hKC : C ≤ K := by
        rw [hK]
        have : 0 ≤ (‖y₀‖ + δ) * (2 * C / δ) := by positivity
        linarith
      calc ‖y₀‖ * ‖A ((s : ℂ) * y₀)‖ ≤ ‖y₀‖ * (C * (s ^ 3)⁻¹) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ ≤ ‖y₀‖ * (K * (s ^ 3)⁻¹) := by gcongr)
    (by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine (hAd.continuousOn.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
        fun s hs => hmemU s y₀ hs hy₀).add (continuousOn_const.mul
          ((Complex.continuous_ofReal.continuousOn).mul (hdA.continuousOn.comp
            (Complex.continuous_ofReal.mul continuous_const).continuousOn fun s hs => hmemU s y₀ hs hy₀))))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs y hy
      have hs' : 1 < s := hs
      obtain ⟨hy1, hy2⟩ := hball y hy
      have hy1' : 1 < ‖y‖ := by linarith
      have h1 := hAb s y hs' (by linarith) hy1'
      have h2 := s3h_dA hρ hAd hA hC hδ hs'.le (z := (s : ℂ) * y) (by rw [hsy s y (by linarith)]; nlinarith)
      have hs0 : 0 < s := by linarith
      rw [← hpow s hs0]
      calc ‖F' y s‖ ≤ ‖A ((s : ℂ) * y)‖ + ‖y‖ * (s * ‖deriv A ((s : ℂ) * y)‖) := by
            refine (norm_add_le _ _).trans (le_of_eq ?_)
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
        _ ≤ C * (s ^ 3)⁻¹ + (‖y₀‖ + δ) * (s * (2 * C / (δ * s ^ 4))) := by gcongr
        _ = K * (s ^ 3)⁻¹ := by
            rw [hK]
            field_simp)
    hbi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs y hy
      have hs' : 1 < s := hs
      have hy1' : 1 < ‖y‖ := by linarith [(hball y hy).1]
      have hAs : HasDerivAt A (deriv A ((s : ℂ) * y)) ((s : ℂ) * y) :=
        (hAd.differentiableAt (hU.mem_nhds (hmemU s y hs' hy1'))).hasDerivAt
      have h := (hasDerivAt_id y).mul (hAs.comp y ((hasDerivAt_id y).const_mul (s : ℂ)))
      exact h.congr_deriv (by
        show 1 * A ((s : ℂ) * y) + y * (deriv A ((s : ℂ) * y) * ((s : ℂ) * 1)) =
          A ((s : ℂ) * y) + y * ((s : ℂ) * deriv A ((s : ℂ) * y))
        ring))
  exact hres.2.differentiableAt

/-- `∂̄ F = 0` at a point of complex differentiability. -/
theorem s3h_dzbar_holo {F : ℂ → ℂ} {y : ℂ} (hF : DifferentiableAt ℂ F y) : dzbar F y = 0 := by
  have h : fderiv ℝ F y = (fderiv ℂ F y).restrictScalars ℝ := hF.fderiv_restrictScalars ℝ
  have hI : fderiv ℂ F y I = I * fderiv ℂ F y 1 := by
    rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
  have hI' : fderiv ℝ F y I = I * fderiv ℝ F y 1 := by rw [h]; exact hI
  have h1 : fderiv ℝ F y 1 = fderiv ℂ F y 1 := by rw [h]; rfl
  show (fderiv ℝ F y 1 + I * fderiv ℝ F y I) / 2 = 0
  rw [hI', h1]
  have hII : I * (I * fderiv ℂ F y 1) = -fderiv ℂ F y 1 := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  rw [hII, add_neg_cancel, zero_div]

/-- A function bounded by `M |Dn|⁻¹` on `𝔻*` is integrable there (`d2e_dn_int`). -/
theorem s3h_int_dn {f : ℂ → ℂ} (hfm : AEStronglyMeasurable f (volume.restrict unitDiscExterior)) {M : ℝ}
    (hb : ∀ ζ ∈ unitDiscExterior, ‖f ζ‖ ≤ M * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹) :
    IntegrableOn f unitDiscExterior := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  refine Integrable.mono' (d2e_dn_int.integrableOn.const_mul M) hfm ?_
  filter_upwards [ae_restrict_mem hEm] with ζ hζ using hb ζ hζ

/-- **(H-VANISH)** `hilbertH (1_{𝔻*} · conj A) = 0` a.e. on `𝔻*` for `A` holomorphic on `{ρ < |z|}`, `ρ < 1`, with
`|A z| ≤ C |z|⁻³` on `𝔻*`. -/
theorem s3f_hvanish {A : ℂ → ℂ} {ρ C : ℝ} (hρ : ρ < 1) (hAd : DifferentiableOn ℂ A {z : ℂ | ρ < ‖z‖})
    (hA : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ C * (‖z‖ ^ 3)⁻¹) :
    ∀ᵐ u ∂(volume.restrict unitDiscExterior),
      hilbertH (unitDiscExterior.indicator (fun z => conj (A z))) u = 0 := by
  set C' : ℝ := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hA' : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ C' * (‖z‖ ^ 3)⁻¹ := fun z hz =>
    (hA z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  set E := unitDiscExterior with hE
  have hEo : IsOpen E := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet E := hEo.measurableSet
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  set W : ℂ → ℂ := fun z => conj (A z) with hWdef
  have hWc : ContinuousOn W E :=
    Complex.continuous_conj.comp_continuousOn (hAd.continuousOn.mono fun z hz => lt_trans hρ hz)
  have hWm : AEStronglyMeasurable W (volume.restrict E) := hWc.aestronglyMeasurable hEm
  have hWn : ∀ ζ ∈ E, ‖W ζ‖ ≤ C' * (‖ζ‖ ^ 3)⁻¹ := fun ζ hζ => by
    rw [hWdef, Complex.norm_conj]
    exact hA' ζ hζ
  have hWb1 : ∀ ζ ∈ E, ∀ j : ℕ, j ≤ 3 → ‖W ζ‖ * ‖ζ‖ ^ j ≤ C' := fun ζ hζ j hj => by
    have h1 : (1 : ℝ) < ‖ζ‖ := hζ
    have h3 : 0 < ‖ζ‖ ^ 3 := by positivity
    calc ‖W ζ‖ * ‖ζ‖ ^ j ≤ C' * (‖ζ‖ ^ 3)⁻¹ * ‖ζ‖ ^ 3 :=
          mul_le_mul (hWn ζ hζ) (pow_le_pow_right₀ h1.le hj) (by positivity) (by positivity)
      _ = C' := by field_simp
  have hWb : ∀ᵐ ζ ∂(volume.restrict E), ‖W ζ‖ ≤ C' := by
    filter_upwards [ae_restrict_mem hEm] with ζ hζ
    simpa using hWb1 ζ hζ 0 (by norm_num)
  have hIm : Measurable (E.indicator W) := by
    rw [← piecewise_eq_indicator]
    exact hWc.measurable_piecewise continuousOn_const hEm
  have hW2 : MemLp (E.indicator W) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hIm.aestronglyMeasurable]
    have hg : Integrable (E.indicator fun z : ℂ => C' ^ 2 * (‖z‖ ^ 6)⁻¹) :=
      (integrable_indicator_iff hEm).2 ((d2l_powint (by norm_num : 3 ≤ 6)).const_mul (C' ^ 2))
    refine hg.mono' (hIm.norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ E
    · rw [indicator_of_mem hz, indicator_of_mem hz, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := hWn z hz
      have h0 : 0 ≤ ‖W z‖ := norm_nonneg _
      calc ‖W z‖ ^ 2 ≤ (C' * (‖z‖ ^ 3)⁻¹) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = C' ^ 2 * (‖z‖ ^ 6)⁻¹ := by ring
    · rw [indicator_of_notMem hz, indicator_of_notMem hz]
      simp
  -- the kernel integrands `W ζʲ / Dn ζ`, `j = 0, 1, 2`
  have hKj : ∀ j : ℕ, j ≤ 3 → IntegrableOn (fun ζ => W ζ * ζ ^ j / ((ζ + 1) * (ζ + I) * (ζ - 1))) E := fun j hj => by
    refine s3h_int_dn ((hWm.aemeasurable.mul (measurable_id.pow_const j).aemeasurable).div
      (by fun_prop : Measurable fun ζ : ℂ => (ζ + 1) * (ζ + I) * (ζ - 1)).aemeasurable).aestronglyMeasurable (M := C')
      fun ζ hζ => ?_
    rw [norm_div, norm_mul, norm_pow, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hWb1 ζ hζ j hj) (by positivity)
  have hK0 : IntegrableOn (fun ζ => W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) E := by
    simpa using hKj 0 (by norm_num)
  have hK1 : IntegrableOn (fun ζ => W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) E := by
    simpa using hKj 1 (by norm_num)
  have hK2 := hKj 2 (by norm_num)
  set K0 := ∫ ζ in E, W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) with hK0d
  set K1 := ∫ ζ in E, W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) with hK1d
  set K2 := ∫ ζ in E, W ζ * ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1)) with hK2d
  set F : ℂ → ℂ := fun y : ℂ => ∫ s in Ioi (1 : ℝ), y * A ((s : ℂ) * y) with hFdef
  have hFd : ∀ y ∈ E, DifferentiableAt ℂ F y := fun y hy => s3h_F_diff hρ hAd hA' hC0 hy
  set Γ : ℂ → ℂ := fun y => -(1 / π : ℂ) * ∫ ζ in E, W ζ * (((y + 1) * (y + I) * (y - 1)) /
    (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) with hΓdef
  set P : ℂ → ℂ := fun y => (1 / π : ℂ) * ((y ^ 2 + I * y - 1) * K0 + (y + I) * K1 + K2) with hPdef
  set Φ : ℂ → ℂ := fun y => P y - conj (F y) with hΦdef
  -- `Γ = Φ` on `𝔻*`: the kernel split and the ray formula
  have hΓΦ : ∀ y ∈ E, Γ y = Φ y := fun y hy => by
    have hN := d2e_N_int hWm hWb hy
    have hae : ∀ᵐ ζ ∂(volume.restrict E), ζ ∈ E ∧ ζ ≠ y := by
      have hne : ∀ᵐ ζ ∂(volume : Measure ℂ), ζ ≠ y :=
        ae_iff.2 (by simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton])
      filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae hne] with ζ h1 h2 using ⟨h1, h2⟩
    have hsplit : ∀ ζ ∈ E, ζ ≠ y → W ζ / (ζ - y) = W ζ * (((y + 1) * (y + I) * (y - 1)) /
        (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) + (y ^ 2 + I * y - 1) * (W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) +
        (y + I) * (W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) + W ζ * ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1)) :=
      fun ζ hζ hζy => by
        have hD := d2e_dn_ne (u := ζ) hζ
        have hs : ζ - y ≠ 0 := sub_ne_zero.2 hζy
        have key : (y + 1) * (y + I) * (y - 1) + ((y ^ 2 + I * y - 1) + (y + I) * ζ + ζ ^ 2) * (ζ - y) =
            (ζ + 1) * (ζ + I) * (ζ - 1) := by ring
        have h1 : (1 : ℂ) / (ζ - y) = ((y + 1) * (y + I) * (y - 1) + ((y ^ 2 + I * y - 1) + (y + I) * ζ + ζ ^ 2) *
            (ζ - y)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)) := by
          rw [key, div_mul_cancel_left₀ hD, one_div]
        have h2 : ((y + 1) * (y + I) * (y - 1) + ((y ^ 2 + I * y - 1) + (y + I) * ζ + ζ ^ 2) * (ζ - y)) /
            (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)) = ((y + 1) * (y + I) * (y - 1)) /
            (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)) + ((y ^ 2 + I * y - 1) + (y + I) * ζ + ζ ^ 2) /
            ((ζ + 1) * (ζ + I) * (ζ - 1)) := by
          rw [add_div, mul_div_mul_right _ _ hs]
        rw [div_eq_mul_one_div (W ζ), h1, h2]
        ring
    have hint : IntegrableOn (fun ζ => conj (A ζ) / (ζ - y)) E := by
      refine IntegrableOn.congr_fun_ae (((hN.add (hK0.const_mul (y ^ 2 + I * y - 1))).add
        (hK1.const_mul (y + I))).add hK2) ?_
      filter_upwards [hae] with ζ hζ
      exact (hsplit ζ hζ.1 hζ.2).symm
    have i1 : IntegrableOn (fun ζ => W ζ * (((y + 1) * (y + I) * (y - 1)) /
        (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) + (y ^ 2 + I * y - 1) * (W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) E :=
      hN.add (hK0.const_mul _)
    have i2 : IntegrableOn (fun ζ => W ζ * (((y + 1) * (y + I) * (y - 1)) /
        (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) + (y ^ 2 + I * y - 1) * (W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) +
        (y + I) * (W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) E :=
      i1.add (hK1.const_mul _)
    have hI : (∫ ζ in E, conj (A ζ) / (ζ - y)) = (∫ ζ in E, W ζ * (((y + 1) * (y + I) * (y - 1)) /
        (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) + (y ^ 2 + I * y - 1) * K0 + (y + I) * K1 + K2 := by
      have hsum : (∫ ζ in E, conj (A ζ) / (ζ - y)) = ∫ ζ in E, (W ζ * (((y + 1) * (y + I) * (y - 1)) /
          (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) + (y ^ 2 + I * y - 1) * (W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) +
          (y + I) * (W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) + W ζ * ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with ζ hζ
        exact hsplit ζ hζ.1 hζ.2
      rw [hsum, integral_add i2 hK2, integral_add i1 (hK1.const_mul _), integral_add hN (hK0.const_mul _),
        integral_const_mul, integral_const_mul]
    have hCy := s3h_C hρ hAd hA' hy hint
    rw [hCy] at hI
    simp only [hΓdef, hΦdef, hPdef]
    rw [show (∫ ζ in E, W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) =
      (π : ℂ) * conj (F y) - ((y ^ 2 + I * y - 1) * K0 + (y + I) * K1 + K2) by rw [hFdef]; linear_combination -hI]
    field_simp
    ring
  -- regularity of `Φ`
  have hPd : ∀ y, HasDerivAt P ((1 / π : ℂ) * ((2 * y + I) * K0 + K1)) y := fun y => by
    have h := ((((hasDerivAt_pow 2 y).add ((hasDerivAt_id y).const_mul I)).sub_const 1).mul_const K0).add
      (((hasDerivAt_id y).add_const I).mul_const K1) |>.add_const K2 |>.const_mul (1 / π : ℂ)
    exact h.congr_deriv (by norm_num)
  have hFC : ContDiffOn ℝ 1 F E :=
    ((DifferentiableOn.contDiffOn (fun y hy => (hFd y hy).differentiableWithinAt) hEo).restrict_scalars ℝ)
  have hΦC : ContDiffOn ℝ 1 Φ E := by
    have hP : ContDiff ℝ 1 P := by
      rw [hPdef]
      fun_prop
    have hcF : ContDiffOn ℝ 1 (fun y => conj (F y)) E :=
      Complex.conjCLE.contDiff.comp_contDiffOn hFC
    exact hP.contDiffOn.sub hcF
  have hΓC : ContDiffOn ℝ 1 Γ E := hΦC.congr hΓΦ
  have hW := d2l_weak hEm hWm hWb hW2 hK0 hK1 (fun y _ => rfl) hΓC
  have hdz : ∀ y ∈ E, dz Γ y = (1 / π : ℂ) * ((2 * y + I) * K0 + K1) := fun y hy => by
    have hev : Γ =ᶠ[𝓝 y] Φ := Filter.eventuallyEq_of_mem (hEo.mem_nhds hy) hΓΦ
    have hf : fderiv ℝ Γ y = fderiv ℝ Φ y := hev.fderiv_eq
    have h1 : dz Γ y = dz Φ y := congrArg (fun L : ℂ →L[ℝ] ℂ => (L 1 - I * L I) / 2) hf
    have hFr : DifferentiableAt ℝ F y := (hFd y hy).restrictScalars ℝ
    have hcF : DifferentiableAt ℝ (fun w => conj (F w)) y :=
      Complex.conjCLE.differentiableAt.comp y hFr
    rw [h1, dz_sub_pointwise ((hPd y).differentiableAt.restrictScalars ℝ) hcF, dz_conj hFr, s3h_dzbar_holo (hFd y hy),
      map_zero, sub_zero, dz_eq_deriv (hPd y).differentiableAt, (hPd y).deriv]
  filter_upwards [hW, ae_restrict_mem hEm] with y hy hyE
  rw [hdz y hyE] at hy
  linear_combination -hy

/-- (FB-E/QD helper) Second-order expansion of `g` at `∞`: `g(ζ) = bζ + b₀ + O(1/ζ)`, `g'(ζ) = b + O(ζ⁻²)`, `b ≠ 0`.
From `F̂(w) = 1/G(1/w)` (removable at `0`, injective, so `F̂'(0) ≠ 0`): `G(ζ) = ζ P(1/ζ)` with `P = 1/dslope F̂ 0`. -/
theorem s3fe_qd_exp {g G : ℂ → ℂ} {ρ : ℝ} (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGg : EqOn G g unitDiscExterior) (hinf : Tendsto g (cocompact ℂ) (cocompact ℂ)) :
    ∃ b b₀ : ℂ, b ≠ 0 ∧ ∃ T M : ℝ, 1 ≤ T ∧ 0 ≤ M ∧ ∀ ζ : ℂ, T ≤ ‖ζ‖ →
      ‖g ζ - b * ζ - b₀‖ ≤ M * ‖ζ‖⁻¹ ∧ ‖deriv g ζ - b‖ ≤ M * (‖ζ‖ ^ 2)⁻¹ := by
  -- `|g| ≥ 1` far out
  have hev : ∀ᶠ z in cocompact ℂ, (1 : ℝ) ≤ ‖g z‖ :=
    hinf.eventually (tendsto_norm_cocompact_atTop.eventually_ge_atTop 1)
  obtain ⟨t, ht, hts⟩ := mem_cocompact.1 hev
  obtain ⟨R1, hR1⟩ := ht.isBounded.subset_closedBall 0
  set R0 : ℝ := max (R1 + 1) 2 with hR0
  have hR02 : 2 ≤ R0 := le_max_right _ _
  have hgR : ∀ z : ℂ, R0 ≤ ‖z‖ → 1 ≤ ‖g z‖ := fun z hz => hts fun hzt => by
    have h1 := mem_closedBall_zero_iff.1 (hR1 hzt)
    have h2 : R1 + 1 ≤ R0 := le_max_left _ _
    linarith
  have hGE : ∀ z : ℂ, R0 ≤ ‖z‖ → z ∈ unitDiscExterior := fun z hz => by
    show 1 < ‖z‖
    linarith
  have hGρ : ∀ z : ℂ, R0 ≤ ‖z‖ → ρ < ‖z‖ := fun z hz => by linarith
  have hG1 : ∀ z : ℂ, R0 ≤ ‖z‖ → G z ≠ 0 := fun z hz h => by
    have := hgR z hz
    rw [← hGg (hGE z hz), h, norm_zero] at this
    linarith
  -- `F̂ = 1/G(1/·)`, updated at `0`
  set s : ℝ := R0⁻¹ with hs
  have hs0 : 0 < s := inv_pos.2 (by linarith)
  have hwin : ∀ w : ℂ, w ≠ 0 → ‖w‖ < s → R0 ≤ ‖w⁻¹‖ := fun w hw0 hw => by
    rw [norm_inv]
    have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw0
    rw [hs] at hw
    rw [le_inv_comm₀ (by linarith) hw']
    exact hw.le
  set Fh : ℂ → ℂ := Function.update (fun w => (G w⁻¹)⁻¹) 0 0 with hFh
  have hFhw : ∀ w : ℂ, w ≠ 0 → Fh w = (G w⁻¹)⁻¹ := fun w hw => Function.update_of_ne hw _ _
  have hF0 : Fh 0 = 0 := Function.update_self _ _ _
  have hO : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hFd : DifferentiableOn ℂ Fh (ball 0 s) := by
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (ball_mem_nhds 0 hs0)).1 ⟨?_, ?_⟩
    · intro w hw
      have hw0 : w ≠ 0 := hw.2
      have hwR := hwin w hw0 (mem_ball_zero_iff.1 hw.1)
      have hd : DifferentiableAt ℂ (fun w : ℂ => (G w⁻¹)⁻¹) w :=
        ((hGd.differentiableAt (hO.mem_nhds (hGρ _ hwR))).comp w (differentiableAt_inv hw0)).inv (hG1 _ hwR)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [isOpen_ne.mem_nhds hw0] with v hv
      exact hFhw v hv
    · rw [hFh, continuousAt_update_same]
      have h1 : Tendsto (fun w : ℂ => G w⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
        have h2 : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
          rw [← Metric.cobounded_eq_cocompact]
          exact tendsto_inv₀_nhdsNE_zero
        refine (hinf.comp h2).congr' ?_
        filter_upwards [h2.eventually ((isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact)] with w hw
        simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hw
        exact (hGg hw).symm
      have h3 : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
        rw [← Metric.cobounded_eq_cocompact]
        exact tendsto_inv₀_cobounded
      exact h3.comp h1
  have hFi : InjOn Fh (ball 0 s) := by
    intro w1 hw1 w2 hw2 he
    by_cases h1 : w1 = 0
    · by_cases h2 : w2 = 0
      · rw [h1, h2]
      · exfalso
        rw [h1, hF0, hFhw w2 h2] at he
        exact inv_ne_zero (hG1 _ (hwin w2 h2 (mem_ball_zero_iff.1 hw2))) he.symm
    · by_cases h2 : w2 = 0
      · exfalso
        rw [h2, hFhw w1 h1, hF0] at he
        exact inv_ne_zero (hG1 _ (hwin w1 h1 (mem_ball_zero_iff.1 hw1))) he
      · rw [hFhw w1 h1, hFhw w2 h2] at he
        have he' := hGi (hGρ _ (hwin w1 h1 (mem_ball_zero_iff.1 hw1)))
          (hGρ _ (hwin w2 h2 (mem_ball_zero_iff.1 hw2))) (inv_injective he)
        exact inv_injective he'
  have hc : deriv Fh 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hFd hFi (mem_ball_self hs0)
  -- `q = dslope F̂ 0`, nonvanishing near `0`; `P = 1/q`
  set q : ℂ → ℂ := dslope Fh 0 with hq
  have hqd : DifferentiableOn ℂ q (ball 0 s) := (differentiableOn_dslope (ball_mem_nhds 0 hs0)).2 hFd
  have hq0 : q 0 = deriv Fh 0 := dslope_same _ _
  have hFq : ∀ w, Fh w = w * q w := fun w => by
    have := sub_smul_dslope Fh 0 w
    rw [sub_zero, smul_eq_mul, hF0, sub_zero] at this
    exact this.symm
  obtain ⟨s2, hs2, hs2q⟩ := Metric.eventually_nhds_iff_ball.1
    (((hqd.differentiableAt (ball_mem_nhds 0 hs0)).continuousAt).eventually_ne (by rw [hq0]; exact hc))
  set s3 : ℝ := min s2 s with hs3
  have hs30 : 0 < s3 := lt_min hs2 hs0
  have hs3b : ball (0 : ℂ) s3 ⊆ ball 0 s := ball_subset_ball (min_le_right _ _)
  have hqne : ∀ w ∈ ball (0 : ℂ) s3, q w ≠ 0 := fun w hw => hs2q w (ball_subset_ball (min_le_left _ _) hw)
  set P : ℂ → ℂ := fun w => (q w)⁻¹ with hP
  have hPd : DifferentiableOn ℂ P (ball 0 s3) := (hqd.mono hs3b).inv hqne
  have hn3 : ball (0 : ℂ) s3 ∈ 𝓝 0 := ball_mem_nhds 0 hs30
  -- Taylor data of `P` at `0`
  set P1 : ℂ → ℂ := dslope P 0 with hP1
  set P2 : ℂ → ℂ := dslope P1 0 with hP2
  have hP1d : DifferentiableOn ℂ P1 (ball 0 s3) := (differentiableOn_dslope hn3).2 hPd
  have hP2d : DifferentiableOn ℂ P2 (ball 0 s3) := (differentiableOn_dslope hn3).2 hP1d
  have hPdd : DifferentiableOn ℂ (deriv P) (ball 0 s3) := hPd.deriv isOpen_ball
  set S3 : ℂ → ℂ := dslope (deriv P) 0 with hS3
  have hS3d : DifferentiableOn ℂ S3 (ball 0 s3) := (differentiableOn_dslope hn3).2 hPdd
  have hcb : closedBall (0 : ℂ) (s3 / 2) ⊆ ball 0 s3 := closedBall_subset_ball (by linarith)
  obtain ⟨B2, hB2⟩ := (isCompact_closedBall (0 : ℂ) (s3 / 2)).exists_bound_of_continuousOn
    (hP2d.continuousOn.mono hcb)
  obtain ⟨B3, hB3⟩ := (isCompact_closedBall (0 : ℂ) (s3 / 2)).exists_bound_of_continuousOn
    (hS3d.continuousOn.mono hcb)
  have hPe : ∀ w, P w = P 0 + w * P1 w := fun w => by
    have := sub_smul_dslope P 0 w
    rw [sub_zero, smul_eq_mul] at this
    rw [← hP1] at this
    linear_combination -this
  have hP1e : ∀ w, P1 w = P1 0 + w * P2 w := fun w => by
    have := sub_smul_dslope P1 0 w
    rw [sub_zero, smul_eq_mul] at this
    rw [← hP2] at this
    linear_combination -this
  have hdPe : ∀ w, deriv P w = deriv P 0 + w * S3 w := fun w => by
    have := sub_smul_dslope (deriv P) 0 w
    rw [sub_zero, smul_eq_mul] at this
    rw [← hS3] at this
    linear_combination -this
  have hP10 : P1 0 = deriv P 0 := dslope_same _ _
  -- `G(z) = z P(1/z)` far out
  set T0 : ℝ := max R0 (s3⁻¹) with hT0
  have hT0R : R0 ≤ T0 := le_max_left _ _
  have hid : ∀ z : ℂ, T0 < ‖z‖ → g z = z * P z⁻¹ := by
    intro z hz
    have hzR : R0 ≤ ‖z‖ := hT0R.trans hz.le
    have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; linarith
    have hw0 : z⁻¹ ≠ 0 := inv_ne_zero hz0
    have hw3 : z⁻¹ ∈ ball (0 : ℂ) s3 := by
      rw [mem_ball_zero_iff, norm_inv]
      exact inv_lt_of_inv_lt₀ hs30 ((le_max_right _ _).trans_lt hz)
    have h1 := hFq z⁻¹
    rw [hFhw _ hw0, inv_inv] at h1
    rw [← hGg (hGE z hzR)]
    have hq' := hqne _ hw3
    show G z = z * (q z⁻¹)⁻¹
    rw [← inv_inv (G z), h1, mul_inv, inv_inv]
  refine ⟨P 0, P1 0, ?_, 2 * T0 + 2 * (s3 / 2)⁻¹, max (max B2 0 + max B3 0) 0, ?_, le_max_right _ _, ?_⟩
  · rw [hP]
    exact inv_ne_zero (by rw [hq0]; exact hc)
  · have : 0 ≤ T0 := (by linarith : (0 : ℝ) ≤ R0).trans hT0R
    have : 0 ≤ (s3 / 2)⁻¹ := (inv_pos.2 (by linarith)).le
    have : (1 : ℝ) ≤ T0 := by linarith
    linarith
  intro ζ hζ
  have hT0p : 0 ≤ T0 := (by linarith : (0 : ℝ) ≤ R0).trans hT0R
  have hζT : T0 < ‖ζ‖ := by
    have : 0 < (s3 / 2)⁻¹ := inv_pos.2 (by linarith)
    have : 1 ≤ T0 := by linarith
    linarith
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζT; linarith
  have hζp : 0 < ‖ζ‖ := norm_pos_iff.2 hζ0
  have hwc : ζ⁻¹ ∈ closedBall (0 : ℂ) (s3 / 2) := by
    rw [mem_closedBall_zero_iff, norm_inv]
    have : (s3 / 2)⁻¹ ≤ ‖ζ‖ := by
      have : 0 ≤ T0 := hT0p
      linarith
    exact inv_le_of_inv_le₀ (by linarith) this
  have hw3 : ζ⁻¹ ∈ ball (0 : ℂ) s3 := hcb hwc
  have hB2' : ‖P2 ζ⁻¹‖ ≤ max B2 0 := (hB2 _ hwc).trans (le_max_left _ _)
  have hB3' : ‖S3 ζ⁻¹‖ ≤ max B3 0 := (hB3 _ hwc).trans (le_max_left _ _)
  have hMle : max B2 0 + max B3 0 ≤ max (max B2 0 + max B3 0) 0 := le_max_left _ _
  refine ⟨?_, ?_⟩
  · -- `g ζ - b ζ - b₀ = ζ⁻¹ P₂(ζ⁻¹)`
    have he : g ζ - P 0 * ζ - P1 0 = ζ⁻¹ * P2 ζ⁻¹ := by
      rw [hid ζ hζT, hPe ζ⁻¹, hP1e ζ⁻¹]
      field_simp <;> ring
    rw [he, norm_mul, norm_inv]
    exact (mul_le_mul_of_nonneg_left (hB2'.trans (by linarith [le_max_right B3 0])) (by positivity)).trans_eq
      (mul_comm _ _)
  · -- `g'(ζ) = P(w) - w P'(w) = b + w² (P₂(w) - S₃(w))`, `w = ζ⁻¹`
    have hU : {z : ℂ | T0 < ‖z‖} ∈ 𝓝 ζ := (isOpen_lt continuous_const continuous_norm).mem_nhds hζT
    have hgev : g =ᶠ[𝓝 ζ] fun z => z * P z⁻¹ := by
      filter_upwards [hU] with z hz
      exact hid z hz
    have hPdw : HasDerivAt P (deriv P ζ⁻¹) ζ⁻¹ :=
      (hPd.differentiableAt (isOpen_ball.mem_nhds hw3)).hasDerivAt
    have hder : HasDerivAt (fun z => z * P z⁻¹) (1 * P ζ⁻¹ + ζ * (deriv P ζ⁻¹ * (-(ζ ^ 2)⁻¹))) ζ :=
      (hasDerivAt_id ζ).mul (hPdw.comp ζ (hasDerivAt_inv hζ0))
    have hdg : deriv g ζ = 1 * P ζ⁻¹ + ζ * (deriv P ζ⁻¹ * (-(ζ ^ 2)⁻¹)) := by
      rw [hgev.deriv_eq]
      exact hder.deriv
    have he : deriv g ζ - P 0 = (ζ ^ 2)⁻¹ * (P2 ζ⁻¹ - S3 ζ⁻¹) := by
      rw [hdg, hPe ζ⁻¹, hP1e ζ⁻¹, hdPe ζ⁻¹, ← hP10]
      field_simp <;> ring
    rw [he, norm_mul, norm_inv, norm_pow]
    exact (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ((add_le_add hB2' hB3').trans hMle))
      (by positivity)).trans_eq (mul_comm _ _)

/-- **(FB-E/QD)** Far-field decay of the `Qk` kernel: `|Qk(ζ, y)| ≤ C |ζ|⁻³` for `|ζ| ≥ T`, uniformly in `y ∈ K`. -/
theorem s3fe_Q_decay {f g G : ℂ → ℂ} {ρ : ℝ} (hpair : IsNormalizedDisjointPair f g) (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGd' : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0) (hGg : EqOn G g unitDiscExterior)
    {K : Set ℂ} (hK : IsCompact K) (hKE : K ⊆ unitDiscExterior) :
    ∃ T C : ℝ, ∀ y ∈ K, ∀ ζ : ℂ, T ≤ ‖ζ‖ →
      ‖deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2‖ ≤ C * (‖ζ‖ ^ 3)⁻¹ := by
  -- `hGd'` (`G' ≠ 0`) is not needed: injectivity of `F̂ = 1/G(1/·)` already gives `F̂'(0) ≠ 0`;
  -- the statement stays true without it.
  have _hGd' := hGd'
  obtain ⟨-, -, -, -, ⟨hgd, -, hinf⟩, -⟩ := hpair
  obtain ⟨b, b₀, hb, T1, M, hT1, hM, hexp⟩ := s3fe_qd_exp hρ hGd hGi hGg hinf
  obtain ⟨Γ, hΓ⟩ := hK.exists_bound_of_continuousOn (hgd.continuousOn.mono hKE)
  obtain ⟨Y, hY⟩ := hK.exists_bound_of_continuousOn (continuousOn_id (s := K))
  have hbp : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hY0 : 0 ≤ max Y 0 := le_max_right _ _
  have hΓ0 : 0 ≤ max Γ 0 := le_max_right _ _
  refine ⟨max (max T1 (2 * max Y 0)) (2 * (‖b₀‖ + M + max Γ 0 + 1) / ‖b‖),
    4 * (‖b‖ * max Y 0 + ‖b₀‖ + max Γ 0 + M * (2 + max Y 0)) / ‖b‖ * (2 * (‖b‖ + M) / ‖b‖ + 2), ?_⟩
  intro y hy ζ hζ
  have hy1 : ‖y‖ ≤ max Y 0 := (hY y hy).trans (le_max_left _ _)
  have hgy : ‖g y‖ ≤ max Γ 0 := (hΓ y hy).trans (le_max_left _ _)
  have hT1ζ : T1 ≤ ‖ζ‖ := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hζ
  have hYζ : 2 * max Y 0 ≤ ‖ζ‖ := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hζ
  have hBζ : 2 * (‖b₀‖ + M + max Γ 0 + 1) / ‖b‖ ≤ ‖ζ‖ := (le_max_right _ _).trans hζ
  have hx1 : 1 ≤ ‖ζ‖ := hT1.trans hT1ζ
  have hxp : 0 < ‖ζ‖ := by linarith
  have hζ0 : ζ ≠ 0 := norm_pos_iff.1 hxp
  obtain ⟨hh, hk⟩ := hexp ζ hT1ζ
  have hinv1 : ‖ζ‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx1
  have hh1 : ‖g ζ - b * ζ - b₀‖ ≤ M := hh.trans (mul_le_of_le_one_right hM hinv1)
  have hx2 : 1 ≤ ‖ζ‖ ^ 2 := one_le_pow₀ hx1
  have hk1 : ‖deriv g ζ - b‖ ≤ M := hk.trans (mul_le_of_le_one_right hM (inv_le_one_of_one_le₀ hx2))
  -- the two denominators
  have hD2 : ‖ζ‖ / 2 ≤ ‖ζ - y‖ := by
    have := norm_sub_norm_le ζ y
    linarith
  have hD1 : ‖b‖ * ‖ζ‖ / 2 ≤ ‖g ζ - g y‖ := by
    have e : g ζ - g y = b * ζ - -(b₀ + (g ζ - b * ζ - b₀) - g y) := by ring
    have h1 : ‖-(b₀ + (g ζ - b * ζ - b₀) - g y)‖ ≤ ‖b₀‖ + M + max Γ 0 := by
      rw [norm_neg]
      refine (norm_sub_le _ _).trans ?_
      linarith [norm_add_le b₀ (g ζ - b * ζ - b₀)]
    have h2 := norm_sub_norm_le (b * ζ) (-(b₀ + (g ζ - b * ζ - b₀) - g y))
    rw [← e, norm_mul] at h2
    have h3 : 2 * (‖b₀‖ + M + max Γ 0 + 1) ≤ ‖b‖ * ‖ζ‖ := by
      rw [div_le_iff₀ hbp] at hBζ
      linarith
    linarith
  have hD1p : 0 < ‖g ζ - g y‖ := lt_of_lt_of_le (div_pos (mul_pos hbp hxp) two_pos) hD1
  have hD2p : 0 < ‖ζ - y‖ := lt_of_lt_of_le (half_pos hxp) hD2
  have hD10 : g ζ - g y ≠ 0 := norm_pos_iff.1 hD1p
  have hD20 : ζ - y ≠ 0 := norm_pos_iff.1 hD2p
  -- the numerator `N = g'(ζ)(ζ - y) - (g ζ - g y)` is bounded
  have hkY : ‖(deriv g ζ - b) * (ζ - y)‖ ≤ M * (1 + max Y 0) := by
    rw [norm_mul]
    have h1 : ‖ζ - y‖ ≤ ‖ζ‖ + max Y 0 := (norm_sub_le _ _).trans (by linarith)
    have h2 : (‖ζ‖ ^ 2)⁻¹ * (‖ζ‖ + max Y 0) ≤ 1 + max Y 0 := by
      rw [inv_mul_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hY0 (sub_nonneg.2 hx2), mul_nonneg hxp.le (sub_nonneg.2 hx1)]
    calc ‖deriv g ζ - b‖ * ‖ζ - y‖ ≤ (M * (‖ζ‖ ^ 2)⁻¹) * (‖ζ‖ + max Y 0) :=
          mul_le_mul hk h1 (norm_nonneg _) (mul_nonneg hM (by positivity))
      _ = M * ((‖ζ‖ ^ 2)⁻¹ * (‖ζ‖ + max Y 0)) := by ring
      _ ≤ M * (1 + max Y 0) := mul_le_mul_of_nonneg_left h2 hM
  have hN : ‖deriv g ζ * (ζ - y) - (g ζ - g y)‖ ≤ ‖b‖ * max Y 0 + ‖b₀‖ + max Γ 0 + M * (2 + max Y 0) := by
    have e : deriv g ζ * (ζ - y) - (g ζ - g y) =
        (deriv g ζ - b) * (ζ - y) - (g ζ - b * ζ - b₀) - b * y - b₀ + g y := by ring
    rw [e]
    have t1 := norm_add_le ((deriv g ζ - b) * (ζ - y) - (g ζ - b * ζ - b₀) - b * y - b₀) (g y)
    have t2 := norm_sub_le ((deriv g ζ - b) * (ζ - y) - (g ζ - b * ζ - b₀) - b * y) b₀
    have t3 := norm_sub_le ((deriv g ζ - b) * (ζ - y) - (g ζ - b * ζ - b₀)) (b * y)
    have t4 := norm_sub_le ((deriv g ζ - b) * (ζ - y)) (g ζ - b * ζ - b₀)
    have t5 : ‖b * y‖ ≤ ‖b‖ * max Y 0 := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hy1 (norm_nonneg _)
    linarith [hkY, hh1, hgy]
  have hN0 : 0 ≤ ‖b‖ * max Y 0 + ‖b₀‖ + max Γ 0 + M * (2 + max Y 0) := (norm_nonneg _).trans hN
  -- `Qk = (A - B)(A + B)`, `A - B = N/(D₁ D₂)`
  have eQ : deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2 =
      (deriv g ζ * (ζ - y) - (g ζ - g y)) / ((g ζ - g y) * (ζ - y)) *
        (deriv g ζ / (g ζ - g y) + 1 / (ζ - y)) := by
    field_simp <;> ring
  rw [eQ, norm_mul, norm_div, norm_mul]
  have hg' : ‖deriv g ζ‖ ≤ ‖b‖ + M := by
    linarith [norm_le_insert' (deriv g ζ) b, hk1]
  have hA0 : 0 ≤ 4 * (‖b‖ * max Y 0 + ‖b₀‖ + max Γ 0 + M * (2 + max Y 0)) / ‖b‖ * (‖ζ‖ ^ 2)⁻¹ :=
    mul_nonneg (div_nonneg (by linarith) hbp.le) (by positivity)
  have hB0 : 0 ≤ 2 * (‖b‖ + M) / ‖b‖ * ‖ζ‖⁻¹ :=
    mul_nonneg (div_nonneg (by linarith) hbp.le) (by positivity)
  have hb1 : ‖deriv g ζ * (ζ - y) - (g ζ - g y)‖ / (‖g ζ - g y‖ * ‖ζ - y‖) ≤
      4 * (‖b‖ * max Y 0 + ‖b₀‖ + max Γ 0 + M * (2 + max Y 0)) / ‖b‖ * (‖ζ‖ ^ 2)⁻¹ := by
    rw [div_le_iff₀ (mul_pos hD1p hD2p)]
    calc ‖deriv g ζ * (ζ - y) - (g ζ - g y)‖ ≤ ‖b‖ * max Y 0 + ‖b₀‖ + max Γ 0 + M * (2 + max Y 0) := hN
      _ = 4 * (‖b‖ * max Y 0 + ‖b₀‖ + max Γ 0 + M * (2 + max Y 0)) / ‖b‖ * (‖ζ‖ ^ 2)⁻¹ *
            ((‖b‖ * ‖ζ‖ / 2) * (‖ζ‖ / 2)) := by
          field_simp <;> ring
      _ ≤ 4 * (‖b‖ * max Y 0 + ‖b₀‖ + max Γ 0 + M * (2 + max Y 0)) / ‖b‖ * (‖ζ‖ ^ 2)⁻¹ *
            (‖g ζ - g y‖ * ‖ζ - y‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hD1 hD2 (by positivity) (norm_nonneg _)) hA0
  have hb2 : ‖deriv g ζ / (g ζ - g y) + 1 / (ζ - y)‖ ≤ (2 * (‖b‖ + M) / ‖b‖ + 2) * ‖ζ‖⁻¹ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_div, norm_one]
    have h1 : ‖deriv g ζ‖ / ‖g ζ - g y‖ ≤ 2 * (‖b‖ + M) / ‖b‖ * ‖ζ‖⁻¹ := by
      rw [div_le_iff₀ hD1p]
      calc ‖deriv g ζ‖ ≤ ‖b‖ + M := hg'
        _ = 2 * (‖b‖ + M) / ‖b‖ * ‖ζ‖⁻¹ * (‖b‖ * ‖ζ‖ / 2) := by
            field_simp <;> ring
        _ ≤ 2 * (‖b‖ + M) / ‖b‖ * ‖ζ‖⁻¹ * ‖g ζ - g y‖ :=
            mul_le_mul_of_nonneg_left hD1 hB0
    have h2 : 1 / ‖ζ - y‖ ≤ 2 * ‖ζ‖⁻¹ := by
      rw [div_le_iff₀ hD2p]
      calc (1 : ℝ) = 2 * ‖ζ‖⁻¹ * (‖ζ‖ / 2) := by field_simp <;> ring
        _ ≤ 2 * ‖ζ‖⁻¹ * ‖ζ - y‖ := mul_le_mul_of_nonneg_left hD2 (by positivity)
    calc ‖deriv g ζ‖ / ‖g ζ - g y‖ + 1 / ‖ζ - y‖ ≤ 2 * (‖b‖ + M) / ‖b‖ * ‖ζ‖⁻¹ + 2 * ‖ζ‖⁻¹ := add_le_add h1 h2
      _ = (2 * (‖b‖ + M) / ‖b‖ + 2) * ‖ζ‖⁻¹ := by ring
  calc ‖deriv g ζ * (ζ - y) - (g ζ - g y)‖ / (‖g ζ - g y‖ * ‖ζ - y‖) *
        ‖deriv g ζ / (g ζ - g y) + 1 / (ζ - y)‖
      ≤ (4 * (‖b‖ * max Y 0 + ‖b₀‖ + max Γ 0 + M * (2 + max Y 0)) / ‖b‖ * (‖ζ‖ ^ 2)⁻¹) *
          ((2 * (‖b‖ + M) / ‖b‖ + 2) * ‖ζ‖⁻¹) :=
        mul_le_mul hb1 hb2 (norm_nonneg _) hA0
    _ = 4 * (‖b‖ * max Y 0 + ‖b₀‖ + max Γ 0 + M * (2 + max Y 0)) / ‖b‖ * (2 * (‖b‖ + M) / ‖b‖ + 2) *
          (‖ζ‖ ^ 3)⁻¹ := by
        field_simp <;> ring

/-- [FB-E helper] The regular part of `Qk(ζ, ·) = H'(ζ)²/(H ζ - H ·)² - 1/(ζ - ·)²` after removing the simple pole
`𝒜(ζ)/(ζ - ·)` is holomorphic on `U` (removable at `ζ`): `dslope² N / H' - π H'(ζ) K₁(ζ, ·)/H'` with
`N(y) = H'(ζ) - H'(y) - 𝒜(ζ) H'(y)(ζ - y)` (double zero at `ζ`). -/
theorem s3fe_kreg {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hH : DifferentiableOn ℂ H U) (hi : InjOn H U)
    (hd : ∀ z ∈ U, deriv H z ≠ 0) {ζ : ℂ} (hζ : ζ ∈ U) :
    ∃ k : ℂ → ℂ, DifferentiableOn ℂ k U ∧ ∀ y ∈ U, y ≠ ζ →
      k y = deriv H ζ ^ 2 / (H ζ - H y) ^ 2 - 1 / (ζ - y) ^ 2 - preSchwarzian H ζ / (ζ - y) := by
  have hn : U ∈ 𝓝 ζ := hU.mem_nhds hζ
  have hH1 : DifferentiableOn ℂ (deriv H) U := (hH.analyticOnNhd hU).deriv.differentiableOn
  set A := preSchwarzian H ζ with hA
  set N : ℂ → ℂ := fun y => deriv H ζ - deriv H y - A * deriv H y * (ζ - y) with hNdef
  have hN : DifferentiableOn ℂ N U :=
    ((differentiableOn_const _).sub hH1).sub (((differentiableOn_const _).mul hH1).mul
      ((differentiableOn_const _).sub differentiableOn_id))
  have h2 := (hH1.differentiableAt hn).hasDerivAt
  have hNd := ((hasDerivAt_const ζ (deriv H ζ)).sub h2).sub
    ((h2.const_mul A).mul ((hasDerivAt_const ζ ζ).sub (hasDerivAt_id ζ)))
  have hN' : deriv N ζ = 0 := by
    rw [show deriv N ζ = _ from hNd.deriv]
    simp only [Pi.sub_apply, id, sub_self, mul_zero, zero_add, zero_sub]
    rw [hA]
    unfold preSchwarzian
    have := hd ζ hζ
    field_simp
    ring
  have hN0 : N ζ = 0 := by simp [hNdef]
  set q := dslope N ζ with hq
  have hqd : DifferentiableOn ℂ q U := (Complex.differentiableOn_dslope hn).mpr hN
  have hq0 : q ζ = 0 := by rw [hq, dslope_same, hN']
  set q2 := dslope q ζ with hq2
  have hq2d : DifferentiableOn ℂ q2 U := (Complex.differentiableOn_dslope hn).mpr hqd
  have hK := AppB.differentiableOn_kerK1_right hU hH hi hζ
  refine ⟨fun y => q2 y / deriv H y - π * deriv H ζ * kerK1 H ζ y / deriv H y, ?_, ?_⟩
  · exact (hq2d.div hH1 hd).sub (((differentiableOn_const _).mul hK).div hH1 hd)
  · intro y hy hyζ
    have hyz : y - ζ ≠ 0 := sub_ne_zero.mpr hyζ
    have hzy : ζ - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyζ)
    have hHy : H ζ - H y ≠ 0 := sub_ne_zero.mpr fun h => hyζ (hi hy hζ h.symm)
    have hdy := hd y hy
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have e1 : q y = N y / (y - ζ) := by
      rw [hq, dslope_of_ne _ hyζ, slope_def_field, hN0, sub_zero]
    have e2 : q2 y = N y / (y - ζ) ^ 2 := by
      rw [hq2, dslope_of_ne _ hyζ, slope_def_field, hq0, e1]
      field_simp
      ring
    simp only
    rw [e2, kerK1_of_ne H (Ne.symm hyζ), hNdef]
    field_simp
    ring

/-- [FB-E helper] Geometry of the extension `G` near `𝕊¹`: a radius `δ` with `closedBall y δ ⊂ {ρ' < ‖z‖}` for
`y ∈ 𝔻*`, a bound `MG` for `G'` there, and a uniform separation `c ≤ |G a - G b|` for `a, b ∈ closedBall y δ` with
`|a - b| ≥ δ/2` (compactness near `𝕊¹`, `s3fe_dd_lower` far out). -/
theorem s3fe_geom {f g G : ℂ → ℂ} {ρ : ℝ} (hpair : IsNormalizedDisjointPair f g) (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGd' : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0) (hGg : EqOn G g unitDiscExterior) :
    ∃ ρ' δ c MG : ℝ, ρ < ρ' ∧ 0 < δ ∧ δ ≤ 1 / 4 ∧ 0 < c ∧ 0 ≤ MG ∧
      (∀ y ∈ unitDiscExterior, ∀ z ∈ closedBall y δ, ρ' < ‖z‖) ∧
      (∀ z : ℂ, ρ' < ‖z‖ → ‖deriv G z‖ ≤ MG) ∧
      (∀ y ∈ unitDiscExterior, ∀ a ∈ closedBall y δ, ∀ b ∈ closedBall y δ, δ / 2 ≤ ‖a - b‖ →
        c ≤ ‖G a - G b‖) := by
  obtain ⟨cd, hcd, hdd⟩ := s3fe_dd_lower hpair hρ hGd hGi hGd' hGg
  obtain ⟨-, -, -, hgG, -⟩ := d2e_basic hρ hGd hGi hGd' hGg
  obtain ⟨cg, -, C', hC'⟩ := d2e_growth hpair
  set ρ' := max ((ρ + 1) / 2) (1 / 2) with hρ'
  have hρ'1 : ρ' < 1 := max_lt (by linarith) (by norm_num)
  have hρρ' : ρ < ρ' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hρ'h : (1 / 2 : ℝ) ≤ ρ' := le_max_right _ _
  set δ := (1 - ρ') / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ4 : δ ≤ 1 / 4 := by rw [hδ]; linarith
  have hdom : ∀ y ∈ unitDiscExterior, ∀ z ∈ closedBall y δ, ρ' < ‖z‖ := by
    intro y hy z hz
    have hy1 : (1 : ℝ) < ‖y‖ := hy
    have h1 := norm_sub_norm_le y z
    rw [← dist_eq_norm, dist_comm] at h1
    have h2 : dist z y ≤ δ := hz
    rw [hδ] at h2
    linarith
  have hGc : ContinuousOn G {z : ℂ | ρ < ‖z‖} := hGd.continuousOn
  have hopen : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  -- the bound for `G'`
  have hK1 : IsCompact ({z : ℂ | ρ' ≤ ‖z‖} ∩ closedBall 0 4) :=
    (isCompact_closedBall 0 4).inter_left (isClosed_le continuous_const continuous_norm)
  have hG'c : ContinuousOn (deriv G) ({z : ℂ | ρ' ≤ ‖z‖} ∩ closedBall 0 4) :=
    ((hGd.analyticOnNhd hopen).deriv.differentiableOn.continuousOn).mono fun z hz =>
      (show ρ < ‖z‖ from lt_of_lt_of_le hρρ' hz.1)
  obtain ⟨M0, hM0⟩ := hK1.exists_bound_of_continuousOn hG'c
  have hMG : ∀ z : ℂ, ρ' < ‖z‖ → ‖deriv G z‖ ≤ max (max M0 C') 0 := by
    intro z hz
    by_cases h4 : ‖z‖ ≤ 4
    · exact (hM0 z ⟨hz.le, mem_closedBall_zero_iff.mpr h4⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
    · push Not at h4
      have hzE : z ∈ unitDiscExterior := (show (1 : ℝ) < ‖z‖ by linarith)
      rw [← hgG z hzE]
      exact ((hC' z h4.le).2).trans ((le_max_right _ _).trans (le_max_left _ _))
  -- the compact separation
  set S : Set (ℂ × ℂ) := {p | ρ' ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ 5 ∧ ρ' ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ 5 ∧ δ / 2 ≤ ‖p.1 - p.2‖} with hS
  have hSc : IsCompact S := by
    refine ((isCompact_closedBall (0 : ℂ) 5).prod (isCompact_closedBall (0 : ℂ) 5)).of_isClosed_subset ?_ ?_
    · have c1 : Continuous fun p : ℂ × ℂ => ‖p.1‖ := continuous_norm.comp continuous_fst
      have c2 : Continuous fun p : ℂ × ℂ => ‖p.2‖ := continuous_norm.comp continuous_snd
      have c3 : Continuous fun p : ℂ × ℂ => ‖p.1 - p.2‖ := (continuous_fst.sub continuous_snd).norm
      exact (isClosed_le continuous_const c1).inter ((isClosed_le c1 continuous_const).inter
        ((isClosed_le continuous_const c2).inter ((isClosed_le c2 continuous_const).inter
          (isClosed_le continuous_const c3))))
    · intro p hp
      exact ⟨mem_closedBall_zero_iff.mpr hp.2.1, mem_closedBall_zero_iff.mpr hp.2.2.2.1⟩
  have hSd : ∀ p ∈ S, ρ < ‖p.1‖ ∧ ρ < ‖p.2‖ := fun p hp =>
    ⟨lt_of_lt_of_le hρρ' hp.1, lt_of_lt_of_le hρρ' hp.2.2.1⟩
  have hFc : ContinuousOn (fun p : ℂ × ℂ => ‖G p.1 - G p.2‖) S := by
    refine ((hGc.comp continuous_fst.continuousOn fun p hp => (hSd p hp).1).sub
      (hGc.comp continuous_snd.continuousOn fun p hp => (hSd p hp).2)).norm
  obtain ⟨c3, hc3, hsep3⟩ : ∃ c3 : ℝ, 0 < c3 ∧ ∀ p ∈ S, c3 ≤ ‖G p.1 - G p.2‖ := by
    by_cases hne : S.Nonempty
    · obtain ⟨p0, hp0, hmin⟩ := hSc.exists_isMinOn hne hFc
      refine ⟨‖G p0.1 - G p0.2‖, ?_, fun p hp => hmin hp⟩
      refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h => ?_)
      have := hGi (hSd p0 hp0).1 (hSd p0 hp0).2 h
      have h0 : ‖p0.1 - p0.2‖ = 0 := by rw [this, sub_self, norm_zero]
      have := hp0.2.2.2.2
      linarith
    · exact ⟨1, one_pos, fun p hp => absurd ⟨p, hp⟩ hne⟩
  refine ⟨ρ', δ, min c3 (cd * (δ / 2)), max (max M0 C') 0, hρρ', hδ0, hδ4,
    lt_min hc3 (mul_pos hcd (half_pos hδ0)), le_max_right _ _, hdom, hMG, ?_⟩
  intro y hy a ha b hb hab
  have hda := hdom y hy a ha
  have hdb := hdom y hy b hb
  have hna : ‖a‖ ≤ ‖y‖ + δ := by
    have := norm_le_norm_add_norm_sub' a y
    have h : ‖a - y‖ ≤ δ := by rw [← dist_eq_norm]; exact ha
    linarith
  have hnb : ‖b‖ ≤ ‖y‖ + δ := by
    have := norm_le_norm_add_norm_sub' b y
    have h : ‖b - y‖ ≤ δ := by rw [← dist_eq_norm]; exact hb
    linarith
  by_cases hy4 : ‖y‖ ≤ 4
  · exact (min_le_left _ _).trans (hsep3 (a, b) ⟨hda.le, by linarith, hdb.le, by linarith, hab⟩)
  · push Not at hy4
    have hla : ‖y‖ - δ ≤ ‖a‖ := by
      have := norm_sub_norm_le y a
      have h : ‖y - a‖ ≤ δ := by rw [← dist_eq_norm, dist_comm]; exact ha
      linarith
    have hlb : ‖y‖ - δ ≤ ‖b‖ := by
      have := norm_sub_norm_le y b
      have h : ‖y - b‖ ≤ δ := by rw [← dist_eq_norm, dist_comm]; exact hb
      linarith
    have haE : a ∈ unitDiscExterior := (show (1 : ℝ) < ‖a‖ by linarith)
    have hbE : b ∈ unitDiscExterior := (show (1 : ℝ) < ‖b‖ by linarith)
    rw [hGg haE, hGg hbE]
    exact (min_le_right _ _).trans ((mul_le_mul_of_nonneg_left hab hcd.le).trans (hdd a haE b hbE))

/-- [FB-E helper] Maximum modulus and Cauchy estimate at the centre of a disc. -/
theorem s3fe_cauchy {φ : ℂ → ℂ} {y : ℂ} {δ M : ℝ} (hδ : 0 < δ) (hφ : DifferentiableOn ℂ φ (closedBall y δ))
    (hM : ∀ z ∈ sphere y δ, ‖φ z‖ ≤ M) : ‖φ y‖ ≤ M ∧ ‖deriv φ y‖ ≤ M / δ := by
  have hd : DiffContOnCl ℂ φ (ball y δ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball y hδ.ne']
    exact hφ
  refine ⟨Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_
    (subset_closure (mem_ball_self hδ)), Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hd hM⟩
  rw [frontier_ball y hδ.ne']
  exact hM

/-- [FB-E helper] `dz` is additive on real-differentiable functions. -/
theorem s3fe_dz_add {F H : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z) (hH : DifferentiableAt ℝ H z) :
    dz (fun y => F y + H y) z = dz F z + dz H z := by
  show (fderiv ℝ (fun y => F y + H y) z 1 - I * fderiv ℝ (fun y => F y + H y) z I) / 2 =
    (fderiv ℝ F z 1 - I * fderiv ℝ F z I) / 2 + (fderiv ℝ H z 1 - I * fderiv ℝ H z I) / 2
  rw [show (fun y => F y + H y) = F + H from rfl, fderiv_add hF hH]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- [FB-E helper] `dz` only depends on the germ. -/
theorem s3fe_dz_congr {F H : ℂ → ℂ} {z : ℂ} (h : F =ᶠ[𝓝 z] H) : dz F z = dz H z := by
  show (fderiv ℝ F z 1 - I * fderiv ℝ F z I) / 2 = (fderiv ℝ H z 1 - I * fderiv ℝ H z I) / 2
  rw [h.fderiv_eq]

/-- [FB-E helper] The kernel identity `(∂ₓ - 𝒜(x)) k̃(x, ω) = -∂_ω Q_reg(x, ω)` (off the diagonal); `a1 = g'(x)`,
`a2 = g'(ω)`, `d2 = g''(x)`, `b1 - b2 = g x - g ω`. -/
theorem s3fe_alg {a1 a2 d2 b1 b2 x ω : ℂ} (hb : b1 - b2 ≠ 0) (hxω : x - ω ≠ 0) (ha1 : a1 ≠ 0) :
    d2 * a2 / (b1 - b2) ^ 2 - 2 * a1 ^ 2 * a2 / (b1 - b2) ^ 3 + 2 / (x - ω) ^ 3 -
        d2 / a1 * (a1 * a2 / (b1 - b2) ^ 2 - 1 / (x - ω) ^ 2) =
      -(2 * a1 ^ 2 * a2 / (b1 - b2) ^ 3 - 2 / (x - ω) ^ 3 - d2 / a1 / (x - ω) ^ 2) := by
  field_simp
  ring

/-- [FB-E helper] `∂_y` of `Q_reg(ζ, y) = H'(ζ)²/(H ζ - H y)² - 1/(ζ - y)² - 𝒜(ζ)/(ζ - y)` off the diagonal. -/
theorem s3fe_dQ {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hH : DifferentiableOn ℂ H U) (hi : InjOn H U)
    {ζ y : ℂ} (hζ : ζ ∈ U) (hy : y ∈ U) (hyζ : y ≠ ζ) (Aζ : ℂ) :
    HasDerivAt (fun w => deriv H ζ ^ 2 / (H ζ - H w) ^ 2 - 1 / (ζ - w) ^ 2 - Aζ / (ζ - w))
      (2 * deriv H ζ ^ 2 * deriv H y / (H ζ - H y) ^ 3 - 2 / (ζ - y) ^ 3 - Aζ / (ζ - y) ^ 2) y := by
  have hHy : H ζ - H y ≠ 0 := sub_ne_zero.mpr fun h => hyζ (hi hy hζ h.symm)
  have hzy : ζ - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyζ)
  have hd := (hH.differentiableAt (hU.mem_nhds hy)).hasDerivAt
  have h1 : HasDerivAt (fun w => H ζ - H w) (-deriv H y) y := hd.const_sub (H ζ)
  have h2 : HasDerivAt (fun w : ℂ => ζ - w) (-1) y := (hasDerivAt_id y).const_sub ζ
  have e1 := ((h1.pow 2).inv (pow_ne_zero 2 hHy)).const_mul (deriv H ζ ^ 2)
  have e2 := (h2.pow 2).inv (pow_ne_zero 2 hzy)
  have e3 := (h2.inv hzy).const_mul Aζ
  have h := (e1.sub e2).sub e3
  have hfun : (fun w => deriv H ζ ^ 2 / (H ζ - H w) ^ 2 - 1 / (ζ - w) ^ 2 - Aζ / (ζ - w)) =
      fun w => deriv H ζ ^ 2 * ((H ζ - H w) ^ 2)⁻¹ - ((ζ - w) ^ 2)⁻¹ - Aζ * (ζ - w)⁻¹ := by
    funext w; simp only [div_eq_mul_inv, one_mul]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.inv_apply]
  field_simp
  ring

/-- [FB-E helper] `∂ₓ` of `k̃(x, ω) = H'(x)H'(ω)/(H x - H ω)² - 1/(x - ω)²` off the diagonal. -/
theorem s3fe_dk {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hH : DifferentiableOn ℂ H U) (hi : InjOn H U)
    {x ω : ℂ} (hx : x ∈ U) (hω : ω ∈ U) (hxω : x ≠ ω) :
    HasDerivAt (fun v => deriv H v * deriv H ω / (H v - H ω) ^ 2 - 1 / (v - ω) ^ 2)
      (deriv (deriv H) x * deriv H ω / (H x - H ω) ^ 2 - 2 * deriv H x ^ 2 * deriv H ω / (H x - H ω) ^ 3 +
        2 / (x - ω) ^ 3) x := by
  have hHx : H x - H ω ≠ 0 := sub_ne_zero.mpr fun h => hxω (hi hx hω h)
  have hxw : x - ω ≠ 0 := sub_ne_zero.mpr hxω
  have hH1 : DifferentiableOn ℂ (deriv H) U := (hH.analyticOnNhd hU).deriv.differentiableOn
  have hd := (hH.differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have hd2 := (hH1.differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have h1 : HasDerivAt (fun v => H v - H ω) (deriv H x) x := hd.sub_const (H ω)
  have h2 : HasDerivAt (fun v : ℂ => v - ω) 1 x := (hasDerivAt_id x).sub_const ω
  have e1 := (hd2.mul_const (deriv H ω)).mul ((h1.pow 2).inv (pow_ne_zero 2 hHx))
  have e2 := (h2.pow 2).inv (pow_ne_zero 2 hxw)
  have h := e1.sub e2
  have hfun : (fun v => deriv H v * deriv H ω / (H v - H ω) ^ 2 - 1 / (v - ω) ^ 2) =
      fun v => deriv H v * deriv H ω * ((H v - H ω) ^ 2)⁻¹ - ((v - ω) ^ 2)⁻¹ := by
    funext v; simp only [div_eq_mul_inv, one_mul]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.inv_apply]
  field_simp
  ring

/-- [FB-E helper] `‖a²/b² - 1/d² - e/d‖ ≤ Ma²/c² + 4/δ² + 2Me/δ` when `‖a‖ ≤ Ma`, `c ≤ ‖b‖`, `δ/2 ≤ ‖d‖`, `‖e‖ ≤ Me`. -/
theorem s3fe_nb {a b d e : ℂ} {Ma Me c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (ha : ‖a‖ ≤ Ma) (hb : c ≤ ‖b‖)
    (hd : δ / 2 ≤ ‖d‖) (he : ‖e‖ ≤ Me) :
    ‖a ^ 2 / b ^ 2 - 1 / d ^ 2 - e / d‖ ≤ Ma ^ 2 / c ^ 2 + 4 / δ ^ 2 + 2 * Me / δ := by
  have hb0 : 0 < ‖b‖ := lt_of_lt_of_le hc hb
  have hd0 : 0 < ‖d‖ := lt_of_lt_of_le (half_pos hδ) hd
  have ha0 : 0 ≤ ‖a‖ := norm_nonneg a
  have h1 : ‖a ^ 2 / b ^ 2‖ ≤ Ma ^ 2 / c ^ 2 := by
    rw [norm_div, norm_pow, norm_pow]
    exact div_le_div₀ (by nlinarith) (pow_le_pow_left₀ ha0 ha 2) (by positivity) (pow_le_pow_left₀ hc.le hb 2)
  have h2 : ‖1 / d ^ 2‖ ≤ 4 / δ ^ 2 := by
    rw [norm_div, norm_one, norm_pow]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_le_pow_left₀ (half_pos hδ).le hd 2]
  have h3 : ‖e / d‖ ≤ 2 * Me / δ := by
    rw [norm_div]
    have hMe : 0 ≤ Me := (norm_nonneg e).trans he
    rw [div_le_div_iff₀ hd0 hδ]
    nlinarith [norm_nonneg e]
  calc ‖a ^ 2 / b ^ 2 - 1 / d ^ 2 - e / d‖ ≤ ‖a ^ 2 / b ^ 2‖ + ‖1 / d ^ 2‖ + ‖e / d‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3

/-- [FB-E helper] `‖1/d² - a a'/b²‖ ≤ 4/δ² + Ma²/c²`. -/
theorem s3fe_nk {a a' b d : ℂ} {Ma c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (ha : ‖a‖ ≤ Ma) (ha' : ‖a'‖ ≤ Ma)
    (hb : c ≤ ‖b‖) (hd : δ / 2 ≤ ‖d‖) :
    ‖1 / d ^ 2 - a * a' / b ^ 2‖ ≤ 4 / δ ^ 2 + Ma ^ 2 / c ^ 2 := by
  have hb0 : 0 < ‖b‖ := lt_of_lt_of_le hc hb
  have hd0 : 0 < ‖d‖ := lt_of_lt_of_le (half_pos hδ) hd
  have h2 : ‖1 / d ^ 2‖ ≤ 4 / δ ^ 2 := by
    rw [norm_div, norm_one, norm_pow]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_le_pow_left₀ (half_pos hδ).le hd 2]
  have h1 : ‖a * a' / b ^ 2‖ ≤ Ma ^ 2 / c ^ 2 := by
    rw [norm_div, norm_mul, norm_pow, sq Ma]
    exact div_le_div₀ (by nlinarith [norm_nonneg a]) (mul_le_mul ha ha' (norm_nonneg _) ((norm_nonneg a).trans ha))
      (by positivity) (pow_le_pow_left₀ hc.le hb 2)
  exact (norm_sub_le _ _).trans (add_le_add h2 h1)

/-- [FB-E helper] The holomorphic regularised kernel family on `𝔻*` with uniform local bounds, and the uniform bound
for `K₁(G)` on `𝔻* × 𝔻*`. -/
theorem s3fe_bd {f g G : ℂ → ℂ} {ρ CA : ℝ} (hpair : IsNormalizedDisjointPair f g) (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGd' : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0) (hGg : EqOn G g unitDiscExterior)
    (hA : ∀ z ∈ unitDiscExterior, ‖preSchwarzian g z‖ ≤ CA * (‖z‖ ^ 3)⁻¹) :
    ∃ kr : ℂ → ℂ → ℂ, ∃ δ M : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ 0 ≤ M ∧
      (∀ ζ ∈ unitDiscExterior, DifferentiableOn ℂ (kr ζ) unitDiscExterior) ∧
      (∀ ζ ∈ unitDiscExterior, ∀ y ∈ unitDiscExterior, y ≠ ζ →
        kr ζ y = deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2 - preSchwarzian g ζ / (ζ - y)) ∧
      (∀ ζ ∈ unitDiscExterior, ∀ y ∈ unitDiscExterior, ‖ζ - y‖ < δ / 2 →
        ‖kr ζ y‖ ≤ M ∧ ‖deriv (kr ζ) y‖ ≤ M) ∧
      (∀ ω ∈ unitDiscExterior, DifferentiableOn ℂ (fun x => kerK1 G x ω) unitDiscExterior) ∧
      (∀ x ∈ unitDiscExterior, ∀ ω ∈ unitDiscExterior, ‖kerK1 G x ω‖ ≤ M) ∧
      (∀ z ∈ unitDiscExterior, ‖deriv g z‖ ≤ M ∧ ‖preSchwarzian g z‖ ≤ M) := by
  obtain ⟨ρ', δ, c, MG, hρρ', hδ0, hδ4, hc, hMG0, hdom, hMG, hsep⟩ := s3fe_geom hpair hρ hGd hGi hGd' hGg
  obtain ⟨cd, hcd, hdd⟩ := s3fe_dd_lower hpair hρ hGd hGi hGd' hGg
  have hΩ : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEΩ : unitDiscExterior ⊆ {z : ℂ | ρ < ‖z‖} := fun z (hz : (1 : ℝ) < ‖z‖) =>
    (show ρ < ‖z‖ by linarith)
  have hballΩ : ∀ y ∈ unitDiscExterior, closedBall y δ ⊆ {z : ℂ | ρ < ‖z‖} := fun y hy z hz =>
    (show ρ < ‖z‖ from lt_trans hρρ' (hdom y hy z hz))
  -- `G` and `g` agree to second order on `𝔻*`
  have hev : ∀ z ∈ unitDiscExterior, G =ᶠ[𝓝 z] g := fun z hz => by
    filter_upwards [hEo.mem_nhds hz] with w hw using hGg hw
  have hGgd : ∀ z ∈ unitDiscExterior, deriv G z = deriv g z := fun z hz => (hev z hz).deriv_eq
  have hGgA : ∀ z ∈ unitDiscExterior, preSchwarzian G z = preSchwarzian g z := fun z hz => by
    unfold preSchwarzian
    rw [(hev z hz).deriv.deriv_eq, (hev z hz).deriv_eq]
  have hCA : 0 ≤ CA := by
    have h2 : (2 : ℂ) ∈ unitDiscExterior := (show (1 : ℝ) < ‖(2 : ℂ)‖ by norm_num)
    have := (norm_nonneg _).trans (hA 2 h2)
    have hp : (0 : ℝ) < (‖(2 : ℂ)‖ ^ 3)⁻¹ := by norm_num
    nlinarith
  have hAb : ∀ z ∈ unitDiscExterior, ‖preSchwarzian g z‖ ≤ CA := fun z hz => by
    have h1 : (1 : ℝ) < ‖z‖ := hz
    have : (‖z‖ ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1.le)
    exact (hA z hz).trans (by nlinarith)
  -- the separation constant for all pairs at distance `≥ δ/2`
  set c' := min c (cd * (δ / 2)) with hc'
  have hc'0 : 0 < c' := lt_min hc (mul_pos hcd (half_pos hδ0))
  have hfar : ∀ a ∈ unitDiscExterior, ∀ b ∈ unitDiscExterior, δ / 2 ≤ ‖a - b‖ → c' ≤ ‖G a - G b‖ := by
    intro a ha b hb hab
    rw [hGg ha, hGg hb]
    exact (min_le_right _ _).trans ((mul_le_mul_of_nonneg_left hab hcd.le).trans (hdd a ha b hb))
  -- the kernel family
  have hfam : ∀ ζ : ℂ, ∃ k : ℂ → ℂ, ζ ∈ {z : ℂ | ρ < ‖z‖} →
      DifferentiableOn ℂ k {z : ℂ | ρ < ‖z‖} ∧ ∀ y ∈ {z : ℂ | ρ < ‖z‖}, y ≠ ζ →
        k y = deriv G ζ ^ 2 / (G ζ - G y) ^ 2 - 1 / (ζ - y) ^ 2 - preSchwarzian G ζ / (ζ - y) := by
    intro ζ
    by_cases h : ζ ∈ {z : ℂ | ρ < ‖z‖}
    · obtain ⟨k, hk1, hk2⟩ := s3fe_kreg hΩ hGd hGi hGd' h
      exact ⟨k, fun _ => ⟨hk1, hk2⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose kr hkr using hfam
  set M1 := MG ^ 2 / c' ^ 2 + 4 / δ ^ 2 + 2 * CA / δ with hM1
  set Mk := 1 / π * (4 / δ ^ 2 + MG ^ 2 / c' ^ 2) with hMk
  have hM1 : 0 ≤ M1 := by positivity
  have hMk0 : 0 ≤ Mk := by positivity
  refine ⟨kr, δ, max (max M1 (M1 / δ)) (max Mk (max MG CA)), hδ0, hδ4,
    le_trans hM1 ((le_max_left _ _).trans (le_max_left _ _)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ζ hζ => ((hkr ζ (hEΩ hζ)).1).mono hEΩ
  · intro ζ hζ y hy hyζ
    rw [(hkr ζ (hEΩ hζ)).2 y (hEΩ hy) hyζ, hGgd ζ hζ, hGgA ζ hζ, hGg hζ, hGg hy]
  · intro ζ hζ y hy hzy
    have hζb : ζ ∈ closedBall y δ := by
      rw [mem_closedBall, dist_eq_norm]; linarith
    have h := s3fe_cauchy (φ := kr ζ) (y := y) (M := M1) hδ0
      (((hkr ζ (hEΩ hζ)).1).mono (hballΩ y hy)) (by
        intro z hz
        have hzb : z ∈ closedBall y δ := sphere_subset_closedBall hz
        have hzd : ‖z - y‖ = δ := by rw [← dist_eq_norm]; exact hz
        have hζz : δ / 2 ≤ ‖ζ - z‖ := by
          have := norm_sub_norm_le (z - y) (ζ - y)
          rw [show z - y - (ζ - y) = -(ζ - z) by ring, norm_neg] at this
          linarith
        have hzζ : z ≠ ζ := fun h => by rw [h, sub_self, norm_zero] at hζz; linarith
        rw [(hkr ζ (hEΩ hζ)).2 z (hballΩ y hy hzb) hzζ, hGgA ζ hζ]
        exact s3fe_nb hc'0 hδ0 (hMG ζ (hdom y hy ζ hζb))
          ((min_le_left _ _).trans (hsep y hy ζ hζb z hzb hζz)) hζz (hAb ζ hζ))
    exact ⟨h.1.trans ((le_max_left _ _).trans (le_max_left _ _)),
      h.2.trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  · exact fun ω hω => (AppB.differentiableOn_kerK1 hΩ hGd hGi (hEΩ hω)).mono hEΩ
  · intro x hx ω hω
    have hbd : ∀ z ∈ {z : ℂ | ρ < ‖z‖}, ρ' < ‖z‖ → ρ' < ‖ω‖ → c' ≤ ‖G z - G ω‖ → δ / 2 ≤ ‖z - ω‖ →
        ‖kerK1 G z ω‖ ≤ Mk := by
      intro z hz hz' hω' hsepz hzω
      have hne : z ≠ ω := fun h => by rw [h, sub_self, norm_zero] at hzω; linarith
      rw [kerK1_of_ne G hne, norm_mul, hMk]
      have hπ : ‖(1 / π : ℂ)‖ = 1 / π := by
        rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      rw [hπ]
      exact mul_le_mul_of_nonneg_left (s3fe_nk hc'0 hδ0 (hMG z hz') (hMG ω hω') hsepz hzω) (by positivity)
    have hωd : ρ' < ‖ω‖ := hdom ω hω ω (mem_closedBall_self hδ0.le)
    by_cases hxω : ‖x - ω‖ < δ / 2
    · have hωb : ω ∈ closedBall x δ := by
        rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; linarith
      have h := s3fe_cauchy (φ := fun z => kerK1 G z ω) (y := x) (M := Mk) hδ0
        ((AppB.differentiableOn_kerK1 hΩ hGd hGi (hEΩ hω)).mono (hballΩ x hx)) (by
          intro z hz
          have hzb : z ∈ closedBall x δ := sphere_subset_closedBall hz
          have hzd : ‖z - x‖ = δ := by rw [← dist_eq_norm]; exact hz
          have hzω : δ / 2 ≤ ‖z - ω‖ := by
            have := norm_sub_norm_le (z - x) (ω - x)
            rw [show z - x - (ω - x) = z - ω by ring] at this
            rw [norm_sub_rev] at hxω
            linarith
          exact hbd z (hballΩ x hx hzb) (hdom x hx z hzb) hωd
            ((min_le_left _ _).trans (hsep x hx z hzb ω hωb hzω)) hzω)
      exact h.1.trans ((le_max_left _ _).trans (le_max_right _ _))
    · push Not at hxω
      exact (hbd x (hEΩ hx) (hdom x hx x (mem_closedBall_self hδ0.le)) hωd (hfar x hx ω hω hxω) hxω).trans
        ((le_max_left _ _).trans (le_max_right _ _))
  · intro z hz
    refine ⟨?_, (hAb z hz).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))⟩
    rw [← hGgd z hz]
    exact (hMG z (hdom z hz z (mem_closedBall_self hδ0.le))).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- [FB-E helper] Uniform bound for `D(u, ω) = ∂_ω Q_reg(u, ω)`:
`|D| ≤ M_f (1 + |u - ω|)⁻³ + C |𝒜(u)|` (Cauchy estimate near the diagonal, `s3fe_dd_lower` away from it). -/
theorem s3fe_Dbd {f g G R : ℂ → ℂ} {ρ Rb CA : ℝ} (hpair : IsNormalizedDisjointPair f g) (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGd' : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0) (hGg : EqOn G g unitDiscExterior)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hA : ∀ z ∈ unitDiscExterior, ‖preSchwarzian g z‖ ≤ CA * (‖z‖ ^ 3)⁻¹) :
    ∃ Mf C4 : ℝ, 0 ≤ Mf ∧ 0 ≤ C4 ∧ ∀ u ∈ unitDiscExterior, ∀ ω ∈ unitDiscExterior, u ≠ ω →
      ‖2 * deriv g u ^ 2 * deriv g ω / (g u - g ω) ^ 3 - 2 / (u - ω) ^ 3 - preSchwarzian g u / (u - ω) ^ 2‖ ≤
        Mf * ((1 + ‖u - ω‖) ^ 3)⁻¹ + C4 * ‖preSchwarzian g u‖ := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hEo.measurableSet
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨hgd, hgd2, hgi, hgG, hgne⟩ := d2e_basic hρ hGd hGi hGd' hGg
  obtain ⟨kr, δ, M, hδ0, hδ4, hM0, hkrd, hkre, hkrb, hKd, hKb, hgb⟩ :=
    s3fe_bd hpair hρ hGd hGi hGd' hGg hA
  obtain ⟨cd, hcd, hdd⟩ := s3fe_dd_lower hpair hρ hGd hGi hGd' hGg
  set μE := volume.restrict unitDiscExterior with hμE
  set Rb' := max Rb 0 with hRb'
  have hR : ∀ᵐ u ∂μE, ‖R u‖ ≤ Rb' := hRb.mono fun u h => h.trans (le_max_left _ _)
  have hRb0 : 0 ≤ Rb' := le_max_right _ _
  have hCA : 0 ≤ CA := by
    have h2 : (2 : ℂ) ∈ unitDiscExterior := (show (1 : ℝ) < ‖(2 : ℂ)‖ by norm_num)
    have := (norm_nonneg _).trans (hA 2 h2)
    have hp : (0 : ℝ) < (‖(2 : ℂ)‖ ^ 3)⁻¹ := by norm_num
    nlinarith
  have hE1 : ∀ z ∈ unitDiscExterior, (1 : ℝ) < ‖z‖ := fun z hz => hz
  -- measurability of the building blocks
  have hgm : AEMeasurable g μE := (hgd.continuousOn.aestronglyMeasurable hEm).aemeasurable
  have hg1 : Measurable (deriv g) := measurable_deriv g
  have hg2 : Measurable (deriv (deriv g)) := measurable_deriv _
  have hAm : Measurable (preSchwarzian g) := by
    show Measurable fun z => deriv (deriv g) z / deriv g z
    exact hg2.div hg1
  -- the explicit kernels
  obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ → ℂ, D = fun ζ y => 2 * deriv g ζ ^ 2 * deriv g y / (g ζ - g y) ^ 3 -
      2 / (ζ - y) ^ 3 - preSchwarzian g ζ / (ζ - y) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Dk, hDk⟩ : ∃ Dk : ℂ → ℂ → ℂ, Dk = fun x ω => deriv (deriv g) x * deriv g ω / (g x - g ω) ^ 2 -
      2 * deriv g x ^ 2 * deriv g ω / (g x - g ω) ^ 3 + 2 / (x - ω) ^ 3 := ⟨_, rfl⟩
  -- (P1) `∂_y` of the holomorphic regular kernel
  have hP1 : ∀ ζ ∈ unitDiscExterior, ∀ y ∈ unitDiscExterior, y ≠ ζ → deriv (kr ζ) y = D ζ y := by
    intro ζ hζ y hy hyζ
    have hev : kr ζ =ᶠ[𝓝 y] fun w => deriv g ζ ^ 2 / (g ζ - g w) ^ 2 - 1 / (ζ - w) ^ 2 -
        preSchwarzian g ζ / (ζ - w) := by
      filter_upwards [hEo.mem_nhds hy, isOpen_ne.mem_nhds hyζ] with w hw hwζ
      exact hkre ζ hζ w hw hwζ
    rw [hev.deriv_eq, (s3fe_dQ hEo hgd hgi hζ hy hyζ (preSchwarzian g ζ)).deriv, hD]
  -- (P4) the uniform bound for `D`
  set κ := (1 + δ / 2) / (δ / 2) with hκ
  have hκ1 : ∀ t : ℝ, 0 ≤ t → t < δ / 2 → 1 ≤ κ ^ 3 * ((1 + t) ^ 3)⁻¹ := by
    intro t ht0 ht
    rw [← inv_pow, ← mul_pow]
    refine one_le_pow₀ ?_
    rw [hκ, div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity)]
    nlinarith
  have hκ2 : ∀ t : ℝ, δ / 2 ≤ t → (t ^ 3)⁻¹ ≤ κ ^ 3 * ((1 + t) ^ 3)⁻¹ := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (half_pos hδ0) ht
    rw [← inv_pow, ← inv_pow, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 3
    have e : κ * (1 + t)⁻¹ = (1 + δ / 2) / (δ / 2 * (1 + t)) := by rw [hκ]; field_simp
    rw [e, inv_eq_one_div, div_le_div_iff₀ ht0 (by positivity)]
    nlinarith
  set Mf := (M + (2 * M ^ 3 / cd ^ 3 + 2)) * κ ^ 3 with hMf
  have hP4 : ∀ u ∈ unitDiscExterior, ∀ ω ∈ unitDiscExterior, u ≠ ω →
      ‖D u ω‖ ≤ Mf * ((1 + ‖u - ω‖) ^ 3)⁻¹ + 4 / δ ^ 2 * ‖preSchwarzian g u‖ := by
    intro u hu ω hω huω
    have hh : 0 < ‖u - ω‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huω)
    have hA0 : 0 ≤ 4 / δ ^ 2 * ‖preSchwarzian g u‖ := by positivity
    have hW : 0 ≤ ((1 + ‖u - ω‖) ^ 3)⁻¹ := by positivity
    by_cases hnear : ‖u - ω‖ < δ / 2
    · rw [← hP1 u hu ω hω (Ne.symm huω)]
      have hb := (hkrb u hu ω hω hnear).2
      have h1 := hκ1 _ (norm_nonneg _) hnear
      calc ‖deriv (kr u) ω‖ ≤ M := hb
        _ ≤ M * (κ ^ 3 * ((1 + ‖u - ω‖) ^ 3)⁻¹) := le_mul_of_one_le_right hM0 h1
        _ ≤ Mf * ((1 + ‖u - ω‖) ^ 3)⁻¹ := by
            have hp : 0 ≤ (2 * M ^ 3 / cd ^ 3 + 2) * κ ^ 3 * ((1 + ‖u - ω‖) ^ 3)⁻¹ := by positivity
            rw [hMf]
            nlinarith
        _ ≤ _ := le_add_of_nonneg_right hA0
    · push Not at hnear
      have hgu := hdd u hu ω hω
      have hcu : 0 < cd * ‖u - ω‖ := mul_pos hcd hh
      have hgω : 0 < ‖g u - g ω‖ := lt_of_lt_of_le hcu hgu
      have t1 : ‖2 * deriv g u ^ 2 * deriv g ω / (g u - g ω) ^ 3‖ ≤ 2 * M ^ 3 / cd ^ 3 * (‖u - ω‖ ^ 3)⁻¹ := by
        rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat]
        have e1 := (hgb u hu).1
        have e2 := (hgb ω hω).1
        have hn : 2 * (‖deriv g u‖ ^ 2 * ‖deriv g ω‖) ≤ 2 * M ^ 3 := by
          have := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) e1 2) e2 (norm_nonneg _) (by positivity)
          nlinarith
        calc 2 * ‖deriv g u‖ ^ 2 * ‖deriv g ω‖ / ‖g u - g ω‖ ^ 3 ≤ 2 * M ^ 3 / (cd * ‖u - ω‖) ^ 3 := by
              rw [mul_assoc]
              exact div_le_div₀ (by positivity) hn (by positivity) (pow_le_pow_left₀ hcu.le hgu 3)
          _ = _ := by rw [mul_pow]; field_simp
      have t2 : ‖2 / (u - ω) ^ 3‖ = 2 * (‖u - ω‖ ^ 3)⁻¹ := by
        rw [norm_div, norm_pow, Complex.norm_ofNat, div_eq_mul_inv]
      have t3 : ‖preSchwarzian g u / (u - ω) ^ 2‖ ≤ 4 / δ ^ 2 * ‖preSchwarzian g u‖ := by
        rw [norm_div, norm_pow, div_eq_mul_inv, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_le_pow_left₀ (half_pos hδ0).le hnear 2]
      have h2 := hκ2 _ hnear
      rw [hD]
      calc ‖2 * deriv g u ^ 2 * deriv g ω / (g u - g ω) ^ 3 - 2 / (u - ω) ^ 3 -
            preSchwarzian g u / (u - ω) ^ 2‖
          ≤ ‖2 * deriv g u ^ 2 * deriv g ω / (g u - g ω) ^ 3‖ + ‖2 / (u - ω) ^ 3‖ +
            ‖preSchwarzian g u / (u - ω) ^ 2‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ (2 * M ^ 3 / cd ^ 3 + 2) * (‖u - ω‖ ^ 3)⁻¹ + 4 / δ ^ 2 * ‖preSchwarzian g u‖ := by
            rw [t2]; nlinarith [t1, t3]
        _ ≤ _ := by
            refine add_le_add ?_ le_rfl
            have hp : 0 ≤ 2 * M ^ 3 / cd ^ 3 + 2 := by positivity
            calc (2 * M ^ 3 / cd ^ 3 + 2) * (‖u - ω‖ ^ 3)⁻¹
                ≤ (2 * M ^ 3 / cd ^ 3 + 2) * (κ ^ 3 * ((1 + ‖u - ω‖) ^ 3)⁻¹) :=
                  mul_le_mul_of_nonneg_left h2 hp
              _ ≤ Mf * ((1 + ‖u - ω‖) ^ 3)⁻¹ := by
                  have hq : 0 ≤ M * κ ^ 3 * ((1 + ‖u - ω‖) ^ 3)⁻¹ := by positivity
                  rw [hMf]
                  nlinarith
  exact ⟨Mf, 4 / δ ^ 2, by positivity, by positivity, fun u hu ω hω huω => by
    simpa only [hD] using hP4 u hu ω hω huω⟩

/-- [FB-E helper] `ζ ↦ R(ζ) 𝒜(ζ)/(ζ - y)` is integrable on `𝔻*` (`‖·‖⁻¹` locally integrable, `|𝒜| ≤ C|ζ|⁻³`). -/
theorem s3fe_RA {f g G R : ℂ → ℂ} {ρ Rb CA : ℝ} (hpair : IsNormalizedDisjointPair f g) (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGd' : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0) (hGg : EqOn G g unitDiscExterior)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hA : ∀ z ∈ unitDiscExterior, ‖preSchwarzian g z‖ ≤ CA * (‖z‖ ^ 3)⁻¹) :
    ∀ y ∈ unitDiscExterior, Integrable (fun ζ => R ζ * preSchwarzian g ζ / (ζ - y))
      (volume.restrict unitDiscExterior) := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hEo.measurableSet
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨hgd, hgd2, hgi, hgG, hgne⟩ := d2e_basic hρ hGd hGi hGd' hGg
  obtain ⟨kr, δ, M, hδ0, hδ4, hM0, hkrd, hkre, hkrb, hKd, hKb, hgb⟩ :=
    s3fe_bd hpair hρ hGd hGi hGd' hGg hA
  obtain ⟨cd, hcd, hdd⟩ := s3fe_dd_lower hpair hρ hGd hGi hGd' hGg
  set μE := volume.restrict unitDiscExterior with hμE
  set Rb' := max Rb 0 with hRb'
  have hR : ∀ᵐ u ∂μE, ‖R u‖ ≤ Rb' := hRb.mono fun u h => h.trans (le_max_left _ _)
  have hRb0 : 0 ≤ Rb' := le_max_right _ _
  have hCA : 0 ≤ CA := by
    have h2 : (2 : ℂ) ∈ unitDiscExterior := (show (1 : ℝ) < ‖(2 : ℂ)‖ by norm_num)
    have := (norm_nonneg _).trans (hA 2 h2)
    have hp : (0 : ℝ) < (‖(2 : ℂ)‖ ^ 3)⁻¹ := by norm_num
    nlinarith
  have hE1 : ∀ z ∈ unitDiscExterior, (1 : ℝ) < ‖z‖ := fun z hz => hz
  -- measurability of the building blocks
  have hgm : AEMeasurable g μE := (hgd.continuousOn.aestronglyMeasurable hEm).aemeasurable
  have hg1 : Measurable (deriv g) := measurable_deriv g
  have hg2 : Measurable (deriv (deriv g)) := measurable_deriv _
  have hAm : Measurable (preSchwarzian g) := by
    show Measurable fun z => deriv (deriv g) z / deriv g z
    exact hg2.div hg1
  -- the explicit kernels
  obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ → ℂ, D = fun ζ y => 2 * deriv g ζ ^ 2 * deriv g y / (g ζ - g y) ^ 3 -
      2 / (ζ - y) ^ 3 - preSchwarzian g ζ / (ζ - y) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Dk, hDk⟩ : ∃ Dk : ℂ → ℂ → ℂ, Dk = fun x ω => deriv (deriv g) x * deriv g ω / (g x - g ω) ^ 2 -
      2 * deriv g x ^ 2 * deriv g ω / (g x - g ω) ^ 3 + 2 / (x - ω) ^ 3 := ⟨_, rfl⟩
  -- (P1) `∂_y` of the holomorphic regular kernel
  have hP1 : ∀ ζ ∈ unitDiscExterior, ∀ y ∈ unitDiscExterior, y ≠ ζ → deriv (kr ζ) y = D ζ y := by
    intro ζ hζ y hy hyζ
    have hev : kr ζ =ᶠ[𝓝 y] fun w => deriv g ζ ^ 2 / (g ζ - g w) ^ 2 - 1 / (ζ - w) ^ 2 -
        preSchwarzian g ζ / (ζ - w) := by
      filter_upwards [hEo.mem_nhds hy, isOpen_ne.mem_nhds hyζ] with w hw hwζ
      exact hkre ζ hζ w hw hwζ
    rw [hev.deriv_eq, (s3fe_dQ hEo hgd hgi hζ hy hyζ (preSchwarzian g ζ)).deriv, hD]
  have hae : ∀ y : ℂ, ∀ᵐ ζ ∂μE, ζ ≠ y := fun y => ae_restrict_of_ae ((volume : Measure ℂ).ae_ne y)
  have hEae : ∀ᵐ ζ ∂μE, ζ ∈ unitDiscExterior := ae_restrict_mem hEm
  have hw3 : Integrable (fun ζ : ℂ => (‖ζ‖ ^ 3)⁻¹) μE := d2l_powint (by norm_num : 3 ≤ 3)
  -- measurability of `ζ ↦ R ζ · Q_reg(ζ, y)`
  have hQm : ∀ y : ℂ, AEStronglyMeasurable (fun ζ => R ζ * (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2 -
      preSchwarzian g ζ / (ζ - y))) μE := by
    intro y
    refine hRm.mul (AEMeasurable.aestronglyMeasurable ?_)
    exact (((hg1.aemeasurable.pow_const 2).div ((hgm.sub_const (g y)).pow_const 2)).sub
      (aemeasurable_const.div ((measurable_id.sub_const y).aemeasurable.pow_const 2))).sub
      (hAm.aemeasurable.div (measurable_id.sub_const y).aemeasurable)
  -- `ζ ↦ R ζ 𝒜(ζ)/(ζ - y)` is integrable
  have hRA : ∀ y ∈ unitDiscExterior, Integrable (fun ζ => R ζ * preSchwarzian g ζ / (ζ - y)) μE := by
    intro y hy
    have hI : Integrable (fun ζ => (ball (0 : ℂ) (1 / 2)).indicator (fun u => ‖u‖⁻¹) (ζ - y)) μE :=
      (((phiKernel_inv_norm_integrableOn.integrable_indicator measurableSet_ball).comp_sub_right y).integrableOn)
    have hbound : Integrable (fun ζ => Rb' * (M * (ball (0 : ℂ) (1 / 2)).indicator (fun u => ‖u‖⁻¹) (ζ - y) +
        2 * CA * (‖ζ‖ ^ 3)⁻¹)) μE :=
      Integrable.const_mul ((Integrable.const_mul hI M).add (Integrable.const_mul hw3 (2 * CA))) Rb'
    refine Integrable.mono' hbound (((hRm.aemeasurable.mul hAm.aemeasurable).div
      (measurable_id.sub_const y).aemeasurable).aestronglyMeasurable) ?_
    filter_upwards [hR, hEae] with ζ hRζ hζ
    have hAζ : ‖preSchwarzian g ζ‖ ≤ M := (hgb ζ hζ).2
    have hAζ' := hA ζ hζ
    have hw0 : 0 ≤ (‖ζ‖ ^ 3)⁻¹ := by positivity
    rw [norm_div, norm_mul]
    by_cases hb : ζ - y ∈ ball (0 : ℂ) (1 / 2)
    · rw [indicator_of_mem hb]
      calc ‖R ζ‖ * ‖preSchwarzian g ζ‖ / ‖ζ - y‖ = ‖R ζ‖ * (‖preSchwarzian g ζ‖ * ‖ζ - y‖⁻¹) := by
            rw [div_eq_mul_inv, mul_assoc]
        _ ≤ Rb' * (M * ‖ζ - y‖⁻¹) :=
            mul_le_mul hRζ (mul_le_mul_of_nonneg_right hAζ (inv_nonneg.mpr (norm_nonneg _))) (by positivity)
              hRb0
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hRb0
    · rw [indicator_of_notMem hb, mul_zero, zero_add]
      have hge : 1 / 2 ≤ ‖ζ - y‖ := by
        rw [mem_ball, dist_zero_right, not_lt] at hb; exact hb
      have hpos : 0 < ‖ζ - y‖ := lt_of_lt_of_le (by norm_num) hge
      calc ‖R ζ‖ * ‖preSchwarzian g ζ‖ / ‖ζ - y‖ ≤ Rb' * ‖preSchwarzian g ζ‖ / (1 / 2) := by
            gcongr
        _ ≤ Rb' * (2 * CA * (‖ζ‖ ^ 3)⁻¹) := by
            rw [div_eq_mul_inv, mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ hRb0
            norm_num
            nlinarith
  exact hRA

/-- [FB-E helper] `dz` of `Φ(y) = ∫ R Qk(·, y)`: `dz Φ = ∫ R ∂_y Q_reg(·, z) + dz C` (`d2p_param` on the holomorphic
regular kernel; far field by `s3fe_Q_decay`). -/
theorem s3fe_S1 {f g G R : ℂ → ℂ} {ρ Rb CA : ℝ} (hpair : IsNormalizedDisjointPair f g) (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGd' : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0) (hGg : EqOn G g unitDiscExterior)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hA : ∀ z ∈ unitDiscExterior, ‖preSchwarzian g z‖ ≤ CA * (‖z‖ ^ 3)⁻¹)
    (hC1 : ContDiffOn ℝ 1 (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * preSchwarzian g ζ / (ζ - y))
      unitDiscExterior) :
    ∀ z ∈ unitDiscExterior, Integrable (fun ζ => R ζ * (2 * deriv g ζ ^ 2 * deriv g z / (g ζ - g z) ^ 3 - 2 / (ζ - z) ^ 3 - preSchwarzian g ζ / (ζ - z) ^ 2)) (volume.restrict unitDiscExterior) ∧
      dz (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2)) z =
        (∫ ζ in unitDiscExterior, R ζ * (2 * deriv g ζ ^ 2 * deriv g z / (g ζ - g z) ^ 3 - 2 / (ζ - z) ^ 3 - preSchwarzian g ζ / (ζ - z) ^ 2)) +
          dz (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * preSchwarzian g ζ / (ζ - y)) z := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hEo.measurableSet
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨hgd, hgd2, hgi, hgG, hgne⟩ := d2e_basic hρ hGd hGi hGd' hGg
  obtain ⟨kr, δ, M, hδ0, hδ4, hM0, hkrd, hkre, hkrb, hKd, hKb, hgb⟩ :=
    s3fe_bd hpair hρ hGd hGi hGd' hGg hA
  obtain ⟨cd, hcd, hdd⟩ := s3fe_dd_lower hpair hρ hGd hGi hGd' hGg
  set μE := volume.restrict unitDiscExterior with hμE
  set Rb' := max Rb 0 with hRb'
  have hR : ∀ᵐ u ∂μE, ‖R u‖ ≤ Rb' := hRb.mono fun u h => h.trans (le_max_left _ _)
  have hRb0 : 0 ≤ Rb' := le_max_right _ _
  have hCA : 0 ≤ CA := by
    have h2 : (2 : ℂ) ∈ unitDiscExterior := (show (1 : ℝ) < ‖(2 : ℂ)‖ by norm_num)
    have := (norm_nonneg _).trans (hA 2 h2)
    have hp : (0 : ℝ) < (‖(2 : ℂ)‖ ^ 3)⁻¹ := by norm_num
    nlinarith
  have hE1 : ∀ z ∈ unitDiscExterior, (1 : ℝ) < ‖z‖ := fun z hz => hz
  -- measurability of the building blocks
  have hgm : AEMeasurable g μE := (hgd.continuousOn.aestronglyMeasurable hEm).aemeasurable
  have hg1 : Measurable (deriv g) := measurable_deriv g
  have hg2 : Measurable (deriv (deriv g)) := measurable_deriv _
  have hAm : Measurable (preSchwarzian g) := by
    show Measurable fun z => deriv (deriv g) z / deriv g z
    exact hg2.div hg1
  -- the explicit kernels
  obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ → ℂ, D = fun ζ y => 2 * deriv g ζ ^ 2 * deriv g y / (g ζ - g y) ^ 3 -
      2 / (ζ - y) ^ 3 - preSchwarzian g ζ / (ζ - y) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Dk, hDk⟩ : ∃ Dk : ℂ → ℂ → ℂ, Dk = fun x ω => deriv (deriv g) x * deriv g ω / (g x - g ω) ^ 2 -
      2 * deriv g x ^ 2 * deriv g ω / (g x - g ω) ^ 3 + 2 / (x - ω) ^ 3 := ⟨_, rfl⟩
  -- (P1) `∂_y` of the holomorphic regular kernel
  have hP1 : ∀ ζ ∈ unitDiscExterior, ∀ y ∈ unitDiscExterior, y ≠ ζ → deriv (kr ζ) y = D ζ y := by
    intro ζ hζ y hy hyζ
    have hev : kr ζ =ᶠ[𝓝 y] fun w => deriv g ζ ^ 2 / (g ζ - g w) ^ 2 - 1 / (ζ - w) ^ 2 -
        preSchwarzian g ζ / (ζ - w) := by
      filter_upwards [hEo.mem_nhds hy, isOpen_ne.mem_nhds hyζ] with w hw hwζ
      exact hkre ζ hζ w hw hwζ
    rw [hev.deriv_eq, (s3fe_dQ hEo hgd hgi hζ hy hyζ (preSchwarzian g ζ)).deriv, hD]
  have hae : ∀ y : ℂ, ∀ᵐ ζ ∂μE, ζ ≠ y := fun y => ae_restrict_of_ae ((volume : Measure ℂ).ae_ne y)
  have hEae : ∀ᵐ ζ ∂μE, ζ ∈ unitDiscExterior := ae_restrict_mem hEm
  have hw3 : Integrable (fun ζ : ℂ => (‖ζ‖ ^ 3)⁻¹) μE := d2l_powint (by norm_num : 3 ≤ 3)
  -- measurability of `ζ ↦ R ζ · Q_reg(ζ, y)`
  have hQm : ∀ y : ℂ, AEStronglyMeasurable (fun ζ => R ζ * (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2 -
      preSchwarzian g ζ / (ζ - y))) μE := by
    intro y
    refine hRm.mul (AEMeasurable.aestronglyMeasurable ?_)
    exact (((hg1.aemeasurable.pow_const 2).div ((hgm.sub_const (g y)).pow_const 2)).sub
      (aemeasurable_const.div ((measurable_id.sub_const y).aemeasurable.pow_const 2))).sub
      (hAm.aemeasurable.div (measurable_id.sub_const y).aemeasurable)
  have hRA := s3fe_RA hpair hρ hGd hGi hGd' hGg hRm hRb hA
  -- (S1) `dz Φ = ∫ R D(·, z) + dz C`
  have hS1 : ∀ z ∈ unitDiscExterior, Integrable (fun ζ => R ζ * D ζ z) μE ∧
      dz (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2)) z =
        (∫ ζ in unitDiscExterior, R ζ * D ζ z) +
          dz (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * preSchwarzian g ζ / (ζ - y)) z := by
    intro z hz
    have hz1 := hE1 z hz
    set r := min (δ / 16) ((‖z‖ - 1) / 4) with hr
    have hr0 : 0 < r := lt_min (by positivity) (by linarith)
    have hr1 : r ≤ δ / 16 := min_le_left _ _
    have hr2 : r ≤ (‖z‖ - 1) / 4 := min_le_right _ _
    have hball : closedBall z (2 * r) ⊆ unitDiscExterior := by
      intro y hy
      have h1 : dist y z ≤ 2 * r := hy
      have h3 := norm_sub_norm_le z y
      rw [← dist_eq_norm, dist_comm] at h3
      show (1 : ℝ) < ‖y‖
      linarith
    obtain ⟨T, CQ, hQ⟩ := s3fe_Q_decay hpair hρ hGd hGi hGd' hGg (isCompact_closedBall z (2 * r)) hball
    set T' := max T (‖z‖ + 2) with hT'
    set Mc := M + (M ^ 2 / (cd * (δ / 2)) ^ 2 + 4 / δ ^ 2 + 2 * 0 / δ) with hMc
    set Cd := |CQ| + 2 * CA / δ with hCd
    have hMc0 : 0 ≤ Mc := by positivity
    have hCd0 : 0 ≤ Cd := by positivity
    set Bf : ℂ → ℝ := fun ζ => Rb' * (Mc * (ball (0 : ℂ) T').indicator (fun _ => (1 : ℝ)) ζ +
      Cd * (‖ζ‖ ^ 3)⁻¹) with hBf
    have hBi : Integrable Bf μE := by
      have h1 : Integrable ((ball (0 : ℂ) T').indicator (fun _ => (1 : ℝ))) μE :=
        ((integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball).integrableOn
      exact Integrable.const_mul ((Integrable.const_mul h1 Mc).add (Integrable.const_mul hw3 Cd)) Rb'
    have hB : ∀ᵐ ζ ∂μE, ∀ y ∈ closedBall z (2 * r), ‖R ζ * kr ζ y‖ ≤ Bf ζ := by
      filter_upwards [hR, hEae] with ζ hRζ hζ y hy
      have hyE := hball hy
      have hw0 : 0 ≤ (‖ζ‖ ^ 3)⁻¹ := by positivity
      have hyz : ‖y‖ ≤ ‖z‖ + 2 * r := by
        have h1 : dist y z ≤ 2 * r := hy
        have h3 := norm_le_norm_add_norm_sub' y z
        rw [← dist_eq_norm] at h3
        linarith
      -- the bound for `kr`
      have hK : ‖kr ζ y‖ ≤ Mc * (ball (0 : ℂ) T').indicator (fun _ => (1 : ℝ)) ζ + Cd * (‖ζ‖ ^ 3)⁻¹ := by
        by_cases hnear : ‖ζ - y‖ < δ / 2
        · have hin : ζ ∈ ball (0 : ℂ) T' := by
            rw [mem_ball_zero_iff]
            have h3 := norm_le_norm_add_norm_sub' ζ y
            have : δ / 2 < 1 := by linarith
            have : 2 * r < 1 := by linarith
            exact lt_of_le_of_lt h3 (by linarith [le_max_right T (‖z‖ + 2)])
          rw [indicator_of_mem hin]
          have := (hkrb ζ hζ y hyE hnear).1
          have : M ≤ Mc := le_add_of_nonneg_right (by positivity)
          nlinarith
        · push Not at hnear
          have hζy : y ≠ ζ := fun h => by rw [h, sub_self, norm_zero] at hnear; linarith
          rw [hkre ζ hζ y hyE hζy]
          have hd0 : 0 < ‖ζ - y‖ := lt_of_lt_of_le (half_pos hδ0) hnear
          have hA2 : ‖preSchwarzian g ζ / (ζ - y)‖ ≤ 2 * CA / δ * (‖ζ‖ ^ 3)⁻¹ := by
            rw [norm_div]
            calc ‖preSchwarzian g ζ‖ / ‖ζ - y‖ ≤ CA * (‖ζ‖ ^ 3)⁻¹ / (δ / 2) :=
                  div_le_div₀ (by positivity) (hA ζ hζ) (half_pos hδ0) hnear
              _ = _ := by field_simp
          have hsep : cd * (δ / 2) ≤ ‖g ζ - g y‖ :=
            (mul_le_mul_of_nonneg_left hnear hcd.le).trans (hdd ζ hζ y hyE)
          have hQ1 : ‖deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2‖ ≤
              M ^ 2 / (cd * (δ / 2)) ^ 2 + 4 / δ ^ 2 + 2 * 0 / δ := by
            have h := s3fe_nb (e := 0) (Me := 0) (mul_pos hcd (half_pos hδ0)) hδ0 (hgb ζ hζ).1 hsep hnear
              (by simp)
            simpa using h
          refine (norm_sub_le _ _).trans ?_
          by_cases hT : T ≤ ‖ζ‖
          · have hq := hQ y hy ζ hT
            have h1 : ‖deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2‖ ≤ |CQ| * (‖ζ‖ ^ 3)⁻¹ :=
              hq.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hw0)
            have hi : 0 ≤ Mc * (ball (0 : ℂ) T').indicator (fun _ => (1 : ℝ)) ζ := by
              apply mul_nonneg hMc0; exact indicator_nonneg (fun _ _ => zero_le_one) _
            rw [hCd]
            nlinarith
          · push Not at hT
            have hin : ζ ∈ ball (0 : ℂ) T' := by
              rw [mem_ball_zero_iff]; exact lt_of_lt_of_le hT (le_max_left _ _)
            rw [indicator_of_mem hin, mul_one]
            have : M ^ 2 / (cd * (δ / 2)) ^ 2 + 4 / δ ^ 2 + 2 * 0 / δ ≤ Mc := le_add_of_nonneg_left hM0
            have : 0 ≤ |CQ| * (‖ζ‖ ^ 3)⁻¹ := by positivity
            rw [hCd]
            nlinarith
      rw [norm_mul, hBf]
      exact mul_le_mul hRζ hK (norm_nonneg _) hRb0
    have hkd : ∀ᵐ ζ ∂μE, DifferentiableOn ℂ (fun y => R ζ * kr ζ y) unitDiscExterior := by
      filter_upwards [hEae] with ζ hζ using (differentiableOn_const _).mul (hkrd ζ hζ)
    have hkm : ∀ y ∈ unitDiscExterior, AEStronglyMeasurable (fun ζ => R ζ * kr ζ y) μE := by
      intro y hy
      refine (hQm y).congr ?_
      filter_upwards [hEae, hae y] with ζ hζ hζy
      rw [hkre ζ hζ y hy (Ne.symm hζy)]
    obtain ⟨-, hi1, hder⟩ := d2p_param hEo hr0 hball hkd hkm hBi hB
    have hdk : (fun ζ => deriv (fun y => R ζ * kr ζ y) z) =ᵐ[μE] fun ζ => R ζ * D ζ z := by
      filter_upwards [hEae, hae z] with ζ hζ hζz
      rw [deriv_const_mul _ ((hkrd ζ hζ).differentiableAt (hEo.mem_nhds hz)), hP1 ζ hζ z hz (Ne.symm hζz)]
    refine ⟨hi1.congr hdk, ?_⟩
    have hev : (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2))
        =ᶠ[𝓝 z] fun y => (∫ ζ, R ζ * kr ζ y ∂μE) +
          ∫ ζ in unitDiscExterior, R ζ * preSchwarzian g ζ / (ζ - y) := by
      filter_upwards [ball_mem_nhds z hr0] with y hy
      have hy2 : y ∈ closedBall z (2 * r) := ball_subset_closedBall (ball_subset_ball (by linarith) hy)
      have hyE := hball hy2
      have hi : Integrable (fun ζ => R ζ * kr ζ y) μE :=
        Integrable.mono' hBi (hkm y hyE) (hB.mono fun ζ h => h y hy2)
      rw [← integral_add hi (hRA y hyE)]
      refine integral_congr_ae ?_
      filter_upwards [hEae, hae y] with ζ hζ hζy
      rw [hkre ζ hζ y hyE (Ne.symm hζy)]
      ring
    have hCd' : DifferentiableAt ℝ (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * preSchwarzian g ζ / (ζ - y)) z :=
      (hC1.differentiableOn one_ne_zero z hz).differentiableAt (hEo.mem_nhds hz)
    rw [s3fe_dz_congr hev, s3fe_dz_add (hder.differentiableAt.restrictScalars ℝ) hCd',
      dz_eq_deriv hder.differentiableAt, hder.deriv, integral_congr_ae hdk]
  intro z hz
  simpa only [hD] using hS1 z hz

/-- [FB-E helper] `h₂` is holomorphic on `𝔻*` with `h₂'(u) = (1/π) ∫ conj 𝒜(ω) ∂ₓk̃(u, ω)` (`d2p_param` on the
holomorphic `K₁(G)(·, ω)`), the integrands being integrable. -/
theorem s3fe_S2 {f g G R : ℂ → ℂ} {ρ Rb CA : ℝ} (hpair : IsNormalizedDisjointPair f g) (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGd' : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0) (hGg : EqOn G g unitDiscExterior)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hA : ∀ z ∈ unitDiscExterior, ‖preSchwarzian g z‖ ≤ CA * (‖z‖ ^ 3)⁻¹) :
    ∀ u ∈ unitDiscExterior,
      Integrable (fun ω => conj (preSchwarzian g ω) * (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2))
        (volume.restrict unitDiscExterior) ∧
      Integrable (fun ω => conj (preSchwarzian g ω) * (deriv (deriv g) u * deriv g ω / (g u - g ω) ^ 2 - 2 * deriv g u ^ 2 * deriv g ω / (g u - g ω) ^ 3 + 2 / (u - ω) ^ 3)) (volume.restrict unitDiscExterior) ∧
      HasDerivAt (fun x : ℂ => (1 / π : ℂ) * ∫ ω in unitDiscExterior,
          conj (preSchwarzian g ω) * (deriv g x * deriv g ω / (g x - g ω) ^ 2 - 1 / (x - ω) ^ 2))
        ((1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian g ω) * (deriv (deriv g) u * deriv g ω / (g u - g ω) ^ 2 - 2 * deriv g u ^ 2 * deriv g ω / (g u - g ω) ^ 3 + 2 / (u - ω) ^ 3)) u := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hEo.measurableSet
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨hgd, hgd2, hgi, hgG, hgne⟩ := d2e_basic hρ hGd hGi hGd' hGg
  obtain ⟨kr, δ, M, hδ0, hδ4, hM0, hkrd, hkre, hkrb, hKd, hKb, hgb⟩ :=
    s3fe_bd hpair hρ hGd hGi hGd' hGg hA
  obtain ⟨cd, hcd, hdd⟩ := s3fe_dd_lower hpair hρ hGd hGi hGd' hGg
  set μE := volume.restrict unitDiscExterior with hμE
  set Rb' := max Rb 0 with hRb'
  have hR : ∀ᵐ u ∂μE, ‖R u‖ ≤ Rb' := hRb.mono fun u h => h.trans (le_max_left _ _)
  have hRb0 : 0 ≤ Rb' := le_max_right _ _
  have hCA : 0 ≤ CA := by
    have h2 : (2 : ℂ) ∈ unitDiscExterior := (show (1 : ℝ) < ‖(2 : ℂ)‖ by norm_num)
    have := (norm_nonneg _).trans (hA 2 h2)
    have hp : (0 : ℝ) < (‖(2 : ℂ)‖ ^ 3)⁻¹ := by norm_num
    nlinarith
  have hE1 : ∀ z ∈ unitDiscExterior, (1 : ℝ) < ‖z‖ := fun z hz => hz
  -- measurability of the building blocks
  have hgm : AEMeasurable g μE := (hgd.continuousOn.aestronglyMeasurable hEm).aemeasurable
  have hg1 : Measurable (deriv g) := measurable_deriv g
  have hg2 : Measurable (deriv (deriv g)) := measurable_deriv _
  have hAm : Measurable (preSchwarzian g) := by
    show Measurable fun z => deriv (deriv g) z / deriv g z
    exact hg2.div hg1
  -- the explicit kernels
  obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ → ℂ, D = fun ζ y => 2 * deriv g ζ ^ 2 * deriv g y / (g ζ - g y) ^ 3 -
      2 / (ζ - y) ^ 3 - preSchwarzian g ζ / (ζ - y) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Dk, hDk⟩ : ∃ Dk : ℂ → ℂ → ℂ, Dk = fun x ω => deriv (deriv g) x * deriv g ω / (g x - g ω) ^ 2 -
      2 * deriv g x ^ 2 * deriv g ω / (g x - g ω) ^ 3 + 2 / (x - ω) ^ 3 := ⟨_, rfl⟩
  -- (P1) `∂_y` of the holomorphic regular kernel
  have hP1 : ∀ ζ ∈ unitDiscExterior, ∀ y ∈ unitDiscExterior, y ≠ ζ → deriv (kr ζ) y = D ζ y := by
    intro ζ hζ y hy hyζ
    have hev : kr ζ =ᶠ[𝓝 y] fun w => deriv g ζ ^ 2 / (g ζ - g w) ^ 2 - 1 / (ζ - w) ^ 2 -
        preSchwarzian g ζ / (ζ - w) := by
      filter_upwards [hEo.mem_nhds hy, isOpen_ne.mem_nhds hyζ] with w hw hwζ
      exact hkre ζ hζ w hw hwζ
    rw [hev.deriv_eq, (s3fe_dQ hEo hgd hgi hζ hy hyζ (preSchwarzian g ζ)).deriv, hD]
  -- (P2) the `k̃` kernel through `K₁(G)` and its `x`-derivative
  have hKt : ∀ x ∈ unitDiscExterior, ∀ ω ∈ unitDiscExterior, x ≠ ω →
      -(π : ℂ) * kerK1 G x ω = deriv g x * deriv g ω / (g x - g ω) ^ 2 - 1 / (x - ω) ^ 2 := by
    intro x hx ω hω hxω
    rw [kerK1_of_ne G hxω, ← hgG x hx, ← hgG ω hω, hGg hx, hGg hω]
    field_simp
    ring
  have hP2 : ∀ ω ∈ unitDiscExterior, ∀ u ∈ unitDiscExterior, u ≠ ω →
      deriv (fun x => -(π : ℂ) * kerK1 G x ω) u = Dk u ω := by
    intro ω hω u hu huω
    have hev : (fun x => -(π : ℂ) * kerK1 G x ω) =ᶠ[𝓝 u]
        fun v => deriv g v * deriv g ω / (g v - g ω) ^ 2 - 1 / (v - ω) ^ 2 := by
      filter_upwards [hEo.mem_nhds hu, isOpen_ne.mem_nhds huω] with v hv hvω
      exact hKt v hv ω hω hvω
    rw [hev.deriv_eq, (s3fe_dk hEo hgd hgi hu hω huω).deriv, hDk]
  -- (P3) the kernel identity
  have hP3 : ∀ u ∈ unitDiscExterior, ∀ ω ∈ unitDiscExterior, u ≠ ω →
      Dk u ω - preSchwarzian g u * (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2) = -D u ω := by
    intro u hu ω hω huω
    rw [hDk, hD]
    exact s3fe_alg (sub_ne_zero.mpr fun h => huω (hgi hu hω h)) (sub_ne_zero.mpr huω) (hgne u hu)
  have hEae : ∀ᵐ ζ ∂μE, ζ ∈ unitDiscExterior := ae_restrict_mem hEm
  have hae : ∀ y : ℂ, ∀ᵐ ζ ∂μE, ζ ≠ y := fun y => ae_restrict_of_ae ((volume : Measure ℂ).ae_ne y)
  have hw3 : Integrable (fun ζ : ℂ => (‖ζ‖ ^ 3)⁻¹) μE := d2l_powint (by norm_num : 3 ≤ 3)
  have hcAm : Measurable fun ω => conj (preSchwarzian g ω) := Complex.continuous_conj.measurable.comp hAm
  have hAi : Integrable (fun ω => ‖preSchwarzian g ω‖) μE := by
    refine Integrable.mono' (Integrable.const_mul hw3 CA) hAm.aestronglyMeasurable.norm ?_
    filter_upwards [hEae] with ω hω
    rw [norm_norm]; exact hA ω hω
  intro u hu
  have hu1 := hE1 u hu
  set r := min (1 / 2) ((‖u‖ - 1) / 4) with hr
  have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
  have hr2 : r ≤ (‖u‖ - 1) / 4 := min_le_right _ _
  have hball : closedBall u (2 * r) ⊆ unitDiscExterior := by
    intro y hy
    have h1 : dist y u ≤ 2 * r := hy
    have h3 := norm_sub_norm_le u y
    rw [← dist_eq_norm, dist_comm] at h3
    show (1 : ℝ) < ‖y‖
    linarith
  have hktm : ∀ x : ℂ, AEStronglyMeasurable (fun ω => conj (preSchwarzian g ω) *
      (deriv g x * deriv g ω / (g x - g ω) ^ 2 - 1 / (x - ω) ^ 2)) μE := by
    intro x
    refine hcAm.aestronglyMeasurable.mul (AEMeasurable.aestronglyMeasurable ?_)
    exact ((aemeasurable_const.mul hg1.aemeasurable).div ((aemeasurable_const.sub hgm).pow_const 2)).sub
      (aemeasurable_const.div ((aemeasurable_const.sub measurable_id.aemeasurable).pow_const 2))
  have hkd : ∀ᵐ ω ∂μE, DifferentiableOn ℂ (fun x => conj (preSchwarzian g ω) * (-(π : ℂ) * kerK1 G x ω))
      unitDiscExterior := by
    filter_upwards [hEae] with ω hω using (differentiableOn_const _).mul ((differentiableOn_const _).mul (hKd ω hω))
  have hkm : ∀ x ∈ unitDiscExterior, AEStronglyMeasurable
      (fun ω => conj (preSchwarzian g ω) * (-(π : ℂ) * kerK1 G x ω)) μE := by
    intro x hx
    refine (hktm x).congr ?_
    filter_upwards [hEae, hae x] with ω hω hωx
    rw [hKt x hx ω hω (Ne.symm hωx)]
  have hBi : Integrable (fun ω => ‖preSchwarzian g ω‖ * (π * M)) μE := hAi.mul_const _
  have hB : ∀ᵐ ω ∂μE, ∀ x ∈ closedBall u (2 * r),
      ‖conj (preSchwarzian g ω) * (-(π : ℂ) * kerK1 G x ω)‖ ≤ ‖preSchwarzian g ω‖ * (π * M) := by
    filter_upwards [hEae] with ω hω x hx
    rw [norm_mul, norm_mul, RCLike.norm_conj, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hKb x (hball hx) ω hω) Real.pi_pos.le)
      (norm_nonneg _)
  obtain ⟨hi0, hi1, hder⟩ := d2p_param hEo hr0 hball hkd hkm hBi hB
  have hk0 : (fun ω => conj (preSchwarzian g ω) * (-(π : ℂ) * kerK1 G u ω)) =ᵐ[μE]
      fun ω => conj (preSchwarzian g ω) * (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2) := by
    filter_upwards [hEae, hae u] with ω hω hωu
    rw [hKt u hu ω hω (Ne.symm hωu)]
  have hk1 : (fun ω => deriv (fun x => conj (preSchwarzian g ω) * (-(π : ℂ) * kerK1 G x ω)) u) =ᵐ[μE]
      fun ω => conj (preSchwarzian g ω) * Dk u ω := by
    filter_upwards [hEae, hae u] with ω hω hωu
    rw [deriv_const_mul _ (((hKd ω hω).differentiableAt (hEo.mem_nhds hu)).const_mul _),
      hP2 ω hω u hu (Ne.symm hωu)]
  have hev : (fun x : ℂ => ∫ ω in unitDiscExterior, conj (preSchwarzian g ω) *
      (deriv g x * deriv g ω / (g x - g ω) ^ 2 - 1 / (x - ω) ^ 2)) =ᶠ[𝓝 u]
      fun x => ∫ ω, conj (preSchwarzian g ω) * (-(π : ℂ) * kerK1 G x ω) ∂μE := by
    filter_upwards [hEo.mem_nhds hu] with x hx
    refine integral_congr_ae ?_
    filter_upwards [hEae, hae x] with ω hω hωx
    rw [hKt x hx ω hω (Ne.symm hωx)]
  have h := (hder.congr_of_eventuallyEq hev).const_mul (1 / π : ℂ)
  rw [integral_congr_ae hk1] at h
  subst hDk
  refine ⟨hi0.congr hk0, hi1.congr hk1, ?_⟩
  beta_reduce at h
  exact h

/-- **(FB-E)** The exterior part of F-FUB. -/
theorem s3fe_ext {f g G R : ℂ → ℂ} {ρ Rb CA : ℝ} (hpair : IsNormalizedDisjointPair f g) (hρ : ρ < 1)
    (hGd : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖}) (hGi : InjOn G {z : ℂ | ρ < ‖z‖})
    (hGd' : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0) (hGg : EqOn G g unitDiscExterior)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hA : ∀ z ∈ unitDiscExterior, ‖preSchwarzian g z‖ ≤ CA * (‖z‖ ^ 3)⁻¹)
    (hC1 : ContDiffOn ℝ 1 (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * preSchwarzian g ζ / (ζ - y))
      unitDiscExterior)
    (hCi : IntegrableOn (fun z => conj (preSchwarzian g z) *
      dz (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * preSchwarzian g ζ / (ζ - y)) z) unitDiscExterior) :
    IntegrableOn (fun z => conj (preSchwarzian g z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior,
        R ζ * (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2)) z)) unitDiscExterior ∧
      (∀ u ∈ unitDiscExterior, DifferentiableAt ℂ (fun x : ℂ => (1 / π : ℂ) * ∫ ω in unitDiscExterior,
        conj (preSchwarzian g ω) * (deriv g x * deriv g ω / (g x - g ω) ^ 2 - 1 / (x - ω) ^ 2)) u) ∧
      IntegrableOn (fun u => R u * (deriv (fun x : ℂ => (1 / π : ℂ) * ∫ ω in unitDiscExterior,
        conj (preSchwarzian g ω) * (deriv g x * deriv g ω / (g x - g ω) ^ 2 - 1 / (x - ω) ^ 2)) u -
        preSchwarzian g u * ((1 / π : ℂ) * ∫ ω in unitDiscExterior,
          conj (preSchwarzian g ω) * (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2))))
        unitDiscExterior ∧
      (∫ z in unitDiscExterior, conj (preSchwarzian g z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior,
          R ζ * (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2)) z)) =
        (∫ u in unitDiscExterior, R u * (deriv (fun x : ℂ => (1 / π : ℂ) * ∫ ω in unitDiscExterior,
          conj (preSchwarzian g ω) * (deriv g x * deriv g ω / (g x - g ω) ^ 2 - 1 / (x - ω) ^ 2)) u -
          preSchwarzian g u * ((1 / π : ℂ) * ∫ ω in unitDiscExterior,
            conj (preSchwarzian g ω) * (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2)))) -
        (1 / π : ℂ) * ∫ z in unitDiscExterior, conj (preSchwarzian g z) *
          dz (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * preSchwarzian g ζ / (ζ - y)) z := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hEo.measurableSet
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨hgd, hgd2, hgi, hgG, hgne⟩ := d2e_basic hρ hGd hGi hGd' hGg
  obtain ⟨kr, δ, M, hδ0, hδ4, hM0, hkrd, hkre, hkrb, hKd, hKb, hgb⟩ :=
    s3fe_bd hpair hρ hGd hGi hGd' hGg hA
  obtain ⟨cd, hcd, hdd⟩ := s3fe_dd_lower hpair hρ hGd hGi hGd' hGg
  set μE := volume.restrict unitDiscExterior with hμE
  set Rb' := max Rb 0 with hRb'
  have hR : ∀ᵐ u ∂μE, ‖R u‖ ≤ Rb' := hRb.mono fun u h => h.trans (le_max_left _ _)
  have hRb0 : 0 ≤ Rb' := le_max_right _ _
  have hCA : 0 ≤ CA := by
    have h2 : (2 : ℂ) ∈ unitDiscExterior := (show (1 : ℝ) < ‖(2 : ℂ)‖ by norm_num)
    have := (norm_nonneg _).trans (hA 2 h2)
    have hp : (0 : ℝ) < (‖(2 : ℂ)‖ ^ 3)⁻¹ := by norm_num
    nlinarith
  have hE1 : ∀ z ∈ unitDiscExterior, (1 : ℝ) < ‖z‖ := fun z hz => hz
  -- measurability of the building blocks
  have hgm : AEMeasurable g μE := (hgd.continuousOn.aestronglyMeasurable hEm).aemeasurable
  have hg1 : Measurable (deriv g) := measurable_deriv g
  have hg2 : Measurable (deriv (deriv g)) := measurable_deriv _
  have hAm : Measurable (preSchwarzian g) := by
    show Measurable fun z => deriv (deriv g) z / deriv g z
    exact hg2.div hg1
  -- the explicit kernels
  obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ → ℂ, D = fun ζ y => 2 * deriv g ζ ^ 2 * deriv g y / (g ζ - g y) ^ 3 -
      2 / (ζ - y) ^ 3 - preSchwarzian g ζ / (ζ - y) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Dk, hDk⟩ : ∃ Dk : ℂ → ℂ → ℂ, Dk = fun x ω => deriv (deriv g) x * deriv g ω / (g x - g ω) ^ 2 -
      2 * deriv g x ^ 2 * deriv g ω / (g x - g ω) ^ 3 + 2 / (x - ω) ^ 3 := ⟨_, rfl⟩
  -- (P1) `∂_y` of the holomorphic regular kernel
  have hP1 : ∀ ζ ∈ unitDiscExterior, ∀ y ∈ unitDiscExterior, y ≠ ζ → deriv (kr ζ) y = D ζ y := by
    intro ζ hζ y hy hyζ
    have hev : kr ζ =ᶠ[𝓝 y] fun w => deriv g ζ ^ 2 / (g ζ - g w) ^ 2 - 1 / (ζ - w) ^ 2 -
        preSchwarzian g ζ / (ζ - w) := by
      filter_upwards [hEo.mem_nhds hy, isOpen_ne.mem_nhds hyζ] with w hw hwζ
      exact hkre ζ hζ w hw hwζ
    rw [hev.deriv_eq, (s3fe_dQ hEo hgd hgi hζ hy hyζ (preSchwarzian g ζ)).deriv, hD]
  -- (P2) the `k̃` kernel through `K₁(G)` and its `x`-derivative
  have hKt : ∀ x ∈ unitDiscExterior, ∀ ω ∈ unitDiscExterior, x ≠ ω →
      -(π : ℂ) * kerK1 G x ω = deriv g x * deriv g ω / (g x - g ω) ^ 2 - 1 / (x - ω) ^ 2 := by
    intro x hx ω hω hxω
    rw [kerK1_of_ne G hxω, ← hgG x hx, ← hgG ω hω, hGg hx, hGg hω]
    field_simp
    ring
  have hP2 : ∀ ω ∈ unitDiscExterior, ∀ u ∈ unitDiscExterior, u ≠ ω →
      deriv (fun x => -(π : ℂ) * kerK1 G x ω) u = Dk u ω := by
    intro ω hω u hu huω
    have hev : (fun x => -(π : ℂ) * kerK1 G x ω) =ᶠ[𝓝 u]
        fun v => deriv g v * deriv g ω / (g v - g ω) ^ 2 - 1 / (v - ω) ^ 2 := by
      filter_upwards [hEo.mem_nhds hu, isOpen_ne.mem_nhds huω] with v hv hvω
      exact hKt v hv ω hω hvω
    rw [hev.deriv_eq, (s3fe_dk hEo hgd hgi hu hω huω).deriv, hDk]
  -- (P3) the kernel identity
  have hP3 : ∀ u ∈ unitDiscExterior, ∀ ω ∈ unitDiscExterior, u ≠ ω →
      Dk u ω - preSchwarzian g u * (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2) = -D u ω := by
    intro u hu ω hω huω
    rw [hDk, hD]
    exact s3fe_alg (sub_ne_zero.mpr fun h => huω (hgi hu hω h)) (sub_ne_zero.mpr huω) (hgne u hu)
  have hEae : ∀ᵐ ζ ∂μE, ζ ∈ unitDiscExterior := ae_restrict_mem hEm
  have hae : ∀ y : ℂ, ∀ᵐ ζ ∂μE, ζ ≠ y := fun y => ae_restrict_of_ae ((volume : Measure ℂ).ae_ne y)
  have hw3 : Integrable (fun ζ : ℂ => (‖ζ‖ ^ 3)⁻¹) μE := d2l_powint (by norm_num : 3 ≤ 3)
  have hcAm : Measurable fun ω => conj (preSchwarzian g ω) := Complex.continuous_conj.measurable.comp hAm
  have hAi : Integrable (fun ω => ‖preSchwarzian g ω‖) μE := by
    refine Integrable.mono' (Integrable.const_mul hw3 CA) hAm.aestronglyMeasurable.norm ?_
    filter_upwards [hEae] with ω hω
    rw [norm_norm]; exact hA ω hω
  obtain ⟨Mf, C4, hMf0, hC40, hDb⟩ := s3fe_Dbd hpair hρ hGd hGi hGd' hGg hRm hRb hA
  have hS1 : ∀ z ∈ unitDiscExterior, Integrable (fun ζ => R ζ * D ζ z) μE ∧
      dz (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2)) z =
        (∫ ζ in unitDiscExterior, R ζ * D ζ z) +
          dz (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * preSchwarzian g ζ / (ζ - y)) z := by
    intro z hz
    simpa only [hD] using s3fe_S1 hpair hρ hGd hGi hGd' hGg hRm hRb hA hC1 z hz
  have hS2 : ∀ u ∈ unitDiscExterior,
      Integrable (fun ω => conj (preSchwarzian g ω) * (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2))
        μE ∧
      Integrable (fun ω => conj (preSchwarzian g ω) * Dk u ω) μE ∧
      HasDerivAt (fun x : ℂ => (1 / π : ℂ) * ∫ ω in unitDiscExterior,
          conj (preSchwarzian g ω) * (deriv g x * deriv g ω / (g x - g ω) ^ 2 - 1 / (x - ω) ^ 2))
        ((1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian g ω) * Dk u ω) u := by
    intro u hu
    simpa only [hDk] using s3fe_S2 hpair hρ hGd hGi hGd' hGg hRm hRb hA u hu
  -- the weight `(1 + |u - ω|)⁻³`
  have hw : Integrable (fun u : ℂ => ((1 + ‖u‖) ^ 3)⁻¹) volume := by
    have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3)
      (by rw [Complex.finrank_real_complex]; norm_num)
    refine h.congr (Eventually.of_forall fun u => ?_)
    show (1 + ‖u‖) ^ (-(3 : ℝ)) = ((1 + ‖u‖) ^ 3)⁻¹
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  set I3 := ∫ u : ℂ, ((1 + ‖u‖) ^ 3)⁻¹ with hI3
  set IA := ∫ u in unitDiscExterior, ‖preSchwarzian g u‖ with hIA
  set Kc := Rb' * (Mf * I3 + C4 * IA) with hKc
  -- the Fubini integrand `F(ω, u) = R(u) conj 𝒜(ω) D(u, ω)`
  set F : ℂ × ℂ → ℂ := fun p => R p.2 * (conj (preSchwarzian g p.1) * D p.2 p.1) with hF
  have hFm : AEStronglyMeasurable F (μE.prod μE) := by
    rw [hF, hD]
    refine (hRm.aemeasurable.comp_snd.mul ((hcAm.comp measurable_fst).aemeasurable.mul ?_)).aestronglyMeasurable
    exact ((((aemeasurable_const.mul ((hg1.comp measurable_snd).aemeasurable.pow_const 2)).mul
      (hg1.comp measurable_fst).aemeasurable).div ((hgm.comp_snd.sub hgm.comp_fst).pow_const 3)).sub
      (aemeasurable_const.div ((measurable_snd.sub measurable_fst).aemeasurable.pow_const 3))).sub
      ((hAm.comp measurable_snd).aemeasurable.div ((measurable_snd.sub measurable_fst).aemeasurable.pow_const 2))
  have hFrow : ∀ ω ∈ unitDiscExterior, Integrable (fun u => F (ω, u)) μE := by
    intro ω hω
    refine (Integrable.const_mul (hS1 ω hω).1 (conj (preSchwarzian g ω))).congr
      (Eventually.of_forall fun u => ?_)
    simp only [hF]
    ring
  have hFint : ∀ ω ∈ unitDiscExterior, ∫ u, ‖F (ω, u)‖ ∂μE ≤ ‖preSchwarzian g ω‖ * Kc := by
    intro ω hω
    have hwi : Integrable (fun u => ((1 + ‖u - ω‖) ^ 3)⁻¹) μE := (hw.comp_sub_right ω).integrableOn
    have hbi : Integrable (fun u => Rb' * (Mf * ((1 + ‖u - ω‖) ^ 3)⁻¹ + C4 * ‖preSchwarzian g u‖)) μE :=
      Integrable.const_mul ((Integrable.const_mul hwi Mf).add (Integrable.const_mul hAi C4)) Rb'
    have hbd : Integrable (fun u => ‖preSchwarzian g ω‖ *
        (Rb' * (Mf * ((1 + ‖u - ω‖) ^ 3)⁻¹ + C4 * ‖preSchwarzian g u‖))) μE := Integrable.const_mul hbi _
    have hle : ∫ u, ((1 + ‖u - ω‖) ^ 3)⁻¹ ∂μE ≤ I3 := by
      rw [hI3, ← integral_sub_right_eq_self (fun u : ℂ => ((1 + ‖u‖) ^ 3)⁻¹) ω]
      exact setIntegral_le_integral (hw.comp_sub_right ω) (Eventually.of_forall fun _ => by positivity)
    calc ∫ u, ‖F (ω, u)‖ ∂μE ≤ ∫ u, ‖preSchwarzian g ω‖ *
          (Rb' * (Mf * ((1 + ‖u - ω‖) ^ 3)⁻¹ + C4 * ‖preSchwarzian g u‖)) ∂μE := by
          refine integral_mono_ae (hFrow ω hω).norm hbd ?_
          filter_upwards [hR, hEae, hae ω] with u hRu hu huω
          have hDu : ‖D u ω‖ ≤ Mf * ((1 + ‖u - ω‖) ^ 3)⁻¹ + C4 * ‖preSchwarzian g u‖ := by
            simp only [hD]; exact hDb u hu ω hω huω
          simp only [hF]
          rw [norm_mul, norm_mul, RCLike.norm_conj]
          calc ‖R u‖ * (‖preSchwarzian g ω‖ * ‖D u ω‖) = ‖preSchwarzian g ω‖ * (‖R u‖ * ‖D u ω‖) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hRu hDu (norm_nonneg _) hRb0) (norm_nonneg _)
      _ = ‖preSchwarzian g ω‖ * (Rb' * (Mf * ∫ u, ((1 + ‖u - ω‖) ^ 3)⁻¹ ∂μE + C4 * IA)) := by
          rw [integral_const_mul, integral_const_mul, integral_add (Integrable.const_mul hwi Mf)
            (Integrable.const_mul hAi C4), integral_const_mul, integral_const_mul]
      _ ≤ ‖preSchwarzian g ω‖ * Kc := by
          rw [hKc]
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hRb0) (norm_nonneg _)
          exact add_le_add (mul_le_mul_of_nonneg_left hle hMf0) le_rfl
  have hFi : Integrable F (μE.prod μE) := by
    refine (integrable_prod_iff hFm).mpr ⟨?_, ?_⟩
    · filter_upwards [hEae] with ω hω using hFrow ω hω
    · refine Integrable.mono' (hAi.mul_const Kc) hFm.norm.integral_prod_right' ?_
      filter_upwards [hEae] with ω hω
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hFint ω hω
  -- rows and columns
  have hrow : ∀ ω ∈ unitDiscExterior, ∫ u, F (ω, u) ∂μE =
      conj (preSchwarzian g ω) * ∫ u in unitDiscExterior, R u * D u ω := by
    intro ω hω
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hF]
    ring
  have hI1 : Integrable (fun ω => conj (preSchwarzian g ω) * ∫ u in unitDiscExterior, R u * D u ω) μE :=
    hFi.integral_prod_left.congr (by filter_upwards [hEae] with ω hω using hrow ω hω)
  have hcol : ∀ u ∈ unitDiscExterior, R u * (deriv (fun x : ℂ => (1 / π : ℂ) * ∫ ω in unitDiscExterior,
        conj (preSchwarzian g ω) * (deriv g x * deriv g ω / (g x - g ω) ^ 2 - 1 / (x - ω) ^ 2)) u -
        preSchwarzian g u * ((1 / π : ℂ) * ∫ ω in unitDiscExterior,
          conj (preSchwarzian g ω) * (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2))) =
      -(1 / π : ℂ) * ∫ ω, F (ω, u) ∂μE := by
    intro u hu
    obtain ⟨i1, i2, hd⟩ := hS2 u hu
    rw [hd.deriv]
    have e : (∫ ω, conj (preSchwarzian g ω) * Dk u ω ∂μE) - preSchwarzian g u * ∫ ω, conj (preSchwarzian g ω) *
        (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2) ∂μE =
        -∫ ω, conj (preSchwarzian g ω) * D u ω ∂μE := by
      rw [← integral_const_mul, ← integral_sub i2 (Integrable.const_mul i1 _), ← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [hEae, hae u] with ω hω hωu
      have := hP3 u hu ω hω (Ne.symm hωu)
      linear_combination (conj (preSchwarzian g ω)) * this
    have e2 : ∫ ω, F (ω, u) ∂μE = R u * ∫ ω, conj (preSchwarzian g ω) * D u ω ∂μE := by
      rw [← integral_const_mul]
    have e3 : (1 / π : ℂ) * (∫ ω, conj (preSchwarzian g ω) * Dk u ω ∂μE) - preSchwarzian g u *
        ((1 / π : ℂ) * ∫ ω, conj (preSchwarzian g ω) *
          (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2) ∂μE) =
        (1 / π : ℂ) * ((∫ ω, conj (preSchwarzian g ω) * Dk u ω ∂μE) - preSchwarzian g u *
          ∫ ω, conj (preSchwarzian g ω) * (deriv g u * deriv g ω / (g u - g ω) ^ 2 - 1 / (u - ω) ^ 2) ∂μE) := by
      ring
    rw [e3, e, e2]
    ring
  have hdzE : ∀ z ∈ unitDiscExterior, conj (preSchwarzian g z) * (-(1 / π : ℂ) * dz (fun y : ℂ =>
      ∫ ζ in unitDiscExterior, R ζ * (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2)) z) =
      -(1 / π : ℂ) * (conj (preSchwarzian g z) * ∫ u in unitDiscExterior, R u * D u z) +
        -(1 / π : ℂ) * (conj (preSchwarzian g z) *
          dz (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ * preSchwarzian g ζ / (ζ - y)) z) := by
    intro z hz
    rw [(hS1 z hz).2]
    ring
  have hswap : ∫ u, ∫ ω, F (ω, u) ∂μE ∂μE = ∫ ω, ∫ u, F (ω, u) ∂μE ∂μE :=
    (integral_integral_swap (f := fun ω u => F (ω, u)) hFi).symm
  refine ⟨?_, fun u hu => (hS2 u hu).2.2.differentiableAt, ?_, ?_⟩
  · exact IntegrableOn.congr_fun ((Integrable.const_mul hI1 _).add (Integrable.const_mul hCi _))
      (fun z hz => (hdzE z hz).symm) hEm
  · exact IntegrableOn.congr_fun (Integrable.const_mul hFi.integral_prod_right (-(1 / π : ℂ)))
      (fun u hu => (hcol u hu).symm) hEm
  · rw [setIntegral_congr_fun hEm hdzE, integral_add (Integrable.const_mul hI1 _) (Integrable.const_mul hCi _),
      integral_const_mul, integral_const_mul, setIntegral_congr_fun hEm hcol, integral_const_mul, hswap,
      setIntegral_congr_fun hEm hrow]
    ring

/-- `𝔻*`-indicator of an `O(|z|⁻³)` function is in `L²(ℂ)`. -/
theorem s3fb_ind_L2 {F : ℂ → ℂ} {K : ℝ} (hFm : AEStronglyMeasurable F (volume.restrict unitDiscExterior))
    (hb : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖F z‖ ≤ K * (‖z‖ ^ 3)⁻¹) :
    MemLp (unitDiscExterior.indicator F) 2 volume := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [memLp_two_iff_integrable_sq_norm ((aestronglyMeasurable_indicator_iff hEm).2 hFm)]
  have h : (fun z => ‖unitDiscExterior.indicator F z‖ ^ 2) = unitDiscExterior.indicator (fun z => ‖F z‖ ^ 2) := by
    funext z
    by_cases hz : z ∈ unitDiscExterior <;> simp [hz]
  rw [h, integrable_indicator_iff hEm]
  refine ((d2l_powint (k := 6) (by norm_num)).const_mul (K ^ 2)).mono' (hFm.norm.pow 2) ?_
  filter_upwards [hb, ae_restrict_mem hEm] with z hz hzE
  have hz1 : (1 : ℝ) < ‖z‖ := hzE
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖F z‖ ^ 2 ≤ (K * (‖z‖ ^ 3)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    _ = K ^ 2 * (‖z‖ ^ 6)⁻¹ := by rw [mul_pow, inv_pow, ← pow_mul]

/-- **(FB-0)** `∫_{𝔻*} conj A · ∂C = 0` from `∂C = -π H(1_{𝔻*} W)` a.e., the pairing symmetry of `hilbertH`, and
`H(1_{𝔻*} conj A) = 0` a.e. on `𝔻*`. -/
theorem s3fb_zero {A W C : ℂ → ℂ} (hA2 : MemLp (unitDiscExterior.indicator (fun z => conj (A z))) 2 volume)
    (hW2 : MemLp (unitDiscExterior.indicator W) 2 volume)
    (hdz : ∀ᵐ y ∂(volume.restrict unitDiscExterior), dz C y = -(π : ℂ) * hilbertH (unitDiscExterior.indicator W) y)
    (hv : ∀ᵐ u ∂(volume.restrict unitDiscExterior),
      hilbertH (unitDiscExterior.indicator (fun z => conj (A z))) u = 0) :
    ∫ z in unitDiscExterior, conj (A z) * dz C z = 0 := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have e1 : (∫ z in unitDiscExterior, conj (A z) * dz C z) =
      ∫ z in unitDiscExterior, -(π : ℂ) * (conj (A z) * hilbertH (unitDiscExterior.indicator W) z) := by
    refine integral_congr_ae ?_
    filter_upwards [hdz] with z hz
    rw [hz]
    ring
  have e2 : (∫ z in unitDiscExterior, conj (A z) * hilbertH (unitDiscExterior.indicator W) z) =
      ∫ z, hilbertH (unitDiscExterior.indicator W) z * unitDiscExterior.indicator (fun z => conj (A z)) z := by
    rw [← integral_indicator hEm]
    congr 1
    funext z
    by_cases hz : z ∈ unitDiscExterior <;> simp [hz, mul_comm]
  have e3 : (∫ z, unitDiscExterior.indicator W z * hilbertH (unitDiscExterior.indicator (fun z => conj (A z))) z) =
      ∫ z in unitDiscExterior, W z * hilbertH (unitDiscExterior.indicator (fun z => conj (A z))) z := by
    rw [← integral_indicator hEm]
    congr 1
    funext z
    by_cases hz : z ∈ unitDiscExterior <;> simp [hz]
  rw [e1, integral_const_mul, e2, hilbertH_pairing_symm_L2 hW2 hA2, e3]
  have e4 : (∫ z in unitDiscExterior, W z * hilbertH (unitDiscExterior.indicator (fun z => conj (A z))) z) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hv] with z hz
    simp [hz]
  rw [e4, mul_zero]

/-- **(F-FUB)** `I₁ + I₃ = ∫_{𝔻*} R (h' - 𝒜 h)` (W-FUB), with
`h(u) = (1/π)∫_𝔻 conj 𝒜(f) g'(u) f'/(g(u) - f)² + (1/π)∫_{𝔻*} conj 𝒜(g)(ω) (g'(u)g'(ω)/(g(u) - g(ω))² - 1/(u - ω)²)`
(the PV part `∫ conj 𝒜(g)/(u - ω)²` vanishes: `conj 𝒜(g) = ∂̄ conj B`, `B' = 𝒜(g)`); all integrands integrable. -/
theorem s3f_fub {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    IntegrableOn (fun z => conj (preSchwarzian (fsans (beltramiMul a κ)) z) * (deriv (fsans (beltramiMul a κ)) z *
        (-(2 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - fsans (beltramiMul a κ) z) ^ 3))) unitDisc ∧
      IntegrableOn (fun z => conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
        (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z)) unitDiscExterior ∧
      IntegrableOn (fun u => RnmFun (toLinf m) a u * (deriv (fun x : ℂ => (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) x * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) x - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2))) u - preSchwarzian (gsans (beltramiMul a κ)) u * (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) u * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) u * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (u - ω) ^ 2)))) unitDiscExterior ∧
      (∫ z in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) z) * (deriv (fsans (beltramiMul a κ)) z *
        (-(2 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - fsans (beltramiMul a κ) z) ^ 3))) +
        (∫ z in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z)) =
        ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * (deriv (fun x : ℂ => (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) x * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) x - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2))) u - preSchwarzian (gsans (beltramiMul a κ)) u * (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) u * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) u * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (u - ω) ^ 2))) := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.2 (has.trans delta0_bounds.2)
  have hμ : beltramiMul a (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨r, hr, ρ, hρ, Rf, hRf, FF, GG, HH, -, -, -, -, -, -, -, ht⟩ := s3g_D_ext hκ hκD ha has haL haD hm hmD
  obtain ⟨⟨hFd, -, hFd', hFf⟩, ⟨hGd, hGi, hGd', hGg⟩, -⟩ := ht 0 (mem_ball_self hr)
  simp only [zero_smul, add_zero] at hFf hGg
  obtain ⟨hRm, hRb⟩ := d2l_R_data has m
  have hRL : ∫⁻ u in unitDiscExterior, ‖RnmFun (toLinf m) a u‖ₑ ^ 2 * ENNReal.ofReal (rho u) < ∞ := by
    have h1 := WPCV.x5_lintegral_lt_top (WPCV.x5_Rnm_L2 hm haB)
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr_ae ?_)) h1
    filter_upwards [bc_Rnm_ae haB (toLinf m)] with u hu
    rw [enorm_eq_nnnorm, hu]
    rfl
  obtain ⟨hN1, hRK, hFub, hder⟩ := s3fb_disc hpair hρ hGd hGi hGd' hGg hRf hFd hFd' hFf hRm hRb hRL
  obtain ⟨hAd, CA, -, hCA, -, hA, -⟩ := d2l_A_bounds hκ hκD ha has haL haD
  obtain ⟨hC1, hCdz⟩ := s3fc_cauchy_dz hκ hκD ha has haL haD hm hmD
  -- `L²` data
  have hAc : ContinuousOn (preSchwarzian (gsans (beltramiMul a κ))) unitDiscExterior := hAd.continuousOn
  have hAm : AEStronglyMeasurable (fun z => conj (preSchwarzian (gsans (beltramiMul a κ)) z)) (volume.restrict unitDiscExterior) :=
    (Complex.continuous_conj.comp_continuousOn hAc).aestronglyMeasurable hEm
  have hA2 : MemLp (unitDiscExterior.indicator (fun z => conj (preSchwarzian (gsans (beltramiMul a κ)) z))) 2 volume :=
    s3fb_ind_L2 hAm ((ae_restrict_iff' hEm).2 (Filter.Eventually.of_forall fun z hz => by
      rw [Complex.norm_conj]; exact hA z hz))
  have hW2 : MemLp (unitDiscExterior.indicator (fun ζ => RnmFun (toLinf m) a ζ * preSchwarzian (gsans (beltramiMul a κ)) ζ)) 2 volume := by
    refine s3fb_ind_L2 (K := (1 / (1 - ‖a‖ ^ 2)) * ‖toLinf m‖ * CA) (hRm.mul (hAc.aestronglyMeasurable hEm)) ?_
    filter_upwards [hRb, ae_restrict_mem hEm] with z hz hzE
    rw [norm_mul, mul_assoc]
    exact mul_le_mul hz (hA z hzE) (norm_nonneg _) ((norm_nonneg _).trans hz)
  have hH2 := (hilbertH_memLp_two hW2).1
  have hCi : IntegrableOn (fun z => conj (preSchwarzian (gsans (beltramiMul a κ)) z) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * preSchwarzian (gsans (beltramiMul a κ)) ζ / (ζ - y)) z) unitDiscExterior := by
    have hI : Integrable (fun z => unitDiscExterior.indicator (fun z => conj (preSchwarzian (gsans (beltramiMul a κ)) z)) z *
        hilbertH (unitDiscExterior.indicator (fun ζ => RnmFun (toLinf m) a ζ * preSchwarzian (gsans (beltramiMul a κ)) ζ)) z) volume := hA2.integrable_mul hH2
    refine ((hI.integrableOn (s := unitDiscExterior)).const_mul (-(π : ℂ))).congr ?_
    filter_upwards [hCdz, ae_restrict_mem hEm] with z hz hzE
    rw [hz, Set.indicator_of_mem hzE]
    ring
  -- the vanishing (H-VANISH) with `𝒜(G)`
  have hGo : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hPG : DifferentiableOn ℂ (preSchwarzian (GG 0)) {z : ℂ | ρ < ‖z‖} :=
    ((hGd.deriv hGo).deriv hGo).div (hGd.deriv hGo) hGd'
  have hAeq : ∀ z ∈ unitDiscExterior, preSchwarzian (GG 0) z = preSchwarzian (gsans (beltramiMul a κ)) z := by
    intro z hz
    have h0 : GG 0 =ᶠ[𝓝 z] gsans (beltramiMul a κ) := by
      filter_upwards [hE.mem_nhds hz] with y hy using hGg hy
    have h1 : deriv (GG 0) =ᶠ[𝓝 z] deriv (gsans (beltramiMul a κ)) := by
      filter_upwards [hE.mem_nhds hz] with y hy
      exact (by filter_upwards [hE.mem_nhds hy] with x hx using hGg hx : GG 0 =ᶠ[𝓝 y] gsans (beltramiMul a κ)).deriv_eq
    show deriv (deriv (GG 0)) z / deriv (GG 0) z = deriv (deriv (gsans (beltramiMul a κ))) z / deriv (gsans (beltramiMul a κ)) z
    rw [h1.deriv_eq, h0.deriv_eq]
  have hv := s3f_hvanish hρ hPG (C := CA) (fun z hz => by rw [hAeq z hz]; exact hA z hz)
  have hind : unitDiscExterior.indicator (fun z => conj (preSchwarzian (GG 0) z)) =
      unitDiscExterior.indicator (fun z => conj (preSchwarzian (gsans (beltramiMul a κ)) z)) :=
    Set.indicator_congr fun z hz => by rw [hAeq z hz]
  rw [hind] at hv
  have hzero := s3fb_zero hA2 hW2 hCdz hv
  -- the exterior part
  obtain ⟨hN2, hh2d, hIH2, hE2⟩ := s3fe_ext hpair hρ hGd hGi hGd' hGg hRm hRb hA hC1 hCi
  have hpt : ∀ u ∈ unitDiscExterior,
      RnmFun (toLinf m) a u * (deriv (fun x : ℂ => ((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) x * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) x - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2)) u - preSchwarzian (gsans (beltramiMul a κ)) u * (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) u * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) u * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (u - ω) ^ 2))) =
        RnmFun (toLinf m) a u * (-(2 / π : ℂ) * deriv (gsans (beltramiMul a κ)) u ^ 2 * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) w) ^ 3) + RnmFun (toLinf m) a u * (deriv (fun x : ℂ => (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2)) u - preSchwarzian (gsans (beltramiMul a κ)) u * ((1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) u * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (u - ω) ^ 2))) := by
    intro u hu
    have hd : HasDerivAt (fun x : ℂ => ((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) x * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) x - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2))
        (deriv (fun x : ℂ => (1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) x * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) x - fsans (beltramiMul a κ) w) ^ 2)) u + deriv (fun x : ℂ => (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2)) u) u :=
      (hder u hu).1.hasDerivAt.add (hh2d u hu).hasDerivAt
    rw [hd.deriv]
    linear_combination (RnmFun (toLinf m) a u) * (hder u hu).2
  refine ⟨hN1, hN2, ?_, ?_⟩
  · refine (hRK.add hIH2).congr ?_
    filter_upwards [ae_restrict_mem hEm] with u hu
    exact (hpt u hu).symm
  · rw [hFub, hE2, hzero, mul_zero, sub_zero, ← integral_add hRK hIH2]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hEm] with u hu
    exact (hpt u hu).symm

/-- **(D on `D`)** TT's computation of `∂_t S₁` (TT:4780–4960, with `lemma_3_6`), as the old `s35_formula` with the
`D`-hypotheses added (all integrals and Fubini rearrangements are then justified by the boundary regularity of
`s3d_g_dom`'s route). Sub-interface (D1/D1₀/D3 by 下属4, D2/D-IDENT/W-FUB by 下属6) to follow. -/
theorem s3d_formula {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ))
    (hA : ∀ z ∈ unitDisc,
      DifferentiableAt ℝ (fun t : ℂ => preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z) 0)
    (hB : ∀ z ∈ unitDiscExterior,
      DifferentiableAt ℝ (fun t : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) 0)
    (hA1 : MemLp (fun z => dz (fun t : ℂ => preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z) 0) 2
      (volume.restrict unitDisc))
    (hA2 : MemLp (fun z => dzbar (fun t : ℂ => preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z) 0) 2
      (volume.restrict unitDisc))
    (hB1 : MemLp (fun z => dz (fun t : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) 0) 2
      (volume.restrict unitDiscExterior))
    (hB2 : MemLp (fun z => dzbar (fun t : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) 0) 2
      (volume.restrict unitDiscExterior))
    (hC : DifferentiableAt ℝ (fun t : ℂ => derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ))) 0) :
    (∫ z in unitDisc, (preSchwarzian (fsans (beltramiMul a κ)) z *
        conj (dzbar (fun s : ℂ => preSchwarzian (fsans (beltramiMul (a + s • toLinf m) κ)) z) 0) +
      conj (preSchwarzian (fsans (beltramiMul a κ)) z) *
        dz (fun s : ℂ => preSchwarzian (fsans (beltramiMul (a + s • toLinf m) κ)) z) 0)) +
    (∫ z in unitDiscExterior, (preSchwarzian (gsans (beltramiMul a κ)) z *
        conj (dzbar (fun s : ℂ => preSchwarzian (gsans (beltramiMul (a + s • toLinf m) κ)) z) 0) +
      conj (preSchwarzian (gsans (beltramiMul a κ)) z) *
        dz (fun s : ℂ => preSchwarzian (gsans (beltramiMul (a + s • toLinf m) κ)) z) 0)) -
    4 * (π : ℂ) * dz (fun t : ℂ => ((Real.log ‖derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ))‖ : ℝ) : ℂ)) 0 =
      2 * ∫ z in unitDiscExterior, schwarzianHol (gsans (beltramiMul a κ)) z * RnmFun (toLinf m) a z := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hd := delta0_bounds
  have ha1 : ‖a‖ < 1 := has.trans hd.2
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.2 ha1
  have hμ : beltramiMul a (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨φ, bb, -, -, -, -, hbb0, hbb, -⟩ := g1_inverted_exterior hpair
  have hb : derivAtInfty (gsans (beltramiMul a κ)) ≠ 0 := by rw [hbb]; exact hbb0
  obtain ⟨r, hr, ρ, hρ, R0, hR0, FF, GG, HH, -, -, -, -, -, -, -, ht⟩ := s3g_D_ext hκ hκD ha has haL haD hm hmD
  obtain ⟨-, ⟨hGd, hGi, hGd', hGg⟩, -⟩ := ht 0 (mem_ball_self hr)
  simp only [zero_smul, add_zero] at hGg
  obtain ⟨hgd, hg'd, hgi, -, hg'⟩ := d2e_basic hρ hGd hGi hGd' hGg
  have hg0 : ∀ u ∈ unitDiscExterior, gsans (beltramiMul a κ) u ≠ 0 := fun u hu h => by
    have := d2e_koebe hpair hu
    rw [h, norm_zero] at this
    norm_num at this
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  -- the stubs
  have hD1 := s3d_D1 (hκ := hκ) (hκD := hκD) (ha := ha) (has := has) (haL := haL) (haD := haD) (hm := hm) (hmD := hmD)
  have hD2 := (s3d_D2 (hκ := hκ) (hκD := hκD) (ha := ha) (has := has) (haL := haL) (haD := haD) (hm := hm) (hmD := hmD)).2
  have hD3 := (s3d_D3 (hκ := hκ) (hκD := hκD) (ha := ha) (has := has) (haL := haL) (haD := haD) (hm := hm) (hmD := hmD)).2
  obtain ⟨hJf, hJg, hJ⟩ := s3f_pole (hκ := hκ) (hκD := hκD) (ha := ha) (has := has) (haL := haL) (haD := haD)
  obtain ⟨hI2i, hI2⟩ := s3f_I2 (hκ := hκ) (hκD := hκD) (ha := ha) (has := has) (haL := haL) (haD := haD) (hm := hm) (hmD := hmD)
  obtain ⟨hN3i, hI4i, hI4⟩ := s3f_I4 (hκ := hκ) (hκD := hκD) (ha := ha) (has := has) (haL := haL) (haD := haD) (hm := hm) (hmD := hmD)
  obtain ⟨hN1i, hN2i, hIHi, hIH⟩ := s3f_fub (hκ := hκ) (hκD := hκD) (ha := ha) (has := has) (haL := haL) (haD := haD) (hm := hm) (hmD := hmD)
  have hH := s3f_h (hκ := hκ) (hκD := hκD) (ha := ha) (has := has) (haL := haL) (haD := haD)
  have h0 : (fun t : ℂ => fun z : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) 0 =
      preSchwarzian (gsans (beltramiMul a κ)) := by
    funext z
    simp only [zero_smul, add_zero]
  obtain ⟨-, hdzg⟩ := s3d_l2sq_dom hEm h0 (s3d_g_dom_proof hκ hκD ha has haL haD hm hmD)
  -- `I_f`
  have hJfc : IntegrableOn (fun z => conj (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z)) unitDisc :=
    (LinearIsometryEquiv.integrable_comp_iff conjLIE).2 hJf
  have hJgc : IntegrableOn (fun z => conj (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ))))) unitDiscExterior :=
    (LinearIsometryEquiv.integrable_comp_iff conjLIE).2 hJg
  have hIf0 : (∫ z in unitDisc, (preSchwarzian (fsans (beltramiMul a κ)) z * conj (dzbar (fun s : ℂ => preSchwarzian (fsans (beltramiMul (a + s • toLinf m) κ)) z) 0) + conj (preSchwarzian (fsans (beltramiMul a κ)) z) * dz (fun s : ℂ => preSchwarzian (fsans (beltramiMul (a + s • toLinf m) κ)) z) 0)) = ∫ z in unitDisc, (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * (deriv (fsans (beltramiMul a κ)) z * (-(2 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - fsans (beltramiMul a κ) z) ^ 3)) + 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z) + conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * conj (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hDm] with z hz
    obtain ⟨-, -, e1, e2⟩ := hD1 z hz
    rw [e1, e2]
    simp only [map_mul, map_div₀, Complex.conj_conj]
    ring
  have hIf1 : (∫ z in unitDisc, (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * (deriv (fsans (beltramiMul a κ)) z * (-(2 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - fsans (beltramiMul a κ) z) ^ 3)) + 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z) + conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * conj (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z))) =
      (∫ z in unitDisc, (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * (deriv (fsans (beltramiMul a κ)) z * (-(2 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - fsans (beltramiMul a κ) z) ^ 3)) + 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z))) + ∫ z in unitDisc, conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * conj (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z) :=
    integral_add (hN1i.add (hJf.const_mul _)) (hJfc.const_mul _)
  have hIf2 : (∫ z in unitDisc, (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * (deriv (fsans (beltramiMul a κ)) z * (-(2 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - fsans (beltramiMul a κ) z) ^ 3)) + 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z))) =
      (∫ z in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) z) * (deriv (fsans (beltramiMul a κ)) z * (-(2 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - fsans (beltramiMul a κ) z) ^ 3))) + ∫ z in unitDisc, 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z) :=
    integral_add hN1i (hJf.const_mul _)
  have hIf3 : (∫ z in unitDisc, 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z)) = 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * ∫ z in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z :=
    integral_const_mul _ _
  have hIf4 : (∫ z in unitDisc, conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * conj (conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z)) =
      conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * conj (∫ z in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z) := by
    rw [← integral_conj]
    exact integral_const_mul _ _
  -- `I_g`
  have hIg : (∫ z in unitDiscExterior, (preSchwarzian (gsans (beltramiMul a κ)) z * conj (dzbar (fun s : ℂ => preSchwarzian (gsans (beltramiMul (a + s • toLinf m) κ)) z) 0) + conj (preSchwarzian (gsans (beltramiMul a κ)) z) * dz (fun s : ℂ => preSchwarzian (gsans (beltramiMul (a + s • toLinf m) κ)) z) 0)) = ∫ z in unitDiscExterior, (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z + 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) * (deriv (gsans (beltramiMul a κ)) z / derivAtInfty (gsans (beltramiMul a κ)) - 1)) + preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) + 2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) * (deriv (gsans (beltramiMul a κ)) z / derivAtInfty (gsans (beltramiMul a κ)) - 1))) := hdzg.symm.trans hD2
  have hT0 : (∫ z in unitDiscExterior, (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z + 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) * (deriv (gsans (beltramiMul a κ)) z / derivAtInfty (gsans (beltramiMul a κ)) - 1)) + preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) + 2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) * (deriv (gsans (beltramiMul a κ)) z / derivAtInfty (gsans (beltramiMul a κ)) - 1)))) = ∫ z in unitDiscExterior, (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z) + preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) + 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ)))) +
      conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * conj (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ))))) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hEm] with z hz
    rw [show deriv (gsans (beltramiMul a κ)) z / derivAtInfty (gsans (beltramiMul a κ)) - 1 = (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ))) / derivAtInfty (gsans (beltramiMul a κ)) by field_simp]
    simp only [map_mul, map_add, map_sub, map_div₀, Complex.conj_conj]
    ring
  have hT1 : (∫ z in unitDiscExterior, (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z) + preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) + 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ)))) +
      conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * conj (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ)))))) = (∫ z in unitDiscExterior, (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z) + preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) + 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ)))))) +
        ∫ z in unitDiscExterior, conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * conj (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ)))) :=
    integral_add ((hN2i.add hN3i).add (hJg.const_mul _)) (hJgc.const_mul _)
  have hT2 : (∫ z in unitDiscExterior, (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z) + preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) + 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ)))))) =
      (∫ z in unitDiscExterior, (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z) + preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3))) + ∫ z in unitDiscExterior, 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ)))) :=
    integral_add (hN2i.add hN3i) (hJg.const_mul _)
  have hT3 : (∫ z in unitDiscExterior, (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z) + preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3))) =
      (∫ z in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z)) + ∫ z in unitDiscExterior, preSchwarzian (gsans (beltramiMul a κ)) z * conj ((2 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) := integral_add hN2i hN3i
  have hT4 : (∫ z in unitDiscExterior, 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ))))) = 2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * ∫ z in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ))) :=
    integral_const_mul _ _
  have hT5 : (∫ z in unitDiscExterior, conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * conj (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ))))) =
      conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * conj (∫ z in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ)))) := by
    rw [← integral_conj]
    exact integral_const_mul _ _
  -- the target as `IH + I4 - 2 I2`
  have hS1 : (∫ u in unitDiscExterior, (RnmFun (toLinf m) a u * (deriv (fun x : ℂ => (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) x * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) x - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2))) u - preSchwarzian (gsans (beltramiMul a κ)) u * (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) u * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) u * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (u - ω) ^ 2))) + RnmFun (toLinf m) a u * (deriv (preSchwarzian (gsans (beltramiMul a κ))) u + 2 * preSchwarzian (gsans (beltramiMul a κ)) u / u) - 2 * (RnmFun (toLinf m) a u * (deriv (gsans (beltramiMul a κ)) u ^ 2 / gsans (beltramiMul a κ) u ^ 2 - 1 / u ^ 2)))) =
      (∫ u in unitDiscExterior, (RnmFun (toLinf m) a u * (deriv (fun x : ℂ => (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) x * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) x - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2))) u - preSchwarzian (gsans (beltramiMul a κ)) u * (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) u * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) u * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (u - ω) ^ 2))) + RnmFun (toLinf m) a u * (deriv (preSchwarzian (gsans (beltramiMul a κ))) u + 2 * preSchwarzian (gsans (beltramiMul a κ)) u / u))) - ∫ u in unitDiscExterior, 2 * (RnmFun (toLinf m) a u * (deriv (gsans (beltramiMul a κ)) u ^ 2 / gsans (beltramiMul a κ) u ^ 2 - 1 / u ^ 2)) :=
    integral_sub (hIHi.add hI4i) (hI2i.const_mul _)
  have hS2 : (∫ u in unitDiscExterior, (RnmFun (toLinf m) a u * (deriv (fun x : ℂ => (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) x * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) x - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2))) u - preSchwarzian (gsans (beltramiMul a κ)) u * (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) u * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) u * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (u - ω) ^ 2))) + RnmFun (toLinf m) a u * (deriv (preSchwarzian (gsans (beltramiMul a κ))) u + 2 * preSchwarzian (gsans (beltramiMul a κ)) u / u))) =
      (∫ u in unitDiscExterior, RnmFun (toLinf m) a u * (deriv (fun x : ℂ => (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) x * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) x - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2))) u - preSchwarzian (gsans (beltramiMul a κ)) u * (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) u * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) u * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (u - ω) ^ 2)))) + ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * (deriv (preSchwarzian (gsans (beltramiMul a κ))) u + 2 * preSchwarzian (gsans (beltramiMul a κ)) u / u) := integral_add hIHi hI4i
  have hS3 : (∫ u in unitDiscExterior, 2 * (RnmFun (toLinf m) a u * (deriv (gsans (beltramiMul a κ)) u ^ 2 / gsans (beltramiMul a κ) u ^ 2 - 1 / u ^ 2))) = 2 * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * (deriv (gsans (beltramiMul a κ)) u ^ 2 / gsans (beltramiMul a κ) u ^ 2 - 1 / u ^ 2) := integral_const_mul _ _
  have hS4 : (∫ z in unitDiscExterior, 2 * (schwarzianHol (gsans (beltramiMul a κ)) z * RnmFun (toLinf m) a z)) =
      2 * ∫ z in unitDiscExterior, schwarzianHol (gsans (beltramiMul a κ)) z * RnmFun (toLinf m) a z := integral_const_mul _ _
  have hS : (∫ z in unitDiscExterior, 2 * (schwarzianHol (gsans (beltramiMul a κ)) z * RnmFun (toLinf m) a z)) =
      ∫ u in unitDiscExterior, (RnmFun (toLinf m) a u * (deriv (fun x : ℂ => (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) x * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) x - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2))) u - preSchwarzian (gsans (beltramiMul a κ)) u * (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) u * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) u * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (u - ω) ^ 2))) + RnmFun (toLinf m) a u * (deriv (preSchwarzian (gsans (beltramiMul a κ))) u + 2 * preSchwarzian (gsans (beltramiMul a κ)) u / u) - 2 * (RnmFun (toLinf m) a u * (deriv (gsans (beltramiMul a κ)) u ^ 2 / gsans (beltramiMul a κ) u ^ 2 - 1 / u ^ 2))) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hEm] with u hu
    have hu0 : u ≠ 0 := fun h => by
      have : (1 : ℝ) < ‖u‖ := hu
      rw [h, norm_zero] at this
      linarith
    have hev : (fun x : ℂ => (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) x * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) x - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2))) =ᶠ[𝓝 u]
        fun x : ℂ => preSchwarzian (gsans (beltramiMul a κ)) x - 2 * (deriv (gsans (beltramiMul a κ)) x / gsans (beltramiMul a κ) x) + 2 / x := by
      filter_upwards [hE.mem_nhds hu] with x hx
      rw [hH x hx]
      ring
    have hgu := hg0 u hu
    have hg'u := hg' u hu
    have hdg : DifferentiableAt ℂ (gsans (beltramiMul a κ)) u := hgd.differentiableAt (hE.mem_nhds hu)
    have hdg' : DifferentiableAt ℂ (deriv (gsans (beltramiMul a κ))) u := hg'd.differentiableAt (hE.mem_nhds hu)
    have hdg'' : DifferentiableAt ℂ (deriv (deriv (gsans (beltramiMul a κ)))) u := (hg'd.deriv hE).differentiableAt (hE.mem_nhds hu)
    have hA : HasDerivAt (preSchwarzian (gsans (beltramiMul a κ))) (deriv (preSchwarzian (gsans (beltramiMul a κ))) u) u := by
      have : DifferentiableAt ℂ (fun x => deriv (deriv (gsans (beltramiMul a κ))) x / deriv (gsans (beltramiMul a κ)) x) u := hdg''.div hdg' hg'u
      exact this.hasDerivAt
    have hP : HasDerivAt (fun x => deriv (gsans (beltramiMul a κ)) x / gsans (beltramiMul a κ) x)
        ((deriv (deriv (gsans (beltramiMul a κ))) u * gsans (beltramiMul a κ) u - deriv (gsans (beltramiMul a κ)) u * deriv (gsans (beltramiMul a κ)) u) / gsans (beltramiMul a κ) u ^ 2) u :=
      hdg'.hasDerivAt.div hdg.hasDerivAt hgu
    have hQ : HasDerivAt (fun x : ℂ => 2 / x) (-(2 : ℂ) / u ^ 2) u := by
      have := (hasDerivAt_inv hu0).const_mul (2 : ℂ)
      simpa [div_eq_mul_inv, neg_div] using this
    have hD : deriv (fun x : ℂ => (((1 / π : ℂ) * ∫ w in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) w) * (deriv (gsans (beltramiMul a κ)) x * deriv (fsans (beltramiMul a κ)) w / (gsans (beltramiMul a κ) x - fsans (beltramiMul a κ) w) ^ 2)) + (1 / π : ℂ) * ∫ ω in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) ω) * (deriv (gsans (beltramiMul a κ)) x * deriv (gsans (beltramiMul a κ)) ω / (gsans (beltramiMul a κ) x - gsans (beltramiMul a κ) ω) ^ 2 - 1 / (x - ω) ^ 2))) u =
        deriv (preSchwarzian (gsans (beltramiMul a κ))) u - 2 * ((deriv (deriv (gsans (beltramiMul a κ))) u * gsans (beltramiMul a κ) u - deriv (gsans (beltramiMul a κ)) u * deriv (gsans (beltramiMul a κ)) u) / gsans (beltramiMul a κ) u ^ 2) +
          -(2 : ℂ) / u ^ 2 := by
      rw [hev.deriv_eq]
      have := (hA.sub (hP.const_mul (2 : ℂ))).add hQ
      exact this.deriv
    rw [hD, hH u hu]
    have hAe : preSchwarzian (gsans (beltramiMul a κ)) u = deriv (deriv (gsans (beltramiMul a κ))) u / deriv (gsans (beltramiMul a κ)) u := rfl
    have hSe : schwarzianHol (gsans (beltramiMul a κ)) u = deriv (preSchwarzian (gsans (beltramiMul a κ))) u - (1 / 2) * (preSchwarzian (gsans (beltramiMul a κ)) u) ^ 2 := rfl
    rw [hSe]
    rw [hAe]
    field_simp
    ring
  have hI2' : 2 * (π : ℂ) * ((1 / π : ℂ) * (∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / gsans (beltramiMul a κ) ζ ^ 2 -
      (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) - conj ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (ζ + I) /
        ((ζ + 1) * (ζ + I) * (ζ - 1)))) = 2 * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * (deriv (gsans (beltramiMul a κ)) u ^ 2 / gsans (beltramiMul a κ) u ^ 2 - 1 / u ^ 2) := by
    rw [hI2]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  have hJc : conj (∫ z in unitDisc, conj (preSchwarzian (fsans (beltramiMul a κ)) z) * deriv (fsans (beltramiMul a κ)) z) + conj (∫ z in unitDiscExterior, conj (preSchwarzian (gsans (beltramiMul a κ)) z) * (deriv (gsans (beltramiMul a κ)) z - derivAtInfty (gsans (beltramiMul a κ)))) =
      2 * (π : ℂ) * conj (limUnder (cocompact ℂ) (fun z => gsans (beltramiMul a κ) z - derivAtInfty (gsans (beltramiMul a κ)) * z)) := by
    rw [← map_add, hJ]
    simp only [map_mul, Complex.conj_ofReal, map_ofNat]
  rw [map_sub, map_mul] at hD3
  linear_combination hIf0 + hIf1 + hIf2 + hIf3 + hIf4 + hIg + hT0 + hT1 + hT2 + hT3 + hT4 + hT5 -
    4 * (π : ℂ) * hD3 + hS4 - hS - hS1 - hS2 + hS3 + hIH + hI4 + (2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * hJ +
    conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * hJc - hI2'

end TakhtajanTeo.Ch2
