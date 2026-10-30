import TakhtajanTeo.Ch1.GroupB1
import TakhtajanTeo.Ch1.WeldingCovarianceBridge

/-!
# Group chain: reflection and inverse estimates

Packages the previously verified S5 and S6 proofs from
`collaboration/下属2/S2grp/g_refl.txt` and `f_inv.txt`, without changing their
statements or proof bodies. These are conditional transfer estimates:
`grp25_reflect` assumes the disk estimate, and `grp25_inv` retains its explicit
regularity and forward-estimate premises. They do not close `lemma_2_5`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem grp_dil_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {x : ℂ} (hx : ContDiffAt ℝ 1 (wA μ) x) :
    ‖dzbar (wA μ) x‖ ≤ ‖μ‖ * ‖dz (wA μ) x‖ := by
  by_contra hlt0
  have hlt := not_le.1 hlt0
  have hcf : ContinuousAt (fderiv ℝ (wA μ)) x := (hx.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hc1 : ContinuousAt (dz (wA μ)) x := by
    unfold dz
    exact ((hcf.clm_apply continuousAt_const).sub (continuousAt_const.mul (hcf.clm_apply continuousAt_const))).div_const 2
  have hc2 : ContinuousAt (dzbar (wA μ)) x := by
    unfold dzbar
    exact ((hcf.clm_apply continuousAt_const).add (continuousAt_const.mul (hcf.clm_apply continuousAt_const))).div_const 2
  have hev : ∀ᶠ y in nhds x, ‖μ‖ * ‖dz (wA μ) y‖ < ‖dzbar (wA μ) y‖ :=
    (continuousAt_const.mul hc1.norm).eventually_lt hc2.norm hlt
  obtain ⟨V, hVsub, hVo, hxV⟩ := _root_.mem_nhds_iff.1 hev
  have hae : ∀ᵐ y : ℂ, ‖dzbar (wA μ) y‖ ≤ ‖μ‖ * ‖dz (wA μ) y‖ := by
    filter_upwards [bc_wA_ae hμ, extA_ae_norm_le μ] with y hy hn
    obtain ⟨-, hdz, hcd, -⟩ := hy
    have h1 : ‖complexDilatation (wA μ) y‖ ≤ ‖μ‖ := by rw [hcd]; exact hn
    rw [complexDilatation, norm_div, div_le_iff₀ (norm_pos_iff.2 hdz)] at h1
    exact h1
  have h0 : volume {y : ℂ | ¬ ‖dzbar (wA μ) y‖ ≤ ‖μ‖ * ‖dz (wA μ) y‖} = 0 := ae_iff.1 hae
  have hpos : 0 < volume V := hVo.measure_pos volume ⟨x, hxV⟩
  refine absurd (measure_mono_null (fun y hy => ?_) h0) hpos.ne'
  exact not_le.2 (hVsub hy)

theorem grp_inv_deriv {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {x : ℂ} (hx : ContDiffAt ℝ 1 (wA μ) x)
    (hfin : wAS μ (x : ExtPlane) ≠ extInf) (hdz : dz (wA μ) x ≠ 0) :
    DifferentiableAt ℝ (wA (beltramiInv μ)) (wA μ x) ∧ wA (beltramiInv μ) (wA μ x) = x ∧
      dz (wA (beltramiInv μ)) (wA μ x) = conj (dz (wA μ) x) / (jacobian (wA μ) x : ℂ) := by
  have hμi : beltramiInv μ ∈ LinfStarBall := grp_inv_mem hμ
  have hk1 : ‖μ‖ < 1 := bc_norm_lt_one hμ
  have hfd : DifferentiableAt ℝ (wA μ) x := hx.differentiableAt one_ne_zero
  set u : ℂ := wA μ x with hu
  have hu' : wAS μ (x : ExtPlane) = (u : ExtPlane) := (coe_finPart_of_ne hfin).symm
  have hgu : wAS (beltramiInv μ) (u : ExtPlane) = (x : ExtPlane) := by
    rw [← hu']
    exact congrFun (grp_wAS_inv_right hμ) (x : ExtPlane)
  have hgx : wA (beltramiInv μ) u = x := by
    show finPart (wAS (beltramiInv μ) (u : ExtPlane)) = x
    rw [hgu]
    rfl
  -- the Jacobian
  have hb := grp_dil_bound hμ hx
  have hapos : 0 < ‖dz (wA μ) x‖ := norm_pos_iff.2 hdz
  have hbl : ‖dzbar (wA μ) x‖ < ‖dz (wA μ) x‖ := by
    calc ‖dzbar (wA μ) x‖ ≤ ‖μ‖ * ‖dz (wA μ) x‖ := hb
      _ < 1 * ‖dz (wA μ) x‖ := mul_lt_mul_of_pos_right hk1 hapos
      _ = ‖dz (wA μ) x‖ := one_mul _
  have hJ : 0 < jacobian (wA μ) x := by
    unfold jacobian
    nlinarith [norm_nonneg (dzbar (wA μ) x)]
  -- the derivative is invertible
  have hinj : Function.Injective (fderiv ℝ (wA μ) x).toLinearMap := by
    intro v w hvw
    have h0 : (fderiv ℝ (wA μ) x) (v - w) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 hvw
    rw [fderiv_eq_dz_dzbar hfd] at h0
    have h1 : dz (wA μ) x * (v - w) = -(dzbar (wA μ) x * conj (v - w)) := by linear_combination h0
    have h2 : ‖dz (wA μ) x‖ * ‖v - w‖ ≤ ‖dzbar (wA μ) x‖ * ‖v - w‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_neg, norm_mul, Complex.norm_conj] at this
      exact this.le
    have h3 : ‖v - w‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖v - w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      nlinarith
    exact sub_eq_zero.1 (norm_eq_zero.1 h3)
  let e : ℂ ≃L[ℝ] ℂ := (LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv
  have he : (e : ℂ →L[ℝ] ℂ) = fderiv ℝ (wA μ) x := by
    ext v
    simp [e, LinearEquiv.coe_ofInjectiveEndo]
  have hfd' : HasFDerivAt (wA μ) (e : ℂ →L[ℝ] ℂ) (wA (beltramiInv μ) u) := by
    rw [hgx, he]
    exact hfd.hasFDerivAt
  have hgc : ContinuousAt (wA (beltramiInv μ)) u := by
    refine (wA_continuousOn_finite hμi).continuousAt ((wA_finite_domain_open hμi).mem_nhds ?_)
    show wAS (beltramiInv μ) (u : ExtPlane) ≠ extInf
    rw [hgu]
    exact OnePoint.coe_ne_infty _
  have hleft : ∀ᶠ y in nhds u, wA μ (wA (beltramiInv μ) y) = y := by
    filter_upwards [(wA_finite_domain_open hμi).mem_nhds (show u ∈ {z : ℂ | wAS (beltramiInv μ) (z : ExtPlane) ≠ extInf} by
      show wAS (beltramiInv μ) (u : ExtPlane) ≠ extInf
      rw [hgu]
      exact OnePoint.coe_ne_infty _)] with y hy
    have hy' : wAS (beltramiInv μ) (y : ExtPlane) = ((wA (beltramiInv μ) y : ℂ) : ExtPlane) :=
      (coe_finPart_of_ne hy).symm
    show finPart (wAS μ ((wA (beltramiInv μ) y : ℂ) : ExtPlane)) = y
    rw [← hy']
    have := congrFun (grp_wAS_inv_left hμ) (y : ExtPlane)
    simp only [Function.comp_apply, id] at this
    rw [this]
    rfl
  have hgd : HasFDerivAt (wA (beltramiInv μ)) (e.symm : ℂ →L[ℝ] ℂ) u :=
    HasFDerivAt.of_local_left_inverse hgc hfd' hleft
  refine ⟨hgd.differentiableAt, hgx, ?_⟩
  have hev : wA (beltramiInv μ) ∘ wA μ =ᶠ[nhds x] id := by
    filter_upwards [(wA_finite_domain_open hμ).mem_nhds hfin] with y hy
    have hy' : wAS μ (y : ExtPlane) = ((wA μ y : ℂ) : ExtPlane) := (coe_finPart_of_ne hy).symm
    show finPart (wAS (beltramiInv μ) ((wA μ y : ℂ) : ExtPlane)) = y
    rw [← hy']
    have := congrFun (grp_wAS_inv_right hμ) (y : ExtPlane)
    simp only [Function.comp_apply, id] at this
    rw [this]
    rfl
  exact bc_inverse_dz hfd hgd.differentiableAt hJ.ne' hev

theorem grp_inv_alg {A s ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 4) (hδ : 0 < δ) (hδ1 : δ < 1 / 4)
    (hA : |A - 1| < ε) (hs0 : 0 ≤ s) (hs : s ≤ δ ^ 2) :
    |1 / (A * (1 - s) ^ 2) - 1| < 3 * ε + 4 * δ := by
  have hs1 : s < 1 / 16 := by nlinarith
  have hAl : 1 - ε < A := by linarith [(abs_lt.1 hA).1]
  have hAu : A < 1 + ε := by linarith [(abs_lt.1 hA).2]
  have hq : 7 / 8 < (1 - s) ^ 2 := by nlinarith
  have hq1 : (1 - s) ^ 2 ≤ 1 := by nlinarith
  have hP : 21 / 32 < A * (1 - s) ^ 2 := by nlinarith
  have hPpos : 0 < A * (1 - s) ^ 2 := by linarith
  rw [abs_lt]
  constructor
  · -- 1/P - 1 > -(3ε+4δ):  P ≤ 1+ε, so 1/P ≥ 1/(1+ε) ≥ 1 - ε
    have h1 : A * (1 - s) ^ 2 ≤ 1 + ε := by nlinarith
    have h2 : 1 - ε ≤ 1 / (A * (1 - s) ^ 2) := by
      rw [le_div_iff₀ hPpos]
      nlinarith
    linarith
  · -- 1/P - 1 < 3ε+4δ: P ≥ (1-ε)(1-s)^2 ≥ 1 - ε - 2s
    have h3 : 1 - ε - 2 * s ≤ A * (1 - s) ^ 2 := by nlinarith
    have h4 : 1 / (A * (1 - s) ^ 2) < 1 + 3 * ε + 4 * δ := by
      rw [div_lt_iff₀ hPpos]
      nlinarith [sq_nonneg δ, mul_pos hε hδ]
    linarith

theorem grp_inv_alg2 {α β X U ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 4) (hδ : 0 < δ) (hδ1 : δ < 1 / 4)
    (hα : 0 < α) (hX : X ≠ 0) (hU : U ≠ 0) (hβ0 : 0 ≤ β) (hβ : β ≤ δ ^ 2 * α)
    (h : |α / U ^ 2 - 1 / X ^ 2| < ε / X ^ 2) :
    |α / (α - β) ^ 2 / X ^ 2 - 1 / U ^ 2| < (3 * ε + 4 * δ) / U ^ 2 := by
  have hX2 : 0 < X ^ 2 := by positivity
  have hU2 : 0 < U ^ 2 := by positivity
  set A : ℝ := α * X ^ 2 / U ^ 2 with hAdef
  have hAe : α / U ^ 2 - 1 / X ^ 2 = (A - 1) / X ^ 2 := by
    rw [hAdef]
    field_simp
  have hA : |A - 1| < ε := by
    rw [hAe, abs_div, abs_of_pos hX2, div_lt_div_iff_of_pos_right hX2] at h
    exact h
  set s : ℝ := β / α with hsdef
  have hs0 : 0 ≤ s := div_nonneg hβ0 hα.le
  have hs : s ≤ δ ^ 2 := by
    rw [hsdef, div_le_iff₀ hα]
    linarith
  have hkey := grp_inv_alg hε hε1 hδ hδ1 hA hs0 hs
  have hs1 : s < 1 := by nlinarith
  have hαβ : α - β = α * (1 - s) := by
    rw [hsdef]
    field_simp
  have hid : α / (α - β) ^ 2 / X ^ 2 - 1 / U ^ 2 = (1 / (A * (1 - s) ^ 2) - 1) / U ^ 2 := by
    rw [hαβ, hAdef]
    have h1s : (1 - s) ≠ 0 := by linarith
    field_simp
  rw [hid, abs_div, abs_of_pos hU2, div_lt_div_iff_of_pos_right hU2]
  exact hkey

theorem grp25_inv {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 4) (hδ : 0 < δ) (hδ1 : δ < 1 / 4)
    (hreg : ∀ μ ∈ harmonicBeltrami, ‖μ‖ < δ → ∀ x : ℂ, x ∈ unitDisc ∪ unitDiscExterior →
      wAS μ (x : ExtPlane) ≠ extInf → ContDiffAt ℝ 1 (wA μ) x)
    (h : ∀ μ ∈ harmonicBeltrami, ‖μ‖ < δ → ∀ z : ℂ, z ∈ unitDisc ∪ unitDiscExterior →
      wAS μ (z : ExtPlane) ≠ extInf →
      |‖dz (wA μ) z‖ ^ 2 / (1 - ‖wA μ z‖ ^ 2) ^ 2 - 1 / (1 - ‖z‖ ^ 2) ^ 2| < ε / (1 - ‖z‖ ^ 2) ^ 2) :
    ∀ μ ∈ harmonicBeltrami, ‖μ‖ < δ → ∀ z : ℂ, z ∈ unitDisc ∪ unitDiscExterior →
      wAS (beltramiInv μ) (z : ExtPlane) ≠ extInf →
      |‖dz (wA (beltramiInv μ)) z‖ ^ 2 / (1 - ‖wA (beltramiInv μ) z‖ ^ 2) ^ 2 - 1 / (1 - ‖z‖ ^ 2) ^ 2| <
        (3 * ε + 4 * δ) / (1 - ‖z‖ ^ 2) ^ 2 := by
  intro μ hμ hμδ z hz hne
  have hμb : μ ∈ LinfStarBall := by
    have : ‖μ‖ < 1 := by linarith
    simpa [LinfStarBall] using this
  have hμi : beltramiInv μ ∈ LinfStarBall := grp_inv_mem hμb
  -- the point x = (w_μ)⁻¹ z, on the same side
  obtain ⟨x, hxz, hxside⟩ : ∃ x : ℂ, wAS (beltramiInv μ) (z : ExtPlane) = (x : ExtPlane) ∧
      x ∈ unitDisc ∪ unitDiscExterior := by
    rcases hz with hz | hz
    · obtain ⟨x, hx1, hx⟩ := wAS_maps_disc hμi (show ‖z‖ < 1 from mem_ball_zero_iff.1 hz)
      exact ⟨x, hx, Or.inl (mem_ball_zero_iff.2 hx1)⟩
    · rcases wAS_maps_ext hμi (show 1 < ‖z‖ from hz) with hinf | ⟨x, hx1, hx⟩
      · exact absurd hinf hne
      · exact ⟨x, hx, Or.inr hx1⟩
  have hgz : wA (beltramiInv μ) z = x := by
    show finPart (wAS (beltramiInv μ) (z : ExtPlane)) = x
    rw [hxz]
    rfl
  have hfx : wAS μ (x : ExtPlane) = (z : ExtPlane) := by
    rw [← hxz]
    exact congrFun (grp_wAS_inv_left hμb) (z : ExtPlane)
  have hfin : wAS μ (x : ExtPlane) ≠ extInf := by
    rw [hfx]
    exact OnePoint.coe_ne_infty _
  have hwx : wA μ x = z := by
    show finPart (wAS μ (x : ExtPlane)) = z
    rw [hfx]
    rfl
  have hX := h μ hμ hμδ x hxside hfin
  rw [hwx] at hX
  have hxn : ‖x‖ ^ 2 ≠ 1 := by
    rcases hxside with hx | hx
    · have : ‖x‖ < 1 := mem_ball_zero_iff.1 hx
      nlinarith [norm_nonneg x]
    · have : 1 < ‖x‖ := hx
      nlinarith [norm_nonneg x]
  have hzn : ‖z‖ ^ 2 ≠ 1 := by
    rcases hz with hz | hz
    · have : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
      nlinarith [norm_nonneg z]
    · have : 1 < ‖z‖ := hz
      nlinarith [norm_nonneg z]
  have hXne : 1 - ‖x‖ ^ 2 ≠ 0 := fun h0 => hxn (by linarith)
  have hUne : 1 - ‖z‖ ^ 2 ≠ 0 := fun h0 => hzn (by linarith)
  -- dz of the forward map is nonzero
  have hdz : dz (wA μ) x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hX
    have hpos : 0 < (1 - ‖x‖ ^ 2) ^ 2 := by positivity
    have h1 : |(0 : ℝ) ^ 2 / (1 - ‖z‖ ^ 2) ^ 2 - 1 / (1 - ‖x‖ ^ 2) ^ 2| = 1 / (1 - ‖x‖ ^ 2) ^ 2 := by
      rw [zero_pow two_ne_zero, zero_div, zero_sub, abs_neg, abs_of_pos (one_div_pos.2 hpos)]
    rw [h1, div_lt_div_iff_of_pos_right hpos] at hX
    linarith
  have hxreg := hreg μ hμ hμδ x hxside hfin
  obtain ⟨hgd, hgx, hgdz⟩ := grp_inv_deriv hμb hxreg hfin hdz
  rw [hwx] at hgd hgx hgdz
  have hb := grp_dil_bound hμb hxreg
  rw [hgz, hgdz]
  set a := dz (wA μ) x with ha
  set b := dzbar (wA μ) x with hbdef
  have hα : 0 < ‖a‖ ^ 2 := by positivity
  have hJ : jacobian (wA μ) x = ‖a‖ ^ 2 - ‖b‖ ^ 2 := rfl
  have hnorm : ‖conj a / ((jacobian (wA μ) x : ℝ) : ℂ)‖ ^ 2 = ‖a‖ ^ 2 / (‖a‖ ^ 2 - ‖b‖ ^ 2) ^ 2 := by
    rw [norm_div, Complex.norm_conj, Complex.norm_real, div_pow, hJ]
    have hJpos : 0 < ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
      have hbl : ‖b‖ < ‖a‖ := by
        calc ‖b‖ ≤ ‖μ‖ * ‖a‖ := hb
          _ < 1 * ‖a‖ := mul_lt_mul_of_pos_right (by linarith) (norm_pos_iff.2 hdz)
          _ = ‖a‖ := one_mul _
      nlinarith [norm_nonneg b]
    rw [Real.norm_of_nonneg hJpos.le]
  rw [hnorm]
  have hβ : ‖b‖ ^ 2 ≤ δ ^ 2 * ‖a‖ ^ 2 := by
    have h1 : ‖b‖ ≤ δ * ‖a‖ := hb.trans (mul_le_mul_of_nonneg_right hμδ.le (norm_nonneg a))
    calc ‖b‖ ^ 2 ≤ (δ * ‖a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg b) h1 2
      _ = δ ^ 2 * ‖a‖ ^ 2 := by ring
  exact grp_inv_alg2 hε hε1 hδ hδ1 hα hXne hUne (sq_nonneg _) hβ hX

theorem grp_dzbar_comp_holo {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℂ g (f z)) :
    dzbar (fun u => g (f u)) z = deriv g (f z) * dzbar f z := by
  have h := eq6_2_dzbar_comp hf (hg.restrictScalars ℝ)
  have hb : dzbar g (f z) = 0 := (cauchyRiemann_iff.1 hg).2
  have h2 : dzbar (g ∘ f) z = deriv g (f z) * dzbar f z := by
    rw [h, hb, zero_mul, add_zero, dz_eq_deriv hg]
  exact h2

theorem grp_refl_dz {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) (hf : DifferentiableAt ℝ f (refl z))
    (hfz : f (refl z) ≠ 0) :
    DifferentiableAt ℝ (fun y => refl (f (refl y))) z ∧
      dz (fun y => refl (f (refl y))) z = conj (dz f (refl z)) / (z ^ 2 * conj (f (refl z)) ^ 2) := by
  have hcz : conj z ≠ 0 := by simpa using hz
  obtain ⟨hcd, hdzc, hdzbc⟩ := l333_mux_dz_conj z
  have hinv : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) (conj z) := differentiableAt_inv (𝕜 := ℂ) hcz
  have hq : DifferentiableAt ℝ refl z := by
    show DifferentiableAt ℝ (fun w : ℂ => (conj w)⁻¹) z
    exact (hinv.restrictScalars ℝ).comp z hcd
  have hqdz : dz refl z = 0 := by
    have := (grp_dz_comp_holo hcd hinv).2
    show dz (fun w : ℂ => (conj w)⁻¹) z = 0
    rw [this]
    simp [hdzc]
  have hqdzbar : dzbar refl z = -((conj z) ^ 2)⁻¹ := by
    have := grp_dzbar_comp_holo hcd hinv
    show dzbar (fun w : ℂ => (conj w)⁻¹) z = _
    rw [this, hdzbc, mul_one, deriv_inv]
  have hp : DifferentiableAt ℝ (fun y => f (refl y)) z := hf.comp z hq
  have hpdzbar : dzbar (fun y => f (refl y)) z = dz f (refl z) * (-((conj z) ^ 2)⁻¹) := by
    have h := eq6_2_dzbar_comp hq hf
    have h3 : dzbar (fun w => conj (refl w)) z = 0 := by
      rw [← (eq6_3 hq).1, hqdz]
      simp
    have h4 : dzbar (fun y => f (refl y)) z = dz f (refl z) * dzbar refl z + dzbar f (refl z) * 0 :=
      h.trans (by rw [h3])
    rw [hqdzbar] at h4
    simpa using h4
  have hcp : DifferentiableAt ℝ (fun y => conj (f (refl y))) z := Complex.differentiable_conj.differentiableAt.comp z hp
  have hcfz : conj (f (refl z)) ≠ 0 := by simpa using hfz
  have hinv2 : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) (conj (f (refl z))) := differentiableAt_inv (𝕜 := ℂ) hcfz
  obtain ⟨hd1, hd2⟩ := grp_dz_comp_holo hcp hinv2
  refine ⟨hd1, ?_⟩
  show dz (fun y => (conj (f (refl y)))⁻¹) z = _
  rw [hd2, deriv_inv, ← (eq6_3 hp).2, hpdzbar]
  simp only [map_mul, map_neg, map_inv₀, map_pow, Complex.conj_conj]
  field_simp

theorem grp_refl_alg {Nz t r d ε : ℝ} (hNz : 0 < Nz) (hNz1 : Nz ≠ 1) (ht : t = 1 / Nz) (hr : 0 < r)
    (hr1 : r ≠ 1) (h : |d / (1 - r ^ 2) ^ 2 - 1 / (1 - t ^ 2) ^ 2| < ε / (1 - t ^ 2) ^ 2) :
    |d / (Nz ^ 4 * r ^ 4) / (1 - (1 / r) ^ 2) ^ 2 - 1 / (1 - Nz ^ 2) ^ 2| < ε / (1 - Nz ^ 2) ^ 2 := by
  have ht1 : 1 - t ^ 2 ≠ 0 := by
    intro h0
    have : t ^ 2 = 1 := by linarith
    have ht0 : 0 < t := by rw [ht]; positivity
    have : t = 1 := by nlinarith
    apply hNz1
    rw [ht] at this
    field_simp at this
    linarith
  have hr2 : 1 - r ^ 2 ≠ 0 := by
    intro h0
    apply hr1
    nlinarith
  have hN2 : 1 - Nz ^ 2 ≠ 0 := by
    intro h0
    apply hNz1
    nlinarith
  have hrr : d / (Nz ^ 4 * r ^ 4) / (1 - (1 / r) ^ 2) ^ 2 = d / Nz ^ 4 / (1 - r ^ 2) ^ 2 := by
    have hr0 : r ≠ 0 := hr.ne'
    have hr3 : r ^ 2 - 1 ≠ 0 := fun h0 => hr2 (by linarith)
    have e : (1 - (1 / r) ^ 2) = (r ^ 2 - 1) / r ^ 2 := by field_simp
    have e2 : (1 - r ^ 2) ^ 2 = (r ^ 2 - 1) ^ 2 := by ring
    rw [e, e2, div_pow]
    field_simp
  have hNN : (1 - Nz ^ 2) ^ 2 = Nz ^ 4 * (1 - t ^ 2) ^ 2 := by
    rw [ht]
    field_simp
    ring
  have hpos : 0 < Nz ^ 4 := by positivity
  have hq : 0 < (1 - t ^ 2) ^ 2 := by positivity
  rw [hrr, hNN]
  have e1 : d / Nz ^ 4 / (1 - r ^ 2) ^ 2 - 1 / (Nz ^ 4 * (1 - t ^ 2) ^ 2) =
      (d / (1 - r ^ 2) ^ 2 - 1 / (1 - t ^ 2) ^ 2) / Nz ^ 4 := by
    field_simp
  have e2 : ε / (Nz ^ 4 * (1 - t ^ 2) ^ 2) = (ε / (1 - t ^ 2) ^ 2) / Nz ^ 4 := by
    field_simp
  rw [e1, e2, abs_div, abs_of_pos hpos, div_lt_div_iff_of_pos_right hpos]
  exact h

theorem grp25_reflect {ε δ : ℝ} (hδ1 : δ < 1)
    (hD : ∀ μ ∈ harmonicBeltrami, ‖μ‖ < δ → ∀ z ∈ unitDisc, DifferentiableAt ℝ (wA μ) z ∧
      |‖dz (wA μ) z‖ ^ 2 / (1 - ‖wA μ z‖ ^ 2) ^ 2 - 1 / (1 - ‖z‖ ^ 2) ^ 2| < ε / (1 - ‖z‖ ^ 2) ^ 2) :
    ∀ μ ∈ harmonicBeltrami, ‖μ‖ < δ → ∀ z ∈ unitDiscExterior, wAS μ (z : ExtPlane) ≠ extInf →
      |‖dz (wA μ) z‖ ^ 2 / (1 - ‖wA μ z‖ ^ 2) ^ 2 - 1 / (1 - ‖z‖ ^ 2) ^ 2| < ε / (1 - ‖z‖ ^ 2) ^ 2 := by
  intro μ hμ hμδ z hz hne
  have hμb : μ ∈ LinfStarBall := by
    have : ‖μ‖ < 1 := by linarith
    simpa [LinfStarBall] using this
  have hzn : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hzn
    simp at hzn
    linarith
  obtain ⟨v, hv1, hvv⟩ : ∃ v : ℂ, 1 < ‖v‖ ∧ wAS μ (z : ExtPlane) = (v : ExtPlane) := by
    rcases wAS_maps_ext hμb hzn with h | ⟨u, h1, h2⟩
    · exact absurd h hne
    · exact ⟨u, h1, h2⟩
  have hgv : wA μ z = v := by
    show finPart (wAS μ (z : ExtPlane)) = v
    rw [hvv]
    rfl
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv1
    linarith
  have h12 := eq_1_2 hμb hz0 (by rw [hgv]; exact hv0)
  rw [hgv] at h12
  have hfz' : wA μ (refl z) = conj (1 / v) := by
    have := congrArg conj h12.symm
    simpa using this
  have hz'D : refl z ∈ unitDisc := mem_ball_zero_iff.2 (by
    show ‖(conj z)⁻¹‖ < 1
    rw [norm_inv, Complex.norm_conj]
    exact inv_lt_one_of_one_lt₀ hzn)
  obtain ⟨hfd, hineq⟩ := hD μ hμ hμδ (refl z) hz'D
  have hfne : wA μ (refl z) ≠ 0 := by
    rw [hfz']
    simpa using hv0
  obtain ⟨-, hHdz⟩ := grp_refl_dz hz0 hfd hfne
  have hDo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hev : wA μ =ᶠ[nhds z] fun y => refl (wA μ (refl y)) := by
    filter_upwards [(wA_finite_domain_open hμb).mem_nhds hne, hDo.mem_nhds hz] with y hy1 hy2
    have hy2' : 1 < ‖y‖ := hy2
    have hy0 : y ≠ 0 := by
      intro h
      rw [h] at hy2'
      simp at hy2'
      linarith
    have hyfin : wAS μ (y : ExtPlane) ≠ extInf := hy1
    obtain ⟨u, hu1, hu⟩ : ∃ u : ℂ, 1 < ‖u‖ ∧ wAS μ (y : ExtPlane) = (u : ExtPlane) := by
      rcases wAS_maps_ext hμb hy2' with h | ⟨u, h1, h2⟩
      · exact absurd h hyfin
      · exact ⟨u, h1, h2⟩
    have hgy : wA μ y = u := by
      show finPart (wAS μ (y : ExtPlane)) = u
      rw [hu]
      rfl
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu1
      linarith
    have h := eq_1_2 hμb hy0 (by rw [hgy]; exact hu0)
    show wA μ y = (conj (wA μ (refl y)))⁻¹
    rw [← h, one_div, inv_inv]
  have hdzg : dz (wA μ) z = conj (dz (wA μ) (refl z)) / (z ^ 2 * conj (wA μ (refl z)) ^ 2) := by
    rw [(t203_c1_dz_congr hev).1]
    exact hHdz
  have hr : ‖wA μ (refl z)‖ = 1 / ‖v‖ := by
    rw [hfz']
    simp
  have hvpos : 0 < ‖v‖ := by linarith
  have hrpos : 0 < ‖wA μ (refl z)‖ := by rw [hr]; positivity
  have hnorm_dz : ‖dz (wA μ) z‖ ^ 2 =
      ‖dz (wA μ) (refl z)‖ ^ 2 / (‖z‖ ^ 4 * ‖wA μ (refl z)‖ ^ 4) := by
    rw [hdzg, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_conj, Complex.norm_conj]
    have hz' : 0 < ‖z‖ := by linarith
    field_simp
  have hnv : ‖wA μ z‖ = 1 / ‖wA μ (refl z)‖ := by
    rw [hgv, hr]
    field_simp
  have hzt : ‖refl z‖ = 1 / ‖z‖ := by
    show ‖(conj z)⁻¹‖ = _
    rw [norm_inv, Complex.norm_conj, one_div]
  rw [hnorm_dz, hnv]
  refine grp_refl_alg (by linarith) (by linarith) hzt hrpos ?_ ?_
  · rw [hr]
    intro h
    have : 1 / ‖v‖ < 1 := by rw [div_lt_one hvpos]; exact hv1
    linarith
  · rw [← hzt] at *
    exact hineq

end TakhtajanTeo

#print axioms TakhtajanTeo.grp25_inv
#print axioms TakhtajanTeo.grp25_reflect

