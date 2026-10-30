import TakhtajanTeo.Ch1.S2_HilbertManifold
import TakhtajanTeo.Ch1.BeltramiCompose
import TakhtajanTeo.Ch1.QCVariationBergman

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem hb_zero_mul {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : beltramiMul 0 μ = μ := by
  obtain ⟨D, hD⟩ := bc_exists_D hμ
  have h := bc_remainder (l := 0) hμ D hD (by simp)
  exact sub_eq_zero.mp (by simpa using h)

theorem hb_Rnm_D0Right {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    Rnm (fderiv ℂ (fun l => beltramiMul l μ) 0 ν) μ = ν := by
  apply Lp.ext
  filter_upwards [bc_Rnm_ae hμ (fderiv ℂ (fun l => beltramiMul l μ) 0 ν),
    bc_invFun_pullback_ae hμ (bc_remark_1_3 hμ ν), bc_invFun_right_ae hμ,
    bc_invFun_pullback_ae hμ (LinfStar_ae_norm_le μ),
    bc_invFun_pullback_ae hμ (ae_restrict_of_ae (bc_wA_ae hμ))] with y h1 h2 h3 hm hg
  rw [h1, h2, h3]
  have hd : 0 < 1 - ‖μ (Function.invFun (wA μ) y)‖ ^ 2 := by
    have hμ1 := bc_norm_lt_one hμ
    nlinarith [norm_nonneg (μ (Function.invFun (wA μ) y))]
  have hdc : (1 : ℂ) - (‖μ (Function.invFun (wA μ) y)‖ : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hd.ne'
  have hz := hg.2.1
  have hcz : conj (dz (wA μ) (Function.invFun (wA μ) y)) ≠ 0 := by simpa using hz
  field_simp

theorem hb_D0Right_Rnm {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    fderiv ℂ (fun l => beltramiMul l μ) 0 (Rnm ν μ) = ν := by
  apply Lp.ext
  filter_upwards [bc_remark_1_3 hμ (Rnm ν μ), bc_pullback_ae hμ (bc_Rnm_ae hμ ν),
    bc_pullback_ae hμ (ae_restrict_mem bc_hEo.measurableSet), LinfStar_ae_norm_le μ,
    ae_restrict_of_ae (bc_wA_ae hμ)] with x h1 h2 hx hm hg
  have hn : wA μ x ≠ 0 := by intro he; norm_num [he, unitDiscExterior] at hx
  rw [h1, h2, bc_invFun_wA hn]
  have hd : 0 < 1 - ‖μ x‖ ^ 2 := by
    have hμ1 := bc_norm_lt_one hμ
    nlinarith [norm_nonneg (μ x)]
  have hdc : (1 : ℂ) - (‖μ x‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hd.ne'
  have hz := hg.2.1
  have hcz : conj (dz (wA μ) x) ≠ 0 := by simpa using hz
  field_simp

/-- Right translation induces a bijective bounded linear map on coefficient tangent spaces. -/
theorem hb_D0Right_bijective {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Function.Bijective (fderiv ℂ (fun l => beltramiMul l μ) 0) := by
  constructor
  · intro ν₁ ν₂ he
    have h := congrArg (fun η => Rnm η μ) he
    simpa only [hb_Rnm_D0Right hμ] using h
  · intro ν
    exact ⟨Rnm ν μ, hb_D0Right_Rnm hμ ν⟩

theorem hb_bers_right_hasFDerivAt {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    HasFDerivAt (fun l => bersPhi (beltramiMul l μ))
      ((fderiv ℂ bersPhi μ).comp (fderiv ℂ (fun l => beltramiMul l μ) 0)) 0 := by
  obtain ⟨D, hd, hD⟩ := bc_hasFDerivAt hμ
  have hb := (QCV.qcv_bersPhi_differentiableOn.differentiableAt (isOpen_ball.mem_nhds hμ)).hasFDerivAt
  have hb' : HasFDerivAt bersPhi (fderiv ℂ bersPhi μ) (beltramiMul 0 μ) := by
    rwa [hb_zero_mul hμ]
  simpa only [hd.fderiv, Function.comp_def] using hb'.comp 0 hd

/-- The chain rule asserted in the definition's mathematical description, with actual derivatives. -/
theorem hb_D0BersR_chain {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    D0BersR μ = (fderiv ℂ bersPhi μ).comp (fderiv ℂ (fun l => beltramiMul l μ) 0) :=
  (hb_bers_right_hasFDerivAt hμ).fderiv

theorem hb_D0BersR_hasFDerivAt {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    HasFDerivAt (fun l => bersPhi (beltramiMul l μ)) (D0BersR μ) 0 := by
  rw [hb_D0BersR_chain hμ]
  exact hb_bers_right_hasFDerivAt hμ

theorem hb_D0BersR_pointwise {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar)
    {z : ℂ} (hz : z ∈ unitDisc) :
    HasDerivAt (fun t : ℂ => AInf.toFun (bersPhi (beltramiMul (t • ν) μ)) z)
      (AInf.toFun (D0BersR μ ν) z) 0 := by
  have hl : HasDerivAt (fun t : ℂ => t • ν) ν 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const ν
  have hD : HasFDerivAt (fun l => bersPhi (beltramiMul l μ)) (D0BersR μ) ((0 : ℂ) • ν) := by
    simpa using hb_D0BersR_hasFDerivAt hμ
  have hline := hD.comp_hasDerivAt 0 hl
  let ev : AInf unitDisc →L[ℂ] ℂ :=
    ((1 - ‖z‖ ^ 2 : ℂ) ^ 2)⁻¹ • ((BoundedContinuousFunction.evalCLM ℂ (⟨z, hz⟩ : unitDisc)).comp
      (Submodule.subtypeL _))
  have hev : ∀ φ : AInf unitDisc, ev φ = AInf.toFun φ z := by
    intro φ
    simp [ev, AInf.toFun, unweight, dite_eq_left hz, div_eq_inv_mul]
  simpa only [Function.comp_def, hev] using ev.hasFDerivAt.comp_hasDerivAt 0 hline

/-- Pointwise variation needed before transporting the fourth-order kernel to the welding domains. -/
theorem hb_D0BersR_schwarzian {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar)
    {z : ℂ} (hz : z ∈ unitDisc) :
    HasDerivAt (fun t : ℂ => schwarzianHol (fB (beltramiMul (t • ν) μ)) z)
      (AInf.toFun (D0BersR μ ν) z) 0 := by
  obtain ⟨D, hd, hD⟩ := bc_hasFDerivAt hμ
  have hc : ContinuousAt (fun t : ℂ => beltramiMul (t • ν) μ) 0 := by
    have hl : ContinuousAt (fun t : ℂ => t • ν) 0 := by fun_prop
    have hd' : ContinuousAt (fun l => beltramiMul l μ) ((0 : ℂ) • ν) := by
      simpa using hd.continuousAt
    exact hd'.comp (f := fun t : ℂ => t • ν) hl
  have hball : ∀ᶠ t : ℂ in 𝓝 0, beltramiMul (t • ν) μ ∈ LinfStarBall := by
    have hbase : beltramiMul ((0 : ℂ) • ν) μ ∈ LinfStarBall := by
      simpa only [zero_smul, hb_zero_mul hμ] using hμ
    exact hc (isOpen_ball.mem_nhds hbase)
  apply (hb_D0BersR_pointwise hμ ν hz).congr_of_eventuallyEq
  filter_upwards [hball] with t ht
  exact ((bersPhi_spec ht).1 z hz).symm

/-- Conformal area change for the fourth-order kernel, including the Beltrami phase.
No integrability premise is needed for this identity of Bochner integrals. -/
theorem hb_fourth_kernel_transport {g : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hg : IsConformalOnto g U V) (ν : ℂ → ℂ) (z : ℂ) :
    (∫ u in g '' U, ν (Function.invFunOn g U u) *
      (conj (deriv (Function.invFunOn g U) u) / deriv (Function.invFunOn g U) u) /
        (u - z) ^ 4) =
      ∫ w in U, ν w * deriv g w ^ 2 / (g w - z) ^ 4 := by
  rw [ahP_integral_image hU hg.1 hg.2.1]
  apply setIntegral_congr_fun hU.measurableSet
  intro w hw
  have hleft := hg.2.1.leftInvOn_invFunOn hw
  have hmul := t1_deriv_invFunOn_mul hU hg hw
  have hne : deriv g w ≠ 0 := deriv_ne_zero_of_injOn hU hg.1 hg.2.1 hw
  have hi : deriv (Function.invFunOn g U) (g w) = (deriv g w)⁻¹ :=
    eq_inv_of_mul_eq_one_left hmul
  dsimp only
  rw [hleft, hi, Complex.real_smul]
  have hcn : conj (deriv g w) ≠ 0 := by simpa using hne
  have hn : ((‖deriv g w‖ ^ 2 : ℝ) : ℂ) = deriv g w * conj (deriv g w) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hphase : ((‖deriv g w‖ ^ 2 : ℝ) : ℂ) *
      (conj ((deriv g w)⁻¹) / (deriv g w)⁻¹) = deriv g w ^ 2 := by
    rw [hn, map_inv₀]
    field_simp
  calc ((‖deriv g w‖ ^ 2 : ℝ) : ℂ) *
        (ν w * (conj ((deriv g w)⁻¹) / (deriv g w)⁻¹) / (g w - z) ^ 4) =
      ν w * (((‖deriv g w‖ ^ 2 : ℝ) : ℂ) *
        (conj ((deriv g w)⁻¹) / (deriv g w)⁻¹)) / (g w - z) ^ 4 := by ring
    _ = _ := by rw [hphase]

/-- The exact analytic reduction behind (2.1): after conformal transport, the remaining
claim is a kernel variation on the original parameter domains. -/
theorem hb_fourth_kernel_pullback_iff {f g : ℂ → ℂ} {U V U' V' : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hf : IsConformalOnto f U U')
    (hg : IsConformalOnto g V V') (q ν : ℂ → ℂ) (c : ℂ) {w : ℂ} (hw : w ∈ U) :
    (q (Function.invFunOn f U (f w)) * deriv (Function.invFunOn f U) (f w) ^ 2 =
      c * ∫ u in g '' V, ν (Function.invFunOn g V u) *
        (conj (deriv (Function.invFunOn g V) u) / deriv (Function.invFunOn g V) u) /
          (u - f w) ^ 4) ↔
      q w = c * deriv f w ^ 2 * ∫ ζ in V, ν ζ * deriv g ζ ^ 2 / (g ζ - f w) ^ 4 := by
  have hne := deriv_ne_zero_of_injOn hU hf.1 hf.2.1 hw
  have hi : deriv (Function.invFunOn f U) (f w) = (deriv f w)⁻¹ :=
    eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul hU hf hw)
  rw [hf.2.1.leftInvOn_invFunOn hw, hi, hb_fourth_kernel_transport hV hg ν (f w),
    inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero 2 hne)]
  rw [mul_right_comm c _ (deriv f w ^ 2)]

end TakhtajanTeo
