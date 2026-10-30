import TakhtajanTeo.Ch1.QCVariationDensity

/-! # The infinitesimal Bers kernel equals the annihilator of exterior quadratic differentials -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

/-- Outward dilations of an exterior test are annihilated by a kernel element. -/
theorem qcv_ker_pairing_dilate {μ : LinfStar} (hμ : fderiv ℂ bersPhi 0 μ = 0)
    {φ : ℂ → ℂ} (hφ : φ ∈ AOneStar) {r : ℝ} (hr : 1 < r) :
    ∫ w in unitDiscExterior, μ w * φ (r • w) = 0 := by
  obtain ⟨F, hF, heq⟩ := qcv_AOneStar_exists_disc_extension hφ
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  let G : ℂ → ℂ := fun z => F ((r : ℂ)⁻¹ * z) / (r : ℂ) ^ 4
  have hm : MapsTo (fun z : ℂ => (r : ℂ)⁻¹ * z) (ball 0 r) unitDisc := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    rw [inv_mul_eq_div, div_lt_one hr0]
    exact mem_ball_zero_iff.mp hz
  have hG : DifferentiableOn ℂ G (ball 0 r) :=
    (hF.comp ((differentiableOn_const (c := (r : ℂ)⁻¹)).mul
      differentiableOn_id) hm).div_const _
  obtain ⟨c, hc, hs⟩ := qcv_exists_summable_powerSeries hr hG
  apply qcv_pairing_eq_zero_of_summable_laurent hμ hc
  intro w hw
  have hw1 : 1 < ‖w‖ := hw
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hw1)
  have hi : w⁻¹ ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr
    rw [norm_inv]
    exact (inv_lt_one₀ (lt_trans zero_lt_one hw1)).mpr hw1
  have hrw : (r : ℂ) * w ∈ unitDiscExterior := by
    change 1 < ‖(r : ℂ) * w‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact lt_of_lt_of_le hw1 (le_mul_of_one_le_left (norm_nonneg w) hr.le)
  have hrw0 : (r : ℂ) * w ≠ 0 := mul_ne_zero hrc hw0
  have hri : ((r : ℂ) * w)⁻¹ ∈ unitDisc \ {0} := by
    refine ⟨?_, inv_ne_zero hrw0⟩
    apply mem_ball_zero_iff.mpr
    rw [norm_inv]
    exact (inv_lt_one₀ (lt_trans zero_lt_one hrw)).mpr hrw
  have he : G w⁻¹ * (w ^ 4)⁻¹ = φ (r • w) := by
    dsimp [G]
    rw [← mul_inv, heq _ hri, inv_inv, inv_pow]
    field_simp
  have hh := (hs w⁻¹ hi).mul_right (w ^ 4)⁻¹
  rw [he] at hh
  convert hh using 1
  ext n
  simp only [inv_pow, pow_add, div_eq_mul_inv, mul_inv]
  ring

/-- Pairing with an essentially bounded Beltrami coefficient is continuous in `L¹`. -/
theorem qcv_pairing_sub_norm_le (μ : LinfStar) {f g : ℂ → ℂ}
    (hf : IntegrableOn f unitDiscExterior) (hg : IntegrableOn g unitDiscExterior) :
    ‖(∫ w in unitDiscExterior, μ w * g w) - ∫ w in unitDiscExterior, μ w * f w‖ ≤
      ‖μ‖ * ∫ w in unitDiscExterior, ‖g w - f w‖ := by
  have hmf := hf.mul_of_top_right (Lp.memLp μ)
  have hmg := hg.mul_of_top_right (Lp.memLp μ)
  have hmd := (hg.sub hf).mul_of_top_right (Lp.memLp μ)
  have hsub := integral_sub hmg hmf
  dsimp only [Pi.mul_apply, Pi.sub_apply] at hmf hmg hmd hsub
  rw [← hsub]
  calc ‖∫ w in unitDiscExterior, μ w * g w - μ w * f w‖
      = ‖∫ w in unitDiscExterior, μ w * (g w - f w)‖ := by
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun w => (mul_sub _ _ _).symm
    _ ≤ ∫ w in unitDiscExterior, ‖μ w * (g w - f w)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ w in unitDiscExterior, ‖μ‖ * ‖g w - f w‖ := by
      apply integral_mono_ae hmd.norm ((hg.sub hf).norm.const_mul ‖μ‖)
      filter_upwards [LinfStar_ae_norm_le μ] with w hw
      dsimp only [Pi.mul_apply, Pi.sub_apply]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- A Bers-kernel element annihilates every admissible exterior quadratic differential. -/
theorem qcv_ker_D0Phi_pairing {μ : LinfStar} (hμ : fderiv ℂ bersPhi 0 μ = 0)
    {φ : ℂ → ℂ} (hφ : φ ∈ AOneStar) :
    ∫ w in unitDiscExterior, μ w * φ w = 0 := by
  let r : ℕ → ℝ := fun n => 1 + 1 / (n + 1 : ℝ)
  have hr : ∀ n, 1 < r n := by
    intro n
    dsimp [r]
    have hp : 0 < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have ht : Tendsto r atTop (𝓝 1) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    simpa only [add_zero] using hh
  have hlim := qcv_exterior_dilate_L1 hφ.2.1 hφ.1.continuousOn
    (fun n => (hr n).le) ht
  have hlim' : Tendsto
      (fun n => ‖μ‖ * ∫ w in unitDiscExterior, ‖φ (r n • w) - φ w‖)
      atTop (𝓝 0) := by simpa using hlim.const_mul ‖μ‖
  have hb : ∀ n, ‖∫ w in unitDiscExterior, μ w * φ w‖ ≤
      ‖μ‖ * ∫ w in unitDiscExterior, ‖φ (r n • w) - φ w‖ := by
    intro n
    have hh := qcv_pairing_sub_norm_le μ hφ.2.1
      (qcv_exterior_dilate_integrable hφ.2.1 (hr n).le).1
    rw [qcv_ker_pairing_dilate hμ hφ (hr n), zero_sub, norm_neg] at hh
    exact hh
  have hz : ‖∫ w in unitDiscExterior, μ w * φ w‖ ≤ 0 := ge_of_tendsto' hlim' hb
  exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))

/-- Exact counterpart of the original `ker_D0Phi`, proved from the corrected test space. -/
theorem qcv_ker_D0Phi :
    LinearMap.ker (fderiv ℂ bersPhi 0 : LinfStar →ₗ[ℂ] AInf unitDisc) =
      trivialBeltrami := by
  apply le_antisymm ?_ qcv_trivialBeltrami_le_ker_D0Phi
  intro μ hμ
  rw [mem_trivialBeltrami_iff]
  intro φ hφ
  exact qcv_ker_D0Phi_pairing hμ hφ

end QCV
end TakhtajanTeo
