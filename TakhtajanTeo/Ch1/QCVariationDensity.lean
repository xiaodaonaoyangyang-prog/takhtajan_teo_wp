import TakhtajanTeo.Ch1.QCVariationLaurent
import TakhtajanTeo.Ch1.QCVariationMoments
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Integral convergence for exterior Laurent approximation -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

/-- Pointwise convergence with no increase in integral norm gives `L¹` convergence. -/
theorem qcv_L1_tendsto_of_integral_norm_le {m : Measure ℂ}
    {f : ℂ → ℂ} {g : ℕ → ℂ → ℂ} (hf : Integrable f m)
    (hg : ∀ n, Integrable (g n) m)
    (hb : ∀ n, ∫ z, ‖g n z‖ ∂m ≤ ∫ z, ‖f z‖ ∂m)
    (ht : ∀ᵐ z ∂m, Tendsto (fun n => g n z) atTop (𝓝 (f z))) :
    Tendsto (fun n => ∫ z, ‖g n z - f z‖ ∂m) atTop (𝓝 0) := by
  let G : ℕ → ℂ → ℝ := fun n z => ‖g n z‖ + ‖f z‖ - ‖g n z - f z‖
  have hG : ∀ n, Integrable (G n) m := fun n =>
    ((hg n).norm.add hf.norm).sub ((hg n).sub hf).norm
  have hG0 : ∀ n z, 0 ≤ G n z := by
    intro n z
    dsimp [G]
    linarith [norm_sub_le (g n z) (f z)]
  have hGb : ∀ n z, G n z ≤ 2 * ‖f z‖ := by
    intro n z
    dsimp [G]
    linarith [norm_sub_norm_le (g n z) (f z)]
  have hlim : Tendsto (fun n => ∫ z, G n z ∂m) atTop
      (𝓝 (∫ z, 2 * ‖f z‖ ∂m)) := by
    apply tendsto_integral_of_dominated_convergence (fun z => 2 * ‖f z‖)
      (fun n => (hG n).aestronglyMeasurable) (hf.norm.const_mul 2)
    · intro n
      exact ae_of_all _ fun z => by rw [Real.norm_of_nonneg (hG0 n z)]; exact hGb n z
    · filter_upwards [ht] with z hz
      have hh := (hz.norm.add_const ‖f z‖).sub ((hz.sub_const (f z)).norm)
      simpa [G, two_mul] using hh
  have hlim' : Tendsto (fun n => 2 * (∫ z, ‖f z‖ ∂m) - ∫ z, G n z ∂m)
      atTop (𝓝 0) := by
    simpa only [integral_const_mul, sub_self] using
      hlim.const_sub (2 * ∫ z, ‖f z‖ ∂m)
  apply squeeze_zero (fun n => integral_nonneg fun z => norm_nonneg _) ?_ hlim'
  intro n
  have he : ∫ z, G n z ∂m =
      (∫ z, ‖g n z‖ ∂m) + (∫ z, ‖f z‖ ∂m) - ∫ z, ‖g n z - f z‖ ∂m := by
    have hsub := integral_sub ((hg n).norm.add hf.norm) ((hg n).sub hf).norm
    have hadd := integral_add (hg n).norm hf.norm
    dsimp only [Pi.add_apply, Pi.sub_apply] at hsub hadd
    exact hsub.trans (congrArg (fun a => a - ∫ z, ‖g n z - f z‖ ∂m) hadd)
  linarith [hb n]

/-- Outward dilations of an integrable exterior function do not increase its integral norm. -/
theorem qcv_exterior_dilate_integrable {φ : ℂ → ℂ}
    (hφ : IntegrableOn φ unitDiscExterior) {r : ℝ} (hr : 1 ≤ r) :
    IntegrableOn (fun z => φ (r • z)) unitDiscExterior ∧
      (∫ z in unitDiscExterior, ‖φ (r • z)‖) ≤ ∫ z in unitDiscExterior, ‖φ z‖ := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hD : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  let F := unitDiscExterior.indicator φ
  have hF : Integrable F := hφ.integrable_indicator hD
  have hFr : Integrable (fun z : ℂ => F (r • z)) := hF.comp_smul hr0.ne'
  have he : ∀ z ∈ unitDiscExterior, F (r • z) = φ (r • z) := by
    intro z hz
    apply indicator_of_mem
    change 1 < ‖r • z‖
    rw [norm_smul, Real.norm_of_nonneg hr0.le]
    exact lt_of_lt_of_le hz (le_mul_of_one_le_left (norm_nonneg z) hr)
  have hri : IntegrableOn (fun z => φ (r • z)) unitDiscExterior :=
    hFr.integrableOn.congr (ae_restrict_of_forall_mem hD he)
  refine ⟨hri, ?_⟩
  calc (∫ z in unitDiscExterior, ‖φ (r • z)‖)
      = ∫ z in unitDiscExterior, ‖F (r • z)‖ :=
        setIntegral_congr_fun hD fun z hz => congrArg norm (he z hz).symm
    _ ≤ ∫ z : ℂ, ‖F (r • z)‖ := setIntegral_le_integral hFr.norm
      (ae_of_all _ fun z => norm_nonneg _)
    _ = (r ^ 2)⁻¹ * ∫ z : ℂ, ‖F z‖ := by
      simpa only [Complex.finrank_real_complex, smul_eq_mul] using
        Measure.integral_comp_smul_of_nonneg volume (fun z => ‖F z‖) r (hR := hr0.le)
    _ ≤ ∫ z : ℂ, ‖F z‖ := by
      apply mul_le_of_le_one_left (integral_nonneg fun z => norm_nonneg _)
      exact (inv_le_one₀ (pow_pos hr0 2)).mpr (one_le_pow₀ hr)
    _ = ∫ z in unitDiscExterior, ‖φ z‖ := by
      rw [show (fun z => ‖F z‖) = unitDiscExterior.indicator (fun z => ‖φ z‖) by
        ext z; by_cases hz : z ∈ unitDiscExterior <;> simp [F, hz]]
      exact integral_indicator hD

/-- Continuity inside the exterior and outward dilation give `L¹` approximation. -/
theorem qcv_exterior_dilate_L1 {φ : ℂ → ℂ}
    (hφ : IntegrableOn φ unitDiscExterior) (hc : ContinuousOn φ unitDiscExterior)
    {r : ℕ → ℝ} (hr : ∀ n, 1 ≤ r n) (ht : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => ∫ z in unitDiscExterior, ‖φ (r n • z) - φ z‖)
      atTop (𝓝 0) := by
  apply qcv_L1_tendsto_of_integral_norm_le hφ
    (fun n => (qcv_exterior_dilate_integrable hφ (hr n)).1)
    (fun n => (qcv_exterior_dilate_integrable hφ (hr n)).2)
  filter_upwards [ae_restrict_mem
    (isOpen_lt continuous_const continuous_norm).measurableSet] with z hz
  have hcz : ContinuousAt φ z := hc.continuousAt
    ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
  apply hcz.tendsto.comp
  simpa only [one_smul] using ht.smul_const z

/-- Absolutely summable Laurent tests can be paired term by term. -/
theorem qcv_pairing_eq_zero_of_summable_laurent {μ : LinfStar}
    (hμ : fderiv ℂ bersPhi 0 μ = 0) {c : ℕ → ℂ}
    (hc : Summable fun n => ‖c n‖) {φ : ℂ → ℂ}
    (hs : ∀ w ∈ unitDiscExterior,
      HasSum (fun n => c n / w ^ (n + 4)) (φ w)) :
    ∫ w in unitDiscExterior, μ w * φ w = 0 := by
  let m := volume.restrict unitDiscExterior
  have hD : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hI : Integrable (fun w : ℂ => (‖w‖ ^ 4)⁻¹) m := by
    have hi := (qcv_cauchyKernel_mem_AOneStar
      (mem_ball_self (by norm_num) : (0 : ℂ) ∈ unitDisc)).2.1.norm
    simpa [sub_zero, norm_div, norm_pow] using hi
  let G : ℕ → ℂ → ℂ := fun n w => c n * (μ w / w ^ (n + 4))
  let B : ℕ → ℂ → ℝ := fun n w => ‖c n‖ * ‖μ‖ * (‖w‖ ^ 4)⁻¹
  have hGm : ∀ n, AEStronglyMeasurable (G n) m := by
    intro n
    have hi : Measurable (fun w : ℂ => (w ^ (n + 4))⁻¹) := by fun_prop
    simpa only [G, m, div_eq_mul_inv, Pi.mul_apply] using
      ((Lp.aestronglyMeasurable μ).mul hi.aestronglyMeasurable).const_mul (c n)
  have hGb : ∀ n, ∀ᵐ w ∂m, ‖G n w‖ ≤ B n w := by
    intro n
    filter_upwards [ae_restrict_mem hD, LinfStar_ae_norm_le μ] with w hw hμw
    have hw1 : 1 < ‖w‖ := hw
    have hw0 : 0 < ‖w‖ := lt_trans zero_lt_one hw1
    dsimp [G, B]
    rw [norm_mul, norm_div, norm_pow]
    calc ‖c n‖ * (‖μ w‖ / ‖w‖ ^ (n + 4))
        ≤ ‖c n‖ * (‖μ‖ / ‖w‖ ^ (n + 4)) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hμw (by positivity)) (norm_nonneg _)
      _ ≤ ‖c n‖ * (‖μ‖ / ‖w‖ ^ 4) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hw0 4)
              (pow_le_pow_right₀ hw1.le (show 4 ≤ n + 4 by omega))) (norm_nonneg _)
      _ = _ := by ring
  have hBs : ∀ᵐ w ∂m, Summable fun n => B n w :=
    ae_of_all _ fun w => (hc.mul_right ‖μ‖).mul_right _
  have hBi : Integrable (fun w => ∑' n, B n w) m := by
    have he : (fun w => ∑' n, B n w) =
        (fun w => ((∑' n, ‖c n‖) * ‖μ‖) * (‖w‖ ^ 4)⁻¹) := by
      ext w
      simp only [B, tsum_mul_right]
    rw [he]
    exact hI.const_mul _
  have hsum : ∀ᵐ w ∂m, HasSum (fun n => G n w) (μ w * φ w) := by
    filter_upwards [ae_restrict_mem hD] with w hw
    convert (hs w hw).mul_left (μ w) using 1
    ext n
    dsimp [G]
    ring
  have hi := hasSum_integral_of_dominated_convergence B hGm hGb hBs hBi hsum
  have hzero : (fun n => ∫ w, G n w ∂m) = fun _ => (0 : ℂ) := by
    ext n
    dsimp [G, m]
    rw [integral_const_mul, qcv_ker_D0Phi_laurentMoments hμ n, mul_zero]
  rw [hzero] at hi
  exact hi.unique hasSum_zero

/-- A function holomorphic beyond the closed disk has absolutely summable Taylor coefficients. -/
theorem qcv_exists_summable_powerSeries {F : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (hF : DifferentiableOn ℂ F (ball 0 R)) :
    ∃ c : ℕ → ℂ, (Summable fun n => ‖c n‖) ∧
      ∀ u ∈ unitDisc, HasSum (fun n => c n * u ^ n) (F u) := by
  let ρ : ℝ := (1 + R) / 2
  have hρ1 : 1 < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  let ρ' : NNReal := ⟨ρ, by linarith⟩
  have hρ'pos : 0 < ρ' := by exact_mod_cast (lt_trans zero_lt_one hρ1)
  have hdc : DifferentiableOn ℂ F (closedBall 0 (ρ' : ℝ)) :=
    hF.mono (closedBall_subset_ball hρR)
  have hps := hdc.hasFPowerSeriesOnBall hρ'pos
  let p := cauchyPowerSeries F 0 (ρ' : ℝ)
  have hrad : ((1 : NNReal) : ENNReal) < p.radius := by
    refine lt_of_lt_of_le ?_ hps.r_le
    exact_mod_cast hρ1
  have hc : Summable fun n => ‖p.coeff n‖ := by
    have := p.summable_norm_mul_pow hrad
    simpa [FormalMultilinearSeries.norm_apply_eq_norm_coef] using this
  refine ⟨p.coeff, hc, ?_⟩
  intro u hu
  have hmem : u ∈ Metric.eball (0 : ℂ) ρ' := by
    rw [Metric.mem_eball, edist_zero_right]
    have : (‖u‖₊ : ℝ) < ρ := lt_trans (mem_ball_zero_iff.mp hu) hρ1
    exact_mod_cast this
  have hh := hps.hasSum hmem
  simp only [zero_add] at hh
  convert hh using 1
  ext n
  rw [p.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]

end QCV
end TakhtajanTeo
