import TakhtajanTeo.Ch1.ScaledMorreyFour
import TakhtajanTeo.Ch1.L4Lebesgue

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def mp_gradientMap (g h : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℝ g).comp Complex.reCLM +
    (ContinuousLinearMap.toSpanSingleton ℝ h).comp Complex.imCLM

@[simp] theorem mp_gradientMap_one (g h : ℂ) : mp_gradientMap g h 1 = g := by
  simp [mp_gradientMap, ContinuousLinearMap.toSpanSingleton_apply]

@[simp] theorem mp_gradientMap_I (g h : ℂ) : mp_gradientMap g h I = h := by
  simp [mp_gradientMap, ContinuousLinearMap.toSpanSingleton_apply]

theorem mp_normalized_radius_algebra {d : ℝ} (hd : 0 < d) (C X Y : ℝ) :
    d⁻¹ * (C * Real.sqrt (8 * d) * (X + Y)) =
      (8 * C) * (X / Real.sqrt (8 * d) + Y / Real.sqrt (8 * d)) := by
  have hs : Real.sqrt (8 * d) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hd.ne', hs]
  rw [Real.sq_sqrt (show 0 ≤ d * 8 by positivity)]
  ring

/-- A real Frechet derivative, obtained from the scaled remainder and two L4
Lebesgue-point limits. Neither ACL nor differentiability is assumed here. -/
theorem mp_hasFDerivAt_of_normalized_l4 {f g h : ℂ → ℂ}
    (hgp : HasGenPartials f g h univ 4) (z : ℂ)
    (hg : Tendsto (fun r : ℝ =>
      (eLpNorm (fun u => g u - g z) 4 (volume.restrict (closedBall z r))).toReal / Real.sqrt r)
      (𝓝[>] 0) (𝓝 0))
    (hh : Tendsto (fun r : ℝ =>
      (eLpNorm (fun u => h u - h z) 4 (volume.restrict (closedBall z r))).toReal / Real.sqrt r)
      (𝓝[>] 0) (𝓝 0)) :
    HasFDerivAt f (mp_gradientMap (g z) (h z)) z := by
  obtain ⟨C, hC, hest⟩ := mp_gen_scaled_remainder_four
  let A := mp_gradientMap (g z) (h z)
  let Q := fun y : ℂ => ‖y - z‖⁻¹ * ‖f y - f z - A (y - z)‖
  have hQz : Q z = 0 := by simp [Q]
  have hrad : Tendsto (fun y : ℂ => 8 * ‖y - z‖) (𝓝[≠] z) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun y : ℂ => 8 * ‖y - z‖) z := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hne : y ≠ z := by simpa using hy
      exact mul_pos (by norm_num) (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hupper := ((hg.comp hrad).add (hh.comp hrad)).const_mul (8 * C)
  simp only [Function.comp_def, add_zero, mul_zero] at hupper
  have hbound : ∀ᶠ y in 𝓝[≠] z, Q y ≤ (8 * C) *
      ((eLpNorm (fun u => g u - g z) 4 (volume.restrict (closedBall z (8 * ‖y - z‖)))).toReal /
        Real.sqrt (8 * ‖y - z‖) +
       (eLpNorm (fun u => h u - h z) 4 (volume.restrict (closedBall z (8 * ‖y - z‖)))).toReal /
        Real.sqrt (8 * ‖y - z‖)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hne : y ≠ z := by simpa using hy
    have hd : 0 < ‖y - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have he := hest f g h hgp A z (8 * ‖y - z‖) (by positivity) y (by linarith)
    simp only [A, mp_gradientMap_one, mp_gradientMap_I, ← Real.sqrt_eq_rpow] at he
    have hmul := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hd.le)
    change Q y ≤ _ at hmul
    rw [mp_normalized_radius_algebra hd] at hmul
    exact hmul
  have hlim : Tendsto Q (𝓝[≠] z) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun y =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hbound hupper
  have hcont : ContinuousAt Q z := continuousAt_iff_punctured_nhds.mpr (by rw [hQz]; exact hlim)
  rw [hasFDerivAt_iff_tendsto]
  change Tendsto Q (𝓝 z) (𝓝 0)
  simpa only [hQz] using hcont.tendsto

/-- In dimension two, generalized L4 partials give a true real Frechet derivative
almost everywhere, for their continuous representative. -/
theorem mp_hasGenPartials_hasFDerivAt_ae {f g h : ℂ → ℂ}
    (hgp : HasGenPartials f g h univ 4) :
    ∀ᵐ z : ℂ, HasFDerivAt f (mp_gradientMap (g z) (h z)) z := by
  have hMg : ∀ s : Set ℂ, IsCompact s → MemLp g 4 (volume.restrict s) :=
    fun s hs => (hgp.1 s (subset_univ _) hs).1
  have hMh : ∀ s : Set ℂ, IsCompact s → MemLp h 4 (volume.restrict s) :=
    fun s hs => (hgp.1 s (subset_univ _) hs).2
  filter_upwards [mp_ae_normalized_l4_lebesgue hMg, mp_ae_normalized_l4_lebesgue hMh] with z hz hz'
  exact mp_hasFDerivAt_of_normalized_l4 hgp z hz hz'

theorem mp_cauchy_hasFDerivAt_ae {κ : ℂ → ℂ} (hκ : MemLp κ 4)
    (hs : Bornology.IsBounded (Function.support κ)) :
    ∀ᵐ z : ℂ, HasFDerivAt (cauchyT κ)
      (mp_gradientMap (hilbertH κ z + κ z) (I * (hilbertH κ z - κ z))) z := by
  have hgp : HasGenPartials (cauchyT κ) (fun z => hilbertH κ z + κ z)
      (fun z => I * (hilbertH κ z - κ z)) univ 4 := by
    simpa using (thm11_1 (p := 4) (by norm_num) (by simpa using hκ) hs).1
  exact mp_hasGenPartials_hasFDerivAt_ae hgp

theorem mp_cauchy_differentiable_ae {κ : ℂ → ℂ} (hκ : MemLp κ 4)
    (hs : Bornology.IsBounded (Function.support κ)) :
    ∀ᵐ z : ℂ, DifferentiableAt ℝ (cauchyT κ) z :=
  (mp_cauchy_hasFDerivAt_ae hκ hs).mono fun _ hz => hz.differentiableAt

end TakhtajanTeo

