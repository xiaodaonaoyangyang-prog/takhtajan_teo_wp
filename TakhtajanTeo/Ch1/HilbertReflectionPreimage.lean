import TakhtajanTeo.Ch1.HilbertBersKernel
import TakhtajanTeo.Ch1.Eq22Reproducing

/-! Quantitative estimates for the actual reflected coefficient.
The geometric density-product bound is explicit until proved for a chosen
reflection; no use is made of the open eq_2_3 statement. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem hbPre_reflected_sq (q h : ℂ → ℂ) (u : ℂ) :
    ‖hbPre_reflected q h u‖ ^ 2 =
      (1 / 4 : ℝ) * ‖q (h u)‖ ^ 2 * ‖u - h u‖ ^ 4 * ‖dzbar h u‖ ^ 2 := by
  norm_num [hbPre_reflected, norm_mul, norm_pow]
  ring

/-- Weighted mass of the actual reflection preimage, from QC area distortion
and the stated geometric product bound, without any smoothness assumption. -/
theorem hbPre_reflected_mass {h q : ℂ → ℂ} {E Ω : Set ℂ} {ρ₁ ρ₂ : ℂ → ℝ} {K C : ℝ}
    (hK : IsKQC (fun u => conj (h u)) E K) (hmap : MapsTo h E Ω)
    (hρ : ∀ v ∈ Ω, 0 < ρ₁ v) (hC : 0 ≤ C)
    (hgeom : ∀ u ∈ E, ‖u - h u‖ ^ 4 * ρ₁ (h u) * ρ₂ u ≤ C) :
    (∫⁻ u in E, ENNReal.ofReal (‖hbPre_reflected q h u‖ ^ 2 * ρ₂ u)) ≤
      ENNReal.ofReal (C * K / 4) *
        ∫⁻ v in Ω, ENNReal.ofReal (‖q v‖ ^ 2 / ρ₁ v) := by
  have hscalar : ∀ u ∈ E, ‖hbPre_reflected q h u‖ ^ 2 * ρ₂ u ≤
      C / 4 * (‖dzbar h u‖ ^ 2 * (‖q (h u)‖ ^ 2 / ρ₁ (h u))) := by
    intro u hu
    have hr := hρ _ (hmap hu)
    rw [hbPre_reflected_sq]
    have hh := mul_le_mul_of_nonneg_left (hgeom u hu)
      (show 0 ≤ ‖q (h u)‖ ^ 2 * ‖dzbar h u‖ ^ 2 / (4 * ρ₁ (h u)) by positivity)
    convert hh using 1 <;> field_simp <;> ring
  have hm := eq22_weighted_pullback hK hmap (fun v => ENNReal.ofReal (‖q v‖ ^ 2 / ρ₁ v))
  calc (∫⁻ u in E, ENNReal.ofReal (‖hbPre_reflected q h u‖ ^ 2 * ρ₂ u))
      ≤ ∫⁻ u in E, ENNReal.ofReal (C / 4) *
          (ENNReal.ofReal (‖dzbar h u‖ ^ 2) * ENNReal.ofReal (‖q (h u)‖ ^ 2 / ρ₁ (h u))) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hK.1.measurableSet] with u hu
        rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity : 0 ≤ C / 4)]
        exact ENNReal.ofReal_le_ofReal (hscalar u hu)
    _ = ENNReal.ofReal (C / 4) *
        ∫⁻ u in E, ENNReal.ofReal (‖dzbar h u‖ ^ 2) * ENNReal.ofReal (‖q (h u)‖ ^ 2 / ρ₁ (h u)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C / 4) * (ENNReal.ofReal K *
        ∫⁻ v in Ω, ENNReal.ofReal (‖q v‖ ^ 2 / ρ₁ v)) := by gcongr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ C / 4)]
      congr 2
      ring

/-- Exact conformal transport of the preimage's weighted L2 mass. The weight
on the image is the pulled-back hyperbolic density, not the unfilled exterior density. -/
theorem hbPre_pullback_mass {g b : ℂ → ℂ} {E V : Set ℂ} (hE : IsOpen E)
    (hg : IsConformalOnto g E V) :
    (∫⁻ w in E, ENNReal.ofReal (‖hbPre_pullback b g w‖ ^ 2) * ENNReal.ofReal (rho w)) =
      ∫⁻ u in g '' E, ENNReal.ofReal (‖b u‖ ^ 2) *
        ENNReal.ofReal (rho (Function.invFunOn g E u) * ‖deriv (Function.invFunOn g E) u‖ ^ 2) := by
  rw [r24_conformal_lintegral hE hg.1 hg.2.1]
  apply setLIntegral_congr_fun hE.measurableSet
  intro w hw
  have hd := deriv_ne_zero_of_injOn hE hg.1 hg.2.1 hw
  have hi : deriv (Function.invFunOn g E) (g w) = (deriv g w)⁻¹ :=
    eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul hE hg hw)
  dsimp only
  rw [hg.2.1.leftInvOn_invFunOn hw, hi, hbPre_pullback_norm hd, norm_inv]
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  field_simp

/-- Pointwise boundedness uses a derivative-weight bound, separately from the
density-product bound needed for the L2 estimate. -/
theorem hbPre_reflected_bound {q h : ℂ → ℂ} {E Ω : Set ℂ} {ρ : ℂ → ℝ} {M C : ℝ}
    (hmap : MapsTo h E Ω) (hM : 0 ≤ M)
    (hq : ∀ v ∈ Ω, ‖q v‖ ≤ M * ρ v)
    (hgeom : ∀ u ∈ E, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ * ρ (h u) ≤ C) :
    ∀ u ∈ E, ‖hbPre_reflected q h u‖ ≤ M * C / 2 := by
  intro u hu
  have h1 := mul_le_mul_of_nonneg_right (hq _ (hmap hu))
    (mul_nonneg (sq_nonneg ‖u - h u‖) (norm_nonneg (dzbar h u)))
  have h2 := mul_le_mul_of_nonneg_left (hgeom u hu) hM
  norm_num [hbPre_reflected, norm_mul, norm_pow]
  nlinarith

end TakhtajanTeo

#print axioms TakhtajanTeo.hbPre_reflected_mass
#print axioms TakhtajanTeo.hbPre_pullback_mass
#print axioms TakhtajanTeo.hbPre_reflected_bound
