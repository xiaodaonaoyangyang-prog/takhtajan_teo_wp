import TakhtajanTeo.Ch1.Eq22Reproducing

/-! Absolute integrability of the reflection kernel from quadratic growth. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- G1
theorem eq22_geometry_decay {u v z : ℂ} {ρ C r : ℝ}
    (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hr : 0 < r)
    (hg : ‖u-v‖^2*ρ ≤ C*(1+‖u‖^2)) (hsep : r ≤ ‖u-z‖) :
    ‖u-v‖^4*ρ^2/‖u-z‖^8 ≤
      (C^2*((1+‖z‖)/r+1)^8)*(1+‖u‖)^(-4 : ℝ) := by
  let N := 1+‖u‖
  let B := (1+‖z‖)/r+1
  have hN : 0 < N := by dsimp [N]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hd : 0 < ‖u-z‖ := hr.trans_le hsep
  have hn : ‖u‖ ≤ ‖u-z‖+‖z‖ := by
    simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub u z 0
  have hNB : N ≤ B*‖u-z‖ := by
    have hrat : 1 ≤ ‖u-z‖/r := (le_div_iff₀ hr).mpr (by simpa using hsep)
    calc
      N ≤ ‖u-z‖+(1+‖z‖) := by dsimp [N]; linarith
      _ ≤ ‖u-z‖+(1+‖z‖)*(‖u-z‖/r) := by nlinarith [norm_nonneg z]
      _ = B*‖u-z‖ := by dsimp [B]; ring
  have hx : ‖u-v‖^2*ρ/N^2 ≤ C := by
    apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
    calc
      ‖u-v‖^2*ρ ≤ C*(1+‖u‖^2) := hg
      _ ≤ C*N^2 := by gcongr; dsimp [N]; nlinarith [norm_nonneg u]
  have hratio : N/‖u-z‖ ≤ B := (div_le_iff₀ hd).mpr hNB
  rw [Real.rpow_neg (by positivity),show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
  change ‖u-v‖^4*ρ^2/‖u-z‖^8 ≤ C^2*B^8*(N^4)⁻¹
  calc
    ‖u-v‖^4*ρ^2/‖u-z‖^8 = (‖u-v‖^2*ρ/N^2)^2*(N/‖u-z‖)^8/N^4 := by
      field_simp
      <;> ring
    _ ≤ C^2*B^8/N^4 := by gcongr
    _ = C^2*B^8*(N^4)⁻¹ := rfl

-- G2
theorem eq22_geometry_integrable_of_growth {h : ℂ → ℂ} {ρ : ℂ → ℝ}
    {E : Set ℂ} {z : ℂ} {C r : ℝ} (hEm : MeasurableSet E)
    (hh : ContinuousOn h E) (hρ : ContinuousOn ρ (h '' E))
    (hρ0 : ∀ u ∈ E, 0 ≤ ρ (h u)) (hC : 0 ≤ C) (hr : 0 < r)
    (hg : ∀ u ∈ E, ‖u-h u‖^2*ρ (h u) ≤ C*(1+‖u‖^2))
    (hsep : ∀ u ∈ E, r ≤ ‖u-z‖) :
    (∫⁻ u in E, ENNReal.ofReal (‖u-h u‖^4*(ρ (h u))^2/‖u-z‖^8)) < ∞ := by
  let G : ℂ → ℝ := fun u => ‖u-h u‖^4*(ρ (h u))^2/‖u-z‖^8
  have hGn : ∀ u, 0 ≤ G u := fun u => by dsimp [G]; positivity
  have hGc : ContinuousOn G E := by
    apply (((continuousOn_id.sub hh).norm.pow 4).mul
      ((hρ.comp hh (fun u hu => mem_image_of_mem h hu)).pow 2)).div
      ((continuousOn_id.sub continuousOn_const).norm.pow 8)
    intro u hu
    exact pow_ne_zero _ (ne_of_gt (hr.trans_le (hsep u hu)))
  have hB : IntegrableOn (fun u : ℂ =>
      (C^2*((1+‖z‖)/r+1)^8)*(1+‖u‖)^(-4 : ℝ)) E := by
    have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 4)
      (by simp [Complex.finrank_real_complex]; norm_num)
    exact (h.const_mul _).integrableOn
  have hGi : IntegrableOn G E := hB.mono' (hGc.aestronglyMeasurable hEm) (by
    filter_upwards [ae_restrict_mem hEm] with u hu
    rw [Real.norm_eq_abs,abs_of_nonneg (hGn u)]
    exact eq22_geometry_decay (hρ0 u hu) hC hr (hg u hu) (hsep u hu))
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ hGn)).mp hGi.hasFiniteIntegral

end TakhtajanTeo
