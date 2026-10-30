import TakhtajanTeo.Ch1.S7GradientConjugate

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem s7ga_laplace_congr {f g : ℂ → ℂ} {z : ℂ} (he : f =ᶠ[𝓝 z] g) :
    laplace0 f z = laplace0 g z := by
  have hb : dzbar f =ᶠ[𝓝 z] dzbar g := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with w hw
    simp only [dzbar, hw]
  simp only [laplace0, dz, hb.fderiv_eq (𝕜 := ℝ)]

/-- The actual weighted Laplacian product rule on the open disk. -/
theorem s7ga_laplace_mul {f g : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f unitDisc)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    laplace0 (fun w => f w * g w) z = f z * laplace0 g z + g z * laplace0 f z -
      (rho z : ℂ)⁻¹ * (dz f z * dzbar g z + dzbar f z * dz g z) := by
  have hfd (w : ℂ) (hw : w ∈ unitDisc) :=
    (hf.differentiableOn (by simp) w hw).differentiableAt (isOpen_ball.mem_nhds hw)
  have hgd (w : ℂ) (hw : w ∈ unitDisc) :=
    (hg.differentiableOn (by simp) w hw).differentiableAt (isOpen_ball.mem_nhds hw)
  have hfb : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar f) unitDisc := wp_contDiffOn_dzbar hf isOpen_ball (by simp)
  have hgb : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar g) unitDisc := wp_contDiffOn_dzbar hg isOpen_ball (by simp)
  have hfbd := (hfb.differentiableOn (by simp) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
  have hgbd := (hgb.differentiableOn (by simp) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
  have he : dzbar (fun w => f w * g w) =ᶠ[𝓝 z]
      (fun w => f w * dzbar g w + g w * dzbar f w) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact dzbar_mul (hfd w hw) (hgd w hw)
  have hd : dz (dzbar (fun w => f w * g w)) z =
      dz (fun w => f w * dzbar g w + g w * dzbar f w) z := by
    simp only [dz, he.fderiv_eq (𝕜 := ℝ)]
  simp only [laplace0]
  rw [hd, wp_dz_add (f := fun w => f w * dzbar g w) (g := fun w => g w * dzbar f w)
      ((hfd z hz).mul hgbd) ((hgd z hz).mul hfbd),
    dz_mul (hfd z hz) hgbd, dz_mul (hgd z hz) hfbd]
  ring

theorem s7ga_eventually_laplace_eq (h : ℂ → ℂ) {z : ℂ} (hz : z ∈ unitDisc) :
    ∀ᶠ n : ℕ in atTop,
      laplace0 (fun w => (s7dc_cutoff n w : ℂ) * h w) z = laplace0 h z := by
  filter_upwards [s7dc_eventually_one hz] with n hn
  apply s7ga_laplace_congr
  filter_upwards [hn] with w hw
  simp only [hw, Complex.ofReal_one, one_mul]

private theorem norm_pair_sq (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have hn := mul_self_le_mul_self (norm_nonneg (a+b)) (norm_add_le a b)
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

theorem s7ga_four_sq (a b c d : ℂ) :
    ‖a+b-c-d‖^2 ≤ 4*(‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2) := by
  have h1 := norm_pair_sq a b
  have h2 := norm_pair_sq (-c) (-d)
  have h3 := norm_pair_sq (a+b) (-c+-d)
  have he : a+b-c-d = (a+b)+(-c+-d) := by ring
  rw [he]
  simp only [norm_neg] at h2
  linarith

theorem s7ga_weighted_cross {r C : ℝ} (hr : 0 < r) (u v : ℂ)
    (hb : ‖u‖^2 ≤ C*r) : ‖(r : ℂ)⁻¹*u*v‖^2*r ≤ C*‖v‖^2 := by
  calc
    _ = (‖u‖^2*‖v‖^2)/r := by
      simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, mul_pow]
      field_simp
      <;> ring
    _ ≤ _ := by
      apply (div_le_iff₀ hr).2
      have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖)
      nlinarith

theorem s7ga_cutoff_dz_norm (n : ℕ) (z : ℂ) :
    ‖dz (fun w => (s7dc_cutoff n w : ℂ)) z‖ =
      ‖dzbar (fun w => (s7dc_cutoff n w : ℂ)) z‖ := by
  have he := s7dc_radial_wirtinger ((n : ℝ)+2) Real.smoothTransition z
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _)
  change dzbar (fun w => (s7dc_cutoff n w : ℂ)) z = _ ∧
    dz (fun w => (s7dc_cutoff n w : ℂ)) z = _ at he
  rw [he.1,he.2]
  simp only [norm_mul, norm_conj]

end TakhtajanTeo
