import TakhtajanTeo.Ch1.S7GradientEnergy

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual hyperbolic Laplacian commutes with conjugation, using C2 mixed symmetry. -/
theorem s7ge_laplace_conj {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    laplace0 (fun w => conj (h w)) z = conj (laplace0 h z) := by
  have hg : dzbar (fun w => conj (h w)) =ᶠ[𝓝 z] (fun w => conj (dz h w)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact dzbar_conj ((hh.differentiableOn (by simp) w hw).differentiableAt
      (isOpen_ball.mem_nhds hw))
  have hdC : ContDiffOn ℝ (⊤ : ℕ∞) (dz h) unitDisc := wp_contDiffOn_dz hh isOpen_ball (by simp)
  have hd : DifferentiableAt ℝ (dz h) z :=
    (hdC.differentiableOn (by simp) z hz).differentiableAt
      (isOpen_ball.mem_nhds hz)
  have h2 : ContDiffAt ℝ 2 h z := (hh.of_le (by simp)).contDiffAt (isOpen_ball.mem_nhds hz)
  have hEq : dz (dzbar (fun w => conj (h w))) z = conj (dz (dzbar h) z) := by
    have he : dz (dzbar (fun w => conj (h w))) z = dz (fun w => conj (dz h w)) z := by
      simp only [dz, hg.fderiv_eq (𝕜 := ℝ)]
    rw [he, dz_conj hd, ← wp_wirtinger_comm h2]
  simp only [laplace0, hEq, map_neg, map_mul, map_inv₀, Complex.conj_ofReal]

private theorem normL2_conjugate (D : Set ℂ) (h : ℂ → ℂ) :
    normL2 D (fun z => conj (h z)) = normL2 D h := by
  unfold normL2
  congr 1
  apply lintegral_congr
  intro z
  have he : ‖conj (h z)‖₊ = ‖h z‖₊ := Subtype.ext (Complex.norm_conj _)
  rw [he]

/-- Both Wirtinger directions have true finite energy for the weighted graph domain. -/
theorem s7ge_dz_integrable {h : ℂ → ℂ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hL : normL2 unitDisc h < ∞) (hDL : normL2 unitDisc (laplace0 h) < ∞) :
    IntegrableOn (fun z => ‖dz h z‖ ^ 2) unitDisc := by
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => conj (h z)) unitDisc :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hh
  have hLc : normL2 unitDisc (fun z => conj (h z)) < ∞ := by
    rw [normL2_conjugate]
    exact hL
  have hDc : normL2 unitDisc (laplace0 (fun z => conj (h z))) < ∞ := by
    have he : laplace0 (fun z => conj (h z)) =ᵐ[volume.restrict unitDisc]
        (fun z => conj (laplace0 h z)) := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      exact s7ge_laplace_conj hh hz
    rw [grp_normL2_congr_ae he, normL2_conjugate]
    exact hDL
  have hi := s7ge_dzbar_integrable hc hLc hDc
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  rw [dzbar_conj ((hh.differentiableOn (by simp) z hz).differentiableAt
    (isOpen_ball.mem_nhds hz)), norm_conj]

end TakhtajanTeo
