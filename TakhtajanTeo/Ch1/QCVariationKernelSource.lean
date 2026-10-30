import TakhtajanTeo.Ch1.QCVariationDifferentialCovariance

/-! # Actual quasiconformal source transport of the general-base fourth kernel -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

/-- Change of variables for the actual first-variation coefficient and any
measurable complex kernel, including all phase and Jacobian factors. -/
theorem qcv_base_dot_kernel_source {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (ν : LinfStar) (K : ℂ → ℂ) (hK : Measurable K) :
    (∫ v, ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ) v * K v) =
      ∫ u in unitDiscExterior, ν u * K (qcv_planeSolution μ u) *
        dz (qcv_planeSolution μ) u ^ 2 := by
  have hN := (qcv_W_props (bc_norm_lt_one hμ)).1
  obtain ⟨⟨k, hk⟩, himg, _, _, hdil⟩ := hN
  have hdot := qcv_base_dot_isBeltramiCoeff hμ ν
  have hdm : AEStronglyMeasurable
      (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ)) volume := by
    simpa only [Measure.restrict_univ] using hdot.1
  rw [qcv_cov_integral hk himg
    (fun v => ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ) v * K v)
    (hdm.mul hK.aestronglyMeasurable)]
  have hJ := thm9_6_cor2_jacobian_pos hk
  rw [Measure.restrict_univ] at hJ
  have hμb := (extB_isBeltramiCoeff μ).2
  rw [Measure.restrict_univ] at hμb
  have hi : InjOn (qcv_planeSolution μ) univ := hk.2.2.1.2.1
  have he : (fun u => (ENNReal.ofReal (jacobian (qcv_planeSolution μ) u)).toReal •
      (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ) (qcv_planeSolution μ u) *
        K (qcv_planeSolution μ u))) =ᵐ[volume]
      (fun u => extB ν u * K (qcv_planeSolution μ u) * dz (qcv_planeSolution μ) u ^ 2) := by
    filter_upwards [hJ, hdil, hμb] with u hJu hdu hbu
    change 0 < jacobian (qcv_planeSolution μ) u at hJu
    have hφ : Function.invFunOn (qcv_planeSolution μ) univ (qcv_planeSolution μ u) = u :=
      hi.leftInvOn_invFunOn (mem_univ u)
    have hz : dz (qcv_planeSolution μ) u ≠ 0 := by
      intro hz0
      have hj : jacobian (qcv_planeSolution μ) u ≤ 0 := by
        unfold jacobian
        rw [hz0]
        simp
      linarith
    have hbar : dzbar (qcv_planeSolution μ) u = extB μ u * dz (qcv_planeSolution μ) u := by
      change dzbar (qcv_planeSolution μ) u / dz (qcv_planeSolution μ) u = extB μ u at hdu
      exact (div_eq_iff hz).mp hdu
    have ha : (1 : ℂ) - conj (extB μ u) * extB μ u ≠ 0 := by
      have hb : ‖conj (extB μ u) * extB μ u‖ < 1 := by
        rw [norm_mul, Complex.norm_conj]
        have hm := bc_norm_lt_one hμ
        nlinarith [norm_nonneg (extB μ u), norm_nonneg μ]
      intro heq
      have heq' : conj (extB μ u) * extB μ u = 1 := by linear_combination -heq
      rw [heq', norm_one] at hb
      exact (lt_irrefl _ hb)
    have hJc : (jacobian (qcv_planeSolution μ) u : ℂ) =
        dz (qcv_planeSolution μ) u * conj (dz (qcv_planeSolution μ) u) *
          (1 - conj (extB μ u) * extB μ u) := by
      unfold jacobian
      rw [hbar, norm_mul]
      push_cast
      rw [Complex.mul_conj, mul_comm (conj (extB μ u)) (extB μ u), Complex.mul_conj]
      simp only [Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      push_cast
      ring
    have hcz : conj (dz (qcv_planeSolution μ) u) ≠ 0 := by simpa using hz
    simp only [ahT_dot, hφ]
    rw [ENNReal.toReal_ofReal hJu.le, Complex.real_smul, hJc]
    field_simp
  change (∫ u, (ENNReal.ofReal (jacobian (qcv_planeSolution μ) u)).toReal •
    (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ) (qcv_planeSolution μ u) *
      K (qcv_planeSolution μ u))) = _
  rw [integral_congr_ae he, ← integral_indicator bc_hEo.measurableSet]
  apply integral_congr_ae
  exact ae_of_all _ fun u => by
    by_cases hu : u ∈ unitDiscExterior <;> simp [extB, hu]

/-- The fourth-order kernel in source coordinates for the actual base solution. -/
theorem qcv_base_dot_fourth_kernel_source {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (ν : LinfStar) (y : ℂ) :
    (∫ v, ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ) v / (v - y) ^ 4) =
      ∫ u in unitDiscExterior, ν u * dz (qcv_planeSolution μ) u ^ 2 /
        (qcv_planeSolution μ u - y) ^ 4 := by
  have hh := qcv_base_dot_kernel_source hμ ν (fun v => (1 : ℂ) / (v - y) ^ 4)
    (by fun_prop)
  simp only [mul_one_div] at hh
  rw [hh]
  apply integral_congr_ae
  exact ae_of_all _ fun u => by ring

end QCV
end TakhtajanTeo
