import TakhtajanTeo.Ch1.S7ResolventL2
import TakhtajanTeo.Ch1.Eq22WeakStokes

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Classical C1 functions on an open set have their actual generalized partials.
The constant approximating sequence supplies the definition directly. -/
theorem s7cg_genpart {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ 1 F D) :
    HasGenPartials F (fun z => fderiv ℝ F z 1) (fun z => fderiv ℝ F z I) D 2 := by
  have hd (e : ℂ) : ContinuousOn (fun z => fderiv ℝ F z e) D :=
    (hF.continuousOn_fderiv_of_isOpen hD le_rfl).clm_apply continuousOn_const
  refine ⟨?_, fun _ => F, fun _ => hF, ?_, ?_⟩
  · intro C hCD hC
    exact ⟨eq22w_cont_memLp (hd 1) hCD hC, eq22w_cont_memLp (hd I) hCD hC⟩
  · have hU : TendstoUniformlyOn (fun (_ : ℕ) => F) F atTop D := by
      intro u hu
      filter_upwards with n z hz
      exact refl_mem_uniformity hu
    exact hU.tendstoLocallyUniformlyOn
  · intro C hCD hC
    constructor <;> simp

/-- Genuine compact-support Stokes for a locally C1 function, including L1
integrability of both terms. No global smoothness of F is assumed. -/
theorem s7cg_stokes {D : Set ℂ} (hD : IsOpen D) {F χ : ℂ → ℂ}
    (hF : ContDiffOn ℝ 1 F D) (hχ : ContDiff ℝ 1 χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ D) :
    Integrable (fun z => χ z * dzbar F z) ∧
    Integrable (fun z => F z * dzbar χ z) ∧
    (∫ z, χ z * dzbar F z) = -(∫ z, F z * dzbar χ z) := by
  apply eq22w_stokes_actual hD (s7cg_genpart hD hF) _ hχ hc hs
  filter_upwards [ae_restrict_mem hD.measurableSet] with z hz
  exact (hF.differentiableOn one_ne_zero z hz).differentiableAt (hD.mem_nhds hz)

/-- The compact-test Green identity for the actual hyperbolic Laplacian.
The test has compact support inside the disk or exterior; no boundary limit
has been discarded. This is the first adjoint step of the energy argument. -/
theorem s7cg_green {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {h χ : ℂ → ℂ} (hh : ContDiffOn ℝ 2 h D) (hχ : ContDiff ℝ 1 χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ D) :
    Integrable (fun z => χ z * conj (laplace0 h z) * (rho z : ℂ)) ∧
    Integrable (fun z => dzbar χ z * conj (dzbar h z)) ∧
    (∫ z, χ z * conj (laplace0 h z) * (rho z : ℂ)) =
      ∫ z, dzbar χ z * conj (dzbar h z) := by
  have hDo := resolvent_domain_isOpen hD
  have hd : ContDiffOn ℝ 1 (dzbar h) D :=
    wp_contDiffOn_dzbar hh hDo (by norm_num)
  let F : ℂ → ℂ := fun z => conj (dzbar h z)
  have hF : ContDiffOn ℝ 1 F D :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hd
  obtain ⟨hI, hJ, he⟩ := s7cg_stokes hDo hF hχ hc hs
  have hleft : (fun z => χ z * conj (laplace0 h z) * (rho z : ℂ)) =
      (fun z => -(χ z * dzbar F z)) := by
    funext z
    by_cases hz : z ∈ D
    · have hn : ‖z‖ ≠ 1 := by
        rcases hD with rfl | rfl
        · exact ne_of_lt (by simpa [unitDisc, mem_ball, dist_zero_right] using hz : ‖z‖ < 1)
        · exact ne_of_gt hz
      have hr : (rho z : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (rho_pos_of_norm_ne_one hn).ne'
      have hdiff : DifferentiableAt ℝ (dzbar h) z :=
        (hd.differentiableOn one_ne_zero z hz).differentiableAt (hDo.mem_nhds hz)
      dsimp only [F]
      rw [dzbar_conj hdiff]
      simp only [laplace0, map_neg, map_mul, map_inv₀, Complex.conj_ofReal]
      field_simp
    · have hzero : χ z = 0 := image_eq_zero_of_notMem_tsupport (fun hzs => hz (hs hzs))
      simp only [hzero, zero_mul, neg_zero]
  have hright : (fun z => F z * dzbar χ z) =
      (fun z => dzbar χ z * conj (dzbar h z)) := by
    funext z
    exact mul_comm _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact hI.neg
  · rw [← hright]
    exact hJ
  · rw [hleft, integral_neg, he, neg_neg, hright]

end TakhtajanTeo
