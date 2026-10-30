import TakhtajanTeo.Ch1.ResolventPlanarGreen
import TakhtajanTeo.Ch1.ResolventUniqueness

/-! The centered resolvent reproduces arbitrary compactly supported planar tests. -/

open Real Complex Filter Set Topology MeasureTheory Metric
open scoped ComplexConjugate

noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option autoImplicit false

/-- Removing a shrinking disk does not change the limit of an absolutely
integrable planar integral. The center is discarded only as a null singleton. -/
theorem resolvent_integral_puncture_limit {f : ℂ → ℂ} {R : ℝ}
    (hf : IntegrableOn f (ball (0 : ℂ) R)) :
    Tendsto (fun r : ℝ => ∫ z in ball (0 : ℂ) R \ ball 0 r, f z)
      (𝓝[>] 0) (𝓝 (∫ z in ball (0 : ℂ) R, f z)) := by
  let F : ℝ → ℂ → ℂ := fun r => (ball (0 : ℂ) r)ᶜ.indicator f
  have hm : ∀ᶠ r : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (F r) (volume.restrict (ball (0 : ℂ) R)) :=
    Filter.Eventually.of_forall (fun r => hf.aestronglyMeasurable.indicator measurableSet_ball.compl)
  have hb : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) R)),
      ‖F r z‖ ≤ ‖f z‖ := by
    filter_upwards [] with r
    filter_upwards [] with z
    exact norm_indicator_le_norm_self _ _
  have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by rw [ae_iff]; simp
  have hl : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) R)),
      Tendsto (fun r : ℝ => F r z) (𝓝[>] 0) (𝓝 (f z)) := by
    filter_upwards [ae_restrict_of_ae hne] with z hz
    apply tendsto_const_nhds.congr'
    have hs : ∀ᶠ r : ℝ in 𝓝[>] 0, r < ‖z‖ :=
      (gt_mem_nhds (norm_pos_iff.mpr hz)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hs] with r hr
    exact (indicator_of_mem (show z ∈ (ball (0 : ℂ) r)ᶜ from
      fun h => (mem_ball_zero_iff.mp h).not_ge hr.le) f).symm
  have ht := tendsto_integral_filter_of_dominated_convergence (fun z => ‖f z‖) hm hb hf.norm hl
  have he (r : ℝ) : (∫ z, F r z ∂(volume.restrict (ball (0 : ℂ) R))) =
      ∫ z in ball (0 : ℂ) R \ ball 0 r, f z := by
    rw [show F r = (ball (0 : ℂ) r)ᶜ.indicator f from rfl,
      integral_indicator measurableSet_ball.compl, Measure.restrict_restrict measurableSet_ball.compl,
      inter_comm]
    rfl
  simpa only [he] using ht

/-- The unweighted centered kernel is integrable on each compact subdisk. -/
theorem resolvent_center_integrable_subdisk {R : ℝ} (hR : R < 1) :
    IntegrableOn (fun z => (resolventKernel 0 z : ℂ)) (ball (0 : ℂ) R) := by
  have hsub : ball (0 : ℂ) R ⊆ unitDisc := ball_subset_ball hR.le
  have hm : IntegrableOn (fun z => ((resolventKernel 0 z * rho z : ℝ) : ℂ))
      (ball (0 : ℂ) R) := (resolvent_center_disk_integrable.ofReal).mono_set hsub
  have hc : Continuous (fun z : ℂ => (((1 - ‖z‖ ^ 2) ^ 2 / 4 : ℝ) : ℂ)) := by fun_prop
  have hi := hm.mul_continuousOn_of_subset hc.continuousOn measurableSet_ball
    (isCompact_closedBall (0 : ℂ) R) ball_subset_closedBall
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have hd := resolvent_domain_denominator_ne_zero (Or.inl rfl) (hsub hz)
  push_cast
  unfold rho
  push_cast
  have hdC : (1 - ‖z‖ ^ 2 : ℂ) ≠ 0 := by exact_mod_cast hd
  field_simp

/-- Away from the source the Green bulk equals the explicit test-density expression. -/
theorem resolvent_center_green_bulk_eq {g : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    -2 * resolventGreenBulk (fun w => (resolventKernel 0 w : ℂ)) g z =
      (resolventKernel 0 z : ℂ) * ((rho z : ℂ) * g z - 2 * dz (dzbar g) z) := by
  have hp := resolventKernel_contDiffAt (Or.inl rfl) (by simp [unitDisc]) hz hz0.symm
  have hreal : ContDiffAt ℝ ⊤ (fun w : ℂ => resolventKernel 0 w) z :=
    hp.comp z (contDiffAt_const.prodMk contDiffAt_id)
  have hK : ContDiffAt ℝ 2 (fun w : ℂ => (resolventKernel 0 w : ℂ)) z :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z hreal).of_le le_top
  have hρ : (rho z : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact div_ne_zero (by norm_num)
      (pow_ne_zero 2 (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz))
  have he := resolvent_disk_laplace_equation (by simp [unitDisc]) hz hz0
  unfold laplace0 at he
  have hm : dz (dzbar (fun w => (resolventKernel 0 w : ℂ))) z =
      (rho z : ℂ) * (resolventKernel 0 z : ℂ) / 2 := by
    field_simp at he
    linear_combination -he / 2
  rw [resolventGreenBulk, ← resolvent_mixed_commute hK, hm]
  ring

/-- The explicit planar source integrand is absolutely integrable up to the center. -/
theorem resolvent_center_source_integrable {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    {R : ℝ} (hR : R < 1) :
    IntegrableOn (fun z => (resolventKernel 0 z : ℂ) *
      ((rho z : ℂ) * g z - 2 * dz (dzbar g) z)) (ball (0 : ℂ) R) := by
  have hρ : ContinuousOn (fun z : ℂ => (rho z : ℂ)) (closedBall (0 : ℂ) R) := by
    intro z hz
    have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hR)
    exact (Complex.continuous_ofReal.continuousAt.comp
      (rho_contDiffAt (resolvent_domain_denominator_ne_zero (Or.inl rfl) hzD)).continuousAt).continuousWithinAt
  have hd : Continuous (dz (dzbar g)) := continuous_dz (resolvent_contDiff_wirtinger hg).2
  exact (resolvent_center_integrable_subdisk hR).mul_continuousOn_of_subset
    ((hρ.mul hg.continuous.continuousOn).sub (continuousOn_const.mul hd.continuousOn))
    measurableSet_ball (isCompact_closedBall (0 : ℂ) R) ball_subset_closedBall

/-- The centered planar Green formula has unit point-source limit for arbitrary
C2 test functions supported strictly inside a subdisk. -/
theorem resolvent_center_planar_source_limit {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) (hs : tsupport g ⊆ ball (0 : ℂ) R) :
    Tendsto (fun r : ℝ => ∫ z in ball (0 : ℂ) R \ ball 0 r,
      (resolventKernel 0 z : ℂ) * ((rho z : ℂ) * g z - 2 * dz (dzbar g) z))
      (𝓝[>] 0) (𝓝 (g 0)) := by
  have ht := (resolvent_center_planar_boundary_limit hg).const_mul I
  have he : I * (-I * g 0) = g 0 := by
    rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
  rw [he] at ht
  apply ht.congr'
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < R :=
    (gt_mem_nhds hR0).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
  change 0 < r at hr
  have houter : (∫ θ in (0 : ℝ)..2 * π, resolventGreenBoundary
      (fun w => (resolventKernel 0 w : ℂ)) g 0 R θ) = 0 := by
    have heq (θ : ℝ) : resolventGreenBoundary
        (fun w => (resolventKernel 0 w : ℂ)) g 0 R θ = 0 := by
      apply resolventGreenBoundary_zero
      intro hθ
      have hn := mem_ball_zero_iff.mp (hs hθ)
      rw [norm_circleMap_zero, abs_of_pos hR0] at hn
      exact lt_irrefl R hn
    simp only [heq, intervalIntegral.integral_zero]
  have hgreen := resolvent_center_planar_green_annulus hg hr hrR.le hR1
  rw [houter, zero_sub] at hgreen
  have hbulk : (∫ z in ball (0 : ℂ) R \ ball 0 r,
      (resolventKernel 0 z : ℂ) * ((rho z : ℂ) * g z - 2 * dz (dzbar g) z)) =
      -2 * ∫ z in ball (0 : ℂ) R \ ball 0 r,
        resolventGreenBulk (fun w => (resolventKernel 0 w : ℂ)) g z := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
    intro z hz
    have hz0 : z ≠ 0 := by
      intro heq
      exact hz.2 (heq ▸ mem_ball_self hr)
    exact (resolvent_center_green_bulk_eq
      (ball_subset_ball hR1.le hz.1) hz0).symm
  rw [hbulk]
  symm
  calc
    _ = (-I) * ((-2 * I) * ∫ z in ball (0 : ℂ) R \ ball 0 r,
        resolventGreenBulk (fun w => (resolventKernel 0 w : ℂ)) g z) := by
      ring_nf
      rw [I_sq]
      ring
    _ = _ := by rw [← hgreen]; ring

/-- The full centered planar source identity, as an ordinary absolutely convergent
integral. This test class is not restricted to radial functions. -/
theorem resolvent_center_planar_source_integral {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) (hs : tsupport g ⊆ ball (0 : ℂ) R) :
    (∫ z in ball (0 : ℂ) R, (resolventKernel 0 z : ℂ) *
      ((rho z : ℂ) * g z - 2 * dz (dzbar g) z)) = g 0 := by
  exact tendsto_nhds_unique
    (resolvent_integral_puncture_limit (resolvent_center_source_integrable hg hR1))
    (resolvent_center_planar_source_limit hg hR0 hR1 hs)

end TakhtajanTeo
