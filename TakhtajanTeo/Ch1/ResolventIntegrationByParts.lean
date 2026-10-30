import TakhtajanTeo.Ch1.ResolventDuality

/-! Integration by parts against compact tests for locally smooth disk functions. -/

open Real Complex Filter Set Topology MeasureTheory Metric
open scoped ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option autoImplicit false

theorem resolvent_mixed_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (he : f =ᶠ[𝓝 z] g) : dz (dzbar f) z = dz (dzbar g) z := by
  have hb : dzbar f =ᶠ[𝓝 z] dzbar g := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with w hw
    simp only [dzbar, hw]
  simp only [dz, hb.fderiv_eq (𝕜 := ℝ)]

/-- A locally continuous disk function times a compact continuous disk test is integrable. -/
theorem resolvent_mul_test_integrable {f ψ : ℂ → ℂ} (hf : ContinuousOn f unitDisc)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ unitDisc) :
    IntegrableOn (fun z => f z * ψ z) unitDisc := by
  have ht : Continuous (fun z => f z * ψ z) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z ∈ unitDisc
    · exact (hf.continuousAt (isOpen_ball.mem_nhds hz)).mul hψ.continuousAt
    · have hzS : z ∉ tsupport ψ := fun h => hz (hs h)
      apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzS] with w hw
      simp only [hw, Pi.zero_apply, mul_zero]
  have htc : HasCompactSupport (fun z => f z * ψ z) :=
    hc.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right
  exact (ht.integrable_of_hasCompactSupport htc).integrableOn

/-- The mixed derivative cannot enlarge topological support. -/
theorem resolvent_mixed_tsupport {g : ℂ → ℂ} : tsupport (dz (dzbar g)) ⊆ tsupport g := by
  apply closure_minimal _ (isClosed_tsupport g)
  intro z hz
  by_contra hnot
  exact hz (resolvent_mixed_zero_of_notMem_tsupport hnot)

/-- Mixed second derivatives transfer between two global C2 functions on a disk
when the test vanishes near its boundary. -/
theorem resolvent_mixed_pairing_subdisk {f φ : ℂ → ℂ}
    (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ) {R : ℝ} (hR : 0 < R)
    (hs : tsupport φ ⊆ ball (0 : ℂ) R) :
    (∫ z in ball (0 : ℂ) R, f z * dz (dzbar φ) z) =
      ∫ z in ball (0 : ℂ) R, φ z * dz (dzbar f) z := by
  have houter : (∫ θ in (0 : ℝ)..2 * π, resolventGreenBoundary f φ 0 R θ) = 0 := by
    have he (θ : ℝ) : resolventGreenBoundary f φ 0 R θ = 0 := by
      apply resolventGreenBoundary_zero
      intro hθ
      have hn := mem_ball_zero_iff.mp (hs hθ)
      rw [norm_circleMap_zero, abs_of_pos hR] at hn
      exact lt_irrefl R hn
    simp only [he, intervalIntegral.integral_zero]
  have hG := resolvent_green_disk hf hφ 0 hR.le
  rw [houter] at hG
  have hz : (∫ z in ball (0 : ℂ) R, resolventGreenBulk f φ z) = 0 :=
    (mul_eq_zero.mp hG.symm).resolve_left (by norm_num)
  have hi (u v : ℂ → ℂ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
      IntegrableOn (fun z => u z * dz (dzbar v) z) (ball (0 : ℂ) R) :=
    ((hu.continuous.mul (continuous_dz (resolvent_contDiff_wirtinger hv).2)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) R)).mono_set ball_subset_closedBall
  have he : resolventGreenBulk f φ = (fun z => f z * dz (dzbar φ) z - φ z * dz (dzbar f) z) := by
    funext z
    rw [resolventGreenBulk, ← resolvent_mixed_commute hf.contDiffAt]
  rw [he, integral_sub (hi f φ hf hφ) (hi φ f hφ hf)] at hz
  exact sub_eq_zero.mp hz

/-- Integration by parts on the whole disk only requires local C2 regularity of
the first factor. A smooth cutoff supplies its global representative. -/
theorem resolvent_mixed_pairing_disc {f φ : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 f unitDisc) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ unitDisc) :
    (∫ z in unitDisc, f z * dz (dzbar φ) z) =
      ∫ z in unitDisc, φ z * dz (dzbar f) z := by
  obtain ⟨R, hR0, hR1, hRs⟩ := resolvent_compact_subdisk hc hs
  let b : ContDiffBump (0 : ℂ) :=
    { rIn := (R + 1) / 2, rOut := (R + 3) / 4,
      rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  let ψ : ℂ → ℂ := fun z => (b z : ℂ)
  have hψ : ContDiff ℝ (2 : ℕ∞) ψ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hψD : tsupport ψ ⊆ unitDisc := by
    intro z hz
    have hb := tsupport_comp_subset (g := Complex.ofReal) (by simp) b hz
    rw [b.tsupport_eq] at hb
    have hn : ‖z‖ ≤ (R + 3) / 4 := mem_closedBall_zero_iff.mp hb
    apply mem_ball_zero_iff.mpr
    linarith
  let F : ℂ → ℂ := fun z => f z * ψ z
  have hF : ContDiff ℝ 2 F := resolvent_source_mul_contDiff isOpen_ball hψ hf hψD
  have he {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) : F =ᶠ[𝓝 z] f := by
    have hn := mem_ball_zero_iff.mp hz
    have hzB : z ∈ ball (0 : ℂ) b.rIn := mem_ball_zero_iff.mpr (by dsimp [b]; linarith)
    filter_upwards [b.eventuallyEq_one_of_mem_ball hzB] with w hw
    simp [F, ψ, hw]
  have hL : (∫ z in unitDisc, f z * dz (dzbar φ) z) =
      ∫ z in ball (0 : ℂ) R, F z * dz (dzbar φ) z := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (show MeasurableSet unitDisc from measurableSet_ball) (ball_subset_ball hR1.le)]
    · apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      change f z * dz (dzbar φ) z = F z * dz (dzbar φ) z
      rw [(he hz).self_of_nhds]
    · intro z hz
      rw [resolvent_mixed_zero_of_notMem_tsupport (fun h => hz.2 (hRs h)), mul_zero]
  have hR : (∫ z in unitDisc, φ z * dz (dzbar f) z) =
      ∫ z in ball (0 : ℂ) R, φ z * dz (dzbar F) z := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (show MeasurableSet unitDisc from measurableSet_ball) (ball_subset_ball hR1.le)]
    · apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      change φ z * dz (dzbar f) z = φ z * dz (dzbar F) z
      rw [resolvent_mixed_congr_of_eventuallyEq (he hz)]
    · intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz.2 (hRs h)), zero_mul]
  rw [hL, hR]
  exact resolvent_mixed_pairing_subdisk hF hφ hR0 hRs

end TakhtajanTeo
