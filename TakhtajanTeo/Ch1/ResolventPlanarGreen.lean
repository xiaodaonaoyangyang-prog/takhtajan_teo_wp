import TakhtajanTeo.Ch1.ResolventSmoothness
import TakhtajanTeo.Ch1.ResolventKernelEquation

/-! Bilinear planar Green identities for the resolvent source argument. -/

open Real Complex Filter Set Topology MeasureTheory Metric
open scoped ComplexConjugate

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

set_option autoImplicit false

/-- C2 functions have C1 Wirtinger derivatives on an open domain. -/
theorem resolvent_contDiffOn_wirtinger {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ 2 f U) :
    ContDiffOn ℝ 1 (dz f) U ∧ ContDiffOn ℝ 1 (dzbar f) U := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  have h1 := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hI := hd.clm_apply (contDiffOn_const (c := I))
  exact ⟨(h1.sub (contDiffOn_const.mul hI)).div_const 2,
    (h1.add (contDiffOn_const.mul hI)).div_const 2⟩

theorem resolvent_contDiff_wirtinger {f : ℂ → ℂ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (dz f) ∧ ContDiff ℝ 1 (dzbar f) := by
  obtain ⟨hz, hb⟩ := resolvent_contDiffOn_wirtinger isOpen_univ hf.contDiffOn
  exact ⟨contDiffOn_univ.mp hz, contDiffOn_univ.mp hb⟩

/-- The mixed bulk expression, before any commutation of second derivatives. -/
def resolventGreenBulk (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * dz (dzbar g) z - g z * dzbar (dz f) z

/-- The oriented sum of the two boundary one-forms. -/
def resolventGreenBoundary (f g : ℂ → ℂ) (c : ℂ) (R θ : ℝ) : ℂ :=
  (f (circleMap c R θ) * dzbar g (circleMap c R θ)) * conj (deriv (circleMap c R) θ) +
    deriv (circleMap c R) θ * (g (circleMap c R θ) * dz f (circleMap c R θ))

private theorem green_bulk_eq_derivatives {f g : ℂ → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (z : ℂ) :
    resolventGreenBulk f g z =
      dz (fun w => f w * dzbar g w) z - dzbar (fun w => g w * dz f w) z := by
  obtain ⟨hfz, hfb⟩ := resolvent_contDiff_wirtinger hf
  obtain ⟨hgz, hgb⟩ := resolvent_contDiff_wirtinger hg
  rw [dz_mul (hf.differentiable (by norm_num)).differentiableAt
      (hgb.differentiable one_ne_zero).differentiableAt,
    dzbar_mul (hg.differentiable (by norm_num)).differentiableAt
      (hfz.differentiable one_ne_zero).differentiableAt]
  unfold resolventGreenBulk
  ring

theorem resolventGreenBulk_continuous {f g : ℂ → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) : Continuous (resolventGreenBulk f g) := by
  obtain ⟨hfz, hfb⟩ := resolvent_contDiff_wirtinger hf
  obtain ⟨hgz, hgb⟩ := resolvent_contDiff_wirtinger hg
  exact (hf.continuous.mul (continuous_dz hgb)).sub (hg.continuous.mul (continuous_dzbar hfz))

/-- Bilinear Green identity on a disk, from the two existing first-order Green formulas. -/
theorem resolvent_green_disk {f g : ℂ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ θ in (0 : ℝ)..2 * π, resolventGreenBoundary f g c R θ) =
      (-2 * I : ℂ) * ∫ z in ball c R, resolventGreenBulk f g z := by
  obtain ⟨hfz, hfb⟩ := resolvent_contDiff_wirtinger hf
  obtain ⟨hgz, hgb⟩ := resolvent_contDiff_wirtinger hg
  have hu : ContDiff ℝ 1 (fun w => f w * dzbar g w) := (hf.of_le (by norm_num)).mul hgb
  have hv : ContDiff ℝ 1 (fun w => g w * dz f w) := (hg.of_le (by norm_num)).mul hfz
  have hGu := green_disc_dz hu c hR
  have hGv := green_disc_dzbar hv c hR
  rw [circleIntegral] at hGv
  simp only [smul_eq_mul] at hGv
  have hcirc : Continuous (circleMap c R) := continuous_circleMap c R
  have hder : Continuous (deriv (circleMap c R)) := by
    have he : deriv (circleMap c R) = (fun θ => circleMap 0 R θ * I) := by
      funext θ
      rw [deriv_circleMap]
    rw [he]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hbu : Continuous (fun θ => (f (circleMap c R θ) * dzbar g (circleMap c R θ)) *
      conj (deriv (circleMap c R) θ)) :=
    (hu.continuous.comp hcirc).mul (Complex.continuous_conj.comp hder)
  have hbv : Continuous (fun θ => deriv (circleMap c R) θ *
      (g (circleMap c R θ) * dz f (circleMap c R θ))) := hder.mul (hv.continuous.comp hcirc)
  have hiu : IntegrableOn (dz (fun w => f w * dzbar g w)) (ball c R) :=
    ((continuous_dz hu).continuousOn.integrableOn_compact (isCompact_closedBall c R)).mono_set
      ball_subset_closedBall
  have hiv : IntegrableOn (dzbar (fun w => g w * dz f w)) (ball c R) :=
    ((continuous_dzbar hv).continuousOn.integrableOn_compact (isCompact_closedBall c R)).mono_set
      ball_subset_closedBall
  have hbulk : (∫ z in ball c R, resolventGreenBulk f g z) =
      (∫ z in ball c R, dz (fun w => f w * dzbar g w) z) -
        ∫ z in ball c R, dzbar (fun w => g w * dz f w) z := by
    simp_rw [green_bulk_eq_derivatives hf hg]
    exact integral_sub hiu hiv
  unfold resolventGreenBoundary
  rw [intervalIntegral.integral_add (hbu.intervalIntegrable _ _) (hbv.intervalIntegrable _ _),
    hGu, hGv, hbulk]
  ring

/-- The bilinear Green identity on a concentric annulus. This theorem does not
silently assume differentiability of a singular kernel at the inner center. -/
theorem resolvent_green_annulus {f g : ℂ → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    (∫ θ in (0 : ℝ)..2 * π, resolventGreenBoundary f g c R θ) -
      (∫ θ in (0 : ℝ)..2 * π, resolventGreenBoundary f g c r θ) =
      (-2 * I : ℂ) * ∫ z in ball c R \ ball c r, resolventGreenBulk f g z := by
  have hi : IntegrableOn (resolventGreenBulk f g) (ball c R) :=
    ((resolventGreenBulk_continuous hf hg).continuousOn.integrableOn_compact
      (isCompact_closedBall c R)).mono_set ball_subset_closedBall
  rw [resolvent_green_disk hf hg c (hr.trans hrR), resolvent_green_disk hf hg c hr,
    setIntegral_sdiff measurableSet_ball hi (ball_subset_ball hrR)]
  ring

/-- A globally smooth representative agrees with the singular centered kernel on
a neighborhood of every point of a prescribed closed annulus. -/
theorem exists_resolvent_smooth_center_cutoff {r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) (hR : R < 1) :
    ∃ F : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
      F =ᶠ[𝓝 z] (fun w => (resolventKernel 0 w : ℂ)) := by
  let inner : ContDiffBump (0 : ℂ) :=
    { rIn := r / 4, rOut := r / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let outer : ContDiffBump (0 : ℂ) :=
    { rIn := (R + 1) / 2, rOut := (R + 3) / 4,
      rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  let ψ : ℂ → ℂ := fun w => ((outer w * (1 - inner w) : ℝ) : ℂ)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    Complex.ofRealCLM.contDiff.comp (outer.contDiff.mul (contDiff_const.sub inner.contDiff))
  have hsO : tsupport ψ ⊆ tsupport outer := by
    exact (tsupport_comp_subset (g := Complex.ofReal) (by simp)
      (fun w => outer w * (1 - inner w))).trans tsupport_mul_subset_left
  have hsD : tsupport ψ ⊆ unitDisc := by
    intro w hw
    have hwO := hsO hw
    rw [outer.tsupport_eq] at hwO
    have hwn : ‖w‖ ≤ (R + 3) / 4 := mem_closedBall_zero_iff.mp hwO
    apply mem_ball_zero_iff.mpr
    linarith
  have hs0 : (0 : ℂ) ∉ tsupport ψ := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [inner.eventuallyEq_one_of_mem_ball (mem_ball_self inner.rIn_pos)] with w hw
    simp [ψ, hw]
  have hs : tsupport ψ ⊆ unitDisc \ {0} := by
    intro w hw
    refine ⟨hsD hw, ?_⟩
    change w ≠ 0
    intro he
    exact hs0 (he ▸ hw)
  have hK : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (resolventKernel 0 w : ℂ)) (unitDisc \ {0}) := by
    intro w hw
    have hw0 : w ≠ 0 := hw.2
    have hp := resolventKernel_contDiffAt (Or.inl rfl) (by simp [unitDisc]) hw.1 hw0.symm
    have hreal : ContDiffAt ℝ ⊤ (fun v : ℂ => resolventKernel 0 v) w :=
      hp.comp w (contDiffAt_const.prodMk contDiffAt_id)
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp w hreal).of_le le_top).contDiffWithinAt
  let F : ℂ → ℂ := fun w => (resolventKernel 0 w : ℂ) * ψ w
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    resolvent_source_mul_contDiff ((show IsOpen unitDisc from isOpen_ball).sdiff isClosed_singleton)
      hψ hK hs
  refine ⟨F, hF, ?_⟩
  intro z hzr hzR
  have hi : inner.rOut < ‖z‖ := by dsimp [inner]; linarith
  have ho : ‖z‖ < outer.rIn := by dsimp [outer]; linarith
  have hni : ∀ᶠ w : ℂ in 𝓝 z, inner.rOut < ‖w‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hi
  have hno : ∀ᶠ w : ℂ in 𝓝 z, ‖w‖ < outer.rIn :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds ho
  filter_upwards [hni, hno] with w hwi hwo
  have hinner : inner w = 0 := inner.zero_of_le_dist (by simpa only [dist_zero_right] using hwi.le)
  have houter : outer w = 1 := outer.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hwo.le)
  simp [F, ψ, hinner, houter]

private theorem green_bulk_congr_left {f f' g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] f') :
    resolventGreenBulk f g z = resolventGreenBulk f' g z := by
  have hd : dz f =ᶠ[𝓝 z] dz f' := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with w hw
    simp only [dz, hw]
  simp only [resolventGreenBulk, h.self_of_nhds, dzbar, hd.fderiv_eq (𝕜 := ℝ)]

private theorem green_boundary_congr_left {f f' g : ℂ → ℂ} {c : ℂ} {r θ : ℝ}
    (h : f =ᶠ[𝓝 (circleMap c r θ)] f') :
    resolventGreenBoundary f g c r θ = resolventGreenBoundary f' g c r θ := by
  simp only [resolventGreenBoundary, h.self_of_nhds, dz, h.fderiv_eq (𝕜 := ℝ)]

/-- A genuine planar Green identity for the singular centered kernel on an annulus.
The proof uses a smooth representative equal to the kernel near the entire annulus. -/
theorem resolvent_center_planar_green_annulus {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hR : R < 1) :
    (∫ θ in (0 : ℝ)..2 * π, resolventGreenBoundary
      (fun w => (resolventKernel 0 w : ℂ)) g 0 R θ) -
      (∫ θ in (0 : ℝ)..2 * π, resolventGreenBoundary
        (fun w => (resolventKernel 0 w : ℂ)) g 0 r θ) =
      (-2 * I : ℂ) * ∫ z in ball (0 : ℂ) R \ ball 0 r,
        resolventGreenBulk (fun w => (resolventKernel 0 w : ℂ)) g z := by
  obtain ⟨F, hF, heq⟩ := exists_resolvent_smooth_center_cutoff hr hrR hR
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hcircle {s : ℝ} (hrs : r ≤ s) (hsR : s ≤ R) (θ : ℝ) :
      resolventGreenBoundary F g 0 s θ =
        resolventGreenBoundary (fun w => (resolventKernel 0 w : ℂ)) g 0 s θ := by
    have hs : 0 < s := hr.trans_le hrs
    apply green_boundary_congr_left
    apply heq
    · simpa only [norm_circleMap_zero, abs_of_pos hs] using hrs
    · simpa only [norm_circleMap_zero, abs_of_pos hs] using hsR
  have hBR := intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := 2 * π)
    (fun θ _ => hcircle hrR le_rfl θ)
  have hBr := intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := 2 * π)
    (fun θ _ => hcircle le_rfl hrR θ)
  have hbulk : (∫ z in ball (0 : ℂ) R \ ball 0 r, resolventGreenBulk F g z) =
      ∫ z in ball (0 : ℂ) R \ ball 0 r,
        resolventGreenBulk (fun w => (resolventKernel 0 w : ℂ)) g z := by
    apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
    intro z hz
    apply green_bulk_congr_left
    apply heq
    · exact le_of_not_gt (fun h => hz.2 (mem_ball_zero_iff.mpr h))
    · exact (mem_ball_zero_iff.mp hz.1).le
  rw [← hBR, ← hBr, resolvent_green_annulus hF2 hg 0 hr.le hrR, hbulk]

/-- A compact test function contributes no boundary term outside its topological support. -/
theorem resolventGreenBoundary_zero {f g : ℂ → ℂ} {c : ℂ} {r θ : ℝ}
    (hg : circleMap c r θ ∉ tsupport g) : resolventGreenBoundary f g c r θ = 0 := by
  simp [resolventGreenBoundary, image_eq_zero_of_notMem_tsupport hg,
    dzbar, fderiv_of_notMem_tsupport ℝ hg]

/-- The inner-circle Green term separates into a vanishing gradient term and
the radial flux multiplied by the angular mean of the arbitrary test function. -/
theorem resolvent_center_planar_boundary_eq {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    (∫ θ in (0 : ℝ)..2 * π, resolventGreenBoundary
      (fun w => (resolventKernel 0 w : ℂ)) g 0 r θ) =
      (-I) * ((r * resolventKernel 0 (r : ℂ) : ℝ) : ℂ) *
        (∫ θ in (0 : ℝ)..2 * π, conj (circleMap 0 1 θ) * dzbar g (circleMap 0 r θ)) +
      (I / 2) * ((r * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) r : ℝ) : ℂ) *
        (∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 r θ)) := by
  have hd := (resolvent_contDiff_wirtinger hg).2.continuous
  have hA : Continuous (fun θ : ℝ => conj (circleMap 0 1 θ) * dzbar g (circleMap 0 r θ)) :=
    (continuous_conj.comp (continuous_circleMap 0 1)).mul (hd.comp (continuous_circleMap 0 r))
  have hB : Continuous (fun θ : ℝ => g (circleMap 0 r θ)) :=
    hg.continuous.comp (continuous_circleMap 0 r)
  have hp (θ : ℝ) : resolventGreenBoundary
      (fun w => (resolventKernel 0 w : ℂ)) g 0 r θ =
      ((-I) * ((r * resolventKernel 0 (r : ℂ) : ℝ) : ℂ)) *
        (conj (circleMap 0 1 θ) * dzbar g (circleMap 0 r θ)) +
      ((I / 2) * ((r * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) r : ℝ) : ℂ)) *
        g (circleMap 0 r θ) := by
    have hn := resolvent_center_circle_normal hr θ
    have hc : conj (deriv (circleMap 0 r) θ) =
        -I * (r : ℂ) * conj (circleMap 0 1 θ) := by
      rw [deriv_circleMap]
      simp [circleMap, map_mul, map_add]
      <;> ring
    unfold resolventGreenBoundary
    dsimp only
    rw [resolvent_center_circle_value, hc]
    have hlast : deriv (circleMap 0 r) θ *
        (g (circleMap 0 r θ) * dz (fun w => (resolventKernel 0 w : ℂ)) (circleMap 0 r θ)) =
        ((I / 2) * ((r * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) r : ℝ) : ℂ)) *
          g (circleMap 0 r θ) := by rw [← hn]; ring
    rw [hlast]
    push_cast
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_add
    ((hA.const_mul ((-I) * ((r * resolventKernel 0 (r : ℂ) : ℝ) : ℂ))).intervalIntegrable _ _)
    ((hB.const_mul ((I / 2) * ((r * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) r : ℝ) : ℂ))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- The full planar inner-boundary limit for an arbitrary C2 test function.
No radiality of the test function is assumed. -/
theorem resolvent_center_planar_boundary_limit {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g) :
    Tendsto (fun r : ℝ => ∫ θ in (0 : ℝ)..2 * π, resolventGreenBoundary
      (fun w => (resolventKernel 0 w : ℂ)) g 0 r θ)
      (𝓝[>] 0) (𝓝 (-I * g 0)) := by
  let A : ℝ → ℂ := fun r => ∫ θ in (0 : ℝ)..2 * π,
    conj (circleMap 0 1 θ) * dzbar g (circleMap 0 r θ)
  let B : ℝ → ℂ := fun r => ∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 r θ)
  have hd := (resolvent_contDiff_wirtinger hg).2.continuous
  have hA : Continuous A :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      ((continuous_conj.comp ((continuous_circleMap 0 1).comp continuous_snd)).mul
        (hd.comp (continuous_circleMap_uncurry 0))) 0 (2 * π)
  have hB : Continuous B :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ : ℝ => g (circleMap 0 r θ))
      (hg.continuous.comp (continuous_circleMap_uncurry 0)) 0 (2 * π)
  have hB0 : B 0 = (2 * π : ℂ) * g 0 := by simp [B, circleMap, smul_eq_mul]
  have hH := (Complex.continuous_ofReal.tendsto 0).comp resolvent_center_radius_mul_tendsto_zero
  have hF := (Complex.continuous_ofReal.tendsto (-(1 / π))).comp resolvent_center_radial_flux
  have ht := ((hH.const_mul (-I)).mul
    (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).add
      ((hF.const_mul (I / 2)).mul (hB.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  have he : (-I) * (0 : ℂ) * A 0 + (I / 2) * ((-(1 / π) : ℝ) : ℂ) * B 0 = -I * g 0 := by
    rw [hB0]
    push_cast
    field_simp
    <;> ring
  rw [Complex.ofReal_zero, he] at ht
  apply ht.congr'
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hr1
  exact (resolvent_center_planar_boundary_eq hg ⟨hr, hr1⟩).symm

end TakhtajanTeo
