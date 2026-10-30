import TakhtajanTeo.Ch1.ResolventPlanarSource

/-! Compact test functions and transport of the planar resolvent source. -/

open Real Complex Filter Set Topology MeasureTheory Metric
open scoped ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option autoImplicit false

/-- A compact subset of the open disk lies in a strictly smaller concentric disk. -/
theorem resolvent_compact_subdisk {K : Set ℂ} (hK : IsCompact K) (hs : K ⊆ unitDisc) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧ K ⊆ ball (0 : ℂ) R := by
  by_cases hn : K.Nonempty
  · obtain ⟨z, hz, hm⟩ := hK.exists_isMaxOn hn continuous_norm.continuousOn
    have hz1 := mem_ball_zero_iff.mp (hs hz)
    refine ⟨(‖z‖ + 1) / 2, by positivity, by linarith, ?_⟩
    intro w hw
    apply mem_ball_zero_iff.mpr
    have hle := hm hw
    change ‖w‖ ≤ ‖z‖ at hle
    linarith
  · exact ⟨1 / 2, by norm_num, by norm_num, by simpa [Set.not_nonempty_iff_eq_empty.mp hn]⟩

/-- The second mixed derivative vanishes off the topological support. -/
theorem resolvent_mixed_zero_of_notMem_tsupport {g : ℂ → ℂ} {z : ℂ}
    (hz : z ∉ tsupport g) : dz (dzbar g) z = 0 := by
  have he : g =ᶠ[𝓝 z] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hz
  have hb : dzbar g =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with w hw
    simp [dzbar, hw]
  simp [dz, hb.fderiv_eq (𝕜 := ℝ)]

/-- The centered Green identity over the whole disk. -/
theorem resolvent_center_source_disc {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ unitDisc) :
    (∫ z in unitDisc, (resolventKernel 0 z : ℂ) *
      ((rho z : ℂ) * g z - 2 * dz (dzbar g) z)) = g 0 := by
  obtain ⟨R, hR0, hR1, hRs⟩ := resolvent_compact_subdisk hc hs
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (show MeasurableSet unitDisc from measurableSet_ball) (ball_subset_ball hR1.le)]
  · exact resolvent_center_planar_source_integral hg hR0 hR1 hRs
  · intro z hz
    have hzg : z ∉ tsupport g := fun h => hz.2 (hRs h)
    simp [image_eq_zero_of_notMem_tsupport hzg, resolvent_mixed_zero_of_notMem_tsupport hzg]

/-- The same centered identity in the normalization of the original resolvent. -/
theorem resolvent_center_test_inverse {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ unitDisc) :
    (∫ z in unitDisc, (resolventKernel 0 z : ℂ) * (2 * laplace0 g z + g z) * rho z) = g 0 := by
  rw [← resolvent_center_source_disc hg hc hs]
  apply setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball)
  intro z hz
  have hρ : (rho z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (div_ne_zero (by norm_num)
      (pow_ne_zero 2 (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz)))
  unfold laplace0
  field_simp
  <;> ring

/-- A disk automorphism pulls a compactly supported C2 test back to a global C2
compact test, after a harmless cutoff outside its disk support. -/
theorem exists_resolvent_blaschke_test {a : ℂ} (ha : a ∈ unitDisc)
    {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ unitDisc) :
    ∃ h : ℂ → ℂ, ContDiff ℝ 2 h ∧ HasCompactSupport h ∧ tsupport h ⊆ unitDisc ∧
      EqOn h (g ∘ blaschke (-a)) unitDisc := by
  have han := mem_ball_zero_iff.mp ha
  have hneg : ‖-a‖ < 1 := by simpa using han
  let K := blaschke a '' tsupport g
  have hK : IsCompact K := hc.image_of_continuousOn
    ((differentiableOn_blaschke han).continuousOn.mono hs)
  have hKD : K ⊆ unitDisc := by
    rintro w ⟨z, hz, rfl⟩
    exact mem_ball_zero_iff.mpr (blaschke_mem_unitDisc han (mem_ball_zero_iff.mp (hs hz)))
  obtain ⟨R, hR0, hR1, hKR⟩ := resolvent_compact_subdisk hK hKD
  let b : ContDiffBump (0 : ℂ) :=
    { rIn := R, rOut := (R + 1) / 2, rIn_pos := hR0, rIn_lt_rOut := by linarith }
  let ψ : ℂ → ℂ := fun z => (b z : ℂ)
  have hψ : ContDiff ℝ (2 : ℕ∞) ψ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hψs : tsupport ψ ⊆ tsupport b := tsupport_comp_subset (g := Complex.ofReal) (by simp) b
  have hψD : tsupport ψ ⊆ unitDisc := by
    intro z hz
    have hn := hψs hz
    rw [b.tsupport_eq] at hn
    have hn' : ‖z‖ ≤ (R + 1) / 2 := mem_closedBall_zero_iff.mp hn
    apply mem_ball_zero_iff.mpr
    linarith
  have hφ : ContDiffOn ℝ (2 : ℕ∞) (blaschke (-a)) unitDisc := by
    intro z hz
    have hanal := (differentiableOn_blaschke hneg).analyticAt (isOpen_ball.mem_nhds hz)
    exact (hanal.restrictScalars (𝕜 := ℝ)).contDiffAt.contDiffWithinAt
  let h : ℂ → ℂ := fun z => g (blaschke (-a) z) * ψ z
  have hhc : ContDiff ℝ 2 h :=
    resolvent_source_mul_contDiff isOpen_ball hψ (hg.comp_contDiffOn hφ) hψD
  have hhS : tsupport h ⊆ tsupport ψ := tsupport_mul_subset_right
  have hhC : HasCompactSupport h :=
    (b.hasCompactSupport.of_isClosed_subset (isClosed_tsupport ψ) hψs).of_isClosed_subset
      (isClosed_tsupport h) hhS
  refine ⟨h, hhc, hhC, hhS.trans hψD, ?_⟩
  intro z hz
  by_cases hv : g (blaschke (-a) z) = 0
  · simp [h, hv, Function.comp_apply]
  · have hvS : blaschke (-a) z ∈ tsupport g := subset_tsupport _ (by simpa using hv)
    have hzK : z ∈ K := ⟨blaschke (-a) z, hvS,
      blaschke_blaschke_neg han (mem_ball_zero_iff.mp hz)⟩
    have hbone : b z = 1 := b.one_of_mem_closedBall (ball_subset_closedBall (hKR hzK))
    simp [h, ψ, hbone, Function.comp_apply]

/-- The original hyperbolic test operator commutes with disk automorphism pullback,
including any global representative that agrees locally on the disk. -/
theorem resolvent_blaschke_test_laplace {a : ℂ} (ha : a ∈ unitDisc)
    {g h : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    (he : EqOn h (g ∘ blaschke (-a)) unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    laplace0 h z = laplace0 g (blaschke (-a) z) := by
  have han : ‖-a‖ < 1 := by simpa using mem_ball_zero_iff.mp ha
  have hf := isConformalOnto_blaschke han
  have hm : MapsTo (blaschke (-a)) unitDisc unitDisc := by
    intro w hw
    exact mem_ball_zero_iff.mpr (blaschke_mem_unitDisc han (mem_ball_zero_iff.mp hw))
  have heq : h =ᶠ[𝓝 z] (g ∘ blaschke (-a)) := by
    filter_upwards [(show IsOpen unitDisc from isOpen_ball).mem_nhds hz] with w hw
    exact he hw
  rw [laplace0_congr_of_eventuallyEq heq]
  exact laplace0_comp_of_density_pullback isOpen_ball isOpen_ball hf.1 hm hg.contDiffOn hz
    (div_ne_zero (by norm_num)
      (pow_ne_zero 2 (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz)))
    (rho_blaschke_jacobian han (mem_ball_zero_iff.mp hz))

/-- The disk resolvent reproduces a compact C2 test after applying the normalized
hyperbolic test operator, at every point of the disk. -/
theorem resolvent_disc_test_inverse {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ unitDisc) {a : ℂ} (ha : a ∈ unitDisc) :
    (∫ z in unitDisc, (resolventKernel a z : ℂ) * (2 * laplace0 g z + g z) * rho z) = g a := by
  obtain ⟨h, hh, hhC, hhD, he⟩ := exists_resolvent_blaschke_test ha hg hc hs
  have han := mem_ball_zero_iff.mp ha
  have hneg : ‖-a‖ < 1 := by simpa using han
  have hf := isConformalOnto_blaschke hneg
  have hi := ahP_integral_image (U := unitDisc) isOpen_ball hf.1 hf.2.1
    (fun z => (resolventKernel a z : ℂ) * (2 * laplace0 g z + g z) * rho z)
  rw [hf.2.2] at hi
  rw [hi]
  calc
    _ = ∫ z in unitDisc, (resolventKernel 0 z : ℂ) * (2 * laplace0 h z + h z) * rho z := by
      apply setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball)
      intro z hz
      have hzn := mem_ball_zero_iff.mp hz
      have hφz := blaschke_mem_unitDisc hneg hzn
      have hker : resolventKernel a (blaschke (-a) z) = resolventKernel 0 z := by
        rw [← resolventKernel_blaschke_center han hφz, blaschke_blaschke_neg han hzn]
      have hL := resolvent_blaschke_test_laplace ha hg he hz
      have hval := he hz
      change h z = g (blaschke (-a) z) at hval
      have hρ := rho_blaschke_jacobian hneg hzn
      calc
        _ = (resolventKernel 0 z : ℂ) * (2 * laplace0 h z + h z) *
            ((rho (blaschke (-a) z) : ℂ) * ((‖deriv (blaschke (-a)) z‖ ^ 2 : ℝ) : ℂ)) := by
          simp only [Complex.real_smul]
          rw [hker, hL, hval]
          ring
        _ = _ := by rw [← Complex.ofReal_mul, hρ]
    _ = h 0 := resolvent_center_test_inverse hh hhC hhD
    _ = g a := by simpa [Function.comp_apply, blaschke] using he (x := 0) (by simp [unitDisc])

/-- The normalized test operator is continuous for global C2 tests, including
the totalized values on the unit circle. -/
theorem resolvent_test_operator_continuous {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g) :
    Continuous (fun z => 2 * laplace0 g z + g z) := by
  have hd : Continuous (dz (dzbar g)) := continuous_dz (resolvent_contDiff_wirtinger hg).2
  have hr : Continuous (fun z : ℂ => (rho z : ℂ)⁻¹) := by
    have he : (fun z : ℂ => (rho z : ℂ)⁻¹) =
        (fun z : ℂ => (((1 - ‖z‖ ^ 2) ^ 2 / 4 : ℝ) : ℂ)) := by
      funext z
      simp [rho, inv_div]
    rw [he]
    fun_prop
  exact (continuous_const.mul (hr.mul hd).neg).add hg.continuous

/-- Applying the normalized test operator does not enlarge topological support. -/
theorem resolvent_test_operator_tsupport {g : ℂ → ℂ} :
    tsupport (fun z => 2 * laplace0 g z + g z) ⊆ tsupport g := by
  apply closure_minimal _ (isClosed_tsupport g)
  intro z hz
  by_contra hnot
  have hv : 2 * laplace0 g z + g z = 0 := by
    simp [laplace0, resolvent_mixed_zero_of_notMem_tsupport hnot,
      image_eq_zero_of_notMem_tsupport hnot]
  exact hz hv

/-- Absolute convergence of the transported compact-test identity at any disk point. -/
theorem resolvent_disc_test_inverse_integrable {g : ℂ → ℂ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) {a : ℂ} (ha : a ∈ unitDisc) :
    IntegrableOn (fun z => (resolventKernel a z : ℂ) *
      (2 * laplace0 g z + g z) * rho z) unitDisc := by
  have ht := resolvent_test_operator_continuous hg
  have htc : HasCompactSupport (fun z => 2 * laplace0 g z + g z) :=
    hc.of_isClosed_subset (isClosed_tsupport _) resolvent_test_operator_tsupport
  obtain ⟨C, hC⟩ := ht.bounded_above_of_compact_support htc
  exact resolvent_integrand_integrable_of_bounded (Or.inl rfl)
    ht.aestronglyMeasurable (fun z _ => hC z) ha

end TakhtajanTeo
