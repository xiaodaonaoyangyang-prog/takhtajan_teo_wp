import TakhtajanTeo.Ch1.Eq22KernelIntegrability
import TakhtajanTeo.Ch1.Eq22BoundaryDomain
import TakhtajanTeo.Ch1.Eq22ReflectionGrowth

/-! Absolute integrability with exactly the original reflection and A2 assumptions. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- A1
theorem eq22_density_regular {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    ContinuousOn (poincareDensity Ω) Ω ∧ ∀ v ∈ Ω, 0 < poincareDensity Ω v := by
  let g := Function.invFunOn f unitDisc
  have hg : IsConformalOnto g Ω unitDisc := hf.symm isOpen_ball
  have hΩ : IsOpen Ω := hf.isOpen isOpen_ball
  have hδ : ∀ v ∈ Ω, 0 < 1-‖g v‖^2 := by
    intro v hv
    have hn := mem_ball_zero_iff.mp (hg.mapsTo hv)
    nlinarith [norm_nonneg (g v)]
  have hc : ContinuousOn (fun v => 2*‖deriv g v‖/(1-‖g v‖^2)) Ω :=
    (continuousOn_const.mul (hg.1.deriv hΩ).continuousOn.norm).div
      (continuousOn_const.sub (hg.1.continuousOn.norm.pow 2)) (fun v hv => (hδ v hv).ne')
  refine ⟨hc.congr (fun v hv => (poincareDensity_well_defined hΩ hg hg hv).2),?_⟩
  exact fun v hv => s20l_a2_density_pos hΩ hg hv

-- A2
theorem eq22_kernel_integrable {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (fsans μ '' unitDisc))
    (hq2 : ∫⁻ v in fsans μ '' unitDisc, (‖q v‖₊ : ℝ≥0∞)^2 *
      ENNReal.ofReal (poincareDensity (fsans μ '' unitDisc) v^2)⁻¹ < ∞)
    {z : ℂ} (hz : z ∈ fsans μ '' unitDisc) :
    IntegrableOn (fun u => q (h u)*(u-h u)^2*dzbar h u/(u-z)^4)
      (gsans μ '' unitDiscExterior) := by
  have hf := S2C.s2c_conf_f hμ
  have hΩ := hf.isOpen isOpen_ball
  obtain ⟨k,hk⟩ := hh.1
  have hhc : ContinuousOn h (gsans μ '' unitDiscExterior) := by
    simpa only [Function.comp_def,conj_conj] using continuous_conj.comp_continuousOn hk.2.2.1.1
  obtain ⟨hρc,hρp⟩ := eq22_density_regular hf
  obtain ⟨e,heΩ,heE⟩ := eq22_welding_common_chart hμ
  have hdis : Disjoint (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) := by
    rw [heΩ,heE]
    apply Set.disjoint_left.mpr
    rintro _ ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
    have hev : v = u := e.injective he
    subst v
    have hnu := mem_ball_zero_iff.mp hu
    change 1 < ‖u‖ at hv
    linarith
  obtain ⟨r,hr,hsep⟩ := eq22_open_separation hΩ hdis hz
  obtain ⟨C,hC,hgrowth⟩ := eq22_reflection_growth hμ hh
  have hgeom := eq22_geometry_integrable_of_growth hk.1.measurableSet hhc
    (hρc.mono (image_subset_iff.mpr hh.2.1))
    (fun u hu => (hρp (h u) (hh.2.1 hu)).le) hC.le hr hgrowth hsep
  have hmass : (∫⁻ v in fsans μ '' unitDisc,
      ENNReal.ofReal (‖q v‖^2/(poincareDensity (fsans μ '' unitDisc) v)^2)) < ∞ := by
    convert hq2 using 1
    apply setLIntegral_congr_fun hΩ.measurableSet
    intro v hv
    dsimp only
    rw [div_eq_mul_inv,ENNReal.ofReal_mul (sq_nonneg ‖q v‖),
      ENNReal.ofReal_pow (norm_nonneg (q v)),ofReal_norm,enorm_eq_nnnorm]
  exact eq22_kernel_integrable_of_geometry hk hh.2.1 hq.continuousOn hρc hρp hmass hgeom

end TakhtajanTeo
