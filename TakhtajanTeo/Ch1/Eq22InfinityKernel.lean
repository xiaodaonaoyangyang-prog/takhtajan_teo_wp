import TakhtajanTeo.Ch1.Eq22ReflectionInfinity

open Complex Set Filter Topology Bornology
namespace TakhtajanTeo
open LiZhongQC

theorem eq22_transfer_factor (u v z : ℂ) :
    1/(u-z)+(u-v)/(u-z)^2+(u-v)^2/(u-z)^3 =
      (1+(1+(z-v)/(u-z))+(1+(z-v)/(u-z))^2)/(u-z) := by
  by_cases hu : u-z = 0
  · simp [hu]
  · field_simp
    <;> ring

theorem eq22_transfer_tendsto_zero {h : ℂ → ℂ} {a : ℂ}
    (hh : Tendsto h (cocompact ℂ) (𝓝 a)) (z : ℂ) :
    Tendsto (fun u => 1/(u-z)+(u-h u)/(u-z)^2+(u-h u)^2/(u-z)^3)
      (cocompact ℂ) (𝓝 0) := by
  have hi : Tendsto (fun u : ℂ => (u-z)⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded z)
  have hb : Tendsto (fun u => (z-h u)/(u-z)) (cocompact ℂ) (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv] using (tendsto_const_nhds.sub hh).mul hi
  have h1 : Tendsto (fun u => 1+(z-h u)/(u-z)) (cocompact ℂ) (𝓝 (1 : ℂ)) := by
    simpa only [add_zero] using hb.const_add 1
  have hpoly := ((h1.const_add 1).add (h1.pow 2)).mul hi
  simp only [mul_zero] at hpoly
  convert hpoly using 1
  funext u
  rw [eq22_transfer_factor]
  rfl

theorem eq22_reflection_transfer_tendsto_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {h q : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hq : DifferentiableOn ℂ q (fsans μ '' unitDisc)) (z : ℂ) :
    Tendsto (fun u => q (h u)*(1/(u-z)+(u-h u)/(u-z)^2+(u-h u)^2/(u-z)^3))
      (cocompact ℂ) (𝓝 0) := by
  obtain ⟨a,ha,ht,_⟩ := eq22_reflection_infty_limit hμ hh
  have hΩ := (S2C.s2c_conf_f hμ).isOpen Metric.isOpen_ball
  have hqcont := hq.continuousOn.continuousAt (hΩ.mem_nhds ha)
  simpa only [Function.comp_def, mul_zero] using
    (hqcont.tendsto.comp ht).mul (eq22_transfer_tendsto_zero ht z)

end TakhtajanTeo
