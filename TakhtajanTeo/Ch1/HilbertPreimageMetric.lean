import TakhtajanTeo.Ch1.HilbertReflectionProduct
import TakhtajanTeo.Ch1.HilbertReflectionPreimage

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The filled exterior density is precisely the metric transported by g.
The reciprocal chart includes its removable value at infinity. -/
theorem hbSurj_exterior_density {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {u : ℂ} (hu : u ∈ gsans μ '' unitDiscExterior) :
    poincareDensityNearInfty (gsans μ '' unitDiscExterior) u ^ 2 =
      rho (Function.invFunOn (gsans μ) unitDiscExterior u) *
        ‖deriv (Function.invFunOn (gsans μ) unitDiscExterior) u‖ ^ 2 := by
  let E := gsans μ '' unitDiscExterior
  let H : ℂ → ℂ := fun t => if t = 0 then 0 else (gsans μ t⁻¹)⁻¹
  obtain ⟨hHd, hHi, hg0⟩ := r24_inversion hμ
  have hHimg : H '' unitDisc = (fun z : ℂ => z⁻¹) '' E ∪ {0} := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases hw0 : w = 0
      · simp [H, hw0]
      · exact Or.inl ⟨gsans μ w⁻¹, ⟨w⁻¹, QCV.qcv_inv_mem_exterior ⟨hw, hw0⟩, rfl⟩,
          by simp [H, hw0]⟩
    · rintro (⟨v, hv, rfl⟩ | hy)
      · obtain ⟨x, hx, rfl⟩ := hv
        have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by have : 1 < ‖x‖ := hx; linarith)
        have hxi : x⁻¹ ∈ unitDisc := by
          rw [unitDisc, mem_ball_zero_iff, norm_inv]
          exact inv_lt_one_of_one_lt₀ hx
        exact ⟨x⁻¹, hxi, by simp [H, inv_ne_zero hx0]⟩
      · have hy0 : y = 0 := hy
        exact ⟨0, mem_ball_self one_pos, by simp [H, hy0]⟩
  have hH : IsConformalOnto H unitDisc ((fun z : ℂ => z⁻¹) '' E ∪ {0}) :=
    ⟨hHd, hHi, hHimg⟩
  obtain ⟨x, hx, rfl⟩ := hu
  have hg := S2C.s2c_conf_g hμ
  have hEo := resolvent_exterior_isOpen
  have hx1 : 1 < ‖x‖ := hx
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hu0 := hg0 x hx
  have hxi : x⁻¹ ∈ unitDisc :=
    mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hx1)
  have hHx : H x⁻¹ = (gsans μ x)⁻¹ := by simp [H, inv_ne_zero hx0]
  have hHder : deriv H x⁻¹ = deriv (gsans μ) x * x ^ 2 / (gsans μ x) ^ 2 := by
    have hev : H =ᶠ[𝓝 x⁻¹] fun t => (gsans μ t⁻¹)⁻¹ := by
      filter_upwards [isOpen_ne.mem_nhds (inv_ne_zero hx0)] with t ht
      simp [H, ht]
    have hgd : HasDerivAt (gsans μ) (deriv (gsans μ) x) (x⁻¹)⁻¹ := by
      rw [inv_inv]
      exact (hg.1.differentiableAt (hEo.mem_nhds hx)).hasDerivAt
    have hd : HasDerivAt (fun t => (gsans μ t⁻¹)⁻¹) _ x⁻¹ :=
      (hgd.comp x⁻¹ (hasDerivAt_inv (inv_ne_zero hx0))).inv
        (by simpa only [Function.comp_apply, inv_inv] using hu0)
    rw [hev.deriv_eq, hd.deriv]
    simp only [Function.comp_apply, inv_inv]
    field_simp
  have hden := eq22_density_formula hH hxi
  rw [hHx, hHder, norm_div, norm_mul, norm_pow, norm_pow, norm_inv] at hden
  have hd0 := deriv_ne_zero_of_injOn hEo hg.1 hg.2.1 hx
  have hi : deriv (Function.invFunOn (gsans μ) unitDiscExterior) (gsans μ x) =
      (deriv (gsans μ) x)⁻¹ :=
    eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul hEo hg hx)
  rw [hg.2.1.leftInvOn_invFunOn hx, hi, norm_inv]
  change (poincareDensity ((fun z : ℂ => z⁻¹) '' E ∪ {0}) (gsans μ x)⁻¹ /
    ‖gsans μ x‖ ^ 2) ^ 2 = rho x * (‖deriv (gsans μ) x‖⁻¹) ^ 2
  rw [hden]
  have hxN : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  have huN : ‖gsans μ x‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have hdN : ‖deriv (gsans μ) x‖ ≠ 0 := norm_ne_zero_iff.mpr hd0
  have hs : 1 - ‖x‖ ^ 2 ≠ 0 := by nlinarith
  have hs' : ‖x‖ ^ 2 - 1 ≠ 0 := by nlinarith
  have he : (1 - ‖x‖⁻¹ ^ 2) * (‖deriv (gsans μ) x‖ * ‖x‖ ^ 2 / ‖gsans μ x‖ ^ 2) =
      (‖x‖ ^ 2 - 1) * ‖deriv (gsans μ) x‖ / ‖gsans μ x‖ ^ 2 := by
    field_simp
    <;> ring
  rw [he]
  unfold rho
  field_simp [hs, hs']
  <;> ring

#print axioms hbSurj_exterior_density
end TakhtajanTeo
