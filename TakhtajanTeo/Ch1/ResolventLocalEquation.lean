import TakhtajanTeo.Ch1.S1_4_ResolventCore
import TakhtajanTeo.Ch1.RadialWirtinger

/-!
# Scalar differential equation for the resolvent kernel

These local scalar identities are prerequisites for the RK3 Green-kernel argument.
They do not assert differentiability of the singular integral or a distributional identity.
-/

open Real Filter Set Topology

noncomputable section

namespace TakhtajanTeo

/-- The local radial Wirtinger interface expressed in the memoir's Laplacian convention. -/
theorem laplace0_radial_of_contDiffAt {F : ℝ → ℂ} {z : ℂ}
    (hF : ContDiffAt ℝ 2 F (‖z‖ ^ 2)) :
    laplace0 (fun w : ℂ => F (‖w‖ ^ 2)) z =
      -((rho z : ℂ)⁻¹ *
        (deriv F (‖z‖ ^ 2) + (‖z‖ ^ 2 : ℝ) * deriv (deriv F) (‖z‖ ^ 2))) := by
  unfold laplace0
  rw [tt_radial_wirtinger_second hF]

/-- First derivative of the scalar kernel profile, away from its singular endpoint. -/
theorem resolvent_scalar_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x : ℝ => (2 * x + 1) / (2 * π) * Real.log ((x + 1) / x) - 1 / π)
      (Real.log ((u + 1) / u) / π - (2 * u + 1) / (2 * π * u * (u + 1))) u := by
  have hu1 : u + 1 ≠ 0 := by positivity
  have hl := (((hasDerivAt_id u).add_const 1).div (hasDerivAt_id u) hu.ne').log
    (div_ne_zero hu1 hu.ne')
  have hp := (((((hasDerivAt_id u).const_mul 2).add_const 1).div_const (2 * π)).mul hl).sub_const (1 / π)
  convert hp using 1
  · funext x
    rfl
  · simp only [id_eq, Pi.div_apply, Pi.mul_apply]
    field_simp [hu.ne', hu1]
    <;> ring

/-- The second derivative of the scalar kernel profile has a simple positive rational form. -/
theorem resolvent_scalar_first_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x : ℝ => Real.log ((x + 1) / x) / π -
      (2 * x + 1) / (2 * π * x * (x + 1)))
      (1 / (2 * π * u ^ 2 * (u + 1) ^ 2)) u := by
  have hu1 : u + 1 ≠ 0 := by positivity
  have hl := (((hasDerivAt_id u).add_const 1).div (hasDerivAt_id u) hu.ne').log
    (div_ne_zero hu1 hu.ne')
  have hd := ((hasDerivAt_id u).const_mul (2 * π)).mul ((hasDerivAt_id u).add_const 1)
  have hp := (hl.div_const π).sub ((((hasDerivAt_id u).const_mul 2).add_const 1).div hd
    (by change 2 * π * u * (u + 1) ≠ 0; positivity))
  convert hp using 1
  · funext x
    rfl
  · simp only [id_eq, Pi.div_apply, Pi.mul_apply]
    field_simp [hu.ne', hu1]
    <;> ring

/-- The radial profile satisfies the homogeneous hyperbolic resolvent equation for positive parameter. -/
theorem resolvent_scalar_ode {u : ℝ} (hu : 0 < u) :
    u * (u + 1) * (1 / (2 * π * u ^ 2 * (u + 1) ^ 2)) +
      (2 * u + 1) * (Real.log ((u + 1) / u) / π - (2 * u + 1) / (2 * π * u * (u + 1))) -
      2 * ((2 * u + 1) / (2 * π) * Real.log ((u + 1) / u) - 1 / π) = 0 := by
  have hu1 : u + 1 ≠ 0 := by positivity
  field_simp [hu.ne', hu1]
  <;> ring

/-- The logarithmic term has vanishing first-order weight at its singular endpoint. -/
theorem resolvent_scalar_weighted_log_tendsto_zero :
    Tendsto (fun u : ℝ => u * Real.log ((u + 1) / u)) (𝓝[>] 0) (𝓝 0) := by
  have hl : ContinuousAt (fun u : ℝ => Real.log (u + 1)) 0 :=
    (continuousAt_id.add continuousAt_const).log (by norm_num)
  have hc : ContinuousAt (fun u : ℝ => u * Real.log (u + 1) - u * Real.log u) 0 :=
    (continuousAt_id.mul hl).sub Real.continuous_mul_log.continuousAt
  have ht : Tendsto (fun u : ℝ => u * Real.log (u + 1) - u * Real.log u)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  change 0 < u at hu
  rw [Real.log_div (by linarith : u + 1 ≠ 0) hu.ne']
  ring

/-- Singular-endpoint flux of the scalar kernel derivative.
This fixes the normalization of the logarithmic fundamental singularity. -/
theorem resolvent_scalar_derivative_flux :
    Tendsto (fun u : ℝ => u * (Real.log ((u + 1) / u) / π -
      (2 * u + 1) / (2 * π * u * (u + 1)))) (𝓝[>] 0) (𝓝 (-(1 / (2 * π)))) := by
  have h0 : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun u : ℝ => (2 * u + 1) / (2 * π * (u + 1)))
      (𝓝[>] 0) (𝓝 (1 / (2 * π))) := by
    change Tendsto ((fun u : ℝ => 2 * u + 1) / (fun u : ℝ => 2 * π * (u + 1)))
      (𝓝[>] 0) (𝓝 (1 / (2 * π)))
    simpa using ((h0.const_mul 2).add_const 1).div
      ((h0.add_const 1).const_mul (2 * π)) (by positivity : 2 * π * (0 + 1) ≠ 0)
  have ht : Tendsto (fun u : ℝ => (u * Real.log ((u + 1) / u)) / π -
      (2 * u + 1) / (2 * π * (u + 1))) (𝓝[>] 0) (𝓝 (-(1 / (2 * π)))) := by
    simpa using (resolvent_scalar_weighted_log_tendsto_zero.div_const π).sub hr
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  change 0 < u at hu
  have hu1 : u + 1 ≠ 0 := by positivity
  field_simp [hu.ne', hu1]
  <;> ring

/-- The finite part remaining after subtracting the logarithmic singularity. -/
theorem resolvent_scalar_logarithmic_finite_part :
    Tendsto (fun u : ℝ =>
      ((2 * u + 1) / (2 * π) * Real.log ((u + 1) / u) - 1 / π) + Real.log u / (2 * π))
      (𝓝[>] 0) (𝓝 (-(1 / π))) := by
  have hl : ContinuousAt (fun u : ℝ => Real.log (u + 1)) 0 :=
    (continuousAt_id.add continuousAt_const).log (by norm_num)
  have hc : ContinuousAt (fun u : ℝ =>
      (2 * u + 1) / (2 * π) * Real.log (u + 1) - (u * Real.log u) / π - 1 / π) 0 :=
    (((continuousAt_const.mul continuousAt_id).add continuousAt_const).div_const (2 * π) |>.mul hl).sub
      (Real.continuous_mul_log.continuousAt.div_const π) |>.sub continuousAt_const
  have ht : Tendsto (fun u : ℝ =>
      (2 * u + 1) / (2 * π) * Real.log (u + 1) - (u * Real.log u) / π - 1 / π)
      (𝓝[>] 0) (𝓝 (-(1 / π))) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  change 0 < u at hu
  rw [Real.log_div (by linarith : u + 1 ≠ 0) hu.ne']
  ring

/-- Restricting the centered complex kernel to the real radius gives the scalar profile. -/
theorem resolvent_center_radius_eq (r : ℝ) :
    resolventKernel 0 (r : ℂ) =
      (2 * (r ^ 2 / (1 - r ^ 2)) + 1) / (2 * π) *
        Real.log (((r ^ 2 / (1 - r ^ 2)) + 1) / (r ^ 2 / (1 - r ^ 2))) - 1 / π := by
  simp [resolventKernel, pointPair, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Radial derivative of the actual centered complex kernel on the punctured unit radius. -/
theorem resolvent_center_radius_hasDerivAt {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => resolventKernel 0 (t : ℂ))
      ((Real.log (((r ^ 2 / (1 - r ^ 2)) + 1) / (r ^ 2 / (1 - r ^ 2))) / π -
        (2 * (r ^ 2 / (1 - r ^ 2)) + 1) /
          (2 * π * (r ^ 2 / (1 - r ^ 2)) * ((r ^ 2 / (1 - r ^ 2)) + 1))) *
        (2 * r / (1 - r ^ 2) ^ 2)) r := by
  have hrD : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hu : 0 < r ^ 2 / (1 - r ^ 2) := div_pos (sq_pos_of_pos hr.1) hrD
  have hp := (resolvent_scalar_hasDerivAt hu).comp (x := r)
    (h := fun t : ℝ => t ^ 2 / (1 - t ^ 2)) (resolvent_radial_coordinate_hasDerivAt hrD.ne')
  convert hp using 1
  funext t
  exact resolvent_center_radius_eq t

/-- The hyperbolic radial parameter approaches zero through positive values. -/
theorem resolvent_radial_coordinate_tendsto_zero_right :
    Tendsto (fun r : ℝ => r ^ 2 / (1 - r ^ 2)) (𝓝[>] 0) (𝓝[>] 0) := by
  have h0 : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · change Tendsto ((fun r : ℝ => r ^ 2) / (fun r : ℝ => 1 - r ^ 2)) (𝓝[>] 0) (𝓝 0)
    simpa using (h0.pow 2).div (tendsto_const_nhds.sub (h0.pow 2)) (by norm_num : (1 : ℝ) - 0 ^ 2 ≠ 0)
  · have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hr1
    change 0 < r at hr
    exact div_pos (sq_pos_of_pos hr) (by nlinarith)

/-- The radial normal flux of the actual kernel has the logarithmic coefficient `-1/π`. -/
theorem resolvent_center_radial_flux :
    Tendsto (fun r : ℝ => r * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) r)
      (𝓝[>] 0) (𝓝 (-(1 / π))) := by
  have h0 : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun r : ℝ => 2 / (1 - r ^ 2)) (𝓝[>] 0) (𝓝 2) := by
    change Tendsto ((fun _ : ℝ => (2 : ℝ)) / (fun r : ℝ => 1 - r ^ 2)) (𝓝[>] 0) (𝓝 2)
    simpa using tendsto_const_nhds.div (tendsto_const_nhds.sub (h0.pow 2))
      (by norm_num : (1 : ℝ) - 0 ^ 2 ≠ 0)
  have hf := resolvent_scalar_derivative_flux.comp resolvent_radial_coordinate_tendsto_zero_right
  have ht := hd.mul hf
  have hconst : (2 : ℝ) * (-(1 / (2 * π))) = -(1 / π) := by field_simp
  rw [hconst] at ht
  apply ht.congr'
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hr1
  change 0 < r at hr
  rw [(resolvent_center_radius_hasDerivAt ⟨hr, hr1⟩).deriv]
  have hrD : 1 - r ^ 2 ≠ 0 := by nlinarith
  have halg (b : ℝ) : 2 / (1 - r ^ 2) * (r ^ 2 / (1 - r ^ 2) * b) =
      r * (b * (2 * r / (1 - r ^ 2) ^ 2)) := by field_simp [hrD]
  exact halg _

/-- Second derivative of the change from Euclidean radius to the point-pair parameter. -/
theorem resolvent_radial_coordinate_first_hasDerivAt {r : ℝ} (hr : 1 - r ^ 2 ≠ 0) :
    HasDerivAt (fun t : ℝ => 2 * t / (1 - t ^ 2) ^ 2)
      (2 * (1 + 3 * r ^ 2) / (1 - r ^ 2) ^ 3) r := by
  have hd := (((hasDerivAt_id r).pow 2).const_sub 1).pow 2
  have hp := ((hasDerivAt_id r).const_mul 2).div hd (pow_ne_zero 2 hr)
  convert hp using 1
  · funext t
    rfl
  · simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hr]
    <;> ring

/-- Second radial derivative of the original centered kernel, locally away from zero and one. -/
theorem resolvent_center_radius_first_hasDerivAt {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)))
      ((1 / (2 * π * (r ^ 2 / (1 - r ^ 2)) ^ 2 *
          (r ^ 2 / (1 - r ^ 2) + 1) ^ 2)) * (2 * r / (1 - r ^ 2) ^ 2) ^ 2 +
        (Real.log ((r ^ 2 / (1 - r ^ 2) + 1) / (r ^ 2 / (1 - r ^ 2))) / π -
          (2 * (r ^ 2 / (1 - r ^ 2)) + 1) /
            (2 * π * (r ^ 2 / (1 - r ^ 2)) * (r ^ 2 / (1 - r ^ 2) + 1))) *
          (2 * (1 + 3 * r ^ 2) / (1 - r ^ 2) ^ 3)) r := by
  have hrD : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hu : 0 < r ^ 2 / (1 - r ^ 2) := div_pos (sq_pos_of_pos hr.1) hrD
  have hp := ((resolvent_scalar_first_hasDerivAt hu).comp (x := r)
    (h := fun t : ℝ => t ^ 2 / (1 - t ^ 2))
    (resolvent_radial_coordinate_hasDerivAt hrD.ne')).mul
    (resolvent_radial_coordinate_first_hasDerivAt hrD.ne')
  have heq : deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) =ᶠ[𝓝 r]
      (fun t : ℝ => (Real.log ((t ^ 2 / (1 - t ^ 2) + 1) / (t ^ 2 / (1 - t ^ 2))) / π -
        (2 * (t ^ 2 / (1 - t ^ 2)) + 1) /
          (2 * π * (t ^ 2 / (1 - t ^ 2)) * (t ^ 2 / (1 - t ^ 2) + 1))) *
        (2 * t / (1 - t ^ 2) ^ 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact (resolvent_center_radius_hasDerivAt ht).deriv
  convert hp.congr_of_eventuallyEq heq using 1 <;>
    simp only [Function.comp_apply] <;> ring

/-- The actual kernel satisfies the Euclidean radial resolvent equation on `0 < r < 1`.
This is a punctured-domain equation; the singular source at zero is accounted for separately
by `resolvent_center_radial_flux`. -/
theorem resolvent_center_radial_ode {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (fun t : ℝ => resolventKernel 0 (t : ℂ))) r +
      deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) r / r =
      8 / (1 - r ^ 2) ^ 2 * resolventKernel 0 (r : ℂ) := by
  rw [(resolvent_center_radius_first_hasDerivAt hr).deriv,
    (resolvent_center_radius_hasDerivAt hr).deriv, resolvent_center_radius_eq]
  have hrD : 1 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
  have hu1 : r ^ 2 / (1 - r ^ 2) + 1 ≠ 0 := by
    have : 0 < r ^ 2 / (1 - r ^ 2) :=
      div_pos (sq_pos_of_pos hr.1) (by nlinarith [hr.1, hr.2])
    positivity
  field_simp [hr.1.ne', hrD, hu1]
  <;> ring

/-- Divergence form of the centered radial equation, suitable for Green identities. -/
theorem resolvent_center_radial_flux_hasDerivAt {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => t * deriv (fun s : ℝ => resolventKernel 0 (s : ℂ)) t)
      (8 * r / (1 - r ^ 2) ^ 2 * resolventKernel 0 (r : ℂ)) r := by
  have hd := (resolvent_center_radius_first_hasDerivAt hr).differentiableAt.hasDerivAt
  convert (hasDerivAt_id r).mul hd using 1
  · rfl
  · calc
    8 * r / (1 - r ^ 2) ^ 2 * resolventKernel 0 (r : ℂ) =
        r * (8 / (1 - r ^ 2) ^ 2 * resolventKernel 0 (r : ℂ)) := by ring
    _ = r * (deriv (deriv (fun t : ℝ => resolventKernel 0 (t : ℂ))) r +
        deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) r / r) := by
      rw [resolvent_center_radial_ode hr]
    _ = _ := by simp only [id_eq]; field_simp [hr.1.ne'] <;> ring

/-- Radial Green flux balance on a closed annulus strictly inside the punctured disk. -/
theorem resolvent_center_annulus_flux {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    (∫ r in a..b, 8 * r / (1 - r ^ 2) ^ 2 * resolventKernel 0 (r : ℂ)) =
      b * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) b -
        a * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) a := by
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_min ha.1 hb.1) hx.1,
      lt_of_le_of_lt hx.2 (max_lt ha.2 hb.2)⟩
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => resolvent_center_radial_flux_hasDerivAt (hsub hx))
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hxD : (1 - x ^ 2) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    have hh := hsub hx
    nlinarith [hh.1, hh.2]
  exact ((((continuousAt_const.mul continuousAt_id).div
    ((continuousAt_const.sub (continuousAt_id.pow 2)).pow 2) hxD).mul
      (resolvent_center_radius_hasDerivAt (hsub hx)).continuousAt).continuousWithinAt)

/-- The Wronskian derivative behind the radial Green identity. Only local derivatives
of the test function are required. -/
theorem resolvent_center_green_hasDerivAt {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    {φ φ' φ'' : ℝ → ℝ} (hφ : HasDerivAt φ (φ' r) r)
    (hφ' : HasDerivAt φ' (φ'' r) r) :
    HasDerivAt (fun t : ℝ => resolventKernel 0 (t : ℂ) * (t * φ' t) -
      (t * deriv (fun s : ℝ => resolventKernel 0 (s : ℂ)) t) * φ t)
      (resolventKernel 0 (r : ℂ) *
        (φ' r + r * φ'' r - 8 * r / (1 - r ^ 2) ^ 2 * φ r)) r := by
  have hK := (resolvent_center_radius_hasDerivAt hr).differentiableAt.hasDerivAt
  have hleft := hK.mul ((hasDerivAt_id r).mul hφ')
  have hright := (resolvent_center_radial_flux_hasDerivAt hr).mul hφ
  convert hleft.sub hright using 1
  · rfl
  · simp only [Pi.mul_apply, id_eq]
    ring

/-- Green identity for a twice differentiable radial test function on an annulus.
The singular endpoint is excluded; taking its limit is a separate step. -/
theorem resolvent_center_annulus_green {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    {φ φ' φ'' : ℝ → ℝ}
    (hφ : ∀ r ∈ uIcc a b, HasDerivAt φ (φ' r) r)
    (hφ' : ∀ r ∈ uIcc a b, HasDerivAt φ' (φ'' r) r)
    (hφ'' : ContinuousOn φ'' (uIcc a b)) :
    (∫ r in a..b, resolventKernel 0 (r : ℂ) *
      (φ' r + r * φ'' r - 8 * r / (1 - r ^ 2) ^ 2 * φ r)) =
      (resolventKernel 0 (b : ℂ) * (b * φ' b) -
        (b * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) b) * φ b) -
      (resolventKernel 0 (a : ℂ) * (a * φ' a) -
        (a * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) a) * φ a) := by
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_min ha.1 hb.1) hx.1,
      lt_of_le_of_lt hx.2 (max_lt ha.2 hb.2)⟩
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => resolvent_center_green_hasDerivAt (hsub hx) (hφ x hx) (hφ' x hx))
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hxD : (1 - x ^ 2) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    have hh := hsub hx
    nlinarith [hh.1, hh.2]
  have hc : ContinuousWithinAt (fun r : ℝ => 8 * r / (1 - r ^ 2) ^ 2) (uIcc a b) x :=
    ((continuousAt_const.mul continuousAt_id).div
      ((continuousAt_const.sub (continuousAt_id.pow 2)).pow 2) hxD).continuousWithinAt
  exact (resolvent_center_radius_hasDerivAt (hsub hx)).continuousAt.continuousWithinAt.mul
    (((hφ' x hx).continuousAt.continuousWithinAt.add
      (continuousWithinAt_id.mul (hφ'' x hx))).sub
        (hc.mul (hφ x hx).continuousAt.continuousWithinAt))

/-- The logarithmic finite part of the original centered kernel in Euclidean radius. -/
theorem resolvent_center_logarithmic_finite_part :
    Tendsto (fun r : ℝ => resolventKernel 0 (r : ℂ) + Real.log r / π)
      (𝓝[>] 0) (𝓝 (-(1 / π))) := by
  have hc : ContinuousAt (fun r : ℝ => Real.log (1 - r ^ 2)) 0 :=
    (continuousAt_const.sub (continuousAt_id.pow 2)).log (by norm_num)
  have hl : Tendsto (fun r : ℝ => Real.log (1 - r ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have ht := (resolvent_scalar_logarithmic_finite_part.comp
    resolvent_radial_coordinate_tendsto_zero_right).add (hl.div_const (2 * π))
  simp only [zero_div, add_zero] at ht
  apply ht.congr'
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hr1
  change 0 < r at hr
  have hrD : 1 - r ^ 2 ≠ 0 := by nlinarith
  dsimp only [Function.comp_apply]
  rw [resolvent_center_radius_eq, Real.log_div (pow_ne_zero 2 hr.ne') hrD,
    Real.log_pow]
  ring

/-- The logarithmic singularity has vanishing first-order radial weight. -/
theorem resolvent_center_radius_mul_tendsto_zero :
    Tendsto (fun r : ℝ => r * resolventKernel 0 (r : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun r : ℝ => r * Real.log r) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun r : ℝ => r * Real.log r) 0 :=
      Real.continuous_mul_log.continuousAt
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have ht := (h0.mul resolvent_center_logarithmic_finite_part).sub (hl.div_const π)
  simp only [zero_mul, zero_div, sub_zero] at ht
  apply ht.congr'
  filter_upwards [] with r
  ring

/-- The inner-boundary term in the centered Green identity tends to the point value
of the test function divided by π. -/
theorem resolvent_center_green_boundary_limit {φ φ' : ℝ → ℝ}
    (hφ : ContinuousAt φ 0) (hφ' : ContinuousAt φ' 0) :
    Tendsto (fun r : ℝ => resolventKernel 0 (r : ℂ) * (r * φ' r) -
      (r * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) r) * φ r)
      (𝓝[>] 0) (𝓝 (φ 0 / π)) := by
  have ht := (resolvent_center_radius_mul_tendsto_zero.mul
    (hφ'.tendsto.mono_left nhdsWithin_le_nhds)).sub
      (resolvent_center_radial_flux.mul (hφ.tendsto.mono_left nhdsWithin_le_nhds))
  have he : (0 : ℝ) * φ' 0 - (-(1 / π)) * φ 0 = φ 0 / π := by ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [] with r
  ring

/-- Passing to the singular inner endpoint in the radial Green identity. -/
theorem resolvent_center_green_integral_limit {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    {φ φ' φ'' : ℝ → ℝ}
    (hφ : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt φ (φ' r) r)
    (hφ' : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt φ' (φ'' r) r)
    (hφ'' : ContinuousOn φ'' (Ioo (0 : ℝ) 1))
    (hφ0 : ContinuousAt φ 0) (hφ'0 : ContinuousAt φ' 0) :
    Tendsto (fun a : ℝ => ∫ r in a..b, resolventKernel 0 (r : ℂ) *
      (φ' r + r * φ'' r - 8 * r / (1 - r ^ 2) ^ 2 * φ r))
      (𝓝[>] 0) (𝓝 ((resolventKernel 0 (b : ℂ) * (b * φ' b) -
        (b * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) b) * φ b) - φ 0 / π)) := by
  have ht := (tendsto_const_nhds (x := resolventKernel 0 (b : ℂ) * (b * φ' b) -
    (b * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) b) * φ b)).sub
      (resolvent_center_green_boundary_limit hφ0 hφ'0)
  apply ht.congr'
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with a ha ha1
  change 0 < a at ha
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_min ha hb.1) hx.1,
      lt_of_le_of_lt hx.2 (max_lt ha1 hb.2)⟩
  exact (resolvent_center_annulus_green ⟨ha, ha1⟩ hb
    (fun x hx => hφ x (hsub hx)) (fun x hx => hφ' x (hsub hx))
      (hφ''.mono hsub)).symm

/-- The normalized radial Green integral has point-source value `φ 0` when the
outer boundary values of the test function and its derivative vanish. This is an
improper radial integral statement, not yet a two-dimensional distributional theorem. -/
theorem resolvent_center_radial_green_source {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    {φ φ' φ'' : ℝ → ℝ}
    (hφ : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt φ (φ' r) r)
    (hφ' : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt φ' (φ'' r) r)
    (hφ'' : ContinuousOn φ'' (Ioo (0 : ℝ) 1))
    (hφ0 : ContinuousAt φ 0) (hφ'0 : ContinuousAt φ' 0)
    (hbφ : φ b = 0) (hbφ' : φ' b = 0) :
    Tendsto (fun a : ℝ => ∫ r in a..b, π * resolventKernel 0 (r : ℂ) *
      (8 * r / (1 - r ^ 2) ^ 2 * φ r - φ' r - r * φ'' r))
      (𝓝[>] 0) (𝓝 (φ 0)) := by
  have ht := (resolvent_center_green_integral_limit hb hφ hφ' hφ'' hφ0 hφ'0).const_mul (-π)
  simp only [hbφ, hbφ', mul_zero, sub_zero, zero_sub] at ht
  have hconst : -π * -(φ 0 / π) = φ 0 := by field_simp
  rw [hconst] at ht
  apply ht.congr'
  filter_upwards [] with a
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  ring

end TakhtajanTeo
