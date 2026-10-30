import TakhtajanTeo.Ch1.ResolventLocalEquation
import TakhtajanTeo.Ch1.ConformalLaplacian

/-! Local homogeneous equation for the actual centered resolvent kernel.
The singular source is treated separately by the radial Green identities. -/

open Real Filter Set Topology Metric

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The centered kernel as a function of the squared Euclidean radius. -/
def resolventSquaredProfile (s : ℝ) : ℝ :=
  -(1 + s) / (2 * π * (1 - s)) * Real.log s - 1 / π

private def profileFirst (s : ℝ) : ℝ :=
  -Real.log s / (π * (1 - s) ^ 2) - (1 + s) / (2 * π * s * (1 - s))

private def profileSecond (s : ℝ) : ℝ :=
  -2 * Real.log s / (π * (1 - s) ^ 3) +
    (1 - 4 * s - s ^ 2) / (2 * π * s ^ 2 * (1 - s) ^ 2)

theorem resolvent_center_squared_profile (z : ℂ) :
    resolventKernel 0 z = resolventSquaredProfile (‖z‖ ^ 2) := by
  have hpair : pointPair 0 z = ‖z‖ ^ 2 / (1 - ‖z‖ ^ 2) := by
    simp [pointPair]
  rw [resolventKernel, hpair]
  generalize ‖z‖ ^ 2 = s
  by_cases hs : s = 0
  · simp [hs, resolventSquaredProfile]
  by_cases hd : 1 - s = 0
  · have hs1 : s = 1 := by linarith
    simp [hs1, resolventSquaredProfile]
  have hquot : (s / (1 - s) + 1) / (s / (1 - s)) = s⁻¹ := by
    field_simp [hs, hd]
    <;> ring
  rw [hquot, Real.log_inv]
  unfold resolventSquaredProfile
  field_simp [hd]
  <;> ring

private theorem profile_hasDerivAt {s : ℝ} (hs : s ≠ 0) (hd : 1 - s ≠ 0) :
    HasDerivAt resolventSquaredProfile (profileFirst s) s := by
  have hp := (((((hasDerivAt_id s).const_add 1).neg).div
    (((hasDerivAt_id s).const_sub 1).const_mul (2 * π))
      (mul_ne_zero (by positivity) hd)).mul ((hasDerivAt_id s).log hs)).sub_const (1 / π)
  convert hp using 1
  · rfl
  · simp only [Pi.div_apply, Pi.mul_apply, Pi.neg_apply, id_eq]
    unfold profileFirst
    field_simp [hs, hd]
    <;> ring

private theorem profile_first_hasDerivAt {s : ℝ} (hs : s ≠ 0) (hd : 1 - s ≠ 0) :
    HasDerivAt profileFirst (profileSecond s) s := by
  have hD := (hasDerivAt_id s).const_sub 1
  have hl := (((hasDerivAt_id s).log hs).neg).div ((hD.pow 2).const_mul π)
    (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hd))
  have hr := ((hasDerivAt_id s).const_add 1).div
    (((hasDerivAt_id s).const_mul (2 * π)).mul hD)
    (by change 2 * π * s * (1 - s) ≠ 0; exact mul_ne_zero (mul_ne_zero (by positivity) hs) hd)
  convert hl.sub hr using 1
  · rfl
  · simp only [Pi.pow_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply,
      id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    unfold profileSecond
    field_simp [hs, hd]
    <;> ring

private theorem profile_contDiffAt {s : ℝ} (hs : s ≠ 0) (hd : 1 - s ≠ 0) :
    ContDiffAt ℝ 2 resolventSquaredProfile s := by
  unfold resolventSquaredProfile
  have hnum : ContDiffAt ℝ 2 (fun x : ℝ => -(1 + x)) s :=
    (contDiffAt_const.add contDiffAt_id).neg
  have hden : ContDiffAt ℝ 2 (fun x : ℝ => 2 * π * (1 - x)) s :=
    contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)
  have hlog : ContDiffAt ℝ 2 (fun x : ℝ => Real.log x) s := contDiffAt_id.log hs
  exact ((hnum.div hden (mul_ne_zero (by positivity) hd)).mul hlog).sub contDiffAt_const

private theorem profile_ode {s : ℝ} (hs : s ≠ 0) (hd : 1 - s ≠ 0) :
    profileFirst s + s * profileSecond s = 2 / (1 - s) ^ 2 * resolventSquaredProfile s := by
  unfold profileFirst profileSecond resolventSquaredProfile
  field_simp [hs, hd]
  <;> ring

private theorem profile_complex_first_hasDerivAt {s : ℝ}
    (hs : s ≠ 0) (hd : 1 - s ≠ 0) :
    HasDerivAt (deriv (fun t : ℝ => (resolventSquaredProfile t : ℂ)))
      (profileSecond s : ℂ) s := by
  apply (profile_first_hasDerivAt hs hd).ofReal_comp.congr_of_eventuallyEq
  have hn : ∀ᶠ t : ℝ in 𝓝 s, t ≠ 0 := eventually_ne_nhds hs
  have hD : ∀ᶠ t : ℝ in 𝓝 s, 1 - t ≠ 0 :=
    (continuousAt_const.sub continuousAt_id).eventually_ne hd
  filter_upwards [hn, hD] with t ht htD
  exact (profile_hasDerivAt ht htD).ofReal_comp.deriv

/-- Away from its center and the unit circle, the actual centered kernel solves
the homogeneous resolvent equation with the original Laplace convention. -/
theorem resolvent_center_laplace_equation {z : ℂ} (hz : z ≠ 0)
    (hzD : 1 - ‖z‖ ^ 2 ≠ 0) :
    laplace0 (fun w : ℂ => (resolventKernel 0 w : ℂ)) z +
      (1 / 2 : ℂ) * resolventKernel 0 z = 0 := by
  have hs : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hF : ContDiffAt ℝ 2 (fun s : ℝ => (resolventSquaredProfile s : ℂ)) (‖z‖ ^ 2) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (profile_contDiffAt hs hzD)
  have heq : (fun w : ℂ => (resolventKernel 0 w : ℂ)) =
      (fun w : ℂ => (resolventSquaredProfile (‖w‖ ^ 2) : ℂ)) := by
    funext w
    rw [resolvent_center_squared_profile]
  rw [heq, laplace0_radial_of_contDiffAt hF,
    (profile_hasDerivAt hs hzD).ofReal_comp.deriv,
    (profile_complex_first_hasDerivAt hs hzD).deriv,
    resolvent_center_squared_profile]
  have hode := congrArg (fun x : ℝ => (x : ℂ)) (profile_ode hs hzD)
  push_cast at hode
  push_cast
  rw [hode]
  unfold rho
  push_cast
  have hDc : (1 : ℂ) - (‖z‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hzD
  field_simp [hDc]
  <;> ring

/-- The homogeneous kernel equation at an arbitrary center in the disk, excluding
the diagonal. It follows by transporting the centered equation through a disk automorphism. -/
theorem resolvent_disk_laplace_equation {a z : ℂ}
    (ha : a ∈ unitDisc) (hz : z ∈ unitDisc) (hza : z ≠ a) :
    laplace0 (fun w : ℂ => (resolventKernel a w : ℂ)) z +
      (1 / 2 : ℂ) * resolventKernel a z = 0 := by
  have han : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  let U : Set ℂ := unitDisc \ {a}
  let V : Set ℂ := unitDisc \ {0}
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hV : IsOpen V := isOpen_ball.sdiff isClosed_singleton
  have hzU : z ∈ U := ⟨hz, hza⟩
  have hm : MapsTo (blaschke a) U V := by
    intro w hw
    have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw.1
    refine ⟨mem_ball_zero_iff.mpr (blaschke_mem_unitDisc han hwn), ?_⟩
    change blaschke a w ≠ 0
    exact div_ne_zero (sub_ne_zero.mpr hw.2) (blaschke_den_ne_zero han hwn)
  have hf : ContDiffOn ℝ 2 (fun w : ℂ => (resolventKernel 0 w : ℂ)) V := by
    intro w hw
    have hw0 : w ≠ 0 := hw.2
    have hzero : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
    have hp := resolventKernel_contDiffAt (Or.inl rfl) hzero hw.1 hw0.symm
    have hr : ContDiffAt ℝ ⊤ (fun v : ℂ => resolventKernel 0 v) w :=
      hp.comp w (contDiffAt_const.prodMk contDiffAt_id)
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp w hr).of_le le_top).contDiffWithinAt
  have hρ : rho z ≠ 0 := div_ne_zero (by norm_num)
    (pow_ne_zero 2 (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz))
  have hc := laplace0_comp_of_density_pullback hU hV
    ((isConformalOnto_blaschke han).1.mono (show U ⊆ unitDisc from diff_subset))
      hm hf hzU hρ (rho_blaschke_jacobian han hzn)
  have heq : (fun w : ℂ => (resolventKernel a w : ℂ)) =ᶠ[𝓝 z]
      ((fun w : ℂ => (resolventKernel 0 w : ℂ)) ∘ blaschke a) := by
    filter_upwards [(show IsOpen unitDisc from isOpen_ball).mem_nhds hz] with w hw
    change (resolventKernel a w : ℂ) = (resolventKernel 0 (blaschke a w) : ℂ)
    rw [resolventKernel_blaschke_center han (mem_ball_zero_iff.mp hw)]
  have hp := resolvent_center_laplace_equation (show blaschke a z ≠ 0 from (hm hzU).2)
    (resolvent_domain_denominator_ne_zero (Or.inl rfl) (hm hzU).1)
  rw [laplace0_congr_of_eventuallyEq heq, hc,
    ← resolventKernel_blaschke_center han hzn]
  exact hp

/-- Inversion transports the off-diagonal homogeneous kernel equation to the exterior disk. -/
theorem resolvent_exterior_laplace_equation {a z : ℂ}
    (ha : a ∈ unitDiscExterior) (hz : z ∈ unitDiscExterior) (hza : z ≠ a) :
    laplace0 (fun w : ℂ => (resolventKernel a w : ℂ)) z +
      (1 / 2 : ℂ) * resolventKernel a z = 0 := by
  have ha0 := resolvent_exterior_ne_zero ha
  have hz0 := resolvent_exterior_ne_zero hz
  have hi : ∀ w ∈ unitDiscExterior, w⁻¹ ∈ unitDisc := by
    intro w hw
    have hw' : w⁻¹ ∈ unitDisc \ {0} := by
      rw [← resolvent_inv_exterior_image]
      exact ⟨w, hw, rfl⟩
    exact hw'.1
  let U : Set ℂ := unitDiscExterior \ {a}
  let V : Set ℂ := unitDisc \ {a⁻¹}
  have hU : IsOpen U := resolvent_exterior_isOpen.sdiff isClosed_singleton
  have hV : IsOpen V := isOpen_ball.sdiff isClosed_singleton
  have hzU : z ∈ U := ⟨hz, hza⟩
  have hm : MapsTo (fun w : ℂ => w⁻¹) U V := by
    intro w hw
    exact ⟨hi w hw.1, fun he => hw.2 (inv_injective he)⟩
  have hf : ContDiffOn ℝ 2 (fun w : ℂ => (resolventKernel a⁻¹ w : ℂ)) V := by
    intro w hw
    have hwa : w ≠ a⁻¹ := hw.2
    have hp := resolventKernel_contDiffAt (Or.inl rfl) (hi a ha) hw.1 hwa.symm
    have hr : ContDiffAt ℝ ⊤ (fun v : ℂ => resolventKernel a⁻¹ v) w :=
      hp.comp w (contDiffAt_const.prodMk contDiffAt_id)
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp w hr).of_le le_top).contDiffWithinAt
  have hρ : rho z ≠ 0 := div_ne_zero (by norm_num)
    (pow_ne_zero 2 (resolvent_domain_denominator_ne_zero (Or.inr rfl) hz))
  have hc := laplace0_comp_of_density_pullback hU hV
    (resolvent_inv_exterior_conformal.1.mono (show U ⊆ unitDiscExterior from sdiff_subset))
      hm hf hzU hρ (rho_inv_jacobian hz0)
  have heq : (fun w : ℂ => (resolventKernel a w : ℂ)) =ᶠ[𝓝 z]
      ((fun w : ℂ => (resolventKernel a⁻¹ w : ℂ)) ∘ fun w : ℂ => w⁻¹) := by
    filter_upwards [resolvent_exterior_isOpen.mem_nhds hz] with w hw
    change (resolventKernel a w : ℂ) = (resolventKernel a⁻¹ w⁻¹ : ℂ)
    rw [resolventKernel_inv ha0 (resolvent_exterior_ne_zero hw)]
  have hp := resolvent_disk_laplace_equation (hi a ha) (hm hzU).1 (hm hzU).2
  rw [laplace0_congr_of_eventuallyEq heq, hc, ← resolventKernel_inv ha0 hz0]
  exact hp

/-- The off-diagonal homogeneous equation in either disk model, in the second variable. -/
theorem resolvent_kernel_laplace_equation {D : Set ℂ}
    (hD : D = unitDisc ∨ D = unitDiscExterior)
    {a z : ℂ} (ha : a ∈ D) (hz : z ∈ D) (hza : z ≠ a) :
    laplace0 (fun w : ℂ => (resolventKernel a w : ℂ)) z +
      (1 / 2 : ℂ) * resolventKernel a z = 0 := by
  rcases hD with rfl | rfl
  · exact resolvent_disk_laplace_equation ha hz hza
  · exact resolvent_exterior_laplace_equation ha hz hza

/-- By symmetry, the same off-diagonal equation holds in the integration operator's
evaluation variable. -/
theorem resolvent_kernel_first_laplace_equation {D : Set ℂ}
    (hD : D = unitDisc ∨ D = unitDiscExterior)
    {a z : ℂ} (ha : a ∈ D) (hz : z ∈ D) (hza : z ≠ a) :
    laplace0 (fun w : ℂ => (resolventKernel w a : ℂ)) z +
      (1 / 2 : ℂ) * resolventKernel z a = 0 := by
  have heq : (fun w : ℂ => (resolventKernel w a : ℂ)) =
      (fun w : ℂ => (resolventKernel a w : ℂ)) := by
    funext w
    rw [resolventKernel_symm w a]
  rw [heq, resolventKernel_symm z a]
  exact resolvent_kernel_laplace_equation hD ha hz hza

/-- The centered kernel is constant along each Euclidean circle. -/
theorem resolvent_center_circle_value (r θ : ℝ) :
    resolventKernel 0 (circleMap 0 r θ) = resolventKernel 0 (r : ℂ) := by
  rw [resolvent_center_squared_profile, resolvent_center_squared_profile]
  simp only [norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs]

/-- The holomorphic normal boundary factor equals one half of the actual radial flux. -/
theorem resolvent_center_circle_normal {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (θ : ℝ) :
    deriv (circleMap 0 r) θ *
      LiZhongQC.dz (fun w : ℂ => (resolventKernel 0 w : ℂ)) (circleMap 0 r θ) =
      (Complex.I / 2) * ((r * deriv (fun t : ℝ => resolventKernel 0 (t : ℂ)) r : ℝ) : ℂ) := by
  have hs : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.1.ne'
  have hD : 1 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
  have hw : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr.1]
  have heq : (fun w : ℂ => (resolventKernel 0 w : ℂ)) =
      (fun w : ℂ => (resolventSquaredProfile (‖w‖ ^ 2) : ℂ)) := by
    funext w
    rw [resolvent_center_squared_profile]
  have hQ : HasDerivAt (fun t : ℝ => (resolventSquaredProfile t : ℂ))
      (profileFirst (r ^ 2) : ℂ) (‖circleMap 0 r θ‖ ^ 2) := by
    rw [hw]
    exact (profile_hasDerivAt hs hD).ofReal_comp
  have hfirst := (tt_radial_wirtinger_first hQ).1
  have hH : HasDerivAt (fun t : ℝ => resolventKernel 0 (t : ℂ))
      (profileFirst (r ^ 2) * (2 * r)) r := by
    have hp := (profile_hasDerivAt hs hD).comp (x := r)
      (h := fun t : ℝ => t ^ 2) ((hasDerivAt_id r).pow 2)
    convert hp using 1
    · funext t
      rw [resolvent_center_squared_profile]
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Function.comp_apply]
    · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  rw [heq, hfirst, hH.deriv, deriv_circleMap]
  calc
    _ = Complex.I * (circleMap 0 r θ * (starRingEnd ℂ) (circleMap 0 r θ)) *
        (profileFirst (r ^ 2) : ℂ) := by ring
    _ = _ := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
      push_cast
      ring

end TakhtajanTeo
