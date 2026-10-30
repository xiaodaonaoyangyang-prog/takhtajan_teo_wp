import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.MetricSpace.Algebra

/-!
# Holomorphic center jets from punctured-disk convergence

Only the functions' holomorphy is assumed on the whole disk. Locally uniform
convergence is required on the punctured disk, not at its center. Compactness
on the circle of radius r/2 and the existing Cauchy estimate recover the center
first derivative; applying that result to z*f also recovers the center value.
-/

open Complex Set Metric Filter Topology
open scoped Classical
noncomputable section
namespace TakhtajanTeo

/-- A fixed interior Cauchy circle recovers the derivative at the missing center. -/
theorem grp25h_deriv_center {r : ℝ} (hr : 0<r) {fn : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hfn : ∀ n, DifferentiableOn ℂ (fn n) (ball (0 : ℂ) r))
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) r))
    (hlim : TendstoLocallyUniformlyOn fn f atTop (ball (0 : ℂ) r\{0})) :
    Tendsto (fun n => deriv (fn n) 0) atTop (𝓝 (deriv f 0)) := by
  have hs : 0<r/2 := half_pos hr
  have hsr : r/2<r := half_lt_self hr
  have hclosed : closedBall (0 : ℂ) (r/2)⊆ball (0 : ℂ) r := closedBall_subset_ball hsr
  have hcirc : sphere (0 : ℂ) (r/2)⊆ball (0 : ℂ) r\{0} := by
    intro z hz
    refine ⟨hclosed (sphere_subset_closedBall hz),?_⟩
    intro he
    have hn : ‖z‖=r/2 := mem_sphere_zero_iff_norm.mp hz
    rw [he,norm_zero] at hn
    linarith
  have hU := (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_ball.sdiff isClosed_singleton)).mp hlim _ hcirc (isCompact_sphere (0 : ℂ) (r/2))
  rw [Metric.tendstoUniformlyOn_iff] at hU
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hU (ε*(r/2)) (mul_pos hε hs)] with n hn
  have hpair : ∀ z∈sphere (0 : ℂ) (r/2), ‖fn n z-f z‖<ε*(r/2) := by
    intro z hz
    simpa only [dist_eq_norm,norm_sub_rev] using hn z hz
  have hb := norm_cderiv_sub_lt hs hpair
    ((hfn n).continuousOn.mono (sphere_subset_closedBall.trans hclosed))
    (hf.continuousOn.mono (sphere_subset_closedBall.trans hclosed))
  simpa only [cderiv_eq_deriv isOpen_ball (hfn n) hs hclosed,
    cderiv_eq_deriv isOpen_ball hf hs hclosed,mul_div_cancel_right₀ _ hs.ne',dist_eq_norm] using hb

/-- The value and first derivative at the center converge; convergence on the punctured disk suffices. -/
theorem grp25h_center_jet {r : ℝ} (hr : 0<r) {fn : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hfn : ∀ n, DifferentiableOn ℂ (fn n) (ball (0 : ℂ) r))
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) r))
    (hlim : TendstoLocallyUniformlyOn fn f atTop (ball (0 : ℂ) r\{0})) :
    Tendsto (fun n => fn n 0) atTop (𝓝 (f 0)) ∧
      Tendsto (fun n => deriv (fn n) 0) atTop (𝓝 (deriv f 0)) := by
  have hId : TendstoLocallyUniformlyOn (fun (_ : ℕ) (z : ℂ) => z) (fun z => z)
      atTop (ball (0 : ℂ) r\{0}) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall (fun _ z _ => by simpa using hε)
  have hL := hId.mul₀ hlim continuous_id.continuousOn (hf.continuousOn.mono sdiff_subset)
  have hV := grp25h_deriv_center hr (fun n => differentiableOn_id.mul (hfn n))
    (differentiableOn_id.mul hf) hL
  have h0 : (0 : ℂ)∈ball (0 : ℂ) r := mem_ball_self hr
  have hd (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (ball (0 : ℂ) r)) :
      deriv (fun z => z*g z) 0=g 0 := by
    simpa only [Pi.mul_def,id_eq,one_mul,zero_mul,add_zero] using ((hasDerivAt_id (0 : ℂ)).mul
      (hg.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt).deriv
  refine ⟨?_,grp25h_deriv_center hr hfn hf hlim⟩
  simpa only [Pi.mul_def,hd _ hf,hd _ (hfn _)] using hV

end TakhtajanTeo
