import LiZhongQC.Ch05.S21_UniversalTeichmuller

/-!
Portable local radial Wirtinger interface for the resolvent PDE lane.
Only the existing Li Zhong foundation is imported; there is no TakhtajanTeo
section dependency, so this file can be moved below S1_4 without an import cycle.
The profile may be singular away from the point under consideration.
-/

open Complex Set Filter Topology
open scoped ComplexConjugate

namespace TakhtajanTeo

open LiZhongQC

/-- Real Fréchet derivative of a radial composition from a derivative of the
profile at the single squared-radius value. -/
theorem tt_radial_hasFDerivAt {F : ℝ → ℂ} {F' : ℂ} {z : ℂ}
    (hF : HasDerivAt F F' (‖z‖ ^ 2)) :
    HasFDerivAt (fun w : ℂ => F (‖w‖ ^ 2))
      ((ContinuousLinearMap.toSpanSingleton ℝ F').comp (2 • innerSL ℝ z)) z := by
  exact hF.hasFDerivAt.comp z (hasStrictFDerivAt_norm_sq z).hasFDerivAt

/-- First radial Wirtinger derivatives from a derivative of the real profile
at the single squared-radius value. -/
theorem tt_radial_wirtinger_first {F : ℝ → ℂ} {F' : ℂ} {z : ℂ}
    (hF : HasDerivAt F F' (‖z‖ ^ 2)) :
    dz (fun w : ℂ => F (‖w‖ ^ 2)) z = conj z * F' ∧
      dzbar (fun w : ℂ => F (‖w‖ ^ 2)) z = z * F' := by
  have hd : HasFDerivAt (fun w : ℂ => F (‖w‖ ^ 2))
      ((ContinuousLinearMap.toSpanSingleton ℝ F').comp (2 • innerSL ℝ z)) z :=
    tt_radial_hasFDerivAt hF
  have hx : fderiv ℝ (fun w : ℂ => F (‖w‖ ^ 2)) z 1 = (2 * z.re : ℝ) • F' := by
    rw [hd.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      innerSL_apply_apply, Complex.inner, mul_assoc]
  have hy : fderiv ℝ (fun w : ℂ => F (‖w‖ ^ 2)) z I = (2 * z.im : ℝ) • F' := by
    rw [hd.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      innerSL_apply_apply, Complex.inner, Complex.mul_re, mul_assoc]
  constructor
  · unfold dz
    rw [hx, hy]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [show conj z = (z.re : ℂ) - I * z.im by
      apply Complex.ext <;> simp]
    ring
  · unfold dzbar
    rw [hx, hy]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    have hz' : (z.re : ℂ) + I * z.im = z := by apply Complex.ext <;> simp
    calc
      _ = ((z.re : ℂ) + I * z.im) * F' := by ring
      _ = z * F' := by rw [hz']

/-- The mixed radial derivative under a genuinely local C2 hypothesis on the
real profile. No global smoothness or endpoint regularity is required. -/
theorem tt_radial_wirtinger_second {F : ℝ → ℂ} {z : ℂ}
    (hF : ContDiffAt ℝ 2 F (‖z‖ ^ 2)) :
    dz (dzbar (fun w : ℂ => F (‖w‖ ^ 2))) z =
      deriv F (‖z‖ ^ 2) + (‖z‖ ^ 2 : ℝ) * deriv (deriv F) (‖z‖ ^ 2) := by
  have hFp : DifferentiableAt ℝ (deriv F) (‖z‖ ^ 2) :=
    (hF.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hn : Continuous (fun w : ℂ => ‖w‖ ^ 2) := continuous_norm.pow 2
  have hnear : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 F (‖w‖ ^ 2) :=
    hn.continuousAt.tendsto.eventually (hF.eventually (by norm_num))
  have heq : dzbar (fun w : ℂ => F (‖w‖ ^ 2)) =ᶠ[𝓝 z]
      (fun w : ℂ => w * deriv F (‖w‖ ^ 2)) := by
    filter_upwards [hnear] with w hw
    exact (tt_radial_wirtinger_first (hw.differentiableAt (by norm_num)).hasDerivAt).2
  have heqd : dz (dzbar (fun w : ℂ => F (‖w‖ ^ 2))) z =
      dz (fun w : ℂ => w * deriv F (‖w‖ ^ 2)) z := by
    unfold dz
    rw [heq.fderiv_eq (𝕜 := ℝ)]
  have hr : DifferentiableAt ℝ (fun w : ℂ => deriv F (‖w‖ ^ 2)) z :=
    (tt_radial_hasFDerivAt hFp.hasDerivAt).differentiableAt
  have hid : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiableAt_id
  have hdz : dz (fun w : ℂ => deriv F (‖w‖ ^ 2)) z =
      conj z * deriv (deriv F) (‖z‖ ^ 2) := (tt_radial_wirtinger_first hFp.hasDerivAt).1
  have hi : dz (fun w : ℂ => w) z = 1 := by simp [dz]
  rw [heqd, dz_mul hid hr, hdz, hi, mul_one, ← mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  ring

/-- Open-domain form, convenient for profiles singular at the endpoints of an
interval such as (0,1). -/
theorem tt_radial_wirtinger_second_on {F : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s)
    (hF : ContDiffOn ℝ 2 F s) {z : ℂ} (hz : ‖z‖ ^ 2 ∈ s) :
    dz (dzbar (fun w : ℂ => F (‖w‖ ^ 2))) z =
      deriv F (‖z‖ ^ 2) + (‖z‖ ^ 2 : ℝ) * deriv (deriv F) (‖z‖ ^ 2) := by
  exact tt_radial_wirtinger_second (hF.contDiffAt (hs.mem_nhds hz))


end TakhtajanTeo
