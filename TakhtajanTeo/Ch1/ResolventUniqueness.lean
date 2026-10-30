import TakhtajanTeo.Ch1.RadialWirtinger
import TakhtajanTeo.Ch1.ConformalLaplacian

/-! Bounded homogeneous resolvent uniqueness on the disk, punctured disk, and
exterior (RK3, TT:1112–1124). The proof uses divergent barriers and the second
derivative test, followed by inversion and density covariance. No resolvent
inversion assertion or puncture-removal assertion is used. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Mixed Wirtinger differentiation is one quarter of the real Hessian trace. -/
theorem resolvent_mixed_eq_hessian_trace {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    dz (dzbar f) z =
      (fderiv ℝ (fderiv ℝ f) z 1 1 + fderiv ℝ (fderiv ℝ f) z I I) / 4 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (1 : ℂ) z)
  have hI := hd.hasFDerivAt.clm_apply (hasFDerivAt_const I z)
  have hb := (h1.add (hI.const_mul I)).mul_const (2 : ℂ)⁻¹
  have hfun : (fun y => (fderiv ℝ f y 1 + I * fderiv ℝ f y I) * (2 : ℂ)⁻¹) = dzbar f := by
    funext y
    simp only [dzbar, div_eq_mul_inv]
  change HasFDerivAt (fun y => (fderiv ℝ f y 1 + I * fderiv ℝ f y I) * (2 : ℂ)⁻¹) _ z at hb
  rw [hfun] at hb
  have hv (v : ℂ) : fderiv ℝ (dzbar f) z v =
      (fderiv ℝ (fderiv ℝ f) z v 1 + I * fderiv ℝ (fderiv ℝ f) z v I) / 2 := by
    rw [hb.fderiv]
    simp [div_eq_mul_inv]
    ring
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  unfold dz
  rw [hv, hv, hs.eq 1 I]
  ring_nf
  rw [I_sq]
  ring

/-- Mixed Wirtinger derivatives commute for locally C2 functions. This low-level
interface is also useful for the Green identity in RK3's existence proof. -/
theorem resolvent_mixed_commute {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    dz (dzbar f) z = dzbar (dz f) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (1 : ℂ) z)
  have hI := hd.hasFDerivAt.clm_apply (hasFDerivAt_const I z)
  have hb := (h1.sub (hI.const_mul I)).mul_const (2 : ℂ)⁻¹
  have hfun : (fun y => (fderiv ℝ f y 1 - I * fderiv ℝ f y I) * (2 : ℂ)⁻¹) = dz f := by
    funext y
    simp only [dz, div_eq_mul_inv]
  change HasFDerivAt (fun y => (fderiv ℝ f y 1 - I * fderiv ℝ f y I) * (2 : ℂ)⁻¹) _ z at hb
  rw [hfun] at hb
  have hv (v : ℂ) : fderiv ℝ (dz f) z v =
      (fderiv ℝ (fderiv ℝ f) z v 1 - I * fderiv ℝ (fderiv ℝ f) z v I) / 2 := by
    rw [hb.fderiv]
    simp [div_eq_mul_inv]
    ring
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  rw [resolvent_mixed_eq_hessian_trace hf]
  unfold dzbar
  rw [hv, hv, hs.eq 1 I]
  ring_nf
  rw [I_sq]
  ring

/-- The Hessian in a real direction equals the second derivative along that line. -/
theorem resolvent_real_line_second {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (v : ℂ) :
    deriv (deriv (fun t : ℝ => (f (z + (t : ℂ) * v)).re)) 0 =
      (fderiv ℝ (fderiv ℝ f) z v v).re := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ 2 f (z + (t : ℂ) * v) :=
    (td_tendsto_line z v).eventually (hf.eventually (by norm_num))
  apply td_twice_deriv2
  refine ⟨fun t => (fderiv ℝ f (z + (t : ℂ) * v) v).re, ?_, ?_⟩
  · filter_upwards [hev] with t ht
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (td_hasDerivAt_line z v t))
  · have hv := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v z)
    have hv' : HasFDerivAt (fun y => fderiv ℝ f y v)
        ((fderiv ℝ (fderiv ℝ f) z).flip v) z := by simpa using hv
    have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * v) v 0 := td_hasDerivAt_line z v 0
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
      (hv'.comp_hasDerivAt_of_eq 0 hl (by simp))
    convert hr using 1 <;> rfl

/-- At a local maximum of the real component, the real mixed derivative is nonpositive. -/
theorem resolvent_mixed_re_nonpos_at_max {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hm : IsLocalMax (fun u => (f u).re) z) :
    (dz (dzbar f) z).re ≤ 0 := by
  have hn (v : ℂ) : (fderiv ℝ (fderiv ℝ f) z v v).re ≤ 0 := by
    have h := td_line_isLocalMin hm.neg
      (Complex.continuous_re.continuousAt.comp hf.continuousAt).neg v
    have hd : deriv (deriv (fun t : ℝ => -(f (z + (t : ℂ) * v)).re)) 0 =
        -deriv (deriv (fun t : ℝ => (f (z + (t : ℂ) * v)).re)) 0 := by
      change deriv (deriv (-(fun t : ℝ => (f (z + (t : ℂ) * v)).re))) 0 = _
      rw [deriv.neg']
      exact deriv.fun_neg
    change 0 ≤ deriv (deriv (fun t : ℝ => -(f (z + (t : ℂ) * v)).re)) 0 at h
    rw [hd, resolvent_real_line_second hf v] at h
    linarith
  rw [resolvent_mixed_eq_hessian_trace hf]
  simp only [Complex.div_ofNat_re, Complex.add_re]
  exact div_nonpos_of_nonpos_of_nonneg (add_nonpos (hn 1) (hn I)) (by norm_num)

/-- Subtraction commutes with the hyperbolic Laplacian on a C2 open domain. -/
theorem resolvent_laplace_sub {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U) {z : ℂ} (hz : z ∈ U) :
    laplace0 (fun u => f u - g u) z = laplace0 f z - laplace0 g z := by
  have he : dzbar (fun u => f u - g u) =ᶠ[𝓝 z] (fun u => dzbar f u - dzbar g u) := by
    filter_upwards [hU.mem_nhds hz] with u hu
    have hfd := (hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu)
    have hgd := (hg.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu)
    unfold dzbar
    rw [fderiv_fun_sub hfd hgd]
    simp only [ContinuousLinearMap.sub_apply]
    ring
  have hm : dz (dzbar (fun u => f u - g u)) z = dz (dzbar f) z - dz (dzbar g) z := by
    have hd : dz (dzbar (fun u => f u - g u)) z = dz (fun u => dzbar f u - dzbar g u) z := by
      unfold dz
      rw [he.fderiv_eq (𝕜 := ℝ)]
    rw [hd, dz_sub_pointwise
      ((differentiableOn_dzbar_of_contDiffOn hU hf).differentiableAt (hU.mem_nhds hz))
      ((differentiableOn_dzbar_of_contDiffOn hU hg).differentiableAt (hU.mem_nhds hz))]
  simp only [laplace0, hm]
  ring

/-- Multiplication by a complex constant commutes with the hyperbolic Laplacian. -/
theorem resolvent_laplace_const_mul {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 f U) (c : ℂ) {z : ℂ} (hz : z ∈ U) :
    laplace0 (fun u => c * f u) z = c * laplace0 f z := by
  have he : dzbar (fun u => c * f u) =ᶠ[𝓝 z] (fun u => c * dzbar f u) := by
    filter_upwards [hU.mem_nhds hz] with u hu
    rw [dzbar_mul (differentiableAt_const c)
      ((hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu))]
    simp [dzbar]
  have hm : dz (dzbar (fun u => c * f u)) z = c * dz (dzbar f) z := by
    have hd : dz (dzbar (fun u => c * f u)) z = dz (fun u => c * dzbar f u) z := by
      unfold dz
      rw [he.fderiv_eq (𝕜 := ℝ)]
    rw [hd, dz_mul (differentiableAt_const c)
      ((differentiableOn_dzbar_of_contDiffOn hU hf).differentiableAt (hU.mem_nhds hz))]
    simp [dz]
  simp only [laplace0, hm]
  ring

/-- The positive barrier diverging at the ideal boundary of the disk. -/
def resolventBarrier (z : ℂ) : ℝ := (1 + ‖z‖ ^ 2) / (1 - ‖z‖ ^ 2)

/-- Positivity of the barrier on the disk. -/
theorem resolventBarrier_pos {z : ℂ} (hz : z ∈ unitDisc) : 0 < resolventBarrier z := by
  have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  apply div_pos (by positivity)
  nlinarith [norm_nonneg z]

/-- Genuine smoothness of the barrier away from its boundary singularity. -/
theorem resolventBarrier_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) resolventBarrier unitDisc := by
  unfold resolventBarrier
  have hn : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => ‖z‖ ^ 2) unitDisc :=
    (contDiff_norm_sq ℝ).contDiffOn
  apply ContDiffOn.div (contDiffOn_const.add hn) (contDiffOn_const.sub hn)
  intro z hz
  have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hp : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  exact hp.ne'

/-- The barrier satisfies the same homogeneous equation with the memoir's
Laplacian normalization. -/
theorem resolventBarrier_equation {z : ℂ} (hz : z ∈ unitDisc) :
    laplace0 (fun u => (resolventBarrier u : ℂ)) z + (resolventBarrier z : ℂ) / 2 = 0 := by
  let F : ℝ → ℂ := fun s => (1 + (s : ℂ)) / (1 - (s : ℂ))
  have hn : (1 : ℂ) - (‖z‖ ^ 2 : ℝ) ≠ 0 := by
    have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hp : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    exact_mod_cast hp.ne'
  have ho : ContDiffAt ℝ 2 (fun s : ℝ => (s : ℂ)) (‖z‖ ^ 2) :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hF : ContDiffAt ℝ 2 F (‖z‖ ^ 2) := by
    convert ((contDiffAt_const (c := (1 : ℂ))).add ho).mul
      (((contDiffAt_const (c := (1 : ℂ))).sub ho).inv hn) using 1
    simp [F, div_eq_mul_inv]
  have hd (s : ℝ) (hs : (1 : ℂ) - s ≠ 0) : HasDerivAt F (2 / (1 - (s : ℂ)) ^ 2) s := by
    have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := (hasDerivAt_id (s : ℂ)).comp_ofReal
    have h := (hc.const_add 1).div (hc.const_sub 1) hs
    change HasDerivAt F _ s at h
    convert h using 1 <;> field_simp <;> ring
  have he : deriv F =ᶠ[𝓝 (‖z‖ ^ 2)] (fun s : ℝ => 2 / (1 - (s : ℂ)) ^ 2) := by
    have hev : ∀ᶠ s : ℝ in 𝓝 (‖z‖ ^ 2), (1 : ℂ) - s ≠ 0 :=
      (by fun_prop : ContinuousAt (fun s : ℝ => (1 : ℂ) - s) (‖z‖ ^ 2)).eventually_ne hn
    filter_upwards [hev] with s hs
    exact (hd s hs).deriv
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 (‖z‖ ^ 2) :=
    (hasDerivAt_id ((‖z‖ ^ 2 : ℝ) : ℂ)).comp_ofReal
  have hd2 := (hasDerivAt_const (‖z‖ ^ 2) (2 : ℂ)).div ((hc.const_sub 1).pow 2) (pow_ne_zero 2 hn)
  change HasDerivAt (fun s : ℝ => 2 / (1 - (s : ℂ)) ^ 2) _ (‖z‖ ^ 2) at hd2
  have hfun : (fun u => (resolventBarrier u : ℂ)) = (fun u => F (‖u‖ ^ 2)) := by
    funext u
    simp [resolventBarrier, F]
  unfold laplace0
  rw [hfun, tt_radial_wirtinger_second hF, (hd _ hn).deriv, he.deriv_eq, hd2.deriv]
  simp only [rho, resolventBarrier, Pi.pow_apply]
  push_cast
  field_simp
  ring

/-- A sufficiently large compact subdisk has barrier values exceeding any
prescribed bound on its boundary, while containing the chosen interior point. -/
theorem resolventBarrier_large_circle {x : ℂ} (hx : x ∈ unitDisc) (C : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, ‖x‖ < r ∧ r < 1 ∧ ∀ z : ℂ, ‖z‖ = r → C < ε * resolventBarrier z := by
  let A : ℝ := |C| + ε + 1
  let δ : ℝ := ε / (2 * A)
  have hA : 0 < A := by dsimp [A]; positivity
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hA)
  have hm : max ‖x‖ (1 - δ) < 1 :=
    max_lt (mem_ball_zero_iff.mp hx) (sub_lt_self 1 hδ)
  obtain ⟨r, hrl, hr⟩ := exists_between hm
  have hxr : ‖x‖ < r := lt_of_le_of_lt (le_max_left _ _) hrl
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg x) hxr
  have hrd : 1 - δ < r := lt_of_le_of_lt (le_max_right _ _) hrl
  have hp : 0 < 1 - r ^ 2 := by nlinarith
  have hgap : 1 - r ^ 2 < 2 * δ := by nlinarith [sq_nonneg (1 - r)]
  have hδeq : A * (2 * δ) = ε := by dsimp only [δ]; field_simp
  have hprod : A * (1 - r ^ 2) < ε := by
    have h := mul_lt_mul_of_pos_left hgap hA
    rwa [hδeq] at h
  have hCA : C ≤ A := by dsimp [A]; linarith [le_abs_self C]
  have hbound : C * (1 - r ^ 2) < ε * (1 + r ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hCA hp.le
    nlinarith [sq_nonneg r]
  refine ⟨r, hxr, hr, ?_⟩
  intro z hz
  rw [resolventBarrier, hz, ← mul_div_assoc]
  exact (lt_div_iff₀ hp).mpr hbound

/-- A bounded C2 homogeneous solution has nonpositive real component on the disk.
The proof uses an interior maximum after subtracting a small divergent barrier. -/
theorem resolvent_homogeneous_re_nonpos_disc {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 f unitDisc) (hb : ∃ C : ℝ, ∀ z ∈ unitDisc, ‖f z‖ ≤ C)
    (he : ∀ z ∈ unitDisc, laplace0 f z + f z / 2 = 0) :
    ∀ x ∈ unitDisc, (f x).re ≤ 0 := by
  intro x hx
  by_contra hn
  have hpos : 0 < (f x).re := lt_of_not_ge hn
  have hBx := resolventBarrier_pos hx
  let ε : ℝ := (f x).re / (2 * resolventBarrier x)
  have hε : 0 < ε := div_pos hpos (mul_pos (by norm_num) hBx)
  have hεeq : ε * resolventBarrier x = (f x).re / 2 := by
    dsimp only [ε]
    field_simp
  obtain ⟨C, hC⟩ := hb
  obtain ⟨r, hxr, hr, hbound⟩ := resolventBarrier_large_circle hx C hε
  let H : ℂ → ℂ := fun z => f z - (ε : ℂ) * (resolventBarrier z : ℂ)
  have hB : ContDiffOn ℝ 2 (fun z => (resolventBarrier z : ℂ)) unitDisc := by
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn resolventBarrier_contDiffOn).of_le (by norm_num)
  have hH : ContDiffOn ℝ 2 H unitDisc := hf.sub (contDiffOn_const.mul hB)
  have hxpos : 0 < (H x).re := by
    simp only [H, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    linarith
  have hsub : closedBall (0 : ℂ) r ⊆ unitDisc := by
    intro z hz
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hr)
  have hcont : ContinuousOn (fun z => (H z).re) (closedBall (0 : ℂ) r) :=
    Complex.continuous_re.comp_continuousOn (hH.continuousOn.mono hsub)
  have hxclosed : x ∈ closedBall (0 : ℂ) r := mem_closedBall_zero_iff.mpr hxr.le
  obtain ⟨y, hy, hmax⟩ := (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn ⟨x, hxclosed⟩ hcont
  have hypos : 0 < (H y).re := lt_of_lt_of_le hxpos (hmax hxclosed)
  have hyin : y ∈ ball (0 : ℂ) r := by
    by_contra hnot
    have hyn : ‖y‖ = r := le_antisymm (mem_closedBall_zero_iff.mp hy)
      (le_of_not_gt (fun h => hnot (mem_ball_zero_iff.mpr h)))
    have hfy : (f y).re ≤ C := (Complex.re_le_norm _).trans (hC y (hsub hy))
    have hby := hbound y hyn
    have hval : (H y).re = (f y).re - ε * resolventBarrier y := by
      simp [H, Complex.mul_re]
    rw [hval] at hypos
    linarith
  have hloc : IsLocalMax (fun z => (H z).re) y :=
    hmax.isLocalMax (mem_of_superset (isOpen_ball.mem_nhds hyin) ball_subset_closedBall)
  have hmix := resolvent_mixed_re_nonpos_at_max (hH.contDiffAt (isOpen_ball.mem_nhds (hsub hy))) hloc
  have hρ : 0 < rho y := by
    have hyn : ‖y‖ < 1 := mem_ball_zero_iff.mp (hsub hy)
    have hden : 1 - ‖y‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg y]
    exact div_pos (by norm_num) (sq_pos_of_ne_zero hden)
  have hlap : 0 ≤ (laplace0 H y).re := by
    unfold laplace0
    rw [show (rho y : ℂ)⁻¹ = ((rho y)⁻¹ : ℝ) by simp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hρ.le) hmix)
  have hPDE : laplace0 H y + H y / 2 = 0 := by
    dsimp only [H]
    rw [resolvent_laplace_sub isOpen_ball hf (contDiffOn_const.mul hB) (hsub hy),
      resolvent_laplace_const_mul isOpen_ball hB (ε : ℂ) (hsub hy)]
    have hfEq := he y (hsub hy)
    have hbEq := resolventBarrier_equation (hsub hy)
    linear_combination hfEq - (ε : ℂ) * hbEq
  have hreal := congrArg Complex.re hPDE
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.zero_re] at hreal
  linarith

/-- Uniqueness of bounded homogeneous solutions on the disk, the independent
uniqueness ingredient for RK3 (TT:1112–1124). Only C2 regularity is needed. -/
theorem resolvent_homogeneous_unique_disc_C2 {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 f unitDisc) (hb : ∃ C : ℝ, ∀ z ∈ unitDisc, ‖f z‖ ≤ C)
    (he : ∀ z ∈ unitDisc, laplace0 f z + f z / 2 = 0) : EqOn f (fun _ => 0) unitDisc := by
  intro z hz
  let c : ℂ := conj (f z)
  have hc : ContDiffOn ℝ 2 (fun u => c * f u) unitDisc := contDiffOn_const.mul hf
  have hcb : ∃ C : ℝ, ∀ u ∈ unitDisc, ‖c * f u‖ ≤ C := by
    obtain ⟨C, hC⟩ := hb
    refine ⟨‖c‖ * C, ?_⟩
    intro u hu
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC u hu) (norm_nonneg c)
  have hce : ∀ u ∈ unitDisc, laplace0 (fun v => c * f v) u + (c * f u) / 2 = 0 := by
    intro u hu
    rw [resolvent_laplace_const_mul isOpen_ball hf c hu]
    linear_combination c * he u hu
  have h := resolvent_homogeneous_re_nonpos_disc hc hcb hce z hz
  have hn : (c * f z).re = ‖f z‖ ^ 2 := by
    dsimp only [c]
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [hn] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (f z)])

/-- Bounded smooth homogeneous resolvent uniqueness in the memoir's BCinf space.
The conclusion is restricted to the disk; no exterior puncture is filled in. -/
theorem resolvent_homogeneous_unique_disc {f : ℂ → ℂ} (hf : f ∈ BCinf unitDisc)
    (he : ∀ z ∈ unitDisc, laplace0 f z + f z / 2 = 0) : EqOn f (fun _ => 0) unitDisc :=
  resolvent_homogeneous_unique_disc_C2 (hf.1.of_le (by norm_num)) hf.2 he


/-- Maximum principle with a positive supersolution that dominates at the
boundary of compact exhaustion sets. This does not fill missing points. -/
theorem resolvent_re_nonpos_of_barrier {U : Set ℂ} (hU : IsOpen U)
    (hρ : ∀ z ∈ U, 0 < rho z) {B : ℂ → ℝ}
    (hB : ContDiffOn ℝ 2 B U) (hBpos : ∀ z ∈ U, 0 < B z)
    (hBL : ∀ z ∈ U, 0 ≤ (laplace0 (fun u => (B u : ℂ)) z + (B z : ℂ) / 2).re)
    (hlarge : ∀ x ∈ U, ∀ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ x ∈ K ∧
        ∀ z ∈ K, z ∉ interior K → C < ε * B z)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ 2 f U)
    (hb : ∃ C : ℝ, ∀ z ∈ U, ‖f z‖ ≤ C)
    (he : ∀ z ∈ U, laplace0 f z + f z / 2 = 0) : ∀ x ∈ U, (f x).re ≤ 0 := by
  intro x hx
  by_contra hn
  have hpos : 0 < (f x).re := lt_of_not_ge hn
  let ε : ℝ := (f x).re / (2 * B x)
  have hε : 0 < ε := div_pos hpos (mul_pos (by norm_num) (hBpos x hx))
  have hεeq : ε * B x = (f x).re / 2 := by
    have hn := (hBpos x hx).ne'
    dsimp only [ε]
    field_simp
  obtain ⟨C, hC⟩ := hb
  obtain ⟨K, hK, hKU, hxK, hbound⟩ := hlarge x hx C ε hε
  let H : ℂ → ℂ := fun z => f z - (ε : ℂ) * (B z : ℂ)
  have hBc : ContDiffOn ℝ 2 (fun z => (B z : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hB
  have hH : ContDiffOn ℝ 2 H U := hf.sub (contDiffOn_const.mul hBc)
  have hxpos : 0 < (H x).re := by
    simp only [H, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    linarith
  have hcont : ContinuousOn (fun z => (H z).re) K :=
    Complex.continuous_re.comp_continuousOn (hH.continuousOn.mono hKU)
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x, hxK⟩ hcont
  have hypos : 0 < (H y).re := lt_of_lt_of_le hxpos (hmax hxK)
  have hyin : y ∈ interior K := by
    by_contra hnot
    have hfy : (f y).re ≤ C := (Complex.re_le_norm _).trans (hC y (hKU hy))
    have hby := hbound y hy hnot
    have hval : (H y).re = (f y).re - ε * B y := by simp [H, Complex.mul_re]
    rw [hval] at hypos
    linarith
  have hloc : IsLocalMax (fun z => (H z).re) y :=
    hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hyin)
  have hmix := resolvent_mixed_re_nonpos_at_max (hH.contDiffAt (hU.mem_nhds (hKU hy))) hloc
  have hlap : 0 ≤ (laplace0 H y).re := by
    unfold laplace0
    rw [show (rho y : ℂ)⁻¹ = ((rho y)⁻¹ : ℝ) by simp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (hρ y (hKU hy)).le) hmix)
  have hcalc : laplace0 H y + H y / 2 =
      -(ε : ℂ) * (laplace0 (fun u => (B u : ℂ)) y + (B y : ℂ) / 2) := by
    dsimp only [H]
    rw [resolvent_laplace_sub hU hf (contDiffOn_const.mul hBc) (hKU hy),
      resolvent_laplace_const_mul hU hBc (ε : ℂ) (hKU hy)]
    linear_combination he y (hKU hy)
  have hreal := congrArg Complex.re hcalc
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im, neg_zero, zero_mul, sub_zero] at hreal
  have hsign := hBL y (hKU hy)
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re] at hsign
  nlinarith

/-- The real logarithm of the norm is smooth away from the origin. -/
theorem resolvent_log_norm_contDiffAt {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℂ => Real.log ‖u‖) z := by
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have h := (((contDiff_norm_sq ℝ (n := (⊤ : ℕ∞))).contDiffAt).log hn).div_const 2
  convert h using 1
  funext u
  rw [Real.log_pow]
  ring

/-- The logarithmic pole is harmonic off the origin for the memoir's Laplacian. -/
theorem resolvent_laplace_log_norm {z : ℂ} (hz : z ≠ 0) :
    laplace0 (fun u : ℂ => (Real.log ‖u‖ : ℂ)) z = 0 := by
  let F : ℝ → ℂ := fun s => ((Real.log s / 2 : ℝ) : ℂ)
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hF : ContDiffAt ℝ 2 F (‖z‖ ^ 2) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((Real.contDiffAt_log.mpr hn).div_const 2)
  have hd (s : ℝ) (hs : s ≠ 0) : HasDerivAt F ((s⁻¹ / 2 : ℝ) : ℂ) s :=
    ((Real.hasDerivAt_log hs).div_const 2).ofReal_comp
  have he : deriv F =ᶠ[𝓝 (‖z‖ ^ 2)] (fun s : ℝ => ((s⁻¹ / 2 : ℝ) : ℂ)) := by
    filter_upwards [eventually_ne_nhds hn] with s hs
    exact (hd s hs).deriv
  have hd2 := (((hasDerivAt_id (‖z‖ ^ 2)).inv hn).div_const 2).ofReal_comp
  change HasDerivAt (fun s : ℝ => ((s⁻¹ / 2 : ℝ) : ℂ)) _ (‖z‖ ^ 2) at hd2
  have hfun : (fun u : ℂ => (Real.log ‖u‖ : ℂ)) = (fun u => F (‖u‖ ^ 2)) := by
    funext u
    simp [F, Real.log_pow]
  unfold laplace0
  rw [hfun, tt_radial_wirtinger_second hF, (hd _ hn).deriv, he.deriv_eq, hd2.deriv]
  simp only [id_eq]
  push_cast
  have hnc : ((‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  field_simp
  ring

/-- A barrier divergent both at zero and at the unit circle. -/
def resolventPuncturedBarrier (z : ℂ) : ℝ := resolventBarrier z - Real.log ‖z‖

theorem resolventPuncturedBarrier_contDiffOn :
    ContDiffOn ℝ 2 resolventPuncturedBarrier (unitDisc \ {0}) := by
  apply (resolventBarrier_contDiffOn.of_le (by norm_num)).mono sdiff_subset |>.sub
  intro z hz
  exact ((resolvent_log_norm_contDiffAt (by simpa using hz.2)).of_le (by norm_num)).contDiffWithinAt

theorem resolventPuncturedBarrier_pos {z : ℂ} (hz : z ∈ unitDisc \ {0}) :
    0 < resolventPuncturedBarrier z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using hz.2)
  have hl := Real.log_neg hn (mem_ball_zero_iff.mp hz.1)
  have hb := resolventBarrier_pos hz.1
  dsimp only [resolventPuncturedBarrier]
  linarith

/-- The proposed punctured barrier is a supersolution: its defect is
`-log |z| / 2`, which is positive on the punctured disk. -/
theorem resolventPuncturedBarrier_equation {z : ℂ} (hz : z ∈ unitDisc \ {0}) :
    laplace0 (fun u => (resolventPuncturedBarrier u : ℂ)) z +
      (resolventPuncturedBarrier z : ℂ) / 2 = -(Real.log ‖z‖ : ℂ) / 2 := by
  have hU : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hB : ContDiffOn ℝ 2 (fun u => (resolventBarrier u : ℂ)) (unitDisc \ {0}) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (resolventBarrier_contDiffOn.of_le (by norm_num))).mono sdiff_subset
  have hL : ContDiffOn ℝ 2 (fun u => (Real.log ‖u‖ : ℂ)) (unitDisc \ {0}) := by
    intro u hu
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp u
      ((resolvent_log_norm_contDiffAt (by simpa using hu.2)).of_le (by norm_num))).contDiffWithinAt
  have hfun : (fun u => (resolventPuncturedBarrier u : ℂ)) =
      (fun u => (resolventBarrier u : ℂ) - (Real.log ‖u‖ : ℂ)) := by funext u; simp [resolventPuncturedBarrier]
  rw [hfun, resolvent_laplace_sub hU hB hL hz,
    resolvent_laplace_log_norm (by simpa using hz.2)]
  have hb := resolventBarrier_equation hz.1
  simp only [resolventPuncturedBarrier, Complex.ofReal_sub]
  linear_combination hb

/-- Compact annuli contain any prescribed point and have punctured-barrier
values exceeding a given bound on both boundary circles. -/
theorem resolventPuncturedBarrier_exhaustion (x : ℂ) (hx : x ∈ unitDisc \ {0})
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ unitDisc \ {0} ∧ x ∈ K ∧
      ∀ z ∈ K, z ∉ interior K → C < ε * resolventPuncturedBarrier z := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr (by simpa using hx.2)
  obtain ⟨r, hxr, hr, houter⟩ := resolventBarrier_large_circle hx.1 C hε
  let δ : ℝ := min (‖x‖ / 2) (Real.exp (-(|C| / ε + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (Real.exp_pos _)
  have hδx : δ < ‖x‖ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ1 : δ < 1 := lt_trans hδx (mem_ball_zero_iff.mp hx.1)
  have hlog : Real.log δ ≤ -(|C| / ε + 1) := by
    have h := Real.log_le_log hδ (min_le_right (‖x‖ / 2) (Real.exp (-(|C| / ε + 1))))
    simpa only [Real.log_exp] using h
  have hinner (z : ℂ) (hz : ‖z‖ = δ) : C < ε * resolventPuncturedBarrier z := by
    have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr (hz.trans_lt hδ1)
    have hBz := resolventBarrier_pos hzD
    have hm := mul_le_mul_of_nonneg_left (neg_le_neg hlog) hε.le
    have heps : ε * (|C| / ε + 1) = |C| + ε := by field_simp
    simp only [neg_neg] at hm
    rw [heps] at hm
    dsimp only [resolventPuncturedBarrier]
    rw [hz]
    nlinarith [le_abs_self C, mul_pos hε hBz]
  let K : Set ℂ := {z | δ ≤ ‖z‖} ∩ closedBall (0 : ℂ) r
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) r).inter_left
    (isClosed_le continuous_const continuous_norm)
  have hKU : K ⊆ unitDisc \ {0} := by
    intro z hz
    refine ⟨mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz.2) hr), ?_⟩
    have hn : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ hz.1)
    simpa using hn
  refine ⟨K, hK, hKU, ⟨hδx.le, mem_closedBall_zero_iff.mpr hxr.le⟩, ?_⟩
  intro z hz hnot
  by_cases hin : ‖z‖ = δ
  · exact hinner z hin
  by_cases hout : ‖z‖ = r
  · have h := houter z hout
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using (hKU hz).2)
    have hl := Real.log_neg hn (mem_ball_zero_iff.mp (hKU hz).1)
    dsimp only [resolventPuncturedBarrier]
    nlinarith [mul_pos hε (neg_pos.mpr hl)]
  exfalso
  apply hnot
  have hl : δ < ‖z‖ := lt_of_le_of_ne hz.1 (Ne.symm hin)
  have hu : ‖z‖ < r := lt_of_le_of_ne (mem_closedBall_zero_iff.mp hz.2) hout
  have hO : IsOpen ({u : ℂ | δ < ‖u‖} ∩ ball (0 : ℂ) r) :=
    (isOpen_lt continuous_const continuous_norm).inter isOpen_ball
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset (hO.mem_nhds ⟨hl, mem_ball_zero_iff.mpr hu⟩)
  intro u hu
  exact ⟨(show δ < ‖u‖ from hu.1).le, ball_subset_closedBall hu.2⟩

/-- Bounded C2 homogeneous solutions vanish on the punctured disk. The proof
uses two boundary circles and does not assume a removable singularity. -/
theorem resolvent_homogeneous_unique_punctured_disc_C2 {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 f (unitDisc \ {0}))
    (hb : ∃ C : ℝ, ∀ z ∈ unitDisc \ {0}, ‖f z‖ ≤ C)
    (he : ∀ z ∈ unitDisc \ {0}, laplace0 f z + f z / 2 = 0) :
    EqOn f (fun _ => 0) (unitDisc \ {0}) := by
  have hU : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hρ : ∀ z ∈ unitDisc \ {0}, 0 < rho z := by
    intro z hz
    have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz.1
    have hd : 1 - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
    exact div_pos (by norm_num) (sq_pos_of_ne_zero hd)
  have hBL : ∀ z ∈ unitDisc \ {0},
      0 ≤ (laplace0 (fun u => (resolventPuncturedBarrier u : ℂ)) z +
        (resolventPuncturedBarrier z : ℂ) / 2).re := by
    intro z hz
    rw [resolventPuncturedBarrier_equation hz]
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re]
    exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos (norm_nonneg z) (mem_ball_zero_iff.mp hz.1).le))
      (by norm_num)
  intro z hz
  let c : ℂ := conj (f z)
  have hc : ContDiffOn ℝ 2 (fun u => c * f u) (unitDisc \ {0}) := contDiffOn_const.mul hf
  have hcb : ∃ C : ℝ, ∀ u ∈ unitDisc \ {0}, ‖c * f u‖ ≤ C := by
    obtain ⟨C, hC⟩ := hb
    refine ⟨‖c‖ * C, ?_⟩
    intro u hu
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC u hu) (norm_nonneg c)
  have hce : ∀ u ∈ unitDisc \ {0}, laplace0 (fun v => c * f v) u + (c * f u) / 2 = 0 := by
    intro u hu
    rw [resolvent_laplace_const_mul hU hf c hu]
    linear_combination c * he u hu
  have h := resolvent_re_nonpos_of_barrier hU hρ resolventPuncturedBarrier_contDiffOn
    (fun u hu => resolventPuncturedBarrier_pos hu) hBL resolventPuncturedBarrier_exhaustion hc hcb hce z hz
  have hn : (c * f z).re = ‖f z‖ ^ 2 := by
    dsimp only [c]
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [hn] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (f z)])

theorem resolvent_homogeneous_unique_punctured_disc {f : ℂ → ℂ}
    (hf : f ∈ BCinf (unitDisc \ {0}))
    (he : ∀ z ∈ unitDisc \ {0}, laplace0 f z + f z / 2 = 0) :
    EqOn f (fun _ => 0) (unitDisc \ {0}) :=
  resolvent_homogeneous_unique_punctured_disc_C2 (hf.1.of_le (by norm_num)) hf.2 he

/-- Exterior uniqueness is transported from the punctured disk by inversion,
using density covariance and retaining the missing center throughout (RK3). -/
theorem resolvent_homogeneous_unique_exterior_C2 {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ 2 f unitDiscExterior)
    (hb : ∃ C : ℝ, ∀ z ∈ unitDiscExterior, ‖f z‖ ≤ C)
    (he : ∀ z ∈ unitDiscExterior, laplace0 f z + f z / 2 = 0) :
    EqOn f (fun _ => 0) unitDiscExterior := by
  let U : Set ℂ := unitDisc \ {0}
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hz0 (z : ℂ) (hz : z ∈ U) : z ≠ 0 := by simpa using hz.2
  have hm : MapsTo (fun z : ℂ => z⁻¹) U unitDiscExterior := by
    intro z hz
    change 1 < ‖z⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr (hz0 z hz))).mpr (mem_ball_zero_iff.mp hz.1)
  have hi : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) U := by
    intro z hz
    exact (differentiableAt_inv (hz0 z hz)).differentiableWithinAt
  have hic : ContDiffOn ℝ 2 (fun z : ℂ => z⁻¹) U :=
    contDiffOn_id.inv hz0
  have hfc : ContDiffOn ℝ 2 (f ∘ fun z : ℂ => z⁻¹) U := hf.comp hic hm
  have hfb : ∃ C : ℝ, ∀ z ∈ U, ‖(f ∘ fun u : ℂ => u⁻¹) z‖ ≤ C := by
    obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun z hz => hC z⁻¹ (hm hz)⟩
  have hfe : ∀ z ∈ U, laplace0 (f ∘ fun u : ℂ => u⁻¹) z + (f ∘ fun u : ℂ => u⁻¹) z / 2 = 0 := by
    intro z hz
    have hρ : rho z ≠ 0 := div_ne_zero (by norm_num)
      (pow_ne_zero 2 (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz.1))
    rw [laplace0_comp_of_density_pullback hU resolvent_exterior_isOpen hi hm hf hz hρ
      (rho_inv_jacobian (hz0 z hz))]
    exact he z⁻¹ (hm hz)
  have huniq := resolvent_homogeneous_unique_punctured_disc_C2 hfc hfb hfe
  intro z hz
  have hzn : 1 < ‖z‖ := hz
  have hiU : z⁻¹ ∈ U := by
    refine ⟨mem_ball_zero_iff.mpr ?_, ?_⟩
    · rw [norm_inv]
      exact (inv_lt_one₀ (lt_trans zero_lt_one hzn)).mpr hzn
    · simpa using inv_ne_zero (resolvent_exterior_ne_zero hz)
  simpa only [Function.comp_apply, inv_inv] using huniq hiU

/-- The exterior BCinf uniqueness clause, without a hypothesis at infinity. -/
theorem resolvent_homogeneous_unique_exterior {f : ℂ → ℂ} (hf : f ∈ BCinf unitDiscExterior)
    (he : ∀ z ∈ unitDiscExterior, laplace0 f z + f z / 2 = 0) :
    EqOn f (fun _ => 0) unitDiscExterior :=
  resolvent_homogeneous_unique_exterior_C2 (hf.1.of_le (by norm_num)) hf.2 he

end TakhtajanTeo
