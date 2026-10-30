import TakhtajanTeo.Ch1.S5_ChernForms
import TakhtajanTeo.Ch1.HarmonicPVCayley
import TakhtajanTeo.Ch1.HarmonicPVCutoff
import TakhtajanTeo.Ch1.HarmonicMixedIdentity
import LiZhongQC.Lemmas.GreenPolar

/-!
# Chapter 1, §6 — First and second variations of the hyperbolic metric (TT:2548–2674)

The model is `ℍ² ≅ 𝕌`. The hyperbolic density is `ρ(z) = y⁻²` there, and `ρ^{εμ} = w_{εμ}^*(ρ)`.

* Lemma 6.1 (Ahlfors: `L_μ ρ = 0`)
* Proposition 6.3 (`L_μ L_{μ̄} ρ = ρ G(|μ|²)`), with (6.1)–(6.5) and the regularized representation
* Corollary 6.4, Remark 6.5 (polarization)

**Modelling.**
- On `𝕌` the resolvent kernel is (1.19) with the point-pair invariant `u(z, w) = |z - w|²/(4 Im z Im w)`. This is
  the `𝕌` form of `u` on `𝔻`; in both cases `u = (cosh d - 1)/2`.
- `Δ₀ = -ρ⁻¹ ∂_z ∂_{z̄}`.

**Corrections.**
- Corollary 6.4 (TT:2662) says `μ, ν ∈ Ω^{-1,1}(𝔻*)`, but all its integrals are over `𝕌`. It is stated for
  `μ, ν ∈ Ω^{-1,1}(𝕌)`.

Remarks 6.2 and 6.6 (TT:2574, 2674) are citations of [Wol86] and are not stated.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The hyperbolic density `ρ(z) = y⁻²` on `𝕌` (TT:2550). -/
def rhoU (z : ℂ) : ℝ := (z.im ^ 2)⁻¹

/-- The point-pair invariant on `𝕌`: `u(z, w) = |z - w|²/(4 Im z Im w)`. -/
def pointPairU (z w : ℂ) : ℝ := ‖z - w‖ ^ 2 / (4 * z.im * w.im)

/-- The resolvent kernel (1.19) of `G = ½(Δ₀ + ½)⁻¹` on `𝕌`. -/
def resolventKernelU (z w : ℂ) : ℝ :=
  (2 * pointPairU z w + 1) / (2 * π) * Real.log ((pointPairU z w + 1) / pointPairU z w) - 1 / π

/-- The disk boundary factor under the Cayley map, used to transfer (1.19) to
the upper-half-plane model in §6 (TT:1083–1089, TT:2550). -/
theorem rhoU_cayley_boundary_factor {z : ℂ} (hz : z ∈ upperHalf) :
    1 - ‖cayley z‖ ^ 2 = 4 * z.im / Complex.normSq (z + I) := by
  have hn := Complex.normSq_pos.mpr (cayley_den_ne_zero hz)
  rw [← Complex.normSq_eq_norm_sq, cayley, Complex.normSq_div,
    eq_div_iff hn.ne', sub_mul, one_mul, div_mul_cancel₀ _ hn.ne']
  exact normSq_cayley_key z

/-- Difference of Cayley coordinates in the upper-half-plane model (TT:1089, TT:2550). -/
theorem rhoU_cayley_sub {z w : ℂ} (hz : z ∈ upperHalf) (hw : w ∈ upperHalf) :
    cayley z - cayley w = 2 * I * (z - w) / ((z + I) * (w + I)) := by
  have hzd := cayley_den_ne_zero hz
  have hwd := cayley_den_ne_zero hw
  unfold cayley
  field_simp
  ring

/-- The point-pair invariant is the same in the disk and upper-half-plane models
under Cayley coordinates (TT:1089, TT:2550). -/
theorem pointPairU_cayley {z w : ℂ} (hz : z ∈ upperHalf) (hw : w ∈ upperHalf) :
    pointPair (cayley z) (cayley w) = pointPairU z w := by
  have hzn := (Complex.normSq_pos.mpr (cayley_den_ne_zero hz)).ne'
  have hwn := (Complex.normSq_pos.mpr (cayley_den_ne_zero hw)).ne'
  have hzi : z.im ≠ 0 := ne_of_gt hz
  have hwi : w.im ≠ 0 := ne_of_gt hw
  have hnorm : ‖cayley z - cayley w‖ ^ 2 =
      4 * ‖z - w‖ ^ 2 / (Complex.normSq (z + I) * Complex.normSq (w + I)) := by
    rw [rhoU_cayley_sub hz hw]
    simp only [norm_div, norm_mul, Complex.norm_I, mul_pow, div_pow,
      Complex.normSq_eq_norm_sq]
    norm_num
  unfold pointPair pointPairU
  rw [rhoU_cayley_boundary_factor hz, rhoU_cayley_boundary_factor hw, hnorm]
  field_simp

/-- The resolvent kernel (1.19) transfers exactly under the Cayley map; the
totalized diagonal values also agree (TT:1083–1089, TT:2550). -/
theorem resolventKernelU_cayley {z w : ℂ} (hz : z ∈ upperHalf) (hw : w ∈ upperHalf) :
    resolventKernel (cayley z) (cayley w) = resolventKernelU z w := by
  simp only [resolventKernel, resolventKernelU, pointPairU_cayley hz hw]

/-- The derivative of the existing Cayley map, for the density transfer in §6
(TT:2550–2563). -/
theorem rhoU_hasDerivAt_cayley {z : ℂ} (hz : z ∈ upperHalf) :
    HasDerivAt cayley (2 * I / (z + I) ^ 2) z := by
  have h := ((hasDerivAt_id z).sub_const I).div ((hasDerivAt_id z).add_const I)
    (cayley_den_ne_zero hz)
  convert h using 1
  · rfl
  · simp only [id_eq]
    ring

/-- The Poincaré density transforms from the disk to the upper half-plane with
the squared derivative Jacobian (TT:2550–2563). -/
theorem rhoU_cayley_pullback {z : ℂ} (hz : z ∈ upperHalf) :
    rho (cayley z) * ‖deriv cayley z‖ ^ 2 = rhoU z := by
  have hzn := (Complex.normSq_pos.mpr (cayley_den_ne_zero hz)).ne'
  have hzi : z.im ≠ 0 := ne_of_gt hz
  have hd := (rhoU_hasDerivAt_cayley hz).deriv
  have hn : ‖2 * I / (z + I) ^ 2‖ ^ 2 = 4 / (Complex.normSq (z + I)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_div]
    simp only [map_pow, Complex.normSq_mul, Complex.normSq_ofNat, Complex.normSq_I]
    norm_num
  rw [hd, hn]
  unfold rho rhoU
  rw [rhoU_cayley_boundary_factor hz]
  field_simp

/-- The holomorphic Wirtinger chain rule under Cayley coordinates
(TT:2550–2563). -/
theorem rhoU_dz_comp_cayley {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ upperHalf)
    (hf : DifferentiableAt ℝ f (cayley z)) :
    dz (f ∘ cayley) z = dz f (cayley z) * deriv cayley z := by
  have hc := (rhoU_hasDerivAt_cayley hz).differentiableAt
  rw [eq6_2_dz_comp (hc.restrictScalars ℝ) hf,
    dz_eq_deriv hc, dz_conj (hc.restrictScalars ℝ), (cauchyRiemann_iff.mp hc).2]
  simp

/-- The antiholomorphic Wirtinger chain rule under Cayley coordinates
(TT:2550–2563). -/
theorem rhoU_dzbar_comp_cayley {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ upperHalf)
    (hf : DifferentiableAt ℝ f (cayley z)) :
    dzbar (f ∘ cayley) z = dzbar f (cayley z) * conj (deriv cayley z) := by
  have hc := (rhoU_hasDerivAt_cayley hz).differentiableAt
  rw [eq6_2_dzbar_comp (hc.restrictScalars ℝ) hf,
    (cauchyRiemann_iff.mp hc).2, dzbar_conj (hc.restrictScalars ℝ), dz_eq_deriv hc]
  simp

/-- A C2 function on the disk has a differentiable antiholomorphic Wirtinger
derivative there, as needed for the model change in §6 (TT:2550–2563). -/
theorem rhoU_differentiableOn_dzbar {f : ℂ → ℂ} (hf : ContDiffOn ℝ 2 f unitDisc) :
    DifferentiableOn ℝ (dzbar f) unitDisc := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ f) unitDisc :=
    hf.fderiv_of_isOpen isOpen_ball (by norm_num)
  have h1 := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hI := hd.clm_apply (contDiffOn_const (c := I))
  have hb : ContDiffOn ℝ 1 (dzbar f) unitDisc :=
    (h1.add (contDiffOn_const.mul hI)).div_const 2
  exact hb.differentiableOn one_ne_zero

/-- The mixed Wirtinger derivative transforms by the squared derivative
Jacobian under Cayley coordinates (TT:2550–2563). -/
theorem rhoU_dz_dzbar_comp_cayley {f : ℂ → ℂ} (hf : ContDiffOn ℝ 2 f unitDisc)
    {z : ℂ} (hz : z ∈ upperHalf) :
    dz (dzbar (f ∘ cayley)) z = dz (dzbar f) (cayley z) * (‖deriv cayley z‖ ^ 2 : ℝ) := by
  have hc := (rhoU_hasDerivAt_cayley hz).differentiableAt
  have hfc : DifferentiableAt ℝ (dzbar f) (cayley z) :=
    (rhoU_differentiableOn_dzbar hf).differentiableAt
      (isOpen_ball.mem_nhds (cayley_mem_unitDisc hz))
  have hdc : DifferentiableAt ℂ (deriv cayley) z :=
    (isConformalOnto_cayley.1.deriv isOpen_upperHalf).differentiableAt
      (isOpen_upperHalf.mem_nhds hz)
  have heq : dzbar (f ∘ cayley) =ᶠ[𝓝 z]
      (fun w => dzbar f (cayley w) * conj (deriv cayley w)) := by
    filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
    exact rhoU_dzbar_comp_cayley hw
      ((hf.differentiableOn (by norm_num)).differentiableAt
        (isOpen_ball.mem_nhds (cayley_mem_unitDisc hw)))
  have hd : dz (dzbar (f ∘ cayley)) z =
      dz (fun w => dzbar f (cayley w) * conj (deriv cayley w)) z := by
    unfold dz
    rw [heq.fderiv_eq (𝕜 := ℝ)]
  have hcomp : DifferentiableAt ℝ (fun w => dzbar f (cayley w)) z :=
    hfc.comp z (hc.restrictScalars ℝ)
  have hconj : DifferentiableAt ℝ (fun w => conj (deriv cayley w)) z :=
    Complex.differentiable_conj.differentiableAt.comp z (hdc.restrictScalars ℝ)
  rw [hd, dz_mul hcomp hconj,
    dz_conj (hdc.restrictScalars ℝ), (cauchyRiemann_iff.mp hdc).2]
  simp only [map_zero, mul_zero, zero_add]
  have hchain : dz (fun w => dzbar f (cayley w)) z =
      dz (dzbar f) (cayley z) * deriv cayley z := rhoU_dz_comp_cayley hz hfc
  rw [hchain]
  calc
    _ = dz (dzbar f) (cayley z) * (deriv cayley z * conj (deriv cayley z)) := by ring
    _ = _ := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Hyperbolic Laplacian covariance from the disk to the upper half-plane for
C2 functions, using the density and mixed-derivative transformations
(TT:1083, TT:2550–2563). -/
theorem rhoU_laplace_cayley {f : ℂ → ℂ} (hf : ContDiffOn ℝ 2 f unitDisc)
    {z : ℂ} (hz : z ∈ upperHalf) :
    -((rhoU z : ℂ)⁻¹ * dz (dzbar (f ∘ cayley)) z) = laplace0 f (cayley z) := by
  have hu : (rhoU z : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact inv_ne_zero (pow_ne_zero 2 (ne_of_gt hz))
  have hr : (rho (cayley z) : ℂ) * (‖deriv cayley z‖ ^ 2 : ℝ) = (rhoU z : ℂ) := by
    exact_mod_cast rhoU_cayley_pullback hz
  have hp : (rho (cayley z) : ℂ) * (‖deriv cayley z‖ ^ 2 : ℝ) ≠ 0 := by
    rw [hr]
    exact hu
  have hρ := (mul_ne_zero_iff.mp hp).1
  have hd := (mul_ne_zero_iff.mp hp).2
  rw [rhoU_dz_dzbar_comp_cayley hf hz, ← hr]
  unfold laplace0
  field_simp

/-- Positivity of the upper-half-plane point-pair invariant off the diagonal
(TT:1089, TT:2550). -/
theorem pointPairU_pos {z w : ℂ} (hz : z ∈ upperHalf) (hw : w ∈ upperHalf) (hzw : z ≠ w) :
    0 < pointPairU z w := by
  exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzw)))
    (mul_pos (mul_pos (by norm_num) hz) hw)

/-- RK2 in the upper-half-plane model of §6 (TT:1100, TT:2550). -/
theorem resolventKernelU_pos {z w : ℂ} (hz : z ∈ upperHalf) (hw : w ∈ upperHalf) (hzw : z ≠ w) :
    0 < resolventKernelU z w := by
  exact resolvent_scalar_pos (pointPairU_pos hz hw hzw)

/-- The density/Jacobian identity with a complex integrand factor (TT:2550–2563). -/
theorem rhoU_cayley_weight (c : ℂ) {z : ℂ} (hz : z ∈ upperHalf) :
    (‖deriv cayley z‖ ^ 2 : ℝ) • (c * (rho (cayley z) : ℂ)) = c * (rhoU z : ℂ) := by
  calc
    _ = c * ((rho (cayley z) * ‖deriv cayley z‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.real_smul, Complex.ofReal_mul]
      ring
    _ = _ := congrArg (fun r : ℝ => c * (r : ℂ)) (rhoU_cayley_pullback hz)

/-- Weighted area change from the disk to the upper half-plane, using the existing
conformal change-of-variables theorem (TT:2550–2563). -/
theorem rhoU_integral_cayley (f : ℂ → ℂ) :
    (∫ z in unitDisc, f z * (rho z : ℂ)) =
      ∫ w in upperHalf, f (cayley w) * (rhoU w : ℂ) := by
  have h := ahP_integral_image isOpen_upperHalf isConformalOnto_cayley.1
    isConformalOnto_cayley.2.1 (fun z => f z * (rho z : ℂ))
  rw [isConformalOnto_cayley.2.2] at h
  rw [h]
  apply setIntegral_congr_fun isOpen_upperHalf.measurableSet
  intro z hz
  exact rhoU_cayley_weight (f (cayley z)) hz

/-- Absolute integrability is preserved by the weighted Cayley area change
(TT:2550–2563). -/
theorem rhoU_integrable_cayley (f : ℂ → ℂ) :
    IntegrableOn (fun z => f z * (rho z : ℂ)) unitDisc ↔
      IntegrableOn (fun w => f (cayley w) * (rhoU w : ℂ)) upperHalf := by
  have h := ahP_integrableOn_image isOpen_upperHalf isConformalOnto_cayley.1
    isConformalOnto_cayley.2.1 (fun z => f z * (rho z : ℂ))
  rw [isConformalOnto_cayley.2.2] at h
  exact h.trans (integrableOn_congr_fun
    (fun z hz => rhoU_cayley_weight (f (cayley z)) hz) isOpen_upperHalf.measurableSet)

/-- `G(f)(z) = ∬_𝕌 G(z, w) f(w) ρ(w) d²w` on `𝕌`. -/
def resolventOpU (f : ℂ → ℂ) (z : ℂ) : ℂ := ∫ w in upperHalf, (resolventKernelU z w : ℂ) * f w * rhoU w

/-- The resolvent integral itself is conjugated by the Cayley map, not just its
kernel (TT:1083–1124, TT:2550). -/
theorem resolventOpU_cayley (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ upperHalf) :
    resolventOp unitDisc f (cayley z) = resolventOpU (f ∘ cayley) z := by
  unfold resolventOp resolventOpU
  rw [rhoU_integral_cayley (fun w => (resolventKernel (cayley z) w : ℂ) * f w)]
  apply setIntegral_congr_fun isOpen_upperHalf.measurableSet
  intro w hw
  dsimp only [Function.comp_def]
  rw [resolventKernelU_cayley hz hw]

/-- Absolute integrability of the resolvent integrand transfers between the disk
and upper-half-plane models (TT:1112–1124, TT:2550). -/
theorem resolventOpU_integrable_cayley (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ upperHalf) :
    IntegrableOn (fun w => (resolventKernel (cayley z) w : ℂ) * f w * rho w) unitDisc ↔
      IntegrableOn (fun w => (resolventKernelU z w : ℂ) * f (cayley w) * rhoU w) upperHalf := by
  apply (rhoU_integrable_cayley (fun w => (resolventKernel (cayley z) w : ℂ) * f w)).trans
  apply integrableOn_congr_fun _ isOpen_upperHalf.measurableSet
  intro w hw
  dsimp only
  rw [resolventKernelU_cayley hz hw]

/-- The upper-half-plane resolvent fixes the constant one, transported from the
proved disk normalization RK4 (TT:1128–1132, TT:2550). -/
theorem resolventOpU_one {z : ℂ} (hz : z ∈ upperHalf) :
    resolventOpU (fun _ => 1) z = 1 := by
  calc
    _ = resolventOp unitDisc (fun _ => 1) (cayley z) :=
      (resolventOpU_cayley (fun _ => 1) hz).symm
    _ = 1 := by
      unfold resolventOp
      simp only [mul_one, ← Complex.ofReal_mul]
      rw [integral_complex_ofReal, RK4 (Or.inl rfl) (cayley_mem_unitDisc hz)]
      rfl

/-- Absolute convergence of the upper-half-plane kernel mass, independently of
the totalized value of its integral (TT:1128–1132, TT:2550). -/
theorem resolventU_mass_integrable {z : ℂ} (hz : z ∈ upperHalf) :
    IntegrableOn (fun w => resolventKernelU z w * rhoU w) upperHalf := by
  have hd : IntegrableOn (fun w => (resolventKernel (cayley z) w : ℂ) * 1 * rho w) unitDisc := by
    have hc : IntegrableOn (fun w => ((resolventKernel (cayley z) w * rho w : ℝ) : ℂ)) unitDisc :=
      (resolvent_mass_integrable (Or.inl rfl) (cayley_mem_unitDisc hz)).ofReal
    simpa only [mul_one, Complex.ofReal_mul] using hc
  have hu := (resolventOpU_integrable_cayley (fun _ => 1) hz).mp hd
  have hu' : IntegrableOn (fun w => ((resolventKernelU z w * rhoU w : ℝ) : ℂ)) upperHalf := by
    simpa only [mul_one, Complex.ofReal_mul] using hu
  exact (IntegrableOn.iff_ofReal (𝕜 := ℂ)).mpr hu'

/-- RK4 in the upper-half-plane model: the kernel has total hyperbolic mass one
(TT:1128–1132, TT:2550). -/
theorem resolventU_mass_integral {z : ℂ} (hz : z ∈ upperHalf) :
    (∫ w in upperHalf, resolventKernelU z w * rhoU w) = 1 := by
  have hc : ((∫ w in upperHalf, resolventKernelU z w * rhoU w) : ℂ) = 1 := by
    simpa only [resolventOpU, mul_one, ← Complex.ofReal_mul, integral_complex_ofReal]
      using resolventOpU_one hz
  exact_mod_cast hc

/-- Only the values on the upper half-plane enter its resolvent integral
(TT:1112–1124, TT:2550). -/
theorem resolventOpU_congr {f g : ℂ → ℂ} (hfg : EqOn f g upperHalf) (z : ℂ) :
    resolventOpU f z = resolventOpU g z := by
  apply setIntegral_congr_fun isOpen_upperHalf.measurableSet
  intro w hw
  dsimp only
  rw [hfg hw]

/-- The upper-half-plane resolvent on arbitrary input data is the disk
resolvent on the inverse-Cayley pullback (TT:1112–1124, TT:2550). -/
theorem resolventOpU_eq_disk (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ upperHalf) :
    resolventOpU f z = resolventOp unitDisc (f ∘ cayleyInv) (cayley z) := by
  calc
    _ = resolventOpU ((f ∘ cayleyInv) ∘ cayley) z := by
      apply resolventOpU_congr
      intro w hw
      simp only [Function.comp_def, cayleyInv_cayley hw]
    _ = _ := (resolventOpU_cayley (f ∘ cayleyInv) hz).symm

/-- The upper-half-plane resolvent preserves uniform input bounds, by the
proved disk estimate and Cayley conjugacy (TT:1112–1124, TT:2550). -/
theorem resolventOpU_norm_le {f : ℂ → ℂ} {C : ℝ}
    (hb : ∀ w ∈ upperHalf, ‖f w‖ ≤ C) {z : ℂ} (hz : z ∈ upperHalf) :
    ‖resolventOpU f z‖ ≤ C := by
  rw [resolventOpU_eq_disk f hz]
  apply resolventOp_norm_le (Or.inl rfl) _ (cayley_mem_unitDisc hz)
  intro w hw
  exact hb (cayleyInv w) (cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hw))

/-- The upper-half-plane mass weight is nonnegative almost everywhere; its
totalized diagonal is explicitly excluded as a null singleton (TT:1100, TT:2550). -/
theorem resolventU_mass_nonneg_ae {z : ℂ} (hz : z ∈ upperHalf) :
    ∀ᵐ w ∂(volume.restrict upperHalf), 0 ≤ resolventKernelU z w * rhoU w := by
  have hne : ∀ᵐ w : ℂ ∂volume, w ≠ z := by rw [ae_iff]; simp
  filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet,
    ae_restrict_of_ae hne] with w hw hzw
  exact mul_nonneg (resolventKernelU_pos hz hw hzw.symm).le (by unfold rhoU; positivity)

/-- Absolute convergence of the upper-half-plane resolvent for bounded measurable
input, without invoking the unproved smoothness or PDE clauses of RK3
(TT:1112–1124, TT:2550). -/
theorem resolventU_integrand_integrable_of_bounded {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict upperHalf)) {C : ℝ}
    (hb : ∀ w ∈ upperHalf, ‖f w‖ ≤ C) {z : ℂ} (hz : z ∈ upperHalf) :
    Integrable (fun w => (resolventKernelU z w : ℂ) * f w * rhoU w) (volume.restrict upperHalf) := by
  have hm : Integrable (fun w => ((resolventKernelU z w * rhoU w : ℝ) : ℂ))
      (volume.restrict upperHalf) := (resolventU_mass_integrable hz).ofReal
  have hbound : ∀ᵐ w ∂(volume.restrict upperHalf), ‖f w‖ ≤ C := by
    filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet] with w hw
    exact hb w hw
  apply (hm.mul_bdd hf hbound).congr
  filter_upwards with w
  push_cast
  ring

/-- Continuity of the inverse Cayley coordinate on the disk, for transferring
resolvent continuity to the upper-half-plane model (TT:2550). -/
theorem rhoU_cayleyInv_continuousOn : ContinuousOn cayleyInv unitDisc := by
  intro w hw
  have hden := cayleyInv_den_ne_zero (mem_ball_zero_iff.mp hw)
  have hc : ContinuousAt cayleyInv w := by
    unfold cayleyInv
    fun_prop
  exact hc.continuousWithinAt

/-- The upper-half-plane resolvent sends continuous bounded inputs to continuous
outputs, transported from the independently proved disk continuity theorem
(TT:1112–1124, TT:2550). -/
theorem resolventOpU_continuousOn_of_continuous_bounded {f : ℂ → ℂ}
    (hf : ContinuousOn f upperHalf) {C : ℝ} (hb : ∀ w ∈ upperHalf, ‖f w‖ ≤ C) :
    ContinuousOn (resolventOpU f) upperHalf := by
  have hg : ContinuousOn (f ∘ cayleyInv) unitDisc :=
    hf.comp rhoU_cayleyInv_continuousOn
      (fun w hw => cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hw))
  have hgb : ∀ w ∈ unitDisc, ‖(f ∘ cayleyInv) w‖ ≤ C :=
    fun w hw => hb (cayleyInv w) (cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hw))
  have hout := resolventOp_continuousOn_of_bounded (Or.inl rfl)
    (hg.aestronglyMeasurable isOpen_ball.measurableSet) hgb
  exact (hout.comp isConformalOnto_cayley.1.continuousOn
    (fun z hz => cayley_mem_unitDisc hz)).congr (fun z hz => resolventOpU_eq_disk f hz)

/-- Harmonic Beltrami representatives in the upper-half-plane model are continuous
on that domain (TT:1242, TT:2554). -/
theorem harmonicU_continuousOn {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    ContinuousOn μ upperHalf := by
  have hc : Continuous (fun z : ℂ => (z - conj z) ^ 2 / 2) := by fun_prop
  exact (hc.continuousOn.mul
    (Complex.continuous_conj.comp_continuousOn hμ.1.continuousOn)).congr hμ.2.2

/-- The A-infinity bound in `IsHarmonicU` gives a nonnegative uniform bound for
the Beltrami representative (TT:1242, TT:2554). -/
theorem harmonicU_bounded {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ upperHalf, ‖μ z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hμ.2.1
  refine ⟨max 0 (2 * C), le_max_left _ _, ?_⟩
  intro z hz
  have hn : ‖μ z‖ = 2 * ‖z.im ^ 2 * φ z‖ := by
    rw [hμ.2.2 z hz, Complex.sub_conj]
    simp only [norm_mul, norm_div, norm_pow, Complex.norm_conj, Complex.norm_real,
      Complex.norm_I, Real.norm_eq_abs, abs_mul, abs_pow, mul_pow]
    norm_num
    <;> ring
  rw [hn]
  exact (mul_le_mul_of_nonneg_left (hC z hz) (by norm_num)).trans (le_max_right _ _)

/-- Products of harmonic upper-half-plane representatives are uniformly bounded,
as used in the resolvent expressions of §6 (TT:2584–2588, TT:2662–2672). -/
theorem harmonicU_product_bounded {μ ν φ ψ : ℂ → ℂ}
    (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ upperHalf, ‖μ z * conj (ν z)‖ ≤ C := by
  obtain ⟨C, hC, hbC⟩ := harmonicU_bounded hμ
  obtain ⟨D, hD, hbD⟩ := harmonicU_bounded hν
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  intro z hz
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hbC z hz) (hbD z hz) (norm_nonneg _) hC

/-- The resolvent of μ times the conjugate of ν in §6 is absolutely convergent
for harmonic inputs, independently of the second-variation identity
(TT:2584–2588, TT:2662–2672). -/
theorem harmonicU_resolvent_product_integrable {μ ν φ ψ : ℂ → ℂ}
    (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    Integrable (fun w => (resolventKernelU z w : ℂ) * (μ w * conj (ν w)) * rhoU w)
      (volume.restrict upperHalf) := by
  obtain ⟨C, _, hb⟩ := harmonicU_product_bounded hμ hν
  have hc := (harmonicU_continuousOn hμ).mul
    (Complex.continuous_conj.comp_continuousOn (harmonicU_continuousOn hν))
  exact resolventU_integrand_integrable_of_bounded
    (hc.aestronglyMeasurable isOpen_upperHalf.measurableSet) hb hz

/-- The resolvent of the harmonic product in §6 is continuous on the upper
half-plane; higher variation/PDE assertions are not assumed
(TT:2584–2588, TT:2662–2672). -/
theorem harmonicU_resolvent_product_continuous {μ ν φ ψ : ℂ → ℂ}
    (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) :
    ContinuousOn (resolventOpU (fun w => μ w * conj (ν w))) upperHalf := by
  obtain ⟨C, _, hb⟩ := harmonicU_product_bounded hμ hν
  have hc := (harmonicU_continuousOn hμ).mul
    (Complex.continuous_conj.comp_continuousOn (harmonicU_continuousOn hν))
  exact resolventOpU_continuousOn_of_continuous_bounded hc hb

/-- The resolvent of real input is the complex coercion of its real weighted
integral (TT:2584–2588, TT:3128–3156). -/
theorem resolventOpU_ofReal (f : ℂ → ℝ) (z : ℂ) :
    resolventOpU (fun w => (f w : ℂ)) z =
      Complex.ofReal (∫ w in upperHalf, resolventKernelU z w * f w * rhoU w) := by
  unfold resolventOpU
  simp only [← Complex.ofReal_mul, integral_complex_ofReal]

/-- Absolute convergence for real continuous bounded input to the upper-half-plane
resolvent (TT:1112–1124, TT:2550). -/
theorem resolventU_real_integrand_integrable {f : ℂ → ℝ} (hf : ContinuousOn f upperHalf)
    {C : ℝ} (hb : ∀ w ∈ upperHalf, |f w| ≤ C) {z : ℂ} (hz : z ∈ upperHalf) :
    IntegrableOn (fun w => resolventKernelU z w * f w * rhoU w) upperHalf := by
  have hc := Complex.continuous_ofReal.comp_continuousOn hf
  have hbc : ∀ w ∈ upperHalf, ‖(f w : ℂ)‖ ≤ C := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hb
  have hi := resolventU_integrand_integrable_of_bounded
    (hc.aestronglyMeasurable isOpen_upperHalf.measurableSet) hbc hz
  have hi' : IntegrableOn
      (fun w => ((resolventKernelU z w * f w * rhoU w : ℝ) : ℂ)) upperHalf := by
    simpa only [IntegrableOn, Function.comp_def, Complex.ofReal_mul] using hi
  exact (IntegrableOn.iff_ofReal (𝕜 := ℂ)).mpr hi'

/-- Nonnegativity of the real resolvent integrand almost everywhere; the kernel's
diagonal convention is handled by the mass-weight lemma (TT:1100, TT:3128–3156). -/
theorem resolventU_real_integrand_nonneg_ae {f : ℂ → ℝ}
    (hf : ∀ w ∈ upperHalf, 0 ≤ f w) {z : ℂ} (hz : z ∈ upperHalf) :
    ∀ᵐ w ∂(volume.restrict upperHalf), 0 ≤ resolventKernelU z w * f w * rhoU w := by
  filter_upwards [resolventU_mass_nonneg_ae hz,
    ae_restrict_mem isOpen_upperHalf.measurableSet] with w hw hwH
  simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_nonneg hw (hf w hwH)

/-- The upper-half-plane resolvent preserves nonnegativity of real input
(TT:1100, TT:3128–3156). -/
theorem resolventOpU_nonneg {f : ℂ → ℝ} (hf : ∀ w ∈ upperHalf, 0 ≤ f w)
    {z : ℂ} (hz : z ∈ upperHalf) : 0 ≤ (resolventOpU (fun w => (f w : ℂ)) z).re := by
  rw [resolventOpU_ofReal, Complex.ofReal_re]
  exact integral_nonneg_of_ae (resolventU_real_integrand_nonneg_ae hf hz)

/-- Strict positivity for nonnegative continuous bounded input that is positive
somewhere in the upper half-plane. A positive-measure open set remains after
excluding the diagonal singleton (TT:1100, TT:3128–3156). -/
theorem resolventOpU_pos {f : ℂ → ℝ} (hf : ContinuousOn f upperHalf)
    (hn : ∀ w ∈ upperHalf, 0 ≤ f w) {C : ℝ} (hb : ∀ w ∈ upperHalf, |f w| ≤ C)
    (hp : ∃ w ∈ upperHalf, 0 < f w) {z : ℂ} (hz : z ∈ upperHalf) :
    0 < (resolventOpU (fun w => (f w : ℂ)) z).re := by
  rw [resolventOpU_ofReal, Complex.ofReal_re]
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (resolventU_real_integrand_nonneg_ae hn hz)
    (resolventU_real_integrand_integrable hf hb hz)).mpr
  have hopen : IsOpen (upperHalf ∩ f ⁻¹' Ioi 0) :=
    hf.isOpen_inter_preimage isOpen_upperHalf isOpen_Ioi
  obtain ⟨w, hw, hfw⟩ := hp
  have hm : 0 < volume ((upperHalf ∩ f ⁻¹' Ioi 0) \ {z}) := by
    rw [measure_sdiff_null (measure_singleton z)]
    exact hopen.measure_pos (μ := volume) ⟨w, hw, hfw⟩
  apply lt_of_lt_of_le hm
  apply measure_mono
  intro w hw
  refine ⟨?_, hw.1.1⟩
  have hzw : w ≠ z := by simpa only [mem_singleton_iff] using hw.2
  change resolventKernelU z w * f w * rhoU w ≠ 0
  have hρ : 0 < rhoU w := inv_pos.mpr (sq_pos_of_pos hw.1.1)
  exact (mul_pos (mul_pos (resolventKernelU_pos hz hw.1.1 hzw.symm) hw.1.2) hρ).ne'

/-- The resolvent of the squared norm of a nonzero harmonic representative is
strictly positive, with nonzero understood on the actual domain
(TT:2584–2588, TT:3128–3156). -/
theorem harmonicU_resolvent_sq_pos {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    (hne : ∃ w ∈ upperHalf, μ w ≠ 0) {z : ℂ} (hz : z ∈ upperHalf) :
    0 < (resolventOpU (fun w => (‖μ w‖ ^ 2 : ℝ)) z).re := by
  obtain ⟨C, hC, hb⟩ := harmonicU_bounded hμ
  apply resolventOpU_pos ((harmonicU_continuousOn hμ).norm.pow 2)
    (fun _ _ => sq_nonneg _) (C := C ^ 2) _ _ hz
  · intro w hw
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb w hw) 2
  · obtain ⟨w, hw, hmw⟩ := hne
    exact ⟨w, hw, sq_pos_of_pos (norm_pos_iff.mpr hmw)⟩

/-- `ρ^{εμ}(z) = w_{εμ}^*(ρ)(z) = -4 |(w_{εμ})_z(z)|²/(w_{εμ}(z) - \overline{w_{εμ}(z)})²` (TT:2563). -/
def rhoVar (μ : ℂ → ℂ) (ε z : ℂ) : ℂ :=
  -4 * (‖dz (wU fun u => ε * μ u) z‖ ^ 2 : ℝ) / (wU (fun u => ε * μ u) z - conj (wU (fun u => ε * μ u) z)) ^ 2

/-- The density in the pullback formula as a complex expression (TT:2563). -/
theorem rhoU_complex (z : ℂ) : (rhoU z : ℂ) = -4 / (z - conj z) ^ 2 := by
  rw [Complex.sub_conj]
  unfold rhoU
  push_cast
  by_cases hz : z.im = 0
  · simp [hz]
  · have hzC : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
    field_simp
    simp [Complex.I_sq]
    ring

/-- Conjugation exchanges the two Wirtinger derivatives in the tensor pullback,
including points where the totalized derivative is zero (TT:1163, TT:2563). -/
theorem rhoVar_dzbar_conj (f : ℂ → ℂ) (z : ℂ) :
    dzbar (fun y => conj (f y)) z = conj (dz f z) := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact dzbar_conj hf
  · have hc : ¬ DifferentiableAt ℝ (fun y => conj (f y)) z := by
      intro h
      apply hf
      simpa only [Function.comp_def, Complex.conj_conj] using
        Complex.differentiable_conj.differentiableAt.comp z h
    simp [dzbar, dz, fderiv_zero_of_not_differentiableAt hf,
      fderiv_zero_of_not_differentiableAt hc]

/-- The zero Beltrami coefficient gives the identity map in the upper-half-plane
normalization (TT:1206, TT:2563). -/
theorem rhoVar_wU_zero : wU (0 : ℂ → ℂ) = id := by
  have hext : extU (0 : ℂ → ℂ) = 0 := by
    funext z
    simp [extU]
  change normalizedSolution (extU (0 : ℂ → ℂ)) = id
  rw [hext]
  exact bB_l_normalizedSolution_zero

/-- The Wirtinger derivative of the identity in the normalization of (6.1) (TT:2563). -/
theorem rhoVar_dz_id (z : ℂ) : dz id z = 1 := by
  simp [dz, fderiv_id]

/-- (TT:2563) `ρ^{εμ}` is the pull-back `w_{εμ}^*(ρ)` of the tensor `ρ` of type `(1,1)`, and `ρ^0 = ρ` on `𝕌`. -/
theorem rhoVar_pullback (μ : ℂ → ℂ) (ε : ℂ) {z : ℂ} (hz : z ∈ upperHalf) :
    rhoVar μ ε z = pullbackTensor (wU fun u => ε * μ u) 1 1 (fun y => (rhoU y : ℂ)) z ∧ rhoVar μ 0 z = rhoU z := by
  constructor
  · unfold rhoVar pullbackTensor
    dsimp only
    rw [rhoU_complex, rhoVar_dzbar_conj]
    simp only [zpow_one]
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    ring
  · have hzero : (fun u => (0 : ℂ) * μ u) = (0 : ℂ → ℂ) := by
      funext u
      simp
    unfold rhoVar
    rw [hzero, rhoVar_wU_zero, rhoVar_dz_id]
    simp only [norm_one, one_pow, Complex.ofReal_one, mul_one, id_eq]
    exact (rhoU_complex z).symm

-- `lemma_6_1` moved to `Ch1/L613.lean` (2026-10-28).

/-- **(6.1)** (TT:2601). `ρ^{εμ}(z) = -4 K_{εμ}(z, z̄)`. -/
theorem eq_6_1 (μ : ℂ → ℂ) (ε z : ℂ) : rhoVar μ ε z = -4 * kernelKbar (fun u => ε * μ u) z z := by
  unfold rhoVar kernelKbar
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  ring

-- `eq_6_2` moved to `Ch1/S6Eq62.lean` (2026-10-28).

/-- The weighted antiholomorphic disk kernel arising in (6.3) (TT:2613). -/
def wp_harmonicPVKernel (φ : ℂ → ℂ) (v : ℂ) : ℂ :=
  (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * conj (φ v) / v ^ 2

/-- Continuity of the transformed singular kernel away from its pole (TT:2613). -/
theorem wp_harmonicPVKernel_continuous {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) :
    ContinuousOn (wp_harmonicPVKernel φ) (unitDisc \ {0}) := by
  have hw : Continuous (fun v : ℂ => (((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ)) := by fun_prop
  exact (hw.continuousOn.mul
    (Complex.continuous_conj.comp_continuousOn (hφ.continuousOn.mono Set.sdiff_subset))).div
    (continuous_pow 2).continuousOn (fun _ hv => pow_ne_zero 2 hv.2)

/-- Weighted boundedness gives the quadratic-pole majorant (TT:2613). -/
theorem wp_harmonicPVKernel_bound {φ : ℂ → ℂ} {M : ℝ}
    (hb : ∀ v ∈ unitDisc, ‖(((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * φ v‖ ≤ M) :
    ∀ v ∈ unitDisc, v ≠ 0 → ‖wp_harmonicPVKernel φ v‖ ≤ M / ‖v‖ ^ 2 := by
  intro v hv _
  have h := hb v hv
  simp only [norm_mul] at h
  simpa only [wp_harmonicPVKernel, norm_div, norm_pow, norm_mul, norm_conj] using
    div_le_div_of_nonneg_right h (sq_nonneg ‖v‖)

/-- The radial weight leaves the antiholomorphic circle cancellation exact (TT:2613). -/
theorem wp_harmonicPVKernel_circle_zero {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (wp_harmonicPVKernel φ) 0 r = 0 := by
  let g : ℂ → ℂ := fun v => v ^ 2 * φ v
  have hsub : closedBall (0 : ℂ) r ⊆ unitDisc := fun v hv =>
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hv).trans_lt hr1)
  have hg : DifferentiableOn ℂ g (closedBall 0 r) :=
    (differentiableOn_id.pow 2).mul (hφ.mono hsub)
  have hmean : Real.circleAverage g 0 r = 0 := by
    have hd : DiffContOnCl ℂ g (ball 0 |r|) := by
      rw [abs_of_pos hr]
      refine ⟨hg.mono ball_subset_closedBall, ?_⟩
      rw [closure_ball (0 : ℂ) hr.ne']
      exact hg.continuousOn
    simpa [g] using hd.circleAverage
  have hconj : Real.circleAverage (fun v => conj (g v)) 0 r = 0 := by
    have hh := Complex.conjCLE.toContinuousLinearMap.circleAverage_comp_comm
      (hg.continuousOn.mono sphere_subset_closedBall |>.circleIntegrable hr.le)
    simpa [Function.comp_def, hmean] using hh
  let c : ℂ := (((1 - r ^ 2) ^ 2 : ℝ) : ℂ) / (r : ℂ) ^ 4
  have he : Real.circleAverage (wp_harmonicPVKernel φ) 0 r =
      Real.circleAverage (fun v => c * conj (g v)) 0 r := by
    apply Real.circleAverage_congr_sphere
    intro v hv
    have hn : ‖v‖ = r := by simpa [mem_sphere, dist_zero_right, abs_of_pos hr] using hv
    have hv0 : v ≠ 0 := norm_pos_iff.mp (hn ▸ hr)
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hp : v ^ 2 * conj v ^ 2 = (r : ℂ) ^ 4 := by
      rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      push_cast
      ring
    dsimp [wp_harmonicPVKernel, c, g]
    rw [hn, map_mul, map_pow]
    field_simp
    linear_combination -((((1 - r ^ 2) ^ 2 : ℝ) : ℂ) * conj (φ v)) * hp
  rw [he]
  change Real.circleAverage (fun v => c • conj (g v)) 0 r = 0
  rw [Real.circleAverage_fun_smul, hconj, smul_zero]

/-- Every positive radial truncation of the transformed kernel integrates to zero (TT:2613). -/
theorem wp_harmonicPVKernel_radial_zero {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ v ∈ unitDisc, ‖(((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * φ v‖ ≤ M)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ v in unitDisc \ ball (0 : ℂ) δ, wp_harmonicPVKernel φ v) = 0 := by
  let S := unitDisc \ ball (0 : ℂ) δ
  let G := S.indicator (wp_harmonicPVKernel φ)
  have hS : MeasurableSet S := measurableSet_ball.diff measurableSet_ball
  have hsub : S ⊆ unitDisc \ {0} := by
    intro v hv
    have hn : δ ≤ ‖v‖ := by simpa only [mem_ball_zero_iff, not_lt] using hv.2
    exact ⟨hv.1, norm_pos_iff.mp (hδ.trans_le hn)⟩
  have hK := (wp_harmonicPVKernel_continuous hφ).mono hsub
  have hGm : Measurable G := by
    have hh := hK.measurable_piecewise (continuousOn_const (c := (0 : ℂ))) hS
    convert hh using 1
    funext v
    by_cases hv : v ∈ S <;> simp [G, Set.piecewise, hv]
  have hSi : IntegrableOn (wp_harmonicPVKernel φ) S := by
    apply wp_disk_cutoff_integrable (wp_harmonicPVKernel_continuous hφ) hM
      (wp_harmonicPVKernel_bound hb) hS Set.sdiff_subset hδ
    intro v hv
    simpa only [mem_ball_zero_iff, not_lt] using hv.2
  have hGi : Integrable G := hSi.integrable_indicator hS
  have havg (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) : Real.circleAverage G 0 r = 0 := by
    by_cases hrδ : r < δ
    · calc
        _ = Real.circleAverage (fun _ : ℂ => (0 : ℂ)) 0 r := by
          apply Real.circleAverage_congr_sphere
          intro v hv
          have hn : ‖v‖ = r := by simpa [mem_sphere, dist_zero_right, abs_of_pos hr.1] using hv
          apply indicator_of_notMem
          intro hs
          exact hs.2 (mem_ball_zero_iff.mpr (hn ▸ hrδ))
        _ = 0 := Real.circleAverage_const 0 0 r
    · calc
        _ = Real.circleAverage (wp_harmonicPVKernel φ) 0 r := by
          apply Real.circleAverage_congr_sphere
          intro v hv
          have hn : ‖v‖ = r := by simpa [mem_sphere, dist_zero_right, abs_of_pos hr.1] using hv
          apply indicator_of_mem
          exact ⟨mem_ball_zero_iff.mpr (hn ▸ hr.2), by simpa only [mem_ball_zero_iff, hn] using hrδ⟩
        _ = 0 := wp_harmonicPVKernel_circle_zero hφ hr.1 hr.2
  have hp := integrableOn_polar_of_integrableOn_ball (R := 1) hGm hGi.integrableOn
  have he := bKernel_polar_integral G (by simpa only [Complex.real_smul] using hp)
  have hz : (∫ v in unitDisc, G v) = 0 := by
    rw [he]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [havg r hr]
    simp
  change (∫ v in unitDisc, S.indicator (wp_harmonicPVKernel φ) v) = 0 at hz
  rw [setIntegral_indicator hS, inter_eq_right.mpr (show S ⊆ unitDisc from Set.sdiff_subset)] at hz
  exact hz


/-- Weighted radial cancellation survives the cutoff distortion from the half-plane (TT:2613). -/
theorem wp_harmonicPVKernel_cutoff_zero {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ v ∈ unitDisc, ‖(((1 - ‖v‖ ^ 2) ^ 2 : ℝ) : ℂ) * φ v‖ ≤ M) :
    Tendsto (fun r : ℝ => ∫ v in wp_cayleyCutoff r, wp_harmonicPVKernel φ v) (𝓝[>] 0) (𝓝 0) :=
  wp_cayleyCutoff_tendsto_zero (wp_harmonicPVKernel_continuous hφ) hM
    (wp_harmonicPVKernel_bound hb) (fun _ hr _ => wp_harmonicPVKernel_radial_zero hφ hM hb hr)

/-- The norm of the reflected half-plane displacement (TT:2613). -/
theorem wp_upperHalf_reflection_norm {z : ℂ} (hz : z ∈ upperHalf) :
    ‖z - conj z‖ = 2 * z.im := by
  rw [Complex.sub_conj]
  norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show 0 < z.im from hz)]

/-- Euclidean truncations become exactly the distorted disk cutoffs (TT:2613). -/
theorem wp_centeredCayley_cutoff_mem {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf)
    (δ : ℝ) :
    wp_centeredCayley z u ∈ wp_cayleyCutoff (δ / (2 * z.im)) ↔ δ ≤ ‖u - z‖ := by
  simp only [wp_cayleyCutoff, mem_setOf_eq, wp_centeredCayley_mem hu hz, true_and]
  rw [wp_centeredCayley_one_sub hz hu, norm_div, wp_upperHalf_reflection_norm hz,
    wp_centeredCayley, norm_div]
  have hi : z.im ≠ 0 := ne_of_gt hz
  have hD : ‖u - conj z‖ ≠ 0 := norm_ne_zero_iff.mpr (wp_upperHalf_sub_conj_ne hu hz)
  have he : δ / (2 * z.im) * (2 * z.im / ‖u - conj z‖) = δ / ‖u - conj z‖ := by field_simp
  rw [he, div_le_div_iff_of_pos_right (norm_pos_iff.mpr (wp_upperHalf_sub_conj_ne hu hz))]

/-- Exact change of variables for the Euclidean-cutoff integral in (6.3) (TT:2613). -/
theorem wp_harmonicPV_change_variables {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    {z : ℂ} (hz : z ∈ upperHalf) {δ : ℝ} (hδ : 0 < δ) :
    (∫ v in wp_cayleyCutoff (δ / (2 * z.im)), wp_harmonicPVKernel (wp_halfPlaneQuadratic z φ) v) =
      (-2 * (z - conj z) ^ 2) *
        ∫ u in upperHalfPunct z δ, μ u / ((u - z) ^ 2 * (u - conj z) ^ 2) := by
  let S := wp_cayleyCutoff (δ / (2 * z.im))
  let K := wp_harmonicPVKernel (wp_halfPlaneQuadratic z φ)
  let F : ℂ → ℂ := fun u => μ u / ((u - z) ^ 2 * (u - conj z) ^ 2)
  let T := upperHalfPunct z δ
  have hopen : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hS := wp_cayleyCutoff_measurable (δ / (2 * z.im))
  have hT : MeasurableSet T := hopen.measurableSet.diff measurableSet_ball
  have hc := wp_centeredCayley_conformal hz
  have he := ahP_integral_image hopen hc.1 hc.2.1 (S.indicator K)
  rw [hc.2.2, setIntegral_indicator hS,
    inter_eq_right.mpr (show S ⊆ unitDisc from fun _ hv => hv.1)] at he
  have hpt (u : ℂ) (hu : u ∈ upperHalf) :
      ‖deriv (wp_centeredCayley z) u‖ ^ 2 • S.indicator K (wp_centeredCayley z u) =
        (-2 * (z - conj z) ^ 2) * T.indicator F u := by
    by_cases hd : δ ≤ ‖u - z‖
    · have hs : wp_centeredCayley z u ∈ S := (wp_centeredCayley_cutoff_mem hz hu δ).mpr hd
      have ht : u ∈ T := ⟨hu, by simpa [mem_ball, dist_eq_norm] using hd⟩
      have huz : u ≠ z := by intro h; simp [h] at hd; linarith
      rw [indicator_of_mem hs, indicator_of_mem ht]
      have hh := wp_centeredCayley_pv_integrand hz hu huz φ
      rw [← hμ.2.2 u hu] at hh
      simpa only [K, F, wp_harmonicPVKernel, mul_div_assoc] using hh
    · have hs : wp_centeredCayley z u ∉ S := by
        exact fun h => hd ((wp_centeredCayley_cutoff_mem hz hu δ).mp h)
      have ht : u ∉ T := by
        intro h
        exact h.2 (by simpa [mem_ball, dist_eq_norm] using not_le.mp hd)
      simp only [indicator_of_notMem hs, indicator_of_notMem ht, smul_zero, mul_zero]
  rw [setIntegral_congr_fun hopen.measurableSet hpt, integral_const_mul,
    setIntegral_indicator hT, inter_eq_right.mpr (show T ⊆ upperHalf from Set.sdiff_subset)] at he
  exact he

/-- **(6.3)** (TT:2613). For `μ ∈ Ω^{-1,1}(𝕌)` and `z ∈ 𝕌` (principal value at `u = z`):
`∬_𝕌 μ(u)/((u - z)²(u - z̄)²) d²u = 0`. -/
theorem eq_6_3 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    Tendsto (fun δ : ℝ => ∫ u in upperHalfPunct z δ, μ u / ((u - z) ^ 2 * (u - conj z) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hμ.2.1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z hz)
  have hbound := wp_halfPlaneQuadratic_bound (φ := φ) (C := C) hz
    (fun u hu => by simpa only [Complex.ofReal_pow] using hC u hu)
  have hlimit := wp_harmonicPVKernel_cutoff_zero (wp_halfPlaneQuadratic_differentiable hz hμ.1)
    (mul_nonneg (by norm_num) hC0) hbound
  have hscale : Tendsto (fun δ : ℝ => δ / (2 * z.im)) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun δ : ℝ => δ / (2 * z.im)) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      change 0 < δ / (2 * z.im)
      exact div_pos hδ (mul_pos (by norm_num : (0 : ℝ) < 2) (show 0 < z.im from hz))
  have hfac : (-2 * (z - conj z) ^ 2 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (wp_upperHalf_sub_conj_ne hz hz))
  have ht := (hlimit.comp hscale).const_mul ((-2 * (z - conj z) ^ 2 : ℂ)⁻¹)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  dsimp only [Function.comp_def]
  rw [wp_harmonicPV_change_variables hμ hz hδ, ← mul_assoc, inv_mul_cancel₀ hfac, one_mul]

-- `eq_6_4` moved to `Ch1/S6Eq64.lean` (2026-10-28).

/-- **(6.5)** (TT:2625). `1/(u - v̄) = (z - z̄)/((u - z̄)(z - v̄)) + (v̄ - z̄)(z - u)/((u - z̄)(z - v̄)(u - v̄))`. -/
theorem eq_6_5 {u v z : ℂ} (h1 : u - conj v ≠ 0) (h2 : u - conj z ≠ 0) (h3 : z - conj v ≠ 0) :
    1 / (u - conj v) = (z - conj z) / ((u - conj z) * (z - conj v)) +
      (conj v - conj z) * (z - u) / ((u - conj z) * (z - conj v) * (u - conj v)) := by
  field_simp
  ring

/-- (TT:2631) The consequence of (6.5) used to regularize (6.4) (the four-term identity). -/
theorem eq_6_5_four_terms {u v z : ℂ} (h0 : u - z ≠ 0) (h1 : u - conj v ≠ 0) (h2 : u - conj z ≠ 0)
    (h3 : z - conj v ≠ 0) (h4 : conj z - conj v ≠ 0) :
    1 / ((u - z) ^ 2 * (u - conj v) ^ 2 * (conj z - conj v) ^ 2) =
      1 / ((u - conj z) ^ 2 * (z - conj v) ^ 2 * (u - conj v) ^ 2) +
      2 * (z - conj z) / ((u - conj z) ^ 3 * (z - conj v) ^ 3 * (u - conj v)) +
      (z - conj z) ^ 2 / ((u - z) ^ 2 * (u - conj z) ^ 2 * (z - conj v) ^ 2 * (conj z - conj v) ^ 2) +
      2 * (z - conj z) ^ 2 / ((u - z) * (u - conj z) ^ 3 * (z - conj v) ^ 3 * (conj z - conj v)) := by
  field_simp
  ring

-- `eq_6_4_regular` moved to `Ch1/S6Eq64.lean` (2026-10-28).

-- `prop_6_3` moved to `Ch1/S6Eq64.lean` (2026-10-28).

/-- Squared modulus of `z - z̄` for the centered coordinate (TT:2662). -/
theorem wp_cc_norm_sub_conj_sq {z : ℂ} (_hz : z ∈ upperHalf) :
    ‖z - conj z‖ ^ 2 = 4 * z.im ^ 2 := by
  rw [Complex.sub_conj]
  simp only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  norm_num

/-- Hyperbolic density transfer under the centered coordinate (TT:2613, 2662). -/
theorem wp_cc_density {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    rho (wp_centeredCayley z u) * ‖(z - conj z) / (u - conj z) ^ 2‖ ^ 2 = rhoU u := by
  have hd : ‖u - conj z‖ ≠ 0 := norm_ne_zero_iff.mpr (wp_upperHalf_sub_conj_ne hu hz)
  have hui : u.im ≠ 0 := ne_of_gt hu
  have hzi : z.im ≠ 0 := ne_of_gt hz
  unfold rho rhoU
  have hAZ := wp_cc_norm_sub_conj_sq hz
  rw [wp_centeredCayley_boundary hu hz]
  simp only [norm_div, norm_pow, div_pow, hAZ]
  field_simp

/-- Change of variables for the centered coordinate. -/
theorem wp_cc_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {z : ℂ}
    (hz : z ∈ upperHalf) (g : ℂ → E) :
    ∫ ζ in unitDisc, g ζ = ∫ u in upperHalf,
      ‖(z - conj z) / (u - conj z) ^ 2‖ ^ 2 • g (wp_centeredCayley z u) := by
  have h := ahP_integral_image isOpen_upperHalf (wp_centeredCayley_conformal hz).1
    (wp_centeredCayley_conformal hz).2.1 g
  rw [(wp_centeredCayley_conformal hz).2.2] at h
  rw [h]
  refine setIntegral_congr_fun isOpen_upperHalf.measurableSet fun u hu => ?_
  rw [(wp_centeredCayley_hasDerivAt hz hu).deriv]

/-- The point-pair invariant in the centered coordinate (TT:2662). -/
theorem wp_cc_pointPair {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    pointPair 0 (wp_centeredCayley z u) = pointPairU z u := by
  have hd : ‖u - conj z‖ ≠ 0 := norm_ne_zero_iff.mpr (wp_upperHalf_sub_conj_ne hu hz)
  have hui : u.im ≠ 0 := ne_of_gt hu
  have hzi : z.im ≠ 0 := ne_of_gt hz
  unfold pointPair pointPairU
  rw [zero_sub, norm_neg, norm_zero, wp_centeredCayley_boundary hu hz]
  unfold wp_centeredCayley
  rw [norm_div, div_pow, norm_sub_rev z u]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, one_mul]
  field_simp

/-- The resolvent kernel in the centered coordinate (TT:2662). -/
theorem wp_cc_resolventKernel {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    resolventKernel 0 (wp_centeredCayley z u) = resolventKernelU z u := by
  simp only [resolventKernel, resolventKernelU, wp_cc_pointPair hz hu]

/-- The weighted conjugate quadratic pullback is the pushed-forward Beltrami differential. -/
theorem wp_cc_weighted_conj {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) (φ : ℂ → ℂ) :
    conj (wp_halfPlaneQuadratic z φ (wp_centeredCayley z u)) *
        (rho (wp_centeredCayley z u) : ℂ)⁻¹ =
      (((u - conj u) ^ 2 / 2 * conj (φ u)) / 2) * ((conj u - z) / (u - conj z)) ^ 2 := by
  have hd := wp_upperHalf_sub_conj_ne hu hz
  have hdc : conj u - z ≠ 0 := by
    simpa only [map_sub, conj_conj] using (map_ne_zero (starRingEnd ℂ)).mpr hd
  have hz0 := wp_upperHalf_sub_conj_ne hz hz
  have hz0c : conj z - z ≠ 0 := by
    rw [show conj z - z = -(z - conj z) by ring]; exact neg_ne_zero.mpr hz0
  rw [wp_halfPlaneQuadratic_at hz hu, wp_rho_inv_complex]
  unfold wp_centeredCayley
  simp only [map_div₀, map_mul, map_pow, map_sub, conj_conj]
  field_simp
  ring

/-- The Cayley transformed kernel, multiplied by the Jacobian squares, is the (6.4) kernel. -/
theorem wp_cc_kernel {z u v : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) (hv : v ∈ upperHalf) :
    ((((1 - wp_centeredCayley z u * conj (wp_centeredCayley z v))⁻¹) ^ 2 +
        (1 - wp_centeredCayley z u * conj (wp_centeredCayley z v))⁻¹)) *
      (((z - conj z) / (u - conj z) ^ 2) ^ 2 * conj ((z - conj z) / (v - conj z) ^ 2) ^ 2) =
    (z - conj z) ^ 2 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
      (z - conj z) ^ 3 / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3) := by
  have h1 := wp_upperHalf_sub_conj_ne hu hz
  have h2 := wp_upperHalf_sub_conj_ne hv hz
  have h3 := wp_upperHalf_sub_conj_ne hz hz
  have h4 : u - conj v ≠ 0 := wp_upperHalf_sub_conj_ne hu hv
  have h5 : z - conj v ≠ 0 := wp_upperHalf_sub_conj_ne hz hv
  have h2c : conj v - z ≠ 0 := by
    simpa only [map_sub, conj_conj] using (map_ne_zero (starRingEnd ℂ)).mpr h2
  have h3c : conj z - z ≠ 0 := by
    rw [show conj z - z = -(z - conj z) by ring]; exact neg_ne_zero.mpr h3
  have hden : 1 - wp_centeredCayley z u * conj (wp_centeredCayley z v) =
      (conj z - z) * (u - conj v) / ((u - conj z) * (conj v - z)) := by
    unfold wp_centeredCayley
    simp only [map_div₀, map_sub, conj_conj]
    field_simp
    ring
  rw [hden]
  simp only [map_div₀, map_sub, map_pow, conj_conj]
  have h4' : conj z - z ≠ 0 := h3c
  field_simp
  ring

/-- The weighted bound survives the centered quadratic pullback (TT:2662). -/
theorem wp_cc_weighted_bound {z : ℂ} (hz : z ∈ upperHalf) {φ : ℂ → ℂ} {C : ℝ}
    (hC : ∀ u ∈ upperHalf, ‖(u.im ^ 2 : ℝ) * φ u‖ ≤ C) :
    ∀ w ∈ unitDisc, ‖wp_halfPlaneQuadratic z φ w‖ * (rho w)⁻¹ ≤ C := by
  intro w hw
  have h := wp_halfPlaneQuadratic_bound hz hC w hw
  have hnn : 0 ≤ (1 - ‖w‖ ^ 2) ^ 2 := sq_nonneg _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn] at h
  have hr : (rho w)⁻¹ = (1 - ‖w‖ ^ 2) ^ 2 / 4 := by unfold rho; rw [inv_div]
  rw [hr]
  linarith

/-- Non-conjugated version of `wp_cc_weighted_conj`. -/
theorem wp_cc_weighted {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) (φ : ℂ → ℂ) :
    wp_halfPlaneQuadratic z φ (wp_centeredCayley z u) * (rho (wp_centeredCayley z u) : ℂ)⁻¹ =
      ((u - conj u) ^ 2 / 4 * φ u) * ((u - conj z) / (conj u - z)) ^ 2 := by
  have hd := wp_upperHalf_sub_conj_ne hu hz
  have hdc : conj u - z ≠ 0 := by
    simpa only [map_sub, conj_conj] using (map_ne_zero (starRingEnd ℂ)).mpr hd
  have hz0 := wp_upperHalf_sub_conj_ne hz hz
  have hz0c : conj z - z ≠ 0 := by
    rw [show conj z - z = -(z - conj z) by ring]; exact neg_ne_zero.mpr hz0
  rw [wp_halfPlaneQuadratic_at hz hu, wp_rho_inv_complex]
  unfold wp_centeredCayley
  simp only [map_div₀, map_mul, map_pow, map_sub, conj_conj]
  field_simp
  ring

/-- Unimodularity of the Jacobian phase (TT:2662). -/
theorem wp_cc_ratio {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    ((conj u - z) / (u - conj z)) ^ 2 * conj (((conj u - z) / (u - conj z)) ^ 2) = 1 := by
  have hd := wp_upperHalf_sub_conj_ne hu hz
  have hdc : conj u - z ≠ 0 := by
    simpa only [map_sub, conj_conj] using (map_ne_zero (starRingEnd ℂ)).mpr hd
  simp only [map_pow, map_div₀, map_sub, conj_conj]
  field_simp

/-- Jacobian square times the phase ratio (TT:2662). -/
theorem wp_cc_jac_ratio {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    ((‖(z - conj z) / (u - conj z) ^ 2‖ ^ 2 : ℝ) : ℂ) * ((conj u - z) / (u - conj z)) ^ 2 =
      -(((z - conj z) / (u - conj z) ^ 2) ^ 2) := by
  have hd := wp_upperHalf_sub_conj_ne hu hz
  have hdc : conj u - z ≠ 0 := by
    simpa only [map_sub, conj_conj] using (map_ne_zero (starRingEnd ℂ)).mpr hd
  rw [← wp_conj_mul_self]
  simp only [map_pow, map_div₀, map_sub, conj_conj]
  field_simp
  ring

/-- Conjugate form of the Jacobian-phase identity (TT:2662). -/
theorem wp_cc_jac_ratio_conj {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    ((‖(z - conj z) / (u - conj z) ^ 2‖ ^ 2 : ℝ) : ℂ) * ((u - conj z) / (conj u - z)) ^ 2 =
      -(conj ((z - conj z) / (u - conj z) ^ 2)) ^ 2 := by
  have hd := wp_upperHalf_sub_conj_ne hu hz
  have hdc : conj u - z ≠ 0 := by
    simpa only [map_sub, conj_conj] using (map_ne_zero (starRingEnd ℂ)).mpr hd
  rw [← wp_conj_mul_self]
  simp only [map_pow, map_div₀, map_sub, conj_conj]
  field_simp
  ring

/-- The pointwise algebra behind the double change of variables. -/
theorem wp_cc_pair {z u v : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) (hv : v ∈ upperHalf)
    {μ ν φ ψ : ℂ → ℂ} (hμ : μ u = (u - conj u) ^ 2 / 2 * conj (φ u))
    (hν : ν v = (v - conj v) ^ 2 / 2 * conj (ψ v)) :
    ((‖(z - conj z) / (v - conj z) ^ 2‖ ^ 2 : ℝ) : ℂ) *
      (((‖(z - conj z) / (u - conj z) ^ 2‖ ^ 2 : ℝ) : ℂ) *
        ((conj (wp_halfPlaneQuadratic z φ (wp_centeredCayley z u)) *
            (rho (wp_centeredCayley z u) : ℂ)⁻¹) *
          (wp_halfPlaneQuadratic z ψ (wp_centeredCayley z v) *
            (rho (wp_centeredCayley z v) : ℂ)⁻¹) *
          (((1 - wp_centeredCayley z u * conj (wp_centeredCayley z v))⁻¹ ^ 2 +
            (1 - wp_centeredCayley z u * conj (wp_centeredCayley z v))⁻¹)))) =
      (1 / 4 : ℂ) * (μ u * conj (ν v) *
        ((z - conj z) ^ 2 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) ^ 3 / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3))) := by
  have hK := wp_cc_kernel hz hu hv
  have hJu := wp_cc_jac_ratio hz hu
  have hJv := wp_cc_jac_ratio_conj hz hv
  have hν' : conj (ν v) = (v - conj v) ^ 2 / 2 * ψ v := by
    rw [hν]
    simp only [map_mul, map_div₀, map_pow, map_sub, conj_conj, Complex.conj_ofNat]
    ring
  rw [wp_cc_weighted_conj hz hu φ, wp_cc_weighted hz hv ψ, ← hK, hμ, hν']
  generalize ((1 - wp_centeredCayley z u * conj (wp_centeredCayley z v))⁻¹ ^ 2 +
    (1 - wp_centeredCayley z u * conj (wp_centeredCayley z v))⁻¹) = X
  linear_combination
    ((u - conj u) ^ 2 * conj (φ u) * (v - conj v) ^ 2 * ψ v * X / 16 *
      (((‖(z - conj z) / (v - conj z) ^ 2‖ ^ 2 : ℝ) : ℂ) * ((v - conj z) / (conj v - z)) ^ 2)) * hJu -
    ((u - conj u) ^ 2 * conj (φ u) * (v - conj v) ^ 2 * ψ v * X / 16 *
      ((z - conj z) / (u - conj z) ^ 2) ^ 2) * hJv


/-- Corollary 6.4 in its proved form: the Cayley transport of the mixed diagonal identity (TT:2662). -/
theorem wp_cor_6_4_main {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    resolventOpU (fun u => μ u * conj (ν u)) z =
      (2 / π ^ 2) * ∫ v in upperHalf, ∫ u in upperHalf, μ u * conj (ν v) *
        ((z - conj z) ^ 2 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) ^ 3 / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)) := by
  obtain ⟨hφd, ⟨Cφ, hCφ⟩, hμφ⟩ := hμ
  obtain ⟨hψd, ⟨Cψ, hCψ⟩, hνψ⟩ := hν
  have hFμd := wp_halfPlaneQuadratic_differentiable hz hφd
  have hFνd := wp_halfPlaneQuadratic_differentiable hz hψd
  obtain ⟨cμ, hcμ, -⟩ := exists_disk_scalar_series hFμd
  obtain ⟨cν, hcν, -⟩ := exists_disk_scalar_series hFνd
  have hbμ := wp_cc_weighted_bound hz (fun u hu => by
    have h := hCφ u hu; rwa [← Complex.ofReal_pow] at h)
  have hbν := wp_cc_weighted_bound hz (fun u hu => by
    have h := hCψ u hu; rwa [← Complex.ofReal_pow] at h)
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  set Gμ : ℂ → ℂ := unitDisc.piecewise (wp_halfPlaneQuadratic z φ) 0 with hGμ
  set Gν : ℂ → ℂ := unitDisc.piecewise (wp_halfPlaneQuadratic z ψ) 0 with hGν
  have hGμm : Measurable Gμ := hFμd.continuousOn.measurable_piecewise continuousOn_const hDm
  have hGνm : Measurable Gν := hFνd.continuousOn.measurable_piecewise continuousOn_const hDm
  have hGμe : ∀ w ∈ unitDisc, Gμ w = wp_halfPlaneQuadratic z φ w :=
    fun w hw => Set.piecewise_eq_of_mem _ _ _ hw
  have hGνe : ∀ w ∈ unitDisc, Gν w = wp_halfPlaneQuadratic z ψ w :=
    fun w hw => Set.piecewise_eq_of_mem _ _ _ hw
  have hcμ' : ∀ w ∈ unitDisc, HasSum (fun n => cμ n * w ^ n) (Gμ w) := fun w hw => by
    rw [hGμe w hw]; exact hcμ w hw
  have hcν' : ∀ w ∈ unitDisc, HasSum (fun n => cν n * w ^ n) (Gν w) := fun w hw => by
    rw [hGνe w hw]; exact hcν w hw
  have hGμc : ContinuousOn Gμ unitDisc := hFμd.continuousOn.congr hGμe
  have hGνc : ContinuousOn Gν unitDisc := hFνd.continuousOn.congr hGνe
  have hbμ' : ∀ w ∈ unitDisc, ‖Gμ w‖ * (rho w)⁻¹ ≤ Cφ := fun w hw => by
    rw [hGμe w hw]; exact hbμ w hw
  have hbν' : ∀ w ∈ unitDisc, ‖Gν w‖ * (rho w)⁻¹ ≤ Cψ := fun w hw => by
    rw [hGνe w hw]; exact hbν w hw
  have hmix := wp_mixed_diagonal_kernel_identity hcμ' hcν' hGμc hGνc hGμm hGνm hbμ' hbν'
  -- left side: the resolvent as a disk integral
  have hI : (∫ w in unitDisc, (resolventKernel 0 w : ℂ) * (conj (Gμ w) * Gν w) * (rho w : ℂ)⁻¹) =
      (1 / 4 : ℂ) * resolventOpU (fun u => μ u * conj (ν u)) z := by
    rw [wp_cc_integral hz, resolventOpU, ← integral_const_mul]
    refine setIntegral_congr_fun isOpen_upperHalf.measurableSet fun u hu => ?_
    have hc := wp_centeredCayley_mem hu hz
    have hρ : (rho (wp_centeredCayley z u) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hc).ne).ne'
    have hs : ((u - conj z) / (conj u - z)) ^ 2 * ((conj u - z) / (u - conj z)) ^ 2 = 1 := by
      have hd := wp_upperHalf_sub_conj_ne hu hz
      have hdc : conj u - z ≠ 0 := by
        simpa only [map_sub, conj_conj] using (map_ne_zero (starRingEnd ℂ)).mpr hd
      field_simp
    have hdens := wp_cc_density hz hu
    have hdens' : ((‖(z - conj z) / (u - conj z) ^ 2‖ ^ 2 : ℝ) : ℂ) *
        (rho (wp_centeredCayley z u) : ℂ) = (rhoU u : ℂ) := by
      rw [← hdens]; push_cast; ring
    have hkey : conj (wp_halfPlaneQuadratic z φ (wp_centeredCayley z u)) *
        wp_halfPlaneQuadratic z ψ (wp_centeredCayley z u) *
          (rho (wp_centeredCayley z u) : ℂ)⁻¹ =
        (1 / 4 : ℂ) * (μ u * conj (ν u)) * (rho (wp_centeredCayley z u) : ℂ) := by
      have e : conj (wp_halfPlaneQuadratic z φ (wp_centeredCayley z u)) *
          wp_halfPlaneQuadratic z ψ (wp_centeredCayley z u) *
            (rho (wp_centeredCayley z u) : ℂ)⁻¹ =
          (conj (wp_halfPlaneQuadratic z φ (wp_centeredCayley z u)) *
              (rho (wp_centeredCayley z u) : ℂ)⁻¹) *
            (wp_halfPlaneQuadratic z ψ (wp_centeredCayley z u) *
              (rho (wp_centeredCayley z u) : ℂ)⁻¹) * (rho (wp_centeredCayley z u) : ℂ) := by
        field_simp
      rw [e, wp_cc_weighted_conj hz hu φ, wp_cc_weighted hz hu ψ, hμφ u hu, hνψ u hu]
      simp only [map_mul, map_div₀, map_pow, map_sub, conj_conj, Complex.conj_ofNat]
      linear_combination ((u - conj u) ^ 4 / 16 * conj (φ u) * ψ u *
        (rho (wp_centeredCayley z u) : ℂ)) * hs
    simp only [Complex.real_smul]
    rw [hGμe _ hc, hGνe _ hc, wp_cc_resolventKernel hz hu]
    calc _ = (resolventKernelU z u : ℂ) * (((‖(z - conj z) / (u - conj z) ^ 2‖ ^ 2 : ℝ) : ℂ) *
            (conj (wp_halfPlaneQuadratic z φ (wp_centeredCayley z u)) *
              wp_halfPlaneQuadratic z ψ (wp_centeredCayley z u) *
                (rho (wp_centeredCayley z u) : ℂ)⁻¹)) := by ring
      _ = _ := by
        rw [hkey]
        rw [← hdens']
        ring
  -- right side: the double integral on the upper half-plane
  have hint := wp_double_kernel_weighted_integrable (f := fun u => conj (Gμ u) * (rho u : ℂ)⁻¹)
    (g := fun u => Gν u * (rho u : ℂ)⁻¹)
    (by
      have hρ : Measurable (fun w : ℂ => (rho w : ℂ)⁻¹) := by
        have : Measurable rho :=
          measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)
        exact (Complex.measurable_ofReal.comp this).inv
      exact (Complex.continuous_conj.measurable.comp hGμm).mul hρ)
    (by
      have hρ : Measurable (fun w : ℂ => (rho w : ℂ)⁻¹) := by
        have : Measurable rho :=
          measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)
        exact (Complex.measurable_ofReal.comp this).inv
      exact hGνm.mul hρ)
    (M := Cφ) (N := Cψ)
    (fun w hw => by
      have hr := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hw).ne
      simpa only [norm_mul, norm_conj, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr] using hbμ' w hw)
    (fun w hw => by
      have hr := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hw).ne
      simpa only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr] using hbν' w hw)
  have hJ : (∫ p : ℂ × ℂ, (conj (Gμ p.1) * (rho p.1 : ℂ)⁻¹) * (Gν p.2 * (rho p.2 : ℂ)⁻¹) *
      (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹)
      ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc))) =
      (1 / 4 : ℂ) * ∫ v in upperHalf, ∫ u in upperHalf, μ u * conj (ν v) *
        ((z - conj z) ^ 2 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) ^ 3 / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)) := by
    rw [integral_prod_symm _ hint]
    rw [wp_cc_integral hz]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun isOpen_upperHalf.measurableSet fun v hv => ?_
    have hcv := wp_centeredCayley_mem hv hz
    simp only [Complex.real_smul]
    rw [wp_cc_integral (E := ℂ) hz, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun isOpen_upperHalf.measurableSet fun u hu => ?_
    have hcu := wp_centeredCayley_mem hu hz
    rw [hGμe _ hcu, hGνe _ hcv]
    have := wp_cc_pair hz hu hv (hμ := hμφ u hu) (hν := hνψ v hv)
    simp only [Complex.real_smul]
    linear_combination this
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hI, hJ] at hmix
  have hS : (∫ v in upperHalf, ∫ u in upperHalf, μ u * conj (ν v) *
        ((z - conj z) ^ 2 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) ^ 3 / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3))) =
      (π ^ 2 / 2 : ℂ) * resolventOpU (fun u => μ u * conj (ν u)) z := by
    linear_combination (4 : ℂ) * hmix
  rw [hS]
  field_simp

/-- **Corollary 6.4** (TT:2662–2666; for `Ω^{-1,1}(𝕌)`, see the module docstring). For `μ, ν ∈ Ω^{-1,1}(𝕌)` and `z ∈ 𝕌`,
`G(μν̄)(z)` equals
`(2/π²) ∬∬_{𝕌×𝕌} μ(u) \overline{ν(v)} ((z - z̄)²/((u - v̄)²(z - v̄)²(u - z̄)²) + (z - z̄)³/((u - z̄)³(u - v̄)(z - v̄)³)) d²u d²v`.
-/
theorem cor_6_4 {μ ν φ ψ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) (hν : IsHarmonicU ν ψ) {z : ℂ} (hz : z ∈ upperHalf) :
    resolventOpU (fun u => μ u * conj (ν u)) z =
      (2 / π ^ 2) * ∫ v in upperHalf, ∫ u in upperHalf, μ u * conj (ν v) *
        ((z - conj z) ^ 2 / ((u - conj v) ^ 2 * (z - conj v) ^ 2 * (u - conj z) ^ 2) +
          (z - conj z) ^ 3 / ((u - conj z) ^ 3 * (u - conj v) * (z - conj v) ^ 3)) := by
  exact wp_cor_6_4_main hμ hν hz

-- `remark_6_5` moved to `Ch1/S6Remark65.lean` (2026-10-28).

end TakhtajanTeo
