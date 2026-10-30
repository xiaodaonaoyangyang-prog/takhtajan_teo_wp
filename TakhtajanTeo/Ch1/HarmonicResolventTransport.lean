import TakhtajanTeo.Ch1.HarmonicResolventParseval
import TakhtajanTeo.Ch1.QCVariationBergman

/-! Normalized sigma coordinates and weighted integrability for Lemma 5.8 (TT:2444–2462). -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def wp_sigmaRotation (z : ℂ) : ℂ := z / (((1 - z) / (1 - conj z)) * conj z)

theorem wp_sigma_normalizing_norm {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ‖(1 - z) / (1 - conj z)‖ = 1 := by
  have hz1 : z ≠ 1 := by intro h; subst z; norm_num [unitDiscExterior] at hz
  have hn : ‖1 - z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz1.symm)
  have he : ‖1 - conj z‖ = ‖1 - z‖ := by
    simpa only [map_sub, map_one] using Complex.norm_conj (1 - z)
  rw [norm_div, he, div_self hn]

theorem wp_sigmaRotation_norm {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ‖wp_sigmaRotation z‖ = 1 := by
  have hz0 := resolvent_exterior_ne_zero hz
  simp only [wp_sigmaRotation, norm_div, norm_mul, wp_sigma_normalizing_norm hz,
    norm_conj, one_mul, div_self (norm_ne_zero_iff.mpr hz0)]

theorem wp_sigmaInv_blaschke {z : ℂ} (hz : z ∈ unitDiscExterior) (w : ℂ) :
    sigmaInv z w = blaschke (-(conj z)⁻¹) (wp_sigmaRotation z * w) := by
  have hz0 := resolvent_exterior_ne_zero hz
  have hzc : conj z ≠ 0 := by simpa using hz0
  have hk : (1 - z) / (1 - conj z) ≠ 0 := by
    have h := wp_sigma_normalizing_norm hz
    intro he
    rw [he, norm_zero] at h
    norm_num at h
  let k := (1 - z) / (1 - conj z)
  change k ≠ 0 at hk
  have hn : wp_sigmaRotation z * w + (conj z)⁻¹ =
      (k + w * z) / (k * conj z) := by
    change z / (k * conj z) * w + (conj z)⁻¹ = _
    field_simp [hk, hzc]
    <;> ring
  have hd : 1 + z⁻¹ * (wp_sigmaRotation z * w) =
      (w + k * conj z) / (k * conj z) := by
    change 1 + z⁻¹ * (z / (k * conj z) * w) = _
    field_simp [hk, hzc, hz0]
    <;> ring
  simp only [blaschke, map_neg, map_inv₀, conj_conj, sub_neg_eq_add, neg_mul]
  rw [hn, hd, div_div_div_cancel_right₀ (mul_ne_zero hk hzc)]
  rfl

theorem wp_sigmaInv_disk_conformal {z : ℂ} (hz : z ∈ unitDiscExterior) :
    IsConformalOnto (sigmaInv z) unitDisc unitDisc := by
  have ha : ‖-(conj z)⁻¹‖ < 1 := by
    rw [norm_neg, norm_inv, norm_conj]
    exact (inv_lt_one₀ (norm_pos_iff.mpr (resolvent_exterior_ne_zero hz))).mpr hz
  have h := (isConformalOnto_blaschke ha).comp
    (isConformalOnto_rot (wp_sigmaRotation_norm hz))
  have he : sigmaInv z = blaschke (-(conj z)⁻¹) ∘ (fun w => wp_sigmaRotation z * w) :=
    funext (wp_sigmaInv_blaschke hz)
  rwa [he]

theorem wp_sigmaInv_deriv {z w : ℂ} (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDisc) :
    deriv (sigmaInv z) w =
      deriv (blaschke (-(conj z)⁻¹)) (wp_sigmaRotation z * w) * wp_sigmaRotation z := by
  have ha : ‖-(conj z)⁻¹‖ < 1 := by
    rw [norm_neg, norm_inv, norm_conj]
    exact (inv_lt_one₀ (norm_pos_iff.mpr (resolvent_exterior_ne_zero hz))).mpr hz
  have hsw : ‖wp_sigmaRotation z * w‖ < 1 := by
    simpa only [norm_mul, wp_sigmaRotation_norm hz, one_mul] using mem_ball_zero_iff.mp hw
  have he : sigmaInv z = blaschke (-(conj z)⁻¹) ∘ (fun w => wp_sigmaRotation z * w) :=
    funext (wp_sigmaInv_blaschke hz)
  have hd := (hasDerivAt_blaschke ha hsw).differentiableAt.hasDerivAt.comp w
    ((hasDerivAt_id w).const_mul (wp_sigmaRotation z))
  rw [he]
  simpa only [mul_one] using hd.deriv

theorem wp_sigmaInv_rho_jacobian {z w : ℂ}
    (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDisc) :
    rho (sigmaInv z w) * ‖deriv (sigmaInv z) w‖ ^ 2 = rho w := by
  have ha : ‖-(conj z)⁻¹‖ < 1 := by
    rw [norm_neg, norm_inv, norm_conj]
    exact (inv_lt_one₀ (norm_pos_iff.mpr (resolvent_exterior_ne_zero hz))).mpr hz
  have hsw : ‖wp_sigmaRotation z * w‖ < 1 := by
    simpa only [norm_mul, wp_sigmaRotation_norm hz, one_mul] using mem_ball_zero_iff.mp hw
  rw [wp_sigmaInv_deriv hz hw, norm_mul, wp_sigmaRotation_norm hz, mul_one,
    wp_sigmaInv_blaschke hz, rho_blaschke_jacobian ha hsw]
  simp only [rho, norm_mul, wp_sigmaRotation_norm hz, one_mul]

theorem wp_sigmaInv_center_kernel {z w : ℂ}
    (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDisc) :
    resolventKernel (conj z)⁻¹ (sigmaInv z w) = resolventKernel 0 w := by
  have ha : ‖(conj z)⁻¹‖ < 1 := by
    rw [norm_inv, norm_conj]
    exact (inv_lt_one₀ (norm_pos_iff.mpr (resolvent_exterior_ne_zero hz))).mpr hz
  have hna : ‖-(conj z)⁻¹‖ < 1 := by simpa only [norm_neg] using ha
  have hsw : ‖wp_sigmaRotation z * w‖ < 1 := by
    simpa only [norm_mul, wp_sigmaRotation_norm hz, one_mul] using mem_ball_zero_iff.mp hw
  have hσ := (wp_sigmaInv_disk_conformal hz).mapsTo hw
  rw [← resolventKernel_blaschke_center ha (mem_ball_zero_iff.mp hσ), wp_sigmaInv_blaschke hz]
  have hb : blaschke (conj z)⁻¹ (blaschke (-(conj z)⁻¹) (wp_sigmaRotation z * w)) =
      wp_sigmaRotation z * w := by
    simpa only [neg_neg] using blaschke_neg_blaschke hna hsw
  rw [hb]
  simp only [resolventKernel, pointPair, zero_sub, norm_neg, norm_mul,
    wp_sigmaRotation_norm hz, one_mul]

theorem wp_sigmaInv_pullback_norm (f : ℂ → ℂ) {z w : ℂ}
    (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDisc) :
    ‖f (sigmaInv z w) * deriv (sigmaInv z) w ^ 2‖ * (rho w)⁻¹ =
      ‖f (sigmaInv z w)‖ * (rho (sigmaInv z w))⁻¹ := by
  have hrw : 0 < rho w := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hw).ne
  have hσ := (wp_sigmaInv_disk_conformal hz).mapsTo hw
  have hrs : 0 < rho (sigmaInv z w) := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hσ).ne
  have hJ := wp_sigmaInv_rho_jacobian hz hw
  have hd : ‖deriv (sigmaInv z) w‖ ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 2 ≠ 0), mul_zero] at hJ
    exact hrw.ne' hJ.symm
  rw [norm_mul, norm_pow, ← hJ]
  field_simp

theorem wp_sigmaInv_resolvent_area (f : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    (∫ v in unitDisc, resolventKernel (conj z)⁻¹ v * ‖f v‖ ^ 2 * (rho v)⁻¹) =
      ∫ w in unitDisc, resolventKernel 0 w *
        ‖f (sigmaInv z w) * deriv (sigmaInv z) w ^ 2‖ ^ 2 * (rho w)⁻¹ := by
  have hσ := wp_sigmaInv_disk_conformal hz
  have hi := ahP_integral_image (U := unitDisc) isOpen_ball hσ.1 hσ.2.1
    (fun v : ℂ => resolventKernel (conj z)⁻¹ v * ‖f v‖ ^ 2 * (rho v)⁻¹)
  rw [hσ.2.2] at hi
  rw [hi]
  apply setIntegral_congr_fun measurableSet_ball
  intro w hw
  have hrw : 0 < rho w := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hw).ne
  have hrs : 0 < rho (sigmaInv z w) :=
    rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp (hσ.mapsTo hw)).ne
  have hJ := wp_sigmaInv_rho_jacobian hz hw
  have hd : ‖deriv (sigmaInv z) w‖ ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 2 ≠ 0), mul_zero] at hJ
    exact hrw.ne' hJ.symm
  dsimp only
  rw [smul_eq_mul, wp_sigmaInv_center_kernel hz hw, norm_mul, norm_pow, ← hJ]
  field_simp
  <;> ring



theorem wp_AInf_disc_measurable (φ : AInf unitDisc) : Measurable (AInf.toFun φ) := by
  have h := φ.property.continuousOn.measurable_piecewise
    (show ContinuousOn (fun _ : ℂ => (0 : ℂ)) unitDiscᶜ from continuousOn_const)
    measurableSet_ball
  have he : unitDisc.piecewise (AInf.toFun φ) (fun _ => 0) = AInf.toFun φ := by
    funext z
    by_cases hz : z ∈ unitDisc
    · simp [hz]
    · simp [hz, AInf.toFun, unweight]
  change Measurable (unitDisc.piecewise (AInf.toFun φ) (fun _ => 0)) at h
  rwa [he] at h

theorem wp_AInf_disc_weighted_bound (φ : AInf unitDisc) {w : ℂ} (hw : w ∈ unitDisc) :
    ‖AInf.toFun φ w‖ * (rho w)⁻¹ ≤ ‖φ‖ / 4 := by
  have hw1 := mem_ball_zero_iff.mp hw
  have hr : 0 < rho w := rho_pos_of_norm_ne_one hw1.ne
  have hd : 1 - ‖w‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg w]
  calc
    _ ≤ (‖φ‖ / (1 - ‖w‖ ^ 2) ^ 2) * (rho w)⁻¹ :=
      mul_le_mul_of_nonneg_right (AInf_disc_pointwise_bound φ hw) (inv_nonneg.mpr hr.le)
    _ = _ := by
      rw [show (rho w)⁻¹ = (1 - ‖w‖ ^ 2) ^ 2 / 4 by simp only [rho, inv_div]]
      exact div_mul_div_cancel₀ (pow_ne_zero 2 hd)

theorem wp_resolvent_quadratic_integrable {F : ℂ → ℂ} (hm : Measurable F)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ w ∈ unitDisc, ‖F w‖ * (rho w)⁻¹ ≤ M)
    {a : ℂ} (ha : a ∈ unitDisc) :
    IntegrableOn (fun w => resolventKernel a w * ‖F w‖ ^ 2 * (rho w)⁻¹) unitDisc := by
  have hρ : Measurable rho :=
    measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)
  let g : ℂ → ℝ := fun w => (‖F w‖ * (rho w)⁻¹) ^ 2
  have hg : AEStronglyMeasurable g (volume.restrict unitDisc) :=
    ((hm.norm.mul hρ.inv).pow_const 2).aestronglyMeasurable
  have hgb : ∀ᵐ w ∂(volume.restrict unitDisc), ‖g w‖ ≤ M ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    have hr : 0 ≤ rho w := by unfold rho; positivity
    have hp : 0 ≤ ‖F w‖ * (rho w)⁻¹ := by positivity
    have hh := hb w hw
    dsimp [g]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hi := (resolvent_mass_integrable (Or.inl rfl) ha).mul_bdd hg hgb
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  have hr : 0 < rho w := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hw).ne
  dsimp [g]
  field_simp
  <;> ring

end TakhtajanTeo



