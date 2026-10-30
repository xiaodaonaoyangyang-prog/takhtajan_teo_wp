import TakhtajanTeo.Ch1.S7Polarization
import TakhtajanTeo.Ch1.WPChangeOfVariables

/-! Actual weighted L2 parameter domain for Qfun. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC WPCV

theorem s7ql_normL2_mono {D : Set ℂ} {f g : ℂ → ℂ}
    (he : ∀ᵐ z ∂(volume.restrict D), ‖f z‖ ≤ ‖g z‖) : normL2 D f ≤ normL2 D g := by
  unfold normL2
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply lintegral_mono_ae
  filter_upwards [he] with z hz
  gcongr
  exact_mod_cast hz

/-- The inverse of the normalized inverse QC map is the original finite
map wherever its source and target are genuine nonzero finite points. -/
theorem s7ql_invFun_inverse {η : LinfStar} (hη : η ∈ LinfStarBall) {z : ℂ}
    (hz : z ≠ 0) (hw : wA η z ≠ 0) :
    Function.invFun (wA (beltramiInv η)) z = wA η z := by
  have he := congrFun (grp_wAS_inv_right hη) (z : ExtPlane)
  simp only [Function.comp_apply, id_eq] at he
  rw [bc_wAS_eq_coe_of_wA_ne_zero hw] at he
  have hv : wA (beltramiInv η) (wA η z) = z := by
    change finPart (wAS (beltramiInv η) (wA η z : ExtPlane)) = z
    rw [he]
    rfl
  have ht := bc_invFun_wA (μ := beltramiInv η) (by rw [hv]; exact hz)
  rwa [hv] at ht

theorem s7ql_invFun_inverse_ae {η : LinfStar} (hη : η ∈ LinfStarBall) :
    (fun z => Function.invFun (wA (beltramiInv η)) z) =ᵐ[volume.restrict unitDiscExterior]
      (wA η) := by
  filter_upwards [wpcv_ae_not_pole hη, ae_restrict_mem resolvent_exterior_isOpen.measurableSet]
    with z hw hz
  apply s7ql_invFun_inverse hη (resolvent_exterior_ne_zero hz)
  exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hw))

/-- Harmonic L2 inputs remain L2 under the actual forward QC composition.
The existing inverse Rnm estimate supplies an integrable majorant. -/
theorem s7ql_harmonic_comp_finite {ψ : ℂ → ℂ} (hψ : ψ ∈ harmonicL2 unitDiscExterior)
    {η : LinfStar} (hη : η ∈ LinfStarBall) :
    normL2 unitDiscExterior (fun z => ψ (wA η z)) < ∞ := by
  have hi := grp_inv_mem hη
  have hib : ‖beltramiInv η‖ < 1 := wpcv_norm_lt_one hi
  have hbound : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖ψ (wA η z)‖ ≤ ‖Rnm (toLinf ψ) (beltramiInv η) z‖ := by
    filter_upwards [bc_Rnm_ae hi (toLinf ψ),
      bc_invFun_pullback_ae hi (wp_harmonic_toLinf_ae hψ),
      bc_invFun_pullback_ae hi (LinfStar_ae_norm_le (beltramiInv η)),
      bc_invFun_pullback_ae hi (ae_restrict_of_ae (bc_wA_ae hi)),
      s7ql_invFun_inverse_ae hη] with z hR hrep hcoef hdiff hinv
    let x := Function.invFun (wA (beltramiInv η)) z
    have hx : ‖beltramiInv η x‖ < 1 := lt_of_le_of_lt hcoef hib
    have hd : 0 < 1 - ‖beltramiInv η x‖ ^ 2 := by nlinarith [norm_nonneg (beltramiInv η x)]
    have hdC : (1 - (‖beltramiInv η x‖ : ℂ) ^ 2) = ((1 - ‖beltramiInv η x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    have hn : ‖Rnm (toLinf ψ) (beltramiInv η) z‖ = ‖ψ x‖ / (1 - ‖beltramiInv η x‖ ^ 2) := by
      rw [hR, hrep]
      change ‖ψ x / (1 - (‖beltramiInv η x‖ : ℂ) ^ 2) *
        (dz (wA (beltramiInv η)) x / conj (dz (wA (beltramiInv η)) x))‖ = _
      rw [norm_mul, norm_div, hdC, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd,
        norm_div, norm_conj, div_self (norm_ne_zero_iff.mpr hdiff.2.1), mul_one]
    rw [hn, ← hinv]
    apply (le_div_iff₀ hd).mpr
    exact mul_le_of_le_one_right (norm_nonneg _) (by nlinarith [sq_nonneg ‖beltramiInv η x‖])
  exact (s7ql_normL2_mono hbound).trans_lt (x5_Rnm_L2 hψ hi)

/-- Qfun is an actual measurable finite-energy function for every admissible
base coefficient, not just at zero. -/
theorem s7ql_Qfun_mem {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {η : LinfStar} (hη : η ∈ LinfStarBall) :
    AEStronglyMeasurable (Qfun (toLinf μ) η) (volume.restrict unitDiscExterior) ∧
      normL2 unitDiscExterior (Qfun (toLinf μ) η) < ∞ := by
  have hR := x5_Rnm_L2 hμ hη
  obtain ⟨⟨ψ, hψ, hrep⟩, _⟩ := harmonicProj_orthogonal (Rnm (toLinf μ) η) hR
  have hP : (fun z => harmonicProjFun (RnmFun (toLinf μ) η) z) =ᵐ[volume.restrict unitDiscExterior] ψ :=
    (wpcv_P_Rnm_ae hη (toLinf μ)).symm.trans hrep
  let phase := fun z => conj (dz (wA η) z) / dz (wA η) z
  have he : Qfun (toLinf μ) η =ᵐ[volume.restrict unitDiscExterior]
      (fun z => ψ (wA η z) * phase z) := by
    filter_upwards [bc_pullback_ae hη hP] with z hz
    change harmonicProjFun (RnmFun (toLinf μ) η) (wA η z) * phase z = _
    rw [hz]
  have hph : Measurable phase :=
    (Complex.continuous_conj.measurable.comp (measurable_dz _)).div (measurable_dz _)
  have hm : AEStronglyMeasurable (fun z => ψ (wA η z) * phase z) (volume.restrict unitDiscExterior) :=
    (bc_comp_aesm hη (s7pol_harmonic_measurable hψ)).mul hph.aestronglyMeasurable
  refine ⟨hm.congr he.symm, ?_⟩
  have hb : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖Qfun (toLinf μ) η z‖ ≤ ‖ψ (wA η z)‖ := by
    filter_upwards [he] with z hz
    rw [hz, norm_mul]
    have hp : ‖phase z‖ ≤ 1 := by
      dsimp [phase]
      by_cases hd : dz (wA η) z = 0
      · simp [hd]
      · simp [norm_div, norm_conj, norm_ne_zero_iff.mpr hd]
    exact mul_le_of_le_one_right (norm_nonneg _) hp
  exact (s7ql_normL2_mono hb).trans_lt (s7ql_harmonic_comp_finite hψ hη)

/-- A common positive parameter neighborhood consists of genuine weighted
L2 values of the actual family. -/
theorem s7ql_parameter_neighborhood {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (κ : LinfStar) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε ∈ ball (0 : ℂ) r,
      AEStronglyMeasurable (Qfun (toLinf μ) (ε • κ)) (volume.restrict unitDiscExterior) ∧
        normL2 unitDiscExterior (Qfun (toLinf μ) (ε • κ)) < ∞ := by
  refine ⟨(‖κ‖ + 1)⁻¹, by positivity, ?_⟩
  intro ε hε
  apply s7ql_Qfun_mem hμ
  have he : ‖ε‖ < 1 / (‖κ‖ + 1) := by simpa only [mem_ball_zero_iff, one_div] using hε
  have ht := (lt_div_iff₀ (by positivity : 0 < ‖κ‖ + 1)).mp he
  change ε • κ ∈ ball (0 : LinfStar) 1
  apply mem_ball_zero_iff.mpr
  rw [norm_smul]
  nlinarith [norm_nonneg ε]

end TakhtajanTeo
