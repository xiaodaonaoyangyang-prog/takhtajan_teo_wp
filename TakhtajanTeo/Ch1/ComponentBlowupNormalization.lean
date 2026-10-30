import TakhtajanTeo.Ch1.ComponentRelativeAmbient

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def cbl_scale (a : ℂ) : ℂ := -(((1 - ‖a‖) / 2 : ℝ) : ℂ) * a / (‖a‖ : ℂ)

def cbl_source (a t : ℂ) : ℂ := a + cbl_scale a * t

def cbl_normalized (e : ℂ ≃ₜ ℂ) (a t : ℂ) : ℂ :=
  (e (cbl_source a t) - e a) / (e (cbl_source a 1) - e a)

theorem cbl_scale_ne_zero {a : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) :
    cbl_scale a ≠ 0 := by
  unfold cbl_scale
  exact div_ne_zero (mul_ne_zero
    (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (by positivity)))
    (norm_pos_iff.mp ha0)) (Complex.ofReal_ne_zero.mpr ha0.ne')

theorem cbl_scale_norm {a : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) :
    ‖cbl_scale a‖ = (1 - ‖a‖) / 2 := by
  rw [cbl_scale, norm_div, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (1 - ‖a‖)/2),
    abs_of_pos ha0]
  exact mul_div_cancel_right₀ _ ha0.ne'

@[simp] theorem cbl_source_zero (a : ℂ) : cbl_source a 0 = a := by
  simp [cbl_source]

theorem cbl_source_one_ne {a : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) :
    cbl_source a 1 ≠ a := by
  intro he
  apply cbl_scale_ne_zero ha0 ha1
  simpa [cbl_source] using congrArg (fun z : ℂ => z-a) he

theorem cbl_source_one_mem {a : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) :
    cbl_source a 1 ∈ unitDisc := by
  rw [unitDisc, mem_ball_zero_iff]
  have hb := norm_add_le a (cbl_scale a)
  rw [cbl_scale_norm ha0 ha1] at hb
  simp only [cbl_source, mul_one]
  linarith

theorem cbl_image_difference_ne_zero (e : ℂ ≃ₜ ℂ) {a : ℂ}
    (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) :
    e (cbl_source a 1) - e a ≠ 0 :=
  sub_ne_zero.mpr (fun he => cbl_source_one_ne ha0 ha1 (e.injective he))

theorem cbl_source_conformal {a : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) :
    IsConformalOnto (cbl_source a) univ univ := by
  change IsConformalOnto (fun t => a + cbl_scale a*t) univ univ
  simpa only [add_comm] using td_affine_conformal a (cbl_scale_ne_zero ha0 ha1)

@[simp] theorem cbl_normalized_zero (e : ℂ ≃ₜ ℂ) (a : ℂ) : cbl_normalized e a 0 = 0 := by
  simp [cbl_normalized]

theorem cbl_normalized_one (e : ℂ ≃ₜ ℂ) {a : ℂ}
    (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) : cbl_normalized e a 1 = 1 :=
  div_self (cbl_image_difference_ne_zero e ha0 ha1)

/-- Both affine normalizations preserve the actual K and the plane image. -/
theorem cbl_normalized_qc (e : ℂ ≃ₜ ℂ) {K : ℝ} (he : IsKQC e univ K)
    {a : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) :
    IsKQC (cbl_normalized e a) univ K ∧ cbl_normalized e a '' univ = univ := by
  have hc := cbl_source_conformal ha0 ha1
  have hpre : IsKQC ((e : ℂ → ℂ) ∘ cbl_source a) univ K := by
    simpa only [one_mul] using
      thm7_1_comp (isKQC_one_of_conformal isOpen_univ hc) he (subset_univ _)
  have honto : ((e : ℂ → ℂ) ∘ cbl_source a) '' univ = univ := by
    rw [image_comp, hc.2.2, image_univ_of_surjective e.surjective]
  exact bB_l_affine_isKQC hpre honto (e a) (cbl_image_difference_ne_zero e ha0 ha1)

/-- Direct input to the S20 normal-family compactness theorems. -/
theorem cbl_normalized_plane (e : ℂ ≃ₜ ℂ) {K : ℝ} (he : IsKQC e univ K)
    {a : ℂ} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) :
    IsKQCNormalizedPlane (cbl_normalized e a) K := by
  obtain ⟨hqc, honto⟩ := cbl_normalized_qc e he ha0 ha1
  exact ⟨hqc, honto, cbl_normalized_zero e a, cbl_normalized_one e ha0 ha1⟩

/-- On the moving interior domain this is the genuine normalized welding
function, with its actual nonzero image-difference denominator. -/
theorem cbl_normalized_interior {μ : LinfStar} (e : ℂ ≃ₜ ℂ)
    (he : EqOn e (fsans μ) unitDisc) {a t : ℂ}
    (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) (ht : cbl_source a t ∈ unitDisc) :
    cbl_normalized e a t =
      (fsans μ (cbl_source a t) - fsans μ a) /
        (fsans μ (cbl_source a 1) - fsans μ a) := by
  rw [cbl_normalized, he ht, he (mem_ball_zero_iff.mpr ha1), he (cbl_source_one_mem ha0 ha1)]

theorem cbl_interior_difference_ne_zero {μ : LinfStar} (e : ℂ ≃ₜ ℂ)
    (he : EqOn e (fsans μ) unitDisc) {a : ℂ}
    (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) :
    fsans μ (cbl_source a 1) - fsans μ a ≠ 0 := by
  have hn := cbl_image_difference_ne_zero e ha0 ha1
  rwa [he (cbl_source_one_mem ha0 ha1), he (mem_ball_zero_iff.mpr ha1)] at hn

/-- One actual welding extension supplies a fixed-K normalized family for
every admissible center, hence for any synchronized sequence of centers. -/
theorem cbl_actual_welding_family {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ (e : ℂ ≃ₜ ℂ) (K : ℝ), 1 ≤ K ∧ IsKQC e univ K ∧ EqOn e (fsans μ) unitDisc ∧
      ∀ a : ℂ, 0 < ‖a‖ → ‖a‖ < 1 → IsKQCNormalizedPlane (cbl_normalized e a) K := by
  obtain ⟨e, K, heK, he⟩ := cra_welding_extension hμ
  exact ⟨e, K, heK.2.1, heK, he, fun _ ha0 ha1 => cbl_normalized_plane e heK ha0 ha1⟩

#print axioms cbl_scale_ne_zero
#print axioms cbl_scale_norm
#print axioms cbl_source_zero
#print axioms cbl_source_one_ne
#print axioms cbl_source_one_mem
#print axioms cbl_image_difference_ne_zero
#print axioms cbl_source_conformal
#print axioms cbl_normalized_zero
#print axioms cbl_normalized_one
#print axioms cbl_normalized_qc
#print axioms cbl_normalized_plane
#print axioms cbl_normalized_interior
#print axioms cbl_interior_difference_ne_zero
#print axioms cbl_actual_welding_family
end TakhtajanTeo
