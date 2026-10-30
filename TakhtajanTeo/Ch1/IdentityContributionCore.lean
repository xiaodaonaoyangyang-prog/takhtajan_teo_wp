import TakhtajanTeo.Ch1.FundDomainIntegral
import TakhtajanTeo.Ch1.WeightedBKernel

/-!
# The identity contribution to (8.1) (TT:3466–3472), in pure form

`idc_main` proves, for a `Γ`-invariant pair of disk harmonic Beltrami differentials and any disk fundamental
domain `F`, that the two terms of `identity_contribution` add up to `-(13/(12π)) (μ, ν)_Γ`:
the first by the unfolding `fdD_term_one`, the second by the pointwise moment `wpb_point_moment`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Cofiniteness makes the hyperbolic density integrable on every disk fundamental domain. -/
theorem idc_rho_integrableOn {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {F : Set ℂ}
    (hF : IsFundDomainD Γ F) : IntegrableOn rho F := by
  have hE := isFundDomain_fundDomain hΓ.1
  have h1 : ∫⁻ z in F, ENNReal.ofReal (rho z) = hypArea Γ := by
    rw [fdD_lintegral_rho_independent hΓ.1 hF (fdr_isFundDomainD_refl hΓ.1 hE),
      fdr_lintegral_rho_refl (fundDomain_measurable Γ)
        (fun z hz => fdr_ne_zero_of_exterior (hE.2.1 hz))]
    rfl
  refine ⟨gam_rho_measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hn : ∀ z, ENNReal.ofReal ‖rho z‖ = ENNReal.ofReal (rho z) := fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by norm_num) (sq_nonneg _))]
  simp_rw [hn]
  rw [h1]
  exact hΓ.2

/-- **`identity_contribution`** in pure form (TT:3466–3472). -/
theorem idc_main {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {F : Set ℂ} (hF : IsFundDomainD Γ F)
    {μ ν φ ψ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) {Cφ : ℝ}
    (hCφ : ∀ z ∈ unitDisc, ‖((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * φ z‖ ≤ Cφ)
    (hψ : DifferentiableOn ℂ ψ unitDisc) {Cψ : ℝ}
    (hCψ : ∀ z ∈ unitDisc, ‖((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * ψ z‖ ≤ Cψ)
    (hμ : ∀ z ∈ unitDisc, μ z = ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * conj (φ z))
    (hν : ∀ z ∈ unitDisc, ν z = ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * conj (ψ z))
    (hμΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc,
      μ (mob g z) * (conj (deriv (mob g) z) / deriv (mob g) z) = μ z)
    (hνΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc,
      ν (mob g z) * (conj (deriv (mob g) z) / deriv (mob g) z) = ν z) :
    -(3 / (4 * (π : ℂ))) * (∫ z in unitDisc, ∫ w in F,
        μ z * conj (ν z) * (resolventKernel z w : ℂ) * (rho w : ℂ) * (rho z : ℂ)) -
      (12 / (π : ℂ)) * (∫ z in F, ∫ w in unitDisc,
        μ z * conj (ν w) * (resolventKernel z w : ℂ) / (1 - z * conj w) ^ 4) =
      -(13 / (12 * (π : ℂ))) * (∫ z in F, μ z * conj (ν z) * (rho z : ℂ)) := by
  classical
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  let g : ℂ → ℂ := fun z => (((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * conj (φ z)) *
    conj (((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * conj (ψ z)) * (rho z : ℂ)
  have hgc : ContinuousOn g unitDisc := by
    have h1 : ContinuousOn (fun z : ℂ => ((1 - ‖z‖ ^ 2) ^ 2 : ℝ)) unitDisc := by
      apply Continuous.continuousOn; fun_prop
    have hr : ContinuousOn (fun z : ℂ => (rho z : ℂ)) unitDisc := by
      apply Complex.continuous_ofReal.comp_continuousOn
      intro z hz
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have : (1 - ‖z‖ ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 (by nlinarith [norm_nonneg z])
      unfold rho
      exact (continuousAt_const.div (by fun_prop : ContinuousAt (fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 2) z)
        this).continuousWithinAt
    have hA := (Complex.continuous_ofReal.comp_continuousOn h1).mul
      (Complex.continuous_conj.comp_continuousOn hφ.continuousOn)
    have hB := (Complex.continuous_ofReal.comp_continuousOn h1).mul
      (Complex.continuous_conj.comp_continuousOn hψ.continuousOn)
    exact (hA.mul (Complex.continuous_conj.comp_continuousOn hB)).mul hr
  let f : ℂ → ℂ := unitDisc.piecewise g 0
  have hfm : Measurable f := hgc.measurable_piecewise continuousOn_const hDm
  have hfD : ∀ z ∈ unitDisc, f z = μ z * conj (ν z) * (rho z : ℂ) := by
    intro z hz
    simp only [f, Set.piecewise_eq_of_mem _ _ _ hz, g, hμ z hz, hν z hz]
  have hρi := idc_rho_integrableOn hΓ hF
  have hCφ0 : 0 ≤ Cφ := (norm_nonneg _).trans (hCφ 0 (by simp [unitDisc]))
  have hCψ0 : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ 0 (by simp [unitDisc]))
  have hfi : IntegrableOn f F := by
    refine (hρi.const_mul (Cφ * Cψ)).mono' hfm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hF.1] with z hz
    have hzD := hF.2.1 hz
    have hρ0 : 0 ≤ rho z := div_nonneg (by norm_num) (sq_nonneg _)
    rw [hfD z hzD, norm_mul, norm_mul, norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ0]
    have hμn : ‖μ z‖ ≤ Cφ := by
      rw [hμ z hzD, norm_mul, norm_conj, ← norm_mul]; exact hCφ z hzD
    have hνn : ‖ν z‖ ≤ Cψ := by
      rw [hν z hzD, norm_mul, norm_conj, ← norm_mul]; exact hCψ z hzD
    exact mul_le_mul_of_nonneg_right (mul_le_mul hμn hνn (norm_nonneg _) hCφ0) hρ0
  have hinv : ∀ γ ∈ Γ, ∀ w ∈ unitDisc,
      f (mob γ w) * ((‖deriv (mob γ) w‖ ^ 2 : ℝ) : ℂ) = f w := by
    intro γ hγ w hw
    have hγs := hΓ.1.1 γ hγ
    have hw1 := mem_ball_zero_iff.mp hw
    have hmw : mob γ w ∈ unitDisc := mem_ball_zero_iff.mpr (fdD_mob_lt hγs hw1)
    have hD := fdD_denom_ne hγs hw1
    have hd' : deriv (mob γ) w = 1 / (γ 1 0 * w + γ 1 1) ^ 2 := gam_mob_deriv hD
    have hg0 : deriv (mob γ) w ≠ 0 := by rw [hd']; exact one_div_ne_zero (pow_ne_zero 2 hD)
    have hjac := gam_rho_mob_jacobian hγs hD
    have hjc : (rho (mob γ w) : ℂ) * ((‖deriv (mob γ) w‖ ^ 2 : ℝ) : ℂ) = (rho w : ℂ) := by
      exact_mod_cast hjac
    have h1 := hμΓ γ hγ w hw
    have h2 := hνΓ γ hγ w hw
    have h3 := congrArg conj h2
    simp only [map_mul, map_div₀, conj_conj] at h3
    have hdc : conj (deriv (mob γ) w) ≠ 0 := (map_ne_zero _).mpr hg0
    have hAB : μ (mob γ w) * conj (ν (mob γ w)) = μ w * conj (ν w) := by
      rw [← h1, ← h3]
      field_simp
    rw [hfD _ hmw, hfD _ hw]
    calc μ (mob γ w) * conj (ν (mob γ w)) * (rho (mob γ w) : ℂ) *
          ((‖deriv (mob γ) w‖ ^ 2 : ℝ) : ℂ)
        = μ (mob γ w) * conj (ν (mob γ w)) *
          ((rho (mob γ w) : ℂ) * ((‖deriv (mob γ) w‖ ^ 2 : ℝ) : ℂ)) := by ring
      _ = _ := by rw [hAB, hjc]
  have hT1 := fdD_term_one hΓ.1 hF hfm hinv hfi
  have hrw1 : (∫ z in unitDisc, ∫ w in F,
      μ z * conj (ν z) * (resolventKernel z w : ℂ) * (rho w : ℂ) * (rho z : ℂ)) =
      ∫ z in unitDisc, f z * ((∫ w in F, resolventKernel z w * rho w : ℝ) : ℂ) := by
    refine setIntegral_congr_fun hDm fun z hz => ?_
    have : ∀ w, μ z * conj (ν z) * (resolventKernel z w : ℂ) * (rho w : ℂ) * (rho z : ℂ) =
        f z * ((resolventKernel z w * rho w : ℝ) : ℂ) := fun w => by
      rw [hfD z hz]; push_cast; ring
    simp_rw [this]
    rw [integral_const_mul, integral_complex_ofReal]
  have hrw2 : (∫ z in F, ∫ w in unitDisc,
      μ z * conj (ν w) * (resolventKernel z w : ℂ) / (1 - z * conj w) ^ 4) =
      ∫ z in F, f z / 36 := by
    refine setIntegral_congr_fun hF.1 fun z hz => ?_
    have hzD := hF.2.1 hz
    have hpt : ∀ w ∈ unitDisc,
        μ z * conj (ν w) * (resolventKernel z w : ℂ) / (1 - z * conj w) ^ 4 =
        μ z * ((resolventKernel z w : ℂ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * ψ w /
          (1 - z * conj w) ^ 4) := by
      intro w hw
      rw [hν w hw]
      simp only [map_mul, Complex.conj_ofReal, conj_conj]
      ring
    show (∫ w in unitDisc, μ z * conj (ν w) * (resolventKernel z w : ℂ) / (1 - z * conj w) ^ 4) = _
    rw [setIntegral_congr_fun hDm hpt, integral_const_mul, wpb_point_moment hψ hCψ hzD,
      hfD z hzD, hν z hzD]
    simp only [map_mul, Complex.conj_ofReal, conj_conj]
    have hz1 : (1 - ‖z‖ ^ 2) ≠ 0 := by
      have := mem_ball_zero_iff.mp hzD
      nlinarith [norm_nonneg z]
    have hρ4 : rho z * (1 - ‖z‖ ^ 2) ^ 2 = 4 := by unfold rho; field_simp
    have hρ4c : (rho z : ℂ) * (((1 - ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ) = 4 := by exact_mod_cast hρ4
    linear_combination (-(μ z * ψ z / 36)) * hρ4c
  have hfF : (∫ z in F, μ z * conj (ν z) * (rho z : ℂ)) = ∫ z in F, f z := by
    exact setIntegral_congr_fun hF.1 fun z hz => (hfD z (hF.2.1 hz)).symm
  rw [hrw1, hrw2, hT1.2, hfF, integral_div]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

end TakhtajanTeo
