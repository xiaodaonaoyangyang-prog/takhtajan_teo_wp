import TakhtajanTeo.Ch1.ComponentRelativeCollar
import TakhtajanTeo.Ch1.ComponentNonlinearEnergy

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def cnf_finite (A B h : ℂ → ℂ) (u : ℂ) : ℂ :=
  (A (h u) + (u - h u) * deriv A (h u)) /
    (B (h u) + (u - h u) * deriv B (h u))

/-- An actual ODE pair for the relative conformal map, with finite interior
values. This does not assert boundary regularity of the individual solutions. -/
theorem cnf_pair {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ∃ A B : ℂ → ℂ,
      DifferentiableOn ℂ A (fsans μ '' unitDisc) ∧
      DifferentiableOn ℂ B (fsans μ '' unitDisc) ∧
      (∀ z ∈ fsans μ '' unitDisc,
        deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
        deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
        A z * deriv B z - B z * deriv A z = 1) ∧
      ∀ z ∈ fsans μ '' unitDisc,
        (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z) := by
  obtain ⟨K, _, hD, _, _⟩ := hc6_welding_quasidisc hμ
  have hΩ := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hF := crs_conformal hμ hν
  obtain ⟨A, B, hA, hB, ho, he⟩ :=
    t203_ode_pair hD (isLocUnivMero_of_isConformalOnto hΩ hF)
  refine ⟨A, B, hA, hB, ?_, ?_⟩
  · intro z hz
    have ht := ho z hz
    rwa [schwarzian_of_analyticAt (hF.1.analyticAt (hΩ.mem_nhds hz))] at ht
  · intro z hz
    have ht := he z hz
    rwa [t203_univ_meroToExt_of_analyticAt (hF.1.analyticAt (hΩ.mem_nhds hz))] at ht

/-- The finite-chart formula has exactly the nonlinear coefficient already
used in the energy estimate. The mapping-value denominator is explicitly
required nonzero; it is different from the Beltrami denominator. -/
theorem cnf_coefficient {Ω : Set ℂ} (hΩ : IsOpen Ω) {A B q h : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A Ω) (hB : DifferentiableOn ℂ B Ω)
    (ho : ∀ z ∈ Ω, deriv (deriv A) z + q z / 2 * A z = 0 ∧
      deriv (deriv B) z + q z / 2 * B z = 0 ∧ A z * deriv B z - B z * deriv A z = 1)
    {u : ℂ} (hu : h u ∈ Ω) (hh : DifferentiableAt ℝ h u)
    (hd : B (h u) + (u - h u) * deriv B (h u) ≠ 0) :
    complexDilatation (cnf_finite A B h) u = crn_coefficient q h u := by
  have hAd := (hA.differentiableAt (hΩ.mem_nhds hu)).hasDerivAt
  have hBd := (hB.differentiableAt (hΩ.mem_nhds hu)).hasDerivAt
  have hAdd := ((hA.deriv hΩ).differentiableAt (hΩ.mem_nhds hu)).hasDerivAt
  have hBdd := ((hB.deriv hΩ).differentiableAt (hΩ.mem_nhds hu)).hasDerivAt
  rw [eq_neg_of_add_eq_zero_left (ho _ hu).1] at hAdd
  rw [eq_neg_of_add_eq_zero_left (ho _ hu).2.1] at hBdd
  have ht := t203_mu_F hh hAd hAdd hBd hBdd (ho _ hu).2.2 hd
  change complexDilatation (cnf_finite A B h) u = _ at ht
  rw [ht]
  unfold crn_coefficient hbPre_reflected
  congr 1
  ring

/-- The chosen collar produces genuine finite-chart dilatation bounds wherever
the map is finite. No boundary trace, side, or global injection is assumed. -/
theorem cnf_chosen_collar {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc) :
    ∃ (h A B : ℂ → ℂ) (R : ℝ),
      IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h ∧
      1 < R ∧
      (∀ z ∈ fsans μ '' unitDisc,
        (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z)) ∧
      ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < R →
        let u := gsans μ w
        B (h u) + (u - h u) * deriv B (h u) ≠ 0 →
        complexDilatation (cnf_finite A B h) u =
          crn_coefficient (schwarzianHol (crs_transition μ ν)) h u ∧
        ‖complexDilatation (cnf_finite A B h) u‖ ≤ 1 / 2 := by
  obtain ⟨A, B, hA, hB, ho, he⟩ := cnf_pair hμ hν
  obtain ⟨h, hh, hC1, hcol⟩ := crc_schwarzian_chosen_collar hμ hν hP
  obtain ⟨R, hR, hb⟩ := hcol (1/2) (by norm_num) (by norm_num)
  refine ⟨h, A, B, R, hh, hR, he, ?_⟩
  intro w hw hwR
  dsimp only
  intro hd
  have hwE : w ∈ unitDiscExterior := hw
  have hu : gsans μ w ∈ gsans μ '' unitDiscExterior := ⟨w, hwE, rfl⟩
  have hv := hh.2.1 hu
  have hΩ := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hE := (S2C.s2c_conf_g hμ).isOpen resolvent_exterior_isOpen
  have hhd := (hC1.differentiableOn one_ne_zero _ hu).differentiableAt (hE.mem_nhds hu)
  refine ⟨cnf_coefficient hΩ hA hB ho hv hhd hd, ?_⟩
  have hAd := (hA.differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
  have hBd := (hB.differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
  have hAdd := ((hA.deriv hΩ).differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
  have hBdd := ((hB.deriv hΩ).differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
  rw [eq_neg_of_add_eq_zero_left (ho _ hv).1] at hAdd
  rw [eq_neg_of_add_eq_zero_left (ho _ hv).2.1] at hBdd
  have hs := (hb w hw hwR).1
  simp only [mul_one_div, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hs
  have hsmall : ‖schwarzianHol (crs_transition μ ν) (h (gsans μ w))‖ *
      ‖h (gsans μ w) - gsans μ w‖^2 * ‖fderiv ℝ h (gsans μ w)‖ ≤ 1 := by
    rw [norm_sub_rev]
    norm_num at hs
    exact hs.le
  exact (t203_F_bound_book hhd hAd hAdd hBd hBdd (ho _ hv).2.2 hd
    (by norm_num : (1 : ℝ) < 2) hsmall).2

end TakhtajanTeo
