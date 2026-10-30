import TakhtajanTeo.Ch1.ComponentNonlinearLocal

/-! Contact jets of the actual ODE-pair sphere map. The mapping-value
denominator is controlled by the contact jet, independently of the Beltrami
coefficient denominator. No boundary trace or global lift is asserted. -/
open Complex Set Metric Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- J1
theorem ccj_pair_finite {Ω : Set ℂ} {F A B : ℂ → ℂ}
    (he : ∀ v ∈ Ω, (F v : ExtPlane) = t203_ratio (A v) (B v))
    {v : ℂ} (hv : v ∈ Ω) : B v ≠ 0 ∧ F v = A v/B v := by
  have hb : B v ≠ 0 := by
    intro hb0
    have h := he v hv
    simp [t203_ratio,hb0,extInf] at h
  refine ⟨hb,OnePoint.coe_injective ?_⟩
  simpa only [t203_ratio,ite_eq_right hb] using he v hv

-- J2
theorem ccj_pair_deriv {Ω : Set ℂ} (hΩ : IsOpen Ω) {F A B : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A Ω) (hB : DifferentiableOn ℂ B Ω)
    (hW : ∀ v ∈ Ω, A v*deriv B v-B v*deriv A v = 1)
    (he : ∀ v ∈ Ω, (F v : ExtPlane) = t203_ratio (A v) (B v))
    {v : ℂ} (hv : v ∈ Ω) : deriv F v = -1/(B v)^2 := by
  have hb := (ccj_pair_finite he hv).1
  have hloc : F =ᶠ[𝓝 v] fun w => A w/B w := by
    filter_upwards [hΩ.mem_nhds hv] with w hw
    exact (ccj_pair_finite he hw).2
  have hd := ((hA.differentiableAt (hΩ.mem_nhds hv)).hasDerivAt).div
    ((hB.differentiableAt (hΩ.mem_nhds hv)).hasDerivAt) hb
  have hw : deriv A v*B v-A v*deriv B v = -1 := by
    linear_combination -(hW v hv)
  calc
    deriv F v = deriv (fun w => A w/B w) v := hloc.deriv_eq
    _ = (deriv A v*B v-A v*deriv B v)/(B v)^2 := hd.deriv
    _ = -1/(B v)^2 := by rw [hw]

-- J3
theorem ccj_pair_jet {Ω : Set ℂ} (hΩ : IsOpen Ω) {F A B : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A Ω) (hB : DifferentiableOn ℂ B Ω)
    (hW : ∀ v ∈ Ω, A v*deriv B v-B v*deriv A v = 1)
    (he : ∀ v ∈ Ω, (F v : ExtPlane) = t203_ratio (A v) (B v))
    {v : ℂ} (hv : v ∈ Ω) :
    B v ≠ 0 ∧ F v = A v/B v ∧ deriv F v ≠ 0 ∧
      deriv F v = -1/(B v)^2 ∧ deriv (deriv F) v = 2*deriv B v/(B v)^3 := by
  obtain ⟨hb,hval⟩ := ccj_pair_finite he hv
  have hd := ccj_pair_deriv hΩ hA hB hW he hv
  have hdn : deriv F v ≠ 0 := by
    rw [hd]
    exact div_ne_zero (by norm_num) (pow_ne_zero 2 hb)
  refine ⟨hb,hval,hdn,hd,?_⟩
  have hloc : deriv F =ᶠ[𝓝 v] fun w => -1/(B w)^2 := by
    filter_upwards [hΩ.mem_nhds hv] with w hw
    exact ccj_pair_deriv hΩ hA hB hW he hw
  have hBd := (hB.differentiableAt (hΩ.mem_nhds hv)).hasDerivAt
  have hdd := (hasDerivAt_const v (-1 : ℂ)).div (hBd.pow 2) (pow_ne_zero 2 hb)
  simp only [Pi.pow_apply] at hdd
  calc
    deriv (deriv F) v = deriv (fun w => -1/(B w)^2) v := hloc.deriv_eq
    _ = 2*deriv B v/(B v)^3 := by
      convert hdd.deriv using 1 <;> field_simp <;> ring

-- J4
theorem ccj_contact {Ω : Set ℂ} (hΩ : IsOpen Ω) {F A B h : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A Ω) (hB : DifferentiableOn ℂ B Ω)
    (hW : ∀ v ∈ Ω, A v*deriv B v-B v*deriv A v = 1)
    (he : ∀ v ∈ Ω, (F v : ExtPlane) = t203_ratio (A v) (B v))
    {u : ℂ} (hu : h u ∈ Ω)
    (hjet : 1-(u-h u)*deriv (deriv F) (h u)/(2*deriv F (h u)) ≠ 0) :
    B (h u)+(u-h u)*deriv B (h u) ≠ 0 ∧
      cnl_sphere A B h u = ((F (h u)+(u-h u)*deriv F (h u)/
        (1-(u-h u)*deriv (deriv F) (h u)/(2*deriv F (h u))) : ℂ) : ExtPlane) := by
  obtain ⟨hb,hval,_,hd,hdd⟩ := ccj_pair_jet hΩ hA hB hW he hu
  have hfactor : 1-(u-h u)*deriv (deriv F) (h u)/(2*deriv F (h u)) =
      (B (h u)+(u-h u)*deriv B (h u))/B (h u) := by
    rw [hdd,hd]
    field_simp
    <;> ring
  have hmap : B (h u)+(u-h u)*deriv B (h u) ≠ 0 := by
    intro hzero
    apply hjet
    rw [hfactor,hzero,zero_div]
  have hcontact : (A (h u)+(u-h u)*deriv A (h u))/(B (h u)+(u-h u)*deriv B (h u)) =
      F (h u)+(u-h u)*deriv F (h u)/
        (1-(u-h u)*deriv (deriv F) (h u)/(2*deriv F (h u))) := by
    rw [hfactor,hval,hd]
    field_simp
    linear_combination -(u-h u)*(hW (h u) hu)
  refine ⟨hmap,?_⟩
  simp only [cnl_sphere,t203_ratio,ite_eq_right hmap]
  exact congrArg (fun w : ℂ => (w : ExtPlane)) hcontact

-- J5: all conclusions use the same actual pair supplied by cnf_pair.
theorem ccj_transition_pair {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ∃ A B : ℂ → ℂ,
      DifferentiableOn ℂ A (fsans μ '' unitDisc) ∧
      DifferentiableOn ℂ B (fsans μ '' unitDisc) ∧
      (∀ v ∈ fsans μ '' unitDisc,
        deriv (deriv A) v+schwarzianHol (crs_transition μ ν) v/2*A v = 0 ∧
        deriv (deriv B) v+schwarzianHol (crs_transition μ ν) v/2*B v = 0 ∧
        A v*deriv B v-B v*deriv A v = 1) ∧
      (∀ v ∈ fsans μ '' unitDisc,
        (crs_transition μ ν v : ExtPlane) = t203_ratio (A v) (B v)) ∧
      (∀ v ∈ fsans μ '' unitDisc,
        B v ≠ 0 ∧ crs_transition μ ν v = A v/B v ∧ deriv (crs_transition μ ν) v ≠ 0 ∧
        deriv (crs_transition μ ν) v = -1/(B v)^2 ∧
        deriv (deriv (crs_transition μ ν)) v = 2*deriv B v/(B v)^3) ∧
      ∀ (h : ℂ → ℂ) (u : ℂ), h u ∈ fsans μ '' unitDisc →
        1-(u-h u)*deriv (deriv (crs_transition μ ν)) (h u)/(2*deriv (crs_transition μ ν) (h u)) ≠ 0 →
        B (h u)+(u-h u)*deriv B (h u) ≠ 0 ∧
        cnl_sphere A B h u = ((crs_transition μ ν (h u)+(u-h u)*deriv (crs_transition μ ν) (h u)/
          (1-(u-h u)*deriv (deriv (crs_transition μ ν)) (h u)/(2*deriv (crs_transition μ ν) (h u))) : ℂ) : ExtPlane) := by
  obtain ⟨A,B,hA,hB,ho,he⟩ := cnf_pair hμ hν
  have hΩ := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hW : ∀ v ∈ fsans μ '' unitDisc, A v*deriv B v-B v*deriv A v = 1 :=
    fun v hv => (ho v hv).2.2
  refine ⟨A,B,hA,hB,ho,he,?_,?_⟩
  · intro v hv
    exact ccj_pair_jet hΩ hA hB hW he hv
  · intro h u hu hjet
    exact ccj_contact hΩ hA hB hW he hu hjet

end TakhtajanTeo
