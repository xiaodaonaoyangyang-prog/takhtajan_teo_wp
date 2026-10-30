import TakhtajanTeo.Ch1.ComponentNonlinearFormula

/-! Local injectivity of the sphere-valued nonlinear reflection on the
actual exterior collar, including mapping poles. No boundary seam is treated. -/
open Complex Set Metric Filter Topology
open scoped ComplexConjugate
noncomputable section

namespace TakhtajanTeo
open LiZhongQC

def cnl_sphere (A B h : ℂ → ℂ) (u : ℂ) : ExtPlane :=
  t203_ratio (A (h u) + (u - h u) * deriv A (h u))
    (B (h u) + (u - h u) * deriv B (h u))

-- L1
theorem cnl_inverse_chart (A B h : ℂ → ℂ) :
    (fun u => -1 / cnf_finite A B h u) =
      fun u => -(B (h u) + (u - h u) * deriv B (h u)) /
        (A (h u) + (u - h u) * deriv A (h u)) := by
  unfold cnf_finite
  rw [t203_neg_inv_F A (deriv A) B (deriv B) h]
  funext u
  dsimp only
  congr 1
  ring

-- L2
theorem cnl_real_ift {f : ℂ → ℂ} {u : ℂ} (hc : ContDiffAt ℝ 1 f u)
    (hlt : ‖dzbar f u‖ < ‖dz f u‖) :
    ∃ V ∈ 𝓝 u, InjOn f V := by
  have hJ : LinearMap.det (fderiv ℝ f u : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by
    rw [det_fderiv_eq_jacobian (hc.differentiableAt one_ne_zero), jacobian]
    have h0 := norm_nonneg (dzbar f u)
    nlinarith
  exact ba_injOn_of_contDiff hc hJ

-- L3
theorem cnl_sphere_locally_injective {Ω E : Set ℂ} (hΩ : IsOpen Ω) (hE : IsOpen E)
    {A B q h : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A Ω) (hB : DifferentiableOn ℂ B Ω)
    (ho : ∀ z ∈ Ω, deriv (deriv A) z + q z / 2 * A z = 0 ∧
      deriv (deriv B) z + q z / 2 * B z = 0 ∧ A z * deriv B z - B z * deriv A z = 1)
    (hC1 : ContDiffOn ℝ 1 h E) (hmap : MapsTo h E Ω)
    {u : ℂ} (hu : u ∈ E)
    (hsmall : ‖q (h u)‖ * ‖h u - u‖ ^ 2 * ‖fderiv ℝ h u‖ ≤ 1) :
    ∃ U ∈ 𝓝 u, IsOpen U ∧ U ⊆ E ∧ InjOn (cnl_sphere A B h) U := by
  let N : ℂ → ℂ := fun v => A (h v) + (v - h v) * deriv A (h v)
  let D : ℂ → ℂ := fun v => B (h v) + (v - h v) * deriv B (h v)
  have hv := hmap hu
  have hhc : ContDiffAt ℝ 1 h u := hC1.contDiffAt (hE.mem_nhds hu)
  have hN : ContDiffAt ℝ 1 N u := t203_c1_cd_num hΩ hA hhc hv
  have hD : ContDiffAt ℝ 1 D u := t203_c1_cd_num hΩ hB hhc hv
  have hbound := t203_mu_w (F := cnf_finite A B h) (φ := q)
    (hhc.differentiableAt one_ne_zero)
    (hA.differentiableAt (hΩ.mem_nhds hv))
    ((hA.deriv hΩ).differentiableAt (hΩ.mem_nhds hv))
    (hB.differentiableAt (hΩ.mem_nhds hv))
    ((hB.deriv hΩ).differentiableAt (hΩ.mem_nhds hv))
    (ho _ hv).1 (ho _ hv).2.1 (ho _ hv).2.2 rfl
    (by norm_num : (1 : ℝ) < 2) hsmall
  by_cases hd : D u = 0
  · have hn : N u ≠ 0 := t203_num_ne_zero (ho _ hv).2.2 hd
    have hc : ContDiffAt ℝ 1 (fun v => -1 / cnf_finite A B h v) u := by
      rw [cnl_inverse_chart]
      exact (hD.neg.mul (hN.inv hn)).congr_of_eventuallyEq
        (Eventually.of_forall fun v => div_eq_mul_inv _ _)
    obtain ⟨V, hV, hi⟩ := cnl_real_ift hc (hbound.2 hd).1
    rw [cnl_inverse_chart] at hi
    have hs : V ∩ E ∩ {v | N v ≠ 0} ∈ 𝓝 u :=
      inter_mem (inter_mem hV (hE.mem_nhds hu)) (hN.continuousAt.eventually_ne hn)
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hs
    refine ⟨ball u δ, ball_mem_nhds u hδ, isOpen_ball,
      fun v hv => (hδsub hv).1.2, ?_⟩
    intro x hx y hy hxy
    apply hi (hδsub hx).1.1 (hδsub hy).1.1
    have hnx := (hδsub hx).2
    have hny := (hδsub hy).2
    have he : t203_ratio (D x) (N x) = t203_ratio (D y) (N y) := by
      apply t203_pack_mobius_injective (a := 0) (b := 1) (c := 1) (d := 0) (by norm_num)
      rw [t203_cont_ratio_inv hnx (D x), t203_cont_ratio_inv hny (D y)]
      exact hxy
    simp only [t203_ratio, ite_eq_right hnx, ite_eq_right hny] at he
    have hval : D x / N x = D y / N y := OnePoint.coe_injective he
    change -D x / N x = -D y / N y
    simpa only [neg_div] using congrArg (fun v : ℂ => -v) hval
  · have hc : ContDiffAt ℝ 1 (cnf_finite A B h) u :=
      (hN.mul (hD.inv hd)).congr_of_eventuallyEq
        (Eventually.of_forall fun v => div_eq_mul_inv _ _)
    obtain ⟨V, hV, hi⟩ := cnl_real_ift hc (hbound.1 hd).1
    have hs : V ∩ E ∩ {v | D v ≠ 0} ∈ 𝓝 u :=
      inter_mem (inter_mem hV (hE.mem_nhds hu)) (hD.continuousAt.eventually_ne hd)
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hs
    refine ⟨ball u δ, ball_mem_nhds u hδ, isOpen_ball,
      fun v hv => (hδsub hv).1.2, ?_⟩
    intro x hx y hy hxy
    apply hi (hδsub hx).1.1 (hδsub hy).1.1
    have hdx := (hδsub hx).2
    have hdy := (hδsub hy).2
    change t203_ratio (N x) (D x) = t203_ratio (N y) (D y) at hxy
    simp only [t203_ratio, ite_eq_right hdx, ite_eq_right hdy] at hxy
    exact OnePoint.coe_injective hxy

-- L4
theorem cnl_chosen_local {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc) :
    ∃ (h A B : ℂ → ℂ) (R : ℝ),
      IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h ∧
      ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior) ∧ 1 < R ∧
      DifferentiableOn ℂ A (fsans μ '' unitDisc) ∧
      DifferentiableOn ℂ B (fsans μ '' unitDisc) ∧
      (∀ z ∈ fsans μ '' unitDisc,
        deriv (deriv A) z + schwarzianHol (crs_transition μ ν) z / 2 * A z = 0 ∧
        deriv (deriv B) z + schwarzianHol (crs_transition μ ν) z / 2 * B z = 0 ∧
        A z * deriv B z - B z * deriv A z = 1) ∧
      (∀ z ∈ fsans μ '' unitDisc,
        (crs_transition μ ν z : ExtPlane) = t203_ratio (A z) (B z)) ∧
      ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < R →
        ∃ U ∈ 𝓝 (gsans μ w), IsOpen U ∧ U ⊆ gsans μ '' unitDiscExterior ∧
          InjOn (cnl_sphere A B h) U := by
  obtain ⟨A, B, hA, hB, ho, he⟩ := cnf_pair hμ hν
  obtain ⟨h, hh, hC1, hcol⟩ := crc_schwarzian_chosen_collar hμ hν hP
  obtain ⟨R, hR, hb⟩ := hcol (1/2) (by norm_num) (by norm_num)
  refine ⟨h, A, B, R, hh, hC1, hR, hA, hB, ho, he, ?_⟩
  intro w hw hwR
  have hu : gsans μ w ∈ gsans μ '' unitDiscExterior := ⟨w, hw, rfl⟩
  have hΩ := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hE := (S2C.s2c_conf_g hμ).isOpen resolvent_exterior_isOpen
  have hs := (hb w hw hwR).1
  norm_num at hs
  have hsmall : ‖schwarzianHol (crs_transition μ ν) (h (gsans μ w))‖ *
      ‖h (gsans μ w) - gsans μ w‖ ^ 2 * ‖fderiv ℝ h (gsans μ w)‖ ≤ 1 := by
    rw [norm_sub_rev]
    exact hs.le
  exact cnl_sphere_locally_injective hΩ hE hA hB ho hC1 hh.2.1 hu hsmall

end TakhtajanTeo
