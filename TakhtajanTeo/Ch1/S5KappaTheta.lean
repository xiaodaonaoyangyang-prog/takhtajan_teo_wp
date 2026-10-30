import TakhtajanTeo.Ch1.S5Prop57
import TakhtajanTeo.Ch1.ResolventDuality
import TakhtajanTeo.Ch1.S4_Metrics

/-!
# The Θ entries of `thetaMatrix` for `thm_5_10` (`s5kt_`, 下属5, Program G)

Host: new module `TakhtajanTeo/Ch1/S5KappaTheta.lean`. Statements are byte-identical copies, prefixed `s5kt_`, of
下属3's stubs `s5k_theta_vert_hor`, `s5k_theta_hor_vert`, `s5k_theta_hor_hor` (`collaboration/下属3/S5Kappa/S5Kappa.lean`
d2b903d3). Those stubs close as one-liners once `S5Kappa` imports this module.

Route. Take `μ' = toLinf μ ∈ Ω^{-1,1}` (`harmonicL2_subset_harmonic`, `wp_harmonic_toLinf_ae`).
* By `s5p57_theta_vk`, `Θ = -2 h_VK`.
* By `s5p57_polarize_L`, `h_VK(X, Y)` at `(0, z)` is the origin form at `(L X, L Y)`.
* `L(∂_z) = (0, a)` and `L(τ_μ) = ((σ_z⁻¹)^* D₀β μ', 0)` (P3, P3′, P4). The latter is linear in `μ'`.
* (vert, hor), (hor, vert): the origin form splits, as in `s5p57_orth` (both orders).
* (hor, hor): polarize `s5p57_hor` over `μ' ± ν'` and `μ' ± i ν'`. Use
  `|a+b|² - |a-b|² + i|a+ib|² - i|a-ib|² = 4 a b̄`. `G` is linear on bounded functions (`resolvent_integrand_integrable_of_bounded`).
  Finally `toLinf μ = μ` a.e.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- `H^{-1,1}(𝔻*) ⊂ Ω^{-1,1}(𝔻*)` (`harmonicL2_subset_harmonic`). -/
theorem s5kt_harm {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) : toLinf μ ∈ harmonicBeltrami := by
  obtain ⟨C, hC⟩ := harmonicL2_subset_harmonic
  exact (hC μ hμ).1

/-- `L_z τ_κ = ((σ_z⁻¹)^* D₀β κ, 0)` (P3, P4). -/
theorem s5kt_L_hor {z : ℂ} (hz : z ∈ unitDiscExterior) {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x (fiberPt z)) (tcCoordH (fiberPt z)) (horVec κ z) =
      (toAInf unitDisc (fun u => AInf.toFun (fderiv ℂ bersPhi 0 κ) (sigmaInv z u) * deriv (sigmaInv z) u ^ 2),
        (0 : ℂ)) :=
  Prod.ext (s5p57_L_fst hz _) (s5p57_L_hor_snd hκ hz)

/-- `G` only sees the a.e. class on `𝔻*`. -/
theorem s5kt_res_congr {f g : ℂ → ℂ} (h : f =ᵐ[volume.restrict unitDiscExterior] g) (z : ℂ) :
    resolventStar f z = resolventStar g z := by
  unfold resolventStar resolventOp
  exact integral_congr_ae (h.mono fun w hw => by simp only [hw])

/-- The polarization identity `|a+b|² - |a-b|² + i|a+ib|² - i|a-ib|² = 4ab̄`. -/
theorem s5kt_pol_id (a b : ℂ) :
    ((‖a + b‖ ^ 2 : ℝ) : ℂ) - ((‖a + (-1) * b‖ ^ 2 : ℝ) : ℂ) + I * ((‖a + I * b‖ ^ 2 : ℝ) : ℂ) -
      I * ((‖a + (-I) * b‖ ^ 2 : ℝ) : ℂ) = 4 * (a * conj b) := by
  apply Complex.ext <;> simp [Complex.sq_norm, Complex.normSq_apply] <;> ring

/-- The resolvent integrand of `|μ + cν|²` (`|c| = 1`) is integrable. -/
theorem s5kt_int_c {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {c : ℂ} (hc : ‖c‖ = 1) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    Integrable (fun w => (resolventKernel z w : ℂ) * ((‖μ w + c * ν w‖ ^ 2 : ℝ) : ℂ) * rho w)
      (volume.restrict unitDiscExterior) := by
  have hcont : ContinuousOn (fun w => ((‖μ w + c * ν w‖ ^ 2 : ℝ) : ℂ)) unitDiscExterior :=
    Complex.continuous_ofReal.comp_continuousOn
      ((((wp_harmonic_continuousOn hμ).add (continuousOn_const.mul (wp_harmonic_continuousOn hν))).norm).pow 2)
  refine resolvent_integrand_integrable_of_bounded (Or.inr rfl)
    (hcont.aestronglyMeasurable wp_exterior_isOpen.measurableSet)
    (C := ((Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior μ).toReal +
      (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior ν).toReal) ^ 2) (fun w hw => ?_) hz
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 := wp_harmonic_pointwise_bound hμ hw
  have h2 := wp_harmonic_pointwise_bound hν hw
  have h3 : ‖μ w + c * ν w‖ ≤ (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior μ).toReal +
      (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior ν).toReal := by
    calc ‖μ w + c * ν w‖ ≤ ‖μ w‖ + ‖c * ν w‖ := norm_add_le _ _
      _ = ‖μ w‖ + ‖ν w‖ := by rw [norm_mul, hc, one_mul]
      _ ≤ _ := add_le_add h1 h2
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

/-- **Stub K1.** `Θ_{(0,z)}(∂_z, τ̄_ν) = 0` (TT:2398, prop_5_7(ii)). -/
theorem s5kt_theta_vert_hor {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    thetaForm (fiberPt z) (vertVec z) (horVec (toLinf ν) z) = 0 := by
  exact (s5p57_prop_5_7 (s5kt_harm hν) hz).2.1.2.1

/-- **Stub K2.** `Θ_{(0,z)}(τ_μ, ∂_z̄) = 0` (TT:2398, prop_5_7(ii)). -/
theorem s5kt_theta_hor_vert {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    thetaForm (fiberPt z) (horVec (toLinf μ) z) (vertVec z) = 0 := by
  have hq := s5vc_fiberPt_mem hz
  rw [s5p57_theta_vk hq, s5p57_polarize_L, s5kt_L_hor hz (s5kt_harm hμ),
    show fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x (fiberPt z)) (tcCoordH (fiberPt z)) (vertVec z) =
      ((0 : AInf unitDisc), (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x (fiberPt z)) (tcCoordH (fiberPt z))
        (vertVec z)).2) from Prod.ext (s5p57_L_vert hz) rfl]
  set ψ := toAInf unitDisc (fun u => AInf.toFun (fderiv ℂ bersPhi 0 (toLinf μ)) (sigmaInv z u) *
    deriv (sigmaInv z) u ^ 2)
  set a := (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x (fiberPt z)) (tcCoordH (fiberPt z)) (vertVec z)).2
  simp only [polarize, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.smul_mk, add_zero, sub_zero, smul_zero,
    zero_add, zero_sub, vkNormSqCoordOrigin, norm_neg, smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
  ring

/-- **Stub K3.** `Θ_{(0,z)}(τ_μ, τ̄_ν) = -G(μν̄)(z)` (TT:2398, prop_5_7(ii) polarized). -/
theorem s5kt_theta_hor_hor {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    thetaForm (fiberPt z) (horVec (toLinf μ) z) (horVec (toLinf ν) z) =
      -resolventStar (fun u => μ u * conj (ν u)) z := by
  have hq := s5vc_fiberPt_mem hz
  have hμ' := s5kt_harm hμ
  have hν' := s5kt_harm hν
  have hμa := wp_harmonic_toLinf_ae hμ
  have hνa := wp_harmonic_toLinf_ae hν
  obtain ⟨P, hP⟩ := s5p57_pull_clm hz
  have hLh : ∀ κ ∈ harmonicBeltrami,
      fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x (fiberPt z)) (tcCoordH (fiberPt z)) (horVec κ z) =
        (P (fderiv ℂ bersPhi 0 κ), (0 : ℂ)) := fun κ hκ => by rw [s5kt_L_hor hz hκ, hP]
  have hN : ∀ κ ∈ harmonicBeltrami, (vkNormSqCoordOrigin (P (fderiv ℂ bersPhi 0 κ), (0 : ℂ)) : ℂ) =
      (1 / 2) * resolventStar (fun u => (‖κ u‖ ^ 2 : ℝ)) z := fun κ hκ => by rw [hP]; exact s5p57_hor hκ hz
  rw [s5p57_theta_vk hq, s5p57_polarize_L, hLh _ hμ', hLh _ hν']
  set μ' := toLinf μ with hμdef
  set ν' := toLinf ν with hνdef
  have e1 : (P (fderiv ℂ bersPhi 0 μ'), (0 : ℂ)) + (P (fderiv ℂ bersPhi 0 ν'), (0 : ℂ)) =
      (P (fderiv ℂ bersPhi 0 (μ' + ν')), (0 : ℂ)) := Prod.ext (by simp) (by simp)
  have e2 : (P (fderiv ℂ bersPhi 0 μ'), (0 : ℂ)) - (P (fderiv ℂ bersPhi 0 ν'), (0 : ℂ)) =
      (P (fderiv ℂ bersPhi 0 (μ' - ν')), (0 : ℂ)) := Prod.ext (by simp) (by simp)
  have e3 : (P (fderiv ℂ bersPhi 0 μ'), (0 : ℂ)) + I • (P (fderiv ℂ bersPhi 0 ν'), (0 : ℂ)) =
      (P (fderiv ℂ bersPhi 0 (μ' + I • ν')), (0 : ℂ)) := Prod.ext (by simp) (by simp)
  have e4 : (P (fderiv ℂ bersPhi 0 μ'), (0 : ℂ)) - I • (P (fderiv ℂ bersPhi 0 ν'), (0 : ℂ)) =
      (P (fderiv ℂ bersPhi 0 (μ' - I • ν')), (0 : ℂ)) := Prod.ext (by simp) (by simp)
  simp only [polarize]
  rw [e1, e2, e3, e4, hN _ (add_mem hμ' hν'), hN _ (sub_mem hμ' hν'),
    hN _ (add_mem hμ' (Submodule.smul_mem _ I hν')), hN _ (sub_mem hμ' (Submodule.smul_mem _ I hν'))]
  -- back to the representatives `μ`, `ν`
  have g1 : resolventStar (fun u => ((‖(μ' + ν') u‖ ^ 2 : ℝ) : ℂ)) z =
      resolventStar (fun u => ((‖μ u + ν u‖ ^ 2 : ℝ) : ℂ)) z := by
    refine s5kt_res_congr ?_ z
    filter_upwards [Lp.coeFn_add μ' ν', hμa, hνa] with u h1 h2 h3
    show ((‖(μ' + ν') u‖ ^ 2 : ℝ) : ℂ) = ((‖μ u + ν u‖ ^ 2 : ℝ) : ℂ)
    rw [h1, Pi.add_apply, h2, h3]
  have g2 : resolventStar (fun u => ((‖(μ' - ν') u‖ ^ 2 : ℝ) : ℂ)) z =
      resolventStar (fun u => ((‖μ u + (-1) * ν u‖ ^ 2 : ℝ) : ℂ)) z := by
    refine s5kt_res_congr ?_ z
    filter_upwards [Lp.coeFn_sub μ' ν', hμa, hνa] with u h1 h2 h3
    show ((‖(μ' - ν') u‖ ^ 2 : ℝ) : ℂ) = ((‖μ u + (-1) * ν u‖ ^ 2 : ℝ) : ℂ)
    rw [h1, Pi.sub_apply, h2, h3, show μ u - ν u = μ u + (-1) * ν u by ring]
  have g3 : resolventStar (fun u => ((‖(μ' + I • ν') u‖ ^ 2 : ℝ) : ℂ)) z =
      resolventStar (fun u => ((‖μ u + I * ν u‖ ^ 2 : ℝ) : ℂ)) z := by
    refine s5kt_res_congr ?_ z
    filter_upwards [Lp.coeFn_add μ' (I • ν'), Lp.coeFn_smul I ν', hμa, hνa] with u h1 h4 h2 h3
    show ((‖(μ' + I • ν') u‖ ^ 2 : ℝ) : ℂ) = ((‖μ u + I * ν u‖ ^ 2 : ℝ) : ℂ)
    rw [h1, Pi.add_apply, h4, Pi.smul_apply, smul_eq_mul, h2, h3]
  have g4 : resolventStar (fun u => ((‖(μ' - I • ν') u‖ ^ 2 : ℝ) : ℂ)) z =
      resolventStar (fun u => ((‖μ u + (-I) * ν u‖ ^ 2 : ℝ) : ℂ)) z := by
    refine s5kt_res_congr ?_ z
    filter_upwards [Lp.coeFn_sub μ' (I • ν'), Lp.coeFn_smul I ν', hμa, hνa] with u h1 h4 h2 h3
    show ((‖(μ' - I • ν') u‖ ^ 2 : ℝ) : ℂ) = ((‖μ u + (-I) * ν u‖ ^ 2 : ℝ) : ℂ)
    rw [h1, Pi.sub_apply, h4, Pi.smul_apply, smul_eq_mul, h2, h3, show μ u - I * ν u = μ u + (-I) * ν u by ring]
  rw [g1, g2, g3, g4]
  -- linearity of `G` on bounded integrands
  have I1 := s5kt_int_c hμ hν (c := 1) (by simp) hz
  have I2 := s5kt_int_c hμ hν (c := -1) (by simp) hz
  have I3 := s5kt_int_c hμ hν (c := I) (by simp) hz
  have I4 := s5kt_int_c hμ hν (c := -I) (by simp) hz
  simp only [one_mul] at I1
  have hA : Integrable (fun w => (resolventKernel z w : ℂ) * ((‖μ w + ν w‖ ^ 2 : ℝ) : ℂ) * rho w -
      (resolventKernel z w : ℂ) * ((‖μ w + (-1) * ν w‖ ^ 2 : ℝ) : ℂ) * rho w) (volume.restrict unitDiscExterior) :=
    I1.sub I2
  have hB : Integrable (fun w => (resolventKernel z w : ℂ) * ((‖μ w + ν w‖ ^ 2 : ℝ) : ℂ) * rho w -
      (resolventKernel z w : ℂ) * ((‖μ w + (-1) * ν w‖ ^ 2 : ℝ) : ℂ) * rho w +
      I * ((resolventKernel z w : ℂ) * ((‖μ w + I * ν w‖ ^ 2 : ℝ) : ℂ) * rho w))
      (volume.restrict unitDiscExterior) := hA.add (I3.const_mul I)
  have hcomb : resolventStar (fun u => ((‖μ u + ν u‖ ^ 2 : ℝ) : ℂ)) z -
      resolventStar (fun u => ((‖μ u + (-1) * ν u‖ ^ 2 : ℝ) : ℂ)) z +
      I * resolventStar (fun u => ((‖μ u + I * ν u‖ ^ 2 : ℝ) : ℂ)) z -
      I * resolventStar (fun u => ((‖μ u + (-I) * ν u‖ ^ 2 : ℝ) : ℂ)) z =
      4 * resolventStar (fun u => μ u * conj (ν u)) z := by
    unfold resolventStar resolventOp
    rw [← integral_sub I1 I2, ← integral_const_mul, ← integral_add hA (I3.const_mul I), ← integral_const_mul,
      ← integral_sub hB (I4.const_mul I), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    have h := s5kt_pol_id (μ w) (ν w)
    linear_combination ((resolventKernel z w : ℂ) * (rho w : ℂ)) * h
  linear_combination (-1 / 4 : ℂ) * hcomb

end TakhtajanTeo
