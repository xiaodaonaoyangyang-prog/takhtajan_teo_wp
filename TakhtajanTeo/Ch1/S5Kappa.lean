import TakhtajanTeo.Ch1.S5_ChernForms
import TakhtajanTeo.Ch1.ResolventDuality
import TakhtajanTeo.Ch1.S5VerticalCurvature
import TakhtajanTeo.Ch1.S5KappaTheta

/-!
# `thm_5_10`, `cor_5_11` (`s5k_`, 下属3, Program G): Mumford–Morita–Miller forms at the origin

Host: new module `TakhtajanTeo/Ch1/S5Kappa.lean`. Targets `s5k_thm_5_10`, `s5k_cor_5_11`: byte-identical statements of
`thm_5_10`, `cor_5_11` (S5) with prefixed names (relocated by the leader).

Route. With `G_{kj}(z) = G(μ_k ν̄_j)(z)`:
* Entries of `thetaMatrix` on `𝔻*` (`s5k_theta_*`, = prop_5_7(ii), polarized):
  `Θ(∂_z, ∂_z̄) = -2/(1-|z|²)² = -ρ/2`, `Θ(∂_z, τ̄_ν) = Θ(τ_μ, ∂_z̄) = 0`, `Θ(τ_μ, τ̄_ν) = -G(μν̄)`.
* Block determinant (`s5k_det`): `det = (-ρ/2)·(-1)ⁿ Σ_σ sgn σ ∏_k G_{k σ(k)}`.
* Integrability for `n ≥ 1` (`s5k_prod_integrable`): `G ≥ 0`, mass 1 (`RK4`) and symmetry give
  `|G(μν̄)| ≤ ‖μ‖∞‖ν‖∞` and `G(μν̄) ∈ L¹(ρ)`; harmonic `L²` differentials are bounded.
* Constants: `(-i/2π)^{n+1}(n+1)!(-ρ/2)(-1)ⁿ(-2i) = iⁿ(n+1)!ρ/(2π)^{n+1}`.
* `cor_5_11` is `n = 1` with `∬ G(μν̄) ρ = ⟨μ, ν⟩` (`s5k_resolvent_mass`: symmetry, Fubini, `G(1) = 1`).
* `n = 0`: the single-permutation sum commutes with `∫` without integrability (both sides are the junk `0` of the
  non-integrable `ρ`, which is never needed).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- `Θ_{(0,z)}(∂_z, ∂_z̄) = -2/(1 - |z|²)²` (TT:2398, prop_5_7(ii)). -/
theorem s5k_theta_vert {z : ℂ} (hz : z ∈ unitDiscExterior) :
    thetaForm (fiberPt z) (vertVec z) (vertVec z) = -2 / (1 - ‖z‖ ^ 2) ^ 2 :=
  s5vc_prop_5_7_vertical hz

/-- `Θ_{(0,z)}(∂_z, τ̄_ν) = 0` (TT:2398, prop_5_7(ii)). -/
theorem s5k_theta_vert_hor {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    thetaForm (fiberPt z) (vertVec z) (horVec (toLinf ν) z) = 0 := by
  exact s5kt_theta_vert_hor hν hz

/-- `Θ_{(0,z)}(τ_μ, ∂_z̄) = 0` (TT:2398, prop_5_7(ii)). -/
theorem s5k_theta_hor_vert {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    thetaForm (fiberPt z) (horVec (toLinf μ) z) (vertVec z) = 0 := by
  exact s5kt_theta_hor_vert hμ hz

/-- `Θ_{(0,z)}(τ_μ, τ̄_ν) = -G(μν̄)(z)` (TT:2398, prop_5_7(ii) polarized). -/
theorem s5k_theta_hor_hor {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    thetaForm (fiberPt z) (horVec (toLinf μ) z) (horVec (toLinf ν) z) =
      -resolventStar (fun u => μ u * conj (ν u)) z := by
  exact s5kt_theta_hor_hor hμ hν hz

/-- Harmonic `L²` differentials give bounded products `μν̄` on `𝔻*`. -/
theorem s5k_psi_bound {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ∃ C : ℝ, ∀ w ∈ unitDiscExterior, ‖μ w * conj (ν w)‖ ≤ C :=
  ⟨(Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior μ).toReal *
      ((Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior ν).toReal), fun w hw => by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (wp_harmonic_pointwise_bound hμ hw) (wp_harmonic_pointwise_bound hν hw) (norm_nonneg _)
      (le_trans (norm_nonneg _) (wp_harmonic_pointwise_bound hμ hw))⟩

/-- `μν̄` is a.e.-strongly measurable on `𝔻*`. -/
theorem s5k_psi_aesm {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    AEStronglyMeasurable (fun u => μ u * conj (ν u)) (volume.restrict unitDiscExterior) :=
  ((wp_harmonic_continuousOn hμ).mul (Complex.continuous_conj.comp_continuousOn
    (wp_harmonic_continuousOn hν))).aestronglyMeasurable wp_exterior_isOpen.measurableSet

/-- `|G(μν̄)| ≤ C` on `𝔻*` (`G ≥ 0`, mass `1`). -/
theorem s5k_res_bound {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ∃ C : ℝ, ∀ z ∈ unitDiscExterior, ‖resolventStar (fun u => μ u * conj (ν u)) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := s5k_psi_bound hμ hν
  refine ⟨C, fun z hz => (norm_integral_le_integral_norm _).trans ?_⟩
  exact resolvent_integral_norm_le (Or.inr rfl) (s5k_psi_aesm hμ hν) hC hz

/-- `G(μν̄) ρ ∈ L¹(𝔻*)`: Fubini against `G(1) = 1`. -/
theorem s5k_res_integrable {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    IntegrableOn (fun z => resolventStar (fun u => μ u * conj (ν u)) z * rho z) unitDiscExterior := by
  have h := (resolvent_bilinear_integrable (Or.inr rfl) (f := fun _ => (1 : ℂ))
    aestronglyMeasurable_const (s5k_psi_aesm hμ hν) (C := 1) (fun _ _ => by simp)
    (wpInner_integrable hμ hν)).integral_prod_right
  refine h.congr (Eventually.of_forall fun y => ?_)
  have he : (fun x : ℂ => ((resolventKernel x y : ℂ) * 1 * rho y) * (μ x * conj (ν x) * (rho x : ℂ))) =
      fun x => (resolventKernel y x : ℂ) * (μ x * conj (ν x)) * rho x * (rho y : ℂ) := by
    funext x
    rw [resolventKernel_symm x y]
    ring
  simp only [he, integral_mul_const]
  rfl

/-- The block determinant of `thetaMatrix` on `𝔻*`. -/
theorem s5k_det (n : ℕ) {μs νs : Fin n → ℂ → ℂ} (hμ : ∀ k, μs k ∈ harmonicL2 unitDiscExterior)
    (hν : ∀ k, νs k ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (thetaMatrix n (fun k => toLinf (μs k)) (fun k => toLinf (νs k)) z).det =
      -(rho z : ℂ) / 2 * (-1) ^ n * ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
        ∏ k, resolventStar (fun u => μs k u * conj (νs (σ k) u)) z := by
  set A := thetaMatrix n (fun k => toLinf (μs k)) (fun k => toLinf (νs k)) z with hA
  have h0 : ∀ j : Fin n, A 0 j.succ = 0 := fun j => by
    simp only [hA, thetaMatrix, Fin.cases_zero, Fin.cases_succ]
    exact s5k_theta_vert_hor (hν j) hz
  have h00 : A 0 0 = -2 / (1 - ‖z‖ ^ 2) ^ 2 := by
    simp only [hA, thetaMatrix, Fin.cases_zero]
    exact s5k_theta_vert hz
  have hsub : A.submatrix Fin.succ (Fin.succAbove 0) =
      -Matrix.of fun i j => resolventStar (fun u => μs i u * conj (νs j u)) z := by
    ext i j
    simp only [hA, Matrix.submatrix_apply, Fin.succAbove_zero, thetaMatrix, Fin.cases_succ,
      Matrix.neg_apply, Matrix.of_apply]
    exact s5k_theta_hor_hor (hμ i) (hν j) hz
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  rw [hsub, Matrix.det_neg, ← Matrix.det_transpose, Matrix.det_apply', h00, Fintype.card_fin]
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  unfold rho
  push_cast
  ring

/-- For `n ≥ 1` the products `∏_k G(μ_k ν̄_{σ(k)}) ρ` are integrable on `𝔻*`. -/
theorem s5k_prod_integrable {n : ℕ} (hn : 0 < n) {μs νs : Fin n → ℂ → ℂ}
    (hμ : ∀ k, μs k ∈ harmonicL2 unitDiscExterior) (hν : ∀ k, νs k ∈ harmonicL2 unitDiscExterior)
    (σ : Equiv.Perm (Fin n)) :
    IntegrableOn (fun z => (∏ k, resolventStar (fun u => μs k u * conj (νs (σ k) u)) z) * rho z)
      unitDiscExterior := by
  set B : Fin n → ℂ → ℂ := fun k z => resolventStar (fun u => μs k u * conj (νs (σ k) u)) z with hB
  let k0 : Fin n := ⟨0, hn⟩
  choose C hC using fun k => s5k_res_bound (hμ k) (hν (σ k))
  have hint : ∀ k, IntegrableOn (fun z => B k z * rho z) unitDiscExterior := fun k =>
    s5k_res_integrable (hμ k) (hν (σ k))
  have hm : ∀ k, AEStronglyMeasurable (B k) (volume.restrict unitDiscExterior) := fun k => by
    have hmr : AEStronglyMeasurable (fun z => ((rho z : ℂ))⁻¹) (volume.restrict unitDiscExterior) :=
      (by unfold rho; fun_prop : Measurable fun z => ((rho z : ℂ))⁻¹).aestronglyMeasurable
    refine ((hint k).aestronglyMeasurable.mul hmr).congr ?_
    filter_upwards [ae_restrict_mem wp_exterior_isOpen.measurableSet] with z hz
    have hr : (rho z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (wp_rho_pos hz).ne'
    show B k z * (rho z : ℂ) * ((rho z : ℂ))⁻¹ = B k z
    rw [mul_assoc, mul_inv_cancel₀ hr, mul_one]
  have hbd : ∀ᵐ z ∂volume.restrict unitDiscExterior,
      ‖∏ k ∈ Finset.univ.erase k0, B k z‖ ≤ ∏ k ∈ Finset.univ.erase k0, C k := by
    filter_upwards [ae_restrict_mem wp_exterior_isOpen.measurableSet] with z hz
    exact (Finset.norm_prod_le _ _).trans
      (Finset.prod_le_prod₀ (h0 := fun _ _ => norm_nonneg _) (h1 := fun k _ => hC k z hz))
  have h := (hint k0).bdd_mul (Finset.aestronglyMeasurable_fun_prod _ fun k _ => hm k) hbd
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k0)]
  ring

/-- `∬_{𝔻*} G(μν̄) ρ d²z = ⟨μ, ν⟩_WP` (`G(1) = 1`). -/
theorem s5k_resolvent_mass {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ∫ z in unitDiscExterior, resolventStar (fun u => μ u * conj (ν u)) z * rho z = wpInner μ ν := by
  have hs := resolvent_bilinear_swap (Or.inr rfl) (f := fun _ => (1 : ℂ))
    aestronglyMeasurable_const (s5k_psi_aesm hμ hν) (C := 1) (fun _ _ => by simp)
    (wpInner_integrable hμ hν)
  have h1 : ∀ z ∈ unitDiscExterior, resolventOp unitDiscExterior (fun _ => (1 : ℂ)) z = 1 := by
    intro z hz
    unfold resolventOp
    simp only [mul_one]
    have h := integral_ofReal (𝕜 := ℂ) (μ := volume.restrict unitDiscExterior)
      (f := fun w => resolventKernel z w * rho w)
    push_cast at h
    exact h.trans (by rw [RK4 (Or.inr rfl) hz]; simp)
  unfold resolventStar wpInner
  calc
    _ = ∫ w in unitDiscExterior, 1 * resolventOp unitDiscExterior (fun u => μ u * conj (ν u)) w * rho w := by
      simp only [one_mul]
    _ = ∫ z in unitDiscExterior, resolventOp unitDiscExterior (fun _ => (1 : ℂ)) z * (μ z * conj (ν z)) *
        rho z := hs.symm
    _ = _ := by
      refine setIntegral_congr_fun wp_exterior_isOpen.measurableSet fun z hz => ?_
      simp only [h1 z hz, one_mul, mul_assoc]

/-- **Theorem 5.10** (TT:2504–2522). For `μ_k, ν_k ∈ H^{-1,1}(𝔻*) ≅ T₀T(1)`:
`κ_n(μ₁, …, μ_n, ν̄₁, …, ν̄_n) = (iⁿ (n+1)!/(2π)^{n+1}) Σ_{σ ∈ S_n} sgn(σ) ∬_{𝔻*} G(μ₁ν̄_{σ(1)}) ⋯ G(μ_nν̄_{σ(n)}) ρ d²z`
(the integrals converge; `G(f) = resolventStar f`). -/
theorem s5k_thm_5_10 (n : ℕ) {μs νs : Fin n → ℂ → ℂ} (hμ : ∀ k, μs k ∈ harmonicL2 unitDiscExterior)
    (hν : ∀ k, νs k ∈ harmonicL2 unitDiscExterior) :
    kappaOrigin n (fun k => toLinf (μs k)) (fun k => toLinf (νs k)) =
      I ^ n * ((Nat.factorial (n + 1) : ℕ) : ℂ) / (2 * π) ^ (n + 1) *
        ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
          ∫ z in unitDiscExterior, (∏ k, resolventStar (fun u => μs k u * conj (νs (σ k) u)) z) * rho z := by
  set P : Equiv.Perm (Fin n) → ℂ → ℂ := fun σ z =>
    (∏ k, resolventStar (fun u => μs k u * conj (νs (σ k) u)) z) * rho z with hP
  have hint : (∫ z in unitDiscExterior, ((Nat.factorial (n + 1) : ℕ) : ℂ) *
        (thetaMatrix n (fun k => toLinf (μs k)) (fun k => toLinf (νs k)) z).det * (-2 * I)) =
      ∫ z in unitDiscExterior, ((Nat.factorial (n + 1) : ℕ) : ℂ) * (-1) ^ n * I *
        ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * P σ z := by
    refine setIntegral_congr_fun resolvent_exterior_isOpen.measurableSet fun z hz => ?_
    rw [s5k_det n hμ hν hz]
    have hS : ∀ S : ℂ, ((Nat.factorial (n + 1) : ℕ) : ℂ) * (-(rho z : ℂ) / 2 * (-1) ^ n * S) * (-2 * I) =
        ((Nat.factorial (n + 1) : ℕ) : ℂ) * (-1) ^ n * I * ((rho z : ℂ) * S) := fun S => by ring
    rw [hS, Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun σ _ => ?_)
    simp only [hP]
    ring
  have hswap : (∫ z in unitDiscExterior, ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * P σ z) =
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * ∫ z in unitDiscExterior, P σ z := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [integral_finsetSum _ fun σ _ => (s5k_prod_integrable hn hμ hν σ).const_mul _]
      simp_rw [integral_const_mul]
      rfl
  unfold kappaOrigin
  rw [hint, integral_const_mul, hswap]
  have hc : (-I / (2 * π)) ^ (n + 1) * (((Nat.factorial (n + 1) : ℕ) : ℂ) * (-1) ^ n * I) =
      I ^ n * ((Nat.factorial (n + 1) : ℕ) : ℂ) / (2 * π) ^ (n + 1) := by
    have h1 : ((-1 : ℂ)) ^ (n + 1) * (-1) ^ n = -1 := by
      rw [← pow_add]; exact Odd.neg_one_pow ⟨n, by ring⟩
    have h2 : I ^ (n + 1) * I = -I ^ n := by
      rw [pow_succ, mul_assoc, I_mul_I]; ring
    rw [div_pow, neg_pow]
    calc (-1) ^ (n + 1) * I ^ (n + 1) / (2 * (π : ℂ)) ^ (n + 1) *
          (((Nat.factorial (n + 1) : ℕ) : ℂ) * (-1) ^ n * I) =
        ((-1) ^ (n + 1) * (-1) ^ n) * (I ^ (n + 1) * I) * ((Nat.factorial (n + 1) : ℕ) : ℂ) /
          (2 * (π : ℂ)) ^ (n + 1) := by ring
      _ = _ := by rw [h1, h2]; ring
  rw [← hc]
  ring

/-- **Corollary 5.11** (TT:2524–2542). On the Hilbert manifold `T(1)` (at the origin): `κ₁ = (1/π²) ω_WP`. -/
theorem s5k_cor_5_11 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    kappaOrigin 1 (fun _ => toLinf μ) (fun _ => toLinf ν) = 1 / π ^ 2 * omegaWPOrigin μ ν := by
  have h := s5k_thm_5_10 1 (μs := fun _ => μ) (νs := fun _ => ν) (fun _ => hμ) (fun _ => hν)
  rw [h, Fintype.sum_unique, show (default : Equiv.Perm (Fin 1)) = 1 from Subsingleton.elim _ _]
  simp_rw [Fin.prod_univ_one]
  rw [s5k_resolvent_mass hμ hν]
  unfold omegaWPOrigin
  simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, pow_one, Nat.factorial]
  push_cast
  field_simp

/-- **Theorem 5.10** (TT:2504–2522). For `μ_k, ν_k ∈ H^{-1,1}(𝔻*) ≅ T₀T(1)`:
`κ_n(μ₁, …, μ_n, ν̄₁, …, ν̄_n) = (iⁿ (n+1)!/(2π)^{n+1}) Σ_{σ ∈ S_n} sgn(σ) ∬_{𝔻*} G(μ₁ν̄_{σ(1)}) ⋯ G(μ_nν̄_{σ(n)}) ρ d²z`
(the integrals converge; `G(f) = resolventStar f`). -/
theorem thm_5_10 (n : ℕ) {μs νs : Fin n → ℂ → ℂ} (hμ : ∀ k, μs k ∈ harmonicL2 unitDiscExterior)
    (hν : ∀ k, νs k ∈ harmonicL2 unitDiscExterior) :
    kappaOrigin n (fun k => toLinf (μs k)) (fun k => toLinf (νs k)) =
      I ^ n * ((Nat.factorial (n + 1) : ℕ) : ℂ) / (2 * π) ^ (n + 1) *
        ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
          ∫ z in unitDiscExterior, (∏ k, resolventStar (fun u => μs k u * conj (νs (σ k) u)) z) * rho z := by
  exact s5k_thm_5_10 n hμ hν

/-- **Corollary 5.11** (TT:2524–2542). On the Hilbert manifold `T(1)` (at the origin): `κ₁ = (1/π²) ω_WP`. -/
theorem cor_5_11 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    kappaOrigin 1 (fun _ => toLinf μ) (fun _ => toLinf ν) = 1 / π ^ 2 * omegaWPOrigin μ ν := by
  exact s5k_cor_5_11 hμ hν

end TakhtajanTeo
