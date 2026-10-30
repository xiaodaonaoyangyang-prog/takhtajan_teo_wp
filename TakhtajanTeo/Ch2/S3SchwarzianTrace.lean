import TakhtajanTeo.Ch2.S3FredholmTraceCancellation
import TakhtajanTeo.Ch2.S3Var_Completed

/-! # Grunsky resolvent cancellation and the exterior Schwarzian trace

The actual variation-kernel / operator-trace identification is developed
separately from the already verified Fredholm differentiation.
-/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- A unit mixed block cancels its Gram resolvent on both sides. -/
theorem s3st_gram_resolvent (B : ell2 →L[ℂ] ell2) (hB : IsUnit B) :
    star B*Ring.inverse (B*star B)*B = 1 := by
  rw [Ring.inverse_mul (Or.inl hB),← mul_assoc,
    Ring.mul_inverse_cancel (star B) (isUnit_star.mpr hB),one_mul,
    Ring.inverse_mul_cancel B hB]

/-- The off-diagonal Grunsky identity eliminates the Fredholm resolvent. -/
theorem s3st_block_resolvent (A B C E : ell2 →L[ℂ] ell2)
    (hB : IsUnit B) (hgram : A*star A+B*star B=1)
    (hcross : C*star A+E*star B=0) :
    C*star A*Ring.inverse (1-A*star A)*B = -E := by
  have hg : 1-A*star A=B*star B := (eq_sub_of_add_eq' hgram).symm
  have hc : C*star A=-(E*star B) := eq_neg_of_add_eq_zero_left hcross
  rw [hg,hc]
  have he : E*star B*Ring.inverse (B*star B)*B = E := by
    calc
      E*star B*Ring.inverse (B*star B)*B = E*(star B*Ring.inverse (B*star B)*B) := by simp only [mul_assoc]
      _ = E := by rw [s3st_gram_resolvent B hB,mul_one]
  simpa only [neg_mul] using! congrArg Neg.neg he

/-- The precise resolvent identity for the actual four Grunsky blocks. -/
theorem s3st_grunsky_resolvent {ν : LinfStar} (hν : ν ∈ LinfStarBall) :
    let b := grunsky (fsans ν) (gsans ν)
    gopOp (B3 b)*star (gopOp (B1 b))*
        Ring.inverse (1-gopOp (B1 b)*star (gopOp (B1 b)))*gopOp (B2 b) = -gopOp (B4 b) := by
  intro b
  obtain ⟨h1,h2,h3,h4,h5,h6,hs⟩ :=
    gop_blocks (AppB.b8_welding_normalized_pair hν) (r22_complement_null hν)
  apply s3st_block_resolvent _ _ _ _ (pgb_mixed_isUnit hν).1 h1
  have hc := congrArg (fun T : ell2 →L[ℂ] ell2 => ContinuousLinearMap.adjoint T) h3
  change ContinuousLinearMap.adjoint
    ((gopOp (B1 b)).comp (ContinuousLinearMap.adjoint (gopOp (B3 b))) +
      (gopOp (B2 b)).comp (ContinuousLinearMap.adjoint (gopOp (B4 b)))) =
      ContinuousLinearMap.adjoint (0 : ell2 →L[ℂ] ell2) at hc
  simp only [map_add,map_zero,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint] at hc
  change gopOp (B3 b)*ContinuousLinearMap.adjoint (gopOp (B1 b)) +
    gopOp (B4 b)*ContinuousLinearMap.adjoint (gopOp (B2 b)) = 0
  exact hc

theorem s3st_weighted_pair_bound (x y : ℝ) {r : ℝ} (hr : 0 < r) :
    x*y ≤ x^2*r⁻¹+y^2*r := by
  calc
    x*y ≤ (x^2+y^2*r^2)/r := (le_div_iff₀ hr).mpr (by nlinarith [sq_nonneg (x-y*r)])
    _ = x^2*r⁻¹+y^2*r := by field_simp

/-- Absolute integrability of the quadratic-differential/harmonic pairing,
deduced from the two actual weighted L2 bounds. -/
theorem s3st_pair_integrable {φ μ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDiscExterior)
    (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    IntegrableOn (fun z => φ z*μ z) unitDiscExterior := by
  have hi := (A2fun.integrable_weighted_sq wp_exterior_isOpen hφ).add (wp_integrable_sq hμ)
  apply hi.mono' ((hφ.1.continuousOn.mul (wp_harmonic_continuousOn hμ)).aestronglyMeasurable
    wp_exterior_isOpen.measurableSet)
  filter_upwards [ae_restrict_mem wp_exterior_isOpen.measurableSet] with z hz
  change ‖φ z*μ z‖ ≤ ‖φ z‖^2*(rho z)⁻¹+‖μ z‖^2*rho z
  rw [norm_mul]
  exact s3st_weighted_pair_bound ‖φ z‖ ‖μ z‖ (wp_rho_pos hz)

/-- The original exterior Schwarzian pairing is genuinely absolutely integrable. -/
theorem s3st_schwarzian_integrable {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    IntegrableOn (fun z => schwarzianHol (gsans ν) z*μ z) unitDiscExterior := by
  have hv := vartheta_spec (Phi ⟨ν,hν⟩)
  have hi := s3st_pair_integrable (hv.1.mp hνT) hμ
  apply hi.congr_fun _ wp_exterior_isOpen.measurableSet
  intro z hz
  change vartheta (Phi ⟨ν,hν⟩) z*μ z = schwarzianHol (gsans ν) z*μ z
  rw [← hv.2 ⟨ν,hν⟩ rfl hz]

/-- The installed removable K4 diagonal and its actual area pairing,
with absolute integrability established rather than assumed. -/
theorem s3st_K4_diagonal_pair {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    IntegrableOn (fun z => kerK4 (gsans ν) z z*μ z) unitDiscExterior ∧
      (∫ z in unitDiscExterior, kerK4 (gsans ν) z z*μ z) =
        -(1/(6*π))*∫ z in unitDiscExterior, schwarzianHol (gsans ν) z*μ z := by
  have he (z : ℂ) : kerK4 (gsans ν) z z*μ z =
      -(1/(6*π))*(schwarzianHol (gsans ν) z*μ z) := by rw [kerK4_diag]; ring
  simp_rw [he]
  exact ⟨(s3st_schwarzian_integrable hν hνT hμ).const_mul _,integral_const_mul _ _⟩

theorem s3st_basisF_sq {z : ℂ} (hz : z ∈ unitDiscExterior) :
    Summable (fun n => ‖basisF n z‖^2) := by
  have h := Complex.reCLM.summable (e24_sumF hz hz).summable
  simpa only [Complex.reCLM_apply,Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq] using h

/-- The genuine exterior Bergman evaluation vector, on its valid domain. -/
def s3st_vector (z : ℂ) : ell2 :=
  if hz : z ∈ unitDiscExterior then ⟨fun n => basisF n z,gop_mem_of_summable (s3st_basisF_sq hz)⟩ else 0

theorem s3st_vector_apply {z : ℂ} (hz : z ∈ unitDiscExterior) (n : ℕ) :
    s3st_vector z n = basisF n z := by simp only [s3st_vector,dif_pos hz]

/-- The holomorphic two-variable kernel of an actual bounded operator in the exterior basis. -/
def s3st_kernel (T : ell2 →L[ℂ] ell2) (z w : ℂ) : ℂ :=
  inner ℂ (star (s3st_vector z)) (T (s3st_vector w))

theorem s3st_kernel_series (T : ell2 →L[ℂ] ell2) {z : ℂ}
    (hz : z ∈ unitDiscExterior) (w : ℂ) :
    s3st_kernel T z w = ∑' n, (T (s3st_vector w)) n*basisF n z := by
  rw [s3st_kernel,lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [gop_inner_apply]
  change conj (conj (s3st_vector z n))*(T (s3st_vector w)) n = _
  rw [Complex.conj_conj,s3st_vector_apply hz,mul_comm]

theorem s3st_kernel_holomorphic (T : ell2 →L[ℂ] ell2) (w : ℂ) :
    DifferentiableOn ℂ (fun z => s3st_kernel T z w) unitDiscExterior := by
  have h := (e212_ext_series (gop_l2_summable (T (s3st_vector w)))).1
  exact h.congr (fun z hz => s3st_kernel_series T hz w)

/-- The actual B4 operator kernel equals the installed Grunsky kernel off its diagonal. -/
theorem s3st_B4_kernel_off {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z w : ℂ}
    (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior) (hzw : z ≠ w) :
    s3st_kernel (gopOp (B4 (grunsky (fsans ν) (gsans ν)))) z w = kerK4 (gsans ν) z w := by
  let B := B4 (grunsky (fsans ν) (gsans ν))
  have hB : IsBoundedMat B := pgb_bounded hν (by simp [B])
  have hs := e24_hK4 (AppB.b8_welding_normalized_pair hν) (r22_complement_null hν) z hz w hw hzw
  rw [s3st_kernel_series _ hz w,← hs.tsum_eq,hs.summable.tsum_prod]
  apply tsum_congr
  intro m
  rw [pmb_apply hB]
  change (∑' n, B m n*s3st_vector w n)*basisF m z = _
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  rw [s3st_vector_apply hw]
  ring

/-- Continuity across the removable diagonal identifies the full B4 kernel,
including the diagonal used in the trace integral. -/
theorem s3st_B4_kernel {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z w : ℂ}
    (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior) :
    s3st_kernel (gopOp (B4 (grunsky (fsans ν) (gsans ν)))) z w = kerK4 (gsans ν) z w := by
  by_cases hzw : z ≠ w
  · exact s3st_B4_kernel_off hν hz hw hzw
  have he : z = w := not_ne_iff.mp hzw
  subst z
  have hK := (s3st_kernel_holomorphic (gopOp (B4 (grunsky (fsans ν) (gsans ν)))) w).continuousOn
    |>.continuousAt (wp_exterior_isOpen.mem_nhds hw)
  have hpair := AppB.b8_welding_normalized_pair hν
  have hg : DifferentiableOn ℂ (gsans ν) unitDiscExterior := hpair.2.2.2.2.1.1
  have hgi : InjOn (gsans ν) unitDiscExterior := hpair.2.2.2.2.1.2.1
  have hG : ContinuousAt (fun z => kerK4 (gsans ν) z w) w :=
    (AppB.differentiableOn_kerK1 wp_exterior_isOpen hg hgi hw).continuousOn.continuousAt
      (wp_exterior_isOpen.mem_nhds hw)
  have hlim := hG.tendsto.mono_left (nhdsWithin_le_nhds (s := {w}ᶜ))
  have heq : (fun z => s3st_kernel (gopOp (B4 (grunsky (fsans ν) (gsans ν)))) z w) =ᶠ[𝓝[≠] w]
      (fun z => kerK4 (gsans ν) z w) := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (wp_exterior_isOpen.mem_nhds hw)] with z hzw hz
    exact s3st_B4_kernel_off hν hz hw hzw
  exact tendsto_nhds_unique (hK.tendsto.mono_left nhdsWithin_le_nhds) (hlim.congr' heq.symm)

/-- The exact bounded operator appearing after the mixed-kernel contraction. -/
def s3st_resolventOperator (ν : LinfStar) : ell2 →L[ℂ] ell2 :=
  let b := grunsky (fsans ν) (gsans ν)
  gopOp (B3 b)*star (gopOp (B1 b))*
    Ring.inverse (1-gopOp (B1 b)*star (gopOp (B1 b)))*gopOp (B2 b)

theorem s3st_resolvent_kernel {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z w : ℂ}
    (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior) :
    s3st_kernel (s3st_resolventOperator ν) z w = -kerK4 (gsans ν) z w := by
  have ho : s3st_resolventOperator ν = -gopOp (B4 (grunsky (fsans ν) (gsans ν))) :=
    s3st_grunsky_resolvent hν
  rw [ho,s3st_kernel,neg_apply,inner_neg_right]
  exact congrArg Neg.neg (s3st_B4_kernel hν hz hw)

theorem s3st_resolvent_diagonal {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    s3st_kernel (s3st_resolventOperator ν) z z = schwarzianHol (gsans ν) z/(6*π) := by
  rw [s3st_resolvent_kernel hν hz hz,kerK4_diag,neg_div,neg_neg]

/-- The actual resolvent contraction kernel has an absolutely integrable
diagonal pairing, with the exact Schwarzian normalization. -/
theorem s3st_resolvent_diagonal_integral {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    IntegrableOn (fun z => s3st_kernel (s3st_resolventOperator ν) z z*μ z) unitDiscExterior ∧
      (∫ z in unitDiscExterior, s3st_kernel (s3st_resolventOperator ν) z z*μ z) =
        (1/(6*π))*∫ z in unitDiscExterior, schwarzianHol (gsans ν) z*μ z := by
  have he : EqOn (fun z => s3st_kernel (s3st_resolventOperator ν) z z*μ z)
      (fun z => (1/(6*π))*(schwarzianHol (gsans ν) z*μ z)) unitDiscExterior := by
    intro z hz
    dsimp only
    rw [s3st_resolvent_diagonal hν hz]
    ring
  have hi : IntegrableOn (fun z => (1/(6*π) : ℂ)*(schwarzianHol (gsans ν) z*μ z))
      unitDiscExterior := (s3st_schwarzian_integrable hν hνT hμ).const_mul _
  refine ⟨hi.congr_fun he.symm wp_exterior_isOpen.measurableSet,?_⟩
  rw [setIntegral_congr_fun wp_exterior_isOpen.measurableSet he,integral_const_mul]

end Ch2
end TakhtajanTeo
