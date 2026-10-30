import TakhtajanTeo.Ch1.S4_Metrics

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The disk coordinate centered at an upper-half-plane point in (6.3) (TT:2613). -/
def wp_centeredCayley (z u : ℂ) : ℂ := (u - z) / (u - conj z)

/-- The inverse of the centered coordinate used in (6.3) (TT:2613). -/
def wp_centeredCayleyInv (z v : ℂ) : ℂ := (z - conj z * v) / (1 - v)

/-- An upper-half-plane point cannot equal the conjugate of another (TT:2613). -/
theorem wp_upperHalf_sub_conj_ne {u z : ℂ} (hu : u ∈ upperHalf) (hz : z ∈ upperHalf) :
    u - conj z ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at hi
  have hu0 : 0 < u.im := hu
  have hz0 : 0 < z.im := hz
  linarith

/-- Difference of squared distances from a point and its reflection (TT:2613). -/
theorem wp_upperHalf_norm_difference (u z : ℂ) :
    ‖u - conj z‖ ^ 2 - ‖u - z‖ ^ 2 = 4 * u.im * z.im := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The centered Cayley coordinate takes the upper half-plane into the disk (TT:2613). -/
theorem wp_centeredCayley_mem {u z : ℂ} (hu : u ∈ upperHalf) (hz : z ∈ upperHalf) :
    wp_centeredCayley z u ∈ unitDisc := by
  apply mem_ball_zero_iff.mpr
  rw [wp_centeredCayley, norm_div, div_lt_one (norm_pos_iff.mpr (wp_upperHalf_sub_conj_ne hu hz))]
  have h := wp_upperHalf_norm_difference u z
  have hu0 : 0 < u.im := hu
  have hz0 : 0 < z.im := hz
  nlinarith [mul_pos hu0 hz0, norm_nonneg (u - z), norm_nonneg (u - conj z)]

/-- The disk-boundary factor for the centered coordinate (TT:2613). -/
theorem wp_centeredCayley_boundary {u z : ℂ} (hu : u ∈ upperHalf) (hz : z ∈ upperHalf) :
    1 - ‖wp_centeredCayley z u‖ ^ 2 = 4 * u.im * z.im / ‖u - conj z‖ ^ 2 := by
  have hd : ‖u - conj z‖ ≠ 0 := norm_ne_zero_iff.mpr (wp_upperHalf_sub_conj_ne hu hz)
  rw [wp_centeredCayley, norm_div, div_pow]
  apply (eq_div_iff (pow_ne_zero 2 hd)).mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hd)]
  exact wp_upperHalf_norm_difference u z

/-- A disk point does not make the inverse-coordinate denominator vanish (TT:2613). -/
theorem wp_centeredCayleyInv_den {v : ℂ} (hv : v ∈ unitDisc) : 1 - v ≠ 0 := by
  intro h
  have he : v = 1 := by linear_combination -h
  have hn := mem_ball_zero_iff.mp hv
  simp [he] at hn

/-- Imaginary part of the inverse centered coordinate (TT:2613). -/
theorem wp_centeredCayleyInv_im (z v : ℂ) :
    (wp_centeredCayleyInv z v).im = z.im * (1 - ‖v‖ ^ 2) / ‖1 - v‖ ^ 2 := by
  simp only [wp_centeredCayleyInv, Complex.div_im, ← Complex.normSq_eq_norm_sq]
  congr 1
  simp only [Complex.sub_im, Complex.sub_re, Complex.mul_im, Complex.mul_re,
    Complex.conj_im, Complex.conj_re, Complex.one_re, Complex.one_im, Complex.normSq_apply]
  ring

/-- The inverse centered coordinate takes the disk into the upper half-plane (TT:2613). -/
theorem wp_centeredCayleyInv_mem {z v : ℂ} (hz : z ∈ upperHalf) (hv : v ∈ unitDisc) :
    wp_centeredCayleyInv z v ∈ upperHalf := by
  change 0 < (wp_centeredCayleyInv z v).im
  rw [wp_centeredCayleyInv_im]
  have hn := mem_ball_zero_iff.mp hv
  have hp : 0 < 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  exact div_pos (mul_pos hz hp) (sq_pos_of_pos (norm_pos_iff.mpr (wp_centeredCayleyInv_den hv)))

/-- The inverse centered coordinate is a left inverse on the upper half-plane (TT:2613). -/
theorem wp_centeredCayley_left_inv {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    wp_centeredCayleyInv z (wp_centeredCayley z u) = u := by
  have hd := wp_upperHalf_sub_conj_ne hu hz
  have hz0 := wp_upperHalf_sub_conj_ne hz hz
  unfold wp_centeredCayleyInv wp_centeredCayley
  field_simp [hd, hz0]
  <;> ring

/-- The inverse centered coordinate is a right inverse on the disk (TT:2613). -/
theorem wp_centeredCayley_right_inv {z v : ℂ} (hz : z ∈ upperHalf) (hv : v ∈ unitDisc) :
    wp_centeredCayley z (wp_centeredCayleyInv z v) = v := by
  have hd := wp_centeredCayleyInv_den hv
  have hz0 := wp_upperHalf_sub_conj_ne hz hz
  have hden : wp_centeredCayleyInv z v - conj z = (z - conj z) / (1 - v) := by
    unfold wp_centeredCayleyInv
    field_simp [hd]
    <;> ring
  have hnum : wp_centeredCayleyInv z v - z = (z - conj z) * v / (1 - v) := by
    unfold wp_centeredCayleyInv
    field_simp [hd]
    <;> ring
  rw [wp_centeredCayley, hnum, hden, div_div_div_cancel_right₀ hd]
  exact mul_div_cancel_left₀ v hz0

/-- The derivative of the centered coordinate, needed for the cutoff integral (TT:2613). -/
theorem wp_centeredCayley_hasDerivAt {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    HasDerivAt (wp_centeredCayley z) ((z - conj z) / (u - conj z) ^ 2) u := by
  have h := ((hasDerivAt_id u).sub_const z).div ((hasDerivAt_id u).sub_const (conj z))
    (wp_upperHalf_sub_conj_ne hu hz)
  convert h using 1
  · rfl
  · simp only [id_eq]
    ring

/-- The derivative of the inverse centered coordinate (TT:2613). -/
theorem wp_centeredCayleyInv_hasDerivAt {z v : ℂ} (hz : z ∈ upperHalf) (hv : v ∈ unitDisc) :
    HasDerivAt (wp_centeredCayleyInv z) ((z - conj z) / (1 - v) ^ 2) v := by
  have h := ((hasDerivAt_const v z).sub ((hasDerivAt_id v).const_mul (conj z))).div
    ((hasDerivAt_const v (1 : ℂ)).sub (hasDerivAt_id v)) (wp_centeredCayleyInv_den hv)
  convert h using 1
  · rfl
  · simp only [id_eq, Pi.sub_apply]
    ring


/-- The centered coordinate is a conformal bijection onto the disk (TT:2613). -/
theorem wp_centeredCayley_conformal {z : ℂ} (hz : z ∈ upperHalf) :
    IsConformalOnto (wp_centeredCayley z) upperHalf unitDisc := by
  refine ⟨fun u hu => (wp_centeredCayley_hasDerivAt hz hu).differentiableAt.differentiableWithinAt,
    ?_, ?_⟩
  · intro u hu v hv he
    have h := congrArg (wp_centeredCayleyInv z) he
    simpa only [wp_centeredCayley_left_inv hz hu, wp_centeredCayley_left_inv hz hv] using h
  · apply Subset.antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact wp_centeredCayley_mem hu hz
    · intro v hv
      exact ⟨wp_centeredCayleyInv z v, wp_centeredCayleyInv_mem hz hv,
        wp_centeredCayley_right_inv hz hv⟩

/-- Complement of the centered coordinate (TT:2613). -/
theorem wp_centeredCayley_one_sub {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    1 - wp_centeredCayley z u = (z - conj z) / (u - conj z) := by
  unfold wp_centeredCayley
  field_simp [wp_upperHalf_sub_conj_ne hu hz]
  <;> ring

/-- Quadratic-differential pullback to a disk centered at z (TT:2613). -/
def wp_halfPlaneQuadratic (z : ℂ) (φ : ℂ → ℂ) (v : ℂ) : ℂ :=
  φ (wp_centeredCayleyInv z v) * ((z - conj z) / (1 - v) ^ 2) ^ 2

/-- The centered quadratic pullback is holomorphic (TT:2613). -/
theorem wp_halfPlaneQuadratic_differentiable {z : ℂ} (hz : z ∈ upperHalf) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ upperHalf) :
    DifferentiableOn ℂ (wp_halfPlaneQuadratic z φ) unitDisc := by
  intro v hv
  have hopen : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hF := (wp_centeredCayleyInv_hasDerivAt hz hv).differentiableAt
  have hφv := hφ.differentiableAt (hopen.mem_nhds (wp_centeredCayleyInv_mem hz hv))
  have hd := wp_centeredCayleyInv_den hv
  have hd2 := pow_ne_zero 2 hd
  have hfactor : DifferentiableAt ℂ (fun v : ℂ => ((z - conj z) / (1 - v) ^ 2) ^ 2) v := by
    fun_prop
  exact ((hφv.comp v hF).mul hfactor).differentiableWithinAt

/-- Pointwise expression of the quadratic pullback in the original coordinate (TT:2613). -/
theorem wp_halfPlaneQuadratic_at {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf)
    (φ : ℂ → ℂ) :
    wp_halfPlaneQuadratic z φ (wp_centeredCayley z u) =
      φ u * (u - conj z) ^ 4 / (z - conj z) ^ 2 := by
  rw [wp_halfPlaneQuadratic, wp_centeredCayley_left_inv hz hu, wp_centeredCayley_one_sub hz hu]
  field_simp [wp_upperHalf_sub_conj_ne hu hz, wp_upperHalf_sub_conj_ne hz hz]
  <;> ring

/-- The weighted boundedness condition survives centered quadratic pullback (TT:2613). -/
theorem wp_halfPlaneQuadratic_bound {z : ℂ} (hz : z ∈ upperHalf) {φ : ℂ → ℂ} {C : ℝ}
    (hC : ∀ u ∈ upperHalf, ‖(u.im ^ 2 : ℝ) * φ u‖ ≤ C) :
    ∀ v ∈ unitDisc, ‖((1 - ‖v‖ ^ 2) ^ 2 : ℝ) * wp_halfPlaneQuadratic z φ v‖ ≤ 4 * C := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := (wp_centeredCayley_conformal hz).2.2.symm ▸ hv
  have hd : ‖u - conj z‖ ≠ 0 := norm_ne_zero_iff.mpr (wp_upperHalf_sub_conj_ne hu hz)
  have hz0 : z.im ≠ 0 := ne_of_gt hz
  have hzpos : 0 < z.im := hz
  have hupos : 0 < u.im := hu
  have hA : ‖z - conj z‖ = 2 * z.im := by
    rw [Complex.sub_conj]
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzpos]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (1 - ‖wp_centeredCayley z u‖ ^ 2)),
    wp_halfPlaneQuadratic_at hz hu, norm_div, norm_mul, norm_pow, norm_pow, hA,
    wp_centeredCayley_boundary hu hz]
  have hh := hC u hu
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg u.im)] at hh
  have halg : (4 * u.im * z.im / ‖u - conj z‖ ^ 2) ^ 2 *
      (‖φ u‖ * ‖u - conj z‖ ^ 4 / (2 * z.im) ^ 2) = 4 * (u.im ^ 2 * ‖φ u‖) := by
    field_simp
    <;> ring
  rw [halg]
  linarith


/-- The singular kernel in (6.3) becomes a radially weighted antiholomorphic disk kernel (TT:2613). -/
theorem wp_centeredCayley_pv_integrand {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf)
    (huz : u ≠ z) (φ : ℂ → ℂ) :
    ‖deriv (wp_centeredCayley z) u‖ ^ 2 •
      ((((1 - ‖wp_centeredCayley z u‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        conj (wp_halfPlaneQuadratic z φ (wp_centeredCayley z u)) / (wp_centeredCayley z u) ^ 2) =
      -2 * (z - conj z) ^ 2 * (((u - conj u) ^ 2 / 2) * conj (φ u)) /
        ((u - z) ^ 2 * (u - conj z) ^ 2) := by
  have hD := wp_upperHalf_sub_conj_ne hu hz
  have hA := wp_upperHalf_sub_conj_ne hz hz
  have hN : ((‖u - conj z‖ : ℝ) : ℂ) ^ 2 = (u - conj z) * conj (u - conj z) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hN4 : ((‖u - conj z‖ : ℝ) : ℂ) ^ 4 = ((u - conj z) * conj (u - conj z)) ^ 2 := by
    rw [← hN]; ring
  have hAZ : ‖z - conj z‖ ^ 2 = 4 * z.im ^ 2 := by
    rw [Complex.sub_conj]
    simp only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    norm_num
  rw [(wp_centeredCayley_hasDerivAt hz hu).deriv, norm_div, norm_pow, div_pow, hAZ,
    wp_halfPlaneQuadratic_at hz hu, wp_centeredCayley_boundary hu hz, Complex.real_smul]
  simp only [map_div₀, map_mul, map_pow, map_sub, conj_conj]
  unfold wp_centeredCayley
  push_cast
  rw [hN]
  simp only [map_sub, conj_conj]
  have hDc : conj u - z ≠ 0 := by
    simpa only [map_sub, conj_conj] using (map_ne_zero (starRingEnd ℂ)).mpr hD
  rw [show conj z - z = -(z - conj z) by ring, neg_sq]
  rw [Complex.sub_conj z, Complex.sub_conj u]
  field_simp [hD, hDc, hA, sub_ne_zero.mpr huz, ne_of_gt (show 0 < z.im from hz),
    norm_ne_zero_iff.mpr hD]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals ring

end TakhtajanTeo
