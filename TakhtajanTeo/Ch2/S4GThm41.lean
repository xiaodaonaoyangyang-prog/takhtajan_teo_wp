import TakhtajanTeo.Ch2.S4GFirstVariation
import TakhtajanTeo.Ch2.S4Variation

/-! # `∂∂̄ S₂ = (i/6π) ω_WP` directly, and Theorem 4.1 from it (`s4g_`)

Route (S2/HS; the dominated-differentiation route through (4.1) needs a Calderón–Zygmund `L²(ρ⁻¹)` bound and is
NO-GO). In the chart `V_κ`, with `A(e₁) = B₁` at `[(e₁μ) * κ]` and `D(e₁)` the HS derivative of `B₁` along the
off-centre chart line `e₂ ↦ [(e₁μ + e₂ν) * κ]` (`s4g_off_chart_data`):
- `∂S₂/∂ε_ν` at `[(e₁μ) * κ]` is `T(e₁) = -tr((I - AA*)⁻¹ D A*)` (`s4g_inner_trace`);
- `A`, `D` are HS-holomorphic in `e₁`, so `∂̄T(0) = -[tr(R A₀ Ȧ* R D₀ A₀*) + tr(R D₀ Ȧ*)]` (`s4g_dzbar_trace`);
- at the centre, `Ȧ = B₂ H_μ B₂ᵀ`, `D₀ = B₂ H_ν B₂ᵀ`, and the Grunsky identities collapse the two traces to
  `tr(H_μ* H_ν) = (1/12π) conj ⟨μ, ν⟩_WP` (`s4g_grunsky_trace`).
Hence `∂²S₂/∂ε_μ∂ε̄_ν = -(1/12π) ⟨μ, ν⟩_WP`; `remark_4_3` closes WITHOUT `thm_4_1`, and `thm_4_1` follows from it
and `S₂ = -(1/12π) S₁` on `T₀(1)` (Theorem 3.8, clause 1). -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

/-- `(T A)* = A* T*` on HS matrices. -/
theorem s4g_adjoint_left (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_adjoint (s3tc_left T A) = s3tc_rightCLM (star T) (s3tc_adjoint A) := by
  apply s3tc_toOperator_injective
  rw [s3tc_adjoint_operator, s3tc_left_operator, star_mul, s3tc_right_operator, s3tc_adjoint_operator]

/-- A bounded factor moves across the trace pairing. -/
theorem s4g_trace_move (T : ell2 →L[ℂ] ell2) (A B : s3tc_HS) :
    s3tc_trace (s3tc_rightCLM T A) B = s3tc_trace A (s3tc_left T B) := by
  rw [s3tc_trace_cyclic, ← s3tc_trace_left_right, s3tc_trace_cyclic]

/-- An operator inverse from a one-sided identity against a unit. -/
theorem s4g_eq_one_of_mul {P U : ell2 →L[ℂ] ell2} (hU : IsUnit U) (h : P * U = U) : P = 1 :=
  hU.mul_right_cancel (by rw [h, one_mul])

/-- **The Grunsky algebra** (TT §2, unitarity of the Grunsky operator): with `R = (I - B₁B₁*)⁻¹` and the factor
matrices `Ȧ = B₂ H_μ B₃`, `D = B₂ H_ν B₃`, the two traces of `∂̄ tr(R D A*)` sum to `tr(H_μ* H_ν)`. Only the block
identities of a unitary `2 × 2` operator matrix and `‖B₁‖, ‖B₄‖ < 1` are used. -/
theorem s4g_trace_algebra {b1 b2 b3 b4 : ell2 →L[ℂ] ell2}
    (h12 : b1 * star b1 + b2 * star b2 = 1) (h34 : b3 * star b3 + b4 * star b4 = 1)
    (h13 : star b1 * b1 + star b3 * b3 = 1) (h24 : star b2 * b2 + star b4 * b4 = 1)
    (hb1 : ‖b1‖ < 1) (hb4 : ‖b4‖ < 1) {A₀ Hμ Hν : s3tc_HS} (hA : s3tc_toOperator A₀ = b1) :
    s3tc_trace (s3tc_left (s3ft_resolvent A₀ * s3tc_toOperator A₀ *
          star (s3tc_toOperator (s3tc_left b2 (s3tc_rightCLM b3 Hμ))) * s3ft_resolvent A₀)
          (s3tc_left b2 (s3tc_rightCLM b3 Hν))) (s3tc_adjoint A₀) +
        s3tc_trace (s3tc_left (s3ft_resolvent A₀) (s3tc_left b2 (s3tc_rightCLM b3 Hν)))
          (s3tc_adjoint (s3tc_left b2 (s3tc_rightCLM b3 Hμ))) =
      s3tc_trace (s3tc_adjoint Hμ) Hν := by
  set R := s3ft_resolvent A₀ with hRdef
  have hn1 : ‖b1 * star b1‖ < 1 := by
    calc ‖b1 * star b1‖ ≤ ‖b1‖ * ‖star b1‖ := norm_mul_le _ _
      _ = ‖b1‖ * ‖b1‖ := by rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
      _ < 1 := by nlinarith [norm_nonneg b1]
  have hn1' : ‖star b1 * b1‖ < 1 := by
    calc ‖star b1 * b1‖ ≤ ‖star b1‖ * ‖b1‖ := norm_mul_le _ _
      _ = ‖b1‖ * ‖b1‖ := by rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
      _ < 1 := by nlinarith [norm_nonneg b1]
  have hn4 : ‖star b4 * b4‖ < 1 := by
    calc ‖star b4 * b4‖ ≤ ‖star b4‖ * ‖b4‖ := norm_mul_le _ _
      _ = ‖b4‖ * ‖b4‖ := by rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
      _ < 1 := by nlinarith [norm_nonneg b4]
  have hn4' : ‖b4 * star b4‖ < 1 := by
    calc ‖b4 * star b4‖ ≤ ‖b4‖ * ‖star b4‖ := norm_mul_le _ _
      _ = ‖b4‖ * ‖b4‖ := by rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
      _ < 1 := by nlinarith [norm_nonneg b4]
  have hU1 : IsUnit (1 - b1 * star b1) := isUnit_one_sub_of_norm_lt_one hn1
  have hR : R = Ring.inverse (1 - b1 * star b1) := by
    rw [hRdef, s3ft_resolvent, s3fd_gram, hA]
  have hR1 : R * (1 - b1 * star b1) = 1 := by rw [hR]; exact Ring.inverse_mul_cancel _ hU1
  have hR2 : (1 - b1 * star b1) * R = 1 := by rw [hR]; exact Ring.mul_inverse_cancel _ hU1
  have e12 : 1 - b1 * star b1 = b2 * star b2 := by rw [← h12]; abel
  have e24 : star b2 * b2 = 1 - star b4 * b4 := by rw [← h24]; abel
  have e13 : star b3 * b3 = 1 - star b1 * b1 := by rw [← h13]; abel
  have e34 : b3 * star b3 = 1 - b4 * star b4 := by rw [← h34]; abel
  have hU2 : IsUnit (star b2 * b2) := by rw [e24]; exact isUnit_one_sub_of_norm_lt_one hn4
  have hU3 : IsUnit (star b3 * b3) := by rw [e13]; exact isUnit_one_sub_of_norm_lt_one hn1'
  have hU3' : IsUnit (b3 * star b3) := by rw [e34]; exact isUnit_one_sub_of_norm_lt_one hn4'
  -- (O1) `B₂* R B₂ = I`
  have hO1 : star b2 * R * b2 = 1 := by
    apply s4g_eq_one_of_mul hU2
    calc star b2 * R * b2 * (star b2 * b2) = star b2 * (R * (b2 * star b2)) * b2 := by noncomm_ring
      _ = star b2 * b2 := by rw [← e12, hR1, mul_one]
  -- (O2) `B₃ (I + B₁* R B₁) B₃* = I`
  set Q := 1 + star b1 * R * b1 with hQ
  have hVQ : star b3 * b3 * Q = 1 := by
    have h : (1 - star b1 * b1) * (1 + star b1 * R * b1) =
        1 - star b1 * b1 + star b1 * ((1 - b1 * star b1) * R) * b1 := by
      simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc]
    rw [e13, hQ, h, hR2, mul_one]
    abel
  have hQV : Q * (star b3 * b3) = 1 := by
    apply hU3.mul_left_cancel
    rw [← mul_assoc, hVQ, one_mul, mul_one]
  have hO2 : b3 * Q * star b3 = 1 := by
    apply s4g_eq_one_of_mul hU3'
    calc b3 * Q * star b3 * (b3 * star b3) = b3 * (Q * (star b3 * b3)) * star b3 := by noncomm_ring
      _ = b3 * star b3 := by rw [hQV, mul_one]
  -- the two traces
  set L := s3tc_left (star b3) (s3tc_adjoint Hμ) with hL
  have hT1 : s3tc_trace (s3tc_left R (s3tc_left b2 (s3tc_rightCLM b3 Hν)))
      (s3tc_adjoint (s3tc_left b2 (s3tc_rightCLM b3 Hμ))) = s3tc_trace L (s3tc_rightCLM b3 Hν) := by
    rw [s3tc_trace_cyclic, s4g_adjoint_left, s3tc_adjoint_right, s4g_trace_move]
    apply s3ft_trace_congr_product
    simp only [hL, s3tc_left_operator, s3tc_right_operator, s3tc_adjoint_operator]
    calc star b3 * star (s3tc_toOperator Hμ) * (star b2 * (R * (b2 * (s3tc_toOperator Hν * b3))))
        = star b3 * star (s3tc_toOperator Hμ) * ((star b2 * R * b2) * (s3tc_toOperator Hν * b3)) := by
          noncomm_ring
      _ = _ := by rw [hO1, one_mul]
  have hT2 : s3tc_trace (s3tc_left (R * s3tc_toOperator A₀ *
        star (s3tc_toOperator (s3tc_left b2 (s3tc_rightCLM b3 Hμ))) * R)
        (s3tc_left b2 (s3tc_rightCLM b3 Hν))) (s3tc_adjoint A₀) =
      s3tc_trace L (s3tc_rightCLM (b3 * (star b1 * R * b1)) Hν) := by
    have hsplit : R * s3tc_toOperator A₀ * star (s3tc_toOperator (s3tc_left b2 (s3tc_rightCLM b3 Hμ))) * R =
        (R * s3tc_toOperator A₀) * (star (s3tc_toOperator (s3tc_left b2 (s3tc_rightCLM b3 Hμ))) * R) := by
      noncomm_ring
    rw [hsplit, s3tc_left_mul, s3tc_trace_left_right]
    apply s3ft_trace_congr_product
    simp only [hL, s3tc_left_operator, s3tc_right_operator, s3tc_adjoint_operator, star_mul, hA]
    calc star b3 * star (s3tc_toOperator Hμ) * star b2 * R * (b2 * (s3tc_toOperator Hν * b3)) *
          (star b1 * (R * b1))
        = star b3 * star (s3tc_toOperator Hμ) * ((star b2 * R * b2) * (s3tc_toOperator Hν * b3)) *
          (star b1 * (R * b1)) := by noncomm_ring
      _ = _ := by rw [hO1, one_mul]; noncomm_ring
  rw [hT2, hT1, ← s3tc_trace_add_right]
  have hsum : s3tc_rightCLM (b3 * (star b1 * R * b1)) Hν + s3tc_rightCLM b3 Hν = s3tc_rightCLM (b3 * Q) Hν := by
    apply s3tc_toOperator_injective
    rw [map_add, s3tc_right_operator, s3tc_right_operator, s3tc_right_operator, hQ]
    noncomm_ring
  rw [hsum, hL, s3tc_trace_left_right, ← s3tc_right_mul, hO2, s3tc_right_one]

/-- The exterior Bergman kernel in the orthonormal basis `basisF` of `A₂¹(𝔻*)`:
`Σ_k F_k(u) conj F_k(z) = 1 / (π (u z̄ - 1)²)`. -/
theorem s4g_bergman_sum {u z : ℂ} (hu : u ∈ unitDiscExterior) (hz : z ∈ unitDiscExterior) :
    s3tp_bilinear (s3st_vector u) (star (s3st_vector z)) = 1 / (π * (u * conj z - 1) ^ 2) := by
  have hu1 : 1 < ‖u‖ := hu
  have hz1 : 1 < ‖z‖ := hz
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; linarith
  have hz0 : conj z ≠ 0 := by
    intro h; rw [map_eq_zero] at h; rw [h, norm_zero] at hz1; linarith
  set w : ℂ := (u * conj z)⁻¹ with hw
  have hw1 : ‖w‖ < 1 := by
    rw [hw, norm_inv, norm_mul, Complex.norm_conj]
    exact inv_lt_one_of_one_lt₀ (by nlinarith)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hw0 : w ≠ 0 := inv_ne_zero (mul_ne_zero hu0 hz0)
  have h1w : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw1
    linarith
  have hterm : ∀ n : ℕ, s3st_vector u n * (star (s3st_vector z)) n =
      w ^ 2 / π * (((n : ℂ) * w ^ n) + w ^ n) := by
    intro n
    rw [lp.star_apply, s3st_vector_apply hu, s3st_vector_apply hz, basisF, basisF]
    have hs : ((Real.sqrt (((n : ℝ) + 1) / π) : ℝ) : ℂ) * ((Real.sqrt (((n : ℝ) + 1) / π) : ℝ) : ℂ) =
        ((n : ℂ) + 1) / π := by
      rw [← ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast
      ring
    have hpow : u ^ (-(n : ℤ) - 2) * conj z ^ (-(n : ℤ) - 2) = w ^ (n + 2) := by
      rw [← mul_zpow, hw, inv_pow, ← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring
    simp only [star_mul', Complex.star_def, conj_ofReal, map_zpow₀]
    calc ((Real.sqrt (((n : ℝ) + 1) / π) : ℝ) : ℂ) * u ^ (-(n : ℤ) - 2) *
          (((Real.sqrt (((n : ℝ) + 1) / π) : ℝ) : ℂ) * conj z ^ (-(n : ℤ) - 2))
        = (((Real.sqrt (((n : ℝ) + 1) / π) : ℝ) : ℂ) * ((Real.sqrt (((n : ℝ) + 1) / π) : ℝ) : ℂ)) *
          (u ^ (-(n : ℤ) - 2) * conj z ^ (-(n : ℤ) - 2)) := by ring
      _ = _ := by rw [hs, hpow]; field_simp; ring
  have hsum : HasSum (fun n : ℕ => w ^ 2 / π * (((n : ℂ) * w ^ n) + w ^ n))
      (w ^ 2 / π * (w / (1 - w) ^ 2 + (1 - w)⁻¹)) :=
    ((hasSum_coe_mul_geometric_of_norm_lt_one hw1).add (hasSum_geometric_of_norm_lt_one hw1)).mul_left _
  rw [s3tp_bilinear_sum, tsum_congr hterm, hsum.tsum_eq]
  have hden : u * conj z - 1 ≠ 0 := by
    intro h
    have : u * conj z = 1 := by linear_combination h
    have hw' : w = 1 := by rw [hw, this, inv_one]
    exact h1w (by rw [hw', sub_self])
  have hwz : u * conj z = w⁻¹ := by rw [hw, inv_inv]
  rw [hwz]
  field_simp
  ring

/-- `tr(H_μ* H_ν) = (1/12π) conj ⟨μ, ν⟩_WP` for the HS pairing symbols of two harmonic differentials. -/
theorem s4g_symbol_trace {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    s3tc_trace (s3tc_adjoint (s3tp_symbol hμ)) (s3tp_symbol hν) = 1 / (12 * π) * conj (wpInner μ ν) := by
  have hE : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hdiag : ∀ z ∈ unitDiscExterior, s3st_kernel (s3tc_toOperator (s3tc_adjoint (s3tp_symbol hμ))) z z =
      conj (μ z) * (rho z : ℂ) / (12 * π) := by
    intro z hz
    set T := s3tc_toOperator (s3tp_symbol hμ) with hT
    set v := s3st_vector z with hv
    have h1 : s3st_kernel (s3tc_toOperator (s3tc_adjoint (s3tp_symbol hμ))) z z =
        conj (s3tp_bilinear (star v) (T (star v))) := by
      rw [s3st_kernel, s3tc_adjoint_operator, ← hT, ← hv, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right, s3tp_bilinear, star_star, inner_conj_symm]
    have h2 := s3tp_symbol_pair hμ (star v) (star v)
    rw [← hT] at h2
    have h3 : (∫ u in unitDiscExterior, μ u * s3tp_bilinear (s3st_vector u) (star v) *
        s3tp_bilinear (s3st_vector u) (star v)) =
        ∫ u in unitDiscExterior, μ u * (1 / (π * (u * conj z - 1) ^ 2)) ^ 2 := by
      apply setIntegral_congr_fun hE
      intro u hu
      dsimp only
      rw [hv, s4g_bergman_sum hu hz]
      ring
    rw [h1, h2, h3, ← integral_conj]
    have h4 : (∫ u in unitDiscExterior, conj (μ u * (1 / ((π : ℂ) * (u * conj z - 1) ^ 2)) ^ 2)) =
        1 / (π : ℂ) ^ 2 * ∫ u in unitDiscExterior, conj (μ u) / (1 - conj u * z) ^ 4 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [map_mul, map_pow, map_div₀, map_one, map_sub, conj_ofReal, Complex.conj_conj]
      field_simp
      ring
    have h5 := s4v_kernel_reproduce hμ hz
    rw [h4]
    have h6 : (∫ u in unitDiscExterior, conj (μ u) / (1 - conj u * z) ^ 4) =
        π / 6 * (conj (μ z) * (rho z : ℂ) / 2) := by
      rw [← h5, ← mul_assoc, show (π : ℂ) / 6 * (6 / π) = 1 by field_simp, one_mul]
    rw [h6]
    field_simp
    ring
  have hcongr : (∫ z in unitDiscExterior,
      s3st_kernel (s3tc_toOperator (s3tc_adjoint (s3tp_symbol hμ))) z z * ν z) =
      ∫ z in unitDiscExterior, conj (μ z) * (rho z : ℂ) / (12 * π) * ν z :=
    setIntegral_congr_fun hE (fun z hz => by rw [hdiag z hz])
  rw [s3tp_trace_integral hν, hcongr, wpInner, ← integral_conj, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [map_mul, conj_ofReal, Complex.conj_conj]
  field_simp

/-- `∂̄` at `0` from the derivatives along the real and imaginary axes. -/
theorem s4g_dzbar_of_lines {T : ℂ → ℂ} {a b : ℂ} (hd : DifferentiableAt ℝ T 0)
    (h1 : HasDerivAt (fun s : ℝ => T ((s : ℂ) * 1)) (1 * a + conj 1 * b) 0)
    (hI : HasDerivAt (fun s : ℝ => T ((s : ℂ) * I)) (I * a + conj I * b) 0) :
    dzbar T 0 = b := by
  have hline : ∀ v : ℂ, HasDerivAt (fun s : ℝ => T ((s : ℂ) * v)) (fderiv ℝ T 0 v) 0 := by
    intro v
    have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * v) v 0 := by
      simpa using (ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const v
    exact hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have e1 := (hline 1).unique h1
  have eI := (hline I).unique hI
  show (fderiv ℝ T 0 1 + I * fderiv ℝ T 0 I) / 2 = b
  rw [e1, eI]
  simp only [map_one, conj_I, one_mul]
  ring_nf
  rw [I_sq]
  ring

/-- The real-bilinear left action of operators on HS matrices. -/
theorem s4g_left_bilinear :
    ∃ BL : (ell2 →L[ℂ] ell2) →L[ℝ] s3tc_HS →L[ℝ] s3tc_HS, ∀ T A, BL T A = s3tc_left T A :=
  ⟨(ContinuousLinearMap.restrictScalarsL ℂ s3tc_HS s3tc_HS ℝ ℝ).comp
    ((s3tc_leftAction : (ell2 →L[ℂ] ell2) →L[ℂ] s3tc_HS →L[ℂ] s3tc_HS).restrictScalars ℝ),
    fun T A => s3tc_leftAction_apply T A⟩

theorem s4g_left_smul (c : ℂ) (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_left (c • T) A = c • s3tc_left T A := by
  apply s3tc_toOperator_injective
  rw [s3tc_left_operator, map_smul, s3tc_left_operator, smul_mul_assoc]

theorem s4g_left_smul_right (c : ℂ) (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_left T (c • A) = c • s3tc_left T A := by
  apply s3tc_toOperator_injective
  rw [s3tc_left_operator, map_smul, map_smul, s3tc_left_operator, mul_smul_comm]

theorem s4g_neg_mul (X Y : ell2 →L[ℂ] ell2) : -X * Y = -(X * Y) := by
  ext x
  rfl

theorem s4g_mul_neg (X Y : ell2 →L[ℂ] ell2) : X * -Y = -(X * Y) := by
  ext x
  simp

theorem s4g_left_neg (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_left (-T) A = -s3tc_left T A := by
  apply s3tc_toOperator_injective
  rw [s3tc_left_operator, map_neg, s3tc_left_operator, s4g_neg_mul]

/-- The operator adjoint as a real-linear continuous map. -/
theorem s4g_starR :
    ∃ S : (ell2 →L[ℂ] ell2) →L[ℝ] (ell2 →L[ℂ] ell2), ∀ X, S X = star X := by
  refine ⟨LinearMap.mkContinuous
    { toFun := fun X => star X
      map_add' := fun X Y => star_add X Y
      map_smul' := fun r X => by
        simp only [ContinuousLinearMap.star_eq_adjoint, RingHom.id_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
          LinearIsometryEquiv.map_smulₛₗ]
        simp } 1 (fun X => ?_), fun X => rfl⟩
  simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, ContinuousLinearMap.star_eq_adjoint,
    LinearIsometryEquiv.norm_map, le_refl]

/-- The entries of `B₁` along a line `t ↦ (a + t m) * κ` are holomorphic on every open set of parameters that the
line keeps inside the unit ball. -/
theorem s4g_entries_open {κ a mh : LinfStar} (hκ : κ ∈ LinfStarBall) {U : Set ℂ} (hU : IsOpen U)
    (hsm : ∀ t ∈ U, a + t • mh ∈ LinfStarBall) (m n : ℕ) :
    DifferentiableOn ℂ (fun t => B1 (grunsky (fsans (beltramiMul (a + t • mh) κ))
      (gsans (beltramiMul (a + t • mh) κ))) m n) U := by
  have hball : ∀ t ∈ U, beltramiMul (a + t • mh) κ ∈ LinfStarBall := fun t ht =>
    bg_mul_mem_ball hκ (hsm t ht)
  have hpath : DifferentiableOn ℂ (fun t : ℂ => beltramiMul (a + t • mh) κ) U := by
    intro t ht
    have h1 := ((bd_differentiableOn hκ) _ (hsm t ht)).differentiableAt (isOpen_ball.mem_nhds (hsm t ht))
    have h2 : DifferentiableAt ℂ (fun t : ℂ => a + t • mh) t :=
      (differentiableAt_id.smul_const mh).const_add a
    exact (h1.comp t h2).differentiableWithinAt
  have hpm := fun t (ht : t ∈ U) =>
    AppB.b8_pair_model (AppB.b8_welding_normalized_pair (hball t ht))
  have hbd : ∀ t ∈ U, ∀ m n,
      ‖B1 (grunsky (fsans (beltramiMul (a + t • mh) κ)) (gsans (beltramiMul (a + t • mh) κ))) m n‖ ≤ 1 := by
    intro t ht m n
    obtain ⟨hs, hle⟩ := (hpm t ht).2.1 m
    have h1 : ‖B1 (grunsky (fsans (beltramiMul (a + t • mh) κ)) (gsans (beltramiMul (a + t • mh) κ))) m n‖ ^ 2
        ≤ 1 := (hs.le_tsum n (fun _ _ => sq_nonneg _)).trans hle
    nlinarith [norm_nonneg (B1 (grunsky (fsans (beltramiMul (a + t • mh) κ))
      (gsans (beltramiMul (a + t • mh) κ))) m n)]
  let c : ℂ → ℕ → ℕ → ℂ := fun t p q =>
    B1 (grunsky (fsans (beltramiMul (a + t • mh) κ)) (gsans (beltramiMul (a + t • mh) κ))) p q *
      (Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) : ℂ)
  have hc := AppB.b1_df_coeff_diff hU (c := c) (L := fun p q => Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)))
    (ρ1 := 1 / 2) (ρ2 := 1 / 4) (by norm_num) (by norm_num) (fun p q => Real.sqrt_nonneg _)
    (AppB.b1_summable_L (1 / 2) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by
      intro t ht p q
      simp only [c, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      calc _ ≤ 1 * Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (hbd t ht p q) (Real.sqrt_nonneg _)
        _ = _ := one_mul _)
    (by
      intro z w hz hw
      have hz1 : z ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hz]; norm_num)
      have hw1 : w ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hw]; norm_num)
      have hzw : z ≠ w := by
        intro he; rw [he] at hz; rw [hz] at hw; norm_num at hw
      have hdiffK : DifferentiableOn ℂ (fun t : ℂ =>
          (π : ℂ) * kerK1 (fsans (beltramiMul (a + t • mh) κ)) z w) U := by
        refine DifferentiableOn.const_mul ?_ _
        exact (l27_kerK1_differentiableOn hz1 hw1 hzw).comp hpath (fun t ht => hball t ht)
      refine hdiffK.congr (fun t ht => ?_)
      have hs := ((hpm t ht).2.2.2 z hz1 w hw1 hzw).mul_left (π : ℂ)
      refine (HasSum.tsum_eq ?_)
      refine hs.congr_fun (fun p => ?_)
      have e := AppB.b1_basis_weight p.1 p.2 z w
      calc c t p.1 p.2 * z ^ p.1 * w ^ p.2
          = B1 (grunsky (fsans (beltramiMul (a + t • mh) κ)) (gsans (beltramiMul (a + t • mh) κ))) p.1 p.2 *
            ((Real.sqrt (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) : ℂ) * z ^ p.1 * w ^ p.2) := by
            simp only [c]; ring
        _ = B1 (grunsky (fsans (beltramiMul (a + t • mh) κ)) (gsans (beltramiMul (a + t • mh) κ))) p.1 p.2 *
            ((π : ℂ) * (basisE p.1 z * basisE p.2 w)) := by rw [e]
        _ = _ := by ring) m n
  have hne : ((Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  refine (hc.div_const ((Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℝ) : ℂ)).congr (fun t ht => ?_)
  simp only [c]
  field_simp

/-- The entries of `B₁` at a point of the unit ball are bounded by `1`. -/
theorem s4g_entry_le_one {ν : LinfStar} (hν : ν ∈ LinfStarBall) (m n : ℕ) :
    ‖B1 (grunsky (fsans ν) (gsans ν)) m n‖ ≤ 1 := by
  obtain ⟨hs, hle⟩ := (AppB.b8_pair_model (AppB.b8_welding_normalized_pair hν)).2.1 m
  have h1 : ‖B1 (grunsky (fsans ν) (gsans ν)) m n‖ ^ 2 ≤ 1 :=
    (hs.le_tsum n (fun _ _ => sq_nonneg _)).trans hle
  nlinarith [norm_nonneg (B1 (grunsky (fsans ν) (gsans ν)) m n)]

/-- A Hilbert–Schmidt bound for `B₁` at `b * κ`, uniform over harmonic `b` with `‖b‖ < δ₀` and bounded `L²` norm. -/
theorem s4g_hs_pt {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) {N : ℝ≥0∞} (hN : N < ∞) :
    ∃ M : ℝ≥0∞, M < ∞ ∧ ∀ b : LinfStar, b ∈ harmonicBeltrami → ‖b‖ < delta0 →
      normL2 unitDiscExterior ⇑b ≤ N →
      (∑' q : ℕ × ℕ, (‖B1 (grunsky (fsans (beltramiMul b κ)) (gsans (beltramiMul b κ))) q.1 q.2‖₊ : ℝ≥0∞) ^ 2)
        ≤ M := by
  have hd := delta0_bounds
  set H : ℝ≥0∞ := ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans κ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 with hH
  have hHf : H < ∞ := gk_K1_T01 _ hκT ⟨κ, hκ⟩ rfl
  set S : ℝ≥0∞ := ENNReal.ofReal (1 / (4 * π)) *
    (ENNReal.ofReal (Real.sqrt 2 / (1 - delta0) ^ 2) * N) ^ 2 with hS
  have hSf : S < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.pow_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN))
  refine ⟨2 * S + 2 * H, ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) hSf,
    ENNReal.mul_lt_top (by norm_num) hHf⟩, ?_⟩
  intro b hharm hsm hbN
  have hmem : b ∈ LinfStarBall := mem_ball_zero_iff.mpr (hsm.trans hd.2)
  have hγ : beltramiMul b κ ∈ LinfStarBall := bg_mul_mem_ball hκ hmem
  have hstep := s4g_step_bound (κ := ⟨κ, hκ⟩) (ν := ⟨b, hmem⟩) hharm hsm
  have hle : ENNReal.ofReal (1 / (4 * π)) *
      (ENNReal.ofReal (Real.sqrt 2 / (1 - ‖b‖) ^ 2) * normL2 unitDiscExterior ⇑b) ^ 2 ≤ S := by
    have hA : ENNReal.ofReal (Real.sqrt 2 / (1 - ‖b‖) ^ 2) ≤
        ENNReal.ofReal (Real.sqrt 2 / (1 - delta0) ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      have h1 : 0 < 1 - delta0 := by linarith [hd.2]
      have h2 : 1 - delta0 ≤ 1 - ‖b‖ := by linarith
      exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (pow_le_pow_left₀ h1.le h2 2)
    rw [hS]
    exact mul_le_mul' le_rfl (pow_le_pow_left₀ bot_le (mul_le_mul' hA hbN) 2)
  rw [t210_hs_eq hγ]
  calc ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (beltramiMul b κ)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ q in unitDisc ×ˢ unitDisc,
          (2 * (‖kerK1 (fsans (beltramiMul b κ)) q.1 q.2 - kerK1 (fsans κ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 +
            2 * (‖kerK1 (fsans κ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) :=
        lintegral_mono fun q => gk_sq_tri _ _
    _ = 2 * (∫⁻ q in unitDisc ×ˢ unitDisc,
            (‖kerK1 (fsans (beltramiMul b κ)) q.1 q.2 - kerK1 (fsans κ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) +
          2 * H := by
        rw [lintegral_add_right' _ ((gk_kerK1_aemeas hκ).const_mul 2),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 2 * S + 2 * H := by
        gcongr
        exact hstep.trans hle

/-- The weighted `L²` norm of the zero coefficient. -/
theorem s4g_normL2_zero : normL2 unitDiscExterior ⇑(0 : LinfStar) = 0 := by
  have hae : (⇑(0 : LinfStar) : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] fun _ => (0 : ℂ) :=
    Lp.coeFn_zero _ _ _
  rw [grp_normL2_congr_ae hae, normL2]
  simp

/-- The weighted `L²` norm along the chart plane `e₁ m + e₂ n`, `|e₁|, |e₂| ≤ 1`. -/
theorem s4g_normL2_plane {m n : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hn : n ∈ harmonicL2 unitDiscExterior) {e₁ e₂ : ℂ} (h₁ : ‖e₁‖ ≤ 1) (h₂ : ‖e₂‖ ≤ 1) :
    normL2 unitDiscExterior ⇑(e₁ • toLinf m + e₂ • toLinf n) ≤
      normL2 unitDiscExterior m + normL2 unitDiscExterior n := by
  have h1 := s4g_normL2_line (e₁ • toLinf m) hn h₂
  have h0 := s4g_normL2_line 0 hm h₁
  rw [zero_add, s4g_normL2_zero, zero_add] at h0
  exact h1.trans (add_le_add h0 le_rfl)

/-- A coordinate of a Hilbert–Schmidt curve differentiates with the curve. -/
theorem s4g_coord_deriv {F : ℂ → s3tc_HS} {d : s3tc_HS} (hF : HasDerivAt F d 0) (q : ℕ × ℕ) :
    HasDerivAt (fun t => F t q) (d q) 0 := by
  have h := (innerSL ℂ (lp.single 2 q (1 : ℂ) : s3tc_HS)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) hF
  simpa only [Function.comp_def, innerSL_apply_apply, lp.inner_single_left, inner_self_eq_norm_sq_to_K,
    RCLike.inner_apply, map_one, one_mul, mul_one, starRingEnd_apply, star_one] using h

/-- **The mixed family.** `D(e₁)`, the Hilbert–Schmidt matrix of `∂_{e₂}` of `B₁` at `(e₁μ + e₂ν) * κ`, is a
complex differentiable Hilbert–Schmidt family at `e₁ = 0`. Entrywise holomorphy is a locally uniform limit of
difference quotients (Cauchy estimate, entries bounded by `1`); the Hilbert–Schmidt bound is the Cauchy estimate
in `e₂` summed over the entries. -/
theorem s4g_mixed_family {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ∃ D : ℂ → s3tc_HS,
      (∀ᶠ e₁ in 𝓝 (0 : ℂ), ∀ q : ℕ × ℕ, D e₁ q = deriv (fun s : ℂ =>
        B1 (grunsky (fsans (beltramiMul (e₁ • toLinf μ + s • toLinf ν) (κ : LinfStar)))
          (gsans (beltramiMul (e₁ • toLinf μ + s • toLinf ν) (κ : LinfStar)))) q.1 q.2) 0) ∧
      ∃ D₁ : s3tc_HS, HasDerivAt D D₁ 0 := by
  have hd := delta0_bounds
  have hpi : 0 < π := Real.pi_pos
  set mh := toLinf μ with hmh
  set nh := toLinf ν with hnh
  have hmH : mh ∈ harmonicBeltrami := (harmonicL2_subset_harmonic.choose_spec μ hμ).1
  have hnH : nh ∈ harmonicBeltrami := (harmonicL2_subset_harmonic.choose_spec ν hν).1
  have hμ' := hμ
  obtain ⟨-, -, -, hμL⟩ := hμ'
  have hν' := hν
  obtain ⟨-, -, -, hνL⟩ := hν'
  set ρ : ℝ := min (1 / 4) (delta0 / (8 * (‖mh‖ + ‖nh‖ + 1))) with hρdef
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hd.1 (by positivity))
  have hρ4 : ρ ≤ 1 / 4 := min_le_left _ _
  have hρδ : ρ * (8 * (‖mh‖ + ‖nh‖ + 1)) ≤ delta0 := by
    have h := min_le_right (1 / 4 : ℝ) (delta0 / (8 * (‖mh‖ + ‖nh‖ + 1)))
    rw [← hρdef, le_div_iff₀ (by positivity)] at h
    exact h
  have hsmall : ∀ e₁ s : ℂ, ‖e₁‖ < 2 * ρ → ‖s‖ < 2 * ρ → ‖e₁ • mh + s • nh‖ < delta0 := by
    intro e₁ s h₁ h₂
    calc ‖e₁ • mh + s • nh‖ ≤ ‖e₁‖ * ‖mh‖ + ‖s‖ * ‖nh‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
      _ ≤ 2 * ρ * ‖mh‖ + 2 * ρ * ‖nh‖ := by gcongr
      _ < delta0 := by nlinarith [norm_nonneg mh, norm_nonneg nh]
  have hmemb : ∀ e₁ s : ℂ, ‖e₁‖ < 2 * ρ → ‖s‖ < 2 * ρ → e₁ • mh + s • nh ∈ LinfStarBall :=
    fun e₁ s h₁ h₂ => mem_ball_zero_iff.mpr ((hsmall e₁ s h₁ h₂).trans hd.2)
  set φ : ℂ → ℂ → ℕ → ℕ → ℂ := fun e₁ s p q =>
    B1 (grunsky (fsans (beltramiMul (e₁ • mh + s • nh) (κ : LinfStar)))
      (gsans (beltramiMul (e₁ • mh + s • nh) (κ : LinfStar)))) p q with hφdef
  -- holomorphy in each variable
  have hφs : ∀ e₁ : ℂ, ‖e₁‖ < 2 * ρ → ∀ p q,
      DifferentiableOn ℂ (fun s => φ e₁ s p q) (ball (0 : ℂ) (2 * ρ)) := by
    intro e₁ h₁ p q
    exact s4g_entries_open κ.2 isOpen_ball
      (fun s hs => hmemb e₁ s h₁ (by simpa using hs)) p q
  have hφe : ∀ s : ℂ, ‖s‖ < 2 * ρ → ∀ p q,
      DifferentiableOn ℂ (fun e₁ => φ e₁ s p q) (ball (0 : ℂ) (2 * ρ)) := by
    intro s h₂ p q
    refine (s4g_entries_open (a := s • nh) (mh := mh) κ.2 isOpen_ball
      (fun e₁ he => by rw [add_comm]; exact hmemb e₁ s (by simpa using he) h₂) p q).congr (fun e₁ _ => ?_)
    simp only [hφdef]
    rw [add_comm (e₁ • mh)]
  have hφ1 : ∀ e₁ s : ℂ, ‖e₁‖ < 2 * ρ → ‖s‖ < 2 * ρ → ∀ p q, ‖φ e₁ s p q‖ ≤ 1 :=
    fun e₁ s h₁ h₂ p q => s4g_entry_le_one (bg_mul_mem_ball κ.2 (hmemb e₁ s h₁ h₂)) p q
  set c : ℂ → ℕ → ℕ → ℂ := fun e₁ p q => deriv (fun s => φ e₁ s p q) 0 with hcdef
  -- (a) entrywise holomorphy of `c`
  have hc : ∀ p q, DifferentiableOn ℂ (fun e₁ => c e₁ p q) (ball (0 : ℂ) (2 * ρ)) := by
    intro p q
    let G : ℂ → ℂ → ℂ := fun s e₁ => dslope (fun s' => φ e₁ s' p q) 0 s
    have hG : ∀ᶠ s in 𝓝[≠] (0 : ℂ), DifferentiableOn ℂ (G s) (ball (0 : ℂ) (2 * ρ)) := by
      have h2 : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖s‖ < 2 * ρ :=
        nhdsWithin_le_nhds (Filter.mem_of_superset (ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 2 * ρ by linarith))
          fun s hs => by simpa using hs)
      filter_upwards [self_mem_nhdsWithin, h2] with s hs0 hs
      have h0 : ‖(0 : ℂ)‖ < 2 * ρ := by simp; linarith
      refine (((hφe s hs p q).sub (hφe 0 h0 p q)).div_const s).congr (fun e₁ _ => ?_)
      show dslope (fun s' => φ e₁ s' p q) 0 s = _
      rw [dslope_of_ne _ hs0, slope_def_field, sub_zero]
      rfl
    have hT : TendstoUniformlyOn G (fun e₁ => c e₁ p q) (𝓝[≠] (0 : ℂ)) (ball (0 : ℂ) (2 * ρ)) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hb : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖s‖ < min (ρ / 2) (ε * ρ ^ 2 / 4) :=
        nhdsWithin_le_nhds (Filter.mem_of_superset (ball_mem_nhds (0 : ℂ)
          (show (0 : ℝ) < min (ρ / 2) (ε * ρ ^ 2 / 4) from lt_min (by linarith) (by positivity)))
          fun s hs => by simpa using hs)
      filter_upwards [self_mem_nhdsWithin, hb] with s hs0 hs e₁ he₁
      have he : ‖e₁‖ < 2 * ρ := by simpa using he₁
      have hs1 : ‖s‖ ≤ ρ / 2 := (hs.trans_le (min_le_left _ _)).le
      have hs2 : ‖s‖ < ε * ρ ^ 2 / 4 := hs.trans_le (min_le_right _ _)
      have hle := t210_remainder_le hρ (hφs e₁ he p q) hs0 hs1
      have hcirc : (∫ θ in (0 : ℝ)..2 * π, ‖φ e₁ (circleMap 0 ρ θ) p q‖) ≤ 2 * π := by
        have hcm : ∀ θ : ℝ, circleMap 0 ρ θ ∈ ball (0 : ℂ) (2 * ρ) := fun θ => by
          rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hρ]; linarith
        have hcont : Continuous fun θ : ℝ => φ e₁ (circleMap 0 ρ θ) p q :=
          (hφs e₁ he p q).continuousOn.comp_continuous (continuous_circleMap 0 ρ) hcm
        calc (∫ θ in (0 : ℝ)..2 * π, ‖φ e₁ (circleMap 0 ρ θ) p q‖) ≤ ∫ _ in (0 : ℝ)..2 * π, (1 : ℝ) := by
              apply intervalIntegral.integral_mono_on (by positivity) (hcont.norm.intervalIntegrable _ _)
                intervalIntegrable_const
              intro θ _
              exact hφ1 e₁ _ he (by simpa using hcm θ) p q
          _ = 2 * π := by simp
      have hkey : ‖G s e₁ - c e₁ p q‖ < ε := by
        calc ‖G s e₁ - c e₁ p q‖ ≤ ‖s‖ / (π * ρ ^ 2) * ∫ θ in (0 : ℝ)..2 * π, ‖φ e₁ (circleMap 0 ρ θ) p q‖ := hle
          _ ≤ ‖s‖ / (π * ρ ^ 2) * (2 * π) := mul_le_mul_of_nonneg_left hcirc (by positivity)
          _ = 2 * ‖s‖ / ρ ^ 2 := by field_simp
          _ < ε := by
              rw [div_lt_iff₀ (by positivity)]
              nlinarith
      rw [dist_comm, dist_eq_norm]
      exact hkey
    exact hT.tendstoLocallyUniformlyOn.differentiableOn hG isOpen_ball
  -- (b) a uniform Hilbert–Schmidt bound for `c` on `closedBall 0 ρ`
  obtain ⟨M, hM, hMb⟩ := s4g_hs_pt κ.2 hκ (N := normL2 unitDiscExterior μ + normL2 unitDiscExterior ν)
    (ENNReal.add_lt_top.2 ⟨hμL, hνL⟩)
  have hφM : ∀ e₁ s : ℂ, ‖e₁‖ ≤ ρ → ‖s‖ ≤ ρ → (∑' q : ℕ × ℕ, (‖φ e₁ s q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤ M := by
    intro e₁ s h₁ h₂
    exact hMb _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hmH) (Submodule.smul_mem _ _ hnH))
      (hsmall e₁ s (by linarith) (by linarith))
      (s4g_normL2_plane hμ hν (by linarith) (by linarith))
  set t₀ : ℂ := ((ρ / 2 : ℝ) : ℂ) with ht₀
  have ht₀n : ‖t₀‖ = ρ / 2 := by
    rw [ht₀, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have ht₀0 : t₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at ht₀n; linarith
  set C₁ : ℝ≥0∞ := ENNReal.ofReal (2 * ‖t₀‖ ^ 2 / (π * ρ ^ 4)) with hC₁
  set K : ℝ≥0∞ := (‖t₀⁻¹‖₊ : ℝ≥0∞) ^ 2 with hK
  set M' : ℝ≥0∞ := 2 * (C₁ * (M * ENNReal.ofReal (2 * π))) + 2 * (K * (2 * M + 2 * M)) with hM'
  have hM'f : M' < ∞ := by
    have hK' : K < ∞ := ENNReal.pow_lt_top ENNReal.coe_lt_top
    refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top hM ENNReal.ofReal_lt_top)), ENNReal.mul_lt_top (by norm_num)
      (ENNReal.mul_lt_top hK' (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) hM,
        ENNReal.mul_lt_top (by norm_num) hM⟩))⟩
  have hcb : ∀ e₁ ∈ closedBall (0 : ℂ) ρ, (∑' q : ℕ × ℕ, (‖c e₁ q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤ M' := by
    intro e₁ he₁
    have he : ‖e₁‖ ≤ ρ := by simpa using he₁
    have he2 : ‖e₁‖ < 2 * ρ := by linarith
    have hcm : ∀ θ : ℝ, ‖circleMap 0 ρ θ‖ ≤ ρ := fun θ => by
      rw [norm_circleMap_zero, abs_of_pos hρ]
    have hmeas : ∀ q : ℕ × ℕ, AEMeasurable (fun θ : ℝ => (‖φ e₁ (circleMap 0 ρ θ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2)
        (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
      intro q
      have hcont : Continuous fun θ : ℝ => φ e₁ (circleMap 0 ρ θ) q.1 q.2 :=
        (hφs e₁ he2 q.1 q.2).continuousOn.comp_continuous (continuous_circleMap 0 ρ)
          (fun θ => mem_ball_zero_iff.mpr ((hcm θ).trans_lt (by linarith)))
      exact (hcont.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable
    have hq : ∀ q : ℕ × ℕ, (‖c e₁ q.1 q.2‖₊ : ℝ≥0∞) ^ 2 ≤
        2 * (C₁ * ∫⁻ θ in Ioc (0 : ℝ) (2 * π), (‖φ e₁ (circleMap 0 ρ θ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) +
          2 * (K * (2 * (‖φ e₁ t₀ q.1 q.2‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖φ e₁ 0 q.1 q.2‖₊ : ℝ≥0∞) ^ 2)) := by
      intro q
      set F := fun s => φ e₁ s q.1 q.2 with hF
      have h1 := gk_sq_tri (c e₁ q.1 q.2) (dslope F 0 t₀)
      have h2 := t210_cauchy_sq hρ (hφs e₁ he2 q.1 q.2) (t := t₀) (by rw [ht₀n])
      have h3 : (‖c e₁ q.1 q.2 - dslope F 0 t₀‖₊ : ℝ≥0∞) = ‖dslope F 0 t₀ - deriv F 0‖₊ := by
        rw [← nnnorm_neg, neg_sub]
      have h4 : dslope F 0 t₀ = t₀⁻¹ * (F t₀ - F 0) := by
        rw [dslope_of_ne _ ht₀0, slope_def_field, sub_zero, div_eq_inv_mul]
      have h5 : (‖dslope F 0 t₀‖₊ : ℝ≥0∞) ^ 2 = K * (‖F t₀ - F 0‖₊ : ℝ≥0∞) ^ 2 := by
        rw [h4, nnnorm_mul, ENNReal.coe_mul, mul_pow]
      have h6 := gk_sq_tri (F t₀ - F 0) (-F 0)
      rw [sub_neg_eq_add, sub_add_cancel, nnnorm_neg] at h6
      calc (‖c e₁ q.1 q.2‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖c e₁ q.1 q.2 - dslope F 0 t₀‖₊ : ℝ≥0∞) ^ 2 +
            2 * (‖dslope F 0 t₀‖₊ : ℝ≥0∞) ^ 2 := h1
        _ ≤ _ := by
            rw [h3, h5]
            gcongr
    calc (∑' q : ℕ × ℕ, (‖c e₁ q.1 q.2‖₊ : ℝ≥0∞) ^ 2)
        ≤ ∑' q : ℕ × ℕ, (2 * (C₁ * ∫⁻ θ in Ioc (0 : ℝ) (2 * π), (‖φ e₁ (circleMap 0 ρ θ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) +
          2 * (K * (2 * (‖φ e₁ t₀ q.1 q.2‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖φ e₁ 0 q.1 q.2‖₊ : ℝ≥0∞) ^ 2))) :=
          ENNReal.tsum_le_tsum hq
      _ = 2 * (C₁ * ∫⁻ θ in Ioc (0 : ℝ) (2 * π), ∑' q : ℕ × ℕ, (‖φ e₁ (circleMap 0 ρ θ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) +
          2 * (K * (2 * ∑' q : ℕ × ℕ, (‖φ e₁ t₀ q.1 q.2‖₊ : ℝ≥0∞) ^ 2 +
            2 * ∑' q : ℕ × ℕ, (‖φ e₁ 0 q.1 q.2‖₊ : ℝ≥0∞) ^ 2)) := by
          simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left]
          rw [lintegral_tsum hmeas]
      _ ≤ M' := by
          rw [hM']
          gcongr
          · calc (∫⁻ θ in Ioc (0 : ℝ) (2 * π), ∑' q : ℕ × ℕ, (‖φ e₁ (circleMap 0 ρ θ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2)
                ≤ ∫⁻ _ in Ioc (0 : ℝ) (2 * π), M := lintegral_mono fun θ => hφM e₁ _ he (hcm θ)
              _ = M * ENNReal.ofReal (2 * π) := by rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
          · exact hφM e₁ t₀ he (by rw [ht₀n]; linarith)
          · exact hφM e₁ 0 he (by simp; linarith)
  have hlim := t210_hs_tendsto (c := c) hρ hc hM'f hcb
  have hhs : ∀ᶠ e₁ in 𝓝 (0 : ℂ), Summable (fun q : ℕ × ℕ => ‖c e₁ q.1 q.2‖ ^ 2) := by
    filter_upwards [closedBall_mem_nhds (0 : ℂ) hρ] with e₁ he
    exact s3fv_hs_of_ennreal ((hcb e₁ he).trans_lt hM'f)
  obtain ⟨D, D₁, he, -, hD⟩ := s3fv_hilbert_derivative (A := c)
    (D := fun p q => deriv (fun e => c e p q) 0) hhs hlim
  exact ⟨D, he, D₁, hD⟩

/-- **Stub (i)+(ii).** The two HS families of the chart `V_κ`: `A(e₁) = B₁` at `[(e₁μ) * κ]`, and `D(e₁)`, whose
trace against `A(e₁)` is the derivative of `S₂` along the off-centre chart line in the direction `ν`. Both are
complex differentiable at `0`; their derivative and value at `0` are the centre factor matrices. -/
theorem s4g_inner_trace {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ∃ A D : ℂ → s3tc_HS,
      (∀ᶠ e₁ in 𝓝 (0 : ℂ),
        (∀ q : ℕ × ℕ, A e₁ q = B1 (grunsky (fsans (beltramiMul (e₁ • toLinf μ) (κ : LinfStar)))
          (gsans (beltramiMul (e₁ • toLinf μ) (κ : LinfStar)))) q.1 q.2) ∧
        DifferentiableAt ℝ (fun e₂ : ℂ =>
          (liouvilleS2 (ptT (beltramiMul (e₁ • toLinf μ + e₂ • toLinf ν) (κ : LinfStar))) : ℂ)) 0 ∧
        dz (fun e₂ : ℂ => (liouvilleS2 (ptT (beltramiMul (e₁ • toLinf μ + e₂ • toLinf ν) (κ : LinfStar))) : ℂ)) 0 =
          -s3tc_trace (s3tc_left (s3ft_resolvent (A e₁)) (D e₁)) (s3tc_adjoint (A e₁))) ∧
      HasDerivAt A (s3sv_factor (κ : LinfStar) hμ) 0 ∧
      (∃ D₁ : s3tc_HS, HasDerivAt D D₁ 0) ∧
      D 0 = s3sv_factor (κ : LinfStar) hν := by
  have hd := delta0_bounds
  have hmH : toLinf μ ∈ harmonicBeltrami := (harmonicL2_subset_harmonic.choose_spec μ hμ).1
  have hμ' := hμ
  obtain ⟨-, -, -, hμL⟩ := hμ'
  have hκT : Phi ⟨(κ : LinfStar), κ.2⟩ ∈ T01 := hκ
  -- the centre family `A` and its derivative
  obtain ⟨FA, dA, heA, hFA, -, -⟩ := s3kv_chart_data κ.2 hκT hμ
  have hdA := s3sv_actual_factor κ.2 hκT hμ heA hFA
  -- the mixed family `D`
  obtain ⟨D, heD, D₁, hD⟩ := s4g_mixed_family hκ hμ hν
  -- `D 0` is the centre factor in the direction `ν`
  obtain ⟨FN, dN, heN, hFN, -, -⟩ := s3kv_chart_data κ.2 hκT hν
  have hdN := s3sv_actual_factor κ.2 hκT hν heN hFN
  have hD0 : D 0 = s3sv_factor (κ : LinfStar) hν := by
    rw [← hdN]
    apply lp.ext
    funext q
    rw [heD.self_of_nhds q]
    have h2 : HasDerivAt (fun s : ℂ => B1 (grunsky (fsans (beltramiMul ((0 : ℂ) • toLinf μ + s • toLinf ν)
        (κ : LinfStar))) (gsans (beltramiMul ((0 : ℂ) • toLinf μ + s • toLinf ν) (κ : LinfStar)))) q.1 q.2)
        (dN q) 0 := by
      apply (s4g_coord_deriv hFN q).congr_of_eventuallyEq
      filter_upwards [heN] with s hs
      rw [hs q, zero_smul, zero_add]
    exact h2.deriv
  refine ⟨FA, D, ?_, hdA ▸ hFA, ⟨D₁, hD⟩, hD0⟩
  -- the off-centre trace formula
  have hev1 : ∀ᶠ e₁ in 𝓝 (0 : ℂ), ‖e₁ • toLinf μ‖ < delta0 := by
    have hc : Continuous fun e₁ : ℂ => ‖e₁ • toLinf μ‖ := (continuous_id.smul continuous_const).norm
    have h0 : ‖(0 : ℂ) • toLinf μ‖ < delta0 := by simp [hd.1]
    exact (hc.tendsto 0).eventually_lt_const h0
  have hev2 : ∀ᶠ e₁ in 𝓝 (0 : ℂ), ‖e₁‖ ≤ 1 :=
    Filter.mem_of_superset (closedBall_mem_nhds (0 : ℂ) one_pos) fun e he => by simpa using he
  filter_upwards [heA, heD, hev1, hev2] with e₁ hA hDe has he1
  have ha : e₁ • toLinf μ ∈ harmonicBeltrami := Submodule.smul_mem _ _ hmH
  have haL : normL2 unitDiscExterior ⇑(e₁ • toLinf μ) < ∞ := by
    have h0 := s4g_normL2_line 0 hμ he1
    rw [zero_add, s4g_normL2_zero, zero_add] at h0
    exact h0.trans_lt hμL
  have ha1 : e₁ • toLinf μ ∈ LinfStarBall := mem_ball_zero_iff.mpr (has.trans hd.2)
  have hν' : beltramiMul (e₁ • toLinf μ) (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 ha1
  obtain ⟨Fo, d₀, heo, hFo, -⟩ := s4g_off_chart_data hκ ha has haL hν
  have hF0 : Fo 0 = FA e₁ := by
    apply lp.ext
    funext q
    rw [hA q]
    have h1 := (heo.self_of_nhds).2 q
    simp only [zero_smul, add_zero] at h1
    exact h1
  have hd0 : d₀ = D e₁ := by
    apply lp.ext
    funext q
    rw [hDe q]
    have h2 : HasDerivAt (fun s : ℂ => B1 (grunsky (fsans (beltramiMul (e₁ • toLinf μ + s • toLinf ν)
        (κ : LinfStar))) (gsans (beltramiMul (e₁ • toLinf μ + s • toLinf ν) (κ : LinfStar)))) q.1 q.2)
        (d₀ q) 0 := by
      apply (s4g_coord_deriv hFo q).congr_of_eventuallyEq
      filter_upwards [heo] with s hs
      exact (hs.2 q).symm
    exact h2.deriv.symm
  have hgap : ‖s3tc_toOperator (Fo 0)‖ < 1 := by
    have hop0 : s3tc_toOperator (Fo 0) = gopOp (B1 (grunsky (fsans (beltramiMul (e₁ • toLinf μ) (κ : LinfStar)))
        (gsans (beltramiMul (e₁ • toLinf μ) (κ : LinfStar))))) := by
      change gopOp (fun m n => Fo 0 (m,n)) = _
      congr 1
      funext p q
      have h1 := (heo.self_of_nhds).2 (p, q)
      simp only [zero_smul, add_zero] at h1
      exact h1
    rw [hop0]
    exact (pgb_norm_lt_one hν').1
  obtain ⟨-, hLog⟩ := s3fd_logSeries_hasFDeriv (Fo 0) hgap
  have hgo : (fun t : ℂ => liouvilleS2 (ptT (beltramiMul (e₁ • toLinf μ + t • toLinf ν) (κ : LinfStar))))
      =ᶠ[𝓝 (0 : ℂ)] (fun t => s3fd_logSeries (Fo t)) := by
    filter_upwards [heo] with t ht
    rw [ptT, dif_pos ht.1]
    exact (s3fd_liouville_eq ht.1 (Fo t) (fun p q => ht.2 (p,q))).symm
  have hfd : DifferentiableAt ℝ
      (fun t : ℂ => liouvilleS2 (ptT (beltramiMul (e₁ • toLinf μ + t • toLinf ν) (κ : LinfStar)))) 0 :=
    ((hLog.comp (0 : ℂ) (hFo.hasFDerivAt.restrictScalars ℝ)).congr_of_eventuallyEq hgo).differentiableAt
  have hv : ∀ v : ℂ, HasDerivAt (fun s : ℝ =>
      liouvilleS2 (ptT (beltramiMul (e₁ • toLinf μ + ((s : ℂ) * v) • toLinf ν) (κ : LinfStar))))
      (∑' N, s3fd_traceTerm (Fo 0) (v • d₀) N) 0 := by
    intro v
    have ht : Tendsto (fun s : ℝ => (s : ℂ) * v) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun s : ℝ => (s : ℂ) * v := continuous_ofReal.mul continuous_const
      simpa using hc.tendsto 0
    exact (s3fd_curve_derivative hFo hgap v).congr_of_eventuallyEq (ht.eventually hgo)
  have hW := s3ft_wirtinger
    (f := fun t : ℂ => liouvilleS2 (ptT (beltramiMul (e₁ • toLinf μ + t • toLinf ν) (κ : LinfStar)))) hfd (Fo 0) d₀ hgap hv
  refine ⟨hA, (s4g_S2_offcentre_variation hκ ha has haL hν).1, ?_⟩
  rw [← hF0, ← hd0]
  exact hW

/-- **Stub (iii).** `∂̄` of the first-variation trace along HS-holomorphic families. -/
theorem s4g_dzbar_trace {A D : ℂ → s3tc_HS} {A₁ D₁ : s3tc_HS} (hA : HasDerivAt A A₁ 0) (hD : HasDerivAt D D₁ 0)
    (hA0 : ‖s3tc_toOperator (A 0)‖ < 1) :
    let T : ℂ → ℂ := fun e => -s3tc_trace (s3tc_left (s3ft_resolvent (A e)) (D e)) (s3tc_adjoint (A e))
    let R := s3ft_resolvent (A 0)
    DifferentiableAt ℝ T 0 ∧
      dzbar T 0 = -(s3tc_trace (s3tc_left (R * s3tc_toOperator (A 0) * star (s3tc_toOperator A₁) * R) (D 0))
          (s3tc_adjoint (A 0)) + s3tc_trace (s3tc_left R (D 0)) (s3tc_adjoint A₁)) := by
  intro T R
  have hU : IsUnit (1 - s3fd_gram (A 0)) := (s3ft_neumann (A 0) hA0).1
  set u := hU.unit with hu
  have hu1 : (u : ell2 →L[ℂ] ell2) = 1 - s3fd_gram (A 0) := hU.unit_spec
  have hRu : R = ((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2) := by
    show Ring.inverse (1 - s3fd_gram (A 0)) = _
    rw [← hu1, Ring.inverse_unit]
  obtain ⟨BL, hBL⟩ := s4g_left_bilinear
  obtain ⟨SR, hSR⟩ := s4g_starR
  have hTe : T = fun e => -inner ℂ (A e) (BL (Ring.inverse (1 - s3tc_toOperator (A e) *
      star (s3tc_toOperator (A e)))) (D e)) := by
    funext e
    show -s3tc_trace (s3tc_left (s3ft_resolvent (A e)) (D e)) (s3tc_adjoint (A e)) = _
    rw [s3tc_trace_gram_pair, hBL]
    rfl
  have hInvF : HasFDerivAt (Ring.inverse : (ell2 →L[ℂ] ell2) → (ell2 →L[ℂ] ell2))
      ((-ContinuousLinearMap.mulLeftRight ℂ (ell2 →L[ℂ] ell2) ↑u⁻¹ ↑u⁻¹).restrictScalars ℝ)
      (u : ell2 →L[ℂ] ell2) :=
    (hasFDerivAt_ringInverse u).restrictScalars ℝ
  -- real differentiability
  have hd : DifferentiableAt ℝ T 0 := by
    rw [hTe]
    have hA' := (hA.hasFDerivAt.restrictScalars ℝ).differentiableAt
    have hD' := (hD.hasFDerivAt.restrictScalars ℝ).differentiableAt
    have hO : DifferentiableAt ℝ (fun e => s3tc_toOperator (A e)) 0 :=
      ((s3tc_toOperator.restrictScalars ℝ).differentiableAt).comp (0 : ℂ) hA'
    have hS : DifferentiableAt ℝ (fun e => star (s3tc_toOperator (A e))) 0 := by
      have h := (SR.differentiableAt).comp (0 : ℂ) hO
      simpa only [Function.comp_def, hSR] using h
    have hG : DifferentiableAt ℝ (fun e => 1 - s3tc_toOperator (A e) * star (s3tc_toOperator (A e))) 0 :=
      (differentiableAt_const _).sub (hO.mul hS)
    have hI : DifferentiableAt ℝ (fun e => Ring.inverse (1 - s3tc_toOperator (A e) *
        star (s3tc_toOperator (A e)))) 0 := by
      have h := hInvF.differentiableAt
      rw [hu1] at h
      exact h.comp (0 : ℂ) hG
    have hX : DifferentiableAt ℝ (fun e => BL (Ring.inverse (1 - s3tc_toOperator (A e) *
        star (s3tc_toOperator (A e)))) (D e)) 0 :=
      (BL.differentiableAt.comp (0 : ℂ) hI).clm_apply hD'
    exact (hA'.inner ℂ hX).neg
  -- the derivative along `s ↦ s v`
  have hlineT : ∀ v : ℂ, HasDerivAt (fun s : ℝ => T ((s : ℂ) * v))
      (v * -(inner ℂ (A 0) (s3tc_left (R * s3tc_toOperator A₁ * star (s3tc_toOperator (A 0)) * R) (D 0)) +
          inner ℂ (A 0) (s3tc_left R D₁)) +
        conj v * -(inner ℂ A₁ (s3tc_left R (D 0)) +
          inner ℂ (A 0) (s3tc_left (R * s3tc_toOperator (A 0) * star (s3tc_toOperator A₁) * R) (D 0)))) 0 := by
    intro v
    have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * v) v 0 := by
      simpa using (ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const v
    have hl0 : (fun s : ℝ => (s : ℂ) * v) 0 = 0 := by simp
    have hA1 : HasDerivAt (fun s : ℝ => A ((s : ℂ) * v)) (v • A₁) 0 := by
      have h := hA
      rw [← hl0] at h
      exact h.scomp (0 : ℝ) hl
    have hD1 : HasDerivAt (fun s : ℝ => D ((s : ℂ) * v)) (v • D₁) 0 := by
      have h := hD
      rw [← hl0] at h
      exact h.scomp (0 : ℝ) hl
    have hO : HasDerivAt (fun s : ℝ => s3tc_toOperator (A ((s : ℂ) * v))) (s3tc_toOperator (v • A₁)) 0 :=
      (s3tc_toOperator.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA1
    have hS : HasDerivAt (fun s : ℝ => star (s3tc_toOperator (A ((s : ℂ) * v))))
        (star (s3tc_toOperator (v • A₁))) 0 := by
      have h := SR.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hO
      simpa only [Function.comp_def, hSR] using h
    have hG := (hasDerivAt_const (0 : ℝ) (1 : ell2 →L[ℂ] ell2)).sub (hO.mul hS)
    have hpt : (fun s : ℝ => 1 - s3tc_toOperator (A ((s : ℂ) * v)) * star (s3tc_toOperator (A ((s : ℂ) * v)))) 0 =
        (u : ell2 →L[ℂ] ell2) := by
      rw [hu1]
      simp [s3fd_gram]
    have hInv := (hpt ▸ hInvF).comp_hasDerivAt (0 : ℝ) hG
    have hX := (BL.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hInv).clm_apply hD1
    have hIn := (hA1.inner ℂ hX).neg
    have hfun : (fun s : ℝ => T ((s : ℂ) * v)) = fun s : ℝ => -inner ℂ (A ((s : ℂ) * v))
        (BL (Ring.inverse (1 - s3tc_toOperator (A ((s : ℂ) * v)) * star (s3tc_toOperator (A ((s : ℂ) * v)))))
          (D ((s : ℂ) * v))) := by
      rw [hTe]
    rw [hfun]
    convert hIn using 1
    · funext s
      rfl
    have hz : ((0 : ℝ) : ℂ) * v = 0 := by simp
    simp only [hz, Function.comp_apply, hBL, ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.mulLeftRight_apply, map_smul, star_smul, zero_sub]
    have hu1' : (u : ell2 →L[ℂ] ell2) = 1 - s3tc_toOperator (A 0) * star (s3tc_toOperator (A 0)) := hu1
    simp only [Pi.sub_apply, Pi.mul_apply, ofReal_zero, zero_mul]
    rw [← hu1', Ring.inverse_unit, ← hRu]
    simp only [mul_neg, neg_mul, s4g_neg_mul, s4g_mul_neg, neg_neg, neg_add, mul_add, Complex.star_def, s4g_left_neg, inner_neg_right, add_mul, smul_mul_assoc, mul_smul_comm, s3ft_left_add,
      s4g_left_smul, s4g_left_smul_right, inner_add_right, inner_smul_right, inner_smul_left, mul_assoc]
    ring
  refine ⟨hd, ?_⟩
  rw [s4g_dzbar_of_lines hd (hlineT 1) (hlineT I), ← s3tc_trace_gram_pair, ← s3tc_trace_gram_pair]
  ring

/-- **Stub (iv).** At the centre of `V_κ`, the Grunsky identities and the exterior Bergman kernel reduce the two
traces to `(1/12π) conj ⟨μ, ν⟩_WP`. -/
theorem s4g_grunsky_trace {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) {A₀ : s3tc_HS}
    (hA₀ : ∀ q : ℕ × ℕ, A₀ q = B1 (grunsky (fsans (κ : LinfStar)) (gsans (κ : LinfStar))) q.1 q.2) :
    let R := s3ft_resolvent A₀
    let A₁ := s3sv_factor (κ : LinfStar) hμ
    let D₀ := s3sv_factor (κ : LinfStar) hν
    s3tc_trace (s3tc_left (R * s3tc_toOperator A₀ * star (s3tc_toOperator A₁) * R) D₀) (s3tc_adjoint A₀) +
        s3tc_trace (s3tc_left R D₀) (s3tc_adjoint A₁) = 1 / (12 * π) * conj (wpInner μ ν) := by
  intro R A₁ D₀
  have hp := AppB.b8_welding_normalized_pair κ.2
  obtain ⟨h12, h34, -, h13, h24, -⟩ := gop_blocks hp (r22_complement_null κ.2)
  simp only [← ContinuousLinearMap.star_eq_adjoint] at h12 h34 h13 h24
  have hn := pgb_norm_lt_one κ.2
  have hA : s3tc_toOperator A₀ = gopOp (B1 (grunsky (fsans (κ : LinfStar)) (gsans (κ : LinfStar)))) := by
    change gopOp (fun m n => A₀ (m,n)) = _
    congr 1
    funext m n
    exact hA₀ (m, n)
  have h := s4g_trace_algebra h12 h34 h13 h24 hn.1 hn.2 (Hμ := s3tp_symbol hμ) (Hν := s3tp_symbol hν) hA
  show s3tc_trace (s3tc_left (s3ft_resolvent A₀ * s3tc_toOperator A₀ *
        star (s3tc_toOperator (s3sv_factor (κ : LinfStar) hμ)) * s3ft_resolvent A₀) (s3sv_factor (κ : LinfStar) hν))
        (s3tc_adjoint A₀) + s3tc_trace (s3tc_left (s3ft_resolvent A₀) (s3sv_factor (κ : LinfStar) hν))
        (s3tc_adjoint (s3sv_factor (κ : LinfStar) hμ)) = _
  rw [s3sv_factor, s3sv_factor, h, s4g_symbol_trace hμ hν]

/-- For a real-valued function, `∂̄ = conj ∂` at a point of real differentiability. -/
theorem s4g_dzbar_ofReal {g : ℂ → ℝ} {z : ℂ} (hg : DifferentiableAt ℝ (fun e => (g e : ℂ)) z) :
    dzbar (fun e => (g e : ℂ)) z = conj (dz (fun e => (g e : ℂ)) z) := by
  have hg' : DifferentiableAt ℝ g z := by
    have h := (reCLM.differentiableAt).comp z hg
    simpa [Function.comp_def] using h
  have hf : fderiv ℝ (fun e => (g e : ℂ)) z = ofRealCLM.comp (fderiv ℝ g z) :=
    (ofRealCLM.hasFDerivAt.comp z hg'.hasFDerivAt).fderiv
  show (fderiv ℝ _ z 1 + I * fderiv ℝ _ z I) / 2 = conj ((fderiv ℝ _ z 1 - I * fderiv ℝ _ z I) / 2)
  rw [hf]
  simp only [ContinuousLinearMap.comp_apply, ofRealCLM_apply, map_div₀, map_sub, map_mul, conj_ofReal, conj_I, map_ofNat]
  norm_num

/-- `∂(f̄) = conj (∂̄ f)`, with no differentiability hypothesis. -/
theorem s4g_dz_conj (f : ℂ → ℂ) (z : ℂ) : dz (fun e => conj (f e)) z = conj (dzbar f z) := by
  have hf : fderiv ℝ (fun e => conj (f e)) z = (conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z) :=
    conjCLE.comp_fderiv (f := f) (x := z)
  show (fderiv ℝ _ z 1 - I * fderiv ℝ _ z I) / 2 = conj ((fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2)
  rw [hf]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_div₀, map_add,
    map_mul, conj_I, map_ofNat]
  norm_num
  ring

/-- `∂²S₂/∂ε_μ∂ε̄_ν([κ]) = -(1/12π) ⟨μ, ν⟩_WP` in the Bers coordinates of `V_κ`, any representative `κ`. -/
theorem s4g_S2_ddbar {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    bersDzDzbar liouvilleS2 (κ : LinfStar) μ ν = -(1 / (12 * π)) * wpInner μ ν := by
  obtain ⟨A, D, hev, hA, ⟨D₁, hD⟩, hD0⟩ := s4g_inner_trace hκ hμ hν
  have hA0 : ∀ q : ℕ × ℕ, A 0 q = B1 (grunsky (fsans (κ : LinfStar)) (gsans (κ : LinfStar))) q.1 q.2 := by
    intro q
    have h := (hev.self_of_nhds).1 q
    simpa only [zero_smul, grp_zero_mul κ.2] using h
  have hgap : ‖s3tc_toOperator (A 0)‖ < 1 := by
    have hop : s3tc_toOperator (A 0) = gopOp (B1 (grunsky (fsans (κ : LinfStar)) (gsans (κ : LinfStar)))) := by
      change gopOp (fun m n => A 0 (m,n)) = _
      congr 1
      funext m n
      exact hA0 (m, n)
    rw [hop]
    exact (pgb_norm_lt_one κ.2).1
  obtain ⟨-, hT⟩ := s4g_dzbar_trace hA hD hgap
  have hin : (fun e₁ : ℂ => dzbar (fun e₂ : ℂ =>
      (liouvilleS2 (ptT (beltramiMul (e₁ • toLinf μ + e₂ • toLinf ν) (κ : LinfStar))) : ℂ)) 0) =ᶠ[𝓝 (0 : ℂ)]
      fun e₁ => conj (-s3tc_trace (s3tc_left (s3ft_resolvent (A e₁)) (D e₁)) (s3tc_adjoint (A e₁))) := by
    filter_upwards [hev] with e₁ he
    rw [s4g_dzbar_ofReal he.2.1, he.2.2]
  unfold bersDzDzbar
  rw [l613_dz_congr hin, s4g_dz_conj, hT, hD0]
  have hG := s4g_grunsky_trace hκ hμ hν hA0
  dsimp only at hG
  rw [hG]
  simp only [map_neg, map_mul, map_div₀, map_one, conj_ofReal, Complex.conj_conj, map_ofNat]
  push_cast
  ring

/-- **Remark 4.3**, proved directly (statement identical to `remark_4_3`; no dependence on Theorem 4.1). -/
theorem s4g_remark_4_3_direct {p : T1} (hp : p ∈ T01) {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    bersDzDzbar liouvilleS2 (Quotient.out p : LinfStarBall) μ ν = I / (6 * π) * omegaWPOrigin μ ν := by
  have hp' : Phi (Quotient.out p : LinfStarBall) ∈ T01 := by
    rw [show Phi (Quotient.out p : LinfStarBall) = p from Quotient.out_eq (s := teichSetoid) p]
    exact hp
  rw [s4g_S2_ddbar hp' hμ hν, omegaWPOrigin]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **Theorem 4.1** from Theorem 3.8 clause 1 (statement identical to `thm_4_1` after `h38`). -/
theorem s4g_thm_4_1 (h38 : ∀ p ∈ T01, liouvilleS2 p = -(1 / (12 * π)) * liouvilleS1 p) {p : T1} (hp : p ∈ T01)
    {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    bersDzDzbar liouvilleS1 (Quotient.out p : LinfStarBall) μ ν = wpInner μ ν := by
  have hc : componentT (Phi (Quotient.out p : LinfStarBall)) = T01 := by
    rw [show Phi (Quotient.out p : LinfStarBall) = p from Quotient.out_eq (s := teichSetoid) p]
    exact (@connectedComponent_eq _ hilbertTopology _ _ hp).symm
  have hp' : Phi (Quotient.out p : LinfStarBall) ∈ T01 := by
    rw [show Phi (Quotient.out p : LinfStarBall) = p from Quotient.out_eq (s := teichSetoid) p]
    exact hp
  have he : bersDzDzbar liouvilleS1 (Quotient.out p : LinfStarBall) μ ν =
      bersDzDzbar (fun q => -(12 * π) * liouvilleS2 q) (Quotient.out p : LinfStarBall) μ ν := by
    apply s4g_bersDzDzbar_congr
    filter_upwards [s4g_local_component hμ hν (Quotient.out p)] with e he
    rw [hc] at he
    rw [h38 _ he.2]
    field_simp
  rw [he, s4g_bersDzDzbar_const_mul, s4g_S2_ddbar hp' hμ hν]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp

/-- **Remark 4.3** (TT:5356). `∂∂̄ log det N_Ω = (i/6π) ω_WP` on `T₀(1)`. By Corollary 2.16, `log det N_Ω = S₂`. -/
theorem remark_4_3 {p : T1} (hp : p ∈ T01) {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    bersDzDzbar liouvilleS2 (Quotient.out p : LinfStarBall) μ ν = I / (6 * π) * omegaWPOrigin μ ν := by
  exact s4g_remark_4_3_direct hp hμ hν

end Ch2
end TakhtajanTeo
