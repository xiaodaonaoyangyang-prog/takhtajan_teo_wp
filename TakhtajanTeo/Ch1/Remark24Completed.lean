import TakhtajanTeo.Ch1.QuasidiskKernel

/-!
# Remark 2.4, proved downstream of §2 (TT:1594–1600)

`r24_remark_2_4` is `remark_2_4`: `‖D₀(β ∘ Φ ∘ R_μ)(ν)‖₂ ≤ 24 ‖ν‖₂`. By (2.1) (`eq_2_1`), Cauchy–Schwarz and the
two kernel bounds of `QuasidiskKernel`, `‖D₀(β ∘ R_[μ])(ν)‖₂² ≤ 6² · 4² ‖ν‖₂² = 576 ‖ν‖₂²` (TT:1523).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real NNReal
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The squared `L²` norm on `𝔻*` as a lintegral. -/
theorem r24_normL2_sq (ν : ℂ → ℂ) :
    normL2 unitDiscExterior ν ^ 2 =
      ∫⁻ z in unitDiscExterior, (‖ν z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) := by
  unfold normL2
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The squared `A₂` norm on `𝔻` as a lintegral. -/
theorem r24_normA2_sq (φ : ℂ → ℂ) :
    normA2 unitDisc φ ^ 2 = ∫⁻ z in unitDisc, (‖φ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ := by
  unfold normA2
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- (2.1) read on `𝔻`: `D₀(β ∘ R_[μ])(ν)(ζ) = -(6/π) 𝖿'(ζ)² ∬_{Ω*} ν̃(u)/(u - 𝖿(ζ))⁴ d²u`. -/
theorem r24_phi_formula {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) {ζ : ℂ} (hζ : ζ ∈ unitDisc) :
    AInf.toFun (D0BersR μ ν) ζ = -(6 / π) * deriv (fsans μ) ζ ^ 2 *
      ∫ u in gsans μ '' unitDiscExterior,
        ν (Function.invFunOn (gsans μ) unitDiscExterior u) *
          (conj (deriv (Function.invFunOn (gsans μ) unitDiscExterior) u) /
            deriv (Function.invFunOn (gsans μ) unitDiscExterior) u) / (u - fsans μ ζ) ^ 4 := by
  have hf := S2C.s2c_conf_f hμ
  have h := eq_2_1 hμ ν ⟨ζ, hζ, rfl⟩
  have hF : Function.invFunOn (fsans μ) unitDisc (fsans μ ζ) = ζ := hf.2.1.leftInvOn_invFunOn hζ
  have hF' := t1_deriv_invFunOn_mul (U := unitDisc) isOpen_ball hf hζ
  have hφ' : deriv (fsans μ) ζ ≠ 0 := kb_deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hζ
  have hFi : deriv (Function.invFunOn (fsans μ) unitDisc) (fsans μ ζ) = (deriv (fsans μ) ζ)⁻¹ :=
    eq_inv_of_mul_eq_one_left hF'
  rw [hF, hFi] at h
  rw [show ∀ I : ℂ, -(6 / π) * deriv (fsans μ) ζ ^ 2 * I = deriv (fsans μ) ζ ^ 2 * (-(6 / π) * I) from
    fun I => by ring, ← h]
  field_simp

/-- The pointwise integrand bound: `|ν̃(u)/(u - z)⁴| ≤ |ν(G u)| |u - z|⁻⁴`. -/
theorem r24_integrand_le (a b w : ℂ) (u z : ℂ) :
    ‖a * (conj b / b) / (u - z) ^ 4‖ₑ ≤ ‖a‖ₑ * (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 := by
  by_cases huz : u - z = 0
  · rw [huz]; simp
  have hb : ‖conj b / b‖ ≤ 1 := by
    by_cases hb0 : b = 0
    · simp [hb0]
    · rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hb0)]
  have hp : 0 < ‖u - z‖ := norm_pos_iff.mpr huz
  have hk : (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 = ENNReal.ofReal ((‖u - z‖ ^ 4)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow hp.le, ← ENNReal.inv_pow, ofReal_norm,
      enorm_eq_nnnorm]
  rw [hk, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_div, norm_mul, norm_pow, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) hb) (by positivity)

/-- Cauchy–Schwarz in the form `(∫ A B)² ≤ (∫ A)(∫ A B²)`. -/
theorem r24_cauchy_schwarz {α : Type*} [MeasurableSpace α] (m : Measure α) {A B : α → ℝ≥0∞}
    (hA : AEMeasurable A m) (hB : AEMeasurable B m) :
    (∫⁻ x, A x * B x ∂m) ^ 2 ≤ (∫⁻ x, A x ∂m) * ∫⁻ x, A x * B x ^ 2 ∂m := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hsA : AEMeasurable (fun x => A x ^ (1 / 2 : ℝ)) m := hA.pow_const _
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq m hpq hsA (hsA.mul hB)
  have e1 : ∀ x, (A x ^ (1 / 2 : ℝ)) * (A x ^ (1 / 2 : ℝ) * B x) = A x * B x := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ x, (A x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = A x := by
    intro x; rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ x, (A x ^ (1 / 2 : ℝ) * B x) ^ (2 : ℝ) = A x * B x ^ 2 := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, e1, e2, e3] at h
  calc (∫⁻ x, A x * B x ∂m) ^ 2
      ≤ ((∫⁻ x, A x ∂m) ^ (1 / 2 : ℝ) * (∫⁻ x, A x * B x ^ 2 ∂m) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ x, A x ∂m) * ∫⁻ x, A x * B x ^ 2 ∂m := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

/-- The pointwise estimate on `𝔻` (TT:1523, first two lines). -/
theorem r24_pointwise {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) {ζ : ℂ} (hζ : ζ ∈ unitDisc) :
    (‖AInf.toFun (D0BersR μ ν) ζ‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho ζ)⁻¹ ≤
      ENNReal.ofReal (144 / π * ‖deriv (fsans μ) ζ‖ ^ 2) *
        ∫⁻ x in unitDiscExterior, ENNReal.ofReal (‖deriv (gsans μ) x‖ ^ 2) *
          (‖gsans μ x - fsans μ ζ‖₊ : ℝ≥0∞)⁻¹ ^ 4 * (‖ν x‖₊ : ℝ≥0∞) ^ 2 := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hf := S2C.s2c_conf_f hμ
  have hg := S2C.s2c_conf_g hμ
  have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have hs : (0 : ℝ) < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hφ' : deriv (fsans μ) ζ ≠ 0 := kb_deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hζ
  set z := fsans μ ζ with hz
  set G := Function.invFunOn (gsans μ) unitDiscExterior with hGdef
  let k : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (‖deriv (gsans μ) x‖ ^ 2) * (‖gsans μ x - z‖₊ : ℝ≥0∞)⁻¹ ^ 4
  let B : ℂ → ℝ≥0∞ := fun x => (‖ν x‖₊ : ℝ≥0∞)
  -- measurability on `𝔻*`
  have hgm : AEMeasurable (gsans μ) (volume.restrict unitDiscExterior) :=
    (hg.1.continuousOn.aestronglyMeasurable hEo.measurableSet).aemeasurable
  have hg'm : AEMeasurable (deriv (gsans μ)) (volume.restrict unitDiscExterior) :=
    ((hg.1.deriv hEo).continuousOn.aestronglyMeasurable hEo.measurableSet).aemeasurable
  have hkm : AEMeasurable k (volume.restrict unitDiscExterior) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable (hg'm.norm.pow_const 2)).mul
      (((hgm.sub_const z).nnnorm.coe_nnreal_ennreal.inv).pow_const 4)
  have hBm : AEMeasurable B (volume.restrict unitDiscExterior) :=
    (Lp.aestronglyMeasurable ν).aemeasurable.nnnorm.coe_nnreal_ennreal
  -- the integral over `Ω*` transported to `𝔻*`
  have hP : ‖∫ u in gsans μ '' unitDiscExterior, ν (G u) * (conj (deriv G u) / deriv G u) / (u - z) ^ 4‖ₑ ≤
      ∫⁻ x in unitDiscExterior, k x * B x := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ u in gsans μ '' unitDiscExterior, ‖ν (G u) * (conj (deriv G u) / deriv G u) / (u - z) ^ 4‖ₑ
        ≤ ∫⁻ u in gsans μ '' unitDiscExterior, ‖ν (G u)‖ₑ * (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 :=
          lintegral_mono fun u => r24_integrand_le _ _ 0 u z
      _ = ∫⁻ x in unitDiscExterior, ENNReal.ofReal (‖deriv (gsans μ) x‖ ^ 2) *
            (‖ν (G (gsans μ x))‖ₑ * (‖gsans μ x - z‖₊ : ℝ≥0∞)⁻¹ ^ 4) :=
          r24_conformal_lintegral hEo hg.1 hg.2.1 _
      _ = ∫⁻ x in unitDiscExterior, k x * B x := by
          apply setLIntegral_congr_fun hEo.measurableSet
          intro x hx
          simp only [k, B]
          have hGx : G (gsans μ x) = x := hg.2.1.leftInvOn_invFunOn hx
          rw [hGx, enorm_eq_nnnorm]
          ring
  -- `∫ k = ∫_{Ω*} |u - z|⁻⁴ ≤ 4π ρ(ζ)/|𝖿'(ζ)|²`
  have hQ : ∫⁻ x in unitDiscExterior, k x ≤ ENNReal.ofReal (4 * π * (rho ζ * ‖deriv (fsans μ) ζ‖⁻¹ ^ 2)) := by
    have h := r24_interior_kernel_bound hμ ⟨ζ, hζ, rfl⟩
    rw [r24_conformal_lintegral hEo hg.1 hg.2.1] at h
    have hF : Function.invFunOn (fsans μ) unitDisc (fsans μ ζ) = ζ := hf.2.1.leftInvOn_invFunOn hζ
    have hF' := t1_deriv_invFunOn_mul (U := unitDisc) isOpen_ball hf hζ
    have hFi : ‖deriv (Function.invFunOn (fsans μ) unitDisc) (fsans μ ζ)‖ = ‖deriv (fsans μ) ζ‖⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← norm_mul, hF', norm_one])
    rw [hF, hFi] at h
    exact h
  have hCS := r24_cauchy_schwarz (volume.restrict unitDiscExterior) hkm hBm
  -- assemble
  rw [r24_phi_formula hμ ν hζ]
  have hnorm : (‖-(6 / π) * deriv (fsans μ) ζ ^ 2 *
      ∫ u in gsans μ '' unitDiscExterior, ν (G u) * (conj (deriv G u) / deriv G u) / (u - z) ^ 4‖₊ :
        ℝ≥0∞) ≤ ENNReal.ofReal (6 / π * ‖deriv (fsans μ) ζ‖ ^ 2) * ∫⁻ x in unitDiscExterior, k x * B x := by
    have e : ‖(-(6 / π) * deriv (fsans μ) ζ ^ 2 : ℂ)‖ = 6 / π * ‖deriv (fsans μ) ζ‖ ^ 2 := by
      rw [norm_mul, norm_neg, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    rw [← enorm_eq_nnnorm, enorm_mul, ← ofReal_norm (-(6 / π) * deriv (fsans μ) ζ ^ 2 : ℂ), e]
    exact mul_le_mul' le_rfl hP
  set P := ∫⁻ x in unitDiscExterior, k x * B x
  set Q := ∫⁻ x in unitDiscExterior, k x
  set S := ∫⁻ x in unitDiscExterior, k x * B x ^ 2
  have hS : S = ∫⁻ x in unitDiscExterior, ENNReal.ofReal (‖deriv (gsans μ) x‖ ^ 2) *
      (‖gsans μ x - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 * (‖ν x‖₊ : ℝ≥0∞) ^ 2 := rfl
  have hd0 : 0 < ‖deriv (fsans μ) ζ‖ := norm_pos_iff.mpr hφ'
  have hρ : 0 < rho ζ := by unfold rho; positivity
  calc _ ≤ (ENNReal.ofReal (6 / π * ‖deriv (fsans μ) ζ‖ ^ 2) * P) ^ 2 * ENNReal.ofReal (rho ζ)⁻¹ :=
        mul_le_mul' (pow_le_pow_left₀ zero_le hnorm 2) le_rfl
    _ = ENNReal.ofReal (6 / π * ‖deriv (fsans μ) ζ‖ ^ 2) ^ 2 * P ^ 2 * ENNReal.ofReal (rho ζ)⁻¹ := by ring
    _ ≤ ENNReal.ofReal (6 / π * ‖deriv (fsans μ) ζ‖ ^ 2) ^ 2 * (Q * S) * ENNReal.ofReal (rho ζ)⁻¹ :=
        mul_le_mul' (mul_le_mul' le_rfl hCS) le_rfl
    _ ≤ ENNReal.ofReal (6 / π * ‖deriv (fsans μ) ζ‖ ^ 2) ^ 2 *
          (ENNReal.ofReal (4 * π * (rho ζ * ‖deriv (fsans μ) ζ‖⁻¹ ^ 2)) * S) * ENNReal.ofReal (rho ζ)⁻¹ :=
        mul_le_mul' (mul_le_mul' le_rfl (mul_le_mul' hQ le_rfl)) le_rfl
    _ = ENNReal.ofReal ((6 / π * ‖deriv (fsans μ) ζ‖ ^ 2) ^ 2 *
          (4 * π * (rho ζ * ‖deriv (fsans μ) ζ‖⁻¹ ^ 2)) * (rho ζ)⁻¹) * S := by
        conv_rhs => rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by positivity)]
        ring
    _ = ENNReal.ofReal (144 / π * ‖deriv (fsans μ) ζ‖ ^ 2) * S := by
        congr 2
        field_simp
        ring

/-- The inner integral over `𝔻` (TT:1523, third line). -/
theorem r24_inner_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {x : ℂ} (hx : x ∈ unitDiscExterior) :
    ∫⁻ ζ in unitDisc, ENNReal.ofReal (‖deriv (fsans μ) ζ‖ ^ 2) * (‖gsans μ x - fsans μ ζ‖₊ : ℝ≥0∞)⁻¹ ^ 4 ≤
      ENNReal.ofReal (4 * π * (rho x * ‖deriv (gsans μ) x‖⁻¹ ^ 2)) := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hf := S2C.s2c_conf_f hμ
  have hg := S2C.s2c_conf_g hμ
  have h := r24_exterior_kernel_bound hμ ⟨x, hx, rfl⟩
  rw [r24_conformal_lintegral (U := unitDisc) isOpen_ball hf.1 hf.2.1] at h
  have hG : Function.invFunOn (gsans μ) unitDiscExterior (gsans μ x) = x := hg.2.1.leftInvOn_invFunOn hx
  have hG' := t1_deriv_invFunOn_mul hEo hg hx
  have hGi : ‖deriv (Function.invFunOn (gsans μ) unitDiscExterior) (gsans μ x)‖ = ‖deriv (gsans μ) x‖⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← norm_mul, hG', norm_one])
  rw [hG, hGi] at h
  exact h

/-- **Remark 2.4** (TT:1594–1600). `‖D₀(β ∘ Φ ∘ R_μ)(ν)‖₂ ≤ 24 ‖ν‖₂`. -/
theorem r24_remark_2_4 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    normA2 unitDisc (AInf.toFun (D0BersR μ ν)) ≤ 24 * normL2 unitDiscExterior ν := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hf := S2C.s2c_conf_f hμ
  have hg := S2C.s2c_conf_g hμ
  let F : ℂ → ℂ → ℝ≥0∞ := fun ζ x => ENNReal.ofReal (‖deriv (fsans μ) ζ‖ ^ 2) *
    (ENNReal.ofReal (‖deriv (gsans μ) x‖ ^ 2) * (‖gsans μ x - fsans μ ζ‖₊ : ℝ≥0∞)⁻¹ ^ 4 * (‖ν x‖₊ : ℝ≥0∞) ^ 2)
  -- joint measurability
  have hfm : AEMeasurable (fsans μ) (volume.restrict unitDisc) :=
    (hf.1.continuousOn.aestronglyMeasurable isOpen_ball.measurableSet).aemeasurable
  have hf'm : AEMeasurable (deriv (fsans μ)) (volume.restrict unitDisc) :=
    ((hf.1.deriv isOpen_ball).continuousOn.aestronglyMeasurable isOpen_ball.measurableSet).aemeasurable
  have hgm : AEMeasurable (gsans μ) (volume.restrict unitDiscExterior) :=
    (hg.1.continuousOn.aestronglyMeasurable hEo.measurableSet).aemeasurable
  have hg'm : AEMeasurable (deriv (gsans μ)) (volume.restrict unitDiscExterior) :=
    ((hg.1.deriv hEo).continuousOn.aestronglyMeasurable hEo.measurableSet).aemeasurable
  have hνm : AEMeasurable (fun x => (‖ν x‖₊ : ℝ≥0∞)) (volume.restrict unitDiscExterior) :=
    (Lp.aestronglyMeasurable ν).aemeasurable.nnnorm.coe_nnreal_ennreal
  have hFm : AEMeasurable (Function.uncurry F)
      ((volume.restrict unitDisc).prod (volume.restrict unitDiscExterior)) := by
    have h1 := (ENNReal.measurable_ofReal.comp_aemeasurable (hf'm.norm.pow_const 2)).comp_fst
      (ν := volume.restrict unitDiscExterior)
    have h2 := (ENNReal.measurable_ofReal.comp_aemeasurable (hg'm.norm.pow_const 2)).comp_snd
      (μ := volume.restrict unitDisc)
    have h3 : AEMeasurable (fun p : ℂ × ℂ => gsans μ p.2 - fsans μ p.1)
        ((volume.restrict unitDisc).prod (volume.restrict unitDiscExterior)) :=
      (hgm.comp_snd).sub (hfm.comp_fst)
    have h4 := (h3.nnnorm.coe_nnreal_ennreal.inv).pow_const 4
    have h5 := (hνm.comp_snd (μ := volume.restrict unitDisc)).pow_const 2
    exact h1.mul ((h2.mul h4).mul h5)
  have hmain : normA2 unitDisc (AInf.toFun (D0BersR μ ν)) ^ 2 ≤ (24 * normL2 unitDiscExterior ν) ^ 2 := by
    rw [r24_normA2_sq, mul_pow, r24_normL2_sq]
    calc ∫⁻ ζ in unitDisc, (‖AInf.toFun (D0BersR μ ν) ζ‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho ζ)⁻¹
        ≤ ∫⁻ ζ in unitDisc, ENNReal.ofReal (144 / π) * ∫⁻ x in unitDiscExterior, F ζ x := by
          apply setLIntegral_mono' isOpen_ball.measurableSet
          intro ζ hζ
          refine (r24_pointwise hμ ν hζ).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (144 / π) * ∫⁻ x in unitDiscExterior, ∫⁻ ζ in unitDisc, F ζ x := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hFm]
      _ ≤ ENNReal.ofReal (144 / π) * ∫⁻ x in unitDiscExterior,
            ENNReal.ofReal (4 * π) * ((‖ν x‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho x)) := by
          gcongr ENNReal.ofReal (144 / π) * ?_
          apply setLIntegral_mono' hEo.measurableSet
          intro x hx
          have hg' : deriv (gsans μ) x ≠ 0 := kb_deriv_ne_zero_of_injOn hEo hg.1 hg.2.1 hx
          have hg0 : 0 < ‖deriv (gsans μ) x‖ := norm_pos_iff.mpr hg'
          have hρ : 0 < rho x := by
            have hx1 : 1 < ‖x‖ := hx
            have : (1 - ‖x‖ ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 (by nlinarith)
            unfold rho; positivity
          calc ∫⁻ ζ in unitDisc, F ζ x
              = ENNReal.ofReal (‖deriv (gsans μ) x‖ ^ 2) * (‖ν x‖₊ : ℝ≥0∞) ^ 2 *
                  ∫⁻ ζ in unitDisc, ENNReal.ofReal (‖deriv (fsans μ) ζ‖ ^ 2) *
                    (‖gsans μ x - fsans μ ζ‖₊ : ℝ≥0∞)⁻¹ ^ 4 := by
                rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
                  (ENNReal.pow_ne_top ENNReal.coe_ne_top))]
                congr 1; funext ζ; simp only [F]; ring
            _ ≤ ENNReal.ofReal (‖deriv (gsans μ) x‖ ^ 2) * (‖ν x‖₊ : ℝ≥0∞) ^ 2 *
                  ENNReal.ofReal (4 * π * (rho x * ‖deriv (gsans μ) x‖⁻¹ ^ 2)) := by
                gcongr; exact r24_inner_bound hμ hx
            _ = ENNReal.ofReal (4 * π) * ((‖ν x‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho x)) := by
                rw [mul_comm (ENNReal.ofReal _) _, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
                  show ‖deriv (gsans μ) x‖ ^ 2 * (4 * π * (rho x * ‖deriv (gsans μ) x‖⁻¹ ^ 2)) =
                    4 * π * rho x by field_simp,
                  ENNReal.ofReal_mul (by positivity)]
                ring
      _ = ((24 : ℝ≥0∞) ^ 2) * ∫⁻ x in unitDiscExterior, (‖ν x‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho x) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show (144 / π * (4 * π) : ℝ) = 576 by field_simp; norm_num]
          norm_num
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hmain

/-- **Remark 2.4** (TT:1594–1600). `D₀(β ∘ R_[μ]) = D₀(β ∘ Φ ∘ R_μ)` extends to a bounded operator on
`L²(𝔻*, ρ d²z)`: `‖D₀(β ∘ Φ ∘ R_μ)(ν)‖₂ ≤ 24 ‖ν‖₂` for all `ν` (bounded, with `‖ν‖₂ < ∞`) and
`μ ∈ L∞(𝔻*)₁`. -/
theorem remark_2_4 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    normA2 unitDisc (AInf.toFun (D0BersR μ ν)) ≤ 24 * normL2 unitDiscExterior ν :=
  r24_remark_2_4 hμ ν

end TakhtajanTeo
