import TakhtajanTeo.Ch1.S2_HilbertManifold
import TakhtajanTeo.Ch1.QCVariationBergman

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- `ℝ≥0∞` change of variables through an injective holomorphic map. -/
theorem d2_lintegral_image {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hi : InjOn f U) (g : ℂ → ℝ≥0∞) :
    ∫⁻ w in f '' U, g w = ∫⁻ z in U, ENNReal.ofReal (‖deriv f z‖ ^ 2) * g (f z) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU.measurableSet
    (fun z hz => ((hd.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hi g]
  refine setLIntegral_congr_fun hU.measurableSet fun z _ => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _)]

/-- Reflection `z ↦ 1/z̄` carries `𝔻*` onto `𝔻 \ {0}` with Jacobian `|z|⁻⁴`. -/
theorem d2_refl_lintegral (G : ℂ → ℝ≥0∞) :
    ∫⁻ w in unitDisc \ {0}, G w =
      ∫⁻ z in unitDiscExterior, ENNReal.ofReal ((‖z‖ ^ 4)⁻¹) * G (refl z) := by
  have hemb : MeasurableEmbedding (⇑Complex.conjLIE) :=
    Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hpre : (⇑Complex.conjLIE) ⁻¹' (unitDisc \ {0}) = unitDisc \ {0} := by
    ext w
    simp [unitDisc]
  have hA : ∫⁻ w in unitDisc \ {0}, G w = ∫⁻ w in unitDisc \ {0}, G (conj w) := by
    have h := (Complex.conjLIE.measurePreserving).setLIntegral_comp_preimage_emb hemb G
      (unitDisc \ {0})
    rw [hpre] at h
    simpa only [Complex.conjLIE_apply] using h.symm
  rw [hA, ← resolvent_inv_exterior_image]
  rw [d2_lintegral_image resolvent_exterior_isOpen
    (fun z hz => differentiableWithinAt_inv (resolvent_exterior_ne_zero hz) _)
    (fun a _ b _ h => inv_injective h) (fun w => G (conj w))]
  refine setLIntegral_congr_fun resolvent_exterior_isOpen.measurableSet fun z hz => ?_
  have hz0 := resolvent_exterior_ne_zero hz
  have hder : ‖deriv (fun z : ℂ => z⁻¹) z‖ ^ 2 = (‖z‖ ^ 4)⁻¹ := by
    rw [deriv_inv']
    simp only [norm_neg, norm_inv, norm_pow]
    ring
  rw [hder]
  simp only [refl, map_inv₀]

/-- Real coefficient size of an `A∞(𝔻)` element. -/
theorem d2_AInf_norm {φ : AInf unitDisc} {w : ℂ} (hw : w ∈ unitDisc) :
    ‖φ.1 ⟨w, hw⟩‖ = (1 - ‖w‖ ^ 2) ^ 2 * ‖AInf.toFun φ w‖ := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hpos : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hcast : (1 - (‖w‖ : ℂ) ^ 2) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have h : AInf.toFun φ w = φ.1 ⟨w, hw⟩ / (1 - (‖w‖ : ℂ) ^ 2) ^ 2 := by
    simp only [AInf.toFun, unweight, dif_pos hw]
  rw [h, norm_div, norm_pow, hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  field_simp

theorem d2_nnnorm_sq (x : ℂ) : (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

/-- The weighted `L²` mass of the explicit `Λ` formula equals four times the weighted `A₂` mass. -/
theorem d2_lambda_mass (φ : AInf unitDisc) :
    ∫⁻ z in unitDiscExterior, (‖-(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 * AInf.toFun φ (refl z) / conj z ^ 4‖₊ : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (rho z) =
      4 * ∫⁻ w in unitDisc, (‖AInf.toFun φ w‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹ := by
  have hnull : unitDisc \ {0} =ᵐ[volume] unitDisc :=
    sdiff_null_ae_eq_self (measure_singleton 0)
  rw [← setLIntegral_congr hnull, ← lintegral_const_mul' _ _ (by norm_num)]
  rw [d2_refl_lintegral]
  refine setLIntegral_congr_fun resolvent_exterior_isOpen.measurableSet fun z hz => ?_
  have hz0 := resolvent_exterior_ne_zero hz
  have hn : 1 < ‖z‖ := hz
  have hzD : refl z ∈ unitDisc := (refl_mem_disc_iff hz0).mpr hz
  have hk := Lambda_kernel_norm φ hz hzD
  have hψ := d2_AInf_norm (φ := φ) hzD
  rw [norm_refl] at hψ
  have h1 : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith
  have h2 : (1 : ℝ) - (‖z‖⁻¹) ^ 2 ≠ 0 := by
    have : (‖z‖⁻¹) < 1 := inv_lt_one_of_one_lt₀ hn
    have : 0 < ‖z‖⁻¹ := inv_pos.mpr (by linarith)
    nlinarith
  have hn0 : ‖z‖ ≠ 0 := by positivity
  have hreal : (1 / 2 * ((1 - ‖z‖⁻¹ ^ 2) ^ 2 * ‖AInf.toFun φ (refl z)‖)) ^ 2 * rho z =
      (‖z‖ ^ 4)⁻¹ * (4 * (‖AInf.toFun φ (refl z)‖ ^ 2 * (rho (refl z))⁻¹)) := by
    simp only [rho, norm_refl]
    field_simp
    ring
  rw [d2_nnnorm_sq, d2_nnnorm_sq, hk, hψ]
  calc ENNReal.ofReal ((1 / 2 * ((1 - ‖z‖⁻¹ ^ 2) ^ 2 * ‖AInf.toFun φ (refl z)‖)) ^ 2) *
        ENNReal.ofReal (rho z)
      = ENNReal.ofReal ((1 / 2 * ((1 - ‖z‖⁻¹ ^ 2) ^ 2 * ‖AInf.toFun φ (refl z)‖)) ^ 2 * rho z) :=
        (ENNReal.ofReal_mul (sq_nonneg _)).symm
    _ = ENNReal.ofReal ((‖z‖ ^ 4)⁻¹ * (4 * (‖AInf.toFun φ (refl z)‖ ^ 2 * (rho (refl z))⁻¹))) := by
        rw [hreal]
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (sq_nonneg _)]
        simp

/-- Bounded harmonic `L²` differentials are essentially bounded (TT:1401–1410). -/
theorem d2_harmonicL2_memLp {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    MemLp μ ∞ (volume.restrict unitDiscExterior) := by
  obtain ⟨φ, hφ, hrep, hfinite⟩ := hμ
  have hcircle : ∀ z ∈ unitDiscExterior, ‖z‖ ≠ 1 := fun z hz => ne_of_gt hz
  have hnorm := normA2_eq_normL2_of_harmonic resolvent_exterior_isOpen.measurableSet hcircle hrep
  have hA2 : φ ∈ A2fun unitDiscExterior := by
    refine ⟨hφ, ?_⟩
    rw [hnorm]
    exact hfinite
  let N : ℝ := (normL2 unitDiscExterior μ).toReal
  have hpoint (z : ℂ) (hz : z ∈ unitDiscExterior) :
      (1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖ ≤ Real.sqrt (12 / π) * N := by
    have hb := lemma_2_1 (D := unitDiscExterior) (Or.inr rfl) hA2 z hz
    rw [hnorm] at hb
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg)).mp
    simpa only [ENNReal.ofReal_mul (Real.sqrt_nonneg _), N, ENNReal.ofReal_toReal hfinite.ne] using hb
  let K : ℝ := (Real.sqrt (12 / π) / 4) * N
  have hμbound (z : ℂ) (hz : z ∈ unitDiscExterior) : ‖μ z‖ ≤ K := by
    have hr := rho_pos_of_norm_ne_one (hcircle z hz)
    have hformula : ‖μ z‖ = ((1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖) / 4 := by
      rw [hrep z hz]
      simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_conj]
      simp only [rho, inv_div]
      ring
    rw [hformula]
    calc
      _ ≤ (Real.sqrt (12 / π) * N) / 4 := div_le_div_of_nonneg_right (hpoint z hz) (by norm_num)
      _ = K := by dsimp [K]; ring
  have hwc : Continuous (fun z : ℂ => (rho z : ℂ)⁻¹) := by
    simp only [← Complex.ofReal_inv, rho, inv_div]
    fun_prop
  have hφc := hφ.continuousOn
  have hc : ContinuousOn (fun z => (rho z : ℂ)⁻¹ * conj (φ z)) unitDiscExterior := by
    simpa only [Pi.mul_def, Function.comp_def] using
      hwc.continuousOn.mul (Complex.continuous_conj.comp_continuousOn hφc)
  have hμc : ContinuousOn μ unitDiscExterior := hc.congr (by intro z hz; exact hrep z hz)
  have hμae : AEStronglyMeasurable μ (volume.restrict unitDiscExterior) :=
    hμc.aestronglyMeasurable resolvent_exterior_isOpen.measurableSet
  have hμboundae : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖μ z‖ ≤ K := by
    filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz
    exact hμbound z hz
  exact memLp_top_of_bound hμae K hμboundae

/-- (TT:1410) Under `D₀β`, `H^{-1,1}(𝔻*) ≅ A₂(𝔻)`. -/
theorem d2_D0bers_harmonicL2 :
    (∀ μ ∈ harmonicL2 unitDiscExterior, AInf.toFun (fderiv ℂ bersPhi 0 (toLinf μ)) ∈ A2fun unitDisc) ∧
      ∀ φ ∈ A2fun unitDisc, ∃ μ ∈ harmonicL2 unitDiscExterior,
        ∀ z ∈ unitDisc, AInf.toFun (fderiv ℂ bersPhi 0 (toLinf μ)) z = φ z := by
  constructor
  · intro μ hμ
    obtain ⟨C, hC⟩ := harmonicL2_subset_harmonic
    have hm : toLinf μ ∈ harmonicBeltrami := (hC μ hμ).1
    have hmem := d2_harmonicL2_memLp hμ
    have hto : (toLinf μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] μ := by
      simp only [toLinf, dite_eq_left hmem]
      exact hmem.coeFn_toLp
    set φ : AInf unitDisc := fderiv ℂ bersPhi 0 (toLinf μ) with hφdef
    have h3 : Lambda φ = toLinf μ := QCV.qcv_lambda_inverse_D0bers.2.2 (toLinf μ) hm
    have hae : μ =ᵐ[volume.restrict unitDiscExterior]
        (fun z : ℂ => -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 * AInf.toFun φ (refl z) / conj z ^ 4) := by
      have h4 := Lambda_coe_ae φ
      rw [h3] at h4
      exact hto.symm.trans h4
    have hX : ∫⁻ z in unitDiscExterior, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) =
        4 * ∫⁻ w in unitDisc, (‖AInf.toFun φ w‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹ := by
      rw [← d2_lambda_mass φ]
      apply lintegral_congr_ae
      filter_upwards [hae] with z hz
      rw [hz]
    have hfin : normL2 unitDiscExterior μ < ⊤ := by
      obtain ⟨_, _, _, h⟩ := hμ
      exact h
    have hXfin : (∫⁻ z in unitDiscExterior, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) ≠ ⊤ := by
      intro htop
      have : normL2 unitDiscExterior μ = ⊤ := by
        unfold normL2
        rw [htop]
        exact ENNReal.top_rpow_of_pos (by norm_num)
      exact absurd hfin (by rw [this]; exact lt_irrefl _)
    rw [hX] at hXfin
    have hYfin : (∫⁻ w in unitDisc, (‖AInf.toFun φ w‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹) ≠ ⊤ := by
      intro htop
      rw [htop] at hXfin
      exact hXfin (by simp)
    refine ⟨φ.property, ?_⟩
    unfold normA2
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hYfin
  · intro φ hφ
    have hcircle : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun z hz => (mem_ball_zero_iff.mp hz).ne
    have hspec := toA2_spec isOpen_ball hcircle hφ
    set φ' : AInf unitDisc := A2toAInf (toA2 unitDisc φ) with hφ'
    have hval : ∀ z ∈ unitDisc, AInf.toFun φ' z = φ z := by
      intro z hz
      rw [hφ', (A2toAInf_bounded.2 _).2 z hz]
      exact hspec hz
    have hnormφ : ∫⁻ w in unitDisc, (‖AInf.toFun φ' w‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹ =
        ∫⁻ w in unitDisc, (‖φ w‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹ := by
      refine setLIntegral_congr_fun measurableSet_ball fun w hw => ?_
      rw [hval w hw]
    have hAfin : (∫⁻ w in unitDisc, (‖φ w‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹) ≠ ⊤ := by
      intro htop
      have : normA2 unitDisc φ = ⊤ := by
        unfold normA2
        rw [htop]
        exact ENNReal.top_rpow_of_pos (by norm_num)
      exact absurd hφ.2 (by rw [this]; exact lt_irrefl _)
    have hdiffAll : ∀ z ∈ unitDiscExterior, DifferentiableAt ℂ
        (fun z : ℂ => -2 * conj (AInf.toFun φ' (refl z)) / z ^ 4) z := by
      intro z hz
      have hz0 := resolvent_exterior_ne_zero hz
      have hzD : refl z ∈ unitDisc := (refl_mem_disc_iff hz0).mpr hz
      have hdiff : DifferentiableAt ℂ (AInf.toFun φ') (refl z) :=
        φ'.property.differentiableAt (isOpen_ball.mem_nhds hzD)
      have hc : DifferentiableAt ℂ (conj ∘ (AInf.toFun φ') ∘ conj) z⁻¹ := by
        apply differentiableAt_conj_conj_iff.mpr
        simpa [refl, map_inv₀] using hdiff
      have hinv : DifferentiableAt ℂ (fun u : ℂ => u⁻¹) z := (hasDerivAt_inv hz0).differentiableAt
      have heq : (fun z : ℂ => -2 * conj (AInf.toFun φ' (refl z)) / z ^ 4) =
          fun z : ℂ => -2 * ((conj ∘ (AInf.toFun φ') ∘ conj) ((fun u : ℂ => u⁻¹) z)) / z ^ 4 := by
        funext z
        simp [refl, map_inv₀]
      rw [heq]
      exact ((hc.comp z hinv).const_mul (-2)).div (differentiableAt_pow 4) (pow_ne_zero 4 hz0)
    refine ⟨fun z : ℂ => -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 * AInf.toFun φ' (refl z) / conj z ^ 4, ?_, ?_⟩
    · refine ⟨fun z => -2 * conj (AInf.toFun φ' (refl z)) / z ^ 4,
        fun z hz => (hdiffAll z hz).differentiableWithinAt, ?_, ?_⟩
      · intro z hz
        beta_reduce
        have hz0 := resolvent_exterior_ne_zero hz
        have hn : 1 < ‖z‖ := hz
        have hzc : conj z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz0
        have h1 : (1 - (‖z‖ : ℂ) ^ 2) ≠ 0 := by
          have : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith
          exact_mod_cast this
        have hr : (rho z : ℂ)⁻¹ = (1 - (‖z‖ : ℂ) ^ 2) ^ 2 / 4 := by
          simp only [rho]
          push_cast
          rw [inv_div]
        rw [hr]
        simp only [map_div₀, map_mul, map_pow, Complex.conj_conj, map_neg, map_ofNat]
        field_simp
        ring
      · unfold normL2
        rw [d2_lambda_mass φ', hnormφ]
        exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top (by simp) hAfin)
    · intro z hz
      have hL : toLinf (fun z : ℂ => -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 * AInf.toFun φ' (refl z) / conj z ^ 4) =
          Lambda φ' := rfl
      rw [hL, QCV.qcv_D0_Lambda]
      exact hval z hz

/-! ### Original relocated from `S2_HilbertManifold` (2026-10-25) -/

/-- (TT:1410) Under `D₀β`, `H^{-1,1}(𝔻*) ≅ A₂(𝔻)`:
- for `μ ∈ H^{-1,1}(𝔻*)`, `D₀β(μ) ∈ A₂(𝔻)`;
- every `φ ∈ A₂(𝔻)` is `D₀β(μ)` for some `μ ∈ H^{-1,1}(𝔻*)`. -/
theorem D0bers_harmonicL2 :
    (∀ μ ∈ harmonicL2 unitDiscExterior, AInf.toFun (fderiv ℂ bersPhi 0 (toLinf μ)) ∈ A2fun unitDisc) ∧
      ∀ φ ∈ A2fun unitDisc, ∃ μ ∈ harmonicL2 unitDiscExterior,
        ∀ z ∈ unitDisc, AInf.toFun (fderiv ℂ bersPhi 0 (toLinf μ)) z = φ z :=
  d2_D0bers_harmonicL2

end TakhtajanTeo
