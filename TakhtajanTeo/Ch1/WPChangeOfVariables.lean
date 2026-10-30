import TakhtajanTeo.Ch1.S7_Curvature
import TakhtajanTeo.Ch1.BeltramiGroup
import TakhtajanTeo.Ch1.BeltramiCompose
import TakhtajanTeo.Ch1.QCVariationPlane
import TakhtajanTeo.Ch1.HarmonicProjCompleted
import TakhtajanTeo.Ch1.QuasidiskKernel

/-!
# (7.7) for every `κ` in the ball: change of variables through `w_κ`

Proof of `eq_7_7` (S7), stated here as `x5_eq_7_7` (statement byte-identical), for all `κ ∈ L∞(𝔻*)₁`:
* a lintegral change of variables for the symmetric quasiconformal map `w_κ` on `𝔻*` (`wpcv_lcov`);
* pseudo-hyperbolic balls `wpB` in `𝔻*` (area, mean value for harmonic Beltrami differentials, Mori's
  quasi-isometry `wpcv_qi`), which give `R(μ, κ) ∈ L²(𝔻*, ρ)` (`x5_Rnm_L2`);
* `P² = P` (`harmonicProj_orthogonal`) for the second equation.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo
namespace WPCV

open LiZhongQC QCV

-- `wpcv_conformal_l` merged into `r24_conformal_lintegral` (`Ch1/QuasidiskKernel.lean`, 2026-10-26).

/-- Möbius change of variables onto the exterior disc. -/
theorem wpcv_mobius_l {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) (G : ℂ → ℝ≥0∞) :
    (∫⁻ u in unitDiscExterior, G u) =
      ∫⁻ v in {v : ℂ | c * v + d ≠ 0 ∧ mobiusFn a b c d v ∈ unitDiscExterior},
        ENNReal.ofReal (‖(a * d - b * c) / (c * v + d) ^ 2‖ ^ 2) * G (mobiusFn a b c d v) := by
  set S : Set ℂ := {v : ℂ | c * v + d ≠ 0 ∧ mobiusFn a b c d v ∈ unitDiscExterior} with hS
  have hP : IsOpen {v : ℂ | c * v + d ≠ 0} := by
    apply isOpen_ne_fun (by fun_prop) (by fun_prop)
  have hMc : ContinuousOn (mobiusFn a b c d) {v : ℂ | c * v + d ≠ 0} := by
    intro v hv
    exact (bc_mobiusFn_hasDerivAt (z := v) hv).continuousAt.continuousWithinAt
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hSo : IsOpen S := by
    have := hMc.isOpen_inter_preimage hP hE
    convert this using 1
    ext v; simp [hS, and_comm]
  have hPS : ∀ v ∈ S, c * v + d ≠ 0 := fun v hv => hv.1
  have hdiff : DifferentiableOn ℂ (mobiusFn a b c d) S := fun v hv =>
    (bc_mobiusFn_hasDerivAt (hPS v hv)).differentiableAt.differentiableWithinAt
  have hinj : InjOn (mobiusFn a b c d) S := bc_mobiusFn_injOn hdet hPS
  have hder : ∀ v ∈ S, deriv (mobiusFn a b c d) v = (a * d - b * c) / (c * v + d) ^ 2 :=
    fun v hv => (bc_mobiusFn_hasDerivAt (hPS v hv)).deriv
  -- the image is the exterior disc up to a null set
  have himg : mobiusFn a b c d '' S ⊆ unitDiscExterior := by
    rintro _ ⟨v, hv, rfl⟩; exact hv.2
  have hnull : (volume : Measure ℂ) (unitDiscExterior \ mobiusFn a b c d '' S) = 0 := by
    have hsub : unitDiscExterior \ mobiusFn a b c d '' S ⊆ {u : ℂ | c * u = a} := by
      intro u hu
      by_contra hcu
      simp only [mem_setOf_eq] at hcu
      apply hu.2
      have hne : a - c * u ≠ 0 := fun h => hcu (by linear_combination -h)
      have hne' : a - u * c ≠ 0 := by rwa [mul_comm u c]
      refine ⟨(d * u - b) / (a - c * u), ⟨?_, ?_⟩, ?_⟩
      · have : c * ((d * u - b) / (a - c * u)) + d = (a * d - b * c) / (a - c * u) := by
          field_simp; ring
        rw [this]; exact div_ne_zero hdet hne
      · have h1 : c * ((d * u - b) / (a - c * u)) + d = (a * d - b * c) / (a - c * u) := by
          field_simp; ring
        have h2 : mobiusFn a b c d ((d * u - b) / (a - c * u)) = u := by
          unfold mobiusFn
          rw [h1]
          field_simp
          ring
        rw [h2]; exact hu.1
      · unfold mobiusFn
        have h1 : c * ((d * u - b) / (a - c * u)) + d = (a * d - b * c) / (a - c * u) := by
          field_simp; ring
        rw [h1]; field_simp; ring
    refine measure_mono_null hsub ?_
    by_cases hc : c = 0
    · have ha : a ≠ 0 := by
        intro h; apply hdet; rw [hc, h]; ring
      have : {u : ℂ | c * u = a} = ∅ := by
        ext u; simp [hc, Ne.symm ha]
      rw [this]; exact measure_empty
    · have : {u : ℂ | c * u = a} = {a / c} := by
        ext u; simp only [mem_setOf_eq, mem_singleton_iff]
        constructor
        · intro h; field_simp; linear_combination h
        · intro h; rw [h]; field_simp
      rw [this]; exact measure_singleton _
  have hae : (mobiusFn a b c d '' S : Set ℂ) =ᵐ[volume] unitDiscExterior := by
    refine (ae_eq_set.mpr ⟨?_, ?_⟩)
    · rw [diff_eq_empty.mpr himg]; exact measure_empty
    · exact hnull
  have h1 := r24_conformal_lintegral hSo hdiff hinj G
  rw [setLIntegral_congr hae.symm]
  rw [h1]
  apply setLIntegral_congr_fun hSo.measurableSet
  intro v hv
  dsimp only
  rw [hder v hv]

theorem wpcv_mem_iff {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {W : ℂ → ℂ} {a b c d : ℂ}
    (hcoe : ∀ z, c * W z + d ≠ 0 → wAS κ (z : ExtPlane) = ((mobiusFn a b c d (W z) : ℂ) : ExtPlane))
    {z : ℂ} (hz : c * W z + d ≠ 0) :
    mobiusFn a b c d (W z) ∈ unitDiscExterior ↔ z ∈ unitDiscExterior := by
  have h := hcoe z hz
  simp only [unitDiscExterior, mem_setOf_eq]
  constructor
  · intro hM
    by_contra hz1
    rcases lt_or_eq_of_le (not_lt.mp hz1) with hlt | heq
    · obtain ⟨u, hu, he⟩ := wAS_maps_disc hκ hlt
      rw [h] at he
      have := OnePoint.coe_injective he
      rw [this] at hM; linarith
    · obtain ⟨u, hu, he⟩ := wAS_maps_circle hκ heq
      rw [h] at he
      have := OnePoint.coe_injective he
      rw [this] at hM; linarith
  · intro hz1
    rcases wAS_maps_ext hκ hz1 with he | ⟨u, hu, he⟩
    · rw [h] at he; exact absurd he (OnePoint.coe_ne_infty _)
    · rw [h] at he
      have := OnePoint.coe_injective he
      rw [this]; exact hu

/-- Lintegral change of variables `u = w_κ(z)` on `𝔻*`. -/
theorem wpcv_lcov {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (G : ℂ → ℝ≥0∞) :
    (∫⁻ u in unitDiscExterior, G u) =
      ∫⁻ z in unitDiscExterior, ENNReal.ofReal (jacobian (wA κ) z) * G (wA κ z) := by
  obtain ⟨a, b, c, d, W, hdet, hW, hform, hcoe⟩ := bc_wA_form hκ
  obtain ⟨K, hK⟩ := hW.1
  have himg : W '' univ = univ := hW.2.1
  have hinj : Function.Injective W := fun x y h => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) h
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  set S : Set ℂ := {v : ℂ | c * v + d ≠ 0 ∧ mobiusFn a b c d v ∈ unitDiscExterior} with hS
  have hP : IsOpen {v : ℂ | c * v + d ≠ 0} := isOpen_ne_fun (by fun_prop) (by fun_prop)
  have hMc : ContinuousOn (mobiusFn a b c d) {v : ℂ | c * v + d ≠ 0} := fun v hv =>
    (bc_mobiusFn_hasDerivAt (z := v) hv).continuousAt.continuousWithinAt
  have hSo : IsOpen S := by
    have := hMc.isOpen_inter_preimage hP hE
    convert this using 1
    ext v; simp [hS, and_comm]
  set H : ℂ → ℝ≥0∞ := S.indicator (fun v => ENNReal.ofReal (‖(a * d - b * c) / (c * v + d) ^ 2‖ ^ 2) *
    G (mobiusFn a b c d v)) with hH
  have e1 : (∫⁻ u in unitDiscExterior, G u) = ∫⁻ v, H v := by
    rw [wpcv_mobius_l hdet G, hH, lintegral_indicator hSo.measurableSet]
  have e2 := qcv_lintegral_image_eq (D := univ) hK H
  rw [himg, Measure.restrict_univ] at e2
  rw [e1, e2, ← lintegral_indicator hE.measurableSet]
  apply lintegral_congr_ae
  have hgood := s23_c2_ae_good hK
  rw [Measure.restrict_univ] at hgood
  have hnull : ∀ᵐ z : ℂ, c * W z + d ≠ 0 := by
    by_cases hc : c = 0
    · have hd : d ≠ 0 := by
        intro h; apply hdet; rw [hc, h]; ring
      exact Eventually.of_forall fun z => by rw [hc, zero_mul, zero_add]; exact hd
    · have hsub : {z : ℂ | c * W z + d = 0} ⊆ {z | W z = -d / c} := by
        intro z hz
        simp only [mem_setOf_eq] at hz ⊢
        field_simp
        linear_combination hz
      have : (volume : Measure ℂ) {z : ℂ | c * W z + d = 0} = 0 :=
        measure_mono_null hsub (Set.Subsingleton.measure_zero
          (fun x hx y hy => hinj (hx.trans hy.symm)) volume)
      exact measure_eq_zero_iff_ae_notMem.mp this
  filter_upwards [hgood, hnull] with z hz1 hz3
  obtain ⟨hdiff, hlt, -⟩ := hz1
  have hg : DifferentiableAt ℂ (mobiusFn a b c d) (W z) :=
    (bc_mobiusFn_hasDerivAt hz3).differentiableAt
  have hfun : wA κ = mobiusFn a b c d ∘ W := funext hform
  have hch := eq6_5 hdiff hg
  have hder : deriv (mobiusFn a b c d) (W z) = (a * d - b * c) / (c * W z + d) ^ 2 :=
    (bc_mobiusFn_hasDerivAt hz3).deriv
  have hjac : jacobian (wA κ) z = ‖(a * d - b * c) / (c * W z + d) ^ 2‖ ^ 2 * jacobian W z := by
    unfold jacobian
    rw [hfun, hch.1, hch.2, hder, norm_mul, norm_mul]
    ring
  have hmem := wpcv_mem_iff hκ hcoe hz3
  by_cases hz : z ∈ unitDiscExterior
  · have hWz : W z ∈ S := ⟨hz3, hmem.mpr hz⟩
    rw [Set.indicator_of_mem hz, hH, Set.indicator_of_mem hWz, hjac, hform z,
      ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  · have hWz : W z ∉ S := fun h => hz (hmem.mp h.2)
    rw [Set.indicator_of_notMem hz, hH, Set.indicator_of_notMem hWz, mul_zero]


/-! ### Pseudo-hyperbolic balls in `𝔻*` -/

/-- `T_y(v) = (v - y)/(1 - ȳ v)`: sends `y ↦ 0`; for `y, v ∈ 𝔻*` it has modulus `< 1`. -/
def wpT (y v : ℂ) : ℂ := (v - y) / (1 - conj y * v)

/-- Inverse chart `V_y(ζ) = (ζ + y)/(1 + ȳ ζ)`. -/
def wpV (y ζ : ℂ) : ℂ := (ζ + y) / (1 + conj y * ζ)

/-- Pseudo-hyperbolic ball of radius `s` about `y` in `𝔻*`. -/
def wpB (y : ℂ) (s : ℝ) : Set ℂ := {v | 1 < ‖v‖ ∧ ‖wpT y v‖ < s}

theorem wpV_eq (y : ℂ) : wpV y = mobiusFn 1 y (conj y) 1 := by
  funext ζ; unfold wpV mobiusFn; rw [one_mul, add_comm (conj y * ζ) 1]

theorem wpcv_norm_id (y v : ℂ) :
    ‖1 - conj y * v‖ ^ 2 - ‖v - y‖ ^ 2 = (‖y‖ ^ 2 - 1) * (‖v‖ ^ 2 - 1) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

theorem wpcv_conj_mul {y : ℂ} : conj y * y = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.conj_mul', Complex.ofReal_pow]

theorem wpcv_one_sub_ne {y : ℂ} (hy : 1 < ‖y‖) : (1 : ℂ) - conj y * y ≠ 0 := by
  rw [wpcv_conj_mul]
  intro h
  have : ((1 - ‖y‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [Complex.ofReal_sub, Complex.ofReal_one]; exact h
  have := Complex.ofReal_eq_zero.1 this
  nlinarith

theorem wpcv_den_ne {y v : ℂ} (hy : 1 < ‖y‖) (hv : 1 < ‖v‖) : 1 - conj y * v ≠ 0 := by
  intro h
  have h1 : conj y * v = 1 := by linear_combination -h
  have : ‖conj y * v‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, Complex.norm_conj] at this
  nlinarith

theorem wpT_wpV {y ζ : ℂ} (h0 : (1 : ℂ) - conj y * y ≠ 0) (hζ : 1 + conj y * ζ ≠ 0) :
    wpT y (wpV y ζ) = ζ := by
  have h3 : wpV y ζ * (1 + conj y * ζ) = ζ + y := div_mul_cancel₀ _ hζ
  have e1 : wpV y ζ - y = ζ * (1 - conj y * y) / (1 + conj y * ζ) := by
    rw [eq_div_iff hζ]; linear_combination h3
  have e2 : 1 - conj y * wpV y ζ = (1 - conj y * y) / (1 + conj y * ζ) := by
    rw [eq_div_iff hζ]; linear_combination (-(conj y)) * h3
  unfold wpT
  rw [e1, e2, div_div_div_cancel_right₀ hζ]
  exact mul_div_cancel_right₀ ζ h0

theorem wpT_one_add {y v : ℂ} (hv : 1 - conj y * v ≠ 0) :
    1 + conj y * wpT y v = (1 - conj y * y) / (1 - conj y * v) := by
  have h3 : wpT y v * (1 - conj y * v) = v - y := div_mul_cancel₀ _ hv
  rw [eq_div_iff hv]; linear_combination (conj y) * h3

theorem wpV_wpT {y v : ℂ} (h0 : (1 : ℂ) - conj y * y ≠ 0) (hv : 1 - conj y * v ≠ 0) :
    wpV y (wpT y v) = v := by
  have h3 : wpT y v * (1 - conj y * v) = v - y := div_mul_cancel₀ _ hv
  have e1 : wpT y v + y = v * (1 - conj y * y) / (1 - conj y * v) := by
    rw [eq_div_iff hv]; linear_combination h3
  unfold wpV
  rw [e1, wpT_one_add hv, div_div_div_cancel_right₀ hv]
  exact mul_div_cancel_right₀ v h0

theorem wpB_eq_image {y : ℂ} (hy : 1 < ‖y‖) {s : ℝ} (hs : s ≤ 1) :
    wpB y s = wpV y '' {ζ | ‖ζ‖ < s ∧ 1 + conj y * ζ ≠ 0} := by
  ext v
  constructor
  · rintro ⟨hv, hT⟩
    have hden := wpcv_den_ne hy hv
    refine ⟨wpT y v, ⟨hT, ?_⟩, wpV_wpT (wpcv_one_sub_ne hy) hden⟩
    rw [wpT_one_add hden]
    exact div_ne_zero (wpcv_one_sub_ne hy) hden
  · rintro ⟨ζ, ⟨hζs, hζ⟩, rfl⟩
    refine ⟨?_, by rw [wpT_wpV (wpcv_one_sub_ne hy) hζ]; exact hζs⟩
    have hid := wpcv_norm_id (-y) ζ
    rw [map_neg, neg_mul, sub_neg_eq_add, sub_neg_eq_add, norm_neg] at hid
    have hA : 0 < ‖1 + conj y * ζ‖ := norm_pos_iff.2 hζ
    have hζ1 : ‖ζ‖ < 1 := lt_of_lt_of_le hζs hs
    have hneg : (‖y‖ ^ 2 - 1) * (‖ζ‖ ^ 2 - 1) < 0 :=
      mul_neg_of_pos_of_neg (by nlinarith) (by nlinarith [norm_nonneg ζ])
    have hlt : ‖1 + conj y * ζ‖ < ‖ζ + y‖ := by
      have h1 : ‖1 + conj y * ζ‖ ^ 2 < ‖ζ + y‖ ^ 2 := by linarith
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
    unfold wpV
    rw [norm_div, lt_div_iff₀ hA]
    simpa using hlt

theorem wpcv_wpV_inj {y : ℂ} (hy : 1 < ‖y‖) {U : Set ℂ} (hU : ∀ ζ ∈ U, 1 + conj y * ζ ≠ 0) :
    InjOn (wpV y) U := by
  rw [wpV_eq]
  have hdet : (1 : ℂ) * 1 - y * conj y ≠ 0 := by
    rw [one_mul, mul_comm]; exact wpcv_one_sub_ne hy
  exact bc_mobiusFn_injOn hdet (fun ζ hζ => by simpa [add_comm] using hU ζ hζ)

theorem wpcv_wpV_density_real {y ζ : ℂ} (hy : 1 < ‖y‖) (hζs : ‖ζ‖ < 1) (hζ : 1 + conj y * ζ ≠ 0) :
    ‖deriv (wpV y) ζ‖ ^ 2 * rho (wpV y ζ) = 4 / (1 - ‖ζ‖ ^ 2) ^ 2 := by
  have hd : deriv (wpV y) ζ = (1 * 1 - y * conj y) / (conj y * ζ + 1) ^ 2 := by
    rw [wpV_eq]
    have := bc_mobiusFn_hasDerivAt (a := 1) (b := y) (c := conj y) (d := 1) (z := ζ)
      (by rwa [add_comm] at hζ)
    exact this.deriv
  have hA : 0 < ‖1 + conj y * ζ‖ := norm_pos_iff.2 hζ
  have hid := wpcv_norm_id (-y) ζ
  rw [map_neg, neg_mul, sub_neg_eq_add, sub_neg_eq_add, norm_neg] at hid
  have hy2 : 0 < ‖y‖ ^ 2 - 1 := by nlinarith
  have hz2 : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hn1 : ‖(1 * 1 - y * conj y : ℂ)‖ = ‖y‖ ^ 2 - 1 := by
    have : (1 * 1 - y * conj y : ℂ) = ((1 - ‖y‖ ^ 2 : ℝ) : ℂ) := by
      rw [one_mul, mul_comm, wpcv_conj_mul, Complex.ofReal_sub, Complex.ofReal_one]
    rw [this, Complex.norm_real, Real.norm_of_nonpos (by nlinarith)]; ring
  have hnV : ‖wpV y ζ‖ = ‖ζ + y‖ / ‖1 + conj y * ζ‖ := by unfold wpV; rw [norm_div]
  have hdn : ‖deriv (wpV y) ζ‖ = (‖y‖ ^ 2 - 1) / ‖1 + conj y * ζ‖ ^ 2 := by
    rw [hd, norm_div, norm_pow, hn1, add_comm (conj y * ζ) 1]
  rw [hdn]
  unfold rho
  rw [hnV, div_pow, div_pow]
  have hA2 : 0 < ‖1 + conj y * ζ‖ ^ 2 := by positivity
  have key : 1 - ‖ζ + y‖ ^ 2 / ‖1 + conj y * ζ‖ ^ 2 =
      (-((‖y‖ ^ 2 - 1) * (1 - ‖ζ‖ ^ 2))) / ‖1 + conj y * ζ‖ ^ 2 := by
    rw [eq_div_iff hA2.ne', sub_mul, div_mul_cancel₀ _ hA2.ne']
    nlinarith [hid]
  rw [key]
  field_simp


theorem wpcv_wpV_density {y ζ : ℂ} (hy : 1 < ‖y‖) (hζs : ‖ζ‖ < 1) (hζ : 1 + conj y * ζ ≠ 0) :
    ENNReal.ofReal (‖deriv (wpV y) ζ‖ ^ 2) * ENNReal.ofReal (rho (wpV y ζ)) =
      ENNReal.ofReal (4 / (1 - ‖ζ‖ ^ 2) ^ 2) := by
  rw [← ENNReal.ofReal_mul (sq_nonneg _), wpcv_wpV_density_real hy hζs hζ]

/-- Hyperbolic area of a pseudo-hyperbolic ball (uniform in the centre). -/
theorem wpcv_wpB_area {y : ℂ} (hy : 1 < ‖y‖) {s : ℝ} (hs0 : 0 < s) (hs : s < 1) :
    ∫⁻ v in wpB y s, ENNReal.ofReal (rho v) ≤
      ENNReal.ofReal (4 / (1 - s ^ 2) ^ 2) * volume (ball (0 : ℂ) s) := by
  set U : Set ℂ := {ζ | ‖ζ‖ < s ∧ 1 + conj y * ζ ≠ 0} with hU
  have hUo : IsOpen U := by
    have h1 : IsOpen {ζ : ℂ | ‖ζ‖ < s} := isOpen_lt continuous_norm continuous_const
    have h2 : IsOpen {ζ : ℂ | 1 + conj y * ζ ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
    exact h1.inter h2
  have hden : ∀ ζ ∈ U, 1 + conj y * ζ ≠ 0 := fun ζ hζ => hζ.2
  have hdiff : DifferentiableOn ℂ (wpV y) U := by
    rw [wpV_eq]
    intro ζ hζ
    exact (bc_mobiusFn_hasDerivAt (a := 1) (b := y) (c := conj y) (d := 1) (z := ζ)
      (by rw [add_comm]; exact hden ζ hζ)).differentiableAt.differentiableWithinAt
  rw [wpB_eq_image hy hs.le, r24_conformal_lintegral hUo hdiff (wpcv_wpV_inj hy hden)]
  calc ∫⁻ ζ in U, ENNReal.ofReal (‖deriv (wpV y) ζ‖ ^ 2) * ENNReal.ofReal (rho (wpV y ζ))
      ≤ ∫⁻ ζ in U, ENNReal.ofReal (4 / (1 - s ^ 2) ^ 2) := by
        apply lintegral_mono_ae
        refine (ae_restrict_iff' hUo.measurableSet).2 (Eventually.of_forall fun ζ hζ => ?_)
        rw [wpcv_wpV_density hy (hζ.1.trans hs) hζ.2]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 - s ^ 2 ≤ 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ, hζ.1]
        have h2 : 0 < 1 - s ^ 2 := by nlinarith
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_left₀ h2.le h1 2
    _ = ENNReal.ofReal (4 / (1 - s ^ 2) ^ 2) * volume U := by rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (4 / (1 - s ^ 2) ^ 2) * volume (ball (0 : ℂ) s) := by
        gcongr
        intro ζ hζ
        simpa using hζ.1

/-! ### Mean value inequality for `|F|²` on a disc -/

open scoped Pointwise in
theorem wpcv_scale_lintegral {s : ℝ} (hs : 0 < s) (G : ℂ → ℝ≥0∞) :
    ∫⁻ ζ in ball (0 : ℂ) s, G ζ =
      ENNReal.ofReal (s ^ 2) * ∫⁻ z in unitDisc, G ((s : ℂ) * z) := by
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => (s : ℂ) * z) unitDisc := by fun_prop
  have hinj : InjOn (fun z : ℂ => (s : ℂ) * z) unitDisc := by
    intro x _ y _ h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hs.ne') h
  have himg : (fun z : ℂ => (s : ℂ) * z) '' unitDisc = ball (0 : ℂ) s := by
    have : (fun z : ℂ => (s : ℂ) * z) '' unitDisc = (s : ℂ) • unitDisc := by
      ext x; simp [Set.mem_smul_set]
    rw [this]
    unfold unitDisc
    rw [_root_.smul_ball (Complex.ofReal_ne_zero.2 hs.ne')]
    simp [abs_of_pos hs]
  have h := r24_conformal_lintegral (U := unitDisc) isOpen_ball hdiff hinj G
  rw [himg] at h
  rw [h, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun isOpen_ball.measurableSet
  intro z _
  have hd : deriv (fun z : ℂ => (s : ℂ) * z) z = s := by simp
  simp only [hd, Complex.norm_real, Real.norm_of_nonneg hs.le]

theorem wpcv_mean_value_sq {F : ℂ → ℂ} {s : ℝ} (hs : 0 < s) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) s)) :
    ENNReal.ofReal (π * s ^ 2 / 3) * (‖F 0‖₊ : ℝ≥0∞) ^ 2 ≤ ∫⁻ ζ in ball (0 : ℂ) s, (‖F ζ‖₊ : ℝ≥0∞) ^ 2 := by
  set L : ℝ≥0∞ := ∫⁻ ζ in ball (0 : ℂ) s, (‖F ζ‖₊ : ℝ≥0∞) ^ 2 with hL
  by_cases hLt : L = ∞
  · rw [hLt]; exact le_top
  have hLt' : L < ∞ := lt_top_iff_ne_top.2 hLt
  set Fs : ℂ → ℂ := fun z => F ((s : ℂ) * z) with hFs
  have hsc := wpcv_scale_lintegral hs (fun ζ => (‖F ζ‖₊ : ℝ≥0∞) ^ 2)
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hI : ∫⁻ z in unitDisc, (‖Fs z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (s ^ 2)⁻¹ * L := by
    have h1 : L = ENNReal.ofReal (s ^ 2) * ∫⁻ z in unitDisc, (‖Fs z‖₊ : ℝ≥0∞) ^ 2 := hsc
    rw [h1, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hs2.le), inv_mul_cancel₀ hs2.ne']
    simp
  have hdiffs : DifferentiableOn ℂ Fs unitDisc := by
    refine hF.comp (by fun_prop) ?_
    intro z hz
    have hz' : ‖z‖ < 1 := by simpa [unitDisc] using hz
    simpa [abs_of_pos hs, norm_mul] using mul_lt_mul_of_pos_left hz' hs
  have hA2 : Fs ∈ A2fun unitDisc := by
    refine ⟨hdiffs, ?_⟩
    unfold normA2
    refine (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).2 ?_
    calc ∫⁻ z in unitDisc, (‖Fs z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹
        ≤ ∫⁻ z in unitDisc, (‖Fs z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 / 4) := by
          apply setLIntegral_mono' measurableSet_ball
          intro z hz
          gcongr
          exact wb_rhoInv_le (by simpa [unitDisc] using hz)
      _ = (∫⁻ z in unitDisc, (‖Fs z‖₊ : ℝ≥0∞) ^ 2) * ENNReal.ofReal (1 / 4) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      _ < ∞ := by
          rw [hI]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hLt') ENNReal.ofReal_lt_top
  have hev := A2fun.disk_weighted_evaluation_sq hA2 (z := 0) (by simp [unitDisc])
  have hn2 : (normA2 unitDisc Fs) ^ 2 = ENNReal.ofReal (∫ z in unitDisc, ‖Fs z‖ ^ 2 * (rho z)⁻¹) :=
    A2fun.normA2_sq isOpen_ball hA2
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, one_pow,
    one_mul] at hev
  have hFs0 : Fs 0 = F 0 := by simp [hFs]
  rw [hFs0] at hev
  -- everything in `ℝ≥0∞`
  have h1 : (‖F 0‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖F 0‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  have h2 : ENNReal.ofReal (‖F 0‖ ^ 2) ≤ ENNReal.ofReal (12 / π) * (normA2 unitDisc Fs) ^ 2 := by
    rw [hn2, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hev
  have h3 : (normA2 unitDisc Fs) ^ 2 ≤ ENNReal.ofReal (1 / 4) * (ENNReal.ofReal (s ^ 2)⁻¹ * L) := by
    rw [← ENNReal.rpow_two]
    unfold normA2
    rw [← ENNReal.rpow_mul]
    norm_num only [show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    calc ∫⁻ z in unitDisc, (‖Fs z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹
        ≤ ∫⁻ z in unitDisc, (‖Fs z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 / 4) := by
          apply setLIntegral_mono' measurableSet_ball
          intro z hz
          gcongr
          exact wb_rhoInv_le (by simpa [unitDisc] using hz)
      _ = (∫⁻ z in unitDisc, (‖Fs z‖₊ : ℝ≥0∞) ^ 2) * ENNReal.ofReal (1 / 4) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      _ = _ := by rw [hI, mul_comm]
  have h4 : (‖F 0‖₊ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (12 / π) * (ENNReal.ofReal (1 / 4) * (ENNReal.ofReal (s ^ 2)⁻¹ * L)) := by
    rw [h1]
    exact h2.trans (by gcongr)
  calc ENNReal.ofReal (π * s ^ 2 / 3) * (‖F 0‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal (π * s ^ 2 / 3) *
          (ENNReal.ofReal (12 / π) * (ENNReal.ofReal (1 / 4) * (ENNReal.ofReal (s ^ 2)⁻¹ * L))) := by
        gcongr
    _ = L := by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        have : π * s ^ 2 / 3 * (12 / π) * (1 / 4) * (s ^ 2)⁻¹ = 1 := by
          field_simp
          ring
        rw [this, ENNReal.ofReal_one, one_mul]

/-! ### Pointwise bound for a harmonic Beltrami differential by its local `L²` mass -/

theorem wpcv_mu_mean {μ φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDiscExterior)
    (hrep : ∀ z ∈ unitDiscExterior, μ z = ((rho z : ℝ) : ℂ)⁻¹ * conj (φ z))
    {y : ℂ} (hy : 1 < ‖y‖) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsy : s * ‖y‖ ≤ 1) :
    (‖μ y‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (3 / (4 * π * s ^ 2 * (1 - s ^ 2) ^ 2)) *
      ∫⁻ v in wpB y s, (‖μ v‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho v) := by
  have hden : ∀ ζ ∈ ball (0 : ℂ) s, 1 + conj y * ζ ≠ 0 := by
    intro ζ hζ h
    have h1 : conj y * ζ = -1 := by linear_combination h
    have h2 : ‖conj y * ζ‖ = 1 := by rw [h1]; simp
    rw [norm_mul, Complex.norm_conj] at h2
    have hz : ‖ζ‖ < s := by simpa using hζ
    nlinarith [norm_nonneg ζ]
  have hset : {ζ : ℂ | ‖ζ‖ < s ∧ 1 + conj y * ζ ≠ 0} = ball 0 s := by
    ext ζ; constructor
    · rintro ⟨h, -⟩; simpa using h
    · intro hζ; exact ⟨by simpa using hζ, hden ζ hζ⟩
  have hBimg : wpB y s = wpV y '' ball 0 s := by rw [wpB_eq_image hy hs1.le, hset]
  set dV : ℂ → ℂ := fun ζ => (1 - y * conj y) / (1 + conj y * ζ) ^ 2 with hdV
  have hderiv : ∀ ζ ∈ ball (0 : ℂ) s, deriv (wpV y) ζ = dV ζ := by
    intro ζ hζ
    rw [wpV_eq]
    have := bc_mobiusFn_hasDerivAt (a := 1) (b := y) (c := conj y) (d := 1) (z := ζ)
      (by rw [add_comm]; exact hden ζ hζ)
    rw [this.deriv, hdV]
    simp only [one_mul]
    rw [add_comm (conj y * ζ) 1]
  have hVdiff : DifferentiableOn ℂ (wpV y) (ball 0 s) := by
    rw [wpV_eq]
    intro ζ hζ
    exact (bc_mobiusFn_hasDerivAt (a := 1) (b := y) (c := conj y) (d := 1) (z := ζ)
      (by rw [add_comm]; exact hden ζ hζ)).differentiableAt.differentiableWithinAt
  have hdVdiff : DifferentiableOn ℂ dV (ball 0 s) := by
    refine DifferentiableOn.div (by fun_prop) (by fun_prop) (fun ζ hζ => pow_ne_zero 2 (hden ζ hζ))
  have hVmaps : ∀ ζ ∈ ball (0 : ℂ) s, wpV y ζ ∈ unitDiscExterior := by
    intro ζ hζ
    have : wpV y ζ ∈ wpB y s := by rw [hBimg]; exact ⟨ζ, hζ, rfl⟩
    simpa [unitDiscExterior] using this.1
  set F : ℂ → ℂ := fun ζ => φ (wpV y ζ) * dV ζ ^ 2 with hF
  have hFdiff : DifferentiableOn ℂ F (ball 0 s) :=
    (hφ.comp hVdiff hVmaps).mul (hdVdiff.pow 2)
  have hmv := wpcv_mean_value_sq hs0 hFdiff
  -- change of variables
  have hcov := r24_conformal_lintegral (U := ball (0 : ℂ) s) isOpen_ball hVdiff
    (wpcv_wpV_inj hy (fun ζ hζ => hden ζ hζ))
    (fun v => (‖μ v‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho v))
  rw [← hBimg] at hcov
  have hpt : ∀ ζ ∈ ball (0 : ℂ) s, ENNReal.ofReal ((1 - s ^ 2) ^ 2 / 4) * (‖F ζ‖₊ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (‖deriv (wpV y) ζ‖ ^ 2) *
        ((‖μ (wpV y ζ)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho (wpV y ζ))) := by
    intro ζ hζ
    have hζs : ‖ζ‖ < s := by simpa using hζ
    have hv := hVmaps ζ hζ
    have hv1 : 1 < ‖wpV y ζ‖ := by simpa [unitDiscExterior] using hv
    have hrho : 0 < rho (wpV y ζ) := by
      unfold rho
      have hne : 1 - ‖wpV y ζ‖ ^ 2 ≠ 0 := by nlinarith
      positivity
    have hdens := wpcv_wpV_density_real hy (hζs.trans hs1) (hden ζ hζ)
    have hmuv : ‖μ (wpV y ζ)‖ = ‖φ (wpV y ζ)‖ / rho (wpV y ζ) := by
      rw [hrep _ hv, norm_mul, norm_inv, Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg hrho.le, inv_mul_eq_div]
    have hz2 : 1 - s ^ 2 ≤ 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
    have hz3 : 0 < 1 - s ^ 2 := by nlinarith
    have hnF : ‖F ζ‖ ^ 2 = ‖φ (wpV y ζ)‖ ^ 2 * (‖deriv (wpV y) ζ‖ ^ 2) ^ 2 := by
      rw [hF]; simp only [norm_mul, norm_pow, hderiv ζ hζ]; ring
    have hrhs : ‖deriv (wpV y) ζ‖ ^ 2 * (‖μ (wpV y ζ)‖ ^ 2 * rho (wpV y ζ)) =
        ‖F ζ‖ ^ 2 * ((1 - ‖ζ‖ ^ 2) ^ 2 / 4) := by
      rw [hmuv, hnF]
      have hP : 0 < ‖deriv (wpV y) ζ‖ ^ 2 := by
        have : deriv (wpV y) ζ ≠ 0 := by
          rw [hderiv ζ hζ]
          refine div_ne_zero ?_ (pow_ne_zero 2 (hden ζ hζ))
          have := wpcv_one_sub_ne hy
          rwa [mul_comm] at this
        positivity
      have hz4 : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
      have hdens' : rho (wpV y ζ) = 4 / (1 - ‖ζ‖ ^ 2) ^ 2 / ‖deriv (wpV y) ζ‖ ^ 2 := by
        rw [eq_div_iff hP.ne', mul_comm]; exact hdens
      rw [hdens']
      field_simp
    have e1 : (‖F ζ‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖F ζ‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    have e2 : (‖μ (wpV y ζ)‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖μ (wpV y ζ)‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    have eL : ENNReal.ofReal ((1 - s ^ 2) ^ 2 / 4) * ENNReal.ofReal (‖F ζ‖ ^ 2) =
        ENNReal.ofReal ((1 - s ^ 2) ^ 2 / 4 * ‖F ζ‖ ^ 2) := (ENNReal.ofReal_mul (by positivity)).symm
    have eR : ENNReal.ofReal (‖deriv (wpV y) ζ‖ ^ 2) *
        (ENNReal.ofReal (‖μ (wpV y ζ)‖ ^ 2) * ENNReal.ofReal (rho (wpV y ζ))) =
        ENNReal.ofReal (‖deriv (wpV y) ζ‖ ^ 2 * (‖μ (wpV y ζ)‖ ^ 2 * rho (wpV y ζ))) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [e1, e2, eL, eR, hrhs]
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ ‖F ζ‖ ^ 2 := sq_nonneg _
    have h5 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz3.le hz2 2) this
    nlinarith [h5]
  have hbound : ENNReal.ofReal ((1 - s ^ 2) ^ 2 / 4) *
      ∫⁻ ζ in ball (0 : ℂ) s, (‖F ζ‖₊ : ℝ≥0∞) ^ 2 ≤
      ∫⁻ v in wpB y s, (‖μ v‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho v) := by
    rw [hcov, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' isOpen_ball.measurableSet
    exact hpt
  set I : ℝ≥0∞ := ∫⁻ v in wpB y s, (‖μ v‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho v) with hI
  -- the value at the centre
  have hV0 : wpV y 0 = y := by simp [wpV]
  have hdV0 : ‖dV 0‖ = ‖y‖ ^ 2 - 1 := by
    have : dV 0 = ((1 - ‖y‖ ^ 2 : ℝ) : ℂ) := by
      simp only [hdV, mul_zero, add_zero, one_pow, div_one]
      rw [mul_comm, wpcv_conj_mul, Complex.ofReal_sub, Complex.ofReal_one]
    rw [this, Complex.norm_real, Real.norm_of_nonpos (by nlinarith)]; ring
  have hy_rho : rho y = 4 / (‖y‖ ^ 2 - 1) ^ 2 := by
    unfold rho
    rw [show (1 - ‖y‖ ^ 2) ^ 2 = (‖y‖ ^ 2 - 1) ^ 2 by ring]
  have hy2 : 0 < ‖y‖ ^ 2 - 1 := by nlinarith
  have hmuy : ‖μ y‖ ^ 2 = ‖F 0‖ ^ 2 / 16 := by
    have hrho : 0 < rho y := by rw [hy_rho]; positivity
    have h1 : ‖μ y‖ = ‖φ y‖ / rho y := by
      rw [hrep _ (by simpa [unitDiscExterior] using hy), norm_mul, norm_inv, Complex.norm_conj,
        Complex.norm_real, Real.norm_of_nonneg hrho.le, inv_mul_eq_div]
    rw [h1, hy_rho]
    have hF0 : ‖F 0‖ = ‖φ y‖ * (‖y‖ ^ 2 - 1) ^ 2 := by
      simp only [hF, hV0, norm_mul, norm_pow, hdV0]
    rw [hF0]
    field_simp
    ring
  have hcenter : (‖μ y‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (1 / 16) * (‖F 0‖₊ : ℝ≥0∞) ^ 2 := by
    have e1 : (‖F 0‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖F 0‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    have e2 : (‖μ y‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖μ y‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    rw [e1, e2, ← ENNReal.ofReal_mul (by norm_num), hmuy]
    congr 1; ring
  rw [hcenter]
  have hz3 : 0 < 1 - s ^ 2 := by nlinarith
  have hc : 0 < π * s ^ 2 / 3 * ((1 - s ^ 2) ^ 2 / 4) := by positivity
  have key : ENNReal.ofReal (π * s ^ 2 / 3 * ((1 - s ^ 2) ^ 2 / 4)) * (‖F 0‖₊ : ℝ≥0∞) ^ 2 ≤ I := by
    rw [ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (π * s ^ 2 / 3)), mul_assoc]
    calc _ ≤ ENNReal.ofReal ((1 - s ^ 2) ^ 2 / 4) * ∫⁻ ζ in ball (0 : ℂ) s, (‖F ζ‖₊ : ℝ≥0∞) ^ 2 := by
          gcongr
      _ ≤ I := hbound
  calc ENNReal.ofReal (1 / 16) * (‖F 0‖₊ : ℝ≥0∞) ^ 2
      = ENNReal.ofReal (1 / 16 / (π * s ^ 2 / 3 * ((1 - s ^ 2) ^ 2 / 4))) *
          (ENNReal.ofReal (π * s ^ 2 / 3 * ((1 - s ^ 2) ^ 2 / 4)) * (‖F 0‖₊ : ℝ≥0∞) ^ 2) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hc.ne']
    _ ≤ ENNReal.ofReal (1 / 16 / (π * s ^ 2 / 3 * ((1 - s ^ 2) ^ 2 / 4))) * I := by gcongr
    _ = ENNReal.ofReal (3 / (4 * π * s ^ 2 * (1 - s ^ 2) ^ 2)) * I := by
        congr 2
        field_simp
        ring

/-! ### Quasi-isometry of `w_κ` (Mori) -/

theorem wpcv_Tdisc {b : ℂ} (hb : ‖b‖ < 1) : IsConformalOnto (wpT b) unitDisc unitDisc := by
  have hb' : 1 - conj b * b ≠ 0 := by
    rw [wpcv_conj_mul]
    intro h
    have : ((1 - ‖b‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [Complex.ofReal_sub, Complex.ofReal_one]; exact h
    have := Complex.ofReal_eq_zero.1 this
    nlinarith [norm_nonneg b]
  have hden : ∀ z ∈ unitDisc, 1 - conj b * z ≠ 0 := by
    intro z hz h
    have h1 : conj b * z = 1 := by linear_combination -h
    have h2 : ‖conj b * z‖ = 1 := by rw [h1, norm_one]
    rw [norm_mul, Complex.norm_conj] at h2
    have hz' : ‖z‖ < 1 := by simpa [unitDisc] using hz
    nlinarith [norm_nonneg z, norm_nonneg b]
  have hmap : ∀ z ∈ unitDisc, ‖wpT b z‖ < 1 := by
    intro z hz
    have hz' : ‖z‖ < 1 := by simpa [unitDisc] using hz
    have hid := wpcv_norm_id b z
    have hA : 0 < ‖1 - conj b * z‖ := norm_pos_iff.2 (hden z hz)
    have hpos : 0 < (‖b‖ ^ 2 - 1) * (‖z‖ ^ 2 - 1) :=
      mul_pos_of_neg_of_neg (by nlinarith [norm_nonneg b]) (by nlinarith [norm_nonneg z])
    have h1 : ‖z - b‖ ^ 2 < ‖1 - conj b * z‖ ^ 2 := by linarith
    have h2 : ‖z - b‖ < ‖1 - conj b * z‖ := lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
    unfold wpT
    rw [norm_div, div_lt_one hA]
    exact h2
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    unfold wpT
    exact (((differentiableAt_id.sub_const b)).div
      ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id))
      (hden z hz)).differentiableWithinAt
  · intro x hx y hy hxy
    have hx' := hden x hx
    have hy' := hden y hy
    unfold wpT at hxy
    rw [div_eq_div_iff hx' hy'] at hxy
    have : (x - y) * (1 - conj b * b) = 0 := by linear_combination hxy
    rcases mul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hb'
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [unitDisc] using hmap z hz
    · intro hw
      have hw' : ‖w‖ < 1 := by simpa [unitDisc] using hw
      have hq : 1 + conj b * w ≠ 0 := by
        intro h
        have h1 : conj b * w = -1 := by linear_combination h
        have h2 : ‖conj b * w‖ = 1 := by rw [h1]; simp
        rw [norm_mul, Complex.norm_conj] at h2
        nlinarith [norm_nonneg w, norm_nonneg b]
      refine ⟨wpV b w, ?_, wpT_wpV hb' hq⟩
      have hid := wpcv_norm_id (-b) w
      rw [map_neg, neg_mul, sub_neg_eq_add, sub_neg_eq_add, norm_neg] at hid
      have hA : 0 < ‖1 + conj b * w‖ := norm_pos_iff.2 hq
      have hpos : 0 < (‖b‖ ^ 2 - 1) * (‖w‖ ^ 2 - 1) :=
        mul_pos_of_neg_of_neg (by nlinarith [norm_nonneg b]) (by nlinarith [norm_nonneg w])
      have h1 : ‖w + b‖ ^ 2 < ‖1 + conj b * w‖ ^ 2 := by linarith
      have h2 : ‖w + b‖ < ‖1 + conj b * w‖ := lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
      have hlt : ‖wpV b w‖ < 1 := by
        unfold wpV
        rw [norm_div, div_lt_one hA]
        exact h2
      simpa [unitDisc] using hlt

theorem wpV_eq_wpT (b : ℂ) : wpV b = wpT (-b) := by
  funext ζ; simp [wpV, wpT]

/-- `w_κ` is a `K`-quasiconformal self-map of the unit disc. -/
theorem wpcv_g_disc {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    ∃ K : ℝ, IsKQC (wA κ) unitDisc K ∧ wA κ '' unitDisc = unitDisc := by
  obtain ⟨M, ⟨a, b, c, d, hdet, rfl⟩, W, hW, hfin, -⟩ := wA_spec hκ
  obtain ⟨K, hK⟩ := hW.1
  have hform : ∀ z, wA κ z = mobiusFn a b c d (W z) := by
    intro z
    unfold wA
    rw [hfin z]
    by_cases h : c * W z + d = 0
    · rw [mobiusExt_coe_of_eq_zero h]
      simp [mobiusFn, h, finPart]
    · rw [mobiusExt_coe h]
      rfl
  have hdisc : ∀ z ∈ unitDisc, c * W z + d ≠ 0 := by
    intro z hz h
    obtain ⟨u, -, hu⟩ := wAS_maps_disc hκ (z := z) (by simpa [unitDisc] using hz)
    rw [hfin z, mobiusExt_coe_of_eq_zero h] at hu
    exact absurd hu.symm (OnePoint.coe_ne_infty u)
  have hWU : IsKQC W unitDisc K := t3b_isKQC_restrict hK isOpen_ball (subset_univ _)
  have hVo : IsOpen (W '' unitDisc) := isOpen_image_of_isKQC hWU
  have hVden : ∀ z ∈ W '' unitDisc, c * z + d ≠ 0 := by
    rintro _ ⟨x, hx, rfl⟩; exact hdisc x hx
  have hconf : IsConformalOnto (mobiusFn a b c d) (W '' unitDisc)
      (mobiusFn a b c d '' (W '' unitDisc)) := by
    refine ⟨fun z hz => ?_, bc_mobiusFn_injOn hdet hVden, rfl⟩
    exact (bc_mobiusFn_hasDerivAt (hVden z hz)).differentiableAt.differentiableWithinAt
  have hg : IsKQC (mobiusFn a b c d) (W '' unitDisc) 1 := isKQC_one_of_conformal hVo hconf
  have hcomp := thm7_1_comp hWU hg (subset_refl _)
  have hfun : wA κ = mobiusFn a b c d ∘ W := funext hform
  refine ⟨K * 1, by rw [hfun]; exact hcomp, ?_⟩
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨u, hu, hzu⟩ := wAS_maps_disc hκ (z := z) (by simpa [unitDisc] using hz)
    show finPart (wAS κ (z : ExtPlane)) ∈ unitDisc
    rw [hzu]
    simpa [finPart, unitDisc] using hu
  · intro hw
    have hmem : (w : ExtPlane) ∈ wAS κ '' toExt unitDisc := by
      rw [(wA_mapsTo hκ).1]; exact ⟨w, hw, rfl⟩
    obtain ⟨p, ⟨z, hz, rfl⟩, hpw⟩ := hmem
    exact ⟨z, hz, by show finPart (wAS κ (z : ExtPlane)) = w; rw [hpw]; rfl⟩

theorem wpcv_mori {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ a ∈ unitDisc, ∀ z ∈ unitDisc, ‖wpT a z‖ < t →
      ‖wpT (wA κ a) (wA κ z)‖ < 1 / 2 := by
  obtain ⟨K, hK, himg⟩ := wpcv_g_disc hκ
  have hK1 : 1 ≤ K := hK.2.1
  refine ⟨(1 / 32 : ℝ) ^ K, Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith), ?_⟩
  intro a ha z hz hzt
  have ha' : ‖a‖ < 1 := by simpa [unitDisc] using ha
  have hz' : ‖z‖ < 1 := by simpa [unitDisc] using hz
  have hga : wA κ a ∈ unitDisc := himg ▸ mem_image_of_mem _ ha
  have hga' : ‖wA κ a‖ < 1 := by simpa [unitDisc] using hga
  have hB : IsConformalOnto (wpV a) unitDisc unitDisc := by
    rw [wpV_eq_wpT]; exact wpcv_Tdisc (by simpa using ha')
  have hA : IsConformalOnto (wpT (wA κ a)) unitDisc unitDisc := wpcv_Tdisc hga'
  have hBK : IsKQC (wpV a) unitDisc 1 := isKQC_one_of_conformal isOpen_ball hB
  have hAK : IsKQC (wpT (wA κ a)) unitDisc 1 := isKQC_one_of_conformal isOpen_ball hA
  have h1 := thm7_1_comp hBK hK (by rw [hB.2.2])
  have h2 := thm7_1_comp h1 hAK (by
    rw [Set.image_comp, hB.2.2, himg])
  have hKK : (1 * K) * 1 = K := by ring
  rw [hKK] at h2
  have himg2 : (wpT (wA κ a) ∘ (wA κ ∘ wpV a)) '' unitDisc = unitDisc := by
    rw [Set.image_comp, Set.image_comp, hB.2.2, himg, hA.2.2]
  have hB0 : wpV a 0 = a := by simp [wpV]
  have hA0 : (wpT (wA κ a) ∘ (wA κ ∘ wpV a)) 0 = 0 := by
    simp only [Function.comp, hB0]
    simp [wpT]
  have hden : 1 - conj a * z ≠ 0 := by
    intro h
    have h1 : conj a * z = 1 := by linear_combination -h
    have h2 : ‖conj a * z‖ = 1 := by rw [h1, norm_one]
    rw [norm_mul, Complex.norm_conj] at h2
    nlinarith [norm_nonneg z, norm_nonneg a]
  have hrec : wpV a (wpT a z) = z := by
    apply wpV_wpT _ hden
    rw [wpcv_conj_mul]
    intro h
    have : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [Complex.ofReal_sub, Complex.ofReal_one]; exact h
    have := Complex.ofReal_eq_zero.1 this
    nlinarith [norm_nonneg a]
  set ζ : ℂ := wpT a z with hζ
  have hζD : ζ ∈ unitDisc := by
    have : ‖ζ‖ < (1 / 32 : ℝ) ^ K := hzt
    have h3 : (1 / 32 : ℝ) ^ K < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
    simpa [unitDisc] using this.trans h3
  have hval : (wpT (wA κ a) ∘ (wA κ ∘ wpV a)) ζ = wpT (wA κ a) (wA κ z) := by
    simp only [Function.comp, hrec]
  rw [← hval]
  by_cases hζ0 : ζ = 0
  · rw [hζ0, hA0]; norm_num
  · have hm := thm15_2_mori h2 himg2 hA0 hζD (mem_ball_self zero_lt_one) hζ0
    rw [hA0, sub_zero, sub_zero] at hm
    have hpow : ‖ζ‖ ^ (1 / K) ≤ ((1 / 32 : ℝ) ^ K) ^ (1 / K) :=
      Real.rpow_le_rpow (norm_nonneg _) hzt.le (by positivity)
    have hval2 : ((1 / 32 : ℝ) ^ K) ^ (1 / K) = 1 / 32 := by
      rw [← Real.rpow_mul (by norm_num)]
      rw [mul_one_div_cancel (by linarith), Real.rpow_one]
    rw [hval2] at hpow
    calc _ < 16 * ‖ζ‖ ^ (1 / K) := hm
      _ ≤ 16 * (1 / 32) := by gcongr
      _ = 1 / 2 := by norm_num

/-- Reflection invariance of the pseudo-hyperbolic quantity. -/
theorem wpcv_wpT_refl {p q : ℂ} (hp : 1 < ‖p‖) (hq : 1 < ‖q‖) :
    ‖wpT (refl p) (refl q)‖ = ‖wpT p q‖ := by
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; simp at hp; linarith
  have hq0 : q ≠ 0 := by intro h; rw [h] at hq; simp at hq; linarith
  have hden := wpcv_den_ne hp hq
  have e : p * conj q - 1 = conj (conj p * q - 1) := by simp [map_sub, mul_comm]
  have hden' : p * conj q - 1 ≠ 0 := by
    rw [e]
    refine (map_ne_zero conj).2 ?_
    intro h
    apply hden
    linear_combination -h
  have hpc : conj p ≠ 0 := (map_ne_zero conj).2 hp0
  have hqc : conj q ≠ 0 := (map_ne_zero conj).2 hq0
  have key : wpT (refl p) (refl q) = (conj p - conj q) * p / (conj p * (p * conj q - 1)) := by
    unfold wpT refl
    simp only [map_inv₀, Complex.conj_conj]
    field_simp
  rw [key, norm_div, norm_mul, norm_mul, ← map_sub, Complex.norm_conj, Complex.norm_conj]
  have e2 : ‖p * conj q - 1‖ = ‖1 - conj p * q‖ := by rw [e, Complex.norm_conj, norm_sub_rev]
  unfold wpT
  rw [norm_div, e2, norm_sub_rev q p]
  have hp1 : ‖p‖ ≠ 0 := by positivity
  have hne : ‖1 - conj p * q‖ ≠ 0 := norm_ne_zero_iff.2 hden
  field_simp

/-- **Quasi-isometry of `w_κ` on `𝔻*`.** -/
theorem wpcv_qi {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ y u : ℂ, 1 < ‖y‖ → 1 < ‖u‖ → 1 < ‖wA κ y‖ → 1 < ‖wA κ u‖ →
      ‖wpT y u‖ < t → ‖wpT (wA κ y) (wA κ u)‖ < 1 / 2 := by
  obtain ⟨t, ht0, ht1, hM⟩ := wpcv_mori hκ
  refine ⟨t, ht0, ht1, fun y u hy hu hwy hwu hyu => ?_⟩
  have hy0 : y ≠ 0 := by intro h; rw [h] at hy; simp at hy; linarith
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu; linarith
  have hwy0 : wA κ y ≠ 0 := by intro h; rw [h] at hwy; simp at hwy; linarith
  have hwu0 : wA κ u ≠ 0 := by intro h; rw [h] at hwu; simp at hwu; linarith
  have hrefl : ∀ p : ℂ, 1 < ‖p‖ → refl p ∈ unitDisc := by
    intro p hp
    have hp0 : p ≠ 0 := by intro h; rw [h] at hp; simp at hp; linarith
    simp only [unitDisc, refl, mem_ball_zero_iff, norm_inv, Complex.norm_conj]
    exact inv_lt_one_of_one_lt₀ hp
  have e1 : wA κ (refl y) = refl (wA κ y) := by
    have h := eq_1_2 hκ hy0 hwy0
    have h' : wA κ (refl y) = conj (1 / wA κ y) := by rw [h, Complex.conj_conj]
    rw [h']
    simp [refl, map_div₀]
  have e2 : wA κ (refl u) = refl (wA κ u) := by
    have h := eq_1_2 hκ hu0 hwu0
    have h' : wA κ (refl u) = conj (1 / wA κ u) := by rw [h, Complex.conj_conj]
    rw [h']
    simp [refl, map_div₀]
  have := hM (refl y) (hrefl y hy) (refl u) (hrefl u hu) (by rw [wpcv_wpT_refl hy hu]; exact hyu)
  rw [e1, e2, wpcv_wpT_refl hwy hwu] at this
  exact this

/-! ### A.e. facts, cell area, far region -/

theorem wpcv_wA_measurable {κ : LinfStar} (hκ : κ ∈ LinfStarBall) : Measurable (wA κ) := by
  obtain ⟨a, b, c, d, W, hdet, hW, hform, -⟩ := bc_wA_form hκ
  obtain ⟨K, hK⟩ := hW.1
  have hWc : Continuous W := continuousOn_univ.1 hK.2.2.1.1
  have hfun : wA κ = mobiusFn a b c d ∘ W := funext hform
  rw [hfun]
  have hM : Measurable (mobiusFn a b c d) := by unfold mobiusFn; fun_prop
  exact hM.comp hWc.measurable

theorem wpcv_norm_lt_one {κ : LinfStar} (hκ : κ ∈ LinfStarBall) : ‖κ‖ < 1 := by
  simpa [LinfStarBall] using hκ

theorem wpcv_ae_facts {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior), 1 < ‖wA κ z‖ ∧
      jacobian (wA κ) z = (1 - ‖κ z‖ ^ 2) * ‖dz (wA κ) z‖ ^ 2 ∧ ‖κ z‖ ≤ ‖κ‖ ∧ dz (wA κ) z ≠ 0 := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hw := bc_wA_ae hκ
  have hwE := bc_pullback_ae hκ (ae_restrict_mem hE)
  filter_upwards [ae_restrict_of_ae hw, ae_restrict_mem hE, hwE, LinfStar_ae_norm_le κ] with z hz3 hzE hzw hk
  obtain ⟨-, hdz, hdil, -⟩ := hz3
  have hext : extA κ z = κ z := by
    have : 1 < ‖z‖ := by simpa [unitDiscExterior] using hzE
    simp [extA, this]
  have hjac : jacobian (wA κ) z = (1 - ‖κ z‖ ^ 2) * ‖dz (wA κ) z‖ ^ 2 := by
    have hdb : dzbar (wA κ) z = κ z * dz (wA κ) z := by
      have := hdil
      unfold complexDilatation at this
      rw [hext] at this
      field_simp at this
      rw [mul_comm]
      exact this
    unfold jacobian
    rw [hdb, norm_mul]
    ring
  exact ⟨by simpa [unitDiscExterior] using hzw, hjac, hk, hdz⟩

theorem wpcv_Wl_le {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ENNReal.ofReal (‖dz (wA κ) z‖ ^ 2 * rho (wA κ z)) ≤
        ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) *
          (ENNReal.ofReal (jacobian (wA κ) z) * ENNReal.ofReal (rho (wA κ z))) := by
  have hk := wpcv_norm_lt_one hκ
  have hk0 : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
  filter_upwards [wpcv_ae_facts hκ] with z hz
  obtain ⟨-, hj, hkz, -⟩ := hz
  have hρ : 0 ≤ rho (wA κ z) := by unfold rho; positivity
  have hJ : 0 ≤ jacobian (wA κ) z := by
    rw [hj]
    have : ‖κ z‖ ^ 2 ≤ ‖κ‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
    exact mul_nonneg (by nlinarith) (sq_nonneg _)
  rw [← ENNReal.ofReal_mul hJ, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [hj, div_mul_eq_mul_div, le_div_iff₀ hk0]
  have h1 : 1 - ‖κ‖ ^ 2 ≤ 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
  have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (sq_nonneg ‖dz (wA κ) z‖) hρ)
  nlinarith [h2]

theorem wpcv_wpT_measurable (y : ℂ) : Measurable (wpT y) := by
  unfold wpT; fun_prop

theorem wpcv_wpB_measurable (y : ℂ) (s : ℝ) : MeasurableSet (wpB y s) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt (measurable_norm.comp (wpcv_wpT_measurable y)) measurable_const)

theorem wpcv_wpB_eq (y : ℂ) (s : ℝ) : wpB y s = {v | ‖wpT y v‖ < s} ∩ unitDiscExterior := by
  ext v; simp [wpB, unitDiscExterior, and_comm]

theorem wpcv_wpT_symm {u v : ℂ} : ‖wpT u v‖ = ‖wpT v u‖ := by
  unfold wpT
  rw [norm_div, norm_div, norm_sub_rev v u]
  congr 1
  have : (1 : ℂ) - conj v * u = conj (1 - conj u * v) := by simp [mul_comm]
  rw [this, Complex.norm_conj]

/-- The far region is contained in one small pseudo-hyperbolic ball. -/
theorem wpcv_far_sub {t y1 : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hy1 : 1 < y1) (hty : 3 ≤ t * y1) {u : ℂ}
    (hu : y1 ≤ ‖u‖) : u ∈ wpB (y1 : ℂ) t := by
  have hu1 : 1 < ‖u‖ := lt_of_lt_of_le hy1 hu
  refine ⟨hu1, ?_⟩
  have hn : ‖(y1 : ℂ)‖ = y1 := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hden : y1 * ‖u‖ - 1 ≤ ‖1 - conj (y1 : ℂ) * u‖ := by
    have h := norm_sub_norm_le (conj (y1 : ℂ) * u) 1
    rw [norm_mul, Complex.norm_conj, hn, norm_one] at h
    rw [norm_sub_rev]
    exact h
  have hnum : ‖u - (y1 : ℂ)‖ ≤ 2 * ‖u‖ := by
    have := norm_sub_le u (y1 : ℂ)
    rw [hn] at this
    linarith
  have hpos : 0 < ‖1 - conj (y1 : ℂ) * u‖ := by
    have : 3 * ‖u‖ - t ≤ t * (y1 * ‖u‖) - t := by nlinarith [norm_nonneg u]
    nlinarith
  unfold wpT
  rw [norm_div, div_lt_iff₀ hpos]
  have h3 : t * (y1 * ‖u‖ - 1) ≤ t * ‖1 - conj (y1 : ℂ) * u‖ := by gcongr
  nlinarith [norm_nonneg u]

theorem wpcv_pole_sub {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    {y : ℂ | y ∈ unitDiscExterior ∧ ¬ 1 < ‖wA κ y‖}.Subsingleton := by
  obtain ⟨U, K, hUo, hUE, hsub, hT, hTmaps⟩ := bc_wA_kqc hκ
  refine hsub.anti ?_
  rintro y ⟨hyE, hy⟩
  refine ⟨hyE, fun hyU => hy ?_⟩
  have := hTmaps (mem_image_of_mem _ hyU)
  simpa [unitDiscExterior] using this

theorem wpcv_ae_not_pole {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    ∀ᵐ y ∂(volume.restrict unitDiscExterior), 1 < ‖wA κ y‖ := by
  filter_upwards [wpcv_ae_facts hκ] with z hz using hz.1

/-- Hyperbolic area bound for a cell, through `w_κ`. -/
theorem wpcv_cell_area {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {t : ℝ}
    (hqi : ∀ y u : ℂ, 1 < ‖y‖ → 1 < ‖u‖ → 1 < ‖wA κ y‖ → 1 < ‖wA κ u‖ → ‖wpT y u‖ < t →
      ‖wpT (wA κ y) (wA κ u)‖ < 1 / 2)
    {y : ℂ} (hy : 1 < ‖y‖) (hwy : 1 < ‖wA κ y‖) {r : ℝ} (hr : r ≤ t) :
    ∫⁻ u in wpB y r, ENNReal.ofReal (jacobian (wA κ) u) * ENNReal.ofReal (rho (wA κ u)) ≤
      ENNReal.ofReal (4 / (1 - (1 / 2 : ℝ) ^ 2) ^ 2) * volume (ball (0 : ℂ) (1 / 2)) := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set B : Set ℂ := wpB (wA κ y) (1 / 2) with hB
  set Gf : ℂ → ℝ≥0∞ := B.indicator (fun v => ENNReal.ofReal (rho v)) with hGf
  have hlc := wpcv_lcov hκ Gf
  have hsubE : wpB y r ⊆ unitDiscExterior := fun u hu => by simpa [unitDiscExterior] using hu.1
  calc ∫⁻ u in wpB y r, ENNReal.ofReal (jacobian (wA κ) u) * ENNReal.ofReal (rho (wA κ u))
      ≤ ∫⁻ u in wpB y r, ENNReal.ofReal (jacobian (wA κ) u) * Gf (wA κ u) := by
        apply lintegral_mono_ae
        have h1 := ae_restrict_of_ae_restrict_of_subset hsubE (wpcv_ae_not_pole hκ)
        filter_upwards [h1, ae_restrict_mem (wpcv_wpB_measurable y r)] with u hu1 hu
        have hmem : wA κ u ∈ B := by
          refine ⟨hu1, ?_⟩
          exact hqi y u hy hu.1 hwy hu1 (lt_of_lt_of_le hu.2 hr)
        rw [hGf, Set.indicator_of_mem hmem]
    _ ≤ ∫⁻ u in unitDiscExterior, ENNReal.ofReal (jacobian (wA κ) u) * Gf (wA κ u) :=
        lintegral_mono_set hsubE
    _ = ∫⁻ u in unitDiscExterior, Gf u := hlc.symm
    _ ≤ ∫⁻ u, Gf u := setLIntegral_le_lintegral _ _
    _ = ∫⁻ v in B, ENNReal.ofReal (rho v) := lintegral_indicator (wpcv_wpB_measurable _ _) _
    _ ≤ _ := wpcv_wpB_area hwy (by norm_num) (by norm_num)

/-! ### Tonelli swap and the near region -/

theorem wpcv_tonelli {Wl N : ℂ → ℝ≥0∞} {s : ℝ} (hWl : Measurable Wl)
    (hN : AEMeasurable N (volume.restrict unitDiscExterior)) :
    ∫⁻ u in unitDiscExterior, Wl u * ∫⁻ v in wpB u s, N v =
      ∫⁻ v in unitDiscExterior, N v * ∫⁻ u in wpB v s, Wl u := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set ν : Measure ℂ := volume.restrict unitDiscExterior with hν
  set R : Set (ℂ × ℂ) := {p | ‖wpT p.1 p.2‖ < s} with hR
  have hwT : Measurable (fun p : ℂ × ℂ => wpT p.1 p.2) := by unfold wpT; fun_prop
  have hRm : MeasurableSet R := measurableSet_lt (measurable_norm.comp hwT) measurable_const
  set Φ : ℂ → ℂ → ℝ≥0∞ := fun u v => Wl u * R.indicator (fun _ => (1 : ℝ≥0∞)) (u, v) * N v with hΦ
  have hΦm : AEMeasurable (Function.uncurry Φ) (ν.prod ν) := by
    have h1 : Measurable fun p : ℂ × ℂ => Wl p.1 := hWl.comp measurable_fst
    have h2 : Measurable fun p : ℂ × ℂ => R.indicator (fun _ => (1 : ℝ≥0∞)) p :=
      measurable_const.indicator hRm
    have h3 : AEMeasurable (fun p : ℂ × ℂ => N p.2) (ν.prod ν) :=
      hN.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    exact (h1.mul h2).aemeasurable.mul h3
  have e1 : ∫⁻ u in unitDiscExterior, Wl u * ∫⁻ v in wpB u s, N v = ∫⁻ u, ∫⁻ v, Φ u v ∂ν ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hE] with u hu
    have hS : MeasurableSet {v : ℂ | ‖wpT u v‖ < s} :=
      measurableSet_lt (measurable_norm.comp (wpcv_wpT_measurable u)) measurable_const
    have hpt : ∀ v, Φ u v = Wl u * {v : ℂ | ‖wpT u v‖ < s}.indicator N v := by
      intro v
      by_cases h : ‖wpT u v‖ < s
      · have : (u, v) ∈ R := h
        simp [hΦ, Set.indicator_of_mem this, Set.indicator_of_mem (show v ∈ {v : ℂ | ‖wpT u v‖ < s} from h)]
      · have : (u, v) ∉ R := h
        simp [hΦ, Set.indicator_of_notMem this,
          Set.indicator_of_notMem (show v ∉ {v : ℂ | ‖wpT u v‖ < s} from h)]
    simp_rw [hpt]
    rw [lintegral_const_mul'' _ (hN.indicator hS), lintegral_indicator hS, hν,
      Measure.restrict_restrict hS, ← wpcv_wpB_eq]
  have e2 : ∫⁻ v in unitDiscExterior, N v * ∫⁻ u in wpB v s, Wl u = ∫⁻ v, ∫⁻ u, Φ u v ∂ν ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hE] with v hv
    have hS : MeasurableSet {u : ℂ | ‖wpT v u‖ < s} :=
      measurableSet_lt (measurable_norm.comp (wpcv_wpT_measurable v)) measurable_const
    have hpt : ∀ u, Φ u v = N v * {u : ℂ | ‖wpT v u‖ < s}.indicator Wl u := by
      intro u
      by_cases h : ‖wpT v u‖ < s
      · have : (u, v) ∈ R := by show ‖wpT u v‖ < s; rw [wpcv_wpT_symm]; exact h
        simp [hΦ, Set.indicator_of_mem this, Set.indicator_of_mem (show u ∈ {u : ℂ | ‖wpT v u‖ < s} from h),
          mul_comm, mul_left_comm]
      · have : (u, v) ∉ R := by
          show ¬ ‖wpT u v‖ < s
          rw [wpcv_wpT_symm]; exact h
        simp [hΦ, Set.indicator_of_notMem this,
          Set.indicator_of_notMem (show u ∉ {u : ℂ | ‖wpT v u‖ < s} from h)]
    simp_rw [hpt]
    rw [lintegral_const_mul'' _ (hWl.indicator hS).aemeasurable, lintegral_indicator hS, hν,
      Measure.restrict_restrict hS, ← wpcv_wpB_eq]
  rw [e1, e2]
  exact lintegral_lintegral_swap hΦm

theorem wpcv_near {μ φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDiscExterior)
    (hrep : ∀ z ∈ unitDiscExterior, μ z = ((rho z : ℝ) : ℂ)⁻¹ * conj (φ z))
    {s Y : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsY : s * Y ≤ 1)
    {Wl : ℂ → ℝ≥0∞} (hWl : Measurable Wl) {A : ℝ≥0∞} (hAtop : A ≠ ∞)
    (hA : ∀ᵐ v ∂(volume.restrict unitDiscExterior), ∫⁻ u in wpB v s, Wl u ≤ A)
    (hN : AEMeasurable (fun v => (‖μ v‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho v))
      (volume.restrict unitDiscExterior)) :
    ∫⁻ u in unitDiscExterior ∩ {u | ‖u‖ < Y}, (‖μ u‖₊ : ℝ≥0∞) ^ 2 * Wl u ≤
      ENNReal.ofReal (3 / (4 * π * s ^ 2 * (1 - s ^ 2) ^ 2)) * A *
        ∫⁻ v in unitDiscExterior, (‖μ v‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho v) := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set N : ℂ → ℝ≥0∞ := fun v => (‖μ v‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho v) with hNdef
  set cs : ℝ≥0∞ := ENNReal.ofReal (3 / (4 * π * s ^ 2 * (1 - s ^ 2) ^ 2)) with hcs
  calc ∫⁻ u in unitDiscExterior ∩ {u | ‖u‖ < Y}, (‖μ u‖₊ : ℝ≥0∞) ^ 2 * Wl u
      ≤ ∫⁻ u in unitDiscExterior ∩ {u | ‖u‖ < Y}, cs * (Wl u * ∫⁻ v in wpB u s, N v) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (hE.inter (measurableSet_lt measurable_norm measurable_const))]
          with u hu
        have hy : 1 < ‖u‖ := by simpa [unitDiscExterior] using hu.1
        have hsy : s * ‖u‖ ≤ 1 := by
          have : ‖u‖ ≤ Y := le_of_lt hu.2
          nlinarith
        have := wpcv_mu_mean hφ hrep hy hs0 hs1 hsy
        calc (‖μ u‖₊ : ℝ≥0∞) ^ 2 * Wl u ≤ (cs * ∫⁻ v in wpB u s, N v) * Wl u := by gcongr
          _ = cs * (Wl u * ∫⁻ v in wpB u s, N v) := by ring
    _ ≤ ∫⁻ u in unitDiscExterior, cs * (Wl u * ∫⁻ v in wpB u s, N v) :=
        lintegral_mono_set inter_subset_left
    _ = cs * ∫⁻ u in unitDiscExterior, Wl u * ∫⁻ v in wpB u s, N v :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = cs * ∫⁻ v in unitDiscExterior, N v * ∫⁻ u in wpB v s, Wl u := by
        rw [wpcv_tonelli hWl hN]
    _ ≤ cs * ∫⁻ v in unitDiscExterior, N v * A := by
        refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
        filter_upwards [hA] with v hv
        exact mul_le_mul' le_rfl hv
    _ = cs * A * ∫⁻ v in unitDiscExterior, N v := by
        rw [lintegral_mul_const'' _ hN]
        ring

/-! ### The weighted `L²` integral of `R(μ, κ)` -/

theorem wpcv_RnmFun_ae {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (ν : LinfStar) :
    (⇑(Rnm ν κ) : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] RnmFun ν κ :=
  bc_Rnm_ae hκ ν

theorem wpcv_R_lintegral {μ : ℂ → ℂ} (hto : (toLinf μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] μ)
    {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    ∫⁻ z in unitDiscExterior, (‖(Rnm (toLinf μ) κ : ℂ → ℂ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
      ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) *
        ∫⁻ z in unitDiscExterior, (‖μ z‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal (‖dz (wA κ) z‖ ^ 2 * rho (wA κ z)) := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hk := wpcv_norm_lt_one hκ
  have hk0 : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
  rw [wpcv_lcov hκ (fun u => (‖(Rnm (toLinf μ) κ : ℂ → ℂ) u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  have hR1 := bc_pullback_ae hκ (wpcv_RnmFun_ae hκ (toLinf μ))
  filter_upwards [wpcv_ae_facts hκ, hR1, hto, ae_restrict_mem hE] with z hz hRz hμz hzE
  obtain ⟨hw1, hj, hkz, hdz⟩ := hz
  have hwn : wA κ z ≠ 0 := by intro h; rw [h] at hw1; simp at hw1; linarith
  have hkz1 : ‖κ z‖ < 1 := lt_of_le_of_lt hkz hk
  have ha : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
  have hc : conj (dz (wA κ) z) ≠ 0 := by simpa using hdz
  have hRn : ‖(Rnm (toLinf μ) κ : ℂ → ℂ) (wA κ z)‖ = ‖μ z‖ / (1 - ‖κ z‖ ^ 2) := by
    rw [hRz]
    show ‖(fun u => (toLinf μ) u / (1 - ‖κ u‖ ^ 2) * (dz (wA κ) u / conj (dz (wA κ) u)))
      (Function.invFun (wA κ) (wA κ z))‖ = _
    rw [bc_invFun_wA hwn]
    simp only [hμz]
    rw [norm_mul, norm_div, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hdz), mul_one]
    congr 1
    have : (1 - (‖κ z‖ : ℂ) ^ 2) = ((1 - ‖κ z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hρw : 0 ≤ rho (wA κ z) := by unfold rho; positivity
  have hJ : 0 ≤ jacobian (wA κ) z := by rw [hj]; exact mul_nonneg ha.le (sq_nonneg _)
  have e1 : ∀ x : ℂ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
    intro x; rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  show ENNReal.ofReal (jacobian (wA κ) z) *
      ((‖(Rnm (toLinf μ) κ : ℂ → ℂ) (wA κ z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho (wA κ z))) ≤
    ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) *
      ((‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (‖dz (wA κ) z‖ ^ 2 * rho (wA κ z)))
  rw [e1, e1, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hJ,
    ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [hRn, hj, div_pow]
  have h1 : 1 - ‖κ‖ ^ 2 ≤ 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
  have key : (1 - ‖κ z‖ ^ 2) * ‖dz (wA κ) z‖ ^ 2 * (‖μ z‖ ^ 2 / (1 - ‖κ z‖ ^ 2) ^ 2 * rho (wA κ z)) =
      ‖μ z‖ ^ 2 * (‖dz (wA κ) z‖ ^ 2 * rho (wA κ z)) / (1 - ‖κ z‖ ^ 2) := by
    field_simp
  have hX : 0 ≤ ‖μ z‖ ^ 2 * (‖dz (wA κ) z‖ ^ 2 * rho (wA κ z)) := by positivity
  rw [key]
  calc ‖μ z‖ ^ 2 * (‖dz (wA κ) z‖ ^ 2 * rho (wA κ z)) / (1 - ‖κ z‖ ^ 2)
      ≤ ‖μ z‖ ^ 2 * (‖dz (wA κ) z‖ ^ 2 * rho (wA κ z)) / (1 - ‖κ‖ ^ 2) :=
        div_le_div_of_nonneg_left hX hk0 h1
    _ = 1 / (1 - ‖κ‖ ^ 2) * (‖μ z‖ ^ 2 * (‖dz (wA κ) z‖ ^ 2 * rho (wA κ z))) := by ring

/-! ### `R(μ, κ) ∈ L²(𝔻*, ρ)` -/

theorem x5_lintegral_lt_top {f : ℂ → ℂ} (h : normL2 unitDiscExterior f < ∞) :
    ∫⁻ z in unitDiscExterior, (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) < ∞ := by
  unfold normL2 at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h

theorem x5_Rnm_L2 {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {κ : LinfStar}
    (hκ : κ ∈ LinfStarBall) : normL2 unitDiscExterior (Rnm (toLinf μ) κ) < ∞ := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hμ' := hμ
  obtain ⟨φ, hφ, hrep, hfin⟩ := hμ'
  obtain ⟨t, ht0, ht1, hqi⟩ := wpcv_qi hκ
  set Y : ℝ := 6 / t with hY
  set s : ℝ := t / 6 with hs
  have hs0 : 0 < s := by positivity
  have hst : s ≤ t := by rw [hs]; linarith
  have hs1 : s < 1 := lt_of_le_of_lt hst ht1
  have hsY : s * Y ≤ 1 := by rw [hs, hY]; field_simp; exact le_rfl
  have hk := wpcv_norm_lt_one hκ
  have hk0 : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
  set Wl : ℂ → ℝ≥0∞ := fun u => ENNReal.ofReal (‖dz (wA κ) u‖ ^ 2 * rho (wA κ u)) with hWldef
  have hWl : Measurable Wl := by
    have hr : Measurable rho := by unfold rho; fun_prop
    exact ENNReal.measurable_ofReal.comp
      (((measurable_dz (wA κ)).norm.pow_const 2).mul (hr.comp (wpcv_wA_measurable hκ)))
  set C0 : ℝ≥0∞ := ENNReal.ofReal (4 / (1 - (1 / 2 : ℝ) ^ 2) ^ 2) * volume (ball (0 : ℂ) (1 / 2)) with hC0
  set A : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) * C0 with hA
  have hAtop : A ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
  have hcell : ∀ y : ℂ, 1 < ‖y‖ → 1 < ‖wA κ y‖ → ∀ r : ℝ, r ≤ t → ∫⁻ u in wpB y r, Wl u ≤ A := by
    intro y hy hwy r hr
    have hsubE : wpB y r ⊆ unitDiscExterior := fun u hu => by simpa [unitDiscExterior] using hu.1
    calc ∫⁻ u in wpB y r, Wl u
        ≤ ∫⁻ u in wpB y r, ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) *
            (ENNReal.ofReal (jacobian (wA κ) u) * ENNReal.ofReal (rho (wA κ u))) :=
          lintegral_mono_ae (ae_restrict_of_ae_restrict_of_subset hsubE (wpcv_Wl_le hκ))
      _ = ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) *
            ∫⁻ u in wpB y r, ENNReal.ofReal (jacobian (wA κ) u) * ENNReal.ofReal (rho (wA κ u)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ A := mul_le_mul' le_rfl (wpcv_cell_area hκ hqi hy hwy hr)
  have hA_ae : ∀ᵐ v ∂(volume.restrict unitDiscExterior), ∫⁻ u in wpB v s, Wl u ≤ A := by
    filter_upwards [ae_restrict_mem hE, wpcv_ae_not_pole hκ] with v hv hw
    exact hcell v (by simpa [unitDiscExterior] using hv) hw s hst
  have hcont := wp_harmonic_continuousOn hμ
  have hN : AEMeasurable (fun v => (‖μ v‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho v))
      (volume.restrict unitDiscExterior) := by
    have hrm : Measurable fun z : ℂ => ENNReal.ofReal (rho z) := by unfold rho; fun_prop
    exact (((hcont.aestronglyMeasurable hE).aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2).mul
      hrm.aemeasurable
  have hnear := wpcv_near hφ hrep hs0 hs1 hsY hWl hAtop hA_ae hN
  -- the far region sits in one small pseudo-hyperbolic ball
  obtain ⟨y1, hty, hy1, hy1Y, hwy1⟩ : ∃ y1 : ℝ, 3 ≤ t * y1 ∧ 1 < y1 ∧ y1 ≤ Y ∧ 1 < ‖wA κ (y1 : ℂ)‖ := by
    have hn : ∀ x : ℝ, 0 < x → ‖(x : ℂ)‖ = x := fun x hx => by
      rw [Complex.norm_real, Real.norm_of_nonneg hx.le]
    have h3 : 1 < 3 / t := by rw [lt_div_iff₀ ht0]; linarith
    have h6 : 1 < Y := by rw [hY, lt_div_iff₀ ht0]; linarith
    by_cases h0 : 1 < ‖wA κ ((3 / t : ℝ) : ℂ)‖
    · refine ⟨3 / t, ?_, h3, ?_, h0⟩
      · rw [mul_div_cancel₀ _ ht0.ne']
      · rw [hY]; gcongr; norm_num
    · refine ⟨Y, ?_, h6, le_rfl, ?_⟩
      · rw [hY, mul_div_cancel₀ _ ht0.ne']; norm_num
      · by_contra h1
        have hsub := wpcv_pole_sub hκ
        have hmemE : ∀ x : ℝ, 1 < x → ((x : ℝ) : ℂ) ∈ unitDiscExterior := fun x hx => by
          show 1 < ‖(x : ℂ)‖
          rw [hn x (by linarith)]; exact hx
        have := hsub ⟨hmemE _ h3, h0⟩ ⟨hmemE _ h6, h1⟩
        have h2 : (3 / t : ℝ) = Y := Complex.ofReal_injective this
        rw [hY] at h2
        have : (3 : ℝ) = 6 := by
          field_simp at h2; linarith
        norm_num at this
  have hfar_sub : unitDiscExterior ∩ {u | ¬ ‖u‖ < Y} ⊆ wpB (y1 : ℂ) t := by
    rintro u ⟨-, hu⟩
    exact wpcv_far_sub ht0 ht1 hy1 hty (le_trans hy1Y (not_lt.1 hu))
  set M : ℝ := (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior μ).toReal with hM
  have hfar : ∫⁻ u in unitDiscExterior ∩ {u | ¬ ‖u‖ < Y}, (‖μ u‖₊ : ℝ≥0∞) ^ 2 * Wl u ≤
      ENNReal.ofReal (M ^ 2) * A := by
    calc ∫⁻ u in unitDiscExterior ∩ {u | ¬ ‖u‖ < Y}, (‖μ u‖₊ : ℝ≥0∞) ^ 2 * Wl u
        ≤ ∫⁻ u in unitDiscExterior ∩ {u | ¬ ‖u‖ < Y}, ENNReal.ofReal (M ^ 2) * Wl u := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left
            (ae_restrict_mem hE)] with u hu
          have hb := wp_harmonic_pointwise_bound hμ hu
          have : (‖μ u‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (M ^ 2) := by
            have e : (‖μ u‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖μ u‖ ^ 2) := by
              rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
            rw [e]
            exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hb 2)
          exact mul_le_mul' this le_rfl
      _ = ENNReal.ofReal (M ^ 2) * ∫⁻ u in unitDiscExterior ∩ {u | ¬ ‖u‖ < Y}, Wl u :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ u in wpB (y1 : ℂ) t, Wl u :=
          mul_le_mul' le_rfl (lintegral_mono_set hfar_sub)
      _ ≤ ENNReal.ofReal (M ^ 2) * A :=
          mul_le_mul' le_rfl (hcell _ (by
            have : 1 < y1 := hy1
            rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact this) hwy1 t le_rfl)
  have hΛ : ∫⁻ u in unitDiscExterior, (‖μ u‖₊ : ℝ≥0∞) ^ 2 * Wl u < ∞ := by
    have hsub : unitDiscExterior ⊆ (unitDiscExterior ∩ {u | ‖u‖ < Y}) ∪
        (unitDiscExterior ∩ {u | ¬ ‖u‖ < Y}) := by
      intro u hu
      by_cases h : ‖u‖ < Y
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hu, h⟩
    refine lt_of_le_of_lt ((lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)) ?_
    refine ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt hnear ?_, lt_of_le_of_lt hfar ?_⟩
    · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAtop.lt_top)
        (x5_lintegral_lt_top hfin)
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAtop.lt_top
  have hR := wpcv_R_lintegral (wp_harmonic_toLinf_ae hμ) hκ
  unfold normL2
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  exact (lt_of_le_of_lt hR (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΛ)).ne

/-- Area change of variables for a holomorphic injection (copy of the conformal case). -/
theorem wpcv_conformal {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hi : InjOn f U) (ψ : ℂ → ℂ) :
    (∫ z in f '' U, ψ z) = ∫ z in U, (‖deriv f z‖ ^ 2 : ℂ) * ψ (f z) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet
    (fun z hz => ((hd.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hi ψ]
  apply setIntegral_congr_fun hU.measurableSet
  intro z _
  dsimp only
  rw [det_restrictScalars_toSpanSingleton, abs_of_nonneg (sq_nonneg _)]
  simp [Complex.real_smul]

/-- Möbius change of variables onto the exterior disc. -/
theorem wpcv_mobius {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) (G : ℂ → ℂ) :
    (∫ u in unitDiscExterior, G u) =
      ∫ v in {v : ℂ | c * v + d ≠ 0 ∧ mobiusFn a b c d v ∈ unitDiscExterior},
        (‖(a * d - b * c) / (c * v + d) ^ 2‖ ^ 2 : ℂ) * G (mobiusFn a b c d v) := by
  set S : Set ℂ := {v : ℂ | c * v + d ≠ 0 ∧ mobiusFn a b c d v ∈ unitDiscExterior} with hS
  have hP : IsOpen {v : ℂ | c * v + d ≠ 0} := by
    apply isOpen_ne_fun (by fun_prop) (by fun_prop)
  have hMc : ContinuousOn (mobiusFn a b c d) {v : ℂ | c * v + d ≠ 0} := by
    intro v hv
    exact (bc_mobiusFn_hasDerivAt (z := v) hv).continuousAt.continuousWithinAt
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hSo : IsOpen S := by
    have := hMc.isOpen_inter_preimage hP hE
    convert this using 1
    ext v; simp [hS, and_comm]
  have hPS : ∀ v ∈ S, c * v + d ≠ 0 := fun v hv => hv.1
  have hdiff : DifferentiableOn ℂ (mobiusFn a b c d) S := fun v hv =>
    (bc_mobiusFn_hasDerivAt (hPS v hv)).differentiableAt.differentiableWithinAt
  have hinj : InjOn (mobiusFn a b c d) S := bc_mobiusFn_injOn hdet hPS
  have hder : ∀ v ∈ S, deriv (mobiusFn a b c d) v = (a * d - b * c) / (c * v + d) ^ 2 :=
    fun v hv => (bc_mobiusFn_hasDerivAt (hPS v hv)).deriv
  -- the image is the exterior disc up to a null set
  have himg : mobiusFn a b c d '' S ⊆ unitDiscExterior := by
    rintro _ ⟨v, hv, rfl⟩; exact hv.2
  have hnull : (volume : Measure ℂ) (unitDiscExterior \ mobiusFn a b c d '' S) = 0 := by
    have hsub : unitDiscExterior \ mobiusFn a b c d '' S ⊆ {u : ℂ | c * u = a} := by
      intro u hu
      by_contra hcu
      simp only [mem_setOf_eq] at hcu
      apply hu.2
      have hne : a - c * u ≠ 0 := fun h => hcu (by linear_combination -h)
      have hne' : a - u * c ≠ 0 := by rwa [mul_comm u c]
      refine ⟨(d * u - b) / (a - c * u), ⟨?_, ?_⟩, ?_⟩
      · have : c * ((d * u - b) / (a - c * u)) + d = (a * d - b * c) / (a - c * u) := by
          field_simp; ring
        rw [this]; exact div_ne_zero hdet hne
      · have h1 : c * ((d * u - b) / (a - c * u)) + d = (a * d - b * c) / (a - c * u) := by
          field_simp; ring
        have h2 : mobiusFn a b c d ((d * u - b) / (a - c * u)) = u := by
          unfold mobiusFn
          rw [h1]
          field_simp
          ring
        rw [h2]; exact hu.1
      · unfold mobiusFn
        have h1 : c * ((d * u - b) / (a - c * u)) + d = (a * d - b * c) / (a - c * u) := by
          field_simp; ring
        rw [h1]; field_simp; ring
    refine measure_mono_null hsub ?_
    by_cases hc : c = 0
    · have ha : a ≠ 0 := by
        intro h; apply hdet; rw [hc, h]; ring
      have : {u : ℂ | c * u = a} = ∅ := by
        ext u; simp [hc, Ne.symm ha]
      rw [this]; exact measure_empty
    · have : {u : ℂ | c * u = a} = {a / c} := by
        ext u; simp only [mem_setOf_eq, mem_singleton_iff]
        constructor
        · intro h; field_simp; linear_combination h
        · intro h; rw [h]; field_simp
      rw [this]; exact measure_singleton _
  have hae : (mobiusFn a b c d '' S : Set ℂ) =ᵐ[volume] unitDiscExterior := by
    refine (ae_eq_set.mpr ⟨?_, ?_⟩)
    · rw [diff_eq_empty.mpr himg]; exact measure_empty
    · exact hnull
  have h1 := wpcv_conformal hSo hdiff hinj G
  rw [setIntegral_congr_set hae.symm]
  rw [h1]
  apply setIntegral_congr_fun hSo.measurableSet
  intro v hv
  dsimp only
  rw [hder v hv]


theorem wpcv_cov {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (G : ℂ → ℂ) (hG : Measurable G) :
    (∫ u in unitDiscExterior, G u) =
      ∫ z in unitDiscExterior, (jacobian (wA κ) z : ℂ) * G (wA κ z) := by
  obtain ⟨a, b, c, d, W, hdet, hW, hform, hcoe⟩ := bc_wA_form hκ
  obtain ⟨K, hK⟩ := hW.1
  have himg : W '' univ = univ := hW.2.1
  have hinj : Function.Injective W := fun x y h => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) h
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  set S : Set ℂ := {v : ℂ | c * v + d ≠ 0 ∧ mobiusFn a b c d v ∈ unitDiscExterior} with hS
  have hP : IsOpen {v : ℂ | c * v + d ≠ 0} := isOpen_ne_fun (by fun_prop) (by fun_prop)
  have hMc : ContinuousOn (mobiusFn a b c d) {v : ℂ | c * v + d ≠ 0} := fun v hv =>
    (bc_mobiusFn_hasDerivAt (z := v) hv).continuousAt.continuousWithinAt
  have hSo : IsOpen S := by
    have := hMc.isOpen_inter_preimage hP hE
    convert this using 1
    ext v; simp [hS, and_comm]
  have hMm : Measurable (mobiusFn a b c d) := by unfold mobiusFn; fun_prop
  have hdm : Measurable fun v : ℂ => (‖(a * d - b * c) / (c * v + d) ^ 2‖ ^ 2 : ℂ) := by fun_prop
  set H : ℂ → ℂ := S.indicator (fun v => (‖(a * d - b * c) / (c * v + d) ^ 2‖ ^ 2 : ℂ) *
    G (mobiusFn a b c d v)) with hH
  have hHm : Measurable H := (hdm.mul (hG.comp hMm)).indicator hSo.measurableSet
  have e1 : (∫ u in unitDiscExterior, G u) = ∫ v, H v := by
    rw [wpcv_mobius hdet G, hH, integral_indicator hSo.measurableSet]
  have e2 := qcv_cov_integral hK himg H hHm.aestronglyMeasurable
  rw [e1, e2, ← integral_indicator hE.measurableSet]
  apply integral_congr_ae
  have hgood := s23_c2_ae_good hK
  rw [Measure.restrict_univ] at hgood
  have hnull : ∀ᵐ z : ℂ, c * W z + d ≠ 0 := by
    by_cases hc : c = 0
    · have hd : d ≠ 0 := by
        intro h; apply hdet; rw [hc, h]; ring
      exact Eventually.of_forall fun z => by rw [hc, zero_mul, zero_add]; exact hd
    · have hsub : {z : ℂ | c * W z + d = 0} ⊆ {z | W z = -d / c} := by
        intro z hz
        simp only [mem_setOf_eq] at hz ⊢
        field_simp
        linear_combination hz
      have : (volume : Measure ℂ) {z : ℂ | c * W z + d = 0} = 0 :=
        measure_mono_null hsub (Set.Subsingleton.measure_zero
          (fun x hx y hy => hinj (hx.trans hy.symm)) volume)
      exact measure_eq_zero_iff_ae_notMem.mp this
  filter_upwards [hgood, hnull] with z hz1 hz3
  obtain ⟨hdiff, hlt, -⟩ := hz1
  have hg : DifferentiableAt ℂ (mobiusFn a b c d) (W z) :=
    (bc_mobiusFn_hasDerivAt hz3).differentiableAt
  have hfun : wA κ = mobiusFn a b c d ∘ W := funext hform
  have hch := eq6_5 hdiff hg
  have hder : deriv (mobiusFn a b c d) (W z) = (a * d - b * c) / (c * W z + d) ^ 2 :=
    (bc_mobiusFn_hasDerivAt hz3).deriv
  have hjac : jacobian (wA κ) z = ‖(a * d - b * c) / (c * W z + d) ^ 2‖ ^ 2 * jacobian W z := by
    unfold jacobian
    rw [hfun, hch.1, hch.2, hder, norm_mul, norm_mul]
    ring
  have hJ0 : 0 ≤ jacobian W z := by
    unfold jacobian
    have := norm_nonneg (dzbar W z)
    nlinarith
  have hmem := wpcv_mem_iff hκ hcoe hz3
  show (ENNReal.ofReal (jacobian W z)).toReal • H (W z) =
    unitDiscExterior.indicator (fun z => (jacobian (wA κ) z : ℂ) * G (wA κ z)) z
  rw [ENNReal.toReal_ofReal hJ0, Complex.real_smul]
  by_cases hz : z ∈ unitDiscExterior
  · have hWz : W z ∈ S := ⟨hz3, hmem.mpr hz⟩
    rw [Set.indicator_of_mem hz, hH, Set.indicator_of_mem hWz, hjac, hform z]
    push_cast
    ring
  · have hWz : W z ∉ S := fun h => hz (hmem.mp h.2)
    rw [Set.indicator_of_notMem hz, hH, Set.indicator_of_notMem hWz, mul_zero]

/-- `P m` is a.e. the pointwise integral formula (via `Λ ∘ D₀β`). -/
theorem wpcv_P_ae (m : LinfStar) :
    (⇑(harmonicProj m) : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior]
      fun z => harmonicProjFun (⇑m) z := by
  rw [hp_eq_Lambda m]
  refine (Lambda_coe_ae _).trans ?_
  filter_upwards [ae_restrict_mem (isOpen_lt continuous_const continuous_norm : IsOpen unitDiscExterior).measurableSet]
    with z hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num [unitDiscExterior] at hz
  have hc : conj z ≠ 0 := (map_ne_zero conj).2 hz0
  have hw : refl z ∈ unitDisc := (refl_mem_disc_iff hz0).2 hz
  have h14 := eq_1_4 m (refl z) hw
  show -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 * AInf.toFun (fderiv ℂ bersPhi 0 m) (refl z) / conj z ^ 4 =
    3 * (1 - ‖z‖ ^ 2) ^ 2 / π * ∫ ζ in unitDiscExterior, m ζ / (1 - ζ * conj z) ^ 4
  rw [h14]
  have hint : ∫ ζ in unitDiscExterior, m ζ / (1 - ζ * conj z) ^ 4 =
      ((conj z)⁻¹) ^ 4 * ∫ ζ in unitDiscExterior, m ζ / (ζ - refl z) ^ 4 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    show m ζ / (1 - ζ * conj z) ^ 4 = ((conj z)⁻¹) ^ 4 * (m ζ / (ζ - refl z) ^ 4)
    have h1 : 1 - ζ * conj z = -conj z * (ζ - (conj z)⁻¹) := by
      field_simp
      ring
    unfold refl
    rw [h1, show (-conj z * (ζ - (conj z)⁻¹)) ^ 4 = conj z ^ 4 * (ζ - (conj z)⁻¹) ^ 4 by ring]
    simp only [div_eq_mul_inv, mul_inv, inv_pow]
    ring
  rw [hint]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring


/-- The `P` of `R(ν, κ)` is a.e. the integral formula applied to the explicit `RnmFun`. -/
theorem wpcv_P_Rnm_ae {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (ν : LinfStar) :
    (⇑(harmonicProj (Rnm ν κ)) : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior]
      fun z => harmonicProjFun (RnmFun ν κ) z := by
  refine (wpcv_P_ae (Rnm ν κ)).trans ?_
  refine Filter.Eventually.of_forall fun z => ?_
  show harmonicProjFun (⇑(Rnm ν κ)) z = harmonicProjFun (RnmFun ν κ) z
  unfold harmonicProjFun
  congr 1
  apply integral_congr_ae
  filter_upwards [wpcv_RnmFun_ae hκ ν] with ζ hζ
  rw [hζ]

/-- **Line 1 of (7.7)**: change of variables `u = w_κ(z)` in the Weil–Petersson integral. -/
theorem x5_gWP_eq_Q (μ ν : ℂ → ℂ) {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    gWP μ ν κ = ∫ z in unitDiscExterior, Qfun (toLinf μ) κ z * conj (Qfun (toLinf ν) κ z) *
      (1 - ‖κ z‖ ^ 2) * (rho (wA κ z) * ‖dz (wA κ) z‖ ^ 2) := by
  set h1 : ℂ → ℂ := ⇑(harmonicProj (Rnm (toLinf μ) κ)) with hh1
  set h2 : ℂ → ℂ := ⇑(harmonicProj (Rnm (toLinf ν) κ)) with hh2
  have hm1 : Measurable h1 := (Lp.stronglyMeasurable _).measurable
  have hm2 : Measurable h2 := (Lp.stronglyMeasurable _).measurable
  have hrho : Measurable fun u : ℂ => ((rho u : ℝ) : ℂ) := by unfold rho; fun_prop
  have hG : Measurable fun u : ℂ => h1 u * conj (h2 u) * ((rho u : ℝ) : ℂ) :=
    (hm1.mul (continuous_conj.measurable.comp hm2)).mul hrho
  have hcov := wpcv_cov hκ _ hG
  have hLHS : gWP μ ν κ = ∫ u in unitDiscExterior, h1 u * conj (h2 u) * ((rho u : ℝ) : ℂ) := rfl
  rw [hLHS, hcov]
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  -- transport the a.e. identities along `w_κ`
  have hP1 := bc_pullback_ae hκ (wpcv_P_Rnm_ae hκ (toLinf μ))
  have hP2 := bc_pullback_ae hκ (wpcv_P_Rnm_ae hκ (toLinf ν))
  have hw := bc_wA_ae hκ
  apply integral_congr_ae
  filter_upwards [hP1, hP2, ae_restrict_of_ae hw, ae_restrict_mem hE] with z hz1 hz2 hz3 hzE
  obtain ⟨-, hdz, hdil, -⟩ := hz3
  have hext : extA κ z = κ z := by
    have : 1 < ‖z‖ := by simpa [unitDiscExterior] using hzE
    simp [extA, this]
  have hjac : jacobian (wA κ) z = (1 - ‖κ z‖ ^ 2) * ‖dz (wA κ) z‖ ^ 2 := by
    have hdb : dzbar (wA κ) z = κ z * dz (wA κ) z := by
      have := hdil
      unfold complexDilatation at this
      rw [hext] at this
      field_simp at this
      rw [mul_comm]
      exact this
    unfold jacobian
    rw [hdb, norm_mul]
    ring
  have hph : conj (dz (wA κ) z) / dz (wA κ) z * conj (conj (dz (wA κ) z) / dz (wA κ) z) = 1 := by
    have hc : conj (dz (wA κ) z) ≠ 0 := by simpa using hdz
    simp only [map_div₀, Complex.conj_conj]
    field_simp
  simp only [Qfun]
  rw [hjac]
  change ((((1 - ‖κ z‖ ^ 2) * ‖dz (wA κ) z‖ ^ 2 : ℝ)) : ℂ) * (h1 (wA κ z) * conj (h2 (wA κ z)) * ((rho (wA κ z) : ℝ) : ℂ)) = _
  rw [show h1 (wA κ z) = _ from hz1, show h2 (wA κ z) = _ from hz2]
  set P1 := harmonicProjFun (RnmFun (toLinf μ) κ) (wA κ z)
  set P2 := harmonicProjFun (RnmFun (toLinf ν) κ) (wA κ z)
  have : P1 * (conj (dz (wA κ) z) / dz (wA κ) z) * conj (P2 * (conj (dz (wA κ) z) / dz (wA κ) z)) =
      P1 * conj P2 := by
    rw [map_mul]
    calc _ = P1 * conj P2 * (conj (dz (wA κ) z) / dz (wA κ) z * conj (conj (dz (wA κ) z) / dz (wA κ) z)) := by ring
      _ = _ := by rw [hph, mul_one]
  rw [this]
  push_cast
  ring



theorem x5_normL2_congr {f g : ℂ → ℂ} (h : f =ᵐ[volume.restrict unitDiscExterior] g) :
    normL2 unitDiscExterior f = normL2 unitDiscExterior g := by
  unfold normL2
  congr 1
  apply lintegral_congr_ae
  filter_upwards [h] with z hz
  rw [hz]

theorem x5_ennreal_mul_le (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

theorem x5_inner_integrable {f g : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    (hg : AEStronglyMeasurable g (volume.restrict unitDiscExterior))
    (hfn : normL2 unitDiscExterior f < ∞) (hgn : normL2 unitDiscExterior g < ∞) :
    Integrable (fun z => f z * conj (g z) * ((rho z : ℝ) : ℂ)) (volume.restrict unitDiscExterior) := by
  have hrho : Measurable fun u : ℂ => ((rho u : ℝ) : ℂ) := by unfold rho; fun_prop
  refine ⟨(hf.mul (continuous_conj.comp_aestronglyMeasurable hg)).mul hrho.aestronglyMeasurable, ?_⟩
  have h1 := x5_lintegral_lt_top hfn
  have h2 := x5_lintegral_lt_top hgn
  have hrm : Measurable fun z : ℂ => ENNReal.ofReal (rho z) := by unfold rho; fun_prop
  have hA : AEMeasurable (fun z => (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z))
      (volume.restrict unitDiscExterior) :=
    ((hf.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2).mul hrm.aemeasurable
  unfold HasFiniteIntegral
  have hle : ∀ z, ‖f z * conj (g z) * ((rho z : ℝ) : ℂ)‖ₑ ≤
      (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) + (‖g z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) := by
    intro z
    have hr : 0 ≤ rho z := by unfold rho; positivity
    have : ‖f z * conj (g z) * ((rho z : ℝ) : ℂ)‖ₑ = (‖f z‖₊ : ℝ≥0∞) * (‖g z‖₊ : ℝ≥0∞) * ENNReal.ofReal (rho z) := by
      rw [enorm_mul, enorm_mul, RCLike.enorm_conj, ← ofReal_norm_eq_enorm ((rho z : ℝ) : ℂ), Complex.norm_real,
        Real.norm_of_nonneg hr]
      rfl
    rw [this, ← add_mul]
    gcongr
    exact x5_ennreal_mul_le _ _
  calc ∫⁻ z in unitDiscExterior, ‖f z * conj (g z) * ((rho z : ℝ) : ℂ)‖ₑ ∂volume
      ≤ ∫⁻ z in unitDiscExterior, ((‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) +
          (‖g z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) := lintegral_mono hle
    _ = _ := lintegral_add_left' hA _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨h1, h2⟩

/-- Second equation of (7.7). -/
theorem x5_line2 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    gWP μ ν κ = ∫ z in unitDiscExterior, μ z * conj (Qfun (toLinf ν) κ z) * (rho (wA κ z) * ‖dz (wA κ) z‖ ^ 2) := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set m : ℂ → ℂ := ⇑(Rnm (toLinf μ) κ) with hm
  set h1 : ℂ → ℂ := ⇑(harmonicProj (Rnm (toLinf μ) κ)) with hh1
  set h2 : ℂ → ℂ := ⇑(harmonicProj (Rnm (toLinf ν) κ)) with hh2
  have hmL := x5_Rnm_L2 hμ hκ
  have hnL := x5_Rnm_L2 hν hκ
  obtain ⟨⟨a1, ha1, hae1⟩, horth1⟩ := harmonicProj_orthogonal _ hmL
  obtain ⟨⟨a2, ha2, hae2⟩, -⟩ := harmonicProj_orthogonal _ hnL
  have hn1 : normL2 unitDiscExterior h1 < ∞ := by
    rw [x5_normL2_congr hae1]; obtain ⟨-, -, -, h⟩ := ha1; exact h
  have hn2 : normL2 unitDiscExterior h2 < ∞ := by
    rw [x5_normL2_congr hae2]; obtain ⟨-, -, -, h⟩ := ha2; exact h
  have hsm : ∀ ξ : LinfStar, AEStronglyMeasurable (⇑ξ : ℂ → ℂ) (volume.restrict unitDiscExterior) :=
    fun ξ => (Lp.stronglyMeasurable ξ).aestronglyMeasurable
  have hI1 := x5_inner_integrable (hsm (Rnm (toLinf μ) κ)) (hsm (harmonicProj (Rnm (toLinf ν) κ))) hmL hn2
  have hI2 := x5_inner_integrable (hsm (harmonicProj (Rnm (toLinf μ) κ))) (hsm (harmonicProj (Rnm (toLinf ν) κ))) hn1 hn2
  -- `P² = P`: replace `h1` by `m` in the pairing against `h2`
  have hstep : ∫ z in unitDiscExterior, h1 z * conj (h2 z) * ((rho z : ℝ) : ℂ) =
      ∫ z in unitDiscExterior, m z * conj (h2 z) * ((rho z : ℝ) : ℂ) := by
    have h0 := horth1 a2 ha2
    have h0' : ∫ z in unitDiscExterior, (m z - h1 z) * conj (h2 z) * ((rho z : ℝ) : ℂ) = 0 := by
      rw [← h0]
      apply integral_congr_ae
      have hae2' : h2 =ᵐ[volume.restrict unitDiscExterior] a2 := hae2
      filter_upwards [hae2'] with z hz
      rw [hz]
    have hsub : ∫ z in unitDiscExterior, (m z - h1 z) * conj (h2 z) * ((rho z : ℝ) : ℂ) =
        (∫ z in unitDiscExterior, m z * conj (h2 z) * ((rho z : ℝ) : ℂ)) -
          ∫ z in unitDiscExterior, h1 z * conj (h2 z) * ((rho z : ℝ) : ℂ) := by
      rw [← integral_sub hI1 hI2]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun z => ?_
      dsimp only
      ring
    rw [hsub] at h0'
    exact (sub_eq_zero.1 h0').symm
  have hLHS : gWP μ ν κ = ∫ u in unitDiscExterior, h1 u * conj (h2 u) * ((rho u : ℝ) : ℂ) := rfl
  rw [hLHS, hstep]
  have hrho : Measurable fun u : ℂ => ((rho u : ℝ) : ℂ) := by unfold rho; fun_prop
  have hmm : Measurable m := (Lp.stronglyMeasurable _).measurable
  have hm2 : Measurable h2 := (Lp.stronglyMeasurable _).measurable
  have hG : Measurable fun u : ℂ => m u * conj (h2 u) * ((rho u : ℝ) : ℂ) :=
    (hmm.mul (continuous_conj.measurable.comp hm2)).mul hrho
  rw [wpcv_cov hκ _ hG]
  have hP2 := bc_pullback_ae hκ (wpcv_P_Rnm_ae hκ (toLinf ν))
  have hR1 := bc_pullback_ae hκ (wpcv_RnmFun_ae hκ (toLinf μ))
  have hw := bc_wA_ae hκ
  have hwE := bc_pullback_ae hκ (ae_restrict_mem hE)
  apply integral_congr_ae
  filter_upwards [hP2, hR1, ae_restrict_of_ae hw, ae_restrict_mem hE, hwE, wp_harmonic_toLinf_ae hμ] with z hz2 hz1 hz3 hzE hzw hzμ
  obtain ⟨-, hdz, hdil, hlt⟩ := hz3
  have hext : extA κ z = κ z := by
    have : 1 < ‖z‖ := by simpa [unitDiscExterior] using hzE
    simp [extA, this]
  have hjac : jacobian (wA κ) z = (1 - ‖κ z‖ ^ 2) * ‖dz (wA κ) z‖ ^ 2 := by
    have hdb : dzbar (wA κ) z = κ z * dz (wA κ) z := by
      have := hdil
      unfold complexDilatation at this
      rw [hext] at this
      field_simp at this
      rw [mul_comm]
      exact this
    unfold jacobian
    rw [hdb, norm_mul]
    ring
  have hκlt : ‖κ z‖ < 1 := by
    have := hlt
    rw [hdil, hext] at this
    exact this
  have hne : (1 - ‖κ z‖ ^ 2 : ℝ) ≠ 0 := by nlinarith [norm_nonneg (κ z)]
  have hwn : wA κ z ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hzw
  have hc : conj (dz (wA κ) z) ≠ 0 := by simpa using hdz
  set ph : ℂ := dz (wA κ) z / conj (dz (wA κ) z) with hph
  have hphc : conj (dz (wA κ) z) / dz (wA κ) z = ph⁻¹ := by
    rw [hph, inv_div]
  have hRz : m (wA κ z) = μ z / (1 - ‖κ z‖ ^ 2) * ph := by
    have h1' : m (wA κ z) = RnmFun (toLinf μ) κ (wA κ z) := hz1
    rw [h1']
    show (fun u => (toLinf μ) u / (1 - ‖κ u‖ ^ 2) * (dz (wA κ) u / conj (dz (wA κ) u)))
      (Function.invFun (wA κ) (wA κ z)) = _
    rw [bc_invFun_wA hwn]
    simp only [hzμ, hph]
  have hP2z : h2 (wA κ z) = ph * Qfun (toLinf ν) κ z := by
    have h2' : h2 (wA κ z) = harmonicProjFun (RnmFun (toLinf ν) κ) (wA κ z) := hz2
    rw [h2']
    unfold Qfun
    rw [hphc]
    have hph0 : ph ≠ 0 := div_ne_zero hdz hc
    field_simp
  have hne' : ((1 - ‖κ z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
  have hph1 : ph * conj ph = 1 := by
    rw [hph]
    simp only [map_div₀, Complex.conj_conj]
    field_simp
  change ((jacobian (wA κ) z : ℝ) : ℂ) * (m (wA κ z) * conj (h2 (wA κ z)) * ((rho (wA κ z) : ℝ) : ℂ)) = _
  rw [hjac, hRz, hP2z, map_mul]
  push_cast at hne' ⊢
  have : (1 - (‖κ z‖ : ℂ) ^ 2) * (‖dz (wA κ) z‖ : ℂ) ^ 2 *
      (μ z / (1 - (‖κ z‖ : ℂ) ^ 2) * ph * (conj ph * conj (Qfun (toLinf ν) κ z)) * (rho (wA κ z) : ℂ)) =
      μ z * conj (Qfun (toLinf ν) κ z) * ((rho (wA κ z) : ℂ) * (‖dz (wA κ) z‖ : ℂ) ^ 2) * (ph * conj ph) := by
    field_simp
  rw [this, hph1, mul_one]

theorem x5_eq_7_7 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    gWP μ ν κ = ∫ z in unitDiscExterior, Qfun (toLinf μ) κ z * conj (Qfun (toLinf ν) κ z) * (1 - ‖κ z‖ ^ 2) *
        (rho (wA κ z) * ‖dz (wA κ) z‖ ^ 2) ∧
      gWP μ ν κ = ∫ z in unitDiscExterior, μ z * conj (Qfun (toLinf ν) κ z) * (rho (wA κ z) * ‖dz (wA κ) z‖ ^ 2) :=
  ⟨x5_gWP_eq_Q μ ν hκ, x5_line2 hμ hν hκ⟩


end WPCV
open LiZhongQC

/-! ### Original relocated (2026-10-26) -/

/-- **(7.7)** (TT:2827). Since `P² = P`,
`g_{μν̄}(κ) = ∬_{𝔻*} Q(μ, κ) \overline{Q(ν, κ)} (1 - |κ|²) w_κ^*(ρ) d²z = ∬_{𝔻*} μ \overline{Q(ν, κ)} w_κ^*(ρ) d²z`,
with `w_κ^*(ρ) = ρ ∘ w_κ |(w_κ)_z|²`. -/
theorem eq_7_7 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    gWP μ ν κ = ∫ z in unitDiscExterior, Qfun (toLinf μ) κ z * conj (Qfun (toLinf ν) κ z) * (1 - ‖κ z‖ ^ 2) *
        (rho (wA κ z) * ‖dz (wA κ) z‖ ^ 2) ∧
      gWP μ ν κ = ∫ z in unitDiscExterior, μ z * conj (Qfun (toLinf ν) κ z) * (rho (wA κ z) * ‖dz (wA κ) z‖ ^ 2) :=
  WPCV.x5_eq_7_7 hμ hν hκ

end TakhtajanTeo
