import TakhtajanTeo.Ch2.S1_Part5
import TakhtajanTeo.Ch2.S2_Completed

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- Inversion carries `𝔻*` onto `𝔻 \ {0}` with Jacobian `|z|⁻⁴` (Bochner form). -/
theorem s2c_inv_integral (K : ℂ → ℂ) :
    ∫ w in unitDisc \ {0}, K w = ∫ z in unitDiscExterior, (‖z‖ ^ 4)⁻¹ • K z⁻¹ := by
  have hopen : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hext0 : ∀ z ∈ unitDiscExterior, z ≠ 0 := fun z hz h => by
    subst h
    norm_num [unitDiscExterior] at hz
  rw [← resolvent_inv_exterior_image,
    integral_image_eq_integral_abs_det_fderiv_smul volume hopen.measurableSet
      (fun z hz => ((differentiableAt_inv (hext0 z hz)).hasDerivAt.hasFDerivAt.restrictScalars
        ℝ).hasFDerivWithinAt) (fun a _ b _ h => inv_injective h) K]
  refine setIntegral_congr_fun hopen.measurableSet fun z hz => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _), deriv_inv']
  simp only [norm_neg, norm_inv, norm_pow]
  congr 1
  ring

/-- Reflection carries `𝔻 \ {0}` onto `𝔻*` with Jacobian `|u|⁻⁴`. -/
theorem s2c_refl_integral (F : ℂ → ℂ) :
    ∫ v in unitDiscExterior, F v = ∫ u in unitDisc \ {0}, (‖u‖ ^ 4)⁻¹ • F (refl u) := by
  have hemb : MeasurableEmbedding (⇑Complex.conjLIE) :=
    Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hpre : (⇑Complex.conjLIE) ⁻¹' (unitDisc \ {0}) = unitDisc \ {0} := by
    ext w
    simp [unitDisc]
  have hA : ∫ w in unitDisc \ {0}, (‖w‖ ^ 4)⁻¹ • F (refl w) =
      ∫ w in unitDisc \ {0}, (‖w‖ ^ 4)⁻¹ • F w⁻¹ := by
    have h := (Complex.conjLIE.measurePreserving).setIntegral_preimage_emb hemb
      (fun w => (‖w‖ ^ 4)⁻¹ • F (refl w)) (unitDisc \ {0})
    rw [hpre] at h
    simp only [Complex.conjLIE_apply] at h
    rw [← h]
    refine setIntegral_congr_fun ?_ fun w _ => ?_
    · exact (measurableSet_ball.diff (measurableSet_singleton _))
    · simp [refl]
  rw [hA, s2c_inv_integral]
  refine setIntegral_congr_fun (isOpen_lt continuous_const continuous_norm).measurableSet
    fun z hz => ?_
  have hz0 : z ≠ 0 := fun h => by
    subst h
    norm_num [unitDiscExterior] at hz
  simp only [norm_inv, smul_smul]
  rw [inv_inv, inv_pow, inv_inv, mul_comm, mul_inv_cancel₀ (pow_ne_zero 4 (norm_ne_zero_iff.2 hz0)),
    one_smul]

/-- On `𝔻 \ {0}`, `𝖿^{μ⁻¹}(z) = conj (φ (conj z))` where `φ(s) = b/𝗀_μ(1/s)`. -/
theorem s2c_f_eq_conj {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {φ : ℂ → ℂ} {b : ℂ} (hφi : InjOn φ unitDisc) (hφ0 : φ 0 = 0) (hb : b ≠ 0)
    (hbg : derivAtInfty (gsans μ) = b)
    (hg : ∀ s ∈ unitDisc, s ≠ 0 → gsans μ (1 / s) = b / φ s) {y : ℂ} (hy : y ∈ unitDisc)
    (hy0 : y ≠ 0) :
    fsans (beltramiInv μ) y = conj (φ (conj y)) := by
  have h1 := (w3_eq_1_3 hμ).1 y hy hy0
  have hcy : conj y ∈ unitDisc := by
    simpa [unitDisc] using hy
  have hcy0 : conj y ≠ 0 := by simpa using hy0
  have h2 := hg (conj y) hcy hcy0
  have hrefl : refl y = 1 / conj y := by simp [refl]
  rw [h1, hbg, hrefl, h2]
  have hφne : φ (conj y) ≠ 0 := by
    intro h
    exact hcy0 (hφi hcy (mem_ball_self one_pos) (h.trans hφ0.symm))
  have hbc : conj b ≠ 0 := by simpa using hb
  simp only [refl, map_div₀]
  have hφc : conj (φ (conj y)) ≠ 0 := by simpa using hφne
  field_simp

theorem s2c_kerK1_conj {f φ : ℂ → ℂ} {z u : ℂ} (hzu : z ≠ u)
    (hfz : f z = conj (φ (conj z))) (hfu : f u = conj (φ (conj u)))
    (hdz : deriv f z = conj (deriv φ (conj z))) (hdu : deriv f u = conj (deriv φ (conj u))) :
    kerK1 f z u = conj (kerK1 φ (conj z) (conj u)) := by
  have hne : conj z ≠ conj u := fun h => hzu ((starRingEnd ℂ).injective h)
  simp [kerK1, hzu, hne, hfz, hfu, hdz, hdu]

theorem s2c_kerK1_refl {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {φ : ℂ → ℂ} {b : ℂ}
    (hφd : DifferentiableOn ℂ φ unitDisc) (hφi : InjOn φ unitDisc) (hφ0 : φ 0 = 0) (hb : b ≠ 0)
    (hbg : derivAtInfty (gsans μ) = b)
    (hg : ∀ s ∈ unitDisc, s ≠ 0 → gsans μ (1 / s) = b / φ s) {z u : ℂ} (hz : z ∈ unitDisc)
    (hu : u ∈ unitDisc) (hz0 : z ≠ 0) (hu0 : u ≠ 0) (hzu : z ≠ u) :
    kerK1 (fsans (beltramiInv μ)) z u =
      (1 / z ^ 2) * (1 / u ^ 2) * conj (kerK4 (gsans μ) (refl z) (refl u)) := by
  have hopen : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hF : ∀ y ∈ unitDisc, y ≠ 0 → fsans (beltramiInv μ) y = conj (φ (conj y)) :=
    fun y hy hy0 => s2c_f_eq_conj hμ hφi hφ0 hb hbg hg hy hy0
  have hder : ∀ y ∈ unitDisc, y ≠ 0 →
      deriv (fsans (beltramiInv μ)) y = conj (deriv φ (conj y)) := by
    intro y hy hy0
    have hev : fsans (beltramiInv μ) =ᶠ[𝓝 y] fun x => conj (φ (conj x)) := by
      filter_upwards [hopen.mem_nhds ⟨hy, hy0⟩] with x hx
      exact hF x hx.1 hx.2
    rw [hev.deriv_eq]
    exact congrFun (deriv_conj_conj (f := φ)) y
  have hζ : refl z ∈ unitDiscExterior := (refl_mem_exterior_iff hz0).2 hz
  have hη : refl u ∈ unitDiscExterior := (refl_mem_exterior_iff hu0).2 hu
  have hζη : refl z ≠ refl u := fun h => hzu ((starRingEnd ℂ).injective (inv_injective h))
  rw [s2c_kerK4_eq hφd hφi hφ0 hb hg hζ hη hζη, s2c_kerK1_conj hzu (hF z hz hz0) (hF u hu hu0)
    (hder z hz hz0) (hder u hu hu0)]
  have e1 : (refl z)⁻¹ = conj z := by simp [refl]
  have e2 : (refl u)⁻¹ = conj u := by simp [refl]
  rw [e1, e2, map_mul, map_mul, map_pow, map_pow, Complex.conj_conj, Complex.conj_conj]
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu0
  field_simp

/-- **(2.9)** (TT:4165), corrected: `𝖪₁([μ⁻¹])(z, w) = \overline{𝖪₄([μ])(1/z̄, 1/w̄)} · (1/z²)(1/w̄²)`.

[CORRECTION 2026-10-25] The memoir's form `𝖪₄([μ])(1/z̄, 1/w̄) (1/z²)(1/w²)` is antiholomorphic in `z` on the right
and holomorphic in `z` on the left. On the diagonal it is not even real, while `𝖪₁(z, z) ≥ 0`. The corrected form has
the right (anti)holomorphy and gives `|z|⁻⁴ 𝖪₄(1/z̄, 1/z̄)` on the diagonal, which is what the memoir uses (下属4). 
Proved here as `s2c_eq_2_9`; statement identical to `eq_2_9`. -/
theorem s2c_eq_2_9 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hz0 : z ≠ 0)
    (hw0 : w ≠ 0) :
    kerKK1 (fsans (beltramiInv μ)) z w =
      conj (kerKK4 (gsans μ) (refl z) (refl w)) * (1 / z ^ 2) * (1 / conj w ^ 2) := by
  obtain ⟨φ, b, hφd, hφi, hφ0, -, hb, hbg, hg⟩ :=
    g1_inverted_exterior (AppB.b8_welding_normalized_pair hμ)
  have hnull : unitDisc \ {0} =ᵐ[volume] unitDisc :=
    sdiff_null_ae_eq_self (measure_singleton 0)
  have hm : MeasurableSet (unitDisc \ {0}) :=
    measurableSet_ball.diff (measurableSet_singleton _)
  have hR : conj (kerKK4 (gsans μ) (refl z) (refl w)) * (1 / z ^ 2) * (1 / conj w ^ 2) =
      ∫ v in unitDiscExterior, conj (kerK4 (gsans μ) (refl z) v *
        conj (kerK4 (gsans μ) (refl w) v)) * ((1 / z ^ 2) * (1 / conj w ^ 2)) := by
    unfold kerKK4
    rw [← integral_conj, mul_assoc, ← integral_mul_const]
  rw [hR, s2c_refl_integral, kerKK1, ← setIntegral_congr_set hnull]
  refine setIntegral_congr_ae hm ?_
  have hz' : ∀ᵐ u : ℂ, u ∉ ({z} : Set ℂ) := (Set.countable_singleton z).ae_notMem volume
  have hw' : ∀ᵐ u : ℂ, u ∉ ({w} : Set ℂ) := (Set.countable_singleton w).ae_notMem volume
  filter_upwards [hz', hw'] with u huz huw hu
  have huz' : u ≠ z := fun h => huz (by simp [h])
  have huw' : u ≠ w := fun h => huw (by simp [h])
  have hu1 : u ∈ unitDisc := hu.1
  have hu0 : u ≠ 0 := fun h => hu.2 (by simp [h])
  have h1 := s2c_kerK1_refl hμ hφd hφi hφ0 hb hbg hg hz hu1 hz0 hu0 (Ne.symm huz')
  have h2 := s2c_kerK1_refl hμ hφd hφi hφ0 hb hbg hg hw hu1 hw0 hu0 (Ne.symm huw')
  rw [h1, h2]
  have hu2 : ((‖u‖ : ℝ) : ℂ) ^ 2 = u * conj u := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hn4 : ((‖u‖ ^ 4 : ℝ) : ℂ) = (u * conj u) ^ 2 := by
    rw [← hu2]
    push_cast
    ring
  have hcu : conj u ≠ 0 := by simpa using hu0
  have hcw : conj w ≠ 0 := by simpa using hw0
  rw [Complex.real_smul, Complex.ofReal_inv, hn4]
  simp only [map_mul, map_div₀, map_pow, Complex.conj_conj, map_one]
  field_simp

/-! ### Original relocated (2026-10-26) -/

/-- **(2.9)** (TT:4165), corrected: `𝖪₁([μ⁻¹])(z, w) = \overline{𝖪₄([μ])(1/z̄, 1/w̄)} · (1/z²)(1/w̄²)`.

[CORRECTION 2026-10-25] The memoir's form `𝖪₄([μ])(1/z̄, 1/w̄) (1/z²)(1/w²)` is antiholomorphic in `z` on the right
and holomorphic in `z` on the left. On the diagonal it is not even real, while `𝖪₁(z, z) ≥ 0`. The corrected form has
the right (anti)holomorphy and gives `|z|⁻⁴ 𝖪₄(1/z̄, 1/z̄)` on the diagonal, which is what the memoir uses (下属4). -/
theorem eq_2_9 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hz0 : z ≠ 0)
    (hw0 : w ≠ 0) :
    kerKK1 (fsans (beltramiInv μ)) z w =
      conj (kerKK4 (gsans μ) (refl z) (refl w)) * (1 / z ^ 2) * (1 / conj w ^ 2) :=
  s2c_eq_2_9 hμ hz hw hz0 hw0

end Ch2

end TakhtajanTeo
