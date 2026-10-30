import TakhtajanTeo.Ch2.S3_Variations
import TakhtajanTeo.Ch2.S2_Completed4
import TakhtajanTeo.Ch2.S1_Part5
import TakhtajanTeo.Ch1.Eq19Completed
import TakhtajanTeo.Ch1.GeneralWeldingUniqueness
import TakhtajanTeo.Ch1.WeldingUniqueness
import TakhtajanTeo.Ch1.ActualWelding

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- `𝒜(1/(g∘ι))(s) = -s⁻² (𝒜(g) - 2g'/g + 2/ζ)(1/s)`, `ι(s) = 1/s`. -/
theorem s2c_A_inv {g : ℂ → ℂ} {E : Set ℂ} (hE : IsOpen E) (hg : DifferentiableOn ℂ g E)
    (hg0 : ∀ w ∈ E, g w ≠ 0) (hg1 : ∀ w ∈ E, deriv g w ≠ 0) {s : ℂ} (hs : s ≠ 0) (hsE : s⁻¹ ∈ E) :
    preSchwarzian (fun s => (g s⁻¹)⁻¹) s =
      -(s ^ 2)⁻¹ * (preSchwarzian g s⁻¹ - 2 * deriv g s⁻¹ / g s⁻¹ + 2 / s⁻¹) := by
  set V : Set ℂ := {s : ℂ | s ≠ 0 ∧ s⁻¹ ∈ E} with hV
  have hVopen : IsOpen V := by
    have h1 : IsOpen {s : ℂ | s ≠ 0} := isOpen_ne
    have h2 : IsOpen {s : ℂ | s ≠ 0 ∧ s⁻¹ ∈ E} := by
      have : ContinuousOn (fun s : ℂ => s⁻¹) {s : ℂ | s ≠ 0} := fun x hx => (continuousAt_inv₀ hx).continuousWithinAt
      have := this.isOpen_inter_preimage h1 hE
      have heq : {s : ℂ | s ≠ 0 ∧ s⁻¹ ∈ E} = {s : ℂ | s ≠ 0} ∩ (fun s : ℂ => s⁻¹) ⁻¹' E := rfl
      rw [heq]
      exact this
    exact h2
  have hsV : s ∈ V := ⟨hs, hsE⟩
  have hD1 : ∀ y ∈ V, HasDerivAt (fun s => (g s⁻¹)⁻¹)
      (deriv g y⁻¹ * (y ^ 2)⁻¹ / g y⁻¹ ^ 2) y := by
    rintro y ⟨hy, hyE⟩
    have hw : HasDerivAt g (deriv g y⁻¹) y⁻¹ :=
      (hg.differentiableAt (hE.mem_nhds hyE)).hasDerivAt
    have hc := hw.comp y (hasDerivAt_inv hy)
    have hi := hc.inv (hg0 _ hyE)
    have hi' : HasDerivAt (fun s => (g s⁻¹)⁻¹) (-(deriv g y⁻¹ * -(y ^ 2)⁻¹) / g y⁻¹ ^ 2) y := hi
    exact hi'.congr_deriv (by ring)
  have hev : deriv (fun s => (g s⁻¹)⁻¹) =ᶠ[𝓝 s]
      fun y => deriv g y⁻¹ * (y ^ 2)⁻¹ / g y⁻¹ ^ 2 := by
    filter_upwards [hVopen.mem_nhds hsV] with y hy
    exact (hD1 y hy).deriv
  have hgd' : DifferentiableOn ℂ (deriv g) E := hg.deriv hE
  have hw : HasDerivAt g (deriv g s⁻¹) s⁻¹ := (hg.differentiableAt (hE.mem_nhds hsE)).hasDerivAt
  have hw' : HasDerivAt (deriv g) (deriv (deriv g) s⁻¹) s⁻¹ :=
    (hgd'.differentiableAt (hE.mem_nhds hsE)).hasDerivAt
  have hinv := hasDerivAt_inv hs
  have hN := hw'.comp s hinv
  have hG := hw.comp s hinv
  have hG2 : HasDerivAt (fun y => g y⁻¹ ^ 2) (2 * g s⁻¹ * (deriv g s⁻¹ * (-(s ^ 2)⁻¹))) s := by
    have := hG.pow 2
    exact this.congr_deriv (by simp only [Function.comp_apply]; push_cast; ring)
  have hP : HasDerivAt (fun y : ℂ => (y ^ 2)⁻¹) (-(2 * s) / (s ^ 2) ^ 2) s := by
    have := (hasDerivAt_pow 2 s).inv (pow_ne_zero 2 hs)
    exact this.congr_deriv (by push_cast; ring)
  have hnum := hN.mul hP
  have hfull := hnum.div hG2 (pow_ne_zero 2 (hg0 _ hsE))
  have hfull' : HasDerivAt (fun y : ℂ => deriv g y⁻¹ * (y ^ 2)⁻¹ / g y⁻¹ ^ 2) _ s := hfull
  rw [preSchwarzian, hev.deriv_eq, hfull'.deriv, (hD1 s hsV).deriv]
  have hgs := hg0 _ hsE
  have hg1s := hg1 _ hsE
  unfold preSchwarzian
  simp only [Function.comp_apply, Pi.mul_apply]
  generalize g s⁻¹ = a at *
  generalize deriv g s⁻¹ = b at *
  generalize deriv (deriv g) s⁻¹ = c at *
  field_simp
  ring

theorem s2c_conj_deriv (h : ℂ → ℂ) (x : ℂ) :
    deriv (fun z => conj (h (conj z))) x = conj (deriv h (conj x)) :=
  congrFun (deriv_conj_conj (f := h)) x

theorem s2c_conj_pre (h : ℂ → ℂ) (x : ℂ) :
    preSchwarzian (fun z => conj (h (conj z))) x = conj (preSchwarzian h (conj x)) := by
  unfold preSchwarzian
  have h1 : deriv (fun z => conj (h (conj z))) = fun z => conj (deriv h (conj z)) :=
    funext (s2c_conj_deriv h)
  rw [h1, s2c_conj_deriv (deriv h) x, map_div₀]

/-- The pair `(𝖿^μ, 𝗀_μ)` depends only on the class of `μ`. -/
theorem s2c_class_pair {μ₁ μ₂ : LinfStarBall} (h : teichSetoid μ₁ μ₂) :
    EqOn (fsans (μ₁ : LinfStar)) (fsans (μ₂ : LinfStar)) unitDisc ∧
      EqOn (gsans (μ₁ : LinfStar)) (gsans (μ₂ : LinfStar)) unitDiscExterior := by
  have hB : ∀ z ∈ unitDisc, fB (μ₁ : LinfStar) z = fB (μ₂ : LinfStar) z :=
    (modelA_iff_modelB μ₁ μ₂).1 h
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [e13_fsans_eq μ₁.2, e13_fsans_eq μ₂.2]
    exact hB z hz
  · obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec μ₂.2
    have hone : IsOneFixedQS (wA (μ₂ : LinfStar)) := by
      refine ⟨⟨wA_circle_sensePreserving μ₂.2, wA_circle_quasisymmetric μ₂.2⟩, ?_⟩
      show finPart (wAS _ ((1 : ℂ) : ExtPlane)) = 1
      rw [hm2]
      rfl
    have hw₁ := weldingPrime_congr_h (fun z hz => h z hz) (normalizedWeldingPrime_actual μ₁.2)
    have hw₂ := normalizedWeldingPrime_actual μ₂.2
    have huniq := (conformal_welding_prime_unique hone hw₁ hw₂).2 hz
    rw [e13_gsans_eq μ₁.2, e13_gsans_eq μ₂.2, gMu_eq_normalizedWeldingExterior μ₁.2 hz,
      gMu_eq_normalizedWeldingExterior μ₂.2 hz]
    exact huniq

/-! ### Real-valued change of variables -/

theorem s2c_refl_integral_real (F : ℂ → ℝ) :
    ∫ v in unitDiscExterior, F v = ∫ u in unitDisc \ {0}, (‖u‖ ^ 4)⁻¹ * F (refl u) := by
  have h := s2c_refl_integral (fun v => ((F v : ℝ) : ℂ))
  have e : ∀ u : ℂ, (‖u‖ ^ 4)⁻¹ • ((F (refl u) : ℝ) : ℂ) =
      (((‖u‖ ^ 4)⁻¹ * F (refl u) : ℝ) : ℂ) := by
    intro u
    rw [Complex.real_smul]
    push_cast
    ring
  simp only [e] at h
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact_mod_cast h

theorem s2c_refl_refl (u : ℂ) : refl (refl u) = u := by
  simp [refl]

theorem s2c_refl_integral_real' (H : ℂ → ℝ) :
    ∫ u in unitDisc \ {0}, H u = ∫ z in unitDiscExterior, (‖z‖ ^ 4)⁻¹ * H (refl z) := by
  have h := s2c_refl_integral_real (fun v => (‖v‖ ^ 4)⁻¹ * H (refl v))
  refine (Eq.trans ?_ h.symm)
  refine setIntegral_congr_fun (measurableSet_ball.diff (measurableSet_singleton _)) fun u hu => ?_
  have hu0 : u ≠ 0 := fun h0 => hu.2 (by simp [h0])
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu0
  simp only [norm_refl, s2c_refl_refl]
  field_simp

theorem s2c_inv_integral_real (K : ℂ → ℝ) :
    ∫ w in unitDisc \ {0}, K w = ∫ z in unitDiscExterior, (‖z‖ ^ 4)⁻¹ * K z⁻¹ := by
  have h := s2c_inv_integral (fun v => ((K v : ℝ) : ℂ))
  have e : ∀ z : ℂ, (‖z‖ ^ 4)⁻¹ • ((K z⁻¹ : ℝ) : ℂ) = (((‖z‖ ^ 4)⁻¹ * K z⁻¹ : ℝ) : ℂ) := by
    intro z
    rw [Complex.real_smul]
    push_cast
    ring
  simp only [e] at h
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact_mod_cast h

theorem s2c_inv_integral_real' (K : ℂ → ℝ) :
    ∫ z in unitDiscExterior, K z = ∫ s in unitDisc \ {0}, (‖s‖ ^ 4)⁻¹ * K s⁻¹ := by
  have h := s2c_inv_integral_real (fun s => (‖s‖ ^ 4)⁻¹ * K s⁻¹)
  refine Eq.trans ?_ h.symm
  refine setIntegral_congr_fun (isOpen_lt continuous_const continuous_norm).measurableSet fun z hz => ?_
  have hz0 : z ≠ 0 := fun h0 => by
    subst h0
    norm_num [unitDiscExterior] at hz
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
  simp only [norm_inv, inv_inv]
  field_simp

/-! ### The kernel `L_g = 𝒜(g) - 2g'/g + 2/z` and `𝒜` of the inverted functions -/

theorem s2c_pre_const_mul {c : ℂ} (hc : c ≠ 0) (h : ℂ → ℂ) (z : ℂ) :
    preSchwarzian (fun x => c * h x) z = preSchwarzian h z := by
  unfold preSchwarzian
  have h1 : deriv (fun x => c * h x) = fun x => c * deriv h x := deriv_const_mul_field' c
  have h2 : deriv (fun x => c * deriv h x) z = c * deriv (deriv h) z :=
    congrFun (deriv_const_mul_field' (v := deriv h) c) z
  rw [h1, h2]
  exact mul_div_mul_left _ _ hc

theorem s2c_facts {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    DifferentiableOn ℂ (fsans μ) unitDisc ∧ InjOn (fsans μ) unitDisc ∧ fsans μ 0 = 0 ∧
      deriv (fsans μ) 0 = 1 ∧ DifferentiableOn ℂ (gsans μ) unitDiscExterior ∧
      InjOn (gsans μ) unitDiscExterior ∧ (∀ w ∈ unitDiscExterior, gsans μ w ≠ 0) ∧
      (∀ w ∈ unitDiscExterior, deriv (gsans μ) w ≠ 0) ∧
      (∀ y ∈ unitDisc, y ≠ 0 → fsans μ y ≠ 0) ∧ (∀ y ∈ unitDisc, deriv (fsans μ) y ≠ 0) := by
  obtain ⟨hfd, hfi, hf0, hf1, ⟨hgd, hgi, hgt⟩, hdisj⟩ := AppB.b8_welding_normalized_pair hμ
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hopenD : IsOpen unitDisc := isOpen_ball
  refine ⟨hfd, hfi, hf0, hf1, hgd, hgi, ?_, ?_, ?_, ?_⟩
  · intro w hw h
    exact Set.disjoint_left.mp hdisj ⟨0, mem_ball_self one_pos, hf0⟩ ⟨w, hw, h⟩
  · intro w hw
    exact deriv_ne_zero_of_injOn hopenE hgd hgi hw
  · intro y hy hy0 h
    exact hy0 (hfi hy (mem_ball_self one_pos) (h.trans hf0.symm))
  · intro y hy
    exact deriv_ne_zero_of_injOn hopenD hfd hfi hy

theorem s2c_pre_F {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    ‖preSchwarzian (fsans (beltramiInv μ)) z‖ = (‖z‖ ^ 2)⁻¹ *
      ‖preSchwarzian (gsans μ) (refl z) - 2 * deriv (gsans μ) (refl z) / gsans μ (refl z) +
        2 / refl z‖ := by
  obtain ⟨-, -, -, -, hgd, hgi, hg0, hg1, -, -⟩ := s2c_facts hμ
  obtain ⟨φ, b, -, -, -, -, hb, hbg, -⟩ := g1_inverted_exterior (AppB.b8_welding_normalized_pair hμ)
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hop : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hbc : conj b ≠ 0 := by simpa using hb
  set Fm : ℂ → ℂ := fun x => conj b * conj ((gsans μ ((conj x)⁻¹))⁻¹) with hFm
  have hev : fsans (beltramiInv μ) =ᶠ[𝓝 z] Fm := by
    filter_upwards [hop.mem_nhds ⟨hz, hz0⟩] with x hx
    rw [(w3_eq_1_3 hμ).1 x hx.1 hx.2, hbg]
    simp [hFm, refl, map_inv₀]
  have hpre : preSchwarzian (fsans (beltramiInv μ)) z = preSchwarzian Fm z := by
    unfold preSchwarzian
    rw [hev.deriv_eq, hev.deriv.deriv_eq]
  have hs : conj z ≠ 0 := by simpa using hz0
  have hsE : (conj z)⁻¹ ∈ unitDiscExterior := (refl_mem_exterior_iff hz0).2 hz
  rw [hpre, hFm, s2c_pre_const_mul hbc, s2c_conj_pre (fun s => (gsans μ s⁻¹)⁻¹) z,
    s2c_A_inv hopenE hgd hg0 hg1 hs hsE]
  simp only [refl, RCLike.norm_conj, norm_mul, norm_neg, norm_inv, norm_pow]

theorem s2c_pre_G {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ‖preSchwarzian (gsans (beltramiInv μ)) z‖ = (‖z‖ ^ 2)⁻¹ *
      ‖preSchwarzian (fsans μ) (refl z) - 2 * deriv (fsans μ) (refl z) / fsans μ (refl z) +
        2 / refl z‖ := by
  obtain ⟨hfd, hfi, hf0, -, -, -, -, -, hf0', hf1'⟩ := s2c_facts hμ
  obtain ⟨φ, b, -, -, -, -, hb, hbg, -⟩ := g1_inverted_exterior (AppB.b8_welding_normalized_pair hμ)
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hE : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hbc : conj b ≠ 0 := by simpa using hb
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
  have hconjE : ∀ y ∈ unitDisc \ {0}, conj y ∈ unitDisc \ {0} := fun y hy =>
    ⟨by simpa [unitDisc] using hy.1, by simpa using hy.2⟩
  set fs : ℂ → ℂ := fun y => conj (fsans μ (conj y)) with hfs
  have hfsd : DifferentiableOn ℂ fs (unitDisc \ {0}) := by
    intro y hy
    have h := (hfd.differentiableAt (isOpen_ball.mem_nhds (hconjE y hy).1)).conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have hfs0 : ∀ y ∈ unitDisc \ {0}, fs y ≠ 0 := fun y hy h =>
    hf0' (conj y) (hconjE y hy).1 (hconjE y hy).2 (by simpa [hfs] using h)
  have hfs1 : ∀ y ∈ unitDisc \ {0}, deriv fs y ≠ 0 := by
    intro y hy h
    have h' : deriv fs y = conj (deriv (fsans μ) (conj y)) := s2c_conj_deriv _ _
    rw [h'] at h
    exact hf1' (conj y) (hconjE y hy).1 (by simpa using h)
  set Gm : ℂ → ℂ := fun x => conj b * (fs x⁻¹)⁻¹ with hGm
  have hev : gsans (beltramiInv μ) =ᶠ[𝓝 z] Gm := by
    filter_upwards [hopenE.mem_nhds hz] with x hx
    rw [(w3_eq_1_3 hμ).2 x hx, hbg]
    simp [hGm, hfs, refl, map_inv₀]
  have hpre : preSchwarzian (gsans (beltramiInv μ)) z = preSchwarzian Gm z := by
    unfold preSchwarzian
    rw [hev.deriv_eq, hev.deriv.deriv_eq]
  have hsE : z⁻¹ ∈ unitDisc \ {0} :=
    ⟨mem_ball_zero_iff.2 (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1), inv_ne_zero hz0⟩
  rw [hpre, hGm, s2c_pre_const_mul hbc, s2c_A_inv hE hfsd hfs0 hfs1 hz0 hsE]
  have e1 : preSchwarzian fs z⁻¹ = conj (preSchwarzian (fsans μ) (conj z⁻¹)) := s2c_conj_pre _ _
  have e2 : deriv fs z⁻¹ = conj (deriv (fsans μ) (conj z⁻¹)) := s2c_conj_deriv _ _
  have e3 : fs z⁻¹ = conj (fsans μ (conj z⁻¹)) := rfl
  rw [e1, e2, e3]
  have hrefl : conj z⁻¹ = refl z := by simp [refl]
  rw [hrefl]
  have hc : conj (preSchwarzian (fsans μ) (refl z) - 2 * deriv (fsans μ) (refl z) / fsans μ (refl z) +
      2 / refl z) = conj (preSchwarzian (fsans μ) (refl z)) -
        2 * conj (deriv (fsans μ) (refl z)) / conj (fsans μ (refl z)) + 2 / z⁻¹ := by
    have hcr : conj (refl z) = z⁻¹ := by simp [refl]
    simp only [map_add, map_sub, map_mul, map_div₀, map_ofNat, hcr]
  rw [← hc, norm_mul, norm_neg, norm_inv, norm_pow, RCLike.norm_conj]

theorem s2c_pre_gt {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {s : ℂ} (hs : s ∈ unitDisc) (hs0 : s ≠ 0) :
    ‖preSchwarzian (gTilde μ) s‖ = (‖s‖ ^ 2)⁻¹ *
      ‖preSchwarzian (gsans μ) s⁻¹ - 2 * deriv (gsans μ) s⁻¹ / gsans μ s⁻¹ + 2 / s⁻¹‖ := by
  obtain ⟨-, -, -, -, hgd, hgi, hg0, hg1, -, -⟩ := s2c_facts hμ
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hop : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hsn : ‖s‖ < 1 := mem_ball_zero_iff.mp hs
  have hsE : s⁻¹ ∈ unitDiscExterior := by
    show 1 < ‖s⁻¹‖
    rw [norm_inv]
    exact one_lt_inv₀ (norm_pos_iff.2 hs0) |>.2 hsn
  have hev : gTilde μ =ᶠ[𝓝 s] fun x => (gsans μ x⁻¹)⁻¹ := by
    filter_upwards [hop.mem_nhds ⟨hs, hs0⟩] with x hx
    have hx0 : x ≠ 0 := fun h => hx.2 (by simp [h])
    simp [gTilde, hx0, one_div]
  have hpre : preSchwarzian (gTilde μ) s = preSchwarzian (fun x => (gsans μ x⁻¹)⁻¹) s := by
    unfold preSchwarzian
    rw [hev.deriv_eq, hev.deriv.deriv_eq]
  rw [hpre, s2c_A_inv hopenE hgd hg0 hg1 hs0 hsE, norm_mul, norm_neg, norm_inv, norm_pow]

theorem s2c_pre_ft {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ‖preSchwarzian (fTilde μ) z‖ = (‖z‖ ^ 2)⁻¹ *
      ‖preSchwarzian (fsans μ) z⁻¹ - 2 * deriv (fsans μ) z⁻¹ / fsans μ z⁻¹ + 2 / z⁻¹‖ := by
  obtain ⟨hfd, hfi, hf0, -, -, -, -, -, hf0', hf1'⟩ := s2c_facts hμ
  have hE : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
  have hsE : z⁻¹ ∈ unitDisc \ {0} :=
    ⟨mem_ball_zero_iff.2 (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1), inv_ne_zero hz0⟩
  have hfe : fTilde μ = fun x => (fsans μ x⁻¹)⁻¹ := funext fun x => by simp [fTilde, one_div]
  rw [hfe, s2c_A_inv hE (hfd.mono Set.sdiff_subset) (fun w hw => hf0' w hw.1 hw.2)
    (fun w hw => hf1' w hw.1) hz0 hsE, norm_mul, norm_neg, norm_inv, norm_pow]

theorem s2c_null_sdiff : unitDisc \ {0} =ᵐ[volume] unitDisc :=
  sdiff_null_ae_eq_self (measure_singleton 0)

theorem s2c_meas_sdiff : MeasurableSet (unitDisc \ {0}) :=
  measurableSet_ball.diff (measurableSet_singleton _)

theorem s2c_T1 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∫ z in unitDisc, ‖preSchwarzian (fsans (beltramiInv μ)) z‖ ^ 2 =
      ∫ w in unitDiscExterior, ‖preSchwarzian (gsans μ) w - 2 * deriv (gsans μ) w / gsans μ w +
        2 / w‖ ^ 2 := by
  rw [← setIntegral_congr_set s2c_null_sdiff,
    s2c_refl_integral_real (fun w => ‖preSchwarzian (gsans μ) w - 2 * deriv (gsans μ) w / gsans μ w +
      2 / w‖ ^ 2)]
  refine setIntegral_congr_fun s2c_meas_sdiff fun z hz => ?_
  have hz0 : z ≠ 0 := fun h => hz.2 (by simp [h])
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
  rw [s2c_pre_F hμ hz.1 hz0]
  field_simp

theorem s2c_T2 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∫ z in unitDiscExterior, ‖preSchwarzian (gsans (beltramiInv μ)) z‖ ^ 2 =
      ∫ w in unitDisc, ‖preSchwarzian (fsans μ) w - 2 * deriv (fsans μ) w / fsans μ w +
        2 / w‖ ^ 2 := by
  rw [← setIntegral_congr_set s2c_null_sdiff,
    s2c_refl_integral_real' (fun w => ‖preSchwarzian (fsans μ) w - 2 * deriv (fsans μ) w / fsans μ w +
      2 / w‖ ^ 2)]
  refine setIntegral_congr_fun (isOpen_lt continuous_const continuous_norm).measurableSet
    fun z hz => ?_
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
  rw [s2c_pre_G hμ hz]
  field_simp

theorem s2c_T4 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∫ z in unitDisc, ‖preSchwarzian (gTilde μ) z‖ ^ 2 =
      ∫ w in unitDiscExterior, ‖preSchwarzian (gsans μ) w - 2 * deriv (gsans μ) w / gsans μ w +
        2 / w‖ ^ 2 := by
  rw [← setIntegral_congr_set s2c_null_sdiff,
    s2c_inv_integral_real' (fun w => ‖preSchwarzian (gsans μ) w - 2 * deriv (gsans μ) w / gsans μ w +
      2 / w‖ ^ 2)]
  refine setIntegral_congr_fun s2c_meas_sdiff fun s hs => ?_
  have hs0 : s ≠ 0 := fun h => hs.2 (by simp [h])
  have hn : ‖s‖ ≠ 0 := norm_ne_zero_iff.2 hs0
  rw [s2c_pre_gt hμ hs.1 hs0]
  field_simp

theorem s2c_T5 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∫ z in unitDiscExterior, ‖preSchwarzian (fTilde μ) z‖ ^ 2 =
      ∫ w in unitDisc, ‖preSchwarzian (fsans μ) w - 2 * deriv (fsans μ) w / fsans μ w +
        2 / w‖ ^ 2 := by
  rw [← setIntegral_congr_set s2c_null_sdiff,
    s2c_inv_integral_real (fun w => ‖preSchwarzian (fsans μ) w - 2 * deriv (fsans μ) w / fsans μ w +
      2 / w‖ ^ 2)]
  refine setIntegral_congr_fun (isOpen_lt continuous_const continuous_norm).measurableSet
    fun z hz => ?_
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
  rw [s2c_pre_ft hμ hz]
  field_simp

/-! ### Behaviour at `∞` -/

theorem s2c_tendsto_inv_cocompact :
    Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · rw [← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded
  · filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (0 : ℝ)] with z hz
    exact inv_ne_zero (norm_pos_iff.1 hz)

theorem s2c_slope_tendsto {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hf0 : f 0 = 0)
    (hf1 : deriv f 0 = 1) : Tendsto (fun s => f s / s) (𝓝[≠] 0) (𝓝 1) := by
  have h : HasDerivAt f 1 0 := by
    have := (hfd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))).hasDerivAt
    rwa [hf1] at this
  have := hasDerivAt_iff_tendsto_slope.1 h
  refine this.congr fun s => ?_
  simp [slope_def_field, hf0]

theorem s2c_fTilde_div {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Tendsto (fun z => fTilde μ z / z) (cocompact ℂ) (𝓝 1) := by
  obtain ⟨hfd, -, hf0, hf1, -⟩ := s2c_facts hμ
  have h1 := (s2c_slope_tendsto hfd hf0 hf1).inv₀ one_ne_zero
  have h2 := h1.comp s2c_tendsto_inv_cocompact
  rw [inv_one] at h2
  refine h2.congr' ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (0 : ℝ)] with z hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 hz
  simp [fTilde, one_div]
  field_simp

theorem s2c_fTilde_univ {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : IsUnivalentAtInfty (fTilde μ) := by
  obtain ⟨hfd, hfi, hf0, hf1, -, -, -, -, hf0', hf1'⟩ := s2c_facts hμ
  have hinvD : ∀ z ∈ unitDiscExterior, z ≠ 0 ∧ z⁻¹ ∈ unitDisc := by
    intro z hz
    have hz1 : 1 < ‖z‖ := hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
    exact ⟨hz0, mem_ball_zero_iff.2 (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1)⟩
  have hfe : fTilde μ = fun x => (fsans μ x⁻¹)⁻¹ := funext fun x => by simp [fTilde, one_div]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨hz0, hzD⟩ := hinvD z hz
    have h1 : DifferentiableAt ℂ (fsans μ) z⁻¹ := hfd.differentiableAt (isOpen_ball.mem_nhds hzD)
    have h2 : DifferentiableAt ℂ (fun x => (fsans μ x⁻¹)⁻¹) z :=
      (h1.comp z (differentiableAt_inv hz0)).inv (hf0' _ hzD (inv_ne_zero hz0))
    rw [hfe]
    exact h2.differentiableWithinAt
  · intro a ha b hb hab
    obtain ⟨ha0, haD⟩ := hinvD a ha
    obtain ⟨hb0, hbD⟩ := hinvD b hb
    rw [hfe] at hab
    have h1 : fsans μ a⁻¹ = fsans μ b⁻¹ := inv_injective hab
    exact inv_injective (hfi haD hbD h1)
  · have h := s2c_fTilde_div hμ
    have hn : Tendsto (fun z => ‖fTilde μ z / z‖) (cocompact ℂ) (𝓝 1) := by
      simpa using h.norm
    have hev1 : ∀ᶠ z in cocompact ℂ, (1 / 2 : ℝ) < ‖fTilde μ z / z‖ :=
      hn.eventually (lt_mem_nhds (by norm_num))
    have hev2 : ∀ᶠ z in cocompact ℂ, ‖z‖ / 2 ≤ ‖fTilde μ z‖ := by
      filter_upwards [hev1, tendsto_norm_cocompact_atTop.eventually_gt_atTop (0 : ℝ)] with z h1 h2
      have hz0 : z ≠ 0 := norm_pos_iff.1 h2
      have : ‖fTilde μ z‖ = ‖z‖ * ‖fTilde μ z / z‖ := by
        rw [norm_div]
        field_simp
      rw [this]
      nlinarith
    have hnorm : Tendsto (fun z => ‖fTilde μ z‖) (cocompact ℂ) atTop :=
      tendsto_atTop_mono' _ hev2 (tendsto_norm_cocompact_atTop.atTop_div_const (by norm_num))
    have := tendsto_norm_atTop_iff_cobounded.1 hnorm
    rwa [Metric.cobounded_eq_cocompact] at this

theorem s2c_fTilde_deriv {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : derivAtInfty (fTilde μ) = 1 :=
  (s2c_fTilde_div hμ).limUnder_eq

theorem s2c_derivAtInfty_G {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {H : ℂ → ℂ} {b : ℂ}
    (hH : EqOn H (fun z => conj b * refl (fsans μ (refl z))) unitDiscExterior) :
    derivAtInfty H = conj b := by
  obtain ⟨hfd, -, hf0, hf1, -⟩ := s2c_facts hμ
  have hs := s2c_slope_tendsto hfd hf0 hf1
  have hr : Tendsto (fun z : ℂ => refl z) (cocompact ℂ) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      have : (fun z : ℂ => ‖refl z‖) = fun z => ‖z‖⁻¹ := funext norm_refl
      rw [this]
      exact tendsto_inv_atTop_zero.comp tendsto_norm_cocompact_atTop
    · filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (0 : ℝ)] with z hz
      have hz0 : z ≠ 0 := norm_pos_iff.1 hz
      simpa [refl] using hz0
  have h1 : Tendsto (fun z : ℂ => conj (fsans μ (refl z) / refl z)) (cocompact ℂ) (𝓝 1) := by
    have := (Complex.continuous_conj.tendsto 1).comp (hs.comp hr)
    rw [map_one] at this
    exact this
  have key : Tendsto (fun z : ℂ => conj b * (conj (fsans μ (refl z) / refl z))⁻¹) (cocompact ℂ)
      (𝓝 (conj b)) := by
    have := (h1.inv₀ one_ne_zero).const_mul (conj b)
    simpa using this
  unfold derivAtInfty
  refine Tendsto.limUnder_eq (key.congr' ?_)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (1 : ℝ)] with z hz
  have hz' : z ∈ unitDiscExterior := hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
  rw [hH hz']
  simp only [refl, map_div₀, map_inv₀, Complex.conj_conj]
  field_simp

theorem s2c_gTilde_facts {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ b : ℂ, b ≠ 0 ∧ derivAtInfty (gsans μ) = b ∧ DifferentiableOn ℂ (gTilde μ) unitDisc ∧
      InjOn (gTilde μ) unitDisc ∧ gTilde μ 0 = 0 ∧ deriv (gTilde μ) 0 = b⁻¹ := by
  obtain ⟨φ, b, hφd, hφi, hφ0, hφ1, hb, hbg, hg⟩ :=
    g1_inverted_exterior (AppB.b8_welding_normalized_pair hμ)
  have hEq : EqOn (gTilde μ) (fun s => φ s / b) unitDisc := by
    intro s hs
    by_cases hs0 : s = 0
    · subst hs0
      simp [gTilde, hφ0]
    · have h' : gsans μ s⁻¹ = b / φ s := by simpa using hg s hs hs0
      simp only [gTilde, hs0, ↓reduceIte, one_div, h', inv_div]
  refine ⟨b, hb, hbg, (hφd.div_const b).congr hEq, ?_, by simp [gTilde], ?_⟩
  · intro x hx y hy h
    apply hφi hx hy
    have := (hEq hx).symm.trans (h.trans (hEq hy))
    exact (div_left_inj' hb).1 this
  · have hev : gTilde μ =ᶠ[𝓝 0] fun s => φ s / b :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) hEq
    rw [hev.deriv_eq, deriv_div_const, hφ1]
    simp

theorem s2c_pre_congr {f g : ℂ → ℂ} {S : Set ℂ} (h : EqOn f g S) (hS : IsOpen S) {z : ℂ} (hz : z ∈ S) :
    preSchwarzian f z = preSchwarzian g z := by
  unfold preSchwarzian
  rw [(h.deriv hS) hz, ((h.deriv hS).deriv hS) hz]

/-- (TT:4680–4690) By (1.3), for `[μ] ∈ T₀(1)`:
- `S̃₁([μ]) = ∬_𝔻 |𝒜(𝖿^μ) - 2(𝖿^μ)'/𝖿^μ + 2/z|² + ∬_{𝔻*} |𝒜(𝗀_μ) - 2𝗀_μ'/𝗀_μ + 2/z|² - 4π log |𝗀_μ'(∞)|`;
- this equals `∬_𝔻 |𝒜(g̃_μ)|² + ∬_{𝔻*} |𝒜(f̃^μ)|² + 4π log |g̃_μ'(0)|`.

Moreover `f̃^μ(∞) = ∞`, `(f̃^μ)'(∞) = 1` and `g̃_μ(0) = 0`. 
Proved here as `s2c_liouvilleS1Tilde_eq`; statement identical to `liouvilleS1Tilde_eq`. -/
theorem s2c_liouvilleS1Tilde_eq {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    liouvilleS1Tilde p =
        (∫ z in unitDisc, ‖preSchwarzian (fsans μ) z - 2 * deriv (fsans μ) z / fsans μ z + 2 / z‖ ^ 2) +
          (∫ z in unitDiscExterior, ‖preSchwarzian (gsans μ) z - 2 * deriv (gsans μ) z / gsans μ z + 2 / z‖ ^ 2) -
          4 * π * Real.log ‖derivAtInfty (gsans μ)‖ ∧
      liouvilleS1Tilde p =
        (∫ z in unitDisc, ‖preSchwarzian (gTilde μ) z‖ ^ 2) + (∫ z in unitDiscExterior, ‖preSchwarzian (fTilde μ) z‖ ^ 2) +
          4 * π * Real.log ‖deriv (gTilde μ) 0‖ ∧
      IsUnivalentAtInfty (fTilde μ) ∧ derivAtInfty (fTilde μ) = 1 ∧ DifferentiableOn ℂ (gTilde μ) unitDisc ∧
      InjOn (gTilde μ) unitDisc ∧ gTilde μ 0 = 0 := by
  intro μ
  have _hp := hp
  have hμ : (μ : LinfStar) ∈ LinfStarBall := (Quotient.out p).2
  have hi : beltramiInv μ ∈ LinfStarBall := bc_beltramiInv_mem_ball hμ
  have hinv : invT p = Phi ⟨beltramiInv μ, hi⟩ := by
    unfold invT
    exact dif_pos hi
  set ν : LinfStarBall := Quotient.out (invT p) with hν
  have hcl : teichSetoid ν ⟨beltramiInv μ, hi⟩ := by
    have h : Phi ν = Phi ⟨beltramiInv μ, hi⟩ := by
      rw [← hinv]
      exact Quotient.out_eq (invT p)
    exact Quotient.exact h
  obtain ⟨hF, hG⟩ := s2c_class_pair hcl
  obtain ⟨b, hb, hbg, hgtd, hgti, hgt0, hgtd0⟩ := s2c_gTilde_facts hμ
  have hopenD : IsOpen unitDisc := isOpen_ball
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hdG : derivAtInfty (gsans (ν : LinfStar)) = conj b := by
    refine s2c_derivAtInfty_G hμ (b := b) (fun z hz => ?_)
    rw [hG hz, (w3_eq_1_3 hμ).2 z hz, hbg]
  have hS : liouvilleS1Tilde p =
      (∫ z in unitDisc, ‖preSchwarzian (fsans (beltramiInv μ)) z‖ ^ 2) +
        (∫ z in unitDiscExterior, ‖preSchwarzian (gsans (beltramiInv μ)) z‖ ^ 2) -
          4 * π * Real.log ‖conj b‖ := by
    show liouvilleS1 (invT p) = _
    unfold liouvilleS1
    have e1 : ∫ z in unitDisc, ‖preSchwarzian (fsans (ν : LinfStar)) z‖ ^ 2 =
        ∫ z in unitDisc, ‖preSchwarzian (fsans (beltramiInv μ)) z‖ ^ 2 :=
      setIntegral_congr_fun hopenD.measurableSet fun z hz => by rw [s2c_pre_congr hF hopenD hz]
    have e2 : ∫ z in unitDiscExterior, ‖preSchwarzian (gsans (ν : LinfStar)) z‖ ^ 2 =
        ∫ z in unitDiscExterior, ‖preSchwarzian (gsans (beltramiInv μ)) z‖ ^ 2 :=
      setIntegral_congr_fun hopenE.measurableSet fun z hz => by rw [s2c_pre_congr hG hopenE hz]
    show (∫ z in unitDisc, ‖preSchwarzian (fsans (ν : LinfStar)) z‖ ^ 2) +
      (∫ z in unitDiscExterior, ‖preSchwarzian (gsans (ν : LinfStar)) z‖ ^ 2) -
        4 * π * Real.log ‖derivAtInfty (gsans (ν : LinfStar))‖ = _
    rw [e1, e2, hdG]
  refine ⟨?_, ?_, s2c_fTilde_univ hμ, s2c_fTilde_deriv hμ, hgtd, hgti, hgt0⟩
  · rw [hS, s2c_T1 hμ, s2c_T2 hμ, hbg, norm_conj]
    ring
  · rw [hS, s2c_T1 hμ, s2c_T2 hμ, s2c_T4 hμ, s2c_T5 hμ, hgtd0, norm_inv, Real.log_inv, norm_conj]
    ring

/-! ### Original relocated (2026-10-26) -/

/-- (TT:4680–4690) By (1.3), for `[μ] ∈ T₀(1)`:
- `S̃₁([μ]) = ∬_𝔻 |𝒜(𝖿^μ) - 2(𝖿^μ)'/𝖿^μ + 2/z|² + ∬_{𝔻*} |𝒜(𝗀_μ) - 2𝗀_μ'/𝗀_μ + 2/z|² - 4π log |𝗀_μ'(∞)|`;
- this equals `∬_𝔻 |𝒜(g̃_μ)|² + ∬_{𝔻*} |𝒜(f̃^μ)|² + 4π log |g̃_μ'(0)|`.

Moreover `f̃^μ(∞) = ∞`, `(f̃^μ)'(∞) = 1` and `g̃_μ(0) = 0`. -/
theorem liouvilleS1Tilde_eq {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    liouvilleS1Tilde p =
        (∫ z in unitDisc, ‖preSchwarzian (fsans μ) z - 2 * deriv (fsans μ) z / fsans μ z + 2 / z‖ ^ 2) +
          (∫ z in unitDiscExterior, ‖preSchwarzian (gsans μ) z - 2 * deriv (gsans μ) z / gsans μ z + 2 / z‖ ^ 2) -
          4 * π * Real.log ‖derivAtInfty (gsans μ)‖ ∧
      liouvilleS1Tilde p =
        (∫ z in unitDisc, ‖preSchwarzian (gTilde μ) z‖ ^ 2) + (∫ z in unitDiscExterior, ‖preSchwarzian (fTilde μ) z‖ ^ 2) +
          4 * π * Real.log ‖deriv (gTilde μ) 0‖ ∧
      IsUnivalentAtInfty (fTilde μ) ∧ derivAtInfty (fTilde μ) = 1 ∧ DifferentiableOn ℂ (gTilde μ) unitDisc ∧
      InjOn (gTilde μ) unitDisc ∧ gTilde μ 0 = 0 :=
  s2c_liouvilleS1Tilde_eq hp

end Ch2

end TakhtajanTeo
