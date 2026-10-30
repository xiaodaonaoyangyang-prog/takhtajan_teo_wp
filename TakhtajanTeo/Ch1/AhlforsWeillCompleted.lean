import TakhtajanTeo.Ch1.HomogeneousCompleted
import TakhtajanTeo.Ch1.BeltramiCompose

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Cayley map `𝔻 → 𝕃`, `w ↦ i (w+1)/(w-1)`. -/
def awG (w : ℂ) : ℂ := I * (w + 1) / (w - 1)
def awGd (w : ℂ) : ℂ := -2 * I / (w - 1) ^ 2
/-- Inverse Cayley map `𝕃 → 𝔻`, `z ↦ (z+i)/(z-i)`. -/
def awQ (z : ℂ) : ℂ := (z + I) / (z - I)
def awQd (z : ℂ) : ℂ := -2 * I / (z - I) ^ 2

theorem aw_Q_G {w : ℂ} (hw : w - 1 ≠ 0) : awQ (awG w) = w := by
  unfold awQ awG
  have h2 : I * (w + 1) / (w - 1) - I ≠ 0 := by
    intro h
    have : I * (w + 1) - I * (w - 1) = 0 := by
      field_simp at h
      linear_combination h
    have h3 : (2 : ℂ) * I = 0 := by linear_combination this
    simp at h3
  field_simp
  ring

theorem aw_G_ne {w : ℂ} (hw : w - 1 ≠ 0) : awG w - I ≠ 0 := by
  unfold awG
  intro h
  field_simp at h
  have h3 : (2 : ℂ) * I = 0 := by linear_combination h
  simp at h3

theorem aw_Qd_G {w : ℂ} (hw : w - 1 ≠ 0) : awQd (awG w) * awGd w = 1 := by
  unfold awQd awGd awG
  have h2 : I * (w + 1) / (w - 1) - I = 2 * I / (w - 1) := by
    field_simp
    ring
  rw [h2]
  field_simp

theorem aw_conj_Q_G {w : ℂ} (hw : 1 < ‖w‖) :
    awQ (conj (awG w)) = (conj w)⁻¹ := by
  have hw1 : w - 1 ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination h
    rw [this] at hw
    norm_num at hw
  have hw1' : conj w - 1 ≠ 0 := by
    intro h
    apply hw1
    have := congrArg conj h
    simpa using this
  have hw0 : conj w ≠ 0 := by
    intro h
    have : w = 0 := by simpa using h
    rw [this] at hw
    norm_num at hw
  unfold awQ awG
  simp only [map_div₀, map_mul, map_add, map_sub, Complex.conj_I, map_one]
  have h2 : -I * (conj w + 1) / (conj w - 1) - I ≠ 0 := by
    intro h
    field_simp at h
    have : (-2 : ℂ) * I * conj w = 0 := by linear_combination h
    simp [hw0] at this
  apply eq_inv_of_mul_eq_one_left
  rw [div_mul_eq_mul_div, div_eq_iff h2]
  field_simp
  ring

theorem aw_dil_alg {w : ℂ} (hw : 1 < ‖w‖) (P : ℂ) :
    -2 * (((awG w).im : ℝ) : ℂ) ^ 2 * (P * awQd (conj (awG w)) ^ 2) * (conj (awGd w) / awGd w) =
      -(1 / 2) * (1 - ((‖w‖ : ℝ) : ℂ) ^ 2) ^ 2 * P / conj w ^ 4 := by
  have hw1 : w - 1 ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination h
    rw [this] at hw
    norm_num at hw
  have hw1' : conj w - 1 ≠ 0 := by
    intro h
    apply hw1
    have := congrArg conj h
    simpa using this
  have hw0 : conj w ≠ 0 := by
    intro h
    have : w = 0 := by simpa using h
    rw [this] at hw
    norm_num at hw
  have hnorm : ((‖w‖ : ℝ) : ℂ) ^ 2 = w * conj w := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hy : (((awG w).im : ℝ) : ℂ) = (w * conj w - 1) / ((w - 1) * (conj w - 1)) := by
    have h1 := Complex.sub_conj (awG w)
    have h2 : (((awG w).im : ℝ) : ℂ) = (awG w - conj (awG w)) / (2 * I) := by
      rw [h1]
      push_cast
      field_simp
    rw [h2]
    unfold awG
    simp only [map_div₀, map_mul, map_add, map_sub, Complex.conj_I, map_one]
    field_simp
    ring
  have hd : conj (awG w) - I = -2 * I * conj w / (conj w - 1) := by
    unfold awG
    simp only [map_div₀, map_mul, map_add, map_sub, Complex.conj_I, map_one]
    field_simp
    ring
  have hd0 : conj (awG w) - I ≠ 0 := by
    rw [hd]
    have : (-2 : ℂ) * I * conj w ≠ 0 := by simp [hw0]
    exact div_ne_zero this hw1'
  rw [hy, hnorm]
  unfold awQd awGd
  rw [hd]
  simp only [map_div₀, map_mul, map_pow, map_neg, map_sub, map_one, Complex.conj_I, map_ofNat]
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- `φ̃(z) = φ(Q z) Q'(z)²`, the pull-back of a disc quadratic differential to the lower half-plane. -/
def awPhi (φ : AInf unitDisc) (z : ℂ) : ℂ := AInf.toFun φ (awQ z) * awQd z ^ 2

theorem aw_ne {z : ℂ} (hz : z.im < 0) : z - I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem aw_sqnorm (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem aw_Q_mem {z : ℂ} (hz : z.im < 0) : awQ z ∈ unitDisc := by
  unfold awQ
  rw [unitDisc, mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.2 (aw_ne hz))]
  have h1 : ‖z + I‖ ^ 2 < ‖z - I‖ ^ 2 := by
    rw [aw_sqnorm, aw_sqnorm]
    simp
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

theorem aw_one_sub_Q {z : ℂ} (hz : z.im < 0) :
    1 - ‖awQ z‖ ^ 2 = -4 * z.im / ‖z - I‖ ^ 2 := by
  have hd : ‖z - I‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (aw_ne hz))
  have h1 : ‖z + I‖ ^ 2 = ‖z - I‖ ^ 2 + 4 * z.im := by
    rw [aw_sqnorm, aw_sqnorm]
    simp
    ring
  unfold awQ
  rw [norm_div, div_pow, h1]
  generalize ‖z - I‖ ^ 2 = d at hd ⊢
  field_simp
  ring

theorem aw_Qd_norm (z : ℂ) : ‖awQd z‖ = 2 / ‖z - I‖ ^ 2 := by
  unfold awQd
  rw [norm_div, norm_pow]
  simp

theorem aw_weighted {φ : AInf unitDisc} {u : ℂ} (hu : u ∈ unitDisc) :
    ‖AInf.toFun φ u‖ * (1 - ‖u‖ ^ 2) ^ 2 ≤ ‖φ‖ := by
  have hn : ‖u‖ < 1 := mem_ball_zero_iff.1 hu
  have hpos : 0 < (1 - ‖u‖ ^ 2) ^ 2 := by
    have : 0 < 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
    positivity
  have hb := φ.1.norm_coe_le_norm ⟨u, hu⟩
  change ‖φ.1 _‖ ≤ ‖φ‖ at hb
  have hc : (((1 - ‖u‖ ^ 2) ^ 2 : ℝ) : ℂ) = (1 - (‖u‖ : ℂ) ^ 2) ^ 2 := by push_cast; ring
  have hne : (1 - (‖u‖ : ℂ) ^ 2) ^ 2 ≠ 0 := by
    rw [← hc]
    exact_mod_cast hpos.ne'
  have he : φ.1 ⟨u, hu⟩ = AInf.toFun φ u * (((1 - ‖u‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
    rw [hc]
    simp only [AInf.toFun, unweight, dif_pos hu]
    exact (div_mul_cancel₀ _ hne).symm
  rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le] at hb
  exact hb

theorem aw_phi_bound (φ : AInf unitDisc) {z : ℂ} (hz : z.im < 0) :
    ‖awPhi φ z‖ * z.im ^ 2 ≤ ‖φ‖ / 4 := by
  have hd : 0 < ‖z - I‖ ^ 2 := pow_pos (norm_pos_iff.2 (aw_ne hz)) 2
  have hw := aw_weighted (φ := φ) (aw_Q_mem hz)
  rw [aw_one_sub_Q hz] at hw
  unfold awPhi
  rw [norm_mul, norm_pow, aw_Qd_norm]
  have h1 : (-4 * z.im / ‖z - I‖ ^ 2) ^ 2 = 16 * z.im ^ 2 / (‖z - I‖ ^ 2) ^ 2 := by
    field_simp
    ring
  rw [h1] at hw
  have h2 : (2 / ‖z - I‖ ^ 2) ^ 2 = 4 / (‖z - I‖ ^ 2) ^ 2 := by
    rw [div_pow]
    norm_num
  rw [h2]
  have h3 : ‖AInf.toFun φ (awQ z)‖ * (4 / (‖z - I‖ ^ 2) ^ 2) * z.im ^ 2 =
      (‖AInf.toFun φ (awQ z)‖ * (16 * z.im ^ 2 / (‖z - I‖ ^ 2) ^ 2)) / 4 := by
    field_simp
    ring
  rw [h3]
  linarith

theorem aw_phi_diff (φ : AInf unitDisc) : DifferentiableOn ℂ (awPhi φ) lowerHalf := by
  have hQ : DifferentiableOn ℂ awQ lowerHalf := by
    unfold awQ
    exact DifferentiableOn.div (by fun_prop) (by fun_prop) (fun z hz => aw_ne hz)
  have hQd : DifferentiableOn ℂ awQd lowerHalf := by
    unfold awQd
    exact DifferentiableOn.div (by fun_prop) (by fun_prop) (fun z hz => pow_ne_zero 2 (aw_ne hz))
  unfold awPhi
  exact (φ.property.comp hQ (fun z hz => aw_Q_mem hz)).mul (hQd.pow 2)



theorem aw_G_im {w : ℂ} (hw1 : w - 1 ≠ 0) : (awG w).im = (‖w‖ ^ 2 - 1) / ‖w - 1‖ ^ 2 := by
  have hw1' : conj w - 1 ≠ 0 := by
    intro h
    apply hw1
    have := congrArg conj h
    simpa using this
  have hnorm : ((‖w‖ : ℝ) : ℂ) ^ 2 = w * conj w := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hnorm1 : ((‖w - 1‖ : ℝ) : ℂ) ^ 2 = (w - 1) * (conj w - 1) := by
    have := Complex.mul_conj (w - 1)
    rw [Complex.normSq_eq_norm_sq] at this
    simp only [map_sub, map_one] at this
    push_cast at this
    rw [← this]
  apply Complex.ofReal_injective
  have h1 := Complex.sub_conj (awG w)
  have h2 : (((awG w).im : ℝ) : ℂ) = (awG w - conj (awG w)) / (2 * I) := by
    rw [h1]
    push_cast
    field_simp
  rw [h2]
  push_cast
  rw [hnorm, hnorm1]
  unfold awG
  simp only [map_div₀, map_mul, map_add, map_sub, Complex.conj_I, map_one]
  field_simp
  ring

theorem aw_G_im_pos {w : ℂ} (hw : 1 < ‖w‖) : 0 < (awG w).im := by
  have hw1 : w - 1 ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination h
    rw [this] at hw
    norm_num at hw
  rw [aw_G_im hw1]
  have : 1 < ‖w‖ ^ 2 := by nlinarith
  exact div_pos (by linarith) (pow_pos (norm_pos_iff.2 hw1) 2)

theorem aw_G_im_neg {w : ℂ} (hw : ‖w‖ < 1) : (awG w).im < 0 := by
  have hw1 : w - 1 ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination h
    rw [this] at hw
    norm_num at hw
  rw [aw_G_im hw1]
  have : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
  exact div_neg_of_neg_of_pos (by linarith) (pow_pos (norm_pos_iff.2 hw1) 2)

theorem aw_hasDerivAt_G {w : ℂ} (hw : w - 1 ≠ 0) : HasDerivAt awG (awGd w) w := by
  have h1 : HasDerivAt (fun w : ℂ => I * (w + 1)) I w := by
    simpa using ((hasDerivAt_id w).add_const 1).const_mul I
  have h2 : HasDerivAt (fun w : ℂ => w - 1) 1 w := (hasDerivAt_id w).sub_const 1
  have h3 := h1.div h2 hw
  unfold awG awGd
  convert h3 using 1
  field_simp
  ring



theorem aw_gS_det : I * (-1 : ℂ) - I * 1 ≠ 0 := by
  have : I * (-1 : ℂ) - I * 1 = -2 * I := by ring
  rw [this]
  simp

theorem aw_gS_mobius : IsMobius (mobiusExt I I 1 (-1)) := ⟨I, I, 1, -1, aw_gS_det, rfl⟩

theorem aw_gS_coe {u : ℂ} (hu : u - 1 ≠ 0) :
    mobiusExt I I 1 (-1) (u : ExtPlane) = ((awG u : ℂ) : ExtPlane) := by
  have h : (1 : ℂ) * u + -1 ≠ 0 := by
    intro h
    apply hu
    linear_combination h
  rw [mobiusExt_coe h]
  congr 1
  unfold mobiusFn awG
  ring

theorem aw_gS_pole {u : ℂ} (hu : u - 1 = 0) : mobiusExt I I 1 (-1) (u : ExtPlane) = extInf :=
  mobiusExt_coe_of_eq_zero (by linear_combination hu)

theorem aw_isMobius_bijective {F : ExtPlane → ExtPlane} (hF : IsMobius F) : Function.Bijective F := by
  obtain ⟨G, -, hGF, hFG⟩ := isMobius_inverse hF
  exact ⟨isMobius_injective hF, fun q => ⟨G q, hFG q⟩⟩

theorem aw_F1 {K : ℝ} {e : ℂ ≃ₜ ℂ} (hH : IsKQC (⇑e) univ K) :
    ∃ R : ExtPlane → ExtPlane, IsMobius R ∧ ∃ F₁ : ℂ → ℂ, (∃ K' : ℝ, IsKQC F₁ univ K') ∧
      F₁ '' univ = univ ∧ Function.Injective F₁ ∧
      (∀ u : ℂ, u - 1 ≠ 0 → R ((e (awG u) : ℂ) : ExtPlane) = ((F₁ u : ℂ) : ExtPlane)) ∧
      ∀ᵐ w : ℂ, w - 1 ≠ 0 → complexDilatation F₁ w = complexDilatation (fun u => e (awG u)) w := by
  have hgS := aw_gS_mobius
  obtain ⟨Gs, hGs⟩ : ∃ Gs : ExtPlane → ExtPlane,
      Gs = fun p => e.onePointCongr (mobiusExt I I 1 (-1) p) := ⟨_, rfl⟩
  have hGb : Function.Bijective Gs := by
    rw [hGs]
    exact e.onePointCongr.bijective.comp (aw_isMobius_bijective hgS)
  have hGc : Continuous Gs := by
    rw [hGs]
    exact e.onePointCongr.continuous.comp (continuous_mobiusExt aw_gS_det)
  obtain ⟨R, hR, F₁, hF₁c, hF₁b, hRF, hRq⟩ := plane_map_of_sphere_homeo hGb hGc
  have hGsu : ∀ u : ℂ, u - 1 ≠ 0 → Gs (u : ExtPlane) = ((e (awG u) : ℂ) : ExtPlane) := by
    intro u hu
    rw [hGs]
    show e.onePointCongr (mobiusExt I I 1 (-1) (u : ExtPlane)) = _
    rw [aw_gS_coe hu]
    rfl
  have hRel : ∀ u : ℂ, u - 1 ≠ 0 → R ((e (awG u) : ℂ) : ExtPlane) = ((F₁ u : ℂ) : ExtPlane) := by
    intro u hu
    rw [← hGsu u hu]
    exact hRF u
  refine ⟨R, hR, F₁, ?_, image_univ_of_surjective hF₁b.2, hF₁b.1, hRel, ?_⟩
  all_goals
    obtain ⟨D, hD⟩ : ∃ D : Set ℂ, D = {u : ℂ | mobiusExt I I 1 (-1) (u : ExtPlane) ≠ extInf} := ⟨_, rfl⟩
    have hDo : IsOpen D := by rw [hD]; exact mobius_finite_open hgS
    have hDu : ∀ u ∈ D, u - 1 ≠ 0 := by
      intro u hu h
      rw [hD] at hu
      exact hu (aw_gS_pole h)
    have hDm : ∀ u : ℂ, u - 1 ≠ 0 → u ∈ D := by
      intro u hu
      rw [hD]
      show mobiusExt I I 1 (-1) (u : ExtPlane) ≠ extInf
      rw [aw_gS_coe hu]
      exact OnePoint.coe_ne_infty _
    have hfp : ∀ u : ℂ, u - 1 ≠ 0 → finPart (mobiusExt I I 1 (-1) (u : ExtPlane)) = awG u := by
      intro u hu
      rw [aw_gS_coe hu]
      rfl
    have hgK : IsKQC (fun u : ℂ => finPart (mobiusExt I I 1 (-1) (u : ExtPlane))) D 1 := by
      have := mobius_finite_conformal hgS
      rw [← hD] at this
      exact isKQC_one_of_conformal hDo this
    have hHg := thm7_1_comp hgK hH (subset_univ _)
    have hRc := mobius_finite_conformal hR
    have hmaps : (⇑e ∘ fun u : ℂ => finPart (mobiusExt I I 1 (-1) (u : ExtPlane))) '' D ⊆
        {u : ℂ | R (u : ExtPlane) ≠ extInf} := by
      rintro _ ⟨u, hu, rfl⟩
      have hu1 := hDu u hu
      show R ((e (finPart (mobiusExt I I 1 (-1) (u : ExtPlane))) : ℂ) : ExtPlane) ≠ extInf
      rw [hfp u hu1, hRel u hu1]
      exact OnePoint.coe_ne_infty _
    have hcomp := bg_comp_conformal hHg (mobius_finite_open hR) hRc hmaps
    have heq : EqOn F₁ ((fun u : ℂ => finPart (R (u : ExtPlane))) ∘ (⇑e ∘ fun u : ℂ =>
        finPart (mobiusExt I I 1 (-1) (u : ExtPlane)))) D := by
      intro u hu
      have hu1 := hDu u hu
      show F₁ u = finPart (R ((e (finPart (mobiusExt I I 1 (-1) (u : ExtPlane))) : ℂ) : ExtPlane))
      rw [hfp u hu1, hRel u hu1]
      rfl
    have heq2 : EqOn (⇑e ∘ fun u : ℂ => finPart (mobiusExt I I 1 (-1) (u : ExtPlane)))
        (fun u => e (awG u)) D := by
      intro u hu
      show e (finPart (mobiusExt I I 1 (-1) (u : ExtPlane))) = _
      rw [hfp u (hDu u hu)]
  · have hF₁D : IsKQC F₁ D (1 * K) := ad_isKQC_congr hcomp.1 heq
    have hhom := qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hF₁c.continuousOn hF₁b.1.injOn
    have hsub : {z : ℂ | z ∈ (univ : Set ℂ) ∧ ¬ (mobiusExt I I 1 (-1) (z : ExtPlane) ≠ extInf)}.Subsingleton := by
      intro z1 h1 z2 h2
      have e1 : mobiusExt I I 1 (-1) (z1 : ExtPlane) = extInf := by
        by_contra h
        exact h1.2 h
      have e2 : mobiusExt I I 1 (-1) (z2 : ExtPlane) = extInf := by
        by_contra h
        exact h2.2 h
      exact OnePoint.coe_injective (isMobius_injective hgS (e1.trans e2.symm))
    exact ⟨1 * K, iskqc_of_subsingleton_exceptional (P := fun z => mobiusExt I I 1 (-1) (z : ExtPlane) ≠ extInf)
      isOpen_univ hhom hHg.2.1 (fun z _ => mem_univ z) hsub (hD ▸ hF₁D)⟩
  · filter_upwards [(ae_restrict_iff' hDo.measurableSet).1 hcomp.2] with w hw hw1
    have hwD := hDm w hw1
    rw [bg_dilatation_congr hDo heq hwD, hw hwD, bg_dilatation_congr hDo heq2 hwD]



theorem aw_awQ_diff {z : ℂ} (hz : z - I ≠ 0) : DifferentiableAt ℂ awQ z := by
  unfold awQ
  exact DifferentiableAt.div (by fun_prop) (by fun_prop) hz

theorem aw_dil_comp {φ : AInf unitDisc} {K : ℝ} {e : ℂ ≃ₜ ℂ} (hH : IsKQC (⇑e) univ K)
    (hHd : DifferentiableOn ℂ (⇑e) lowerHalf)
    (hHμ : ∀ z ∈ upperHalf, complexDilatation (⇑e) z = -2 * (z.im : ℂ) ^ 2 * awPhi φ (conj z)) :
    ∀ᵐ w : ℂ, w - 1 ≠ 0 → complexDilatation (fun u => e (awG u)) w = extB (Lambda φ) w := by
  have hmeas : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have A1 : ∀ᵐ w : ℂ, w ∈ unitDiscExterior → (Lambda φ : ℂ → ℂ) w =
      -(1 / 2 : ℂ) * (1 - ‖w‖ ^ 2) ^ 2 * AInf.toFun φ (refl w) / conj w ^ 4 :=
    (ae_restrict_iff' hmeas).1 (bc_toLinf_ae (Lambda_kernel_memLp φ))
  have A0 : ∀ᵐ z : ℂ, DifferentiableAt ℝ (⇑e) z := by
    have := thm9_3_differentiable_ae hH
    rwa [Measure.restrict_univ] at this
  have A2 : ∀ᵐ w : ℂ, w - 1 ≠ 0 → DifferentiableAt ℝ (⇑e) (awG w) := by
    have hN0 : volume {z : ℂ | ¬ DifferentiableAt ℝ (⇑e) z} = 0 := ae_iff.1 A0
    have hS : volume ({z : ℂ | ¬ DifferentiableAt ℝ (⇑e) z} ∩ {z : ℂ | z - I ≠ 0}) = 0 :=
      measure_mono_null inter_subset_left hN0
    have hdiff : DifferentiableOn ℝ awQ
        ({z : ℂ | ¬ DifferentiableAt ℝ (⇑e) z} ∩ {z : ℂ | z - I ≠ 0}) := fun z hz =>
      ((aw_awQ_diff hz.2).restrictScalars ℝ).differentiableWithinAt
    have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hS
    refine ae_iff.2 (measure_mono_null (fun w hw => ?_) himg)
    obtain ⟨hw1, hw2⟩ := not_imp.1 hw
    exact ⟨awG w, ⟨hw2, aw_G_ne hw1⟩, aw_Q_G hw1⟩
  have A3 : ∀ᵐ w : ℂ, w ∉ Metric.sphere (0 : ℂ) 1 :=
    measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume 0 1)
  filter_upwards [A1, A2, A3] with w a1 a2 a3 hw1
  have hderiv := aw_hasDerivAt_G hw1
  have hd0 : deriv awG w ≠ 0 := by
    rw [hderiv.deriv]
    unfold awGd
    exact div_ne_zero (by simp) (pow_ne_zero 2 hw1)
  rcases lt_trichotomy ‖w‖ 1 with h | h | h
  · have hg : DifferentiableAt ℂ (⇑e) (awG w) :=
      hHd.differentiableAt (isOpen_lowerHalf.mem_nhds (aw_G_im_neg h))
    have hdz : complexDilatation (fun u => e (awG u)) w =
        complexDilatation (⇑e) (awG w) * (conj (deriv awG w) / deriv awG w) :=
      complexDilatation_comp_conformal_right hderiv.differentiableAt hd0 (hg.restrictScalars ℝ)
    rw [hdz, complexDilatation_eq_zero_of_diffAt hg, zero_mul, extB,
      indicator_of_notMem (show w ∉ unitDiscExterior from fun hh => absurd (show 1 < ‖w‖ from hh) (not_lt.2 h.le))]
  · exact absurd (mem_sphere_zero_iff_norm.2 h) a3
  · have hwE : w ∈ unitDiscExterior := h
    have hdz : complexDilatation (fun u => e (awG u)) w =
        complexDilatation (⇑e) (awG w) * (conj (deriv awG w) / deriv awG w) :=
      complexDilatation_comp_conformal_right hderiv.differentiableAt hd0 (a2 hw1)
    rw [hdz, hHμ _ (aw_G_im_pos h), hderiv.deriv, extB, indicator_of_mem hwE, a1 hwE]
    unfold awPhi
    rw [aw_conj_Q_G h]
    have := aw_dil_alg h (AInf.toFun φ (conj w)⁻¹)
    simpa [refl] using this



theorem ahlfors_weill_cand {φ : AInf unitDisc} (hφ : ‖φ‖ < 2) :
    ∃ h : Lambda φ ∈ LinfStarBall, bers (Phi ⟨Lambda φ, h⟩) = φ := by
  have hnn : 0 ≤ ‖φ‖ := norm_nonneg _
  have hμball : Lambda φ ∈ LinfStarBall := Lambda_mem_ball hφ
  refine ⟨hμball, ?_⟩
  obtain ⟨H, K, hH, hHs, hH0, hH1, hHd, hHS, hHμ⟩ :=
    l333_core (s := ‖φ‖ / 4) (by positivity) (by linarith) (aw_phi_diff φ)
      (fun z hz => aw_phi_bound φ hz)
  obtain ⟨e, he⟩ := t1_homeomorph hH hHs
  subst he
  obtain ⟨R, hR, F₁, ⟨K', hK'⟩, hF₁s, hF₁i, hRel, hdil⟩ := aw_F1 hH
  have hdilμ := aw_dil_comp hH hHd hHμ
  obtain ⟨hBμ, -⟩ := wB_spec hμball
  obtain ⟨N, hN, V, hV, hvf, hvi, f, hf, hf0, hf1, hfp⟩ := hBμ
  have hz1 : ∀ᵐ z : ℂ, z - 1 ≠ 0 :=
    ae_iff.2 (by simpa [sub_eq_zero] using measure_singleton (1 : ℂ))
  obtain ⟨ψ, hψ, hVψ⟩ := uq_conformal_auto isOpen_univ ⟨K', hK'⟩ hV.1 hF₁s hV.2.1
    (by
      rw [Measure.restrict_univ]
      filter_upwards [hdil, hdilμ, hV.2.2.2.2, hz1] with z a b c d
      rw [a d, b d, c])
  obtain ⟨a, b, ha, hab⟩ := nx_entire_affine hψ
  have hVu : ∀ u, V u = a * F₁ u + b := fun u => by rw [hVψ u (mem_univ u), hab]
  have haff : IsMobius (mobiusExt a b 0 1) := ⟨a, b, 0, 1, by simp [ha], rfl⟩
  have haffc : ∀ x : ℂ, mobiusExt a b 0 1 (x : ExtPlane) = ((a * x + b : ℂ) : ExtPlane) := by
    intro x
    rw [mobiusExt_coe (by simp)]
    congr 1
    simp [mobiusFn]
  have hM : IsMobius (fun p => N (mobiusExt a b 0 1 (R p))) := isMobius_comp (isMobius_comp hR haff) hN
  obtain ⟨a', b', c', d', hdet, hMe⟩ := hM
  have hz1' : ∀ z ∈ unitDisc, z - 1 ≠ 0 := by
    intro z hz h
    have : z = 1 := by linear_combination h
    rw [this] at hz
    simp [unitDisc] at hz
  have hfM : ∀ z ∈ unitDisc, ((f z : ℂ) : ExtPlane) =
      mobiusExt a' b' c' d' ((e (awG z) : ℂ) : ExtPlane) := by
    intro z hz
    rw [← hMe]
    show _ = N (mobiusExt a b 0 1 (R ((e (awG z) : ℂ) : ExtPlane)))
    rw [hRel z (hz1' z hz), haffc, ← hVu, ← hvf z, hf z hz]
  have hden : ∀ z ∈ unitDisc, c' * e (awG z) + d' ≠ 0 := by
    intro z hz h
    have := hfM z hz
    rw [mobiusExt_coe_of_eq_zero h] at this
    exact OnePoint.coe_ne_infty _ this
  have hfform : ∀ z ∈ unitDisc, f z = (a' * e (awG z) + b') / (c' * e (awG z) + d') := by
    intro z hz
    have := hfM z hz
    rw [mobiusExt_coe (hden z hz)] at this
    exact OnePoint.coe_injective this
  -- the Schwarzian
  have hSch : ∀ z ∈ unitDisc, schwarzianHol (fB (Lambda φ)) z = AInf.toFun φ z := by
    intro z hz
    have hz1z := hz1' z hz
    have hzn : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    have hmem : awG z ∈ lowerHalf := aw_G_im_neg hzn
    have hgA : AnalyticAt ℂ awG z := by
      unfold awG
      exact (analyticAt_const.mul (analyticAt_id.add analyticAt_const)).div
        (analyticAt_id.sub analyticAt_const) hz1z
    have hgd : HasDerivAt awG (awGd z) z := aw_hasDerivAt_G hz1z
    have hgd' : deriv awG z ≠ 0 := by
      rw [hgd.deriv]
      unfold awGd
      exact div_ne_zero (by simp) (pow_ne_zero 2 hz1z)
    have hfA : AnalyticAt ℂ (⇑e) (awG z) := hHd.analyticOnNhd isOpen_lowerHalf _ hmem
    have hfd' : deriv (⇑e) (awG z) ≠ 0 := deriv_ne_zero_of_injOn isOpen_lowerHalf hHd e.injective.injOn hmem
    have hchain := eq19_1_chain_rule hgA hgd' hfA hfd'
    have hΦA : AnalyticAt ℂ (fun w => e (awG w)) z := hfA.comp hgA
    have hΦd : deriv (fun w => e (awG w)) z ≠ 0 := by
      have := deriv_comp z hfA.differentiableAt hgA.differentiableAt
      show deriv (⇑e ∘ awG) z ≠ 0
      rw [this]
      exact mul_ne_zero hfd' hgd'
    have hSG : schwarzian awG z = 0 := by
      have h0 := schwarzian_mobius (a := I) (b := I) (c := 1) (d := -1) aw_gS_det z
      have : awG = fun w => (I * w + I) / (1 * w + -1) := funext fun w => by unfold awG; ring
      rw [this]
      exact h0
    have hmob := schwarzian_mobius_comp_analytic hΦA hΦd hdet
    have hev : fB (Lambda φ) =ᶠ[𝓝 z] fun w => (a' * e (awG w) + b') / (c' * e (awG w) + d') := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      show finPart (wB (Lambda φ) (w : ExtPlane)) = _
      rw [hf w hw]
      exact hfform w hw
    have hMA : AnalyticAt ℂ (fun w => (a' * e (awG w) + b') / (c' * e (awG w) + d')) z :=
      ((analyticAt_const.mul hΦA).add analyticAt_const).div
        ((analyticAt_const.mul hΦA).add analyticAt_const) (hden z hz) |> fun h => h
    rw [schwarzianHol_congr hev, ← schwarzian_of_analyticAt hMA, hmob]
    have hchain' : schwarzian (fun w => e (awG w)) z =
        schwarzian (⇑e) (awG z) * deriv awG z ^ 2 + schwarzian awG z := hchain
    rw [hchain', hSG, add_zero, hHS _ hmem, hgd.deriv]
    unfold awPhi
    have h1 := aw_Q_G hz1z
    have h2 := aw_Qd_G hz1z
    rw [h1, mul_assoc, ← mul_pow, h2, one_pow, mul_one]
  rw [bers_Phi]
  apply AInf.ext_toFun_disc
  intro z hz
  rw [(bersPhi_spec hμball).1 z hz]
  exact hSch z hz

/-! ### Original relocated from `S1_1` (2026-10-25) -/

/-- (TT:504) **Ahlfors–Weill.** On the ball of radius `2` in `A∞(𝔻)`, `φ ↦ [Λ(φ)]` is a right inverse of `β`:
`Λ(φ) ∈ L∞(𝔻*)₁` and `β([Λ(φ)]) = φ`. -/
theorem ahlfors_weill {φ : AInf unitDisc} (hφ : ‖φ‖ < 2) :
    ∃ h : Lambda φ ∈ LinfStarBall, bers (Phi ⟨Lambda φ, h⟩) = φ :=
  ahlfors_weill_cand hφ

end TakhtajanTeo
