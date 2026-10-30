import TakhtajanTeo.Ch1.HilbertChosenReflection
import TakhtajanTeo.Ch1.Eq22ReproducingFinal
import TakhtajanTeo.Ch1.Eq22BoundaryDomain
import TakhtajanTeo.Ch1.Remark24Completed
import TakhtajanTeo.Ch1.HilbertBersDifferential
import TakhtajanTeo.Ch1.HilbertBersPreimage
import TakhtajanTeo.Ch1.HilbertBersPreimageAssembly
import TakhtajanTeo.Ch1.BersOpenEmbedding
import TakhtajanTeo.Ch1.BeltramiTranslation
import TakhtajanTeo.Ch1.QCVariationSurjSmall
import TakhtajanTeo.Ch1.QCVariationTransportCriteria
import TakhtajanTeo.Ch1.BanachReproducing

/-!
# `Φ` is a holomorphic submersion at every base (prefix `bsub_`)

Route.
* (A) Surjectivity of `D₀(l ↦ βΦ(l * μ))` on `A∞`, at every `μ`. This is GPT's Hilbert section with `A₂` replaced by
  the weighted sup bound:
  - the chosen reflection `hc6_chosen_raw_coefficient` bounds the reflected coefficient by `M C / 2`;
  - the Bers reproducing formula for weighted-sup `q` (`bsub_reproducing`, `Ch1/BanachReproducing`, 下属5) follows from `eq22_reproducing` for the dilates
    `q_r = (r² P(r·) ∘ F) F'²` (which lie in `A₂(Ω)`), by dominated convergence `r → 1` with dominant
    `M C / |u - z|⁴` on `Ω*`;
  - finally `r24_phi_formula` and `hb_fourth_kernel_transport`.
* (B) `G_μ(χ) = βΦ(Λχ * μ)` is injective on `ball 0 2`, since `βΦ` is a class function, right translation cancels
  and Ahlfors–Weill holds. By Lyusternik's tangent argument (`surjOn_closedBall_of_nonlinearRightInverse`), its
  derivative at `0`, which is onto by (A), is injective. This gives (★).
* (C) The four originals: `ker_DmuPhi`, `phi_submersion`, `bers_isOpenEmbedding`, `rightTrans_biholomorphic`. For
  the last one, `β R_μ β⁻¹ = G_{ν*μ} ∘ G_ν⁻¹` near `β[ν]`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## (A) Surjectivity at every base -/

/-- An `A∞(𝔻)` differential transported to `Ω = 𝖿(𝔻)` satisfies the weighted sup bound `|q| ≤ (‖φ‖/4) λ_Ω²`. -/
theorem bsub_transport_weighted {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (φ : AInf unitDisc) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q (fsans μ '' unitDisc) ∧
      (∀ w ∈ unitDisc, q (fsans μ w) * deriv (fsans μ) w ^ 2 = AInf.toFun φ w) ∧
      ∀ v ∈ fsans μ '' unitDisc, ‖q v‖ ≤ (‖φ‖ / 4) * poincareDensity (fsans μ '' unitDisc) v ^ 2 := by
  have hf := S2C.s2c_conf_f hμ
  have hΩ : IsOpen (fsans μ '' unitDisc) := hf.isOpen isOpen_ball
  have hF : IsConformalOnto (Function.invFunOn (fsans μ) unitDisc) (fsans μ '' unitDisc) unitDisc :=
    hf.symm isOpen_ball
  have hφd : DifferentiableOn ℂ (AInf.toFun φ) unitDisc := φ.2
  let q : ℂ → ℂ := fun v => AInf.toFun φ (Function.invFunOn (fsans μ) unitDisc v) *
    deriv (Function.invFunOn (fsans μ) unitDisc) v ^ 2
  have hq : DifferentiableOn ℂ q (fsans μ '' unitDisc) :=
    (hφd.comp hF.1 hF.mapsTo).mul ((hF.1.deriv hΩ).pow 2)
  have he : ∀ w ∈ unitDisc, q (fsans μ w) * deriv (fsans μ) w ^ 2 = AInf.toFun φ w := by
    intro w hw
    have hi := t1_deriv_invFunOn_mul isOpen_ball hf hw
    change deriv (Function.invFunOn (fsans μ) unitDisc) (fsans μ w) * deriv (fsans μ) w = 1 at hi
    dsimp only [q]
    rw [hf.2.1.leftInvOn_invFunOn hw]
    calc AInf.toFun φ w * deriv (Function.invFunOn (fsans μ) unitDisc) (fsans μ w) ^ 2 *
          deriv (fsans μ) w ^ 2 =
        AInf.toFun φ w * (deriv (Function.invFunOn (fsans μ) unitDisc) (fsans μ w) *
          deriv (fsans μ) w) ^ 2 := by ring
      _ = AInf.toFun φ w := by rw [hi]; ring
  refine ⟨q, hq, he, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have hd : deriv (fsans μ) w ≠ 0 := kb_deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hw
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hw2 : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hqw : q (fsans μ w) = AInf.toFun φ w / deriv (fsans μ) w ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hd)]
    exact he w hw
  have hP : ‖AInf.toFun φ w‖ ≤ ‖φ‖ / (1 - ‖w‖ ^ 2) ^ 2 := by
    show ‖unweight unitDisc φ.1 w‖ ≤ _
    simp only [unweight, hw, ↓reduceDIte, norm_div]
    have hden : ‖((1 : ℂ) - (‖w‖ : ℂ) ^ 2) ^ 2‖ = (1 - ‖w‖ ^ 2) ^ 2 := by
      have hc : ((1 : ℂ) - (‖w‖ : ℂ) ^ 2) ^ 2 = (((1 - ‖w‖ ^ 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_of_nonneg (by positivity)]
    rw [hden]
    exact div_le_div_of_nonneg_right (φ.1.norm_coe_le_norm _) (by positivity)
  rw [hqw, eq22_density_formula hf hw, norm_div, norm_pow]
  have hdn : 0 < ‖deriv (fsans μ) w‖ := norm_pos_iff.mpr hd
  calc ‖AInf.toFun φ w‖ / ‖deriv (fsans μ) w‖ ^ 2 ≤
        (‖φ‖ / (1 - ‖w‖ ^ 2) ^ 2) / ‖deriv (fsans μ) w‖ ^ 2 :=
        div_le_div_of_nonneg_right hP (by positivity)
    _ = ‖φ‖ / 4 * (2 / ((1 - ‖w‖ ^ 2) * ‖deriv (fsans μ) w‖)) ^ 2 := by
        generalize 1 - ‖w‖ ^ 2 = A
        ring

/-- **Surjectivity at every base**: `D₀(l ↦ βΦ(l * μ)) : L∞(𝔻*) → A∞(𝔻)` is onto. -/
theorem bsub_translated_surjective {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Function.Surjective (QCV.qcv_translatedBersDerivative μ) := by
  intro φ
  obtain ⟨q, hq, hqe, hqb⟩ := bsub_transport_weighted hμ φ
  obtain ⟨h, C0, hC0, hh, hC1, hbounded⟩ := hc6_chosen_raw_coefficient hμ
  have hM : 0 ≤ ‖φ‖ / 4 := by positivity
  have hrepro : ∀ z ∈ fsans μ '' unitDisc, q z = -(3 / π) * ∫ u in gsans μ '' unitDiscExterior,
      q (h u) * (u - h u) ^ 2 * dzbar h u / (u - z) ^ 4 :=
    fun z hz => bsub_reproducing hμ hh hbounded hq hM hqb hz
  obtain ⟨-, hbnd⟩ := hbounded q _ hM hq hqb
  have hg := S2C.s2c_conf_g hμ
  have hE := hg.isOpen resolvent_exterior_isOpen
  have hbc : ContinuousOn (hbPre_reflected q h) (gsans μ '' unitDiscExterior) := by
    unfold hbPre_reflected
    exact ((continuousOn_const.mul (hq.continuousOn.comp hC1.continuousOn hh.2.1)).mul
      ((continuousOn_id.sub hC1.continuousOn).pow 2)).mul
      (continuousOn_dz_dzbar hC1 hE).2
  have hdne : ∀ w ∈ unitDiscExterior, deriv (gsans μ) w ≠ 0 :=
    fun w hw => deriv_ne_zero_of_injOn resolvent_exterior_isOpen hg.1 hg.2.1 hw
  have hdc := (hg.1.deriv resolvent_exterior_isOpen).continuousOn
  have hac : ContinuousOn (hbPre_pullback (hbPre_reflected q h) (gsans μ)) unitDiscExterior :=
    (hbc.comp hg.1.continuousOn hg.mapsTo).mul
      ((continuous_conj.comp_continuousOn hdc).div hdc hdne)
  have hamem : MemLp (hbPre_pullback (hbPre_reflected q h) (gsans μ)) ∞
      (volume.restrict unitDiscExterior) := by
    apply memLp_top_of_bound (hac.aestronglyMeasurable resolvent_exterior_isOpen.measurableSet)
      (‖φ‖ / 4 * C0 / 2)
    filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with w hw
    rw [hbPre_pullback_norm (hdne w hw)]
    exact hbnd _ (hg.mapsTo hw)
  let a := toLinf (hbPre_pullback (hbPre_reflected q h) (gsans μ))
  have ha := bc_toLinf_ae hamem
  refine ⟨a, ?_⟩
  apply AInf.ext_toFun_disc
  intro ζ hζ
  change AInf.toFun (D0BersR μ a) ζ = AInf.toFun φ ζ
  rw [← hqe ζ hζ, r24_phi_formula hμ _ hζ, hb_fourth_kernel_transport resolvent_exterior_isOpen hg]
  have haint : (∫ w in unitDiscExterior, a w * deriv (gsans μ) w ^ 2 / (gsans μ w - fsans μ ζ) ^ 4) =
      ∫ w in unitDiscExterior, hbPre_pullback (hbPre_reflected q h) (gsans μ) w *
        deriv (gsans μ) w ^ 2 / (gsans μ w - fsans μ ζ) ^ 4 := by
    apply integral_congr_ae
    filter_upwards [ha] with w hw
    rw [hw]
  rw [haint, hbPre_pullback_integral resolvent_exterior_isOpen hg]
  have hi : (∫ u in gsans μ '' unitDiscExterior, hbPre_reflected q h u / (u - fsans μ ζ) ^ 4) =
      (1 / 2 : ℂ) * ∫ u in gsans μ '' unitDiscExterior,
        q (h u) * (u - h u) ^ 2 * dzbar h u / (u - fsans μ ζ) ^ 4 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hE.measurableSet
    intro u _
    dsimp [hbPre_reflected]
    ring
  rw [hi, hrepro _ ⟨ζ, hζ, rfl⟩]
  ring

/-! ## (B) The derivative of `G_μ(χ) = βΦ(Λχ * μ)` at `0` is bijective -/

/-- `G_μ` is holomorphic on `ball 0 2` (so strictly differentiable there). -/
theorem bsub_G_differentiableOn {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    DifferentiableOn ℂ (fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ) μ)) (ball 0 2) := by
  have h1 : MapsTo Lambda (ball (0 : AInf unitDisc) 2) LinfStarBall :=
    fun χ hχ => Lambda_mem_ball (mem_ball_zero_iff.mp hχ)
  have h2 : MapsTo (fun l => beltramiMul l μ) LinfStarBall LinfStarBall :=
    fun l hl => bg_mul_mem_ball hμ hl
  exact (QCV.qcv_bersPhi_differentiableOn.comp (bd_differentiableOn hμ) h2).comp
    Lambda_differentiable.differentiableOn h1

/-- `G_μ` is injective on `ball 0 2`. -/
theorem bsub_G_injOn {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    InjOn (fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ) μ)) (ball 0 2) := by
  intro χ hχ χ' hχ' he
  obtain ⟨-, -, hμi, -, -⟩ := bc_wA_mul hμ hμ
  obtain ⟨hΛ, hb⟩ := QCV.qs_AW (mem_ball_zero_iff.mp hχ)
  obtain ⟨hΛ', hb'⟩ := QCV.qs_AW (mem_ball_zero_iff.mp hχ')
  have h1 := QCV.qs_bersPhi_mul_congr (bg_mul_mem_ball hμ hΛ) (bg_mul_mem_ball hμ hΛ') hμi he
  rw [QCV.qs_bersPhi_mul_inv hΛ hμ, QCV.qs_bersPhi_mul_inv hΛ' hμ] at h1
  rw [← hb, ← hb', h1]

/-- Near `0`, `βΦ(l * μ) = G_μ(βΦ l)`; hence `D₀(l ↦ βΦ(l * μ)) = D₀G_μ ∘ D₀βΦ`. -/
theorem bsub_translated_eq_comp {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    QCV.qcv_translatedBersDerivative μ =
      (fderiv ℂ (fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ) μ)) 0).comp (fderiv ℂ bersPhi 0) := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := by simp [LinfStarBall]
  have hbd : DifferentiableAt ℂ bersPhi 0 :=
    QCV.qcv_bersPhi_differentiableOn.differentiableAt (isOpen_ball.mem_nhds h0)
  have hGd : DifferentiableAt ℂ (fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ) μ)) (bersPhi 0) := by
    rw [QCV.qs_bersPhi_zero]
    exact (bsub_G_differentiableOn hμ).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num)))
  have hev : (fun l => bersPhi (beltramiMul l μ)) =ᶠ[𝓝 0]
      ((fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ) μ)) ∘ bersPhi) := by
    have h1 : ∀ᶠ l in 𝓝 (0 : LinfStar), l ∈ LinfStarBall := isOpen_ball.mem_nhds h0
    have h2 : ∀ᶠ l in 𝓝 (0 : LinfStar), bersPhi l ∈ ball (0 : AInf unitDisc) 2 :=
      hbd.continuousAt (by rw [QCV.qs_bersPhi_zero]; exact ball_mem_nhds _ (by norm_num))
    filter_upwards [h1, h2] with l hl hl2
    obtain ⟨hΛ, hb⟩ := QCV.qs_AW (mem_ball_zero_iff.mp hl2)
    exact (QCV.qs_bersPhi_mul_congr hΛ hl hμ hb).symm
  change fderiv ℂ (fun l => bersPhi (beltramiMul l μ)) 0 = _
  rw [hev.fderiv_eq, fderiv_comp 0 hGd hbd, QCV.qs_bersPhi_zero]

/-- Lyusternik's tangent argument: a strictly differentiable map that is injective near `a` and has a surjective
derivative at `a` has an injective derivative there. -/
theorem bsub_injective_of_surjective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {f : E → F} {f' : E →L[ℂ] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hs : Function.Surjective f') {s : Set E} (hsa : s ∈ 𝓝 a)
    (hinj : InjOn f s) : Function.Injective f' := by
  obtain ⟨R, hR⟩ := ContinuousLinearMap.exists_nonlinearRightInverse_of_surjective f'
    (LinearMap.range_eq_top.mpr hs)
  have hc : (0 : ℝ≥0) < R.nnnorm⁻¹ / 3 := by positivity
  obtain ⟨t, ht, hA⟩ := hf.approximates_deriv_on_nhds (Or.inr hc)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hsa ht)
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hv0
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set b : E := a + ((ρ / (4 * ‖v‖) : ℝ) : ℂ) • v with hb
  have hba : ‖b - a‖ = ρ / 4 := by
    rw [hb, add_sub_cancel_left, norm_smul, Complex.norm_of_nonneg (by positivity)]
    field_simp
  have hbmem : b ∈ ball a ρ := by
    rw [mem_ball, dist_eq_norm, hba]
    linarith
  have ham : a ∈ ball a ρ := mem_ball_self hρ
  have hN : (0 : ℝ) < (R.nnnorm : ℝ)⁻¹ := by
    have : (0 : ℝ) < R.nnnorm := by exact_mod_cast hR
    positivity
  have hcR : ((R.nnnorm⁻¹ / 3 : ℝ≥0) : ℝ) = (R.nnnorm : ℝ)⁻¹ / 3 := by push_cast; ring
  have hden : 0 < (R.nnnorm : ℝ)⁻¹ - ((R.nnnorm⁻¹ / 3 : ℝ≥0) : ℝ) := by rw [hcR]; linarith
  have hfb : ‖f b - f a‖ ≤ (R.nnnorm : ℝ)⁻¹ / 3 * (ρ / 4) := by
    have h := hA _ (hball hbmem).2 _ (hball ham).2
    have hz : f' (b - a) = 0 := by
      rw [hb, add_sub_cancel_left, map_smul, hv, smul_zero]
    rw [hz, sub_zero, hba, hcR] at h
    exact h
  set ε : ℝ := ‖f b - f a‖ / ((R.nnnorm : ℝ)⁻¹ - ((R.nnnorm⁻¹ / 3 : ℝ≥0) : ℝ)) with hε
  have hε0 : 0 ≤ ε := div_nonneg (norm_nonneg _) hden.le
  have hεle : ε ≤ ρ / 8 := by
    rw [hε, div_le_iff₀ hden, hcR]
    nlinarith
  have hsub : closedBall b ε ⊆ t := by
    intro y hy
    apply (hball _).2
    rw [mem_ball]
    have h1 := mem_closedBall.mp hy
    have h2 : dist b a = ρ / 4 := by rw [dist_eq_norm, hba]
    linarith [dist_triangle y b a]
  have hsurj := hA.surjOn_closedBall_of_nonlinearRightInverse R hε0 hsub
  have hfa : f a ∈ closedBall (f b) (((R.nnnorm : ℝ)⁻¹ - ((R.nnnorm⁻¹ / 3 : ℝ≥0) : ℝ)) * ε) := by
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev, hε, mul_div_cancel₀ _ hden.ne']
  obtain ⟨y, hy, hfy⟩ := hsurj hfa
  have hys : y ∈ s := by
    apply (hball _).1
    rw [mem_ball]
    have h1 := mem_closedBall.mp hy
    have h2 : dist b a = ρ / 4 := by rw [dist_eq_norm, hba]
    linarith [dist_triangle y b a]
  have hya : y = a := hinj hys (hball ham).1 hfy
  rw [hya, mem_closedBall, dist_eq_norm, norm_sub_rev, hba] at hy
  linarith

/-- **(★)** For every `μ ∈ L∞(𝔻*)₁`, `D₀G_μ : A∞(𝔻) → A∞(𝔻)` is bijective (so a `ContinuousLinearEquiv`,
`ContinuousLinearEquiv.ofBijective`). -/
theorem bsub_star {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Function.Bijective (fderiv ℂ (fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ) μ)) 0) := by
  have : CompleteSpace (AInf unitDisc) := AInf_completeSpace_disc
  have hsurj : Function.Surjective
      (fderiv ℂ (fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ) μ)) 0) := by
    intro φ
    obtain ⟨ν, hν⟩ := bsub_translated_surjective hμ φ
    rw [bsub_translated_eq_comp hμ] at hν
    exact ⟨_, hν⟩
  have h0 : (0 : AInf unitDisc) ∈ ball (0 : AInf unitDisc) 2 := mem_ball_self (by norm_num)
  have hstrict := bh_hasStrictFDerivAt isOpen_ball (bsub_G_differentiableOn hμ) h0
  exact ⟨bsub_injective_of_surjective hstrict hsurj (isOpen_ball.mem_nhds h0) (bsub_G_injOn hμ), hsurj⟩

/-! ## (C) Consumers -/

/-- The kernel of the translated derivative is `𝓝(𝔻*)` at every base. -/
theorem bsub_ker_translated {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    (QCV.qcv_translatedBersDerivative μ).ker = trivialBeltrami := by
  rw [← QCV.qcv_ker_D0Phi]
  ext ν
  change QCV.qcv_translatedBersDerivative μ ν = 0 ↔ fderiv ℂ bersPhi 0 ν = 0
  rw [bsub_translated_eq_comp hμ, ContinuousLinearMap.comp_apply]
  constructor
  · intro h
    apply (bsub_star hμ).1
    rw [h, map_zero]
  · intro h
    rw [h, map_zero]

/-- The frozen statement of `ker_DmuPhi` (TT:466–471). -/
theorem bsub_ker_DmuPhi {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    LinearMap.ker (fderiv ℂ bersPhi μ : LinfStar →ₗ[ℂ] AInf unitDisc) =
      Submodule.map (fderiv ℂ (fun l => beltramiMul l μ) 0 : LinfStar →ₗ[ℂ] LinfStar) trivialBeltrami := by
  exact (QCV.qcv_ker_DmuPhi_iff hμ).mpr (bsub_ker_translated hμ)

/-- The frozen statement of `phi_submersion` (TT:366). -/
theorem bsub_phi_submersion {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    LinearMap.range (fderiv ℂ bersPhi μ : LinfStar →ₗ[ℂ] AInf unitDisc) = ⊤ ∧
      ∃ C : Submodule ℂ LinfStar, IsClosed (C : Set LinfStar) ∧ IsCompl (LinearMap.ker (fderiv ℂ bersPhi μ : LinfStar →ₗ[ℂ] AInf unitDisc)) C := by
  refine ⟨LinearMap.range_eq_top.mpr ((QCV.qcv_bers_surjective_iff hμ).mpr (bsub_translated_surjective hμ)),
    QCV.qcv_transportedHarmonic μ, QCV.qcv_transportedHarmonic_isClosed hμ, ?_⟩
  rw [bsub_ker_DmuPhi hμ]
  exact QCV.qcv_transported_isCompl hμ

/-- The frozen statement of `bers_isOpenEmbedding` (TT:492, TT:512). -/
theorem bsub_bers_isOpenEmbedding : Topology.IsOpenEmbedding bers := by
  exact bers_isOpenEmbedding_of_submersion fun μ hμ => (bsub_phi_submersion hμ).1

/-- `βΦ((a * b) * c) = βΦ(a * (b * c))`. -/
theorem bsub_bersPhi_assoc {a b c : LinfStar} (ha : a ∈ LinfStarBall) (hb : b ∈ LinfStarBall)
    (hc : c ∈ LinfStarBall) :
    bersPhi (beltramiMul (beltramiMul a b) c) = bersPhi (beltramiMul a (beltramiMul b c)) := by
  obtain ⟨hab, hS1, -⟩ := bc_wA_mul hb ha
  obtain ⟨habc, hS2, -⟩ := bc_wA_mul hc hab
  obtain ⟨hbc, hS3, -⟩ := bc_wA_mul hc hb
  obtain ⟨habc', hS4, -⟩ := bc_wA_mul hbc ha
  have hS : wAS (beltramiMul (beltramiMul a b) c) = wAS (beltramiMul a (beltramiMul b c)) := by
    rw [hS2, hS1, hS4, hS3]
    rfl
  have hP : Phi ⟨beltramiMul (beltramiMul a b) c, habc⟩ = Phi ⟨beltramiMul a (beltramiMul b c), habc'⟩ := by
    apply Quotient.sound
    intro z _
    simp only [wA, hS]
  have := congrArg bers hP
  rw [bers_Phi, bers_Phi] at this
  exact this

/-- A holomorphic local inverse of `G_ν` at `β[ν] = G_ν(0)`. -/
theorem bsub_G_local_inverse {ν : LinfStar} (hν : ν ∈ LinfStarBall) :
    ∃ L : AInf unitDisc → AInf unitDisc, DifferentiableAt ℂ L (bersPhi ν) ∧ L (bersPhi ν) = 0 ∧
      ∀ᶠ χ in 𝓝 (bersPhi ν), L χ ∈ ball (0 : AInf unitDisc) 2 ∧
        bersPhi (beltramiMul (Lambda (L χ)) ν) = χ := by
  have : CompleteSpace (AInf unitDisc) := AInf_completeSpace_disc
  have hb := bsub_star hν
  have h0 : (0 : AInf unitDisc) ∈ ball (0 : AInf unitDisc) 2 := mem_ball_self (by norm_num)
  have hstrict := bh_hasStrictFDerivAt isOpen_ball (bsub_G_differentiableOn hν) h0
  obtain ⟨e, he⟩ : ∃ e : AInf unitDisc ≃L[ℂ] AInf unitDisc, (e : AInf unitDisc →L[ℂ] AInf unitDisc) =
      fderiv ℂ (fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ) ν)) 0 :=
    ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2),
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  have hs : HasStrictFDerivAt (fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ) ν))
      (e : AInf unitDisc →L[ℂ] AInf unitDisc) 0 := by
    rw [he]
    exact hstrict
  have hΛ0 : Lambda (0 : AInf unitDisc) = 0 := by
    simpa using Lambda_smul (0 : ℂ) (0 : AInf unitDisc)
  have hG0 : (fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ) ν)) 0 = bersPhi ν := by
    show bersPhi (beltramiMul (Lambda 0) ν) = bersPhi ν
    rw [hΛ0, QCV.qcv_beltramiMul_zero hν]
  refine ⟨hs.localInverse _ e 0, ?_, ?_, ?_⟩
  · rw [← hG0]
    exact hs.to_localInverse.differentiableAt
  · rw [← hG0]
    exact hs.localInverse_apply_image
  · rw [← hG0]
    have hc := hs.localInverse_continuousAt
    have hball : ∀ᶠ χ in 𝓝 ((fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ) ν)) 0),
        hs.localInverse _ e 0 χ ∈ ball (0 : AInf unitDisc) 2 :=
      hc (by rw [hs.localInverse_apply_image]; exact ball_mem_nhds _ (by norm_num))
    filter_upwards [hball, hs.eventually_right_inverse] with χ h1 h2
    exact ⟨h1, h2⟩

/-- `β ∘ R_[μ] ∘ β⁻¹` is holomorphic on `β(T(1))`. -/
theorem bsub_rightTrans_differentiableOn (μ : LinfStarBall) :
    DifferentiableOn ℂ (bers ∘ rightTrans μ ∘ Function.invFunOn bers univ) (range bers) := by
  intro χ0 hχ0
  obtain ⟨p0, rfl⟩ := hχ0
  obtain ⟨ν, rfl⟩ := Quotient.exists_rep p0
  have hbp0 : bers ⟦ν⟧ = bersPhi (ν : LinfStar) := bers_Phi ν
  obtain ⟨L, hLd, hL0, hLev⟩ := bsub_G_local_inverse ν.2
  have hm : beltramiMul (ν : LinfStar) μ ∈ LinfStarBall := bg_mul_mem_ball μ.2 ν.2
  have hGd : DifferentiableAt ℂ (fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ)
      (beltramiMul (ν : LinfStar) μ))) (L (bersPhi (ν : LinfStar))) := by
    rw [hL0]
    exact (bsub_G_differentiableOn hm).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num)))
  have hHd := hGd.comp (bersPhi (ν : LinfStar)) hLd
  have hev : ∀ᶠ χ in 𝓝 (bersPhi (ν : LinfStar)), χ ∈ range bers →
      (bers ∘ rightTrans μ ∘ Function.invFunOn bers univ) χ =
        ((fun χ : AInf unitDisc => bersPhi (beltramiMul (Lambda χ) (beltramiMul (ν : LinfStar) μ))) ∘ L) χ := by
    filter_upwards [hLev] with χ hχL hχ
    obtain ⟨hLb, hLχ⟩ := hχL
    have hex : ∃ x ∈ (univ : Set T1), bers x = χ := by
      obtain ⟨x, hx⟩ := hχ
      exact ⟨x, trivial, hx⟩
    obtain ⟨p, hpdef⟩ : ∃ p : T1, p = Function.invFunOn bers univ χ := ⟨_, rfl⟩
    have hp : bers p = χ := by rw [hpdef]; exact Function.invFunOn_eq hex
    have hΛ : Lambda (L χ) ∈ LinfStarBall := Lambda_mem_ball (mem_ball_zero_iff.mp hLb)
    have e1 : bers p = bersPhi ((Quotient.out (s := teichSetoid) p : LinfStarBall) : LinfStar) := by
      conv_lhs => rw [← Quotient.out_eq p]
      exact bers_Phi _
    have e2 : rightTrans μ p =
        Phi ⟨beltramiMul ((Quotient.out (s := teichSetoid) p : LinfStarBall) : LinfStar) μ, bg_mul_mem_ball μ.2 (Quotient.out (s := teichSetoid) p).2⟩ := by
      conv_lhs => rw [← Quotient.out_eq p]
      exact bt_rightTrans_phi μ _
    show bers (rightTrans μ (Function.invFunOn bers univ χ)) = _
    rw [← hpdef, e2, bers_Phi]
    calc bersPhi (beltramiMul ((Quotient.out (s := teichSetoid) p : LinfStarBall) : LinfStar) μ) =
          bersPhi (beltramiMul (beltramiMul (Lambda (L χ)) ν) μ) :=
          QCV.qs_bersPhi_mul_congr (Quotient.out (s := teichSetoid) p).2
            (bg_mul_mem_ball ν.2 hΛ) μ.2 (e1.symm.trans (hp.trans hLχ.symm))
      _ = _ := bsub_bersPhi_assoc hΛ ν.2 μ.2
  rw [hbp0]
  exact hHd.differentiableWithinAt.congr_of_eventuallyEq_of_mem
    (eventually_nhdsWithin_iff.mpr hev) ⟨⟦ν⟧, hbp0⟩

/-- The frozen statement of `rightTrans_biholomorphic` (TT:464). -/
theorem bsub_rightTrans_biholomorphic (μ : LinfStarBall) :
    Function.Bijective (rightTrans μ) ∧
      DifferentiableOn ℂ (bers ∘ rightTrans μ ∘ Function.invFunOn bers univ) (range bers) ∧
      ∃ h : beltramiInv μ ∈ LinfStarBall,
        DifferentiableOn ℂ (bers ∘ rightTrans ⟨_, h⟩ ∘ Function.invFunOn bers univ) (range bers) ∧
        rightTrans ⟨_, h⟩ ∘ rightTrans μ = id := by
  obtain ⟨hbij, h, hcomp⟩ := bt_rightTrans_bijective μ
  exact ⟨hbij, bsub_rightTrans_differentiableOn μ, h, bsub_rightTrans_differentiableOn ⟨_, h⟩, hcomp⟩

/-- (TT:492, TT:512) `β` is injective, and a homeomorphism of `T(1)` onto an open subset of `A∞(𝔻)`. This is the
statement that the Bers coordinates are global coordinates of the complex Banach manifold `T(1)`. -/
theorem bers_isOpenEmbedding : Topology.IsOpenEmbedding bers :=
  bsub_bers_isOpenEmbedding

/-- (TT:366) `Φ` is a holomorphic submersion: at every `μ ∈ L∞(𝔻*)₁` the differential of `β ∘ Φ` is a surjection
whose kernel has a closed complement. -/
theorem phi_submersion {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    LinearMap.range (fderiv ℂ bersPhi μ : LinfStar →ₗ[ℂ] AInf unitDisc) = ⊤ ∧
      ∃ C : Submodule ℂ LinfStar, IsClosed (C : Set LinfStar) ∧ IsCompl (LinearMap.ker (fderiv ℂ bersPhi μ : LinfStar →ₗ[ℂ] AInf unitDisc)) C :=
  bsub_phi_submersion hμ

/-- (TT:466–471) For `μ ∈ L∞(𝔻*)₁` the kernel of `D_μΦ` is `D₀R_μ(𝓝(𝔻*))`, where `R_μ(λ) = λ * μ` on
`L∞(𝔻*)`. -/
theorem ker_DmuPhi {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    LinearMap.ker (fderiv ℂ bersPhi μ : LinfStar →ₗ[ℂ] AInf unitDisc) =
      Submodule.map (fderiv ℂ (fun l => beltramiMul l μ) 0 : LinfStar →ₗ[ℂ] LinfStar) trivialBeltrami :=
  bsub_ker_DmuPhi hμ

/-- (TT:464) Right translations are biholomorphic automorphisms of `T(1)`: bijective, and holomorphic in Bers
coordinates. The coordinate expression `β ∘ R_[μ] ∘ β⁻¹` is holomorphic on the open set `β(T(1))`, and so is that of
the inverse `R_[μ⁻¹]`. -/
theorem rightTrans_biholomorphic (μ : LinfStarBall) :
    Function.Bijective (rightTrans μ) ∧
      DifferentiableOn ℂ (bers ∘ rightTrans μ ∘ Function.invFunOn bers univ) (range bers) ∧
      ∃ h : beltramiInv μ ∈ LinfStarBall,
        DifferentiableOn ℂ (bers ∘ rightTrans ⟨_, h⟩ ∘ Function.invFunOn bers univ) (range bers) ∧
        rightTrans ⟨_, h⟩ ∘ rightTrans μ = id :=
  bsub_rightTrans_biholomorphic μ

end TakhtajanTeo
