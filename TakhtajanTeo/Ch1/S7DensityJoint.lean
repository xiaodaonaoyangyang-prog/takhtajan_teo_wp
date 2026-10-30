import TakhtajanTeo.Ch1.S7DensityParameter

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem s7dj_spatial_dz {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ upperHalf k) (hs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) :
    ContDiffOn ℝ 2 (fun p : ℂ × ℂ => dz (wU (fun u => p.1*μ u)) p.2)
      ({ε : ℂ | ‖ε‖*k < 1} ×ˢ upperHalf) := by
  let W : ℂ × ℂ → ℂ := fun p => wU (fun u => p.1*μ u) p.2
  have hW := wr_joint_contDiff_U hk hμ hs
  have ho : IsOpen ({ε : ℂ | ‖ε‖*k < 1} ×ˢ upperHalf) :=
    (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).prod
      (isOpen_lt continuous_const Complex.continuous_im)
  have hD : ContDiffOn ℝ 2 (fderiv ℝ W) ({ε : ℂ | ‖ε‖*k < 1} ×ˢ upperHalf) :=
    hW.fderiv_of_isOpen ho (by norm_num)
  have hC : ContDiffOn ℝ 2 (fun p =>
      (fderiv ℝ W p (0,1)-I*fderiv ℝ W p (0,I))/2)
      ({ε : ℂ | ‖ε‖*k < 1} ×ˢ upperHalf) :=
    ((hD.clm_apply contDiffOn_const).sub
      (contDiffOn_const.mul (hD.clm_apply contDiffOn_const))).div_const 2
  apply hC.congr
  intro p hp
  have hd : DifferentiableAt ℝ W p :=
    (hW.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds hp)
  change (fderiv ℝ (fun z => W (p.1,z)) p.2 1-I*fderiv ℝ (fun z => W (p.1,z)) p.2 I)/2 = _
  rw [l613_fderiv_right hd,l613_fderiv_right hd]

/-- Joint real C2 regularity of the actual pulled-back density on the full
admissible parameter strip and the upper half-plane. -/
theorem s7dj_density {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ upperHalf k) (hs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) :
    ContDiffOn ℝ 2 (fun p : ℂ × ℂ => rhoVar μ p.1 p.2)
      ({ε : ℂ | ‖ε‖*k < 1} ×ˢ upperHalf) := by
  have hW : ContDiffOn ℝ 2 (fun p : ℂ × ℂ => wU (fun u => p.1*μ u) p.2)
      ({ε : ℂ | ‖ε‖*k < 1} ×ˢ upperHalf) :=
    (wr_joint_contDiff_U hk hμ hs).of_le (by norm_num)
  have hD := s7dj_spatial_dz hk hμ hs
  have hN := ((contDiffOn_const (c := (-4:ℂ))).mul hD).mul
    (Complex.conjCLE.contDiff.comp_contDiffOn hD)
  have hB := (hW.sub (Complex.conjCLE.contDiff.comp_contDiffOn hW)).pow 2
  have hden : ∀ p ∈ ({ε : ℂ | ‖ε‖*k < 1} ×ˢ upperHalf),
      (wU (fun u => p.1*μ u) p.2-conj (wU (fun u => p.1*μ u) p.2))^2 ≠ 0 := by
    intro p hp
    apply pow_ne_zero 2
    have he : IsBeltramiCoeff (fun u => p.1*μ u) upperHalf (‖p.1‖*k) :=
      ⟨hμ.1.const_mul p.1,hμ.2.mono (fun u hu => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left hu (norm_nonneg _))⟩
    have hi : wU (fun u => p.1*μ u) '' upperHalf = upperHalf := by
      rw [e124_wU_eq_fMuSym hk hμ hp.1]
      exact (fMuSym_upperHalf (by positivity) hp.1 he).1
    have hz : wU (fun u => p.1*μ u) p.2 ∈ upperHalf := by
      rw [← hi]
      exact mem_image_of_mem _ hp.2
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.sub_im,Complex.conj_im,Complex.zero_im] at him
    change 0 < (wU (fun u => p.1*μ u) p.2).im at hz
    linarith
  have hc := hN.mul (hB.inv hden)
  apply hc.congr
  intro p hp
  change -4*((‖dz (wU (fun u => p.1*μ u)) p.2‖^2:ℝ):ℂ)/_ = _
  rw [← Complex.normSq_eq_norm_sq,← Complex.mul_conj,div_eq_mul_inv]
  simp only [Function.comp_apply,Complex.conjCLE_apply,Pi.inv_apply]
  ring

theorem s7dj_ratio {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ upperHalf k) (hs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) :
    ContDiffOn ℝ 2 (fun p : ℂ × ℂ => rhoVar μ p.1 p.2/(rhoU p.2:ℂ))
      ({ε : ℂ | ‖ε‖*k < 1} ×ˢ upperHalf) := by
  have hr : ContDiff ℝ 2 (fun p : ℂ × ℂ => ((p.2.im^2:ℝ):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((Complex.imCLM.contDiff.comp contDiff_snd).pow 2)
  have he (z : ℂ) : (rhoU z:ℂ)⁻¹ = ((z.im^2:ℝ):ℂ) := by
    simp [rhoU,Complex.ofReal_inv]
  simpa only [div_eq_mul_inv,he] using (s7dj_density hk hμ hs).mul hr.contDiffOn

end TakhtajanTeo
