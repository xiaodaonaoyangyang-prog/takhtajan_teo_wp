import TakhtajanTeo.Ch2.S1_SymmetricLift
import TakhtajanTeo.Ch2.S1_BP16Completed

/-! # Actual asymptotically conformal welding extensions -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- Reflection of a differentiable punctured disk map preserves the norm of its dilatation pointwise. -/
theorem symt_reflection_dilatation {G : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hG : G (conj z)⁻¹ ≠ 0) (hd : DifferentiableAt ℝ G (conj z)⁻¹) :
    ‖complexDilatation (fun w => (conj (G (conj w)⁻¹))⁻¹) z‖ =
      ‖complexDilatation G (conj z)⁻¹‖ := by
  have hd' : DifferentiableAt ℝ G (conj z⁻¹) := by simpa only [map_inv₀] using hd
  obtain ⟨hgd, hdz, hdzbar⟩ := abR_x_dz_dzbar_conj hd'
  have hne : conj (G (conj z⁻¹)) ≠ 0 := by simpa only [map_ne_zero, map_inv₀] using hG
  have he : (fun w => (conj (G (conj w)⁻¹))⁻¹) = nxInvConj (fun w => conj (G (conj w))) := by
    funext w
    simp only [nxInvConj, map_inv₀]
  rw [he, nxI2_dilatation_invConj_at hz hne hgd, norm_mul]
  have hn : ‖z^2 / conj z^2‖ = 1 := by
    rw [norm_div, norm_pow, norm_pow, Complex.norm_conj]
    exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
  rw [hn, mul_one, complexDilatation, complexDilatation, hdz, hdzbar,
    norm_div, norm_div, Complex.norm_conj, Complex.norm_conj, map_inv₀]

/-- A symmetric QS boundary map admits a plane QC extension whose exterior
dilatation tends pointwise to zero at the circle. -/
theorem symt_plane_extension {h : ℂ → ℂ} (hq : IsQSCircleHomeo h) (hs : IsSymmetricHomeo h) :
    ∃ H : ℂ → ℂ, IsQuasiconformal H univ ∧ H '' univ = univ ∧
      H '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 ∧ EqOn H h unitCircle ∧
      Tendsto (complexDilatation H) (comap (fun z : ℂ => ‖z‖) (𝓝[>] 1)) (𝓝 0) := by
  obtain ⟨G, hc, hi, himg, h0, hb, ⟨K,hK⟩, hd, hdec⟩ := symt_disk_extension hq hs
  have hunit : unitCircle = sphere (0 : ℂ) 1 := by ext z; simp [unitCircle]
  have hhi : InjOn h unitCircle := by rw [hunit]; exact hq.2.choose_spec.1
  have hhs := sense_circle_image hq.1
  have hext := disk_map_closed_extension hc hi himg hb hhi hhs
  obtain ⟨H, hHK, hHs, hHG, hHb, hsym, -⟩ := ab_reflect hK himg h0 hext
  have hHb' : EqOn H h unitCircle := by
    intro z hz
    have he := hHb z hz
    change (H z : ExtPlane) = (G z : ExtPlane) at he
    exact (OnePoint.coe_injective he).trans (hb hz)
  refine ⟨H, ⟨K,hHK⟩, hHs, ?_, hHb', ?_⟩
  · rw [← hunit, image_congr hHb', hhs]
  have hE : IsOpen unitDiscExterior := resolvent_exterior_isOpen
  have heq : EqOn H (fun z => (conj (G (conj z)⁻¹))⁻¹) unitDiscExterior := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hz)
    have hwD : (conj z)⁻¹ ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, norm_inv, Complex.norm_conj]
      exact inv_lt_one_of_one_lt₀ hz
    have he := hsym (conj z)⁻¹ (inv_ne_zero ((map_ne_zero _).mpr hz0))
    rw [abR_t_conj_inv_inv, hHG hwD] at he
    exact he
  have hcomp : Tendsto (fun z : ℂ => (conj z)⁻¹)
      (comap (fun z : ℂ => ‖z‖) (𝓝[>] 1)) (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) := by
    apply tendsto_comap_iff.mpr
    have hi : Tendsto (fun r : ℝ => r⁻¹) (𝓝[>] 1) (𝓝[<] 1) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa using (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact inv_lt_one_of_one_lt₀ (show (1 : ℝ) < r from hr)
    simpa only [Function.comp_def, norm_inv, Complex.norm_conj] using hi.comp tendsto_comap
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (Metric.tendsto_nhds.mp (hdec.comp hcomp)) ε hε
  have hzE : ∀ᶠ z in comap (fun z : ℂ => ‖z‖) (𝓝[>] 1), 1 < ‖z‖ :=
    tendsto_comap.eventually self_mem_nhdsWithin
  filter_upwards [he,hzE] with z hz hz1
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hz1)
  have hwD : (conj z)⁻¹ ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, norm_inv, Complex.norm_conj]
    exact inv_lt_one_of_one_lt₀ hz1
  have hw0 : (conj z)⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero _).mpr hz0)
  have hG0 : G (conj z)⁻¹ ≠ 0 := fun he =>
    hw0 (hi hwD (mem_ball_self zero_lt_one) (he.trans h0.symm))
  rw [dist_zero_right, abR_t_complexDilatation_congr hE heq hz1,
    symt_reflection_dilatation hz0 hG0 (hd _ hwD hw0)]
  simpa only [dist_zero_right, Function.comp_apply] using hz

/-- Glue two plane QC disk self-maps agreeing on the circle, retaining the
first map inside and the second map outside. -/
theorem symt_glue {A B : ℂ → ℂ} (hA : IsQuasiconformal A univ) (hAs : A '' univ = univ)
    (hAc : A '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1)
    (hB : IsQuasiconformal B univ) (hBs : B '' univ = univ)
    (hBc : B '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1)
    (heq : ∀ z : ℂ, ‖z‖ = 1 → A z = B z) :
    ∃ P : ℂ → ℂ, IsQuasiconformal P univ ∧ P '' univ = univ ∧
      EqOn P A (closedBall (0 : ℂ) 1) ∧ EqOn P B unitDiscExterior ∧
      P '' unitDiscExterior = unitDiscExterior := by
  obtain ⟨KA,hKA⟩ := hA
  obtain ⟨KB,hKB⟩ := hB
  obtain ⟨a,rfl⟩ := t1_homeomorph hKA hAs
  obtain ⟨b,rfl⟩ := t1_homeomorph hKB hBs
  obtain ⟨hAcl,-,hAE⟩ := planeHomeomorph_circle_regions a hAc
  obtain ⟨hBcl,-,hBE⟩ := planeHomeomorph_circle_regions b hBc
  let P : ℂ → ℂ := fun z => if ‖z‖ ≤ 1 then a z else b z
  have hPa : EqOn P a (closedBall (0 : ℂ) 1) := fun z hz => if_pos (mem_closedBall_zero_iff.mp hz)
  have hPb : EqOn P b unitDiscExterior := fun z hz => if_neg (not_le.mpr hz)
  have hPc : Continuous P := a.continuous.if_le b.continuous continuous_norm continuous_const heq
  have hPcl : MapsTo P (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [hPa hz]
    exact hAcl ▸ mem_image_of_mem a hz
  have hPE : MapsTo P unitDiscExterior unitDiscExterior := by
    intro z hz
    rw [hPb hz]
    exact hBE ▸ mem_image_of_mem b hz
  have hPi : Function.Injective P := by
    intro z w hzw
    by_cases hz : ‖z‖ ≤ 1 <;> by_cases hw : ‖w‖ ≤ 1
    · apply a.injective
      simpa only [P, if_pos hz, if_pos hw] using hzw
    · have h1 := mem_closedBall_zero_iff.mp (hPcl (mem_closedBall_zero_iff.mpr hz))
      have h2 := hPE (not_le.mp hw)
      rw [hzw] at h1
      exact (not_lt.mpr h1 h2).elim
    · have h1 := mem_closedBall_zero_iff.mp (hPcl (mem_closedBall_zero_iff.mpr hw))
      have h2 := hPE (not_le.mp hz)
      rw [hzw] at h2
      exact (not_lt.mpr h1 h2).elim
    · apply b.injective
      simpa only [P, if_neg hz, if_neg hw] using hzw
  have hPs : P '' univ = univ := by
    apply Set.Subset.antisymm (subset_univ _)
    intro w _
    by_cases hw : ‖w‖ ≤ 1
    · obtain ⟨z,hz,he⟩ := hAcl.symm ▸ mem_closedBall_zero_iff.mpr hw
      exact ⟨z,mem_univ _,(hPa hz).trans he⟩
    · obtain ⟨z,hz,he⟩ := hBE.symm ▸ (show w ∈ unitDiscExterior from not_le.mp hw)
      exact ⟨z,mem_univ _,(hPb hz).trans he⟩
  have hhom : IsHomeomorphOnto P univ univ := by
    have he := qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hPc.continuousOn hPi.injOn
    rwa [hPs] at he
  have hPin : IsKQC P unitDisc (max KA KB) :=
    ad_isKQC_congr ((nx_isKQC_restrict hKA isOpen_ball (subset_univ _)).mono (le_max_left _ _))
      (fun z hz => hPa (ball_subset_closedBall hz))
  have hPout : IsKQC P unitDiscExterior (max KA KB) :=
    ad_isKQC_congr ((nx_isKQC_restrict hKB resolvent_exterior_isOpen (subset_univ _)).mono (le_max_right _ _)) hPb
  refine ⟨P, ⟨_,abR_removable hhom hPin hPout⟩, hPs, hPa, hPb, ?_⟩
  rw [image_congr hPb, hBE]

/-- The actual Model B map of a symmetric class has an asymptotically conformal
QC extension; no extension or decay premise is supplied by the caller. -/
theorem symt_fB_extension {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hs : IsSymmetricHomeo (wA μ)) :
    ∃ R > 1, ∃ F : ℂ → ℂ, IsQuasiconformal F (ball 0 R) ∧ EqOn F (fB μ) unitDisc ∧
      Tendsto (complexDilatation F) (comap (fun z : ℂ => ‖z‖) (𝓝[>] 1)) (𝓝 0) := by
  have hqs : IsQSCircleHomeo (wA μ) := ⟨wA_circle_sensePreserving hμ,wA_circle_quasisymmetric hμ⟩
  obtain ⟨H,hH,hHs,hHc,hHb,hHd⟩ := symt_plane_extension hqs hs
  obtain ⟨A,hA,hAs,hAb⟩ := wA_hasQCExtension_closed hμ
  have hunit : unitCircle = sphere (0 : ℂ) 1 := by ext z; simp [unitCircle]
  have hAc : A '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    rw [← hunit]
    have he : EqOn A (wA μ) unitCircle := fun z hz => hAb (mem_closedBall_zero_iff.mpr hz.le)
    rw [image_congr he]
    exact sense_circle_image hqs.1
  obtain ⟨P,hP,hPs,hPa,hPH,hPE⟩ := symt_glue hA hAs hAc hH hHs hHc
    (fun z hz => (hAb (mem_closedBall_zero_iff.mpr hz.le)).trans (hHb hz).symm)
  obtain ⟨KG,hKG⟩ := normalizedWeldingExterior_quasiconformal hμ
  obtain ⟨e,he⟩ := t203_pack_homeo hKG (normalizedWeldingExterior_homeomorph hμ).2.2.1
  have heK : IsKQC e univ KG := by rw [he]; exact hKG
  have hed : DifferentiableOn ℂ e unitDiscExterior := by
    rw [he]; exact normalizedWeldingExterior_differentiableOn hμ
  have hE := resolvent_exterior_isOpen
  have hconf : IsConformalOnto e unitDiscExterior (e '' unitDiscExterior) := ⟨hed,e.injective.injOn,rfl⟩
  have hPd : Tendsto (complexDilatation P) (comap (fun z : ℂ => ‖z‖) (𝓝[>] 1)) (𝓝 0) := by
    apply hHd.congr'
    filter_upwards [tendsto_comap.eventually self_mem_nhdsWithin] with z hz
    exact (abR_t_complexDilatation_congr hE hPH hz).symm
  obtain ⟨KP,hKP⟩ := hP
  have hFK := thm7_1_comp hKP heK (subset_univ _)
  refine ⟨2,by norm_num,e ∘ P,⟨KP*KG,nx_isKQC_restrict hFK isOpen_ball (subset_univ _)⟩,?_,?_⟩
  · intro z hz
    rw [Function.comp_apply,hPa (ball_subset_closedBall hz),hAb (ball_subset_closedBall hz),he]
    exact normalizedWeldingExterior_closedDisk hμ (ball_subset_closedBall hz)
  · apply hPd.congr'
    filter_upwards [tendsto_comap.eventually self_mem_nhdsWithin] with z hz
    have hpE : P z ∈ unitDiscExterior := hPE ▸ mem_image_of_mem P hz
    have hpU : e (P z) ∈ e '' unitDiscExterior := mem_image_of_mem e hpE
    have hi := (hconf.symm hE).1.differentiableAt ((hconf.isOpen hE).mem_nhds hpU)
    have hinv : Function.invFunOn e unitDiscExterior (e (P z)) = P z :=
      e.injective.injOn.leftInvOn_invFunOn hpE
    exact (s23_dilatation_comp_left (continuousOn_univ.mp hKP.2.2.1.1 |>.continuousAt)
      (hed.differentiableAt (hE.mem_nhds hpE)) hi
      (by
        filter_upwards [hE.mem_nhds hpE] with w hw
        exact e.injective.injOn.leftInvOn_invFunOn hw)).symm

/-- Symmetry implies actual weighted Schwarzian decay, via the constructed extension and BP78. -/
theorem symt_schwarzian_decay {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hs : IsSymmetricHomeo (wA μ)) :
    Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (fB μ) z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) :=
  bpa_i_imp_ii (fB_holomorphic_injective hμ).1 (fB_holomorphic_injective hμ).2
    (symt_fB_extension hμ hs)

end Ch2
end TakhtajanTeo
