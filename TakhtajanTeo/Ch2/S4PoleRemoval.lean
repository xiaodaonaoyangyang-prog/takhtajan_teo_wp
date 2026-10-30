import TakhtajanTeo.Ch2.S4JointContinuity

/-! # Removing the auxiliary coordinate exception in the actual variation (`s4pv_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- P17
theorem s4pv_gsans_joint_continuous :
    ContinuousOn (fun p : LinfStar × ℂ => gsans p.1 p.2) (LinfStarBall ×ˢ unitDiscExterior) := by
  have hi : ContinuousOn (fun p : LinfStar × ℂ => Function.invFun (wAS p.1) (p.2 : ExtPlane))
      (LinfStarBall ×ˢ unitDiscExterior) :=
    AppA.acc_wAS_inv_cont.comp (f := fun p : LinfStar × ℂ => (p.1, (p.2 : ExtPlane)))
      (continuous_fst.prodMk (OnePoint.continuous_coe.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  have hB : ContinuousOn (fun p : LinfStar × ℂ =>
      wB p.1 (Function.invFun (wAS p.1) (p.2 : ExtPlane))) (LinfStarBall ×ˢ unitDiscExterior) :=
    AppA.acc_wB_cont.comp (f := fun p : LinfStar × ℂ =>
      (p.1, Function.invFun (wAS p.1) (p.2 : ExtPlane)))
      (continuousOn_fst.prodMk hi) (fun p hp => ⟨hp.1, mem_univ _⟩)
  apply OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff.mpr
  refine hB.congr ?_
  intro p hp
  change (gsans p.1 p.2 : ExtPlane) = _
  rw [(r22_fsans_gsans hp.1).2]
  exact gMu_sphere_factorization hp.1 hp.2

-- P18
theorem s4pv_welded_schwarzian_continuous {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    let D := {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior ∧
      wAS (p.1 • ν) (p.2 : ExtPlane) ≠ extInf}
    IsOpen D ∧ ContinuousOn (fun p : ℂ × ℂ => schwarzianDz
      (gsans (beltramiMul (p.1 • ν) κ) ∘ wA (p.1 • ν)) p.2) D := by
  let B : Set ℂ := {e | ‖e‖ * ‖ν‖ < 1}
  let D := {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior ∧
    wAS (p.1 • ν) (p.2 : ExtPlane) ≠ extInf}
  let G := fun e : ℂ => gsans (beltramiMul (e • ν) κ)
  let W := fun e : ℂ => wA (e • ν)
  change IsOpen D ∧ ContinuousOn (fun p : ℂ × ℂ => schwarzianDz (G p.1 ∘ W p.1) p.2) D
  have hB : IsOpen B := isOpen_lt (continuous_norm.mul continuous_const) continuous_const
  have heB : ∀ e ∈ B, e • ν ∈ LinfStarBall := by
    intro e he
    simpa [B, LinfStarBall, mem_ball_zero_iff, norm_smul] using he
  have hellB : ∀ e ∈ B, beltramiMul (e • ν) κ ∈ LinfStarBall := fun e he => (wA_mul hκ (heB e he)).1
  have hS : ContinuousOn (fun p : ℂ × ℂ => wAS (p.1 • ν) (p.2 : ExtPlane))
      (B ×ˢ unitDiscExterior) :=
    AppA.acc_wAS_cont.comp (f := fun p : ℂ × ℂ => (p.1 • ν, (p.2 : ExtPlane)))
      ((continuous_fst.smul continuous_const).prodMk (OnePoint.continuous_coe.comp continuous_snd)).continuousOn
      (fun p hp => ⟨heB p.1 hp.1, mem_univ _⟩)
  have hD : IsOpen D := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hSp : B ×ˢ unitDiscExterior ∈ 𝓝 p :=
      (hB.prod wp_exterior_isOpen).mem_nhds ⟨hp.1, hp.2.1⟩
    filter_upwards [hSp, (hS.continuousAt hSp).eventually_ne hp.2.2] with q hq hfin
    exact ⟨hq.1, hq.2, hfin⟩
  have hellc : ContinuousOn (fun e : ℂ => beltramiMul (e • ν) κ) B :=
    (bd_differentiableOn hκ).continuousOn.comp (continuous_id.smul continuous_const).continuousOn heB
  have hGc : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2) (B ×ˢ unitDiscExterior) :=
    s4pv_gsans_joint_continuous.comp (f := fun p : ℂ × ℂ => (beltramiMul (p.1 • ν) κ, p.2))
      ((hellc.comp continuousOn_fst (fun p hp => hp.1)).prodMk continuousOn_snd)
      (fun p hp => ⟨hellB p.1 hp.1, hp.2⟩)
  have hGh : ∀ e ∈ B, DifferentiableOn ℂ (G e) unitDiscExterior :=
    fun e he => (S2C.s2c_conf_g (hellB e he)).1
  have hGs : ∀ e ∈ B, ContDiffOn ℝ 3 (G e) unitDiscExterior :=
    fun e he => ((hGh e he).contDiffOn wp_exterior_isOpen).restrict_scalars ℝ
  have hGn : ∀ e ∈ B, ∀ z ∈ unitDiscExterior, dz (G e) z ≠ 0 := by
    intro e he z hz
    obtain ⟨ha, hn⟩ := e41_g_holo (hellB e he) hz
    rw [dz_eq_deriv ha.differentiableAt]
    exact hn
  have hGSz := s4v_schwarzian_joint_continuous wp_exterior_isOpen hGs
    (fun j _ => s4pv_holomorphic_family_jets hB wp_exterior_isOpen hGc hGh j) hGn
  have hGSh : ContinuousOn (fun p : ℂ × ℂ => schwarzianHol (G p.1) p.2) (B ×ˢ unitDiscExterior) := by
    refine hGSz.congr ?_
    intro p hp
    obtain ⟨ha, hn⟩ := e41_g_holo (hellB p.1 hp.1) hp.2
    exact (s4ma_schwarzianDz_hol ha hn).symm
  have hW : ContDiffOn ℝ 3 (fun p : ℂ × ℂ => W p.1 p.2) D := wr_joint_contDiff_A hν
  have hWn : ∀ p ∈ D, dz (W p.1) p.2 ≠ 0 :=
    fun p hp => (e41_w_regular hν hp.1 hp.2.1 hp.2.2).2.1
  have hWE : ∀ p ∈ D, W p.1 p.2 ∈ unitDiscExterior :=
    fun p hp => (e41_w_regular hν hp.1 hp.2.1 hp.2.2).2.2
  have hWz := s4pv_joint_dz_smooth (F := W) (m := 2) hD hW (by norm_num)
  have hWS := s4pv_joint_schwarzian_continuous hD hW hWn
  have hGScomp := hGSh.comp (f := fun p : ℂ × ℂ => (p.1, W p.1 p.2))
    (continuousOn_fst.prodMk hW.continuousOn)
    (fun (p : ℂ × ℂ) (hp : p ∈ D) => ⟨hp.1, hWE p hp⟩)
  refine ⟨hD, ((hGScomp.mul (hWz.continuousOn.pow 2)).add hWS).congr ?_⟩
  intro p hp
  obtain ⟨hwc, hwz, hwE⟩ := e41_w_regular hν hp.1 hp.2.1 hp.2.2
  obtain ⟨hga, hgz⟩ := e41_g_holo (hellB p.1 hp.1) hwE
  exact e41_schw_left hga hgz hwc hwz

-- P19
theorem s4pv_welded_schwarzian_holomorphic {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    DifferentiableAt ℂ (fun e : ℂ => schwarzianDz
      (gsans (beltramiMul (e • ν) κ) ∘ wA (e • ν)) z) 0 := by
  obtain ⟨P, hP, hP₀, hsmall, hhol⟩ := s4pv_welded_schwarzian_holomorphic_off_point hκ hν
  have hp₀ : wAS ((0 : ℂ) • ν) (z : ExtPlane) ≠ extInf :=
    (s4ma_pole_absent_eventually ν z).self_of_nhds
  by_cases hz₀ : wAS κ extInf ≠ (z : ExtPlane)
  · exact hhol 0 hP₀ z hz hz₀ hp₀
  have hbase : wAS κ extInf = (z : ExtPlane) := not_ne_iff.mp hz₀
  let D := {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior ∧
    wAS (p.1 • ν) (p.2 : ExtPlane) ≠ extInf}
  obtain ⟨hD, hc⟩ := s4pv_welded_schwarzian_continuous hκ hν
  have hnear : ∀ᶠ q : ℂ × ℂ in 𝓝 ((0 : ℂ), z), q.1 ∈ P ∧ q ∈ D :=
    ((continuous_fst.tendsto (0, z)).eventually (hP.mem_nhds hP₀)).and
      (hD.mem_nhds (show ((0 : ℂ), z) ∈ D from ⟨by simp, hz, hp₀⟩))
  obtain ⟨Q, V, hQ, hQ₀, hV, hzV, hQV⟩ := mem_nhds_prod_iff'.mp hnear
  have hcont : ContinuousOn (fun q : ℂ × ℂ => schwarzianDz
      (gsans (beltramiMul (q.1 • ν) κ) ∘ wA (q.1 • ν)) q.2) (Q ×ˢ V) :=
    hc.mono fun q hq => (hQV hq).2
  have haway : ∀ u ∈ V, u ≠ z → DifferentiableOn ℂ
      (fun e : ℂ => schwarzianDz (gsans (beltramiMul (e • ν) κ) ∘ wA (e • ν)) u) Q := by
    intro u hu hne e he
    have hq := hQV (show (e, u) ∈ Q ×ˢ V from ⟨he, hu⟩)
    have hnu : wAS κ extInf ≠ (u : ExtPlane) := by
      intro heq
      exact hne (OnePoint.coe_injective (hbase.symm.trans heq)).symm
    exact (hhol e hq.1 u hq.2.2.1 hnu hq.2.2.2).differentiableWithinAt
  exact (s4pv_parameter_holomorphic_at_exception hQ hV hzV hcont haway).differentiableAt
    (hQ.mem_nhds hQ₀)

-- P20
theorem s4pv_variation {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    dzbar (fun e => schwarzianHol (gsans (beltramiMul (e • toLinf ν) κ)) (wA (e • toLinf ν) z) *
        dz (wA (e • toLinf ν)) z ^ 2) 0 =
      6 / π * ∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4 := by
  have hνh : toLinf ν ∈ harmonicBeltrami := (harmonicL2_subset_harmonic.choose_spec ν hν).1
  let H := fun e : ℂ => schwarzianDz (gsans (beltramiMul (e • toLinf ν) κ) ∘ wA (e • toLinf ν)) z
  let W := fun e : ℂ => schwarzianDz (wA (e • toLinf ν)) z
  have hH : DifferentiableAt ℂ H 0 := s4pv_welded_schwarzian_holomorphic hκ hνh hz
  have hW := s4ma_wA_variation hνh hz
  have hsmall : ∀ᶠ e : ℂ in 𝓝 0, ‖e‖ * ‖toLinf ν‖ < 1 :=
    (continuous_norm.mul continuous_const).continuousAt.eventually_lt continuousAt_const (by simp)
  have heq : (fun e : ℂ => schwarzianHol (gsans (beltramiMul (e • toLinf ν) κ))
      (wA (e • toLinf ν) z) * dz (wA (e • toLinf ν)) z ^ 2) =ᶠ[𝓝 0] (fun e => H e - W e) := by
    filter_upwards [hsmall, s4ma_pole_absent_eventually (toLinf ν) z] with e he hp
    have heB : e • toLinf ν ∈ LinfStarBall := by
      simpa [LinfStarBall, mem_ball_zero_iff, norm_smul] using he
    obtain ⟨hwc, hwz, hwE⟩ := e41_w_regular hνh he hz hp
    obtain ⟨hga, hgz⟩ := e41_g_holo (wA_mul hκ heB).1 hwE
    exact eq_sub_of_add_eq (e41_schw_left hga hgz hwc hwz).symm
  have hsub : dzbar (fun e => H e - W e) 0 = dzbar H 0 - dzbar W 0 := by
    unfold dzbar
    rw [fderiv_fun_sub (hH.restrictScalars ℝ) hW.1]
    simp only [sub_apply]
    ring
  have hi : (∫ w in unitDiscExterior, conj ((toLinf ν) w) / (1 - conj w * z) ^ 4) =
      ∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4 := by
    apply integral_congr_ae
    filter_upwards [wp_harmonic_toLinf_ae hν] with w hw
    rw [hw]
  rw [(t203_c1_dz_congr heq).2, hsub, (cauchyRiemann_iff.mp hH).2]
  change 0 - dzbar (fun e : ℂ => schwarzianDz (wA (e • toLinf ν)) z) 0 = _
  rw [hW.2, hi]
  ring

end Ch2
end TakhtajanTeo
