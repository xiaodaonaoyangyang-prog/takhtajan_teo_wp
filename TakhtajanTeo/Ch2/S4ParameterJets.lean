import TakhtajanTeo.Ch2.S4ReflectedSchwarzian
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Holomorphic parameter dependence survives spatial differentiation

Locally uniform spatial difference quotients supply parameter holomorphy
without assuming an unavailable extra joint spatial derivative.
-/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

-- L15
theorem s4v_param_fderiv_holomorphic {F : ℂ → ℂ → ℂ} {P U : Set ℂ}
    (hP : IsOpen P) (hU : IsOpen U)
    (hp : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hz : ∀ t ∈ P, DifferentiableOn ℝ (F t) U)
    (hd : ContinuousOn (fun q : ℂ × ℂ => fderiv ℝ (F q.1) q.2) (P ×ˢ U))
    {z : ℂ} (hzU : z ∈ U) (a : ℂ) :
    DifferentiableOn ℂ (fun t => fderiv ℝ (F t) z a) P := by
  let Q : ℝ → ℂ → ℂ := fun h t => (h : ℂ)⁻¹ * (F t (z + h • a) - F t z)
  have hstep : Tendsto (fun h : ℝ => z + h • a) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun h : ℝ => z + h • a) := by fun_prop
    simpa using hc.tendsto (0 : ℝ)
  have hhol : ∀ᶠ h : ℝ in 𝓝[≠] 0, DifferentiableOn ℂ (Q h) P := by
    filter_upwards [(hstep.eventually (hU.mem_nhds hzU)).filter_mono nhdsWithin_le_nhds] with h hh
    exact ((hp _ hh).sub (hp z hzU)).const_mul _
  have hlim : TendstoLocallyUniformlyOn Q (fun t => fderiv ℝ (F t) z a) (𝓝[≠] (0 : ℝ)) P := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hP]
    intro K hKP hK
    obtain ⟨R, hR, hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hzU)
    have hc : ContinuousOn (fun q : ℂ × ℂ => fderiv ℝ (F q.2) q.1)
        (closedBall z R ×ˢ K) :=
      hd.comp continuous_swap.continuousOn (fun q hq => ⟨hKP hq.2, hRU hq.1⟩)
    have huc := ((isCompact_closedBall z R).prod hK).uniformContinuousOn_of_continuous hc
    have hdlim : TendstoUniformlyOn (fun w t => fderiv ℝ (F t) w)
        (fun t => fderiv ℝ (F t) z) (𝓝 z) K := by
      have h := huc.tendstoUniformlyOn (F := fun w t => fderiv ℝ (F t) w) (mem_closedBall_self hR.le)
      rwa [nhdsWithin_eq_nhds.mpr (closedBall_mem_nhds z hR)] at h
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hεa : 0 < ε / (‖a‖ + 1) := div_pos hε (by positivity)
    have hev := (Metric.tendstoUniformlyOn_iff.mp hdlim) _ hεa
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hev (hU.mem_nhds hzU))
    filter_upwards [(hstep.eventually (ball_mem_nhds z hδ)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with h hh hn
    have hn0 : h ≠ 0 := hn
    intro t ht
    let A : ℂ →L[ℝ] ℂ := fderiv ℝ (F t) z
    have hdiff : ∀ w ∈ ball z δ, HasFDerivWithinAt (fun w => F t w - A w)
        (fderiv ℝ (F t) w - A) (ball z δ) w := by
      intro w hw
      exact (((hz t (hKP ht)).differentiableAt (hU.mem_nhds (hsub hw).2)).hasFDerivAt.sub
        A.hasFDerivAt).hasFDerivWithinAt
    have hbound : ∀ w ∈ ball z δ, ‖fderiv ℝ (F t) w - A‖ ≤ ε / (‖a‖ + 1) := by
      intro w hw
      have he := (hsub hw).1 t ht
      have he' : ‖fderiv ℝ (F t) w - A‖ < ε / (‖a‖ + 1) := by
        simpa only [A, dist_eq_norm, norm_sub_rev] using he
      exact he'.le
    have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      hdiff hbound (convex_ball z δ) (mem_ball_self hδ) hh
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hmvt
    have halg : Q h t - A a = (h : ℂ)⁻¹ *
        ((F t (z + h • a) - A (z + h • a)) - (F t z - A z)) := by
      dsimp only [Q]
      rw [map_add, map_smul]
      simp only [Complex.real_smul]
      field_simp [Complex.ofReal_ne_zero.mpr hn0]
      <;> ring
    have he : ‖Q h t - A a‖ < ε := by
      rw [halg, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
      calc
        |h|⁻¹ * ‖(F t (z + h • a) - A (z + h • a)) - (F t z - A z)‖
            ≤ |h|⁻¹ * (ε / (‖a‖ + 1) * (|h| * ‖a‖)) :=
          mul_le_mul_of_nonneg_left hmvt (inv_nonneg.mpr (abs_nonneg h))
        _ = ε / (‖a‖ + 1) * ‖a‖ := by field_simp [abs_ne_zero.mpr hn0]
        _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
    simpa only [A, dist_eq_norm, norm_sub_rev] using he
  exact hlim.differentiableOn hhol hP

-- L16
theorem s4v_dz_family_regular {X : Type} [TopologicalSpace X]
    {F : X → ℂ → ℂ} {P : Set X} {U : Set ℂ} {n : ℕ} (hU : IsOpen U)
    (hs : ∀ t ∈ P, ContDiffOn ℝ (n + 1 : ℕ) (F t) U)
    (hc : ∀ j ≤ n + 1, ContinuousOn
      (fun q : X × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U)) :
    (∀ t ∈ P, ContDiffOn ℝ n (dz (F t)) U) ∧
      ∀ j ≤ n, ContinuousOn
        (fun q : X × ℂ => iteratedFDeriv ℝ j (dz (F q.1)) q.2) (P ×ˢ U) := by
  let L : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
    (2 : ℂ)⁻¹ • (ContinuousLinearMap.apply ℝ ℂ 1 - I • ContinuousLinearMap.apply ℝ ℂ I)
  have he (t : X) : (fun z => L (fderiv ℝ (F t) z)) = dz (F t) := by
    funext z
    simp [L, dz, div_eq_inv_mul]
  simpa only [he] using wr_d2a_der hU hs hc L

-- L17
theorem s4v_param_dz_holomorphic {F : ℂ → ℂ → ℂ} {P U : Set ℂ} {n : ℕ}
    (hP : IsOpen P) (hU : IsOpen U)
    (hp : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hs : ∀ t ∈ P, ContDiffOn ℝ (n + 1 : ℕ) (F t) U)
    (hc : ∀ j ≤ n + 1, ContinuousOn
      (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U))
    {z : ℂ} (hzU : z ∈ U) :
    DifferentiableOn ℂ (fun t => dz (F t) z) P := by
  have hraw := wr_d2a_der hU hs hc (ContinuousLinearMap.id ℝ (ℂ →L[ℝ] ℂ))
  have hFD : ContinuousOn (fun q : ℂ × ℂ => fderiv ℝ (F q.1) q.2) (P ×ˢ U) := by
    have hraw0 : ContinuousOn
        (fun q : ℂ × ℂ => iteratedFDeriv ℝ 0 (fderiv ℝ (F q.1)) q.2) (P ×ˢ U) := by
      simpa only [ContinuousLinearMap.id_apply] using hraw.2 0 (Nat.zero_le n)
    exact wr_d2a_zero (a := fun t => fderiv ℝ (F t)) hraw0
  have hdiff : ∀ t ∈ P, DifferentiableOn ℝ (F t) U := by
    intro t ht
    exact (hs t ht).differentiableOn (by norm_cast)
  have h1 := s4v_param_fderiv_holomorphic hP hU hp hdiff hFD hzU 1
  have hI := s4v_param_fderiv_holomorphic hP hU hp hdiff hFD hzU I
  simpa only [dz, Pi.sub_apply] using (h1.sub (hI.const_mul I)).div_const (2 : ℂ)

-- L18
theorem s4v_schwarzianDz_eq {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 3 f z)
    (hn : dz f z ≠ 0) :
    schwarzianDz f z = dz (dz (dz f)) z / dz f z -
      (3 / 2 : ℂ) * (dz (dz f) z / dz f z) ^ 2 := by
  have h1 : ContDiffAt ℝ 2 (dz f) z := e41_dz_contDiffAt hf (by norm_num)
  have h2 : ContDiffAt ℝ 1 (dz (dz f)) z := e41_dz_contDiffAt h1 (by norm_num)
  unfold schwarzianDz
  rw [(t203_dz_div (h2.differentiableAt (by norm_num)) (h1.differentiableAt (by norm_num)) hn).1]
  field_simp
  <;> ring

-- L19
theorem s4v_param_schwarzian_holomorphic {F : ℂ → ℂ → ℂ} {P U : Set ℂ}
    (hP : IsOpen P) (hU : IsOpen U)
    (hp : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hs : ∀ t ∈ P, ContDiffOn ℝ 3 (F t) U)
    (hc : ∀ j ≤ 3, ContinuousOn
      (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U))
    {z t : ℂ} (hzU : z ∈ U) (htP : t ∈ P) (hn : dz (F t) z ≠ 0) :
    DifferentiableAt ℂ (fun s => schwarzianDz (F s) z) t := by
  have h1 := s4v_dz_family_regular (n := 2) hU hs hc
  have h2 := s4v_dz_family_regular (n := 1) hU h1.1 h1.2
  have hp1 : ∀ w ∈ U, DifferentiableOn ℂ (fun s => dz (F s) w) P :=
    fun w hw => s4v_param_dz_holomorphic (n := 2) hP hU hp hs hc hw
  have hp2 : ∀ w ∈ U, DifferentiableOn ℂ (fun s => dz (dz (F s)) w) P :=
    fun w hw => s4v_param_dz_holomorphic (n := 1) hP hU hp1 h1.1 h1.2 hw
  have hp3 : DifferentiableOn ℂ (fun s => dz (dz (dz (F s))) z) P :=
    s4v_param_dz_holomorphic (n := 0) hP hU hp2 h2.1 h2.2 hzU
  have hd1 := (hp1 z hzU).differentiableAt (hP.mem_nhds htP)
  have hd2 := (hp2 z hzU).differentiableAt (hP.mem_nhds htP)
  have hd3 := hp3.differentiableAt (hP.mem_nhds htP)
  have he : (fun s => schwarzianDz (F s) z) =ᶠ[𝓝 t]
      (fun s => dz (dz (dz (F s))) z / dz (F s) z -
        (3 / 2 : ℂ) * (dz (dz (F s)) z / dz (F s) z) ^ 2) := by
    filter_upwards [hP.mem_nhds htP, hd1.continuousAt.eventually_ne hn] with s hsP hs0
    exact s4v_schwarzianDz_eq ((hs s hsP).contDiffAt (hU.mem_nhds hzU)) hs0
  exact ((hd3.div hd1 hn).sub (((hd2.div hd1 hn).pow 2).const_mul (3 / 2 : ℂ))).congr_of_eventuallyEq he

-- L20
theorem s4v_schwarzian_joint_continuous {X : Type} [TopologicalSpace X]
    {F : X → ℂ → ℂ} {P : Set X} {U : Set ℂ} (hU : IsOpen U)
    (hs : ∀ t ∈ P, ContDiffOn ℝ 3 (F t) U)
    (hc : ∀ j ≤ 3, ContinuousOn
      (fun q : X × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U))
    (hn : ∀ t ∈ P, ∀ z ∈ U, dz (F t) z ≠ 0) :
    ContinuousOn (fun q : X × ℂ => schwarzianDz (F q.1) q.2) (P ×ˢ U) := by
  have h1 := s4v_dz_family_regular (n := 2) hU hs hc
  have h2 := s4v_dz_family_regular (n := 1) hU h1.1 h1.2
  have h3 := s4v_dz_family_regular (n := 0) hU h2.1 h2.2
  have hzero {G : X → ℂ → ℂ}
      (h : ContinuousOn (fun q : X × ℂ => iteratedFDeriv ℝ 0 (G q.1) q.2) (P ×ˢ U)) :
      ContinuousOn (fun q : X × ℂ => G q.1 q.2) (P ×ˢ U) := by
    refine ((continuousMultilinearCurryFin0 ℝ ℂ ℂ).continuous.comp_continuousOn h).congr fun q _ => ?_
    change G q.1 q.2 = continuousMultilinearCurryFin0 ℝ ℂ ℂ (iteratedFDeriv ℝ 0 (G q.1) q.2)
    rw [iteratedFDeriv_zero_eq_comp]
    simp
  have hc1 := hzero (G := fun t => dz (F t)) (h1.2 0 (by norm_num))
  have hc2 := hzero (G := fun t => dz (dz (F t))) (h2.2 0 (by norm_num))
  have hc3 := hzero (G := fun t => dz (dz (dz (F t)))) (h3.2 0 (by norm_num))
  have hnon : ∀ q ∈ P ×ˢ U, dz (F q.1) q.2 ≠ 0 := fun q hq => hn q.1 hq.1 q.2 hq.2
  refine ((hc3.div hc1 hnon).sub (((hc2.div hc1 hnon).pow 2).const_mul (3 / 2 : ℂ))).congr ?_
  intro q hq
  exact s4v_schwarzianDz_eq ((hs q.1 hq.1).contDiffAt (hU.mem_nhds hq.2)) (hnon q hq)

end Ch2
end TakhtajanTeo
