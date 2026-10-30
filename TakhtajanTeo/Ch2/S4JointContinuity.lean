import TakhtajanTeo.Ch2.S4PullbackAssembly

/-! # Joint continuity and parameter holomorphy at the auxiliary point (`s4pv_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- P13
theorem s4pv_joint_dz_smooth {F : ℂ → ℂ → ℂ} {D : Set (ℂ × ℂ)}
    {n m : WithTop ℕ∞} (hD : IsOpen D)
    (hF : ContDiffOn ℝ n (fun p : ℂ × ℂ => F p.1 p.2) D) (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (fun p : ℂ × ℂ => dz (F p.1) p.2) D := by
  intro p hp
  have hFp := hF.contDiffAt (hD.mem_nhds hp)
  have hu : ContDiffAt ℝ n (Function.uncurry (fun q : ℂ × ℂ => F q.1)) (p, p.2) :=
    hFp.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hd : ContDiffAt ℝ m (fun q : ℂ × ℂ => fderiv ℝ (F q.1) q.2) p :=
    hu.fderiv contDiffAt_snd hmn
  have h1 : ContDiffAt ℝ m (fun q : ℂ × ℂ => fderiv ℝ (F q.1) q.2 1) p :=
    hd.clm_apply contDiffAt_const
  have hi : ContDiffAt ℝ m (fun q : ℂ × ℂ => fderiv ℝ (F q.1) q.2 I) p :=
    hd.clm_apply contDiffAt_const
  exact ((h1.sub (contDiffAt_const.mul hi)).div_const 2).contDiffWithinAt

-- P14
theorem s4pv_joint_schwarzian_continuous {F : ℂ → ℂ → ℂ} {D : Set (ℂ × ℂ)}
    (hD : IsOpen D) (hF : ContDiffOn ℝ 3 (fun p : ℂ × ℂ => F p.1 p.2) D)
    (hn : ∀ p ∈ D, dz (F p.1) p.2 ≠ 0) :
    ContinuousOn (fun p : ℂ × ℂ => schwarzianDz (F p.1) p.2) D := by
  have h1 := s4pv_joint_dz_smooth (m := 2) hD hF (by norm_num)
  have h2 := s4pv_joint_dz_smooth (F := fun e => dz (F e)) (m := 1) hD h1 (by norm_num)
  have h3 := s4pv_joint_dz_smooth (F := fun e => dz (dz (F e))) (m := 0) hD h2 (by norm_num)
  refine ((h3.continuousOn.div h1.continuousOn hn).sub
    (((h2.continuousOn.div h1.continuousOn hn).pow 2).const_mul (3 / 2 : ℂ))).congr ?_
  intro p hp
  have hs : ContDiffAt ℝ 3 (F p.1) p.2 :=
    (hF.contDiffAt (hD.mem_nhds hp)).comp (f := fun z : ℂ => (p.1, z)) p.2
      (contDiffAt_const.prodMk contDiffAt_id)
  exact s4v_schwarzianDz_eq hs (hn p hp)

-- P15
theorem s4pv_holomorphic_family_jets {F : ℂ → ℂ → ℂ} {P U : Set ℂ}
    (hP : IsOpen P) (hU : IsOpen U)
    (hc : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (P ×ˢ U))
    (hh : ∀ e ∈ P, DifferentiableOn ℂ (F e) U) (j : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => iteratedFDeriv ℝ j (F p.1) p.2) (P ×ˢ U) := by
  intro p hp
  obtain ⟨R, hR, hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp.2)
  let H := fun e z : ℂ => ∮ ξ in C(p.2, R),
    (ξ - z) ^ (-1 : ℤ) • ((2 * π * I)⁻¹ * F e ξ)
  have hcircle : ContinuousOn (fun q : ℂ × ℂ => (2 * π * I)⁻¹ * F q.1 q.2)
      (P ×ˢ sphere p.2 R) :=
    continuousOn_const.mul (hc.mono (prod_mono Subset.rfl (sphere_subset_closedBall.trans hRU)))
  have hH : ContinuousOn (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (H q.1) q.2)
      (P ×ˢ ball p.2 R) := wr_param_cauchy_iter_cont
        (h := fun e ξ : ℂ => (2 * π * I)⁻¹ * F e ξ) hR hcircle j
  have hrep : ∀ e ∈ P, ∀ z ∈ ball p.2 R, F e z = H e z := by
    intro e he z hz
    have hCa := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (f := F e) (c := p.2) (R := R) Set.countable_empty hz ((hh e he).continuousOn.mono hRU)
      (fun x hx => (hh e he).differentiableAt (hU.mem_nhds (hRU (ball_subset_closedBall hx.1))))
    calc F e z = (2 * π * I)⁻¹ • ∮ ξ in C(p.2, R), (ξ - z)⁻¹ • F e ξ := hCa.symm
      _ = (2 * π * I)⁻¹ * ∮ ξ in C(p.2, R), F e ξ / (ξ - z) := by
          rw [smul_eq_mul]
          congr 1
          apply circleIntegral.integral_congr hR.le
          intro ξ hξ
          simp only [smul_eq_mul, div_eq_mul_inv]
          ring
      _ = H e z := wr_cauchy_form (F e) p.2 z R
  have hpB : p ∈ P ×ˢ ball p.2 R := ⟨hp.1, mem_ball_self hR⟩
  apply ContinuousAt.continuousWithinAt
  apply (hH.continuousAt ((hP.prod isOpen_ball).mem_nhds hpB)).congr_of_eventuallyEq
  filter_upwards [(hP.prod isOpen_ball).mem_nhds hpB] with q hq
  have heq : F q.1 =ᶠ[𝓝 q.2] H q.1 := by
    filter_upwards [isOpen_ball.mem_nhds hq.2] with z hz
    exact hrep q.1 hq.1 z hz
  exact (heq.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds

-- P16
theorem s4pv_parameter_holomorphic_at_exception {F : ℂ → ℂ → ℂ} {P U : Set ℂ}
    (hP : IsOpen P) (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hc : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (P ×ˢ U))
    (hh : ∀ z ∈ U, z ≠ z₀ → DifferentiableOn ℂ (fun e => F e z) P) :
    DifferentiableOn ℂ (fun e => F e z₀) P := by
  have hlim : TendstoLocallyUniformlyOn (fun z e : ℂ => F e z) (fun e => F e z₀)
      (𝓝[≠] z₀) P := by
    rw [hP.tendstoLocallyUniformlyOn_iff_forall_tendsto]
    intro e he
    have hc₀ : Tendsto (fun p : ℂ × ℂ => F p.1 p.2) (𝓝 (e, z₀)) (𝓝 (F e z₀)) :=
      (hc.continuousAt ((hP.prod hU).mem_nhds (show (e, z₀) ∈ P ×ˢ U from ⟨he, hz₀⟩))).tendsto
    have hleft : Tendsto (fun q : ℂ × ℂ => (q.2, z₀))
        ((𝓝[≠] z₀) ×ˢ 𝓝 e) (𝓝 (e, z₀)) :=
      tendsto_snd.prodMk_nhds tendsto_const_nhds
    have hright : Tendsto (fun q : ℂ × ℂ => (q.2, q.1))
        ((𝓝[≠] z₀) ×ˢ 𝓝 e) (𝓝 (e, z₀)) :=
      tendsto_snd.prodMk_nhds (tendsto_fst.mono_right nhdsWithin_le_nhds)
    exact ((hc₀.comp hleft).prodMk_nhds (hc₀.comp hright)).mono_right (nhds_le_uniformity _)
  apply hlim.differentiableOn _ hP
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hz₀),
    self_mem_nhdsWithin] with z hz hne
  exact hh z hz hne

end Ch2
end TakhtajanTeo
