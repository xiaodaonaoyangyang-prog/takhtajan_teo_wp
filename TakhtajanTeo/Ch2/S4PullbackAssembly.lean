import TakhtajanTeo.Ch2.S4PullbackHolomorphic

/-! # Identifying the actual welding Schwarzian in the smooth chart (`s4pv_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- P10
theorem s4pv_chart_schwarzian {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) {e : ℂ} (he : ‖e‖ * ‖ν‖ < 1)
    {U : Set ℂ} {J : ℂ → ℂ} (hJ : AnalyticOnNhd ℂ J U)
    (hmap : MapsTo J U unitDiscExterior) (hJzero : ∀ y ∈ U, deriv J y ≠ 0)
    (hchart : ∀ x ∈ unitDiscExterior, wAS κ (x : ExtPlane) ≠ extInf →
      qcv_planeSolution κ x ∈ U ∧ J (qcv_planeSolution κ x) = wA κ x)
    {y : ℂ} (hy : y ∈ qcv_planeSolution κ ''
      {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf})
    (hR : ContDiffAt ℝ 3 (qcv_planeTransition (beltramiMul (e • ν) κ) κ) y)
    (hRzero : dz (qcv_planeTransition (beltramiMul (e • ν) κ) κ) y ≠ 0)
    (hp : wAS (e • ν) (J y : ExtPlane) ≠ extInf) :
    (schwarzianHol (gsans (beltramiMul (e • ν) κ)) (wA (e • ν) (J y)) *
        dz (wA (e • ν)) (J y) ^ 2 + schwarzianDz (wA (e • ν)) (J y)) * deriv J y ^ 2 +
      schwarzianHol J y = schwarzianDz (qcv_planeTransition (beltramiMul (e • ν) κ) κ) y := by
  let V := qcv_planeSolution κ ''
    {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}
  have hV : IsOpen V := s4pv_plane_exterior_isOpen hκ
  have hVU : V ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hchart x hx.1 hx.2).1
  have hyU : y ∈ U := hVU hy
  have hJa := hJ y hyU
  have heB : e • ν ∈ LinfStarBall := by
    simpa [LinfStarBall, mem_ball_zero_iff, norm_smul] using he
  let ell := beltramiMul (e • ν) κ
  let R := qcv_planeTransition ell κ
  have hell : ell ∈ LinfStarBall := (wA_mul hκ heB).1
  have hcomp : wAS ell = wAS (e • ν) ∘ wAS κ := (wA_mul hκ heB).2.1
  obtain ⟨a, b, c, d, hdet, -, hfac⟩ := S2C.s2c_mobius hell
  have hvalue : ∀ u ∈ V, wAS (e • ν) (J u : ExtPlane) ≠ extInf →
      c * R u + d ≠ 0 ∧
        gsans ell (wA (e • ν) (J u)) = (a * R u + b) / (c * R u + d) := by
    rintro _ ⟨x, hx, rfl⟩ hpu
    have hJx := (hchart x hx.1 hx.2).2
    rw [hJx] at hpu ⊢
    have hcoe : (wA κ x : ExtPlane) = wAS κ (x : ExtPlane) := coe_finPart_of_ne hx.2
    have hLX : wAS ell (x : ExtPlane) = wAS (e • ν) (wA κ x : ExtPlane) := by
      rw [hcomp, Function.comp_apply, ← hcoe]
    have hpell : wAS ell (x : ExtPlane) ≠ extInf := by rwa [hLX]
    have hw : wA ell x = wA (e • ν) (wA κ x) := congrArg finPart hLX
    have hRx : R (qcv_planeSolution κ x) = qcv_planeSolution ell x := by
      dsimp only [R, qcv_planeTransition, Function.comp_apply]
      rw [Function.leftInverse_invFun (qcv_planeSolution_bijective hκ).1]
    obtain ⟨hd, hv⟩ := hfac x hx.1 hpell
    rw [hRx]
    exact ⟨hd, (congrArg (gsans ell) hw).symm.trans hv⟩
  have hc : ContinuousAt (fun u : ℂ => wAS (e • ν) (J u : ExtPlane)) y :=
    (wAS_continuous heB).continuousAt.comp
      (OnePoint.continuous_coe.continuousAt.comp hJa.continuousAt)
  have heq : ((gsans ell ∘ wA (e • ν)) ∘ J) =ᶠ[𝓝 y]
      (fun u => (a * R u + b) / (c * R u + d)) := by
    filter_upwards [hV.mem_nhds hy, hc.eventually_ne hp] with u hu hpu
    exact (hvalue u hu hpu).2
  obtain ⟨hwc, hwz, hwE⟩ := e41_w_regular hν he (hmap hyU) hp
  obtain ⟨hga, hgz⟩ := e41_g_holo hell hwE
  have hFc : ContDiffAt ℝ 3 (gsans ell ∘ wA (e • ν)) (J y) :=
    (hga.contDiffAt.restrict_scalars ℝ).comp (f := wA (e • ν)) (J y) hwc
  have hFz : dz (gsans ell ∘ wA (e • ν)) (J y) ≠ 0 := by
    simp only [Function.comp_def]
    rw [e41_dz_hol_left hga.differentiableAt (hwc.differentiableAt (by norm_num))]
    exact mul_ne_zero hgz hwz
  have hEq := e41_schw_congr heq
  rw [e41_schw_right hJa (hJzero y hyU) hFc hFz,
    e41_schw_left hga hgz hwc hwz,
    s4ma_schwarzianDz_mobius hR hRzero hdet (hvalue y hy hp).1] at hEq
  exact hEq

-- P11
theorem s4pv_chart_surjective {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    {J : ℂ → ℂ} (hchart : ∀ x ∈ unitDiscExterior, wAS κ (x : ExtPlane) ≠ extInf →
      J (qcv_planeSolution κ x) = wA κ x)
    {z : ℂ} (hz : z ∈ unitDiscExterior) (hz₀ : wAS κ extInf ≠ (z : ExtPlane)) :
    ∃ y ∈ qcv_planeSolution κ ''
      {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}, J y = z := by
  have hzS : (z : ExtPlane) ∈ toExt unitDiscExterior ∪ {extInf} := Or.inl ⟨z, hz, rfl⟩
  rw [← (wA_mapsTo hκ).2.1] at hzS
  obtain ⟨X, hXE, hXz⟩ := hzS
  rcases hXE with ⟨x, hx, rfl⟩ | hXi
  · have hp : wAS κ (x : ExtPlane) ≠ extInf := by
      rw [hXz]
      exact OnePoint.coe_ne_infty z
    refine ⟨qcv_planeSolution κ x, ⟨x, ⟨hx, hp⟩, rfl⟩, ?_⟩
    rw [hchart x hx hp]
    exact congrArg finPart hXz
  · have hX : X = extInf := hXi
    exact (hz₀ (hX ▸ hXz)).elim

-- P12
theorem s4pv_welded_schwarzian_holomorphic_off_point {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    ∃ P : Set ℂ, IsOpen P ∧ 0 ∈ P ∧ (∀ e ∈ P, ‖e‖ * ‖ν‖ < 1) ∧
      ∀ e ∈ P, ∀ z ∈ unitDiscExterior, wAS κ extInf ≠ (z : ExtPlane) →
        wAS (e • ν) (z : ExtPlane) ≠ extInf →
        DifferentiableAt ℂ (fun t : ℂ => schwarzianDz
          (gsans (beltramiMul (t • ν) κ) ∘ wA (t • ν)) z) e := by
  obtain ⟨A, hA, hA₀, hreg, -, hn, hhol⟩ := s4pv_plane_transition_regular hκ hν
  obtain ⟨U, J, hU, hJ, hmap, hJzero, hchart⟩ := s4pv_actual_chart hκ
  let P : Set ℂ := A ∩ {t : ℂ | ‖t‖ * ‖ν‖ < 1}
  have hP : IsOpen P := hA.inter (isOpen_lt (continuous_norm.mul continuous_const) continuous_const)
  refine ⟨P, hP, ⟨hA₀, by simp⟩, fun e he => he.2, ?_⟩
  intro e he z hz hz₀ hp
  obtain ⟨y, hy, hJy⟩ := s4pv_chart_surjective hκ (fun x hx hp => (hchart x hx hp).2) hz hz₀
  have hyU : y ∈ U := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact (hchart x hx.1 hx.2).1
  have hJnz : deriv J y ^ 2 ≠ 0 := pow_ne_zero _ (hJzero y hyU)
  have hd := (((hhol y hy).differentiableAt (hA.mem_nhds he.1)).sub_const
    (schwarzianHol J y)).div_const (deriv J y ^ 2)
  have heB : e • ν ∈ LinfStarBall := by
    simpa [LinfStarBall, mem_ball_zero_iff, norm_smul] using he.2
  have hc₀ : ContinuousAt (fun p : LinfStar × ExtPlane => wAS p.1 p.2)
      (e • ν, (z : ExtPlane)) :=
    AppA.acc_wAS_cont.continuousAt
      ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨heB, mem_univ _⟩)
  have hc : ContinuousAt (fun t : ℂ => wAS (t • ν) (z : ExtPlane)) e :=
    hc₀.comp (f := fun t : ℂ => (t • ν, (z : ExtPlane)))
      ((continuous_id.smul continuous_const).continuousAt.prodMk continuousAt_const)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hP.mem_nhds he, hc.eventually_ne hp] with t ht htp
  have htB : t • ν ∈ LinfStarBall := by
    simpa [LinfStarBall, mem_ball_zero_iff, norm_smul] using ht.2
  have hC := s4pv_chart_schwarzian hκ hν ht.2 hJ hmap hJzero hchart hy
    ((hreg t ht.1).contDiffAt ((s4pv_plane_exterior_isOpen hκ).mem_nhds hy))
    (hn t ht.1 y hy) (by simpa only [hJy] using htp)
  rw [hJy] at hC
  obtain ⟨hwc, hwz, hwE⟩ := e41_w_regular hν ht.2 hz htp
  obtain ⟨hga, hgz⟩ := e41_g_holo (wA_mul hκ htB).1 hwE
  rw [← e41_schw_left hga hgz hwc hwz] at hC
  exact (eq_div_iff hJnz).2 (eq_sub_iff_add_eq.mpr hC)

end Ch2
end TakhtajanTeo
