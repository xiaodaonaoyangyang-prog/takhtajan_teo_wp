import TakhtajanTeo.Ch2.S4HolomorphicTransport
import TakhtajanTeo.Ch2.S4HolomorphicVariation

/-! # Actual holomorphic derivative in the normalized plane chart (`s4hv_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- H20
theorem s4hv_welded_chart_derivative {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami)
    {U : Set ℂ} {J : ℂ → ℂ} (hJ : AnalyticOnNhd ℂ J U)
    (hmap : MapsTo J U unitDiscExterior) (hJzero : ∀ y ∈ U, deriv J y ≠ 0)
    (hchart : ∀ x ∈ unitDiscExterior, wAS κ (x : ExtPlane) ≠ extInf →
      qcv_planeSolution κ x ∈ U ∧ J (qcv_planeSolution κ x) = wA κ x)
    {y : ℂ} (hy : y ∈ qcv_planeSolution κ ''
      {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}) :
    HasDerivAt (fun e : ℂ => schwarzianDz
      (gsans (beltramiMul (e • ν) κ) ∘ wA (e • ν)) (J y))
      (dz (dz (dz (ahVar (ahT_dot (extB (qcv_rightDerivative κ ν))
        (extB κ) (qcv_planeSolution κ))))) y / deriv J y ^ 2) 0 := by
  have hyU : y ∈ U := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact (hchart x hx.1 hx.2).1
  have hz : J y ∈ unitDiscExterior := hmap hyU
  have hJnz : deriv J y ^ 2 ≠ 0 := pow_ne_zero _ (hJzero y hyU)
  obtain ⟨P, hP, hP₀, hreg, -, hn, -⟩ := s4pv_plane_transition_regular hκ hν
  have hsmall : ∀ᶠ e : ℂ in 𝓝 0, ‖e‖ * ‖ν‖ < 1 :=
    (continuous_norm.mul continuous_const).continuousAt.eventually_lt continuousAt_const (by simp)
  have hd := ((s4hv_plane_transition_derivative hκ hν hy).sub_const
    (schwarzianHol J y)).div_const (deriv J y ^ 2)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hP.mem_nhds hP₀, hsmall, s4ma_pole_absent_eventually ν (J y)] with e he he₁ hp
  have heB : e • ν ∈ LinfStarBall := by
    simpa [LinfStarBall, mem_ball_zero_iff, norm_smul] using he₁
  have hC := s4pv_chart_schwarzian hκ hν he₁ hJ hmap hJzero hchart hy
    ((hreg e he).contDiffAt ((s4pv_plane_exterior_isOpen hκ).mem_nhds hy))
    (hn e he y hy) hp
  obtain ⟨hwc, hwz, hwE⟩ := e41_w_regular hν he₁ hz hp
  obtain ⟨hga, hgz⟩ := e41_g_holo (wA_mul hκ heB).1 hwE
  rw [← e41_schw_left hga hgz hwc hwz] at hC
  exact (eq_div_iff hJnz).2 (eq_sub_iff_add_eq.mpr hC)

-- H21
theorem s4hv_lieTheta_chart {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior)
    {U : Set ℂ} {J : ℂ → ℂ} (hJ : AnalyticOnNhd ℂ J U)
    (hmap : MapsTo J U unitDiscExterior) (hJzero : ∀ y ∈ U, deriv J y ≠ 0)
    (hchart : ∀ x ∈ unitDiscExterior, wAS κ (x : ExtPlane) ≠ extInf →
      qcv_planeSolution κ x ∈ U ∧ J (qcv_planeSolution κ x) = wA κ x)
    {y : ℂ} (hy : y ∈ qcv_planeSolution κ ''
      {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}) :
    lieTheta κ ν (J y) =
      dz (dz (dz (ahVar (ahT_dot (extB (qcv_rightDerivative κ (toLinf ν)))
        (extB κ) (qcv_planeSolution κ))))) y / deriv J y ^ 2 -
        dz (dz (dz (ahVar (extB (toLinf ν))))) (J y) := by
  have hyU : y ∈ U := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact (hchart x hx.1 hx.2).1
  have hz : J y ∈ unitDiscExterior := hmap hyU
  have hνh : toLinf ν ∈ harmonicBeltrami := (harmonicL2_subset_harmonic.choose_spec ν hν).1
  rw [s4hv_lieTheta_split hκ hν hz,
    (s4hv_welded_chart_derivative hκ hνh hJ hmap hJzero hchart hy).deriv,
    s4hv_wA_holomorphic_variation hνh hz]

end Ch2
end TakhtajanTeo
