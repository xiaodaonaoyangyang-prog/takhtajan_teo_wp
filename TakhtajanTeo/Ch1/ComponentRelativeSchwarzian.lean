import TakhtajanTeo.Ch1.HilbertBersSurjection
import TakhtajanTeo.Ch1.ComponentTB

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual conformal transition between the two interior welding domains. -/
def crs_transition (μ ν : LinfStar) : ℂ → ℂ :=
  fsans ν ∘ Function.invFunOn (fsans μ) unitDisc

theorem crs_conformal {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hν : ν ∈ LinfStarBall) :
    IsConformalOnto (crs_transition μ ν) (fsans μ '' unitDisc)
      (fsans ν '' unitDisc) :=
  (S2C.s2c_conf_f hν).comp ((S2C.s2c_conf_f hμ).symm isOpen_ball)

/-- The physical relative Schwarzian pulls back to the actual Bers difference. -/
theorem crs_schwarzian_pullback {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hν : ν ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDisc) :
    schwarzianHol (crs_transition μ ν) (fsans μ w) * deriv (fsans μ) w ^ 2 =
      AInf.toFun (bersPhi ν - bersPhi μ) w := by
  have hf := S2C.s2c_conf_f hμ
  have hF := crs_conformal hμ hν
  have hΩ := hf.isOpen isOpen_ball
  have hwΩ : fsans μ w ∈ fsans μ '' unitDisc := ⟨w, hw, rfl⟩
  have hfa := hf.1.analyticAt (isOpen_ball.mem_nhds hw)
  have hFa := hF.1.analyticAt (hΩ.mem_nhds hwΩ)
  have hdf := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hw
  have hdF := deriv_ne_zero_of_injOn hΩ hF.1 hF.2.1 hwΩ
  have hchain := eq19_1_chain_rule hfa hdf hFa hdF
  rw [schwarzian_of_analyticAt (hFa.comp hfa),
    schwarzian_of_analyticAt hFa, schwarzian_of_analyticAt hfa] at hchain
  have he : (crs_transition μ ν ∘ fsans μ) =ᶠ[𝓝 w] fsans ν := by
    filter_upwards [isOpen_ball.mem_nhds hw] with z hz
    change fsans ν (Function.invFunOn (fsans μ) unitDisc (fsans μ z)) = fsans ν z
    rw [hf.2.1.leftInvOn_invFunOn hz]
  rw [schwarzianHol_congr he] at hchain
  rw [ctb_toFun_sub, Pi.sub_apply, (bersPhi_spec hν).1 w hw,
    (bersPhi_spec hμ).1 w hw, ← S2C.s2c_fsans_eq hν, ← S2C.s2c_fsans_eq hμ]
  exact eq_sub_of_add_eq hchain.symm

/-- An affine A2 difference gives finite energy of the actual nonlinear
transition's Schwarzian, not merely of a linearized preimage. -/
theorem crs_schwarzian_energy {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc) :
    (∫⁻ v in fsans μ '' unitDisc,
      ENNReal.ofReal (‖schwarzianHol (crs_transition μ ν) v‖ ^ 2 /
        poincareDensity (fsans μ '' unitDisc) v ^ 2)) < ∞ := by
  obtain ⟨q, _, hq, hm⟩ := hbSurj_target hμ hP
  have hf := S2C.s2c_conf_f hμ
  have he : EqOn q (schwarzianHol (crs_transition μ ν)) (fsans μ '' unitDisc) := by
    rintro v ⟨w, hw, rfl⟩
    have hd := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hw
    exact mul_right_cancel₀ (pow_ne_zero 2 hd)
      ((hq w hw).trans (crs_schwarzian_pullback hμ hν hw).symm)
  have hi := setLIntegral_congr_fun (μ := volume) (hf.isOpen isOpen_ball).measurableSet
    (fun v hv => congrArg (fun a : ℂ => ENNReal.ofReal
      (‖a‖ ^ 2 / poincareDensity (fsans μ '' unitDisc) v ^ 2)) (he hv))
  rwa [← hi]

end TakhtajanTeo
