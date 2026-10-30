import TakhtajanTeo.Ch1.HilbertChartRegularity
import TakhtajanTeo.Ch1.HilbertBersSurjection
import TakhtajanTeo.Ch1.HilbertInjectiveSubmersion

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Real
namespace TakhtajanTeo
open LiZhongQC

theorem hbAll_chart_injOn (μ : LinfStarBall) :
    InjOn (hib_chart μ) (ball (0 : A2 unitDisc) (Real.sqrt (π/3))) := by
  intro x hx y hy he
  have hxval := ctb_A2toAInf_toA2 ((hcr_chart_regular μ).1 x hx)
  have hyval := ctb_A2toAInf_toA2 ((hcr_chart_regular μ).1 y hy)
  have he' := congrArg A2toAInf he
  change A2toAInf (toA2 unitDisc (AInf.toFun (bers (bersChartInv μ (A2toAInf x))-bersPhi μ))) =
    A2toAInf (toA2 unitDisc (AInf.toFun (bers (bersChartInv μ (A2toAInf y))-bersPhi μ))) at he'
  rw [hxval,hyval] at he'
  have hB : bers (bersChartInv μ (A2toAInf x)) =
      bers (bersChartInv μ (A2toAInf y)) := by
    simpa only [sub_add_cancel] using congrArg (fun v => v + bersPhi μ) he'
  apply A2toAInf_injective
  exact ba_injOn μ (mem_ball_zero_iff.mpr (ct_A2toAInf_norm_lt hx))
    (mem_ball_zero_iff.mpr (ct_A2toAInf_norm_lt hy)) (bers_injective hB)

theorem hbAll_bijective (μ : LinfStarBall) : Function.Bijective (hbL2_bersOperator μ) := by
  have honto := hbSurj_bersOperator μ
  refine ⟨his_injective_of_surjective (hcr_chart_strict_zero μ) honto
    (ball_mem_nhds _ (by positivity)) (hbAll_chart_injOn μ), honto⟩

theorem hbAll_thm_2_3 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ C C' : ℝ,
      (∀ ν ∈ harmonicL2 unitDiscExterior, AInf.toFun (D0BersR μ (toLinf ν)) ∈ A2fun unitDisc ∧
        normA2 unitDisc (AInf.toFun (D0BersR μ (toLinf ν))) ≤ ENNReal.ofReal C * normL2 unitDiscExterior ν) ∧
      (∀ ν₁ ∈ harmonicL2 unitDiscExterior, ∀ ν₂ ∈ harmonicL2 unitDiscExterior,
        D0BersR μ (toLinf ν₁) = D0BersR μ (toLinf ν₂) → EqOn ν₁ ν₂ unitDiscExterior) ∧
      ∀ φ ∈ A2fun unitDisc, ∃ ν ∈ harmonicL2 unitDiscExterior,
        (∀ z ∈ unitDisc, AInf.toFun (D0BersR μ (toLinf ν)) z = φ z) ∧
        normL2 unitDiscExterior ν ≤ ENNReal.ofReal C' * normA2 unitDisc φ := by
  exact hbL2_thm_2_3_of_bijective ⟨μ,hμ⟩ (hbAll_bijective ⟨μ,hμ⟩)

end TakhtajanTeo
