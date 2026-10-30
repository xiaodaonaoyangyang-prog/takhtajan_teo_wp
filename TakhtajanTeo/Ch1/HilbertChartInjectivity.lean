import TakhtajanTeo.Ch1.QCVariationSurjSmall

open Complex Set Metric
namespace TakhtajanTeo
open LiZhongQC QCV

theorem hbChart_injectiveOn {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    InjOn (fun φ : AInf unitDisc => bersPhi (beltramiMul (Lambda φ) μ))
      (ball 0 2) := by
  intro φ hφ ψ hψ heq
  obtain ⟨hΛφ,hBφ⟩ := qs_AW (mem_ball_zero_iff.mp hφ)
  obtain ⟨hΛψ,hBψ⟩ := qs_AW (mem_ball_zero_iff.mp hψ)
  obtain ⟨_,_,hμi,_,_⟩ := bc_wA_mul hμ hμ
  have he := qs_bersPhi_mul_congr (bg_mul_mem_ball hμ hΛφ)
    (bg_mul_mem_ball hμ hΛψ) hμi heq
  calc
    φ = bersPhi (Lambda φ) := hBφ.symm
    _ = bersPhi (beltramiMul (beltramiMul (Lambda φ) μ) (beltramiInv μ)) :=
      (qs_bersPhi_mul_inv hΛφ hμ).symm
    _ = bersPhi (beltramiMul (beltramiMul (Lambda ψ) μ) (beltramiInv μ)) := he
    _ = bersPhi (Lambda ψ) := qs_bersPhi_mul_inv hΛψ hμ
    _ = ψ := hBψ

end TakhtajanTeo
