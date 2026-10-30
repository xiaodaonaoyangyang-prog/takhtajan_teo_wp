import TakhtajanTeo.Ch1.QCOneLimitEndpoint
import LiZhongQC.Ch01.S09_AnalyticProperties

/-! Holomorphy of locally uniform limits with distortion tending to one.
The local constant branch is retained, so no nondegeneracy assumption is needed.
This is the independent limit helper for the funded group chain. -/

open Complex Set Metric Filter Topology
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- A tail with distortion below K has the same locally uniform limit on a ball. -/
theorem kn6_limit_ball_qc {Fn : ℕ → ℂ → ℂ} {Kn : ℕ → ℝ} {F : ℂ → ℂ}
    (hqc : ∀ n, IsKQC (Fn n) univ (Kn n))
    (hKn : Tendsto Kn atTop (𝓝 1)) (hlim : TendstoLocallyUniformly Fn F atTop)
    (z : ℂ) (hnc : ¬ ∃ c : ℂ, ∀ w ∈ ball z 1, F w = c)
    {K : ℝ} (hK : 1 < K) : IsKQC F (ball z 1) K := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hKn.eventually_lt_const hK)
  have htail : ∀ n, IsKQC (Fn (n + N)) (ball z 1) K := by
    intro n
    exact ac_t_isKQC_restrict ((hqc (n + N)).mono (hN (n + N) (Nat.le_add_left N n)).le)
      isOpen_ball (subset_univ _)
  have hlocal : TendstoLocallyUniformlyOn Fn F atTop (ball z 1) :=
    hlim.tendstoLocallyUniformlyOn
  have hshift : TendstoLocallyUniformlyOn (fun n => Fn (n + N)) F atTop (ball z 1) := by
    intro u hu x hx
    obtain ⟨s, hs, H⟩ := hlocal u hu x hx
    exact ⟨s, hs, (tendsto_add_atTop_nat N).eventually H⟩
  rcases thm8_2_limit isBounded_ball (isConnected_ball (by norm_num : (0 : ℝ) < 1))
      htail hshift with hconstant | hF
  · exact False.elim (hnc hconstant)
  · exact hF

/-- The frozen group-chain target: a constant limit is allowed. -/
theorem ab_kn_one_limit {Fn : ℕ → ℂ → ℂ} {Kn : ℕ → ℝ} {F : ℂ → ℂ} {Kbar : ℝ}
    (hqc : ∀ n, IsKQC (Fn n) univ (Kn n))
    (hbound : ∀ n, Kn n ≤ Kbar)
    (hKn : Tendsto Kn atTop (𝓝 1))
    (hlim : TendstoLocallyUniformly Fn F atTop) : Differentiable ℂ F := by
  intro z
  have hz : z ∈ ball z (1 : ℝ) := mem_ball_self (by norm_num)
  by_cases hconstant : ∃ c : ℂ, ∀ w ∈ ball z 1, F w = c
  · obtain ⟨c, hc⟩ := hconstant
    have he : F =ᶠ[𝓝 z] (fun _ => c) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) hc
    exact (differentiableAt_const c).congr_of_eventuallyEq he
  · have hF : IsConformalOnto F (ball z 1) (F '' ball z 1) :=
      kn6_conformal_of_forall_gt (fun K hK => kn6_limit_ball_qc hqc hKn hlim z hconstant hK)
    exact hF.1.differentiableAt (isOpen_ball.mem_nhds hz)

/-- Nondegeneracy is imposed only for the conformal corollary. -/
theorem ab_kn_one_limit_conformal {Fn : ℕ → ℂ → ℂ} {Kn : ℕ → ℝ} {F : ℂ → ℂ} {Kbar : ℝ}
    (hqc : ∀ n, IsKQC (Fn n) univ (Kn n))
    (hbound : ∀ n, Kn n ≤ Kbar)
    (hKn : Tendsto Kn atTop (𝓝 1))
    (hlim : TendstoLocallyUniformly Fn F atTop) (hinj : Function.Injective F) :
    IsConformalOnto F univ (F '' univ) :=
  ⟨(ab_kn_one_limit hqc hbound hKn hlim).differentiableOn, hinj.injOn, rfl⟩

end TakhtajanTeo
