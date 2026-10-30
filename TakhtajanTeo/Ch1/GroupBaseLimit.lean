import TakhtajanTeo.Ch1.GroupBaseChart
import TakhtajanTeo.Ch1.GroupBaseDensity
import TakhtajanTeo.Ch1.GroupBaseTransition
import TakhtajanTeo.Ch1.GroupTransitionLimit

/-! Convergence of the origin density from the normalized AW charts. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem grp25b_normalized_tendsto {Fn : ℕ → ℂ → ℂ} {Kn : ℕ → ℝ} {Kbar : ℝ}
    (hqc : ∀ n, IsKQC (Fn n) univ (Kn n)) (hbound : ∀ n, Kn n ≤ Kbar)
    (hnorm : ∀ n, Fn n '' univ = univ ∧ Fn n 0 = 0 ∧ Fn n 1 = 1)
    (hKn : Tendsto Kn atTop (𝓝 1)) : TendstoLocallyUniformly Fn id atTop := by
  let f : ℕ → C(ℂ, ℂ) := fun n => ⟨Fn n, continuousOn_univ.mp (hqc n).2.2.1.1⟩
  have hh : Tendsto f atTop (𝓝 (ContinuousMap.id ℂ)) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, -, hms⟩ := grp25b_normalized_subseq (fun n => hqc (ns n))
      (fun n => hbound (ns n)) (fun n => hnorm (ns n)) (hKn.comp hns)
    exact ⟨ms, ContinuousMap.tendsto_of_tendstoLocallyUniformly hms⟩
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hh

theorem grp25b_density_limit {μ : ℕ → LinfStar} (hμ : ∀ n, μ n ∈ LinfStarBall)
    {F W : ℕ → (ℂ ≃ₜ ℂ)} {τ ψ : ℕ → ℂ → ℂ}
    (hF0 : ∀ n, F n 0 = 0)
    (hW : ∀ n, IsNormalizedSolution (W n : ℂ → ℂ) (extA (μ n)))
    (hψ : ∀ n, IsConformalOnto (ψ n) (F n '' unitDiscExterior) (W n '' unitDiscExterior))
    (hrel : ∀ n z, z ∈ unitDiscExterior → W n z = ψ n (F n z))
    (hτcd : ∀ n, ContDiffAt ℝ 1 (τ n) 0) (hτ0 : ∀ n, τ n 0 = 0)
    (hτrel : ∀ n, ∀ᶠ t in 𝓝[≠] (0 : ℂ), τ n t = (F n t⁻¹)⁻¹)
    (hFlim : TendstoLocallyUniformly (fun n => (F n : ℂ → ℂ)) id atTop)
    (hWlim : TendstoLocallyUniformly (fun n => (W n : ℂ → ℂ)) id atTop)
    (hτlim : Tendsto (fun n => dz (τ n) 0) atTop (𝓝 1)) :
    Tendsto (fun n => ‖dz (wA (μ n)) 0‖ ^ 2 / (1 - ‖wA (μ n) 0‖ ^ 2) ^ 2)
      atTop (𝓝 1) := by
  let ξ : ℕ → ℂ → ℂ := fun n t => (W n ((F n).symm t⁻¹))⁻¹
  have hbound := grp25b_eventually_disc_bound hFlim
  have hdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (ξ n) (ball 0 (1 / 3)) := by
    filter_upwards [hbound] with n hn
    exact grp25b_transition_analytic (F n) (W n) (hF0 n) (hW n).2.2.1 (hψ n) (hrel n) hn
  have hξlim : TendstoLocallyUniformlyOn ξ id atTop (ball (0 : ℂ) (1 / 3) \ {0}) :=
    (grp_transition_reciprocal_tendsto hFlim hWlim).mono (fun _ hx => hx.2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdiff
  have htail : TendstoLocallyUniformlyOn (fun n => ξ (n + N)) id atTop
      (ball (0 : ℂ) (1 / 3) \ {0}) := by
    intro u hu x hx
    obtain ⟨s, hs, hh⟩ := hξlim u hu x hx
    exact ⟨s, hs, (tendsto_add_atTop_nat N).eventually hh⟩
  have hder : Tendsto (fun n => deriv (ξ n) 0) atTop (𝓝 (1 : ℂ)) := by
    apply (tendsto_add_atTop_iff_nat N).mp
    simpa using grp25h_deriv_center (by norm_num : (0 : ℝ) < 1 / 3)
      (fun n => hN (n + N) (Nat.le_add_left N n)) differentiableOn_id htail
  have hpoint : ∀ᶠ n in atTop, ContDiffAt ℝ 1 (W n : ℂ → ℂ) 0 ∧
      dz (W n : ℂ → ℂ) 0 = conj (deriv (ξ n) 0 * dz (τ n) 0) := by
    filter_upwards [hdiff] with n hn
    exact grp25b_transition_dz (F n) (W n) (hF0 n) (hW n) (hτcd n) (hτ0 n) (hτrel n)
      (hn.analyticOnNhd isOpen_ball 0 (mem_ball_self (by norm_num)))
  have hWdz : Tendsto (fun n => dz (W n : ℂ → ℂ) 0) atTop (𝓝 (1 : ℂ)) := by
    have hh := (Complex.continuous_conj.tendsto (1 * 1)).comp (hder.mul hτlim)
    have hh' : Tendsto (fun n => conj (deriv (ξ n) 0 * dz (τ n) 0)) atTop (𝓝 (1 : ℂ)) := by
      simpa only [Function.comp_def, mul_one, map_one] using hh
    exact hh'.congr' (hpoint.mono (fun n hn => hn.2.symm))
  have hnorm : Tendsto (fun n => ‖dz (W n : ℂ → ℂ) 0‖ ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa using hWdz.norm.pow 2
  exact hnorm.congr' (hpoint.mono (fun n hn =>
    (grp25b_normalized_density (hμ n) (hW n) hn.1).symm))

end TakhtajanTeo

#print axioms TakhtajanTeo.grp25b_density_limit
#print axioms TakhtajanTeo.grp25b_normalized_tendsto
