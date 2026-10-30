import TakhtajanTeo.Ch1.GroupInverseLimit

/-!
# Uniform control at infinity for converging plane homeomorphisms

Compact-uniform convergence of the inverses bounds all sufficiently late
inverse images of a fixed closed ball by one radius.
-/

open Set Filter Topology Metric

namespace TakhtajanTeo

/-- Locally uniform convergence to a plane homeomorphism supplies a common
neighborhood of infinity mapped outside any prescribed positive-radius ball. -/
theorem kn6_uniform_proper
    {Fn : ℕ → (ℂ ≃ₜ ℂ)} {F : ℂ ≃ₜ ℂ}
    (hlim : TendstoLocallyUniformly (fun n => (Fn n : ℂ → ℂ))
      (F : ℂ → ℂ) atTop) :
    ∀ R : ℝ, 0 < R → ∃ S : ℝ, 0 < S ∧
      ∀ᶠ n in atTop, ∀ z : ℂ, S ≤ ‖z‖ → R < ‖Fn n z‖ := by
  intro R _hR
  have hK := isCompact_closedBall (0 : ℂ) R
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn F.symm.continuous.continuousOn
  have hinv := kn6_inverse_locallyUniform hlim
  have hunif := tendstoLocallyUniformly_iff_forall_isCompact.mp hinv _ hK
  refine ⟨|C| + 2, by positivity, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif 1 zero_lt_one] with n hn
  intro z hz
  by_contra hbad
  have hy : Fn n z ∈ closedBall (0 : ℂ) R := by
    simpa only [mem_closedBall, dist_zero_right] using (not_lt.mp hbad)
  have hbound := hC (Fn n z) hy
  have hdist := hn (Fn n z) hy
  simp only [Homeomorph.symm_apply_apply] at hdist
  have htri := dist_triangle (0 : ℂ) (F.symm (Fn n z)) z
  simp only [dist_zero_left] at htri
  linarith [le_abs_self C]

end TakhtajanTeo
