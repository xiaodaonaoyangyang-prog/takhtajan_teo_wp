import TakhtajanTeo.Ch1.PeriodicDiskCover

/-! Generic QC exponential descent and boundary continuity. No Appendix
module is imported, so the interface is reusable by symmetric-boundary work. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem periodicDiskMap_isKQC {f : ℂ → ℂ} {K : ℝ}
    (hf : IsKQC f upperHalf K)
    (hp : ∀ z : ℂ, ∀ n : ℤ, f (z + n) = f z + n) :
    IsKQC (periodicDiskMap f) (unitDisc \ {0}) K := by
  have hΩ : IsOpen (unitDisc \ ({0} : Set ℂ)) := isOpen_ball.sdiff isClosed_singleton
  apply s23_lg hΩ hf.2.1 (periodicDiskMap_injOn hp hf.2.2.1.2.1)
  intro w hw
  rw [← diskCover_image] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  let U : Set ℂ := (upperHalf ∩ ball z (1 / 3)) ∩ f ⁻¹' ball (f z) (1 / 3)
  have hUo : IsOpen U :=
    (hf.2.2.1.1.mono inter_subset_left).isOpen_inter_preimage
      (isOpen_upperHalf.inter isOpen_ball) isOpen_ball
  have hzU : z ∈ U := ⟨⟨hz, mem_ball_self (by norm_num)⟩, mem_ball_self (by norm_num)⟩
  have hUH : U ⊆ upperHalf := fun _ hx => hx.1.1
  have hUi : InjOn diskCover U := (diskCover_injOn_ball z).mono (fun _ hx => hx.1.2)
  have hc : IsConformalOnto diskCover U (diskCover '' U) :=
    ⟨diskCover_differentiable.differentiableOn, hUi, rfl⟩
  have hVo := hc.isOpen hUo
  refine ⟨diskCover '' U, hVo, mem_image_of_mem _ hzU, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (diskCover_mem _).mpr (hUH hx)
  · have hi := hc.symm hUo
    have hσ : IsKQC (Function.invFunOn diskCover U) (diskCover '' U) 1 :=
      isKQC_one_of_conformal hVo hi
    have hfU := nx_isKQC_restrict hf hUo hUH
    have hfUo := isOpen_image_of_isKQC hfU
    have hcp : IsConformalOnto diskCover (f '' U) (diskCover '' (f '' U)) := by
      refine ⟨diskCover_differentiable.differentiableOn, (diskCover_injOn_ball (f z)).mono ?_, rfl⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    have hπ := isKQC_one_of_conformal hfUo hcp
    have h₂ := thm7_1_comp hσ hfU (by rw [hi.2.2])
    have h₃ := thm7_1_comp h₂ hπ (by rw [image_comp, hi.2.2])
    rw [one_mul, mul_one] at h₃
    apply ad_isKQC_congr h₃
    rintro y ⟨x, hx, rfl⟩
    simp only [Function.comp_apply]
    rw [hUi.leftInvOn_invFunOn hx]
    exact periodicDiskMap_cover hp x

theorem periodicDiskMap_continuousAt_ne_zero {f : ℂ → ℂ} (hf : Continuous f)
    (hp : ∀ z : ℂ, ∀ n : ℤ, f (z + n) = f z + n)
    {w : ℂ} (hw : w ≠ 0) : ContinuousAt (periodicDiskMap f) w := by
  let z := diskCoverLog w
  let U := ball z (1 / 3)
  have hUi : InjOn diskCover U := diskCover_injOn_ball z
  have hc : IsConformalOnto diskCover U (diskCover '' U) :=
    ⟨diskCover_differentiable.differentiableOn, hUi, rfl⟩
  have hVo := hc.isOpen isOpen_ball
  have hi := hc.symm isOpen_ball
  have hwV : w ∈ diskCover '' U := ⟨z, mem_ball_self (by norm_num), diskCover_log hw⟩
  have hcont : ContinuousOn (diskCover ∘ f ∘ Function.invFunOn diskCover U) (diskCover '' U) :=
    (diskCover_differentiable.continuous.comp hf).comp_continuousOn hi.1.continuousOn
  have he : EqOn (periodicDiskMap f) (diskCover ∘ f ∘ Function.invFunOn diskCover U) (diskCover '' U) := by
    rintro y ⟨x, hx, rfl⟩
    simp only [Function.comp_apply]
    rw [hUi.leftInvOn_invFunOn hx]
    exact periodicDiskMap_cover hp x
  exact ((hcont.congr he) w hwV).continuousAt (hVo.mem_nhds hwV)

theorem beurlingAhlfors_disk_boundary {h : ℂ → ℂ} {u : ℝ → ℝ}
    (hu : GardinerLakic2000.IsCircleLift h u) :
    EqOn (periodicDiskMap (beurlingAhlfors u 1)) h unitCircle := by
  obtain ⟨hc, hm, -, -, hp, he⟩ := hu
  intro z hz
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective (⟨z, mem_sphere_zero_iff_norm.mpr hz⟩ : Circle)
  have hθ' : exp ((θ : ℂ) * I) = z := by
    simpa only [Circle.coe_exp] using congrArg (fun ζ : Circle => (ζ : ℂ)) hθ
  let t : ℝ := θ / (2 * π)
  have ht : diskCover (t : ℂ) = z := by
    rw [diskCover]
    have hcθ : (2 * π * I : ℂ) * (t : ℂ) = (θ : ℂ) * I := by
      dsimp [t]
      push_cast
      field_simp
    rw [hcθ, hθ']
  rw [← ht, periodicDiskMap_cover (beurlingAhlfors_add_int hc hp 1), ba_f1h_real]
  exact he t

end TakhtajanTeo

#print axioms TakhtajanTeo.periodicDiskMap_isKQC
#print axioms TakhtajanTeo.periodicDiskMap_continuousAt_ne_zero
#print axioms TakhtajanTeo.beurlingAhlfors_disk_boundary
