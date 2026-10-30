import TakhtajanTeo.Appendix.CompactBergmanKernel
import TakhtajanTeo.Ch2.S1_SymmetricT

/-! # Compact period matrices have symmetric boundary values

The compact-to-symmetric direction of B.4 follows from proved compact
dilation convergence and closedness of weighted boundary decay.
No use of the open B.4 or B.9 declarations.
-/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

-- C1
theorem pcs_decay_of_uniform {f : ℂ → ℂ} {g : ℕ → ℂ → ℂ}
    (hg : ∀ n, Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * g n z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0))
    (hlim : Tendsto (fun n => ⨆ z ∈ unitDisc,
      ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖g n z - f z‖)) atTop (𝓝 0)) :
    Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * f z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε2))).exists
  have hsmall := Metric.tendsto_nhds.mp (hg n) (ε / 2) hε2
  have hdisk : ∀ᶠ z : ℂ in comap (fun z : ℂ => ‖z‖) (𝓝[<] (1 : ℝ)), ‖z‖ < 1 :=
    tendsto_comap.eventually self_mem_nhdsWithin
  filter_upwards [hsmall, hdisk] with z hz hzd
  simp only [dist_zero_right] at hz ⊢
  have he : (1 - ‖z‖ ^ 2) ^ 2 * ‖g n z - f z‖ < ε / 2 := by
    apply (ENNReal.ofReal_lt_ofReal_iff hε2).mp
    refine lt_of_le_of_lt ?_ hn
    apply le_iSup_of_le z
    change ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖g n z - f z‖) ≤
      ⨆ (_ : z ∈ ball (0 : ℂ) 1), ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖g n z - f z‖)
    exact le_iSup_of_le (mem_ball_zero_iff.mpr hzd) le_rfl
  have hw : ‖((1 - ‖z‖ ^ 2) ^ 2 : ℂ)‖ = (1 - ‖z‖ ^ 2) ^ 2 := by
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have herr : ‖((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * f z -
      ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * g n z‖ < ε / 2 := by
    rw [← mul_sub, norm_mul, hw, norm_sub_rev]
    exact he
  exact (norm_le_norm_sub_add _ _).trans_lt (by linarith)

-- C2
theorem pcs_compact_symmetric {p : T1} (hK : IsCompactMat (periodP p)) :
    p ∈ symmetricT := by
  apply (symt_iff_schwarzian_decay p).mpr
  let μ : LinfStarBall := Quotient.out p
  have hpair := b8_welding_normalized_pair μ.2
  have hf : IsUnivalentDisc (fsans μ) := ⟨hpair.1, hpair.2.1⟩
  have hh := pcs_decay_of_uniform
    (g := fun n => schwarzianHol (dilateF (fsans μ) (n + 1)))
    (fun n => dilateF_schwarzian_boundary hf (by omega : 1 ≤ n + 1))
    ((remark_B_9_of_compact hK).1.comp (tendsto_add_atTop_nat 1))
  simpa only [b1_fsans_eq μ.2, μ] using hh

end AppB
end TakhtajanTeo
