import TakhtajanTeo.Ch1.GroupCov

/-! The S4 disk reduction, with the still-open origin inputs explicit. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Covariance transports origin regularity and the origin estimate to the whole disk.
This is conditional on S1/S3, and does not close the original Lemma 2.5. -/
theorem grp25_disc_of_origin {ε δ : ℝ} (hδ1 : δ ≤ 1)
    (hreg0 : ∀ μ ∈ harmonicBeltrami, ‖μ‖ < δ → ContDiffAt ℝ 1 (wA μ) 0)
    (hbase : ∀ μ ∈ harmonicBeltrami, ‖μ‖ < δ →
      |‖dz (wA μ) 0‖ ^ 2 / (1 - ‖wA μ 0‖ ^ 2) ^ 2 - 1| < ε) :
    ∀ μ ∈ harmonicBeltrami, ‖μ‖ < δ → ∀ z ∈ unitDisc,
      ContDiffAt ℝ 1 (wA μ) z ∧
      |‖dz (wA μ) z‖ ^ 2 / (1 - ‖wA μ z‖ ^ 2) ^ 2 -
        1 / (1 - ‖z‖ ^ 2) ^ 2| < ε / (1 - ‖z‖ ^ 2) ^ 2 := by
  intro μ hμ hμδ z hz
  obtain ⟨ν, hν, hn, hcov⟩ := grp25_cov hμ (hμδ.trans_le hδ1) hz
  have hνδ := hn.trans_lt hμδ
  obtain ⟨hreg, he⟩ := hcov (hreg0 ν hν hνδ)
  refine ⟨hreg, ?_⟩
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hq : 0 < (1 - ‖z‖ ^ 2) ^ 2 := by
    have : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    positivity
  have hb := hbase ν hν hνδ
  rw [← he] at hb
  have heq :
      ‖dz (wA μ) z‖ ^ 2 / (1 - ‖wA μ z‖ ^ 2) ^ 2 - 1 / (1 - ‖z‖ ^ 2) ^ 2 =
      (‖dz (wA μ) z‖ ^ 2 / (1 - ‖wA μ z‖ ^ 2) ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 - 1) /
        (1 - ‖z‖ ^ 2) ^ 2 := by
    rw [sub_div, mul_div_cancel_right₀ _ (ne_of_gt hq)]
  rw [heq, abs_div, abs_of_pos hq]
  exact (div_lt_div_iff_of_pos_right hq).mpr hb

end TakhtajanTeo
