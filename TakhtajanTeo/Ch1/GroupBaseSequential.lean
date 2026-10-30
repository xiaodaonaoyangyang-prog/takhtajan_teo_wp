import TakhtajanTeo.Ch1.GroupOrigin
import Mathlib.Analysis.SpecificLimits.Basic

/-! The sequential reduction for the remaining origin density estimate. -/
open Complex Set Filter Topology Metric
open scoped Real
namespace TakhtajanTeo
open LiZhongQC

/-- The actual sequence limit implies the quantified origin bound. The sequence-limit
hypothesis is explicit until the normalized-chart proof supplies it. -/
theorem grp25_base_of_sequences
    (hseq : ∀ μ : ℕ → LinfStar,
      (∀ n, μ n ∈ harmonicBeltrami ∧ ‖μ n‖ < 1) →
      Tendsto (fun n => ‖μ n‖) atTop (𝓝 0) →
      Tendsto (fun n => ‖dz (wA (μ n)) 0‖ ^ 2 /
        (1 - ‖wA (μ n) 0‖ ^ 2) ^ 2) atTop (𝓝 1)) :
    ∀ ε > 0, ∃ δ > 0, ∀ μ ∈ harmonicBeltrami, ‖μ‖ < δ →
      |‖dz (wA μ) 0‖ ^ 2 / (1 - ‖wA μ 0‖ ^ 2) ^ 2 - 1| < ε := by
  intro ε hε
  by_contra h
  push_neg at h
  choose μ hμ hm hb using fun n : ℕ =>
    h ((1/2 : ℝ) * (1 / ((n : ℝ) + 1))) (by positivity)
  have hball : ∀ n, ‖μ n‖ < 1 := by
    intro n
    have hfrac : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have := hm n
    linarith
  have hlim : Tendsto (fun n => ‖μ n‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => (hm n).le)
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1/2 : ℝ)
  have he := Metric.tendsto_nhds.mp (hseq μ (fun n => ⟨hμ n, hball n⟩) hlim) ε hε
  obtain ⟨n, hn⟩ := he.exists
  have hn' : |‖dz (wA (μ n)) 0‖ ^ 2 / (1 - ‖wA (μ n) 0‖ ^ 2) ^ 2 - 1| < ε := by
    simpa only [Real.dist_eq] using hn
  exact (not_lt_of_ge (hb n)) hn'

end TakhtajanTeo
