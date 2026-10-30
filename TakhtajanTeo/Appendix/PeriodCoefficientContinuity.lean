import TakhtajanTeo.Appendix.CompactBergmanKernel

/-! # Operator-norm continuity of the actual period matrix in Beltrami coefficients -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

-- N1
theorem pcc_entries {μ δ : LinfStar} {U : Set ℂ} (hU : IsOpen U)
    (hmem : ∀ t ∈ U, μ + t • δ ∈ LinfStarBall) (m n : ℕ) :
    DifferentiableOn ℂ (fun t => B1 (grunsky (fsans (μ + t • δ)) (gsans (μ + t • δ))) m n) U := by
  intro t ht
  obtain ⟨r, hr, _, hd⟩ := b1_entries (hmem t ht)
  exact ((hd m n).differentiableAt (ball_mem_nhds t (by linarith))).differentiableWithinAt

-- N2
theorem pcc_local_bound {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hsmall : ‖ν - μ‖ < (1 - ‖μ‖) / 2) :
    matOpNorm (fun m n => B1 (grunsky (fsans ν) (gsans ν)) m n -
      B1 (grunsky (fsans μ) (gsans μ)) m n) ≤
        ENNReal.ofReal (4 * ‖ν - μ‖ / (1 - ‖μ‖)) := by
  have hμ1 : ‖μ‖ < 1 := mem_ball_zero_iff.mp hμ
  by_cases he : ν = μ
  · subst ν
    simp only [sub_self, norm_zero, mul_zero, zero_div, ENNReal.ofReal_zero]
    exact matOpNorm_zero.le
  let δ := ν - μ
  have hd0 : 0 < ‖δ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  let R := (1 - ‖μ‖) / (2 * ‖δ‖)
  have hR : 1 < R := by
    rw [show R = (1 - ‖μ‖) / (2 * ‖ν - μ‖) from rfl, lt_div_iff₀ (by positivity)]
    linarith
  have hmem : ∀ t ∈ ball (0 : ℂ) R, μ + t • δ ∈ LinfStarBall := by
    intro t ht
    have ht' : ‖t‖ < R := mem_ball_zero_iff.mp ht
    have hp : ‖t‖ * (2 * ‖δ‖) < 1 - ‖μ‖ :=
      (lt_div_iff₀ (by positivity)).mp ht'
    apply mem_ball_zero_iff.mpr
    calc ‖μ + t • δ‖ ≤ ‖μ‖ + ‖t • δ‖ := norm_add_le _ _
      _ = ‖μ‖ + ‖t‖ * ‖δ‖ := by rw [norm_smul]
      _ < 1 := by nlinarith [norm_nonneg t]
  let B : ℂ → ℕ → ℕ → ℂ := fun t => B1 (grunsky (fsans (μ + t • δ)) (gsans (μ + t • δ)))
  have hB : ∀ t ∈ ball (0 : ℂ) R, FinBil (B t) 1 := fun t ht =>
    b1_finBil_of_contractive (b8_pair_model (b8_welding_normalized_pair (hmem t ht))).2.2.1
  have hB0 : B 0 = B1 (grunsky (fsans μ) (gsans μ)) := by simp [B]
  have hB1 : B 1 = B1 (grunsky (fsans ν) (gsans ν)) := by simp [B, δ]
  have hK : 0 ≤ 4 * ‖ν - μ‖ / (1 - ‖μ‖) := by positivity
  apply (b1_finBil_bounded hK ?_).2
  intro X Y x y
  let φ : ℂ → ℂ := fun t => ∑ m ∈ Y, ∑ n ∈ X, y m * B t m n * x n
  let M := Real.sqrt (∑ n ∈ X, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Y, ‖y m‖ ^ 2)
  have hφd : DifferentiableOn ℂ φ (ball 0 R) := by
    apply DifferentiableOn.fun_sum
    intro m _
    apply DifferentiableOn.fun_sum
    intro n _
    exact ((pcc_entries isOpen_ball hmem m n).const_mul (y m)).mul_const (x n)
  have hφb : ∀ t ∈ ball (0 : ℂ) R, ‖φ t‖ ≤ M := by
    intro t ht
    simpa only [one_mul] using hB t ht X Y x y
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self (by linarith)
  have hmaps : MapsTo φ (ball 0 R) (closedBall (φ 0) (2 * M)) := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hφb t ht, hφb 0 hzero])
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hφd hmaps
    (show (1 : ℂ) ∈ ball 0 R by simpa only [mem_ball_zero_iff, norm_one] using hR)
  rw [dist_eq_norm, dist_zero_right, norm_one, mul_one] at hs
  have hsum : (∑ m ∈ Y, ∑ n ∈ X, y m *
      (B1 (grunsky (fsans ν) (gsans ν)) m n - B1 (grunsky (fsans μ) (gsans μ)) m n) * x n) =
      φ 1 - φ 0 := by
    simp only [φ, ← hB1, ← hB0, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsum]
  apply hs.trans_eq
  dsimp [R, M, δ]
  field_simp
  <;> ring

-- N3
theorem pcc_tendsto {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {ν : ℕ → LinfStar}
    (hν : Tendsto ν atTop (𝓝 μ)) :
    Tendsto (fun k => matOpNorm (fun m n =>
      B1 (grunsky (fsans (ν k)) (gsans (ν k))) m n -
      B1 (grunsky (fsans μ) (gsans μ)) m n)) atTop (𝓝 0) := by
  have hd : Tendsto (fun k => ‖ν k - μ‖) atTop (𝓝 0) := by
    simpa using (hν.sub_const μ).norm
  have hp : 0 < (1 - ‖μ‖) / 2 := by
    have := mem_ball_zero_iff.mp hμ
    positivity
  have hh : Tendsto (fun k => ENNReal.ofReal (4 * ‖ν k - μ‖ / (1 - ‖μ‖))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal ((hd.const_mul 4).div_const (1 - ‖μ‖))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [hd.eventually (gt_mem_nhds hp)] with k hk
  exact pcc_local_bound hμ hk

end AppB
end TakhtajanTeo
