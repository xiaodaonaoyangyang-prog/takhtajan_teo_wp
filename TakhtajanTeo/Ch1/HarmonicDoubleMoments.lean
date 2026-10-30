import TakhtajanTeo.Ch1.HarmonicDoubleSeries
import TakhtajanTeo.Ch1.HarmonicResolventTransport
import Mathlib.Analysis.Normed.Group.Tannery

/-! Separable weighted moments and scalar Abel convergence for the resolvent kernel (TT:2662–2666). -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem wp_weighted_conjugate_moment {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ w ∈ unitDisc, HasSum (fun n => c n * w ^ n) (F w))
    (hf : Measurable F) {M : ℝ} (hB : ∀ w ∈ unitDisc, ‖F w‖ * (rho w)⁻¹ ≤ M) (n : ℕ) :
    (∫ w in unitDisc, conj (F w) * w ^ n * (rho w : ℂ)⁻¹) =
      conj ((π / 2 : ℂ) * c n / ((n + 1 : ℂ) * (n + 2) * (n + 3))) := by
  rw [← wp_disk_series_weighted_moment hc hf hB n, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with w
  simp only [map_mul, map_pow, map_inv₀, conj_conj, Complex.conj_ofReal]

theorem wp_weighted_double_moment {F G : ℂ → ℂ} {c d : ℕ → ℂ}
    (hc : ∀ w ∈ unitDisc, HasSum (fun n => c n * w ^ n) (F w))
    (hd : ∀ w ∈ unitDisc, HasSum (fun n => d n * w ^ n) (G w))
    (hf : Measurable F) (hg : Measurable G) {M N : ℝ}
    (hB : ∀ w ∈ unitDisc, ‖F w‖ * (rho w)⁻¹ ≤ M)
    (hC : ∀ w ∈ unitDisc, ‖G w‖ * (rho w)⁻¹ ≤ N) (n : ℕ) :
    (∫ p : ℂ × ℂ, (conj (F p.1) * (rho p.1 : ℂ)⁻¹) *
      (G p.2 * (rho p.2 : ℂ)⁻¹) * (p.1 * conj p.2) ^ n
      ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc))) =
      conj ((π / 2 : ℂ) * c n / ((n + 1 : ℂ) * (n + 2) * (n + 3))) *
        ((π / 2 : ℂ) * d n / ((n + 1 : ℂ) * (n + 2) * (n + 3))) := by
  calc
    _ = ∫ p : ℂ × ℂ, (conj (F p.1) * p.1 ^ n * (rho p.1 : ℂ)⁻¹) *
        (G p.2 * conj p.2 ^ n * (rho p.2 : ℂ)⁻¹)
        ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [mul_pow]
      ring
    _ = _ := by
      rw [integral_prod_mul (fun u : ℂ => conj (F u) * u ^ n * (rho u : ℂ)⁻¹)
        (fun v : ℂ => G v * conj v ^ n * (rho v : ℂ)⁻¹), wp_weighted_conjugate_moment hc hf hB n,
        wp_disk_series_weighted_moment hd hg hC n]

theorem wp_weighted_double_moment_diagonal {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ w ∈ unitDisc, HasSum (fun n => c n * w ^ n) (F w))
    (hf : Measurable F) {M : ℝ} (hB : ∀ w ∈ unitDisc, ‖F w‖ * (rho w)⁻¹ ≤ M) (n : ℕ) :
    (∫ p : ℂ × ℂ, (conj (F p.1) * (rho p.1 : ℂ)⁻¹) *
      (F p.2 * (rho p.2 : ℂ)⁻¹) * (p.1 * conj p.2) ^ n
      ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc))) =
      (π / 2 : ℂ) ^ 2 * (‖c n‖ ^ 2 : ℝ) /
        ((n + 1 : ℂ) * (n + 2) * (n + 3)) ^ 2 := by
  rw [wp_weighted_double_moment hc hc hf hf hB hB n]
  simp only [map_div₀, map_mul, map_add, map_natCast, map_ofNat, map_one, Complex.conj_ofReal]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  have h1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have h2 : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  have h3 : (n + 3 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 3 ≠ 0)
  field_simp

theorem wp_nonnegative_abel_series_tendsto {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (hs : Summable b) :
    Tendsto (fun t : ℝ => ∑' n : ℕ, t ^ n * b n) (𝓝[<] 1) (𝓝 (∑' n, b n)) := by
  refine tendsto_tsum_of_dominated_convergence hs ?_ ?_
  · intro n
    have ht : Tendsto (fun t : ℝ => t) (𝓝[<] 1) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [one_pow, one_mul] using
      (ht.pow n).mul_const (b n)
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
    intro n
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht.1.le _) (hb n))]
    exact mul_le_of_le_one_left (hb n) (pow_le_one₀ ht.1.le ht.2.le)

end TakhtajanTeo


