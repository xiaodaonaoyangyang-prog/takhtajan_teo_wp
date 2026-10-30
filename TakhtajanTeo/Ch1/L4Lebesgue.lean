import TakhtajanTeo.Ch1.GenPartialsMorreyFour
import Mathlib.MeasureTheory.Covering.DensityTheorem

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real
noncomputable section
namespace TakhtajanTeo

theorem mp_locallyIntegrable_four_sub {g : ℂ → ℂ}
    (hg : ∀ s : Set ℂ, IsCompact s → MemLp g 4 (volume.restrict s)) (q : ℂ) :
    LocallyIntegrable (fun u => ‖g u - q‖ ^ 4) volume := by
  apply locallyIntegrable_iff.mpr
  intro s hs
  haveI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hs.measure_ne_top
  have hsub : MemLp (fun u => g u - q) 4 (volume.restrict s) :=
    (hg s hs).sub (memLp_const q)
  exact hsub.integrable_norm_pow (by norm_num)

theorem mp_average_mono {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : ∀ a, f a ≤ g a) :
    (⨍ a, f a ∂μ) ≤ ⨍ a, g a ∂μ := by
  simp only [average_eq, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (integral_mono hf hg hfg)
    (inv_nonneg.mpr measureReal_nonneg)

theorem mp_average_four_sub_le {g : ℂ → ℂ}
    (hg : ∀ s : Set ℂ, IsCompact s → MemLp g 4 (volume.restrict s))
    (z q : ℂ) {r : ℝ} (hr : 0 < r) :
    (⨍ u in closedBall z r, ‖g u - g z‖ ^ 4) ≤
      8 * (⨍ u in closedBall z r, ‖g u - q‖ ^ 4) + 8 * ‖g z - q‖ ^ 4 := by
  haveI : IsFiniteMeasure (volume.restrict (closedBall z r)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  have hzero : volume (closedBall z r) ≠ 0 := (measure_closedBall_pos volume z hr).ne'
  have hleft := (mp_locallyIntegrable_four_sub hg (g z)).integrableOn_isCompact (isCompact_closedBall z r)
  have hq := (mp_locallyIntegrable_four_sub hg q).integrableOn_isCompact (isCompact_closedBall z r)
  have hup : IntegrableOn (fun u => 8 * ‖g u - q‖ ^ 4 + 8 * ‖g z - q‖ ^ 4) (closedBall z r) :=
    (hq.const_mul 8).add (integrable_const _)
  have h := mp_average_mono hleft hup (fun u => by
    simpa only [norm_sub_rev q (g z)] using mp_norm_sub_four_le (g u) q (g z))
  refine h.trans_eq ?_
  rw [average_fun_add (hq.const_mul 8) (integrable_const _), average_const_mul,
    setAverage_const hzero measure_closedBall_lt_top.ne]

/-- Genuine L4 Lebesgue points for complex-valued locally L4 functions.
Scalar differentiation is applied simultaneously at countably many dense
constants, then the fourth-power triangle inequality removes that constant. -/
theorem mp_ae_l4_lebesgue {g : ℂ → ℂ}
    (hg : ∀ s : Set ℂ, IsCompact s → MemLp g 4 (volume.restrict s)) :
    ∀ᵐ z : ℂ, Tendsto (fun r : ℝ => ⨍ u in closedBall z r, ‖g u - g z‖ ^ 4)
      (𝓝[>] 0) (𝓝 0) := by
  have hscalar : ∀ n : ℕ, ∀ᵐ z : ℂ,
      Tendsto (fun r : ℝ => ⨍ u in closedBall z r, ‖g u - TopologicalSpace.denseSeq ℂ n‖ ^ 4)
        (𝓝[>] 0) (𝓝 (‖g z - TopologicalSpace.denseSeq ℂ n‖ ^ 4)) := by
    intro n
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume
      (mp_locallyIntegrable_four_sub hg (TopologicalSpace.denseSeq ℂ n)) 1] with z hz
    exact hz (fun _ : ℝ => z) (fun r => r) tendsto_id
      (by filter_upwards [self_mem_nhdsWithin] with r hr
          show z ∈ closedBall z (1 * r)
          exact mem_closedBall_self (by simpa using (le_of_lt hr)))
  filter_upwards [ae_all_iff.mpr hscalar] with z hz
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun r => lt_of_lt_of_le ha
      (average_nonneg fun u => pow_nonneg (norm_nonneg _) 4)
  · intro ε hε
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq ℂ)
      (g z) (min 1 (ε / 64)) (lt_min zero_lt_one (div_pos hε (by norm_num)))
    rw [dist_eq_norm] at hn
    have hd1 : ‖g z - TopologicalSpace.denseSeq ℂ n‖ ≤ 1 := (lt_min_iff.mp hn).1.le
    have hdε := (lt_min_iff.mp hn).2
    have hd4 := pow_le_of_le_one (norm_nonneg (g z - TopologicalSpace.denseSeq ℂ n)) hd1
      (by norm_num : (4 : ℕ) ≠ 0)
    have hev := (hz n).eventually (gt_mem_nhds (by linarith :
      ‖g z - TopologicalSpace.denseSeq ℂ n‖ ^ 4 <
        ‖g z - TopologicalSpace.denseSeq ℂ n‖ ^ 4 + ε / 16))
    filter_upwards [hev, self_mem_nhdsWithin] with r hr hrpos
    have hbound := mp_average_four_sub_le hg z (TopologicalSpace.denseSeq ℂ n) hrpos
    linarith

theorem mp_normalized_l4_eq {g : ℂ → ℂ}
    (hg : ∀ s : Set ℂ, IsCompact s → MemLp g 4 (volume.restrict s))
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (eLpNorm (fun u => g u - g z) 4 (volume.restrict (closedBall z r))).toReal / Real.sqrt r =
      Real.sqrt (Real.sqrt (Real.pi * (⨍ u in closedBall z r, ‖g u - g z‖ ^ 4))) := by
  haveI : IsFiniteMeasure (volume.restrict (closedBall z r)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  have hsub : MemLp (fun u => g u - g z) 4 (volume.restrict (closedBall z r)) :=
    (hg _ (isCompact_closedBall z r)).sub (memLp_const (g z))
  have hN := mp_l4_fourth_power hsub.aestronglyMeasurable
  have hvol : volume.real (closedBall z r) = r ^ 2 * Real.pi := by
    simp [measureReal_def, Complex.volume_closedBall, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le]
  have havg : (⨍ u in closedBall z r, ‖g u - g z‖ ^ 4) =
      (r ^ 2 * Real.pi)⁻¹ * (∫ u in closedBall z r, ‖g u - g z‖ ^ 4) := by
    rw [average_eq, measureReal_restrict_apply_univ, hvol, smul_eq_mul]
  have hs4 : Real.sqrt r ^ 4 = r ^ 2 := by
    calc Real.sqrt r ^ 4 = (Real.sqrt r ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hr.le]
  have hnpow : ((eLpNorm (fun u => g u - g z) 4 (volume.restrict (closedBall z r))).toReal /
      Real.sqrt r) ^ 4 = Real.pi * (⨍ u in closedBall z r, ‖g u - g z‖ ^ 4) := by
    rw [div_pow, hN, hs4, havg]
    field_simp [hr.ne', Real.pi_ne_zero]
  have havg0 : 0 ≤ Real.pi * (⨍ u in closedBall z r, ‖g u - g z‖ ^ 4) :=
    mul_nonneg Real.pi_pos.le (average_nonneg fun u => pow_nonneg (norm_nonneg _) 4)
  have hroot : Real.sqrt (Real.sqrt (Real.pi * (⨍ u in closedBall z r, ‖g u - g z‖ ^ 4))) ^ 4 =
      Real.pi * (⨍ u in closedBall z r, ‖g u - g z‖ ^ 4) := by
    rw [show ∀ a : ℝ, a ^ 4 = (a ^ 2) ^ 2 from fun a => by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt havg0]
  exact (pow_left_inj₀ (div_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _) (by norm_num : (4 : ℕ) ≠ 0)).mp (hnpow.trans hroot.symm)

/-- The precise radius normalization needed by the two-dimensional p=4
Morrey estimate: the local gradient L4 error is o(sqrt r) a.e. -/
theorem mp_ae_normalized_l4_lebesgue {g : ℂ → ℂ}
    (hg : ∀ s : Set ℂ, IsCompact s → MemLp g 4 (volume.restrict s)) :
    ∀ᵐ z : ℂ, Tendsto (fun r : ℝ =>
      (eLpNorm (fun u => g u - g z) 4 (volume.restrict (closedBall z r))).toReal / Real.sqrt r)
      (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [mp_ae_l4_lebesgue hg] with z hz
  have hlim := (hz.const_mul Real.pi).sqrt.sqrt
  simp only [mul_zero, Real.sqrt_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (mp_normalized_l4_eq hg z hr).symm

end TakhtajanTeo

