import TakhtajanTeo.Ch1.ResolventCutoff
import Mathlib.Analysis.Calculus.ContDiff.Convolution

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real Convolution
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Integration on a fixed compact interval preserves global smooth parameter dependence (TT:2781). -/
theorem wp_contDiff_interval_integral {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {g : P → ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℝ => g q.1 q.2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => ∫ t in (0 : ℝ)..1, g p t) := by
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := 2, rOut := 3, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let H : ℝ → ℝ := (Icc (-1 : ℝ) 0).indicator (fun _ => 1)
  let G : P → ℝ → ℝ := fun p t => b t * g p t
  have hH : LocallyIntegrable H volume := by
    have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (-1 : ℝ) 0) :=
      continuous_const.continuousOn.integrableOn_compact isCompact_Icc
    exact (hi.integrable_indicator measurableSet_Icc).locallyIntegrable
  have hs : ∀ p t, p ∈ (univ : Set P) → t ∉ tsupport b → G p t = 0 := by
    intro p t _ ht
    simp only [G, image_eq_zero_of_notMem_tsupport ht, zero_mul]
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : P × ℝ => G q.1 q.2) (univ ×ˢ univ) :=
    ((b.contDiff.comp contDiff_snd).mul hg).contDiffOn
  have hp := contDiffOn_convolution_left_with_param_comp
    (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip (v := fun _ : P => (0 : ℝ))
    (g := G) contDiffOn_const isOpen_univ b.hasCompactSupport hs hH hG
  have he (p : P) : (G p ⋆[(ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip, volume] H) 0 =
      ∫ t in (0 : ℝ)..1, g p t := by
    simp only [MeasureTheory.convolution_def, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.lsmul_apply, zero_sub, smul_eq_mul]
    calc
      _ = ∫ t, (Icc (0 : ℝ) 1).indicator (fun t => b t * g p t) t := by
        apply integral_congr_ae
        filter_upwards with t
        have hm : -t ∈ Icc (-1 : ℝ) 0 ↔ t ∈ Icc (0 : ℝ) 1 := by
          constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
        by_cases ht : t ∈ Icc (0 : ℝ) 1 <;> simp [H, G, Set.indicator, hm, ht]
      _ = ∫ t in Icc (0 : ℝ) 1, b t * g p t := integral_indicator measurableSet_Icc
      _ = ∫ t in Icc (0 : ℝ) 1, g p t := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        have hb : b t = 1 := b.one_of_mem_closedBall (by
          rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_of_nonneg ht.1]
          change t ≤ 2
          linarith [ht.2])
        dsimp only
        rw [hb, one_mul]
      _ = _ := by rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  simpa only [he, contDiffOn_univ] using hp

/-- The extended weighted resolvent kernel is genuinely smooth jointly at separated closed-disk pairs (TT:2781). -/
theorem wp_boundaryKernel_contDiffAt {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ closedBall (0 : ℂ) 1) (hzw : z ≠ w) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ => resolventBoundaryKernel p.1 p.2) (z, w) := by
  obtain ⟨δ, hδ, hnear⟩ := resolvent_boundary_denominator_uniform hz hw hzw
  obtain ⟨F, hF, _, hFeq⟩ := exists_resolvent_cutoff_inv_sq hδ
  let g : (ℂ × ℂ) → ℝ → ℝ := fun p t =>
    (2 / π) * (1 - ‖p.1‖ ^ 2) ^ 2 * (t * (1 - t) *
      F (‖p.1 - p.2‖ ^ 2 + t * (1 - ‖p.1‖ ^ 2) * (1 - ‖p.2‖ ^ 2)))
  have hZ : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℂ × ℂ) × ℝ => q.1.1) := contDiff_fst.fst
  have hW : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℂ × ℂ) × ℝ => q.1.2) := contDiff_fst.snd
  have hT : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℂ × ℂ) × ℝ => q.2) := contDiff_snd
  have hDz := (contDiff_const (c := (1 : ℝ))).sub (hZ.norm_sq ℂ)
  have hDw := (contDiff_const (c := (1 : ℝ))).sub (hW.norm_sq ℂ)
  have hden := ((hZ.sub hW).norm_sq ℂ).add ((hT.mul hDz).mul hDw)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℂ × ℂ) × ℝ => g q.1 q.2) :=
    (contDiff_const.mul (hDz.pow 2)).mul
      ((hT.mul (contDiff_const.sub hT)).mul (hF.comp hden))
  apply (wp_contDiff_interval_integral hg).contDiffAt.congr_of_eventuallyEq
  filter_upwards [hnear] with p hp
  unfold resolventBoundaryKernel
  apply intervalIntegral.integral_congr
  intro t ht
  have hti : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  have hval := hFeq _ ((hp t hti).trans (le_abs_self _))
  simp only [g, resolventBoundaryIntegrand, hval, div_eq_mul_inv, one_mul]

end TakhtajanTeo


