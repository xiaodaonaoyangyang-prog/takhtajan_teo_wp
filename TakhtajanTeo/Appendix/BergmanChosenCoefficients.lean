import TakhtajanTeo.Appendix.BergmanKernelModel

/-! # Actual kernel series for the chosen Grunsky coefficients -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

theorem b8_double_series_from_exp {f : ℂ → ℂ} {a : ℕ → ℕ → ℂ} {c : ℂ}
    (he : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (c - S)) :
    (∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      Summable (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2)) ∧
    ContinuousOn (fun q : ℂ × ℂ => ∑' p : ℕ × ℕ,
      a p.1 p.2 * q.1 ^ p.1 * q.2 ^ p.2) (unitDisc ×ˢ unitDisc) := by
  have hR : ∀ R : ℝ, 0 < R → R < 1 →
      Summable (fun p : ℕ × ℕ => ‖a p.1 p.2‖ * R ^ p.1 * R ^ p.2) := by
    intro R hR0 hR1
    have hRD : (R : ℂ) ∈ unitDisc := by simpa [unitDisc, abs_of_pos hR0] using hR1
    have hnD : -(R : ℂ) ∈ unitDisc := by simpa [unitDisc, abs_of_pos hR0] using hR1
    have hne : (R : ℂ) ≠ -(R : ℂ) := by
      intro h
      have hh := congrArg Complex.re h
      simp only [neg_re, ofReal_re] at hh
      linarith
    obtain ⟨S, hs, _⟩ := he _ hRD _ hnD hne
    simpa only [norm_mul, norm_pow, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hR0.le] using hs.summable.norm
  have hb : ∀ R : ℝ, ∀ p : ℕ × ℕ, ∀ q : ℂ × ℂ, ‖q‖ ≤ R →
      ‖a p.1 p.2 * q.1 ^ p.1 * q.2 ^ p.2‖ ≤ ‖a p.1 p.2‖ * R ^ p.1 * R ^ p.2 := by
    intro R p q hq
    have hq1 : ‖q.1‖ ≤ R := (le_max_left _ _).trans (by simpa [Prod.norm_def] using hq)
    have hq2 : ‖q.2‖ ≤ R := (le_max_right _ _).trans (by simpa [Prod.norm_def] using hq)
    have hR0 : 0 ≤ R := (norm_nonneg q).trans hq
    simp only [norm_mul, norm_pow]
    gcongr
  have hchoose : ∀ q ∈ unitDisc ×ˢ unitDisc, ∃ R : ℝ, ‖q‖ < R ∧ R < 1 := by
    intro q hq
    apply exists_between
    simpa [Prod.norm_def] using max_lt (mem_ball_zero_iff.mp hq.1) (mem_ball_zero_iff.mp hq.2)
  constructor
  · intro z hz w hw
    obtain ⟨R, hqR, hR1⟩ := hchoose (z,w) ⟨hz,hw⟩
    exact ((hR R ((norm_nonneg _).trans_lt hqR) hR1).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun p => hb R p (z,w) hqR.le)).of_norm
  · intro q hq
    obtain ⟨R, hqR, hR1⟩ := hchoose q hq
    have hc : ContinuousOn (fun q : ℂ × ℂ => ∑' p : ℕ × ℕ,
        a p.1 p.2 * q.1 ^ p.1 * q.2 ^ p.2) (closedBall 0 R) := by
      apply continuousOn_tsum (fun _ => by fun_prop)
        (hR R ((norm_nonneg _).trans_lt hqR) hR1)
      intro p q hq
      exact hb R p q (mem_closedBall_zero_iff.mp hq)
    exact (hc.continuousAt (closedBall_mem_nhds_of_mem (by simpa using hqR))).continuousWithinAt

set_option maxHeartbeats 500000 in
theorem b8_kernel_series_of_exp {f : ℂ → ℂ} {a : ℕ → ℕ → ℂ} {c : ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    (he : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (c - S))
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    HasSum (fun p : ℕ × ℕ => a (p.1+1) (p.2+1) * ((p.1+1 : ℕ) : ℂ) *
      ((p.2+1 : ℕ) : ℂ) * z ^ p.1 * w ^ p.2) ((π : ℂ) * kerK1 f z w) := by
  let F : ℂ → ℂ → ℂ := fun z w => ∑' p : ℕ × ℕ, a p.1 p.2 * z ^ p.1 * w ^ p.2
  let L : ℂ × ℂ → ℂ := fun q => c - F q.1 q.2
  obtain ⟨hS, hC⟩ := b8_double_series_from_exp he
  have hLC : ContinuousOn L (unitDisc ×ˢ unitDisc) := continuousOn_const.sub hC
  have hLe : ∀ q ∈ unitDisc ×ˢ unitDisc, exp (L q) = dslope f q.1 q.2 := by
    rintro ⟨u,v⟩ ⟨hu,hv⟩
    have hmap : MapsTo (fun u : ℂ => (u,v)) unitDisc (unitDisc ×ˢ unitDisc) :=
      fun _ hu => ⟨hu,hv⟩
    have hpc : ContinuousOn (fun u : ℂ => (u,v)) unitDisc :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hlc := Complex.continuous_exp.comp_continuousOn (hLC.comp hpc hmap)
    change ContinuousOn (fun u : ℂ => exp (L (u,v))) unitDisc at hlc
    have hqc := (continuousOn_dslope_joint (f := f) hf).comp hpc hmap
    change ContinuousOn (fun u : ℂ => dslope f u v) unitDisc at hqc
    have hd : Dense ({v} : Set ℂ)ᶜ := (Set.finite_singleton v).countable.dense_compl ℝ
    have hdense : unitDisc ⊆ closure (unitDisc \ {v}) :=
      fun _ hu => hd.open_subset_closure_inter isOpen_ball hu
    have hh : EqOn (fun u => exp (L (u,v))) (fun u => dslope f u v) unitDisc := by
      apply Set.EqOn.of_subset_closure (s := unitDisc \ {v}) (t := unitDisc) _
        hlc hqc sdiff_subset hdense
      intro u hu
      have huv : u ≠ v := by simpa using hu.2
      obtain ⟨S, hs, heq⟩ := he u hu.1 v hv huv
      dsimp [L, F]
      rw [hs.tsum_eq, ← heq, dslope_swap, dslope_of_ne f huv, slope_def_field]
    exact hh hu
  have hLD := differentiableOn_exp_lift_prod (isOpen_ball.prod isOpen_ball)
    (holomorphic_dslope_joint hf) hLC hLe
  have hder := g2c_log_dslope_deriv_mixed hf hi hLD hLe hz hw hzw
  dsimp only [L] at hder
  simp only [deriv_const_sub, deriv.fun_neg] at hder
  have hs := g2c_double_series_deriv_mixed_succ
    (fun u hu v hv => (hS u hu v hv).hasSum) hz hw
  change HasSum _ (deriv (fun v => deriv (fun u => F u v) z) w) at hs
  convert hs using 1
  rw [kerK1_of_ne f hzw]
  have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp' : (π : ℂ) * (1 / (π : ℂ)) = 1 := by field_simp
  rw [← mul_assoc, hp', one_mul]
  linear_combination hder

end AppB
end TakhtajanTeo
