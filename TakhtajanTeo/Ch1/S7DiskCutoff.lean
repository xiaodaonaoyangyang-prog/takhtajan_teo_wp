import TakhtajanTeo.Ch1.S7CompactAdjoint
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

private theorem normSq_smooth : ContDiff ℝ (⊤ : ℕ∞) (Complex.normSq : ℂ → ℝ) := by
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

/-- A genuine exhaustion cutoff, equal to one away from a shrinking boundary collar. -/
def s7dc_cutoff (n : ℕ) (z : ℂ) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 2) * (1 - Complex.normSq z) - 1)

theorem s7dc_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (s7dc_cutoff n) := by
  unfold s7dc_cutoff
  apply Real.smoothTransition.contDiff.comp
  exact (contDiff_const.mul (contDiff_const.sub normSq_smooth)).sub contDiff_const

theorem s7dc_bounds (n : ℕ) (z : ℂ) :
    0 ≤ s7dc_cutoff n z ∧ s7dc_cutoff n z ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem s7dc_support_bound (n : ℕ) :
    tsupport (s7dc_cutoff n) ⊆
      {z : ℂ | Complex.normSq z ≤ 1 - 1 / ((n : ℝ) + 2)} := by
  have hn : 0 < (n : ℝ) + 2 := by positivity
  apply closure_minimal
  · intro z hz
    have hp : 0 < ((n : ℝ) + 2) * (1 - Complex.normSq z) - 1 := by
      by_contra hh
      exact hz (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hh))
    have hh : 1 / ((n : ℝ) + 2) < 1 - Complex.normSq z := by
      apply (div_lt_iff₀ hn).2
      nlinarith
    dsimp
    linarith
  · apply isClosed_le
    · exact normSq_smooth.continuous
    · exact continuous_const

theorem s7dc_compact (n : ℕ) :
    HasCompactSupport (s7dc_cutoff n) ∧ tsupport (s7dc_cutoff n) ⊆ unitDisc := by
  have hs : tsupport (s7dc_cutoff n) ⊆ unitDisc := by
    intro z hz
    have hb := s7dc_support_bound n hz
    change Complex.normSq z ≤ 1 - 1 / ((n : ℝ) + 2) at hb
    have hp : 0 < 1 / ((n : ℝ) + 2) := by positivity
    have hz1 : ‖z‖ < 1 := by
      rw [Complex.normSq_eq_norm_sq] at hb
      nlinarith [norm_nonneg z]
    simpa [unitDisc, mem_ball, dist_zero_right] using hz1
  refine ⟨?_, hs⟩
  exact (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_tsupport _)
    (fun z hz => ball_subset_closedBall (hs hz))

/-- At each interior point the cutoffs eventually agree with one on a neighborhood. -/
theorem s7dc_eventually_one {z : ℂ} (hz : z ∈ unitDisc) :
    ∀ᶠ n : ℕ in atTop, s7dc_cutoff n =ᶠ[𝓝 z] (fun _ => 1) := by
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball, dist_zero_right] using hz
  have hd : 0 < 1 - Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / (1 - Complex.normSq z))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hbig : 2 < ((n : ℝ) + 2) * (1 - Complex.normSq z) := by
    have hh := (div_lt_iff₀ hd).1 hN
    nlinarith
  have hc : Continuous (fun w : ℂ => ((n : ℝ) + 2) * (1 - Complex.normSq w) - 1) := by
    exact (continuous_const.mul (continuous_const.sub normSq_smooth.continuous)).sub continuous_const
  filter_upwards [hc.continuousAt.eventually (lt_mem_nhds (show
      1 < ((n : ℝ) + 2) * (1 - Complex.normSq z) - 1 by linarith))] with w hw
  exact Real.smoothTransition.one_of_one_le hw.le

/-- The transition derivative is supported in the fixed unit interval. -/
theorem s7dc_transition_deriv_support :
    tsupport (deriv Real.smoothTransition) ⊆ Icc (0 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hh
  have hh' : x < 0 ∨ 1 < x := by simpa only [mem_Icc, not_and_or, not_le] using hh
  rcases hh' with hn | hp
  · have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [gt_mem_nhds hn] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    exact hx (by simpa using he.deriv_eq)
  · have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [lt_mem_nhds hp] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    exact hx (by simpa using he.deriv_eq)

/-- Both scalar derivatives used in the cutoff estimates have a uniform bound. -/
theorem s7dc_transition_deriv_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖deriv Real.smoothTransition x‖ ≤ C ∧
      ‖deriv (deriv Real.smoothTransition) x‖ ≤ C := by
  have h1 : HasCompactSupport (deriv Real.smoothTransition) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) s7dc_transition_deriv_support
  have hd1 : ContDiff ℝ (⊤ : ℕ∞) (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  have hd2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv Real.smoothTransition)) :=
    (contDiff_infty_iff_deriv.mp hd1).2
  obtain ⟨A,hA⟩ := hd1.continuous.bounded_above_of_compact_support h1
  obtain ⟨B,hB⟩ := hd2.continuous.bounded_above_of_compact_support h1.deriv
  refine ⟨max 0 (max A B), le_max_left _ _, fun x => ⟨?_, ?_⟩⟩
  · exact (hA x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hB x).trans ((le_max_right _ _).trans (le_max_right _ _))

end TakhtajanTeo
