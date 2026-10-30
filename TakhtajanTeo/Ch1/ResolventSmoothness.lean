import TakhtajanTeo.Ch1.ResolventTail

/-! Localizing the resolvent into compact-source and smooth-tail parts. -/

open Real Complex Filter Set Topology MeasureTheory Metric

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

set_option autoImplicit false

/-- The full disk resolvent maps bounded smooth inputs to smooth functions.
No global bounds on derivatives of the input are assumed. -/
theorem RK3_output_smooth_disc {g : ℂ → ℂ} (hg : g ∈ BCinf unitDisc) :
    ContDiffOn ℝ (⊤ : ℕ∞) (resolventOp unitDisc g) unitDisc := by
  obtain ⟨C, hb⟩ := hg.2
  have hzero : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hC : 0 ≤ C := (norm_nonneg (g 0)).trans (hb 0 hzero)
  have hD : IsOpen unitDisc := isOpen_ball
  intro z hz
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  let b : ContDiffBump z :=
    { rIn := (1 - ‖z‖) / 4, rOut := (1 - ‖z‖) / 2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hs : tsupport b ⊆ unitDisc := by
    rw [b.tsupport_eq]
    intro w hw
    have hdist : dist w z ≤ (1 - ‖z‖) / 2 := hw
    have hn : ‖w‖ ≤ dist w z + ‖z‖ := by
      simpa only [dist_zero_right] using dist_triangle w z (0 : ℂ)
    apply mem_ball_zero_iff.mpr
    linarith
  have hbc : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => (b w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hbs : tsupport (fun w : ℂ => (b w : ℂ)) ⊆ unitDisc := by
    exact (tsupport_comp_subset (g := Complex.ofReal) (by simp) b).trans hs
  have hbh : HasCompactSupport (fun w : ℂ => (b w : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  have hI : ContDiff ℝ (⊤ : ℕ∞) (fun w => g w * (b w : ℂ)) :=
    resolvent_source_mul_contDiff hD hbc hg.1 hbs
  have hIc : HasCompactSupport (fun w => g w * (b w : ℂ)) := hbh.mul_left (f := g)
  have hIs : tsupport (fun w => g w * (b w : ℂ)) ⊆ unitDisc :=
    (tsupport_mul_subset_right (f := g) (g := fun w => (b w : ℂ))).trans hbs
  have hIb : ∀ w ∈ unitDisc, ‖g w * (b w : ℂ)‖ ≤ C := by
    intro w hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    calc
      ‖g w‖ * b w ≤ C * 1 := mul_le_mul (hb w hw) b.le_one b.nonneg hC
      _ = C := mul_one C
  have hIbc : (fun w => g w * (b w : ℂ)) ∈ BCinf unitDisc := ⟨hI.contDiffOn, C, hIb⟩
  have hTc : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => ((1 - b w : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.sub b.contDiff)
  have hTb : ∀ w ∈ unitDisc, ‖((1 - b w : ℝ) : ℂ) * g w‖ ≤ C := by
    intro w hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr b.le_one)]
    calc
      (1 - b w) * ‖g w‖ ≤ 1 * C :=
        mul_le_mul (by linarith [b.nonneg' w]) (hb w hw) (norm_nonneg _) (by norm_num)
      _ = C := one_mul C
  have hTbc : (fun w => ((1 - b w : ℝ) : ℂ) * g w) ∈ BCinf unitDisc :=
    ⟨hTc.contDiffOn.mul hg.1, C, hTb⟩
  have hIo := (resolventOp_contDiffOn_compact hI hIc hIs).contDiffAt (hD.mem_nhds hz)
  have hTo := resolvent_tail_operator_contDiffAt b hg.1.continuousOn hC hb hz
    (mem_ball_self (by linarith [b.rIn_pos] : 0 < b.rIn / 2))
  have hp := hIo.add hTo
  apply ContDiffAt.contDiffWithinAt
  apply hp.congr_of_eventuallyEq
  filter_upwards [hD.mem_nhds hz] with v hv
  have he : g = (fun w => g w * (b w : ℂ) + ((1 - b w : ℝ) : ℂ) * g w) := by
    funext w
    push_cast
    ring
  exact (congrArg (fun k : ℂ → ℂ => resolventOp unitDisc k v) he).trans
    (resolventOp_add (Or.inl rfl) hIbc hTbc hv)

/-- The full bounded-smooth output clause of RK3 in the disk model. -/
theorem RK3_output_BCinf_disc {g : ℂ → ℂ} (hg : g ∈ BCinf unitDisc) :
    resolventOp unitDisc g ∈ BCinf unitDisc :=
  ⟨RK3_output_smooth_disc hg, RK3_output_bounded (Or.inl rfl) hg⟩

end TakhtajanTeo
