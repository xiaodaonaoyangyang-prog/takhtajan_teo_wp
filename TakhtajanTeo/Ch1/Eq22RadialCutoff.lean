import TakhtajanTeo.Ch1.Eq22Reproducing

/-! Smooth radial cutoffs for the conformal disk exhaustion in (2.2). -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def eq22RadialCutoff (ε : ℝ) (w : ℂ) : ℂ :=
  (Real.smoothTransition ((1-ε-‖w‖^2)/ε) : ℂ)

-- R1
theorem eq22_transition_deriv_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖deriv Real.smoothTransition x‖ ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ 1 _).continuous_deriv_one
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0,le_max_right _ _,fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact (hM x hx).trans (le_max_left _ _)
  · rcases lt_or_ge x 0 with hx0 | hx0
    · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hx0] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      rw [he.deriv_eq]
      simpa using le_max_right M 0
    · have hx1 : 1 < x := lt_of_not_ge (fun hx1 => hx ⟨hx0,hx1⟩)
      have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hx1] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      rw [he.deriv_eq]
      simpa using le_max_right M 0

-- R2
theorem eq22_radial_cutoff_smooth (ε : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (eq22RadialCutoff ε) := by
  exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const ε))

-- R3
theorem eq22_radial_cutoff_values {ε : ℝ} (hε : 0 < ε) :
    (∀ w, ‖w‖^2 ≤ 1-2*ε → eq22RadialCutoff ε w = 1) ∧
    (∀ w, 1-ε ≤ ‖w‖^2 → eq22RadialCutoff ε w = 0) ∧
    (∀ w, ‖eq22RadialCutoff ε w‖ ≤ 1) ∧
    (∀ w, ‖1-eq22RadialCutoff ε w‖ ≤ 1) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro w hw
    have ha : 1 ≤ (1-ε-‖w‖^2)/ε := (le_div_iff₀ hε).mpr (by linarith)
    simp [eq22RadialCutoff,Real.smoothTransition.one_of_one_le ha]
  · intro w hw
    have ha : (1-ε-‖w‖^2)/ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    simp [eq22RadialCutoff,Real.smoothTransition.zero_of_nonpos ha]
  · intro w
    simpa only [eq22RadialCutoff,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg _)] using Real.smoothTransition.le_one ((1-ε-‖w‖^2)/ε)
  · intro w
    have he : (1 : ℂ)-eq22RadialCutoff ε w =
        ((1-Real.smoothTransition ((1-ε-‖w‖^2)/ε) : ℝ) : ℂ) := by
      simp [eq22RadialCutoff]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one _))]
    linarith [Real.smoothTransition.nonneg ((1-ε-‖w‖^2)/ε)]

-- R4
theorem eq22_radial_cutoff_support {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (eq22RadialCutoff ε) ∧
    tsupport (eq22RadialCutoff ε) ⊆ unitDisc := by
  let S : Set ℂ := {w | ‖w‖^2 ≤ 1-ε}
  have hSc : IsClosed S := isClosed_le (continuous_norm.pow 2) continuous_const
  have hSD : S ⊆ unitDisc := by
    intro w hw
    apply mem_ball_zero_iff.mpr
    change ‖w‖^2 ≤ 1-ε at hw
    nlinarith [norm_nonneg w]
  have hs : Function.support (eq22RadialCutoff ε) ⊆ S := by
    intro w hw
    by_contra hn
    exact hw ((eq22_radial_cutoff_values hε).2.1 w (le_of_lt (lt_of_not_ge hn)))
  have ht : tsupport (eq22RadialCutoff ε) ⊆ S := closure_minimal hs hSc
  have hSk : IsCompact S := (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hSc
    (fun w hw => ball_subset_closedBall (hSD hw))
  exact ⟨hSk.of_isClosed_subset (isClosed_tsupport _) ht,ht.trans hSD⟩

-- R5
theorem eq22_radial_cutoff_derivative :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ∀ w ∈ unitDisc,
      ‖dzbar (eq22RadialCutoff ε) w‖ ≤ M/ε := by
  obtain ⟨M,hM0,hM⟩ := eq22_transition_deriv_bound
  refine ⟨2*M,by positivity,fun ε hε w hw => ?_⟩
  let a : ℂ → ℝ := fun v => (1-ε-‖v‖^2)/ε
  let A : ℂ →L[ℝ] ℝ := ε⁻¹ • (-((2 : ℝ) • innerSL ℝ w))
  have ha : HasFDerivAt a A w := by
    have ha0 := ((hasStrictFDerivAt_norm_sq w).hasFDerivAt.const_sub (1-ε)).const_smul ε⁻¹
    change HasFDerivAt (fun x : ℂ => ε⁻¹*(1-ε-‖x‖^2))
      (ε⁻¹ • (-(2 • innerSL ℝ w))) w at ha0
    simpa only [a,A,two_smul,div_eq_mul_inv,mul_comm] using ha0
  have hs := (Real.smoothTransition.contDiff : ContDiff ℝ 1 _).differentiable (by simp)
  have hd : fderiv ℝ (eq22RadialCutoff ε) w =
      Complex.ofRealCLM.comp ((fderiv ℝ Real.smoothTransition (a w)).comp A) :=
    (Complex.ofRealCLM.hasFDerivAt.comp w ((hs (a w)).hasFDerivAt.comp w ha)).fderiv
  have hA : ‖A‖ = ε⁻¹*2*‖w‖ := by
    simp only [A,norm_smul,norm_neg,innerSL_apply_norm]
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    norm_num
    ring
  have hσ : ‖fderiv ℝ Real.smoothTransition (a w)‖ ≤ M := by
    rw [← norm_deriv_eq_norm_fderiv]
    exact hM _
  have hv : ∀ v : ℂ, ‖fderiv ℝ (eq22RadialCutoff ε) w v‖ ≤ (2*M/ε)*‖v‖ := by
    intro v
    rw [hd,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,Complex.norm_real]
    calc
      ‖((fderiv ℝ Real.smoothTransition (a w)).comp A) v‖
          ≤ ‖fderiv ℝ Real.smoothTransition (a w)‖*‖A v‖ := by
            simpa only [ContinuousLinearMap.comp_apply] using
              ContinuousLinearMap.le_opNorm (fderiv ℝ Real.smoothTransition (a w)) (A v)
      _ ≤ M*(‖A‖*‖v‖) := mul_le_mul hσ (ContinuousLinearMap.le_opNorm A v) (norm_nonneg _) hM0
      _ ≤ M*(ε⁻¹*2*1*‖v‖) := by rw [hA]; gcongr; exact (mem_ball_zero_iff.mp hw).le
      _ = (2*M/ε)*‖v‖ := by ring
  have h1 := hv 1
  have hI := hv I
  simp only [norm_one,norm_I,mul_one] at h1 hI
  unfold dzbar
  rw [norm_div,show ‖(2 : ℂ)‖ = 2 by simp,div_le_iff₀ (by norm_num : (0 : ℝ)<2)]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul,norm_I,one_mul]
  linarith

-- R6
theorem eq22_radial_cutoff_derivative_zero {ε : ℝ} (hε : 0 < ε)
    {w : ℂ} (hw : ‖w‖^2 < 1-2*ε) : dzbar (eq22RadialCutoff ε) w = 0 := by
  have he : eq22RadialCutoff ε =ᶠ[𝓝 w] fun _ => (1 : ℂ) := by
    filter_upwards [(isOpen_lt (continuous_norm.pow 2) continuous_const).mem_nhds hw] with v hv
    exact (eq22_radial_cutoff_values hε).1 v hv.le
  unfold dzbar
  rw [he.fderiv_eq]
  simp

-- R7
theorem eq22_radial_cutoff_tendsto {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) {w : ℂ} (hw : w ∈ unitDisc) :
    Tendsto (fun n => eq22RadialCutoff (ε n) w) atTop (𝓝 1) := by
  have hw1 : ‖w‖^2 < 1 := by
    have hn := mem_ball_zero_iff.mp hw
    nlinarith [norm_nonneg w]
  have he : (fun n => eq22RadialCutoff (ε n) w) =ᶠ[atTop] fun _ => (1 : ℂ) := by
    filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < (1-‖w‖^2)/2 by linarith))] with n hn
    exact (eq22_radial_cutoff_values (hε n)).1 w (by linarith)
  exact tendsto_const_nhds.congr' he.symm

theorem eq22_radial_cutoff_derivative_zero_outer {ε : ℝ} (hε : 0 < ε)
    {w : ℂ} (hw : 1-ε < ‖w‖^2) : dzbar (eq22RadialCutoff ε) w = 0 := by
  have he : eq22RadialCutoff ε =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_norm.pow 2)).mem_nhds hw] with v hv
    exact (eq22_radial_cutoff_values hε).2.1 v hv.le
  unfold dzbar
  rw [he.fderiv_eq]
  simp

theorem eq22_radial_cutoff_global_derivative :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ∀ w : ℂ,
      ‖dzbar (eq22RadialCutoff ε) w‖ ≤ M/ε := by
  obtain ⟨M,hM0,hM⟩ := eq22_radial_cutoff_derivative
  refine ⟨M,hM0,fun ε hε w => ?_⟩
  by_cases hw : w ∈ unitDisc
  · exact hM ε hε w hw
  · have hn : 1 ≤ ‖w‖ := le_of_not_gt (fun hn => hw (mem_ball_zero_iff.mpr hn))
    rw [eq22_radial_cutoff_derivative_zero_outer hε (by nlinarith [norm_nonneg w]),norm_zero]
    exact div_nonneg hM0 hε.le

end TakhtajanTeo
