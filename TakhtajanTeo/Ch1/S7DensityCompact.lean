import TakhtajanTeo.Ch1.S7DensityJoint

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- A genuine common parameter neighborhood and derivative bound on every
fixed compact spatial set. No bound is supplied as an assumption. -/
theorem s7dcp_bound {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ)
    {C : Set ℂ} (hC : IsCompact C) (hCU : C ⊆ upperHalf) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
      ∀ z ∈ C, ∀ ε ∈ closedBall (0:ℂ) r,
        DifferentiableAt ℝ (fun e => rhoVar μ e z/(rhoU z:ℂ)) ε ∧
        ‖fderiv ℝ (fun e => rhoVar μ e z/(rhoU z:ℂ)) ε‖ ≤ M := by
  obtain ⟨k,hk,hb,hs⟩ := s71_harm_setup hμ
  let r : ℝ := 1/(k+1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrk : r*k < 1 := by
    dsimp [r]
    rw [one_div,mul_comm,← div_eq_mul_inv]
    exact (div_lt_one (by linarith : 0 < k+1)).2 (by linarith)
  let F : ℂ × ℂ → ℂ := fun p => rhoVar μ p.1 p.2/(rhoU p.2:ℂ)
  let D := {ε : ℂ | ‖ε‖*k < 1} ×ˢ upperHalf
  have hF : ContDiffOn ℝ 2 F D := s7dj_ratio hk hb hs
  have hDo : IsOpen D :=
    (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).prod
      (isOpen_lt continuous_const Complex.continuous_im)
  have hFD : ContinuousOn (fderiv ℝ F) D :=
    hF.continuousOn_fderiv_of_isOpen hDo (by norm_num)
  let P : ℂ × ℂ → (ℂ →L[ℝ] ℂ) := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ ℂ ℂ)
  have hP : ContinuousOn P D := hFD.clm_comp continuousOn_const
  have hsub : closedBall (0:ℂ) r ×ˢ C ⊆ D := by
    intro p hp
    refine ⟨?_,hCU hp.2⟩
    exact (mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.mp hp.1) hk).trans_lt hrk
  obtain ⟨M,hM⟩ := ((isCompact_closedBall (0:ℂ) r).prod hC).exists_bound_of_continuousOn (hP.mono hsub)
  refine ⟨r,max M 0,hr,le_max_right _ _,?_⟩
  intro z hz ε hε
  have hp : (ε,z) ∈ D := hsub ⟨hε,hz⟩
  have hd : DifferentiableAt ℝ F (ε,z) :=
    (hF.differentiableOn (by norm_num)).differentiableAt (hDo.mem_nhds hp)
  have hpz : DifferentiableAt ℝ (fun e : ℂ => (e,z)) ε :=
    differentiableAt_id.prodMk (differentiableAt_const z)
  have hsec : DifferentiableAt ℝ (fun e => F (e,z)) ε :=
    DifferentiableAt.comp (f := fun e : ℂ => (e,z)) (g := F) ε hd hpz
  have he : fderiv ℝ (fun e => F (e,z)) ε = P (ε,z) := by
    ext v
    rw [l613_fderiv_left hd]
    rfl
  refine ⟨hsec,?_⟩
  change ‖fderiv ℝ (fun e => F (e,z)) ε‖ ≤ max M 0
  rw [he]
  exact (hM (ε,z) ⟨hε,hz⟩).trans (le_max_left _ _)

end TakhtajanTeo
