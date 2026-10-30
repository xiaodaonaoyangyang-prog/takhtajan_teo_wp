import TakhtajanTeo.Ch2.FaberGramCorollary

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-! ## Mixed Green identity on the gap (`mg_` prefix) -/

/-- A smooth radial cutoff `0` on `‖z‖ ≤ a` and `1` on `‖z‖ ≥ b`. -/
theorem mg_cut {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ c : ℂ → ℂ, ContDiff ℝ 1 c ∧ (∀ z : ℂ, ‖z‖ ≤ a → c z = 0) ∧ (∀ z : ℂ, b ≤ ‖z‖ → c z = 1) := by
  have hden : 0 < b ^ 2 - a ^ 2 := by nlinarith
  refine ⟨fun z => ((Real.smoothTransition ((‖z‖ ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2)) : ℝ) : ℂ),
    ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ 1 (fun z : ℂ => (‖z‖ ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2)) :=
      (((contDiff_norm_sq ℝ).sub contDiff_const).div_const _)
    exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp h1)
  · intro z hz
    have : ‖z‖ ^ 2 - a ^ 2 ≤ 0 := by nlinarith [norm_nonneg z]
    show ((Real.smoothTransition ((‖z‖ ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2)) : ℝ) : ℂ) = 0
    rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg this hden.le)]
    simp
  · intro z hz
    have : b ^ 2 - a ^ 2 ≤ ‖z‖ ^ 2 - a ^ 2 := by nlinarith [norm_nonneg z]
    show ((Real.smoothTransition ((‖z‖ ^ 2 - a ^ 2) / (b ^ 2 - a ^ 2)) : ℝ) : ℂ) = 1
    rw [Real.smoothTransition.one_of_one_le ((one_le_div hden).mpr this)]
    simp

/-- Green's identity outside the circle `‖z‖ = R` for a `C¹` function on `{‖z‖ > 1}` with compact support. -/
theorem mg_green_exterior {Ψ : ℂ → ℂ} {R R2 : ℝ} (hR : 1 < R)
    (hΨ : ContDiffOn ℝ 1 Ψ {z : ℂ | 1 < ‖z‖}) (hsupp : ∀ z : ℂ, R2 ≤ ‖z‖ → Ψ z = 0) :
    (∮ z in C(0, R), Ψ z) = -2 * I * ∫ z in (ball (0 : ℂ) R)ᶜ, dzbar Ψ z := by
  obtain ⟨s1, hs1⟩ : ∃ s1 : ℝ, s1 = 1 + (R - 1) / 3 := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s2 : ℝ, s2 = 1 + 2 * (R - 1) / 3 := ⟨_, rfl⟩
  have hs1p : 1 < s1 := by rw [hs1]; linarith
  have hs12 : s1 < s2 := by rw [hs1, hs2]; linarith
  have hs2R : s2 < R := by rw [hs2]; linarith
  obtain ⟨c, hcs, hc0, hc1⟩ := mg_cut (by linarith : 0 < s1) hs12
  have hopen : IsOpen {z : ℂ | 1 < ‖z‖} := isOpen_lt continuous_const continuous_norm
  set Ψt : ℂ → ℂ := fun z => c z * Ψ z with hΨt
  have hΨtC : ContDiff ℝ 1 Ψt := by
    have hA : ContDiffOn ℝ 1 Ψt {z : ℂ | 1 < ‖z‖} := hcs.contDiffOn.mul hΨ
    have hB : ContDiffOn ℝ 1 Ψt (ball (0 : ℂ) s1) := by
      refine (contDiffOn_const (c := (0 : ℂ))).congr ?_
      intro z hz
      simp [hΨt, hc0 z (mem_ball_zero_iff.mp hz).le]
    have hU := hA.union_of_isOpen hB hopen isOpen_ball
    refine contDiffOn_univ.mp (hU.mono ?_)
    intro z _
    by_cases hz : 1 < ‖z‖
    · exact Or.inl hz
    · exact Or.inr (mem_ball_zero_iff.mpr (by linarith [not_lt.mp hz]))
  have hΨt0 : ∀ z : ℂ, R2 ≤ ‖z‖ → Ψt z = 0 := fun z hz => by simp [hΨt, hsupp z hz]
  -- compact support of `dzbar Ψt`
  have hdz0 : ∀ z : ℂ, R2 + 1 < ‖z‖ → dzbar Ψt z = 0 := by
    intro z hz
    have hev : Ψt =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm :
        IsOpen {u : ℂ | R2 + 1 < ‖u‖}).mem_nhds hz] with u hu
      exact hΨt0 u (by linarith [(show R2 + 1 < ‖u‖ from hu)])
    rw [dzbar_congr_of_eventuallyEq hev]
    simp [dzbar]
  have hint : Integrable (dzbar Ψt) := by
    refine Continuous.integrable_of_hasCompactSupport (continuous_dzbar hΨtC) ?_
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R2 + 1)) ?_
    intro z hz
    exact hdz0 z (by simpa [mem_closedBall_zero_iff, not_le] using hz)
  have hglob : ∫ w, dzbar Ψt w = 0 := by
    refine g2_green_global hΨtC hint ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop R2, eventually_gt_atTop 0] with r hr hr0
    symm
    rw [circleIntegral]
    have : ∀ θ : ℝ, Ψt (circleMap 0 r θ) = 0 := fun θ =>
      hΨt0 _ (by rw [norm_circleMap_zero, abs_of_pos hr0]; exact hr)
    simp [this]
  have hsplit := integral_add_compl (measurableSet_ball (x := (0 : ℂ)) (ε := R)) hint
  rw [hglob] at hsplit
  have hgreen := green_disc_dzbar_of_contDiffOn isOpen_univ hΨtC.contDiffOn (0 : ℂ)
    (by linarith : (0 : ℝ) ≤ R) (subset_univ _)
  have hcirc : (∮ z in C(0, R), Ψt z) = ∮ z in C(0, R), Ψ z := by
    rw [circleIntegral, circleIntegral]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [hΨt]
    rw [hc1 _ (by rw [norm_circleMap_zero, abs_of_pos (by linarith)]; linarith)]
    simp
  have hcompl : ∫ z in (ball (0 : ℂ) R)ᶜ, dzbar Ψt z = ∫ z in (ball (0 : ℂ) R)ᶜ, dzbar Ψ z := by
    refine setIntegral_congr_fun measurableSet_ball.compl (fun z hz => ?_)
    have hzR : R ≤ ‖z‖ := by simpa [not_lt] using hz
    have hev : Ψt =ᶠ[𝓝 z] Ψ := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm :
        IsOpen {u : ℂ | s2 < ‖u‖}).mem_nhds (show s2 < ‖z‖ by linarith)] with u hu
      simp only [hΨt]
      rw [hc1 u (le_of_lt (show s2 < ‖u‖ from hu)), one_mul]
    exact dzbar_congr_of_eventuallyEq hev
  rw [← hcirc, hgreen, ← hcompl]
  have h2 : ∫ z in ball (0 : ℂ) R, dzbar Ψt z = -∫ z in (ball (0 : ℂ) R)ᶜ, dzbar Ψt z := by
    linear_combination hsplit
  rw [h2]
  ring


/-- Green's identity outside `f(closedBall 0 ρ)` for a `C¹` (off `0`) compactly supported `Φ`, pulled back by `f`. -/
theorem mg_green_fchart {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    (hf0 : f 0 = 0) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {Φ : ℂ → ℂ}
    (hΦ : ContDiffOn ℝ 1 Φ {0}ᶜ) {R0 : ℝ} (hsupp : ∀ w : ℂ, R0 ≤ ‖w‖ → Φ w = 0) :
    IntegrableOn (dzbar Φ) (f '' closedBall (0 : ℂ) ρ)ᶜ ∧ ((∮ z in C(0, ρ), Φ (f z) * deriv f z) =
      -2 * I * ∫ w in (f '' closedBall (0 : ℂ) ρ)ᶜ, dzbar Φ w) := by
  have hUo : IsOpen unitDisc := isOpen_ball
  have hcbD : closedBall (0 : ℂ) ρ ⊆ unitDisc := by
    intro z hz
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hρ1)
  have hbD : ball (0 : ℂ) ρ ⊆ unitDisc := ball_subset_closedBall.trans hcbD
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hfD := RMT.differentiableOn_invFunOn_of_injOn hUo hf hi
  have hfDopen : IsOpen (f '' unitDisc) := hfD.1
  set finv := Function.invFunOn f unitDisc with hfinv
  have hleft : ∀ z ∈ unitDisc, finv (f z) = z := fun z hz => hi.leftInvOn_invFunOn hz
  obtain ⟨c, hcs, hc0, hc1⟩ := mg_cut (by linarith : 0 < ρ / 2) (by linarith : ρ / 2 < ρ)
  -- the cutoff in the plane
  let χ : ℂ → ℂ := fun w => if w ∈ f '' ball (0 : ℂ) ρ then c (finv w) else 1
  let Φt : ℂ → ℂ := fun w => χ w * Φ w
  have hballopen : ∀ r : ℝ, r ≤ 1 → IsOpen (f '' ball (0 : ℂ) r) := fun r hr =>
    (RMT.differentiableOn_invFunOn_of_injOn isOpen_ball (hf.mono (ball_subset_ball hr))
      (hi.mono (ball_subset_ball hr))).1
  have hKcompact : IsCompact (f '' closedBall (0 : ℂ) ρ) :=
    (isCompact_closedBall (0 : ℂ) ρ).image_of_continuousOn (hf.continuousOn.mono hcbD)
  have hKclosed : IsClosed (f '' closedBall (0 : ℂ) ρ) := hKcompact.isClosed
  have hKsubD : f '' closedBall (0 : ℂ) ρ ⊆ f '' unitDisc := image_mono hcbD
  have hballsub : f '' ball (0 : ℂ) ρ ⊆ f '' closedBall (0 : ℂ) ρ := image_mono ball_subset_closedBall
  have hχD : ∀ w ∈ f '' unitDisc, χ w = c (finv w) := by
    rintro w ⟨z, hz, rfl⟩
    simp only [χ]
    split_ifs with hm
    · rfl
    · have : ρ ≤ ‖z‖ := by
        by_contra hlt
        push_neg at hlt
        exact hm ⟨z, mem_ball_zero_iff.mpr hlt, rfl⟩
      rw [hleft z hz, hc1 z this]
  have hA1 : IsOpen (f '' ball (0 : ℂ) (ρ / 2)) := hballopen (ρ / 2) (by linarith)
  have hA2 : IsOpen (f '' unitDisc ∩ {0}ᶜ) := hfDopen.inter isOpen_compl_singleton
  have hA3 : IsOpen (f '' closedBall (0 : ℂ) ρ)ᶜ := hKclosed.isOpen_compl
  have h0K : (0 : ℂ) ∈ f '' closedBall (0 : ℂ) ρ := ⟨0, by simp [hρ0.le], hf0⟩
  have hP1 : ContDiffOn ℝ 1 Φt (f '' ball (0 : ℂ) (ρ / 2)) := by
    refine (contDiffOn_const (c := (0 : ℂ))).congr ?_
    rintro w ⟨z, hz, rfl⟩
    have hzn : ‖z‖ < ρ / 2 := mem_ball_zero_iff.mp hz
    have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr (by linarith)
    simp only [Φt]
    rw [hχD _ ⟨z, hzD, rfl⟩, hleft z hzD, hc0 z hzn.le, zero_mul]
  have hP2 : ContDiffOn ℝ 1 Φt (f '' unitDisc ∩ {0}ᶜ) := by
    have hfinvs : ContDiffOn ℝ 1 finv (f '' unitDisc) :=
      (hfD.2.contDiffOn hfDopen).restrict_scalars ℝ
    have hcf : ContDiffOn ℝ 1 (fun w => c (finv w)) (f '' unitDisc) := hcs.comp_contDiffOn hfinvs
    refine ((hcf.mono inter_subset_left).mul (hΦ.mono inter_subset_right)).congr ?_
    intro w hw
    simp only [Φt]
    rw [hχD w hw.1]
  have hP3 : ContDiffOn ℝ 1 Φt (f '' closedBall (0 : ℂ) ρ)ᶜ := by
    have hsub : (f '' closedBall (0 : ℂ) ρ)ᶜ ⊆ {0}ᶜ := by
      intro w hw h0
      exact hw (by rw [mem_singleton_iff.mp h0]; exact h0K)
    refine (hΦ.mono hsub).congr ?_
    intro w hw
    have : w ∉ f '' ball (0 : ℂ) ρ := fun hm => hw (hballsub hm)
    simp only [Φt, χ, if_neg this, one_mul]
  have hΦt : ContDiff ℝ 1 Φt := by
    have hU := ((hP1.union_of_isOpen hP2 hA1 hA2).union_of_isOpen hP3 (hA1.union hA2) hA3)
    refine contDiffOn_univ.mp (hU.mono ?_)
    intro w _
    by_cases hw3 : w ∈ (f '' closedBall (0 : ℂ) ρ)ᶜ
    · exact Or.inr hw3
    · have hwK : w ∈ f '' closedBall (0 : ℂ) ρ := not_not.mp hw3
      by_cases hw0 : w = 0
      · refine Or.inl (Or.inl ?_)
        exact ⟨0, by simp [hρ0], by rw [hw0, hf0]⟩
      · exact Or.inl (Or.inr ⟨hKsubD hwK, hw0⟩)
  have hΦt0 : ∀ w : ℂ, R0 ≤ ‖w‖ → Φt w = 0 := fun w hw => by simp [Φt, hsupp w hw]
  have hdz0 : ∀ w : ℂ, R0 < ‖w‖ → dzbar Φt w = 0 := by
    intro w hw
    have hev : Φt =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm :
        IsOpen {u : ℂ | R0 < ‖u‖}).mem_nhds hw] with u hu
      exact hΦt0 u (le_of_lt (show R0 < ‖u‖ from hu))
    rw [dzbar_congr_of_eventuallyEq hev]
    simp [dzbar]
  have hint : Integrable (dzbar Φt) := by
    refine Continuous.integrable_of_hasCompactSupport (continuous_dzbar hΦt) ?_
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (|R0| + 1)) ?_
    intro w hw
    refine hdz0 w ?_
    have : |R0| + 1 < ‖w‖ := by simpa [mem_closedBall_zero_iff, not_le] using hw
    linarith [le_abs_self R0]
  have hglob : ∫ w, dzbar Φt w = 0 := by
    refine g2_green_global hΦt hint ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop R0, eventually_gt_atTop 0] with r hr hr0
    symm
    rw [circleIntegral]
    have : ∀ θ : ℝ, Φt (circleMap 0 r θ) = 0 := fun θ =>
      hΦt0 _ (by rw [norm_circleMap_zero, abs_of_pos hr0]; exact hr)
    simp [this]
  have hsplit := integral_add_compl hKclosed.measurableSet hint
  have hcompl : ∫ x in (f '' closedBall (0 : ℂ) ρ)ᶜ, dzbar Φt x =
      ∫ x in (f '' closedBall (0 : ℂ) ρ)ᶜ, dzbar Φ x := by
    refine setIntegral_congr_fun hKclosed.measurableSet.compl (fun w hw => ?_)
    have hev : Φt =ᶠ[𝓝 w] Φ := by
      filter_upwards [hA3.mem_nhds hw] with u hu
      have : u ∉ f '' ball (0 : ℂ) ρ := fun hm => hu (hballsub hm)
      simp only [Φt, χ, if_neg this, one_mul]
    exact dzbar_congr_of_eventuallyEq hev
  -- the pull-back to the disk
  set Ψ : ℂ → ℂ := fun z => Φt (f z) * deriv f z with hΨ
  have hΨs : ContDiffOn ℝ 1 Ψ unitDisc := by
    have h1 : ContDiffOn ℝ 1 (fun z => Φt (f z)) unitDisc :=
      hΦt.comp_contDiffOn ((hf.contDiffOn hUo).restrict_scalars ℝ)
    have h2 : ContDiffOn ℝ 1 (deriv f) unitDisc :=
      ((hf.deriv hUo).contDiffOn hUo).restrict_scalars ℝ
    exact h1.mul h2
  have hpt : ∀ z ∈ closedBall (0 : ℂ) ρ, |(fderiv ℝ f z).det| • dzbar Φt (f z) = dzbar Ψ z := by
    intro z hz
    have hzD := hcbD hz
    have hfC : DifferentiableAt ℂ f z := hf.differentiableAt (hUo.mem_nhds hzD)
    have hfR : DifferentiableAt ℝ f z := hfC.restrictScalars ℝ
    have hdet : (fderiv ℝ f z).det = ‖deriv f z‖ ^ 2 := by
      have h1 := det_fderiv_eq_jacobian hfR
      rw [jacobian, (cauchyRiemann_iff.1 hfC).2, dz_eq_deriv hfC, norm_zero] at h1
      rw [ContinuousLinearMap.det, h1]
      ring
    have hd1 : DifferentiableAt ℂ (deriv f) z :=
      (hf.deriv hUo).differentiableAt (hUo.mem_nhds hzD)
    have hΦR : DifferentiableAt ℝ Φt (f z) := (hΦt.differentiable one_ne_zero).differentiableAt
    have hcomp : DifferentiableAt ℝ (fun u => Φt (f u)) z := hΦR.comp z hfR
    show _ = dzbar (fun u => Φt (f u) * deriv f u) z
    rw [dzbar_mul hcomp (hd1.restrictScalars ℝ),
      (cauchyRiemann_iff.1 hd1).2, g2_dzbar_comp hΦR hfC, hdet,
      abs_of_nonneg (by positivity), Complex.real_smul, mul_zero, zero_add,
      ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_closedBall (x := (0 : ℂ)) (ε := ρ)) (f' := fun x => fderiv ℝ f x)
    (fun x hx => ((hf.differentiableAt (hUo.mem_nhds (hcbD hx))).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt)
    (hi.mono hcbD) (dzbar Φt)
  have hKint : ∫ x in f '' closedBall (0 : ℂ) ρ, dzbar Φt x = ∫ z in closedBall (0 : ℂ) ρ, dzbar Ψ z := by
    rw [hcov]
    exact setIntegral_congr_fun measurableSet_closedBall (fun z hz => hpt z hz)
  have hsph : volume (sphere (0 : ℂ) ρ) = 0 := Measure.addHaar_sphere volume 0 ρ
  have hae : ball (0 : ℂ) ρ =ᵐ[volume] closedBall (0 : ℂ) ρ := by
    rw [← ball_union_sphere]
    exact (union_ae_eq_left_iff_ae_subset.mpr (ae_le_set.mpr (measure_mono_null diff_subset hsph))).symm
  have hball : ∫ z in closedBall (0 : ℂ) ρ, dzbar Ψ z = ∫ z in ball (0 : ℂ) ρ, dzbar Ψ z :=
    (setIntegral_congr_set hae).symm
  have hgreen := green_disc_dzbar_of_contDiffOn hUo hΨs (0 : ℂ) hρ0.le hcbD
  have hcirc : (∮ z in C(0, ρ), Ψ z) = ∮ z in C(0, ρ), Φ (f z) * deriv f z := by
    rw [circleIntegral, circleIntegral]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hz : ‖circleMap 0 ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos hρ0]
    have hzD : circleMap 0 ρ θ ∈ unitDisc := hcbD (mem_closedBall_zero_iff.mpr hz.le)
    have hχ : χ (f (circleMap 0 ρ θ)) = 1 := by
      simp only [χ]
      rw [if_neg]
      rintro ⟨u, hu, hue⟩
      have := hi (hbD hu) hzD hue
      rw [this] at hu
      rw [mem_ball_zero_iff, hz] at hu
      exact lt_irrefl _ hu
    simp only [hΨ, Φt]
    rw [hχ, one_mul]
  refine ⟨?_, ?_⟩
  · have h1 : IntegrableOn (dzbar Φt) (f '' closedBall (0 : ℂ) ρ)ᶜ := hint.integrableOn
    refine h1.congr_fun (fun w hw => ?_) hKclosed.measurableSet.compl
    have hev : Φt =ᶠ[𝓝 w] Φ := by
      filter_upwards [hA3.mem_nhds hw] with u hu
      have : u ∉ f '' ball (0 : ℂ) ρ := fun hm => hu (hballsub hm)
      simp only [Φt, χ, if_neg this, one_mul]
    exact dzbar_congr_of_eventuallyEq hev
  · rw [hKint, hball, hcompl, hglob] at hsplit
    rw [← hcirc, hgreen]
    linear_combination 2 * I * hsplit


/-- The image of a closed far exterior of a map univalent at `∞` is closed. -/
theorem mg_image_closed {g : ℂ → ℂ} (hg : IsUnivalentAtInfty g) {R : ℝ} (hR : 1 < R) :
    IsClosed (g '' {z : ℂ | R ≤ ‖z‖}) := by
  have hS : {z : ℂ | R ≤ ‖z‖} ⊆ unitDiscExterior := fun z hz => lt_of_lt_of_le hR hz
  have hc : ContinuousOn g unitDiscExterior := hg.1.continuousOn
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have hev : ∀ᶠ z in cocompact ℂ, ‖w‖ + 1 < ‖g z‖ :=
    (tendsto_norm_cocompact_atTop.comp hg.2.2).eventually_gt_atTop _
  obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hev
  obtain ⟨M, hM⟩ := ht.isBounded.subset_closedBall (0 : ℂ)
  have hbig : ∀ z : ℂ, M < ‖z‖ → ‖w‖ + 1 < ‖g z‖ := by
    intro z hz
    apply hts
    intro hzt
    have := mem_closedBall_zero_iff.mp (hM hzt)
    linarith
  set K : Set ℂ := {z : ℂ | R ≤ ‖z‖} ∩ closedBall (0 : ℂ) M with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) M).inter_left (isClosed_le continuous_const continuous_norm)
  have hgK : IsCompact (g '' K) := hKc.image_of_continuousOn (hc.mono (inter_subset_left.trans hS))
  have hwK : w ∈ closure (g '' K) := by
    rw [mem_closure_iff_nhds]
    intro t ht
    have ht' : t ∩ ball w 1 ∈ 𝓝 w := inter_mem ht (ball_mem_nhds w one_pos)
    obtain ⟨u, ⟨hut, hub⟩, z, hz, rfl⟩ := mem_closure_iff_nhds.mp hw _ ht'
    have hzM : ‖z‖ ≤ M := by
      by_contra hlt
      have := hbig z (not_le.mp hlt)
      have h2 : dist (g z) w < 1 := mem_ball.mp hub
      have h3 : ‖g z‖ ≤ ‖w‖ + dist (g z) w := by
        rw [dist_eq_norm] at *
        calc ‖g z‖ = ‖(g z - w) + w‖ := by ring_nf
          _ ≤ ‖g z - w‖ + ‖w‖ := norm_add_le _ _
          _ = ‖w‖ + ‖g z - w‖ := add_comm _ _
      linarith
    exact ⟨g z, hut, z, ⟨hz, mem_closedBall_zero_iff.mpr hzM⟩, rfl⟩
  rw [hgK.isClosed.closure_eq] at hwK
  obtain ⟨z, hz, hzw⟩ := hwK
  exact ⟨z, hz.1, hzw⟩


/-- Cutoff on the `g`-chart: `χ = cg ∘ g⁻¹` on `g(𝔻*)` and `1` elsewhere, with `cg = 1` on `‖z‖ ≤ R` and
`cg = 0` on `‖z‖ ≥ 2R`. -/
theorem mg_gcut {g : ℂ → ℂ} (hg : IsUnivalentAtInfty g) {R : ℝ} (hR : 1 < R) :
    ∃ cg χ : ℂ → ℂ, ContDiff ℝ 1 cg ∧ (∀ z : ℂ, ‖z‖ ≤ R → cg z = 1) ∧ (∀ z : ℂ, 2 * R ≤ ‖z‖ → cg z = 0) ∧
      ContDiff ℝ 1 χ ∧ (∀ z : ℂ, 1 < ‖z‖ → χ (g z) = cg z) ∧
      (∀ w : ℂ, w ∉ g '' unitDiscExterior → χ w = 1) := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  obtain ⟨c, hcs, hc0, hc1⟩ := mg_cut (by linarith : 0 < R) (by linarith : R < 2 * R)
  set cg : ℂ → ℂ := fun z => 1 - c z with hcg
  have hcgs : ContDiff ℝ 1 cg := contDiff_const.sub hcs
  have hgo := RMT.differentiableOn_invFunOn_of_injOn hEo hg.1 hg.2.1
  have hgopen : IsOpen (g '' unitDiscExterior) := hgo.1
  set ginv := Function.invFunOn g unitDiscExterior with hginv
  have hleft : ∀ z ∈ unitDiscExterior, ginv (g z) = z := fun z hz => hg.2.1.leftInvOn_invFunOn hz
  let χ : ℂ → ℂ := fun w => if w ∈ g '' unitDiscExterior then cg (ginv w) else 1
  have hχg : ∀ z : ℂ, 1 < ‖z‖ → χ (g z) = cg z := by
    intro z hz
    have hzE : z ∈ unitDiscExterior := hz
    simp only [χ]
    rw [if_pos ⟨z, hzE, rfl⟩, hleft z hzE]
  have hχ1 : ∀ w : ℂ, w ∉ g '' unitDiscExterior → χ w = 1 := fun w hw => by simp only [χ]; rw [if_neg hw]
  have hKclosed := mg_image_closed hg hR
  have hA : ContDiffOn ℝ 1 χ (g '' unitDiscExterior) := by
    have hginvs : ContDiffOn ℝ 1 ginv (g '' unitDiscExterior) :=
      (hgo.2.contDiffOn hgopen).restrict_scalars ℝ
    refine (hcgs.comp_contDiffOn hginvs).congr ?_
    intro w hw
    simp only [χ]
    rw [if_pos hw]
    rfl
  have hB : ContDiffOn ℝ 1 χ (g '' {z : ℂ | R ≤ ‖z‖})ᶜ := by
    refine (contDiffOn_const (c := (1 : ℂ))).congr ?_
    intro w hw
    by_cases hwE : w ∈ g '' unitDiscExterior
    · obtain ⟨z, hz, rfl⟩ := hwE
      have hzR : ‖z‖ < R := by
        by_contra hge
        exact hw ⟨z, not_lt.mp hge, rfl⟩
      rw [hχg z hz, hcg]
      simp only
      rw [hc0 z hzR.le]
      ring
    · exact hχ1 w hwE
  refine ⟨cg, χ, hcgs, ?_, ?_, ?_, hχg, hχ1⟩
  · intro z hz
    simp only [hcg]
    rw [hc0 z hz]; ring
  · intro z hz
    simp only [hcg]
    rw [hc1 z hz]; ring
  · have hU := hA.union_of_isOpen hB hgopen hKclosed.isOpen_compl
    refine contDiffOn_univ.mp (hU.mono ?_)
    intro w _
    by_cases hw : w ∈ g '' unitDiscExterior
    · exact Or.inl hw
    · refine Or.inr (fun hwK => hw ?_)
      obtain ⟨z, hz, rfl⟩ := hwK
      exact ⟨z, lt_of_lt_of_le hR hz, rfl⟩


/-- Far points are values of `g` at large arguments. -/
theorem mg_far_exterior {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {T : ℝ} (hT : 0 < T) :
    ∃ R1 : ℝ, ∀ w : ℂ, R1 < ‖w‖ → ∃ z : ℂ, T ≤ ‖z‖ ∧ g z = w := by
  obtain ⟨φ, b, hφd, hφi, hφ0, hφ1, hb, hbg, hg⟩ := g1_inverted_exterior h
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (1 / 2 : ℝ) (1 / T) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact lt_min (by norm_num) (by positivity)
  have hr1 : r ≤ 1 / 2 := by rw [hr]; exact min_le_left _ _
  have hrT : r ≤ 1 / T := by rw [hr]; exact min_le_right _ _
  have hopen : IsOpen (φ '' ball (0 : ℂ) r) :=
    (RMT.differentiableOn_invFunOn_of_injOn isOpen_ball
      (hφd.mono (ball_subset_ball (by linarith))) (hφi.mono (ball_subset_ball (by linarith)))).1
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hopen.mem_nhds (show (0 : ℂ) ∈ φ '' ball (0 : ℂ) r from ⟨0, mem_ball_self hr0, hφ0⟩))
  refine ⟨‖b‖ / δ, fun w hw => ?_⟩
  have hwn : 0 < ‖w‖ := (div_nonneg (norm_nonneg b) hδ.le).trans_lt hw
  have hw0 : w ≠ 0 := norm_pos_iff.mp hwn
  have hnear : b / w ∈ ball (0 : ℂ) δ := by
    apply mem_ball_zero_iff.mpr
    rw [norm_div]
    apply (div_lt_iff₀ hwn).mpr
    have hh := (div_lt_iff₀ hδ).mp hw
    nlinarith
  obtain ⟨s, hs, hφs⟩ := hball hnear
  have hs0 : s ≠ 0 := by
    intro he
    have hbw : b / w ≠ 0 := div_ne_zero hb hw0
    apply hbw
    simpa [he, hφ0] using hφs.symm
  have hsn : ‖s‖ < r := mem_ball_zero_iff.mp hs
  have hsD : s ∈ unitDisc := mem_ball_zero_iff.mpr (by linarith)
  refine ⟨s⁻¹, ?_, ?_⟩
  · rw [norm_inv]
    have hsp : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    rw [le_inv_comm₀ hT hsp, ← one_div]
    exact hsn.le.trans hrT
  · have hh := hg s hsD hs0
    rw [one_div, hφs] at hh
    rw [hh]
    field_simp

theorem mg_circle_eq {F : ℂ → ℂ} {r : ℝ} :
    (∮ z in C(0, r), F z) = I * ∫ θ in (0 : ℝ)..2 * π, F (circleMap 0 r θ) * circleMap 0 r θ := by
  rw [circleIntegral, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [smul_eq_mul]
  rw [deriv_circleMap]
  ring

/-- Green's identity inside `g{‖z‖ ≥ R}` for a `C¹` `Φ` (on `g(𝔻*)`), pulled back by `g`. -/
theorem mg_green_gchart {g : ℂ → ℂ} (hg : IsUnivalentAtInfty g) {R : ℝ} (hR : 1 < R) {Φ : ℂ → ℂ}
    (hΦ : ContDiffOn ℝ 1 Φ (g '' unitDiscExterior)) (hsupp : ∀ z : ℂ, 2 * R ≤ ‖z‖ → Φ (g z) = 0) :
    (∮ z in C(0, R), Φ (g z) * deriv g z) =
      -2 * I * ∫ w in g '' {z : ℂ | R ≤ ‖z‖}, dzbar Φ w := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hgo := RMT.differentiableOn_invFunOn_of_injOn hEo hg.1 hg.2.1
  have hgopen : IsOpen (g '' unitDiscExterior) := hgo.1
  set Ψ : ℂ → ℂ := fun z => Φ (g z) * deriv g z with hΨ
  have hΨs : ContDiffOn ℝ 1 Ψ {z : ℂ | 1 < ‖z‖} := by
    have h1 : ContDiffOn ℝ 1 (fun z => Φ (g z)) unitDiscExterior :=
      hΦ.comp ((hg.1.contDiffOn hEo).restrict_scalars ℝ) (fun z hz => ⟨z, hz, rfl⟩)
    have h2 : ContDiffOn ℝ 1 (deriv g) unitDiscExterior :=
      ((hg.1.deriv hEo).contDiffOn hEo).restrict_scalars ℝ
    exact h1.mul h2
  have hΨ0 : ∀ z : ℂ, 2 * R ≤ ‖z‖ → Ψ z = 0 := fun z hz => by simp [hΨ, hsupp z hz]
  have hgreen := mg_green_exterior hR hΨs hΨ0
  have hS : {z : ℂ | R ≤ ‖z‖} = (ball (0 : ℂ) R)ᶜ := by
    ext z; simp [not_lt]
  have hSm : MeasurableSet {z : ℂ | R ≤ ‖z‖} := by rw [hS]; exact measurableSet_ball.compl
  have hSE : {z : ℂ | R ≤ ‖z‖} ⊆ unitDiscExterior := fun z hz => lt_of_lt_of_le hR hz
  have hpt : ∀ z ∈ {z : ℂ | R ≤ ‖z‖}, |(fderiv ℝ g z).det| • dzbar Φ (g z) = dzbar Ψ z := by
    intro z hz
    have hzE := hSE hz
    have hgC : DifferentiableAt ℂ g z := hg.1.differentiableAt (hEo.mem_nhds hzE)
    have hgR : DifferentiableAt ℝ g z := hgC.restrictScalars ℝ
    have hdet : (fderiv ℝ g z).det = ‖deriv g z‖ ^ 2 := by
      have h1 := det_fderiv_eq_jacobian hgR
      rw [jacobian, (cauchyRiemann_iff.1 hgC).2, dz_eq_deriv hgC, norm_zero] at h1
      rw [ContinuousLinearMap.det, h1]
      ring
    have hd1 : DifferentiableAt ℂ (deriv g) z :=
      (hg.1.deriv hEo).differentiableAt (hEo.mem_nhds hzE)
    have hΦR : DifferentiableAt ℝ Φ (g z) :=
      (hΦ.differentiableOn one_ne_zero).differentiableAt (hgopen.mem_nhds ⟨z, hzE, rfl⟩)
    have hcomp : DifferentiableAt ℝ (fun u => Φ (g u)) z := hΦR.comp z hgR
    show _ = dzbar (fun u => Φ (g u) * deriv g u) z
    rw [dzbar_mul hcomp (hd1.restrictScalars ℝ),
      (cauchyRiemann_iff.1 hd1).2, g2_dzbar_comp hΦR hgC, hdet,
      abs_of_nonneg (by positivity), Complex.real_smul, mul_zero, zero_add,
      ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume hSm (f' := fun x => fderiv ℝ g x)
    (fun x hx => ((hg.1.differentiableAt (hEo.mem_nhds (hSE hx))).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt)
    (hg.2.1.mono hSE) (dzbar Φ)
  have hint : ∫ w in g '' {z : ℂ | R ≤ ‖z‖}, dzbar Φ w = ∫ z in (ball (0 : ℂ) R)ᶜ, dzbar Ψ z := by
    rw [hcov, ← hS]
    exact setIntegral_congr_fun hSm (fun z hz => hpt z hz)
  rw [hint]
  exact hgreen


/-- (M1) Green identity on the gap for any `U` holomorphic off `0`. -/
theorem mg_gap_green {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {U : ℂ → ℂ} (hU : DifferentiableOn ℂ U {0}ᶜ) :
    (((∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ, ‖deriv U w‖ ^ 2 : ℝ)) : ℂ) =
      -(1 / 2 : ℂ) * (∫ θ in (0 : ℝ)..2 * π,
        conj (U (f (circleMap 0 ρ θ))) * deriv (fun z => U (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ) +
      (1 / 2 : ℂ) * (∫ θ in (0 : ℝ)..2 * π,
        conj (U (g (circleMap 0 (1 / ρ) θ))) * deriv (fun z => U (g z)) (circleMap 0 (1 / ρ) θ) *
          circleMap 0 (1 / ρ) θ) := by
  have h' := h
  obtain ⟨hfd, hfi, hf0, hf1, hgu, hdisj⟩ := h
  have hR : 1 < 1 / ρ := one_lt_one_div hρ0 hρ1
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hUo : IsOpen unitDisc := isOpen_ball
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hg0 : ∀ w ∈ g '' unitDiscExterior, w ≠ 0 := by
    intro w hw hw0
    exact Set.disjoint_left.mp hdisj ⟨0, h0D, by rw [hf0]; exact hw0.symm⟩ hw
  obtain ⟨cg, χ, hcg, hcg1, hcg0, hχ, hχg, hχ1⟩ := mg_gcut hgu hR
  -- the integrand
  have hU' : DifferentiableOn ℂ (deriv U) {0}ᶜ := hU.deriv isOpen_compl_singleton
  have hUs : ContDiffOn ℝ 1 U {0}ᶜ := (hU.contDiffOn isOpen_compl_singleton).restrict_scalars ℝ
  have hUs' : ContDiffOn ℝ 1 (deriv U) {0}ᶜ := (hU'.contDiffOn isOpen_compl_singleton).restrict_scalars ℝ
  set W : ℂ → ℂ := fun w => conj (U w) * deriv U w with hW
  have hWs : ContDiffOn ℝ 1 W {0}ᶜ :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hUs).mul hUs'
  set Φ : ℂ → ℂ := fun w => χ w * W w with hΦ
  have hΦs : ContDiffOn ℝ 1 Φ {0}ᶜ := hχ.contDiffOn.mul hWs
  have hgsub : g '' unitDiscExterior ⊆ {0}ᶜ := fun w hw => hg0 w hw
  have hgz : ∀ z : ℂ, 1 < ‖z‖ → g z ≠ 0 := fun z hz => hg0 _ ⟨z, hz, rfl⟩
  -- far support
  obtain ⟨R1, hR1⟩ := mg_far_exterior h' (T := 2 * (1 / ρ)) (by positivity)
  have hfar : ∀ w : ℂ, |R1| + 1 ≤ ‖w‖ → Φ w = 0 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hR1 w (by linarith [le_abs_self R1])
    have hz1 : 1 < ‖z‖ := by linarith
    simp only [hΦ]
    rw [hχg z hz1, hcg0 z hz]
    simp
  obtain ⟨hFint, hFeq⟩ := mg_green_fchart hfd hfi hf0 hρ0 hρ1 hΦs hfar
  have hG := mg_green_gchart hgu hR (Φ := Φ) (hΦs.mono hgsub) (fun z hz => by
    have hz1 : 1 < ‖z‖ := by linarith
    simp only [hΦ]
    rw [hχg z hz1, hcg0 z hz]
    simp)
  -- regions
  set Kf : Set ℂ := f '' closedBall (0 : ℂ) ρ with hKf
  set Kg : Set ℂ := g '' {z : ℂ | 1 / ρ ≤ ‖z‖} with hKg
  have hKfc : IsCompact Kf := (isCompact_closedBall (0 : ℂ) ρ).image_of_continuousOn
    (hfd.continuousOn.mono (fun z hz => mem_ball_zero_iff.mpr
      (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hρ1)))
  have hKgc : IsClosed Kg := mg_image_closed hgu hR
  have hdKfKg : Disjoint Kf Kg := by
    rw [Set.disjoint_left]
    rintro w ⟨u, hu, rfl⟩ ⟨z, hz, hzu⟩
    have huD : u ∈ unitDisc := mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hu) hρ1)
    exact Set.disjoint_left.mp hdisj ⟨u, huD, rfl⟩ ⟨z, lt_of_lt_of_le hR hz, hzu⟩
  have hunion : (Kf ∪ Kg)ᶜ ∪ Kg = Kfᶜ := by
    ext w
    simp only [mem_union, mem_compl_iff]
    constructor
    · rintro (h1 | h1)
      · exact fun hf => h1 (Or.inl hf)
      · exact fun hf => Set.disjoint_left.mp hdKfKg hf h1
    · intro h1
      by_cases hw : w ∈ Kg
      · exact Or.inr hw
      · exact Or.inl (fun hh => hh.elim h1 hw)
  have hdisj2 : Disjoint (Kf ∪ Kg)ᶜ Kg := by
    rw [Set.disjoint_left]
    intro w hw hwg
    exact hw (Or.inr hwg)
  have hKgm : MeasurableSet Kg := hKgc.measurableSet
  have hGapm : MeasurableSet (Kf ∪ Kg)ᶜ := (hKfc.isClosed.union hKgc).measurableSet.compl
  have hint1 : IntegrableOn (dzbar Φ) (Kf ∪ Kg)ᶜ := by
    refine hFint.mono_set ?_
    rw [← hunion]; exact subset_union_left
  have hint2 : IntegrableOn (dzbar Φ) Kg := by
    refine hFint.mono_set ?_
    rw [← hunion]; exact subset_union_right
  have hsplit : ∫ w in Kfᶜ, dzbar Φ w = (∫ w in (Kf ∪ Kg)ᶜ, dzbar Φ w) + ∫ w in Kg, dzbar Φ w := by
    rw [← hunion]
    exact setIntegral_union hdisj2 hKgm hint1 hint2
  -- the gap integral
  have hgap : ∫ w in (Kf ∪ Kg)ᶜ, dzbar Φ w = (((∫ w in (Kf ∪ Kg)ᶜ, ‖deriv U w‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun hGapm (fun w hw => ?_)
    have hw0 : w ≠ 0 := by
      intro h0
      exact hw (Or.inl ⟨0, by simp [hρ0.le], by rw [hf0, h0]⟩)
    have hev : Φ =ᶠ[𝓝 w] W := by
      filter_upwards [(hKfc.isClosed.union hKgc).isOpen_compl.mem_nhds hw] with u hu
      have hχu : χ u = 1 := by
        by_cases hug : u ∈ g '' unitDiscExterior
        · obtain ⟨z, hz, rfl⟩ := hug
          have hzR : ‖z‖ < 1 / ρ := by
            by_contra hge
            exact hu (Or.inr ⟨z, not_lt.mp hge, rfl⟩)
          rw [hχg z hz, hcg1 z hzR.le]
        · exact hχ1 u hug
      simp only [hΦ, hχu, one_mul]
    rw [dzbar_congr_of_eventuallyEq hev]
    exact g2_dzbar_conj_mul (hU.differentiableAt (isOpen_compl_singleton.mem_nhds hw0))
      (hU'.differentiableAt (isOpen_compl_singleton.mem_nhds hw0))
  -- boundary terms
  have hfb : (∮ z in C(0, ρ), Φ (f z) * deriv f z) = I * ∫ θ in (0 : ℝ)..2 * π,
      conj (U (f (circleMap 0 ρ θ))) * deriv (fun z => U (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ := by
    rw [mg_circle_eq]
    congr 1
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hz : ‖circleMap 0 ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos hρ0]
    have hzD : circleMap 0 ρ θ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hz]; exact hρ1)
    have hz0 : circleMap 0 ρ θ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz; exact hρ0.ne' hz.symm
    have hfz0 : f (circleMap 0 ρ θ) ≠ 0 := fun h0 =>
      hz0 (hfi hzD h0D (by rw [h0, hf0]))
    have hχf : χ (f (circleMap 0 ρ θ)) = 1 :=
      hχ1 _ (fun hm => Set.disjoint_left.mp hdisj ⟨_, hzD, rfl⟩ hm)
    have hUd : DifferentiableAt ℂ U (f (circleMap 0 ρ θ)) :=
      hU.differentiableAt (isOpen_compl_singleton.mem_nhds hfz0)
    have hfdz : DifferentiableAt ℂ f (circleMap 0 ρ θ) := hfd.differentiableAt (hUo.mem_nhds hzD)
    have hch : deriv (fun z => U (f z)) (circleMap 0 ρ θ) =
        deriv U (f (circleMap 0 ρ θ)) * deriv f (circleMap 0 ρ θ) := deriv_comp _ hUd hfdz
    simp only [hΦ, hW]
    rw [hχf, hch]
    ring
  have hgb : (∮ z in C(0, 1 / ρ), Φ (g z) * deriv g z) = I * ∫ θ in (0 : ℝ)..2 * π,
      conj (U (g (circleMap 0 (1 / ρ) θ))) * deriv (fun z => U (g z)) (circleMap 0 (1 / ρ) θ) *
        circleMap 0 (1 / ρ) θ := by
    rw [mg_circle_eq]
    congr 1
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hz : ‖circleMap 0 (1 / ρ) θ‖ = 1 / ρ := by rw [norm_circleMap_zero, abs_of_pos (by positivity)]
    have hz1 : 1 < ‖circleMap 0 (1 / ρ) θ‖ := by rw [hz]; exact hR
    have hgz0 := hgz _ hz1
    have hUd : DifferentiableAt ℂ U (g (circleMap 0 (1 / ρ) θ)) :=
      hU.differentiableAt (isOpen_compl_singleton.mem_nhds hgz0)
    have hgdz : DifferentiableAt ℂ g (circleMap 0 (1 / ρ) θ) := hgu.1.differentiableAt (hEo.mem_nhds hz1)
    have hch : deriv (fun z => U (g z)) (circleMap 0 (1 / ρ) θ) =
        deriv U (g (circleMap 0 (1 / ρ) θ)) * deriv g (circleMap 0 (1 / ρ) θ) := deriv_comp _ hUd hgdz
    simp only [hΦ, hW]
    rw [hχg _ hz1, hcg1 _ (by rw [hz]), hch]
    ring
  rw [hfb] at hFeq
  rw [hgb] at hG
  set A : ℂ := ∫ θ in (0 : ℝ)..2 * π,
      conj (U (f (circleMap 0 ρ θ))) * deriv (fun z => U (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ with hA
  set B : ℂ := ∫ θ in (0 : ℝ)..2 * π,
      conj (U (g (circleMap 0 (1 / ρ) θ))) * deriv (fun z => U (g z)) (circleMap 0 (1 / ρ) θ) *
        circleMap 0 (1 / ρ) θ with hB
  have hX : ∫ w in Kfᶜ, dzbar Φ w = -A / 2 := by
    have h1 : I * (2 * ∫ w in Kfᶜ, dzbar Φ w) = I * (-A) := by linear_combination hFeq
    have := mul_left_cancel₀ Complex.I_ne_zero h1
    linear_combination this / 2
  have hY : ∫ w in Kg, dzbar Φ w = -B / 2 := by
    have h1 : I * (2 * ∫ w in Kg, dzbar Φ w) = I * (-B) := by linear_combination hG
    have := mul_left_cancel₀ Complex.I_ne_zero h1
    linear_combination this / 2
  rw [← hgap]
  linear_combination (-1 : ℂ) * hsplit + hX - hY


/-- Summability of a two-sided series with a geometric majorant on each side. -/
theorem mg_laurent_summable (d : ℤ → ℂ) {r1 ρ r2 : ℝ} (hr1 : 0 < r1) (h1 : r1 < ρ) (h2 : ρ < r2)
    (hpos : Summable (fun n : ℕ => ‖d n‖ * r2 ^ n))
    (hneg : Summable (fun n : ℕ => ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹)) :
    Summable (fun n : ℤ => ‖d n‖ * max (r1 ^ n) (r2 ^ n)) ∧
      Summable (fun n : ℤ => |(n : ℝ)| * ‖d n‖ * ρ ^ n) := by
  have hρ0 : 0 < ρ := hr1.trans h1
  have hr20 : 0 < r2 := hρ0.trans h2
  refine ⟨?_, ?_⟩
  · rw [summable_int_iff_summable_nat_and_neg]
    refine ⟨?_, ?_⟩
    · refine hpos.congr (fun n => ?_)
      have : max (r1 ^ (n : ℤ)) (r2 ^ (n : ℤ)) = r2 ^ n := by
        rw [zpow_natCast, zpow_natCast]
        exact max_eq_right (pow_le_pow_left₀ hr1.le (by linarith) n)
      rw [this]
    · refine hneg.congr (fun n => ?_)
      have : max (r1 ^ (-(n : ℤ))) (r2 ^ (-(n : ℤ))) = (r1 ^ n)⁻¹ := by
        rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        exact max_eq_left (inv_anti₀ (pow_pos hr1 n) (pow_le_pow_left₀ hr1.le (by linarith) n))
      rw [this]
  · rw [summable_int_iff_summable_nat_and_neg]
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC⟩ := hpos.tendsto_atTop_zero.bddAbove_range
      have hgeo : Summable (fun n : ℕ => ((n : ℝ) ^ 1) * (ρ / r2) ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one 1 (by
          rw [Real.norm_of_nonneg (by positivity)]
          exact (div_lt_one hr20).mpr h2)
      refine (hgeo.mul_left (|C|)).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      have h1' : ‖d n‖ * r2 ^ n ≤ |C| := (hC ⟨n, rfl⟩).trans (le_abs_self C)
      have h2' : (0 : ℝ) < r2 ^ n := pow_pos hr20 n
      simp only [Int.cast_natCast, Nat.abs_cast, zpow_natCast, pow_one]
      calc (n : ℝ) * ‖d n‖ * ρ ^ n = (n : ℝ) * ((‖d n‖ * r2 ^ n) * (ρ / r2) ^ n) := by
            rw [div_pow]; field_simp
        _ ≤ (n : ℝ) * (|C| * (ρ / r2) ^ n) := by gcongr
        _ = |C| * ((n : ℝ) * (ρ / r2) ^ n) := by ring
    · obtain ⟨C, hC⟩ := hneg.tendsto_atTop_zero.bddAbove_range
      have hgeo : Summable (fun n : ℕ => ((n : ℝ) ^ 1) * (r1 / ρ) ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one 1 (by
          rw [Real.norm_of_nonneg (by positivity)]
          exact (div_lt_one hρ0).mpr h1)
      refine (hgeo.mul_left (|C|)).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      have h1' : ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹ ≤ |C| := (hC ⟨n, rfl⟩).trans (le_abs_self C)
      have h2' : (0 : ℝ) < (r1 ^ n)⁻¹ := inv_pos.mpr (pow_pos hr1 n)
      simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, zpow_neg, zpow_natCast, pow_one]
      calc (n : ℝ) * ‖d (-(n : ℤ))‖ * (ρ ^ n)⁻¹
          = (n : ℝ) * ((‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹) * (r1 / ρ) ^ n) := by
            rw [div_pow]; field_simp
        _ ≤ (n : ℝ) * (|C| * (r1 / ρ) ^ n) := by gcongr
        _ = |C| * ((n : ℝ) * (r1 / ρ) ^ n) := by ring

/-- The circle integral of `conj H H' z` for `H` given by a Laurent series on an annulus. -/
theorem mg_circle_energy {H : ℂ → ℂ} (d : ℤ → ℂ) {r1 ρ r2 : ℝ} (hr1 : 0 < r1) (h1 : r1 < ρ) (h2 : ρ < r2)
    (hpos : Summable (fun n : ℕ => ‖d n‖ * r2 ^ n))
    (hneg : Summable (fun n : ℕ => ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹))
    (hH : ∀ w : ℂ, r1 < ‖w‖ → ‖w‖ < r2 → H w = ∑' n : ℤ, d n * w ^ n) :
    (∫ θ in (0 : ℝ)..2 * π, conj (H (circleMap 0 ρ θ)) * deriv H (circleMap 0 ρ θ) * circleMap 0 ρ θ) =
      2 * π * ∑' n : ℤ, (n : ℂ) * ((‖d n‖ ^ 2 * ρ ^ (2 * n) : ℝ) : ℂ) := by
  obtain ⟨hs, hs1⟩ := mg_laurent_summable d hr1 h1 h2 hpos hneg
  have hP := g2_laurent_parseval hr1 h1 h2 hs hs1
  rw [← hP]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  have hcirc : r1 < ‖circleMap 0 ρ θ‖ ∧ ‖circleMap 0 ρ θ‖ < r2 := by
    simp only [norm_circleMap_zero, abs_of_pos (hr1.trans h1)]
    exact ⟨h1, h2⟩
  have hU : IsOpen {w : ℂ | r1 < ‖w‖ ∧ ‖w‖ < r2} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hev : H =ᶠ[𝓝 (circleMap 0 ρ θ)] fun w : ℂ => ∑' n : ℤ, d n * w ^ n := by
    filter_upwards [hU.mem_nhds hcirc] with w hw
    exact hH w hw.1 hw.2
  rw [hev.deriv_eq, hH _ hcirc.1 hcirc.2]

theorem mg_tsum_int_split {a : ℤ → ℝ} (ha : Summable a) (h0 : a 0 = 0) :
    ∑' n : ℤ, a n = (∑' j : ℕ, a (((j + 1 : ℕ) : ℤ))) + ∑' k : ℕ, a (-((k : ℤ) + 1)) := by
  have hpos : Summable (fun n : ℕ => a (n : ℤ)) := ha.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => a (-((n : ℤ) + 1))) := by
    have : Function.Injective (fun n : ℕ => (-((n : ℤ) + 1))) := by
      intro x y hxy; simp at hxy; exact_mod_cast hxy
    exact ha.comp_injective this
  rw [tsum_of_nat_of_neg_add_one hpos hneg, hpos.tsum_eq_zero_add]
  simp only [Nat.cast_zero, h0, zero_add, Nat.cast_add, Nat.cast_one]

/-- The weighted energy of a Laurent coefficient sequence on the circle `|z| = ρ`, as a real sum. -/
theorem mg_energy_real {d : ℤ → ℂ} {r1 ρ r2 : ℝ} (hr1 : 0 < r1) (h1 : r1 < ρ) (h2 : ρ < r2)
    (hpos : Summable (fun n : ℕ => ‖d n‖ * r2 ^ n))
    (hneg : Summable (fun n : ℕ => ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹)) :
    Summable (fun n : ℤ => (n : ℝ) * (‖d n‖ ^ 2 * ρ ^ (2 * n))) ∧
      (∑' n : ℤ, (n : ℂ) * ((‖d n‖ ^ 2 * ρ ^ (2 * n) : ℝ) : ℂ)) =
        ((∑' n : ℤ, (n : ℝ) * (‖d n‖ ^ 2 * ρ ^ (2 * n)) : ℝ) : ℂ) := by
  obtain ⟨hs, hs1⟩ := mg_laurent_summable d hr1 h1 h2 hpos hneg
  have hρ0 : 0 < ρ := hr1.trans h1
  have hs0 : Summable fun n : ℤ => ‖d n‖ * ρ ^ n :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by gcongr; exact g2_zpow_le_max hr1 h1.le h2.le n) hs
  have hB : ∀ n : ℤ, ‖d n‖ * ρ ^ n ≤ ∑' m : ℤ, ‖d m‖ * ρ ^ m := fun n =>
    hs0.le_tsum n (fun m _ => by positivity)
  have hgs : Summable fun n : ℤ => (n : ℝ) * (‖d n‖ ^ 2 * ρ ^ (2 * n)) := by
    refine ((hs1.mul_left (∑' m : ℤ, ‖d m‖ * ρ ^ m)).of_norm_bounded (fun n => ?_))
    have e : (n : ℝ) * (‖d n‖ ^ 2 * ρ ^ (2 * n)) =
        ((n : ℝ) * (‖d n‖ * ρ ^ n)) * (‖d n‖ * ρ ^ n) := by
      rw [show 2 * n = n + n by ring, zpow_add₀ hρ0.ne']; ring
    rw [e, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖d n‖ * ρ ^ n),
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖d n‖ * ρ ^ n)]
    calc |(n : ℝ)| * (‖d n‖ * ρ ^ n) * (‖d n‖ * ρ ^ n)
        ≤ |(n : ℝ)| * (‖d n‖ * ρ ^ n) * (∑' m : ℤ, ‖d m‖ * ρ ^ m) := by
          gcongr; exact hB n
      _ = (∑' m : ℤ, ‖d m‖ * ρ ^ m) * (|(n : ℝ)| * ‖d n‖ * ρ ^ n) := by ring
  refine ⟨hgs, ?_⟩
  rw [Complex.ofReal_tsum]
  push_cast
  rfl

/-- Splitting of the energy sum into its positive and negative parts. -/
theorem mg_energy_split {d : ℤ → ℂ} {r1 ρ r2 : ℝ} (hr1 : 0 < r1) (h1 : r1 < ρ) (h2 : ρ < r2)
    (hpos : Summable (fun n : ℕ => ‖d n‖ * r2 ^ n))
    (hneg : Summable (fun n : ℕ => ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹)) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖d ((j + 1 : ℕ) : ℤ)‖ ^ 2 * ρ ^ (2 * (j + 1)))) ∧
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (‖d (-((k + 1 : ℕ) : ℤ))‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹)) ∧
      (∑' n : ℤ, (n : ℝ) * (‖d n‖ ^ 2 * ρ ^ (2 * n))) =
        (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖d ((j + 1 : ℕ) : ℤ)‖ ^ 2 * ρ ^ (2 * (j + 1)))) -
          ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (‖d (-((k + 1 : ℕ) : ℤ))‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹) := by
  obtain ⟨hgs, -⟩ := mg_energy_real hr1 h1 h2 hpos hneg
  have hinj1 : Function.Injective (fun j : ℕ => (((j + 1 : ℕ) : ℤ))) := by
    intro x y hxy; simpa using hxy
  have hinj2 : Function.Injective (fun k : ℕ => (-(((k + 1 : ℕ) : ℤ)))) := by
    intro x y hxy; simp at hxy; exact_mod_cast hxy
  have ep : ∀ j : ℕ, (((((j + 1 : ℕ) : ℤ)) : ℝ)) * (‖d (((j + 1 : ℕ) : ℤ))‖ ^ 2 * ρ ^ (2 * (((j + 1 : ℕ) : ℤ)))) =
      ((j + 1 : ℕ) : ℝ) * (‖d ((j + 1 : ℕ) : ℤ)‖ ^ 2 * ρ ^ (2 * (j + 1))) := by
    intro j
    rw [show (2 * (((j + 1 : ℕ) : ℤ))) = (((2 * (j + 1) : ℕ)) : ℤ) by push_cast; ring, zpow_natCast]
    simp
  have en : ∀ k : ℕ, ((((-(((k + 1 : ℕ) : ℤ))) : ℤ) : ℝ)) *
      (‖d (-(((k + 1 : ℕ) : ℤ)))‖ ^ 2 * ρ ^ (2 * (-(((k + 1 : ℕ) : ℤ))))) =
      -(((k + 1 : ℕ) : ℝ) * (‖d (-((k + 1 : ℕ) : ℤ))‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹)) := by
    intro k
    rw [show 2 * (-(((k + 1 : ℕ) : ℤ))) = -(((2 * (k + 1) : ℕ)) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    simp only [Int.cast_neg, Int.cast_natCast]
    ring
  have hp : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖d ((j + 1 : ℕ) : ℤ)‖ ^ 2 * ρ ^ (2 * (j + 1)))) := by
    have := hgs.comp_injective hinj1
    exact this.congr (fun j => ep j)
  have hn : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (‖d (-((k + 1 : ℕ) : ℤ))‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹)) := by
    have := (hgs.comp_injective hinj2).neg
    exact this.congr (fun k => by simp only [Function.comp_apply]; rw [en k]; ring)
  refine ⟨hp, hn, ?_⟩
  rw [mg_tsum_int_split hgs (by simp)]
  have e1 : (∑' j : ℕ, (((((j + 1 : ℕ) : ℤ)) : ℝ)) * (‖d (((j + 1 : ℕ) : ℤ))‖ ^ 2 * ρ ^ (2 * (((j + 1 : ℕ) : ℤ))))) =
      ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖d ((j + 1 : ℕ) : ℤ)‖ ^ 2 * ρ ^ (2 * (j + 1))) :=
    tsum_congr ep
  have e2 : (∑' k : ℕ, ((((-((k : ℤ) + 1)) : ℤ) : ℝ)) *
      (‖d (-((k : ℤ) + 1))‖ ^ 2 * ρ ^ (2 * (-((k : ℤ) + 1))))) =
      -∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (‖d (-((k + 1 : ℕ) : ℤ))‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹) := by
    rw [← tsum_neg]
    refine tsum_congr (fun k => ?_)
    have e : (-((k : ℤ) + 1)) = -(((k + 1 : ℕ) : ℤ)) := by push_cast; ring
    rw [e]
    exact en k
  rw [e1, e2]
  ring

theorem mg_sum_Icc_eq_range {M : Type*} [AddCommMonoid M] (F : ℕ → M) (m : ℕ) :
    ∑ n ∈ Finset.Icc 1 m, F n = ∑ k ∈ Finset.range m, F (k + 1) := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' F 0 m 1]
  simp only [zero_add]
  rfl

theorem mg_hasSum_int (F G : ℕ → ℂ) {z : ℂ} {S T : ℂ}
    (hF : HasSum (fun n : ℕ => F n * z ^ n) S)
    (hG : HasSum (fun n : ℕ => G (n + 1) * z ^ (-((n : ℤ) + 1))) T) :
    HasSum (fun m : ℤ => (if 0 ≤ m then F m.toNat else G (-m).toNat) * z ^ m) (S + T) := by
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · refine hF.congr_fun (fun n => ?_)
    simp
  · refine hG.congr_fun (fun n => ?_)
    have h1 : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1) := by omega
    have h2 : (-(-((n : ℤ) + 1))).toNat = n + 1 := by omega
    simp only [h1, if_false, h2]

/-- The `f`-side circle integral of `U_lam`, in Grunsky coordinates. -/
theorem mg_f_side {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber f g P Q) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) (lam : ℤ → ℂ) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖∑ k ∈ Finset.range m,
        (((k + 1 : ℕ) : ℂ) * (lam ((k : ℤ) + 1) / (Real.sqrt ((k : ℝ) + 1) : ℂ)) *
            grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)) +
          ((k + 1 : ℕ) : ℂ) * (lam (-((k : ℤ) + 1)) / (Real.sqrt ((k : ℝ) + 1) : ℂ)) *
            grunsky f g (-((k : ℤ) + 1)) (-((j : ℤ) + 1)))‖ ^ 2 * ρ ^ (2 * (j + 1)))) ∧
    (∫ θ in (0 : ℝ)..2 * π,
        conj ((fun w : ℂ => ∑ n ∈ Finset.Icc 1 m,
          (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹))
          (f (circleMap 0 ρ θ))) *
        deriv (fun z => (fun w : ℂ => ∑ n ∈ Finset.Icc 1 m,
          (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹))
          (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ) =
      2 * π * (((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖∑ k ∈ Finset.range m,
        (((k + 1 : ℕ) : ℂ) * (lam ((k : ℤ) + 1) / (Real.sqrt ((k : ℝ) + 1) : ℂ)) *
            grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)) +
          ((k + 1 : ℕ) : ℂ) * (lam (-((k : ℤ) + 1)) / (Real.sqrt ((k : ℝ) + 1) : ℂ)) *
            grunsky f g (-((k : ℤ) + 1)) (-((j : ℤ) + 1)))‖ ^ 2 * ρ ^ (2 * (j + 1)))) -
        ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * (‖lam (-((k : ℤ) + 1)) / (Real.sqrt ((k : ℝ) + 1) : ℂ)‖ ^ 2 *
          (ρ ^ (2 * (k + 1)))⁻¹) : ℝ) : ℂ) := by
  set b := grunsky f g with hb
  set α : ℕ → ℂ := fun k => lam ((k : ℤ) + 1) / (Real.sqrt ((k : ℝ) + 1) : ℂ) with hα
  set β : ℕ → ℂ := fun k => lam (-((k : ℤ) + 1)) / (Real.sqrt ((k : ℝ) + 1) : ℂ) with hβ
  set D : ℕ → ℂ := fun j => ∑ k ∈ Finset.range m,
    (((k + 1 : ℕ) : ℂ) * α k * b ((k : ℤ) + 1) (-((j : ℤ) + 1)) +
      ((k + 1 : ℕ) : ℂ) * β k * b (-((k : ℤ) + 1)) (-((j : ℤ) + 1))) with hD
  set c0 : ℂ := ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℂ) * α k * b ((k : ℤ) + 1) 0 with hc0
  set U : ℂ → ℂ := fun w => ∑ n ∈ Finset.Icc 1 m,
    (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹) with hU
  have hUr : ∀ w : ℂ, U w = ∑ k ∈ Finset.range m, (α k * (P (k + 1)).eval w + β k * (Q (k + 1)).eval w⁻¹) := by
    intro w
    simp only [hU]
    rw [mg_sum_Icc_eq_range]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hα, hβ]
    push_cast
    rfl
  -- the Laurent expansion on the disc
  have hexp : ∀ z ∈ unitDisc, z ≠ 0 →
      HasSum (fun j : ℕ => D j * z ^ (j + 1))
        (U (f z) - c0 - ∑ k ∈ Finset.range m, β k * z ^ (-((k : ℤ) + 1))) := by
    intro z hz hz0
    have hk : ∀ k ∈ Finset.range m,
        HasSum (fun j : ℕ => α k * (((k + 1 : ℕ) : ℂ) * b ((k : ℤ) + 1) (-((j + 1 : ℕ) : ℤ)) * z ^ (j + 1)) +
            β k * (((k + 1 : ℕ) : ℂ) * b (-((k : ℤ) + 1)) (-((j + 1 : ℕ) : ℤ)) * z ^ (j + 1)))
          (α k * ((P (k + 1)).eval (f z) - ((k + 1 : ℕ) : ℂ) * b ((k : ℤ) + 1) 0) +
            β k * ((Q (k + 1)).eval (f z)⁻¹ - z ^ (-((k : ℤ) + 1)))) := by
      intro k _
      have hA := (faber_grunsky h hPQ k).1 z hz
      have hB := hPQ.2.2 k z hz hz0
      simp only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one] at hA hB ⊢
      exact (hA.mul_left (α k)).add (hB.mul_left (β k))
    have hS := hasSum_sum hk
    convert hS using 1
    · funext j
      simp only [hD]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      push_cast
      ring
    · rw [hUr (f z)]
      have hc0' : c0 = ∑ k ∈ Finset.range m, α k * (((k + 1 : ℕ) : ℂ) * b ((k : ℤ) + 1) 0) :=
        Finset.sum_congr rfl (fun k _ => by ring)
      rw [hc0']
      simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
  -- Laurent coefficients
  set F : ℕ → ℂ := fun n => if n = 0 then c0 else D (n - 1) with hF
  set G : ℕ → ℂ := fun n => if 1 ≤ n ∧ n ≤ m then β (n - 1) else 0 with hG
  set d : ℤ → ℂ := fun n => if 0 ≤ n then F n.toNat else G (-n).toNat with hd
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = ρ / 2 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℝ, r2 = (ρ + 1) / 2 := ⟨_, rfl⟩
  have hr1p : 0 < r1 := by rw [hr1]; positivity
  have hr1ρ : r1 < ρ := by rw [hr1]; linarith
  have hρr2 : ρ < r2 := by rw [hr2]; linarith
  have hr2one : r2 < 1 := by rw [hr2]; linarith
  have hdpos : ∀ n : ℕ, d (n : ℤ) = F n := fun n => by simp [hd]
  have hdneg : ∀ n : ℕ, d (-((n : ℤ) + 1)) = G (n + 1) := fun n => by
    have h1 : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1) := by omega
    have h2 : (-(-((n : ℤ) + 1))).toNat = n + 1 := by omega
    simp only [hd, h1, if_false, h2]
  have hFs1 : ∀ n : ℕ, F (n + 1) = D n := fun n => by simp [hF]
  have hGβ : ∀ n : ℕ, G (n + 1) = if n < m then β n else 0 := fun n => by
    simp only [hG]
    by_cases hn : n < m
    · rw [if_pos ⟨by omega, by omega⟩, if_pos hn]; rfl
    · rw [if_neg (by omega), if_neg hn]
  have hLaurent : ∀ w : ℂ, r1 < ‖w‖ → ‖w‖ < r2 → U (f w) = ∑' n : ℤ, d n * w ^ n := by
    intro w hw1 hw2
    have hwD : w ∈ unitDisc := mem_ball_zero_iff.mpr (hw2.trans hr2one)
    have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hw1; linarith
    have hS := hexp w hwD hw0
    have hFsum : HasSum (fun n : ℕ => F n * w ^ n)
        ((U (f w) - c0 - ∑ k ∈ Finset.range m, β k * w ^ (-((k : ℤ) + 1))) + c0) := by
      rw [← hasSum_nat_add_iff' 1]
      simp only [Finset.sum_range_one, hF, if_true, pow_zero, mul_one, add_sub_cancel_right]
      refine hS.congr_fun (fun n => ?_)
      simp
    have hGsum : HasSum (fun n : ℕ => G (n + 1) * w ^ (-((n : ℤ) + 1)))
        (∑ k ∈ Finset.range m, β k * w ^ (-((k : ℤ) + 1))) := by
      have hh : HasSum (fun n : ℕ => G (n + 1) * w ^ (-((n : ℤ) + 1)))
          (∑ n ∈ Finset.range m, G (n + 1) * w ^ (-((n : ℤ) + 1))) :=
        hasSum_sum_of_ne_finset_zero (fun n hn => by
          rw [hGβ, if_neg (by simpa using hn), zero_mul])
      convert hh using 1
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [hGβ, if_pos (by simpa using hk)]
    have htsum : ∑' n : ℤ, d n * w ^ n =
        (U (f w) - c0 - ∑ k ∈ Finset.range m, β k * w ^ (-((k : ℤ) + 1))) + c0 +
          ∑ k ∈ Finset.range m, β k * w ^ (-((k : ℤ) + 1)) :=
      (mg_hasSum_int F G hFsum hGsum).tsum_eq
    rw [htsum]
    ring
  -- summability
  have hpos : Summable (fun n : ℕ => ‖d n‖ * r2 ^ n) := by
    have hr2D : ((r2 : ℝ) : ℂ) ∈ unitDisc :=
      mem_ball_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hr2one)
    have hr20 : ((r2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hS := hexp _ hr2D hr20
    have hn := summable_norm_iff.mpr hS.summable
    rw [← summable_nat_add_iff 1]
    refine hn.congr (fun j => ?_)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show ((j : ℤ) + 1) = (((j + 1 : ℕ)) : ℤ) by push_cast; ring, hdpos, hFs1, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hneg : Summable (fun n : ℕ => ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹) := by
    refine summable_of_ne_finset_zero (s := Finset.range (m + 1)) (fun n hn => ?_)
    have hn' : m + 1 ≤ n := by simpa using hn
    have h1 : ¬ (0 : ℤ) ≤ -(n : ℤ) := by omega
    have h2 : (-(-(n : ℤ))).toNat = n := by omega
    have : d (-(n : ℤ)) = 0 := by
      simp only [hd, h1, if_false, h2]
      simp only [hG]
      rw [if_neg (by omega)]
    rw [this, norm_zero, zero_mul]
  have hE := mg_circle_energy (H := fun z => U (f z)) d hr1p hr1ρ hρr2 hpos hneg hLaurent
  obtain ⟨hgs, hTc⟩ := mg_energy_real hr1p hr1ρ hρr2 hpos hneg
  obtain ⟨hsp, hsn, hsplit⟩ := mg_energy_split hr1p hr1ρ hρr2 hpos hneg
  have e1 : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖d ((j + 1 : ℕ) : ℤ)‖ ^ 2 * ρ ^ (2 * (j + 1)))) =
      fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖D j‖ ^ 2 * ρ ^ (2 * (j + 1))) := by
    funext j
    rw [hdpos, hFs1]
  have e2 : ∀ k : ℕ, d (-((k + 1 : ℕ) : ℤ)) = if k < m then β k else 0 := by
    intro k
    rw [show (-((k + 1 : ℕ) : ℤ)) = -((k : ℤ) + 1) by push_cast; ring, hdneg, hGβ]
  rw [e1] at hsp
  refine ⟨hsp, ?_⟩
  rw [hE, hTc, hsplit, e1]
  congr 3
  rw [tsum_eq_sum (s := Finset.range m) (fun k hk => by
    rw [e2, if_neg (by simpa using hk)]; simp)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [e2, if_pos (by simpa using hk)]

/-- The `g`-side circle integral of `U_lam`, in Grunsky coordinates. -/
theorem mg_g_side {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber f g P Q) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) (lam : ℤ → ℂ) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (‖∑ j ∈ Finset.range m,
        (((j + 1 : ℕ) : ℂ) * (lam ((j : ℤ) + 1) / (Real.sqrt ((j : ℝ) + 1) : ℂ)) *
            grunsky f g ((j : ℤ) + 1) ((k : ℤ) + 1) +
          ((j + 1 : ℕ) : ℂ) * (lam (-((j : ℤ) + 1)) / (Real.sqrt ((j : ℝ) + 1) : ℂ)) *
            grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)))‖ ^ 2 * ρ ^ (2 * (k + 1)))) ∧
    (∫ θ in (0 : ℝ)..2 * π,
        conj ((fun w : ℂ => ∑ n ∈ Finset.Icc 1 m,
          (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹))
          (g (circleMap 0 (1 / ρ) θ))) *
        deriv (fun z => (fun w : ℂ => ∑ n ∈ Finset.Icc 1 m,
          (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹))
          (g z)) (circleMap 0 (1 / ρ) θ) * circleMap 0 (1 / ρ) θ) =
      2 * π * ((((∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) *
          (‖lam ((j : ℤ) + 1) / (Real.sqrt ((j : ℝ) + 1) : ℂ)‖ ^ 2 * (ρ ^ (2 * (j + 1)))⁻¹)) -
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (‖∑ j ∈ Finset.range m,
        (((j + 1 : ℕ) : ℂ) * (lam ((j : ℤ) + 1) / (Real.sqrt ((j : ℝ) + 1) : ℂ)) *
            grunsky f g ((j : ℤ) + 1) ((k : ℤ) + 1) +
          ((j + 1 : ℕ) : ℂ) * (lam (-((j : ℤ) + 1)) / (Real.sqrt ((j : ℝ) + 1) : ℂ)) *
            grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)))‖ ^ 2 * ρ ^ (2 * (k + 1)))) : ℝ) : ℂ) := by
  set b := grunsky f g with hb
  set α : ℕ → ℂ := fun k => lam ((k : ℤ) + 1) / (Real.sqrt ((k : ℝ) + 1) : ℂ) with hα
  set β : ℕ → ℂ := fun k => lam (-((k : ℤ) + 1)) / (Real.sqrt ((k : ℝ) + 1) : ℂ) with hβ
  set E : ℕ → ℂ := fun k => ∑ j ∈ Finset.range m,
    (((j + 1 : ℕ) : ℂ) * α j * b ((j : ℤ) + 1) ((k : ℤ) + 1) +
      ((j + 1 : ℕ) : ℂ) * β j * b ((k : ℤ) + 1) (-((j : ℤ) + 1))) with hE
  set c0 : ℂ := -∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℂ) * β j * b (-((j : ℤ) + 1)) 0 with hc0
  set U : ℂ → ℂ := fun w => ∑ n ∈ Finset.Icc 1 m,
    (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹) with hU
  have hUr : ∀ w : ℂ, U w = ∑ k ∈ Finset.range m, (α k * (P (k + 1)).eval w + β k * (Q (k + 1)).eval w⁻¹) := by
    intro w
    simp only [hU]
    rw [mg_sum_Icc_eq_range]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hα, hβ]
    push_cast
    rfl
  have hR : 1 < 1 / ρ := one_lt_one_div hρ0 hρ1
  -- the Laurent expansion at infinity
  have hexp : ∀ z : ℂ, 1 < ‖z‖ →
      HasSum (fun k : ℕ => E k * z ^ (-((k : ℤ) + 1)))
        (U (g z) - ∑ j ∈ Finset.range m, α j * z ^ (j + 1) - c0) := by
    intro z hz
    have hk : ∀ j ∈ Finset.range m,
        HasSum (fun k : ℕ => α j * (((j + 1 : ℕ) : ℂ) * b ((j : ℤ) + 1) ((k : ℤ) + 1) * z ^ (-((k : ℤ) + 1))) +
            β j * (((j + 1 : ℕ) : ℂ) * b ((k : ℤ) + 1) (-((j : ℤ) + 1)) * z ^ (-((k : ℤ) + 1))))
          (α j * ((P (j + 1)).eval (g z) - z ^ (j + 1)) +
            β j * ((Q (j + 1)).eval (g z)⁻¹ + ((j + 1 : ℕ) : ℂ) * b (-((j : ℤ) + 1)) 0)) := by
      intro j _
      have hA := hPQ.2.1 j z hz
      have hB := (faber_grunsky h hPQ j).2 z hz
      simp only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one] at hA hB ⊢
      exact (hA.mul_left (α j)).add (hB.mul_left (β j))
    have hS := hasSum_sum hk
    convert hS using 1
    · funext k
      simp only [hE]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      push_cast
      ring
    · rw [hUr (g z)]
      have hc0' : c0 = -∑ j ∈ Finset.range m, β j * (((j + 1 : ℕ) : ℂ) * b (-((j : ℤ) + 1)) 0) := by
        simp only [hc0]
        congr 1
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [hc0']
      simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
  -- Laurent coefficients
  set F : ℕ → ℂ := fun n => if n = 0 then c0 else if n ≤ m then α (n - 1) else 0 with hF
  set G : ℕ → ℂ := fun n => if n = 0 then 0 else E (n - 1) with hG
  set d : ℤ → ℂ := fun n => if 0 ≤ n then F n.toNat else G (-n).toNat with hd
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 1 / ρ := ⟨_, rfl⟩
  rw [← hRdef] at hR ⊢
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = (1 + R) / 2 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℝ, r2 = 2 * R := ⟨_, rfl⟩
  have hr1one : 1 < r1 := by rw [hr1]; linarith
  have hr1p : 0 < r1 := by linarith
  have hr1R : r1 < R := by rw [hr1]; linarith
  have hRr2 : R < r2 := by rw [hr2]; linarith
  have hdpos : ∀ n : ℕ, d (n : ℤ) = F n := fun n => by simp [hd]
  have hdneg : ∀ n : ℕ, d (-((n : ℤ) + 1)) = E n := fun n => by
    have h1 : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1) := by omega
    have h2 : (-(-((n : ℤ) + 1))).toNat = n + 1 := by omega
    simp only [hd, h1, if_false, h2, hG]
    simp
  have hFs : ∀ n : ℕ, F (n + 1) = if n < m then α n else 0 := fun n => by
    simp only [hF]
    by_cases hn : n < m
    · rw [if_neg (by omega), if_pos (by omega), if_pos hn]; rfl
    · rw [if_neg (by omega), if_neg (by omega), if_neg hn]
  have hLaurent : ∀ w : ℂ, r1 < ‖w‖ → ‖w‖ < r2 → U (g w) = ∑' n : ℤ, d n * w ^ n := by
    intro w hw1 hw2
    have hw1' : 1 < ‖w‖ := lt_trans hr1one hw1
    have hFsum : HasSum (fun n : ℕ => F n * w ^ n)
        (c0 + ∑ j ∈ Finset.range m, α j * w ^ (j + 1)) := by
      have hh : HasSum (fun n : ℕ => F n * w ^ n) (∑ n ∈ Finset.range (m + 1), F n * w ^ n) :=
        hasSum_sum_of_ne_finset_zero (fun n hn => by
          have : ¬ n = 0 ∧ ¬ n ≤ m := by
            simp only [Finset.mem_range] at hn
            omega
          simp only [hF, if_neg this.1, if_neg this.2, zero_mul])
      convert hh using 1
      have hF0 : F 0 = c0 := by simp [hF]
      rw [Finset.sum_range_succ', hF0, pow_zero, mul_one, add_comm]
      congr 1
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [hFs j, if_pos (by simpa using hj)]
    have hGsum : HasSum (fun n : ℕ => G (n + 1) * w ^ (-((n : ℤ) + 1)))
        (U (g w) - ∑ j ∈ Finset.range m, α j * w ^ (j + 1) - c0) := by
      refine (hexp w hw1').congr_fun (fun n => ?_)
      simp [hG]
    have htsum : ∑' n : ℤ, d n * w ^ n =
        (c0 + ∑ j ∈ Finset.range m, α j * w ^ (j + 1)) +
          (U (g w) - ∑ j ∈ Finset.range m, α j * w ^ (j + 1) - c0) :=
      (mg_hasSum_int F G hFsum hGsum).tsum_eq
    rw [htsum]
    ring
  -- summability
  have hpos : Summable (fun n : ℕ => ‖d n‖ * r2 ^ n) := by
    refine summable_of_ne_finset_zero (s := Finset.range (m + 1)) (fun n hn => ?_)
    have hn' : m + 1 ≤ n := by simpa using hn
    rw [hdpos]
    simp only [hF, if_neg (show ¬ n = 0 by omega), if_neg (show ¬ n ≤ m by omega), norm_zero, zero_mul]
  have hneg : Summable (fun n : ℕ => ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹) := by
    have hr1D : ((r1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr1p.ne'
    have hS := hexp ((r1 : ℝ) : ℂ) (by rw [Complex.norm_real, Real.norm_of_nonneg hr1p.le]; exact hr1one)
    have hn := summable_norm_iff.mpr hS.summable
    rw [← summable_nat_add_iff 1]
    refine hn.congr (fun k => ?_)
    rw [show (-(((k + 1 : ℕ)) : ℤ)) = -((k : ℤ) + 1) by push_cast; ring, hdneg, norm_mul, norm_zpow,
      Complex.norm_real, Real.norm_of_nonneg hr1p.le, zpow_neg]
    rw [show ((k : ℤ) + 1) = (((k + 1 : ℕ)) : ℤ) by push_cast; ring, zpow_natCast]
  have hE' := mg_circle_energy (H := fun z => U (g z)) d hr1p hr1R hRr2 hpos hneg hLaurent
  obtain ⟨hgs, hTc⟩ := mg_energy_real hr1p hr1R hRr2 hpos hneg
  obtain ⟨hsp, hsn, hsplit⟩ := mg_energy_split hr1p hr1R hRr2 hpos hneg
  have eR : ∀ n : ℕ, (R ^ (2 * (n + 1)))⁻¹ = ρ ^ (2 * (n + 1)) := fun n => by
    rw [hRdef, one_div, inv_pow, inv_inv]
  have e2 : (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (‖d (-((k + 1 : ℕ) : ℤ))‖ ^ 2 * (R ^ (2 * (k + 1)))⁻¹)) =
      fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (‖E k‖ ^ 2 * ρ ^ (2 * (k + 1))) := by
    funext k
    rw [show (-((k + 1 : ℕ) : ℤ)) = -((k : ℤ) + 1) by push_cast; ring, hdneg, eR]
  rw [e2] at hsn
  refine ⟨hsn, ?_⟩
  rw [hE', hTc, hsplit, e2]
  congr 3
  rw [tsum_eq_sum (s := Finset.range m) (fun j hj => by
    rw [show (((j + 1 : ℕ)) : ℤ) = ((j + 1 : ℕ) : ℤ) from rfl, hdpos, hFs, if_neg (by simpa using hj)]
    simp)]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [hdpos, hFs, if_pos (by simpa using hj), hRdef, one_div, inv_pow]

theorem mg_sum_erase {M : Type*} [AddCommMonoid M] (F : ℤ → M) (m : ℕ) :
    ∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, F l =
      ∑ k ∈ Finset.range m, (F ((k : ℤ) + 1) + F (-((k : ℤ) + 1))) := by
  have hset : (Finset.Icc (-(m : ℤ)) m).erase 0 =
      (Finset.range m).image (fun k : ℕ => (k : ℤ) + 1) ∪
        (Finset.range m).image (fun k : ℕ => -((k : ℤ) + 1)) := by
    ext l
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h0, h1, h2⟩
      rcases lt_or_gt_of_ne h0 with hl | hl
      · right; exact ⟨(-l - 1).toNat, by omega, by omega⟩
      · left; exact ⟨(l - 1).toNat, by omega, by omega⟩
    · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
      · refine ⟨by omega, by omega, by omega⟩
      · refine ⟨by omega, by omega, by omega⟩
  have hdisj : Disjoint ((Finset.range m).image (fun k : ℕ => (k : ℤ) + 1))
      ((Finset.range m).image (fun k : ℕ => -((k : ℤ) + 1))) := by
    rw [Finset.disjoint_left]
    intro l hl hl'
    simp only [Finset.mem_image, Finset.mem_range] at hl hl'
    obtain ⟨a, _, rfl⟩ := hl
    obtain ⟨c, _, hc⟩ := hl'
    omega
  have hi1 : Function.Injective (fun k : ℕ => (k : ℤ) + 1) := by
    intro x y hxy; simpa using hxy
  have hi2 : Function.Injective (fun k : ℕ => -((k : ℤ) + 1)) := by
    intro x y hxy; simp at hxy; exact_mod_cast hxy
  rw [hset, Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ h => hi1 h),
    Finset.sum_image (fun x _ y _ h => hi2 h), Finset.sum_add_distrib]

/-- Regrouping of the `g`-side coefficient. -/
theorem mg_coeff_g {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) (m k : ℕ) (lam : ℤ → ℂ) :
    ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ) * (∑ j ∈ Finset.range m,
        (((j + 1 : ℕ) : ℂ) * (lam ((j : ℤ) + 1) / (Real.sqrt ((j : ℝ) + 1) : ℂ)) *
            grunsky f g ((j : ℤ) + 1) ((k : ℤ) + 1) +
          ((j + 1 : ℕ) : ℂ) * (lam (-((j : ℤ) + 1)) / (Real.sqrt ((j : ℝ) + 1) : ℂ)) *
            grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)))) =
      ∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
        grunsky f g ((k : ℤ) + 1) l * lam l := by
  have hspec := grunsky_spec h
  rw [mg_sum_erase, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hsym : grunsky f g ((j : ℤ) + 1) ((k : ℤ) + 1) = grunsky f g ((k : ℤ) + 1) ((j : ℤ) + 1) := by
    have := (hspec.2 j k).1
    simpa using this
  have hjj : (Real.sqrt ((j : ℝ) + 1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  have e1 : |(((k + 1 : ℕ) : ℝ) * (((((j : ℤ) + 1 : ℤ)) : ℝ)))| = ((k : ℝ) + 1) * ((j : ℝ) + 1) := by
    push_cast
    rw [abs_of_nonneg (by positivity)]
  have e2 : |(((k + 1 : ℕ) : ℝ) * (((-((j : ℤ) + 1) : ℤ) : ℝ)))| = ((k : ℝ) + 1) * ((j : ℝ) + 1) := by
    push_cast
    rw [abs_of_nonpos (by nlinarith [(by positivity : (0 : ℝ) ≤ (k : ℝ)), (by positivity : (0 : ℝ) ≤ (j : ℝ))])]
    ring
  rw [e1, e2, Real.sqrt_mul (by positivity), hsym]
  have hs : ((j + 1 : ℕ) : ℂ) = (Real.sqrt ((j : ℝ) + 1) : ℂ) * (Real.sqrt ((j : ℝ) + 1) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; ring
  rw [hs]
  push_cast
  field_simp

/-- Regrouping of the `f`-side coefficient. -/
theorem mg_coeff_f {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) (m j : ℕ) (lam : ℤ → ℂ) :
    ((Real.sqrt ((j : ℝ) + 1) : ℝ) : ℂ) * (∑ k ∈ Finset.range m,
        (((k + 1 : ℕ) : ℂ) * (lam ((k : ℤ) + 1) / (Real.sqrt ((k : ℝ) + 1) : ℂ)) *
            grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)) +
          ((k + 1 : ℕ) : ℂ) * (lam (-((k : ℤ) + 1)) / (Real.sqrt ((k : ℝ) + 1) : ℂ)) *
            grunsky f g (-((k : ℤ) + 1)) (-((j : ℤ) + 1)))) =
      ∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((j + 1 : ℕ) * l : ℝ)| : ℂ) *
        grunsky f g (-((j : ℤ) + 1)) l * lam l := by
  have hspec := grunsky_spec h
  rw [mg_sum_erase, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hsym1 : grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)) = grunsky f g (-((j : ℤ) + 1)) ((k : ℤ) + 1) := by
    have := h
    have h1 := hspec.1.2.2.2.2 (j + 1) k
    push_cast at h1
    exact h1.symm
  have hsym2 : grunsky f g (-((k : ℤ) + 1)) (-((j : ℤ) + 1)) = grunsky f g (-((j : ℤ) + 1)) (-((k : ℤ) + 1)) := by
    have h1 := (hspec.2 (k + 1) (j + 1)).2
    push_cast at h1
    exact h1
  have hkk : (Real.sqrt ((k : ℝ) + 1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  have e1 : |(((j + 1 : ℕ) : ℝ) * (((((k : ℤ) + 1 : ℤ)) : ℝ)))| = ((j : ℝ) + 1) * ((k : ℝ) + 1) := by
    push_cast
    rw [abs_of_nonneg (by positivity)]
  have e2 : |(((j + 1 : ℕ) : ℝ) * (((-((k : ℤ) + 1) : ℤ) : ℝ)))| = ((j : ℝ) + 1) * ((k : ℝ) + 1) := by
    push_cast
    rw [abs_of_nonpos (by nlinarith [(by positivity : (0 : ℝ) ≤ (k : ℝ)), (by positivity : (0 : ℝ) ≤ (j : ℝ))])]
    ring
  rw [e1, e2, Real.sqrt_mul (by positivity), hsym1, hsym2]
  have hs : ((k + 1 : ℕ) : ℂ) = (Real.sqrt ((k : ℝ) + 1) : ℂ) * (Real.sqrt ((k : ℝ) + 1) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; ring
  rw [hs]
  push_cast
  field_simp

theorem mg_norm_sq (k : ℕ) (z : ℂ) :
    ‖((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ) * z‖ ^ 2 = ((k + 1 : ℕ) : ℝ) * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity)]
  push_cast
  ring

theorem mg_norm_sq_div (k : ℕ) (z : ℂ) :
    ((k + 1 : ℕ) : ℝ) * ‖z / (Real.sqrt ((k : ℝ) + 1) : ℂ)‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity)]
  push_cast
  field_simp

/-- The `f`-side circle integral in final form. -/
theorem mg_f_final {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber f g P Q) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) (lam : ℤ → ℂ) :
    Summable (fun j : ℕ => ρ ^ (2 * (j + 1)) *
        ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((j + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (-(j + 1 : ℤ)) l * lam l)‖ ^ 2) ∧
    (∫ θ in (0 : ℝ)..2 * π,
        conj ((fun w : ℂ => ∑ n ∈ Finset.Icc 1 m,
          (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹))
          (f (circleMap 0 ρ θ))) *
        deriv (fun z => (fun w : ℂ => ∑ n ∈ Finset.Icc 1 m,
          (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹))
          (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ) =
      2 * π * ((((∑' j : ℕ, ρ ^ (2 * (j + 1)) *
        ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((j + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (-(j + 1 : ℤ)) l * lam l)‖ ^ 2) -
        ∑ n ∈ Finset.Icc 1 m, ‖lam (-(n : ℤ))‖ ^ 2 * (ρ ^ (2 * n))⁻¹) : ℝ) : ℂ) := by
  obtain ⟨hSf, hf⟩ := mg_f_side h hPQ hρ0 hρ1 m lam
  have hj : ∀ j : ℕ, ρ ^ (2 * (j + 1)) *
      ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((j + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (-(j + 1 : ℤ)) l * lam l)‖ ^ 2 =
      ((j + 1 : ℕ) : ℝ) * (‖∑ k ∈ Finset.range m,
        (((k + 1 : ℕ) : ℂ) * (lam ((k : ℤ) + 1) / (Real.sqrt ((k : ℝ) + 1) : ℂ)) *
            grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)) +
          ((k + 1 : ℕ) : ℂ) * (lam (-((k : ℤ) + 1)) / (Real.sqrt ((k : ℝ) + 1) : ℂ)) *
            grunsky f g (-((k : ℤ) + 1)) (-((j : ℤ) + 1)))‖ ^ 2 * ρ ^ (2 * (j + 1))) := by
    intro j
    rw [← mg_coeff_f h m j lam, mg_norm_sq]
    ring
  have hT : ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * (‖lam (-((k : ℤ) + 1)) / (Real.sqrt ((k : ℝ) + 1) : ℂ)‖ ^ 2 *
          (ρ ^ (2 * (k + 1)))⁻¹) = ∑ n ∈ Finset.Icc 1 m, ‖lam (-(n : ℤ))‖ ^ 2 * (ρ ^ (2 * n))⁻¹ := by
    rw [mg_sum_Icc_eq_range]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← mul_assoc, mg_norm_sq_div]
    push_cast
    ring_nf
  refine ⟨(hSf.congr (fun j => (hj j).symm)), ?_⟩
  rw [hf, hT]
  simp only [hj]

/-- The `g`-side circle integral in final form. -/
theorem mg_g_final {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber f g P Q) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) (lam : ℤ → ℂ) :
    Summable (fun k : ℕ => ρ ^ (2 * (k + 1)) *
        ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (k + 1) l * lam l)‖ ^ 2) ∧
    (∫ θ in (0 : ℝ)..2 * π,
        conj ((fun w : ℂ => ∑ n ∈ Finset.Icc 1 m,
          (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹))
          (g (circleMap 0 (1 / ρ) θ))) *
        deriv (fun z => (fun w : ℂ => ∑ n ∈ Finset.Icc 1 m,
          (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹))
          (g z)) (circleMap 0 (1 / ρ) θ) * circleMap 0 (1 / ρ) θ) =
      2 * π * ((((∑ n ∈ Finset.Icc 1 m, ‖lam n‖ ^ 2 * (ρ ^ (2 * n))⁻¹) -
        ∑' k : ℕ, ρ ^ (2 * (k + 1)) *
        ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (k + 1) l * lam l)‖ ^ 2) : ℝ) : ℂ) := by
  obtain ⟨hSg, hg'⟩ := mg_g_side h hPQ hρ0 hρ1 m lam
  have hk : ∀ k : ℕ, ρ ^ (2 * (k + 1)) *
      ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (k + 1) l * lam l)‖ ^ 2 =
      ((k + 1 : ℕ) : ℝ) * (‖∑ j ∈ Finset.range m,
        (((j + 1 : ℕ) : ℂ) * (lam ((j : ℤ) + 1) / (Real.sqrt ((j : ℝ) + 1) : ℂ)) *
            grunsky f g ((j : ℤ) + 1) ((k : ℤ) + 1) +
          ((j + 1 : ℕ) : ℂ) * (lam (-((j : ℤ) + 1)) / (Real.sqrt ((j : ℝ) + 1) : ℂ)) *
            grunsky f g ((k : ℤ) + 1) (-((j : ℤ) + 1)))‖ ^ 2 * ρ ^ (2 * (k + 1))) := by
    intro k
    rw [← mg_coeff_g h m k lam, mg_norm_sq]
    ring
  have hT : ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ) * (‖lam ((j : ℤ) + 1) / (Real.sqrt ((j : ℝ) + 1) : ℂ)‖ ^ 2 *
          (ρ ^ (2 * (j + 1)))⁻¹) = ∑ n ∈ Finset.Icc 1 m, ‖lam n‖ ^ 2 * (ρ ^ (2 * n))⁻¹ := by
    rw [mg_sum_Icc_eq_range]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← mul_assoc, mg_norm_sq_div]
    push_cast
    ring_nf
  refine ⟨(hSg.congr (fun j => (hk j).symm)), ?_⟩
  rw [hg', hT]
  simp only [hk]

/-- (M2) Energy of the gap for `U_lam`, in Grunsky coordinates. -/
theorem mg_gap_energy {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber f g P Q) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) (lam : ℤ → ℂ) :
    Summable (fun k : ℕ => ρ ^ (2 * (k + 1)) *
        (‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (k + 1) l * lam l)‖ ^ 2 +
          ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (-(k + 1 : ℤ)) l * lam l)‖ ^ 2)) ∧
    (∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ,
        ‖deriv (fun w : ℂ => ∑ n ∈ Finset.Icc 1 m,
          (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹)) w‖ ^ 2) =
      π * ((∑ n ∈ Finset.Icc 1 m, (‖lam n‖ ^ 2 + ‖lam (-(n : ℤ))‖ ^ 2) * (ρ ^ (2 * n))⁻¹) -
        ∑' k : ℕ, ρ ^ (2 * (k + 1)) *
          (‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
              grunsky f g (k + 1) l * lam l)‖ ^ 2 +
            ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
              grunsky f g (-(k + 1 : ℤ)) l * lam l)‖ ^ 2)) := by
  set U : ℂ → ℂ := fun w : ℂ => ∑ n ∈ Finset.Icc 1 m,
    (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹) with hU
  have hUd : DifferentiableOn ℂ U {0}ᶜ := by
    refine DifferentiableOn.fun_sum (fun n _ => ?_)
    refine DifferentiableOn.add ?_ ?_
    · exact (differentiableOn_const _).mul (Polynomial.differentiable _).differentiableOn
    · exact (differentiableOn_const _).mul
        ((Polynomial.differentiable (Q n)).comp_differentiableOn differentiableOn_inv)
  have hgreen := mg_gap_green h hρ0 hρ1 hUd
  obtain ⟨hS2, hf⟩ := mg_f_final h hPQ hρ0 hρ1 m lam
  obtain ⟨hS1, hg'⟩ := mg_g_final h hPQ hρ0 hρ1 m lam
  beta_reduce at hgreen hf hg'
  rw [hf, hg'] at hgreen
  have hS : (∑' k : ℕ, ρ ^ (2 * (k + 1)) *
          (‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
              grunsky f g (k + 1) l * lam l)‖ ^ 2 +
            ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
              grunsky f g (-(k + 1 : ℤ)) l * lam l)‖ ^ 2)) =
      (∑' k : ℕ, ρ ^ (2 * (k + 1)) *
        ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (k + 1) l * lam l)‖ ^ 2) +
      ∑' k : ℕ, ρ ^ (2 * (k + 1)) *
        ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (-(k + 1 : ℤ)) l * lam l)‖ ^ 2 := by
    simp only [mul_add]
    exact hS1.tsum_add hS2
  have hT : (∑ n ∈ Finset.Icc 1 m, (‖lam n‖ ^ 2 + ‖lam (-(n : ℤ))‖ ^ 2) * (ρ ^ (2 * n))⁻¹) =
      (∑ n ∈ Finset.Icc 1 m, ‖lam n‖ ^ 2 * (ρ ^ (2 * n))⁻¹) +
        ∑ n ∈ Finset.Icc 1 m, ‖lam (-(n : ℤ))‖ ^ 2 * (ρ ^ (2 * n))⁻¹ := by
    simp only [add_mul, Finset.sum_add_distrib]
  refine ⟨?_, ?_⟩
  · have := hS1.add hS2
    refine this.congr (fun k => ?_)
    ring
  · apply Complex.ofReal_injective
    rw [hgreen, hT, hS]
    simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    ring

theorem mg_radius_seq : ∃ r : ℕ → ℝ, (∀ n, 0 < r n ∧ r n < 1) ∧ Monotone r ∧ Tendsto r atTop (𝓝 1) := by
  refine ⟨fun n => 1 - 1 / ((n : ℝ) + 2), fun n => ?_, ?_, ?_⟩
  · have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h3 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    constructor
    · linarith
    · have : 0 < 1 / ((n : ℝ) + 2) := by positivity
      linarith
  · intro a b hab
    have h1 : (a : ℝ) ≤ b := by exact_mod_cast hab
    have h2 : 1 / ((b : ℝ) + 2) ≤ 1 / ((a : ℝ) + 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    show 1 - 1 / ((a : ℝ) + 2) ≤ 1 - 1 / ((b : ℝ) + 2)
    linarith
  · have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_add_atTop_iff_nat (f := fun n : ℕ => 1 / ((n : ℝ) + 1)) 1).mpr
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      refine this.congr (fun n => ?_)
      push_cast
      ring_nf
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1

/-- The gap integrals of `‖U'‖²` tend to the (null) integral over the complement `F`. -/
theorem mg_gap_integral_tendsto {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {U : ℂ → ℂ}
    (hU : DifferentiableOn ℂ U {0}ᶜ) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n ∧ r n < 1) (hmono : Monotone r)
    (hlim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => ∫ w in (f '' closedBall (0 : ℂ) (r n) ∪ g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ,
      ‖deriv U w‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨hfd, hfi, hf0, hf1, hgu, hdisj⟩ := h
  have h' : IsNormalizedDisjointPair f g := ⟨hfd, hfi, hf0, hf1, hgu, hdisj⟩
  have hUo : IsOpen unitDisc := isOpen_ball
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hcb : ∀ n, closedBall (0 : ℂ) (r n) ⊆ unitDisc := fun n z hz =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) (hr n).2)
  have hKf : ∀ n, IsClosed (f '' closedBall (0 : ℂ) (r n)) := fun n =>
    ((isCompact_closedBall (0 : ℂ) (r n)).image_of_continuousOn (hfd.continuousOn.mono (hcb n))).isClosed
  have hR : ∀ n, 1 < 1 / r n := fun n => one_lt_one_div (hr n).1 (hr n).2
  have hKg : ∀ n, IsClosed (g '' {z : ℂ | 1 / r n ≤ ‖z‖}) := fun n => mg_image_closed hgu (hR n)
  set S : ℕ → Set ℂ := fun n => (f '' closedBall (0 : ℂ) (r n) ∪ g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n => ((hKf n).union (hKg n)).measurableSet.compl
  have hanti : Antitone S := by
    intro a b hab
    have hrab : r a ≤ r b := hmono hab
    intro w hw hwb
    apply hw
    rcases hwb with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · exact Or.inl ⟨z, closedBall_subset_closedBall hrab hz, rfl⟩
    · refine Or.inr ⟨z, ?_, rfl⟩
      have : 1 / r b ≤ 1 / r a := one_div_le_one_div_of_le (hr a).1 hrab
      exact le_trans this hz
  -- integrability on the first gap
  have hint : IntegrableOn (fun w => ‖deriv U w‖ ^ 2) (S 0) := by
    obtain ⟨R1, hR1⟩ := mg_far_exterior h' (T := 1 / r 0) (by have := hR 0; positivity)
    set C : Set ℂ := closedBall (0 : ℂ) R1 ∩ (f '' ball (0 : ℂ) (r 0))ᶜ with hC
    have hopen : IsOpen (f '' ball (0 : ℂ) (r 0)) :=
      (RMT.differentiableOn_invFunOn_of_injOn isOpen_ball (hfd.mono (ball_subset_ball (hr 0).2.le))
        (hfi.mono (ball_subset_ball (hr 0).2.le))).1
    have hCc : IsCompact C := (isCompact_closedBall (0 : ℂ) R1).inter_right hopen.isClosed_compl
    have hC0 : C ⊆ {0}ᶜ := by
      intro w hw h0
      exact hw.2 ⟨0, mem_ball_self (hr 0).1, by rw [hf0, mem_singleton_iff.mp h0]⟩
    have hcont : ContinuousOn (fun w => ‖deriv U w‖ ^ 2) C := by
      have hU' : DifferentiableOn ℂ (deriv U) {0}ᶜ := hU.deriv isOpen_compl_singleton
      exact ((hU'.continuousOn.mono hC0).norm).pow 2
    refine (hcont.integrableOn_compact hCc).mono_set ?_
    intro w hw
    refine ⟨?_, fun hm => hw (Or.inl (image_mono ball_subset_closedBall hm))⟩
    by_contra hnot
    obtain ⟨z, hz, hzw⟩ := hR1 w (not_le.mp (by simpa [mem_closedBall_zero_iff] using hnot))
    exact hw (Or.inr ⟨z, hz, hzw⟩)
  have hT := Antitone.tendsto_setIntegral hSm hanti hint
  have hinter : (⋂ n, S n) ⊆ (f '' unitDisc ∪ g '' unitDiscExterior)ᶜ := by
    intro w hw hwU
    rw [mem_iInter] at hw
    rcases hwU with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hzn)).exists
      exact hw n (Or.inl ⟨z, mem_closedBall_zero_iff.mpr hn.le, rfl⟩)
    · have hzn : 1 < ‖z‖ := hz
      have hlim' : Tendsto (fun n => 1 / r n) atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).div hlim one_ne_zero
        rw [div_one] at this
        exact this.congr (fun n => by simp)
      obtain ⟨n, hn⟩ := (hlim'.eventually (gt_mem_nhds hzn)).exists
      exact hw n (Or.inr ⟨z, hn.le, rfl⟩)
  have h0 : ∫ w in ⋂ n, S n, ‖deriv U w‖ ^ 2 = 0 :=
    setIntegral_measure_zero _ (measure_mono_null hinter hF)
  rw [h0] at hT
  exact hT


/-- (M3) Grunsky equality for a null complement (diagonal case of `eq_2_1`). -/
theorem mg_equality_diag {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) (m : ℕ) (lam : ℤ → ℂ) :
    Summable (fun k : ℕ =>
        (‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (k + 1) l * lam l)‖ ^ 2 +
          ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (-(k + 1 : ℤ)) l * lam l)‖ ^ 2)) ∧
    (∑' k : ℕ,
        (‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (k + 1) l * lam l)‖ ^ 2 +
          ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (-(k + 1 : ℤ)) l * lam l)‖ ^ 2)) =
      ∑ n ∈ Finset.Icc 1 m, (‖lam n‖ ^ 2 + ‖lam (-(n : ℤ))‖ ^ 2) := by
  obtain ⟨P, Q, hPQ⟩ := faber_exists h
  obtain ⟨r, hr, hmono, hlim⟩ := mg_radius_seq
  set a : ℕ → ℝ := fun k : ℕ =>
    (‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (k + 1) l * lam l)‖ ^ 2 +
          ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (-(k + 1 : ℤ)) l * lam l)‖ ^ 2) with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => by positivity
  set T : ℝ := ∑ n ∈ Finset.Icc 1 m, (‖lam n‖ ^ 2 + ‖lam (-(n : ℤ))‖ ^ 2) with hT
  set U : ℂ → ℂ := fun w : ℂ => ∑ n ∈ Finset.Icc 1 m,
    (lam n / (Real.sqrt n : ℂ) * (P n).eval w + lam (-(n : ℤ)) / (Real.sqrt n : ℂ) * (Q n).eval w⁻¹) with hU
  have hUd : DifferentiableOn ℂ U {0}ᶜ := by
    refine DifferentiableOn.fun_sum (fun n _ => ?_)
    refine DifferentiableOn.add ?_ ?_
    · exact (differentiableOn_const _).mul (Polynomial.differentiable _).differentiableOn
    · exact (differentiableOn_const _).mul
        ((Polynomial.differentiable (Q n)).comp_differentiableOn differentiableOn_inv)
  set I : ℕ → ℝ := fun n => ∫ w in (f '' closedBall (0 : ℂ) (r n) ∪ g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ,
    ‖deriv U w‖ ^ 2 with hI
  set Tr : ℕ → ℝ := fun n => ∑ k ∈ Finset.Icc 1 m,
    (‖lam k‖ ^ 2 + ‖lam (-(k : ℤ))‖ ^ 2) * ((r n) ^ (2 * k))⁻¹ with hTr
  have hEn : ∀ n, Summable (fun k : ℕ => (r n) ^ (2 * (k + 1)) * a k) ∧
      I n = π * (Tr n - ∑' k : ℕ, (r n) ^ (2 * (k + 1)) * a k) := fun n =>
    mg_gap_energy h hPQ (hr n).1 (hr n).2 m lam
  have hI0 : ∀ n, 0 ≤ I n := fun n => integral_nonneg (fun w => by positivity)
  have hIlim : Tendsto I atTop (𝓝 0) := mg_gap_integral_tendsto h hF hUd hr hmono hlim
  have hTrlim : Tendsto Tr atTop (𝓝 T) := by
    have : Tendsto Tr atTop (𝓝 (∑ k ∈ Finset.Icc 1 m, (‖lam k‖ ^ 2 + ‖lam (-(k : ℤ))‖ ^ 2) * ((1 : ℝ) ^ (2 * k))⁻¹)) := by
      refine tendsto_finset_sum _ (fun k _ => ?_)
      refine Tendsto.const_mul _ ?_
      exact ((hlim.pow (2 * k)).inv₀ (by simp))
    simpa using this
  -- the weights tend to `1`
  have hw : ∀ k : ℕ, Tendsto (fun n => (r n) ^ (2 * (k + 1))) atTop (𝓝 1) := fun k => by
    simpa using hlim.pow (2 * (k + 1))
  have hwle : ∀ n k : ℕ, (r n) ^ (2 * (k + 1)) ≤ 1 := fun n k =>
    pow_le_one₀ (hr n).1.le (hr n).2.le
  have hSr : ∀ n, π * (Tr n - ∑' k : ℕ, (r n) ^ (2 * (k + 1)) * a k) ≥ 0 := fun n => by
    rw [← (hEn n).2]; exact hI0 n
  have hSr' : ∀ n, ∑' k : ℕ, (r n) ^ (2 * (k + 1)) * a k ≤ Tr n := fun n => by
    have := hSr n
    have hpi : 0 < π := Real.pi_pos
    nlinarith
  have hbound : ∀ K : ℕ, ∑ k ∈ Finset.range K, a k ≤ T := by
    intro K
    have h1 : ∀ n, ∑ k ∈ Finset.range K, (r n) ^ (2 * (k + 1)) * a k ≤ Tr n := fun n =>
      ((Summable.sum_le_tsum _ (fun k _ => mul_nonneg (by have := (hr n).1; positivity) (ha0 k)) (hEn n).1)).trans (hSr' n)
    have h2 : Tendsto (fun n => ∑ k ∈ Finset.range K, (r n) ^ (2 * (k + 1)) * a k) atTop
        (𝓝 (∑ k ∈ Finset.range K, a k)) := by
      have := tendsto_finset_sum (Finset.range K) (fun k _ => (hw k).mul_const (a k))
      simpa using this
    exact le_of_tendsto_of_tendsto h2 hTrlim (Eventually.of_forall h1)
  have hsum : Summable a := summable_of_sum_range_le ha0 hbound
  refine ⟨hsum, le_antisymm (Real.tsum_le_of_sum_range_le ha0 hbound) ?_⟩
  -- the other inequality
  have hge : ∀ n, Tr n - I n / π ≤ ∑' k, a k := by
    intro n
    have hpi : 0 < π := Real.pi_pos
    have h1 : I n / π = Tr n - ∑' k : ℕ, (r n) ^ (2 * (k + 1)) * a k := by
      rw [(hEn n).2]; field_simp
    rw [h1]
    have : ∑' k : ℕ, (r n) ^ (2 * (k + 1)) * a k ≤ ∑' k, a k :=
      (hEn n).1.tsum_le_tsum (fun k => by
        calc (r n) ^ (2 * (k + 1)) * a k ≤ 1 * a k := by gcongr; exact hwle n k
          _ = a k := one_mul _) hsum
    linarith
  have hlimT : Tendsto (fun n => Tr n - I n / π) atTop (𝓝 (T - 0 / π)) :=
    hTrlim.sub (hIlim.div_const π)
  rw [zero_div, sub_zero] at hlimT
  exact le_of_tendsto' hlimT hge


/-- A nonnegative `ℤ`-sequence vanishing at `0`, summable over the symmetric pairs, has the pair sum. -/
theorem mg_hasSum_int_of_nat {q : ℤ → ℝ} (h0 : q 0 = 0) (hq : ∀ k, 0 ≤ q k)
    (hs : Summable (fun k : ℕ => q ((k : ℤ) + 1) + q (-((k : ℤ) + 1)))) :
    HasSum q (∑' k : ℕ, (q ((k : ℤ) + 1) + q (-((k : ℤ) + 1)))) := by
  have hA : Summable (fun k : ℕ => q ((k : ℤ) + 1)) :=
    Summable.of_nonneg_of_le (fun k => hq _) (fun k => le_add_of_nonneg_right (hq _)) hs
  have hB : Summable (fun k : ℕ => q (-((k : ℤ) + 1))) :=
    Summable.of_nonneg_of_le (fun k => hq _) (fun k => le_add_of_nonneg_left (hq _)) hs
  have hA' : HasSum (fun n : ℕ => q (n : ℤ)) (∑' k : ℕ, q ((k : ℤ) + 1)) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    have h1 : HasSum (fun n : ℕ => q (((n + 1 : ℕ)) : ℤ)) (∑' k : ℕ, q ((k : ℤ) + 1)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hA.hasSum
    simpa [h0] using h1
  have := hA'.of_nat_of_neg_add_one hB.hasSum
  rwa [← Summable.tsum_add hA hB] at this

/-- (M4) The polarized Grunsky equality `eq_2_1`, with summability. -/
theorem mg_eq_2_1_hasSum {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) (m : ℕ) (lam eta : ℤ → ℂ) :
    HasSum (fun k : ℤ => if k = 0 then 0 else
        ∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ∑ l' ∈ (Finset.Icc (-(m : ℤ)) m).erase 0,
          (Real.sqrt |(k * l : ℝ)| : ℂ) * grunsky f g k l * Real.sqrt |(k * l' : ℝ)| * conj (grunsky f g k l') *
            lam l * conj (eta l'))
      (∑ k ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, lam k * conj (eta k)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℤ → (ℤ → ℂ) → ℂ, ∀ k μ, N k μ =
      ∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |(k * l : ℝ)| : ℂ) * grunsky f g k l * μ l :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨mu, hmu⟩ : ∃ mu : ℂ → ℤ → ℂ, ∀ t l, mu t l = lam l + t * eta l := ⟨_, fun _ _ => rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ → ℤ → ℝ, ∀ t k, q t k = if k = 0 then 0 else ‖N k (mu t)‖ ^ 2 :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℂ → ℝ, ∀ t, T t =
      ∑ n ∈ Finset.Icc 1 m, (‖mu t n‖ ^ 2 + ‖mu t (-(n : ℤ))‖ ^ 2) := ⟨_, fun _ => rfl⟩
  have hNadd : ∀ (k : ℤ) (t : ℂ), N k (mu t) = N k lam + t * N k eta := by
    intro k t
    simp only [hN, hmu, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun l _ => by ring)
  have hNpos : ∀ (k : ℕ) (μ : ℤ → ℂ), N ((k : ℤ) + 1) μ =
      ∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
        grunsky f g ((k : ℤ) + 1) l * μ l := by
    intro k μ
    rw [hN]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    first | (push_cast; rfl) | push_cast
  have hNneg : ∀ (k : ℕ) (μ : ℤ → ℂ), N (-((k : ℤ) + 1)) μ =
      ∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
        grunsky f g (-((k : ℤ) + 1)) l * μ l := by
    intro k μ
    rw [hN]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    push_cast
    rw [neg_mul, abs_neg]
  have hne1 : ∀ k : ℕ, ((k : ℤ) + 1 ≠ 0) := fun k => by omega
  have hne2 : ∀ k : ℕ, (-((k : ℤ) + 1) ≠ 0) := fun k => by omega
  have hdiag : ∀ t : ℂ, Summable (fun k : ℕ => ‖N ((k : ℤ) + 1) (mu t)‖ ^ 2 + ‖N (-((k : ℤ) + 1)) (mu t)‖ ^ 2) ∧
      ∑' k : ℕ, (‖N ((k : ℤ) + 1) (mu t)‖ ^ 2 + ‖N (-((k : ℤ) + 1)) (mu t)‖ ^ 2) = T t := by
    intro t
    have hfun : (fun k : ℕ => ‖N ((k : ℤ) + 1) (mu t)‖ ^ 2 + ‖N (-((k : ℤ) + 1)) (mu t)‖ ^ 2) =
        (fun k : ℕ =>
        (‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (k + 1) l * mu t l)‖ ^ 2 +
          ‖(∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, (Real.sqrt |((k + 1 : ℕ) * l : ℝ)| : ℂ) *
            grunsky f g (-(k + 1 : ℤ)) l * mu t l)‖ ^ 2)) := by
      funext k
      rw [hNpos, hNneg]
    rw [hfun, hTdef]
    exact mg_equality_diag h hF m (mu t)
  have hq : ∀ t : ℂ, HasSum (q t) (T t) := by
    intro t
    obtain ⟨hs, he⟩ := hdiag t
    have hqe : (fun k : ℕ => q t ((k : ℤ) + 1) + q t (-((k : ℤ) + 1))) =
        (fun k : ℕ => ‖N ((k : ℤ) + 1) (mu t)‖ ^ 2 + ‖N (-((k : ℤ) + 1)) (mu t)‖ ^ 2) := by
      funext k
      rw [hqdef, hqdef, if_neg (hne1 k), if_neg (hne2 k)]
    have key := mg_hasSum_int_of_nat (q := q t) (by rw [hqdef]; simp)
      (fun k => by rw [hqdef]; split_ifs <;> positivity) (by rw [hqe]; exact hs)
    rw [hqe, he] at key
    exact key
  have hb : ∀ k : ℤ, (if k = 0 then 0 else
        ∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ∑ l' ∈ (Finset.Icc (-(m : ℤ)) m).erase 0,
          (Real.sqrt |(k * l : ℝ)| : ℂ) * grunsky f g k l * Real.sqrt |(k * l' : ℝ)| * conj (grunsky f g k l') *
            lam l * conj (eta l')) =
      (((q 1 k : ℝ) : ℂ) - ((q (-1) k : ℝ) : ℂ) + (((q I k : ℝ) : ℂ) - ((q (-I) k : ℝ) : ℂ)) * I) / 4 := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [hqdef]
    · have hL : (∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ∑ l' ∈ (Finset.Icc (-(m : ℤ)) m).erase 0,
          (Real.sqrt |(k * l : ℝ)| : ℂ) * grunsky f g k l * Real.sqrt |(k * l' : ℝ)| * conj (grunsky f g k l') *
            lam l * conj (eta l')) = N k lam * conj (N k eta) := by
        simp only [hN, map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun l' _ => by ring))
      rw [if_neg hk, hL, bergman_polarization (N k lam) (N k eta)]
      simp only [hqdef, if_neg hk, hNadd, neg_mul, one_mul, ← sub_eq_add_neg]
  have hc : ∀ t : ℂ, HasSum (fun k : ℤ => ((q t k : ℝ) : ℂ)) ((T t : ℝ) : ℂ) := fun t =>
    Complex.hasSum_ofReal.mpr (hq t)
  have hsum := (((hc 1).sub (hc (-1))).add (((hc I).sub (hc (-I))).mul_right I)).div_const 4
  have hfun : (fun k : ℤ => if k = 0 then (0 : ℂ) else
        ∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ∑ l' ∈ (Finset.Icc (-(m : ℤ)) m).erase 0,
          (Real.sqrt |(k * l : ℝ)| : ℂ) * grunsky f g k l * Real.sqrt |(k * l' : ℝ)| * conj (grunsky f g k l') *
            lam l * conj (eta l')) =
      (fun k : ℤ => (((q 1 k : ℝ) : ℂ) - ((q (-1) k : ℝ) : ℂ) + (((q I k : ℝ) : ℂ) - ((q (-I) k : ℝ) : ℂ)) * I) / 4) :=
    funext hb
  rw [hfun]
  have hTr : ∀ t, T t = ∑ k ∈ Finset.range m, (‖mu t ((k : ℤ) + 1)‖ ^ 2 + ‖mu t (-((k : ℤ) + 1))‖ ^ 2) := by
    intro t
    rw [hTdef, mg_sum_Icc_eq_range (fun n : ℕ => ‖mu t n‖ ^ 2 + ‖mu t (-(n : ℤ))‖ ^ 2) m]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [mg_sum_erase (fun l => lam l * conj (eta l)) m]
  have hpt : ∀ k : ℕ,
      (((‖mu 1 ((k : ℤ) + 1)‖ ^ 2 + ‖mu 1 (-((k : ℤ) + 1))‖ ^ 2 : ℝ) : ℂ) -
        ((‖mu (-1) ((k : ℤ) + 1)‖ ^ 2 + ‖mu (-1) (-((k : ℤ) + 1))‖ ^ 2 : ℝ) : ℂ) +
      (((‖mu I ((k : ℤ) + 1)‖ ^ 2 + ‖mu I (-((k : ℤ) + 1))‖ ^ 2 : ℝ) : ℂ) -
        ((‖mu (-I) ((k : ℤ) + 1)‖ ^ 2 + ‖mu (-I) (-((k : ℤ) + 1))‖ ^ 2 : ℝ) : ℂ)) * I) =
      4 * (lam ((k : ℤ) + 1) * conj (eta ((k : ℤ) + 1)) +
        lam (-((k : ℤ) + 1)) * conj (eta (-((k : ℤ) + 1)))) := by
    intro k
    have pa := bergman_polarization (lam ((k : ℤ) + 1)) (eta ((k : ℤ) + 1))
    have pb := bergman_polarization (lam (-((k : ℤ) + 1))) (eta (-((k : ℤ) + 1)))
    simp only [Complex.ofReal_add, hmu, neg_mul, one_mul, ← sub_eq_add_neg]
    linear_combination (-4) * pa + (-4) * pb
  have hall : (((T 1 : ℝ) : ℂ) - ((T (-1) : ℝ) : ℂ) + (((T I : ℝ) : ℂ) - ((T (-I) : ℝ) : ℂ)) * I) =
      ∑ k ∈ Finset.range m, 4 * (lam ((k : ℤ) + 1) * conj (eta ((k : ℤ) + 1)) +
        lam (-((k : ℤ) + 1)) * conj (eta (-((k : ℤ) + 1)))) := by
    rw [hTr 1, hTr (-1), hTr I, hTr (-I)]
    simp only [Complex.ofReal_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => hpt k)
  have hval : (((T 1 : ℝ) : ℂ) - ((T (-1) : ℝ) : ℂ) + (((T I : ℝ) : ℂ) - ((T (-I) : ℝ) : ℂ)) * I) / 4 =
      ∑ k ∈ Finset.range m, (lam ((k : ℤ) + 1) * conj (eta ((k : ℤ) + 1)) +
        lam (-((k : ℤ) + 1)) * conj (eta (-((k : ℤ) + 1)))) := by
    rw [hall, ← Finset.mul_sum, mul_div_cancel_left₀ _ (by norm_num : (4 : ℂ) ≠ 0)]
  rw [← hval]
  exact hsum

/-- (M4) The polarized Grunsky equality `eq_2_1` (statement of `eq_2_1`). -/
theorem mg_eq_2_1 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) (m : ℕ) (lam eta : ℤ → ℂ) :
    (∑' k : ℤ, if k = 0 then 0 else
        ∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ∑ l' ∈ (Finset.Icc (-(m : ℤ)) m).erase 0,
          (Real.sqrt |(k * l : ℝ)| : ℂ) * grunsky f g k l * Real.sqrt |(k * l' : ℝ)| * conj (grunsky f g k l') *
            lam l * conj (eta l')) =
      ∑ k ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, lam k * conj (eta k) :=
  (mg_eq_2_1_hasSum h hF m lam eta).tsum_eq

/-! ### Original relocated (2026-10-26) -/

/-- **(2.1)** (TT:3856–3866). If `F` is a null set, then for all `λ, η` supported in `[-m, m] \ {0}`:
`Σ'_k Σ'_l Σ'_{l'} √|kl| b_{kl} √|kl'| \overline{b_{kl'}} λ_l η̄_{l'} = Σ'_k λ_k η̄_k`. -/
theorem eq_2_1 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) (m : ℕ) (lam eta : ℤ → ℂ) :
    (∑' k : ℤ, if k = 0 then 0 else
        ∑ l ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, ∑ l' ∈ (Finset.Icc (-(m : ℤ)) m).erase 0,
          (Real.sqrt |(k * l : ℝ)| : ℂ) * grunsky f g k l * Real.sqrt |(k * l' : ℝ)| * conj (grunsky f g k l') *
            lam l * conj (eta l')) =
      ∑ k ∈ (Finset.Icc (-(m : ℤ)) m).erase 0, lam k * conj (eta k) :=
  mg_eq_2_1 h hF m lam eta

end Ch2

end TakhtajanTeo
