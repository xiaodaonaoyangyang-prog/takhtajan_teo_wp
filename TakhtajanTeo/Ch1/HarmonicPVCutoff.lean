import TakhtajanTeo.Ch1.S4_Metrics

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real symmDiff
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The image of a Euclidean pole cutoff in the centered disk coordinate (TT:2613). -/
def wp_cayleyCutoff (r : ℝ) : Set ℂ :=
  {v | v ∈ unitDisc ∧ r * ‖1 - v‖ ≤ ‖v‖}

/-- The distorted cutoff remains measurable (TT:2613). -/
theorem wp_cayleyCutoff_measurable (r : ℝ) : MeasurableSet (wp_cayleyCutoff r) := by
  exact measurableSet_ball.inter (measurableSet_le (by fun_prop) measurable_norm)

/-- Two concentric cutoffs bound the image of a Euclidean cutoff (TT:2613). -/
theorem wp_cayleyCutoff_sandwich {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    unitDisc \ ball (0 : ℂ) (r / (1 - r)) ⊆ wp_cayleyCutoff r ∧
      wp_cayleyCutoff r ⊆ unitDisc \ ball (0 : ℂ) (r / (1 + r)) := by
  have hd : 0 < 1 - r := sub_pos.mpr hr1
  have hp : 0 < 1 + r := by linarith
  constructor
  · intro v hv
    have hn : r / (1 - r) ≤ ‖v‖ := by simpa [mem_ball_zero_iff] using hv.2
    have h := (div_le_iff₀ hd).mp hn
    refine ⟨hv.1, ?_⟩
    calc
      r * ‖1 - v‖ ≤ r * (1 + ‖v‖) := by
        apply mul_le_mul_of_nonneg_left _ hr.le
        simpa only [norm_one] using norm_sub_le (1 : ℂ) v
      _ ≤ ‖v‖ := by nlinarith
  · intro v hv
    refine ⟨hv.1, ?_⟩
    have hn : 1 - ‖v‖ ≤ ‖1 - v‖ := by
      simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) v
    have h := (mul_le_mul_of_nonneg_left hn hr.le).trans hv.2
    have hbound : r / (1 + r) ≤ ‖v‖ := (div_le_iff₀ hp).mpr (by nlinarith)
    simpa only [mem_ball_zero_iff, not_lt] using hbound

/-- The mismatch of radial and Euclidean cutoffs lies in a thin annulus (TT:2613). -/
theorem wp_cayleyCutoff_symmDiff {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    wp_cayleyCutoff r ∆ (unitDisc \ ball (0 : ℂ) r) ⊆
      closedBall (0 : ℂ) (r / (1 - r)) \ ball (0 : ℂ) (r / (1 + r)) := by
  have h := wp_cayleyCutoff_sandwich hr hr1
  have ha : r / (1 + r) ≤ r := (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  have hb : r ≤ r / (1 - r) := (le_div_iff₀ (by linarith)).mpr (by nlinarith)
  intro v hv
  rcases hv with ⟨hvS, hvR⟩ | ⟨hvR, hvS⟩
  · refine ⟨mem_closedBall_zero_iff.mpr ?_, (h.2 hvS).2⟩
    have hn : ‖v‖ < r := by
      by_contra hn
      exact hvR ⟨hvS.1, by simpa only [mem_ball_zero_iff] using hn⟩
    exact hn.le.trans hb
  · have hn : r ≤ ‖v‖ := by simpa only [mem_ball_zero_iff, not_lt] using hvR.2
    refine ⟨mem_closedBall_zero_iff.mpr ?_, ?_⟩
    · by_contra hn'
      apply hvS
      apply h.1
      exact ⟨hvR.1, by simpa only [mem_ball_zero_iff, not_lt] using (not_le.mp hn').le⟩
    · simpa only [mem_ball_zero_iff, not_lt] using ha.trans hn

/-- Dividing the annulus area by its inner squared radius gives a vanishing bound (TT:2613). -/
theorem wp_cayleyCutoff_area_factor {r : ℝ} (hr : 0 < r) (hrh : r < 1 / 2) :
    ((r / (1 - r)) ^ 2 - (r / (1 + r)) ^ 2) / (r / (1 + r)) ^ 2 ≤ 16 * r := by
  have hr0 : r ≠ 0 := hr.ne'
  have hp : 1 + r ≠ 0 := by linarith
  have hm : 1 - r ≠ 0 := by linarith
  have he : ((r / (1 - r)) ^ 2 - (r / (1 + r)) ^ 2) / (r / (1 + r)) ^ 2 =
      4 * r / (1 - r) ^ 2 := by
    field_simp
    <;> ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_ne_zero hm)).mpr
  have hquarter : (1 / 4 : ℝ) ≤ (1 - r) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hquarter hr.le]


/-- A quadratic pole is integrable on every measurable disk subset separated from zero (TT:2613). -/
theorem wp_disk_cutoff_integrable {F : ℂ → ℂ} (hF : ContinuousOn F (unitDisc \ {0}))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ v ∈ unitDisc, v ≠ 0 → ‖F v‖ ≤ M / ‖v‖ ^ 2)
    {S : Set ℂ} (hS : MeasurableSet S) (hSD : S ⊆ unitDisc)
    {a : ℝ} (ha : 0 < a) (hsep : ∀ v ∈ S, a ≤ ‖v‖) : IntegrableOn F S := by
  have hsub : S ⊆ unitDisc \ {0} := by
    intro v hv
    exact ⟨hSD hv, norm_pos_iff.mp (ha.trans_le (hsep v hv))⟩
  have hfin : volume S < ∞ := (measure_mono (hSD.trans ball_subset_closedBall)).trans_lt
    (isCompact_closedBall (0 : ℂ) 1).measure_lt_top
  apply IntegrableOn.of_bound hfin ((hF.mono hsub).aestronglyMeasurable hS) (M / a ^ 2)
  filter_upwards [ae_restrict_mem hS] with v hv
  exact (hb v (hSD hv) (hsub hv).2).trans
    (div_le_div_of_nonneg_left hM (sq_pos_of_pos ha) (pow_le_pow_left₀ ha.le (hsep v hv) 2))

/-- Area of a closed/open planar annulus, including its null boundary circles (TT:2613). -/
theorem wp_complex_annulus_area {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    volume.real (closedBall (0 : ℂ) b \ ball (0 : ℂ) a) = π * (b ^ 2 - a ^ 2) := by
  rw [measureReal_sdiff (ball_subset_closedBall.trans (closedBall_subset_closedBall hab))
    measurableSet_ball (isCompact_closedBall (0 : ℂ) b).measure_lt_top.ne]
  simp only [Measure.real, Complex.volume_closedBall, Complex.volume_ball, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal (ha.trans hab),
    ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

/-- The integral difference over two cutoffs is controlled by their mismatch annulus (TT:2613). -/
theorem wp_cutoff_integral_diff_bound {F : ℂ → ℂ} {S T A : Set ℂ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hA : MeasurableSet A)
    (hSi : IntegrableOn F S) (hTi : IntegrableOn F T) (hfin : volume A < ∞)
    (hsub : S ∆ T ⊆ A) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v ∈ A, ‖F v‖ ≤ C) :
    ‖(∫ v in S, F v) - ∫ v in T, F v‖ ≤ C * volume.real A := by
  let G : ℂ → ℂ := fun v => S.indicator F v - T.indicator F v
  have hGi : Integrable G := (hSi.integrable_indicator hS).sub (hTi.integrable_indicator hT)
  have he : (∫ v in S, F v) - ∫ v in T, F v = ∫ v in A, G v := by
    rw [← integral_indicator hS, ← integral_indicator hT, ← integral_sub
      (hSi.integrable_indicator hS) (hTi.integrable_indicator hT), ← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards with v
    by_cases hv : v ∈ A
    · simp only [indicator_of_mem hv, G]
    · have hn : v ∉ S ∆ T := fun hh => hv (hsub hh)
      by_cases hs : v ∈ S <;> by_cases ht : v ∈ T
      · simp [G, hs, ht, hv]
      · exact False.elim (hn (Or.inl ⟨hs, ht⟩))
      · exact False.elim (hn (Or.inr ⟨ht, hs⟩))
      · simp [G, hs, ht, hv]
  rw [he]
  apply norm_setIntegral_le_of_norm_le_const hfin
  intro v hv
  by_cases hs : v ∈ S <;> by_cases ht : v ∈ T
  · simpa [G, hs, ht] using hC
  · simpa [G, hs, ht] using hb v hv
  · simpa [G, hs, ht] using hb v hv
  · simpa [G, hs, ht] using hC


/-- The Euclidean/radial cutoff error is O(r) for a bounded quadratic pole (TT:2613). -/
theorem wp_cayleyCutoff_integral_error {F : ℂ → ℂ} (hF : ContinuousOn F (unitDisc \ {0}))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ v ∈ unitDisc, v ≠ 0 → ‖F v‖ ≤ M / ‖v‖ ^ 2)
    {r : ℝ} (hr : 0 < r) (hrh : r < 1 / 2) :
    ‖(∫ v in wp_cayleyCutoff r, F v) - ∫ v in unitDisc \ ball (0 : ℂ) r, F v‖ ≤
      16 * π * M * r := by
  let a := r / (1 + r)
  let b := r / (1 - r)
  let A := closedBall (0 : ℂ) b \ ball (0 : ℂ) a
  have hr1 : r < 1 := by linarith
  have ha : 0 < a := div_pos hr (by linarith)
  have hab : a ≤ b := div_le_div_of_nonneg_left hr.le (by linarith) (by linarith)
  have hbr : b < 1 := (div_lt_one (by linarith : 0 < 1 - r)).mpr (by linarith)
  have hsand := wp_cayleyCutoff_sandwich hr hr1
  have hsep : ∀ v ∈ wp_cayleyCutoff r, a ≤ ‖v‖ := by
    intro v hv
    simpa only [mem_ball_zero_iff, not_lt] using (hsand.2 hv).2
  have hSi := wp_disk_cutoff_integrable hF hM hb (wp_cayleyCutoff_measurable r)
    (fun _ hv => hv.1) ha hsep
  have hTint : IntegrableOn F (unitDisc \ ball (0 : ℂ) r) := by
    apply wp_disk_cutoff_integrable hF hM hb (measurableSet_ball.diff measurableSet_ball)
      Set.sdiff_subset hr
    intro v hv
    simpa only [mem_ball_zero_iff, not_lt] using hv.2
  have hAfin : volume A < ∞ := (measure_mono Set.sdiff_subset).trans_lt
    (isCompact_closedBall (0 : ℂ) b).measure_lt_top
  have hAB : ∀ v ∈ A, ‖F v‖ ≤ M / a ^ 2 := by
    intro v hv
    have hlo : a ≤ ‖v‖ := by simpa only [mem_ball_zero_iff, not_lt] using hv.2
    have hhi : ‖v‖ ≤ b := mem_closedBall_zero_iff.mp hv.1
    exact (hb v (mem_ball_zero_iff.mpr (hhi.trans_lt hbr))
      (norm_pos_iff.mp (ha.trans_le hlo))).trans
      (div_le_div_of_nonneg_left hM (sq_pos_of_pos ha) (pow_le_pow_left₀ ha.le hlo 2))
  have he := wp_cutoff_integral_diff_bound (wp_cayleyCutoff_measurable r)
    (measurableSet_ball.diff measurableSet_ball) (measurableSet_closedBall.diff measurableSet_ball)
    hSi hTint hAfin (wp_cayleyCutoff_symmDiff hr hr1) (div_nonneg hM (sq_nonneg a)) hAB
  have harea : volume.real A = π * (b ^ 2 - a ^ 2) := wp_complex_annulus_area ha.le hab
  rw [harea] at he
  refine he.trans ?_
  calc
    M / a ^ 2 * (π * (b ^ 2 - a ^ 2)) = (π * M) * ((b ^ 2 - a ^ 2) / a ^ 2) := by ring
    _ ≤ (π * M) * (16 * r) := mul_le_mul_of_nonneg_left (wp_cayleyCutoff_area_factor hr hrh)
      (mul_nonneg Real.pi_pos.le hM)
    _ = 16 * π * M * r := by ring


/-- Radial principal-value cancellation persists under the Euclidean cutoff distortion (TT:2613). -/
theorem wp_cayleyCutoff_tendsto_zero {F : ℂ → ℂ} (hF : ContinuousOn F (unitDisc \ {0}))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ v ∈ unitDisc, v ≠ 0 → ‖F v‖ ≤ M / ‖v‖ ^ 2)
    (hzero : ∀ r : ℝ, 0 < r → r < 1 → (∫ v in unitDisc \ ball (0 : ℂ) r, F v) = 0) :
    Tendsto (fun r : ℝ => ∫ v in wp_cayleyCutoff r, F v) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun r : ℝ => 16 * π * M * r) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => 16 * π * M * r) := by fun_prop
    simpa only [mul_zero] using (hc.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with r hr hrh
  have he := wp_cayleyCutoff_integral_error hF hM hb hr hrh
  rw [hzero r hr (by linarith), sub_zero] at he
  exact he

end TakhtajanTeo
