import TakhtajanTeo.Ch1.Eq22PunctureCutoff

/-! Local boundedness and shrinking-hole estimates for the paired remainder. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- P1
theorem eq22_remainder_uniform_bound {q u v z : ℂ} {B V η a : ℝ}
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hη : 0 < η) (ha : 0 < a)
    (hq : ‖q‖ ≤ B) (hv : ‖v-z‖ ≤ V) (hu : η ≤ ‖u-z‖) (hv' : a ≤ ‖v-z‖) :
    ‖q*(u-v)^3/((u-z)^3*(v-z))‖ ≤ B*(1+V/η)^3/a := by
  have hd : 0 < ‖u-z‖ := hη.trans_le hu
  have hratio : ‖u-v‖/‖u-z‖ ≤ 1+V/η := by
    calc
      ‖u-v‖/‖u-z‖ ≤ (‖u-z‖+‖v-z‖)/‖u-z‖ := by
        apply div_le_div_of_nonneg_right _ hd.le
        simpa only [norm_sub_rev z v] using norm_sub_le_norm_sub_add_norm_sub u z v
      _ = 1+‖v-z‖/‖u-z‖ := by field_simp
      _ ≤ 1+V/η := by gcongr
  simp only [norm_div,norm_mul,norm_pow]
  calc
    ‖q‖*‖u-v‖^3/(‖u-z‖^3*‖v-z‖) = ‖q‖*(‖u-v‖/‖u-z‖)^3/‖v-z‖ := by
      simp only [div_eq_mul_inv,mul_inv,div_pow,mul_pow,inv_pow]
      ring
    _ ≤ B*(1+V/η)^3/a := by gcongr

-- P2
theorem eq22_puncture_dzbar_zero {b : ℂ → ℂ} {p w : ℂ} {r : ℝ}
    (hb : ∀ v, r ≤ ‖v-p‖ → b v = 0) (hw : r < ‖w-p‖) : dzbar b w = 0 := by
  have he : b =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
    filter_upwards [(isOpen_lt continuous_const ((continuous_id.sub continuous_const).norm)).mem_nhds hw] with v hv
    exact hb v hv.le
  unfold dzbar
  rw [he.fderiv_eq]
  simp

-- P3
theorem eq22_small_hole_tail {Ω : Set ℂ} (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) {R : ℂ → ℂ} {p : ℂ} {r₀ B M : ℝ}
    (hRm : AEStronglyMeasurable R (volume.restrict Ω))
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hball : ball p r₀ ⊆ Ω) (hR : ∀ v ∈ ball p r₀, ‖R v‖ ≤ B)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hrsmall : ∀ n, 2*r n ≤ r₀) {θ b : ℕ → ℂ → ℂ}
    (hθ : ∀ n, Continuous (θ n)) (hθb : ∀ n v, ‖θ n v‖ ≤ 1)
    (hb : ∀ n, ContDiff ℝ 1 (b n))
    (hb0 : ∀ n v, r n ≤ ‖v-p‖ → b n v = 0)
    (hbd : ∀ n v, ‖dzbar (b n) v‖ ≤ M/r n) :
    (∀ n, IntegrableOn (fun v => R v*θ n v*dzbar (b n) v) Ω) ∧
    Tendsto (fun n => ∫ v in Ω, R v*θ n v*dzbar (b n) v) atTop (𝓝 0) := by
  let F : ℕ → ℂ → ℂ := fun n v => R v*θ n v*dzbar (b n) v
  have hballn : ∀ n, ball p (2*r n) ⊆ Ω := fun n =>
    (ball_subset_ball (hrsmall n)).trans hball
  have hzero : ∀ n v, v ∉ ball p (2*r n) → F n v = 0 := by
    intro n v hv
    have hn : 2*r n ≤ ‖v-p‖ := by simpa only [mem_ball,dist_eq_norm,not_lt] using hv
    have hd := eq22_puncture_dzbar_zero (hb0 n) (show r n < ‖v-p‖ by linarith [hr n])
    simp only [F,hd,mul_zero]
  have hzeroΩ : ∀ n v, v ∉ Ω → F n v = 0 := fun n v hv =>
    hzero n v (fun hw => hv (hballn n hw))
  have hbound : ∀ n v, v ∈ Ω → ‖F n v‖ ≤ B*M/r n := by
    intro n v hv
    by_cases hvr : v ∈ ball p (2*r n)
    · have hRv := hR v (ball_subset_ball (hrsmall n) hvr)
      simp only [F,norm_mul]
      calc
        ‖R v‖*‖θ n v‖*‖dzbar (b n) v‖ ≤ B*1*(M/r n) := mul_le_mul
          (mul_le_mul hRv (hθb n v) (norm_nonneg _) hB) (hbd n v) (norm_nonneg _) (by positivity)
        _ = B*M/r n := by ring
    · rw [hzero n v hvr,norm_zero]
      exact div_nonneg (mul_nonneg hB hM) (hr n).le
  haveI : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hΩb.measure_lt_top⟩
  have hFi : ∀ n, IntegrableOn (F n) Ω := by
    intro n
    have hm : AEStronglyMeasurable (F n) (volume.restrict Ω) :=
      (hRm.mul (hθ n).aestronglyMeasurable).mul (continuous_dzbar (hb n)).aestronglyMeasurable
    exact (integrable_const (B*M/r n)).mono' hm
      ((ae_restrict_mem hΩm).mono (fun v hv => hbound n v hv))
  have hnorm : ∀ n, ‖∫ v in Ω, F n v‖ ≤ (4*π*B*M)*r n := by
    intro n
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hzeroΩ n),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (hzero n)]
    have hsmall := eq22_puncture_error_bound (r := 2*r n) (M := 2*M)
      (mul_pos (by norm_num) (hr n)) hB (by positivity)
      (F := fun v => R v*θ n v) (b := b n) (a := p) (fun v hv => by
        rw [norm_mul]
        simpa only [mul_one] using mul_le_mul (hR v (ball_subset_ball (hrsmall n) hv))
          (hθb n v) (norm_nonneg _) hB) (fun v _ => by
            convert hbd n v using 1 <;> field_simp)
    apply hsmall.trans_eq
    ring
  refine ⟨hFi,?_⟩
  exact squeeze_zero_norm hnorm (by simpa using hrlim.const_mul (4*π*B*M))

end TakhtajanTeo
