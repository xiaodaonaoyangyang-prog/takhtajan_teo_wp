import TakhtajanTeo.Ch1.QCVariationKernel
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Laurent expansion of exterior integrable quadratic differentials

Regularity at infinity removes the singularity of the quadratic pullback at zero.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

/-- The quadratic pullback before filling its value at the origin. -/
def qcv_quadraticPullback (φ : ℂ → ℂ) (z : ℂ) : ℂ := φ z⁻¹ / z ^ 4

/-- Inversion takes the punctured disk into the exterior. -/
theorem qcv_inv_mem_exterior {z : ℂ} (hz : z ∈ unitDisc \ {0}) :
    z⁻¹ ∈ unitDiscExterior := by
  have hz0 : z ≠ 0 := hz.2
  change 1 < ‖z⁻¹‖
  rw [norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr (mem_ball_zero_iff.mp hz.1)

theorem qcv_quadraticPullback_differentiableOn {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDiscExterior) :
    DifferentiableOn ℂ (qcv_quadraticPullback φ) (unitDisc \ {0}) := by
  intro z hz
  have hz0 : z ≠ 0 := hz.2
  have hi : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) z := differentiableAt_inv hz0
  have he := qcv_inv_mem_exterior hz
  have hd := hφ.differentiableAt
    ((isOpen_lt continuous_const continuous_norm).mem_nhds he)
  exact ((hd.comp z hi).div (differentiableAt_id.pow 4)
    (pow_ne_zero 4 hz0)).differentiableWithinAt

/-- Fourth-order decay gives a bounded quadratic pullback near the origin. -/
theorem qcv_quadraticPullback_bounded {φ : ℂ → ℂ}
    (hφ : ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖φ z‖ ≤ C / ‖z‖ ^ 4) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      BddAbove ((norm ∘ qcv_quadraticPullback φ) '' (ball 0 r \ {0})) := by
  obtain ⟨C, R, hbound⟩ := hφ
  let M : ℝ := max R 1 + 1
  have hM : 1 < M := by dsimp [M]; linarith [le_max_right R 1]
  refine ⟨M⁻¹, by positivity, (inv_le_one₀ (by linarith)).mpr hM.le, C, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz0 : z ≠ 0 := hz.2
  have hn0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzr : ‖z‖ < M⁻¹ := mem_ball_zero_iff.mp hz.1
  have hlarge : R < ‖z⁻¹‖ := by
    rw [norm_inv]
    have hMi : M < ‖z‖⁻¹ := (lt_inv_comm₀ hn0 (lt_trans zero_lt_one hM)).mp hzr
    dsimp [M] at hMi
    linarith [le_max_left R 1]
  have hb := hbound z⁻¹ hlarge
  change ‖φ z⁻¹ / z ^ 4‖ ≤ C
  rw [norm_div, norm_pow, div_le_iff₀ (pow_pos hn0 4)]
  simpa only [norm_inv, inv_pow, div_inv_eq_mul] using hb

/-- An admissible exterior quadratic differential extends holomorphically after inversion. -/
theorem qcv_AOneStar_exists_disc_extension {φ : ℂ → ℂ} (hφ : φ ∈ AOneStar) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F unitDisc ∧
      ∀ z ∈ unitDisc \ {0}, F z = φ z⁻¹ / z ^ 4 := by
  let f := qcv_quadraticPullback φ
  let F := Function.update f 0 (limUnder (𝓝[≠] (0 : ℂ)) f)
  have hd := qcv_quadraticPullback_differentiableOn hφ.1
  obtain ⟨r, hr, hr1, hb⟩ := qcv_quadraticPullback_bounded hφ.2.2
  have hsmall : ball (0 : ℂ) r \ {0} ⊆ unitDisc \ {0} :=
    sdiff_subset_sdiff_left (ball_subset_ball hr1)
  have hFsmall : DifferentiableOn ℂ F (ball 0 r) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds _ hr)
      (hd.mono hsmall) hb
  refine ⟨F, ?_, ?_⟩
  · intro z hz
    by_cases hz0 : z = 0
    · subst z
      exact (hFsmall.differentiableAt (ball_mem_nhds _ hr)).differentiableWithinAt
    · have heq : F =ᶠ[𝓝 z] f := by
        filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
        exact Function.update_of_ne hw _ _
      have hdz : DifferentiableAt ℂ f z := hd.differentiableAt
        ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz, hz0⟩)
      exact (hdz.congr_of_eventuallyEq heq).differentiableWithinAt
  · intro z hz
    exact Function.update_of_ne hz.2 _ _

/-- Every admissible exterior test has a Laurent expansion beginning with degree `-4`. -/
theorem qcv_AOneStar_hasSum_laurent {φ : ℂ → ℂ} (hφ : φ ∈ AOneStar) :
    ∃ c : ℕ → ℂ, ∀ w ∈ unitDiscExterior,
      HasSum (fun n => c n / w ^ (n + 4)) (φ w) := by
  obtain ⟨F, hF, heq⟩ := qcv_AOneStar_exists_disc_extension hφ
  refine ⟨fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0, ?_⟩
  intro w hw
  have hw1 : 1 < ‖w‖ := hw
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hw1)
  have hi0 : w⁻¹ ≠ 0 := inv_ne_zero hw0
  have hi : w⁻¹ ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr
    rw [norm_inv]
    exact (inv_lt_one₀ (lt_trans zero_lt_one hw1)).mpr hw1
  have hs := (Complex.hasSum_taylorSeries_on_ball hF hi).mul_right (w ^ 4)⁻¹
  have hf : F w⁻¹ * (w ^ 4)⁻¹ = φ w := by
    rw [heq _ ⟨hi, hi0⟩, inv_inv, inv_pow]
    field_simp
  rw [hf] at hs
  convert hs using 1
  ext n
  simp only [sub_zero, smul_eq_mul, inv_pow, pow_add, div_eq_mul_inv, mul_inv]
  ring

end QCV
end TakhtajanTeo
