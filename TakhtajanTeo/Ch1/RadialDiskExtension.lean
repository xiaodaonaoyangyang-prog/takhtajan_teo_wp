import TakhtajanTeo.Ch1.S1_2_Homogeneous
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Normed.Group.CocompactMap
/-! # Explicit radial extension of disk maps

This module proves the topological and exterior C¹ parts of the explicit
extension used for disk Möbius maps. It does not assert a QC distortion bound.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Preserve the disk map and extend its boundary values radially outside. -/
def radialDiskExtension (m : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 then m z else (‖z‖ : ℂ) * m (z / (‖z‖ : ℂ))

theorem radialDiskExtension_eq_closed {m : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) : radialDiskExtension m z = m z := by
  simp only [radialDiskExtension, if_pos (mem_closedBall_zero_iff.mp hz)]

theorem norm_div_norm_eq_one {z : ℂ} (hz : z ≠ 0) : ‖z / (‖z‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hz)]

theorem radialDiskExtension_norm_exterior {m : ℂ → ℂ}
    (hm : ∀ z : ℂ, ‖z‖ = 1 → ‖m z‖ = 1) {z : ℂ} (hz : 1 < ‖z‖) :
    ‖radialDiskExtension m z‖ = ‖z‖ := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  rw [radialDiskExtension, if_neg (not_le.mpr hz), norm_mul,
    Complex.norm_of_nonneg (norm_nonneg _), hm _ (norm_div_norm_eq_one hz0), mul_one]

theorem radialDiskExtension_continuous {m : ℂ → ℂ}
    (hm : ContinuousOn m (closedBall (0 : ℂ) 1)) : Continuous (radialDiskExtension m) := by
  have hdir : ContinuousOn (fun z : ℂ => z / (‖z‖ : ℂ)) {z : ℂ | 1 ≤ ‖z‖} :=
    continuousOn_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousOn
      (fun z hz => by exact_mod_cast (show ‖z‖ ≠ 0 by linarith [show 1 ≤ ‖z‖ from hz]))
  have hmap : MapsTo (fun z : ℂ => z / (‖z‖ : ℂ)) {z : ℂ | 1 ≤ ‖z‖}
      (closedBall (0 : ℂ) 1) := by
    intro z hz
    exact mem_closedBall_zero_iff.mpr (norm_div_norm_eq_one
      (norm_ne_zero_iff.mp (by linarith [show 1 ≤ ‖z‖ from hz]))).le
  apply continuous_if_le continuous_norm continuous_const
    (hm.mono (fun _ hz => mem_closedBall_zero_iff.mpr hz))
    ((Complex.continuous_ofReal.comp continuous_norm).continuousOn.mul (hm.comp hdir hmap))
  intro z hz
  simp [hz]

theorem radialDiskExtension_bijective {m : ℂ → ℂ}
    (hi : InjOn m (closedBall (0 : ℂ) 1))
    (hc : m '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1)
    (hs : m '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1) :
    Function.Bijective (radialDiskExtension m) := by
  have hm : ∀ z : ℂ, ‖z‖ = 1 → ‖m z‖ = 1 := by
    intro z hz
    exact mem_sphere_zero_iff_norm.mp (hs ▸ mem_image_of_mem m (mem_sphere_zero_iff_norm.mpr hz))
  have hmc : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖m z‖ ≤ 1 := by
    intro z hz
    exact mem_closedBall_zero_iff.mp (hc ▸ mem_image_of_mem m (mem_closedBall_zero_iff.mpr hz))
  constructor
  · intro x y he
    by_cases hx : ‖x‖ ≤ 1 <;> by_cases hy : ‖y‖ ≤ 1
    · rw [radialDiskExtension, if_pos hx, radialDiskExtension, if_pos hy] at he
      exact hi (mem_closedBall_zero_iff.mpr hx) (mem_closedBall_zero_iff.mpr hy) he
    · have hn := congrArg norm he
      rw [radialDiskExtension_norm_exterior hm (not_le.mp hy), radialDiskExtension, if_pos hx] at hn
      have := hmc x hx
      exfalso
      linarith
    · have hn := congrArg norm he
      rw [radialDiskExtension_norm_exterior hm (not_le.mp hx), radialDiskExtension, if_pos hy] at hn
      have := hmc y hy
      exfalso
      linarith
    · have hn := congrArg norm he
      rw [radialDiskExtension_norm_exterior hm (not_le.mp hx),
        radialDiskExtension_norm_exterior hm (not_le.mp hy)] at hn
      have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by linarith [not_le.mp hx])
      have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (by linarith [not_le.mp hy])
      rw [radialDiskExtension, if_neg hx, radialDiskExtension, if_neg hy, hn] at he
      have hd := hi (mem_closedBall_zero_iff.mpr (norm_div_norm_eq_one hx0).le)
        (mem_closedBall_zero_iff.mpr (norm_div_norm_eq_one hy0).le)
        (by rw [hn]; exact mul_left_cancel₀ (by exact_mod_cast norm_ne_zero_iff.mpr hy0) he)
      rw [hn] at hd
      exact (div_left_inj' (by exact_mod_cast norm_ne_zero_iff.mpr hy0)).mp hd
  · intro w
    by_cases hw : ‖w‖ ≤ 1
    · have hwc : w ∈ m '' closedBall (0 : ℂ) 1 := by rw [hc]; exact mem_closedBall_zero_iff.mpr hw
      obtain ⟨z, hz, he⟩ := hwc
      exact ⟨z, (radialDiskExtension_eq_closed hz).trans he⟩
    · have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by linarith [not_le.mp hw])
      have hws : w / (‖w‖ : ℂ) ∈ m '' sphere (0 : ℂ) 1 := by
        rw [hs]
        exact mem_sphere_zero_iff_norm.mpr (norm_div_norm_eq_one hw0)
      obtain ⟨ζ, hζ, he⟩ := hws
      have hζn : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
      have hn : ‖(‖w‖ : ℂ) * ζ‖ = ‖w‖ := by
        rw [norm_mul, Complex.norm_of_nonneg (norm_nonneg _), hζn, mul_one]
      refine ⟨(‖w‖ : ℂ) * ζ, ?_⟩
      rw [radialDiskExtension, if_neg (by rwa [hn]), hn]
      have hnr : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw0
      rw [mul_div_cancel_left₀ _ hnr, he, mul_div_cancel₀ _ hnr]

theorem radialDiskExtension_proper {m : ℂ → ℂ}
    (hm : ∀ z : ℂ, ‖z‖ = 1 → ‖m z‖ = 1) :
    Tendsto (radialDiskExtension m) (cocompact ℂ) (cocompact ℂ) := by
  apply Filter.tendsto_cocompact_cocompact_of_norm
  intro ε
  refine ⟨max 1 ε, fun z hz => ?_⟩
  rw [radialDiskExtension_norm_exterior hm (lt_of_le_of_lt (le_max_left _ _) hz)]
  exact lt_of_le_of_lt (le_max_right _ _) hz

theorem radialDiskExtension_homeomorph {m : ℂ → ℂ}
    (hm : ContinuousOn m (closedBall (0 : ℂ) 1))
    (hi : InjOn m (closedBall (0 : ℂ) 1))
    (hc : m '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1)
    (hs : m '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = radialDiskExtension m := by
  have hcircle : ∀ z : ℂ, ‖z‖ = 1 → ‖m z‖ = 1 := by
    intro z hz
    exact mem_sphere_zero_iff_norm.mp (hs ▸ mem_image_of_mem m (mem_sphere_zero_iff_norm.mpr hz))
  have hp : IsProperMap (radialDiskExtension m) := isProperMap_iff_tendsto_cocompact.mpr
    ⟨radialDiskExtension_continuous hm, radialDiskExtension_proper hcircle⟩
  exact ⟨(Equiv.ofBijective _ (radialDiskExtension_bijective hi hc hs)).toHomeomorphOfContinuousClosed
    hp.continuous hp.isClosedMap, rfl⟩

theorem radialDiskExtension_contDiffOn_exterior {m : ℂ → ℂ}
    (hm : ContDiffOn ℝ 1 m (sphere (0 : ℂ) 1)) :
    ContDiffOn ℝ 1 (radialDiskExtension m) unitDiscExterior := by
  have hn : ContDiffOn ℝ 1 (fun z : ℂ => (‖z‖ : ℂ)) unitDiscExterior := by
    intro z hz
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by have : 1 < ‖z‖ := hz; linarith)
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_norm ℝ hz0)).contDiffWithinAt
  have hd : ContDiffOn ℝ 1 (fun z : ℂ => z / (‖z‖ : ℂ)) unitDiscExterior := by
    simpa only [div_eq_mul_inv, Pi.inv_apply, Pi.mul_apply, id_eq] using
      (contDiffOn_id : ContDiffOn ℝ 1 (id : ℂ → ℂ) unitDiscExterior).mul
        (hn.inv (fun z hz => by
          exact_mod_cast (show ‖z‖ ≠ 0 by have : 1 < ‖z‖ := hz; linarith)))
  have hmap : MapsTo (fun z : ℂ => z / (‖z‖ : ℂ)) unitDiscExterior (sphere (0 : ℂ) 1) := by
    intro z hz
    exact mem_sphere_zero_iff_norm.mpr (norm_div_norm_eq_one
      (norm_ne_zero_iff.mp (by have : 1 < ‖z‖ := hz; linarith)))
  apply (hn.mul (hm.comp hd hmap)).congr
  intro z hz
  exact if_neg (not_le.mpr (show 1 < ‖z‖ from hz))

theorem radialMobiusExtension_contDiffOn_exterior {a b c d : ℂ}
    (hden : ∀ z ∈ sphere (0 : ℂ) 1, c * z + d ≠ 0) :
    ContDiffOn ℝ 1 (radialDiskExtension (mobiusFn a b c d)) unitDiscExterior := by
  apply radialDiskExtension_contDiffOn_exterior
  have hm : ContDiffOn ℂ 1 (mobiusFn a b c d) (sphere (0 : ℂ) 1) := by
    unfold mobiusFn
    exact ((contDiffOn_const.mul contDiffOn_id).add contDiffOn_const).div
      ((contDiffOn_const.mul contDiffOn_id).add contDiffOn_const) hden
  exact hm.restrict_scalars ℝ

end TakhtajanTeo
