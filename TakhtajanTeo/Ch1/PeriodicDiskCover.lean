import TakhtajanTeo.Ch1.CircleLiftExtension
import Mathlib.Analysis.Complex.CoveringMap

/-! Exponential descent for periodic half-plane extensions. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def diskCover (z : ℂ) : ℂ := exp (2 * π * I * z)
def diskCoverLog (w : ℂ) : ℂ := log w / (2 * π * I)
def periodicDiskMap (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  if w = 0 then 0 else diskCover (f (diskCoverLog w))

theorem diskCoverCoeff_ne_zero : (2 * π * I : ℂ) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero

theorem diskCover_ne_zero (z : ℂ) : diskCover z ≠ 0 := exp_ne_zero _

theorem diskCover_norm (z : ℂ) : ‖diskCover z‖ = Real.exp (-2 * π * z.im) := by
  rw [diskCover, norm_exp]
  congr 1
  simp [mul_re, mul_im]
  <;> ring

theorem diskCover_mem (z : ℂ) : diskCover z ∈ unitDisc \ {0} ↔ z ∈ upperHalf := by
  have hπ := Real.pi_pos
  simp only [mem_diff, mem_singleton_iff, diskCover_ne_zero, not_false_eq_true, and_true,
    unitDisc, mem_ball_zero_iff, diskCover_norm, Real.exp_lt_one_iff]
  change -2 * π * z.im < 0 ↔ 0 < z.im
  constructor <;> intro hz
  · nlinarith
  · nlinarith

theorem diskCover_log {w : ℂ} (hw : w ≠ 0) : diskCover (diskCoverLog w) = w := by
  have he : (2 * π * I : ℂ) * (log w / (2 * π * I)) = log w := by
    field_simp [diskCoverCoeff_ne_zero]
  rw [diskCover, diskCoverLog, he, exp_log hw]

theorem diskCover_image : diskCover '' upperHalf = unitDisc \ {0} := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (diskCover_mem z).mpr hz
  · intro w hw
    have hlog := diskCover_log (show w ≠ 0 from hw.2)
    exact ⟨diskCoverLog w, (diskCover_mem _).mp (hlog.symm ▸ hw), hlog⟩

theorem diskCover_eq_iff {z w : ℂ} : diskCover z = diskCover w ↔ ∃ n : ℤ, z = w + n := by
  rw [diskCover, diskCover, exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply mul_left_cancel₀ diskCoverCoeff_ne_zero
    linear_combination hn
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

theorem diskCover_add_int (z : ℂ) (n : ℤ) : diskCover (z + n) = diskCover z :=
  diskCover_eq_iff.mpr ⟨n, rfl⟩

theorem beurlingAhlfors_add_int {u : ℝ → ℝ} (hu : Continuous u)
    (hp : ∀ x, u (x + 1) = u x + 1) (r : ℝ) (z : ℂ) (n : ℤ) :
    beurlingAhlfors u r (z + n) = beurlingAhlfors u r z + n := by
  have hper : Function.Periodic (fun z => beurlingAhlfors u r z - z) (1 : ℂ) := by
    intro z
    dsimp only
    rw [beurlingAhlfors_add_one hu hp]
    ring
  have hn := hper.int_mul n z
  simp only [mul_one] at hn
  linear_combination hn

theorem periodicDiskMap_cover {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, ∀ n : ℤ, f (z + n) = f z + n) (z : ℂ) :
    periodicDiskMap f (diskCover z) = diskCover (f z) := by
  rw [periodicDiskMap, if_neg (diskCover_ne_zero z)]
  obtain ⟨n, hn⟩ := diskCover_eq_iff.mp (diskCover_log (diskCover_ne_zero z))
  rw [hn, hf, diskCover_add_int]

theorem periodicDiskMap_image {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, ∀ n : ℤ, f (z + n) = f z + n)
    (himage : f '' upperHalf = upperHalf) :
    periodicDiskMap f '' (unitDisc \ {0}) = unitDisc \ {0} := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [← diskCover_image] at hv
    obtain ⟨z, hz, rfl⟩ := hv
    rw [periodicDiskMap_cover hf]
    exact (diskCover_mem _).mpr (himage ▸ mem_image_of_mem f hz)
  · intro hw
    rw [← diskCover_image] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    rw [← himage] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨diskCover z, (diskCover_mem _).mpr hz, periodicDiskMap_cover hf z⟩

theorem periodicDiskMap_injOn {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, ∀ n : ℤ, f (z + n) = f z + n)
    (hinj : InjOn f upperHalf) : InjOn (periodicDiskMap f) (unitDisc \ {0}) := by
  intro w hw v hv he
  rw [← diskCover_image] at hw hv
  obtain ⟨z, hz, rfl⟩ := hw
  obtain ⟨t, ht, rfl⟩ := hv
  rw [periodicDiskMap_cover hf, periodicDiskMap_cover hf] at he
  obtain ⟨n, hn⟩ := diskCover_eq_iff.mp he
  have htn : t + (n : ℂ) ∈ upperHalf := by simpa [upperHalf] using ht
  have hzt : z = t + n := hinj hz htn (hn.trans (hf t n).symm)
  exact diskCover_eq_iff.mpr ⟨n, hzt⟩

theorem diskCover_differentiable : Differentiable ℂ diskCover := by
  unfold diskCover
  fun_prop

theorem diskCover_injOn_ball (a : ℂ) : InjOn diskCover (ball a (1 / 3)) := by
  intro z hz w hw he
  obtain ⟨n, hn⟩ := diskCover_eq_iff.mp he
  have hdist : ‖z - w‖ < 1 := by
    have hh := dist_triangle z a w
    rw [dist_comm a w] at hh
    have hz' := mem_ball.mp hz
    have hw' := mem_ball.mp hw
    rw [dist_eq_norm] at hh
    linarith
  have hnNorm : ‖(n : ℂ)‖ < 1 := by
    rw [hn, add_sub_cancel_left] at hdist
    exact hdist
  have hnReal : |(n : ℝ)| < 1 := by simpa using hnNorm
  have hn0 : n = 0 := by
    have hneg : (-1 : ℤ) < n := by exact_mod_cast (abs_lt.mp hnReal).1
    have hpos : n < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hnReal).2
    omega
  simpa [hn0] using hn

end TakhtajanTeo

#print axioms TakhtajanTeo.periodicDiskMap_image
#print axioms TakhtajanTeo.periodicDiskMap_injOn
#print axioms TakhtajanTeo.beurlingAhlfors_add_int
