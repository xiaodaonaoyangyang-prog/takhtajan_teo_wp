import TakhtajanTeo.Ch2.S1_UnivalentFunctions
import References.GardinerLakic2000.Ch16.S04_BeurlingAhlforsExtension

/-! # An actual boundary consequence of the symmetric-homeomorphism hypothesis

This establishes uniform vanishing of the Beltrami coefficient of the
Beurling–Ahlfors extension of the real lift. It does not yet assert compactness
of the period matrix or identify a descended disk welding extension.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

/-- The project's absolute ratio condition implies the two-sided reciprocal
ratio bounds needed by the actual localized Beurling–Ahlfors estimate. -/
theorem b9_lift_BA_vanishing {u : ℝ → ℝ} (hu : StrictMono u) (hc : Continuous u)
    (hr : ∀ ε > 0, ∃ δ > 0, ∀ x t : ℝ, 0 < t → t < δ →
      |(u (x+t) - u x) / (u x - u (x-t)) - 1| < ε) :
    ∀ ε > 0, ∃ η > 0, ∀ z : ℂ, 0 < z.im → z.im < η →
      ‖complexDilatation (beurlingAhlfors u 2) z‖ < ε := by
  intro ε hε
  obtain ⟨δ,hδ,hloc⟩ := GardinerLakic2000.gl16_bal_local ε hε
  have hd : 0 < 1 + δ := by linarith
  obtain ⟨t₀,ht₀,ht⟩ := hr (δ/(1+δ)) (div_pos hδ hd)
  refine ⟨t₀/4, by positivity, ?_⟩
  intro z hz hzη
  apply hloc u hu hc z.re (t₀/2) (by positivity) _ z
    (by simp only [sub_self,abs_zero]; positivity) hz (by linarith)
  intro x t ht0 hleft hright
  have htt : t < t₀ := by linarith
  have hh := abs_lt.mp (ht x t ht0 htt)
  have hsmall : δ/(1+δ) ≤ δ := (div_le_iff₀ hd).mpr (by nlinarith)
  have hid : 1 - δ/(1+δ) = 1/(1+δ) := by field_simp; ring
  change 1/(1+δ) ≤ (u (x+t)-u x)/(u x-u (x-t)) ∧
    (u (x+t)-u x)/(u x-u (x-t)) ≤ 1+δ
  constructor <;> linarith

/-- A symmetric circle homeomorphism has its defining real lift with an
actual Beurling–Ahlfors extension whose Beltrami coefficient vanishes uniformly
as the upper-half-plane height tends to zero. -/
theorem b9_symmetric_lift_BA {h : ℂ → ℂ} (hh : IsSymmetricHomeo h) :
    ∃ u : ℝ → ℝ, Continuous u ∧ StrictMono u ∧ (∀ t, u (t+2*π) = u t+2*π) ∧
      (∀ t : ℝ, h (exp (t*I)) = exp (u t*I)) ∧
      ∀ ε > 0, ∃ η > 0, ∀ z : ℂ, 0 < z.im → z.im < η →
        ‖complexDilatation (beurlingAhlfors u 2) z‖ < ε := by
  obtain ⟨u,hc,hu,hper,hcover,hr⟩ := hh
  exact ⟨u,hc,hu,hper,hcover,b9_lift_BA_vanishing hu hc hr⟩

end AppB
end TakhtajanTeo
