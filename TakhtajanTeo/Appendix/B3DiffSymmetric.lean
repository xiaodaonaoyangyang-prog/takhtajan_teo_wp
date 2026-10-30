import TakhtajanTeo.Appendix.B_PeriodMapping

/-!
# Smooth circle diffeomorphisms are symmetric (Program G, 下属6)

Second conjunct of Remark B.3 (TT:6046): `Möb(S¹)\Diff₊(S¹) ⊆ S`. For a lift `u` with `u' > 0` continuous, the mean
value theorem writes the Gardiner–Sullivan ratio as `u'(ξ₁)/u'(ξ₂)` with `|ξ₁ - ξ₂| < 2t`; uniform continuity and a
positive lower bound of `u'` on a compact window, after a `2π`-shift, give the uniform limit `1`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

namespace AppB

/-- A lift with `u(t + 2π) = u(t) + 2π` satisfies `u(t + 2πk) = u(t) + 2πk`. -/
theorem b3d_lift_int {u : ℝ → ℝ} (hp : ∀ t, u (t + 2 * π) = u t + 2 * π) (k : ℤ) (t : ℝ) :
    u (t + k * (2 * π)) = u t + k * (2 * π) := by
  have hg : Function.Periodic (fun t => u t - t) (2 * π) := by
    intro t
    show u (t + 2 * π) - (t + 2 * π) = u t - t
    rw [hp]
    ring
  have h : u (t + k * (2 * π)) - (t + k * (2 * π)) = u t - t := (hg.int_mul k) t
  linarith

/-- A smooth sense-preserving circle diffeomorphism is symmetric. -/
theorem b3d_diff_symmetric {h : ℂ → ℂ} (hh : IsCircleDiffeo h) : IsSymmetricHomeo h := by
  obtain ⟨u, hu, hpos, hp, he⟩ := hh
  have hd : Differentiable ℝ u := hu.differentiable (by simp)
  have hdc : Continuous (deriv u) := hu.continuous_deriv (by simp)
  refine ⟨u, hd.continuous, strictMono_of_deriv_pos hpos, hp, he, ?_⟩
  intro ε hε
  have hπ := Real.pi_pos
  set s : Set ℝ := Icc (-(2 * π)) (4 * π) with hs
  have hsc : IsCompact s := isCompact_Icc
  obtain ⟨x0, -, hmin⟩ := hsc.exists_isMinOn (nonempty_Icc.mpr (by linarith)) hdc.continuousOn
  have hm : 0 < deriv u x0 := hpos x0
  obtain ⟨δ', hδ', hδ'u⟩ := Metric.uniformContinuousOn_iff.mp
    (hsc.uniformContinuousOn_of_continuous hdc.continuousOn) (ε * deriv u x0) (by positivity)
  refine ⟨min (δ' / 2) π, by positivity, fun x t ht0 htδ => ?_⟩
  have htπ : t < π := htδ.trans_le (min_le_right _ _)
  have htδ' : 2 * t < δ' := by
    have := htδ.trans_le (min_le_left _ _)
    linarith
  -- shift `x` into `[0, 2π)`
  set k : ℤ := ⌊x / (2 * π)⌋ with hk
  set x' : ℝ := x - k * (2 * π) with hx'
  have hk1 : (k : ℝ) ≤ x / (2 * π) := Int.floor_le _
  have hk2 : x / (2 * π) < k + 1 := Int.lt_floor_add_one _
  have h2π : 0 < 2 * π := by positivity
  rw [le_div_iff₀ h2π] at hk1
  rw [div_lt_iff₀ h2π] at hk2
  have hx'0 : 0 ≤ x' := by rw [hx']; linarith
  have hx'1 : x' < 2 * π := by rw [hx']; nlinarith
  have hshift (r : ℝ) : u (x + r) = u (x' + r) + k * (2 * π) := by
    have := b3d_lift_int hp k (x' + r)
    rw [show x' + r + k * (2 * π) = x + r by rw [hx']; ring] at this
    exact this
  have hratio : (u (x + t) - u x) / (u x - u (x - t)) = (u (x' + t) - u x') / (u x' - u (x' - t)) := by
    have h1 := hshift t
    have h2 := hshift 0
    have h3 := hshift (-t)
    rw [add_zero] at h2
    rw [add_zero] at h2
    rw [show x - t = x + -t by ring, show x' - t = x' + -t by ring, h1, h2, h3]
    congr 1 <;> ring
  rw [hratio]
  -- the mean value theorem on both sides
  obtain ⟨c₁, hc₁, hc₁e⟩ := exists_deriv_eq_slope u (show x' < x' + t by linarith) hd.continuous.continuousOn
    hd.differentiableOn
  obtain ⟨c₂, hc₂, hc₂e⟩ := exists_deriv_eq_slope u (show x' - t < x' by linarith) hd.continuous.continuousOn
    hd.differentiableOn
  have ht' : (x' + t) - x' = t := by ring
  have ht'' : x' - (x' - t) = t := by ring
  rw [ht'] at hc₁e
  rw [ht''] at hc₂e
  have hnum : u (x' + t) - u x' = t * deriv u c₁ := by rw [hc₁e]; field_simp
  have hden : u x' - u (x' - t) = t * deriv u c₂ := by rw [hc₂e]; field_simp
  have hp₂ := hpos c₂
  rw [hnum, hden, mul_div_mul_left _ _ ht0.ne', div_sub_one hp₂.ne', abs_div, abs_of_pos hp₂,
    div_lt_iff₀ hp₂]
  have hc₁s : c₁ ∈ s := ⟨by linarith [hc₁.1], by linarith [hc₁.2]⟩
  have hc₂s : c₂ ∈ s := ⟨by linarith [hc₂.1], by linarith [hc₂.2]⟩
  have hdist : dist c₁ c₂ < δ' := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hc₁.1, hc₁.2, hc₂.1, hc₂.2]
  have hlt := hδ'u c₁ hc₁s c₂ hc₂s hdist
  rw [Real.dist_eq] at hlt
  have hle : deriv u x0 ≤ deriv u c₂ := (isMinOn_iff.mp hmin) c₂ hc₂s
  calc |deriv u c₁ - deriv u c₂| < ε * deriv u x0 := hlt
    _ ≤ ε * deriv u c₂ := mul_le_mul_of_nonneg_left hle hε.le

/-- Remark B.3, second conjunct: `Möb(S¹)\Diff₊(S¹) ⊆ S`. -/
theorem b3d_diffT_subset : diffT ⊆ symmetricT := fun _ hp => b3d_diff_symmetric hp

end AppB

end TakhtajanTeo
