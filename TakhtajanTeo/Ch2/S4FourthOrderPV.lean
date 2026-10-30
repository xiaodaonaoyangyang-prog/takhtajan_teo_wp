import TakhtajanTeo.Ch2.S4HolomorphicChart
import TakhtajanTeo.Ch2.S4PrincipalValue
import TakhtajanTeo.Ch1.L112

/-! # True fourth-order principal values for smooth local coefficients (`s4p4_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- P1
theorem s4p4_taylor1 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℂ → F} {z : ℂ} {ρ L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ x ∈ ball z ρ, DifferentiableAt ℝ f x)
    (hl : ∀ x ∈ ball z ρ, ‖fderiv ℝ f x - fderiv ℝ f z‖ ≤ L * ‖x - z‖)
    {h : ℂ} (hh : ‖h‖ < ρ) :
    ‖f (z + h) - f z - fderiv ℝ f z h‖ ≤ L * ‖h‖ ^ 2 := by
  set D := fderiv ℝ f z with hD
  set g : ℂ → F := fun x => f x - (D x - D z) with hgdef
  have hmem : ∀ x ∈ closedBall z ‖h‖, x ∈ ball z ρ := fun x hx =>
    mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) hh)
  have hg : ∀ x ∈ closedBall z ‖h‖, HasFDerivWithinAt g (fderiv ℝ f x - D) (closedBall z ‖h‖) x := by
    intro x hx
    exact ((hd x (hmem x hx)).hasFDerivAt.sub (D.hasFDerivAt.sub_const (D z))).hasFDerivWithinAt
  have hb : ∀ x ∈ closedBall z ‖h‖, ‖fderiv ℝ f x - D‖ ≤ L * ‖h‖ := by
    intro x hx
    calc ‖fderiv ℝ f x - D‖ ≤ L * ‖x - z‖ := hl x (hmem x hx)
      _ ≤ L * ‖h‖ := by
        apply mul_le_mul_of_nonneg_left _ hL
        rw [← dist_eq_norm]
        exact mem_closedBall.1 hx
  have hz : z ∈ closedBall z ‖h‖ := mem_closedBall_self (norm_nonneg h)
  have hzh : z + h ∈ closedBall z ‖h‖ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have hmv := (convex_closedBall z ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hg hb hz hzh
  have he : g (z + h) - g z = f (z + h) - f z - D h := by
    simp only [hgdef, map_add, sub_self]
    abel
  rw [he, add_sub_cancel_left] at hmv
  calc ‖f (z + h) - f z - D h‖ ≤ L * ‖h‖ * ‖h‖ := hmv
    _ = L * ‖h‖ ^ 2 := by ring

-- P2
theorem s4p4_taylor2 {f : ℂ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (z : ℂ) :
    ∃ ρ > 0, ∃ L : ℝ, 0 ≤ L ∧ ∀ h : ℂ, ‖h‖ < ρ →
      ‖f (z + h) - f z - fderiv ℝ f z h -
        (1 / 2 : ℝ) • (fderiv ℝ (fderiv ℝ f) z h h)‖ ≤ L * ‖h‖ ^ 3 := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hD1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) := hf.fderiv_right htop
  have hD2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (fderiv ℝ f)) := hD1.fderiv_right htop
  have h1top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have h2top : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  obtain ⟨K, t, ht, hK⟩ := ((hD2.contDiffAt (x := z)).of_le h1top).exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hρt⟩ := Metric.mem_nhds_iff.1 ht
  have hsym : IsSymmSndFDerivAt ℝ f z := ((hf.contDiffAt (x := z)).of_le h2top).isSymmSndFDerivAt (by simp)
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hD1d : Differentiable ℝ (fderiv ℝ f) := hD1.differentiable (by simp)
  set B := fderiv ℝ (fderiv ℝ f) z with hB
  set D := fderiv ℝ f z with hD
  refine ⟨ρ, hρ, K, K.2, fun h hh => ?_⟩
  -- the first-order remainder of `Df`
  have hA : ∀ x ∈ ball z ρ, ‖fderiv ℝ f x - D - B (x - z)‖ ≤ K * ‖x - z‖ ^ 2 := by
    intro x hx
    have hxz : ‖x - z‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.1 hx
    have h1 := s4p4_taylor1 (f := fderiv ℝ f) (z := z) (ρ := ρ) (L := K) K.2
      (fun y _ => hD1d.differentiableAt)
      (fun y hy => by
        have h2 := hK.dist_le_mul y (hρt hy) z (hρt (mem_ball_self hρ))
        rwa [dist_eq_norm, dist_eq_norm] at h2) hxz
    rwa [add_sub_cancel] at h1
  set g : ℂ → ℂ := fun x => f x - (D x - D z) - (1 / 2 : ℝ) • B (x - z) (x - z) with hgdef
  have hg : ∀ x, HasFDerivAt g (fderiv ℝ f x - D - B (x - z)) x := by
    intro x
    have hs : HasFDerivAt (fun y : ℂ => y - z) (ContinuousLinearMap.id ℝ ℂ) x := (hasFDerivAt_id x).sub_const z
    have hq := B.hasFDerivAt_of_bilinear hs hs
    have h3 : HasFDerivAt g _ x :=
      ((hfd x).hasFDerivAt.sub (D.hasFDerivAt.sub_const (D z))).sub (hq.const_smul (1 / 2 : ℝ))
    refine h3.congr_fderiv ?_
    ext1 v
    have hv := hsym v (x - z)
    rw [← hB] at hv
    show fderiv ℝ f x v - D v - (1 / 2 : ℝ) • (B (x - z) v + B v (x - z)) = fderiv ℝ f x v - D v - B (x - z) v
    rw [hv]
    module
  have hmem : ∀ x ∈ closedBall z ‖h‖, x ∈ ball z ρ := fun x hx =>
    mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) hh)
  have hb : ∀ x ∈ closedBall z ‖h‖, ‖fderiv ℝ f x - D - B (x - z)‖ ≤ K * ‖h‖ ^ 2 := by
    intro x hx
    calc ‖fderiv ℝ f x - D - B (x - z)‖ ≤ K * ‖x - z‖ ^ 2 := hA x (hmem x hx)
      _ ≤ K * ‖h‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ K.2
        have : ‖x - z‖ ≤ ‖h‖ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hz : z ∈ closedBall z ‖h‖ := mem_closedBall_self (norm_nonneg h)
  have hzh : z + h ∈ closedBall z ‖h‖ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have hmv := (convex_closedBall z ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hg x).hasFDerivWithinAt) hb hz hzh
  have he : g (z + h) - g z = f (z + h) - f z - D h - (1 / 2 : ℝ) • B h h := by
    simp only [hgdef, map_add, sub_self, add_sub_cancel_left, map_zero, smul_zero]
    abel
  rw [he, add_sub_cancel_left] at hmv
  calc _ ≤ K * ‖h‖ ^ 2 * ‖h‖ := hmv
    _ = K * ‖h‖ ^ 3 := by ring

-- P3
theorem s4p4_bilinear_polynomial (D : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ)) :
    ∃ a b c : ℂ, ∀ h : ℂ, D h h = a * h ^ 2 + b * h * conj h + c * conj h ^ 2 := by
  refine ⟨(D 1 1 - D I I) / 4 - I * (D 1 I + D I 1) / 4, (D 1 1 + D I I) / 2,
    (D 1 1 - D I I) / 4 + I * (D 1 I + D I 1) / 4, fun h => ?_⟩
  set x := h.re
  set y := h.im
  have h1 : h = x • (1 : ℂ) + y • I := by
    apply Complex.ext <;> simp [x, y]
  have h2 : conj h = (x : ℂ) - y * I := by
    apply Complex.ext <;> simp [x, y]
  have h3 : h = (x : ℂ) + y * I := by
    apply Complex.ext <;> simp [x, y]
  have hL : D h h = x • (x • D 1 1 + y • D I 1) + y • (x • D 1 I + y • D I I) := by
    conv_lhs => rw [h1]
    simp only [map_add, map_smul, add_apply, FunLike.coe_smul, Pi.smul_apply]
  rw [hL, h2]
  conv_rhs => rw [h3]
  simp only [Complex.real_smul]
  ring_nf
  rw [I_sq]
  ring

end Ch2
end TakhtajanTeo
