import TakhtajanTeo.Appendix.BergmanKernelModel
import TakhtajanTeo.Appendix.BergmanChosenCoefficients
import TakhtajanTeo.Ch1.WeldingUniqueness

/-! # The chosen period matrix and its actual Bergman kernel -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

theorem b8_lambda_infty_forces_zero {g : ℂ → ℂ} {c : ℂ}
    (hg : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hc : Tendsto (fun z => lambdaW c (g z)) (cocompact ℂ) (cocompact ℂ)) : c = 0 := by
  by_contra hcn
  have hi : Tendsto (fun z => (g z)⁻¹) (cocompact ℂ) (𝓝 0) := by
    have hh : Tendsto (Inv.inv : ℂ → ℂ) (cocompact ℂ) (𝓝 0) := by
      simpa only [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
    exact hh.comp hg
  have hh : Tendsto (fun z => (c + (g z)⁻¹)⁻¹) (cocompact ℂ) (𝓝 c⁻¹) := by
    simpa using (hi.const_add c).inv₀ (by simpa using hcn)
  have hne : ∀ᶠ z in cocompact ℂ, g z ≠ 0 :=
    hg.eventually (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have he : (fun z => (c + (g z)⁻¹)⁻¹) =ᶠ[cocompact ℂ] (fun z => lambdaW c (g z)) := by
    filter_upwards [hne] with z hz
    dsimp [lambdaW]
    rw [show c + (g z)⁻¹ = (c * g z + 1) / g z by field_simp, inv_div]
  exact (hh.congr' he).not_tendsto (disjoint_nhds_cocompact _) hc

theorem b8_weldConst_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : weldConst μ = 0 := by
  have hid : Function.invFun (id : ExtPlane → ExtPlane) = id :=
    funext (fun z => Function.leftInverse_invFun Function.injective_id z)
  unfold weldConst
  split_ifs with hex
  · have hprime := hex.choose_spec
    have hg := (gMu_isWelding hμ).2.2.2.2.2.2
    apply b8_lambda_infty_forces_zero hg.2.2
    apply hprime.2.2.2.2.2.2.2.congr
    intro z
    apply congrArg (fun w : ℂ => lambdaW hex.choose (gMu μ w))
    rw [alphaMu_eq_id, hid]
    rfl
  · rfl

theorem b8_welding_normalized_pair {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsNormalizedDisjointPair (fsans μ) (gsans μ) := by
  have hid : Function.invFun (id : ExtPlane → ExtPlane) = id :=
    funext (fun z => Function.leftInverse_invFun Function.injective_id z)
  have hf : fsans μ = fB μ := by ext z; simp [fsans, b8_weldConst_zero hμ, lambdaW]
  have hg : gsans μ = gMu μ := by
    ext z
    simp only [gsans, b8_weldConst_zero hμ, alphaMu_eq_id, hid, id_eq,
      lambdaW, zero_mul, zero_add, div_one]
    rfl
  rw [hf, hg]
  refine ⟨(fB_holomorphic_injective hμ).1, (fB_holomorphic_injective hμ).2,
    (fB_normalization μ).1, (fB_normalization μ).2.1,
    (gMu_isWelding hμ).2.2.2.2.2.2, ?_⟩
  apply disjoint_left.mpr
  rintro u ⟨z, hz, rfl⟩ ⟨w, hw, he⟩
  have hext : wB μ (z : ExtPlane) = wB μ (Function.invFun (wAS μ) (w : ExtPlane)) := by
    rw [wB_disc_eq_fB hμ hz, ← gMu_sphere_factorization hμ hw, he]
  have hzext := (wB_bijective μ).1 hext
  have hzw : wAS μ (z : ExtPlane) = (w : ExtPlane) := by
    rw [hzext, Function.rightInverse_invFun (wAS_bijective μ).2]
  obtain ⟨v, hv, hve⟩ := wAS_maps_disc hμ (mem_ball_zero_iff.mp hz)
  have hvw : v = w := OnePoint.coe_injective (hve.symm.trans hzw)
  subst v
  exact (not_lt.mpr (le_of_lt hw)) hv

/-- The actual chosen B1 matrix, not an independently selected coefficient
array, represents the normalized disjoint pair's integral kernel. -/
theorem b8_pair_model {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    let B := B1 (grunsky f g)
    (∀ m n, B m n = B n m) ∧
      (∀ m, Summable (fun n => ‖B m n‖ ^ 2) ∧ (∑' n, ‖B m n‖ ^ 2) ≤ 1) ∧
      B7Contractive B ∧
      ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
        HasSum (fun p : ℕ × ℕ => B p.1 p.2 * basisE p.1 z * basisE p.2 w) (kerK1 f z w) := by
  have hg := grunsky_spec h
  let a : ℕ → ℕ → ℂ := fun m n => grunsky f g (-(m : ℤ)) (-(n : ℤ))
  have hsym : ∀ m n, a m n = a n m := fun m n => (hg.2 m n).2
  have hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (grunsky f g 0 0 - S) := hg.1.2.2.2.1
  let B : ℕ → ℕ → ℂ := fun m n =>
    (Real.sqrt (((m : ℝ)+1)*((n : ℝ)+1)) : ℂ) * a (m+1) (n+1)
  have hBeq : B = B1 (grunsky f g) := by
    ext m n
    simp [B, B1, a, Nat.cast_add, Nat.cast_one]
  change (∀ m n, B1 (grunsky f g) m n = B1 (grunsky f g) n m) ∧ _
  rw [← hBeq]
  have hB := g2c_grunsky_matrix_contraction h.1 h.2.1 hsym hexp
  refine ⟨?_, hB.1, (fun x hx => (hB.2 x hx).2), ?_⟩
  · intro m n
    simp only [B, hsym (m+1) (n+1), mul_comm ((m : ℝ)+1)]
  · intro z hz w hw hzw
    have hs := (b8_kernel_series_of_exp h.1 h.2.1 hexp hz hw hzw).div_const (π : ℂ)
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [show ((π : ℂ) * kerK1 f z w) / (π : ℂ) = kerK1 f z w by field_simp] at hs
    exact hs.congr_fun (fun p => g2c_basis_weight a p.1 p.2 z w)

end AppB
end TakhtajanTeo
