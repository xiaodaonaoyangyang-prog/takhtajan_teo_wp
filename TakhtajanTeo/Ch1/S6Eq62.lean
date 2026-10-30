import TakhtajanTeo.Ch1.S6_HyperbolicMetricVariation
import TakhtajanTeo.Ch1.WRegFoundation
import TakhtajanTeo.Ch1.Eq124General

/-!
# Chapter 1, §6 — (6.2) (`e62_`, 下属2)

`e62_eq_6_2` is a byte-identical copy of `eq_6_2` (S6; relocated at the round-end batch). Route: `eq_6_1`
(`ρ^{εμ} = -4 K_{εμ}(z, z̄)`) and `e124_eq_1_25` at `u = z`; the principal value at `z̄ ∉ 𝕌` is vacuous
(`e62_pv2_conj`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- `pv2 f z z = pv2 f z z̄` for `z ∈ 𝕌`: for `δ ≤ Im z` the disc around `z̄` misses `𝕌`. -/
theorem e62_pv2_conj (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ upperHalf) : pv2 f z z = pv2 f z (conj z) := by
  have hz' : 0 < z.im := hz
  have hev : (fun δ : ℝ => ∫ v in upperHalf \ (ball z δ ∪ ball z δ), f v) =ᶠ[𝓝[>] (0 : ℝ)]
      fun δ => ∫ v in upperHalf \ (ball z δ ∪ ball (conj z) δ), f v := by
    filter_upwards [Ioo_mem_nhdsGT hz'] with δ hδ
    have hset : upperHalf \ (ball z δ ∪ ball z δ) = upperHalf \ (ball z δ ∪ ball (conj z) δ) := by
      ext v
      simp only [mem_diff, mem_union, or_self]
      constructor
      · rintro ⟨hv, hvz⟩
        refine ⟨hv, ?_⟩
        rintro (h | h)
        · exact hvz h
        · have hv' : 0 < v.im := hv
          have h1 : dist v (conj z) < δ := h
          have h2 : |(v - conj z).im| ≤ ‖v - conj z‖ := Complex.abs_im_le_norm _
          rw [dist_eq_norm] at h1
          have h3 : (v - conj z).im = v.im + z.im := by simp
          rw [h3, abs_of_pos (by linarith)] at h2
          linarith [hδ.2]
      · rintro ⟨hv, hvz⟩
        exact ⟨hv, fun h => hvz (Or.inl h)⟩
    rw [hset]
  show limUnder (𝓝[>] (0 : ℝ)) (fun δ => ∫ v in upperHalf \ (ball z δ ∪ ball z δ), f v) =
    limUnder (𝓝[>] (0 : ℝ)) (fun δ => ∫ v in upperHalf \ (ball z δ ∪ ball (conj z) δ), f v)
  unfold limUnder
  rw [Filter.map_congr hev]

/-- `∂_ε (c g) = c ∂_ε g` for a nonzero constant `c`, without a differentiability hypothesis. -/
theorem e62_dz_const_mul {g : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (ε : ℂ) :
    dz (fun e => c * g e) ε = c * dz g ε := by
  by_cases hg : DifferentiableAt ℝ g ε
  · have h := (hg.hasFDerivAt.const_mul c).fderiv
    show (fderiv ℝ (fun e => c * g e) ε 1 - I * fderiv ℝ (fun e => c * g e) ε I) / 2 =
      c * ((fderiv ℝ g ε 1 - I * fderiv ℝ g ε I) / 2)
    rw [h]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  · have hcg : ¬ DifferentiableAt ℝ (fun e => c * g e) ε := by
      intro h
      apply hg
      have h2 := h.const_mul c⁻¹
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun e => ?_)
      show g e = c⁻¹ * (c * g e)
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    show (fderiv ℝ (fun e => c * g e) ε 1 - I * fderiv ℝ (fun e => c * g e) ε I) / 2 =
      c * ((fderiv ℝ g ε 1 - I * fderiv ℝ g ε I) / 2)
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hcg]
    simp

/-- **(6.2)** (TT:2607). For `μ ∈ Ω^{-1,1}(𝕌)`, small `ε`, `z ∈ 𝕌`, in the principal value sense:
`∂/∂ε ρ^{εμ}(z) = (4/π) ∬_𝕌 μ(u) K_{εμ}(z, u) K_{εμ}(u, z̄) d²u`. -/
theorem e62_eq_6_2 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    {ε : ℂ} (hε : ‖ε‖ * k < 1) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun e => rhoVar μ e z) ε =
      (4 / π) * pv2 (fun u => μ u * kernelK (fun y => ε * μ y) z u * kernelKbar (fun y => ε * μ y) u z) z (conj z) := by
  have hμs := wr_isHarmonicU_contDiffOn hμ
  have hfun : (fun e => rhoVar μ e z) = fun e => (-4 : ℂ) * kernelKbar (fun y => e * μ y) z z :=
    funext fun e => eq_6_1 μ e z
  rw [hfun, e62_dz_const_mul (by norm_num) ε, (e124_eq_1_25 hk hμk hμs hε hz hz).1, e62_pv2_conj _ hz]
  ring

/-- **(6.2)** (TT:2607). For `μ ∈ Ω^{-1,1}(𝕌)`, small `ε`, `z ∈ 𝕌`, in the principal value sense:
`∂/∂ε ρ^{εμ}(z) = (4/π) ∬_𝕌 μ(u) K_{εμ}(z, u) K_{εμ}(u, z̄) d²u`. -/
theorem eq_6_2 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {k : ℝ} (hk : 0 ≤ k) (hμk : IsBeltramiCoeff μ upperHalf k)
    {ε : ℂ} (hε : ‖ε‖ * k < 1) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun e => rhoVar μ e z) ε =
      (4 / π) * pv2 (fun u => μ u * kernelK (fun y => ε * μ y) z u * kernelKbar (fun y => ε * μ y) u z) z (conj z) :=
  e62_eq_6_2 hμ hk hμk hε hz

end TakhtajanTeo
