import TakhtajanTeo.Ch2.S1_Cor18
import TakhtajanTeo.Ch2.S1_Remark19
import TakhtajanTeo.Ch2.S1_SymmetricWelding
import TakhtajanTeo.Ch2.S1_SymmetricGroup

/-! # Symmetric boundary maps and Schwarzian decay

Actual boundary implications for Chapter 2, §1. No use of the open
`symmetricT_spec` declaration.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- Weighted Schwarzian decay implies symmetry of the actual Model A boundary map.
This is the collar argument from Corollary 1.8 with its precise weaker input. -/
theorem symt_of_schwarzian_decay {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hS : Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (fB μ) z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)) :
    IsSymmetricHomeo (wA μ) := by
  -- the two-sided asymptotically conformal extension of `w_μ|S¹`
  obtain ⟨r, hr, Ψ, hq, hc, hi, hb, hout, hμΨ⟩ := c18_outer hμ hS
  have hh : ∀ z : ℂ, ‖z‖ = 1 → ‖wA μ z‖ = 1 := by
    intro z hz
    obtain ⟨u, hu, he⟩ := wAS_maps_circle hμ hz
    have ha : wA μ z = u := congrArg finPart he
    rwa [ha]
  obtain ⟨r', hr', Φ, hqΦ, hbΦ, hμΦ⟩ := c18_two_sided hr hh hq hc hi hb hout hμΨ
  apply c18_symmetric_of_chord (wA_circle_sensePreserving hμ)
  intro ε hε
  obtain ⟨ε0, hε0⟩ : ∃ ε0 : ℝ, ε0 = min ε 1 := ⟨_, rfl⟩
  have hε00 : 0 < ε0 := by rw [hε0]; exact lt_min hε one_pos
  have hε01 : ε0 ≤ 1 := by rw [hε0]; exact min_le_right _ _
  have hε0ε : ε0 ≤ ε := by rw [hε0]; exact min_le_left _ _
  -- `K` with `λ(K) ≤ 1 + ε0/3`, the splitting, and the conformal ratio bound
  obtain ⟨K, hK1, hKlam⟩ := c18_lambdaInv_near_one (η := ε0 / 3) (by positivity)
  have hlam : lambdaInv K ≤ 1 + ε0 / 3 := hKlam K hK1.le le_rfl
  obtain ⟨W, H, U, hWK, hWs, hUo, hWU, hHd, hHi, hfac⟩ := c18_split hr' hqΦ hμΦ hK1
  have hWc : Continuous W := continuousOn_univ.mp hWK.2.2.1.1
  have hWi : InjOn W univ := hWK.2.2.1.2.1
  have hCc : IsCompact (W '' sphere (0 : ℂ) 1) := (isCompact_sphere 0 1).image hWc
  obtain ⟨δH, hδH, hHr⟩ := c18_ratio_H hUo hCc hWU hHd hHi (ε := ε0 / 3) (by positivity)
  obtain ⟨δW, hδW, hWuc⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hWc.continuousOn) δH hδH
  have hboth : ∀ z : ℂ, ‖z‖ = 1 → wA μ z = H (W z) := fun z hz => by rw [← hbΦ z hz, hfac z hz]
  -- the ratio estimate for a symmetric pair of points about `b`
  have key : ∀ b p s : ℂ, ‖b‖ = 1 → ‖p‖ = 1 → ‖s‖ = 1 → ‖p - b‖ = ‖s - b‖ → p ≠ b →
      ‖p - b‖ < δW → ‖s - b‖ < δW → ‖wA μ s - wA μ b‖ ≤ (1 + ε) * ‖wA μ p - wA μ b‖ := by
    intro b p s hb1 hp1 hs1 heq hpb hpδ hsδ
    have hsb : s ≠ b := fun h => hpb (norm_sub_eq_zero_iff.mp (by rw [heq, h, sub_self, norm_zero]))
    have hmemC : ∀ z : ℂ, ‖z‖ = 1 → W z ∈ W '' sphere (0 : ℂ) 1 := fun z hz =>
      ⟨z, mem_sphere_zero_iff_norm.mpr hz, rfl⟩
    have hball : ∀ z : ℂ, ‖z‖ = 1 → z ∈ closedBall (0 : ℂ) 1 := fun z hz =>
      mem_closedBall_zero_iff.mpr hz.le
    have hWp : ‖W p - W b‖ < δH := by
      have h := hWuc p (hball p hp1) b (hball b hb1) (by rwa [dist_eq_norm])
      rwa [dist_eq_norm] at h
    have hWs' : ‖W s - W b‖ < δH := by
      have h := hWuc s (hball s hs1) b (hball b hb1) (by rwa [dist_eq_norm])
      rwa [dist_eq_norm] at h
    have hr1 := hHr (W p) (hmemC p hp1) (W b) (hmemC b hb1) (W s) (hmemC s hs1) hWp hWs'
    have hr2 := c18_ratio_W hWK hWs heq hpb
    have hwp : 0 < ‖W p - W b‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hpb (hWi (mem_univ _) (mem_univ _) h)))
    rw [hboth s hs1, hboth b hb1, hboth p hp1]
    have hA := norm_nonneg (H (W p) - H (W b))
    have k1 : ‖H (W s) - H (W b)‖ * ‖W p - W b‖ ≤
        ((1 + ε0 / 3) * lambdaInv K * ‖H (W p) - H (W b)‖) * ‖W p - W b‖ := by
      calc ‖H (W s) - H (W b)‖ * ‖W p - W b‖
          ≤ (1 + ε0 / 3) * ‖H (W p) - H (W b)‖ * ‖W s - W b‖ := hr1
        _ ≤ (1 + ε0 / 3) * ‖H (W p) - H (W b)‖ * (lambdaInv K * ‖W p - W b‖) :=
            mul_le_mul_of_nonneg_left hr2 (by positivity)
        _ = ((1 + ε0 / 3) * lambdaInv K * ‖H (W p) - H (W b)‖) * ‖W p - W b‖ := by ring
    have k2 := le_of_mul_le_mul_right k1 hwp
    have k3 : (1 + ε0 / 3) * lambdaInv K ≤ 1 + ε := by
      have h1 : (1 + ε0 / 3) * lambdaInv K ≤ (1 + ε0 / 3) * (1 + ε0 / 3) :=
        mul_le_mul_of_nonneg_left hlam (by positivity)
      nlinarith
    calc ‖H (W s) - H (W b)‖ ≤ (1 + ε0 / 3) * lambdaInv K * ‖H (W p) - H (W b)‖ := k2
      _ ≤ (1 + ε) * ‖H (W p) - H (W b)‖ := mul_le_mul_of_nonneg_right k3 hA
  -- chords of `S¹`
  have hnorm1 : ∀ y : ℝ, ‖exp ((y : ℂ) * I)‖ = 1 := fun y => norm_exp_ofReal_mul_I y
  have hdiff : ∀ y s : ℝ, exp (((y : ℂ) + (s : ℂ)) * I) - exp ((y : ℂ) * I) =
      exp ((y : ℂ) * I) * (exp (I * (s : ℂ)) - 1) := by
    intro y s
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    ring
  have hchn : ∀ y s : ℝ, ‖exp (((y : ℂ) + (s : ℂ)) * I) - exp ((y : ℂ) * I)‖ = ‖exp (I * (s : ℂ)) - 1‖ := by
    intro y s
    rw [hdiff, norm_mul, hnorm1, one_mul]
  have hpt : ∀ y s : ℝ, ‖exp (((y : ℂ) + (s : ℂ)) * I)‖ = 1 := by
    intro y s
    rw [show ((y : ℂ) + (s : ℂ)) = ((y + s : ℝ) : ℂ) by push_cast; ring]
    exact hnorm1 _
  refine ⟨min δW π, lt_min hδW Real.pi_pos, fun x t ht htδ => ?_⟩
  have htW : t < δW := lt_of_lt_of_le htδ (min_le_left _ _)
  have htπ : t < π := lt_of_lt_of_le htδ (min_le_right _ _)
  have hm : ((x : ℂ) - (t : ℂ)) = (x : ℂ) + ((-t : ℝ) : ℂ) := by push_cast; ring
  rw [hm]
  have hsym : ‖exp (I * (t : ℂ)) - 1‖ = ‖exp (I * ((-t : ℝ) : ℂ)) - 1‖ := by
    rw [norm_exp_I_mul_ofReal_sub_one, norm_exp_I_mul_ofReal_sub_one, neg_div, Real.sin_neg, mul_neg,
      norm_neg]
  have hpos : 0 < ‖exp (I * (t : ℂ)) - 1‖ := by
    rw [norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      Real.norm_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
    exact mul_pos two_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  have hlt : ∀ s : ℝ, |s| = t → ‖exp (I * (s : ℂ)) - 1‖ < δW := by
    intro s hs
    refine lt_of_le_of_lt Real.norm_exp_I_mul_ofReal_sub_one_le ?_
    rw [Real.norm_eq_abs, hs]
    exact htW
  have hlt1 := hlt t (abs_of_pos ht)
  have hlt2 := hlt (-t) (by rw [abs_neg, abs_of_pos ht])
  have hne : ∀ s : ℝ, 0 < ‖exp (I * (s : ℂ)) - 1‖ →
      exp (((x : ℂ) + (s : ℂ)) * I) ≠ exp ((x : ℂ) * I) := by
    intro s hs h
    rw [← hchn x s, h, sub_self, norm_zero] at hs
    exact lt_irrefl _ hs
  constructor
  · rw [norm_sub_rev (wA μ (exp ((x : ℂ) * I)))]
    exact key _ _ _ (hnorm1 x) (hpt x (-t)) (hpt x t) (by rw [hchn, hchn, hsym])
      (hne (-t) (hsym ▸ hpos)) (by rw [hchn]; exact hlt2) (by rw [hchn]; exact hlt1)
  · rw [norm_sub_rev (wA μ (exp ((x : ℂ) * I)))]
    exact key _ _ _ (hnorm1 x) (hpt x t) (hpt x (-t)) (by rw [hchn, hchn, hsym])
      (hne t hpos) (by rw [hchn]; exact hlt1) (by rw [hchn]; exact hlt2)

/-- The full boundary-decay characterization, on the actual quotient representative. -/
theorem symt_iff_schwarzian_decay (p : T1) :
    p ∈ symmetricT ↔ Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (fB (Quotient.out p : LinfStarBall)) z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) :=
  ⟨symt_schwarzian_decay (Quotient.out p).2, symt_of_schwarzian_decay (Quotient.out p).2⟩

/-- The complete characterization and subgroup assertions of `symmetricT_spec`. -/
theorem symt_symmetricT_spec :
    (∀ p : T1, p ∈ symmetricT ↔ Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (fB (Quotient.out p : LinfStarBall)) z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)) ∧
      (∀ p ∈ symmetricT, ∀ q ∈ symmetricT, mulT p q ∈ symmetricT) ∧ ∀ p ∈ symmetricT, invT p ∈ symmetricT :=
  ⟨symt_iff_schwarzian_decay, fun _ hp _ hq => symt_mulT hp hq, fun _ hp => symt_invT hp⟩

/-- (TT:3646, [GS92]) The univalent functions associated with the elements of `S` are exactly those satisfying
condition (ii) of Theorem 1.6: `[μ] ∈ S` iff `(1 - |z|²)² 𝒮(f^μ)(z) → 0` as `|z| → 1⁻`. Moreover `S` is a subgroup. -/
theorem symmetricT_spec :
    (∀ p : T1, p ∈ symmetricT ↔ Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (fB (Quotient.out p : LinfStarBall)) z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)) ∧
      (∀ p ∈ symmetricT, ∀ q ∈ symmetricT, mulT p q ∈ symmetricT) ∧ ∀ p ∈ symmetricT, invT p ∈ symmetricT :=
  symt_symmetricT_spec

end Ch2
end TakhtajanTeo

