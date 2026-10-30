import TakhtajanTeo.Ch1.S2_HilbertManifold
import TakhtajanTeo.Ch1.HilbertChosenReflection
import TakhtajanTeo.Ch1.ComponentRelativeSchwarzian

/-! Boundary smallness in actual welding coordinates and a reflected boundary filter.
These estimates do not assert an injective nonlinear collar or a global lift. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate
noncomputable section

namespace TakhtajanTeo
open LiZhongQC

def crb_diskBoundary : Filter ℂ :=
  comap (fun w : ℂ => ‖w‖) (𝓝 1) ⊓ 𝓟 unitDisc

def crb_reflectionBoundary (μ : LinfStar) (h : ℂ → ℂ) : Filter ℂ :=
  comap (fun u => Function.invFunOn (fsans μ) unitDisc (h u)) crb_diskBoundary ⊓
    𝓟 (gsans μ '' unitDiscExterior)

-- L1
theorem crb_weighted_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {P q : ℂ → ℂ}
    (heq : ∀ w ∈ unitDisc, q (fsans μ w) * deriv (fsans μ) w ^ 2 = P w)
    {w : ℂ} (hw : w ∈ unitDisc) :
    ‖q (fsans μ w)‖ / poincareDensity (fsans μ '' unitDisc) (fsans μ w) ^ 2 =
      ((1 - ‖w‖ ^ 2) ^ 2 * ‖P w‖) / 4 := by
  rw [eq22_density_formula (S2C.s2c_conf_f hμ) hw, ← heq w hw]
  simp only [norm_mul, norm_pow, div_pow, div_div_eq_mul_div]
  ring

-- L2
theorem crb_weighted_tendsto_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {P q : ℂ → ℂ} (hP : P ∈ A2fun unitDisc)
    (heq : ∀ w ∈ unitDisc, q (fsans μ w) * deriv (fsans μ) w ^ 2 = P w) :
    Tendsto (fun w => ‖q (fsans μ w)‖ /
      poincareDensity (fsans μ '' unitDisc) (fsans μ w) ^ 2)
      crb_diskBoundary (𝓝 0) := by
  have ht := (A2fun.disk_weighted_tendsto_zero hP).div_const 4
  simp only [zero_div] at ht
  apply ht.congr'
  have hw : ∀ᶠ w in crb_diskBoundary, w ∈ unitDisc :=
    (eventually_principal.mpr (fun w hw => hw)).filter_mono inf_le_right
  filter_upwards [hw] with w hw
  exact (crb_weighted_eq hμ heq hw).symm

-- L3
theorem crb_reflected_weighted_tendsto_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {P q h : ℂ → ℂ} (hP : P ∈ A2fun unitDisc)
    (heq : ∀ w ∈ unitDisc, q (fsans μ w) * deriv (fsans μ) w ^ 2 = P w)
    (hmap : MapsTo h (gsans μ '' unitDiscExterior) (fsans μ '' unitDisc)) :
    Tendsto (fun u => ‖q (h u)‖ / poincareDensity (fsans μ '' unitDisc) (h u) ^ 2)
      (crb_reflectionBoundary μ h) (𝓝 0) := by
  have hT : Tendsto (fun u => Function.invFunOn (fsans μ) unitDisc (h u))
      (crb_reflectionBoundary μ h) crb_diskBoundary :=
    tendsto_comap.mono_left inf_le_left
  have ht := (crb_weighted_tendsto_zero hμ hP heq).comp hT
  apply ht.congr'
  have hu : ∀ᶠ u in crb_reflectionBoundary μ h, u ∈ gsans μ '' unitDiscExterior :=
    (eventually_principal.mpr (fun u hu => hu)).filter_mono inf_le_right
  filter_upwards [hu] with u hu
  have hi : fsans μ (Function.invFunOn (fsans μ) unitDisc (h u)) = h u := by
    obtain ⟨w, hw, hwf⟩ := hmap hu
    rw [← hwf, (S2C.s2c_conf_f hμ).2.1.leftInvOn_invFunOn hw]
  dsimp only [Function.comp_def]
  rw [hi]

-- L4
theorem crb_reflection_error_tendsto_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {P q h : ℂ → ℂ} (hP : P ∈ A2fun unitDisc)
    (heq : ∀ w ∈ unitDisc, q (fsans μ w) * deriv (fsans μ) w ^ 2 = P w)
    (hmap : MapsTo h (gsans μ '' unitDiscExterior) (fsans μ '' unitDisc))
    {C : ℝ} (_hC : 0 ≤ C)
    (hgeom : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 *
      ‖fderiv ℝ h u‖ * poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C) :
    Tendsto (fun u => ‖q (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖)
      (crb_reflectionBoundary μ h) (𝓝 0) := by
  have ht := (crb_reflected_weighted_tendsto_zero hμ hP heq hmap).const_mul C
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun u => by positivity) _ ht
  have hu : ∀ᶠ u in crb_reflectionBoundary μ h, u ∈ gsans μ '' unitDiscExterior :=
    (eventually_principal.mpr (fun u hu => hu)).filter_mono inf_le_right
  filter_upwards [hu] with u hu
  have hf := S2C.s2c_conf_f hμ
  have hpos := sq_pos_of_pos (s20l_a2_density_pos (hf.isOpen isOpen_ball)
    (hf.symm isOpen_ball) (hmap hu))
  rw [← mul_div_assoc, le_div_iff₀ hpos]
  calc
    ‖q (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
        poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 =
      ‖q (h u)‖ * (‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
        poincareDensity (fsans μ '' unitDisc) (h u) ^ 2) := by ring
    _ ≤ ‖q (h u)‖ * C := mul_le_mul_of_nonneg_left (hgeom u hu) (norm_nonneg _)
    _ = C * ‖q (h u)‖ := mul_comm _ _

-- L5
theorem crb_denominator_eventually {μ : LinfStar} {q h : ℂ → ℂ}
    (ht : Tendsto (fun u => ‖q (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖)
      (crb_reflectionBoundary μ h) (𝓝 0))
    {k : ℝ} (hk : 0 < k) (hk1 : k < 1) :
    ∀ᶠ u in crb_reflectionBoundary μ h,
      ‖q (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ < 2 * k ∧
      ‖(u - h u) ^ 2 * (q (h u) / 2) * dz h u‖ < k ∧
      1 - k ≤ ‖1 + (u - h u) ^ 2 * (q (h u) / 2) * dz h u‖ ∧
      1 + (u - h u) ^ 2 * (q (h u) / 2) * dz h u ≠ 0 := by
  have he := ht (gt_mem_nhds (show (0 : ℝ) < 2 * k by positivity))
  filter_upwards [he] with u hu
  change ‖q (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ < 2 * k at hu
  have hd : ‖dz h u‖ ≤ ‖fderiv ℝ h u‖ :=
    (le_add_of_nonneg_right (norm_nonneg (dzbar h u))).trans
      (t203_norm_dz_add_dzbar_le (g := h) (z := u))
  have hb : ‖(u - h u) ^ 2 * (q (h u) / 2) * dz h u‖ ≤
      (‖q (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖) / 2 := by
    simp only [norm_mul, norm_pow, norm_div, Complex.norm_two]
    calc
      ‖u - h u‖ ^ 2 * (‖q (h u)‖ / 2) * ‖dz h u‖ ≤
        ‖u - h u‖ ^ 2 * (‖q (h u)‖ / 2) * ‖fderiv ℝ h u‖ := by gcongr
      _ = _ := by ring
  have hb' : ‖(u - h u) ^ 2 * (q (h u) / 2) * dz h u‖ < k := by linarith
  have hn := norm_sub_norm_le (1 : ℂ) (-((u - h u) ^ 2 * (q (h u) / 2) * dz h u))
  simp only [norm_one, norm_neg, sub_neg_eq_add] at hn
  have hlow : 1 - k ≤ ‖1 + (u - h u) ^ 2 * (q (h u) / 2) * dz h u‖ := by linarith
  refine ⟨hu, hb', hlow, ?_⟩
  exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by linarith : 0 < 1 - k) hlow))

-- L6
theorem crb_chosen_reflection {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {P q : ℂ → ℂ} (hP : P ∈ A2fun unitDisc)
    (heq : ∀ w ∈ unitDisc, q (fsans μ w) * deriv (fsans μ) w ^ 2 = P w) :
    ∃ h : ℂ → ℂ,
      IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h ∧
      ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior) ∧
      Tendsto (fun u => ‖q (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖)
        (crb_reflectionBoundary μ h) (𝓝 0) ∧
      ∀ k : ℝ, 0 < k → k < 1 → ∀ᶠ u in crb_reflectionBoundary μ h,
        ‖q (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ < 2 * k ∧
        ‖(u - h u) ^ 2 * (q (h u) / 2) * dz h u‖ < k ∧
        1 - k ≤ ‖1 + (u - h u) ^ 2 * (q (h u) / 2) * dz h u‖ ∧
        1 + (u - h u) ^ 2 * (q (h u) / 2) * dz h u ≠ 0 := by
  obtain ⟨h, K, p, C, hC, hp, hC1, hplanar, hh, hinfty, hgeom, hbar⟩ :=
    hc6_chosen_reflection hμ
  have ht := crb_reflection_error_tendsto_zero hμ hP heq hh.2.1 hC hgeom
  exact ⟨h, hh, hC1, ht, fun k hk hk1 => crb_denominator_eventually ht hk hk1⟩

-- L7: the actual nonlinear conformal transition, via its proved chain rule.
theorem crb_schwarzian_tendsto_zero {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc) :
    Tendsto (fun w => ‖schwarzianHol (crs_transition μ ν) (fsans μ w)‖ /
      poincareDensity (fsans μ '' unitDisc) (fsans μ w) ^ 2)
      crb_diskBoundary (𝓝 0) :=
  crb_weighted_tendsto_zero hμ hP (fun _ hw => crs_schwarzian_pullback hμ hν hw)

-- L8
theorem crb_schwarzian_chosen_reflection {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc) :
    ∃ h : ℂ → ℂ,
      IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h ∧
      ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior) ∧
      Tendsto (fun u => ‖schwarzianHol (crs_transition μ ν) (h u)‖ *
        ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖) (crb_reflectionBoundary μ h) (𝓝 0) ∧
      ∀ k : ℝ, 0 < k → k < 1 → ∀ᶠ u in crb_reflectionBoundary μ h,
        ‖schwarzianHol (crs_transition μ ν) (h u)‖ * ‖u - h u‖ ^ 2 *
          ‖fderiv ℝ h u‖ < 2 * k ∧
        ‖(u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) * dz h u‖ < k ∧
        1 - k ≤ ‖1 + (u - h u) ^ 2 *
          (schwarzianHol (crs_transition μ ν) (h u) / 2) * dz h u‖ ∧
        1 + (u - h u) ^ 2 * (schwarzianHol (crs_transition μ ν) (h u) / 2) * dz h u ≠ 0 :=
  crb_chosen_reflection hμ hP (fun _ hw => crs_schwarzian_pullback hμ hν hw)

end TakhtajanTeo
