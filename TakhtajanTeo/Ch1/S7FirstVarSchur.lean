import TakhtajanTeo.Ch1.QuasidiskKernel

/-!
# Program G, F1 piece R2: Schur test for `|X - Y|⁻⁴` between disjoint open sets (下属1)

`s7g_schur`: `∬_{Ω × Ω'} f g/|X - Y|⁴ ≤ π (∫_Ω f²/d_Ω²)^{1/2} (∫_{Ω'} g²/d_{Ω'}²)^{1/2}`, `d = infDist · ᶜ`.
Cauchy–Schwarz on `Ω × Ω'` with `f g/|X - Y|⁴ = (f/|X - Y|²)(g/|X - Y|²)`, then
`∫_{Ω'} |X - Y|⁻⁴ dY ≤ π/d_Ω(X)²` (`r24_lintegral_outside`, since `Ω' ⊆ Ωᶜ`), and symmetrically.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- One side of the Schur test: `∬_{Ω × Ω'} f(X)²/|X - Y|⁴ ≤ π ∫_Ω f²/d_Ω²` for `Ω' ⊆ Ωᶜ` nonempty. -/
theorem s7g_r2_side {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) (hsub : Ω' ⊆ Ωᶜ) (hne : Ω'.Nonempty) (f : ℂ → ℝ≥0∞) :
    (∫⁻ X in Ω, ∫⁻ Y in Ω', f X ^ 2 / ‖X - Y‖ₑ ^ 4) ≤
      ENNReal.ofReal π * ∫⁻ X in Ω, f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2 := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hΩ.measurableSet fun X hX => ?_
  have hcl : IsClosed Ωᶜ := hΩ.isClosed_compl
  have ha : 0 < infDist X Ωᶜ :=
    (hcl.notMem_iff_infDist_pos (hne.mono hsub)).1 (fun h => h hX)
  have hR : ∀ Y ∈ Ω', infDist X Ωᶜ ≤ ‖Y - X‖ := by
    intro Y hY
    rw [← dist_eq_norm, dist_comm]
    exact infDist_le_dist_of_mem (hsub hY)
  have hpt : ∀ Y, f X ^ 2 / ‖X - Y‖ₑ ^ 4 = f X ^ 2 * (‖Y - X‖₊ : ℝ≥0∞)⁻¹ ^ 4 := by
    intro Y
    rw [div_eq_mul_inv, ← ENNReal.inv_pow, enorm_sub_rev, enorm_eq_nnnorm]
  simp_rw [hpt]
  have hm : Measurable fun Y : ℂ => (‖Y - X‖₊ : ℝ≥0∞)⁻¹ ^ 4 := by fun_prop
  rw [lintegral_const_mul _ hm]
  calc f X ^ 2 * ∫⁻ Y in Ω', (‖Y - X‖₊ : ℝ≥0∞)⁻¹ ^ 4
      ≤ f X ^ 2 * ENNReal.ofReal (π / infDist X Ωᶜ ^ 2) := by
        gcongr
        exact r24_lintegral_outside ha hR
    _ = ENNReal.ofReal π * (f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow ha.le, div_eq_mul_inv,
          div_eq_mul_inv]
        ring

/-- **R2** (stub `s7g_schur`). -/
theorem s7g_schur : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ Ω Ω' : Set ℂ, IsOpen Ω → IsOpen Ω' → Disjoint Ω Ω' →
    ∀ f g : ℂ → ℝ≥0∞, Measurable f → Measurable g →
      (∫⁻ X in Ω, ∫⁻ Y in Ω', f X * g Y / ‖X - Y‖ₑ ^ 4) ≤
        C * (∫⁻ X in Ω, f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2) ^ (1 / 2 : ℝ) *
          (∫⁻ Y in Ω', g Y ^ 2 / ENNReal.ofReal (infDist Y Ω'ᶜ) ^ 2) ^ (1 / 2 : ℝ) := by
  refine ⟨ENNReal.ofReal π, ENNReal.ofReal_lt_top, ?_⟩
  intro Ω Ω' hΩ hΩ' hdisj f g hf hg
  rcases Ω'.eq_empty_or_nonempty with h' | hne'
  · simp [h']
  rcases Ω.eq_empty_or_nonempty with h | hne
  · simp [h]
  have hsub' : Ω' ⊆ Ωᶜ := fun Y hY hYΩ => disjoint_left.1 hdisj hYΩ hY
  have hsub : Ω ⊆ Ω'ᶜ := fun X hX hXΩ' => disjoint_left.1 hdisj hX hXΩ'
  set μP : Measure (ℂ × ℂ) := (volume.restrict Ω).prod (volume.restrict Ω') with hμP
  set F1 : ℂ × ℂ → ℝ≥0∞ := fun p => f p.1 / ‖p.1 - p.2‖ₑ ^ 2 with hF1
  set F2 : ℂ × ℂ → ℝ≥0∞ := fun p => g p.2 / ‖p.1 - p.2‖ₑ ^ 2 with hF2
  have hR : Measurable fun p : ℂ × ℂ => ‖p.1 - p.2‖ₑ := by fun_prop
  have hF1m : Measurable F1 := (hf.comp measurable_fst).div (hR.pow_const 2)
  have hF2m : Measurable F2 := (hg.comp measurable_snd).div (hR.pow_const 2)
  have hprod : ∀ p : ℂ × ℂ, f p.1 * g p.2 / ‖p.1 - p.2‖ₑ ^ 4 = (F1 * F2) p := by
    intro p
    simp only [hF1, hF2, Pi.mul_apply, div_eq_mul_inv]
    rw [show ‖p.1 - p.2‖ₑ ^ 4 = ‖p.1 - p.2‖ₑ ^ 2 * ‖p.1 - p.2‖ₑ ^ 2 by ring,
      ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top enorm_ne_top)) (Or.inl (ENNReal.pow_ne_top enorm_ne_top))]
    ring
  have hlhs : (∫⁻ X in Ω, ∫⁻ Y in Ω', f X * g Y / ‖X - Y‖ₑ ^ 4) = ∫⁻ p, (F1 * F2) p ∂μP := by
    rw [hμP, lintegral_prod _ (hF1m.mul hF2m).aemeasurable]
    simp_rw [← hprod]
  have hsq1 : (∫⁻ p, F1 p ^ (2 : ℝ) ∂μP) ≤
      ENNReal.ofReal π * ∫⁻ X in Ω, f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2 := by
    have he : ∀ p : ℂ × ℂ, F1 p ^ (2 : ℝ) = f p.1 ^ 2 / ‖p.1 - p.2‖ₑ ^ 4 := by
      intro p
      rw [ENNReal.rpow_two, hF1]
      simp only [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← pow_mul]
    simp_rw [he]
    have hm1 : AEMeasurable (fun p : ℂ × ℂ => f p.1 ^ 2 / ‖p.1 - p.2‖ₑ ^ 4) μP :=
      (((hf.comp measurable_fst).pow_const 2).div (hR.pow_const 4)).aemeasurable
    rw [lintegral_prod (fun p : ℂ × ℂ => f p.1 ^ 2 / ‖p.1 - p.2‖ₑ ^ 4) hm1]
    exact s7g_r2_side hΩ hsub' hne' f
  have hsq2 : (∫⁻ p, F2 p ^ (2 : ℝ) ∂μP) ≤
      ENNReal.ofReal π * ∫⁻ Y in Ω', g Y ^ 2 / ENNReal.ofReal (infDist Y Ω'ᶜ) ^ 2 := by
    have he : ∀ p : ℂ × ℂ, F2 p ^ (2 : ℝ) = g p.2 ^ 2 / ‖p.2 - p.1‖ₑ ^ 4 := by
      intro p
      rw [ENNReal.rpow_two, hF2, enorm_sub_rev]
      simp only [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← pow_mul]
    simp_rw [he]
    have hm2 : AEMeasurable (fun p : ℂ × ℂ => g p.2 ^ 2 / ‖p.2 - p.1‖ₑ ^ 4) μP :=
      (((hg.comp measurable_snd).pow_const 2).div
        ((show Measurable fun p : ℂ × ℂ => ‖p.2 - p.1‖ₑ by fun_prop).pow_const 4)).aemeasurable
    rw [lintegral_prod_symm (fun p : ℂ × ℂ => g p.2 ^ 2 / ‖p.2 - p.1‖ₑ ^ 4) hm2]
    exact s7g_r2_side hΩ' hsub hne g
  have hπ0 : ENNReal.ofReal π ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.pi_pos
  rw [hlhs]
  calc (∫⁻ p, (F1 * F2) p ∂μP)
      ≤ (∫⁻ p, F1 p ^ (2 : ℝ) ∂μP) ^ (1 / (2 : ℝ)) * (∫⁻ p, F2 p ^ (2 : ℝ) ∂μP) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq μP Real.HolderConjugate.two_two hF1m.aemeasurable hF2m.aemeasurable
    _ ≤ (ENNReal.ofReal π * ∫⁻ X in Ω, f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2) ^ (1 / (2 : ℝ)) *
          (ENNReal.ofReal π * ∫⁻ Y in Ω', g Y ^ 2 / ENNReal.ofReal (infDist Y Ω'ᶜ) ^ 2) ^ (1 / (2 : ℝ)) := by
        gcongr
    _ = ENNReal.ofReal π * (∫⁻ X in Ω, f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2) ^ (1 / 2 : ℝ) *
          (∫⁻ Y in Ω', g Y ^ 2 / ENNReal.ofReal (infDist Y Ω'ᶜ) ^ 2) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        have hpp : ENNReal.ofReal π ^ (1 / (2 : ℝ)) * ENNReal.ofReal π ^ (1 / (2 : ℝ)) = ENNReal.ofReal π := by
          rw [← ENNReal.rpow_add _ _ hπ0 ENNReal.ofReal_ne_top]
          norm_num
        calc _ = (ENNReal.ofReal π ^ (1 / (2 : ℝ)) * ENNReal.ofReal π ^ (1 / (2 : ℝ))) *
              (∫⁻ X in Ω, f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2) ^ (1 / 2 : ℝ) *
                (∫⁻ Y in Ω', g Y ^ 2 / ENNReal.ofReal (infDist Y Ω'ᶜ) ^ 2) ^ (1 / 2 : ℝ) := by ring
          _ = _ := by rw [hpp]

end TakhtajanTeo
