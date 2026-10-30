import TakhtajanTeo.Ch1.CuiPieces

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real
noncomputable section
namespace TakhtajanTeo.CUI
open LiZhongQC

theorem cui_compl_ae_interior {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    (hnull : volume (frontier Ω) = 0) :
    ∀ᵐ u ∂volume.restrict Ωᶜ, u ∈ interior Ωᶜ := by
  filter_upwards [ae_restrict_mem hΩ.compl,
    ae_restrict_of_ae (compl_mem_ae_iff.mpr hnull)] with u hu hn
  have hi : u ∈ interior Ω ∪ interior Ωᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact hn
  rcases hi with hi | hi
  · exact (hu (interior_subset hi)).elim
  · exact hi

/-- Tonelli with a weight measurable only on the outer integration set. -/
theorem cui_kernel_tonelli {S T : Set ℂ} {a : ℂ → ℝ≥0∞}
    (ha : AEMeasurable a (volume.restrict S)) :
    (∫⁻ z in T, ∫⁻ u in S, a u * ENNReal.ofReal (1 / ‖u - z‖ ^ 4)) =
      ∫⁻ u in S, a u * ∫⁻ z in T, ENNReal.ofReal (1 / ‖u - z‖ ^ 4) := by
  have hk : Measurable (fun p : ℂ × ℂ => ENNReal.ofReal (1 / ‖p.2 - p.1‖ ^ 4)) := by
    fun_prop
  have hm : AEMeasurable
      (Function.uncurry fun z u : ℂ => a u * ENNReal.ofReal (1 / ‖u - z‖ ^ 4))
      ((volume.restrict T).prod (volume.restrict S)) := ha.comp_snd.mul hk.aemeasurable
  rw [lintegral_lintegral_swap hm]
  apply lintegral_congr
  intro u
  exact lintegral_const_mul _ (by fun_prop)

/-- The C6g kernel step, with exactly its interior-only bound and null frontier.
No measurability or positivity assumption on the real function ρs is needed. -/
theorem cui_kernel_tonelli_bound {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hnull : volume (frontier Ω) = 0) {a : ℂ → ℝ≥0∞}
    (ha : AEMeasurable a (volume.restrict Ωᶜ)) {C0 : ℝ} (hC0 : 0 ≤ C0)
    (ρs : ℂ → ℝ)
    (hI : ∀ u ∈ interior Ωᶜ,
      ∫⁻ z in Ω, ENNReal.ofReal (1 / ‖u - z‖ ^ 4) ≤ ENNReal.ofReal (C0 * ρs u)) :
    (∫⁻ z in Ω, ∫⁻ u in Ωᶜ, a u * ENNReal.ofReal (1 / ‖u - z‖ ^ 4)) ≤
      ENNReal.ofReal C0 * ∫⁻ u in Ωᶜ, a u * ENNReal.ofReal (ρs u) := by
  rw [cui_kernel_tonelli ha]
  calc
    (∫⁻ u in Ωᶜ, a u * ∫⁻ z in Ω, ENNReal.ofReal (1 / ‖u - z‖ ^ 4)) ≤
        ∫⁻ u in Ωᶜ, a u * ENNReal.ofReal (C0 * ρs u) := by
      apply lintegral_mono_ae
      filter_upwards [cui_compl_ae_interior hΩ.measurableSet hnull] with u hu
      exact mul_le_mul' le_rfl (hI u hu)
    _ = ∫⁻ u in Ωᶜ, ENNReal.ofReal C0 * (a u * ENNReal.ofReal (ρs u)) := by
      apply lintegral_congr
      intro u
      rw [ENNReal.ofReal_mul hC0]
      ac_rfl
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem cui_disc_kernel_tonelli {a : ℂ → ℝ≥0∞}
    (ha : AEMeasurable a (volume.restrict unitDiscExterior)) :
    (∫⁻ z in unitDisc, ∫⁻ u in unitDiscExterior,
      a u * ENNReal.ofReal (1 / ‖u - z‖ ^ 4)) =
      ENNReal.ofReal (π / 4) * ∫⁻ u in unitDiscExterior, a u * ENNReal.ofReal (rho u) := by
  rw [cui_kernel_tonelli ha]
  have he : (∫⁻ u in unitDiscExterior,
      a u * ∫⁻ z in unitDisc, ENNReal.ofReal (1 / ‖u - z‖ ^ 4)) =
      ∫⁻ u in unitDiscExterior, ENNReal.ofReal (π / 4) * (a u * ENNReal.ofReal (rho u)) := by
    apply setLIntegral_congr_fun (isOpen_lt continuous_const continuous_norm).measurableSet
    intro u hu
    dsimp only
    rw [cui_bergman hu]
    have hr : π / (‖u‖ ^ 2 - 1) ^ 2 = (π / 4) * rho u := by
      unfold rho
      ring
    rw [hr, ENNReal.ofReal_mul (by positivity)]
    ac_rfl
  rw [he]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end TakhtajanTeo.CUI
