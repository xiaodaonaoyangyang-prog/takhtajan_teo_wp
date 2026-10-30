import TakhtajanTeo.Ch1.ComponentRelativeAmbient

open Complex Set Metric Filter Topology
noncomputable section
namespace TakhtajanTeo

/-- A plane homeomorphism cannot agree on an unbounded set with a fractional
linear map having a finite value at infinity. No QC limit-existence premise
is hidden here: this is a consequence to apply after constructing that limit. -/
theorem cml_denominator_zero (H : ℂ ≃ₜ ℂ) {D : Set ℂ}
    (hD : ¬ Bornology.IsBounded D) {a b c d : ℂ}
    (he : ∀ z ∈ D, H z = (a * z + b) / (c * z + d)) : c = 0 := by
  by_contra hc
  have hex : ∀ n : ℕ, ∃ z ∈ D, (n : ℝ) < ‖z‖ := by
    intro n
    by_contra hn
    push_neg at hn
    exact hD (isBounded_iff_forall_norm_le.mpr ⟨(n : ℝ), hn⟩)
  choose z hz hn using hex
  have hzn : ∀ n, z n ≠ 0 := by
    intro n
    exact norm_ne_zero_iff.mp (lt_of_le_of_lt (Nat.cast_nonneg n) (hn n)).ne'
  have hnorm : Tendsto (fun n => ‖z n‖) atTop atTop :=
    tendsto_atTop_mono (fun n => (hn n).le) tendsto_natCast_atTop_atTop
  have hzc : Tendsto z atTop (Bornology.cobounded ℂ) := tendsto_norm_atTop_iff_cobounded.mp hnorm
  have hzc' : Tendsto z atTop (cocompact ℂ) := by
    rwa [Metric.cobounded_eq_cocompact] at hzc
  have hH : Tendsto (H : ℂ → ℂ) (cocompact ℂ) (cocompact ℂ) :=
    show map H (cocompact ℂ) ≤ cocompact ℂ from le_of_eq H.map_cocompact
  have hHnorm : Tendsto (fun n => ‖H (z n)‖) atTop atTop :=
    tendsto_norm_cocompact_atTop.comp (hH.comp hzc')
  have hinv := Filter.tendsto_inv₀_cobounded.comp hzc
  have hnum : Tendsto (fun n => a + b / z n) atTop (𝓝 a) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add (hinv.const_mul b)
  have hden : Tendsto (fun n => c + d / z n) atTop (𝓝 c) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add (hinv.const_mul d)
  have hlim : Tendsto (fun n => H (z n)) atTop (𝓝 (a / c)) := by
    apply (hnum.div hden hc).congr'
    apply Eventually.of_forall
    intro n
    change (a + b / z n) / (c + d / z n) = H (z n)
    rw [he _ (hz n)]
    calc (a + b / z n) / (c + d / z n) =
        ((a * z n + b) / z n) / ((c * z n + d) / z n) := by
          congr 1 <;> rw [add_div, mul_div_cancel_right₀ _ (hzn n)]
      _ = _ := div_div_div_cancel_right₀ (hzn n) _ _
  exact not_tendsto_nhds_of_tendsto_atTop hHnorm _ hlim.norm

/-- The nondegenerate Möbius restriction of such a limit is genuinely affine. -/
theorem cml_affine_restriction (H : ℂ ≃ₜ ℂ) {D : Set ℂ}
    (hD : ¬ Bornology.IsBounded D) {a b c d : ℂ} (hdet : a*d-b*c ≠ 0)
    (he : ∀ z ∈ D, H z = (a*z+b)/(c*z+d)) :
    c = 0 ∧ d ≠ 0 ∧ a / d ≠ 0 ∧ ∀ z ∈ D, H z = (a/d)*z + b/d := by
  have hc := cml_denominator_zero H hD he
  subst c
  have had : a*d ≠ 0 := by simpa using hdet
  have hd := (mul_ne_zero_iff.mp had).2
  refine ⟨rfl, hd, div_ne_zero (mul_ne_zero_iff.mp had).1 hd, ?_⟩
  intro z hz
  rw [he z hz]
  simp only [zero_mul, zero_add, add_div]
  ring

end TakhtajanTeo
