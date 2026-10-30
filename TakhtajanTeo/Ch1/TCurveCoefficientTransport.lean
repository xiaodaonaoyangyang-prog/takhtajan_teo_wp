import TakhtajanTeo.Ch1.TCurveNormalizedTransport
import TakhtajanTeo.Ch1.GeneralWeldingUniqueness

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The displayed coefficient is the actual dilatation of the transported
solution. All inverse evaluations occur on the genuine exterior domain. -/
theorem tcg_lambda_is_dilatation {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    {W : ℂ → ℂ} {KW K : ℝ} (hW : IsKQC W univ KW)
    (hWν : complexDilatation W =ᵐ[volume.restrict unitDiscExterior] (ν : ℂ → ℂ))
    (e : ℂ ≃ₜ ℂ) (he : IsKQC (⇑e) univ K)
    (heE : e '' unitDiscExterior = unitDiscExterior) :
    (tcurveLambda ν e : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior]
      complexDilatation (W ∘ e.symm) := by
  have hes : e '' univ = univ := image_univ.trans e.surjective.range_eq
  have hinv : ∀ z ∈ unitDiscExterior, Function.invFunOn (⇑e) unitDiscExterior z = e.symm z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := heE.symm ▸ hz
    rw [e.injective.injOn.leftInvOn_invFunOn hx, e.symm_apply_apply]
  have hdiff : EqOn (complexDilatation (W ∘ Function.invFunOn (⇑e) unitDiscExterior))
      (complexDilatation (W ∘ e.symm)) unitDiscExterior := by
    intro z hz
    have hg : (W ∘ Function.invFunOn (⇑e) unitDiscExterior) =ᶠ[𝓝 z] (W ∘ e.symm) := by
      filter_upwards [bc_hEo.mem_nhds hz] with y hy
      simp only [Function.comp_apply, hinv y hy]
    obtain ⟨h1, h2⟩ := t203_c1_dz_congr hg
    simp only [complexDilatation, h1, h2]
  filter_upwards [(tmi_lambda_props hν he hes heE).2,
    tmi_dilatation_comp_inv hW he hes heE hWν, ae_restrict_mem bc_hEo.measurableSet]
    with z hLam hd hz
  exact hLam.trans (hd.symm.trans (hdiff hz))

/-- Exact composition law for transport by arbitrary exterior-preserving
plane quasiconformal homeomorphisms. -/
theorem tcg_lambda_comp {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (e₁ e₂ : ℂ ≃ₜ ℂ) {K₁ K₂ : ℝ}
    (he₁ : IsKQC (⇑e₁) univ K₁) (he₂ : IsKQC (⇑e₂) univ K₂)
    (hE₁ : e₁ '' unitDiscExterior = unitDiscExterior)
    (hE₂ : e₂ '' unitDiscExterior = unitDiscExterior) :
    tcurveLambda ν (e₁.trans e₂) = tcurveLambda (tcurveLambda ν e₁) e₂ := by
  obtain ⟨⟨M, hM, W, hWn, hrest⟩, hrest'⟩ := wB_spec hν
  obtain ⟨⟨KW, hKW⟩, hWs, hW0, hW1, hWae⟩ := hWn
  have hWν : complexDilatation W =ᵐ[volume.restrict unitDiscExterior] (ν : ℂ → ℂ) := by
    filter_upwards [ae_restrict_of_ae hWae, ae_restrict_mem bc_hEo.measurableSet]
      with z hz hzE
    rw [hz]
    simp [extB, Set.indicator_of_mem hzE]
  have hs₁ : e₁ '' univ = univ := image_univ.trans e₁.surjective.range_eq
  have hLam1 := (tmi_lambda_props hν he₁ hs₁ hE₁).1
  have hKW₁ : IsKQC (W ∘ e₁.symm) univ (K₁ * KW) :=
    thm7_1_comp (homeomorph_inverse_isKQC e₁ he₁) hKW (subset_univ _)
  have he₁₂ : IsKQC (⇑(e₁.trans e₂)) univ (K₁ * K₂) := by
    change IsKQC ((⇑e₂) ∘ (⇑e₁)) univ (K₁ * K₂)
    exact thm7_1_comp he₁ he₂ (subset_univ _)
  have hE₁₂ : (e₁.trans e₂) '' unitDiscExterior = unitDiscExterior := by
    change ((⇑e₂) ∘ (⇑e₁)) '' unitDiscExterior = unitDiscExterior
    rw [image_comp, hE₁, hE₂]
  have hfirst := tcg_lambda_is_dilatation hν hKW hWν e₁ he₁ hE₁
  have hsecond := tcg_lambda_is_dilatation hLam1 hKW₁ hfirst.symm e₂ he₂ hE₂
  have hboth := tcg_lambda_is_dilatation hν hKW hWν (e₁.trans e₂) he₁₂ hE₁₂
  apply Lp.ext
  exact hboth.trans hsecond.symm

#print axioms tcg_lambda_comp
end TakhtajanTeo
