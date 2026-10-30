import TakhtajanTeo.Ch1.S5ExteriorChartRegularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! A parameterized analytic inverse from the existing Banach inverse function theorem. -/
open Complex Set Metric Filter Topology
open scoped Classical
noncomputable section
namespace TakhtajanTeo

-- L1
theorem s5cf_vertical_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : E × ℂ → ℂ} {p : E} {t : ℂ} (hH : DifferentiableAt ℂ H (p, t)) :
    deriv (fun w => H (p, w)) t = fderiv ℂ H (p, t) (0, 1) := by
  have h := hH.hasFDerivAt.comp t (hasFDerivAt_prodMk_right (𝕜 := ℂ) p t)
  convert! h.hasDerivAt.deriv using 1

-- L2
theorem s5cf_triangular_bijective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : (E × ℂ) →L[ℂ] ℂ) (hd : L (0, 1) ≠ 0) :
    Function.Bijective ((ContinuousLinearMap.fst ℂ E ℂ).prod L) := by
  have hsplit : ∀ (v : E) (c : ℂ), L (v, c) = L (v, 0) + c * L (0, 1) := by
    intro v c
    rw [show (v, c) = (v, 0) + c • ((0 : E), (1 : ℂ)) by ext <;> simp,
      map_add, map_smul, smul_eq_mul]
  constructor
  · intro x y he
    change (x.1, L x) = (y.1, L y) at he
    have h1 := congrArg (fun a : E × ℂ => a.1) he
    have h2 := congrArg (fun a : E × ℂ => a.2) he
    change x.1 = y.1 at h1
    change L (x.1, x.2) = L (y.1, y.2) at h2
    rw [hsplit x.1 x.2, hsplit y.1 y.2, h1] at h2
    exact Prod.ext h1 (mul_right_cancel₀ hd (add_left_cancel h2))
  · rintro ⟨v, w⟩
    refine ⟨(v, (w - L (v, 0)) / L (0, 1)), ?_⟩
    change (v, L (v, (w - L (v, 0)) / L (0, 1))) = (v, w)
    apply Prod.ext
    · rfl
    · change L (v, (w - L (v, 0)) / L (0, 1)) = w
      rw [hsplit, div_mul_cancel₀ _ hd]
      ring

-- L3
theorem s5cf_analytic_implicit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {H : E × ℂ → ℂ} {p : E} {t : ℂ} (ha : AnalyticAt ℂ H (p, t))
    (hd : deriv (fun w => H (p, w)) t ≠ 0) :
    ∃ G : E × ℂ → ℂ, AnalyticAt ℂ G (p, H (p, t)) ∧ G (p, H (p, t)) = t ∧
      (∀ᶠ q in 𝓝 (p, H (p, t)), H (q.1, G q) = q.2) ∧
      (∀ᶠ q in 𝓝 (p, t), G (q.1, H q) = q.2) := by
  let L := fderiv ℂ H (p, t)
  let T : (E × ℂ) →L[ℂ] (E × ℂ) := (ContinuousLinearMap.fst ℂ E ℂ).prod L
  have hdL : L (0, 1) ≠ 0 := by
    rw [← s5cf_vertical_fderiv ha.differentiableAt]
    exact hd
  have hT : Function.Bijective T := s5cf_triangular_bijective L hdL
  let e : (E × ℂ) ≃L[ℂ] (E × ℂ) := ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr hT.1) (LinearMap.range_eq_top.mpr hT.2)
  have he : (e : (E × ℂ) →L[ℂ] (E × ℂ)) = T := ContinuousLinearEquiv.coe_ofBijective _ _ _
  let F : E × ℂ → E × ℂ := fun q => (q.1, H q)
  have hF : HasStrictFDerivAt F T (p, t) := hasStrictFDerivAt_fst.prodMk ha.hasStrictFDerivAt
  have hFe : HasStrictFDerivAt F (e : (E × ℂ) →L[ℂ] (E × ℂ)) (p, t) := by rw [he]; exact hF
  let R := hFe.toOpenPartialHomeomorph F
  have hx : (p, t) ∈ R.source := hFe.mem_toOpenPartialHomeomorph_source
  have hFa : AnalyticAt ℂ F (p, t) := analyticAt_fst.prod ha
  have hInv : AnalyticAt ℂ (R.symm : E × ℂ → E × ℂ) (F (p, t)) :=
    R.analyticAt_symm' hx hFa hFe.hasFDerivAt.fderiv
  refine ⟨fun q => (R.symm q).2, analyticAt_snd.comp_of_eq hInv rfl, ?_, ?_, ?_⟩
  · change (R.symm (R (p, t))).2 = t
    exact congrArg Prod.snd (R.left_inv hx)
  · filter_upwards [R.open_target.mem_nhds (R.map_source hx)] with q hq
    have hqeq := R.right_inv hq
    change ((R.symm q).1, H (R.symm q)) = q at hqeq
    have h1 := congrArg (fun a : E × ℂ => a.1) hqeq
    have h2 := congrArg (fun a : E × ℂ => a.2) hqeq
    change (R.symm q).1 = q.1 at h1
    change H ((R.symm q).1, (R.symm q).2) = q.2 at h2
    rw [h1] at h2
    exact h2
  · filter_upwards [R.open_source.mem_nhds hx] with q hq
    change (R.symm (R q)).2 = q.2
    exact congrArg Prod.snd (R.left_inv hq)

end TakhtajanTeo

