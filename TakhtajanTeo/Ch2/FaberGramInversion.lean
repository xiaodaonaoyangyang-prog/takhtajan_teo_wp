import TakhtajanTeo.Ch2.FaberGramLimit

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

/-- Pairing change of variables on measurable domains, with differentiability at every point. -/
theorem faber_pairing_pullback_measurable {f : ℂ → ℂ} {U : Set ℂ}
    (hU : MeasurableSet U) (hf : ∀ z∈U, DifferentiableAt ℂ f z)
    (hi : InjOn f U) (ψ χ : ℂ → ℂ) :
    (∫ w in f '' U, ψ w*conj (χ w))=
      ∫ z in U, (ψ (f z)*deriv f z)*conj (χ (f z)*deriv f z) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU
    (fun z hz => ((hf z hz).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hi]
  apply setIntegral_congr_fun hU
  intro z _
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg (‖deriv f z‖))]
  have hn : ((‖deriv f z‖^2 : ℝ) : ℂ)=deriv f z*conj (deriv f z) := by
    simp only [Complex.mul_conj,Complex.sq_norm]
  simp only [Complex.real_smul,map_mul,hn]
  ring

/-- Inversion carries the closed complement of the inverted image onto the exterior-image
complement with its origin removed. -/
theorem faber_inversion_complement {g φ : ℂ → ℂ} {b : ℂ}
    (hφ0 : φ 0=0) (hb : b≠0)
    (hg : ∀ s∈unitDisc, s≠0 → g (1/s)=b/φ s) :
    (fun w => b/w) '' (φ '' unitDisc)ᶜ=(g '' unitDiscExterior)ᶜ\{0} := by
  let T : ℂ → ℂ := fun w => b/w
  have hTT (w : ℂ) : T (T w)=w := by dsimp [T]; field_simp
  have hT0 {w : ℂ} (hw : w≠0) : T w≠0 := div_ne_zero hb hw
  have hzero : (0 : ℂ)∈φ '' unitDisc := ⟨0,mem_ball_self one_pos,hφ0⟩
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    have hz0 : z≠0 := fun he => hz (he.symm ▸ hzero)
    refine ⟨?_,hT0 hz0⟩
    rintro ⟨ζ,hζ,he⟩
    have hs := a21_inv_exterior hζ
    have hgζ : g ζ=T (φ ζ⁻¹) := by
      simpa only [one_div,inv_inv,T] using hg ζ⁻¹ hs.1 hs.2
    have he' : φ ζ⁻¹=z := by
      have heT : T (φ ζ⁻¹)=T z := hgζ.symm.trans he
      have hh := congrArg T heT
      simpa only [hTT] using hh
    exact hz ⟨ζ⁻¹,hs.1,he'⟩
  · rintro ⟨hw,hw0⟩
    refine ⟨T w,?_,hTT w⟩
    rintro ⟨s,hs,he⟩
    have hs0 : s≠0 := by
      intro hh
      have hz : T w≠0 := hT0 hw0
      exact hz (by simpa [hh,hφ0] using he.symm)
    have hgs : g s⁻¹=w := by
      have hh := hg s hs hs0
      rw [one_div,he] at hh
      exact hh.trans (hTT w)
    exact hw ⟨s⁻¹,a21_inv_punctured ⟨hs,hs0⟩,hgs⟩

theorem faber_scaled_polynomial_pullback {R P : Polynomial ℂ} {b : ℂ}
    (hb : b≠0) (hP : P=R.comp (Polynomial.C b⁻¹*Polynomial.X)) {w : ℂ} (hw : w≠0) :
    P.derivative.eval (b/w)*deriv (fun z => b/z) w=deriv (fun z => R.eval z⁻¹) w := by
  have he : (fun z => P.eval (b/z))=(fun z => R.eval z⁻¹) := by
    funext z
    rw [hP,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    congr 1
    field_simp
  have hd : DifferentiableAt ℂ (fun z => b/z) w :=
    (differentiableAt_const b).div differentiableAt_id hw
  have hh := deriv_comp w P.differentiableAt hd
  simpa only [Function.comp_def,he,P.deriv] using hh.symm

/-- The inverse Faber pairing for the inverted map is the polynomial pairing on the
complement of the original exterior image. The omitted origin is removed by an a.e. equality. -/
theorem faber_scaled_gram_complement {g φ : ℂ → ℂ} {b : ℂ}
    (hφd : DifferentiableOn ℂ φ unitDisc) (hφi : InjOn φ unitDisc) (hφ0 : φ 0=0)
    (hb : b≠0) (hg : ∀ s∈unitDisc, s≠0 → g (1/s)=b/φ s)
    {R S P Q : Polynomial ℂ}
    (hP : P=R.comp (Polynomial.C b⁻¹*Polynomial.X))
    (hQ : Q=S.comp (Polynomial.C b⁻¹*Polynomial.X)) (c d : ℂ) :
    (∫ w in (g '' unitDiscExterior)ᶜ, (P.derivative.eval w/c)*conj (Q.derivative.eval w/d))=
      ∫ w in (φ '' unitDisc)ᶜ, (deriv (fun z => R.eval z⁻¹) w/c)*
        conj (deriv (fun z => S.eval z⁻¹) w/d) := by
  let T : ℂ → ℂ := fun w => b/w
  have hU : MeasurableSet (φ '' unitDisc)ᶜ :=
    (RMT.differentiableOn_invFunOn_of_injOn (show IsOpen unitDisc from isOpen_ball) hφd hφi).1.measurableSet.compl
  have h0 (w : ℂ) (hw : w∈(φ '' unitDisc)ᶜ) : w≠0 := by
    rintro rfl
    exact hw ⟨0,mem_ball_self one_pos,hφ0⟩
  have hd : ∀ w∈(φ '' unitDisc)ᶜ, DifferentiableAt ℂ T w :=
    fun w hw => (differentiableAt_const b).div differentiableAt_id (h0 w hw)
  have hTT (w : ℂ) : T (T w)=w := by dsimp [T]; field_simp
  have hi : InjOn T (φ '' unitDisc)ᶜ := by
    intro w hw z hz he
    have hh := congrArg T he
    simpa only [hTT] using hh
  have hdel : volume.restrict ((g '' unitDiscExterior)ᶜ\{0})=
      volume.restrict (g '' unitDiscExterior)ᶜ := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (0 : ℂ)] with w hw
    simp [hw]
  have hh := faber_pairing_pullback_measurable hU hd hi
    (fun w => P.derivative.eval w/c) (fun w => Q.derivative.eval w/d)
  change (∫ w in (fun z => b/z) '' (φ '' unitDisc)ᶜ, _)=_ at hh
  rw [faber_inversion_complement hφ0 hb hg,hdel] at hh
  refine hh.trans (setIntegral_congr_fun hU (fun w hw => ?_))
  change (P.derivative.eval (b/w)/c*deriv (fun z => b/z) w)*
    conj (Q.derivative.eval (b/w)/d*deriv (fun z => b/z) w)=_
  have heP := faber_scaled_polynomial_pullback hb hP (h0 w hw)
  have heQ := faber_scaled_polynomial_pullback hb hQ (h0 w hw)
  have he (A D c : ℂ) : A/c*D=(A*D)/c := by ring
  rw [he (P.derivative.eval (b/w)) (deriv (fun z => b/z) w) c,
    he (Q.derivative.eval (b/w)) (deriv (fun z => b/z) w) d,heP,heQ]

end TakhtajanTeo.Ch2
