import TakhtajanTeo.Ch2.FaberGramLimit

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

/-- Complex polarization of an actual weighted energy identity. -/
theorem faber_polarized_energy {U : Set ℂ} {F G : ℂ → ℂ}
    {x y u v : ℕ → ℂ} (s : Finset ℕ)
    (hi : ∀ t : ℂ, IntegrableOn (fun z => ‖F z+t*G z‖^2) U)
    (hs : ∀ t : ℂ, Summable (fun n => ((n+1 : ℕ) : ℝ)*‖x n+t*y n‖^2))
    (he : ∀ t : ℂ, (∫ z in U, ‖F z+t*G z‖^2)=π*
      ((∑ k∈s, (k : ℝ)*‖u k+t*v k‖^2)-∑' n, ((n+1 : ℕ) : ℝ)*‖x n+t*y n‖^2)) :
    (∫ z in U, F z*conj (G z))=(π : ℂ)*
      ((∑ k∈s, (k : ℂ)*u k*conj (v k))-∑' n, ((n+1 : ℕ) : ℂ)*x n*conj (y n)) := by
  let E (t : ℂ) : ℂ := ((∫ z in U, ‖F z+t*G z‖^2 : ℝ) : ℂ)
  let A (t : ℂ) : ℂ := ((∑ k∈s, (k : ℝ)*‖u k+t*v k‖^2 : ℝ) : ℂ)
  let C (t : ℂ) : ℂ := ((∑' n, ((n+1 : ℕ) : ℝ)*‖x n+t*y n‖^2 : ℝ) : ℂ)
  have hE : (∫ z in U, F z*conj (G z))=(E 1-E (-1)+(E I-E (-I))*I)/4 := by
    let Q (t : ℂ) (z : ℂ) : ℂ := ((‖F z+t*G z‖^2 : ℝ) : ℂ)
    have hQ (t : ℂ) : IntegrableOn (Q t) U := (hi t).ofReal
    have hp (z : ℂ) : F z*conj (G z)=(Q 1 z-Q (-1) z+(Q I z-Q (-I) z)*I)/4 := by
      simpa [Q,sub_eq_add_neg] using bergman_polarization (F z) (G z)
    simp_rw [hp]
    rw [integral_div,integral_add ((hQ 1).sub' (hQ (-1)))
      (((hQ I).sub' (hQ (-I))).mul_const I),integral_sub (hQ 1) (hQ (-1)),
      integral_mul_const,integral_sub (hQ I) (hQ (-I))]
    simp only [Q,E,integral_complex_ofReal]
  have hc (t : ℂ) : HasSum (fun n => (((n+1 : ℕ) : ℂ))*((‖x n+t*y n‖^2 : ℝ) : ℂ)) (C t) := by
    simpa only [C,Complex.ofReal_mul,Complex.ofReal_natCast] using
      Complex.hasSum_ofReal.mpr (hs t).hasSum
  have hp := (((hc 1).sub (hc (-1))).add (((hc I).sub (hc (-I))).mul_right I)).div_const 4
  have hp' : HasSum (fun n => ((n+1 : ℕ) : ℂ)*x n*conj (y n))
      ((C 1-C (-1)+(C I-C (-I))*I)/4) := by
    apply hp.congr_fun
    intro n
    have hn := bergman_polarization (x n) (y n)
    simp only [one_mul,neg_mul,one_mul,← sub_eq_add_neg] at hn ⊢
    rw [mul_assoc,hn]
    ring
  have hA : (∑ k∈s, (k : ℂ)*u k*conj (v k))=(A 1-A (-1)+(A I-A (-I))*I)/4 := by
    simp only [A,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast]
    rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,Finset.sum_mul,
      ← Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_assoc,bergman_polarization (u k) (v k)]
    simp only [one_mul,neg_mul,one_mul,← sub_eq_add_neg]
    ring
  have hEC (t : ℂ) : E t=(π : ℂ)*(A t-C t) := by
    dsimp [E,A,C]
    rw [he t]
    push_cast
    rfl
  rw [hE,hA,hp'.tsum_eq,hEC,hEC,hEC,hEC]
  ring

/-- The finite Laurent potential is exactly the corresponding finite Faber combination,
up to its constant term. -/
theorem faber_potential_eval {φ : ℕ → ℕ → ℂ} (a : ℕ → ℕ → ℂ)
    (hφ0 : ∀ l k : ℕ, k<l → φ l k=0) (N : ℕ) (μ : ℕ → ℂ) (w : ℂ) :
    (∑ l∈Finset.Icc 1 N, (∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*φ l k/(l : ℂ))*w^(-(l : ℤ)))=
      ∑ k∈Finset.Icc 1 N, μ k*((faberPolynomial φ a k).eval w⁻¹+(k : ℂ)*a 0 k) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [faberPolynomial_eval_inv,sub_add_cancel,Finset.mul_sum,Finset.mul_sum]
  rw [← Finset.sum_subset (s₁ := Finset.Icc 1 k) (s₂ := Finset.Icc 1 N)
    (fun l hl => by simp at hk hl ⊢; omega) (fun l hl hl' => by
      have hkl : k<l := by simp at hl hl'; omega
      simp [hφ0 l k hkl])]
  apply Finset.sum_congr rfl
  intro l _
  rw [zpow_neg,zpow_natCast]
  ring

theorem faber_potential_deriv {φ : ℕ → ℕ → ℂ} (a : ℕ → ℕ → ℂ)
    (hφ0 : ∀ l k : ℕ, k<l → φ l k=0) (N : ℕ) (μ : ℕ → ℂ) {w : ℂ} (hw : w≠0) :
    deriv (fun w => ∑ l∈Finset.Icc 1 N,
      (∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*φ l k/(l : ℂ))*w^(-(l : ℤ))) w=
      ∑ k∈Finset.Icc 1 N, μ k*deriv (fun w => (faberPolynomial φ a k).eval w⁻¹) w := by
  have he : (fun w => ∑ l∈Finset.Icc 1 N,
      (∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*φ l k/(l : ℂ))*w^(-(l : ℤ)))=
      fun w => ∑ k∈Finset.Icc 1 N, μ k*((faberPolynomial φ a k).eval w⁻¹+(k : ℂ)*a 0 k) :=
    funext (faber_potential_eval a hφ0 N μ)
  rw [he]
  have hd (k : ℕ) : DifferentiableAt ℂ (fun w => (faberPolynomial φ a k).eval w⁻¹) w :=
    (faberPolynomial φ a k).differentiableAt.comp w (differentiableAt_inv hw)
  rw [deriv_fun_sum (fun k _ => ((hd k).add_const _).const_mul _)]
  apply Finset.sum_congr rfl
  intro k _
  rw [deriv_const_mul _ ((hd k).add_const _),deriv_add_const]

def faberFiniteDifferential (φ a : ℕ → ℕ → ℂ) (N : ℕ) (μ : ℕ → ℂ) (w : ℂ) : ℂ :=
  ∑ k∈Finset.Icc 1 N, μ k*deriv (fun w => (faberPolynomial φ a k).eval w⁻¹) w

def faberFiniteCoefficient (a : ℕ → ℕ → ℂ) (N : ℕ) (μ : ℕ → ℂ) (p : ℕ) : ℂ :=
  ∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*a (p+1) k

theorem faberFiniteDifferential_add_smul (φ a : ℕ → ℕ → ℂ) (N : ℕ)
    (μ ν : ℕ → ℂ) (t w : ℂ) :
    faberFiniteDifferential φ a N (fun k => μ k+t*ν k) w=
      faberFiniteDifferential φ a N μ w+t*faberFiniteDifferential φ a N ν w := by
  simp only [faberFiniteDifferential,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem faberFiniteCoefficient_add_smul (a : ℕ → ℕ → ℂ) (N : ℕ)
    (μ ν : ℕ → ℂ) (t : ℂ) (p : ℕ) :
    faberFiniteCoefficient a N (fun k => μ k+t*ν k) p=
      faberFiniteCoefficient a N μ p+t*faberFiniteCoefficient a N ν p := by
  simp only [faberFiniteCoefficient,mul_add,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact energy of the actual finite combination of inverse Faber differentials. -/
theorem faber_finite_differential_energy {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (hf0 : f 0=0)
    {a φ : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z∈unitDisc, ∀ w∈unitDisc, z≠w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2*z^p.1*w^p.2) S ∧ (f z-f w)/(z-w)=exp (b00-S))
    (hφ : ∀ l k : ℕ, ∀ r : ℝ, 0<r → r<1 → Real.circleAverage (fun z => f z^l/z^k) 0 r=φ l k)
    (hφ0 : ∀ l k : ℕ, k<l → φ l k=0) (N : ℕ) (μ : ℕ → ℂ) :
    IntegrableOn (fun w => ‖faberFiniteDifferential φ a N μ w‖^2) (f '' unitDisc)ᶜ ∧
    Summable (fun p => ((p+1 : ℕ) : ℝ)*‖faberFiniteCoefficient a N μ p‖^2) ∧
    (∫ w in (f '' unitDisc)ᶜ, ‖faberFiniteDifferential φ a N μ w‖^2)=
      π*((∑ k∈Finset.Icc 1 N, (k : ℝ)*‖μ k‖^2)-
        ∑' p, ((p+1 : ℕ) : ℝ)*‖faberFiniteCoefficient a N μ p‖^2) := by
  let ν : ℕ → ℂ := fun l => ∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*φ l k/(l : ℂ)
  let H : ℂ → ℂ := fun w => ∑ l∈Finset.Icc 1 N, ν l*w^(-(l : ℤ))
  let p : Polynomial ℂ := ∑ l∈Finset.Icc 1 N, Polynomial.monomial l (ν l)
  have hp : H=(fun w => p.eval w⁻¹) := by
    funext w
    simp only [H,p,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
    apply Finset.sum_congr rfl
    intro l _
    rw [zpow_neg,zpow_natCast,inv_pow]
  have hD : IsOpen unitDisc := isOpen_ball
  have hm : MeasurableSet (f '' unitDisc)ᶜ :=
    (RMT.differentiableOn_invFunOn_of_injOn hD hf hi).1.measurableSet.compl
  have h0 (w : ℂ) (hw : w∈(f '' unitDisc)ᶜ) : w≠0 := by
    rintro rfl
    exact hw ⟨0,mem_ball_self one_pos,hf0⟩
  have he (w : ℂ) (hw : w∈(f '' unitDisc)ᶜ) : deriv H w=faberFiniteDifferential φ a N μ w :=
    faber_potential_deriv a hφ0 N μ (h0 w hw)
  have hInt : IntegrableOn (fun w => ‖deriv H w‖^2) (f '' unitDisc)ᶜ := by
    rw [hp]
    exact (faber_inverse_poly_integrable hf hi hf0 (by norm_num : (0 : ℝ)<1/2)
      (by norm_num : (1/2 : ℝ)<1) p).mono_set
      (compl_subset_compl.mpr (image_mono (closedBall_subset_ball (by norm_num : (1/2 : ℝ)<1))))
  have hEq : (fun w => ‖deriv H w‖^2)=ᵐ[volume.restrict (f '' unitDisc)ᶜ]
      (fun w => ‖faberFiniteDifferential φ a N μ w‖^2) := by
    filter_upwards [ae_restrict_mem hm] with w hw
    rw [he w hw]
  have hE := faber_grunsky_energy_limit hf hi hf0 hexp hφ hφ0 N μ
  exact ⟨hInt.congr hEq,hE.1,(integral_congr_ae hEq).symm.trans hE.2⟩

/-- Polarized finite-support Grunsky energy, with both sides interpreted as actual integrals/sums. -/
theorem faber_finite_differential_pairing {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (hf0 : f 0=0)
    {a φ : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z∈unitDisc, ∀ w∈unitDisc, z≠w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2*z^p.1*w^p.2) S ∧ (f z-f w)/(z-w)=exp (b00-S))
    (hφ : ∀ l k : ℕ, ∀ r : ℝ, 0<r → r<1 → Real.circleAverage (fun z => f z^l/z^k) 0 r=φ l k)
    (hφ0 : ∀ l k : ℕ, k<l → φ l k=0) (N : ℕ) (μ ν : ℕ → ℂ) :
    (∫ w in (f '' unitDisc)ᶜ,
      faberFiniteDifferential φ a N μ w*conj (faberFiniteDifferential φ a N ν w))=
      (π : ℂ)*((∑ k∈Finset.Icc 1 N, (k : ℂ)*μ k*conj (ν k))-
        ∑' p, ((p+1 : ℕ) : ℂ)*faberFiniteCoefficient a N μ p*conj (faberFiniteCoefficient a N ν p)) := by
  apply faber_polarized_energy (Finset.Icc 1 N)
  · intro t
    have hh := (faber_finite_differential_energy hf hi hf0 hexp hφ hφ0 N (fun k => μ k+t*ν k)).1
    simpa only [faberFiniteDifferential_add_smul] using hh
  · intro t
    have hh := (faber_finite_differential_energy hf hi hf0 hexp hφ hφ0 N (fun k => μ k+t*ν k)).2.1
    simpa only [faberFiniteCoefficient_add_smul] using hh
  · intro t
    have hh := (faber_finite_differential_energy hf hi hf0 hexp hφ hφ0 N (fun k => μ k+t*ν k)).2.2
    simpa only [faberFiniteDifferential_add_smul,faberFiniteCoefficient_add_smul] using hh

end TakhtajanTeo.Ch2
