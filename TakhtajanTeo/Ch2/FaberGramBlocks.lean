import TakhtajanTeo.Ch2.FaberGramPolarization

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

def faberUnitCoefficient (n k : ℕ) : ℂ :=
  if k=n+1 then (Real.sqrt (π*((n : ℝ)+1)) : ℂ)⁻¹ else 0

theorem faber_unit_differential (φ a : ℕ → ℕ → ℂ) {N n : ℕ} (hn : n+1≤N) (w : ℂ) :
    faberFiniteDifferential φ a N (faberUnitCoefficient n) w=
      deriv (fun w => (faberPolynomial φ a (n+1)).eval w⁻¹) w/(Real.sqrt (π*((n : ℝ)+1)) : ℂ) := by
  unfold faberFiniteDifferential
  rw [Finset.sum_eq_single (n+1)]
  · simp [faberUnitCoefficient,div_eq_mul_inv,mul_comm]
  · intro k _ hk
    simp [faberUnitCoefficient,hk]
  · intro hk
    exact (hk (Finset.mem_Icc.mpr ⟨by omega,hn⟩)).elim

theorem faber_unit_coefficient (a : ℕ → ℕ → ℂ) {N n : ℕ} (hn : n+1≤N) (p : ℕ) :
    faberFiniteCoefficient a N (faberUnitCoefficient n) p=
      ((n+1 : ℕ) : ℂ)*(Real.sqrt (π*((n : ℝ)+1)) : ℂ)⁻¹*a (p+1) (n+1) := by
  unfold faberFiniteCoefficient
  rw [Finset.sum_eq_single (n+1)]
  · simp [faberUnitCoefficient]
  · intro k _ hk
    simp [faberUnitCoefficient,hk]
  · intro hk
    exact (hk (Finset.mem_Icc.mpr ⟨by omega,hn⟩)).elim

theorem faber_unit_finite_pairing {N m n : ℕ} (hm : m+1≤N) (hn : n+1≤N) :
    (π : ℂ)*(∑ k∈Finset.Icc 1 N, (k : ℂ)*faberUnitCoefficient m k*conj (faberUnitCoefficient n k))=
      kron m n := by
  rw [Finset.sum_eq_single (m+1)]
  · by_cases he : m=n
    · subst n
      have hs : (Real.sqrt (π*((m : ℝ)+1)) : ℂ)≠0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
      have hsq : (Real.sqrt (π*((m : ℝ)+1)) : ℂ)^2=(π : ℂ)*((m : ℂ)+1) := by
        exact_mod_cast Real.sq_sqrt (by positivity : 0≤π*((m : ℝ)+1))
      rw [show faberUnitCoefficient m (m+1)=(Real.sqrt (π*((m : ℝ)+1)) : ℂ)⁻¹ by
        simp [faberUnitCoefficient],show kron m m=1 by simp [kron]]
      rw [map_inv₀,Complex.conj_ofReal]
      field_simp
      simpa only [Nat.cast_add,Nat.cast_one] using hsq.symm
    · have he' : m+1≠n+1 := by omega
      simp [faberUnitCoefficient,he',kron,he]
  · intro k _ hk
    simp [faberUnitCoefficient,hk]
  · intro hk
    exact (hk (Finset.mem_Icc.mpr ⟨by omega,hm⟩)).elim

theorem faber_unit_sqrt_weight (n p : ℕ) :
    Real.sqrt π*Real.sqrt ((p : ℝ)+1)*((n : ℝ)+1)/Real.sqrt (π*((n : ℝ)+1))=
      Real.sqrt (((n : ℝ)+1)*((p : ℝ)+1)) := by
  have hn : 0<((n : ℝ)+1) := by positivity
  have hsπ : Real.sqrt π≠0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hsn : Real.sqrt ((n : ℝ)+1)≠0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  rw [Real.sqrt_mul Real.pi_pos.le,Real.sqrt_mul hn.le]
  calc
    _ = Real.sqrt ((p : ℝ)+1)*((n : ℝ)+1)/Real.sqrt ((n : ℝ)+1) := by field_simp
    _ = Real.sqrt ((p : ℝ)+1)*Real.sqrt ((n : ℝ)+1) := by
      apply (div_eq_iff hsn).mpr
      rw [mul_assoc,← sq,Real.sq_sqrt hn.le]
    _ = _ := mul_comm _ _

theorem faber_unit_pair_weight (a : ℕ → ℕ → ℂ) {N m n : ℕ}
    (hm : m+1≤N) (hn : n+1≤N) (p : ℕ) :
    (π : ℂ)*(((p+1 : ℕ) : ℂ)*faberFiniteCoefficient a N (faberUnitCoefficient m) p*
      conj (faberFiniteCoefficient a N (faberUnitCoefficient n) p))=
      ((Real.sqrt (((m : ℝ)+1)*((p : ℝ)+1)) : ℂ)*a (p+1) (m+1))*
      conj ((Real.sqrt (((n : ℝ)+1)*((p : ℝ)+1)) : ℂ)*a (p+1) (n+1)) := by
  let σ : ℂ := (Real.sqrt π*Real.sqrt ((p : ℝ)+1) : ℝ)
  have hsq : σ*conj σ=(π : ℂ)*((p+1 : ℕ) : ℂ) := by
    have hr : (Real.sqrt π*Real.sqrt ((p : ℝ)+1))^2=π*((p : ℝ)+1) := by
      rw [mul_pow,Real.sq_sqrt Real.pi_pos.le,Real.sq_sqrt (by positivity : 0≤(p : ℝ)+1)]
    simp only [σ,Complex.conj_ofReal,← sq]
    exact_mod_cast hr
  have he (j : ℕ) (hj : j+1≤N) : σ*faberFiniteCoefficient a N (faberUnitCoefficient j) p=
      (Real.sqrt (((j : ℝ)+1)*((p : ℝ)+1)) : ℂ)*a (p+1) (j+1) := by
    rw [faber_unit_coefficient a hj]
    have hw : σ*((j+1 : ℕ) : ℂ)/(Real.sqrt (π*((j : ℝ)+1)) : ℂ)=
        (Real.sqrt (((j : ℝ)+1)*((p : ℝ)+1)) : ℂ) := by
      dsimp [σ]
      exact_mod_cast faber_unit_sqrt_weight j p
    calc
      _ = (σ*((j+1 : ℕ) : ℂ)/(Real.sqrt (π*((j : ℝ)+1)) : ℂ))*a (p+1) (j+1) := by ring
      _ = _ := by rw [hw]
  calc
    _ = (σ*faberFiniteCoefficient a N (faberUnitCoefficient m) p)*
        conj (σ*faberFiniteCoefficient a N (faberUnitCoefficient n) p) := by
      rw [map_mul]
      calc
        _ = ((π : ℂ)*((p+1 : ℕ) : ℂ))*
            (faberFiniteCoefficient a N (faberUnitCoefficient m) p*
              conj (faberFiniteCoefficient a N (faberUnitCoefficient n) p)) := by ring
        _ = _ := by rw [← hsq]; ring
    _ = _ := by rw [he m hm,he n hn]

/-- Normalized inverse Faber Gram matrix on the complement of a conformal disk image. -/
theorem faber_polynomial_gram_complement {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (hf0 : f 0=0)
    {a φ : ℕ → ℕ → ℂ} {b00 : ℂ} (hsym : ∀ m n, a m n=a n m)
    (hexp : ∀ z∈unitDisc, ∀ w∈unitDisc, z≠w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2*z^p.1*w^p.2) S ∧ (f z-f w)/(z-w)=exp (b00-S))
    (hφ : ∀ l k : ℕ, ∀ r : ℝ, 0<r → r<1 → Real.circleAverage (fun z => f z^l/z^k) 0 r=φ l k)
    (hφ0 : ∀ l k : ℕ, k<l → φ l k=0) (m n : ℕ) :
    (∫ w in (f '' unitDisc)ᶜ,
      (deriv (fun w => (faberPolynomial φ a (m+1)).eval w⁻¹) w/Real.sqrt (π*((m : ℝ)+1)))*
      conj (deriv (fun w => (faberPolynomial φ a (n+1)).eval w⁻¹) w/Real.sqrt (π*((n : ℝ)+1))))=
      kron m n-∑' p : ℕ,
        ((Real.sqrt (((m : ℝ)+1)*((p : ℝ)+1)) : ℂ)*a (m+1) (p+1))*
        conj ((Real.sqrt (((n : ℝ)+1)*((p : ℝ)+1)) : ℂ)*a (n+1) (p+1)) := by
  let N := max (m+1) (n+1)
  have hm : m+1≤N := le_max_left _ _
  have hn : n+1≤N := le_max_right _ _
  have hh := faber_finite_differential_pairing hf hi hf0 hexp hφ hφ0 N
    (faberUnitCoefficient m) (faberUnitCoefficient n)
  simp only [faber_unit_differential φ a hm,faber_unit_differential φ a hn] at hh
  rw [mul_sub,faber_unit_finite_pairing hm hn,← tsum_mul_left] at hh
  rw [hh]
  congr 1
  apply tsum_congr
  intro p
  rw [faber_unit_pair_weight a hm hn p,hsym (p+1) (m+1),hsym (p+1) (n+1)]

/-- The second remaining block identity in the original Corollary 2.16. -/
theorem cor_2_16_block_negative {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ)=0)
    {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q) (m n : ℕ) :
    mulAdj (B2 (grunsky f g)) (B2 (grunsky f g)) m n=
      kron m n-mulAdj (B1 (grunsky f g)) (B1 (grunsky f g)) m n := by
  obtain ⟨φ,hφ,hφ0⟩ := g2_phi_exists h.1 h.2.2.1
  have hspec := grunsky_spec h
  have hG := faber_polynomial_gram_complement h.1 h.2.1 h.2.2.1
    (fun j k => (hspec.2 j k).2) hspec.1.2.2.2.1 hφ hφ0 m n
  have hM := faber_complement_measure h.2.2.2.2.2 hF
  rw [hM] at hG
  rw [← cor_2_16_gram_exterior h hPQ n m]
  rw [hPQ.negative_polynomial_eq h hφ hφ0 m,hPQ.negative_polynomial_eq h hφ hφ0 n]
  simpa only [mulAdj,B1,Nat.cast_add,Nat.cast_one] using hG

end TakhtajanTeo.Ch2
