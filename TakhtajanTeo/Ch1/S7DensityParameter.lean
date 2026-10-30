import TakhtajanTeo.Ch1.S7First

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual pulled-back hyperbolic density has zero real Frechet derivative.
Real differentiability is supplied by the genuine two-parameter kernel family. -/
theorem s7dp_density_hasFDerivAt {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    HasFDerivAt (fun ε => rhoVar ν ε z) (0 : ℂ →L[ℝ] ℂ) 0 := by
  have he : (fun ε => rhoVar ν ε z) =
      (fun ε => (-4:ℂ)*kernelKbar (fun u => ε*ν u) z z) :=
    funext fun ε => eq_6_1 ν ε z
  have hd : DifferentiableAt ℝ (fun ε => rhoVar ν ε z) 0 := by
    rw [he]
    exact (s71_K_diffAt hν hz hz).const_mul (-4)
  have hdz := lemma_6_1 hν hz
  have hreal : (fun ε => conj (rhoVar ν ε z)) = (fun ε => rhoVar ν ε z) :=
    funext fun ε => s71_rho_real ν ε z
  have hdb : dzbar (fun ε => rhoVar ν ε z) 0 = 0 := by
    have ht := dzbar_conj hd
    rw [hreal,hdz,map_zero] at ht
    exact ht
  have hf : fderiv ℝ (fun ε => rhoVar ν ε z) 0 = 0 := by
    ext w
    rw [fderiv_eq_dz_dzbar hd,hdz,hdb]
    simp
  simpa only [hf] using hd.hasFDerivAt

theorem s7dp_ratio_zero (ν : ℂ → ℂ) {z : ℂ} (hz : z ∈ upperHalf) :
    rhoVar ν 0 z/(rhoU z:ℂ) = 1 := by
  rw [(rhoVar_pullback ν 0 hz).2]
  apply div_self
  apply Complex.ofReal_ne_zero.mpr
  have hp : 0 < z.im := hz
  unfold rhoU
  positivity

theorem s7dp_ratio_hasFDerivAt {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    HasFDerivAt (fun ε => rhoVar ν ε z/(rhoU z:ℂ)) (0 : ℂ →L[ℝ] ℂ) 0 := by
  simpa [div_eq_mul_inv] using (s7dp_density_hasFDerivAt hν hz).mul_const (rhoU z:ℂ)⁻¹

/-- The actual normalized density has a pointwise little-o remainder. This
does not assert a spatially uniform bound or interchange any integral. -/
theorem s7dp_ratio_remainder {ν ψ : ℂ → ℂ} (hν : IsHarmonicU ν ψ)
    {z : ℂ} (hz : z ∈ upperHalf) :
    (fun ε => rhoVar ν ε z/(rhoU z:ℂ)-1) =o[𝓝 (0:ℂ)] (fun ε => ε) := by
  simpa only [s7dp_ratio_zero ν hz,zero_apply,sub_zero]
    using (s7dp_ratio_hasFDerivAt hν hz).isLittleO

end TakhtajanTeo
