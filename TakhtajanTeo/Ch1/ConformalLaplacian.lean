import TakhtajanTeo.Ch1.S1_4_ResolventCore

/-! Open-domain mixed Wirtinger and weighted Laplace covariance.
This isolates the calculation used in the Cayley model change of §6, so lower
resolvent modules can use it without importing §6. -/

open Complex Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The Laplacian depends only on the function's germ at the evaluation point. -/
theorem laplace0_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    laplace0 f z = laplace0 g z := by
  have hb : dzbar f =ᶠ[𝓝 z] dzbar g := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with w hw
    simp only [dzbar, hw]
  unfold laplace0 dz
  rw [hb.fderiv_eq (𝕜 := ℝ)]

/-- A locally C2 function has a differentiable antiholomorphic Wirtinger derivative. -/
theorem differentiableOn_dzbar_of_contDiffOn {V : Set ℂ} (hV : IsOpen V)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ 2 f V) : DifferentiableOn ℝ (dzbar f) V := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ f) V :=
    hf.fderiv_of_isOpen hV (by norm_num)
  have h1 := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hI := hd.clm_apply (contDiffOn_const (c := I))
  have hb : ContDiffOn ℝ 1 (dzbar f) V :=
    (h1.add (contDiffOn_const.mul hI)).div_const 2
  exact hb.differentiableOn one_ne_zero

/-- Mixed Wirtinger derivatives acquire the squared holomorphic derivative under
a holomorphic change of coordinates between open sets. -/
theorem dz_dzbar_comp_holomorphic {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {φ f : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ U) (hm : MapsTo φ U V)
    (hf : ContDiffOn ℝ 2 f V) {z : ℂ} (hz : z ∈ U) :
    dz (dzbar (f ∘ φ)) z = dz (dzbar f) (φ z) * (‖deriv φ z‖ ^ 2 : ℝ) := by
  have hc := hφ.differentiableAt (hU.mem_nhds hz)
  have hfc : DifferentiableAt ℝ (dzbar f) (φ z) :=
    (differentiableOn_dzbar_of_contDiffOn hV hf).differentiableAt
      (hV.mem_nhds (hm hz))
  have hdc : DifferentiableAt ℂ (deriv φ) z :=
    (hφ.deriv hU).differentiableAt (hU.mem_nhds hz)
  have heq : dzbar (f ∘ φ) =ᶠ[𝓝 z]
      (fun w => dzbar f (φ w) * conj (deriv φ w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (eq6_4 (hφ.differentiableAt (hU.mem_nhds hw))
      ((hf.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds (hm hw)))).2
  have hd : dz (dzbar (f ∘ φ)) z =
      dz (fun w => dzbar f (φ w) * conj (deriv φ w)) z := by
    unfold dz
    rw [heq.fderiv_eq (𝕜 := ℝ)]
  have hcomp : DifferentiableAt ℝ (fun w => dzbar f (φ w)) z :=
    hfc.comp z (hc.restrictScalars ℝ)
  have hconj : DifferentiableAt ℝ (fun w => conj (deriv φ w)) z :=
    Complex.differentiable_conj.differentiableAt.comp z (hdc.restrictScalars ℝ)
  rw [hd, dz_mul hcomp hconj,
    dz_conj (hdc.restrictScalars ℝ), (cauchyRiemann_iff.mp hdc).2]
  simp only [map_zero, mul_zero, zero_add]
  have hchain : dz (fun w => dzbar f (φ w)) z =
      dz (dzbar f) (φ z) * deriv φ z := (eq6_4 hc hfc).1
  rw [hchain]
  calc
    _ = dz (dzbar f) (φ z) * (deriv φ z * conj (deriv φ z)) := by ring
    _ = _ := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Covariance of the memoir's Laplacian under a holomorphic map preserving
the hyperbolic density. The density identity is an explicit hypothesis. -/
theorem laplace0_comp_of_density_pullback {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {φ f : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ U) (hm : MapsTo φ U V)
    (hf : ContDiffOn ℝ 2 f V) {z : ℂ} (hz : z ∈ U)
    (hρ : rho z ≠ 0) (hp : rho (φ z) * ‖deriv φ z‖ ^ 2 = rho z) :
    laplace0 (f ∘ φ) z = laplace0 f (φ z) := by
  have hr : (rho (φ z) : ℂ) * (‖deriv φ z‖ ^ 2 : ℝ) = (rho z : ℂ) := by
    exact_mod_cast hp
  have hpc : (rho (φ z) : ℂ) * (‖deriv φ z‖ ^ 2 : ℝ) ≠ 0 := by
    rw [hr]
    exact Complex.ofReal_ne_zero.mpr hρ
  have hρc := (mul_ne_zero_iff.mp hpc).1
  have hdc := (mul_ne_zero_iff.mp hpc).2
  unfold laplace0
  rw [dz_dzbar_comp_holomorphic hU hV hφ hm hf hz, ← hr]
  field_simp

end TakhtajanTeo
