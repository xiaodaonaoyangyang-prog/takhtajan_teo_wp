import TakhtajanTeo.Ch1.S1_5_Variational
import TakhtajanTeo.Ch1.Welding
import TakhtajanTeo.Ch1.ResolventDiskMass
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Chapter 1, §2 — `T(1)` as a Hilbert manifold (TT:1346–1898)

* §2.1 the Hilbert spaces `A₂(𝔻)`, `A₂(𝔻*)`, `H^{-1,1}(𝔻)`, `H^{-1,1}(𝔻*)`; Lemma 2.1, Remark 2.2; the distributions
  `𝔇_T`, `𝔇_A`; Theorem 2.3 with (2.1)–(2.3); Remark 2.4
* §2.2 Lemma 2.5, Corollary 2.6, the group `𝒪(𝔻*)₁`, Lemma 2.7, Remark 2.8, Lemma 2.9
* §2.3 the charts `(V_μ, h̃_μ)`, Theorem 2.10, Definition 2.11 (the Hilbert manifold topology), Corollary 2.12, the
  vector fields `∂/∂ε_ν` and the orthogonal projector `P`
* §2.4 the Hilbert manifold structure of `A∞(𝔻)`, Theorem 2.13, the components `T_[μ](1)` and `T₀(1)`

**Modelling.**
- `A₂(𝔻)` is a `Submodule` of `L²(𝔻, ρ⁻¹ d²z)`, so it carries the Hilbert norm `‖φ‖₂`. This is needed for
  holomorphy in the Hilbert space (Theorem 2.10, Theorem 2.13).
- Norm estimates between function spaces use the `ℝ≥0∞`-valued norms `normL2Star` and `normA2`, so that finiteness
  is part of the statement.
- As in §1.1, the Hilbert manifold structure is expressed through its charts.
- The Hilbert manifold topology is the final topology of the atlas (`hilbertTopology`). Components are taken in it.

**Corrections.**
- Lemma 2.7 (TT:1679) is stated with `≤`. The memoir writes `<`, which fails for `λ₁ = λ₂`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## §2.1 Hilbert space structure on tangent spaces -/

/-- The measure `ρ⁻¹ d²z` on `D`. -/
def rhoInvMeasure (D : Set ℂ) : Measure ℂ :=
  (volume.restrict D).withDensity fun z => ENNReal.ofReal (rho z)⁻¹

/-- The measure `ρ d²z` on `D`. -/
def rhoMeasure (D : Set ℂ) : Measure ℂ :=
  (volume.restrict D).withDensity fun z => ENNReal.ofReal (rho z)

/-- `‖φ‖₂ = (∬_D |φ|² ρ⁻¹ d²z)^{1/2} ∈ [0, ∞]` (TT:1351, TT:1359). -/
def normA2 (D : Set ℂ) (φ : ℂ → ℂ) : ℝ≥0∞ :=
  (∫⁻ z in D, (‖φ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹) ^ (1 / 2 : ℝ)

/-- `‖μ‖₂ = (∬_D |μ|² ρ d²z)^{1/2} ∈ [0, ∞]` (TT:1401, TT:1407). -/
def normL2 (D : Set ℂ) (μ : ℂ → ℂ) : ℝ≥0∞ :=
  (∫⁻ z in D, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) ^ (1 / 2 : ℝ)

/-- Homogeneity of the weighted quadratic-differential norm (TT:1351, TT:1359), including infinite norms. -/
theorem normA2_const_mul (D : Set ℂ) (c : ℂ) (φ : ℂ → ℂ) :
    normA2 D (fun z => c * φ z) = (‖c‖₊ : ℝ≥0∞) * normA2 D φ := by
  unfold normA2
  simp_rw [nnnorm_mul, ENNReal.coe_mul, mul_pow, mul_assoc]
  rw [lintegral_const_mul' _ _ (by finiteness)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

/-- Homogeneity of the weighted Beltrami norm (TT:1401, TT:1407), including infinite norms. -/
theorem normL2_const_mul (D : Set ℂ) (c : ℂ) (μ : ℂ → ℂ) :
    normL2 D (fun z => c * μ z) = (‖c‖₊ : ℝ≥0∞) * normL2 D μ := by
  unfold normL2
  simp_rw [nnnorm_mul, ENNReal.coe_mul, mul_pow, mul_assoc]
  rw [lintegral_const_mul' _ _ (by finiteness)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

/-- The weighted norm only uses values on its integration domain (TT:1351, TT:1359). -/
theorem normA2_congr {D : Set ℂ} (hD : MeasurableSet D) {φ ψ : ℂ → ℂ}
    (h : EqOn φ ψ D) : normA2 D φ = normA2 D ψ := by
  unfold normA2
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hD] with z hz
  rw [h hz]

/-- The displayed weighted integral norm is the `L²` seminorm for `ρ⁻¹ d²z` (TT:1351, TT:1359). -/
theorem normA2_eq_eLpNorm (D : Set ℂ) (φ : ℂ → ℂ)
    (hφ : AEStronglyMeasurable φ (rhoInvMeasure D)) :
    normA2 D φ = eLpNorm φ 2 (rhoInvMeasure D) := by
  have hm : Measurable (fun z : ℂ => ENNReal.ofReal (rho z)⁻¹) := by
    unfold rho
    fun_prop
  have hg : AEMeasurable (fun z => ‖φ z‖ₑ ^ (2 : ℕ)) (rhoInvMeasure D) := by fun_prop
  have hi := lintegral_withDensity_eq_lintegral_mul₀' hm.aemeasurable hg
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hφ]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [rhoInvMeasure, hi]
  simp only [normA2, Pi.mul_apply, enorm_eq_nnnorm, mul_comm]

/-- The set of holomorphic functions `φ` on `D` with `‖φ‖₂ < ∞`, i.e. `A₂(D)` as a set of functions (TT:1351, TT:1359).
-/
def A2fun (D : Set ℂ) : Set (ℂ → ℂ) := {φ | DifferentiableOn ℂ φ D ∧ normA2 D φ < ∞}

/-- Finiteness of the weighted quadratic-differential norm gives an integrable real squared norm
(TT:1351, TT:1359). -/
theorem A2fun.integrable_weighted_sq {D : Set ℂ} (hD : IsOpen D) {φ : ℂ → ℂ}
    (hφ : φ ∈ A2fun D) : IntegrableOn (fun z => ‖φ z‖ ^ 2 * (rho z)⁻¹) D := by
  have hw : Continuous (fun z : ℂ => (rho z)⁻¹) := by
    simp only [rho, inv_div]
    fun_prop
  have hc := (hφ.1.continuousOn.norm.pow 2).mul hw.continuousOn
  have hfinite : (∫⁻ z in D, (‖φ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹) < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp hφ.2
  refine ⟨hc.aestronglyMeasurable hD.measurableSet, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hpt (z : ℂ) : ‖‖φ z‖ ^ 2 * (rho z)⁻¹‖ₑ =
      (‖φ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by unfold rho; positivity),
      ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  simpa only [hpt] using hfinite

/-- The squared extended norm equals the real weighted area integral for an `A₂` function
(TT:1351, TT:1359). -/
theorem A2fun.normA2_sq {D : Set ℂ} (hD : IsOpen D) {φ : ℂ → ℂ} (hφ : φ ∈ A2fun D) :
    (normA2 D φ) ^ 2 = ENNReal.ofReal (∫ z in D, ‖φ z‖ ^ 2 * (rho z)⁻¹) := by
  rw [← ENNReal.rpow_two]
  unfold normA2
  rw [← ENNReal.rpow_mul]
  norm_num only [show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  rw [ofReal_integral_eq_lintegral_ofReal (A2fun.integrable_weighted_sq hD hφ)
    (Filter.Eventually.of_forall fun z => by unfold rho; positivity)]
  apply lintegral_congr
  intro z
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]

/-- Integrability of the real weighted squared norm implies finiteness of `normA2`. -/
theorem normA2_lt_top_of_integrable_weighted_sq {D : Set ℂ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun z => ‖f z‖ ^ 2 * (rho z)⁻¹) D) : normA2 D f < ∞ := by
  have hfinite := hf.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfinite
  have hpt (z : ℂ) : ‖‖f z‖ ^ 2 * (rho z)⁻¹‖ₑ =
      (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by unfold rho; positivity),
      ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  simp only [hpt] at hfinite
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfinite.ne

/-- Bounds for the inverse density on the unit disk, used in local L² estimates. -/
theorem rhoInv_disk_bounds {z : ℂ} (hz : z ∈ unitDisc) : 0 ≤ (rho z)⁻¹ ∧ (rho z)⁻¹ ≤ 1 / 4 := by
  have hzN : ‖z‖ < 1 := by simpa only [unitDisc, mem_ball, dist_zero_right] using hz
  have hbase : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hbase1 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖z‖]
  have hs := pow_le_pow_left₀ hbase hbase1 2
  simp only [one_pow] at hs
  constructor
  · unfold rho
    positivity
  · simp only [rho, inv_div]
    exact div_le_div_of_nonneg_right hs (by norm_num)

/-- The elements of `L²(D, ρ⁻¹ d²z)` with a holomorphic representative on `D`. -/
def A2Set (D : Set ℂ) : Set (Lp ℂ 2 (rhoInvMeasure D)) :=
  {f | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ D ∧ f =ᵐ[rhoInvMeasure D] φ}

/-- The Hilbert space `A₂(D)` (TT:1351, TT:1359) for `D = 𝔻` or `D = 𝔻*`, as a subspace of `L²(D, ρ⁻¹ d²z)`, with
norm `‖φ‖₂`. It is written as the span of `A2Set` (a linear subspace); `mem_A2_iff` states that the span adds
nothing. -/
def A2 (D : Set ℂ) : Submodule ℂ (Lp ℂ 2 (rhoInvMeasure D)) := Submodule.span ℂ (A2Set D)

/-- The span in `A2` adds nothing. -/
theorem mem_A2_iff (D : Set ℂ) (f : Lp ℂ 2 (rhoInvMeasure D)) : f ∈ A2 D ↔ f ∈ A2Set D := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem g hg => exact hg
    | zero =>
        exact ⟨0, differentiableOn_const _, Lp.coeFn_zero _ _ _⟩
    | add g h hg hh ihg ihh =>
        obtain ⟨φ, hφ, hgφ⟩ := ihg
        obtain ⟨ψ, hψ, hhψ⟩ := ihh
        exact ⟨φ + ψ, hφ.add hψ, (Lp.coeFn_add g h).trans (hgφ.add hhψ)⟩
    | smul c g hg ih =>
        obtain ⟨φ, hφ, hgφ⟩ := ih
        refine ⟨c • φ, hφ.const_smul c, ?_⟩
        filter_upwards [Lp.coeFn_smul c g, hgφ] with z hz hgz
        simpa only [Pi.smul_apply, hgz] using hz
  · intro hf
    exact Submodule.subset_span hf

/-- The holomorphic representative of an element of `A₂(D)` (junk `0` if none; unique on `D`). -/
def A2.toFun {D : Set ℂ} (φ : A2 D) : ℂ → ℂ :=
  if h : ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ D ∧ (φ : Lp ℂ 2 (rhoInvMeasure D)) =ᵐ[rhoInvMeasure D] ψ then h.choose
  else 0

/-- The chosen representative is holomorphic and represents the original `L²` element (TT:1351, TT:1359). -/
theorem A2.toFun_spec {D : Set ℂ} (φ : A2 D) :
    DifferentiableOn ℂ (A2.toFun φ) D ∧
      (φ : Lp ℂ 2 (rhoInvMeasure D)) =ᵐ[rhoInvMeasure D] A2.toFun φ := by
  have h := (mem_A2_iff D _).mp φ.property
  change ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ D ∧
    (φ : Lp ℂ 2 (rhoInvMeasure D)) =ᵐ[rhoInvMeasure D] ψ at h
  simpa only [A2.toFun, dite_eq_left h] using h.choose_spec

/-- The chosen representative preserves the Hilbert norm (TT:1351, TT:1359). -/
theorem A2.norm_toFun {D : Set ℂ} (φ : A2 D) :
    normA2 D (A2.toFun φ) = (‖φ‖₊ : ℝ≥0∞) := by
  have hrep := (A2.toFun_spec φ).2
  rw [normA2_eq_eLpNorm D _ ((Lp.aestronglyMeasurable _).congr hrep)]
  rw [← eLpNorm_congr_ae hrep, ← Lp.enorm_def]
  rfl

/-- The representative of every `A₂` element belongs to the function-space formulation (TT:1351, TT:1359). -/
theorem A2.toFun_mem {D : Set ℂ} (φ : A2 D) : A2.toFun φ ∈ A2fun D := by
  refine ⟨(A2.toFun_spec φ).1, ?_⟩
  rw [A2.norm_toFun]
  exact ENNReal.coe_lt_top

/-- The density in (1.17) is positive away from the unit circle (TT:1037). -/
theorem rho_pos_of_norm_ne_one {z : ℂ} (hz : ‖z‖ ≠ 1) : 0 < rho z := by
  have hden : 1 - ‖z‖ ^ 2 ≠ 0 := by
    intro h
    apply hz
    nlinarith [norm_nonneg z]
  exact div_pos (by norm_num) (sq_pos_of_ne_zero hden)

/-- The weighted measure used for `A₂` has the same null sets as area on domains away from the unit circle
(TT:1351, TT:1359). -/
theorem rhoInvMeasure_ae_eq_iff {D : Set ℂ} (hD : MeasurableSet D)
    (hcircle : ∀ z ∈ D, ‖z‖ ≠ 1) {f g : ℂ → ℂ} :
    f =ᵐ[rhoInvMeasure D] g ↔ f =ᵐ[volume.restrict D] g := by
  have hm : Measurable (fun z : ℂ => ENNReal.ofReal (rho z)⁻¹) := by
    unfold rho
    fun_prop
  have hp : ∀ᵐ z ∂(volume.restrict D), 0 < ENNReal.ofReal (rho z)⁻¹ := by
    filter_upwards [ae_restrict_mem hD] with z hz
    exact ENNReal.ofReal_pos.mpr (inv_pos.mpr (rho_pos_of_norm_ne_one (hcircle z hz)))
  exact withDensity_ae_eq hm.aemeasurable (hp.mono fun _ hz => ne_of_gt hz)

/-- Holomorphic representatives of the same weighted `L²` element agree pointwise on open domains
away from the unit circle (TT:1351, TT:1359). -/
theorem A2.toFun_eqOn {D : Set ℂ} (hD : IsOpen D) (hcircle : ∀ z ∈ D, ‖z‖ ≠ 1)
    (φ : A2 D) {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ D)
    (hrep : (φ : Lp ℂ 2 (rhoInvMeasure D)) =ᵐ[rhoInvMeasure D] ψ) :
    EqOn (A2.toFun φ) ψ D := by
  have hae := (A2.toFun_spec φ).2.symm.trans hrep
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq
    ((rhoInvMeasure_ae_eq_iff hD.measurableSet hcircle).mp hae) hD
    (A2.toFun_spec φ).1.continuousOn hψ.continuousOn

/-- Addition of chosen holomorphic representatives agrees pointwise on the domain (TT:1351, TT:1359). -/
theorem A2.toFun_add {D : Set ℂ} (hD : IsOpen D) (hcircle : ∀ z ∈ D, ‖z‖ ≠ 1)
    (φ ψ : A2 D) : EqOn (A2.toFun (φ + ψ)) (A2.toFun φ + A2.toFun ψ) D := by
  apply A2.toFun_eqOn hD hcircle
  · exact (A2.toFun_spec φ).1.add (A2.toFun_spec ψ).1
  · exact (Lp.coeFn_add _ _).trans ((A2.toFun_spec φ).2.add (A2.toFun_spec ψ).2)

/-- Scalar multiplication of chosen holomorphic representatives agrees pointwise on the domain
(TT:1351, TT:1359). -/
theorem A2.toFun_smul {D : Set ℂ} (hD : IsOpen D) (hcircle : ∀ z ∈ D, ‖z‖ ≠ 1)
    (c : ℂ) (φ : A2 D) : EqOn (A2.toFun (c • φ)) (c • A2.toFun φ) D := by
  apply A2.toFun_eqOn hD hcircle
  · exact (A2.toFun_spec φ).1.const_smul c
  · rw [Submodule.coe_smul]
    filter_upwards [Lp.coeFn_smul c (φ : Lp ℂ 2 (rhoInvMeasure D)),
      (A2.toFun_spec φ).2] with z hz hφ
    simpa only [Pi.smul_apply, hφ] using hz

/-- Equality of representatives on the integration domain implies equality in `A₂` (TT:1351, TT:1359). -/
theorem A2.ext_of_toFun_eqOn {D : Set ℂ} (hD : MeasurableSet D) {φ ψ : A2 D}
    (h : EqOn (A2.toFun φ) (A2.toFun ψ) D) : φ = ψ := by
  have hae : A2.toFun φ =ᵐ[volume.restrict D] A2.toFun ψ := by
    filter_upwards [ae_restrict_mem hD] with z hz
    exact h hz
  have haw := (withDensity_absolutelyContinuous (volume.restrict D)
    (fun z => ENNReal.ofReal (rho z)⁻¹)).ae_eq hae
  apply Subtype.ext
  exact Lp.ext ((A2.toFun_spec φ).2.trans (haw.trans (A2.toFun_spec ψ).2.symm))

/-- The element of `A₂(D)` represented by a function `φ` with `‖φ‖₂ < ∞` (junk `0` otherwise). -/
def toA2 (D : Set ℂ) (φ : ℂ → ℂ) : A2 D :=
  if h : ∃ f : A2 D, ∀ z ∈ D, A2.toFun f z = φ z then h.choose else 0

/-- Every holomorphic function with finite weighted norm has an `A₂` representative (TT:1351, TT:1359). -/
theorem exists_A2_representative {D : Set ℂ} (hD : IsOpen D)
    (hcircle : ∀ z ∈ D, ‖z‖ ≠ 1) {φ : ℂ → ℂ} (hφ : φ ∈ A2fun D) :
    ∃ f : A2 D, EqOn (A2.toFun f) φ D := by
  have ha : AEStronglyMeasurable φ (rhoInvMeasure D) :=
    (hφ.1.continuousOn.aestronglyMeasurable hD.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hm : MemLp φ 2 (rhoInvMeasure D) := by
    change eLpNorm φ 2 (rhoInvMeasure D) < ∞
    rw [← normA2_eq_eLpNorm D φ ha]
    exact hφ.2
  let f : A2 D := ⟨hm.toLp φ, (mem_A2_iff D _).mpr ⟨φ, hφ.1, hm.coeFn_toLp⟩⟩
  exact ⟨f, A2.toFun_eqOn hD hcircle f hφ.1 hm.coeFn_toLp⟩

/-- `toA2` selects a representative rather than its fallback for functions in `A₂` (TT:1351, TT:1359). -/
theorem toA2_spec {D : Set ℂ} (hD : IsOpen D) (hcircle : ∀ z ∈ D, ‖z‖ ≠ 1)
    {φ : ℂ → ℂ} (hφ : φ ∈ A2fun D) : EqOn (A2.toFun (toA2 D φ)) φ D := by
  obtain ⟨f, hf⟩ := exists_A2_representative hD hcircle hφ
  have hex : ∃ f : A2 D, ∀ z ∈ D, A2.toFun f z = φ z := ⟨f, fun z hz => hf hz⟩
  intro z hz
  simpa only [toA2, dite_eq_left hex] using hex.choose_spec z hz

/-- Passing to the holomorphic representative and back preserves the `A₂` element (TT:1351, TT:1359). -/
theorem toA2_toFun {D : Set ℂ} (hD : IsOpen D) (hcircle : ∀ z ∈ D, ‖z‖ ≠ 1)
    (φ : A2 D) : toA2 D (A2.toFun φ) = φ := by
  exact A2.ext_of_toFun_eqOn hD.measurableSet (toA2_spec hD hcircle (A2.toFun_mem φ))

/-- The inclusion `A₂(𝔻) ↪ A∞(𝔻)` of Lemma 2.1. -/
def A2toAInf (φ : A2 unitDisc) : AInf unitDisc := toAInf unitDisc (A2.toFun φ)

/-- A bounded weighted holomorphic function determines an `A∞` element with the same values
and the stated norm bound. This is the representation step of Lemma 2.1 (TT:1366–1396). -/
theorem exists_AInf_representative_of_bound {D : Set ℂ}
    (hcircle : ∀ z ∈ D, ‖z‖ ≠ 1) {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ D, ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * φ z‖ ≤ C) :
    ∃ f : AInf D, EqOn (AInf.toFun f) φ D ∧ ‖f‖ ≤ C := by
  have hw : Continuous (fun z : D => (1 - (‖(z : ℂ)‖ : ℂ) ^ 2) ^ 2) := by fun_prop
  let f : C(D, ℂ) := ⟨fun z => (1 - (‖(z : ℂ)‖ : ℂ) ^ 2) ^ 2 * φ z,
    hw.mul hφ.continuousOn.domRestrict⟩
  have hf (z : D) : ‖f z‖ ≤ C := hbound z z.property
  let g : BoundedContinuousFunction D ℂ := BoundedContinuousFunction.mkOfBound f (2 * C) (by
    intro x y
    calc
      dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := by simpa only [dist_eq_norm] using norm_sub_le (f x) (f y)
      _ ≤ C + C := add_le_add (hf x) (hf y)
      _ = 2 * C := by ring)
  have hg : EqOn (unweight D g) φ D := by
    intro z hz
    have hn : 1 - ‖z‖ ^ 2 ≠ 0 := by
      intro he
      apply hcircle z hz
      nlinarith [norm_nonneg z]
    have hc : (1 - (‖z‖ : ℂ) ^ 2) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      exact_mod_cast hn
    simp only [unweight, dite_eq_left hz]
    change ((1 - (‖z‖ : ℂ) ^ 2) ^ 2 * φ z) / (1 - (‖z‖ : ℂ) ^ 2) ^ 2 = φ z
    exact mul_div_cancel_left₀ (φ z) hc
  have hgm : g ∈ AInf D := hφ.congr hg
  refine ⟨⟨g, hgm⟩, hg, ?_⟩
  exact (BoundedContinuousFunction.norm_le hC).mpr hf

/-- Away from the unit circle, an `A∞` element is determined by its unweighted representative
(TT:1366–1396). -/
theorem AInf.ext_of_toFun_eqOn {D : Set ℂ} (hcircle : ∀ z ∈ D, ‖z‖ ≠ 1)
    {f g : AInf D} (h : EqOn (AInf.toFun f) (AInf.toFun g) D) : f = g := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro z
  have hn : 1 - ‖(z : ℂ)‖ ^ 2 ≠ 0 := by
    intro he
    apply hcircle z z.property
    nlinarith [norm_nonneg (z : ℂ)]
  have hc : (1 - (‖(z : ℂ)‖ : ℂ) ^ 2) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast hn
  have he := h z.property
  simp only [AInf.toFun, unweight, dite_eq_left z.property] at he
  exact (div_left_inj' hc).mp he

/-- The choice-defined `toAInf` has the expected values and norm whenever the weighted function
is bounded (the representation step of Lemma 2.1, TT:1366–1396). -/
theorem toAInf_spec_of_bound {D : Set ℂ} (hcircle : ∀ z ∈ D, ‖z‖ ≠ 1)
    {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ D) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ D, ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * φ z‖ ≤ C) :
    EqOn (AInf.toFun (toAInf D φ)) φ D ∧ ‖toAInf D φ‖ ≤ C := by
  obtain ⟨f, hf, hnorm⟩ := exists_AInf_representative_of_bound hcircle hφ hC hbound
  have hex : ∃ f : AInf D, ∀ z ∈ D, AInf.toFun f z = φ z := ⟨f, fun z hz => hf hz⟩
  have heq : toAInf D φ = f := by
    apply AInf.ext_of_toFun_eqOn hcircle
    intro z hz
    simpa only [toAInf, dite_eq_left hex] using (hex.choose_spec z hz).trans (hf hz).symm
  rw [heq]
  exact ⟨hf, hnorm⟩

/-- The angular integral on the polar-coordinate interval agrees with the circle average. -/
theorem integral_circleMap_neg_pi_pi (F : ℂ → ℝ) (r : ℝ) :
    (∫ θ in Ioo (-π) π, F (circleMap 0 r θ)) = 2 * π * Real.circleAverage F 0 r := by
  have h := Real.circleAverage_eq_integral_add (f := F) (c := 0) (R := r) (-π)
  rw [intervalIntegral.integral_comp_add_right (fun θ => F (circleMap 0 r θ))] at h
  simp only [zero_add, show 2 * π + -π = π by ring] at h
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo] at h
  rw [h, smul_eq_mul]
  field_simp

/-- Polar integration of a continuous function over the disk through its circle averages.
This supplies the area-to-angular/radial bridge in the weighted Parseval formula (TT:1374–1378). -/
theorem integral_unitDisc_circleAverage (F : ℂ → ℝ) (hF : Continuous F) :
    (∫ z in unitDisc, F z) = 2 * π * ∫ r in (0 : ℝ)..1, r * Real.circleAverage F 0 r := by
  let H : ℝ × ℝ → ℝ := fun p => p.1 * F (circleMap 0 p.1 p.2)
  have hmap (p : ℝ × ℝ) : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    simp only [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I]
    push_cast
    ring
  have hcont : Continuous H := by
    dsimp [H, circleMap]
    fun_prop
  have hint : IntegrableOn H (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) :=
    (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hrestrict : (volume : Measure (ℝ × ℝ)).restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) =
      (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (-π) π)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hset : _root_.polarCoord.target ∩ (Iio (1 : ℝ) ×ˢ (univ : Set ℝ)) =
      Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π := by
    ext p
    simp only [polarCoord_target, mem_inter_iff, mem_prod, mem_Ioi, mem_Iio,
      mem_Ioo, mem_univ, and_true]
    tauto
  calc
    _ = ∫ z, unitDisc.indicator F z := (integral_indicator measurableSet_ball).symm
    _ = ∫ p in _root_.polarCoord.target, p.1 * unitDisc.indicator F (Complex.polarCoord.symm p) := by
      simpa only [smul_eq_mul] using (Complex.integral_comp_polarCoord_symm (unitDisc.indicator F)).symm
    _ = ∫ p in _root_.polarCoord.target, (Iio (1 : ℝ) ×ˢ (univ : Set ℝ)).indicator H p := by
      apply setIntegral_congr_fun _root_.polarCoord.open_target.measurableSet
      intro p hp
      dsimp only
      have hp0 : 0 < p.1 := hp.1
      have hm : Complex.polarCoord.symm p ∈ unitDisc ↔ p.1 < 1 := by
        simp only [unitDisc, mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp0]
      by_cases hr : p.1 < 1
      · rw [indicator_of_mem (hm.mpr hr), indicator_of_mem (show p ∈ Iio (1 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hr, trivial⟩)]
        simp only [H, hmap]
      · rw [indicator_of_notMem (fun hx => hr (hm.mp hx)),
          indicator_of_notMem (show p ∉ Iio (1 : ℝ) ×ˢ (univ : Set ℝ) from fun hx => hr hx.1), mul_zero]
    _ = ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π, H p := by
      rw [setIntegral_indicator (measurableSet_Iio.prod MeasurableSet.univ), hset]
    _ = ∫ r in Ioo (0 : ℝ) 1, ∫ θ in Ioo (-π) π, H (r, θ) := by
      rw [hrestrict]
      exact integral_prod H (by rwa [← hrestrict])
    _ = 2 * π * ∫ r in Ioo (0 : ℝ) 1, r * Real.circleAverage F 0 r := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp only [H]
      rw [integral_const_mul, integral_circleMap_neg_pi_pi]
      ring
    _ = _ := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- The radial moment giving the monomial norms in the weighted Parseval formula
(TT:1374–1378). The factor `π / 2` is supplied by angular integration and `ρ⁻¹`. -/
theorem bergman_radial_moment (n : ℕ) :
    (∫ r in (0 : ℝ)..1, r ^ (2 * n + 1) * (1 - r ^ 2) ^ 2) =
      1 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have hi (k : ℕ) : IntervalIntegrable (fun r : ℝ => r ^ k) volume 0 1 :=
    (continuous_pow k).intervalIntegrable _ _
  have hpoly : (fun r : ℝ => r ^ (2 * n + 1) * (1 - r ^ 2) ^ 2) =
      (fun r => (r ^ (2 * n + 1) - 2 * r ^ (2 * n + 3)) + r ^ (2 * n + 5)) := by
    funext r
    rw [show 2 * n + 3 = (2 * n + 1) + 2 by omega,
      show 2 * n + 5 = (2 * n + 1) + 4 by omega]
    simp only [pow_add]
    ring
  rw [hpoly, intervalIntegral.integral_add ((hi _).sub ((hi _).const_mul 2)) (hi _),
    intervalIntegral.integral_sub (hi _) ((hi _).const_mul 2), intervalIntegral.integral_const_mul]
  rw [integral_pow, integral_pow, integral_pow]
  simp only [one_pow, pow_succ, mul_zero, sub_zero,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  <;> ring

/-- Angular Parseval for a polynomial on a circle of arbitrary nonnegative radius, used in the
weighted disk Parseval formula (TT:1374–1378). -/
theorem polynomial_circle_average_sq (p : Polynomial ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Real.circleAverage (fun z => ‖p.eval z‖ ^ 2) 0 r =
      ∑ n ∈ p.support, ‖p.coeff n‖ ^ 2 * r ^ (2 * n) := by
  let q := p.comp (Polynomial.C (r : ℂ) * Polynomial.X)
  have hsupport : q.support ⊆ p.support := by
    intro n hn
    by_contra hp
    have hpzero : p.coeff n = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hp
    have hqzero : q.coeff n = 0 := by
      simp only [q, Polynomial.comp_C_mul_X_coeff, hpzero, zero_mul]
    exact (Polynomial.mem_support_iff.mp hn) hqzero
  have hcircle : Real.circleAverage (fun z => ‖q.eval z‖ ^ 2) 0 1 =
      Real.circleAverage (fun z => ‖p.eval z‖ ^ 2) 0 r := by
    simp only [q, Real.circleAverage, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, circleMap, Complex.ofReal_one, zero_add, one_mul]
  calc
    _ = Real.circleAverage (fun z => ‖q.eval z‖ ^ 2) 0 1 := hcircle.symm
    _ = ∑ n ∈ q.support, ‖q.coeff n‖ ^ 2 := q.sum_sq_norm_coeff_eq_circleAverage.symm
    _ = ∑ n ∈ p.support, ‖q.coeff n‖ ^ 2 := by
      apply Finset.sum_subset hsupport
      intro n hn hqn
      have hqzero : q.coeff n = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hqn
      simp only [hqzero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [q, Polynomial.comp_C_mul_X_coeff, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr, mul_pow, ← pow_mul, Nat.mul_comm]

/-- Integrating the polynomial angular Parseval identity against the radial weight
gives the coefficient denominators in TT:1374–1378. -/
theorem polynomial_weighted_circle_average (p : Polynomial ℂ) :
    (∫ r in (0 : ℝ)..1, r * (1 - r ^ 2) ^ 2 * Real.circleAverage (fun z => ‖p.eval z‖ ^ 2) 0 r) =
      ∑ n ∈ p.support, ‖p.coeff n‖ ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have heq : (∫ r in (0 : ℝ)..1, r * (1 - r ^ 2) ^ 2 * Real.circleAverage (fun z => ‖p.eval z‖ ^ 2) 0 r) =
      ∫ r in (0 : ℝ)..1, ∑ n ∈ p.support, ‖p.coeff n‖ ^ 2 * (r ^ (2 * n + 1) * (1 - r ^ 2) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : 0 ≤ r := (show r ∈ Icc (0 : ℝ) 1 by simpa using hr).1
    dsimp only
    rw [polynomial_circle_average_sq p hr0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [pow_succ]
    ring
  rw [heq, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_const_mul, bergman_radial_moment]
    ring
  · intro n hn
    exact (by fun_prop : Continuous (fun r : ℝ =>
      ‖p.coeff n‖ ^ 2 * (r ^ (2 * n + 1) * (1 - r ^ 2) ^ 2))).intervalIntegrable _ _

/-- Weighted disk Parseval for polynomials, with the memoir's density normalization
(TT:1374–1378). -/
theorem polynomial_weighted_area (p : Polynomial ℂ) :
    (∫ z in unitDisc, ‖p.eval z‖ ^ 2 * (rho z)⁻¹) =
      (π / 2) * ∑ n ∈ p.support, ‖p.coeff n‖ ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  let F : ℂ → ℝ := fun z => ‖p.eval z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hpoint (z : ℂ) : ‖p.eval z‖ ^ 2 * (rho z)⁻¹ = F z := by
    simp only [F, rho, inv_div]
    ring
  have havg (r : ℝ) : Real.circleAverage F 0 r =
      (1 - r ^ 2) ^ 2 / 4 * Real.circleAverage (fun z => ‖p.eval z‖ ^ 2) 0 r := by
    simp only [Real.circleAverage, F, norm_circleMap_zero, sq_abs, div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
    simp only [smul_eq_mul]
    ring
  calc
    _ = ∫ z in unitDisc, F z := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      exact hpoint z
    _ = 2 * π * ∫ r in (0 : ℝ)..1, r * Real.circleAverage F 0 r := integral_unitDisc_circleAverage F hF
    _ = 2 * π * ((1 / 4) * ∫ r in (0 : ℝ)..1,
        r * (1 - r ^ 2) ^ 2 * Real.circleAverage (fun z => ‖p.eval z‖ ^ 2) 0 r) := by
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r hr
      dsimp only
      rw [havg]
      ring
    _ = _ := by
      rw [polynomial_weighted_circle_average]
      ring

/-- The exact weighted area norm of a monomial, using the shared disk radial formula
(TT:1374–1378). -/
theorem bergman_monomial_area (n : ℕ) :
    (∫ z in unitDisc, ‖z ^ n‖ ^ 2 * (rho z)⁻¹) =
      π / (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) := by
  let f : ℝ → ℝ := fun r => r ^ (2 * n) * (1 - r ^ 2) ^ 2 / 4
  have hpoint (z : ℂ) : ‖z ^ n‖ ^ 2 * (rho z)⁻¹ = f ‖z‖ := by
    simp only [f, norm_pow, rho, inv_div, ← pow_mul, Nat.mul_comm]
    ring
  have hrad : (∫ r in Ioo (0 : ℝ) 1, r * f r) =
      (1 / 4) * ∫ r in (0 : ℝ)..1, r ^ (2 * n + 1) * (1 - r ^ 2) ^ 2 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only [f]
    rw [pow_succ]
    ring
  calc
    _ = ∫ z in unitDisc, f ‖z‖ := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      exact hpoint z
    _ = 2 * π * ∫ r in Ioo (0 : ℝ) 1, r * f r := integral_unitDisc_radial f
    _ = _ := by
      rw [hrad, bergman_radial_moment]
      field_simp
      ring

/-- The shifted cubic coefficient in the weighted Bergman kernel is a binomial coefficient
(TT:1386–1390). -/
theorem bergman_coefficient_eq_choose (n : ℕ) :
    6 * ((n + 3).choose 3 : ℝ) = ((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2) := by
  have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.ascFactorial_eq_factorial_mul_choose n 3)
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero] at h
  linear_combination -h

/-- The scalar series used in the sharp weighted Bergman evaluation estimate (TT:1386–1390),
with the original index `n ≥ 2` shifted to `n ≥ 0`. -/
theorem hasSum_bergman_coefficients {r : ℝ} (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => (((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2)) * r ^ n)
      (6 / (1 - r) ^ 4) := by
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one 3 hr).mul_left (6 : ℝ)
  convert hs using 1
  · ext n
    rw [← mul_assoc, bergman_coefficient_eq_choose]
  · norm_num
    ring

/-- The finite weighted Cauchy–Schwarz estimate used before passing to the Bergman series
(TT:1380–1384). -/
theorem weighted_polynomial_bound_sq (s : Finset ℕ) (w : ℕ → ℝ) (a : ℕ → ℂ) (z : ℂ)
    (hw : ∀ n ∈ s, 0 ≤ w n) :
    ‖∑ n ∈ s, (w n : ℂ) * a n * z ^ n‖ ^ 2 ≤
      (∑ n ∈ s, w n * ‖a n‖ ^ 2) * (∑ n ∈ s, w n * (‖z‖ ^ n) ^ 2) := by
  have hnorm : ‖∑ n ∈ s, (w n : ℂ) * a n * z ^ n‖ ≤
      ∑ n ∈ s, w n * ‖a n‖ * ‖z‖ ^ n := by
    calc
      _ ≤ ∑ n ∈ s, ‖(w n : ℂ) * a n * z ^ n‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n hn)]
  apply (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro n hn
    exact mul_nonneg (hw n hn) (sq_nonneg _)
  · intro n hn
    exact mul_nonneg (hw n hn) (sq_nonneg _)
  · intro n hn
    apply le_of_eq
    ring

/-- The finite partial sums satisfy the scalar evaluation bound in Lemma 2.1 (TT:1380–1394).
The remaining Parseval step identifies the coefficient sum with the weighted area norm. -/
theorem bergman_polynomial_bound_sq (s : Finset ℕ) (a : ℕ → ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖∑ n ∈ s, ((((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2) : ℝ) : ℂ) * a n * z ^ n‖ ^ 2 ≤
      (∑ n ∈ s, (((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2)) * ‖a n‖ ^ 2) *
        (6 / (1 - ‖z‖ ^ 2) ^ 4) := by
  let w : ℕ → ℝ := fun n => ((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2)
  have hw (n : ℕ) : 0 ≤ w n := by
    dsimp [w]
    rw [← bergman_coefficient_eq_choose]
    positivity
  have hr : ‖‖z‖ ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg z]
  have hs := hasSum_bergman_coefficients hr
  have hsum : (∑ n ∈ s, w n * (‖z‖ ^ n) ^ 2) ≤ 6 / (1 - ‖z‖ ^ 2) ^ 4 := by
    have hle := sum_le_hasSum s (fun n _ => mul_nonneg (hw n) (pow_nonneg (sq_nonneg ‖z‖) n)) hs
    simpa only [w, ← pow_mul, Nat.mul_comm] using hle
  exact (weighted_polynomial_bound_sq s w a z (fun n _ => hw n)).trans
    (mul_le_mul_of_nonneg_left hsum (Finset.sum_nonneg fun n _ => mul_nonneg (hw n) (sq_nonneg _)))

/-- Passing the finite weighted estimate to a convergent Bergman expansion (TT:1380–1394). -/
theorem bergman_series_bound_sq (a : ℕ → ℂ) {z v : ℂ} (hz : ‖z‖ < 1)
    (hseries : HasSum (fun n : ℕ =>
      ((((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2) : ℝ) : ℂ) * a n * z ^ n) v)
    (henergy : Summable (fun n : ℕ => (((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2)) * ‖a n‖ ^ 2)) :
    ‖v‖ ^ 2 ≤ (∑' n : ℕ, (((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2)) * ‖a n‖ ^ 2) *
      (6 / (1 - ‖z‖ ^ 2) ^ 4) := by
  have hl : Tendsto (fun s : Finset ℕ =>
      ∑ n ∈ s, ((((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2) : ℝ) : ℂ) * a n * z ^ n) atTop (𝓝 v) := hseries
  have hr : Tendsto (fun s : Finset ℕ =>
      ∑ n ∈ s, (((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2)) * ‖a n‖ ^ 2) atTop
      (𝓝 (∑' n : ℕ, (((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2)) * ‖a n‖ ^ 2)) := henergy.hasSum
  exact le_of_tendsto_of_tendsto' (hl.norm.pow 2) (hr.mul_const _)
    (fun s => bergman_polynomial_bound_sq s a hz)

/-- The sharp weighted evaluation inequality for polynomials, now expressed in terms of the
actual weighted disk integral rather than an assumed coefficient identity (TT:1374–1396). -/
theorem polynomial_weighted_evaluation_sq (p : Polynomial ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - ‖z‖ ^ 2) ^ 4 * ‖p.eval z‖ ^ 2 ≤
      (12 / π) * ∫ u in unitDisc, ‖p.eval u‖ ^ 2 * (rho u)⁻¹ := by
  let w : ℕ → ℝ := fun n => ((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2)
  have hwfactor (n : ℕ) : w n = ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by
    dsimp [w]
    ring
  have hwpos (n : ℕ) : 0 < w n := by rw [hwfactor]; positivity
  have hsum : (∑ n ∈ p.support, (w n : ℂ) * (p.coeff n / (w n : ℂ)) * z ^ n) = p.eval z := by
    rw [Polynomial.eval_eq_sum]
    change _ = ∑ n ∈ p.support, p.coeff n * z ^ n
    apply Finset.sum_congr rfl
    intro n hn
    have hnc : (w n : ℂ) ≠ 0 := by exact_mod_cast (hwpos n).ne'
    field_simp
  have henergy : (∑ n ∈ p.support, w n * ‖p.coeff n / (w n : ℂ)‖ ^ 2) =
      ∑ n ∈ p.support, ‖p.coeff n‖ ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hwpos n)]
    rw [← hwfactor]
    field_simp
  have hb := bergman_polynomial_bound_sq p.support (fun n => p.coeff n / (w n : ℂ)) hz
  change ‖∑ n ∈ p.support, (w n : ℂ) * (p.coeff n / (w n : ℂ)) * z ^ n‖ ^ 2 ≤
    (∑ n ∈ p.support, w n * ‖p.coeff n / (w n : ℂ)‖ ^ 2) * (6 / (1 - ‖z‖ ^ 2) ^ 4) at hb
  rw [hsum, henergy] at hb
  have hbase : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hm := mul_le_mul_of_nonneg_left hb (le_of_lt (pow_pos hbase 4))
  rw [polynomial_weighted_area]
  convert hm using 1 <;> field_simp <;> ring

/-- A function holomorphic on a larger closed disk is uniformly approximated by complex
polynomials on the closed unit disk. This supplies the approximation step for Lemma 2.1
(TT:1374–1396). -/
theorem holomorphic_polynomial_approx_closedBall {R : ℝ} (hR : 1 < R) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    ∃ p : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z => (p n).eval z) f atTop (closedBall 0 1) := by
  let Rn : NNReal := ⟨R, by linarith⟩
  let rn : NNReal := ⟨(1 + R) / 2, by linarith⟩
  have hpower := hf.hasFPowerSeriesOnBall (R := Rn) (by change 0 < R; linarith)
  have hsmall : (rn : ℝ≥0∞) < (Rn : ℝ≥0∞) := by
    apply ENNReal.coe_lt_coe.mpr
    change (1 + R) / 2 < R
    linarith
  have hU := hpower.tendstoUniformlyOn hsmall
  let a : ℕ → ℂ := fun n => cauchyPowerSeries f 0 (Rn : ℝ) n (fun _ => 1)
  let p : ℕ → Polynomial ℂ := fun n => ∑ k ∈ Finset.range n, Polynomial.C (a k) * Polynomial.X ^ k
  have heval (n : ℕ) (z : ℂ) : (p n).eval z = (cauchyPowerSeries f 0 (Rn : ℝ)).partialSum n z := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, FormalMultilinearSeries.partialSum]
    apply Finset.sum_congr rfl
    intro k hk
    simp [a, cauchyPowerSeries,
      ContinuousMultilinearMap.mkPiRing_apply, mul_comm]
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 (rn : ℝ) := by
    intro z hz
    exact lt_of_le_of_lt hz (by change 1 < (1 + R) / 2; linarith)
  refine ⟨p, ?_⟩
  simpa only [← heval, zero_add] using hU.mono hsub

/-- Uniform polynomial approximation on the closed disk preserves the weighted area integral
(the limiting step in Lemma 2.1, TT:1374–1396). -/
theorem weighted_polynomial_integral_tendsto (p : ℕ → Polynomial ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (closedBall 0 1))
    (hU : TendstoUniformlyOn (fun n z => (p n).eval z) f atTop (closedBall 0 1)) :
    Tendsto (fun n => ∫ z in unitDisc, ‖(p n).eval z‖ ^ 2 * (rho z)⁻¹) atTop
      (𝓝 (∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹)) := by
  letI : IsFiniteMeasure (volume.restrict unitDisc) := isFiniteMeasure_restrict.mpr (by
    change volume (ball (0 : ℂ) 1) ≠ ∞
    exact measure_ball_lt_top.ne)
  let G : ℕ → ℂ → ℝ := fun n z => ‖(p n).eval z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4
  let g : ℂ → ℝ := fun z => ‖f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
  have hnear := (Metric.tendstoUniformlyOn_iff.mp hU) 1 (by norm_num)
  have hmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (G n) (volume.restrict unitDisc) := by
    apply Filter.Eventually.of_forall
    intro n
    exact (by dsimp [G]; fun_prop : Continuous (G n)).aestronglyMeasurable
  have hbound : ∃ K, ∀ᶠ n : ℕ in atTop, ∀ᵐ z ∂(volume.restrict unitDisc), ‖G n z‖ ≤ K := by
    refine ⟨(C + 1) ^ 2, ?_⟩
    filter_upwards [hnear] with n hn
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzc : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz
    have hdist : ‖(p n).eval z - f z‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hn z hzc
    have hpn : ‖(p n).eval z‖ ≤ C + 1 := by
      have ht := norm_add_le ((p n).eval z - f z) (f z)
      rw [sub_add_cancel] at ht
      linarith [hC z hzc]
    have hzN : ‖z‖ < 1 := by simpa only [unitDisc, mem_ball, dist_zero_right] using hz
    have hbase : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hbase1 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖z‖]
    have hw : (1 - ‖z‖ ^ 2) ^ 2 / 4 ≤ 1 := by
      have hs := pow_le_pow_left₀ hbase hbase1 2
      simp only [one_pow] at hs
      linarith
    have hG0 : 0 ≤ G n z := by dsimp [G]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hG0]
    calc
      G n z = ‖(p n).eval z‖ ^ 2 * ((1 - ‖z‖ ^ 2) ^ 2 / 4) := by dsimp [G]; ring
      _ ≤ ‖(p n).eval z‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ ≤ (C + 1) ^ 2 := by simpa only [mul_one] using pow_le_pow_left₀ (norm_nonneg _) hpn 2
  have hlim : ∀ᵐ z ∂(volume.restrict unitDisc), Tendsto (fun n => G n z) atTop (𝓝 (g z)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have ht := ((hU.tendsto_at (ball_subset_closedBall hz)).norm.pow 2).mul_const
      ((1 - ‖z‖ ^ 2) ^ 2 / 4)
    simpa only [G, g, mul_div_assoc] using ht
  have h := tendsto_integral_filter_of_norm_le_const hmeas hbound hlim
  simpa only [G, g, rho, inv_div, mul_div_assoc] using h

/-- The sharp weighted evaluation inequality for functions holomorphic on a neighborhood of the
closed disk, obtained by actual polynomial approximation (TT:1374–1396). -/
theorem holomorphic_closedDisk_weighted_evaluation_sq {R : ℝ} (hR : 1 < R) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - ‖z‖ ^ 2) ^ 4 * ‖f z‖ ^ 2 ≤ (12 / π) * ∫ u in unitDisc, ‖f u‖ ^ 2 * (rho u)⁻¹ := by
  obtain ⟨p, hp⟩ := holomorphic_polynomial_approx_closedBall hR hf
  have hzclosed : z ∈ closedBall (0 : ℂ) 1 := by simpa only [mem_closedBall, dist_zero_right] using hz.le
  have hleft := ((hp.tendsto_at hzclosed).norm.pow 2).const_mul ((1 - ‖z‖ ^ 2) ^ 4)
  have hright := (weighted_polynomial_integral_tendsto p
    (hf.continuousOn.mono (closedBall_subset_closedBall hR.le)) hp).const_mul (12 / π)
  exact le_of_tendsto_of_tendsto' hleft hright (fun n => polynomial_weighted_evaluation_sq (p n) hz)

/-- Inward dilation of a disk-holomorphic function is holomorphic on a larger closed disk.
This is the exhaustion step for Lemma 2.1 (TT:1374–1396). -/
theorem holomorphic_inward_dilate {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ R : ℝ, 1 < R ∧ DifferentiableOn ℂ (fun z => f ((s : ℂ) * z)) (closedBall 0 R) := by
  let R : ℝ := (1 + s) / (2 * s)
  have hR : 1 < R := (lt_div_iff₀ (mul_pos (by norm_num) hs0)).mpr (by linarith)
  refine ⟨R, hR, hf.comp (differentiable_id.const_mul (s : ℂ)).differentiableOn ?_⟩
  intro z hz
  have hzN : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  simp only [unitDisc, mem_ball, dist_zero_right]
  calc
    ‖(s : ℂ) * z‖ = s * ‖z‖ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    _ ≤ s * R := mul_le_mul_of_nonneg_left hzN hs0.le
    _ = (1 + s) / 2 := by dsimp [R]; field_simp
    _ < 1 := by linarith

/-- The inverse hyperbolic density increases under inward radial dilation on the disk. -/
theorem rhoInv_inward_dilate_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z : ℂ}
    (hz : z ∈ unitDisc) : (rho z)⁻¹ ≤ (rho ((s : ℂ) * z))⁻¹ := by
  have hzN : ‖z‖ < 1 := by simpa only [unitDisc, mem_ball, dist_zero_right] using hz
  have hsn : ‖(s : ℂ) * z‖ ≤ ‖z‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs1 (norm_nonneg z)
  have hs2 := pow_le_pow_left₀ (norm_nonneg ((s : ℂ) * z)) hsn 2
  have hbase : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hdiff : 1 - ‖z‖ ^ 2 ≤ 1 - ‖(s : ℂ) * z‖ ^ 2 := by linarith
  have hsq := pow_le_pow_left₀ hbase hdiff 2
  simp only [rho, inv_div]
  exact div_le_div_of_nonneg_right hsq (by norm_num)

/-- The weighted mass of an inward dilation is at most `s⁻²` times the original mass.
This allows the closed-disk evaluation estimate to exhaust the open disk (TT:1374–1396). -/
theorem A2fun.inward_dilate_mass_le {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (∫ z in unitDisc, ‖f ((s : ℂ) * z)‖ ^ 2 * (rho z)⁻¹) ≤
      (s ^ 2)⁻¹ * ∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹ := by
  let F : ℂ → ℝ := fun z => ‖f z‖ ^ 2 * (rho z)⁻¹
  let Fs : ℂ → ℝ := fun z => ‖f ((s : ℂ) * z)‖ ^ 2 * (rho z)⁻¹
  let H : ℂ → ℝ := unitDisc.indicator F
  have hH : Integrable H := (A2fun.integrable_weighted_sq isOpen_ball hf).integrable_indicator measurableSet_ball
  have hcomp : Integrable (fun z => H ((s : ℂ) * z)) := by
    simpa only [Complex.real_smul] using hH.comp_smul hs0.ne'
  obtain ⟨R, hR, hfs⟩ := holomorphic_inward_dilate hf.1 hs0 hs1
  have hw : Continuous (fun z : ℂ => (rho z)⁻¹) := by simp only [rho, inv_div]; fun_prop
  have hclosed : ContinuousOn Fs (closedBall 0 1) :=
    ((hfs.continuousOn.mono (closedBall_subset_closedBall hR.le)).norm.pow 2).mul hw.continuousOn
  have hFs : IntegrableOn Fs unitDisc :=
    (hclosed.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set ball_subset_closedBall
  have hHnonneg (z : ℂ) : 0 ≤ H z := by
    dsimp only [H]
    apply Set.indicator_nonneg
    intro u hu
    dsimp [F, rho]
    positivity
  have hmono (z : ℂ) : unitDisc.indicator Fs z ≤ H ((s : ℂ) * z) := by
    by_cases hz : z ∈ unitDisc
    · have hzN : ‖z‖ < 1 := by simpa only [unitDisc, mem_ball, dist_zero_right] using hz
      have hsz : (s : ℂ) * z ∈ unitDisc := by
        simp only [unitDisc, mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hs0]
        exact lt_of_le_of_lt (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hs1.le (norm_nonneg z)) hzN
      rw [indicator_of_mem hz]
      dsimp only [H]
      rw [indicator_of_mem hsz]
      exact mul_le_mul_of_nonneg_left (rhoInv_inward_dilate_le hs0.le hs1.le hz) (sq_nonneg _)
    · rw [indicator_of_notMem hz]
      exact hHnonneg _
  have hscale : (∫ z : ℂ, H ((s : ℂ) * z)) = (s ^ 2)⁻¹ * ∫ z in unitDisc, F z := by
    have h := Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ) H s (hR := hs0.le)
    have hHi : (∫ z : ℂ, H z) = ∫ z in unitDisc, F z :=
      integral_indicator (measurableSet_ball : MeasurableSet unitDisc)
    simpa only [Complex.real_smul, Complex.finrank_real_complex, smul_eq_mul, hHi] using h
  calc
    _ = ∫ z : ℂ, unitDisc.indicator Fs z := (integral_indicator measurableSet_ball).symm
    _ ≤ ∫ z : ℂ, H ((s : ℂ) * z) := integral_mono (hFs.integrable_indicator measurableSet_ball) hcomp hmono
    _ = _ := hscale

/-- The sharp weighted evaluation inequality on the open disk, obtained by inward dilation
and passage to the limit (TT:1374–1396). -/
theorem A2fun.disk_weighted_evaluation_sq {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    (1 - ‖z‖ ^ 2) ^ 4 * ‖f z‖ ^ 2 ≤ (12 / π) * ∫ u in unitDisc, ‖f u‖ ^ 2 * (rho u)⁻¹ := by
  have hzN : ‖z‖ < 1 := by simpa only [unitDisc, mem_ball, dist_zero_right] using hz
  have harg₀ : Tendsto (fun s : ℝ => (s : ℂ) * z) (𝓝 1) (𝓝 z) := by
    simpa only [Complex.ofReal_one, one_mul] using (continuous_ofReal.mul_const z).tendsto 1
  have harg : Tendsto (fun s : ℝ => (s : ℂ) * z) (𝓝[<] 1) (𝓝 z) := harg₀.mono_left nhdsWithin_le_nhds
  have hfz := (hf.1.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)).tendsto.comp harg
  have hleft := (hfz.norm.pow 2).const_mul ((1 - ‖z‖ ^ 2) ^ 4)
  let M : ℝ := ∫ u in unitDisc, ‖f u‖ ^ 2 * (rho u)⁻¹
  have hright₀ : Tendsto (fun s : ℝ => (12 / π) * ((s ^ 2)⁻¹ * M)) (𝓝 1) (𝓝 ((12 / π) * M)) := by
    have hc : ContinuousAt (fun s : ℝ => (12 / π) * ((s ^ 2)⁻¹ * M)) 1 :=
      (((continuousAt_id.pow 2).inv₀ (by norm_num)).mul_const M).const_mul (12 / π)
    simpa only [one_pow, inv_one, one_mul] using hc.tendsto
  have hright : Tendsto (fun s : ℝ => (12 / π) * ((s ^ 2)⁻¹ * M)) (𝓝[<] 1)
      (𝓝 ((12 / π) * M)) := hright₀.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  have hpos₀ : ∀ᶠ s : ℝ in 𝓝 (1 : ℝ), 0 < s := Ioi_mem_nhds (by norm_num)
  have hpos : ∀ᶠ s : ℝ in 𝓝[<] 1, 0 < s := hpos₀.filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with s hs0 hs1
  obtain ⟨R, hR, hfs⟩ := holomorphic_inward_dilate hf.1 hs0 hs1
  exact (holomorphic_closedDisk_weighted_evaluation_sq hR hfs hzN).trans
    (mul_le_mul_of_nonneg_left (A2fun.inward_dilate_mass_le hf hs0 hs1) (by positivity))

/-- The disk case of Lemma 2.1 with the extended norm used by the statement (TT:1366–1396). -/
theorem lemma_2_1_disc {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDisc) :
    ∀ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖) ≤
      ENNReal.ofReal (Real.sqrt (12 / π)) * normA2 unitDisc φ := by
  intro z hz
  have hsq := A2fun.disk_weighted_evaluation_sq hφ hz
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simp only [ENNReal.rpow_two, mul_pow]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity), A2fun.normA2_sq (D := unitDisc) isOpen_ball hφ,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  convert hsq using 1 <;> ring

/-- An unweighted local L² estimate at the disk center, used to remove an L² puncture.
The non-sharp constant `3 / π` follows from the proved weighted evaluation bound. -/
theorem holomorphic_L2_disk_center_bound {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hL2 : IntegrableOn (fun z => ‖f z‖ ^ 2) unitDisc) :
    ‖f 0‖ ^ 2 ≤ (3 / π) * ∫ z in unitDisc, ‖f z‖ ^ 2 := by
  have hw : Continuous (fun z : ℂ => (rho z)⁻¹) := by simp only [rho, inv_div]; fun_prop
  have hc := (hf.continuousOn.norm.pow 2).mul hw.continuousOn
  have hG : IntegrableOn (fun z => ‖f z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
    apply hL2.mono' (hc.aestronglyMeasurable measurableSet_ball)
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hb := rhoInv_disk_bounds hz
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hb.1)]
    have hw1 : (rho z)⁻¹ ≤ 1 := hb.2.trans (by norm_num)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hw1 (sq_nonneg ‖f z‖)
  have hmass : (∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹) ≤
      (1 / 4) * ∫ z in unitDisc, ‖f z‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae hG (hL2.const_mul (1 / 4))
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (rhoInv_disk_bounds hz).2 (sq_nonneg ‖f z‖)
  have hA2 : f ∈ A2fun unitDisc := ⟨hf, normA2_lt_top_of_integrable_weighted_sq hG⟩
  have hcenter := A2fun.disk_weighted_evaluation_sq hA2 (mem_ball_self (by norm_num))
  calc
    ‖f 0‖ ^ 2 ≤ (12 / π) * ∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹ := by simpa using hcenter
    _ ≤ (12 / π) * ((1 / 4) * ∫ z in unitDisc, ‖f z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

/-- The affine rescaling used to transfer local disk estimates. -/
theorem affine_unitDisc_image (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (fun z : ℂ => c + (R : ℂ) * z) '' unitDisc = ball c R := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzN : ‖z‖ < 1 := by simpa only [unitDisc, mem_ball, dist_zero_right] using hz
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hzN hR
  · intro hw
    refine ⟨(w - c) / (R : ℂ), ?_, ?_⟩
    · simp only [unitDisc, mem_ball, dist_zero_right, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR]
      apply (div_lt_one hR).mpr
      simpa only [mem_ball, dist_eq_norm] using hw
    · field_simp
      <;> ring

/-- A local area L² estimate on an arbitrary disk; its radius-normalized form is suited to
the removable-singularity argument. -/
theorem holomorphic_L2_ball_center_bound {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hL2 : IntegrableOn (fun z => ‖f z‖ ^ 2) (ball c R)) :
    R ^ 2 * ‖f c‖ ^ 2 ≤ (3 / π) * ∫ z in ball c R, ‖f z‖ ^ 2 := by
  let A : ℂ → ℂ := fun z => c + (R : ℂ) * z
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hAdiff : Differentiable ℂ A := by dsimp [A]; fun_prop
  have hAinj : Function.Injective A := by
    intro z w he
    exact mul_left_cancel₀ hRc (add_left_cancel he)
  have hAder (z : ℂ) : deriv A z = (R : ℂ) := by
    simpa only [A, Pi.add_def, id_eq, zero_add, mul_one] using
      ((hasDerivAt_const z c).add ((hasDerivAt_id z).const_mul (R : ℂ))).deriv
  have himage : A '' unitDisc = ball c R := affine_unitDisc_image c hR
  have hmap : MapsTo A unitDisc (ball c R) := by
    intro z hz
    rw [← himage]
    exact mem_image_of_mem A hz
  have hqhol : DifferentiableOn ℂ (fun z => f (A z)) unitDisc := hf.comp hAdiff.differentiableOn hmap
  have hi := ahP_integrableOn_image (U := unitDisc) isOpen_ball hAdiff.differentiableOn hAinj.injOn
    (fun z => ‖f z‖ ^ 2)
  rw [himage] at hi
  have hqscaled := hi.mp hL2
  simp only [hAder, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, smul_eq_mul] at hqscaled
  have hqInt : IntegrableOn (fun z => ‖f (A z)‖ ^ 2) unitDisc :=
    (integrable_const_mul_iff (c := R ^ 2) (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hR.ne')) _).mp hqscaled
  have harea := ahP_integral_image (U := unitDisc) isOpen_ball hAdiff.differentiableOn hAinj.injOn
    (fun z => ‖f z‖ ^ 2)
  rw [himage] at harea
  simp only [hAder, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, smul_eq_mul] at harea
  rw [integral_const_mul] at harea
  have hcenter : ‖f c‖ ^ 2 ≤ (3 / π) * ∫ z in unitDisc, ‖f (A z)‖ ^ 2 := by
    simpa only [A, mul_zero, add_zero] using holomorphic_L2_disk_center_bound hqhol hqInt
  calc
    _ ≤ R ^ 2 * ((3 / π) * ∫ z in unitDisc, ‖f (A z)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcenter (sq_nonneg R)
    _ = _ := by rw [harea]; ring

/-- The integral of a locally integrable function over disks shrinking to a point tends to zero.
This is the mass-decay input for removing an L² puncture. -/
theorem integrableOn_integral_ball_tendsto_zero {F : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hF : IntegrableOn F (ball 0 R)) :
    Tendsto (fun r : ℝ => ∫ z in ball (0 : ℂ) r, F z) (𝓝 0) (𝓝 0) := by
  let H : ℂ → ℝ := (ball (0 : ℂ) R).indicator F
  have hH : Integrable H := hF.integrable_indicator measurableSet_ball
  have hlim : ∀ᵐ z : ℂ, Tendsto (fun r : ℝ => (ball (0 : ℂ) r).indicator H z) (𝓝 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    have he : ∀ᶠ r : ℝ in 𝓝 0, r < ‖z‖ := Iio_mem_nhds (norm_pos_iff.mpr hz)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with r hr
    have hnot : z ∉ ball (0 : ℂ) r := by
      simp only [mem_ball, dist_zero_right, not_lt]
      exact hr.le
    simp only [indicator_of_notMem hnot]
  have ht := tendsto_integral_filter_of_dominated_convergence (fun z => ‖H z‖)
    (Filter.Eventually.of_forall fun r : ℝ => hH.aestronglyMeasurable.indicator (measurableSet_ball : MeasurableSet (ball (0 : ℂ) r)))
    (Filter.Eventually.of_forall fun _ => ae_of_all volume fun z => norm_indicator_le_norm_self H z)
    hH.norm hlim
  have hi (r : ℝ) : (∫ z : ℂ, (ball (0 : ℂ) r).indicator H z) = ∫ z in ball (0 : ℂ) r, H z :=
    integral_indicator measurableSet_ball
  have ht' : Tendsto (fun r : ℝ => ∫ z in ball (0 : ℂ) r, H z) (𝓝 0) (𝓝 0) := by
    simpa only [hi, integral_zero] using ht
  apply ht'.congr'
  filter_upwards [Iio_mem_nhds hR] with r hr
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  simp only [H, indicator_of_mem (ball_subset_ball hr.le hz)]

/-- A punctured holomorphic L² function is controlled near the puncture by its shrinking local mass. -/
theorem punctured_holomorphic_L2_bound {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R \ {0}))
    (hL2 : IntegrableOn (fun z => ‖f z‖ ^ 2) (ball 0 R)) {z : ℂ}
    (hz0 : z ≠ 0) (hzR : ‖z‖ < R / 2) :
    ‖z‖ ^ 2 * ‖f z‖ ^ 2 ≤ (12 / π) * ∫ u in ball (0 : ℂ) (2 * ‖z‖), ‖f u‖ ^ 2 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hsub : ball z (‖z‖ / 2) ⊆ ball (0 : ℂ) R \ {0} := by
    intro u hu
    have hd : ‖u - z‖ < ‖z‖ / 2 := by simpa only [mem_ball, dist_eq_norm] using hu
    have ht := norm_add_le (u - z) z
    rw [sub_add_cancel] at ht
    refine ⟨mem_ball_zero_iff.mpr (by linarith), ?_⟩
    intro he
    have hu0 : u = 0 := he
    subst u
    simp only [zero_sub, norm_neg] at hd
    linarith
  have hsmallbig : ball z (‖z‖ / 2) ⊆ ball (0 : ℂ) (2 * ‖z‖) := by
    intro u hu
    have hd : ‖u - z‖ < ‖z‖ / 2 := by simpa only [mem_ball, dist_eq_norm] using hu
    have ht := norm_add_le (u - z) z
    rw [sub_add_cancel] at ht
    exact mem_ball_zero_iff.mpr (by linarith)
  have hbigsub : ball (0 : ℂ) (2 * ‖z‖) ⊆ ball 0 R := ball_subset_ball (by linarith)
  have hcenter := holomorphic_L2_ball_center_bound (by positivity : 0 < ‖z‖ / 2)
    (hf.mono hsub) (hL2.mono_set fun u hu => (hsub hu).1)
  have hmass := setIntegral_mono_set (hL2.mono_set hbigsub)
    (Filter.Eventually.of_forall fun u => sq_nonneg ‖f u‖)
    (Filter.Eventually.of_forall fun u hu => hsmallbig hu)
  have hb := hcenter.trans (mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 3 / π))
  convert mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> ring

/-- Multiplication by the coordinate makes a punctured holomorphic L² function tend to zero. -/
theorem punctured_holomorphic_L2_mul_tendsto_zero {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R \ {0}))
    (hL2 : IntegrableOn (fun z => ‖f z‖ ^ 2) (ball 0 R)) :
    Tendsto (fun z => z * f z) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  have hmass := integrableOn_integral_ball_tendsto_zero hR hL2
  have hrad₀ : Tendsto (fun z : ℂ => 2 * ‖z‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero, mul_zero] using (continuous_norm.const_mul (2 : ℝ)).tendsto (0 : ℂ)
  have hrad : Tendsto (fun z : ℂ => 2 * ‖z‖) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := hrad₀.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun z : ℂ => (12 / π) * ∫ u in ball (0 : ℂ) (2 * ‖z‖), ‖f u‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using (hmass.comp hrad).const_mul (12 / π)
  have hball₀ : ∀ᶠ z : ℂ in 𝓝 0, z ∈ ball 0 (R / 2) := ball_mem_nhds _ (by positivity)
  have hupper : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      ‖z‖ ^ 2 * ‖f z‖ ^ 2 ≤ (12 / π) * ∫ u in ball (0 : ℂ) (2 * ‖z‖), ‖f u‖ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, hball₀.filter_mono nhdsWithin_le_nhds] with z hz0 hzR
    exact punctured_holomorphic_L2_bound hR hf hL2 hz0 (mem_ball_zero_iff.mp hzR)
  have hsq : Tendsto (fun z : ℂ => ‖z‖ ^ 2 * ‖f z‖ ^ 2) (𝓝[≠] 0) (𝓝 (0 : ℝ)) :=
    squeeze_zero' (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hupper hright
  have hsqrt : Tendsto (fun z : ℂ => Real.sqrt (‖z‖ ^ 2 * ‖f z‖ ^ 2)) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have he (z : ℂ) : Real.sqrt (‖z‖ ^ 2 * ‖f z‖ ^ 2) = ‖z * f z‖ := by
    rw [← mul_pow, Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _)), norm_mul]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [he] using hsqrt

/-- The L² removable-singularity criterion used for the exterior case of Lemma 2.1.
The value at the puncture is explicitly replaced by the punctured limit. -/
theorem punctured_holomorphic_L2_removable {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R \ {0}))
    (hL2 : IntegrableOn (fun z => ‖f z‖ ^ 2) (ball 0 R)) :
    DifferentiableOn ℂ (Function.update f 0 (limUnder (𝓝[≠] (0 : ℂ)) f)) (ball 0 R) := by
  have hp := punctured_holomorphic_L2_mul_tendsto_zero hR hf hL2
  have hc₀ : Tendsto (fun z : ℂ => z * f 0) (𝓝 0) (𝓝 0) := by
    simpa only [id_eq, zero_mul] using (continuous_id.mul_const (f 0)).tendsto (0 : ℂ)
  have hc : Tendsto (fun z : ℂ => z * f 0) (𝓝[≠] 0) (𝓝 0) := hc₀.mono_left nhdsWithin_le_nhds
  apply Complex.differentiableOn_update_limUnder_of_isLittleO (ball_mem_nhds _ hR) hf
  have hzero : ∀ z : ℂ, (z - 0)⁻¹ = 0 → f z - f 0 = 0 := by
    intro z hz
    have hz0 : z = 0 := inv_eq_zero.mp (by simpa only [sub_zero] using hz)
    simp only [hz0, sub_self]
  apply (Asymptotics.isLittleO_iff_tendsto hzero).mpr
  simpa only [sub_zero, div_eq_mul_inv, inv_inv, sub_mul, mul_sub, mul_comm, sub_self] using hp.sub hc

/-- Inversion maps the punctured disk conformally onto the exterior disk, for transport of
quadratic differentials in Lemma 2.1 (TT:1366–1396). -/
theorem inversion_puncturedDisk_conformal :
    IsConformalOnto (fun z : ℂ => z⁻¹) (unitDisc \ {0}) unitDiscExterior := by
  have hsub : unitDisc \ {0} ⊆ ({0}ᶜ : Set ℂ) := fun z hz => hz.2
  refine ⟨nx_inv_isConformalOnto.1.mono hsub, nx_inv_isConformalOnto.2.1.mono hsub, ?_⟩
  rw [← resolvent_inv_exterior_image, Set.image_image]
  simp only [Function.comp_def, inv_inv, Set.image_id']

/-- Pullback of a holomorphic exterior quadratic differential is holomorphic off the disk center
(TT:1351–1366). The removable-center step is separate. -/
theorem inverted_quadratic_differentiable {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDiscExterior) :
    DifferentiableOn ℂ (fun z => φ z⁻¹ / z ^ 4) (unitDisc \ {0}) := by
  intro z hz
  have hz0 : z ≠ 0 := hz.2
  have hzinv : z⁻¹ ∈ unitDiscExterior := by
    rw [← inversion_puncturedDisk_conformal.2.2]
    exact ⟨z, hz, rfl⟩
  have hφat := hφ.differentiableAt (resolvent_exterior_isOpen.mem_nhds hzinv)
  exact ((hφat.comp z (differentiableAt_inv hz0)).div (differentiableAt_id.pow 4)
    (pow_ne_zero _ hz0)).differentiableWithinAt

/-- The weighted squared norm of a quadratic differential transforms by the area Jacobian
under inversion (TT:1351–1366). -/
theorem inverted_quadratic_weight {φ : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) :
    ‖φ z⁻¹ / z ^ 4‖ ^ 2 * (rho z)⁻¹ =
      ‖φ z⁻¹‖ ^ 2 * (rho z⁻¹)⁻¹ * ‖deriv (fun w : ℂ => w⁻¹) z‖ ^ 2 := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [(hasDerivAt_inv hz).deriv]
  simp only [norm_div, norm_pow, rho, inv_div, norm_inv, norm_neg]
  field_simp
  <;> ring

/-- The exterior weighted L² condition transports to the punctured disk (TT:1351–1366). -/
theorem A2fun.inverted_integrable_weighted_sq {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDiscExterior) :
    IntegrableOn (fun z => ‖φ z⁻¹ / z ^ 4‖ ^ 2 * (rho z)⁻¹) (unitDisc \ {0}) := by
  have hopen : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hc := inversion_puncturedDisk_conformal
  have hi := ahP_integrableOn_image hopen hc.1 hc.2.1 (fun u => ‖φ u‖ ^ 2 * (rho u)⁻¹)
  rw [hc.2.2] at hi
  apply (hi.mp (A2fun.integrable_weighted_sq resolvent_exterior_isOpen hφ)).congr
  filter_upwards [ae_restrict_mem hopen.measurableSet] with z hz
  simpa only [smul_eq_mul, mul_comm] using (inverted_quadratic_weight (φ := φ) hz.2).symm

/-- Exact weighted area invariance under inversion, before filling the removable center
(TT:1351–1366). -/
theorem inverted_quadratic_weighted_integral (φ : ℂ → ℂ) :
    (∫ z in unitDisc \ {0}, ‖φ z⁻¹ / z ^ 4‖ ^ 2 * (rho z)⁻¹) =
      ∫ u in unitDiscExterior, ‖φ u‖ ^ 2 * (rho u)⁻¹ := by
  have hopen : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hc := inversion_puncturedDisk_conformal
  have hi := ahP_integral_image hopen hc.1 hc.2.1 (fun u => ‖φ u‖ ^ 2 * (rho u)⁻¹)
  rw [hc.2.2] at hi
  rw [hi]
  apply setIntegral_congr_fun hopen.measurableSet
  intro z hz
  simpa only [smul_eq_mul, mul_comm] using inverted_quadratic_weight (φ := φ) hz.2

/-- The sharp constant in Lemma 2.1 follows from the weighted Parseval identity and a convergent
expansion (TT:1374–1396). The Parseval identity itself is an explicit input here. -/
theorem bergman_evaluation_of_parseval (a : ℕ → ℂ) {z v : ℂ} (hz : ‖z‖ < 1)
    (hseries : HasSum (fun n : ℕ =>
      ((((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2) : ℝ) : ℂ) * a n * z ^ n) v)
    (henergy : Summable (fun n : ℕ => (((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2)) * ‖a n‖ ^ 2))
    {N : ℝ} (hN : 0 ≤ N)
    (hparseval : N ^ 2 = π / 2 * (∑' n : ℕ, (((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2)) * ‖a n‖ ^ 2)) :
    (1 - ‖z‖ ^ 2) ^ 2 * ‖v‖ ≤ Real.sqrt (12 / π) * N := by
  have hbase : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hpow : 0 < (1 - ‖z‖ ^ 2) ^ 4 := pow_pos hbase _
  have hs := bergman_series_bound_sq a hz hseries henergy
  have hscaled : (1 - ‖z‖ ^ 2) ^ 4 * ‖v‖ ^ 2 ≤
      6 * (∑' n : ℕ, (((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2)) * ‖a n‖ ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hs hpow.le
    convert hm using 1 <;> field_simp <;> ring
  have henergy_eq :
      6 * (∑' n : ℕ, (((n : ℝ) + 2) ^ 3 - ((n : ℝ) + 2)) * ‖a n‖ ^ 2) = (12 / π) * N ^ 2 := by
    rw [hparseval]
    field_simp
    <;> ring
  rw [henergy_eq] at hscaled
  apply (sq_le_sq₀ (mul_nonneg (sq_nonneg _) (norm_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) hN)).mp
  calc
    ((1 - ‖z‖ ^ 2) ^ 2 * ‖v‖) ^ 2 = (1 - ‖z‖ ^ 2) ^ 4 * ‖v‖ ^ 2 := by ring
    _ ≤ (12 / π) * N ^ 2 := hscaled
    _ = (Real.sqrt (12 / π) * N) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]

/-- Near the puncture, the inverse density is bounded below, so weighted L² implies ordinary L². -/
theorem punctured_weighted_L2_local_integrable {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (unitDisc \ {0}))
    (hw : IntegrableOn (fun z => ‖q z‖ ^ 2 * (rho z)⁻¹) (unitDisc \ {0})) :
    IntegrableOn (fun z => ‖q z‖ ^ 2) (ball (0 : ℂ) (1 / 2)) := by
  have hsub : ball (0 : ℂ) (1 / 2) ⊆ unitDisc := ball_subset_ball (by norm_num)
  have hnull : unitDisc \ {0} =ᵐ[volume] unitDisc := sdiff_null_ae_eq_self (measure_singleton (0 : ℂ))
  have hwfull : IntegrableOn (fun z => ‖q z‖ ^ 2 * (rho z)⁻¹) unitDisc := hw.congr_set_ae hnull.symm
  have hwlocal := hwfull.mono_set hsub
  have hm : AEStronglyMeasurable (fun z => ‖q z‖ ^ 2)
      (volume.restrict (ball (0 : ℂ) (1 / 2) \ {0})) :=
    ((hq.mono (sdiff_subset_sdiff_left hsub)).continuousOn.norm.pow 2).aestronglyMeasurable
      (isOpen_ball.sdiff isClosed_singleton).measurableSet
  have hbnull : ball (0 : ℂ) (1 / 2) \ {0} =ᵐ[volume] ball 0 (1 / 2) :=
    sdiff_null_ae_eq_self (measure_singleton (0 : ℂ))
  rw [Measure.restrict_congr_set hbnull] at hm
  apply (hwlocal.const_mul (16 : ℝ)).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have hzN : ‖z‖ < 1 / 2 := by simpa only [mem_ball, dist_zero_right] using hz
  have hb : (1 / 2 : ℝ) ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hb 2
  have hlo : (1 / 16 : ℝ) ≤ (rho z)⁻¹ := by
    simp only [rho, inv_div]
    nlinarith only [hs]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    ‖q z‖ ^ 2 = 16 * (‖q z‖ ^ 2 * (1 / 16)) := by ring
    _ ≤ 16 * (‖q z‖ ^ 2 * (rho z)⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlo (sq_nonneg _)) (by norm_num)

/-- A holomorphic weighted-L² function on the punctured disk extends to `A₂` on the disk
without changing its weighted area integral (TT:1351–1366). -/
theorem exists_A2_extension_punctured {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (unitDisc \ {0}))
    (hw : IntegrableOn (fun z => ‖q z‖ ^ 2 * (rho z)⁻¹) (unitDisc \ {0})) :
    ∃ ψ : ℂ → ℂ, ψ ∈ A2fun unitDisc ∧ EqOn ψ q (unitDisc \ {0}) ∧
      (∫ z in unitDisc, ‖ψ z‖ ^ 2 * (rho z)⁻¹) =
        ∫ z in unitDisc \ {0}, ‖q z‖ ^ 2 * (rho z)⁻¹ := by
  let ψ := Function.update q 0 (limUnder (𝓝[≠] (0 : ℂ)) q)
  have hsub : ball (0 : ℂ) (1 / 2) ⊆ unitDisc := ball_subset_ball (by norm_num)
  have hlocal : DifferentiableOn ℂ ψ (ball 0 (1 / 2)) :=
    punctured_holomorphic_L2_removable (by norm_num) (hq.mono (sdiff_subset_sdiff_left hsub))
      (punctured_weighted_L2_local_integrable hq hw)
  have heq : EqOn ψ q (unitDisc \ {0}) := by
    intro z hz
    simp only [ψ, Function.update_of_ne hz.2]
  have hψ : DifferentiableOn ℂ ψ unitDisc :=
    (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))).mp
      ⟨hq.congr heq, hlocal.continuousOn.continuousAt (ball_mem_nhds _ (by norm_num))⟩
  have hae : ψ =ᵐ[volume.restrict unitDisc] q := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    simp only [ψ, Function.update_of_ne hz]
  have hnull : unitDisc \ {0} =ᵐ[volume] unitDisc := sdiff_null_ae_eq_self (measure_singleton (0 : ℂ))
  have hwfull : IntegrableOn (fun z => ‖q z‖ ^ 2 * (rho z)⁻¹) unitDisc := hw.congr_set_ae hnull.symm
  have hψInt : IntegrableOn (fun z => ‖ψ z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
    apply hwfull.congr
    filter_upwards [hae] with z hz
    simp only [hz]
  refine ⟨ψ, ⟨hψ, normA2_lt_top_of_integrable_weighted_sq hψInt⟩, heq, ?_⟩
  calc
    _ = ∫ z in unitDisc, ‖q z‖ ^ 2 * (rho z)⁻¹ := by
      apply integral_congr_ae
      filter_upwards [hae] with z hz
      rw [hz]
    _ = _ := setIntegral_congr_set hnull.symm

/-- Inversion gives an `A₂` disk representative with exactly the exterior norm (TT:1351–1366). -/
theorem exists_inverted_A2 {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDiscExterior) :
    ∃ ψ : ℂ → ℂ, ψ ∈ A2fun unitDisc ∧
      EqOn ψ (fun z => φ z⁻¹ / z ^ 4) (unitDisc \ {0}) ∧
      normA2 unitDisc ψ = normA2 unitDiscExterior φ := by
  obtain ⟨ψ, hψ, heq, harea⟩ := exists_A2_extension_punctured
    (inverted_quadratic_differentiable hφ.1) (A2fun.inverted_integrable_weighted_sq hφ)
  refine ⟨ψ, hψ, heq, ?_⟩
  apply (ENNReal.strictMono_rpow_of_pos (by norm_num : (0 : ℝ) < 2)).injective
  simp only [ENNReal.rpow_two]
  rw [A2fun.normA2_sq (D := unitDisc) isOpen_ball hψ,
    A2fun.normA2_sq (D := unitDiscExterior) resolvent_exterior_isOpen hφ,
    harea, inverted_quadratic_weighted_integral]

/-- The exterior case of Lemma 2.1, including the removable-center and norm-transport steps
(TT:1366–1396). -/
theorem lemma_2_1_exterior {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDiscExterior) :
    ∀ z ∈ unitDiscExterior, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖) ≤
      ENNReal.ofReal (Real.sqrt (12 / π)) * normA2 unitDiscExterior φ := by
  obtain ⟨ψ, hψ, heq, hnorm⟩ := exists_inverted_A2 hφ
  intro z hz
  have hz0 := resolvent_exterior_ne_zero hz
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hw : z⁻¹ ∈ unitDisc \ {0} := by
    rw [← resolvent_inv_exterior_image]
    exact ⟨z, hz, rfl⟩
  have hb := lemma_2_1_disc hψ z⁻¹ hw.1
  rw [heq hw] at hb
  dsimp only at hb
  rw [inv_inv, hnorm] at hb
  have hweight : (1 - ‖z⁻¹‖ ^ 2) ^ 2 * ‖φ z / (z⁻¹) ^ 4‖ =
      (1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖ := by
    simp only [norm_inv, norm_div, norm_pow]
    field_simp
    <;> ring
  rw [hweight] at hb
  exact hb

/-- **Lemma 2.1** (TT:1366–1396). `A₂(D) ⊂ A∞(D)` for `D = 𝔻, 𝔻*`, and the inclusion is bounded:
`‖φ‖∞ = sup_D |(1 - |z|²)² φ| ≤ √(12/π) ‖φ‖₂`. -/
theorem lemma_2_1 {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior) {φ : ℂ → ℂ} (hφ : φ ∈ A2fun D) :
    ∀ z ∈ D, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖) ≤ ENNReal.ofReal (Real.sqrt (12 / π)) * normA2 D φ := by
  rcases hD with rfl | rfl
  · exact lemma_2_1_disc hφ
  · exact lemma_2_1_exterior hφ

/-- Subtraction respects the chosen holomorphic representatives. -/
theorem A2.toFun_sub {D : Set ℂ} (hD : IsOpen D) (hcircle : ∀ z ∈ D, ‖z‖ ≠ 1)
    (φ ψ : A2 D) : EqOn (A2.toFun (φ - ψ)) (A2.toFun φ - A2.toFun ψ) D := by
  apply A2.toFun_eqOn hD hcircle
  · exact (A2.toFun_spec φ).1.sub (A2.toFun_spec ψ).1
  · exact (Lp.coeFn_sub _ _).trans ((A2.toFun_spec φ).2.sub (A2.toFun_spec ψ).2)

/-- The real-valued point-evaluation estimate for the actual Hilbert subspace. -/
theorem A2.weighted_pointwise_bound {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    (φ : A2 D) {z : ℂ} (hz : z ∈ D) :
    (1 - ‖z‖ ^ 2) ^ 2 * ‖A2.toFun φ z‖ ≤ Real.sqrt (12 / π) * ‖φ‖ := by
  have hb := lemma_2_1 hD (A2.toFun_mem φ) z hz
  rw [A2.norm_toFun] at hb
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ofReal_norm, enorm_eq_nnnorm] using hb

/-- Hilbert-Cauchy sequences are uniformly Cauchy wherever the evaluation weight has a positive lower bound. -/
theorem A2.uniformCauchySeqOn_of_weight_lower_bound {D S : Set ℂ}
    (hD : D = unitDisc ∨ D = unitDiscExterior) (hS : S ⊆ D) {a : ℝ} (ha : 0 < a)
    (hweight : ∀ z ∈ S, a ≤ (1 - ‖z‖ ^ 2) ^ 2)
    {v : ℕ → A2 D} (hv : CauchySeq v) : UniformCauchySeqOn (fun n => A2.toFun (v n)) atTop S := by
  have hopen : IsOpen D := by rcases hD with rfl | rfl; exact isOpen_ball; exact resolvent_exterior_isOpen
  have hcircle : ∀ z ∈ D, ‖z‖ ≠ 1 := by
    rcases hD with rfl | rfl
    · intro z hz; exact ne_of_lt (mem_ball_zero_iff.mp hz)
    · intro z hz; exact ne_of_gt hz
  let C : ℝ := Real.sqrt (12 / π) / a
  have hC : 0 < C := div_pos (Real.sqrt_pos.mpr (by positivity)) ha
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hv (ε / C) (div_pos hε hC)
  refine ⟨N, ?_⟩
  intro m hm n hn z hz
  have hb := A2.weighted_pointwise_bound hD (v m - v n) (hS hz)
  rw [A2.toFun_sub hopen hcircle (v m) (v n) (hS hz)] at hb
  simp only [Pi.sub_apply] at hb
  have hlo := mul_le_mul_of_nonneg_right (hweight z hz) (norm_nonneg (A2.toFun (v m) z - A2.toFun (v n) z))
  have hnorm : ‖A2.toFun (v m) z - A2.toFun (v n) z‖ ≤ C * ‖v m - v n‖ := by
    have hh : ‖A2.toFun (v m) z - A2.toFun (v n) z‖ * a ≤ Real.sqrt (12 / π) * ‖v m - v n‖ := by
      simpa only [mul_comm a] using hlo.trans hb
    convert (le_div_iff₀ ha).mpr hh using 1 <;> dsimp [C] <;> ring
  rw [dist_eq_norm]
  apply hnorm.trans_lt
  have hsmall := (mul_lt_mul_of_pos_left (hN m hm n hn) hC)
  rw [dist_eq_norm] at hsmall
  simpa only [mul_div_cancel₀ _ hC.ne'] using hsmall

/-- Hilbert-Cauchy sequences have a locally uniform holomorphic limit on either disk model. -/
theorem A2.exists_locally_uniform_limit {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {v : ℕ → A2 D} (hv : CauchySeq v) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f D ∧
      TendstoLocallyUniformlyOn (fun n => A2.toFun (v n)) f atTop D := by
  have hopen : IsOpen D := by rcases hD with rfl | rfl; exact isOpen_ball; exact resolvent_exterior_isOpen
  have hcircle : ∀ z ∈ D, ‖z‖ ≠ 1 := by
    rcases hD with rfl | rfl
    · intro z hz; exact ne_of_lt (mem_ball_zero_iff.mp hz)
    · intro z hz; exact ne_of_gt hz
  let w : ℂ → ℝ := fun z => (1 - ‖z‖ ^ 2) ^ 2
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hwpos (z : ℂ) (hz : z ∈ D) : 0 < w z := by
    apply sq_pos_of_ne_zero
    intro he
    exact hcircle z hz (by nlinarith [norm_nonneg z])
  let f : ℂ → ℂ := fun z => limUnder atTop (fun n => A2.toFun (v n) z)
  have hpoint (z : ℂ) (hz : z ∈ D) : Tendsto (fun n => A2.toFun (v n) z) atTop (𝓝 (f z)) := by
    have hsingle : ({z} : Set ℂ) ⊆ D := singleton_subset_iff.mpr hz
    have huc := A2.uniformCauchySeqOn_of_weight_lower_bound hD hsingle (hwpos z hz)
      (by intro u hu; rcases mem_singleton_iff.mp hu with rfl; exact le_rfl) hv
    exact (huc.cauchySeq (mem_singleton z)).tendsto_limUnder
  have hlocal : TendstoLocallyUniformlyOn (fun n => A2.toFun (v n)) f atTop D := by
    intro U hU z hz
    let S : Set ℂ := D ∩ {u : ℂ | w z / 2 < w u}
    have hSopen : IsOpen S := hopen.inter (isOpen_lt continuous_const hw)
    have hzS : z ∈ S := ⟨hz, by change w z / 2 < w z; linarith [hwpos z hz]⟩
    have huc := A2.uniformCauchySeqOn_of_weight_lower_bound hD (show S ⊆ D from inter_subset_left)
      (div_pos (hwpos z hz) (by norm_num)) (fun u hu => hu.2.le) hv
    have huni : TendstoUniformlyOn (fun n => A2.toFun (v n)) f atTop S :=
      huc.tendstoUniformlyOn_of_tendsto (fun u hu => hpoint u hu.1)
    exact ⟨S, mem_nhdsWithin_of_mem_nhds (hSopen.mem_nhds hzS), huni U hU⟩
  exact ⟨f, hlocal.differentiableOn (Filter.Eventually.of_forall fun n => (A2.toFun_spec (v n)).1) hopen, hlocal⟩

/-- The actual `A₂` subspace is closed in its weighted L² ambient space. -/
theorem A2.isClosed {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior) :
    IsClosed (A2 D : Set (Lp ℂ 2 (rhoInvMeasure D))) := by
  apply IsSeqClosed.isClosed
  intro u g hu hlim
  let v : ℕ → A2 D := fun n => ⟨u n, hu n⟩
  have hv : CauchySeq v := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq ε hε
    exact ⟨N, hN⟩
  obtain ⟨f, hf, hlocal⟩ := A2.exists_locally_uniform_limit hD hv
  obtain ⟨ns, hns, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hrep : ∀ᵐ z ∂rhoInvMeasure D, ∀ n : ℕ, u n z = A2.toFun (v n) z :=
    ae_all_iff.mpr (fun n => (A2.toFun_spec (v n)).2)
  have hmeas : MeasurableSet D := by
    rcases hD with rfl | rfl
    · exact measurableSet_ball
    · exact resolvent_exterior_isOpen.measurableSet
  have hDae : ∀ᵐ z ∂rhoInvMeasure D, z ∈ D :=
    (ae_restrict_mem hmeas).filter_mono (withDensity_absolutelyContinuous (volume.restrict D) _).ae_le
  apply (mem_A2_iff D g).mpr
  refine ⟨f, hf, ?_⟩
  filter_upwards [hAE, hrep, hDae] with z hlimz hzrep hzD
  have hpoint := (hlocal.tendsto_at hzD).comp hns.tendsto_atTop
  have he : (fun n => u (ns n) z) = (fun n => A2.toFun (v (ns n)) z) := funext fun n => hzrep (ns n)
  rw [he] at hlimz
  exact tendsto_nhds_unique hlimz hpoint

/-- Completeness of the Hilbert subspace in either disk model. -/
theorem A2.completeSpace {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior) :
    CompleteSpace (A2 D) := (A2.isClosed hD).isComplete.completeSpace_coe

instance A2.instCompleteSpaceDisk : CompleteSpace (A2 unitDisc) :=
  A2.completeSpace (Or.inl rfl)

instance A2.instCompleteSpaceExterior : CompleteSpace (A2 unitDiscExterior) :=
  A2.completeSpace (Or.inr rfl)

/-- The pointwise estimate in Lemma 2.1 implies bounded linearity of the actual choice-defined inclusion
(TT:1366–1396). This separates the analytic evaluation estimate from the function-space constructions. -/
theorem A2toAInf_bounded_of_pointwise_bound {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : A2 unitDisc, ∀ z ∈ unitDisc,
      ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * A2.toFun φ z‖ ≤ C * ‖φ‖) :
    (∀ (a : ℂ) (φ ψ : A2 unitDisc), A2toAInf (a • φ + ψ) = a • A2toAInf φ + A2toAInf ψ) ∧
      ∀ φ, ‖A2toAInf φ‖ ≤ C * ‖φ‖ ∧ ∀ z ∈ unitDisc, AInf.toFun (A2toAInf φ) z = A2.toFun φ z := by
  have hcircle : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := by
    intro z hz
    exact ne_of_lt (by simpa only [unitDisc, mem_ball, dist_zero_right] using hz)
  have hs (φ : A2 unitDisc) : EqOn (AInf.toFun (A2toAInf φ)) (A2.toFun φ) unitDisc ∧
      ‖A2toAInf φ‖ ≤ C * ‖φ‖ :=
    toAInf_spec_of_bound hcircle (A2.toFun_spec φ).1 (mul_nonneg hC (norm_nonneg _)) (hbound φ)
  constructor
  · intro a φ ψ
    apply AInf.ext_of_toFun_eqOn hcircle
    intro z hz
    calc
      AInf.toFun (A2toAInf (a • φ + ψ)) z = A2.toFun (a • φ + ψ) z := (hs _).1 hz
      _ = a • A2.toFun φ z + A2.toFun ψ z := by
        have hadd := A2.toFun_add (D := unitDisc) isOpen_ball hcircle (a • φ) ψ hz
        have hsmul := A2.toFun_smul (D := unitDisc) isOpen_ball hcircle a φ hz
        simpa only [Pi.add_apply, Pi.smul_apply, hsmul] using hadd
      _ = a • AInf.toFun (A2toAInf φ) z + AInf.toFun (A2toAInf ψ) z := by
        rw [(hs φ).1 hz, (hs ψ).1 hz]
      _ = AInf.toFun (a • A2toAInf φ + A2toAInf ψ) z := by
        simp only [AInf.toFun, Submodule.coe_add, Submodule.coe_smul, unweight_add,
          unweight_smul, Pi.add_apply, Pi.smul_apply]
  · intro φ
    exact ⟨(hs φ).2, fun z hz => (hs φ).1 hz⟩

/-- (TT:1366) The inclusion `A₂(𝔻) → A∞(𝔻)` is a bounded linear map of Banach spaces. -/
theorem A2toAInf_bounded :
    (∀ (a : ℂ) (φ ψ : A2 unitDisc), A2toAInf (a • φ + ψ) = a • A2toAInf φ + A2toAInf ψ) ∧
      ∀ φ, ‖A2toAInf φ‖ ≤ Real.sqrt (12 / π) * ‖φ‖ ∧ ∀ z ∈ unitDisc, AInf.toFun (A2toAInf φ) z = A2.toFun φ z := by
  apply A2toAInf_bounded_of_pointwise_bound (Real.sqrt_nonneg _)
  intro φ z hz
  have h := lemma_2_1_disc (A2.toFun_mem φ) z hz
  rw [A2.norm_toFun] at h
  have hreal : (1 - ‖z‖ ^ 2) ^ 2 * ‖A2.toFun φ z‖ ≤ Real.sqrt (12 / π) * ‖φ‖ := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ofReal_norm, enorm_eq_nnnorm] using h
  have hcast : (1 - (‖z‖ : ℂ) ^ 2) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  simpa only [norm_mul, norm_pow, hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hreal

/-- The choice-defined inclusion sends zero to zero. -/
theorem A2toAInf_zero : A2toAInf 0 = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa only [norm_zero, mul_zero] using (A2toAInf_bounded.2 0).1) (norm_nonneg _)

/-- The inclusion of Lemma 2.1 as an actual continuous complex-linear map. -/
def A2toAInfCLM : A2 unitDisc →L[ℂ] AInf unitDisc :=
  LinearMap.mkContinuous
    { toFun := A2toAInf
      map_add' := fun φ ψ => by simpa only [one_smul] using A2toAInf_bounded.1 1 φ ψ
      map_smul' := fun c φ => by
        simpa only [add_zero, A2toAInf_zero, smul_zero, RingHom.id_apply] using A2toAInf_bounded.1 c φ 0 }
    (Real.sqrt (12 / π)) (fun φ => (A2toAInf_bounded.2 φ).1)

@[simp] theorem A2toAInfCLM_apply (φ : A2 unitDisc) : A2toAInfCLM φ = A2toAInf φ := rfl

/-- The Hilbert-to-Bers inclusion is injective because its representatives agree pointwise. -/
theorem A2toAInf_injective : Function.Injective A2toAInf := by
  intro φ ψ he
  apply A2.ext_of_toFun_eqOn (D := unitDisc) measurableSet_ball
  intro z hz
  rw [← (A2toAInf_bounded.2 φ).2 z hz, ← (A2toAInf_bounded.2 ψ).2 z hz, he]

/-- The range of the inclusion is exactly the weighted-L² locus in Bers function space. -/
theorem A2toAInf_range : range A2toAInf = {φ : AInf unitDisc | AInf.toFun φ ∈ A2fun unitDisc} := by
  have hcircle : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun z hz => ne_of_lt (mem_ball_zero_iff.mp hz)
  ext φ
  constructor
  · rintro ⟨ψ, rfl⟩
    have he : EqOn (AInf.toFun (A2toAInf ψ)) (A2.toFun ψ) unitDisc := fun z hz =>
      (A2toAInf_bounded.2 ψ).2 z hz
    refine ⟨(A2.toFun_spec ψ).1.congr he, ?_⟩
    rw [normA2_congr (D := unitDisc) measurableSet_ball he]
    exact (A2.toFun_mem ψ).2
  · intro hφ
    refine ⟨toA2 unitDisc (AInf.toFun φ), ?_⟩
    apply AInf.ext_of_toFun_eqOn hcircle
    intro z hz
    rw [(A2toAInf_bounded.2 _).2 z hz]
    exact toA2_spec isOpen_ball hcircle hφ hz

/-- The inclusion is complex differentiable everywhere, with its own constant derivative. -/
theorem A2toAInf_hasFDerivAt (φ : A2 unitDisc) : HasFDerivAt A2toAInf A2toAInfCLM φ :=
  A2toAInfCLM.hasFDerivAt

/-- The Hilbert space `H^{-1,1}(D)` of harmonic Beltrami differentials (TT:1401, TT:1407), as a set of functions:
`μ = ρ⁻¹ φ̄` on `D` with `φ` holomorphic on `D`, and `‖μ‖₂² = ∬_D |μ|² ρ d²z < ∞`. -/
def harmonicL2 (D : Set ℂ) : Set (ℂ → ℂ) :=
  {μ | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ D ∧ (∀ z ∈ D, μ z = (rho z : ℂ)⁻¹ * conj (φ z)) ∧ normL2 D μ < ∞}

/-- Harmonic contraction identifies the quadratic-differential and Beltrami L² norms
(TT:1401–1410). -/
theorem normA2_eq_normL2_of_harmonic {D : Set ℂ} (hD : MeasurableSet D)
    (hcircle : ∀ z ∈ D, ‖z‖ ≠ 1) {μ φ : ℂ → ℂ}
    (hrep : ∀ z ∈ D, μ z = (rho z : ℂ)⁻¹ * conj (φ z)) : normA2 D φ = normL2 D μ := by
  unfold normA2 normL2
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hD] with z hz
  have hr := rho_pos_of_norm_ne_one (hcircle z hz)
  have hn : ‖μ z‖ = (rho z)⁻¹ * ‖φ z‖ := by
    rw [hrep z hz]
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_conj]
  have hreal : ‖φ z‖ ^ 2 * (rho z)⁻¹ = ‖μ z‖ ^ 2 * rho z := by
    rw [hn]
    field_simp [hr.ne']
    <;> ring
  have he := congrArg ENNReal.ofReal hreal
  simpa only [ENNReal.ofReal_mul (sq_nonneg ‖φ z‖), ENNReal.ofReal_mul (sq_nonneg ‖μ z‖),
    ENNReal.ofReal_pow (norm_nonneg (φ z)), ENNReal.ofReal_pow (norm_nonneg (μ z)),
    ofReal_norm, enorm_eq_nnnorm] using he

/-- (TT:1410) The inclusion `H^{-1,1}(𝔻*) ↪ Ω^{-1,1}(𝔻*)` is bounded: `μ ∈ H^{-1,1}(𝔻*)` lies in `Ω^{-1,1}(𝔻*)`
with `‖μ‖∞ ≤ C ‖μ‖₂`. -/
theorem harmonicL2_subset_harmonic :
    ∃ C : ℝ, ∀ μ ∈ harmonicL2 unitDiscExterior, toLinf μ ∈ harmonicBeltrami ∧
      ENNReal.ofReal ‖toLinf μ‖ ≤ ENNReal.ofReal C * normL2 unitDiscExterior μ := by
  refine ⟨Real.sqrt (12 / π) / 4, ?_⟩
  intro μ hμ
  obtain ⟨φ, hφ, hrep, hfinite⟩ := hμ
  have hcircle : ∀ z ∈ unitDiscExterior, ‖z‖ ≠ 1 := fun z hz => ne_of_gt hz
  have hnorm := normA2_eq_normL2_of_harmonic resolvent_exterior_isOpen.measurableSet hcircle hrep
  have hA2 : φ ∈ A2fun unitDiscExterior := by
    refine ⟨hφ, ?_⟩
    rw [hnorm]
    exact hfinite
  let N : ℝ := (normL2 unitDiscExterior μ).toReal
  let K : ℝ := (Real.sqrt (12 / π) / 4) * N
  have hpoint (z : ℂ) (hz : z ∈ unitDiscExterior) :
      (1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖ ≤ Real.sqrt (12 / π) * N := by
    have hb := lemma_2_1 (D := unitDiscExterior) (Or.inr rfl) hA2 z hz
    rw [hnorm] at hb
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg)).mp
    simpa only [ENNReal.ofReal_mul (Real.sqrt_nonneg _), N, ENNReal.ofReal_toReal hfinite.ne] using hb
  have hbound (z : ℂ) (hz : z ∈ unitDiscExterior) :
      ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * φ z‖ ≤ Real.sqrt (12 / π) * N := by
    have hcast : (1 - (‖z‖ : ℂ) ^ 2) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    simpa only [norm_mul, norm_pow, hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hpoint z hz
  obtain ⟨φI, hI, hInorm⟩ := exists_AInf_representative_of_bound hcircle hφ
    (mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg) hbound
  let φJ : AInf unitDiscExterior := (1 / 4 : ℂ) • φI
  have hJ (z : ℂ) (hz : z ∈ unitDiscExterior) : AInf.toFun φJ z = (1 / 4 : ℂ) * φ z := by
    simp only [φJ, AInf.toFun, Submodule.coe_smul, unweight_smul, Pi.smul_apply, smul_eq_mul]
    change (1 / 4 : ℂ) * AInf.toFun φI z = (1 / 4 : ℂ) * φ z
    rw [hI hz]
  have hμbound (z : ℂ) (hz : z ∈ unitDiscExterior) : ‖μ z‖ ≤ K := by
    have hr := rho_pos_of_norm_ne_one (hcircle z hz)
    have hformula : ‖μ z‖ = ((1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖) / 4 := by
      rw [hrep z hz]
      simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_conj]
      simp only [rho, inv_div]
      ring
    rw [hformula]
    calc
      _ ≤ (Real.sqrt (12 / π) * N) / 4 := div_le_div_of_nonneg_right (hpoint z hz) (by norm_num)
      _ = K := by dsimp [K]; ring
  have hwc : Continuous (fun z : ℂ => (rho z : ℂ)⁻¹) := by
    simp only [← Complex.ofReal_inv, rho, inv_div]
    fun_prop
  have hφc := hφ.continuousOn
  have hc : ContinuousOn (fun z => (rho z : ℂ)⁻¹ * conj (φ z)) unitDiscExterior := by
    simpa only [Pi.mul_def, Function.comp_def] using
      hwc.continuousOn.mul (Complex.continuous_conj.comp_continuousOn hφc)
  have hμc : ContinuousOn μ unitDiscExterior := hc.congr (by intro z hz; exact hrep z hz)
  have hμae : AEStronglyMeasurable μ (volume.restrict unitDiscExterior) :=
    hμc.aestronglyMeasurable resolvent_exterior_isOpen.measurableSet
  have hμboundae : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖μ z‖ ≤ K := by
    filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz
    exact hμbound z hz
  have hmem : MemLp μ ∞ (volume.restrict unitDiscExterior) := memLp_top_of_bound hμae K hμboundae
  have hto : (toLinf μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] μ := by
    simp only [toLinf, dite_eq_left hmem]
    exact hmem.coeFn_toLp
  constructor
  · apply Submodule.subset_span
    refine ⟨φJ, ?_⟩
    filter_upwards [hto, ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z htoz hz
    rw [htoz, hrep z hz, hJ z hz]
    simp only [map_mul, map_div₀, map_one, map_ofNat, rho]
    push_cast
    rw [inv_div]
    ring
  · calc
      ENNReal.ofReal ‖toLinf μ‖ = eLpNorm μ ∞ (volume.restrict unitDiscExterior) := by
        rw [ofReal_norm, Lp.enorm_def, eLpNorm_congr_ae hto]
      _ ≤ ENNReal.ofReal K := by
        rw [eLpNorm_exponent_top hμae]
        exact eLpNormEssSup_le_of_ae_bound hμboundae
      _ = _ := by
        dsimp [K, N]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfinite.ne]

-- `D0bers_harmonicL2` moved to `Ch1/HarmonicL2Bers.lean` (2026-10-25).

/-- Integrable mass on the disk tends to zero on shrinking boundary collars. -/
theorem integrableOn_disk_tail_tendsto_zero {F : ℂ → ℝ} (hF : IntegrableOn F unitDisc) :
    Tendsto (fun r : ℝ => ∫ z in unitDisc ∩ {z : ℂ | r < ‖z‖}, F z) (𝓝 1) (𝓝 0) := by
  let H : ℂ → ℝ := unitDisc.indicator F
  have hH : Integrable H := hF.integrable_indicator measurableSet_ball
  have hmeas (r : ℝ) : MeasurableSet {z : ℂ | r < ‖z‖} := isOpen_lt continuous_const continuous_norm |>.measurableSet
  have hlim : ∀ᵐ z : ℂ, Tendsto (fun r : ℝ => ({z : ℂ | r < ‖z‖}).indicator H z) (𝓝 1) (𝓝 (0 : ℝ)) := by
    apply ae_of_all
    intro z
    by_cases hz : z ∈ unitDisc
    · have hzN : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioi_mem_nhds hzN] with r hr
      change ‖z‖ < r at hr
      exact (indicator_of_notMem (by exact not_lt.mpr hr.le) H).symm
    · have hzero : H z = 0 := indicator_of_notMem hz F
      simp only [indicator_apply, hzero, ite_self]
      exact tendsto_const_nhds
  have ht := tendsto_integral_filter_of_dominated_convergence (fun z => ‖H z‖)
    (Filter.Eventually.of_forall fun r : ℝ => hH.aestronglyMeasurable.indicator (hmeas r))
    (Filter.Eventually.of_forall fun _ => ae_of_all volume fun z => norm_indicator_le_norm_self H z)
    hH.norm hlim
  have he (r : ℝ) : (∫ z : ℂ, ({z : ℂ | r < ‖z‖}).indicator H z) =
      ∫ z in unitDisc ∩ {z : ℂ | r < ‖z‖}, F z := by
    rw [show ({z : ℂ | r < ‖z‖}).indicator H = (unitDisc ∩ {z : ℂ | r < ‖z‖}).indicator F by
      ext z; simp only [H, indicator_apply, mem_inter_iff]; split_ifs <;> simp_all]
    exact integral_indicator (measurableSet_ball.inter (hmeas r))
  simpa only [he, integral_zero] using ht

/-- A weighted L² holomorphic function is controlled by its mass near the boundary. -/
theorem A2fun.disk_boundary_mass_bound {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ((1 - ‖z‖ ^ 2) ^ 2 * ‖f z‖) ^ 2 ≤ (3072 / π) *
      ∫ u in unitDisc ∩ {u : ℂ | 2 * ‖z‖ - 1 < ‖u‖}, ‖f u‖ ^ 2 * (rho u)⁻¹ := by
  let δ : ℝ := 1 - ‖z‖
  let W : ℂ → ℝ := fun u => ‖f u‖ ^ 2 * (rho u)⁻¹
  have hzN : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hδ : 0 < δ := sub_pos.mpr hzN
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hW : IntegrableOn W unitDisc := A2fun.integrable_weighted_sq isOpen_ball hf
  have hWpos (u : ℂ) : 0 ≤ W u := by dsimp [W, rho]; positivity
  have hsub : ball z (δ / 2) ⊆ unitDisc := by
    intro u hu
    have hd : ‖u - z‖ < δ / 2 := by simpa only [mem_ball, dist_eq_norm] using hu
    have ht := norm_add_le (u - z) z
    rw [sub_add_cancel] at ht
    exact mem_ball_zero_iff.mpr (by dsimp [δ] at hd; linarith)
  have hlo (u : ℂ) (hu : u ∈ ball z (δ / 2)) : δ ^ 2 / 16 ≤ (rho u)⁻¹ := by
    have huN : ‖u‖ < 1 := mem_ball_zero_iff.mp (hsub hu)
    have hd : ‖u - z‖ < δ / 2 := by simpa only [mem_ball, dist_eq_norm] using hu
    have ht := norm_add_le (u - z) z
    rw [sub_add_cancel] at ht
    have ha : δ / 2 ≤ 1 - ‖u‖ ^ 2 := by
      have hp := mul_nonneg (norm_nonneg u) (sub_nonneg.mpr huN.le)
      dsimp [δ] at hd ⊢
      nlinarith
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ δ / 2) ha 2
    simp only [rho, inv_div]
    nlinarith only [hs]
  have hb (u : ℂ) (hu : u ∈ ball z (δ / 2)) : ‖f u‖ ^ 2 ≤ (16 / δ ^ 2) * W u := by
    have hm := mul_le_mul_of_nonneg_left (hlo u hu) (sq_nonneg ‖f u‖)
    convert (show ‖f u‖ ^ 2 ≤ (16 * W u) / δ ^ 2 from
      (le_div_iff₀ hδsq).mpr (by dsimp [W]; nlinarith only [hm])) using 1 <;> field_simp <;> ring
  have hwlocal := hW.mono_set hsub
  have hL2 : IntegrableOn (fun u => ‖f u‖ ^ 2) (ball z (δ / 2)) := by
    apply (hwlocal.const_mul (16 / δ ^ 2)).mono'
      (((hf.1.mono hsub).continuousOn.norm.pow 2).aestronglyMeasurable measurableSet_ball)
    filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f u‖)] using hb u hu
  have hmass : (∫ u in ball z (δ / 2), ‖f u‖ ^ 2) ≤
      (16 / δ ^ 2) * ∫ u in ball z (δ / 2), W u := by
    rw [← integral_const_mul]
    apply integral_mono_ae hL2 (hwlocal.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
    exact hb u hu
  have hcenter := holomorphic_L2_ball_center_bound (by positivity : 0 < δ / 2) (hf.1.mono hsub) hL2
  have hcenter' := hcenter.trans (mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 3 / π))
  have hscaled : δ ^ 4 * ‖f z‖ ^ 2 ≤ (192 / π) * ∫ u in ball z (δ / 2), W u := by
    have hm := mul_le_mul_of_nonneg_left hcenter' (by positivity : 0 ≤ 4 * δ ^ 2)
    convert hm using 1 <;> field_simp <;> ring
  have htail : ball z (δ / 2) ⊆ unitDisc ∩ {u : ℂ | 2 * ‖z‖ - 1 < ‖u‖} := by
    intro u hu
    refine ⟨hsub hu, ?_⟩
    have hd : ‖u - z‖ < δ / 2 := by simpa only [mem_ball, dist_eq_norm] using hu
    have ht := norm_sub_le z u
    have ht' := norm_add_le (z - u) u
    rw [sub_add_cancel, norm_sub_rev] at ht'
    dsimp [δ] at hd
    change 2 * ‖z‖ - 1 < ‖u‖
    linarith
  have htailmass := setIntegral_mono_set (hW.mono_set inter_subset_left)
    (Filter.Eventually.of_forall hWpos) (Filter.Eventually.of_forall fun u hu => htail hu)
  have hp : (1 + ‖z‖) ^ 4 ≤ (2 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  calc
    _ = (1 + ‖z‖) ^ 4 * (δ ^ 4 * ‖f z‖ ^ 2) := by dsimp [δ]; ring
    _ ≤ 16 * (δ ^ 4 * ‖f z‖ ^ 2) := by
      convert mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ δ ^ 4 * ‖f z‖ ^ 2) using 1 <;> norm_num
    _ ≤ 16 * ((192 / π) * ∫ u in ball z (δ / 2), W u) := mul_le_mul_of_nonneg_left hscaled (by norm_num)
    _ = (3072 / π) * ∫ u in ball z (δ / 2), W u := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htailmass (by positivity)

/-- The weighted value of a disk A₂ differential tends to zero at the unit circle. -/
theorem A2fun.disk_weighted_tendsto_zero {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) :
    Tendsto (fun z => (1 - ‖z‖ ^ 2) ^ 2 * ‖f z‖)
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0) := by
  let L := comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc
  have hn : Tendsto (fun z : ℂ => ‖z‖) L (𝓝 1) := tendsto_comap.mono_left inf_le_left
  have hD : ∀ᶠ z in L, z ∈ unitDisc :=
    (show ∀ᶠ z in 𝓟 unitDisc, z ∈ unitDisc from eventually_principal.mpr (fun _ hz => hz)).filter_mono inf_le_right
  have hr : Tendsto (fun z : ℂ => 2 * ‖z‖ - 1) L (𝓝 1) := by
    simpa only [mul_one, sub_self, sub_zero, show (2 : ℝ) - 1 = 1 by norm_num] using (hn.const_mul 2).sub_const 1
  have hm := integrableOn_disk_tail_tendsto_zero (A2fun.integrable_weighted_sq isOpen_ball hf)
  have hright : Tendsto (fun z : ℂ => (3072 / π) *
      ∫ u in unitDisc ∩ {u : ℂ | 2 * ‖z‖ - 1 < ‖u‖}, ‖f u‖ ^ 2 * (rho u)⁻¹) L (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using (hm.comp hr).const_mul (3072 / π)
  have hsq : Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 * ‖f z‖) ^ 2) L (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun z => sq_nonneg _) _ hright
    filter_upwards [hD] with z hz
    exact A2fun.disk_boundary_mass_bound hf hz
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (mul_nonneg (sq_nonneg _) (norm_nonneg _)),
    Real.sqrt_zero] using hsqrt

/-- The weighted boundary limit transports to exterior A₂ differentials by inversion. -/
theorem A2fun.exterior_weighted_tendsto_zero {f : ℂ → ℂ} (hf : f ∈ A2fun unitDiscExterior) :
    Tendsto (fun z => (1 - ‖z‖ ^ 2) ^ 2 * ‖f z‖)
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDiscExterior) (𝓝 0) := by
  obtain ⟨ψ, hψ, heq, _⟩ := exists_inverted_A2 hf
  let L := comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDiscExterior
  have hn : Tendsto (fun z : ℂ => ‖z‖) L (𝓝 1) := tendsto_comap.mono_left inf_le_left
  have hD : ∀ᶠ z in L, z ∈ unitDiscExterior :=
    (show ∀ᶠ z in 𝓟 unitDiscExterior, z ∈ unitDiscExterior from
      eventually_principal.mpr (fun _ hz => hz)).filter_mono inf_le_right
  have hInv : Tendsto (fun z : ℂ => z⁻¹) L
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) := by
    apply tendsto_inf.mpr
    constructor
    · apply tendsto_comap_iff.mpr
      simpa only [Function.comp_def, norm_inv, inv_one] using hn.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    · apply tendsto_principal.mpr
      filter_upwards [hD] with z hz
      have hw : z⁻¹ ∈ unitDisc \ {0} := by
        rw [← resolvent_inv_exterior_image]
        exact ⟨z, hz, rfl⟩
      exact hw.1
  apply (A2fun.disk_weighted_tendsto_zero hψ).comp hInv |>.congr'
  filter_upwards [hD] with z hz
  have hw : z⁻¹ ∈ unitDisc \ {0} := by
    rw [← resolvent_inv_exterior_image]
    exact ⟨z, hz, rfl⟩
  have hn0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr (resolvent_exterior_ne_zero hz)
  simp only [Function.comp_def, heq hw, inv_inv, norm_inv, norm_div, norm_pow]
  field_simp
  <;> ring

/-- **Remark 2.2** (TT:1412–1444). Every `μ ∈ H^{-1,1}(𝔻)` (resp. `H^{-1,1}(𝔻*)`) satisfies `μ(z) → 0` as
`|z| → 1`. -/
theorem remark_2_2 {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 D) :
    Tendsto μ (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 D) (𝓝 0) := by
  obtain ⟨φ, hφ, hrep, hfinite⟩ := hμ
  have hopen : IsOpen D := by rcases hD with rfl | rfl; exact isOpen_ball; exact resolvent_exterior_isOpen
  have hcircle : ∀ z ∈ D, ‖z‖ ≠ 1 := by
    rcases hD with rfl | rfl
    · intro z hz; exact ne_of_lt (mem_ball_zero_iff.mp hz)
    · intro z hz; exact ne_of_gt hz
  have hnorm := normA2_eq_normL2_of_harmonic hopen.measurableSet hcircle hrep
  have hA2 : φ ∈ A2fun D := ⟨hφ, by rwa [hnorm]⟩
  have ht : Tendsto (fun z => (1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖)
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 D) (𝓝 0) := by
    rcases hD with rfl | rfl
    · exact A2fun.disk_weighted_tendsto_zero hA2
    · exact A2fun.exterior_weighted_tendsto_zero hA2
  have hDmem : ∀ᶠ z in comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 D, z ∈ D :=
    (show ∀ᶠ z in 𝓟 D, z ∈ D from eventually_principal.mpr (fun _ hz => hz)).filter_mono inf_le_right
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht' : Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖) / 4)
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 D) (𝓝 0) := by
    simpa only [zero_div] using ht.div_const 4
  apply ht'.congr'
  filter_upwards [hDmem] with z hz
  rw [hrep z hz]
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (rho_pos_of_norm_ne_one (hcircle z hz)), Complex.norm_conj]
  simp only [rho, inv_div]
  ring

/-- A double pole on the boundary is weighted bounded on the disk but is not in A₂. -/
theorem exists_AInf_not_A2 : ∃ f : AInf unitDisc, AInf.toFun f ∉ A2fun unitDisc := by
  let p : ℂ → ℂ := fun z => (1 - z)⁻¹ ^ 2
  have hcircle : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun _ hz => ne_of_lt (mem_ball_zero_iff.mp hz)
  have hpole (z : ℂ) (hz : z ∈ unitDisc) : 1 - z ≠ 0 := by
    intro he
    have hz1 : z = 1 := (sub_eq_zero.mp he).symm
    have hn := mem_ball_zero_iff.mp hz
    rw [hz1, norm_one] at hn
    exact lt_irrefl _ hn
  have hhol : DifferentiableOn ℂ p unitDisc :=
    ((differentiableOn_const (1 : ℂ)).sub differentiableOn_id).inv hpole |>.pow 2
  have hbound (z : ℂ) (hz : z ∈ unitDisc) : ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * p z‖ ≤ 4 := by
    have hr : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hn : 0 < ‖1 - z‖ := norm_pos_iff.mpr (hpole z hz)
    have htri : 1 - ‖z‖ ≤ ‖1 - z‖ := by simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) z
    have hbase : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hw : 1 - ‖z‖ ^ 2 ≤ 2 * ‖1 - z‖ := by nlinarith [sq_nonneg (1 - ‖z‖)]
    have hs := pow_le_pow_left₀ hbase hw 2
    have hcast : 1 - (‖z‖ : ℂ) ^ 2 = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    simp only [norm_mul, norm_pow, hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs, p, norm_inv]
    rw [inv_pow, ← div_eq_mul_inv]
    exact (div_le_iff₀ (sq_pos_of_pos hn)).mpr (by nlinarith only [hs])
  obtain ⟨f, heq, _⟩ := exists_AInf_representative_of_bound hcircle hhol (by norm_num : (0 : ℝ) ≤ 4) hbound
  refine ⟨f, ?_⟩
  intro hA2
  have hpos₀ : ∀ᶠ r : ℝ in 𝓝 1, 0 < r := Ioi_mem_nhds (by norm_num)
  have hpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r := hpos₀.filter_mono nhdsWithin_le_nhds
  have hmap : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[<] 1)
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) := by
    apply tendsto_inf.mpr
    constructor
    · apply tendsto_comap_iff.mpr
      have hn : Tendsto (fun r : ℝ => ‖(r : ℂ)‖) (𝓝[<] 1) (𝓝 ‖((1 : ℝ) : ℂ)‖) :=
        (Complex.continuous_ofReal.norm.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
      simpa only [Function.comp_def, Complex.ofReal_one, norm_one] using hn
    · apply tendsto_principal.mpr
      filter_upwards [hpos, self_mem_nhdsWithin] with r hr0 hr1
      change r < 1 at hr1
      apply mem_ball_zero_iff.mpr
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] using hr1
  have hzero := (A2fun.disk_weighted_tendsto_zero hA2).comp hmap
  have hfour : Tendsto (fun r : ℝ => (1 + r) ^ 2) (𝓝[<] 1) (𝓝 (4 : ℝ)) := by
    have hc : Continuous (fun r : ℝ => (1 + r) ^ 2) := by fun_prop
    simpa only [show (1 + (1 : ℝ)) ^ 2 = 4 by norm_num] using
      (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hevent : ∀ᶠ r : ℝ in 𝓝[<] 1,
      (1 - ‖(r : ℂ)‖ ^ 2) ^ 2 * ‖AInf.toFun f (r : ℂ)‖ = (1 + r) ^ 2 := by
    filter_upwards [hpos, self_mem_nhdsWithin] with r hr0 hr1
    have hrlt : r < 1 := hr1
    have hrD : (r : ℂ) ∈ unitDisc := by
      apply mem_ball_zero_iff.mpr
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] using hrlt
    have hcast : (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) := by push_cast; rfl
    rw [heq hrD]
    simp only [p, norm_pow, norm_inv, hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, abs_of_pos (sub_pos.mpr hrlt)]
    rw [inv_pow, ← div_eq_mul_inv]
    apply (div_eq_iff (pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_gt hrlt)))).mpr
    ring
  have hzero' : Tendsto (fun r : ℝ => (1 + r) ^ 2) (𝓝[<] 1) (𝓝 (0 : ℝ)) := hzero.congr' hevent
  have he := tendsto_nhds_unique hzero' hfour
  norm_num at he

/-- The Hilbert inclusion is a proper subspace inclusion. -/
theorem A2toAInf_not_surjective : ¬ Function.Surjective A2toAInf := by
  intro h
  obtain ⟨f, hf⟩ := exists_AInf_not_A2
  apply hf
  have hr : f ∈ range A2toAInf := h f
  rwa [A2toAInf_range] at hr

/-- There are uncountably many algebraic A₂ cosets in Bers function space; this does not use a chosen manifold topology. -/
theorem AInf_quotient_A2_uncountable :
    Uncountable (AInf unitDisc ⧸ LinearMap.range A2toAInfCLM.toLinearMap) := by
  obtain ⟨f, hf⟩ := exists_AInf_not_A2
  let Q := AInf unitDisc ⧸ LinearMap.range A2toAInfCLM.toLinearMap
  let q : Q := Submodule.Quotient.mk f
  have hq : q ≠ 0 := by
    intro he
    have hm : f ∈ LinearMap.range A2toAInfCLM.toLinearMap := (Submodule.Quotient.mk_eq_zero _).mp he
    obtain ⟨x, hx⟩ := hm
    have hr : f ∈ range A2toAInf := ⟨x, hx⟩
    rw [A2toAInf_range] at hr
    exact hf hr
  letI : Uncountable ℂ := Complex.ofReal_injective.uncountable
  exact (smul_left_injective ℂ hq).uncountable

/-- `D₀(β ∘ R_[μ]) = D_μ(β ∘ Φ) ∘ D₀R_μ` (TT:1463), computed on the representative `μ`: the differential at `0` of
`λ ↦ β(Φ(λ * μ))`. -/
def D0BersR (μ : LinfStar) : LinfStar →L[ℂ] AInf unitDisc := fderiv ℂ (fun l => bersPhi (beltramiMul l μ)) 0

/-- The distribution `𝔇_T` (TT:1446–1449) in Bers coordinates. At `[μ]` it is the image of `H^{-1,1}(𝔻*)` under
`D₀(β ∘ R_[μ])`, as a set of holomorphic functions on `𝔻`. -/
def distT (μ : LinfStar) : Set (ℂ → ℂ) :=
  (fun ν => AInf.toFun (D0BersR μ (toLinf ν))) '' harmonicL2 unitDiscExterior

-- Original thm_2_3 moved unchanged to Ch1/HilbertManifoldCompleted.lean (2026-10-27).

-- Original distT_eq_A2 moved unchanged to Ch1/HilbertManifoldCompleted.lean (2026-10-27).

-- weldConst, fsans, gsans moved to Ch1/Welding.lean (2026-10-25, leader; import cycle with QCVariationWeld).

-- `eq_2_1` moved to `Ch1/S2Core.lean` (2026-10-26).

/-- `h` is a quasiconformal reflection in the quasicircle `∂Ω` of the quasidisk `Ω` (TT:1526, [EN88]):
- `z ↦ \overline{h(z)}` is quasiconformal on `Ω*` (so `h` is sense reversing);
- `h` maps `Ω*` into `Ω`;
- `h(z) → z` at the boundary: `h` extends continuously by the identity on `∂Ω`. -/
def IsQCReflection (Ω Ωs : Set ℂ) (h : ℂ → ℂ) : Prop :=
  IsQuasiconformal (fun z => conj (h z)) Ωs ∧ MapsTo h Ωs Ω ∧
    ∀ z ∈ frontier Ω, Tendsto h (𝓝[Ωs] z) (𝓝 z)

-- `eq_2_2` and `eq_2_3` moved to `Ch1/BersReproducingCompleted.lean` (2026-10-27).

-- `remark_2_4` moved to `Ch1/Remark24Completed.lean` (2026-10-26).

/-! ## §2.2 The `L²`-estimates -/

/-- The conclusion of Lemma 2.5 for `ε` and `δ`: for all `μ ∈ Ω^{-1,1}(𝔻*)` with `‖μ‖∞ < δ` and all
`z ∈ 𝔻 ∪ 𝔻*`, `| |(w_μ)_z(z)|²/(1 - |w_μ(z)|²)² - 1/(1 - |z|²)² | < ε/(1 - |z|²)²`, and the same for
`w_{μ⁻¹} = w_μ⁻¹`.

[CORRECTION 2026-10-26] Each clause excludes the single pole of the Model A map. For harmonic `μ`, `wAS μ` need not
fix `∞`, so `wA μ = finPart ∘ wAS μ` takes the junk value `0` at a point of `𝔻*` and `dz` vanishes there; the
unguarded clause was false at that point (found by 下属2). -/
def Lemma25Prop (ε δ : ℝ) : Prop :=
  0 < δ ∧ δ < 1 ∧ ∀ μ ∈ harmonicBeltrami, ‖μ‖ < δ → ∀ z : ℂ, z ∈ unitDisc ∪ unitDiscExterior →
    (wAS μ (z : ExtPlane) ≠ extInf →
      |‖dz (wA μ) z‖ ^ 2 / (1 - ‖wA μ z‖ ^ 2) ^ 2 - 1 / (1 - ‖z‖ ^ 2) ^ 2| < ε / (1 - ‖z‖ ^ 2) ^ 2) ∧
    (wAS (beltramiInv μ) (z : ExtPlane) ≠ extInf →
      |‖dz (wA (beltramiInv μ)) z‖ ^ 2 / (1 - ‖wA (beltramiInv μ) z‖ ^ 2) ^ 2 - 1 / (1 - ‖z‖ ^ 2) ^ 2| <
        ε / (1 - ‖z‖ ^ 2) ^ 2)

-- Original lemma_2_5 moved unchanged to Ch1/GroupChainCompleted.lean (2026-10-26).

/-- The `δ` of Lemma 2.5 for `ε = 1`, fixed once and for all (TT:1640; junk `1/2` if none exists, which
`lemma_2_5` rules out). -/
def delta0 : ℝ := if h : ∃ δ, Lemma25Prop 1 δ then h.choose else 1 / 2

/-- The chosen radius is positive and less than one, including its specified fallback (TT:1640). -/
theorem delta0_bounds : 0 < delta0 ∧ delta0 < 1 := by
  unfold delta0
  split_ifs with h
  · exact ⟨h.choose_spec.1, h.choose_spec.2.1⟩
  · norm_num

-- Original cor_2_6 moved unchanged to Ch1/GroupChainCompleted.lean (2026-10-26).

/-- The subgroup `𝒪(𝔻*)₁` of `L∞(𝔻*)₁` generated by the `μ ∈ Ω^{-1,1}(𝔻*)` with `‖μ‖∞ < δ` (TT:1674): the
intersection of all subsets of `L∞(𝔻*)₁` containing these generators and closed under `*` and `⁻¹`. -/
def groupO : Set LinfStar :=
  {μ | ∀ S : Set LinfStar, S ⊆ LinfStarBall → (∀ ν ∈ harmonicBeltrami, ‖ν‖ < delta0 → ν ∈ S) →
    (∀ a ∈ S, ∀ b ∈ S, beltramiMul a b ∈ S) → (∀ a ∈ S, beltramiInv a ∈ S) → μ ∈ S}

/-- The generating small harmonic differentials belong to `𝒪(𝔻*)₁` (TT:1674). -/
theorem groupO_mem_of_harmonic {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hsmall : ‖μ‖ < delta0) :
    μ ∈ groupO := by
  intro S hS hgen hmul hinv
  exact hgen μ hμ hsmall

/-- The generated set contains zero (TT:1674). -/
theorem zero_mem_groupO : (0 : LinfStar) ∈ groupO := by
  apply groupO_mem_of_harmonic (Submodule.zero_mem _)
  simpa only [norm_zero] using delta0_bounds.1

/-- The generated set is closed under the Beltrami product (TT:1674). -/
theorem groupO_mul_mem {μ ν : LinfStar} (hμ : μ ∈ groupO) (hν : ν ∈ groupO) :
    beltramiMul μ ν ∈ groupO := by
  intro S hS hgen hmul hinv
  exact hmul μ (hμ S hS hgen hmul hinv) ν (hν S hS hgen hmul hinv)

/-- The generated set is closed under the Beltrami inverse (TT:1674). -/
theorem groupO_inv_mem {μ : LinfStar} (hμ : μ ∈ groupO) : beltramiInv μ ∈ groupO := by
  intro S hS hgen hmul hinv
  exact hinv μ (hμ S hS hgen hmul hinv)

-- Original lemma_2_7 moved unchanged to Ch1/GroupChainCompleted.lean (2026-10-26).

-- Original remark_2_8 moved unchanged to Ch1/GroupChainCompleted.lean (2026-10-26).

-- `lemma_2_9` moved to `Ch1/Lemma29Restricted.lean` (2026-10-28, restricted form, user-approved).

/-! ## §2.3 The Hilbert manifold structure of `T(1)` -/

/-- The chart domain `V_μ ⊂ U_μ` (TT:1764): the image under `h_μ⁻¹ = Φ ∘ R_μ ∘ Λ` of the ball of radius `√(π/3)` in
`A₂(𝔻)`. By Lemma 2.1 that ball lies in the ball of radius `2` of `A∞(𝔻)`. -/
def hilbertChartDomain (μ : LinfStarBall) : Set T1 :=
  (fun φ => bersChartInv μ (A2toAInf φ)) '' ball (0 : A2 unitDisc) (Real.sqrt (π / 3))

/-- The Hilbert chart `h̃_μ = h_μ|V_μ : V_μ → A₂(𝔻)` (TT:1767). -/
def hilbertChart (μ : LinfStarBall) : T1 → A2 unitDisc :=
  Function.invFunOn (fun φ => bersChartInv μ (A2toAInf φ)) (ball 0 (Real.sqrt (π / 3)))

-- Original thm_2_10 moved unchanged to Ch1/ComponentTCompleted.lean (2026-10-26).

-- `hilbertChartDomain_cover` moved to `Ch1/S2Cover_Completed.lean` (2026-10-26).

/-- **Definition 2.11** (TT:1844–1856). The Hilbert manifold topology of `T(1)`: the final topology of the atlas
`(V_μ, h̃_μ)`, `μ ∈ 𝒪(𝔻*)₁`, i.e. the finest topology making every inverse chart `h̃_μ⁻¹` (on the ball of radius
`√(π/3)` in `A₂(𝔻)`) continuous: the `⨆` of the coinduced topologies ([CORRECTION 2026-10-25]: was `⨅`, see
`hilbertTopologyA`). Together with `thm_2_10` and `hilbertChartDomain_cover`, this is the structure of a
complex Hilbert manifold modeled on `A₂(𝔻)`. -/
def hilbertTopology : TopologicalSpace T1 :=
  ⨆ μ : {μ : LinfStarBall // (μ : LinfStar) ∈ groupO},
    TopologicalSpace.coinduced (fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
      bersChartInv μ.1 (A2toAInf φ)) inferInstance

-- `cor_2_12` moved to `Ch1/S2Chart_Completed.lean` (2026-10-25).

-- harmonicProj_orthogonal moved to Ch1/WeightedBergman.lean (cycle)

/-! ## §2.4 Integral manifolds of the distribution `𝔇_T` -/

/-- The Hilbert manifold topology of `A∞(𝔻)` (TT:1872), with chart `φ + A₂(𝔻)` at every `φ`: the finest topology
making every map `ψ ↦ φ + ψ`, `A₂(𝔻) → A∞(𝔻)`, continuous.

[CORRECTION 2026-10-25] In Mathlib's order (`t₁ ≤ t₂` iff `t₁` is finer), all maps are continuous iff the `⨆` of
the coinduced topologies is `≤` the target, so the final topology is that `⨆`. The skeleton had `⨅`, which made this
topology discrete (diagnosed by lean3, `collaboration/lean3_actual_topology_diagnostic.lean`). -/
def hilbertTopologyA : TopologicalSpace (AInf unitDisc) :=
  ⨆ φ : AInf unitDisc, TopologicalSpace.coinduced (fun ψ : A2 unitDisc => φ + A2toAInf ψ) inferInstance

/-- The coset `φ + A₂(𝔻)` is the fiber of the quotient map `A∞(𝔻) → A∞(𝔻)/A₂(𝔻)` (lean3). -/
theorem affine_A2_coset_eq_quotient_fiber (φ : AInf unitDisc) :
    (fun ψ : A2 unitDisc => φ + A2toAInf ψ) '' univ =
      {χ | (LinearMap.range A2toAInfCLM.toLinearMap).mkQ χ =
        (LinearMap.range A2toAInfCLM.toLinearMap).mkQ φ} := by
  let P := LinearMap.range A2toAInfCLM.toLinearMap
  have hiQ (ψ : A2 unitDisc) : P.mkQ (A2toAInf ψ) = 0 :=
    (Submodule.Quotient.mk_eq_zero P).mpr ⟨ψ, rfl⟩
  ext χ
  constructor
  · rintro ⟨ψ, _, rfl⟩
    change P.mkQ (φ + A2toAInf ψ) = P.mkQ φ
    rw [map_add, hiQ, add_zero]
  · intro hχ
    have hmem : χ - φ ∈ P := (Submodule.Quotient.eq P).mp hχ
    obtain ⟨ψ, hψ⟩ := hmem
    refine ⟨ψ, mem_univ _, ?_⟩
    change A2toAInf ψ = χ - φ at hψ
    change φ + A2toAInf ψ = χ
    rw [hψ]
    abel

/-- The components of `hilbertTopologyA` are the cosets `φ + A₂(𝔻)` (lean3). -/
theorem hilbertTopologyA_component (φ : AInf unitDisc) :
    @connectedComponent _ hilbertTopologyA φ =
      (fun ψ : A2 unitDisc => φ + A2toAInf ψ) '' univ := by
  let P := LinearMap.range A2toAInfCLM.toLinearMap
  let Q := AInf unitDisc ⧸ P
  letI : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  letI : TopologicalSpace Q := ⊥
  letI : DiscreteTopology Q := ⟨rfl⟩
  have hiQ (ψ : A2 unitDisc) : P.mkQ (A2toAInf ψ) = 0 :=
    (Submodule.Quotient.mk_eq_zero P).mpr ⟨ψ, rfl⟩
  have hπ : Continuous[hilbertTopologyA, (⊥ : TopologicalSpace Q)] P.mkQ := by
    apply continuous_iSup_dom.mpr
    intro χ
    apply continuous_coinduced_dom.mpr
    have he : P.mkQ ∘ (fun ψ : A2 unitDisc => χ + A2toAInf ψ) = fun _ => P.mkQ χ := by
      funext ψ
      simp only [Function.comp_def, map_add, hiQ, add_zero]
    rw [he]
    exact continuous_const
  have hcl : @IsClopen (AInf unitDisc) hilbertTopologyA
      {χ | P.mkQ χ = P.mkQ φ} := (isClopen_discrete {P.mkQ φ}).preimage hπ
  have heq := affine_A2_coset_eq_quotient_fiber φ
  have hx : φ ∈ (fun ψ : A2 unitDisc => φ + A2toAInf ψ) '' univ :=
    ⟨0, mem_univ _, by change φ + A2toAInf 0 = φ; rw [A2toAInf_zero, add_zero]⟩
  have hcont : Continuous[(inferInstance : TopologicalSpace (A2 unitDisc)), hilbertTopologyA]
      (fun ψ : A2 unitDisc => φ + A2toAInf ψ) := by
    apply continuous_iff_coinduced_le.mpr
    unfold hilbertTopologyA
    exact le_iSup (fun χ : AInf unitDisc =>
      (TopologicalSpace.coinduced (fun ψ : A2 unitDisc => χ + A2toAInf ψ)
        (inferInstance : TopologicalSpace (A2 unitDisc)) : TopologicalSpace (AInf unitDisc))) φ
  have hpc : @IsPreconnected (AInf unitDisc) hilbertTopologyA
      ((fun ψ : A2 unitDisc => φ + A2toAInf ψ) '' univ) :=
    isPreconnected_univ.image _ hcont.continuousOn
  apply Set.Subset.antisymm
  · rw [heq]
    exact hcl.connectedComponent_subset (by rfl)
  · exact hpc.subset_connectedComponent hx


/-- (TT:1872) The Hilbert manifold topology on `A∞(𝔻)` is stronger than the Banach space topology. Its components
are the cosets `φ + A₂(𝔻)`, the integral manifolds of `𝔇_A`, and there are uncountably many of them. -/
theorem hilbertTopologyA_spec :
    hilbertTopologyA ≤ (inferInstance : TopologicalSpace (AInf unitDisc)) ∧
      (∀ φ, @connectedComponent _ hilbertTopologyA φ = (fun ψ => φ + A2toAInf ψ) '' univ) ∧
      ¬ (range fun φ => @connectedComponent _ hilbertTopologyA φ).Countable := by
  refine ⟨?_, hilbertTopologyA_component, ?_⟩
  · apply iSup_le
    intro φ
    apply continuous_iff_coinduced_le.mp
    exact continuous_const.add A2toAInfCLM.continuous
  · let P := LinearMap.range A2toAInfCLM.toLinearMap
    let Q := AInf unitDisc ⧸ P
    letI : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
    letI : Uncountable Q := AInf_quotient_A2_uncountable
    let r : Q → AInf unitDisc := fun q => (P.mkQ_surjective q).choose
    have hr (q : Q) : P.mkQ (r q) = q := (P.mkQ_surjective q).choose_spec
    let c : AInf unitDisc → Set (AInf unitDisc) := fun φ => @connectedComponent _ hilbertTopologyA φ
    let k : Q → range c := fun q => ⟨c (r q), ⟨r q, rfl⟩⟩
    have hk : Function.Injective k := by
      intro q q' h
      have he : c (r q) = c (r q') := congrArg Subtype.val h
      have hm : r q ∈ c (r q) := mem_connectedComponent
      rw [he] at hm
      change r q ∈ @connectedComponent _ hilbertTopologyA (r q') at hm
      rw [hilbertTopologyA_component, affine_A2_coset_eq_quotient_fiber] at hm
      change P.mkQ (r q) = P.mkQ (r q') at hm
      simpa only [hr] using hm
    have hunc : Uncountable (range c) := hk.uncountable
    intro hcount
    haveI : Countable (range c) := hcount.to_subtype
    exact hunc.not_countable inferInstance

-- Original thm_2_13 moved unchanged to Ch1/HilbertManifoldCompleted.lean (2026-10-27).

/-- The component `T_[μ](1)` of the Hilbert manifold `T(1)` containing `[μ]` (TT:1896). -/
def componentT (p : T1) : Set T1 := @connectedComponent _ hilbertTopology p

/-- `T₀(1)`, the component of the origin (TT:1898). -/
def T01 : Set T1 := componentT (Phi ⟨0, mem_ball_self one_pos⟩)

-- `componentT_spec` moved to `TakhtajanTeo.Ch1.QDiskComponent` (2026-10-29, Program G).

-- Original componentT_uncountable moved unchanged to Ch1/ComponentTCompleted.lean (2026-10-26).

end TakhtajanTeo
