import TakhtajanTeo.Ch1.S7ResolventEnergy

/-! Actual raw-function linearity and complex polarization for Corollary 7.3. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem s7pol_harmonic_measurable {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    AEStronglyMeasurable μ (volume.restrict unitDiscExterior) :=
  (Lp.aestronglyMeasurable (toLinf μ)).congr (wp_harmonic_toLinf_ae hμ)

theorem s7pol_harmonic_add {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    (fun z => μ z + ν z) ∈ harmonicL2 unitDiscExterior := by
  have hm := s7pol_harmonic_measurable hμ
  have hn := s7pol_harmonic_measurable hν
  obtain ⟨φ, hφ, heφ, hμn⟩ := hμ
  obtain ⟨ψ, hψ, heψ, hνn⟩ := hν
  refine ⟨fun z => φ z + ψ z, hφ.add hψ, ?_, ?_⟩
  · intro z hz
    dsimp only
    rw [heφ z hz, heψ z hz, map_add]
    ring
  · rw [s7pc_normL2_eq unitDiscExterior (f := fun z => μ z + ν z) (hm.add hn)]
    exact (s7pc_memLp hm hμn).add (s7pc_memLp hn hνn)

theorem s7pol_harmonic_smul {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (c : ℂ) :
    (fun z => c * μ z) ∈ harmonicL2 unitDiscExterior := by
  obtain ⟨φ, hφ, heφ, hμn⟩ := hμ
  refine ⟨fun z => conj c * φ z, hφ.const_mul _, ?_, ?_⟩
  · intro z hz
    dsimp only
    rw [heφ z hz, map_mul, conj_conj]
    ring
  · rw [normL2_const_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hμn

theorem s7pol_forcing_measurable {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (κ : LinfStar) :
    AEStronglyMeasurable (fun z => μ z * conj (κ z)) (volume.restrict unitDiscExterior) :=
  (s7pol_harmonic_measurable hμ).mul
    (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable κ))

/-- The raw forcing has a smooth finite-energy potential and actual absolute
kernel convergence, through its proved smooth a.e. representative. -/
theorem s7pol_potential_data {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    resolventStar (fun z => μ z * conj (κ z)) ∈ BCinf unitDiscExterior ∧
      normL2 unitDiscExterior (resolventStar (fun z => μ z * conj (κ z))) < ∞ ∧
      ∀ z ∈ unitDiscExterior, Integrable
        (fun w => (resolventKernel z w : ℂ) * (μ w * conj (κ w)) * rho w)
        (volume.restrict unitDiscExterior) := by
  obtain ⟨f, hf, hfn, he⟩ := s7er_forcing_smooth hμ hκ
  have hp : resolventStar (fun z => μ z * conj (κ z)) = resolventStar f := by
    funext z
    apply integral_congr_ae
    filter_upwards [he] with w hw
    simp only [hw]
  refine ⟨hp ▸ RK3_output_BCinf_exterior hf, ?_, ?_⟩
  · rw [hp]
    exact s7rl_finite (Or.inr rfl) hf hfn
  · intro z hz
    apply (RK3_absolute_convergence (Or.inr rfl) hf hz).congr
    filter_upwards [he] with w hw
    simp only [hw]

/-- Actual additivity of the raw resolvent is justified by kernel L1. -/
theorem s7pol_potential_add {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    resolventStar (fun w => (μ w + ν w) * conj (κ w)) z =
      resolventStar (fun w => μ w * conj (κ w)) z + resolventStar (fun w => ν w * conj (κ w)) z := by
  have hI := (s7pol_potential_data hμ hκ).2.2 z hz
  have hJ := (s7pol_potential_data hν hκ).2.2 z hz
  unfold resolventStar resolventOp
  rw [← integral_add hI hJ]
  apply integral_congr_ae
  filter_upwards with w
  ring

/-- Scalar linearity of the actual Bochner integral holds globally. -/
theorem s7pol_potential_smul (μ : ℂ → ℂ) (κ : LinfStar) (c z : ℂ) :
    resolventStar (fun w => (c * μ w) * conj (κ w)) z =
      c * resolventStar (fun w => μ w * conj (κ w)) z := by
  have he : (fun w => (c * μ w) * conj (κ w)) = (fun w => c * (μ w * conj (κ w))) := by
    funext w
    ring
  rw [he]
  exact resolventOp_const_mul unitDiscExterior _ c z

theorem s7pol_q_add {D : Set ℂ} (hD : IsOpen D) {f g : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f D) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g D) {z : ℂ} (hz : z ∈ D) :
    s7et_q (fun w => f w + g w) z = s7et_q f z + s7et_q g z := by
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (rho w : ℂ)⁻¹ * dzbar f w) D :=
    (wp_rho_inv_contDiff.of_le le_top).contDiffOn.mul (wp_contDiffOn_dzbar hf hD (by simp))
  have hB : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (rho w : ℂ)⁻¹ * dzbar g w) D :=
    (wp_rho_inv_contDiff.of_le le_top).contDiffOn.mul (wp_contDiffOn_dzbar hg hD (by simp))
  have he : (fun w => (rho w : ℂ)⁻¹ * dzbar (fun v => f v + g v) w) =ᶠ[𝓝 z]
      (fun w => (rho w : ℂ)⁻¹ * dzbar f w + (rho w : ℂ)⁻¹ * dzbar g w) := by
    filter_upwards [hD.mem_nhds hz] with w hw
    rw [wp_dzbar_add ((hf.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hw))
      ((hg.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hw))]
    ring
  unfold s7et_q
  rw [dzbar_congr_of_eventuallyEq he, wp_dzbar_add
    ((hA.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hz))
    ((hB.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hz))]

theorem s7pol_q_smul {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f D) (c : ℂ) {z : ℂ} (hz : z ∈ D) :
    s7et_q (fun w => c * f w) z = c * s7et_q f z := by
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (rho w : ℂ)⁻¹ * dzbar f w) D :=
    (wp_rho_inv_contDiff.of_le le_top).contDiffOn.mul (wp_contDiffOn_dzbar hf hD (by simp))
  have he : (fun w => (rho w : ℂ)⁻¹ * dzbar (fun v => c * f v) w) =ᶠ[𝓝 z]
      (fun w => c * ((rho w : ℂ)⁻¹ * dzbar f w)) := by
    filter_upwards [hD.mem_nhds hz] with w hw
    rw [wp_dzbar_const_mul ((hf.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hw))]
    ring
  unfold s7et_q
  rw [dzbar_congr_of_eventuallyEq he, wp_dzbar_const_mul
    ((hA.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hz))]

/-- Raw harmonic additivity, without any pointwise claim about toLinf representatives. -/
theorem s7pol_Qdot_add {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    Qdot (toLinf (fun w => μ w + ν w)) κ z = Qdot (toLinf μ) κ z + Qdot (toLinf ν) κ z := by
  let P := resolventStar (fun w => μ w * conj (κ w))
  let R := resolventStar (fun w => ν w * conj (κ w))
  have he : resolventStar (fun w => (μ w + ν w) * conj (κ w)) =ᶠ[𝓝 z] (fun w => P w + R w) := by
    filter_upwards [resolvent_exterior_isOpen.mem_nhds hz] with w hw
    exact s7pol_potential_add hμ hν hκ hw
  rw [s7ed_Qdot_raw (s7pol_harmonic_add hμ hν) hκ hz, s7ed_Qdot_raw hμ hκ hz,
    s7ed_Qdot_raw hν hκ hz]
  change -2 * s7et_q _ z = -2 * s7et_q P z + -2 * s7et_q R z
  rw [s7et_q_congr he, s7pol_q_add resolvent_exterior_isOpen
    (s7pol_potential_data hμ hκ).1.1 (s7pol_potential_data hν hκ).1.1 hz]
  ring

theorem s7pol_Qdot_smul {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) (c : ℂ) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    Qdot (toLinf (fun w => c * μ w)) κ z = c * Qdot (toLinf μ) κ z := by
  let P := resolventStar (fun w => μ w * conj (κ w))
  have he : resolventStar (fun w => (c * μ w) * conj (κ w)) = (fun w => c * P w) :=
    funext fun w => s7pol_potential_smul μ κ c w
  rw [s7ed_Qdot_raw (s7pol_harmonic_smul hμ c) hκ hz, s7ed_Qdot_raw hμ hκ hz]
  change -2 * s7et_q _ z = c * (-2 * s7et_q P z)
  rw [he, s7pol_q_smul resolvent_exterior_isOpen (s7pol_potential_data hμ hκ).1.1 c hz]
  ring

theorem s7pol_Qdot_measurable {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    AEStronglyMeasurable (Qdot (toLinf μ) κ) (volume.restrict unitDiscExterior) := by
  have hm : AEStronglyMeasurable (fun z => -2 * s7et_q
      (resolventStar (fun w => μ w * conj (κ w))) z) (volume.restrict unitDiscExterior) :=
    (measurable_const.mul (s7el_q_measurable _)).aestronglyMeasurable
  apply hm.congr
  filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz
  exact (s7ed_Qdot_raw hμ hκ hz).symm

theorem s7pol_pair_congr {f g F G : ℂ → ℂ}
    (hf : f =ᵐ[volume.restrict unitDiscExterior] F)
    (hg : g =ᵐ[volume.restrict unitDiscExterior] G) : l2Inner f g = l2Inner F G := by
  apply integral_congr_ae
  filter_upwards [hf, hg] with z hfz hgz
  simp only [hfz, hgz]

/-- Actual complex sesquilinear expansion with all four product integrals
justified by the genuine weighted L2 data. -/
theorem s7pol_pair_comb {f g u v : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    (hg : AEStronglyMeasurable g (volume.restrict unitDiscExterior))
    (hu : AEStronglyMeasurable u (volume.restrict unitDiscExterior))
    (hv : AEStronglyMeasurable v (volume.restrict unitDiscExterior))
    (hfn : normL2 unitDiscExterior f < ∞) (hgn : normL2 unitDiscExterior g < ∞)
    (hun : normL2 unitDiscExterior u < ∞) (hvn : normL2 unitDiscExterior v < ∞) (c : ℂ) :
    l2Inner (fun z => f z + c * g z) (fun z => u z + c * v z) =
      l2Inner f u + conj c * l2Inner f v + c * l2Inner g u +
        (c * conj c) * l2Inner g v := by
  have h1 := s7pc_pairing_integrable hf hu hfn hun
  have h2 := s7pc_pairing_integrable hf hv hfn hvn
  have h3 := s7pc_pairing_integrable hg hu hgn hun
  have h4 := s7pc_pairing_integrable hg hv hgn hvn
  have h12 : Integrable (fun z => f z * conj (u z) * rho z +
      conj c * (f z * conj (v z) * rho z)) (volume.restrict unitDiscExterior) :=
    h1.add (h2.const_mul (conj c))
  have h123 : Integrable (fun z => (f z * conj (u z) * rho z +
      conj c * (f z * conj (v z) * rho z)) + c * (g z * conj (u z) * rho z))
      (volume.restrict unitDiscExterior) := h12.add (h3.const_mul c)
  unfold l2Inner
  calc
    _ = ∫ z in unitDiscExterior,
        (f z * conj (u z) * rho z + conj c * (f z * conj (v z) * rho z)) +
        c * (g z * conj (u z) * rho z) + (c * conj c) * (g z * conj (v z) * rho z) := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [map_add, map_mul]
      ring
    _ = _ := by
      rw [integral_add h123 (h4.const_mul (c * conj c)),
        integral_add h12 (h3.const_mul c),
        integral_add h1 (h2.const_mul (conj c)), integral_const_mul, integral_const_mul,
        integral_const_mul]

/-- **Corollary 7.3** (TT:2812–2815). For `μ, ν ∈ H^{-1,1}(𝔻*)` and `κ ∈ Ω^{-1,1}(𝔻*)`:
`(Q̇(μ)[κ], Q̇(ν)[κ]) = (μκ̄, νκ̄) - (μκ̄, G(νκ̄))`. -/
theorem s7pol_cor_7_3 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    l2Inner (Qdot (toLinf μ) κ) (Qdot (toLinf ν) κ) =
      l2Inner (fun z => μ z * conj (κ z)) (fun z => ν z * conj (κ z)) -
        l2Inner (fun z => μ z * conj (κ z)) (resolventStar fun z => ν z * conj (κ z)) := by
  let A := Qdot (toLinf μ) κ
  let B := Qdot (toLinf ν) κ
  let f := fun z => μ z * conj (κ z)
  let g := fun z => ν z * conj (κ z)
  let u := resolventStar f
  let v := resolventStar g
  have hAm : AEStronglyMeasurable A (volume.restrict unitDiscExterior) := s7pol_Qdot_measurable hμ hκ
  have hBm : AEStronglyMeasurable B (volume.restrict unitDiscExterior) := s7pol_Qdot_measurable hν hκ
  have hfm : AEStronglyMeasurable f (volume.restrict unitDiscExterior) := s7pol_forcing_measurable hμ κ
  have hgm : AEStronglyMeasurable g (volume.restrict unitDiscExterior) := s7pol_forcing_measurable hν κ
  obtain ⟨hu, hun, _⟩ := s7pol_potential_data hμ hκ
  obtain ⟨hv, hvn, _⟩ := s7pol_potential_data hν hκ
  have hum : AEStronglyMeasurable u (volume.restrict unitDiscExterior) :=
    hu.1.continuousOn.aestronglyMeasurable resolvent_exterior_isOpen.measurableSet
  have hvm : AEStronglyMeasurable v (volume.restrict unitDiscExterior) :=
    hv.1.continuousOn.aestronglyMeasurable resolvent_exterior_isOpen.measurableSet
  have hfn : normL2 unitDiscExterior f < ∞ := s7ed_forcing_finite hμ κ
  have hgn : normL2 unitDiscExterior g < ∞ := s7ed_forcing_finite hν κ
  obtain ⟨hAn, hdiagA⟩ := s7re_prop_7_2 hμ hκ
  obtain ⟨hBn, hdiagB⟩ := s7re_prop_7_2 hν hκ
  change l2Inner A A = l2Inner f f - l2Inner f u at hdiagA
  change l2Inner B B = l2Inner g g - l2Inner g v at hdiagB
  let X := l2Inner A B - l2Inner f g + l2Inner f v
  let Y := l2Inner B A - l2Inner g f + l2Inner g u
  have H (c : ℂ) : conj c * X + c * Y = 0 := by
    have hcν := s7pol_harmonic_smul hν c
    have hmc := s7pol_harmonic_add hμ hcν
    have hd := (s7re_prop_7_2 hmc hκ).2
    have hQc : Qdot (toLinf (fun z => μ z + c * ν z)) κ =ᵐ[volume.restrict unitDiscExterior]
        (fun z => A z + c * B z) := by
      filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz
      rw [s7pol_Qdot_add hμ hcν hκ hz, s7pol_Qdot_smul hν hκ c hz]
    have hRc : (fun z => (μ z + c * ν z) * conj (κ z)) =ᵐ[volume.restrict unitDiscExterior]
        (fun z => f z + c * g z) := Eventually.of_forall fun z => by dsimp [f, g]; ring
    have hPc : resolventStar (fun z => (μ z + c * ν z) * conj (κ z)) =ᵐ[volume.restrict unitDiscExterior]
        (fun z => u z + c * v z) := by
      filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz
      rw [s7pol_potential_add hμ hcν hκ hz, s7pol_potential_smul]
    rw [s7pol_pair_congr hQc hQc, s7pol_pair_congr hRc hRc, s7pol_pair_congr hRc hPc] at hd
    rw [s7pol_pair_comb hAm hBm hAm hBm hAn hBn hAn hBn c,
      s7pol_pair_comb hfm hgm hfm hgm hfn hgn hfn hgn c,
      s7pol_pair_comb hfm hgm hum hvm hfn hgn hun hvn c] at hd
    dsimp only [X, Y]
    linear_combination hd - hdiagA - (c * conj c) * hdiagB
  have h1 := H 1
  have hi := H I
  simp only [map_one, one_mul] at h1
  simp only [conj_I] at hi
  have hx : (2 * I) * X = 0 := by linear_combination I * h1 - hi
  have hX : X = 0 := (mul_eq_zero.mp hx).resolve_left (mul_ne_zero (by norm_num) I_ne_zero)
  change l2Inner A B = l2Inner f g - l2Inner f v
  dsimp only [X] at hX
  linear_combination hX

end TakhtajanTeo
