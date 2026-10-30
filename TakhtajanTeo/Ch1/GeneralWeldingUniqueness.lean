import TakhtajanTeo.Ch1.WeldingPairRigidity

/-! Uniqueness of arbitrary welding pairs, without using either original
conformal-welding existence/uniqueness placeholder. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem homeomorph_inverse_isKQC (e : ℂ ≃ₜ ℂ) {K : ℝ} (he : IsKQC e univ K) :
    IsKQC e.symm univ K := by
  have hi : Function.invFunOn (e : ℂ → ℂ) univ = e.symm := by
    funext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [e.injective.injOn.leftInvOn_invFunOn (mem_univ x)]
    exact (e.symm_apply_apply x).symm
  have hh := thm7_2_inv he
  rwa [image_univ_of_surjective e.surjective, hi] at hh

theorem weldingPrime_pair_unique {h f₁ f₂ g₁ g₂ : ℂ → ℂ}
    (hh : h '' unitCircle = unitCircle)
    (hw₁ : IsWeldingPrime h f₁ g₁) (hw₂ : IsWeldingPrime h f₂ g₂) :
    EqOn f₁ f₂ unitDisc ∧ EqOn g₁ g₂ unitDiscExterior := by
  obtain ⟨⟨F₁, G₁, ⟨KF₁, hKF₁⟩, hFs₁, hFf₁, ⟨KG₁, hKG₁⟩, hGs₁, hGg₁, hb₁⟩,
    hf₁d, -, hf₁0, hf₁1, hg₁d, -, -⟩ := hw₁
  obtain ⟨⟨F₂, G₂, ⟨KF₂, hKF₂⟩, hFs₂, hFf₂, ⟨KG₂, hKG₂⟩, hGs₂, hGg₂, hb₂⟩,
    hf₂d, -, hf₂0, hf₂1, hg₂d, -, -⟩ := hw₂
  obtain ⟨eF₁, rfl⟩ := t1_homeomorph hKF₁ hFs₁
  obtain ⟨eG₁, rfl⟩ := t1_homeomorph hKG₁ hGs₁
  obtain ⟨eF₂, rfl⟩ := t1_homeomorph hKF₂ hFs₂
  obtain ⟨eG₂, rfl⟩ := t1_homeomorph hKG₂ hGs₂
  let T₁ : ℂ ≃ₜ ℂ := eF₁.trans eG₁.symm
  let T₂ : ℂ ≃ₜ ℂ := eF₂.trans eG₂.symm
  have hT₁ : IsKQC T₁ univ (KF₁ * KG₁) := by
    change IsKQC ((eG₁.symm : ℂ → ℂ) ∘ (eF₁ : ℂ → ℂ)) univ _
    exact thm7_1_comp hKF₁ (homeomorph_inverse_isKQC eG₁ hKG₁) (subset_univ _)
  have hT₂ : IsKQC T₂ univ (KF₂ * KG₂) := by
    change IsKQC ((eG₂.symm : ℂ → ℂ) ∘ (eF₂ : ℂ → ℂ)) univ _
    exact thm7_1_comp hKF₂ (homeomorph_inverse_isKQC eG₂ hKG₂) (subset_univ _)
  have ht₁ : ∀ z ∈ unitCircle, T₁ z = h z := by
    intro z hz
    change eG₁.symm (eF₁ z) = _
    rw [← hb₁ z hz, eG₁.symm_apply_apply]
  have ht₂ : ∀ z ∈ unitCircle, T₂ z = h z := by
    intro z hz
    change eG₂.symm (eF₂ z) = _
    rw [← hb₂ z hz, eG₂.symm_apply_apply]
  have hunit : unitCircle = sphere (0 : ℂ) 1 := by
    ext z
    simp [unitCircle, mem_sphere_zero_iff_norm]
  have ht₁c : T₁ '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    rw [← hunit, image_congr ht₁, hh]
  have ht₂c : T₂ '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    rw [← hunit, image_congr ht₂, hh]
  have ht₁E := (planeHomeomorph_circle_regions T₁ ht₁c).2.2
  let C : ℂ → ℂ := circleGlue T₂ T₁
  obtain ⟨⟨KC, hKC⟩, hCs⟩ := circleGlue_quasiconformal ⟨_, hT₂⟩ ⟨_, hT₁⟩
    (image_univ_of_surjective T₂.surjective) (image_univ_of_surjective T₁.surjective)
    ht₂c ht₁c (fun z hz => (ht₂ z hz).trans (ht₁ z hz).symm)
  let W : ℂ → ℂ := eG₂ ∘ C
  have hW : IsKQC W univ (KC * KG₂) := thm7_1_comp hKC hKG₂ (subset_univ _)
  have hWs : W '' univ = univ := by
    rw [image_comp, hCs, hGs₂]
  have hWin : EqOn W eF₂ unitDisc := by
    intro z hz
    change eG₂ (circleGlue T₂ T₁ z) = _
    rw [circleGlue_inside T₂ T₁ hz]
    exact eG₂.apply_symm_apply _
  have hWout : EqOn W (eG₂ ∘ T₁) unitDiscExterior := by
    intro z hz
    change eG₂ (circleGlue T₂ T₁ z) = eG₂ (T₁ z)
    rw [circleGlue_outside T₂ T₁ hz]
  have hrep : eG₁ ∘ T₁ = (eF₁ : ℂ → ℂ) := by
    funext z
    exact eG₁.apply_symm_apply _
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hF₁d : DifferentiableOn ℂ eF₁ unitDisc := hf₁d.congr hFf₁
  have hF₂d : DifferentiableOn ℂ eF₂ unitDisc := hf₂d.congr hFf₂
  have hWd : DifferentiableOn ℂ W unitDisc := hF₂d.congr hWin
  have hG₁d : DifferentiableOn ℂ eG₁ unitDiscExterior := hg₁d.congr hGg₁
  have hG₂d : DifferentiableOn ℂ eG₂ unitDiscExterior := hg₂d.congr hGg₂
  have hμ : ∀ᵐ z, complexDilatation eF₁ z = complexDilatation W z := by
    apply abR_c_ae_of_in_out
    · filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from isOpen_ball.measurableSet)] with z hz
      rw [complexDilatation_eq_zero_of_diffAt (hF₁d.differentiableAt (isOpen_ball.mem_nhds hz)),
        complexDilatation_eq_zero_of_diffAt (hWd.differentiableAt (isOpen_ball.mem_nhds hz))]
    · have htE := nx_isKQC_restrict hT₁ hE (subset_univ _)
      have hd₁ := (bg_comp_conformal htE hE ⟨hG₁d, eG₁.injective.injOn, rfl⟩ ht₁E.subset).2
      have hd₂ := (bg_comp_conformal htE hE ⟨hG₂d, eG₂.injective.injOn, rfl⟩ ht₁E.subset).2
      rw [hrep] at hd₁
      filter_upwards [hd₁, hd₂, ae_restrict_mem hE.measurableSet] with z hz₁ hz₂ hz
      rw [abR_t_complexDilatation_congr hE hWout hz]
      exact hz₁.trans hz₂.symm
  have hz0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hjet₁ : deriv (eF₁ : ℂ → ℂ) 0 = 1 :=
    (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz0) hFf₁).deriv_eq.trans hf₁1
  have hjetW : deriv W 0 = 1 :=
    (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz0)
      (fun z hz => (hWin hz).trans (hFf₂ hz))).deriv_eq.trans hf₂1
  have hequal : (eF₁ : ℂ → ℂ) = W := planeQC_unique_normalized_jet ⟨_, hKF₁⟩ ⟨_, hW⟩
    hFs₁ hWs hμ (hF₁d.differentiableAt (isOpen_ball.mem_nhds hz0))
    ((hFf₁ hz0).trans hf₁0) ((hWin hz0).trans ((hFf₂ hz0).trans hf₂0)) hjet₁ hjetW
  constructor
  · intro z hz
    exact (hFf₁ hz).symm.trans ((congrFun hequal z).trans ((hWin hz).trans (hFf₂ hz)))
  · intro z hz
    have hz' : z ∈ T₁ '' unitDiscExterior := by rw [ht₁E]; exact hz
    obtain ⟨y, hy, hyz⟩ := hz'
    calc
      g₁ z = eG₁ z := (hGg₁ hz).symm
      _ = eG₁ (T₁ y) := by rw [hyz]
      _ = eF₁ y := congrFun hrep y
      _ = W y := congrFun hequal y
      _ = eG₂ (T₁ y) := hWout hy
      _ = eG₂ z := by rw [hyz]
      _ = g₂ z := hGg₂ hz

theorem conformal_welding_prime_unique {h f₁ f₂ g₁ g₂ : ℂ → ℂ}
    (hh : IsOneFixedQS h) (hw₁ : IsWeldingPrime h f₁ g₁) (hw₂ : IsWeldingPrime h f₂ g₂) :
    EqOn f₁ f₂ unitDisc ∧ EqOn g₁ g₂ unitDiscExterior :=
  weldingPrime_pair_unique (sense_circle_image hh.1.1) hw₁ hw₂

theorem weldingPrime_of_welding {h f g : ℂ → ℂ} (hw : IsWelding h id f g) :
    IsWeldingPrime h f g := by
  obtain ⟨-, ⟨F, G, hF, hFs, hFf, hG, hGs, hGg, hb⟩, hrest⟩ := hw
  refine ⟨⟨F, G, hF, hFs, hFf, hG, hGs, hGg, ?_⟩, hrest⟩
  intro z hz
  exact OnePoint.coe_injective (hb z hz)

theorem conformal_welding_unique {h f₁ f₂ g₁ g₂ : ℂ → ℂ}
    (hh : IsNormalizedQS h) (hw₁ : IsWelding h id f₁ g₁) (hw₂ : IsWelding h id f₂ g₂) :
    EqOn f₁ f₂ unitDisc ∧ EqOn g₁ g₂ unitDiscExterior :=
  weldingPrime_pair_unique (sense_circle_image hh.1.1)
    (weldingPrime_of_welding hw₁) (weldingPrime_of_welding hw₂)

end TakhtajanTeo

#print axioms TakhtajanTeo.conformal_welding_prime_unique
#print axioms TakhtajanTeo.conformal_welding_unique
