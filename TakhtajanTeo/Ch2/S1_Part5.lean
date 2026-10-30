import TakhtajanTeo.Ch2.S1_Part4
import TakhtajanTeo.Ch1.NormalizedWelding
import TakhtajanTeo.Ch1.WeldingUniqueness
import TakhtajanTeo.Ch1.SphereWeldingTransport
import TakhtajanTeo.Ch1.S1_1_Completed
import TakhtajanTeo.Ch2.S2_Grunsky

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-! ## Ch2 `eq_1_3` (`e13_` prefix) -/

theorem e13_wB_disc {ν : LinfStar} (hν : ν ∈ LinfStarBall) {u : ℂ} (hu : u ∈ unitDisc) :
    wB ν (u : ExtPlane) = ((fB ν u : ℂ) : ExtPlane) := by
  obtain ⟨M, hM, W, hW, hwf, hwi, f, hf, hf0, hf1, hfp⟩ := (wB_spec hν).1
  have h1 := hf u hu
  have h2 : fB ν u = f u := by
    show finPart (wB ν (u : ExtPlane)) = f u
    rw [h1]; rfl
  rw [h2]; exact h1

theorem e13_invFun_wAS {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Function.invFun (wAS (beltramiInv μ)) = wAS μ := by
  funext q
  apply (wAS_bijective (beltramiInv μ)).1
  rw [Function.invFun_eq ((wAS_bijective (beltramiInv μ)).2 q), bg_inverse_left_sphere hμ]

theorem e13_Lam_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (z : ℂ) :
    normalizedWeldingExterior (beltramiInv μ) z = finPart (wB (beltramiInv μ) (wAS μ (z : ExtPlane))) := by
  unfold normalizedWeldingExterior normalizedWeldingSphere
  rw [Function.comp_apply, e13_invFun_wAS hμ]

theorem e13_Lam_disc {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    normalizedWeldingExterior (beltramiInv μ) z = fB (beltramiInv μ) (wA μ z) := by
  have hν := bc_beltramiInv_mem_ball hμ
  obtain ⟨u, hu, hzu⟩ := wAS_maps_disc hμ (mem_ball_zero_iff.mp hz)
  have hwA : wA μ z = u := by
    show finPart (wAS μ (z : ExtPlane)) = u
    rw [hzu]; rfl
  rw [e13_Lam_eq hμ, hzu, e13_wB_disc hν (mem_ball_zero_iff.mpr hu), hwA]
  rfl

theorem e13_gsans_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    gsans μ = gMu μ := by
  funext z
  have hid : Function.invFun (id : ExtPlane → ExtPlane) = id :=
    funext (fun z => Function.leftInverse_invFun Function.injective_id z)
  rw [gsans, AppB.b8_weldConst_zero hμ, alphaMu_eq_id, hid]
  simp [lambdaW, finPart]

theorem e13_fsans_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    fsans μ = fB μ := by
  funext z
  rw [fsans, AppB.b8_weldConst_zero hμ]
  simp [lambdaW]


theorem e13_mobius_one : mobiusExt 1 0 0 1 = id := by
  funext p
  induction p using OnePoint.rec with
  | infty => exact mobiusExt_infty_of_eq rfl
  | coe z =>
    rw [mobiusExt_coe (by simp)]
    simp [mobiusFn]

theorem e13_map_homeo {W : ℂ → ℂ} (e : ℂ ≃ₜ ℂ) (he : ⇑e = W) :
    OnePoint.map W = e.onePointCongr := by
  funext p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z => simp [Homeomorph.onePointCongr_apply, he]

theorem e13_rho_continuous : Continuous (fun p : ExtPlane => mobiusExt 0 1 1 0 (OnePoint.map conj p)) := by
  have hmap : OnePoint.map (conj : ℂ → ℂ) = Complex.conjCLE.toHomeomorph.onePointCongr :=
    e13_map_homeo Complex.conjCLE.toHomeomorph rfl
  have h1 : Continuous (fun p : ExtPlane => OnePoint.map (conj : ℂ → ℂ) p) := by
    rw [hmap]; exact Homeomorph.continuous _
  exact (continuous_mobiusExt (by norm_num)).comp h1

theorem e13_rho_bijective :
    Function.Bijective (fun p : ExtPlane => mobiusExt 0 1 1 0 (OnePoint.map conj p)) :=
  Function.Involutive.bijective rho_invol

theorem e13_reflConj {W : ℂ → ℂ} {K : ℝ} (hK : IsKQC W univ K) (hs : W '' univ = univ) (h0 : W 0 = 0) :
    IsKQC (fun z : ℂ => (conj (W (conj z⁻¹)))⁻¹) univ K := by
  set f₁ : ℂ → ℂ := fun w => conj (W (conj w)) with hf₁
  have hf₁K : IsKQC f₁ univ K := by
    have h := abR_x_isKQC_conj hK
    rwa [preimage_univ] at h
  have hf₁s : f₁ '' univ = univ := by
    refine eq_univ_of_forall fun w => ?_
    have hw : conj w ∈ W '' univ := by
      rw [hs]
      exact mem_univ _
    obtain ⟨v, -, hv⟩ := hw
    exact ⟨conj v, mem_univ _, by simp only [hf₁, Complex.conj_conj, hv]⟩
  have hf₁0 : f₁ 0 = 0 := by simp [hf₁, h0]
  have hGh := bg2_m1_isHomeomorphOnto hf₁K hf₁s 0 1 0 one_ne_zero
  have hGK0 := bg2_m1_isKQC hf₁K 0 1 0 one_ne_zero
  have hGK := b4_isKQC_univ_of_punctured hGh hGK0
  have : (fun z : ℂ => (conj (W (conj z⁻¹)))⁻¹) = fun z => (f₁ (0 + 1 * (z + 0)⁻¹) - f₁ 0)⁻¹ := by
    funext z
    simp [hf₁, h0]
  rw [this]
  exact hGK


theorem e13_Lam'_kqc {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {b : ℂ} (hb : b ≠ 0) :
    ∃ K, IsKQC (fun z : ℂ => finPart (mobiusExt (conj b) 0 0 1
      (mobiusExt 0 1 1 0 (OnePoint.map conj (wB μ (mobiusExt 0 1 1 0 (OnePoint.map conj (z : ExtPlane)))))))) univ K := by
  obtain ⟨hB, -⟩ := wB_spec hμ
  obtain ⟨M, hM, W, hW, hwf, hwi, f, hf, hf0, hf1, hfp⟩ := hB
  obtain ⟨K, hK⟩ := hW.1
  have hWs : W '' univ = univ := hW.2.1
  have hW0 : W 0 = 0 := hW.2.2.1
  have hWi : Function.Injective W := fun x y h => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) h
  have heq : wB μ = fun p => M (OnePoint.map W p) := by
    funext p
    induction p using OnePoint.rec with
    | infty => exact hwi
    | coe z => exact hwf z
  obtain ⟨e, he⟩ := t1_homeomorph hK hWs
  have hWhat : OnePoint.map W = e.onePointCongr := e13_map_homeo e he
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ExtPlane → ExtPlane, ρ = fun p => mobiusExt 0 1 1 0 (OnePoint.map conj p) :=
    ⟨_, rfl⟩
  have hρc : ∀ v : ℂ, v ≠ 0 → ρ (v : ExtPlane) = ((refl v : ℂ) : ExtPlane) := by
    intro v hv; rw [hρ]; exact rho_coe hv
  have hρ0 : ρ ((0 : ℂ) : ExtPlane) = extInf := by rw [hρ]; exact rho_zero
  have hρi : ρ extInf = ((0 : ℂ) : ExtPlane) := by rw [hρ]; exact rho_infty
  have hρρ : ∀ q, ρ (ρ q) = q := by intro q; rw [hρ]; exact rho_invol q
  have hρcont : Continuous ρ := by rw [hρ]; exact e13_rho_continuous
  have hρbij : Function.Bijective ρ := by rw [hρ]; exact e13_rho_bijective
  have hŴb : Function.Bijective (OnePoint.map W) := by rw [hWhat]; exact e.onePointCongr.bijective
  have hŴc : Continuous (OnePoint.map W) := by rw [hWhat]; exact e.onePointCongr.continuous
  have hGb : Function.Bijective (fun p => ρ (OnePoint.map W (ρ p))) :=
    hρbij.comp (hŴb.comp hρbij)
  have hGc : Continuous (fun p => ρ (OnePoint.map W (ρ p))) :=
    hρcont.comp (hŴc.comp hρcont)
  have hg : ∀ z : ℂ, ρ (OnePoint.map W (ρ (z : ExtPlane))) =
      (((conj (W (conj z⁻¹)))⁻¹ : ℂ) : ExtPlane) := by
    intro z
    by_cases hz : z = 0
    · subst hz
      rw [hρ0]
      show ρ extInf = _
      rw [hρi]
      simp [hW0]
    · have hrz : refl z ≠ 0 := by simpa [refl] using hz
      rw [hρc z hz]
      show ρ ((W (refl z) : ℂ) : ExtPlane) = _
      have hWz : W (refl z) ≠ 0 := fun h => hrz (hWi (h.trans hW0.symm))
      rw [hρc _ hWz]
      simp [refl]
  have hgq := e13_reflConj hK hWs hW0
  have hMid : IsMobius (mobiusExt 1 0 0 1) := ⟨1, 0, 0, 1, by norm_num, rfl⟩
  have hrr : IsMobius (mobiusExt (conj b) 0 0 1) :=
    ⟨conj b, 0, 0, 1, by simpa using hb, rfl⟩
  have hinvM : IsMobius (mobiusExt 0 1 1 0) := ⟨0, 1, 1, 0, by norm_num, rfl⟩
  have hN0 : IsMobius (fun q => ρ (M (ρ q))) := by
    have h1 : IsMobius (fun w => M (mobiusExt 0 1 1 0 w)) := isMobius_comp hinvM hM
    have h2 := isMobius_conj h1
    have h3 := isMobius_comp h2 hinvM
    rw [hρ]
    exact h3
  have hN : IsMobius (fun q => mobiusExt (conj b) 0 0 1 (ρ (M (ρ q)))) := isMobius_comp hN0 hrr
  have hWf0 : M ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) := by
    have h1 := e13_wB_disc hμ (u := 0) (by simp [unitDisc])
    rw [(fB_normalization μ).1, heq] at h1
    simpa [hW0] using h1
  have hi : mobiusExt (conj b) 0 0 1 (ρ (M (ρ (ρ (OnePoint.map W (ρ (mobiusExt 1 0 0 1 extInf))))))) =
      extInf := by
    rw [e13_mobius_one]
    show mobiusExt (conj b) 0 0 1 (ρ (M (ρ (ρ (OnePoint.map W (ρ extInf)))))) = extInf
    rw [hρi, hρρ]
    show mobiusExt (conj b) 0 0 1 (ρ (M ((W 0 : ℂ) : ExtPlane))) = extInf
    rw [hW0, hWf0, hρ0]
    exact mobiusExt_infty_of_eq rfl
  have := sphereTransport_isKQC hGb hGc hg hgq hMid hN (by simpa using hi)
  refine ⟨K, ?_⟩
  convert this using 2 with z
  rw [e13_mobius_one]
  show _ = finPart (mobiusExt (conj b) 0 0 1 (ρ (M (ρ (ρ (OnePoint.map W (ρ (z : ExtPlane))))))))
  rw [hρρ, heq]
  rw [hρ]


theorem e13_wB_factor (μ : LinfStar) (p : ExtPlane) :
    wB μ p = normalizedWeldingSphere μ (wAS μ p) := by
  unfold normalizedWeldingSphere
  rw [Function.comp_apply, Function.leftInverse_invFun (wAS_bijective μ).1 p]

theorem e13_rr_coe {b x : ℂ} :
    mobiusExt (conj b) 0 0 1 (x : ExtPlane) = ((conj b * x : ℂ) : ExtPlane) := by
  rw [mobiusExt_coe (by simp)]
  simp [mobiusFn]

theorem e13_Lam'_ext {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (b : ℂ) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    finPart (mobiusExt (conj b) 0 0 1
      (mobiusExt 0 1 1 0 (OnePoint.map conj (wB μ (mobiusExt 0 1 1 0 (OnePoint.map conj (z : ExtPlane))))))) =
      conj b * refl (fB μ (refl z)) := by
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; exact absurd hz1 (by norm_num)
  have hrz : refl z ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, norm_refl]
    exact inv_lt_one_of_one_lt₀ hz1
  have hrz0 : refl z ≠ 0 := by simpa [refl] using hz0
  obtain ⟨hd, hi⟩ := fB_holomorphic_injective hμ
  have h0 : fB μ (refl z) ≠ 0 := by
    intro h
    exact hrz0 (hi hrz (by simp [unitDisc]) (h.trans (fB_normalization μ).1.symm))
  rw [rho_coe hz0, e13_wB_disc hμ hrz, rho_coe h0, e13_rr_coe]
  rfl

theorem e13_Lam'_disc {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {φ : ℂ → ℂ} {b : ℂ} (hb : b ≠ 0)
    (hφ0 : φ 0 = 0) (hφi : InjOn φ unitDisc)
    (hG : ∀ s ∈ unitDisc, s ≠ 0 → gMu μ (1 / s) = b / φ s) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    finPart (mobiusExt (conj b) 0 0 1
      (mobiusExt 0 1 1 0 (OnePoint.map conj (wB μ (mobiusExt 0 1 1 0 (OnePoint.map conj (z : ExtPlane))))))) =
      conj (φ (conj (wA μ z))) := by
  obtain ⟨u, hu, hzu⟩ := wAS_maps_disc hμ (mem_ball_zero_iff.mp hz)
  have hwA : wA μ z = u := by
    show finPart (wAS μ (z : ExtPlane)) = u
    rw [hzu]; rfl
  have _hz0 := hz0
  rw [hwA, e13_wB_factor, wAS_refl_comm hμ, hzu]
  by_cases hu0 : u = 0
  · subst hu0
    rw [rho_zero]
    have hΓ : normalizedWeldingSphere μ extInf = extInf := normalizedWeldingSphere_infty hμ
    rw [hΓ, rho_infty]
    show finPart (mobiusExt (conj b) 0 0 1 ((0 : ℂ) : ExtPlane)) = _
    rw [e13_rr_coe]
    simp [hφ0]
    rfl
  · have hcu : conj u ≠ 0 := (map_ne_zero conj).mpr hu0
    have hcud : conj u ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, Complex.norm_conj]
      exact mem_ball_zero_iff.mp (by simpa [unitDisc] using hu)
    have hφu : φ (conj u) ≠ 0 := fun h =>
      hcu (hφi hcud (by simp [unitDisc]) (h.trans hφ0.symm))
    have hrext : refl u ∈ unitDiscExterior := by
      show 1 < ‖refl u‖
      rw [norm_refl]
      exact one_lt_inv₀ (norm_pos_iff.mpr hu0) |>.mpr (by simpa using hu)
    have hG1 : gMu μ (refl u) = b / φ (conj u) := by
      have := hG (conj u) hcud hcu
      rw [one_div] at this
      simpa [refl] using this
    have hΓ : normalizedWeldingSphere μ ((refl u : ℂ) : ExtPlane) =
        ((gMu μ (refl u) : ℂ) : ExtPlane) := by
      rw [← normalizedWeldingExterior_coe hμ, gMu_eq_normalizedWeldingExterior hμ hrext]
    rw [rho_coe hu0, hΓ, hG1]
    have hne : b / φ (conj u) ≠ 0 := div_ne_zero hb hφu
    rw [rho_coe hne, e13_rr_coe]
    show conj b * refl (b / φ (conj u)) = _
    simp only [refl, map_div₀]
    have hcb : conj b ≠ 0 := (map_ne_zero conj).mpr hb
    field_simp


theorem e13_diff_conj {f : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℂ f (conj x)) :
    DifferentiableAt ℂ (fun y => conj (f (conj y))) x := by
  have h := hf.conj_conj
  rwa [Complex.conj_conj] at h

theorem e13_deriv_conj {f : ℂ → ℂ} {x : ℂ} :
    deriv (fun y => conj (f (conj y))) x = conj (deriv f (conj x)) := by
  have h := congrFun (deriv_conj_conj (f := f)) x
  simpa [Function.comp_def] using h

theorem e13_ext_diff {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (b : ℂ) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    DifferentiableAt ℂ (fun x => conj b * refl (fB μ (refl x))) z := by
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; exact absurd hz1 (by norm_num)
  have hrz : refl z ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, norm_refl]
    exact inv_lt_one_of_one_lt₀ hz1
  have hrz0 : refl z ≠ 0 := by simpa [refl] using hz0
  obtain ⟨hd, hi⟩ := fB_holomorphic_injective hμ
  have h0 : fB μ (refl z) ≠ 0 := by
    intro h
    exact hrz0 (hi hrz (by simp [unitDisc]) (h.trans (fB_normalization μ).1.symm))
  have hfd : DifferentiableAt ℂ (fB μ) (conj z⁻¹) := by
    have : conj z⁻¹ = refl z := by simp [refl]
    rw [this]
    exact hd.differentiableAt (isOpen_ball.mem_nhds hrz)
  have hk : DifferentiableAt ℂ (fun y => conj (fB μ (conj y))) z⁻¹ := e13_diff_conj hfd
  have hkz : DifferentiableAt ℂ (fun y => conj (fB μ (conj y))) (z⁻¹) := hk
  have hcomp : DifferentiableAt ℂ (fun x : ℂ => conj (fB μ (conj x⁻¹))) z :=
    DifferentiableAt.comp z (g := fun y => conj (fB μ (conj y))) hkz (differentiableAt_inv hz0)
  have hne : conj (fB μ (conj z⁻¹)) ≠ 0 := by
    have : conj z⁻¹ = refl z := by simp [refl]
    rw [this]
    exact (map_ne_zero conj).mpr h0
  have hinv := hcomp.inv hne
  have heq : (fun x : ℂ => conj b * refl (fB μ (refl x))) =
      fun x => conj b * (conj (fB μ (conj x⁻¹)))⁻¹ := by
    funext x
    simp [refl]
  rw [heq]
  exact (differentiableAt_const _).mul hinv

theorem e13_Lam'_bij {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {b : ℂ} (hb : b ≠ 0) :
    Function.Bijective (fun z : ℂ => finPart (mobiusExt (conj b) 0 0 1
      (mobiusExt 0 1 1 0 (OnePoint.map conj (wB μ (mobiusExt 0 1 1 0 (OnePoint.map conj (z : ExtPlane)))))))) := by
  have hrr : IsMobius (mobiusExt (conj b) 0 0 1) :=
    ⟨conj b, 0, 0, 1, by simpa using hb, rfl⟩
  have hrrb := (mobius_sphere_continuous_bijective hrr).2
  have hρb := e13_rho_bijective
  have hFb : Function.Bijective (fun p : ExtPlane => mobiusExt (conj b) 0 0 1
      (mobiusExt 0 1 1 0 (OnePoint.map conj (wB μ (mobiusExt 0 1 1 0 (OnePoint.map conj p)))))) :=
    hrrb.comp (hρb.comp ((wB_bijective μ).comp hρb))
  have hFi : mobiusExt (conj b) 0 0 1
      (mobiusExt 0 1 1 0 (OnePoint.map conj (wB μ (mobiusExt 0 1 1 0 (OnePoint.map conj extInf))))) =
      extInf := by
    have h1 : ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) := rfl
    have hw0 : wB μ ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) := by
      rw [e13_wB_disc hμ (u := 0) (by simp [unitDisc]), (fB_normalization μ).1]
    rw [rho_infty, hw0]
    rw [rho_zero]
    exact mobiusExt_infty_of_eq rfl
  exact sphereFinite_bijective hFb hFi


theorem e13_dil_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    complexDilatation f z = complexDilatation g z := by
  unfold complexDilatation dz dzbar
  rw [h.fderiv_eq]

theorem e13_dil_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {φ : ℂ → ℂ} {b : ℂ} (hb : b ≠ 0)
    (hφd : DifferentiableOn ℂ φ unitDisc) (hφi : InjOn φ unitDisc) (hφ0 : φ 0 = 0)
    (hG : ∀ s ∈ unitDisc, s ≠ 0 → gMu μ (1 / s) = b / φ s) :
    ∀ᵐ z : ℂ, complexDilatation (normalizedWeldingExterior (beltramiInv μ)) z =
      complexDilatation (fun z : ℂ => finPart (mobiusExt (conj b) 0 0 1
        (mobiusExt 0 1 1 0 (OnePoint.map conj (wB μ (mobiusExt 0 1 1 0 (OnePoint.map conj (z : ExtPlane)))))))) z := by
  have hν := bc_beltramiInv_mem_ball hμ
  have hopen : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hcirc : ∀ᵐ z : ℂ, ‖z‖ ≠ 1 := by
    have hnull : volume (sphere (0 : ℂ) 1) = 0 := Measure.addHaar_sphere volume 0 1
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz
    exact fun h => hz (by simpa using h)
  filter_upwards [bc_wA_ae hμ, hcirc, compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with z hAz hc1 hz0
  have hz0' : z ≠ 0 := hz0
  rcases lt_or_gt_of_ne hc1 with hlt | hgt
  · have hz : z ∈ unitDisc := mem_ball_zero_iff.mpr hlt
    obtain ⟨u, hu, hzu⟩ := wAS_maps_disc hμ hlt
    have hwA : wA μ z = u := by
      show finPart (wAS μ (z : ExtPlane)) = u
      rw [hzu]; rfl
    have hud : u ∈ unitDisc := mem_ball_zero_iff.mpr hu
    obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective hν
    have hd1 : DifferentiableAt ℂ (fB (beltramiInv μ)) (wA μ z) := by
      rw [hwA]; exact hfd.differentiableAt (isOpen_ball.mem_nhds hud)
    have hd2 : deriv (fB (beltramiInv μ)) (wA μ z) ≠ 0 := by
      rw [hwA]; exact deriv_ne_zero_of_injOn isOpen_ball hfd hfi hud
    have h1 : normalizedWeldingExterior (beltramiInv μ) =ᶠ[𝓝 z] fB (beltramiInv μ) ∘ wA μ := by
      filter_upwards [isOpen_ball.mem_nhds hz] with z' hz'
      exact e13_Lam_disc hμ hz'
    rw [e13_dil_congr h1, complexDilatation_comp_conformal_left hAz.1 hd1 hd2]
    -- the other side
    have hcud : conj u ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, Complex.norm_conj]; exact hu
    have hd3 : DifferentiableAt ℂ (fun w => conj (φ (conj w))) (wA μ z) := by
      rw [hwA]; exact e13_diff_conj (hφd.differentiableAt (isOpen_ball.mem_nhds hcud))
    have hd4 : deriv (fun w => conj (φ (conj w))) (wA μ z) ≠ 0 := by
      rw [hwA, e13_deriv_conj]
      exact (map_ne_zero conj).mpr (deriv_ne_zero_of_injOn isOpen_ball hφd hφi hcud)
    have h2 : (fun z : ℂ => finPart (mobiusExt (conj b) 0 0 1
        (mobiusExt 0 1 1 0 (OnePoint.map conj (wB μ (mobiusExt 0 1 1 0 (OnePoint.map conj (z : ExtPlane)))))))) =ᶠ[𝓝 z]
        (fun w => conj (φ (conj w))) ∘ wA μ := by
      have hnb : (unitDisc ∩ {(0 : ℂ)}ᶜ) ∈ 𝓝 z :=
        (isOpen_ball.inter isOpen_compl_singleton).mem_nhds ⟨hz, hz0'⟩
      filter_upwards [hnb] with z' hz'
      exact e13_Lam'_disc hμ hb hφ0 hφi hG hz'.1 hz'.2
    rw [e13_dil_congr h2, complexDilatation_comp_conformal_left hAz.1 hd3 hd4]
  · have hz : z ∈ unitDiscExterior := hgt
    have hL : DifferentiableAt ℂ (normalizedWeldingExterior (beltramiInv μ)) z :=
      (normalizedWeldingExterior_differentiableOn hν).differentiableAt (hopen.mem_nhds hz)
    rw [complexDilatation_eq_zero_of_diffAt hL]
    have h2 : (fun z : ℂ => finPart (mobiusExt (conj b) 0 0 1
        (mobiusExt 0 1 1 0 (OnePoint.map conj (wB μ (mobiusExt 0 1 1 0 (OnePoint.map conj (z : ExtPlane)))))))) =ᶠ[𝓝 z]
        (fun x => conj b * refl (fB μ (refl x))) := by
      filter_upwards [hopen.mem_nhds hz] with z' hz'
      exact e13_Lam'_ext hμ b hz'
    rw [e13_dil_congr h2, complexDilatation_eq_zero_of_diffAt (e13_ext_diff hμ b hz)]


/-- **(1.3)** (TT:3757). With `j(z) = 1/z̄` and `r(z) = \overline{𝗀_μ'(∞)} z`:
`𝖿^{μ⁻¹} = r ∘ j ∘ 𝗀_μ ∘ j` on `𝔻` and `𝗀_{μ⁻¹} = r ∘ j ∘ 𝖿^μ ∘ j` on `𝔻*`. -/
theorem w3_eq_1_3 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    (∀ z ∈ unitDisc, z ≠ 0 →
        fsans (beltramiInv μ) z = conj (derivAtInfty (gsans μ)) * refl (gsans μ (refl z))) ∧
      ∀ z ∈ unitDiscExterior,
        gsans (beltramiInv μ) z = conj (derivAtInfty (gsans μ)) * refl (fsans μ (refl z)) := by
  have hν := bc_beltramiInv_mem_ball hμ
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨φ, b, hφd, hφi, hφ0, hφ1, hb, hbg, hG⟩ := g1_inverted_exterior hpair
  have hG' : ∀ s ∈ unitDisc, s ≠ 0 → gMu μ (1 / s) = b / φ s := by
    rw [← e13_gsans_eq hμ]; exact hG
  have hopen : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective hν
  obtain ⟨hf0, hf1, -⟩ := fB_normalization (beltramiInv μ)
  -- the two plane quasiconformal maps
  have hΛq := normalizedWeldingExterior_quasiconformal hν
  have hΛs : normalizedWeldingExterior (beltramiInv μ) '' univ = univ :=
    (normalizedWeldingExterior_homeomorph hν).2.2.1
  obtain ⟨K, hK⟩ := e13_Lam'_kqc hμ hb
  have hΛ's : (fun z : ℂ => finPart (mobiusExt (conj b) 0 0 1
      (mobiusExt 0 1 1 0 (OnePoint.map conj (wB μ (mobiusExt 0 1 1 0 (OnePoint.map conj (z : ExtPlane))))))))
        '' univ = univ := by
    rw [image_univ]
    exact (e13_Lam'_bij hμ hb).2.range_eq
  obtain ⟨ψ, hψ, hrel⟩ := uq_conformal_auto isOpen_univ hΛq ⟨K, hK⟩ hΛs hΛ's
    (by simpa only [Measure.restrict_univ] using e13_dil_ae hμ hb hφd hφi hφ0 hG')
  obtain ⟨a, c, -, hψ'⟩ := nx_entire_affine hψ
  have hrel' : ∀ z : ℂ, finPart (mobiusExt (conj b) 0 0 1
      (mobiusExt 0 1 1 0 (OnePoint.map conj (wB μ (mobiusExt 0 1 1 0 (OnePoint.map conj (z : ExtPlane)))))))
        = a * normalizedWeldingExterior (beltramiInv μ) z + c := by
    intro z
    rw [hrel z (mem_univ z), hψ']
  -- identification on the disc
  have hS : EqOn (fun w => conj (φ (conj w))) (fun w => a * fB (beltramiInv μ) w + c)
      (unitDisc ∩ {wA μ 0}ᶜ) := by
    rintro u ⟨hu, hu0⟩
    obtain ⟨t, ht, hwt⟩ := wAS_maps_disc hν (mem_ball_zero_iff.mp hu)
    have htd : t ∈ unitDisc := mem_ball_zero_iff.mpr ht
    have hwA : wA μ t = u := by
      have h1 : wAS μ (t : ExtPlane) = (u : ExtPlane) := by
        rw [← hwt, bg_inverse_right_sphere hμ]
      show finPart (wAS μ (t : ExtPlane)) = u
      rw [h1]; rfl
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hu0 hwA.symm
    have h1 := e13_Lam'_disc hμ hb hφ0 hφi hG' htd ht0
    rw [hrel' t, e13_Lam_disc hμ htd, hwA] at h1
    simpa [hwA] using h1.symm
  have hcont1 : ContinuousOn (fun w => conj (φ (conj w))) unitDisc := by
    intro w hw
    have hcw : conj w ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, Complex.norm_conj]; exact mem_ball_zero_iff.mp hw
    exact (e13_diff_conj (hφd.differentiableAt (isOpen_ball.mem_nhds hcw))).continuousAt.continuousWithinAt
  have hcont2 : ContinuousOn (fun w => a * fB (beltramiInv μ) w + c) unitDisc :=
    (continuousOn_const.mul hfd.continuousOn).add continuousOn_const
  have hEq : EqOn (fun w => conj (φ (conj w))) (fun w => a * fB (beltramiInv μ) w + c) unitDisc :=
    Set.EqOn.of_subset_closure hS hcont1 hcont2 Set.inter_subset_left
      ((dense_compl_singleton (wA μ 0)).open_subset_closure_inter isOpen_ball)
  have h0mem : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hc : c = 0 := by
    have := hEq h0mem
    simpa [hφ0, hf0] using this.symm
  have ha : a = 1 := by
    have hev : (fun w => conj (φ (conj w))) =ᶠ[𝓝 (0 : ℂ)] fun w => a * fB (beltramiInv μ) w + c :=
      hEq.eventuallyEq_of_mem (isOpen_ball.mem_nhds h0mem)
    have h1 := hev.deriv_eq
    rw [e13_deriv_conj] at h1
    have hd0 : DifferentiableAt ℂ (fB (beltramiInv μ)) 0 := hfd.differentiableAt (isOpen_ball.mem_nhds h0mem)
    rw [deriv_add_const, deriv_const_mul _ hd0, hf1, map_zero, hφ1] at h1
    simpa using h1.symm
  subst hc
  subst ha
  have hΛeq : ∀ z : ℂ, finPart (mobiusExt (conj b) 0 0 1
      (mobiusExt 0 1 1 0 (OnePoint.map conj (wB μ (mobiusExt 0 1 1 0 (OnePoint.map conj (z : ExtPlane)))))))
        = normalizedWeldingExterior (beltramiInv μ) z := by
    intro z; rw [hrel']; ring
  rw [hbg, e13_gsans_eq hμ, e13_fsans_eq hμ, e13_fsans_eq hν, e13_gsans_eq hν]
  constructor
  · intro z hz hz0
    have h1 := hEq hz
    simp only [one_mul, add_zero] at h1
    rw [← h1]
    have hcz : conj z ≠ 0 := (map_ne_zero conj).mpr hz0
    have hcd : conj z ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, Complex.norm_conj]; exact mem_ball_zero_iff.mp hz
    have hφz : φ (conj z) ≠ 0 := fun h =>
      hcz (hφi hcd (by simp [unitDisc]) (h.trans hφ0.symm))
    have hrz : refl z = 1 / conj z := by simp [refl, one_div]
    rw [hrz, hG' (conj z) hcd hcz]
    have hcb : conj b ≠ 0 := (map_ne_zero conj).mpr hb
    simp only [refl, map_div₀]
    field_simp
  · intro z hz
    rw [gMu_eq_normalizedWeldingExterior hν hz, ← hΛeq z, e13_Lam'_ext hμ b hz]

/-! ### Original relocated (2026-10-26) -/

/-- **(1.3)** (TT:3757). With `j(z) = 1/z̄` and `r(z) = \overline{𝗀_μ'(∞)} z`:
`𝖿^{μ⁻¹} = r ∘ j ∘ 𝗀_μ ∘ j` on `𝔻` and `𝗀_{μ⁻¹} = r ∘ j ∘ 𝖿^μ ∘ j` on `𝔻*`. -/
theorem eq_1_3 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    (∀ z ∈ unitDisc, z ≠ 0 →
        fsans (beltramiInv μ) z = conj (derivAtInfty (gsans μ)) * refl (gsans μ (refl z))) ∧
      ∀ z ∈ unitDiscExterior,
        gsans (beltramiInv μ) z = conj (derivAtInfty (gsans μ)) * refl (fsans μ (refl z)) :=
  w3_eq_1_3 hμ

end Ch2

end TakhtajanTeo
