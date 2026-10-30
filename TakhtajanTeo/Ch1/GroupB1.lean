import TakhtajanTeo.Ch1.S3_TopologicalGroup
import TakhtajanTeo.Ch1.BeltramiDerivative
import TakhtajanTeo.Ch1.BeltramiGroup
import TakhtajanTeo.Ch1.AhlforsWeillCompleted
import TakhtajanTeo.Ch1.S1_1_Completed
import TakhtajanTeo.Ch1.ComponentTBasics
import TakhtajanTeo.Ch1.BeltramiTranslation
import TakhtajanTeo.Ch1.GroupAlgebra


/-!
# Group chain, B1: regularity of `wA μ` on `𝔻*` for harmonic `μ`

[下属2, T₀(1) program, lemma_2_5 step B1]  `grp25_regular_ext`: for harmonic `μ` with `‖μ‖ < 1`, `wA μ` is `C¹` near
every `z ∈ 𝔻*` that is not the pole (`wAS μ z ≠ ∞`), with `dz ≠ 0` there.  Route: the explicit Ahlfors–Weill map `H = M ∘ E`
on `ℍ` (`grp_l333_core_reg`, a strengthened copy of `l333_core` with the regularity conjunct `∂_z E = -1/D²`), the plane map
`F₁ = R ∘ H ∘ awG` (`grp_aw_reg`), and Stoilow (`grp_stoilow`): `wA = (finPart ∘ M) ∘ ψ ∘ F₁` on `𝔻*` with `ψ` conformal.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Strengthens `LiZhongQC.l333_mu_exact`: besides the dilatation of `H = M ∘ E`, this gives that `H` is `C¹` near `z ∈ ℍ`
with `∂_z H ≠ 0` (`∂_z E = -1/D²`, Wronskian `1`).  The proof is that of `l333_mu_exact`, with `t203_dz_dzbar_F`. -/
theorem grp_l333_reg {φ w₁ w₂ H : ℂ → ℂ} {α β κ δ : ℂ} (hdet : α * δ - β * κ ≠ 0)
    (hw₁ : DifferentiableOn ℂ w₁ lowerHalf) (hw₂ : DifferentiableOn ℂ w₂ lowerHalf)
    (hode : ∀ z ∈ lowerHalf, deriv (deriv w₁) z + φ z / 2 * w₁ z = 0 ∧ deriv (deriv w₂) z + φ z / 2 * w₂ z = 0 ∧
      w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1)
    (hH : ∀ z ∈ upperHalf, mobiusExt α β κ δ (l333_E w₁ w₂ z) = ((H z : ℂ) : ExtPlane)) {z : ℂ}
    (hz : z ∈ upperHalf) : ContDiffAt ℝ 1 H z ∧ dz H z ≠ 0 := by
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_pow_nat_eq (α * δ - β * κ) two_pos
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    apply hdet
    rw [← hσ]
    ring
  have hdet' : α / σ * (δ / σ) - β / σ * (κ / σ) = 1 := by
    rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, ← hσ, pow_two]
    exact div_self (mul_ne_zero hσ0 hσ0)
  set A₁ : ℂ → ℂ := fun y => α / σ * w₁ y + β / σ * w₂ y
  set A₂ : ℂ → ℂ := fun y => κ / σ * w₁ y + δ / σ * w₂ y
  have hconjL : ∀ y ∈ upperHalf, conj y ∈ lowerHalf := fun y hy => by
    simp only [upperHalf, lowerHalf, mem_ofPred_eq, conj_im] at hy ⊢
    linarith
  -- `M ∘ E` is the `E` of the normalized pair
  have hME : ∀ y ∈ upperHalf, mobiusExt α β κ δ (l333_E w₁ w₂ y) =
      t203_ratio (A₁ (conj y) + (y - conj y) * deriv A₁ (conj y))
        (A₂ (conj y) + (y - conj y) * deriv A₂ (conj y)) := by
    intro y hy
    have hyL := hconjL y hy
    obtain ⟨e1, -⟩ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ (α / σ) (β / σ) hyL
    obtain ⟨e2, -⟩ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ (κ / σ) (δ / σ) hyL
    rw [l333_E, t203_c1_mobius_ratio hσ0 (l333_mux_pair_ne (hode _ hyL).2.2), e1, e2]
    congr 1 <;> ring
  -- `H = N/D` near `z`
  have hev : H =ᶠ[𝓝 z] fun w => (A₁ (conj w) + (w - conj w) * deriv A₁ (conj w)) /
      (A₂ (conj w) + (w - conj w) * deriv A₂ (conj w)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds hz] with y hy
    have h := (hH y hy).symm.trans (hME y hy)
    have hD : A₂ (conj y) + (y - conj y) * deriv A₂ (conj y) ≠ 0 :=
      t203_c1_ratio_ne (h ▸ OnePoint.coe_ne_infty (H y))
    have h2 := congrArg extToC h
    rw [t203_c1_extToC_ratio hD] at h2
    exact h2
  have hDz : A₂ (conj z) + (z - conj z) * deriv A₂ (conj z) ≠ 0 := by
    have h := (hH z hz).symm.trans (hME z hz)
    exact t203_c1_ratio_ne (h ▸ OnePoint.coe_ne_infty (H z))
  -- the ODE data at `conj z`
  have hzL := hconjL z hz
  have hA₁d : DifferentiableOn ℂ A₁ lowerHalf := (hw₁.const_mul _).add (hw₂.const_mul _)
  have hA₂d : DifferentiableOn ℂ A₂ lowerHalf := (hw₁.const_mul _).add (hw₂.const_mul _)
  obtain ⟨e1, e1'⟩ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ (α / σ) (β / σ) hzL
  obtain ⟨e2, e2'⟩ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ (κ / σ) (δ / σ) hzL
  obtain ⟨o1, o2, hW⟩ := hode (conj z) hzL
  have hn := isOpen_lowerHalf.mem_nhds hzL
  obtain ⟨a1, b1⟩ := t203_ode_hasDerivAt (a := φ (conj z) / 2) (hA₁d.differentiableAt hn)
    ((hA₁d.deriv isOpen_lowerHalf).differentiableAt hn)
    (by rw [e1']; linear_combination α / σ * o1 + β / σ * o2)
  obtain ⟨a2, b2⟩ := t203_ode_hasDerivAt (a := φ (conj z) / 2) (hA₂d.differentiableAt hn)
    ((hA₂d.deriv isOpen_lowerHalf).differentiableAt hn)
    (by rw [e2']; linear_combination κ / σ * o1 + δ / σ * o2)
  have hWA : A₁ (conj z) * deriv A₂ (conj z) - A₂ (conj z) * deriv A₁ (conj z) = 1 := by
    rw [e1, e2]
    exact (neh_wronskian_comb (a := α / σ) (b := β / σ) (c := κ / σ) (d := δ / σ) hW).trans hdet'
  obtain ⟨hg, hdz, hdzbar⟩ := l333_mux_dz_conj z
  obtain ⟨hF1, -⟩ := t203_dz_dzbar_F (A₁ := A₁) (B₁ := deriv A₁) (A₂ := A₂) (B₂ := deriv A₂)
    (g := fun w => conj w) (z := z) (a := φ (conj z) / 2) hg a1 b1 a2 b2 hWA hDz
  have hN := t203_hasFDerivAt_G hg a1 b1
  have hDn := t203_hasFDerivAt_G hg a2 b2
  have hinv : DifferentiableAt ℝ (fun w : ℂ => (A₂ (conj w) + (w - conj w) * deriv A₂ (conj w))⁻¹) z :=
    ((differentiableAt_inv (𝕜 := ℂ) hDz).restrictScalars ℝ).comp z hDn.differentiableAt
  have hFd : DifferentiableAt ℝ (fun w : ℂ => (A₁ (conj w) + (w - conj w) * deriv A₁ (conj w)) /
      (A₂ (conj w) + (w - conj w) * deriv A₂ (conj w))) z := by
    have e : (fun w : ℂ => (A₁ (conj w) + (w - conj w) * deriv A₁ (conj w)) /
        (A₂ (conj w) + (w - conj w) * deriv A₂ (conj w))) =
        fun w : ℂ => (A₁ (conj w) + (w - conj w) * deriv A₁ (conj w)) *
          (A₂ (conj w) + (w - conj w) * deriv A₂ (conj w))⁻¹ := by
      funext w
      rw [div_eq_mul_inv]
    rw [e]
    exact hN.differentiableAt.mul hinv
  have hsm : ∀ A : ℂ → ℂ, DifferentiableOn ℂ A lowerHalf →
      ContDiffAt ℝ 1 (fun w : ℂ => A (conj w) + (w - conj w) * deriv A (conj w)) z := by
    intro A hA
    have h1 : ContDiffAt ℂ 1 A (conj z) := (hA.contDiffOn isOpen_lowerHalf).contDiffAt (isOpen_lowerHalf.mem_nhds hzL)
    have h2 : ContDiffAt ℂ 1 (deriv A) (conj z) :=
      ((hA.deriv isOpen_lowerHalf).contDiffOn isOpen_lowerHalf).contDiffAt (isOpen_lowerHalf.mem_nhds hzL)
    have hc : ContDiffAt ℝ 1 (fun w : ℂ => conj w) z := conjCLE.contDiff.contDiffAt
    exact ((h1.restrict_scalars ℝ).comp z hc).add ((contDiffAt_id.sub hc).mul ((h2.restrict_scalars ℝ).comp z hc))
  have hFs : ContDiffAt ℝ 1 (fun w : ℂ => (A₁ (conj w) + (w - conj w) * deriv A₁ (conj w)) /
      (A₂ (conj w) + (w - conj w) * deriv A₂ (conj w))) z := by
    have e : (fun w : ℂ => (A₁ (conj w) + (w - conj w) * deriv A₁ (conj w)) /
        (A₂ (conj w) + (w - conj w) * deriv A₂ (conj w))) =
        fun w : ℂ => (A₁ (conj w) + (w - conj w) * deriv A₁ (conj w)) *
          (A₂ (conj w) + (w - conj w) * deriv A₂ (conj w))⁻¹ := by
      funext w
      rw [div_eq_mul_inv]
    rw [e]
    exact (hsm A₁ hA₁d).mul ((contDiffAt_inv ℝ hDz).comp z (hsm A₂ hA₂d))
  refine ⟨(hFs).congr_of_eventuallyEq hev, ?_⟩
  obtain ⟨c1, -⟩ := t203_c1_dz_congr hev
  rw [c1, hF1, hdz]
  have hD2 : (A₂ (conj z) + (z - conj z) * deriv A₂ (conj z)) ^ 2 ≠ 0 := pow_ne_zero 2 hDz
  simpa using hD2


/-- Strengthens `LiZhongQC.l333_core` by one conjunct: `H` is `C¹` near every `z ∈ ℍ` with `∂_z H ≠ 0` (`grp_l333_reg`).
The proof is that of `l333_core`, with the final conjunct supplied by `grp_l333_reg`. -/
theorem grp_l333_core_reg {φ : ℂ → ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2) (hφd : DifferentiableOn ℂ φ lowerHalf)
    (hφ : ∀ z ∈ lowerHalf, ‖φ z‖ * z.im ^ 2 ≤ s) :
    ∃ (H : ℂ → ℂ) (K : ℝ), IsKQC H univ K ∧ H '' univ = univ ∧ H 0 = 0 ∧ H 1 = 1 ∧
      DifferentiableOn ℂ H lowerHalf ∧ (∀ z ∈ lowerHalf, schwarzian H z = φ z) ∧
      (∀ z ∈ upperHalf, complexDilatation H z = -2 * (z.im : ℂ) ^ 2 * φ (conj z)) ∧
      ∀ z ∈ upperHalf, ContDiffAt ℝ 1 H z ∧ dz H z ≠ 0 := by
  obtain ⟨w₁, w₂, hw₁, hw₂, hode, hloc, hSf, hmero⟩ := l333_ode hφd
  obtain ⟨hfam, hconv⟩ := l333_family hs0 hs hφ hw₁ hw₂ hode
  obtain ⟨hdisc, hmono, hU⟩ := l333_disc_facts
  have hk0 : 0 ≤ 4 * s / 2 := by positivity
  have hk1 : 4 * s / 2 < 1 := by linarith
  obtain ⟨G, A, T, h, hA, hT, hh, hhs, hG, hGD, hGlim⟩ :=
    l333_limit (D := lowerHalf) (f := fun z => w₁ z / w₂ z) (Dn := l333_disc) (F := l333_F w₁ w₂)
      hk0 hk1 le_rfl ⟨-I, by simp [lowerHalf]⟩ isOpen_lowerHalf hmono (fun n => (hdisc n).2.1) hU
      fun n => ⟨(hfam n).1, (hfam n).2.1, fun z hz => ((hfam n).2.2.1 z hz).trans
        (hmero z ((hdisc n).2.2.2.1 (subset_closure hz))).symm, (hfam n).2.2.2⟩
  obtain ⟨α, β, κ, δ, hdet, H, hH, hHs, hH0, hH1, hM⟩ := l333_normalize hA hT hh hhs hG
  have hGv : ∀ v ∈ lowerHalf, mobiusExt α β κ δ (meroToExt (fun z => w₁ z / w₂ z) v) = ((H v : ℂ) : ExtPlane) := by
    intro v hv
    rw [← hGD v hv, hM]
    rfl
  have hHE : ∀ y ∈ upperHalf, mobiusExt α β κ δ (l333_E w₁ w₂ y) = ((H y : ℂ) : ExtPlane) := fun y hy => by
    rw [← hGlim y _ (hconv y hy), hM]
    rfl
  refine ⟨H, (1 + 4 * s / 2) / (1 - 4 * s / 2), hH, hHs, hH0, hH1,
    fun v hv => (aw_ext_analyticAt isOpen_lowerHalf hloc hGv hv).differentiableAt.differentiableWithinAt,
    fun v hv => (aw_ext_schwarzian isOpen_lowerHalf hloc hdet hGv hv).trans (hSf v hv),
    fun z hz => l333_mu_exact hdet hw₁ hw₂ hode hHE hz, fun z hz => grp_l333_reg hdet hw₁ hw₂ hode hHE hz⟩


theorem grp_stoilow {f g : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hf : IsQuasiconformal f D) (hg : IsQuasiconformal g D)
    (hμ : ∀ᵐ z ∂(volume.restrict D), complexDilatation f z = complexDilatation g z) :
    ∃ φ : ℂ → ℂ, IsConformalOnto φ (f '' D) (g '' D) ∧ ∀ z ∈ D, g z = φ (f z) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K', hK'⟩ := hg
  obtain ⟨hβf, hsolf⟩ := thm10_2_genHomeoSolution_of_isKQC hK
  obtain ⟨-, hsolg⟩ := thm10_2_genHomeoSolution_of_isKQC hK'
  have hK1 : (1 : ℝ) ≤ K := hK.2.1
  have hkpos : (0 : ℝ) < K + 1 := by linarith
  have hk : (K - 1) / (K + 1) < 1 := by
    rw [div_lt_one hkpos]
    linarith
  have hsolg' : IsGenHomeoSolution g (complexDilatation f) D 2 := by
    obtain ⟨hghom, gx, gy, hgp, hgae⟩ := hsolg
    refine ⟨hghom, gx, gy, hgp, ?_⟩
    filter_upwards [hgae, hμ] with z h1 h2
    rw [h2]
    exact h1
  obtain ⟨φ, hφ, hgφ⟩ := same_dilatation_conformal hD hk hβf hsolf hsolg'
  exact ⟨φ, hφ, hgφ⟩


theorem grp_dz_comp_holo {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℂ g (f z)) :
    DifferentiableAt ℝ (fun u => g (f u)) z ∧ dz (fun u => g (f u)) z = deriv g (f z) * dz f z := by
  refine ⟨(hg.restrictScalars ℝ).comp z hf, ?_⟩
  have h := eq6_2_dz_comp hf (hg.restrictScalars ℝ)
  have hb : dzbar g (f z) = 0 := (cauchyRiemann_iff.1 hg).2
  have h2 : dz (g ∘ f) z = deriv g (f z) * dz f z := by
    rw [h, hb, zero_mul, add_zero, dz_eq_deriv hg]
  exact h2

theorem grp_image_open {F : ℂ → ℂ} {K : ℝ} (hK : IsKQC F univ K) (hs : F '' univ = univ) {D : Set ℂ}
    (hD : IsOpen D) : IsOpen (F '' D) := by
  have hinj : InjOn F univ := hK.2.2.1.2.1
  have hc : ContinuousOn (Function.invFunOn F univ) univ := by
    have := hK.2.2.1.2.2.2
    rwa [hs] at this
  have himg : F '' D = (Function.invFunOn F univ) ⁻¹' D := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      show Function.invFunOn F univ (F u) ∈ D
      rw [hinj.leftInvOn_invFunOn (mem_univ u)]
      exact hu
    · intro hw
      have hw' : w ∈ F '' univ := by
        rw [hs]
        trivial
      obtain ⟨u, -, rfl⟩ := hw'
      refine ⟨u, ?_, rfl⟩
      have h1 : Function.invFunOn F univ (F u) ∈ D := hw
      rwa [hinj.leftInvOn_invFunOn (mem_univ u)] at h1
  rw [himg]
  exact (continuousOn_univ.1 hc).isOpen_preimage D hD

theorem grp_holo_cd {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) {x : ℂ} (hx : x ∈ U) :
    ContDiffAt ℝ 1 g x :=
  ((hg.contDiffOn hU).contDiffAt (hU.mem_nhds hx)).restrict_scalars ℝ


theorem grp_aw_reg {φ : AInf unitDisc} (hφ : ‖φ‖ < 2) :
    ∃ F₁ : ℂ → ℂ, (∃ K' : ℝ, IsKQC F₁ univ K') ∧ F₁ '' univ = univ ∧
      (∀ᵐ z ∂(volume.restrict unitDiscExterior), complexDilatation F₁ z = Lambda φ z) ∧
      ∀ z ∈ unitDiscExterior, ContDiffAt ℝ 1 F₁ z ∧ dz F₁ z ≠ 0 := by
  have hnn : 0 ≤ ‖φ‖ := norm_nonneg φ
  obtain ⟨H, K, hH, hHs, hH0, hH1, hHd, hHS, hHμ, hHreg⟩ :=
    grp_l333_core_reg (s := ‖φ‖ / 4) (by positivity) (by linarith) (aw_phi_diff φ)
      (fun z hz => aw_phi_bound φ hz)
  obtain ⟨e, he⟩ := t1_homeomorph hH hHs
  subst he
  obtain ⟨R, hR, F₁, ⟨K', hK'⟩, hF₁s, hF₁i, hRel, hdil⟩ := aw_F1 hH
  have hdilμ := aw_dil_comp hH hHd hHμ
  have hmeas : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  refine ⟨F₁, ⟨K', hK'⟩, hF₁s, ?_, ?_⟩
  · have hz1 : ∀ᵐ z : ℂ, z - 1 ≠ 0 :=
      ae_iff.2 (by simp [sub_eq_zero])
    refine (ae_restrict_iff' hmeas).2 ?_
    filter_upwards [hdil, hdilμ, hz1] with z a b c hzE
    rw [a c, b c, extB, indicator_of_mem hzE]
  · intro z hz
    have hzn : 1 < ‖z‖ := hz
    have hz1 : z - 1 ≠ 0 := by
      intro h
      have : z = 1 := by linear_combination h
      rw [this] at hzn
      simp at hzn
    have hw : awG z ∈ upperHalf := aw_G_im_pos hzn
    obtain ⟨hHcd, hHdz⟩ := hHreg (awG z) hw
    have hHd' : DifferentiableAt ℝ (⇑e) (awG z) := hHcd.differentiableAt one_ne_zero
    have hg := aw_hasDerivAt_G hz1
    have hgA : AnalyticAt ℂ awG z := by
      unfold awG
      exact (analyticAt_const.mul (analyticAt_id.add analyticAt_const)).div
        (analyticAt_id.sub analyticAt_const) hz1
    have hcomp : DifferentiableAt ℝ (fun u => e (awG u)) z :=
      hHd'.comp z (hg.differentiableAt.restrictScalars ℝ)
    have hcs : ContDiffAt ℝ 1 (fun u => e (awG u)) z := hHcd.comp z (hgA.contDiffAt.restrict_scalars ℝ)
    have hcdz : dz (fun u => e (awG u)) z = dz (⇑e) (awG z) * awGd z := by
      have := (eq6_4 hg.differentiableAt hHd').1
      rwa [hg.deriv] at this
    have hRfin : R ((e (awG z) : ℂ) : ExtPlane) ≠ extInf := by
      rw [hRel z hz1]
      exact OnePoint.coe_ne_infty _
    obtain ⟨hPd, hPinj, -⟩ := mobius_finite_conformal hR
    have hPo := mobius_finite_open hR
    have hPat : DifferentiableAt ℂ (fun x : ℂ => finPart (R (x : ExtPlane))) (e (awG z)) :=
      hPd.differentiableAt (hPo.mem_nhds hRfin)
    have hPder : deriv (fun x : ℂ => finPart (R (x : ExtPlane))) (e (awG z)) ≠ 0 :=
      deriv_ne_zero_of_injOn hPo hPd hPinj hRfin
    have hev : F₁ =ᶠ[nhds z] fun u => finPart (R ((e (awG u) : ℂ) : ExtPlane)) := by
      filter_upwards [isOpen_ne.mem_nhds (show z ≠ 1 from fun h => hz1 (by rw [h]; ring))] with u hu
      have := hRel u (sub_ne_zero.2 hu)
      rw [this]
      rfl
    obtain ⟨hd1, hd2⟩ := grp_dz_comp_holo hcomp hPat
    have hPcd : ContDiffAt ℝ 1 (fun x : ℂ => finPart (R (x : ExtPlane))) (e (awG z)) :=
      grp_holo_cd hPo hPd hRfin
    have hcd : ContDiffAt ℝ 1 (fun u => finPart (R ((e (awG u) : ℂ) : ExtPlane))) z :=
      ContDiffAt.comp (g := fun x : ℂ => finPart (R (x : ExtPlane))) z hPcd hcs
    refine ⟨hcd.congr_of_eventuallyEq hev, ?_⟩
    rw [(t203_c1_dz_congr hev).1, hd2, hcdz]
    have hawGd : awGd z ≠ 0 := by
      unfold awGd
      exact div_ne_zero (by simp) (pow_ne_zero 2 hz1)
    exact mul_ne_zero hPder (mul_ne_zero hHdz hawGd)

theorem grp25_regular_ext {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hμ1 : ‖μ‖ < 1) {z : ℂ}
    (hz : z ∈ unitDiscExterior) (hp : wAS μ (z : ExtPlane) ≠ extInf) :
    ContDiffAt ℝ 1 (wA μ) z ∧ dz (wA μ) z ≠ 0 := by
  have hμb : μ ∈ LinfStarBall := by simpa [LinfStarBall] using hμ1
  obtain ⟨φ, hφμ⟩ := Lambda_surjective_harmonic hμ
  have hφ2 : ‖φ‖ < 2 := by
    have := Lambda_norm_eq φ
    rw [hφμ] at this
    linarith
  obtain ⟨F₁, ⟨K', hK'⟩, hF₁s, hdil, hreg⟩ := grp_aw_reg hφ2
  rw [hφμ] at hdil
  obtain ⟨M, hM, W, hW, hwf, -, -, -, -⟩ := wA_spec hμb
  obtain ⟨KW, hKW⟩ := hW.1
  have hDo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  obtain ⟨ψ, hψ, hWψ⟩ := grp_stoilow hDo
    ⟨K', ac_t_isKQC_restrict hK' hDo (subset_univ _)⟩ ⟨KW, ac_t_isKQC_restrict hKW hDo (subset_univ _)⟩
    (by
      filter_upwards [hdil, ae_restrict_of_ae hW.2.2.2.2, ae_restrict_mem hDo.measurableSet] with u a b hu
      rw [a, b]
      exact (extA_eq_on_exterior _ hu).symm)
  obtain ⟨hψd, hψinj, -⟩ := hψ
  have hUo : IsOpen (F₁ '' unitDiscExterior) := grp_image_open hK' hF₁s hDo
  have hzF : F₁ z ∈ F₁ '' unitDiscExterior := ⟨z, hz, rfl⟩
  have hψat : DifferentiableAt ℂ ψ (F₁ z) := hψd.differentiableAt (hUo.mem_nhds hzF)
  have hψder : deriv ψ (F₁ z) ≠ 0 := deriv_ne_zero_of_injOn hUo hψd hψinj hzF
  obtain ⟨hQd, hQinj, -⟩ := mobius_finite_conformal hM
  have hQo := mobius_finite_open hM
  have hWz : W z = ψ (F₁ z) := hWψ z hz
  have hMfin : M ((W z : ℂ) : ExtPlane) ≠ extInf := by
    rw [← hwf z]
    exact hp
  have hQat : DifferentiableAt ℂ (fun x : ℂ => finPart (M (x : ExtPlane))) (ψ (F₁ z)) := by
    rw [← hWz]
    exact hQd.differentiableAt (hQo.mem_nhds hMfin)
  have hQder : deriv (fun x : ℂ => finPart (M (x : ExtPlane))) (ψ (F₁ z)) ≠ 0 := by
    rw [← hWz]
    exact deriv_ne_zero_of_injOn hQo hQd hQinj hMfin
  have hev : wA μ =ᶠ[nhds z] fun u => finPart (M ((ψ (F₁ u) : ℂ) : ExtPlane)) := by
    filter_upwards [hDo.mem_nhds hz] with u hu
    show finPart (wAS μ (u : ExtPlane)) = _
    rw [hwf u, hWψ u hu]
  have hF1d : DifferentiableAt ℝ F₁ z := (hreg z hz).1.differentiableAt one_ne_zero
  obtain ⟨hd1, hd2⟩ := grp_dz_comp_holo hF1d hψat
  obtain ⟨hd3, hd4⟩ := grp_dz_comp_holo hd1 hQat
  have hψcd : ContDiffAt ℝ 1 ψ (F₁ z) := grp_holo_cd hUo hψd hzF
  have hQcd : ContDiffAt ℝ 1 (fun x : ℂ => finPart (M (x : ExtPlane))) (ψ (F₁ z)) := by
    rw [← hWz]
    exact grp_holo_cd hQo hQd hMfin
  have hcd : ContDiffAt ℝ 1 (fun u => finPart (M ((ψ (F₁ u) : ℂ) : ExtPlane))) z :=
    ContDiffAt.comp (g := fun x : ℂ => finPart (M (x : ExtPlane))) z hQcd
      (ContDiffAt.comp (g := ψ) z hψcd (hreg z hz).1)
  refine ⟨hcd.congr_of_eventuallyEq hev, ?_⟩
  have e4 : dz (fun u => finPart (M ((ψ (F₁ u) : ℂ) : ExtPlane))) z =
      deriv (fun x : ℂ => finPart (M (x : ExtPlane))) (ψ (F₁ z)) * dz (fun u => ψ (F₁ u)) z := hd4
  rw [(t203_c1_dz_congr hev).1, e4, hd2]
  exact mul_ne_zero hQder (mul_ne_zero hψder (hreg z hz).2)

end TakhtajanTeo
