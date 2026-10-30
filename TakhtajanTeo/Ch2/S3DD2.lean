import TakhtajanTeo.Ch2.S3DBase
import TakhtajanTeo.Ch2.S3DGFam
import TakhtajanTeo.Ch2.S4ReflectedKernel
import TakhtajanTeo.Appendix.AppACompleted2
import TakhtajanTeo.Ch2.S35Gamma
import TakhtajanTeo.Ch2.S4GThm41

/-! # Density route: (D2) the welded `g`-side term (Program G)

(E1) `s3d_D2_eta`, `d2g_` + `s3d_D2_gd1_C1`, (E2) `s3d_D2_unwelded`, (P) `s3d_D2_pointwise`, (Λ) `s3d_D2_lambda`, (Λ-INT) `s3d_D2_lambda_int`, `s3d_D2`. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- **(E1)** The exterior vector fields `η₁ = ġ/g'`, `η₂ = ∂̄_t g/g'` are holomorphic on `𝔻*`. -/
theorem s3d_D2_eta {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    DifferentiableOn ℂ (fun y : ℂ => (((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) y) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) y / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) y ^ 2 -
        deriv (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) / deriv (gsans (beltramiMul a κ)) y)) unitDiscExterior ∧
    DifferentiableOn ℂ (fun y : ℂ => ((((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) y ^ 2 -
        deriv (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) / deriv (gsans (beltramiMul a κ)) y)) unitDiscExterior := by
  have hd := delta0_bounds
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.2 (has.trans hd.2)
  have hμ : beltramiMul a (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨r, hr, ρ, hρ, R0, hR0, F, G, H, -, -, -, -, -, -, -, ht⟩ := s3g_D_ext hκ hκD ha has haL haD hm hmD
  obtain ⟨-, ⟨hGd, hGi, hGd', hGg⟩, -⟩ := ht 0 (mem_ball_self hr)
  simp only [zero_smul, add_zero] at hGg
  have hRm : AEStronglyMeasurable (RnmFun (toLinf m) a) (volume.restrict unitDiscExterior) :=
    (bc_Rnm_memLp haB (toLinf m)).aestronglyMeasurable
  have hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior),
      ‖RnmFun (toLinf m) a u‖ ≤ (1 / (1 - ‖a‖ ^ 2)) * ‖toLinf m‖ :=
    bc_invFun_pullback_ae haB (bc_Rnm_integrand_bound haB (toLinf m))
  exact ⟨d2e_eta1 _ hρ hGd hGi hGd' hGg (fun u hu => d2e_koebe hpair hu) (d2e_growth hpair) hRm hRb,
    d2e_eta2 _ hρ hGd hGi hGd' hGg hRm hRb⟩

/-- Real inverse function theorem in Wirtinger form: a `C³` map with positive Jacobian has a `C³` local inverse. -/
theorem d2g_ift {F : ℂ → ℂ} {z₀ : ℂ} (hF : ContDiffAt ℝ 3 F z₀)
    (hJ : 0 < ‖dz F z₀‖ ^ 2 - ‖dzbar F z₀‖ ^ 2) :
    ∃ L : ℂ → ℂ, ContDiffAt ℝ 3 L (F z₀) ∧ L (F z₀) = z₀ ∧ ∀ᶠ y in 𝓝 (F z₀), F (L y) = y := by
  have hd : DifferentiableAt ℝ F z₀ := hF.differentiableAt (by norm_num)
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ F z₀ with hA
  have hinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).mpr fun v hv => ?_
    rw [hA, fderiv_eq_dz_dzbar hd v] at hv
    by_contra hv0
    have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have h1 : dz F z₀ * v = -(dzbar F z₀ * conj v) := by linear_combination hv
    have h2 := congrArg norm h1
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_conj] at h2
    have h3 : ‖dz F z₀‖ = ‖dzbar F z₀‖ := mul_right_cancel₀ hvn.ne' h2
    rw [h3] at hJ
    simp at hJ
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective (f := (A : ℂ →ₗ[ℝ] ℂ))).mp hinj
  obtain ⟨e, he⟩ : ∃ e : ℂ ≃L[ℝ] ℂ,
      e = (LinearEquiv.ofBijective (A : ℂ →ₗ[ℝ] ℂ) ⟨hinj, hsurj⟩).toContinuousLinearEquiv := ⟨_, rfl⟩
  have hf' : HasFDerivAt F (e : ℂ →L[ℝ] ℂ) z₀ := by
    refine hd.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    rw [he]
    rfl
  have h3 : (3 : WithTop ℕ∞) ≠ 0 := by norm_num
  obtain ⟨PH, hPH⟩ : ∃ PH : OpenPartialHomeomorph ℂ ℂ, PH = hF.toOpenPartialHomeomorph F hf' h3 := ⟨_, rfl⟩
  have hPHc : ∀ x, PH x = F x := fun x => by rw [hPH]; rfl
  have hsymm : ContDiffAt ℝ 3 PH.symm (F z₀) := by
    rw [hPH]
    exact hF.to_localInverse hf' h3
  have hsrc : z₀ ∈ PH.source := by
    rw [hPH]
    exact hF.mem_toOpenPartialHomeomorph_source hf' h3
  have htgt : F z₀ ∈ PH.target := by
    rw [hPH]
    exact hF.image_mem_toOpenPartialHomeomorph_target hf' h3
  refine ⟨PH.symm, hsymm, ?_, ?_⟩
  · rw [← hPHc z₀]
    exact PH.left_inv hsrc
  · filter_upwards [PH.open_target.mem_nhds htgt] with y hy
    rw [← hPHc]
    exact PH.right_inv hy

/-- A holomorphic first slice of a real-differentiable `J` has derivative `fderiv J ((1, 0), 0)`. -/
theorem d2g_slice1 {J : (ℂ × ℂ) × ℂ → ℂ} {P : ℂ × ℂ} {z : ℂ} (hJ : DifferentiableAt ℝ J (P, z))
    (h1 : DifferentiableAt ℂ (fun b => J ((b, P.2), z)) P.1) :
    ∀ v : ℂ, fderiv ℝ J (P, z) ((v, 0), 0) = deriv (fun b => J ((b, P.2), z)) P.1 * v := by
  have hp : HasFDerivAt (fun b : ℂ => ((b, P.2), z))
      (((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ)).prod (0 : ℂ →L[ℝ] ℂ)) P.1 :=
    ((hasFDerivAt_id P.1).prodMk (hasFDerivAt_const P.2 P.1)).prodMk (hasFDerivAt_const z P.1)
  have hc := HasFDerivAt.comp (g := J) P.1 (hJ.hasFDerivAt) hp
  have hu := hc.unique (h1.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  intro v
  have := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hu
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.coe_restrictScalars'] at this
  rw [this, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]

/-- A holomorphic second slice of a real-differentiable `J` has derivative `fderiv J ((0, 1), 0)`. -/
theorem d2g_slice2 {J : (ℂ × ℂ) × ℂ → ℂ} {P : ℂ × ℂ} {z : ℂ} (hJ : DifferentiableAt ℝ J (P, z))
    (h2 : DifferentiableAt ℂ (fun b => J ((P.1, b), z)) P.2) :
    ∀ v : ℂ, fderiv ℝ J (P, z) ((0, v), 0) = deriv (fun b => J ((P.1, b), z)) P.2 * v := by
  have hp : HasFDerivAt (fun b : ℂ => ((P.1, b), z))
      (((0 : ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ)).prod (0 : ℂ →L[ℝ] ℂ)) P.2 :=
    ((hasFDerivAt_const P.1 P.2).prodMk (hasFDerivAt_id P.2)).prodMk (hasFDerivAt_const z P.2)
  have hc := HasFDerivAt.comp (g := J) P.2 (hJ.hasFDerivAt) hp
  have hu := hc.unique (h2.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  intro v
  have := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hu
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.coe_restrictScalars'] at this
  rw [this, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]

/-- Along the diagonal `P = (t, t̄)`: `∂_t J((t, t̄), z) = ∂₁J`, `∂_t̄ J((t, t̄), z) = ∂₂J` for separately holomorphic `J`. -/
theorem d2g_diag {J : (ℂ × ℂ) × ℂ → ℂ} {t0 z : ℂ} (hJ : DifferentiableAt ℝ J ((t0, conj t0), z))
    (h1 : DifferentiableAt ℂ (fun b => J ((b, conj t0), z)) t0)
    (h2 : DifferentiableAt ℂ (fun b => J ((t0, b), z)) (conj t0)) :
    DifferentiableAt ℝ (fun t => J ((t, conj t), z)) t0 ∧
      dz (fun t => J ((t, conj t), z)) t0 = deriv (fun b => J ((b, conj t0), z)) t0 ∧
      dzbar (fun t => J ((t, conj t), z)) t0 = deriv (fun b => J ((t0, b), z)) (conj t0) := by
  have hp : HasFDerivAt (fun t : ℂ => ((t, conj t), z))
      (((ContinuousLinearMap.id ℝ ℂ).prod Complex.conjCLE.toContinuousLinearMap).prod (0 : ℂ →L[ℝ] ℂ)) t0 :=
    ((hasFDerivAt_id t0).prodMk Complex.conjCLE.hasFDerivAt).prodMk (hasFDerivAt_const z t0)
  have hc := HasFDerivAt.comp (g := J) t0 (hJ.hasFDerivAt) hp
  have e1 := d2g_slice1 (P := (t0, conj t0)) hJ h1
  have e2 := d2g_slice2 (P := (t0, conj t0)) hJ h2
  set d1 := deriv (fun b => J ((b, conj t0), z)) t0 with hd1
  set d2 := deriv (fun b => J ((t0, b), z)) (conj t0) with hd2
  set D := fderiv ℝ J ((t0, conj t0), z) with hD
  have hlin : ∀ v : ℂ, D ((v, conj v), 0) = d1 * v + d2 * conj v := by
    intro v
    have hs : ((v, conj v), (0 : ℂ)) = ((v, 0), 0) + ((0, conj v), 0) := by simp
    rw [hs, map_add, e1 v, e2 (conj v)]
  have hfd : ∀ v : ℂ, fderiv ℝ (fun t => J ((t, conj t), z)) t0 v = d1 * v + d2 * conj v := by
    intro v
    rw [show (fun t => J ((t, conj t), z)) = J ∘ (fun t => ((t, conj t), z)) from rfl, hc.fderiv]
    simpa using hlin v
  refine ⟨hc.differentiableAt, ?_, ?_⟩
  · unfold dz
    rw [hfd, hfd]
    simp only [map_one, Complex.conj_I]
    ring_nf
    rw [I_sq]
    ring
  · unfold dzbar
    rw [hfd, hfd]
    simp only [map_one, Complex.conj_I]
    ring_nf
    rw [I_sq]
    ring

/-- `t ↦ w_{a+tμ}(p)` stays off `∞` near `t = 0` when `w_a(p) ≠ ∞`. -/
theorem d2g_ev_fin {a μ : LinfStar} (haB : a ∈ LinfStarBall) {p : ExtPlane} (hp : wAS a p ≠ extInf) :
    ∀ᶠ t : ℂ in 𝓝 0, a + t • μ ∈ LinfStarBall ∧ wAS (a + t • μ) p ≠ extInf := by
  have hc : Continuous fun t : ℂ => a + t • μ := continuous_const.add (continuous_id.smul continuous_const)
  have hB : ∀ᶠ t : ℂ in 𝓝 0, a + t • μ ∈ LinfStarBall :=
    hc.continuousAt.preimage_mem_nhds (by
      have hO : IsOpen LinfStarBall := isOpen_ball
      rw [zero_smul, add_zero]
      exact hO.mem_nhds haB)
  have hW : ContinuousAt (fun t : ℂ => wAS (a + t • μ) p) 0 := by
    have h1 : ContinuousAt (fun q : LinfStar × ExtPlane => wAS q.1 q.2) (a, p) :=
      AppA.acc_wAS_cont.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨haB, mem_univ _⟩)
    have h2 : ContinuousAt (fun t : ℂ => (a + t • μ, p)) 0 := (hc.prodMk continuous_const).continuousAt
    have h3 := ContinuousAt.comp (f := fun t : ℂ => (a + t • μ, p)) (g := fun q : LinfStar × ExtPlane => wAS q.1 q.2)
      (by simpa using h1) h2
    exact h3
  have hN : ∀ᶠ t : ℂ in 𝓝 0, wAS (a + t • μ) p ≠ extInf :=
    hW.preimage_mem_nhds (isOpen_ne.mem_nhds (by simpa using hp))
  exact hB.and hN

/-- **Γ-reg, finite points.** With the jointly `C³` family `U` (Γ-FAM (F1)) and the `D0` formula for `γ̇ = gd`,
`gd` is `C¹` at `w_a(z₀)` for every finite `z₀ ∈ 𝔻*` with `w_a(z₀) ≠ ∞`. -/
theorem d2g_reg_fin {a μ : LinfStar} (haB : a ∈ LinfStarBall) {gd : ℂ → ℂ}
    (hD0 : ∀ y ∈ unitDiscExterior,
      dz (fun t : ℂ => wA (beltramiMul (a + t • μ) (beltramiInv a)) y) 0 = gd y)
    {r : ℝ} (hr : 0 < r) {D : Set ((ℂ × ℂ) × ℂ)} {U : ℂ × ℂ → ℂ → ℂ} (hDo : IsOpen D)
    (hDE : ∀ q ∈ D, q.2 ∈ unitDiscExterior)
    (hDU : ∀ t : ℂ, ‖t‖ < r → ∀ z ∈ unitDiscExterior, wAS (a + t • μ) (z : ExtPlane) ≠ extInf →
      ((t, conj t), z) ∈ D ∧ U (t, conj t) z = wA (a + t • μ) z)
    (hhol : ∀ q ∈ D, DifferentiableAt ℂ (fun b => U (b, q.1.2) q.2) q.1.1 ∧
      DifferentiableAt ℂ (fun b => U (q.1.1, b) q.2) q.1.2)
    (hJ : ContDiffOn ℝ 3 (fun q : (ℂ × ℂ) × ℂ => U q.1 q.2) D)
    (hjac : ∀ q ∈ D, 0 < ‖dz (U q.1) q.2‖ ^ 2 - ‖dzbar (U q.1) q.2‖ ^ 2)
    {z0 : ℂ} (hz0 : z0 ∈ unitDiscExterior) (hfin : wAS a (z0 : ExtPlane) ≠ extInf) :
    ContDiffAt ℝ 1 gd (wA a z0) := by
  set J : (ℂ × ℂ) × ℂ → ℂ := fun q => U q.1 q.2 with hJdef
  have h00 : ((0 : ℂ), conj (0 : ℂ)) = ((0 : ℂ), (0 : ℂ)) := by simp
  -- the base slice `U (0,0) = w_a` near finite points
  have hbase : ∀ z ∈ unitDiscExterior, wAS a (z : ExtPlane) ≠ extInf →
      ((0, 0), z) ∈ D ∧ U (0, 0) z = wA a z := by
    intro z hz hzf
    have h := hDU 0 (by rw [norm_zero]; exact hr) z hz (by rw [zero_smul, add_zero]; exact hzf)
    rw [h00, zero_smul, add_zero] at h
    exact h
  -- pointwise representation `gd (w_a z) = ∂₁U`
  have hpt : ∀ z ∈ unitDiscExterior, wAS a (z : ExtPlane) ≠ extInf →
      gd (wA a z) = fderiv ℝ J ((0, 0), z) ((1, 0), 0) := by
    intro z hz hzf
    obtain ⟨hzD, -⟩ := hbase z hz hzf
    have hyE : wA a z ∈ unitDiscExterior := by
      rcases wAS_maps_ext haB hz with h | ⟨u, hu, he⟩
      · exact absurd h hzf
      · show 1 < ‖wA a z‖
        simp only [wA, he, finPart_coe]
        exact hu
    have hev : (fun t : ℂ => wA (beltramiMul (a + t • μ) (beltramiInv a)) (wA a z)) =ᶠ[𝓝 0]
        fun t : ℂ => J ((t, conj t), z) := by
      have hr' : ∀ᶠ t : ℂ in 𝓝 0, ‖t‖ < r := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with t ht
        simpa using ht
      filter_upwards [d2g_ev_fin (μ := μ) haB hzf, hr'] with t ht htr
      rw [s35g_gamma_eq haB ht.1 hzf ht.2]
      exact ((hDU t htr z hz ht.2).2).symm
    have hJd : DifferentiableAt ℝ J (((0 : ℂ), conj (0 : ℂ)), z) := by
      rw [h00]
      exact ((hJ.contDiffAt (hDo.mem_nhds hzD)).differentiableAt (by norm_num))
    have hh := hhol _ hzD
    obtain ⟨-, hdz, -⟩ := d2g_diag (J := J) (t0 := 0) (z := z) hJd (by simpa using hh.1) (by simpa using hh.2)
    have hd1 := d2g_slice1 (J := J) (P := (0, 0)) (z := z)
      ((hJ.contDiffAt (hDo.mem_nhds hzD)).differentiableAt (by norm_num)) hh.1 1
    rw [← hD0 _ hyE, show dz (fun t : ℂ => wA (beltramiMul (a + t • μ) (beltramiInv a)) (wA a z)) 0 =
      dz (fun t : ℂ => J ((t, conj t), z)) 0 by unfold dz; rw [hev.fderiv_eq], hdz, hd1, mul_one]
    simp
  -- the base map and its inverse
  obtain ⟨hz0D, hU0⟩ := hbase z0 hz0 hfin
  have hF : ContDiffAt ℝ 3 (U (0, 0)) z0 :=
    (hJ.contDiffAt (hDo.mem_nhds hz0D)).comp z0 (contDiffAt_const.prodMk contDiffAt_id)
  have hj0 : 0 < ‖dz (U (0, 0)) z0‖ ^ 2 - ‖dzbar (U (0, 0)) z0‖ ^ 2 := hjac ((0, 0), z0) hz0D
  obtain ⟨L, hL, hLz, hFL⟩ := d2g_ift (F := U (0, 0)) (z₀ := z0) hF hj0
  rw [hU0] at hL hLz hFL
  -- `Ψ = ∂₁U` is `C²` near `z₀`
  have hΨ : ContDiffAt ℝ 2 (fun z => fderiv ℝ J ((0, 0), z) ((1, 0), 0)) z0 := by
    have h1 := (hJ.contDiffAt (hDo.mem_nhds hz0D)).fderiv_right (m := 2) (by norm_num)
    exact (h1.comp z0 (contDiffAt_const.prodMk contDiffAt_id)).clm_apply contDiffAt_const
  have hLc : ContinuousAt L (wA a z0) := hL.continuousAt
  have hgood : ∀ᶠ z : ℂ in 𝓝 z0, z ∈ unitDiscExterior ∧ wAS a (z : ExtPlane) ≠ extInf := by
    have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
    have hc : ContinuousAt (fun z : ℂ => wAS a (z : ExtPlane)) z0 :=
      (wAS_continuous haB).continuousAt.comp OnePoint.continuous_coe.continuousAt
    have h1 : ∀ᶠ z in 𝓝 z0, z ∈ unitDiscExterior := hE.mem_nhds hz0
    have h2 : ∀ᶠ z : ℂ in 𝓝 z0, wAS a (z : ExtPlane) ≠ extInf := hc.preimage_mem_nhds (isOpen_ne.mem_nhds hfin)
    exact h1.and h2
  have hgoodL : ∀ᶠ y in 𝓝 (wA a z0), L y ∈ unitDiscExterior ∧ wAS a (L y : ExtPlane) ≠ extInf := by
    have := hLc.preimage_mem_nhds (by rw [hLz]; exact hgood)
    exact this
  have hrep : gd =ᶠ[𝓝 (wA a z0)] fun y => fderiv ℝ J ((0, 0), L y) ((1, 0), 0) := by
    filter_upwards [hgoodL, hFL] with y hy hyF
    have hU := (hbase (L y) hy.1 hy.2).2
    calc gd y = gd (U (0, 0) (L y)) := by rw [hyF]
      _ = gd (wA a (L y)) := by rw [hU]
      _ = _ := hpt (L y) hy.1 hy.2
  have hcomp : ContDiffAt ℝ 2 (fun y => fderiv ℝ J ((0, 0), L y) ((1, 0), 0)) (wA a z0) := by
    have := ContDiffAt.comp (wA a z0) (g := fun z => fderiv ℝ J ((0, 0), z) ((1, 0), 0)) (by rw [hLz]; exact hΨ)
      (hL.of_le (by norm_num))
    exact this
  exact (hcomp.congr_of_eventuallyEq hrep).of_le (by norm_num)

/-- The sphere reflection `p ↦ 1/p̄` at a finite nonzero point. -/
theorem d2g_R_coe {w : ℂ} (hw : w ≠ 0) :
    mobiusExt 0 1 1 0 (OnePoint.map conj (w : ExtPlane)) = (((conj w)⁻¹ : ℂ) : ExtPlane) := by
  have hc : (1 : ℂ) * conj w + 0 ≠ 0 := by simpa using hw
  rw [OnePoint.map_some, mobiusExt_coe hc]
  simp [mobiusFn]

/-- The sphere reflection sends `0` to `∞`. -/
theorem d2g_R_zero : mobiusExt 0 1 1 0 (OnePoint.map conj ((0 : ℂ) : ExtPlane)) = extInf := by
  rw [OnePoint.map_some, map_zero, mobiusExt_coe_of_eq_zero (by simp)]

/-- Sphere form of G3: `w_{l * a⁻¹} ∘ w_a = w_l`. -/
theorem d2g_G3S {a l : LinfStar} (ha : a ∈ LinfStarBall) (hl : l ∈ LinfStarBall) (p : ExtPlane) :
    wAS (beltramiMul l (beltramiInv a)) (wAS a p) = wAS l p := by
  rw [grp_wAS_mul hl (grp_inv_mem ha), Function.comp_apply]
  have h := congrFun (grp_wAS_inv_right ha) p
  simp only [Function.comp_apply, id] at h
  rw [h]

/-- **Γ-reg at the pole image `p_a = w_a(∞)`** via the reflected chart and the `𝔻`-family (Γ-FAM (F2)). -/
theorem d2g_reg_inf {a μ : LinfStar} (haB : a ∈ LinfStarBall) {gd : ℂ → ℂ}
    (hD0 : ∀ y ∈ unitDiscExterior,
      dz (fun t : ℂ => wA (beltramiMul (a + t • μ) (beltramiInv a)) y) 0 = gd y)
    {r : ℝ} (hr : 0 < r) {D : Set ((ℂ × ℂ) × ℂ)} {U : ℂ × ℂ → ℂ → ℂ} (hDo : IsOpen D)
    (hDE : ∀ q ∈ D, q.2 ∈ unitDisc)
    (hDU : ∀ t : ℂ, ‖t‖ < r → ∀ z ∈ unitDisc, wAS (a + t • μ) (z : ExtPlane) ≠ extInf →
      ((t, conj t), z) ∈ D ∧ U (t, conj t) z = wA (a + t • μ) z)
    (hhol : ∀ q ∈ D, DifferentiableAt ℂ (fun b => U (b, q.1.2) q.2) q.1.1 ∧
      DifferentiableAt ℂ (fun b => U (q.1.1, b) q.2) q.1.2)
    (hJ : ContDiffOn ℝ 3 (fun q : (ℂ × ℂ) × ℂ => U q.1 q.2) D)
    (hjac : ∀ q ∈ D, 0 < ‖dz (U q.1) q.2‖ ^ 2 - ‖dzbar (U q.1) q.2‖ ^ 2)
    (hpole : wAS a extInf ≠ extInf) :
    ContDiffAt ℝ 1 gd (finPart (wAS a extInf)) := by
  set J : (ℂ × ℂ) × ℂ → ℂ := fun q => U q.1 q.2 with hJdef
  have h00 : ((0 : ℂ), conj (0 : ℂ)) = ((0 : ℂ), (0 : ℂ)) := by simp
  have hfinD : ∀ ν : LinfStar, ν ∈ LinfStarBall → ∀ z ∈ unitDisc, wAS ν (z : ExtPlane) = ((wA ν z : ℂ) : ExtPlane) ∧
      ‖wA ν z‖ < 1 := by
    intro ν hν z hz
    obtain ⟨u, hu, he⟩ := wAS_maps_disc hν (mem_ball_zero_iff.1 hz)
    refine ⟨?_, ?_⟩
    · simp only [wA, he, finPart_coe]
    · simp only [wA, he, finPart_coe]; exact hu
  have hbase : ∀ z ∈ unitDisc, ((0, 0), z) ∈ D ∧ U (0, 0) z = wA a z := by
    intro z hz
    have hzf : wAS a (z : ExtPlane) ≠ extInf := by rw [(hfinD a haB z hz).1]; exact OnePoint.coe_ne_infty _
    have h := hDU 0 (by rw [norm_zero]; exact hr) z hz (by rw [zero_smul, add_zero]; exact hzf)
    rw [h00, zero_smul, add_zero] at h
    exact h
  -- the reflected chart: `w_a(∞) = 1/c₀̄`, `c₀ = w_a(0) ≠ 0`
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  set c0 := wA a 0 with hc0
  have hinf : wAS a extInf = mobiusExt 0 1 1 0 (OnePoint.map conj ((c0 : ℂ) : ExtPlane)) := by
    rw [← d2g_R_zero, wAS_refl_comm haB, (hfinD a haB 0 h0D).1]
  have hc00 : c0 ≠ 0 := by
    intro h
    rw [h, d2g_R_zero] at hinf
    exact hpole hinf
  have hy0 : finPart (wAS a extInf) = (conj c0)⁻¹ := by
    rw [hinf, d2g_R_coe hc00, finPart_coe]
  -- pointwise representation through the reflected chart
  have hpt : ∀ ζ ∈ unitDisc, wA a ζ ≠ 0 →
      gd (conj (wA a ζ))⁻¹ = -(conj (fderiv ℝ J ((0, 0), ζ) ((0, 1), 0))) * ((conj (U (0, 0) ζ)) ^ 2)⁻¹ := by
    intro ζ hζ hx0
    obtain ⟨hζD, hU0ζ⟩ := hbase ζ hζ
    set x := wA a ζ with hx
    have hxn : ‖x‖ < 1 := (hfinD a haB ζ hζ).2
    have hyE : (conj x)⁻¹ ∈ unitDiscExterior := by
      show 1 < ‖(conj x)⁻¹‖
      rw [norm_inv, Complex.norm_conj]
      exact one_lt_inv_iff₀.2 ⟨norm_pos_iff.2 hx0, hxn⟩
    have hJd : DifferentiableAt ℝ J (((0 : ℂ), conj (0 : ℂ)), ζ) := by
      rw [h00]
      exact ((hJ.contDiffAt (hDo.mem_nhds hζD)).differentiableAt (by norm_num))
    have hh := hhol _ hζD
    obtain ⟨hGd, -, hGbar⟩ := d2g_diag (J := J) (t0 := 0) (z := ζ) hJd (by simpa using hh.1) (by simpa using hh.2)
    have hG0 : J (((0 : ℂ), conj (0 : ℂ)), ζ) = x := by rw [h00]; exact hU0ζ
    have hGne : ∀ᶠ t : ℂ in 𝓝 0, J ((t, conj t), ζ) ≠ 0 := by
      have hc := hGd.continuousAt
      exact hc.preimage_mem_nhds (isOpen_ne.mem_nhds (by rw [hG0]; exact hx0))
    have hr' : ∀ᶠ t : ℂ in 𝓝 0, ‖t‖ < r := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with t ht
      simpa using ht
    have hev : (fun t : ℂ => wA (beltramiMul (a + t • μ) (beltramiInv a)) (conj x)⁻¹) =ᶠ[𝓝 0]
        fun t : ℂ => (conj (J ((t, conj t), ζ)))⁻¹ := by
      filter_upwards [d2g_ev_fin (μ := μ) (p := ((0 : ℂ) : ExtPlane)) haB
        (by rw [(hfinD a haB 0 h0D).1]; exact OnePoint.coe_ne_infty _), hr', hGne] with t ht htr htn
      have hfz := hfinD _ ht.1 ζ hζ
      have hUt := hDU t htr ζ hζ (by rw [hfz.1]; exact OnePoint.coe_ne_infty _)
      have hsph : wAS a (mobiusExt 0 1 1 0 (OnePoint.map conj ((ζ : ℂ) : ExtPlane))) =
          (((conj x)⁻¹ : ℂ) : ExtPlane) := by
        rw [wAS_refl_comm haB, (hfinD a haB ζ hζ).1, d2g_R_coe hx0]
      have hval : wAS (beltramiMul (a + t • μ) (beltramiInv a)) (((conj x)⁻¹ : ℂ) : ExtPlane) =
          (((conj (J ((t, conj t), ζ)))⁻¹ : ℂ) : ExtPlane) := by
        rw [← hsph, d2g_G3S haB ht.1, wAS_refl_comm ht.1, hfz.1, ← hUt.2]
        exact d2g_R_coe htn
      show finPart _ = _
      rw [hval, finPart_coe]
    have hcd : DifferentiableAt ℝ (fun t : ℂ => conj (J ((t, conj t), ζ))) 0 :=
      Complex.conjCLE.differentiableAt.comp 0 hGd
    have hinvd : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) (conj (J ((0, conj 0), ζ))) := by
      refine differentiableAt_inv ?_
      rw [hG0]
      exact (map_ne_zero _).2 hx0
    have hchain := (ra_dz_comp_holo (g := fun w : ℂ => w⁻¹) (f := fun t : ℂ => conj (J ((t, conj t), ζ)))
      (z := 0) hinvd hcd).1
    have hdzc : dz (fun t : ℂ => conj (J ((t, conj t), ζ))) 0 = conj (dzbar (fun t => J ((t, conj t), ζ)) 0) :=
      s4g_dz_conj _ 0
    have hd2 := d2g_slice2 (J := J) (P := (0, 0)) (z := ζ)
      ((hJ.contDiffAt (hDo.mem_nhds hζD)).differentiableAt (by norm_num)) hh.2 1
    rw [← hD0 _ hyE, show dz (fun t : ℂ => wA (beltramiMul (a + t • μ) (beltramiInv a)) (conj x)⁻¹) 0 =
      dz ((fun w : ℂ => w⁻¹) ∘ fun t : ℂ => conj (J ((t, conj t), ζ))) 0 by unfold dz; rw [hev.fderiv_eq]; rfl,
      hchain, hdzc, hGbar, deriv_inv, hG0]
    have e1 : deriv (fun b => J ((0, b), ζ)) (conj 0) = fderiv ℝ J ((0, 0), ζ) ((0, 1), 0) := by
      rw [map_zero, hd2, mul_one]
    rw [e1, ← hU0ζ]
    ring
  -- smoothness of the representation
  obtain ⟨h0D', hU00⟩ := hbase 0 h0D
  have hF : ContDiffAt ℝ 3 (U (0, 0)) 0 :=
    (hJ.contDiffAt (hDo.mem_nhds h0D')).comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hj0 : 0 < ‖dz (U (0, 0)) 0‖ ^ 2 - ‖dzbar (U (0, 0)) 0‖ ^ 2 := hjac ((0, 0), 0) h0D'
  obtain ⟨L, hL, hLz, hFL⟩ := d2g_ift (F := U (0, 0)) (z₀ := 0) hF hj0
  rw [hU00] at hL hLz hFL
  -- `ρ(y) = (ȳ)⁻¹` maps `y₀` to `c₀`
  have hy0ne : (conj c0)⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero _).2 hc00)
  have hρ : ContDiffAt ℝ 3 (fun y : ℂ => (conj y)⁻¹) (conj c0)⁻¹ :=
    (Complex.conjCLE.contDiff.contDiffAt (n := 3)).inv (by simpa using hy0ne)
  have hρ0 : (conj (conj c0)⁻¹)⁻¹ = c0 := by simp
  have hΞ : ContDiffAt ℝ 2 (fun ζ => -(conj (fderiv ℝ J ((0, 0), ζ) ((0, 1), 0))) *
      ((conj (U (0, 0) ζ)) ^ 2)⁻¹) 0 := by
    have h1 := (hJ.contDiffAt (hDo.mem_nhds h0D')).fderiv_right (m := 2) (by norm_num)
    have hnum : ContDiffAt ℝ 2 (fun ζ => fderiv ℝ J ((0, 0), ζ) ((0, 1), 0)) 0 :=
      (h1.comp 0 (contDiffAt_const.prodMk contDiffAt_id)).clm_apply contDiffAt_const
    have hden : ContDiffAt ℝ 2 (fun ζ => (conj (U (0, 0) ζ)) ^ 2) 0 :=
      ((Complex.conjCLE.contDiff.contDiffAt).comp 0 (hF.of_le (by norm_num))).pow 2
    refine ((Complex.conjCLE.contDiff.contDiffAt).comp 0 hnum).neg.mul (hden.inv ?_)
    rw [hU00]
    exact pow_ne_zero 2 ((map_ne_zero _).2 hc00)
  have hLc : ContinuousAt L c0 := hL.continuousAt
  have hgood : ∀ᶠ y in 𝓝 (conj c0)⁻¹, (L (conj y)⁻¹ ∈ unitDisc ∧ U (0, 0) (L (conj y)⁻¹) = (conj y)⁻¹) ∧ y ≠ 0 := by
    have hρc : ContinuousAt (fun y : ℂ => (conj y)⁻¹) (conj c0)⁻¹ := hρ.continuousAt
    have h1 : ∀ᶠ y in 𝓝 (conj c0)⁻¹, L (conj y)⁻¹ ∈ unitDisc := by
      have hLρ : ContinuousAt (fun y : ℂ => L (conj y)⁻¹) (conj c0)⁻¹ :=
        ContinuousAt.comp (g := L) (by rw [hρ0]; exact hLc) hρc
      exact hLρ.preimage_mem_nhds (isOpen_ball.mem_nhds (by rw [hρ0, hLz]; exact h0D))
    have h2 : ∀ᶠ y in 𝓝 (conj c0)⁻¹, U (0, 0) (L (conj y)⁻¹) = (conj y)⁻¹ := by
      have h := hρc.tendsto
      rw [hρ0] at h
      exact h.eventually hFL
    have h3 : ∀ᶠ y in 𝓝 (conj c0)⁻¹, y ≠ 0 := isOpen_ne.mem_nhds hy0ne
    exact (h1.and h2).and h3
  have hrep : gd =ᶠ[𝓝 (conj c0)⁻¹] fun y => -(conj (fderiv ℝ J ((0, 0), L (conj y)⁻¹) ((0, 1), 0))) *
      ((conj (U (0, 0) (L (conj y)⁻¹))) ^ 2)⁻¹ := by
    filter_upwards [hgood] with y hyy
    obtain ⟨hy, hy0⟩ := hyy
    have hU := (hbase _ hy.1).2
    have hwne : wA a (L (conj y)⁻¹) ≠ 0 := by
      rw [← hU, hy.2]
      exact inv_ne_zero ((map_ne_zero _).2 hy0)
    have e := hpt _ hy.1 hwne
    rw [← hU, hy.2] at e
    simp only [map_inv₀, Complex.conj_conj, inv_inv] at e
    rw [hy.2]
    simp only [map_inv₀, Complex.conj_conj]
    exact e
  have hcomp : ContDiffAt ℝ 2 (fun y => -(conj (fderiv ℝ J ((0, 0), L (conj y)⁻¹) ((0, 1), 0))) *
      ((conj (U (0, 0) (L (conj y)⁻¹))) ^ 2)⁻¹) (conj c0)⁻¹ := by
    have hLρ : ContDiffAt ℝ 3 (fun y : ℂ => L (conj y)⁻¹) (conj c0)⁻¹ :=
      ContDiffAt.comp (g := L) (conj c0)⁻¹ (by rw [hρ0]; exact hL) hρ
    exact ContDiffAt.comp (conj c0)⁻¹ (by rw [hρ0, hLz]; exact hΞ) (hLρ.of_le (by norm_num))
  rw [hy0]
  exact (hcomp.congr_of_eventuallyEq hrep).of_le (by norm_num)

/-- **(Γ-reg)** [下属6, export for (Λ)] `γ̇ = gd1` is `C¹` on `𝔻*` (from `γ̇ ∘ w_a = ∂_t U_t`, S35Gamma G1a/G2/G3, and
the inverse function theorem for `w_a`). -/
theorem s3d_D2_gd1_C1 {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    ContDiffOn ℝ 1 (fun y : ℂ => -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) unitDiscExterior := by
  have hd := delta0_bounds
  have ha1 : ‖a‖ < 1 := has.trans hd.2
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.2 ha1
  have hμh : toLinf m ∈ harmonicBeltrami := by
    obtain ⟨ψ, -, hψ⟩ := hmD
    rw [hψ]
    exact Lambda_mem_harmonic _
  have hD0 : ∀ y ∈ unitDiscExterior,
      dz (fun t : ℂ => wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) y) 0 =
        -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) :=
    fun y hy => (s3d_D0 hκ hκD ha has haL haD hm hmD y hy).2.1
  obtain ⟨r, hr, D, U, hDo, hDE, hDU, hhol, hJ, hjac⟩ := d2g_family_ext ha ha1 hμh
  obtain ⟨r', hr', D', U', hDo', hDE', hDU', hhol', hJ', hjac'⟩ := d2g_family_disc ha ha1 hμh
  intro y hy
  have hy1 : 1 < ‖y‖ := hy
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨p, hp⟩ := (wAS_bijective a).2 (y : ExtPlane)
  induction p using OnePoint.rec with
  | infty =>
    have hpole : wAS a extInf ≠ extInf := by
      intro h
      exact OnePoint.coe_ne_infty y (hp.symm.trans h)
    have h := d2g_reg_inf haB hD0 hr' hDo' hDE' hDU' hhol' hJ' hjac' hpole
    have hyv : finPart (wAS a extInf) = y := by
      show finPart (wAS a OnePoint.infty) = y
      rw [hp, finPart_coe]
    rwa [hyv] at h
  | coe z =>
    have hz : z ∈ unitDiscExterior := by
      show 1 < ‖z‖
      by_contra hle
      rw [not_lt] at hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨u, hu, he⟩ := wAS_maps_disc haB hlt
        rw [hp] at he
        have := OnePoint.coe_injective he
        rw [← this] at hu
        linarith
      · obtain ⟨u, hu, he⟩ := wAS_maps_circle haB heq
        rw [hp] at he
        have := OnePoint.coe_injective he
        rw [← this] at hu
        linarith
    have hfin : wAS a (z : ExtPlane) ≠ extInf := by
      rw [hp]
      exact OnePoint.coe_ne_infty y
    have h := d2g_reg_fin haB hD0 hr hDo hDE hDU hhol hJ hjac hz hfin
    have hyv : wA a z = y := by
      show finPart (wAS a (z : ExtPlane)) = y
      rw [hp, finPart_coe]
    rwa [hyv] at h

/-- **(E2)** The unwelded first variation of `𝒜(g_t)` on `𝔻*`. -/
theorem s3d_D2_unwelded {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    ∀ z ∈ unitDiscExterior,
      DifferentiableAt ℝ (fun t : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) 0 ∧
      dz (fun t : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) 0 =
        deriv (fun x : ℂ => deriv (fun y : ℂ => (((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) y) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) y / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) y ^ 2 -
        deriv (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) / deriv (gsans (beltramiMul a κ)) y)) x + preSchwarzian (gsans (beltramiMul a κ)) x * (((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) x) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) x / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) x ^ 2 -
        deriv (gsans (beltramiMul a κ)) x * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((x + 1) * (x + I) * (x - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - x))))) / deriv (gsans (beltramiMul a κ)) x)) z ∧
      dzbar (fun t : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) 0 =
        deriv (fun x : ℂ => deriv (fun y : ℂ => ((((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) y ^ 2 -
        deriv (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) / deriv (gsans (beltramiMul a κ)) y)) x + preSchwarzian (gsans (beltramiMul a κ)) x * ((((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) x ^ 2 -
        deriv (gsans (beltramiMul a κ)) x * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((x + 1) * (x + I) * (x - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - x))))) / deriv (gsans (beltramiMul a κ)) x)) z := by
  intro z hz
  obtain ⟨r, hr, ρ, hρ, R0, hR0, F, G, H, -, -, -, -, -, -, -, hEt⟩ := s3g_D_ext hκ hκD ha has haL haD hm hmD
  have hηs := s3d_D2_eta hκ hκD ha has haL haD hm hmD
  have hV := (s3d_pair_variation hκ hκD ha has haL haD hm hmD).2.2.2
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hz1 : 1 < ‖z‖ := hz
  -- holomorphy of `g_t` on `𝔻*` (from the `G` family of `s3g_D_ext`)
  have hGt : ∀ t : ℂ, ‖t‖ < r →
      DifferentiableOn ℂ (gsans (beltramiMul (a + t • toLinf m) κ)) unitDiscExterior := by
    intro t ht
    obtain ⟨-, ⟨hGd, -, -, hGe⟩, -⟩ := hEt t (mem_ball_zero_iff.2 ht)
    exact (hGd.mono fun w hw => show ρ < ‖w‖ from lt_trans hρ hw).congr fun w hw => (hGe hw).symm
  have h0 : a + (0 : ℂ) • toLinf m = a := by rw [zero_smul, add_zero]
  have hgD : DifferentiableOn ℂ (gsans (beltramiMul a κ)) unitDiscExterior := by
    have h := hGt 0 (by rw [norm_zero]; exact hr)
    rwa [h0] at h
  have hg' : ∀ x ∈ unitDiscExterior, deriv (gsans (beltramiMul a κ)) x ≠ 0 := by
    intro x hx
    obtain ⟨-, ⟨-, -, hGd', hGe⟩, -⟩ := hEt 0 (mem_ball_self hr)
    rw [h0] at hGe
    have heq : G 0 =ᶠ[𝓝 x] gsans (beltramiMul a κ) := Filter.mem_of_superset (hE.mem_nhds hx) fun w hw => hGe hw
    rw [← heq.deriv_eq]
    exact hGd' x (lt_trans hρ hx)
  obtain ⟨X, hX⟩ : ∃ X : ℂ → ℂ, X = fun y : ℂ => (-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) y) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) y / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) y ^ 2 -
        deriv (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℂ → ℂ, Y = fun y : ℂ => ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) y ^ 2 -
        deriv (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) := ⟨_, rfl⟩
  -- `X = η₁ g'`, `Y = η₂ g'` are holomorphic on `𝔻*` by (E1)
  have hXd : DifferentiableOn ℂ X unitDiscExterior := by
    refine (hηs.1.mul (hgD.deriv hE)).congr fun y hy => ?_
    rw [hX]
    exact (div_mul_cancel₀ _ (hg' y hy)).symm
  have hYd : DifferentiableOn ℂ Y unitDiscExterior := by
    refine (hηs.2.mul (hgD.deriv hE)).congr fun y hy => ?_
    rw [hY]
    exact (div_mul_cancel₀ _ (hg' y hy)).symm
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℝ, s0 = (‖z‖ - 1) / 8 := ⟨_, rfl⟩
  have hs0p : 0 < s0 := by rw [hs0]; linarith
  have hball : ball z (3 * (2 * s0)) ⊆ unitDiscExterior := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    show 1 < ‖w‖
    have h1 := norm_sub_norm_le z w
    rw [norm_sub_rev] at h1
    linarith
  have hball2 : ball z (3 * s0) ⊆ unitDiscExterior := (ball_subset_ball (by linarith)).trans hball
  -- the uniform expansion of (V) on the annulus around `z`
  have hV2 : ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ w ∈ closedBall z (2 * (2 * s0)),
      ‖gsans (beltramiMul (a + t • toLinf m) κ) w - gsans (beltramiMul a κ) w - (t * X w + conj t * Y w)‖ ≤
        ε * ‖t‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := hV (‖z‖ - 4 * s0) (‖z‖ + 4 * s0) (by rw [hs0]; linarith) ε hε
    refine ⟨δ, hδ, fun t ht w hw => ?_⟩
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 := norm_sub_norm_le z w
    have h2 := norm_sub_norm_le w z
    rw [norm_sub_rev] at h1
    have h3 := hb t ht w (by linarith) (by linarith)
    rw [hX, hY]
    exact h3
  -- Cauchy estimates: first and second `z`-derivatives
  have hd1 := s3d2u_step (G := fun t => gsans (beltramiMul (a + t • toLinf m) κ)) (G0 := gsans (beltramiMul a κ))
    (X := X) (Y := Y) (c := z) (s := 2 * s0) (r := r) (by positivity) hr (fun t ht => (hGt t ht).mono hball)
    (hgD.mono hball) (hXd.mono hball) (hYd.mono hball) hV2
  have hd2 := s3d2u_step (G := fun t => deriv (gsans (beltramiMul (a + t • toLinf m) κ)))
    (G0 := deriv (gsans (beltramiMul a κ))) (X := deriv X) (Y := deriv Y) (c := z) (s := s0) (r := r) hs0p hr
    (fun t ht => ((hGt t ht).deriv hE).mono hball2) ((hgD.deriv hE).mono hball2) ((hXd.deriv hE).mono hball2)
    ((hYd.deriv hE).mono hball2) hd1
  obtain ⟨hF1z, hF1⟩ := s3d2u_hasFDeriv (F := fun t => deriv (gsans (beltramiMul (a + t • toLinf m) κ)) z)
    (c0 := deriv (gsans (beltramiMul a κ)) z) (A := deriv X z) (B := deriv Y z) (fun ε hε => by
      obtain ⟨δ, hδ, hb⟩ := hd1 ε hε
      exact ⟨δ, hδ, fun t ht => hb t ht z (mem_closedBall_self (by positivity))⟩)
  obtain ⟨hF2z, hF2⟩ := s3d2u_hasFDeriv
    (F := fun t => deriv (deriv (gsans (beltramiMul (a + t • toLinf m) κ))) z)
    (c0 := deriv (deriv (gsans (beltramiMul a κ))) z) (A := deriv (deriv X) z) (B := deriv (deriv Y) z)
    (fun ε hε => by
      obtain ⟨δ, hδ, hb⟩ := hd2 ε hε
      exact ⟨δ, hδ, fun t ht => hb t ht z (mem_closedBall_self hs0p.le)⟩)
  have hPS : HasFDerivAt (fun t : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z)
      (((deriv (deriv X) z * deriv (gsans (beltramiMul a κ)) z - deriv X z * deriv (deriv (gsans (beltramiMul a κ))) z) /
          deriv (gsans (beltramiMul a κ)) z ^ 2) • (1 : ℂ →L[ℝ] ℂ) +
        ((deriv (deriv Y) z * deriv (gsans (beltramiMul a κ)) z - deriv Y z * deriv (deriv (gsans (beltramiMul a κ))) z) /
          deriv (gsans (beltramiMul a κ)) z ^ 2) • (conjCLE : ℂ →L[ℝ] ℂ)) 0 :=
    s3d2u_div hF1 hF2 hF1z hF2z (hg' z hz)
  obtain ⟨hdz, hdzb⟩ := s3d2u_dz hPS
  refine ⟨hPS.differentiableAt, ?_, ?_⟩
  · rw [hdz]
    have h := s3d2u_rhs hE hz hgD hXd hg'
    rw [hX] at h ⊢
    exact h.symm
  · rw [hdzb]
    have h := s3d2u_rhs hE hz hgD hYd hg'
    rw [hY] at h ⊢
    exact h.symm

/-- [(P) helper] `d2e_param` with the value of the derivative: `(∫ k(·, y))' = ∫ ∂_y k(·, z₀)`. -/
theorem d2p_param {k : ℂ → ℂ → ℂ} {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) {z0 : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall z0 (2 * r) ⊆ U) (hkd : ∀ᵐ u ∂μ, DifferentiableOn ℂ (k u) U)
    (hkm : ∀ y ∈ U, AEStronglyMeasurable (fun u => k u y) μ) {B : ℂ → ℝ} (hBi : Integrable B μ)
    (hB : ∀ᵐ u ∂μ, ∀ y ∈ closedBall z0 (2 * r), ‖k u y‖ ≤ B u) :
    Integrable (fun u => k u z0) μ ∧ Integrable (fun u => deriv (k u) z0) μ ∧
      HasDerivAt (fun y => ∫ u, k u y ∂μ) (∫ u, deriv (k u) z0 ∂μ) z0 := by
  have hz0 : z0 ∈ U := hball (mem_closedBall_self (by positivity))
  have htri : ∀ a b c : ℂ, ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := fun a b c => by
    have := norm_add_le (a - b) (b - c)
    rwa [show a - b + (b - c) = a - c by ring] at this
  have hbU : ∀ y ∈ ball z0 r, closedBall y r ⊆ closedBall z0 (2 * r) := fun y hy w hw => by
    have h1 := mem_closedBall_iff_norm.1 hw
    have h2 := mem_ball_iff_norm.1 hy
    exact mem_closedBall_iff_norm.2 (by linarith [htri w y z0])
  have hyU : ∀ y ∈ ball z0 r, y ∈ U := fun y hy => hball (hbU y hy (mem_closedBall_self hr.le))
  have hdb : ∀ᵐ u ∂μ, ∀ y ∈ ball z0 r, ‖deriv (k u) y‖ ≤ B u / r := by
    filter_upwards [hkd, hB] with u hu hBu y hy
    have hdc : DiffContOnCl ℂ (k u) (ball y r) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ hr.ne']
      exact hu.mono ((hbU y hy).trans hball)
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc
      (fun w hw => hBu w (hbU y hy (sphere_subset_closedBall hw)))
  have hdm : AEStronglyMeasurable (fun u => deriv (k u) z0) μ := by
    set s : ℕ → ℂ := fun n => z0 + ((r / ((n : ℝ) + 2) : ℝ) : ℂ) with hs
    have hsp : ∀ n : ℕ, 0 < r / ((n : ℝ) + 2) := fun n => div_pos hr (by positivity)
    have hsU : ∀ n, s n ∈ U := by
      intro n
      apply hyU
      rw [mem_ball_iff_norm, hs]
      simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hsp n)]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsne : ∀ n, s n ≠ z0 := by
      intro n h
      rw [hs] at h
      have : ((r / ((n : ℝ) + 2) : ℝ) : ℂ) = 0 := by linear_combination h
      exact (hsp n).ne' (by exact_mod_cast this)
    have hrt : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have hsc : Tendsto s atTop (𝓝 z0) := by
      have := ((Complex.continuous_ofReal.tendsto 0).comp hrt).const_add z0
      simpa [hs, Function.comp_def] using this
    have hsn : Tendsto s atTop (𝓝[≠] z0) :=
      tendsto_nhdsWithin_iff.2 ⟨hsc, Eventually.of_forall fun n => hsne n⟩
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n u => (s n - z0)⁻¹ * (k u (s n) - k u z0)) (fun n => ?_) ?_
    · exact ((hkm _ (hsU n)).sub (hkm z0 hz0)).const_mul _
    · filter_upwards [hkd] with u hu
      have hda := (hu.differentiableAt (hU.mem_nhds hz0)).hasDerivAt
      have ht := (hasDerivAt_iff_tendsto_slope.1 hda).comp hsn
      refine ht.congr fun n => ?_
      simp only [Function.comp_apply, slope_def_field, div_eq_inv_mul]
  have hF_int : Integrable (fun u => k u z0) μ := by
    refine hBi.mono' (hkm z0 hz0) ?_
    filter_upwards [hB] with u hu using hu z0 (mem_closedBall_self (by positivity))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun y u => k u y) (F' := fun y u => deriv (k u) y) (x₀ := z0)
    (bound := fun u => B u / r) (ball_mem_nhds z0 hr)
    (by filter_upwards [hU.mem_nhds hz0] with y hy using hkm y hy) hF_int hdm hdb (hBi.div_const r)
    (by
      filter_upwards [hkd] with u hu y hy
      exact (hu.differentiableAt (hU.mem_nhds (hyU y hy))).hasDerivAt)
  exact ⟨hF_int, key.1, key.2⟩

/-- [(P) helper] `d2e_core` with the value of the derivative (via `d2p_param`). -/
theorem d2p_core {g G R : ℂ → ℂ} {ρ Rb : ℝ} (hρ : ρ < 1) (hG : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖})
    (hGi : InjOn G {z : ℂ | ρ < ‖z‖}) (hGd : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0)
    (hGg : EqOn G g unitDiscExterior) (hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖g u‖)
    (hinf : ∃ c > 0, ∃ C : ℝ, ∀ u : ℂ, 4 ≤ ‖u‖ → c * ‖u‖ ≤ ‖g u‖ ∧ ‖deriv g u‖ ≤ C)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb) {z0 : ℂ} (hz0 : z0 ∈ unitDiscExterior) :
    IntegrableOn (fun u => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z0) unitDiscExterior ∧
      IntegrableOn (fun u => deriv (fun y => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) z0) unitDiscExterior ∧
      HasDerivAt (fun y => ∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y)
        (∫ u in unitDiscExterior, deriv (fun y => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) z0) z0 := by
  obtain ⟨hgd, hg'd, hgi, hdd, hg'⟩ := d2e_basic hρ hG hGi hGd hGg
  have hg0 : ∀ u ∈ unitDiscExterior, g u ≠ 0 := fun u hu h => by
    have := hk u hu
    rw [h, norm_zero] at this
    norm_num at this
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have hz01 : 1 < ‖z0‖ := hz0
  set ε : ℝ := (‖z0‖ - 1) / 8 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hsubE : ∀ w : ℂ, ‖w - z0‖ ≤ 7 * ε → w ∈ unitDiscExterior := by
    intro w hw
    have h1 := norm_sub_norm_le z0 w
    rw [norm_sub_rev] at h1
    show 1 < ‖w‖
    rw [hε] at hw
    linarith
  have hKc : closedBall z0 (6 * ε) ⊆ unitDiscExterior := fun w hw =>
    hsubE w (by have := mem_closedBall_iff_norm.1 hw; linarith)
  obtain ⟨B, hBi, hB0, hBk⟩ := d2e_bound hρ hG hGi hGd hGg hk hinf (isCompact_closedBall z0 (6 * ε)) hKc
    (by positivity : (0 : ℝ) < 2 * ε)
  have hKeq : ∀ u ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, w ≠ u → -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u w = deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * (g u - g w)) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1) * (u - w)) :=
    fun u hu w hw hwu => d2e_K_eq hwu (hg0 u hu) (hg' u hu) (hg' w hw) (fun h => hwu (hgi hu hw h).symm)
      (d2e_dn_ne hu)
  have hKd : ∀ u ∈ unitDiscExterior, DifferentiableOn ℂ (fun y => -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) unitDiscExterior :=
    fun u hu => d2e_K_diff hgd hg'd hgi hg' hg0 hu
  have htri : ∀ a b c : ℂ, ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := fun a b c => by
    have := norm_add_le (a - b) (b - c)
    rwa [show a - b + (b - c) = a - c by ring] at this
  -- (KB2) the kernel bound on `closedBall z₀ (2ε)`
  have hKB2 : ∀ u ∈ unitDiscExterior, ∀ y ∈ closedBall z0 (2 * ε), ‖-dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y‖ ≤ B u := by
    intro u hu y hy
    have hy' : ‖y - z0‖ ≤ 2 * ε := mem_closedBall_iff_norm.1 hy
    by_cases hun : ‖u - z0‖ < 4 * ε
    · have hdc : DiffContOnCl ℂ (fun y => -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) (ball z0 (6 * ε)) := by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball _ (by positivity)]
        exact (hKd u hu).mono hKc
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_ ?_
      · intro w hw
        rw [frontier_ball _ (by positivity)] at hw
        have hw' : ‖w - z0‖ = 6 * ε := mem_sphere_iff_norm.1 hw
        have hwK : w ∈ closedBall z0 (6 * ε) := sphere_subset_closedBall hw
        have hsep : 2 * ε ≤ ‖u - w‖ := by
          have := htri w u z0
          rw [norm_sub_rev w u] at this
          linarith
        have hwu : w ≠ u := fun h => by rw [h, sub_self, norm_zero] at hsep; linarith
        rw [hKeq u hu w (hKc hwK) hwu]
        exact hBk u hu w hwK hsep
      · rw [closure_ball _ (by positivity)]
        exact mem_closedBall_iff_norm.2 (by linarith)
    · rw [not_lt] at hun
      have hsep : 2 * ε ≤ ‖u - y‖ := by
        have := htri u y z0
        linarith
      have hyK : y ∈ closedBall z0 (6 * ε) := mem_closedBall_iff_norm.2 (by linarith)
      have hyu : y ≠ u := fun h => by rw [h, sub_self, norm_zero] at hsep; linarith
      rw [hKeq u hu y (hKc hyK) hyu]
      exact hBk u hu y hyK hsep
  -- measurability in `u`
  have hmeasK : ∀ y ∈ unitDiscExterior, AEStronglyMeasurable (fun u => -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y)
      (volume.restrict unitDiscExterior) := by
    intro y hy
    have hcont : ContinuousOn (fun u => deriv g u ^ 2 * g y ^ 2 / (g u ^ 2 * deriv g y * (g u - g y)) - (y + 1) * (y + I) * (y - 1) / ((u + 1) * (u + I) * (u - 1) * (u - y))) (unitDiscExterior \ {y}) := by
      have hgc := hgd.continuousOn.mono (diff_subset (s := unitDiscExterior) (t := {y}))
      have hg'c := hg'd.continuousOn.mono (diff_subset (s := unitDiscExterior) (t := {y}))
      apply ContinuousOn.sub
      · apply ContinuousOn.div ((hg'c.pow 2).mul continuousOn_const)
          (((hgc.pow 2).mul continuousOn_const).mul (hgc.sub continuousOn_const))
        intro u hu
        exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (hg0 u hu.1)) (hg' y hy))
          (sub_ne_zero.2 (fun h => hu.2 (hgi hu.1 hy h)))
      · apply ContinuousOn.div continuousOn_const
          ((by fun_prop : Continuous fun u : ℂ => (u + 1) * (u + I) * (u - 1) * (u - y)).continuousOn)
        intro u hu
        exact mul_ne_zero (d2e_dn_ne hu.1) (sub_ne_zero.2 hu.2)
    have h1 := hcont.aestronglyMeasurable (μ := volume) (hEm.diff (measurableSet_singleton y))
    rw [Measure.restrict_congr_set (sdiff_null_ae_eq_self (μ := volume) (s := unitDiscExterior)
      (measure_singleton y))] at h1
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae ((countable_singleton y).ae_notMem volume)]
      with u hu huy
    exact (hKeq u hu y hy (fun h => huy (h ▸ rfl))).symm
  obtain ⟨h1, h2, h3⟩ := d2p_param (k := fun u y => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y)
    (μ := volume.restrict unitDiscExterior) hE (z0 := z0) hε0
    (fun w hw => hsubE w (by have := mem_closedBall_iff_norm.1 hw; linarith))
    (by
      filter_upwards [ae_restrict_mem hEm] with u hu
      exact (differentiableOn_const _).mul (hKd u hu))
    (fun y hy => hRm.mul (hmeasK y hy)) (B := fun u => Rb * B u) (hBi.const_mul Rb).integrableOn
    (by
      filter_upwards [hRb, ae_restrict_mem hEm] with u hRu hu y hy
      rw [norm_mul]
      exact mul_le_mul hRu (hKB2 u hu y hy) (norm_nonneg _) ((norm_nonneg _).trans hRu))
  exact ⟨h1, h2, h3⟩

/-- [(P)/(D3) helper] **The merged D3 integrand is integrable**: `R (g'²/g² - (u + i)/Dn(u))` on `𝔻*`, for `R` bounded
(`(u + i)/Dn(u) = 1/(u² - 1)`; via `g(1/s) = b/φ(s)`, the difference is `s² h(s)` with `h` holomorphic, `h(0) = 0`). -/
theorem d2p_merged_int {f g R : ℂ → ℂ} {Rb M : ℝ} (hpair : IsNormalizedDisjointPair f g)
    (hM : ∀ u ∈ unitDiscExterior, ‖deriv g u‖ ≤ M) (hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖g u‖)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb) :
    IntegrableOn (fun u => R u * (deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1))))
      unitDiscExterior := by
  have hgd : DifferentiableOn ℂ g unitDiscExterior := hpair.2.2.2.2.1.1
  obtain ⟨φ, b, hφd, -, hφ0, hφ1, hb, -, hgφ⟩ := g1_inverted_exterior hpair
  have hD : IsOpen unitDisc := isOpen_ball
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  -- `ψ = φ/s`, `h = φ'²/ψ² - 1/((1+s)(1-s))`
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℂ, ψ = dslope φ 0 := ⟨_, rfl⟩
  have hψd : DifferentiableOn ℂ ψ unitDisc := by
    rw [hψ]
    exact (differentiableOn_dslope (hD.mem_nhds h0D)).2 hφd
  have hψ0 : ψ 0 = 1 := by rw [hψ, dslope_same, hφ1]
  have hψs : ∀ s : ℂ, s ≠ 0 → φ s = s * ψ s := fun s hs => by
    rw [hψ, dslope_of_ne _ hs, slope_def_field, hφ0, sub_zero, sub_zero]
    field_simp
  obtain ⟨r0, hr0, hr0b⟩ : ∃ r0 > 0, ∀ s ∈ ball (0 : ℂ) r0, ψ s ≠ 0 := by
    have hc : ContinuousAt ψ 0 := (hψd 0 h0D).continuousWithinAt.continuousAt (hD.mem_nhds h0D)
    have hev : ∀ᶠ s in 𝓝 (0 : ℂ), ψ s ≠ 0 := hc.eventually_ne (by rw [hψ0]; exact one_ne_zero)
    obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.1 hev
    exact ⟨r, hr, fun s hs => hrb hs⟩
  obtain ⟨ρ1, hρ1⟩ : ∃ ρ1 : ℝ, ρ1 = min r0 (1 / 2) := ⟨_, rfl⟩
  have hρ10 : 0 < ρ1 := by rw [hρ1]; exact lt_min hr0 (by norm_num)
  have hρ1h : ρ1 ≤ 1 / 2 := by rw [hρ1]; exact min_le_right _ _
  have hρ1r : ρ1 ≤ r0 := by rw [hρ1]; exact min_le_left _ _
  have hBD : ball (0 : ℂ) ρ1 ⊆ unitDisc := ball_subset_ball (by linarith)
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ, h = fun s => deriv φ s ^ 2 / ψ s ^ 2 - 1 / ((1 + s) * (1 - s)) := ⟨_, rfl⟩
  have hpm : ∀ s ∈ ball (0 : ℂ) ρ1, (1 + s) * (1 - s) ≠ 0 := by
    intro s hs
    have hs' : ‖s‖ < 1 / 2 := lt_of_lt_of_le (mem_ball_zero_iff.1 hs) hρ1h
    refine mul_ne_zero (fun e => ?_) (fun e => ?_)
    · have : s = -1 := by linear_combination e
      rw [this, norm_neg, norm_one] at hs'
      norm_num at hs'
    · have : s = 1 := by linear_combination -e
      rw [this, norm_one] at hs'
      norm_num at hs'
  have hhd : DifferentiableOn ℂ h (ball 0 ρ1) := by
    rw [hh]
    refine ((((hφd.deriv hD).mono hBD).pow 2).div ((hψd.mono hBD).pow 2) fun s hs =>
      pow_ne_zero 2 (hr0b s (ball_subset_ball hρ1r hs))).sub
      ((differentiableOn_const 1).div (by fun_prop) hpm)
  have hh0 : h 0 = 0 := by
    rw [hh]
    simp only [hψ0]
    rw [show deriv φ 0 = 1 from hφ1]
    norm_num
  obtain ⟨Ck, hCk⟩ : ∃ C : ℝ, ∀ s ∈ closedBall (0 : ℂ) (ρ1 / 2), ‖dslope h 0 s‖ ≤ C := by
    have hdd : DifferentiableOn ℂ (dslope h 0) (ball 0 ρ1) :=
      (differentiableOn_dslope (ball_mem_nhds 0 hρ10)).2 hhd
    exact (isCompact_closedBall _ _).exists_bound_of_continuousOn
      (hdd.continuousOn.mono (closedBall_subset_ball (by linarith)))
  have hCk0 : 0 ≤ Ck := (norm_nonneg _).trans (hCk 0 (mem_closedBall_self (by positivity)))
  -- the far bound: `|g'²/g² - 1/(u² - 1)| ≤ Ck/|u|³`
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 2 / ρ1 := ⟨_, rfl⟩
  have hU4 : 4 ≤ U := by rw [hU, le_div_iff₀ hρ10]; linarith
  have hfar : ∀ u : ℂ, U ≤ ‖u‖ → ‖deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1))‖ ≤
      Ck * (‖u‖ ^ 3)⁻¹ := by
    intro u hu
    have hu0 : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hu; linarith
    have hun : 0 < ‖u‖ := norm_pos_iff.2 hu0
    have huE : u ∈ unitDiscExterior := show 1 < ‖u‖ by linarith
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s = u⁻¹ := ⟨_, rfl⟩
    have hs0 : s ≠ 0 := by rw [hs]; exact inv_ne_zero hu0
    have hsn : ‖s‖ ≤ ρ1 / 2 := by
      rw [hs, norm_inv, inv_le_comm₀ hun (by positivity), inv_div]
      rw [hU] at hu
      exact hu
    have hsB : s ∈ ball (0 : ℂ) ρ1 := mem_ball_zero_iff.2 (by linarith)
    have hsD : s ∈ unitDisc := hBD hsB
    have hψs0 : ψ s ≠ 0 := hr0b s (ball_subset_ball hρ1r hsB)
    have hφs0 : φ s ≠ 0 := by rw [hψs s hs0]; exact mul_ne_zero hs0 hψs0
    have hus : u = s⁻¹ := by rw [hs, inv_inv]
    -- `g = b/φ(1/·)` near `u`
    have heq : g =ᶠ[𝓝 u] fun w => b / φ w⁻¹ := by
      filter_upwards [hE.mem_nhds huE] with w hw
      have hw1 : 1 < ‖w‖ := hw
      have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hw1; linarith
      have hwD : w⁻¹ ∈ unitDisc := by
        show w⁻¹ ∈ ball (0 : ℂ) 1
        rw [mem_ball_zero_iff, norm_inv]
        exact inv_lt_one_of_one_lt₀ hw1
      have := hgφ w⁻¹ hwD (inv_ne_zero hw0)
      rwa [one_div, inv_inv] at this
    have hφa : HasDerivAt φ (deriv φ s) s := (hφd.differentiableAt (hD.mem_nhds hsD)).hasDerivAt
    have hcomp : HasDerivAt (fun w : ℂ => φ w⁻¹) (deriv φ s * -(u ^ 2)⁻¹) u := by
      have h1 := hasDerivAt_inv hu0
      rw [hs] at hφa
      have h2 := hφa.comp u h1
      rw [← hs] at h2
      exact h2
    have hφu : φ u⁻¹ ≠ 0 := by rw [← hs]; exact hφs0
    have hder : HasDerivAt g ((0 * φ u⁻¹ - b * (deriv φ s * -(u ^ 2)⁻¹)) / φ u⁻¹ ^ 2) u :=
      ((hasDerivAt_const u b).div hcomp hφu).congr_of_eventuallyEq heq
    have hgu : g u = b / φ s := by rw [heq.eq_of_nhds, hs]
    have hDn : u + I ≠ 0 := by
      intro e
      have : u = -I := by linear_combination e
      rw [this, norm_neg, Complex.norm_I] at hu
      linarith
    have hid : deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1)) = s ^ 2 * h s := by
      rw [hder.deriv, hgu, ← hs, hψs s hs0, hh, hus]
      have h1 : 1 + s ≠ 0 := fun e => (hpm s hsB) (by rw [e, zero_mul])
      have h2 : 1 - s ≠ 0 := fun e => (hpm s hsB) (by rw [e, mul_zero])
      rw [hus] at hDn
      have h5 : 1 + s * I ≠ 0 := by
        have e : s⁻¹ + I = (1 + s * I) / s := by field_simp
        rw [e] at hDn
        exact (div_ne_zero_iff.1 hDn).1
      have h3 : s⁻¹ + 1 ≠ 0 := by
        have e : s⁻¹ + 1 = (1 + s) / s := by field_simp
        rw [e]
        exact div_ne_zero h1 hs0
      have h4 : s⁻¹ - 1 ≠ 0 := by
        have e : s⁻¹ - 1 = (1 - s) / s := by field_simp
        rw [e]
        exact div_ne_zero h2 hs0
      field_simp
      ring
    have hhs : h s = s * dslope h 0 s := by
      have := sub_smul_dslope h 0 s
      rw [hh0, sub_zero, sub_zero, smul_eq_mul] at this
      exact this.symm
    rw [hid, hhs, norm_mul, norm_mul, norm_pow, ← mul_assoc, ← pow_succ]
    have hk' := hCk s (mem_closedBall_zero_iff.2 hsn)
    have hs3 : ‖s‖ ^ 3 = (‖u‖ ^ 3)⁻¹ := by rw [hs, norm_inv, inv_pow]
    rw [hs3, mul_comm]
    exact mul_le_mul_of_nonneg_right hk' (by positivity)
  -- the global majorant
  obtain ⟨Rb', hRb'⟩ : ∃ r : ℝ, r = max Rb 0 := ⟨_, rfl⟩
  have hRb'0 : 0 ≤ Rb' := by rw [hRb']; exact le_max_right _ _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 2 (show (1 : ℝ) < ‖(2 : ℂ)‖ by norm_num))
  obtain ⟨B, hB⟩ : ∃ B : ℂ → ℝ, B = fun u => Rb' * ((M ^ 2 * 16) * (ball (0 : ℂ) U).indicator 1 u +
      (U + 1) * ‖(u + 1) * (u + I) * (u - 1)‖⁻¹ + 8 * Ck * ((1 + ‖u‖) ^ 3)⁻¹) := ⟨_, rfl⟩
  have hBi : Integrable B (volume.restrict unitDiscExterior) := by
    have h3 : Integrable (fun u : ℂ => (1 + ‖u‖) ^ (-(3 : ℝ))) :=
      integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
    have e : (fun u : ℂ => (1 + ‖u‖) ^ (-(3 : ℝ))) = fun u => ((1 + ‖u‖) ^ 3)⁻¹ := by
      funext u
      rw [Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e] at h3
    have hind : Integrable ((ball (0 : ℂ) U).indicator (1 : ℂ → ℝ)) :=
      (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
    rw [hB]
    exact ((((hind.const_mul (M ^ 2 * 16)).add (d2e_dn_int.const_mul (U + 1))).add
      (h3.const_mul (8 * Ck))).const_mul Rb').integrableOn
  -- measurability
  have hgc : ContinuousOn g unitDiscExterior := hgd.continuousOn
  have hg'c : ContinuousOn (deriv g) unitDiscExterior := (hgd.deriv hE).continuousOn
  have hg0 : ∀ u ∈ unitDiscExterior, g u ≠ 0 := fun u hu e => by
    have := hk u hu
    rw [e, norm_zero] at this
    norm_num at this
  have hcont : ContinuousOn (fun u => deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1)))
      unitDiscExterior :=
    ((hg'c.pow 2).div (hgc.pow 2) fun u hu => pow_ne_zero 2 (hg0 u hu)).sub
      ((by fun_prop : Continuous fun u : ℂ => u + I).continuousOn.div (by fun_prop) fun u hu => d2e_dn_ne hu)
  refine Integrable.mono' hBi (hRm.mul (hcont.aestronglyMeasurable hEm)) ?_
  filter_upwards [hRb, ae_restrict_mem hEm] with u hRu hu
  have hu1 : 1 < ‖u‖ := hu
  have hRu' : ‖R u‖ ≤ Rb' := hRu.trans (by rw [hRb']; exact le_max_left _ _)
  rw [norm_mul]
  refine (mul_le_mul_of_nonneg_right hRu' (norm_nonneg _)).trans ?_
  rw [hB]
  refine mul_le_mul_of_nonneg_left ?_ hRb'0
  have hind0 : 0 ≤ (M ^ 2 * 16) * (ball (0 : ℂ) U).indicator 1 u := by
    apply mul_nonneg (by positivity)
    exact indicator_nonneg (fun _ _ => zero_le_one) _
  have hdn0 : 0 ≤ (U + 1) * ‖(u + 1) * (u + I) * (u - 1)‖⁻¹ := by
    apply mul_nonneg (by linarith) (inv_nonneg.2 (norm_nonneg _))
  have hfar0 : 0 ≤ 8 * Ck * ((1 + ‖u‖) ^ 3)⁻¹ := by positivity
  by_cases hfu : U ≤ ‖u‖
  · have h8 : Ck * (‖u‖ ^ 3)⁻¹ ≤ 8 * Ck * ((1 + ‖u‖) ^ 3)⁻¹ := by
      have hu0 : 0 < ‖u‖ := by linarith
      have hp : (1 + ‖u‖) ^ 3 ≤ 8 * ‖u‖ ^ 3 := by
        calc (1 + ‖u‖) ^ 3 ≤ (2 * ‖u‖) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
          _ = 8 * ‖u‖ ^ 3 := by ring
      have hi : (‖u‖ ^ 3)⁻¹ ≤ 8 * ((1 + ‖u‖) ^ 3)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
        linarith
      calc Ck * (‖u‖ ^ 3)⁻¹ ≤ Ck * (8 * ((1 + ‖u‖) ^ 3)⁻¹) := mul_le_mul_of_nonneg_left hi hCk0
        _ = 8 * Ck * ((1 + ‖u‖) ^ 3)⁻¹ := by ring
    linarith [hfar u hfu]
  · rw [not_le] at hfu
    have hmem : u ∈ ball (0 : ℂ) U := mem_ball_zero_iff.2 hfu
    rw [indicator_of_mem hmem, Pi.one_apply, mul_one]
    have hgk := hk u hu
    have h1 : ‖deriv g u ^ 2 / g u ^ 2‖ ≤ M ^ 2 * 16 := by
      rw [norm_div, norm_pow, norm_pow, div_le_iff₀ (by positivity)]
      calc ‖deriv g u‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM u hu) 2
        _ = M ^ 2 * 16 * (1 / 4) ^ 2 := by ring
        _ ≤ M ^ 2 * 16 * ‖g u‖ ^ 2 := by gcongr
    have h2 : ‖(u + I) / ((u + 1) * (u + I) * (u - 1))‖ ≤ (U + 1) * ‖(u + 1) * (u + I) * (u - 1)‖⁻¹ := by
      rw [norm_div, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
      calc ‖u + I‖ ≤ ‖u‖ + ‖I‖ := norm_add_le _ _
        _ ≤ U + 1 := by rw [Complex.norm_I]; linarith
    linarith [norm_sub_le (deriv g u ^ 2 / g u ^ 2) ((u + I) / ((u + 1) * (u + I) * (u - 1)))]

/-- [(P) helper] `∂_y` of the three-point kernel `N(ζ, y)` and of `∂_y N`. -/
theorem d2p_Nderiv {ζ y : ℂ} (hD : (ζ + 1) * (ζ + I) * (ζ - 1) ≠ 0) (hy : y ≠ ζ) :
    HasDerivAt (fun y => ((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))
      (1 / (ζ - y) ^ 2 - (ζ + 2 * y + I) / ((ζ + 1) * (ζ + I) * (ζ - 1))) y ∧
    HasDerivAt (fun y => 1 / (ζ - y) ^ 2 - (ζ + 2 * y + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))
      (2 / (ζ - y) ^ 3 - 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) y := by
  have h1 : ζ - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hl : HasDerivAt (fun y : ℂ => ζ - y) (-1) y := by
    simpa using (hasDerivAt_id' y).const_sub ζ
  have hP := (((hasDerivAt_id' y).add_const 1).mul ((hasDerivAt_id' y).add_const I)).mul
    ((hasDerivAt_id' y).sub_const 1)
  refine ⟨?_, ?_⟩
  · convert hP.div (hl.const_mul ((ζ + 1) * (ζ + I) * (ζ - 1))) (mul_ne_zero hD h1) using 1
    simp only [Pi.mul_apply]
    generalize hDd : (ζ + 1) * (ζ + I) * (ζ - 1) = D at hD ⊢
    field_simp
    rw [← hDd]
    ring
  · have h2 := (hasDerivAt_const y (1 : ℂ)).div (hl.pow 2) (pow_ne_zero 2 h1)
    have h3 := ((((hasDerivAt_id' y).const_mul 2).const_add ζ).add_const I).div_const ((ζ + 1) * (ζ + I) * (ζ - 1))
    convert h2.sub h3 using 1
    simp only [Pi.pow_apply, Nat.cast_ofNat]
    generalize (ζ + 1) * (ζ + I) * (ζ - 1) = D at hD ⊢
    field_simp
    ring

/-- [(P) helper] The kernel identity off the diagonal:
`∂_y(R K̃) + 𝒜(y) R (K̃ + N) = R Q - R (g'²/g² - (u + i)/Dn) + 2y R/Dn`. -/
theorem d2p_kid {g : ℂ → ℂ} (hgd : DifferentiableOn ℂ g unitDiscExterior)
    (hg'd : DifferentiableOn ℂ (deriv g) unitDiscExterior) (hgi : InjOn g unitDiscExterior)
    (hg' : ∀ u ∈ unitDiscExterior, deriv g u ≠ 0) (hg0 : ∀ u ∈ unitDiscExterior, g u ≠ 0) (r : ℂ)
    {u y : ℂ} (hu : u ∈ unitDiscExterior) (hy : y ∈ unitDiscExterior) (huy : u ≠ y) :
    deriv (fun y => r * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) y +
        preSchwarzian g y * (r * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y +
          r * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y)))) =
      r * (deriv g u ^ 2 / (g u - g y) ^ 2 - 1 / (u - y) ^ 2) -
        r * (deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1))) +
        2 * y * (r / ((u + 1) * (u + I) * (u - 1))) := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hDn := d2e_dn_ne (show 1 < ‖u‖ from hu)
  have hgu := hg0 u hu
  have hg'u := hg' u hu
  have hq := hg' y hy
  have hP : g u - g y ≠ 0 := sub_ne_zero.2 fun h => huy (hgi hu hy h)
  have hyu : y ≠ u := Ne.symm huy
  have hev : (fun y => r * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) =ᶠ[𝓝 y]
      fun w => r * (deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * (g u - g w)) -
        (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1) * (u - w))) := by
    filter_upwards [hE.mem_nhds hy, isOpen_ne.mem_nhds hyu] with w hw hwu
    rw [d2e_K_eq hwu hgu hg'u (hg' w hw) (fun h => hwu (hgi hu hw h).symm) hDn]
  have hp := (hgd.differentiableAt (hE.mem_nhds hy)).hasDerivAt
  have hs := (hg'd.differentiableAt (hE.mem_nhds hy)).hasDerivAt
  have hM := ((hp.pow 2).const_mul (deriv g u ^ 2)).div
    ((hs.const_mul (g u ^ 2)).mul (hp.const_sub (g u))) (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hgu) hq) hP)
  have hN := (d2p_Nderiv hDn hyu).1
  have hd := (((hM.sub hN).const_mul r).congr_of_eventuallyEq hev).deriv
  rw [hd, d2e_K_eq hyu hgu hg'u hq (fun h => huy (hgi hu hy h)) hDn,
    show preSchwarzian g y = deriv (deriv g) y / deriv g y from rfl]
  have h5 : u - y ≠ 0 := sub_ne_zero.2 huy
  simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
  generalize hDd : (u + 1) * (u + I) * (u - 1) = D at hDn ⊢
  field_simp
  rw [← hDd]
  ring

/-- [(P) helper] **`t`-part, abstract form.** On `𝔻*`, `η₁' + 𝒜η₁ + 𝒜γ̇ = -(1/π)(T - I_M + 2y I_D) + 2(c₂/b) g`
(kernel identity `d2p_kid`, every piece integrable), hence `T` is ℝ-differentiable and the `t`-clause of (P). -/
theorem d2p_tpart {g G R : ℂ → ℂ} {ρ Rb : ℝ} (b : ℂ) (hρ : ρ < 1) (hG : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖})
    (hGi : InjOn G {z : ℂ | ρ < ‖z‖}) (hGd : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0)
    (hGg : EqOn G g unitDiscExterior) (hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖g u‖)
    (hinf : ∃ c > 0, ∃ C : ℝ, ∀ u : ℂ, 4 ≤ ‖u‖ → c * ‖u‖ ≤ ‖g u‖ ∧ ‖deriv g u‖ ≤ C)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hγ : ContDiffOn ℝ 1 (fun y : ℂ => -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) unitDiscExterior)
    (hC0 : IntegrableOn (fun u => R u * (deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1)))) unitDiscExterior) :
    ∀ z ∈ unitDiscExterior,
      DifferentiableAt ℝ (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ *
          (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2)) z ∧
      deriv (fun x : ℂ => deriv (fun y : ℂ => (((-(1 / π : ℂ) * ∫ u in unitDiscExterior, R u * deriv g u ^ 2 *
          (1 / (g u - g y) - 1 / g u - g y / g u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b * g y ^ 2 -
        deriv g y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) / deriv g y)) x + preSchwarzian g x * (((-(1 / π : ℂ) * ∫ u in unitDiscExterior, R u * deriv g u ^ 2 *
          (1 / (g u - g x) - 1 / g u - g x / g u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b * g x ^ 2 -
        deriv g x * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ *
          (((x + 1) * (x + I) * (x - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - x))))) / deriv g x)) z +
          dz (fun y : ℂ => preSchwarzian g y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z = (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, R ζ *
          (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2)) z +
        2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) * (deriv g z / b - 1)) := by
  obtain ⟨hgd, hg'd, hgi, hdd, hg'⟩ := d2e_basic hρ hG hGi hGd hGg
  have hg0 : ∀ u ∈ unitDiscExterior, g u ≠ 0 := fun u hu h => by
    have := hk u hu
    rw [h, norm_zero] at this
    norm_num at this
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hcore := fun y (hy : y ∈ unitDiscExterior) => d2p_core hρ hG hGi hGd hGg hk hinf hRm hRb hy
  have hηD := d2e_eta1 (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) hρ hG hGi hGd hGg hk hinf hRm hRb
  obtain ⟨η, hη⟩ : ∃ η : ℂ → ℂ, η = fun y => (((-(1 / π : ℂ) * ∫ u in unitDiscExterior, R u * deriv g u ^ 2 * (1 / (g u - g y) - 1 / g u - g y / g u ^ 2)) + (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) * g y ^ 2 - deriv g y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) / deriv g y) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℂ → ℂ, T = fun y => ∫ ζ in unitDiscExterior, R ζ * (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2) := ⟨_, rfl⟩
  obtain ⟨γ, hγe⟩ : ∃ γ : ℂ → ℂ, γ = fun y => -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) := ⟨_, rfl⟩
  obtain ⟨Lf, hLf⟩ : ∃ Lf : ℂ → ℂ, Lf = fun x => deriv η x + preSchwarzian g x * η x := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun y => preSchwarzian g y * γ y := ⟨_, rfl⟩
  rw [← hη] at hηD
  have hRD : IntegrableOn (fun u => R u / ((u + 1) * (u + I) * (u - 1))) unitDiscExterior := by
    refine (d2e_dn_int.const_mul Rb).integrableOn.mono'
      (hRm.div₀ (by fun_prop : Continuous fun u : ℂ => ((u + 1) * (u + I) * (u - 1))).aestronglyMeasurable) ?_
    filter_upwards [hRb] with u hu
    rw [norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hu (inv_nonneg.2 (norm_nonneg _))
  -- `η₁ = -(1/π) ∫ R K̃ + (c₂/b) g²/g'` (as in `d2e_eta1`)
  have hηe : ∀ y ∈ unitDiscExterior, η y = -(1 / π : ℂ) * (∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) + (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) * g y ^ 2 / deriv g y := by
    intro y hy
    have hIK := (hcore y hy).1
    have hIN := d2e_N_int hRm hRb hy
    have hM : (∫ u in unitDiscExterior, R u * deriv g u ^ 2 * (1 / (g u - g y) - 1 / g u - g y / g u ^ 2)) =
        deriv g y * ((∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) + ∫ u in unitDiscExterior, R u * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y)))) := by
      rw [← integral_add hIK hIN, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae ((countable_singleton y).ae_notMem volume)]
        with u hu huy
      have huy' : u ≠ y := fun h => huy (h ▸ rfl)
      rw [d2e_K_eq (Ne.symm huy') (hg0 u hu) (hg' u hu) (hg' y hy) (fun h => huy' (hgi hu hy h))
        (d2e_dn_ne hu)]
      have h1 := hg0 u hu
      have h2 : g u - g y ≠ 0 := sub_ne_zero.2 (fun h => huy' (hgi hu hy h))
      have h3 := hg' y hy
      have h4 := d2e_dn_ne (show 1 < ‖u‖ from hu)
      have h5 : u - y ≠ 0 := sub_ne_zero.2 huy'
      generalize (u + 1) * (u + I) * (u - 1) = D at h4 ⊢
      generalize (y + 1) * (y + I) * (y - 1) = E
      field_simp
      ring
    have h3 := hg' y hy
    rw [hη]
    beta_reduce
    rw [hM]
    generalize (∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) = IK
    generalize (∫ u in unitDiscExterior, R u * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y)))) = IN
    field_simp
    ring
  have hηd : ∀ y ∈ unitDiscExterior, deriv η y = -(1 / π : ℂ) * (∫ u in unitDiscExterior, deriv (fun y => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) y) +
      (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) * (2 * g y * deriv g y * deriv g y - g y ^ 2 * deriv (deriv g) y) / deriv g y ^ 2 := by
    intro y hy
    have hp := (hgd.differentiableAt (hE.mem_nhds hy)).hasDerivAt
    have hs := (hg'd.differentiableAt (hE.mem_nhds hy)).hasDerivAt
    have h := (((hcore y hy).2.2.const_mul (-(1 / π : ℂ))).add (((hp.pow 2).const_mul (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b)).div hs (hg' y hy))).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hE.mem_nhds hy) hηe)
    rw [h.deriv]
    simp only [Pi.pow_apply, Nat.cast_ofNat]
    have h3 := hg' y hy
    generalize (∫ u in unitDiscExterior, deriv (fun y => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) y) = J
    generalize (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) = C
    field_simp
    ring
  -- the integrated kernel identity; every piece is an explicit `Integrable` fact
  have hInt : ∀ y ∈ unitDiscExterior, (∫ u in unitDiscExterior, deriv (fun y => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) y) +
      preSchwarzian g y * ((∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) + ∫ u in unitDiscExterior, R u * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y)))) =
      (∫ u in unitDiscExterior, R u * (deriv g u ^ 2 / (g u - g y) ^ 2 - 1 / (u - y) ^ 2)) - (∫ u in unitDiscExterior, R u * (deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1)))) + 2 * y * (∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) := by
    intro y hy
    obtain ⟨hk1, hk2, -⟩ := hcore y hy
    have hn := d2e_N_int hRm hRb hy
    have hae : ∀ᵐ u ∂(volume.restrict unitDiscExterior), deriv (fun y => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) y +
        preSchwarzian g y * (R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y + R u * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y)))) =
        R u * (deriv g u ^ 2 / (g u - g y) ^ 2 - 1 / (u - y) ^ 2) - R u * (deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1))) + 2 * y * (R u / ((u + 1) * (u + I) * (u - 1))) := by
      filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae ((countable_singleton y).ae_notMem volume)]
        with u hu huy
      exact d2p_kid hgd hg'd hgi hg' hg0 (R u) hu hy (fun h => huy (h ▸ rfl))
    have hkn : IntegrableOn (fun u => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y + R u * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y)))) unitDiscExterior := Integrable.add hk1 hn
    have hA : IntegrableOn (fun u => preSchwarzian g y * (R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y + R u * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y))))) unitDiscExterior :=
      Integrable.const_mul hkn _
    have hS : IntegrableOn (fun u => deriv (fun y => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) y +
        preSchwarzian g y * (R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y + R u * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y))))) unitDiscExterior := Integrable.add hk2 hA
    have h2D : IntegrableOn (fun u => 2 * y * (R u / ((u + 1) * (u + I) * (u - 1)))) unitDiscExterior := Integrable.const_mul hRD _
    have hX : IntegrableOn (fun u => deriv (fun y => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) y +
        preSchwarzian g y * (R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y + R u * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y)))) + R u * (deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1))) - 2 * y * (R u / ((u + 1) * (u + I) * (u - 1)))) unitDiscExterior :=
      Integrable.sub (Integrable.add hS hC0) h2D
    have hQ : IntegrableOn (fun u => R u * (deriv g u ^ 2 / (g u - g y) ^ 2 - 1 / (u - y) ^ 2)) unitDiscExterior := by
      refine Integrable.congr hX ?_
      filter_upwards [hae] with u hu
      rw [hu]
      ring
    have hQm : IntegrableOn (fun u => R u * (deriv g u ^ 2 / (g u - g y) ^ 2 - 1 / (u - y) ^ 2) - R u * (deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1)))) unitDiscExterior := Integrable.sub hQ hC0
    calc _ = ∫ u in unitDiscExterior, deriv (fun y => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) y +
          preSchwarzian g y * (R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y + R u * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y)))) := by
          rw [integral_add hk2 hA, integral_const_mul, integral_add hk1 hn]
      _ = ∫ u in unitDiscExterior, R u * (deriv g u ^ 2 / (g u - g y) ^ 2 - 1 / (u - y) ^ 2) - R u * (deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1))) + 2 * y * (R u / ((u + 1) * (u + I) * (u - 1))) := integral_congr_ae hae
      _ = _ := by rw [integral_add hQm h2D, integral_sub hQ hC0, integral_const_mul]
  have hL : ∀ y ∈ unitDiscExterior, deriv η y + preSchwarzian g y * η y + preSchwarzian g y * γ y =
      -(1 / π : ℂ) * ((∫ u in unitDiscExterior, R u * (deriv g u ^ 2 / (g u - g y) ^ 2 - 1 / (u - y) ^ 2)) - (∫ u in unitDiscExterior, R u * (deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1)))) + 2 * y * (∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) + 2 * (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) * g y := by
    intro y hy
    rw [← hInt y hy, hηd y hy, hηe y hy, hγe, show preSchwarzian g y = deriv (deriv g) y / deriv g y from rfl]
    beta_reduce
    have h3 := hg' y hy
    generalize (∫ u in unitDiscExterior, deriv (fun y => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) y) = J1
    generalize (∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) = J2
    generalize (∫ u in unitDiscExterior, R u * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y)))) = J3
    generalize (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) = C
    field_simp
    ring
  -- regularity
  have hAd : DifferentiableOn ℂ (preSchwarzian g) unitDiscExterior := (hg'd.deriv hE).div hg'd hg'
  have hLd : DifferentiableOn ℂ Lf unitDiscExterior := by
    rw [hLf]
    exact (hηD.deriv hE).add (hAd.mul hηD)
  have hγd : DifferentiableOn ℝ γ unitDiscExterior := by
    rw [hγe]
    exact hγ.differentiableOn one_ne_zero
  have key : ∀ z ∈ unitDiscExterior, DifferentiableAt ℝ T z ∧
      deriv Lf z + dz P z = -(1 / π : ℂ) * dz T z + 2 * ((1 / π : ℂ) * (∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) * (deriv g z / b - 1) := by
    intro z hz
    have hn := hE.mem_nhds hz
    have hLz : DifferentiableAt ℂ Lf z := hLd.differentiableAt hn
    have hPz : DifferentiableAt ℝ P z := by
      rw [hP]
      exact ((hAd.differentiableAt hn).restrictScalars ℝ).mul (hγd.differentiableAt hn)
    have hgz : DifferentiableAt ℂ g z := hgd.differentiableAt hn
    obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun y => -(π : ℂ) * (Lf y + P y - 2 * (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) * g y) + (∫ u in unitDiscExterior, R u * (deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1)))) - 2 * (∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) * y := ⟨_, rfl⟩
    have hTF : T =ᶠ[𝓝 z] F := by
      filter_upwards [hn] with y hy
      have h := hL y hy
      rw [hT, hF, hLf, hP]
      beta_reduce
      rw [h]
      generalize (∫ ζ in unitDiscExterior, R ζ * (deriv g ζ ^ 2 / (g ζ - g y) ^ 2 - 1 / (ζ - y) ^ 2)) = t
      generalize (∫ u in unitDiscExterior, R u * (deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1)))) = t1
      generalize (∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) = t2
      field_simp
      ring
    have hFh : HasFDerivAt F ((-(π : ℂ)) • ((fderiv ℝ Lf z + fderiv ℝ P z) - (2 * (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b)) • fderiv ℝ g z) -
        (2 * (∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) • ContinuousLinearMap.id ℝ ℂ) z := by
      rw [hF]
      exact (((((hLz.restrictScalars ℝ).hasFDerivAt.add hPz.hasFDerivAt).sub
        ((hgz.restrictScalars ℝ).hasFDerivAt.const_mul (2 * (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b)))).const_mul (-(π : ℂ))).add_const (∫ u in unitDiscExterior, R u * (deriv g u ^ 2 / g u ^ 2 - (u + I) / ((u + 1) * (u + I) * (u - 1))))).sub
        ((hasFDerivAt_id z).const_mul (2 * (∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))))
    have hdzT : dz T z = dz F z := by
      show (fderiv ℝ T z 1 - I * fderiv ℝ T z I) / 2 = (fderiv ℝ F z 1 - I * fderiv ℝ F z I) / 2
      rw [hTF.fderiv_eq]
    have hdzF : dz F z = -(π : ℂ) * (dz Lf z + dz P z - 2 * (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) * dz g z) - 2 * (∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) := by
      show (fderiv ℝ F z 1 - I * fderiv ℝ F z I) / 2 = -(π : ℂ) * ((fderiv ℝ Lf z 1 - I * fderiv ℝ Lf z I) / 2 +
        (fderiv ℝ P z 1 - I * fderiv ℝ P z I) / 2 - 2 * (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) * ((fderiv ℝ g z 1 - I * fderiv ℝ g z I) / 2)) - 2 * (∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))
      rw [hFh.fderiv]
      generalize (∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) = t2
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
      linear_combination t2 * I_sq
    rw [dz_eq_deriv hLz, dz_eq_deriv hgz] at hdzF
    refine ⟨hFh.differentiableAt.congr_of_eventuallyEq hTF, ?_⟩
    rw [hdzT, hdzF]
    generalize dz P z = p
    generalize (∫ ζ in unitDiscExterior, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) = t2
    field_simp
    ring
  subst hLf hP hη hγe hT
  exact key

/-- [(P) helper] **`t̄`-part, abstract form** (`S` bounded on `𝔻`). `η₂ = (c₂'/b) g²/g' + (1/π) J₀` with
`J₀ = ∫_𝔻 S N(·, y)` holomorphic on `𝔻*`, so `η₂' + 𝒜η₂ + 𝒜γ̇₂ = 2(c₂'/b) g + (1/π) J₀'` and `J₀'' = ∫_𝔻 S ∂²N`. -/
theorem d2p_tbar {g G S : ℂ → ℂ} {ρ Sb : ℝ} (b : ℂ) (hρ : ρ < 1) (hG : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖})
    (hGi : InjOn G {z : ℂ | ρ < ‖z‖}) (hGd : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0)
    (hGg : EqOn G g unitDiscExterior) (hSm : AEStronglyMeasurable S (volume.restrict unitDisc))
    (hSb : ∀ᵐ ζ ∂(volume.restrict unitDisc), ‖S ζ‖ ≤ Sb) :
    ∀ z ∈ unitDiscExterior,
      deriv (fun x : ℂ => deriv (fun y : ℂ => ((((1 / π : ℂ) * ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b * g y ^ 2 -
        deriv g y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, S ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) / deriv g y)) x + preSchwarzian g x * ((((1 / π : ℂ) * ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b * g x ^ 2 -
        deriv g x * (-(1 / π : ℂ) * ∫ ζ in unitDisc, S ζ *
          (((x + 1) * (x + I) * (x - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - x))))) / deriv g x)) z +
          dz (fun y : ℂ => preSchwarzian g y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, S ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z = ((2 / π : ℂ) * (∫ ζ in unitDisc, S ζ / (ζ - z) ^ 3) +
        2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) * (deriv g z / b - 1)) := by
  obtain ⟨hgd, hg'd, hgi, hdd, hg'⟩ := d2e_basic hρ hG hGi hGd hGg
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hD1 : ∀ ζ ∈ unitDisc, ((ζ + 1) * (ζ + I) * (ζ - 1)) ≠ 0 := fun ζ hζ => d2e_dn_ne1 (mem_ball_zero_iff.1 hζ)
  have hne : ∀ ζ ∈ unitDisc, ∀ y ∈ unitDiscExterior, y ≠ ζ := fun ζ hζ y hy h => by
    have h1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
    have h2 : 1 < ‖y‖ := hy
    rw [h] at h2
    linarith
  have hDi : IntegrableOn (fun ζ : ℂ => ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹) unitDisc := d2e_dn_int.integrableOn
  have hci : ∀ c : ℝ, IntegrableOn (fun _ : ℂ => c) unitDisc := fun c =>
    (continuousOn_const.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set ball_subset_closedBall
  have hgeo : ∀ z0 ∈ unitDiscExterior, ∀ ζ ∈ unitDisc, ∀ y ∈ closedBall z0 (2 * ((‖z0‖ - 1) / 4)),
      2 * ((‖z0‖ - 1) / 4) ≤ ‖ζ - y‖ ∧ ‖y‖ ≤ 2 * ‖z0‖ ∧ 0 < 2 * ((‖z0‖ - 1) / 4) := by
    intro z0 hz0 ζ hζ y hy
    have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
    have hz01 : 1 < ‖z0‖ := hz0
    have hy' := mem_closedBall_iff_norm.1 hy
    have h1 := norm_sub_norm_le y ζ
    have h2 := norm_sub_norm_le z0 y
    have h3 := norm_sub_norm_le y z0
    rw [norm_sub_rev ζ y]
    rw [norm_sub_rev] at h2
    refine ⟨by linarith, by linarith, by linarith⟩
  -- parametric differentiation on `𝔻*` of `∫_𝔻 S K(·, y)` (`d2p_param`)
  have hpar : ∀ K : ℂ → ℂ → ℂ, (∀ ζ ∈ unitDisc, DifferentiableOn ℂ (K ζ) unitDiscExterior) →
      (∀ y ∈ unitDiscExterior, ContinuousOn (fun ζ => K ζ y) unitDisc) →
      (∀ z0 ∈ unitDiscExterior, ∃ c1 c2 : ℝ, ∀ ζ ∈ unitDisc, ∀ y ∈ closedBall z0 (2 * ((‖z0‖ - 1) / 4)),
        ‖K ζ y‖ ≤ c1 + c2 * ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹) →
      ∀ z0 ∈ unitDiscExterior, HasDerivAt (fun y => ∫ ζ in unitDisc, S ζ * K ζ y)
        (∫ ζ in unitDisc, deriv (fun y => S ζ * K ζ y) z0) z0 := by
    intro K hKd hKc hKb z0 hz0
    have hz01 : 1 < ‖z0‖ := hz0
    have hr0 : 0 < (‖z0‖ - 1) / 4 := by linarith
    have hball : closedBall z0 (2 * ((‖z0‖ - 1) / 4)) ⊆ unitDiscExterior := fun w hw => by
      have h1 := mem_closedBall_iff_norm.1 hw
      have h2 := norm_sub_norm_le z0 w
      rw [norm_sub_rev] at h2
      show 1 < ‖w‖
      linarith
    obtain ⟨c1, c2, hc⟩ := hKb z0 hz0
    refine (d2p_param (k := fun ζ y => S ζ * K ζ y) (μ := volume.restrict unitDisc) hE hr0 hball ?_ ?_
      (B := fun ζ => Sb * (c1 + c2 * ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹)) ?_ ?_).2.2
    · filter_upwards [ae_restrict_mem hDm] with ζ hζ
      exact (hKd ζ hζ).const_mul _
    · intro y hy
      exact hSm.mul ((hKc y hy).aestronglyMeasurable hDm)
    · exact Integrable.const_mul (Integrable.add (hci c1) (Integrable.const_mul hDi c2)) Sb
    · filter_upwards [ae_restrict_mem hDm, hSb] with ζ hζ hSζ y hy
      rw [norm_mul]
      exact mul_le_mul hSζ (hc ζ hζ y hy) (norm_nonneg _) ((norm_nonneg _).trans hSζ)
  obtain ⟨J0, hJ0e⟩ : ∃ J : ℂ → ℂ, J = fun y => ∫ ζ in unitDisc, S ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) := ⟨_, rfl⟩
  obtain ⟨J1, hJ1e⟩ : ∃ J : ℂ → ℂ, J = fun y => ∫ ζ in unitDisc, S ζ * (1 / (ζ - y) ^ 2 - (ζ + 2 * y + I) / ((ζ + 1) * (ζ + I) * (ζ - 1))) := ⟨_, rfl⟩
  obtain ⟨J2, hJ2e⟩ : ∃ J : ℂ → ℂ, J = fun y => ∫ ζ in unitDisc, S ζ * (2 / (ζ - y) ^ 3 - 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) := ⟨_, rfl⟩
  have hJ0 : ∀ y ∈ unitDiscExterior, HasDerivAt J0 (J1 y) y := by
    intro y hy
    rw [hJ0e, hJ1e]
    refine (hpar (fun ζ y => (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) (fun ζ hζ w hw => (d2p_Nderiv (hD1 ζ hζ) (hne ζ hζ w hw)).1.differentiableAt.differentiableWithinAt)
      (fun w hw => ?_) (fun z0 hz0 => ?_) y hy).congr_deriv ?_
    · apply ContinuousOn.div continuousOn_const
        ((by fun_prop : Continuous fun ζ : ℂ => (ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - w)).continuousOn)
      intro ζ hζ
      exact mul_ne_zero (hD1 ζ hζ) (sub_ne_zero.2 (hne ζ hζ w hw).symm)
    · obtain ⟨A, hA⟩ := (isCompact_closedBall z0 (2 * ((‖z0‖ - 1) / 4))).exists_bound_of_continuousOn
        ((by fun_prop : Continuous fun w : ℂ => (w + 1) * (w + I) * (w - 1)).continuousOn)
      refine ⟨0, A / (2 * ((‖z0‖ - 1) / 4)), fun ζ hζ w hw => ?_⟩
      obtain ⟨hs, -, hr⟩ := hgeo z0 hz0 ζ hζ w hw
      have hD := norm_pos_iff.2 (hD1 ζ hζ)
      have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA w hw)
      rw [norm_div, norm_mul ((ζ + 1) * (ζ + I) * (ζ - 1)) (ζ - w), zero_add]
      calc _ ≤ A / (‖((ζ + 1) * (ζ + I) * (ζ - 1))‖ * (2 * ((‖z0‖ - 1) / 4))) :=
            div_le_div₀ hA0 (hA w hw) (by positivity) (mul_le_mul_of_nonneg_left hs hD.le)
        _ = A / (2 * ((‖z0‖ - 1) / 4)) * ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ := by
            have := hD.ne'
            field_simp
    · refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem hDm] with ζ hζ
      exact ((d2p_Nderiv (hD1 ζ hζ) (hne ζ hζ y hy)).1.const_mul (S ζ)).deriv
  have hJ1 : ∀ y ∈ unitDiscExterior, HasDerivAt J1 (J2 y) y := by
    intro y hy
    rw [hJ1e, hJ2e]
    refine (hpar (fun ζ y => (1 / (ζ - y) ^ 2 - (ζ + 2 * y + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) (fun ζ hζ w hw => (d2p_Nderiv (hD1 ζ hζ) (hne ζ hζ w hw)).2.differentiableAt.differentiableWithinAt)
      (fun w hw => ?_) (fun z0 hz0 => ?_) y hy).congr_deriv ?_
    · exact (continuousOn_const.div ((continuous_sub_right w).pow 2).continuousOn
        fun ζ hζ => pow_ne_zero 2 (sub_ne_zero.2 (hne ζ hζ w hw).symm)).sub
        ((by fun_prop : Continuous fun ζ : ℂ => ζ + 2 * w + I).continuousOn.div
          (by fun_prop : Continuous fun ζ : ℂ => ((ζ + 1) * (ζ + I) * (ζ - 1))).continuousOn hD1)
    · refine ⟨((2 * ((‖z0‖ - 1) / 4)) ^ 2)⁻¹, 2 + 4 * ‖z0‖, fun ζ hζ w hw => ?_⟩
      obtain ⟨hs, hw2, hr⟩ := hgeo z0 hz0 ζ hζ w hw
      have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
      have hn : ‖ζ + 2 * w + I‖ ≤ 2 + 4 * ‖z0‖ := by
        have h1 := norm_add_le (ζ + 2 * w) I
        have h2 := norm_add_le ζ (2 * w)
        rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at h2
        rw [Complex.norm_I] at h1
        linarith
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_div, norm_one, norm_pow, one_div]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hr.le hs 2)
      · rw [norm_div, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hn (inv_nonneg.2 (norm_nonneg _))
    · refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem hDm] with ζ hζ
      exact ((d2p_Nderiv (hD1 ζ hζ) (hne ζ hζ y hy)).2.const_mul (S ζ)).deriv
  -- `J₂(z) = 2 ∫ S/(ζ - z)³ - 2 ∫ S/Dn`
  have hJ2v : ∀ z ∈ unitDiscExterior, J2 z = 2 * (∫ ζ in unitDisc, S ζ / (ζ - z) ^ 3) - 2 * (∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) := by
    intro z hz
    have hz1 : 1 < ‖z‖ := hz
    have i3 : IntegrableOn (fun ζ => S ζ / (ζ - z) ^ 3) unitDisc := by
      refine (hci (Sb * ((‖z‖ - 1) ^ 3)⁻¹)).mono' (hSm.div₀ ((continuous_sub_right z).pow 3).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem hDm, hSb] with ζ hζ hSζ
      have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
      have hs : ‖z‖ - 1 ≤ ‖ζ - z‖ := by
        have := norm_sub_norm_le z ζ
        rw [norm_sub_rev z ζ] at this
        linarith
      rw [norm_div, norm_pow, div_eq_mul_inv]
      exact mul_le_mul hSζ (inv_anti₀ (by have : 0 < ‖z‖ - 1 := by linarith
                                          positivity) (pow_le_pow_left₀ (by linarith) hs 3))
        (inv_nonneg.2 (by positivity)) ((norm_nonneg _).trans hSζ)
    have iD : IntegrableOn (fun ζ => S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) unitDisc := by
      refine (Integrable.const_mul hDi Sb).mono'
        (hSm.div₀ (by fun_prop : Continuous fun u : ℂ => ((u + 1) * (u + I) * (u - 1))).aestronglyMeasurable) ?_
      filter_upwards [hSb] with ζ hζ
      rw [norm_div, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hζ (inv_nonneg.2 (norm_nonneg _))
    rw [hJ2e]
    beta_reduce
    rw [show (fun ζ => S ζ * (2 / (ζ - z) ^ 3 - 2 / ((ζ + 1) * (ζ + I) * (ζ - 1)))) = fun ζ => 2 * (S ζ / (ζ - z) ^ 3) - 2 * (S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) from
      funext fun ζ => by ring, integral_sub (Integrable.const_mul i3 2) (Integrable.const_mul iD 2),
      integral_const_mul, integral_const_mul]
  -- the `t̄`-clause
  have hAd : DifferentiableOn ℂ (preSchwarzian g) unitDiscExterior := (hg'd.deriv hE).div hg'd hg'
  have hJ0d : DifferentiableOn ℂ J0 unitDiscExterior := fun y hy => (hJ0 y hy).differentiableAt.differentiableWithinAt
  obtain ⟨η, hη⟩ : ∃ η : ℂ → ℂ, η = fun y => ((((1 / π : ℂ) * ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) * g y ^ 2 - deriv g y * (-(1 / π : ℂ) * J0 y)) / deriv g y := ⟨_, rfl⟩
  obtain ⟨Lf, hLf⟩ : ∃ Lf : ℂ → ℂ, Lf = fun x => deriv η x + preSchwarzian g x * η x := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun y => preSchwarzian g y * (-(1 / π : ℂ) * J0 y) := ⟨_, rfl⟩
  have hηe : ∀ y ∈ unitDiscExterior, η y = (((1 / π : ℂ) * ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) * g y ^ 2 / deriv g y + (1 / π : ℂ) * J0 y := by
    intro y hy
    have h3 := hg' y hy
    rw [hη]
    field_simp
    ring
  have hηD : DifferentiableOn ℂ η unitDiscExterior :=
    ((((differentiableOn_const _).mul (hgd.pow 2)).div hg'd hg').add (hJ0d.const_mul _)).congr hηe
  have hηd : ∀ y ∈ unitDiscExterior, deriv η y = (((1 / π : ℂ) * ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) * (2 * g y * deriv g y * deriv g y - g y ^ 2 * deriv (deriv g) y) / deriv g y ^ 2 +
      (1 / π : ℂ) * J1 y := by
    intro y hy
    have hp := (hgd.differentiableAt (hE.mem_nhds hy)).hasDerivAt
    have hs := (hg'd.differentiableAt (hE.mem_nhds hy)).hasDerivAt
    have h := ((((hp.pow 2).const_mul (((1 / π : ℂ) * ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b)).div hs (hg' y hy)).add ((hJ0 y hy).const_mul (1 / π : ℂ))).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hE.mem_nhds hy) hηe)
    rw [h.deriv]
    simp only [Pi.pow_apply, Nat.cast_ofNat]
    have h3 := hg' y hy
    generalize (((1 / π : ℂ) * ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) = C
    field_simp
    ring
  have key : ∀ z ∈ unitDiscExterior, deriv Lf z + dz P z =
      (2 / π : ℂ) * (∫ ζ in unitDisc, S ζ / (ζ - z) ^ 3) + 2 * ((1 / π : ℂ) * (∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) * (deriv g z / b - 1) := by
    intro z hz
    have hn := hE.mem_nhds hz
    have hLd : DifferentiableAt ℂ Lf z := by
      rw [hLf]
      exact ((hηD.deriv hE).add (hAd.mul hηD)).differentiableAt hn
    have hPd : DifferentiableAt ℂ P z := by
      rw [hP]
      exact (hAd.mul (hJ0d.const_mul _)).differentiableAt hn
    have hsum : (fun y => Lf y + P y) =ᶠ[𝓝 z] fun y => 2 * (((1 / π : ℂ) * ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) * g y + (1 / π : ℂ) * J1 y := by
      filter_upwards [hn] with y hy
      rw [hLf, hP]
      beta_reduce
      rw [hηd y hy, hηe y hy, show preSchwarzian g y = deriv (deriv g) y / deriv g y from rfl]
      have h3 := hg' y hy
      generalize J0 y = j0
      generalize J1 y = j1
      generalize (((1 / π : ℂ) * ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) = C
      field_simp
      ring
    have hD2 := (((hgd.differentiableAt hn).hasDerivAt.const_mul (2 * (((1 / π : ℂ) * ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b))).add ((hJ1 z hz).const_mul (1 / π : ℂ))).congr_of_eventuallyEq hsum
    have e : deriv (fun y => Lf y + P y) z = 2 * (((1 / π : ℂ) * ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / b) * deriv g z + (1 / π : ℂ) * J2 z := hD2.deriv
    rw [dz_eq_deriv hPd, ← deriv_add hLd hPd]
    erw [e]
    rw [hJ2v z hz]
    generalize (∫ ζ in unitDisc, S ζ / (ζ - z) ^ 3) = t
    generalize (∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) = t2
    field_simp
    ring
  intro z hz
  have k := key z hz
  subst hLf hP hη hJ0e
  exact k

/-- **(P)** The pointwise welded identity: the unwelded variation plus the Lie term `∂_z(𝒜 γ̇)` is the D2 integrand
`Ċ` (resp. `∂̄C`). Includes the ℝ-differentiability of `y ↦ ∫ R Q(·, y)` on `𝔻*` (the PV derivative). -/
theorem s3d_D2_pointwise {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    ∀ z ∈ unitDiscExterior,
      DifferentiableAt ℝ (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z ∧
      deriv (fun x : ℂ => deriv (fun y : ℂ => (((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) y) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) y / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) y ^ 2 -
        deriv (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) / deriv (gsans (beltramiMul a κ)) y)) x + preSchwarzian (gsans (beltramiMul a κ)) x * (((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) x) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) x / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) x ^ 2 -
        deriv (gsans (beltramiMul a κ)) x * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((x + 1) * (x + I) * (x - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - x))))) / deriv (gsans (beltramiMul a κ)) x)) z +
          dz (fun y : ℂ => preSchwarzian (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z = (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 - 1 / (ζ - y) ^ 2)) z +
        2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) * (deriv (gsans (beltramiMul a κ)) z / derivAtInfty (gsans (beltramiMul a κ)) - 1)) ∧
      deriv (fun x : ℂ => deriv (fun y : ℂ => ((((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) y ^ 2 -
        deriv (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) / deriv (gsans (beltramiMul a κ)) y)) x + preSchwarzian (gsans (beltramiMul a κ)) x * ((((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) x ^ 2 -
        deriv (gsans (beltramiMul a κ)) x * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((x + 1) * (x + I) * (x - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - x))))) / deriv (gsans (beltramiMul a κ)) x)) z +
          dz (fun y : ℂ => preSchwarzian (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z = ((2 / π : ℂ) * (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) +
        2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) * (deriv (gsans (beltramiMul a κ)) z / derivAtInfty (gsans (beltramiMul a κ)) - 1)) := by
  have hd := delta0_bounds
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.2 (has.trans hd.2)
  have hμ : beltramiMul a (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨r, hr, ρ, hρ, R0, hR0, F, G, H, -, -, -, -, -, -, -, ht⟩ := s3g_D_ext hκ hκD ha has haL haD hm hmD
  obtain ⟨-, ⟨hGd, hGi, hGd', hGg⟩, -⟩ := ht 0 (mem_ball_self hr)
  simp only [zero_smul, add_zero] at hGg
  have hRm : AEStronglyMeasurable (RnmFun (toLinf m) a) (volume.restrict unitDiscExterior) :=
    (bc_Rnm_memLp haB (toLinf m)).aestronglyMeasurable
  have hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior),
      ‖RnmFun (toLinf m) a u‖ ≤ (1 / (1 - ‖a‖ ^ 2)) * ‖toLinf m‖ :=
    bc_invFun_pullback_ae haB (bc_Rnm_integrand_bound haB (toLinf m))
  obtain ⟨hSm, hSb⟩ := d2e_S_ae hRm hRb
  -- `‖g'‖` is bounded on `𝔻*`: `d2e_growth` for `‖u‖ ≥ 4`, compactness of `1 ≤ ‖u‖ ≤ 4` for `G'`
  obtain ⟨c, -, C, hC⟩ := d2e_growth hpair
  have hdd := (d2e_basic hρ hGd hGi hGd' hGg).2.2.2.1
  have hO : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨M1, hM1⟩ := ((isCompact_closedBall (0 : ℂ) 4).inter_right
    (isClosed_le continuous_const continuous_norm)).exists_bound_of_continuousOn
    ((hGd.deriv hO).continuousOn.mono fun z hz => show ρ < ‖z‖ from lt_of_lt_of_le hρ hz.2)
  have hM : ∀ u ∈ unitDiscExterior, ‖deriv (gsans (beltramiMul a κ)) u‖ ≤ max M1 C := by
    intro u hu
    have hu1 : 1 < ‖u‖ := hu
    by_cases h4 : 4 ≤ ‖u‖
    · exact (hC u h4).2.trans (le_max_right _ _)
    · rw [hdd u hu]
      exact (hM1 u ⟨mem_closedBall_zero_iff.2 (by linarith), hu1.le⟩).trans (le_max_left _ _)
  have hC0 := d2p_merged_int hpair hM (fun u hu => d2e_koebe hpair hu) hRm hRb
  have h1 := d2p_tpart (derivAtInfty (gsans (beltramiMul a κ))) hρ hGd hGi hGd' hGg (fun u hu => d2e_koebe hpair hu)
    (d2e_growth hpair) hRm hRb (s3d_D2_gd1_C1 hκ hκD ha has haL haD hm hmD) hC0
  have h2 := d2p_tbar (S := fun ζ => conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2)
    (derivAtInfty (gsans (beltramiMul a κ))) hρ hGd hGi hGd' hGg hSm hSb
  intro z hz
  exact ⟨(h1 z hz).1, (h1 z hz).2, h2 z hz⟩

/-- [(Λ) helper] For a real-linear `L : ℂ → ℂ`, `L w - i L(i w) = w (L 1 - i L i)`. -/
theorem s3dl_clm (L : ℂ →L[ℝ] ℂ) (w : ℂ) : L w - I * L (I * w) = w * (L 1 - I * L I) := by
  have h : ∀ v : ℂ, L v = (v.re : ℂ) * L 1 + (v.im : ℂ) * L I := by
    intro v
    have e1 : v = v.re • (1 : ℂ) + v.im • I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one]
      exact (re_add_im v).symm
    conv_lhs => rw [e1]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  rw [h w, h (I * w)]
  simp only [mul_re, mul_im, I_re, I_im, zero_mul, one_mul, zero_sub, zero_add]
  push_cast
  conv_rhs => rw [← re_add_im w]
  linear_combination ((w.im : ℂ) * L I) * I_sq

/-- [(Λ) helper] **Stokes on an annulus** in polar coordinates: for `Φ` of class `C¹` near the closed annulus
`r₀ ≤ |z| ≤ R₁`, `∫_{r₀<|z|<R₁} ∂_z Φ = ½ (∮_{R₁} - ∮_{r₀}) Φ(r e^{iθ}) r e^{-iθ} dθ`. -/
theorem s3dl_stokes {Φ : ℂ → ℂ} {U : Set ℂ} {r0 R1 : ℝ} (hU : IsOpen U) (hr0 : 0 < r0) (hr : r0 < R1)
    (hK : ∀ z : ℂ, r0 ≤ ‖z‖ → ‖z‖ ≤ R1 → z ∈ U) (hΦ : ContDiffOn ℝ 1 Φ U) :
    ∫ z in {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < R1}, dz Φ z =
      (1 / 2 : ℂ) * ((∫ θ in (-π)..π, (R1 : ℂ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) *
          Φ (R1 * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))) -
        ∫ θ in (-π)..π, (r0 : ℂ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) *
          Φ (r0 * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))) := by
  obtain ⟨e, he⟩ : ∃ e : ℝ → ℂ, e = fun θ => (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := ⟨_, rfl⟩
  obtain ⟨e', he'⟩ : ∃ e' : ℝ → ℂ, e' = fun θ => (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := ⟨_, rfl⟩
  have hev : ∀ θ : ℝ, (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I = e θ := fun θ => by rw [he]
  have hev' : ∀ θ : ℝ, (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I = e' θ := fun θ => by rw [he']
  simp only [hev, hev']
  have hpi : -π < π := by linarith [Real.pi_pos]
  -- the unit circle parametrization
  have hee : ∀ θ, e' θ * e θ = 1 := by
    intro θ
    rw [← hev, ← hev']
    have h : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq θ
    linear_combination h - (Real.sin θ : ℂ) ^ 2 * I_sq
  have hen : ∀ θ, ‖e θ‖ = 1 := by
    intro θ
    rw [← hev, Complex.ofReal_cos, Complex.ofReal_sin]
    exact Complex.norm_cos_add_sin_mul_I θ
  have hpn : ∀ r θ : ℝ, 0 ≤ r → ‖(r : ℂ) * e θ‖ = r := by
    intro r θ h0
    rw [norm_mul, hen, mul_one, Complex.norm_real, Real.norm_of_nonneg h0]
  have hpU : ∀ r θ : ℝ, r ∈ Icc r0 R1 → (r : ℂ) * e θ ∈ U := fun r θ hr' =>
    hK _ (by rw [hpn r θ (hr0.le.trans hr'.1)]; exact hr'.1) (by rw [hpn r θ (hr0.le.trans hr'.1)]; exact hr'.2)
  have hde : ∀ θ, HasDerivAt e (I * e θ) θ := by
    intro θ
    have h := ((Real.hasDerivAt_cos θ).ofReal_comp).add (((Real.hasDerivAt_sin θ).ofReal_comp).mul_const I)
    rw [he]
    convert h using 1
    beta_reduce
    rw [Complex.ofReal_neg]
    linear_combination (Real.sin θ : ℂ) * I_sq
  have hde' : ∀ θ, HasDerivAt e' (-I * e' θ) θ := by
    intro θ
    have h := ((Real.hasDerivAt_cos θ).ofReal_comp).sub (((Real.hasDerivAt_sin θ).ofReal_comp).mul_const I)
    rw [he']
    convert h using 1
    beta_reduce
    rw [Complex.ofReal_neg]
    linear_combination (Real.sin θ : ℂ) * I_sq
  have hec : Continuous e := by rw [he]; fun_prop
  have hec' : Continuous e' := by rw [he']; fun_prop
  have hpi1 : e π = e (-π) := by rw [he]; simp only [Real.cos_neg, Real.sin_neg, Real.sin_pi, neg_zero]
  have hpi1' : e' π = e' (-π) := by rw [he']; simp only [Real.cos_neg, Real.sin_neg, Real.sin_pi, neg_zero]
  -- regularity of `Φ`
  have hΦd : ∀ z ∈ U, HasFDerivAt Φ (fderiv ℝ Φ z) z := fun z hz =>
    (((hΦ.differentiableOn one_ne_zero) z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hfc : ContinuousOn (fderiv ℝ Φ) U := hΦ.continuousOn_fderiv_of_isOpen hU le_rfl
  have hΦc : ContinuousOn Φ U := hΦ.continuousOn
  -- the radial and angular primitives
  obtain ⟨Dr, hDr⟩ : ∃ Dr : ℝ → ℝ → ℂ, Dr = fun (r θ : ℝ) => e' θ * Φ ((r : ℂ) * e θ) +
      (r : ℂ) * e' θ * fderiv ℝ Φ ((r : ℂ) * e θ) (e θ) := ⟨_, rfl⟩
  obtain ⟨Dt, hDt⟩ : ∃ Dt : ℝ → ℝ → ℂ, Dt = fun (r θ : ℝ) => -I * (-I * e' θ) * Φ ((r : ℂ) * e θ) +
      -I * e' θ * fderiv ℝ Φ ((r : ℂ) * e θ) ((r : ℂ) * (I * e θ)) := ⟨_, rfl⟩
  have hFr : ∀ θ : ℝ, ∀ r ∈ Icc r0 R1,
      HasDerivAt (fun r : ℝ => (r : ℂ) * e' θ * Φ (r * e θ)) (Dr r θ) r := by
    intro θ r hr'
    have hp : HasDerivAt (fun r : ℝ => (r : ℂ) * e θ) (e θ) r := by
      simpa using ((hasDerivAt_id r).ofReal_comp).mul_const (e θ)
    have hl : HasDerivAt (fun r : ℝ => (r : ℂ) * e' θ) (e' θ) r := by
      simpa using ((hasDerivAt_id r).ofReal_comp).mul_const (e' θ)
    have hq := (hΦd _ (hpU r θ hr')).comp_hasDerivAt r hp
    rw [hDr]
    exact hl.mul hq
  have hGt : ∀ r ∈ Icc r0 R1, ∀ θ : ℝ,
      HasDerivAt (fun θ : ℝ => -I * e' θ * Φ (r * e θ)) (Dt r θ) θ := by
    intro r hr' θ
    have hp : HasDerivAt (fun θ : ℝ => (r : ℂ) * e θ) (r * (I * e θ)) θ := (hde θ).const_mul (r : ℂ)
    have hl : HasDerivAt (fun θ : ℝ => -I * e' θ) (-I * (-I * e' θ)) θ := (hde' θ).const_mul (-I)
    have hq := (hΦd _ (hpU r θ hr')).comp_hasDerivAt θ hp
    rw [hDt]
    exact hl.mul hq
  have hsum : ∀ r θ : ℝ, Dr r θ + Dt r θ = 2 * ((r : ℂ) * dz Φ (r * e θ)) := by
    intro r θ
    obtain ⟨L, hL⟩ : ∃ L : ℂ →L[ℝ] ℂ, L = fderiv ℝ Φ ((r : ℂ) * e θ) := ⟨_, rfl⟩
    have hdz : dz Φ ((r : ℂ) * e θ) = (L 1 - I * L I) / 2 := by rw [hL]; rfl
    have h1 : L ((r : ℂ) * (I * e θ)) = (r : ℂ) * L (I * e θ) := by
      rw [← Complex.real_smul, map_smul, Complex.real_smul]
    have h2 := s3dl_clm L (e θ)
    rw [hDr, hDt]
    beta_reduce
    rw [← hL, hdz, h1]
    linear_combination (e' θ * Φ ((r : ℂ) * e θ)) * I_sq + ((r : ℂ) * e' θ) * h2 +
      ((r : ℂ) * (L 1 - I * L I)) * hee θ
  -- continuity on the compact rectangle
  have hS : IsCompact (Icc r0 R1 ×ˢ Icc (-π) π) := isCompact_Icc.prod isCompact_Icc
  have hq : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * e p.2) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul (hec.comp continuous_snd)
  have hmaps : MapsTo (fun p : ℝ × ℝ => (p.1 : ℂ) * e p.2) (Icc r0 R1 ×ˢ Icc (-π) π) U :=
    fun p hp => hpU p.1 p.2 hp.1
  have hΦq : ContinuousOn (fun p : ℝ × ℝ => Φ ((p.1 : ℂ) * e p.2)) (Icc r0 R1 ×ˢ Icc (-π) π) :=
    hΦc.comp hq.continuousOn hmaps
  have hfq : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ Φ ((p.1 : ℂ) * e p.2)) (Icc r0 R1 ×ˢ Icc (-π) π) :=
    hfc.comp hq.continuousOn hmaps
  have hr1 : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ)) := Complex.continuous_ofReal.comp continuous_fst
  have he2 : Continuous (fun p : ℝ × ℝ => e p.2) := hec.comp continuous_snd
  have he2' : Continuous (fun p : ℝ × ℝ => e' p.2) := hec'.comp continuous_snd
  have hcI : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dz Φ ((p.1 : ℂ) * e p.2)) (Icc r0 R1 ×ˢ Icc (-π) π) := by
    have h : ContinuousOn (fun p : ℝ × ℝ => dz Φ ((p.1 : ℂ) * e p.2)) (Icc r0 R1 ×ˢ Icc (-π) π) :=
      ((hfq.clm_apply continuousOn_const).sub (continuousOn_const.mul (hfq.clm_apply continuousOn_const))).div_const 2
    exact hr1.continuousOn.mul h
  have hcDr : ContinuousOn (fun p : ℝ × ℝ => Dr p.1 p.2) (Icc r0 R1 ×ˢ Icc (-π) π) := by
    rw [hDr]
    exact (he2'.continuousOn.mul hΦq).add ((hr1.mul he2').continuousOn.mul (hfq.clm_apply he2.continuousOn))
  have hcDt : ContinuousOn (fun p : ℝ × ℝ => Dt p.1 p.2) (Icc r0 R1 ×ˢ Icc (-π) π) := by
    rw [hDt]
    exact ((continuous_const.mul (continuous_const.mul he2')).continuousOn.mul hΦq).add
      ((continuous_const.mul he2').continuousOn.mul (hfq.clm_apply (hr1.mul (continuous_const.mul he2)).continuousOn))
  have hsl : ∀ {f : ℝ × ℝ → ℂ}, ContinuousOn f (Icc r0 R1 ×ˢ Icc (-π) π) → ∀ r ∈ Icc r0 R1,
      ContinuousOn (fun θ : ℝ => f (r, θ)) (Icc (-π) π) := fun {f} hf r hr' =>
    hf.comp (Continuous.prodMk continuous_const continuous_id).continuousOn fun θ hθ => ⟨hr', hθ⟩
  have hsl2 : ∀ {f : ℝ × ℝ → ℂ}, ContinuousOn f (Icc r0 R1 ×ˢ Icc (-π) π) → ∀ θ ∈ Icc (-π) π,
      ContinuousOn (fun r : ℝ => f (r, θ)) (Icc r0 R1) := fun {f} hf θ hθ =>
    hf.comp (Continuous.prodMk continuous_id continuous_const).continuousOn fun r hr' => ⟨hr', hθ⟩
  have hsub : Ioo r0 R1 ×ˢ Ioo (-π) π ⊆ Icc r0 R1 ×ˢ Icc (-π) π := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  -- (1) polar coordinates
  have hA : MeasurableSet {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < R1} :=
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
  have h1 : ∫ z in {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < R1}, dz Φ z =
      ∫ p in Ioo r0 R1 ×ˢ Ioo (-π) π, (p.1 : ℂ) * dz Φ ((p.1 : ℂ) * e p.2) := by
    rw [← integral_indicator hA, ← Complex.integral_comp_polarCoord_symm]
    have hT : MeasurableSet (polarCoord.target) := polarCoord.open_target.measurableSet
    rw [setIntegral_congr_fun hT (g := (Ioo r0 R1 ×ˢ (univ : Set ℝ)).indicator
      fun p : ℝ × ℝ => (p.1 : ℂ) * dz Φ ((p.1 : ℂ) * e p.2)) ?_]
    · rw [setIntegral_indicator (measurableSet_Ioo.prod MeasurableSet.univ)]
      have hs : polarCoord.target ∩ (Ioo r0 R1 ×ˢ (univ : Set ℝ)) = Ioo r0 R1 ×ˢ Ioo (-π) π := by
        rw [show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl]
        ext p
        simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo, mem_univ, and_true]
        constructor
        · rintro ⟨⟨-, h2⟩, h3⟩
          exact ⟨h3, h2⟩
        · rintro ⟨h3, h2⟩
          exact ⟨⟨by linarith [h3.1], h2⟩, h3⟩
      rw [hs]
    · intro p hp
      have hp1 : 0 < p.1 := hp.1
      have hsym : Complex.polarCoord.symm p = (p.1 : ℂ) * e p.2 := by rw [Complex.polarCoord_symm_apply, hev]
      have hn : ‖(p.1 : ℂ) * e p.2‖ = p.1 := hpn p.1 p.2 hp1.le
      show p.1 • {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < R1}.indicator (dz Φ) (Complex.polarCoord.symm p) = _
      rw [hsym]
      by_cases hm : p.1 ∈ Ioo r0 R1
      · rw [indicator_of_mem (show p ∈ Ioo r0 R1 ×ˢ (univ : Set ℝ) from ⟨hm, trivial⟩),
          indicator_of_mem (show (p.1 : ℂ) * e p.2 ∈ {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < R1} by
            show r0 < ‖(p.1 : ℂ) * e p.2‖ ∧ ‖(p.1 : ℂ) * e p.2‖ < R1
            rw [hn]
            exact hm), Complex.real_smul]
      · rw [indicator_of_notMem (show p ∉ Ioo r0 R1 ×ˢ (univ : Set ℝ) from fun h => hm h.1),
          indicator_of_notMem (show (p.1 : ℂ) * e p.2 ∉ {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < R1} from fun h => hm (by
            have h' : r0 < ‖(p.1 : ℂ) * e p.2‖ ∧ ‖(p.1 : ℂ) * e p.2‖ < R1 := h
            rw [hn] at h'
            exact h')), smul_zero]
  -- (2) Fubini
  have hint1 : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dz Φ ((p.1 : ℂ) * e p.2)) (Ioo r0 R1 ×ˢ Ioo (-π) π)
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hcI.integrableOn_compact hS).mono_set hsub
  have h2 : ∫ p in Ioo r0 R1 ×ˢ Ioo (-π) π, (p.1 : ℂ) * dz Φ ((p.1 : ℂ) * e p.2) =
      ∫ r in Ioo r0 R1, ∫ θ in Ioo (-π) π, (r : ℂ) * dz Φ ((r : ℂ) * e θ) := by
    rw [Measure.volume_eq_prod]
    exact setIntegral_prod _ hint1
  -- (3) the angular part integrates to `0`
  have h3 : ∀ r ∈ Ioo r0 R1, ∫ θ in Ioo (-π) π, (r : ℂ) * dz Φ ((r : ℂ) * e θ) =
      (1 / 2 : ℂ) * ∫ θ in Ioo (-π) π, Dr r θ := by
    intro r hr'
    have hrI : r ∈ Icc r0 R1 := Ioo_subset_Icc_self hr'
    have hDrc := hsl hcDr r hrI
    have hDtc := hsl hcDt r hrI
    have hDrI : IntegrableOn (fun θ => Dr r θ) (Ioo (-π) π) :=
      (hDrc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
    have hDtI : IntegrableOn (fun θ => Dt r θ) (Ioo (-π) π) :=
      (hDtc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
    have hDt0 : ∫ θ in Ioo (-π) π, Dt r θ = 0 := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi.le,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hGt r hrI θ)
          (hDtc.intervalIntegrable_of_Icc hpi.le)]
      simp only [hpi1, hpi1', sub_self]
    calc ∫ θ in Ioo (-π) π, (r : ℂ) * dz Φ ((r : ℂ) * e θ)
        = ∫ θ in Ioo (-π) π, (1 / 2 : ℂ) * (Dr r θ + Dt r θ) :=
          setIntegral_congr_fun measurableSet_Ioo fun θ _ => by rw [hsum r θ]; ring
      _ = (1 / 2 : ℂ) * ((∫ θ in Ioo (-π) π, Dr r θ) + ∫ θ in Ioo (-π) π, Dt r θ) := by
          rw [integral_const_mul, integral_add hDrI hDtI]
      _ = (1 / 2 : ℂ) * ∫ θ in Ioo (-π) π, Dr r θ := by rw [hDt0, add_zero]
  -- (4) swap and integrate radially
  have hDrprod : Integrable (Function.uncurry fun r θ => Dr r θ)
      ((volume.restrict (Ioo r0 R1)).prod (volume.restrict (Ioo (-π) π))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hcDr.integrableOn_compact hS).mono_set hsub
  have h5 : ∀ θ ∈ Icc (-π) π, ∫ r in Ioo r0 R1, Dr r θ =
      (R1 : ℂ) * e' θ * Φ (R1 * e θ) - (r0 : ℂ) * e' θ * Φ (r0 * e θ) := by
    intro θ hθ
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun r hr' => hFr θ r (by rwa [uIcc_of_le hr.le] at hr'))
        ((hsl2 hcDr θ hθ).intervalIntegrable_of_Icc hr.le)]
  have hFc : ∀ r ∈ Icc r0 R1, ContinuousOn (fun θ : ℝ => (r : ℂ) * e' θ * Φ (r * e θ)) (Icc (-π) π) := by
    intro r hr'
    refine (continuous_const.mul hec').continuousOn.mul ?_
    exact hΦc.comp ((continuous_const.mul hec).continuousOn) fun θ _ => hpU r θ hr'
  rw [h1, h2, setIntegral_congr_fun measurableSet_Ioo h3, integral_const_mul,
    integral_integral_swap hDrprod, setIntegral_congr_fun measurableSet_Ioo fun θ hθ => h5 θ (Ioo_subset_Icc_self hθ),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi.le,
    intervalIntegral.integral_sub ((hFc R1 ⟨hr.le, le_rfl⟩).intervalIntegrable_of_Icc hpi.le)
      ((hFc r0 ⟨le_rfl, hr.le⟩).intervalIntegrable_of_Icc hpi.le)]

/-- [(Λ) helper] `conj Dn(1/ū) = i Dn(u) / u³`, in the form `Dn`-of-`u⁻¹`-with-conjugated-node. -/
theorem s3dl_conj_dn {u : ℂ} (hu : u ≠ 0) :
    (u⁻¹ + 1) * (u⁻¹ - I) * (u⁻¹ - 1) = I * ((u + 1) * (u + I) * (u - 1)) * u⁻¹ ^ 3 := by
  have h1 : u⁻¹ + 1 = (u + 1) * u⁻¹ := by rw [add_mul, mul_inv_cancel₀ hu, one_mul, add_comm]
  have h2 : u⁻¹ - I = -I * (u + I) * u⁻¹ := by
    have h : -I * (u + I) * u⁻¹ = -I * (u * u⁻¹) - I ^ 2 * u⁻¹ := by ring
    rw [h, mul_inv_cancel₀ hu, I_sq]
    ring
  have h3 : u⁻¹ - 1 = -(u - 1) * u⁻¹ := by
    have h : -(u - 1) * u⁻¹ = -(u * u⁻¹) + u⁻¹ := by ring
    rw [h, mul_inv_cancel₀ hu]
    ring
  rw [h1, h2, h3]
  ring

/-- [(Λ) helper] **Tangency on `𝕊¹`.** For `|y| = 1`, `conj γ̇₂(y) = -γ̇(y)/y²`: the `t̄`-variation is the reflection
of the `t`-variation (substitute `ζ = 1/w̄`, `s4v_integral_reflection`). -/
theorem s3dl_tangent (R : ℂ → ℂ) {y : ℂ} (hy : ‖y‖ = 1) :
    conj (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
      (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) =
    -((-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ *
      (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) / y ^ 2) := by
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hy
    exact zero_ne_one hy
  have hcy : conj y = y⁻¹ := by
    have h := Complex.mul_conj' y
    rw [hy] at h
    push_cast at h
    rw [one_pow] at h
    exact eq_inv_of_mul_eq_one_right h
  have hpi : conj (-(1 / π : ℂ)) = -(1 / π : ℂ) := by
    rw [map_neg, map_div₀, map_one, Complex.conj_ofReal]
  rw [s4v_integral_reflection, map_mul, ← integral_conj, hpi]
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hR : -((-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ *
      (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) / y ^ 2) =
      -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ *
        (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) * -(y ^ 2)⁻¹ := by
    rw [integral_mul_const]
    ring
  rw [hR]
  congr 1
  refine setIntegral_congr_fun hE fun w hw => ?_
  have hw1 : 1 < ‖w‖ := hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    linarith
  have hcw : conj w ≠ 0 := (map_ne_zero _).2 hw0
  have hwy : w - y ≠ 0 := by
    intro h
    have : w = y := sub_eq_zero.1 h
    rw [this, hy] at hw1
    linarith
  have hyw : y - w ≠ 0 := fun h => hwy (by rw [← neg_sub, h, neg_zero])
  have hDw := d2e_dn_ne hw1
  have hD1 : w + 1 ≠ 0 := fun h => hDw (by rw [h, zero_mul, zero_mul])
  have hD2 : w + I ≠ 0 := fun h => hDw (by rw [h, mul_zero, zero_mul])
  have hD3 : w - 1 ≠ 0 := fun h => hDw (by rw [h, mul_zero])
  have hr : refl w = (conj w)⁻¹ := rfl
  have hn4 : ((((‖w‖ ^ 4)⁻¹ : ℝ)) : ℂ) = ((w * conj w) ^ 2)⁻¹ := by
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [hn4]
  simp only [map_mul, map_div₀, map_pow, map_sub, map_add, map_one, map_inv₀, conj_conj, conj_I, hr, one_div,
    inv_inv, hcy, ← sub_eq_add_neg]
  rw [s3dl_conj_dn hy0, s3dl_conj_dn hw0]
  field_simp
  ring

/-- [(Λ) helper] For `A` holomorphic at `z`: `∂_z(Ā · (A u)) = Ā ∂_z(A u)`. -/
theorem s3dl_wirt {A u : ℂ → ℂ} {z : ℂ} (hA : DifferentiableAt ℂ A z) (hu : DifferentiableAt ℝ u z) :
    dz (fun y => conj (A y) * (A y * u y)) z = conj (A z) * dz (fun y => A y * u y) z := by
  have h1 : HasFDerivAt (fun y => conj (A y))
      ((conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℂ A z).restrictScalars ℝ)) z :=
    (conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt.comp z (hA.hasFDerivAt.restrictScalars ℝ)
  have h2 : HasFDerivAt (fun y => A y * u y) (fderiv ℝ (fun y => A y * u y) z) z :=
    ((hA.restrictScalars ℝ).mul hu).hasFDerivAt
  have hm : HasFDerivAt (fun y => conj (A y) * (A y * u y))
      (conj (A z) • fderiv ℝ (fun y => A y * u y) z +
        (A z * u z) • (conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℂ A z).restrictScalars ℝ)) z := h1.mul h2
  have hI : fderiv ℂ A z I = I * fderiv ℂ A z 1 := by
    have h : (I : ℂ) = I • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    conv_lhs => rw [h]
    rw [map_smul, smul_eq_mul]
  show (fderiv ℝ (fun y => conj (A y) * (A y * u y)) z 1 -
      I * fderiv ℝ (fun y => conj (A y) * (A y * u y)) z I) / 2 =
    conj (A z) * ((fderiv ℝ (fun y => A y * u y) z 1 - I * fderiv ℝ (fun y => A y * u y) z I) / 2)
  rw [hm.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul, hI,
    map_mul, conj_I]
  linear_combination (A z * u z * conj (fderiv ℂ A z 1) / 2) * I_sq

/-- [(Λ) helper] A Hölder bound gives continuity. -/
theorem s3dl_holder {T : ℂ → ℂ} {K p : ℝ} (hp : 0 < p) (h : ∀ z₁ z₂ : ℂ, ‖T z₁ - T z₂‖ ≤ K * ‖z₁ - z₂‖ ^ p) :
    Continuous T := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous (fun w : ℂ => K * ‖w - z‖ ^ p) :=
    continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const fun _ => Or.inr hp.le)
  have h0 : Tendsto (fun w : ℂ => K * ‖w - z‖ ^ p) (𝓝 z) (𝓝 0) := by
    have h' := hc.tendsto z
    simp only [sub_self, norm_zero, Real.zero_rpow hp.ne', mul_zero] at h'
    exact h'
  exact squeeze_zero (fun w => norm_nonneg _) (fun w => h w z) h0

/-- [(Λ) helper] **Continuity of the normalized Cauchy transform** `y ↦ ∫_S W(ζ) Dn(y)/(Dn(ζ)(ζ - y))` on `|y| ≤ 2`, for `W`
bounded on `S` (split `N = 1/(ζ - y) - Q(ζ, y)/Dn(ζ)` on `|ζ| < 4`: Cauchy transform of an `L⁴` function plus a quadratic
polynomial in `y`; dominated convergence on `|ζ| ≥ 4`). -/
theorem s3dl_cont {W : ℂ → ℂ} {S : Set ℂ} {Wb : ℝ} (hS : MeasurableSet S)
    (hWm : AEStronglyMeasurable W (volume.restrict S)) (hWb : ∀ᵐ ζ ∂(volume.restrict S), ‖W ζ‖ ≤ Wb) :
    ContinuousOn (fun y : ℂ => ∫ ζ in S, W ζ * (((y + 1) * (y + I) * (y - 1)) /
      (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) (closedBall 0 2) := by
  have hB : MeasurableSet (ball (0 : ℂ) 4) := measurableSet_ball
  have hS1m : MeasurableSet (S ∩ ball (0 : ℂ) 4) := hS.inter hB
  have hS2m : MeasurableSet (S \ ball (0 : ℂ) 4) := hS.diff hB
  have hW1 : AEStronglyMeasurable W (volume.restrict (S ∩ ball (0 : ℂ) 4)) :=
    hWm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hW2 : AEStronglyMeasurable W (volume.restrict (S \ ball (0 : ℂ) 4)) :=
    hWm.mono_measure (Measure.restrict_mono sdiff_subset le_rfl)
  have hWb1 : ∀ᵐ ζ ∂(volume.restrict (S ∩ ball (0 : ℂ) 4)), ‖W ζ‖ ≤ Wb :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hWb
  have hWb2 : ∀ᵐ ζ ∂(volume.restrict (S \ ball (0 : ℂ) 4)), ‖W ζ‖ ≤ Wb :=
    ae_restrict_of_ae_restrict_of_subset sdiff_subset hWb
  have hDnm : Measurable (fun ζ : ℂ => (ζ + 1) * (ζ + I) * (ζ - 1)) := by fun_prop
  -- polynomial coefficients
  have hcoef : ∀ q : ℂ → ℂ, Continuous q →
      IntegrableOn (fun ζ => W ζ * (q ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) (S ∩ ball (0 : ℂ) 4) := by
    intro q hq
    obtain ⟨Cq, hCq⟩ := (isCompact_closedBall (0 : ℂ) 4).exists_bound_of_continuousOn hq.continuousOn
    refine Integrable.mono' ((d2e_dn_int.integrableOn).const_mul (Wb * Cq))
      (hW1.mul (hq.measurable.div hDnm).aestronglyMeasurable) ?_
    filter_upwards [hWb1, ae_restrict_mem hS1m] with ζ hζ hmem
    have hq' := hCq ζ (ball_subset_closedBall hmem.2)
    rw [norm_mul, norm_div, div_eq_mul_inv, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hζ hq' (norm_nonneg _) ((norm_nonneg _).trans hζ))
      (inv_nonneg.2 (norm_nonneg _))
  obtain ⟨c0, hc0⟩ : ∃ c : ℂ, c = ∫ ζ in S ∩ ball (0 : ℂ) 4, W ζ *
      ((ζ ^ 2 + I * ζ - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1))) := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ c : ℂ, c = ∫ ζ in S ∩ ball (0 : ℂ) 4, W ζ * ((ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1))) :=
    ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : ℂ, c = ∫ ζ in S ∩ ball (0 : ℂ) 4, W ζ * (1 / ((ζ + 1) * (ζ + I) * (ζ - 1))) := ⟨_, rfl⟩
  have hi0 := hcoef (fun ζ => ζ ^ 2 + I * ζ - 1) (by fun_prop)
  have hi1 := hcoef (fun ζ => ζ + I) (by fun_prop)
  have hi2 := hcoef (fun _ => 1) continuous_const
  -- the Cauchy-transform part
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ → ℂ, ω = (S ∩ ball (0 : ℂ) 4).indicator W := ⟨_, rfl⟩
  haveI hfin : IsFiniteMeasure (volume.restrict (S ∩ ball (0 : ℂ) 4)) :=
    isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_right))
  have hmem : MemLp ω (ENNReal.ofReal 4) volume := by
    rw [hω, memLp_indicator_iff_restrict hS1m]
    exact MemLp.of_bound hW1 Wb hWb1
  obtain ⟨M2, hM2⟩ := lemma11_2 (p := 4) (by norm_num)
  have hT : Continuous (cauchyT ω) := s3dl_holder (by norm_num : (0 : ℝ) < (4 - 2) / 4) (hM2 ω hmem)
  have hpi0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hT1 : ∀ y : ℂ, ∫ ζ in S ∩ ball (0 : ℂ) 4, W ζ * (1 / (ζ - y)) = -(π : ℂ) * cauchyT ω y := by
    intro y
    have hc : cauchyT ω y = -(1 / π : ℂ) * ∫ ζ, ω ζ / (ζ - y) := rfl
    have hf : (fun ζ => ω ζ / (ζ - y)) = (S ∩ ball (0 : ℂ) 4).indicator fun ζ => W ζ * (1 / (ζ - y)) := by
      funext ζ
      rw [hω]
      by_cases h : ζ ∈ S ∩ ball (0 : ℂ) 4
      · rw [indicator_of_mem h, indicator_of_mem h, mul_one_div]
      · rw [indicator_of_notMem h, indicator_of_notMem h, zero_div]
    rw [hc, hf, integral_indicator hS1m]
    field_simp
  -- the far part: dominated convergence
  have hbI : Integrable (fun ζ : ℂ => Wb * (27 * (8 * (1 + ‖ζ‖) ^ (-(3 : ℝ)) * 2⁻¹)))
      (volume.restrict (S \ ball (0 : ℂ) 4)) := by
    refine Integrable.integrableOn ?_
    refine Integrable.const_mul ?_ _
    refine Integrable.const_mul ?_ _
    refine Integrable.mul_const ?_ _
    refine Integrable.const_mul ?_ _
    exact integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  have hNm : ∀ y : ℂ, Measurable fun ζ : ℂ => ((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)) :=
    fun y => measurable_const.div (hDnm.mul (measurable_id.sub_const y))
  have hFm : ∀ y ∈ closedBall (0 : ℂ) 2, AEStronglyMeasurable (fun ζ => W ζ * (((y + 1) * (y + I) * (y - 1)) /
      (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) (volume.restrict (S \ ball (0 : ℂ) 4)) :=
    fun y _ => hW2.mul (hNm y).aestronglyMeasurable
  have hFb : ∀ y ∈ closedBall (0 : ℂ) 2, ∀ᵐ ζ ∂(volume.restrict (S \ ball (0 : ℂ) 4)),
      ‖W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))‖ ≤
        Wb * (27 * (8 * (1 + ‖ζ‖) ^ (-(3 : ℝ)) * 2⁻¹)) := by
    intro y hy
    have hy2 : ‖y‖ ≤ 2 := mem_closedBall_zero_iff.1 hy
    filter_upwards [hWb2, ae_restrict_mem hS2m] with ζ hζ hm
    have hz4 : 4 ≤ ‖ζ‖ := by
      have h := hm.2
      rw [mem_ball_zero_iff, not_lt] at h
      exact h
    have hD := d2e_dn_far (by linarith : (3 : ℝ) ≤ ‖ζ‖)
    have hzy : 2 ≤ ‖ζ - y‖ := by
      have := norm_sub_norm_le ζ y
      linarith
    have hDy : ‖(y + 1) * (y + I) * (y - 1)‖ ≤ 27 := by
      have h1 : ‖y + 1‖ ≤ 3 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
      have h2 : ‖y + I‖ ≤ 3 := (norm_add_le _ _).trans (by rw [Complex.norm_I]; linarith)
      have h3 : ‖y - 1‖ ≤ 3 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
      rw [norm_mul, norm_mul]
      calc ‖y + 1‖ * ‖y + I‖ * ‖y - 1‖ ≤ 3 * 3 * 3 := by gcongr
        _ = 27 := by norm_num
    have hzy' : ‖ζ - y‖⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hzy
    rw [norm_mul, norm_div, norm_mul ((ζ + 1) * (ζ + I) * (ζ - 1)) (ζ - y), div_eq_mul_inv, mul_inv]
    have hWn : 0 ≤ Wb := (norm_nonneg _).trans hζ
    refine mul_le_mul hζ ?_ (by positivity) hWn
    refine mul_le_mul hDy ?_ (by positivity) (by norm_num)
    exact mul_le_mul hD hzy' (by positivity) (by positivity)
  have hFc : ∀ᵐ ζ ∂(volume.restrict (S \ ball (0 : ℂ) 4)), ContinuousOn (fun y : ℂ => W ζ *
      (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) (closedBall 0 2) := by
    filter_upwards [ae_restrict_mem hS2m] with ζ hm
    have hz4 : 4 ≤ ‖ζ‖ := by
      have h := hm.2
      rw [mem_ball_zero_iff, not_lt] at h
      exact h
    have hDz := d2e_dn_ne (by linarith : 1 < ‖ζ‖)
    refine continuousOn_const.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => ?_)
    refine mul_ne_zero hDz (sub_ne_zero.2 fun h => ?_)
    have hy2 : ‖y‖ ≤ 2 := mem_closedBall_zero_iff.1 hy
    rw [h] at hz4
    linarith
  have hT3 := continuousOn_of_dominated hFm hFb hbI hFc
  -- assemble
  have hcont : ContinuousOn (fun y : ℂ => -(π : ℂ) * cauchyT ω y - (c0 + y * c1 + y ^ 2 * c2) +
      ∫ ζ in S \ ball (0 : ℂ) 4, W ζ * (((y + 1) * (y + I) * (y - 1)) /
        (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) (closedBall 0 2) := by
    refine ContinuousOn.add ?_ hT3
    exact (by fun_prop : Continuous fun y : ℂ => -(π : ℂ) * cauchyT ω y - (c0 + y * c1 + y ^ 2 * c2)).continuousOn
  refine hcont.congr ?_
  intro y hy
  beta_reduce
  have hy2 : ‖y‖ ≤ 2 := mem_closedBall_zero_iff.1 hy
  have hF0 : volume ({y, 1, -1, -I} : Set ℂ) = 0 := (Set.toFinite _).measure_zero _
  have hae : ∀ᵐ ζ ∂(volume.restrict (S ∩ ball (0 : ℂ) 4)),
      W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) =
        W ζ * (1 / (ζ - y)) - (W ζ * ((ζ ^ 2 + I * ζ - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1))) +
          y * (W ζ * ((ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) +
          y ^ 2 * (W ζ * (1 / ((ζ + 1) * (ζ + I) * (ζ - 1))))) := by
    filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hF0)] with ζ hζ
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hζ
    obtain ⟨h1, h2, h3, h4⟩ := hζ
    have hs : ζ - y ≠ 0 := sub_ne_zero.2 h1
    have ha : ζ + 1 ≠ 0 := fun h => h3 (by linear_combination h)
    have hb : ζ + I ≠ 0 := fun h => h4 (by linear_combination h)
    have hc : ζ - 1 ≠ 0 := sub_ne_zero.2 h2
    field_simp
    ring
  have hic : IntegrableOn (fun ζ => W ζ * (1 / (ζ - y))) (S ∩ ball (0 : ℂ) 4) := by
    refine Integrable.mono' (((e124p_invnorm_int y 6).mono_set ?_).const_mul Wb)
      (hW1.mul (measurable_const.div (measurable_id.sub_const y)).aestronglyMeasurable) ?_
    · intro ζ hζ
      rw [mem_ball, dist_eq_norm]
      have h1 := hζ.2
      rw [mem_ball_zero_iff] at h1
      calc ‖ζ - y‖ ≤ ‖ζ‖ + ‖y‖ := norm_sub_le _ _
        _ < 6 := by linarith
    · filter_upwards [hWb1] with ζ hζ
      rw [norm_mul, norm_div, norm_one, one_div]
      exact mul_le_mul_of_nonneg_right hζ (inv_nonneg.2 (norm_nonneg _))
  have hi1' : IntegrableOn (fun ζ => W ζ * (((y + 1) * (y + I) * (y - 1)) /
      (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) (S ∩ ball (0 : ℂ) 4) :=
    (hic.sub ((hi0.add (hi1.const_mul y)).add (hi2.const_mul (y ^ 2)))).congr (hae.mono fun ζ h => h.symm)
  have hi2' : IntegrableOn (fun ζ => W ζ * (((y + 1) * (y + I) * (y - 1)) /
      (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) (S \ ball (0 : ℂ) 4) :=
    Integrable.mono' hbI (hFm y hy) (hFb y hy)
  have hiS : IntegrableOn (fun ζ => W ζ * (((y + 1) * (y + I) * (y - 1)) /
      (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) S := by
    have h := hi1'.union hi2'
    rwa [inter_union_diff] at h
  have h01 : IntegrableOn (fun ζ => W ζ * ((ζ ^ 2 + I * ζ - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1))) +
      y * (W ζ * ((ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1))))) (S ∩ ball (0 : ℂ) 4) := hi0.add (hi1.const_mul y)
  have h012 : IntegrableOn (fun ζ => W ζ * ((ζ ^ 2 + I * ζ - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1))) +
      y * (W ζ * ((ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) +
      y ^ 2 * (W ζ * (1 / ((ζ + 1) * (ζ + I) * (ζ - 1))))) (S ∩ ball (0 : ℂ) 4) := h01.add (hi2.const_mul (y ^ 2))
  rw [← integral_inter_add_sdiff hB hiS, integral_congr_ae hae, integral_sub hic h012,
    integral_add h01 (hi2.const_mul (y ^ 2)), integral_add hi0 (hi1.const_mul y), integral_const_mul,
    integral_const_mul, ← hc0, ← hc1, ← hc2, hT1]

/-- [(Λ) helper] Growth at `∞`: `|∫_S W(ζ) Dn(y)/(Dn(ζ)(ζ - y))| ≤ C |y|³` for `|y| ≥ 4`, `W` bounded on `S`. -/
theorem s3dl_growth {W : ℂ → ℂ} {S : Set ℂ} {Wb : ℝ} (hWb : ∀ᵐ ζ ∂(volume.restrict S), ‖W ζ‖ ≤ Wb) :
    ∃ C : ℝ, ∀ y : ℂ, 4 ≤ ‖y‖ → ‖∫ ζ in S, W ζ * (((y + 1) * (y + I) * (y - 1)) /
      (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))‖ ≤ C * ‖y‖ ^ 3 := by
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℝ, f = (ball (0 : ℂ) 1).indicator fun v => ‖v‖⁻¹ := ⟨_, rfl⟩
  have hfi : Integrable f := by
    rw [hf, integrable_indicator_iff measurableSet_ball]
    have h := e124p_invnorm_int 0 1
    simp only [sub_zero] at h
    exact h
  have hf0 : ∀ v, 0 ≤ f v := fun v => by
    rw [hf]
    exact indicator_nonneg (fun v _ => inv_nonneg.2 (norm_nonneg v)) v
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (∫ ζ, ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹) + ∫ v, f v := ⟨_, rfl⟩
  refine ⟨max Wb 0 * 8 * K, fun y hy => ?_⟩
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hDy : ‖(y + 1) * (y + I) * (y - 1)‖ ≤ 8 * ‖y‖ ^ 3 := by
    have h1 : ‖y + 1‖ ≤ 2 * ‖y‖ := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
    have h2 : ‖y + I‖ ≤ 2 * ‖y‖ := (norm_add_le _ _).trans (by rw [Complex.norm_I]; linarith)
    have h3 : ‖y - 1‖ ≤ 2 * ‖y‖ := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    rw [norm_mul, norm_mul]
    calc ‖y + 1‖ * ‖y + I‖ * ‖y - 1‖ ≤ (2 * ‖y‖) * (2 * ‖y‖) * (2 * ‖y‖) := by gcongr
      _ = 8 * ‖y‖ ^ 3 := by ring
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℝ, G = fun ζ => max Wb 0 * ‖(y + 1) * (y + I) * (y - 1)‖ *
      (‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ + f (ζ - y)) := ⟨_, rfl⟩
  have hGi : Integrable G := by
    rw [hG]
    exact (d2e_dn_int.add (hfi.comp_sub_right y)).const_mul _
  have hG0 : ∀ ζ, 0 ≤ G ζ := fun ζ => by
    rw [hG]
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (norm_nonneg _))
      (add_nonneg (inv_nonneg.2 (norm_nonneg _)) (hf0 _))
  have hpt : ∀ᵐ ζ ∂(volume.restrict S), ‖W ζ * (((y + 1) * (y + I) * (y - 1)) /
      (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))‖ ≤ G ζ := by
    filter_upwards [hWb] with ζ hζ
    rw [hG, norm_mul, norm_div, norm_mul ((ζ + 1) * (ζ + I) * (ζ - 1)) (ζ - y), div_eq_mul_inv, mul_inv, ← mul_assoc]
    refine mul_le_mul (mul_le_mul_of_nonneg_right (hζ.trans (le_max_left _ _)) (norm_nonneg _)) ?_
      (by positivity) (mul_nonneg (le_max_right _ _) (norm_nonneg _))
    by_cases hzy : 1 ≤ ‖ζ - y‖
    · have h1 : ‖ζ - y‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hzy
      calc ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - y‖⁻¹ ≤ ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (norm_nonneg _))
        _ ≤ _ := by rw [mul_one]; exact le_add_of_nonneg_right (hf0 _)
    · rw [not_le] at hzy
      have hz3 : 1 + 2 ≤ ‖ζ‖ := by
        have := norm_sub_norm_le y ζ
        rw [norm_sub_rev] at this
        linarith
      have hD8 := d2e_dn_lower (by norm_num : (0 : ℝ) ≤ 2) hz3
      have hDn : ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have hfv : f (ζ - y) = ‖ζ - y‖⁻¹ := by
        rw [hf, indicator_of_mem (mem_ball_zero_iff.2 hzy)]
      calc ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - y‖⁻¹ ≤ 1 * ‖ζ - y‖⁻¹ :=
            mul_le_mul_of_nonneg_right hDn (inv_nonneg.2 (norm_nonneg _))
        _ ≤ _ := by rw [one_mul, hfv]; exact le_add_of_nonneg_left (inv_nonneg.2 (norm_nonneg _))
  have hint : ∫ ζ, G ζ = max Wb 0 * ‖(y + 1) * (y + I) * (y - 1)‖ * K := by
    rw [hG, integral_const_mul, integral_add d2e_dn_int (hfi.comp_sub_right y),
      integral_sub_right_eq_self (fun v => f v) y, hK]
  calc _ ≤ ∫ ζ in S, G ζ := norm_integral_le_of_norm_le hGi.integrableOn hpt
    _ ≤ ∫ ζ, G ζ := setIntegral_le_integral hGi (Eventually.of_forall hG0)
    _ = max Wb 0 * ‖(y + 1) * (y + I) * (y - 1)‖ * K := hint
    _ ≤ max Wb 0 * (8 * ‖y‖ ^ 3) * K := by
        have hK0 : 0 ≤ K := by
          rw [hK]
          exact add_nonneg (integral_nonneg fun ζ => inv_nonneg.2 (norm_nonneg _)) (integral_nonneg hf0)
        gcongr
    _ = max Wb 0 * 8 * K * ‖y‖ ^ 3 := by ring

/-- **(Λ)** The Lie terms integrate to `0` (Stokes on `𝔻*`, tangency of `γ̂_t` on `𝕊¹`, decay at `∞`). -/
theorem s3d_D2_lambda {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    (∫ z in unitDiscExterior, (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * dz (fun y : ℂ => preSchwarzian (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z +
      preSchwarzian (gsans (beltramiMul a κ)) z * conj (dz (fun y : ℂ => preSchwarzian (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z))) = 0 := by
  have hd := delta0_bounds
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.2 (has.trans hd.2)
  have hμ : beltramiMul a (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨r, hr, ρ, hρ, R0, hR0, F, G, H, -, -, -, -, -, -, -, ht⟩ := s3g_D_ext hκ hκD ha has haL haD hm hmD
  obtain ⟨-, ⟨hGd, hGi, hGd', hGg⟩, -⟩ := ht 0 (mem_ball_self hr)
  simp only [zero_smul, add_zero] at hGg
  have hRm : AEStronglyMeasurable (RnmFun (toLinf m) a) (volume.restrict unitDiscExterior) :=
    (bc_Rnm_memLp haB (toLinf m)).aestronglyMeasurable
  have hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior),
      ‖RnmFun (toLinf m) a u‖ ≤ (1 / (1 - ‖a‖ ^ 2)) * ‖toLinf m‖ :=
    bc_invFun_pullback_ae haB (bc_Rnm_integrand_bound haB (toLinf m))
  obtain ⟨hSm, hSb⟩ := d2e_S_ae hRm hRb
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have hO : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hEO : unitDiscExterior ⊆ {z : ℂ | ρ < ‖z‖} := fun z hz => show ρ < ‖z‖ from lt_trans hρ hz
  obtain ⟨-, -, -, -, hg'ne⟩ := d2e_basic hρ hGd hGi hGd' hGg
  -- the two vector fields `γ̇`, `γ̇₂`
  obtain ⟨γ1, hγ1⟩ : ∃ γ : ℂ → ℂ, ∀ y, γ y = -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
      (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) := ⟨_, fun y => rfl⟩
  obtain ⟨γ2, hγ2⟩ : ∃ γ : ℂ → ℂ, ∀ y, γ y = -(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) *
      ζ ^ 2 / conj ζ ^ 2 * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) :=
    ⟨_, fun y => rfl⟩
  simp only [← hγ1, ← hγ2]
  have hC1 : ContDiffOn ℝ 1 γ1 unitDiscExterior := by
    have h := s3d_D2_gd1_C1 hκ hκD ha has haL haD hm hmD
    simp only [← hγ1] at h
    exact h
  have hγ2d : DifferentiableOn ℂ γ2 unitDiscExterior := by
    have h := d2e_eta2 0 hρ hGd hGi hGd' hGg hRm hRb
    simp only [← hγ2] at h
    refine h.neg.congr fun y hy => ?_
    have h0 := hg'ne y hy
    show γ2 y = -((0 * gsans (beltramiMul a κ) y ^ 2 - deriv (gsans (beltramiMul a κ)) y * γ2 y) /
      deriv (gsans (beltramiMul a κ)) y)
    rw [zero_mul, zero_sub, neg_div, neg_neg, mul_div_cancel_left₀ _ h0]
  -- the holomorphic extension of `𝒜(g)` across `𝕊¹`
  obtain ⟨A, hA⟩ : ∃ A : ℂ → ℂ, A = fun z => deriv (deriv (G 0)) z / deriv (G 0) z := ⟨_, rfl⟩
  have hAd : DifferentiableOn ℂ A {z : ℂ | ρ < ‖z‖} := by
    rw [hA]
    exact ((hGd.deriv hO).deriv hO).div (hGd.deriv hO) fun z hz => hGd' z hz
  have hPA : ∀ y ∈ unitDiscExterior, preSchwarzian (gsans (beltramiMul a κ)) y = A y := by
    intro y hy
    have heq : gsans (beltramiMul a κ) =ᶠ[𝓝 y] G 0 :=
      Filter.mem_of_superset (hE.mem_nhds hy) fun w hw => (hGg hw).symm
    have h1 := heq.deriv
    show deriv (deriv (gsans (beltramiMul a κ))) y / deriv (gsans (beltramiMul a κ)) y = A y
    rw [hA, h1.deriv_eq, h1.eq_of_nhds]
  -- the two potentials and their regularity
  obtain ⟨Φ1, hΦ1⟩ : ∃ Φ : ℂ → ℂ, Φ = fun y => conj (A y) * (A y * γ1 y) := ⟨_, rfl⟩
  obtain ⟨Φ2, hΦ2⟩ : ∃ Φ : ℂ → ℂ, Φ = fun y => conj (A y) * (A y * γ2 y) := ⟨_, rfl⟩
  have hAR : ContDiffOn ℝ 1 A unitDiscExterior := ((hAd.mono hEO).contDiffOn hE).restrict_scalars ℝ
  have hAcR : ContDiffOn ℝ 1 (fun y => conj (A y)) unitDiscExterior :=
    (conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hAR
  have hΦ1C : ContDiffOn ℝ 1 Φ1 unitDiscExterior := by rw [hΦ1]; exact hAcR.mul (hAR.mul hC1)
  have hΦ2C : ContDiffOn ℝ 1 Φ2 unitDiscExterior := by
    rw [hΦ2]; exact hAcR.mul (hAR.mul ((hγ2d.contDiffOn hE).restrict_scalars ℝ))
  -- the integrand is `∂_z Φ₁ + conj ∂_z Φ₂`
  have hdzc : ∀ (f f' : ℂ → ℂ) (z : ℂ), f =ᶠ[𝓝 z] f' → dz f z = dz f' z := fun f f' z h => by
    show (fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2 = (fderiv ℝ f' z 1 - I * fderiv ℝ f' z I) / 2
    rw [h.fderiv_eq]
  have hItg : ∀ z ∈ unitDiscExterior,
      conj (preSchwarzian (gsans (beltramiMul a κ)) z) *
          dz (fun y => preSchwarzian (gsans (beltramiMul a κ)) y * γ1 y) z +
        preSchwarzian (gsans (beltramiMul a κ)) z *
          conj (dz (fun y => preSchwarzian (gsans (beltramiMul a κ)) y * γ2 y) z) =
      dz Φ1 z + conj (dz Φ2 z) := by
    intro z hz
    have hn : unitDiscExterior ∈ 𝓝 z := hE.mem_nhds hz
    have hAz : DifferentiableAt ℂ A z := (hAd z (hEO hz)).differentiableAt (hO.mem_nhds (hEO hz))
    have h1z : DifferentiableAt ℝ γ1 z := ((hC1.differentiableOn one_ne_zero) z hz).differentiableAt hn
    have h2z : DifferentiableAt ℝ γ2 z := ((hγ2d z hz).differentiableAt hn).restrictScalars ℝ
    have e1 : dz (fun y => preSchwarzian (gsans (beltramiMul a κ)) y * γ1 y) z = dz (fun y => A y * γ1 y) z :=
      hdzc _ _ z (Filter.mem_of_superset hn fun w hw => by
        show preSchwarzian (gsans (beltramiMul a κ)) w * γ1 w = A w * γ1 w
        rw [hPA w hw])
    have e2 : dz (fun y => preSchwarzian (gsans (beltramiMul a κ)) y * γ2 y) z = dz (fun y => A y * γ2 y) z :=
      hdzc _ _ z (Filter.mem_of_superset hn fun w hw => by
        show preSchwarzian (gsans (beltramiMul a κ)) w * γ2 w = A w * γ2 w
        rw [hPA w hw])
    rw [e1, e2, hPA z hz, hΦ1, hΦ2, s3dl_wirt hAz h1z, s3dl_wirt hAz h2z, map_mul, conj_conj]
  rw [setIntegral_congr_fun hEm hItg]
  by_cases hI : IntegrableOn (fun z => dz Φ1 z + conj (dz Φ2 z)) unitDiscExterior
  swap
  · exact integral_undef hI
  -- continuity of `∂_z Φ`
  have hdzC : ∀ Φ : ℂ → ℂ, ContDiffOn ℝ 1 Φ unitDiscExterior → ContinuousOn (fun z => dz Φ z) unitDiscExterior := by
    intro Φ hΦ
    have hf := hΦ.continuousOn_fderiv_of_isOpen hE le_rfl
    show ContinuousOn (fun z => (fderiv ℝ Φ z 1 - I * fderiv ℝ Φ z I) / 2) unitDiscExterior
    exact ((hf.clm_apply continuousOn_const).sub (continuousOn_const.mul (hf.clm_apply continuousOn_const))).div_const 2
  -- the exhaustion by annuli
  obtain ⟨rs, hrs⟩ : ∃ rs : ℕ → ℝ, rs = fun n : ℕ => 1 + 1 / ((n : ℝ) + 2) := ⟨_, rfl⟩
  obtain ⟨Rs, hRs⟩ : ∃ Rs : ℕ → ℝ, Rs = fun n : ℕ => (n : ℝ) + 2 := ⟨_, rfl⟩
  have hrs1 : ∀ n, 1 < rs n := fun n => by
    rw [hrs]
    have h : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    show 1 < 1 + 1 / ((n : ℝ) + 2)
    linarith
  have hrs2 : ∀ n, rs n ≤ 3 / 2 := fun n => by
    rw [hrs]
    have h : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
    show 1 + 1 / ((n : ℝ) + 2) ≤ 3 / 2
    linarith
  have hRs2 : ∀ n, 2 ≤ Rs n := fun n => by rw [hRs]; show (2 : ℝ) ≤ n + 2; linarith [n.cast_nonneg (α := ℝ)]
  have hrR : ∀ n, rs n < Rs n := fun n => by linarith [hrs2 n, hRs2 n]
  have hAm : ∀ n, MeasurableSet {z : ℂ | rs n < ‖z‖ ∧ ‖z‖ < Rs n} := fun n =>
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
  have hmono : Monotone fun n => {z : ℂ | rs n < ‖z‖ ∧ ‖z‖ < Rs n} := by
    intro n k hnk z hz
    have h1 : rs k ≤ rs n := by
      rw [hrs]
      show 1 + 1 / ((k : ℝ) + 2) ≤ 1 + 1 / ((n : ℝ) + 2)
      have : (n : ℝ) ≤ k := Nat.cast_le.2 hnk
      have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 2) (by linarith : (n : ℝ) + 2 ≤ k + 2)
      linarith
    have h2 : Rs n ≤ Rs k := by
      rw [hRs]
      show (n : ℝ) + 2 ≤ k + 2
      have : (n : ℝ) ≤ k := Nat.cast_le.2 hnk
      linarith
    exact ⟨h1.trans_lt hz.1, hz.2.trans_le h2⟩
  have hU : (⋃ n, {z : ℂ | rs n < ‖z‖ ∧ ‖z‖ < Rs n}) = unitDiscExterior := by
    ext z
    rw [mem_iUnion]
    constructor
    · rintro ⟨n, hz⟩
      exact (hrs1 n).trans hz.1
    · intro hz
      have hz1 : 1 < ‖z‖ := hz
      obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / (‖z‖ - 1)) ‖z‖)
      have hN1 : 1 / (‖z‖ - 1) < N := lt_of_le_of_lt (le_max_left _ _) hN
      have hN2 : ‖z‖ < N := lt_of_le_of_lt (le_max_right _ _) hN
      refine ⟨N, ?_, ?_⟩
      · rw [hrs]
        show 1 + 1 / ((N : ℝ) + 2) < ‖z‖
        have h0 : 0 < ‖z‖ - 1 := by linarith
        have h1 : 1 / ((N : ℝ) + 2) < ‖z‖ - 1 := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ h0] at hN1
          nlinarith
        linarith
      · rw [hRs]
        show ‖z‖ < (N : ℝ) + 2
        linarith
  -- the circle parametrization
  have hev1 : ∀ θ : ℝ, ‖(Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I‖ = 1 := fun θ => by
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    exact Complex.norm_cos_add_sin_mul_I θ
  have hcj : ∀ θ : ℝ, conj ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I :=
    fun θ => by rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, conj_I]; ring
  have hev2 : ∀ θ : ℝ, ‖(Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I‖ = 1 := fun θ => by
    rw [← Complex.norm_conj, hcj]
    exact hev1 θ
  have hee : ∀ θ : ℝ, ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) = 1 := by
    intro θ
    have h : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq θ
    linear_combination h - (Real.sin θ : ℂ) ^ 2 * I_sq
  have hpn : ∀ (x θ : ℝ), 0 ≤ x → ‖(x : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)‖ = x := fun x θ hx => by
    rw [norm_mul, hev1, mul_one, Complex.norm_real, Real.norm_of_nonneg hx]
  -- the boundary integrals and Stokes on each annulus
  obtain ⟨J1, hJ1⟩ : ∃ J : ℝ → ℂ, ∀ x : ℝ, J x = ∫ θ in (-π)..π, (x : ℂ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) *
      Φ1 (x * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) := ⟨_, fun x => rfl⟩
  obtain ⟨J2, hJ2⟩ : ∃ J : ℝ → ℂ, ∀ x : ℝ, J x = ∫ θ in (-π)..π, (x : ℂ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) *
      Φ2 (x * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) := ⟨_, fun x => rfl⟩
  have hstokes : ∀ n, ∫ z in {z : ℂ | rs n < ‖z‖ ∧ ‖z‖ < Rs n}, (dz Φ1 z + conj (dz Φ2 z)) =
      (1 / 2 : ℂ) * (J1 (Rs n) - J1 (rs n)) + conj ((1 / 2 : ℂ) * (J2 (Rs n) - J2 (rs n))) := by
    intro n
    have hK : ∀ z : ℂ, rs n ≤ ‖z‖ → ‖z‖ ≤ Rs n → z ∈ unitDiscExterior := fun z h1 _ =>
      show 1 < ‖z‖ from lt_of_lt_of_le (hrs1 n) h1
    have hKc : IsCompact {z : ℂ | rs n ≤ ‖z‖ ∧ ‖z‖ ≤ Rs n} :=
      Metric.isCompact_of_isClosed_isBounded
        ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
        (isBounded_closedBall.subset fun z hz => mem_closedBall_zero_iff.2 hz.2)
    have hKE : {z : ℂ | rs n ≤ ‖z‖ ∧ ‖z‖ ≤ Rs n} ⊆ unitDiscExterior := fun z hz => hK z hz.1 hz.2
    have hAK : {z : ℂ | rs n < ‖z‖ ∧ ‖z‖ < Rs n} ⊆ {z : ℂ | rs n ≤ ‖z‖ ∧ ‖z‖ ≤ Rs n} :=
      fun z hz => ⟨hz.1.le, hz.2.le⟩
    have i1 : IntegrableOn (fun z => dz Φ1 z) {z : ℂ | rs n < ‖z‖ ∧ ‖z‖ < Rs n} :=
      (((hdzC Φ1 hΦ1C).mono hKE).integrableOn_compact hKc).mono_set hAK
    have i2 : IntegrableOn (fun z => conj (dz Φ2 z)) {z : ℂ | rs n < ‖z‖ ∧ ‖z‖ < Rs n} :=
      ((Complex.continuous_conj.comp_continuousOn ((hdzC Φ2 hΦ2C).mono hKE)).integrableOn_compact hKc).mono_set hAK
    rw [integral_add i1 i2, integral_conj, s3dl_stokes hE (by linarith [hrs1 n]) (hrR n) hK hΦ1C,
      s3dl_stokes hE (by linarith [hrs1 n]) (hrR n) hK hΦ2C, ← hJ1, ← hJ1, ← hJ2, ← hJ2]
  -- (i) the outer boundary term vanishes at `∞`
  obtain ⟨CA, RA, hCA⟩ := AppA.appa2_preSchwarzian_cubic hpair.2.2.2.2.1
  obtain ⟨C1, hC1g⟩ := s3dl_growth (S := unitDiscExterior) hRb
  obtain ⟨C2, hC2g⟩ := s3dl_growth (S := unitDisc) hSb
  have hdec : ∀ (Φ γ : ℂ → ℂ) (C : ℝ), Φ = (fun y => conj (A y) * (A y * γ y)) →
      (∀ y : ℂ, 4 ≤ ‖y‖ → ‖γ y‖ ≤ ‖(-(1 / π : ℂ))‖ * (C * ‖y‖ ^ 3)) →
      Tendsto (fun n => ∫ θ in (-π)..π, (Rs n : ℂ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) *
        Φ (Rs n * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))) atTop (𝓝 0) := by
    intro Φ γ C hΦ hγ
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = CA ^ 2 * (‖(-(1 / π : ℂ))‖ * C) := ⟨_, rfl⟩
    have hRt : Tendsto Rs atTop atTop := by
      rw [hRs]
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hlim : Tendsto (fun n => B / Rs n ^ 2 * |π - -π|) atTop (𝓝 0) := by
      have hR2 : Tendsto (fun n => Rs n ^ 2) atTop atTop := (tendsto_pow_atTop two_ne_zero).comp hRt
      have h : Tendsto (fun n => B / Rs n ^ 2) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hR2
      simpa using h.mul_const |π - -π|
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hRt.eventually_ge_atTop (max (RA + 1) 4)] with n hn
    have hR4 : 4 ≤ Rs n := le_trans (le_max_right _ _) hn
    have hRA : RA < Rs n := lt_of_lt_of_le (by linarith) (le_trans (le_max_left _ _) hn)
    have hR0 : 0 < Rs n := by linarith
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (Rs n : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) := ⟨_, rfl⟩
    have hwn : ‖w‖ = Rs n := by rw [hw]; exact hpn _ _ hR0.le
    rw [← hw, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR0.le, hev2, mul_one, hΦ]
    have hwE : w ∈ unitDiscExterior := show 1 < ‖w‖ by rw [hwn]; linarith
    have hAw : ‖A w‖ ≤ CA / Rs n ^ 3 := by
      rw [← hPA w hwE, ← hwn]
      exact hCA w (by rw [hwn]; exact hRA)
    have hγw : ‖γ w‖ ≤ ‖(-(1 / π : ℂ))‖ * (C * Rs n ^ 3) := by
      rw [← hwn]
      exact hγ w (by rw [hwn]; exact hR4)
    show Rs n * ‖conj (A w) * (A w * γ w)‖ ≤ B / Rs n ^ 2
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hc0 : 0 ≤ CA / Rs n ^ 3 := (norm_nonneg _).trans hAw
    have h1 : ‖A w‖ * ‖γ w‖ ≤ (CA / Rs n ^ 3) * (‖(-(1 / π : ℂ))‖ * (C * Rs n ^ 3)) :=
      mul_le_mul hAw hγw (norm_nonneg _) hc0
    have h2 : ‖A w‖ * (‖A w‖ * ‖γ w‖) ≤ (CA / Rs n ^ 3) * ((CA / Rs n ^ 3) * (‖(-(1 / π : ℂ))‖ * (C * Rs n ^ 3))) :=
      mul_le_mul hAw h1 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc0
    calc Rs n * (‖A w‖ * (‖A w‖ * ‖γ w‖))
        ≤ Rs n * ((CA / Rs n ^ 3) * ((CA / Rs n ^ 3) * (‖(-(1 / π : ℂ))‖ * (C * Rs n ^ 3)))) :=
          mul_le_mul_of_nonneg_left h2 hR0.le
      _ = B / Rs n ^ 2 := by rw [hB]; field_simp
  have hgr : ∀ (W : ℂ → ℂ) (S : Set ℂ) (C : ℝ) (γ : ℂ → ℂ),
      (∀ y, γ y = -(1 / π : ℂ) * ∫ ζ in S, W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) →
      (∀ y : ℂ, 4 ≤ ‖y‖ → ‖∫ ζ in S, W ζ * (((y + 1) * (y + I) * (y - 1)) /
        (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))‖ ≤ C * ‖y‖ ^ 3) →
      ∀ y : ℂ, 4 ≤ ‖y‖ → ‖γ y‖ ≤ ‖(-(1 / π : ℂ))‖ * (C * ‖y‖ ^ 3) := by
    intro W S C γ hγ hC y hy
    rw [hγ, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC y hy) (norm_nonneg _)
  have hJ1R : Tendsto (fun n => J1 (Rs n)) atTop (𝓝 0) := by
    simp only [hJ1]
    exact hdec Φ1 γ1 C1 hΦ1 (hgr _ _ C1 γ1 hγ1 hC1g)
  have hJ2R : Tendsto (fun n => J2 (Rs n)) atTop (𝓝 0) := by
    simp only [hJ2]
    exact hdec Φ2 γ2 C2 hΦ2 (hgr _ _ C2 γ2 hγ2 hC2g)
  -- (ii) the inner boundary term converges to its value on `𝕊¹`
  have hγ1c : ContinuousOn γ1 (closedBall 0 2) := by
    have h := (s3dl_cont hEm hRm hRb).const_smul (-(1 / π : ℂ))
    refine h.congr fun y _ => ?_
    rw [hγ1]
    rfl
  have hγ2c : ContinuousOn γ2 (closedBall 0 2) := by
    have h := (s3dl_cont measurableSet_ball hSm hSb).const_smul (-(1 / π : ℂ))
    refine h.congr fun y _ => ?_
    rw [hγ2]
    rfl
  have hK12O : {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2} ⊆ {z : ℂ | ρ < ‖z‖} := fun z hz => show ρ < ‖z‖ by linarith [hz.1]
  have hK12B : {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2} ⊆ closedBall (0 : ℂ) 2 := fun z hz => mem_closedBall_zero_iff.2 hz.2
  have hAc : ContinuousOn A {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2} := hAd.continuousOn.mono hK12O
  have hcont : ∀ (Φ γ : ℂ → ℂ), Φ = (fun y => conj (A y) * (A y * γ y)) → ContinuousOn γ (closedBall 0 2) →
      Tendsto (fun n => ∫ θ in (-π)..π, (rs n : ℂ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) *
        Φ (rs n * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))) atTop
        (𝓝 (∫ θ in (-π)..π, ((1 : ℝ) : ℂ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) *
          Φ (((1 : ℝ) : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)))) := by
    intro Φ γ hΦ hγc
    have hΦc : ContinuousOn Φ {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2} := by
      rw [hΦ]
      exact (Complex.continuous_conj.comp_continuousOn hAc).mul (hAc.mul (hγc.mono hK12B))
    obtain ⟨P, hP⟩ : ∃ P : ℝ → ℝ, P = fun x => (Set.projIcc (1 : ℝ) 2 (by norm_num) x : ℝ) := ⟨_, rfl⟩
    have hPc : Continuous P := by rw [hP]; exact continuous_subtype_val.comp continuous_projIcc
    have hPm : ∀ x, P x ∈ Icc (1 : ℝ) 2 := fun x => by rw [hP]; exact (Set.projIcc (1 : ℝ) 2 _ x).2
    have hPe : ∀ x ∈ Icc (1 : ℝ) 2, P x = x := fun x hx => by
      rw [hP]
      exact congrArg Subtype.val (Set.projIcc_of_mem _ hx)
    have hq : Continuous fun p : ℝ × ℝ => ((P p.1 : ℝ) : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I) := by
      fun_prop
    have hqK : ∀ p : ℝ × ℝ, ((P p.1 : ℝ) : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I) ∈
        {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2} := fun p => by
      show 1 ≤ ‖_‖ ∧ ‖_‖ ≤ 2
      rw [hpn _ _ (by linarith [(hPm p.1).1])]
      exact hPm p.1
    have hJc : Continuous fun x : ℝ => ∫ θ in (-π)..π, ((P x : ℝ) : ℂ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) *
        Φ ((P x : ℝ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) := by
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ (-π) π
      exact ((Complex.continuous_ofReal.comp (hPc.comp continuous_fst)).mul (by fun_prop)).mul
        (hΦc.comp_continuous hq hqK)
    have hrt : Tendsto rs atTop (𝓝 1) := by
      rw [hrs]
      have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa using h.const_add 1
    have h := (hJc.tendsto 1).comp hrt
    rw [hPe 1 ⟨le_rfl, by norm_num⟩] at h
    refine h.congr fun n => ?_
    show ∫ θ in (-π)..π, ((P (rs n) : ℝ) : ℂ) * _ * Φ ((P (rs n) : ℝ) * _) = _
    rw [hPe (rs n) ⟨(hrs1 n).le, by linarith [hrs2 n]⟩]
  have hJ1r : Tendsto (fun n => J1 (rs n)) atTop (𝓝 (J1 1)) := by
    simp only [hJ1]
    exact hcont Φ1 γ1 hΦ1 hγ1c
  have hJ2r : Tendsto (fun n => J2 (rs n)) atTop (𝓝 (J2 1)) := by
    simp only [hJ2]
    exact hcont Φ2 γ2 hΦ2 hγ2c
  -- (iii) tangency: the boundary terms on `𝕊¹` cancel
  have htan : J1 1 = -conj (J2 1) := by
    rw [hJ1, hJ2, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ← integral_conj, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := ⟨_, rfl⟩
    have hw1 : ‖w‖ = 1 := by rw [hw]; exact hev1 θ
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, norm_zero] at hw1
      exact zero_ne_one hw1
    have ht2 := s3dl_tangent (RnmFun (toLinf m) a) hw1
    rw [← hγ2, ← hγ1] at ht2
    have he : ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) = w⁻¹ := by
      rw [hw]
      exact eq_inv_of_mul_eq_one_left (hee θ)
    show ((1 : ℝ) : ℂ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) *
        Φ1 (((1 : ℝ) : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) =
      -conj (((1 : ℝ) : ℂ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) *
        Φ2 (((1 : ℝ) : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)))
    have hcw : conj w = w⁻¹ := by
      have h := Complex.mul_conj' w
      rw [hw1] at h
      push_cast at h
      rw [one_pow] at h
      exact eq_inv_of_mul_eq_one_right h
    simp only [Complex.ofReal_one, one_mul]
    rw [he, ← hw, hΦ1, hΦ2]
    simp only [map_mul, map_inv₀, conj_conj, ht2, hcw, inv_inv]
    field_simp
  -- conclusion
  have hlim : Tendsto (fun n => ∫ z in {z : ℂ | rs n < ‖z‖ ∧ ‖z‖ < Rs n}, (dz Φ1 z + conj (dz Φ2 z))) atTop
      (𝓝 ((1 / 2 : ℂ) * (0 - J1 1) + conj ((1 / 2 : ℂ) * (0 - J2 1)))) := by
    simp only [hstokes]
    exact (tendsto_const_nhds.mul (hJ1R.sub hJ1r)).add
      ((Complex.continuous_conj.tendsto _).comp (tendsto_const_nhds.mul (hJ2R.sub hJ2r)))
  have hval : (1 / 2 : ℂ) * (0 - J1 1) + conj ((1 / 2 : ℂ) * (0 - J2 1)) = 0 := by
    rw [htan, map_mul, map_sub, map_zero, map_div₀, map_one, map_ofNat]
    ring
  have hlim2 := tendsto_setIntegral_of_monotone hAm hmono (by rw [hU]; exact hI)
  rw [hU] at hlim2
  rw [hval] at hlim
  exact tendsto_nhds_unique hlim2 hlim

/-- [Λ-INT helper] Integration by parts against a test function: `∫ φ ∂F = -∫ ∂φ F` for `F` C¹ on an open set
containing `tsupport φ`. -/
theorem d2l_ibp {F φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∫ y, φ y * dz F y = -∫ y, dz φ y * F y := by
  have hFd : ∀ x ∈ U, DifferentiableAt ℝ F x := fun x hx =>
    (hF.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  have hFc := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  have hφd : ∀ x, DifferentiableAt ℝ φ x := fun x => hφ.differentiable one_ne_zero x
  have hφf := hφ.continuous_fderiv one_ne_zero
  have hc1 : ∀ G : ℂ → ℂ, ContinuousOn G U → Integrable (fun x => φ x * G x) := fun G hG => by
    refine Continuous.integrable_of_hasCompactSupport (continuous_of_tsupport fun x hx => ?_) hφc.mul_right
    have hxU : x ∈ U := hφU (tsupport_mul_subset_left hx)
    exact hφ.continuous.continuousAt.mul ((hG x hxU).continuousAt (hU.mem_nhds hxU))
  have hc2 : ∀ v : ℂ, Integrable (fun x => fderiv ℝ φ x v * F x) := fun v => by
    refine Continuous.integrable_of_hasCompactSupport (continuous_of_tsupport fun x hx => ?_)
      (hφc.fderiv_apply (𝕜 := ℝ) v).mul_right
    have hxU : x ∈ U := hφU (tsupport_fderiv_apply_subset ℝ v (tsupport_mul_subset_left hx))
    exact (hφf.clm_apply continuous_const).continuousAt.mul (hFd x hxU).continuousAt
  have hv : ∀ v : ℂ, ∫ x, φ x * fderiv ℝ F x v = -∫ x, fderiv ℝ φ x v * F x := fun v =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hc2 v) (hc1 _ (hFc.clm_apply continuousOn_const))
      (hc1 F hF.continuousOn) (fun x _ => hφd x) (fun x hx => hFd x (hφU hx))
  show ∫ y, φ y * ((fderiv ℝ F y 1 - I * fderiv ℝ F y I) / 2) =
    -∫ y, (fderiv ℝ φ y 1 - I * fderiv ℝ φ y I) / 2 * F y
  have e1 : (fun y => φ y * ((fderiv ℝ F y 1 - I * fderiv ℝ F y I) / 2)) =
      fun y => (1 / 2 : ℂ) * (φ y * fderiv ℝ F y 1) - (I / 2) * (φ y * fderiv ℝ F y I) := by
    funext y; ring
  have e2 : (fun y => (fderiv ℝ φ y 1 - I * fderiv ℝ φ y I) / 2 * F y) =
      fun y => (1 / 2 : ℂ) * (fderiv ℝ φ y 1 * F y) - (I / 2) * (fderiv ℝ φ y I * F y) := by
    funext y; ring
  rw [e1, e2, integral_sub ((hc1 _ (hFc.clm_apply continuousOn_const)).const_mul _)
      ((hc1 _ (hFc.clm_apply continuousOn_const)).const_mul _),
    integral_sub ((hc2 1).const_mul _) ((hc2 I).const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, hv 1, hv I]
  ring

/-- [Λ-INT helper] The inner integral: `∫ ∂φ(y) N(ζ, y) dy = π Hφ(ζ) + (∫ φ(y)(ζ + 2y + i) dy)/Dn(ζ)`. -/
theorem d2l_inner {φ : ℂ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ) {ζ : ℂ}
    (hD : ((ζ + 1) * (ζ + I) * (ζ - 1)) ≠ 0) :
    ∫ y, dz φ y * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) = π * hilbertHSmooth φ ζ + (ζ * (∫ y, φ y) + ∫ y, φ y * (2 * y + I)) / ((ζ + 1) * (ζ + I) * (ζ - 1)) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hdc : Continuous (dz φ) := by
    have hf := hφ1.continuous_fderiv one_ne_zero
    exact ((hf.clm_apply continuous_const).sub (continuous_const.mul (hf.clm_apply continuous_const))).div_const 2
  have hdcs : HasCompactSupport (dz φ) := by
    refine HasCompactSupport.intro hφc.isCompact fun y hy => ?_
    show (fderiv ℝ φ y 1 - I * fderiv ℝ φ y I) / 2 = 0
    rw [fderiv_of_notMem_tsupport ℝ hy]
    simp
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hQ : ∀ y, y ≠ ζ → (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) = -(1 / (y - ζ)) - (ζ ^ 2 + ζ * y + y ^ 2 + I * (ζ + y) - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1)) := by
    intro y hy
    have h1 : y - ζ ≠ 0 := sub_ne_zero.2 hy
    have h2 : ζ - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
    generalize hDd : ((ζ + 1) * (ζ + I) * (ζ - 1)) = D at hD ⊢
    field_simp
    rw [← hDd]
    ring
  have hae : (fun y => dz φ y * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) =ᵐ[volume]
      fun y => -(dz φ y / (y - ζ)) - (1 / ((ζ + 1) * (ζ + I) * (ζ - 1))) * (dz φ y * (ζ ^ 2 + ζ * y + y ^ 2 + I * (ζ + y) - 1)) := by
    filter_upwards [(countable_singleton ζ).ae_notMem volume] with y hy
    rw [hQ y (fun h => hy (h ▸ rfl))]
    ring
  have i1 := integrable_div_sub_of_hasCompactSupport hdc hdcs ζ
  have hQd : ContDiff ℝ 1 (fun y : ℂ => (ζ ^ 2 + ζ * y + y ^ 2 + I * (ζ + y) - 1)) := by fun_prop
  have i2 : Integrable (fun y => dz φ y * (ζ ^ 2 + ζ * y + y ^ 2 + I * (ζ + y) - 1)) :=
    (hdc.mul hQd.continuous).integrable_of_hasCompactSupport hdcs.mul_right
  have hdzQ : ∀ y, dz (fun y : ℂ => (ζ ^ 2 + ζ * y + y ^ 2 + I * (ζ + y) - 1)) y = ζ + 2 * y + I := fun y => by
    have h := ((((hasDerivAt_const y (ζ ^ 2)).add ((hasDerivAt_id' y).const_mul ζ)).add
      ((hasDerivAt_id' y).pow 2)).add (((hasDerivAt_id' y).const_add ζ).const_mul I)).sub_const 1
    have h' : HasDerivAt (fun y : ℂ => (ζ ^ 2 + ζ * y + y ^ 2 + I * (ζ + y) - 1)) (ζ + 2 * y + I) y := by
      convert h using 1
      simp
    rw [dz_eq_deriv h'.differentiableAt, h'.deriv]
  have hibp := d2l_ibp isOpen_univ hQd.contDiffOn hφ1 hφc (subset_univ _)
  simp only [hdzQ] at hibp
  have hcT : ∫ y, dz φ y / (y - ζ) = -(π : ℂ) * hilbertHSmooth φ ζ := by
    rw [congrFun (i1_hilbertH_eq_cauchyT_dz hφ hφc).1 ζ]
    show _ = -(π : ℂ) * (-(1 / π : ℂ) * ∫ y, dz φ y / (y - ζ))
    field_simp
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hφi2 : Integrable (fun y => φ y * (2 * y + I)) :=
    (hφ.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hφc.mul_right
  have hsplit : ∫ y, φ y * (ζ + 2 * y + I) = ζ * (∫ y, φ y) + ∫ y, φ y * (2 * y + I) := by
    rw [show (fun y => φ y * (ζ + 2 * y + I)) = fun y => ζ * φ y + φ y * (2 * y + I) from
      funext fun y => by ring, integral_add (hφi.const_mul ζ) hφi2, integral_const_mul]
  have j1 : Integrable (fun y => -(dz φ y / (y - ζ))) := i1.neg
  have j2 : Integrable (fun y => (1 / ((ζ + 1) * (ζ + I) * (ζ - 1))) * (dz φ y * (ζ ^ 2 + ζ * y + y ^ 2 + I * (ζ + y) - 1))) := i2.const_mul _
  rw [integral_congr_ae hae, integral_sub j1 j2, integral_neg, integral_const_mul, hcT,
    show ∫ y, dz φ y * (ζ ^ 2 + ζ * y + y ^ 2 + I * (ζ + y) - 1) = -∫ y, φ y * (ζ + 2 * y + I) by rw [hibp, neg_neg], hsplit]
  field_simp
  ring

/-- [Λ-INT helper] The three-point kernel near a compact `K ⊆ 𝔻*`: for `‖y‖ ≥ 1 + 2δ`,
`‖N(ζ, y)‖ ≤ ‖Dn y‖ (δ⁻¹ ‖Dn ζ‖⁻¹ + δ⁻³ 1_{B(y,δ)}(ζ) ‖ζ - y‖⁻¹)` for every `ζ`. -/
theorem d2l_N_bound {y ζ : ℂ} {δ : ℝ} (hδ : 0 < δ) (hy : 1 + 2 * δ ≤ ‖y‖) :
    ‖(((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))‖ ≤ ‖((y + 1) * (y + I) * (y - 1))‖ * (δ⁻¹ * ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ + (δ ^ 3)⁻¹ * (ball y δ).indicator (fun ζ => ‖ζ - y‖⁻¹) ζ) := by
  have hind0 : 0 ≤ (ball y δ).indicator (fun ζ => ‖ζ - y‖⁻¹) ζ :=
    indicator_nonneg (fun _ _ => inv_nonneg.2 (norm_nonneg _)) _
  rw [norm_div, norm_mul ((ζ + 1) * (ζ + I) * (ζ - 1)) (ζ - y), div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rcases eq_or_lt_of_le (norm_nonneg ((ζ + 1) * (ζ + I) * (ζ - 1))) with hD | hD
  · rw [← hD, zero_mul, inv_zero]
    positivity
  rcases eq_or_lt_of_le (norm_nonneg (ζ - y)) with hd | hd
  · rw [← hd, mul_zero, inv_zero]
    positivity
  rw [mul_inv]
  by_cases hb : ‖ζ - y‖ < δ
  · rw [indicator_of_mem (mem_ball_iff_norm.2 hb)]
    have hlow : δ ^ 3 ≤ ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖ := by
      apply d2e_dn_lower hδ.le
      have := norm_sub_norm_le y ζ
      rw [norm_sub_rev] at this
      linarith
    have : ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ ≤ (δ ^ 3)⁻¹ := inv_anti₀ (by positivity) hlow
    have h2 : 0 ≤ δ⁻¹ * ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right this (inv_nonneg.2 hd.le)]
  · rw [not_lt] at hb
    have : ‖ζ - y‖⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hb
    have h2 : 0 ≤ (δ ^ 3)⁻¹ * (ball y δ).indicator (fun ζ => ‖ζ - y‖⁻¹) ζ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this (inv_nonneg.2 hD.le)]

/-- [Λ-INT helper] **Weak derivative of a three-point Cauchy integral.** If `W` is bounded on `E`, `1_E W ∈ L²`,
and `Γ = -(1/π) ∫_E W N(·, y)` is `C¹` on `𝔻*`, then a.e. on `𝔻*`
`∂Γ = H(1_E W) + (1/π)(K₁ + (2y + i) K₀)`, `K₀ = ∫_E W/Dn`, `K₁ = ∫_E W ζ/Dn` (IBP, Fubini, `d2l_inner`, the
`L²` symmetry of the Beurling transform, and the fundamental lemma). -/
theorem d2l_weak {W Γ : ℂ → ℂ} {E : Set ℂ} {Wb : ℝ} (hEm : MeasurableSet E)
    (hWm : AEStronglyMeasurable W (volume.restrict E)) (hWb : ∀ᵐ ζ ∂(volume.restrict E), ‖W ζ‖ ≤ Wb)
    (hW2 : MemLp (E.indicator W) 2)
    (hK0 : IntegrableOn (fun ζ => W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) E) (hK1 : IntegrableOn (fun ζ => W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) E)
    (hΓ : ∀ y ∈ unitDiscExterior, Γ y = -(1 / π : ℂ) * ∫ ζ in E, W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))
    (hΓC : ContDiffOn ℝ 1 Γ unitDiscExterior) :
    ∀ᵐ y ∂(volume.restrict unitDiscExterior), dz Γ y = hilbertH (E.indicator W) y +
      (1 / π : ℂ) * ((∫ ζ in E, W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) + (2 * y + I) * ∫ ζ in E, W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hOm : MeasurableSet unitDiscExterior := hO.measurableSet
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hH2 := (hilbertH_memLp_two hW2).1
  obtain ⟨K0, hK0d⟩ : ∃ K, K = ∫ ζ in E, W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) := ⟨_, rfl⟩
  obtain ⟨K1, hK1d⟩ : ∃ K, K = ∫ ζ in E, W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) := ⟨_, rfl⟩
  rw [← hK0d, ← hK1d]
  have hWb' : ∀ᵐ ζ ∂(volume.restrict E), ‖W ζ‖ ≤ max Wb 0 := by
    filter_upwards [hWb] with ζ h using h.trans (le_max_left _ _)
  have hdzC : ContinuousOn (dz Γ) unitDiscExterior := by
    have hf := hΓC.continuousOn_fderiv_of_isOpen hO le_rfl
    exact ((hf.clm_apply continuousOn_const).sub (continuousOn_const.mul (hf.clm_apply continuousOn_const))).div_const 2
  have hDn0 : ∀ᵐ ζ ∂volume, ((ζ + 1) * (ζ + I) * (ζ - 1)) ≠ 0 := by
    have hc : ({1, -1, -I} : Set ℂ).Countable := (Set.toFinite _).countable
    filter_upwards [hc.ae_notMem volume] with ζ hζ h
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hζ
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact hζ.2.1 (by linear_combination h)
      · exact hζ.2.2 (by linear_combination h)
    · exact hζ.1 (by linear_combination h)
  -- the weak identity against real test functions
  have key : ∀ g : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → tsupport g ⊆ unitDiscExterior →
      ∫ y, g y • (dz Γ y - (hilbertH (E.indicator W) y + (1 / π : ℂ) * (K1 + (2 * y + I) * K0))) = 0 := by
    intro g hg hgc hgU
    obtain ⟨φ, hφd⟩ : ∃ φ : ℂ → ℂ, φ = fun y => (g y : ℂ) := ⟨_, rfl⟩
    have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := by
      rw [hφd]
      exact ofRealCLM.contDiff.comp hg
    have hφs : Function.support φ ⊆ tsupport g := fun y hy => subset_closure fun h => hy (by rw [hφd]; simp [h])
    have hφc : HasCompactSupport φ := hgc.mono' hφs
    have hφU : tsupport φ ⊆ unitDiscExterior := (closure_minimal hφs (isClosed_tsupport g)).trans hgU
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have hφ2 : MemLp φ 2 := hφ.continuous.memLp_of_hasCompactSupport hφc
    have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
    have hdc : Continuous (dz φ) := by
      have hf := hφ1.continuous_fderiv one_ne_zero
      exact ((hf.clm_apply continuous_const).sub (continuous_const.mul (hf.clm_apply continuous_const))).div_const 2
    have hdz0 : ∀ y ∉ tsupport φ, dz φ y = 0 := fun y hy => by
      show (fderiv ℝ φ y 1 - I * fderiv ℝ φ y I) / 2 = 0
      rw [fderiv_of_notMem_tsupport ℝ hy]
      simp
    have hdcs : HasCompactSupport (dz φ) := HasCompactSupport.intro hφc.isCompact hdz0
    -- Fubini on `ℂ × E` from the combined kernel bound
    obtain ⟨δ, hδ, hδK⟩ : ∃ δ > 0, ∀ y ∈ tsupport φ, 1 + 2 * δ ≤ ‖y‖ := by
      rcases (tsupport φ).eq_empty_or_nonempty with h | h
      · exact ⟨1, one_pos, fun y hy => by simp [h] at hy⟩
      · obtain ⟨y0, hy0, hmin⟩ := hφc.isCompact.exists_isMinOn h continuous_norm.continuousOn
        have h1 : 1 < ‖y0‖ := hφU hy0
        exact ⟨(‖y0‖ - 1) / 2, by linarith, fun y hy => by
          have : ‖y0‖ ≤ ‖y‖ := hmin hy
          linarith⟩
    obtain ⟨A, hA⟩ := hφc.isCompact.exists_bound_of_continuousOn
      ((by fun_prop : Continuous fun w : ℂ => ((w + 1) * (w + I) * (w - 1))).continuousOn)
    obtain ⟨M, hM⟩ := hdc.bounded_above_of_compact_support hdcs
    obtain ⟨maj, hmaj⟩ : ∃ maj : ℂ → ℂ → ℝ, maj = fun y ζ =>
        δ⁻¹ * ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ + (δ ^ 3)⁻¹ * (ball y δ).indicator (fun ζ => ‖ζ - y‖⁻¹) ζ := ⟨_, rfl⟩
    have hmi : ∀ y, Integrable (maj y) := fun y => by
      rw [hmaj]
      exact (d2e_dn_int.const_mul δ⁻¹).add
        (((integrable_indicator_iff measurableSet_ball).2 (e124p_invnorm_int y δ)).const_mul _)
    have hm0 : ∀ y ζ, 0 ≤ maj y ζ := fun y ζ => by
      rw [hmaj]
      have : 0 ≤ (ball y δ).indicator (fun ζ => ‖ζ - y‖⁻¹) ζ :=
        indicator_nonneg (fun _ _ => inv_nonneg.2 (norm_nonneg _)) _
      positivity
    have hCB : ∀ y, ∫ ζ, (ball y δ).indicator (fun ζ => ‖ζ - y‖⁻¹) ζ =
        ∫ ζ, (ball (0 : ℂ) δ).indicator (fun ζ => ‖ζ‖⁻¹) ζ := fun y => by
      have ht : (fun ζ => (ball y δ).indicator (fun ζ => ‖ζ - y‖⁻¹) ζ) =
          fun ζ => (ball (0 : ℂ) δ).indicator (fun ζ => ‖ζ‖⁻¹) (ζ - y) := funext fun ζ => by
        simp only [Set.indicator, mem_ball, dist_eq_norm, sub_zero]
      rw [ht]
      exact integral_sub_right_eq_self (fun ζ => (ball (0 : ℂ) δ).indicator (fun ζ => ‖ζ‖⁻¹) ζ) y
    have hmB : ∀ y, ∫ ζ, maj y ζ = ∫ ζ, maj 0 ζ := fun y => by
      simp only [hmaj]
      rw [integral_add (d2e_dn_int.const_mul δ⁻¹)
        (((integrable_indicator_iff measurableSet_ball).2 (e124p_invnorm_int y δ)).const_mul _),
        integral_add (d2e_dn_int.const_mul δ⁻¹)
        (((integrable_indicator_iff measurableSet_ball).2 (e124p_invnorm_int 0 δ)).const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, hCB y, hCB 0]
    obtain ⟨Bk, hBk⟩ : ∃ B : ℝ, B = ∫ ζ, maj 0 ζ := ⟨_, rfl⟩
    have hFb : ∀ y ∈ tsupport φ, ∀ᵐ ζ ∂(volume.restrict E),
        ‖dz φ y * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))‖ ≤ ‖dz φ y‖ * (max Wb 0 * (A * maj y ζ)) := fun y hy => by
      filter_upwards [hWb'] with ζ hζ
      rw [norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left (mul_le_mul hζ ?_ (norm_nonneg _) (le_max_right _ _)) (norm_nonneg _)
      rw [hmaj]
      exact (d2l_N_bound hδ (hδK y hy)).trans
        (mul_le_mul_of_nonneg_right (hA y hy) (by have := hm0 y ζ; rwa [hmaj] at this))
    have hFm : AEStronglyMeasurable (Function.uncurry fun y ζ => dz φ y * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))))
        (volume.prod (volume.restrict E)) := by
      show AEStronglyMeasurable (fun p : ℂ × ℂ => dz φ p.1 * (W p.2 * (((p.1 + 1) * (p.1 + I) * (p.1 - 1)) / (((p.2 + 1) * (p.2 + I) * (p.2 - 1)) * (p.2 - p.1))))) _
      have h1 : AEStronglyMeasurable (fun p : ℂ × ℂ => W p.2) (volume.prod (volume.restrict E)) := hWm.comp_snd
      have h2 : AEStronglyMeasurable (fun p : ℂ × ℂ => (((p.1 + 1) * (p.1 + I) * (p.1 - 1)) / (((p.2 + 1) * (p.2 + I) * (p.2 - 1)) * (p.2 - p.1)))) (volume.prod (volume.restrict E)) :=
        (((by fun_prop : Continuous fun p : ℂ × ℂ => ((p.1 + 1) * (p.1 + I) * (p.1 - 1))).measurable).div
          ((by fun_prop : Continuous fun p : ℂ × ℂ => ((p.2 + 1) * (p.2 + I) * (p.2 - 1)) * (p.2 - p.1)).measurable)).aestronglyMeasurable
      exact (hdc.comp continuous_fst).aestronglyMeasurable.mul (h1.mul h2)
    have hFi : Integrable (Function.uncurry fun y ζ => dz φ y * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))))
        (volume.prod (volume.restrict E)) := by
      refine (integrable_prod_iff hFm).2 ⟨?_, ?_⟩
      · filter_upwards [hFm.prodMk_left] with y hym
        by_cases hy : y ∈ tsupport φ
        · exact ((((hmi y).integrableOn (s := E)).const_mul A).const_mul (max Wb 0) |>.const_mul ‖dz φ y‖).mono'
            hym (hFb y hy)
        · simp only [Function.uncurry_apply_pair, hdz0 y hy, zero_mul]
          exact integrable_zero _ _ _
      · refine (hdc.norm.mul_const (max Wb 0 * (A * Bk))).integrable_of_hasCompactSupport
          hdcs.norm.mul_right |>.mono' hFm.norm.integral_prod_right' (Eventually.of_forall fun y => ?_)
        by_cases hy : y ∈ tsupport φ
        · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
          have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA y hy)
          calc ∫ ζ in E, ‖Function.uncurry (fun y ζ => dz φ y * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) (y, ζ)‖
              ≤ ∫ ζ in E, ‖dz φ y‖ * (max Wb 0 * (A * maj y ζ)) :=
                integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
                  ((((hmi y).integrableOn (s := E)).const_mul A).const_mul (max Wb 0) |>.const_mul ‖dz φ y‖)
                  (hFb y hy)
            _ = ‖dz φ y‖ * (max Wb 0 * (A * ∫ ζ in E, maj y ζ)) := by
                rw [integral_const_mul, integral_const_mul, integral_const_mul]
            _ ≤ ‖dz φ y‖ * (max Wb 0 * (A * Bk)) := by
                refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left ?_ hA0) (le_max_right _ _)) (norm_nonneg _)
                rw [hBk, ← hmB y]
                exact setIntegral_le_integral (hmi y) (Eventually.of_forall (hm0 y))
        · simp only [Function.uncurry_apply_pair, hdz0 y hy, zero_mul, norm_zero, integral_zero,
            le_refl]
    -- the chain
    have e1 := d2l_ibp hO hΓC hφ1 hφc hφU
    have e2 : ∫ y, dz φ y * Γ y = -(1 / π : ℂ) * ∫ ζ in E, ∫ y, dz φ y * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) := by
      rw [← integral_integral_swap hFi, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ tsupport φ
      · show dz φ y * Γ y = -(1 / π : ℂ) * ∫ ζ in E, dz φ y * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))
        rw [hΓ y (hφU hy), integral_const_mul]
        ring
      · show dz φ y * Γ y = -(1 / π : ℂ) * ∫ ζ in E, dz φ y * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))
        simp only [hdz0 y hy, zero_mul, integral_zero, mul_zero]
    have hHs := hilbertH_eq_ae_smooth hφ hφc
    have hWH : Integrable (fun ζ => E.indicator W ζ * hilbertH φ ζ) :=
      hW2.integrable_mul (hilbertH_memLp_two hφ2).1
    have hWHs : IntegrableOn (fun ζ => W ζ * hilbertHSmooth φ ζ) E := by
      refine (integrable_indicator_iff hEm).1 (hWH.congr ?_)
      filter_upwards [hHs] with ζ hζ
      by_cases hζE : ζ ∈ E
      · simp [indicator_of_mem hζE, hζ]
      · simp [indicator_of_notMem hζE]
    have e3 : ∫ ζ in E, ∫ y, dz φ y * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) = π * (∫ ζ in E, W ζ * hilbertHSmooth φ ζ) +
        (∫ y, φ y) * K1 + (∫ y, φ y * (2 * y + I)) * K0 := by
      have hc : ∫ ζ in E, ∫ y, dz φ y * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) = ∫ ζ in E, (π * (W ζ * hilbertHSmooth φ ζ) +
          (∫ y, φ y) * (W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) + (∫ y, φ y * (2 * y + I)) * (W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae hDn0] with ζ hζ
        rw [show (fun y => dz φ y * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) = fun y => W ζ * (dz φ y * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) from
          funext fun y => by ring, integral_const_mul, d2l_inner hφ hφc hζ]
        field_simp
        ring
      have j1 : IntegrableOn (fun ζ => π * (W ζ * hilbertHSmooth φ ζ)) E := Integrable.const_mul hWHs _
      have j2 : IntegrableOn (fun ζ => (∫ y, φ y) * (W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) E := Integrable.const_mul hK1 _
      have j3 : IntegrableOn (fun ζ => (∫ y, φ y * (2 * y + I)) * (W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) E := Integrable.const_mul hK0 _
      have j12 : IntegrableOn (fun ζ => π * (W ζ * hilbertHSmooth φ ζ) + (∫ y, φ y) * (W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) E :=
        Integrable.add j1 j2
      rw [hc, integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul, integral_const_mul,
        ← hK0d, ← hK1d]
    have e4 : ∫ ζ in E, W ζ * hilbertHSmooth φ ζ = ∫ ζ, hilbertH (E.indicator W) ζ * φ ζ := by
      rw [hilbertH_pairing_symm_L2 hW2 hφ2, ← integral_indicator hEm]
      refine integral_congr_ae ?_
      filter_upwards [hHs] with ζ hζ
      by_cases hζE : ζ ∈ E
      · simp [indicator_of_mem hζE, hζ]
      · simp [indicator_of_notMem hζE]
    -- assemble
    have hP : Integrable (fun y => φ y * dz Γ y) := by
      refine Continuous.integrable_of_hasCompactSupport (continuous_of_tsupport fun x hx => ?_) hφc.mul_right
      have hxU : x ∈ unitDiscExterior := hφU (tsupport_mul_subset_left hx)
      exact hφ.continuous.continuousAt.mul ((hdzC x hxU).continuousAt (hO.mem_nhds hxU))
    have hHφ : Integrable (fun y => φ y * hilbertH (E.indicator W) y) := hφ2.integrable_mul hH2
    have hφp : Integrable (fun y => φ y * ((1 / π : ℂ) * (K1 + (2 * y + I) * K0))) :=
      (hφ.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hφc.mul_right
    have hφ2y : Integrable (fun y => φ y * (2 * y + I)) :=
      (hφ.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hφc.mul_right
    have hpoly : ∫ y, φ y * ((1 / π : ℂ) * (K1 + (2 * y + I) * K0)) =
        (1 / π : ℂ) * ((∫ y, φ y) * K1 + (∫ y, φ y * (2 * y + I)) * K0) := by
      rw [show (fun y => φ y * ((1 / π : ℂ) * (K1 + (2 * y + I) * K0))) =
        fun y => (1 / π : ℂ) * (K1 * φ y + K0 * (φ y * (2 * y + I))) from funext fun y => by ring,
        integral_const_mul, integral_add (hφi.const_mul _) (hφ2y.const_mul _), integral_const_mul,
        integral_const_mul]
      ring
    have hsm : (fun y => g y • (dz Γ y - (hilbertH (E.indicator W) y + (1 / π : ℂ) * (K1 + (2 * y + I) * K0)))) =
        fun y => φ y * dz Γ y - φ y * hilbertH (E.indicator W) y -
          φ y * ((1 / π : ℂ) * (K1 + (2 * y + I) * K0)) := funext fun y => by
      rw [hφd, real_smul]
      ring
    have hPH : Integrable (fun y => φ y * dz Γ y - φ y * hilbertH (E.indicator W) y) := Integrable.sub hP hHφ
    rw [hsm, integral_sub hPH hφp, integral_sub hP hHφ, hpoly, e1, e2, e3, e4]
    rw [show (fun y => φ y * hilbertH (E.indicator W) y) = fun y => hilbertH (E.indicator W) y * φ y from
      funext fun y => mul_comm _ _]
    field_simp
    ring
  -- the fundamental lemma
  have hloc : LocallyIntegrableOn (fun y => dz Γ y - (hilbertH (E.indicator W) y +
      (1 / π : ℂ) * (K1 + (2 * y + I) * K0))) unitDiscExterior :=
    (hdzC.locallyIntegrableOn hOm).sub (((hH2.locallyIntegrable one_le_two).locallyIntegrableOn _).add
      ((by fun_prop : Continuous fun y : ℂ => (1 / π : ℂ) * (K1 + (2 * y + I) * K0)).locallyIntegrable.locallyIntegrableOn _))
  have h0 := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc key
  filter_upwards [ae_restrict_of_ae h0, ae_restrict_mem hOm] with y hy hyO
  exact sub_eq_zero.1 (hy hyO)

/-- [Λ-INT helper] `‖y‖⁻² ‖ζ - y‖⁻¹ ≤ 8(1 + ‖y‖)⁻³ + 1_{B(ζ,1)}(y) ‖y - ζ‖⁻¹ + 8(1 + ‖y - ζ‖)⁻³` for `‖y‖ ≥ 1`. -/
theorem d2l_split {y ζ : ℂ} (hy : 1 ≤ ‖y‖) :
    (‖y‖ ^ 2)⁻¹ * ‖ζ - y‖⁻¹ ≤ 8 * (1 + ‖y‖) ^ (-(3 : ℝ)) + (ball ζ 1).indicator (fun y => ‖y - ζ‖⁻¹) y +
      8 * (1 + ‖y - ζ‖) ^ (-(3 : ℝ)) := by
  have hb := norm_nonneg (y - ζ)
  have hc : ∀ t : ℝ, 0 ≤ t → (1 + t) ^ (-(3 : ℝ)) = ((1 + t) ^ 3)⁻¹ := fun t ht => by
    rw [Real.rpow_neg (by linarith), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hc _ (norm_nonneg _), hc _ hb, norm_sub_rev ζ y]
  have hind0 : 0 ≤ (ball ζ 1).indicator (fun y => ‖y - ζ‖⁻¹) y :=
    indicator_nonneg (fun _ _ => inv_nonneg.2 (norm_nonneg _)) _
  have h1 : 0 ≤ 8 * ((1 + ‖y‖) ^ 3)⁻¹ := by positivity
  have h3 : 0 ≤ 8 * ((1 + ‖y - ζ‖) ^ 3)⁻¹ := by positivity
  rcases eq_or_lt_of_le hb with h0 | h0
  · rw [← h0, inv_zero, mul_zero]
    positivity
  set a := ‖y‖
  set c := ‖y - ζ‖
  have ha0 : 0 < a := by linarith
  have key8 : ∀ t : ℝ, 1 ≤ t → 1 / t ^ 3 ≤ 8 * ((1 + t) ^ 3)⁻¹ := fun t ht => by
    rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + t) (by linarith : 1 + t ≤ 2 * t) 3]
  by_cases hab : a ≤ c
  · have : (a ^ 2)⁻¹ * c⁻¹ ≤ 1 / a ^ 3 := by
      rw [← mul_inv, one_div]
      exact inv_anti₀ (by positivity) (by nlinarith [sq_nonneg a])
    linarith [key8 a hy]
  · push_neg at hab
    by_cases hc1 : c < 1
    · rw [indicator_of_mem (mem_ball_iff_norm.2 hc1)]
      have : (a ^ 2)⁻¹ * c⁻¹ ≤ c⁻¹ := by
        have : (a ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
        nlinarith [inv_nonneg.2 h0.le]
      linarith
    · push_neg at hc1
      have : (a ^ 2)⁻¹ * c⁻¹ ≤ 1 / c ^ 3 := by
        rw [← mul_inv, one_div]
        exact inv_anti₀ (by positivity) (by nlinarith [mul_le_mul hab.le hab.le h0.le ha0.le])
      linarith [key8 c hc1]

/-- [Λ-INT helper] **Weighted integrability of a three-point Cauchy integral**: `‖y‖⁻⁵ ‖Γ(y)‖ ∈ L¹(𝔻*)` for
`Γ = -(1/π) ∫_E W N(·, y)` with `W` bounded (Tonelli with the uniform bound `d2l_split`). -/
theorem d2l_wint {W Γ : ℂ → ℂ} {E : Set ℂ} {Wb : ℝ} (hEm : MeasurableSet E)
    (hWm : AEStronglyMeasurable W (volume.restrict E)) (hWb : ∀ᵐ ζ ∂(volume.restrict E), ‖W ζ‖ ≤ Wb)
    (hΓ : ∀ y ∈ unitDiscExterior, Γ y = -(1 / π : ℂ) * ∫ ζ in E, W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))
    (hΓc : ContinuousOn Γ unitDiscExterior) :
    IntegrableOn (fun y => (‖y‖ ^ 5)⁻¹ * ‖Γ y‖) unitDiscExterior := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hOm : MeasurableSet unitDiscExterior := hO.measurableSet
  have hfin : (Module.finrank ℝ ℂ : ℝ) < 3 := by rw [Complex.finrank_real_complex]; norm_num
  have hj := integrable_one_add_norm (E := ℂ) (μ := volume) hfin
  -- the uniform inner bound
  obtain ⟨maj, hmaj⟩ : ∃ m : ℂ → ℂ → ℝ, m = fun ζ y => 8 * (1 + ‖y‖) ^ (-(3 : ℝ)) +
      (ball ζ 1).indicator (fun y => ‖y - ζ‖⁻¹) y + 8 * (1 + ‖y - ζ‖) ^ (-(3 : ℝ)) := ⟨_, rfl⟩
  have hmi : ∀ ζ, Integrable (maj ζ) := fun ζ => by
    rw [hmaj]
    exact ((hj.const_mul 8).add ((integrable_indicator_iff measurableSet_ball).2
      (by simpa only [norm_sub_rev] using e124p_invnorm_int ζ 1))).add ((hj.comp_sub_right ζ).const_mul 8)
  have hm0 : ∀ ζ y, 0 ≤ maj ζ y := fun ζ y => by
    rw [hmaj]
    have : 0 ≤ (ball ζ 1).indicator (fun y => ‖y - ζ‖⁻¹) y :=
      indicator_nonneg (fun _ _ => inv_nonneg.2 (norm_nonneg _)) _
    positivity
  have hmB : ∀ ζ, ∫ y, maj ζ y = ∫ y, maj 0 y := fun ζ => by
    have ht : ∀ ζ : ℂ, (fun y => (ball ζ 1).indicator (fun y => ‖y - ζ‖⁻¹) y) =
        fun y => (ball (0 : ℂ) 1).indicator (fun y => ‖y‖⁻¹) (y - ζ) := fun ζ => funext fun y => by
      simp only [Set.indicator, mem_ball, dist_eq_norm, sub_zero]
    have hi : ∀ ζ : ℂ, Integrable fun y => (ball ζ 1).indicator (fun y => ‖y - ζ‖⁻¹) y := fun ζ =>
      (integrable_indicator_iff measurableSet_ball).2 (by simpa only [norm_sub_rev] using e124p_invnorm_int ζ 1)
    have hC : Integrable (fun y : ℂ => 8 * (1 + ‖y‖) ^ (-(3 : ℝ))) := hj.const_mul 8
    have hA : ∀ ζ : ℂ, Integrable (fun y => 8 * (1 + ‖y‖) ^ (-(3 : ℝ)) +
        (ball ζ 1).indicator (fun y => ‖y - ζ‖⁻¹) y) := fun ζ => Integrable.add hC (hi ζ)
    have hB : ∀ ζ : ℂ, Integrable (fun y : ℂ => 8 * (1 + ‖y - ζ‖) ^ (-(3 : ℝ))) := fun ζ =>
      (hj.comp_sub_right ζ).const_mul 8
    simp only [hmaj]
    rw [integral_add (hA ζ) (hB ζ), integral_add hC (hi ζ), integral_add (hA 0) (hB 0), integral_add hC (hi 0),
      integral_const_mul 8 (fun y : ℂ => (1 + ‖y - ζ‖) ^ (-(3 : ℝ))),
      integral_const_mul 8 (fun y : ℂ => (1 + ‖y - 0‖) ^ (-(3 : ℝ))), ht ζ, ht 0,
      integral_sub_right_eq_self (fun y => (ball (0 : ℂ) 1).indicator (fun y => ‖y‖⁻¹) y) ζ,
      integral_sub_right_eq_self (fun y => (ball (0 : ℂ) 1).indicator (fun y => ‖y‖⁻¹) y) 0,
      integral_sub_right_eq_self (fun y => (1 + ‖y‖) ^ (-(3 : ℝ))) ζ,
      integral_sub_right_eq_self (fun y => (1 + ‖y‖) ^ (-(3 : ℝ))) 0]
  -- Tonelli on `𝔻* × E`
  obtain ⟨f, hf⟩ : ∃ f : ℂ × ℂ → ℝ, f = fun p => (‖p.2‖ ^ 2)⁻¹ * (‖((p.1 + 1) * (p.1 + I) * (p.1 - 1))‖⁻¹ * ‖p.1 - p.2‖⁻¹) := ⟨_, rfl⟩
  have hfM : Measurable f := by
    rw [hf]
    fun_prop
  have hfm : AEStronglyMeasurable f ((volume.restrict E).prod (volume.restrict unitDiscExterior)) :=
    hfM.aestronglyMeasurable
  have hfb : ∀ ζ, ∀ᵐ y ∂(volume.restrict unitDiscExterior), ‖f (ζ, y)‖ ≤ ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ * maj ζ y := fun ζ => by
    filter_upwards [ae_restrict_mem hOm] with y hy
    have hy1 : 1 ≤ ‖y‖ := le_of_lt hy
    rw [hf, Real.norm_eq_abs, abs_of_nonneg (by positivity), hmaj]
    calc (‖y‖ ^ 2)⁻¹ * (‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ * ‖ζ - y‖⁻¹) = ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ * ((‖y‖ ^ 2)⁻¹ * ‖ζ - y‖⁻¹) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (d2l_split hy1) (inv_nonneg.2 (norm_nonneg _))
  have hfi : Integrable f ((volume.restrict E).prod (volume.restrict unitDiscExterior)) := by
    refine (integrable_prod_iff hfm).2 ⟨Eventually.of_forall fun ζ => ?_, ?_⟩
    · exact (((hmi ζ).integrableOn (s := unitDiscExterior)).const_mul _).mono'
        (hfM.comp measurable_prodMk_left).aestronglyMeasurable (hfb ζ)
    · refine ((d2e_dn_int.const_mul (∫ y, maj 0 y)).integrableOn (s := E)).mono'
        hfm.norm.integral_prod_right' (Eventually.of_forall fun ζ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← hmB ζ]
      calc ∫ y in unitDiscExterior, ‖f (ζ, y)‖ ≤ ∫ y in unitDiscExterior, ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ * maj ζ y :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              (((hmi ζ).integrableOn (s := unitDiscExterior)).const_mul _) (hfb ζ)
        _ ≤ ∫ y, ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ * maj ζ y :=
            setIntegral_le_integral ((hmi ζ).const_mul _)
              (Eventually.of_forall fun y => mul_nonneg (inv_nonneg.2 (norm_nonneg _)) (hm0 ζ y))
        _ = (∫ y, maj ζ y) * ‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ := by rw [integral_const_mul, mul_comm]
  -- the pointwise bound
  have hint := hfi.integral_prod_right
  have hWb' : ∀ᵐ ζ ∂(volume.restrict E), ‖W ζ‖ ≤ max Wb 0 := by
    filter_upwards [hWb] with ζ h using h.trans (le_max_left _ _)
  refine ((hint.const_mul (8 * max Wb 0))).mono'
    ((continuous_norm.pow 5).continuousOn.inv₀ (fun y hy => pow_ne_zero 5 (lt_trans one_pos hy).ne') |>.mul hΓc.norm |>.aestronglyMeasurable hOm) ?_
  have hsec : ∀ᵐ y ∂(volume.restrict unitDiscExterior), Integrable (fun ζ => f (ζ, y)) (volume.restrict E) :=
    ((integrable_prod_iff' hfm).1 hfi).1
  filter_upwards [ae_restrict_mem hOm, hsec] with y hy hyi
  have hy1 : 1 < ‖y‖ := hy
  have hDy : ‖((y + 1) * (y + I) * (y - 1))‖ ≤ 8 * ‖y‖ ^ 3 := by
    have h1 : ‖y + 1‖ ≤ 2 * ‖y‖ := by
      have := norm_add_le y 1
      rw [norm_one] at this
      linarith
    have h2 : ‖y + I‖ ≤ 2 * ‖y‖ := by
      have := norm_add_le y I
      rw [Complex.norm_I] at this
      linarith
    have h3 : ‖y - 1‖ ≤ 2 * ‖y‖ := by
      have := norm_sub_le y 1
      rw [norm_one] at this
      linarith
    rw [norm_mul, norm_mul]
    calc ‖y + 1‖ * ‖y + I‖ * ‖y - 1‖ ≤ (2 * ‖y‖) * (2 * ‖y‖) * (2 * ‖y‖) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)
      _ = 8 * ‖y‖ ^ 3 := by ring
  have hpt : ∀ᵐ ζ ∂(volume.restrict E), ‖W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))‖ ≤ max Wb 0 * (8 * ‖y‖ ^ 3) * (‖y‖ ^ 2 * f (ζ, y)) := by
    filter_upwards [hWb'] with ζ hζ
    rw [norm_mul, norm_div, norm_mul ((ζ + 1) * (ζ + I) * (ζ - 1)) (ζ - y), hf]
    have hy0 : ‖y‖ ^ 2 ≠ 0 := by positivity
    calc ‖W ζ‖ * (‖((y + 1) * (y + I) * (y - 1))‖ / (‖((ζ + 1) * (ζ + I) * (ζ - 1))‖ * ‖ζ - y‖)) = ‖W ζ‖ * (‖((y + 1) * (y + I) * (y - 1))‖ * (‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ * ‖ζ - y‖⁻¹)) := by
          rw [div_eq_mul_inv, mul_inv]
      _ ≤ max Wb 0 * (8 * ‖y‖ ^ 3 * (‖((ζ + 1) * (ζ + I) * (ζ - 1))‖⁻¹ * ‖ζ - y‖⁻¹)) :=
          mul_le_mul hζ (mul_le_mul_of_nonneg_right hDy (by positivity)) (by positivity) (le_max_right _ _)
      _ = _ := by field_simp
  have hΓb : ‖Γ y‖ ≤ max Wb 0 * (8 * ‖y‖ ^ 3) * (‖y‖ ^ 2 * ∫ ζ in E, f (ζ, y)) := by
    rw [hΓ y hy, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have hπ1 : 1 / π ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
    calc 1 / π * ‖∫ ζ in E, W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))‖ ≤ 1 * ∫ ζ in E, max Wb 0 * (8 * ‖y‖ ^ 3) * (‖y‖ ^ 2 * f (ζ, y)) :=
          mul_le_mul hπ1 ((norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
            (Eventually.of_forall fun _ => norm_nonneg _) ((hyi.const_mul _).const_mul _) hpt))
            (norm_nonneg _) zero_le_one
      _ = _ := by rw [one_mul, integral_const_mul, integral_const_mul]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (‖y‖ ^ 5)⁻¹ * ‖Γ y‖ ≤ (‖y‖ ^ 5)⁻¹ * (max Wb 0 * (8 * ‖y‖ ^ 3) * (‖y‖ ^ 2 * ∫ ζ in E, f (ζ, y))) :=
        mul_le_mul_of_nonneg_left hΓb (by positivity)
    _ = 8 * max Wb 0 * ∫ ζ in E, f (ζ, y) := by field_simp

/-- [Λ-INT helper] `‖y‖⁻ᵏ ∈ L¹(𝔻*)` for `k ≥ 3`. -/
theorem d2l_powint {k : ℕ} (hk : 3 ≤ k) : IntegrableOn (fun y : ℂ => (‖y‖ ^ k)⁻¹) unitDiscExterior := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hfin : (Module.finrank ℝ ℂ : ℝ) < k := by
    rw [Complex.finrank_real_complex]
    exact_mod_cast (by omega : 2 < k)
  have hj := (integrable_one_add_norm (E := ℂ) (μ := volume) hfin).const_mul (2 ^ k)
  refine hj.integrableOn.mono' ((continuous_norm.pow k).continuousOn.inv₀ (fun y hy =>
    pow_ne_zero k (lt_trans one_pos hy).ne') |>.aestronglyMeasurable hO.measurableSet) ?_
  filter_upwards [ae_restrict_mem hO.measurableSet] with y hy
  have hy1 : 1 < ‖y‖ := hy
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast,
    ← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc (1 + ‖y‖) ^ k ≤ (2 * ‖y‖) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    _ = 2 ^ k * ‖y‖ ^ k := mul_pow _ _ _

/-- [Λ-INT helper] `dz` of a function `C¹` on `𝔻*` is continuous on `𝔻*`. -/
theorem d2l_dz_cont {F : ℂ → ℂ} (hF : ContDiffOn ℝ 1 F unitDiscExterior) :
    ContinuousOn (dz F) unitDiscExterior := by
  have hf := hF.continuousOn_fderiv_of_isOpen (isOpen_lt continuous_const continuous_norm) le_rfl
  exact ((hf.clm_apply continuousOn_const).sub (continuousOn_const.mul (hf.clm_apply continuousOn_const))).div_const 2

/-- [Λ-INT helper] **Λ-INT, abstract form.** -/
theorem d2l_main {A R S : ℂ → ℂ} {CA CA' Rb Sb : ℝ} (hCA : 0 ≤ CA) (hCA' : 0 ≤ CA')
    (hAd : DifferentiableOn ℂ A unitDiscExterior)
    (hA : ∀ z ∈ unitDiscExterior, ‖A z‖ ≤ CA * (‖z‖ ^ 3)⁻¹)
    (hA' : ∀ z ∈ unitDiscExterior, ‖deriv A z‖ ≤ CA' * (‖z‖ ^ 4)⁻¹)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hSm : AEStronglyMeasurable S (volume.restrict unitDisc)) (hSb : ∀ᵐ ζ ∂(volume.restrict unitDisc), ‖S ζ‖ ≤ Sb)
    (hγ1 : ContDiffOn ℝ 1 (fun y : ℂ => -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) unitDiscExterior)
    (hγ2 : DifferentiableOn ℂ (fun y : ℂ => -(1 / π : ℂ) * ∫ ζ in unitDisc, S ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) unitDiscExterior) :
    Integrable (fun z : ℂ => (conj (A z) * dz (fun y : ℂ => A y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z +
      A z * conj (dz (fun y : ℂ => A y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, S ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z)))
      (volume.restrict unitDiscExterior) := by
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hOm : MeasurableSet unitDiscExterior := hO.measurableSet
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hπ1 : ‖(1 / π : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  obtain ⟨γ1, hγ1e⟩ : ∃ γ : ℂ → ℂ, γ = fun y => -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) := ⟨_, rfl⟩
  obtain ⟨γ2, hγ2e⟩ : ∃ γ : ℂ → ℂ, γ = fun y => -(1 / π : ℂ) * ∫ ζ in unitDisc, S ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) := ⟨_, rfl⟩
  rw [show (fun y : ℂ => A y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) = fun y => A y * γ1 y by
      rw [hγ1e],
    show (fun y : ℂ => A y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, S ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) = fun y => A y * γ2 y by rw [hγ2e]]
  rw [← hγ1e] at hγ1
  rw [← hγ2e] at hγ2
  -- `W = R/ζ²`
  obtain ⟨W, hWe⟩ : ∃ W : ℂ → ℂ, W = fun ζ => R ζ / ζ ^ 2 := ⟨_, rfl⟩
  have hWm : AEStronglyMeasurable W (volume.restrict unitDiscExterior) := by
    rw [hWe]
    exact hRm.div₀ (continuous_id.pow 2).aestronglyMeasurable
  have hWb : ∀ᵐ ζ ∂(volume.restrict unitDiscExterior), ‖W ζ‖ ≤ max Rb 0 * (‖ζ‖ ^ 2)⁻¹ := by
    filter_upwards [hRb, ae_restrict_mem hOm] with ζ h hζ
    rw [hWe, norm_div, norm_pow, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (h.trans (le_max_left _ _)) (by positivity)
  have hWb1 : ∀ᵐ ζ ∂(volume.restrict unitDiscExterior), ‖W ζ‖ ≤ max Rb 0 := by
    filter_upwards [hWb, ae_restrict_mem hOm] with ζ h hζ
    have : (‖ζ‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [show (1 : ℝ) < ‖ζ‖ from hζ])
    nlinarith [le_max_right Rb 0]
  have hW2 : MemLp (unitDiscExterior.indicator W) 2 := by
    have h4 := d2l_powint (k := 4) (by norm_num)
    refine (memLp_indicator_iff_restrict hOm).2 ?_
    refine MemLp.of_le (g := fun ζ => max Rb 0 * (‖ζ‖ ^ 2)⁻¹) ?_ hWm ?_
    swap
    · filter_upwards [hWb] with ζ h
      rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (by positivity))]
    refine (memLp_two_iff_integrable_sq ((continuous_norm.pow 2).continuousOn.inv₀ (fun y hy =>
      pow_ne_zero 2 (lt_trans one_pos hy).ne') |>.aestronglyMeasurable hOm |>.const_mul _)).2 ?_
    refine (h4.const_mul (max Rb 0 ^ 2)).congr ?_
    filter_upwards [ae_restrict_mem hOm] with ζ hζ
    show max Rb 0 ^ 2 * (‖ζ‖ ^ 4)⁻¹ = (max Rb 0 * (‖ζ‖ ^ 2)⁻¹) ^ 2
    ring
  -- the constants
  have hDi : ∀ {E : Set ℂ} {V : ℂ → ℂ} {b : ℝ}, AEStronglyMeasurable V (volume.restrict E) →
      (∀ᵐ ζ ∂(volume.restrict E), ‖V ζ‖ ≤ b) → IntegrableOn (fun ζ => V ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) E := fun {E V b} hm hb => by
    refine (d2e_dn_int.const_mul b).integrableOn.mono'
      (hm.div₀ (by fun_prop : Continuous fun u : ℂ => ((u + 1) * (u + I) * (u - 1))).aestronglyMeasurable) ?_
    filter_upwards [hb] with u hu
    rw [norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hu (inv_nonneg.2 (norm_nonneg _))
  have hK0 := hDi hWm hWb1
  have hK1 : IntegrableOn (fun ζ => W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) unitDiscExterior := by
    refine hDi (hWm.mul continuous_id.aestronglyMeasurable) (b := max Rb 0) ?_
    filter_upwards [hRb, ae_restrict_mem hOm] with ζ h hζ
    have hζ1 : 1 < ‖ζ‖ := hζ
    have hζ0 : 0 < ‖ζ‖ := by linarith
    have h' : ‖R ζ‖ ≤ max Rb 0 := h.trans (le_max_left _ _)
    rw [hWe, norm_mul, norm_div, norm_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h' hζ0.le,
      mul_le_mul_of_nonneg_left (show ‖ζ‖ ≤ ‖ζ‖ ^ 2 by nlinarith) (le_max_right Rb 0)]
  haveI : IsFiniteMeasure (volume.restrict unitDisc) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hS2 : MemLp (unitDisc.indicator S) 2 := by
    refine (memLp_indicator_iff_restrict hDm).2 (MemLp.of_bound hSm (max Sb 0) ?_)
    filter_upwards [hSb] with ζ h using h.trans (le_max_left _ _)
  have hSD : ∀ᵐ ζ ∂(volume.restrict unitDisc), ‖S ζ * ζ‖ ≤ max Sb 0 := by
    filter_upwards [hSb, ae_restrict_mem hDm] with ζ h hζ
    have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
    rw [norm_mul]
    nlinarith [le_max_left Sb 0, le_max_right Sb 0, norm_nonneg (S ζ), norm_nonneg ζ]
  have hL0 := hDi hSm hSb
  have hL1 : IntegrableOn (fun ζ => S ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) unitDisc :=
    hDi (hSm.mul continuous_id.aestronglyMeasurable) hSD
  obtain ⟨K0, hK0d⟩ : ∃ K, K = ∫ ζ in unitDiscExterior, W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) := ⟨_, rfl⟩
  obtain ⟨K1, hK1d⟩ : ∃ K, K = ∫ ζ in unitDiscExterior, W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) := ⟨_, rfl⟩
  obtain ⟨L0, hL0d⟩ : ∃ K, K = ∫ ζ in unitDisc, S ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) := ⟨_, rfl⟩
  obtain ⟨L1, hL1d⟩ : ∃ K, K = ∫ ζ in unitDisc, S ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) := ⟨_, rfl⟩
  -- `γ̇ = y² Γ + P`
  obtain ⟨Γ, hΓe⟩ : ∃ Γ : ℂ → ℂ, Γ = fun y => -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) := ⟨_, rfl⟩
  obtain ⟨P, hPe⟩ : ∃ P : ℂ → ℂ, P = fun y => -(1 / π : ℂ) * (((y + 1) * (y + I) * (y - 1)) * (K1 + y * K0)) := ⟨_, rfl⟩
  have hrel : ∀ y ∈ unitDiscExterior, γ1 y = y ^ 2 * Γ y + P y := by
    intro y hy
    have hRN := d2e_N_int hRm hRb hy
    have hWN := d2e_N_int hWm hWb1 hy
    have hae : ∀ᵐ ζ ∂(volume.restrict unitDiscExterior), R ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) =
        y ^ 2 * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) + ((y + 1) * (y + I) * (y - 1)) * (W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) + ((y + 1) * (y + I) * (y - 1)) * y * (W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) := by
      filter_upwards [ae_restrict_mem hOm, ae_restrict_of_ae ((countable_singleton y).ae_notMem volume)]
        with ζ hζ hζy
      have h1 : ζ - y ≠ 0 := sub_ne_zero.2 fun h => hζy (h ▸ rfl)
      have h2 : ζ ≠ 0 := fun h => by
        have : (1 : ℝ) < ‖ζ‖ := hζ
        rw [h, norm_zero] at this
        linarith
      have h3 := d2e_dn_ne (show 1 < ‖ζ‖ from hζ)
      rw [hWe]
      generalize hDd : ((ζ + 1) * (ζ + I) * (ζ - 1)) = D at h3 ⊢
      field_simp
      first | ring | (rw [← hDd]; ring)
    have j1 : IntegrableOn (fun ζ => y ^ 2 * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) unitDiscExterior := Integrable.const_mul hWN _
    have j2 : IntegrableOn (fun ζ => ((y + 1) * (y + I) * (y - 1)) * (W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) unitDiscExterior := Integrable.const_mul hK1 _
    have j3 : IntegrableOn (fun ζ => ((y + 1) * (y + I) * (y - 1)) * y * (W ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) unitDiscExterior := Integrable.const_mul hK0 _
    have j12 : IntegrableOn (fun ζ => y ^ 2 * (W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) + ((y + 1) * (y + I) * (y - 1)) * (W ζ * ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) unitDiscExterior :=
      Integrable.add j1 j2
    rw [hγ1e, hΓe, hPe]
    simp only []
    rw [integral_congr_ae hae, integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
      integral_const_mul, ← hK0d, ← hK1d]
    ring
  have hPd : ∀ y, HasDerivAt P (-(1 / π : ℂ) * ((3 * y ^ 2 + 2 * I * y - 1) * (K1 + y * K0) + ((y + 1) * (y + I) * (y - 1)) * K0)) y := by
    intro y
    rw [hPe]
    have h := ((((hasDerivAt_id' y).add_const 1).mul ((hasDerivAt_id' y).add_const I)).mul
      ((hasDerivAt_id' y).sub_const 1)).mul (((hasDerivAt_id' y).mul_const K0).const_add K1)
    convert h.const_mul (-(1 / π : ℂ)) using 1
    simp only [Pi.mul_apply]
    ring
  have hP1 : ContDiff ℝ 1 P := by
    rw [hPe]
    fun_prop
  have hy0 : ∀ y ∈ unitDiscExterior, y ≠ 0 := fun y hy h => by
    have : (1 : ℝ) < ‖y‖ := hy
    rw [h, norm_zero] at this
    linarith
  have hΓC : ContDiffOn ℝ 1 Γ unitDiscExterior := by
    have hinv : ContDiffOn ℝ 1 (fun y : ℂ => (y ^ 2)⁻¹) unitDiscExterior :=
      (((differentiableOn_id.pow 2).inv fun y hy => pow_ne_zero 2 (hy0 y hy)).contDiffOn hO :
        ContDiffOn ℂ 1 _ _).restrict_scalars ℝ
    refine ((hγ1.sub hP1.contDiffOn).mul hinv).congr fun y hy => ?_
    have := hy0 y hy
    rw [hrel y hy]
    field_simp
    ring
  -- weak derivatives and weighted bounds
  have hγ2C : ContDiffOn ℝ 1 γ2 unitDiscExterior := (hγ2.contDiffOn hO : ContDiffOn ℂ 1 γ2 _).restrict_scalars ℝ
  have hΓdef : ∀ y ∈ unitDiscExterior, Γ y = -(1 / π : ℂ) * ∫ ζ in unitDiscExterior, W ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) :=
    fun y _ => by rw [hΓe]
  have hγ2def : ∀ y ∈ unitDiscExterior, γ2 y = -(1 / π : ℂ) * ∫ ζ in unitDisc, S ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))) :=
    fun y _ => by rw [hγ2e]
  have hw1 := d2l_weak hOm hWm hWb1 hW2 hK0 hK1 hΓdef hΓC
  have hw2 := d2l_weak hDm hSm hSb hS2 hL0 hL1 hγ2def hγ2C
  rw [← hK0d, ← hK1d] at hw1
  rw [← hL0d, ← hL1d] at hw2
  have hv1 := d2l_wint hOm hWm hWb1 hΓdef hΓC.continuousOn
  have hv2 := d2l_wint hDm hSm hSb hγ2def hγ2C.continuousOn
  obtain ⟨H1, hH1e⟩ : ∃ H, H = hilbertH (unitDiscExterior.indicator W) := ⟨_, rfl⟩
  obtain ⟨H2, hH2e⟩ : ∃ H, H = hilbertH (unitDisc.indicator S) := ⟨_, rfl⟩
  rw [← hH1e] at hw1
  rw [← hH2e] at hw2
  have hH1 : MemLp H1 2 := hH1e ▸ (hilbertH_memLp_two hW2).1
  have hH2 : MemLp H2 2 := hH2e ▸ (hilbertH_memLp_two hS2).1
  have hwt : ∀ k : ℕ, 2 ≤ k → MemLp (fun y : ℂ => (‖y‖ ^ k)⁻¹) 2 (volume.restrict unitDiscExterior) := fun k hk => by
    have hm : AEStronglyMeasurable (fun y : ℂ => (‖y‖ ^ k)⁻¹) (volume.restrict unitDiscExterior) :=
      (continuous_norm.pow k).continuousOn.inv₀ (fun y hy => pow_ne_zero k (lt_trans one_pos hy).ne')
        |>.aestronglyMeasurable hOm
    refine (memLp_two_iff_integrable_sq hm).2 ((d2l_powint (k := 2 * k) (by omega)).congr ?_)
    filter_upwards with y
    show (‖y‖ ^ (2 * k))⁻¹ = ((‖y‖ ^ k)⁻¹) ^ 2
    rw [inv_pow, ← pow_mul, mul_comm k 2]
  have hI1 : IntegrableOn (fun y => (‖y‖ ^ 4)⁻¹ * ‖H1 y‖) unitDiscExterior :=
    (hwt 4 (by norm_num)).integrable_mul (hH1.norm.restrict unitDiscExterior)
  have hI2 : IntegrableOn (fun y => (‖y‖ ^ 6)⁻¹ * ‖H2 y‖) unitDiscExterior :=
    (hwt 6 (by norm_num)).integrable_mul (hH2.norm.restrict unitDiscExterior)
  have hI7 : IntegrableOn (fun y => (‖y‖ ^ 7)⁻¹ * ‖γ2 y‖) unitDiscExterior := by
    refine hv2.mono' ((((continuous_norm.pow 7).continuousOn.inv₀ (fun y hy =>
      pow_ne_zero 7 (lt_trans one_pos hy).ne')).mul hγ2C.continuousOn.norm).aestronglyMeasurable hOm) ?_
    filter_upwards [ae_restrict_mem hOm] with y hy
    have hy1 : 1 < ‖y‖ := hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (pow_le_pow_right₀ hy1.le (by norm_num)))
      (norm_nonneg _)
  -- regularity and the product rule
  have hAC : ContDiffOn ℝ 1 A unitDiscExterior := (hAd.contDiffOn hO : ContDiffOn ℂ 1 A _).restrict_scalars ℝ
  have hdzA : ∀ y ∈ unitDiscExterior, DifferentiableAt ℂ A y := fun y hy => hAd.differentiableAt (hO.mem_nhds hy)
  have hdP : ∀ {γ : ℂ → ℂ}, ContDiffOn ℝ 1 γ unitDiscExterior → ∀ y ∈ unitDiscExterior,
      dz (fun w => A w * γ w) y = A y * dz γ y + γ y * deriv A y := fun hγ y hy => by
    rw [dz_mul ((hdzA y hy).restrictScalars ℝ)
      ((hγ.differentiableOn one_ne_zero y hy).differentiableAt (hO.mem_nhds hy)), dz_eq_deriv (hdzA y hy)]
  have hΛc : ContinuousOn (fun z => conj (A z) * dz (fun y => A y * γ1 y) z + A z * conj (dz (fun y => A y * γ2 y) z))
      unitDiscExterior :=
    ((continuous_conj.comp_continuousOn hAC.continuousOn).mul (d2l_dz_cont (hAC.mul hγ1))).add
      (hAC.continuousOn.mul (continuous_conj.comp_continuousOn (d2l_dz_cont (hAC.mul hγ2C))))
  have hdγ1 : ∀ y ∈ unitDiscExterior, dz γ1 y = y ^ 2 * dz Γ y + 2 * y * Γ y +
      -(1 / π : ℂ) * ((3 * y ^ 2 + 2 * I * y - 1) * (K1 + y * K0) + ((y + 1) * (y + I) * (y - 1)) * K0) := by
    intro y hy
    have hev : γ1 =ᶠ[𝓝 y] fun w => w ^ 2 * Γ w + P w := Filter.eventuallyEq_of_mem (hO.mem_nhds hy) hrel
    have hΓd := (hΓC.differentiableOn one_ne_zero y hy).differentiableAt (hO.mem_nhds hy)
    have hsqc : DifferentiableAt ℂ (fun w : ℂ => w ^ 2) y := differentiableAt_id.pow 2
    have hsq := hsqc.restrictScalars ℝ
    have hd2 : deriv (fun w : ℂ => w ^ 2) y = 2 * y := by
      rw [(hasDerivAt_pow 2 y).deriv]
      norm_num
    have e : dz γ1 y = dz (fun w => w ^ 2 * Γ w + P w) y := by
      show (fderiv ℝ γ1 y 1 - I * fderiv ℝ γ1 y I) / 2 =
        (fderiv ℝ (fun w => w ^ 2 * Γ w + P w) y 1 - I * fderiv ℝ (fun w => w ^ 2 * Γ w + P w) y I) / 2
      rw [hev.fderiv_eq]
    have hadd : dz (fun w => w ^ 2 * Γ w + P w) y = dz (fun w => w ^ 2 * Γ w) y + dz P y := by
      have hd1 : DifferentiableAt ℝ (fun w => w ^ 2 * Γ w) y := hsq.mul hΓd
      show (fderiv ℝ (fun w => w ^ 2 * Γ w + P w) y 1 - I * fderiv ℝ (fun w => w ^ 2 * Γ w + P w) y I) / 2 =
        (fderiv ℝ (fun w => w ^ 2 * Γ w) y 1 - I * fderiv ℝ (fun w => w ^ 2 * Γ w) y I) / 2 +
          (fderiv ℝ P y 1 - I * fderiv ℝ P y I) / 2
      rw [fderiv_fun_add hd1 ((hPd y).differentiableAt.restrictScalars ℝ)]
      simp only [ContinuousLinearMap.add_apply]
      ring
    rw [e, hadd, dz_mul hsq hΓd,
      dz_eq_deriv hsqc, dz_eq_deriv (hPd y).differentiableAt, (hPd y).deriv, hd2]
    ring
  -- polynomial bounds
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = ‖K1‖ + 3 * ‖K0‖ + ‖L1‖ + 3 * ‖L0‖ := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hpb : ∀ y : ℂ, 1 < ‖y‖ → ∀ c0 c1 : ℂ, ‖c1‖ + 3 * ‖c0‖ ≤ κ →
      ‖(1 / π : ℂ) * (c1 + (2 * y + I) * c0)‖ ≤ κ * ‖y‖ := fun y hy c0 c1 hc => by
    have h2 : ‖2 * y + I‖ ≤ 3 * ‖y‖ := by
      have := norm_add_le (2 * y) I
      rw [norm_mul, Complex.norm_I, show ‖(2 : ℂ)‖ = 2 by norm_num] at this
      linarith
    rw [norm_mul]
    calc ‖(1 / π : ℂ)‖ * ‖c1 + (2 * y + I) * c0‖ ≤ 1 * (‖c1‖ * ‖y‖ + 3 * ‖y‖ * ‖c0‖) := by
          refine mul_le_mul hπ1 ((norm_add_le _ _).trans (add_le_add (by nlinarith [norm_nonneg c1]) ?_))
            (norm_nonneg _) zero_le_one
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ κ * ‖y‖ := by nlinarith [norm_nonneg y, norm_nonneg c0]
  have hDy : ∀ y : ℂ, 1 < ‖y‖ → ‖((y + 1) * (y + I) * (y - 1))‖ ≤ 8 * ‖y‖ ^ 3 := fun y hy1 => by
    have h1 : ‖y + 1‖ ≤ 2 * ‖y‖ := by
      have := norm_add_le y 1
      rw [norm_one] at this
      linarith
    have h2 : ‖y + I‖ ≤ 2 * ‖y‖ := by
      have := norm_add_le y I
      rw [Complex.norm_I] at this
      linarith
    have h3 : ‖y - 1‖ ≤ 2 * ‖y‖ := by
      have := norm_sub_le y 1
      rw [norm_one] at this
      linarith
    rw [norm_mul, norm_mul]
    calc ‖y + 1‖ * ‖y + I‖ * ‖y - 1‖ ≤ (2 * ‖y‖) * (2 * ‖y‖) * (2 * ‖y‖) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)
      _ = 8 * ‖y‖ ^ 3 := by ring
  have hKy : ∀ y : ℂ, 1 < ‖y‖ → ‖K1 + y * K0‖ ≤ κ * ‖y‖ := fun y hy => by
    have := norm_add_le K1 (y * K0)
    rw [norm_mul] at this
    rw [hκ]
    nlinarith [norm_nonneg K1, norm_nonneg K0, norm_nonneg L1, norm_nonneg L0]
  have hPb : ∀ y : ℂ, 1 < ‖y‖ → ‖P y‖ ≤ 8 * κ * ‖y‖ ^ 4 := fun y hy => by
    rw [hPe]
    show ‖-(1 / π : ℂ) * (((y + 1) * (y + I) * (y - 1)) * (K1 + y * K0))‖ ≤ _
    rw [norm_mul, norm_neg, norm_mul]
    calc ‖(1 / π : ℂ)‖ * (‖((y + 1) * (y + I) * (y - 1))‖ * ‖K1 + y * K0‖) ≤ 1 * (8 * ‖y‖ ^ 3 * (κ * ‖y‖)) :=
          mul_le_mul hπ1 (mul_le_mul (hDy y hy) (hKy y hy) (norm_nonneg _) (by positivity)) (by positivity)
            zero_le_one
      _ = 8 * κ * ‖y‖ ^ 4 := by ring
  have hPdb : ∀ y : ℂ, 1 < ‖y‖ →
      ‖-(1 / π : ℂ) * ((3 * y ^ 2 + 2 * I * y - 1) * (K1 + y * K0) + ((y + 1) * (y + I) * (y - 1)) * K0)‖ ≤ 14 * κ * ‖y‖ ^ 3 := fun y hy => by
    have h3 : ‖3 * y ^ 2 + 2 * I * y - 1‖ ≤ 6 * ‖y‖ ^ 2 := by
      have e1 := norm_sub_le (3 * y ^ 2 + 2 * I * y) 1
      have e2 := norm_add_le (3 * y ^ 2) (2 * I * y)
      rw [norm_mul, norm_pow, show ‖(3 : ℂ)‖ = 3 by norm_num, norm_mul, norm_mul, Complex.norm_I,
        show ‖(2 : ℂ)‖ = 2 by norm_num] at e2
      rw [norm_one] at e1
      nlinarith
    have hK0κ : ‖K0‖ ≤ κ := by rw [hκ]; nlinarith [norm_nonneg K1, norm_nonneg L1, norm_nonneg L0]
    rw [norm_mul, norm_neg]
    calc ‖(1 / π : ℂ)‖ * ‖(3 * y ^ 2 + 2 * I * y - 1) * (K1 + y * K0) + ((y + 1) * (y + I) * (y - 1)) * K0‖
        ≤ 1 * (6 * ‖y‖ ^ 2 * (κ * ‖y‖) + 8 * ‖y‖ ^ 3 * κ) := by
          refine mul_le_mul hπ1 ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _) zero_le_one
          · rw [norm_mul]
            exact mul_le_mul h3 (hKy y hy) (norm_nonneg _) (by positivity)
          · rw [norm_mul]
            exact mul_le_mul (hDy y hy) hK0κ (norm_nonneg _) (by positivity)
      _ = 14 * κ * ‖y‖ ^ 3 := by ring
  -- the majorant
  have p3 := d2l_powint (k := 3) le_rfl
  have p5 := d2l_powint (k := 5) (by norm_num)
  have hsum : IntegrableOn (fun y => CA ^ 2 * ((‖y‖ ^ 4)⁻¹ * ‖H1 y‖ + κ * (‖y‖ ^ 3)⁻¹ + 2 * ((‖y‖ ^ 5)⁻¹ * ‖Γ y‖) +
      14 * κ * (‖y‖ ^ 3)⁻¹) + CA * CA' * ((‖y‖ ^ 5)⁻¹ * ‖Γ y‖ + 8 * κ * (‖y‖ ^ 3)⁻¹) +
      CA ^ 2 * ((‖y‖ ^ 6)⁻¹ * ‖H2 y‖ + κ * (‖y‖ ^ 5)⁻¹) + CA * CA' * ((‖y‖ ^ 7)⁻¹ * ‖γ2 y‖)) unitDiscExterior :=
    ((((((hI1.add (p3.const_mul κ)).add (hv1.const_mul 2)).add (p3.const_mul (14 * κ))).const_mul (CA ^ 2)).add
      ((hv1.add (p3.const_mul (8 * κ))).const_mul (CA * CA'))).add
      ((hI2.add (p5.const_mul κ)).const_mul (CA ^ 2))).add (hI7.const_mul (CA * CA'))
  refine hsum.mono' (hΛc.aestronglyMeasurable hOm) ?_
  filter_upwards [hw1, hw2, ae_restrict_mem hOm] with y h1 h2 hy
  have hy1 : 1 < ‖y‖ := hy
  have ha0 : 0 < ‖y‖ := by linarith
  have hA0 := hA y hy
  have hA'0 := hA' y hy
  have hdz1 : ‖dz γ1 y‖ ≤ ‖y‖ ^ 2 * (‖H1 y‖ + κ * ‖y‖) + 2 * ‖y‖ * ‖Γ y‖ + 14 * κ * ‖y‖ ^ 3 := by
    rw [hdγ1 y hy, h1]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (hPdb y hy1))
    · rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl
        (hpb y hy1 K0 K1 (by rw [hκ]; nlinarith [norm_nonneg L1, norm_nonneg L0])))) (by positivity)
    · rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have hg1 : ‖γ1 y‖ ≤ ‖y‖ ^ 2 * ‖Γ y‖ + 8 * κ * ‖y‖ ^ 4 := by
    rw [hrel y hy]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hPb y hy1))
    rw [norm_mul, norm_pow]
  have hdz2 : ‖dz γ2 y‖ ≤ ‖H2 y‖ + κ * ‖y‖ := by
    rw [h2]
    exact (norm_add_le _ _).trans (add_le_add le_rfl
      (hpb y hy1 L0 L1 (by rw [hκ]; nlinarith [norm_nonneg K1, norm_nonneg K0])))
  rw [hdP hγ1 y hy, hdP hγ2C y hy]
  calc ‖conj (A y) * (A y * dz γ1 y + γ1 y * deriv A y) + A y * conj (A y * dz γ2 y + γ2 y * deriv A y)‖
      ≤ ‖A y‖ * (‖A y‖ * ‖dz γ1 y‖ + ‖γ1 y‖ * ‖deriv A y‖) +
        ‖A y‖ * (‖A y‖ * ‖dz γ2 y‖ + ‖γ2 y‖ * ‖deriv A y‖) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, RCLike.norm_conj]
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (norm_nonneg _)
          rw [norm_mul, norm_mul]
        · rw [norm_mul, RCLike.norm_conj]
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (norm_nonneg _)
          rw [norm_mul, norm_mul]
    _ ≤ (CA * (‖y‖ ^ 3)⁻¹) * ((CA * (‖y‖ ^ 3)⁻¹) * (‖y‖ ^ 2 * (‖H1 y‖ + κ * ‖y‖) + 2 * ‖y‖ * ‖Γ y‖ +
          14 * κ * ‖y‖ ^ 3) + (‖y‖ ^ 2 * ‖Γ y‖ + 8 * κ * ‖y‖ ^ 4) * (CA' * (‖y‖ ^ 4)⁻¹)) +
        (CA * (‖y‖ ^ 3)⁻¹) * ((CA * (‖y‖ ^ 3)⁻¹) * (‖H2 y‖ + κ * ‖y‖) + ‖γ2 y‖ * (CA' * (‖y‖ ^ 4)⁻¹)) := by
        gcongr
    _ = _ := by
        field_simp
        ring

/-- [Λ-INT helper] `m = 0` satisfies the `m`-hypotheses of the D-lemmas (`0 ∈ harmonicL2`, witness `ψ = 0`). -/
theorem d2l_m0 : (0 : ℂ → ℂ) ∈ harmonicL2 unitDiscExterior ∧
    ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf (0 : ℂ → ℂ) = Lambda (A2toAInf ψ) := by
  refine ⟨⟨0, differentiableOn_const 0, fun z _ => by simp, ?_⟩, 0, ⟨0, fun z hz => ?_⟩, ?_⟩
  · show (∫⁻ z in unitDiscExterior, (‖(0 : ℂ → ℂ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) ^ (1 / 2 : ℝ) < ∞
    simp
  · have h := A2.toFun_add (D := unitDisc) isOpen_ball (fun z hz => (mem_ball_zero_iff.1 hz).ne) 0 0 hz
    rw [add_zero, Pi.add_apply] at h
    rw [Polynomial.eval_zero]
    linear_combination -h
  · rw [A2toAInf_zero, show (0 : AInf unitDisc) = (0 : ℂ) • (0 : AInf unitDisc) from (zero_smul ℂ _).symm,
      Lambda_smul, zero_smul]
    unfold toLinf
    split_ifs with h
    · exact MemLp.toLp_zero h
    · rfl

/-- [Λ-INT helper, export] The holomorphic extensions of the welding pair at `ν₀ = a * κ` across `𝕊¹` (`s3g_D_ext` at
`t = 0`, with `m = 0`): `G` on `ρ < ‖z‖` extends `𝗀`, `F` on `‖z‖ < R` extends `𝖿`. -/
theorem d2l_ext {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ)) :
    (∃ ρ < 1, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖} ∧ InjOn G {z : ℂ | ρ < ‖z‖} ∧
      (∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0) ∧ EqOn G (gsans (beltramiMul a κ)) unitDiscExterior) ∧
    ∃ R > 1, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball 0 R) ∧ InjOn F (ball 0 R) ∧
      (∀ z ∈ ball (0 : ℂ) R, deriv F z ≠ 0) ∧ EqOn F (fsans (beltramiMul a κ)) unitDisc := by
  obtain ⟨hm0, hmD0⟩ := d2l_m0
  obtain ⟨r, hr, ρ, hρ, R0, hR0, F, G, H, -, -, -, -, -, -, -, ht⟩ := s3g_D_ext hκ hκD ha has haL haD hm0 hmD0
  obtain ⟨⟨hFd, hFi, hFd', hFg⟩, ⟨hGd, hGi, hGd', hGg⟩, -⟩ := ht 0 (mem_ball_self hr)
  simp only [zero_smul, add_zero] at hFg hGg
  exact ⟨⟨ρ, hρ, G 0, hGd, hGi, hGd', hGg⟩, R0, hR0, F 0, hFd, hFi, hFd', hFg⟩

/-- [Λ-INT helper, export] `R = R(m, a)` is measurable and bounded on `𝔻*`. -/
theorem d2l_R_data {a : LinfStar} (has : ‖a‖ < delta0) (m : ℂ → ℂ) :
    AEStronglyMeasurable (RnmFun (toLinf m) a) (volume.restrict unitDiscExterior) ∧
      ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖RnmFun (toLinf m) a u‖ ≤ (1 / (1 - ‖a‖ ^ 2)) * ‖toLinf m‖ := by
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.2 (has.trans delta0_bounds.2)
  exact ⟨(bc_Rnm_memLp haB (toLinf m)).aestronglyMeasurable,
    bc_invFun_pullback_ae haB (bc_Rnm_integrand_bound haB (toLinf m))⟩

/-- [Λ-INT helper, export] **Decay of `𝒜 = 𝒜(𝗀)` on `𝔻*`**: `𝒜` is holomorphic, `|𝒜(z)| ≤ C|z|⁻³` and
`|𝒜'(z)| ≤ C'|z|⁻⁴` (`s3g_inf` at `∞`, compactness of `𝒜(G)` on `1 ≤ |z| ≤ 4`, Cauchy estimates). -/
theorem d2l_A_bounds {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ)) :
    DifferentiableOn ℂ (preSchwarzian (gsans (beltramiMul a κ))) unitDiscExterior ∧
      ∃ CA CA' : ℝ, 0 ≤ CA ∧ 0 ≤ CA' ∧
        (∀ z ∈ unitDiscExterior, ‖preSchwarzian (gsans (beltramiMul a κ)) z‖ ≤ CA * (‖z‖ ^ 3)⁻¹) ∧
        ∀ z ∈ unitDiscExterior, ‖deriv (preSchwarzian (gsans (beltramiMul a κ))) z‖ ≤ CA' * (‖z‖ ^ 4)⁻¹ := by
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.2 (has.trans delta0_bounds.2)
  have hμ : beltramiMul a (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  obtain ⟨⟨ρ, hρ, G, hGd, hGi, hGd', hGg⟩, -⟩ := d2l_ext hκ hκD ha has haL haD
  have hO : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hsub : unitDiscExterior ⊆ {z : ℂ | ρ < ‖z‖} := fun z hz => lt_trans hρ hz
  -- `𝒜 = 𝒜(G)` on `𝔻*`, holomorphic
  have hPG : DifferentiableOn ℂ (preSchwarzian G) {z : ℂ | ρ < ‖z‖} :=
    ((hGd.deriv hO).deriv hO).div (hGd.deriv hO) hGd'
  have hAG : ∀ z ∈ unitDiscExterior, preSchwarzian (gsans (beltramiMul a κ)) =ᶠ[𝓝 z] preSchwarzian G :=
    fun z hz => by
      filter_upwards [hE.mem_nhds hz] with w hw
      exact s3g_presch_congr (hGg.eventuallyEq_of_mem (hE.mem_nhds hw)).symm
  have hAd : DifferentiableOn ℂ (preSchwarzian (gsans (beltramiMul a κ))) unitDiscExterior := fun z hz =>
    (((hPG z (hsub hz)).differentiableAt (hO.mem_nhds (hsub hz))).congr_of_eventuallyEq (hAG z hz)).differentiableWithinAt
  -- bounds on the compact annulus `1 ≤ ‖z‖ ≤ 4`
  have hK : IsCompact (closedBall (0 : ℂ) 4 ∩ {z : ℂ | 1 ≤ ‖z‖}) :=
    (isCompact_closedBall 0 4).inter_right (isClosed_le continuous_const continuous_norm)
  have hKs : closedBall (0 : ℂ) 4 ∩ {z : ℂ | 1 ≤ ‖z‖} ⊆ {z : ℂ | ρ < ‖z‖} := fun z hz =>
    show ρ < ‖z‖ from lt_of_lt_of_le hρ hz.2
  obtain ⟨MA, hMA⟩ := hK.exists_bound_of_continuousOn (hPG.continuousOn.mono hKs)
  obtain ⟨MA', hMA'⟩ := hK.exists_bound_of_continuousOn ((hPG.deriv hO).continuousOn.mono hKs)
  have hKm : ∀ z ∈ unitDiscExterior, ‖z‖ ≤ 4 → z ∈ closedBall (0 : ℂ) 4 ∩ {z : ℂ | 1 ≤ ‖z‖} :=
    fun z hz h4 => ⟨mem_closedBall_zero_iff.2 h4, show (1 : ℝ) ≤ ‖z‖ from le_of_lt hz⟩
  -- decay at `∞` (`s3g_inf` for the constant family)
  obtain ⟨Ψ, hΨc, hΨ⟩ := s3g_inf (ν := fun _ => beltramiMul a κ) (r := 1) (fun _ _ => hμ) (fun _ _ => analyticAt_const)
  have hΨ0 : ContinuousOn (fun s : ℂ => Ψ (0, s)) (closedBall 0 (1 / 2)) :=
    hΨc.continuousOn.comp (by fun_prop : Continuous fun s : ℂ => ((0 : ℂ), s)).continuousOn fun s hs =>
      ⟨mem_ball_self one_pos, mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hs) (by norm_num))⟩
  obtain ⟨MΨ, hMΨ⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn hΨ0
  obtain ⟨CA, hCAd⟩ : ∃ C : ℝ, C = max (64 * max MA 0) (max MΨ 0) := ⟨_, rfl⟩
  have hCA : 0 ≤ CA := by rw [hCAd]; positivity
  have hA : ∀ z ∈ unitDiscExterior, ‖preSchwarzian (gsans (beltramiMul a κ)) z‖ ≤ CA * (‖z‖ ^ 3)⁻¹ := by
    intro z hz
    have hz1 : 1 < ‖z‖ := hz
    by_cases h4 : ‖z‖ ≤ 4
    · rw [(hAG z hz).eq_of_nhds]
      have h64 : 1 ≤ 64 * (‖z‖ ^ 3)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
        nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ ‖z‖) h4 3]
      calc ‖preSchwarzian G z‖ ≤ max MA 0 := (hMA z (hKm z hz h4)).trans (le_max_left _ _)
        _ ≤ max MA 0 * (64 * (‖z‖ ^ 3)⁻¹) := le_mul_of_one_le_right (le_max_right _ _) h64
        _ = 64 * max MA 0 * (‖z‖ ^ 3)⁻¹ := by ring
        _ ≤ CA * (‖z‖ ^ 3)⁻¹ := by
            rw [hCAd]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · push_neg at h4
      have hzi : z⁻¹ ∈ closedBall (0 : ℂ) (1 / 2) := by
        rw [mem_closedBall_zero_iff, norm_inv]
        exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
      rw [hΨ 0 (mem_ball_self one_pos) z hz, norm_mul, norm_neg, norm_pow, norm_inv, inv_pow, mul_comm]
      exact mul_le_mul ((hMΨ _ hzi).trans ((le_max_left _ _).trans (by rw [hCAd]; exact le_max_right _ _)))
        le_rfl (by positivity) hCA
  obtain ⟨CA', hCA'd⟩ : ∃ C : ℝ, C = max (256 * max MA' 0) (16 * CA) := ⟨_, rfl⟩
  have hCA' : 0 ≤ CA' := by rw [hCA'd]; positivity
  have hA' : ∀ z ∈ unitDiscExterior, ‖deriv (preSchwarzian (gsans (beltramiMul a κ))) z‖ ≤ CA' * (‖z‖ ^ 4)⁻¹ := by
    intro z hz
    have hz1 : 1 < ‖z‖ := hz
    by_cases h4 : ‖z‖ ≤ 4
    · rw [(hAG z hz).deriv_eq]
      have h256 : 1 ≤ 256 * (‖z‖ ^ 4)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
        nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ ‖z‖) h4 4]
      calc ‖deriv (preSchwarzian G) z‖ ≤ max MA' 0 := (hMA' z (hKm z hz h4)).trans (le_max_left _ _)
        _ ≤ max MA' 0 * (256 * (‖z‖ ^ 4)⁻¹) := le_mul_of_one_le_right (le_max_right _ _) h256
        _ = 256 * max MA' 0 * (‖z‖ ^ 4)⁻¹ := by ring
        _ ≤ CA' * (‖z‖ ^ 4)⁻¹ := by
            rw [hCA'd]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · push_neg at h4
      have hr2 : 0 < ‖z‖ / 2 := by positivity
      have hcb : closedBall z (‖z‖ / 2) ⊆ unitDiscExterior := fun w hw => by
        have h1 := mem_closedBall_iff_norm.1 hw
        have h2 := norm_sub_norm_le z w
        rw [norm_sub_rev] at h2
        show 1 < ‖w‖
        linarith
      have hdc : DiffContOnCl ℂ (preSchwarzian (gsans (beltramiMul a κ))) (ball z (‖z‖ / 2)) := by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball _ hr2.ne']
        exact hAd.mono hcb
      have hsph : ∀ w ∈ sphere z (‖z‖ / 2), ‖preSchwarzian (gsans (beltramiMul a κ)) w‖ ≤ 8 * CA * (‖z‖ ^ 3)⁻¹ := by
        intro w hw
        have hw1 := mem_sphere_iff_norm.1 hw
        have h2 := norm_sub_norm_le z w
        rw [norm_sub_rev] at h2
        have hwz : ‖z‖ / 2 ≤ ‖w‖ := by linarith
        calc ‖preSchwarzian (gsans (beltramiMul a κ)) w‖ ≤ CA * (‖w‖ ^ 3)⁻¹ :=
              hA w (hcb (sphere_subset_closedBall hw))
          _ ≤ CA * (((‖z‖ / 2)) ^ 3)⁻¹ :=
              mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ hr2.le hwz 3)) hCA
          _ = 8 * CA * (‖z‖ ^ 3)⁻¹ := by
              field_simp
              ring
      calc ‖deriv (preSchwarzian (gsans (beltramiMul a κ))) z‖ ≤ 8 * CA * (‖z‖ ^ 3)⁻¹ / (‖z‖ / 2) :=
            Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr2 hdc hsph
        _ = 16 * CA * (‖z‖ ^ 4)⁻¹ := by
            field_simp
            ring
        _ ≤ CA' * (‖z‖ ^ 4)⁻¹ := by
            rw [hCA'd]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  exact ⟨hAd, CA, CA', hCA, hCA', hA, hA'⟩

/-- **(Λ-INT)** The Lie-term integrand of (Λ) is integrable on `𝔻*`. -/
theorem s3d_D2_lambda_int {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    Integrable (fun z : ℂ => (conj (preSchwarzian (gsans (beltramiMul a κ)) z) * dz (fun y : ℂ => preSchwarzian (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z +
      preSchwarzian (gsans (beltramiMul a κ)) z * conj (dz (fun y : ℂ => preSchwarzian (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z)))
      (volume.restrict unitDiscExterior) := by
  have hd := delta0_bounds
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.2 (has.trans hd.2)
  obtain ⟨⟨ρ, hρ, G, hGd, hGi, hGd', hGg⟩, -⟩ := d2l_ext hκ hκD ha has haL haD
  obtain ⟨hRm, hRb⟩ := d2l_R_data has m
  obtain ⟨hSm, hSb⟩ := d2e_S_ae hRm hRb
  obtain ⟨hgd, hg'd, hgi, hdd, hg'⟩ := d2e_basic hρ hGd hGi hGd' hGg
  obtain ⟨hAd, CA, CA', hCA, hCA', hA, hA'⟩ := d2l_A_bounds hκ hκD ha has haL haD
  -- `γ̇₂` is holomorphic on `𝔻*` (from E1)
  have hη2 := (s3d_D2_eta hκ hκD ha has haL haD hm hmD).2
  have hγ2 : DifferentiableOn ℂ (fun y : ℂ => -(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) *
      ζ ^ 2 / conj ζ ^ 2 * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) unitDiscExterior := by
    refine ((((differentiableOn_const (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) *
      ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)))).mul
      (hgd.pow 2)).div hg'd hg').sub hη2).congr fun y hy => ?_
    have h3 := hg' y hy
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    beta_reduce
    generalize (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
      (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) = J
    generalize (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) *
      ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) = C
    field_simp
    ring
  exact d2l_main (S := fun ζ => conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2) hCA hCA' hAd hA hA'
    hRm hRb hSm hSb (s3d_D2_gd1_C1 hκ hκD ha has haL haD hm hmD) hγ2

/-- **(D2)** The exterior area term, welded (TT's `I₃ + I₄`): `∫_{𝔻*} |𝒜(g_t)|² = ∫_{𝔻*} |C_t|² (1 - |μ(γ̂_t)|²)`,
`C_t = 𝒜(g_t) ∘ γ̂_t · ∂γ̂_t = 𝒜(W_t) ∘ g · g' + 𝒜(g) - 𝒜(γ̂_t)`, so (pole terms cancel at `∞`)
`Ċ = g' (-(2/π)∫ R g'²/(g - g(z))³) + (2/π)∫ R/(ζ - z)³ + 2 c₂ (g'/b - 1)`,
`∂_t̄ C = (2/π)∫_𝔻 R̃/(ζ - z)³ + 2 c₂' (g'/b - 1)`. The `t`-kernel `g'(ζ)²g'(z)/(g(ζ) - g(z))³ - 1/(ζ - z)³ = (𝒜(g)(z)/2)(ζ - z)⁻² + O(|ζ - z|⁻¹)` is only a principal
value; it is written as `½ ∂_z Q`, `Q(ζ, z) = g'(ζ)²/(g(ζ) - g(z))² - 1/(ζ - z)² = O(𝒜(g)/|ζ - z|)` (integrable), with
the Wirtinger `∂_z` outside. `z ↦ ∫ R Q` is ℝ-differentiable on `𝔻*` (`R` smooth inside `𝔻*`; PV derivative); the
proof of D2 must establish this, it is not assumed.
At `κ = 0, a = 0` (`g = id`, `𝒜(g) = 0`): both sides are `0`; `Ċ = 0` (`Ẇ - γ̇` is linear) and
`∂_z ∂_t̄ C = (6/π) ∫_{𝔻*} conj m/(1 - w̄ z)⁴ = s4pv_variation` (welded Schwarzian `= C'` to first order). -/
theorem s3d_D2 {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    DifferentiableAt ℝ (fun t : ℂ =>
      ((∫ z in unitDiscExterior, ‖preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z‖ ^ 2 : ℝ) : ℂ)) 0 ∧
    dz (fun t : ℂ =>
      ((∫ z in unitDiscExterior, ‖preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z‖ ^ 2 : ℝ) : ℂ)) 0 =
      ∫ z in unitDiscExterior,
        (conj (preSchwarzian (gsans (beltramiMul a κ)) z) *
            (-(1 / π : ℂ) * dz (fun y : ℂ => ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
                (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - gsans (beltramiMul a κ) y) ^ 2 -
                  1 / (ζ - y) ^ 2)) z +
              2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) *
                (deriv (gsans (beltramiMul a κ)) z / derivAtInfty (gsans (beltramiMul a κ)) - 1)) +
          preSchwarzian (gsans (beltramiMul a κ)) z *
            conj ((2 / π : ℂ) * (∫ ζ in unitDisc,
                conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / (ζ - z) ^ 3) +
              2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 /
                ((ζ + 1) * (ζ + I) * (ζ - 1))) *
                (deriv (gsans (beltramiMul a κ)) z / derivAtInfty (gsans (beltramiMul a κ)) - 1))) := by
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hdom := s3d_g_dom_proof hκ hκD ha has haL haD hm hmD
  have h0 : (fun t : ℂ => fun z : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) 0 =
      preSchwarzian (gsans (beltramiMul a κ)) := by
    funext z
    simp only [zero_smul, add_zero]
  obtain ⟨hdiff, hdz⟩ := s3d_l2sq_dom hEm h0 hdom
  obtain ⟨-, hm1, hm2⟩ := s3x_dom_data hEm hdom
  have hA2 : MemLp (preSchwarzian (gsans (beltramiMul a κ))) 2 (volume.restrict unitDiscExterior) := by
    obtain ⟨r, hr, G, hG, hb⟩ := hdom
    obtain ⟨hmeas, hpt⟩ := hb 0 (mem_ball_self hr)
    simp only [zero_smul, add_zero] at hmeas
    refine hG.of_le hmeas ?_
    filter_upwards [ae_restrict_mem hEm] with z hz
    have := (hpt z hz).2.2
    simp only [zero_smul, add_zero] at this
    exact this.trans (Real.le_norm_self _)
  have hfirst : Integrable (fun z => preSchwarzian (gsans (beltramiMul a κ)) z *
      conj (dzbar (fun s => preSchwarzian (gsans (beltramiMul (a + s • toLinf m) κ)) z) 0) +
      conj (preSchwarzian (gsans (beltramiMul a κ)) z) *
        dz (fun s => preSchwarzian (gsans (beltramiMul (a + s • toLinf m) κ)) z) 0)
      (volume.restrict unitDiscExterior) :=
    (hA2.integrable_mul hm2.star).add (hA2.star.integrable_mul hm1)
  have hE2 := s3d_D2_unwelded hκ hκD ha has haL haD hm hmD
  have hP := s3d_D2_pointwise hκ hκD ha has haL haD hm hmD
  have hΛ := s3d_D2_lambda hκ hκD ha has haL haD hm hmD
  have hΛi := s3d_D2_lambda_int hκ hκD ha has haL haD hm hmD
  refine ⟨hdiff, ?_⟩
  rw [hdz]
  symm
  calc _ = ∫ z in unitDiscExterior, ((preSchwarzian (gsans (beltramiMul a κ)) z * conj (dzbar (fun s => preSchwarzian (gsans (beltramiMul (a + s • toLinf m) κ)) z) 0) + conj (preSchwarzian (gsans (beltramiMul a κ)) z) * dz (fun s => preSchwarzian (gsans (beltramiMul (a + s • toLinf m) κ)) z) 0) + ((conj (preSchwarzian (gsans (beltramiMul a κ)) z) * dz (fun y : ℂ => preSchwarzian (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z +
      preSchwarzian (gsans (beltramiMul a κ)) z * conj (dz (fun y : ℂ => preSchwarzian (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z)))) := integral_congr_ae ?_
    _ = (∫ z in unitDiscExterior, (preSchwarzian (gsans (beltramiMul a κ)) z * conj (dzbar (fun s => preSchwarzian (gsans (beltramiMul (a + s • toLinf m) κ)) z) 0) + conj (preSchwarzian (gsans (beltramiMul a κ)) z) * dz (fun s => preSchwarzian (gsans (beltramiMul (a + s • toLinf m) κ)) z) 0)) + ∫ z in unitDiscExterior, ((conj (preSchwarzian (gsans (beltramiMul a κ)) z) * dz (fun y : ℂ => preSchwarzian (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z +
      preSchwarzian (gsans (beltramiMul a κ)) z * conj (dz (fun y : ℂ => preSchwarzian (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) z))) := integral_add hfirst hΛi
    _ = _ := by rw [hΛ, add_zero]
  filter_upwards [ae_restrict_mem hEm] with z hz
  obtain ⟨-, e1, e2⟩ := hE2 z hz
  obtain ⟨-, p1, p2⟩ := hP z hz
  rw [e1, e2, ← p1, ← p2, map_add]
  ring

end TakhtajanTeo.Ch2
