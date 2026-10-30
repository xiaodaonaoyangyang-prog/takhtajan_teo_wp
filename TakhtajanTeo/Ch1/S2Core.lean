import TakhtajanTeo.Ch1.HilbertBersDifferential
import TakhtajanTeo.Ch1.QCVariationKernelSource
import TakhtajanTeo.Ch1.QCVariationDifferentialCovariance
import TakhtajanTeo.Ch1.QCVariationLocalKernel
import TakhtajanTeo.Ch1.ActualWelding
import TakhtajanTeo.Appendix.BergmanPeriodModel

/-!
# Chapter 1, §2 — `(2.1)`: the fourth-order kernel formula for `D₀(β ∘ R_[μ])`

Route (TT:1440–1480): `D₀BersR μ ν = D_μ(β∘Φ)(D₀R_μ ν)` is expressed in the plane coordinate `W = W_μ`
(`qcv_bers_differential_covariance`, `qcv_ahVar_iter3`, `qcv_base_dot_fourth_kernel_source`), then moved to the
welding coordinates `𝖿 = M∘W` on `𝔻` and `𝗀∘w_μ = M∘W` on `𝔻*` (`M` Möbius).  The unique pole of `w_μ`
in `𝔻*` (where `w_μ = ∞`, junk value `0` of `wA μ`) is a single point and is discarded almost everywhere.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo
namespace S2C

open QCV LiZhongQC

/-- (S1) `D₀(β∘R_[μ])ν` at `ζ ∈ 𝔻` in the plane coordinate `W = W_μ`; assembly of existing results. -/
theorem s2c_source {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) {ζ : ℂ} (hζ : ζ ∈ unitDisc) :
    AInf.toFun (D0BersR μ ν) ζ =
      -(6 / π) * deriv (qcv_planeSolution μ) ζ ^ 2 *
        ∫ x in unitDiscExterior, qcv_rightDerivative μ ν x * dz (qcv_planeSolution μ) x ^ 2 /
          (qcv_planeSolution μ x - qcv_planeSolution μ ζ) ^ 4 := by
  rw [hb_D0BersR_chain hμ]
  change AInf.toFun (fderiv ℂ bersPhi μ (qcv_rightDerivative μ ν)) ζ = _
  rw [qcv_bers_differential_covariance hμ (qcv_rightDerivative μ ν) hζ]
  have hy : qcv_planeSolution μ ζ ∈ qcv_planeDisk μ := ⟨ζ, hζ, rfl⟩
  have hm := bc_norm_lt_one hμ
  have hk : 0 ≤ ‖qcv_rightDerivative μ ν‖ / (1 - ‖μ‖ ^ 2) :=
    div_nonneg (norm_nonneg _) (by nlinarith [norm_nonneg μ])
  rw [qcv_ahVar_iter3 hk (qcv_base_dot_isBeltramiCoeff hμ _) (qcv_planeDisk_isOpen hμ)
    (fun u hu => qcv_base_dot_zero_on_disk hμ _ hu) hy,
    qcv_base_dot_fourth_kernel_source hμ]
  ring

/-- `𝖿 = f^μ` agrees with `f^μ = w^μ|𝔻` (`fB`). -/
theorem s2c_fsans_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : fsans μ = fB μ := by
  ext z; simp [fsans, AppB.b8_weldConst_zero hμ, lambdaW]

/-- `𝗀 = g_μ` agrees with `g_μ` (`gMu`). -/
theorem s2c_gsans_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : gsans μ = gMu μ := by
  have hid : Function.invFun (id : ExtPlane → ExtPlane) = id :=
    funext (fun z => Function.leftInverse_invFun Function.injective_id z)
  ext z
  simp only [gsans, AppB.b8_weldConst_zero hμ, alphaMu_eq_id, hid, id_eq, lambdaW, zero_mul,
    zero_add, div_one]
  rfl

/-- (S2) `𝖿 = f^μ` is conformal onto its image. -/
theorem s2c_conf_f {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsConformalOnto (fsans μ) unitDisc (fsans μ '' unitDisc) := by
  rw [s2c_fsans_eq hμ]
  obtain ⟨hd, hi⟩ := fB_holomorphic_injective hμ
  exact ⟨hd, hi, rfl⟩

/-- (S3) `𝗀 = g_μ` is conformal onto its image. -/
theorem s2c_conf_g {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsConformalOnto (gsans μ) unitDiscExterior (gsans μ '' unitDiscExterior) := by
  rw [s2c_gsans_eq hμ]
  have hw := (gMu_isWelding hμ).2.2.2.2.2.2
  exact ⟨hw.1, hw.2.1, rfl⟩

/-- The finite points where `w_μ = ∞` form a subsingleton (`w_μ` is injective on the sphere). -/
theorem s2c_pole_subsingleton (μ : LinfStar) :
    {x : ℂ | wAS μ (x : ExtPlane) = extInf}.Subsingleton :=
  fun _ hx _ hy => OnePoint.coe_injective ((wAS_bijective μ).1 (hx.trans hy.symm))

/-- Away from its (at most one) finite pole, `w_μ` is finite: an open set. -/
theorem s2c_pole_open (μ : LinfStar) : IsOpen {y : ℂ | wAS μ (y : ExtPlane) ≠ extInf} :=
  (s2c_pole_subsingleton μ).finite.isClosed.isOpen_compl

/-- (S4) `𝖿 = M ∘ W` on `𝔻` and `𝗀 ∘ w_μ = M ∘ W` on `𝔻*` (off the pole of `w_μ`) for one Möbius
`M(y) = (a y + b)/(c y + d)`.  [Interface correction: clause (ii) is restricted to `wAS μ x ≠ ∞`.] -/
theorem s2c_mobius {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
      (∀ ζ ∈ unitDisc, c * qcv_planeSolution μ ζ + d ≠ 0 ∧
        fsans μ ζ = (a * qcv_planeSolution μ ζ + b) / (c * qcv_planeSolution μ ζ + d)) ∧
      (∀ x ∈ unitDiscExterior, wAS μ (x : ExtPlane) ≠ extInf →
        c * qcv_planeSolution μ x + d ≠ 0 ∧
        gsans μ (wA μ x) = (a * qcv_planeSolution μ x + b) / (c * qcv_planeSolution μ x + d)) := by
  have hk := bc_norm_lt_one hμ
  obtain ⟨M, hM, W, hW, hfinite, -, f, hf, -⟩ := (wB_spec hμ).1
  have hWeq : qcv_planeSolution μ = W :=
    qcv_ns_eq (norm_nonneg μ) hk (extB_isBeltramiCoeff μ) hW
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  have hden : ∀ z ∈ unitDisc, c * W z + d ≠ 0 := by
    intro z hz he
    have hfin := (hfinite z).symm.trans (hf z hz)
    rw [mobiusExt_coe_of_eq_zero he] at hfin
    exact OnePoint.infty_ne_coe _ hfin
  refine ⟨a, b, c, d, hdet, fun ζ hζ => ?_, fun x hx hpole => ?_⟩
  · rw [hWeq]
    refine ⟨hden ζ hζ, ?_⟩
    rw [s2c_fsans_eq hμ, fB, hfinite ζ, mobiusExt_coe (hden ζ hζ)]
    rfl
  · have hx1 : 1 < ‖x‖ := by simpa [unitDiscExterior] using hx
    rcases wAS_maps_ext hμ hx1 with h | ⟨u, hu, hu'⟩
    · exact absurd h hpole
    · have hwA : wA μ x = u := by
        show finPart (wAS μ (x : ExtPlane)) = u
        rw [hu', finPart_coe]
      have hinv : Function.invFun (wAS μ) (u : ExtPlane) = (x : ExtPlane) := by
        rw [← hu']
        exact Function.leftInverse_invFun (wAS_bijective μ).1 _
      have hxu : u ∈ unitDiscExterior := by simpa [unitDiscExterior] using hu
      have hfac := gMu_sphere_factorization hμ hxu
      rw [hinv, hfinite x] at hfac
      have hden' : c * W x + d ≠ 0 := by
        intro he
        rw [mobiusExt_coe_of_eq_zero he] at hfac
        exact OnePoint.infty_ne_coe _ hfac.symm
      rw [mobiusExt_coe hden'] at hfac
      have hfac' := OnePoint.coe_injective hfac
      rw [hWeq]
      refine ⟨hden', ?_⟩
      rw [s2c_gsans_eq hμ, hwA, hfac']
      rfl

/-- Change of variables through a quasiconformal map on a set `D` (Bochner form, image restricted to
`g '' D`). -/
theorem s2c_cov_set {g : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hg : IsKQC g D K) (hgm : Measurable g)
    (G : ℂ → ℂ) (hG : AEStronglyMeasurable G (volume.restrict (g '' D))) :
    ∫ w in g '' D, G w = ∫ z in D, (ENNReal.ofReal (jacobian g z)).toReal • G (g z) := by
  have hJm : Measurable fun u => ENNReal.ofReal (jacobian g u) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_dz g).norm.pow_const 2).sub ((measurable_dzbar g).norm.pow_const 2))
  have hm : Measure.map g ((volume.restrict D).withDensity fun u => ENNReal.ofReal (jacobian g u)) =
      volume.restrict (g '' D) := by
    ext s hs
    rw [Measure.map_apply hgm hs, withDensity_apply _ (hgm hs)]
    have h := qcv_lintegral_image_eq hg (s.indicator fun _ => 1)
    rw [lintegral_indicator hs] at h
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul] at h
    rw [h]
    have h2 : ∫⁻ z in D, ENNReal.ofReal (jacobian g z) * (s.indicator (fun _ => (1 : ℝ≥0∞))) (g z) =
        ∫⁻ z in g ⁻¹' s, ENNReal.ofReal (jacobian g z) ∂(volume.restrict D) := by
      rw [← lintegral_indicator (hgm hs)]
      congr 1
      funext z
      by_cases hz : g z ∈ s <;> simp [Set.indicator, hz]
    exact h2.symm
  calc ∫ w in g '' D, G w
      = ∫ w, G w ∂(Measure.map g ((volume.restrict D).withDensity
          fun u => ENNReal.ofReal (jacobian g u))) := by rw [hm]
    _ = ∫ z, G (g z) ∂((volume.restrict D).withDensity fun u => ENNReal.ofReal (jacobian g u)) := by
        refine integral_map hgm.aemeasurable ?_
        rw [hm]; exact hG
    _ = ∫ z in D, (ENNReal.ofReal (jacobian g z)).toReal • G (g z) :=
        integral_withDensity_eq_integral_toReal_smul hJm
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _

/-- A subset of `𝔻*` with finite complement in `𝔻*` is almost everywhere equal to `𝔻*`. -/
theorem s2c_ae_eq_ext {T : Set ℂ} (hT : T ⊆ unitDiscExterior) (hf : (unitDiscExterior \ T).Finite) :
    T =ᵐ[volume] unitDiscExterior :=
  ae_eq_set.2 ⟨by rw [Set.sdiff_eq_empty.2 hT, measure_empty], hf.measure_zero volume⟩

/-- (S5) Change of variables `ξ = w_μ(x)` on `𝔻*`, with the phase and Jacobian of `qcv_rightDerivative`
(`(1 - |μ|²) ν(w_μ) conj(∂w_μ)/∂w_μ`), for the composite `𝗀 ∘ w_μ`. No integrability premise. -/
theorem s2c_cov_var {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) (K : ℂ → ℂ)
    (hK : Measurable K) :
    ∫ x in unitDiscExterior, qcv_rightDerivative μ ν x *
        dz (fun x => gsans μ (wA μ x)) x ^ 2 * K (gsans μ (wA μ x)) =
      ∫ ξ in unitDiscExterior, ν ξ * deriv (gsans μ) ξ ^ 2 * K (gsans μ ξ) := by
  obtain ⟨U, KK, hUo, hUE, hsub, hkqc, hmaps⟩ := bc_wA_kqc hμ
  have hfinI := bc_wA_image_compl_finite hμ hsub.finite
  have hgd := (s2c_conf_g hμ).1
  have hVo : IsOpen unitDiscExterior := bc_hEo
  have hH : AEStronglyMeasurable (fun ξ => ν ξ * deriv (gsans μ) ξ ^ 2 * K (gsans μ ξ))
      (volume.restrict unitDiscExterior) := by
    have h1 : AEStronglyMeasurable (⇑ν) (volume.restrict unitDiscExterior) :=
      Lp.aestronglyMeasurable ν
    have h2 : AEStronglyMeasurable (deriv (gsans μ)) (volume.restrict unitDiscExterior) :=
      ((hgd.deriv hVo).continuousOn).aestronglyMeasurable hVo.measurableSet
    have h3 : AEStronglyMeasurable (fun ξ => K (gsans μ ξ)) (volume.restrict unitDiscExterior) :=
      (hK.comp_aemeasurable (hgd.continuousOn.aemeasurable hVo.measurableSet)).aestronglyMeasurable
    exact (h1.mul (h2.pow 2)).mul h3
  have hHm : AEStronglyMeasurable (fun ξ => ν ξ * deriv (gsans μ) ξ ^ 2 * K (gsans μ ξ))
      (volume.restrict (wA μ '' U)) :=
    hH.mono_measure (Measure.restrict_mono hmaps le_rfl)
  have e1 : ∫ x in unitDiscExterior, qcv_rightDerivative μ ν x *
        dz (fun x => gsans μ (wA μ x)) x ^ 2 * K (gsans μ (wA μ x)) =
      ∫ x in U, qcv_rightDerivative μ ν x *
        dz (fun x => gsans μ (wA μ x)) x ^ 2 * K (gsans μ (wA μ x)) :=
    (setIntegral_congr_set (s2c_ae_eq_ext hUE hsub.finite)).symm
  have e2 : ∫ ξ in unitDiscExterior, ν ξ * deriv (gsans μ) ξ ^ 2 * K (gsans μ ξ) =
      ∫ ξ in wA μ '' U, ν ξ * deriv (gsans μ) ξ ^ 2 * K (gsans μ ξ) :=
    (setIntegral_congr_set (s2c_ae_eq_ext hmaps hfinI)).symm
  rw [e1, e2, s2c_cov_set hkqc (bc_wA_measurable hμ) _ hHm]
  refine setIntegral_congr_ae hUo.measurableSet ?_
  have hqrd := (ae_restrict_iff' hVo.measurableSet).1 (qcv_rightDerivative_ae hμ ν)
  filter_upwards [bc_wA_ae hμ, hqrd] with x hx hq hxU
  obtain ⟨hd, hdz, hdil, hlt⟩ := hx
  have hxE : x ∈ unitDiscExterior := hUE hxU
  have hx1 : 1 < ‖x‖ := by simpa [unitDiscExterior] using hxE
  have hext : extA μ x = μ x := by simp [extA, hx1]
  rw [hext] at hdil
  rw [hdil] at hlt
  have hy : wA μ x ∈ unitDiscExterior := hmaps ⟨x, hxU, rfl⟩
  have hgy : DifferentiableAt ℂ (gsans μ) (wA μ x) := hgd.differentiableAt (hVo.mem_nhds hy)
  have hchain : dz (fun x => gsans μ (wA μ x)) x = deriv (gsans μ) (wA μ x) * dz (wA μ) x :=
    (eq6_5 hd hgy).1
  have hbar : dzbar (wA μ) x = μ x * dz (wA μ) x := by
    change dzbar (wA μ) x / dz (wA μ) x = μ x at hdil
    exact (div_eq_iff hdz).mp hdil
  have hJr : jacobian (wA μ) x = ‖dz (wA μ) x‖ ^ 2 * (1 - ‖μ x‖ ^ 2) := by
    unfold jacobian
    rw [hbar, norm_mul]
    ring
  have hJ0 : 0 ≤ jacobian (wA μ) x := by
    rw [hJr]
    exact mul_nonneg (sq_nonneg _) (by nlinarith [norm_nonneg (μ x)])
  have hJ : (jacobian (wA μ) x : ℂ) =
      dz (wA μ) x * conj (dz (wA μ) x) * (1 - (‖μ x‖ : ℂ) ^ 2) := by
    rw [hJr, Complex.mul_conj]
    simp only [Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    push_cast
    ring
  have hcz : conj (dz (wA μ) x) ≠ 0 := by simpa using hdz
  rw [hq hxE, hchain, ENNReal.toReal_ofReal hJ0, Complex.real_smul, hJ]
  field_simp

/-- (S6) Chain rule for a Möbius composite of `W` (real differentiable at `x`), when `𝗀 ∘ w_μ = M ∘ W`
near `x`. -/
theorem s2c_dz_mobius {μ : LinfStar} {a b c d : ℂ} {x : ℂ}
    (hP : ∀ᶠ y in 𝓝 x, gsans μ (wA μ y) =
      (a * qcv_planeSolution μ y + b) / (c * qcv_planeSolution μ y + d))
    (hden : c * qcv_planeSolution μ x + d ≠ 0) (hdiff : DifferentiableAt ℝ (qcv_planeSolution μ) x) :
    dz (fun x => gsans μ (wA μ x)) x =
      (a * d - b * c) / (c * qcv_planeSolution μ x + d) ^ 2 * dz (qcv_planeSolution μ) x := by
  have hMd := bc_mobiusFn_hasDerivAt (a := a) (b := b) hden
  have hev : (fun x => gsans μ (wA μ x)) =ᶠ[𝓝 x] mobiusFn a b c d ∘ qcv_planeSolution μ := hP
  have h1 : dz (fun x => gsans μ (wA μ x)) x = dz (mobiusFn a b c d ∘ qcv_planeSolution μ) x := by
    unfold dz
    rw [hev.fderiv_eq (𝕜 := ℝ)]
  rw [h1, (eq6_5 hdiff hMd.differentiableAt).1, hMd.deriv]

/-- (S7) Derivative of a Möbius composite of the holomorphic `W` at `ζ ∈ 𝔻`. -/
theorem s2c_deriv_mobius {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {a b c d : ℂ}
    (hP : ∀ ζ ∈ unitDisc, c * qcv_planeSolution μ ζ + d ≠ 0 ∧
        fsans μ ζ = (a * qcv_planeSolution μ ζ + b) / (c * qcv_planeSolution μ ζ + d))
    {ζ : ℂ} (hζ : ζ ∈ unitDisc) :
    deriv (fsans μ) ζ = (a * d - b * c) / (c * qcv_planeSolution μ ζ + d) ^ 2 *
      deriv (qcv_planeSolution μ) ζ := by
  have hUo : IsOpen unitDisc := isOpen_ball
  have hWd : HasDerivAt (qcv_planeSolution μ) (deriv (qcv_planeSolution μ) ζ) ζ :=
    ((qcv_planeSolution_conformal hμ).1.differentiableAt (hUo.mem_nhds hζ)).hasDerivAt
  have hMd := bc_mobiusFn_hasDerivAt (a := a) (b := b) (hP ζ hζ).1
  have hev : fsans μ =ᶠ[𝓝 ζ] mobiusFn a b c d ∘ qcv_planeSolution μ :=
    eventually_of_mem (hUo.mem_nhds hζ) (fun y hy => (hP y hy).2)
  rw [hev.deriv_eq]
  exact (hMd.comp ζ hWd).deriv

/-- Pure algebra behind `s2c_main`. -/
theorem s2c_alg {Δ P Q e W' R D : ℂ} (hΔ : Δ ≠ 0) (hP : P ≠ 0) (hQ : Q ≠ 0) (he : e ≠ 0) :
    W' ^ 2 * (R * D ^ 2 / e ^ 4) =
      (Δ / Q ^ 2 * W') ^ 2 * (R * (Δ / P ^ 2 * D) ^ 2 * (1 / (Δ * e / (P * Q)) ^ 4)) := by
  field_simp

/-- The middle identity of `(2.1)`: plane-coordinate integral = welding-coordinate integral. -/
theorem s2c_main {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) {ζ : ℂ} (hζ : ζ ∈ unitDisc) :
    deriv (qcv_planeSolution μ) ζ ^ 2 *
        ∫ x in unitDiscExterior, qcv_rightDerivative μ ν x * dz (qcv_planeSolution μ) x ^ 2 /
          (qcv_planeSolution μ x - qcv_planeSolution μ ζ) ^ 4 =
      deriv (fsans μ) ζ ^ 2 *
        ∫ ξ in unitDiscExterior, ν ξ * deriv (gsans μ) ξ ^ 2 / (gsans μ ξ - fsans μ ζ) ^ 4 := by
  obtain ⟨a, b, c, d, hdet, hf, hg⟩ := s2c_mobius hμ
  have hk := bc_norm_lt_one hμ
  have hVo : IsOpen unitDiscExterior := bc_hEo
  have hKm : Measurable fun u : ℂ => 1 / (u - fsans μ ζ) ^ 4 :=
    measurable_const.div ((measurable_id.sub measurable_const).pow_const 4)
  have hcov := s2c_cov_var hμ ν (fun u => 1 / (u - fsans μ ζ) ^ 4) hKm
  have hR : ∫ ξ in unitDiscExterior, ν ξ * deriv (gsans μ) ξ ^ 2 / (gsans μ ξ - fsans μ ζ) ^ 4 =
      ∫ ξ in unitDiscExterior, ν ξ * deriv (gsans μ) ξ ^ 2 * (1 / (gsans μ ξ - fsans μ ζ) ^ 4) := by
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [mul_one_div]
  rw [hR, ← hcov, ← integral_const_mul, ← integral_const_mul]
  have hdiffW : ∀ᵐ x : ℂ, DifferentiableAt ℝ (qcv_planeSolution μ) x := by
    obtain ⟨⟨KW, hKW⟩, -⟩ := (qcv_W_props hk).1
    have h := s23_c2_ae_good hKW
    rw [Measure.restrict_univ] at h
    filter_upwards [h] with x hx using hx.1
  have hpole : ∀ᵐ x : ℂ, wAS μ (x : ExtPlane) ≠ extInf :=
    measure_eq_zero_iff_ae_notMem.mp ((s2c_pole_subsingleton μ).measure_zero volume)
  refine setIntegral_congr_ae hVo.measurableSet ?_
  filter_upwards [hdiffW, hpole] with x hdx hpx hx
  obtain ⟨hdenx, hgx⟩ := hg x hx hpx
  have hZ : ∀ᶠ y in 𝓝 x, gsans μ (wA μ y) =
      (a * qcv_planeSolution μ y + b) / (c * qcv_planeSolution μ y + d) := by
    filter_upwards [hVo.mem_nhds hx, (s2c_pole_open μ).mem_nhds hpx] with y hy hpy
    exact (hg y hy hpy).2
  have hdz := s2c_dz_mobius hZ hdenx hdx
  have hdenζ := (hf ζ hζ).1
  have hfζ := (hf ζ hζ).2
  have hdv := s2c_deriv_mobius hμ hf hζ
  rw [hdz, hdv, hgx, hfζ]
  by_cases hxe : qcv_planeSolution μ x = qcv_planeSolution μ ζ
  · rw [hxe]
    simp
  · have hne : qcv_planeSolution μ x - qcv_planeSolution μ ζ ≠ 0 := sub_ne_zero.2 hxe
    have hdiff : (a * qcv_planeSolution μ x + b) / (c * qcv_planeSolution μ x + d) -
        (a * qcv_planeSolution μ ζ + b) / (c * qcv_planeSolution μ ζ + d) =
        (a * d - b * c) * (qcv_planeSolution μ x - qcv_planeSolution μ ζ) /
          ((c * qcv_planeSolution μ x + d) * (c * qcv_planeSolution μ ζ + d)) := by
      rw [div_sub_div _ _ hdenx hdenζ]
      congr 1
      ring
    rw [hdiff]
    exact s2c_alg hdet hdenx hdenζ hne

/-- **(2.1)** (statement identical to the original `eq_2_1`). -/
theorem s2c_eq_2_1 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) {z : ℂ}
    (hz : z ∈ fsans μ '' unitDisc) :
    AInf.toFun (D0BersR μ ν) (Function.invFunOn (fsans μ) unitDisc z) *
        deriv (Function.invFunOn (fsans μ) unitDisc) z ^ 2 =
      -(6 / π) * ∫ u in gsans μ '' unitDiscExterior,
        ν (Function.invFunOn (gsans μ) unitDiscExterior u) *
          (conj (deriv (Function.invFunOn (gsans μ) unitDiscExterior) u) /
            deriv (Function.invFunOn (gsans μ) unitDiscExterior) u) / (u - z) ^ 4 := by
  obtain ⟨ζ, hζ, rfl⟩ := hz
  have hUo : IsOpen unitDisc := isOpen_ball
  have hVo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  refine (hb_fourth_kernel_pullback_iff hUo hVo (s2c_conf_f hμ) (s2c_conf_g hμ)
    (AInf.toFun (D0BersR μ ν)) (⇑ν) (-(6 / π)) hζ).2 ?_
  rw [s2c_source hμ ν hζ, mul_assoc, s2c_main hμ ν hζ]
  ring

end S2C

open LiZhongQC

/-- **(2.1)** (TT:1468–1497). With `Ω = 𝖿(𝔻)`, `Ω* = 𝗀(𝔻*)` and
`ν̃ = (ν ∘ 𝗀⁻¹) \overline{(𝗀⁻¹)'}/(𝗀⁻¹)'` on `Ω*` (`0` on `Ω`):
`D₀(β ∘ R_[μ])(ν)(𝖿⁻¹(z)) ((𝖿⁻¹)'(z))² = -(6/π) ∬_{Ω*} ν̃(u)/(u - z)⁴ d²u` for `z ∈ Ω`. -/
theorem eq_2_1 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) {z : ℂ} (hz : z ∈ fsans μ '' unitDisc) :
    AInf.toFun (D0BersR μ ν) (Function.invFunOn (fsans μ) unitDisc z) *
        deriv (Function.invFunOn (fsans μ) unitDisc) z ^ 2 =
      -(6 / π) * ∫ u in gsans μ '' unitDiscExterior,
        ν (Function.invFunOn (gsans μ) unitDiscExterior u) *
          (conj (deriv (Function.invFunOn (gsans μ) unitDiscExterior) u) /
            deriv (Function.invFunOn (gsans μ) unitDiscExterior) u) / (u - z) ^ 4 :=
  S2C.s2c_eq_2_1 hμ ν hz

end TakhtajanTeo
