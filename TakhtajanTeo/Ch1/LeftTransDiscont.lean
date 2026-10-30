import TakhtajanTeo.Ch1.GroupTranslation
import TakhtajanTeo.Ch1.GroupAlgebra
import TakhtajanTeo.Ch1.S1_1_Completed
import TakhtajanTeo.Ch1.WPChangeOfVariables
import TakhtajanTeo.Ch1.CircleLiftExtension
import LiZhongQC.Ch04.S16_Quasicircles
import LiZhongQC.Ch04.S17_BoundaryValues

/-!
# Left translations of `T(1)` are not continuous (`ltd_`, 下属2 + 下属3)

Host: new module `Ch1/LeftTransDiscont.lean`. `exists_leftTrans_not_continuous` is relocated here from
`S1_1_TeichmullerTheory` (no consumers); `ltd_exists_leftTrans_not_continuous` is its byte-identical copy.

Route ([Leh87, III.3.4]). Boundary values are read on `ℝ` through the Cayley map `C(z) = i(1 + z)/(1 - z)`
(`C : 𝔻 → ℍ`, `-1, -i, 1 ↦ 0, 1, ∞`, `C⁻¹(x) = (x - i)/(x + i)`), so `x ↦ Re C(w_κ(C⁻¹ x))` is the real boundary map of
`w_κ` normalized at `0, 1, ∞`.
1. `ltd_lam`: `λ(K) → 1` as `K → 1` (`lambdaInv`, `quadLambda`).
2. `ltd_sat_open`: the saturation `{[ν] : ‖ν - μ‖∞ < ε}` of a sup-norm ball is open in the quotient topology
   (right translation `σ ↦ σ * ν₀'` is continuous at `0`, `bc_hasFDerivAt`; `‖ν * ν₀⁻¹‖ ≲ ‖ν - ν₀‖`).
3. Boundary bookkeeping on `S¹`: `ltd_circle_mul`, `ltd_circle_inv` (`wA_mul`, `wAS_maps_circle`).
4. `ltd_transport` (下属3): `w_κ` is a `(1 + ‖κ‖)/(1 - ‖κ‖)`-q.c. self-map of `𝔻`; conjugated by `C` it is a q.c. self-map
   of `ℍ` fixing `∞` with boundary values `Re C(w_κ(C⁻¹ x))` (`HasQCExtensionH`).
5. `ltd_near_qs`: for `‖ν - μ‖∞` small the boundary map of `ν * μ⁻¹` is `ρ`-quasisymmetric (`thm17_1_quasisymmetric`
   and steps 1, 4; `|ν - μ|/|1 - μ̄ν| ≤ ‖ν - μ‖/(1 - ‖μ‖)`, `beltramiMul_inv_formula`).
6. Explicit maps: `ltd_strip_qc` (the strip map `x + iy ↦ a(x) + iy` for piecewise-linear `a` is q.c., with its
   dilatation), `ltd_realize` (下属3: a conj-symmetric plane q.c. map fixing `0, 1, -i` is `C ∘ w_μ ∘ C⁻¹` for some `μ`
   with `‖μ‖ ≤ k`).
7. `ltd_kink`: `h(x) = x + min(x + 1, 0)` (a kink at `-1`) and `g_n(x) = x + δ_n τ(x)` (`τ = 1` near `-1`, `δ_n → 0`):
   `h ∘ g_n ∘ h⁻¹` has `qsRatio = 2` at `-1` on scales `t ≤ 2δ_n`, while `‖λ_n‖∞ → 0`.
8. Assembly: if `L_[μ]` were continuous, `[μ * λ_n] → [μ]`, so `[μ * λ_n]` lies in the open set of step 2 and step 5
   makes `h ∘ g_n ∘ h⁻¹` `3/2`-quasisymmetric, against step 7.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-! ### Step 1: `λ(K) → 1` -/

/-- `C⁻¹(x) = (x - i)/(x + i)` lies on `S¹`. -/
theorem ltd_cay_mem (x : ℝ) : ((x : ℂ) - I) / ((x : ℂ) + I) ∈ unitCircle := by
  have hne : (x : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  show ‖((x : ℂ) - I) / ((x : ℂ) + I)‖ = 1
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.2 hne)]
  have h1 : (x : ℂ) - I = conj ((x : ℂ) + I) := by simp [map_add, Complex.conj_ofReal, sub_eq_add_neg]
  rw [h1, Complex.norm_conj]

/-- `w_μ` maps `S¹` to `S¹`. -/
theorem ltd_wA_mem {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitCircle) :
    wA μ z ∈ unitCircle := by
  obtain ⟨u, hu, he⟩ := wAS_maps_circle hμ hz
  show ‖finPart (wAS μ (z : ExtPlane))‖ = 1
  rw [he]
  exact hu

/-- On `S¹`, `w_μ` is finite: `wAS μ z = ↑(wA μ z)`. -/
theorem ltd_wAS_circle {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitCircle) :
    wAS μ (z : ExtPlane) = ((wA μ z : ℂ) : ExtPlane) := by
  obtain ⟨u, -, he⟩ := wAS_maps_circle hμ hz
  show wAS μ (z : ExtPlane) = ((finPart (wAS μ (z : ExtPlane)) : ℂ) : ExtPlane)
  rw [he]
  rfl

/-- `w_{ν * κ} = w_ν ∘ w_κ` on `S¹` (helper copy, usable above step 3). -/
theorem ltd_cmul {ν κ : LinfStar} (hν : ν ∈ LinfStarBall) (hκ : κ ∈ LinfStarBall) :
    ∀ z ∈ unitCircle, wA (beltramiMul ν κ) z = wA ν (wA κ z) := by
  intro z hz
  have hmul := (wA_mul hκ hν).2.1
  show finPart (wAS (beltramiMul ν κ) (z : ExtPlane)) = finPart (wAS ν (wA κ z : ExtPlane))
  rw [hmul, Function.comp_apply, ltd_wAS_circle hκ hz]

/-- `w_μ ∘ w_{μ⁻¹} = id` on `S¹` (helper copy). -/
theorem ltd_cinv {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ z ∈ unitCircle, wA μ (wA (beltramiInv μ) z) = z := by
  intro z hz
  have h := (wA_mul hμ hμ).2.2
  have hi : wAS μ (wAS (beltramiInv μ) (z : ExtPlane)) = (z : ExtPlane) := congrFun h.2.1 (z : ExtPlane)
  rw [ltd_wAS_circle h.1 hz, ltd_wAS_circle hμ (ltd_wA_mem h.1 hz)] at hi
  exact OnePoint.coe_injective hi

/-- `w_{μ⁻¹} ∘ w_μ = id` on `S¹`. -/
theorem ltd_circle_inv' {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ z ∈ unitCircle, wA (beltramiInv μ) (wA μ z) = z := by
  intro z hz
  have h := (wA_mul hμ hμ).2.2
  have hi : wAS (beltramiInv μ) (wAS μ (z : ExtPlane)) = (z : ExtPlane) := congrFun h.2.2 (z : ExtPlane)
  rw [ltd_wAS_circle hμ hz, ltd_wAS_circle h.1 (ltd_wA_mem hμ hz)] at hi
  exact OnePoint.coe_injective hi

/-- `0 * ν = ν`. -/
theorem ltd_zero_mul {ν : LinfStar} (hν : ν ∈ LinfStarBall) : beltramiMul 0 ν = ν := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  refine grp_wAS_injective (bg_mul_mem_ball hν h0) hν ?_
  rw [(wA_mul hν h0).2.1, grp_wAS_zero, Function.id_comp]

/-- `‖ν * ν₀⁻¹‖∞ ≤ ‖ν - ν₀‖∞/(1 - ‖ν₀‖∞)` (`beltramiMul_inv_formula`). -/
theorem ltd_inv_bound {ν ν₀ : LinfStar} (hν : ν ∈ LinfStarBall) (hν₀ : ν₀ ∈ LinfStarBall) :
    ‖beltramiMul ν (beltramiInv ν₀)‖ ≤ ‖ν - ν₀‖ / (1 - ‖ν₀‖) := by
  have hn₀ := bc_norm_lt_one hν₀
  have hn := bc_norm_lt_one hν
  refine bc_Lp_norm_le _ (div_nonneg (norm_nonneg _) (by linarith)) ?_
  have hf := beltramiMul_inv_formula hν₀ hν
  have hb := bc_invFun_pullback_ae hν₀
    (P := fun u => ‖(ν - ν₀) u‖ ≤ ‖ν - ν₀‖ ∧ (ν - ν₀) u = ν u - ν₀ u ∧ ‖ν₀ u‖ ≤ ‖ν₀‖ ∧ ‖ν u‖ ≤ ‖ν‖)
    ((LinfStar_ae_norm_le (ν - ν₀)).and ((Lp.coeFn_sub ν ν₀).and
      ((LinfStar_ae_norm_le ν₀).and (LinfStar_ae_norm_le ν))))
  filter_upwards [hf, hb] with z hz hP
  obtain ⟨h1, h2, h3, h4⟩ := hP
  rw [hz]
  set u := Function.invFun (wA ν₀) z
  rw [h2] at h1
  have hθ : ‖dz (wA ν₀) u / conj (dz (wA ν₀) u)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_conj]
    exact div_self_le_one _
  have hden : 1 - ‖ν₀‖ ≤ ‖1 - conj (ν₀ u) * ν u‖ := by
    have h5 : ‖conj (ν₀ u) * ν u‖ ≤ ‖ν₀‖ := by
      rw [norm_mul, Complex.norm_conj]
      calc ‖ν₀ u‖ * ‖ν u‖ ≤ ‖ν₀‖ * 1 :=
            mul_le_mul h3 (h4.trans hn.le) (norm_nonneg _) (norm_nonneg _)
        _ = ‖ν₀‖ := mul_one _
    have h6 := norm_sub_norm_le (1 : ℂ) (conj (ν₀ u) * ν u)
    rw [norm_one] at h6
    linarith
  rw [norm_mul, norm_div]
  calc ‖ν u - ν₀ u‖ / ‖1 - conj (ν₀ u) * ν u‖ * ‖dz (wA ν₀) u / conj (dz (wA ν₀) u)‖
      ≤ ‖ν u - ν₀ u‖ / ‖1 - conj (ν₀ u) * ν u‖ * 1 :=
        mul_le_mul_of_nonneg_left hθ (div_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖ν - ν₀‖ / (1 - ‖ν₀‖) := by
        rw [mul_one]
        exact div_le_div₀ (norm_nonneg _) h1 (by linarith) hden

/-- `λ((1 + k)/(1 - k)) ≤ ρ` for `k` small. -/
theorem ltd_lam : ∀ ρ : ℝ, 1 < ρ → ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, 0 ≤ k → k < k₀ →
    lambdaInv ((1 + k) / (1 - k)) ≤ ρ := by
  intro ρ hρ
  have hmono := quadLambda_strictMono.1
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hv : 1 < quadLambda ρ := by
    have := hmono (show (1 : ℝ) ∈ Ioi 0 from mem_Ioi.2 one_pos) (show ρ ∈ Ioi 0 from hρ0) hρ
    rwa [b4_quadLambda_one] at this
  set v := quadLambda ρ with hvdef
  refine ⟨(v - 1) / (v + 1), div_pos (by linarith) (by linarith), fun k hk0 hk => ?_⟩
  have hk1 : k < 1 := lt_of_lt_of_le hk ((div_le_one (by linarith)).2 (by linarith))
  have hK : (1 + k) / (1 - k) < v := by
    rw [div_lt_iff₀ (by linarith)]
    rw [lt_div_iff₀ (by linarith)] at hk
    nlinarith
  refine Real.sSup_le (fun σ hσ => ?_) hρ0.le
  obtain ⟨hσ0, hσK⟩ := hσ
  have hlt : quadLambda σ < quadLambda ρ := lt_of_le_of_lt hσK hK
  exact ((hmono.lt_iff_lt (show σ ∈ Ioi 0 from hσ0) (show ρ ∈ Ioi 0 from hρ0)).1 hlt).le

/-! ### Step 2: saturations of sup-norm balls are open -/

/-- `{[ν] : ‖ν - μ‖∞ < ε}` is open in `T(1)`. -/
theorem ltd_sat_open (μ : LinfStar) (ε : ℝ) :
    IsOpen {p : T1 | ∃ ν : LinfStarBall, Phi ν = p ∧ ‖(ν : LinfStar) - μ‖ < ε} := by
  have hq : IsQuotientMap Phi := isQuotientMap_quotient_mk'
  rw [← hq.isOpen_preimage, Metric.isOpen_iff]
  rintro ν₀ ⟨ν₀', he, hlt⟩
  have hrel := Quotient.exact he
  obtain ⟨D, hD, -⟩ := bc_hasFDerivAt ν₀'.2
  have hca := Metric.continuousAt_iff.1 hD.continuousAt
  obtain ⟨η, hη, hηr⟩ := hca (ε - ‖(ν₀' : LinfStar) - μ‖) (by linarith)
  have hν₀n := bc_norm_lt_one ν₀.2
  have hinv := bc_beltramiInv_mem_ball ν₀.2
  refine ⟨η * (1 - ‖(ν₀ : LinfStar)‖), mul_pos hη (by linarith), fun ν hν => ?_⟩
  have hνd : ‖(ν : LinfStar) - ν₀‖ < η * (1 - ‖(ν₀ : LinfStar)‖) := by
    rw [mem_ball, Subtype.dist_eq, dist_eq_norm] at hν
    exact hν
  have hσ := bg_mul_mem_ball hinv ν.2
  have hσn : ‖beltramiMul (ν : LinfStar) (beltramiInv ν₀)‖ < η := by
    refine (ltd_inv_bound ν.2 ν₀.2).trans_lt ?_
    rw [div_lt_iff₀ (by linarith)]
    exact hνd
  have hF := hηr (show dist (beltramiMul (ν : LinfStar) (beltramiInv ν₀)) 0 < η by
    rw [dist_zero_right]; exact hσn)
  rw [ltd_zero_mul ν₀'.2, dist_eq_norm] at hF
  refine ⟨⟨beltramiMul (beltramiMul (ν : LinfStar) (beltramiInv ν₀)) ν₀', bg_mul_mem_ball ν₀'.2 hσ⟩,
    Quotient.sound ?_, ?_⟩
  · intro z hz
    show wA (beltramiMul (beltramiMul (ν : LinfStar) (beltramiInv ν₀)) ν₀') z = wA ν z
    rw [ltd_cmul hσ ν₀'.2 z hz, hrel z hz, ltd_cmul ν.2 hinv _ (ltd_wA_mem ν₀.2 hz),
      ltd_circle_inv' ν₀.2 z hz]
  · show ‖beltramiMul (beltramiMul (ν : LinfStar) (beltramiInv ν₀)) ν₀' - μ‖ < ε
    have := norm_sub_le_norm_sub_add_norm_sub
      (beltramiMul (beltramiMul (ν : LinfStar) (beltramiInv ν₀)) ν₀') (ν₀' : LinfStar) μ
    linarith

/-! ### Step 3: boundary bookkeeping on `S¹` -/

/-- `w_{ν * κ} = w_ν ∘ w_κ` on `S¹`. -/
theorem ltd_circle_mul {ν κ : LinfStar} (hν : ν ∈ LinfStarBall) (hκ : κ ∈ LinfStarBall) :
    ∀ z ∈ unitCircle, wA (beltramiMul ν κ) z = wA ν (wA κ z) := by
  exact ltd_cmul hν hκ

/-- `w_μ ∘ w_{μ⁻¹} = id` on `S¹`. -/
theorem ltd_circle_inv {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ z ∈ unitCircle, wA μ (wA (beltramiInv μ) z) = z := by
  exact ltd_cinv hμ

/-! ### Step 4: transport to the upper half-plane (下属3) -/

/-- `w_κ` is a `(1 + ‖κ‖)/(1 - ‖κ‖)`-q.c. self-map of `𝔻` (`wpcv_g_disc` with the constant pinned by the
uniqueness clause of `extA_normalized_plane_exists`). -/
theorem ltd_wA_disc {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    IsKQC (wA κ) unitDisc ((1 + ‖κ‖) / (1 - ‖κ‖)) ∧ wA κ '' unitDisc = unitDisc := by
  obtain ⟨M, ⟨a, b, c, d, hdet, rfl⟩, W, hW, hfin, -⟩ := wA_spec hκ
  obtain ⟨W', -, hK, huniq⟩ := extA_normalized_plane_exists hκ
  rw [← huniq W hW] at hK
  have hform : ∀ z, wA κ z = mobiusFn a b c d (W z) := by
    intro z
    show finPart (wAS κ (z : ExtPlane)) = _
    rw [hfin z]
    by_cases h : c * W z + d = 0
    · rw [mobiusExt_coe_of_eq_zero h]
      simp [mobiusFn, h, finPart]
    · rw [mobiusExt_coe h]
      rfl
  have hdisc : ∀ z ∈ unitDisc, c * W z + d ≠ 0 := by
    intro z hz h
    obtain ⟨u, -, hu⟩ := wAS_maps_disc hκ (z := z) (by simpa [unitDisc] using hz)
    rw [hfin z, mobiusExt_coe_of_eq_zero h] at hu
    exact absurd hu.symm (OnePoint.coe_ne_infty u)
  have hWU : IsKQC W unitDisc ((1 + ‖κ‖) / (1 - ‖κ‖)) := t3b_isKQC_restrict hK isOpen_ball (subset_univ _)
  have hVo : IsOpen (W '' unitDisc) := isOpen_image_of_isKQC hWU
  have hVden : ∀ z ∈ W '' unitDisc, c * z + d ≠ 0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdisc x hx
  have hconf : IsConformalOnto (mobiusFn a b c d) (W '' unitDisc) (mobiusFn a b c d '' (W '' unitDisc)) := by
    refine ⟨fun z hz => ?_, bc_mobiusFn_injOn hdet hVden, rfl⟩
    exact (bc_mobiusFn_hasDerivAt (hVden z hz)).differentiableAt.differentiableWithinAt
  have hg : IsKQC (mobiusFn a b c d) (W '' unitDisc) 1 := isKQC_one_of_conformal hVo hconf
  have hcomp := thm7_1_comp hWU hg (subset_refl _)
  have hfun : wA κ = mobiusFn a b c d ∘ W := funext hform
  rw [mul_one] at hcomp
  refine ⟨by rw [hfun]; exact hcomp, ?_⟩
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨u, hu, hzu⟩ := wAS_maps_disc hκ (z := z) (by simpa [unitDisc] using hz)
    show finPart (wAS κ (z : ExtPlane)) ∈ unitDisc
    rw [hzu]
    simpa [finPart, unitDisc] using hu
  · intro hw
    have hmem : (w : ExtPlane) ∈ wAS κ '' toExt unitDisc := by
      rw [(wA_mapsTo hκ).1]
      exact ⟨w, hw, rfl⟩
    obtain ⟨p, ⟨z, hz, rfl⟩, hpw⟩ := hmem
    exact ⟨z, hz, by show finPart (wAS κ (z : ExtPlane)) = w; rw [hpw]; rfl⟩

/-- A map of `ℂ̄` agreeing with `g` on `U` carries `toExt U` onto `toExt (g '' U)`. -/
theorem ltd_image_toExt {E : ExtPlane → ExtPlane} {g : ℂ → ℂ} {U V : Set ℂ}
    (hE : ∀ w ∈ U, E (w : ExtPlane) = ((g w : ℂ) : ExtPlane)) (hg : g '' U = V) : E '' toExt U = toExt V := by
  unfold toExt
  rw [image_image, ← hg, image_image]
  exact image_congr hE

/-- `C⁻¹(x) = (x - i)/(x + i)` lies on `S¹ ∖ {1}` for real `x`. -/
theorem ltd_cayley_real (x : ℝ) : ‖cayley (x : ℂ)‖ = 1 ∧ cayley (x : ℂ) ≠ 1 := by
  have hden : (x : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hc : (x : ℂ) - I = conj ((x : ℂ) + I) := by
    rw [map_add, Complex.conj_ofReal, Complex.conj_I]
    ring
  refine ⟨?_, ?_⟩
  · show ‖((x : ℂ) - I) / ((x : ℂ) + I)‖ = 1
    rw [norm_div, hc, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hden)]
  · intro h
    have h1 : (x : ℂ) - I = (x : ℂ) + I := by
      have := (div_eq_one_iff_eq hden).1 h
      exact this
    have := congrArg Complex.im h1
    norm_num at this

/-- `C(u) = i(1 + u)/(1 - u)` is real for `u ∈ S¹ ∖ {1}`. -/
theorem ltd_cayleyInv_real {u : ℂ} (hu : ‖u‖ = 1) (hu1 : u ≠ 1) : (cayleyInv u).im = 0 := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  have hcu : conj u = u⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hu]
    simp
  have h1 : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have h2 : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  rw [← Complex.conj_eq_iff_im]
  show conj (I * (1 + u) / (1 - u)) = I * (1 + u) / (1 - u)
  rw [map_div₀, map_mul, map_add, map_sub, Complex.conj_I, map_one, hcu]
  field_simp
  ring

/-- `C ∘ w_κ ∘ C⁻¹` is a `(1 + ‖κ‖)/(1 - ‖κ‖)`-q.c. self-map of `ℍ` fixing `∞`, with boundary values
`Re C(w_κ(C⁻¹ x))`. -/
theorem ltd_transport {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    ∃ g : ℂ → ℂ, HasQCExtensionH
      (fun x : ℝ => (I * (1 + wA κ (((x : ℂ) - I) / ((x : ℂ) + I))) /
        (1 - wA κ (((x : ℂ) - I) / ((x : ℂ) + I)))).re) g ((1 + ‖κ‖) / (1 - ‖κ‖)) := by
  obtain ⟨hWK, hWimg⟩ := ltd_wA_disc hκ
  -- the three homeomorphisms of `ℂ̄`
  set e1 : ExtPlane ≃ₜ ExtPlane := mobiusHomeomorph 1 (-I) 1 I cayley_inv_det with he1d
  set e3 : ExtPlane ≃ₜ ExtPlane := mobiusHomeomorph I I (-1) 1 cayley_det with he3d
  set eW : ExtPlane ≃ₜ ExtPlane :=
    (wAS_continuous hκ).homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ (wAS_bijective κ)) with heWd
  have he1 : ∀ z ∈ upperHalf, e1 (z : ExtPlane) = ((cayley z : ℂ) : ExtPlane) := by
    intro z hz
    have hden : (1 : ℂ) * z + I ≠ 0 := by
      rw [one_mul]
      exact cayley_den_ne_zero hz
    rw [he1d, mobiusHomeomorph_apply, mobiusExt_coe hden]
    congr 1
    simp only [mobiusFn, cayley]
    congr 1 <;> ring
  have he3 : ∀ w ∈ unitDisc, e3 (w : ExtPlane) = ((cayleyInv w : ℂ) : ExtPlane) := by
    intro w hw
    have hden : (-1 : ℂ) * w + 1 ≠ 0 := by
      rw [show (-1 : ℂ) * w + 1 = 1 - w by ring]
      exact cayleyInv_den_ne_zero (mem_ball_zero_iff.1 hw)
    rw [he3d, mobiusHomeomorph_apply, mobiusExt_coe hden]
    congr 1
    simp only [mobiusFn, cayleyInv]
    congr 1 <;> ring
  have heW : ∀ w ∈ unitDisc, eW (w : ExtPlane) = ((wA κ w : ℂ) : ExtPlane) := by
    intro w hw
    obtain ⟨u, -, hu⟩ := wAS_maps_disc hκ (z := w) (by simpa [unitDisc] using hw)
    show wAS κ (w : ExtPlane) = ((finPart (wAS κ (w : ExtPlane)) : ℂ) : ExtPlane)
    rw [hu]
    rfl
  have hc1 : MapsTo (cayley ∘ id) upperHalf unitDisc := fun z hz => cayley_mem_unitDisc hz
  have hcW : MapsTo (wA κ ∘ (cayley ∘ id)) upperHalf unitDisc := fun z hz =>
    hWimg ▸ mem_image_of_mem (wA κ) (hc1 hz)
  have H1 := (isHomeoExtension_id upperHalf).comp_homeomorph (mapsTo_id _) e1 he1
    (ltd_image_toExt he1 isConformalOnto_cayley.2.2)
  have H2 := H1.comp_homeomorph hc1 eW heW (wA_mapsTo hκ).1
  have H3 := H2.comp_homeomorph hcW e3 he3 (ltd_image_toExt he3 s35a_x_isConformalOnto_cayleyInv.2.2)
  -- quasiconformality and image
  have hq1 : IsKQC cayley upperHalf 1 := isKQC_one_of_conformal isOpen_upperHalf isConformalOnto_cayley
  have hq3 : IsKQC cayleyInv unitDisc 1 := isKQC_one_of_conformal isOpen_ball s35a_x_isConformalOnto_cayleyInv
  have hQ1 := thm7_1_comp hq1 hWK (by rw [isConformalOnto_cayley.2.2])
  have hQ2 := thm7_1_comp hQ1 hq3 (by rw [image_comp, isConformalOnto_cayley.2.2, hWimg])
  rw [one_mul, mul_one] at hQ2
  refine ⟨cayleyInv ∘ (wA κ ∘ (cayley ∘ id)), hQ2, ?_, e3 ∘ (eW ∘ (e1 ∘ id)), H3, ?_, ?_⟩
  · rw [image_comp, image_comp, image_comp, image_id, isConformalOnto_cayley.2.2, hWimg,
      s35a_x_isConformalOnto_cayleyInv.2.2]
  · obtain ⟨-, -, -, -, -, -, -, -, hw1⟩ := wA_spec hκ
    show e3 (wAS κ (e1 extInf)) = extInf
    rw [he1d, he3d]
    simp only [mobiusHomeomorph_apply]
    rw [mobiusExt_infty_of_ne one_ne_zero, div_one, hw1, mobiusExt_coe_of_eq_zero (by ring)]
  · intro x
    obtain ⟨hx1, hx2⟩ := ltd_cayley_real x
    have hxH : ((x : ℂ) + I) ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
    have hex : e1 ((x : ℂ) : ExtPlane) = ((cayley (x : ℂ) : ℂ) : ExtPlane) := by
      rw [he1d, mobiusHomeomorph_apply, mobiusExt_coe (by rwa [one_mul])]
      congr 1
      simp only [mobiusFn, cayley]
      congr 1 <;> ring
    obtain ⟨u, hu, hwu⟩ := wAS_maps_circle hκ hx1
    have hu1 : u ≠ 1 := by
      rintro rfl
      obtain ⟨-, -, -, -, -, -, -, -, hw1⟩ := wA_spec hκ
      have h := (wAS_bijective κ).1 (hwu.trans hw1.symm)
      exact hx2 (OnePoint.coe_injective h)
    have hwA : wA κ (cayley (x : ℂ)) = u := by
      show finPart (wAS κ ((cayley (x : ℂ) : ℂ) : ExtPlane)) = u
      rw [hwu]
      rfl
    have hden : (-1 : ℂ) * u + 1 ≠ 0 := by
      rw [show (-1 : ℂ) * u + 1 = 1 - u by ring]
      exact sub_ne_zero.mpr (Ne.symm hu1)
    show e3 (wAS κ (e1 ((x : ℂ) : ExtPlane))) =
      ((((cayleyInv (wA κ (cayley (x : ℂ)))).re : ℝ) : ℂ) : ExtPlane)
    rw [hex, hwu, hwA, he3d, mobiusHomeomorph_apply, mobiusExt_coe hden]
    congr 1
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      congr 1
      simp only [mobiusFn, cayleyInv]
      congr 1 <;> ring
    · rw [Complex.ofReal_im, ← ltd_cayleyInv_real hu hu1]
      congr 1
      simp only [mobiusFn, cayleyInv]
      congr 1 <;> ring

/-! ### Step 5: near `μ` in `L∞`, `ν * μ⁻¹` has nearly symmetric boundary values -/

/-- For `‖ν - μ‖∞` small the boundary map of `ν * μ⁻¹` is `ρ`-quasisymmetric. -/
theorem ltd_near_qs (μ : LinfStarBall) : ∀ ρ : ℝ, 1 < ρ → ∃ ε > 0, ∀ ν : LinfStarBall,
    ‖(ν : LinfStar) - μ‖ < ε → LiZhongQC.IsQuasisymmetric
      (fun x : ℝ => (I * (1 + wA (beltramiMul ν (beltramiInv μ)) (((x : ℂ) - I) / ((x : ℂ) + I))) /
        (1 - wA (beltramiMul ν (beltramiInv μ)) (((x : ℂ) - I) / ((x : ℂ) + I)))).re) ρ := by
  intro ρ hρ
  obtain ⟨k₀, hk₀, hlam⟩ := ltd_lam ρ hρ
  have hμn := bc_norm_lt_one μ.2
  refine ⟨k₀ * (1 - ‖(μ : LinfStar)‖), mul_pos hk₀ (by linarith), fun ν hν => ?_⟩
  have hκ := bg_mul_mem_ball (bc_beltramiInv_mem_ball μ.2) ν.2
  have hκn : ‖beltramiMul (ν : LinfStar) (beltramiInv μ)‖ < k₀ := by
    refine (ltd_inv_bound ν.2 μ.2).trans_lt ?_
    rw [div_lt_iff₀ (by linarith)]
    exact hν
  have hκ1 := bc_norm_lt_one hκ
  obtain ⟨g, hg⟩ := ltd_transport hκ
  obtain ⟨h1, h2, h3, h4, h5⟩ := thm17_1_quasisymmetric hg
  have hL := hlam _ (norm_nonneg _) hκn
  have hpos := (td_quadLambda_lambdaInv (show (0 : ℝ) < (1 + ‖beltramiMul (ν : LinfStar) (beltramiInv μ)‖) /
    (1 - ‖beltramiMul (ν : LinfStar) (beltramiInv μ)‖) from div_pos (by positivity) (by linarith))).1
  refine ⟨h1, h2, h3, h4, fun x t ht => ?_⟩
  obtain ⟨ha, hb⟩ := h5 x t ht
  exact ⟨(inv_anti₀ hpos hL).trans ha, hb.trans hL⟩

/-! ### Step 6: explicit quasiconformal maps -/

/-- `IsKQC` only sees the values on the domain. -/
theorem ltd_isKQC_congr {f g : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hf : IsKQC f U K) (h : EqOn f g U) :
    IsKQC g U K := by
  obtain ⟨hU, hK, ⟨hc, hi, -, hinv⟩, hQ⟩ := hf
  have himg : g '' U = f '' U := h.image_eq.symm
  refine ⟨hU, hK, ⟨hc.congr fun z hz => (h hz).symm, hi.congr h, rfl, ?_⟩, ?_⟩
  · rw [himg]
    refine hinv.congr fun b hb => ?_
    have hexg : ∃ a ∈ U, g a = b := by
      obtain ⟨a, ha, rfl⟩ := hb
      exact ⟨a, ha, (h ha).symm⟩
    have hex : ∃ a ∈ U, f a = b := hb
    have h1 := Function.invFunOn_mem hexg
    have h2 := Function.invFunOn_eq hexg
    have h3 := Function.invFunOn_mem hex
    have h4 := Function.invFunOn_eq hex
    exact hi h1 h3 (by rw [h h1, h2, h4])
  · intro Q hQU
    obtain ⟨Q', ⟨hd, hv⟩, hm⟩ := hQ Q hQU
    have hdU : Q.dom ⊆ U := fun z hz => by
      obtain ⟨w, hw, he⟩ := hQU (subset_closure ⟨z, hz, rfl⟩)
      rw [← OnePoint.coe_injective he]
      exact hw
    refine ⟨Q', ⟨hd.trans (h.mono hdU).image_eq, fun i => ?_⟩, hm⟩
    rw [hv i]
    obtain ⟨w, hw, he⟩ := hQU (frontier_subset_closure (Q.isTopQuad.2.1 i))
    rw [← he, OnePoint.map_some, OnePoint.map_some, h hw]

/-- The real-affine map `x + iy ↦ s x + c + iy` (`s > 0`) as `A z + B z̄ + C`: it is `(1 + k)/(1 - k)`-q.c. when
`|s - 1|/(s + 1) ≤ k`, with constant dilatation `(s - 1)/(s + 1)`. -/
theorem ltd_affine {s c k : ℝ} (hs : 0 < s) (hk1 : k < 1) (hsk : |s - 1| / (s + 1) ≤ k) :
    IsKQC (fun z : ℂ => ((s * z.re + c : ℝ) : ℂ) + z.im * I) univ ((1 + k) / (1 - k)) ∧
      ∀ z, ‖complexDilatation (fun z : ℂ => ((s * z.re + c : ℝ) : ℂ) + z.im * I) z‖ ≤ k := by
  have heq : (fun z : ℂ => ((s * z.re + c : ℝ) : ℂ) + z.im * I) =
      fun z => (((s + 1) / 2 : ℝ) : ℂ) * z + (((s - 1) / 2 : ℝ) : ℂ) * conj z + (c : ℂ) := by
    funext z
    apply Complex.ext <;> simp <;> ring
  have hnA : ‖(((s + 1) / 2 : ℝ) : ℂ)‖ = (s + 1) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hnB : ‖(((s - 1) / 2 : ℝ) : ℂ)‖ = |s - 1| / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
  have hm : |s - 1| ≤ k * (s + 1) := (div_le_iff₀ (by linarith)).1 hsk
  have hlt : ‖(((s - 1) / 2 : ℝ) : ℂ)‖ < ‖(((s + 1) / 2 : ℝ) : ℂ)‖ := by
    rw [hnA, hnB]
    have : k * (s + 1) < s + 1 := by nlinarith
    linarith
  obtain ⟨hC1, hdil⟩ := affine_isC1Quasiconformal (C := (c : ℂ)) hlt
  rw [heq]
  refine ⟨(isKQC_of_isC1Quasiconformal hC1).mono ?_, fun z => ?_⟩
  · rw [hnA, hnB, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [abs_nonneg (s - 1)]
  · rw [(hdil z).1, norm_div, hnA, hnB]
    rw [div_div_div_cancel_right₀ (two_ne_zero)]
    exact hsk

/-- The strip map `x + iy ↦ a(x) + iy` of a piecewise-linear increasing homeomorphism `a` of `ℝ` (slopes `s` with
`|s - 1|/(s + 1) ≤ k` off a finite set `S`) is a `(1 + k)/(1 - k)`-q.c. map of `ℂ` onto `ℂ` with `|μ| ≤ k`. -/
theorem ltd_strip_qc {a : ℝ → ℝ} {S : Set ℝ} (hS : S.Finite) (ha : StrictMono a) (hac : Continuous a)
    (has : Function.Surjective a) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hloc : ∀ x ∉ S, ∃ s : ℝ, 0 < s ∧ |s - 1| / (s + 1) ≤ k ∧ ∀ᶠ y in 𝓝 x, a y = a x + s * (y - x)) :
    IsKQC (fun z : ℂ => (a z.re : ℂ) + z.im * I) univ ((1 + k) / (1 - k)) ∧
      (fun z : ℂ => (a z.re : ℂ) + z.im * I) '' univ = univ ∧
      ∀ᵐ z : ℂ, ‖complexDilatation (fun z : ℂ => (a z.re : ℂ) + z.im * I) z‖ ≤ k := by
  set F : ℂ → ℂ := fun z => (a z.re : ℂ) + z.im * I with hF
  obtain ⟨e, he⟩ : ∃ e : ℝ ≃o ℝ, ⇑e = a := ⟨StrictMono.orderIsoOfSurjective a ha has, rfl⟩
  set G : ℂ → ℂ := fun w => (e.symm w.re : ℂ) + w.im * I with hG
  have hFG : ∀ w, F (G w) = w := by
    intro w
    apply Complex.ext <;> simp [hF, hG, ← he]
  have hGF : ∀ z, G (F z) = z := by
    intro z
    apply Complex.ext <;> simp [hF, hG, ← he]
  have hFc : Continuous F := by
    rw [hF]
    exact (Complex.continuous_ofReal.comp (hac.comp Complex.continuous_re)).add
      ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)
  have hGc : Continuous G := by
    rw [hG]
    exact (Complex.continuous_ofReal.comp (e.symm.continuous.comp Complex.continuous_re)).add
      ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)
  have hFi : Function.Injective F := fun x y hxy => by rw [← hGF x, hxy, hGF y]
  have hFs : F '' univ = univ := by
    rw [image_univ]
    exact range_eq_univ.2 fun w => ⟨G w, hFG w⟩
  have hK : (1 : ℝ) ≤ (1 + k) / (1 - k) := (one_le_div (by linarith)).2 (by linarith)
  have hhom : IsHomeomorphOnto F univ (F '' univ) := by
    refine ⟨hFc.continuousOn, hFi.injOn, rfl, ?_⟩
    refine hGc.continuousOn.congr fun w hw => ?_
    have hex : ∃ x ∈ (univ : Set ℂ), F x = w := ⟨G w, mem_univ _, hFG w⟩
    exact hFi ((Function.invFunOn_eq hex).trans (hFG w).symm)
  set L : Set ℂ := {z | z.re ∈ S} with hLdef
  have hLnull : volume L = 0 := by
    have hpre : L = measurableEquivRealProd ⁻¹' (S ×ˢ univ) := by
      ext z
      simp [hLdef, measurableEquivRealProd]
    rw [hpre, Complex.volume_preserving_equiv_real_prod.measure_preimage
      ((hS.measurableSet.prod MeasurableSet.univ).nullMeasurableSet), Measure.volume_eq_prod,
      Measure.prod_prod, hS.measure_zero, zero_mul]
  have hLv : ∀ᵐ x : ℝ, {y : ℝ | (x : ℂ) + (y : ℂ) * I ∈ L}.Countable := by
    filter_upwards [hS.countable.ae_notMem volume] with x hx
    have : {y : ℝ | (x : ℂ) + (y : ℂ) * I ∈ L} = ∅ := by
      ext y
      simp [hLdef, hx]
    rw [this]
    exact countable_empty
  have hLh : ∀ᵐ y : ℝ, {x : ℝ | (x : ℂ) + (y : ℂ) * I ∈ L}.Countable := by
    refine Eventually.of_forall fun y => ?_
    have : {x : ℝ | (x : ℂ) + (y : ℂ) * I ∈ L} = S := by
      ext x
      simp [hLdef]
    rw [this]
    exact hS.countable
  -- local affine form off `L`
  have hlocal : ∀ z ∉ L, ∃ s c r : ℝ, 0 < s ∧ |s - 1| / (s + 1) ≤ k ∧ 0 < r ∧
      EqOn (fun z : ℂ => ((s * z.re + c : ℝ) : ℂ) + z.im * I) F (Complex.re ⁻¹' ball z.re r) := by
    intro z hz
    obtain ⟨s, hs, hsk, hev⟩ := hloc z.re hz
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨s, a z.re - s * z.re, r, hs, hsk, hr, fun w hw => ?_⟩
    have h := hball (show dist w.re z.re < r from hw)
    show ((s * w.re + (a z.re - s * z.re) : ℝ) : ℂ) + w.im * I = (a w.re : ℂ) + w.im * I
    rw [h]
    push_cast
    ring
  refine ⟨?_, hFs, ?_⟩
  · refine s13x_removable isOpen_univ hK hhom hLnull hLv hLh fun z hz => ?_
    obtain ⟨s, c, r, hs, hsk, hr, heq⟩ := hlocal z hz.2
    have hUo : IsOpen (Complex.re ⁻¹' ball z.re r) := isOpen_ball.preimage Complex.continuous_re
    refine ⟨_, hUo, mem_ball_self hr, subset_univ _, ltd_isKQC_congr ?_ heq⟩
    exact t3b_isKQC_restrict (ltd_affine hs hk1 hsk).1 hUo (subset_univ _)
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hLnull] with z hz
    obtain ⟨s, c, r, hs, hsk, hr, heq⟩ := hlocal z hz
    have hUo : IsOpen (Complex.re ⁻¹' ball z.re r) := isOpen_ball.preimage Complex.continuous_re
    have hev : (fun z : ℂ => ((s * z.re + c : ℝ) : ℂ) + z.im * I) =ᶠ[𝓝 z] F :=
      Filter.eventually_of_mem (hUo.mem_nhds (mem_ball_self hr)) heq
    have hd := hev.fderiv_eq (𝕜 := ℝ)
    have h := (ltd_affine (c := c) hs hk1 hsk).2 z
    have hcd : complexDilatation (fun z : ℂ => ((s * z.re + c : ℝ) : ℂ) + z.im * I) z =
        complexDilatation F z := by
      show (fderiv ℝ _ z 1 + I * fderiv ℝ _ z I) / 2 / ((fderiv ℝ _ z 1 - I * fderiv ℝ _ z I) / 2) =
        (fderiv ℝ F z 1 + I * fderiv ℝ F z I) / 2 / ((fderiv ℝ F z 1 - I * fderiv ℝ F z I) / 2)
      rw [hd]
    rw [← hcd]
    exact h

/-- `Im C(x) · |1 - x|² = 1 - |x|²` for `C(x) = i(1 + x)/(1 - x)`. -/
theorem ltd_C_im {x : ℂ} (hx : x ≠ 1) : (cayleyInv x).im * normSq (1 - x) = 1 - normSq x := by
  have h : normSq (1 - x) ≠ 0 := by
    rw [Ne, normSq_eq_zero]
    exact sub_ne_zero.mpr (Ne.symm hx)
  show (I * (1 + x) / (1 - x)).im * normSq (1 - x) = 1 - normSq x
  rw [Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  rw [sub_mul, div_mul_cancel₀ _ h, div_mul_cancel₀ _ h, normSq_apply]
  ring

/-- `C(x) ≠ -i` (the preimage of `-i` under `C` is `∞`). -/
theorem ltd_C_ne_negI (x : ℂ) : cayleyInv x ≠ -I := by
  intro h
  by_cases hx : x = 1
  · subst hx
    have h' : I * (1 + 1) / (1 - 1) = -I := h
    rw [sub_self, div_zero] at h'
    have := congrArg Complex.im h'
    simp at this
  · have h1 : (1 : ℂ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have h' : I * (1 + x) / (1 - x) = -I := h
    rw [div_eq_iff h1] at h'
    have h2 : (2 : ℂ) * I = 0 := by linear_combination h'
    simp at h2

/-- `|C⁻¹(w)|² · |w + i|² = |w - i|²`. -/
theorem ltd_Cinv_normSq {w : ℂ} (hw : w + I ≠ 0) : normSq (cayley w) * normSq (w + I) = normSq (w - I) := by
  show normSq ((w - I) / (w + I)) * normSq (w + I) = normSq (w - I)
  rw [normSq_div, div_mul_cancel₀ _ ((normSq_pos.mpr hw).ne')]

/-- `C⁻¹` maps the lower half-plane to `𝔻*` and the closed upper half-plane to the closed disc. -/
theorem ltd_Cinv_norm {w : ℂ} (hw : w ≠ -I) :
    (w.im < 0 → 1 < ‖cayley w‖) ∧ (0 ≤ w.im → ‖cayley w‖ ≤ 1) := by
  have hw' : w + I ≠ 0 := by
    intro h
    exact hw (by linear_combination h)
  have hpos := normSq_pos.mpr hw'
  have hk := normSq_cayley_key w
  have hn := ltd_Cinv_normSq hw'
  have hsq : ‖cayley w‖ ^ 2 = normSq (cayley w) := (Complex.normSq_eq_norm_sq _).symm
  refine ⟨fun him => ?_, fun him => ?_⟩
  · have h1 : 1 < normSq (cayley w) := by
      by_contra hc
      push Not at hc
      nlinarith
    nlinarith [norm_nonneg (cayley w)]
  · have h1 : normSq (cayley w) ≤ 1 := by
      by_contra hc
      push Not at hc
      nlinarith
    nlinarith [norm_nonneg (cayley w)]

/-- `C(C⁻¹ y) = y` for `y ≠ -i`. -/
theorem ltd_C_Cinv_of_ne {y : ℂ} (hy : y ≠ -I) : cayleyInv (cayley y) = y := by
  have hy' : y + I ≠ 0 := by
    intro h
    exact hy (by linear_combination h)
  show I * (1 + (y - I) / (y + I)) / (1 - (y - I) / (y + I)) = y
  have h2 : 1 - (y - I) / (y + I) = 2 * I / (y + I) := by
    field_simp
    ring
  have h3 : 1 + (y - I) / (y + I) = 2 * y / (y + I) := by
    field_simp
    ring
  rw [h2, h3]
  field_simp

/-- A `conj`-symmetric homeomorphism of `ℂ` fixing `-i` preserves the real line, the lower half-plane and the closed
upper half-plane. -/
theorem ltd_f_halfplanes {f : ℂ → ℂ} (hfc : Continuous f) (hfi : Function.Injective f)
    (hconj : ∀ z, f (conj z) = conj (f z)) (hI : f (-I) = -I) :
    (∀ z : ℂ, z.im = 0 → (f z).im = 0) ∧ (∀ z : ℂ, z.im < 0 → (f z).im < 0) ∧
      (∀ z : ℂ, 0 ≤ z.im → 0 ≤ (f z).im) := by
  have hreal : ∀ z : ℂ, z.im = 0 → (f z).im = 0 := by
    intro z hz
    have hc : conj z = z := Complex.conj_eq_iff_im.mpr hz
    have h := hconj z
    rw [hc] at h
    exact Complex.conj_eq_iff_im.mp h.symm
  have hrinv : ∀ z : ℂ, (f z).im = 0 → z.im = 0 := by
    intro z hz
    have h := hconj z
    rw [Complex.conj_eq_iff_im.mpr hz] at h
    exact Complex.conj_eq_iff_im.mp (hfi h)
  have hlow : ∀ z : ℂ, z.im < 0 → (f z).im < 0 := by
    have hS : IsPreconnected {z : ℂ | z.im < 0} :=
      (convex_halfSpace_lt (f := fun z : ℂ => z.im) ⟨fun _ _ => rfl, fun c z => Complex.smul_im c z⟩ 0).isPreconnected
    have hsub : f '' {z : ℂ | z.im < 0} ⊆ {w : ℂ | w.im < 0} := by
      refine (hS.image f hfc.continuousOn).subset_left_of_subset_union
        (v := {w : ℂ | 0 < w.im}) (isOpen_lt continuous_im continuous_const)
        (isOpen_lt (continuous_const (y := (0 : ℝ))) continuous_im)
        ?_ ?_ ⟨-I, ⟨-I, by simp, hI⟩, by simp⟩
      · rw [Set.disjoint_left]
        intro w h1 h2
        have h1' : w.im < 0 := h1
        have h2' : 0 < w.im := h2
        linarith
      · rintro _ ⟨z, hz, rfl⟩
        rcases lt_trichotomy (f z).im 0 with h | h | h
        · exact Or.inl h
        · exact absurd (hrinv z h) (ne_of_lt hz)
        · exact Or.inr h
    exact fun z hz => hsub ⟨z, hz, rfl⟩
  refine ⟨hreal, hlow, fun z hz => ?_⟩
  rcases hz.lt_or_eq with h | h
  · have h1 : (conj z).im < 0 := by rw [Complex.conj_im]; linarith
    have h2 := hlow _ h1
    rw [hconj, Complex.conj_im] at h2
    linarith
  · rw [hreal z h.symm]

/-- `C = (iz + i)/(-z + 1)` as a Möbius map. -/
theorem ltd_mob_C : mobiusFn I I (-1) 1 = cayleyInv := by
  funext x
  simp only [mobiusFn, cayleyInv]
  congr 1 <;> ring

/-- `C⁻¹ = (z - i)/(z + i)` as a Möbius map. -/
theorem ltd_mob_Cinv : mobiusFn 1 (-I) 1 I = cayley := by
  funext x
  simp only [mobiusFn, cayley]
  congr 1 <;> ring

/-- `C⁻¹ ∘ f ∘ C` maps `𝔻*` into `𝔻*` and the closed disc minus `1` into the closed disc. -/
theorem ltd_G_norm {f : ℂ → ℂ} (hfi : Function.Injective f) (hI : f (-I) = -I)
    (hlow : ∀ z : ℂ, z.im < 0 → (f z).im < 0) (hup : ∀ z : ℂ, 0 ≤ z.im → 0 ≤ (f z).im) {y : ℂ} (hy : y ≠ 1) :
    (1 < ‖y‖ → 1 < ‖cayley (f (cayleyInv y))‖) ∧ (‖y‖ ≤ 1 → ‖cayley (f (cayleyInv y))‖ ≤ 1) := by
  have hne : f (cayleyInv y) ≠ -I := by
    intro h
    exact ltd_C_ne_negI y (hfi (h.trans hI.symm))
  have him := ltd_C_im hy
  have hpos : 0 < normSq (1 - y) := normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hy))
  have hsq : normSq y = ‖y‖ ^ 2 := Complex.normSq_eq_norm_sq y
  obtain ⟨hA, hB⟩ := ltd_Cinv_norm hne
  refine ⟨fun h => hA (hlow _ ?_), fun h => hB (hup _ ?_)⟩
  · by_contra hc
    push Not at hc
    have : 0 ≤ (cayleyInv y).im * normSq (1 - y) := mul_nonneg hc hpos.le
    nlinarith [norm_nonneg y]
  · by_contra hc
    push Not at hc
    have : (cayleyInv y).im * normSq (1 - y) < 0 := mul_neg_of_neg_of_pos hc hpos
    nlinarith [norm_nonneg y]

/-- `C⁻¹ ∘ f ∘ C` is `K`-q.c. on `𝔻*`. -/
theorem ltd_G_qc {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hfi : Function.Injective f) (hI : f (-I) = -I) :
    IsKQC (fun z => cayley (f (cayleyInv z))) unitDiscExterior K := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hden1 : ∀ z ∈ unitDiscExterior, (-1 : ℂ) * z + 1 ≠ 0 := by
    intro z hz h
    have hz1 : z = 1 := by linear_combination -h
    have : (1 : ℝ) < ‖z‖ := hz
    rw [hz1, norm_one] at this
    exact lt_irrefl _ this
  have hc1 : IsConformalOnto (mobiusFn I I (-1) 1) unitDiscExterior (mobiusFn I I (-1) 1 '' unitDiscExterior) :=
    ⟨fun z hz => (bc_mobiusFn_hasDerivAt (hden1 z hz)).differentiableAt.differentiableWithinAt,
      bc_mobiusFn_injOn cayley_det hden1, rfl⟩
  have hq1 : IsKQC (mobiusFn I I (-1) 1) unitDiscExterior 1 := isKQC_one_of_conformal hEo hc1
  rw [ltd_mob_C] at hq1
  have hD3 : IsOpen {w : ℂ | w ≠ -I} := isOpen_ne
  have hden3 : ∀ w ∈ {w : ℂ | w ≠ -I}, (1 : ℂ) * w + I ≠ 0 := by
    intro w hw h
    exact hw (by linear_combination h)
  have hc3 : IsConformalOnto (mobiusFn 1 (-I) 1 I) {w : ℂ | w ≠ -I} (mobiusFn 1 (-I) 1 I '' {w : ℂ | w ≠ -I}) :=
    ⟨fun z hz => (bc_mobiusFn_hasDerivAt (hden3 z hz)).differentiableAt.differentiableWithinAt,
      bc_mobiusFn_injOn cayley_inv_det hden3, rfl⟩
  have hq3 : IsKQC (mobiusFn 1 (-I) 1 I) {w : ℂ | w ≠ -I} 1 := isKQC_one_of_conformal hD3 hc3
  rw [ltd_mob_Cinv] at hq3
  have hQ1 := thm7_1_comp hq1 hf (subset_univ _)
  have hQ2 := thm7_1_comp hQ1 hq3 (by
    rintro _ ⟨z, -, rfl⟩
    show f (cayleyInv z) ≠ -I
    intro h
    exact ltd_C_ne_negI z (hfi (h.trans hI.symm)))
  rw [one_mul, mul_one] at hQ2
  exact hQ2

/-- The dilatation of `G ∘ w_{μ⁻¹}` vanishes a.e. on `𝔻*` when `G` has dilatation `μ` there (as in
`bg_F_dilatation_zero`). -/
theorem ltd_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {G : ℂ → ℂ}
    (hP : ∀ᵐ u ∂(volume.restrict unitDiscExterior), DifferentiableAt ℝ G u ∧ dz G u ≠ 0 ∧
      complexDilatation G u = μ u ∧ ‖complexDilatation G u‖ < 1) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior), complexDilatation (G ∘ wA (beltramiInv μ)) z = 0 := by
  have hι := bc_beltramiInv_mem_ball hμ
  filter_upwards [bg_comp_dilatation_ae hι hP, bc_beltramiInv_ae hμ, bc_inverse_germ hμ,
    bc_invFun_phase_ae hμ] with z hc hinv hgerm hph
  have hx : wA (beltramiInv μ) z = Function.invFun (wA μ) z := hgerm.self_of_nhds
  have hdz : dz (wA (beltramiInv μ)) z = dz (Function.invFun (wA μ)) z := (t203_c1_dz_congr hgerm).1
  rw [hc, hx, hdz, hph, hinv]
  have hz0 : (-μ (Function.invFun (wA μ) z) *
        (dz (wA μ) (Function.invFun (wA μ) z) / conj (dz (wA μ) (Function.invFun (wA μ) z))) +
      μ (Function.invFun (wA μ) z) *
        (dz (wA μ) (Function.invFun (wA μ) z) / conj (dz (wA μ) (Function.invFun (wA μ) z)))) = 0 := by
    ring
  simp only [hz0, zero_div]

/-- (下属3) A `conj`-symmetric q.c. map of `ℂ` onto `ℂ` fixing `0, 1, -i`, with `|μ_f| ≤ k`, is `C ∘ w_μ ∘ C⁻¹` on `ℝ`
for some `μ ∈ L∞(𝔻*)₁` with `‖μ‖∞ ≤ k`. -/
theorem ltd_realize {f : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hf : IsKQC f univ ((1 + k) / (1 - k)))
    (hfs : f '' univ = univ) (hconj : ∀ z, f (conj z) = conj (f z)) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hI : f (-I) = -I) (hdil : ∀ᵐ z : ℂ, ‖complexDilatation f z‖ ≤ k) :
    ∃ μ : LinfStarBall, ‖(μ : LinfStar)‖ ≤ k ∧ ∀ x : ℝ,
      I * (1 + wA μ (((x : ℂ) - I) / ((x : ℂ) + I))) / (1 - wA μ (((x : ℂ) - I) / ((x : ℂ) + I))) = f x := by
  -- `hdil` is not needed: the bound `|μ| ≤ k` on `𝔻*` follows from the `K`-quasiconformality of `C⁻¹ ∘ f ∘ C`
  -- (`isKQC_maxDilatation_le`), which also takes care of the Möbius change of variables.
  have _hdil := hdil
  obtain ⟨e, he⟩ := t1_homeomorph hf hfs
  have hfc : Continuous f := he ▸ e.continuous
  have hfi : Function.Injective f := he ▸ e.injective
  obtain ⟨hreal, hlow, hup⟩ := ltd_f_halfplanes hfc hfi hconj hI
  have hGK := ltd_G_qc hf hfi hI
  -- the coefficient `μ`
  have hbd : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖complexDilatation (fun z => cayley (f (cayleyInv z))) z‖ ≤ k := by
    have h := (isKQC_maxDilatation_le hGK).2
    have hk : ((1 + k) / (1 - k) - 1) / ((1 + k) / (1 - k) + 1) = k := by
      have : (1 : ℝ) - k ≠ 0 := by linarith
      field_simp
      ring
    rwa [hk] at h
  have hmem : MemLp (complexDilatation (fun z => cayley (f (cayleyInv z)))) ∞
      (volume.restrict unitDiscExterior) :=
    memLp_top_of_bound ((measurable_dzbar _).div (measurable_dz _)).aestronglyMeasurable _ hbd
  have hμn := norm_toLinf_le_of_ae_bound hk0 hbd
  have hμ : toLinf (complexDilatation (fun z => cayley (f (cayleyInv z)))) ∈ LinfStarBall :=
    mem_ball_zero_iff.mpr (hμn.trans_lt hk1)
  refine ⟨⟨_, hμ⟩, hμn, ?_⟩
  set G : ℂ → ℂ := fun z => cayley (f (cayleyInv z)) with hGd
  set μ : LinfStar := toLinf (complexDilatation G) with hμd
  have hι := bc_beltramiInv_mem_ball hμ
  -- the sphere map `FS = C⁻¹ ∘ f ∘ C`
  set FS : ExtPlane ≃ₜ ExtPlane := (mobiusHomeomorph I I (-1) 1 cayley_det).trans
    (e.onePointCongr.trans (mobiusHomeomorph 1 (-I) 1 I cayley_inv_det)) with hFSd
  have hFS : ∀ p, FS p = mobiusExt 1 (-I) 1 I (OnePoint.map f (mobiusExt I I (-1) 1 p)) := by
    intro p
    rw [← he]
    rfl
  have hFSc : ∀ y : ℂ, y ≠ 1 → FS (y : ExtPlane) = ((G y : ℂ) : ExtPlane) := by
    intro y hy
    have hd1 : (-1 : ℂ) * y + 1 ≠ 0 := by
      intro h
      exact hy (by linear_combination -h)
    have hne : f (cayleyInv y) ≠ -I := by
      intro h
      exact ltd_C_ne_negI y (hfi (h.trans hI.symm))
    have hd3 : (1 : ℂ) * f (mobiusFn I I (-1) 1 y) + I ≠ 0 := by
      rw [ltd_mob_C]
      intro h
      exact hne (by linear_combination h)
    rw [hFS, mobiusExt_coe hd1, OnePoint.map_some, mobiusExt_coe hd3, ltd_mob_C, ltd_mob_Cinv]
  have hFSinf : FS extInf = extInf := by
    rw [hFS, mobiusExt_infty_of_ne (by norm_num : (-1 : ℂ) ≠ 0)]
    have : I / (-1 : ℂ) = -I := by ring
    rw [this, OnePoint.map_some, hI, mobiusExt_coe_of_eq_zero (by ring)]
  have hFS1 : FS ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
    rw [hFS, mobiusExt_coe_of_eq_zero (by ring), OnePoint.map_infty, mobiusExt_infty_of_ne one_ne_zero, div_one]
  -- data of `G` on `𝔻*`
  have hGdata : ∃ (U : Set ℂ) (K : ℝ), IsOpen U ∧ U ⊆ unitDiscExterior ∧ (unitDiscExterior \ U).Finite ∧
      IsKQC G U K ∧ ∀ x ∈ U, G x ∈ unitDiscExterior ∧ FS (x : ExtPlane) = ((G x : ℂ) : ExtPlane) := by
    refine ⟨unitDiscExterior, _, isOpen_lt continuous_const continuous_norm, subset_rfl, by simp, hGK,
      fun x hx => ?_⟩
    have hx1 : x ≠ 1 := by
      rintro rfl
      have : (1 : ℝ) < ‖(1 : ℂ)‖ := hx
      rw [norm_one] at this
      exact lt_irrefl _ this
    exact ⟨(ltd_G_norm hfi hI hlow hup hx1).1 hx, hFSc x hx1⟩
  have hP : ∀ᵐ u ∂(volume.restrict unitDiscExterior), DifferentiableAt ℝ G u ∧ dz G u ≠ 0 ∧
      complexDilatation G u = μ u ∧ ‖complexDilatation G u‖ < 1 := by
    filter_upwards [s23_c2_ae_good hGK, bc_toLinf_ae hmem] with u hu hμu
    obtain ⟨hd, hlt, -⟩ := hu
    have hdz : dz G u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hlt
      exact absurd hlt (not_lt.mpr (norm_nonneg _))
    refine ⟨hd, hdz, hμu.symm, ?_⟩
    show ‖dzbar G u / dz G u‖ < 1
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hdz)]
    exact hlt
  -- rigidity of `F = FS ∘ w_{μ⁻¹}` on `𝔻*`
  set F : ExtPlane → ExtPlane := fun p => FS (wAS (beltramiInv μ) p) with hFd
  have hFc : Continuous F := FS.continuous.comp (wAS_continuous hι)
  have hFb : Function.Bijective F := FS.bijective.comp (wAS_bijective _)
  have hFm : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), F p ∉ toExt (closedBall (0 : ℂ) 1) := by
    intro p hp
    have hq : wAS (beltramiInv μ) p ∉ toExt (closedBall (0 : ℂ) 1) := fun h => hp ((wAS_closed_iff hι p).mpr h)
    show FS (wAS (beltramiInv μ) p) ∉ toExt (closedBall (0 : ℂ) 1)
    generalize wAS (beltramiInv μ) p = q at hq
    induction q using OnePoint.rec with
    | infty =>
      rw [hFSinf]
      rintro ⟨z, -, hz⟩
      exact OnePoint.coe_ne_infty z hz
    | coe y =>
      have hy : 1 < ‖y‖ := by
        rw [TakhtajanTeo.coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le] at hq
        exact hq
      have hy1 : y ≠ 1 := by
        rintro rfl
        rw [norm_one] at hy
        exact lt_irrefl _ hy
      rw [hFSc y hy1, TakhtajanTeo.coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le]
      exact (ltd_G_norm hfi hI hlow hup hy1).1 hy
  have hFin : ∀ p ∈ toExt (closedBall (0 : ℂ) 1), F p ∈ toExt (closedBall (0 : ℂ) 1) := by
    intro p hp
    have hq := (wAS_closed_iff hι p).mp hp
    show FS (wAS (beltramiInv μ) p) ∈ toExt (closedBall (0 : ℂ) 1)
    generalize wAS (beltramiInv μ) p = q at hq
    obtain ⟨y, hy, rfl⟩ := hq
    have hy' : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
    by_cases hy1 : y = 1
    · subst hy1
      rw [hFS1]
      exact ⟨1, by simp, rfl⟩
    · rw [hFSc y hy1, TakhtajanTeo.coe_mem_toExt_iff, mem_closedBall_zero_iff]
      exact (ltd_G_norm hfi hI hlow hup hy1).2 hy'
  have hFs : ∀ q ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1), F p = q := by
    intro q hq
    obtain ⟨p, hp⟩ := hFb.2 q
    exact ⟨p, fun h => hq (hp ▸ hFin p h), hp⟩
  obtain ⟨U, K, hUo, hUE, hUf, hT, hdata⟩ := bg_kqc_comp (bg_good_wA hι) hGdata
  have hdiffU : DifferentiableOn ℂ (G ∘ wA (beltramiInv μ)) U :=
    nx_differentiableOn_of_dilatation_zero hT (ae_restrict_of_ae_restrict_of_subset hUE (ltd_zero hμ hP))
  have hdiff := bc_sigma_conjugate_holomorphic hFc hFm hUf hdiffU hdata
  obtain ⟨i1, iI, i2⟩ := bg_fix hι
  have hm1 : FS ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) := by
    rw [hFSc _ (by norm_num)]
    congr 1
    show cayley (f (cayleyInv (-1))) = -1
    have : cayleyInv (-1) = 0 := by
      show I * (1 + -1) / (1 - -1) = 0
      simp
    rw [this, h0]
    show ((0 : ℂ) - I) / (0 + I) = -1
    field_simp
    ring
  have hmI : FS ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane) := by
    have hI1 : (-I : ℂ) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    rw [hFSc _ hI1]
    congr 1
    show cayley (f (cayleyInv (-I))) = -I
    have : cayleyInv (-I) = 1 := by
      show I * (1 + -I) / (1 - -I) = 1
      have h2 : (1 : ℂ) - -I ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this
      rw [div_eq_one_iff_eq h2]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [this, h1]
    show ((1 : ℂ) - I) / (1 + I) = -I
    have h2 : (1 : ℂ) + I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    rw [div_eq_iff h2]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hext := bc_exterior_rigidity hFc hFb.1 hFm hFs
    (by show FS _ = _; rw [i1, hm1]) (by show FS _ = _; rw [iI, hmI]) (by show FS _ = _; rw [i2, hFS1]) hdiff
  -- on the circle, by continuity
  have hcirc : ∀ z : ℂ, ‖z‖ = 1 → F (z : ExtPlane) = (z : ExtPlane) := by
    intro z hz
    have hlim : Tendsto (fun t : ℝ => (((t : ℂ) * z : ℂ) : ExtPlane)) (𝓝[>] 1) (𝓝 (z : ExtPlane)) := by
      have h1' : Tendsto (fun t : ℝ => (t : ℂ) * z) (𝓝 1) (𝓝 z) := by
        have hc : Continuous (fun t : ℝ => (t : ℂ) * z) := Complex.continuous_ofReal.mul continuous_const
        have := hc.tendsto 1
        simpa only [Complex.ofReal_one, one_mul] using this
      exact (OnePoint.continuous_coe.tendsto z).comp (h1'.mono_left nhdsWithin_le_nhds)
    have hev : ∀ᶠ t : ℝ in 𝓝[>] 1, F (((t : ℂ) * z : ℂ) : ExtPlane) = (((t : ℂ) * z : ℂ) : ExtPlane) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      apply hext
      rw [TakhtajanTeo.coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le, norm_mul, hz, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_trans one_pos ht)]
      exact ht
    exact tendsto_nhds_unique ((hFc.tendsto _).comp hlim) (hlim.congr' (hev.mono fun t ht => ht.symm))
  -- conclusion on `ℝ`
  intro x
  obtain ⟨hx1, hx2⟩ := ltd_cayley_real x
  obtain ⟨u, hu, hwu⟩ := wAS_maps_circle hμ hx1
  have hinv : wAS (beltramiInv μ) (wAS μ ((cayley (x : ℂ) : ℂ) : ExtPlane)) =
      ((cayley (x : ℂ) : ℂ) : ExtPlane) :=
    congrFun (grp_wAS_inv_right hμ) _
  have hF := hcirc u hu
  rw [← hwu] at hF
  have hFx : FS ((cayley (x : ℂ) : ℂ) : ExtPlane) = wAS μ ((cayley (x : ℂ) : ℂ) : ExtPlane) := by
    have := hF
    simp only [hFd, hinv] at this
    exact this
  have hwA : wA μ (cayley (x : ℂ)) = G (cayley (x : ℂ)) := by
    show finPart (wAS μ ((cayley (x : ℂ) : ℂ) : ExtPlane)) = _
    rw [← hFx, hFSc _ hx2]
    rfl
  have hCC : cayleyInv (cayley (x : ℂ)) = x := ltd_C_Cinv_of_ne (by
    intro h
    have := congrArg Complex.im h
    simp at this)
  have hfx : f x ≠ -I := by
    intro h
    have := congrArg Complex.im h
    rw [hreal x (Complex.ofReal_im x)] at this
    simp at this
  show cayleyInv (wA μ (cayley (x : ℂ))) = f x
  rw [hwA]
  show cayleyInv (cayley (f (cayleyInv (cayley (x : ℂ))))) = f x
  rw [hCC, ltd_C_Cinv_of_ne hfx]

/-! ### Step 7: the kink -/

/-- `C⁻¹(r) ≠ 1`. -/
theorem ltd_Cinv_ne_one (r : ℝ) : ((r : ℂ) - I) / ((r : ℂ) + I) ≠ 1 := by
  have hne : (r : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  intro h
  rw [div_eq_one_iff_eq hne] at h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- `C(C⁻¹ r) = r` for real `r`. -/
theorem ltd_C_Cinv (r : ℝ) :
    I * (1 + ((r : ℂ) - I) / ((r : ℂ) + I)) / (1 - ((r : ℂ) - I) / ((r : ℂ) + I)) = r := by
  have hne : (r : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have h1 : (1 : ℂ) - ((r : ℂ) - I) / ((r : ℂ) + I) = 2 * I / ((r : ℂ) + I) := by
    field_simp
    ring
  have h2 : (1 : ℂ) + ((r : ℂ) - I) / ((r : ℂ) + I) = 2 * r / ((r : ℂ) + I) := by
    field_simp
    ring
  rw [h1, h2, mul_div_assoc', div_div_div_cancel_right₀ hne]
  field_simp

/-- `w_μ(1) = 1`. -/
theorem ltd_wA_one {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : wA μ 1 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hm2⟩ := wA_spec hμ
  show finPart (wAS μ ((1 : ℂ) : ExtPlane)) = 1
  rw [hm2]
  rfl

/-- `w_μ` is injective on `S¹`. -/
theorem ltd_wA_inj {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitCircle)
    (h₂ : z₂ ∈ unitCircle) (h : wA μ z₁ = wA μ z₂) : z₁ = z₂ := by
  have := (wAS_bijective μ).1 (show wAS μ (z₁ : ExtPlane) = wAS μ (z₂ : ExtPlane) by
    rw [ltd_wAS_circle hμ h₁, ltd_wAS_circle hμ h₂, h])
  exact OnePoint.coe_injective this

/-- From the Cayley form of the boundary values to `w_μ(C⁻¹ x) = C⁻¹(φ(x))`. -/
theorem ltd_rep {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {φ : ℝ → ℝ}
    (h : ∀ x : ℝ, I * (1 + wA μ (((x : ℂ) - I) / ((x : ℂ) + I))) / (1 - wA μ (((x : ℂ) - I) / ((x : ℂ) + I))) =
      (φ x : ℂ)) (x : ℝ) :
    wA μ (((x : ℂ) - I) / ((x : ℂ) + I)) = (((φ x : ℝ) : ℂ) - I) / (((φ x : ℝ) : ℂ) + I) := by
  have hz := ltd_cay_mem x
  have h1 : (1 : ℂ) ∈ unitCircle := by
    show ‖(1 : ℂ)‖ = 1
    simp
  have hw1 : wA μ (((x : ℂ) - I) / ((x : ℂ) + I)) ≠ 1 := by
    intro hw
    exact ltd_Cinv_ne_one x (ltd_wA_inj hμ hz h1 (hw.trans (ltd_wA_one hμ).symm))
  have hne : (1 : ℂ) - wA μ (((x : ℂ) - I) / ((x : ℂ) + I)) ≠ 0 := sub_ne_zero.2 (Ne.symm hw1)
  have hpI : ((φ x : ℝ) : ℂ) + I ≠ 0 := by
    intro h'
    have := congrArg Complex.im h'
    simp at this
  have hr := h x
  rw [div_eq_iff hne] at hr
  rw [eq_div_iff hpI]
  linear_combination hr

/-- The strip map of `a` with `a(0) = 0`, `a(1) = 1` is `C ∘ w_μ ∘ C⁻¹` on `ℝ` for some `μ` with `‖μ‖∞ ≤ k`. -/
theorem ltd_strip_realize {a : ℝ → ℝ} {S : Set ℝ} (hS : S.Finite) (ha : StrictMono a) (hac : Continuous a)
    (has : Function.Surjective a) (ha0 : a 0 = 0) (ha1 : a 1 = 1) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hloc : ∀ x ∉ S, ∃ s : ℝ, 0 < s ∧ |s - 1| / (s + 1) ≤ k ∧ ∀ᶠ y in 𝓝 x, a y = a x + s * (y - x)) :
    ∃ μ : LinfStarBall, ‖(μ : LinfStar)‖ ≤ k ∧ ∀ x : ℝ,
      wA μ (((x : ℂ) - I) / ((x : ℂ) + I)) = (((a x : ℝ) : ℂ) - I) / (((a x : ℝ) : ℂ) + I) := by
  obtain ⟨hK, hs, hd⟩ := ltd_strip_qc hS ha hac has hk0 hk1 hloc
  obtain ⟨μ, hμn, hμ⟩ := ltd_realize hk0 hk1 hK hs
    (fun z => by apply Complex.ext <;> simp) (by simp [ha0]) (by simp [ha1]) (by simp [ha0]) hd
  refine ⟨μ, hμn, ltd_rep μ.2 (fun x => ?_)⟩
  rw [hμ x]
  simp

/-- The conjugate `μ * λ * μ⁻¹` acts on `ℝ` as `h ∘ g ∘ h⁻¹`. -/
theorem ltd_conj_val {μ l : LinfStar} (hμ : μ ∈ LinfStarBall) (hl : l ∈ LinfStarBall) {h g : ℝ → ℝ}
    (hμr : ∀ x : ℝ, wA μ (((x : ℂ) - I) / ((x : ℂ) + I)) = (((h x : ℝ) : ℂ) - I) / (((h x : ℝ) : ℂ) + I))
    (hlr : ∀ x : ℝ, wA l (((x : ℂ) - I) / ((x : ℂ) + I)) = (((g x : ℝ) : ℂ) - I) / (((g x : ℝ) : ℂ) + I))
    (x : ℝ) :
    (I * (1 + wA (beltramiMul (beltramiMul μ l) (beltramiInv μ)) ((((h x : ℝ) : ℂ) - I) / (((h x : ℝ) : ℂ) + I))) /
      (1 - wA (beltramiMul (beltramiMul μ l) (beltramiInv μ)) ((((h x : ℝ) : ℂ) - I) /
        (((h x : ℝ) : ℂ) + I)))).re = h (g x) := by
  have hμi := bc_beltramiInv_mem_ball hμ
  have hm := bg_mul_mem_ball hl hμ
  have hz := ltd_cay_mem (h x)
  have hv : wA (beltramiMul (beltramiMul μ l) (beltramiInv μ)) ((((h x : ℝ) : ℂ) - I) / (((h x : ℝ) : ℂ) + I)) =
      (((h (g x) : ℝ) : ℂ) - I) / (((h (g x) : ℝ) : ℂ) + I) := by
    rw [ltd_cmul hm hμi _ hz, ← hμr x, ltd_circle_inv' hμ _ (ltd_cay_mem x),
      ltd_cmul hμ hl _ (ltd_cay_mem x), hlr x, hμr (g x)]
  rw [hv, ltd_C_Cinv]
  simp

/-- A kink `μ` and `λ_n → 0` in `L∞` such that the boundary map of `μ * λ_n * μ⁻¹` has `qsRatio ≥ 2` at `-1`. -/
theorem ltd_kink : ∃ μ : LinfStarBall, ∃ ls : ℕ → LinfStarBall,
    Tendsto (fun n => ((ls n : LinfStarBall) : LinfStar)) atTop (𝓝 0) ∧ ∀ n, ∃ t : ℝ, 0 < t ∧
      2 ≤ qsRatio (fun x : ℝ =>
        (I * (1 + wA (beltramiMul (beltramiMul μ (ls n)) (beltramiInv μ)) (((x : ℂ) - I) / ((x : ℂ) + I))) /
          (1 - wA (beltramiMul (beltramiMul μ (ls n)) (beltramiInv μ)) (((x : ℂ) - I) / ((x : ℂ) + I)))).re) (-1) t := by
  -- the kink `h(x) = x + min (x + 1) 0`
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, h = fun x => x + min (x + 1) 0 := ⟨_, rfl⟩
  have hhm : StrictMono h := by
    intro x y hxy
    rw [hh]
    have : min (x + 1) 0 ≤ min (y + 1) 0 := min_le_min (by linarith) le_rfl
    show x + min (x + 1) 0 < y + min (y + 1) 0
    linarith
  have hhc : Continuous h := by
    rw [hh]
    fun_prop
  have hhs : Function.Surjective h := by
    refine hhc.surjective ?_ ?_
    · refine tendsto_id.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [hh]
      simp [min_eq_right (by linarith : (0 : ℝ) ≤ x + 1)]
    · refine tendsto_atBot_mono (fun x => ?_) tendsto_id
      rw [hh]
      simp only [id]
      linarith [min_le_right (x + 1) 0]
  obtain ⟨μ, -, hμr⟩ := ltd_strip_realize (S := {-1}) (finite_singleton _) hhm hhc hhs
    (by rw [hh]; norm_num) (by rw [hh]; norm_num) (k := 1 / 3) (by norm_num) (by norm_num) (by
      intro x hx
      rcases lt_or_gt_of_ne (show x ≠ -1 from hx) with hlt | hgt
      · refine ⟨2, by norm_num, by norm_num, ?_⟩
        filter_upwards [Iio_mem_nhds hlt] with y hy
        rw [hh]
        simp only
        rw [min_eq_left (by linarith [show y < -1 from hy]), min_eq_left (by linarith)]
        ring
      · refine ⟨1, by norm_num, by norm_num, ?_⟩
        filter_upwards [Ioi_mem_nhds hgt] with y hy
        rw [hh]
        simp only
        rw [min_eq_right (by linarith [show -1 < y from hy]), min_eq_right (by linarith)]
        ring)
  -- the shifts `g_δ(x) = x + δ max 0 (min 1 (-2x))`
  have hgen : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∃ l : LinfStarBall, ‖(l : LinfStar)‖ ≤ 2 * δ ∧ ∀ x : ℝ,
      wA l (((x : ℂ) - I) / ((x : ℂ) + I)) =
        (((x + δ * max 0 (min 1 (-2 * x)) : ℝ) : ℂ) - I) / (((x + δ * max 0 (min 1 (-2 * x)) : ℝ) : ℂ) + I) := by
    intro δ hδ hδ4
    obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun x => x + δ * max 0 (min 1 (-2 * x)) := ⟨_, rfl⟩
    have hτ : ∀ x y : ℝ, x < y → max 0 (min 1 (-2 * x)) ≤ max 0 (min 1 (-2 * y)) + 2 * (y - x) := by
      intro x y hxy
      refine max_le (by positivity) ?_
      have : min 1 (-2 * x) ≤ min 1 (-2 * y) + 2 * (y - x) := by
        rcases le_total 1 (-2 * y) with h1 | h1
        · rw [min_eq_left h1]
          linarith [min_le_left 1 (-2 * x)]
        · rw [min_eq_right h1]
          linarith [min_le_right 1 (-2 * x)]
      linarith [le_max_right 0 (min 1 (-2 * y))]
    have hgm : StrictMono g := by
      intro x y hxy
      rw [hg]
      have := hτ x y hxy
      show x + δ * max 0 (min 1 (-2 * x)) < y + δ * max 0 (min 1 (-2 * y))
      nlinarith
    have hgc : Continuous g := by
      rw [hg]
      fun_prop
    have hb : ∀ x : ℝ, x ≤ g x ∧ g x ≤ x + δ := by
      intro x
      rw [hg]
      have h0 := le_max_left 0 (min 1 (-2 * x))
      have h1 : max 0 (min 1 (-2 * x)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
      constructor <;> nlinarith
    have hgs : Function.Surjective g := by
      refine hgc.surjective ?_ ?_
      · exact tendsto_atTop_mono (fun x => (hb x).1) tendsto_id
      · exact tendsto_atBot_mono (fun x => (hb x).2) (tendsto_atBot_add_const_right _ δ tendsto_id)
    obtain ⟨l, hl, hlr⟩ := ltd_strip_realize (S := {-1 / 2, 0}) (by simp) hgm hgc hgs
      (by rw [hg]; norm_num) (by rw [hg]; norm_num) (k := 2 * δ) (by linarith) (by linarith) (by
        intro x hx
        simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx
        rcases lt_or_gt_of_ne hx.1 with hlt | hgt
        · refine ⟨1, by norm_num, by norm_num; linarith, ?_⟩
          filter_upwards [Iio_mem_nhds hlt] with y hy
          rw [hg]
          have hy' : y < -1 / 2 := hy
          have hx' : x < -1 / 2 := hlt
          simp only
          rw [min_eq_left (by linarith), min_eq_left (by linarith), max_eq_right (by norm_num)]
          ring
        · rcases lt_or_gt_of_ne hx.2 with hlt0 | hgt0
          · refine ⟨1 - 2 * δ, by linarith, ?_, ?_⟩
            · rw [abs_of_nonpos (by linarith), div_le_iff₀ (by linarith)]
              nlinarith
            · filter_upwards [Ioo_mem_nhds hgt hlt0] with y hy
              rw [hg]
              obtain ⟨hy1, hy2⟩ := hy
              simp only
              rw [min_eq_right (by linarith), min_eq_right (by linarith), max_eq_right (by linarith),
                max_eq_right (by linarith)]
              ring
          · refine ⟨1, by norm_num, by norm_num; linarith, ?_⟩
            filter_upwards [Ioi_mem_nhds hgt0] with y hy
            rw [hg]
            have hy' : 0 < y := hy
            simp only
            rw [min_eq_right (by linarith), min_eq_right (by linarith), max_eq_left (by linarith),
              max_eq_left (by linarith)]
            ring)
    refine ⟨l, hl, fun x => ?_⟩
    rw [hlr x, hg]
  -- the sequence `δ_n = 1/(8(n+1))`
  have hδpos : ∀ n : ℕ, 0 < 1 / 4 * (1 / ((n : ℝ) + 1)) := fun n => by positivity
  have hδle : ∀ n : ℕ, 1 / 4 * (1 / ((n : ℝ) + 1)) ≤ 1 / 4 := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  choose ls hls hlsr using fun n : ℕ => hgen _ (hδpos n) (hδle n)
  refine ⟨μ, ls, ?_, fun n => ?_⟩
  · refine squeeze_zero_norm hls ?_
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 * (1 / 4 : ℝ))
    simpa [mul_assoc] using this
  · set δ := 1 / 4 * (1 / ((n : ℝ) + 1)) with hδdef
    have hδ := hδpos n
    have hδ4 := hδle n
    refine ⟨δ, hδ, ?_⟩
    have hv := ltd_conj_val μ.2 (ls n).2 hμr (hlsr n)
    have e1 : (-1 : ℝ) + δ = h (-1 + δ) := by rw [hh]; simp only; rw [min_eq_right (by linarith)]; ring
    have e2 : (-1 : ℝ) = h (-1) := by rw [hh]; norm_num
    have e3 : (-1 : ℝ) - δ = h (-1 - δ / 2) := by rw [hh]; simp only; rw [min_eq_left (by linarith)]; ring
    have v1 := hv (-1 + δ)
    have v2 := hv (-1)
    have v3 := hv (-1 - δ / 2)
    rw [← e1] at v1
    rw [← e2] at v2
    rw [← e3] at v3
    show 2 ≤ (_ - _) / (_ - _)
    beta_reduce
    rw [v1, v2, v3, hh]
    simp only
    have t1 : max 0 (min 1 (-2 * (-1 + δ))) = 1 := by
      rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
    have t2 : max 0 (min 1 (-2 * (-1 : ℝ))) = 1 := by norm_num
    have t3 : max 0 (min 1 (-2 * (-1 - δ / 2))) = 1 := by
      rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
    rw [t1, t2, t3]
    rw [min_eq_right (by linarith), min_eq_right (by linarith), min_eq_right (by linarith)]
    rw [le_div_iff₀ (by linarith)]
    linarith

/-! ### Assembly -/

/-- (TT:466, [Leh87, III.3.4]) Left translations are, in general, not even continuous. -/
theorem ltd_exists_leftTrans_not_continuous : ∃ μ : LinfStarBall, ¬ Continuous (leftTrans μ) := by
  obtain ⟨μ, ls, hls, hk⟩ := ltd_kink
  refine ⟨μ, fun hc => ?_⟩
  obtain ⟨ε, hε, hqs⟩ := ltd_near_qs μ (3 / 2) (by norm_num)
  have hVo := ltd_sat_open (μ : LinfStar) ε
  have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  have hPhi : Continuous Phi := continuous_quotient_mk'
  have hlim : Tendsto (fun n => Phi (ls n)) atTop (𝓝 (Phi ⟨0, h0⟩)) :=
    (hPhi.tendsto _).comp (tendsto_subtype_rng.2 hls)
  have hL := (hc.tendsto _).comp hlim
  have hμV : leftTrans μ (Phi ⟨0, h0⟩) ∈
      {p : T1 | ∃ ν : LinfStarBall, Phi ν = p ∧ ‖(ν : LinfStar) - μ‖ < ε} := by
    rw [gtr_leftTrans_phi]
    refine ⟨μ, Quotient.sound ?_, by simpa using hε⟩
    intro z hz
    show wA (μ : LinfStar) z = wA (beltramiMul (μ : LinfStar) 0) z
    rw [ltd_circle_mul μ.2 h0 z hz]
    show wA (μ : LinfStar) z = wA (μ : LinfStar) (finPart (wAS 0 (z : ExtPlane)))
    rw [grp_wAS_zero]
    rfl
  obtain ⟨n, hn⟩ := (Filter.Tendsto.eventually_mem hL (hVo.mem_nhds hμV)).exists
  obtain ⟨ν, hνe, hνn⟩ := hn
  rw [Function.comp_apply, gtr_leftTrans_phi] at hνe
  have hrel := Quotient.exact hνe
  obtain ⟨t, ht, h2⟩ := hk n
  have hμi := bc_beltramiInv_mem_ball μ.2
  have hm := bg_mul_mem_ball (ls n).2 μ.2
  have hfun : (fun x : ℝ =>
      (I * (1 + wA (beltramiMul ν (beltramiInv μ)) (((x : ℂ) - I) / ((x : ℂ) + I))) /
        (1 - wA (beltramiMul ν (beltramiInv μ)) (((x : ℂ) - I) / ((x : ℂ) + I)))).re) = fun x : ℝ =>
      (I * (1 + wA (beltramiMul (beltramiMul μ (ls n)) (beltramiInv μ)) (((x : ℂ) - I) / ((x : ℂ) + I))) /
        (1 - wA (beltramiMul (beltramiMul μ (ls n)) (beltramiInv μ)) (((x : ℂ) - I) / ((x : ℂ) + I)))).re := by
    funext x
    have hz := ltd_cay_mem x
    have he : wA (beltramiMul ν (beltramiInv μ)) (((x : ℂ) - I) / ((x : ℂ) + I)) =
        wA (beltramiMul (beltramiMul μ (ls n)) (beltramiInv μ)) (((x : ℂ) - I) / ((x : ℂ) + I)) := by
      rw [ltd_circle_mul ν.2 hμi _ hz, ltd_circle_mul hm hμi _ hz]
      exact hrel _ (ltd_wA_mem hμi hz)
    rw [he]
  have hq := ((hqs ν hνn).2.2.2.2 (-1) t ht).2
  rw [hfun] at hq
  linarith

/-- (TT:466, [Leh87, III.3.4]) Left translations are, in general, not even continuous. -/
theorem exists_leftTrans_not_continuous : ∃ μ : LinfStarBall, ¬ Continuous (leftTrans μ) :=
  ltd_exists_leftTrans_not_continuous

end TakhtajanTeo
