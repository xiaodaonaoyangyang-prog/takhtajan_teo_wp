import TakhtajanTeo.Ch2.S4_WPPotential
import TakhtajanTeo.Ch2.S2_Remark22
import TakhtajanTeo.Ch1.WRegFoundation
import TakhtajanTeo.Ch1.GroupB1
import TakhtajanTeo.Ch1.WeldingUniqueness
import TakhtajanTeo.Appendix.AppACont

/-!
# Chapter 2, §4 — the welding identity (4.1) (TT:5318)

Host of `eq_4_1` (relocated from `Ch2/S4_WPPotential`).

**Route.**
- `w_{(εν)*κ} = w_{εν} ∘ w_κ` on `ℂ̄` (`grp_wAS_mul`) and `g_μ = w^μ ∘ w_μ⁻¹` on `𝔻*`
  (`gMu_sphere_factorization`) give `g_ε ∘ w_{εν} = v_ε ∘ g` off the two pole points (`e41_weld`).
- The `∂_z`-Schwarzian chain rules (`e41_schw_left`, `e41_schw_right`), applied to the two sides of the welding
  identity on a neighbourhood of `z`, give the Schwarzian identity.
- Regularity: `w_{εν}` is `C³` with `∂_z w_{εν} ≠ 0` off its pole (W-REG model A, `grp25_regular_ext`);
  `v_ε = g_ε ∘ w_{εν} ∘ g⁻¹` near `g(z)`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-- The `∂_z`-Schwarzian depends only on the germ. -/
theorem e41_schw_congr {f₁ f₂ : ℂ → ℂ} {z : ℂ} (h : f₁ =ᶠ[𝓝 z] f₂) :
    schwarzianDz f₁ z = schwarzianDz f₂ z := by
  have h1 : dz f₁ =ᶠ[𝓝 z] dz f₂ := h.eventuallyEq_nhds.mono fun u hu => (t203_c1_dz_congr hu).1
  have h2 : dz (dz f₁) =ᶠ[𝓝 z] dz (dz f₂) := h1.eventuallyEq_nhds.mono fun u hu => (t203_c1_dz_congr hu).1
  have h3 : (fun u => dz (dz f₁) u / dz f₁ u) =ᶠ[𝓝 z] (fun u => dz (dz f₂) u / dz f₂ u) :=
    h2.mp (h1.mono fun u hu1 hu2 => by dsimp only; rw [hu1, hu2])
  show dz (fun u => dz (dz f₁) u / dz f₁ u) z - (1 / 2) * (dz (dz f₁) z / dz f₁ z) ^ 2 =
    dz (fun u => dz (dz f₂) u / dz f₂ u) z - (1 / 2) * (dz (dz f₂) z / dz f₂ z) ^ 2
  rw [(t203_c1_dz_congr h3).1, h1.eq_of_nhds, h2.eq_of_nhds]

/-- `∂_z` of a sum. -/
theorem e41_dz_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz (fun u => f u + g u) z = dz f z + dz g z := by
  rw [t203_dz_of_hasFDerivAt (hf.hasFDerivAt.fun_add hg.hasFDerivAt), t203_dz_of_hasFDerivAt hf.hasFDerivAt,
    t203_dz_of_hasFDerivAt hg.hasFDerivAt]
  simp only [add_apply]
  ring

/-- `∂_z` of a product. -/
theorem e41_dz_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz (fun u => f u * g u) z = dz f z * g z + f z * dz g z := by
  rw [t203_dz_of_hasFDerivAt (hf.hasFDerivAt.fun_mul hg.hasFDerivAt), t203_dz_of_hasFDerivAt hf.hasFDerivAt,
    t203_dz_of_hasFDerivAt hg.hasFDerivAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Real differentiability of a quotient. -/
theorem e41_diff_div {N D : ℂ → ℂ} {z : ℂ} (hN : DifferentiableAt ℝ N z) (hD : DifferentiableAt ℝ D z)
    (h0 : D z ≠ 0) : DifferentiableAt ℝ (fun u => N u / D u) z := by
  have hinv : DifferentiableAt ℝ (fun u => (D u)⁻¹) z :=
    ((hasDerivAt_inv h0).comp_hasFDerivAt z hD.hasFDerivAt).differentiableAt
  have hm : DifferentiableAt ℝ (fun u => N u * (D u)⁻¹) z := hN.mul hinv
  simpa only [div_eq_mul_inv] using hm

/-- `∂_z (G ∘ f) = G'(f) ∂_z f` for `G` holomorphic. -/
theorem e41_dz_hol_left {G f : ℂ → ℂ} {u : ℂ} (hG : DifferentiableAt ℂ G (f u)) (hf : DifferentiableAt ℝ f u) :
    dz (fun x => G (f x)) u = deriv G (f u) * dz f u := by
  show dz (G ∘ f) u = _
  rw [eq6_2_dz_comp hf (hG.restrictScalars ℝ), (cauchyRiemann_iff.1 hG).2, dz_eq_deriv hG]
  ring

/-- `∂_z (v ∘ g) = ∂_z v (g) g'` for `g` holomorphic. -/
theorem e41_dz_hol_right {v g : ℂ → ℂ} {u : ℂ} (hg : DifferentiableAt ℂ g u) (hv : DifferentiableAt ℝ v (g u)) :
    dz (fun x => v (g x)) u = dz v (g u) * deriv g u := by
  show dz (v ∘ g) u = _
  rw [eq6_2_dz_comp (hg.restrictScalars ℝ) hv, dz_conj (hg.restrictScalars ℝ), (cauchyRiemann_iff.1 hg).2,
    dz_eq_deriv hg]
  simp

/-- `∂_z f` is `C^m` where `f` is `C^{m+1}`. -/
theorem e41_dz_contDiffAt {f : ℂ → ℂ} {u : ℂ} {m n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f u) (hmn : m + 1 ≤ n) :
    ContDiffAt ℝ m (dz f) u := by
  have hd : ContDiffAt ℝ m (fderiv ℝ f) u := hf.fderiv_right hmn
  have e : dz f = fun x => (fderiv ℝ f x 1 - I * fderiv ℝ f x I) / 2 := rfl
  rw [e]
  exact ((hd.clm_apply contDiffAt_const).sub (contDiffAt_const.mul (hd.clm_apply contDiffAt_const))).div_const _

/-- Chain rule, holomorphic map on the left: `𝒮_z(h ∘ w) = 𝒮(h) ∘ w · w_z² + 𝒮_z(w)`. -/
theorem e41_schw_left {h w : ℂ → ℂ} {z : ℂ} (hh : AnalyticAt ℂ h (w z)) (hh' : deriv h (w z) ≠ 0)
    (hw : ContDiffAt ℝ 3 w z) (hwz : dz w z ≠ 0) :
    schwarzianDz (h ∘ w) z = schwarzianHol h (w z) * dz w z ^ 2 + schwarzianDz w z := by
  obtain ⟨q, hq⟩ : ∃ q : ℂ → ℂ, q = fun x => deriv (deriv h) x / deriv h x := ⟨_, rfl⟩
  have hU2 : ContDiffAt ℝ 2 (dz w) z := e41_dz_contDiffAt hw (by norm_num)
  have hU1 : ContDiffAt ℝ 1 (dz (dz w)) z := e41_dz_contDiffAt hU2 (by norm_num)
  have hwe : ∀ᶠ u in 𝓝 z, ContDiffAt ℝ 3 w u := hw.eventually (by simp)
  have hha : ∀ᶠ u in 𝓝 z, AnalyticAt ℂ h (w u) := hw.continuousAt.eventually hh.eventually_analyticAt
  have hdh : ∀ᶠ u in 𝓝 z, deriv h (w u) ≠ 0 :=
    (hh.deriv.continuousAt.comp (g := deriv h) hw.continuousAt).eventually_ne hh'
  have ha0 : ∀ᶠ u in 𝓝 z, dz w u ≠ 0 := hU2.continuousAt.eventually_ne hwz
  have hE1 : dz (h ∘ w) =ᶠ[𝓝 z] fun u => deriv h (w u) * dz w u := by
    filter_upwards [hwe, hha] with u hu1 hu2
    exact e41_dz_hol_left hu2.differentiableAt (hu1.differentiableAt (by norm_num))
  have hE2 : dz (dz (h ∘ w)) =ᶠ[𝓝 z]
      fun u => deriv (deriv h) (w u) * dz w u * dz w u + deriv h (w u) * dz (dz w) u := by
    filter_upwards [hE1.eventuallyEq_nhds, hwe, hha] with u hu1 hu2 hu3
    have hwd : DifferentiableAt ℝ w u := hu2.differentiableAt (by norm_num)
    have had : DifferentiableAt ℝ (dz w) u :=
      (e41_dz_contDiffAt hu2 (m := 2) (by norm_num)).differentiableAt (by norm_num)
    have hgd : DifferentiableAt ℝ (fun x => deriv h (w x)) u :=
      (hu3.deriv.differentiableAt.restrictScalars ℝ).comp (f := w) u hwd
    rw [(t203_c1_dz_congr hu1).1, e41_dz_mul hgd had, e41_dz_hol_left hu3.deriv.differentiableAt hwd]
  have hR : (fun u => dz (dz (h ∘ w)) u / dz (h ∘ w) u) =ᶠ[𝓝 z]
      fun u => q (w u) * dz w u + dz (dz w) u / dz w u := by
    filter_upwards [hE1, hE2, hdh, ha0] with u hu1 hu2 hu3 hu4
    rw [hu1, hu2]
    simp only [hq]
    field_simp
  have hwd0 : DifferentiableAt ℝ w z := hw.differentiableAt (by norm_num)
  have had0 : DifferentiableAt ℝ (dz w) z := hU2.differentiableAt (by norm_num)
  have hbd0 : DifferentiableAt ℝ (dz (dz w)) z := hU1.differentiableAt (by norm_num)
  have hqd : DifferentiableAt ℂ q (w z) := by
    rw [hq]
    exact hh.deriv.deriv.differentiableAt.div hh.deriv.differentiableAt hh'
  have hqw : DifferentiableAt ℝ (fun u => q (w u)) z := (hqd.restrictScalars ℝ).comp (f := w) z hwd0
  have hqz : q (w z) = deriv (deriv h) (w z) / deriv h (w z) := by rw [hq]
  show dz (fun u => dz (dz (h ∘ w)) u / dz (h ∘ w) u) z - (1 / 2) * (dz (dz (h ∘ w)) z / dz (h ∘ w) z) ^ 2 =
    (deriv (fun x => deriv (deriv h) x / deriv h x) (w z) -
        (1 / 2) * (deriv (deriv h) (w z) / deriv h (w z)) ^ 2) * dz w z ^ 2 +
      (dz (fun u => dz (dz w) u / dz w u) z - (1 / 2) * (dz (dz w) z / dz w z) ^ 2)
  rw [← hq, (t203_c1_dz_congr hR).1, hE1.eq_of_nhds, hE2.eq_of_nhds, e41_dz_add (show DifferentiableAt ℝ (fun u => q (w u) * dz w u) z from hqw.mul had0)
      (e41_diff_div hbd0 had0 hwz),
    e41_dz_mul hqw had0, e41_dz_hol_left hqd hwd0, hqz]
  field_simp
  ring

/-- Chain rule, holomorphic map on the right: `𝒮_z(v ∘ g) = 𝒮_z(v) ∘ g · g'² + 𝒮(g)`. -/
theorem e41_schw_right {v g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) (hg' : deriv g z ≠ 0)
    (hv : ContDiffAt ℝ 3 v (g z)) (hvz : dz v (g z) ≠ 0) :
    schwarzianDz (v ∘ g) z = schwarzianDz v (g z) * deriv g z ^ 2 + schwarzianHol g z := by
  obtain ⟨q, hq⟩ : ∃ q : ℂ → ℂ, q = fun x => deriv (deriv g) x / deriv g x := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℂ → ℂ, r = fun y => dz (dz v) y / dz v y := ⟨_, rfl⟩
  have hgd : DifferentiableAt ℂ g z := hg.differentiableAt
  have hV2 : ContDiffAt ℝ 2 (dz v) (g z) := e41_dz_contDiffAt hv (by norm_num)
  have hV1 : ContDiffAt ℝ 1 (dz (dz v)) (g z) := e41_dz_contDiffAt hV2 (by norm_num)
  have hga : ∀ᶠ u in 𝓝 z, AnalyticAt ℂ g u := hg.eventually_analyticAt
  have hve : ∀ᶠ u in 𝓝 z, ContDiffAt ℝ 3 v (g u) := hgd.continuousAt.eventually (hv.eventually (by simp))
  have hg0 : ∀ᶠ u in 𝓝 z, deriv g u ≠ 0 := hg.deriv.continuousAt.eventually_ne hg'
  have hA0 : ∀ᶠ u in 𝓝 z, dz v (g u) ≠ 0 :=
    (hV2.continuousAt.comp (g := dz v) hgd.continuousAt).eventually_ne hvz
  have hE1 : dz (v ∘ g) =ᶠ[𝓝 z] fun u => dz v (g u) * deriv g u := by
    filter_upwards [hga, hve] with u hu1 hu2
    exact e41_dz_hol_right hu1.differentiableAt (hu2.differentiableAt (by norm_num))
  have hE2 : dz (dz (v ∘ g)) =ᶠ[𝓝 z]
      fun u => dz (dz v) (g u) * deriv g u * deriv g u + dz v (g u) * deriv (deriv g) u := by
    filter_upwards [hE1.eventuallyEq_nhds, hga, hve] with u hu1 hu2 hu3
    have hAd : DifferentiableAt ℝ (dz v) (g u) :=
      (e41_dz_contDiffAt hu3 (m := 2) (by norm_num)).differentiableAt (by norm_num)
    have hAg : DifferentiableAt ℝ (fun x => dz v (g x)) u :=
      hAd.comp (f := g) u (hu2.differentiableAt.restrictScalars ℝ)
    have hg'd : DifferentiableAt ℝ (deriv g) u := hu2.deriv.differentiableAt.restrictScalars ℝ
    rw [(t203_c1_dz_congr hu1).1, e41_dz_mul hAg hg'd, e41_dz_hol_right hu2.differentiableAt hAd,
      dz_eq_deriv hu2.deriv.differentiableAt]
  have hR : (fun u => dz (dz (v ∘ g)) u / dz (v ∘ g) u) =ᶠ[𝓝 z] fun u => r (g u) * deriv g u + q u := by
    filter_upwards [hE1, hE2, hg0, hA0] with u hu1 hu2 hu3 hu4
    rw [hu1, hu2]
    simp only [hr, hq]
    field_simp
  have hrd : DifferentiableAt ℝ r (g z) := by
    rw [hr]
    exact e41_diff_div (hV1.differentiableAt (by norm_num)) (hV2.differentiableAt (by norm_num)) hvz
  have hrg : DifferentiableAt ℝ (fun x => r (g x)) z := hrd.comp (f := g) z (hgd.restrictScalars ℝ)
  have hg'd0 : DifferentiableAt ℝ (deriv g) z := hg.deriv.differentiableAt.restrictScalars ℝ
  have hqd : DifferentiableAt ℂ q z := by
    rw [hq]
    exact hg.deriv.deriv.differentiableAt.div hg.deriv.differentiableAt hg'
  have hrz : r (g z) = dz (dz v) (g z) / dz v (g z) := by rw [hr]
  have hqz : q z = deriv (deriv g) z / deriv g z := by rw [hq]
  show dz (fun u => dz (dz (v ∘ g)) u / dz (v ∘ g) u) z - (1 / 2) * (dz (dz (v ∘ g)) z / dz (v ∘ g) z) ^ 2 =
    (dz (fun u => dz (dz v) u / dz v u) (g z) - (1 / 2) * (dz (dz v) (g z) / dz v (g z)) ^ 2) * deriv g z ^ 2 +
      (deriv (fun x => deriv (deriv g) x / deriv g x) z - (1 / 2) * (deriv (deriv g) z / deriv g z) ^ 2)
  rw [← hr, ← hq, (t203_c1_dz_congr hR).1, hE1.eq_of_nhds, hE2.eq_of_nhds,
    e41_dz_add (show DifferentiableAt ℝ (fun u => r (g u) * deriv g u) z from hrg.mul hg'd0)
      (hqd.restrictScalars ℝ), e41_dz_mul hrg hg'd0, e41_dz_hol_right hgd hrd,
    dz_eq_deriv hqd, dz_eq_deriv hg.deriv.differentiableAt, hrz]
  field_simp
  ring

/-- `g_μ` is holomorphic on `𝔻*` with nonvanishing derivative. -/
theorem e41_g_holo {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    AnalyticAt ℂ (gsans μ) z ∧ deriv (gsans μ) z ≠ 0 := by
  rw [(r22_fsans_gsans hμ).2]
  obtain ⟨-, -, -, -, -, -, hgi⟩ := gMu_isWelding hμ
  have hU : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  exact ⟨hgi.1.analyticAt (hU.mem_nhds hz), LiZhongQC.deriv_ne_zero_of_injOn hU hgi.1 hgi.2.1 hz⟩

/-- W-REG model A at a point of `𝔻*` off the pole of `w_{εν}`: `C³`, `∂_z w ≠ 0`, and `w(z) ∈ 𝔻*`. -/
theorem e41_w_regular {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) {e : ℂ} (he : ‖e‖ * ‖ν‖ < 1) {z : ℂ}
    (hz : z ∈ unitDiscExterior) (hp : wAS (e • ν) (z : ExtPlane) ≠ extInf) :
    ContDiffAt ℝ 3 (wA (e • ν)) z ∧ dz (wA (e • ν)) z ≠ 0 ∧ wA (e • ν) z ∈ unitDiscExterior := by
  have hU : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hμb : e • ν ∈ LinfStarBall := by
    show e • ν ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, norm_smul]
    exact he
  -- joint continuity of `(e, z) ↦ wAS (e • ν) z` at the point
  have hjc : ContinuousAt (fun p : ℂ × ℂ => wAS (p.1 • ν) (p.2 : ExtPlane)) (e, z) := by
    have hin : ContinuousAt (fun p : ℂ × ℂ => ((p.1 • ν, (p.2 : ExtPlane)) : LinfStar × ExtPlane)) (e, z) :=
      ((continuous_fst.smul continuous_const).prodMk (OnePoint.continuous_coe.comp continuous_snd)).continuousAt
    have hS : LinfStarBall ×ˢ (univ : Set ExtPlane) ∈ 𝓝 ((e • ν, (z : ExtPlane)) : LinfStar × ExtPlane) :=
      prod_mem_nhds (isOpen_ball.mem_nhds hμb) univ_mem
    exact ((AppA.acc_wAS_cont.continuousAt hS).comp (f := fun p : ℂ × ℂ =>
      ((p.1 • ν, (p.2 : ExtPlane)) : LinfStar × ExtPlane)) hin)
  have hN : {p : ℂ × ℂ | ‖p.1‖ * ‖ν‖ < 1 ∧ p.2 ∈ unitDiscExterior ∧ wAS (p.1 • ν) (p.2 : ExtPlane) ≠ extInf} ∈
      𝓝 (e, z) := by
    have h1 : ∀ᶠ p : ℂ × ℂ in 𝓝 (e, z), ‖p.1‖ * ‖ν‖ < 1 :=
      ((continuous_norm.comp continuous_fst).mul continuous_const).continuousAt.eventually_lt
        continuousAt_const he
    have h2 : ∀ᶠ p : ℂ × ℂ in 𝓝 (e, z), p.2 ∈ unitDiscExterior :=
      continuous_snd.continuousAt.eventually_mem (hU.mem_nhds hz)
    have h3 : ∀ᶠ p : ℂ × ℂ in 𝓝 (e, z), wAS (p.1 • ν) (p.2 : ExtPlane) ≠ extInf := hjc.eventually_ne hp
    filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
    exact ⟨hp1, hp2, hp3⟩
  have hJ : ContDiffAt ℝ 3 (fun p : ℂ × ℂ => wA (p.1 • ν) p.2) (e, z) :=
    (wr_joint_contDiff_A hν).contDiffAt hN
  have hC : ContDiffAt ℝ 3 (wA (e • ν)) z :=
    hJ.comp (f := fun u : ℂ => ((e, u) : ℂ × ℂ)) z (contDiffAt_const.prodMk contDiffAt_id)
  have hμh : e • ν ∈ harmonicBeltrami := Submodule.smul_mem _ e hν
  have hμ1 : ‖e • ν‖ < 1 := by rw [norm_smul]; exact he
  have hmem : wAS (e • ν) (z : ExtPlane) ∈ toExt unitDiscExterior ∪ {extInf} := by
    rw [← (wA_mapsTo hμb).2.1]
    exact mem_image_of_mem _ (Or.inl ⟨z, hz, rfl⟩)
  have hD : wA (e • ν) z ∈ unitDiscExterior := by
    rcases hmem with hm | hm
    · obtain ⟨y, hy, hyz⟩ := hm
      have hw : wA (e • ν) z = y := by
        show finPart (wAS (e • ν) (z : ExtPlane)) = y
        rw [← hyz]
        rfl
      rw [hw]
      exact hy
    · exact absurd hm hp
  exact ⟨hC, (grp25_regular_ext hμh hμ1 hz hp).2, hD⟩

/-- The welding identity `g_ε ∘ w_{εν} = v_ε ∘ g` at a point of `𝔻*` off the two pole points. -/
theorem e41_weld {κ μ : LinfStar} (hκ : κ ∈ LinfStarBall) (hμ : μ ∈ LinfStarBall) {z : ℂ}
    (hz : z ∈ unitDiscExterior) (hz0 : wAS κ extInf ≠ (z : ExtPlane)) (hp : wAS μ (z : ExtPlane) ≠ extInf) :
    gsans (beltramiMul μ κ) (wA μ z) =
      (fsans (beltramiMul μ κ) ∘ Function.invFun (fsans κ)) (gsans κ z) := by
  have hlb : beltramiMul μ κ ∈ LinfStarBall := (wA_mul hκ hμ).1
  have hcomp : wAS (beltramiMul μ κ) = wAS μ ∘ wAS κ := (wA_mul hκ hμ).2.1
  have hU : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  -- `y = w_μ(z)` is a finite point of `𝔻*`
  have hmem : wAS μ (z : ExtPlane) ∈ toExt unitDiscExterior ∪ {extInf} := by
    rw [← (wA_mapsTo hμ).2.1]
    exact mem_image_of_mem _ (Or.inl ⟨z, hz, rfl⟩)
  obtain ⟨y, hyD, hyz⟩ : ∃ y : ℂ, y ∈ unitDiscExterior ∧ (y : ExtPlane) = wAS μ (z : ExtPlane) := by
    rcases hmem with hm | hm
    · obtain ⟨y, hy, hyz⟩ := hm
      exact ⟨y, hy, hyz⟩
    · exact absurd hm hp
  have hwy : wA μ z = y := by
    show finPart (wAS μ (z : ExtPlane)) = y
    rw [← hyz]
    rfl
  -- `x₀ = w_κ⁻¹(z)` is a finite point
  obtain ⟨X, hX⟩ := (wAS_bijective κ).2 (z : ExtPlane)
  have hXne : X ≠ extInf := by
    intro h
    rw [h] at hX
    exact hz0 hX
  obtain ⟨x₀, hx₀⟩ := OnePoint.ne_infty_iff_exists.1 hXne
  rw [← hx₀] at hX
  have hinvκ : Function.invFun (wAS κ) (z : ExtPlane) = (x₀ : ExtPlane) := by
    rw [← hX]
    exact Function.leftInverse_invFun (wAS_bijective κ).1 _
  have hlx : wAS (beltramiMul μ κ) (x₀ : ExtPlane) = (y : ExtPlane) := by
    rw [hcomp, Function.comp_apply, hX, hyz]
  have hinvl : Function.invFun (wAS (beltramiMul μ κ)) (y : ExtPlane) = (x₀ : ExtPlane) := by
    rw [← hlx]
    exact Function.leftInverse_invFun (wAS_bijective _).1 _
  -- the two sphere factorizations
  have hgκ : (gMu κ z : ExtPlane) = wB κ (x₀ : ExtPlane) := by
    rw [gMu_sphere_factorization hκ hz, hinvκ]
  have hgl : (gMu (beltramiMul μ κ) y : ExtPlane) = wB (beltramiMul μ κ) (x₀ : ExtPlane) := by
    rw [gMu_sphere_factorization hlb hyD, hinvl]
  have hc0 : gMu κ z ≠ 0 := gMu_exterior_ne_zero hκ hz
  -- `invFun (fB κ)` returns `x₀` at `g(z)`
  have hfx : fB κ x₀ = gMu κ z := by
    show finPart (wB κ (x₀ : ExtPlane)) = gMu κ z
    rw [← hgκ]
    rfl
  have hinvf : Function.invFun (fB κ) (gMu κ z) = x₀ := by
    have ht : fB κ (Function.invFun (fB κ) (gMu κ z)) = gMu κ z := Function.invFun_eq ⟨x₀, hfx⟩
    obtain ⟨t, htd⟩ : ∃ t, t = Function.invFun (fB κ) (gMu κ z) := ⟨_, rfl⟩
    rw [← htd] at ht ⊢
    have ht' : finPart (wB κ (t : ExtPlane)) = gMu κ z := ht
    rcases eq_or_ne (wB κ (t : ExtPlane)) extInf with h | h
    · rw [h] at ht'
      exact absurd ht'.symm hc0
    · obtain ⟨q, hq⟩ := OnePoint.ne_infty_iff_exists.1 h
      rw [← hq] at ht'
      have hq' : q = gMu κ z := ht'
      have hB : wB κ (t : ExtPlane) = wB κ (x₀ : ExtPlane) := by rw [← hq, hq', hgκ]
      exact OnePoint.coe_injective ((wB_bijective κ).1 hB)
  rw [(r22_fsans_gsans hlb).2, (r22_fsans_gsans hlb).1, (r22_fsans_gsans hκ).1, (r22_fsans_gsans hκ).2,
    Function.comp_apply, hinvf, hwy]
  show gMu (beltramiMul μ κ) y = finPart (wB (beltramiMul μ κ) (x₀ : ExtPlane))
  rw [← hgl]
  rfl

/-- The welding identity holds on a neighbourhood of such a point. -/
theorem e41_weld_ev {κ μ : LinfStar} (hκ : κ ∈ LinfStarBall) (hμ : μ ∈ LinfStarBall) {z : ℂ}
    (hz : z ∈ unitDiscExterior) (hz0 : wAS κ extInf ≠ (z : ExtPlane)) (hp : wAS μ (z : ExtPlane) ≠ extInf) :
    (gsans (beltramiMul μ κ) ∘ wA μ) =ᶠ[𝓝 z]
      ((fsans (beltramiMul μ κ) ∘ Function.invFun (fsans κ)) ∘ gsans κ) := by
  have hU : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have h1 : ∀ᶠ u : ℂ in 𝓝 z, u ∈ unitDiscExterior := hU.mem_nhds hz
  have h2 : ∀ᶠ u : ℂ in 𝓝 z, (u : ExtPlane) ≠ wAS κ extInf :=
    OnePoint.continuous_coe.continuousAt.eventually_ne (Ne.symm hz0)
  have h3 : ∀ᶠ u : ℂ in 𝓝 z, wAS μ (u : ExtPlane) ≠ extInf :=
    ((wAS_continuous hμ).comp OnePoint.continuous_coe).continuousAt.eventually_ne hp
  filter_upwards [h1, h2, h3] with u hu1 hu2 hu3
  exact e41_weld hκ hμ hu1 (Ne.symm hu2) hu3

/-- `v_ε` is `C³` with `∂_z v_ε ≠ 0` at `g(z)` (locally `v_ε = g_ε ∘ w_{εν} ∘ g⁻¹`). -/
theorem e41_ve_regular {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) {e : ℂ}
    (he : ‖e‖ * ‖ν‖ < 1) {z : ℂ} (hz : z ∈ unitDiscExterior) (hz0 : wAS κ extInf ≠ (z : ExtPlane))
    (hp : wAS (e • ν) (z : ExtPlane) ≠ extInf) :
    ContDiffAt ℝ 3 (fsans (beltramiMul (e • ν) κ) ∘ Function.invFun (fsans κ)) (gsans κ z) ∧
      dz (fsans (beltramiMul (e • ν) κ) ∘ Function.invFun (fsans κ)) (gsans κ z) ≠ 0 := by
  have hμb : e • ν ∈ LinfStarBall := by
    show e • ν ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, norm_smul]
    exact he
  have hlb : beltramiMul (e • ν) κ ∈ LinfStarBall := (wA_mul hκ hμb).1
  obtain ⟨hwc, hwz, hwD⟩ := e41_w_regular hν he hz hp
  obtain ⟨hga, hgd'⟩ := e41_g_holo hκ hz
  obtain ⟨hgea, hged⟩ := e41_g_holo hlb hwD
  have hW := e41_weld_ev hκ hμb hz hz0 hp
  obtain ⟨gk, hgk⟩ : ∃ f : ℂ → ℂ, f = gsans κ := ⟨_, rfl⟩
  obtain ⟨ge, hge⟩ : ∃ f : ℂ → ℂ, f = gsans (beltramiMul (e • ν) κ) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ f : ℂ → ℂ, f = wA (e • ν) := ⟨_, rfl⟩
  obtain ⟨ve, hve⟩ : ∃ f : ℂ → ℂ, f = fsans (beltramiMul (e • ν) κ) ∘ Function.invFun (fsans κ) := ⟨_, rfl⟩
  rw [← hgk, ← hve]
  rw [← hgk, ← hge, ← hw, ← hve] at hW
  rw [← hgk] at hga hgd'
  rw [← hge, ← hw] at hgea hged
  rw [← hw] at hwc hwz
  -- the holomorphic local inverse `P.symm` of `g` at `z`
  have hgC : ContDiffAt ℂ 3 gk z := hga.contDiffAt
  have hn : (3 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hf' : HasFDerivAt gk (((ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv gk z) hgd')) :
      ℂ ≃L[ℂ] ℂ) : ℂ →L[ℂ] ℂ) z := by
    convert hga.differentiableAt.hasDerivAt.hasFDerivAt using 1
    ext1
    simp
  have hsrc := hgC.mem_toOpenPartialHomeomorph_source hf' hn
  have htgt := hgC.image_mem_toOpenPartialHomeomorph_target hf' hn
  have hPinv : ContDiffAt ℂ 3 (hgC.toOpenPartialHomeomorph gk hf' hn).symm (gk z) := hgC.to_localInverse hf' hn
  obtain ⟨P, hP⟩ : ∃ P : OpenPartialHomeomorph ℂ ℂ, P = hgC.toOpenPartialHomeomorph gk hf' hn := ⟨_, rfl⟩
  have hPc : (P : ℂ → ℂ) = gk := by rw [hP]; rfl
  rw [← hP] at hsrc htgt hPinv
  have hRI : ∀ᶠ y in 𝓝 (gk z), gk (P.symm y) = y := by
    filter_upwards [P.eventually_right_inverse htgt] with y hy
    rw [← hPc]
    exact hy
  have hPz : P.symm (gk z) = z := by
    have h := P.left_inv hsrc
    rw [hPc] at h
    exact h
  have hc' : Tendsto P.symm (𝓝 (gk z)) (𝓝 z) := by
    have h := P.continuousAt_symm htgt
    rw [ContinuousAt, hPz] at h
    exact h
  have hEq : ve =ᶠ[𝓝 (gk z)] fun y => ge (w (P.symm y)) := by
    filter_upwards [hRI, hc'.eventually hW] with y h1 h2
    calc ve y = ve (gk (P.symm y)) := by rw [h1]
      _ = ge (w (P.symm y)) := h2.symm
  -- regularity of `ge ∘ w` at `z`
  have hF : ContDiffAt ℝ 3 (ge ∘ w) z :=
    (hgea.contDiffAt.restrict_scalars ℝ).comp (f := w) z hwc
  have hF' : ContDiffAt ℝ 3 (ge ∘ w) (P.symm (gk z)) := by rw [hPz]; exact hF
  have hPd : DifferentiableAt ℂ P.symm (gk z) := hPinv.differentiableAt (by norm_num)
  have hgd2 : DifferentiableAt ℂ gk (P.symm (gk z)) := by rw [hPz]; exact hga.differentiableAt
  -- `(P.symm)' ≠ 0`
  have hd1 : deriv (gk ∘ P.symm) (gk z) = 1 := by
    have hRI' : (gk ∘ P.symm) =ᶠ[𝓝 (gk z)] id := hRI
    rw [hRI'.deriv_eq, deriv_id]
  have hd2 : deriv (gk ∘ P.symm) (gk z) = deriv gk (P.symm (gk z)) * deriv P.symm (gk z) :=
    deriv_comp (gk z) hgd2 hPd
  have hPd0 : deriv P.symm (gk z) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hd2
    rw [hd2] at hd1
    exact zero_ne_one hd1
  refine ⟨(hF'.comp (f := P.symm) (gk z) (hPinv.restrict_scalars ℝ)).congr_of_eventuallyEq hEq, ?_⟩
  rw [(t203_c1_dz_congr hEq).1]
  have hD := e41_dz_hol_right (v := ge ∘ w) hPd (hF'.differentiableAt (by norm_num))
  change dz (fun x => (ge ∘ w) (P.symm x)) (gk z) ≠ 0
  rw [hD, hPz]
  have hD2 := e41_dz_hol_left (G := ge) (f := w) hgea.differentiableAt (hwc.differentiableAt (by norm_num))
  change dz (fun x => ge (w x)) z * deriv P.symm (gk z) ≠ 0
  rw [hD2]
  exact mul_ne_zero (mul_ne_zero hged hwz) hPd0

/-- **(4.1)** (TT:5318). Let `[κ] ∈ T₀(1)`, `ν ∈ H^{-1,1}(𝔻*)`, and let `g_ε^{-1} ∘ f^ε = w_{εν} ∘ w_κ`, with
`f = f⁰`, `g = g₀` and `v_ε = f^ε ∘ f⁻¹`.

Then `g_ε ∘ w_{εν} = v_ε ∘ g`, so on `𝔻*`:
`𝒮(g_ε) ∘ w_{εν} (w_{εν})_z² + 𝒮(w_{εν}) = 𝒮(v_ε) ∘ g (g')² + 𝒮(g)`.
- **[CORRECTION 2026-10-28, leader junk fix]** The identities are stated for `z ∈ 𝔻*` off two points where the
  finite maps carry junk values (correction 14: Model A is a sphere map and `wA = finPart ∘ wAS`):
  - `z = w_κ(∞)`: there `g(z) = w^κ(∞)` is not a value of `f = finPart ∘ w^κ` on `ℂ`, so `v_ε(g(z))` is the junk
    value of `invFun`. The old statement was false at `ε = 0` for every `κ` with `w_κ(∞) ≠ ∞` (found by 下属5).
  - `z = w_{εν}⁻¹(∞)`: there `w_{εν}(z)` is the junk value `0`, and `g_ε(0)` is unconstrained.
  The memoir's identity is between maps of `ℂ̄`; on `𝔻*` minus these two points nothing is lost. -/
theorem e41_eq_4_1 {κ : LinfStar} (hκ : ∃ h : κ ∈ LinfStarBall, Phi ⟨κ, h⟩ ∈ T01) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ∀ᶠ e in 𝓝 (0 : ℂ), ∀ z ∈ unitDiscExterior, wAS κ extInf ≠ (z : ExtPlane) →
      wAS (e • toLinf ν) (z : ExtPlane) ≠ extInf →
      let w := wA (e • toLinf ν)
      let ge := gsans (beltramiMul (e • toLinf ν) κ)
      let ve := fsans (beltramiMul (e • toLinf ν) κ) ∘ Function.invFun (fsans κ)
      ge (w z) = ve (gsans κ z) ∧
        schwarzianHol ge (w z) * dz w z ^ 2 + schwarzianDz w z =
          schwarzianDz ve (gsans κ z) * deriv (gsans κ) z ^ 2 + schwarzianHol (gsans κ) z := by
  -- Only `κ ∈ L∞(𝔻*)₁` is used; the condition `[κ] ∈ T₀(1)` is the memoir's setting and is not needed.
  obtain ⟨hκb, _hT⟩ := hκ
  have hνh : toLinf ν ∈ harmonicBeltrami := (harmonicL2_subset_harmonic.choose_spec ν hν).1
  have hev : ∀ᶠ e in 𝓝 (0 : ℂ), ‖e‖ * ‖toLinf ν‖ < 1 := by
    have hc : Continuous fun e : ℂ => ‖e‖ * ‖toLinf ν‖ := continuous_norm.mul continuous_const
    have h0 : (fun e : ℂ => ‖e‖ * ‖toLinf ν‖) 0 < 1 := by simp
    exact hc.continuousAt.eventually_lt continuousAt_const h0
  filter_upwards [hev] with e he z hz hz0 hp
  have hμb : e • toLinf ν ∈ LinfStarBall := by
    show e • toLinf ν ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, norm_smul]
    exact he
  obtain ⟨hwc, hwz, hwD⟩ := e41_w_regular hνh he hz hp
  have hlb : beltramiMul (e • toLinf ν) κ ∈ LinfStarBall := (wA_mul hκb hμb).1
  obtain ⟨hga, hgd⟩ := e41_g_holo hκb hz
  obtain ⟨hgea, hged⟩ := e41_g_holo hlb hwD
  obtain ⟨hvc, hvz⟩ := e41_ve_regular hκb hνh he hz hz0 hp
  refine ⟨e41_weld hκb hμb hz hz0 hp, ?_⟩
  have hL := e41_schw_left hgea hged hwc hwz
  have hR := e41_schw_right hga hgd hvc hvz
  have hC := e41_schw_congr (e41_weld_ev hκb hμb hz hz0 hp)
  show schwarzianHol (gsans (beltramiMul (e • toLinf ν) κ)) (wA (e • toLinf ν) z) * dz (wA (e • toLinf ν)) z ^ 2 +
      schwarzianDz (wA (e • toLinf ν)) z =
    schwarzianDz (fsans (beltramiMul (e • toLinf ν) κ) ∘ Function.invFun (fsans κ)) (gsans κ z) *
      deriv (gsans κ) z ^ 2 + schwarzianHol (gsans κ) z
  rw [← hL, ← hR]
  exact hC

/-- **(4.1)** (TT:5318). Let `[κ] ∈ T₀(1)`, `ν ∈ H^{-1,1}(𝔻*)`, and let `g_ε^{-1} ∘ f^ε = w_{εν} ∘ w_κ`, with
`f = f⁰`, `g = g₀` and `v_ε = f^ε ∘ f⁻¹`.

Then `g_ε ∘ w_{εν} = v_ε ∘ g`, so on `𝔻*`:
`𝒮(g_ε) ∘ w_{εν} (w_{εν})_z² + 𝒮(w_{εν}) = 𝒮(v_ε) ∘ g (g')² + 𝒮(g)`.
- **[CORRECTION 2026-10-28, leader junk fix]** The identities are stated for `z ∈ 𝔻*` off two points where the
  finite maps carry junk values (correction 14: Model A is a sphere map and `wA = finPart ∘ wAS`):
  - `z = w_κ(∞)`: there `g(z) = w^κ(∞)` is not a value of `f = finPart ∘ w^κ` on `ℂ`, so `v_ε(g(z))` is the junk
    value of `invFun`. The old statement was false at `ε = 0` for every `κ` with `w_κ(∞) ≠ ∞` (found by 下属5).
  - `z = w_{εν}⁻¹(∞)`: there `w_{εν}(z)` is the junk value `0`, and `g_ε(0)` is unconstrained.
  The memoir's identity is between maps of `ℂ̄`; on `𝔻*` minus these two points nothing is lost. -/
theorem eq_4_1 {κ : LinfStar} (hκ : ∃ h : κ ∈ LinfStarBall, Phi ⟨κ, h⟩ ∈ T01) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ∀ᶠ e in 𝓝 (0 : ℂ), ∀ z ∈ unitDiscExterior, wAS κ extInf ≠ (z : ExtPlane) →
      wAS (e • toLinf ν) (z : ExtPlane) ≠ extInf →
      let w := wA (e • toLinf ν)
      let ge := gsans (beltramiMul (e • toLinf ν) κ)
      let ve := fsans (beltramiMul (e • toLinf ν) κ) ∘ Function.invFun (fsans κ)
      ge (w z) = ve (gsans κ z) ∧
        schwarzianHol ge (w z) * dz w z ^ 2 + schwarzianDz w z =
          schwarzianDz ve (gsans κ z) * deriv (gsans κ) z ^ 2 + schwarzianHol (gsans κ) z :=
  e41_eq_4_1 hκ hν

end Ch2

end TakhtajanTeo
