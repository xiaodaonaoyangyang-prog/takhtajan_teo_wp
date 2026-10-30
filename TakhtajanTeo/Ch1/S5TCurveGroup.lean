import TakhtajanTeo.Ch1.TCurveFiberFormula
import TakhtajanTeo.Ch1.TCurveClosure
import TakhtajanTeo.Ch1.GroupTopGroup
import TakhtajanTeo.Ch1.GroupAlgebra
import TakhtajanTeo.Ch1.Cor32Completed
import TakhtajanTeo.Ch1.S5VerticalCurvature
import TakhtajanTeo.Ch1.SphereWeldingTransport
import TakhtajanTeo.Ch1.ComponentTB

/-!
# Group laws of `𝒯(1)` (`s5tg_`, 下属3, Program G, thm_5_3 W4)

Host: new module `TakhtajanTeo/Ch1/S5TCurveGroup.lean`.

* `s5tg_mul_self`: `q * q⁻¹ = (0, ∞)` for `q ∈ 𝒯(1)` (`tcurveMulInv q q = tOrigin`). Route: GPT's base and fibre formulas
  with a σ-extension `R` (`tcg_mul_bers_with_sigma`, `tcg_mul_fibre_with_sigma`); the base is `[μ][μ]⁻¹ = 0`, so the
  Möbius `B` of the fibre formula agrees with `R` on `𝔻`, hence with `σ_u` on the circle, so `B = σ_u` and the fibre
  point is `σ_u(u) = ∞`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- `[μ][μ]⁻¹ = 0` in `T(1)`. -/
theorem s5tg_mulT_inv_self (p : T1) : mulT p (invT p) = originT := by
  have h := gtr_c_inv_mul_self (invT p)
  rwa [grp_invT_invT] at h

/-- `A∞` evaluation of `0`. -/
theorem s5tg_toFun_zero : AInf.toFun (0 : AInf unitDisc) = fun _ => 0 := by
  have h := ctb_toFun_smul 0 (0 : AInf unitDisc)
  rw [zero_smul] at h
  rw [h]
  funext z
  simp

/-- The conformal map `f` of the origin class is the identity on `𝔻`. -/
theorem s5tg_origin_fB {z : ℂ} (hz : z ∈ unitDisc) :
    fB ((Quotient.out originT : LinfStarBall) : LinfStar) z = z := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  have hclass : teichSetoid (Quotient.out originT : LinfStarBall) ⟨0, h0⟩ :=
    Quotient.exact (Quotient.out_eq originT)
  rw [modelA_to_modelB _ ⟨0, h0⟩ hclass z hz]
  have h := Ch2.e13_wB_disc h0 hz
  rw [s5vc_wB_zero] at h
  exact (OnePoint.coe_injective h).symm

/-- The normalized sphere welding of the origin class is the identity on `𝔻̄*`. -/
theorem s5tg_origin_nWS {u : ExtPlane} (hu : u ∈ extDiscExterior) :
    normalizedWeldingSphere ((Quotient.out originT : LinfStarBall) : LinfStar) u = u := by
  have hμ := (Quotient.out originT : LinfStarBall).2
  rcases hu with ⟨w, hw, rfl⟩ | hu
  · rw [← normalizedWeldingExterior_coe hμ, ← gMu_eq_normalizedWeldingExterior hμ hw, s5vc_origin_gMu hw]
  · have hu' : u = extInf := hu
    subst u
    exact normalizedWeldingSphere_infty hμ

/-- The base of `q * q⁻¹` is the origin. -/
theorem s5tg_base_self {q : T1 × ExtPlane} (hq : q ∈ TCurve) : (tcurveMulInv q q).1 = originT := by
  have hμ := (Quotient.out q.1 : LinfStarBall).2
  have hu := tcg_parameter_mem hμ hq
  obtain ⟨R, KR, hR, hRE, hRD, hRb⟩ := tcg_sigma_extension hu
  apply bers_injective
  apply AInf.ext_toFun_disc
  intro z hz
  rw [tcg_mul_bers_with_sigma hq hq R hR hRE hRD hRb hz, s5tg_mulT_inv_self]
  show AInf.toFun (bers (Phi ⟨0, mem_ball_self one_pos⟩)) _ * _ =
    AInf.toFun (bers (Phi ⟨0, mem_ball_self one_pos⟩)) z
  rw [c32_bers_origin, s5tg_toFun_zero]
  simp

/-- **`q * q⁻¹ = (0, ∞)`** on `𝒯(1)`. -/
theorem s5tg_mul_self {q : T1 × ExtPlane} (hq : q ∈ TCurve) : tcurveMulInv q q = tOrigin := by
  have hμ := (Quotient.out q.1 : LinfStarBall).2
  have hu := tcg_parameter_mem hμ hq
  set u := Function.invFun (normalizedWeldingSphere (Quotient.out q.1 : LinfStarBall)) q.2 with hudef
  obtain ⟨R, KR, hR, hRE, hRD, hRb⟩ := tcg_sigma_extension hu
  obtain ⟨B, hB, hfib, hBf⟩ := tcg_mul_fibre_with_sigma hq hq R hR hRE hRD hRb
  have hbase := s5tg_base_self hq
  rw [s5tg_mulT_inv_self] at hfib hBf
  rw [hbase] at hBf
  -- `R` maps `𝔻` into `𝔻`
  have hRD' : ∀ z ∈ unitDisc, R z ∈ unitDisc := by
    intro z hz
    have hz' : z ∈ R.symm '' unitDisc := by rw [hRD.2.2]; exact hz
    obtain ⟨w, hw, hwz⟩ := hz'
    rw [← hwz, R.apply_symm_apply]
    exact hw
  -- `B = R` on `𝔻`, hence on the closed disk
  have hBR : EqOn (fun z : ℂ => B (z : ExtPlane)) (fun z : ℂ => ((R z : ℂ) : ExtPlane)) unitDisc := by
    intro z hz
    have h := hBf z hz
    rw [s5tg_origin_fB hz, s5tg_origin_fB (hRD' z hz)] at h
    exact h
  have hBc := (mobius_sphere_continuous_bijective hB).1
  have hcl := hBR.closure (hBc.comp OnePoint.continuous_coe) (OnePoint.continuous_coe.comp R.continuous)
  rw [unitDisc, closure_ball 0 one_ne_zero] at hcl
  -- `B = σ_u` on the circle
  have hσ := tce_sigma_isMobius hu
  have hσi := tce_sigma_inj hu
  have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 → B (ζ : ExtPlane) = sigmaSphere u (ζ : ExtPlane) := by
    intro ζ hζ
    have h1 : B (ζ : ExtPlane) = ((R ζ : ℂ) : ExtPlane) := hcl (by simp [hζ])
    have h2 := hRb (show ζ ∈ unitCircle by simpa [unitCircle] using hζ)
    rw [h1, h2]
    apply coe_finPart_of_ne
    intro hinf
    have hpole := sigmaSphere_pole u
    have hζu : (ζ : ExtPlane) = u := hσi (hinf.trans hpole.symm)
    rw [← hζu, fi_extDiscExterior_eq_compl] at hu
    exact hu ⟨ζ, by simp [hζ], rfl⟩
  have hBσ : B = sigmaSphere u := by
    refine mobius_eq_of_three_points hB hσ (p₁ := 1) (p₂ := -1) (p₃ := I) (by norm_num) ?_ ?_
      (hcirc 1 (by simp)) (hcirc (-1) (by simp)) (hcirc I (by simp))
    · intro h
      have := congrArg Complex.im h
      simp at this
    · intro h
      have := congrArg Complex.re h
      simp at this
  refine Prod.ext hbase ?_
  rw [hfib, hBσ, s5tg_origin_nWS hu]
  exact sigmaSphere_pole u

end TakhtajanTeo
