import TakhtajanTeo.Ch1.HilbertBersDifferentialL2
import TakhtajanTeo.Ch1.HarmonicProjCompleted

/-! Genuine harmonic projection support for the reflected preimage construction.
No general-base bijectivity or reflection estimate is assumed here. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The existing harmonic projector sends bounded L2 coefficients to genuine
harmonic L2 representatives. The coarse constant 48 avoids any unproved
orthogonal-projector assertion. -/
theorem hbPre_projection_L2 (a : LinfStar) (ha : normL2 unitDiscExterior a < ∞) :
    ∃ ν ∈ harmonicL2 unitDiscExterior, toLinf ν = harmonicProj a ∧
      normL2 unitDiscExterior ν ≤ 48 * normL2 unitDiscExterior a := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  have he : (fun l : LinfStar => bersPhi (beltramiMul l 0)) =ᶠ[𝓝 0] bersPhi := by
    filter_upwards [isOpen_ball.mem_nhds h0] with l hl
    rw [grp_mul_zero hl]
  have hD : D0BersR 0 = fderiv ℂ bersPhi 0 := he.fderiv_eq
  have hb := remark_2_4 h0 a
  rw [hD] at hb
  have hA : AInf.toFun (fderiv ℂ bersPhi 0 a) ∈ A2fun unitDisc :=
    ⟨(fderiv ℂ bersPhi 0 a).property,
      hb.trans_lt (ENNReal.mul_lt_top (by norm_num) ha)⟩
  let φ := toA2 unitDisc (AInf.toFun (fderiv ℂ bersPhi 0 a))
  have hφ : A2toAInf φ = fderiv ℂ bersPhi 0 a := ctb_A2toAInf_toA2 hA
  obtain ⟨ν, hν, hνφ, hn⟩ := hbL2_coordinate_representative φ
  refine ⟨ν, hν, ?_, ?_⟩
  · rw [hνφ, hφ, hp_eq_Lambda]
  · rw [hn, l29b_nnnorm_eq, hφ]
    calc 2 * normA2 unitDisc (AInf.toFun (fderiv ℂ bersPhi 0 a))
        ≤ 2 * (24 * normL2 unitDiscExterior a) := by gcongr
      _ = 48 * normL2 unitDiscExterior a := by ring

/-- The actual projector preserves every A1 pairing on the exterior. -/
theorem hbPre_projection_pairing (a : LinfStar) {q : ℂ → ℂ} (hq : q ∈ AOneStar) :
    (∫ w in unitDiscExterior, harmonicProj a w * q w) =
      ∫ w in unitDiscExterior, a w * q w := by
  have hzero : fderiv ℂ bersPhi 0 (a - harmonicProj a) = 0 := by
    rw [map_sub, hp_eq_Lambda, QCV.qcv_D0_Lambda, sub_self]
  have hp := QCV.qcv_ker_D0Phi_pairing hzero hq
  have hi : IntegrableOn (fun w => a w * q w) unitDiscExterior :=
    hq.2.1.mul_of_top_right (Lp.memLp a)
  have hPi : IntegrableOn (fun w => harmonicProj a w * q w) unitDiscExterior :=
    hq.2.1.mul_of_top_right (Lp.memLp (harmonicProj a))
  have he : (∫ w in unitDiscExterior, (a - harmonicProj a) w * q w) =
      (∫ w in unitDiscExterior, a w * q w) - ∫ w in unitDiscExterior, harmonicProj a w * q w := by
    rw [← integral_sub hi hPi]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub a (harmonicProj a)] with w hw
    rw [hw]
    simp only [Pi.sub_apply]
    ring
  exact (sub_eq_zero.mp (he.symm.trans hp)).symm

/-- The raw reflection coefficient before conformal pullback and projection. -/
def hbPre_reflected (q h : ℂ → ℂ) (u : ℂ) : ℂ :=
  (1 / 2 : ℂ) * q (h u) * (u - h u) ^ 2 * dzbar h u

/-- Pullback by the exterior conformal welding map, with the Beltrami phase. -/
def hbPre_pullback (b g : ℂ → ℂ) (w : ℂ) : ℂ :=
  b (g w) * (conj (deriv g w) / deriv g w)

theorem hbPre_pullback_norm {b g : ℂ → ℂ} {w : ℂ} (hw : deriv g w ≠ 0) :
    ‖hbPre_pullback b g w‖ = ‖b (g w)‖ := by
  simp [hbPre_pullback, norm_mul, norm_div, hw]

end TakhtajanTeo

#print axioms TakhtajanTeo.hbPre_projection_L2
#print axioms TakhtajanTeo.hbPre_projection_pairing
#print axioms TakhtajanTeo.hbPre_pullback_norm
