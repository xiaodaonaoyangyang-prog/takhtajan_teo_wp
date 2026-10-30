import TakhtajanTeo.Ch1.HilbertReflectionPreimage

/-! The explicit reflected preimage, with the still-missing reproduction and
coefficient admissibility inputs visible. This is not a bijectivity assumption. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem hbPre_pullback_integral {g : ℂ → ℂ} {E V : Set ℂ}
    (hE : IsOpen E) (hg : IsConformalOnto g E V) (b : ℂ → ℂ) (z : ℂ) :
    (∫ w in E, hbPre_pullback b g w * deriv g w ^ 2 / (g w - z) ^ 4) =
      ∫ u in g '' E, b u / (u - z) ^ 4 := by
  rw [← hb_fourth_kernel_transport hE hg]
  apply setIntegral_congr_fun (show MeasurableSet (g '' E) by
    rw [hg.2.2]
    exact (hg.isOpen hE).measurableSet)
  rintro u ⟨w, hw, rfl⟩
  have hd := deriv_ne_zero_of_injOn hE hg.1 hg.2.1 hw
  have hi : deriv (Function.invFunOn g E) (g w) = (deriv g w)⁻¹ :=
    eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul hE hg hw)
  dsimp only
  rw [hg.2.1.leftInvOn_invFunOn hw, hi]
  congr 1
  dsimp [hbPre_pullback]
  have hc : conj (deriv g w) ≠ 0 := by simpa using hd
  rw [map_inv₀]
  field_simp

/-- Projection of the real reflection formula gives an actual harmonic L2
preimage once the raw coefficient is bounded and L2. No eq_2_2 placeholder
or operator-bijectivity premise occurs in the proof. -/
theorem hbPre_reflection_preimage {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (q h : ℂ → ℂ)
    (hrepro : ∀ z ∈ fsans μ '' unitDisc,
      q z = -(3 / π) * ∫ u in gsans μ '' unitDiscExterior,
        q (h u) * (u - h u) ^ 2 * dzbar h u / (u - z) ^ 4)
    (hraw : MemLp (hbPre_pullback (hbPre_reflected q h) (gsans μ)) ∞
      (volume.restrict unitDiscExterior))
    (hrawL2 : normL2 unitDiscExterior (hbPre_pullback (hbPre_reflected q h) (gsans μ)) < ∞) :
    ∃ ν ∈ harmonicL2 unitDiscExterior,
      (∀ ζ ∈ unitDisc, AInf.toFun (D0BersR μ (toLinf ν)) ζ = q (fsans μ ζ) * deriv (fsans μ) ζ ^ 2) ∧
      normL2 unitDiscExterior ν ≤
        48 * normL2 unitDiscExterior (hbPre_pullback (hbPre_reflected q h) (gsans μ)) := by
  let a := toLinf (hbPre_pullback (hbPre_reflected q h) (gsans μ))
  have ha := bc_toLinf_ae hraw
  have hn : normL2 unitDiscExterior a =
      normL2 unitDiscExterior (hbPre_pullback (hbPre_reflected q h) (gsans μ)) := by
    unfold normL2
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ha] with w hw
    rw [hw]
  obtain ⟨ν, hν, hνa, hνnorm⟩ := hbPre_projection_L2 a (hn ▸ hrawL2)
  refine ⟨ν, hν, ?_, hn ▸ hνnorm⟩
  intro ζ hζ
  rw [hνa, hbPre_derivative_projection hμ, r24_phi_formula hμ _ hζ,
    hb_fourth_kernel_transport resolvent_exterior_isOpen (S2C.s2c_conf_g hμ)]
  have haint : (∫ w in unitDiscExterior, a w * deriv (gsans μ) w ^ 2 / (gsans μ w - fsans μ ζ) ^ 4) =
      ∫ w in unitDiscExterior, hbPre_pullback (hbPre_reflected q h) (gsans μ) w *
        deriv (gsans μ) w ^ 2 / (gsans μ w - fsans μ ζ) ^ 4 := by
    apply integral_congr_ae
    filter_upwards [ha] with w hw
    rw [hw]
  rw [haint, hbPre_pullback_integral resolvent_exterior_isOpen (S2C.s2c_conf_g hμ)]
  have hi : (∫ u in gsans μ '' unitDiscExterior, hbPre_reflected q h u / (u - fsans μ ζ) ^ 4) =
      (1 / 2 : ℂ) * ∫ u in gsans μ '' unitDiscExterior,
        q (h u) * (u - h u) ^ 2 * dzbar h u / (u - fsans μ ζ) ^ 4 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun ((S2C.s2c_conf_g hμ).isOpen resolvent_exterior_isOpen).measurableSet
    intro u _
    dsimp [hbPre_reflected]
    ring
  rw [hi, hrepro _ ⟨ζ, hζ, rfl⟩]
  ring

end TakhtajanTeo

#print axioms TakhtajanTeo.hbPre_pullback_integral
#print axioms TakhtajanTeo.hbPre_reflection_preimage
