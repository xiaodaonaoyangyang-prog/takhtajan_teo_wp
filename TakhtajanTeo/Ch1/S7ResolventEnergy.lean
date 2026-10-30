import TakhtajanTeo.Ch1.S7SecondGraphNorm
import TakhtajanTeo.Ch1.S7SecondEnergyIdentity

/-! Actual disk resolvent energy and exterior Proposition 7.2 assembly. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual Laplacian of the resolvent has finite weighted L2 norm,
derived from its PDE and the proved L2 contraction. -/
theorem s7re_resolvent_laplace_finite {F : ℂ → ℂ}
    (hF : F ∈ BCinf unitDisc) (hFn : normL2 unitDisc F < ∞) :
    normL2 unitDisc (laplace0 (resolventOp unitDisc F)) < ∞ := by
  let h := resolventOp unitDisc F
  have hh : h ∈ BCinf unitDisc := RK3_output_BCinf_disc hF
  have hhn : normL2 unitDisc h < ∞ := s7rl_finite (Or.inl rfl) hF hFn
  have hFm : AEStronglyMeasurable F (volume.restrict unitDisc) :=
    hF.1.continuousOn.aestronglyMeasurable measurableSet_ball
  have hhm : AEStronglyMeasurable h (volume.restrict unitDisc) :=
    hh.1.continuousOn.aestronglyMeasurable measurableSet_ball
  have hsub : normL2 unitDisc (fun z => F z - h z) < ∞ := by
    rw [s7pc_normL2_eq unitDisc (f := fun z => F z - h z) (hFm.sub hhm)]
    exact (s7pc_memLp hFm hFn).sub (s7pc_memLp hhm hhn)
  have he : laplace0 h =ᵐ[volume.restrict unitDisc]
      (fun z => (1 / 2 : ℂ) * (F z - h z)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hp := RK3_output_equation_disc hF z hz
    change 2 * (laplace0 h z + (1 / 2) * h z) = F z at hp
    linear_combination (1 / 2 : ℂ) * hp
  change normL2 unitDisc (laplace0 h) < ∞
  rw [grp_normL2_congr_ae he, normL2_const_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hsub

/-- Conjugating the actual pairing exchanges its arguments. -/
theorem s7re_pair_conj (D : Set ℂ) (f g : ℂ → ℂ) :
    conj (∫ z in D, f z * conj (g z) * rho z) =
      ∫ z in D, g z * conj (f z) * rho z := by
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with z
  simp only [map_mul, conj_conj, Complex.conj_ofReal]
  ring

/-- Exact scaling of the actual diagonal pairing. -/
theorem s7re_pair_neg_two (D : Set ℂ) (q : ℂ → ℂ) :
    (∫ z in D, (-2 * q z) * conj (-2 * q z) * rho z) =
      4 * ∫ z in D, q z * conj (q z) * rho z := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  simp only [map_mul, map_neg, map_ofNat]
  ring

/-- The PDE expansion of the difference of two pairings, with all integral
splittings justified by the indicated actual integrability facts. -/
theorem s7re_pair_difference {D : Set ℂ} (hD : MeasurableSet D) {F h d : ℂ → ℂ}
    (he : EqOn F (fun z => 2 * d z + h z) D)
    (hFF : Integrable (fun z => F z * conj (F z) * rho z) (volume.restrict D))
    (hFh : Integrable (fun z => F z * conj (h z) * rho z) (volume.restrict D))
    (hdd : Integrable (fun z => d z * conj (d z) * rho z) (volume.restrict D))
    (hhd : Integrable (fun z => h z * conj (d z) * rho z) (volume.restrict D)) :
    (∫ z in D, F z * conj (F z) * rho z) - (∫ z in D, F z * conj (h z) * rho z) =
      4 * (∫ z in D, d z * conj (d z) * rho z) +
        2 * (∫ z in D, h z * conj (d z) * rho z) := by
  rw [← integral_sub hFF hFh]
  calc
    _ = ∫ z in D, 4 * (d z * conj (d z) * rho z) +
        2 * (h z * conj (d z) * rho z) := by
      apply setIntegral_congr_fun hD
      intro z hz
      dsimp only
      rw [he hz]
      simp only [map_add, map_mul, map_ofNat]
      ring
    _ = _ := by
      rw [integral_add (hdd.const_mul 4) (hhd.const_mul 2), integral_const_mul,
        integral_const_mul]

/-- The actual graph-domain cross pairing is real: this follows from the
proved second-energy identity and the reality of its two self-pairings. -/
theorem s7re_laplace_pair_symmetric {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hL : normL2 unitDisc h < ∞) (hDL : normL2 unitDisc (laplace0 h) < ∞) :
    (∫ z in unitDisc, h z * conj (laplace0 h z) * rho z) =
      ∫ z in unitDisc, laplace0 h z * conj (h z) * rho z := by
  have hid := (s7ei_second_energy hh hL hDL).2
  have hconj := congrArg conj hid
  simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, s7re_pair_conj] at hconj
  linear_combination 2 * hid - 2 * hconj

/-- The actual resolvent second derivative has finite energy and satisfies
the required complex energy identity, with no energy identity assumed. -/
theorem s7re_resolvent_energy {F : ℂ → ℂ}
    (hF : F ∈ BCinf unitDisc) (hFn : normL2 unitDisc F < ∞) :
    normL2 unitDisc (fun z => -2 * s7et_q (resolventOp unitDisc F) z) < ∞ ∧
      (∫ z in unitDisc, (-2 * s7et_q (resolventOp unitDisc F) z) *
        conj (-2 * s7et_q (resolventOp unitDisc F) z) * rho z) =
        (∫ z in unitDisc, F z * conj (F z) * rho z) -
          ∫ z in unitDisc, F z * conj (resolventOp unitDisc F z) * rho z := by
  let h := resolventOp unitDisc F
  have hh : h ∈ BCinf unitDisc := RK3_output_BCinf_disc hF
  have hL : normL2 unitDisc h < ∞ := s7rl_finite (Or.inl rfl) hF hFn
  have hDL : normL2 unitDisc (laplace0 h) < ∞ := s7re_resolvent_laplace_finite hF hFn
  obtain ⟨hq, hid⟩ := s7ei_second_energy hh.1 hL hDL
  have hFm : AEStronglyMeasurable F (volume.restrict unitDisc) :=
    hF.1.continuousOn.aestronglyMeasurable measurableSet_ball
  have hhm : AEStronglyMeasurable h (volume.restrict unitDisc) :=
    hh.1.continuousOn.aestronglyMeasurable measurableSet_ball
  have hDm : AEStronglyMeasurable (laplace0 h) (volume.restrict unitDisc) :=
    (s7el_laplace_measurable h).aestronglyMeasurable
  have hP : EqOn F (fun z => 2 * laplace0 h z + h z) unitDisc := by
    intro z hz
    have hp := RK3_output_equation_disc hF z hz
    change 2 * (laplace0 h z + (1 / 2) * h z) = F z at hp
    linear_combination -hp
  have hdiff := s7re_pair_difference (D := unitDisc) measurableSet_ball hP
    (s7pc_pairing_integrable hFm hFm hFn hFn)
    (s7pc_pairing_integrable hFm hhm hFn hL)
    (s7pc_pairing_integrable hDm hDm hDL hDL)
    (s7pc_pairing_integrable hhm hDm hL hDL)
  have hsym := s7re_laplace_pair_symmetric hh.1 hL hDL
  constructor
  · rw [normL2_const_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hq
  · change (∫ z in unitDisc, (-2 * s7et_q h z) * conj (-2 * s7et_q h z) * rho z) =
      (∫ z in unitDisc, F z * conj (F z) * rho z) -
        ∫ z in unitDisc, F z * conj (h z) * rho z
    rw [s7re_pair_neg_two, hdiff, hsym]
    linear_combination 4 * hid

/-- **Proposition 7.2** (TT:2762–2768). For `μ ∈ H^{-1,1}(𝔻*)` and `ν ∈ Ω^{-1,1}(𝔻*)`:
- `Q̇(μ)[ν] ∈ L²(𝔻*, ρ d²z)`;
- `‖Q̇(μ)[ν]‖₂² = ‖μν̄‖₂² - (μν̄, G(μν̄))`. -/
theorem s7re_prop_7_2 {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    normL2 unitDiscExterior (Qdot (toLinf μ) ν) < ∞ ∧
      l2Inner (Qdot (toLinf μ) ν) (Qdot (toLinf μ) ν) =
        l2Inner (fun z => μ z * conj (ν z)) (fun z => μ z * conj (ν z)) -
          l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => μ z * conj (ν z)) := by
  obtain ⟨F, hF, hFn, _, _, _, hQnorm, hQQ, hRR, hRG⟩ := s7et_prop72_reduction hμ hν
  obtain ⟨hfinite, henergy⟩ := s7re_resolvent_energy hF hFn
  constructor
  · rw [hQnorm]
    exact hfinite
  · rw [hQQ, hRR, hRG]
    exact henergy

end TakhtajanTeo
