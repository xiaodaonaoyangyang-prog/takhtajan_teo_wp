import TakhtajanTeo.Ch2.S4MixedVariation

/-! # Actual dz-Schwarzian linearization at the identity (`s4hv_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- H14
theorem s4hv_schwarzian_linearization {F : ℂ → ℂ → ℂ} {P U : Set ℂ}
    (hP : IsOpen P) (hU : IsOpen U) (hP₀ : (0 : ℂ) ∈ P)
    (hp : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hs : ∀ t ∈ P, ContDiffOn ℝ 3 (F t) U)
    (hc : ∀ j ≤ 3, ContinuousOn
      (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U))
    (hzero : F 0 = id) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun t : ℂ => schwarzianDz (F t) z)
      (dz (dz (dz (fun w => deriv (fun t => F t w) 0))) z) 0 := by
  have hreg1 := s4v_dz_family_regular (n := 2) hU hs hc
  have hp1 : ∀ w ∈ U, DifferentiableOn ℂ (fun t => dz (F t) w) P :=
    fun w hw => s4v_param_dz_holomorphic hP hU hp hs hc hw
  have hreg2 := s4v_dz_family_regular (n := 1) hU hreg1.1 hreg1.2
  have hp2 : ∀ w ∈ U, DifferentiableOn ℂ (fun t => dz (dz (F t)) w) P :=
    fun w hw => s4v_param_dz_holomorphic hP hU hp1 hreg1.1 hreg1.2 hw
  have hp3 : ∀ w ∈ U, DifferentiableOn ℂ (fun t => dz (dz (dz (F t))) w) P :=
    fun w hw => s4v_param_dz_holomorphic hP hU hp2 hreg2.1 hreg2.2 hw
  have hd1 := ((hp1 z hz).differentiableAt (hP.mem_nhds hP₀)).hasDerivAt
  have hd2 := ((hp2 z hz).differentiableAt (hP.mem_nhds hP₀)).hasDerivAt
  have hd3 := ((hp3 z hz).differentiableAt (hP.mem_nhds hP₀)).hasDerivAt
  have hid : dz (id : ℂ → ℂ) = (fun _ => (1 : ℂ)) := by
    funext w
    norm_num [dz, fderiv_id, Complex.I_sq]
  have hconst (a : ℂ) : dz (fun _ : ℂ => a) = (fun _ => (0 : ℂ)) := by
    funext w
    simp [dz]
  have hv1 : dz (F 0) z = 1 := by rw [hzero, hid]
  have hv2 : dz (dz (F 0)) z = 0 := by rw [hzero, hid, hconst]
  have hv3 : dz (dz (dz (F 0))) z = 0 := by rw [hzero, hid, hconst, hconst]
  have hn₀ : dz (F 0) z ≠ 0 := by rw [hv1]; exact one_ne_zero
  have hformula : HasDerivAt (fun t : ℂ => dz (dz (dz (F t))) z / dz (F t) z -
        (3 / 2 : ℂ) * (dz (dz (F t)) z / dz (F t) z) ^ 2)
      (deriv (fun t => dz (dz (dz (F t))) z) 0) 0 := by
    apply ((hd3.div hd1 hn₀).sub (((hd2.div hd1 hn₀).pow 2).const_mul (3 / 2 : ℂ))).congr_deriv
    simp [hv1, hv2, hv3]
  have hswap := s4hv_parameter_dz3_commute hP hU hp hs hc hP₀ hz
  apply (hformula.congr_deriv hswap).congr_of_eventuallyEq
  filter_upwards [hP.mem_nhds hP₀, hd1.continuousAt.eventually_ne hn₀] with t ht htn
  exact s4v_schwarzianDz_eq ((hs t ht).contDiffAt (hU.mem_nhds hz)) htn

-- H15
theorem s4hv_normalized_schwarzian_derivative {m : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : IsBeltramiCoeff m univ k) {U : Set ℂ} (hU : IsOpen U)
    (hms : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun t : ℂ => schwarzianDz (normalizedSolution (fun w => t * m w)) z)
      (dz (dz (dz (ahVar m))) z) 0 := by
  let F := fun t : ℂ => normalizedSolution (fun w => t * m w)
  let W := fun q : ℂ × ℂ => normalizedSolution (fun w => q.1 * m w + q.2 * (0 : ℂ))
  let V : Set (ℂ × ℂ) := {q | (2 * k) * ‖q‖ < 1}
  let P : Set ℂ := {t | (2 * k) * ‖t‖ < 1}
  have hV : IsOpen V := isOpen_lt (continuous_const.mul continuous_norm) continuous_const
  have hP : IsOpen P := isOpen_lt (continuous_const.mul continuous_norm) continuous_const
  have hP₀ : (0 : ℂ) ∈ P := by simp [P]
  have hPV : ∀ t ∈ P, (t, (0 : ℂ)) ∈ V := by
    intro t ht
    simpa only [P, V, mem_ofPred_eq, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg t)] using ht
  have hm₀ : IsBeltramiCoeff (fun _ : ℂ => 0) univ k :=
    ⟨aestronglyMeasurable_const, Eventually.of_forall fun _ => by simpa using hk⟩
  have hs₀ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℂ => (0 : ℂ)) U := contDiffOn_const
  have hVk : ∀ q ∈ V, ∃ b < 1, IsBeltramiCoeff (fun w => q.1 * m w + q.2 * (0 : ℂ)) univ b := by
    intro q hq
    refine ⟨(2 * k) * ‖q‖, hq, ?_⟩
    simpa only [abs_of_nonneg hk, two_mul] using wr_coeff_lin hm hm₀ q
  have hreg : (∀ q ∈ V, ContDiffOn ℝ 3 (W q) U) ∧
      ∀ j ≤ 3, ContinuousOn
        (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (W q.1) q.2) (V ×ˢ U) :=
    wr_ns2_z_regular hm hm₀ hU hms hs₀ hV hVk
  have hs : ∀ t ∈ P, ContDiffOn ℝ 3 (F t) U := by
    intro t ht
    simpa only [F, W, zero_mul, add_zero] using hreg.1 _ (hPV t ht)
  have hj : ∀ j ≤ 3, ContinuousOn
      (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U) := by
    intro j hj
    have hh := (hreg.2 j hj).comp (f := fun q : ℂ × ℂ => ((q.1, (0 : ℂ)), q.2))
      ((continuous_fst.prodMk continuous_const).prodMk continuous_snd).continuousOn
      (fun (q : ℂ × ℂ) (hq : q ∈ P ×ˢ U) => ⟨hPV q.1 hq.1, hq.2⟩)
    simpa only [Function.comp_def, F, W, zero_mul, add_zero] using hh
  have hp : ∀ w ∈ U, DifferentiableOn ℂ (fun t => F t w) P := by
    intro w hw t ht
    have hh := ((wr_ns2_holo hm hm₀ hV hVk w).1 (0 : ℂ)).differentiableAt
      ((hV.preimage (continuous_id.prodMk continuous_const)).mem_nhds (hPV t ht))
    simpa only [F, zero_mul, add_zero] using hh.differentiableWithinAt (s := P)
  have hzero : F 0 = id := by
    dsimp only [F]
    simp only [zero_mul]
    exact bB_l_normalizedSolution_zero
  have hd := s4hv_schwarzian_linearization hP hU hP₀ hp hs hj hzero hz
  have hfirst : (fun w => deriv (fun t => F t w) 0) = ahVar m :=
    funext fun w => (s4v_normalized_first_variation hk hm w).deriv
  rwa [hfirst] at hd

end Ch2
end TakhtajanTeo
