import TakhtajanTeo.Ch1.HilbertBersPreimage

/-! Actual fourth-order welding kernels as admissible exterior quadratic tests. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def hbPre_kernel (μ : LinfStar) (z w : ℂ) : ℂ :=
  deriv (gsans μ) w ^ 2 / (gsans μ w - z) ^ 4

theorem hbPre_kernel_ne {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {z w : ℂ} (hz : z ∈ fsans μ '' unitDisc) (hw : w ∈ unitDiscExterior) : gsans μ w - z ≠ 0 := by
  intro he
  exact Set.disjoint_left.mp (AppB.b8_welding_normalized_pair hμ).2.2.2.2.2 hz
    ⟨w, hw, sub_eq_zero.mp he⟩

theorem hbPre_kernel_holo {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {z : ℂ} (hz : z ∈ fsans μ '' unitDisc) : DifferentiableOn ℂ (hbPre_kernel μ z) unitDiscExterior := by
  have hg := (S2C.s2c_conf_g hμ).1
  exact ((hg.deriv resolvent_exterior_isOpen).pow 2).div ((hg.sub_const z).pow 4)
    (fun w hw => pow_ne_zero 4 (hbPre_kernel_ne hμ hz hw))

theorem hbPre_kernel_integrable {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {z : ℂ} (hz : z ∈ fsans μ '' unitDisc) : IntegrableOn (hbPre_kernel μ z) unitDiscExterior := by
  have hg := S2C.s2c_conf_g hμ
  refine ⟨(hbPre_kernel_holo hμ hz).continuousOn.aestronglyMeasurable
    resolvent_exterior_isOpen.measurableSet, ?_⟩
  change (∫⁻ w in unitDiscExterior, ‖hbPre_kernel μ z w‖ₑ) < ∞
  have he : (∫⁻ w in unitDiscExterior, ‖hbPre_kernel μ z w‖ₑ) =
      ∫⁻ u in gsans μ '' unitDiscExterior, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 := by
    rw [r24_conformal_lintegral resolvent_exterior_isOpen hg.1 hg.2.1]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with w hw
    rw [← ofReal_norm, hbPre_kernel, norm_div, norm_pow, norm_pow,
      ENNReal.ofReal_div_of_pos (pow_pos (norm_pos_iff.mpr (hbPre_kernel_ne hμ hz hw)) 4)]
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm,
      div_eq_mul_inv, ENNReal.inv_pow]
  rw [he]
  exact (r24_interior_kernel_bound hμ hz).trans_lt ENNReal.ofReal_lt_top

/-- A reciprocal coordinate at infinity gives fourth-order decay of the kernel. -/
theorem hbPre_kernel_decay {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {z : ℂ} (hz : z ∈ fsans μ '' unitDisc) :
    ∃ C R : ℝ, ∀ w : ℂ, R < ‖w‖ → ‖hbPre_kernel μ z w‖ ≤ C / ‖w‖ ^ 4 := by
  let H : ℂ → ℂ := fun t => if t = 0 then 0 else (gsans μ t⁻¹)⁻¹
  let J : ℂ → ℂ := fun t => H t / (1 - z * H t)
  obtain ⟨hH, -, hg0⟩ := r24_inversion hμ
  have hden : ∀ t ∈ unitDisc, 1 - z * H t ≠ 0 := by
    intro t ht
    by_cases ht0 : t = 0
    · simp [H, ht0]
    · have he := QCV.qcv_inv_mem_exterior ⟨ht, ht0⟩
      have hg := hg0 _ he
      have hn := hbPre_kernel_ne hμ hz he
      dsimp only [H]
      rw [if_neg ht0]
      intro hh
      apply hn
      have hm := congrArg (fun a : ℂ => a * gsans μ t⁻¹) hh
      simpa only [sub_mul, mul_assoc, inv_mul_cancel₀ hg, mul_one, one_mul, zero_mul] using hm
  have hJ : DifferentiableOn ℂ J unitDisc :=
    hH.div ((differentiableOn_const (c := (1 : ℂ))).sub (hH.const_mul z)) hden
  have hJc : ContinuousAt (deriv J) 0 :=
    ((hJ.deriv isOpen_ball).continuousOn).continuousAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), ‖deriv J t‖ < ‖deriv J 0‖ + 1 :=
    hJc.norm.tendsto.eventually_lt_const (by linarith : ‖deriv J 0‖ < ‖deriv J 0‖ + 1)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hform : ∀ w ∈ unitDiscExterior, J w⁻¹ = (gsans μ w - z)⁻¹ := by
    intro w hw
    have hw0 := resolvent_exterior_ne_zero hw
    have hg := hg0 w hw
    dsimp only [J, H]
    rw [if_neg (inv_ne_zero hw0), inv_inv]
    field_simp
  have hkd : ∀ w ∈ unitDiscExterior,
      hbPre_kernel μ z w = deriv J w⁻¹ ^ 2 / w ^ 4 := by
    intro w hw
    have hw0 := resolvent_exterior_ne_zero hw
    have hwi : w⁻¹ ∈ unitDisc := by
      apply mem_ball_zero_iff.mpr
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hw
    have hdJ := ((hJ.differentiableAt (isOpen_ball.mem_nhds hwi)).hasDerivAt.comp w (hasDerivAt_inv hw0))
    have hge : HasDerivAt (fun u => (gsans μ u - z)⁻¹)
        (-deriv (gsans μ) w / (gsans μ w - z) ^ 2) w := by
      convert (((S2C.s2c_conf_g hμ).1.differentiableAt
        (resolvent_exterior_isOpen.mem_nhds hw)).hasDerivAt.sub_const z).inv
        (hbPre_kernel_ne hμ hz hw) using 1 <;> ring
    have heq : (fun u => J u⁻¹) =ᶠ[𝓝 w] fun u => (gsans μ u - z)⁻¹ :=
      Filter.eventuallyEq_of_mem (resolvent_exterior_isOpen.mem_nhds hw) (fun u hu => hform u hu)
    have hdEq := (hdJ.congr_of_eventuallyEq heq.symm).unique hge
    have hsq := congrArg (fun v : ℂ => v ^ 2) hdEq
    dsimp only [hbPre_kernel]
    convert hsq.symm using 1 <;> field_simp <;> ring
  refine ⟨(‖deriv J 0‖ + 1) ^ 2, max 1 r⁻¹, ?_⟩
  intro w hw
  have hwE : w ∈ unitDiscExterior := lt_of_le_of_lt (le_max_left _ _) hw
  have hw0 : 0 < ‖w‖ := lt_trans zero_lt_one hwE
  have hwin : w⁻¹ ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, norm_inv]
    exact (inv_lt_comm₀ hw0 hr).mpr (lt_of_le_of_lt (le_max_right _ _) hw)
  rw [hkd w hwE, norm_div, norm_pow, norm_pow]
  gcongr
  exact (hball hwin).le

theorem hbPre_kernel_mem_AOne {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {z : ℂ} (hz : z ∈ fsans μ '' unitDisc) : hbPre_kernel μ z ∈ AOneStar :=
  ⟨hbPre_kernel_holo hμ hz, hbPre_kernel_integrable hμ hz, hbPre_kernel_decay hμ hz⟩

/-- The actual translated Bers derivative factors through the existing harmonic projector. -/
theorem hbPre_derivative_projection {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (a : LinfStar) :
    D0BersR μ (harmonicProj a) = D0BersR μ a := by
  apply AInf.ext_toFun_disc
  intro ζ hζ
  rw [r24_phi_formula hμ _ hζ, r24_phi_formula hμ _ hζ]
  rw [hb_fourth_kernel_transport resolvent_exterior_isOpen (S2C.s2c_conf_g hμ),
    hb_fourth_kernel_transport resolvent_exterior_isOpen (S2C.s2c_conf_g hμ)]
  have hh := hbPre_projection_pairing a (hbPre_kernel_mem_AOne hμ ⟨ζ, hζ, rfl⟩)
  simpa only [hbPre_kernel, mul_div_assoc, mul_assoc] using congrArg
    (fun v : ℂ => -(6 / π) * (deriv (fsans μ) ζ ^ 2 * v)) hh

end TakhtajanTeo

#print axioms TakhtajanTeo.hbPre_kernel_mem_AOne
#print axioms TakhtajanTeo.hbPre_derivative_projection
