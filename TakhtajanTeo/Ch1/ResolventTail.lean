import TakhtajanTeo.Ch1.ResolventCutoff

/-! Smooth compact kernel factors for the localized boundary tail. -/

open Real Complex Filter Set Topology MeasureTheory Metric
open scoped Convolution Classical

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

set_option autoImplicit false

local instance : Measure.IsAddLeftInvariant (volume : Measure (ℂ × ℝ)) := by
  change Measure.IsAddLeftInvariant ((volume : Measure ℂ).prod (volume : Measure ℝ))
  infer_instance

local instance : Measure.IsNegInvariant (volume : Measure (ℂ × ℝ)) := by
  constructor
  change Measure.map (Prod.map (fun z : ℂ => -z) (fun t : ℝ => -t))
    ((volume : Measure ℂ).prod (volume : Measure ℝ)) =
      (volume : Measure ℂ).prod (volume : Measure ℝ)
  rw [← Measure.map_prod_map _ _ measurable_neg measurable_neg,
    Measure.map_neg_eq_self, Measure.map_neg_eq_self]

/-- A globally smooth, compact-in-integration-variables factor for a regularized tail. -/
def resolventTailFactor {a : ℂ} (F : ℝ → ℝ) (inner : ContDiffBump a)
    (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ))
    (z : ℂ) (p : ℂ × ℝ) : ℂ :=
  (outer p.1 * time p.2 * (1 - inner p.1) * (2 / π) * (1 - ‖z‖ ^ 2) ^ 2 *
    p.2 * (1 - p.2) * F (‖z - p.1‖ ^ 2 + p.2 * (1 - ‖z‖ ^ 2) * (1 - ‖p.1‖ ^ 2)) : ℝ)

theorem resolventTailFactor_contDiff {a : ℂ} {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (inner : ContDiffBump a)
    (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℂ × (ℂ × ℝ) => resolventTailFactor F inner outer time q.1 q.2) := by
  have hZ : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℂ × (ℂ × ℝ) => q.1) := contDiff_fst
  have hW : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℂ × (ℂ × ℝ) => q.2.1) := contDiff_snd.fst
  have hT : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℂ × (ℂ × ℝ) => q.2.2) := contDiff_snd.snd
  have hDz := (contDiff_const (c := (1 : ℝ))).sub (hZ.norm_sq ℂ)
  have hDw := (contDiff_const (c := (1 : ℝ))).sub (hW.norm_sq ℂ)
  have hden := ((hZ.sub hW).norm_sq ℂ).add ((hT.mul hDz).mul hDw)
  have hp := (((((((outer.contDiff.comp hW).mul (time.contDiff.comp hT)).mul
    ((contDiff_const (c := (1 : ℝ))).sub (inner.contDiff.comp hW))).mul
      (contDiff_const (c := (2 / π : ℝ)))).mul (hDz.pow 2)).mul hT).mul
        ((contDiff_const (c := (1 : ℝ))).sub hT)).mul (hF.comp hden)
  exact Complex.ofRealCLM.contDiff.comp hp

theorem resolventTailFactor_zero_off_support {a : ℂ} (F : ℝ → ℝ) (inner : ContDiffBump a)
    (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ)) (z : ℂ) {p : ℂ × ℝ}
    (hp : p ∉ tsupport outer ×ˢ tsupport time) : resolventTailFactor F inner outer time z p = 0 := by
  change ¬(p.1 ∈ tsupport outer ∧ p.2 ∈ tsupport time) at hp
  rcases not_and_or.mp hp with hw | ht
  · simp [resolventTailFactor, image_eq_zero_of_notMem_tsupport hw]
  · simp [resolventTailFactor, image_eq_zero_of_notMem_tsupport ht]

theorem resolventTailFactor_hasCompactSupport {a : ℂ} (F : ℝ → ℝ) (inner : ContDiffBump a)
    (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ)) (z : ℂ) :
    HasCompactSupport (resolventTailFactor F inner outer time z) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (outer.hasCompactSupport.prod time.hasCompactSupport)
  intro p hp
  by_contra hnot
  exact hp (resolventTailFactor_zero_off_support F inner outer time z hnot)

/-- Absolute convergence of the regularized tail against a locally integrable input
on the product space. The input may be nonsmooth. -/
theorem resolvent_tail_integrable {a : ℂ} {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (inner : ContDiffBump a)
    (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ))
    {H : ℂ × ℝ → ℂ} (hH : LocallyIntegrable H volume) (z : ℂ) :
    Integrable (fun p : ℂ × ℝ => resolventTailFactor F inner outer time z p * H (-p)) volume := by
  have hg : Continuous (resolventTailFactor F inner outer time z) :=
    ((resolventTailFactor_contDiff hF inner outer time).comp
      (contDiff_const.prodMk contDiff_id)).continuous
  have hi := ((resolventTailFactor_hasCompactSupport F inner outer time z).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℂ) hg hH (0 : ℂ × ℝ)).integrable
  simpa only [zero_sub, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hi

/-- Parameterized convolution makes the regularized tail smooth without taking
derivatives of the locally integrable input. -/
theorem resolvent_tail_contDiff {a : ℂ} {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (inner : ContDiffBump a)
    (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ))
    {H : ℂ × ℝ → ℂ} (hH : LocallyIntegrable H volume) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z =>
      ∫ p : ℂ × ℝ, resolventTailFactor F inner outer time z p * H (-p)) := by
  have hp := contDiffOn_convolution_left_with_param_comp (ContinuousLinearMap.lsmul ℝ ℂ)
    (v := fun _ : ℂ => (0 : ℂ × ℝ)) (g := resolventTailFactor F inner outer time)
    (s := univ) contDiffOn_const isOpen_univ
    (outer.hasCompactSupport.prod time.hasCompactSupport)
    (fun z p _ hp => resolventTailFactor_zero_off_support F inner outer time z hp) hH
    (resolventTailFactor_contDiff hF inner outer time).contDiffOn
  rw [← contDiffOn_univ]
  convert hp using 1
  funext z
  simp only [MeasureTheory.convolution_def, zero_sub, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- The inner cutoff supplies a uniform separation between nearby evaluation points
and integration points where the tail is nonzero. -/
theorem resolvent_tail_separation {a z w : ℂ} (inner : ContDiffBump a)
    (hz : z ∈ ball a (inner.rIn / 2)) (hw : inner w ≠ 1) :
    inner.rIn / 2 ≤ ‖z - w‖ := by
  have hw' : inner.rIn < dist w a := lt_of_not_ge fun h => hw (inner.one_of_mem_closedBall h)
  have hz' : dist z a < inner.rIn / 2 := hz
  have ht : dist w a ≤ ‖z - w‖ + dist z a := by
    simpa only [dist_eq_norm w z, norm_sub_rev w z] using dist_triangle w z a
  linarith

/-- On the true tail integration domain, the regularized factor equals the original
weighted rational integrand exactly. -/
theorem resolventTailFactor_eq {a z w : ℂ} {t δ : ℝ} {F : ℝ → ℝ}
    (inner : ContDiffBump a) (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ))
    (hF : ∀ x, δ ≤ |x| → F x = 1 / x ^ 2)
    (hδ : δ ≤ (inner.rIn / 2) ^ 2) (hout : 1 ≤ outer.rIn) (htime : 1 ≤ time.rIn)
    (hz : z ∈ unitDisc) (hnear : z ∈ ball a (inner.rIn / 2))
    (hw : w ∈ unitDisc) (ht : t ∈ Icc (0 : ℝ) 1) :
    resolventTailFactor F inner outer time z (w, t) =
      ((1 - inner w) * resolventBoundaryIntegrand z w t : ℝ) := by
  have ho : outer w = 1 := outer.one_of_mem_closedBall
    (mem_closedBall_zero_iff.mpr ((mem_ball_zero_iff.mp hw).le.trans hout))
  have ht' : time t = 1 := time.one_of_mem_closedBall (by
    apply mem_closedBall_zero_iff.mpr
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2.trans htime)
  by_cases hi : inner w = 1
  · simp [resolventTailFactor, hi]
  · have hsep := resolvent_tail_separation inner hnear hi
    have hsep2 : (inner.rIn / 2) ^ 2 ≤ ‖z - w‖ ^ 2 := by
      nlinarith [inner.rIn_pos, norm_nonneg (z - w)]
    have hzn := mem_ball_zero_iff.mp hz
    have hwn := mem_ball_zero_iff.mp hw
    have hd : 0 ≤ t * (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) :=
      mul_nonneg (mul_nonneg ht.1 (by nlinarith [norm_nonneg z]))
        (by nlinarith [norm_nonneg w])
    have hlower : δ ≤ ‖z - w‖ ^ 2 + t * (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
      linarith
    have he := hF (‖z - w‖ ^ 2 + t * (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2))
      (hlower.trans (le_abs_self _))
    unfold resolventTailFactor resolventBoundaryIntegrand
    rw [ho, ht', he]
    congr 1
    ring

/-- The bounded input on the product space, reflected to match convolution at zero. -/
def resolventTailInput (g : ℂ → ℂ) (p : ℂ × ℝ) : ℂ :=
  (Icc (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℂ)) (-p.2) *
    unitDisc.piecewise g (fun _ => 0) (-p.1)

theorem resolventTailInput_measurable {g : ℂ → ℂ} (hg : ContinuousOn g unitDisc) :
    Measurable (resolventTailInput g) := by
  have hm : Measurable (unitDisc.piecewise g (fun _ => (0 : ℂ))) :=
    hg.measurable_piecewise continuousOn_const (show MeasurableSet unitDisc from isOpen_ball.measurableSet)
  exact ((measurable_const.indicator measurableSet_Icc).comp measurable_snd.neg).mul
    (hm.comp measurable_fst.neg)

theorem resolventTailInput_norm_le {g : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ w ∈ unitDisc, ‖g w‖ ≤ C) (p : ℂ × ℝ) : ‖resolventTailInput g p‖ ≤ C := by
  by_cases ht : -p.2 ∈ Icc (0 : ℝ) 1
  · by_cases hw : -p.1 ∈ unitDisc
    · simpa [resolventTailInput, ht, hw] using hg (-p.1) hw
    · simpa [resolventTailInput, ht, hw] using hC
  · simpa [resolventTailInput, ht] using hC

theorem resolventTailInput_locallyIntegrable {g : ℂ → ℂ}
    (hg : ContinuousOn g unitDisc) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ w ∈ unitDisc, ‖g w‖ ≤ C) :
    LocallyIntegrable (resolventTailInput g) volume := by
  have hc : LocallyIntegrable (fun _ : ℂ × ℝ => C) volume := continuous_const.locallyIntegrable
  apply hc.mono (resolventTailInput_measurable hg).aestronglyMeasurable
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using resolventTailInput_norm_le hC hb p

theorem resolventTailInput_neg (g : ℂ → ℂ) (p : ℂ × ℝ) :
    resolventTailInput g (-p) =
      (Icc (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℂ)) p.2 *
        unitDisc.piecewise g (fun _ => 0) p.1 := by
  simp only [resolventTailInput, Prod.fst_neg, Prod.snd_neg, neg_neg]
  rw [show -(-p.1) = p.1 from neg_neg p.1]

/-- Fubini for the regularized tail, justified by the already proved absolute convergence. -/
theorem resolvent_tail_integral_prod {a : ℂ} {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (inner : ContDiffBump a)
    (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ))
    {H : ℂ × ℝ → ℂ} (hH : LocallyIntegrable H volume) (z : ℂ) :
    (∫ p : ℂ × ℝ, resolventTailFactor F inner outer time z p * H (-p)) =
      ∫ w : ℂ, ∫ t : ℝ, resolventTailFactor F inner outer time z (w, t) * H (-(w, t)) := by
  have hi := resolvent_tail_integrable hF inner outer time hH z
  rw [Measure.volume_eq_prod] at hi ⊢
  exact integral_prod _ hi

/-- Smoothness of the product-space potential for an actual continuous bounded disk input. -/
theorem resolvent_tail_potential_contDiff {a : ℂ} {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (inner : ContDiffBump a)
    (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ))
    {g : ℂ → ℂ} (hg : ContinuousOn g unitDisc) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ w ∈ unitDisc, ‖g w‖ ≤ C) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => ∫ p : ℂ × ℝ,
      resolventTailFactor F inner outer time z p * resolventTailInput g (-p)) := by
  exact resolvent_tail_contDiff hF inner outer time (resolventTailInput_locallyIntegrable hg hC hb)

private theorem tail_potential_eq_iterated {a : ℂ} {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (inner : ContDiffBump a)
    (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ))
    {g : ℂ → ℂ} (hg : ContinuousOn g unitDisc) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ w ∈ unitDisc, ‖g w‖ ≤ C) (z : ℂ) :
    (∫ p : ℂ × ℝ, resolventTailFactor F inner outer time z p * resolventTailInput g (-p)) =
      ∫ w in unitDisc, (∫ t in Icc (0 : ℝ) 1, resolventTailFactor F inner outer time z (w, t)) * g w := by
  rw [resolvent_tail_integral_prod hF inner outer time (resolventTailInput_locallyIntegrable hg hC hb)]
  rw [← integral_indicator (show MeasurableSet unitDisc from isOpen_ball.measurableSet)]
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : w ∈ unitDisc
  · rw [indicator_of_mem hw]
    calc
      _ = ∫ t : ℝ, (Icc (0 : ℝ) 1).indicator
          (fun t => resolventTailFactor F inner outer time z (w, t) * g w) t := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [resolventTailInput_neg]
        by_cases ht : t ∈ Icc (0 : ℝ) 1 <;> simp [hw, ht]
      _ = ∫ t in Icc (0 : ℝ) 1, resolventTailFactor F inner outer time z (w, t) * g w :=
        integral_indicator measurableSet_Icc
      _ = _ := integral_mul_const _ _
  · rw [indicator_of_notMem hw]
    have he (t : ℝ) : resolventTailInput g (-(w, t)) = 0 := by
      rw [resolventTailInput_neg]
      simp [hw]
    simp only [he, mul_zero, integral_zero]

private theorem tail_factor_time_integral {a z w : ℂ} {δ : ℝ} {F : ℝ → ℝ}
    (inner : ContDiffBump a) (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ))
    (hF : ∀ x, δ ≤ |x| → F x = 1 / x ^ 2)
    (hδ : δ ≤ (inner.rIn / 2) ^ 2) (hout : 1 ≤ outer.rIn) (htime : 1 ≤ time.rIn)
    (hz : z ∈ unitDisc) (hnear : z ∈ ball a (inner.rIn / 2)) (hw : w ∈ unitDisc) :
    (∫ t in Icc (0 : ℝ) 1, resolventTailFactor F inner outer time z (w, t)) =
      ((1 - inner w) : ℝ) * (resolventKernel z w : ℂ) * (rho w : ℂ) := by
  by_cases hi : inner w = 1
  · simp [resolventTailFactor, hi]
  · have hzw : z ≠ w := by
      intro he
      have hp := resolvent_tail_separation inner hnear hi
      rw [he, sub_self, norm_zero] at hp
      linarith [inner.rIn_pos]
    calc
      _ = ∫ t in Icc (0 : ℝ) 1, (((1 - inner w) * resolventBoundaryIntegrand z w t : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        exact resolventTailFactor_eq inner outer time hF hδ hout htime hz hnear hw ht
      _ = (((1 - inner w) * resolventBoundaryKernel z w : ℝ) : ℂ) := by
        rw [integral_complex_ofReal (μ := volume.restrict (Icc (0 : ℝ) 1))
          (f := fun t : ℝ => (1 - inner w) * resolventBoundaryIntegrand z w t),
          integral_const_mul, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        rfl
      _ = _ := by
        rw [resolventBoundaryKernel_eq_weighted hz hw hzw]
        push_cast
        ring

/-- Exact identification of the smooth product-space potential with the original tail operator. -/
theorem resolvent_tail_potential_eq {a z : ℂ} {δ : ℝ} {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (inner : ContDiffBump a)
    (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ))
    (hFeq : ∀ x, δ ≤ |x| → F x = 1 / x ^ 2)
    (hδ : δ ≤ (inner.rIn / 2) ^ 2) (hout : 1 ≤ outer.rIn) (htime : 1 ≤ time.rIn)
    {g : ℂ → ℂ} (hg : ContinuousOn g unitDisc) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ w ∈ unitDisc, ‖g w‖ ≤ C) (hz : z ∈ unitDisc)
    (hnear : z ∈ ball a (inner.rIn / 2)) :
    (∫ p : ℂ × ℝ, resolventTailFactor F inner outer time z p * resolventTailInput g (-p)) =
      resolventOp unitDisc (fun w => ((1 - inner w : ℝ) : ℂ) * g w) z := by
  rw [tail_potential_eq_iterated hF inner outer time hg hC hb]
  unfold resolventOp
  apply setIntegral_congr_fun (show MeasurableSet unitDisc from isOpen_ball.measurableSet)
  intro w hw
  dsimp only
  rw [tail_factor_time_integral inner outer time hFeq hδ hout htime hz hnear hw]
  ring

/-- The actual tail operator is C-infinity near the center of its inner cutoff,
even when the original disk input is merely continuous and bounded. -/
theorem resolvent_tail_operator_contDiffAt {a z : ℂ} (inner : ContDiffBump a)
    {g : ℂ → ℂ} (hg : ContinuousOn g unitDisc) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ w ∈ unitDisc, ‖g w‖ ≤ C) (hz : z ∈ unitDisc)
    (hnear : z ∈ ball a (inner.rIn / 2)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (resolventOp unitDisc (fun w => ((1 - inner w : ℝ) : ℂ) * g w)) z := by
  have hδ : 0 < (inner.rIn / 2) ^ 2 := sq_pos_of_pos (by linarith [inner.rIn_pos])
  obtain ⟨F, hF, hFpos, hFeq⟩ := exists_resolvent_cutoff_inv_sq hδ
  let outer : ContDiffBump (0 : ℂ) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let time : ContDiffBump (0 : ℝ) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  have hp := (resolvent_tail_potential_contDiff hF inner outer time hg hC hb).contDiffAt (x := z)
  apply hp.congr_of_eventuallyEq
  filter_upwards [((show IsOpen unitDisc from isOpen_ball).inter isOpen_ball).mem_nhds
    (show z ∈ unitDisc ∩ ball a (inner.rIn / 2) from ⟨hz, hnear⟩)] with x hx
  exact (resolvent_tail_potential_eq hF inner outer time hFeq le_rfl (by rfl) (by rfl)
    hg hC hb hx.1 hx.2).symm

end TakhtajanTeo
