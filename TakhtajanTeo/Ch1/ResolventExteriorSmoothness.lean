import TakhtajanTeo.Ch1.ResolventTail

/-! Exterior bounded-smooth output for RK3 (TT:1112–1124).
The inverted input is allowed to be discontinuous at the missing center.
Only a bounded measurable tail and smoothness near the evaluation point are used. -/

open Real Complex Filter Set Topology MeasureTheory Metric
open scoped Convolution Classical

noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option autoImplicit false

/-- The existing product-space tail input is locally integrable for measurable
bounded data; no continuity at the center is required. -/
theorem resolventTailInput_locallyIntegrable_measurable {g : ℂ → ℂ}
    (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ w ∈ unitDisc, ‖g w‖ ≤ C) :
    LocallyIntegrable (resolventTailInput g) volume := by
  have hm : Measurable (unitDisc.piecewise g (fun _ => (0 : ℂ))) :=
    Measurable.piecewise (show MeasurableSet unitDisc from measurableSet_ball) hg measurable_const
  have hH : Measurable (resolventTailInput g) :=
    ((measurable_const.indicator measurableSet_Icc).comp measurable_snd.neg).mul
      (hm.comp measurable_fst.neg)
  have hc : LocallyIntegrable (fun _ : ℂ × ℝ => C) volume := continuous_const.locallyIntegrable
  apply hc.mono hH.aestronglyMeasurable
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using resolventTailInput_norm_le hC hb p

private theorem measurable_tail_potential_eq_iterated {a : ℂ} {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (inner : ContDiffBump a)
    (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ))
    {g : ℂ → ℂ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ w ∈ unitDisc, ‖g w‖ ≤ C) (z : ℂ) :
    (∫ p : ℂ × ℝ, resolventTailFactor F inner outer time z p * resolventTailInput g (-p)) =
      ∫ w in unitDisc, (∫ t in Icc (0 : ℝ) 1, resolventTailFactor F inner outer time z (w, t)) * g w := by
  rw [resolvent_tail_integral_prod hF inner outer time
    (resolventTailInput_locallyIntegrable_measurable hg hC hb)]
  rw [← integral_indicator (show MeasurableSet unitDisc from measurableSet_ball)]
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

private theorem measurable_tail_factor_integral {a z w : ℂ} {δ : ℝ} {F : ℝ → ℝ}
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

/-- The existing convolution potential represents the true resolvent tail for
measurable bounded data, by absolute integrability and Fubini. -/
theorem resolvent_tail_potential_eq_measurable {a z : ℂ} {δ : ℝ} {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (inner : ContDiffBump a)
    (outer : ContDiffBump (0 : ℂ)) (time : ContDiffBump (0 : ℝ))
    (hFeq : ∀ x, δ ≤ |x| → F x = 1 / x ^ 2)
    (hδ : δ ≤ (inner.rIn / 2) ^ 2) (hout : 1 ≤ outer.rIn) (htime : 1 ≤ time.rIn)
    {g : ℂ → ℂ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ w ∈ unitDisc, ‖g w‖ ≤ C) (hz : z ∈ unitDisc)
    (hnear : z ∈ ball a (inner.rIn / 2)) :
    (∫ p : ℂ × ℝ, resolventTailFactor F inner outer time z p * resolventTailInput g (-p)) =
      resolventOp unitDisc (fun w => ((1 - inner w : ℝ) : ℂ) * g w) z := by
  rw [measurable_tail_potential_eq_iterated hF inner outer time hg hC hb]
  unfold resolventOp
  apply setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball)
  intro w hw
  dsimp only
  rw [measurable_tail_factor_integral inner outer time hFeq hδ hout htime hz hnear hw]
  ring

/-- A bounded measurable input has a smooth tail near the inner cutoff center. -/
theorem resolvent_tail_operator_contDiffAt_measurable {a z : ℂ} (inner : ContDiffBump a)
    {g : ℂ → ℂ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ w ∈ unitDisc, ‖g w‖ ≤ C) (hz : z ∈ unitDisc)
    (hnear : z ∈ ball a (inner.rIn / 2)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (resolventOp unitDisc (fun w => ((1 - inner w : ℝ) : ℂ) * g w)) z := by
  have hδ : 0 < (inner.rIn / 2) ^ 2 := sq_pos_of_pos (by linarith [inner.rIn_pos])
  obtain ⟨F, hF, hFpos, hFeq⟩ := exists_resolvent_cutoff_inv_sq hδ
  let outer : ContDiffBump (0 : ℂ) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let time : ContDiffBump (0 : ℝ) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  have hp := (resolvent_tail_contDiff hF inner outer time
    (resolventTailInput_locallyIntegrable_measurable hg hC hb)).contDiffAt (x := z)
  apply hp.congr_of_eventuallyEq
  filter_upwards [((show IsOpen unitDisc from isOpen_ball).inter isOpen_ball).mem_nhds
    (show z ∈ unitDisc ∩ ball a (inner.rIn / 2) from ⟨hz, hnear⟩)] with x hx
  exact (resolvent_tail_potential_eq_measurable hF inner outer time hFeq le_rfl (by rfl) (by rfl)
    hg hC hb hx.1 hx.2).symm

/-- A disk potential of bounded measurable data is smooth wherever its input is
smooth. This includes punctured-disk data with no regularity at the origin. -/
theorem resolventOp_contDiffOn_of_measurable_locally_smooth {U : Set ℂ}
    (hU : IsOpen U) (hUD : U ⊆ unitDisc) {g : ℂ → ℂ} (hgm : Measurable g)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (hb : ∃ C : ℝ, ∀ w ∈ unitDisc, ‖g w‖ ≤ C) :
    ContDiffOn ℝ (⊤ : ℕ∞) (resolventOp unitDisc g) U := by
  obtain ⟨C, hb⟩ := hb
  have hC : 0 ≤ C := (norm_nonneg (g 0)).trans (hb 0 (by simp [unitDisc]))
  have hD : IsOpen unitDisc := isOpen_ball
  intro z hz
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU z hz
  let b : ContDiffBump z :=
    { rIn := R / 4, rOut := R / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hs : tsupport b ⊆ U := by
    rw [b.tsupport_eq]
    intro w hw
    apply hRU
    have hd : dist w z ≤ R / 2 := hw
    change dist w z < R
    linarith
  have hbc : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => (b w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hbs : tsupport (fun w : ℂ => (b w : ℂ)) ⊆ U :=
    (tsupport_comp_subset (g := Complex.ofReal) (by simp) b).trans hs
  have hbh : HasCompactSupport (fun w : ℂ => (b w : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  have hI : ContDiff ℝ (⊤ : ℕ∞) (fun w => g w * (b w : ℂ)) :=
    resolvent_source_mul_contDiff hU hbc hg hbs
  have hIc : HasCompactSupport (fun w => g w * (b w : ℂ)) := hbh.mul_left (f := g)
  have hIs : tsupport (fun w => g w * (b w : ℂ)) ⊆ unitDisc :=
    (tsupport_mul_subset_right (f := g) (g := fun w => (b w : ℂ))).trans (hbs.trans hUD)
  have hIb : ∀ w ∈ unitDisc, ‖g w * (b w : ℂ)‖ ≤ C := by
    intro w hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    calc
      ‖g w‖ * b w ≤ C * 1 := mul_le_mul (hb w hw) b.le_one b.nonneg hC
      _ = C := mul_one C
  have hTc : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => ((1 - b w : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.sub b.contDiff)
  have hTb : ∀ w ∈ unitDisc, ‖((1 - b w : ℝ) : ℂ) * g w‖ ≤ C := by
    intro w hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr b.le_one)]
    calc
      (1 - b w) * ‖g w‖ ≤ 1 * C :=
        mul_le_mul (by linarith [b.nonneg' w]) (hb w hw) (norm_nonneg _) (by norm_num)
      _ = C := one_mul C
  have hsplit (v : ℂ) (hv : v ∈ unitDisc) : resolventOp unitDisc g v =
      resolventOp unitDisc (fun w => g w * (b w : ℂ)) v +
        resolventOp unitDisc (fun w => ((1 - b w : ℝ) : ℂ) * g w) v := by
    have hiI := resolvent_integrand_integrable_of_bounded (Or.inl rfl)
      hI.continuous.aestronglyMeasurable hIb hv
    have hiT := resolvent_integrand_integrable_of_bounded (Or.inl rfl)
      (hTc.continuous.measurable.mul hgm).aestronglyMeasurable hTb hv
    unfold resolventOp
    dsimp only [Pi.mul_apply] at hiT ⊢
    rw [← integral_add hiI hiT]
    apply integral_congr_ae
    filter_upwards [] with w
    push_cast
    ring
  have hIo := (resolventOp_contDiffOn_compact hI hIc hIs).contDiffAt (hD.mem_nhds (hUD hz))
  have hTo := resolvent_tail_operator_contDiffAt_measurable b hgm hC hb (hUD hz)
    (mem_ball_self (by linarith [b.rIn_pos] : 0 < b.rIn / 2))
  apply ContDiffAt.contDiffWithinAt
  apply (hIo.add hTo).congr_of_eventuallyEq
  filter_upwards [hD.mem_nhds (hUD hz)] with v hv
  exact hsplit v hv

private theorem exterior_pullback_mapsTo :
    MapsTo (fun z : ℂ => z⁻¹) (unitDisc \ {0}) unitDiscExterior := by
  intro z hz
  have hz0 : z ≠ 0 := by simpa using hz.2
  change 1 < ‖z⁻¹‖
  rw [norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr (mem_ball_zero_iff.mp hz.1)

private theorem exterior_pullback_inv_contDiff :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => z⁻¹) (unitDisc \ {0}) :=
  contDiffOn_id.inv (fun z hz => by simpa using hz.2)

/-- The exterior input transported to the punctured disk and set to zero on the
complement. The assigned center value is only a measurable representative. -/
def resolventExteriorPullback (g : ℂ → ℂ) : ℂ → ℂ :=
  (unitDisc \ {(0 : ℂ)}).piecewise (fun z => g z⁻¹) (fun _ => 0)

/-- The inverted exterior input admits a globally measurable representative. -/
theorem resolventExteriorPullback_measurable {g : ℂ → ℂ}
    (hg : ContinuousOn g unitDiscExterior) : Measurable (resolventExteriorPullback g) := by
  have hc : ContinuousOn (fun z => g z⁻¹) (unitDisc \ {0}) :=
    hg.comp exterior_pullback_inv_contDiff.continuousOn exterior_pullback_mapsTo
  exact hc.measurable_piecewise continuousOn_const
    ((show IsOpen unitDisc from isOpen_ball).sdiff isClosed_singleton).measurableSet

/-- The pullback is smooth on the punctured disk, without a center regularity claim. -/
theorem resolventExteriorPullback_contDiffOn {g : ℂ → ℂ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g unitDiscExterior) :
    ContDiffOn ℝ (⊤ : ℕ∞) (resolventExteriorPullback g) (unitDisc \ {0}) := by
  apply (hg.comp exterior_pullback_inv_contDiff exterior_pullback_mapsTo).congr
  intro z hz
  simp [resolventExteriorPullback, hz, Function.comp_apply]

/-- The arbitrary center value zero preserves the exterior uniform bound. -/
theorem resolventExteriorPullback_bound {g : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ w ∈ unitDiscExterior, ‖g w‖ ≤ C) :
    ∀ w ∈ unitDisc, ‖resolventExteriorPullback g w‖ ≤ C := by
  intro w hw
  by_cases hz : w = 0
  · subst w
    simpa [resolventExteriorPullback] using hC
  · have hwU : w ∈ unitDisc \ {0} := ⟨hw, by simpa using hz⟩
    simpa [resolventExteriorPullback, hwU] using hg w⁻¹ (exterior_pullback_mapsTo hwU)

/-- Actual inversion change of variables for the resolvent integral. The center
is removed only as a null singleton, not as a removable singularity of the input. -/
theorem resolventOp_exterior_inv (g : ℂ → ℂ) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    resolventOp unitDiscExterior g z =
      resolventOp unitDisc (resolventExteriorPullback g) z⁻¹ := by
  have hf := resolvent_inv_exterior_conformal
  have hi := ahP_integral_image (U := unitDiscExterior) resolvent_exterior_isOpen hf.1 hf.2.1
    (fun u => (resolventKernel z⁻¹ u : ℂ) * resolventExteriorPullback g u * rho u)
  rw [hf.2.2] at hi
  unfold resolventOp
  calc
    _ = ∫ w in unitDiscExterior, ‖deriv (fun u : ℂ => u⁻¹) w‖ ^ 2 •
        ((resolventKernel z⁻¹ w⁻¹ : ℂ) * resolventExteriorPullback g w⁻¹ * rho w⁻¹) := by
      apply setIntegral_congr_fun resolvent_exterior_isOpen.measurableSet
      intro w hw
      dsimp only
      have hwU : w⁻¹ ∈ unitDisc \ {0} := hf.mapsTo hw
      have hG : resolventExteriorPullback g w⁻¹ = g w := by
        simp [resolventExteriorPullback, hwU]
      rw [hG]
      have hweight := congrArg Complex.ofReal (resolventKernel_inv_weight
        (resolvent_exterior_ne_zero hz) (resolvent_exterior_ne_zero hw))
      push_cast at hweight
      simp only [Complex.real_smul, Complex.ofReal_pow]
      linear_combination -(g w) * hweight
    _ = ∫ u in unitDisc \ {0}, (resolventKernel z⁻¹ u : ℂ) * resolventExteriorPullback g u * rho u := hi.symm
    _ = ∫ u in unitDisc, (resolventKernel z⁻¹ u : ℂ) * resolventExteriorPullback g u * rho u :=
      setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton (0 : ℂ)))

/-- The exterior resolvent output is genuinely smooth, although its inverted
input can be discontinuous at zero (RK3, TT:1112–1124). -/
theorem RK3_output_smooth_exterior {g : ℂ → ℂ} (hg : g ∈ BCinf unitDiscExterior) :
    ContDiffOn ℝ (⊤ : ℕ∞) (resolventOp unitDiscExterior g) unitDiscExterior := by
  obtain ⟨C, hC⟩ := hg.2
  have hCb : ∀ w ∈ unitDiscExterior, ‖g w‖ ≤ max C 0 := fun w hw => (hC w hw).trans (le_max_left _ _)
  have hbound : ∃ C : ℝ, ∀ w ∈ unitDisc, ‖resolventExteriorPullback g w‖ ≤ C :=
    ⟨max C 0, resolventExteriorPullback_bound (le_max_right _ _) hCb⟩
  have hU : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hsm := resolventOp_contDiffOn_of_measurable_locally_smooth hU sdiff_subset
    (resolventExteriorPullback_measurable hg.1.continuousOn)
    (resolventExteriorPullback_contDiffOn hg.1) hbound
  have hinv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => z⁻¹) unitDiscExterior :=
    contDiffOn_id.inv (fun z hz => resolvent_exterior_ne_zero hz)
  apply (hsm.comp hinv resolvent_inv_exterior_conformal.mapsTo).congr
  intro z hz
  exact resolventOp_exterior_inv g hz

/-- The full bounded-smooth output clause of RK3 on the exterior disk. -/
theorem RK3_output_BCinf_exterior {g : ℂ → ℂ} (hg : g ∈ BCinf unitDiscExterior) :
    resolventOp unitDiscExterior g ∈ BCinf unitDiscExterior :=
  ⟨RK3_output_smooth_exterior hg, RK3_output_bounded (Or.inr rfl) hg⟩

end TakhtajanTeo
