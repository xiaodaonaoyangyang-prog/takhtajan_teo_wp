import TakhtajanTeo.Appendix.BergmanPeriodModel
import TakhtajanTeo.Ch2.S2_Mixed

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-! ## `remark_2_2`: the complement of the welding pair is null -/

/-- For `μ ∈ L∞(𝔻*)₁`, `𝖿 = f^μ` and `𝗀 = g_μ`. -/
theorem r22_fsans_gsans {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    fsans μ = fB μ ∧ gsans μ = gMu μ := by
  have hid : Function.invFun (id : ExtPlane → ExtPlane) = id :=
    funext (fun z => Function.leftInverse_invFun Function.injective_id z)
  refine ⟨?_, ?_⟩
  · ext z; simp [fsans, AppB.b8_weldConst_zero hμ, lambdaW]
  · ext z
    simp only [gsans, AppB.b8_weldConst_zero hμ, alphaMu_eq_id, hid, id_eq,
      lambdaW, zero_mul, zero_add, div_one]
    rfl

/-- `g_μ(u) = w^μ(p)` whenever `w_μ(p) = u ∈ 𝔻*`. -/
theorem r22_wB_of_wAS {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ℂ} (hu : 1 < ‖u‖) {p : ExtPlane}
    (hp : wAS μ p = (u : ExtPlane)) : wB μ p = ((gMu μ u : ℂ) : ExtPlane) := by
  have h1 : Function.invFun (wAS μ) (wAS μ p) = p :=
    Function.leftInverse_invFun (wAS_bijective μ).1 p
  rw [hp] at h1
  rw [← h1]
  exact (gMu_sphere_factorization hμ hu).symm

/-- A point outside `𝖿(𝔻) ∪ 𝗀(𝔻*)` is the `w^μ`-image of a point of the unit circle. -/
theorem r22_complement_circle {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ}
    (hw : w ∉ fB μ '' unitDisc ∪ gMu μ '' unitDiscExterior) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ wB μ (z : ExtPlane) = (w : ExtPlane) := by
  obtain ⟨hB, -⟩ := wB_spec hμ
  obtain ⟨M, hM, W, hW, hfin, hinfty, f, hfd, hf0, hf1, hpole⟩ := hB
  obtain ⟨p, hp⟩ := (wB_bijective μ).2 (w : ExtPlane)
  have hpoleW : ∀ q : ExtPlane, wAS μ q = extInf → wB μ q = extInf := by
    intro q hq
    have h1 : Function.invFun (wAS μ) (wAS μ q) = q :=
      Function.leftInverse_invFun (wAS_bijective μ).1 q
    rw [hq] at h1
    rw [← h1]
    exact hpole
  have hg : ∀ u : ℂ, 1 < ‖u‖ → ∀ q : ExtPlane, wAS μ q = (u : ExtPlane) → wB μ q = (w : ExtPlane) → False := by
    intro u hu q hq hqw
    have h1 := r22_wB_of_wAS hμ hu hq
    rw [h1] at hqw
    exact hw (Or.inr ⟨u, hu, OnePoint.coe_injective hqw⟩)
  have hne : ∀ q : ExtPlane, wB μ q = extInf → wB μ q = (w : ExtPlane) → False := by
    intro q h1 h2
    rw [h1] at h2
    exact OnePoint.infty_ne_coe _ h2
  induction p using OnePoint.rec with
  | infty =>
    exfalso
    rcases wAS_maps_infty hμ with h0 | ⟨u, hu, h0⟩
    · exact hne _ (hpoleW _ h0) hp
    · exact hg u hu _ h0 hp
  | coe z =>
    rcases lt_trichotomy ‖z‖ 1 with hz | hz | hz
    · exfalso
      have h1 := wB_disc_eq_fB hμ (mem_ball_zero_iff.mpr hz)
      rw [h1] at hp
      exact hw (Or.inl ⟨z, mem_ball_zero_iff.mpr hz, OnePoint.coe_injective hp⟩)
    · exact ⟨z, hz, hp⟩
    · exfalso
      rcases wAS_maps_ext hμ hz with h0 | ⟨u, hu, h0⟩
      · exact hne _ (hpoleW _ h0) hp
      · exact hg u hu _ h0 hp

/-- (b) The complement of `𝖿(𝔻) ∪ 𝗀(𝔻*)` is a null set. -/
theorem r22_complement_null {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    volume ((fsans μ '' unitDisc ∪ gsans μ '' unitDiscExterior)ᶜ) = 0 := by
  rw [(r22_fsans_gsans hμ).1, (r22_fsans_gsans hμ).2]
  obtain ⟨hB, -⟩ := wB_spec hμ
  obtain ⟨M, hM, W, hW, hfin, hinfty, f, hfd, hf0, hf1, hpole⟩ := hB
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  obtain ⟨K, hK⟩ := hW.1
  have hS : volume (W '' sphere (0 : ℂ) 1) = 0 :=
    ac_n_volume_image_null_of_isKQC hK (Set.subset_univ _) (Measure.addHaar_sphere volume 0 1)
  set s : Set ℂ := W '' sphere (0 : ℂ) 1 ∩ {x : ℂ | c * x + d ≠ 0} with hs
  have hs0 : volume s = 0 := measure_mono_null Set.inter_subset_left hS
  have hdiff : DifferentiableOn ℝ (fun x : ℂ => (a * x + b) / (c * x + d)) s := by
    have : DifferentiableOn ℂ (fun x : ℂ => (a * x + b) / (c * x + d)) {x : ℂ | c * x + d ≠ 0} :=
      DifferentiableOn.div (by fun_prop) (by fun_prop) (fun x hx => hx)
    exact (this.restrictScalars ℝ).mono Set.inter_subset_right
  have hE := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hs0
  refine measure_mono_null (fun w hw => ?_) hE
  obtain ⟨z, hz, hzw⟩ := r22_complement_circle hμ hw
  rw [hfin z] at hzw
  by_cases hcz : c * W z + d = 0
  · exfalso
    have := hzw
    simp only [LiZhongQC.mobiusExt, OnePoint.elim_some, hcz, if_true] at this
    exact OnePoint.infty_ne_coe _ this
  · refine ⟨W z, ⟨⟨z, mem_sphere_zero_iff_norm.mpr hz, rfl⟩, hcz⟩, ?_⟩
    simp only [LiZhongQC.mobiusExt, OnePoint.elim_some, hcz, if_false] at hzw
    exact OnePoint.coe_injective hzw

/-- (M1') Green identity on the gap for any `C¹` (off `0`) function `W`. -/
theorem mg_gap_green_gen {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {W : ℂ → ℂ} (hWs : ContDiffOn ℝ 1 W {0}ᶜ) :
    (∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ, dzbar W w) =
      -(1 / 2 : ℂ) * (∫ θ in (0 : ℝ)..2 * π,
        W (f (circleMap 0 ρ θ)) * deriv f (circleMap 0 ρ θ) * circleMap 0 ρ θ) +
      (1 / 2 : ℂ) * (∫ θ in (0 : ℝ)..2 * π,
        W (g (circleMap 0 (1 / ρ) θ)) * deriv g (circleMap 0 (1 / ρ) θ) *
          circleMap 0 (1 / ρ) θ) := by
  have h' := h
  obtain ⟨hfd, hfi, hf0, hf1, hgu, hdisj⟩ := h
  have hR : 1 < 1 / ρ := one_lt_one_div hρ0 hρ1
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hUo : IsOpen unitDisc := isOpen_ball
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hg0 : ∀ w ∈ g '' unitDiscExterior, w ≠ 0 := by
    intro w hw hw0
    exact Set.disjoint_left.mp hdisj ⟨0, h0D, by rw [hf0]; exact hw0.symm⟩ hw
  obtain ⟨cg, χ, hcg, hcg1, hcg0, hχ, hχg, hχ1⟩ := mg_gcut hgu hR
  -- the integrand
  set Φ : ℂ → ℂ := fun w => χ w * W w with hΦ
  have hΦs : ContDiffOn ℝ 1 Φ {0}ᶜ := hχ.contDiffOn.mul hWs
  have hgsub : g '' unitDiscExterior ⊆ {0}ᶜ := fun w hw => hg0 w hw
  have hgz : ∀ z : ℂ, 1 < ‖z‖ → g z ≠ 0 := fun z hz => hg0 _ ⟨z, hz, rfl⟩
  -- far support
  obtain ⟨R1, hR1⟩ := mg_far_exterior h' (T := 2 * (1 / ρ)) (by positivity)
  have hfar : ∀ w : ℂ, |R1| + 1 ≤ ‖w‖ → Φ w = 0 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hR1 w (by linarith [le_abs_self R1])
    have hz1 : 1 < ‖z‖ := by linarith
    simp only [hΦ]
    rw [hχg z hz1, hcg0 z hz]
    simp
  obtain ⟨hFint, hFeq⟩ := mg_green_fchart hfd hfi hf0 hρ0 hρ1 hΦs hfar
  have hG := mg_green_gchart hgu hR (Φ := Φ) (hΦs.mono hgsub) (fun z hz => by
    have hz1 : 1 < ‖z‖ := by linarith
    simp only [hΦ]
    rw [hχg z hz1, hcg0 z hz]
    simp)
  -- regions
  set Kf : Set ℂ := f '' closedBall (0 : ℂ) ρ with hKf
  set Kg : Set ℂ := g '' {z : ℂ | 1 / ρ ≤ ‖z‖} with hKg
  have hKfc : IsCompact Kf := (isCompact_closedBall (0 : ℂ) ρ).image_of_continuousOn
    (hfd.continuousOn.mono (fun z hz => mem_ball_zero_iff.mpr
      (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hρ1)))
  have hKgc : IsClosed Kg := mg_image_closed hgu hR
  have hdKfKg : Disjoint Kf Kg := by
    rw [Set.disjoint_left]
    rintro w ⟨u, hu, rfl⟩ ⟨z, hz, hzu⟩
    have huD : u ∈ unitDisc := mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hu) hρ1)
    exact Set.disjoint_left.mp hdisj ⟨u, huD, rfl⟩ ⟨z, lt_of_lt_of_le hR hz, hzu⟩
  have hunion : (Kf ∪ Kg)ᶜ ∪ Kg = Kfᶜ := by
    ext w
    simp only [mem_union, mem_compl_iff]
    constructor
    · rintro (h1 | h1)
      · exact fun hf => h1 (Or.inl hf)
      · exact fun hf => Set.disjoint_left.mp hdKfKg hf h1
    · intro h1
      by_cases hw : w ∈ Kg
      · exact Or.inr hw
      · exact Or.inl (fun hh => hh.elim h1 hw)
  have hdisj2 : Disjoint (Kf ∪ Kg)ᶜ Kg := by
    rw [Set.disjoint_left]
    intro w hw hwg
    exact hw (Or.inr hwg)
  have hKgm : MeasurableSet Kg := hKgc.measurableSet
  have hGapm : MeasurableSet (Kf ∪ Kg)ᶜ := (hKfc.isClosed.union hKgc).measurableSet.compl
  have hint1 : IntegrableOn (dzbar Φ) (Kf ∪ Kg)ᶜ := by
    refine hFint.mono_set ?_
    rw [← hunion]; exact subset_union_left
  have hint2 : IntegrableOn (dzbar Φ) Kg := by
    refine hFint.mono_set ?_
    rw [← hunion]; exact subset_union_right
  have hsplit : ∫ w in Kfᶜ, dzbar Φ w = (∫ w in (Kf ∪ Kg)ᶜ, dzbar Φ w) + ∫ w in Kg, dzbar Φ w := by
    rw [← hunion]
    exact setIntegral_union hdisj2 hKgm hint1 hint2
  -- the gap integral
  have hgap : ∫ w in (Kf ∪ Kg)ᶜ, dzbar Φ w = ∫ w in (Kf ∪ Kg)ᶜ, dzbar W w := by
    refine setIntegral_congr_fun hGapm (fun w hw => ?_)
    have hev : Φ =ᶠ[𝓝 w] W := by
      filter_upwards [(hKfc.isClosed.union hKgc).isOpen_compl.mem_nhds hw] with u hu
      have hχu : χ u = 1 := by
        by_cases hug : u ∈ g '' unitDiscExterior
        · obtain ⟨z, hz, rfl⟩ := hug
          have hzR : ‖z‖ < 1 / ρ := by
            by_contra hge
            exact hu (Or.inr ⟨z, not_lt.mp hge, rfl⟩)
          rw [hχg z hz, hcg1 z hzR.le]
        · exact hχ1 u hug
      simp only [hΦ, hχu, one_mul]
    exact dzbar_congr_of_eventuallyEq hev
  -- boundary terms
  have hfb : (∮ z in C(0, ρ), Φ (f z) * deriv f z) = I * ∫ θ in (0 : ℝ)..2 * π,
      W (f (circleMap 0 ρ θ)) * deriv f (circleMap 0 ρ θ) * circleMap 0 ρ θ := by
    rw [mg_circle_eq]
    congr 1
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hz : ‖circleMap 0 ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos hρ0]
    have hzD : circleMap 0 ρ θ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hz]; exact hρ1)
    have hχf : χ (f (circleMap 0 ρ θ)) = 1 :=
      hχ1 _ (fun hm => Set.disjoint_left.mp hdisj ⟨_, hzD, rfl⟩ hm)
    simp only [hΦ]
    rw [hχf]
    ring
  have hgb : (∮ z in C(0, 1 / ρ), Φ (g z) * deriv g z) = I * ∫ θ in (0 : ℝ)..2 * π,
      W (g (circleMap 0 (1 / ρ) θ)) * deriv g (circleMap 0 (1 / ρ) θ) *
        circleMap 0 (1 / ρ) θ := by
    rw [mg_circle_eq]
    congr 1
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hz : ‖circleMap 0 (1 / ρ) θ‖ = 1 / ρ := by rw [norm_circleMap_zero, abs_of_pos (by positivity)]
    have hz1 : 1 < ‖circleMap 0 (1 / ρ) θ‖ := by rw [hz]; exact hR
    simp only [hΦ]
    rw [hχg _ hz1, hcg1 _ (by rw [hz])]
    ring
  rw [hfb] at hFeq
  rw [hgb] at hG
  set A : ℂ := ∫ θ in (0 : ℝ)..2 * π,
      W (f (circleMap 0 ρ θ)) * deriv f (circleMap 0 ρ θ) * circleMap 0 ρ θ with hA
  set B : ℂ := ∫ θ in (0 : ℝ)..2 * π,
      W (g (circleMap 0 (1 / ρ) θ)) * deriv g (circleMap 0 (1 / ρ) θ) *
        circleMap 0 (1 / ρ) θ with hB
  have hX : ∫ w in Kfᶜ, dzbar Φ w = -A / 2 := by
    have h1 : I * (2 * ∫ w in Kfᶜ, dzbar Φ w) = I * (-A) := by linear_combination hFeq
    have := mul_left_cancel₀ Complex.I_ne_zero h1
    linear_combination this / 2
  have hY : ∫ w in Kg, dzbar Φ w = -B / 2 := by
    have h1 : I * (2 * ∫ w in Kg, dzbar Φ w) = I * (-B) := by linear_combination hG
    have := mul_left_cancel₀ Complex.I_ne_zero h1
    linear_combination this / 2
  rw [← hgap]
  linear_combination (-1 : ℂ) * hsplit + hX - hY



/-- The gap integrals of `‖U'‖²` tend to the (null) integral over the complement `F`. -/
theorem mg_gap_integral_tendsto_gen {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ {0}ᶜ) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n ∧ r n < 1) (hmono : Monotone r)
    (hlim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => ∫ w in (f '' closedBall (0 : ℂ) (r n) ∪ g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ,
      φ w) atTop (𝓝 0) := by
  obtain ⟨hfd, hfi, hf0, hf1, hgu, hdisj⟩ := h
  have h' : IsNormalizedDisjointPair f g := ⟨hfd, hfi, hf0, hf1, hgu, hdisj⟩
  have hUo : IsOpen unitDisc := isOpen_ball
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hcb : ∀ n, closedBall (0 : ℂ) (r n) ⊆ unitDisc := fun n z hz =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) (hr n).2)
  have hKf : ∀ n, IsClosed (f '' closedBall (0 : ℂ) (r n)) := fun n =>
    ((isCompact_closedBall (0 : ℂ) (r n)).image_of_continuousOn (hfd.continuousOn.mono (hcb n))).isClosed
  have hR : ∀ n, 1 < 1 / r n := fun n => one_lt_one_div (hr n).1 (hr n).2
  have hKg : ∀ n, IsClosed (g '' {z : ℂ | 1 / r n ≤ ‖z‖}) := fun n => mg_image_closed hgu (hR n)
  set S : ℕ → Set ℂ := fun n => (f '' closedBall (0 : ℂ) (r n) ∪ g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n => ((hKf n).union (hKg n)).measurableSet.compl
  have hanti : Antitone S := by
    intro a b hab
    have hrab : r a ≤ r b := hmono hab
    intro w hw hwb
    apply hw
    rcases hwb with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · exact Or.inl ⟨z, closedBall_subset_closedBall hrab hz, rfl⟩
    · refine Or.inr ⟨z, ?_, rfl⟩
      have : 1 / r b ≤ 1 / r a := one_div_le_one_div_of_le (hr a).1 hrab
      exact le_trans this hz
  -- integrability on the first gap
  have hint : IntegrableOn φ (S 0) := by
    obtain ⟨R1, hR1⟩ := mg_far_exterior h' (T := 1 / r 0) (by have := hR 0; positivity)
    set C : Set ℂ := closedBall (0 : ℂ) R1 ∩ (f '' ball (0 : ℂ) (r 0))ᶜ with hC
    have hopen : IsOpen (f '' ball (0 : ℂ) (r 0)) :=
      (RMT.differentiableOn_invFunOn_of_injOn isOpen_ball (hfd.mono (ball_subset_ball (hr 0).2.le))
        (hfi.mono (ball_subset_ball (hr 0).2.le))).1
    have hCc : IsCompact C := (isCompact_closedBall (0 : ℂ) R1).inter_right hopen.isClosed_compl
    have hC0 : C ⊆ {0}ᶜ := by
      intro w hw h0
      exact hw.2 ⟨0, mem_ball_self (hr 0).1, by rw [hf0, mem_singleton_iff.mp h0]⟩
    have hcont : ContinuousOn φ C := hφ.mono hC0
    refine (hcont.integrableOn_compact hCc).mono_set ?_
    intro w hw
    refine ⟨?_, fun hm => hw (Or.inl (image_mono ball_subset_closedBall hm))⟩
    by_contra hnot
    obtain ⟨z, hz, hzw⟩ := hR1 w (not_le.mp (by simpa [mem_closedBall_zero_iff] using hnot))
    exact hw (Or.inr ⟨z, hz, hzw⟩)
  have hT := Antitone.tendsto_setIntegral hSm hanti hint
  have hinter : (⋂ n, S n) ⊆ (f '' unitDisc ∪ g '' unitDiscExterior)ᶜ := by
    intro w hw hwU
    rw [mem_iInter] at hw
    rcases hwU with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hzn)).exists
      exact hw n (Or.inl ⟨z, mem_closedBall_zero_iff.mpr hn.le, rfl⟩)
    · have hzn : 1 < ‖z‖ := hz
      have hlim' : Tendsto (fun n => 1 / r n) atTop (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).div hlim one_ne_zero
        rw [div_one] at this
        exact this.congr (fun n => by simp)
      obtain ⟨n, hn⟩ := (hlim'.eventually (gt_mem_nhds hzn)).exists
      exact hw n (Or.inr ⟨z, hn.le, rfl⟩)
  have h0 : ∫ w in ⋂ n, S n, φ w = 0 :=
    setIntegral_measure_zero _ (measure_mono_null hinter hF)
  rw [h0] at hT
  exact hT



/-! ## The logarithmic Green function `log|w|² / w` -/

/-- `w ↦ log|w|² / w` is `C¹` off `0`. -/
theorem r22_log_contDiff : ContDiffOn ℝ 1 (fun w : ℂ => ((Real.log (‖w‖ ^ 2) : ℝ) : ℂ) / w) {0}ᶜ := by
  have h1 : ContDiffOn ℝ 1 (fun w : ℂ => ((Real.log (‖w‖ ^ 2) : ℝ) : ℂ)) {0}ᶜ := by
    refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
    intro w hw
    have hw0 : w ≠ 0 := hw
    have hn : ‖w‖ ^ 2 ≠ 0 := by positivity
    exact (((contDiff_norm_sq ℝ).contDiffAt).log hn).contDiffWithinAt
  have h2 : ContDiffOn ℝ 1 (fun w : ℂ => w⁻¹) {0}ᶜ :=
    ((differentiableOn_inv.contDiffOn isOpen_compl_singleton).restrict_scalars ℝ)
  simpa only [div_eq_mul_inv] using h1.mul h2

/-- `∂_{w̄} (log|w|² / w) = 1 / |w|²` off `0`. -/
theorem r22_dzbar_log {w : ℂ} (hw : w ≠ 0) :
    dzbar (fun w : ℂ => ((Real.log (‖w‖ ^ 2) : ℝ) : ℂ) / w) w = ((1 / ‖w‖ ^ 2 : ℝ) : ℂ) := by
  have hn : ‖w‖ ^ 2 ≠ 0 := by positivity
  have h1 : HasFDerivAt (fun x : ℂ => ‖x‖ ^ 2) (2 • innerSL ℝ w) w :=
    (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have h2 := h1.log hn
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp w h2
  have hu : DifferentiableAt ℝ (fun x : ℂ => ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) w := h3.differentiableAt
  have hvc : DifferentiableAt ℂ (fun x : ℂ => x⁻¹) w := differentiableAt_inv_iff.mpr hw
  have hv : DifferentiableAt ℝ (fun x : ℂ => x⁻¹) w := hvc.restrictScalars ℝ
  have hvz : dzbar (fun x : ℂ => x⁻¹) w = 0 := (cauchyRiemann_iff.1 hvc).2
  have hd : fderiv ℝ (fun x : ℂ => ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) w =
      Complex.ofRealCLM.comp (((‖w‖ ^ 2)⁻¹) • (2 • innerSL ℝ w)) := h3.fderiv
  have hu1 : dzbar (fun x : ℂ => ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) w = w / ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dzbar, hd]
    simp [innerSL_apply_apply ℝ, Complex.inner]
    have e : ((‖w‖ : ℂ) ^ 2) = ((Complex.normSq w : ℝ) : ℂ) := by
      rw [← Complex.sq_norm]; push_cast; ring
    rw [e]
    apply Complex.ext
    · simp [Complex.div_ofReal_re]
      field_simp
    · simp [Complex.div_ofReal_im]
      field_simp
  have := dzbar_mul hu hv
  simp only [← div_eq_mul_inv] at this
  rw [this, hvz, hu1, mul_zero, zero_add]
  have hwn : ((‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

/-! ## Series for `f` and `g` from the Grunsky coefficients with `0` -/

/-- Restriction of a double series with a factor `0 ^ p.2` to the first axis. -/
theorem r22_prod_zero {X : ℕ → ℕ → ℂ} {S : ℂ}
    (h : HasSum (fun p : ℕ × ℕ => X p.1 p.2 * (0 : ℂ) ^ p.2) S) : HasSum (fun n : ℕ => X n 0) S := by
  have hi : Function.Injective (fun n : ℕ => ((n, 0) : ℕ × ℕ)) := fun a b hab => by simpa using hab
  have h1 := (hi.hasSum_iff (f := fun p : ℕ × ℕ => X p.1 p.2 * (0 : ℂ) ^ p.2) (a := S) (fun p hp => by
    have hp2 : p.2 ≠ 0 := by
      intro h0
      exact hp ⟨p.1, by ext <;> simp [h0]⟩
    simp [hp2])).mpr h
  convert h1 using 1
  funext n
  simp

/-- `f(z) = z exp(φ(z))` on `𝔻`, with `φ(z) = -∑_{n ≥ 1} b_{-n,0} zⁿ`. -/
theorem r22_f_series {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∃ φ : ℂ → ℂ, (∀ z ∈ unitDisc,
        HasSum (fun n : ℕ => (if n = 0 then 0 else -grunsky f g (-(n : ℤ)) 0) * z ^ n) (φ z)) ∧
      ∀ z ∈ unitDisc, f z = z * Complex.exp (φ z) := by
  have hh := h
  obtain ⟨-, -, hf0, -, -, -⟩ := hh
  obtain ⟨-, -, -, hff, -⟩ := (grunsky_spec h).1
  have key : ∀ z ∈ unitDisc, ∃ V, HasSum (fun n : ℕ =>
      (if n = 0 then 0 else -grunsky f g (-(n : ℤ)) 0) * z ^ n) V ∧ (z ≠ 0 → f z = z * Complex.exp V) := by
    intro z hz
    by_cases hz0 : z = 0
    · refine ⟨0, ?_, fun h0 => absurd hz0 h0⟩
      have : (fun n : ℕ => (if n = 0 then 0 else -grunsky f g (-(n : ℤ)) 0) * (0 : ℂ) ^ n) = 0 := by
        funext n
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · simp [hn.ne']
      rw [hz0, this]
      exact hasSum_zero
    · obtain ⟨S, hS, heq⟩ := hff z hz 0 (mem_ball_self one_pos) hz0
      have h1 := r22_prod_zero (X := fun n m => grunsky f g (-(n : ℤ)) (-(m : ℤ)) * z ^ n) hS
      have h2 := (hasSum_ite_eq 0 (grunsky f g 0 0)).sub h1
      refine ⟨grunsky f g 0 0 - S, ?_, fun _ => ?_⟩
      · refine h2.congr_fun (fun n => ?_)
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · simp [hn.ne']
      · rw [hf0, sub_zero, sub_zero] at heq
        field_simp at heq
        exact heq
  refine ⟨fun z => ∑' n : ℕ, (if n = 0 then 0 else -grunsky f g (-(n : ℤ)) 0) * z ^ n, ?_, ?_⟩
  · intro z hz
    obtain ⟨V, hV, -⟩ := key z hz
    exact hV.summable.hasSum
  · intro z hz
    obtain ⟨V, hV, hf⟩ := key z hz
    by_cases hz0 : z = 0
    · rw [hz0, hf0]; simp
    · show f z = z * Complex.exp (∑' n : ℕ, (if n = 0 then 0 else -grunsky f g (-(n : ℤ)) 0) * z ^ n)
      rw [hV.tsum_eq]
      exact hf hz0

/-- `g(1/u) = β u⁻¹ exp(φ̃(u))` on `𝔻 \ {0}`, with `φ̃(u) = -∑_{n ≥ 1} b_{n,0} uⁿ`. -/
theorem r22_g_series {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∃ φ : ℂ → ℂ, (∀ u ∈ unitDisc,
        HasSum (fun n : ℕ => (if n = 0 then 0 else -grunsky f g (n : ℤ) 0) * u ^ n) (φ u)) ∧
      ∀ u ∈ unitDisc, u ≠ 0 → g u⁻¹ = derivAtInfty g * u⁻¹ * Complex.exp (φ u) := by
  have hh := h
  obtain ⟨-, -, hf0, -, -, -⟩ := hh
  obtain ⟨hexp, -, hgf, -, -⟩ := (grunsky_spec h).1
  have hβ : derivAtInfty g ≠ 0 := by rw [← hexp]; exact Complex.exp_ne_zero _
  have key : ∀ u ∈ unitDisc, ∃ V, HasSum (fun n : ℕ =>
      (if n = 0 then 0 else -grunsky f g (n : ℤ) 0) * u ^ n) V ∧
        (u ≠ 0 → g u⁻¹ = derivAtInfty g * u⁻¹ * Complex.exp V) := by
    intro u hu
    by_cases hu0 : u = 0
    · refine ⟨0, ?_, fun h0 => absurd hu0 h0⟩
      have : (fun n : ℕ => (if n = 0 then 0 else -grunsky f g (n : ℤ) 0) * (0 : ℂ) ^ n) = 0 := by
        funext n
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · simp [hn.ne']
      rw [hu0, this]
      exact hasSum_zero
    · have hz : u⁻¹ ∈ unitDiscExterior := by
        have hun : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
        have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        show 1 < ‖u⁻¹‖
        rw [norm_inv]
        exact (one_lt_inv₀ hpos).mpr hun
      obtain ⟨S, hS, heq⟩ := hgf u⁻¹ hz 0 (mem_ball_self one_pos)
      have h1 := r22_prod_zero
        (X := fun n m => grunsky f g ((n : ℤ) + 1) (-(m : ℤ)) * (u⁻¹) ^ (-((n : ℤ) + 1))) hS
      have hp : ∀ n : ℕ, (u⁻¹) ^ (-((n : ℤ) + 1)) = u ^ (n + 1) := by
        intro n
        rw [zpow_neg, inv_zpow, inv_inv]
        exact_mod_cast zpow_natCast u (n + 1)
      refine ⟨-S, ?_, fun _ => ?_⟩
      · refine (hasSum_nat_add_iff' 1).mp ?_
        have e : (-S - ∑ i ∈ Finset.range 1, (if i = 0 then (0 : ℂ) else -grunsky f g (i : ℤ) 0) * u ^ i) = -S := by
          simp
        rw [e]
        convert h1.neg using 1
        funext n
        simp [hp]
        left
        rw [← zpow_natCast]
        push_cast
        rfl
      · rw [hf0, sub_zero] at heq
        have hz0 : u⁻¹ ≠ 0 := inv_ne_zero hu0
        field_simp at heq
        field_simp
        rw [heq]
  refine ⟨fun u => ∑' n : ℕ, (if n = 0 then 0 else -grunsky f g (n : ℤ) 0) * u ^ n, ?_, ?_⟩
  · intro u hu
    obtain ⟨V, hV, -⟩ := key u hu
    exact hV.summable.hasSum
  · intro u hu hu0
    obtain ⟨V, hV, hg⟩ := key u hu
    show g u⁻¹ = derivAtInfty g * u⁻¹ * Complex.exp (∑' n : ℕ, (if n = 0 then 0 else -grunsky f g (n : ℤ) 0) * u ^ n)
    rw [hV.tsum_eq]
    exact hg hu0

/-! ## The circle integrals of the logarithmic Green function -/

/-- Mean value property on a circle inside the disc. -/
theorem r22_mean {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ θ in (0 : ℝ)..2 * π, F (circleMap 0 r θ) = 2 * π * F 0 := by
  have hsub : closedBall (0 : ℂ) r ⊆ unitDisc := fun z hz =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hr1)
  have hD : DiffContOnCl ℂ F (ball (0 : ℂ) r) :=
    ⟨hF.mono (ball_subset_closedBall.trans hsub), by
      rw [closure_ball _ hr0.ne']; exact hF.continuousOn.mono hsub⟩
  have h1 := hD.circleIntegral_sub_inv_smul (c := 0) (w := 0) (mem_ball_self hr0)
  rw [mg_circle_eq] at h1
  have h2 : ∫ θ in (0 : ℝ)..2 * π, ((circleMap 0 r θ - 0)⁻¹ • F (circleMap 0 r θ)) * circleMap 0 r θ =
      ∫ θ in (0 : ℝ)..2 * π, F (circleMap 0 r θ) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr0.ne'
    simp only [sub_zero, smul_eq_mul]
    field_simp
  rw [h2] at h1
  have h3 : I * ∫ θ in (0 : ℝ)..2 * π, F (circleMap 0 r θ) = I * (2 * π * F 0) := by
    rw [h1, smul_eq_mul]; ring
  exact mul_left_cancel₀ Complex.I_ne_zero h3

/-- Energy of a power series on a circle. -/
theorem r22_energy {φ : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => c n * z ^ n) (φ z)) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖c (j + 1)‖ ^ 2 * r ^ (2 * (j + 1)))) ∧
      (∫ θ in (0 : ℝ)..2 * π, conj (φ (circleMap 0 r θ)) * deriv φ (circleMap 0 r θ) * circleMap 0 r θ) =
        2 * π * ((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖c (j + 1)‖ ^ 2 * r ^ (2 * (j + 1))) : ℝ) : ℂ) := by
  obtain ⟨d, hd⟩ : ∃ d : ℤ → ℂ, ∀ m, d m = if 0 ≤ m then c m.toNat else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨r1, hr1d⟩ : ∃ r1 : ℝ, r1 = r / 2 := ⟨_, rfl⟩
  obtain ⟨r2, hr2d⟩ : ∃ r2 : ℝ, r2 = (r + 1) / 2 := ⟨_, rfl⟩
  have hr1p : 0 < r1 := by rw [hr1d]; positivity
  have hr1ρ : r1 < r := by rw [hr1d]; linarith
  have hρr2 : r < r2 := by rw [hr2d]; linarith
  have hr2one : r2 < 1 := by rw [hr2d]; linarith
  have hdpos : ∀ n : ℕ, d (n : ℤ) = c n := fun n => by simp [hd]
  have hdneg : ∀ n : ℕ, d (-((n : ℤ) + 1)) = 0 := fun n => by
    have h1 : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1) := by omega
    rw [hd, if_neg h1]
  have hpos : Summable (fun n : ℕ => ‖d n‖ * r2 ^ n) := by
    have hr2D : ((r2 : ℝ) : ℂ) ∈ unitDisc :=
      mem_ball_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hr2one)
    have hn := summable_norm_iff.mpr (hs _ hr2D).summable
    refine hn.congr (fun j => ?_)
    rw [hdpos, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hneg : Summable (fun n : ℕ => ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹) := by
    refine summable_of_ne_finset_zero (s := Finset.range 1) (fun n hn => ?_)
    have hn' : 1 ≤ n := by rw [Finset.mem_range] at hn; omega
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show (-((k + 1 : ℕ) : ℤ)) = -((k : ℤ) + 1) by push_cast; ring, hdneg, norm_zero, zero_mul]
  have hH : ∀ w : ℂ, r1 < ‖w‖ → ‖w‖ < r2 → φ w = ∑' n : ℤ, d n * w ^ n := by
    intro w hw1 hw2
    have hwD : w ∈ unitDisc := mem_ball_zero_iff.mpr (hw2.trans hr2one)
    have hF : HasSum (fun n : ℕ => c n * w ^ n) (φ w) := hs w hwD
    have hG : HasSum (fun n : ℕ => (fun _ : ℕ => (0 : ℂ)) (n + 1) * w ^ (-((n : ℤ) + 1))) 0 := by
      simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
    have := mg_hasSum_int c (fun _ => 0) hF hG
    have e : (fun m : ℤ => (if 0 ≤ m then c m.toNat else (fun _ : ℕ => (0 : ℂ)) (-m).toNat) * w ^ m) =
        fun m : ℤ => d m * w ^ m := by
      funext m; rw [hd]
    rw [e] at this
    rw [this.tsum_eq, add_zero]
  have hE := mg_circle_energy (H := φ) d hr1p hr1ρ hρr2 hpos hneg hH
  obtain ⟨hgs, hTc⟩ := mg_energy_real hr1p hr1ρ hρr2 hpos hneg
  obtain ⟨hsp, hsn, hsplit⟩ := mg_energy_split hr1p hr1ρ hρr2 hpos hneg
  have e1 : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖d ((j + 1 : ℕ) : ℤ)‖ ^ 2 * r ^ (2 * (j + 1)))) =
      fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖c (j + 1)‖ ^ 2 * r ^ (2 * (j + 1))) := by
    funext j; rw [hdpos]
  have e2 : (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (‖d (-((k + 1 : ℕ) : ℤ))‖ ^ 2 * (r ^ (2 * (k + 1)))⁻¹)) = 0 := by
    have : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * (‖d (-((k + 1 : ℕ) : ℤ))‖ ^ 2 * (r ^ (2 * (k + 1)))⁻¹) = 0 :=
      fun k => by
        rw [show (-((k + 1 : ℕ) : ℤ)) = -((k : ℤ) + 1) by push_cast; ring, hdneg]
        simp
    simp only [this, tsum_zero]
  rw [e1] at hsp
  refine ⟨hsp, ?_⟩
  rw [hE, hTc, hsplit, e1, e2, sub_zero]

/-- The circle integral of `(L + φ + φ̄)(1 + ε z φ')` for a power series `φ` with `φ(0) = 0`. -/
theorem r22_side_core {φ : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => c n * z ^ n) (φ z)) (hc0 : c 0 = 0)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (L ε : ℂ) :
    (∫ θ in (0 : ℝ)..2 * π, (L + φ (circleMap 0 r θ) + conj (φ (circleMap 0 r θ))) *
        (1 + ε * (circleMap 0 r θ * deriv φ (circleMap 0 r θ)))) =
      2 * π * L + ε * (2 * π * ((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖c (j + 1)‖ ^ 2 * r ^ (2 * (j + 1))) : ℝ) : ℂ)) := by
  have hφ := differentiableOn_of_powerSeries hs
  have hφ0 : φ 0 = 0 := by
    have h1 := hs 0 (mem_ball_self one_pos)
    have h2 : HasSum (fun n : ℕ => c n * (0 : ℂ) ^ n) (c 0 * (0 : ℂ) ^ 0) :=
      hasSum_single 0 (fun n hn => by simp [hn])
    rw [h1.unique h2, hc0]; simp
  have hφ' : DifferentiableOn ℂ (deriv φ) unitDisc := hφ.deriv isOpen_ball
  have hcmD : ∀ θ : ℝ, circleMap 0 r θ ∈ unitDisc := fun θ =>
    mem_ball_zero_iff.mpr (by rw [norm_circleMap_zero, abs_of_pos hr0]; exact hr1)
  have hcont : ∀ F : ℂ → ℂ, ContinuousOn F unitDisc → Continuous (fun θ : ℝ => F (circleMap 0 r θ)) :=
    fun F hF => hF.comp_continuous (continuous_circleMap 0 r) hcmD
  have hcφ : Continuous (fun θ : ℝ => φ (circleMap 0 r θ)) := hcont φ hφ.continuousOn
  have hcφ' : Continuous (fun θ : ℝ => deriv φ (circleMap 0 r θ)) := hcont _ hφ'.continuousOn
  have hcc : Continuous (fun θ : ℝ => circleMap 0 r θ) := continuous_circleMap 0 r
  obtain ⟨H1, hH1d⟩ : ∃ H1 : ℂ → ℂ, ∀ u, H1 u = (L + φ u) * (1 + ε * (u * deriv φ u)) := ⟨_, fun _ => rfl⟩
  have hH1 : DifferentiableOn ℂ H1 unitDisc := by
    have : H1 = fun u => (L + φ u) * (1 + ε * (u * deriv φ u)) := funext hH1d
    rw [this]
    exact ((differentiableOn_const L).add hφ).mul
      ((differentiableOn_const 1).add ((differentiableOn_const ε).mul (differentiableOn_id.mul hφ')))
  have hcH1 : Continuous (fun θ : ℝ => H1 (circleMap 0 r θ)) := hcont H1 hH1.continuousOn
  have hcconj : Continuous (fun θ : ℝ => conj (φ (circleMap 0 r θ))) := Complex.continuous_conj.comp hcφ
  have hcen : Continuous (fun θ : ℝ => conj (φ (circleMap 0 r θ)) * deriv φ (circleMap 0 r θ) *
      circleMap 0 r θ) := (hcconj.mul hcφ').mul hcc
  have hsplit : ∀ θ : ℝ, (L + φ (circleMap 0 r θ) + conj (φ (circleMap 0 r θ))) *
        (1 + ε * (circleMap 0 r θ * deriv φ (circleMap 0 r θ))) =
      H1 (circleMap 0 r θ) + conj (φ (circleMap 0 r θ)) +
        ε * (conj (φ (circleMap 0 r θ)) * deriv φ (circleMap 0 r θ) * circleMap 0 r θ) := fun θ => by
    rw [hH1d]; ring
  have i1 : IntervalIntegrable (fun θ : ℝ => H1 (circleMap 0 r θ) + conj (φ (circleMap 0 r θ))) volume
      0 (2 * π) := (hcH1.add hcconj).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ : ℝ => ε * (conj (φ (circleMap 0 r θ)) * deriv φ (circleMap 0 r θ) *
      circleMap 0 r θ)) volume 0 (2 * π) := (hcen.const_mul ε).intervalIntegrable _ _
  have hconjint : (∫ θ in (0 : ℝ)..2 * π, conj (φ (circleMap 0 r θ))) =
      conj (∫ θ in (0 : ℝ)..2 * π, φ (circleMap 0 r θ)) := by
    rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity)]
    exact integral_conj
  simp_rw [hsplit]
  rw [intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_add (hcH1.intervalIntegrable _ _) (hcconj.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, r22_mean hH1 hr0 hr1, hconjint,
    r22_mean hφ hr0 hr1, (r22_energy hs hr0 hr1).2, hH1d, hφ0]
  simp

/-! ## The `f`-side and `g`-side circle integrals -/

/-- Algebraic form of the Green boundary term: `W(F z) F'(z) z = log‖F z‖² · (z F'(z) / F z)`. -/
theorem r22_boundary_alg {F : ℂ → ℂ} {z : ℂ} (hF : F z ≠ 0) :
    ((Real.log (‖F z‖ ^ 2) : ℝ) : ℂ) / F z * deriv F z * z =
      ((Real.log (‖F z‖ ^ 2) : ℝ) : ℂ) * (z * deriv F z / F z) := by
  field_simp

/-- `log‖a e^φ‖² = log‖a‖² + φ + φ̄` for `a ≠ 0`. -/
theorem r22_log_norm {a φ : ℂ} (ha : a ≠ 0) :
    ((Real.log (‖a * Complex.exp φ‖ ^ 2) : ℝ) : ℂ) = ((Real.log (‖a‖ ^ 2) : ℝ) : ℂ) + φ + conj φ := by
  have h1 : ‖a * Complex.exp φ‖ ^ 2 = ‖a‖ ^ 2 * Real.exp (2 * φ.re) := by
    rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul]
    norm_num
  have hn : ‖a‖ ^ 2 ≠ 0 := by positivity
  rw [h1, Real.log_mul hn (Real.exp_pos _).ne', Real.log_exp]
  push_cast
  rw [add_assoc, Complex.add_conj]
  push_cast
  ring

/-- The `f`-side boundary term of the logarithmic Green identity. -/
theorem r22_f_circle {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 * ρ ^ (2 * (j + 1)))) ∧
    (∫ θ in (0 : ℝ)..2 * π, ((Real.log (‖f (circleMap 0 ρ θ)‖ ^ 2) : ℝ) : ℂ) / f (circleMap 0 ρ θ) *
        deriv f (circleMap 0 ρ θ) * circleMap 0 ρ θ) =
      2 * π * ((Real.log (ρ ^ 2) : ℝ) : ℂ) +
        2 * π * ((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 * ρ ^ (2 * (j + 1))) : ℝ) : ℂ) := by
  have hh := h
  obtain ⟨-, -, hf0, -, -, -⟩ := hh
  obtain ⟨φ, hs, hf⟩ := r22_f_series h
  have hc0 : (if (0 : ℕ) = 0 then (0 : ℂ) else -grunsky f g (-((0 : ℕ) : ℤ)) 0) = 0 := by simp
  have hφ := differentiableOn_of_powerSeries hs
  have hcore := r22_side_core hs hc0 hρ0 hρ1 ((Real.log (ρ ^ 2) : ℝ) : ℂ) 1
  have hen := r22_energy hs hρ0 hρ1
  have hnorm : ∀ j : ℕ, ‖(if j + 1 = 0 then (0 : ℂ) else -grunsky f g (-((j + 1 : ℕ) : ℤ)) 0)‖ =
      ‖grunsky f g (-((j : ℤ) + 1)) 0‖ := fun j => by
    rw [if_neg (Nat.succ_ne_zero j), norm_neg]
    push_cast
    rfl
  have hsum : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖(if j + 1 = 0 then (0 : ℂ) else -grunsky f g (-((j + 1 : ℕ) : ℤ)) 0)‖ ^ 2 * ρ ^ (2 * (j + 1)))) =
      fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 * ρ ^ (2 * (j + 1))) := by
    funext j; rw [hnorm]
  rw [hsum] at hen hcore
  refine ⟨hen.1, ?_⟩
  have hpt : ∀ θ : ℝ, ((Real.log (‖f (circleMap 0 ρ θ)‖ ^ 2) : ℝ) : ℂ) / f (circleMap 0 ρ θ) *
        deriv f (circleMap 0 ρ θ) * circleMap 0 ρ θ =
      (((Real.log (ρ ^ 2) : ℝ) : ℂ) + φ (circleMap 0 ρ θ) + conj (φ (circleMap 0 ρ θ))) *
        (1 + 1 * (circleMap 0 ρ θ * deriv φ (circleMap 0 ρ θ))) := by
    intro θ
    have hz : ‖circleMap 0 ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos hρ0]
    have hu : circleMap 0 ρ θ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hz]; exact hρ1)
    have hu0 : circleMap 0 ρ θ ≠ 0 := circleMap_ne_center hρ0.ne'
    set u := circleMap 0 ρ θ with hudef
    have hfu : f u = u * Complex.exp (φ u) := hf u hu
    have hφd : DifferentiableAt ℂ φ u := hφ.differentiableAt (isOpen_ball.mem_nhds hu)
    have hev : f =ᶠ[𝓝 u] fun z => z * Complex.exp (φ z) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hu) (fun z hz => hf z hz)
    have hder : deriv f u = Complex.exp (φ u) * (1 + u * deriv φ u) := by
      have h2 : HasDerivAt (fun z => z * Complex.exp (φ z))
          (1 * Complex.exp (φ u) + u * (Complex.exp (φ u) * deriv φ u)) u :=
        (hasDerivAt_id' u).mul hφd.hasDerivAt.cexp
      rw [hev.deriv_eq, h2.deriv]
      ring
    have hfne : f u ≠ 0 := by rw [hfu]; exact mul_ne_zero hu0 (Complex.exp_ne_zero _)
    rw [r22_boundary_alg hfne, hder, hfu, r22_log_norm hu0, hz]
    have hexp : Complex.exp (φ u) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  simp_rw [hpt]
  rw [hcore]
  ring

/-- Reflection `θ ↦ -θ` of a circle integral. -/
theorem r22_reflect (G : ℂ → ℂ) (s : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, G (circleMap 0 s (-θ)) = ∫ θ in (0 : ℝ)..2 * π, G (circleMap 0 s θ) := by
  rw [intervalIntegral.integral_comp_neg (fun θ => G (circleMap 0 s θ)), neg_zero]
  have hper : Function.Periodic (fun θ : ℝ => G (circleMap 0 s θ)) (2 * π) :=
    (periodic_circleMap 0 s).comp G
  have := hper.intervalIntegral_add_eq (-(2 * π)) 0
  rw [neg_add_cancel, zero_add] at this
  exact this

/-- `(R e^{iθ})⁻¹ = (1/R) e^{-iθ}`. -/
theorem r22_circle_inv {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    (circleMap 0 R θ)⁻¹ = circleMap 0 (1 / R) (-θ) := by
  simp only [circleMap, zero_add, mul_inv, Complex.ofReal_div, Complex.ofReal_one, one_div]
  rw [← Complex.exp_neg]
  congr 2 <;> push_cast <;> ring

/-- The `g`-side boundary term of the logarithmic Green identity. -/
theorem r22_g_circle {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖grunsky f g ((j : ℤ) + 1) 0‖ ^ 2 * ρ ^ (2 * (j + 1)))) ∧
    (∫ θ in (0 : ℝ)..2 * π, ((Real.log (‖g (circleMap 0 (1 / ρ) θ)‖ ^ 2) : ℝ) : ℂ) / g (circleMap 0 (1 / ρ) θ) *
        deriv g (circleMap 0 (1 / ρ) θ) * circleMap 0 (1 / ρ) θ) =
      2 * π * ((Real.log (‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹) : ℝ) : ℂ) -
        2 * π * ((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖grunsky f g ((j : ℤ) + 1) 0‖ ^ 2 * ρ ^ (2 * (j + 1))) : ℝ) : ℂ) := by
  obtain ⟨hexp, -, -, -, -⟩ := (grunsky_spec h).1
  have hβ : derivAtInfty g ≠ 0 := by rw [← hexp]; exact Complex.exp_ne_zero _
  obtain ⟨φ, hs, hg⟩ := r22_g_series h
  have hc0 : (if (0 : ℕ) = 0 then (0 : ℂ) else -grunsky f g ((0 : ℕ) : ℤ) 0) = 0 := by simp
  have hφ := differentiableOn_of_powerSeries hs
  have hcore := r22_side_core hs hc0 hρ0 hρ1 ((Real.log (‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹) : ℝ) : ℂ) (-1)
  have hen := r22_energy hs hρ0 hρ1
  have hnorm : ∀ j : ℕ, ‖(if j + 1 = 0 then (0 : ℂ) else -grunsky f g ((j + 1 : ℕ) : ℤ) 0)‖ =
      ‖grunsky f g ((j : ℤ) + 1) 0‖ := fun j => by
    rw [if_neg (Nat.succ_ne_zero j), norm_neg]
    push_cast
    rfl
  have hsum : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖(if j + 1 = 0 then (0 : ℂ) else -grunsky f g ((j + 1 : ℕ) : ℤ) 0)‖ ^ 2 * ρ ^ (2 * (j + 1)))) =
      fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖grunsky f g ((j : ℤ) + 1) 0‖ ^ 2 * ρ ^ (2 * (j + 1))) := by
    funext j; rw [hnorm]
  rw [hsum] at hen hcore
  refine ⟨hen.1, ?_⟩
  have hR : 0 < 1 / ρ := by positivity
  have hpt : ∀ θ : ℝ, ((Real.log (‖g (circleMap 0 (1 / ρ) θ)‖ ^ 2) : ℝ) : ℂ) / g (circleMap 0 (1 / ρ) θ) *
        deriv g (circleMap 0 (1 / ρ) θ) * circleMap 0 (1 / ρ) θ =
      (fun u : ℂ => (((Real.log (‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹) : ℝ) : ℂ) + φ u + conj (φ u)) *
        (1 + (-1) * (u * deriv φ u))) (circleMap 0 ρ (-θ)) := by
    intro θ
    set z := circleMap 0 (1 / ρ) θ with hzdef
    have hzn : ‖z‖ = 1 / ρ := by rw [norm_circleMap_zero, abs_of_pos hR]
    have hz0 : z ≠ 0 := circleMap_ne_center hR.ne'
    have hzE : z ∈ unitDiscExterior := by
      show 1 < ‖z‖
      rw [hzn]; exact one_lt_one_div hρ0 hρ1
    obtain ⟨u, hu⟩ : ∃ u, u = circleMap 0 ρ (-θ) := ⟨_, rfl⟩
    have huz : z⁻¹ = u := by
      rw [hu, hzdef, r22_circle_inv hR, one_div_one_div]
    have hun : ‖u‖ = ρ := by rw [hu, norm_circleMap_zero, abs_of_pos hρ0]
    have huD : u ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hun]; exact hρ1)
    have hu0 : u ≠ 0 := by rw [hu]; exact circleMap_ne_center hρ0.ne'
    have hzu : z = u⁻¹ := by rw [← huz, inv_inv]
    have hgz : g z = derivAtInfty g * z * Complex.exp (φ u) := by
      have := hg u huD hu0
      rw [← hzu] at this
      rw [this, hzu]
    have hφd : DifferentiableAt ℂ φ u := hφ.differentiableAt (isOpen_ball.mem_nhds huD)
    have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
    have hev : g =ᶠ[𝓝 z] fun w => derivAtInfty g * w * Complex.exp (φ w⁻¹) := by
      refine Filter.eventuallyEq_of_mem (hEo.mem_nhds hzE) (fun w hw => ?_)
      have hwn : 1 < ‖w‖ := hw
      have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hwn; linarith
      have hwD : w⁻¹ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hwn)
      have := hg w⁻¹ hwD (inv_ne_zero hw0)
      rwa [inv_inv] at this
    have hinv : HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz0
    have hcomp : HasDerivAt (fun w : ℂ => φ w⁻¹) (deriv φ u * (-(z ^ 2)⁻¹)) z := by
      have h1 : HasDerivAt φ (deriv φ u) z⁻¹ := by rw [huz]; exact hφd.hasDerivAt
      exact h1.comp z hinv
    have h2 : HasDerivAt (fun w : ℂ => derivAtInfty g * w * Complex.exp (φ w⁻¹))
        (derivAtInfty g * 1 * Complex.exp (φ z⁻¹) +
          derivAtInfty g * z * (Complex.exp (φ z⁻¹) * (deriv φ u * (-(z ^ 2)⁻¹)))) z :=
      (((hasDerivAt_id' z).const_mul (derivAtInfty g)).mul hcomp.cexp)
    have hder : deriv g z = derivAtInfty g * Complex.exp (φ u) * (1 - u * deriv φ u) := by
      rw [hev.deriv_eq, h2.deriv, huz]
      rw [hzu]
      field_simp
      ring
    have hgne : g z ≠ 0 := by rw [hgz]; exact mul_ne_zero (mul_ne_zero hβ hz0) (Complex.exp_ne_zero _)
    rw [r22_boundary_alg hgne, hder, hgz, r22_log_norm (mul_ne_zero hβ hz0), norm_mul, hzn]
    have hexp' : Complex.exp (φ u) ≠ 0 := Complex.exp_ne_zero _
    have : (‖derivAtInfty g‖ * (1 / ρ)) ^ 2 = ‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹ := by
      rw [mul_pow, one_div, inv_pow]
    rw [this, ← hu]
    beta_reduce
    rw [hzu]
    field_simp
    ring
  simp_rw [hpt]
  rw [r22_reflect (fun u : ℂ => (((Real.log (‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹) : ℝ) : ℂ) + φ u + conj (φ u)) *
        (1 + (-1) * (u * deriv φ u))) ρ, hcore]
  ring

/-! ## The gap identity and its limit -/

/-- The logarithmic Green identity on the gap. -/
theorem r22_gap_eq {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ, 1 / ‖w‖ ^ 2) =
      π * Real.log (‖derivAtInfty g‖ ^ 2) - 2 * π * Real.log (ρ ^ 2) -
        π * (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 * ρ ^ (2 * (j + 1)))) -
        π * (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖grunsky f g ((j : ℤ) + 1) 0‖ ^ 2 * ρ ^ (2 * (j + 1)))) := by
  have hh := h
  obtain ⟨-, -, hf0, -, -, -⟩ := hh
  obtain ⟨hexp, -, -, -, -⟩ := (grunsky_spec h).1
  have hβ : ‖derivAtInfty g‖ ^ 2 ≠ 0 := by
    have : derivAtInfty g ≠ 0 := by rw [← hexp]; exact Complex.exp_ne_zero _
    positivity
  have hG := mg_gap_green_gen h hρ0 hρ1 r22_log_contDiff
  beta_reduce at hG
  rw [(r22_f_circle h hρ0 hρ1).2, (r22_g_circle h hρ0 hρ1).2] at hG
  have hgap : ∀ w ∈ (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ, w ≠ 0 := by
    intro w hw hw0
    exact hw (Or.inl ⟨0, by simp [hρ0.le], by rw [hf0, hw0]⟩)
  have hKm : MeasurableSet (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ := by
    have hfd := h.1
    have hgu := h.2.2.2.2.1
    have hR : 1 < 1 / ρ := one_lt_one_div hρ0 hρ1
    exact (((isCompact_closedBall (0 : ℂ) ρ).image_of_continuousOn (hfd.continuousOn.mono (fun z hz =>
      mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hρ1)))).isClosed.union
        (mg_image_closed hgu hR)).measurableSet.compl
  have hint : (∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ, dzbar
      (fun w : ℂ => ((Real.log (‖w‖ ^ 2) : ℝ) : ℂ) / w) w) =
      (((∫ w in (f '' closedBall (0 : ℂ) ρ ∪ g '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ, 1 / ‖w‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun hKm (fun w hw => r22_dzbar_log (hgap w hw))
  rw [hint] at hG
  have hlog : Real.log (‖derivAtInfty g‖ ^ 2 * (ρ ^ 2)⁻¹) = Real.log (‖derivAtInfty g‖ ^ 2) - Real.log (ρ ^ 2) := by
    rw [Real.log_mul hβ (inv_ne_zero (by positivity)), Real.log_inv]; ring
  rw [hlog] at hG
  apply Complex.ofReal_injective
  rw [hG]
  push_cast
  ring

/-- The Grunsky sums with `0` for a null complement: `Σ n |b_{-n,0}|² + Σ n |b_{n,0}|² = log |g'(∞)|²`. -/
theorem r22_sum {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2) ∧
      Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖grunsky f g ((j : ℤ) + 1) 0‖ ^ 2) ∧
      (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2) +
          (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖grunsky f g ((j : ℤ) + 1) 0‖ ^ 2) =
        Real.log (‖derivAtInfty g‖ ^ 2) := by
  obtain ⟨r, hr, hmono, hlim⟩ := mg_radius_seq
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ j, a j = ((j + 1 : ℕ) : ℝ) * ‖grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ j, c j = ((j + 1 : ℕ) : ℝ) * ‖grunsky f g ((j : ℤ) + 1) 0‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Real.log (‖derivAtInfty g‖ ^ 2) := ⟨_, rfl⟩
  have ha0 : ∀ j, 0 ≤ a j := fun j => by rw [ha]; positivity
  have hc0 : ∀ j, 0 ≤ c j := fun j => by rw [hc]; positivity
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ, ∀ n, I n = ∫ w in (f '' closedBall (0 : ℂ) (r n) ∪
      g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ, 1 / ‖w‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hI0 : ∀ n, 0 ≤ I n := fun n => by rw [hI]; exact integral_nonneg (fun w => by positivity)
  have hIlim : Tendsto I atTop (𝓝 0) := by
    have hcont : ContinuousOn (fun w : ℂ => 1 / ‖w‖ ^ 2) {0}ᶜ :=
      continuousOn_const.div (continuous_norm.pow 2).continuousOn (fun w hw => by
        have : w ≠ 0 := hw
        positivity)
    have := mg_gap_integral_tendsto_gen h hF hcont hr hmono hlim
    refine this.congr (fun n => ?_)
    rw [hI]
  have hSf : ∀ n, Summable (fun j : ℕ => a j * (r n) ^ (2 * (j + 1))) := fun n => by
    have := (r22_f_circle h (hr n).1 (hr n).2).1
    refine this.congr (fun j => ?_)
    rw [ha, mul_assoc]
  have hSg : ∀ n, Summable (fun j : ℕ => c j * (r n) ^ (2 * (j + 1))) := fun n => by
    have := (r22_g_circle h (hr n).1 (hr n).2).1
    refine this.congr (fun j => ?_)
    rw [hc, mul_assoc]
  have hEq : ∀ n, (∑' j : ℕ, a j * (r n) ^ (2 * (j + 1))) + (∑' j : ℕ, c j * (r n) ^ (2 * (j + 1))) =
      K - 2 * Real.log ((r n) ^ 2) - I n / π := by
    intro n
    have h1 := r22_gap_eq h (hr n).1 (hr n).2
    rw [← hI n] at h1
    have e1 : (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 * (r n) ^ (2 * (j + 1)))) =
        ∑' j : ℕ, a j * (r n) ^ (2 * (j + 1)) := tsum_congr (fun j => by rw [ha, mul_assoc])
    have e2 : (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖grunsky f g ((j : ℤ) + 1) 0‖ ^ 2 * (r n) ^ (2 * (j + 1)))) =
        ∑' j : ℕ, c j * (r n) ^ (2 * (j + 1)) := tsum_congr (fun j => by rw [hc, mul_assoc])
    rw [e1, e2, ← hK] at h1
    field_simp
    linarith
  have hw : ∀ j : ℕ, Tendsto (fun n => (r n) ^ (2 * (j + 1))) atTop (𝓝 1) := fun j => by
    simpa using hlim.pow (2 * (j + 1))
  have hwle : ∀ n j : ℕ, (r n) ^ (2 * (j + 1)) ≤ 1 := fun n j => pow_le_one₀ (hr n).1.le (hr n).2.le
  have hlog : Tendsto (fun n => Real.log ((r n) ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (r n) ^ 2) atTop (𝓝 1) := by simpa using hlim.pow 2
    have := h1.log (by norm_num)
    simpa using this
  have hV : Tendsto (fun n => K - 2 * Real.log ((r n) ^ 2) - I n / π) atTop (𝓝 K) := by
    have h2 := ((tendsto_const_nhds (x := K)).sub (hlog.const_mul 2)).sub (hIlim.div_const π)
    simpa using h2
  have hV' : Tendsto (fun n => K - 2 * Real.log ((r n) ^ 2)) atTop (𝓝 K) := by
    have h2 := (tendsto_const_nhds (x := K)).sub (hlog.const_mul 2)
    simpa using h2
  -- partial sums are bounded
  have hbound : ∀ N : ℕ, ∑ j ∈ Finset.range N, (a j + c j) ≤ K := by
    intro N
    have h1 : ∀ n, ∑ j ∈ Finset.range N, (a j + c j) * (r n) ^ (2 * (j + 1)) ≤
        K - 2 * Real.log ((r n) ^ 2) := by
      intro n
      have hs := (hSf n).add (hSg n)
      have hw0 : 0 < r n := (hr n).1
      have h2 : ∑ j ∈ Finset.range N, (a j * (r n) ^ (2 * (j + 1)) + c j * (r n) ^ (2 * (j + 1))) ≤
          ∑' j : ℕ, (a j * (r n) ^ (2 * (j + 1)) + c j * (r n) ^ (2 * (j + 1))) :=
        Summable.sum_le_tsum (Finset.range N) (fun j _ => by
          have := ha0 j; have := hc0 j; positivity) hs
      have h3 := (hSf n).tsum_add (hSg n)
      have h4 := hEq n
      have h5 : 0 ≤ I n / π := div_nonneg (hI0 n) hpi.le
      calc ∑ j ∈ Finset.range N, (a j + c j) * (r n) ^ (2 * (j + 1))
          = ∑ j ∈ Finset.range N, (a j * (r n) ^ (2 * (j + 1)) + c j * (r n) ^ (2 * (j + 1))) :=
            Finset.sum_congr rfl (fun j _ => add_mul _ _ _)
        _ ≤ _ := h2
        _ = K - 2 * Real.log ((r n) ^ 2) - I n / π := by rw [h3, h4]
        _ ≤ K - 2 * Real.log ((r n) ^ 2) := by linarith
    have h2 : Tendsto (fun n => ∑ j ∈ Finset.range N, (a j + c j) * (r n) ^ (2 * (j + 1))) atTop
        (𝓝 (∑ j ∈ Finset.range N, (a j + c j))) := by
      have := tendsto_finset_sum (Finset.range N) (fun j _ => (hw j).const_mul (a j + c j))
      simpa using this
    exact le_of_tendsto_of_tendsto h2 hV' (Eventually.of_forall h1)
  have hsum : Summable (fun j => a j + c j) :=
    summable_of_sum_range_le (fun j => add_nonneg (ha0 j) (hc0 j)) hbound
  have hle : ∑' j, (a j + c j) ≤ K := Real.tsum_le_of_sum_range_le (fun j => add_nonneg (ha0 j) (hc0 j)) hbound
  have hsa : Summable a := Summable.of_nonneg_of_le ha0 (fun j => le_add_of_nonneg_right (hc0 j)) hsum
  have hsc : Summable c := Summable.of_nonneg_of_le hc0 (fun j => le_add_of_nonneg_left (ha0 j)) hsum
  have hge : K ≤ ∑' j, (a j + c j) := by
    have h1 : ∀ n, K - 2 * Real.log ((r n) ^ 2) - I n / π ≤ ∑' j, (a j + c j) := by
      intro n
      rw [← hEq n, ← (hSf n).tsum_add (hSg n)]
      refine Summable.tsum_le_tsum (fun j => add_le_add ?_ ?_) ((hSf n).add (hSg n)) hsum
      · exact mul_le_of_le_one_right (ha0 j) (hwle n j)
      · exact mul_le_of_le_one_right (hc0 j) (hwle n j)
    exact le_of_tendsto' hV h1
  have hA : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2) = a :=
    funext (fun j => (ha j).symm)
  have hC : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖grunsky f g ((j : ℤ) + 1) 0‖ ^ 2) = c :=
    funext (fun j => (hc j).symm)
  rw [hA, hC, ← hK, ← hsa.tsum_add hsc]
  exact ⟨hsa, hsc, le_antisymm hle hge⟩

/-! ## The area integrals -/

/-- Area Parseval for the derivative of a power series. -/
theorem r22_area_series {φ : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => c n * z ^ n) (φ z))
    (hsum : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖c (j + 1)‖ ^ 2)) :
    (∫ z in unitDisc, ‖deriv φ z‖ ^ 2) = π * ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖c (j + 1)‖ ^ 2 := by
  have hs' : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => (c (n + 1) * ((n + 1 : ℕ) : ℂ)) * z ^ n) (deriv φ z) :=
    fun z hz => faber_powerSeries_deriv hs hz
  have hterm : ∀ n : ℕ, π * ‖c (n + 1) * ((n + 1 : ℕ) : ℂ)‖ ^ 2 / ((n : ℝ) + 1) =
      π * (((n + 1 : ℕ) : ℝ) * ‖c (n + 1)‖ ^ 2) := by
    intro n
    rw [norm_mul, mul_pow, Complex.norm_natCast]
    push_cast
    field_simp
  have hsumm : Summable (fun n : ℕ => π * ‖c (n + 1) * ((n + 1 : ℕ) : ℂ)‖ ^ 2 / ((n : ℝ) + 1)) := by
    simp_rw [hterm]; exact hsum.mul_left π
  have hmem := bergman_mem_A21_of_coeff hs' hsumm
  have hpar := A21_area_parseval hmem hs'
  have : (fun n : ℕ => π * ‖c (n + 1) * ((n + 1 : ℕ) : ℂ)‖ ^ 2 / ((n : ℝ) + 1)) =
      fun n => π * (((n + 1 : ℕ) : ℝ) * ‖c (n + 1)‖ ^ 2) := funext hterm
  rw [this] at hpar
  rw [← hpar.tsum_eq, tsum_mul_left]

/-- `∫_𝔻 |f'/f - 1/z|² = π Σ n |b_{-n,0}|²`. -/
theorem r22_f_area {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hsum : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2)) :
    (∫ z in unitDisc, ‖deriv f z / f z - 1 / z‖ ^ 2) =
      π * ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 := by
  obtain ⟨φ, hs, hf⟩ := r22_f_series h
  have hφ := differentiableOn_of_powerSeries hs
  have hnorm : ∀ j : ℕ, ‖(if j + 1 = 0 then (0 : ℂ) else -grunsky f g (-((j + 1 : ℕ) : ℤ)) 0)‖ =
      ‖grunsky f g (-((j : ℤ) + 1)) 0‖ := fun j => by
    rw [if_neg (Nat.succ_ne_zero j), norm_neg]
    push_cast
    rfl
  have hsum' : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
      ‖(if j + 1 = 0 then (0 : ℂ) else -grunsky f g (-((j + 1 : ℕ) : ℤ)) 0)‖ ^ 2) := by
    simp_rw [hnorm]; exact hsum
  have harea := r22_area_series hs hsum'
  simp_rw [hnorm] at harea
  rw [← harea]
  refine setIntegral_congr_ae measurableSet_ball ?_
  filter_upwards [(Set.countable_singleton (0 : ℂ)).ae_notMem volume] with z hz0 hz
  have hz0' : z ≠ 0 := hz0
  have hφd : DifferentiableAt ℂ φ z := hφ.differentiableAt (isOpen_ball.mem_nhds hz)
  have hfz : f z = z * Complex.exp (φ z) := hf z hz
  have hev : f =ᶠ[𝓝 z] fun w => w * Complex.exp (φ w) :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) (fun w hw => hf w hw)
  have h2 : HasDerivAt (fun w => w * Complex.exp (φ w))
      (1 * Complex.exp (φ z) + z * (Complex.exp (φ z) * deriv φ z)) z :=
    (hasDerivAt_id' z).mul hφd.hasDerivAt.cexp
  have hder : deriv f z = Complex.exp (φ z) * (1 + z * deriv φ z) := by
    rw [hev.deriv_eq, h2.deriv]; ring
  have hexp : Complex.exp (φ z) ≠ 0 := Complex.exp_ne_zero _
  have : deriv f z / f z - 1 / z = deriv φ z := by
    rw [hder, hfz]
    field_simp
    ring
  rw [this]

/-- The derivative of `g` on `𝔻*` in terms of the series variable `u = 1/z`. -/
theorem r22_g_deriv {g φ : ℂ → ℂ} {β : ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hg : ∀ u ∈ unitDisc, u ≠ 0 → g u⁻¹ = β * u⁻¹ * Complex.exp (φ u)) {u : ℂ} (hu : u ∈ unitDisc)
    (hu0 : u ≠ 0) : deriv g u⁻¹ = β * Complex.exp (φ u) * (1 - u * deriv φ u) := by
  have hz0 : u⁻¹ ≠ 0 := inv_ne_zero hu0
  have hun : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hzE : u⁻¹ ∈ unitDiscExterior := by
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    show 1 < ‖u⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ hpos).mpr hun
  have hφd : DifferentiableAt ℂ φ u := hφ.differentiableAt (isOpen_ball.mem_nhds hu)
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hev : g =ᶠ[𝓝 u⁻¹] fun w => β * w * Complex.exp (φ w⁻¹) := by
    refine Filter.eventuallyEq_of_mem (hEo.mem_nhds hzE) (fun w hw => ?_)
    have hwn : 1 < ‖w‖ := hw
    have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hwn; linarith
    have hwD : w⁻¹ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hwn)
    have := hg w⁻¹ hwD (inv_ne_zero hw0)
    rwa [inv_inv] at this
  have hinv : HasDerivAt (fun w : ℂ => w⁻¹) (-((u⁻¹) ^ 2)⁻¹) u⁻¹ := hasDerivAt_inv hz0
  have hcomp : HasDerivAt (fun w : ℂ => φ w⁻¹) (deriv φ u * (-((u⁻¹) ^ 2)⁻¹)) u⁻¹ := by
    have h1 : HasDerivAt φ (deriv φ u) (u⁻¹)⁻¹ := by rw [inv_inv]; exact hφd.hasDerivAt
    exact h1.comp u⁻¹ hinv
  have h2 : HasDerivAt (fun w : ℂ => β * w * Complex.exp (φ w⁻¹))
      (β * 1 * Complex.exp (φ (u⁻¹)⁻¹) +
        β * u⁻¹ * (Complex.exp (φ (u⁻¹)⁻¹) * (deriv φ u * (-((u⁻¹) ^ 2)⁻¹)))) u⁻¹ :=
    (((hasDerivAt_id' u⁻¹).const_mul β).mul hcomp.cexp)
  rw [hev.deriv_eq, h2.deriv, inv_inv]
  field_simp
  ring

/-- `∫_{𝔻*} |g'/g - 1/z|² = π Σ n |b_{n,0}|²`. -/
theorem r22_g_area {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hsum : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖grunsky f g ((j : ℤ) + 1) 0‖ ^ 2)) :
    (∫ z in unitDiscExterior, ‖deriv g z / g z - 1 / z‖ ^ 2) =
      π * ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖grunsky f g ((j : ℤ) + 1) 0‖ ^ 2 := by
  obtain ⟨hexp, -, -, -, -⟩ := (grunsky_spec h).1
  have hβ : derivAtInfty g ≠ 0 := by rw [← hexp]; exact Complex.exp_ne_zero _
  obtain ⟨φ, hs, hg⟩ := r22_g_series h
  have hφ := differentiableOn_of_powerSeries hs
  have hnorm : ∀ j : ℕ, ‖(if j + 1 = 0 then (0 : ℂ) else -grunsky f g ((j + 1 : ℕ) : ℤ) 0)‖ =
      ‖grunsky f g ((j : ℤ) + 1) 0‖ := fun j => by
    rw [if_neg (Nat.succ_ne_zero j), norm_neg]
    push_cast
    rfl
  have hsum' : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) *
      ‖(if j + 1 = 0 then (0 : ℂ) else -grunsky f g ((j + 1 : ℕ) : ℤ) 0)‖ ^ 2) := by
    simp_rw [hnorm]; exact hsum
  have harea := r22_area_series hs hsum'
  simp_rw [hnorm] at harea
  rw [← harea]
  have hDm : MeasurableSet (unitDisc \ {0}) := measurableSet_ball.diff (measurableSet_singleton 0)
  have himg : (fun u : ℂ => u⁻¹) '' (unitDisc \ {0}) = unitDiscExterior := by
    ext z
    constructor
    · rintro ⟨u, ⟨hu, hu0⟩, rfl⟩
      have hu0' : u ≠ 0 := hu0
      have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0'
      show 1 < ‖u⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ hpos).mpr (mem_ball_zero_iff.mp hu)
    · intro hz
      have hz1 : 1 < ‖z‖ := hz
      have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hz1; linarith
      exact ⟨z⁻¹, ⟨mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1),
        inv_ne_zero hz0⟩, inv_inv z⟩
  have hdiff : ∀ u ∈ unitDisc \ {0}, DifferentiableAt ℂ (fun w : ℂ => w⁻¹) u :=
    fun u hu => differentiableAt_inv_iff.mpr hu.2
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume hDm
    (f := fun u : ℂ => u⁻¹) (f' := fun u => fderiv ℝ (fun w : ℂ => w⁻¹) u)
    (fun u hu => ((hdiff u hu).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt)
    (fun a _ b _ hab => by simpa using hab)
    (fun z => ‖deriv g z / g z - 1 / z‖ ^ 2)
  rw [← himg, hcov]
  have hae : (unitDisc \ {0} : Set ℂ) =ᵐ[volume] unitDisc :=
    diff_null_ae_eq_self (measure_singleton 0)
  rw [setIntegral_congr_set hae.symm]
  refine setIntegral_congr_fun hDm (fun u hu => ?_)
  obtain ⟨hu, hu0⟩ := hu
  have hu0' : u ≠ 0 := hu0
  have hgu := hg u hu hu0'
  have hder := r22_g_deriv hφ hg hu hu0'
  have hexp' : Complex.exp (φ u) ≠ 0 := Complex.exp_ne_zero _
  have hC : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) u := hdiff u ⟨hu, hu0⟩
  have hdet : (fderiv ℝ (fun w : ℂ => w⁻¹) u).det = ‖deriv (fun w : ℂ => w⁻¹) u‖ ^ 2 := by
    have h1 := det_fderiv_eq_jacobian (hC.restrictScalars ℝ)
    rw [jacobian, (cauchyRiemann_iff.1 hC).2, dz_eq_deriv hC, norm_zero] at h1
    rw [ContinuousLinearMap.det, h1]
    ring
  have hval : deriv g u⁻¹ / g u⁻¹ - 1 / u⁻¹ = -(u ^ 2 * deriv φ u) := by
    rw [hder, hgu]
    field_simp
    ring
  simp only [smul_eq_mul]
  rw [hdet, deriv_inv, hval, abs_of_nonneg (by positivity)]
  simp only [norm_neg, norm_mul, norm_pow, norm_inv]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0'
  field_simp

/-- **Remark 2.2** for the welding pair of a point of `T(1)`: the quasicircle is a null set and the
generalized Grunsky equality with `λ₀ = 1` holds (copy of `Ch2.remark_2_2`). -/
theorem mg_remark_2_2 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsNormalizedDisjointPair (fsans μ) (gsans μ) ∧
      volume ((fsans μ '' unitDisc ∪ gsans μ '' unitDiscExterior)ᶜ) = 0 ∧
      2 * (grunsky (fsans μ) (gsans μ) 0 0).re =
        ∑' k : ℤ, |(k : ℝ)| * ‖grunsky (fsans μ) (gsans μ) k 0‖ ^ 2 ∧
      2 * π * Real.log ‖derivAtInfty (gsans μ)‖ =
        (∫ z in unitDisc, ‖deriv (fsans μ) z / fsans μ z - 1 / z‖ ^ 2) +
          ∫ z in unitDiscExterior, ‖deriv (gsans μ) z / gsans μ z - 1 / z‖ ^ 2 := by
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hnull := r22_complement_null hμ
  obtain ⟨hs1, hs2, hsum⟩ := r22_sum hpair hnull
  obtain ⟨hexp, -, -, -, -⟩ := (grunsky_spec hpair).1
  have hlog : Real.log (‖derivAtInfty (gsans μ)‖ ^ 2) = 2 * (grunsky (fsans μ) (gsans μ) 0 0).re := by
    have : ‖derivAtInfty (gsans μ)‖ = Real.exp (grunsky (fsans μ) (gsans μ) 0 0).re := by
      rw [← hexp, Complex.norm_exp]
    rw [Real.log_pow, this, Real.log_exp]
    norm_num
  refine ⟨hpair, hnull, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F : ℤ → ℝ, ∀ k, F k = |(k : ℝ)| * ‖grunsky (fsans μ) (gsans μ) k 0‖ ^ 2 :=
      ⟨_, fun _ => rfl⟩
    have hF0 : F 0 = 0 := by simp [hF]
    have hFpos : ∀ j : ℕ, F ((j + 1 : ℕ) : ℤ) =
        ((j + 1 : ℕ) : ℝ) * ‖grunsky (fsans μ) (gsans μ) ((j : ℤ) + 1) 0‖ ^ 2 := fun j => by
      rw [hF]
      push_cast
      rw [abs_of_nonneg (by positivity)]
    have hFneg : ∀ j : ℕ, F (-((j : ℤ) + 1)) =
        ((j + 1 : ℕ) : ℝ) * ‖grunsky (fsans μ) (gsans μ) (-((j : ℤ) + 1)) 0‖ ^ 2 := fun j => by
      rw [hF]
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    have hpos' : Summable (fun j : ℕ => F ((j + 1 : ℕ) : ℤ)) := by
      simp_rw [hFpos]; exact hs2
    have hneg' : Summable (fun j : ℕ => F (-((j : ℤ) + 1))) := by
      simp_rw [hFneg]; exact hs1
    have hsumF : Summable F :=
      Summable.of_nat_of_neg_add_one ((summable_nat_add_iff 1).mp hpos') hneg'
    have := mg_tsum_int_split hsumF hF0
    simp_rw [← hF]
    rw [this]
    simp_rw [hFpos, hFneg]
    linarith
  · rw [r22_f_area hpair hs1, r22_g_area hpair hs2, ← mul_add, hsum, Real.log_pow]
    push_cast
    ring

/-! ### Original relocated (2026-10-26) -/

/-- **Remark 2.2** (TT:3836–3852). For the welding pair of a point of `𝒯(1)` (here of `[μ] ∈ T(1)`), the quasicircle is
a null set, so the generalized Grunsky equality holds. Taking `λ₀ = 1`, `λ_k = 0` (`k ≠ 0`):
- `2 Re b₀₀ = Σ_k |k| |b_{k0}|²`;
- `2π log |g'(∞)| = ∬_𝔻 |f'/f - 1/z|² d²z + ∬_{𝔻*} |g'/g - 1/z|² d²z`. -/
theorem remark_2_2 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsNormalizedDisjointPair (fsans μ) (gsans μ) ∧
      volume ((fsans μ '' unitDisc ∪ gsans μ '' unitDiscExterior)ᶜ) = 0 ∧
      2 * (grunsky (fsans μ) (gsans μ) 0 0).re =
        ∑' k : ℤ, |(k : ℝ)| * ‖grunsky (fsans μ) (gsans μ) k 0‖ ^ 2 ∧
      2 * π * Real.log ‖derivAtInfty (gsans μ)‖ =
        (∫ z in unitDisc, ‖deriv (fsans μ) z / fsans μ z - 1 / z‖ ^ 2) +
          ∫ z in unitDiscExterior, ‖deriv (gsans μ) z / gsans μ z - 1 / z‖ ^ 2 :=
  mg_remark_2_2 hμ

end Ch2

end TakhtajanTeo
