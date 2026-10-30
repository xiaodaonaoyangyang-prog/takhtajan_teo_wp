import TakhtajanTeo.Ch2.S3GDom
import TakhtajanTeo.Ch2.S3DD0
import TakhtajanTeo.Ch2.S35WNorm
import TakhtajanTeo.Ch1.S5WeldingNormalization
import TakhtajanTeo.Ch1.S5PlaneJets
import TakhtajanTeo.Ch1.S5ConformalFamilyContinuity
import TakhtajanTeo.Ch1.S2Core
import TakhtajanTeo.Appendix.AppACont
import TakhtajanTeo.Ch1.Eq124General
import TakhtajanTeo.Ch1.QuasidiskKernel
import TakhtajanTeo.Ch1.BeltramiCompose
import TakhtajanTeo.Ch1.BeltramiGroup
import TakhtajanTeo.Appendix.BergmanPeriodModel

/-! # Density route: shared base (Program G)

`d2e_` kernel/Koebe helpers, (G-DOM) `s3d_l2sq_dom`, `s3x_dom_data`, the (V) chain `s3d5_`/`s3dv_`/`s3d2u_` and `s3d_pair_variation`. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- `‖Dn u‖⁻¹ ≤ 4 (‖u - 1‖⁻¹ + ‖u + 1‖⁻¹ + ‖u + i‖⁻¹)` away from the nodes. -/
theorem d2e_dn_pt {u : ℂ} (h1 : u ≠ 1) (h2 : u ≠ -1) (h3 : u ≠ -I) :
    ‖(u + 1) * (u + I) * (u - 1)‖⁻¹ ≤ 4 * (‖u - 1‖⁻¹ + ‖u - -1‖⁻¹ + ‖u - -I‖⁻¹) := by
  have ha : 0 < ‖u - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 h1)
  have hb : 0 < ‖u - -1‖ := norm_pos_iff.2 (sub_ne_zero.2 h2)
  have hc : 0 < ‖u - -I‖ := norm_pos_iff.2 (sub_ne_zero.2 h3)
  have hab : 2 ≤ ‖u - 1‖ + ‖u - -1‖ := by
    have h := norm_sub_le (u - -1) (u - 1)
    have e : (u - -1) - (u - 1) = 2 := by ring
    rw [e] at h
    have h2' : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  have hac : 1 ≤ ‖u - 1‖ + ‖u - -I‖ := by
    have h := norm_sub_le (u - -I) (u - 1)
    have e : (u - -I) - (u - 1) = 1 + I := by ring
    rw [e] at h
    have h1' : (1 : ℝ) ≤ ‖1 + I‖ := by
      have := Complex.abs_re_le_norm (1 + I)
      simp only [add_re, one_re, I_re, add_zero, abs_one] at this
      exact this
    linarith
  have hbc : 1 ≤ ‖u - -1‖ + ‖u - -I‖ := by
    have h := norm_sub_le (u - -1) (u - -I)
    have e : (u - -1) - (u - -I) = 1 - I := by ring
    rw [e] at h
    have h1' : (1 : ℝ) ≤ ‖1 - I‖ := by
      have := Complex.abs_re_le_norm (1 - I)
      simp only [sub_re, one_re, I_re, sub_zero, abs_one] at this
      exact this
    linarith
  set a := ‖u - 1‖ with hA
  set b := ‖u - -1‖ with hB
  set c := ‖u - -I‖ with hC
  have key : 1 ≤ 4 * (b * c + a * c + a * b) := by
    rcases le_or_gt c (1 / 2) with hc2 | hc2
    · nlinarith [mul_le_mul hac hbc zero_le_one (by linarith)]
    · nlinarith [mul_le_mul_of_nonneg_left hab hc.le]
  have hn : ‖(u + 1) * (u + I) * (u - 1)‖ = b * c * a := by
    rw [norm_mul, norm_mul, hA, hB, hC, sub_neg_eq_add, sub_neg_eq_add]
  have e4 : 4 * (a⁻¹ + b⁻¹ + c⁻¹) = 4 * (b * c + a * c + a * b) / (b * c * a) := by
    field_simp
  rw [hn, e4, le_div_iff₀ (by positivity), inv_mul_cancel₀ (by positivity)]
  exact key

/-- `‖Dn u‖⁻¹ ≤ 8 (1 + ‖u‖)⁻³` for `‖u‖ ≥ 3`. -/
theorem d2e_dn_far {u : ℂ} (hu : 3 ≤ ‖u‖) :
    ‖(u + 1) * (u + I) * (u - 1)‖⁻¹ ≤ 8 * (1 + ‖u‖) ^ (-3 : ℝ) := by
  have h1 : (1 + ‖u‖) / 2 ≤ ‖u + 1‖ := by
    have := norm_sub_norm_le u (-1)
    rw [norm_neg, norm_one, sub_neg_eq_add] at this
    linarith
  have h2 : (1 + ‖u‖) / 2 ≤ ‖u + I‖ := by
    have := norm_sub_norm_le u (-I)
    rw [norm_neg, Complex.norm_I, sub_neg_eq_add] at this
    linarith
  have h3 : (1 + ‖u‖) / 2 ≤ ‖u - 1‖ := by
    have := norm_sub_norm_le u 1
    rw [norm_one] at this
    linarith
  have hp : 0 < (1 + ‖u‖) / 2 := by positivity
  have hprod : ((1 + ‖u‖) / 2) ^ 3 ≤ ‖(u + 1) * (u + I) * (u - 1)‖ := by
    rw [norm_mul, norm_mul, pow_succ, pow_succ, pow_one]
    exact mul_le_mul (mul_le_mul h1 h2 hp.le (norm_nonneg _)) h3 hp.le (by positivity)
  have hr : (1 + ‖u‖) ^ (-3 : ℝ) = ((1 + ‖u‖) ^ 3)⁻¹ := by
    rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [hr]
  calc ‖(u + 1) * (u + I) * (u - 1)‖⁻¹ ≤ (((1 + ‖u‖) / 2) ^ 3)⁻¹ :=
        inv_anti₀ (by positivity) hprod
    _ = 8 * ((1 + ‖u‖) ^ 3)⁻¹ := by field_simp; ring

/-- `‖Dn‖⁻¹` is integrable on `ℂ`. -/
theorem d2e_dn_int : Integrable (fun u : ℂ => ‖(u + 1) * (u + I) * (u - 1)‖⁻¹) := by
  have hloc : ∀ p : ℂ, ‖p‖ = 1 → IntegrableOn (fun u : ℂ => ‖u - p‖⁻¹) (ball 0 4) := by
    intro p hp
    refine (e124p_invnorm_int p 5).mono_set (ball_subset_ball' ?_)
    rw [dist_comm, dist_eq_norm, sub_zero, hp]
    norm_num
  have hI1 : IntegrableOn (fun u : ℂ => 4 * (‖u - 1‖⁻¹ + ‖u - -1‖⁻¹ + ‖u - -I‖⁻¹)) (ball 0 4) :=
    (((hloc 1 (by simp)).add (hloc (-1) (by simp))).add (hloc (-I) (by simp))).const_mul 4
  have hmaj : Integrable (fun u : ℂ => (ball (0 : ℂ) 4).indicator
      (fun u : ℂ => 4 * (‖u - 1‖⁻¹ + ‖u - -1‖⁻¹ + ‖u - -I‖⁻¹)) u + 8 * (1 + ‖u‖) ^ (-3 : ℝ)) :=
    ((integrable_indicator_iff measurableSet_ball).2 hI1).add
      ((integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3)
        (by rw [Complex.finrank_real_complex]; norm_num)).const_mul 8)
  refine hmaj.mono' ?_ ?_
  · exact (Continuous.measurable (by fun_prop : Continuous fun u : ℂ => (u + 1) * (u + I) * (u - 1))).norm.inv
      |>.aestronglyMeasurable
  · have hS : ({1, -1, -I} : Set ℂ).Countable := (Set.toFinite _).countable
    filter_upwards [hS.ae_notMem volume] with u hu
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hu
    obtain ⟨hu1, hu2, hu3⟩ := hu
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
    have h0 : 0 ≤ 8 * (1 + ‖u‖) ^ (-3 : ℝ) := by positivity
    by_cases h4 : ‖u‖ < 4
    · rw [indicator_of_mem (mem_ball_zero_iff.2 h4)]
      linarith [d2e_dn_pt hu1 hu2 hu3]
    · have hi0 : 0 ≤ (ball (0 : ℂ) 4).indicator
          (fun u : ℂ => 4 * (‖u - 1‖⁻¹ + ‖u - -1‖⁻¹ + ‖u - -I‖⁻¹)) u :=
        indicator_nonneg (fun _ _ => by positivity) _
      linarith [d2e_dn_far (show (3 : ℝ) ≤ ‖u‖ by rw [not_lt] at h4; linarith)]

/-- Koebe: `‖g u‖ ≥ 1/4` on `𝔻*` for a normalized disjoint pair. -/
theorem d2e_koebe {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {u : ℂ} (hu : u ∈ unitDiscExterior) :
    1 / 4 ≤ ‖g u‖ := by
  obtain ⟨hfd, hfi, hf0, hf1, -, hdisj⟩ := h
  have hb := r24_koebe_point hfd hfi (mem_ball_self one_pos : (0 : ℂ) ∈ unitDisc)
  rw [hf0, hf1] at hb
  by_contra hlt
  rw [not_le] at hlt
  have hm : g u ∈ f '' unitDisc := hb (mem_ball_zero_iff.2 (by simpa using hlt))
  exact hdisj.ne_of_mem hm ⟨u, hu, rfl⟩ rfl

/-- Growth of `g` and `g'` at `∞` (from the inverted interior map). -/
theorem d2e_growth {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∃ c > 0, ∃ C : ℝ, ∀ u : ℂ, 4 ≤ ‖u‖ → c * ‖u‖ ≤ ‖g u‖ ∧ ‖deriv g u‖ ≤ C := by
  have hgd : DifferentiableOn ℂ g unitDiscExterior := h.2.2.2.2.1.1
  obtain ⟨φ, b, hφd, hφi, hφ0, hφ1, hb, -, hgφ⟩ := g1_inverted_exterior h
  set ψ : ℂ → ℂ := dslope φ 0 with hψ
  have hψd : DifferentiableOn ℂ ψ unitDisc :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self one_pos))).2 hφd
  have hK : IsCompact (closedBall (0 : ℂ) (1 / 2)) := isCompact_closedBall _ _
  have hKsub : closedBall (0 : ℂ) (1 / 2) ⊆ unitDisc := closedBall_subset_ball (by norm_num)
  have hψc : ContinuousOn ψ (closedBall 0 (1 / 2)) := hψd.continuousOn.mono hKsub
  have hψs : ∀ s : ℂ, s ≠ 0 → ψ s = φ s / s := by
    intro s hs
    rw [hψ, dslope_of_ne _ hs, slope_def_field, hφ0, sub_zero, sub_zero]
  have hψ0 : ∀ s ∈ closedBall (0 : ℂ) (1 / 2), ψ s ≠ 0 := by
    intro s hs
    by_cases hs0 : s = 0
    · rw [hs0, hψ, dslope_same, hφ1]
      exact one_ne_zero
    · rw [hψs s hs0]
      refine div_ne_zero (fun hφs => hs0 ?_) hs0
      exact hφi (hKsub hs) (mem_ball_self one_pos) (hφs.trans hφ0.symm)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hψc
  obtain ⟨s₀, hs₀, hmin⟩ := hK.exists_isMinOn ⟨0, mem_closedBall_self (by norm_num)⟩ hψc.norm
  set m := ‖ψ s₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (hψ0 s₀ hs₀)
  have hM0 : 0 < M := lt_of_lt_of_le hm0 (hM s₀ hs₀)
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  -- `‖g w‖` two-sided for `‖w‖ ≥ 2`
  have hgw : ∀ w : ℂ, 2 ≤ ‖w‖ → ‖b‖ / M * ‖w‖ ≤ ‖g w‖ ∧ ‖g w‖ ≤ ‖b‖ / m * ‖w‖ := by
    intro w hw
    have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hw; linarith
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    set s := w⁻¹ with hs
    have hs0 : s ≠ 0 := inv_ne_zero hw0
    have hsn : ‖s‖ ≤ 1 / 2 := by
      rw [hs, norm_inv]
      exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
    have hsK : s ∈ closedBall (0 : ℂ) (1 / 2) := mem_closedBall_zero_iff.2 hsn
    have hsD : s ∈ unitDisc := hKsub hsK
    have hge : g w = b / φ s := by
      have := hgφ s hsD hs0
      rwa [one_div, hs, inv_inv] at this
    have hφs : φ s = s * ψ s := by rw [hψs s hs0]; field_simp
    have hψs0 := hψ0 s hsK
    have hψn : 0 < ‖ψ s‖ := norm_pos_iff.2 hψs0
    have hval : ‖g w‖ = ‖b‖ * ‖w‖ / ‖ψ s‖ := by
      rw [hge, hφs, norm_div, norm_mul, hs, norm_inv]
      field_simp
    have hle : ‖ψ s‖ ≤ M := hM s hsK
    have hge' : m ≤ ‖ψ s‖ := hmin hsK
    rw [hval]
    constructor
    · rw [div_mul_eq_mul_div, div_le_div_iff₀ hM0 hψn]
      nlinarith [mul_le_mul_of_nonneg_left hle (mul_nonneg hbn.le hwn.le)]
    · rw [div_mul_eq_mul_div, div_le_div_iff₀ hψn hm0]
      nlinarith [mul_le_mul_of_nonneg_left hge' (mul_nonneg hbn.le hwn.le)]
  refine ⟨‖b‖ / M, div_pos hbn hM0, 3 * (‖b‖ / m), fun u hu => ⟨(hgw u (by linarith)).1, ?_⟩⟩
  -- Cauchy estimate on `ball u (‖u‖/2)`
  have hun : 0 < ‖u‖ := by linarith
  have hr : 0 < ‖u‖ / 2 := by positivity
  have hsub : closedBall u (‖u‖ / 2) ⊆ {w : ℂ | 2 ≤ ‖w‖} := by
    intro w hw
    have h1 := norm_sub_norm_le u w
    have h2 : ‖u - w‖ ≤ ‖u‖ / 2 := by rw [norm_sub_rev]; exact mem_closedBall_iff_norm.1 hw
    show 2 ≤ ‖w‖
    linarith
  have hsubE : {w : ℂ | 2 ≤ ‖w‖} ⊆ unitDiscExterior := fun w hw => by
    show 1 < ‖w‖
    exact lt_of_lt_of_le (by norm_num) hw
  have hdc : DiffContOnCl ℂ g (ball u (‖u‖ / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball u hr.ne']
    exact hgd.mono (hsub.trans hsubE)
  have hbd := norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc (C := ‖b‖ / m * (3 / 2 * ‖u‖)) (by
    intro w hw
    have hwB : w ∈ closedBall u (‖u‖ / 2) := sphere_subset_closedBall hw
    have h2 := (hgw w (hsub hwB)).2
    have h3 : ‖w‖ ≤ 3 / 2 * ‖u‖ := by
      have := norm_le_norm_add_norm_sub' w u
      have h4 : ‖w - u‖ = ‖u‖ / 2 := mem_sphere_iff_norm.1 hw
      linarith [norm_le_of_mem_closedBall hwB, norm_sub_norm_le w u]
    calc ‖g w‖ ≤ ‖b‖ / m * ‖w‖ := h2
      _ ≤ ‖b‖ / m * (3 / 2 * ‖u‖) := mul_le_mul_of_nonneg_left h3 (by positivity))
  calc ‖deriv g u‖ ≤ ‖b‖ / m * (3 / 2 * ‖u‖) / (‖u‖ / 2) := hbd
    _ = 3 * (‖b‖ / m) := by field_simp

/-- `Dn u ≠ 0` off the closed disc. -/
theorem d2e_dn_ne {u : ℂ} (hu : 1 < ‖u‖) : (u + 1) * (u + I) * (u - 1) ≠ 0 := by
  have h1 : u + 1 ≠ 0 := fun h => by
    have e : u = -1 := by linear_combination h
    rw [e] at hu; simp at hu
  have h2 : u + I ≠ 0 := fun h => by
    have e : u = -I := by linear_combination h
    rw [e] at hu; simp at hu
  have h3 : u - 1 ≠ 0 := fun h => by
    have e : u = 1 := by linear_combination h
    rw [e] at hu; simp at hu
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

/-- Transfer from the extension `G` (on `{ρ < ‖z‖}`) to `g` on `𝔻*`. -/
theorem d2e_basic {g G : ℂ → ℂ} {ρ : ℝ} (hρ : ρ < 1) (hG : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖})
    (hGi : InjOn G {z : ℂ | ρ < ‖z‖}) (hGd : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0)
    (hGg : EqOn G g unitDiscExterior) :
    DifferentiableOn ℂ g unitDiscExterior ∧ DifferentiableOn ℂ (deriv g) unitDiscExterior ∧
      InjOn g unitDiscExterior ∧ (∀ u ∈ unitDiscExterior, deriv g u = deriv G u) ∧
      ∀ u ∈ unitDiscExterior, deriv g u ≠ 0 := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hsub : unitDiscExterior ⊆ {z : ℂ | ρ < ‖z‖} := fun z hz => lt_trans hρ hz
  have hgd : DifferentiableOn ℂ g unitDiscExterior :=
    (hG.mono hsub).congr (fun z hz => (hGg hz).symm)
  have hdd : ∀ u ∈ unitDiscExterior, deriv g u = deriv G u := fun u hu =>
    ((hGg.eventuallyEq_of_mem (hE.mem_nhds hu)).deriv_eq).symm
  refine ⟨hgd, hgd.deriv hE, fun x hx y hy h => hGi (hsub hx) (hsub hy) (by rw [hGg hx, hGg hy]; exact h),
    hdd, fun u hu => ?_⟩
  rw [hdd u hu]
  exact hGd u (hsub hu)

/-- The removable-singularity kernel `K̃(u, ·) = -dslope Φ_u u` is holomorphic on `𝔻*`. -/
theorem d2e_K_diff {g : ℂ → ℂ} (hgd : DifferentiableOn ℂ g unitDiscExterior)
    (hg'd : DifferentiableOn ℂ (deriv g) unitDiscExterior) (hgi : InjOn g unitDiscExterior)
    (hg' : ∀ u ∈ unitDiscExterior, deriv g u ≠ 0) (hg0 : ∀ u ∈ unitDiscExterior, g u ≠ 0)
    {u : ℂ} (hu : u ∈ unitDiscExterior) :
    DifferentiableOn ℂ (fun y => -dslope (fun w => deriv g u ^ 2 * g w ^ 2 /
      (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y)
      unitDiscExterior := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hD : DifferentiableOn ℂ (dslope g u) unitDiscExterior :=
    (differentiableOn_dslope (hE.mem_nhds hu)).2 hgd
  have hD0 : ∀ w ∈ unitDiscExterior, dslope g u w ≠ 0 := by
    intro w hw
    by_cases hwu : w = u
    · rw [hwu, dslope_same]; exact hg' u hu
    · rw [dslope_of_ne _ hwu, slope_def_field]
      exact div_ne_zero (sub_ne_zero.2 (fun h => hwu (hgi hw hu h))) (sub_ne_zero.2 hwu)
  have hΦ : DifferentiableOn ℂ (fun w => deriv g u ^ 2 * g w ^ 2 /
      (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1)))
      unitDiscExterior := by
    apply DifferentiableOn.sub
    · apply DifferentiableOn.div
      · exact (differentiableOn_const _).mul (hgd.pow 2)
      · exact ((differentiableOn_const _).mul hg'd).mul hD
      · intro w hw
        exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (hg0 u hu)) (hg' w hw)) (hD0 w hw)
    · exact (by fun_prop : Differentiable ℂ fun w : ℂ =>
        (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))).differentiableOn
  exact ((differentiableOn_dslope (hE.mem_nhds hu)).2 hΦ).neg

/-- Off the diagonal, `K̃(u, w)` is the explicit kernel `M(u, w)/g'(w) - N(u, w)`. -/
theorem d2e_K_eq {g : ℂ → ℂ} {u w : ℂ} (hwu : w ≠ u) (hgu : g u ≠ 0) (hg'u : deriv g u ≠ 0)
    (hg'w : deriv g w ≠ 0) (hgw : g u ≠ g w) (hDn : (u + 1) * (u + I) * (u - 1) ≠ 0) :
    -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) -
        (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u w =
      deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * (g u - g w)) -
        (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1) * (u - w)) := by
  have h1 : w - u ≠ 0 := sub_ne_zero.2 hwu
  have h2 : u - w ≠ 0 := sub_ne_zero.2 (Ne.symm hwu)
  have h3 : g w - g u ≠ 0 := sub_ne_zero.2 (Ne.symm hgw)
  have h4 : g u - g w ≠ 0 := sub_ne_zero.2 hgw
  simp only [dslope_of_ne _ hwu, dslope_same, slope_def_field]
  generalize (w + 1) * (w + I) * (w - 1) = E
  generalize (u + 1) * (u + I) * (u - 1) = D at hDn ⊢
  field_simp
  ring

/-- The integrable majorant of the off-diagonal kernel, uniform for `w` in a compact `K ⊆ 𝔻*` and
`‖u - w‖ ≥ η`. -/
theorem d2e_bound {g G : ℂ → ℂ} {ρ : ℝ} (hρ : ρ < 1) (hG : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖})
    (hGi : InjOn G {z : ℂ | ρ < ‖z‖}) (hGd : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0)
    (hGg : EqOn G g unitDiscExterior) (hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖g u‖)
    (hinf : ∃ c > 0, ∃ C : ℝ, ∀ u : ℂ, 4 ≤ ‖u‖ → c * ‖u‖ ≤ ‖g u‖ ∧ ‖deriv g u‖ ≤ C)
    {K : Set ℂ} (hK : IsCompact K) (hKE : K ⊆ unitDiscExterior) {η : ℝ} (hη : 0 < η) :
    ∃ B : ℂ → ℝ, Integrable B ∧ (∀ u, 0 ≤ B u) ∧ ∀ u ∈ unitDiscExterior, ∀ w ∈ K, η ≤ ‖u - w‖ →
      ‖deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * (g u - g w)) -
        (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1) * (u - w))‖ ≤ B u := by
  obtain ⟨hgd, hg'd, hgi, hdd, hg'⟩ := d2e_basic hρ hG hGi hGd hGg
  by_cases hKne : K.Nonempty
  swap
  · refine ⟨fun _ => 0, integrable_zero _ _ _, fun _ => le_rfl, fun u _ w hw => ?_⟩
    exact absurd ⟨w, hw⟩ hKne
  have hU : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨A1, hA1⟩ := hK.exists_bound_of_continuousOn (hgd.continuousOn.mono hKE)
  obtain ⟨w₁, hw₁, hmin1⟩ := hK.exists_isMinOn hKne (hg'd.continuousOn.mono hKE).norm
  set a1 := ‖deriv g w₁‖ with ha1
  have ha1p : 0 < a1 := norm_pos_iff.2 (hg' w₁ (hKE hw₁))
  obtain ⟨A2, hA2⟩ := hK.exists_bound_of_continuousOn
    ((by fun_prop : Continuous fun w : ℂ => (w + 1) * (w + I) * (w - 1)).continuousOn)
  obtain ⟨w₀, hw₀⟩ := hKne
  have hA1n : 0 ≤ A1 := (norm_nonneg _).trans (hA1 w₀ hw₀)
  have hA2n : 0 ≤ A2 := (norm_nonneg _).trans (hA2 w₀ hw₀)
  obtain ⟨c, hc, C, hcC⟩ := hinf
  set R1 : ℝ := max 4 (2 * A1 / c) with hR1
  have hR14 : 4 ≤ R1 := le_max_left _ _
  have hAnn : IsCompact (closedBall (0 : ℂ) R1 ∩ {u : ℂ | 1 ≤ ‖u‖}) :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hAnnU : closedBall (0 : ℂ) R1 ∩ {u : ℂ | 1 ≤ ‖u‖} ⊆ {z : ℂ | ρ < ‖z‖} := fun u hu =>
    lt_of_lt_of_le hρ hu.2
  obtain ⟨B1, hB1⟩ := hAnn.exists_bound_of_continuousOn ((hG.deriv hU).continuousOn.mono hAnnU)
  have hKU : K ⊆ {z : ℂ | ρ < ‖z‖} := fun w hw => lt_trans hρ (hKE hw)
  set S : Set (ℂ × ℂ) := ((closedBall (0 : ℂ) R1 ∩ {u : ℂ | 1 ≤ ‖u‖}) ×ˢ K) ∩ {p | η ≤ ‖p.1 - p.2‖} with hS
  have hSc : IsCompact S :=
    (hAnn.prod hK).inter_right (isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm)
  have hGc : ContinuousOn G {z : ℂ | ρ < ‖z‖} := hG.continuousOn
  have hSf : ContinuousOn (fun p : ℂ × ℂ => ‖G p.1 - G p.2‖) S := by
    refine ((hGc.comp continuousOn_fst ?_).sub (hGc.comp continuousOn_snd ?_)).norm
    · intro p hp; exact hAnnU hp.1.1
    · intro p hp; exact hKU hp.1.2
  obtain ⟨δ, hδ, hδS⟩ : ∃ δ > 0, ∀ p ∈ S, δ ≤ ‖G p.1 - G p.2‖ := by
    by_cases hSne : S.Nonempty
    · obtain ⟨p₀, hp₀, hmin⟩ := hSc.exists_isMinOn hSne hSf
      refine ⟨‖G p₀.1 - G p₀.2‖, norm_pos_iff.2 (sub_ne_zero.2 fun h => ?_), fun p hp => hmin hp⟩
      have he := hGi (hAnnU hp₀.1.1) (hKU hp₀.1.2) h
      have := hp₀.2
      simp only [mem_ofPred_eq, he, sub_self, norm_zero] at this
      linarith
    · exact ⟨1, one_pos, fun p hp => absurd ⟨p, hp⟩ hSne⟩
  refine ⟨fun u => A1 ^ 2 / a1 * (16 * B1 ^ 2 / δ * (closedBall (0 : ℂ) R1).indicator (fun _ => (1 : ℝ)) u +
      16 * C ^ 2 / c ^ 3 * (1 + ‖u‖) ^ (-3 : ℝ)) + A2 / η * ‖(u + 1) * (u + I) * (u - 1)‖⁻¹, ?_, ?_, ?_⟩
  · refine ((((integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne (by simp))).const_mul _).add
      ((integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3)
        (by rw [Complex.finrank_real_complex]; norm_num)).const_mul _)).const_mul _ |>.add
      (d2e_dn_int.const_mul _)
  · intro u
    have : 0 ≤ (closedBall (0 : ℂ) R1).indicator (fun _ => (1 : ℝ)) u :=
      indicator_nonneg (fun _ _ => zero_le_one) _
    positivity
  intro u hu w hw huw
  have hwE := hKE hw
  have hu1 : 1 < ‖u‖ := hu
  have hne : u ≠ w := fun h => by rw [h, sub_self, norm_zero] at huw; linarith
  have hgw : g u ≠ g w := fun h => hne (hgi hu hwE h)
  have hgu0 : 0 < ‖g u‖ := lt_of_lt_of_le (by norm_num) (hk u hu)
  have hguw : 0 < ‖g u - g w‖ := norm_pos_iff.2 (sub_ne_zero.2 hgw)
  have hDu : 0 < ‖(u + 1) * (u + I) * (u - 1)‖ := norm_pos_iff.2 (d2e_dn_ne hu1)
  have huw0 : 0 < ‖u - w‖ := lt_of_lt_of_le hη huw
  have hY : ‖(w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1) * (u - w))‖ ≤
      A2 / η * ‖(u + 1) * (u + I) * (u - 1)‖⁻¹ := by
    rw [norm_div, norm_mul ((u + 1) * (u + I) * (u - 1)) (u - w), div_le_iff₀ (mul_pos hDu huw0)]
    have := hA2 w hw
    calc ‖(w + 1) * (w + I) * (w - 1)‖ ≤ A2 := this
      _ = A2 / η * ‖(u + 1) * (u + I) * (u - 1)‖⁻¹ * (‖(u + 1) * (u + I) * (u - 1)‖ * η) := by
        field_simp
      _ ≤ A2 / η * ‖(u + 1) * (u + I) * (u - 1)‖⁻¹ * (‖(u + 1) * (u + I) * (u - 1)‖ * ‖u - w‖) := by
        gcongr
  set Bm : ℝ := ‖deriv g u‖ ^ 2 / (‖g u‖ ^ 2 * ‖g u - g w‖) with hBm
  have hX : ‖deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * (g u - g w))‖ ≤ A1 ^ 2 / a1 * Bm := by
    have hgw' : ‖g w‖ ≤ A1 := hA1 w hw
    have ha1w : a1 ≤ ‖deriv g w‖ := hmin1 hw
    have hdw0 : 0 < ‖deriv g w‖ := lt_of_lt_of_le ha1p ha1w
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, hBm]
    have e : ‖deriv g u‖ ^ 2 * ‖g w‖ ^ 2 / (‖g u‖ ^ 2 * ‖deriv g w‖ * ‖g u - g w‖) =
        ‖g w‖ ^ 2 / ‖deriv g w‖ * (‖deriv g u‖ ^ 2 / (‖g u‖ ^ 2 * ‖g u - g w‖)) := by
      field_simp
    rw [e]
    have hq : ‖g w‖ ^ 2 / ‖deriv g w‖ ≤ A1 ^ 2 / a1 :=
      div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) hgw' 2) ha1p ha1w
    exact mul_le_mul_of_nonneg_right hq (by positivity)
  have hBm0 : 0 ≤ Bm := by positivity
  have hBmB : Bm ≤ 16 * B1 ^ 2 / δ * (closedBall (0 : ℂ) R1).indicator (fun _ => (1 : ℝ)) u +
      16 * C ^ 2 / c ^ 3 * (1 + ‖u‖) ^ (-3 : ℝ) := by
    by_cases hR : ‖u‖ ≤ R1
    · have huA : u ∈ closedBall (0 : ℂ) R1 ∩ {u : ℂ | 1 ≤ ‖u‖} :=
        ⟨mem_closedBall_zero_iff.2 hR, show 1 ≤ ‖u‖ from hu1.le⟩
      rw [indicator_of_mem huA.1, mul_one]
      have hd' : ‖deriv g u‖ ≤ B1 := by rw [hdd u hu]; exact hB1 u huA
      have hδ' : δ ≤ ‖g u - g w‖ := by
        have := hδS (u, w) ⟨⟨huA, hw⟩, huw⟩
        rwa [hGg hu, hGg hwE] at this
      have h3 : 0 ≤ 16 * C ^ 2 / c ^ 3 * (1 + ‖u‖) ^ (-3 : ℝ) := by positivity
      have h4 : Bm ≤ 16 * B1 ^ 2 / δ := by
        rw [hBm, div_le_div_iff₀ (by positivity) hδ]
        have hg2 : (1 / 16 : ℝ) ≤ ‖g u‖ ^ 2 := by nlinarith [hk u hu]
        have hd2 : ‖deriv g u‖ ^ 2 ≤ B1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd' 2
        nlinarith [mul_le_mul hg2 hδ' hδ.le (by positivity)]
      linarith
    · rw [not_le] at hR
      have hu4 : 4 ≤ ‖u‖ := hR14.trans hR.le
      obtain ⟨hcu, hCu⟩ := hcC u hu4
      have hun : 0 < ‖u‖ := by linarith
      have h2A : 2 * A1 ≤ c * ‖u‖ := by
        have : 2 * A1 / c ≤ ‖u‖ := (le_max_right _ _).trans hR.le
        rw [div_le_iff₀ hc] at this
        linarith
      have hsep : c * ‖u‖ / 2 ≤ ‖g u - g w‖ := by
        have := norm_sub_norm_le (g u) (g w)
        linarith [hA1 w hw]
      have h3 : 0 ≤ 16 * B1 ^ 2 / δ * (closedBall (0 : ℂ) R1).indicator (fun _ => (1 : ℝ)) u := by
        have : 0 ≤ (closedBall (0 : ℂ) R1).indicator (fun _ => (1 : ℝ)) u :=
          indicator_nonneg (fun _ _ => zero_le_one) _
        positivity
      have h5 : Bm ≤ C ^ 2 / ((c * ‖u‖) ^ 2 * (c * ‖u‖ / 2)) := by
        rw [hBm]
        apply div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) hCu 2) (by positivity)
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) hcu 2) hsep (by positivity) (by positivity)
      have hr : (1 + ‖u‖) ^ (-3 : ℝ) = ((1 + ‖u‖) ^ 3)⁻¹ := by
        rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
      have h6 : C ^ 2 / ((c * ‖u‖) ^ 2 * (c * ‖u‖ / 2)) ≤ 16 * C ^ 2 / c ^ 3 * (1 + ‖u‖) ^ (-3 : ℝ) := by
        rw [hr]
        have e1 : C ^ 2 / ((c * ‖u‖) ^ 2 * (c * ‖u‖ / 2)) = 2 * C ^ 2 / c ^ 3 * (‖u‖ ^ 3)⁻¹ := by
          field_simp
        rw [e1]
        have h7 : (‖u‖ ^ 3)⁻¹ ≤ 8 * ((1 + ‖u‖) ^ 3)⁻¹ := by
          have hp : (1 + ‖u‖) ^ 3 ≤ (2 * ‖u‖) ^ 3 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 3
          rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        calc 2 * C ^ 2 / c ^ 3 * (‖u‖ ^ 3)⁻¹ ≤ 2 * C ^ 2 / c ^ 3 * (8 * ((1 + ‖u‖) ^ 3)⁻¹) :=
              mul_le_mul_of_nonneg_left h7 (by positivity)
          _ = 16 * C ^ 2 / c ^ 3 * ((1 + ‖u‖) ^ 3)⁻¹ := by ring
      linarith
  calc _ ≤ ‖deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * (g u - g w))‖ +
        ‖(w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1) * (u - w))‖ := norm_sub_le _ _
    _ ≤ A1 ^ 2 / a1 * Bm + A2 / η * ‖(u + 1) * (u + I) * (u - 1)‖⁻¹ := add_le_add hX hY
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hBmB (div_nonneg (sq_nonneg _) ha1p.le)) le_rfl

/-- **Core of (E1).** For bounded measurable `R`, `y ↦ ∫_{𝔻*} R(u) K̃(u, y)` is integrable and complex-differentiable at
every `z₀ ∈ 𝔻*` (dominated differentiation; max modulus near the diagonal, Cauchy estimates). -/
theorem d2e_core {g G R : ℂ → ℂ} {ρ Rb : ℝ} (hρ : ρ < 1) (hG : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖})
    (hGi : InjOn G {z : ℂ | ρ < ‖z‖}) (hGd : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0)
    (hGg : EqOn G g unitDiscExterior) (hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖g u‖)
    (hinf : ∃ c > 0, ∃ C : ℝ, ∀ u : ℂ, 4 ≤ ‖u‖ → c * ‖u‖ ≤ ‖g u‖ ∧ ‖deriv g u‖ ≤ C)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb) {z0 : ℂ} (hz0 : z0 ∈ unitDiscExterior) :
    IntegrableOn (fun u => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z0) unitDiscExterior ∧
      DifferentiableAt ℂ (fun y => ∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) z0 := by
  obtain ⟨hgd, hg'd, hgi, hdd, hg'⟩ := d2e_basic hρ hG hGi hGd hGg
  have hg0 : ∀ u ∈ unitDiscExterior, g u ≠ 0 := fun u hu h => by
    have := hk u hu
    rw [h, norm_zero] at this
    norm_num at this
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have hz01 : 1 < ‖z0‖ := hz0
  set ε : ℝ := (‖z0‖ - 1) / 8 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hsubE : ∀ w : ℂ, ‖w - z0‖ ≤ 7 * ε → w ∈ unitDiscExterior := by
    intro w hw
    have h1 := norm_sub_norm_le z0 w
    rw [norm_sub_rev] at h1
    show 1 < ‖w‖
    rw [hε] at hw
    linarith
  have hKc : closedBall z0 (6 * ε) ⊆ unitDiscExterior := fun w hw =>
    hsubE w (by have := mem_closedBall_iff_norm.1 hw; linarith)
  obtain ⟨B, hBi, hB0, hBk⟩ := d2e_bound hρ hG hGi hGd hGg hk hinf (isCompact_closedBall z0 (6 * ε)) hKc
    (by positivity : (0 : ℝ) < 2 * ε)
  have hKeq : ∀ u ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, w ≠ u → -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u w = deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * (g u - g w)) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1) * (u - w)) :=
    fun u hu w hw hwu => d2e_K_eq hwu (hg0 u hu) (hg' u hu) (hg' w hw) (fun h => hwu (hgi hu hw h).symm)
      (d2e_dn_ne hu)
  have hKd : ∀ u ∈ unitDiscExterior, DifferentiableOn ℂ (fun y => -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) unitDiscExterior :=
    fun u hu => d2e_K_diff hgd hg'd hgi hg' hg0 hu
  have htri : ∀ a b c : ℂ, ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := fun a b c => by
    have := norm_add_le (a - b) (b - c)
    rwa [show a - b + (b - c) = a - c by ring] at this
  -- (KB2) the kernel bound on `closedBall z₀ (2ε)`
  have hKB2 : ∀ u ∈ unitDiscExterior, ∀ y ∈ closedBall z0 (2 * ε), ‖-dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y‖ ≤ B u := by
    intro u hu y hy
    have hy' : ‖y - z0‖ ≤ 2 * ε := mem_closedBall_iff_norm.1 hy
    by_cases hun : ‖u - z0‖ < 4 * ε
    · have hdc : DiffContOnCl ℂ (fun y => -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) (ball z0 (6 * ε)) := by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball _ (by positivity)]
        exact (hKd u hu).mono hKc
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_ ?_
      · intro w hw
        rw [frontier_ball _ (by positivity)] at hw
        have hw' : ‖w - z0‖ = 6 * ε := mem_sphere_iff_norm.1 hw
        have hwK : w ∈ closedBall z0 (6 * ε) := sphere_subset_closedBall hw
        have hsep : 2 * ε ≤ ‖u - w‖ := by
          have := htri w u z0
          rw [norm_sub_rev w u] at this
          linarith
        have hwu : w ≠ u := fun h => by rw [h, sub_self, norm_zero] at hsep; linarith
        rw [hKeq u hu w (hKc hwK) hwu]
        exact hBk u hu w hwK hsep
      · rw [closure_ball _ (by positivity)]
        exact mem_closedBall_iff_norm.2 (by linarith)
    · rw [not_lt] at hun
      have hsep : 2 * ε ≤ ‖u - y‖ := by
        have := htri u y z0
        linarith
      have hyK : y ∈ closedBall z0 (6 * ε) := mem_closedBall_iff_norm.2 (by linarith)
      have hyu : y ≠ u := fun h => by rw [h, sub_self, norm_zero] at hsep; linarith
      rw [hKeq u hu y (hKc hyK) hyu]
      exact hBk u hu y hyK hsep
  -- (KB3) the derivative bound on `ball z₀ ε`
  have hKB3 : ∀ u ∈ unitDiscExterior, ∀ y ∈ ball z0 ε, ‖deriv (fun y => -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) y‖ ≤ B u / ε := by
    intro u hu y hy
    have hyz : ‖y - z0‖ < ε := mem_ball_iff_norm.1 hy
    have hcb : closedBall y ε ⊆ closedBall z0 (2 * ε) := fun w hw => by
      have := mem_closedBall_iff_norm.1 hw
      exact mem_closedBall_iff_norm.2 (by linarith [htri w y z0])
    have hdc : DiffContOnCl ℂ (fun y => -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) (ball y ε) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ hε0.ne']
      exact (hKd u hu).mono (fun w hw => hKc (mem_closedBall_iff_norm.2 (by
        have := mem_closedBall_iff_norm.1 (hcb hw); linarith)))
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε0 hdc
      (fun w hw => hKB2 u hu w (hcb (sphere_subset_closedBall hw)))
  -- measurability in `u`
  have hmeasK : ∀ y ∈ unitDiscExterior, AEStronglyMeasurable (fun u => -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y)
      (volume.restrict unitDiscExterior) := by
    intro y hy
    have hcont : ContinuousOn (fun u => deriv g u ^ 2 * g y ^ 2 / (g u ^ 2 * deriv g y * (g u - g y)) - (y + 1) * (y + I) * (y - 1) / ((u + 1) * (u + I) * (u - 1) * (u - y))) (unitDiscExterior \ {y}) := by
      have hgc := hgd.continuousOn.mono (diff_subset (s := unitDiscExterior) (t := {y}))
      have hg'c := hg'd.continuousOn.mono (diff_subset (s := unitDiscExterior) (t := {y}))
      apply ContinuousOn.sub
      · apply ContinuousOn.div ((hg'c.pow 2).mul continuousOn_const)
          (((hgc.pow 2).mul continuousOn_const).mul (hgc.sub continuousOn_const))
        intro u hu
        exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (hg0 u hu.1)) (hg' y hy))
          (sub_ne_zero.2 (fun h => hu.2 (hgi hu.1 hy h)))
      · apply ContinuousOn.div continuousOn_const
          ((by fun_prop : Continuous fun u : ℂ => (u + 1) * (u + I) * (u - 1) * (u - y)).continuousOn)
        intro u hu
        exact mul_ne_zero (d2e_dn_ne hu.1) (sub_ne_zero.2 hu.2)
    have h1 := hcont.aestronglyMeasurable (μ := volume) (hEm.diff (measurableSet_singleton y))
    rw [Measure.restrict_congr_set (sdiff_null_ae_eq_self (μ := volume) (s := unitDiscExterior)
      (measure_singleton y))] at h1
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae ((countable_singleton y).ae_notMem volume)]
      with u hu huy
    exact (hKeq u hu y hy (fun h => huy (h ▸ rfl))).symm
  -- derivative measurability at `z₀` (limit of difference quotients)
  have hdm : AEStronglyMeasurable (fun u => deriv (fun y => -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) z0) (volume.restrict unitDiscExterior) := by
    set s : ℕ → ℂ := fun n => z0 + ((ε / ((n : ℝ) + 2) : ℝ) : ℂ) with hs
    have hsp : ∀ n : ℕ, 0 < ε / ((n : ℝ) + 2) := fun n => div_pos hε0 (by positivity)
    have hsE : ∀ n, s n ∈ unitDiscExterior := by
      intro n
      apply hsubE
      rw [hs]
      simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hsp n)]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hε0, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsne : ∀ n, s n ≠ z0 := by
      intro n h
      rw [hs] at h
      have : ((ε / ((n : ℝ) + 2) : ℝ) : ℂ) = 0 := by linear_combination h
      exact (hsp n).ne' (by exact_mod_cast this)
    have hr : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have hsc : Tendsto s atTop (𝓝 z0) := by
      have := ((Complex.continuous_ofReal.tendsto 0).comp hr).const_add z0
      simpa [hs, Function.comp_def] using this
    have hsn : Tendsto s atTop (𝓝[≠] z0) :=
      tendsto_nhdsWithin_iff.2 ⟨hsc, Eventually.of_forall fun n => hsne n⟩
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n u => (s n - z0)⁻¹ * (-dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u (s n) - -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z0)) (fun n => ?_) ?_
    · exact ((hmeasK _ (hsE n)).sub (hmeasK z0 hz0)).const_mul _
    · filter_upwards [ae_restrict_mem hEm] with u hu
      have hda := ((hKd u hu).differentiableAt (hE.mem_nhds hz0)).hasDerivAt
      have ht := (hasDerivAt_iff_tendsto_slope.1 hda).comp hsn
      refine ht.congr fun n => ?_
      simp only [Function.comp_apply, slope_def_field, div_eq_inv_mul]
  have hF_int : Integrable (fun u => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z0) (volume.restrict unitDiscExterior) := by
    refine (hBi.integrableOn.const_mul Rb).mono' (hRm.mul (hmeasK z0 hz0)) ?_
    filter_upwards [hRb, ae_restrict_mem hEm] with u hRu hu
    rw [norm_mul]
    exact mul_le_mul hRu (hKB2 u hu z0 (mem_closedBall_self (by positivity))) (norm_nonneg _)
      ((norm_nonneg _).trans hRu)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict unitDiscExterior)
    (F := fun y u => R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) (F' := fun y u => R u * deriv (fun y => -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) y) (x₀ := z0)
    (bound := fun u => Rb * (B u / ε)) (ball_mem_nhds z0 hε0)
    (by filter_upwards [hE.mem_nhds hz0] with y hy using hRm.mul (hmeasK y hy)) hF_int (hRm.mul hdm)
    (by
      filter_upwards [hRb, ae_restrict_mem hEm] with u hRu hu y hy
      rw [norm_mul]
      exact mul_le_mul hRu (hKB3 u hu y hy) (norm_nonneg _) ((norm_nonneg _).trans hRu))
    ((hBi.div_const ε).const_mul Rb).integrableOn
    (by
      filter_upwards [ae_restrict_mem hEm] with u hu y hy
      have hyE : y ∈ unitDiscExterior := hsubE y (by have := mem_ball_iff_norm.1 hy; linarith)
      exact (((hKd u hu).differentiableAt (hE.mem_nhds hyE)).hasDerivAt).const_mul (R u))
  exact ⟨hF_int, key.2.differentiableAt⟩

/-- `‖Dn ζ‖ ≥ δ³` once `‖ζ‖ ≥ 1 + δ`. -/
theorem d2e_dn_lower {ζ : ℂ} {δ : ℝ} (hδ : 0 ≤ δ) (h : 1 + δ ≤ ‖ζ‖) :
    δ ^ 3 ≤ ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ := by
  have h1 : δ ≤ ‖ζ + 1‖ := by
    have := norm_sub_norm_le ζ (-1)
    rw [norm_neg, norm_one, sub_neg_eq_add] at this
    linarith
  have h2 : δ ≤ ‖ζ + I‖ := by
    have := norm_sub_norm_le ζ (-I)
    rw [norm_neg, Complex.norm_I, sub_neg_eq_add] at this
    linarith
  have h3 : δ ≤ ‖ζ - 1‖ := by
    have := norm_sub_norm_le ζ 1
    rw [norm_one] at this
    linarith
  rw [norm_mul, norm_mul, pow_succ, pow_succ, pow_one]
  exact mul_le_mul (mul_le_mul h1 h2 hδ (norm_nonneg _)) h3 hδ (by positivity)

/-- `Dn u ≠ 0` inside the open disc. -/
theorem d2e_dn_ne1 {u : ℂ} (hu : ‖u‖ < 1) : (u + 1) * (u + I) * (u - 1) ≠ 0 := by
  have h1 : u + 1 ≠ 0 := fun h => by
    have e : u = -1 := by linear_combination h
    rw [e] at hu; simp at hu
  have h2 : u + I ≠ 0 := fun h => by
    have e : u = -I := by linear_combination h
    rw [e] at hu; simp at hu
  have h3 : u - 1 ≠ 0 := fun h => by
    have e : u = 1 := by linear_combination h
    rw [e] at hu; simp at hu
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

/-- The three-point kernel `N(·, y)` against a bounded `R` is integrable on `𝔻*`. -/
theorem d2e_N_int {R : ℂ → ℂ} {Rb : ℝ} (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb) {y : ℂ} (hy : y ∈ unitDiscExterior) :
    IntegrableOn (fun ζ => R ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) unitDiscExterior := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have hy1 : 1 < ‖y‖ := hy
  set δ : ℝ := (‖y‖ - 1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hmaj : Integrable (fun ζ : ℂ => Rb * (‖(y + 1) * (y + I) * (y - 1)‖ *
      (δ⁻¹ * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ + (δ ^ 3)⁻¹ * (ball y δ).indicator (fun ζ => ‖ζ - y‖⁻¹) ζ))) :=
    (((d2e_dn_int.const_mul δ⁻¹).add
      (((integrable_indicator_iff measurableSet_ball).2 (e124p_invnorm_int y δ)).const_mul _)).const_mul _).const_mul _
  have hc : ContinuousOn (fun ζ : ℂ => (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) (unitDiscExterior \ {y}) := by
    apply ContinuousOn.div continuousOn_const
      ((by fun_prop : Continuous fun ζ : ℂ => (ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - y)).continuousOn)
    intro ζ hζ
    exact mul_ne_zero (d2e_dn_ne hζ.1) (sub_ne_zero.2 hζ.2)
  have h1 := hc.aestronglyMeasurable (μ := volume) (hEm.diff (measurableSet_singleton y))
  rw [Measure.restrict_congr_set (sdiff_null_ae_eq_self (μ := volume) (s := unitDiscExterior)
    (measure_singleton y))] at h1
  refine hmaj.integrableOn.mono' (hRm.mul h1) ?_
  filter_upwards [hRb, ae_restrict_mem hEm, ae_restrict_of_ae ((countable_singleton y).ae_notMem volume)]
    with ζ hR hζ hζy
  have hζy' : ζ ≠ y := fun h => hζy (h ▸ rfl)
  have hζ1 : 1 < ‖ζ‖ := hζ
  have hD : 0 < ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ := norm_pos_iff.2 (d2e_dn_ne hζ1)
  have hd : 0 < ‖ζ - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hζy')
  have hRb0 : 0 ≤ Rb := (norm_nonneg _).trans hR
  rw [norm_mul (R ζ), norm_div, norm_mul ((ζ + 1) * (ζ + I) * (ζ - 1)) (ζ - y)]
  have hind0 : 0 ≤ (ball y δ).indicator (fun ζ => ‖ζ - y‖⁻¹) ζ :=
    indicator_nonneg (fun _ _ => inv_nonneg.2 (norm_nonneg _)) _
  have key : (‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ * ‖ζ - y‖)⁻¹ ≤
      δ⁻¹ * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ + (δ ^ 3)⁻¹ * (ball y δ).indicator (fun ζ => ‖ζ - y‖⁻¹) ζ := by
    rw [mul_inv]
    by_cases hb : ‖ζ - y‖ < δ
    · rw [indicator_of_mem (mem_ball_iff_norm.2 hb)]
      have hlow : δ ^ 3 ≤ ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ := by
        apply d2e_dn_lower hδ0.le
        have := norm_sub_norm_le y ζ
        rw [norm_sub_rev] at this
        rw [hδ] at hb ⊢
        linarith
      have : ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ ≤ (δ ^ 3)⁻¹ := inv_anti₀ (by positivity) hlow
      have h2 : 0 ≤ δ⁻¹ * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this (inv_nonneg.2 hd.le)]
    · rw [not_lt] at hb
      have : ‖ζ - y‖⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ0 hb
      have h2 : 0 ≤ (δ ^ 3)⁻¹ * (ball y δ).indicator (fun ζ => ‖ζ - y‖⁻¹) ζ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this (inv_nonneg.2 hD.le)]
  calc ‖R ζ‖ * (‖(y + 1) * (y + I) * (y - 1)‖ / (‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ * ‖ζ - y‖))
      = ‖R ζ‖ * (‖(y + 1) * (y + I) * (y - 1)‖ * (‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ * ‖ζ - y‖)⁻¹) := by
        rw [div_eq_mul_inv]
    _ ≤ Rb * (‖(y + 1) * (y + I) * (y - 1)‖ * (δ⁻¹ * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ +
        (δ ^ 3)⁻¹ * (ball y δ).indicator (fun ζ => ‖ζ - y‖⁻¹) ζ)) :=
        mul_le_mul hR (mul_le_mul_of_nonneg_left key (norm_nonneg _)) (by positivity) hRb0

/-- **(E1), first field, abstract form.** -/
theorem d2e_eta1 {g G R : ℂ → ℂ} {ρ Rb : ℝ} (C : ℂ) (hρ : ρ < 1) (hG : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖})
    (hGi : InjOn G {z : ℂ | ρ < ‖z‖}) (hGd : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0)
    (hGg : EqOn G g unitDiscExterior) (hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖g u‖)
    (hinf : ∃ c > 0, ∃ C : ℝ, ∀ u : ℂ, 4 ≤ ‖u‖ → c * ‖u‖ ≤ ‖g u‖ ∧ ‖deriv g u‖ ≤ C)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb) :
    DifferentiableOn ℂ (fun y : ℂ => (((-(1 / π : ℂ) * ∫ u in unitDiscExterior, R u * deriv g u ^ 2 *
          (1 / (g u - g y) - 1 / g u - g y / g u ^ 2)) + C * g y ^ 2 -
        deriv g y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) / deriv g y))
      unitDiscExterior := by
  obtain ⟨hgd, hg'd, hgi, hdd, hg'⟩ := d2e_basic hρ hG hGi hGd hGg
  have hg0 : ∀ u ∈ unitDiscExterior, g u ≠ 0 := fun u hu h => by
    have := hk u hu
    rw [h, norm_zero] at this
    norm_num at this
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have hcore := fun y (hy : y ∈ unitDiscExterior) => d2e_core hρ hG hGi hGd hGg hk hinf hRm hRb hy
  have hIKd : DifferentiableOn ℂ (fun y => ∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) unitDiscExterior :=
    fun y hy => (hcore y hy).2.differentiableWithinAt
  refine DifferentiableOn.congr ((hIKd.const_mul (-(1 / π : ℂ))).add
    (((differentiableOn_const C).mul (hgd.pow 2)).div hg'd hg')) ?_
  intro y hy
  have hIK := (hcore y hy).1
  have hIN := d2e_N_int hRm hRb hy
  have hM : (∫ u in unitDiscExterior, R u * deriv g u ^ 2 * (1 / (g u - g y) - 1 / g u - g y / g u ^ 2)) =
      deriv g y * ((∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) + ∫ u in unitDiscExterior, R u * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y)))) := by
    rw [← integral_add hIK hIN, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae ((countable_singleton y).ae_notMem volume)]
      with u hu huy
    have huy' : u ≠ y := fun h => huy (h ▸ rfl)
    rw [d2e_K_eq (Ne.symm huy') (hg0 u hu) (hg' u hu) (hg' y hy) (fun h => huy' (hgi hu hy h))
      (d2e_dn_ne hu)]
    have h1 := hg0 u hu
    have h2 : g u - g y ≠ 0 := sub_ne_zero.2 (fun h => huy' (hgi hu hy h))
    have h3 := hg' y hy
    have h4 := d2e_dn_ne (show 1 < ‖u‖ from hu)
    have h5 : u - y ≠ 0 := sub_ne_zero.2 huy'
    generalize (u + 1) * (u + I) * (u - 1) = D at h4 ⊢
    generalize (y + 1) * (y + I) * (y - 1) = E
    field_simp
    ring
  have h3 := hg' y hy
  show _ = -(1 / π : ℂ) * (∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) + C * g y ^ 2 / deriv g y
  rw [hM]
  generalize (∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) = IK
  generalize (∫ u in unitDiscExterior, R u * (((y + 1) * (y + I) * (y - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - y)))) = IN
  field_simp
  ring

/-- Dominated complex differentiation of a parametric integral with a holomorphic kernel. -/
theorem d2e_param {k : ℂ → ℂ → ℂ} {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) {z0 : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall z0 (2 * r) ⊆ U) (hkd : ∀ᵐ u ∂μ, DifferentiableOn ℂ (k u) U)
    (hkm : ∀ y ∈ U, AEStronglyMeasurable (fun u => k u y) μ) {B : ℂ → ℝ} (hBi : Integrable B μ)
    (hB : ∀ᵐ u ∂μ, ∀ y ∈ closedBall z0 (2 * r), ‖k u y‖ ≤ B u) :
    Integrable (fun u => k u z0) μ ∧ DifferentiableAt ℂ (fun y => ∫ u, k u y ∂μ) z0 := by
  have hz0 : z0 ∈ U := hball (mem_closedBall_self (by positivity))
  have htri : ∀ a b c : ℂ, ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := fun a b c => by
    have := norm_add_le (a - b) (b - c)
    rwa [show a - b + (b - c) = a - c by ring] at this
  have hbU : ∀ y ∈ ball z0 r, closedBall y r ⊆ closedBall z0 (2 * r) := fun y hy w hw => by
    have h1 := mem_closedBall_iff_norm.1 hw
    have h2 := mem_ball_iff_norm.1 hy
    exact mem_closedBall_iff_norm.2 (by linarith [htri w y z0])
  have hyU : ∀ y ∈ ball z0 r, y ∈ U := fun y hy => hball (hbU y hy (mem_closedBall_self hr.le))
  have hdb : ∀ᵐ u ∂μ, ∀ y ∈ ball z0 r, ‖deriv (k u) y‖ ≤ B u / r := by
    filter_upwards [hkd, hB] with u hu hBu y hy
    have hdc : DiffContOnCl ℂ (k u) (ball y r) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ hr.ne']
      exact hu.mono ((hbU y hy).trans hball)
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc
      (fun w hw => hBu w (hbU y hy (sphere_subset_closedBall hw)))
  have hdm : AEStronglyMeasurable (fun u => deriv (k u) z0) μ := by
    set s : ℕ → ℂ := fun n => z0 + ((r / ((n : ℝ) + 2) : ℝ) : ℂ) with hs
    have hsp : ∀ n : ℕ, 0 < r / ((n : ℝ) + 2) := fun n => div_pos hr (by positivity)
    have hsU : ∀ n, s n ∈ U := by
      intro n
      apply hyU
      rw [mem_ball_iff_norm, hs]
      simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hsp n)]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsne : ∀ n, s n ≠ z0 := by
      intro n h
      rw [hs] at h
      have : ((r / ((n : ℝ) + 2) : ℝ) : ℂ) = 0 := by linear_combination h
      exact (hsp n).ne' (by exact_mod_cast this)
    have hrt : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have hsc : Tendsto s atTop (𝓝 z0) := by
      have := ((Complex.continuous_ofReal.tendsto 0).comp hrt).const_add z0
      simpa [hs, Function.comp_def] using this
    have hsn : Tendsto s atTop (𝓝[≠] z0) :=
      tendsto_nhdsWithin_iff.2 ⟨hsc, Eventually.of_forall fun n => hsne n⟩
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n u => (s n - z0)⁻¹ * (k u (s n) - k u z0)) (fun n => ?_) ?_
    · exact ((hkm _ (hsU n)).sub (hkm z0 hz0)).const_mul _
    · filter_upwards [hkd] with u hu
      have hda := (hu.differentiableAt (hU.mem_nhds hz0)).hasDerivAt
      have ht := (hasDerivAt_iff_tendsto_slope.1 hda).comp hsn
      refine ht.congr fun n => ?_
      simp only [Function.comp_apply, slope_def_field, div_eq_inv_mul]
  have hF_int : Integrable (fun u => k u z0) μ := by
    refine hBi.mono' (hkm z0 hz0) ?_
    filter_upwards [hB] with u hu using hu z0 (mem_closedBall_self (by positivity))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun y u => k u y) (F' := fun y u => deriv (k u) y) (x₀ := z0)
    (bound := fun u => B u / r) (ball_mem_nhds z0 hr)
    (by filter_upwards [hU.mem_nhds hz0] with y hy using hkm y hy) hF_int hdm hdb (hBi.div_const r)
    (by
      filter_upwards [hkd] with u hu y hy
      exact (hu.differentiableAt (hU.mem_nhds (hyU y hy))).hasDerivAt)
  exact ⟨hF_int, key.2.differentiableAt⟩

/-- The reflected coefficient `S(ζ) = conj R(1/ζ̄) ζ²/ζ̄²` is bounded measurable on `𝔻`. -/
theorem d2e_S_ae {R : ℂ → ℂ} {Rb : ℝ} (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb) :
    AEStronglyMeasurable (fun ζ => conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2) (volume.restrict unitDisc) ∧
      ∀ᵐ ζ ∂(volume.restrict unitDisc), ‖conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2‖ ≤ Rb := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hR' : AEStronglyMeasurable (unitDiscExterior.indicator R) volume :=
    (aestronglyMeasurable_indicator_iff hEm).2 hRm
  have hRr := aestronglyMeasurable_comp_refl hR'
  have h0 : ∀ᵐ ζ ∂(volume.restrict unitDisc), ζ ≠ 0 :=
    ae_restrict_of_ae ((countable_singleton (0 : ℂ)).ae_notMem volume)
  have heq : ∀ ζ ∈ unitDisc, ζ ≠ 0 → R (1 / conj ζ) = (unitDiscExterior.indicator R ∘ refl) ζ := by
    intro ζ hζ hζ0
    have hr : refl ζ ∈ unitDiscExterior := (refl_mem_exterior_iff hζ0).2 hζ
    rw [Function.comp_apply, indicator_of_mem hr, one_div]
    rfl
  constructor
  · have h1 : AEStronglyMeasurable (fun ζ => conj ((unitDiscExterior.indicator R ∘ refl) ζ) * ζ ^ 2 / conj ζ ^ 2)
        (volume.restrict unitDisc) :=
      ((continuous_conj.comp_aestronglyMeasurable hRr.restrict).mul
        (continuous_id.pow 2).aestronglyMeasurable).div₀
        ((continuous_conj.pow 2).aestronglyMeasurable)
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem hDm, h0] with ζ hζ hζ0
    rw [heq ζ hζ hζ0]
  · have hb := (ae_restrict_iff' hEm).1 hRb
    have hb' := ae_refl hb
    filter_upwards [ae_restrict_mem hDm, h0, ae_restrict_of_ae hb'] with ζ hζ hζ0 hζb
    have hr : refl ζ ∈ unitDiscExterior := (refl_mem_exterior_iff hζ0).2 hζ
    have hn : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.2 hζ0
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_conj, Complex.norm_conj,
      mul_div_assoc, div_self (pow_ne_zero 2 hn), mul_one, one_div]
    exact hζb hr

/-- **(E1), second field, abstract form.** -/
theorem d2e_eta2 {g G R : ℂ → ℂ} {ρ Rb : ℝ} (C : ℂ) (hρ : ρ < 1) (hG : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖})
    (hGi : InjOn G {z : ℂ | ρ < ‖z‖}) (hGd : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0)
    (hGg : EqOn G g unitDiscExterior)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb) :
    DifferentiableOn ℂ (fun y : ℂ => ((C * g y ^ 2 -
        deriv g y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) / deriv g y)) unitDiscExterior := by
  obtain ⟨hgd, hg'd, hgi, hdd, hg'⟩ := d2e_basic hρ hG hGi hGd hGg
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  obtain ⟨hSm, hSb⟩ := d2e_S_ae hRm hRb
  have hQ : DifferentiableOn ℂ (fun y => ∫ ζ in unitDisc, conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) unitDiscExterior := by
    intro z0 hz0
    have hz01 : 1 < ‖z0‖ := hz0
    set r : ℝ := (‖z0‖ - 1) / 4 with hr
    have hr0 : 0 < r := by rw [hr]; linarith
    have hball : closedBall z0 (2 * r) ⊆ unitDiscExterior := fun w hw => by
      have h1 := mem_closedBall_iff_norm.1 hw
      have h2 := norm_sub_norm_le z0 w
      rw [norm_sub_rev] at h2
      show 1 < ‖w‖
      rw [hr] at h1
      linarith
    obtain ⟨A, hA⟩ := (isCompact_closedBall z0 (2 * r)).exists_bound_of_continuousOn
      ((by fun_prop : Continuous fun w : ℂ => (w + 1) * (w + I) * (w - 1)).continuousOn)
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA z0 (mem_closedBall_self (by positivity)))
    refine (d2e_param (k := fun ζ y => conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y)))) (μ := volume.restrict unitDisc) hE hr0 hball
      ?_ ?_ (B := fun ζ => Rb * A / (2 * r) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹)
      (d2e_dn_int.const_mul _).integrableOn ?_).2.differentiableWithinAt
    · filter_upwards [ae_restrict_mem hDm] with ζ hζ
      have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
      apply DifferentiableOn.const_mul
      apply DifferentiableOn.div (by fun_prop) (by fun_prop)
      intro y hy
      have hy1 : 1 < ‖y‖ := hy
      exact mul_ne_zero (d2e_dn_ne1 hζ1) (sub_ne_zero.2 fun h => by rw [h] at hζ1; linarith)
    · intro y hy
      have hy1 : 1 < ‖y‖ := hy
      refine hSm.mul (ContinuousOn.aestronglyMeasurable ?_ hDm)
      apply ContinuousOn.div continuousOn_const
        ((by fun_prop : Continuous fun ζ : ℂ => (ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - y)).continuousOn)
      intro ζ hζ
      have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
      exact mul_ne_zero (d2e_dn_ne1 hζ1) (sub_ne_zero.2 fun h => by rw [h] at hζ1; linarith)
    · filter_upwards [ae_restrict_mem hDm, hSb] with ζ hζ hSζ y hy
      have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
      have hy' := mem_closedBall_iff_norm.1 hy
      have hsep : 2 * r ≤ ‖ζ - y‖ := by
        have h1 := norm_sub_norm_le y ζ
        have h2 := norm_sub_norm_le z0 y
        rw [norm_sub_rev ζ y]
        rw [norm_sub_rev] at h2
        rw [hr] at hy' ⊢
        linarith
      have hD : 0 < ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ := norm_pos_iff.2 (d2e_dn_ne1 hζ1)
      have hRb0 : 0 ≤ Rb := (norm_nonneg _).trans hSζ
      rw [norm_mul (conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2), norm_div ((y + 1) * (y + I) * (y - 1)),
        norm_mul ((ζ + 1) * (ζ + I) * (ζ - 1)) (ζ - y)]
      calc ‖conj (R (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2‖ * (‖(y + 1) * (y + I) * (y - 1)‖ / (‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ * ‖ζ - y‖))
          ≤ Rb * (A / (‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ * (2 * r))) := by
            apply mul_le_mul hSζ _ (by positivity) hRb0
            exact div_le_div₀ hA0 (hA y hy) (by positivity)
              (mul_le_mul_of_nonneg_left hsep (norm_nonneg _))
        _ = Rb * A / (2 * r) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ := by
            field_simp
  exact ((((differentiableOn_const C).mul (hgd.pow 2)).sub
    (hg'd.mul (hQ.const_mul (-(1 / π : ℂ))))).div hg'd hg')

/-- **(G-DOM)** Dominated version of (G): if `t ↦ F_t(z)` is real differentiable near `0` with `|F_s|` and `|∂F_s|`
dominated by a fixed `G ∈ L²(D)`, then `t ↦ ∫_D |F_t|²` is real differentiable at `0` with the TT derivative. -/
theorem s3d_l2sq_dom {D : Set ℂ} (hD : MeasurableSet D) {F : ℂ → ℂ → ℂ} {F₀ : ℂ → ℂ} (h0 : F 0 = F₀)
    (hdom : ∃ r > 0, ∃ G : ℂ → ℝ, MemLp G 2 (volume.restrict D) ∧ ∀ s ∈ ball (0 : ℂ) r,
      AEStronglyMeasurable (F s) (volume.restrict D) ∧ ∀ z ∈ D,
        DifferentiableAt ℝ (fun t => F t z) s ∧ ‖fderiv ℝ (fun t => F t z) s‖ ≤ G z ∧ ‖F s z‖ ≤ G z) :
    DifferentiableAt ℝ (fun t : ℂ => ((∫ z in D, ‖F t z‖ ^ 2 : ℝ) : ℂ)) 0 ∧
      dz (fun t : ℂ => ((∫ z in D, ‖F t z‖ ^ 2 : ℝ) : ℂ)) 0 =
        ∫ z in D, (F₀ z * conj (dzbar (fun s => F s z) 0) + conj (F₀ z) * dz (fun s => F s z) 0) := by
  subst h0
  obtain ⟨r, hr, G, hG, hb⟩ := hdom
  have hG2 : Integrable (fun z => G z ^ 2) (volume.restrict D) := hG.integrable_sq
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hae : ∀ᵐ z ∂(volume.restrict D), z ∈ D := ae_restrict_mem hD
  -- measurability of the directional derivatives at `0`
  have hdir : ∀ v : ℂ, ‖v‖ = 1 →
      AEStronglyMeasurable (fun z => fderiv ℝ (fun t => F t z) 0 v) (volume.restrict D) := by
    intro v hv
    set c : ℕ → ℝ := fun n => ((n : ℝ) + 1) * (2 / r) with hc
    have hcpos : ∀ n, 0 < c n := fun n => by positivity
    have hcin : ∀ n, (0 : ℂ) + (c n)⁻¹ • v ∈ ball (0 : ℂ) r := by
      intro n
      have h2 : r⁻¹ < 2 / r := by
        rw [div_eq_mul_inv]
        linarith [inv_pos.2 hr]
      have h3 : 2 / r ≤ c n := le_mul_of_one_le_left (by positivity)
        (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      rw [zero_add, mem_ball_zero_iff, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_inv,
        abs_of_pos (hcpos n)]
      exact (inv_lt_comm₀ (hcpos n) hr).2 (by linarith)
    have htc : Tendsto (fun n => ‖c n‖) atTop atTop := by
      have hct : Tendsto c atTop atTop :=
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const (by positivity)
      exact tendsto_norm_atTop_atTop.comp hct
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n z => c n • (F ((0 : ℂ) + (c n)⁻¹ • v) z - F 0 z)) (fun n => ?_) ?_
    · exact ((hb _ (hcin n)).1.sub (hb 0 h0b).1).const_smul (c n)
    · filter_upwards [hae] with z hz
      exact ((hb 0 h0b).2 z hz).1.hasFDerivAt.lim v htc
  have hDF : AEStronglyMeasurable (fun z => fderiv ℝ (fun t => F t z) 0) (volume.restrict D) := by
    have h1 := hdir 1 (by simp)
    have hI := hdir I (by simp)
    set A := ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM with hA
    set B := ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM with hB
    have hrep : (fun z => fderiv ℝ (fun t => F t z) 0) = fun z =>
        A (fderiv ℝ (fun t => F t z) 0 1) + B (fderiv ℝ (fun t => F t z) 0 I) := by
      funext z
      refine ContinuousLinearMap.ext fun v => ?_
      have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • I := by
        apply Complex.ext <;> simp
      have e1 : (A (fderiv ℝ (fun t => F t z) 0 1) + B (fderiv ℝ (fun t => F t z) 0 I)) v =
          (v.re : ℝ) • fderiv ℝ (fun t => F t z) 0 1 + (v.im : ℝ) • fderiv ℝ (fun t => F t z) 0 I :=
        rfl
      rw [e1]
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul]
    have hcont : Continuous (fun p : ℂ × ℂ => A p.1 + B p.2) :=
      (A.continuous.comp continuous_fst).add (B.continuous.comp continuous_snd)
    have hm := hcont.comp_aestronglyMeasurable (h1.prodMk hI)
    rw [hrep]
    exact hm
  -- the derivative of `t ↦ ‖F_t(z)‖²`
  set F' : ℂ → ℂ → ℂ →L[ℝ] ℝ := fun s z => 2 • (innerSL ℝ (F s z)).comp (fderiv ℝ (fun t => F t z) s)
    with hF'
  set P := (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).comp (innerSL ℝ (E := ℂ)) with hP
  have hF'meas : AEStronglyMeasurable (F' 0) (volume.restrict D) := by
    have hc := (P.continuous₂.comp_aestronglyMeasurable ((hb 0 h0b).1.prodMk hDF)).const_smul (2 : ℕ)
    exact hc
  have hbound : ∀ᵐ z ∂(volume.restrict D), ∀ s ∈ ball (0 : ℂ) r, ‖F' s z‖ ≤ 2 * G z ^ 2 := by
    filter_upwards [hae] with z hz s hs
    obtain ⟨-, hn1, hn2⟩ := (hb s hs).2 z hz
    calc ‖F' s z‖ = 2 * ‖(innerSL ℝ (F s z)).comp (fderiv ℝ (fun t => F t z) s)‖ := by
          simp only [hF']
          rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
          norm_num
      _ ≤ 2 * (‖innerSL ℝ (F s z)‖ * ‖fderiv ℝ (fun t => F t z) s‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by norm_num)
      _ = 2 * (‖F s z‖ * ‖fderiv ℝ (fun t => F t z) s‖) := by rw [innerSL_apply_norm]
      _ ≤ 2 * (G z * G z) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hn2 hn1 (norm_nonneg _) ((norm_nonneg _).trans hn2))
            (by norm_num)
      _ = 2 * G z ^ 2 := by ring
  have hdiff : ∀ᵐ z ∂(volume.restrict D), ∀ s ∈ ball (0 : ℂ) r,
      HasFDerivAt (fun t => ‖F t z‖ ^ 2) (F' s z) s := by
    filter_upwards [hae] with z hz s hs
    exact ((hb s hs).2 z hz).1.hasFDerivAt.norm_sq
  have hint0 : Integrable (fun z => ‖F 0 z‖ ^ 2) (volume.restrict D) := by
    refine hG2.mono' ((hb 0 h0b).1.norm.pow 2) ?_
    filter_upwards [hae] with z hz
    have h := ((hb 0 h0b).2 z hz).2.2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hmeasF : ∀ᶠ s in 𝓝 (0 : ℂ), AEStronglyMeasurable (fun z => ‖F s z‖ ^ 2) (volume.restrict D) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with s hs
    exact (hb s hs).1.norm.pow 2
  have hfd := hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds (0 : ℂ) hr) hmeasF hint0
    hF'meas hbound (hG2.const_mul 2) hdiff
  have hcd : HasFDerivAt (fun t : ℂ => ((∫ z in D, ‖F t z‖ ^ 2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (∫ z in D, F' 0 z)) 0 :=
    Complex.ofRealCLM.hasFDerivAt.comp 0 hfd
  refine ⟨hcd.differentiableAt, ?_⟩
  -- the value of `∂`
  have hF'int : Integrable (F' 0) (volume.restrict D) :=
    (hG2.const_mul 2).mono' hF'meas (hbound.mono fun z hz => hz 0 h0b)
  have happ : ∀ v : ℂ, (∫ z in D, F' 0 z) v = ∫ z in D, F' 0 z v := fun v =>
    ContinuousLinearMap.integral_apply hF'int v
  have hpt : ∀ z v, F' 0 z v = 2 * (conj (F 0 z) * fderiv ℝ (fun t => F t z) 0 v).re := by
    intro z v
    simp only [hF', ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Pi.smul_apply,
      Function.comp_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat]
    rw [Complex.inner, mul_comm (fderiv ℝ (fun t => F t z) 0 v)]
  have hre : ∀ v : ℂ, ‖v‖ = 1 → Integrable (fun z => (conj (F 0 z) * fderiv ℝ (fun t => F t z) 0 v).re)
      (volume.restrict D) := by
    intro v hv
    refine hG2.mono' ((Complex.continuous_re.comp_aestronglyMeasurable
      ((((hb 0 h0b).1).star).mul (hdir v hv)))) ?_
    filter_upwards [hae] with z hz
    obtain ⟨-, hn1, hn2⟩ := (hb 0 h0b).2 z hz
    have hdv : ‖fderiv ℝ (fun t => F t z) 0 v‖ ≤ G z := by
      calc _ ≤ ‖fderiv ℝ (fun t => F t z) 0‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (fun t => F t z) 0‖ := by rw [hv, mul_one]
        _ ≤ G z := hn1
    calc ‖(conj (F 0 z) * fderiv ℝ (fun t => F t z) 0 v).re‖
        ≤ ‖conj (F 0 z) * fderiv ℝ (fun t => F t z) 0 v‖ := by
          rw [Real.norm_eq_abs]
          exact Complex.abs_re_le_norm _
      _ = ‖F 0 z‖ * ‖fderiv ℝ (fun t => F t z) 0 v‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ G z * G z := mul_le_mul hn2 hdv (norm_nonneg _) ((norm_nonneg _).trans hn2)
      _ = G z ^ 2 := by ring
  have hval : dz (fun t : ℂ => ((∫ z in D, ‖F t z‖ ^ 2 : ℝ) : ℂ)) 0 =
      (((∫ z in D, (conj (F 0 z) * fderiv ℝ (fun t => F t z) 0 1).re : ℝ) : ℂ) -
        I * ((∫ z in D, (conj (F 0 z) * fderiv ℝ (fun t => F t z) 0 I).re : ℝ) : ℂ)) := by
    unfold dz
    rw [hcd.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, happ, happ,
      Complex.ofRealCLM_apply, Complex.ofRealCLM_apply]
    simp only [hpt]
    rw [integral_const_mul, integral_const_mul]
    push_cast
    ring
  rw [hval]
  have hfin : (fun z => (F 0 z * conj (dzbar (fun s => F s z) 0) + conj (F 0 z) * dz (fun s => F s z) 0)) =
      fun z => (((conj (F 0 z) * fderiv ℝ (fun t => F t z) 0 1).re : ℝ) : ℂ) -
        I * (((conj (F 0 z) * fderiv ℝ (fun t => F t z) 0 I).re : ℝ) : ℂ) := by
    funext z
    unfold dz dzbar
    rw [Complex.re_eq_add_conj, Complex.re_eq_add_conj]
    simp only [map_div₀, map_add, map_sub, map_mul, Complex.conj_I, Complex.conj_conj, map_ofNat]
    ring
  have i1 : Integrable (fun z => (((conj (F 0 z) * fderiv ℝ (fun t => F t z) 0 1).re : ℝ) : ℂ))
      (volume.restrict D) := (hre 1 (by simp)).ofReal
  have i2 : Integrable (fun z => I * (((conj (F 0 z) * fderiv ℝ (fun t => F t z) 0 I).re : ℝ) : ℂ))
      (volume.restrict D) := ((hre I (by simp)).ofReal).const_mul I
  rw [hfin, integral_sub i1 i2, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]

/-- From the (G-DOM) domination: differentiability at `0` and `L²` Wirtinger derivatives at `0` (measurability
from difference quotients, `HasFDerivAt.lim`; bound `‖∂F‖, ‖∂̄F‖ ≤ ‖DF‖ ≤ G`). -/
theorem s3x_dom_data {D : Set ℂ} (hD : MeasurableSet D) {F : ℂ → ℂ → ℂ}
    (hdom : ∃ r > 0, ∃ G : ℂ → ℝ, MemLp G 2 (volume.restrict D) ∧ ∀ s ∈ ball (0 : ℂ) r,
      AEStronglyMeasurable (F s) (volume.restrict D) ∧ ∀ z ∈ D,
        DifferentiableAt ℝ (fun t => F t z) s ∧ ‖fderiv ℝ (fun t => F t z) s‖ ≤ G z ∧ ‖F s z‖ ≤ G z) :
    (∀ z ∈ D, DifferentiableAt ℝ (fun t => F t z) 0) ∧
      MemLp (fun z => dz (fun t => F t z) 0) 2 (volume.restrict D) ∧
      MemLp (fun z => dzbar (fun t => F t z) 0) 2 (volume.restrict D) := by
  obtain ⟨r, hr, G, hG, hb⟩ := hdom
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hae : ∀ᵐ z ∂(volume.restrict D), z ∈ D := ae_restrict_mem hD
  have hdir : ∀ v : ℂ, ‖v‖ = 1 →
      AEStronglyMeasurable (fun z => fderiv ℝ (fun t => F t z) 0 v) (volume.restrict D) := by
    intro v hv
    set c : ℕ → ℝ := fun n => ((n : ℝ) + 1) * (2 / r) with hc
    have hcpos : ∀ n, 0 < c n := fun n => by positivity
    have hcin : ∀ n, (0 : ℂ) + (c n)⁻¹ • v ∈ ball (0 : ℂ) r := by
      intro n
      have h3 : 2 / r ≤ c n := le_mul_of_one_le_left (by positivity)
        (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      have h2 : r⁻¹ < 2 / r := by
        rw [div_eq_mul_inv]
        linarith [inv_pos.2 hr]
      rw [zero_add, mem_ball_zero_iff, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_inv,
        abs_of_pos (hcpos n)]
      exact (inv_lt_comm₀ (hcpos n) hr).2 (by linarith)
    have htc : Tendsto (fun n => ‖c n‖) atTop atTop := by
      have hct : Tendsto c atTop atTop :=
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const (by positivity)
      exact tendsto_norm_atTop_atTop.comp hct
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n z => c n • (F ((0 : ℂ) + (c n)⁻¹ • v) z - F 0 z)) (fun n => ?_) ?_
    · exact ((hb _ (hcin n)).1.sub (hb 0 h0b).1).const_smul (c n)
    · filter_upwards [hae] with z hz
      exact ((hb 0 h0b).2 z hz).1.hasFDerivAt.lim v htc
  have h1 := hdir 1 (by simp)
  have hI := hdir I (by simp)
  have hbd : ∀ z ∈ D, ‖fderiv ℝ (fun t => F t z) 0 1‖ ≤ ‖G z‖ ∧ ‖fderiv ℝ (fun t => F t z) 0 I‖ ≤ ‖G z‖ := by
    intro z hz
    have hf := ((hb 0 h0b).2 z hz).2.1
    have hG' : G z ≤ ‖G z‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    constructor
    · refine ((fderiv ℝ (fun t => F t z) 0).le_opNorm 1).trans ?_
      rw [norm_one, mul_one]
      exact hf.trans hG'
    · refine ((fderiv ℝ (fun t => F t z) 0).le_opNorm I).trans ?_
      rw [Complex.norm_I, mul_one]
      exact hf.trans hG'
  refine ⟨fun z hz => ((hb 0 h0b).2 z hz).1, ?_, ?_⟩
  · refine hG.of_le ?_ ?_
    · show AEStronglyMeasurable (fun z => (fderiv ℝ (fun t => F t z) 0 1 - I * fderiv ℝ (fun t => F t z) 0 I) / 2)
        (volume.restrict D)
      exact (continuous_id.div_const (2 : ℂ)).comp_aestronglyMeasurable (h1.sub (hI.const_mul I))
    · filter_upwards [hae] with z hz
      obtain ⟨e1, e2⟩ := hbd z hz
      show ‖(fderiv ℝ (fun t => F t z) 0 1 - I * fderiv ℝ (fun t => F t z) 0 I) / 2‖ ≤ ‖G z‖
      rw [norm_div, Complex.norm_two]
      have := (norm_sub_le _ _).trans (add_le_add e1 (show ‖I * fderiv ℝ (fun t => F t z) 0 I‖ ≤ ‖G z‖ by
        rw [norm_mul, Complex.norm_I, one_mul]; exact e2))
      linarith
  · refine hG.of_le ?_ ?_
    · show AEStronglyMeasurable (fun z => (fderiv ℝ (fun t => F t z) 0 1 + I * fderiv ℝ (fun t => F t z) 0 I) / 2)
        (volume.restrict D)
      exact (continuous_id.div_const (2 : ℂ)).comp_aestronglyMeasurable (h1.add (hI.const_mul I))
    · filter_upwards [hae] with z hz
      obtain ⟨e1, e2⟩ := hbd z hz
      show ‖(fderiv ℝ (fun t => F t z) 0 1 + I * fderiv ℝ (fun t => F t z) 0 I) / 2‖ ≤ ‖G z‖
      rw [norm_div, Complex.norm_two]
      have := (norm_add_le _ _).trans (add_le_add e1 (show ‖I * fderiv ℝ (fun t => F t z) 0 I‖ ≤ ‖G z‖ by
        rw [norm_mul, Complex.norm_I, one_mul]; exact e2))
      linarith

/-- `|ζ - z|⁻¹` on a disc: integrable, with `∫_{B(z, r)} |ζ - z|⁻¹ = 2πr` (as `s4g_int_inv_norm_ball` and
`s71c2_ball_inv`, which lie outside this import closure). -/
theorem s3d5_ball (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun w : ℂ => ‖w - z‖⁻¹) (ball z r) ∧ ∫ w in ball z r, ‖w - z‖⁻¹ = 2 * π * r := by
  refine ⟨⟨((measurable_id.sub_const z).norm.inv).aestronglyMeasurable, ?_⟩, ?_⟩
  · show (∫⁻ w in ball z r, ‖‖w - z‖⁻¹‖ₑ) < ∞
    have h := lintegral_ball_sub_enorm_rpow_neg (a := 1) (by norm_num) hr z
    refine lt_of_le_of_lt (lintegral_mono fun w => ?_) (h ▸ ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ENNReal.ofReal_lt_top)
    by_cases hw : w = z
    · subst hw
      simp
    · have hne : ‖w - z‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hw)
      rw [ENNReal.rpow_neg_one, enorm_inv hne, Real.enorm_eq_ofReal (norm_nonneg _), ofReal_norm]
  · rw [← integral_indicator measurableSet_ball]
    have he : (ball z r).indicator (fun v => ‖v - z‖⁻¹) =
        fun v => (Iio r).indicator (fun y : ℝ => y⁻¹) ‖v - z‖ := by
      funext v
      simp only [indicator, mem_ball, dist_eq_norm, mem_Iio]
    rw [he, integral_sub_right_eq_self (fun x : ℂ => (Iio r).indicator (fun y : ℝ => y⁻¹) ‖x‖) z,
      integral_fun_norm_addHaar, Complex.finrank_real_complex]
    have hb : volume.real (ball (0 : ℂ) 1) = π := by simp [Measure.real, Complex.volume_ball]
    rw [hb]
    have hc : EqOn (fun y : ℝ => y ^ (2 - 1) • (Iio r).indicator (fun y : ℝ => y⁻¹) y)
        ((Ioo 0 r).indicator fun _ => (1 : ℝ)) (Ioi 0) := by
      intro y hy
      have hy0 : (0 : ℝ) < y := hy
      by_cases hyr : y < r
      · simp only [indicator, mem_Iio, mem_Ioo, hyr, hy0, true_and, ite_true, show (2 : ℕ) - 1 = 1 from rfl,
          pow_one, smul_eq_mul]
        field_simp
      · simp [indicator, hyr]
    rw [setIntegral_congr_fun measurableSet_Ioi hc, setIntegral_indicator measurableSet_Ioo,
      Ioi_inter_Ioo, max_self]
    simp [hr.le]
    ring

/-- **Decay of the Cauchy potential of a weight decaying like `|ζ|⁻²`.** For `v ≥ 0` with `v ≤ A|ζ|⁻²` near `∞` and
`v/max(1, |ζ|) ∈ L¹`, `ζ ↦ v(ζ)/|ζ - w|` is integrable for large `w`, and `∫ v(ζ)/|ζ - w| → 0` as `w → ∞`
(near part `|ζ - w| < |w|/2` by the exact disc integral, far part by dominated convergence). -/
theorem s3d5_decay {v : ℂ → ℝ} (hvm : Measurable v) (hv0 : ∀ ζ, 0 ≤ v ζ) {A ρ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ ζ : ℂ, ρ ≤ ‖ζ‖ → v ζ ≤ A / ‖ζ‖ ^ 2) (hvi : Integrable fun ζ => v ζ / max 1 ‖ζ‖) :
    (∀ᶠ w in cocompact ℂ, Integrable fun ζ => v ζ * ‖ζ - w‖⁻¹) ∧
      Tendsto (fun w => ∫ ζ, v ζ * ‖ζ - w‖⁻¹) (cocompact ℂ) (𝓝 0) := by
  have hA0 : 0 ≤ A := by
    have hn : ‖((ρ : ℝ) : ℂ)‖ = ρ := by rw [Complex.norm_real, Real.norm_of_nonneg hρ.le]
    have h := (hv0 (ρ : ℂ)).trans (hA (ρ : ℂ) hn.ge)
    rw [hn] at h
    exact (div_nonneg_iff.mp h).elim (fun h' => h'.1) fun h' => absurd h'.2 (not_le.mpr (by positivity))
  have hT : ∀ᶠ w in cocompact ℂ, max (2 * ρ) 2 ≤ ‖w‖ := tendsto_norm_cocompact_atTop.eventually_ge_atTop _
  have hfar : ∀ w : ℂ, max (2 * ρ) 2 ≤ ‖w‖ → ∀ ζ, ζ ∉ ball w (‖w‖ / 2) → ‖ζ - w‖⁻¹ ≤ 6 / max 1 ‖ζ‖ := by
    intro w hw ζ hζ
    rw [mem_ball, dist_eq_norm, not_lt] at hζ
    have h2 : 2 ≤ ‖w‖ := (le_max_right _ _).trans hw
    have h3 : ‖ζ‖ ≤ ‖ζ - w‖ + ‖w‖ := by
      have := norm_add_le (ζ - w) w
      rwa [sub_add_cancel] at this
    have hm : max 1 ‖ζ‖ ≤ 6 * ‖ζ - w‖ := max_le (by linarith) (by linarith)
    rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by positivity)]
    linarith
  have hnear : ∀ w : ℂ, max (2 * ρ) 2 ≤ ‖w‖ → ∀ ζ ∈ ball w (‖w‖ / 2), v ζ ≤ 4 * A / ‖w‖ ^ 2 := by
    intro w hw ζ hζ
    rw [mem_ball, dist_eq_norm] at hζ
    have h1 : ‖w‖ ≤ ‖w - ζ‖ + ‖ζ‖ := by
      have := norm_add_le (w - ζ) ζ
      rwa [sub_add_cancel] at this
    rw [norm_sub_rev] at h1
    have hz : ‖w‖ / 2 ≤ ‖ζ‖ := by linarith
    have hρz : ρ ≤ ‖ζ‖ := le_trans (by linarith [le_max_left (2 * ρ) 2]) hz
    have hwp : 0 < ‖w‖ := by linarith [le_max_right (2 * ρ) 2]
    refine (hA ζ hρz).trans ?_
    calc A / ‖ζ‖ ^ 2 ≤ A / (‖w‖ / 2) ^ 2 :=
          div_le_div_of_nonneg_left hA0 (by positivity) (pow_le_pow_left₀ (by positivity) hz 2)
      _ = 4 * A / ‖w‖ ^ 2 := by field_simp; ring
  have hmeas : ∀ w : ℂ, Measurable fun ζ => v ζ * ‖ζ - w‖⁻¹ := fun w =>
    hvm.mul (measurable_id.sub_const w).norm.inv
  have hint : ∀ w : ℂ, max (2 * ρ) 2 ≤ ‖w‖ → Integrable fun ζ => v ζ * ‖ζ - w‖⁻¹ := by
    intro w hw
    have hwp : 0 < ‖w‖ := by linarith [le_max_right (2 * ρ) 2]
    refine Integrable.mono' ((((s3d5_ball w (by positivity : 0 < ‖w‖ / 2)).1.integrable_indicator
      measurableSet_ball).const_mul (4 * A / ‖w‖ ^ 2)).add (hvi.const_mul 6)) (hmeas w).aestronglyMeasurable
      (Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hv0 ζ) (inv_nonneg.mpr (norm_nonneg _)))]
    show _ ≤ 4 * A / ‖w‖ ^ 2 * (ball w (‖w‖ / 2)).indicator (fun ζ => ‖ζ - w‖⁻¹) ζ + 6 * (v ζ / max 1 ‖ζ‖)
    have hi0 : 0 ≤ ‖ζ - w‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    by_cases hζ : ζ ∈ ball w (‖w‖ / 2)
    · rw [Set.indicator_of_mem hζ]
      have := mul_le_mul_of_nonneg_right (hnear w hw ζ hζ) hi0
      have : 0 ≤ 6 * (v ζ / max 1 ‖ζ‖) := by
        have := hv0 ζ; positivity
      linarith
    · rw [Set.indicator_of_notMem hζ, mul_zero, zero_add]
      have := mul_le_mul_of_nonneg_left (hfar w hw ζ hζ) (hv0 ζ)
      calc v ζ * ‖ζ - w‖⁻¹ ≤ v ζ * (6 / max 1 ‖ζ‖) := this
        _ = 6 * (v ζ / max 1 ‖ζ‖) := by ring
  refine ⟨hT.mono hint, ?_⟩
  -- the far part tends to `0` by dominated convergence
  haveI : (cocompact ℂ).IsCountablyGenerated := by
    rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop]
    infer_instance
  set Fw : ℂ → ℂ → ℝ := fun w ζ => (ball w (‖w‖ / 2))ᶜ.indicator (fun ζ => v ζ * ‖ζ - w‖⁻¹) ζ with hFw
  have hF : Tendsto (fun w => ∫ ζ, Fw w ζ) (cocompact ℂ) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (F := Fw) (f := fun _ => (0 : ℝ))
      (fun ζ => 6 * (v ζ / max 1 ‖ζ‖))
      (Eventually.of_forall fun w => ((hmeas w).indicator
        (measurableSet_ball : MeasurableSet (ball w (‖w‖ / 2))).compl).aestronglyMeasurable)
      (hT.mono fun w hw => Eventually.of_forall fun ζ => ?_) (hvi.const_mul 6)
      (Eventually.of_forall fun ζ => ?_)
    · simpa only [integral_zero] using h
    · show ‖(ball w (‖w‖ / 2))ᶜ.indicator (fun ζ => v ζ * ‖ζ - w‖⁻¹) ζ‖ ≤ 6 * (v ζ / max 1 ‖ζ‖)
      by_cases hζ : ζ ∈ ball w (‖w‖ / 2)
      · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hζ), norm_zero]
        have := hv0 ζ; positivity
      · rw [Set.indicator_of_mem hζ, Real.norm_of_nonneg (mul_nonneg (hv0 ζ) (inv_nonneg.mpr (norm_nonneg _)))]
        calc v ζ * ‖ζ - w‖⁻¹ ≤ v ζ * (6 / max 1 ‖ζ‖) := mul_le_mul_of_nonneg_left (hfar w hw ζ hζ) (hv0 ζ)
          _ = 6 * (v ζ / max 1 ‖ζ‖) := by ring
    · have hd : Tendsto (fun w => ‖ζ - w‖) (cocompact ℂ) atTop := by
        refine tendsto_atTop_mono (fun w => ?_) (tendsto_atTop_add_const_right _ (-‖ζ‖) tendsto_norm_cocompact_atTop)
        have := norm_sub_norm_le w ζ
        rw [norm_sub_rev] at this
        linarith
      have hl : Tendsto (fun w => v ζ * ‖ζ - w‖⁻¹) (cocompact ℂ) (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.comp hd).const_mul (v ζ)
      refine hl.congr' ?_
      filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (2 * ‖ζ‖)] with w hw
      have hζ : ζ ∈ (ball w (‖w‖ / 2))ᶜ := by
        rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt]
        have := norm_sub_norm_le w ζ
        rw [norm_sub_rev w ζ] at this
        linarith
      show _ = (ball w (‖w‖ / 2))ᶜ.indicator (fun ζ => v ζ * ‖ζ - w‖⁻¹) ζ
      rw [Set.indicator_of_mem hζ]
  have hG : Tendsto (fun w => 4 * π * A / ‖w‖ + ∫ ζ, Fw w ζ) (cocompact ℂ) (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop).add hF
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hG
    (Eventually.of_forall fun w => integral_nonneg fun ζ =>
      mul_nonneg (hv0 ζ) (inv_nonneg.mpr (norm_nonneg _))) (hT.mono fun w hw => ?_)
  have hwp : 0 < ‖w‖ := by linarith [le_max_right (2 * ρ) 2]
  obtain ⟨hbi, hbv⟩ := s3d5_ball w (by positivity : 0 < ‖w‖ / 2)
  have hI1 : Integrable fun ζ => 4 * A / ‖w‖ ^ 2 * (ball w (‖w‖ / 2)).indicator (fun ζ => ‖ζ - w‖⁻¹) ζ :=
    (hbi.integrable_indicator measurableSet_ball).const_mul _
  have hI2 : Integrable fun ζ => Fw w ζ := (hint w hw).indicator measurableSet_ball.compl
  calc ∫ ζ, v ζ * ‖ζ - w‖⁻¹
      ≤ ∫ ζ, (4 * A / ‖w‖ ^ 2 * (ball w (‖w‖ / 2)).indicator (fun ζ => ‖ζ - w‖⁻¹) ζ + Fw w ζ) := by
        refine integral_mono (hint w hw) (hI1.add hI2) fun ζ => ?_
        show _ ≤ 4 * A / ‖w‖ ^ 2 * (ball w (‖w‖ / 2)).indicator (fun ζ => ‖ζ - w‖⁻¹) ζ +
          (ball w (‖w‖ / 2))ᶜ.indicator (fun ζ => v ζ * ‖ζ - w‖⁻¹) ζ
        by_cases hζ : ζ ∈ ball w (‖w‖ / 2)
        · rw [Set.indicator_of_mem hζ, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hζ), add_zero]
          exact mul_le_mul_of_nonneg_right (hnear w hw ζ hζ) (inv_nonneg.mpr (norm_nonneg _))
        · rw [Set.indicator_of_notMem hζ, Set.indicator_of_mem hζ, mul_zero, zero_add]
    _ = 4 * π * A / ‖w‖ + ∫ ζ, Fw w ζ := by
        rw [integral_add hI1 hI2, integral_const_mul, integral_indicator measurableSet_ball, hbv]
        field_simp

/-- A factor of `Dn` away from its root: `|ζ - p| ≥ (1 + |ζ|)/6` when `|p| ≤ 1` and `|ζ - p| ≥ 1/2`. -/
theorem s3d5_fac {p ζ : ℂ} (hp : ‖p‖ ≤ 1) (hζ : 1 / 2 ≤ ‖ζ - p‖) : (1 + ‖ζ‖) / 6 ≤ ‖ζ - p‖ := by
  have h := norm_sub_norm_le ζ p
  by_cases h2 : 2 ≤ ‖ζ‖
  · linarith
  · push_neg at h2
    linarith

/-- `1/|Dn| ∈ L¹(ℂ)`, `Dn(ζ) = (ζ + 1)(ζ + i)(ζ - 1)` (three simple poles, decay `|ζ|⁻³`). -/
theorem s3d5_Dn_int : Integrable fun ζ : ℂ => ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ := by
  have hb := fun p : ℂ => ((s3d5_ball p (by norm_num : (0 : ℝ) < 1 / 2)).1.integrable_indicator measurableSet_ball)
  have hj : Integrable fun ζ : ℂ => (1 + ‖ζ‖) ^ (-(3 : ℝ)) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  have hm : Measurable fun ζ : ℂ => ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ := by fun_prop
  refine Integrable.mono' ((((hb (-1)).const_mul 4).add ((hb (-I)).const_mul 4)).add
    (((hb 1).const_mul 4).add (hj.const_mul 216))) hm.aestronglyMeasurable (Eventually.of_forall fun ζ => ?_)
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  show _ ≤ 4 * (ball (-1) (1 / 2)).indicator (fun w => ‖w - -1‖⁻¹) ζ +
      4 * (ball (-I) (1 / 2)).indicator (fun w => ‖w - -I‖⁻¹) ζ +
    (4 * (ball 1 (1 / 2)).indicator (fun w => ‖w - 1‖⁻¹) ζ + 216 * (1 + ‖ζ‖) ^ (-(3 : ℝ)))
  have e1 : ζ + 1 = ζ - -1 := by ring
  have e2 : ζ + I = ζ - -I := by ring
  rw [norm_mul, norm_mul, e1, e2]
  set a := ‖ζ - -1‖
  set b := ‖ζ - -I‖
  set c := ‖ζ - 1‖
  have ha := norm_nonneg (ζ - -1)
  have hbn := norm_nonneg (ζ - -I)
  have hc := norm_nonneg (ζ - 1)
  -- pairwise separation of the roots
  have s12 : 1 ≤ a + b := by
    have := norm_sub_le (ζ - -1) (ζ - -I)
    have h' : ‖(ζ - -1) - (ζ - -I)‖ = ‖1 - I‖ := by congr 1; ring
    have h'' : 1 ≤ ‖1 - I‖ := by
      have := Complex.abs_re_le_norm (1 - I); simpa using this
    rw [h'] at this; linarith [norm_sub_rev (ζ - -I) (ζ - -1)]
  have s13 : 2 ≤ a + c := by
    have := norm_sub_le (ζ - -1) (ζ - 1)
    have h' : ‖(ζ - -1) - (ζ - 1)‖ = 2 := by
      rw [show (ζ - -1) - (ζ - 1) = (2 : ℂ) by ring]; norm_num
    rw [h'] at this; linarith [norm_sub_rev (ζ - 1) (ζ - -1)]
  have s23 : 1 ≤ b + c := by
    have := norm_sub_le (ζ - -I) (ζ - 1)
    have h' : ‖(ζ - -I) - (ζ - 1)‖ = ‖1 + I‖ := by congr 1; ring
    have h'' : 1 ≤ ‖1 + I‖ := by
      have := Complex.abs_re_le_norm (1 + I); simpa using this
    rw [h'] at this; linarith [norm_sub_rev (ζ - 1) (ζ - -I)]
  have i0 : ∀ p : ℂ, 0 ≤ (ball p (1 / 2)).indicator (fun w => ‖w - p‖⁻¹) ζ := fun p =>
    Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) ζ
  have j0 : 0 ≤ (1 + ‖ζ‖) ^ (-(3 : ℝ)) := by positivity
  have hpos : ∀ x : ℝ, 1 / 2 ≤ x → ∀ y : ℝ, 1 / 2 ≤ y → ∀ t : ℝ, 0 ≤ t → (t * x * y)⁻¹ ≤ 4 * t⁻¹ := by
    intro x hx y hy t ht
    rcases ht.eq_or_lt with h | h
    · rw [← h]; simp
    rw [mul_assoc, mul_inv, show 4 * t⁻¹ = t⁻¹ * 4 by ring]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr ht)
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  by_cases h1 : ζ ∈ ball (-1) (1 / 2)
  · have ha' : a < 1 / 2 := by rw [mem_ball, dist_eq_norm] at h1; exact h1
    rw [Set.indicator_of_mem h1]
    have := hpos b (by linarith) c (by linarith) a ha
    nlinarith [i0 (-I), i0 1]
  by_cases h2 : ζ ∈ ball (-I) (1 / 2)
  · have hb' : b < 1 / 2 := by rw [mem_ball, dist_eq_norm] at h2; exact h2
    rw [Set.indicator_of_mem h2]
    have := hpos a (by linarith) c (by linarith) b hbn
    have e : (a * b * c)⁻¹ = (b * a * c)⁻¹ := by ring_nf
    nlinarith [i0 (-1), i0 1]
  by_cases h3 : ζ ∈ ball (1 : ℂ) (1 / 2)
  · have hc' : c < 1 / 2 := by rw [mem_ball, dist_eq_norm] at h3; exact h3
    rw [Set.indicator_of_mem h3]
    have := hpos a (by linarith) b (by linarith) c hc
    have e : (a * b * c)⁻¹ = (c * a * b)⁻¹ := by ring_nf
    nlinarith [i0 (-1), i0 (-I)]
  -- away from the roots: each factor is `≥ (1 + |ζ|)/6`
  have ga : 1 / 2 ≤ a := by rw [mem_ball, dist_eq_norm, not_lt] at h1; exact h1
  have gb : 1 / 2 ≤ b := by rw [mem_ball, dist_eq_norm, not_lt] at h2; exact h2
  have gc : 1 / 2 ≤ c := by rw [mem_ball, dist_eq_norm, not_lt] at h3; exact h3
  have fa := s3d5_fac (by simp) ga
  have fb := s3d5_fac (by simp) gb
  have fc := s3d5_fac (by simp) gc
  have hq : 0 < 1 + ‖ζ‖ := by positivity
  have hr : (1 + ‖ζ‖) ^ (-(3 : ℝ)) = ((1 + ‖ζ‖) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hq.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hprod : ((1 + ‖ζ‖) / 6) ^ 3 ≤ a * b * c := by
    have := mul_le_mul (mul_le_mul fa fb (by positivity) ha) fc (by positivity) (by positivity)
    nlinarith [this]
  have hinv : (a * b * c)⁻¹ ≤ 216 * (1 + ‖ζ‖) ^ (-(3 : ℝ)) := by
    rw [hr, ← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by nlinarith [hprod, pow_pos hq 3])]
    nlinarith [hprod]
  nlinarith [i0 (-1), i0 (-I), i0 1]

/-- `0 ∉ closure g(𝔻*)`: the normalized exterior welding `W` (a homeomorphism of `ℂ` with `W(w_A(0)) = 0`,
`|w_A(0)| < 1`) satisfies `|W u| ≥ ε` for `|u| ≥ 1`. -/
theorem s3d5_lower {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ u : ℂ, 1 ≤ ‖u‖ → ε ≤ ‖normalizedWeldingExterior μ u‖ := by
  obtain ⟨hc, hp⟩ := normalizedWeldingExterior_continuous_proper hμ
  obtain ⟨u₀, hu₀, he⟩ := wAS_maps_disc hμ (z := 0) (by norm_num)
  have hau : wA μ 0 = u₀ := congrArg finPart he
  have hG0 : normalizedWeldingExterior μ u₀ = 0 := by
    rw [← hau, normalizedWeldingExterior_closedDisk hμ (by simp), (fB_normalization μ).1]
  have hne : ∀ u : ℂ, 1 ≤ ‖u‖ → normalizedWeldingExterior μ u ≠ 0 := fun u hu h => by
    have := (normalizedWeldingExterior_bijective hμ).1 (h.trans hG0.symm)
    rw [this] at hu
    linarith
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.mp (hp (isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact)
  have hK1 : IsCompact (K ∩ {u : ℂ | 1 ≤ ‖u‖}) := hK.inter_right (isClosed_le continuous_const continuous_norm)
  obtain ⟨B, hB⟩ := hK1.exists_bound_of_continuousOn
    ((hc.norm.continuousOn).inv₀ fun u hu => norm_ne_zero_iff.mpr (hne u hu.2))
  have hB1 : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨min 1 (1 / max B 1), lt_min one_pos (by positivity), min_le_left _ _, fun u hu => ?_⟩
  by_cases huK : u ∈ K
  · have h1 : ‖‖normalizedWeldingExterior μ u‖⁻¹‖ ≤ B := hB u ⟨huK, hu⟩
    rw [norm_inv, norm_norm] at h1
    have hw := norm_pos_iff.mpr (hne u hu)
    have h2 : ‖normalizedWeldingExterior μ u‖⁻¹ ≤ max B 1 := h1.trans (le_max_left _ _)
    refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ hB1]
    calc (1 : ℝ) = ‖normalizedWeldingExterior μ u‖ * ‖normalizedWeldingExterior μ u‖⁻¹ :=
          (mul_inv_cancel₀ hw.ne').symm
      _ ≤ ‖normalizedWeldingExterior μ u‖ * max B 1 := mul_le_mul_of_nonneg_left h2 hw.le
  · have h := hKs huK
    simp only [mem_preimage, mem_compl_iff, mem_closedBall_zero_iff, not_le] at h
    exact (min_le_left _ _).trans h.le

/-- Linear growth `|g(z)| ≤ K|z|` near `∞`, from the reciprocal chart `t ↦ 1/g(1/t)` (analytic at `0`, value `0`,
nonzero derivative). -/
theorem s3d5_growth {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ z in cocompact ℂ, ‖gsans μ z‖ ≤ K * ‖z‖ := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hd := s5cf_exterior_reciprocal_deriv_ne_zero hμ h0
  have ha : AnalyticAt ℂ (fun w => s5cf_exterior_reciprocal (μ, star μ) w) 0 :=
    (s5cf_exterior_reciprocal_analytic hμ h0).comp (analyticAt_const.prod analyticAt_id)
  have hD := ha.differentiableAt.hasDerivAt
  have hE0 : s5cf_exterior_reciprocal (μ, star μ) 0 = 0 := by
    rw [← s5cf_gchart_eq hμ h0]
    simp [s5cf_gchart]
  set d := deriv (fun w => s5cf_exterior_reciprocal (μ, star μ) w) 0 with hdd
  have hdp : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hb := hD.isLittleO.def (c := ‖d‖ / 2) (by positivity)
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), ‖d‖ / 2 * ‖t‖ ≤ ‖s5cf_exterior_reciprocal (μ, star μ) t‖ := hb.mono fun t ht => by
    simp only [hE0, sub_zero, smul_eq_mul] at ht
    have h1 := norm_sub_norm_le (t * d) (s5cf_exterior_reciprocal (μ, star μ) t)
    rw [norm_sub_rev, norm_mul] at h1
    linarith
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) :=
    Metric.cobounded_eq_cocompact (α := ℂ) ▸ tendsto_inv₀_cobounded
  refine ⟨2 / ‖d‖, by positivity, ?_⟩
  filter_upwards [hinv.eventually hev, tendsto_norm_cocompact_atTop.eventually_gt_atTop 1] with z hz hz1
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
  have ht : z⁻¹ ∈ unitDisc := by
    refine mem_ball_zero_iff.mpr ?_
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz1
  have hc : s5cf_exterior_reciprocal (μ, star μ) z⁻¹ = (gMu μ z)⁻¹ := by
    rw [← s5cf_gchart_eq hμ ht]
    simp only [s5cf_gchart, inv_eq_zero, hz0, if_false, inv_inv]
  rw [hc, norm_inv, norm_inv] at hz
  rw [S2C.s2c_gsans_eq hμ]
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hgp : 0 < ‖gMu μ z‖⁻¹ := lt_of_lt_of_le (by positivity) hz
  have hg : 0 < ‖gMu μ z‖ := inv_pos.mp hgp
  have h1 : ‖d‖ / 2 * ‖z‖⁻¹ * ‖gMu μ z‖ ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hz hg.le
    rwa [inv_mul_cancel₀ hg.ne'] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ hdp]
  have h2 : ‖d‖ * ‖gMu μ z‖ ≤ 2 * ‖z‖ := by
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 * ‖z‖)
    field_simp at this
    linarith
  linarith

/-- **(P5a)** `γ̇(z)/z² → c₂` at `∞`, for the D0 kernel `N(ζ, z) = Dn(z)/(Dn(ζ)(ζ - z))`. Since
`N(ζ, z)/z² → -1/Dn(ζ)`, the claim is that `∫_S R N / z² → -∫_S R/Dn`, on any measurable `S`, for bounded `R`.
Hint: `N/z² + 1/Dn = (z²(ζ+i) - z - i)/(z² Dn(ζ)(ζ - z))`, which is `≲ |ζ|⁻²|ζ - z|⁻¹` for large `|z|`, so
`∫ |ζ|⁻²|ζ - z|⁻¹ = O(log|z|/|z|)`. -/
theorem s3dv_gamma_asym {S : Set ℂ} (hS : MeasurableSet S) {R : ℂ → ℂ} {M : ℝ}
    (hRm : AEStronglyMeasurable R (volume.restrict S)) (hRb : ∀ᵐ u ∂(volume.restrict S), ‖R u‖ ≤ M) :
    Tendsto (fun z : ℂ => (∫ ζ in S, R ζ *
        ((z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z)))) / z ^ 2)
      (cocompact ℂ) (𝓝 (-∫ ζ in S, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)))) := by
  set M' := max M 0 with hM'
  have hRb' : ∀ᵐ u ∂(volume.restrict S), ‖R u‖ ≤ M' := hRb.mono fun u hu => hu.trans (le_max_left _ _)
  have hM0 : 0 ≤ M' := le_max_right _ _
  have hDi := s3d5_Dn_int
  -- the weight `v = (1 + |ζ|)/|Dn(ζ)|`
  have hvm : Measurable fun ζ : ℂ => (1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ := by fun_prop
  have hv0 : ∀ ζ : ℂ, 0 ≤ (1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ := fun ζ => by positivity
  have hA : ∀ ζ : ℂ, 2 ≤ ‖ζ‖ → (1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ ≤ 12 / ‖ζ‖ ^ 2 := by
    intro ζ hζ
    have f : ∀ p : ℂ, ‖p‖ = 1 → ‖ζ‖ / 2 ≤ ‖ζ - p‖ := fun p hp => by
      have := norm_sub_norm_le ζ p; linarith
    have e1 : ζ + 1 = ζ - -1 := by ring
    have e2 : ζ + I = ζ - -I := by ring
    rw [norm_mul, norm_mul, e1, e2]
    have fa := f (-1) (by simp)
    have fb := f (-I) (by simp)
    have fc := f 1 (by simp)
    have hz : 0 < ‖ζ‖ := by linarith
    have hprod : (‖ζ‖ / 2) ^ 3 ≤ ‖ζ - -1‖ * ‖ζ - -I‖ * ‖ζ - 1‖ := by
      have := mul_le_mul (mul_le_mul fa fb (by positivity) (norm_nonneg _)) fc (by positivity) (by positivity)
      nlinarith [this]
    have hp : 0 < ‖ζ - -1‖ * ‖ζ - -I‖ * ‖ζ - 1‖ := lt_of_lt_of_le (by positivity) hprod
    rw [← div_eq_mul_inv, div_le_div_iff₀ hp (by positivity)]
    nlinarith [hprod, pow_pos hz 3]
  have hvi : Integrable fun ζ : ℂ => (1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ / max 1 ‖ζ‖ := by
    refine Integrable.mono' (hDi.const_mul 2) (hvm.div (measurable_const.max measurable_norm)).aestronglyMeasurable
      (Eventually.of_forall fun ζ => ?_)
    have hm1 : 1 ≤ max 1 ‖ζ‖ := le_max_left _ _
    rw [Real.norm_of_nonneg (div_nonneg (hv0 ζ) (by linarith)), div_le_iff₀ (by linarith)]
    have hi := inv_nonneg.mpr (norm_nonneg ((ζ + 1) * (ζ + I) * (ζ - 1)))
    nlinarith [le_max_right 1 ‖ζ‖, mul_le_mul_of_nonneg_left (le_max_right 1 ‖ζ‖) hi,
      mul_le_mul_of_nonneg_left hm1 hi]
  obtain ⟨hKi, hKt⟩ := s3d5_decay hvm hv0 (by norm_num : (0 : ℝ) < 2) hA hvi
  -- reduce to the difference
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (by have := hKt.const_mul (3 * M'); rwa [mul_zero] at this)
  filter_upwards [hKi, tendsto_norm_cocompact_atTop.eventually_ge_atTop 1] with z hKz hz1
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
  have hzz : (z ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hz0
  have hmN : Measurable fun ζ : ℂ => (z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z)) := by
    fun_prop
  have hmD : Measurable fun ζ : ℂ => (1 : ℂ) / ((ζ + 1) * (ζ + I) * (ζ - 1)) := by fun_prop
  -- integrability of the two pieces on `S`
  have hI1 : IntegrableOn (fun ζ => R ζ *
      ((z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z)))) S := by
    refine Integrable.mono' ((hKz.const_mul (M' * ‖(z + 1) * (z + I) * (z - 1)‖)).integrableOn)
      (hRm.mul hmN.aestronglyMeasurable) (hRb'.mono fun ζ hζ => ?_)
    rw [norm_mul, norm_div, norm_mul ((ζ + 1) * (ζ + I) * (ζ - 1)), div_eq_mul_inv, mul_inv]
    have h1 := inv_nonneg.mpr (norm_nonneg ((ζ + 1) * (ζ + I) * (ζ - 1)))
    have h2 := inv_nonneg.mpr (norm_nonneg (ζ - z))
    have h3 : ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - z‖⁻¹ ≤
        (1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - z‖⁻¹ := by
      nlinarith [norm_nonneg ζ, mul_nonneg h1 h2, mul_nonneg (mul_nonneg (norm_nonneg ζ) h1) h2]
    calc ‖R ζ‖ * (‖(z + 1) * (z + I) * (z - 1)‖ * (‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - z‖⁻¹))
        ≤ M' * (‖(z + 1) * (z + I) * (z - 1)‖ * ((1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - z‖⁻¹)) :=
          mul_le_mul hζ (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) (by positivity) hM0
      _ = _ := by ring
  have hI2 : IntegrableOn (fun ζ => R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) S := by
    have hmi : Measurable fun ζ : ℂ => ((ζ + 1) * (ζ + I) * (ζ - 1))⁻¹ := by fun_prop
    refine Integrable.mono' ((hDi.const_mul M').integrableOn)
      ((hRm.mul hmi.aestronglyMeasurable).congr (Eventually.of_forall fun ζ => (div_eq_mul_inv _ _).symm))
      (hRb'.mono fun ζ hζ => ?_)
    rw [norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hζ (inv_nonneg.mpr (norm_nonneg _))
  have hrw : (∫ ζ in S, R ζ * ((z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z)))) / z ^ 2 -
      -∫ ζ in S, R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) =
      ∫ ζ in S, (R ζ * ((z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z))) / z ^ 2 +
        R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) := by
    rw [sub_neg_eq_add, ← integral_div, integral_add (hI1.div_const _) hI2]
  rw [hrw]
  have hne : ∀ᵐ ζ ∂(volume.restrict S), ζ ≠ z := ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton z))
  have hKz' : Integrable fun ζ => 3 * M' * ((1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - z‖⁻¹) :=
    hKz.const_mul _
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ ζ in S, ‖R ζ * ((z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z))) / z ^ 2 +
        R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))‖
      ≤ ∫ ζ in S, 3 * M' * ((1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - z‖⁻¹) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ζ => norm_nonneg _) hKz'.integrableOn ?_
        filter_upwards [hRb', hne] with ζ hR hζz
        have e : R ζ * ((z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z))) / z ^ 2 +
            R ζ / ((ζ + 1) * (ζ + I) * (ζ - 1)) = R ζ * ((z + 1) * (z + I) * (z - 1) /
              ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z)) / z ^ 2 + 1 / ((ζ + 1) * (ζ + I) * (ζ - 1))) := by ring
        rw [e, norm_mul]
        have hk : ‖(z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z)) / z ^ 2 +
            1 / ((ζ + 1) * (ζ + I) * (ζ - 1))‖ ≤
            3 * ((1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - z‖⁻¹) := by
          by_cases hD0 : (ζ + 1) * (ζ + I) * (ζ - 1) = 0
          · rw [hD0]
            simp only [zero_mul, div_zero, zero_div, add_zero, norm_zero]
            positivity
          have hsz : ζ - z ≠ 0 := sub_ne_zero.mpr hζz
          have hid : (z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z)) / z ^ 2 +
              1 / ((ζ + 1) * (ζ + I) * (ζ - 1)) =
              (z ^ 2 * (ζ + I) - z - I) / (z ^ 2 * ((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z)) := by
            field_simp
            ring
          rw [hid, norm_div, norm_mul, norm_mul, norm_pow]
          have hn : ‖z ^ 2 * (ζ + I) - z - I‖ ≤ 3 * ‖z‖ ^ 2 * (1 + ‖ζ‖) := by
            have h1 := norm_sub_le (z ^ 2 * (ζ + I) - z) I
            have h2 := norm_sub_le (z ^ 2 * (ζ + I)) z
            have h3 : ‖ζ + I‖ ≤ ‖ζ‖ + 1 := by
              have := norm_add_le ζ I; rwa [Complex.norm_I] at this
            rw [norm_mul, norm_pow, Complex.norm_I] at *
            have h4 : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖z‖), norm_nonneg ζ]
          have hd : 0 < ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ := norm_pos_iff.mpr hD0
          have he : 0 < ‖ζ - z‖ := norm_pos_iff.mpr hsz
          have hz2 : 0 < ‖z‖ ^ 2 := by positivity
          have e3 : 3 * ((1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - z‖⁻¹) =
              3 * ‖z‖ ^ 2 * (1 + ‖ζ‖) / (‖z‖ ^ 2 * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ * ‖ζ - z‖) := by
            field_simp
          rw [e3]
          exact div_le_div_of_nonneg_right hn (by positivity)
        calc ‖R ζ‖ * _ ≤ M' * (3 * ((1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - z‖⁻¹)) :=
              mul_le_mul hR hk (norm_nonneg _) hM0
          _ = _ := by ring
    _ ≤ ∫ ζ, 3 * M' * ((1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - z‖⁻¹) :=
        setIntegral_le_integral hKz' (Eventually.of_forall fun ζ => by positivity)
    _ = 3 * M' * ∫ ζ, (1 + ‖ζ‖) * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ * ‖ζ - z‖⁻¹ := integral_const_mul _ _

/-- **(P5b)** `V̇(g z)/z² → 0` at `∞`, for the Model B variation pushed through `g = gsans μ`, with kernel
`1/(g u - ζ) - 1/g u - ζ/g u² = ζ²/(g u² (g u - ζ))` at `ζ = g z`. Split the integral at `|u| = R₀`:
- on the bounded part, `g(u)` is bounded and `g(z) → ∞`, so the kernel is `O(1/|g z|)`, and
  `∫ |R| |g'|² ≤ M · area` is finite;
- on `|u| ≥ R₀`, `g(u) = bu + O(1)`, `g' = b + O(u⁻²)` (exterior reciprocal chart), so the integrand
  divided by `z²` is `≲ |u|⁻²|u - z|⁻¹`. -/
theorem s3dv_vdot_asym {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {R : ℂ → ℂ} {M : ℝ}
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ M) :
    Tendsto (fun z : ℂ => (∫ u in unitDiscExterior, R u * deriv (gsans μ) u ^ 2 *
        (1 / (gsans μ u - gsans μ z) - 1 / gsans μ u - gsans μ z / gsans μ u ^ 2)) / z ^ 2)
      (cocompact ℂ) (𝓝 0) := by
  set M' := max M 0 with hM'
  have hM0 : 0 ≤ M' := le_max_right _ _
  have hRb' : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ M' :=
    hRb.mono fun u hu => hu.trans (le_max_left _ _)
  obtain ⟨ε, hε, hε1, hlow⟩ := s3d5_lower hμ
  obtain ⟨K, hK, hgrow⟩ := s3d5_growth hμ
  have hGW : ∀ u ∈ unitDiscExterior, gsans μ u = normalizedWeldingExterior μ u := fun u hu => by
    rw [S2C.s2c_gsans_eq hμ]
    exact gMu_eq_normalizedWeldingExterior hμ hu
  have hext : ∀ᶠ z in cocompact ℂ, z ∈ unitDiscExterior := tendsto_norm_cocompact_atTop.eventually_gt_atTop 1
  have hGt : Tendsto (gsans μ) (cocompact ℂ) (cocompact ℂ) :=
    (normalizedWeldingExterior_continuous_proper hμ).2.congr' (hext.mono fun z hz => (hGW z hz).symm)
  have hconf := S2C.s2c_conf_g hμ
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hΩm : MeasurableSet (gsans μ '' unitDiscExterior) :=
    hEo.measurableSet.image_of_continuousOn_injOn hconf.1.continuousOn hconf.2.1
  have hΩε : ∀ ζ ∈ gsans μ '' unitDiscExterior, ε ≤ ‖ζ‖ := by
    rintro ζ ⟨u, hu, rfl⟩
    rw [hGW u hu]
    exact hlow u (le_of_lt hu)
  -- the weight `v = 1_{|ζ| ≥ ε} |ζ|⁻²`
  have hSm : MeasurableSet {ζ : ℂ | ε ≤ ‖ζ‖} := measurableSet_le measurable_const measurable_norm
  have hvm : Measurable fun ζ : ℂ => {ζ : ℂ | ε ≤ ‖ζ‖}.indicator (fun ζ => (‖ζ‖ ^ 2)⁻¹) ζ :=
    ((measurable_norm.pow_const 2).inv).indicator hSm
  have hv0 : ∀ ζ : ℂ, 0 ≤ {ζ : ℂ | ε ≤ ‖ζ‖}.indicator (fun ζ => (‖ζ‖ ^ 2)⁻¹) ζ := fun ζ =>
    Set.indicator_nonneg (fun _ _ => by positivity) ζ
  have hA : ∀ ζ : ℂ, ε ≤ ‖ζ‖ → {ζ : ℂ | ε ≤ ‖ζ‖}.indicator (fun ζ => (‖ζ‖ ^ 2)⁻¹) ζ ≤ 1 / ‖ζ‖ ^ 2 :=
    fun ζ hζ => by rw [Set.indicator_of_mem (show ζ ∈ {ζ : ℂ | ε ≤ ‖ζ‖} from hζ), one_div]
  have hvi : Integrable fun ζ : ℂ => {ζ : ℂ | ε ≤ ‖ζ‖}.indicator (fun ζ => (‖ζ‖ ^ 2)⁻¹) ζ / max 1 ‖ζ‖ := by
    have hj : Integrable fun ζ : ℂ => (1 + ‖ζ‖) ^ (-(3 : ℝ)) :=
      integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
    refine Integrable.mono' (hj.const_mul (8 / ε ^ 2))
      (hvm.div (measurable_const.max measurable_norm)).aestronglyMeasurable (Eventually.of_forall fun ζ => ?_)
    have hm1 : 1 ≤ max 1 ‖ζ‖ := le_max_left _ _
    rw [Real.norm_of_nonneg (div_nonneg (hv0 ζ) (by linarith))]
    by_cases hζ : ε ≤ ‖ζ‖
    · rw [Set.indicator_of_mem (show ζ ∈ {ζ : ℂ | ε ≤ ‖ζ‖} from hζ)]
      have ht : 0 < ‖ζ‖ := lt_of_lt_of_le hε hζ
      have hq : 0 < 1 + ‖ζ‖ := by linarith
      rw [Real.rpow_neg hq.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        show (‖ζ‖ ^ 2)⁻¹ / max 1 ‖ζ‖ = 1 / (‖ζ‖ ^ 2 * max 1 ‖ζ‖) by field_simp,
        show 8 / ε ^ 2 * ((1 + ‖ζ‖) ^ 3)⁻¹ = 8 / (ε ^ 2 * (1 + ‖ζ‖) ^ 3) by field_simp,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have hε2 : ε ^ 2 ≤ 1 := by nlinarith
      by_cases h1 : 1 ≤ ‖ζ‖
      · rw [max_eq_right h1]
        have h2 : (1 + ‖ζ‖) ^ 3 ≤ 8 * ‖ζ‖ ^ 3 := by
          have := pow_le_pow_left₀ hq.le (show 1 + ‖ζ‖ ≤ 2 * ‖ζ‖ by linarith) 3
          nlinarith
        nlinarith [pow_pos hq 3]
      · push_neg at h1
        rw [max_eq_left h1.le]
        have h2 : (1 + ‖ζ‖) ^ 3 ≤ 8 := by
          have := pow_le_pow_left₀ hq.le (show 1 + ‖ζ‖ ≤ 2 by linarith) 3
          nlinarith
        have h3 : ε ^ 2 ≤ ‖ζ‖ ^ 2 := pow_le_pow_left₀ hε.le hζ 2
        nlinarith [pow_pos hq 3]
    · rw [Set.indicator_of_notMem (show ζ ∉ {ζ : ℂ | ε ≤ ‖ζ‖} from hζ), zero_div]
      positivity
  obtain ⟨hKi, hKt⟩ := s3d5_decay hvm hv0 hε hA hvi
  refine squeeze_zero_norm' ?_ (by have := (hKt.comp hGt).const_mul (M' * K ^ 2); rwa [mul_zero] at this)
  filter_upwards [hGt.eventually hKi, hgrow, hext] with z hKz hgz hzD
  have hz0 : 0 < ‖z‖ := lt_trans one_pos hzD
  set w := gsans μ z with hw
  -- the kernel on `Ω = g(𝔻*)`
  have hH : IntegrableOn (fun ζ => (‖ζ‖ ^ 2)⁻¹ * ‖ζ - w‖⁻¹) (gsans μ '' unitDiscExterior) := by
    refine (hKz.integrableOn (s := gsans μ '' unitDiscExterior)).congr_fun (fun ζ hζ => ?_) hΩm
    show {ζ : ℂ | ε ≤ ‖ζ‖}.indicator (fun ζ => (‖ζ‖ ^ 2)⁻¹) ζ * ‖ζ - w‖⁻¹ = _
    rw [Set.indicator_of_mem (show ζ ∈ {ζ : ℂ | ε ≤ ‖ζ‖} from hΩε ζ hζ)]
  have hint1 := (ahP_integrableOn_image hEo hconf.1 hconf.2.1 _).mp hH
  have hcov := ahP_integral_image (E := ℝ) hEo hconf.1 hconf.2.1 fun ζ => (‖ζ‖ ^ 2)⁻¹ * ‖ζ - w‖⁻¹
  have hle : ∫ ζ in gsans μ '' unitDiscExterior, (‖ζ‖ ^ 2)⁻¹ * ‖ζ - w‖⁻¹ ≤
      ∫ ζ, {ζ : ℂ | ε ≤ ‖ζ‖}.indicator (fun ζ => (‖ζ‖ ^ 2)⁻¹) ζ * ‖ζ - w‖⁻¹ := by
    rw [setIntegral_congr_fun hΩm (g := fun ζ => {ζ : ℂ | ε ≤ ‖ζ‖}.indicator (fun ζ => (‖ζ‖ ^ 2)⁻¹) ζ *
      ‖ζ - w‖⁻¹) fun ζ hζ => by
        show _ = {ζ : ℂ | ε ≤ ‖ζ‖}.indicator (fun ζ => (‖ζ‖ ^ 2)⁻¹) ζ * ‖ζ - w‖⁻¹
        rw [Set.indicator_of_mem (show ζ ∈ {ζ : ℂ | ε ≤ ‖ζ‖} from hΩε ζ hζ)]]
    exact setIntegral_le_integral hKz (Eventually.of_forall fun ζ =>
      mul_nonneg (hv0 ζ) (inv_nonneg.mpr (norm_nonneg _)))
  have hne : ∀ᵐ u ∂(volume.restrict unitDiscExterior), u ≠ z :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton z))
  have hpt : ∀ᵐ u ∂(volume.restrict unitDiscExterior),
      ‖R u * deriv (gsans μ) u ^ 2 * (1 / (gsans μ u - w) - 1 / gsans μ u - w / gsans μ u ^ 2)‖ ≤
        M' * ‖w‖ ^ 2 * (‖deriv (gsans μ) u‖ ^ 2 • ((‖gsans μ u‖ ^ 2)⁻¹ * ‖gsans μ u - w‖⁻¹)) := by
    filter_upwards [hRb', hne, ae_restrict_mem hEo.measurableSet] with u hR huz hu
    have hgu : gsans μ u ≠ 0 := by
      intro h
      have := hlow u (le_of_lt hu)
      rw [← hGW u hu, h, norm_zero] at this
      linarith
    have hguw : gsans μ u - w ≠ 0 := by
      intro h
      rw [sub_eq_zero, hw, hGW u hu, hGW z hzD] at h
      exact huz ((normalizedWeldingExterior_bijective hμ).1 h)
    have hk : 1 / (gsans μ u - w) - 1 / gsans μ u - w / gsans μ u ^ 2 = w ^ 2 / (gsans μ u ^ 2 * (gsans μ u - w)) := by
      field_simp
      ring
    rw [hk, smul_eq_mul, norm_mul, norm_mul, norm_div, norm_mul, norm_pow, norm_pow, norm_pow, div_eq_mul_inv,
      mul_inv]
    have h1 := norm_nonneg (deriv (gsans μ) u)
    have h2 := norm_nonneg w
    have h3 := inv_nonneg.mpr (pow_nonneg (norm_nonneg (gsans μ u)) 2)
    have h4 := inv_nonneg.mpr (norm_nonneg (gsans μ u - w))
    calc ‖R u‖ * ‖deriv (gsans μ) u‖ ^ 2 * (‖w‖ ^ 2 * ((‖gsans μ u‖ ^ 2)⁻¹ * ‖gsans μ u - w‖⁻¹))
        ≤ M' * ‖deriv (gsans μ) u‖ ^ 2 * (‖w‖ ^ 2 * ((‖gsans μ u‖ ^ 2)⁻¹ * ‖gsans μ u - w‖⁻¹)) := by
          gcongr
      _ = _ := by ring
  rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
  calc ‖∫ u in unitDiscExterior, R u * deriv (gsans μ) u ^ 2 *
        (1 / (gsans μ u - w) - 1 / gsans μ u - w / gsans μ u ^ 2)‖
      ≤ ∫ u in unitDiscExterior, M' * ‖w‖ ^ 2 *
          (‖deriv (gsans μ) u‖ ^ 2 • ((‖gsans μ u‖ ^ 2)⁻¹ * ‖gsans μ u - w‖⁻¹)) :=
        (norm_integral_le_integral_norm _).trans
          (integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) (hint1.const_mul _) hpt)
    _ = M' * ‖w‖ ^ 2 * ∫ ζ in gsans μ '' unitDiscExterior, (‖ζ‖ ^ 2)⁻¹ * ‖ζ - w‖⁻¹ := by
        rw [integral_const_mul, hcov]
    _ ≤ M' * ‖w‖ ^ 2 * ∫ ζ, {ζ : ℂ | ε ≤ ‖ζ‖}.indicator (fun ζ => (‖ζ‖ ^ 2)⁻¹) ζ * ‖ζ - w‖⁻¹ :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ M' * K ^ 2 * (∫ ζ, {ζ : ℂ | ε ≤ ‖ζ‖}.indicator (fun ζ => (‖ζ‖ ^ 2)⁻¹) ζ * ‖ζ - w‖⁻¹) * ‖z‖ ^ 2 := by
        have hI0 : 0 ≤ ∫ ζ, {ζ : ℂ | ε ≤ ‖ζ‖}.indicator (fun ζ => (‖ζ‖ ^ 2)⁻¹) ζ * ‖ζ - w‖⁻¹ :=
          integral_nonneg fun ζ => mul_nonneg (hv0 ζ) (inv_nonneg.mpr (norm_nonneg _))
        have hw2 : ‖w‖ ^ 2 ≤ K ^ 2 * ‖z‖ ^ 2 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hgz 2
        nlinarith [mul_le_mul_of_nonneg_left hw2 (mul_nonneg hM0 hI0)]

/-- Integrability is preserved by `σ ↦ c σ`, `c ≠ 0`. -/
theorem s3dv_int_mul {f : ℂ → ℂ} (hf : Integrable f) {c : ℂ} (hc : c ≠ 0) :
    Integrable (fun σ : ℂ => f (c * σ)) := by
  let L : ℂ →ₗ[ℝ] ℂ := Algebra.lmul ℝ ℂ c
  have hdet : LinearMap.det L ≠ 0 := by
    rw [← Algebra.norm_apply]
    exact Algebra.norm_ne_zero_iff.mpr hc
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ℂ)) hdet
  have hL : Measurable L := L.continuous_of_finiteDimensional.measurable
  have h1 : Integrable f (Measure.map L volume) := by
    rw [hmap]; exact hf.smul_measure ENNReal.ofReal_ne_top
  have h2 := (integrable_map_measure h1.aestronglyMeasurable hL.aemeasurable).mp h1
  exact h2

/-- The model integrable kernel `1/(σ(σ - a)(σ - b))` (a scaled `ahKer`). -/
theorem s3dv_int_model {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Integrable (fun σ : ℂ => 1 / (σ * (σ - a) * (σ - b))) := by
  have hw : b / a ≠ 0 := div_ne_zero hb ha
  have hw1 : b / a - 1 ≠ 0 := by
    rw [div_sub_one ha]; exact div_ne_zero (sub_ne_zero.mpr hab.symm) ha
  have h := (s3dv_int_mul (ah_ker_integrable (b / a)) (inv_ne_zero ha)).const_mul
    (1 / (b / a * (b / a - 1) * a ^ 3))
  refine h.congr ?_
  have hS : ({0, a, b} : Set ℂ).Countable := (Set.toFinite _).countable
  filter_upwards [hS.ae_notMem volume] with σ hσ
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hσ
  obtain ⟨h0, h1, h2⟩ := hσ
  have h1' : σ - a ≠ 0 := sub_ne_zero.mpr h1
  have h2' : σ - b ≠ 0 := sub_ne_zero.mpr h2
  unfold ahKer
  have e1 : a⁻¹ * σ - 1 = (σ - a) / a := by field_simp
  have e2 : a⁻¹ * σ - b / a = (σ - b) / a := by field_simp
  rw [e1, e2]
  field_simp


/-- Second-order Taylor remainder of a bounded holomorphic function, by two Schwarz-lemma steps:
`‖F t - F 0 - t F'(0)‖ ≤ 4C ‖t‖² / ρ²` on `ball 0 ρ`. The constant depends only on `ρ` and the bound `C`. -/
theorem s3dv_taylor {F : ℂ → ℂ} {ρ C : ℝ} (hρ : 0 < ρ) (hF : DifferentiableOn ℂ F (ball 0 ρ))
    (hC : ∀ s ∈ ball (0 : ℂ) ρ, ‖F s‖ ≤ C) {t : ℂ} (ht : t ∈ ball (0 : ℂ) ρ) :
    ‖F t - F 0 - t * deriv F 0‖ ≤ 4 * C / ρ ^ 2 * ‖t‖ ^ 2 := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ρ := mem_ball_self hρ
  have hG : DifferentiableOn ℂ (dslope F 0) (ball 0 ρ) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds h0)).2 hF
  have hmapF : MapsTo F (ball 0 ρ) (closedBall (F 0) (2 * C)) := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm]
    calc ‖F s - F 0‖ ≤ ‖F s‖ + ‖F 0‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hC s hs) (hC 0 h0)
      _ = 2 * C := by ring
  have hGb : ∀ s ∈ ball (0 : ℂ) ρ, ‖dslope F 0 s‖ ≤ 2 * C / ρ := fun s hs =>
    norm_dslope_le_div_of_mapsTo_ball hF hmapF hs
  have hmapG : MapsTo (dslope F 0) (ball 0 ρ) (closedBall (dslope F 0 0) (4 * C / ρ)) := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm]
    calc ‖dslope F 0 s - dslope F 0 0‖ ≤ ‖dslope F 0 s‖ + ‖dslope F 0 0‖ := norm_sub_le _ _
      _ ≤ 2 * C / ρ + 2 * C / ρ := add_le_add (hGb s hs) (hGb 0 h0)
      _ = 4 * C / ρ := by ring
  have hH : ‖dslope (dslope F 0) 0 t‖ ≤ 4 * C / ρ / ρ := norm_dslope_le_div_of_mapsTo_ball hG hmapG ht
  have e1 := sub_smul_dslope F 0 t
  have e2 := sub_smul_dslope (dslope F 0) 0 t
  rw [dslope_same] at e2
  simp only [sub_zero, smul_eq_mul] at e1 e2
  have key : F t - F 0 - t * deriv F 0 = t * t * dslope (dslope F 0) 0 t := by
    rw [← e1, mul_assoc, e2]; ring
  rw [key, norm_mul, norm_mul]
  calc ‖t‖ * ‖t‖ * ‖dslope (dslope F 0) 0 t‖ ≤ ‖t‖ * ‖t‖ * (4 * C / ρ / ρ) :=
        mul_le_mul_of_nonneg_left hH (by positivity)
    _ = 4 * C / ρ ^ 2 * ‖t‖ ^ 2 := by ring

/-- `s3dv_taylor` on a ball of any complex normed space, along the complex line through `p`:
`‖F p - F 0 - F'(0) p‖ ≤ 4C ‖p‖² / ρ²`. -/
theorem s3dv_taylorE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : E → ℂ} {ρ C : ℝ} (hρ : 0 < ρ)
    (hF : DifferentiableOn ℂ F (ball 0 ρ)) (hC : ∀ v ∈ ball (0 : E) ρ, ‖F v‖ ≤ C) {p : E}
    (hp : p ∈ ball (0 : E) ρ) :
    ‖F p - F 0 - fderiv ℂ F 0 p‖ ≤ 4 * C / ρ ^ 2 * ‖p‖ ^ 2 := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  set e : E := (‖p‖⁻¹ : ℂ) • p with he
  have hen : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm, inv_mul_cancel₀ hn.ne']
  have hmap : ∀ τ ∈ ball (0 : ℂ) ρ, τ • e ∈ ball (0 : E) ρ := fun τ hτ => by
    rw [mem_ball_zero_iff, norm_smul, hen, mul_one]; exact mem_ball_zero_iff.mp hτ
  have hG : DifferentiableOn ℂ (fun τ : ℂ => F (τ • e)) (ball 0 ρ) :=
    hF.comp (differentiable_id.smul_const e).differentiableOn hmap
  have hpn : ((‖p‖ : ℝ) : ℂ) ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_norm]; exact mem_ball_zero_iff.mp hp
  have h := s3dv_taylor hρ hG (fun τ hτ => hC _ (hmap τ hτ)) hpn
  have hpe : ((‖p‖ : ℝ) : ℂ) • e = p := by
    rw [he, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  have h0 : (0 : ℂ) • e = 0 := zero_smul _ _
  have hd : deriv (fun τ : ℂ => F (τ • e)) 0 = fderiv ℂ F 0 e := by
    have hF0 : DifferentiableAt ℂ F 0 := hF.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρ))
    have hl : HasDerivAt (fun τ : ℂ => τ • e) e 0 := by simpa using (hasDerivAt_id (0 : ℂ)).smul_const e
    have hF0' : HasFDerivAt F (fderiv ℂ F 0) ((0 : ℂ) • e) := by rw [h0]; exact hF0.hasFDerivAt
    exact (hF0'.comp_hasDerivAt (0 : ℂ) hl).deriv
  rw [hd, hpe, h0, Complex.norm_real, Real.norm_eq_abs, abs_norm] at h
  have hlin : ((‖p‖ : ℝ) : ℂ) * fderiv ℂ F 0 e = fderiv ℂ F 0 p := by
    have he' : fderiv ℂ F 0 e = ((‖p‖ : ℝ) : ℂ)⁻¹ * fderiv ℂ F 0 p := by rw [he, map_smul, smul_eq_mul]
    rw [he', ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_mul]
  rw [hlin] at h
  exact h

/-- Model B on `𝔻` through the plane solution: `𝖿 = W/(d (1 - P W))`, with `W = W_{extB μ}`, `d = W'(0)` and
`P = 1/W(p)` the reciprocal pole (`acc_wB_rep`, `s35wn_pole`). -/
theorem s3dv_frep {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * normalizedSolution (extB μ) z ≠ 0 ∧
    fsans μ z = normalizedSolution (extB μ) z / (deriv (normalizedSolution (extB μ)) 0 *
      (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * normalizedSolution (extB μ) z)) := by
  obtain ⟨hd, -, hrep⟩ := AppA.acc_wB_rep hμ
  have hP := s35wn_pole hμ
  obtain ⟨-, -, -, -, -, -, f, hf, -⟩ := (wB_spec hμ).1
  set W := normalizedSolution (extB μ) with hW
  set P := s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) with hPdef
  have h1 := hrep (z : ExtPlane)
  rw [OnePoint.map_some] at h1
  have hP' : finPart (mobiusExt 0 1 1 0 (OnePoint.map W (Function.invFun (wAS μ) extInf))) = P := hP
  rw [hP'] at h1
  have hden : -P * W z + 1 ≠ 0 := by
    intro h0
    rw [mobiusExt_coe_of_eq_zero h0, hf z hz] at h1
    exact OnePoint.coe_ne_infty _ h1
  have hden' : 1 - P * W z ≠ 0 := by
    intro h0; apply hden; linear_combination h0
  refine ⟨hden', ?_⟩
  rw [S2C.s2c_fsans_eq hμ]
  show finPart (wB μ (z : ExtPlane)) = _
  rw [h1, mobiusExt_coe hden, finPart_coe]
  simp only [mobiusFn]
  rw [div_eq_div_iff hden (mul_ne_zero hd hden')]
  field_simp
  ring

/-- Uniform Taylor bound for a family holomorphic in `t`, jointly continuous on `closedBall 0 (ρ/2) × K` with
`K` compact: `‖F t y - F 0 y - t ∂_t F(0, y)‖ ≤ C ‖t‖²` on `ball 0 (ρ/2) × K`. -/
theorem s3dv_taylor_unif {X : Type*} [TopologicalSpace X] {F : ℂ → X → ℂ} {K : Set X} (hK : IsCompact K)
    {ρ : ℝ} (hρ : 0 < ρ) (hF : ∀ y ∈ K, DifferentiableOn ℂ (fun t => F t y) (ball 0 ρ))
    (hc : ContinuousOn (fun q : ℂ × X => F q.1 q.2) (closedBall (0 : ℂ) (ρ / 2) ×ˢ K)) :
    ∃ C : ℝ, ∀ t ∈ ball (0 : ℂ) (ρ / 2), ∀ y ∈ K,
      ‖F t y - F 0 y - t * deriv (fun s => F s y) 0‖ ≤ C * ‖t‖ ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := ((isCompact_closedBall (0 : ℂ) (ρ / 2)).prod hK).exists_bound_of_continuousOn hc
  refine ⟨4 * C₀ / (ρ / 2) ^ 2, fun t ht y hy => ?_⟩
  have hρ2 : 0 < ρ / 2 := half_pos hρ
  have hd : DifferentiableOn ℂ (fun t => F t y) (ball 0 (ρ / 2)) :=
    (hF y hy).mono (ball_subset_ball (by linarith))
  exact s3dv_taylor hρ2 hd (fun s hs => hC₀ (s, y) ⟨ball_subset_closedBall hs, hy⟩) ht

/-- The plane solution along a holomorphic curve `c` of Beltrami coefficients: uniform Taylor bound on
compact sets of `ℂ`. -/
theorem s3dv_W_taylor {c : ℂ → LinfStar} {ρ : ℝ} (hρ : 0 < ρ) (hc : DifferentiableOn ℂ c (ball 0 ρ))
    (hcm : MapsTo c (ball 0 ρ) LinfStarBall) {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ t ∈ ball (0 : ℂ) (ρ / 2), ∀ y ∈ K,
      ‖normalizedSolution (extB (c t)) y - normalizedSolution (extB (c 0)) y -
        t * deriv (fun s => normalizedSolution (extB (c s)) y) 0‖ ≤ C * ‖t‖ ^ 2 := by
  have hsub : closedBall (0 : ℂ) (ρ / 2) ⊆ ball 0 ρ := closedBall_subset_ball (by linarith)
  have hd : ∀ y ∈ K, DifferentiableOn ℂ (fun t => normalizedSolution (extB (c t)) y) (ball 0 ρ) :=
    fun y _ => (QCV.qcv_planeB_differentiableOn y).comp hc hcm
  have hcc : ContinuousOn c (closedBall (0 : ℂ) (ρ / 2)) := hc.continuousOn.mono hsub
  have hpair : ContinuousOn (fun q : ℂ × ℂ => (c q.1, q.2)) (closedBall (0 : ℂ) (ρ / 2) ×ˢ K) :=
    (hcc.comp continuousOn_fst fun q hq => hq.1).prodMk continuousOn_snd
  have hmap : MapsTo (fun q : ℂ × ℂ => (c q.1, q.2)) (closedBall (0 : ℂ) (ρ / 2) ×ˢ K)
      (ball (0 : LinfStar) 1 ×ˢ univ) := fun q hq =>
    ⟨hcm (hsub hq.1), mem_univ _⟩
  have hcont : ContinuousOn (fun q : ℂ × ℂ => normalizedSolution (extB (c q.1)) q.2)
      (closedBall (0 : ℂ) (ρ / 2) ×ˢ K) :=
    (s5cf_planeB_cont.comp hpair hmap).congr fun q _ => rfl
  exact s3dv_taylor_unif (F := fun t y => normalizedSolution (extB (c t)) y) hK hρ hd hcont

/-- The Ahlfors–Bers kernel (nodes `0, 1, ∞`) transported by `Φ(w) = w/(d(1 - P w))` to the f-plane:
with `A = d(1 - P)`, `B = P d`, `N(σ) = σ(1 + Bσ)(Aσ - 1)`, `w = Φ⁻¹ ζ`, `s = Φ⁻¹ σ`:
`Φ'(w) K(w, s)/Φ'(s)² = k(ζ, σ) - ζ/(σ N(σ)) - AB ζ²/N(σ)`, with `k = 1/(σ - ζ) - 1/σ - ζ/σ²`. -/
theorem s3dv_kernel_f {d P ζ σ : ℂ} (hd : d ≠ 0) (hζ : 1 + P * d * ζ ≠ 0) (hσ : 1 + P * d * σ ≠ 0)
    (hσ0 : σ ≠ 0) (hσ1 : d * (1 - P) * σ - 1 ≠ 0) (hσζ : σ - ζ ≠ 0) :
    (1 + P * d * ζ) ^ 2 / d * ahKer (d * ζ / (1 + P * d * ζ)) (d * σ / (1 + P * d * σ)) *
        (d / (1 + P * d * σ) ^ 2) ^ 2 =
      1 / (σ - ζ) - 1 / σ - ζ / σ ^ 2 - ζ / (σ * (σ * (1 + P * d * σ) * (d * (1 - P) * σ - 1))) -
        d * (1 - P) * (P * d) * ζ ^ 2 / (σ * (1 + P * d * σ) * (d * (1 - P) * σ - 1)) := by
  have e1 : d * σ / (1 + P * d * σ) - 1 = (d * (1 - P) * σ - 1) / (1 + P * d * σ) := by
    rw [div_sub_one hσ]; congr 1; ring
  have e2 : d * σ / (1 + P * d * σ) - d * ζ / (1 + P * d * ζ) =
      d * (σ - ζ) / ((1 + P * d * σ) * (1 + P * d * ζ)) := by
    rw [div_sub_div _ _ hσ hζ]; congr 1; ring
  have e3 : d * ζ / (1 + P * d * ζ) - 1 = (d * (1 - P) * ζ - 1) / (1 + P * d * ζ) := by
    rw [div_sub_one hζ]; congr 1; ring
  unfold ahKer
  rw [e1, e2, e3]
  obtain ⟨u, hu⟩ : ∃ u, u = 1 + P * d * σ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = 1 + P * d * ζ := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = d * (1 - P) * σ - 1 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = σ - ζ := ⟨_, rfl⟩
  rw [← hu, ← hv, ← hq, ← hr]
  rw [← hu] at hσ; rw [← hv] at hζ; rw [← hq] at hσ1; rw [← hr] at hσζ
  field_simp
  rw [hu, hv, hq, hr]
  ring

/-- The first variation of the plane solution along the off-centre line, in source coordinates:
`∂_t W_{ν_t}(y)|₀ = -(1/π) ∫_{𝔻*} ν̇ K(W₀ y, W₀ x) (∂W₀)²`, with `ν̇ = D(l ↦ l * κ)(a) m'`. -/
theorem s3dv_Wdot {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (m' : LinfStar) (y : ℂ) :
    HasDerivAt (fun t : ℂ => normalizedSolution (extB (beltramiMul (a + t • m') κ)) y)
      (-(1 / π : ℂ) * ∫ x in unitDiscExterior, fderiv ℂ (fun l => beltramiMul l κ) a m' x *
        ahKer (normalizedSolution (extB (beltramiMul a κ)) y) (normalizedSolution (extB (beltramiMul a κ)) x) *
          dz (normalizedSolution (extB (beltramiMul a κ))) x ^ 2) 0 := by
  have hν₀ : beltramiMul a κ ∈ LinfStarBall := bg_mul_mem_ball hκ ha
  have hk : ‖beltramiMul a κ‖ < 1 := mem_ball_zero_iff.mp hν₀
  obtain ⟨L, hL, hd⟩ := QCV.qcv_planeSolution_base_hasFDerivAt hν₀ y
  have hD : HasFDerivAt (fun l => beltramiMul l κ) (fderiv ℂ (fun l => beltramiMul l κ) a) a :=
    ((bd_differentiableOn hκ a ha).differentiableAt (isOpen_ball.mem_nhds ha)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℂ => a + t • m') m' 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const m').const_add a
  have hD' : HasFDerivAt (fun l => beltramiMul l κ) (fderiv ℂ (fun l => beltramiMul l κ) a)
      (a + (0 : ℂ) • m') := by rw [zero_smul, add_zero]; exact hD
  have hc := hD'.comp_hasDerivAt (0 : ℂ) hl
  have hδ : HasDerivAt (fun t : ℂ => beltramiMul (a + t • m') κ - beltramiMul a κ)
      (fderiv ℂ (fun l => beltramiMul l κ) a m') 0 := by
    simpa using hc.sub_const (beltramiMul a κ)
  have hδ0 : (fun t : ℂ => beltramiMul (a + t • m') κ - beltramiMul a κ) 0 = 0 := by simp
  have hd' : HasFDerivAt (fun v => QCV.qcv_planeSolution (beltramiMul a κ + v) y) L
      ((fun t : ℂ => beltramiMul (a + t • m') κ - beltramiMul a κ) 0) := by rw [hδ0]; exact hd
  have hcomp := hd'.comp_hasDerivAt (0 : ℂ) hδ
  have hfun : ((fun v => QCV.qcv_planeSolution (beltramiMul a κ + v) y) ∘
      fun t : ℂ => beltramiMul (a + t • m') κ - beltramiMul a κ) =
      fun t : ℂ => normalizedSolution (extB (beltramiMul (a + t • m') κ)) y := by
    funext t
    simp only [Function.comp_apply, add_sub_cancel]
    rfl
  rw [hfun] at hcomp
  refine hcomp.congr_deriv ?_
  rw [hL]
  change ahVar (ahT_dot (extB (fderiv ℂ (fun l => beltramiMul l κ) a m')) (extB (beltramiMul a κ))
    (normalizedSolution (extB (beltramiMul a κ)))) (normalizedSolution (extB (beltramiMul a κ)) y) = _
  rw [QCV.qcv_var_source (norm_nonneg _) hk (extB_isBeltramiCoeff _) (QCV.qcv_W_props hk).1
    (extB_isBeltramiCoeff _)]
  congr 1
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [← integral_indicator hE]
  congr 1
  funext x
  by_cases hx : x ∈ unitDiscExterior
  · simp only [extB, indicator_of_mem hx]
  · simp only [extB, indicator_of_notMem hx, zero_mul]

/-- Model B on `𝔻*`, off the pole of `w_μ`: `𝗀 ∘ w_μ = Φ ∘ W` with the same `Φ(w) = w/(d(1 - P w))` as on `𝔻`
(`acc_wB_rep`, `gMu_sphere_factorization`), written in the Möbius form of `S2C.s2c_dz_mobius`. -/
theorem s3dv_grep {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {x : ℂ} (hx : x ∈ unitDiscExterior)
    (hpole : wAS μ (x : ExtPlane) ≠ extInf) :
    -s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * normalizedSolution (extB μ) x + 1 ≠ 0 ∧
    gsans μ (wA μ x) = (1 / deriv (normalizedSolution (extB μ)) 0 * normalizedSolution (extB μ) x + 0) /
      (-s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * normalizedSolution (extB μ) x + 1) := by
  obtain ⟨-, -, hrep⟩ := AppA.acc_wB_rep hμ
  have hP' : finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB μ))
      (Function.invFun (wAS μ) extInf))) = s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) :=
    s35wn_pole hμ
  have hx1 : 1 < ‖x‖ := by simpa [unitDiscExterior] using hx
  rcases wAS_maps_ext hμ hx1 with h | ⟨u, hu, hu'⟩
  · exact absurd h hpole
  have hwA : wA μ x = u := by
    show finPart (wAS μ (x : ExtPlane)) = u
    rw [hu', finPart_coe]
  have hinv : Function.invFun (wAS μ) (u : ExtPlane) = (x : ExtPlane) := by
    rw [← hu']
    exact Function.leftInverse_invFun (wAS_bijective μ).1 _
  have hxu : u ∈ unitDiscExterior := by simpa [unitDiscExterior] using hu
  have hfac := gMu_sphere_factorization hμ hxu
  rw [hinv, hrep, OnePoint.map_some, hP'] at hfac
  have hden : -s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * normalizedSolution (extB μ) x + 1 ≠ 0 := by
    intro he
    rw [mobiusExt_coe_of_eq_zero he] at hfac
    exact OnePoint.infty_ne_coe _ hfac.symm
  rw [mobiusExt_coe hden] at hfac
  refine ⟨hden, ?_⟩
  rw [S2C.s2c_gsans_eq hμ, hwA, OnePoint.coe_injective hfac]
  rfl

/-- Möbius algebra for `Φ(w) = w/(d(1 - Pw))` used in `s3dv_transport`. -/
theorem s3dv_mob_alg {d P w : ℂ} (hd : d ≠ 0) (h1 : 1 - P * w ≠ 0) :
    (1 / d * w + 0) / (-P * w + 1) = w / (d * (1 - P * w)) ∧
    d * (w / (d * (1 - P * w))) / (1 + P * d * (w / (d * (1 - P * w)))) = w ∧
    ∀ X Y Z : ℂ, X * ((1 / d * 1 - 0 * -P) / (-P * w + 1) ^ 2 * Y) ^ 2 * (Z * (d * (1 - P * w) ^ 2) ^ 2) =
      X * Y ^ 2 * Z := by
  have hm : -P * w + 1 = 1 - P * w := by ring
  obtain ⟨u, hu⟩ : ∃ u, u = 1 - P * w := ⟨_, rfl⟩
  rw [hm, ← hu]
  rw [← hu] at h1
  have hPw : P * w = 1 - u := by rw [hu]; ring
  refine ⟨?_, ?_, fun X Y Z => ?_⟩
  · field_simp; ring
  · have e : 1 + P * d * (w / (d * u)) = 1 / u := by
      rw [show P * d * (w / (d * u)) = (P * w) / u by field_simp, hPw]
      field_simp; ring
    rw [e]; field_simp
  · field_simp; ring

/-- Transport of a source-coordinate integral on `𝔻*` to the `𝗀`-plane: with `Φ(w) = w/(d(1 - Pw))`,
`Φ⁻¹(σ) = dσ/(1 + Pdσ)` and `1/Φ'(s)² = (d(1 - Ps)²)²`,
`∫ D_μ θ (∂W)² F(W) = ∫ θ g'² · F(Φ⁻¹ g) (d(1 - P Φ⁻¹ g)²)²` (`S2C.s2c_cov_var`). -/
theorem s3dv_transport {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (θ : LinfStar) {F : ℂ → ℂ} (hF : Measurable F) :
    ∫ x in unitDiscExterior, QCV.qcv_rightDerivative μ θ x * dz (normalizedSolution (extB μ)) x ^ 2 *
        F (normalizedSolution (extB μ) x) =
      ∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
        (F (deriv (normalizedSolution (extB μ)) 0 * gsans μ ξ /
            (1 + s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) *
              deriv (normalizedSolution (extB μ)) 0 * gsans μ ξ)) *
          (deriv (normalizedSolution (extB μ)) 0 *
            (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) *
              (deriv (normalizedSolution (extB μ)) 0 * gsans μ ξ /
                (1 + s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) *
                  deriv (normalizedSolution (extB μ)) 0 * gsans μ ξ))) ^ 2) ^ 2) := by
  set W := normalizedSolution (extB μ) with hW
  set d := deriv W 0 with hd
  set P := s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) with hP
  have hd0 : d ≠ 0 := (AppA.acc_wB_rep hμ).1
  have hk := bc_norm_lt_one hμ
  have hKm : Measurable fun σ : ℂ => F (d * σ / (1 + P * d * σ)) * (d * (1 - P * (d * σ / (1 + P * d * σ))) ^ 2) ^ 2 :=
    (hF.comp (by fun_prop)).mul (by fun_prop)
  rw [← S2C.s2c_cov_var hμ θ _ hKm]
  have hVo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  refine setIntegral_congr_ae hVo.measurableSet ?_
  have hdiffW : ∀ᵐ x : ℂ, DifferentiableAt ℝ W x := by
    obtain ⟨⟨KW, hKW⟩, -⟩ := (QCV.qcv_W_props hk).1
    have h := s23_c2_ae_good hKW
    rw [Measure.restrict_univ] at h
    filter_upwards [h] with x hx using hx.1
  have hpole : ∀ᵐ x : ℂ, wAS μ (x : ExtPlane) ≠ extInf :=
    measure_eq_zero_iff_ae_notMem.mp ((S2C.s2c_pole_subsingleton μ).measure_zero volume)
  filter_upwards [hdiffW, hpole] with x hdx hpx hx
  obtain ⟨hden, hg⟩ := s3dv_grep hμ hx hpx
  have hZ : ∀ᶠ y in 𝓝 x, gsans μ (wA μ y) =
      (1 / d * QCV.qcv_planeSolution μ y + 0) / (-P * QCV.qcv_planeSolution μ y + 1) := by
    filter_upwards [hVo.mem_nhds hx, (S2C.s2c_pole_open μ).mem_nhds hpx] with y hy hpy
    exact (s3dv_grep hμ hy hpy).2
  have hdz := S2C.s2c_dz_mobius hZ hden hdx
  have hq : QCV.qcv_planeSolution μ = W := rfl
  rw [hq] at hdz
  rw [hdz, hg]
  simp only [← hW, ← hd, ← hP]
  obtain ⟨w, hw⟩ : ∃ w, w = W x := ⟨_, rfl⟩
  rw [← hw]
  have hden' : -P * w + 1 ≠ 0 := by rw [hw]; exact hden
  have h1 : 1 - P * w ≠ 0 := by intro h; apply hden'; linear_combination h
  obtain ⟨e1, e2, e3⟩ := s3dv_mob_alg hd0 h1
  rw [e1, e2, e3]

/-- `𝗀_μ(𝔻*)` stays at positive distance from `0` (`s3d5_lower`). -/
theorem s3dv_g_region {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ ∈ unitDiscExterior, ε ≤ ‖gsans μ ξ‖ := by
  obtain ⟨ε, hε, -, h⟩ := s3d5_lower hμ
  refine ⟨ε, hε, fun ξ hξ => ?_⟩
  rw [S2C.s2c_gsans_eq hμ, gMu_eq_normalizedWeldingExterior hμ hξ]
  exact h ξ (le_of_lt hξ)

/-- Integrability transfer to the `𝗀`-plane: if `h` is integrable on `𝗀(𝔻*)` and `R` is bounded, then
`R g'² h(g)` is integrable on `𝔻*` (`ahP_integrableOn_image`). -/
theorem s3dv_int_transfer {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {R : ℂ → ℂ} {M : ℝ}
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ M) {h : ℂ → ℂ}
    (hh : IntegrableOn h (gsans μ '' unitDiscExterior)) :
    IntegrableOn (fun ξ => R ξ * deriv (gsans μ) ξ ^ 2 * h (gsans μ ξ)) unitDiscExterior := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hconf := S2C.s2c_conf_g hμ
  have h1 := (ahP_integrableOn_image hEo hconf.1 hconf.2.1 h).mp hh
  have hdm : Measurable (deriv (gsans μ)) := measurable_deriv _
  have hfm : AEStronglyMeasurable (fun ξ => R ξ * deriv (gsans μ) ξ ^ 2 / ((‖deriv (gsans μ) ξ‖ ^ 2 : ℝ) : ℂ))
      (volume.restrict unitDiscExterior) := by
    have hq : Measurable (fun ξ => deriv (gsans μ) ξ ^ 2 / ((‖deriv (gsans μ) ξ‖ ^ 2 : ℝ) : ℂ)) :=
      (hdm.pow_const 2).div (Complex.measurable_ofReal.comp (hdm.norm.pow_const 2))
    exact (hRm.mul hq.aestronglyMeasurable).congr (ae_of_all _ fun ξ => (mul_div_assoc _ _ _).symm)
  have hb : ∀ᵐ ξ ∂(volume.restrict unitDiscExterior),
      ‖R ξ * deriv (gsans μ) ξ ^ 2 / ((‖deriv (gsans μ) ξ‖ ^ 2 : ℝ) : ℂ)‖ ≤ M := by
    filter_upwards [hRb] with ξ hξ
    by_cases h0 : deriv (gsans μ) ξ = 0
    · simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div, norm_zero]
      exact (norm_nonneg _).trans hξ
    · rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        mul_div_assoc, div_self (by positivity), mul_one]
      exact hξ
  refine (h1.bdd_mul hfm hb).congr ?_
  filter_upwards [] with ξ
  by_cases h0 : deriv (gsans μ) ξ = 0
  · simp [h0]
  · have hn : ((‖deriv (gsans μ) ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : 0 < ‖deriv (gsans μ) ξ‖ := norm_pos_iff.mpr h0
      exact_mod_cast (by positivity : (0 : ℝ) < ‖deriv (gsans μ) ξ‖ ^ 2).ne'
    simp only [Complex.real_smul]
    field_simp

/-- Domination by the model kernel gives integrability on a measurable set. -/
theorem s3dv_int_dom {f : ℂ → ℂ} {S : Set ℂ} {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) {C : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict S))
    (h : ∀ᵐ σ ∂(volume.restrict S), ‖f σ‖ ≤ C * ‖1 / (σ * (σ - a) * (σ - b))‖) : IntegrableOn f S :=
  Integrable.mono' ((s3dv_int_model ha hb hab).integrableOn.norm.const_mul C) hf h

/-- On `{ε ≤ ‖σ‖}`: `‖(σ - p)/σ‖ ≤ 1 + ‖p‖/ε`. -/
theorem s3dv_ratio_le {ε : ℝ} (hε : 0 < ε) {σ p : ℂ} (hσ : ε ≤ ‖σ‖) : ‖(σ - p) / σ‖ ≤ 1 + ‖p‖ / ε := by
  have hσ0 : 0 < ‖σ‖ := lt_of_lt_of_le hε hσ
  rw [norm_div, div_le_iff₀ hσ0]
  calc ‖σ - p‖ ≤ ‖σ‖ + ‖p‖ := norm_sub_le _ _
    _ ≤ ‖σ‖ + ‖p‖ / ε * ‖σ‖ := by
        have : ‖p‖ ≤ ‖p‖ / ε * ‖σ‖ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hε]; exact mul_le_mul_of_nonneg_left hσ (norm_nonneg _)
        linarith
    _ = (1 + ‖p‖ / ε) * ‖σ‖ := by ring

/-- The `V̇` kernel `k(ζ, σ) = 1/(σ - ζ) - 1/σ - ζ/σ²` is integrable on `{ε ≤ ‖σ‖}`. -/
theorem s3dv_int_k {ε : ℝ} (hε : 0 < ε) (ζ : ℂ) :
    IntegrableOn (fun σ : ℂ => 1 / (σ - ζ) - 1 / σ - ζ / σ ^ 2) {σ : ℂ | ε ≤ ‖σ‖} := by
  have hS : MeasurableSet {σ : ℂ | ε ≤ ‖σ‖} := measurableSet_le measurable_const measurable_norm
  have hm : AEStronglyMeasurable (fun σ : ℂ => 1 / (σ - ζ) - 1 / σ - ζ / σ ^ 2) (volume.restrict {σ : ℂ | ε ≤ ‖σ‖}) :=
    (by fun_prop : Measurable fun σ : ℂ => 1 / (σ - ζ) - 1 / σ - ζ / σ ^ 2).aestronglyMeasurable
  rcases eq_or_ne ζ 0 with rfl | hζ
  · exact (integrableOn_zero).congr_fun (fun σ _ => by simp) hS
  have h2 : (2 : ℂ) * ζ ≠ 0 := mul_ne_zero two_ne_zero hζ
  have h12 : ζ ≠ 2 * ζ := fun h => hζ (by linear_combination -h)
  refine s3dv_int_dom hζ h2 h12 (C := ‖ζ‖ ^ 2 * (1 + ‖2 * ζ‖ / ε)) hm ?_
  have hF : ({ζ, 2 * ζ} : Set ℂ).Countable := (Set.toFinite _).countable
  filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (hF.ae_notMem volume)] with σ hσ hσF
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hσF
  obtain ⟨h1, h2'⟩ := hσF
  have hσ : ε ≤ ‖σ‖ := hσ
  have hσ0 : σ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hε hσ)
  have e : 1 / (σ - ζ) - 1 / σ - ζ / σ ^ 2 = ζ ^ 2 * ((σ - 2 * ζ) / σ) * (1 / (σ * (σ - ζ) * (σ - 2 * ζ))) := by
    have h3 : σ - ζ * 2 ≠ 0 := by rw [mul_comm]; exact sub_ne_zero.mpr h2'
    field_simp [sub_ne_zero.mpr h1, sub_ne_zero.mpr h2', h3]
    ring
  rw [e, norm_mul, norm_mul, norm_pow]
  gcongr
  exact s3dv_ratio_le hε hσ

/-- `AB/N(σ)`, `N(σ) = σ(1 + Bσ)(Aσ - 1)`, is integrable on `{ε ≤ ‖σ‖}` (it vanishes when `AB = 0`). -/
theorem s3dv_int_N2 {ε : ℝ} (hε : 0 < ε) {A B : ℂ} (hAB : A + B ≠ 0) :
    IntegrableOn (fun σ : ℂ => A * B / (σ * (1 + B * σ) * (A * σ - 1))) {σ : ℂ | ε ≤ ‖σ‖} := by
  have hS : MeasurableSet {σ : ℂ | ε ≤ ‖σ‖} := measurableSet_le measurable_const measurable_norm
  rcases eq_or_ne A 0 with rfl | hA
  · exact (integrableOn_zero).congr_fun (fun σ _ => by simp) hS
  rcases eq_or_ne B 0 with rfl | hB
  · exact (integrableOn_zero).congr_fun (fun σ _ => by simp) hS
  have ha : -1 / B ≠ 0 := div_ne_zero (neg_ne_zero.mpr one_ne_zero) hB
  have hb : 1 / A ≠ 0 := one_div_ne_zero hA
  have hab : -1 / B ≠ 1 / A := by
    intro h
    rw [div_eq_div_iff hB hA] at h
    exact hAB (by linear_combination -h)
  refine s3dv_int_dom ha hb hab (C := 1)
    (by fun_prop : Measurable fun σ : ℂ => A * B / (σ * (1 + B * σ) * (A * σ - 1))).aestronglyMeasurable ?_
  have hF : ({-1 / B, 1 / A} : Set ℂ).Countable := (Set.toFinite _).countable
  filter_upwards [ae_restrict_of_ae (hF.ae_notMem volume)] with σ hσF
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hσF
  obtain ⟨h1, h2⟩ := hσF
  rw [one_mul]
  apply le_of_eq
  congr 1
  have e1 : 1 + B * σ = B * (σ - -1 / B) := by field_simp; ring
  have e2 : A * σ - 1 = A * (σ - 1 / A) := by field_simp
  rw [e1, e2]
  field_simp

/-- `1/(σ N(σ))` is integrable on `{ε ≤ ‖σ‖}` when `A + B ≠ 0`. -/
theorem s3dv_int_N1 {ε : ℝ} (hε : 0 < ε) {A B : ℂ} (hAB : A + B ≠ 0) :
    IntegrableOn (fun σ : ℂ => 1 / (σ * (σ * (1 + B * σ) * (A * σ - 1)))) {σ : ℂ | ε ≤ ‖σ‖} := by
  have hS : MeasurableSet {σ : ℂ | ε ≤ ‖σ‖} := measurableSet_le measurable_const measurable_norm
  have hm : AEStronglyMeasurable (fun σ : ℂ => 1 / (σ * (σ * (1 + B * σ) * (A * σ - 1))))
      (volume.restrict {σ : ℂ | ε ≤ ‖σ‖}) :=
    (by fun_prop : Measurable fun σ : ℂ => 1 / (σ * (σ * (1 + B * σ) * (A * σ - 1)))).aestronglyMeasurable
  rcases eq_or_ne A 0 with rfl | hA
  · have hB : B ≠ 0 := by simpa using hAB
    have ha : -1 / B ≠ 0 := div_ne_zero (neg_ne_zero.mpr one_ne_zero) hB
    have hb : -2 / B ≠ 0 := div_ne_zero (by norm_num) hB
    have hab : -1 / B ≠ -2 / B := by
      intro h; rw [div_eq_div_iff hB hB] at h; apply hB; linear_combination h
    refine s3dv_int_dom ha hb hab (C := ‖-1 / B‖ * (1 + ‖-2 / B‖ / ε)) hm ?_
    have hF : ({-1 / B, -2 / B} : Set ℂ).Countable := (Set.toFinite _).countable
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (hF.ae_notMem volume)] with σ hσ hσF
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hσF
    obtain ⟨h1, h2⟩ := hσF
    have hσ : ε ≤ ‖σ‖ := hσ
    have hσ0 : σ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hε hσ)
    have e : 1 / (σ * (σ * (1 + B * σ) * (0 * σ - 1))) =
        -1 / B * ((σ - -2 / B) / σ) * (1 / (σ * (σ - -1 / B) * (σ - -2 / B))) := by
      have e1 : 1 + B * σ = B * (σ - -1 / B) := by field_simp; ring
      rw [e1]
      have h1' : σ - -1 / B ≠ 0 := sub_ne_zero.mpr h1
      have h2' : σ - -2 / B ≠ 0 := sub_ne_zero.mpr h2
      generalize σ - -1 / B = u at h1' ⊢
      generalize σ - -2 / B = v at h2' ⊢
      field_simp
      ring
    rw [e, norm_mul, norm_mul]
    gcongr
    exact s3dv_ratio_le hε hσ
  rcases eq_or_ne B 0 with rfl | hB
  · have ha : 1 / A ≠ 0 := one_div_ne_zero hA
    have hb : 2 / A ≠ 0 := div_ne_zero two_ne_zero hA
    have hab : 1 / A ≠ 2 / A := by
      intro h; rw [div_eq_div_iff hA hA] at h; apply hA; linear_combination -h
    refine s3dv_int_dom ha hb hab (C := ‖1 / A‖ * (1 + ‖2 / A‖ / ε)) hm ?_
    have hF : ({1 / A, 2 / A} : Set ℂ).Countable := (Set.toFinite _).countable
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (hF.ae_notMem volume)] with σ hσ hσF
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hσF
    obtain ⟨h1, h2⟩ := hσF
    have hσ : ε ≤ ‖σ‖ := hσ
    have hσ0 : σ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hε hσ)
    have e : 1 / (σ * (σ * (1 + 0 * σ) * (A * σ - 1))) =
        1 / A * ((σ - 2 / A) / σ) * (1 / (σ * (σ - 1 / A) * (σ - 2 / A))) := by
      have e2 : A * σ - 1 = A * (σ - 1 / A) := by field_simp
      rw [e2]
      have h1' : σ - 1 / A ≠ 0 := sub_ne_zero.mpr h1
      have h2' : σ - 2 / A ≠ 0 := sub_ne_zero.mpr h2
      generalize σ - 1 / A = u at h1' ⊢
      generalize σ - 2 / A = v at h2' ⊢
      field_simp
      ring
    rw [e, norm_mul, norm_mul]
    gcongr
    exact s3dv_ratio_le hε hσ
  · have ha : -1 / B ≠ 0 := div_ne_zero (neg_ne_zero.mpr one_ne_zero) hB
    have hb : 1 / A ≠ 0 := one_div_ne_zero hA
    have hab : -1 / B ≠ 1 / A := by
      intro h
      rw [div_eq_div_iff hB hA] at h
      exact hAB (by linear_combination -h)
    refine s3dv_int_dom ha hb hab (C := 1 / (‖A * B‖ * ε)) hm ?_
    have hF : ({-1 / B, 1 / A} : Set ℂ).Countable := (Set.toFinite _).countable
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (hF.ae_notMem volume)] with σ hσ hσF
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hσF
    obtain ⟨h1, h2⟩ := hσF
    have hσ : ε ≤ ‖σ‖ := hσ
    have hσ0 : σ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hε hσ)
    have e : 1 / (σ * (σ * (1 + B * σ) * (A * σ - 1))) =
        1 / (A * B) * (1 / σ) * (1 / (σ * (σ - -1 / B) * (σ - 1 / A))) := by
      have e1 : 1 + B * σ = B * (σ - -1 / B) := by field_simp; ring
      have e2 : A * σ - 1 = A * (σ - 1 / A) := by field_simp
      rw [e1, e2]
      have h1' : σ - -1 / B ≠ 0 := sub_ne_zero.mpr h1
      have h2' : σ - 1 / A ≠ 0 := sub_ne_zero.mpr h2
      field_simp
    rw [e, norm_mul, norm_mul]
    have hAB0 : 0 < ‖A * B‖ := norm_pos_iff.mpr (mul_ne_zero hA hB)
    have hs : ‖1 / σ‖ ≤ 1 / ε := by
      rw [norm_div, norm_one]; exact one_div_le_one_div_of_le hε hσ
    have hc : ‖1 / (A * B)‖ * ‖1 / σ‖ ≤ 1 / (‖A * B‖ * ε) := by
      rw [norm_div, norm_one]
      calc 1 / ‖A * B‖ * ‖1 / σ‖ ≤ 1 / ‖A * B‖ * (1 / ε) := by gcongr
        _ = 1 / (‖A * B‖ * ε) := by field_simp
    exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

/-- `𝗀_μ` takes any given value at most once on `𝔻*`, so `g ξ ≠ c` a.e. on `𝔻*`. -/
theorem s3dv_g_ne_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (c : ℂ) :
    ∀ᵐ ξ ∂(volume.restrict unitDiscExterior), gsans μ ξ ≠ c := by
  have hinj := (S2C.s2c_conf_g hμ).2.1
  have hsub : (unitDiscExterior ∩ gsans μ ⁻¹' {c}).Subsingleton := fun x hx y hy =>
    hinj hx.1 hy.1 (hx.2.trans hy.2.symm)
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [ae_restrict_iff' hE]
  have h0 : volume (unitDiscExterior ∩ gsans μ ⁻¹' {c}) = 0 := hsub.finite.measure_zero volume
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with ξ hξ hξE hgc
  exact hξ ⟨hξE, hgc⟩

/-- **The transported first variation.** For `w` off the pole (`1 - P w ≠ 0`) and `ζ = Φ(w) = w/(d(1 - P w))`:
`Φ'(w) · (-(1/π) ∫ D_μ θ · K(w, W x) (∂W)²) = V̇(ζ) + I₁ ζ + I₂ ζ²`, with
`V̇(ζ) = -(1/π)∫ θ g'² k(ζ, g)`, `I₁ = (1/π)∫ θ g'²/(g N(g))` and `I₂ = (1/π)∫ θ g'² AB/N(g)`.
Each of the three integrals converges on its own (`s3dv_int_k`, `s3dv_int_N1`, `s3dv_int_N2`). -/
theorem s3dv_ident {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (θ : LinfStar) {w : ℂ}
    (hw : 1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * w ≠ 0) :
    1 / (deriv (normalizedSolution (extB μ)) 0 * (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * w) ^ 2) *
      (-(1 / π : ℂ) * ∫ x in unitDiscExterior, QCV.qcv_rightDerivative μ θ x *
        ahKer w (normalizedSolution (extB μ) x) * dz (normalizedSolution (extB μ)) x ^ 2) =
    -(1 / π : ℂ) * (∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
        (1 / (gsans μ ξ - w / (deriv (normalizedSolution (extB μ)) 0 *
            (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * w))) - 1 / gsans μ ξ -
          w / (deriv (normalizedSolution (extB μ)) 0 *
            (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * w)) / gsans μ ξ ^ 2)) +
      w / (deriv (normalizedSolution (extB μ)) 0 * (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * w)) *
        ((1 / π : ℂ) * ∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
          (1 / (gsans μ ξ * (gsans μ ξ * (1 + s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) *
              deriv (normalizedSolution (extB μ)) 0 * gsans μ ξ) *
            (deriv (normalizedSolution (extB μ)) 0 * (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0)) *
              gsans μ ξ - 1))))) +
      (w / (deriv (normalizedSolution (extB μ)) 0 * (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * w))) ^ 2 *
        ((1 / π : ℂ) * ∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
          (deriv (normalizedSolution (extB μ)) 0 * (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0)) *
              (s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * deriv (normalizedSolution (extB μ)) 0) /
            (gsans μ ξ * (1 + s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) *
              deriv (normalizedSolution (extB μ)) 0 * gsans μ ξ) *
              (deriv (normalizedSolution (extB μ)) 0 * (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0)) *
                gsans μ ξ - 1)))) := by
  have hd0 : deriv (normalizedSolution (extB μ)) 0 ≠ 0 := (AppA.acc_wB_rep hμ).1
  set W := normalizedSolution (extB μ) with hW
  set d := deriv W 0 with hd
  set P := s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) with hP
  set g := gsans μ with hg
  set ζ := w / (d * (1 - P * w)) with hζ
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  -- step 1: into the transport form
  have hFm : Measurable fun s : ℂ => 1 / (d * (1 - P * w) ^ 2) * ahKer w s := by
    unfold ahKer; fun_prop
  have h1 : 1 / (d * (1 - P * w) ^ 2) *
      (-(1 / π : ℂ) * ∫ x in unitDiscExterior, QCV.qcv_rightDerivative μ θ x * ahKer w (W x) * dz W x ^ 2) =
      -(1 / π : ℂ) * ∫ x in unitDiscExterior, QCV.qcv_rightDerivative μ θ x * dz W x ^ 2 *
        (fun s : ℂ => 1 / (d * (1 - P * w) ^ 2) * ahKer w s) (W x) := by
    rw [mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    ring
  rw [h1, s3dv_transport hμ θ hFm]
  -- step 2: the kernel identity, a.e. on `𝔻*`
  obtain ⟨ε, hε, hreg⟩ := s3dv_g_region hμ
  have hsub : g '' unitDiscExterior ⊆ {σ : ℂ | ε ≤ ‖σ‖} := by
    rintro _ ⟨ξ, hξ, rfl⟩; exact hreg ξ hξ
  have hAB : d * (1 - P) + P * d ≠ 0 := by
    have : d * (1 - P) + P * d = d := by ring
    rw [this]; exact hd0
  have hζw : 1 + P * d * ζ ≠ 0 := by
    have : 1 + P * d * ζ = 1 / (1 - P * w) := by rw [hζ]; field_simp; ring
    rw [this]; exact one_div_ne_zero hw
  have hwζ : d * ζ / (1 + P * d * ζ) = w := by
    have : 1 + P * d * ζ = 1 / (1 - P * w) := by rw [hζ]; field_simp; ring
    have hw' : 1 - w * P ≠ 0 := by rwa [mul_comm]
    rw [this, hζ]; field_simp
  have hpre : 1 / (d * (1 - P * w) ^ 2) = (1 + P * d * ζ) ^ 2 / d := by
    have : 1 + P * d * ζ = 1 / (1 - P * w) := by rw [hζ]; field_simp; ring
    rw [this]; field_simp
  have hB : ∀ᵐ ξ ∂(volume.restrict unitDiscExterior), 1 + P * d * g ξ ≠ 0 := by
    by_cases hPd : P * d = 0
    · exact ae_of_all _ fun ξ => by rw [hPd]; simp
    · filter_upwards [s3dv_g_ne_ae hμ (-1 / (P * d))] with ξ hξ h0
      apply hξ
      rw [eq_div_iff hPd]
      linear_combination h0
  have hA : ∀ᵐ ξ ∂(volume.restrict unitDiscExterior), d * (1 - P) * g ξ - 1 ≠ 0 := by
    by_cases hA0 : d * (1 - P) = 0
    · exact ae_of_all _ fun ξ => by rw [hA0]; simp
    · filter_upwards [s3dv_g_ne_ae hμ (1 / (d * (1 - P)))] with ξ hξ h0
      apply hξ
      rw [eq_div_iff hA0]
      linear_combination h0
  have hpt : ∀ᵐ ξ ∂(volume.restrict unitDiscExterior),
      θ ξ * deriv g ξ ^ 2 * ((fun s : ℂ => 1 / (d * (1 - P * w) ^ 2) * ahKer w s) (d * g ξ / (1 + P * d * g ξ)) *
        (d * (1 - P * (d * g ξ / (1 + P * d * g ξ))) ^ 2) ^ 2) =
      θ ξ * deriv g ξ ^ 2 * (1 / (g ξ - ζ) - 1 / g ξ - ζ / g ξ ^ 2) -
        ζ * (θ ξ * deriv g ξ ^ 2 * (1 / (g ξ * (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1))))) -
        ζ ^ 2 * (θ ξ * deriv g ξ ^ 2 * (d * (1 - P) * (P * d) /
          (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1)))) := by
    filter_upwards [hB, hA, s3dv_g_ne_ae hμ ζ, ae_restrict_mem hE] with ξ hBξ hAξ hζξ hξ
    have hσ0 : g ξ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hε (hreg ξ hξ))
    have hk := s3dv_kernel_f hd0 hζw hBξ hσ0 hAξ (sub_ne_zero.mpr hζξ)
    rw [hwζ] at hk
    have h2 : d * (1 - P * (d * g ξ / (1 + P * d * g ξ))) ^ 2 = d / (1 + P * d * g ξ) ^ 2 := by
      have : 1 - P * (d * g ξ / (1 + P * d * g ξ)) = 1 / (1 + P * d * g ξ) := by field_simp; ring
      rw [this]; field_simp
    rw [hpre, h2, hk]
    ring
  simp only [← hW, ← hd, ← hP, ← hg]
  rw [integral_congr_ae hpt]
  -- step 3: split (each piece integrable)
  have hθm : AEStronglyMeasurable (⇑θ) (volume.restrict unitDiscExterior) := Lp.aestronglyMeasurable θ
  have hθb := LinfStar_ae_norm_le θ
  have i1 := s3dv_int_transfer hμ hθm hθb ((s3dv_int_k hε ζ).mono_set hsub)
  have i2 := (s3dv_int_transfer hμ hθm hθb ((s3dv_int_N1 hε hAB).mono_set hsub)).const_mul ζ
  have i3 := (s3dv_int_transfer hμ hθm hθb ((s3dv_int_N2 hε hAB).mono_set hsub)).const_mul (ζ ^ 2)
  simp only [← hg] at i1 i2 i3
  have i12 : IntegrableOn (fun ξ => θ ξ * deriv g ξ ^ 2 * (1 / (g ξ - ζ) - 1 / g ξ - ζ / g ξ ^ 2) -
      ζ * (θ ξ * deriv g ξ ^ 2 * (1 / (g ξ * (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1)))))) unitDiscExterior :=
    i1.sub i2
  rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul]
  ring

/-- The off-centre line `t ↦ (a + t m) * κ` is holomorphic on a disc around `0`, with values in the ball. -/
theorem s3dv_line {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (m' : LinfStar) :
    ∃ ρ > 0, DifferentiableOn ℂ (fun t : ℂ => beltramiMul (a + t • m') κ) (ball 0 ρ) ∧
      MapsTo (fun t : ℂ => beltramiMul (a + t • m') κ) (ball 0 ρ) LinfStarBall := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  set ρ := (1 - ‖a‖) / (‖m'‖ + 1) with hρ
  have hρ0 : 0 < ρ := div_pos (by linarith) (by positivity)
  have hline : MapsTo (fun t : ℂ => a + t • m') (ball 0 ρ) LinfStarBall := by
    intro t ht
    have ht' : ‖t‖ < ρ := mem_ball_zero_iff.mp ht
    show a + t • m' ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff]
    calc ‖a + t • m'‖ ≤ ‖a‖ + ‖t‖ * ‖m'‖ := (norm_add_le _ _).trans (by rw [norm_smul])
      _ ≤ ‖a‖ + ρ * ‖m'‖ := by gcongr
      _ < 1 := by
        have : ρ * ‖m'‖ < 1 - ‖a‖ := by
          rw [hρ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg m']
        linarith
  refine ⟨ρ, hρ0, ?_, fun t ht => bg_mul_mem_ball hκ (hline ht)⟩
  exact (bd_differentiableOn hκ).comp ((differentiable_const _).add (differentiable_id.smul_const m')).differentiableOn
    hline

/-- `Ẇ(y) = ∂_t W_{ν_t}(y)|₀` is holomorphic on `𝔻`, vanishes at `0`, and `Ẇ'(0) = ∂_t W_{ν_t}'(0)|₀`: it is the locally
uniform limit of the holomorphic difference quotients (`s3dv_W_taylor`). -/
theorem s3dv_Wdot_holo {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (m' : LinfStar) :
    DifferentiableOn ℂ (fun y => deriv (fun t : ℂ => normalizedSolution (extB (beltramiMul (a + t • m') κ)) y) 0)
        unitDisc ∧
      deriv (fun t : ℂ => normalizedSolution (extB (beltramiMul (a + t • m') κ)) 0) 0 = 0 ∧
      deriv (fun y => deriv (fun t : ℂ => normalizedSolution (extB (beltramiMul (a + t • m') κ)) y) 0) 0 =
        deriv (fun t : ℂ => deriv (normalizedSolution (extB (beltramiMul (a + t • m') κ))) 0) 0 := by
  obtain ⟨ρ, hρ, hc, hcm⟩ := s3dv_line hκ ha m'
  set c : ℂ → LinfStar := fun t => beltramiMul (a + t • m') κ with hcdef
  set Wd : ℂ → ℂ := fun y => deriv (fun t : ℂ => normalizedSolution (extB (c t)) y) 0 with hWd
  set G : ℂ → ℂ → ℂ := fun t y => (normalizedSolution (extB (c t)) y - normalizedSolution (extB (c 0)) y) / t
    with hG
  have hU : IsOpen unitDisc := isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ρ := mem_ball_self hρ
  have hWhol : ∀ t ∈ ball (0 : ℂ) ρ, DifferentiableOn ℂ (normalizedSolution (extB (c t))) unitDisc := fun t ht =>
    (QCV.qcv_W_props (mem_ball_zero_iff.mp (hcm ht))).2.1
  have hTLU : TendstoLocallyUniformlyOn G Wd (𝓝[≠] (0 : ℂ)) unitDisc := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K _ hK
    obtain ⟨C, hC⟩ := s3dv_W_taylor hρ hc hcm hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ ball (0 : ℂ) (ρ / 2) ∧ (|C| + 1) * ‖t‖ < ε ∧ t ≠ 0 := by
      have h1 : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ ball (0 : ℂ) (ρ / 2) := isOpen_ball.mem_nhds (mem_ball_self (by linarith))
      have h2 : ∀ᶠ t in 𝓝 (0 : ℂ), (|C| + 1) * ‖t‖ < ε := by
        have hcont : Continuous fun t : ℂ => (|C| + 1) * ‖t‖ := by fun_prop
        exact hcont.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
      filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, self_mem_nhdsWithin] with t ht1 ht2 ht3
      exact ⟨ht1, ht2, ht3⟩
    filter_upwards [hev] with t ht y hy
    obtain ⟨ht1, ht2, ht3⟩ := ht
    have hb := hC t ht1 y hy
    have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht3
    rw [dist_eq_norm, norm_sub_rev]
    have e : G t y - Wd y = (normalizedSolution (extB (c t)) y - normalizedSolution (extB (c 0)) y -
        t * Wd y) / t := by
      simp only [hG]; field_simp
    rw [e, norm_div]
    calc ‖normalizedSolution (extB (c t)) y - normalizedSolution (extB (c 0)) y - t * Wd y‖ / ‖t‖
        ≤ C * ‖t‖ ^ 2 / ‖t‖ := by gcongr
      _ = C * ‖t‖ := by field_simp
      _ ≤ (|C| + 1) * ‖t‖ := by gcongr; linarith [le_abs_self C]
      _ < ε := ht2
  have hFev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), DifferentiableOn ℂ (G t) unitDisc := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds h0)] with t ht
    exact ((hWhol t ht).sub (hWhol 0 h0)).div_const t
  have hWdo : DifferentiableOn ℂ Wd unitDisc := hTLU.differentiableOn hFev hU
  refine ⟨hWdo, ?_, ?_⟩
  · have hconst : (fun t : ℂ => normalizedSolution (extB (c t)) 0) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [isOpen_ball.mem_nhds h0] with t ht
      exact (QCV.qcv_W_props (mem_ball_zero_iff.mp (hcm ht))).2.2.2
    rw [hconst.deriv_eq, deriv_const]
  · have hD := hTLU.deriv hFev hU
    have h0D : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
    have hlim := hD.tendsto_at h0D
    -- the derivative of the quotients at `0` is the slope of `t ↦ W_{c t}'(0)`
    have hDd : DifferentiableAt ℂ (fun t : ℂ => deriv (normalizedSolution (extB (c t))) 0) 0 := by
      have h1 := (s5cf_planeB_deriv_analytic (hcm h0)).differentiableAt
      exact h1.comp (0 : ℂ) (hc.differentiableAt (isOpen_ball.mem_nhds h0))
    have hslope := hDd.hasDerivAt.tendsto_slope_zero
    have heq : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (deriv ∘ G) t 0 =
        t⁻¹ • (deriv (normalizedSolution (extB (c (0 + t)))) 0 - deriv (normalizedSolution (extB (c 0))) 0) := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds h0), self_mem_nhdsWithin] with t ht ht0
      have hd1 := (hWhol t ht).differentiableAt (hU.mem_nhds h0D)
      have hd2 := (hWhol 0 h0).differentiableAt (hU.mem_nhds h0D)
      simp only [Function.comp_apply, hG, zero_add, smul_eq_mul]
      rw [deriv_div_const, deriv_fun_sub hd1 hd2]
      ring
    exact tendsto_nhds_unique (hlim.congr' heq) hslope

/-- `1/σ³` is integrable on `{ε ≤ ‖σ‖}`. -/
theorem s3dv_int_cube {ε : ℝ} (hε : 0 < ε) : IntegrableOn (fun σ : ℂ => 1 / σ ^ 3) {σ : ℂ | ε ≤ ‖σ‖} := by
  have hS : MeasurableSet {σ : ℂ | ε ≤ ‖σ‖} := measurableSet_le measurable_const measurable_norm
  refine s3dv_int_dom one_ne_zero two_ne_zero (by norm_num) (C := (1 + ‖(1 : ℂ)‖ / ε) * (1 + ‖(2 : ℂ)‖ / ε))
    (by fun_prop : Measurable fun σ : ℂ => 1 / σ ^ 3).aestronglyMeasurable ?_
  have hF : ({1, 2} : Set ℂ).Countable := (Set.toFinite _).countable
  filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (hF.ae_notMem volume)] with σ hσ hσF
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hσF
  obtain ⟨h1, h2⟩ := hσF
  have hσ : ε ≤ ‖σ‖ := hσ
  have hσ0 : σ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hε hσ)
  have e : 1 / σ ^ 3 = ((σ - 1) / σ) * ((σ - 2) / σ) * (1 / (σ * (σ - 1) * (σ - 2))) := by
    have h1' : σ - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h2' : σ - 2 ≠ 0 := sub_ne_zero.mpr h2
    field_simp
  rw [e, norm_mul, norm_mul]
  gcongr
  · exact s3dv_ratio_le hε hσ
  · exact s3dv_ratio_le hε hσ

/-- `V̇(ζ) = O(|ζ|²)` near `ζ = 0`. -/
theorem s3dv_Vdot_small {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (θ : LinfStar) :
    ∃ δ > 0, ∃ C : ℝ, ∀ ζ : ℂ, ‖ζ‖ ≤ δ →
      ‖∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
        (1 / (gsans μ ξ - ζ) - 1 / gsans μ ξ - ζ / gsans μ ξ ^ 2)‖ ≤ C * ‖ζ‖ ^ 2 := by
  obtain ⟨ε, hε, hreg⟩ := s3dv_g_region hμ
  have hsub : gsans μ '' unitDiscExterior ⊆ {σ : ℂ | ε ≤ ‖σ‖} := by
    rintro _ ⟨ξ, hξ, rfl⟩; exact hreg ξ hξ
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hθm : AEStronglyMeasurable (⇑θ) (volume.restrict unitDiscExterior) := Lp.aestronglyMeasurable θ
  have hi := (s3dv_int_transfer hμ hθm (LinfStar_ae_norm_le θ) ((s3dv_int_cube hε).mono_set hsub)).norm
  refine ⟨ε / 2, half_pos hε, 2 * ∫ ξ in unitDiscExterior, ‖θ ξ * deriv (gsans μ) ξ ^ 2 * (1 / gsans μ ξ ^ 3)‖,
    fun ζ hζ => ?_⟩
  have hb : ∀ᵐ ξ ∂(volume.restrict unitDiscExterior),
      ‖θ ξ * deriv (gsans μ) ξ ^ 2 * (1 / (gsans μ ξ - ζ) - 1 / gsans μ ξ - ζ / gsans μ ξ ^ 2)‖ ≤
        2 * ‖ζ‖ ^ 2 * ‖θ ξ * deriv (gsans μ) ξ ^ 2 * (1 / gsans μ ξ ^ 3)‖ := by
    filter_upwards [ae_restrict_mem hE] with ξ hξ
    have hσ := hreg ξ hξ
    set σ := gsans μ ξ
    have hσ0 : 0 < ‖σ‖ := lt_of_lt_of_le hε hσ
    have hσne : σ ≠ 0 := norm_pos_iff.mp hσ0
    have hsz : ‖σ‖ / 2 ≤ ‖σ - ζ‖ := by
      have := norm_sub_norm_le σ ζ
      linarith
    have hsz0 : σ - ζ ≠ 0 := by
      intro h; rw [h, norm_zero] at hsz; linarith
    have e : 1 / (σ - ζ) - 1 / σ - ζ / σ ^ 2 = ζ ^ 2 / (σ ^ 2 * (σ - ζ)) := by field_simp; ring
    rw [e, norm_mul, norm_mul, norm_mul, norm_div, norm_div, norm_mul, norm_pow, norm_pow, norm_pow, norm_one]
    have hk : ‖ζ‖ ^ 2 / (‖σ‖ ^ 2 * ‖σ - ζ‖) ≤ 2 * ‖ζ‖ ^ 2 * (1 / ‖σ‖ ^ 3) := by
      rw [div_le_iff₀ (by positivity)]
      have : 2 * ‖ζ‖ ^ 2 * (1 / ‖σ‖ ^ 3) * (‖σ‖ ^ 2 * ‖σ - ζ‖) = ‖ζ‖ ^ 2 * (2 * ‖σ - ζ‖ / ‖σ‖) := by
        field_simp
      rw [this]
      have h2 : 1 ≤ 2 * ‖σ - ζ‖ / ‖σ‖ := by rw [le_div_iff₀ hσ0]; linarith
      nlinarith [sq_nonneg ‖ζ‖]
    calc ‖θ ξ‖ * ‖deriv (gsans μ) ξ‖ ^ 2 * (‖ζ‖ ^ 2 / (‖σ‖ ^ 2 * ‖σ - ζ‖))
        ≤ ‖θ ξ‖ * ‖deriv (gsans μ) ξ‖ ^ 2 * (2 * ‖ζ‖ ^ 2 * (1 / ‖σ‖ ^ 3)) := by gcongr
      _ = 2 * ‖ζ‖ ^ 2 * (‖θ ξ * deriv (gsans μ) ξ ^ 2‖ * (1 / ‖σ ^ 3‖)) := by
        rw [norm_mul, norm_pow, norm_pow]; ring
  calc ‖∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
        (1 / (gsans μ ξ - ζ) - 1 / gsans μ ξ - ζ / gsans μ ξ ^ 2)‖
      ≤ ∫ ξ in unitDiscExterior, 2 * ‖ζ‖ ^ 2 * ‖θ ξ * deriv (gsans μ) ξ ^ 2 * (1 / gsans μ ξ ^ 3)‖ :=
        norm_integral_le_of_norm_le (hi.const_mul _) hb
    _ = 2 * (∫ ξ in unitDiscExterior, ‖θ ξ * deriv (gsans μ) ξ ^ 2 * (1 / gsans μ ξ ^ 3)‖) * ‖ζ‖ ^ 2 := by
        rw [integral_const_mul]; ring

/-- **Normalization** (`f_t'(0) = 1`): the linear coefficient of the transported first variation vanishes,
`I₁ = ḋ/d`, where `ḋ = ∂_t W_{ν_t}'(0)|₀`. Differentiate `Φ'(W)·Ẇ = V̇(𝖿) + I₁ 𝖿 + I₂ 𝖿²` at `0`: on the left
`Ẇ(0) = 0` and `Ẇ'(0) = ḋ`; on the right `V̇(ζ) = O(|ζ|²)`, `𝖿(0) = 0`, `𝖿'(0) = 1`. -/
theorem s3dv_norm {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (m' : LinfStar) :
    (1 / π : ℂ) * ∫ ξ in unitDiscExterior, Rnm m' a ξ * deriv (gsans (beltramiMul a κ)) ξ ^ 2 *
        (1 / (gsans (beltramiMul a κ) ξ * (gsans (beltramiMul a κ) ξ *
          (1 + s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ))
              (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) *
            deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * gsans (beltramiMul a κ) ξ) *
          (deriv (normalizedSolution (extB (beltramiMul a κ))) 0 *
              (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ))
                (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0)) *
            gsans (beltramiMul a κ) ξ - 1)))) =
      deriv (fun t : ℂ => deriv (normalizedSolution (extB (beltramiMul (a + t • m') κ))) 0) 0 /
        deriv (normalizedSolution (extB (beltramiMul a κ))) 0 := by
  set μ := beltramiMul a κ with hμdef
  have hμ : μ ∈ LinfStarBall := bg_mul_mem_ball hκ ha
  have hd0 : deriv (normalizedSolution (extB μ)) 0 ≠ 0 := (AppA.acc_wB_rep hμ).1
  set W := normalizedSolution (extB μ) with hW
  set d := deriv W 0 with hd
  set P := s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) with hP
  set θ : LinfStar := Rnm m' a with hθ
  set Wd : ℂ → ℂ := fun y => deriv (fun t : ℂ => normalizedSolution (extB (beltramiMul (a + t • m') κ)) y) 0
    with hWd
  set dd := deriv (fun t : ℂ => deriv (normalizedSolution (extB (beltramiMul (a + t • m') κ))) 0) 0 with hdd
  obtain ⟨hWdo, hWd0, hWdd⟩ := s3dv_Wdot_holo hκ ha m'
  have hWdo' : DifferentiableOn ℂ Wd unitDisc := hWdo
  have hWd0' : Wd 0 = 0 := hWd0
  have hWdd' : deriv Wd 0 = dd := hWdd
  -- the source tangent is `D_μ θ`
  have htan : fderiv ℂ (fun l => beltramiMul l κ) a m' = QCV.qcv_rightDerivative μ θ := by
    have h1 := s4g_tangent hκ ha m'
    simp only [← hμdef, ← hθ] at h1
    rw [← h1, QCV.qcv_rightDerivative_Rnm hμ]
  -- the identity on `𝔻`
  set V : ℂ → ℂ := fun ζ => -(1 / π : ℂ) * ∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
      (1 / (gsans μ ξ - ζ) - 1 / gsans μ ξ - ζ / gsans μ ξ ^ 2) with hV
  set I₁ : ℂ := (1 / π : ℂ) * ∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
      (1 / (gsans μ ξ * (gsans μ ξ * (1 + P * d * gsans μ ξ) * (d * (1 - P) * gsans μ ξ - 1)))) with hI₁
  set I₂ : ℂ := (1 / π : ℂ) * ∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
      (d * (1 - P) * (P * d) / (gsans μ ξ * (1 + P * d * gsans μ ξ) * (d * (1 - P) * gsans μ ξ - 1))) with hI₂
  set f := fsans μ with hf
  have hiden : ∀ y ∈ unitDisc, 1 / (d * (1 - P * W y) ^ 2) * Wd y = V (f y) + f y * I₁ + f y ^ 2 * I₂ := by
    intro y hy
    obtain ⟨hw, hfy⟩ := s3dv_frep hμ hy
    have hWdy : Wd y = -(1 / π : ℂ) * ∫ x in unitDiscExterior, QCV.qcv_rightDerivative μ θ x *
        ahKer (W y) (W x) * dz W x ^ 2 := by
      change deriv (fun t : ℂ => normalizedSolution (extB (beltramiMul (a + t • m') κ)) y) 0 = _
      rw [(s3dv_Wdot hκ ha m' y).deriv, htan]
    have hfy' : f y = W y / (d * (1 - P * W y)) := hfy
    rw [hWdy, s3dv_ident hμ θ hw, hfy']
  -- left side: derivative `ḋ/d`
  have hU : IsOpen unitDisc := isOpen_ball
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  obtain ⟨-, hWhol, -, hW0⟩ := QCV.qcv_W_props (mem_ball_zero_iff.mp hμ)
  have hW0' : W 0 = 0 := hW0
  have hWda : DifferentiableAt ℂ W 0 := hWhol.differentiableAt (hU.mem_nhds h0)
  have hφ : DifferentiableAt ℂ (fun y => 1 / (d * (1 - P * W y) ^ 2)) 0 := by
    have hne : d * (1 - P * W 0) ^ 2 ≠ 0 := by rw [hW0']; simpa using hd0
    exact (differentiableAt_const _).div ((differentiableAt_const _).mul
      (((differentiableAt_const _).sub ((differentiableAt_const _).mul hWda)).pow 2)) hne
  have hWdA : DifferentiableAt ℂ Wd 0 := hWdo'.differentiableAt (hU.mem_nhds h0)
  have hL : HasDerivAt (fun y => 1 / (d * (1 - P * W y) ^ 2) * Wd y) (dd / d) 0 := by
    have h := hφ.hasDerivAt.mul hWdA.hasDerivAt
    convert h using 1
    rw [hWd0', hWdd', hW0']
    simp only [mul_zero, zero_add, sub_zero, one_pow, mul_one]
    field_simp
  -- right side: derivative `I₁`
  obtain ⟨hf0, hf1, -⟩ := fB_normalization μ
  have hfeq : f = fB μ := S2C.s2c_fsans_eq hμ
  have hfd : DifferentiableAt ℂ f 0 := by
    rw [hfeq]; exact (fB_holomorphic_injective hμ).1.differentiableAt (hU.mem_nhds h0)
  have hf0' : f 0 = 0 := by rw [hfeq]; exact hf0
  have hf1' : deriv f 0 = 1 := by rw [hfeq]; exact hf1
  have hV0 : V 0 = 0 := by simp [hV]
  obtain ⟨δ, hδ, C, hC⟩ := s3dv_Vdot_small hμ θ
  have hVf : HasDerivAt (fun y => V (f y)) 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, hf0', hV0, sub_zero, smul_zero]
    have hfb : (fun y => f y) =O[𝓝 0] fun y => y := by
      have h := hfd.hasDerivAt.isBigO_sub
      simpa [hf0'] using h
    have hfc : Tendsto f (𝓝 0) (𝓝 0) := by
      have h := hfd.continuousAt.tendsto
      rwa [hf0'] at h
    have hsmall : ∀ᶠ y in 𝓝 (0 : ℂ), ‖f y‖ ≤ δ := by
      have := hfc.eventually (closedBall_mem_nhds 0 hδ)
      filter_upwards [this] with y hy
      simpa using hy
    have hbig : (fun y => V (f y)) =O[𝓝 0] fun y => f y ^ 2 := by
      refine Asymptotics.IsBigO.of_bound (|C| * (1 / π)) ?_
      filter_upwards [hsmall] with y hy
      have h1 := hC (f y) hy
      simp only [hV, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, norm_pow]
      calc 1 / π * ‖∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
            (1 / (gsans μ ξ - f y) - 1 / gsans μ ξ - f y / gsans μ ξ ^ 2)‖
          ≤ 1 / π * (C * ‖f y‖ ^ 2) := by gcongr
        _ ≤ |C| * (1 / π) * ‖f y‖ ^ 2 := by
            rw [mul_comm |C|, mul_assoc]
            gcongr
            exact le_abs_self C
    have hsq : (fun y => f y ^ 2) =o[𝓝 0] fun y => y := by
      have h2 : (fun y : ℂ => y ^ 2) =o[𝓝 0] fun y => y := by
        have := Asymptotics.isLittleO_pow_id (𝕜 := ℂ) (n := 2) (by norm_num)
        simpa using this
      have h3 : (fun y => f y ^ 2) =O[𝓝 0] fun y : ℂ => y ^ 2 := by
        simpa using hfb.pow 2
      exact h3.trans_isLittleO h2
    exact hbig.trans_isLittleO hsq
  have hR : HasDerivAt (fun y => V (f y) + f y * I₁ + f y ^ 2 * I₂) I₁ 0 := by
    have h := (hVf.add (hfd.hasDerivAt.mul_const I₁)).add ((hfd.hasDerivAt.pow 2).mul_const I₂)
    convert h using 1
    rw [hf1', hf0']
    ring
  have heq : (fun y => 1 / (d * (1 - P * W y) ^ 2) * Wd y) =ᶠ[𝓝 0]
      fun y => V (f y) + f y * I₁ + f y ^ 2 * I₂ := by
    filter_upwards [hU.mem_nhds h0] with y hy
    exact hiden y hy
  have hfin := (hL.congr_of_eventuallyEq heq.symm).unique hR
  rw [← hfin]

/-- Replacing the `L^∞` representative `Rnm m' a` by the pointwise `RnmFun m' a` in an integral over `𝔻*`. -/
theorem s3dv_RF {a : LinfStar} (ha : a ∈ LinfStarBall) (m' : LinfStar) (G H : ℂ → ℂ) :
    ∫ ξ in unitDiscExterior, Rnm m' a ξ * G ξ * H ξ = ∫ ξ in unitDiscExterior, RnmFun m' a ξ * G ξ * H ξ :=
  integral_congr_ae ((WPCV.wpcv_RnmFun_ae ha m').mono fun ξ h => by simp only [h])

/-- The transported first variation on `𝔻`: `Ẇ / (d (1 - PW)²) = V̇(𝖿) + I₁ 𝖿 + I₂ 𝖿²` (the f/g identity
`s3dv_ident` at `w = W(y)`, with `Ẇ` from `s3dv_Wdot`). -/
theorem s3dv_fiden {κ a μ : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (hμ : μ = beltramiMul a κ)
    (m' : LinfStar) {y : ℂ} (hy : y ∈ unitDisc) :
    1 / (deriv (normalizedSolution (extB μ)) 0 *
        (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * normalizedSolution (extB μ) y) ^ 2) *
      deriv (fun t : ℂ => normalizedSolution (extB (beltramiMul (a + t • m') κ)) y) 0 =
    -(1 / π : ℂ) * (∫ ξ in unitDiscExterior, Rnm m' a ξ * deriv (gsans μ) ξ ^ 2 *
        (1 / (gsans μ ξ - fsans μ y) - 1 / gsans μ ξ - fsans μ y / gsans μ ξ ^ 2)) +
      fsans μ y * ((1 / π : ℂ) * ∫ ξ in unitDiscExterior, Rnm m' a ξ * deriv (gsans μ) ξ ^ 2 *
        (1 / (gsans μ ξ * (gsans μ ξ * (1 + s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) *
            deriv (normalizedSolution (extB μ)) 0 * gsans μ ξ) *
          (deriv (normalizedSolution (extB μ)) 0 * (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0)) *
            gsans μ ξ - 1))))) +
      fsans μ y ^ 2 * ((1 / π : ℂ) * ∫ ξ in unitDiscExterior, Rnm m' a ξ * deriv (gsans μ) ξ ^ 2 *
        (deriv (normalizedSolution (extB μ)) 0 * (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0)) *
            (s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * deriv (normalizedSolution (extB μ)) 0) /
          (gsans μ ξ * (1 + s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) *
              deriv (normalizedSolution (extB μ)) 0 * gsans μ ξ) *
            (deriv (normalizedSolution (extB μ)) 0 * (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0)) *
              gsans μ ξ - 1)))) := by
  have hμb : μ ∈ LinfStarBall := by rw [hμ]; exact bg_mul_mem_ball hκ ha
  obtain ⟨hw, hfy⟩ := s3dv_frep hμb hy
  have h1 := s4g_tangent hκ ha m'
  rw [← hμ] at h1
  have htan : fderiv ℂ (fun l => beltramiMul l κ) a m' = QCV.qcv_rightDerivative μ (Rnm m' a) := by
    rw [← h1, QCV.qcv_rightDerivative_Rnm hμb]
  have hWdy := (s3dv_Wdot hκ ha m' y).deriv
  rw [← hμ, htan] at hWdy
  rw [hWdy, s3dv_ident hμb (Rnm m' a) hw, hfy]

/-- The exact second-order remainder of `(N, d, P) ↦ N / (d (1 - P N))`, with `M = d(1 - Pn)`,
`ℓM = t ḋ (1 - Pn) - d((t P₁ + s P₂) n + P t Ṅ)` the linear part of `M_t - M`. -/
theorem s3dv_comp_alg {t s n nd Nt d dT P PT dd P₁ P₂ : ℂ} (hd : d ≠ 0) (hD : 1 - P * n ≠ 0)
    (hMt : dT * (1 - PT * Nt) ≠ 0) :
    Nt / (dT * (1 - PT * Nt)) - n / (d * (1 - P * n)) -
        (t * (nd / (d * (1 - P * n) ^ 2) - dd / d * (n / (d * (1 - P * n))) +
            P₁ * d * (n / (d * (1 - P * n))) ^ 2) +
          s * (P₂ * d * (n / (d * (1 - P * n))) ^ 2)) =
      (((Nt - n - t * nd) * (d * (1 - P * n)) -
            n * ((dT * (1 - PT * Nt) - d * (1 - P * n)) -
              (t * dd * (1 - P * n) - d * ((t * P₁ + s * P₂) * n + P * (t * nd))))) * (d * (1 - P * n)) -
          (t * nd * (d * (1 - P * n)) - n * (t * dd * (1 - P * n) - d * ((t * P₁ + s * P₂) * n + P * (t * nd)))) *
            (dT * (1 - PT * Nt) - d * (1 - P * n))) *
        (1 / (dT * (1 - PT * Nt))) * (1 / (d * (1 - P * n))) ^ 2 := by
  generalize hv : dT * (1 - PT * Nt) = v at hMt ⊢
  obtain ⟨u, hu⟩ : ∃ u, 1 - P * n = u := ⟨_, rfl⟩
  rw [hu] at hD ⊢
  field_simp
  rw [← hu]
  ring

open Asymptotics in
/-- Uniform first-order expansion of `N_t / (d_t (1 - P_t N_t))` on a set `K`, from a uniform Taylor bound for
`N_t` (holomorphic in `t`), `d_t` complex-differentiable and `P_t` real-differentiable (`P₁ = ∂_t`, `P₂ = ∂_t̄`). -/
theorem s3dv_comp_unif {K : Set ℂ} {N : ℂ → ℂ → ℂ} {n Nd dt Pt : ℂ → ℂ} {d P dd P₁ P₂ : ℂ} {ρ C B : ℝ}
    (hρ : 0 < ρ) (hN : ∀ t ∈ ball (0 : ℂ) ρ, ∀ z ∈ K, ‖N t z - n z - t * Nd z‖ ≤ C * ‖t‖ ^ 2)
    (hB : ∀ z ∈ K, ‖n z‖ ≤ B ∧ ‖Nd z‖ ≤ B ∧ ‖1 / (d * (1 - P * n z))‖ ≤ B)
    (hM : ∀ z ∈ K, d * (1 - P * n z) ≠ 0) (hd : HasDerivAt dt dd 0) (hd0 : dt 0 = d)
    (hP : (fun t => Pt t - P - (t * P₁ + conj t * P₂)) =o[𝓝 0] fun t => t) :
    ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ z ∈ K,
      ‖N t z / (dt t * (1 - Pt t * N t z)) - n z / (d * (1 - P * n z)) -
        (t * (Nd z / (d * (1 - P * n z) ^ 2) - dd / d * (n z / (d * (1 - P * n z))) +
            P₁ * d * (n z / (d * (1 - P * n z))) ^ 2) +
          conj t * (P₂ * d * (n z / (d * (1 - P * n z))) ^ 2))‖ ≤ ε * ‖t‖ := by
  intro ε hε
  set l : Filter (ℂ × ℂ) := 𝓝 (0 : ℂ) ×ˢ 𝓟 K with hl
  have hT : Tendsto (fun q : ℂ × ℂ => q.1) l (𝓝 0) := tendsto_fst
  have hK : ∀ᶠ q in l, q.2 ∈ K := eventually_prod_principal_iff.mpr (Eventually.of_forall fun _ _ hz => hz)
  have hρl : ∀ᶠ q in l, q.1 ∈ ball (0 : ℂ) ρ := hT.eventually (ball_mem_nhds 0 hρ)
  have hT1 : (fun q : ℂ × ℂ => q.1) =O[l] (fun _ => (1 : ℂ)) := hT.isBigO_one ℂ
  have hTo : (fun q : ℂ × ℂ => q.1) =o[l] (fun _ => (1 : ℂ)) := (isLittleO_one_iff ℂ).mpr hT
  have hTT : (fun q : ℂ × ℂ => q.1) =O[l] (fun q => q.1) := isBigO_refl _ _
  have hcT : (fun q : ℂ × ℂ => conj q.1) =O[l] (fun q => q.1) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun q => by simp)
  have hc1 : ∀ c : ℂ, (fun _ : ℂ × ℂ => c) =O[l] (fun _ => (1 : ℂ)) := fun c => isBigO_const_one ℂ c l
  have m11 : ∀ {f g : ℂ × ℂ → ℂ}, f =O[l] (fun _ => (1 : ℂ)) → g =O[l] (fun _ => (1 : ℂ)) →
      (fun q => f q * g q) =O[l] (fun _ => (1 : ℂ)) := fun hf hg =>
    (hf.mul hg).congr_right fun _ => one_mul 1
  have mT1 : ∀ {f g : ℂ × ℂ → ℂ}, f =O[l] (fun q => q.1) → g =O[l] (fun _ => (1 : ℂ)) →
      (fun q => f q * g q) =O[l] (fun q => q.1) := fun hf hg =>
    (hf.mul hg).congr_right fun _ => mul_one _
  have m1T : ∀ {f g : ℂ × ℂ → ℂ}, f =O[l] (fun _ => (1 : ℂ)) → g =O[l] (fun q => q.1) →
      (fun q => f q * g q) =O[l] (fun q => q.1) := fun hf hg =>
    (hf.mul hg).congr_right fun _ => one_mul _
  have oT1 : ∀ {f g : ℂ × ℂ → ℂ}, f =o[l] (fun q => q.1) → g =O[l] (fun _ => (1 : ℂ)) →
      (fun q => f q * g q) =o[l] (fun q => q.1) := fun hf hg =>
    (hf.mul_isBigO hg).congr_right fun _ => mul_one _
  have o1T : ∀ {f g : ℂ × ℂ → ℂ}, f =O[l] (fun _ => (1 : ℂ)) → g =o[l] (fun q => q.1) →
      (fun q => f q * g q) =o[l] (fun q => q.1) := fun hf hg =>
    (hf.mul_isLittleO hg).congr_right fun _ => one_mul _
  have TT : ∀ {f g : ℂ × ℂ → ℂ}, f =O[l] (fun q => q.1) → g =O[l] (fun q => q.1) →
      (fun q => f q * g q) =o[l] (fun q => q.1) := fun hf hg =>
    (hf.mul_isLittleO (hg.trans_isLittleO hTo)).congr_right fun _ => mul_one _
  have bdd : ∀ g : ℂ → ℂ, (∀ z ∈ K, ‖g z‖ ≤ B) → (fun q : ℂ × ℂ => g q.2) =O[l] (fun _ => (1 : ℂ)) := by
    intro g hg
    refine IsBigO.of_bound B ?_
    filter_upwards [hK] with q hq
    simpa using hg q.2 hq
  have hn1 := bdd n fun z hz => (hB z hz).1
  have hnd1 := bdd Nd fun z hz => (hB z hz).2.1
  have hiM1 := bdd (fun z => 1 / (d * (1 - P * n z))) fun z hz => (hB z hz).2.2
  have hD1 : (fun q : ℂ × ℂ => 1 - P * n q.2) =O[l] (fun _ => (1 : ℂ)) := (hc1 1).sub (m11 (hc1 P) hn1)
  have hM1 : (fun q : ℂ × ℂ => d * (1 - P * n q.2)) =O[l] (fun _ => (1 : ℂ)) := m11 (hc1 d) hD1
  -- first-order errors
  have heN : (fun q : ℂ × ℂ => N q.1 q.2 - n q.2 - q.1 * Nd q.2) =o[l] (fun q => q.1) := by
    have h1 : (fun q : ℂ × ℂ => N q.1 q.2 - n q.2 - q.1 * Nd q.2) =O[l] (fun q => q.1 ^ 2) := by
      refine IsBigO.of_bound C ?_
      filter_upwards [hK, hρl] with q hq hq'
      rw [norm_pow]; exact hN q.1 hq' q.2 hq
    exact h1.trans_isLittleO ((isLittleO_pow_id (by norm_num : 1 < 2)).comp_tendsto hT)
  have hed : (fun q : ℂ × ℂ => dt q.1 - d - q.1 * dd) =o[l] (fun q => q.1) := by
    have h1 := (hasDerivAt_iff_isLittleO_nhds_zero.mp hd).comp_tendsto hT
    refine h1.congr_left fun q => ?_
    simp [hd0, smul_eq_mul]
  have heP : (fun q : ℂ × ℂ => Pt q.1 - P - (q.1 * P₁ + conj q.1 * P₂)) =o[l] (fun q => q.1) :=
    hP.comp_tendsto hT
  -- linear parts and increments
  have hlN : (fun q : ℂ × ℂ => q.1 * Nd q.2) =O[l] (fun q => q.1) := mT1 hTT hnd1
  have hlP : (fun q : ℂ × ℂ => q.1 * P₁ + conj q.1 * P₂) =O[l] (fun q => q.1) :=
    (mT1 hTT (hc1 P₁)).add (mT1 hcT (hc1 P₂))
  have hΔN : (fun q : ℂ × ℂ => N q.1 q.2 - n q.2) =O[l] (fun q => q.1) :=
    (heN.isBigO.add hlN).congr_left fun q => by ring
  have hΔd : (fun q : ℂ × ℂ => dt q.1 - d) =O[l] (fun q => q.1) :=
    (hed.isBigO.add (mT1 hTT (hc1 dd))).congr_left fun q => by ring
  have hΔP : (fun q : ℂ × ℂ => Pt q.1 - P) =O[l] (fun q => q.1) :=
    (heP.isBigO.add hlP).congr_left fun q => by ring
  have hNt1 : (fun q : ℂ × ℂ => N q.1 q.2) =O[l] (fun _ => (1 : ℂ)) :=
    (hn1.add (hΔN.trans hT1)).congr_left fun q => by ring
  -- the denominator
  set ℓM : ℂ × ℂ → ℂ := fun q => q.1 * dd * (1 - P * n q.2) -
      d * ((q.1 * P₁ + conj q.1 * P₂) * n q.2 + P * (q.1 * Nd q.2)) with hℓM
  have hlM : ℓM =O[l] (fun q => q.1) :=
    (mT1 (mT1 hTT (hc1 dd)) hD1).sub (m1T (hc1 d) ((mT1 hlP hn1).add (m1T (hc1 P) hlN)))
  have heM : (fun q : ℂ × ℂ => (dt q.1 * (1 - Pt q.1 * N q.1 q.2) - d * (1 - P * n q.2)) - ℓM q) =o[l]
      (fun q => q.1) := by
    have h := ((((oT1 hed hD1).sub (o1T (hc1 d) (oT1 heP hn1))).sub (o1T (hc1 d) (TT hΔP hΔN))).sub
      (o1T (hc1 (d * P)) heN)).sub (TT hΔd ((mT1 hΔP hNt1).add (m1T (hc1 P) hΔN)))
    refine h.congr_left fun q => ?_
    simp only [hℓM]
    ring
  have hΔM : (fun q : ℂ × ℂ => dt q.1 * (1 - Pt q.1 * N q.1 q.2) - d * (1 - P * n q.2)) =O[l]
      (fun q => q.1) :=
    (heM.isBigO.add hlM).congr_left fun q => by ring
  -- lower bound for the moving denominator
  set B' := max B 1 with hB'
  have hB'0 : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsmall : ∀ᶠ q in l, ‖dt q.1 * (1 - Pt q.1 * N q.1 q.2) - d * (1 - P * n q.2)‖ < 1 / (2 * B') := by
    have h := (hΔM.trans_tendsto hT).eventually (ball_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < 1 / (2 * B')))
    filter_upwards [h] with q hq
    simpa using hq
  have hlow : ∀ᶠ q in l, dt q.1 * (1 - Pt q.1 * N q.1 q.2) ≠ 0 ∧
      ‖1 / (dt q.1 * (1 - Pt q.1 * N q.1 q.2))‖ ≤ 2 * B' := by
    filter_upwards [hK, hsmall] with q hq hs
    obtain ⟨-, -, hb⟩ := hB q.2 hq
    have hM0 := hM q.2 hq
    set M := d * (1 - P * n q.2) with hMdef
    set Mt := dt q.1 * (1 - Pt q.1 * N q.1 q.2) with hMtdef
    have hpos : 0 < ‖M‖ := norm_pos_iff.mpr hM0
    have hge : 1 / B' ≤ ‖M‖ := by
      rw [norm_div, norm_one] at hb
      exact (one_div_le hpos hB'0).mp (hb.trans (le_max_left _ _))
    have h2 := norm_sub_norm_le M Mt
    rw [norm_sub_rev] at h2
    have hhalf : 1 / (2 * B') = 1 / B' - 1 / (2 * B') := by field_simp; ring
    have hgt : 1 / (2 * B') ≤ ‖Mt‖ := by linarith
    have hMtpos : 0 < ‖Mt‖ := lt_of_lt_of_le (by positivity) hgt
    refine ⟨norm_pos_iff.mp hMtpos, ?_⟩
    rw [norm_div, norm_one]
    exact (one_div_le hMtpos (by positivity)).mpr hgt
  have hiMt1 : (fun q : ℂ × ℂ => 1 / (dt q.1 * (1 - Pt q.1 * N q.1 q.2))) =O[l] (fun _ => (1 : ℂ)) :=
    IsBigO.of_bound (2 * B') (hlow.mono fun q h => by simpa using h.2)
  -- the remainder
  have hR : (fun q : ℂ × ℂ =>
      (((N q.1 q.2 - n q.2 - q.1 * Nd q.2) * (d * (1 - P * n q.2)) -
          n q.2 * ((dt q.1 * (1 - Pt q.1 * N q.1 q.2) - d * (1 - P * n q.2)) - ℓM q)) * (d * (1 - P * n q.2)) -
        (q.1 * Nd q.2 * (d * (1 - P * n q.2)) - n q.2 * ℓM q) *
          (dt q.1 * (1 - Pt q.1 * N q.1 q.2) - d * (1 - P * n q.2))) *
      (1 / (dt q.1 * (1 - Pt q.1 * N q.1 q.2))) * (1 / (d * (1 - P * n q.2))) ^ 2) =o[l] (fun q => q.1) := by
    have h1 := oT1 ((oT1 heN hM1).sub (o1T hn1 heM)) hM1
    have h2 := TT ((mT1 hlN hM1).sub (m1T hn1 hlM)) hΔM
    exact oT1 (oT1 (h1.sub h2) hiMt1) ((m11 hiM1 hiM1).congr_left fun q => by ring)
  have hE : (fun q : ℂ × ℂ =>
      N q.1 q.2 / (dt q.1 * (1 - Pt q.1 * N q.1 q.2)) - n q.2 / (d * (1 - P * n q.2)) -
        (q.1 * (Nd q.2 / (d * (1 - P * n q.2) ^ 2) - dd / d * (n q.2 / (d * (1 - P * n q.2))) +
            P₁ * d * (n q.2 / (d * (1 - P * n q.2))) ^ 2) +
          conj q.1 * (P₂ * d * (n q.2 / (d * (1 - P * n q.2))) ^ 2))) =o[l] (fun q => q.1) := by
    refine hR.congr' ?_ EventuallyEq.rfl
    filter_upwards [hK, hlow] with q hq hlq
    have hM0 := hM q.2 hq
    exact (s3dv_comp_alg (left_ne_zero_of_mul hM0) (right_ne_zero_of_mul hM0) hlq.1).symm
  have h := eventually_prod_principal_iff.mp (hE.def hε)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨δ, hδ, fun t ht z hz => hδ' (by simpa using ht) z hz⟩

open Asymptotics in
/-- **(V-A-f)** Uniform first-order expansion of `𝖿_t` on closed discs `|z| ≤ r < 1`, with the explicit pole
pair `Q₁ = I₂ + P₁ d`, `Q₂ = P₂ d` (shared with the g-side `s3dv_expand_g`). -/
theorem s3dv_expand_f {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (m : ℂ → ℂ) :
    ∀ r : ℝ, r < 1 → ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ z ∈ closedBall (0 : ℂ) r,
      ‖fsans (beltramiMul (a + t • toLinf m) κ) z - fsans (beltramiMul a κ) z -
        (t * ((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) + (((1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 * ((deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0))) * (s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) / (gsans (beltramiMul a κ) u * (1 + (s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) * gsans (beltramiMul a κ) u) * ((deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0))) * gsans (beltramiMul a κ) u - 1)))) + dz (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) 0 * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) * fsans (beltramiMul a κ) z ^ 2) + conj t * ((dzbar (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) 0 * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) * fsans (beltramiMul a κ) z ^ 2))‖ ≤ ε * ‖t‖ := by
  intro r hr ε hε
  have hμ : beltramiMul a κ ∈ LinfStarBall := bg_mul_mem_ball hκ ha
  have hd0 : deriv (normalizedSolution (extB (beltramiMul a κ))) 0 ≠ 0 := (AppA.acc_wB_rep hμ).1
  obtain ⟨ρ, hρ, hcd, hcm⟩ := s3dv_line hκ ha (toLinf m)
  have hc0 : beltramiMul (a + (0 : ℂ) • toLinf m) κ = beltramiMul a κ := by rw [zero_smul, add_zero]
  have hK : IsCompact (closedBall (0 : ℂ) r) := isCompact_closedBall 0 r
  have hKD : closedBall (0 : ℂ) r ⊆ unitDisc := fun z hz => by
    have := closedBall_subset_ball hr hz
    simpa [unitDisc] using this
  obtain ⟨C, hC⟩ := s3dv_W_taylor hρ hcd hcm hK
  simp only [hc0] at hC
  obtain ⟨-, hWhol, -, -⟩ := QCV.qcv_W_props (mem_ball_zero_iff.mp hμ)
  obtain ⟨hWdo, -, -⟩ := s3dv_Wdot_holo hκ ha (toLinf m)
  have hMne : ∀ z ∈ closedBall (0 : ℂ) r, deriv (normalizedSolution (extB (beltramiMul a κ))) 0 *
      (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ))
        (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * normalizedSolution (extB (beltramiMul a κ)) z) ≠ 0 :=
    fun z hz => mul_ne_zero hd0 (s3dv_frep hμ (hKD hz)).1
  have hWc : ContinuousOn (normalizedSolution (extB (beltramiMul a κ))) (closedBall 0 r) :=
    hWhol.continuousOn.mono hKD
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn hWc
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn (hWdo.continuousOn.mono hKD)
  obtain ⟨B3, hB3⟩ := hK.exists_bound_of_continuousOn
    (continuousOn_const.div (continuousOn_const.mul (continuousOn_const.sub (continuousOn_const.mul hWc))) hMne)
  have hνd := s35wn_nu_diff hκ ha (toLinf m)
  obtain ⟨dt, hdt⟩ : ∃ f : ℂ → ℂ,
      f = fun t : ℂ => deriv (normalizedSolution (extB (beltramiMul (a + t • toLinf m) κ))) 0 := ⟨_, rfl⟩
  obtain ⟨Pt, hPt⟩ : ∃ f : ℂ → ℂ, f = fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ,
      star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ,
        star (beltramiMul (a + t • toLinf m) κ)) 0) := ⟨_, rfl⟩
  have h0b : beltramiMul (a + (0 : ℂ) • toLinf m) κ ∈ LinfStarBall := by rw [hc0]; exact hμ
  have hdtd : DifferentiableAt ℂ dt 0 := by
    rw [hdt]; exact (s5cf_planeB_deriv_analytic h0b).differentiableAt.comp (0 : ℂ) hνd
  have hdt0 : dt 0 = deriv (normalizedSolution (extB (beltramiMul a κ))) 0 := by rw [hdt]; simp only [hc0]
  have hPtd : DifferentiableAt ℝ Pt 0 := by
    rw [hPt]; exact (s5t53_P_analytic h0b).differentiableAt.comp (0 : ℂ) (hνd.restrictScalars ℝ)
  have hPt0 : Pt 0 = s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ))
      (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) := by
    rw [hPt]; simp only [hc0]
  have hPo : (fun t => Pt t - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ))
      (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) - (t * dz Pt 0 + conj t * dzbar Pt 0)) =o[𝓝 0]
      fun t => t := by
    have h := hasFDerivAt_iff_isLittleO_nhds_zero.mp hPtd.hasFDerivAt
    refine h.congr_left fun t => ?_
    rw [zero_add, hPt0, fderiv_eq_dz_dzbar hPtd t]
    ring
  obtain ⟨δ₁, hδ₁, hb⟩ := s3dv_comp_unif (B := max B1 (max B2 B3)) (half_pos hρ) hC
    (fun z hz => ⟨(hB1 z hz).trans (le_max_left _ _),
      (hB2 z hz).trans ((le_max_left _ _).trans (le_max_right _ _)),
      (hB3 z hz).trans ((le_max_right _ _).trans (le_max_right _ _))⟩) hMne hdtd.hasDerivAt hdt0 hPo ε hε
  refine ⟨min δ₁ (ρ / 2), lt_min hδ₁ (half_pos hρ), fun t ht z hz => ?_⟩
  have htρ : t ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff]; exact lt_of_lt_of_le ht ((min_le_right _ _).trans (half_le_self hρ.le))
  have h := hb t (lt_of_lt_of_le ht (min_le_left _ _)) z hz
  have hzD := hKD hz
  have h1 := s3dv_fiden hκ ha rfl (toLinf m) hzD
  rw [s3dv_norm hκ ha (toLinf m)] at h1
  simp only [s3dv_RF ha (toLinf m)] at h1
  obtain ⟨-, hft⟩ := s3dv_frep (μ := beltramiMul (a + t • toLinf m) κ) (hcm htρ) hzD
  obtain ⟨-, hf0⟩ := s3dv_frep hμ hzD
  subst hdt hPt
  beta_reduce at h
  rw [hft]
  refine le_of_eq_of_le ?_ h
  congr 1
  rw [← hf0]
  linear_combination t * h1


/-- [(E2) helper] A uniform first-order expansion `F t = c₀ + t A + t̄ B + o(t)` gives `F 0 = c₀` and the real
derivative `t ↦ A t + B t̄` at `0`. -/
theorem s3d2u_hasFDeriv {F : ℂ → ℂ} {A B c0 : ℂ}
    (h : ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ‖F t - c0 - (t * A + conj t * B)‖ ≤ ε * ‖t‖) :
    F 0 = c0 ∧ HasFDerivAt F (A • (1 : ℂ →L[ℝ] ℂ) + B • (conjCLE : ℂ →L[ℝ] ℂ)) 0 := by
  have h0 : F 0 = c0 := by
    obtain ⟨δ, hδ, hb⟩ := h 1 one_pos
    have h1 := hb 0 (by rw [norm_zero]; exact hδ)
    simp only [norm_zero, mul_zero, map_zero, zero_mul, add_zero, sub_zero] at h1
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
  refine ⟨h0, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.isLittleO_iff.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hb⟩ := h ε hε
  filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with t ht
  rw [mem_ball_zero_iff] at ht
  have e : F (0 + t) - F 0 - (A • (1 : ℂ →L[ℝ] ℂ) + B • (conjCLE : ℂ →L[ℝ] ℂ)) t =
      F t - c0 - (t * A + conj t * B) := by
    rw [zero_add, h0]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul]
    ring
  rw [e]
  exact hb t ht

/-- [(E2) helper] The Wirtinger derivatives of a map with real derivative `t ↦ A t + B t̄` at `0`. -/
theorem s3d2u_dz {F : ℂ → ℂ} {A B : ℂ}
    (h : HasFDerivAt F (A • (1 : ℂ →L[ℝ] ℂ) + B • (conjCLE : ℂ →L[ℝ] ℂ)) 0) :
    dz F 0 = A ∧ dzbar F 0 = B := by
  have e1 : fderiv ℝ F 0 1 = A + B := by
    rw [h.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul, map_one]
    ring
  have e2 : fderiv ℝ F 0 I = A * I - B * I := by
    rw [h.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul, conj_I]
    ring
  refine ⟨?_, ?_⟩
  · show (fderiv ℝ F 0 1 - I * fderiv ℝ F 0 I) / 2 = A
    rw [e1, e2]
    linear_combination (B - A) / 2 * I_sq
  · show (fderiv ℝ F 0 1 + I * fderiv ℝ F 0 I) / 2 = B
    rw [e1, e2]
    linear_combination (A - B) / 2 * I_sq

/-- [(E2) helper] Quotient rule for real derivatives of the shape `t ↦ A t + B t̄` at `0`. -/
theorem s3d2u_div {F1 F2 : ℂ → ℂ} {A1 B1 A2 B2 c1 c2 : ℂ}
    (h1 : HasFDerivAt F1 (A1 • (1 : ℂ →L[ℝ] ℂ) + B1 • (conjCLE : ℂ →L[ℝ] ℂ)) 0)
    (h2 : HasFDerivAt F2 (A2 • (1 : ℂ →L[ℝ] ℂ) + B2 • (conjCLE : ℂ →L[ℝ] ℂ)) 0)
    (hc1 : F1 0 = c1) (hc2 : F2 0 = c2) (h0 : c1 ≠ 0) :
    HasFDerivAt (fun t => F2 t / F1 t) (((A2 * c1 - A1 * c2) / c1 ^ 2) • (1 : ℂ →L[ℝ] ℂ) +
      ((B2 * c1 - B1 * c2) / c1 ^ 2) • (conjCLE : ℂ →L[ℝ] ℂ)) 0 := by
  subst hc1 hc2
  have hinv : HasFDerivAt (fun x : ℂ => x⁻¹) ((-(F1 0 ^ 2)⁻¹) • (1 : ℂ →L[ℝ] ℂ)) (F1 0) := by
    refine (((hasDerivAt_inv h0).hasFDerivAt).restrictScalars ℝ).congr_fderiv
      (ContinuousLinearMap.ext fun t => ?_)
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hm := h2.mul (hinv.comp (0 : ℂ) h1)
  have e : (fun t => F2 t / F1 t) = F2 * ((fun x : ℂ => x⁻¹) ∘ F1) :=
    funext fun t => by rw [Pi.mul_apply, Function.comp_apply, div_eq_mul_inv]
  rw [e]
  refine hm.congr_fderiv (ContinuousLinearMap.ext fun t => ?_)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul, Function.comp_apply]
  field_simp
  ring

/-- [(E2) helper] Cauchy estimate step: a uniform expansion `G t = G₀ + t X + t̄ Y + o(t)` on `closedBall c (2s)` of
holomorphic maps passes to the `z`-derivatives on `closedBall c s`. -/
theorem s3d2u_step {G : ℂ → ℂ → ℂ} {G0 X Y : ℂ → ℂ} {c : ℂ} {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hG : ∀ t : ℂ, ‖t‖ < r → DifferentiableOn ℂ (G t) (ball c (3 * s)))
    (hG0 : DifferentiableOn ℂ G0 (ball c (3 * s))) (hX : DifferentiableOn ℂ X (ball c (3 * s)))
    (hY : DifferentiableOn ℂ Y (ball c (3 * s)))
    (hV : ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ w ∈ closedBall c (2 * s),
      ‖G t w - G0 w - (t * X w + conj t * Y w)‖ ≤ ε * ‖t‖) :
    ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ w ∈ closedBall c s,
      ‖deriv (G t) w - deriv G0 w - (t * deriv X w + conj t * deriv Y w)‖ ≤ ε * ‖t‖ := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hV (ε * s) (mul_pos hε hs)
  refine ⟨min δ r, lt_min hδ hr, fun t ht w hw => ?_⟩
  have htδ : ‖t‖ < δ := lt_of_lt_of_le ht (min_le_left _ _)
  have htr : ‖t‖ < r := lt_of_lt_of_le ht (min_le_right _ _)
  have hφ : DifferentiableOn ℂ (fun u => G t u - G0 u - (t * X u + conj t * Y u)) (ball c (3 * s)) :=
    ((hG t htr).sub hG0).sub (((differentiableOn_const t).mul hX).add ((differentiableOn_const (conj t)).mul hY))
  have hsub : closedBall w s ⊆ ball c (3 * s) := by
    intro u hu
    rw [mem_closedBall] at hu hw
    rw [mem_ball]
    calc dist u c ≤ dist u w + dist w c := dist_triangle u w c
      _ < 3 * s := by linarith
  have hsub2 : sphere w s ⊆ closedBall c (2 * s) := by
    intro u hu
    rw [mem_sphere] at hu
    rw [mem_closedBall] at hw ⊢
    calc dist u c ≤ dist u w + dist w c := dist_triangle u w c
      _ ≤ 2 * s := by linarith
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs (hφ.diffContOnCl_ball hsub)
    (fun u hu => hb t htδ u (hsub2 hu))
  have hn : ball c (3 * s) ∈ 𝓝 w := isOpen_ball.mem_nhds (hsub (mem_closedBall_self hs.le))
  have hd : deriv (fun u => G t u - G0 u - (t * X u + conj t * Y u)) w =
      deriv (G t) w - deriv G0 w - (t * deriv X w + conj t * deriv Y w) :=
    ((((hG t htr).differentiableAt hn).hasDerivAt.sub (hG0.differentiableAt hn).hasDerivAt).sub
      ((((hX.differentiableAt hn).hasDerivAt).const_mul t).add
        (((hY.differentiableAt hn).hasDerivAt).const_mul (conj t)))).deriv
  rw [← hd]
  calc _ ≤ ε * s * ‖t‖ / s := hC
    _ = ε * ‖t‖ := by field_simp

/-- [(E2) helper] `(η' + 𝒜(g) η)' = (X'' g' - X' g'')/g'²` for `η = X/g'` on an open set where `g' ≠ 0`. -/
theorem s3d2u_rhs {g X : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (hg : DifferentiableOn ℂ g U) (hX : DifferentiableOn ℂ X U) (hne : ∀ x ∈ U, deriv g x ≠ 0) :
    deriv (fun x => deriv (fun y => X y / deriv g y) x + preSchwarzian g x * (X x / deriv g x)) z =
      (deriv (deriv X) z * deriv g z - deriv X z * deriv (deriv g) z) / deriv g z ^ 2 := by
  have hg1 := hg.deriv hU
  have hX1 := hX.deriv hU
  have heq : (fun x => deriv (fun y => X y / deriv g y) x + preSchwarzian g x * (X x / deriv g x)) =ᶠ[𝓝 z]
      fun x => deriv X x / deriv g x := by
    filter_upwards [hU.mem_nhds hz] with x hx
    have hn : U ∈ 𝓝 x := hU.mem_nhds hx
    have hd : HasDerivAt (fun y => X y / deriv g y)
        ((deriv X x * deriv g x - X x * deriv (deriv g) x) / deriv g x ^ 2) x :=
      (hX.differentiableAt hn).hasDerivAt.div (hg1.differentiableAt hn).hasDerivAt (hne x hx)
    rw [hd.deriv]
    have e : preSchwarzian g x = deriv (deriv g) x / deriv g x := rfl
    rw [e]
    have h0 := hne x hx
    field_simp
    ring
  have hn : U ∈ 𝓝 z := hU.mem_nhds hz
  have hd : HasDerivAt (fun x => deriv X x / deriv g x)
      ((deriv (deriv X) z * deriv g z - deriv X z * deriv (deriv g) z) / deriv g z ^ 2) z :=
    (hX1.differentiableAt hn).hasDerivAt.div (hg1.differentiableAt hn).hasDerivAt (hne z hz)
  rw [heq.deriv_eq, hd.deriv]

/-- [(V-B) helper] The exterior reciprocal chart at `z⁻¹`, `|z| > 1`: `E(μ, μ̄)(z⁻¹) = 1/𝗀_μ(z)`. -/
theorem s3d5_recip {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : 1 < ‖z‖) :
    s5cf_exterior_reciprocal (μ, star μ) z⁻¹ = (gsans μ z)⁻¹ := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; linarith
  have ht : z⁻¹ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz)
  rw [← s5cf_gchart_eq hμ ht, S2C.s2c_gsans_eq hμ]
  simp only [s5cf_gchart, inv_eq_zero, hz0, ite_false, inv_inv]

/-- [(V-B) helper] `𝗀_μ'(∞) ≠ 0`, `𝗀_μ(z)/z → 𝗀_μ'(∞)` and `𝗀_μ'(z) → 𝗀_μ'(∞)` at `∞`, from the exterior reciprocal
chart (analytic at `0`, value `0`, nonzero derivative). -/
theorem s3d5_asym {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    derivAtInfty (gsans μ) ≠ 0 ∧ Tendsto (fun z => gsans μ z / z) (cocompact ℂ) (𝓝 (derivAtInfty (gsans μ))) ∧
      Tendsto (fun z => deriv (gsans μ) z) (cocompact ℂ) (𝓝 (derivAtInfty (gsans μ))) := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  set E : ℂ → ℂ := fun w => s5cf_exterior_reciprocal (μ, star μ) w with hE
  have hd : deriv E 0 ≠ 0 := s5cf_exterior_reciprocal_deriv_ne_zero hμ h0
  have ha : AnalyticAt ℂ E 0 :=
    (s5cf_exterior_reciprocal_analytic hμ h0).comp (analyticAt_const.prod analyticAt_id)
  have hE0 : E 0 = 0 := by simp [hE, s5cf_exterior_reciprocal]
  have hb : derivAtInfty (gsans μ) = (deriv E 0)⁻¹ := s35wn_derivAtInfty hμ
  rw [hb]
  have ht : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    · filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
      exact inv_ne_zero (by simpa using hz)
  have ht0 : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := ht.mono_right nhdsWithin_le_nhds
  have hsl := ha.differentiableAt.hasDerivAt.tendsto_slope.comp ht
  have hext : ∀ᶠ z : ℂ in cocompact ℂ, 1 < ‖z‖ := tendsto_norm_cocompact_atTop.eventually_gt_atTop 1
  have hrec : ∀ z : ℂ, 1 < ‖z‖ → E z⁻¹ = (gsans μ z)⁻¹ := fun z hz => s3d5_recip hμ hz
  have hg0 : ∀ z : ℂ, 1 < ‖z‖ → gsans μ z ≠ 0 := fun z hz h => by
    obtain ⟨ε, hε, -, hl⟩ := s3d5_lower hμ
    have h1 := hl z hz.le
    rw [← gMu_eq_normalizedWeldingExterior hμ hz, ← S2C.s2c_gsans_eq hμ, h, norm_zero] at h1
    linarith
  have hsl_eq : ∀ z : ℂ, 1 < ‖z‖ → slope E 0 z⁻¹ = (gsans μ z / z)⁻¹ := fun z hz => by
    rw [slope_def_field, hE0, sub_zero, sub_zero, hrec z hz]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
  have h1 : Tendsto (fun z => gsans μ z / z) (cocompact ℂ) (𝓝 (deriv E 0)⁻¹) := by
    refine (hsl.inv₀ hd).congr' ?_
    filter_upwards [hext] with z hz
    simp only [Function.comp_apply]
    rw [hsl_eq z hz, inv_inv]
  have hderiv : ∀ z : ℂ, 1 < ‖z‖ → deriv (gsans μ) z = deriv E z⁻¹ / (slope E 0 z⁻¹) ^ 2 := fun z hz => by
    have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; linarith
    have hs : z⁻¹ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz)
    have hEa : AnalyticAt ℂ E z⁻¹ :=
      (s5cf_exterior_reciprocal_analytic hμ hs).comp (analyticAt_const.prod analyticAt_id)
    have hc := hEa.differentiableAt.hasDerivAt.comp z (hasDerivAt_inv hz0)
    have hne : (E ∘ fun x : ℂ => x⁻¹) z ≠ 0 := by
      simp only [Function.comp_apply]
      rw [hrec z hz]
      exact inv_ne_zero (hg0 z hz)
    have hi := hc.inv hne
    have hev : gsans μ =ᶠ[𝓝 z] fun y => ((E ∘ fun x : ℂ => x⁻¹) y)⁻¹ := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with y hy
      simp only [Function.comp_apply]
      rw [hrec y hy, inv_inv]
    have hi' : HasDerivAt (fun y => ((E ∘ fun x : ℂ => x⁻¹) y)⁻¹)
        (-(deriv E z⁻¹ * -(z ^ 2)⁻¹) / (E ∘ fun x : ℂ => x⁻¹) z ^ 2) z := hi
    rw [hev.deriv_eq, hi'.deriv]
    simp only [Function.comp_apply]
    rw [slope_def_field, hE0, sub_zero, sub_zero, hrec z hz]
    have := hg0 z hz
    field_simp
  have h2 : Tendsto (fun z => deriv (gsans μ) z) (cocompact ℂ) (𝓝 (deriv E 0)⁻¹) := by
    have hc : Tendsto (fun z : ℂ => deriv E z⁻¹) (cocompact ℂ) (𝓝 (deriv E 0)) :=
      ha.deriv.continuousAt.tendsto.comp ht0
    have h3 := hc.div (hsl.pow 2) (pow_ne_zero 2 hd)
    have e : deriv E 0 / deriv E 0 ^ 2 = (deriv E 0)⁻¹ := by field_simp
    rw [e] at h3
    refine h3.congr' ?_
    filter_upwards [hext] with z hz
    rw [hderiv z hz]
    rfl
  exact ⟨inv_ne_zero hd, h1, h2⟩

/-- [(V-B) helper] Growth of the first variation of `𝗀` at `∞` from the exterior reciprocal chart: for large `|z|`,
`t ↦ 𝗀_{ν_t}(z)` (with `ν_t = (a + t μ) * κ`) has a real derivative at `0` of norm `≤ C |z|`. Through
`𝗀_t(z) = 1/E(p_t, z⁻¹)`, the derivative is `-𝗀(z)² ∂_p E(p₀, z⁻¹) ṗ`, and `∂_p E(p₀, ·)` vanishes at `0`. -/
theorem s3d5_chart {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (μ : LinfStar) :
    ∃ C : ℝ, ∀ᶠ z in cocompact ℂ, ∃ L : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun t : ℂ => gsans (beltramiMul (a + t • μ) κ) z) L 0 ∧ ∀ v : ℂ, ‖L v‖ ≤ C * ‖z‖ * ‖v‖ := by
  have hν0 : beltramiMul a κ ∈ LinfStarBall := bg_mul_mem_ball hκ ha
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have h0D : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  set p₀ : LinfStar × LinfStar := (beltramiMul a κ, star (beltramiMul a κ)) with hp₀
  set Ê : (LinfStar × LinfStar) × ℂ → ℂ := fun q => s5cf_exterior_reciprocal q.1 q.2 with hÊ
  have hA0 : AnalyticAt ℂ Ê (p₀, 0) := s5cf_exterior_reciprocal_analytic hν0 h0D
  set φ : ℂ → (LinfStar × LinfStar →L[ℂ] ℂ) := fun s =>
    (fderiv ℂ Ê (p₀, s)).comp (ContinuousLinearMap.inl ℂ (LinfStar × LinfStar) ℂ) with hφ
  have hφd : DifferentiableAt ℂ φ 0 := by
    have h1 : DifferentiableAt ℂ (fun s : ℂ => fderiv ℂ Ê (p₀, s)) 0 :=
      hA0.fderiv.differentiableAt.comp (0 : ℂ) (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => (p₀, s)) 0)
    exact h1.clm_comp (differentiableAt_const _)
  have hφ0 : φ 0 = 0 := by
    have hc : HasFDerivAt (fun q : LinfStar × LinfStar => Ê (q, 0)) (φ 0) p₀ :=
      HasFDerivAt.comp (g := Ê) (f := fun q : LinfStar × LinfStar => (q, (0 : ℂ))) p₀
        hA0.differentiableAt.hasFDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℂ) p₀ (0 : ℂ))
    have hz : (fun q : LinfStar × LinfStar => Ê (q, 0)) = fun _ => 0 :=
      funext fun q => by simp [hÊ, s5cf_exterior_reciprocal]
    rw [hz] at hc
    exact hc.unique (hasFDerivAt_const _ _)
  obtain ⟨C₁, hC₁⟩ := hφd.isBigO_sub.bound
  set P : ℂ → LinfStar × LinfStar := fun t =>
    (beltramiMul (a + t • μ) κ, star (beltramiMul (a + t • μ) κ)) with hP
  have hP0 : P 0 = p₀ := by simp [hP, hp₀]
  have hPd : DifferentiableAt ℝ P 0 := by
    have hν : DifferentiableAt ℝ (fun t : ℂ => beltramiMul (a + t • μ) κ) 0 :=
      (s35wn_nu_diff hκ ha μ).restrictScalars ℝ
    have hs : DifferentiableAt ℝ (fun t : ℂ => star (beltramiMul (a + t • μ) κ)) 0 :=
      DifferentiableAt.comp (g := fun ν : LinfStar => star ν) (0 : ℂ)
        (s5cf_star_analytic (beltramiMul (a + (0 : ℂ) • μ) κ)).differentiableAt hν
    exact hν.prodMk hs
  set DP := fderiv ℝ P 0 with hDP
  obtain ⟨K, hK, hgrow⟩ := s3d5_growth hν0
  have hinv0 : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  refine ⟨K ^ 2 * C₁ * ‖DP‖, ?_⟩
  filter_upwards [hgrow, hinv0.eventually hC₁, tendsto_norm_cocompact_atTop.eventually_gt_atTop 1]
    with z hgz hφz hz1
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
  have hsD : z⁻¹ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1)
  have hAs : HasFDerivAt Ê ((fderiv ℂ Ê (p₀, z⁻¹)).restrictScalars ℝ) (P 0, z⁻¹) := by
    rw [hP0]
    exact (s5cf_exterior_reciprocal_analytic hν0 hsD).differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hFs := hAs.comp (0 : ℂ) (hPd.hasFDerivAt.prodMk (hasFDerivAt_const z⁻¹ (0 : ℂ)))
  set c : ℂ := Ê (P 0, z⁻¹) with hc
  have hcg : c = (gsans (beltramiMul a κ) z)⁻¹ := by
    rw [hc, hP0]
    exact s3d5_recip hν0 hz1
  have hg0 : gsans (beltramiMul a κ) z ≠ 0 := by
    intro h
    obtain ⟨ε, hε, -, hl⟩ := s3d5_lower hν0
    have h1 := hl z hz1.le
    rw [← gMu_eq_normalizedWeldingExterior hν0 hz1, ← S2C.s2c_gsans_eq hν0, h, norm_zero] at h1
    linarith
  have hc0 : c ≠ 0 := by rw [hcg]; exact inv_ne_zero hg0
  have hinv : HasFDerivAt (fun x : ℂ => x⁻¹) ((-(c ^ 2)⁻¹) • (1 : ℂ →L[ℝ] ℂ)) c := by
    refine (((hasDerivAt_inv hc0).hasFDerivAt).restrictScalars ℝ).congr_fderiv
      (ContinuousLinearMap.ext fun t => ?_)
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hL := hinv.comp (0 : ℂ) hFs
  refine ⟨_, hL.congr_of_eventuallyEq ?_, fun v => ?_⟩
  · filter_upwards [s35wn_mem hκ ha1 μ] with t ht
    show gsans (beltramiMul (a + t • μ) κ) z = (s5cf_exterior_reciprocal (P t) z⁻¹)⁻¹
    rw [hP]
    dsimp only
    rw [s3d5_recip ht.2 hz1, inv_inv]
  · have hφv : (fderiv ℂ Ê (p₀, z⁻¹)) (DP v, 0) = φ z⁻¹ (DP v) := rfl
    have hφs : ‖φ z⁻¹‖ ≤ C₁ * ‖z‖⁻¹ := by
      have h1 := hφz
      rw [hφ0, sub_zero, sub_zero, norm_inv] at h1
      exact h1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
      smul_eq_mul, norm_mul, norm_neg, norm_inv, norm_pow, hφv, ← hDP]
    have hcn : ‖c‖⁻¹ = ‖gsans (beltramiMul a κ) z‖ := by rw [hcg, norm_inv, inv_inv]
    have e1 : (‖c‖ ^ 2)⁻¹ = ‖gsans (beltramiMul a κ) z‖ ^ 2 := by rw [← hcn, inv_pow]
    rw [e1]
    have h2 : ‖φ z⁻¹ (DP v)‖ ≤ C₁ * ‖z‖⁻¹ * (‖DP‖ * ‖v‖) :=
      ((φ z⁻¹).le_opNorm _).trans
        (mul_le_mul hφs (DP.le_opNorm v) (norm_nonneg _) ((norm_nonneg _).trans hφs))
    have h3 : ‖gsans (beltramiMul a κ) z‖ ^ 2 ≤ (K * ‖z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgz 2
    calc ‖gsans (beltramiMul a κ) z‖ ^ 2 * ‖φ z⁻¹ (DP v)‖
        ≤ (K * ‖z‖) ^ 2 * (C₁ * ‖z‖⁻¹ * (‖DP‖ * ‖v‖)) :=
          mul_le_mul h3 h2 (norm_nonneg _) (by positivity)
      _ = K ^ 2 * C₁ * ‖DP‖ * ‖z‖ * ‖v‖ := by
          have : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
          field_simp

/-- [(V-B) helper] Pinning from growth: if `G t z = g z + t A(z) + t̄ B(z) + o(t)` for each `|z| > 1`, and the real
derivative of `t ↦ G t z` at `0` is `O(|z|)` near `∞`, then `A(z)/z² → 0` and `B(z)/z² → 0`. -/
theorem s3d5_pin_core {G : ℂ → ℂ → ℂ} {g A B : ℂ → ℂ} {C : ℝ}
    (hexp : ∀ z : ℂ, 1 < ‖z‖ → ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ →
      ‖G t z - g z - (t * A z + conj t * B z)‖ ≤ ε * ‖t‖)
    (hch : ∀ᶠ z in cocompact ℂ, ∃ L : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun t : ℂ => G t z) L 0 ∧ ∀ v : ℂ, ‖L v‖ ≤ C * ‖z‖ * ‖v‖) :
    Tendsto (fun z => A z / z ^ 2) (cocompact ℂ) (𝓝 0) ∧ Tendsto (fun z => B z / z ^ 2) (cocompact ℂ) (𝓝 0) := by
  have hb : ∀ᶠ z in cocompact ℂ, ‖A z / z ^ 2‖ ≤ C * ‖z‖⁻¹ ∧ ‖B z / z ^ 2‖ ≤ C * ‖z‖⁻¹ := by
    filter_upwards [hch, tendsto_norm_cocompact_atTop.eventually_gt_atTop 1] with z hz hz1
    obtain ⟨L, hL, hLb⟩ := hz
    obtain ⟨-, hd⟩ := s3d2u_hasFDeriv (F := fun t : ℂ => G t z) (A := A z) (B := B z) (c0 := g z) (hexp z hz1)
    have he := hd.unique hL
    have h1 : L 1 = A z + B z := by
      rw [← he]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul, map_one]
      ring
    have hI : L I = A z * I - B z * I := by
      rw [← he]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul, conj_I]
      ring
    have hA : A z = (L 1 - I * L I) / 2 := by
      rw [h1, hI]
      linear_combination (A z - B z) / 2 * I_sq
    have hB : B z = (L 1 + I * L I) / 2 := by
      rw [h1, hI]
      linear_combination (B z - A z) / 2 * I_sq
    have hz0 : 0 < ‖z‖ := by linarith
    have hL1 : ‖L 1‖ ≤ C * ‖z‖ := by simpa using hLb 1
    have hLI : ‖L I‖ ≤ C * ‖z‖ := by simpa using hLb I
    have hA' : ‖A z‖ ≤ C * ‖z‖ := by
      rw [hA, norm_div]
      have h2 : ‖L 1 - I * L I‖ ≤ ‖L 1‖ + ‖L I‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, one_mul]
      have h3 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h3]
      linarith
    have hB' : ‖B z‖ ≤ C * ‖z‖ := by
      rw [hB, norm_div]
      have h2 : ‖L 1 + I * L I‖ ≤ ‖L 1‖ + ‖L I‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, one_mul]
      have h3 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h3]
      linarith
    have e : ∀ w : ℂ, ‖w‖ ≤ C * ‖z‖ → ‖w / z ^ 2‖ ≤ C * ‖z‖⁻¹ := fun w hw => by
      rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
      calc ‖w‖ ≤ C * ‖z‖ := hw
        _ = C * ‖z‖⁻¹ * ‖z‖ ^ 2 := by field_simp
    exact ⟨e _ hA', e _ hB'⟩
  have hlim : Tendsto (fun z : ℂ => C * ‖z‖⁻¹) (cocompact ℂ) (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp (tendsto_norm_cocompact_atTop (E := ℂ))).const_mul C
    rw [mul_zero] at h
    exact h
  exact ⟨squeeze_zero_norm' (hb.mono fun z hz => hz.1) hlim, squeeze_zero_norm' (hb.mono fun z hz => hz.2) hlim⟩

/-- [(V-B) helper] `R = R(ν, κ)` is bounded measurable on `𝔻*`, and its reflection `R̃(ζ) = R(1/ζ̄)‾ ζ²/ζ̄²` is
bounded measurable on `𝔻`. -/
theorem s3d5_R_data {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (ν : LinfStar) :
    ∃ M : ℝ, AEStronglyMeasurable (RnmFun ν κ) (volume.restrict unitDiscExterior) ∧
      (∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖RnmFun ν κ u‖ ≤ M) ∧
      AEStronglyMeasurable (fun ζ => conj (RnmFun ν κ (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2)
        (volume.restrict unitDisc) ∧
      ∀ᵐ ζ ∂(volume.restrict unitDisc), ‖conj (RnmFun ν κ (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2‖ ≤ M := by
  have hae := WPCV.wpcv_RnmFun_ae hκ ν
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hDm : MeasurableSet unitDisc := (show MeasurableSet unitDisc from measurableSet_ball)
  have hRm : AEStronglyMeasurable (RnmFun ν κ) (volume.restrict unitDiscExterior) :=
    (Lp.aestronglyMeasurable (Rnm ν κ)).congr hae
  set M := max ‖Rnm ν κ‖ 0 with hM
  have hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖RnmFun ν κ u‖ ≤ M := by
    filter_upwards [hae, LinfStar_ae_norm_le (Rnm ν κ)] with u h1 h2
    rw [← h1]
    exact h2.trans (le_max_left _ _)
  set R' : ℂ → ℂ := unitDiscExterior.indicator (RnmFun ν κ) with hR'
  have hR'm : AEStronglyMeasurable R' volume := (aestronglyMeasurable_indicator_iff hEm).mpr hRm
  have hR'b : ∀ᵐ u, ‖R' u‖ ≤ M := by
    filter_upwards [(ae_restrict_iff' hEm).mp hRb] with u hu
    by_cases h : u ∈ unitDiscExterior
    · rw [hR', Set.indicator_of_mem h]
      exact hu h
    · rw [hR', Set.indicator_of_notMem h, norm_zero]
      exact le_max_right _ _
  have hrefl : ∀ ζ ∈ unitDisc, conj (RnmFun ν κ (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 =
      conj (R' (refl ζ)) * ζ ^ 2 / conj ζ ^ 2 := fun ζ hζ => by
    by_cases h0 : ζ = 0
    · subst h0
      simp
    · have hm : refl ζ ∈ unitDiscExterior := (refl_mem_exterior_iff h0).mpr hζ
      rw [hR', Set.indicator_of_mem hm, one_div]
      rfl
  have hm0 : AEStronglyMeasurable (fun ζ : ℂ => conj (R' (refl ζ)) * ζ ^ 2 / conj ζ ^ 2) volume := by
    have h1 : AEStronglyMeasurable (fun ζ : ℂ => conj (R' (refl ζ))) volume :=
      Complex.continuous_conj.comp_aestronglyMeasurable (aestronglyMeasurable_comp_refl hR'm)
    have h2 : AEStronglyMeasurable (fun ζ : ℂ => conj (R' (refl ζ)) * ζ ^ 2 * (conj ζ ^ 2)⁻¹) volume :=
      (h1.mul (Continuous.aestronglyMeasurable (by fun_prop))).mul
        (Measurable.aestronglyMeasurable (by fun_prop))
    exact h2.congr (Eventually.of_forall fun ζ => by simp only [div_eq_mul_inv])
  refine ⟨M, hRm, hRb, ?_, ?_⟩
  · exact hm0.restrict.congr ((ae_restrict_mem hDm).mono fun ζ hζ => (hrefl ζ hζ).symm)
  · filter_upwards [ae_restrict_mem hDm, ae_restrict_of_ae (ae_refl hR'b)] with ζ hζ hb
    rw [hrefl ζ hζ]
    by_cases h0 : ζ = 0
    · subst h0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div, norm_zero]
      exact le_max_right _ _
    · have hn : ‖ζ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)
      rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_conj, Complex.norm_conj, mul_div_assoc,
        div_self hn, mul_one]
      exact hb

/-- **(V-B)** Pinning the pole coefficients: the g-side expansion with `Q₁, Q₂` forces `Q₁ = c₂/b`, `Q₂ = c₂'/b`. -/
theorem s3dv_pin {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    ∀ Q₁ Q₂ : ℂ, (∀ r₁ r₂ : ℝ, 1 < r₁ → ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ →
      ‖gsans (beltramiMul (a + t • toLinf m) κ) z - gsans (beltramiMul a κ) z -
        (t * ((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) + Q₁ * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) +
          conj t * (Q₂ * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))))‖ ≤ ε * ‖t‖) →
      Q₁ = ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) ∧ Q₂ = ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) := by
  -- the frozen hypotheses `hκ`, `hκD`, `ha`, `haL`, `haD`, `hm`, `hmD` are not needed: the pinning uses only the
  -- growth of `t ↦ 𝗀_t(z)` from the exterior reciprocal chart and P5a/P5b (the statement stays true without them)
  have _h := And.intro hκ (And.intro hκD (And.intro ha (And.intro haL (And.intro haD (And.intro hm hmD)))))
  intro Q₁ Q₂ hQ
  have ha1 : ‖a‖ < 1 := has.trans delta0_bounds.2
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.mpr ha1
  have hν0 : beltramiMul a κ ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hDm : MeasurableSet unitDisc := (show MeasurableSet unitDisc from measurableSet_ball)
  obtain ⟨hb0, hgz, hdg⟩ := s3d5_asym hν0
  obtain ⟨C, hC⟩ := s3d5_chart κ.2 haB (toLinf m)
  obtain ⟨M, hRm, hRb, hRm', hRb'⟩ := s3d5_R_data haB (toLinf m)
  have hcore := s3d5_pin_core (G := fun t z => gsans (beltramiMul (a + t • toLinf m) κ) z)
    (g := gsans (beltramiMul a κ)) (fun z hz ε hε => by
      obtain ⟨δ, hδ, hb⟩ := hQ ‖z‖ ‖z‖ hz ε hε
      exact ⟨δ, hδ, fun t ht => hb t ht z le_rfl le_rfl⟩) hC
  have hV := s3dv_vdot_asym hν0 hRm hRb
  have hγ1 := s3dv_gamma_asym hEm hRm hRb
  have hγ2 := s3dv_gamma_asym hDm hRm' hRb'
  beta_reduce at hγ2
  have hl1 := ((hV.const_mul (-(1 / π : ℂ))).add ((hgz.pow 2).const_mul Q₁)).sub
    (hdg.mul (hγ1.const_mul (-(1 / π : ℂ))))
  have hl2 := ((hgz.pow 2).const_mul Q₂).sub (hdg.mul (hγ2.const_mul (-(1 / π : ℂ))))
  have e1 := tendsto_nhds_unique hcore.1 (hl1.congr fun z => by beta_reduce; ring)
  have e2 := tendsto_nhds_unique hcore.2 (hl2.congr fun z => by beta_reduce; ring)
  refine ⟨eq_div_of_mul_eq hb0 ?_, eq_div_of_mul_eq hb0 ?_⟩
  · have h : derivAtInfty (gsans (beltramiMul a κ)) * (Q₁ * derivAtInfty (gsans (beltramiMul a κ)) -
        (1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) = 0 := by
      linear_combination -e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hb0)
  · have h : derivAtInfty (gsans (beltramiMul a κ)) * (Q₂ * derivAtInfty (gsans (beltramiMul a κ)) -
        (1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 /
          ((ζ + 1) * (ζ + I) * (ζ - 1))) = 0 := by
      linear_combination -e2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hb0)

/-- [(V-A-g) helper] A real derivative at `0` in Wirtinger form: `F'(0) t = ∂F(0) t + ∂̄F(0) t̄`. -/
theorem s3dg_fd {F : ℂ → ℂ} (h : DifferentiableAt ℝ F 0) :
    HasFDerivAt F (dz F 0 • (1 : ℂ →L[ℝ] ℂ) + dzbar F 0 • (conjCLE : ℂ →L[ℝ] ℂ)) 0 := by
  refine h.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul]
  have e1 : dz F 0 = (fderiv ℝ F 0 1 - I * fderiv ℝ F 0 I) / 2 := rfl
  have e2 : dzbar F 0 = (fderiv ℝ F 0 1 + I * fderiv ℝ F 0 I) / 2 := rfl
  have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • I := by
    apply Complex.ext <;> simp
  have hL : fderiv ℝ F 0 v = (v.re : ℂ) * fderiv ℝ F 0 1 + (v.im : ℂ) * fderiv ℝ F 0 I := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have hv2 : v = (v.re : ℂ) + (v.im : ℂ) * I := (Complex.re_add_im v).symm
  rw [hL, e1, e2]
  conv_rhs => rw [hv2]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination ((v.im : ℂ) * fderiv ℝ F 0 I) * I_sq

/-- [(V-A-g) helper] A complex derivative in the form `c t + 0 t̄`. -/
theorem s3dg_hol {F : ℂ → ℂ} {c : ℂ} (h : HasDerivAt F c 0) :
    HasFDerivAt F (c • (1 : ℂ →L[ℝ] ℂ) + (0 : ℂ) • (conjCLE : ℂ →L[ℝ] ℂ)) 0 := by
  refine (h.hasFDerivAt.restrictScalars ℝ).congr_fderiv (ContinuousLinearMap.ext fun t => ?_)
  simp [mul_comm]

/-- [(V-A-g) helper] Product rule for real derivatives of the shape `t ↦ A t + B t̄` at `0`. -/
theorem s3dg_mul {F1 F2 : ℂ → ℂ} {A1 B1 A2 B2 : ℂ}
    (h1 : HasFDerivAt F1 (A1 • (1 : ℂ →L[ℝ] ℂ) + B1 • (conjCLE : ℂ →L[ℝ] ℂ)) 0)
    (h2 : HasFDerivAt F2 (A2 • (1 : ℂ →L[ℝ] ℂ) + B2 • (conjCLE : ℂ →L[ℝ] ℂ)) 0) :
    HasFDerivAt (fun t => F1 t * F2 t) ((A1 * F2 0 + F1 0 * A2) • (1 : ℂ →L[ℝ] ℂ) +
      (B1 * F2 0 + F1 0 * B2) • (conjCLE : ℂ →L[ℝ] ℂ)) 0 := by
  refine (h1.mul h2).congr_fderiv (ContinuousLinearMap.ext fun t => ?_)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul]
  ring

/-- [(V-A-g) helper] A uniform first-order bound `‖F t - c₀ - Λ t‖ ≤ ε ‖t‖` gives `F'(0) = Λ`. -/
theorem s3dg_of_unif {F : ℂ → ℂ} {c0 : ℂ} {Λ : ℂ →L[ℝ] ℂ}
    (h : ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ‖F t - c0 - Λ t‖ ≤ ε * ‖t‖) : HasFDerivAt F Λ 0 := by
  have h0 : F 0 = c0 := by
    obtain ⟨δ, hδ, hb⟩ := h 1 one_pos
    have h1 := hb 0 (by rw [norm_zero]; exact hδ)
    simp only [norm_zero, mul_zero, map_zero, sub_zero] at h1
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.isLittleO_iff.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hb⟩ := h ε hε
  filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with t ht
  rw [mem_ball_zero_iff] at ht
  rw [zero_add, h0]
  exact hb t ht

/-- [(V-A-g) helper] A finite point of the sphere is the coercion of its finite part. -/
theorem s3dg_fin {p : ExtPlane} (h : p ≠ extInf) : ((finPart p : ℂ) : ExtPlane) = p := by
  induction p using OnePoint.rec with
  | infty => exact absurd rfl h
  | coe u => rw [finPart_coe]

/-- [(V-A-g) helper] Inversion estimate: `‖1/E_t - 1/E₀ + ℓ/E₀²‖ ≤ 2(αM + β(α + β))/m³` when
`‖E_t - E₀ - ℓ‖ ≤ α`, `‖ℓ‖ ≤ β`, `m ≤ ‖E₀‖ ≤ M` and `α + β ≤ m/2`. -/
theorem s3dg_inv_est {E0 Et ℓ : ℂ} {m M α β : ℝ} (hm : 0 < m) (h0 : m ≤ ‖E0‖) (h0' : ‖E0‖ ≤ M)
    (hα : ‖Et - E0 - ℓ‖ ≤ α) (hβ : ‖ℓ‖ ≤ β) (hs : α + β ≤ m / 2) :
    ‖Et⁻¹ - E0⁻¹ + ℓ / E0 ^ 2‖ ≤ 2 * (α * M + β * (α + β)) / m ^ 3 := by
  have hE0p : 0 < ‖E0‖ := hm.trans_le h0
  have hE0 : E0 ≠ 0 := norm_pos_iff.mp hE0p
  have hα0 : 0 ≤ α := (norm_nonneg _).trans hα
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hβ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans h0'
  have hd : ‖Et - E0‖ ≤ α + β := by
    calc ‖Et - E0‖ = ‖(Et - E0 - ℓ) + ℓ‖ := by rw [sub_add_cancel]
      _ ≤ ‖Et - E0 - ℓ‖ + ‖ℓ‖ := norm_add_le _ _
      _ ≤ α + β := add_le_add hα hβ
  have hEt : m / 2 ≤ ‖Et‖ := by
    have h1 := norm_sub_norm_le E0 Et
    rw [norm_sub_rev] at h1
    linarith
  have hEt0 : Et ≠ 0 := norm_pos_iff.mp (by linarith)
  have e : Et⁻¹ - E0⁻¹ + ℓ / E0 ^ 2 = (-(Et - E0 - ℓ) * E0 + ℓ * (Et - E0)) / (Et * E0 ^ 2) := by
    field_simp
    ring
  rw [e, norm_div, norm_mul, norm_pow]
  have hnum : ‖-(Et - E0 - ℓ) * E0 + ℓ * (Et - E0)‖ ≤ α * M + β * (α + β) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_neg]
    gcongr
  have hden : m / 2 * m ^ 2 ≤ ‖Et‖ * ‖E0‖ ^ 2 :=
    mul_le_mul hEt (pow_le_pow_left₀ hm.le h0 2) (by positivity) (by positivity)
  calc _ ≤ (α * M + β * (α + β)) / (m / 2 * m ^ 2) := div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 2 * (α * M + β * (α + β)) / m ^ 3 := by field_simp

/-- [(V-A-g) helper] Compactness for the exterior reciprocal chart `E = E(μ, μ̄)` on a compact `K ⊆ 𝔻` where `E ≠ 0`:
uniform bounds `m ≤ |E| ≤ M`, `‖∂_pE‖ ≤ B` and a uniform second-order Taylor bound in `p` on a ball of radius `ρ`. -/
theorem s3dg_cpt {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {K : Set ℂ} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hKD : K ⊆ unitDisc) (hK0 : ∀ s ∈ K, s5cf_exterior_reciprocal (μ, star μ) s ≠ 0) :
    ∃ ρ > 0, ∃ m M B T : ℝ, 0 < m ∧ m ≤ M ∧ 0 ≤ B ∧ 0 ≤ T ∧ ∀ s ∈ K,
      m ≤ ‖s5cf_exterior_reciprocal (μ, star μ) s‖ ∧ ‖s5cf_exterior_reciprocal (μ, star μ) s‖ ≤ M ∧
      ‖(fderiv ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_exterior_reciprocal q.1 q.2) ((μ, star μ), s)).comp
        (ContinuousLinearMap.inl ℂ (LinfStar × LinfStar) ℂ)‖ ≤ B ∧
      ∀ q : LinfStar × LinfStar, ‖q‖ < ρ →
        ‖s5cf_exterior_reciprocal ((μ, star μ) + q) s - s5cf_exterior_reciprocal (μ, star μ) s -
          (fderiv ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_exterior_reciprocal q.1 q.2) ((μ, star μ), s)).comp
            (ContinuousLinearMap.inl ℂ (LinfStar × LinfStar) ℂ) q‖ ≤ T * ‖q‖ ^ 2 := by
  set p₀ : LinfStar × LinfStar := (μ, star μ) with hp₀
  set Ê : (LinfStar × LinfStar) × ℂ → ℂ := fun q => s5cf_exterior_reciprocal q.1 q.2 with hÊ
  have hA : ∀ s ∈ K, AnalyticAt ℂ Ê (p₀, s) := fun s hs => s5cf_exterior_reciprocal_analytic hμ (hKD hs)
  have hE0c : ContinuousOn (fun w => Ê (p₀, w)) K := fun s hs =>
    ((hA s hs).comp (analyticAt_const.prod analyticAt_id)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hE0c
  obtain ⟨s₀, hs₀, hmin⟩ := hKc.exists_isMinOn hKne hE0c.norm
  have hm0 : 0 < ‖Ê (p₀, s₀)‖ := norm_pos_iff.mpr (hK0 s₀ hs₀)
  have hMm : ‖Ê (p₀, s₀)‖ ≤ M := hM s₀ hs₀
  have hφc : ContinuousOn (fun s => (fderiv ℂ Ê (p₀, s)).comp (ContinuousLinearMap.inl ℂ (LinfStar × LinfStar) ℂ)) K :=
    fun s hs => by
      have h1 : DifferentiableAt ℂ (fun w : ℂ => fderiv ℂ Ê (p₀, w)) s :=
        (hA s hs).fderiv.differentiableAt.comp s (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (p₀, w)) s)
      exact (h1.clm_comp (differentiableAt_const _)).continuousAt.continuousWithinAt
  obtain ⟨Bφ, hBφ⟩ := hKc.exists_bound_of_continuousOn hφc
  have hev : ∀ s ∈ K, ∀ᶠ q : (LinfStar × LinfStar) × ℂ in 𝓝 (p₀, s),
      AnalyticAt ℂ Ê (q.1, q.2) ∧ ‖Ê (q.1, q.2)‖ ≤ M + 1 := fun s hs => by
    have h2 : ‖Ê (p₀, s)‖ < M + 1 := by linarith [hM s hs]
    filter_upwards [(hA s hs).eventually_analyticAt, (hA s hs).continuousAt.norm.eventually (gt_mem_nhds h2)]
      with q h1 h3
    exact ⟨h1, h3.le⟩
  obtain ⟨ρ, hρ, hρU⟩ := Metric.eventually_nhds_iff.mp (hKc.eventually_forall_of_forall_eventually (x₀ := p₀)
    (P := fun (q : LinfStar × LinfStar) (s : ℂ) => AnalyticAt ℂ Ê (q, s) ∧ ‖Ê (q, s)‖ ≤ M + 1) hev)
  have hdist : ∀ q : LinfStar × LinfStar, ‖q‖ < ρ → dist (p₀ + q) p₀ < ρ := fun q hq => by
    rwa [dist_eq_norm, add_sub_cancel_left]
  have hM0 : 0 ≤ M := hm0.le.trans hMm
  refine ⟨ρ, hρ, ‖Ê (p₀, s₀)‖, M, max Bφ 0, 4 * (M + 1) / ρ ^ 2, hm0, hMm, le_max_right _ _, by positivity,
    fun s hs => ⟨isMinOn_iff.mp hmin s hs, hM s hs, (hBφ s hs).trans (le_max_left _ _), fun q hq => ?_⟩⟩
  have hF : DifferentiableOn ℂ (fun q : LinfStar × LinfStar => Ê (p₀ + q, s)) (ball 0 ρ) := fun q' hq' => by
    have h1 := (hρU (hdist q' (mem_ball_zero_iff.mp hq')) s hs).1
    exact (h1.differentiableAt.comp q'
      (by fun_prop : DifferentiableAt ℂ (fun q : LinfStar × LinfStar => (p₀ + q, s)) q')).differentiableWithinAt
  have hC : ∀ v ∈ ball (0 : LinfStar × LinfStar) ρ, ‖(fun q : LinfStar × LinfStar => Ê (p₀ + q, s)) v‖ ≤ M + 1 :=
    fun v hv => (hρU (hdist v (mem_ball_zero_iff.mp hv)) s hs).2
  have h := s3dv_taylorE hρ hF hC (mem_ball_zero_iff.mpr hq)
  have hfd : fderiv ℂ (fun q : LinfStar × LinfStar => Ê (p₀ + q, s)) 0 =
      (fderiv ℂ Ê (p₀, s)).comp (ContinuousLinearMap.inl ℂ (LinfStar × LinfStar) ℂ) := by
    have h1 : HasFDerivAt Ê (fderiv ℂ Ê (p₀, s)) (p₀ + 0, s) := by
      rw [add_zero]
      exact (hA s hs).differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun q : LinfStar × LinfStar => (p₀ + q, s))
        (ContinuousLinearMap.inl ℂ (LinfStar × LinfStar) ℂ) 0 :=
      ((hasFDerivAt_id (0 : LinfStar × LinfStar)).const_add p₀).prodMk (hasFDerivAt_const s 0)
    exact (h1.comp 0 h2).fderiv
  rw [hfd] at h
  simp only [add_zero] at h
  exact h

/-- [(V-A-g) helper] The `ε`-`δ` bookkeeping of `s3dg_unif` (pure arithmetic): with `q ≤ e + Dτ`, `e ≤ ητ` and
`τ < δ₀`, the Taylor radius is respected, `α + β ≤ m/2` and the inversion bound of `s3dg_inv_est` is `≤ ετ`, for
`α = Tq² + Be`, `β = BDτ`. -/
theorem s3dg_arith {m M B D T ρ ε : ℝ} (hm : 0 < m) (hM : m ≤ M) (hB : 0 ≤ B) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ η > 0, ∃ δ₀ > 0, ∀ τ q e : ℝ, 0 ≤ τ → τ < δ₀ → 0 ≤ q → 0 ≤ e → e ≤ η * τ → q ≤ e + D * τ →
      q < ρ ∧ (T * q ^ 2 + B * e) + B * D * τ ≤ m / 2 ∧
      2 * ((T * q ^ 2 + B * e) * M + B * D * τ * ((T * q ^ 2 + B * e) + B * D * τ)) / m ^ 3 ≤ ε * τ := by
  have hM0 : 0 ≤ M := hm.le.trans hM
  set C₁ := D + 1 with hC₁
  set L₀ := B * D with hL₀
  have hL₀0 : 0 ≤ L₀ := mul_nonneg hB hD
  set c₀ := m ^ 3 / 2 * ε with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  set ε₁ := min 1 (c₀ / (2 * (M + 1))) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min one_pos (by positivity)
  have hε₁1 : ε₁ ≤ 1 := min_le_left _ _
  have hε₁M : ε₁ * M ≤ c₀ / 2 := by
    have h1 : ε₁ ≤ c₀ / (2 * (M + 1)) := min_le_right _ _
    have h2 : ε₁ * (M + 1) ≤ c₀ / 2 := by
      calc ε₁ * (M + 1) ≤ c₀ / (2 * (M + 1)) * (M + 1) := by gcongr
        _ = c₀ / 2 := by field_simp
    calc ε₁ * M ≤ ε₁ * (M + 1) := by gcongr; linarith
      _ ≤ c₀ / 2 := h2
  set η := min 1 (ε₁ / (2 * (B + 1))) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηB : B * η ≤ ε₁ / 2 := by
    have h1 : η ≤ ε₁ / (2 * (B + 1)) := min_le_right _ _
    have h2 : (B + 1) * η ≤ ε₁ / 2 := by
      calc (B + 1) * η ≤ (B + 1) * (ε₁ / (2 * (B + 1))) := by gcongr
        _ = ε₁ / 2 := by field_simp
    calc B * η ≤ (B + 1) * η := by gcongr; linarith
      _ ≤ ε₁ / 2 := h2
  refine ⟨η, hη0, min (min (ρ / (C₁ + 1)) (ε₁ / (2 * (T * C₁ ^ 2 + 1))))
    (min (c₀ / (2 * (L₀ * (1 + L₀) + 1))) (m / (2 * (1 + L₀)))),
    lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity)), ?_⟩
  intro τ q e hτ0 hτ hq0 he0 he hq
  have ht1 : τ ≤ ρ / (C₁ + 1) := hτ.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have ht2 : τ ≤ ε₁ / (2 * (T * C₁ ^ 2 + 1)) := hτ.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have ht3 : τ ≤ c₀ / (2 * (L₀ * (1 + L₀) + 1)) := hτ.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht4 : τ ≤ m / (2 * (1 + L₀)) := hτ.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hqb : q ≤ C₁ * τ := by
    calc q ≤ e + D * τ := hq
      _ ≤ η * τ + D * τ := by linarith
      _ ≤ 1 * τ + D * τ := by gcongr
      _ = C₁ * τ := by rw [hC₁]; ring
  have hC₁0 : 0 < C₁ + 1 := by positivity
  have hqρ : q < ρ := by
    have h1 : C₁ * τ ≤ C₁ * (ρ / (C₁ + 1)) := by gcongr
    have h2 : C₁ * (ρ / (C₁ + 1)) < ρ := by
      rw [mul_div_assoc', div_lt_iff₀ hC₁0]
      have h3 : ρ * (C₁ + 1) = C₁ * ρ + ρ := by ring
      rw [h3]
      linarith
    linarith
  -- `α ≤ ε₁ τ`
  have hα : T * q ^ 2 + B * e ≤ ε₁ * τ := by
    have h4 : q ^ 2 ≤ C₁ ^ 2 * τ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hq0 hqb 2
    have h5 : (T * C₁ ^ 2 + 1) * τ ≤ ε₁ / 2 := by
      calc (T * C₁ ^ 2 + 1) * τ ≤ (T * C₁ ^ 2 + 1) * (ε₁ / (2 * (T * C₁ ^ 2 + 1))) := by gcongr
        _ = ε₁ / 2 := by field_simp
    have h6 : T * q ^ 2 ≤ ε₁ / 2 * τ := by
      calc T * q ^ 2 ≤ T * (C₁ ^ 2 * τ ^ 2) := by gcongr
        _ = (T * C₁ ^ 2 * τ) * τ := by ring
        _ ≤ ε₁ / 2 * τ := by
          gcongr
          have h8 : (T * C₁ ^ 2 + 1) * τ = T * C₁ ^ 2 * τ + τ := by ring
          linarith
    have h7 : B * e ≤ ε₁ / 2 * τ := by
      calc B * e ≤ B * (η * τ) := by gcongr
        _ = (B * η) * τ := by ring
        _ ≤ ε₁ / 2 * τ := by gcongr
    linarith
  have hαβ : (T * q ^ 2 + B * e) + B * D * τ ≤ m / 2 := by
    have h1 : (1 + L₀) * τ ≤ m / 2 := by
      calc (1 + L₀) * τ ≤ (1 + L₀) * (m / (2 * (1 + L₀))) := by gcongr
        _ = m / 2 := by field_simp
    have h2 : ε₁ * τ ≤ 1 * τ := by gcongr
    rw [hL₀] at h1
    have h3 : (1 + B * D) * τ = τ + B * D * τ := by ring
    linarith
  refine ⟨hqρ, hαβ, ?_⟩
  have hα0 : 0 ≤ T * q ^ 2 + B * e := by positivity
  have hL : L₀ * (ε₁ + L₀) * τ ≤ c₀ / 2 := by
    have h1 : (L₀ * (1 + L₀) + 1) * τ ≤ c₀ / 2 := by
      calc (L₀ * (1 + L₀) + 1) * τ ≤ (L₀ * (1 + L₀) + 1) * (c₀ / (2 * (L₀ * (1 + L₀) + 1))) := by gcongr
        _ = c₀ / 2 := by field_simp
    have h2 : L₀ * (ε₁ + L₀) ≤ L₀ * (1 + L₀) := by gcongr
    calc L₀ * (ε₁ + L₀) * τ ≤ L₀ * (1 + L₀) * τ := by gcongr
      _ ≤ L₀ * (1 + L₀) * τ + τ := by linarith
      _ = (L₀ * (1 + L₀) + 1) * τ := by ring
      _ ≤ c₀ / 2 := h1
  rw [div_le_iff₀ (by positivity)]
  have hc : ε * τ * m ^ 3 = 2 * c₀ * τ := by rw [hc₀]; ring
  rw [hc]
  -- `α M + β (α + β) ≤ ε₁ τ M + L₀ τ (ε₁ + L₀) τ ≤ c₀ τ`
  have h1 : (T * q ^ 2 + B * e) * M ≤ ε₁ * τ * M := by gcongr
  have h2 : B * D * τ * ((T * q ^ 2 + B * e) + B * D * τ) ≤ L₀ * τ * (ε₁ * τ + L₀ * τ) := by
    rw [hL₀]
    gcongr
  have h3 : ε₁ * τ * M + L₀ * τ * (ε₁ * τ + L₀ * τ) ≤ c₀ * τ := by
    have h4 := mul_le_mul_of_nonneg_left hε₁M hτ0
    have h5 := mul_le_mul_of_nonneg_left hL hτ0
    calc ε₁ * τ * M + L₀ * τ * (ε₁ * τ + L₀ * τ) = τ * (ε₁ * M) + τ * (L₀ * (ε₁ + L₀) * τ) := by ring
      _ ≤ τ * (c₀ / 2) + τ * (c₀ / 2) := add_le_add h4 h5
      _ = c₀ * τ := by ring
  linarith

/-- [(V-A-g) helper] **Uniform chart expansion.** For `ν_t = (a + t μ) * κ`, there is a family of real-linear
maps `Λ_z` with `𝗀_t(z) = 𝗀(z) + Λ_z t + o(t)` uniformly on every closed annulus `r₁ ≤ |z| ≤ r₂`, `r₁ > 1`.
Through `𝗀_t(z) = 1/E(p_t, 1/z)` with `E` jointly analytic (`s5cf_exterior_reciprocal_analytic`) and `p_t` real
differentiable, `Λ_z t = -𝗀(z)² ∂_pE(p₀, 1/z) ṗ t`; uniformity from compactness of `{1/z}` (`s3dg_cpt`). -/
theorem s3dg_unif {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (μ : LinfStar) :
    ∃ Λ : ℂ → (ℂ →L[ℝ] ℂ), ∀ r₁ r₂ : ℝ, 1 < r₁ → ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ z : ℂ, r₁ ≤ ‖z‖ →
      ‖z‖ ≤ r₂ → ‖gsans (beltramiMul (a + t • μ) κ) z - gsans (beltramiMul a κ) z - Λ z t‖ ≤ ε * ‖t‖ := by
  have hν0 : beltramiMul a κ ∈ LinfStarBall := bg_mul_mem_ball hκ ha
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  set P : ℂ → LinfStar × LinfStar := fun t =>
    (beltramiMul (a + t • μ) κ, star (beltramiMul (a + t • μ) κ)) with hP
  have hP0 : P 0 = (beltramiMul a κ, star (beltramiMul a κ)) := by simp [hP]
  have hPd : DifferentiableAt ℝ P 0 := by
    have hν : DifferentiableAt ℝ (fun t : ℂ => beltramiMul (a + t • μ) κ) 0 :=
      (s35wn_nu_diff hκ ha μ).restrictScalars ℝ
    have hs : DifferentiableAt ℝ (fun t : ℂ => star (beltramiMul (a + t • μ) κ)) 0 :=
      DifferentiableAt.comp (g := fun ν : LinfStar => star ν) (0 : ℂ)
        (s5cf_star_analytic (beltramiMul (a + (0 : ℂ) • μ) κ)).differentiableAt hν
    exact hν.prodMk hs
  set DP := fderiv ℝ P 0 with hDP
  refine ⟨fun z => (-(gsans (beltramiMul a κ) z) ^ 2) •
    ((((fderiv ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_exterior_reciprocal q.1 q.2)
      ((beltramiMul a κ, star (beltramiMul a κ)), z⁻¹)).comp
        (ContinuousLinearMap.inl ℂ (LinfStar × LinfStar) ℂ)).restrictScalars ℝ).comp DP), ?_⟩
  intro r₁ r₂ hr₁ ε hε
  by_cases hr : r₁ ≤ r₂
  swap
  · exact ⟨1, one_pos, fun t _ z h1 h2 => absurd (h1.trans h2) hr⟩
  have hr₁0 : 0 < r₁ := by linarith
  have hr₂ : 0 < r₂ := by linarith
  have hKc : IsCompact {s : ℂ | r₂⁻¹ ≤ ‖s‖ ∧ ‖s‖ ≤ r₁⁻¹} := (isCompact_closedBall (0 : ℂ) r₁⁻¹).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
      (fun s hs => mem_closedBall_zero_iff.mpr hs.2)
  have hKD : {s : ℂ | r₂⁻¹ ≤ ‖s‖ ∧ ‖s‖ ≤ r₁⁻¹} ⊆ unitDisc := fun s hs =>
    mem_ball_zero_iff.mpr (hs.2.trans_lt (inv_lt_one_of_one_lt₀ hr₁))
  have hKi : ∀ s ∈ {s : ℂ | r₂⁻¹ ≤ ‖s‖ ∧ ‖s‖ ≤ r₁⁻¹}, 1 < ‖s⁻¹‖ := fun s hs => by
    have hs0 : s ≠ 0 := fun h => by
      have h1 := hs.1
      rw [h, norm_zero] at h1
      exact absurd h1 (not_le.mpr (inv_pos.mpr hr₂))
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hs0)).mpr (mem_ball_zero_iff.mp (hKD hs))
  have hgne : ∀ w : ℂ, 1 < ‖w‖ → gsans (beltramiMul a κ) w ≠ 0 := fun w hw h => by
    obtain ⟨ε', hε', -, hl⟩ := s3d5_lower hν0
    have h1 := hl w hw.le
    rw [← gMu_eq_normalizedWeldingExterior hν0 hw, ← S2C.s2c_gsans_eq hν0, h, norm_zero] at h1
    linarith
  have hK0 : ∀ s ∈ {s : ℂ | r₂⁻¹ ≤ ‖s‖ ∧ ‖s‖ ≤ r₁⁻¹},
      s5cf_exterior_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) s ≠ 0 := fun s hs => by
    have h1 := s3d5_recip hν0 (hKi s hs)
    rw [inv_inv] at h1
    rw [h1]
    exact inv_ne_zero (hgne _ (hKi s hs))
  have hKne : ({s : ℂ | r₂⁻¹ ≤ ‖s‖ ∧ ‖s‖ ≤ r₁⁻¹}).Nonempty := by
    refine ⟨((r₁⁻¹ : ℝ) : ℂ), ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr₁0)]
      exact inv_anti₀ hr₁0 hr
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr₁0)]
  obtain ⟨ρ, hρ, m, M, B, T, hm0, hMm, hB0, hT0, hK⟩ := s3dg_cpt hν0 hKc hKne hKD hK0
  obtain ⟨η, hη0, δ₀, hδ₀0, harith⟩ := s3dg_arith hm0 hMm hB0 (norm_nonneg DP) hT0 hρ hε
  have hEv : ∀ᶠ t in 𝓝 (0 : ℂ), (a + t • μ ∈ LinfStarBall ∧ beltramiMul (a + t • μ) κ ∈ LinfStarBall) ∧
      ‖P t - P 0 - DP (t - 0)‖ ≤ η * ‖t - 0‖ ∧ t ∈ ball (0 : ℂ) δ₀ :=
    (s35wn_mem hκ ha1 μ).and ((hPd.hasFDerivAt.isLittleO.def hη0).and (ball_mem_nhds 0 hδ₀0))
  obtain ⟨δ, hδ, hδU⟩ := Metric.eventually_nhds_iff.mp hEv
  refine ⟨δ, hδ, fun t ht z hz1 hz2 => ?_⟩
  obtain ⟨⟨-, hνt⟩, hPt, htδ⟩ := hδU (by rwa [dist_zero_right])
  rw [sub_zero, hP0] at hPt
  rw [mem_ball_zero_iff] at htδ
  have hzr : 1 < ‖z‖ := by linarith
  have hsK : z⁻¹ ∈ {s : ℂ | r₂⁻¹ ≤ ‖s‖ ∧ ‖s‖ ≤ r₁⁻¹} := by
    refine ⟨?_, ?_⟩
    · rw [norm_inv]; exact inv_anti₀ (by linarith) hz2
    · rw [norm_inv]; exact inv_anti₀ hr₁0 hz1
  obtain ⟨hmK, hMK, hBK, hTK⟩ := hK z⁻¹ hsK
  set p₀ : LinfStar × LinfStar := (beltramiMul a κ, star (beltramiMul a κ)) with hp₀
  set φ := (fderiv ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_exterior_reciprocal q.1 q.2) (p₀, z⁻¹)).comp
    (ContinuousLinearMap.inl ℂ (LinfStar × LinfStar) ℂ) with hφ
  have hqd : ‖P t - p₀‖ ≤ ‖P t - p₀ - DP t‖ + ‖DP‖ * ‖t‖ := by
    calc ‖P t - p₀‖ = ‖(P t - p₀ - DP t) + DP t‖ := by rw [sub_add_cancel]
      _ ≤ ‖P t - p₀ - DP t‖ + ‖DP t‖ := norm_add_le _ _
      _ ≤ ‖P t - p₀ - DP t‖ + ‖DP‖ * ‖t‖ := by gcongr; exact DP.le_opNorm t
  obtain ⟨hqρ, hs, hfin⟩ := harith ‖t‖ ‖P t - p₀‖ ‖P t - p₀ - DP t‖ (norm_nonneg _)
    (htδ.trans_le le_rfl) (norm_nonneg _) (norm_nonneg _) hPt hqd
  have hEt : s5cf_exterior_reciprocal (P t) z⁻¹ = s5cf_exterior_reciprocal (p₀ + (P t - p₀)) z⁻¹ := by
    rw [add_sub_cancel]
  have hα : ‖s5cf_exterior_reciprocal (P t) z⁻¹ - s5cf_exterior_reciprocal p₀ z⁻¹ - φ (DP t)‖ ≤
      T * ‖P t - p₀‖ ^ 2 + B * ‖P t - p₀ - DP t‖ := by
    have e : s5cf_exterior_reciprocal (P t) z⁻¹ - s5cf_exterior_reciprocal p₀ z⁻¹ - φ (DP t) =
        (s5cf_exterior_reciprocal (p₀ + (P t - p₀)) z⁻¹ - s5cf_exterior_reciprocal p₀ z⁻¹ - φ (P t - p₀)) +
          φ (P t - p₀ - DP t) := by
      rw [hEt, map_sub φ (P t - p₀) (DP t)]; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (hTK _ hqρ) ?_)
    exact (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_right hBK (norm_nonneg _))
  have hβ : ‖φ (DP t)‖ ≤ B * ‖DP‖ * ‖t‖ := by
    calc ‖φ (DP t)‖ ≤ ‖φ‖ * ‖DP t‖ := φ.le_opNorm _
      _ ≤ B * (‖DP‖ * ‖t‖) := mul_le_mul hBK (DP.le_opNorm t) (norm_nonneg _) hB0
      _ = B * ‖DP‖ * ‖t‖ := by ring
  have hinv := s3dg_inv_est hm0 hmK hMK hα hβ hs
  have hgt : gsans (beltramiMul (a + t • μ) κ) z = (s5cf_exterior_reciprocal (P t) z⁻¹)⁻¹ := by
    show _ = (s5cf_exterior_reciprocal (beltramiMul (a + t • μ) κ, star (beltramiMul (a + t • μ) κ)) z⁻¹)⁻¹
    rw [s3d5_recip hνt hzr, inv_inv]
  have hg : gsans (beltramiMul a κ) z = (s5cf_exterior_reciprocal p₀ z⁻¹)⁻¹ := by
    rw [hp₀, s3d5_recip hν0 hzr, inv_inv]
  have he : gsans (beltramiMul (a + t • μ) κ) z - gsans (beltramiMul a κ) z -
      ((-(gsans (beltramiMul a κ) z) ^ 2) • ((φ.restrictScalars ℝ).comp DP)) t =
      (s5cf_exterior_reciprocal (P t) z⁻¹)⁻¹ - (s5cf_exterior_reciprocal p₀ z⁻¹)⁻¹ +
        φ (DP t) / s5cf_exterior_reciprocal p₀ z⁻¹ ^ 2 := by
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', smul_eq_mul]
    rw [hgt, hg]
    ring
  show ‖gsans (beltramiMul (a + t • μ) κ) z - gsans (beltramiMul a κ) z -
      ((-(gsans (beltramiMul a κ) z) ^ 2) • ((φ.restrictScalars ℝ).comp DP)) t‖ ≤ ε * ‖t‖
  rw [he]
  exact hinv.trans hfin

/-- [(V-A-g) helper] The chart `(t, w) ↦ 𝗀_t(w) = 1/E(p_t, 1/w)` is jointly real differentiable at `(0, z)`,
`z ∈ 𝔻*`, with `w`-part `𝗀'(z)`. -/
theorem s3dg_joint {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (μ : LinfStar) {z : ℂ}
    (hz : 1 < ‖z‖) :
    ∃ D : ℂ × ℂ →L[ℝ] ℂ, HasFDerivAt (fun p : ℂ × ℂ => gsans (beltramiMul (a + p.1 • μ) κ) p.2) D ((0 : ℂ), z) ∧
      ∀ w : ℂ, D (0, w) = deriv (gsans (beltramiMul a κ)) z * w := by
  have hν0 : beltramiMul a κ ∈ LinfStarBall := bg_mul_mem_ball hκ ha
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  set p₀ : LinfStar × LinfStar := (beltramiMul a κ, star (beltramiMul a κ)) with hp₀
  set Ê : (LinfStar × LinfStar) × ℂ → ℂ := fun q => s5cf_exterior_reciprocal q.1 q.2 with hÊ
  set P : ℂ → LinfStar × LinfStar := fun t =>
    (beltramiMul (a + t • μ) κ, star (beltramiMul (a + t • μ) κ)) with hP
  have hP0 : P 0 = p₀ := by simp [hP, hp₀]
  have hPd : DifferentiableAt ℝ P 0 := by
    have hν : DifferentiableAt ℝ (fun t : ℂ => beltramiMul (a + t • μ) κ) 0 :=
      (s35wn_nu_diff hκ ha μ).restrictScalars ℝ
    have hs : DifferentiableAt ℝ (fun t : ℂ => star (beltramiMul (a + t • μ) κ)) 0 :=
      DifferentiableAt.comp (g := fun ν : LinfStar => star ν) (0 : ℂ)
        (s5cf_star_analytic (beltramiMul (a + (0 : ℂ) • μ) κ)).differentiableAt hν
    exact hν.prodMk hs
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; linarith
  have hzD : z⁻¹ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz)
  have hA : AnalyticAt ℂ Ê (p₀, z⁻¹) := s5cf_exterior_reciprocal_analytic hν0 hzD
  have hg0 : gsans (beltramiMul a κ) z ≠ 0 := by
    intro h
    obtain ⟨ε, hε, -, hl⟩ := s3d5_lower hν0
    have h1 := hl z hz.le
    rw [← gMu_eq_normalizedWeldingExterior hν0 hz, ← S2C.s2c_gsans_eq hν0, h, norm_zero] at h1
    linarith
  have hEz : Ê (p₀, z⁻¹) = (gsans (beltramiMul a κ) z)⁻¹ := s3d5_recip hν0 hz
  have hne : Ê (p₀, z⁻¹) ≠ 0 := by rw [hEz]; exact inv_ne_zero hg0
  set G : ℂ × ℂ → ℂ := fun p => gsans (beltramiMul (a + p.1 • μ) κ) p.2 with hG
  have hext : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hGe : G =ᶠ[𝓝 ((0 : ℂ), z)] fun p => (Ê (P p.1, p.2⁻¹))⁻¹ := by
    have h1 : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), z),
        a + p.1 • μ ∈ LinfStarBall ∧ beltramiMul (a + p.1 • μ) κ ∈ LinfStarBall :=
      Filter.Tendsto.eventually (f := Prod.fst) (continuous_fst.tendsto ((0 : ℂ), z)) (s35wn_mem hκ ha1 μ)
    have h2 : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), z), 1 < ‖p.2‖ :=
      Filter.Tendsto.eventually (f := Prod.snd) (continuous_snd.tendsto ((0 : ℂ), z)) (hext.mem_nhds hz)
    filter_upwards [h1, h2] with p hp1 hp2
    show gsans (beltramiMul (a + p.1 • μ) κ) p.2 =
      (s5cf_exterior_reciprocal (beltramiMul (a + p.1 • μ) κ, star (beltramiMul (a + p.1 • μ) κ)) p.2⁻¹)⁻¹
    rw [s3d5_recip hp1.2 hp2, inv_inv]
  have hGd : DifferentiableAt ℝ G ((0 : ℂ), z) := by
    have hc1 : DifferentiableAt ℝ (fun p : ℂ × ℂ => P p.1) ((0 : ℂ), z) :=
      DifferentiableAt.comp (g := P) (f := Prod.fst) ((0 : ℂ), z) hPd differentiableAt_fst
    have hc2 : DifferentiableAt ℝ (fun p : ℂ × ℂ => p.2⁻¹) ((0 : ℂ), z) :=
      DifferentiableAt.comp (g := fun w : ℂ => w⁻¹) (f := Prod.snd) ((0 : ℂ), z)
        ((differentiableAt_inv (𝕜 := ℂ) hz0).restrictScalars ℝ) differentiableAt_snd
    have hin : DifferentiableAt ℝ (fun p : ℂ × ℂ => (P p.1, p.2⁻¹)) ((0 : ℂ), z) := hc1.prodMk hc2
    have hE : DifferentiableAt ℝ Ê (P 0, z⁻¹) := by
      rw [hP0]
      exact hA.differentiableAt.restrictScalars ℝ
    have hne' : Ê (P 0, z⁻¹) ≠ 0 := by rw [hP0]; exact hne
    have hcomp := hE.comp ((0 : ℂ), z) hin
    exact (((differentiableAt_inv (𝕜 := ℂ) hne').restrictScalars ℝ).comp ((0 : ℂ), z) hcomp).congr_of_eventuallyEq hGe
  set D := fderiv ℝ G ((0 : ℂ), z) with hD
  have hGD : HasFDerivAt G D ((0 : ℂ), z) := hGd.hasFDerivAt
  -- `𝗀` is holomorphic at `z`
  have hgd : DifferentiableAt ℂ (gsans (beltramiMul a κ)) z := by
    have hEa : AnalyticAt ℂ (fun w => Ê (p₀, w)) z⁻¹ := hA.comp (analyticAt_const.prod analyticAt_id)
    have hne2 : (fun w => Ê (p₀, w)) z⁻¹ ≠ 0 := hne
    have h1 := (hEa.differentiableAt.comp z (differentiableAt_inv hz0)).inv hne2
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hext.mem_nhds hz] with w hw
    show gsans (beltramiMul a κ) w = (s5cf_exterior_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) w⁻¹)⁻¹
    rw [s3d5_recip hν0 hw, inv_inv]
  have hD2v : ∀ w : ℂ, D (0, w) = deriv (gsans (beltramiMul a κ)) z * w := by
    have h1 : HasFDerivAt (fun w => G (0, w)) (D.comp (ContinuousLinearMap.inr ℝ ℂ ℂ)) z :=
      HasFDerivAt.comp (g := G) (f := fun w : ℂ => ((0 : ℂ), w)) z hGD (hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : ℂ) z)
    have h2 : (fun w => G (0, w)) = gsans (beltramiMul a κ) := funext fun w => by
      simp only [hG, zero_smul, add_zero]
    rw [h2] at h1
    have h3 := h1.unique (hgd.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
    intro w
    have h4 := congrArg (fun L : ℂ →L[ℝ] ℂ => L w) h3
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h4
    rw [h4, mul_comm]
  exact ⟨D, hGD, hD2v⟩

/-- [(V-A-g) helper] **Identification core.** If `𝗀_t(c(t)) = R(t)` near `t = 0`, with `c(0) = z ∈ 𝔻*` and real
derivatives `c'(0) = D_c`, `R'(0) = R'`, then `t ↦ 𝗀_t(z)` has real derivative `R' - 𝗀'(z) D_c` at `0` (chain
rule through the jointly differentiable chart `(t, w) ↦ 1/E(p_t, 1/w)`). -/
theorem s3dg_core {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (μ : LinfStar) {z : ℂ}
    (hz : 1 < ‖z‖) {c Rf : ℂ → ℂ} {Dc R' : ℂ →L[ℝ] ℂ} (hc : HasFDerivAt c Dc 0) (hc0 : c 0 = z)
    (hR : HasFDerivAt Rf R' 0)
    (heq : ∀ᶠ t in 𝓝 (0 : ℂ), gsans (beltramiMul (a + t • μ) κ) (c t) = Rf t) :
    HasFDerivAt (fun t : ℂ => gsans (beltramiMul (a + t • μ) κ) z)
      (R' - (deriv (gsans (beltramiMul a κ)) z) • Dc) 0 := by
  obtain ⟨D, hGD, hD2v⟩ := s3dg_joint hκ ha μ hz
  have hΛ : HasFDerivAt (fun t : ℂ => gsans (beltramiMul (a + t • μ) κ) z) (D.comp (ContinuousLinearMap.inl ℝ ℂ ℂ)) 0 :=
    HasFDerivAt.comp (g := fun p : ℂ × ℂ => gsans (beltramiMul (a + p.1 • μ) κ) p.2) (f := fun t : ℂ => (t, z))
      (0 : ℂ) hGD (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℂ) z)
  have hG' : HasFDerivAt (fun p : ℂ × ℂ => gsans (beltramiMul (a + p.1 • μ) κ) p.2) D ((0 : ℂ), c 0) := by
    rw [hc0]; exact hGD
  have hcc : HasFDerivAt (fun t : ℂ => gsans (beltramiMul (a + t • μ) κ) (c t))
      (D.comp ((ContinuousLinearMap.id ℝ ℂ).prod Dc)) 0 :=
    HasFDerivAt.comp (g := fun p : ℂ × ℂ => gsans (beltramiMul (a + p.1 • μ) κ) p.2) (f := fun t : ℂ => (t, c t))
      (0 : ℂ) hG' ((hasFDerivAt_id (0 : ℂ)).prodMk hc)
  have he := hcc.unique (hR.congr_of_eventuallyEq heq)
  refine hΛ.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  have h1 := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) he
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply] at h1
  have h2 : D (v, Dc v) = D (v, 0) + D (0, Dc v) := by rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← h1, h2, hD2v]
  ring

/-- [(V-A-g) helper] The transported kernel `k(ζ, σ) - ζ/(σN(σ)) - ABζ²/N(σ) = N(ζ)/(N(σ)(σ - ζ))`,
`N(x) = x(1 + Bx)(Ax - 1)`. -/
theorem s3dg_kalg {σ ζ A B : ℂ} (hσ0 : σ ≠ 0) (hσζ : σ - ζ ≠ 0) (hσB : 1 + B * σ ≠ 0) (hσA : A * σ - 1 ≠ 0) :
    1 / (σ - ζ) - 1 / σ - ζ / σ ^ 2 - ζ * (1 / (σ * (σ * (1 + B * σ) * (A * σ - 1)))) -
        ζ ^ 2 * (A * B / (σ * (1 + B * σ) * (A * σ - 1))) =
      ζ * (1 + B * ζ) * (A * ζ - 1) / (σ * (1 + B * σ) * (A * σ - 1) * (σ - ζ)) := by
  obtain ⟨u, hu⟩ : ∃ u, u = 1 + B * σ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = A * σ - 1 := ⟨_, rfl⟩
  rw [← hu] at hσB ⊢
  rw [← hv] at hσA ⊢
  field_simp
  rw [hu, hv]
  ring

/-- [(V-A-g) helper] At the pole value `ζ = -1/(P d)` of the transported kernel (`1 + P d ζ = 0`, i.e. `N(ζ) = 0`),
`V̇(ζ) + I₁ ζ + I₂ ζ² = -(1/π)∫ θ g'² N(ζ)/(N(g)(g - ζ)) = 0`. -/
theorem s3dg_vanish {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (θ : LinfStar) {ζ : ℂ}
    (hζ : 1 + s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * deriv (normalizedSolution (extB μ)) 0 * ζ = 0) :
    -(1 / π : ℂ) * (∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
        (1 / (gsans μ ξ - ζ) - 1 / gsans μ ξ - ζ / gsans μ ξ ^ 2)) +
      ζ * ((1 / π : ℂ) * ∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
        (1 / (gsans μ ξ * (gsans μ ξ * (1 + s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) *
            deriv (normalizedSolution (extB μ)) 0 * gsans μ ξ) *
          (deriv (normalizedSolution (extB μ)) 0 * (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0)) *
            gsans μ ξ - 1))))) +
      ζ ^ 2 * ((1 / π : ℂ) * ∫ ξ in unitDiscExterior, θ ξ * deriv (gsans μ) ξ ^ 2 *
        (deriv (normalizedSolution (extB μ)) 0 * (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0)) *
            (s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * deriv (normalizedSolution (extB μ)) 0) /
          (gsans μ ξ * (1 + s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) *
            deriv (normalizedSolution (extB μ)) 0 * gsans μ ξ) *
            (deriv (normalizedSolution (extB μ)) 0 * (1 - s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0)) *
              gsans μ ξ - 1)))) = 0 := by
  set P := s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) with hP
  set d := deriv (normalizedSolution (extB μ)) 0 with hd
  set g := gsans μ with hg
  have hd0 : d ≠ 0 := (AppA.acc_wB_rep hμ).1
  have hB0 : P * d ≠ 0 := fun h => by rw [h, zero_mul, add_zero] at hζ; exact one_ne_zero hζ
  obtain ⟨ε, hε, hreg⟩ := s3dv_g_region hμ
  have himg : g '' unitDiscExterior ⊆ {σ : ℂ | ε ≤ ‖σ‖} := by
    rintro _ ⟨ξ, hξ, rfl⟩
    exact hreg ξ hξ
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hθm : AEStronglyMeasurable θ (volume.restrict unitDiscExterior) := Lp.aestronglyMeasurable θ
  have hθb := LinfStar_ae_norm_le θ
  have hAB : d * (1 - P) + P * d ≠ 0 := by
    rw [show d * (1 - P) + P * d = d by ring]
    exact hd0
  have i1 : Integrable (fun ξ => θ ξ * deriv g ξ ^ 2 * (1 / (g ξ - ζ) - 1 / g ξ - ζ / g ξ ^ 2))
      (volume.restrict unitDiscExterior) :=
    s3dv_int_transfer (h := fun σ => 1 / (σ - ζ) - 1 / σ - ζ / σ ^ 2) hμ hθm hθb ((s3dv_int_k hε ζ).mono_set himg)
  have i2 : Integrable (fun ξ => θ ξ * deriv g ξ ^ 2 *
      (1 / (g ξ * (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1))))) (volume.restrict unitDiscExterior) :=
    s3dv_int_transfer (h := fun σ => 1 / (σ * (σ * (1 + P * d * σ) * (d * (1 - P) * σ - 1)))) hμ hθm hθb
      ((s3dv_int_N1 hε hAB).mono_set himg)
  have i3 : Integrable (fun ξ => θ ξ * deriv g ξ ^ 2 *
      (d * (1 - P) * (P * d) / (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1))))
      (volume.restrict unitDiscExterior) :=
    s3dv_int_transfer (h := fun σ => d * (1 - P) * (P * d) / (σ * (1 + P * d * σ) * (d * (1 - P) * σ - 1))) hμ hθm hθb
      ((s3dv_int_N2 hε hAB).mono_set himg)
  have hsplit : -(1 / π : ℂ) * (∫ ξ in unitDiscExterior, θ ξ * deriv g ξ ^ 2 *
        (1 / (g ξ - ζ) - 1 / g ξ - ζ / g ξ ^ 2)) +
      ζ * ((1 / π : ℂ) * ∫ ξ in unitDiscExterior, θ ξ * deriv g ξ ^ 2 *
        (1 / (g ξ * (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1))))) +
      ζ ^ 2 * ((1 / π : ℂ) * ∫ ξ in unitDiscExterior, θ ξ * deriv g ξ ^ 2 *
        (d * (1 - P) * (P * d) / (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1)))) =
      -(1 / π : ℂ) * ∫ ξ in unitDiscExterior, (θ ξ * deriv g ξ ^ 2 * (1 / (g ξ - ζ) - 1 / g ξ - ζ / g ξ ^ 2) -
        ζ * (θ ξ * deriv g ξ ^ 2 * (1 / (g ξ * (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1))))) -
        ζ ^ 2 * (θ ξ * deriv g ξ ^ 2 *
          (d * (1 - P) * (P * d) / (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1))))) := by
    rw [integral_sub, integral_sub, integral_const_mul, integral_const_mul]
    all_goals first
      | exact i1
      | exact i2.const_mul ζ
      | exact i1.sub (i2.const_mul ζ)
      | exact i3.const_mul (ζ ^ 2)
      | ring1
  rw [hsplit]
  have h0 : ∫ ξ in unitDiscExterior, (θ ξ * deriv g ξ ^ 2 * (1 / (g ξ - ζ) - 1 / g ξ - ζ / g ξ ^ 2) -
        ζ * (θ ξ * deriv g ξ ^ 2 * (1 / (g ξ * (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1))))) -
        ζ ^ 2 * (θ ξ * deriv g ξ ^ 2 *
          (d * (1 - P) * (P * d) / (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1))))) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [s3dv_g_ne_ae hμ ζ, s3dv_g_ne_ae hμ (1 / (d * (1 - P))), ae_restrict_mem hEm]
      with ξ h1 h2 hξ
    have hσ0 : g ξ ≠ 0 := norm_pos_iff.mp (hε.trans_le (hreg ξ hξ))
    have hσζ : g ξ - ζ ≠ 0 := sub_ne_zero.mpr h1
    have hσB : 1 + P * d * g ξ ≠ 0 := fun h => h1 (mul_left_cancel₀ hB0 (by linear_combination h - hζ))
    have hσA : d * (1 - P) * g ξ - 1 ≠ 0 := fun h => by
      have hA0 : d * (1 - P) ≠ 0 := fun h' => by
        rw [h', zero_mul, zero_sub] at h
        exact one_ne_zero (neg_eq_zero.mp h)
      exact h2 (by rw [eq_div_iff hA0]; linear_combination h)
    have key := s3dg_kalg hσ0 hσζ hσB hσA
    have e : θ ξ * deriv g ξ ^ 2 * (1 / (g ξ - ζ) - 1 / g ξ - ζ / g ξ ^ 2) -
        ζ * (θ ξ * deriv g ξ ^ 2 * (1 / (g ξ * (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1))))) -
        ζ ^ 2 * (θ ξ * deriv g ξ ^ 2 *
          (d * (1 - P) * (P * d) / (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1)))) =
        θ ξ * deriv g ξ ^ 2 * (1 / (g ξ - ζ) - 1 / g ξ - ζ / g ξ ^ 2 -
          ζ * (1 / (g ξ * (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1)))) -
          ζ ^ 2 * (d * (1 - P) * (P * d) / (g ξ * (1 + P * d * g ξ) * (d * (1 - P) * g ξ - 1)))) := by ring
    simp only [Pi.zero_apply]
    rw [e, key, hζ]
    simp only [mul_zero, zero_mul, zero_div]
  rw [h0, mul_zero]

/-- [(V-A-g) helper] Quotient algebra for `Φ_t(W_t) = (W_t/d_t)/(1 - P_t W_t)`: the `t`- and `t̄`-coefficients are
`Φ'(w) Ẇ - (ḋ/d) ζ + P₁ d ζ²` and `P₂ d ζ²`, `ζ = w/(d(1 - Pw))`. (The derivative hypotheses only fix the names.) -/
theorem s3dg_algA {d P w Wd dd P₁ P₂ : ℂ} {Wf df Pf : ℂ → ℂ} (hd : d ≠ 0) (hw : -P * w + 1 ≠ 0)
    (_hW : HasDerivAt Wf Wd 0) (_hdd : HasDerivAt df dd 0)
    (_hP : HasFDerivAt Pf (P₁ • (1 : ℂ →L[ℝ] ℂ) + P₂ • (conjCLE : ℂ →L[ℝ] ℂ)) 0) :
    ((-dd / d ^ 2 * w + 1 / d * Wd) * (-P * w + 1) - (-P₁ * w + -P * Wd) * (1 / d * w)) / (-P * w + 1) ^ 2 =
        1 / (d * (1 - P * w) ^ 2) * Wd - dd / d * (w / (d * (1 - P * w))) + P₁ * d * (w / (d * (1 - P * w))) ^ 2 ∧
      ((0 * w + 1 / d * 0) * (-P * w + 1) - (-P₂ * w + -P * 0) * (1 / d * w)) / (-P * w + 1) ^ 2 =
        P₂ * d * (w / (d * (1 - P * w))) ^ 2 := by
  have hw' : 1 - P * w ≠ 0 := by
    intro h
    apply hw
    linear_combination h
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- [(V-A-g) helper] Quotient algebra at the pole image `ζ = (1/d)/(-P)` (the value `Φ_t(∞)`). -/
theorem s3dg_algB {d P dd P₁ P₂ ζ : ℂ} {df Pf : ℂ → ℂ} (hd : d ≠ 0) (hP : -P ≠ 0) (hζ : ζ = 1 / d / -P)
    (_hdd : HasDerivAt df dd 0)
    (_hP : HasFDerivAt Pf (P₁ • (1 : ℂ →L[ℝ] ℂ) + P₂ • (conjCLE : ℂ →L[ℝ] ℂ)) 0) :
    ((-dd / d ^ 2) * -P - -P₁ * (1 / d)) / (-P) ^ 2 = -(dd / d) * ζ + P₁ * d * ζ ^ 2 ∧
      ((0 : ℂ) * -P - -P₂ * (1 / d)) / (-P) ^ 2 = P₂ * d * ζ ^ 2 := by
  have hP' : P ≠ 0 := fun h => hP (by rw [h, neg_zero])
  subst hζ
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- [(V-A-g) helper] **Pointwise identification.** At each `z ∈ 𝔻*`, `t ↦ 𝗀_t(z)` has the real derivative
`X(z) t + Y(z) t̄` of the frozen g-side expansion. Write `z = w_{ν₀}(y)`: for small `t`,
`w_{ν_t}(y) = w_{λ_t}(z)` (`λ_t = (a + t m) * a⁻¹`) and `𝗀_t(w_{λ_t} z) = Φ_t(W_t y)` (`s3dv_grep`); differentiate both
sides (`s3dg_core`, D0, `s3dv_Wdot`, `s3dv_ident`, `s3dv_norm`). If `z = w_{ν₀}(∞)`, use `𝗀_t(w_{ν_t}∞) = Φ_t(∞)`
instead, where `V̇ + I₁ζ + I₂ζ²` vanishes (`s3dg_vanish`). -/
theorem s3dg_point {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    HasFDerivAt (fun t : ℂ => gsans (beltramiMul (a + t • toLinf m) κ) z)
      (((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) + (((1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 * ((deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0))) * (s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) / (gsans (beltramiMul a κ) u * (1 + (s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) * gsans (beltramiMul a κ) u) * ((deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0))) * gsans (beltramiMul a κ) u - 1)))) + dz (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) 0 * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) • (1 : ℂ →L[ℝ] ℂ) + ((dzbar (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) 0 * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) • (conjCLE : ℂ →L[ℝ] ℂ)) 0 := by
  have hz1 : 1 < ‖z‖ := hz
  have ha1 : ‖a‖ < 1 := has.trans delta0_bounds.2
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.mpr ha1
  have hν0 : beltramiMul a κ ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  have hν00 : beltramiMul (a + (0 : ℂ) • toLinf m) κ = beltramiMul a κ := by rw [zero_smul, add_zero]
  have hb0 : beltramiMul (a + (0 : ℂ) • toLinf m) κ ∈ LinfStarBall := by rw [hν00]; exact hν0
  have hd0 : deriv (normalizedSolution (extB (beltramiMul a κ))) 0 ≠ 0 := (AppA.acc_wB_rep hν0).1
  -- the reciprocal pole `P_t` and the scale `d_t`
  have hPfd : HasFDerivAt (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0))
      (dz (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) 0 • (1 : ℂ →L[ℝ] ℂ) + dzbar (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) 0 • (conjCLE : ℂ →L[ℝ] ℂ)) 0 :=
    s3dg_fd (s35wn_line_diff κ.2 haB (toLinf m) (s5t53_P_analytic hν0).differentiableAt)
  have hnP : HasFDerivAt (fun t : ℂ => -(fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) t)
      ((-dz (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) 0) • (1 : ℂ →L[ℝ] ℂ) + (-dzbar (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) 0) • (conjCLE : ℂ →L[ℝ] ℂ)) 0 := by
    refine hPfd.neg.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul]
    ring
  have hdfd : DifferentiableAt ℂ
      (fun t : ℂ => deriv (normalizedSolution (extB (beltramiMul (a + t • toLinf m) κ))) 0) 0 :=
    DifferentiableAt.comp (g := fun ν : LinfStar => deriv (normalizedSolution (extB ν)) 0) (0 : ℂ)
      (s5cf_planeB_deriv_analytic hb0).differentiableAt (s35wn_nu_diff κ.2 haB (toLinf m))
  have hdf0 : deriv (normalizedSolution (extB (beltramiMul (a + (0 : ℂ) • toLinf m) κ))) 0 ≠ 0 := by
    rw [hν00]; exact hd0
  have hinvd : HasDerivAt (fun t : ℂ => 1 / deriv (normalizedSolution (extB (beltramiMul (a + t • toLinf m) κ))) 0)
      (-deriv (fun t : ℂ => deriv (normalizedSolution (extB (beltramiMul (a + t • toLinf m) κ))) 0) 0 /
        deriv (normalizedSolution (extB (beltramiMul (a + (0 : ℂ) • toLinf m) κ))) 0 ^ 2) 0 := by
    have h := hdfd.hasDerivAt.inv hdf0
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => one_div _)
  have hinvF := s3dg_hol hinvd
  -- the Model A factor `w_{λ_t}` (D0)
  have hlam := s3d0_curve haB (toLinf m)
  obtain ⟨hcd, hc1, hc2⟩ := s3d_D0 hκ hκD ha has haL haD hm hmD z hz
  have hcF := s3dg_fd hcd
  rw [hc1, hc2] at hcF
  have hc0 : wA (beltramiMul (a + (0 : ℂ) • toLinf m) (beltramiInv a)) z = z := by
    show finPart (wAS (beltramiMul (a + (0 : ℂ) • toLinf m) (beltramiInv a)) (z : ExtPlane)) = z
    rw [hlam.2, grp_wAS_zero, id, finPart_coe]
  have hgrp : ∀ᶠ t in 𝓝 (0 : ℂ), wAS (beltramiMul (a + t • toLinf m) κ) =
      wAS (beltramiMul (a + t • toLinf m) (beltramiInv a)) ∘ wAS (beltramiMul a κ) := by
    filter_upwards [s35wn_mem κ.2 ha1 (toLinf m)] with t ht
    rw [grp_wAS_mul ht.1 κ.2, grp_wAS_mul ht.1 (grp_inv_mem haB), grp_wAS_mul haB κ.2, Function.comp_assoc,
      ← Function.comp_assoc (wAS (beltramiInv a)), grp_wAS_inv_right haB, Function.id_comp]
  have hlamc : ContinuousAt (fun t : ℂ => beltramiMul (a + t • toLinf m) (beltramiInv a)) 0 := hlam.1.continuousAt
  have hwc : ContinuousAt (fun t : ℂ => wAS (beltramiMul (a + t • toLinf m) (beltramiInv a)) (z : ExtPlane)) 0 := by
    have h0m : (beltramiMul (a + (0 : ℂ) • toLinf m) (beltramiInv a), (z : ExtPlane)) ∈
        LinfStarBall ×ˢ (univ : Set ExtPlane) := by
      refine ⟨?_, mem_univ _⟩
      rw [hlam.2]
      simp [LinfStarBall]
    have hU : LinfStarBall ×ˢ (univ : Set ExtPlane) ∈
        𝓝 (beltramiMul (a + (0 : ℂ) • toLinf m) (beltramiInv a), (z : ExtPlane)) :=
      ((isOpen_ball : IsOpen LinfStarBall).prod isOpen_univ).mem_nhds h0m
    exact ContinuousAt.comp (g := fun p : LinfStar × ExtPlane => wAS p.1 p.2)
      (f := fun t : ℂ => (beltramiMul (a + t • toLinf m) (beltramiInv a), (z : ExtPlane)))
      (AppA.acc_wAS_cont.continuousAt hU) (hlamc.prodMk continuousAt_const)
  have hfin : ∀ᶠ t in 𝓝 (0 : ℂ), wAS (beltramiMul (a + t • toLinf m) (beltramiInv a)) (z : ExtPlane) ≠ extInf := by
    refine hwc.eventually_ne ?_
    show wAS (beltramiMul (a + (0 : ℂ) • toLinf m) (beltramiInv a)) (z : ExtPlane) ≠ extInf
    rw [hlam.2, grp_wAS_zero]
    exact OnePoint.coe_ne_infty z
  have hcz : ∀ᶠ t in 𝓝 (0 : ℂ), ((wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z : ℂ) : ExtPlane) =
      wAS (beltramiMul (a + t • toLinf m) (beltramiInv a)) (z : ExtPlane) := hfin.mono fun t ht => s3dg_fin ht
  have hcext : ∀ᶠ t in 𝓝 (0 : ℂ), 1 < ‖wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z‖ := by
    have h1 : 1 < ‖wA (beltramiMul (a + (0 : ℂ) • toLinf m) (beltramiInv a)) z‖ := by rw [hc0]; exact hz1
    exact hcF.continuousAt.norm.eventually (lt_mem_nhds h1)
  -- the transported first variation and the normalization
  have htan : fderiv ℂ (fun l => beltramiMul l κ) a (toLinf m) =
      QCV.qcv_rightDerivative (beltramiMul a κ) (Rnm (toLinf m) a) := by
    have h1 := s4g_tangent κ.2 haB (toLinf m)
    rw [← h1, QCV.qcv_rightDerivative_Rnm hν0]
  have eN := s3dv_norm κ.2 haB (toLinf m)
  have eV : (-(1 / π : ℂ) * ∫ u in unitDiscExterior, Rnm (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) = (-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) := by
    congr 1
    exact integral_congr_ae ((WPCV.wpcv_RnmFun_ae haB (toLinf m)).mono fun ξ h => by simp only [h])
  have eQ : ((1 / π : ℂ) * ∫ u in unitDiscExterior, Rnm (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 * ((deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0))) * (s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) / (gsans (beltramiMul a κ) u * (1 + (s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) * gsans (beltramiMul a κ) u) * ((deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0))) * gsans (beltramiMul a κ) u - 1)))) = ((1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 * ((deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0))) * (s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) / (gsans (beltramiMul a κ) u * (1 + (s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) * gsans (beltramiMul a κ) u) * ((deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0))) * gsans (beltramiMul a κ) u - 1)))) := by
    congr 1
    exact integral_congr_ae ((WPCV.wpcv_RnmFun_ae haB (toLinf m)).mono fun ξ h => by simp only [h])
  set Ys := Function.invFun (wAS (beltramiMul a κ)) (z : ExtPlane) with hYs
  have hYz : wAS (beltramiMul a κ) Ys = z := Function.rightInverse_invFun (wAS_bijective _).2 _
  by_cases hY : Ys = extInf
  · -- `z = w_{ν₀}(∞)`: `𝗀_t(w_{ν_t} ∞) = Φ_t(∞) = (1/d_t)/(-P_t)`
    have hzi : wAS (beltramiMul a κ) extInf = z := by rw [← hY]; exact hYz
    have heqB : ∀ᶠ t in 𝓝 (0 : ℂ), (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) t ≠ 0 ∧
        gsans (beltramiMul (a + t • toLinf m) κ) (wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z) =
          (fun t : ℂ => 1 / deriv (normalizedSolution (extB (beltramiMul (a + t • toLinf m) κ))) 0) t /
            (fun t : ℂ => -(fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) t) t := by
      filter_upwards [s35wn_mem κ.2 ha1 (toLinf m), hgrp, hcz, hcext] with t ht hg hc hce
      have hinf : wAS (beltramiMul (a + t • toLinf m) κ) extInf =
          ((wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z : ℂ) : ExtPlane) := by
        rw [hg, Function.comp_apply, hzi, hc]
      have hinvf : Function.invFun (wAS (beltramiMul (a + t • toLinf m) κ))
          ((wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z : ℂ) : ExtPlane) = extInf := by
        rw [← hinf]
        exact Function.leftInverse_invFun (wAS_bijective _).1 extInf
      have hfac := gMu_sphere_factorization ht.2 hce
      have hP' : finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB (beltramiMul (a + t • toLinf m) κ)))
          (Function.invFun (wAS (beltramiMul (a + t • toLinf m) κ)) extInf))) =
          s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ))
            (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0) :=
        s35wn_pole ht.2
      rw [hinvf, (AppA.acc_wB_rep ht.2).2.2, OnePoint.map_infty, hP'] at hfac
      by_cases hP : (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) t = 0
      · rw [show s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ))
            (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0) = 0 from hP,
          neg_zero, mobiusExt_infty_of_eq rfl] at hfac
        exact absurd hfac (OnePoint.coe_ne_infty _)
      · rw [mobiusExt_infty_of_ne (neg_ne_zero.mpr hP)] at hfac
        refine ⟨hP, ?_⟩
        rw [S2C.s2c_gsans_eq ht.2]
        exact OnePoint.coe_injective hfac
    have hPne : (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) 0 ≠ 0 := heqB.self_of_nhds.1
    have hRd := s3d2u_div hnP hinvF rfl rfl (neg_ne_zero.mpr hPne)
    have hcore := s3dg_core κ.2 haB (toLinf m) hz1 hcF hc0 hRd (heqB.mono fun t h => h.2)
    have hg0 : gsans (beltramiMul a κ) z = 1 / deriv (normalizedSolution (extB (beltramiMul a κ))) 0 /
        -s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) := by
      have h := heqB.self_of_nhds.2
      rw [hc0] at h
      simp only [zero_smul, add_zero] at h
      exact h
    have hP0 : s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ))
        (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) ≠ 0 := by
      have h := hPne
      simp only [zero_smul, add_zero] at h
      exact h
    have hζ : 1 + s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ))
        (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) *
        deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * gsans (beltramiMul a κ) z = 0 := by
      rw [hg0]
      field_simp
      try ring
    have hv := s3dg_vanish hν0 (Rnm (toLinf m) a) hζ
    have alg := s3dg_algB hd0 (neg_ne_zero.mpr hP0) hg0 hdfd.hasDerivAt hPfd
    simp only [zero_smul, add_zero] at hcore
    refine hcore.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul]
    linear_combination v * (alg.1 + gsans (beltramiMul a κ) z * eN - hv + eV +
      gsans (beltramiMul a κ) z ^ 2 * eQ) + conj v * alg.2
  · -- `z = w_{ν₀}(y)` with `y ∈ 𝔻*` off the pole
    set y := finPart Ys with hy
    have hyY : (y : ExtPlane) = Ys := s3dg_fin hY
    have hyz : wAS (beltramiMul a κ) (y : ExtPlane) = z := by rw [hyY]; exact hYz
    have hyext : 1 < ‖y‖ := by
      rcases lt_trichotomy ‖y‖ 1 with h | h | h
      · obtain ⟨u, hu, hu'⟩ := wAS_maps_disc hν0 h
        rw [hyz] at hu'
        have h2 := OnePoint.coe_injective hu'
        rw [h2] at hz1
        linarith
      · obtain ⟨u, hu, hu'⟩ := wAS_maps_circle hν0 h
        rw [hyz] at hu'
        have h2 := OnePoint.coe_injective hu'
        rw [h2, hu] at hz1
        exact absurd hz1 (lt_irrefl 1)
      · exact h
    have hypole : wAS (beltramiMul a κ) (y : ExtPlane) ≠ extInf := by rw [hyz]; exact OnePoint.coe_ne_infty z
    have hwy : wA (beltramiMul a κ) y = z := by
      show finPart (wAS _ _) = z
      rw [hyz, finPart_coe]
    have heqA : ∀ᶠ t in 𝓝 (0 : ℂ),
        gsans (beltramiMul (a + t • toLinf m) κ) (wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z) =
          (fun t : ℂ => 1 / deriv (normalizedSolution (extB (beltramiMul (a + t • toLinf m) κ))) 0 *
            normalizedSolution (extB (beltramiMul (a + t • toLinf m) κ)) y + 0) t /
          (fun t : ℂ => -(fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) t * normalizedSolution (extB (beltramiMul (a + t • toLinf m) κ)) y + 1) t := by
      filter_upwards [s35wn_mem κ.2 ha1 (toLinf m), hgrp, hfin] with t ht hg hf
      have hpole' : wAS (beltramiMul (a + t • toLinf m) κ) (y : ExtPlane) ≠ extInf := by
        rw [hg, Function.comp_apply, hyz]
        exact hf
      have hw : wA (beltramiMul (a + t • toLinf m) κ) y = wA (beltramiMul (a + t • toLinf m) (beltramiInv a)) z := by
        show finPart (wAS _ _) = finPart (wAS _ _)
        rw [hg, Function.comp_apply, hyz]
      rw [← hw]
      exact (s3dv_grep ht.2 hyext hpole').2
    have hW := s3dv_Wdot κ.2 haB (toLinf m) y
    have hWF := s3dg_hol hW
    have hF2 := (s3dg_mul hinvF hWF).add_const (0 : ℂ)
    have hF1 := (s3dg_mul hnP hWF).add_const (1 : ℂ)
    have hgr0 := s3dv_grep hν0 hyext hypole
    have hc1ne : (fun t : ℂ => -(fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) t * normalizedSolution (extB (beltramiMul (a + t • toLinf m) κ)) y + 1) 0 ≠ 0 := by
      simp only [zero_smul, add_zero]
      exact hgr0.1
    have hRd := s3d2u_div hF1 hF2 rfl rfl hc1ne
    have hcore := s3dg_core κ.2 haB (toLinf m) hz1 hcF hc0 hRd heqA
    have hw1 : 1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ))
        (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * normalizedSolution (extB (beltramiMul a κ)) y ≠ 0 := by
      intro h
      apply hgr0.1
      linear_combination h
    have hζ : gsans (beltramiMul a κ) z = normalizedSolution (extB (beltramiMul a κ)) y /
        (deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ))
          (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * normalizedSolution (extB (beltramiMul a κ)) y)) := by
      rw [← hwy, hgr0.2, (s3dv_mob_alg hd0 hw1).1]
    have eI := s3dv_ident hν0 (Rnm (toLinf m) a) hw1
    rw [← htan, ← hζ] at eI
    have alg := s3dg_algA hd0 hgr0.1 hW hdfd.hasDerivAt hPfd
    rw [← hζ] at alg
    simp only [zero_smul, add_zero] at hcore
    refine hcore.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul]
    linear_combination v * (alg.1 + eI + gsans (beltramiMul a κ) z * eN + eV +
      gsans (beltramiMul a κ) z ^ 2 * eQ) + conj v * alg.2

/-- **(V-A-g)** Uniform first-order expansion of `𝗀_t` on closed annuli of `𝔻*`, with the explicit pole pair
`Q₁ = I₂ + P₁ d`, `Q₂ = P₂ d` (shared with the f-side). -/
theorem s3dv_expand_g {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    ∀ r₁ r₂ : ℝ, 1 < r₁ → ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ →
      ‖gsans (beltramiMul (a + t • toLinf m) κ) z - gsans (beltramiMul a κ) z -
        (t * ((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) + (((1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 * ((deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0))) * (s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) / (gsans (beltramiMul a κ) u * (1 + (s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0) * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) * gsans (beltramiMul a κ) u) * ((deriv (normalizedSolution (extB (beltramiMul a κ))) 0 * (1 - s5cf_reciprocal (beltramiMul a κ, star (beltramiMul a κ)) (s5cf_alpha (beltramiMul a κ, star (beltramiMul a κ)) 0))) * gsans (beltramiMul a κ) u - 1)))) + dz (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) 0 * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) +
          conj t * ((dzbar (fun t : ℂ => s5cf_reciprocal (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) (s5cf_alpha (beltramiMul (a + t • toLinf m) κ, star (beltramiMul (a + t • toLinf m) κ)) 0)) 0 * deriv (normalizedSolution (extB (beltramiMul a κ))) 0) * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))))‖ ≤ ε * ‖t‖ := by
  -- uniformity from the exterior reciprocal chart (`s3dg_unif`), coefficients from the pointwise
  -- identification (`s3dg_point`) and uniqueness of the derivative
  intro r₁ r₂ hr₁ ε hε
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.mpr (has.trans delta0_bounds.2)
  obtain ⟨Λ, hΛ⟩ := s3dg_unif κ.2 haB (toLinf m)
  obtain ⟨δ, hδ, hb⟩ := hΛ r₁ r₂ hr₁ ε hε
  refine ⟨δ, hδ, fun t ht z hz1 hz2 => ?_⟩
  have hzE : z ∈ unitDiscExterior := (show 1 < ‖z‖ by linarith)
  have hpt := s3dg_point hκ hκD ha has haL haD hm hmD hzE
  have hΛd : HasFDerivAt (fun t : ℂ => gsans (beltramiMul (a + t • toLinf m) κ) z) (Λ z) 0 :=
    s3dg_of_unif (c0 := gsans (beltramiMul a κ) z) fun ε' hε' => by
      obtain ⟨δ', hδ', hb'⟩ := hΛ ‖z‖ ‖z‖ (by linarith) ε' hε'
      exact ⟨δ', hδ', fun t' ht' => hb' t' ht' z le_rfl le_rfl⟩
  have he := hΛd.unique hpt
  have h := hb t ht z hz1 hz2
  rw [he] at h
  refine Eq.trans_le ?_ h
  congr 2
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul]
  ring

/-- **(V-A)** Uniform first-order expansions of the welding pair, with pole coefficients `Q₁, Q₂` common to both sides. -/
theorem s3dv_expand {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    ∃ Q₁ Q₂ : ℂ, (∀ r : ℝ, r < 1 → ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ z ∈ closedBall (0 : ℂ) r,
      ‖fsans (beltramiMul (a + t • toLinf m) κ) z - fsans (beltramiMul a κ) z -
        (t * ((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) + Q₁ * fsans (beltramiMul a κ) z ^ 2) + conj t * (Q₂ * fsans (beltramiMul a κ) z ^ 2))‖ ≤ ε * ‖t‖) ∧
    ∀ r₁ r₂ : ℝ, 1 < r₁ → ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ →
      ‖gsans (beltramiMul (a + t • toLinf m) κ) z - gsans (beltramiMul a κ) z -
        (t * ((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) + Q₁ * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) +
          conj t * (Q₂ * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))))‖ ≤ ε * ‖t‖ := by
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.mpr (has.trans delta0_bounds.2)
  exact ⟨_, _, s3dv_expand_f κ.2 haB m, s3dv_expand_g hκ hκD ha has haL haD hm hmD⟩

/-- **(V)** [shared, 下属4: D1 is its `z`-derivative at points of `𝔻`] First variation of the welding pair along the
line, pointwise and locally uniformly (compacts of `𝔻` and closed annuli of `𝔻*`; Cauchy estimates then give the
`z`-jets for D1 and (E2)). At `κ = 0, a = 0`: `ḟ = ahVar (extB m)` normalized at `0, ∞` plus `c₂ f²`
(`s4v_normalized_first_variation`). -/
theorem s3d_pair_variation {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    (∀ z ∈ unitDisc,
      DifferentiableAt ℝ (fun t : ℂ => fsans (beltramiMul (a + t • toLinf m) κ) z) 0 ∧
      dz (fun t : ℂ => fsans (beltramiMul (a + t • toLinf m) κ) z) 0 = (-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * fsans (beltramiMul a κ) z ^ 2 ∧
      dzbar (fun t : ℂ => fsans (beltramiMul (a + t • toLinf m) κ) z) 0 = ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * fsans (beltramiMul a κ) z ^ 2) ∧
    (∀ z ∈ unitDiscExterior,
      DifferentiableAt ℝ (fun t : ℂ => gsans (beltramiMul (a + t • toLinf m) κ) z) 0 ∧
      dz (fun t : ℂ => gsans (beltramiMul (a + t • toLinf m) κ) z) 0 = (-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) z ^ 2 -
        deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z)))) ∧
      dzbar (fun t : ℂ => gsans (beltramiMul (a + t • toLinf m) κ) z) 0 = ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) z ^ 2 -
        deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) ∧
    (∀ r : ℝ, r < 1 → ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ z ∈ closedBall (0 : ℂ) r,
      ‖fsans (beltramiMul (a + t • toLinf m) κ) z - fsans (beltramiMul a κ) z -
        (t * ((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * fsans (beltramiMul a κ) z ^ 2) + conj t * (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * fsans (beltramiMul a κ) z ^ 2))‖ ≤ ε * ‖t‖) ∧
    ∀ r₁ r₂ : ℝ, 1 < r₁ → ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ →
      ‖gsans (beltramiMul (a + t • toLinf m) κ) z - gsans (beltramiMul a κ) z -
        (t * ((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
          (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) +
          conj t * (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))))‖ ≤ ε * ‖t‖ := by
  obtain ⟨Q₁, Q₂, hf, hg⟩ := s3dv_expand hκ hκD ha has haL haD hm hmD
  obtain ⟨rfl, rfl⟩ := s3dv_pin hκ hκD ha has haL haD hm hmD Q₁ Q₂ hg
  refine ⟨fun z hz => ?_, fun z hz => ?_, hf, hg⟩
  · have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    obtain ⟨-, hd⟩ := s3d2u_hasFDeriv (F := fun t : ℂ => fsans (beltramiMul (a + t • toLinf m) κ) z)
      (fun ε hε => by
        obtain ⟨δ, hδ, hb⟩ := hf ‖z‖ hz1 ε hε
        exact ⟨δ, hδ, fun t ht => hb t ht z (by simp [mem_closedBall])⟩)
    obtain ⟨h1, h2⟩ := s3d2u_dz hd
    exact ⟨hd.differentiableAt, h1, h2⟩
  · have hz1 : 1 < ‖z‖ := hz
    obtain ⟨-, hd⟩ := s3d2u_hasFDeriv (F := fun t : ℂ => gsans (beltramiMul (a + t • toLinf m) κ) z)
      (fun ε hε => by
        obtain ⟨δ, hδ, hb⟩ := hg ‖z‖ ‖z‖ hz1 ε hε
        exact ⟨δ, hδ, fun t ht => hb t ht z le_rfl le_rfl⟩)
    obtain ⟨h1, h2⟩ := s3d2u_dz hd
    exact ⟨hd.differentiableAt, h1, h2⟩

end TakhtajanTeo.Ch2
