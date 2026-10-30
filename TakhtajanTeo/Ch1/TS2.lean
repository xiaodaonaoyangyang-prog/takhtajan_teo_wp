import TakhtajanTeo.Ch1.S1_2_Homogeneous
import TakhtajanTeo.Basic

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

section Ts2Aux
open scoped Nat

/-- Radial comparison: if `H` has derivative `G` on the disc, `H 0 = 0`, and `‖z‖ ‖G (t z)‖ ≤ K' t` along the
ray with `K' = derivative of K`, `K 0 ≥ 0`, then `‖H z‖ ≤ K 1`. -/
theorem ts2_radial_bound {H G : ℂ → ℂ} {z : ℂ} (hz : ‖z‖ < 1)
    (hH : ∀ w ∈ unitDisc, HasDerivAt H (G w) w) (hH0 : H 0 = 0)
    {K K' : ℝ → ℝ} (hK : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt K (K' t) t) (hK0 : 0 ≤ K 0)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖z‖ * ‖G ((t : ℂ) * z)‖ ≤ K' t) : ‖H z‖ ≤ K 1 := by
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ unitDisc := by
    intro t ht
    rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hz
  let f : ℝ → ℂ := fun t => H ((t : ℂ) * z)
  have hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (z * G ((t : ℂ) * z)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t := by
      simpa using (hasDerivAt_id t).ofReal_comp.mul_const z
    have h2 := (hH _ (hmem t ht)).scomp t h1
    simpa [f, Function.comp_def] using h2
  have hfc : ContinuousOn f (Icc 0 1) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hKc : ContinuousOn K (Icc 0 1) := fun t ht => (hK t ht).continuousAt.continuousWithinAt
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := f) (f' := fun t => z * G ((t : ℂ) * z))
    (B := K) (B' := K') hfc (fun t ht => (hf t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) (by
      show ‖H ((0 : ℝ) * z)‖ ≤ K 0
      simpa [hH0] using hK0) hKc (fun t ht => (hK t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (fun t ht => by rw [norm_mul]; exact hb t ⟨ht.1, ht.2.le⟩) (b := 1) (x := 1) ⟨zero_le_one, le_rfl⟩
  simpa [f] using this

theorem ts2_primitive {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G unitDisc) :
    ∃ H : ℂ → ℂ, H 0 = 0 ∧ ∀ w ∈ unitDisc, HasDerivAt H (G w) w := by
  have hG' : DifferentiableOn ℂ G (ball (0 : ℂ) 1) := hG
  obtain ⟨H, hH⟩ := hG'.isExactOn_ball
  obtain ⟨H', h0, h1⟩ := IsExactOn.with_val_at ⟨H, hH⟩ 0 0
  exact ⟨H', h0, h1⟩

theorem ts2_chain {phi : ℂ → ℂ} (hphi : DifferentiableOn ℂ phi unitDisc) :
    ∃ F0 F1 F2 : ℂ → ℂ, F0 0 = 0 ∧ F1 0 = 0 ∧ F2 0 = 0 ∧
      (∀ w ∈ unitDisc, HasDerivAt F2 (phi w) w) ∧ (∀ w ∈ unitDisc, HasDerivAt F1 (F2 w) w) ∧
      (∀ w ∈ unitDisc, HasDerivAt F0 (F1 w) w) := by
  obtain ⟨F2, h20, h2⟩ := ts2_primitive hphi
  have d2 : DifferentiableOn ℂ F2 unitDisc := fun w hw => (h2 w hw).differentiableAt.differentiableWithinAt
  obtain ⟨F1, h10, h1⟩ := ts2_primitive d2
  have d1 : DifferentiableOn ℂ F1 unitDisc := fun w hw => (h1 w hw).differentiableAt.differentiableWithinAt
  obtain ⟨F0, h00, h0⟩ := ts2_primitive d1
  exact ⟨F0, F1, F2, h00, h10, h20, h2, h1, h0⟩

theorem ts2_F2_bound {phi F2 : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hphi : ∀ z ∈ unitDisc, ‖phi z‖ ≤ M / (1 - ‖z‖) ^ 2)
    (h2 : ∀ w ∈ unitDisc, HasDerivAt F2 (phi w) w) (h20 : F2 0 = 0) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖F2 z‖ ≤ M / (1 - ‖z‖) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  set ρ := ‖z‖ with hρ
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 - t * ρ := by
    intro t ht
    have : t * ρ ≤ 1 * ρ := mul_le_mul_of_nonneg_right ht.2 hρ0
    linarith
  have hK : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => M / (1 - t * ρ)) (M * ρ / (1 - t * ρ) ^ 2) t := by
    intro t ht
    have hd : HasDerivAt (fun t : ℝ => 1 - t * ρ) (-ρ) t := by
      simpa using ((hasDerivAt_id t).mul_const ρ).const_sub 1
    have := (hasDerivAt_const t M).div hd (hpos t ht).ne'
    convert this using 1
    ring
  have key := ts2_radial_bound hz1 h2 h20 hK (by simpa using hM) (K' := fun t => M * ρ / (1 - t * ρ) ^ 2) (by
    intro t ht
    have hn : ‖(t : ℂ) * z‖ = t * ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hmem : (t : ℂ) * z ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, hn]
      linarith [hpos t ht]
    have := mul_le_mul_of_nonneg_left (hphi _ hmem) hρ0
    rw [hn] at this
    calc ρ * ‖phi ((t : ℂ) * z)‖ ≤ ρ * (M / (1 - t * ρ) ^ 2) := this
      _ = M * ρ / (1 - t * ρ) ^ 2 := by ring)
  simpa using key

theorem ts2_F1_bound {F1 F2 : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hF2 : ∀ z ∈ unitDisc, ‖F2 z‖ ≤ M / (1 - ‖z‖))
    (h1 : ∀ w ∈ unitDisc, HasDerivAt F1 (F2 w) w) (h10 : F1 0 = 0) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖F1 z‖ ≤ -M * Real.log (1 - ‖z‖) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  set ρ := ‖z‖ with hρ
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 - t * ρ := by
    intro t ht
    have : t * ρ ≤ 1 * ρ := mul_le_mul_of_nonneg_right ht.2 hρ0
    linarith
  have hK : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => -M * Real.log (1 - t * ρ)) (M * ρ / (1 - t * ρ)) t := by
    intro t ht
    have hd : HasDerivAt (fun t : ℝ => 1 - t * ρ) (-ρ) t := by
      simpa using ((hasDerivAt_id t).mul_const ρ).const_sub 1
    have := (hd.log (hpos t ht).ne').const_mul (-M)
    convert this using 1
    field_simp [(hpos t ht).ne']
  have key := ts2_radial_bound hz1 h1 h10 hK (by simp) (K' := fun t => M * ρ / (1 - t * ρ)) (by
    intro t ht
    have hn : ‖(t : ℂ) * z‖ = t * ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hmem : (t : ℂ) * z ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, hn]
      linarith [hpos t ht]
    have := mul_le_mul_of_nonneg_left (hF2 _ hmem) hρ0
    rw [hn] at this
    calc ρ * ‖F2 ((t : ℂ) * z)‖ ≤ ρ * (M / (1 - t * ρ)) := this
      _ = M * ρ / (1 - t * ρ) := by ring)
  simpa using key

/-- The auxiliary curve `g_ζ(s) = F₀(sζ) + (1-s) ζ F₁(sζ)` has derivative `(1-s) ζ² F₂(sζ)`. -/
theorem ts2_g_deriv {F0 F1 F2 : ℂ → ℂ} (hF0 : ∀ w ∈ unitDisc, HasDerivAt F0 (F1 w) w)
    (hF1 : ∀ w ∈ unitDisc, HasDerivAt F1 (F2 w) w) {ζ : ℂ} (hζ : ‖ζ‖ = 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasDerivAt (fun s : ℝ => F0 ((s : ℂ) * ζ) + ((1 - s : ℝ) : ℂ) * ζ * F1 ((s : ℂ) * ζ))
      (((1 - s : ℝ) : ℂ) * ζ * ζ * F2 ((s : ℂ) * ζ)) s := by
  have hmem : (s : ℂ) * ζ ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, hζ, mul_one]
    exact hs1
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * ζ) ζ s := by
    simpa using (hasDerivAt_id s).ofReal_comp.mul_const ζ
  have hA := (hF0 _ hmem).scomp s h1
  have hB := (hF1 _ hmem).scomp s h1
  have hc : HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ) * ζ) (-ζ) s := by
    have : HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ)) (-1) s := by
      simpa using ((hasDerivAt_id s).const_sub 1).ofReal_comp
    simpa using this.mul_const ζ
  have hC := hc.mul hB
  have hsum := hA.add hC
  convert hsum using 1
  · funext x
    simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
  · simp only [Function.comp_apply, smul_eq_mul]
    ring

theorem ts2_g_lipschitz {F0 F1 F2 phi : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hF0 : ∀ w ∈ unitDisc, HasDerivAt F0 (F1 w) w) (hF1 : ∀ w ∈ unitDisc, HasDerivAt F1 (F2 w) w)
    (hF2 : ∀ z ∈ unitDisc, ‖F2 z‖ ≤ M / (1 - ‖z‖)) {ζ : ℂ} (hζ : ‖ζ‖ = 1) {s s' : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (hs' : s' ∈ Ico (0 : ℝ) 1) :
    ‖(F0 ((s' : ℂ) * ζ) + ((1 - s' : ℝ) : ℂ) * ζ * F1 ((s' : ℂ) * ζ)) -
      (F0 ((s : ℂ) * ζ) + ((1 - s : ℝ) : ℂ) * ζ * F1 ((s : ℂ) * ζ))‖ ≤ M * |s' - s| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => F0 ((s : ℂ) * ζ) + ((1 - s : ℝ) : ℂ) * ζ * F1 ((s : ℂ) * ζ))
    (f' := fun s : ℝ => ((1 - s : ℝ) : ℂ) * ζ * ζ * F2 ((s : ℂ) * ζ)) (C := M) (s := Ico (0 : ℝ) 1)
    (fun x hx => (ts2_g_deriv hF0 hF1 hζ hx.1 hx.2).hasDerivWithinAt) (fun x hx => by
      have hn : ‖(x : ℂ) * ζ‖ = x := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1, hζ, mul_one]
      have hmem : (x : ℂ) * ζ ∈ unitDisc := by
        rw [unitDisc, mem_ball_zero_iff, hn]
        exact hx.2
      have h2 := hF2 _ hmem
      rw [hn] at h2
      have h1x : (0 : ℝ) < 1 - x := by linarith [hx.2]
      calc ‖((1 - x : ℝ) : ℂ) * ζ * ζ * F2 ((x : ℂ) * ζ)‖ = (1 - x) * ‖F2 ((x : ℂ) * ζ)‖ := by
            rw [norm_mul, norm_mul, norm_mul, hζ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1x]
            ring
        _ ≤ (1 - x) * (M / (1 - x)) := mul_le_mul_of_nonneg_left h2 h1x.le
        _ = M := by field_simp)
    (convex_Ico 0 1) hs hs'
  simpa [Real.norm_eq_abs] using h

/-- The boundary trace `B` of `F₀` as the limit of the Lipschitz curves `g_ζ`. -/
theorem ts2_trace_exists {F0 F1 F2 : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hF0 : ∀ w ∈ unitDisc, HasDerivAt F0 (F1 w) w) (hF1 : ∀ w ∈ unitDisc, HasDerivAt F1 (F2 w) w)
    (hF2 : ∀ z ∈ unitDisc, ‖F2 z‖ ≤ M / (1 - ‖z‖)) :
    ∃ B : ℂ → ℂ, ContinuousOn B (sphere (0 : ℂ) 1) ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ s : ℝ, 0 ≤ s → s < 1 →
      ‖B ζ - (F0 ((s : ℂ) * ζ) + ((1 - s : ℝ) : ℂ) * ζ * F1 ((s : ℂ) * ζ))‖ ≤ M * (1 - s) := by
  let g : ℂ → ℝ → ℂ := fun ζ s => F0 ((s : ℂ) * ζ) + ((1 - s : ℝ) : ℂ) * ζ * F1 ((s : ℂ) * ζ)
  have hlip : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ s s' : ℝ, s ∈ Ico (0 : ℝ) 1 → s' ∈ Ico (0 : ℝ) 1 →
      ‖g ζ s' - g ζ s‖ ≤ M * |s' - s| := fun ζ hζ s s' hs hs' =>
    ts2_g_lipschitz (phi := F2) hM hF0 hF1 hF2 hζ hs hs'
  let u : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  have hu0 : ∀ n, u n ∈ Ico (0 : ℝ) 1 := by
    intro n
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
    have h3 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨by simp only [u]; linarith, by simp only [u]; linarith⟩
  have hut : Tendsto u atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
    simpa [u] using this
  have key : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ L : ℂ, ∀ s : ℝ, 0 ≤ s → s < 1 → ‖L - g ζ s‖ ≤ M * (1 - s) := by
    intro ζ hζ
    have hL : LipschitzOnWith M.toNNReal (g ζ) (Ico (0 : ℝ) 1) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ hM]
      exact hlip ζ hζ y x hy hx
    have hc : CauchySeq (g ζ ∘ u) := hL.cauchySeq_comp hut.cauchySeq (by rintro _ ⟨n, rfl⟩; exact hu0 n)
    obtain ⟨L, hL'⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨L, fun s hs0 hs1 => ?_⟩
    have h1 : Tendsto (fun n => ‖(g ζ ∘ u) n - g ζ s‖) atTop (𝓝 ‖L - g ζ s‖) :=
      (hL'.sub_const _).norm
    have h2 : Tendsto (fun n => M * |u n - s|) atTop (𝓝 (M * |1 - s|)) :=
      ((hut.sub_const s).abs).const_mul M
    have h3 : ‖L - g ζ s‖ ≤ M * |1 - s| := by
      refine le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun n => ?_)
      simpa using hlip ζ hζ s (u n) ⟨hs0, hs1⟩ (hu0 n)
    rwa [abs_of_pos (by linarith : (0 : ℝ) < 1 - s)] at h3
  choose! B hB using key
  refine ⟨B, ?_, fun ζ hζ s hs0 hs1 => hB ζ hζ s hs0 hs1⟩
  -- continuity: uniform limit of continuous `g · s`
  refine continuousOn_of_uniform_approx_of_continuousOn (fun V hV => ?_)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.1 hV
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M * (1 - u n) < ε := by
    have : Tendsto (fun n => M * (1 - u n)) atTop (𝓝 (M * (1 - 1))) :=
      ((tendsto_const_nhds.sub hut).const_mul M)
    rw [sub_self, mul_zero] at this
    exact (this.eventually (gt_mem_nhds hε)).exists
  refine ⟨fun ζ => g ζ (u n), ?_, fun ζ hζ => hεV ?_⟩
  · have hmem : ((u n : ℝ) : ℂ) ≠ 0 ∨ True := Or.inr trivial
    have hun : u n < 1 := (hu0 n).2
    have hun0 : 0 ≤ u n := (hu0 n).1
    have hdisc : ∀ ζ ∈ sphere (0 : ℂ) 1, ((u n : ℝ) : ℂ) * ζ ∈ unitDisc := by
      intro ζ hζ
      rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hun0,
        mem_sphere_zero_iff_norm.1 hζ, mul_one]
      exact hun
    have hcont : ∀ H : ℂ → ℂ, (∀ w ∈ unitDisc, HasDerivAt H (0 : ℂ) w ∨ True) → True := fun _ _ => trivial
    have hF0c : ContinuousOn F0 unitDisc := fun w hw => (hF0 w hw).continuousAt.continuousWithinAt
    have hF1c : ContinuousOn F1 unitDisc := fun w hw => (hF1 w hw).continuousAt.continuousWithinAt
    have hlin : Continuous (fun ζ : ℂ => ((u n : ℝ) : ℂ) * ζ) := continuous_const.mul continuous_id
    refine ContinuousOn.add (hF0c.comp hlin.continuousOn hdisc) ?_
    exact (continuousOn_const.mul continuousOn_id).mul (hF1c.comp hlin.continuousOn hdisc)
  · have := hB ζ (mem_sphere_zero_iff_norm.1 hζ) (u n) (hu0 n).1 (hu0 n).2
    rw [dist_eq_norm]
    exact lt_of_le_of_lt this hn

theorem ts2_F0_bound {F0 F1 : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hF1 : ∀ z ∈ unitDisc, ‖F1 z‖ ≤ -M * Real.log (1 - ‖z‖))
    (h0 : ∀ w ∈ unitDisc, HasDerivAt F0 (F1 w) w) (h00 : F0 0 = 0) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖F0 z‖ ≤ M := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  set ρ := ‖z‖ with hρ
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 - t * ρ := by
    intro t ht
    have : t * ρ ≤ 1 * ρ := mul_le_mul_of_nonneg_right ht.2 hρ0
    linarith
  have hK : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => M * (1 + (1 - t * ρ) * (Real.log (1 - t * ρ) - 1)))
        (-M * ρ * Real.log (1 - t * ρ)) t := by
    intro t ht
    have hd : HasDerivAt (fun t : ℝ => 1 - t * ρ) (-ρ) t := by
      simpa using ((hasDerivAt_id t).mul_const ρ).const_sub 1
    have hl := hd.log (hpos t ht).ne'
    have := (hd.mul (hl.sub_const 1)).const_add 1 |>.const_mul M
    convert this using 1
    have hne1 := (hpos t ht).ne'
    have hne2 : 1 - ρ * t ≠ 0 := by rw [mul_comm]; exact hne1
    field_simp
    ring
  have key := ts2_radial_bound hz1 h0 h00 hK (K' := fun t => -M * ρ * Real.log (1 - t * ρ)) (by simp) (by
    intro t ht
    have hn : ‖(t : ℂ) * z‖ = t * ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hmem : (t : ℂ) * z ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, hn]
      linarith [hpos t ht]
    have := mul_le_mul_of_nonneg_left (hF1 _ hmem) hρ0
    rw [hn] at this
    calc ρ * ‖F1 ((t : ℂ) * z)‖ ≤ ρ * (-M * Real.log (1 - t * ρ)) := this
      _ = -M * ρ * Real.log (1 - t * ρ) := by ring)
  refine le_trans key ?_
  have hlog : Real.log (1 - 1 * ρ) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h1 : 0 < 1 - 1 * ρ := by linarith
  have : (1 - 1 * ρ) * (Real.log (1 - 1 * ρ) - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h1.le (by linarith)
  nlinarith

/-- Direction (b), analytic core: from `phi` with `‖phi z‖ ≤ M/(1-|z|)²` build the triple primitive `F₀` and its continuous
Zygmund boundary trace `b`. -/
theorem ts2_trace_final {phi : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hphid : DifferentiableOn ℂ phi unitDisc)
    (hphi : ∀ z ∈ unitDisc, ‖phi z‖ ≤ M / (1 - ‖z‖) ^ 2) :
    ∃ F0 F1 F2 : ℂ → ℂ, F0 0 = 0 ∧ F1 0 = 0 ∧ F2 0 = 0 ∧
      (∀ w ∈ unitDisc, HasDerivAt F2 (phi w) w) ∧ (∀ w ∈ unitDisc, HasDerivAt F1 (F2 w) w) ∧
      (∀ w ∈ unitDisc, HasDerivAt F0 (F1 w) w) ∧
      ∃ b : ℝ → ℂ, Continuous b ∧ (∀ x, b (x + 2 * π) = b x) ∧ (∀ x, ‖b x‖ ≤ 2 * M) ∧
        (∀ x t, ‖b (x + t) + b (x - t) - 2 * b x‖ ≤ 24 * M * |t|) ∧
        ∀ x r : ℝ, 0 ≤ r → r < 1 →
          ‖b x - F0 ((r : ℂ) * exp (x * I))‖ ≤ M * (1 - r) + (1 - r) * (-M * Real.log (1 - r)) := by
  obtain ⟨F0, F1, F2, h00, h10, h20, h2, h1, h0⟩ := ts2_chain hphid
  have hF2b : ∀ z ∈ unitDisc, ‖F2 z‖ ≤ M / (1 - ‖z‖) := fun z hz => ts2_F2_bound hM hphi h2 h20 hz
  have hF1b : ∀ z ∈ unitDisc, ‖F1 z‖ ≤ -M * Real.log (1 - ‖z‖) := fun z hz => ts2_F1_bound hM hF2b h1 h10 hz
  have hF0b : ∀ z ∈ unitDisc, ‖F0 z‖ ≤ M := fun z hz => ts2_F0_bound hM hF1b h0 h00 hz
  obtain ⟨B, hBc, hB⟩ := ts2_trace_exists hM h0 h1 hF2b
  -- uniform bound for the trace
  have hB0 : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖B ζ‖ ≤ 2 * M := by
    intro ζ hζ
    have hmem : (((1 / 2 : ℝ) : ℂ) * ζ) ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, hζ]
      norm_num
    have hn : ‖(((1 / 2 : ℝ) : ℂ) * ζ)‖ = 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hζ]; norm_num
    have hh := hB ζ hζ (1 / 2) (by norm_num) (by norm_num)
    have e0 := hF0b _ hmem
    have e1 := hF1b _ hmem
    rw [hn] at e1
    have hl : Real.log (1 - 1 / 2) = -Real.log 2 := by
      rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    rw [hl] at e1
    have e1' : ‖F1 (((1 / 2 : ℝ) : ℂ) * ζ)‖ ≤ M := by
      nlinarith [mul_le_mul_of_nonneg_left hl2 hM]
    have hg : ‖F0 (((1 / 2 : ℝ) : ℂ) * ζ) + ((1 - 1 / 2 : ℝ) : ℂ) * ζ * F1 (((1 / 2 : ℝ) : ℂ) * ζ)‖ ≤
        3 / 2 * M := by
      refine (norm_add_le _ _).trans ?_
      have : ‖((1 - 1 / 2 : ℝ) : ℂ) * ζ * F1 (((1 / 2 : ℝ) : ℂ) * ζ)‖ ≤ M / 2 := by
        rw [norm_mul, norm_mul, hζ, Complex.norm_real, Real.norm_eq_abs,
          show |(1 - 1 / 2 : ℝ)| = 1 / 2 by norm_num]
        linarith
      linarith
    have := norm_le_insert' (B ζ) (F0 (((1 / 2 : ℝ) : ℂ) * ζ) +
      ((1 - 1 / 2 : ℝ) : ℂ) * ζ * F1 (((1 / 2 : ℝ) : ℂ) * ζ))
    norm_num at hh this hg ⊢
    linarith
  -- approximation of the trace by the interior values
  have hBT : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ r : ℝ, 0 ≤ r → r < 1 →
      ‖B ζ - F0 ((r : ℂ) * ζ) - ((1 - r : ℝ) : ℂ) * ζ * F1 ((r : ℂ) * ζ)‖ ≤ M * (1 - r) := by
    intro ζ hζ r hr0 hr1
    have := hB ζ hζ r hr0 hr1
    rwa [← sub_sub] at this
  have hcirc : ∀ x : ℝ, ‖exp ((x : ℂ) * I)‖ = 1 := fun x => by simp [norm_exp]
  have hcont : Continuous (fun x : ℝ => B (exp ((x : ℂ) * I))) := by
    have hc : Continuous (fun x : ℝ => exp ((x : ℂ) * I)) := by fun_prop
    exact hBc.comp_continuous hc (fun x => mem_sphere_zero_iff_norm.2 (hcirc x))
  refine ⟨F0, F1, F2, h00, h10, h20, h2, h1, h0, fun x => B (exp (x * I)), hcont, ?_, ?_, ?_, ?_⟩
  · intro x
    have : exp (((x + 2 * π : ℝ) : ℂ) * I) = exp ((x : ℂ) * I) := by
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    simp only [this]
  · intro x
    exact hB0 _ (hcirc x)
  · -- Zygmund bound from the in-tree boundary second-difference theorem
    have hdisc : DifferentiableOn ℂ F0 unitDisc := fun w hw => (h0 w hw).differentiableAt.differentiableWithinAt
    have hd1 : ∀ z ∈ unitDisc, deriv F0 z = F1 z := fun z hz => (h0 z hz).deriv
    have hd2 : ∀ z ∈ unitDisc, deriv (deriv F0) z = F2 z := by
      intro z hz
      have ev : deriv F0 =ᶠ[𝓝 z] F1 :=
        Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (show z ∈ ball (0 : ℂ) 1 from hz))
          (fun w hw => hd1 w hw)
      rw [ev.deriv_eq]
      exact (h1 z hz).deriv
    have hC : (0 : ℝ) ≤ 2 * M := by linarith
    let Bc : C(Circle, ℂ) := ⟨fun ζ => B (ζ : ℂ), hBc.comp_continuous continuous_subtype_val
      (fun ζ => mem_sphere_zero_iff_norm.2 (by simp))⟩
    have hz := disk_boundary_second_difference_bound (F := F0) (C := 2 * M) hC hdisc
      (fun z hz => by
        rw [hd1 z hz]
        have := hF1b z hz
        have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
        have hlog : Real.log (1 - ‖z‖) ≤ 0 :=
          Real.log_nonpos (by linarith [norm_nonneg z]) (by linarith [norm_nonneg z])
        nlinarith)
      (fun z hz => by
        rw [hd2 z hz]
        have := hF2b z hz
        have hp : 0 < 1 - ‖z‖ := by
          have : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
          linarith
        calc ‖F2 z‖ ≤ M / (1 - ‖z‖) := this
          _ ≤ 2 * M / (1 - ‖z‖) := by gcongr; linarith)
      Bc (fun ζ => hB0 _ (by simp)) (fun ζ r hr0 hr1 => by
        have h := hBT (ζ : ℂ) (by simp) r hr0 hr1
        have hd := hd1 ((r : ℂ) * ζ) (by
          rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
          simpa using hr1)
        show ‖B (ζ : ℂ) - F0 ((r : ℂ) * ζ) - ((1 - r : ℝ) : ℂ) * ζ * deriv F0 ((r : ℂ) * ζ)‖ ≤ 2 * M * (1 - r)
        rw [hd]
        nlinarith [mul_nonneg hM (sub_nonneg.2 hr1.le)])
    intro x t
    have := hz x t
    have e : ∀ y : ℝ, Bc (Circle.exp y) = B (exp ((y : ℂ) * I)) := fun y => by
      simp [Bc, Circle.coe_exp]
    simp only [e] at this
    show ‖B (exp (((x + t : ℝ) : ℂ) * I)) + B (exp (((x - t : ℝ) : ℂ) * I)) -
      2 * B (exp ((x : ℂ) * I))‖ ≤ 24 * M * |t|
    calc _ ≤ 12 * (2 * M) * |t| := this
      _ = 24 * M * |t| := by ring
  · intro x r hr0 hr1
    have hζ := hcirc x
    have h := hB (exp ((x : ℂ) * I)) hζ r hr0 hr1
    have hmem : ((r : ℂ) * exp ((x : ℂ) * I)) ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hζ, mul_one]
      exact hr1
    have hn : ‖(r : ℂ) * exp ((x : ℂ) * I)‖ = r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hζ, mul_one]
    have e1 := hF1b _ hmem
    rw [hn] at e1
    have hx : B (exp ((x : ℂ) * I)) - F0 ((r : ℂ) * exp ((x : ℂ) * I)) =
        (B (exp ((x : ℂ) * I)) - (F0 ((r : ℂ) * exp ((x : ℂ) * I)) +
          ((1 - r : ℝ) : ℂ) * exp ((x : ℂ) * I) * F1 ((r : ℂ) * exp ((x : ℂ) * I)))) +
        ((1 - r : ℝ) : ℂ) * exp ((x : ℂ) * I) * F1 ((r : ℂ) * exp ((x : ℂ) * I)) := by ring
    show ‖B (exp ((x : ℂ) * I)) - F0 ((r : ℂ) * exp ((x : ℂ) * I))‖ ≤ _
    rw [hx]
    refine (norm_add_le _ _).trans ?_
    have h1r : (0 : ℝ) < 1 - r := by linarith
    have : ‖((1 - r : ℝ) : ℂ) * exp ((x : ℂ) * I) * F1 ((r : ℂ) * exp ((x : ℂ) * I))‖ ≤
        (1 - r) * (-M * Real.log (1 - r)) := by
      rw [norm_mul, norm_mul, hζ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1r, mul_one]
      exact mul_le_mul_of_nonneg_left e1 h1r.le
    linarith

theorem ts2_orth (m : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, exp ((m : ℂ) * θ * I) = if m = 0 then 2 * π else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp
  · rw [if_neg hm]
    have hc : (m : ℂ) * I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hm) I_ne_zero
    have h := integral_exp_mul_complex (a := 0) (b := 2 * π) hc
    have e : (fun θ : ℝ => exp ((m : ℂ) * θ * I)) = fun θ : ℝ => exp (((m : ℂ) * I) * θ) :=
      funext fun θ => by ring_nf
    rw [e, h]
    have : ((m : ℂ) * I) * ((2 * π : ℝ) : ℂ) = (m : ℂ) * (2 * π * I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp

theorem ts2_taylor_hasSum {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    HasSum (fun n : ℕ => ((n ! : ℂ)⁻¹ * iteratedDeriv n F 0) * z ^ n) (F z) := by
  have h := Complex.hasSum_taylorSeries_on_ball (show DifferentiableOn ℂ F (ball (0 : ℂ) 1) from hF)
    (show z ∈ ball (0 : ℂ) 1 from hz)
  have e : (fun n : ℕ => ((n ! : ℂ)⁻¹ * iteratedDeriv n F 0) * z ^ n) =
      fun n : ℕ => (n ! : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n F 0 :=
    funext fun n => by simp only [smul_eq_mul, sub_zero]; ring
  rw [e]
  exact h

theorem ts2_circle_coeff_series {F : ℂ → ℂ} {a : ℕ → ℂ}
    (hser : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => a n * z ^ n) (F z)) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (k : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, F ((r : ℂ) * exp (θ * I)) * exp (-((k : ℂ) * θ * I)) =
      2 * π * (if 0 ≤ k then a k.toNat * (r : ℂ) ^ k.toNat else 0) := by
  set r' : ℝ := (r + 1) / 2 with hr'
  have hr'0 : 0 < r' := by rw [hr']; linarith
  have hr'1 : r' < 1 := by rw [hr']; linarith
  have hrr' : r < r' := by rw [hr']; linarith
  have hr'mem : ((r' : ℝ) : ℂ) ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr'0]
    exact hr'1
  have hs := (hser _ hr'mem).summable
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ n, ‖a n‖ * r' ^ n ≤ C := by
    have h0 := hs.tendsto_atTop_zero
    obtain ⟨C, hC⟩ := h0.norm.bddAbove_range
    refine ⟨C, fun n => ?_⟩
    have := hC ⟨n, rfl⟩
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr'0] using this
  have hgeo : Summable fun n : ℕ => C * (r / r') ^ n :=
    (summable_geometric_of_lt_one (div_nonneg hr0 hr'0.le) ((div_lt_one hr'0).2 hrr')).mul_left C
  have hterm : ∀ n : ℕ, ‖a n‖ * r ^ n ≤ C * (r / r') ^ n := by
    intro n
    have h1 := hC n
    have hrn : r ^ n = (r / r') ^ n * r' ^ n := by rw [← mul_pow, div_mul_cancel₀ _ hr'0.ne']
    rw [hrn]
    calc ‖a n‖ * ((r / r') ^ n * r' ^ n) = (‖a n‖ * r' ^ n) * (r / r') ^ n := by ring
      _ ≤ C * (r / r') ^ n := mul_le_mul_of_nonneg_right h1 (pow_nonneg (div_nonneg hr0 hr'0.le) n)
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := 0) (b := 2 * π) (μ := volume)
    (F := fun (n : ℕ) (θ : ℝ) => a n * (r : ℂ) ^ n * exp ((((n : ℤ) - k : ℤ) : ℂ) * θ * I))
    (f := fun θ : ℝ => F ((r : ℂ) * exp (θ * I)) * exp (-((k : ℂ) * θ * I)))
    (fun n _ => C * (r / r') ^ n) (fun n => by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop) (fun n => Filter.Eventually.of_forall fun θ _ => by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      have : ‖exp ((((n : ℤ) - k : ℤ) : ℂ) * θ * I)‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [this, mul_one]
      exact hterm n) (Filter.Eventually.of_forall fun θ _ => hgeo)
    (by exact intervalIntegrable_const) (Filter.Eventually.of_forall fun θ _ => by
      have hz : (r : ℂ) * exp (θ * I) ∈ unitDisc := by
        rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
        simpa [norm_exp] using hr1
      have := (hser _ hz).mul_right (exp (-((k : ℂ) * θ * I)))
      convert this using 1
      funext n
      have h1 : ((r : ℂ) * exp (θ * I)) ^ n = (r : ℂ) ^ n * exp (n * θ * I) := by
        rw [mul_pow, ← Complex.exp_nat_mul]; congr 2; ring
      rw [h1]
      have h2 : exp ((((n : ℤ) - k : ℤ) : ℂ) * θ * I) = exp ((n : ℂ) * θ * I) * exp (-((k : ℂ) * θ * I)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [h2]
      ring)
  have hint : ∀ n : ℕ, ∫ θ in (0 : ℝ)..2 * π, a n * (r : ℂ) ^ n * exp ((((n : ℤ) - k : ℤ) : ℂ) * θ * I) =
      a n * (r : ℂ) ^ n * (if (n : ℤ) - k = 0 then 2 * π else 0) := by
    intro n
    rw [intervalIntegral.integral_const_mul, ts2_orth]
  simp only [hint] at hsum
  by_cases hk : 0 ≤ k
  · rw [if_pos hk]
    have h1 : HasSum (fun n : ℕ => a n * (r : ℂ) ^ n * (if (n : ℤ) - k = 0 then 2 * π else 0))
        (a k.toNat * (r : ℂ) ^ k.toNat * 2 * π) := by
      have : (fun n : ℕ => a n * (r : ℂ) ^ n * (if (n : ℤ) - k = 0 then 2 * π else 0)) =
          fun n : ℕ => if n = k.toNat then a k.toNat * (r : ℂ) ^ k.toNat * (2 * π) else 0 := by
        funext n
        by_cases hn : n = k.toNat
        · subst hn
          simp [Int.toNat_of_nonneg hk]
        · have : (n : ℤ) - k ≠ 0 := by
            intro h0
            apply hn
            omega
          simp [hn, this]
      rw [this, show a k.toNat * (r : ℂ) ^ k.toNat * 2 * π = a k.toNat * (r : ℂ) ^ k.toNat * (2 * π) by ring]
      exact hasSum_ite_eq _ _
    rw [← h1.unique hsum]
    ring
  · rw [if_neg hk]
    have h1 : HasSum (fun n : ℕ => a n * (r : ℂ) ^ n * (if (n : ℤ) - k = 0 then 2 * π else 0)) 0 := by
      have : (fun n : ℕ => a n * (r : ℂ) ^ n * (if (n : ℤ) - k = 0 then 2 * π else 0)) = fun _ => 0 := by
        funext n
        have : (n : ℤ) - k ≠ 0 := by omega
        simp [this]
      rw [this]
      exact hasSum_zero
    rw [← h1.unique hsum]
    simp

theorem ts2_circle_coeff {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (k : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, F ((r : ℂ) * exp (θ * I)) * exp (-((k : ℂ) * θ * I)) =
      2 * π * (if 0 ≤ k then ((k.toNat ! : ℂ)⁻¹ * iteratedDeriv k.toNat F 0) * (r : ℂ) ^ k.toNat else 0) :=
  ts2_circle_coeff_series (a := fun n => (n ! : ℂ)⁻¹ * iteratedDeriv n F 0)
    (fun z hz => ts2_taylor_hasSum hF hz) hr0 hr1 k

/-- Uniqueness of power series coefficients (via the circle integrals). -/
theorem ts2_series_coeff_unique {F : ℂ → ℂ} {a a' : ℕ → ℂ}
    (h : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => a n * z ^ n) (F z))
    (h' : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => a' n * z ^ n) (F z)) (n : ℕ) : a n = a' n := by
  have e1 := ts2_circle_coeff_series h (r := 1 / 2) (by norm_num) (by norm_num) (n : ℤ)
  have e2 := ts2_circle_coeff_series h' (r := 1 / 2) (by norm_num) (by norm_num) (n : ℤ)
  rw [e1] at e2
  simp only [Int.natCast_nonneg, if_true, Int.toNat_natCast] at e2
  have hpi : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hp : ((1 / 2 : ℝ) : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have := mul_left_cancel₀ hpi e2
  exact mul_right_cancel₀ hp this

/-- The Fourier coefficients of the boundary trace `b` are the Taylor coefficients of `F₀` (zero for negative index). -/
theorem ts2_fourier_b {F0 : ℂ → ℂ} {b : ℝ → ℂ} {M : ℝ} (hF : DifferentiableOn ℂ F0 unitDisc)
    (hbc : Continuous b)
    (happ : ∀ x r : ℝ, 0 ≤ r → r < 1 →
      ‖b x - F0 ((r : ℂ) * exp (x * I))‖ ≤ M * (1 - r) + (1 - r) * (-M * Real.log (1 - r))) (k : ℤ) :
    fourierCoeff b k = if 0 ≤ k then (k.toNat ! : ℂ)⁻¹ * iteratedDeriv k.toNat F0 0 else 0 := by
  set A : ℂ := if 0 ≤ k then (k.toNat ! : ℂ)⁻¹ * iteratedDeriv k.toNat F0 0 else 0 with hA
  set Ak : ℝ → ℂ := fun r => if 0 ≤ k then ((k.toNat ! : ℂ)⁻¹ * iteratedDeriv k.toNat F0 0) * (r : ℂ) ^ k.toNat
    else 0 with hAk
  set ε : ℝ → ℝ := fun r => M * (1 - r) + (1 - r) * (-M * Real.log (1 - r)) with hε
  have hpt : ∀ r : ℝ, 0 ≤ r → r < 1 → ‖fourierCoeff b k - Ak r‖ ≤ ε r := by
    intro r hr0 hr1
    have hc := ts2_circle_coeff hF hr0 hr1 k
    have hcont1 : Continuous fun θ : ℝ => b θ * exp (-((k : ℂ) * θ * I)) := by
      have := hbc; fun_prop
    have hcont2 : Continuous fun θ : ℝ => F0 ((r : ℂ) * exp (θ * I)) * exp (-((k : ℂ) * θ * I)) := by
      have hF0c : ContinuousOn F0 unitDisc := hF.continuousOn
      have hlin : Continuous fun θ : ℝ => (r : ℂ) * exp (θ * I) := by fun_prop
      have hmem : ∀ θ : ℝ, (r : ℂ) * exp (θ * I) ∈ unitDisc := fun θ => by
        rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
        simpa [norm_exp] using hr1
      have := hF0c.comp_continuous hlin hmem
      exact this.mul (by fun_prop)
    have hdiff : fourierCoeff b k - Ak r =
        (1 / (2 * π)) * ∫ θ in (0 : ℝ)..2 * π,
          (b θ - F0 ((r : ℂ) * exp (θ * I))) * exp (-((k : ℂ) * θ * I)) := by
      have hAkr : Ak r = (1 / (2 * π)) * (2 * π * Ak r) := by
        have : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
        field_simp
      have hc' : (∫ θ in (0 : ℝ)..2 * π, F0 ((r : ℂ) * exp (θ * I)) * exp (-((k : ℂ) * θ * I))) =
          2 * π * Ak r := by
        rw [hc]
      rw [hAkr, fourierCoeff, ← mul_sub, ← hc', ← intervalIntegral.integral_sub
        (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _)]
      congr 1
      refine intervalIntegral.integral_congr fun θ _ => ?_
      ring
    rw [hdiff, norm_mul]
    have hb : ‖∫ θ in (0 : ℝ)..2 * π, (b θ - F0 ((r : ℂ) * exp (θ * I))) * exp (-((k : ℂ) * θ * I))‖ ≤
        ε r * |2 * π - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
      rw [norm_mul]
      have : ‖exp (-((k : ℂ) * θ * I))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, mul_one]
      exact happ θ r hr0 hr1
    have hpi : (0 : ℝ) < 2 * π := by positivity
    rw [sub_zero, abs_of_pos hpi] at hb
    have h12 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, Complex.norm_mul]
      simp [abs_of_pos Real.pi_pos]
    rw [h12]
    calc 1 / (2 * π) * ‖∫ θ in (0 : ℝ)..2 * π, (b θ - F0 ((r : ℂ) * exp (θ * I))) *
          exp (-((k : ℂ) * θ * I))‖ ≤ 1 / (2 * π) * (ε r * (2 * π)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ε r := by field_simp
  -- pass to the limit r → 1
  have hlim1 : Tendsto (fun r : ℝ => fourierCoeff b k - Ak r) (𝓝[<] 1) (𝓝 (fourierCoeff b k - A)) := by
    refine (tendsto_const_nhds.sub ?_).mono_left nhdsWithin_le_nhds
    have hcont : Continuous Ak := by
      simp only [hAk]
      split_ifs
      · fun_prop
      · exact continuous_const
    have := hcont.tendsto 1
    simpa [hAk, hA] using this
  have hlim2 : Tendsto ε (𝓝[<] 1) (𝓝 0) := by
    have hcm : Continuous fun x : ℝ => x * Real.log x := Real.continuous_mul_log
    have hc : Continuous ε := by
      have e : ε = fun r => (fun x : ℝ => M * x - M * (x * Real.log x)) (1 - r) := by
        funext r
        simp only [hε]
        ring
      rw [e]
      exact ((continuous_const.mul continuous_id).sub (continuous_const.mul hcm)).comp
        (continuous_const.sub continuous_id)
    have h0 : ε 1 = 0 := by simp [hε]
    have := hc.tendsto 1
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hle : ‖fourierCoeff b k - A‖ ≤ 0 := by
    refine le_of_tendsto_of_tendsto hlim1.norm hlim2 ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact hpt r hr.1.le hr.2
  have := norm_nonneg (fourierCoeff b k - A)
  have h0 : fourierCoeff b k - A = 0 := norm_eq_zero.1 (le_antisymm hle this)
  exact sub_eq_zero.1 h0

theorem ts2_exp_real (t : ℝ) : exp ((t : ℂ) * I) = (Real.cos t : ℂ) + (Real.sin t : ℂ) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem ts2_one_sub_cos_le (t : ℝ) : 1 - Real.cos t ≤ |t| := by
  by_cases h : |t| ≤ 2
  · have h1 := Real.one_sub_sq_div_two_le_cos (x := t)
    have h2 : t ^ 2 / 2 ≤ |t| := by
      have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      rw [this]
      nlinarith [abs_nonneg t]
    linarith
  · push_neg at h
    linarith [Real.neg_one_le_cos t]

theorem ts2_second_diff_q {b : ℝ → ℂ} {K0 K1 : ℝ} (hK0 : 0 ≤ K0) (hb : ∀ x, ‖b x‖ ≤ K0)
    (hz : ∀ x t, ‖b (x + t) + b (x - t) - 2 * b x‖ ≤ K1 * |t|) (x t : ℝ) :
    ‖-I * b (x + t) * exp (-(((x + t : ℝ) : ℂ) * I)) + (-I * b (x - t) * exp (-(((x - t : ℝ) : ℂ) * I)))
        - 2 * (-I * b x * exp (-((x : ℂ) * I)))‖ ≤ (K1 + 4 * K0) * |t| := by
  set e : ℂ := exp (-((x : ℂ) * I)) with he
  set E1 : ℂ := (Real.cos t : ℂ) - (Real.sin t : ℂ) * I with hE1
  set E2 : ℂ := (Real.cos t : ℂ) + (Real.sin t : ℂ) * I with hE2
  have hEm : exp (-((t : ℂ) * I)) = E1 := by
    have h := ts2_exp_real (-t)
    rw [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Complex.ofReal_neg] at h
    rw [show -(t : ℂ) * I = -((t : ℂ) * I) by ring] at h
    rw [h, hE1]
    ring
  have hx1 : exp (-(((x + t : ℝ) : ℂ) * I)) = e * E1 := by
    rw [← hEm, he, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hx2 : exp (-(((x - t : ℝ) : ℂ) * I)) = e * E2 := by
    rw [hE2, ← ts2_exp_real t, he, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hne : ‖e‖ = 1 := by
    rw [he, Complex.norm_exp]
    simp
  have hkey : (-I * b (x + t) * exp (-(((x + t : ℝ) : ℂ) * I)) + (-I * b (x - t) * exp (-(((x - t : ℝ) : ℂ) * I)))
        - 2 * (-I * b x * exp (-((x : ℂ) * I)))) =
      (-I * e) * ((Real.cos t : ℂ) * (b (x + t) + b (x - t) - 2 * b x) +
        (2 * ((Real.cos t : ℂ) - 1)) * b x - ((Real.sin t : ℂ) * I) * (b (x + t) - b (x - t))) := by
    rw [hx1, hx2, hE1, hE2]
    ring
  rw [hkey, norm_mul]
  have h1 : ‖-I * e‖ = 1 := by rw [norm_mul, norm_neg, Complex.norm_I, hne, one_mul]
  rw [h1, one_mul]
  have hz0 := hz x t
  have hKt : 0 ≤ K1 * |t| := le_trans (norm_nonneg _) hz0
  have hc : ‖(Real.cos t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one t
  have hc1 : ‖2 * ((Real.cos t : ℂ) - 1)‖ ≤ 2 * |t| := by
    have : (2 : ℂ) * ((Real.cos t : ℂ) - 1) = ((2 * (Real.cos t - 1) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [Real.cos_le_one t])]
    linarith [ts2_one_sub_cos_le t]
  have hs : ‖(Real.sin t : ℂ) * I‖ ≤ |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_abs
  have hbb : ‖b (x + t) - b (x - t)‖ ≤ 2 * K0 := by
    refine (norm_sub_le _ _).trans ?_
    linarith [hb (x + t), hb (x - t)]
  have t1 : ‖(Real.cos t : ℂ) * (b (x + t) + b (x - t) - 2 * b x)‖ ≤ K1 * |t| := by
    rw [norm_mul]
    calc ‖(Real.cos t : ℂ)‖ * ‖b (x + t) + b (x - t) - 2 * b x‖ ≤ 1 * (K1 * |t|) :=
          mul_le_mul hc hz0 (norm_nonneg _) zero_le_one
      _ = K1 * |t| := one_mul _
  have t2 : ‖(2 * ((Real.cos t : ℂ) - 1)) * b x‖ ≤ 2 * |t| * K0 := by
    rw [norm_mul]
    exact mul_le_mul hc1 (hb x) (norm_nonneg _) (by positivity)
  have t3 : ‖((Real.sin t : ℂ) * I) * (b (x + t) - b (x - t))‖ ≤ |t| * (2 * K0) := by
    rw [norm_mul]
    exact mul_le_mul hs hbb (norm_nonneg _) (abs_nonneg t)
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3).trans ?_
  nlinarith [abs_nonneg t]

/-- The real vector field `u = 2 Re(-i b e^{-iθ})` built from the trace `b` is Zygmund. -/
theorem ts2_u_zygmund {b : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hbc : Continuous b)
    (hper : ∀ x, b (x + 2 * π) = b x) (hb : ∀ x, ‖b x‖ ≤ 2 * M)
    (hz : ∀ x t, ‖b (x + t) + b (x - t) - 2 * b x‖ ≤ 24 * M * |t|) :
    IsZygmund (fun θ : ℝ => 2 * (-I * b θ * exp (-((θ : ℂ) * I))).re) := by
  refine ⟨by fun_prop, ?_, 64 * M, ?_⟩
  · intro θ
    have h2pi : exp (-(2 * (π : ℂ) * I)) = 1 := by
      rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    have : exp (-(((θ + 2 * π : ℝ) : ℂ) * I)) = exp (-((θ : ℂ) * I)) := by
      push_cast
      rw [show -(((θ : ℂ) + 2 * (π : ℂ)) * I) = -((θ : ℂ) * I) + -(2 * (π : ℂ) * I) by ring,
        Complex.exp_add, h2pi, mul_one]
    simp only [hper, this]
  · intro θ t
    have h := ts2_second_diff_q (K0 := 2 * M) (K1 := 24 * M) (by linarith) hb hz θ t
    set Δ : ℂ := -I * b (θ + t) * exp (-(((θ + t : ℝ) : ℂ) * I)) + (-I * b (θ - t) * exp (-(((θ - t : ℝ) : ℂ) * I)))
        - 2 * (-I * b θ * exp (-((θ : ℂ) * I))) with hΔ
    have hre : 2 * (-I * b (θ + t) * exp (-(((θ + t : ℝ) : ℂ) * I))).re +
        2 * (-I * b (θ - t) * exp (-(((θ - t : ℝ) : ℂ) * I))).re -
        2 * (2 * (-I * b θ * exp (-((θ : ℂ) * I))).re) = 2 * Δ.re := by
      simp only [hΔ, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
      ring
    show |2 * (-I * b (θ + t) * exp (-(((θ + t : ℝ) : ℂ) * I))).re +
        2 * (-I * b (θ - t) * exp (-(((θ - t : ℝ) : ℂ) * I))).re -
        2 * (2 * (-I * b θ * exp (-((θ : ℂ) * I))).re)| ≤ 64 * M * |t|
    rw [hre, abs_mul, abs_two]
    have := Complex.abs_re_le_norm Δ
    nlinarith [abs_nonneg t]

theorem ts2_fc_conj (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (fun θ => conj (f θ)) n = conj (fourierCoeff f (-n)) := by
  have he : (fun θ : ℝ => conj (f θ) * exp (-((n : ℂ) * θ * I))) =
      (fun θ : ℝ => conj (f θ * exp (-(((-n : ℤ) : ℂ) * θ * I)))) := by
    funext θ
    simp only [map_mul, ← exp_conj, map_neg, map_intCast, conj_I, Int.cast_neg, conj_ofReal]
    congr 2
    ring
  have hi (g : ℝ → ℂ) : (∫ θ in (0 : ℝ)..2 * π, conj (g θ)) =
      conj (∫ θ in (0 : ℝ)..2 * π, g θ) := by
    simp only [intervalIntegral, integral_conj, map_sub]
  unfold fourierCoeff
  rw [he, hi, map_mul]
  congr 1
  norm_num [Complex.ext_iff]

theorem ts2_fc_q (b : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (fun θ => -I * b θ * exp (-((θ : ℂ) * I))) n = -I * fourierCoeff b (n + 1) := by
  have h : ∀ θ : ℝ, -I * b θ * exp (-((θ : ℂ) * I)) * exp (-((n : ℂ) * θ * I)) =
      -I * (b θ * exp (-((((n + 1 : ℤ)) : ℂ) * θ * I))) := by
    intro θ
    rw [show -((((n + 1 : ℤ)) : ℂ) * θ * I) = -((θ : ℂ) * I) + -((n : ℂ) * θ * I) by push_cast; ring,
      Complex.exp_add]
    ring
  unfold fourierCoeff
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Fourier coefficients of `u = 2 Re q`, `q = -i b e^{-iθ}`. -/
theorem ts2_fc_u (b : ℝ → ℂ) (hbc : Continuous b) (n : ℤ) :
    fourierCoeff (fun θ => ((2 * (-I * b θ * exp (-((θ : ℂ) * I))).re : ℝ) : ℂ)) n =
      -I * fourierCoeff b (n + 1) + I * conj (fourierCoeff b (1 - n)) := by
  set q : ℝ → ℂ := fun θ => -I * b θ * exp (-((θ : ℂ) * I)) with hq
  have hqc : Continuous q := by simp only [hq]; fun_prop
  have hsplit : (fun θ : ℝ => ((2 * (q θ).re : ℝ) : ℂ)) = fun θ => q θ + conj (q θ) := by
    funext θ
    rw [Complex.add_conj]
  have hint : ∀ f : ℝ → ℂ, Continuous f →
      fourierCoeff (fun θ => f θ + conj (f θ)) n = fourierCoeff f n + fourierCoeff (fun θ => conj (f θ)) n := by
    intro f hf
    unfold fourierCoeff
    have h1 : Continuous fun θ : ℝ => f θ * exp (-((n : ℂ) * θ * I)) := by fun_prop
    have h2 : Continuous fun θ : ℝ => conj (f θ) * exp (-((n : ℂ) * θ * I)) := by
      have := (Complex.continuous_conj.comp hf); fun_prop
    simp only [add_mul]
    rw [intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)]
    ring
  show fourierCoeff (fun θ => ((2 * (q θ).re : ℝ) : ℂ)) n = _
  rw [hsplit, hint q hqc, ts2_fc_conj, hq, ts2_fc_q, ts2_fc_q]
  simp only [map_mul, map_neg, conj_I]
  have : -n + 1 = 1 - n := by ring
  rw [this]
  ring

theorem ts2_deriv_ev {f g : ℂ → ℂ} (hf : ∀ w ∈ unitDisc, HasDerivAt f (g w) w) {z : ℂ} (hz : z ∈ unitDisc) :
    deriv f =ᶠ[𝓝 z] g :=
  Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (show z ∈ ball (0 : ℂ) 1 from hz))
    (fun w hw => (hf w hw).deriv)

theorem ts2_iter3 {F0 F1 F2 phi : ℂ → ℂ} (h2 : ∀ w ∈ unitDisc, HasDerivAt F2 (phi w) w)
    (h1 : ∀ w ∈ unitDisc, HasDerivAt F1 (F2 w) w) (h0 : ∀ w ∈ unitDisc, HasDerivAt F0 (F1 w) w)
    {z : ℂ} (hz : z ∈ unitDisc) : iteratedDeriv 3 F0 z = phi z := by
  rw [iteratedDeriv_succ', (ts2_deriv_ev h0 hz).iteratedDeriv_eq 2, iteratedDeriv_succ',
    (ts2_deriv_ev h1 hz).iteratedDeriv_eq 1, iteratedDeriv_one]
  exact (h2 z hz).deriv

theorem ts2_taylor_low {F0 F1 F2 : ℂ → ℂ} (h00 : F0 0 = 0) (h10 : F1 0 = 0) (h20 : F2 0 = 0)
    (h1 : ∀ w ∈ unitDisc, HasDerivAt F1 (F2 w) w) (h0 : ∀ w ∈ unitDisc, HasDerivAt F0 (F1 w) w) :
    iteratedDeriv 0 F0 0 = 0 ∧ iteratedDeriv 1 F0 0 = 0 ∧ iteratedDeriv 2 F0 0 = 0 := by
  have hz : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  refine ⟨by simpa using h00, ?_, ?_⟩
  · rw [iteratedDeriv_one, (h0 0 hz).deriv, h10]
  · rw [iteratedDeriv_succ', (ts2_deriv_ev h0 hz).iteratedDeriv_eq 1, iteratedDeriv_one, (h1 0 hz).deriv, h20]

/-- Direction (b): existence of the Zygmund field `u` for a weighted-bounded holomorphic `phi`. -/
theorem ts2_exists_u {phi : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hd : DifferentiableOn ℂ phi unitDisc)
    (hb : ∀ z ∈ unitDisc, ‖phi z‖ ≤ M / (1 - ‖z‖) ^ 2) :
    ∃ u : ℝ → ℝ, u ∈ tangentQS ∧
      (∀ n : ℤ, n ∈ ({-1, 0, 1} : Set ℤ) → fourierCoeff (fun θ => (u θ : ℂ)) n = 0) ∧
      ∀ z ∈ unitDisc, phi z = iteratedDeriv 3 (uPlus u) z := by
  obtain ⟨F0, F1, F2, h00, h10, h20, h2, h1, h0, b, hbc, hper, hb2, hz, happ⟩ := ts2_trace_final hM hd hb
  have hFd : DifferentiableOn ℂ F0 unitDisc := fun w hw => (h0 w hw).differentiableAt.differentiableWithinAt
  obtain ⟨a0, a1, a2⟩ := ts2_taylor_low h00 h10 h20 h1 h0
  have hB : ∀ k : ℤ, fourierCoeff b k =
      if 0 ≤ k then (k.toNat ! : ℂ)⁻¹ * iteratedDeriv k.toNat F0 0 else 0 :=
    fun k => ts2_fourier_b hFd hbc happ k
  have hBneg : ∀ k : ℤ, k < 0 → fourierCoeff b k = 0 := fun k hk => by
    rw [hB k, if_neg (not_le.2 hk)]
  have hB0 : fourierCoeff b 0 = 0 := by rw [hB 0]; simp [a0]
  have hB1 : fourierCoeff b 1 = 0 := by rw [hB 1]; simp [a1]
  have hB2 : fourierCoeff b 2 = 0 := by rw [hB 2]; simp [a2]
  have hBnat : ∀ n : ℕ, fourierCoeff b (n : ℤ) = (n ! : ℂ)⁻¹ * iteratedDeriv n F0 0 := fun n => by
    rw [hB]; simp
  set u : ℝ → ℝ := fun θ => 2 * (-I * b θ * exp (-((θ : ℂ) * I))).re with hu
  have hfc : ∀ n : ℤ, fourierCoeff (fun θ => (u θ : ℂ)) n =
      -I * fourierCoeff b (n + 1) + I * conj (fourierCoeff b (1 - n)) := fun n => ts2_fc_u b hbc n
  have hc0 : fourierCoeff (fun θ => (u θ : ℂ)) 0 = 0 := by
    rw [hfc]; simp [hB1]
  have hcm1 : fourierCoeff (fun θ => (u θ : ℂ)) (-1) = 0 := by
    rw [hfc]; norm_num [hB0, hB2]
  have hc1 : fourierCoeff (fun θ => (u θ : ℂ)) 1 = 0 := by
    rw [hfc]; norm_num [hB0, hB2]
  refine ⟨u, ⟨ts2_u_zygmund hM hbc hper hb2 hz, ?_⟩, ?_, ?_⟩
  · have h := hc0
    unfold fourierCoeff at h
    simp only [Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at h
    have h2 : ∫ θ in (0 : ℝ)..2 * π, (u θ : ℂ) = 0 := by
      have hpi : (1 / (2 * π) : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      exact (mul_eq_zero.1 h).resolve_left hpi
    rw [intervalIntegral.integral_ofReal] at h2
    exact_mod_cast h2
  · intro n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl
    · exact hcm1
    · exact hc0
    · exact hc1
  · have hup : ∀ z ∈ unitDisc, uPlus u z = F0 z := by
      intro z hz
      have hcc : ∀ n : ℕ, fourierCoeff (fun θ => (u θ : ℂ)) ((n : ℤ) + 1) =
          -I * (((n + 2) ! : ℂ)⁻¹ * iteratedDeriv (n + 2) F0 0) := by
        intro n
        rw [hfc]
        have hneg : fourierCoeff b (1 - ((n : ℤ) + 1)) = 0 := by
          rcases Nat.eq_zero_or_pos n with h | h
          · subst h; simpa using hB0
          · exact hBneg _ (by omega)
        rw [hneg]
        have := hBnat (n + 2)
        rw [show (n : ℤ) + 1 + 1 = ((n + 2 : ℕ) : ℤ) by push_cast; ring, this]
        simp
      have hs := (hasSum_nat_add_iff' 2).mpr (ts2_taylor_hasSum hFd hz)
      have hsum0 : ∑ i ∈ Finset.range 2, ((i ! : ℂ)⁻¹ * iteratedDeriv i F0 0) * z ^ i = 0 := by
        simp [Finset.sum_range_succ, a0, a1]
      rw [hsum0, sub_zero] at hs
      unfold uPlus
      have e : ∀ n : ℕ, fourierCoeff (fun θ => (u θ : ℂ)) ((n : ℤ) + 1) * z ^ (n + 2) =
          -I * (((n + 2) ! : ℂ)⁻¹ * iteratedDeriv (n + 2) F0 0 * z ^ (n + 2)) := fun n => by
        rw [hcc]; ring
      simp_rw [e]
      rw [tsum_mul_left, hs.tsum_eq]
      rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
    intro z hz
    have hev : uPlus u =ᶠ[𝓝 z] F0 :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (show z ∈ ball (0 : ℂ) 1 from hz))
        (fun w hw => hup w hw)
    rw [hev.iteratedDeriv_eq 3, ts2_iter3 h2 h1 h0 hz]

theorem ts2_uPlus_props {u : ℝ → ℝ} (hu : u ∈ tangentQS) :
    DifferentiableOn ℂ (uPlus u) unitDisc ∧
      ∀ z ∈ unitDisc, HasSum (fun n : ℕ => (if n < 2 then (0 : ℂ)
        else I * fourierCoeff (fun θ => (u θ : ℂ)) ((n : ℤ) - 1)) * z ^ n) (uPlus u z) := by
  set c : ℤ → ℂ := fourierCoeff (fun θ => (u θ : ℂ)) with hc
  have hs : Summable (fun n : ℤ => ‖c n‖) := tangentQS_fourier_summable hu
  have hsn : Summable (fun n : ℕ => ‖c ((n : ℤ) + 1)‖) :=
    hs.comp_injective (fun a b h => by simpa using h)
  have hterm : ∀ z ∈ unitDisc, ∀ n : ℕ, ‖c ((n : ℤ) + 1) * z ^ (n + 2)‖ ≤ ‖c ((n : ℤ) + 1)‖ := by
    intro z hz n
    rw [norm_mul, norm_pow]
    have h1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le
    have h2 : ‖z‖ ^ (n + 2) ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
    nlinarith [norm_nonneg (c ((n : ℤ) + 1))]
  have hdiff : DifferentiableOn ℂ (fun z => ∑' n : ℕ, c ((n : ℤ) + 1) * z ^ (n + 2)) unitDisc :=
    differentiableOn_tsum_of_summable_norm hsn
      (fun n => (differentiableOn_const _).mul (differentiableOn_id.pow _)) isOpen_ball
      (fun n z hz => hterm z hz n)
  refine ⟨hdiff.const_mul I, fun z hz => ?_⟩
  have hsum : Summable (fun n : ℕ => c ((n : ℤ) + 1) * z ^ (n + 2)) :=
    Summable.of_norm_bounded hsn (fun n => hterm z hz n)
  have hS := hsum.hasSum.mul_left I
  refine (hasSum_nat_add_iff' 2).mp ?_
  have e : (fun n : ℕ => (if n + 2 < 2 then (0 : ℂ) else I * c (((n + 2 : ℕ) : ℤ) - 1)) * z ^ (n + 2)) =
      fun n : ℕ => I * (c ((n : ℤ) + 1) * z ^ (n + 2)) := by
    funext n
    have : ¬ (n + 2 < 2) := by omega
    rw [if_neg this, show (((n + 2 : ℕ) : ℤ) - 1) = (n : ℤ) + 1 by push_cast; ring]
    ring
  have h0 : (∑ i ∈ Finset.range 2, (if i < 2 then (0 : ℂ) else I * c ((i : ℤ) - 1)) * z ^ i) = 0 := by
    simp [Finset.sum_range_succ]
  rw [h0, sub_zero]
  convert hS using 1
  rfl

theorem ts2_unique_u {phi : ℂ → ℂ} {u v : ℝ → ℝ} (hu : u ∈ tangentQS) (hv : v ∈ tangentQS)
    (hu0 : fourierCoeff (fun θ => (u θ : ℂ)) 0 = 0) (hv0 : fourierCoeff (fun θ => (v θ : ℂ)) 0 = 0)
    (hu1 : fourierCoeff (fun θ => (u θ : ℂ)) 1 = 0) (hv1 : fourierCoeff (fun θ => (v θ : ℂ)) 1 = 0)
    (heu : ∀ z ∈ unitDisc, phi z = iteratedDeriv 3 (uPlus u) z)
    (hev : ∀ z ∈ unitDisc, phi z = iteratedDeriv 3 (uPlus v) z) : u = v := by
  obtain ⟨hdu, hsu⟩ := ts2_uPlus_props hu
  obtain ⟨hdv, hsv⟩ := ts2_uPlus_props hv
  set cu : ℤ → ℂ := fourierCoeff (fun θ => (u θ : ℂ)) with hcu
  set cv : ℤ → ℂ := fourierCoeff (fun θ => (v θ : ℂ)) with hcv
  set H : ℂ → ℂ := fun z => uPlus u z - uPlus v z with hH
  have hdH : DifferentiableOn ℂ H unitDisc := hdu.sub hdv
  have hH3 : ∀ z ∈ unitDisc, iteratedDeriv 3 H z = 0 := by
    intro z hz
    have hz' : z ∈ ball (0 : ℂ) 1 := hz
    have hcu' : ContDiffAt ℂ 3 (uPlus u) z := ((hdu.analyticOnNhd isOpen_ball) z hz).contDiffAt
    have hcv' : ContDiffAt ℂ 3 (uPlus v) z := ((hdv.analyticOnNhd isOpen_ball) z hz).contDiffAt
    rw [hH, iteratedDeriv_fun_sub hcu' hcv', ← heu z hz, ← hev z hz, sub_self]
  have hT : ∀ k : ℕ, 3 ≤ k → iteratedDeriv k H 0 = 0 := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
    have e : iteratedDeriv 3 H =ᶠ[𝓝 (0 : ℂ)] fun _ => (0 : ℂ) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (show (0 : ℂ) ∈ ball (0 : ℂ) 1 from h0))
        (fun w hw => hH3 w hw)
    have : iteratedDeriv (m + 3) H 0 = iteratedDeriv m (iteratedDeriv 3 H) 0 := by
      rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, Function.iterate_add_apply]
    rw [this, e.iteratedDeriv_eq m, iteratedDeriv_const]
    simp
  set gu : ℕ → ℂ := fun n => if n < 2 then 0 else I * cu ((n : ℤ) - 1) with hgu
  set gv : ℕ → ℂ := fun n => if n < 2 then 0 else I * cv ((n : ℤ) - 1) with hgv
  have hHser : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => (gu n - gv n) * z ^ n) (H z) := by
    intro z hz
    have := (hsu z hz).sub (hsv z hz)
    convert this using 1
    funext n
    ring
  have hcoef : ∀ n : ℕ, gu n - gv n = ((n ! : ℂ)⁻¹ * iteratedDeriv n H 0) :=
    fun n => ts2_series_coeff_unique (hHser) (fun z hz => ts2_taylor_hasSum hdH hz) n
  have hgeq : ∀ n : ℕ, 3 ≤ n → gu n = gv n := by
    intro n hn
    have := hcoef n
    rw [hT n hn] at this
    simpa [sub_eq_zero] using this
  have hc_nat : ∀ m : ℕ, cu (m : ℤ) = cv (m : ℤ) := by
    intro m
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · simpa using hu0.trans hv0.symm
      · simpa using hu1.trans hv1.symm
    · have := hgeq (m + 1) (by omega)
      simp only [hgu, hgv, show ¬ (m + 1 < 2) by omega, if_false] at this
      have h' := mul_left_cancel₀ I_ne_zero this
      simpa using h'
  refine tangentQS_eq_of_fourierCoeff_eq hu hv (fun n => ?_)
  show cu n = cv n
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact hc_nat m
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨n.natAbs, by omega⟩
    rw [hm, hcu, hcv, fourierCoeff_neg_real, fourierCoeff_neg_real]
    exact congrArg conj (hc_nat m)

theorem ts2_second (phi : AInf unitDisc) :
    ∃! u : ℝ → ℝ, u ∈ tangentQS ∧
      (∀ n : ℤ, n ∈ ({-1, 0, 1} : Set ℤ) → fourierCoeff (fun θ => (u θ : ℂ)) n = 0) ∧
      ∀ z ∈ unitDisc, AInf.toFun phi z = iteratedDeriv 3 (uPlus u) z := by
  have hd : DifferentiableOn ℂ (AInf.toFun phi) unitDisc := phi.2
  have hb : ∀ z ∈ unitDisc, ‖AInf.toFun phi z‖ ≤ ‖phi.1‖ / (1 - ‖z‖) ^ 2 := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
    have e : AInf.toFun phi z = phi.1 ⟨z, hz⟩ / ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ^ 2 := by
      unfold AInf.toFun unweight
      rw [dif_pos hz]
      push_cast
      rfl
    rw [e, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < 1 - ‖z‖ := by linarith
    have h1 : 1 - ‖z‖ ≤ 1 - ‖z‖ ^ 2 := by nlinarith
    rw [abs_of_pos (by linarith : 0 < 1 - ‖z‖ ^ 2)]
    calc ‖phi.1 ⟨z, hz⟩‖ / (1 - ‖z‖ ^ 2) ^ 2 ≤ ‖phi.1‖ / (1 - ‖z‖ ^ 2) ^ 2 := by
          gcongr
          exact BoundedContinuousFunction.norm_coe_le_norm _ _
      _ ≤ ‖phi.1‖ / (1 - ‖z‖) ^ 2 := by
          gcongr
  obtain ⟨u, hu, hf, hder⟩ := ts2_exists_u (norm_nonneg _) hd hb
  refine ⟨u, ⟨hu, hf, hder⟩, ?_⟩
  rintro v ⟨hv, hfv, hderv⟩
  exact ts2_unique_u hv hu (hfv 0 (by simp)) (hf 0 (by simp)) (hfv 1 (by simp)) (hf 1 (by simp)) hderv hder

end Ts2Aux

-- `TS2` (with its first conjunct, formerly `TS2_a_new`) moved to `Ch1/TS2A.lean` (2026-10-26).

end TakhtajanTeo
