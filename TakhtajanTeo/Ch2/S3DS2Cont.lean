import TakhtajanTeo.Ch2.S4GFirstVariation
import TakhtajanTeo.Ch2.R43Potential
import TakhtajanTeo.Ch1.GroupTopGroup

/-!
# Density route (5b): `S₂` is continuous on `T₀(1)` (下属6, work file)

At `q = [κ]`, `κ ∈ 𝒪(𝔻*)₁` (`r43p_groupO_rep`), the chart points are `[Λφ * κ]`, and
`‖B₁(Λφ * κ) - B₁(κ)‖²_HS = ∬∬ |K₁(𝖿^{Λφ*κ}) - K₁(𝖿^κ)|²` (bidisk Parseval for the difference of the two kernel
series) `≤ C ‖φ‖²` (`s4g_step_bound`, `l29b_Lambda_L2`). `S₂ = s3fd_logSeries ∘ B₁` (`s3fd_liouville_eq`) with
`s3fd_logSeries` continuous on `{‖B‖ < 1}` (`r43p_logSeries_analytic`, `pgb_norm_lt_one`), and the chart images of
small balls are neighbourhoods (`gtr_c_image_mem`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- Bidisk Parseval for the difference of two Grunsky kernels. -/
theorem s3d_kerK1_diff {κ κ' : LinfStar} (hκ : κ ∈ LinfStarBall) (hκ' : κ' ∈ LinfStarBall) :
    (∑' q : ℕ × ℕ, (‖B1 (grunsky (fsans κ') (gsans κ')) q.1 q.2 -
        B1 (grunsky (fsans κ) (gsans κ)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans κ') x.1 x.2 - kerK1 (fsans κ) x.1 x.2‖₊ : ℝ≥0∞) ^ 2 := by
  have hcf := S2C.s2c_conf_f hκ
  have hcf' := S2C.s2c_conf_f hκ'
  let a : ℕ → ℕ → ℂ := fun m n => grunsky (fsans κ) (gsans κ) (-(m : ℤ)) (-(n : ℤ))
  let a' : ℕ → ℕ → ℂ := fun m n => grunsky (fsans κ') (gsans κ') (-(m : ℤ)) (-(n : ℤ))
  have hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (fsans κ z - fsans κ w) / (z - w) = exp (grunsky (fsans κ) (gsans κ) 0 0 - S) :=
    (grunsky_spec (AppB.b8_welding_normalized_pair hκ)).1.2.2.2.1
  have hexp' : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a' p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (fsans κ' z - fsans κ' w) / (z - w) = exp (grunsky (fsans κ') (gsans κ') 0 0 - S) :=
    (grunsky_spec (AppB.b8_welding_normalized_pair hκ')).1.2.2.2.1
  set d : ℕ → ℕ → ℂ := fun p q => (a' (p + 1) (q + 1) - a (p + 1) (q + 1)) * ((p + 1 : ℕ) : ℂ) *
    ((q + 1 : ℕ) : ℂ) with hd
  have hser : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => d p.1 p.2 * z ^ p.1 * w ^ p.2)
        ((π : ℂ) * (kerK1 (fsans κ') z w - kerK1 (fsans κ) z w)) := by
    intro z hz w hw hzw
    have h1 := s2c_kernel_series_of_exp hcf'.1 hcf'.2.1 hexp' hz hw hzw
    have h2 := s2c_kernel_series_of_exp hcf.1 hcf.2.1 hexp hz hw hzw
    have e1 : (fun p : ℕ × ℕ => d p.1 p.2 * z ^ p.1 * w ^ p.2) = fun p : ℕ × ℕ =>
        a' (p.1 + 1) (p.2 + 1) * ((p.1 + 1 : ℕ) : ℂ) * ((p.2 + 1 : ℕ) : ℂ) * z ^ p.1 * w ^ p.2 -
          a (p.1 + 1) (p.2 + 1) * ((p.1 + 1 : ℕ) : ℂ) * ((p.2 + 1 : ℕ) : ℂ) * z ^ p.1 * w ^ p.2 := by
      funext p
      simp only [hd]
      ring
    rw [e1, mul_sub]
    exact h1.sub h2
  have hs0 := s2c_bidisk_hasSum (a := d) (fun z hz w hw hzw => (hser z hz w hw hzw).summable)
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ → ℂ,
      F = fun z w => ∑' p : ℕ × ℕ, d p.1 p.2 * z ^ p.1 * w ^ p.2 := ⟨_, rfl⟩
  have hs : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => d p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w) := by
    intro z hz w hw
    rw [hFdef]
    exact hs0 z hz w hw
  have hFK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      F z w = (π : ℂ) * (kerK1 (fsans κ') z w - kerK1 (fsans κ) z w) :=
    fun z hz w hw hzw => (hs z hz w hw).unique (hser z hz w hw hzw)
  have hpar := s2c_bidisk_parseval hs
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hae : (fun x : ℂ × ℂ => (‖kerK1 (fsans κ') x.1 x.2 - kerK1 (fsans κ) x.1 x.2‖₊ : ℝ≥0∞) ^ 2) =ᵐ[
      (volume : Measure (ℂ × ℂ)).restrict (unitDisc ×ˢ unitDisc)]
      (fun x => ENNReal.ofReal (1 / π ^ 2) * ENNReal.ofReal (‖F x.1 x.2‖ ^ 2)) := by
    filter_upwards [s2c_diag_ae, ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)]
      with x hx hxm
    rw [hFK x.1 hxm.1 x.2 hxm.2 hx, ← ENNReal.ofReal_mul (by positivity)]
    have e1 : (‖kerK1 (fsans κ') x.1 x.2 - kerK1 (fsans κ) x.1 x.2‖₊ : ℝ≥0∞) ^ 2 =
        ENNReal.ofReal (‖kerK1 (fsans κ') x.1 x.2 - kerK1 (fsans κ) x.1 x.2‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    rw [e1]
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hπ.le]
    field_simp
  rw [lintegral_congr_ae hae, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hpar,
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  have e : (‖B1 (grunsky (fsans κ') (gsans κ')) q.1 q.2 - B1 (grunsky (fsans κ) (gsans κ)) q.1 q.2‖₊ :
      ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖B1 (grunsky (fsans κ') (gsans κ')) q.1 q.2 -
        B1 (grunsky (fsans κ) (gsans κ)) q.1 q.2‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rfl
  rw [e]
  congr 1
  have eB : B1 (grunsky (fsans κ') (gsans κ')) q.1 q.2 - B1 (grunsky (fsans κ) (gsans κ)) q.1 q.2 =
      (Real.sqrt ((q.1 + 1) * (q.2 + 1) : ℝ) : ℂ) * (a' (q.1 + 1) (q.2 + 1) - a (q.1 + 1) (q.2 + 1)) := by
    unfold B1
    simp only [a, a']
    push_cast
    ring
  rw [eB, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity)]
  simp only [hd, norm_mul, Complex.norm_natCast]
  push_cast
  field_simp

/-- **(5b)** `S₂` is continuous on `T₀(1)` in the Hilbert manifold topology. -/
theorem s3d_S2_cont : @ContinuousOn T1 ℝ hilbertTopology _ liouvilleS2 T01 := by
  letI : TopologicalSpace T1 := hilbertTopology
  intro q hq
  apply ContinuousAt.continuousWithinAt
  obtain ⟨κ, hκO, rfl⟩ := r43p_groupO_rep q
  set ε₁ : ℝ := min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) with hε₁
  have hd := delta0_bounds
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (div_pos (by linarith [hd.1]) (Real.sqrt_pos.2 (by positivity)))
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  set K : ℝ := 2 / (π * (1 - delta0) ^ 4) with hK
  have hK0 : 0 ≤ K := by
    have : 0 < 1 - delta0 := by linarith [hd.2]
    positivity
  -- finite Hilbert–Schmidt sums give `ℓ²` vectors
  have hmemOf : ∀ ν : LinfStar,
      (∑' q : ℕ × ℕ, (‖B1 (grunsky (fsans ν) (gsans ν)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ →
        Memℓp (fun q : ℕ × ℕ => B1 (grunsky (fsans ν) (gsans ν)) q.1 q.2) 2 := by
    intro ν h
    have hs : Summable (fun q : ℕ × ℕ => (‖B1 (grunsky (fsans ν) (gsans ν)) q.1 q.2‖₊ ^ 2 : ℝ≥0)) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable]
      simpa [ENNReal.coe_pow] using h.ne
    have hr : Summable (fun q : ℕ × ℕ => ‖B1 (grunsky (fsans ν) (gsans ν)) q.1 q.2‖ ^ 2) := by
      have := NNReal.summable_coe.2 hs
      simpa using this
    rw [memℓp_gen_iff h2]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact hr
  have hKfin := gk_K1_T01 _ hq κ rfl
  have hmem0 : Memℓp (fun q : ℕ × ℕ => B1 (grunsky (fsans (κ : LinfStar)) (gsans (κ : LinfStar))) q.1 q.2) 2 :=
    hmemOf _ (by rw [t210_hs_eq κ.2]; exact hKfin)
  set X0 : s3tc_HS := ⟨_, hmem0⟩ with hX0
  -- the chart points
  have hdata : ∀ φ : A2 unitDisc, ‖φ‖ < ε₁ →
      ∃ hm : beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar) ∈ LinfStarBall,
        ∃ hmem : Memℓp (fun q : ℕ × ℕ => B1 (grunsky (fsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))
          (gsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))) q.1 q.2) 2,
        bersChartInv κ (A2toAInf φ) = Phi ⟨_, hm⟩ ∧ ‖(⟨_, hmem⟩ : s3tc_HS) - X0‖ ≤ Real.sqrt K * ‖φ‖ := by
    intro φ hφ
    obtain ⟨hn, -, -, -⟩ := gtp_small_a hφ
    have hΛ : Lambda (A2toAInf φ) ∈ LinfStarBall := Lambda_mem_ball hn
    have hm : beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 hΛ
    have hstep := t210_step_bound (κ := κ) (ν := ⟨_, hΛ⟩) hφ rfl
    have hdiff := s3d_kerK1_diff κ.2 hm
    have hfin : (∑' q : ℕ × ℕ, (‖B1 (grunsky (fsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))
        (gsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ := by
      rw [t210_hs_eq hm]
      calc _ ≤ ∫⁻ x in unitDisc ×ˢ unitDisc,
            (2 * (‖kerK1 (fsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar))) x.1 x.2 -
              kerK1 (fsans (κ : LinfStar)) x.1 x.2‖₊ : ℝ≥0∞) ^ 2 +
              2 * (‖kerK1 (fsans (κ : LinfStar)) x.1 x.2‖₊ : ℝ≥0∞) ^ 2) :=
            lintegral_mono fun x => gk_sq_tri _ _
        _ = 2 * (∫⁻ x in unitDisc ×ˢ unitDisc,
              (‖kerK1 (fsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar))) x.1 x.2 -
                kerK1 (fsans (κ : LinfStar)) x.1 x.2‖₊ : ℝ≥0∞) ^ 2) +
            2 * ∫⁻ x in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (κ : LinfStar)) x.1 x.2‖₊ : ℝ≥0∞) ^ 2 := by
            rw [lintegral_add_right' _ ((gk_kerK1_aemeas κ.2).const_mul 2),
              lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
        _ < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num)
            (lt_of_le_of_lt hstep ENNReal.ofReal_lt_top), ENNReal.mul_lt_top (by norm_num) hKfin⟩
    have hmem := hmemOf _ hfin
    refine ⟨hm, hmem, ?_, ?_⟩
    · rw [ct_bersChartInv_eq hn, bt_rightTrans_phi]
    · set X : s3tc_HS := ⟨_, hmem⟩ with hX
      have hsub : Memℓp (fun q : ℕ × ℕ => B1 (grunsky (fsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))
          (gsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))) q.1 q.2 -
            B1 (grunsky (fsans (κ : LinfStar)) (gsans (κ : LinfStar))) q.1 q.2) 2 := hmem.sub hmem0
      have hsr : Summable (fun q : ℕ × ℕ => ‖B1 (grunsky (fsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))
          (gsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))) q.1 q.2 -
            B1 (grunsky (fsans (κ : LinfStar)) (gsans (κ : LinfStar))) q.1 q.2‖ ^ 2) := by
        have := (memℓp_gen_iff h2).1 hsub
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using this
      have hreal : (∑' q : ℕ × ℕ, ‖B1 (grunsky (fsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))
          (gsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))) q.1 q.2 -
            B1 (grunsky (fsans (κ : LinfStar)) (gsans (κ : LinfStar))) q.1 q.2‖ ^ 2) ≤ K * ‖φ‖ ^ 2 := by
        have hE : ENNReal.ofReal (∑' q : ℕ × ℕ, ‖B1 (grunsky (fsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))
            (gsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))) q.1 q.2 -
              B1 (grunsky (fsans (κ : LinfStar)) (gsans (κ : LinfStar))) q.1 q.2‖ ^ 2) ≤
            ENNReal.ofReal (K * ‖φ‖ ^ 2) := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsr]
          calc _ = ∑' q : ℕ × ℕ, (‖B1 (grunsky (fsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))
                (gsans (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)))) q.1 q.2 -
                  B1 (grunsky (fsans (κ : LinfStar)) (gsans (κ : LinfStar))) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 := by
                refine tsum_congr fun q => ?_
                rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
                rfl
            _ = _ := hdiff
            _ ≤ _ := hstep
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hE
      apply lp.norm_le_of_tsum_le h2 (by positivity)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply]
      rw [mul_pow, Real.sq_sqrt hK0]
      exact hreal
  -- continuity of the log series at `X0`
  have hop : ‖s3tc_toOperator X0‖ < 1 := (pgb_norm_lt_one κ.2).1
  have hcont : ContinuousAt s3fd_logSeries X0 := (r43p_logSeries_analytic X0 hop).continuousAt
  have hS0 : liouvilleS2 (Phi κ) = s3fd_logSeries X0 := (s3fd_liouville_eq κ.2 X0 (fun m n => rfl)).symm
  show Tendsto liouvilleS2 (𝓝 (Phi κ)) (𝓝 (liouvilleS2 (Phi κ)))
  rw [hS0]
  intro U hU
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 (hcont hU)
  set δ : ℝ := min ε₁ (η / (Real.sqrt K + 1)) with hδ
  have hδ0 : 0 < δ := lt_min hε₁0 (div_pos hη (by positivity))
  have hδr : δ ≤ Real.sqrt (π / 3) := (min_le_left _ _).trans (min_le_left _ _)
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (gtr_c_image_mem hκO hδ0 hδr) ?_
  rintro _ ⟨φ, hφ, rfl⟩
  have hφδ : ‖φ‖ < δ := mem_ball_zero_iff.1 hφ
  have hφ1 : ‖φ‖ < ε₁ := lt_of_lt_of_le hφδ (min_le_left _ _)
  obtain ⟨hm, hmem, hpt, hdist⟩ := hdata φ hφ1
  show liouvilleS2 (bersChartInv κ (A2toAInf φ)) ∈ U
  rw [hpt, ← s3fd_liouville_eq hm ⟨_, hmem⟩ (fun m n => rfl)]
  apply hball
  rw [mem_ball, dist_eq_norm]
  have hsK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  calc ‖(⟨_, hmem⟩ : s3tc_HS) - X0‖ ≤ Real.sqrt K * ‖φ‖ := hdist
    _ ≤ Real.sqrt K * δ := mul_le_mul_of_nonneg_left hφδ.le hsK
    _ ≤ Real.sqrt K * (η / (Real.sqrt K + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hsK
    _ < η := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

end TakhtajanTeo.Ch2
