import TakhtajanTeo.Ch2.BergmanSeries
import TakhtajanTeo.Ch1.Eq22WeakStokes
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import LiZhongQC.Lemmas.Pompeiu
import TakhtajanTeo.Ch1.TS2
import TakhtajanTeo.Ch2.S5_PeriodMapping

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

-- L1
theorem s5st_basis_memLp (n : ℕ) :
    MemLp (basisE n) 2 (volume.restrict unitDisc) := by
  change MemLp (fun z : ℂ => (Real.sqrt (((n : ℝ) + 1) / π) : ℂ) * z ^ n)
    2 (volume.restrict unitDisc)
  simpa [unitDisc] using ((mem_A21fun_iff_memLp measurableSet_ball).mp
    (polynomial_mem_A21 (Polynomial.monomial n
      (Real.sqrt (((n : ℝ) + 1) / π) : ℂ)))).2

theorem s5st_L2_inner {u v : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict unitDisc))
    (hv : MemLp v 2 (volume.restrict unitDisc)) :
    inner ℂ (hu.toLp u) (hv.toLp v) = ∫ z in unitDisc, v z * conj (u z) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with z hzu hzv
  simp [hzu, hzv, RCLike.inner_apply]

theorem s5st_L2_norm_sq {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict unitDisc)) :
    ‖hu.toLp u‖ ^ 2 = ∫ z in unitDisc, ‖u z‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), s5st_L2_inner hu hu]
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, integral_complex_ofReal]
  rfl

theorem s5st_basis_pairing (m n : ℕ) :
    (∫ z in unitDisc, basisE n z * conj (basisE m z)) =
      if m = n then (1 : ℂ) else 0 := by
  have hA (k : ℕ) : basisE k ∈ A21fun unitDisc := by
    change (fun z : ℂ => (Real.sqrt (((k : ℝ) + 1) / π) : ℂ) * z ^ k) ∈ A21fun unitDisc
    simpa using polynomial_mem_A21 (Polynomial.monomial k
      (Real.sqrt (((k : ℝ) + 1) / π) : ℂ))
  have hs (k : ℕ) (z : ℂ) :
      HasSum (fun j : ℕ => (if j = k then (1 : ℂ) else 0) * basisE j z)
        (basisE k z) := by
    convert (hasSum_ite_eq k (basisE k z)) using 1
    funext j
    split_ifs with h <;> simp [h]
  have hp := A21_basis_pairing (hA n) (hA m)
    (fun z _ => hs n z) (fun z _ => hs m z)
  rw [← hp.tsum_eq]
  simp [mul_ite, eq_comm]

-- L2
theorem s5st_basis_orthonormal :
    Orthonormal ℂ (fun n : ℕ => (s5st_basis_memLp n).toLp (basisE n)) := by
  rw [orthonormal_iff_ite]
  intro m n
  exact (s5st_L2_inner (s5st_basis_memLp m) (s5st_basis_memLp n)).trans
    (s5st_basis_pairing m n)

-- L3
theorem s5st_bessel {u : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict unitDisc))
    (s : Finset ℕ) :
    (∑ n ∈ s, ‖∫ z in unitDisc, u z * conj (basisE n z)‖ ^ 2) ≤
      ∫ z in unitDisc, ‖u z‖ ^ 2 := by
  have h := s5st_basis_orthonormal.sum_inner_products_le (x := hu.toLp u) (s := s)
  simpa only [s5st_L2_inner, s5st_L2_norm_sq] using h

-- L4: local weak Green, tested by a genuinely C1 holomorphic multiplier.
theorem s5st_weak_green {D : Set ℂ} {F Fx Fy a : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hD : IsOpen D) (hF : HasGenPartials F Fx Fy D 2)
    (ha : ContDiffOn ℝ 1 a D) (ha0 : ∀ z ∈ D, dzbar a z = 0)
    (hR : 0 ≤ R) (hsub : closedBall c R ⊆ D) :
    (∮ z in C(c, R), F z * a z) =
      2 * I * ∫ z in ball c R, genDzbar Fx Fy z * a z := by
  obtain ⟨hloc, fn, hfn, hconv, hLp⟩ := hF
  have hK : IsCompact (closedBall c R) := isCompact_closedBall c R
  have hμ : volume.restrict (ball c R) ≤ volume.restrict (closedBall c R) :=
    Measure.restrict_mono ball_subset_closedBall le_rfl
  have haL : MemLp a 2 (volume.restrict (ball c R)) :=
    (eq22w_cont_memLp ha.continuousOn hsub hK).mono_measure hμ
  have hX := (hloc _ hsub hK).1.mono_measure hμ
  have hY := (hloc _ hsub hK).2.mono_measure hμ
  have hd (n : ℕ) (v : ℂ) : MemLp (fun z => fderiv ℝ (fn n) z v) 2
      (volume.restrict (ball c R)) :=
    (eq22w_cont_memLp
      (((hfn n).continuousOn_fderiv_of_isOpen hD le_rfl).clm_apply continuousOn_const)
      hsub hK).mono_measure hμ
  have hlim (v : ℂ) (g : ℂ → ℂ)
      (hg : MemLp g 2 (volume.restrict (ball c R)))
      (hl : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z v - g z) 2
        (volume.restrict (closedBall c R))) atTop (𝓝 0)) :
      Tendsto (fun n => ∫ z in ball c R, fderiv ℝ (fn n) z v * a z) atTop
        (𝓝 (∫ z in ball c R, g z * a z)) := by
    apply sp_tendsto_integral_mul_of_L2 (fun n => hd n v) hg haL
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
      (fun _ => bot_le) (fun n => eLpNorm_mono_measure _ hμ)
  have hxlim := hlim 1 Fx hX (hLp _ hsub hK).1
  have hylim := hlim I Fy hY (hLp _ hsub hK).2
  have hint (g h : ℂ → ℂ) (hg : MemLp g 2 (volume.restrict (ball c R)))
      (hh : MemLp h 2 (volume.restrict (ball c R))) :
      (∫ z in ball c R, genDzbar g h z * a z) =
        ((∫ z in ball c R, g z * a z) + I * ∫ z in ball c R, h z * a z) / 2 := by
    have he : (fun z => genDzbar g h z * a z) =
        fun z => (g z * a z + I * (h z * a z)) / 2 := by
      funext z; simp only [genDzbar]; ring
    have hgi : IntegrableOn (fun z => g z * a z) (ball c R) := hg.integrable_mul haL
    have hhi : IntegrableOn (fun z => h z * a z) (ball c R) := hh.integrable_mul haL
    rw [he, integral_div, integral_add hgi (hhi.const_mul I), integral_const_mul]
  have hstep (n : ℕ) : (∮ z in C(c, R), fn n z * a z) =
      2 * I * (((∫ z in ball c R, fderiv ℝ (fn n) z 1 * a z) +
        I * ∫ z in ball c R, fderiv ℝ (fn n) z I * a z) / 2) := by
    rw [green_disc_dzbar_of_contDiffOn hD ((hfn n).mul ha) c hR hsub]
    congr 1
    rw [← hint _ _ (hd n 1) (hd n I)]
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    have hzD := hsub (ball_subset_closedBall hz)
    have hfnd := ((hfn n).differentiableOn one_ne_zero).differentiableAt (hD.mem_nhds hzD)
    have had := (ha.differentiableOn one_ne_zero).differentiableAt (hD.mem_nhds hzD)
    rw [dzbar_mul hfnd had, ha0 z hzD, mul_zero, zero_add]
    simp only [dzbar, genDzbar]
    ring
  have hfc : ContinuousOn F D :=
    hconv.continuousOn (Frequently.of_forall fun n => (hfn n).continuousOn)
  have haconv : TendstoLocallyUniformlyOn (fun _ : ℕ => a) a atTop D := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall fun n z hz => by simpa using hε
  have hprod := hconv.mul₀ haconv hfc ha.continuousOn
  have hS : sphere c R ⊆ D := sphere_subset_closedBall.trans hsub
  have hU : TendstoUniformlyOn (fun n z => fn n z * a z) (fun z => F z * a z)
      atTop (sphere c R) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_sphere c R)).mp (hprod.mono hS)
  have hboundary := hU.tendsto_circleIntegral_of_continuousOn hR
    (Eventually.of_forall fun n => ((hfn n).continuousOn.mul ha.continuousOn).mono hS)
  have harea := ((hxlim.add (hylim.const_mul I)).div_const (2 : ℂ)).const_mul (2 * I)
  have hboundary' := hboundary.congr (fun n => hstep n)
  rw [hint Fx Fy hX hY]
  exact tendsto_nhds_unique hboundary' harea

/-- Radial continuity uses only continuity on the closed disk. -/
theorem s5st_circle_limit {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {r : ℕ → ℝ}
    (hR : 0 ≤ R) (hF : ContinuousOn F (closedBall c R))
    (hr : ∀ n, 0 ≤ r n ∧ r n ≤ R) (ht : Tendsto r atTop (𝓝 R)) :
    Tendsto (fun n => ∮ z in C(c, r n), F z) atTop (𝓝 (∮ z in C(c, R), F z)) := by
  have hmem (s : ℝ) (hs : 0 ≤ s) (hsR : s ≤ R) (θ : ℝ) :
      circleMap c s θ ∈ closedBall c R := by
    have h := circleMap_mem_sphere' c s θ
    rw [mem_sphere, abs_of_nonneg hs] at h
    rw [mem_closedBall, h]
    exact hsR
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hF
  have hcont (s : ℝ) (hs : 0 ≤ s) (hsR : s ≤ R) :
      Continuous (fun θ : ℝ => deriv (circleMap c s) θ • F (circleMap c s θ)) := by
    have h1 : Continuous (fun θ : ℝ => deriv (circleMap c s) θ) := by
      simp only [deriv_circleMap, circleMap]
      fun_prop
    exact h1.smul (hF.comp_continuous (continuous_circleMap c s) (hmem s hs hsR))
  simp only [circleIntegral]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => R * M)
    (Eventually.of_forall fun n => (hcont (r n) (hr n).1 (hr n).2).aestronglyMeasurable)
  · refine Eventually.of_forall fun n => ?_
    filter_upwards with θ hθ
    rw [norm_smul, deriv_circleMap]
    have he : ‖circleMap 0 (r n) θ * I‖ = r n := by
      simp [circleMap, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg (hr n).1]
    rw [he]
    have hb := hM _ (hmem (r n) (hr n).1 (hr n).2 θ)
    have hM0 := (norm_nonneg _).trans hb
    exact (mul_le_mul_of_nonneg_left hb (hr n).1).trans
      (mul_le_mul_of_nonneg_right (hr n).2 hM0)
  · exact _root_.intervalIntegrable_const
  · filter_upwards with θ hθ
    have hctr : Continuous (fun s : ℝ => circleMap c s θ) := by
      simp only [circleMap]; fun_prop
    have hfc : Tendsto (fun n => F (circleMap c (r n) θ)) atTop
        (𝓝 (F (circleMap c R θ))) :=
      (hF _ (hmem R hR le_rfl θ)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨(hctr.tendsto R).comp ht,
          Eventually.of_forall fun n => hmem (r n) (hr n).1 (hr n).2 θ⟩)
    have hdc : Tendsto (fun n => deriv (circleMap c (r n)) θ) atTop
        (𝓝 (deriv (circleMap c R) θ)) := by
      have hc := (Complex.continuous_ofReal.tendsto R).comp ht
      simp only [deriv_circleMap, circleMap, zero_add]
      exact (hc.mul_const _).mul_const _
    exact hdc.smul hfc

/-- Weak Green up to a continuous boundary, with an explicitly integrable area term. -/
theorem s5st_weak_green_boundary {F Fx Fy a : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hF : HasGenPartials F Fx Fy (ball c R) 2)
    (hFc : ContinuousOn F (closedBall c R)) (ha : ContDiff ℝ 1 a)
    (ha0 : ∀ z ∈ ball c R, dzbar a z = 0)
    (hint : IntegrableOn (fun z => genDzbar Fx Fy z * a z) (ball c R)) :
    (∮ z in C(c, R), F z * a z) =
      2 * I * ∫ z in ball c R, genDzbar Fx Fy z * a z := by
  let u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hu0 (n : ℕ) : 0 < u n := by dsimp [u]; positivity
  have hu1 (n : ℕ) : u n ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by positivity)]
    simp only [le_add_iff_nonneg_left]
    positivity
  have hut : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let r : ℕ → ℝ := fun n => R * (1 - u n)
  have hr0 (n : ℕ) : 0 ≤ r n := by dsimp [r]; have := hu1 n; positivity
  have hrR (n : ℕ) : r n < R := by dsimp [r]; nlinarith [hu0 n]
  have hrt : Tendsto r atTop (𝓝 R) := by
    simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.sub hut) :
      Tendsto r atTop (𝓝 (R * (1 - 0))))
  have hrmono : Monotone r := by
    intro m n hmn
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    have hun : u n ≤ u m := one_div_le_one_div_of_le (by positivity) hmn'
    dsimp [r]
    nlinarith [hR]
  have hstep (n : ℕ) : (∮ z in C(c, r n), F z * a z) =
      2 * I * ∫ z in ball c (r n), genDzbar Fx Fy z * a z :=
    s5st_weak_green isOpen_ball hF ha.contDiffOn ha0 (hr0 n) (closedBall_subset_ball (hrR n))
  have hunion : (⋃ n, ball c (r n)) = ball c R := by
    apply Subset.antisymm
    · exact iUnion_subset fun n => ball_subset_ball (hrR n).le
    · intro z hz
      obtain ⟨n, hn⟩ := (hrt.eventually (eventually_gt_nhds (mem_ball.mp hz))).exists
      exact mem_iUnion.mpr ⟨n, mem_ball.mpr hn⟩
  have harea : Tendsto (fun n => ∫ z in ball c (r n), genDzbar Fx Fy z * a z)
      atTop (𝓝 (∫ z in ball c R, genDzbar Fx Fy z * a z)) := by
    have hi : IntegrableOn (fun z => genDzbar Fx Fy z * a z) (⋃ n, ball c (r n)) := by
      rwa [hunion]
    have h := tendsto_setIntegral_of_monotone (fun n => measurableSet_ball)
      (fun m n hmn => ball_subset_ball (hrmono hmn)) hi
    rwa [hunion] at h
  have hboundary := s5st_circle_limit hR.le (hFc.mul ha.continuous.continuousOn)
    (fun n => ⟨hr0 n, (hrR n).le⟩) hrt
  exact tendsto_nhds_unique (hboundary.congr hstep) (harea.const_mul (2 * I))

theorem s5st_conj_hasGen {D : Set ℂ} {F Fx Fy : ℂ → ℂ}
    (hD : IsOpen D) (hF : HasGenPartials F Fx Fy D 2) :
    HasGenPartials (fun z => conj (F z)) (fun z => conj (Fx z))
      (fun z => conj (Fy z)) D 2 := by
  let L : ℂ →L[ℝ] ℂ := Complex.conjCLE
  have h := eq22w_hasGen_comp hD hF L.contDiff
    (B := ‖L‖) (fun u => by rw [L.fderiv])
  simp only [ContinuousLinearMap.fderiv] at h
  exact h

theorem s5st_wirtinger_memLp {D : Set ℂ} {Fx Fy : ℂ → ℂ}
    (hx : MemLp Fx 2 (volume.restrict D)) (hy : MemLp Fy 2 (volume.restrict D)) :
    MemLp (genDz Fx Fy) 2 (volume.restrict D) ∧
      MemLp (genDzbar Fx Fy) 2 (volume.restrict D) := by
  constructor
  · change MemLp (fun z => (Fx z - I * Fy z) / 2) 2 (volume.restrict D)
    simpa only [Pi.sub_apply, div_eq_mul_inv] using (hx.sub (hy.const_mul I)).mul_const (2 : ℂ)⁻¹
  · change MemLp (fun z => (Fx z + I * Fy z) / 2) 2 (volume.restrict D)
    simpa only [Pi.add_apply, div_eq_mul_inv] using (hx.add (hy.const_mul I)).mul_const (2 : ℂ)⁻¹

theorem s5st_bessel_conj {u : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict unitDisc))
    (s : Finset ℕ) :
    (∑ n ∈ s, ‖∫ z in unitDisc, u z * basisE n z‖ ^ 2) ≤
      ∫ z in unitDisc, ‖u z‖ ^ 2 := by
  have hc : MemLp (fun z => conj (u z)) 2 (volume.restrict unitDisc) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_memLp' hu
  have h := s5st_bessel hc s
  have he (n : ℕ) : (∫ z in unitDisc, conj (u z) * conj (basisE n z)) =
      conj (∫ z in unitDisc, u z * basisE n z) := by
    rw [← integral_conj]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => (map_mul (starRingEnd ℂ) _ _).symm
  simpa only [he, norm_conj] using h

theorem s5st_circle_monomial (F : ℂ → ℂ) (m : ℕ) :
    (∮ z in C(0, 1), F z * z ^ m) =
      2 * π * I * fourierCoeff (fun θ => F (exp (θ * I))) (-(m + 1 : ℤ)) := by
  have he (θ : ℝ) : exp (-((-(m + 1 : ℤ)) * θ * I)) = exp (θ * I) ^ (m + 1) := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold circleIntegral fourierCoeff
  simp only [Int.cast_neg]
  simp_rw [he]
  have hf : (fun θ : ℝ => deriv (circleMap 0 1) θ • (F (circleMap 0 1 θ) * circleMap 0 1 θ ^ m)) =
      fun θ : ℝ => I * (F (exp (θ * I)) * exp (θ * I) ^ (m + 1)) := by
    funext θ
    simp only [deriv_circleMap, circleMap, zero_add, Complex.ofReal_one, one_mul, smul_eq_mul,
      pow_succ]
    ring
  rw [hf, intervalIntegral.integral_const_mul]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

theorem s5st_negative_moment {F Fx Fy : ℂ → ℂ}
    (hF : HasGenPartials F Fx Fy unitDisc 2)
    (hFc : ContinuousOn F (closedBall 0 1))
    (hx : MemLp Fx 2 (volume.restrict unitDisc))
    (hy : MemLp Fy 2 (volume.restrict unitDisc)) (m : ℕ) :
    (∫ z in unitDisc, genDzbar Fx Fy z * z ^ m) =
      π * fourierCoeff (fun θ => F (exp (θ * I))) (-(m + 1 : ℤ)) := by
  have hm : MemLp (fun z : ℂ => z ^ m) 2 (volume.restrict unitDisc) := by
    simpa [unitDisc] using ((mem_A21fun_iff_memLp measurableSet_ball).mp
      (polynomial_mem_A21 (Polynomial.X ^ m))).2
  have hi : IntegrableOn (fun z => genDzbar Fx Fy z * z ^ m) unitDisc :=
    (s5st_wirtinger_memLp hx hy).2.integrable_mul hm
  have h := s5st_weak_green_boundary (c := 0) (R := 1) zero_lt_one hF hFc
    (contDiff_id.pow m) (fun z _ => (cauchyRiemann_iff.mp (differentiableAt_id.pow m)).2) hi
  simp only [id_eq] at h
  rw [s5st_circle_monomial] at h
  apply mul_left_cancel₀ (show (2 : ℂ) * I ≠ 0 by simp)
  calc
    2 * I * (∫ z in unitDisc, genDzbar Fx Fy z * z ^ m) =
        2 * π * I * fourierCoeff (fun θ => F (exp (θ * I))) (-(m + 1 : ℤ)) := h.symm
    _ = _ := by ring

theorem s5st_negative_bound {F Fx Fy : ℂ → ℂ}
    (hF : HasGenPartials F Fx Fy unitDisc 2)
    (hFc : ContinuousOn F (closedBall 0 1))
    (hx : MemLp Fx 2 (volume.restrict unitDisc))
    (hy : MemLp Fy 2 (volume.restrict unitDisc)) (s : Finset ℕ) :
    (∑ n ∈ s, ((n : ℝ) + 1) * ‖circleCoeff F (-(n + 1 : ℤ))‖ ^ 2) ≤
      (∫ z in unitDisc, ‖genDzbar Fx Fy z‖ ^ 2) / π := by
  have h := s5st_bessel_conj (s5st_wirtinger_memLp hx hy).2 s
  have hm (n : ℕ) : (∫ z in unitDisc, genDzbar Fx Fy z * basisE n z) =
      (Real.sqrt (((n : ℝ) + 1) / π) : ℂ) * π * circleCoeff F (-(n + 1 : ℤ)) := by
    calc
      _ = (Real.sqrt (((n : ℝ) + 1) / π) : ℂ) *
          ∫ z in unitDisc, genDzbar Fx Fy z * z ^ n := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by simp only [basisE]; ring
      _ = _ := by rw [s5st_negative_moment hF hFc hx hy]; simp only [circleCoeff]; ring
  have hn (n : ℕ) : ‖∫ z in unitDisc, genDzbar Fx Fy z * basisE n z‖ ^ 2 =
      π * (((n : ℝ) + 1) * ‖circleCoeff F (-(n + 1 : ℤ))‖ ^ 2) := by
    rw [hm]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos Real.pi_pos, mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ ((n : ℝ) + 1) / π)]
    field_simp
  simp_rw [hn] at h
  rw [← Finset.mul_sum] at h
  exact (le_div_iff₀ Real.pi_pos).mpr (by simpa only [mul_comm] using h)

theorem s5st_positive_bound {F Fx Fy : ℂ → ℂ}
    (hF : HasGenPartials F Fx Fy unitDisc 2)
    (hFc : ContinuousOn F (closedBall 0 1))
    (hx : MemLp Fx 2 (volume.restrict unitDisc))
    (hy : MemLp Fy 2 (volume.restrict unitDisc)) (s : Finset ℕ) :
    (∑ n ∈ s, ((n : ℝ) + 1) * ‖circleCoeff F (n + 1 : ℤ)‖ ^ 2) ≤
      (∫ z in unitDisc, ‖genDz Fx Fy z‖ ^ 2) / π := by
  have hxc : MemLp (fun z => conj (Fx z)) 2 (volume.restrict unitDisc) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_memLp' hx
  have hyc : MemLp (fun z => conj (Fy z)) 2 (volume.restrict unitDisc) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_memLp' hy
  have h := s5st_negative_bound (s5st_conj_hasGen isOpen_ball hF)
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).continuous.comp_continuousOn hFc) hxc hyc s
  have he (n : ℕ) : circleCoeff (fun z => conj (F z)) (-(n + 1 : ℤ)) =
      conj (circleCoeff F (n + 1 : ℤ)) := by
    simpa only [circleCoeff, neg_neg] using
      ts2_fc_conj (fun θ => F (exp (θ * I))) (-(n + 1 : ℤ))
  have hg (z : ℂ) : genDzbar (fun z => conj (Fx z)) (fun z => conj (Fy z)) z =
      conj (genDz Fx Fy z) := by
    simp only [genDzbar, genDz, map_div₀, map_sub, map_mul, map_ofNat, conj_I]
    ring
  simpa only [he, hg, norm_conj] using h

theorem s5st_wirtinger_energy {D : Set ℂ} {Fx Fy : ℂ → ℂ}
    (hx : MemLp Fx 2 (volume.restrict D)) (hy : MemLp Fy 2 (volume.restrict D)) :
    (∫ z in D, ‖genDz Fx Fy z‖ ^ 2) + (∫ z in D, ‖genDzbar Fx Fy z‖ ^ 2) =
      (∫ z in D, ‖Fx z‖ ^ 2 + ‖Fy z‖ ^ 2) / 2 := by
  have hd := (s5st_wirtinger_memLp hx hy).1.integrable_norm_pow (by decide : 2 ≠ 0)
  have hb := (s5st_wirtinger_memLp hx hy).2.integrable_norm_pow (by decide : 2 ≠ 0)
  rw [← integral_add hd hb]
  have he (z : ℂ) : ‖genDz Fx Fy z‖ ^ 2 + ‖genDzbar Fx Fy z‖ ^ 2 =
      (‖Fx z‖ ^ 2 + ‖Fy z‖ ^ 2) / 2 := by
    simp only [genDz, genDzbar, norm_div, norm_ofNat, div_pow, Complex.sq_norm,
      Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, I_re, I_im]
    ring
  simp_rw [he]
  exact integral_div (2 : ℝ) _

/-- Continuous W1,2 traces have genuine H1/2 Fourier energy, with the sharp
Dirichlet upper bound. The supplied partial derivatives are L2 on the whole disk. -/
theorem s5st_trace_energy {F Fx Fy : ℂ → ℂ}
    (hF : HasGenPartials F Fx Fy unitDisc 2)
    (hFc : ContinuousOn F (closedBall 0 1))
    (hx : MemLp Fx 2 (volume.restrict unitDisc))
    (hy : MemLp Fy 2 (volume.restrict unitDisc)) :
    F ∈ HC ∧ (∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff F n‖ ^ 2) ≤
      (∫ z in unitDisc, ‖Fx z‖ ^ 2 + ‖Fy z‖ ^ 2) / (2 * π) := by
  let e : ℤ → ℝ := fun n => |(n : ℝ)| * ‖circleCoeff F n‖ ^ 2
  have hep (n : ℕ) : e (n + 1) = ((n : ℝ) + 1) * ‖circleCoeff F (n + 1 : ℤ)‖ ^ 2 := by
    dsimp [e]
    rw [Int.cast_add, Int.cast_natCast, Int.cast_one, abs_of_nonneg (by positivity)]
  have hem (n : ℕ) : e (-(n + 1)) = ((n : ℝ) + 1) * ‖circleCoeff F (-(n + 1 : ℤ))‖ ^ 2 := by
    dsimp [e]
    rw [Int.cast_neg, abs_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_of_nonneg (by positivity)]
  have hp : Summable (fun n : ℕ => e (n + 1)) := by
    apply summable_of_sum_le (fun n => by dsimp [e]; positivity)
    intro s
    simpa only [hep] using s5st_positive_bound hF hFc hx hy s
  have hm : Summable (fun n : ℕ => e (-(n + 1))) := by
    apply summable_of_sum_le (fun n => by dsimp [e]; positivity)
    intro s
    simpa only [hem] using s5st_negative_bound hF hFc hx hy s
  have hs : Summable e := hp.of_add_one_of_neg_add_one hm
  have hc : Continuous (fun θ : ℝ => F (exp (θ * I))) := by
    apply hFc.comp_continuous (by fun_prop)
    intro θ
    rw [mem_closedBall, dist_zero_right]
    simp [Complex.norm_exp]
  refine ⟨⟨hc.intervalIntegrable _ _, hs⟩, ?_⟩
  have hbp : (∑' n : ℕ, e (n + 1)) ≤ (∫ z in unitDisc, ‖genDz Fx Fy z‖ ^ 2) / π :=
    hp.tsum_le_of_sum_le (fun s => by simpa only [hep] using s5st_positive_bound hF hFc hx hy s)
  have hbm : (∑' n : ℕ, e (-(n + 1))) ≤ (∫ z in unitDisc, ‖genDzbar Fx Fy z‖ ^ 2) / π :=
    hm.tsum_le_of_sum_le (fun s => by simpa only [hem] using s5st_negative_bound hF hFc hx hy s)
  have he0 : e 0 = 0 := by simp [e]
  change (∑' n : ℤ, e n) ≤ _
  rw [tsum_of_add_one_of_neg_add_one hp hm, he0, add_zero]
  have h := add_le_add hbp hbm
  rwa [← add_div, s5st_wirtinger_energy hx hy, div_div] at h

end TakhtajanTeo.Ch2
