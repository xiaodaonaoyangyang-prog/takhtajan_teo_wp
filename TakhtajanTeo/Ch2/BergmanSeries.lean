import TakhtajanTeo.Ch2.S2_Grunsky

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

def bergmanTaylorPoly (c : ℕ → ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range N, Polynomial.monomial n (c n)

theorem bergmanTaylorPoly_eval (c : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (bergmanTaylorPoly c N).eval z = ∑ n ∈ Finset.range N, c n * z ^ n := by
  simp only [bergmanTaylorPoly, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem bergmanTaylorPoly_coeff (c : ℕ → ℂ) (N n : ℕ) :
    (bergmanTaylorPoly c N).coeff n = if n < N then c n else 0 := by
  simp [bergmanTaylorPoly, Polynomial.coeff_monomial]

/-- The existing polynomial Parseval formula applied to Taylor partial sums. -/
theorem bergmanTaylorPoly_area (c : ℕ → ℂ) (N : ℕ) :
    (∫ z in unitDisc, ‖(bergmanTaylorPoly c N).eval z‖ ^ 2) =
      π * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / ((n : ℝ)+1) := by
  rw [polynomial_A21_area]
  congr 1
  have hsub : (bergmanTaylorPoly c N).support ⊆ Finset.range N := by
    intro n hn
    by_contra h
    have hnz := Polynomial.mem_support_iff.mp hn
    exact hnz (by simp [bergmanTaylorPoly_coeff, Finset.mem_range.mpr.mt h])
  calc
    _ = ∑ n ∈ Finset.range N, ‖(bergmanTaylorPoly c N).coeff n‖ ^ 2 / ((n : ℝ)+1) := by
      apply Finset.sum_subset hsub
      intro n _ hn
      have hc : (bergmanTaylorPoly c N).coeff n = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hn
      simp [hc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [bergmanTaylorPoly_coeff, if_pos (Finset.mem_range.mp hn)]

/-- Taylor partial sums of an inward dilation converge uniformly on the closed unit disk. -/
theorem bergmanTaylorPoly_dilate_uniform {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (f z))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    TendstoUniformlyOn (fun N z => (bergmanTaylorPoly (fun n => c n * (r : ℂ)^n) N).eval z)
      (fun z => f ((r : ℂ)*z)) atTop (closedBall 0 1) := by
  have hrD : (r : ℂ) ∈ unitDisc := by simpa [unitDisc, abs_of_pos hr0] using hr1
  have hbound : Summable (fun n => ‖c n‖ * r ^ n) := by
    simpa [norm_mul, norm_pow, abs_of_pos hr0] using (hs (r : ℂ) hrD).summable.norm
  have hU := tendstoUniformlyOn_tsum_nat hbound (s := closedBall (0 : ℂ) 1)
    (f := fun n z => (c n * (r : ℂ)^n)*z^n) (by
      intro n z hz
      have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg z) hz1))
  have he : ∀ z ∈ closedBall (0 : ℂ) 1,
      (∑' n, (c n * (r : ℂ)^n)*z^n) = f ((r : ℂ)*z) := by
    intro z hz
    have hzD : (r : ℂ)*z ∈ unitDisc := by
      apply mem_ball_zero_iff.mpr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      exact (mul_le_of_le_one_right hr0.le (mem_closedBall_zero_iff.mp hz)).trans_lt hr1
    simpa [mul_pow, mul_assoc] using (hs _ hzD).tsum_eq
  simpa only [bergmanTaylorPoly_eval] using hU.congr_right he

/-- Parseval for an inward dilation, obtained from the existing uniform-integral theorem. -/
theorem bergman_dilate_hasSum {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (f z))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasSum (fun n => π * ‖c n‖ ^ 2 * r ^ (2*n) / ((n : ℝ)+1))
      (∫ z in unitDisc, ‖f ((r : ℂ)*z)‖ ^ 2) := by
  have hf := differentiableOn_of_powerSeries hs
  obtain ⟨R,hR,hfd⟩ := holomorphic_inward_dilate hf hr0 hr1
  have hlim := A21_polynomial_integral_tendsto
    (fun N => bergmanTaylorPoly (fun n => c n*(r : ℂ)^n) N)
    (hfd.continuousOn.mono (closedBall_subset_closedBall hR.le))
    (bergmanTaylorPoly_dilate_uniform hs hr0 hr1)
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity) _).mpr
  convert hlim using 1
  funext N
  rw [bergmanTaylorPoly_area, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, mul_pow]
  rw [← pow_mul]
  ring

/-- Every finite Bergman coefficient mass is bounded by the actual area mass. -/
theorem bergman_coeff_partial_bound {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hf : f ∈ A21fun unitDisc)
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (f z)) (N : ℕ) :
    (∑ n ∈ Finset.range N, π * ‖c n‖ ^ 2 / ((n : ℝ)+1)) ≤
      ∫ z in unitDisc, ‖f z‖ ^ 2 := by
  have hL : Tendsto (fun r : ℝ => ∑ n ∈ Finset.range N,
      π * ‖c n‖ ^ 2 * r ^ (2*n) / ((n : ℝ)+1)) (𝓝[<] 1)
      (𝓝 (∑ n ∈ Finset.range N, π * ‖c n‖ ^ 2 / ((n : ℝ)+1))) := by
    have hc : Continuous (fun r : ℝ => ∑ n ∈ Finset.range N,
        π * ‖c n‖ ^ 2 * r ^ (2*n) / ((n : ℝ)+1)) := by fun_prop
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun r : ℝ => (∫ z in unitDisc, ‖f z‖ ^ 2) / r^2) (𝓝[<] 1)
      (𝓝 (∫ z in unitDisc, ‖f z‖ ^ 2)) := by
    have hc : ContinuousAt (fun r : ℝ => (∫ z in unitDisc, ‖f z‖ ^ 2) / r^2) 1 :=
      continuousAt_const.div (continuousAt_id.pow 2) (by norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hr0 : 0 < r := hr.1
  have hsum := bergman_dilate_hasSum hs hr.1 hr.2
  have hb := hsum.summable.sum_le_tsum (Finset.range N) (fun n _ => by positivity)
  rw [hsum.tsum_eq] at hb
  exact hb.trans (A21_dilate_mass_bound hf hr.1 hr.2)

theorem bergman_coeff_summable {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hf : f ∈ A21fun unitDisc)
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (f z)) :
    Summable (fun n => π * ‖c n‖ ^ 2 / ((n : ℝ)+1)) :=
  summable_of_sum_range_le (fun n => by positivity) (bergman_coeff_partial_bound hf hs)

/-- Fatou's lemma passes finite polynomial Parseval to an arbitrary convergent series. -/
theorem bergman_series_lintegral_le {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (f z))
    (hc : Summable (fun n => π * ‖c n‖ ^ 2 / ((n : ℝ)+1))) :
    (∫⁻ z in unitDisc, ENNReal.ofReal (‖f z‖ ^ 2)) ≤
      ENNReal.ofReal (∑' n, π * ‖c n‖ ^ 2 / ((n : ℝ)+1)) := by
  let P := bergmanTaylorPoly c
  let F : ℕ → ℂ → ℝ≥0∞ := fun N z => ENNReal.ofReal (‖(P N).eval z‖ ^ 2)
  have hm (N : ℕ) : Measurable (F N) := by dsimp [F]; fun_prop
  have ht (z : ℂ) (hz : z ∈ unitDisc) : Tendsto (fun N => F N z) atTop
      (𝓝 (ENNReal.ofReal (‖f z‖ ^ 2))) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    have hp : Tendsto (fun N => (P N).eval z) atTop (𝓝 (f z)) := by
      simpa only [P, bergmanTaylorPoly_eval] using (hs z hz).tendsto_sum_nat
    exact hp.norm.pow 2
  have hI (N : ℕ) : (∫⁻ z in unitDisc, F N z) =
      ENNReal.ofReal (∑ n ∈ Finset.range N, π * ‖c n‖ ^ 2 / ((n : ℝ)+1)) := by
    dsimp only [F]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (a21_integrable_sq (show MeasurableSet unitDisc from measurableSet_ball) (polynomial_mem_A21 (P N)))
      (Eventually.of_forall fun z => sq_nonneg ‖(P N).eval z‖)]
    simp only [P, bergmanTaylorPoly_area, Finset.mul_sum, mul_div_assoc]
  have hlim : Tendsto (fun N => ∫⁻ z in unitDisc, F N z) atTop
      (𝓝 (ENNReal.ofReal (∑' n, π * ‖c n‖ ^ 2 / ((n : ℝ)+1)))) := by
    simp only [hI]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc.hasSum.tendsto_sum_nat
  calc
    _ = ∫⁻ z in unitDisc, liminf (fun N => F N z) atTop := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with z hz
      exact (ht z hz).liminf_eq.symm
    _ ≤ liminf (fun N => ∫⁻ z in unitDisc, F N z) atTop := lintegral_liminf_le hm
    _ = _ := hlim.liminf_eq

/-- Area Parseval for every actual A21 power series on the whole open disk. -/
theorem A21_area_parseval {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hf : f ∈ A21fun unitDisc)
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (f z)) :
    HasSum (fun n => π * ‖c n‖ ^ 2 / ((n : ℝ)+1)) (∫ z in unitDisc, ‖f z‖ ^ 2) := by
  have hc := bergman_coeff_summable hf hs
  have hle : (∑' n, π * ‖c n‖ ^ 2 / ((n : ℝ)+1)) ≤ ∫ z in unitDisc, ‖f z‖ ^ 2 :=
    Real.tsum_le_of_sum_range_le (fun n => by positivity) (bergman_coeff_partial_bound hf hs)
  have hge := bergman_series_lintegral_le hs hc
  rw [← ofReal_integral_eq_lintegral_ofReal
    (a21_integrable_sq (show MeasurableSet unitDisc from measurableSet_ball) hf)
    (Eventually.of_forall fun z => sq_nonneg ‖f z‖)] at hge
  have hnonneg : 0 ≤ ∑' n, π * ‖c n‖ ^ 2 / ((n : ℝ)+1) := tsum_nonneg (fun n => by positivity)
  have heq := le_antisymm hle ((ENNReal.ofReal_le_ofReal_iff hnonneg).mp hge)
  exact heq ▸ hc.hasSum

/-- Summable Bergman coefficient mass implies actual area L2 membership. -/
theorem bergman_mem_A21_of_coeff {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (f z))
    (hc : Summable (fun n => π * ‖c n‖ ^ 2 / ((n : ℝ)+1))) : f ∈ A21fun unitDisc := by
  have hd := differentiableOn_of_powerSeries hs
  have hm : AEStronglyMeasurable f (volume.restrict unitDisc) :=
    hd.continuousOn.aestronglyMeasurable (show MeasurableSet unitDisc from measurableSet_ball)
  have hi : IntegrableOn (fun z => ‖f z‖ ^ 2) unitDisc := by
    refine ⟨hm.norm.pow 2, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg ‖f z‖)).mpr
    exact lt_of_le_of_lt (bergman_series_lintegral_le hs hc) ENNReal.ofReal_lt_top
  exact (mem_A21fun_iff_memLp (show MeasurableSet unitDisc from measurableSet_ball)).mpr
    ⟨hd, (memLp_two_iff_integrable_sq_norm hm).mpr hi⟩

/-- Every A21 function has actual square-summable coefficients in the normalized
Bergman basis, with the coefficient mass equal to its area mass. -/
theorem A21_exists_ell2_expansion {f : ℂ → ℂ} (hf : f ∈ A21fun unitDisc) :
    ∃ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) ∧
      (∀ z ∈ unitDisc, HasSum (fun n => x n * basisE n z) (f z)) ∧
      HasSum (fun n => ‖x n‖ ^ 2) (∫ z in unitDisc, ‖f z‖ ^ 2) := by
  let c : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0
  have hs : ∀ z ∈ unitDisc, HasSum (fun n => c n*z^n) (f z) := by
    intro z hz
    simpa only [c, smul_eq_mul, sub_zero, mul_assoc, mul_comm, mul_left_comm] using
      Complex.hasSum_taylorSeries_on_ball hf.1 hz
  let x : ℕ → ℂ := fun n => c n / (Real.sqrt (((n : ℝ)+1)/π) : ℂ)
  have hnorm (n : ℕ) : ‖x n‖^2 = π * ‖c n‖^2 / ((n : ℝ)+1) := by
    simp only [x, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      div_pow, Real.sq_sqrt (by positivity : 0 ≤ ((n : ℝ)+1)/π)]
    field_simp
  have hmass := (A21_area_parseval hf hs).congr_fun (fun n => hnorm n)
  refine ⟨x, hmass.summable, ?_, hmass⟩
  intro z hz
  apply (hs z hz).congr_fun
  intro n
  have hsqrt : (Real.sqrt (((n : ℝ)+1)/π) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  dsimp [x, basisE]
  field_simp

theorem A21_ell2_norm_sq {f : ℂ → ℂ} (hf : f ∈ A21fun unitDisc)
    {x : ℕ → ℂ} (hx : HasSum (fun n => ‖x n‖ ^ 2) (∫ z in unitDisc, ‖f z‖ ^ 2)) :
    normA21 unitDisc f ^ 2 = ENNReal.ofReal (∑' n, ‖x n‖ ^ 2) := by
  rw [a21_norm_sq_eq_integral (show MeasurableSet unitDisc from measurableSet_ball) hf, hx.tsum_eq]

theorem basisE_norm_sq (n : ℕ) (z : ℂ) :
    ‖basisE n z‖ ^ 2 = (((n : ℝ)+1)/π) * (‖z‖^2)^n := by
  simp only [basisE, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ ((n : ℝ)+1)/π)]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]

theorem basisE_sq_summable {z : ℂ} (hz : z ∈ unitDisc) :
    Summable (fun n => ‖basisE n z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hq : ‖‖z‖^2‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; nlinarith [norm_nonneg z]
  have hs := ((summable_pow_mul_geometric_of_norm_lt_one 1 hq).add
    (summable_geometric_of_norm_lt_one hq)).div_const π
  simpa only [basisE_norm_sq, pow_one, add_mul, one_mul, div_mul_eq_mul_div] using hs

/-- Square-summable scalar sequences pair absolutely; used for evaluation and kernel rows. -/
theorem bergman_pair_summable {x y : ℕ → ℂ}
    (hx : Summable (fun n => ‖x n‖ ^ 2)) (hy : Summable (fun n => ‖y n‖ ^ 2)) :
    Summable (fun n => ‖x n * y n‖) := by
  apply (((hx.add hy).div_const 2).of_nonneg_of_le (fun n => norm_nonneg _))
  intro n
  rw [norm_mul]
  nlinarith [sq_nonneg (‖x n‖-‖y n‖)]

/-- Every square-summable sequence defines a holomorphic Bergman function, with
exactly its coefficient norm. This is the converse to `A21_exists_ell2_expansion`. -/
theorem bergman_ell2_series {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    (fun z => ∑' n, x n * basisE n z) ∈ A21fun unitDisc ∧
      HasSum (fun n => ‖x n‖ ^ 2) (∫ z in unitDisc, ‖∑' n, x n * basisE n z‖ ^ 2) := by
  let c : ℕ → ℂ := fun n => x n * (Real.sqrt (((n : ℝ)+1)/π) : ℂ)
  have hcoef (n : ℕ) : π * ‖c n‖^2 / ((n : ℝ)+1) = ‖x n‖^2 := by
    simp only [c, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (by positivity : 0 ≤ ((n : ℝ)+1)/π)]
    field_simp
  have hs : ∀ z ∈ unitDisc, HasSum (fun n => c n*z^n) (∑' n, x n*basisE n z) := by
    intro z hz
    simpa only [c, basisE, mul_assoc] using
      (bergman_pair_summable hx (basisE_sq_summable hz)).of_norm.hasSum
  have hc : Summable (fun n => π * ‖c n‖^2 / ((n : ℝ)+1)) := by simpa only [hcoef] using hx
  have hf := bergman_mem_A21_of_coeff hs hc
  exact ⟨hf, by simpa only [hcoef] using A21_area_parseval hf hs⟩

theorem A21_basis_parseval {f : ℂ → ℂ} {x : ℕ → ℂ} (hf : f ∈ A21fun unitDisc)
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => x n*basisE n z) (f z)) :
    HasSum (fun n => ‖x n‖^2) (∫ z in unitDisc, ‖f z‖^2) := by
  let c : ℕ → ℂ := fun n => x n * (Real.sqrt (((n : ℝ)+1)/π) : ℂ)
  have hc : ∀ z ∈ unitDisc, HasSum (fun n => c n*z^n) (f z) := by
    intro z hz
    simpa only [c, basisE, mul_assoc] using hs z hz
  apply (A21_area_parseval hf hc).congr_fun
  intro n
  simp only [c, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (by positivity : 0 ≤ ((n : ℝ)+1)/π)]
  field_simp

theorem bergman_polarization (u v : ℂ) : u * conj v =
    (((‖u+v‖^2 : ℝ) : ℂ) - ((‖u-v‖^2 : ℝ) : ℂ) +
      (((‖u+I*v‖^2 : ℝ) : ℂ) - ((‖u-I*v‖^2 : ℝ) : ℂ))*I) / 4 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  apply Complex.ext <;> simp <;> ring

/-- The Bergman integral pairing equals the genuine summable coefficient pairing.
Polarization of area Parseval avoids an unsupported exchange of integrals and series. -/
theorem A21_basis_pairing {f g : ℂ → ℂ} {x y : ℕ → ℂ}
    (hf : f ∈ A21fun unitDisc) (hg : g ∈ A21fun unitDisc)
    (hx : ∀ z ∈ unitDisc, HasSum (fun n => x n*basisE n z) (f z))
    (hy : ∀ z ∈ unitDisc, HasSum (fun n => y n*basisE n z) (g z)) :
    HasSum (fun n => x n * conj (y n)) (∫ z in unitDisc, f z * conj (g z)) := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have ha (a : ℂ) : (fun z => f z+a*g z) ∈ A21fun unitDisc :=
    a21_add hD hf (a21_const_mul hD hg a)
  have hs (a : ℂ) : HasSum (fun n => ‖x n+a*y n‖^2)
      (∫ z in unitDisc, ‖f z+a*g z‖^2) := by
    apply A21_basis_parseval (ha a)
    intro z hz
    exact ((hx z hz).add ((hy z hz).mul_left a)).congr_fun (fun n => by ring)
  have hsc (a : ℂ) := Complex.hasSum_ofReal.mpr (hs a)
  have hi (a : ℂ) : IntegrableOn (fun z => ((‖f z+a*g z‖^2 : ℝ) : ℂ)) unitDisc :=
    (a21_integrable_sq hD (ha a)).ofReal
  have hsum := (((hsc 1).sub (hsc (-1))).add (((hsc I).sub (hsc (-I))).mul_right I)).div_const 4
  have hiEq : (∫ z in unitDisc, f z * conj (g z)) =
      (((∫ z in unitDisc, ‖f z+1*g z‖^2 : ℝ) : ℂ) -
        ((∫ z in unitDisc, ‖f z+(-1)*g z‖^2 : ℝ) : ℂ) +
        (((∫ z in unitDisc, ‖f z+I*g z‖^2 : ℝ) : ℂ) -
          ((∫ z in unitDisc, ‖f z+(-I)*g z‖^2 : ℝ) : ℂ))*I) / 4 := by
    let Q : ℂ → ℂ → ℂ := fun a z => ((‖f z+a*g z‖^2 : ℝ) : ℂ)
    have hQ (a : ℂ) : Integrable (Q a) (volume.restrict unitDisc) := hi a
    have he (z : ℂ) : f z * conj (g z) = (Q 1 z-Q (-1) z+(Q I z-Q (-I) z)*I)/4 := by
      simpa [Q, sub_eq_add_neg] using bergman_polarization (f z) (g z)
    simp_rw [he]
    rw [integral_div, integral_add ((hQ 1).sub' (hQ (-1)))
      (((hQ I).sub' (hQ (-I))).mul_const I), integral_sub (hQ 1) (hQ (-1)),
      integral_mul_const, integral_sub (hQ I) (hQ (-I))]
    simp only [Q, integral_complex_ofReal]
  rw [hiEq]
  apply hsum.congr_fun
  intro n
  simpa [sub_eq_add_neg] using bergman_polarization (x n) (y n)

/-- Evaluation vectors are absolutely summable inside the disk. -/
theorem basisE_norm_summable {z : ℂ} (hz : z ∈ unitDisc) :
    Summable (fun n => ‖basisE n z‖) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hg := summable_geometric_of_lt_one (norm_nonneg z) hz1
  have hn : Summable (fun n : ℕ => (n : ℝ)*‖z‖^n) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖‖z‖‖ < 1 by simpa only [norm_norm] using hz1)
  apply ((((hn.add hg).div_const π).add hg).of_nonneg_of_le (fun n => norm_nonneg _))
  intro n
  have ht : 0 ≤ ((n : ℝ)+1)/π := by positivity
  have hsq : Real.sqrt (((n : ℝ)+1)/π) ≤ ((n : ℝ)+1)/π+1 := by
    nlinarith [Real.sqrt_nonneg (((n : ℝ)+1)/π), Real.sq_sqrt ht]
  simp only [basisE, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (((n : ℝ)+1)/π+1)*‖z‖^n := mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = _ := by ring

end TakhtajanTeo.Ch2
