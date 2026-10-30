import TakhtajanTeo.Ch2.S3FredholmLog
import TakhtajanTeo.Ch2.S2Thm210
import TakhtajanTeo.Ch2.PeriodGrunskyBounds

/-! # Actual Bers-chart Hilbert--Schmidt and operator variation

All matrices below are evaluated on the explicit coefficient path, without
asserting continuity of the quotient's representative selector.
-/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- Finite extended square sum gives genuine square summability. -/
theorem s3fv_hs_of_ennreal {ι : Type*} {a : ι → ℂ}
    (h : (∑' i, (‖a i‖₊ : ℝ≥0∞)^2) < ∞) : Summable (fun i => ‖a i‖^2) := by
  simpa only [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm] using ENNReal.summable_toReal h.ne

theorem s3fv_mem_hs {ι : Type*} {a : ι → ℂ} (h : Summable fun i => ‖a i‖^2) : Memℓp a 2 :=
  memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h)

theorem s3fv_sum_hs {ι : Type*} {a : ι → ℂ} (h : Memℓp a 2) : Summable (fun i => ‖a i‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.summable (by norm_num)

/-- HS matrices define their intended gopOp, with the actual operator-norm bound. -/
theorem s3fv_hs_operator {A : ℕ → ℕ → ℂ} (hs : Summable fun q : ℕ × ℕ => ‖A q.1 q.2‖^2) :
    IsBoundedMat A ∧ ‖gopOp A‖ ≤ Real.sqrt (∑' q : ℕ × ℕ, ‖A q.1 q.2‖^2) := by
  have hr : ∀ m, Summable fun n => ‖A m n‖^2 := hs.prod_factor
  let r : ℕ → ell2 := fun m => ⟨fun n => conj (A m n),
    gop_mem_of_summable ((hr m).congr fun n => by rw [Complex.norm_conj])⟩
  have hrow : ∀ m, ‖r m‖^2 = ∑' n, ‖A m n‖^2 := by
    intro m
    rw [gop_norm_sq]
    exact tsum_congr fun n => by change ‖conj (A m n)‖^2 = _; rw [Complex.norm_conj]
  have hrs : Summable (fun m => ‖r m‖^2) := hs.prod.congr fun m => (hrow m).symm
  obtain ⟨T,hT,hTb⟩ := gop_rows_mk r hrs
  have hentry : ∀ m n, T (lp.single 2 n 1 : ell2) m = A m n := by
    intro m n
    rw [hT,lp.inner_single_right]
    simp only [r,gop_inner_apply,Complex.conj_conj,mul_one]
  have hb := pmb_of_operator T hentry
  have he : gopOp A = T := gop_ext (fun m n => (pmb_entry hb m n).trans (hentry m n).symm)
  refine ⟨hb,?_⟩
  rw [he]
  convert hTb using 1
  congr 1
  rw [hs.tsum_prod]
  exact tsum_congr hrow |>.symm

/-- Operator norm is bounded by the HS norm of its matrix in the canonical basis. -/
theorem s3fv_operator_hs_bound (T : ell2 →L[ℂ] ell2) {A : ℕ → ℕ → ℂ}
    (he : ∀ m n, T (lp.single 2 n 1 : ell2) m = A m n)
    (hs : Summable fun q : ℕ × ℕ => ‖A q.1 q.2‖^2) :
    ‖T‖ ≤ Real.sqrt (∑' q : ℕ × ℕ, ‖A q.1 q.2‖^2) := by
  obtain ⟨hb,hn⟩ := s3fv_hs_operator hs
  have hT : T = gopOp A := gop_ext (fun m n => (he m n).trans (pmb_entry hb m n).symm)
  rwa [hT]

/-- Extended HS convergence of the actual entries implies operator-norm convergence. -/
theorem s3fv_operator_tendsto_zero {ι : Type*} {l : Filter ι}
    {T : ι → ell2 →L[ℂ] ell2} {A : ι → ℕ → ℕ → ℂ}
    (he : ∀ᶠ t in l, ∀ m n, T t (lp.single 2 n 1 : ell2) m = A t m n)
    (hlim : Tendsto (fun t => ∑' q : ℕ × ℕ, (‖A t q.1 q.2‖₊ : ℝ≥0∞)^2) l (𝓝 0)) :
    Tendsto T l (𝓝 0) := by
  have hfinite : ∀ᶠ t in l, (∑' q : ℕ × ℕ, (‖A t q.1 q.2‖₊ : ℝ≥0∞)^2) < ∞ :=
    hlim.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  have hreal : Tendsto (fun t => (∑' q : ℕ × ℕ, (‖A t q.1 q.2‖₊ : ℝ≥0∞)^2).toReal) l (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hreal
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg (T t)) _ (by simpa using hsqrt)
  filter_upwards [he,hfinite] with t ht hf
  have hn := s3fv_operator_hs_bound (T t) ht (s3fv_hs_of_ennreal hf)
  have heq : (∑' q : ℕ × ℕ, ‖A t q.1 q.2‖^2) =
      (∑' q : ℕ × ℕ, (‖A t q.1 q.2‖₊ : ℝ≥0∞)^2).toReal := by
    simpa only [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm] using
      (ENNReal.tsum_toReal_eq (f := fun q : ℕ × ℕ => (‖A t q.1 q.2‖₊ : ℝ≥0∞)^2)
        (fun q => ENNReal.pow_ne_top (by simp))).symm
  rwa [heq] at hn

/-- The limit matrix of a genuine HS difference quotient is itself HS. -/
theorem s3fv_derivative_hs {A : ℂ → ℕ → ℕ → ℂ} {D : ℕ → ℕ → ℂ}
    (hA : ∀ᶠ t in 𝓝 (0 : ℂ), Summable fun q : ℕ × ℕ => ‖A t q.1 q.2‖^2)
    (hlim : Tendsto (fun t : ℂ => ∑' q : ℕ × ℕ,
      (‖(A t q.1 q.2-A 0 q.1 q.2)/t-D q.1 q.2‖₊ : ℝ≥0∞)^2) (𝓝[≠] 0) (𝓝 0)) :
    Summable (fun q : ℕ × ℕ => ‖D q.1 q.2‖^2) := by
  have h0 := s3fv_mem_hs (hA.self_of_nhds)
  have hf := hlim.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  obtain ⟨t,ht,hR⟩ := ((hA.filter_mono nhdsWithin_le_nhds).and hf).exists
  have hQ := ((s3fv_mem_hs ht).sub h0).const_smul t⁻¹
  have hR' := s3fv_mem_hs (s3fv_hs_of_ennreal hR)
  have hD := hQ.sub hR'
  apply s3fv_sum_hs
  convert hD using 1
  funext q
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
  ring

/-- The actual HS difference quotient gives a continuous-operator derivative. -/
theorem s3fv_hasDerivAt_of_hs {A : ℂ → ℕ → ℕ → ℂ} {D : ℕ → ℕ → ℂ}
    (hA : ∀ᶠ t in 𝓝 (0 : ℂ), Summable fun q : ℕ × ℕ => ‖A t q.1 q.2‖^2)
    (hlim : Tendsto (fun t : ℂ => ∑' q : ℕ × ℕ,
      (‖(A t q.1 q.2-A 0 q.1 q.2)/t-D q.1 q.2‖₊ : ℝ≥0∞)^2) (𝓝[≠] 0) (𝓝 0)) :
    Summable (fun q : ℕ × ℕ => ‖D q.1 q.2‖^2) ∧
      HasDerivAt (fun t => gopOp (A t)) (gopOp D) 0 := by
  have hD := s3fv_derivative_hs hA hlim
  have hbD := (s3fv_hs_operator hD).1
  have hb0 := (s3fv_hs_operator (hA.self_of_nhds)).1
  refine ⟨hD,hasDerivAt_iff_tendsto_slope.mpr ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_zero_iff_norm_tendsto_zero.mp
  apply s3fv_operator_tendsto_zero (A := fun t m n => (A t m n-A 0 m n)/t-D m n) _ hlim
  filter_upwards [hA.filter_mono nhdsWithin_le_nhds] with t ht
  intro m n
  have hbt := (s3fv_hs_operator ht).1
  simp only [slope,vsub_eq_sub,sub_zero,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    lp.coeFn_sub,lp.coeFn_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    pmb_entry hbt,pmb_entry hb0,pmb_entry hbD]
  ring

/-- On the actual Bers-chart path, the HS derivative is square summable, is
the genuine continuous-operator derivative, and admits a local uniform gap. -/
theorem s3fv_chart_operator {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    let A : ℂ → ℕ → ℕ → ℂ := fun t => B1 (grunsky
      (fsans (beltramiMul (t • toLinf μ) ν)) (gsans (beltramiMul (t • toLinf μ) ν)))
    ∃ D : ℕ → ℕ → ℂ, Summable (fun q : ℕ × ℕ => ‖D q.1 q.2‖^2) ∧
      Tendsto (fun t : ℂ => ∑' q : ℕ × ℕ,
        (‖(A t q.1 q.2-A 0 q.1 q.2)/t-D q.1 q.2‖₊ : ℝ≥0∞)^2) (𝓝[≠] 0) (𝓝 0) ∧
      HasDerivAt (fun t => gopOp (A t)) (gopOp D) 0 ∧
      ∃ r > 0, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ t ∈ ball (0 : ℂ) r,
        beltramiMul (t • toLinf μ) ν ∈ LinfStarBall ∧
        Summable (fun q : ℕ × ℕ => ‖A t q.1 q.2‖^2) ∧ ‖gopOp (A t)‖ ≤ c := by
  intro A
  obtain ⟨r,hr,M,hM,hb⟩ := t210_uniform hν hνT hμ
  have hAb : ∀ᶠ t in 𝓝 (0 : ℂ), beltramiMul (t • toLinf μ) ν ∈ LinfStarBall ∧
      Summable (fun q : ℕ × ℕ => ‖A t q.1 q.2‖^2) := by
    filter_upwards [closedBall_mem_nhds (0 : ℂ) hr] with t ht
    exact ⟨(hb t ht).1,s3fv_hs_of_ennreal ((hb t ht).2.trans_lt hM)⟩
  have hA0 : A 0 = B1 (grunsky (fsans ν) (gsans ν)) := by
    simp only [A,zero_smul,grp_zero_mul hν]
  obtain ⟨D,hD⟩ := thm_2_10 hν hνT hμ
  have hlim : Tendsto (fun t : ℂ => ∑' q : ℕ × ℕ,
      (‖(A t q.1 q.2-A 0 q.1 q.2)/t-D q.1 q.2‖₊ : ℝ≥0∞)^2) (𝓝[≠] 0) (𝓝 0) := by
    rw [hA0]
    exact hD
  obtain ⟨hDs,hd⟩ := s3fv_hasDerivAt_of_hs (hAb.mono fun t ht => ht.2) hlim
  have hnorm : ‖gopOp (A 0)‖ < 1 := by rw [hA0]; exact (pgb_norm_lt_one hν).1
  let c : ℝ := (‖gopOp (A 0)‖+1)/2
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hc1 : c < 1 := by dsimp only [c]; linarith
  have htc : ‖gopOp (A 0)‖ < c := by dsimp only [c]; linarith
  have hgap : ∀ᶠ t in 𝓝 (0 : ℂ), ‖gopOp (A t)‖ < c :=
    hd.continuousAt.norm.eventually (gt_mem_nhds htc)
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp (hAb.and hgap)
  refine ⟨D,hDs,hlim,hd,s,hs,c,hc0,hc1,?_⟩
  intro t ht
  obtain ⟨hbt,hnt⟩ := hball ht
  exact ⟨hbt.1,hbt.2,hnt.le⟩

/-- The norm in the matrix Hilbert space is the genuine square sum. -/
theorem s3fv_lp_norm_sq (x : lp (fun _ : ℕ × ℕ => ℂ) 2) :
    ‖x‖^2 = ∑' q : ℕ × ℕ, ‖x q‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x

/-- Extended square sums control the actual matrix Hilbert norm, including at limits. -/
theorem s3fv_lp_tendsto_zero {ι : Type*} {l : Filter ι}
    {F : ι → lp (fun _ : ℕ × ℕ => ℂ) 2} {A : ι → ℕ × ℕ → ℂ}
    (he : ∀ᶠ t in l, ∀ q, F t q = A t q)
    (hlim : Tendsto (fun t => ∑' q, (‖A t q‖₊ : ℝ≥0∞)^2) l (𝓝 0)) : Tendsto F l (𝓝 0) := by
  have hreal : Tendsto (fun t => (∑' q, (‖A t q‖₊ : ℝ≥0∞)^2).toReal) l (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  have heq : ∀ᶠ t in l, ‖F t‖^2 = (∑' q, (‖A t q‖₊ : ℝ≥0∞)^2).toReal := by
    filter_upwards [he] with t ht
    rw [s3fv_lp_norm_sq]
    simp_rw [ht]
    simpa only [ENNReal.toReal_pow,ENNReal.coe_toReal,coe_nnnorm] using
      (ENNReal.tsum_toReal_eq (f := fun q => (‖A t q‖₊ : ℝ≥0∞)^2)
        (fun q => ENNReal.pow_ne_top (by simp))).symm
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp (hreal.congr' (heq.mono fun t ht => ht.symm))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hn

/-- The actual extended HS difference quotient is a derivative in the Hilbert
space of matrices, with a representative agreeing on a whole neighbourhood. -/
theorem s3fv_hilbert_derivative {A : ℂ → ℕ → ℕ → ℂ} {D : ℕ → ℕ → ℂ}
    (hA : ∀ᶠ t in 𝓝 (0 : ℂ), Summable fun q : ℕ × ℕ => ‖A t q.1 q.2‖^2)
    (hlim : Tendsto (fun t : ℂ => ∑' q : ℕ × ℕ,
      (‖(A t q.1 q.2-A 0 q.1 q.2)/t-D q.1 q.2‖₊ : ℝ≥0∞)^2) (𝓝[≠] 0) (𝓝 0)) :
    ∃ F : ℂ → lp (fun _ : ℕ × ℕ => ℂ) 2, ∃ d : lp (fun _ : ℕ × ℕ => ℂ) 2,
      (∀ᶠ t in 𝓝 (0 : ℂ), ∀ q, F t q = A t q.1 q.2) ∧
      (∀ q, d q = D q.1 q.2) ∧ HasDerivAt F d 0 := by
  have hD := s3fv_mem_hs (s3fv_derivative_hs hA hlim)
  let F : ℂ → lp (fun _ : ℕ × ℕ => ℂ) 2 := fun t =>
    if ht : Memℓp (fun q : ℕ × ℕ => A t q.1 q.2) 2 then ⟨_,ht⟩ else 0
  let d : lp (fun _ : ℕ × ℕ => ℂ) 2 := ⟨_,hD⟩
  have he : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ q, F t q = A t q.1 q.2 := by
    filter_upwards [hA] with t ht
    intro q
    simp only [F,dif_pos (s3fv_mem_hs ht)]
  have he0 := he.self_of_nhds
  refine ⟨F,d,he,fun _ => rfl,hasDerivAt_iff_tendsto_slope.mpr ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_zero_iff_norm_tendsto_zero.mp
  apply s3fv_lp_tendsto_zero (A := fun t q => (A t q.1 q.2-A 0 q.1 q.2)/t-D q.1 q.2) _ hlim
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with t ht
  intro q
  simp only [slope,vsub_eq_sub,sub_zero,lp.coeFn_sub,lp.coeFn_smul,
    Pi.sub_apply,Pi.smul_apply,smul_eq_mul,ht,he0]
  change t⁻¹*(A t q.1 q.2-A 0 q.1 q.2)-D q.1 q.2 = _
  ring

/-- Real directional variation of the first trace moment, proved through the
HS Hilbert-space derivative rather than by an assumed sum/derivative exchange. -/
theorem s3fv_first_trace_variation {A : ℂ → ℕ → ℕ → ℂ} {D : ℕ → ℕ → ℂ}
    (hA : ∀ᶠ t in 𝓝 (0 : ℂ), Summable fun q : ℕ × ℕ => ‖A t q.1 q.2‖^2)
    (hlim : Tendsto (fun t : ℂ => ∑' q : ℕ × ℕ,
      (‖(A t q.1 q.2-A 0 q.1 q.2)/t-D q.1 q.2‖₊ : ℝ≥0∞)^2) (𝓝[≠] 0) (𝓝 0)) (v : ℂ) :
    Summable (fun q : ℕ × ℕ => conj (A 0 q.1 q.2)*D q.1 q.2) ∧
      HasDerivAt (fun s : ℝ => ∑' q : ℕ × ℕ, ‖A ((s : ℂ)*v) q.1 q.2‖^2)
        (2*(v*(∑' q : ℕ × ℕ, conj (A 0 q.1 q.2)*D q.1 q.2)).re) 0 := by
  obtain ⟨F,d,he,hd,hdiff⟩ := s3fv_hilbert_derivative hA hlim
  have he0 := he.self_of_nhds
  have hs : Summable (fun q : ℕ × ℕ => conj (A 0 q.1 q.2)*D q.1 q.2) := by
    simpa only [gop_inner_apply,he0,hd] using lp.summable_inner (𝕜 := ℂ) (F 0) d
  have hinner : inner ℂ (F 0) d = ∑' q : ℕ × ℕ, conj (A 0 q.1 q.2)*D q.1 q.2 := by
    rw [lp.inner_eq_tsum]
    simp only [gop_inner_apply,he0,hd]
  have hline : HasDerivAt (fun s : ℝ => (s : ℂ)*v) v 0 := by
    simpa only [Complex.real_smul,id,Complex.ofReal_one,one_mul] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hdR : HasDerivAt (fun s : ℝ => F ((s : ℂ)*v)) (v • d) 0 := by
    have h := (hdiff.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 hline (by simp)
    simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply] using! h
  have hnorm := hdR.norm_sq
  have hedir : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), (∑' q : ℕ × ℕ, ‖A ((s : ℂ)*v) q.1 q.2‖^2) = ‖F ((s : ℂ)*v)‖^2 := by
    have he' : ∀ᶠ t in 𝓝 (((0 : ℝ) : ℂ)*v), ∀ q, F t q = A t q.1 q.2 := by simpa only [Complex.ofReal_zero,zero_mul] using he
    filter_upwards [hline.continuousAt.tendsto.eventually he'] with s hs
    rw [s3fv_lp_norm_sq]
    exact tsum_congr (fun q => by rw [hs q])
  refine ⟨hs,?_⟩
  convert hnorm.congr_of_eventuallyEq hedir using 1
  simp only [Complex.ofReal_zero,zero_mul]
  have hr : inner ℝ (F 0) (v • d) = (inner ℂ (F 0) (v • d)).re := by
    rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
    rw [Complex.re_tsum (lp.summable_inner (𝕜 := ℂ) (F 0) (v • d))]
    apply tsum_congr
    intro q
    rfl
  rw [hr,inner_smul_right,hinner]

/-- The diagonal sum of the actual Gram operator is the HS square norm;
summability is proved before identifying this trace. -/
theorem s3fv_gram_trace {A : ℕ → ℕ → ℂ} (hs : Summable fun q : ℕ × ℕ => ‖A q.1 q.2‖^2) :
    Summable (fun m => (inner ℂ (lp.single 2 m 1 : ell2)
      ((gopOp A * star (gopOp A)) (lp.single 2 m 1))).re) ∧
    (∑' m, (inner ℂ (lp.single 2 m 1 : ell2)
      ((gopOp A * star (gopOp A)) (lp.single 2 m 1))).re) = ∑' q : ℕ × ℕ, ‖A q.1 q.2‖^2 := by
  have hA := (s3fv_hs_operator hs).1
  have he (m : ℕ) : (inner ℂ (lp.single 2 m 1 : ell2)
      ((gopOp A * star (gopOp A)) (lp.single 2 m 1))).re = ∑' n, ‖A m n‖^2 := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    have ht := dF_inner_mul_adjoint (gopOp A) (lp.single 2 m 1 : ell2)
    change (inner ℂ (lp.single 2 m 1 : ell2) ((gopOp A * ContinuousLinearMap.adjoint (gopOp A))
      (lp.single 2 m 1))).re = _ at ht
    rw [ht,gop_norm_sq]
    apply tsum_congr
    intro n
    rw [gop_adjoint_apply (isBoundedMat_row_isL2 hA) (pmb_partial_bound hA),gop_tsum_single]
    rw [Complex.norm_conj]
  exact ⟨hs.prod.congr (fun m => (he m).symm),(tsum_congr he).trans hs.tsum_prod.symm⟩

/-- Genuine first Gram-trace variation, with its trace defined by the convergent diagonal sum. -/
theorem s3fv_gram_trace_variation {A : ℂ → ℕ → ℕ → ℂ} {D : ℕ → ℕ → ℂ}
    (hA : ∀ᶠ t in 𝓝 (0 : ℂ), Summable fun q : ℕ × ℕ => ‖A t q.1 q.2‖^2)
    (hlim : Tendsto (fun t : ℂ => ∑' q : ℕ × ℕ,
      (‖(A t q.1 q.2-A 0 q.1 q.2)/t-D q.1 q.2‖₊ : ℝ≥0∞)^2) (𝓝[≠] 0) (𝓝 0)) (v : ℂ) :
    HasDerivAt (fun s : ℝ => ∑' m, (inner ℂ (lp.single 2 m 1 : ell2)
      ((gopOp (A ((s : ℂ)*v)) * star (gopOp (A ((s : ℂ)*v)))) (lp.single 2 m 1))).re)
      (2*(v*(∑' q : ℕ × ℕ, conj (A 0 q.1 q.2)*D q.1 q.2)).re) 0 := by
  have hd := (s3fv_first_trace_variation hA hlim v).2
  apply hd.congr_of_eventuallyEq
  have hline : ContinuousAt (fun s : ℝ => (s : ℂ)*v) 0 := by fun_prop
  have hA' : ∀ᶠ t in 𝓝 (((0 : ℝ) : ℂ)*v), Summable fun q : ℕ × ℕ => ‖A t q.1 q.2‖^2 :=
    by simpa only [Complex.ofReal_zero,zero_mul] using hA
  filter_upwards [hline.tendsto.eventually hA'] with s hs
  exact (s3fv_gram_trace hs).2

/-- Real directional derivative of the actual Gram operator. -/
theorem s3fv_gram_derivative {T : ℂ → ell2 →L[ℂ] ell2} {D : ell2 →L[ℂ] ell2}
    (hd : HasDerivAt T D 0) (v : ℂ) :
    HasDerivAt (fun s : ℝ => T ((s : ℂ)*v) * star (T ((s : ℂ)*v)))
      ((v • D)*star (T 0) + T 0*star (v • D)) 0 := by
  letI : StarModule ℝ (ell2 →L[ℂ] ell2) := ⟨fun r U => by
    have hsm (V : ell2 →L[ℂ] ell2) : r • V = (r : ℂ) • V := by
      ext x n
      simp only [ContinuousLinearMap.smul_apply,lp.coeFn_smul,Pi.smul_apply,Complex.real_smul,smul_eq_mul]
    rw [star_trivial r,hsm U,star_smul,hsm (star U)]
    simp⟩
  have hline : HasDerivAt (fun s : ℝ => (s : ℂ)*v) v 0 := by
    simpa only [Complex.real_smul,id,Complex.ofReal_one,one_mul] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hdR : HasDerivAt (fun s : ℝ => T ((s : ℂ)*v)) (v • D) 0 := by
    have h := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 hline (by simp)
    simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply] using! h
  simpa only [Complex.ofReal_zero,zero_mul] using! hdR.mul hdR.star

/-- Every operator power has the actual noncommutative first variation,
before any infinite trace or logarithm summation is attempted. -/
theorem s3fv_gram_power_derivative {T : ℂ → ell2 →L[ℂ] ell2} {D : ell2 →L[ℂ] ell2}
    (hd : HasDerivAt T D 0) (v : ℂ) (N : ℕ) :
    HasDerivAt (fun s : ℝ => (T ((s : ℂ)*v) * star (T ((s : ℂ)*v)))^N)
      (∑ j ∈ Finset.range N, (T 0*star (T 0))^(N.pred-j) *
        ((v • D)*star (T 0) + T 0*star (v • D)) * (T 0*star (T 0))^j) 0 := by
  simpa only [Complex.ofReal_zero,zero_mul] using! (s3fv_gram_derivative hd v).fun_pow' N

/-- The first trace moment and all finite operator-power variations,
instantiated on the actual Bers-chart path at any T₀(1) base representative. -/
theorem s3fv_chart_trace_variation {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    let A : ℂ → ℕ → ℕ → ℂ := fun t => B1 (grunsky
      (fsans (beltramiMul (t • toLinf μ) ν)) (gsans (beltramiMul (t • toLinf μ) ν)))
    let T : ℂ → ell2 →L[ℂ] ell2 := fun t => gopOp (A t)
    ∃ D : ℕ → ℕ → ℂ, Summable (fun q : ℕ × ℕ => ‖D q.1 q.2‖^2) ∧
      HasDerivAt T (gopOp D) 0 ∧
      (∀ v : ℂ, HasDerivAt (fun s : ℝ => ∑' m, (inner ℂ (lp.single 2 m 1 : ell2)
        ((T ((s : ℂ)*v) * star (T ((s : ℂ)*v))) (lp.single 2 m 1))).re)
        (2*(v*(∑' q : ℕ × ℕ, conj (A 0 q.1 q.2)*D q.1 q.2)).re) 0) ∧
      ∀ (v : ℂ) (N : ℕ), HasDerivAt (fun s : ℝ => (T ((s : ℂ)*v)*star (T ((s : ℂ)*v)))^N)
        (∑ j ∈ Finset.range N, (T 0*star (T 0))^(N.pred-j) *
          ((v • gopOp D)*star (T 0)+T 0*star (v • gopOp D)) * (T 0*star (T 0))^j) 0 := by
  intro A T
  obtain ⟨D,hD,hlim,hd,r,hr,c,hc0,hc1,hb⟩ := s3fv_chart_operator hν hνT hμ
  have hA : ∀ᶠ t in 𝓝 (0 : ℂ), Summable fun q : ℕ × ℕ => ‖A t q.1 q.2‖^2 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t ht
    exact (hb t ht).2.1
  exact ⟨D,hD,hd,fun v => s3fv_gram_trace_variation hA hlim v,
    fun v N => s3fv_gram_power_derivative hd v N⟩

/-- The trace pairing of two actual HS operators is absolutely convergent,
agrees with the matrix Hilbert pairing, and satisfies its sharp norm bound. -/
theorem s3fv_trace_pair {A B : ℕ → ℕ → ℂ}
    (hA : Summable fun q : ℕ × ℕ => ‖A q.1 q.2‖^2)
    (hB : Summable fun q : ℕ × ℕ => ‖B q.1 q.2‖^2) :
    Summable (fun m => inner ℂ (lp.single 2 m 1 : ell2)
      ((gopOp A * star (gopOp B)) (lp.single 2 m 1))) ∧
      (∑' m, inner ℂ (lp.single 2 m 1 : ell2)
        ((gopOp A * star (gopOp B)) (lp.single 2 m 1))) =
        ∑' q : ℕ × ℕ, conj (B q.1 q.2)*A q.1 q.2 ∧
      ‖∑' m, inner ℂ (lp.single 2 m 1 : ell2)
        ((gopOp A * star (gopOp B)) (lp.single 2 m 1))‖ ≤
        Real.sqrt (∑' q : ℕ × ℕ, ‖A q.1 q.2‖^2) * Real.sqrt (∑' q : ℕ × ℕ, ‖B q.1 q.2‖^2) := by
  let X : lp (fun _ : ℕ × ℕ => ℂ) 2 := ⟨_,s3fv_mem_hs hA⟩
  let Y : lp (fun _ : ℕ × ℕ => ℂ) 2 := ⟨_,s3fv_mem_hs hB⟩
  have hi : inner ℂ Y X = ∑' q : ℕ × ℕ, conj (B q.1 q.2)*A q.1 q.2 := by
    rw [lp.inner_eq_tsum]
    exact tsum_congr (fun q => gop_inner_apply _ _)
  have hs : Summable (fun q : ℕ × ℕ => conj (B q.1 q.2)*A q.1 q.2) := by
    simpa only [gop_inner_apply] using lp.summable_inner (𝕜 := ℂ) Y X
  have hAb := (s3fv_hs_operator hA).1
  have hBb := (s3fv_hs_operator hB).1
  have he (m : ℕ) : inner ℂ (lp.single 2 m 1 : ell2)
      ((gopOp A * star (gopOp B)) (lp.single 2 m 1)) = ∑' n, conj (B m n)*A m n := by
    rw [gop_inner_single_left,ContinuousLinearMap.star_eq_adjoint,
      gop_mul_adjoint_entry (isBoundedMat_row_isL2 hAb) (pmb_partial_bound hAb)
        (isBoundedMat_row_isL2 hBb) (pmb_partial_bound hBb),mulAdj]
    exact tsum_congr (fun n => mul_comm _ _)
  have hsum := (tsum_congr he).trans hs.tsum_prod.symm
  refine ⟨hs.prod.congr (fun m => (he m).symm),hsum,?_⟩
  rw [hsum,← hi]
  have hn := norm_inner_le_norm (𝕜 := ℂ) Y X
  have hx : Real.sqrt (∑' q : ℕ × ℕ, ‖A q.1 q.2‖^2) = ‖X‖ := by
    change Real.sqrt (∑' q, ‖X q‖^2) = _
    rw [← s3fv_lp_norm_sq,Real.sqrt_sq (norm_nonneg X)]
  have hy : Real.sqrt (∑' q : ℕ × ℕ, ‖B q.1 q.2‖^2) = ‖Y‖ := by
    change Real.sqrt (∑' q, ‖Y q‖^2) = _
    rw [← s3fv_lp_norm_sq,Real.sqrt_sq (norm_nonneg Y)]
  rw [hx,hy,mul_comm]
  exact hn

/-- The actual chart has a uniform Neumann majorant and genuine resolvents;
the geometric series uses the proved operator gap, not a supplied spectrum. -/
theorem s3fv_chart_neumann {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    let T : ℂ → ell2 →L[ℂ] ell2 := fun t => gopOp (B1 (grunsky
      (fsans (beltramiMul (t • toLinf μ) ν)) (gsans (beltramiMul (t • toLinf μ) ν))))
    ∃ r > 0, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ t ∈ ball (0 : ℂ) r,
      IsUnit (1-T t*star (T t)) ∧
      (∀ N : ℕ, ‖(T t*star (T t))^N‖ ≤ (c^2)^N) ∧
      HasSum (fun N : ℕ => (T t*star (T t))^N) (Ring.inverse (1-T t*star (T t))) := by
  intro T
  obtain ⟨D,hD,hlim,hd,r,hr,c,hc0,hc1,hb⟩ := s3fv_chart_operator hν hνT hμ
  refine ⟨r,hr,c,hc0,hc1,fun t ht => ?_⟩
  have htbound : ‖T t‖ ≤ c := (hb t ht).2.2
  have hstar : ‖star (T t)‖ = ‖T t‖ := by
    change ‖ContinuousLinearMap.adjoint (T t)‖ = _
    exact LinearIsometryEquiv.norm_map _ _
  have hk : ‖T t*star (T t)‖ ≤ c^2 := by
    have hmul := norm_mul_le (T t) (star (T t))
    rw [hstar] at hmul
    nlinarith [norm_nonneg (T t)]
  have hc2 : c^2 < 1 := by nlinarith
  have hk1 := hk.trans_lt hc2
  have hp : ∀ N : ℕ, ‖(T t*star (T t))^N‖ ≤ (c^2)^N := by
    intro N
    induction N with
    | zero => simpa only [pow_zero] using! (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := ell2))
    | succ N ih =>
      rw [pow_succ,pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih hk (norm_nonneg _) (pow_nonneg (sq_nonneg c) N))
  exact ⟨isUnit_one_sub_of_norm_lt_one hk1,
    hp,
    hasSum_geom_series_inverse _ hk1⟩

end Ch2
end TakhtajanTeo
