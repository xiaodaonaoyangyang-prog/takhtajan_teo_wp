import TakhtajanTeo.Ch1.ComponentBlowupNormalization
import TakhtajanTeo.Ch1.S2_HilbertManifold

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem cbs_norm_one_sub (c : ℝ) (t : ℂ) :
    ‖(1 : ℂ)-(c : ℂ)*t‖^2 = 1-2*c*t.re+c^2*‖t‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,sub_re,sub_im,one_re,one_im,
    mul_re,mul_im,ofReal_re,ofReal_im,zero_mul,sub_zero]
  ring

/-- Exact radial gap, valid in every direction of the original point a. -/
theorem cbs_source_gap {a : ℂ} (ha : 0<‖a‖) (t : ℂ) :
    1-‖cbl_source a t‖^2 =
      (1-‖a‖)*(1+‖a‖+‖a‖*t.re-(1-‖a‖)*‖t‖^2/4) := by
  have hC : (‖a‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have he : cbl_source a t = a*(1-(((1-‖a‖)/(2*‖a‖) : ℝ) : ℂ)*t) := by
    unfold cbl_source cbl_scale
    push_cast
    field_simp
    ring
  rw [he,norm_mul,mul_pow,cbs_norm_one_sub]
  field_simp [ha.ne']
  ring

/-- The fixed radius-two disk is already inside every moving source domain. -/
theorem cbs_source_ball_two {a : ℂ} (ha0 : 0<‖a‖) (ha1 : ‖a‖<1) :
    MapsTo (cbl_source a) (ball (0 : ℂ) 2) unitDisc := by
  intro t ht
  have ht2 : ‖t‖<2 := mem_ball_zero_iff.mp ht
  have hb := norm_add_le a (cbl_scale a*t)
  rw [norm_mul,cbl_scale_norm ha0 ha1] at hb
  apply mem_ball_zero_iff.mpr
  change ‖a+cbl_scale a*t‖<1
  nlinarith

theorem cbs_compact_parameters {K : Set ℂ} (hK : IsCompact K)
    (hhalf : K⊆{t : ℂ | -2<t.re}) :
    ∃ m>0, ∃ M≥0, ∀ t∈K, m≤2+t.re ∧ ‖t‖≤M := by
  by_cases hne : K.Nonempty
  · obtain ⟨t0,ht0,hmin⟩ := hK.exists_isMinOn hne
      ((continuous_const.add Complex.continuous_re).continuousOn)
    obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨2+t0.re,by have := hhalf ht0; dsimp at this; linarith,
      M,(norm_nonneg t0).trans (hM t0 ht0),?_⟩
    intro t ht
    exact ⟨hmin ht,hM t ht⟩
  · exact ⟨1,one_pos,0,le_rfl,fun t ht => False.elim (hne ⟨t,ht⟩)⟩

theorem cbs_gap_lower {a t : ℂ} {m M : ℝ}
    (ha0 : 0<‖a‖) (ha1 : ‖a‖<1) (hM0 : 0≤M)
    (hm : m≤2+t.re) (ht : ‖t‖≤M)
    (hsmall : (1-‖a‖)*(1+M+M^2/4) ≤ m/2) :
    (1-‖a‖)*(m/2)≤1-‖cbl_source a t‖^2 := by
  have hsq : ‖t‖^2≤M^2 := by nlinarith [norm_nonneg t]
  have hre : t.re≤M := (Complex.re_le_norm t).trans ht
  have herr : 1+t.re+‖t‖^2/4≤1+M+M^2/4 := by linarith
  have hterm : (1-‖a‖)*(1+t.re+‖t‖^2/4) ≤ m/2 :=
    (mul_le_mul_of_nonneg_left herr (sub_nonneg.mpr ha1.le)).trans hsmall
  rw [cbs_source_gap ha0]
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ha1.le)
  have he : 1+‖a‖+‖a‖*t.re-(1-‖a‖)*‖t‖^2/4 =
      (2+t.re)-(1-‖a‖)*(1+t.re+‖t‖^2/4) := by ring
  rw [he]
  linarith

/-- Uniform positive gap on each compact subset of the limiting half-plane. -/
theorem cbs_compact_gap {a : ℕ → ℂ}
    (ha : ∀ n, 0<‖a n‖ ∧ ‖a n‖<1) (hlim : Tendsto (fun n => ‖a n‖) atTop (𝓝 1))
    {K : Set ℂ} (hK : IsCompact K) (hhalf : K⊆{t : ℂ | -2<t.re}) :
    ∃ m>0, ∀ᶠ n in atTop, ∀ t∈K,
      (1-‖a n‖)*(m/2)≤1-‖cbl_source (a n) t‖^2 ∧ cbl_source (a n) t∈unitDisc := by
  obtain ⟨m,hm,M,hM0,hbounds⟩ := cbs_compact_parameters hK hhalf
  have hzero : Tendsto (fun n => (1-‖a n‖)*(1+M+M^2/4)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim).mul_const (1+M+M^2/4)
  refine ⟨m,hm,?_⟩
  filter_upwards [hzero.eventually (gt_mem_nhds (half_pos hm))] with n hn t ht
  have hgap := cbs_gap_lower (ha n).1 (ha n).2 hM0 (hbounds t ht).1 (hbounds t ht).2 hn.le
  refine ⟨hgap,mem_ball_zero_iff.mpr ?_⟩
  have hpos : 0<(1-‖a n‖)*(m/2) := mul_pos (sub_pos.mpr (ha n).2) (half_pos hm)
  nlinarith [norm_nonneg (cbl_source (a n) t)]

theorem cbs_eventually_mapsTo {a : ℕ → ℂ}
    (ha : ∀ n, 0<‖a n‖ ∧ ‖a n‖<1) (hlim : Tendsto (fun n => ‖a n‖) atTop (𝓝 1))
    {K : Set ℂ} (hK : IsCompact K) (hhalf : K⊆{t : ℂ | -2<t.re}) :
    ∀ᶠ n in atTop, MapsTo (cbl_source (a n)) K unitDisc := by
  obtain ⟨m,_,h⟩ := cbs_compact_gap ha hlim hK hhalf
  exact h.mono (fun n hn t ht => (hn t ht).2)

theorem cbs_source_radial_error {a t : ℂ} {M : ℝ}
    (ha0 : 0<‖a‖) (ha1 : ‖a‖<1) (ht : ‖t‖≤M) :
    |‖cbl_source a t‖-1|≤(1-‖a‖)*(1+M/2) := by
  have hdiff : ‖cbl_source a t-a‖=(1-‖a‖)/2*‖t‖ := by
    simp only [cbl_source,add_sub_cancel_left,norm_mul,cbl_scale_norm ha0 ha1]
  calc |‖cbl_source a t‖-1| ≤ |‖cbl_source a t‖-‖a‖|+|‖a‖-1| := abs_sub_le _ _ _
    _ ≤ ‖cbl_source a t-a‖+(1-‖a‖) := by
      apply add_le_add (abs_norm_sub_norm_le _ _) (le_of_eq ?_)
      rw [abs_of_neg (sub_neg.mpr ha1)]
      ring
    _ ≤ (1-‖a‖)*(1+M/2) := by rw [hdiff]; nlinarith

/-- Epsilon form of the actual A2 weighted boundary limit. -/
theorem cbs_A2_boundary_small {P : ℂ → ℂ} (hP : P∈A2fun unitDisc) {ε : ℝ} (hε : 0<ε) :
    ∃ η>0, ∀ w∈unitDisc, dist ‖w‖ 1<η → (1-‖w‖^2)^2*‖P w‖<ε := by
  have he := (A2fun.disk_weighted_tendsto_zero hP).eventually (gt_mem_nhds hε)
  have he' := eventually_inf_principal.mp he
  obtain ⟨U,hU,hsub⟩ := Filter.mem_comap.mp he'
  obtain ⟨η,hη,hηU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨η,hη,?_⟩
  intro w hw hdist
  exact hsub (hηU hdist) hw

/-- The scaled actual A2 differential tends uniformly to zero on each fixed interior compact. -/
theorem cbs_scaled_tendsto_uniformlyOn {a : ℕ → ℂ} {P : ℂ → ℂ}
    (ha : ∀ n, 0<‖a n‖ ∧ ‖a n‖<1) (hlim : Tendsto (fun n => ‖a n‖) atTop (𝓝 1))
    (hP : P∈A2fun unitDisc) {K : Set ℂ} (hK : IsCompact K)
    (hhalf : K⊆{t : ℂ | -2<t.re}) :
    TendstoUniformlyOn (fun n t => cbl_scale (a n)^2*P (cbl_source (a n) t))
      (fun _ => 0) atTop K := by
  obtain ⟨m,hm,hgeom⟩ := cbs_compact_gap ha hlim hK hhalf
  obtain ⟨_,_,M,hM0,hbounds⟩ := cbs_compact_parameters hK hhalf
  have hnear : Tendsto (fun n => (1-‖a n‖)*(1+M/2)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim).mul_const (1+M/2)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hm2 : 0 < m^2 := sq_pos_of_pos hm
  obtain ⟨η,hη,hweight⟩ := cbs_A2_boundary_small hP (mul_pos hε hm2)
  filter_upwards [hgeom,hnear.eventually (gt_mem_nhds hη)] with n hn hηn t ht
  have hdist : dist ‖cbl_source (a n) t‖ 1<η := by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (cbs_source_radial_error (ha n).1 (ha n).2 (hbounds t ht).2) hηn
  have hweighted := hweight _ (hn t ht).2 hdist
  have hgap := (hn t ht).1
  have hlow0 : 0≤(1-‖a n‖)*(m/2) :=
    mul_nonneg (sub_nonneg.mpr (ha n).2.le) (half_pos hm).le
  have hsq : ((1-‖a n‖)*(m/2))^2≤(1-‖cbl_source (a n) t‖^2)^2 := by
    simpa only [pow_two] using mul_le_mul hgap hgap hlow0 (hlow0.trans hgap)
  have hbound : m^2*‖cbl_scale (a n)^2*P (cbl_source (a n) t)‖ ≤
      (1-‖cbl_source (a n) t‖^2)^2*‖P (cbl_source (a n) t)‖ := by
    calc m^2*‖cbl_scale (a n)^2*P (cbl_source (a n) t)‖ =
        ((1-‖a n‖)*(m/2))^2*‖P (cbl_source (a n) t)‖ := by
          rw [norm_mul,norm_pow,cbl_scale_norm (ha n).1 (ha n).2]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
  have hsmall : ‖cbl_scale (a n)^2*P (cbl_source (a n) t)‖<ε := by
    apply (mul_lt_mul_iff_right₀ hm2).mp
    simpa only [mul_comm] using lt_of_le_of_lt hbound hweighted
  simpa only [dist_zero_left,dist_zero_right] using hsmall

theorem cbs_scaled_tendsto_locallyUniformlyOn {a : ℕ → ℂ} {P : ℂ → ℂ}
    (ha : ∀ n, 0<‖a n‖ ∧ ‖a n‖<1) (hlim : Tendsto (fun n => ‖a n‖) atTop (𝓝 1))
    (hP : P∈A2fun unitDisc) :
    TendstoLocallyUniformlyOn (fun n t => cbl_scale (a n)^2*P (cbl_source (a n) t))
      (fun _ => 0) atTop {t : ℂ | -2<t.re} := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_re)).mpr
  intro K hhalf hK
  exact cbs_scaled_tendsto_uniformlyOn ha hlim hP hK hhalf

end TakhtajanTeo

