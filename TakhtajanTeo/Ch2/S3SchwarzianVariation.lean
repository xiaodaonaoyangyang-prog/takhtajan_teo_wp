import TakhtajanTeo.Ch2.S3TracePairing

/-! # Actual Fredholm variation and the exterior Schwarzian pairing -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

theorem s3sv_eval_series (A : s3tc_HS) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    HasSum (fun q : ℕ × ℕ => (A q*(s3dl_weight q : ℂ))*z^q.1*w^q.2) (s3kv_eval z w A) := by
  rw [s3dl_kernel_sum A hz hw]
  apply (s3dl_kernel_summable A hz hw).hasSum.congr_fun
  intro q
  rw [basisE,basisE,s3dl_weight,Complex.ofReal_mul]
  ring

theorem s3sv_eval_holomorphic (A : s3tc_HS) (w : ℂ) :
    DifferentiableOn ℂ (fun z => s3kv_eval z w A) unitDisc := by
  have h := (bergman_ell2_series (gop_l2_summable (s3tc_toOperator A (s3kv_vector w)))).1.1
  exact h.congr (fun z hz => s3kv_kernel_series (s3tc_toOperator A) hz w)

/-- Actual HS kernels determine their matrices; the removable diagonal is
recovered by continuity before applying two-variable coefficient uniqueness. -/
theorem s3sv_eval_injective {A B : s3tc_HS}
    (he : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → s3kv_eval z w A = s3kv_eval z w B) : A = B := by
  have hall : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, s3kv_eval z w A = s3kv_eval z w B := by
    intro z hz w hw
    by_cases hzw : z ≠ w
    · exact he z hz w hw hzw
    have hew : z = w := not_ne_iff.mp hzw
    subst z
    have hA := (s3sv_eval_holomorphic A w).continuousOn.continuousAt (isOpen_ball.mem_nhds hw)
    have hB := (s3sv_eval_holomorphic B w).continuousOn.continuousAt (isOpen_ball.mem_nhds hw)
    have hev : (fun z => s3kv_eval z w A) =ᶠ[𝓝[≠] w] (fun z => s3kv_eval z w B) := by
      filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (isOpen_ball.mem_nhds hw)] with z hzw hz
      exact he z hz w hw hzw
    exact tendsto_nhds_unique (hA.tendsto.mono_left nhdsWithin_le_nhds)
      ((hB.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm)
  have hc := double_powerSeries_coeff_unique
    (a := fun m n => A (m,n)*(s3dl_weight (m,n) : ℂ))
    (b := fun m n => B (m,n)*(s3dl_weight (m,n) : ℂ))
    (fun z hz w hw => s3sv_eval_series A hz hw)
    (fun z hz w hw => by rw [hall z hz w hw]; exact s3sv_eval_series B hz hw)
  ext q
  rcases q with ⟨m,n⟩
  have hpos : 0 < s3dl_weight (m,n) := by unfold s3dl_weight; positivity
  exact mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hpos.ne') (congrFun (congrFun hc m) n)

theorem s3sv_mixed_eval {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z u : ℂ}
    (hz : z ∈ unitDisc) (hu : u ∈ unitDiscExterior) :
    s3tp_bilinear (s3st_vector u) (gopOp (B3 (grunsky (fsans ν) (gsans ν))) (s3kv_vector z)) =
      kerK2 (fsans ν) (gsans ν) z u := by
  rw [s3tp_bilinear_sum,← (s3kv_K2_row_series hν hz hu).tsum_eq]
  apply tsum_congr
  intro n
  rw [s3st_vector_apply hu,mul_comm]

/-- The HS matrix supplied by the continuous harmonic pairing, transported
by the two actual mixed Grunsky blocks. -/
def s3sv_factor (ν : LinfStar) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) : s3tc_HS :=
  s3tc_left (gopOp (B2 (grunsky (fsans ν) (gsans ν))))
    (s3tc_rightCLM (gopOp (B3 (grunsky (fsans ν) (gsans ν)))) (s3tp_symbol hμ))

theorem s3sv_factor_kernel {ν : LinfStar} (hν : ν ∈ LinfStarBall) {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    s3kv_eval z w (s3sv_factor ν hμ) = ∫ u in unitDiscExterior,
      μ u*kerK2 (fsans ν) (gsans ν) z u*kerK2 (fsans ν) (gsans ν) w u := by
  let B := gopOp (B2 (grunsky (fsans ν) (gsans ν)))
  let C := gopOp (B3 (grunsky (fsans ν) (gsans ν)))
  obtain ⟨_,_,_,_,_,_,_,_,hT⟩ :=
    gop_blocks (AppB.b8_welding_normalized_pair hν) (r22_complement_null hν)
  rw [s3kv_eval_apply,s3sv_factor,s3kv_kernel,s3tc_left_operator,s3tc_right_operator,
    ContinuousLinearMap.mul_apply,ContinuousLinearMap.mul_apply]
  change s3tp_bilinear (s3kv_vector z) (B (s3tc_toOperator (s3tp_symbol hμ) (C (s3kv_vector w)))) = _
  rw [s3tp_bilinear_transpose,← hT,s3tp_symbol_pair]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem wp_exterior_isOpen.measurableSet] with u hu
  rw [s3sv_mixed_eval hν hz hu,s3sv_mixed_eval hν hw hu]

/-- The actual derivative matrix is the transported pairing symbol. -/
theorem s3sv_actual_factor {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {F : ℂ → s3tc_HS} {d : s3tc_HS}
    (he : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ q : ℕ × ℕ, F t q =
      B1 (grunsky (fsans (beltramiMul (t • toLinf μ) ν))
        (gsans (beltramiMul (t • toLinf μ) ν))) q.1 q.2)
    (hF : HasDerivAt F d 0) : d = s3sv_factor ν hμ := by
  apply s3sv_eval_injective
  intro z hz w hw hzw
  rw [s3sv_factor_kernel hν hμ hz hw]
  exact (s3kv_HS_mixed_kernel hν hνT hμ he hF hz hw hzw).2

/-- The genuine first variation, with no kernel identity or integrability premise. -/
theorem s3sv_first_variation {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    bersDz liouvilleS2 ν μ = -(1/(6*π))*∫ z in unitDiscExterior, schwarzianHol (gsans ν) z*μ z := by
  obtain ⟨F,d,he,hF,htrace,hkernel⟩ := s3kv_chart_data hν hνT hμ
  let A := F 0
  let B := gopOp (B2 (grunsky (fsans ν) (gsans ν)))
  let C := gopOp (B3 (grunsky (fsans ν) (gsans ν)))
  let H := s3tp_symbol hμ
  let Q := s3tc_rightCLM (s3ft_resolvent A*B) (s3tc_left C (s3tc_adjoint A))
  have hd := s3sv_actual_factor hν hνT hμ he hF
  have hop : s3tc_toOperator A = gopOp (B1 (grunsky (fsans ν) (gsans ν))) := by
    change gopOp (fun m n => F 0 (m,n)) = _
    congr 1
    funext m n
    simpa only [zero_smul,grp_zero_mul hν] using he.self_of_nhds (m,n)
  have hQ : s3tc_toOperator Q = s3st_resolventOperator ν := by
    dsimp only [Q]
    rw [s3tc_right_operator,s3tc_left_operator,s3tc_adjoint_operator]
    dsimp only [s3st_resolventOperator,s3ft_resolvent,s3fd_gram,B,C]
    rw [hop]
    simp only [mul_assoc]
  have ht : s3tc_trace (s3tc_left (s3ft_resolvent A) d) (s3tc_adjoint A) = s3tc_trace Q H := by
    rw [hd]
    change s3tc_trace (s3tc_left (s3ft_resolvent A) (s3tc_left B (s3tc_rightCLM C H))) (s3tc_adjoint A) = _
    calc
      _ = s3tc_trace (s3tc_left (s3ft_resolvent A*B) H) (s3tc_left C (s3tc_adjoint A)) := by
        apply s3ft_trace_congr_product
        simp only [s3tc_left_operator,s3tc_right_operator,mul_assoc]
      _ = s3tc_trace H Q := s3tc_trace_left_right _ _ _
      _ = _ := s3tc_trace_cyclic _ _
  calc
    bersDz liouvilleS2 ν μ = -s3tc_trace (s3tc_left (s3ft_resolvent A) d) (s3tc_adjoint A) := htrace
    _ = -s3tc_trace Q H := congrArg Neg.neg ht
    _ = -(∫ z in unitDiscExterior, s3st_kernel (s3tc_toOperator Q) z z*μ z) := by rw [s3tp_trace_integral hμ Q]
    _ = -((1/(6*π))*∫ z in unitDiscExterior, schwarzianHol (gsans ν) z*μ z) := by
      rw [hQ,(s3st_resolvent_diagonal_integral hν hνT hμ).2]
    _ = _ := (neg_mul _ _).symm

/-- Exact candidate for the original Theorem 3.1; original-name installation is coordinator-owned. -/
theorem s3sv_thm_3_1 {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    let ν : LinfStar := (Quotient.out p : LinfStarBall)
    BersDiffAt liouvilleS2 ν μ ∧
      bersDz liouvilleS2 ν μ = -(1 / (6 * π)) * ∫ z in unitDiscExterior, schwarzianHol (gsans ν) z * μ z := by
  intro ν
  have hν : ν ∈ LinfStarBall := (Quotient.out p).2
  have hpt : Phi ⟨ν,hν⟩ ∈ T01 := by
    rw [show Phi ⟨ν,hν⟩ = p from Quotient.out_eq p]
    exact hp
  exact ⟨s3fd_bersDiffAt hp hμ,s3sv_first_variation hν hpt hμ⟩

/-- Exact candidate for the original Corollary 3.2. -/
theorem s3sv_cor_3_2 {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    bersDz liouvilleS2 (Quotient.out p : LinfStarBall) μ = -(1 / (6 * π)) * varthetaPair p μ :=
  (s3sv_thm_3_1 hp hμ).2

end Ch2
end TakhtajanTeo
