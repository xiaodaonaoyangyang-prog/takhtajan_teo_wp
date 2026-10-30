import TakhtajanTeo.Ch2.S3SchwarzianTrace

/-! # Actual HS derivative and the transported mixed variation kernel -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

def s3kv_vector (z : ℂ) : ell2 :=
  if hz : z ∈ unitDisc then ⟨fun n => basisE n z,gop_mem_of_summable (basisE_sq_summable hz)⟩ else 0

theorem s3kv_vector_apply {z : ℂ} (hz : z ∈ unitDisc) (n : ℕ) :
    s3kv_vector z n = basisE n z := by simp only [s3kv_vector,dif_pos hz]

def s3kv_kernel (T : ell2 →L[ℂ] ell2) (z w : ℂ) : ℂ :=
  inner ℂ (star (s3kv_vector z)) (T (s3kv_vector w))

/-- Evaluation of the genuine HS kernel is a continuous linear functional. -/
def s3kv_eval (z w : ℂ) : s3tc_HS →L[ℂ] ℂ :=
  (innerSL ℂ (star (s3kv_vector z))).comp
    ((ContinuousLinearMap.apply ℂ ell2 (s3kv_vector w)).comp s3tc_toOperator)

theorem s3kv_eval_apply (A : s3tc_HS) (z w : ℂ) :
    s3kv_eval z w A = s3kv_kernel (s3tc_toOperator A) z w := rfl

theorem s3kv_kernel_series (T : ell2 →L[ℂ] ell2) {z : ℂ} (hz : z ∈ unitDisc) (w : ℂ) :
    s3kv_kernel T z w = ∑' n, (T (s3kv_vector w)) n*basisE n z := by
  rw [s3kv_kernel,lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [gop_inner_apply]
  change conj (conj (s3kv_vector z n))*(T (s3kv_vector w)) n = _
  rw [Complex.conj_conj,s3kv_vector_apply hz,mul_comm]

theorem s3kv_B1_kernel {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    s3kv_kernel (gopOp (B1 (grunsky (fsans ν) (gsans ν)))) z w = kerK1 (fsans ν) z w := by
  let B := B1 (grunsky (fsans ν) (gsans ν))
  have hB : IsBoundedMat B := pgb_bounded hν (by simp [B])
  have hs := e24_hK1 (AppB.b8_welding_normalized_pair hν) z hz w hw hzw
  rw [s3kv_kernel_series _ hz w,← hs.tsum_eq,hs.summable.tsum_prod]
  apply tsum_congr
  intro m
  rw [pmb_apply hB]
  change (∑' n, B m n*s3kv_vector w n)*basisE m z = _
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  rw [s3kv_vector_apply hw]
  ring

/-- The actual HS derivative differentiates the actual Grunsky kernel;
no termwise differentiation of an unbounded evaluation sum is used. -/
theorem s3kv_HS_kernel_derivative {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {F : ℂ → s3tc_HS} {d : s3tc_HS}
    (he : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ q : ℕ × ℕ, F t q =
      B1 (grunsky (fsans (beltramiMul (t • toLinf μ) ν))
        (gsans (beltramiMul (t • toLinf μ) ν))) q.1 q.2)
    (hF : HasDerivAt F d 0) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    HasDerivAt (fun t : ℂ => kerK1 (fsans (beltramiMul (t • toLinf μ) ν)) z w)
      (s3kv_eval z w d) 0 := by
  have hd := (s3kv_eval z w).hasFDerivAt.comp_hasDerivAt 0 hF
  apply hd.congr_of_eventuallyEq
  obtain ⟨D,hD,hlim,hder,r,hr,c,hc,hc1,hb⟩ := s3fv_chart_operator hν hνT hμ
  filter_upwards [he,ball_mem_nhds (0 : ℂ) hr] with t ht htr
  have hop : s3tc_toOperator (F t) = gopOp (B1 (grunsky
      (fsans (beltramiMul (t • toLinf μ) ν)) (gsans (beltramiMul (t • toLinf μ) ν)))) := by
    change gopOp (fun m n => F t (m,n)) = _
    congr 1
    funext m n
    exact ht (m,n)
  change _ = s3kv_eval z w (F t)
  rw [s3kv_eval_apply,hop]
  exact (s3kv_B1_kernel (hb t htr).1 hz hw hzw).symm

/-- The actual coefficient tangent induced by right translation. -/
def s3kv_tangent (ν : LinfStar) (μ : ℂ → ℂ) : LinfStar :=
  fderiv ℂ (fun l => beltramiMul l ν) 0 (toLinf μ)

theorem s3kv_chart_derivative {ν : LinfStar} (hν : ν ∈ LinfStarBall) (μ : ℂ → ℂ) :
    HasDerivAt (fun t : ℂ => beltramiMul (t • toLinf μ) ν) (s3kv_tangent ν μ) 0 := by
  obtain ⟨L,hL,hLe⟩ := bc_hasFDerivAt hν
  have hline : HasDerivAt (fun t : ℂ => t • toLinf μ) (toLinf μ) 0 := by
    simpa only [one_smul] using! (hasDerivAt_id (0 : ℂ)).smul_const (toLinf μ)
  exact hL.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)

/-- Ahlfors variation on the actual Bers path, in the already verified source coordinates. -/
theorem s3kv_source_variation {ν : LinfStar} (hν : ν ∈ LinfStarBall) (μ : ℂ → ℂ)
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    HasDerivAt (fun t : ℂ => kerK1 (fsans (beltramiMul (t • toLinf μ) ν)) z w)
      (1/π^2*(deriv (qcv_planeSolution ν) z*deriv (qcv_planeSolution ν) w)*
        ∫ u in unitDiscExterior, s3kv_tangent ν μ u*dz (qcv_planeSolution ν) u^2 /
          ((qcv_planeSolution ν u-qcv_planeSolution ν z)^2*
            (qcv_planeSolution ν u-qcv_planeSolution ν w)^2)) 0 := by
  have hK := ((l27_kerK1_differentiableOn hz hw hzw ν hν).differentiableAt
    (isOpen_ball.mem_nhds hν)).hasFDerivAt
  have hc := hK.comp_hasDerivAt_of_eq 0 (s3kv_chart_derivative hν μ)
    (by simp only [zero_smul,grp_zero_mul hν])
  have hline : HasDerivAt (fun t : ℂ => ν+t • s3kv_tangent ν μ) (s3kv_tangent ν μ) 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0 : ℂ)).smul_const (s3kv_tangent ν μ)).const_add ν
  have hl := hK.comp_hasDerivAt_of_eq 0 hline (by simp)
  exact hc.congr_deriv (hl.unique (l27_kerK1_line hν (s3kv_tangent ν μ) hz hw hzw))

/-- The verified source-coordinate variation equals the actual K2-product
integral in the exterior coordinate of the original harmonic tangent. -/
theorem s3kv_transport {ν : LinfStar} (hν : ν ∈ LinfStarBall) {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    (1/π^2*(deriv (qcv_planeSolution ν) z*deriv (qcv_planeSolution ν) w)*
      ∫ u in unitDiscExterior, s3kv_tangent ν μ u*dz (qcv_planeSolution ν) u^2 /
        ((qcv_planeSolution ν u-qcv_planeSolution ν z)^2*
          (qcv_planeSolution ν u-qcv_planeSolution ν w)^2)) =
      ∫ u in unitDiscExterior, μ u*kerK2 (fsans ν) (gsans ν) z u*kerK2 (fsans ν) (gsans ν) w u := by
  let f := fsans ν
  let g := gsans ν
  let W := qcv_planeSolution ν
  let θ := s3kv_tangent ν μ
  let Q := deriv W z*deriv W w*∫ u in unitDiscExterior,
    θ u*dz W u^2/((W u-W z)^2*(W u-W w)^2)
  let J := ∫ u in unitDiscExterior, μ u*deriv g u^2/((g u-f z)^2*(g u-f w)^2)
  have hf := S2C.s2c_conf_f hν
  have hzf : f z ∈ f '' unitDisc := ⟨z,hz,rfl⟩
  have hwf : f w ∈ f '' unitDisc := ⟨w,hw,rfl⟩
  have hzwf : f z ≠ f w := fun hh => hzw (hf.2.1 hz hw hh)
  have hzInv := hf.2.1.leftInvOn_invFunOn hz
  have hwInv := hf.2.1.leftInvOn_invFunOn hw
  have hdzInv : deriv (Function.invFunOn f unitDisc) (f z) = (deriv f z)⁻¹ :=
    eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul isOpen_ball hf hz)
  have hdwInv : deriv (Function.invFunOn f unitDisc) (f w) = (deriv f w)⁻¹ :=
    eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul isOpen_ball hf hw)
  have hθ : Rnm θ ν = toLinf μ := hb_Rnm_D0Right hν (toLinf μ)
  have htr := l27_transport hν θ hzf hwf hzwf
  dsimp only at htr
  rw [hzInv,hwInv,hdzInv,hdwInv,hθ,
    l27_g_transport wp_exterior_isOpen (S2C.s2c_conf_g hν)] at htr
  have hJ : (∫ u in unitDiscExterior, toLinf μ u*deriv g u^2/((g u-f z)^2*(g u-f w)^2)) = J := by
    apply integral_congr_ae
    filter_upwards [bc_toLinf_ae (d2_harmonicL2_memLp hμ)] with u hu
    rw [hu]
  change Q*(deriv f z)⁻¹*(deriv f w)⁻¹ = _ at htr
  rw [hJ] at htr
  have hz1 : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hw1 : deriv f w ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hw
  have hQ : Q = deriv f z*deriv f w*J := by
    calc
      Q = (Q*(deriv f z)⁻¹*(deriv f w)⁻¹)*deriv f z*deriv f w := by field_simp <;> ring
      _ = deriv f z*deriv f w*J := by rw [htr]; ring
  change (1/π^2)*(deriv W z*deriv W w)*_ = _
  calc
    _ = (1/π^2)*Q := by dsimp only [Q]; ring
    _ = ((1/π^2)*deriv f z*deriv f w)*J := by rw [hQ]; ring
    _ = ∫ u in unitDiscExterior, ((1/π^2)*deriv f z*deriv f w)*
        (μ u*deriv g u^2/((g u-f z)^2*(g u-f w)^2)) := (integral_const_mul _ _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp only [f,g]
      rw [kerK2,kerK2,
        show (fsans ν z-gsans ν u)^2 = (gsans ν u-fsans ν z)^2 by ring,
        show (fsans ν w-gsans ν u)^2 = (gsans ν u-fsans ν w)^2 by ring]
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
      ring

/-- The genuine Bers-chart Grunsky kernel variation in its mixed-kernel form. -/
theorem s3kv_K2_variation {ν : LinfStar} (hν : ν ∈ LinfStarBall) {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    HasDerivAt (fun t : ℂ => kerK1 (fsans (beltramiMul (t • toLinf μ) ν)) z w)
      (∫ u in unitDiscExterior, μ u*kerK2 (fsans ν) (gsans ν) z u*kerK2 (fsans ν) (gsans ν) w u) 0 :=
  (s3kv_source_variation hν μ hz hw hzw).congr_deriv (s3kv_transport hν hμ hz hw hzw)

/-- The mixed kernel row is the actual exterior Bergman series of B3 e(z). -/
theorem s3kv_K2_row_series {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z u : ℂ}
    (hz : z ∈ unitDisc) (hu : u ∈ unitDiscExterior) :
    HasSum (fun n => (gopOp (B3 (grunsky (fsans ν) (gsans ν))) (s3kv_vector z)) n*basisF n u)
      (kerK2 (fsans ν) (gsans ν) z u) := by
  let B := B3 (grunsky (fsans ν) (gsans ν))
  have hB : IsBoundedMat B := pgb_bounded hν (by simp [B])
  have hp := AppB.b8_welding_normalized_pair hν
  have hsym := (grunsky_unitary hp (r22_complement_null hν)).1
  have hs := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (e24_K2_series hp hz hu)
  have hn := (bergman_pair_summable (gop_l2_summable (gopOp B (s3kv_vector z))) (s3st_basisF_sq hu)).of_norm
  have he : (∑' n, (gopOp B (s3kv_vector z)) n*basisF n u) = kerK2 (fsans ν) (gsans ν) z u := by
    rw [← hs.tsum_eq,hs.summable.tsum_prod]
    apply tsum_congr
    intro n
    rw [pmb_apply hB]
    change (∑' m, B n m*s3kv_vector z m)*basisF n u = _
    rw [← tsum_mul_right]
    apply tsum_congr
    intro m
    rw [s3kv_vector_apply hz]
    change B3 (grunsky (fsans ν) (gsans ν)) n m*basisE m z*basisF n u = _
    rw [(hsym n m).2.2]
    rfl
  exact he ▸ hn.hasSum

theorem s3kv_K2_row_A21 {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    (fun u => kerK2 (fsans ν) (gsans ν) z u) ∈ A21fun unitDiscExterior := by
  apply (ab112_A21fun_congr wp_exterior_isOpen (fun u hu => (s3kv_K2_row_series hν hz hu).tsum_eq)).mp
  exact e212_ext_series (gop_l2_summable _)

/-- The genuine mixed variation integrand is absolutely integrable. -/
theorem s3kv_K2_product_integrable {ν : LinfStar} (hν : ν ∈ LinfStarBall) {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    IntegrableOn (fun u => μ u*kerK2 (fsans ν) (gsans ν) z u*kerK2 (fsans ν) (gsans ν) w u)
      unitDiscExterior := by
  have h1 := a21_memLp_two wp_exterior_isOpen.measurableSet (s3kv_K2_row_A21 hν hz)
  have h2 := a21_memLp_two wp_exterior_isOpen.measurableSet (s3kv_K2_row_A21 hν hw)
  have hi := (h1.integrable_mul h2).mul_of_top_right (d2_harmonicL2_memLp hμ)
  change IntegrableOn (fun u => μ u*(kerK2 (fsans ν) (gsans ν) z u*kerK2 (fsans ν) (gsans ν) w u))
    unitDiscExterior at hi
  simpa only [mul_assoc] using hi

/-- The actual HS derivative equals the actual, integrable mixed variation kernel. -/
theorem s3kv_HS_mixed_kernel {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {F : ℂ → s3tc_HS} {d : s3tc_HS}
    (he : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ q : ℕ × ℕ, F t q =
      B1 (grunsky (fsans (beltramiMul (t • toLinf μ) ν))
        (gsans (beltramiMul (t • toLinf μ) ν))) q.1 q.2)
    (hF : HasDerivAt F d 0) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    IntegrableOn (fun u => μ u*kerK2 (fsans ν) (gsans ν) z u*kerK2 (fsans ν) (gsans ν) w u)
      unitDiscExterior ∧
    s3kv_eval z w d = ∫ u in unitDiscExterior,
      μ u*kerK2 (fsans ν) (gsans ν) z u*kerK2 (fsans ν) (gsans ν) w u :=
  ⟨s3kv_K2_product_integrable hν hμ hz hw,
    (s3kv_HS_kernel_derivative hν hνT hμ he hF hz hw hzw).unique (s3kv_K2_variation hν hμ hz hw hzw)⟩

/-- The original hypotheses supply one and the same actual HS derivative
for both the Fredholm trace formula and the integrable mixed-kernel formula. -/
theorem s3kv_chart_data {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∃ F : ℂ → s3tc_HS, ∃ d : s3tc_HS,
      (∀ᶠ t in 𝓝 (0 : ℂ), ∀ q : ℕ × ℕ, F t q =
        B1 (grunsky (fsans (beltramiMul (t • toLinf μ) ν))
          (gsans (beltramiMul (t • toLinf μ) ν))) q.1 q.2) ∧
      HasDerivAt F d 0 ∧
      bersDz liouvilleS2 ν μ = -s3tc_trace
        (s3tc_left (s3ft_resolvent (F 0)) d) (s3tc_adjoint (F 0)) ∧
      ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
        IntegrableOn (fun u => μ u*kerK2 (fsans ν) (gsans ν) z u*kerK2 (fsans ν) (gsans ν) w u)
          unitDiscExterior ∧
        s3kv_eval z w d = ∫ u in unitDiscExterior,
          μ u*kerK2 (fsans ν) (gsans ν) z u*kerK2 (fsans ν) (gsans ν) w u := by
  obtain ⟨F,d,he,hF,hunit,htrace,hs,hdiag⟩ := s3ft_chart_resolvent hν hνT hμ
  exact ⟨F,d,he,hF,htrace,fun z hz w hw hzw => s3kv_HS_mixed_kernel hν hνT hμ he hF hz hw hzw⟩

end Ch2
end TakhtajanTeo
