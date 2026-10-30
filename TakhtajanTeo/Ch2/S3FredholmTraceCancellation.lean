import TakhtajanTeo.Ch2.S3FredholmDerivative

/-! # Cyclic cancellation and the genuine Fredholm resolvent trace -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- Equal products have equal actual diagonal traces. -/
theorem s3ft_trace_congr_product {A B C D : s3tc_HS}
    (h : s3tc_toOperator A*s3tc_toOperator B = s3tc_toOperator C*s3tc_toOperator D) :
    s3tc_trace A B = s3tc_trace C D := by
  rw [← (s3tc_trace_diagonal A B).2,← (s3tc_trace_diagonal C D).2,h]

/-- A bounded-factor cyclic rotation, with every trace represented by two HS factors. -/
theorem s3ft_cycle (T U : ell2 →L[ℂ] ell2) (A B C E : s3tc_HS) :
    s3tc_trace (s3tc_left (T*(s3tc_toOperator B*s3tc_toOperator C)*U) A) E =
      s3tc_trace (s3tc_left (U*(s3tc_toOperator A*s3tc_toOperator E)*T) B) C := by
  calc
    _ = s3tc_trace (s3tc_left T B)
        (s3tc_rightCLM (U*(s3tc_toOperator A*s3tc_toOperator E)) C) := by
      apply s3ft_trace_congr_product
      simp only [s3tc_left_operator,s3tc_right_operator,mul_assoc]
    _ = _ := by rw [← s3tc_trace_left_right,← s3tc_left_mul]

theorem s3ft_left_add (T U : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_left (T+U) A = s3tc_left T A+s3tc_left U A := by
  change (s3tc_leftAction (T+U)) A = _
  rw [map_add]
  rfl

theorem s3ft_power_combine (A : s3tc_HS) (p q : ℕ) :
    s3fd_gram A^q*s3fd_gram A*s3fd_gram A^p = s3fd_gram A^(p+q+1) := by
  rw [← pow_succ,← pow_add]
  congr 1
  omega

/-- Every position of the inserted Gram variation gives the same trace. -/
theorem s3ft_insertion (A D : s3tc_HS) (p q : ℕ) :
    inner ℂ A (s3tc_left (s3fd_gram A^p*s3fd_gramChange A D*s3fd_gram A^q) A) =
      inner ℂ A (s3tc_left (s3fd_gram A^(p+q+1)) D) +
      inner ℂ D (s3tc_left (s3fd_gram A^(p+q+1)) A) := by
  rw [← s3tc_trace_gram_pair]
  have hsplit : s3fd_gram A^p*s3fd_gramChange A D*s3fd_gram A^q =
      s3fd_gram A^p*(s3tc_toOperator A*s3tc_toOperator (s3tc_adjoint D))*s3fd_gram A^q +
      s3fd_gram A^p*(s3tc_toOperator D*s3tc_toOperator (s3tc_adjoint A))*s3fd_gram A^q := by
    simp only [s3fd_gramChange,s3tc_adjoint_operator,mul_add,add_mul]
  rw [hsplit,s3ft_left_add,s3tc_trace_add_left,
    s3ft_cycle (s3fd_gram A^p) (s3fd_gram A^q) A A (s3tc_adjoint D) (s3tc_adjoint A),
    s3ft_cycle (s3fd_gram A^p) (s3fd_gram A^q) A D (s3tc_adjoint A) (s3tc_adjoint A),
    s3tc_adjoint_operator]
  change s3tc_trace (s3tc_left (s3fd_gram A^q*s3fd_gram A*s3fd_gram A^p) A) (s3tc_adjoint D) +
    s3tc_trace (s3tc_left (s3fd_gram A^q*s3fd_gram A*s3fd_gram A^p) D) (s3tc_adjoint A) = _
  rw [s3ft_power_combine,s3tc_trace_gram_pair,s3tc_trace_gram_pair]
  exact add_comm _ _

/-- Cancellation of the entire insertion sum, including the zero-power case. -/
theorem s3ft_powerChange_trace (A D : s3tc_HS) (N : ℕ) :
    inner ℂ A (s3tc_left (s3fd_powerChange A D N) A) =
      (N : ℂ)*(inner ℂ A (s3tc_left (s3fd_gram A^N) D) +
        inner ℂ D (s3tc_left (s3fd_gram A^N) A)) := by
  unfold s3fd_powerChange
  change (innerSL ℂ A) ((s3tc_leftAction.flip A) (∑ j ∈ Finset.range N,
    s3fd_gram A^(N.pred-j)*s3fd_gramChange A D*s3fd_gram A^j)) = _
  rw [map_sum,map_sum]
  have he : ∀ j ∈ Finset.range N,
      (innerSL ℂ A) ((s3tc_leftAction.flip A)
        (s3fd_gram A^(N.pred-j)*s3fd_gramChange A D*s3fd_gram A^j)) =
        inner ℂ A (s3tc_left (s3fd_gram A^N) D) +
          inner ℂ D (s3tc_left (s3fd_gram A^N) A) := by
    intro j hj
    have hn : N.pred-j+j+1 = N := by
      have hj' : j < N := Finset.mem_range.mp hj
      simp only [Nat.pred_eq_sub_one]
      omega
    exact (s3ft_insertion A D (N.pred-j) j).trans (by rw [hn])
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem s3ft_gram_star (A : s3tc_HS) (N : ℕ) : star (s3fd_gram A^N) = s3fd_gram A^N := by
  rw [star_pow]
  congr 1
  simp only [s3fd_gram,star_mul,star_star]

theorem s3ft_inner_symm (A D : s3tc_HS) (N : ℕ) :
    inner ℂ D (s3tc_left (s3fd_gram A^N) A) =
      conj (inner ℂ A (s3tc_left (s3fd_gram A^N) D)) := by
  rw [s3tc_left_inner,s3ft_gram_star]
  exact (inner_conj_symm _ _).symm

/-- All N+1 differentiated factors cancel the logarithm coefficient 1/(N+1). -/
theorem s3ft_traceTerm (A D : s3tc_HS) (N : ℕ) :
    s3fd_traceTerm A D N = -2*(s3tc_trace (s3tc_left (s3fd_gram A^N) D) (s3tc_adjoint A)).re := by
  simp only [s3fd_traceTerm,s3tc_trace_gram_pair,inner_add_right]
  rw [s3ft_powerChange_trace,s3ft_inner_symm]
  simp only [Complex.add_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    Complex.conj_re,Complex.conj_im,zero_mul,sub_zero]
  have hn : (N : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

/-- The resolvent of the actual Gram operator on ell2. -/
def s3ft_resolvent (A : s3tc_HS) : ell2 →L[ℂ] ell2 := Ring.inverse (1-s3fd_gram A)

theorem s3ft_neumann (A : s3tc_HS) (hA : ‖s3tc_toOperator A‖ < 1) :
    IsUnit (1-s3fd_gram A) ∧ HasSum (fun N : ℕ => s3fd_gram A^N) (s3ft_resolvent A) := by
  have hk : ‖s3fd_gram A‖ < 1 := by
    have h := s3fd_power_norm A (norm_nonneg _) le_rfl 1
    simp only [pow_one] at h
    have hsq : ‖s3tc_toOperator A‖^2 < 1 := by nlinarith [norm_nonneg (s3tc_toOperator A)]
    exact h.trans_lt hsq
  exact ⟨isUnit_one_sub_of_norm_lt_one hk,hasSum_geom_series_inverse _ hk⟩

/-- Continuous HS actions and trace pairing justify the Neumann/trace exchange. -/
theorem s3ft_trace_neumann (A D : s3tc_HS) (hA : ‖s3tc_toOperator A‖ < 1) :
    HasSum (fun N => s3tc_trace (s3tc_left (s3fd_gram A^N) D) (s3tc_adjoint A))
      (s3tc_trace (s3tc_left (s3ft_resolvent A) D) (s3tc_adjoint A)) := by
  let L := (s3tc_tracePair.flip (s3tc_adjoint A)).comp (s3tc_leftAction.flip D)
  exact L.hasSum (s3ft_neumann A hA).2

/-- The real derivative series equals the real part of one actual resolvent trace. -/
theorem s3ft_traceTerm_hasSum (A D : s3tc_HS) (hA : ‖s3tc_toOperator A‖ < 1) :
    HasSum (s3fd_traceTerm A D)
      (-2*(s3tc_trace (s3tc_left (s3ft_resolvent A) D) (s3tc_adjoint A)).re) := by
  have h := (Complex.reCLM.hasSum (s3ft_trace_neumann A D hA)).mul_left (-2)
  change HasSum (fun N => s3fd_traceTerm A D N) _
  simpa only [Complex.reCLM_apply,s3ft_traceTerm] using h

theorem s3ft_resolvent_trace_smul (A D : s3tc_HS) (v : ℂ) :
    s3tc_trace (s3tc_left (s3ft_resolvent A) (v • D)) (s3tc_adjoint A) =
      v*s3tc_trace (s3tc_left (s3ft_resolvent A) D) (s3tc_adjoint A) := by
  change s3tc_trace ((s3tc_leftCLM (s3ft_resolvent A)) (v • D)) (s3tc_adjoint A) = _
  rw [map_smul,s3tc_trace_smul_left]
  rfl

/-- The two real directions recover the single complex resolvent trace. -/
theorem s3ft_two_directions (A D : s3tc_HS) (hA : ‖s3tc_toOperator A‖ < 1) :
    ((∑' N, s3fd_traceTerm A D N : ℝ) -
      I*(∑' N, s3fd_traceTerm A (I • D) N : ℝ))/2 =
      -s3tc_trace (s3tc_left (s3ft_resolvent A) D) (s3tc_adjoint A) := by
  rw [(s3ft_traceTerm_hasSum A D hA).tsum_eq,
    (s3ft_traceTerm_hasSum A (I • D) hA).tsum_eq,s3ft_resolvent_trace_smul]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring

/-- A real Frechet derivative with the proved directional trace formulas has
the corresponding Wirtinger resolvent trace. -/
theorem s3ft_wirtinger {f : ℂ → ℝ} (hf : DifferentiableAt ℝ f 0) (A D : s3tc_HS)
    (hA : ‖s3tc_toOperator A‖ < 1)
    (hv : ∀ v : ℂ, HasDerivAt (fun s : ℝ => f ((s : ℂ)*v))
      (∑' N, s3fd_traceTerm A (v • D) N) 0) :
    dz (fun t => (f t : ℂ)) 0 =
      -s3tc_trace (s3tc_left (s3ft_resolvent A) D) (s3tc_adjoint A) := by
  have heval (v : ℂ) : fderiv ℝ f 0 v = ∑' N, s3fd_traceTerm A (v • D) N := by
    have hline : HasDerivAt (fun s : ℝ => (s : ℂ)*v) v 0 := by
      simpa only [Complex.real_smul,id,Complex.ofReal_one,one_mul] using
        (hasDerivAt_id (0 : ℝ)).smul_const v
    exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)).unique (hv v)
  have hg := Complex.ofRealCLM.hasFDerivAt.comp 0 hf.hasFDerivAt
  change dz (Complex.ofRealCLM ∘ f) 0 = _
  rw [dz,hg.fderiv]
  simp only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,heval,one_smul]
  exact s3ft_two_directions A D hA

/-- This is the genuine, absolutely convergent ell2 diagonal trace of R D A*. -/
theorem s3ft_resolvent_diagonal (A D : s3tc_HS) :
    Summable (fun m => inner ℂ (lp.single 2 m 1 : ell2)
      ((s3ft_resolvent A*s3tc_toOperator D*star (s3tc_toOperator A)) (lp.single 2 m 1))) ∧
      (∑' m, inner ℂ (lp.single 2 m 1 : ell2)
        ((s3ft_resolvent A*s3tc_toOperator D*star (s3tc_toOperator A)) (lp.single 2 m 1))) =
        s3tc_trace (s3tc_left (s3ft_resolvent A) D) (s3tc_adjoint A) := by
  simpa only [s3tc_left_operator,s3tc_adjoint_operator] using
    s3tc_trace_diagonal (s3tc_left (s3ft_resolvent A) D) (s3tc_adjoint A)

/-- The actual Bers first variation is the resolvent trace, retaining the
genuine HS curve and its derivative for subsequent kernel identification. -/
theorem s3ft_chart_resolvent {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (hνT : Phi ⟨ν,hν⟩ ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∃ F : ℂ → s3tc_HS, ∃ d : s3tc_HS,
      (∀ᶠ t in 𝓝 (0 : ℂ), ∀ q : ℕ × ℕ, F t q =
        B1 (grunsky (fsans (beltramiMul (t • toLinf μ) ν))
          (gsans (beltramiMul (t • toLinf μ) ν))) q.1 q.2) ∧
      HasDerivAt F d 0 ∧ IsUnit (1-s3fd_gram (F 0)) ∧
      bersDz liouvilleS2 ν μ =
        -s3tc_trace (s3tc_left (s3ft_resolvent (F 0)) d) (s3tc_adjoint (F 0)) ∧
      Summable (fun m => inner ℂ (lp.single 2 m 1 : ell2)
        ((s3ft_resolvent (F 0)*s3tc_toOperator d*star (s3tc_toOperator (F 0))) (lp.single 2 m 1))) ∧
      bersDz liouvilleS2 ν μ = -(∑' m, inner ℂ (lp.single 2 m 1 : ell2)
        ((s3ft_resolvent (F 0)*s3tc_toOperator d*star (s3tc_toOperator (F 0))) (lp.single 2 m 1))) := by
  obtain ⟨F,d,he,hF,hd,hv⟩ := s3fd_chart_variation hν hνT hμ
  have hentry (m n : ℕ) : F 0 (m,n) = B1 (grunsky (fsans ν) (gsans ν)) m n := by
    simpa only [zero_smul,grp_zero_mul hν] using he.self_of_nhds (m,n)
  have hop : s3tc_toOperator (F 0) = gopOp (B1 (grunsky (fsans ν) (gsans ν))) := by
    change gopOp (fun m n => F 0 (m,n)) = _
    congr 1
    funext m n
    exact hentry m n
  have hgap : ‖s3tc_toOperator (F 0)‖ < 1 := by rw [hop]; exact (pgb_norm_lt_one hν).1
  have hb : bersDz liouvilleS2 ν μ =
      -s3tc_trace (s3tc_left (s3ft_resolvent (F 0)) d) (s3tc_adjoint (F 0)) :=
    s3ft_wirtinger hd (F 0) d hgap (fun v => (hv v).2)
  have hdiag := s3ft_resolvent_diagonal (F 0) d
  exact ⟨F,d,he,hF,(s3ft_neumann (F 0) hgap).1,hb,hdiag.1,by rw [hdiag.2]; exact hb⟩

end Ch2
end TakhtajanTeo
